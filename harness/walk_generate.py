#!/usr/bin/env python3
"""
V3 walk state-table generator (PREREG-v3-walk-3batch.md).
Per goal: remove 1-2 constraints (ground truth), build repair menu (cap 4), emit ALL 2^m states
(twin + fixed-suite variant) after a verbatim de-modularized prefix. Canaries C2/C3 per file.
Usage: walk_generate.py <src.lean> <batch> <N> <outdir> <manifest.json>
"""
import re, json, os, sys, hashlib

SRC, BATCH, N, OUT, MAN = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
SUITE = "by intros; first | assumption | rfl | simp_all | aesop | skip"
LADDER_DOWN={"GroupWithZero":"MonoidWithZero","CommGroupWithZero":"CommMonoidWithZero",
  "MonoidWithZero":"MulZeroOneClass","CancelMonoidWithZero":"MonoidWithZero",
  "MulZeroOneClass":"MulZeroClass","Field":"DivisionRing","DivisionRing":"Ring",
  "CommRing":"Ring","IsDomain":"NoZeroDivisors","CommGroup":"Group","Group":"Monoid",
  "CommMonoid":"Monoid","Monoid":"Semigroup","Fintype":"Finite"}
LADDER_UP={v:k for k,v in LADDER_DOWN.items()}
PROPISH=re.compile(r'[=≠<≤∣∈¬∀∃→↔]|Prime|Irreducible|IsUnit|degree|Monic')

lines=open(SRC).read().split("\n")
def demod(l):
    if l.strip()=="module": return None
    l=re.sub(r'^public import ','import ',l)
    if re.match(r'^@\[expose\]\s*public section\s*$',l): return "section"
    return re.sub(r'^public section\s*$','section',l)

DECL_RE=re.compile(r'^(?P<attrs>(@\[[^\]]*\]\s*)*)(?P<mods>(private\s+|protected\s+|nonrec\s+|noncomputable\s+)*)(?P<kw>theorem|lemma)\s+(?P<name>[^\s({\[:⦃]+)')
TOP_RE =re.compile(r'^(@\[|theorem\s|lemma\s|instance\b|def\s|abbrev\s|attribute\b|section\b|end\b|namespace\s|variable\b|open\s|/--|/-!|assert_not_exists|private\s|protected\s|noncomputable\b|deriving\b|#|example\b|local\b|scoped\b|set_option\b)')
scope=[]; varstack=[]; events=[]
for i,l in enumerate(lines):
    s=l.strip(); events.append((len(scope),list(scope),list(varstack)))
    if re.match(r'^@\[expose\]\s*public section\s*$',s) or re.match(r'^public section\s*$',s) or s=="noncomputable section":
        scope.append(("section","")); continue
    m=re.match(r'^section\s*([^\s]*)\s*$',s)
    if m: scope.append(("section",m.group(1))); continue
    m=re.match(r'^namespace\s+([^\s]+)\s*$',s)
    if m: scope.append(("namespace",m.group(1))); continue
    m=re.match(r'^end\s*([^\s]*)\s*$',s)
    if m:
        if scope: scope.pop()
        continue
    if s.startswith("variable"): varstack.append((len(scope),s[len("variable"):].strip()))
def scope_at(i):
    d,sc,vs=events[i]; return sc," ".join(t for dd,t in vs if dd<=d)

anchors=[i for i,l in enumerate(lines) if TOP_RE.match(l)]
def block_end(st):
    for a in anchors:
        if a>st: return a
    return len(lines)
decls=[]; i=0
while i<len(lines):
    m=DECL_RE.match(lines[i])
    if not m:
        if re.match(r'^(@\[[^\]]*\]\s*)+$',lines[i].strip()) and i+1<len(lines) and DECL_RE.match(lines[i+1]):
            m2=DECL_RE.match(lines[i+1]); e=block_end(i+2); decls.append((i,i+1,e,m2)); i=e; continue
        i+=1; continue
    e=block_end(i+1); decls.append((i,i,e,m)); i=e
def with_doc(st):
    j=st-1
    while j>=0 and lines[j].strip()=="": j-=1
    if j>=0 and lines[j].strip().endswith("-/"):
        k=j
        while k>=0 and not lines[k].strip().startswith("/--"): k-=1
        if k>=0: return k
    return st

def depth0_split(t):
    pairs={'(':')','{':'}','[':']','⦃':'⦄'}; op=set(pairs); cl=set(pairs.values())
    d=0; col=-1; asg=-1; j=0
    while j<len(t):
        c=t[j]
        if c in op: d+=1
        elif c in cl: d-=1
        elif d==0:
            if col<0 and c==':' and (j+1>=len(t) or t[j+1] not in '=:'): col=j
            elif c==':' and j+1<len(t) and t[j+1]=='=': asg=j; break
        j+=1
    if col<0 or asg<0: return None
    return t[:col],t[col+1:asg],t[asg+2:]
def groups(sig, opench, closech):
    out=[]; d=0; st=-1
    pairs={'(':')','{':'}','[':']','⦃':'⦄'}
    for j,c in enumerate(sig):
        if c in pairs:
            if d==0 and c==opench: st=j
            d+=1
        elif c in pairs.values():
            d-=1
            if d==0 and st>=0 and c==closech: out.append((st,j)); st=-1
    return out

os.makedirs(OUT,exist_ok=True)
manifest=[]; skips=[]; gidx=0
for k,(dstart,kwline,dend,m) in enumerate(decls):
    if gidx>=N: break
    name=m.group("name")
    block="\n".join(lines[kwline:dend]).rstrip()
    mm=DECL_RE.match(block); body=block[mm.end():]
    p=depth0_split(body)
    if not p: skips.append((name,"parse")); continue
    sig,stmt,proof=p
    # sites
    hyp_sites=[]
    for a,b in groups(sig,'(',')'):
        inner=sig[a+1:b]
        if ':' in inner and PROPISH.search(inner.split(':',1)[1]):
            hyp_sites.append((a,b,inner))
    inst_sites=[]
    for a,b in groups(sig,'[',']'):
        inner=sig[a+1:b].strip(); cm=re.match(r'([A-Za-z][A-Za-z0-9]*)\s+(.+)$',inner)
        if cm and cm.group(1) in LADDER_DOWN:
            inst_sites.append((a,b,cm.group(1),cm.group(2)))
    sites=[("H",)+h for h in hyp_sites]+[("I",)+s for s in inst_sites]
    if not sites: skips.append((name,"no removable site")); continue
    h=hashlib.md5(name.encode()).digest()
    order=sorted(range(len(sites)),key=lambda ix:hashlib.md5((name+str(ix)).encode()).digest())
    nrem=min(len(sites), 1+(h[0]%2))
    rem_ix=sorted(order[:nrem])
    removals=[sites[ix] for ix in rem_ix]
    # damaged sig: apply removals right-to-left
    dsig=sig
    for site in sorted(removals,key=lambda s:-s[1]):
        if site[0]=="H": a,b=site[1],site[2]; dsig=dsig[:a]+dsig[b+1:]
        else:
            a,b,c,rest=site[1],site[2],site[3],site[4]
            dsig=dsig[:a]+f"[{LADDER_DOWN[c]} {rest}]"+dsig[b+1:]
    # menu: true inverses then decoys
    menu=[]
    for site in removals:
        if site[0]=="H":
            P=site[3].split(':',1)[1].strip()
            menu.append({"kind":"AddHyp","P":P,"truth":True,"cost":2})
        else:
            menu.append({"kind":"StrInst","frm":LADDER_DOWN[site[3]],"to":site[3],"rest":site[4],"truth":True,"cost":1})
    # type var for decoys: first ambient {A B : Type*} or from sig
    sc,livevars=scope_at(kwline)
    tv=None
    tm=re.search(r'\{([A-Za-zα-ωΑ-Ω][₀-₉\w\']*)[^:{}]*:\s*Type',livevars+" "+sig)
    if tm: tv=tm.group(1)
    vv=None
    vm=re.search(r'\{([a-z])[^:{}]*:\s*'+(re.escape(tv) if tv else 'XX')+r'\}',livevars+" "+sig)
    if vm: vv=vm.group(1)
    decoys=[]
    if tv: decoys.append({"kind":"AddHyp","P":f"Nontrivial {tv}","truth":False,"cost":2,"inst":True})
    if vv: decoys.append({"kind":"AddHyp","P":f"{vv} = {vv}","truth":False,"cost":2})
    for d0 in decoys:
        if len(menu)<4: menu.append(d0)
    m_len=len(menu)
    # emit file
    fname=f"{BATCH}_G{gidx:02d}"
    out=[]
    for l in lines[:with_doc(dstart)]:
        dl=demod(l)
        if dl is not None: out.append(dl)
    entries=[]
    def emit(txt, **kw):
        a=len(out)+1
        for part in txt: out.extend(part.split("\n"))
        entries.append(dict(lines=[a,len(out)],**kw))
    emit([f"theorem {BATCH.lower()}g{gidx}_c2 : True := Nat.zero",""],role="canary_break")
    emit([f"theorem {BATCH.lower()}g{gidx}_c3 : NoSuchIdent_zz{gidx} := sorry",""],role="canary_na")
    for mask in range(2**m_len):
        ssig=dsig
        appended=[]
        for bi,mv in enumerate(menu):
            if mask>>bi & 1:
                if mv["kind"]=="AddHyp":
                    appended.append(f"[{mv['P']}]" if mv.get("inst") else f"(rh{bi} : {mv['P']})")
                else:
                    ssig=re.sub(r'\['+re.escape(mv["frm"])+r'\s+'+re.escape(mv["rest"])+r'\]',
                                f"[{mv['to']} {mv['rest']}]", ssig, count=1)
        full=(ssig+" "+" ".join(appended)).strip()
        tw=f"theorem t{gidx}_s{mask} {full} : {stmt} := sorry"
        vr=f"theorem g{gidx}_s{mask} {full} : {stmt} := {SUITE}"
        a=len(out)+1
        out.extend(tw.split("\n")); vs=len(out)+1
        out.extend(vr.split("\n")); out.append("")
        entries.append(dict(lines=[a,len(out)],role="state",mask=mask,twin_start=a,var_start=vs))
    sc_now,_=scope_at(kwline)
    for kind,nm2 in reversed(sc_now): out.append(f"end {nm2}".strip())
    open(os.path.join(OUT,fname+".lean"),"w").write("\n".join(out)+"\n")
    manifest.append(dict(batch=BATCH,file=fname,theorem=name,goal=gidx,menu=menu,
        n_removed=nrem,truth_mask=sum(1<<i for i,mv in enumerate(menu) if mv["truth"]),
        entries=entries))
    gidx+=1
json.dump({"goals":manifest,"skips":skips},open(MAN,"w"),indent=0)
print(f"{BATCH}: goals={len(manifest)} skips={len(skips)} states_total={sum(2**len(g['menu']) for g in manifest)}")
