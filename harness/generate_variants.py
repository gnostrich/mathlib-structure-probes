#!/usr/bin/env python3
"""
Loosening-lattice variant generator (PREREG-loosening-lattice.md).
Emits one file per theorem: de-modularized verbatim prefix + canaries (C1 survive / C2 break /
C3 N/A) + per-move sorry-twin & variant + pre-named pairs + scope closers. Manifest JSON maps
decl -> (file, role, move, line range) for log attribution. Uniform rules only; parse-skips logged.
"""
import re, json, os, sys

SRC="mathlib4/Mathlib/Algebra/GroupWithZero/Basic.lean"
OUT="lattice_upload/RequestProject/Variants"
MAN="lattice_manifest.json"

LADDER={"GroupWithZero":"MonoidWithZero","CommGroupWithZero":"CommMonoidWithZero",
        "MonoidWithZero":"MulZeroOneClass","CancelMonoidWithZero":"MonoidWithZero",
        "MulZeroOneClass":"MulZeroClass"}

lines=open(SRC).read().split("\n")

# ---------- de-modularize (deterministic transform, applied to prefix text) ----------
def demod(l):
    if l.strip()=="module": return None                      # drop
    l=re.sub(r'^public import ', 'import ', l)
    if re.match(r'^@\[expose\]\s*public section\s*$', l): return "section"
    l=re.sub(r'^public section\s*$', 'section', l)
    return l

# ---------- scope + variable tracking ----------
DECL_RE=re.compile(r'^(?P<attrs>(@\[[^\]]*\]\s*)*)(?P<mods>(private\s+|protected\s+|nonrec\s+|noncomputable\s+)*)(?P<kw>theorem|lemma)\s+(?P<name>[^\s({\[:⦃]+)')
TOP_RE =re.compile(r'^(@\[|theorem\s|lemma\s|instance\b|def\s|abbrev\s|attribute\b|section\b|end\b|namespace\s|variable\b|open\s|/--|/-!|assert_not_exists|private\s|protected\s|noncomputable\s|deriving\b|#|example\b)')

scope=[]          # list of ("section",name_or_"") / ("namespace",name)
varstack=[]       # list of (depth, vartext)
events=[]         # per-line: snapshot refs
for i,l in enumerate(lines):
    s=l.strip()
    m=re.match(r'^section\s*([A-Za-z0-9_\'.₀-₉]*)\s*$', s) or (re.match(r'^@\[expose\]\s*public section\s*$',s) and re.match(r'(public section)','public section'))
    events.append((len(scope), list(scope), list(varstack)))
    if re.match(r'^@\[expose\]\s*public section\s*$', s) or re.match(r'^public section\s*$', s):
        scope.append(("section","")); continue
    m=re.match(r'^section\s*([^\s]*)\s*$', s)
    if m: scope.append(("section",m.group(1))); continue
    m=re.match(r'^namespace\s+([^\s]+)\s*$', s)
    if m: scope.append(("namespace",m.group(1))); continue
    m=re.match(r'^end\s*([^\s]*)\s*$', s)
    if m and scope: scope.pop();
    if m: continue
    if s.startswith("variable"):
        varstack.append((len(scope), s[len("variable"):].strip()))
        continue
# note: varstack entries with depth > current scope depth are dead; filter at use.

def scope_at(i):   # open scopes + live variable binders at line i
    depth, sc, vs = events[i]
    live=" ".join(t for d,t in vs if d<=depth)
    return sc, live

# ---------- locate theorem blocks ----------
anchors=[i for i,l in enumerate(lines) if TOP_RE.match(l)]
def block_end(start):
    for a in anchors:
        if a>start:
            # skip continuation attr on same decl (attr line then kw line handled below)
            return a
    return len(lines)

decls=[]
i=0
while i < len(lines):
    l=lines[i]
    m=DECL_RE.match(l)
    if not m:
        # attr-only line followed by decl line
        if re.match(r'^(@\[[^\]]*\]\s*)+$', l.strip()) and i+1<len(lines):
            m2=DECL_RE.match(lines[i+1])
            if m2:
                start=i; kwline=i+1
                end=block_end(kwline+1)
                decls.append((start,kwline,end,m2))
                i=end; continue
        i+=1; continue
    start=i; end=block_end(i+1)
    decls.append((start,i,end,m))
    i=end

# include preceding doc-comment in block start (for prefix truncation)
def with_doc(start):
    j=start-1
    while j>=0 and (lines[j].strip()=="" ): j-=1
    # walk back over a /-- ... -/ block
    if j>=0 and lines[j].strip().endswith("-/"):
        k=j
        while k>=0 and not lines[k].strip().startswith("/--"):
            k-=1
        if k>=0: return k
    return start

# ---------- signature parsing ----------
def depth0_split(text):
    """return (sig, stmt, proof) splitting at depth-0 ':' and ':='"""
    pairs={'(' :')','{':'}','[':']','⦃':'⦄'}
    openers=set(pairs); closers={v:k for k,v in pairs.items()}
    depth=0; colon=-1; assign=-1
    j=0
    while j<len(text):
        c=text[j]
        if c in openers: depth+=1
        elif c in closers: depth-=1
        elif depth==0:
            if colon<0 and c==':' and (j+1>=len(text) or text[j+1] not in '=:'):
                colon=j
            elif c==':' and j+1<len(text) and text[j+1]=='=':
                assign=j; break
        j+=1
    if colon<0 or assign<0: return None
    return text[:colon], text[colon+1:assign], text[assign+2:]

def top_paren_groups(sig):
    """explicit () binder groups at depth 0: list of (start,end) inclusive"""
    out=[]; depth=0; st=-1
    pairs={'(' :')','{':'}','[':']','⦃':'⦄'}
    for j,c in enumerate(sig):
        if c in pairs:
            if depth==0 and c=='(': st=j
            depth+=1
        elif c in pairs.values():
            depth-=1
            if depth==0 and st>=0 and c==')':
                out.append((st,j)); st=-1
    return out

def wordsub(text, a, b):
    return re.sub(r'(?<![A-Za-z0-9_₀-₉\'])'+re.escape(a)+r'(?![A-Za-z0-9_₀-₉\'])', b, text)

# ---------- build variants ----------
os.makedirs(OUT, exist_ok=True)
manifest=[]; skips=[]
TYVARS=["M₀","G₀","R","S"]

for k,(dstart,kwline,dend,m) in enumerate(decls):
    name=m.group("name")
    block="\n".join(lines[kwline:dend]).rstrip()
    # strip attrs+mods from the decl's own text
    mm=DECL_RE.match(block)
    body=block[mm.end():]
    parsed=depth0_split(body)
    if not parsed:
        skips.append({"theorem":name,"reason":"no depth-0 ':'/':=' parse"}); continue
    sig, stmt, proof = parsed
    if proof.strip()=="" or "where" in sig:
        skips.append({"theorem":name,"reason":"empty proof or where-clause"}); continue
    sc, livevars = scope_at(kwline)
    # ambient class binders on ty vars
    amb=[]  # (class, tyvar)
    for cm in re.finditer(r'\[([A-Za-z][A-Za-z0-9]*)\s+([A-Za-z]?[₀-₉]?\w*)\]', livevars):
        amb.append((cm.group(1), cm.group(2)))
    fulltext=sig+" : "+stmt
    tyv=next((t for t in TYVARS if re.search(r'(?<![A-Za-z0-9_₀-₉])'+t, fulltext) or any(v==t for _,v in amb)), None)
    myamb=[(c,v) for c,v in amb if v==tyv]
    # value binders in scope on tyv, mentioned in decl text
    valbinders=[]
    for vm in re.finditer(r'\{([^:{}]+):\s*'+ (tyv or "NOMATCH") +r'\}', livevars):
        for nm in vm.group(1).split():
            if re.search(r'(?<![A-Za-z0-9_₀-₉\'])'+re.escape(nm)+r'(?![A-Za-z0-9_₀-₉\'])', fulltext+" "+proof):
                valbinders.append(nm)
    # natvars {n : ℕ} etc mentioned
    extra=[]
    for vm in re.finditer(r'\{([^:{}]+):\s*(ℕ|ℤ)\}', livevars):
        for nm in vm.group(1).split():
            if re.search(r'(?<![A-Za-z0-9_₀-₉\'])'+re.escape(nm)+r'(?![A-Za-z0-9_₀-₉\'])', fulltext):
                extra.append((nm,vm.group(2)))

    fname=f"V{k:03d}"
    outlines=[]
    # prefix: demodularized verbatim up to (incl doc of) this decl
    trunc=with_doc(dstart)
    for l in lines[:trunc]:
        dl=demod(l)
        if dl is not None: outlines.append(dl)
    prefix_end=len(outlines)
    entries=[]
    def emit(decl_lines, role, move, twin_rel=None, var_rel=None):
        flat=[]
        rel_map=[]
        for part in decl_lines:
            for ln in part.split("\n"):
                flat.append(ln)
        a=len(outlines)+1
        outlines.extend(flat)
        b=len(outlines)
        e={"role":role,"move":move,"lines":[a,b]}
        if twin_rel is not None: e["twin_start"]=a+twin_rel
        if var_rel is not None: e["var_start"]=a+var_rel
        entries.append(e)
    # canaries
    emit([f"theorem v{k}_c1 {sig} : {stmt} := {proof}", ""], "canary_survive","C1")
    emit([f"theorem v{k}_c2 : True := Nat.zero",""], "canary_break","C2")
    emit([f"theorem v{k}_c3 : NoSuchIdent_xyzzy_{k} := sorry",""], "canary_na","C3")

    moves=[]
    groups=top_paren_groups(sig)
    for gi,(a,b) in enumerate(groups):
        newsig=(sig[:a]+sig[b+1:]).strip()
        moves.append((f"M1_h{gi}", newsig, stmt, proof, None, None))
    # M2 / M3 restatement with fresh tyvar
    def restate(weaken=None, drop_nontrivial=False):
        if not tyv or not myamb: return None
        nt="MXV"
        bs=[f"{{{nt} : Type*}}"]
        used=False
        for c,v in myamb:
            if drop_nontrivial and c=="Nontrivial": used=True; continue
            cc=c
            if weaken and c==weaken[0]: cc=weaken[1]; used=True
            bs.append(f"[{cc} {nt}]")
        if not used: return None
        if valbinders: bs.append("{"+" ".join(dict.fromkeys(valbinders))+f" : {nt}"+"}")
        for nm,ty in extra: bs.append(f"{{{nm} : {ty}}}")
        rs=wordsub(sig,tyv,nt); rst=wordsub(stmt,tyv,nt); rp=wordsub(proof,tyv,nt)
        return (" ".join(bs)+" "+rs).strip(), rst, rp
    for c,v in myamb:
        if c in LADDER:
            r=restate(weaken=(c,LADDER[c]))
            if r: moves.append((f"M2_{c}", r[0], r[1], r[2], None, None))
            break
    if any(c=="Nontrivial" for c,v in myamb):
        r=restate(drop_nontrivial=True)
        if r: moves.append(("M3_Nontrivial", r[0], r[1], r[2], None, None))
    # infra moves (statement unchanged)
    moves.append(("I1_shadow", sig, stmt, proof, "section_shadow", None))
    moves.append(("I2_synthHB", sig, stmt, proof, None, "set_option synthInstance.maxHeartbeats 1000 in"))
    moves.append(("I3_synthSize", sig, stmt, proof, None, "set_option synthInstance.maxSize 16 in"))
    # pairs
    if groups:
        a,b=groups[0]
        ps=(sig[:a]+sig[b+1:]).strip()
        moves.append(("P1_M1xI1", ps, stmt, proof, "section_shadow", None))
        moves.append(("P2_M1xI2", ps, stmt, proof, None, "set_option synthInstance.maxHeartbeats 1000 in"))

    for tag,msig,mstmt,mproof,wrap,opt in moves:
        if wrap=="section_shadow" and (not myamb or not tyv):
            entries.append({"role":"na_recorded","move":tag,"lines":[0,0]}); continue
        pre=(opt+"\n") if opt else ""
        tw=f"{pre}theorem t{k}_{tag} {msig} : {mstmt} := sorry".replace("  "," ")
        vr=f"{pre}theorem v{k}_{tag} {msig} : {mstmt} := {mproof}"
        role="pair" if tag.startswith("P") else ("math" if tag.startswith("M") else "infra")
        if wrap=="section_shadow":
            sh=f"local instance (priority := 10000) v{k}_shadow_{tag} : {myamb[0][0]} {tyv} := inferInstance"
            twin_rel=2 + (1 if opt else 0)
            head=["section", sh]
            tw_lines=tw.split("\n"); vr_lines=vr.split("\n")
            var_rel=len(head)+len(tw_lines)+ (1 if opt else 0) - (1 if opt else 0)
            var_rel=len(head)+len(tw_lines)
            emit(head+tw_lines+vr_lines+["end",""], role, tag, twin_rel=len(head), var_rel=var_rel)
        else:
            tw_lines=tw.split("\n"); vr_lines=vr.split("\n")
            emit(tw_lines+vr_lines+[""], role, tag, twin_rel=0, var_rel=len(tw_lines))

    # closers for open scopes at truncation
    sc_now,_=scope_at(kwline)
    for kind,nm in reversed(sc_now):
        outlines.append(f"end {nm}".strip())
    open(os.path.join(OUT,fname+".lean"),"w").write("\n".join(outlines)+"\n")
    manifest.append({"file":fname,"theorem":name,"k":k,"kwline":kwline+1,
                     "n_moves":len(moves),"prefix_end":prefix_end,"entries":entries,
                     "amb":myamb,"tyv":tyv,"n_hyp":len(groups),
                     "namespace":[nm for kd,nm in sc if kd=="namespace"]})

json.dump({"decls":manifest,"skips":skips}, open(MAN,"w"), indent=1)
print(f"theorems parsed={len(manifest)}  skipped={len(skips)}  files -> {OUT}")
for s in skips: print("  SKIP:", s)
nm=sum(d["n_moves"] for d in manifest)
print(f"total move-variants={nm} (+3 canaries x {len(manifest)} files)")
