#!/usr/bin/env python3
"""
Probe 16 — term-space failure anisotropy: variant generator.
Per PREREG-term-anisotropy.md. Emits one Lean file per theorem: de-modularised verbatim prefix
(truncated so the theorem cannot close its own perturbation), a baseline cell, then for each
direction D1-D6 and depth 1..3 a sorry-twin + the perturbed statement with the ORIGINAL proof
replayed. Twin adjudication separates statement-ill-formed (N/A) from proof-broke (BREAK).
Also synthesises the harness-validity trivialities. Manifest maps every cell to a line range.

Usage: probe16.py <mathlib_root> <outdir> <manifest.json>
"""
import re, json, os, sys, hashlib

MATHLIB, OUT, MAN = sys.argv[1], sys.argv[2], sys.argv[3]
MODULES = ["Mathlib/Algebra/Group/Basic.lean", "Mathlib/Order/Basic.lean"]
MAXTHM = 300
DEPTHS = (1, 2, 3)

# ---- fixed ladders (PREREG) ----
CLASS_LADDER = {
 "CommGroup":["Group","Monoid","Semigroup"], "Group":["Monoid","Semigroup","Mul"],
 "CommMonoid":["Monoid","Semigroup","Mul"], "Monoid":["Semigroup","Mul"],
 "AddCommGroup":["AddGroup","AddMonoid","AddSemigroup"], "AddGroup":["AddMonoid","AddSemigroup","Add"],
 "AddCommMonoid":["AddMonoid","AddSemigroup","Add"], "AddMonoid":["AddSemigroup","Add"],
 "Field":["DivisionRing","Ring","Semiring"], "DivisionRing":["Ring","Semiring"],
 "CommRing":["Ring","Semiring"], "Ring":["Semiring"],
 "LinearOrder":["PartialOrder","Preorder","LE"], "PartialOrder":["Preorder","LE"], "Preorder":["LE"],
 "Lattice":["SemilatticeSup","PartialOrder","Preorder"],
 "CompleteLattice":["Lattice","SemilatticeSup","PartialOrder"],
 "SemilatticeSup":["PartialOrder","Preorder"], "SemilatticeInf":["PartialOrder","Preorder"],
 "CommGroupWithZero":["GroupWithZero","MonoidWithZero","MulZeroClass"],
 "GroupWithZero":["MonoidWithZero","MulZeroClass"], "MonoidWithZero":["MulZeroClass"],
 "DivisionMonoid":["DivInvMonoid","Monoid"], "DivInvMonoid":["Monoid","Semigroup"],
}
INST_LADDER = {"Fintype":["Finite"], "LinearOrder":["PartialOrder","Preorder"],
               "DecidableEq":[], "Decidable":[], "DecidablePred":[]}
FINITENESS = {"Decidable","DecidableEq","DecidablePred","Fintype","Finite"}
CONCRETE = ["ℕ","ℤ","ℚ","ℝ"]
CONCRETE_CLASS = {"ℕ":"AddCommMonoid","ℤ":"AddCommGroup","ℚ":"Field","ℝ":"Field"}
PROPISH = re.compile(r'[=≠<≤≥∣∈¬∀∃→↔]|Prime|Irreducible|IsUnit|Monotone|Injective|Surjective')

DECL_RE = re.compile(r'^(?P<attrs>(@\[[^\]]*\]\s*)*)(?P<mods>(private\s+|protected\s+|nonrec\s+|noncomputable\s+)*)(?P<kw>theorem|lemma)\s+(?P<name>[^\s({\[:⦃]+)')
TOP_RE = re.compile(r'^(@\[|theorem\s|lemma\s|instance\b|def\s|abbrev\s|attribute\b|section\b|end\b|namespace\s|variable\b|open\s|/--|/-!|assert_not_exists|private\s|protected\s|noncomputable\b|deriving\b|#|example\b|local\b|scoped\b|set_option\b|universe\b)')

def demod(l):
    if l.strip() == "module": return None
    l = re.sub(r'^public import ', 'import ', l)
    if re.match(r'^@\[expose\]\s*public section\s*$', l): return "section"
    return re.sub(r'^public section\s*$', 'section', l)

def depth0_split(t):
    pairs = {'(':')','{':'}','[':']','⦃':'⦄'}; op=set(pairs); cl=set(pairs.values())
    d=0; col=-1; asg=-1; j=0
    while j < len(t):
        c=t[j]
        if c in op: d+=1
        elif c in cl: d-=1
        elif d==0:
            if col<0 and c==':' and (j+1>=len(t) or t[j+1] not in '=:'): col=j
            elif c==':' and j+1<len(t) and t[j+1]=='=': asg=j; break
        j+=1
    if col<0 or asg<0: return None
    return t[:col], t[col+1:asg], t[asg+2:]

def groups(sig, o, c):
    out=[]; d=0; st=-1; pairs={'(':')','{':'}','[':']','⦃':'⦄'}
    for j,ch in enumerate(sig):
        if ch in pairs:
            if d==0 and ch==o: st=j
            d+=1
        elif ch in pairs.values():
            d-=1
            if d==0 and st>=0 and ch==c: out.append((st,j)); st=-1
    return out

def wordsub(t,a,b):
    return re.sub(r'(?<![A-Za-z0-9_₀-₉\'])'+re.escape(a)+r'(?![A-Za-z0-9_₀-₉\'])', b, t)

def parse_module(path):
    lines = open(path).read().split("\n")
    scope=[]; varstack=[]; events=[]
    for i,l in enumerate(lines):
        s=l.strip(); events.append((len(scope), list(scope), list(varstack)))
        if re.match(r'^@\[expose\]\s*public section\s*$',s) or re.match(r'^public section\s*$',s) or s=="noncomputable section":
            scope.append(("section","")); continue
        m=re.match(r'^section\s*([^\s]*)\s*$',s)
        if m: scope.append(("section",m.group(1))); continue
        m=re.match(r'^namespace\s+([^\s]+)\s*$',s)
        if m: scope.append(("namespace",m.group(1))); continue
        if re.match(r'^end\b',s):
            if scope: scope.pop()
            # a closing section kills every variable binder declared inside it
            varstack[:] = [(d,t) for d,t in varstack if d <= len(scope)]
            continue
        if s.startswith("variable"): varstack.append((len(scope), s[len("variable"):].strip()))
    anchors=[i for i,l in enumerate(lines) if TOP_RE.match(l)]
    def block_end(st):
        for a in anchors:
            if a>st: return a
        return len(lines)
    decls=[]; i=0
    while i < len(lines):
        m=DECL_RE.match(lines[i])
        if not m:
            if re.match(r'^(@\[[^\]]*\]\s*)+$', lines[i].strip()) and i+1<len(lines) and DECL_RE.match(lines[i+1]):
                m2=DECL_RE.match(lines[i+1]); e=block_end(i+2); decls.append((i,i+1,e,m2)); i=e; continue
            i+=1; continue
        e=block_end(i+1); decls.append((i,i,e,m)); i=e
    return lines, events, decls

def with_doc(lines, st):
    j=st-1
    while j>=0 and lines[j].strip()=="": j-=1
    if j>=0 and lines[j].strip().endswith("-/"):
        k=j
        while k>=0 and not lines[k].strip().startswith("/--"): k-=1
        if k>=0: return k
    return st

# ---------- direction builders: return list over depth of (sig, stmt, proof) or None ----------
def build_D1(sig, stmt, proof, ctx):
    sites=[(a,b) for a,b in groups(sig,'(',')')
           if ':' in sig[a+1:b] and PROPISH.search(sig[a+1:b].split(':',1)[1])]
    outs=[]
    for k in DEPTHS:
        if k>len(sites): outs.append(None); continue
        s=sig
        for a,b in sorted(sites[:k], key=lambda x:-x[0]): s=s[:a]+s[b+1:]
        outs.append((s.strip(), stmt, proof))
    return outs, len(sites)

def build_D2(sig, stmt, proof, ctx):
    amb=ctx["amb"]; tyv=ctx["tyv"]
    cand=[(c,v) for c,v in amb if v==tyv and c in CLASS_LADDER]
    if not cand or not tyv: return [None]*3, 0
    cls=cand[0][0]; ladder=CLASS_LADDER[cls]; cap=min(3,len(ladder))
    outs=[]
    for k in DEPTHS:
        if k>cap: outs.append(None); continue
        nt="PXV"
        bs=[f"{{{nt} : Type*}}"]
        anc=set(CLASS_LADDER.get(cls,[]))
        for c,v in amb:
            if v!=tyv: continue
            if c!=cls and c in anc: continue   # implied by the (pre-weakening) target: redundant
            bs.append(f"[{ladder[k-1] if c==cls else c} {nt}]")
        if ctx["valbinders"]: bs.append("{"+" ".join(dict.fromkeys(ctx["valbinders"]))+f" : {nt}"+"}")
        outs.append(((" ".join(bs)+" "+wordsub(sig,tyv,nt)).strip(),
                     wordsub(stmt,tyv,nt), wordsub(proof,tyv,nt)))
    return outs, cap

def build_D3(sig, stmt, proof, ctx):
    text=ctx["livevars"]+" "+sig
    sites=re.findall(r'\{([A-Za-zα-ω][\w₀-₉\']*)\s*:\s*Type(?!\*)\s*\}', text)
    outs=[]; cap=len(sites)
    for k in DEPTHS:
        if k>cap: outs.append(None); continue
        s=sig
        for nm in sites[:k]:
            s=re.sub(r'\{'+re.escape(nm)+r'\s*:\s*Type\s*\}', f"{{{nm} : Type*}}", s)
        if s==sig:
            s=" ".join(f"{{{nm} : Type*}}" for nm in sites[:k])+" "+sig
        outs.append((s.strip(), stmt, proof))
    return outs, cap

def build_D4(sig, stmt, proof, ctx):
    sites=[]
    for a,b in groups(sig,'[',']'):
        inner=sig[a+1:b].strip(); m=re.match(r'([A-Za-z][A-Za-z0-9]*)\s+(.+)$', inner)
        if m and m.group(1) in INST_LADDER: sites.append((a,b,m.group(1),m.group(2)))
    outs=[]; cap=len(sites)
    for k in DEPTHS:
        if k>cap: outs.append(None); continue
        s=sig
        for a,b,c,rest in sorted(sites[:k], key=lambda x:-x[0]):
            lad=INST_LADDER[c]
            s = s[:a]+(f"[{lad[0]} {rest}]" if lad else "")+s[b+1:]
        outs.append((s.strip(), stmt, proof))
    return outs, cap

def build_D5(sig, stmt, proof, ctx):
    present=[t for t in CONCRETE if t in sig or t in stmt]
    outs=[]; cap=len(present)
    for k in DEPTHS:
        if k>cap: outs.append(None); continue
        s, st2, pf = sig, stmt, proof
        pre=[]
        for idx,t in enumerate(present[:k]):
            g=f"GX{idx}"
            pre.append(f"{{{g} : Type*}} [{CONCRETE_CLASS[t]} {g}]")
            s=s.replace(t,g); st2=st2.replace(t,g)
        outs.append((" ".join(pre)+" "+s.strip(), st2, pf))
    return outs, cap

def build_D6(sig, stmt, proof, ctx):
    sites=[]
    for a,b in groups(sig,'[',']'):
        inner=sig[a+1:b].strip(); m=re.match(r'([A-Za-z][A-Za-z0-9]*)', inner)
        if m and m.group(1) in FINITENESS: sites.append((a,b))
    amb_fin=[(c,v) for c,v in ctx["amb"] if c in FINITENESS]
    outs=[]; cap=len(sites)+len(amb_fin)
    for k in DEPTHS:
        if k>cap: outs.append(None); continue
        s=sig; rem=k
        for a,b in sorted(sites, key=lambda x:-x[0]):
            if rem<=0: break
            s=s[:a]+s[b+1:]; rem-=1
        # ambient finiteness cannot be removed textually; if any remain needed, mark by restating
        # with explicit non-finite context is not sound -> those depths are N/A
        if rem>0: outs.append(None); continue
        outs.append((s.strip(), stmt, proof))
    return outs, min(cap, len(sites))

BUILDERS=[("D1",build_D1),("D2",build_D2),("D3",build_D3),
          ("D4",build_D4),("D5",build_D5),("D6",build_D6)]

def emit_theorem_file(fname, prefix_lines, gid, cells, closers, extra_header=None):
    out=list(prefix_lines); entries=[]
    if extra_header: out.extend(extra_header)
    def add(txt_twin, txt_var, role, direction, depth):
        a=len(out)+1
        tl=txt_twin.split("\n"); out.extend(tl); vs=len(out)+1
        out.extend(txt_var.split("\n")); out.append("")
        entries.append(dict(role=role, direction=direction, depth=depth,
                            lines=[a,len(out)], twin_start=a, var_start=vs))
    for (role, direction, depth, sig, stmt, proof) in cells:
        tag=f"{direction}_{depth}" if direction else role
        add(f"theorem p16t_{gid}_{tag} {sig} : {stmt} := sorry",
            f"theorem p16v_{gid}_{tag} {sig} : {stmt} := {proof}", role, direction, depth)
    a=len(out)+1
    out.append(f"theorem p16c2_{gid} : True := Nat.zero"); out.append("")
    entries.append(dict(role="canary_break", direction=None, depth=None, lines=[a,len(out)]))
    a=len(out)+1
    out.append(f"theorem p16c3_{gid} : NoSuchIdent_p16_{gid} := sorry"); out.append("")
    entries.append(dict(role="canary_na", direction=None, depth=None, lines=[a,len(out)]))
    out.extend(closers)
    open(os.path.join(OUT, fname+".lean"), "w").write("\n".join(out)+"\n")
    return entries

def main():
    os.makedirs(OUT, exist_ok=True)
    manifest=[]; skips=[]; gid=0
    for modpath in MODULES:
        full=os.path.join(MATHLIB, modpath)
        lines, events, decls = parse_module(full)
        for dstart, kwline, dend, m in decls:
            if gid >= MAXTHM: break
            name=m.group("name")
            block="\n".join(lines[kwline:dend]).rstrip()
            mm=DECL_RE.match(block); body=block[mm.end():]
            p=depth0_split(body)
            if not p: skips.append((name,"parse")); continue
            sig, stmt, proof = p
            if not proof.strip() or "where" in sig: skips.append((name,"no-proof/where")); continue
            depth_i, sc, vs = events[kwline]
            livevars=" ".join(t for d,t in vs)
            amb=[(c.group(1), c.group(2)) for c in
                 re.finditer(r'\[([A-Za-z][A-Za-z0-9]*)\s+([A-Za-zα-ω][\w₀-₉\']*)\]', livevars)]
            # every declared Type variable in scope (a single binder may declare several)
            tyvars=[]
            for vm in re.finditer(r'\{([^:{}]+):\s*Type', livevars): tyvars += vm.group(1).split()
            # prefer the type variable that actually carries a ladderable ambient class
            lad=[v for c,v in amb if c in CLASS_LADDER and v in tyvars]
            anyc=[v for c,v in amb if v in tyvars]
            tv = lad[0] if lad else (anyc[0] if anyc else (tyvars[0] if tyvars else None))
            # names the theorem's own signature already binds -> never re-bind them
            own=set()
            for o,c in (('(',')'),('{','}'),('[',']')):
                for a,b in groups(sig,o,c):
                    inner=sig[a+1:b]
                    if ':' in inner: own.update(inner.split(':',1)[0].split())
            valb=[]
            if tv:
                for vm in re.finditer(r'\{([^:{}]+):\s*'+re.escape(tv)+r'\}', livevars):
                    for nm in vm.group(1).split():
                        if nm in own: continue
                        if re.search(r'(?<![A-Za-z0-9_\'])'+re.escape(nm)+r'(?![A-Za-z0-9_\'])', sig+stmt+proof):
                            valb.append(nm)
            ctx=dict(amb=amb, tyv=tv, valbinders=valb, livevars=livevars)
            cells=[("baseline", None, 0, sig.strip(), stmt, proof)]
            caps={}
            for dname, fn in BUILDERS:
                try: outs, cap = fn(sig, stmt, proof, ctx)
                except Exception: outs, cap = [None]*3, 0
                caps[dname]=cap
                for k, o in zip(DEPTHS, outs):
                    if o is None: continue
                    cells.append(("cell", dname, k, o[0], o[1], o[2]))
            if all(c==0 for c in caps.values()): skips.append((name,"no applicable direction")); continue
            fname=f"P{gid:03d}"
            prefix=[]
            for l in lines[:with_doc(lines,dstart)]:
                dl=demod(l)
                if dl is not None: prefix.append(dl)
            closers=[f"end {nm}".strip() for kind,nm in reversed(sc)]
            entries=emit_theorem_file(fname, prefix, gid, cells, closers)
            manifest.append(dict(file=fname, gid=gid, theorem=name, module=modpath,
                                 caps=caps, n_hyp=len([1 for a,b in groups(sig,'(',')')
                                     if ':' in sig[a+1:b] and PROPISH.search(sig[a+1:b].split(':',1)[1])]),
                                 group="corpus", entries=entries))
            gid+=1
    # ---- harness-validity trivialities (decorative structure) ----
    for i in range(30):
        gid_t=gid+i
        sig=("{α : Type*} [CommGroup α] (a b : α) "
             f"(hd1_{i} : a = a) (hd2_{i} : b = b) (hd3_{i} : a * b = a * b)")
        stmt="a * 1 = a"; proof="mul_one a"
        ctx=dict(amb=[("CommGroup","α")], tyv="α", valbinders=[], livevars="{α : Type*} [CommGroup α]")
        cells=[("baseline",None,0,sig,stmt,proof)]; caps={}
        for dname, fn in BUILDERS:
            try: outs, cap = fn(sig, stmt, proof, ctx)
            except Exception: outs, cap = [None]*3, 0
            caps[dname]=cap
            for k,o in zip(DEPTHS,outs):
                if o is None: continue
                cells.append(("cell",dname,k,o[0],o[1],o[2]))
        entries=emit_theorem_file(f"T{i:03d}", ["import Mathlib",""], gid_t, cells, [])
        manifest.append(dict(file=f"T{i:03d}", gid=gid_t, theorem=f"triviality_{i}", module="<synthetic>",
                             caps=caps, n_hyp=3, group="trivial", entries=entries))
    json.dump({"decls":manifest,"skips":skips,
               "mathlib_sha":"8f9d9cff6bd728b17a24e163c9402775d9e6a365",
               "toolchain":"leanprover/lean4:v4.28.0","modules":MODULES},
              open(MAN,"w"), indent=0)
    ncell=sum(len([e for e in d["entries"] if e["role"]=="cell"]) for d in manifest)
    print(f"theorems={len([d for d in manifest if d['group']=='corpus'])} "
          f"trivialities={len([d for d in manifest if d['group']=='trivial'])} "
          f"skips={len(skips)} perturbation-cells={ncell}")
    cov={}
    for d in manifest:
        if d["group"]!="corpus": continue
        for k,v in d["caps"].items(): cov[k]=cov.get(k,0)+(1 if v>=1 else 0)
    n=len([d for d in manifest if d['group']=='corpus'])
    print("direction coverage (cap>=1):", {k:f"{v}/{n} ({100*v/max(1,n):.0f}%)" for k,v in sorted(cov.items())})

main()
