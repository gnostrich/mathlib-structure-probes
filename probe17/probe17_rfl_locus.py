#!/usr/bin/env python3
"""
rfl-locus confirmation run. Applies PREREG-rfl-locus.md mechanically.
CHECK A: D = AUC(declaration-level longest-path depth -> substantive), depth built from real
         dependency extraction (DumpDeps.lean / getUsedConstants over type AND value).
CHECK B: S = fraction of module-level variance in strict-definitional fraction explained by subject.
Harness: Logic+Init > Analysis; max depth within an order of magnitude of ~300; unwrapped rank check.
"""
import json, re, os, sys, collections, math
import numpy as np, networkx as nx
from sklearn.metrics import roc_auc_score

BASE = "/tmp/claude-0/-home-user-Structure-Backprop/a747742e-9a2f-5c79-9f64-ed3bc601f93e/scratchpad"
GRAPH = f"{BASE}/faithful/decl_deps.jsonl"
MLROOT = f"{BASE}/mathlib4"
TARGET = "AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType"

# ---------------- CHECK A part 1: build their depth ----------------
print("building declaration-level dependency DAG (route (a)) ...", flush=True)
G = nx.DiGraph(); module = {}; kind = {}; nval = {}
for line in open(GRAPH):
    r = json.loads(line); n = r["name"]
    module[n] = r.get("module", ""); kind[n] = r.get("kind", "")
    deps = list(dict.fromkeys(r.get("type_deps", []) + r.get("value_deps", [])))
    nval[n] = len(r.get("value_deps", []))
    G.add_node(n)
    for d in deps:
        if d != n: G.add_edge(n, d)          # edges point to dependencies
G.remove_edges_from(nx.selfloop_edges(G))
print(f"  vertices={G.number_of_nodes()} edges={G.number_of_edges()} "
      f"(Mathlib decls={len(module)}; the remainder are core/primitive targets)", flush=True)

print("collapsing SCCs ...", flush=True)
C = nx.condensation(G); mp = C.graph["mapping"]
ncomp = C.number_of_nodes()
nontriv = sum(1 for c in C.nodes if len(C.nodes[c]["members"]) > 1)
print(f"  {G.number_of_nodes()} -> {ncomp} vertices after condensation "
      f"({nontriv} non-trivial SCCs)", flush=True)

print("longest path to primitives ...", flush=True)
depthC = {}
for c in reversed(list(nx.topological_sort(C))):
    succ = list(C.successors(c))
    depthC[c] = (max(depthC[s] for s in succ) + 1) if succ else 0
depth = {n: depthC[mp[n]] for n in G.nodes}
dvals = np.array([depth[n] for n in module], dtype=float)
print(f"  max depth = {int(dvals.max())}  mean = {dvals.mean():.1f}  "
      f"(paper reports max ~300)", flush=True)

# multiplicity-blind unwrapped size, in log10 (soft check only)
print("unwrapped size (multiplicity-blind, log10) ...", flush=True)
logu = {}
for c in reversed(list(nx.topological_sort(C))):
    succ = list(C.successors(c))
    if not succ: logu[c] = 0.0
    else:
        m = max(logu[s] for s in succ)
        logu[c] = m + math.log10(sum(10 ** (logu[s] - m) for s in succ)) if m > -1e18 else 0.0
unw = {n: logu[mp[n]] for n in module}
top = sorted(unw.items(), key=lambda kv: -kv[1])[:5]
target_rank = None
order = sorted(unw.items(), key=lambda kv: -kv[1])
for i, (n, _) in enumerate(order):
    if n == TARGET: target_rank = i + 1; break
print(f"  top-5 by unwrapped(log10): {[(n.split('.')[-1][:38], round(v,1)) for n,v in top]}")
print(f"  paper's named largest element rank here: {target_rank} of {len(order)}"
      f"{' (present)' if TARGET in unw else ' (ABSENT)'}", flush=True)

# ---------------- classification from source (directive §5) ----------------
print("\nclassifying proofs from source text ...", flush=True)
DECL = re.compile(r'^(?P<attrs>(@\[[^\]]*\]\s*)*)(?P<mods>(private\s+|protected\s+|nonrec\s+|noncomputable\s+)*)'
                  r'(?P<kw>theorem|lemma)\s+(?P<name>[^\s({\[:⦃]+)')
TOP = re.compile(r'^(@\[|theorem\s|lemma\s|instance\b|def\s|abbrev\s|attribute\b|section\b|end\b|namespace\s|'
                 r'variable\b|open\s|/--|/-!|assert_not_exists|private\s|protected\s|noncomputable\b|deriving\b|'
                 r'#|example\b|local\b|scoped\b|set_option\b|universe\b)')
STRICT = {"rfl", "by rfl", "Iff.rfl", "by exact rfl", "HEq.rfl"}
SIMP = re.compile(r'^by\s+simp(\s+only)?\s*(\[[^\]]*\])?\s*$')

def split_proof(body):
    pairs = {'(':')','{':'}','[':']','⦃':'⦄'}; op=set(pairs); cl=set(pairs.values())
    d=0; j=0
    while j < len(body):
        c=body[j]
        if c in op: d+=1
        elif c in cl: d-=1
        elif d==0 and c==':' and j+1<len(body) and body[j+1]=='=': return body[j+2:]
        j+=1
    return None

rows=[]; per_module=collections.defaultdict(lambda: [0,0,0])   # strict, simp, substantive
for dirpath,_,files in os.walk(os.path.join(MLROOT,"Mathlib")):
    for fn in files:
        if not fn.endswith(".lean"): continue
        p=os.path.join(dirpath,fn)
        rel=os.path.relpath(p, MLROOT).replace("/",".")[:-5]
        try: lines=open(p,errors="ignore").read().split("\n")
        except Exception: continue
        ns=[]
        anchors=[i for i,l in enumerate(lines) if TOP.match(l)]
        def bend(st):
            for a in anchors:
                if a>st: return a
            return len(lines)
        i=0
        while i < len(lines):
            l=lines[i]
            m=re.match(r'^namespace\s+([^\s]+)\s*$', l.strip())
            if m: ns.append(m.group(1)); i+=1; continue
            if re.match(r'^end\b', l.strip()):
                mm=re.match(r'^end\s+([^\s]+)\s*$', l.strip())
                if mm and ns and ns[-1]==mm.group(1): ns.pop()
                i+=1; continue
            md=DECL.match(l)
            if not md: i+=1; continue
            e=bend(i+1); block="\n".join(lines[i:e])
            body=block[DECL.match(block).end():] if DECL.match(block) else ""
            pf=split_proof(body)
            i=e
            if pf is None: continue
            pf=" ".join(pf.split()).strip()
            nm=md.group("name")
            qn=".".join(ns+[nm]) if ns and not nm.startswith("_root_.") else nm.replace("_root_.","")
            if pf in STRICT: cls="strict"
            elif SIMP.match(pf): cls="simp"
            else: cls="substantive"
            rows.append((qn, rel, cls))
            per_module[rel][{"strict":0,"simp":1,"substantive":2}[cls]] += 1

tot=len(rows)
cs=collections.Counter(c for _,_,c in rows)
print(f"  classified {tot} theorem/lemma declarations")
print(f"  strict rfl = {cs['strict']/tot:.4f}   by simp = {cs['simp']/tot:.4f}   "
      f"substantive = {cs['substantive']/tot:.4f}")

# ---------------- CHECK A part 2: D = AUC(depth -> substantive) ----------------
joined=[(depth[q], 1 if c=="substantive" else 0, c) for q,_,c in rows if q in depth]
print(f"\njoin to graph: {len(joined)}/{tot} ({len(joined)/tot:.1%})")
dep=np.array([a for a,_,_ in joined],float); sub=np.array([b for _,b,_ in joined])
D = roc_auc_score(sub, dep)
print(f"  ** D = AUC(their depth -> substantive) = {D:.4f} **")
# elaborated-term cross-check: proof-side footprint of source-classified strict rfl
sv=[nval.get(q,0) for q,_,c in rows if c=="strict" and q in nval]
sb=[nval.get(q,0) for q,_,c in rows if c=="substantive" and q in nval]
print(f"  cross-check (elaborated proof-side value_deps): strict-rfl median={np.median(sv):.0f} "
      f"(n={len(sv)}) vs substantive median={np.median(sb):.0f} (n={len(sb)})")

# ---------------- CHECK B: S ----------------
def subject(mod):
    p=mod.split(".")
    return ".".join(p[:2]) if len(p)>=2 else mod

def var_expl(mods):
    y=np.array([per_module[m][0]/sum(per_module[m]) for m in mods])
    subj=[subject(m) for m in mods]
    gm=collections.defaultdict(list)
    for s,v in zip(subj,y): gm[s].append(v)
    means={s:np.mean(v) for s,v in gm.items()}
    pred=np.array([means[s] for s in subj])
    if np.var(y)==0: return float("nan"), len(mods), 0
    return 1 - np.var(y-pred)/np.var(y), len(mods), len(gm)

allm=[m for m in per_module if sum(per_module[m])>0]
big=[m for m in allm if sum(per_module[m])>=20]
S, nb, ng = var_expl(big)
S_all, na, ga = var_expl(allm)
w=np.array([sum(per_module[m]) for m in big],float)
yb=np.array([per_module[m][0]/sum(per_module[m]) for m in big])
subjb=[subject(m) for m in big]
gmw=collections.defaultdict(lambda:[0.0,0.0])
for s,v,ww in zip(subjb,yb,w): gmw[s][0]+=v*ww; gmw[s][1]+=ww
predw=np.array([gmw[s][0]/gmw[s][1] for s in subjb])
mu=np.average(yb,weights=w)
S_w = 1 - np.average((yb-predw)**2,weights=w)/np.average((yb-mu)**2,weights=w)
print(f"\n  ** S (primary: {nb} modules >=20 thms, {ng} subjects, unweighted) = {S:.4f} **")
print(f"     S (all {na} modules, {ga} subjects) = {S_all:.4f};  S (size-weighted) = {S_w:.4f}")

# ---------------- harness cell ----------------
def frac(prefix):
    st=sub_=0
    for m,(a,b,c) in per_module.items():
        if m.startswith(prefix): st+=a; sub_+=a+b+c
    return st/sub_ if sub_ else float("nan"), sub_
li_s=li_n=0
for pre in ("Mathlib.Logic","Mathlib.Init"):
    f,n=frac(pre)
    if n: li_s+=f*n; li_n+=n
li=li_s/li_n if li_n else float("nan")
an,ann=frac("Mathlib.Analysis")
print(f"\nHARNESS: Logic+Init strict definitional = {li:.4f} (n={li_n}) vs "
      f"Analysis = {an:.4f} (n={ann}) -> {'PASS' if li>an else 'FAIL'}")
maxd=int(dvals.max()); depth_ok = 30 <= maxd <= 3000
print(f"HARNESS: max depth = {maxd} (need 30-3000, paper ~300) -> {'PASS' if depth_ok else 'FAIL'}")
harness_ok = (li>an) and depth_ok

# ---------------- ladder ----------------
print("\n"+"="*72)
if not harness_ok: v="VOID — harness-validity cell failed; published as the verdict."
elif D>=0.75:      v=f"DEPTH-REDUCIBLE (D={D:.3f}) — it was depth all along. CLOSED."
elif S>=0.80:      v=f"SUBJECT-REDUCIBLE (S={S:.3f}) — it is what the file is about. CLOSED."
elif D<=0.60 and S<0.50: v=f"CONFIRMED (D={D:.3f}, S={S:.3f}) — native coordinate."
else:              v=f"PARTIAL (D={D:.3f}, S={S:.3f}) — report both, claim nothing beyond. TERMINAL."
print("VERDICT:", v); print("="*72)

json.dump(dict(D=float(D), S=float(S), S_all=float(S_all), S_weighted=float(S_w),
               max_depth=maxd, n_classified=tot, join=len(joined)/tot,
               strict=cs['strict']/tot, simp=cs['simp']/tot, substantive=cs['substantive']/tot,
               logic_init=li, analysis=an, target_rank=target_rank, n_modules_primary=nb,
               vertices=G.number_of_nodes(), condensed=ncomp, verdict=v),
          open(f"{BASE}/p17_report.json","w"), indent=1)
