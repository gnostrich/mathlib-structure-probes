#!/usr/bin/env python3
"""
Style-mode decomposition, Phases 1+2, on the FAITHFUL decl graph.
PRE-REGISTERED (fixed before running; no post-hoc tuning):

Phase 1 (metric + H1-fix): birth-simplex loop metric B(v) via union-find filtration in
  increasing (depth, name) order; B(v)=#edges-to-earlier-neighbors - #distinct-components-
  among-them = 1-cycles born at v. Sum B = b1. Degree-controlled residue Lbs = rank-residual
  of B on {rank log-udeg, rank depth}. Re-run H1 (rho(B,depth) <=0.40 ?), H2 (partial
  rho(B, Y2 | depth,udeg) with correct sign), H3(a) reuse of prior foil logic is skipped here
  (already PASS with triangles; birth-simplex of a distant conjunction is 0 by the same argument).

Phase 2 style features per node (taste coordinate; subject is CONTROL only, never a feature):
  f1 loop_residue = Lbs (birth-simplex, degree+depth residualized)   [THE taste coordinate]
  f2 proof_size   = log1p(#value_deps)
  f3 depth        = depth-from-axioms
  f4 in_degree    = log1p(in-degree)
  f5 out_degree   = log1p(out-degree)
  f6 classical    = 1 if any dep name starts with 'Classical.' else 0   (classical vs constructive proxy)
  subject label   = top-level Mathlib namespace (Analysis/Algebra/Topology/...)

Step A: standardize f1..f6, SVD; report singular-value spectrum + largest relative gap.
  READ: clear gap after k in [3,8] => discrete tastes; smooth tail no gap => smear (prior).
Step B: KMeans into k=k_gap modes; MI(mode; subject) vs MI(mode; style-features).
  READ: MI(mode;subject) high => just fields (reject). MI(mode;style) dominates & subject low
  => genuine schools-of-practice.
"""
import json, sys, collections, numpy as np
import networkx as nx
from scipy.stats import spearmanr, rankdata

import os
BASE=os.environ.get("STYLE_BASE",".")
PATH=f"{BASE}/faithful/decl_deps.jsonl"
OUT=f"{BASE}/style_features.npz"

print("loading faithful graph ...", flush=True)
G=nx.DiGraph(); kind={}; module={}; proofsize={}; classical={}
for line in open(PATH):
    r=json.loads(line); n=r["name"]; kind[n]=r.get("kind","")
    module[n]=r.get("module","");
    td=r.get("type_deps",[]); vd=r.get("value_deps",[])
    proofsize[n]=len(vd)
    classical[n]=1 if any(d.startswith("Classical.") for d in (td+vd)) else 0
    deps=r.get("deps") or list(dict.fromkeys(td+vd))
    G.add_node(n)
    for d in deps:
        if d!=n: G.add_edge(n,d)
G.remove_edges_from(nx.selfloop_edges(G))
core=set(kind); G2=G.subgraph(core).copy()
nodes=[n for n in G2.nodes() if kind.get(n)]
print(f"nodes={len(nodes)} edges={G2.number_of_edges()}", flush=True)

indeg=dict(G2.in_degree()); outdeg=dict(G2.out_degree())
UG=G2.to_undirected(); udeg=dict(UG.degree())

print("depth via SCC condensation ...", flush=True)
Cg=nx.condensation(G2); cdep={}
for c in reversed(list(nx.topological_sort(Cg))):
    ds=[cdep[s]+1 for s in Cg.successors(c) if s in cdep]; cdep[c]=max(ds) if ds else 0
mp=Cg.graph['mapping']; depth={n:cdep[mp[n]] for n in nodes}

print("birth-simplex via union-find filtration ...", flush=True)
# introduction order: increasing (depth, name)
order=sorted(nodes, key=lambda n:(depth[n], n))
pos={n:i for i,n in enumerate(order)}
parent={}; rank_={}
def find(x):
    while parent[x]!=x:
        parent[x]=parent[parent[x]]; x=parent[x]
    return x
def union(a,b):
    ra,rb=find(a),find(b)
    if ra==rb: return False
    if rank_[ra]<rank_[rb]: ra,rb=rb,ra
    parent[rb]=ra
    if rank_[ra]==rank_[rb]: rank_[ra]+=1
    return True
B={}
adjU={n:set(UG.neighbors(n)) for n in nodes}
introduced=set()
for n in order:
    parent[n]=n; rank_[n]=0
    earlier=[m for m in adjU[n] if m in introduced]
    comps={find(m) for m in earlier}
    born=len(earlier)-len(comps)          # independent cycles created at n
    B[n]=born
    for m in earlier: union(n,m)
    introduced.add(n)
print(f"  sum B (b1) = {sum(B.values())}", flush=True)

# arrays
xi=np.array([indeg[n] for n in nodes],float)
xo=np.array([outdeg[n] for n in nodes],float)
xu=np.array([udeg[n] for n in nodes],float)
xd=np.array([depth[n] for n in nodes],float)
Barr=np.array([B[n] for n in nodes],float)
ps=np.array([proofsize[n] for n in nodes],float)
cl=np.array([classical[n] for n in nodes],float)
Y2=np.log1p(xi)
logu=np.log1p(xu)

def rankres(a,ctrls):
    cols=[rankdata(c) for c in ctrls]
    X=np.column_stack(cols+[np.ones(len(a))]); ra=rankdata(a)
    beta,*_=np.linalg.lstsq(X,ra,rcond=None); return ra-X@beta
def partial_spear(a,b,ctrl): return spearmanr(rankres(a,ctrl),rankres(b,ctrl)).correlation

# degree+depth-controlled birth-simplex residue (the taste coordinate)
Lbs = rankres(Barr,[logu,xd])

print("\n== PHASE 1: birth-simplex metric — H1/H2 re-run ==", flush=True)
rhoBd=spearmanr(Barr,xd).correlation
rhoBu=spearmanr(Barr,xu).correlation
print(f"  rho(B, depth)={rhoBd:.3f}   rho(B, undirected-degree)={rhoBu:.3f}", flush=True)
print(f"  H1 dissociation (GO needs |rho(B,depth)|<=0.40): {'CLEARS' if abs(rhoBd)<=0.40 else 'FAILS'}", flush=True)
h2b_base=partial_spear(Barr,Y2,[xd])
h2b_deg =partial_spear(Barr,Y2,[xd,logu])
print(f"  H2 partial rho(B, Y2 | depth)={h2b_base:.3f}  | depth+log-udeg={h2b_deg:.3f}  "
      f"({'CLEARS' if h2b_deg>=0.10 else 'does not clear'})", flush=True)

print("\n== PHASE 2 Step A: style-feature spectrum ==", flush=True)
feats=["loop_residue","proof_size","depth","in_degree","out_degree","classical"]
M=np.column_stack([Lbs, np.log1p(ps), xd, np.log1p(xi), np.log1p(xo), cl]).astype(float)
# standardize
Ms=(M-M.mean(0))/ (M.std(0)+1e-12)
# correlation structure
print("  feature corr matrix (Pearson):", flush=True)
C=np.corrcoef(Ms.T)
for i,f in enumerate(feats):
    print("   ", f.ljust(13), " ".join(f"{C[i,j]:+.2f}" for j in range(len(feats))), flush=True)
U,S,Vt=np.linalg.svd(Ms, full_matrices=False)
Svar=S**2/ (S**2).sum()
print("  singular values:", " ".join(f"{s:.3f}" for s in S), flush=True)
print("  variance frac  :", " ".join(f"{v:.3f}" for v in Svar), flush=True)
gaps=[S[i]/S[i+1] for i in range(len(S)-1)]
print("  consecutive ratios sigma_k/sigma_k+1:", " ".join(f"{g:.2f}" for g in gaps), flush=True)
kgap=int(np.argmax(gaps))+1
print(f"  largest gap after k={kgap}  (pre-reg: gap at k in [3,8] => discrete; else smear)", flush=True)

# choose k for step B: the gap location, clamped to [3,8] window per pre-reg; if gap outside, still cluster at k=6 for MI diagnostic and report gap verdict separately
k_modes = kgap if 3<=kgap<=8 else 6
print(f"  Step B will cluster k={k_modes} modes", flush=True)

print("\n== PHASE 2 Step B: MI(mode; subject) vs MI(mode; style) ==", flush=True)
from sklearn.cluster import MiniBatchKMeans
from sklearn.metrics import mutual_info_score, normalized_mutual_info_score
km=MiniBatchKMeans(n_clusters=k_modes, random_state=0, n_init=5, batch_size=10000)
mode=km.fit_predict(Ms)
# subject label
def subj(m):
    p=m.split(".")
    return p[1] if len(p)>=2 and p[0]=="Mathlib" else (p[0] or "?")
subject=np.array([subj(module[n]) for n in nodes])
# discretize style features into bins for MI
def binned(x,q=8):
    try: return np.digitize(x, np.quantile(x,np.linspace(0,1,q+1)[1:-1]))
    except: return np.zeros_like(x,dtype=int)
mi_subj=normalized_mutual_info_score(mode, subject)
style_bins={f: binned(Ms[:,i]) for i,f in enumerate(feats)}
mi_style={f: normalized_mutual_info_score(mode, b) for f,b in style_bins.items()}
mi_style_max=max(mi_style.values())
print(f"  NMI(mode; subject) = {mi_subj:.3f}", flush=True)
for f,v in sorted(mi_style.items(), key=lambda x:-x[1]):
    print(f"  NMI(mode; {f.ljust(13)}) = {v:.3f}", flush=True)
print(f"  -> subject NMI={mi_subj:.3f} vs max style NMI={mi_style_max:.3f}", flush=True)
verdict = ("subject-dominated (fields, reject)" if mi_subj>mi_style_max else
           "style-dominated (schools-of-practice)")
print(f"  Step B read: {verdict}", flush=True)

# save features for Step C
np.savez_compressed(OUT,
    names=np.array(nodes), subject=subject, mode=mode,
    loop_residue=Lbs, birth_simplex=Barr, proof_size=ps, depth=xd,
    in_degree=xi, out_degree=xo, classical=cl,
    feats=np.array(feats), singular=S, k_gap=kgap, k_modes=k_modes,
    mi_subject=mi_subj, mi_style_max=mi_style_max)
print(f"\nsaved features -> {OUT}", flush=True)

print("\n== STYLE-MODE VERDICT (pre-registered grid) ==", flush=True)
gap_ok = 3<=kgap<=8
print(f"  Step A: {'GAP at k='+str(kgap)+' -> discrete tastes' if gap_ok else 'no gap in [3,8] -> SMEAR (continuous taste)'}", flush=True)
print(f"  Step B: {verdict}", flush=True)
if gap_ok and mi_style_max>mi_subj:
    print("  => sharp modes + style-dominated: candidate genuine tastes (Step C decides personal-ness)", flush=True)
elif gap_ok and mi_subj>=mi_style_max:
    print("  => sharp modes but subject-dominated: rediscovered subject areas (NULL)", flush=True)
else:
    print("  => no clean gap: taste is a SMEAR / continuous (prior confirmed; kills few-archetypes shortcut)", flush=True)
