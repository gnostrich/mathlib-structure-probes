#!/usr/bin/env python3
"""
Phase 0 (PREREG-conjecturer.md): degree-normalized-by-construction loop metric Lnorm
(configuration-model triangle residue) and the H1/H2/H3 robustness re-test on the
faithful decl graph. Thresholds fixed in the pre-reg; report whatever comes out.
"""
import json, sys, os, collections, numpy as np, networkx as nx
from scipy.stats import spearmanr, rankdata

BASE=os.environ.get("STYLE_BASE",".")
PATH=sys.argv[1] if len(sys.argv)>1 else f"{BASE}/faithful/decl_deps.jsonl"

print("loading faithful graph ...", flush=True)
G=nx.DiGraph(); kind={}
for line in open(PATH):
    r=json.loads(line); n=r["name"]; kind[n]=r.get("kind","")
    deps=r.get("deps") or list(dict.fromkeys(r.get("type_deps",[])+r.get("value_deps",[])))
    G.add_node(n)
    for d in deps:
        if d!=n: G.add_edge(n,d)
G.remove_edges_from(nx.selfloop_edges(G))
core=set(kind); G2=G.subgraph(core).copy()
nodes=[n for n in G2.nodes() if kind.get(n)]
print(f"nodes={len(nodes)} edges={G2.number_of_edges()}", flush=True)

indeg=dict(G2.in_degree())
UG=G2.to_undirected(); udeg=dict(UG.degree())
m=UG.number_of_edges(); twoM=2.0*m
print("triangles ...", flush=True)
tri=nx.triangles(UG)

print("configuration-model expected triangles E_v ...", flush=True)
# E_v = 0.5 * ((sum d_i)^2 - sum d_i^2)/(2m),  d_i = k_i - 1  over undirected neighbors i of v
E={}
deg=udeg
for v in nodes:
    s1=0.0; s2=0.0
    for w in UG.neighbors(v):
        d=deg[w]-1.0
        s1+=d; s2+=d*d
    E[v]=0.5*max(0.0,(s1*s1 - s2))/twoM

print("depth via SCC condensation ...", flush=True)
Cg=nx.condensation(G2); cdep={}
for c in reversed(list(nx.topological_sort(Cg))):
    ds=[cdep[s]+1 for s in Cg.successors(c) if s in cdep]; cdep[c]=max(ds) if ds else 0
mp=Cg.graph['mapping']; depth={n:cdep[mp[n]] for n in nodes}

xu=np.array([udeg[n] for n in nodes],float)
xi=np.array([indeg[n] for n in nodes],float)
xd=np.array([depth[n] for n in nodes],float)
T =np.array([tri[n] for n in nodes],float)
Ev=np.array([E[n]  for n in nodes],float)
Lnorm=(T-Ev)/np.sqrt(Ev+1.0)                 # degree-normalized-by-construction loop residue
ratio=T/(Ev+1.0)
Cc=np.array([ (2.0*tri[n])/(udeg[n]*(udeg[n]-1)) if udeg[n]>1 else 0.0 for n in nodes])  # clustering coeff
Y2=np.log1p(xi)
Y1=np.array([1.0 if kind[n]=="theorem" else 0.0 for n in nodes])
logu=np.log1p(xu)

def rankres(a,ctrls):
    cols=[rankdata(c) for c in ctrls]; X=np.column_stack(cols+[np.ones(len(a))]); ra=rankdata(a)
    beta,*_=np.linalg.lstsq(X,ra,rcond=None); return ra-X@beta
def pspear(a,b,ctrl): return spearmanr(rankres(a,ctrl),rankres(b,ctrl)).correlation

print("\n== PHASE 0: degree-normalized loop metric Lnorm (config-model triangle residue) ==", flush=True)
print(f"  b1-ish: sum T={T.sum():.0f}  sum E={Ev.sum():.0f}", flush=True)
print(f"  DEGREE DECOUPLING (design goal: LOW):", flush=True)
print(f"    rho(rawT, degree)  = {spearmanr(T,xu).correlation:.3f}", flush=True)
print(f"    rho(Lnorm, degree) = {spearmanr(Lnorm,xu).correlation:.3f}   "
      f"rho(ratio,degree)={spearmanr(ratio,xu).correlation:.3f}   rho(clust,degree)={spearmanr(Cc,xu).correlation:.3f}", flush=True)
print(f"  H1 dissociation rho(Lnorm, depth) = {spearmanr(Lnorm,xd).correlation:.3f}  "
      f"(GO<=0.40, wall>=0.70)", flush=True)
print("  H2 payoff (partial Spearman), Lnorm vs each Y:", flush=True)
for yn,Y in [("Y2 log in-deg (degree-linked)",Y2),("Y1 thm/lemma (degree-INDEP)",Y1)]:
    b=pspear(Lnorm,Y,[xd]); dctl=pspear(Lnorm,Y,[xd,logu])
    print(f"    {yn:32s} | depth={b:+.3f}   | depth+log-deg={dctl:+.3f}", flush=True)
print("  (for reference, raw triangle metric:)", flush=True)
print(f"    rawT vs Y2 | depth={pspear(T,Y2,[xd]):+.3f}  | depth+log-deg={pspear(T,Y2,[xd,logu]):+.3f}", flush=True)

# H3(a) forward foil: distant A^B -> node with 2 edges to non-adjacent, no-common-neighbor A,B.
# Its T=0 and E≈0 (its 2 neighbors have their own degrees but the node's own triangle exp is ~0),
# so Lnorm≈0. Demonstrate on injected foils.
rng=np.random.default_rng(20260717)
adj={n:set(UG.neighbors(n)) for n in nodes}
NL=nodes; K=2000; foils=[]
idx=rng.integers(0,len(NL),size=(K*8,2))
for a_i,b_i in idx:
    if len(foils)>=K: break
    a,b=NL[a_i],NL[b_i]
    if a==b or b in adj[a] or (adj[a]&adj[b]): continue
    foils.append((a,b))
Gf=UG.copy(); fn=[]
for i,(a,b) in enumerate(foils):
    c=f"__FOIL_{i}"; fn.append(c); Gf.add_edge(c,a); Gf.add_edge(c,b)
trf=nx.triangles(Gf, fn)
# foil Lnorm: T=trf (should be 0), E from its 2 neighbors
def foilE(c):
    ns=list(Gf.neighbors(c)); s1=sum(udeg.get(x,Gf.degree(x))-1 for x in ns); s2=sum((udeg.get(x,Gf.degree(x))-1)**2 for x in ns)
    return 0.5*max(0.0,s1*s1-s2)/twoM
cred=sum(1 for c in fn if ((trf[c]-foilE(c))/np.sqrt(foilE(c)+1))>0.5)
print(f"  H3(a) forward foil: {cred}/{len(fn)} distant A^B foils get Lnorm>0.5 (want ~0)", flush=True)

# save Lnorm-based node scores for Phase 1 reuse
np.savez_compressed(f"{BASE}/phase0_lnorm.npz",
    names=np.array(nodes), Lnorm=Lnorm, triangles=T, E=Ev, depth=xd, udeg=xu, indeg=xi)

# verdict
dctl_Y2=pspear(Lnorm,Y2,[xd,logu]); dctl_Y1=pspear(Lnorm,Y1,[xd,logu])
decoupled = abs(spearmanr(Lnorm,xu).correlation) < 0.4
print("\n== PHASE 0 VERDICT ==", flush=True)
print(f"  metric degree-decoupled: {decoupled} (rho(Lnorm,deg)={spearmanr(Lnorm,xu).correlation:.3f})", flush=True)
print(f"  H2 degree-controlled: Y2(citation)={dctl_Y2:+.3f}  Y1(degree-indep label)={dctl_Y1:+.3f}", flush=True)
if decoupled and dctl_Y2>=0.20:
    print("  => PASS on the degree-linked citation proxy (signal is not a raw-count artifact).", flush=True)
    print(f"     Degree-INDEPENDENT Y check: {'also positive' if dctl_Y1>=0.10 else 'weak/absent (Y1~0)'} "
          f"-> {'robust' if dctl_Y1>=0.10 else 'holds mainly vs degree-linked Y — note in read'}", flush=True)
else:
    print("  => FAIL: degree-normalized metric does not carry the H2 signal — judge was metric/degree-fragile.", flush=True)
