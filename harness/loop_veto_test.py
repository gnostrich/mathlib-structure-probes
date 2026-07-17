#!/usr/bin/env python3
"""
loop_veto_test.py — decisive decl-level dissociation + significance test.
Pre-registration in docs/03. Reads either:
  - decl_deps.jsonl       (DumpDeps.lean: name,module,kind,type_deps,value_deps)  FAITHFUL
  - decl_ref_graph.jsonl  (decl_dep_extract.py: name,kind,deps)                    APPROX
Runs H1 (dissociation) and H2 (loop predicts significance beyond slide). H3
(incorruptibility: gaming foil + warm/cold floor) needs the prover -> hooks only.

CORRECTED pre-reg reads: WALL if |rho(L,S)|>=0.7 OR R2(L~S)>=0.75 OR H2 fails.
GO if |rho|<=0.4 AND R2<=0.5 AND both cells populated AND H2 clears AND foils ok.
"""
import sys, json, collections
import networkx as nx, numpy as np
from scipy.stats import spearmanr, rankdata

path = sys.argv[1] if len(sys.argv)>1 else "decl_deps.jsonl"
G=nx.DiGraph(); kind={}
for line in open(path):
    r=json.loads(line); n=r["name"]; kind[n]=r.get("kind","")
    deps=r.get("deps") or (list(dict.fromkeys((r.get("type_deps",[])+r.get("value_deps",[])))))
    G.add_node(n)
    for d in deps:
        if d!=n: G.add_edge(n,d)
G.remove_edges_from(nx.selfloop_edges(G))
# keep only nodes we have kind for (declared Mathlib decls), drop external leaves
core=set(kind); 
G2=G.subgraph(core).copy()
nodes=[n for n in G2.nodes() if kind.get(n)]
print(f"nodes={len(nodes)} edges={G2.number_of_edges()}")

indeg=dict(G2.in_degree())                       # times-used (SLIDE & also Y2 proxy)
UG=G2.to_undirected()
# depth-from-axioms: longest chain along dependencies (condense SCCs for safety)
Cg=nx.condensation(G2); cdep={}
for c in nx.topological_sort(Cg):
    ds=[cdep[s]+1 for s in Cg.successors(c) if s in cdep]; cdep[c]=max(ds) if ds else 0
mp=Cg.graph['mapping']; depth={n:cdep[mp[n]] for n in nodes}
sq=nx.square_clustering(UG); tri=nx.triangles(UG)

xi=np.array([indeg[n] for n in nodes],float)
xd=np.array([depth[n] for n in nodes],float)
L =np.array([tri[n]  for n in nodes],float)      # LOOP (swap in birth-simplex when available)
# SLIDE composite = proof-size proxy(depth) + degree; keep in-degree separate for Y2 to avoid circularity
S =np.array([depth[n] for n in nodes],float)     # use depth as the non-circular slide axis
Y1=np.array([1.0 if kind[n]=="theorem" else 0.0 for n in nodes])   # human label
Y2=np.log1p(xi)                                                    # in-library citation proxy

def rankres(a,b):  # residual of a after regressing (rank) on b -> for partial Spearman
    ra,rb=rankdata(a),rankdata(b); B=np.polyfit(rb,ra,1); return ra-(B[0]*rb+B[1])
def partial_spear(a,b,ctrl):
    return spearmanr(rankres(a,ctrl),rankres(b,ctrl)).correlation

print("\n== H1 dissociation ==")
rho=spearmanr(L,S).correlation; rho_deg=spearmanr(L,xi).correlation
print(f"  rho(L, slide=depth)={rho:.3f}   rho(L, in-degree)={rho_deg:.3f}")
X=np.column_stack([S,np.log1p(xi),np.ones_like(S)]); beta,*_=np.linalg.lstsq(X,L,rcond=None)
R2=1-((L-X@beta)**2).sum()/((L-L.mean())**2).sum(); print(f"  R2(L ~ slide+deg)={R2:.3f}")
def terc(a):
    q1,q2=np.quantile(a,[1/3,2/3]); return np.where(a<=q1,0,np.where(a<=q2,1,2))
ct=collections.Counter(zip(terc(S),terc(L)))
print(f"  cells: high-slide/low-loop={ct.get((2,0),0)}  low-slide/high-loop={ct.get((0,2),0)}")

print("\n== H2 loop predicts significance beyond slide (PAYOFF) ==")
for name,Y in [("Y1 thm/lemma",Y1),("Y2 log in-deg",Y2)]:
    pr=partial_spear(L,Y,S)
    print(f"  partial rho(L, {name} | slide)={pr:.3f}")

print("\n== H3 incorruptibility (HOOKS - need prover) ==")
print("  TODO(a) gaming foil: synthesize A∧B nodes for distant A,B; assert L not credited")
print("  TODO(b) warm/cold floor: reprove sample minimally; L_cold=survivor; veto uses L_cold only")

print("\n== VERDICT (fill H2 bar + H3 before GO) ==")
wall = abs(rho)>=0.7 or R2>=0.75
go_pre = abs(rho)<=0.4 and R2<=0.5 and ct.get((2,0),0)>0 and ct.get((0,2),0)>0
print(f"  H1: {'WALL' if wall else ('GO-precondition' if go_pre else 'AMBIGUOUS')}")
print("  (H2 GO requires partial rho(L,Y|S) significantly >0 with correct sign; H3 foils must not be credited)")
