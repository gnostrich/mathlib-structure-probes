# Mathlib slide/loop dissociation PRE-TEST (module import graph, coarse)
# PRE-REG reads (corrected): WALL if |rho|>=0.7 OR loop-R2>=0.75 ; GO if |rho|<=0.4 AND loop-R2<=0.5 & both off-diag cells populated ; else AMBIGUOUS
# Result: no wall; sqclust track = GO, triangle track = borderline. Module-level only; NOT a theorem-significance test.
# NEXT: declaration-level graph w/ proof edges + significance ground-truth + warm/cold floor (run in Claude Code).
import os, re, collections
import networkx as nx, numpy as np
from scipy.stats import spearmanr
root="mathlib4"
def p2m(p): rel=os.path.relpath(p,root); return rel[:-5].replace(os.sep,".")
files=[os.path.join(dp,f) for dp,_,fs in os.walk(os.path.join(root,"Mathlib")) for f in fs if f.endswith(".lean")]
mods=set(p2m(p) for p in files)
imp_re=re.compile(r'^\s*(?:public\s+|private\s+|protected\s+|meta\s+)*import\s+(?:all\s+)?(Mathlib(?:\.[A-Za-z0-9_]+)+)')
stop_re=re.compile(r'^\s*(/-!|namespace|section|open\b|theorem|lemma|def |instance|variable|noncomputable|structure|class |inductive|abbrev|example|@\[|attribute|notation|scoped|universe)')
def imports_of(p):
    out=[]; incmt=0
    for line in open(p,errors="ignore"):
        s=line.strip()
        # handle block comments /- ... -/ (not the import lines)
        if incmt:
            if '-/' in s: incmt=0
            continue
        if s.startswith('/-') and not s.startswith('/-!'):
            if '-/' not in s: incmt=1
            continue
        mm=imp_re.match(line)
        if mm: out.append(mm.group(1)); continue
        if s=='' or s=='module' or s.startswith('set_option') or s=='prelude': 
            continue
        if stop_re.match(line):  # first real command → import block ended
            break
    return out
G=nx.DiGraph(); G.add_nodes_from(mods)
for p in files:
    m=p2m(p)
    for t in imports_of(p):
        if t in mods and t!=m: G.add_edge(m,t)
V=G.number_of_nodes(); E=G.number_of_edges(); UG=G.to_undirected()
C=nx.number_connected_components(UG); b1=UG.number_of_edges()-V+C
isdag=nx.is_directed_acyclic_graph(G)
sccs=[len(s) for s in nx.strongly_connected_components(G)]
print(f"V={V} E={E} comps={C} b1={b1} b1/V={b1/V:.2f} is_DAG={isdag} top_SCC={sorted(sccs,reverse=True)[:3]}")
indeg=dict(G.in_degree())
depth={}
for n in reversed(list(nx.topological_sort(G))):
    ds=[depth[s]+1 for s in G.successors(n) if s in depth]; depth[n]=max(ds) if ds else 0
sq=nx.square_clustering(UG); tri=nx.triangles(UG)
nodes=list(mods)
xi=np.array([indeg[n] for n in nodes],float); xd=np.array([depth[n] for n in nodes],float)
ys=np.array([sq[n] for n in nodes],float); yt=np.array([tri[n] for n in nodes],float)
def rep(nm,a,b): r,_=spearmanr(a,b); print(f"  {nm}: rho={r:.3f}")
print("\n== PRIMARY loop vs slide ==")
rep("sqclust ~ indeg",ys,xi); rep("triangles ~ indeg",yt,xi)
rep("sqclust ~ depth",ys,xd); rep("triangles ~ depth",yt,xd); rep("sqclust ~ triangles",ys,yt)
X=np.column_stack([np.log1p(xi),xd,np.ones_like(xi)])
for nm,y in [("sqclust",ys),("log-tri",np.log1p(yt))]:
    beta,*_=np.linalg.lstsq(X,y,rcond=None); yh=X@beta
    R2=1-((y-yh)**2).sum()/((y-y.mean())**2).sum(); print(f"  loop-R^2 [{nm} ~ log(indeg)+depth]={R2:.3f}")
def terc(a): q1,q2=np.quantile(a,[1/3,2/3]); return np.where(a<=q1,0,np.where(a<=q2,1,2))
ts=terc(xi); tl=terc(yt); ct=collections.Counter(zip(ts,tl))
print("\n== tercile xtab rows=slide(indeg) cols=loop(triangles) L/M/H ==")
for s in range(3): print("  ",[ct.get((s,l),0) for l in range(3)])
print(f"  high-slide/low-loop={ct.get((2,0),0)}  low-slide/high-loop={ct.get((0,2),0)}")
print(f"\ntriangles: frac-zero={(yt==0).mean():.3f} q90={np.quantile(yt,.9):.0f} q99={np.quantile(yt,.99):.0f} max={yt.max():.0f}")
