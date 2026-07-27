#!/usr/bin/env python3
"""
Back-guess/back-actual deviation gate. Pre-reg: PREREG-deviation-gate.md.
back-actual = depth (max-generation); back-guessed = g (mean-generation, PROXY). Deviation =
residual of rank(g) on rank(depth). Four tests vs locked lines. Intrinsic only (no dates).
"""
import json, os, collections, numpy as np, networkx as nx
from scipy.stats import spearmanr, rankdata

BASE=os.environ.get("STYLE_BASE",".")
PATH=f"{BASE}/faithful/decl_deps.jsonl"
print("loading faithful graph ...", flush=True)
G=nx.DiGraph(); kind={}; module={}
for line in open(PATH):
    r=json.loads(line); n=r["name"]; kind[n]=r.get("kind",""); module[n]=r.get("module","")
    deps=r.get("deps") or list(dict.fromkeys(r.get("type_deps",[])+r.get("value_deps",[])))
    G.add_node(n)
    for d in deps:
        if d!=n: G.add_edge(n,d)
G.remove_edges_from(nx.selfloop_edges(G))
core=set(kind); G2=G.subgraph(core).copy()
nodes=list(G2.nodes()); N=len(nodes); nidx={n:i for i,n in enumerate(nodes)}
print(f"nodes={N} edges={G2.number_of_edges()}", flush=True)

print("condensation + edge multiplicities ...", flush=True)
Cg=nx.condensation(G2); mp=Cg.graph['mapping']
w=collections.Counter()
for u,v in G2.edges():
    cu,cv=mp[u],mp[v]
    if cu!=cv: w[(cu,cv)]+=1
succ=collections.defaultdict(list)
for (cu,cv),cnt in w.items(): succ[cu].append((cv,cnt))

print("depth (max-gen = back-actual) and g (mean-gen = back-guessed proxy) ...", flush=True)
depthC={}; gC={}
for c in reversed(list(nx.topological_sort(Cg))):
    ss=succ.get(c,[])
    if ss:
        depthC[c]=max(depthC[s]+1 for s,_ in ss)
        tot=sum(cnt for _,cnt in ss); gC[c]=1.0+sum(cnt*gC[s] for s,cnt in ss)/tot
    else:
        depthC[c]=0; gC[c]=0.0
depth=np.array([depthC[mp[n]] for n in nodes],float)
g=np.array([gC[mp[n]] for n in nodes],float)

rg=rankdata(g); rd=rankdata(depth)
raw=spearmanr(g,depth).correlation
# deviation = residual of rank(g) on rank(depth)
X=np.column_stack([rd,np.ones(N)]); beta,*_=np.linalg.lstsq(X,rg,rcond=None); dev=rg-X@beta
R2=1-((rg-X@beta)**2).sum()/((rg-rg.mean())**2).sum()

print("\n== DEVIATION GATE ==", flush=True)
print(f"  raw agreement Spearman(g, depth) = {raw:.3f}", flush=True)

# Test 1 magnitude
mag=1-R2
print(f"  [T1 magnitude] unforced fraction 1-R2(rank g~rank depth) = {mag:.3f}  (line >=0.15) "
      f"-> {'PASS' if mag>=0.15 else 'fail'}", flush=True)

# Test 2 concentration: top-decile |dev| mass
ad=np.abs(dev); order=np.argsort(ad)[::-1]; top=order[:N//10]
conc=ad[top].sum()/ad.sum()
print(f"  [T2 concentration] top-decile |dev| mass = {conc:.3f}  (noise~0.26; line >=0.40) "
      f"-> {'PASS' if conc>=0.40 else 'fail'}", flush=True)

# Test 3 reproducibility under tie-break perturbation
rng=np.random.default_rng(0)
def dev_perturbed(seed):
    r=np.random.default_rng(seed)
    rg2=rankdata(g + r.normal(0,g.std()*0.01,N))
    rd2=rankdata(depth + r.normal(0,depth.std()*0.01+1e-9,N))
    X2=np.column_stack([rd2,np.ones(N)]); b2,*_=np.linalg.lstsq(X2,rg2,rcond=None)
    return rg2-X2@b2
dev_p=dev_perturbed(1)
repro=spearmanr(dev,dev_p).correlation
print(f"  [T3 reproducibility] Spearman(dev, dev_perturbed) = {repro:.3f}  (line >=0.70) "
      f"-> {'PASS' if repro>=0.70 else 'fail'}", flush=True)

# Test 4 clusters: module-concentration of top-decile-|dev| nodes vs shuffle null
def subj(m): return m  # full module = finest region
mod=np.array([module[n] for n in nodes])
istop=np.zeros(N,bool); istop[top]=True
bymod=collections.defaultdict(list)
for i in range(N): bymod[mod[i]].append(i)
def modconc(mask):
    # mean over top nodes of (fraction of same-module OTHER nodes that are also top)
    vals=[]
    for i in np.where(mask)[0]:
        mm=bymod[mod[i]]
        if len(mm)>1:
            other=[j for j in mm if j!=i]
            vals.append(np.mean([mask[j] for j in other]))
    return np.mean(vals) if vals else 0.0
obs=modconc(istop)
nulls=[]
for s in range(20):
    r=np.random.default_rng(100+s); m=np.zeros(N,bool); m[r.choice(N,len(top),replace=False)]=True
    nulls.append(modconc(m))
nullm=np.mean(nulls); ratio=obs/max(1e-9,nullm)
print(f"  [T4 clusters] top-dev module-concentration obs={obs:.3f} vs null={nullm:.3f} "
      f"ratio={ratio:.2f}x  (line >=1.5) -> {'cluster-structure' if ratio>=1.5 else 'no extra clustering'}", flush=True)

print("\n== VERDICT (locked lines; proxy => DEAD is provisional) ==", flush=True)
t1=mag>=0.15; t2=conc>=0.40; t3=repro>=0.70
if t1 and t2 and t3:
    print(f"  ALIVE: structured, reproducible unforced order-content exists "
          f"(mag={mag:.2f}, conc={conc:.2f}, repro={repro:.2f})."
          f" Hypergraph-flow design warranted{' — cluster-structure present, hypergraph justified' if ratio>=1.5 else ''}.", flush=True)
else:
    fails=[n for n,ok in [('magnitude',t1),('concentration',t2),('reproducibility',t3)] if not ok]
    print(f"  DEAD (PROVISIONAL ON PROXY): failed {fails}. Guess vs truth differ by forced topology + noise;"
          f" nothing learnable on THIS proxy. Retest only if the real Gibbs object is wired.", flush=True)
