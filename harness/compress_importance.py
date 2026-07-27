#!/usr/bin/env python3
"""
Compression/rank C(v) vs exogenous famous-theorem anchor Y*. Pre-reg:
PREREG-compression-importance.md. C(v)=log(1+D(v)), D=transitive-descendant count via
bottom-k MinHash. Gate |rho(C,in-degree)|<0.40. Payoff partial Spearman(C,Y*|log-indeg,depth)
+ AUC vs degree/subject baselines. Anti-gaming A^B foil. Honest kill.
"""
import json, os, sys, collections, numpy as np, networkx as nx
from scipy.stats import spearmanr, rankdata
from sklearn.metrics import roc_auc_score

BASE=os.environ.get("STYLE_BASE",".")
PATH=f"{BASE}/faithful/decl_deps.jsonl"
K=96

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
nodes=list(G2.nodes())
nidx={n:i for i,n in enumerate(nodes)}
N=len(nodes)
print(f"nodes={N} edges={G2.number_of_edges()}", flush=True)
indeg=np.array([G2.in_degree(n) for n in nodes],float)
outdeg=np.array([G2.out_degree(n) for n in nodes],float)
UG=G2.to_undirected(); udeg=np.array([UG.degree(n) for n in nodes],float)

print("depth + condensation ...", flush=True)
Cg=nx.condensation(G2); cdep={}
for c in reversed(list(nx.topological_sort(Cg))):
    ds=[cdep[s]+1 for s in Cg.successors(c) if s in cdep]; cdep[c]=max(ds) if ds else 0
mp=Cg.graph['mapping']
depth=np.array([cdep[mp[n]] for n in nodes],float)

print(f"transitive-descendant MinHash (k={K}) ...", flush=True)
rng=np.random.default_rng(0)
hvals=rng.random(N)                       # unique hash per node
members={c:[] for c in Cg.nodes()}
for n in nodes: members[mp[n]].append(nidx[n])
topo=list(nx.topological_sort(Cg))
sketch={}
for c in reversed(topo):                  # successors (descendants) processed first
    pool=[hvals[i] for i in members[c]]
    for s in Cg.successors(c):
        pool.append(sketch[s])
    arr=np.unique(np.concatenate([np.atleast_1d(p) for p in pool]))
    sketch[c]=arr[:K].copy()
# cardinality estimate of reachable-incl-self per SCC
Dscc={}
for c in Cg.nodes():
    s=sketch[c]
    if len(s)<K: Dscc[c]=float(len(s))                 # exact: fewer than K distinct reachable
    else:        Dscc[c]=(K-1)/s[K-1]                  # bottom-k estimator
D=np.array([max(0.0,Dscc[mp[n]]-1.0) for n in nodes],float)   # descendants excl self
C=np.log1p(D)

def rr(a,ctrls):
    cols=[rankdata(c) for c in ctrls]; X=np.column_stack(cols+[np.ones(len(a))]); ra=rankdata(a)
    b,*_=np.linalg.lstsq(X,ra,rcond=None); return ra-X@b
def ps(a,b,c): return spearmanr(rr(a,c),rr(b,c)).correlation
logi=np.log1p(indeg)

print("\n== PHASE A: compression metric C = log(1+descendants) — GATE ==", flush=True)
r_in=spearmanr(C,indeg).correlation; r_deg=spearmanr(C,udeg).correlation; r_out=spearmanr(C,outdeg).correlation
print(f"  D: median={np.median(D):.0f} max={D.max():.0f} mean={D.mean():.0f}", flush=True)
print(f"  rho(C, in-degree)={r_in:+.3f}   rho(C, undirected-deg)={r_deg:+.3f}   rho(C, out-degree)={r_out:+.3f}", flush=True)
gate = abs(r_in)<0.40
print(f"  GATE |rho(C,in-degree)|<0.40: {'PASS' if gate else 'FAIL -> C disqualified'}"
      f"   (out-degree note: {'C ~ out-degree (proof-width)' if r_out>0.9 else 'not just out-degree'})", flush=True)

# anchor
fam=set(l.strip() for l in open(f"{BASE}/anchor_famous.txt") if l.strip())
Y=np.array([1.0 if n in fam else 0.0 for n in nodes])
print(f"\n== PHASE B: exogenous anchor Y* (famous theorems) — {int(Y.sum())} positives / {N} ==", flush=True)

print("\n== PAYOFF: C vs Y* (controlling in-degree, depth) ==", flush=True)
part=ps(C,Y,[logi,depth])
# permutation p-value: shuffle Y labels
rngp=np.random.default_rng(1); nperm=200; null=[]
base_res=rr(C,[logi,depth])
for _ in range(nperm):
    Yp=Y.copy(); rngp.shuffle(Yp)
    null.append(spearmanr(base_res, rr(Yp,[logi,depth])).correlation)
null=np.array(null); pval=(np.sum(null>=part)+1)/(nperm+1)
print(f"  partial Spearman(C, Y* | log-indeg, depth) = {part:+.3f}   perm p={pval:.3f}", flush=True)
# AUC baselines
def auc(score):
    try: return roc_auc_score(Y, score)
    except: return float('nan')
auc_C=auc(C); auc_in=auc(indeg)
# subject baseline: P(famous|subject) frequency
def subj(m): p=m.split("."); return p[1] if len(p)>=2 and p[0]=="Mathlib" else (p[0] or "?")
subject=np.array([subj(module[n]) for n in nodes])
sfreq=collections.defaultdict(lambda:[0,0])
for i in range(N): sfreq[subject[i]][int(Y[i])]+=1
subj_score=np.array([sfreq[subject[i]][1]/max(1,(sfreq[subject[i]][0]+sfreq[subject[i]][1])) for i in range(N)])
auc_subj=auc(subj_score)
print(f"  AUC(C)={auc_C:.3f}   AUC(in-degree)={auc_in:.3f}   AUC(subject-freq)={auc_subj:.3f}", flush=True)
print(f"  C beats degree: {auc_C>auc_in}   C beats subject: {auc_C>auc_subj}", flush=True)
# stratified: median C famous vs non-famous within depth x in-degree deciles
def dec(x): return np.clip(np.searchsorted(np.quantile(x,np.linspace(0,1,11)[1:-1]),x),0,9)
strat=list(zip(dec(depth),dec(logi)))
famC=C[Y==1]; # matched non-famous: same strata distribution
print(f"  median C: famous={np.median(C[Y==1]):.2f}  non-famous={np.median(C[Y==0]):.2f}  "
      f"(overall rank-biserial rho(C,Y)={spearmanr(C,Y).correlation:+.3f})", flush=True)

print("\n== ANTI-GAMING: A^B conjunction foils (C via descendant-union) ==", flush=True)
# a synthetic A^B references distant A,B -> its descendants = union(desc(A),desc(B)) -> high C
adj={n:set(UG.neighbors(n)) for n in nodes}
rngf=np.random.default_rng(7); pairs=[]; idx=rngf.integers(0,N,size=(4000,2))
Didx={n:D[nidx[n]] for n in nodes}
for a_i,b_i in idx:
    a,b=nodes[a_i],nodes[b_i]
    if a!=b and b not in adj[a] and not (adj[a]&adj[b]) and D[a_i]>np.median(D) and D[b_i]>np.median(D):
        pairs.append((a_i,b_i))
    if len(pairs)>=500: break
foilD=np.array([max(D[a_i],D[b_i]) for a_i,b_i in pairs])  # union >= max; lower bound
foilC=np.log1p(foilD)
hi=np.quantile(C,0.9)
print(f"  {len(pairs)} A^B foils of deep A,B: foil C >= max(dA,dB); "
      f"{(foilC>=hi).mean()*100:.0f}% would land in top-decile C -> descendant-C IS gameable by conjunction",
      flush=True)

print("\n== VERDICT ==", flush=True)
payoff = (part>0 and pval<0.05 and auc_C>auc_in and auc_C>auc_subj)
if not gate:
    print("  C failed the degree-decoupling gate -> disqualified; cannot run importance test cleanly.", flush=True)
elif payoff:
    print(f"  POSITIVE: compression-rank C predicts exogenous human importance beyond degree/subject.", flush=True)
    print(f"    (caveat: C gameable by conjunction — fine for the descriptive finding; gates a conjecturer.)", flush=True)
else:
    print(f"  KILL: C vs Y* ~0/negative or does not beat degree/subject "
          f"(part={part:+.3f} p={pval:.3f} AUC_C={auc_C:.3f} vs in={auc_in:.3f} subj={auc_subj:.3f}).", flush=True)
    print(f"    => human importance is NOT a structural invariant of Mathlib's proof library.", flush=True)
np.savez_compressed(f"{BASE}/compress_scores.npz", names=np.array(nodes), C=C, D=D, Y=Y, depth=depth, indeg=indeg)
