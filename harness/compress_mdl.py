#!/usr/bin/env python3
"""
De-gamed MDL compression C_mdl vs the exogenous famous-theorem anchor.
Pre-reg: PREREG-compression-mdl.md. C_mdl(v)=log(1+max(0, sum_{v->c} D(c) - D(v))) = shared
descendant content v's dependencies bind (charged once); disjoint A^B -> 0 by construction.
Gates: |rho(C_mdl,in-deg)|<0.40 AND foil top-decile fraction <10%. Decisive: C_mdl-beyond-depth
AUC (pre-committed line >=0.58, perm p<0.01). Three outcomes SURVIVES/REDUCES/BROKE.
"""
import json, os, collections, numpy as np, networkx as nx
from scipy.stats import spearmanr, rankdata, mannwhitneyu
from sklearn.metrics import roc_auc_score

BASE=os.environ.get("STYLE_BASE",".")
PATH=f"{BASE}/faithful/decl_deps.jsonl"
K=160

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
nodes=list(G2.nodes()); nidx={n:i for i,n in enumerate(nodes)}; N=len(nodes)
print(f"nodes={N} edges={G2.number_of_edges()}", flush=True)
indeg=np.array([G2.in_degree(n) for n in nodes],float)
UG=G2.to_undirected()

print("depth + condensation ...", flush=True)
Cg=nx.condensation(G2); cdep={}
for c in reversed(list(nx.topological_sort(Cg))):
    ds=[cdep[s]+1 for s in Cg.successors(c) if s in cdep]; cdep[c]=max(ds) if ds else 0
mp=Cg.graph['mapping']; depth=np.array([cdep[mp[n]] for n in nodes],float)

print(f"MinHash descendants (k={K}) + per-SCC sketches ...", flush=True)
rng=np.random.default_rng(0); hvals=rng.random(N)
members={c:[] for c in Cg.nodes()}
for n in nodes: members[mp[n]].append(nidx[n])
sketch={}; Dself={}
for c in reversed(list(nx.topological_sort(Cg))):
    pool=[np.array([hvals[i] for i in members[c]])]
    for s in Cg.successors(c): pool.append(sketch[s])
    arr=np.unique(np.concatenate(pool)); sketch[c]=arr[:K].copy()
    Dself[c]= float(len(arr)) if len(arr)<K else (K-1)/arr[K-1]
Dnode=np.array([Dself[mp[n]] for n in nodes],float)     # incl-self reach cardinality

def union_card(sk_list):
    arr=np.unique(np.concatenate(sk_list))
    return float(len(arr)) if len(arr)<K else (K-1)/arr[K-1]

print("C_mdl = shared content bound by v's dependencies ...", flush=True)
# sum over direct out-neighbors of Dself(child); minus D(v) (union proxy)
sumchild=np.zeros(N)
for u,v in G2.edges():
    sumchild[nidx[u]]+=Dself[mp[v]]
Cmdl_raw=np.maximum(0.0, sumchild - Dnode)
Cmdl=np.log1p(Cmdl_raw)
# reference raw C = log(1+descendants)
C=np.log1p(np.maximum(0.0,Dnode-1.0))

def rr(a,ctrls):
    cols=[rankdata(c) for c in ctrls]; X=np.column_stack(cols+[np.ones(len(a))]); ra=rankdata(a)
    b,*_=np.linalg.lstsq(X,ra,rcond=None); return ra-X@b
logi=np.log1p(indeg)

print("\n== GATE 1: degree decoupling ==", flush=True)
r_in=spearmanr(Cmdl,indeg).correlation
gate1= abs(r_in)<0.40
print(f"  rho(C_mdl, in-degree)={r_in:+.3f}  rho(C_mdl,depth)={spearmanr(Cmdl,depth).correlation:+.3f}"
      f"  -> {'PASS' if gate1 else 'FAIL (disqualified)'}", flush=True)

print("\n== GATE 2: anti-gaming foils (must be <10% in top decile) ==", flush=True)
adj={n:set(UG.neighbors(n)) for n in nodes}
rngf=np.random.default_rng(7); idx=rngf.integers(0,N,size=(20000,2)); pairs=[]
medD=np.median(Dnode)
for a_i,b_i in idx:
    a,b=nodes[a_i],nodes[b_i]
    if a!=b and b not in adj[a] and not (adj[a]&adj[b]) and Dnode[a_i]>medD and Dnode[b_i]>medD:
        pairs.append((a_i,b_i))
    if len(pairs)>=500: break
foil_raw=[]
for a_i,b_i in pairs:
    uc=union_card([sketch[mp[nodes[a_i]]], sketch[mp[nodes[b_i]]]])
    foil_raw.append(max(0.0, Dself[mp[nodes[a_i]]]+Dself[mp[nodes[b_i]]] - uc))
foilCmdl=np.log1p(np.array(foil_raw))
topdec=np.quantile(Cmdl,0.9)
frac=(foilCmdl>=topdec).mean()
gate2= frac<0.10
print(f"  {len(pairs)} A^B foils: {100*frac:.1f}% in C_mdl top decile (raw C was 32%) -> "
      f"{'PASS' if gate2 else 'FAIL -> run VOID'}", flush=True)

# anchor
fam=set(l.strip() for l in open(f"{BASE}/anchor_famous.txt") if l.strip())
Y=np.array([1.0 if n in fam else 0.0 for n in nodes])

print(f"\n== ANCHOR TEST (185 positives; report even if void, marked) ==", flush=True)
def perm_auc(score,nperm=1000):
    obs=roc_auc_score(Y,score); nP=int(Y.sum()); rp=np.random.default_rng(5); null=[]
    for _ in range(nperm):
        Yp=np.zeros(N); Yp[rp.choice(N,nP,replace=False)]=1; null.append(roc_auc_score(Yp,score))
    null=np.array(null); return obs,(np.sum(null>=obs)+1)/(nperm+1)
Cmdl_res=rr(Cmdl,[rankdata(depth)])
for nm,s in [("C_mdl",Cmdl),("raw C",C),("depth",depth),("reuse(in-deg)",indeg),
             ("C_mdl beyond depth",Cmdl_res)]:
    o,p=perm_auc(s); print(f"  AUC({nm:20s})={o:.3f}  perm p={p:.4f}", flush=True)
part=spearmanr(rr(Cmdl,[logi,depth]), rr(Y,[logi,depth])).correlation
print(f"  [both stats] partial Spearman(C_mdl,Y|indeg,depth)={part:+.3f}   (AUC is the valid one here)", flush=True)
bd_auc,bd_p=perm_auc(Cmdl_res)

print("\n== VERDICT (against locked outcomes) ==", flush=True)
if not (gate1 and gate2):
    print("  RUN VOID: a gate failed; AUC above does not count.", flush=True)
else:
    aucCmdl=roc_auc_score(Y,Cmdl)
    if bd_auc>=0.58 and bd_p<0.01:
        print(f"  SURVIVES: foil gate passed AND C_mdl-beyond-depth AUC={bd_auc:.3f} (p={bd_p:.4f}) >=0.58."
              f" Compression-rank is real AND gaming-resistant -> build judge on C_mdl.", flush=True)
    elif aucCmdl < 0.75:
        print(f"  BROKE: C_mdl AUC={aucCmdl:.3f} materially < raw C (0.827); MDL discarded real signal -> iterate metric.", flush=True)
    else:
        print(f"  REDUCES: foil gate passed but C_mdl-beyond-depth AUC={bd_auc:.3f} (p={bd_p:.4f}) < 0.58."
              f" The +0.616 surplus was gameable inflation -> IMPORTANCE ~= FOUNDATIONAL DEPTH; build judge on depth.", flush=True)

print("\n== STANDING RESULT 2: partial-Spearman is inert at 0.056% prevalence (PROOF) ==", flush=True)
perfect = Y*1e6 + np.random.default_rng(9).random(N)   # perfect ranker: all positives on top
sp=spearmanr(perfect,Y).correlation
psp=spearmanr(rr(perfect,[logi,depth]), rr(Y,[logi,depth])).correlation
print(f"  PERFECT ranker (AUC={roc_auc_score(Y,perfect):.3f}): plain Spearman(Y)={sp:+.3f}  "
      f"partial Spearman(Y|indeg,depth)={psp:+.3f}", flush=True)
print(f"  => even a perfect ranker yields Spearman ~= {sp:.3f} at this prevalence; the -0.08 for C is within"
      f" this inert band. Rank-correlation is the WRONG statistic under extreme imbalance; AUC+perm is correct.", flush=True)
print("\n== STANDING RESULT 1: reuse-kill (from prior run) ==", flush=True)
print(f"  reuse(in-degree) AUC(famous)={roc_auc_score(Y,indeg):.3f} ~ chance -> loops=reuse != importance (exogenous).", flush=True)
np.savez_compressed(f"{BASE}/compress_mdl_scores.npz", names=np.array(nodes), Cmdl=Cmdl, C=C, Y=Y, depth=depth, indeg=indeg)
