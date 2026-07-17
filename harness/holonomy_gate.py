#!/usr/bin/env python3
"""
Order-holonomy gate (Hodge curl of the dependency comparison flow). Pre-reg:
PREREG-holonomy-gate.md. curl_fraction = ||f - grad phi*||^2 / ||f||^2 for unit flow f(u->v)=1.
Controls: topology (built into the gradient) + module conditioning (intra-module curl).
Intrinsic; no proxy; a null is a real DEAD.
"""
import json, os, collections, numpy as np, networkx as nx
import scipy.sparse as sp
from scipy.sparse.linalg import lsqr

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
edges=[(nidx[u],nidx[v]) for u,v in G2.edges()]
E=len(edges)
print(f"nodes={N} edges={E}", flush=True)

def incidence(edge_list, n):
    m=len(edge_list); rows=np.repeat(np.arange(m),2)
    cols=np.empty(2*m,int); dat=np.empty(2*m,float)
    for k,(u,v) in enumerate(edge_list):
        cols[2*k]=u; dat[2*k]=1.0; cols[2*k+1]=v; dat[2*k+1]=-1.0
    return sp.csr_matrix((dat,(rows,cols)),shape=(m,n))

def curl_fraction(edge_list, n, iters=300, seed=0):
    m=len(edge_list)
    if m==0: return 0.0,0,0.0
    B=incidence(edge_list,n); f=np.ones(m)
    sol=lsqr(B, f, iter_lim=iters, atol=1e-8, btol=1e-8)
    phi=sol[0]; res=f - B.dot(phi)
    cf=float((res@res)/(f@f))
    return cf, sol[1], sol[3]  # curl_fraction, istop, resid-norm

print("\n== TAUTOLOGY CHECK: holonomy of a node-scalar order residual is ~0 ==", flush=True)
# a pure gradient flow g_e = phi[u]-phi[v] for random node potential -> curl must be ~0
rng=np.random.default_rng(0); phi_rand=rng.random(N)
B=incidence(edges,N); grad_flow=B.dot(phi_rand)
sol=lsqr(B, grad_flow, iter_lim=300, atol=1e-10, btol=1e-10)
curl_of_gradient=float(((grad_flow-B.dot(sol[0]))**2).sum()/(grad_flow@grad_flow))
print(f"  curl_fraction of a pure node-potential flow = {curl_of_gradient:.2e}  (≈0 confirms node-order holonomy is tautologically zero)", flush=True)

print("\n== MAIN: Hodge curl of the unit dependency comparison flow ==", flush=True)
cf, istop, rn = curl_fraction(edges, N, iters=400)
print(f"  curl_fraction (global) = {cf:.4f}   [lsqr istop={istop}, resid={rn:.2e}]", flush=True)

print("\n== CONTROL: module conditioning (intra-module edges only) ==", flush=True)
intra=[(u,v) for (u,v) in edges if module[nodes[u]]==module[nodes[v]]]
print(f"  intra-module edges: {len(intra)}/{E} ({100*len(intra)/E:.0f}%)", flush=True)
cf_intra,_,_ = curl_fraction(intra, N, iters=400)
print(f"  curl_fraction (intra-module) = {cf_intra:.4f}   ratio intra/global = {cf_intra/max(1e-12,cf):.2f}", flush=True)

print("\n== REPRODUCIBILITY: second solve, shuffled edge order ==", flush=True)
perm=np.random.default_rng(1).permutation(E); edges2=[edges[i] for i in perm]
cf2,_,_ = curl_fraction(edges2, N, iters=400)
print(f"  curl_fraction (reordered) = {cf2:.4f}   |Δ| = {abs(cf2-cf):.4e}", flush=True)

print("\n== VERDICT (locked; intrinsic -> a null is a REAL kill) ==", flush=True)
repro = abs(cf2-cf) < 0.01
t_mag = cf>=0.15
t_mod = cf_intra >= 0.5*cf
if t_mag and t_mod and repro:
    print(f"  ALIVE: antisymmetric order-circulation survives topology AND module conditioning "
          f"(curl={cf:.3f}, intra={cf_intra:.3f}={cf_intra/cf:.2f}x, reproducible). Holonomy design warranted.", flush=True)
else:
    why=[]
    if not t_mag: why.append(f"curl_fraction {cf:.3f}<0.15 (order ~ clean hierarchy)")
    if not t_mod: why.append(f"intra-module {cf_intra:.3f} < 0.5x global (circulation is cross-module coarse topology)")
    if not repro: why.append("not reproducible")
    print(f"  DEAD (REAL, non-provisional): {', '.join(why)}. No intra-region circulation to learn "
          f"-> back-then-forward collapses to forward. Thread ends here.", flush=True)
