#!/usr/bin/env python3
"""
Cell 5 — intrinsic atomicity self-selection with the REAL Schur gate on the Mathlib graph.
Pre-reg: PREREG-cell5.md. Real gate: schur A b d = d - b.(A^-1 b). Incidence kernel
K(u,v)=|({u}u deps(u)) cap ({v}u deps(v))|. Observable: Hodge curl_fraction of the Schur
preference field s(u->v)=schur_add(u|v)-schur_add(v|u), vs the 0.076 scalar-proxy baseline.
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
print(f"nodes={N} edges={G2.number_of_edges()}", flush=True)

# phi(v) = {v} u direct-deps(v)  (closed out-neighborhood); K(v,v)=|phi(v)|=outdeg+1
out=[None]*N
for i,n in enumerate(nodes):
    s=set(nidx[d] for d in G2.successors(n)); s.add(i); out[i]=s
Kdiag=np.array([len(out[i]) for i in range(N)],float)

edges=[(nidx[u],nidx[v]) for u,v in G2.edges()]
E=len(edges)
print(f"computing Schur preference field s over {E} edges (real gate, 1x1 context) ...", flush=True)
s=np.empty(E)
for k,(u,v) in enumerate(edges):
    a,b=out[u],out[v]
    Kuv=len(a & b) if len(a)<len(b) else len(b & a)
    Kuu=Kdiag[u]; Kvv=Kdiag[v]
    schur_u_given_v = Kuu - Kuv*Kuv/Kvv      # schur_add(u|v) = d - b^2/A , exact Schur complement
    schur_v_given_u = Kvv - Kuv*Kuv/Kuu
    s[k]=schur_u_given_v - schur_v_given_u
print(f"  s: mean={s.mean():.3f} std={s.std():.3f}", flush=True)

def incidence(edge_list,n):
    m=len(edge_list); rows=np.repeat(np.arange(m),2)
    cols=np.empty(2*m,int); dat=np.empty(2*m,float)
    for k,(u,v) in enumerate(edge_list):
        cols[2*k]=u; dat[2*k]=1.0; cols[2*k+1]=v; dat[2*k+1]=-1.0
    return sp.csr_matrix((dat,(rows,cols)),shape=(m,n))
def curl_fraction(edge_list, flow, n, iters=400):
    B=incidence(edge_list,n)
    sol=lsqr(B, flow, iter_lim=iters, atol=1e-8, btol=1e-8)
    res=flow - B.dot(sol[0])
    return float((res@res)/(flow@flow)), sol[1]

print("\n== TAUTOLOGY CHECK ==", flush=True)
rng=np.random.default_rng(0); phi=rng.random(N); B=incidence(edges,N); gradf=B.dot(phi)
cf0,_=curl_fraction(edges,gradf,N,iters=200)
print(f"  curl_fraction of pure node-potential flow = {cf0:.2e} (~0)", flush=True)

print("\n== MAIN: curl of the Schur preference field s ==", flush=True)
cf,istop=curl_fraction(edges,s,N)
print(f"  curl_fraction(s) = {cf:.4f}   [lsqr istop={istop}]   (scalar-proxy baseline = 0.076)", flush=True)
# decompose: curl of the gradient-only part (Kuu-Kvv) should be ~0; the operator cross-term carries any curl
s_pot=np.array([Kdiag[u]-Kdiag[v] for (u,v) in edges],float)
cf_pot,_=curl_fraction(edges,s_pot,N,iters=200)
print(f"  (control: curl of the potential-only part Kuu-Kvv = {cf_pot:.2e} ~0 -> any curl is operator cross-term)", flush=True)

print("\n== CONTROL: module conditioning ==", flush=True)
intra=[(u,v) for (u,v) in edges if module[nodes[u]]==module[nodes[v]]]
s_intra=np.array([s[k] for k,(u,v) in enumerate(edges) if module[nodes[u]]==module[nodes[v]]])
cf_intra,_=curl_fraction(intra,s_intra,N)
print(f"  intra-module edges={len(intra)}  curl_fraction(s|intra)={cf_intra:.4f}  ratio={cf_intra/max(1e-12,cf):.2f}", flush=True)

print("\n== REPRODUCIBILITY ==", flush=True)
perm=np.random.default_rng(1).permutation(E)
cf2,_=curl_fraction([edges[i] for i in perm], s[perm], N)
print(f"  curl_fraction(reordered)={cf2:.4f}  |d|={abs(cf2-cf):.2e}", flush=True)

print("\n== CONFIRMATION: REAL singleton->expand(argmax schur) on bounded regions ==", flush=True)
# pick a few modules of moderate size; run the real Schur-gated argmax self-selection
bymod=collections.defaultdict(list)
for i in range(N): bymod[module[nodes[i]]].append(i)
regions=[m for m,v in bymod.items() if 80<=len(v)<=180][:3]
def schur_add(Minv, bvec, d):
    return d - bvec @ (Minv @ bvec)
for rm in regions:
    R=bymod[rm]; idx={g:l for l,g in enumerate(R)}; nR=len(R)
    Ksub=np.zeros((nR,nR))
    for a in range(nR):
        for b in range(a,nR):
            ov=len(out[R[a]] & out[R[b]]); Ksub[a,b]=Ksub[b,a]=ov
    # singleton = max-diagonal site; then argmax-schur admissible expansion
    admitted=[int(np.argmax(np.diag(Ksub)))]
    Minv=np.array([[1.0/Ksub[admitted[0],admitted[0]]]])
    order=[admitted[0]]; halted=0
    remaining=set(range(nR))-set(admitted)
    while remaining:
        best=None; bestschur=0.0
        for c in remaining:
            bvec=np.array([Ksub[c,a] for a in admitted]); d=Ksub[c,c]
            sc=schur_add(Minv,bvec,d)
            if sc>bestschur: bestschur=sc; best=c
        if best is None: break   # no admissible site (all schur<=0) -> halt
        # update inverse by bordering (Schur/block-inverse)
        bvec=np.array([Ksub[best,a] for a in admitted]); d=Ksub[best,best]
        w=Minv@bvec; sc=d-bvec@w
        newMinv=np.zeros((len(admitted)+1,len(admitted)+1))
        newMinv[:-1,:-1]=Minv+np.outer(w,w)/sc; newMinv[:-1,-1]=-w/sc; newMinv[-1,:-1]=-w/sc; newMinv[-1,-1]=1/sc
        Minv=newMinv; admitted.append(best); order.append(best); remaining.discard(best)
    print(f"  region '{rm.split('.')[-1]}' (N={nR}): real gate admitted {len(order)}/{nR} sites via argmax-schur "
          f"(halt when all schur<=0). Real expand ran on the bridge.", flush=True)

print("\n== VERDICT (locked) ==", flush=True)
repro=abs(cf2-cf)<0.01
if cf>=0.20 and cf_intra>=0.5*cf and repro:
    print(f"  ALIVE: Schur preference field carries circulation {cf:.3f} >= 0.20, survives module ({cf_intra:.3f}), reproducible."
          f" Operator-valued self-selection finds structure the scalar order discarded. Cell 5 real (modulo kernel caveat).", flush=True)
elif cf<=0.10:
    print(f"  DEAD: curl_fraction(s)={cf:.3f} <= 0.10 (proxy-level). The atomicity gate self-selects a near-gradient order too."
          f" Cell 5 closed on the real gate (incidence-kernel bridge). The epitaph stands.", flush=True)
else:
    print(f"  AMBIGUOUS: curl_fraction(s)={cf:.3f} in (0.10,0.20). Report; do not advance.", flush=True)
