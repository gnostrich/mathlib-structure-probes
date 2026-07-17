#!/usr/bin/env python3
"""
Tension gate. Pre-reg: PREREG-tension-gate.md.
T_r(v) = b1/E of the bounded out-expansion of v's STATEMENT references (type_deps; never
value_deps). Labels: Y_a=log1p(#value_deps), Y_b=@[simp]. Decisive: degree-residual partial at
each radius (joint table). Locked: ALIVE / DEGREE / PROVER / FLAT / AMBIGUOUS.
"""
import json, os, collections, numpy as np
from scipy.stats import spearmanr, rankdata
from sklearn.metrics import roc_auc_score

BASE=os.environ.get("STYLE_BASE",".")
PATH=f"{BASE}/faithful/decl_deps.jsonl"
SEED=20260717; NSAMP=40000; NSAMP2=10000; CAP2=5000

print("loading faithful graph (type/value deps split) ...", flush=True)
names=[]; nidx={}; kind={}; tdeps={}; nval={}
raw_edges=[]
for line in open(PATH):
    r=json.loads(line); n=r["name"]
    i=nidx.setdefault(n,len(names))
    if i==len(names): names.append(n)
    kind[n]=r.get("kind","")
    td=[d for d in r.get("type_deps",[]) if d!=n]
    vd=[d for d in r.get("value_deps",[]) if d!=n]
    tdeps[n]=td; nval[n]=len(vd)
    for d in dict.fromkeys(td+vd):
        raw_edges.append((n,d))
N=len(names)
inset=set(names)
out=[set() for _ in range(N)]
indeg=np.zeros(N);
for u,v in raw_edges:
    if v in nidx and u!=v:
        ui,vi=nidx[u],nidx[v]
        if vi not in out[ui]:
            out[ui].add(vi); indeg[vi]+=1
outdeg=np.array([len(s) for s in out],float)
print(f"nodes={N} edges={int(outdeg.sum())}", flush=True)

# simp labels
simp={}
for row in open(f"{BASE}/decl_simp.tsv"):
    q,f=row.rstrip("\n").split("\t"); simp[q]=int(f)

# sample: theorems with simp coverage
pop=[n for n in names if kind[n]=="theorem" and n in simp]
rng=np.random.default_rng(SEED); rng.shuffle(pop)
samp=pop[:NSAMP]; samp2=set(samp[:NSAMP2])
print(f"theorem population with labels={len(pop)}; sample={len(samp)} (r=0,1), {len(samp2)} (r=2, node-cap {CAP2})", flush=True)

class UF:
    __slots__=("p",)
    def __init__(s,ns): s.p={x:x for x in ns}
    def find(s,x):
        p=s.p
        while p[x]!=x: p[x]=p[p[x]]; x=p[x]
        return x
    def union(s,a,b):
        ra,rb=s.find(a),s.find(b)
        if ra!=rb: s.p[rb]=ra; return True
        return False

def tension(seedset, radius, cap=None):
    Nset=set(seedset)
    frontier=list(Nset)
    for _ in range(radius):
        nxt=[]
        for u in frontier:
            for w in out[u]:
                if w not in Nset:
                    Nset.add(w); nxt.append(w)
                    if cap and len(Nset)>=cap: break
            if cap and len(Nset)>=cap: break
        frontier=nxt
        if cap and len(Nset)>=cap: break
    nn=len(Nset)
    if nn==0: return 0.0,0,0
    uf=UF(Nset); E=0
    for u in Nset:
        ou=out[u]
        tgt=ou&Nset if len(ou)<nn else Nset.intersection(ou)
        for w in tgt:
            E+=1; uf.union(u,w)
    C=len({uf.find(x) for x in Nset})
    b1=E-nn+C
    return (b1/E if E>0 else 0.0), nn, E

def rankres(a,ctrls):
    cols=[rankdata(c) for c in ctrls]; X=np.column_stack(cols+[np.ones(len(a))]); ra=rankdata(a)
    b,*_=np.linalg.lstsq(X,ra,rcond=None); return ra-X@b
def pspear(a,b,ctrls): return spearmanr(rankres(a,ctrls),rankres(b,ctrls)).correlation

results={}
for radius,sub,cap in [(0,samp,None),(1,samp,None),(2,[n for n in samp if n in samp2],CAP2)]:
    print(f"\ncomputing T at r={radius} over {len(sub)} theorems ...", flush=True)
    T=np.empty(len(sub)); Nr=np.empty(len(sub)); Er=np.empty(len(sub))
    capped=0
    for k,n in enumerate(sub):
        seeds={nidx[d] for d in tdeps[n] if d in nidx}
        t,nn,e=tension(seeds,radius,cap)
        T[k]=t; Nr[k]=nn; Er[k]=e
        if cap and nn>=cap: capped+=1
        if k%10000==0: print(f"  {k}/{len(sub)}", flush=True)
    Ya=np.array([np.log1p(nval[n]) for n in sub])
    Yb=np.array([float(simp[n]) for n in sub])
    iv=np.array([indeg[nidx[n]] for n in sub]); ov=np.array([outdeg[nidx[n]] for n in sub])
    ctrls=[np.log1p(iv),np.log1p(ov),np.log1p(Nr),np.log1p(Er)]
    auc=roc_auc_score(Yb,T); auc=max(auc,1-auc)
    rho_a=spearmanr(T,Ya).correlation
    rho_b=spearmanr(T,Yb).correlation
    p_a=pspear(T,Ya,ctrls); p_b=pspear(T,Yb,ctrls)
    zeroE=float((Er==0).mean())
    results[radius]=dict(auc=auc,rho_a=rho_a,rho_b=rho_b,p_a=p_a,p_b=p_b)
    print(f"  r={radius}: median N={np.median(Nr):.0f} E={np.median(Er):.0f}  E==0 frac={zeroE:.3f}"
          f"{f'  capped={capped}' if cap else ''}", flush=True)
    print(f"  raw:   AUC(T,simp)={auc:.3f}   rho(T,Ya)={rho_a:+.3f}   rho(T,simp)={rho_b:+.3f}", flush=True)
    print(f"  DEGREE-RESIDUAL (decisive): partial(T,Ya|deg)={p_a:+.3f}   partial(T,simp|deg)={p_b:+.3f}", flush=True)

print("\n== JOINT TABLE (radius x raw-signal x degree-residual) ==", flush=True)
print(f"  {'r':>2} {'AUC(simp)':>10} {'rho(Ya)':>9} {'resid(Ya)':>10} {'resid(simp)':>12}", flush=True)
for r in sorted(results):
    d=results[r]
    print(f"  {r:>2} {d['auc']:>10.3f} {d['rho_a']:>+9.3f} {d['p_a']:>+10.3f} {d['p_b']:>+12.3f}", flush=True)

print("\n== VERDICT (locked) ==", flush=True)
def signal(d): return d['auc']>=0.65 and abs(d['rho_a'])>=0.15
def resid_ok(d): return abs(d['p_a'])>=0.10 and abs(d['p_b'])>=0.10 and np.sign(d['p_a'])==-np.sign(d['p_b'])
small=[results[r] for r in (0,1)]
alive=any(signal(d) and resid_ok(d) for d in small)
raw_any=any(signal(results[r]) for r in results)
flat=all(results[r]['auc']<0.55 and abs(results[r]['rho_a'])<0.05 for r in results)
prover=(not alive) and 2 in results and signal(results[2]) and resid_ok(results[2])
if alive:
    print("  ALIVE: cheap local tension predicts forced-vs-open beyond degree at small radius, both labels,"
          " consistent signs -> build the EBM sampler next session.", flush=True)
elif flat:
    print("  FLAT: no signal on either label at any radius -> DEAD (provisional on label faithfulness).", flush=True)
elif prover:
    print("  PROVER: predicts only at large radius -> prover in a hat -> DEAD.", flush=True)
elif raw_any:
    print("  DEGREE: raw signal exists but the degree-residual dies (<0.10 or inconsistent signs) at r<=1"
          " -> reuse in a hat -> DEAD. (The stated-prior outcome.)", flush=True)
else:
    print("  AMBIGUOUS: mixed pattern; report, do not build.", flush=True)
