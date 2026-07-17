#!/usr/bin/env python3
"""Phase 0b: re-read the degree-independent significance arm with better proxies.
Y3 = @[simp] flag (decl_simp.tsv). Y4 = # distinct subjects among dependents (cross-subject
downstream breadth), from the faithful graph. Metric = ratio T/E (degree-normalized) from
phase0_lnorm.npz. Pre-registered pass: degree-controlled partial rho(ratio,Y|depth,logdeg)
>= +0.10 correct sign for at least one of {Y3, Y4}."""
import json, os, numpy as np, collections
from scipy.stats import spearmanr, rankdata

BASE=os.environ.get("STYLE_BASE",".")
d=np.load(f"{BASE}/phase0_lnorm.npz", allow_pickle=True)
names=list(d["names"]); T=d["triangles"]; E=d["E"]; xu=d["udeg"]; xi=d["indeg"]; xd=d["depth"]
ratio=T/(E+1.0); logu=np.log1p(xu); logi=np.log1p(xi)
idx={n:i for i,n in enumerate(names)}
N=len(names)

def subj(m):
    p=m.split("."); return p[1] if len(p)>=2 and p[0]=="Mathlib" else (p[0] or "?")

# one pass over faithful graph: module per node + cross-subject downstream breadth
print("computing cross-subject downstream breadth Y4 ...", flush=True)
module={}
breadth=collections.defaultdict(set)
for line in open(f"{BASE}/faithful/decl_deps.jsonl"):
    r=json.loads(line); u=r["name"]; module[u]=r.get("module","")
for line in open(f"{BASE}/faithful/decl_deps.jsonl"):
    r=json.loads(line); u=r["name"]; su=subj(r.get("module",""))
    deps=r.get("deps") or list(dict.fromkeys(r.get("type_deps",[])+r.get("value_deps",[])))
    for dep in deps:
        if dep in idx and dep!=u:
            breadth[dep].add(su)     # a dependent in subject su uses dep
Y4=np.array([len(breadth.get(n,())) for n in names],float)

# Y3 simp flag
simp={}
for row in open(f"{BASE}/decl_simp.tsv"):
    q,f=row.rstrip("\n").split("\t"); simp[q]=int(f)
Y3=np.array([simp.get(n,0) for n in names],float)

# Y1 label for reference
kind={}
for line in open(f"{BASE}/faithful/decl_deps.jsonl"):
    r=json.loads(line); kind[r["name"]]=r.get("kind","")
Y1=np.array([1.0 if kind.get(n)=="theorem" else 0.0 for n in names])
Y2=np.log1p(xi)

def rr(a,ctrls):
    cols=[rankdata(c) for c in ctrls]; X=np.column_stack(cols+[np.ones(len(a))]); ra=rankdata(a)
    b,*_=np.linalg.lstsq(X,ra,rcond=None); return ra-X@b
def ps(a,b,c): return spearmanr(rr(a,c),rr(b,c)).correlation

print("\n== PHASE 0b: degree-INDEPENDENT significance arm (metric = ratio T/E) ==", flush=True)
print(f"  coverage: simp-flagged={int(Y3.sum())} ({100*Y3.mean():.1f}%)  "
      f"Y4 breadth: median={np.median(Y4):.0f} max={Y4.max():.0f}", flush=True)
print(f"  degree-linkage of each Y (rho with in-degree): "
      f"Y3={spearmanr(Y3,xi).correlation:+.3f}  Y4={spearmanr(Y4,xi).correlation:+.3f}  "
      f"Y1={spearmanr(Y1,xi).correlation:+.3f}", flush=True)
print("  partial rho(ratio, Y | controls):", flush=True)
for yn,Y in [("Y3 @[simp] (deg-indep)",Y3),("Y4 cross-subj breadth",Y4),
             ("Y1 thm/lemma label",Y1),("Y2 citation (ref)",Y2)]:
    print(f"    {yn:26s} | depth={ps(ratio,Y,[xd]):+.3f}   | depth+log-deg={ps(ratio,Y,[xd,logu]):+.3f}"
          f"   | depth+log-indeg={ps(ratio,Y,[xd,logi]):+.3f}", flush=True)

# pre-registered read — a proxy only counts as degree-INDEPENDENT if |rho(Y,in-deg)|<0.40,
# and it must be controlled for ITS OWN degree confound (in-degree), not undirected degree.
print("\n== PHASE 0b READ (honest: gate on actual degree-independence) ==", flush=True)
verdict=[]
for yn,Y in [("Y3 @[simp]",Y3),("Y4 breadth",Y4),("Y1 label",Y1)]:
    dl=abs(spearmanr(Y,xi).correlation)
    indep = dl<0.40
    p = ps(ratio,Y,[xd,logi])          # control the actual (in-degree) confound
    print(f"    {yn:12s} deg-linkage(|rho in-deg|)={dl:.3f} {'[degree-INDEP]' if indep else '[degree-LINKED -> not a valid proxy]'}"
          f"  partial rho(ratio,Y|depth,in-deg)={p:+.3f}", flush=True)
    if indep: verdict.append((yn,p))
arm_pass = any(p>=0.10 for _,p in verdict)
print(f"  genuinely degree-independent proxies: {[f'{n}={p:+.3f}' for n,p in verdict]}", flush=True)
print(f"  degree-independent arm: {'PASS' if arm_pass else 'FAIL'} "
      f"-> {'proceed to Phase 1' if arm_pass else 'QUALIFIED NEGATIVE: judge predicts reuse-volume/citation, not degree-free significance'}", flush=True)
