#!/usr/bin/env python3
"""
Loosening-lattice analysis (PREREG-loosening-lattice.md).
Parses runner logs -> per-(theorem, move) outcome {SURVIVE, BREAK, NA, MOVE_ERROR} via
line-attributed errors + sorry-twin adjudication. Fidelity: canaries + double-run identity.
Budget flip-rate. Gates: STRUCTURED + INFRA-DISTINCT (decisive), stated prior DEGREE.
"""
import json, re, os, sys, collections, pathlib
import numpy as np

BASE=pathlib.Path("/tmp/claude-0/-home-user-Structure-Backprop/a747742e-9a2f-5c79-9f64-ed3bc601f93e/scratchpad")
man=json.load(open(BASE/"lattice_manifest.json"))
RES=BASE/"lattice_results"

ERR=re.compile(r'V(\d{3})\.lean:(\d+):\d+:\s*error')

def parse_run(runtag, budget):
    logs={}
    logdir=None
    for cand in RES.rglob("hb"+budget):
        if runtag in str(cand): logdir=cand; break
    if logdir is None: return None
    for lf in logdir.glob("V*.log"):
        errs=set()
        for line in open(lf, errors="ignore"):
            m=ERR.search(line)
            if m: errs.add(int(m.group(2)))
        logs[lf.stem]=errs
    return logs

def outcomes(logs):
    """per (file, move) -> outcome; plus canary verdicts"""
    out={}; canary_ok=True; canary_report=[]
    for d in man["decls"]:
        f=d["file"]
        if f not in logs: continue
        errs=logs[f]
        for e in d["entries"]:
            a,b=e["lines"]
            if e["role"].startswith("canary"):
                has=any(a<=x<=b for x in errs)
                want = (e["role"]!="canary_survive")
                ok = (has==want)
                if not ok:
                    canary_ok=False
                    canary_report.append((f,e["move"],"errored" if has else "no error"))
                continue
            if e["role"]=="na_recorded":
                out[(f,e["move"])]="NA"; continue
            ts=e.get("twin_start",a); vs=e.get("var_start",b)
            pre_err  = any(a<=x<ts for x in errs)
            twin_err = any(ts<=x<vs for x in errs)
            var_err  = any(vs<=x<=b for x in errs)
            if pre_err: out[(f,e["move"])]="MOVE_ERROR"
            elif twin_err: out[(f,e["move"])]="NA"
            elif var_err: out[(f,e["move"])]="BREAK"
            else: out[(f,e["move"])]="SURVIVE"
    return out, canary_ok, canary_report

runs=[t for t in ("run0","run1") if any(RES.rglob(f"*{t}*"))]
print("runs found:", runs, flush=True)
tables={}
for rt in runs:
    for hb in ("200k","50k"):
        lg=parse_run(rt,hb)
        if lg is None: print(f"  {rt}/hb{hb}: MISSING"); continue
        o,cok,crep=outcomes(lg)
        tables[(rt,hb)]=o
        nf=len({f for f,_ in o})
        cnt=collections.Counter(o.values())
        print(f"  {rt}/hb{hb}: files={nf} cells={len(o)} {dict(cnt)} canaries={'OK' if cok else 'FAIL '+str(crep[:5])}", flush=True)

# fidelity: double-run identity at 200k
void=False
if ("run0","200k") in tables and ("run1","200k") in tables:
    a,b=tables[("run0","200k")],tables[("run1","200k")]
    common=set(a)&set(b)
    mism=[k for k in common if a[k]!=b[k]]
    print(f"double-run identity: {len(common)} common cells, {len(mism)} mismatches", flush=True)
    if len(mism)>0.02*len(common): print("  -> FIDELITY VOID (>2% mismatch)"); void=True
main=tables.get(("run0","200k")) or tables.get(("run1","200k"))
tight=tables.get(("run0","50k")) or tables.get(("run1","50k"))
if main is None: sys.exit("no usable logs")

# budget flip-rate
if tight:
    common=set(main)&set(tight)
    flips=[k for k in common if main[k]!=tight[k]]
    fr=len(flips)/max(1,len(common))
    print(f"budget flip-rate (200k vs 50k): {len(flips)}/{len(common)} = {fr:.3f} "
          f"{'PROVER-LEAK FLAG' if fr>0.10 else '(ok, <=0.10)'}", flush=True)

# lattice
MATH=lambda m: m.startswith("M"); INFRA=lambda m: m in ("I1_shadow","I2_synthHB","I3_synthSize")
rows=[]
for d in man["decls"]:
    f=d["file"]
    mv={m:main.get((f,m)) for m in [e["move"] for e in d["entries"] if e["role"] in ("math","infra","pair","na_recorded")]}
    mM=[v for m,v in mv.items() if MATH(m) and v in ("SURVIVE","BREAK")]
    mI=[v for m,v in mv.items() if INFRA(m) and v in ("SURVIVE","BREAK")]
    if not mI: continue
    rows.append(dict(theorem=d["theorem"], file=f,
        math_res=(np.mean([v=="SURVIVE" for v in mM]) if mM else np.nan),
        infra_res=np.mean([v=="SURVIVE" for v in mI]),
        n_amb=len(d.get("amb",[])), n_hyp=d.get("n_hyp",0),
        pattern=tuple(sorted((m,v) for m,v in mv.items() if v in ("SURVIVE","BREAK"))),
        breaks=[m for m,v in mv.items() if v=="BREAK"]))
print(f"lattice rows: {len(rows)}", flush=True)

# degree controls from faithful graph
deg={}
gpath=BASE/"faithful/decl_deps.jsonl"
names_needed=set()
for d in man["decls"]:
    nm=d["theorem"].lstrip("_root_.")
    names_needed.add(nm)
    for ns in d.get("namespace",[]): names_needed.add(ns+"."+nm)
indeg=collections.Counter(); outdeg={}
for line in open(gpath):
    r=json.loads(line); n=r["name"]
    deps=list(dict.fromkeys(r.get("type_deps",[])+r.get("value_deps",[])))
    if n in names_needed: outdeg[n]=len(deps)
    for dd in deps:
        if dd in names_needed: indeg[dd]+=1
def lookup(d0):
    nm=d0
    for d in man["decls"]:
        if d["theorem"]==d0:
            for ns in d.get("namespace",[]):
                if ns+"."+d0 in outdeg: return ns+"."+d0
    return d0 if d0 in outdeg else None
for r in rows:
    key=lookup(r["theorem"])
    r["indeg"]=indeg.get(key,0) if key else 0
    r["outdeg"]=outdeg.get(key,0) if key else 0
    r["matched"]=key is not None
print(f"graph-matched: {sum(r['matched'] for r in rows)}/{len(rows)}", flush=True)

# ---- gates ----
pats=collections.Counter(r["pattern"] for r in rows)
n=len(rows)
distinct=len(pats); maxshare=max(pats.values())/n if n else 1
allbreakers=collections.Counter()
broken=[r for r in rows if r["breaks"]]
for r in broken:
    for m in set(r["breaks"]): allbreakers[m]+=1
nb=len(broken)
big_breakers=[m for m,c in allbreakers.items() if nb and c/nb>=0.10]
never=sum(1 for r in rows if not r["breaks"])/n if n else 1
print(f"\n== STRUCTURED gate ==")
print(f"  distinct patterns={distinct} (need>=3)  max-share={maxshare:.2f} (need<=0.70)")
print(f"  breakers>=10% of broken: {len(big_breakers)} {big_breakers[:6]} (need>=3)")
print(f"  never-break fraction={never:.2f} (DEGENERATE if >0.50)")
structured = distinct>=3 and maxshare<=0.70 and len(big_breakers)>=3 and never<=0.50

mr=np.array([r["math_res"] for r in rows]); ir=np.array([r["infra_res"] for r in rows])
li=np.log1p([r["indeg"] for r in rows]); lo=np.log1p([r["outdeg"] for r in rows])
na=np.array([r["n_amb"] for r in rows],float)
ok=~np.isnan(mr)
X=np.column_stack([li,lo,na,np.where(np.isnan(mr),np.nanmean(mr),mr),np.ones(len(ir))])
beta,*_=np.linalg.lstsq(X,ir,rcond=None)
resid=ir-X@beta
R2=1-((resid**2).sum()/max(1e-12,((ir-ir.mean())**2).sum()))
one_minus=1-R2
degen=(collections.Counter(np.round(ir,3)).most_common(1)[0][1]/len(ir))
print(f"\n== INFRA-DISTINCT gate (decisive) ==")
print(f"  infra-res: mean={ir.mean():.2f} degenerate-share={degen:.2f} (need<0.90)")
print(f"  1-R2(infra ~ indeg+outdeg+n_amb+math) = {one_minus:.3f} (need>=0.30)")
# split-consistency: I1-only vs I2&I3 residuals
def axis_res(movs):
    vals=[]
    for r in rows:
        f=r["file"]
        xs=[1.0 if main.get((f,m))=="SURVIVE" else 0.0 for m in movs if main.get((f,m)) in ("SURVIVE","BREAK")]
        vals.append(np.mean(xs) if xs else np.nan)
    return np.array(vals)
i1=axis_res(["I1_shadow"]); i23=axis_res(["I2_synthHB","I3_synthSize"])
m1=~np.isnan(i1)&~np.isnan(i23)
def rescontrol(y):
    b,*_=np.linalg.lstsq(X[m1],y[m1],rcond=None); return y[m1]-X[m1]@b
if m1.sum()>5 and np.std(i1[m1])>0 and np.std(i23[m1])>0:
    cc=np.corrcoef(rescontrol(i1),rescontrol(i23))[0,1]
else: cc=float('nan')
print(f"  split-consistency corr(I1-resid, I2&I3-resid) = {cc:.3f} (need>=0.5)")
infra_ok = one_minus>=0.30 and degen<0.90 and (cc>=0.5 if not np.isnan(cc) else False)

print(f"\n== VERDICT (locked; n={n}, power caveat SE~0.11) ==")
if void: print("  RUN VOID (fidelity)")
elif not structured:
    if never>0.50: print("  DEGENERATE-FLAT: majority of theorems break nowhere -> lattice degenerate -> DEAD.")
    elif maxshare>0.70 or distinct<3: print("  TRIVIAL: breaking pattern dominated by one mode -> DEAD.")
    else: print("  NOT STRUCTURED (breaker diversity fail) -> DEAD.")
elif infra_ok:
    print("  ALIVE: lattice structured AND infra-resistance survives degree+math controls -> recommend resistance-navigator next session.")
else:
    if one_minus<0.30: print("  DEGREE: infra-resistance explained by degree/math controls -> seventh confound -> DEAD (stated prior).")
    else: print("  AMBIGUOUS: structured but infra-distinctness inconsistent -> report, do not build.")

json.dump({"rows":[{k:(v if not isinstance(v,tuple) else list(v)) for k,v in r.items()} for r in rows]},
          open(BASE/"lattice_rows.json","w"), indent=0)
print("\nrows -> lattice_rows.json", flush=True)
