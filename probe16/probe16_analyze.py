#!/usr/bin/env python3
"""
Probe 16 analysis — applies PREREG-term-anisotropy.md mechanically.
Log -> per-cell adjudication (twin/variant line ranges) -> normalized survival R = S/cap_eff
-> anisotropy A = V_T/V_D with column-wise across-theorem permutation control
-> harness-validity cell -> CEILING check -> verdict from the fixed interpretation rules.
"""
import json, re, collections, pathlib, sys
import numpy as np
from scipy.stats import mannwhitneyu

BASE = pathlib.Path("/tmp/claude-0/-home-user-Structure-Backprop/a747742e-9a2f-5c79-9f64-ed3bc601f93e/scratchpad")
MAN = json.load(open(BASE/"p16_manifest.json"))
RES = BASE/"p16_results"
DEPTHS = (1,2,3)
COVERAGE_MIN = 0.30      # prereg
SHUFFLES = 1000

ERR = re.compile(r'([A-Za-z0-9_]+)\.lean:(\d+):\d+:\s*error(?:\((?P<cls>[^)]*)\))?:?\s*(?P<msg>.*)')

def parse_logs(tagfilter=None):
    """file -> {line: (errclass, msg)}"""
    out = {}
    for lf in RES.rglob("*.log"):
        if tagfilter and tagfilter not in str(lf): continue
        errs = {}
        for line in open(lf, errors="ignore"):
            m = ERR.search(line)
            if m: errs[int(m.group(2))] = (m.group("cls") or "", (m.group("msg") or "")[:120])
        out.setdefault(lf.stem, {}).update(errs)
    return out

def adjudicate(logs):
    """(gid, direction, depth) -> 'OK'|'BREAK'|'NA'; plus canary + baseline validity, error classes"""
    cells = {}; canary_bad = []; baseline_bad = []; errclass = collections.Counter()
    seen = set()
    for d in MAN["decls"]:
        f = d["file"]
        if f not in logs: continue
        seen.add(f); errs = logs[f]
        for e in d["entries"]:
            a, b = e["lines"]
            hit = [errs[x] for x in errs if a <= x <= b]
            if e["role"] == "canary_break":
                if not hit: canary_bad.append((f, "C2 did not fail")); continue
            if e["role"] == "canary_na":
                if not hit: canary_bad.append((f, "C3 did not fail")); continue
            if e["role"] not in ("baseline", "cell"): continue
            ts, vs = e["twin_start"], e["var_start"]
            twin = [errs[x] for x in errs if ts <= x < vs]
            var  = [errs[x] for x in errs if vs <= x <= b]
            if twin:   st = "NA"
            elif var:  st = "BREAK"; errclass[var[0][0] or "unclassified"] += 1
            else:      st = "OK"
            if e["role"] == "baseline":
                if st != "OK": baseline_bad.append(f)
                cells[(d["gid"], "baseline", 0)] = st
            else:
                cells[(d["gid"], e["direction"], e["depth"])] = st
    return cells, canary_bad, baseline_bad, errclass, seen

def survival(cells, gid, direction):
    """cap_eff = leading depths whose STATEMENT is well-formed; S = leading depths that elaborate."""
    cap = 0
    for k in DEPTHS:
        st = cells.get((gid, direction, k))
        if st is None or st == "NA": break
        cap += 1
    if cap == 0: return None, 0
    S = 0
    for k in DEPTHS[:cap]:
        if cells.get((gid, direction, k)) == "OK": S += 1
        else: break
    return S, cap

def build_R(cells, decls):
    dirs = ["D1","D2","D3","D4","D5","D6"]
    rows = []
    for d in decls:
        if (d["gid"], "baseline", 0) not in cells: continue
        if cells[(d["gid"], "baseline", 0)] != "OK": continue      # extraction defect -> excluded
        r = {}
        for dd in dirs:
            S, cap = survival(cells, d["gid"], dd)
            if S is not None: r[dd] = S/cap
        if r: rows.append(dict(gid=d["gid"], theorem=d["theorem"], group=d["group"],
                               n_hyp=d.get("n_hyp",0), R=r))
    return rows, dirs

def anisotropy(M):
    """M: dict dir -> np.array over theorems (nan where N/A). A = V_T/V_D."""
    arr = np.vstack([M[k] for k in M])                     # dirs x theorems
    with np.errstate(invalid='ignore'):
        rowmeans = np.nanmean(arr, axis=0)                  # per theorem
        colmeans = np.nanmean(arr, axis=1)                  # per direction
    V_T = np.nanvar(rowmeans); V_D = np.nanvar(colmeans)
    return V_T/(V_D+1e-9), V_T, V_D

def main():
    logs = parse_logs()
    cells, canary_bad, baseline_bad, errclass, seen = adjudicate(logs)
    print(f"files with logs: {len(seen)} / {len(MAN['decls'])}")
    print(f"canary failures: {len(canary_bad)} {canary_bad[:4]}")
    print(f"baseline (unperturbed) failures -> theorems excluded: {len(baseline_bad)}")
    print(f"error classes on BREAK cells: {dict(errclass.most_common(6))}")

    rows, dirs = build_R(cells, MAN["decls"])
    corpus = [r for r in rows if r["group"]=="corpus"]
    triv   = [r for r in rows if r["group"]=="trivial"]
    print(f"\nanalysable theorems: corpus={len(corpus)} trivialities={len(triv)}")

    n = len(corpus)
    cov = {d: sum(1 for r in corpus if d in r["R"])/max(1,n) for d in dirs}
    print("direction coverage (measurable, cap_eff>=1):", {k:f"{v:.0%}" for k,v in cov.items()})
    live = [d for d in dirs if cov[d] >= COVERAGE_MIN]
    print(f"directions entering the statistic (>= {COVERAGE_MIN:.0%}): {live}")

    # ---- CEILING check (prereg) ----
    allcells = [(r,d) for r in corpus for d in dirs if d in r["R"]]
    fail_at_1 = sum(1 for r,d in allcells if r["R"][d]==0.0)
    ever_fail = sum(1 for r,d in allcells if r["R"][d] < 1.0)
    ceil_lo = fail_at_1/max(1,len(allcells)); ceil_hi = ever_fail/max(1,len(allcells))
    print(f"\nCEILING check: cells failing at depth 1 = {ceil_lo:.1%} (>90% => ceiling); "
          f"cells that ever fail = {ceil_hi:.1%} (<10% => ceiling)")
    ceiling = ceil_lo > 0.90 or ceil_hi < 0.10

    # ---- harness-validity cell (prereg): decorative trivialities vs most-hypothesis-laden corpus ----
    deep = sorted(corpus, key=lambda r: -r["n_hyp"])[:30]
    tv = [np.mean(list(r["R"].values())) for r in triv]
    dv = [np.mean(list(r["R"].values())) for r in deep]
    if tv and dv:
        u, p = mannwhitneyu(tv, dv, alternative="greater")
        print(f"\nHARNESS VALIDITY: mean R trivialities={np.mean(tv):.3f} (n={len(tv)}) vs "
              f"deep={np.mean(dv):.3f} (n={len(dv)}); Mann-Whitney p={p:.2e} (need p<0.01)")
        harness_ok = p < 0.01
    else:
        print("\nHARNESS VALIDITY: insufficient data"); harness_ok = False; p = 1.0

    # ---- anisotropy statistic + control ----
    A_obs = A_sh = float("nan")
    if len(live) >= 2:
        M = {d: np.array([r["R"].get(d, np.nan) for r in corpus]) for d in live}
        A_obs, V_T, V_D = anisotropy(M)
        rng = np.random.default_rng(20260727); As = []
        for _ in range(SHUFFLES):
            Ms = {}
            for d in live:
                col = M[d].copy(); obs = ~np.isnan(col)
                vals = col[obs].copy(); rng.shuffle(vals); col[obs] = vals
                Ms[d] = col
            As.append(anisotropy(Ms)[0])
        A_sh = float(np.mean(As))
        print(f"\nANISOTROPY: V_T={V_T:.4f} V_D={V_D:.4f}  A_obs={A_obs:.3f}  "
              f"A_shuffled={A_sh:.3f}  ratio={A_obs/max(1e-9,A_sh):.2f}x (need >=3x)")
    else:
        print(f"\nANISOTROPY: not computed — only {len(live)} direction(s) clear coverage")

    # ---- fidelity (s0 vs sdup) ----
    l0 = parse_logs("p16_s0"); ld = parse_logs("p16_sdup")
    c0,_,_,_,_ = adjudicate(l0); cd,_,_,_,_ = adjudicate(ld)
    common = set(c0) & set(cd); mism = [k for k in common if c0[k]!=cd[k]]
    fid = len(mism)/max(1,len(common))
    print(f"\nFIDELITY: {len(common)} duplicated cells, {len(mism)} disagreements = {fid:.2%} (VOID if >2%)")

    # ---- verdict, applied mechanically ----
    print("\n" + "="*70)
    if canary_bad or not harness_ok:
        v = "VOID — harness cell fails; published as the verdict."
    elif fid > 0.02 and len(common) > 0:
        v = "VOID — duplicate-shard disagreement exceeds 2%."
    elif ceiling:
        v = "CEILING (not a null) — no headroom; depths NOT re-tuned."
    elif len(live) < 2:
        v = "inconclusive at this scale with this method — CLOSED."
    elif A_obs >= 3*A_sh:
        v = "PASS — failure field is anisotropic and theorem-clustered."
    elif A_obs <= 1.2*A_sh:
        v = "NULL — direction-dominated; no theorem-specific structure. CLOSED."
    else:
        v = "inconclusive at this scale with this method — CLOSED."
    print("VERDICT:", v)
    print("="*70)

    json.dump(dict(coverage=cov, live=live, A_obs=A_obs, A_shuffled=A_sh,
                   harness_p=float(p), fidelity=fid, ceiling_lo=ceil_lo, ceiling_hi=ceil_hi,
                   n_corpus=len(corpus), n_triv=len(triv), verdict=v,
                   errclasses=dict(errclass), rows=[{k:v2 for k,v2 in r.items()} for r in rows]),
              open(BASE/"p16_report.json","w"), indent=1, default=str)

main()
