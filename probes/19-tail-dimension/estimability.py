#!/usr/bin/env python3
"""
Probe 19 — ESTIMABILITY CEILING.  Maximum rank distinguishable at N samples, per cell.

Three bounds, all reported; r_max is their minimum.

  (i)   algebraic       r <= min(#pasts, #futures)
  (ii)  minimax/param   a rank-r conditional matrix on m pasts x f futures has r(m+f-r) free
                        parameters; minimax risk for rank-r estimation scales as r(m+f)/N, so the
                        model is not distinguishable from a lower-rank one unless N >= r(m+f-r).
                        r_param = largest r satisfying that.
  (iii) per-row SNR     row u is a multinomial estimate from n_u draws, so E||p_hat_u - p_u||^2
                        <= 1/n_u and the stacked noise has spectral norm ~ sqrt(m/nbar).  The
                        signal obeys sum_i sigma_i^2 = ||H||_F^2 <= m, so r sigma_r^2 <= m forces
                        r <= nbar (the mean count per past).

N is taken as **20,000** — the number of independent declarations, as the directive states.
Windows drawn from the same declaration's chain overlap and are not independent, so the window
count (~207k-245k) is reported as a permissive secondary only.

A cell with effective rank >= 0.8 * r_max is a CEILING cell, not a measurement, and is excluded
from any Rule-B growth-law fit.
"""
import json, math
import numpy as np

SP = "/tmp/claude-0/-home-user-Structure-Backprop/a747742e-9a2f-5c79-9f64-ed3bc601f93e/scratchpad/p19"
N_INDEP = 20000

d = json.load(open(f"{SP}/cells.json"))
cells, meta = d["cells"], d["meta"]


def r_param(m, f, N):
    """largest r with r(m+f-r) <= N."""
    s = m + f
    if s * s < 4 * N:
        return min(m, f)                      # constraint never binds
    r = (s - math.sqrt(s * s - 4 * N)) / 2.0
    return max(1, min(int(math.floor(r)), min(m, f)))


out = {}
print(f"{'cell':9s} {'arm':10s} {'m':>7s} {'f':>7s} {'nbar':>8s} "
      f"{'r_alg':>6s} {'r_par':>6s} {'r_snr':>6s} {'r_max':>6s} {'eff':>5s}  flag")
for k in range(4):
    for L in (1, 2, 3):
        key = f"k{k}_L{L}"
        c = cells[key]
        out[key] = {}
        for arm in ("real", "shuffle", "synthetic"):
            a = c[arm]
            m, f, nbar = a["pasts"], a["futures"], a["mean_count_per_past"]
            r_alg = min(m, f)
            rp = r_param(m, f, N_INDEP)
            rp_win = r_param(m, f, a["windows"])
            rs = max(1, int(math.floor(nbar)))
            rmax = min(r_alg, rp, rs)
            er = a["eff_rank"]
            ceil = er >= 0.8 * rmax
            out[key][arm] = dict(pasts=m, futures=f, nbar=nbar, r_alg=r_alg, r_param=rp,
                                 r_param_windows=rp_win, r_snr=rs, r_max=rmax,
                                 eff_rank=er, ceiling_estimability=bool(ceil))
            print(f"{key:9s} {arm:10s} {m:7d} {f:7d} {nbar:8.2f} {r_alg:6d} {rp:6d} "
                  f"{rs:6d} {rmax:6d} {er:5d}  {'CEILING' if ceil else '-'}")

json.dump(out, open(f"{SP}/estimability.json", "w"), indent=1)

print("\nsummary (real arm): cell  eff_rank / r_max  -> flag")
for k in range(4):
    for L in (1, 2, 3):
        r = out[f"k{k}_L{L}"]["real"]
        print(f"  k={k} L={L}   {r['eff_rank']:4d} / {r['r_max']:4d}   "
              f"{'CEILING (excluded from any Rule-B fit)' if r['ceiling_estimability'] else 'below ceiling'}")
nc = sum(1 for k in range(4) for L in (1, 2, 3) if out[f"k{k}_L{L}"]["real"]["ceiling_estimability"])
print(f"\nreal-arm CEILING cells: {nc} of 12")
ns = sum(1 for k in range(4) for L in (1, 2, 3) if out[f"k{k}_L{L}"]["synthetic"]["ceiling_estimability"])
print(f"synthetic-arm CEILING cells: {ns} of 12")
