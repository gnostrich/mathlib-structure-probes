#!/usr/bin/env python3
"""
Probe 18 — harmonic-measure growth on a non-amenable graph, by direct Laplace solve.

Dielectric Breakdown Model (Niemeyer-Pietronero-Wiesmann 1984), eta = 1 (equivalent to DLA).
No random walkers: per deposition we SOLVE the discrete Laplace equation

    h = 0 on the cluster,  h = 1 outside the ball of radius R_out,  h harmonic elsewhere

and grow at a perimeter site with probability proportional to h^eta.

Everything here is fixed by PREREG.md (committed before any run):
  rtol = 1e-9, maxiter = 20000, warm-started CG, spsolve validation on the first 20 depositions,
  MAX_DOMAIN = 1_200_000, margins 15 (Z^2) / 5 (T3xZ), seeds 0/1/2, 90-minute per-arm budget.

Usage:
  solver.py --graph z2|t3z --rule eden|dbm --n N --seed S --margin M --out out.json
"""
import argparse, json, math, time
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import cg, spsolve, LinearOperator

# ---- pinned in PREREG.md -----------------------------------------------------------------
MAX_DOMAIN = 1_200_000
RTOL       = 1e-9
MAXITER    = 20000
VALIDATE_STEPS = 20          # spsolve cross-check on the first 20 depositions of every run
BUDGET_SEC = 90 * 60


# ---- substrates --------------------------------------------------------------------------
class Z2:
    name   = "Z2"
    origin = (0, 0)

    @staticmethod
    def nbrs(n):
        x, y = n
        return ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1))

    @staticmethod
    def dist(n):
        return math.hypot(n[0], n[1])

    @staticmethod
    def ball(R):
        R2 = R * R
        Ri = int(math.floor(R))
        out = []
        for x in range(-Ri, Ri + 1):
            ym = int(math.floor(math.sqrt(max(0.0, R2 - x * x))))
            out.extend((x, y) for y in range(-ym, ym + 1))
        return out

    @staticmethod
    def ball_size(R):
        return int(math.pi * R * R) + 4 * int(R) + 1


class T3Z:
    """T_3 x Z.  Node = (v, z), v a tuple of tree digits (the rooted binary tree = 3-regular
    away from the root), z in Z.  dist = len(v) + |z|.  Non-amenable, ambient rate log 2."""
    name   = "T3xZ"
    origin = ((), 0)

    @staticmethod
    def nbrs(n):
        v, z = n
        if v:
            return ((v, z - 1), (v, z + 1), (v + (0,), z), (v + (1,), z), (v[:-1], z))
        return ((v, z - 1), (v, z + 1), (v + (0,), z), (v + (1,), z))

    @staticmethod
    def dist(n):
        return len(n[0]) + abs(n[1])

    @staticmethod
    def ball(R):
        R = int(R)
        out = []
        level = [()]
        for k in range(R + 1):
            span = range(-(R - k), R - k + 1)
            for v in level:
                out.extend((v, z) for z in span)
            if k < R:
                level = [v + (b,) for v in level for b in (0, 1)]
        return out

    @staticmethod
    def ball_size(R):
        R = int(R)
        return sum((2 ** k) * (2 * (R - k) + 1) for k in range(R + 1))


GRAPHS = {"z2": Z2, "t3z": T3Z}


# ---- domain / Laplacian ------------------------------------------------------------------
def build_domain(gr, R):
    """Ball of radius R about the origin, its graph Laplacian, and the Dirichlet-1 load
    b0[i] = number of neighbours of i that fall OUTSIDE the ball (each held at h = 1)."""
    nodes = gr.ball(R)
    n = len(nodes)
    idx = {v: i for i, v in enumerate(nodes)}
    rows = np.empty(5 * n, dtype=np.int32)
    cols = np.empty(5 * n, dtype=np.int32)
    deg = np.empty(n)
    b0 = np.zeros(n)
    e = 0
    for i, v in enumerate(nodes):
        nb = gr.nbrs(v)
        deg[i] = len(nb)
        for m in nb:
            j = idx.get(m)
            if j is None:
                b0[i] += 1.0
            else:
                rows[e] = i; cols[e] = j; e += 1
    A = sp.csr_matrix((-np.ones(e), (rows[:e], cols[:e])), shape=(n, n)) + sp.diags(deg)
    return nodes, idx, A.tocsr(), b0


def solve_field(A, b0, mask, x0):
    """Solve the Dirichlet problem with h = 0 on the cluster.

    With P = diag(mask) (1 on unknowns, 0 on cluster nodes), the operator
    M = P A P + (I - P) is symmetric positive definite on the whole ball, and the solution of
    M x = P b0 has x = 0 on the cluster and A_UU x_U = b0_U on the unknowns.  Warm-started CG.
    """
    n = A.shape[0]
    inv = 1.0 - mask

    def mv(x):
        return mask * (A @ (mask * x)) + inv * x

    M = LinearOperator((n, n), matvec=mv, dtype=float)
    b = mask * b0
    x, info = cg(M, b, x0=mask * x0, rtol=RTOL, maxiter=MAXITER)
    fell_back = False
    if info != 0:                      # exact fallback; recorded, never a different growth rule
        U = np.flatnonzero(mask)
        Auu = A[U][:, U].tocsc()
        xu = spsolve(Auu, b0[U])
        x = np.zeros(n); x[U] = xu
        fell_back = True
    return np.maximum(x, 0.0), fell_back


def exact_field(A, b0, mask):
    U = np.flatnonzero(mask)
    xu = spsolve(A[U][:, U].tocsc(), b0[U])
    x = np.zeros(A.shape[0]); x[U] = xu
    return x


# ---- growth ------------------------------------------------------------------------------
def grow(gr, rule, N, seed, margin, verbose=True):
    rng = np.random.default_rng(seed)
    t0 = time.time()

    cluster = {gr.origin}
    perim = set(gr.nbrs(gr.origin))
    order = [gr.origin]
    Rmax = 0.0

    nodes = idx = A = b0 = None
    x = None                      # warm start, in the current domain's index space
    R_built = -1.0
    fallbacks = 0
    max_dev = 0.0                 # spsolve cross-check on the first VALIDATE_STEPS solves
    solves = 0
    stop = None

    # Z^2 radius-of-gyration trajectory
    sx = float(gr.origin[0]) if gr.name == "Z2" else 0.0
    sy = float(gr.origin[1]) if gr.name == "Z2" else 0.0
    s2 = 0.0
    traj = []                     # (N, R_g)

    while len(cluster) < N:
        if time.time() - t0 > BUDGET_SEC:
            stop = "wall-clock budget (90 min)"
            break

        if rule == "dbm":
            R_out = Rmax + margin
            if R_out > R_built:
                if gr.ball_size(R_out) > MAX_DOMAIN:
                    stop = (f"MAX_DOMAIN guard: ball of radius {R_out:.1f} would hold "
                            f"~{gr.ball_size(R_out):,} nodes > {MAX_DOMAIN:,}")
                    break
                old = None if x is None else {nodes[i]: x[i] for i in range(len(nodes))}
                nodes, idx, A, b0 = build_domain(gr, R_out)
                R_built = R_out
                x = np.ones(len(nodes))
                if old:
                    for i, v in enumerate(nodes):
                        if v in old:
                            x[i] = old[v]
                if verbose:
                    print(f"    [domain] R_out={R_out:.1f} nodes={len(nodes):,} "
                          f"N={len(cluster)} t={time.time()-t0:.0f}s", flush=True)

            mask = np.ones(len(nodes))
            for c in cluster:
                j = idx.get(c)
                if j is not None:
                    mask[j] = 0.0
            x, fb = solve_field(A, b0, mask, x)
            fallbacks += int(fb)
            if solves < VALIDATE_STEPS:
                xe = exact_field(A, b0, mask)
                max_dev = max(max_dev, float(np.max(np.abs(xe - x))))
            solves += 1

            cand = [p for p in perim if p in idx]
            w = np.array([x[idx[p]] for p in cand])
            tot = w.sum()
            if tot <= 0:
                stop = "harmonic measure vanished on every perimeter site"
                break
            pick = cand[int(rng.choice(len(cand), p=w / tot))]
        else:
            cand = list(perim)
            pick = cand[int(rng.integers(len(cand)))]

        cluster.add(pick)
        order.append(pick)
        perim.discard(pick)
        for m in gr.nbrs(pick):
            if m not in cluster:
                perim.add(m)
        Rmax = max(Rmax, gr.dist(pick))

        if gr.name == "Z2":
            sx += pick[0]; sy += pick[1]; s2 += pick[0] ** 2 + pick[1] ** 2
            n = len(cluster)
            rg2 = s2 / n - (sx / n) ** 2 - (sy / n) ** 2
            traj.append((n, math.sqrt(max(rg2, 0.0))))

        if verbose and len(cluster) % 250 == 0:
            print(f"    N={len(cluster)} Rmax={Rmax:.1f} t={time.time()-t0:.0f}s", flush=True)

    return dict(cluster=cluster, order=order, traj=traj, Rmax=Rmax, stop=stop,
                fallbacks=fallbacks, max_dev=max_dev, solves=solves,
                seconds=time.time() - t0)


# ---- observables -------------------------------------------------------------------------
def fractal_D(traj):
    """R_g ~ N^(1/D); discard the first 30% of the trajectory (PREREG)."""
    if len(traj) < 20:
        return float("nan"), 0
    cut = int(0.30 * len(traj))
    pts = [(n, r) for n, r in traj[cut:] if r > 0]
    if len(pts) < 10:
        return float("nan"), len(pts)
    ln = np.log([p[0] for p in pts]); lr = np.log([p[1] for p in pts])
    slope = np.polyfit(ln, lr, 1)[0]
    return (1.0 / slope if slope > 0 else float("nan")), len(pts)


def growth_rate(gr, cluster, Rmax):
    """c = slope of ln N(r) vs r over r in [Rmax/4, 3 Rmax/4] (PREREG)."""
    d = np.array([gr.dist(v) for v in cluster])
    lo = max(1, int(math.ceil(Rmax / 4.0)))
    hi = int(math.floor(3.0 * Rmax / 4.0))
    rs = [r for r in range(lo, hi + 1) if (d <= r).sum() > 0]
    if len(rs) < 2:
        return float("nan"), rs, []
    counts = [int((d <= r).sum()) for r in rs]
    slope = np.polyfit(np.array(rs, float), np.log(counts), 1)[0]
    return float(slope), rs, counts


def is_single_path(gr, cluster):
    return all(sum(1 for m in gr.nbrs(v) if m in cluster) <= 2 for v in cluster)


# ---- main --------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--graph", choices=GRAPHS, required=True)
    ap.add_argument("--rule", choices=["eden", "dbm"], required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--margin", type=float, required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()

    gr = GRAPHS[a.graph]
    tag = f"{gr.name}/{a.rule}/seed{a.seed}/margin{a.margin:g}"
    print(f"[{tag}] target N={a.n}", flush=True)
    r = grow(gr, a.rule, a.n, a.seed, a.margin)

    rec = dict(graph=gr.name, rule=a.rule, seed=a.seed, margin=a.margin,
               N_target=a.n, N=len(r["cluster"]), Rmax=r["Rmax"], stop=r["stop"],
               fallbacks=r["fallbacks"], solves=r["solves"],
               spsolve_max_dev=r["max_dev"], seconds=r["seconds"],
               single_path=bool(is_single_path(gr, r["cluster"])))

    if gr.name == "Z2":
        D, npts = fractal_D(r["traj"])
        rec.update(D=D, fit_points=npts)
    c, rs, counts = growth_rate(gr, r["cluster"], r["Rmax"])
    rec.update(c=c, fit_radii=rs, fit_counts=counts,
               fit_meaningful=bool(len(rs) >= 4 and r["Rmax"] >= 6))

    with open(a.out, "w") as f:
        json.dump(rec, f, indent=1)
    print(f"[{tag}] " + json.dumps({k: v for k, v in rec.items()
                                    if k not in ("fit_radii", "fit_counts")}), flush=True)


if __name__ == "__main__":
    main()
