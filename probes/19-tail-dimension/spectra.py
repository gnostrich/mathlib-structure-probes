#!/usr/bin/env python3
"""
Probe 19 — the 36-cell condition matrix.  Fixed by PREREG.md.

k in {0,1,2,3} x L in {1,2,3} (R = 3 fixed) x arm in {real, shuffle, synthetic}.
Per cell: H[u,v] = P(future v | past u) over observed contexts, SVD, full spectrum reported
(truncated at 300 values; a cell that reaches the truncation bound is flagged CEILING).

Effective rank = # singular values above the 95th percentile of the SHUFFLE spectrum at the
same (k, L).
"""
import json, os, collections
import numpy as np
import scipy.sparse as sp
from sklearn.utils.extmath import randomized_svd

SP    = "/tmp/claude-0/-home-user-Structure-Backprop/a747742e-9a2f-5c79-9f64-ed3bc601f93e/scratchpad"
OUT   = f"{SP}/p19"
SEED  = 20260729
R     = 3
NSV   = 300
TRANS = np.array([[.80, .15, .05], [.05, .80, .15], [.15, .05, .80]])

d = np.load(f"{OUT}/tape.npz")
T, LEN = d["T"], d["LEN"]
meta = json.load(open(f"{OUT}/tape_meta.json"))
NS, CAP = T.shape[1], T.shape[2]
print(f"tape {T.shape}, mean len {LEN.mean():.1f}", flush=True)


def seqs_from(M):
    """ascending-depth order: column 0 of the tape is the DEEP end, so reverse each row."""
    return [M[r, :LEN[r]][::-1] for r in range(NS)]


def shuffled(M, rng):
    S = M.copy()
    for j in range(CAP):
        idx = np.flatnonzero(LEN > j)
        if len(idx) > 1:
            S[idx, j] = S[rng.permutation(idx), j]
    return S


def synthetic(A, unigram, rng):
    """hand-built 3-state HMM, alphabet size A, emissions = 3 tilted copies of the real unigram."""
    order = np.argsort(-unigram)
    blocks = [order[i::3] for i in range(3)]
    E = np.zeros((3, A))
    for i in range(3):
        b = np.zeros(A, bool); b[blocks[i]] = True
        inb = unigram * b; out = unigram * (~b)
        inb = inb / inb.sum() if inb.sum() > 0 else b / max(b.sum(), 1)
        out = out / out.sum() if out.sum() > 0 else (~b) / max((~b).sum(), 1)
        E[i] = .90 * inb + .10 * out
    M = np.full((NS, CAP), -1, dtype=np.int32)
    cdfT = np.cumsum(TRANS, 1); cdfE = np.cumsum(E, 1)
    for r in range(NS):
        s = int(rng.integers(3)); L = int(LEN[r])
        for t in range(L):
            M[r, L - 1 - t] = int(np.searchsorted(cdfE[s], rng.random()))   # deep end at col 0
            s = int(np.searchsorted(cdfT[s], rng.random()))
    return M


def hankel(seqs, L):
    pid, fid = {}, {}
    pr, fc = [], []
    for s in seqs:
        m = len(s) - L - R + 1
        for t in range(m):
            pu = s[t:t + L].tobytes(); fv = s[t + L:t + L + R].tobytes()
            i = pid.get(pu)
            if i is None: i = len(pid); pid[pu] = i
            j = fid.get(fv)
            if j is None: j = len(fid); fid[fv] = j
            pr.append(i); fc.append(j)
    if not pr:
        return None, 0, 0, 0, 0.0
    pr = np.array(pr); fc = np.array(fc)
    C = sp.coo_matrix((np.ones(len(pr)), (pr, fc)), shape=(len(pid), len(fid))).tocsr()
    rs = np.asarray(C.sum(1)).ravel()
    H = sp.diags(1.0 / rs) @ C
    return H, len(pr), len(pid), len(fid), float(rs.mean())


def spectrum(H):
    mn = min(H.shape)
    k = min(NSV, mn)
    if mn <= NSV and max(H.shape) <= 4000:
        return np.linalg.svd(H.toarray(), compute_uv=False)[:k], k
    U, s, Vt = randomized_svd(H, n_components=k, n_iter=7, random_state=SEED)
    return s, k


cells = {}
for k in range(4):
    M = T[k]
    A = meta["alphabets"][k]["alphabet"]
    rng = np.random.default_rng(SEED + 1000 * k)
    uni = np.bincount(M[M >= 0].ravel(), minlength=A).astype(float); uni /= uni.sum()
    arms = {"real": M, "shuffle": shuffled(M, rng), "synthetic": synthetic(A, uni, rng)}
    for L in (1, 2, 3):
        spec = {}
        for arm, MM in arms.items():
            H, nw, npst, nfut, meanc = hankel(seqs_from(MM), L)
            s, kk = spectrum(H)
            spec[arm] = dict(sv=[float(x) for x in s], nsv=int(kk), windows=nw,
                             pasts=npst, futures=nfut, mean_count_per_past=meanc)
            print(f"  k={k} L={L} {arm:9s} win={nw:7d} pasts={npst:7d} futs={nfut:7d} "
                  f"mean/past={meanc:6.2f} sv[0]={s[0]:.3f} nsv={kk}", flush=True)
        thr = float(np.percentile(spec["shuffle"]["sv"], 95))
        for arm in spec:
            sv = np.array(spec[arm]["sv"])
            er = int((sv > thr).sum())
            spec[arm]["eff_rank"] = er
            spec[arm]["ceiling_sv"] = bool(er >= spec[arm]["nsv"])
            spec[arm]["ceiling_data"] = bool(spec[arm]["mean_count_per_past"] < 5)
        spec["threshold"] = thr
        cells[f"k{k}_L{L}"] = spec
        print(f"  -> k={k} L={L} thr={thr:.4f} eff_rank real={spec['real']['eff_rank']} "
              f"shuffle={spec['shuffle']['eff_rank']} synth={spec['synthetic']['eff_rank']} "
              f"| ceiling_sv={spec['real']['ceiling_sv']} starved={spec['real']['ceiling_data']}",
              flush=True)

json.dump(dict(meta=meta, cells=cells), open(f"{OUT}/cells.json", "w"))

# ---- harness ---------------------------------------------------------------------------
harness = [(k, L, cells[f"k{k}_L{L}"]["synthetic"]["eff_rank"]) for k in range(4) for L in (1, 2, 3)]
bad = [(k, L, e) for k, L, e in harness if not (2 <= e <= 4)]
print("\nHARNESS (synthetic must be 2-4 at every k,L):",
      "PASS" if not bad else f"FAIL at {bad}", flush=True)

# ---- plot ------------------------------------------------------------------------------
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
fig, ax = plt.subplots(4, 3, figsize=(13, 15), sharex=False)
for k in range(4):
    for li, L in enumerate((1, 2, 3)):
        a = ax[k][li]; c = cells[f"k{k}_L{L}"]
        for arm, col in (("real", "C0"), ("shuffle", "C1"), ("synthetic", "C2")):
            sv = np.array(c[arm]["sv"])
            a.semilogy(np.arange(1, len(sv) + 1), np.maximum(sv, 1e-12), col, lw=1.4, label=arm)
        a.axhline(c["threshold"], color="k", ls="--", lw=.9, label="shuffle p95")
        a.set_title(f"k={k}, L={L}  (eff rank real={c['real']['eff_rank']}, "
                    f"synth={c['synthetic']['eff_rank']})", fontsize=9)
        a.set_xlabel("index"); a.set_ylabel("singular value")
        if k == 0 and li == 0: a.legend(fontsize=8)
fig.suptitle("Probe 19 — Hankel spectra of the Mathlib prerequisite tape (R=3)", fontsize=12)
fig.tight_layout()
fig.savefig(f"{OUT}/spectra.png", dpi=110)
print("wrote cells.json / spectra.png", flush=True)
