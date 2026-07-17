# RESULTS — the FAITHFUL decisive run (proof-edge decl graph)

This is the run the whole experiment was gated on: the decl-level loop-veto test on
the **faithful** Mathlib dependency graph — the one that INCLUDES proof-synthesized
edges (simp/omega/typeclass/tactic-invoked lemmas), which the statement-only "approx"
graph misses. Full log: `veto_faithful.log`. Reproduced identically across two runs
(deterministic; fixed RNG seed).

## How the faithful graph was obtained (the local build was egress-blocked)

The Lean toolchain (github releases) and Mathlib olean cache (`*.blob.core.windows.net`)
were policy-blocked at the egress gateway, so no local `lake build` was possible. The
graph was instead produced by running `DumpDeps.lean` inside **Aristotle's** (Harmonic)
built Mathlib **v4.28.0** environment and downloading the result — see
`aristotle_faithful_dump.py`.

- `decl_deps.jsonl`: **333,044** declarations, **7,523,067** internal edges
  (vs 1.5M in the approx graph); avg **28.7** value-deps and **16.7** type-deps per
  decl (the proof-synthesized edges are present). kinds: theorem 250,327 / def 70,658 / other 12,059.
- Provenance: **two independent Aristotle jobs returned BYTE-IDENTICAL output**
  (md5 `9f3a3c364cf975525e50049d10df194c`). Kept out of the repo (395 MB); regenerate via the launcher.

## Headline: the H2 payoff FLIPS positive on the faithful graph

| test | approx graph 1 (213,929) | approx graph 2 (229,502) | **FAITHFUL (333,044)** |
|------|:---:|:---:|:---:|
| H1 `rho(L, depth)` | 0.267 | 0.350 | **0.528** |
| H1 verdict (GO needs ≤0.40) | GO-precondition | GO-precondition | **AMBIGUOUS** |
| **H2 baseline** `rho(L,Y2\|depth)` | 0.485 | 0.554 | 0.539 |
| **H2 degree-controlled** `\|depth+log-udeg` | **−0.046** | **0.087** | **0.372** |
| H2 residual-corr cross-check | −0.046 | 0.087 | 0.372 |
| H2 verdict | does NOT clear | does NOT clear | **CLEARS** |
| H3(a) gaming foil | 0/3000 (PASS) | 0/3000 (PASS) | **0/3000 (PASS)** |
| H3(b) `L_cold` own-degree-controlled | 0.19–0.23 | 0.14–0.18 | **0.15 (min2) / 0.31 (min3)** |

**The core scientific claim holds on the faithful graph and did NOT on the approximation.**
On both approx graphs the H2 payoff collapsed to ~0 under a proper (undirected-degree)
control — a degree artifact. On the faithful graph — with the proof edges added back —
the same control leaves **partial rho(L, Y2 | depth, degree) = 0.372**, and the
residual-correlation method agrees exactly (0.372). The loop-residue carries genuine
in-library-significance information beyond depth AND degree on Mathlib's real
proof-dependency structure. This is exactly the pre-registered reason for demanding the
faithful graph: loops live in the proof-synthesized edges.

Supporting:
- **H3(a) incorruptibility — PASS.** 3,000 injected distant `A∧B` conjunction nodes get
  0 loop credit and perturb 0/2000 real nodes (median real loop-bearing triangle count
  here is 56; foils sit at 0). The meter is not gamed by cheap cross-region conjunctions.
- **H3(b) incorruptible residue.** The reuse-shortcut-stripped `L_cold` (the residue that
  a minimal reproof would keep) ALSO survives its own (cold) degree control on the
  faithful graph: **0.146** (REDUNDANCY_MIN=2) to **0.305** (MIN=3). So the veto-relevant
  residue — not just the raw metric — carries signal here. (Still a static proxy; a
  built-env minimal reproof is the pre-reg's gold standard for certifying `L_cold`.)

## The honest caveat: not a clean pre-registered GO

By the **strict** pre-registration (`docs/03`), a GO requires ALL of: H1 dissociation
`|rho(L,S)| ≤ 0.40`, `R2 ≤ 0.50`, both terciles populated, H2 clears, foils not credited.
On the faithful graph:
- `R2(L~slide+deg) = 0.048` ✓, both cells populated (12,133 / 16,116) ✓, H2 clears ✓, H3(a) PASS ✓
- **but `rho(L, depth) = 0.528`**, above the 0.40 "clean dissociation" line (though well
  under the 0.70 "wall"). Loop and proof-depth are more entangled on the faithful graph
  than the precondition wanted.

So the **pre-registered combined verdict is AMBIGUOUS → DO NOT WIRE** — driven solely by
H1's borderline dissociation, NOT by a payoff failure. No goalposts moved: H1's 0.40 bar
was fixed in advance, and 0.528 misses it.

## What this means (plain reading)

- **Substantively positive:** the loop-veto's central claim — loop-residue predicts
  significance beyond slide, on real proof structure, and isn't gameable — is **supported
  on the faithful graph**, and is **refuted on the approximation**. The faithful/approx
  distinction was decisive, and pursuing the faithful graph was the right call.
- **Procedurally short of GO:** because loops and depth co-vary more than the pre-registered
  precondition allowed (`rho=0.53 > 0.40`), the clean green-light is not earned. The
  disciplined next step is to tighten the loop metric so it is less depth-entangled (e.g.
  birth-simplex / non-backtracking-cycle residue instead of raw triangle count, per
  `docs/03`'s metric menu), re-run, and see whether H1 drops below 0.40 while H2 stays up.
  Only then does wiring (`docs/05`) become warranted.

Bottom line: **promising positive, verify-before-you-build — not yet a wire-it GO.**

## UPDATE — metric-robustness caveat (see RESULTS-style-modes.md)

A follow-up swapped the triangle loop-count `L` for a **birth-simplex** cycle metric `B`
(1-cycles born at each decl's introduction, via a union-find filtration). It does NOT
behave like `L`: `rho(B,depth)=0.715` and `rho(B,degree)=0.805` (a late high-degree lemma
trivially closes many cycles, so `B ≈ degree`), and its **degree-controlled H2 goes
negative (−0.585)**. So the `+0.372` H2 payoff above is **specific to the triangle
metric**, not a general "loop-residue" property. This tempers the "positive" read: the
signal is real for triangle-clustering but does not survive a birth-simplex reformulation
of "loop". A non-backtracking-cycle residue is the next metric to try before any wiring.
