# PRE-REGISTRATION — Probe 16: term-space failure anisotropy

STATUS: pre-registered. Committed **before** the run. One round, single batch. No follow-up rounds
are authorised. Occupancy sweep (`SWEEP.md`) completed first: NOT OCCUPIED on the question,
[occupied] on every component, margin recorded as thin.

## Pinned environment (manifest)

| item | value |
|---|---|
| Mathlib commit SHA | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`) |
| Lean toolchain | `leanprover/lean4:v4.28.0` |
| algebraic module | `Mathlib/Algebra/Group/Basic.lean` |
| order-theoretic module | `Mathlib/Order/Basic.lean` |
| elaboration budget | `-DmaxHeartbeats=400000`, fixed for every cell |

Module choice follows the directive's own named examples. It was made from a *structural* census
(how many theorems carry explicit hypotheses / class binders / finiteness assumptions), before any
perturbation was elaborated. Direction coverage is an **outcome**, reported, not something to shop
substrates for.

## Hypothesis

**H1 (claim).** The failure field around a proven term is **anisotropic**: some perturbation
directions break elaboration immediately, others tolerate several steps, and *which is which is a
property of the theorem*, not of the perturbation generator.

**H0 (null).** Failure depends only on perturbation depth, not direction — every theorem is equally
brittle in every direction. A real and acceptable outcome.

## Perturbation directions (six, fixed; supplied by the type theory, not invented)

| # | direction | depth = | implementation (uniform, deterministic) |
|---|---|---|---|
| D1 | delete a hypothesis | number deleted | drop k explicit propositional binders `(h : P)` from the signature, left-to-right |
| D2 | weaken a typeclass to an ancestor | steps up the hierarchy | restate with a fresh type variable carrying the class k steps up a fixed ladder (e.g. `CommGroup→Group→Monoid→Semigroup`, `LinearOrder→PartialOrder→Preorder`) |
| D3 | generalise a universe level | levels generalised | replace k concrete `Type` / fixed-level binders by `Type*` |
| D4 | replace an instance with a more general one | steps in instance graph | generalise k instance binders *appearing in the theorem's own signature* along a fixed instance ladder (`Fintype→Finite`, `DecidableEq→_`, `LinearOrder→PartialOrder`) |
| D5 | generalise a bound variable's type | steps | replace k occurrences of a concrete type (`ℕ`,`ℤ`,`ℚ`,`ℝ`) bound in the statement by a fresh type variable plus its minimal class binder from a fixed table |
| D6 | drop a `Decidable`/`Fintype`/finiteness assumption | number dropped | delete k binders whose class is in `{Decidable, DecidableEq, DecidablePred, Fintype, Finite}` |

**No seventh direction may be added.** A direction that turns out inapplicable to a theorem is
recorded **N/A**, never substituted.

## Measurable, and the availability confound

For theorem `t` and direction `Dᵢ`:

- `cap[t][i]` = the largest depth the direction can even be applied to at (0 if inapplicable).
- The perturbed statement is elaborated with the theorem's **original proof replayed** under it
  (prefix-verbatim file context, original theorem truncated out so it cannot close its own
  perturbation). Whether the cell was decided by proof-term recheck or tactic replay is recorded
  per cell.
- `S[t][i]` = the number of consecutive depths from 1 upward that still elaborate (0 … cap).
- **`R[t][i] = S[t][i] / cap[t][i]`**, defined only where `cap ≥ 1`. `R` is the analysed quantity;
  using raw `S` would confound rigidity with how many steps the direction happened to offer.
- Cells with `S = cap` are **right-censored** (survived everything available); censoring rate is
  reported per direction.

The per-theorem object is the **6-tuple** `(R[t][D1] … R[t][D6])`, multi-component by construction.

## Condition matrix — ONE ROUND

- **Theorems:** ~300, all parseable theorems with ≥1 applicable direction from the two modules
  above (order of appearance, no cherry-picking).
- **Directions:** all six. **Depths:** 1, 2, 3.
- **Harness-validity cell (must pass or the run is VOID):**
  - *Trivialities* (30, synthesised): statements carrying **decorative** structure — unused
    hypotheses and a deliberately over-strong class binder — proved by a trivial term
    (`rfl`/`mul_one`-style). Their decorative structure *should* tolerate perturbation.
  - *Deep* (30): the corpus theorems with the **most explicit hypotheses** (deterministic rule),
    whose hypotheses are load-bearing.
  - **Test:** mean `R` of trivialities > mean `R` of deep theorems, Mann–Whitney *p* < 0.01. If the
    instrument cannot separate decorative from load-bearing structure it is **blind**, the run is
    uninterpretable, **and that failure is the published verdict.**
- **Negative control:** for each direction column independently, permute cell values **across
  theorems** (preserves each direction's marginal distribution, destroys theorem-level coherence),
  1000 replicates; recompute the anisotropy statistic.
- Every elaboration outcome is logged with error class and failing subterm where available.

Total ≈ 330 × 6 × 3 ≈ 5,900 elaborations plus controls. Bounded.

## Anisotropy statistic (fixed here, before running)

On the matrix `R` (rows = theorems, columns = directions, N/A excluded pairwise):

```
V_T = variance across theorems of the row means of R      (theorem effect)
V_D = variance across directions of the column means of R  (direction effect)
A   = V_T / (V_D + 1e-9)
```

`A_obs` is compared with `A_shuffled` = mean of `A` over the 1000 column-wise permutation
replicates described above. (The permutation preserves `V_D` exactly and reduces `V_T` to its noise
floor, so the control genuinely collapses `A`.)

A direction enters the statistic only if it is applicable (`cap ≥ 1`) to **≥30% of theorems**;
directions below that threshold are reported with their coverage but excluded from `A`, and the
exclusion is stated in the results.

## Interpretation rules — FIXED NOW, applied mechanically at the end (verbatim from directive §5)

Do not re-litigate, re-tune, or run "one more sweep."

- **PASS** — tuples are anisotropic, cluster by *theorem* rather than by *direction*, and exceed the
  shuffled control by ≥3× on the anisotropy statistic. The failure field has structure.
- **NULL** — tuples are direction-dominated: direction `Dᵢ` fails at approximately the same depth
  regardless of theorem. No structure. CLOSED.
- **CEILING (not a null)** — >90% of cells fail at depth 1, or <10% ever fail. No headroom. Report
  explicitly as a ceiling, never as a null, and do not re-tune depths to escape it.
- **VOID** — harness cell fails. Publish that as the verdict.
- Anything else: **"inconclusive at this scale with this method"**, which is a binding terminal
  verdict, recorded as CLOSED, never as pending.

## Kill conditions

- Harness-validity cell fails → **VOID**, published.
- Fewer than two directions clear the 30% coverage threshold → the tuple cannot support an
  anisotropy claim → **"inconclusive at this scale with this method"**, CLOSED.
- Fidelity: a duplicate shard is elaborated independently; cell-level disagreement > 2% → **VOID**.
- No re-tuning of depths, ladders, module choice, or the statistic after seeing results.

## Ceiling on any positive (stated before effort is spent)

A PASS yields a **measurement instrument**, not a conjecturer. It would be the first evidence that
anything about Mathlib is anisotropic — against fifteen documented nulls — but it measures the
library's *rigidity structure*, not what is true and not what is worth proving. The results file
must say this explicitly in a "what is NOT claimed" section.
