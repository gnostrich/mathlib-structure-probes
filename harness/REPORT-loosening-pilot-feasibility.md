# REPORT — loosening-lattice pilot: preamble gate FAILED in this session; design frozen for a runnable one

Per the pilot protocol ("confirm (a),(b),(c); if any is false, stop and report"), this session's
output is a stop-report, not results. No prereg is committed here because no run can happen here;
the design below is frozen now (before any results exist anywhere) so the executing session can
commit it as its prereg verbatim, or report deviations.

## Preamble verdict

- **(a) PASS** — substrate identified: `Mathlib.Algebra.GroupWithZero.Basic` (77 theorems; 30–100
  window; self-contained; source in the v4.28.0 clone, dependencies in the faithful graph).
- **(c) PASS** — instance / coercion / `@[simp]` structure statically inspectable in-corner.
- **(b) FAIL** — no fixed bounded prover exists in this session. Re-verified at report time: the
  Lean toolchain is egress-blocked (elan tarball via github releases → HTTP 403; mathlib olean
  cache unreachable; no local `lean`/`lake`/`elan`). Established at session start; policy binds at
  session start, so this cannot change within this session.

## Why the two available workarounds are the hatch (refused, with reasons)

1. **Static simulation of "still proves"** (check whether the dropped hypothesis / swapped instance
   appears in the proof's `value_deps`): degenerate by construction. Mathlib lints unused
   hypotheses, so math-loosenings break ~uniformly (trivial lattice); infra-"resistance" becomes a
   count of instance dependencies = **infrastructure degree — the seventh confound, built in by
   definition**. This measures usage-counting, not provability-under-loosening.
2. **Aristotle as the prover:** (i) it is an unbounded agentic search — no budget cap, no
   held-fixed prover; resistance would measure Aristotle-variance (the pilot's own
   "prover-in-disguise" failure mode, adopted as the instrument); (ii) variant generation cannot be
   validated blind — dropping/weakening a hypothesis typically ill-types the *statement*, and with
   no local elaborator "loosening broke the proof" (signal) is indistinguishable from "variant is
   ill-typed" (noise) before shipping; an agentic intermediary may also silently repair variants.
   An unfaithful lattice makes ALIVE and DEAD both meaningless.

## The concrete unlock (cheap, known)

Egress policy binds at session start, and fuller egress has already been enabled account-side. A
**fresh session** in which `elan` + `lake exe cache get` succeed has everything needed:

- **Fixed bounded prover** = the Lean elaborator replaying each theorem's ORIGINAL proof under the
  loosened context with a fixed `maxHeartbeats` cap. Deterministic, budget-capped, prover-constant —
  exactly what the pilot requires (no ML prover anywhere).
- Fast local iteration to validate each variant's *statement well-formedness* on control cases
  before measurement (well-formedness validation is not tuning; the move-list stays fixed).
- Cost: 77 theorems × (~10 single loosenings + ~3 pairs) ≈ ~1,000 capped elaborations, seconds each
  → a single session.

## Frozen draft design (for the executing session to adopt as prereg)

- **Substrate:** `Mathlib.Algebra.GroupWithZero.Basic` (77 theorems).
- **Move-list (named, finite; file-edit recipes; NO arbitrary perturbation):**
  - Math: M1 drop each explicit non-instance hypothesis (one at a time); M2 weaken the ambient
    class one canonical step (`GroupWithZero → MonoidWithZero`); M3 remove `Nontrivial` where present.
  - Infra: I1 shadow the canonical instance with a locally declared defeq-different copy
    (MulOpposite-transported); I2 replace defeq closure with propositional rewriting (original
    `rfl`/unfold steps forced through `rw` with the corresponding `@[simp]` equation lemmas);
    I3 instance→superclass binder split; I4 break the zero-coercion path (route `(0 : G₀)` through
    a local non-canonical `OfNat` instance).
  - Each recipe's exact spelling must be validated for statement well-formedness by the executing
    session on control theorems BEFORE measurement; recipes may be dropped for ill-formedness but
    never tuned toward producing structure.
- **Resistance(t)** = minimal loosening-depth to break (1 = breaks under some single loosening,
  2 = only under some pair, ∞ = never breaks in the list). Also record the break-set (which moves).
- **Budget-sensitivity rail:** run the full lattice at two heartbeat caps (e.g. 200k / 400k);
  report the fraction of (theorem, loosening) cells that flip; > 10% flips ⇒ prover-leak flag.
- **Locked gates:**
  - *Structured:* ≥ 3 distinct resistance values, no single value covering > 70% of theorems, and
    ≥ 3 distinct moves each being the first-breaker for ≥ 10% of theorems. Reject
    all-break-on-one (TRIVIAL) and > 50%-never-break (DEGENERATE).
  - *Infra-distinct (decisive):* `1 − R²(infra-resistance ~ log-indeg + log-outdeg +
    #instance-binders + math-resistance) ≥ 0.30`, AND split-half reproducibility of that residual
    across the infra move-list ≥ 0.5. DEGREE = residual dies under the degree terms (the expected
    outcome — seventh confound); TRIVIAL/FLAT per the structured gate; else AMBIGUOUS.
  - Power caveat (honest): n = 77, so SE(ρ) ≈ 0.11 — the gates are coarse by design; borderline
    numbers read AMBIGUOUS, not ALIVE.
- **Rails carried over:** measurement only (no EBM/sampler/continuation formalism); prover held
  fixed; degree-residual is the decisive number; bounded budget mandatory; one pilot, no move-list
  tuning toward structure.

## One-line call

The pilot is well-scoped and cheap **in a fresh session with a working toolchain**; in this session
it cannot be run faithfully, and running it unfaithfully would be the hatch — so it was not run.
