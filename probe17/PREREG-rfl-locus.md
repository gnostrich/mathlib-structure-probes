# PRE-REGISTRATION — rfl-locus confirmation run (Checks A and B)

STATUS: committed **before** computing D or S. The interpretation ladder is fixed by the directive
and is reproduced verbatim below; this file only pins the operational choices that the directive
leaves open, so they cannot be selected after seeing numbers. One round, terminal.

## Route declaration (Check A)

**Route (a): real dependency extraction from a built Mathlib**, not source-text regex.
Source: `harness/DumpDeps.lean`, run inside a built Mathlib environment; it walks each declaration's
**type and value** with `Lean.Expr.getUsedConstants` — the analogue of the paper's `collectElems`
(signature AND body, every `.const` node). Output `decl_deps.jsonl`, 333,044 declarations.

| item | value |
|---|---|
| Mathlib commit | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`) |
| toolchain | `leanprover/lean4:v4.28.0` |
| extraction | `DumpDeps.lean`, two independent runs, byte-identical output (md5 `9f3a3c36…`) |

**Declared deviations from the paper's construction (fixed now, not after seeing results):**
1. **Multiplicity.** `getUsedConstants` yields the *set* of referenced constants, so edge weights are
   1, not reference multiplicity. Depth is a longest-path (hop) quantity and is **unaffected**.
   Unwrapped length **is** affected: our unwrapped figure is a multiplicity-blind lower bound and is
   reported only as a rank/order-of-magnitude sanity check, never as a replication of their value.
2. **Vertex set.** Nodes are the 333,044 Mathlib declarations; Lean-core constants and `Sort` appear
   as dependency targets with no outgoing edges, i.e. exactly as **primitives at depth 0**. We do not
   claim to reproduce their 463,661-vertex count.
3. **SCC collapse** is applied (condensation) before longest-path, as they do.

## Definitions fixed now

- **depth(u)** = longest path to a primitive in the condensed DAG; primitives (no outgoing
  dependency edges) have depth 0.
- **Classification (directive §5, not loosened).** From source text at the same commit:
  - STRICT definitional: proof body is exactly one of `rfl`, `by rfl`, `Iff.rfl`, `by exact rfl`,
    `HEq.rfl` (whitespace-normalised).
  - `by simp` / `by simp [...]` (and `by simp only [...]`) = a SEPARATE class, reported separately at
    every stage, never merged into definitional.
  - Everything else = SUBSTANTIVE.
  - Classification is **source-text**, so `rfl` hidden behind wrappers is missed; this is a stated
    limitation, and an elaborated-term cross-check (proof-side `value_deps` footprint of
    source-classified `rfl` theorems) is reported alongside.
- **Join**: source-parsed namespace-qualified name ↔ graph declaration name, exact match only;
  join rate reported.
- **D** = AUC(depth → substantive), computed over joined theorems.
- **S (Check B)** = fraction of module-level variance in **strict definitional fraction** explained
  by subject alone, where subject = top-two path components (`Mathlib.Analysis`, `Mathlib.Data.List`,
  …). Model: group mean by subject. `S = 1 − Var(resid)/Var(y)`.
  - **Primary population: modules with ≥20 classified theorems, unweighted across modules** (small
    modules have unstable fractions). The all-modules and size-weighted figures are also reported.

## Interpretation ladder (verbatim from directive §3)

Let D = AUC(their depth -> substantive), S = fraction of module variance explained by subject.

- **CONFIRMED**: D <= 0.60 AND S < 0.50. Native coordinate, orthogonal to their depth, not reducible
  to subject matter.
- **DEPTH-REDUCIBLE**: D >= 0.75. It was depth all along under the coarse proxy. CLOSED.
- **SUBJECT-REDUCIBLE**: S >= 0.80. It is what the file is about. CLOSED.
- **PARTIAL**: anything else. Report both numbers verbatim, claim nothing beyond them, terminal.
- **BLOCKED**: their depth could not be built. Report as such; that is a legitimate terminal verdict.

## Harness-validity cell (directive §4) — must pass or the run is VOID

1. `Mathlib.Logic` + `Mathlib.Init` strict definitional fraction **must exceed** `Mathlib.Analysis`.
2. Reconstructed **max depth must be within an order of magnitude of ~300** (i.e. 30–3000).
3. Reported alongside: whether
   `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType` ranks at the top of
   our (multiplicity-blind) unwrapped-size measure. Because of deviation 1 this is a **soft** check:
   it is reported and interpreted, but only checks 1 and 2 are VOID-bearing.

No follow-up rounds. "Inconclusive at this scale with this method" is terminal, recorded CLOSED.
