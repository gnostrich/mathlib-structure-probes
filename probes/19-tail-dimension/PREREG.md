# PRE-REGISTRATION — Probe 19: tail dimension of Mathlib (Hankel rank of the prerequisite tape)

**Committed before the tape was built and before any spectrum was computed.** ONE ROUND, single
batch, 36 cells. Interpretation rules fixed here, applied mechanically. No follow-up rounds, no
re-tuning. "Inconclusive at this scale with this method" is a binding terminal verdict, logged
CLOSED, never pending.

Not a conjecturer probe. New registry entry; **no link to the paraconsistent-metric line, which is
CLOSED and stays closed.**

## What is measured

`E = I(shallow half of library ; deep half)` — the tail dimension: how many causal states are needed
to predict deep declarations from shallow ones. **The rank is measured directly.** `E` is *not*
estimated as `L(M) − M·h`; that is a difference of two divergent quantities and is unstable. The
rank **is** the quantity.

## Tape

- **Row** = one declaration. **String** = its prerequisite chain from axioms to itself, read in
  **ascending depth order**.
- **Column axis** = prerequisite depth, using the **intrinsic grading already computed in this
  repository** (probe 17): the faithful declaration-dependency DAG from `DumpDeps.lean`
  (`type_deps ∪ value_deps`), SCC-condensed, longest path to primitives. Reused, not redefined.
- **Chain construction (declared):** the depth-realizing path. From the declaration, repeatedly step
  to a dependency of maximal depth; ties broken by lexicographically smallest name, so the chain is
  deterministic. Along such a path depth falls by exactly 1 per step, so **position in the string is
  exactly prerequisite depth** — the column axis is the grading, not a proxy for it.
- **Cap 24 symbols, truncated from the shallow end, deep end kept.**
- **Sample 20,000 declarations uniformly at random**, `numpy.random.default_rng(20260729)`. Seed
  recorded: **20260729**.
- **Column index used by the shuffle arm** = position counted from the deep end (0 = the declaration
  itself). For strings shorter than the cap, the shuffle permutes within a column only among rows
  that possess that column.

## Alphabet filtration (declared, not tuned)

Nested chain of quotients on each symbol, coarse to fine:

| k | symbol |
|---|---|
| 0 | declaration kind ∈ {def, theorem, instance, structure, abbrev, other} |
| 1 | k=0 + top-level namespace root (first component of the declaration name; `_root_` if none) |
| 2 | k=1 + head type constructor of the statement |
| 3 | k=2 + full namespace path (declaration name minus its final component) |

If the k=3 alphabet exceeds **2000** symbols it is hashed to 2000 buckets and that is recorded.

### Declared deviation — the k=2 component is a source-text surrogate

The faithful dump carries `{name, module, kind, type_deps, value_deps}`; it does **not** carry the
declaration's type expression, and `type_deps` is in `getUsedConstants` traversal order, so its first
element is a binder constant, not the head. The elaborated head is therefore not available without a
fresh Lean extraction, which is out of scope for a one-round probe.

**Surrogate, fixed now:** parse the Mathlib source at `8f9d9cff` (v4.28.0), take the text between the
top-level `:` and the top-level `:=` of each declaration, strip leading binders, and reduce to a head
token with a fixed notation table (`=`→`Eq`, `↔`→`Iff`, `≠`→`Ne`, `≤`→`LE.le`, `<`→`LT.lt`, `∈`→
`Membership.mem`, `⊆`→`HasSubset.Subset`, `∣`→`Dvd.dvd`, `∀`→`Pi`, `∃`→`Exists`, `¬`→`Not`, `∧`→`And`,
`∨`→`Or`, `→`→`Arrow`, otherwise the leading identifier). Symbols with no parsed source — Lean core
constants, anonymous instances, auto-generated declarations — get head `NA`.

**Coverage is reported.** If the `NA` share is high, k=2 collapses toward k=1 and that is recorded as
a *partial* Port-3 failure (rule D territory) rather than smoothed over.

## Condition matrix — single batch, 36 cells

`k ∈ {0,1,2,3}` × `L ∈ {1,2,3}` (future length `R = 3` fixed) × `arm ∈ {real, shuffle, synthetic}`.

Per cell: slide a window over each string in ascending-depth order, collecting (past of length `L`,
next `R = 3` symbols). Build `H[u,v] = P(future v | past u)` over **observed** contexts, take the SVD,
report the **full singular value spectrum**, not just a count.

**Declared computational deviation:** an exact full spectrum is infeasible when the matrix has
hundreds of thousands of observed contexts. The top `N_SV = min(min(dim), 300)` singular values are
computed (dense SVD when `min(dim) ≤ 300`, else `scipy.sparse.linalg.svds`), identically for all three
arms in a cell. **Any cell whose effective rank equals `N_SV` is flagged CEILING — no headroom — and
is not reported as a rank estimate.**

Also recorded per cell: number of windows, distinct pasts, distinct futures, and **mean count per
past context**. Cells with mean count per past `< 5` are flagged **data-starved (CEILING)**, and the
write-up must distinguish ceiling cells from genuine nulls.

### Arms

- **real** — the Mathlib tape as constructed above.
- **shuffle** — symbols permuted within each depth column across declarations. Destroys past/future
  dependence while preserving every column marginal. **Its spectrum is the noise floor.**
- **synthetic** — a hand-built 3-state HMM over an alphabet of the same size, the same number of
  strings (20,000) and the same length cap (24). Fixed now: transition matrix
  `[[.80,.15,.05],[.05,.80,.15],[.15,.05,.80]]`; the alphabet is split into three blocks by
  interleaved unigram-frequency rank, state *i* puts 0.90 of its mass on block *i* and 0.10 on the
  rest, in both cases proportional to the **real** unigram distribution at that k, so the synthetic
  arm inherits the real arm's frequency skew and sampling sparsity rather than being unrealistically
  uniform. Same seed, 20260729.

## HARNESS-VALIDITY CELL — must pass or the whole run is uninterpretable

**The synthetic arm must return effective rank 3 (accept 2–4) at every k and L.** If it does not, the
pipeline is broken, the run is **VOID**, that failure is itself the published verdict, and the real
arm is **not interpreted**.

## Interpretation rules, fixed now

**Effective rank** = number of singular values exceeding the **95th percentile of the shuffle arm's
spectrum at the same (k, L)**.

- **A.** Effective rank saturates below 10 at k=0 → **"Mathlib is effectively finite-state under the
  kind quotient."** Run complete; report and stop.
- **B.** Effective rank grows with L without saturating **and** clears the shuffle floor →
  **divergent tail.** Report the growth law (fit linear, log, power; report which wins by **BIC**).
  No claim beyond the fit.
- **C.** Effective rank indistinguishable from the shuffle floor at all k → **no past–future structure
  in depth; the corpus is memoryless along the prerequisite axis.** Terminal, publishable, CLOSED.
- **D.** Port 3 fails — no constructible filtration (k=0 alphabet degenerate, or the quotient chain
  not nested) → **substrate does not render. F5.** That is the result.
- Anything matching none of the above → **"inconclusive at this scale with this method"**, terminal,
  logged **CLOSED**, never pending.

The write-up must distinguish explicitly between **"no headroom / ceiling reached"** cells and
**genuine nulls**.

## Deliverable

ONE PAGE containing: (1) the 36-cell matrix of effective ranks, (2) the singular value spectra
plotted, real vs shuffle vs synthetic, (3) one verdict sentence, (4) an explicit "what is NOT
claimed" section.

**Mandatory in "what is NOT claimed":** this measures the **formalized corpus** under **one declared
alphabet filtration**. It is **not** a statement about mathematics. Mathlib is a curated artifact
with sociology in it.

## Prior art

**arXiv:2604.24797, "The Network Structure of Mathlib"** — structural/network analysis of the same
corpus, not information-theoretic. It independently reports that centrality captures infrastructure
rather than mathematical relevance. Cited; that is **their** finding, not presented here as new.

Files: `probes/19-tail-dimension/{PREREG.md, tape.py, spectra.py, RESULTS.md, spectra.png, cells/}`
plus one `harness/STATUS.md` registry line, closed with the verdict.
