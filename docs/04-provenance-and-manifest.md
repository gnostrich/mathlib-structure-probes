# 04 — Provenance & external files to drop in

## The certified generator ("the actual thing as built")
Built in chat "Gauge-covariant free energy and state transitions" (CPP 2027
paper thread). Shipped artifact: **certified-positivity-artifact.zip**
- 59 Lean files; 170 strict declarations (137 theorems + 33 lemmas); 3 files with
  `sorry` under one root; builds with the included lakefile.toml / lean-toolchain /
  lake-manifest.json (pinned Mathlib). NOTE: not compiled in-container in that chat
  either — run `lake build` locally.
- Objects to reuse: `GramState`, `expand`, `expand_pd` (certificate-carrying
  self-expansion), `halt_not_pd` + `haltWitness` (honest halt = certified
  counterexample), `isPDq_iff_nMinus_nZero` (inertia meter = certifier; Sylvester),
  `checkPDq` (R-B1 executable reflection). Suzuki zeta screw kernel transcribed;
  3×3 real-kernel PD window, margin >= 0.005 (first machine-checked instance of
  Suzuki Thm 4.2); positivity persists across first prime entry.
- Companion docs from that chat: cpp2027-paper.pdf/.tex, SIGNOFF.md,
  PAPER2-CONTEXT.md, CONTRIBUTION-MAP.md, aristotle-batch-v6.md.

## DROP-IN LIST for the repo (get these from the gauge-covariant chat outputs)
[ ] certified-positivity-artifact.zip        (the generator + build files)  REQUIRED
[ ] PAPER2-CONTEXT.md                          (the "certified frontier" spec)  useful
[ ] CONTRIBUTION-MAP.md                         (contribution ledger)           useful
These cannot be regenerated here without fabricating; they must be copied over.

## Prior measurements referenced (not files, just numbers to reproduce)
- b₁/V ≈ 25.6, NBC / Ihara-zeta on Mathlib dependency graph (the "Baur-flip" chat).
- Hodge gradient fraction R² ≈ 0.013–0.019 on commit/author-attention flow (the
  autonomous-discovery chat) — the SLIDE-side flat reading; do not conflate with
  the dependency-graph loop side.
