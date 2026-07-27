# Results — module-level pre-test (this session, coarse)

Ran on a fresh shallow clone of mathlib4 (8,273 files). Direct-import module DAG:
V=8,273  E=25,774  b1=17,504  b1/V=2.12  (DAG confirmed after fixing parser).

Parser bugs found & fixed en route (fidelity provenance):
- new module system uses `public import` (not bare `import`).
- `import Mathlib...` strings inside docstrings faked a 1,288-node SCC — fixed by
  reading only the genuine top import block (block-comment aware, stop at 1st cmd).
- depth needed reverse-topological order.

Metrics: slide = {in-degree, depth}; loop = {square-clustering, triangles}.
- rho(loop, in-degree): 0.13 (sqclust), 0.42 (triangles)
- rho(loop, depth): 0.05, -0.10   (loop ~independent of depth)
- loop-R^2 explained by slide: 0.009 (sqclust), 0.21 (triangles)   [LOW = orthogonal]
- tercile cells: high-slide/low-loop=884, low-slide/high-loop=174 (both populated)
- qualitative: top in-degree = pure plumbing (Tactic.Attr.Register, Init,
  Manifold.Notation; zero loop). top triangles = cohesive math cluster
  (Probability.Gaussian.*, BrownianMotion).

Verdict vs corrected pre-reg: NO WALL. sqclust track = GO (rho<=0.4, R2<=0.5,
cells populated); triangle track = borderline (rho=0.42). Loop is a distinct axis
from centrality/depth, pointing at cohesive subfields not plumbing.

SCOPE: module granularity only. Module "loops" are import-convergence diamonds,
NOT concept-space cycles. This tests the H1 precondition (loop != slide on the real
graph) and passes it weakly. It does NOT test H2 (loop predicts significance). The
decl-level test with proof edges is the decisive one.
