# Flywheel mirror — the reasoning DAG of this repository, as a graph

[Paradigma Flywheel](https://docs.flywheel.paradigma.inc/) is "infrastructure for autonomous
research workflows": a graph of evidence-backed hypotheses, claims and conclusions. These scripts
mirror this repository's *chain of reasoning* into it, so the programme is legible as a DAG rather
than as a pile of `RESULTS-*.md` files.

**Live graph: <https://flywheel.paradigma.inc>** — 59 nodes at first build.

## Shape of the graph

```
root — Mathlib structure probes
├── method — the standing discipline (pre-reg, one round, mechanical ladders, nulls first-class)
│   ├── methods-result — rank correlation is inert under extreme class imbalance  [STANDING]
│   └── occupancy — prior-art sweeps; nothing here claims novelty
├── instrument — the deterministic Lean-variant harness  [STANDING]
│   └── egress — why a remote built-Mathlib env became the runtime (courier, never prover)
├── LINE A — loop residue as a significance signal ................ killed
│   └── A1 → A1b (the redundancy bug) → A2 (faithful graph) → A3 (AMBIGUOUS) → A4 (backfire)
├── LINE B — what importance actually correlates with ............. STANDING POSITIVE
│   └── B1 (AUC 0.814 depth vs 0.522 reuse) → B2 (de-gamed compression REDUCES)
├── LINE C — antisymmetric / order coordinate ..................... dead
│   └── C1 → C2 → C3 (curl 0.076) → C4 (curl 0.0009, the epitaph) / C5 (degree in a hat)
├── LINE D — discrete style / taste modes ......................... continuous smear
├── LINE E — term space: does the substrate render? ............... mostly refuses
│   └── E1 (stop-report) → E2 (infra axis flat) / E3 (COMPASS BLIND) / E4 = probe 16 (CEILING)
│       └── E4bugs — three parser bugs caught BEFORE the run
├── LINE F — is the rfl-locus a native coordinate? ................ PARTIAL
│   └── F1 = probe 17 (D 0.651, S 0.077) → F1disc (five unsmoothed discrepancies)
├── LINE G — growth mechanism: resolvent as driver? ............... precondition UNESTABLISHED
│   └── G1 = 17b (VOID) → G2 = probe 18 (VOID) → G2diag → G3 (successor, not authorised)
├── LINE H — tail dimension / Hankel rank ......................... VOID
│   └── H1 = probe 19 → H2 (estimability ceiling: 9/12 cells were never measurements) / H3
├── notclaimed — what is NOT claimed, everywhere
└── standing — the ledger (converges from B1, B2, methods-result, instrument, C4, E4, F1, G2diag, H2)
```

Plus one `DOC —` node per `RESULTS*.md` in the repository, carrying the document itself.

## Usage

```bash
export FWK=fwk_...                       # or drop the key in ./.fwk (chmod 600, never committed)
python3 tools/flywheel/build_graph.py    # idempotent: skips anything already in node_ids.json
python3 tools/flywheel/sync.py           # build + add a node for any new RESULTS doc
python3 tools/flywheel/sync.py --verify  # read-only liveness check
sh      tools/flywheel/keepalive.sh      # 15-min verify heartbeat for 24h
```

`node_ids.json` maps local keys → Flywheel node ids and is what makes every script idempotent.
Delete it and you get a second, parallel graph — so keep it.

## API notes (learned by probing; the published docs stop at the index page)

- Base URL `https://flywheel.paradigma.inc/api`, OpenAPI at `/api/openapi.json` (title
  *Flywheel Server 0.1.0*), auth `Authorization: Bearer <fwk_...>`.
- **Every mutating call requires an `Idempotency-Key` header** — omitting it returns
  `{"detail":{"type":"invalid_request","message":"Idempotency-Key header is required"}}`.
- `POST /v1/nodes/commit-new` creates a node *with* its parent edges in one call:
  `{local_temp_node_id, parent_ids[], staged_payload{title, content, summary, repo_context}}`.
  `repo_context` requires all six keys explicitly (`additionalProperties: false`), nulls allowed.
- `POST /v1/nodes` only takes a title — use `commit-new` for real content.
- Nodes come back with a human-readable `slug_name` (`polished-hill-9728`) alongside the uuid.
- There is no node-type or edge-type enum in the schema: the graph is untyped parent/child, so all
  typing here is carried in the node text.

**The key is never committed.** It lives in `$FWK` or an ungitted `.fwk`.

## Upkeep

An hourly Routine (`trig_01VWsidNeD83AQFv1muvu1Vw`) fires into the originating session and re-runs
`sync.py`, adding nodes for genuinely new work and staying silent when nothing changed. It does not
start probes, re-run experiments, or open PRs.
