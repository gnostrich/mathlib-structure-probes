#!/usr/bin/env python3
"""
Ingest the think-CV claim corpus (nodes.jsonl / edges.jsonl) into Paradigma Flywheel and
connect it to the mathlib-structure-probes layer already there.

Design decisions, all recorded in the node text so the mapping is auditable:

* Flywheel's graph is UNTYPED parent/child. The corpus is typed. Nothing is collapsed:
  `id`, `type`, `tag`, `status` and every `rel` survive verbatim in the node body.
* Asymmetric relations (depends-on, instance-of, occupied-by, closed-by, kills, supersedes,
  measured-by, inherits) become real parent edges, with `to` as the parent of `from`.
* Symmetric relations (same-object-as, rhymes-with, contradicts) are NOT forced into the DAG —
  a parent edge would assert a direction the corpus explicitly does not have. They are recorded
  as cross-references in both nodes' text and listed in the run report.
* Namespaces are NOT merged, per INGEST.md.

Usage:  FWK=... python3 tools/flywheel/ingest_thinkcv.py <dir-with-nodes.jsonl>
"""
import json, os, sys, time, uuid, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
API = "https://flywheel.paradigma.inc/api"
KEY = os.environ.get("FWK") or open(os.path.join(HERE, ".fwk")).read().strip()
SRC = sys.argv[1] if len(sys.argv) > 1 else "."
STATE = f"{HERE}/node_ids.json"
ASYM = {"depends-on", "instance-of", "occupied-by", "closed-by", "kills",
        "supersedes", "measured-by", "inherits"}
SYM = {"same-object-as", "rhymes-with", "contradicts"}

# Cross-layer links. The corpus's INGEST.md expected the existing layer to be a Lean
# DECLARATION graph and therefore proposed exactly one link. The existing layer is in fact a
# CLAIM/reasoning graph over the same programme, so these claim nodes have their actual
# measurement records already present. Each link below is `claim --measured-by--> record`,
# which is asymmetric and safe; nothing is merged.
CROSS = {
    "probe-19-mathlib-tail":     ["root", "H1"],   # root link is the one INGEST.md asks for
    "probe-mathlib-hodge":       ["C3"],
    "probe-mathlib-chain-depth": ["B1"],
    "pa-network-mathlib":        ["occupancy"],
    "f5-port3-empirical":        ["H3"],
    "estimability-ceiling-rule": ["H2"],
    "one-round-policy":          ["method"],
    "epistemic-ledger":          ["method"],
    "horizon-excess-entropy":    ["lineH"],
}


def call(method, path, body=None):
    req = urllib.request.Request(API + path, method=method,
                                 data=json.dumps(body).encode() if body is not None else None)
    req.add_header("Authorization", "Bearer " + KEY)
    req.add_header("Content-Type", "application/json")
    req.add_header("Idempotency-Key", str(uuid.uuid4()))
    for a in range(5):
        try:
            with urllib.request.urlopen(req, timeout=90) as r:
                return json.loads(r.read())
        except urllib.error.HTTPError as e:
            if a == 4:
                return {"detail": f"HTTP {e.code} {e.read().decode()[:160]}"}
            time.sleep(2 ** a)
        except Exception:
            if a == 4:
                raise
            time.sleep(2 ** a)


nodes = {json.loads(l)["id"]: json.loads(l) for l in open(f"{SRC}/nodes.jsonl")}
edges = [json.loads(l) for l in open(f"{SRC}/edges.jsonl")]
state = json.load(open(STATE))

# ---- invariants (INGEST.md's own check) -------------------------------------------------
assert not [e for e in edges if e["from"] not in nodes or e["to"] not in nodes], "dangling ref"
cb = {e["from"] for e in edges if e["rel"] == "closed-by"}
assert not [n for n in nodes.values() if n["status"] == "closed" and n["id"] not in cb]
print(f"invariants OK: {len(nodes)} nodes, {len(edges)} edges")

# ---- parent map from asymmetric edges, with cycle guard ----------------------------------
parents = {k: [] for k in nodes}
out_rel = {k: [] for k in nodes}
sym_refs = {k: [] for k in nodes}
dropped = []
for e in edges:
    out_rel[e["from"]].append((e["rel"], e["to"], e.get("note")))
    if e["rel"] in SYM:
        sym_refs[e["from"]].append((e["rel"], e["to"], e.get("note")))
        sym_refs[e["to"]].append((e["rel"], e["from"], e.get("note")))
    elif e["rel"] in ASYM:
        parents[e["from"]].append(e["to"])
    else:
        dropped.append((e, "unknown rel"))


def creates_cycle(child, parent):
    seen, stack = set(), [parent]
    while stack:
        v = stack.pop()
        if v == child:
            return True
        if v in seen:
            continue
        seen.add(v)
        stack.extend(parents.get(v, []))
    return False


for k in list(parents):
    keep = []
    for p in parents[k]:
        tmp = parents[k]
        parents[k] = [x for x in keep]
        cyc = creates_cycle(k, p)
        parents[k] = tmp
        if cyc:
            dropped.append(({"from": k, "to": p}, "would create a cycle"))
        else:
            keep.append(p)
    parents[k] = keep

order, mark = [], {}


def visit(k):
    if mark.get(k) == 2:
        return
    mark[k] = 1
    for p in parents[k]:
        if mark.get(p) != 2:
            visit(p)
    mark[k] = 2
    order.append(k)


for k in nodes:
    visit(k)

# ---- render + create ---------------------------------------------------------------------
def body(n):
    o = [f"**Corpus id** `{n['id']}` · **type** `{n['type']}` · **tag** `{n.get('tag')}` · "
         f"**status** `{n.get('status')}` · **date** {n.get('date') or '—'}", "",
         n.get("summary", ""), ""]
    if n.get("detail"):
        o += ["## Detail", n["detail"], ""]
    if n.get("verdict"):
        o += ["## Verdict (terminal — do not reopen)", f"> {n['verdict']}", ""]
    if n.get("falsifier"):
        o += ["## Falsifier", f"> {n['falsifier']}", ""]
    if n.get("not_claimed"):
        o += ["## What is NOT claimed", f"> {n['not_claimed']}", ""]
    if n.get("prior_art"):
        o += ["## Prior art"] + [f"- {x}" for x in n["prior_art"]] + [""]
    if out_rel[n["id"]]:
        o += ["## Typed relations (corpus vocabulary — preserved, not collapsed)"]
        o += [f"- `{r}` → `{t}`" + (f" — {nt}" if nt else "") for r, t, nt in out_rel[n["id"]]]
        o += [""]
    if sym_refs[n["id"]]:
        o += ["## Symmetric cross-references",
              "*Not represented as parent edges: a DAG edge would assert a direction the corpus "
              "explicitly does not have.*"]
        o += [f"- `{r}` ↔ `{t}`" + (f" — {nt}" if nt else "") for r, t, nt in sym_refs[n["id"]]]
        o += [""]
    if n.get("sources"):
        o += ["## Sources"] + [f"- {x}" for x in n["sources"]] + [""]
    if n["id"] in CROSS:
        o += ["## Cross-layer link",
              "This claim's measurement record is already in the mathlib-structure-probes layer "
              "of this graph; the record is attached as a parent (`measured-by`). "
              "The two namespaces are kept separate, per `INGEST.md`.", ""]
    return "\n".join(o)


created = 0
for k in order:
    key = "cv:" + k
    if key in state:
        continue
    n = nodes[k]
    pids = [state["cv:" + p] for p in parents[k] if "cv:" + p in state]
    pids += [state[x] for x in CROSS.get(k, []) if x in state]
    r = call("POST", "/v1/nodes/commit-new", {
        "local_temp_node_id": "cv-" + k,
        "parent_ids": pids,
        "staged_payload": {
            "title": f"[{n['type']}] {n['title']}",
            "content": body(n),
            "summary": (n.get("summary") or n["title"])[:280],
            "repo_context": {"repo_url": "https://github.com/gnostrich/mathlib-structure-probes",
                             "branch_name": "claude/flywheel-mirror", "head_commit_sha": None,
                             "origin_host": "github.com", "updated_by": "thinkcv-ingest",
                             "external_transcript_ref": None}}})
    state[key] = r["node"]["node_id"]
    json.dump(state, open(STATE, "w"), indent=1)
    created += 1
    print(f"  + {k:34s} {r['node']['slug_name']:24s} parents={len(pids)}")


# ---- reconcile: parent edges + refreshed bodies for nodes created by an earlier corpus ----
def node_get(nid):
    return call("GET", f"/v1/nodes/{nid}")


added_edges = refreshed = failed = 0
for k in order:
    key = "cv:" + k
    if key not in state:
        continue
    cur = node_get(state[key])
    nd = cur.get("node", cur)
    want = [state["cv:" + p] for p in parents[k] if "cv:" + p in state]
    want += [state[x] for x in CROSS.get(k, []) if x in state]
    have = set(nd.get("parent_ids") or [])
    for pid in want:
        if pid in have:
            continue
        pr = node_get(pid)
        prn = pr.get("node", pr)
        r = call("POST", f"/v1/nodes/{state[key]}/parents/add",
                 {"parent_id": pid, "expected_revision": nd.get("revision", 0),
                  "expected_parent_revision": prn.get("revision", 0),
                  "updated_by": "thinkcv-ingest"})
        if isinstance(r, dict) and r.get("detail"):
            failed += 1
            continue
        added_edges += 1
        nd = node_get(state[key]).get("node", {})
    # refresh body so a superseding corpus's richer text and relations win
    try:
        rev = node_get(state[key]).get("node", {}).get("revision", 0)
        sess = str(uuid.uuid4())
        call("POST", f"/v1/nodes/{state[key]}/stage/lease/acquire",
             {"stage_session_id": sess, "base_committed_revision": rev})
        n = nodes[k]
        r = call("POST", f"/v1/nodes/{state[key]}/commit",
                 {"stage_session_id": sess, "base_committed_revision": rev,
                  "staged_payload": {"title": f"[{n['type']}] {n['title']}", "content": body(n),
                                     "summary": (n.get("summary") or n["title"])[:280],
                                     "repo_context": {"repo_url": "https://github.com/gnostrich/mathlib-structure-probes",
                                                      "branch_name": "claude/flywheel-mirror",
                                                      "head_commit_sha": None, "origin_host": "github.com",
                                                      "updated_by": "thinkcv-ingest",
                                                      "external_transcript_ref": None}}})
        if not (isinstance(r, dict) and r.get("detail")):
            refreshed += 1
    except Exception:
        pass

print(f"\ncreated {created} claim nodes; +{added_edges} parent edges on existing nodes; "
      f"{refreshed} bodies refreshed; {failed} edge adds refused")
print(f"symmetric cross-refs recorded as text: "
      f"{sum(1 for e in edges if e['rel'] in SYM)} edges")
if dropped:
    print("DROPPED edges (reported, not silently discarded):")
    for e, why in dropped:
        print(f"  {e.get('from')} -> {e.get('to')}  [{why}]")
print(f"cross-layer links: {sum(len(v) for v in CROSS.values())} across {len(CROSS)} claim nodes")
