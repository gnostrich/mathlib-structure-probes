#!/usr/bin/env python3
"""
Attach our claim nodes to matching PUBLIC nodes owned by other Flywheel accounts.

Rule applied (conservative, and stated so it can be audited or reversed):
only nodes whose corpus tag is `occupied`, `structural-rhyme`, or which are prior-art /
project records, get a public parent. A public node becomes the PARENT of ours, which is the
honest direction for an `occupied` claim: "this space is already inhabited by that work."
Nothing tagged `candidate-original` or `conjectured` is attached — that would assert a lineage
the corpus does not claim.

Undo: POST /v1/nodes/{child}/parents/remove with the same parent_id.
"""
import json, os, time, uuid, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
API = "https://flywheel.paradigma.inc/api"
KEY = os.environ.get("FWK") or open(os.path.join(HERE, ".fwk")).read().strip()
state = json.load(open(f"{HERE}/node_ids.json"))

LINKS = [
    # (our corpus id, public node id, public title, why)
    ("pa-connes-program", "205ba108-d425-42ed-bfc1-336cb7520c25",
     "Connes Adelic Geometry / Weil Quadratic Form",
     "our prior-art node for the Connes programme; theirs is that programme"),
    ("horizon-archimedean", "205ba108-d425-42ed-bfc1-336cb7520c25",
     "Connes Adelic Geometry / Weil Quadratic Form",
     "the archimedean term in the Weil picture — same object, occupied"),
    ("q-weil-horizon-instruments", "3787b01e-adb3-46f7-8165-ee88c424c78b",
     "Hilbert-Polya Wall / Selberg Analogy / Lee-Yang Mechanism",
     "our registered wall sits inside their statement of the same obstruction"),
    ("horizon-critical-line", "d436689d-4a4c-5ab8-abb0-7e70047f58dc",
     "RH via Spectral-Arithmetic Framework",
     "critical line as the convergence/divergence boundary — occupied by their framework"),
    ("proj-lean-certified-positivity", "fff0645c-38ac-5e54-8312-c37ae1dcb58e",
     "Campaign: RH-Adjacent Formalization and Certified Computation",
     "certified positivity for truncated Weil forms is an instance of that campaign"),
    ("pa-groskin", "fff0645c-38ac-5e54-8312-c37ae1dcb58e",
     "Campaign: RH-Adjacent Formalization and Certified Computation",
     "Groskin 2026 truncated-Weil-form numerics/certificates sit in the same campaign"),
    ("q-monster-direction", "5b8f08d3-99ec-4b8b-b39c-3913d1576163",
     "Spectral Compressibility / Prime Error Tower",
     "they assert the Golay-Leech-Monster tower as one compressible object; we CLOSED that "
     "direction as structural-rhyme — the link records the disagreement, not agreement"),
    ("horizon-excess-entropy", "5b8f08d3-99ec-4b8b-b39c-3913d1576163",
     "Spectral Compressibility / Prime Error Tower",
     "their spectral compressibility and our excess entropy are the same quantity"),
    ("lean-trust-protocol", "c7f57707-c488-4b0c-8047-12b96f27d3ca",
     "Gabriel's Horn / Spectral RH (Hilbert-Polya Candidate)",
     "their node carries a [PROVER CORRECTION] where Aristotle refuted the authors' claim — "
     "the exact failure mode our Lean trust protocol exists to catch"),
]


def call(method, path, body=None):
    for a in range(4):
        req = urllib.request.Request(API + path, method=method,
                                     data=json.dumps(body).encode() if body is not None else None)
        req.add_header("Authorization", "Bearer " + KEY)
        req.add_header("Content-Type", "application/json")
        req.add_header("Idempotency-Key", str(uuid.uuid4()))
        try:
            with urllib.request.urlopen(req, timeout=90) as r:
                return json.loads(r.read())
        except urllib.error.HTTPError as e:
            return {"_http": e.code, "_body": e.read().decode()[:200]}
        except Exception as e:
            if a == 3:
                return {"_http": 0, "_body": str(e)[:120]}
            time.sleep(2 * (a + 1))


ok = skipped = failed = 0
report = []
for cid, pid, ptitle, why in LINKS:
    key = "cv:" + cid
    if key not in state:
        print(f"  ?? {cid}: not in our graph"); skipped += 1; continue
    child = call("GET", f"/v1/nodes/{state[key]}")
    parent = call("GET", f"/v1/nodes/{pid}")
    if "_http" in child or "_http" in parent:
        print(f"  !! {cid}: unreadable ({child.get('_http') or parent.get('_http')})")
        failed += 1
        continue
    cn, pn = child.get("node", child), parent.get("node", parent)
    if pid in (cn.get("parent_ids") or []):
        print(f"  == {cid} -> {ptitle[:40]} (already linked)"); skipped += 1; continue
    r = call("POST", f"/v1/nodes/{state[key]}/parents/add",
             {"parent_id": pid, "expected_revision": cn.get("revision", 0),
              "expected_parent_revision": pn.get("revision", 0), "updated_by": "cross-account-link"})
    if "_http" in r:
        print(f"  XX {cid} -> {ptitle[:40]}: HTTP {r['_http']} {r['_body'][:120]}")
        failed += 1
    else:
        print(f"  ++ {cid} -> {ptitle[:48]}")
        ok += 1
        report.append({"child": cid, "child_node": state[key], "parent_node": pid,
                       "parent_title": ptitle, "why": why})

json.dump(report, open(f"{HERE}/cross_account_links.json", "w"), indent=1)
print(f"\n{ok} linked, {skipped} skipped, {failed} failed -> cross_account_links.json")
