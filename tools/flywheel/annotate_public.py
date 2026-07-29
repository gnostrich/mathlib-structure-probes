#!/usr/bin/env python3
"""
Record the cross-account mapping INSIDE our own nodes.

Why not edges: Flywheel refuses `parents/add` when the parent belongs to another account —
`403 auth_error: "Only users with write access may perform this operation."` Public sharing
grants view, not write, so a cross-account edge is not expressible by a viewer. The mapping is
therefore written into the bodies of the nodes we own, which is the strongest form the platform
permits from this side.

Run after link_public.py has recorded the 403s. Idempotent: skips a node that already carries
the section.
"""
import json, os, time, uuid, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
API = "https://flywheel.paradigma.inc/api"
KEY = os.environ.get("FWK") or open(os.path.join(HERE, ".fwk")).read().strip()
state = json.load(open(f"{HERE}/node_ids.json"))
MARK = "## Related public work on Flywheel"

LINKS = [
    ("pa-connes-program", "205ba108-d425-42ed-bfc1-336cb7520c25", "raspy-pond-4042",
     "Connes Adelic Geometry / Weil Quadratic Form",
     "Their node reports the Weil quadratic form (Connes 2025/2026) with prolate spheroidal wave "
     "functions reaching 55 decimal places for the first zero using primes <= 13. Same programme "
     "this prior-art node names. `occupied-by`."),
    ("horizon-archimedean", "205ba108-d425-42ed-bfc1-336cb7520c25", "raspy-pond-4042",
     "Connes Adelic Geometry / Weil Quadratic Form",
     "The archimedean term in the Weil picture is the same object their adele-class-space node "
     "describes (zeros as eigenvalues of the scaling action). `same-object-as`, different "
     "vocabulary."),
    ("q-weil-horizon-instruments", "3787b01e-adb3-46f7-8165-ee88c424c78b", "bold-wave-8870",
     "Hilbert-Polya Wall / Selberg Analogy / Lee-Yang Mechanism",
     "Their node states the same obstruction this wall records, and adds the Selberg-zeta "
     "solved analogue and the Lee-Yang positivity mechanism. Independent statement of the "
     "occupier."),
    ("horizon-critical-line", "d436689d-4a4c-5ab8-abb0-7e70047f58dc", "shiny-glade-3819",
     "RH via Spectral-Arithmetic Framework",
     "Multi-threaded RH programme (Hellinger embedding with critical line at pi/4, "
     "Nyman-Beurling, H^1 torsion, Lean 4 / Aristotle verification). The critical-line-as-boundary "
     "framing is occupied there."),
    ("proj-lean-certified-positivity", "fff0645c-38ac-5e54-8312-c37ae1dcb58e", "lingering-rice-8808",
     "Campaign: RH-Adjacent Formalization and Certified Computation",
     "Their campaign is exactly this project's category: verified artifacts around RH-equivalent "
     "criteria and bounded certified checks, explicitly *not* claiming a proof. This project is "
     "an instance of it."),
    ("pa-groskin", "fff0645c-38ac-5e54-8312-c37ae1dcb58e", "lingering-rice-8808",
     "Campaign: RH-Adjacent Formalization and Certified Computation",
     "Groskin 2026 truncated-Weil-form numerics and certificates sit inside the same campaign."),
    ("q-monster-direction", "5b8f08d3-99ec-4b8b-b39c-3913d1576163", "divine-firefly-2376",
     "Spectral Compressibility / Prime Error Tower",
     "**Disagreement, recorded as such.** Their node asserts the Golay -> Leech -> Monster -> "
     "V-natural -> j(tau) rigid tower is *one* spectrally compressible object viewed from "
     "different levels. This corpus CLOSED that direction as `structural-rhyme` — same shape, no "
     "method transfer. The link records the conflict, not agreement."),
    ("horizon-excess-entropy", "5b8f08d3-99ec-4b8b-b39c-3913d1576163", "divine-firefly-2376",
     "Spectral Compressibility / Prime Error Tower",
     "Their 'spectral compressibility' and this corpus's excess entropy / tail constant are the "
     "same quantity in different vocabularies; their Weil quadratic form W(f) as conserved charge "
     "across tower levels is the transport this corpus calls `same-object-as`."),
    ("lean-trust-protocol", "c7f57707-c488-4b0c-8047-12b96f27d3ca", "purple-shape-4417",
     "Gabriel's Horn / Spectral RH (Hilbert-Polya Candidate)",
     "Their node carries a `[PROVER CORRECTION]`: Aristotle proved the authors' limit-circle "
     "claim WRONG (the operator is limit-point at both endpoints). That is precisely the failure "
     "mode this trust protocol exists to catch, observed in the wild in someone else's work."),
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


by_child = {}
for cid, pid, slug, title, why in LINKS:
    by_child.setdefault(cid, []).append((pid, slug, title, why))

ok = failed = skipped = 0
for cid, items in by_child.items():
    key = "cv:" + cid
    if key not in state:
        print(f"  ?? {cid} not in graph"); skipped += 1; continue
    r = call("GET", f"/v1/nodes/{state[key]}")
    if "_http" in r:
        print(f"  !! {cid} unreadable"); failed += 1; continue
    n = r.get("node", r)
    content = n.get("content") or ""
    if MARK in content:
        print(f"  == {cid} already annotated"); skipped += 1; continue
    sec = ["", MARK,
           "*Recorded as text, not as graph edges: Flywheel returns "
           "`403 auth_error — only users with write access may perform this operation` when a "
           "node owned by another account is used as a parent. Public sharing grants view, not "
           "write, so a cross-account edge is not expressible from this side.*", ""]
    for pid, slug, title, why in items:
        sec += [f"- **{title}** — `{slug}` (`{pid}`)", f"  {why}", ""]
    rev = n.get("revision", 0)
    sess = str(uuid.uuid4())
    call("POST", f"/v1/nodes/{state[key]}/stage/lease/acquire",
         {"stage_session_id": sess, "base_committed_revision": rev})
    c = call("POST", f"/v1/nodes/{state[key]}/commit",
             {"stage_session_id": sess, "base_committed_revision": rev,
              "staged_payload": {
                  "title": n.get("title") or cid,
                  "content": content + "\n" + "\n".join(sec),
                  "summary": n.get("summary") or cid,
                  "repo_context": {"repo_url": "https://github.com/gnostrich/mathlib-structure-probes",
                                   "branch_name": "claude/flywheel-mirror", "head_commit_sha": None,
                                   "origin_host": "github.com", "updated_by": "cross-account-map",
                                   "external_transcript_ref": None}}})
    if "_http" in c:
        print(f"  XX {cid}: HTTP {c['_http']} {c['_body'][:120]}"); failed += 1
    else:
        print(f"  ++ {cid}: {len(items)} public reference(s) recorded"); ok += 1

print(f"\n{ok} nodes annotated, {skipped} skipped, {failed} failed")
