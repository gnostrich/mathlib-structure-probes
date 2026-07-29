#!/usr/bin/env python3
"""Read the candidate public nodes before deciding whether to link into them."""
import json, os, sys, time, uuid, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
API = "https://flywheel.paradigma.inc/api"
KEY = os.environ.get("FWK") or open(os.path.join(HERE, ".fwk")).read().strip()

TARGETS = [
    ("205ba108-d425-42ed-bfc1-336cb7520c25", "Connes Adelic Geometry / Weil Quadratic Form"),
    ("fff0645c-38ac-5e54-8312-c37ae1dcb58e", "Campaign: RH-Adjacent Formalization and Certified Computation"),
    ("3787b01e-adb3-46f7-8165-ee88c424c78b", "Hilbert-Polya Wall / Selberg Analogy / Lee-Yang"),
    ("d436689d-4a4c-5ab8-abb0-7e70047f58dc", "RH via Spectral-Arithmetic Framework"),
    ("c7f57707-c488-4b0c-8047-12b96f27d3ca", "Gabriel's Horn / Spectral RH"),
    ("5b8f08d3-99ec-4b8b-b39c-3913d1576163", "Spectral Compressibility / Prime Error Tower"),
    ("85d34419-bb9b-5bcc-afa9-59b139baf1ec", "Campaign: BSD Elliptic-Curve Evidence and Formalization"),
    ("e3cca24a-c16a-4a42-90a9-b0756b1459fa", "RP^n Cohomology / Arithmetic Hierarchy (Lean 4)"),
]


def get(path):
    for a in range(4):
        req = urllib.request.Request(API + path)
        req.add_header("Authorization", "Bearer " + KEY)
        req.add_header("Idempotency-Key", str(uuid.uuid4()))
        try:
            with urllib.request.urlopen(req, timeout=90) as r:
                return json.loads(r.read())
        except urllib.error.HTTPError as e:
            return {"_http": e.code, "_body": e.read().decode()[:160]}
        except Exception as e:
            if a == 3:
                return {"_http": 0, "_body": str(e)[:100]}
            time.sleep(2 * (a + 1))


for nid, label in TARGETS:
    r = get(f"/v1/nodes/{nid}")
    if "_http" in r:
        print(f"\n### {label}\n    UNREADABLE: HTTP {r['_http']} {r['_body'][:100]}")
        continue
    n = r.get("node", r)
    print(f"\n### {label}")
    print(f"    id={nid}  slug={n.get('slug_name')}  rev={n.get('revision')} "
          f"parents={len(n.get('parent_ids') or [])} children={len(n.get('child_ids') or [])}")
    print(f"    summary: {(n.get('summary') or '')[:300]}")
    body = (n.get("content") or "").replace("\n", " ")
    print(f"    body[:600]: {body[:600]}")
