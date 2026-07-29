#!/usr/bin/env python3
"""
Survey Flywheel's public surface and find nodes our corpus could legitimately attach to.

Read-only. Prints keyword matches with owner + node id so linking is a deliberate second step.
"""
import json, os, re, sys, uuid, urllib.parse, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
API = "https://flywheel.paradigma.inc/api"
KEY = os.environ.get("FWK") or open(os.path.join(HERE, ".fwk")).read().strip()
MINE = set(json.load(open(f"{HERE}/node_ids.json")).values())

TOPICS = {
    "RH / zeta / L-functions": r"riemann|zeta|l-function|l function|weil|explicit formula|"
                               r"critical line|prime gap|primes|de branges|selberg",
    "elliptic curves / modular": r"elliptic curve|modular form|bsd|birch|swinnerton|galois|"
                                 r"iwasawa|abelian variet|arithmetic geometr",
    "operator theory / spectral": r"toeplitz|hankel|szeg|spectral|resolvent|pseudospectr|"
                                  r"operator algebra|von neumann|subfactor|free probab|c\*-",
    "information / entropy": r"excess entropy|tail sigma|causal state|epsilon-machine|"
                             r"kolmogorov|sophistication|prequential|mdl|minimum description",
    "formalisation / Lean": r"\blean\b|mathlib|coq|isabelle|formali[sz]|proof assistant|itp\b",
    "complexity / GCT": r"geometric complexity|gct\b|permanent|determinant|vp\b|vnp\b",
    "sampling / dynamics": r"non-?reversible|langevin|quasipotential|large deviation|"
                           r"metastab|freidlin|wentzell",
}


import time


def get(path):
    for a in range(6):
        req = urllib.request.Request(API + path)
        req.add_header("Authorization", "Bearer " + KEY)
        req.add_header("Idempotency-Key", str(uuid.uuid4()))
        try:
            with urllib.request.urlopen(req, timeout=90) as r:
                return json.loads(r.read())
        except urllib.error.HTTPError as e:
            return {"_http": e.code, "_body": e.read().decode()[:200]}
        except Exception as e:
            if a == 5:
                return {"_http": 0, "_body": str(e)[:120]}
            time.sleep(1.5 * (a + 1))


owners = {o["id"]: o["label"] for o in (get("/v1/graph/facets").get("owners") or [])}

pub, page = [], 1
while True:
    r = get(f"/v1/nodes?page={page}&page_size=50&access_scopes=public")
    if "_http" in r or not r.get("nodes"):
        break
    pub += [n for n in r["nodes"] if n["node_id"] not in MINE]
    if not r.get("has_more"):
        break
    page += 1
    if page > 60:
        break
print(f"public surface: {len(pub)} nodes not owned by this account "
      f"(across {len(owners)} owners)\n")

seen = set()
for topic, pat in TOPICS.items():
    rx = re.compile(pat, re.I)
    hits = [n for n in pub
            if rx.search((n.get("title") or "") + " " + (n.get("summary") or ""))]
    print(f"── {topic}: {len(hits)} matches")
    for n in hits[:25]:
        seen.add(n["node_id"])
        who = owners.get(n.get("owner_id") or n.get("user_id"), "?")
        print(f"   {n['node_id']}  {(n.get('title') or '')[:78]}")
        print(f"      owner={who}  {(n.get('summary') or '')[:110]}")
    print()

json.dump([n for n in pub if n["node_id"] in seen],
          open(f"{HERE}/public_matches.json", "w"), indent=1)
print(f"wrote {len(seen)} candidate nodes -> public_matches.json")
