#!/usr/bin/env python3
"""
Set the sharing mode on every Flywheel node this account owns.

    python3 tools/flywheel/set_visibility.py private
    python3 tools/flywheel/set_visibility.py public

Operates on every node the API lists for this account — not just the ones in node_ids.json —
so nodes written by other sessions are covered too. Reports the before/after visibility tally.
"""
import json, os, sys, time, uuid, urllib.error, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
API = "https://flywheel.paradigma.inc/api"
KEY = os.environ.get("FWK") or open(os.path.join(HERE, ".fwk")).read().strip()
MODE = (sys.argv[1] if len(sys.argv) > 1 else "private").lower()
assert MODE in ("private", "public", "unlisted"), f"bad mode {MODE}"


def call(method, path, body=None):
    for a in range(5):
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
            if a == 4:
                return {"_http": 0, "_body": str(e)[:120]}
            time.sleep(2 * (a + 1))


ids, page = [], 1
while page <= 40:
    r = call("GET", f"/v1/nodes?page={page}&page_size=100")
    if "_http" in r or not r.get("nodes"):
        break
    ids += [n["node_id"] for n in r["nodes"]]
    if not r.get("has_more"):
        break
    page += 1
ids = sorted(set(ids))


def tally(node_ids):
    out = {}
    for i in range(0, len(node_ids), 50):
        s = call("POST", "/v1/nodes/access-policy/summaries", {"node_ids": node_ids[i:i + 50]})
        for x in (s.get("summaries") or []):
            out[x.get("visibility", "?")] = out.get(x.get("visibility", "?"), 0) + 1
    return out


print(f"{len(ids)} nodes owned by this account")
print("before:", tally(ids))

ok = bad = 0
for i in range(0, len(ids), 50):
    chunk = ids[i:i + 50]
    r = call("POST", "/v1/nodes/access-policy/bulk",
             {"node_ids": chunk, "policy": {"sharing_mode": MODE}})
    if isinstance(r, dict) and r.get("_http"):
        print(f"  chunk {i // 50}: HTTP {r['_http']} {r['_body'][:140]}")
        bad += len(chunk)
    else:
        ok += len(chunk)

print(f"set {MODE}: {ok} ok, {bad} failed")
print("after:", tally(ids))
