#!/usr/bin/env python3
"""Set every Flywheel node in node_ids.json to public visibility (view-only for the public)."""
import json, os, sys, time, uuid, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
API = "https://flywheel.paradigma.inc/api"
KEY = os.environ.get("FWK") or open(os.path.join(HERE, ".fwk")).read().strip()
POLICY = {"sharing_mode": "public"}   # server rejects sharing_mode combined with users/link/public fields


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
                return {"error": e.code, "detail": e.read().decode()[:300]}
            time.sleep(2 ** a)
        except Exception:
            if a == 4:
                raise
            time.sleep(2 ** a)


ids = sorted(set(json.load(open(f"{HERE}/node_ids.json")).values()))
print(f"setting {len(ids)} nodes public ...")
ok = bad = 0
for i in range(0, len(ids), 50):
    chunk = ids[i:i + 50]
    r = call("POST", "/v1/nodes/access-policy/bulk", {"node_ids": chunk, "policy": POLICY})
    if isinstance(r, dict) and r.get("error"):
        print(f"  chunk {i//50}: HTTP {r['error']} {r['detail']}")
        bad += len(chunk)
    else:
        ok += len(chunk)
        print(f"  chunk {i//50}: {len(chunk)} nodes -> public")

summ = call("POST", "/v1/nodes/access-policy/summaries", {"node_ids": ids[:50]})
print(f"\n{ok} set, {bad} failed")
print("sample summary:", json.dumps(summ)[:400] if summ else "n/a")
