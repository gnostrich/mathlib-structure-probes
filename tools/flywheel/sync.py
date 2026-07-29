#!/usr/bin/env python3
"""
Ongoing Flywheel sync for mathlib-structure-probes.

Idempotent. On each run:
  1. re-applies fw_build.py's node set (skips anything already in fw_state.json);
  2. scans the repo for RESULTS docs / probe dirs that have no node yet and adds them;
  3. reports graph size.

Run with FWK set.  `--verify` only reports.
"""
import json, os, re, subprocess, sys, time, uuid, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_DIR = os.environ.get("MSP_REPO", "/home/user/Structure-Backprop")
STATE = f"{HERE}/fw_state.json"
LOG = f"{HERE}/fw_sync.log"
API = "https://flywheel.paradigma.inc/api"
KEY = os.environ.get("FWK") or open(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".fwk")).read().strip()


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
        except Exception:
            if a == 4:
                raise
            time.sleep(2 ** a)


def log(msg):
    line = f"{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())} {msg}"
    print(line, flush=True)
    with open(LOG, "a") as f:
        f.write(line + "\n")


def git(*args):
    try:
        return subprocess.run(["git", "-C", REPO_DIR, *args], capture_output=True,
                              text=True, timeout=60).stdout.strip()
    except Exception:
        return ""


state = json.load(open(STATE)) if os.path.exists(STATE) else {}
total = call("GET", "/v1/nodes?page=1&page_size=1")["total"]
log(f"sync start: {len(state)} tracked keys, {total} nodes server-side")

if "--verify" in sys.argv:
    sys.exit(0)

# 1. base graph (idempotent)
os.environ.setdefault("FW_SHA", git("rev-parse", "HEAD"))
subprocess.run([sys.executable, f"{HERE}/fw_build.py"], check=False)
state = json.load(open(STATE))

# 2. any RESULTS doc in the repo without a node
docs = []
for root, _, files in os.walk(REPO_DIR):
    if "/.git" in root or "/archive" in root:
        continue
    for fn in files:
        if fn.startswith("RESULTS") and fn.endswith(".md"):
            docs.append(os.path.relpath(os.path.join(root, fn), REPO_DIR))

added = 0
for rel in sorted(docs):
    key = "doc:" + rel
    if key in state:
        continue
    body = open(os.path.join(REPO_DIR, rel), errors="ignore").read()
    first = next((l.lstrip("# ").strip() for l in body.split("\n") if l.startswith("#")), rel)
    verdict = ""
    m = re.search(r'(VERDICT|Verdict)[^\n]{0,160}', body)
    if m:
        verdict = m.group(0)[:160]
    r = call("POST", "/v1/nodes/commit-new", {
        "local_temp_node_id": "msp-" + re.sub(r'[^a-zA-Z0-9]+', '-', rel),
        "parent_ids": [state["root"]],
        "staged_payload": {
            "title": f"DOC — {rel}",
            "content": f"Repository document `{rel}`.\n\n**{first}**\n\n{verdict}\n\n---\n\n"
                       + body[:12000],
            "summary": (verdict or first)[:200],
            "repo_context": {"repo_url": "https://github.com/gnostrich/mathlib-structure-probes",
                             "branch_name": git("rev-parse", "--abbrev-ref", "HEAD"),
                             "head_commit_sha": git("rev-parse", "HEAD"),
                             "origin_host": "github.com", "updated_by": "flywheel-sync",
                             "external_transcript_ref": None}}})
    state[key] = r["node"]["node_id"]
    json.dump(state, open(STATE, "w"), indent=1)
    added += 1
    log(f"  + doc node {rel} -> {r['node']['slug_name']}")

total = call("GET", "/v1/nodes?page=1&page_size=1")["total"]
log(f"sync done: +{added} doc nodes, {total} nodes total")
