#!/usr/bin/env python3
"""
Probe 19 — build the prerequisite tape (Ports 1-3).  Fixed by PREREG.md.

Row  = one declaration.  String = its depth-realizing prerequisite chain from a primitive to
itself, read in ascending depth order.  Position in the string IS prerequisite depth: along a
depth-realizing path the intrinsic grading falls by exactly 1 per step.

Grading reused from probe 17 (faithful decl DAG over type_deps u value_deps, longest path to
primitives), not redefined.

Emits tape.npz:  T{k}  (20000 x 24 int32, column j = position from the DEEP end, 0 = the
declaration itself, -1 = absent), LEN, plus alphabet metadata in tape_meta.json.
"""
import json, os, re, sys, hashlib, collections
from array import array
import numpy as np

SP     = "/tmp/claude-0/-home-user-Structure-Backprop/a747742e-9a2f-5c79-9f64-ed3bc601f93e/scratchpad"
GRAPH  = f"{SP}/faithful/decl_deps.jsonl"
MLROOT = f"{SP}/mathlib4"
OUT    = f"{SP}/p19"
SEED   = 20260729
NSAMP  = 20000
CAP    = 24
K3_MAX = 2000
KINDS  = {"def", "theorem", "instance", "structure", "abbrev"}

os.makedirs(OUT, exist_ok=True)

# ---------------------------------------------------------------- graph + intrinsic grading
print("loading faithful dependency graph ...", flush=True)
idx, names = {}, []
kind, module = [], []


def nid(s):
    i = idx.get(s)
    if i is None:
        i = len(names); idx[s] = i; names.append(s); kind.append("other"); module.append("")
    return i


rows = []
with open(GRAPH) as f:
    for line in f:
        r = json.loads(line)
        u = nid(r["name"]); kind[u] = r.get("kind", "other"); module[u] = r.get("module", "")
        rows.append((u, r))
for u, r in rows:
    pass
# second pass: adjacency must be indexed by node id, so build a dict then flatten
deps = {}
for u, r in rows:
    d = []
    seen = set()
    for x in r.get("type_deps", []) + r.get("value_deps", []):
        if x != r["name"] and x not in seen:
            seen.add(x); d.append(nid(x))
    deps[u] = d
del rows
n = len(names)
mathlib_ids = np.array(sorted(deps.keys()), dtype=np.int64)
print(f"  nodes={n:,}  declarations with a record={len(deps):,}  "
      f"edges={sum(len(v) for v in deps.values()):,}", flush=True)

# ---- longest path to primitives + the depth-realizing successor (iterative, no recursion)
print("computing intrinsic grading (longest path) ...", flush=True)
depth = np.full(n, -1, dtype=np.int32)
best = np.full(n, -1, dtype=np.int64)
for s in range(n):
    if depth[s] >= 0:
        continue
    stack = [(s, 0)]
    while stack:
        v, state = stack[-1]
        if depth[v] >= 0:
            stack.pop(); continue
        dv = deps.get(v)
        if not dv:
            depth[v] = 0; stack.pop(); continue
        if state == 0:
            stack[-1] = (v, 1)
            for w in dv:
                if depth[w] < 0:
                    stack.append((w, 0))
            continue
        bd, bw = -1, -1
        for w in dv:
            dw = depth[w]
            if dw > bd or (dw == bd and bw >= 0 and names[w] < names[bw]):
                bd, bw = dw, w
        depth[v] = bd + 1; best[v] = bw
        stack.pop()
print(f"  max depth={int(depth.max())}  mean(decls)={depth[mathlib_ids].mean():.1f}", flush=True)

# ---------------------------------------------------------------- Port 3: head type constructor
print("parsing source-text head type constructors (declared surrogate) ...", flush=True)
DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*'
    r'(?P<kw>theorem|lemma|def|abbrev|instance|structure|class|inductive)\b\s*(?P<name>[^\s({\[:⦃]*)')
TOP = re.compile(r'^(@\[|theorem\s|lemma\s|instance\b|def\s|abbrev\s|attribute\b|section\b|end\b|namespace\s|'
                 r'variable\b|open\s|/--|/-!|assert_not_exists|private\s|protected\s|noncomputable\b|deriving\b|'
                 r'#|example\b|local\b|scoped\b|set_option\b|universe\b|structure\s|class\s|inductive\s)')
NOTATION = [("↔", "Iff"), ("≠", "Ne"), ("=", "Eq"), ("≤", "LE.le"), ("<", "LT.lt"), ("≥", "LE.le"),
            (">", "LT.lt"), ("∈", "Membership.mem"), ("⊆", "HasSubset.Subset"), ("∣", "Dvd.dvd"),
            ("∧", "And"), ("∨", "Or"), ("→", "Arrow")]
IDENT = re.compile(r'[A-Za-z_][A-Za-z0-9_.\'!?]*')


def split_sig(body):
    """return (type_text) between the top-level ':' and the top-level ':=' / 'where' / end."""
    pr = {'(': ')', '{': '}', '[': ']', '⦃': '⦄'}
    op, cl = set(pr), set(pr.values())
    d = 0; start = None; j = 0
    while j < len(body):
        c = body[j]
        if c in op: d += 1
        elif c in cl: d -= 1
        elif d == 0 and c == ':':
            if j + 1 < len(body) and body[j + 1] == '=':
                return body[start:j] if start is not None else None
            if start is None: start = j + 1
        j += 1
    return body[start:] if start is not None else None


def head_of(txt):
    t = " ".join(txt.split())
    for _ in range(8):                                   # strip leading binders / quantifiers
        m = re.match(r'^(∀|∃|Π|λ)[^,]*,\s*', t)
        if m: t = t[m.end():]; continue
        m = re.match(r'^[({\[⦃]', t)
        if not m: break
        pr = {'(': ')', '{': '}', '[': ']', '⦃': '⦄'}[t[0]]
        d = 0
        for j, c in enumerate(t):
            if c == t[0]: d += 1
            elif c == pr:
                d -= 1
                if d == 0:
                    nxt = t[j + 1:].lstrip()
                    if nxt.startswith("→"): t = nxt[1:].lstrip()
                    elif nxt.startswith(":"): t = nxt[1:].lstrip()
                    else: t = nxt
                    break
        else:
            break
    d = 0
    for j, c in enumerate(t):                            # top-level notation wins
        if c in "({[⦃": d += 1
        elif c in ")}]⦄": d -= 1
        elif d == 0:
            for sym, nm in NOTATION:
                if t.startswith(sym, j):
                    return nm
    m = IDENT.match(t)
    return m.group(0) if m else "NA"


head = {}
nfiles = 0
for dp, _, fs in os.walk(os.path.join(MLROOT, "Mathlib")):
    for fn in fs:
        if not fn.endswith(".lean"):
            continue
        nfiles += 1
        lines = open(os.path.join(dp, fn), errors="ignore").read().split("\n")
        anchors = [i for i, l in enumerate(lines) if TOP.match(l)]
        ns = []
        i = 0
        while i < len(lines):
            s = lines[i].strip()
            m = re.match(r'^namespace\s+([^\s]+)\s*$', s)
            if m: ns.append(m.group(1)); i += 1; continue
            if re.match(r'^end\b', s):
                mm = re.match(r'^end\s+([^\s]+)\s*$', s)
                if mm and ns and ns[-1] == mm.group(1): ns.pop()
                i += 1; continue
            md = DECL.match(lines[i])
            if not md:
                i += 1; continue
            e = next((a for a in anchors if a > i), len(lines))
            block = "\n".join(lines[i:e]); i = e
            nm = md.group("name")
            if not nm:
                continue
            qn = nm.replace("_root_.", "") if nm.startswith("_root_.") else ".".join(ns + [nm])
            if md.group("kw") in ("structure", "class", "inductive"):
                head[qn] = "Sort"; continue
            ty = split_sig(block[md.end():])
            head[qn] = head_of(ty) if ty else "NA"
print(f"  parsed {nfiles:,} files, {len(head):,} named declarations with a head token", flush=True)

# ---------------------------------------------------------------- symbols per filtration
def root_of(nm):
    p = nm.split(".")
    return p[0] if len(p) >= 2 else "_root_"


def nspath(nm):
    p = nm.split(".")
    return ".".join(p[:-1]) if len(p) >= 2 else "_root_"


sym_k = []
alpha_meta = []
for k in range(4):
    tab = {}
    ids = np.empty(n, dtype=np.int32)
    for v in range(n):
        nm = names[v]
        kd = kind[v] if kind[v] in KINDS else "other"
        if k == 0: key = kd
        elif k == 1: key = (kd, root_of(nm))
        elif k == 2: key = (kd, root_of(nm), head.get(nm, "NA"))
        else: key = (kd, root_of(nm), head.get(nm, "NA"), nspath(nm))
        j = tab.get(key)
        if j is None:
            j = len(tab); tab[key] = j
        ids[v] = j
    A = len(tab)
    hashed = False
    if A > K3_MAX:
        hashed = True                       # deterministic hash of the *key*, applied per node
        keymap = np.empty(A, dtype=np.int32)
        for kk, j in tab.items():
            keymap[j] = int(hashlib.blake2b(repr(kk).encode(), digest_size=8).hexdigest(), 16) % K3_MAX
        ids = keymap[ids]
        A = K3_MAX
    sym_k.append(ids)
    alpha_meta.append(dict(k=k, alphabet=int(A), hashed=bool(hashed), raw_alphabet=int(len(tab))))
    print(f"  k={k}: alphabet={A}{' (hashed from %d)' % len(tab) if hashed else ''}", flush=True)

na_share = float(np.mean([head.get(names[v], "NA") == "NA" for v in mathlib_ids]))
print(f"  k=2 head coverage over sampled population: NA share = {na_share:.3f}", flush=True)

# ---------------------------------------------------------------- sample + chains
rng = np.random.default_rng(SEED)
pick = rng.choice(mathlib_ids, size=NSAMP, replace=False)
T = np.full((4, NSAMP, CAP), -1, dtype=np.int32)
LEN = np.zeros(NSAMP, dtype=np.int32)
for r, v in enumerate(pick):
    chain = []
    u = int(v)
    while u >= 0 and len(chain) < CAP:
        chain.append(u); u = int(best[u])
    LEN[r] = len(chain)
    for k in range(4):
        T[k, r, :len(chain)] = sym_k[k][np.array(chain, dtype=np.int64)]
print(f"  tape: {NSAMP} rows, mean chain length {LEN.mean():.1f}, full-cap rows "
      f"{int((LEN == CAP).sum()):,}", flush=True)

np.savez_compressed(f"{OUT}/tape.npz", T=T, LEN=LEN, pick=pick,
                    depth=depth[pick].astype(np.int32))
json.dump(dict(seed=SEED, n_sample=NSAMP, cap=CAP, alphabets=alpha_meta,
               head_NA_share=na_share, max_depth=int(depth.max()),
               mean_chain=float(LEN.mean()), nodes=n, decls=len(deps)),
          open(f"{OUT}/tape_meta.json", "w"), indent=1)
print("wrote tape.npz / tape_meta.json", flush=True)
