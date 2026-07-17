#!/usr/bin/env python3
"""
decl_dep_extract.py — NO-BUILD APPROX declaration graph (fallback for DumpDeps.lean).

Builds a declaration REFERENCE graph from Lean source: nodes = declarations
(namespace-qualified), edges = decl -> other-declaration-name appearing in its
statement+body. This is an approximation of the true kernel dependency graph:
it MISSES proof-synthesized edges (simp/omega/typeclass/tactic-invoked lemmas)
and can catch names in comments. Use only when a built env / LeanDojo trace is
unavailable; a NULL result here is confounded by the missing proof edges.

Usage:
  python decl_dep_extract.py [ROOT=mathlib4/Mathlib] [--max-files N] [--out decl_ref_graph.jsonl]
"""
import os, re, sys, json, collections

ROOT = "mathlib4/Mathlib"
MAXF = None
OUT  = "decl_ref_graph.jsonl"
args = sys.argv[1:]
if args and not args[0].startswith("--"): ROOT = args[0]
if "--max-files" in args: MAXF = int(args[args.index("--max-files")+1])
if "--out" in args: OUT = args[args.index("--out")+1]

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*'
                  r'(theorem|lemma|def|instance|abbrev|structure|inductive|class)\s+([A-Za-z_][A-Za-z0-9_\'\.]*)')
NS   = re.compile(r'^\s*namespace\s+([A-Za-z_][A-Za-z0-9_\'\.]*)')
ENDN = re.compile(r'^\s*end\s+([A-Za-z_][A-Za-z0-9_\'\.]*)\s*$')
IDENT= re.compile(r"[A-Za-z_][A-Za-z0-9_\.']*")

def qualify(ns_stack, name):
    return ".".join([p for p in ns_stack] + [name]) if ns_stack else name

# pass 1: collect declarations (qualified name) and their text spans
files=[]
for dp,_,fs in os.walk(ROOT):
    for f in fs:
        if f.endswith(".lean"): files.append(os.path.join(dp,f))
files.sort()
if MAXF: files=files[:MAXF]

decls=[]           # (qname, kind, file, text)
for p in files:
    ns=[]
    try: lines=open(p,errors="ignore").read().split("\n")
    except: continue
    # find decl start line indices
    starts=[]
    for i,ln in enumerate(lines):
        m=NS.match(ln)
        if m: ns.append(m.group(1)); continue
        m=ENDN.match(ln)
        if m and ns and ns[-1]==m.group(1): ns.pop(); continue
        m=DECL.match(ln)
        if m:
            starts.append((i, qualify(ns, m.group(2)), m.group(1)))
    for j,(i,q,k) in enumerate(starts):
        end = starts[j+1][0] if j+1<len(starts) else len(lines)
        decls.append((q,k,p,"\n".join(lines[i:end])))

allnames=set(q for q,_,_,_ in decls)
short2q=collections.defaultdict(list)
for q in allnames:
    short2q[q.split(".")[-1]].append(q)

# pass 2: edges (only unambiguous resolutions to reduce noise)
G=collections.defaultdict(set)
for q,k,p,text in decls:
    toks=set(IDENT.findall(text))
    for t in toks:
        if t in allnames and t!=q:
            G[q].add(t)                       # fully-qualified hit
        else:
            cands=short2q.get(t.split(".")[-1])
            if cands and len(cands)==1 and cands[0]!=q:
                G[q].add(cands[0])            # unique short-name hit

E=sum(len(v) for v in G.values())
with open(OUT,"w") as fh:
    for q,k,p,_ in decls:
        fh.write(json.dumps({"name":q,"kind":k,"deps":sorted(G.get(q,[]))})+"\n")
print(f"decls={len(decls)} edges={E} unique_names={len(allnames)} -> {OUT}")
print("kinds:", collections.Counter(k for _,k,_,_ in decls))
