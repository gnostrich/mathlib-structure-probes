#!/usr/bin/env python3
"""Map each Mathlib declaration -> (relative file, 1-based line) by parsing source.
Reuses the namespace-tracking + decl-start regex from decl_dep_extract; emits TSV."""
import os, re, sys
ROOT=sys.argv[1] if len(sys.argv)>1 else "mathlib4/Mathlib"
OUT=sys.argv[2] if len(sys.argv)>2 else "decl_lines.tsv"
DECL=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*'
                r'(theorem|lemma|def|instance|abbrev|structure|inductive|class)\s+([A-Za-z_][A-Za-z0-9_\'\.]*)')
NS=re.compile(r'^\s*namespace\s+([A-Za-z_][A-Za-z0-9_\'\.]*)')
ENDN=re.compile(r'^\s*end\s+([A-Za-z_][A-Za-z0-9_\'\.]*)\s*$')
def qualify(ns,name): return ".".join(ns+[name]) if ns else name
files=[]
for dp,_,fs in os.walk(ROOT):
    for f in fs:
        if f.endswith(".lean"): files.append(os.path.join(dp,f))
files.sort()
n=0
with open(OUT,"w") as out:
    for p in files:
        ns=[]
        try: lines=open(p,errors="ignore").read().split("\n")
        except: continue
        rel=os.path.relpath(p, os.path.dirname(ROOT))  # keep Mathlib/... prefix
        for i,ln in enumerate(lines):
            m=NS.match(ln)
            if m: ns.append(m.group(1)); continue
            m=ENDN.match(ln)
            if m and ns and ns[-1]==m.group(1): ns.pop(); continue
            m=DECL.match(ln)
            if m:
                q=qualify(ns,m.group(2))
                out.write(f"{q}\t{rel}\t{i+1}\n"); n+=1
print(f"wrote {n} decl->line rows -> {OUT}")
