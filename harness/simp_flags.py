#!/usr/bin/env python3
"""Extract @[simp] flag per declaration from mathlib4 source.
Uses decl_lines.tsv (qname, relfile, line). A decl is flagged simp if:
 (a) an attribute block within the 3 lines on/above its declaration contains 'simp', OR
 (b) a global `attribute [ ... simp ... ] name1 name2` statement names it.
Writes decl_simp.tsv (qname \t 0/1)."""
import os, re, sys, collections
REPO=sys.argv[1] if len(sys.argv)>1 else "mathlib4"
TSV=sys.argv[2] if len(sys.argv)>2 else "decl_lines.tsv"
OUT=sys.argv[3] if len(sys.argv)>3 else "decl_simp.tsv"

byfile=collections.defaultdict(list)
for row in open(TSV):
    q,rel,ln=row.rstrip("\n").split("\t"); byfile[rel].append((int(ln),q))

ATTR_SIMP=re.compile(r'@\[[^\]]*\bsimp\b[^\]]*\]')
ATTR_STMT=re.compile(r'^\s*attribute\s*\[[^\]]*\bsimp\b[^\]]*\]\s+(.+)$')
simp=set()
for rel,decls in byfile.items():
    p=os.path.join(REPO, rel)
    try: lines=open(p,errors="ignore").read().split("\n")
    except: continue
    # global attribute [simp] statements
    for ln in lines:
        m=ATTR_STMT.match(ln)
        if m:
            for nm in re.findall(r"[A-Za-z_][A-Za-z0-9_\.']*", m.group(1)):
                simp.add(nm)   # short/qualified; matched loosely below
    for ln0,q in decls:
        i=ln0-1
        window="\n".join(lines[max(0,i-3):i+1])
        if ATTR_SIMP.search(window):
            simp.add(q)

# write per-decl flag; also try short-name match for attribute-stmt names
short=collections.defaultdict(list)
allq=[q for ds in byfile.values() for _,q in ds]
for q in allq: short[q.split(".")[-1]].append(q)
resolved=set()
for nm in list(simp):
    if nm in short or "." in nm:  # already qualified-ish
        resolved.add(nm)
    else:
        for q in short.get(nm,[]): resolved.add(q)
simp|=resolved
n=0
with open(OUT,"w") as o:
    seen=set()
    for ds in byfile.values():
        for _,q in ds:
            if q in seen: continue
            seen.add(q)
            o.write(f"{q}\t{1 if q in simp else 0}\n"); n+=1
flagged=sum(1 for ds in byfile.values() for _,q in ds if q in simp)
print(f"wrote {n} rows -> {OUT}; simp-flagged decls (approx) = {len(simp & set(allq))}")
