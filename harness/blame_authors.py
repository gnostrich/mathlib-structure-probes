#!/usr/bin/env python3
"""Harvest git-blame authorship for every decl line, in parallel.
Reads decl_lines.tsv (qname, relfile, line); blames each file once (--line-porcelain),
maps final-line -> author; writes decl_author.tsv (qname, author)."""
import sys, subprocess, collections, os
from multiprocessing import Pool

REPO=sys.argv[1] if len(sys.argv)>1 else "mathlib4"
TSV=sys.argv[2] if len(sys.argv)>2 else "decl_lines.tsv"
OUT=sys.argv[3] if len(sys.argv)>3 else "decl_author.tsv"

# file -> list of (line, qname)
byfile=collections.defaultdict(list)
for row in open(TSV):
    q,rel,ln=row.rstrip("\n").split("\t"); byfile[rel].append((int(ln),q))

def blame_file(rel):
    try:
        out=subprocess.run(["git","-C",REPO,"blame","--line-porcelain","--",rel],
                           capture_output=True,text=True,timeout=120)
        txt=out.stdout
    except Exception:
        return rel,{}
    line2auth={}; cur_final=None; cur_auth=None
    for L in txt.split("\n"):
        if len(L)>=41 and L[:40].isalnum() and L[40:41]==" ":
            parts=L.split()
            # <sha> <orig> <final> [group]
            if len(parts)>=3 and parts[2].isdigit(): cur_final=int(parts[2])
        elif L.startswith("author "):
            cur_auth=L[7:].strip()
        elif L.startswith("\t"):
            if cur_final is not None and cur_auth is not None:
                line2auth[cur_final]=cur_auth
    # attribute this file's decls
    res={}
    for ln,q in byfile[rel]:
        a=line2auth.get(ln)
        if a is None:  # fallback: nearest earlier line
            for d in range(1,6):
                if ln-d in line2auth: a=line2auth[ln-d]; break
        if a: res[q]=a
    return rel,res

files=list(byfile.keys())
print(f"blaming {len(files)} files ...", flush=True)
decl_auth={}
with Pool(16) as pool:
    for i,(rel,res) in enumerate(pool.imap_unordered(blame_file, files, chunksize=8)):
        decl_auth.update(res)
        if i%500==0: print(f"  {i}/{len(files)} files, {len(decl_auth)} decls attributed", flush=True)
with open(OUT,"w") as o:
    for q,a in decl_auth.items(): o.write(f"{q}\t{a}\n")
ac=collections.Counter(decl_auth.values())
print(f"wrote {len(decl_auth)} decl->author rows -> {OUT}", flush=True)
print("top 15 authors by #decls:", flush=True)
for a,c in ac.most_common(15): print(f"  {c:6d}  {a}", flush=True)
