#!/usr/bin/env python3
"""Per-class figures: AUC(depth -> each class) and S per class. Classes never merged."""
import json, re, os, collections, numpy as np, networkx as nx
from sklearn.metrics import roc_auc_score
MLROOT="mathlib4"

G=nx.DiGraph()
for line in open("faithful/decl_deps.jsonl"):
    r=json.loads(line); n=r["name"]; G.add_node(n)
    for d in dict.fromkeys(r.get("type_deps",[])+r.get("value_deps",[])):
        if d!=n: G.add_edge(n,d)
G.remove_edges_from(nx.selfloop_edges(G))
C=nx.condensation(G); mp=C.graph["mapping"]; dc={}
for c in reversed(list(nx.topological_sort(C))):
    s=list(C.successors(c)); dc[c]=(max(dc[x] for x in s)+1) if s else 0
depth={n:dc[mp[n]] for n in G.nodes}

DECL=re.compile(r'^(?P<attrs>(@\[[^\]]*\]\s*)*)(?P<mods>(private\s+|protected\s+|nonrec\s+|noncomputable\s+)*)'
                r'(?P<kw>theorem|lemma)\s+(?P<name>[^\s({\[:⦃]+)')
TOP=re.compile(r'^(@\[|theorem\s|lemma\s|instance\b|def\s|abbrev\s|attribute\b|section\b|end\b|namespace\s|'
               r'variable\b|open\s|/--|/-!|assert_not_exists|private\s|protected\s|noncomputable\b|deriving\b|'
               r'#|example\b|local\b|scoped\b|set_option\b|universe\b)')
STRICT={"rfl","by rfl","Iff.rfl","by exact rfl","HEq.rfl"}
SIMP=re.compile(r'^by\s+simp(\s+only)?\s*(\[[^\]]*\])?\s*$')
def split_proof(b):
    pr={'(':')','{':'}','[':']','⦃':'⦄'}; op=set(pr); cl=set(pr.values()); d=0; j=0
    while j<len(b):
        c=b[j]
        if c in op: d+=1
        elif c in cl: d-=1
        elif d==0 and c==':' and j+1<len(b) and b[j+1]=='=': return b[j+2:]
        j+=1
    return None
rows=[]; per=collections.defaultdict(lambda:[0,0,0])
for dp,_,fs in os.walk(os.path.join(MLROOT,"Mathlib")):
    for fn in fs:
        if not fn.endswith(".lean"): continue
        p=os.path.join(dp,fn); rel=os.path.relpath(p,MLROOT).replace("/",".")[:-5]
        lines=open(p,errors="ignore").read().split("\n"); ns=[]
        anchors=[i for i,l in enumerate(lines) if TOP.match(l)]
        def bend(st):
            for a in anchors:
                if a>st: return a
            return len(lines)
        i=0
        while i<len(lines):
            l=lines[i].strip()
            m=re.match(r'^namespace\s+([^\s]+)\s*$',l)
            if m: ns.append(m.group(1)); i+=1; continue
            if re.match(r'^end\b',l):
                mm=re.match(r'^end\s+([^\s]+)\s*$',l)
                if mm and ns and ns[-1]==mm.group(1): ns.pop()
                i+=1; continue
            md=DECL.match(lines[i])
            if not md: i+=1; continue
            e=bend(i+1); block="\n".join(lines[i:e]); i=e
            m2=DECL.match(block)
            if not m2: continue
            pf=split_proof(block[m2.end():])
            if pf is None: continue
            pf=" ".join(pf.split()).strip(); nm=md.group("name")
            qn=".".join(ns+[nm]) if ns and not nm.startswith("_root_.") else nm.replace("_root_.","")
            cls="strict" if pf in STRICT else ("simp" if SIMP.match(pf) else "substantive")
            rows.append((qn,rel,cls)); per[rel][{"strict":0,"simp":1,"substantive":2}[cls]]+=1

j=[(depth[q],c) for q,_,c in rows if q in depth]
d=np.array([a for a,_ in j],float); cl=[c for _,c in j]
print(f"joined {len(j)} theorems")
for name,y in [("substantive",[1 if c=="substantive" else 0 for c in cl]),
               ("strict rfl", [1 if c=="strict"      else 0 for c in cl]),
               ("by simp",    [1 if c=="simp"        else 0 for c in cl])]:
    print(f"  AUC(depth -> {name:12s}) = {roc_auc_score(y,d):.4f}")
def subject(m):
    p=m.split("."); return ".".join(p[:2]) if len(p)>=2 else m
def S_for(idx):
    big=[m for m in per if sum(per[m])>=20]
    y=np.array([per[m][idx]/sum(per[m]) for m in big]); sub=[subject(m) for m in big]
    gm=collections.defaultdict(list)
    for s,v in zip(sub,y): gm[s].append(v)
    mu={s:np.mean(v) for s,v in gm.items()}
    pred=np.array([mu[s] for s in sub])
    return 1-np.var(y-pred)/np.var(y), len(big)
s0,nb=S_for(0); s1,_=S_for(1)
print(f"  S(strict rfl) = {s0:.4f}   S(by simp) = {s1:.4f}   (n={nb} modules >=20 thms)")
json.dump(dict(S_strict=float(s0), S_simp=float(s1)), open("p17_perclass.json","w"))
