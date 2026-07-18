#!/usr/bin/env python3
"""
V3 walk analysis (PREREG-v3-walk-3batch.md). State tables from logs -> fidelity -> evaluability ->
advised (fixed compass) vs blind (200 seeds) local replay -> locked verdicts per batch + B3 gate.
"""
import json, re, collections, pathlib, random
import numpy as np

BASE=pathlib.Path("/tmp/claude-0/-home-user-Structure-Backprop/a747742e-9a2f-5c79-9f64-ed3bc601f93e/scratchpad")
RES=BASE/"walk_results"
MANS={ "B1": json.load(open(BASE/"walk_manifest_B1.json")),
       "B2": json.load(open(BASE/"walk_manifest_B2.json")) }
ERRLINE=re.compile(r'([A-Za-z0-9_]+)\.lean:(\d+):\d+:\s*error(?:\(|:)\s*(.*)')

def parse_log(path):
    """returns list of (line, kind, trailing-text-block)"""
    out=[]
    lines=open(path,errors="ignore").read().split("\n")
    for i,l in enumerate(lines):
        m=ERRLINE.search(l)
        if m:
            block=[]
            for j in range(i+1, min(i+40,len(lines))):
                if ERRLINE.search(lines[j]) or lines[j].startswith("DONE"): break
                block.append(lines[j])
            out.append((int(m.group(2)), m.group(3), "\n".join(block)))
    return out

def state_table(run, hb):
    """{(batch,goal,mask): (outcome, stucktext)}"""
    tab={}; canfail=[]
    for b,man in MANS.items():
        for g in man["goals"]:
            lp=RES/run/"logs"/("hb"+hb)/(g["file"]+".log")
            if not lp.exists(): continue
            errs=parse_log(lp)
            for e in g["entries"]:
                a,bb=e["lines"]
                if e["role"]=="canary_break":
                    if not any(a<=x<=bb for x,_,_ in errs): canfail.append((g["file"],"C2 no error"))
                    continue
                if e["role"]=="canary_na":
                    if not any(a<=x<=bb for x,_,_ in errs): canfail.append((g["file"],"C3 no error"))
                    continue
                ts,vs=e["twin_start"],e["var_start"]
                twin=[x for x in errs if ts<=x[0]<vs]; var=[x for x in errs if vs<=x[0]<=bb]
                if twin: tab[(b,g["goal"],e["mask"])]=("NA","")
                elif var:
                    stuck="\n".join(k+"\n"+t for _,k,t in var)
                    tab[(b,g["goal"],e["mask"])]=("STUCK",stuck)
                else: tab[(b,g["goal"],e["mask"])]=("CLOSES","")
    return tab, canfail

t0,cf0=state_table("wrun0","200k"); t1,cf1=state_table("wrun1","200k")
t50,_=state_table("wrun0","50k")
common=set(t0)&set(t1); mism=[k for k in common if t0[k][0]!=t1[k][0]]
print(f"fidelity: cells={len(common)} run-mismatch={len(mism)} canary-failures run0={len(cf0)} run1={len(cf1)}")
void = len(mism)>0.02*len(common) or cf0 or cf1
if cf0: print("  canary problems:",cf0[:5])
c50=set(t0)&set(t50); flips=[k for k in c50 if (t0[k][0]=="CLOSES")!=(t50[k][0]=="CLOSES")]
print(f"budget flip-rate: {len(flips)}/{len(c50)} = {len(flips)/max(1,len(c50)):.3f} "
      f"{'PROVER-LEAK FLAG' if len(flips)>0.10*len(c50) else '(ok)'}")
T=t0

OPSYMS={"Field":["⁻¹","/"],"DivisionRing":["⁻¹","/"],"GroupWithZero":["⁻¹","/"],
        "CommGroupWithZero":["⁻¹","/"],"Ring":[" - ","-"],"Monoid":["^"],"Fintype":["Fintype","card"],
        "CommRing":[" - "],"IsDomain":["*"],"Group":["⁻¹"],"CommGroup":["⁻¹"]}
def norm(s): return re.sub(r'\s+',' ',s).strip()

def advise(menu, applied, G):
    best=None
    for bi,mv in enumerate(menu):
        if applied>>bi & 1: continue
        sc=0
        if mv["kind"]=="AddHyp":
            P=norm(mv["P"]); Gn=norm(G)
            if P and P in Gn: sc+=3
            else:
                mneg=re.match(r'(.+?)≠(.+)',P)
                if mneg and norm(mneg.group(1)+"="+mneg.group(2)) in Gn: sc+=3
            hv=re.match(r'([A-Za-z][A-Za-z0-9_₀-₉\'.]*)',P)
            if hv and re.search(r'(?<![A-Za-z0-9_])'+re.escape(hv.group(1))+r'(?![A-Za-z0-9_])',G): sc+=1
        else:
            to=mv["to"]
            if "failed to synthesize" in G or to in G: sc+=3
            for sym in OPSYMS.get(to,[]):
                if sym in G: sc+=2; break
        if sc>mv["cost"]:
            key=(sc-mv["cost"],-mv["cost"],-bi)
            if best is None or key>best[0]: best=(key,bi)
    return best[1] if best else None

def walk_goal(b,g, mode, rng=None):
    menu=g["menu"]; m=len(menu); goal=g["goal"]
    mask=0; steps=0; applied=[]
    for _ in range(6):
        st=T.get((b,goal,mask))
        if st is None: return None
        if st[0]=="CLOSES": break
        if mode=="advised":
            nb=advise(menu,mask,st[1] if st[0]=="STUCK" else "")
            if nb is None: break
            if T.get((b,goal,mask|(1<<nb)),("NA",""))[0]=="NA": break
        else:
            cands=[i for i in range(m) if not mask>>i&1 and T.get((b,goal,mask|(1<<i)),("NA",""))[0]!="NA"]
            if not cands: break
            nb=rng.choice(cands)
        mask|=1<<nb; applied.append(nb); steps+=1
    st=T.get((b,goal,mask))
    closed = st is not None and st[0]=="CLOSES"
    return dict(closed=closed, steps=steps, applied=applied, mask=mask)

report={}
for b,man in MANS.items():
    goals=man["goals"]; ev=[]; k_groups=collections.Counter(); step0=0; hostile=0
    for g in goals:
        e0=T.get((b,g["goal"],0)); ef=T.get((b,g["goal"],g["truth_mask"]))
        if e0 is None or ef is None: continue
        if e0[0]=="CLOSES": step0+=1; continue
        if ef[0]!="CLOSES":
            hostile+=1
            k_groups["synth-fail" if "synthesize" in (ef[1] or "") else
                     ("stmt-NA" if ef[0]=="NA" else "unsolved-goal")]+=1
            continue
        if e0[0]=="NA": hostile+=1; k_groups["stmt-NA-at-empty"]+=1; continue
        ev.append(g)
    n=len(goals); ne=len(ev)
    print(f"\n== {b}: goals={n} evaluable={ne} step0-close={step0} not-repairable/hostile={hostile}")
    print(f"   k-groups (irreducible remainder classes): {dict(k_groups)}")
    if ne<10 or ne<0.5*n:
        report[b]=dict(verdict="DEGENERATE", evaluable=ne, n=n, step0=step0, hostile=hostile,
                       kgroups=dict(k_groups))
        print(f"   VERDICT {b}: DEGENERATE (evaluable {ne}/{n})")
        continue
    adv=[walk_goal(b,g,"advised") for g in ev]
    contain=0; asteps=[]; acost=[]
    for g,w in zip(ev,adv):
        truth={i for i in range(len(g["menu"])) if g["menu"][i]["truth"]}
        if w and w["closed"] and set(w["applied"])<=truth and w["steps"]<=g["n_removed"]+1: contain+=1
        asteps.append(w["steps"] if w and w["closed"] else 6)
        acost.append(sum(g["menu"][i]["cost"] for i in (w["applied"] if w else [])))
    bsteps=[]
    for g in ev:
        ss=[]
        for seed in range(200):
            rng=random.Random(1000+seed)
            w=walk_goal(b,g,"blind",rng)
            ss.append(w["steps"] if w and w["closed"] else 6)
        bsteps.append(np.mean(ss))
    am,bm=np.mean(asteps),np.mean(bsteps)
    margin=bm/max(1e-9,am); cont=contain/ne
    print(f"   advised mean steps={am:.2f}  blind mean steps={bm:.2f}  margin={margin:.2f}x  containment={cont:.2f}")
    print(f"   mean advised cost-paid={np.mean(acost):.2f}")
    if cont>=0.70 and margin>=1.5: v="COMPASS WORKS"
    else: v="COMPASS BLIND"
    report[b]=dict(verdict=v, evaluable=ne, n=n, containment=cont, adv_steps=am, blind_steps=bm,
                   margin=margin, step0=step0, hostile=hostile, kgroups=dict(k_groups))
    print(f"   VERDICT {b}: {v}")

print("\n== STAGE B GATE ==")
gate = any(report[b]["verdict"] in ("COMPASS WORKS","COMPASS BLIND") for b in report)
print("  B3 LAUNCHES" if gate else "  B3 DOES NOT LAUNCH (both A batches DEGENERATE)")
if void: print("  NOTE: FIDELITY VOID FLAG SET — treat all above as void")
json.dump(report, open(BASE/"walk_report_stageA.json","w"), indent=1)
