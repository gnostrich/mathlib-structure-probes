#!/usr/bin/env python3
"""
loop_veto_test.py — decisive decl-level dissociation + significance test.
Pre-registration in docs/03. Reads either:
  - decl_deps.jsonl       (DumpDeps.lean: name,module,kind,type_deps,value_deps)  FAITHFUL
  - decl_ref_graph.jsonl  (decl_dep_extract.py: name,kind,deps)                    APPROX
Runs H1 (dissociation), H2 (loop predicts significance beyond slide, now with a
DEGREE CONFOUND CONTROL), and H3 (incorruptibility: gaming foil + warm/cold floor).

CORRECTED pre-reg reads: WALL if |rho(L,S)|>=0.7 OR R2(L~S)>=0.75 OR H2 fails.
GO if |rho|<=0.4 AND R2<=0.5 AND both cells populated AND H2 clears AND foils ok.

H3 note: the graph-only harness cannot re-run the Lean prover, so H3(a)/(b) are
realised as GRAPH-THEORETIC operationalisations of the pre-reg's two foils, run
directly on the decl graph (see docstrings on each). They are honest structural
proxies, not prover reproofs; a built-env reproof would strengthen H3(b).
"""
import sys, json, collections
import networkx as nx, numpy as np
from scipy.stats import spearmanr, rankdata

# deterministic: fixed seed so foil sampling is reproducible across runs
RNG = np.random.default_rng(20260717)

path = sys.argv[1] if len(sys.argv)>1 else "decl_deps.jsonl"
G=nx.DiGraph(); kind={}
for line in open(path):
    r=json.loads(line); n=r["name"]; kind[n]=r.get("kind","")
    deps=r.get("deps") or (list(dict.fromkeys((r.get("type_deps",[])+r.get("value_deps",[])))))
    G.add_node(n)
    for d in deps:
        if d!=n: G.add_edge(n,d)
G.remove_edges_from(nx.selfloop_edges(G))
# keep only nodes we have kind for (declared Mathlib decls), drop external leaves
core=set(kind);
G2=G.subgraph(core).copy()
nodes=[n for n in G2.nodes() if kind.get(n)]
print(f"nodes={len(nodes)} edges={G2.number_of_edges()}")

indeg=dict(G2.in_degree())                       # times-used (SLIDE & also Y2 proxy)
outdeg=dict(G2.out_degree())                     # uses-count (proof breadth)
UG=G2.to_undirected()
udeg=dict(UG.degree())                           # undirected degree = the driver of triangle count
# depth-from-axioms: longest chain along dependencies (condense SCCs for safety)
Cg=nx.condensation(G2); cdep={}
for c in reversed(list(nx.topological_sort(Cg))):  # successors (deps) first, else every depth collapses to 0
    ds=[cdep[s]+1 for s in Cg.successors(c) if s in cdep]; cdep[c]=max(ds) if ds else 0
mp=Cg.graph['mapping']; depth={n:cdep[mp[n]] for n in nodes}
tri=nx.triangles(UG)                             # LOOP metric; square_clustering was unused (dropped: O(n<k>^2), intractable on full Mathlib)

xi=np.array([indeg[n] for n in nodes],float)
xo=np.array([outdeg[n] for n in nodes],float)
xu=np.array([udeg[n]  for n in nodes],float)     # undirected degree (triangle driver)
xd=np.array([depth[n] for n in nodes],float)
L =np.array([tri[n]  for n in nodes],float)      # LOOP (swap in birth-simplex when available)
# SLIDE composite = proof-size proxy(depth) + degree; keep in-degree separate for Y2 to avoid circularity
S =np.array([depth[n] for n in nodes],float)     # use depth as the non-circular slide axis
Y1=np.array([1.0 if kind[n]=="theorem" else 0.0 for n in nodes])   # human label
Y2=np.log1p(xi)                                                    # in-library citation proxy

def rankres(a, ctrls):
    """residual of rank(a) after regressing on rank(ctrl_1..k) + intercept.
    ctrls: 1-D array (single control) or list/tuple of 1-D arrays (multi-control)."""
    if isinstance(ctrls,(list,tuple)):
        cols=[rankdata(c) for c in ctrls]
    else:
        cols=[rankdata(ctrls)]
    X=np.column_stack(cols+[np.ones(len(a))])
    ra=rankdata(a)
    beta,*_=np.linalg.lstsq(X,ra,rcond=None)
    return ra - X@beta
def partial_spear(a,b,ctrl):
    return spearmanr(rankres(a,ctrl),rankres(b,ctrl)).correlation

print("\n== H1 dissociation ==")
rho=spearmanr(L,S).correlation; rho_deg=spearmanr(L,xi).correlation
print(f"  rho(L, slide=depth)={rho:.3f}   rho(L, in-degree)={rho_deg:.3f}")
X=np.column_stack([S,np.log1p(xi),np.ones_like(S)]); beta,*_=np.linalg.lstsq(X,L,rcond=None)
R2=1-((L-X@beta)**2).sum()/((L-L.mean())**2).sum(); print(f"  R2(L ~ slide+deg)={R2:.3f}")
def terc(a):
    q1,q2=np.quantile(a,[1/3,2/3]); return np.where(a<=q1,0,np.where(a<=q2,1,2))
ct=collections.Counter(zip(terc(S),terc(L)))
print(f"  cells: high-slide/low-loop={ct.get((2,0),0)}  low-slide/high-loop={ct.get((0,2),0)}")

print("\n== H2 loop predicts significance beyond slide (PAYOFF) ==")
for name,Y in [("Y1 thm/lemma",Y1),("Y2 log in-deg",Y2)]:
    pr=partial_spear(L,Y,S)
    print(f"  partial rho(L, {name} | slide)={pr:.3f}")

print("\n== H2b DEGREE CONFOUND CONTROL (task 4) ==")
print("  Concern: L (triangles) and Y2 (in-degree) both grow with node degree; the")
print("  baseline partial controls depth only. Below we add degree controls. Note")
print("  Y2==log(in-degree), so controlling Y2 for IN-degree is near-circular and is")
print("  reported only as a floor; the honest test is the OUT-degree / undirected-")
print("  degree control (degree the triangle count depends on, not identical to Y2).")
logi, logo, logu = np.log1p(xi), np.log1p(xo), np.log1p(xu)
controls = [
    ("depth only (baseline)",              [S]),
    ("depth + log out-degree",             [S, logo]),          # clean: out-deg independent of Y2
    ("depth + log undirected-degree",      [S, logu]),          # aggressive: triangle driver
    ("depth + log out + log undirected",   [S, logo, logu]),
    ("depth + log in-degree (near-circular floor)", [S, logi]), # collapses by construction
]
for name,Y in [("Y1 thm/lemma",Y1),("Y2 log in-deg",Y2)]:
    print(f"  -- {name} --")
    for cname,cset in controls:
        pr=partial_spear(L,Y,cset)
        print(f"     partial rho(L,Y | {cname}) = {pr:.3f}")
# residualisation cross-check (regress L and Y2 on {depth,log-undirected-deg}, correlate residuals)
rc=[S,logu]
resL=rankres(L,rc); resY=rankres(Y2,rc)
H2_base = partial_spear(L,Y2,[S])                 # baseline (depth-only) payoff
H2_degctl = partial_spear(L,Y2,[S,logu])          # HONEST degree-controlled payoff (triangle driver)
print(f"  residual-corr method  rho(res L, res Y2 | depth,log-udeg) = {spearmanr(resL,resY).correlation:.3f}")
print(f"  >>> H2 read: baseline={H2_base:.3f} -> degree-controlled={H2_degctl:.3f} "
      f"({'SURVIVES' if H2_degctl>=0.1 else 'COLLAPSES'} the degree control)")

print("\n== H3(a) gaming foil: cheap cross-region conjunctions (task 5) ==")
# Pre-reg: inject trivial A∧B decls for DISTANT A,B; the loop meter must NOT credit
# them, and must not let them inflate real nodes' loop credit (Schur-MASA trap).
# Graph operationalisation: a conjunction node C_AB is introduced with two out-edges
# C->A, C->B (it "uses" A and B). In the undirected complex, C participates in a
# triangle iff A~B. For DISTANT (non-adjacent, no common neighbour) A,B, C gets 0
# triangles AND adds no triangle to any existing node -> zero loop credit, provably.
adj = {n:set(UG.neighbors(n)) for n in UG.nodes()}
node_list = nodes
K = min(3000, len(node_list)//2)
def sample_distant_pairs(k):
    pairs=[]; tries=0
    idx = RNG.integers(0, len(node_list), size=(k*8, 2))
    for a_i,b_i in idx:
        if len(pairs)>=k: break
        a,b = node_list[a_i], node_list[b_i]
        if a==b: continue
        if b in adj[a]: continue                      # must be non-adjacent (distance>=2)
        if adj[a] & adj[b]: continue                  # and no common neighbour (distance>=3): truly distant
        pairs.append((a,b))
    return pairs
foils = sample_distant_pairs(K)
# empirical check: inject foils, recompute triangles on foil nodes + a sample of endpoints
Gf = UG.copy()
foil_names=[]
endpoints=set()
for i,(a,b) in enumerate(foils):
    c=f"__FOIL_{i}"; foil_names.append(c)
    Gf.add_edge(c,a); Gf.add_edge(c,b); endpoints.add(a); endpoints.add(b)
tri_foil = nx.triangles(Gf, foil_names)
credited = sum(1 for c in foil_names if tri_foil[c]>0)
print(f"  injected {len(foils)} distant A∧B conjunction foils")
print(f"  foils receiving ANY loop credit (triangles>0): {credited}/{len(foils)} "
      f"({100*credited/max(1,len(foils)):.2f}%)")
# incorruptibility of REAL nodes: verify no sampled endpoint gained triangles from foils
ep_sample=list(endpoints)[:2000]
tri_before = nx.triangles(UG, ep_sample)
tri_after  = nx.triangles(Gf, ep_sample)
changed = sum(1 for n in ep_sample if tri_before[n]!=tri_after[n])
print(f"  real endpoints whose loop credit CHANGED after foil injection: {changed}/{len(ep_sample)}")
real_median = float(np.median(L[L>0])) if (L>0).any() else 0.0
print(f"  (context: median triangle count of real loop-bearing decls = {real_median:.0f}; "
      f"foils sit at the floor 0)")
foil_ok = credited==0 and changed==0
print(f"  H3(a) verdict: foils {'NOT credited and real credit unchanged -> PASS' if foil_ok else 'CREDITED -> FAIL'}")

print("\n== H3(b) warm/cold floor: reuse-shortcut minimisation (task 5) ==")
# Pre-reg: only the loop residue that survives MINIMAL INDEPENDENT REPROOF (L_cold)
# gets veto authority; L_warm - L_cold = path debt (loops that exist only because a
# proof reused an already-available lemma path). A faithful warm/cold split needs
# the PROVER (reprove a sample minimally); the pre-reg says so explicitly. Here we
# give the best PROVER-FREE structural proxy and are explicit about its limit.
#
# Naive proxy (strip every 2-hop-redundant edge u->v with any w: u->w->v) is
# DEGENERATE: a directed triangle a->b->c, a->c has its closing edge a->c redundant
# via b BY DEFINITION, so it removes the closing edge of *every* triangle and drives
# L_cold->0 mechanically. That is an artefact, not a floor. We therefore require an
# edge to be redundant via >=REDUNDANCY_MIN DISTINCT intermediates before calling it
# a reuse shortcut: a bare/essential triangle has exactly ONE intermediate per edge
# and SURVIVES; only edges whose target is reachable by several independent 2-paths
# (genuinely reused shortcuts) are stripped. path-debt = triangles that depend on
# such a multiply-redundant edge.
# (Bounded: ultra-high-out-degree sources are kept warm and reported, so cold
#  survival is never silently under-counted.)
succ = {n:set(G2.successors(n)) for n in G2.nodes()}
OUTCAP=400
for REDUNDANCY_MIN in (2,3):
    redundant=0; scanned_src=0; skipped_src=0
    cold_dir = nx.DiGraph(); cold_dir.add_nodes_from(G2.nodes())
    for u in G2.nodes():
        su=succ[u]
        if len(su)>OUTCAP:                  # ultra-hub source: keep all its edges (warm), report
            skipped_src+=1
            for v in su: cold_dir.add_edge(u,v)
            continue
        scanned_src+=1
        cnt=collections.Counter()           # #distinct intermediates w with u->w->v, per target v
        for w in su:
            for x in succ[w]:
                cnt[x]+=1
        for v in su:
            if v!=u and cnt.get(v,0)>=REDUNDANCY_MIN:   # target reachable via >=MIN independent 2-paths
                redundant+=1
            else:
                cold_dir.add_edge(u,v)
    UGc=cold_dir.to_undirected()
    tri_cold=nx.triangles(UGc)
    Lc=np.array([tri_cold.get(n,0) for n in nodes],float)
    cudeg=dict(UGc.degree()); logcu=np.log1p(np.array([cudeg.get(n,0) for n in nodes],float))
    warm_sum=L.sum(); cold_sum=Lc.sum()
    print(f"  [REDUNDANCY_MIN={REDUNDANCY_MIN}] edges: warm={G2.number_of_edges()} "
          f"stripped as reuse shortcuts={redundant} (scanned={scanned_src}, ultra-hub kept={skipped_src})")
    print(f"     triangle mass: warm={warm_sum:.0f}  cold(L_cold)={cold_sum:.0f}  "
          f"survival={100*cold_sum/max(1,warm_sum):.1f}%")
    print(f"     node-level Spearman(L_warm, L_cold) = {spearmanr(L,Lc).correlation:.3f}   "
          f"decls carrying path-debt = {100*((L-Lc)>0).mean():.1f}%")
    # The veto uses L_cold ONLY: re-run the H2 payoff with the cold metric + degree control.
    # The HONEST degree control for L_cold is the COLD undirected degree (its own driver),
    # not the warm one; report both so the confound cannot hide.
    for cname,cset in [("depth",[S]), ("depth+log WARM-udeg",[S,logu]), ("depth+log COLD-udeg",[S,logcu])]:
        pr=partial_spear(Lc,Y2,cset)
        if cname.endswith("COLD-udeg"): h3b_cold_last=pr; h3b_min_last=REDUNDANCY_MIN   # own-degree-controlled residue
        print(f"     partial rho(L_cold, Y2 | {cname}) = {pr:.3f}")
print("  NOTE: even this refined split is a static proxy; a built-env minimal reproof")
print("  (per pre-reg) is required to certify L_cold as the true incorruptible residue.")

print("\n== VERDICT (H1 precondition + H2 payoff/confound + H3 foils) ==")
wall = abs(rho)>=0.7 or R2>=0.75
go_pre = abs(rho)<=0.4 and R2<=0.5 and ct.get((2,0),0)>0 and ct.get((0,2),0)>0
h2_clears = H2_degctl>=0.1
print(f"  H1: {'WALL' if wall else ('GO-precondition' if go_pre else 'AMBIGUOUS')}")
print(f"  H2: baseline {H2_base:.3f} -> degree-controlled {H2_degctl:.3f}  =>  "
      f"{'CLEARS' if h2_clears else 'DOES NOT CLEAR (payoff was largely a degree artefact)'}")
print(f"  H3(a): {'PASS' if foil_ok else 'FAIL'} (distant A/∧B foils not credited & real credit unchanged)")
# H3(b) read is DATA-DRIVEN: the reuse-stripped, own-degree-controlled cold residue.
_h3b_c = h3b_cold_last if 'h3b_cold_last' in dir() else float('nan')
_h3b_word = ("clears (>=0.20)" if _h3b_c>=0.20 else
             ("weak-positive (0.10-0.20)" if _h3b_c>=0.10 else "collapses (<0.10)"))
print(f"  H3(b): incorruptible L_cold residue (REDUNDANCY_MIN={h3b_min_last if 'h3b_min_last' in dir() else '?'}), "
      f"own-(cold)-degree-controlled partial rho(L_cold,Y2) = {_h3b_c:.3f} -> {_h3b_word}")
print(f"         (static reuse-shortcut proxy; a built-env minimal reproof is still needed to certify it)")
overall = ("GO" if (go_pre and h2_clears and foil_ok) else
           ("WALL" if wall else "AMBIGUOUS -> DO NOT WIRE"))
print(f"  OVERALL (this substrate): {overall}")
print("  NOTE: this is the APPROX (statement-reference) graph unless you passed a faithful")
print("  decl_deps.jsonl. A faithful (proof-edge) graph needs a built Lean env; see HANDOFF.")
