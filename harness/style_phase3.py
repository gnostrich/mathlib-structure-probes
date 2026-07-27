#!/usr/bin/env python3
"""
Style-mode: rigorous Step A discreteness test + Step C author fingerprints.
Pre-registered reads (fixed):
 A' discreteness (modes vs smear, beyond the SVD gap which only measures dimensionality):
    GMM BIC across k=1..10 (smooth monotone decrease => smear; sharp knee/min => modes) and
    silhouette at the SVD-gap k (>=0.25 well-separated modes; <0.15 => smear).
 C author fingerprints: for top-N prolific authors, (i) do style features predict author
    above the subject-only and majority baselines? (ii) are per-author mode-mixtures STABLE
    across a random split (within-author JS << between-author JS)?  If yes on both => tastes
    are personal & predictive; if author style-pred ~ subject-pred or mixtures unstable => not.
"""
import numpy as np, collections, sys
from sklearn.mixture import GaussianMixture
from sklearn.metrics import silhouette_score
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import cross_val_score
from scipy.spatial.distance import jensenshannon

import os
BASE=os.environ.get("STYLE_BASE",".")
d=np.load(f"{BASE}/style_features.npz", allow_pickle=True)
names=d["names"]; subject=d["subject"]; mode=d["mode"]; feats=list(d["feats"])
k_modes=int(d["k_modes"])
# rebuild standardized feature matrix (same order as saved arrays)
M=np.column_stack([d["loop_residue"], np.log1p(d["proof_size"]), d["depth"],
                   np.log1p(d["in_degree"]), np.log1p(d["out_degree"]), d["classical"]]).astype(float)
Ms=(M-M.mean(0))/(M.std(0)+1e-12)
N=len(names)
rng=np.random.default_rng(0)
samp=rng.choice(N, size=min(40000,N), replace=False)   # subsample for GMM/silhouette speed

print("== STEP A' discreteness (modes vs smear) ==", flush=True)
Xs=Ms[samp]
bics=[]
for k in range(1,11):
    g=GaussianMixture(n_components=k, covariance_type="full", random_state=0, reg_covar=1e-4, max_iter=100)
    g.fit(Xs); bics.append(g.bic(Xs))
bics=np.array(bics)
print("  GMM BIC k=1..10:", " ".join(f"{b:.0f}" for b in bics), flush=True)
dbic=np.diff(bics)
print("  BIC deltas      :", " ".join(f"{x:.0f}" for x in dbic), flush=True)
kbest=int(np.argmin(bics))+1
# knee: does BIC keep dropping (smear) or flatten (real k)?
rel_drop=(bics[:-1]-bics[1:])/np.abs(bics[:-1])
print(f"  BIC argmin k={kbest}; relative drops:", " ".join(f"{r:.3f}" for r in rel_drop), flush=True)
sil=silhouette_score(Xs, GaussianMixture(k_modes,random_state=0,reg_covar=1e-4).fit_predict(Xs))
print(f"  silhouette at k={k_modes}: {sil:.3f}  (>=0.25 separated modes; <0.15 smear)", flush=True)
a_read = "SMEAR (continuous)" if (sil<0.15 or kbest>=9) else ("weak modes" if sil<0.25 else "discrete modes")
print(f"  Step A' read: {a_read}", flush=True)

print("\n== STEP C author fingerprints ==", flush=True)
try:
    da={}
    for row in open(f"{BASE}/decl_author.tsv"):
        q,a=row.rstrip("\n").split("\t"); da[q]=a
except FileNotFoundError:
    print("  decl_author.tsv not ready yet — rerun after blame finishes."); sys.exit(0)
idx={n:i for i,n in enumerate(names)}
# join
auth=np.array([da.get(n,"") for n in names])
have=auth!=""
print(f"  decls with author: {have.sum()}/{N} ({100*have.sum()/N:.1f}%)", flush=True)
cnt=collections.Counter(auth[have])
TOPN=20
top=[a for a,_ in cnt.most_common(TOPN)]
print(f"  top {TOPN} authors (by #decls): "+", ".join(f"{a}({cnt[a]})" for a in top[:8])+" ...", flush=True)
sel=np.isin(auth, top)
Xa=Ms[sel]; ya=auth[sel]; sa=subject[sel]
print(f"  analysing {sel.sum()} decls across {len(top)} authors", flush=True)

# (i) predictability: style features vs subject-only vs majority
from sklearn.preprocessing import LabelEncoder
le=LabelEncoder(); yy=le.fit_transform(ya)
maj=collections.Counter(yy).most_common(1)[0][1]/len(yy)
acc_style=cross_val_score(LogisticRegression(max_iter=400,C=1.0),
                          Xa, yy, cv=3, scoring="accuracy").mean()
# subject-only baseline: one-hot subject as sole predictor
subj_oh=np.zeros((sel.sum(), len(set(sa))))
for i,s in enumerate(sorted(set(sa))): subj_oh[:,i]=(sa==s)
acc_subj=cross_val_score(LogisticRegression(max_iter=400,C=1.0),
                         subj_oh, yy, cv=3, scoring="accuracy").mean()
print(f"  author-prediction accuracy: majority={maj:.3f}  subject-only={acc_subj:.3f}  STYLE={acc_style:.3f}", flush=True)

# (ii) mode-mixture stability: split each author's decls in half, JS divergence within vs between
def mixture(ids):
    m=mode[ids]; v=np.bincount(m, minlength=k_modes).astype(float); return v/max(1,v.sum())
within=[]; mixA={}; mixB={}
allids=np.where(sel)[0]
for a in top:
    ids=allids[ya==a]
    rng.shuffle(ids); h=len(ids)//2
    if h<5: continue
    mA=mixture(ids[:h]); mB=mixture(ids[h:])
    mixA[a]=mA; mixB[a]=mB
    within.append(jensenshannon(mA,mB))
between=[]
au=list(mixA)
for i in range(len(au)):
    for j in range(i+1,len(au)):
        between.append(jensenshannon(mixA[au[i]], mixA[au[j]]))
within=np.array(within); between=np.array(between)
print(f"  mode-mixture JS: within-author(split)={np.nanmean(within):.3f}  between-author={np.nanmean(between):.3f}", flush=True)
sep = np.nanmean(between) > 1.5*np.nanmean(within)
print(f"  separability: between {'>>' if sep else 'NOT >>'} within  ({np.nanmean(between)/max(1e-9,np.nanmean(within)):.2f}x)", flush=True)

print("\n== STEP C read ==", flush=True)
style_beats_subject = acc_style > acc_subj + 0.02
print(f"  style predicts author beyond subject: {style_beats_subject} (style {acc_style:.3f} vs subj {acc_subj:.3f})", flush=True)
print(f"  author mode-fingerprints separable & stable: {sep}", flush=True)
if style_beats_subject and sep:
    print("  => tastes are PERSONAL and predictive (bridge holds)", flush=True)
elif not style_beats_subject:
    print("  => style adds little over subject for placing authors (taste != person, or ~ field)", flush=True)
else:
    print("  => author mixtures not clearly separable (weak personal signal)", flush=True)
