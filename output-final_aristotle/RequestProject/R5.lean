import Mathlib
import RequestProject.V5_5
import RequestProject.R_A6

open scoped BigOperators Matrix
open Horizon

namespace R5

/-- The endpoint requested in R5, written exactly as the rational `0.69`. -/
noncomputable def b : ℝ := 69 / 100

/-- The chosen endpoint is nonnegative and lies strictly before the first prime. -/
theorem b_pos_lt_log_two : 0 < b ∧ b < Real.log 2 := by
  constructor
  · norm_num [b]
  · exact (by norm_num [b] : b < (0.6931471803 : ℝ)).trans Real.log_two_gt_d9

/-
The Lerch series is continuous on every nonnegative compact interval.
The summands are dominated there by the summable series defining `C`.
-/
theorem continuousOn_L (B : ℝ) :
    ContinuousOn V5_1.L (Set.Icc (0 : ℝ) B) := by
  refine' continuousOn_tsum _ _ _;
  use fun n => 1 / ( n + 1 / 4 ) ^ 2;
  · fun_prop;
  · convert V5_1.summable_C using 1;
  · norm_num +zetaDelta at *;
    exact fun n x hx₁ hx₂ => mul_le_of_le_one_left ( by positivity ) ( Real.exp_le_one_iff.mpr ( by nlinarith ) )

/-
R5-1(a): the archimedean profile is continuous on `[0,0.69]`.
-/
theorem continuousOn_PsiArch :
    ContinuousOn V5_1.PsiArch (Set.Icc (0 : ℝ) b) := by
  refine' ContinuousOn.add ( ContinuousOn.add _ _ ) _;
  · fun_prop;
  · fun_prop;
  · exact ContinuousOn.mul continuousOn_const ( ContinuousOn.sub continuousOn_const ( ContinuousOn.mul ( ContinuousOn.rexp ( continuousOn_id.neg.div_const _ ) ) ( continuousOn_L _ ) ) )

/-- R5-1(a): the normalization at the left endpoint. -/
theorem PsiArch_zero : V5_1.PsiArch 0 = 0 := V5_1.PsiArch_zero

/-
The requested convexity input is false, already on `[0,0.4]`.
The certified values from V5-5 give `PsiArch 0.2 > 0.0543` but
`PsiArch 0.4 < 0.0413`; convexity with value zero at the origin would force
the former to be at most half the latter.
-/
theorem PsiArch_not_convex :
    ¬ ConvexOn ℝ (Set.Icc (0 : ℝ) (2 / 5)) V5_1.PsiArch := by
  norm_num [ ConvexOn ];
  refine' fun h => ⟨ 0, _, _, 2 / 5, _, _, 1 / 2, _, 1 / 2, _, _ ⟩ <;> norm_num;
  rw [ show V5_1.PsiArch 0 = 0 by exact PsiArch_zero ] ; norm_num;
  rw [ show V5_1.PsiArch ( 2 / 5 ) = V5_1.Psi ( 2 / 5 ) by
        rw [ V5_1.Psi_eq_arch ] <;> norm_num;
        exact Real.log_two_gt_d9.trans_le' <| by norm_num, show V5_1.PsiArch ( 1 / 5 ) = V5_1.Psi ( 1 / 5 ) by
                                                                    rw [ V5_1.Psi_eq_arch ] <;> norm_num [ Real.log_two_gt_d9 ];
                                                                    exact Real.log_two_gt_d9.trans_le' <| by norm_num ];
  have := V5_5.psi_grid_bounds; norm_num at * ; linarith

/-
R5-2(a): the advertised two-by-two determinant identity.
-/
theorem two_by_two_det (g : ℝ → ℝ) (s t : ℝ) :
    Matrix.det (!![2 * g s, g s + g t - g (t - s);
                   g s + g t - g (t - s), 2 * g t]) =
      4 * g s * g t - (g s + g t - g (t - s)) ^ 2 := by
  simpa using by ring;

/-
A quantitative two-by-two diagonal-dominance criterion.  This is the
sound sufficient condition requested in R5-2(b), phrased directly as a
Rayleigh floor and therefore avoiding the unnecessary square-root formula.
-/
theorem two_by_two_margin
    (a d c μ : ℝ)
    (ha : μ + |c| ≤ a) (hd : μ + |c| ≤ d) :
    ∀ x : Fin 2 → ℝ,
      μ * ∑ i, x i ^ 2 ≤
        quadForm (!![a, c; c, d]) x := by
  unfold quadForm;
  intro x; norm_num [ Fin.sum_univ_two ] ; cases abs_cases c <;> nlinarith [ sq_nonneg ( x 0 + x 1 ), sq_nonneg ( x 0 - x 1 ) ] ;

/-- The exact hypotheses appearing in the proposed headline coverage theorem.
`adjacentGap` is vacuous for a singleton, as any ordinary minimum-gap condition
must be. -/
def adjacentGap {n : ℕ} (δ : ℝ) (t : Fin n → ℝ) : Prop :=
  ∀ i j, j.val = i.val + 1 → δ ≤ t j - t i

/-- Faithful formalization of the requested all-grid statement at `b = 0.69`.
It deliberately permits the left endpoint `0`, exactly as the prompt does. -/
def CoveragePrimeFree (δ μ : ℝ) : Prop :=
  0 < δ ∧ 0 < μ ∧
  ∀ (n : ℕ) [NeZero n] (t : Fin n → ℝ),
    StrictMono t →
    (∀ i, 0 ≤ t i) →
    (∀ i, t i ≤ b) →
    adjacentGap δ t →
    IsPDq (fun i j => V5_1.G (t i) (t j)) ∧
      μ ≤ lambdaMin (fun i j => V5_1.G (t i) (t j))

/-
A grid consisting only of the allowed point zero has the zero Gram matrix,
so it is not positive definite.
-/
theorem zero_singleton_not_pd :
    ¬ IsPDq (fun _ _ : Fin 1 => V5_1.G 0 0) := by
  unfold IsPDq; norm_num [ V5_1.G ] ;
  refine' ⟨ fun _ => 1, _, _ ⟩ <;> norm_num [ quadForm, V5_1.Psi_zero ];
  exact fun h => by simpa using congr_fun h 0;

/-
R5-3, as requested, is inconsistent: no positive mesh and margin can cover
*every* grid satisfying `0 ≤ t`, because the admissible singleton grid `{0}`
has zero diagonal.  This obstruction is independent of all analytic bounds.
-/
theorem coverage_prime_free :
    ¬ ∃ δ μ : ℝ, CoveragePrimeFree δ μ := by
  rintro ⟨ δ, μ, hδ, hμ, h ⟩;
  contrapose! h;
  refine' ⟨ 1, _, fun _ => 0, _, _, _, _, _ ⟩ <;> norm_num [ StrictMono, adjacentGap ];
  · infer_instance;
  · exact div_nonneg ( by norm_num ) ( by norm_num );
  · exact fun h => False.elim <| zero_singleton_not_pd h

/-
The corresponding R5-4 frontier claim also fails on the allowed singleton
zero grid: a `GramState` necessarily carries a positive-definiteness proof.
-/
theorem frontier_covers :
    ¬ ∃ G : TierR.GramState,
      G.dim = 1 ∧ HEq G.M (fun _ _ : Fin 1 => V5_1.G 0 0) := by
  simp +zetaDelta at *;
  intro G hG hM
  have hPD : IsPDq (fun _ _ : Fin 1 => V5_1.G 0 0) := by
    have := G.hpd;
    grind +qlia
  exact zero_singleton_not_pd hPD

/-- A non-vacuous audited positive result that remains available: the
`(0.2,0.4,0.6)` prime-free grid is built literally by singleton and two
`expand` operations, and its matrix uses `V5_1.G`. -/
theorem audited_frontier_three :
    ∃ G : TierR.GramState, G.dim = 3 ∧ HEq G.M V5_5.M3 :=
  TierR.exists_expanded_true_kernel_state

end R5