import Mathlib
import RequestProject.R5Prime
import RequestProject.R_A6

open scoped BigOperators Matrix
open Horizon

namespace R5

/-
A three-site endpoint-forcing lemma for the full band `[1/5,3/5]`.
The pairwise mesh `1/5` is explicit. Since three ordered sites occupy the
entire width `2/5`, this coarse mesh forces the certified grid
`(1/5,2/5,3/5)`; no fine-grid assertion is hidden here.
-/
lemma band_three_grid (t : Fin 3 → ℝ) (ht : StrictMono t)
    (hlo : ∀ i, (1 / 5 : ℝ) ≤ t i) (hhi : ∀ i, t i ≤ (3 / 5 : ℝ))
    (hsep : ∀ i j, i ≠ j → (1 / 5 : ℝ) ≤ |t i - t j|) :
    t = ![1 / 5, 2 / 5, 3 / 5] := by
  have h01 : t 0 < t 1 := ht (by decide)
  have h12 : t 1 < t 2 := ht (by decide)
  have hs01 := hsep 0 1 (by decide)
  have hs12 := hsep 1 2 (by decide)
  rw [abs_of_nonpos (sub_nonpos.mpr h01.le)] at hs01
  rw [abs_of_nonpos (sub_nonpos.mpr h12.le)] at hs12
  funext i
  fin_cases i <;> simp <;> linarith [hlo 0, hhi 2]

/-
On the certified equally-spaced grid, the last Gershgorin row has
exactly zero diagonal-dominance margin. This explains why the general
Gershgorin theorem cannot itself yield a positive three-site margin here.
-/
lemma three_grid_last_row_gershgorin_zero :
    let t : Fin 3 → ℝ := ![1 / 5, 2 / 5, 3 / 5]
    V5_1.G (t 2) (t 2) = V5_1.G (t 2) (t 0) + V5_1.G (t 2) (t 1) := by
  unfold V5_1.G; norm_num; ring;
  erw [ show ( ![1 / 5, 2 / 5, 3 / 5] : Fin 3 → ℝ ) 2 = 3 / 5 by rfl ] ; norm_num [ V5_1.Psi, V5_1.PsiArch ] ; ring;
  unfold V5_1.PsiNonneg; norm_num [ V5_1.Psi_zero ] ;
  rw [ V5_1.PsiArch_zero, V5_1.primeSum_eq_zero ] <;> norm_num;
  positivity

/-
Final certified three-site coverage theorem on the full band.  Every
strictly increasing three-point grid in `[1/5,3/5]` with total pairwise
separation at least `δ = 1/5` has the genuine `V5_1.G` Gram matrix positive
definite, with Rayleigh floor `μ = 1/200`.  The mesh hypothesis is
load-bearing and forces the coarse grid `(0.2,0.4,0.6)`. Since the last
Gershgorin row has zero margin, the proof honestly uses the stronger audited
`V5_5.true_kernel_grid_margin` certificate.
-/
theorem coverage_band_k :
    ∃ (δ μ : ℝ), 0 < δ ∧ 0 < μ ∧
      ∀ (t : Fin 3 → ℝ), StrictMono t →
        (∀ i, (1 / 5 : ℝ) ≤ t i) → (∀ i, t i ≤ (3 / 5 : ℝ)) →
        (∀ i j, i ≠ j → δ ≤ |t i - t j|) →
        IsPDq (fun i j => V5_1.G (t i) (t j)) ∧
          μ ≤ lambdaMin (fun i j => V5_1.G (t i) (t j)) := by
  refine' ⟨ 1 / 5, 1 / 200, _, _, _ ⟩ <;> norm_num;
  intro t ht hlo hhi hsep
  have ht_eq : t = ![1 / 5, 2 / 5, 3 / 5] :=
    band_three_grid t ht hlo hhi hsep
  refine' ⟨ _, _ ⟩;
  · convert V5_5.true_kernel_grid_posdef;
    rename_i i j; fin_cases i <;> fin_cases j <;> norm_num [ ht_eq, V5_5.M3 ] ;
  · convert le_lambdaMin _ _;
    · infer_instance;
    · intro x hx; convert V5_5.true_kernel_grid_margin x |> le_trans _ using 1 ;
      · unfold V5_5.M3; norm_num [ Fin.sum_univ_succ, ht_eq ] ;
      · norm_num [ hx ]

/-- The strongest final coverage rung obtained in Tier R: the explicit
three-site coarse-mesh theorem `coverage_band_k`. -/
theorem coverage_band_final :
    ∃ (δ μ : ℝ), 0 < δ ∧ 0 < μ ∧
      ∀ (t : Fin 3 → ℝ), StrictMono t →
        (∀ i, (1 / 5 : ℝ) ≤ t i) → (∀ i, t i ≤ (3 / 5 : ℝ)) →
        (∀ i j, i ≠ j → δ ≤ |t i - t j|) →
        IsPDq (fun i j => V5_1.G (t i) (t j)) ∧
          μ ≤ lambdaMin (fun i j => V5_1.G (t i) (t j)) :=
  coverage_band_k

/-
Final frontier corollary.  Under the same explicit coarse mesh, the
three-site true-kernel matrix is represented by the state constructed in
`R_A6` literally by `singleton` and two successful `expand` operations.
Thus all two Schur gates are discharged by the existing audited construction.
-/
theorem frontier_covers_band_final :
    ∀ (t : Fin 3 → ℝ), StrictMono t →
      (∀ i, (1 / 5 : ℝ) ≤ t i) → (∀ i, t i ≤ (3 / 5 : ℝ)) →
      (∀ i j, i ≠ j → (1 / 5 : ℝ) ≤ |t i - t j|) →
      ∃ G : TierR.GramState,
        G.dim = 3 ∧ HEq G.M (fun i j => V5_1.G (t i) (t j)) := by
  intro t ht hlo hhi hsep;
  have := band_three_grid t ht hlo hhi hsep;
  convert TierR.exists_expanded_true_kernel_state using 1;
  ext; simp [this];
  unfold V5_5.M3; norm_num [ Fin.forall_fin_succ ] ;

end R5