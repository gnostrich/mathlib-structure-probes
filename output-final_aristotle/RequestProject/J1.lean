import Mathlib
import RequestProject.Horizon

open scoped BigOperators Matrix
open Horizon

namespace J1

/-!
# J1. Sharp horizons break positivity; fuzzy horizons preserve it

* (a) The `3 × 3` real symmetric Toeplitz matrix with first row `(1, 1, 0)` is NOT PSD.
* (b) Any autocorrelation Toeplitz matrix `T(j,k) = c_{j−k}` with `c_m = ∑_i x(i)·x(i+m)`
  (finite data `x`) is PSD (it is an adjoint square).
-/

/-- The sharp `3 × 3` box Toeplitz matrix with first row `(1, 1, 0)`. -/
def T110 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 1, 0; 1, 1, 1; 0, 1, 1]

/-
(a) The sharp box fails positive semidefiniteness.
-/
theorem J1_a : ¬ IsPSDq T110 := by
  intro h;
  -- Apply the hypothesis to the vector `x = ![1, -1, 1]`.
  have := h ![1, -1, 1];
  unfold quadForm T110 at this; norm_num [ Fin.sum_univ_succ ] at this;

/-- The autocorrelation sequence `c_m = ∑ᶠ i, x(i)·x(i+m)`. -/
noncomputable def autocorr (x : ℤ → ℝ) (m : ℤ) : ℝ := ∑ᶠ i : ℤ, x i * x (i + m)

/-- The autocorrelation Toeplitz matrix `T(j,k) = c_{j−k}`. -/
noncomputable def autoToeplitz (x : ℤ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k => autocorr x ((j : ℤ) - (k : ℤ))

/-
(b) Every autocorrelation Toeplitz matrix is positive semidefinite.
-/
theorem J1_b (x : ℤ → ℝ) (hx : (Function.support x).Finite) (n : ℕ) :
    IsPSDq (autoToeplitz x n) := by
  -- By definition of IsPSDq, we need to show that for all y : Fin n → ℝ, 0 ≤ ∑ j, ∑ k, y j * (∑ᶠ i, x i * x (i + (j - k))) * y k.
  intro y
  have h_quad_form : ∑ j : Fin n, ∑ k : Fin n, y j * (∑ᶠ i : ℤ, x i * x (i + (j - k))) * y k = ∑ᶠ i : ℤ, (∑ j : Fin n, y j * x (i + j))^2 := by
    -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ j : Fin n, ∑ k : Fin n, y j * (∑ᶠ i : ℤ, x i * x (i + (j - k))) * y k = ∑ᶠ i : ℤ, ∑ j : Fin n, ∑ k : Fin n, y j * x (i + j) * x (i + k) * y k := by
      have h_fubini : ∀ j k : Fin n, ∑ᶠ i : ℤ, x i * x (i + (j - k : ℤ)) = ∑ᶠ i : ℤ, x (i + j) * x (i + k) := by
        intro j k;
        rw [ ← finsum_comp ( Equiv.addRight ( k : ℤ ) ) ] ; norm_num ; congr ; ext ; ring;
        exact Equiv.bijective _;
      have h_fubini : ∑ j : Fin n, ∑ k : Fin n, y j * (∑ᶠ i : ℤ, x (i + j) * x (i + k)) * y k = ∑ᶠ i : ℤ, ∑ j : Fin n, ∑ k : Fin n, y j * x (i + j) * x (i + k) * y k := by
        have h_finite : Set.Finite {i : ℤ | ∃ j k : Fin n, x (i + j) ≠ 0 ∧ x (i + k) ≠ 0} := by
          refine' Set.Finite.subset ( hx.biUnion fun i hi => Set.finite_Icc ( i - n : ℤ ) ( i + n : ℤ ) ) _;
          intro i hi; obtain ⟨ j, k, hj, hk ⟩ := hi; simp_all +decide [ Function.support ] ;
          exact ⟨ i + j, by linarith [ Fin.is_lt j ], hj, by linarith [ Fin.is_lt j ] ⟩
        have h_fubini : ∑ j : Fin n, ∑ k : Fin n, y j * (∑ i ∈ h_finite.toFinset, x (i + j) * x (i + k)) * y k = ∑ i ∈ h_finite.toFinset, ∑ j : Fin n, ∑ k : Fin n, y j * x (i + j) * x (i + k) * y k := by
          simp +decide only [Finset.mul_sum _ _ _, mul_comm, mul_left_comm];
          exact Eq.symm ( by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
        convert h_fubini using 1;
        · refine' Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => _;
          rw [ finsum_eq_sum_of_support_subset ];
          exact fun i hi => h_finite.mem_toFinset.mpr ⟨ j, k, by aesop ⟩;
        · rw [ ← finsum_eq_sum_of_support_subset ];
          intro i hi; contrapose! hi; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_nonneg ] ;
      aesop;
    simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
  convert h_quad_form.ge.trans' ( finsum_nonneg fun i => sq_nonneg _ ) using 1

end J1