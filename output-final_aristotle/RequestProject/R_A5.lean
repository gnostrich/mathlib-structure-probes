import Mathlib
import RequestProject.R_A3_A4

open scoped BigOperators Matrix
open Horizon

namespace TierR

variable {n : ℕ}

/-- Number of eigenvalues strictly above a threshold. -/
noncomputable def nPlus (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (τ : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => τ < (show M.IsHermitian from hM).eigenvalues i).card

/-- Number of eigenvalues equal to a threshold. -/
noncomputable def nZero (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (τ : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => (show M.IsHermitian from hM).eigenvalues i = τ).card

/-- Number of eigenvalues strictly below a threshold. -/
noncomputable def nMinus (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (τ : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => (show M.IsHermitian from hM).eigenvalues i < τ).card

/-
R-A5(a): every real eigenvalue lies in exactly one of the three threshold classes.
-/
theorem inertia_count_sum (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (τ : ℝ) :
    nPlus M hM τ + nZero M hM τ + nMinus M hM τ = n := by
  unfold nPlus nZero nMinus;
  rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
  rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ];
  convert Finset.sum_const ( 1 : ℕ );
  · grind;
  · norm_num

/-
R-A5(c): for a symmetric matrix, PD means that the zero-threshold meter has no
negative or zero eigenvalues.
-/
theorem isPDq_iff_nMinus_nZero_eq_zero (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) :
    IsPDq M ↔ nMinus M hM 0 = 0 ∧ nZero M hM 0 = 0 := by
  -- Apply the equivalence between IsPDq and the positive definiteness of M.
  have h_equiv : IsPDq M ↔ M.PosDef := by
    convert D6.isPDq_iff_posDef M hM;
  -- By definition of positive definiteness, M is positive definite if and only if all its eigenvalues are positive.
  have h_pos_def : M.PosDef ↔ ∀ i, 0 < (Matrix.IsHermitian.eigenvalues (show M.IsHermitian from hM) i) := by
                                                                          convert Matrix.IsHermitian.posDef_iff_eigenvalues_pos ( show M.IsHermitian from hM );
  simp_all +decide [ nMinus, nZero ];
  grind +qlia

/-- The PD (zero-negative/zero-null) readout is invariant under an invertible real
congruence.  This is the certifying special case of Sylvester's law used by `GramState`.
The full three-way count for indefinite matrices is not needed by expansion. -/
theorem pd_readout_congruence_iff (M P : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᵀ = M) (hP : IsUnit P) :
    let C := Pᵀ * M * P
    let hC : Cᵀ = C := by simp [C, Matrix.transpose_mul, hM, Matrix.mul_assoc]
    (nMinus C hC 0 = 0 ∧ nZero C hC 0 = 0) ↔
      (nMinus M hM 0 = 0 ∧ nZero M hM 0 = 0) := by
  dsimp
  rw [← isPDq_iff_nMinus_nZero_eq_zero (Pᵀ * M * P)
        (by simp [Matrix.transpose_mul, hM, Matrix.mul_assoc]),
      ← isPDq_iff_nMinus_nZero_eq_zero M hM,
      D6.isPDq_iff_posDef _ (by simp [Matrix.transpose_mul, hM, Matrix.mul_assoc]),
      D6.isPDq_iff_posDef _ hM]
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose, star_trivial] using
    (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := M) hP)

end TierR