import Mathlib

open scoped BigOperators Matrix

namespace B4

/-!
# B4. Finite-dimensional atomicity of the resolvent

For a real symmetric matrix `A` and vector `v`, the resolvent form
`vᵀ (zI - A)⁻¹ v` is a sum of simple poles `Σ w_i / (z - λ_i)` with `w_i ≥ 0`,
for every `z` that is not an eigenvalue of `A`.
-/

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)

theorem B4_resolvent (hA : A.IsHermitian) :
    ∃ (l w : Fin n → ℝ), (∀ i, 0 ≤ w i) ∧
      ∀ z : ℝ, (z • (1 : Matrix (Fin n) (Fin n) ℝ) - A).det ≠ 0 →
        v ⬝ᵥ ((z • (1 : Matrix (Fin n) (Fin n) ℝ) - A)⁻¹ *ᵥ v)
          = ∑ i, w i / (z - l i) := by
  -- By the spectral theorem, there exists an orthogonal matrix $U$ such that $A = UDU^T$, where $D$ is diagonal.
  obtain ⟨U, D, hU⟩ : ∃ U : Matrix (Fin n) (Fin n) ℝ, ∃ D : Fin n → ℝ, U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ A = U * Matrix.diagonal D * Uᵀ := by
    have := Matrix.IsHermitian.spectral_theorem hA;
    refine' ⟨ hA.eigenvectorUnitary, fun i => hA.eigenvalues i, _, _, _ ⟩;
    · convert hA.eigenvectorUnitary.2.2 using 1;
    · convert hA.eigenvectorUnitary.2.1 using 1;
    · convert this using 1;
  -- For $z$ that is not an eigenvalue of $A$, we have $(z • 1 - A)⁻¹ = U (diagonal (fun i => (z - D i)⁻¹)) Uᵀ$.
  have h_inv : ∀ z : ℝ, (∀ i, z ≠ D i) → (z • 1 - A)⁻¹ = U * Matrix.diagonal (fun i => (z - D i)⁻¹) * Uᵀ := by
    intro z hz
    have h_inv : (z • 1 - A) = U * Matrix.diagonal (fun i => z - D i) * Uᵀ := by
      rw [ show ( Matrix.diagonal fun i => z - D i ) = z • 1 - Matrix.diagonal D by ext i j; by_cases hi : i = j <;> simp +decide [ hi ] ] ; simp +decide [ mul_sub, sub_mul, hU ];
    rw [ h_inv, Matrix.inv_eq_right_inv ];
    simp +decide [ ← Matrix.mul_assoc, hU ];
    simp +decide [ Matrix.mul_assoc, hU, sub_ne_zero.mpr ( hz _ ) ];
  -- Let $w_i = (U^T v)_i^2$.
  use D, fun i => (Matrix.mulVec Uᵀ v i)^2;
  refine' ⟨ fun i => sq_nonneg _, fun z hz => _ ⟩;
  convert congr_arg ( fun m => v ⬝ᵥ m *ᵥ v ) ( h_inv z _ ) using 1;
  · simp +decide [ Matrix.mul_assoc, Matrix.mulVec, dotProduct, sq ];
    simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
    simp +decide [ Matrix.diagonal, Finset.sum_div _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  · intro i hi
    have h_det : Matrix.det (z • 1 - A) = Matrix.det (z • 1 - Matrix.diagonal D) := by
      have h_det : Matrix.det (z • 1 - A) = Matrix.det (U * (z • 1 - Matrix.diagonal D) * Uᵀ) := by
        simp +decide [ *, mul_sub, sub_mul, mul_assoc ];
      simp_all +decide [ Matrix.det_mul ];
      have := congr_arg Matrix.det hU.1; norm_num at this; rw [ mul_right_comm ] ; aesop;
    simp_all +decide [ Matrix.det_diagonal ];
    exact hz <| Matrix.det_eq_zero_of_column_eq_zero i fun j => by by_cases hj : j = i <;> simp_all +decide [ Matrix.smul_eq_diagonal_mul ] ;

end B4