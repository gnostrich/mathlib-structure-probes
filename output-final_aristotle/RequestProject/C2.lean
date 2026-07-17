import Mathlib

open scoped BigOperators Matrix

namespace C2

/-!
# C2. Doob h-transform is stochastic

If `P ≥ 0`, `h > 0`, `λ > 0` and `P h = λ h`, then `Q_{ij} = P_{ij} h_j / (λ h_i)`
is nonnegative with unit row sums.
-/

variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (lam : ℝ)

/-- The h-transform. -/
noncomputable def Q (i j : Fin n) : ℝ := P i j * h j / (lam * h i)

theorem C2_stochastic
    (hP : ∀ i j, 0 ≤ P i j) (hh : ∀ i, 0 < h i) (hlam : 0 < lam)
    (heig : ∀ i, ∑ j, P i j * h j = lam * h i) :
    (∀ i j, 0 ≤ Q P h lam i j) ∧ (∀ i, ∑ j, Q P h lam i j = 1) := by
  unfold Q;
  exact ⟨ fun i j => div_nonneg ( mul_nonneg ( hP i j ) ( le_of_lt ( hh j ) ) ) ( mul_nonneg hlam.le ( le_of_lt ( hh i ) ) ), fun i => by rw [ ← Finset.sum_div, heig i, div_self ( ne_of_gt ( mul_pos hlam ( hh i ) ) ) ] ⟩

end C2