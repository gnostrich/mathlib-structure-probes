import Mathlib

open scoped BigOperators Matrix

namespace B3

/-!
# B3. Schur / E_B identity

For an upper-triangular matrix `A`, the `(i,i)` entry of `Aᵏ` is `(A_{ii})ᵏ`.
-/

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

/-
Upper-triangular: entries strictly below the diagonal vanish.
-/
theorem B3_diag_pow (hA : ∀ i j, j < i → A i j = 0) :
    ∀ (k : ℕ) (i : Fin n), (A ^ k) i i = (A i i) ^ k := by
  intro k;
  induction k <;> simp_all +decide [ pow_succ, Matrix.mul_apply ];
  intro i; rw [ Finset.sum_eq_single i ] <;> simp_all +decide [ pow_succ, Matrix.mul_apply ] ;
  -- By induction on $k$, we can show that $(A^k)_{ij} = 0$ for all $j < i$.
  have h_ind : ∀ k : ℕ, ∀ i j : Fin n, j < i → (A ^ k) i j = 0 := by
    intro k i j hij; induction' k with k ih generalizing i j <;> simp_all +decide [ pow_succ, Matrix.mul_apply ] ;
    · exact if_neg hij.ne';
    · rw [ Finset.sum_eq_single j ] <;> simp_all +decide [ Matrix.mul_apply ];
      grind;
  grind

end B3