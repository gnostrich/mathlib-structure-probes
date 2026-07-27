import Mathlib
import RequestProject.Horizon

open scoped BigOperators Matrix
open Horizon

namespace H5

/-!
# H5. Smith positivity: the GCD matrix is PSD

For `n ≥ 1`, the `n × n` matrix `M(i,j) = gcd(i,j)` (indices `1..n`) is positive semidefinite.
Route: `gcd(i,j) = ∑_{d=1}^{n} φ(d)·e_d(i)·e_d(j)` with `e_d(i) = 1` if `d ∣ i` else `0`
(from `∑_{d ∣ m} φ(d) = m`), so `M` is a nonnegative combination of rank-one squares.
-/

/-- The gcd matrix on indices `1..n` (represented by `Fin n` shifted by one). -/
def gcdMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (Nat.gcd (i + 1) (j + 1) : ℝ)

theorem H5_psd (n : ℕ) : IsPSDq (gcdMatrix n) := by
  -- By definition of gcdMatrix, we know that for any i, j, gcdMatrix n i j = ∑ d ∈ Finset.Icc 1 n, (if d ∣ i + 1 ∧ d ∣ j + 1 then Nat.totient d else 0).
  have h_gcdMatrix : ∀ i j : Fin n, gcdMatrix n i j = ∑ d ∈ Finset.Icc 1 n, (if d ∣ i.val + 1 ∧ d ∣ j.val + 1 then Nat.totient d else 0) := by
    intro i j; simp +decide [ gcdMatrix ] ;
    rw_mod_cast [ ← Nat.sum_totient ( Nat.gcd ( i + 1 ) ( j + 1 ) ) ];
    rw [ ← Finset.sum_filter ];
    congr 1 with x ; simp +decide [ Nat.dvd_gcd_iff ];
    exact fun hi hj => ⟨ Nat.pos_of_dvd_of_pos hi ( Nat.succ_pos _ ), Nat.le_trans ( Nat.le_of_dvd ( Nat.succ_pos _ ) hi ) ( Nat.succ_le_of_lt i.2 ) ⟩;
  -- By definition of quadratic form, we can write it as a sum over the indices.
  intro x
  have h_quadForm : quadForm (gcdMatrix n) x = ∑ d ∈ Finset.Icc 1 n, Nat.totient d * (∑ i : Fin n, if d ∣ (i.val + 1) then x i else 0) ^ 2 := by
    simp +decide only [quadForm, h_gcdMatrix];
    simp +decide only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.mul_sum _ _ _, mul_comm, mul_left_comm,
        pow_two];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; rw [ Finset.sum_comm ] ;
    intro i hi; rw [ Finset.sum_comm ] ; congr; ext j; split_ifs <;> simp +decide [ *, mul_assoc, mul_comm, mul_left_comm ] ;
  exact h_quadForm.symm ▸ Finset.sum_nonneg fun _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ )

end H5