import RequestProject.V5_1
import RequestProject.GW1

open scoped BigOperators
open ArithmeticFunction

namespace V5_7

/-- The compactly supported triangular window. -/
noncomputable def triangle (t x : ℝ) : ℝ :=
  if |x| ≤ t then (t - |x|) / 2 else 0

/-
Exact finite prime-power identity for triangular test data.
-/
theorem triangular_prime_sum (t : ℝ) (ht : 0 < t) (N : ℕ)
    (hN : Real.exp t ≤ N) :
    ∑ n ∈ Finset.Icc 2 N,
        (Λ n / Real.sqrt n) *
          (triangle t (Real.log n) + triangle t (-Real.log n)) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        (Λ n / Real.sqrt n) * (t - Real.log n) := by
  unfold triangle;
  rw [ ← Finset.sum_subset ( Finset.Icc_subset_Icc_right ( Nat.floor_le_of_le hN ) ) ];
  · refine' Finset.sum_congr rfl fun x hx => _;
    norm_num [ abs_of_nonneg, Real.log_nonneg ( show ( x : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hx ] ) ];
    split_ifs <;> norm_num;
    exact False.elim <| ‹¬Real.log x ≤ t› <| Real.log_le_iff_le_exp ( by norm_cast; linarith [ Finset.mem_Icc.mp hx ] ) |>.2 <| by linarith [ Nat.floor_le <| Real.exp_nonneg t, show ( x : ℝ ) ≤ ⌊Real.exp t⌋₊ by exact_mod_cast Finset.mem_Icc.mp hx |>.2 ] ;
  · intro x hx₁ hx₂; contrapose! hx₂; simp_all +decide [ abs_of_nonneg, Real.log_nonneg ] ;
    exact Nat.le_floor <| by rw [ abs_of_nonneg <| Real.log_nonneg <| Nat.one_le_cast.2 <| by linarith ] at hx₂; rw [ ← Real.log_le_iff_le_exp ] <;> norm_cast <;> linarith;

/-
The prime side of `GW1.W` at a triangular window is exactly Suzuki's finite prime sum.
-/
theorem weil_triangle_prime_side (t : ℝ) (ht : 0 < t) (N : ℕ)
    (hN : Real.exp t ≤ N) :
    ∑ n ∈ Finset.Icc 2 N,
        (Λ n / Real.sqrt n) *
          (triangle t (Real.log n) + triangle t (-Real.log n)) = V5_1.primeSum t := by
  convert triangular_prime_sum t ht N hN using 1

end V5_7