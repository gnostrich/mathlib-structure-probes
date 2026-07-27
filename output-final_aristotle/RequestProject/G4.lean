import Mathlib
import RequestProject.E1
import RequestProject.E2

open scoped BigOperators
open Real

namespace G4

/-!
# G4. Atom enclosures for p = 7 and p = 11

Using `1.9459 < log 7 < 1.9460` (E2) and `2.6457 < √7 < 2.6458` (E1), together with proven
enclosures `2.3978 < log 11 < 2.3980` and `3.3166 < √11 < 3.3167`:

* (a) `0.7354 < (log 7)/√7 < 0.7356`;
* (b) `0.7229 < (log 11)/√11 < 0.7231`;
* (c) `(log 11)/√11 < (log 7)/√7`.
-/

/-- Enclosure `3.3166 < √11 < 3.3167` (by squaring). -/
theorem G4_sqrt11 : (3.3166 : ℝ) < Real.sqrt 11 ∧ Real.sqrt 11 < 3.3167 := by
  constructor
  · rw [show (3.3166 : ℝ) = Real.sqrt (3.3166 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by positivity); norm_num
  · rw [show (3.3167 : ℝ) = Real.sqrt (3.3167 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by norm_num); norm_num

/-
Enclosure `2.3978 < log 11 < 2.3980`.  Route: `log 11 = 2·log 2 + log 3 + log(1 − 1/12)`
with the truncated-series error bound `Real.abs_log_sub_add_sum_range_le` at `x = 1/12`, using
the G1/E2 enclosures of `log 2, log 3`.
-/
theorem G4_log11 : (2.3978 : ℝ) < Real.log 11 ∧ Real.log 11 < 2.3980 := by
  constructor;
  · norm_num [ Real.lt_log_iff_exp_lt ];
    -- We can prove the inequality $e^{11989 / 5000} < 11$ by raising both sides to the power of $5000$:
    have h_exp_5000 : Real.exp 11989 < 11 ^ 5000 := by
      have := Real.exp_one_lt_d9.le;
      -- We can use the fact that $e^{11989} < 11^{5000}$ by comparing their logarithms.
      have h_log : 11989 * Real.log 2.7182818286 < 5000 * Real.log 11 := by
        rw [ ← Real.log_rpow, ← Real.log_rpow, Real.log_lt_log_iff ] <;> norm_num;
        rw [ div_pow, div_lt_iff₀ ] <;> first | positivity | exact mod_cast by native_decide;
      rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_pow ];
      exact lt_of_le_of_lt ( by norm_num ) ( h_log.trans_le' ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) this ) ( by norm_num ) ) );
    contrapose! h_exp_5000;
    exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp_5000 5000 ) ( by rw [ ← Real.exp_nat_mul ] ; norm_num );
  · -- We'll use the exponential function to bound 11 from above.
    have h_exp : 11 < Real.exp (2.3980) := by
      norm_num [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ] at *;
      exact lt_of_lt_of_le ( by norm_num [ Finset.sum_range_succ, Nat.factorial ] ) ( Summable.sum_le_tsum ( Finset.range 20 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
    rwa [ Real.log_lt_iff_lt_exp ( by norm_num ) ]

/-- (a) The p = 7 atom enclosure. -/
theorem G4_a : (0.7354 : ℝ) < Real.log 7 / Real.sqrt 7 ∧ Real.log 7 / Real.sqrt 7 < 0.7356 := by
  have hs := E1.E1_sqrt7
  have hl := E2.E2_log7
  have hsp : (0 : ℝ) < Real.sqrt 7 := by positivity
  constructor
  · rw [lt_div_iff₀ hsp]; nlinarith [hs.1, hs.2, hl.1]
  · rw [div_lt_iff₀ hsp]; nlinarith [hs.1, hs.2, hl.2]

/-- (b) The p = 11 atom enclosure. -/
theorem G4_b :
    (0.7229 : ℝ) < Real.log 11 / Real.sqrt 11 ∧ Real.log 11 / Real.sqrt 11 < 0.7231 := by
  have hs := G4_sqrt11
  have hl := G4_log11
  have hsp : (0 : ℝ) < Real.sqrt 11 := by positivity
  constructor
  · rw [lt_div_iff₀ hsp]; nlinarith [hs.1, hs.2, hl.1]
  · rw [div_lt_iff₀ hsp]; nlinarith [hs.1, hs.2, hl.2]

/-- (c) The p = 11 atom is smaller than the p = 7 atom. -/
theorem G4_c : Real.log 11 / Real.sqrt 11 < Real.log 7 / Real.sqrt 7 := by
  calc Real.log 11 / Real.sqrt 11 < 0.7231 := G4_b.2
    _ < 0.7354 := by norm_num
    _ < Real.log 7 / Real.sqrt 7 := G4_a.1

end G4