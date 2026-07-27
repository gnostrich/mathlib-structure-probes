import Mathlib
import RequestProject.E1
import RequestProject.E2

open scoped BigOperators
open Real

namespace E3

/-!
# E3. Weighted atom bounds

Rational enclosures of the first weighted von Mangoldt atoms `(log 2)/√2` and `(log 3)/√3`.
-/

theorem E3_atom2 : (0.4900 : ℝ) < Real.log 2 / Real.sqrt 2 ∧ Real.log 2 / Real.sqrt 2 < 0.4902 := by
  constructor <;> norm_num;
  · rw [ lt_div_iff₀ ] <;> norm_num;
    exact lt_of_le_of_lt ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) ( Real.log_two_gt_d9.gt );
  · rw [ div_lt_iff₀ ] <;> norm_num;
    exact lt_of_le_of_lt ( Real.log_two_lt_d9.le ) ( by norm_num; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] )

/-
The original prompt stated `0.6343 < (log 3)/√3 < 0.6344`, but this is false: the true
value is `(log 3)/√3 ≈ 0.634284`, which is *below* `0.6343`.  With the E1/E2 enclosures the
provable (and correct) enclosure is `0.6342 < (log 3)/√3 < 0.6344`; this is what is stated.
-/
theorem E3_atom3 : (0.6342 : ℝ) < Real.log 3 / Real.sqrt 3 ∧ Real.log 3 / Real.sqrt 3 < 0.6344 := by
  rw [ lt_div_iff₀, div_lt_iff₀ ] <;> norm_num;
  constructor;
  · -- We'll use that $Real.log 3 > 1.0986$ to conclude the proof.
    have h_log3 : Real.log 3 > 1.0986 := by
      exact E2.E2_log3.1.trans_le' <| by norm_num;
    norm_num at h_log3 ; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ];
  · -- We'll use that $Real.log 3 < 1.0987$ to conclude the proof.
    have h_log : Real.log 3 < 1.0987 := by
      exact E2.E2_log3.2.trans_le <| by norm_num;
    exact h_log.trans_le <| by norm_num; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] ;

end E3