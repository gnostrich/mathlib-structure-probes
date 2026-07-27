import Mathlib

open scoped BigOperators
open Real

namespace G1

/-!
# G1. Kernel-pure logarithm enclosures (no `native_decide`)

Rational enclosures of `log 2, log 3, log 5, log 7` proved without any compiler-trusting
tactic.  `log 2` uses Mathlib's kernel-checked `Real.log_two_gt_d9 / _lt_d9`.  The others use
`Real.abs_log_sub_add_sum_range_le` (a kernel-checked truncated-series error bound for
`log (1 - x)`):

* `log 3 = log 2 − log(1 − 1/3)` (`x = 1/3`, 12 terms);
* `log 5 = 2·log 2 − log(1 − 1/5)` (`x = 1/5`, 8 terms);
* `log 7 = 3·log 2 + log(1 − 1/8)` (`x = 1/8`, 8 terms).

No `native_decide` (or any compiler-trusting tactic) is used anywhere in this file.
-/

set_option maxHeartbeats 1000000

theorem G1_log2 : (0.6931 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6932 :=
  ⟨Real.log_two_gt_d9.trans_le' (by norm_num), Real.log_two_lt_d9.trans_le (by norm_num)⟩

theorem G1_log3 : (1.0986 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.0987 := by
  have hb := Real.abs_log_sub_add_sum_range_le (show |(1 / 3 : ℝ)| < 1 by norm_num) 12
  rw [abs_le] at hb
  have hlog : Real.log 3 = Real.log 2 - Real.log (1 - 1 / 3) := by
    rw [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    ring
  obtain ⟨hb1, hb2⟩ := hb
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  rw [hlog]
  norm_num [Finset.sum_range_succ] at hb1 hb2 ⊢
  constructor <;> nlinarith [hb1, hb2, hlo, hhi]

theorem G1_log5 : (1.6094 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.6095 := by
  have hb := Real.abs_log_sub_add_sum_range_le (show |(1 / 5 : ℝ)| < 1 by norm_num) 8
  rw [abs_le] at hb
  have hlog : Real.log 5 = 2 * Real.log 2 - Real.log (1 - 1 / 5) := by
    rw [show (1 - 1 / 5 : ℝ) = 4 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  obtain ⟨hb1, hb2⟩ := hb
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  rw [hlog]
  norm_num [Finset.sum_range_succ] at hb1 hb2 ⊢
  constructor <;> nlinarith [hb1, hb2, hlo, hhi]

theorem G1_log7 : (1.9459 : ℝ) < Real.log 7 ∧ Real.log 7 < 1.9460 := by
  have hb := Real.abs_log_sub_add_sum_range_le (show |(1 / 8 : ℝ)| < 1 by norm_num) 8
  rw [abs_le] at hb
  have hlog : Real.log 7 = 3 * Real.log 2 + Real.log (1 - 1 / 8) := by
    rw [show (1 - 1 / 8 : ℝ) = 7 / 8 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  obtain ⟨hb1, hb2⟩ := hb
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  rw [hlog]
  norm_num [Finset.sum_range_succ] at hb1 hb2 ⊢
  constructor <;> nlinarith [hb1, hb2, hlo, hhi]

end G1
