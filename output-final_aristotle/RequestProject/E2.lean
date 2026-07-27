import Mathlib

open scoped BigOperators
open Real

namespace E2

/-!
# E2. Enclosure toolkit: logarithms

Explicit rational enclosures of `log 2, log 3, log 5, log 7`.
-/

theorem E2_log2 : (0.6931 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6932 := by
  exact ⟨ Real.log_two_gt_d9.trans_le' <| by norm_num, Real.log_two_lt_d9.trans_le <| by norm_num ⟩

theorem E2_log3 : (1.0986 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.0987 := by
  constructor <;> norm_num [ Real.lt_log_iff_exp_lt, Real.log_lt_iff_lt_exp ];
  · -- We can prove the inequality $e^{5493 / 5000} < 3$ by raising both sides to the power of $5000$:
    have h_exp_5000 : Real.exp (5493) < 3 ^ 5000 := by
      have := Real.exp_one_lt_d9.le;
      have h_exp : Real.exp 5493 < (2.7182818286 : ℝ) ^ 5493 := by
        rw [ show Real.exp 5493 = ( Real.exp 1 ) ^ 5493 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact pow_lt_pow_left₀ ( lt_of_le_of_ne this ( by exact ne_of_lt ( Real.exp_one_lt_d9.trans_le ( by norm_num ) ) ) ) ( by positivity ) ( by norm_num );
      exact h_exp.trans_le ( by rw [ show ( 2.7182818286 : ℝ ) = 27182818286 / 10000000000 by norm_num ] ; rw [ div_pow ] ; rw [ div_le_iff₀ ] <;> exact mod_cast by native_decide );
    contrapose! h_exp_5000;
    exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp_5000 5000 ) ( by rw [ ← Real.exp_nat_mul ] ; norm_num );
  · -- We can use the exponential property: $e^{10987 / 10000} = \left(e^{1 / 10000}\right)^{10987}$.
    suffices h_exp : (Real.exp (1 / 10000)) ^ 10987 > 3 by
      exact h_exp.trans_le ( by rw [ ← Real.exp_nat_mul ] ; norm_num );
    refine' lt_of_lt_of_le _ ( pow_le_pow_left₀ ( by positivity ) ( show Real.exp ( 1 / 10000 ) ≥ 1 + 1 / 10000 + ( 1 / 10000 ) ^ 2 / 2 + ( 1 / 10000 ) ^ 3 / 6 by
                                                                      rw [ Real.exp_eq_exp_ℝ ];
                                                                      rw [ NormedSpace.exp_eq_tsum_div ] ; exact le_trans ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 4 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) ) ; ) _ ) ; norm_num;
    rw [ div_pow, lt_div_iff₀ ] <;> first | positivity | exact mod_cast by native_decide;

theorem E2_log5 : (1.6094 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.6095 := by
  constructor <;> norm_num [ Real.lt_log_iff_exp_lt, Real.log_lt_iff_lt_exp ];
  · -- We can raise both sides to the power of 5000 to remove the fraction.
    suffices h_exp : Real.exp 8047 < 5 ^ 5000 by
      contrapose! h_exp;
      exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp 5000 ) ( by norm_num [ ← Real.exp_nat_mul ] );
    have := Real.exp_one_lt_d9.le;
    -- We'll use that $Real.exp 8047 < (2.7182818286)^{8047}$ and compare it to $5^{5000}$.
    have h_exp : Real.exp 8047 < (2.7182818286 : ℝ) ^ 8047 := by
      rw [ show Real.exp 8047 = ( Real.exp 1 ) ^ 8047 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact pow_lt_pow_left₀ ( show Real.exp 1 < 2.7182818286 by exact lt_of_le_of_ne this <| by exact ne_of_lt <| Real.exp_one_lt_d9.trans_le <| by norm_num ) ( by positivity ) <| by norm_num;
    exact h_exp.trans_le ( by rw [ show ( 2.7182818286 : ℝ ) = 27182818286 / 10000000000 by norm_num ] ; rw [ div_pow ] ; rw [ div_le_iff₀ ] <;> exact mod_cast by native_decide );
  · -- We can raise both sides to the power of 2000 to remove the fraction.
    suffices h_exp : (5 : ℝ) ^ 2000 < Real.exp 3219 by
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 2000 );
    have := Real.exp_one_gt_d9.le;
    -- We can raise both sides to the power of 3219 to remove the fraction.
    have h_exp : (5 : ℝ) ^ 2000 < (2.7182818283 : ℝ) ^ 3219 := by
      norm_num;
      rw [ div_pow, lt_div_iff₀ ] <;> first | positivity | exact mod_cast by native_decide;
    exact h_exp.trans_le ( by rw [ show Real.exp 3219 = ( Real.exp 1 ) ^ 3219 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact pow_le_pow_left₀ ( by norm_num ) this _ )

theorem E2_log7 : (1.9459 : ℝ) < Real.log 7 ∧ Real.log 7 < 1.9460 := by
  constructor;
  · norm_num [ Real.lt_log_iff_exp_lt ];
    -- We can raise both sides to the power of 10000 to remove the fraction.
    suffices h_exp : Real.exp 19459 < 7 ^ 10000 by
      contrapose! h_exp;
      exact le_trans ( pow_le_pow_left₀ ( by norm_num ) h_exp 10000 ) ( by rw [ ← Real.exp_nat_mul ] ; norm_num );
    have := Real.exp_one_lt_d9;
    -- We can raise both sides to the power of 10000 to remove the fraction and simplify the inequality.
    have h_exp : (Real.exp 1) ^ 19459 < (7 : ℝ) ^ 10000 := by
      -- By raising both sides of the inequality $Real.exp 1 < 2.7182818286$ to the power of $19459$, we get $(Real.exp 1)^{19459} < (2.7182818286)^{19459}$.
      have h_exp_pow : (Real.exp 1) ^ 19459 < (2.7182818286 : ℝ) ^ 19459 := by
        gcongr;
      exact h_exp_pow.trans_le ( by rw [ show ( 2.7182818286 : ℝ ) = 27182818286 / 10000000000 by norm_num ] ; rw [ div_pow ] ; rw [ div_le_iff₀ ] <;> exact mod_cast by native_decide );
    simpa [ ← Real.exp_nat_mul ] using h_exp;
  · -- By combining the results, we conclude that $\log 7 < 1.9460$.
    have h_log7_lt : Real.log 7 < 1.9460 := by
      have h_exp_bound : Real.exp (1.9460) > 7 := by
        -- We can raise both sides to the power of 1000 to remove the fraction.
        suffices h_exp : (7 : ℝ) ^ 1000 < Real.exp 1946 by
          contrapose! h_exp;
          exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 1000 );
        have := Real.exp_one_gt_d9.le;
        -- We can raise both sides to the power of 1946 to remove the fraction.
        have h_exp : (7 : ℝ) ^ 1000 < (2.7182818283 : ℝ) ^ 1946 := by
          norm_num;
          rw [ div_pow, lt_div_iff₀ ] <;> first | positivity | exact mod_cast by native_decide;
        exact h_exp.trans_le ( by simpa using pow_le_pow_left₀ ( by norm_num ) this 1946 )
      rwa [ Real.log_lt_iff_lt_exp ( by norm_num ) ];
    exact h_log7_lt

end E2