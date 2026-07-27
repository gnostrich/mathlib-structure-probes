import Mathlib
import RequestProject.E1
import RequestProject.E2

open scoped BigOperators
open Real

namespace G2

/-!
# G2. Enclosure for the p = 5 atom

From `1.6094 < log 5 < 1.6095` (E2) and `2.2360 < √5 < 2.2361` (E1),
`0.7197 < (log 5)/√5 < 0.7198`.
-/

theorem G2_atom5 :
    (0.7197 : ℝ) < Real.log 5 / Real.sqrt 5 ∧ Real.log 5 / Real.sqrt 5 < 0.7198 := by
  constructor;
  · -- Use `E2.E2_log5` to obtain the lower bound on `Real.log 5`.
    have h_log5 : Real.log 5 > 1.6094 := by
      exact E2.E2_log5.1.trans_le' <| by norm_num;
    rw [ lt_div_iff₀ ] <;> norm_num at * ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
  · rw [ div_lt_iff₀ ] <;> norm_num;
    exact lt_of_le_of_lt ( show Real.log 5 ≤ 1.6095 by exact le_of_lt <| by have := E2.E2_log5; norm_num at *; linarith ) <| by nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt <| show 0 ≤ 5 by norm_num ] ;

end G2