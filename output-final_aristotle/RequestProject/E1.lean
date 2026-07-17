import Mathlib

open scoped BigOperators

namespace E1

/-!
# E1. Enclosure toolkit: square roots

Explicit rational enclosures of `√2, √3, √5, √7`, each provable by squaring.
-/

theorem E1_sqrt2 : (1.4142 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  norm_num [ Real.lt_sqrt, Real.sqrt_lt ]

theorem E1_sqrt3 : (1.7320 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1.7321 := by
  norm_num [ Real.lt_sqrt, Real.sqrt_lt ]

theorem E1_sqrt5 : (2.2360 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2.2361 := by
  norm_num [ Real.lt_sqrt, Real.sqrt_lt ]

theorem E1_sqrt7 : (2.6457 : ℝ) < Real.sqrt 7 ∧ Real.sqrt 7 < 2.6458 := by
  norm_num [ Real.lt_sqrt, Real.sqrt_lt ]

end E1