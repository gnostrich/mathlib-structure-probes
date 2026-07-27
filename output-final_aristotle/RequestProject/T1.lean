import Mathlib

open scoped BigOperators
open ArithmeticFunction

namespace T1

/-!
# T1. Von Mangoldt is dominated by log

For every natural number `n`, `Λ n ≤ log n`, where `Λ` is the von Mangoldt function.
This is `ArithmeticFunction.vonMangoldt_le_log` (which holds for all `n`, including `n = 0`
where both sides are `0`).
-/

theorem T1_vonMangoldt_le_log (n : ℕ) : Λ n ≤ Real.log n :=
  ArithmeticFunction.vonMangoldt_le_log

end T1
