import Mathlib

open scoped BigOperators

namespace I3

/-!
# I3. Fermion parity of the gas

For every squarefree positive integer `n`, `μ(n) = (−1)^Ω(n)`, where `Ω(n)` is the number of
prime factors counted with multiplicity (`ArithmeticFunction.cardFactors`).
-/

theorem I3_moebius (n : ℕ) (hn : Squarefree n) :
    ArithmeticFunction.moebius n = (-1) ^ ArithmeticFunction.cardFactors n :=
  ArithmeticFunction.moebius_apply_of_squarefree hn

end I3
