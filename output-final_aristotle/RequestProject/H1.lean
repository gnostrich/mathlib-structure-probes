import Mathlib

open scoped BigOperators Matrix

namespace H1

/-!
# H1. Discrete continuity equation (probability flux)

`P` is an `n × n` real matrix with row sums `1`, `π : Fin n → ℝ`.  With
`next P π j = ∑ i, π i * P i j` the next distribution and
`current P π i j = π i * P i j - π j * P j i` the probability current,
`next P π j - π j = ∑ i, current P π i j`, and stationarity is equivalent to a
divergence-free current.

(The nonnegativity hypothesis on `P` is not needed for these identities, so it is omitted.)
-/

variable {n : ℕ}

/-- The next distribution `π'(j) = ∑ i, π i * P i j`. -/
def next (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, π i * P i j

/-- The probability current `J(i,j) = π i * P i j - π j * P j i`. -/
def current (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) (i j : Fin n) : ℝ :=
  π i * P i j - π j * P j i

/-
Discrete continuity equation.
-/
theorem H1_continuity (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1) (j : Fin n) :
    next P π j - π j = ∑ i, current P π i j := by
  unfold next current;
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hrow ]

/-
Stationarity is equivalent to a divergence-free current.
-/
theorem H1_stationary (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1) :
    (∀ j, next P π j = π j) ↔ (∀ j, ∑ i, current P π i j = 0) := by
  constructor <;> intro h j;
  · have := H1_continuity P π hrow j; aesop;
  · exact eq_of_sub_eq_zero ( H1_continuity P π hrow j ▸ by simpa [ Finset.mul_sum _ _ _ ] using h j )

end H1