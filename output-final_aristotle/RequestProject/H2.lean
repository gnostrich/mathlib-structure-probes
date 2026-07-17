import Mathlib

open scoped BigOperators Matrix

namespace H2

/-!
# H2. The force is a gradient (h-transform drift identity)

For the Doob transform `Q(i,j) = P(i,j)·h(j)/(λ·h(i))`,
`log Q(i,j) − log P(i,j) = log h(j) − log h(i) − log λ`.

(The eigenvector hypothesis `P·h = λ·h` is not needed for this pointwise identity, so it is
omitted; only positivity of the entries involved is used to split the logarithm.)
-/

variable {n : ℕ}

/-- The Doob `h`-transform `Q(i,j) = P(i,j)·h(j)/(λ·h(i))`. -/
noncomputable def doob (P : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (lam : ℝ)
    (i j : Fin n) : ℝ :=
  P i j * h j / (lam * h i)

/-
The tilt adds a potential difference and a constant.
-/
theorem H2_gradient (P : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (lam : ℝ)
    (hP : ∀ i j, 0 < P i j) (hh : ∀ i, 0 < h i) (hlam : 0 < lam) (i j : Fin n) :
    Real.log (doob P h lam i j) - Real.log (P i j)
      = Real.log (h j) - Real.log (h i) - Real.log lam := by
  unfold doob; rw [ Real.log_div, Real.log_mul, Real.log_mul ] <;> ring <;> simp +decide [ ne_of_gt, * ] ;

end H2