import Mathlib

open scoped BigOperators

namespace C3

/-!
# C3 base definitions (finite Schrödinger bridge)

Shared definitions for the entropic optimal transport problem.
-/

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The entropic objective. -/
noncomputable def F (r c : X × Y → ℝ) (ε : ℝ) (π : X × Y → ℝ) : ℝ :=
  ∑ p, π p * c p + ε * ∑ p, π p * Real.log (π p / r p)

/-- The transport polytope with marginals `μ, ν`. -/
def feasible (μ : X → ℝ) (ν : Y → ℝ) (π : X × Y → ℝ) : Prop :=
  (∀ p, 0 ≤ π p) ∧ (∀ x, ∑ y, π (x, y) = μ x) ∧ (∀ y, ∑ x, π (x, y) = ν y)

end C3
