import Mathlib

open scoped BigOperators

namespace H4

/-!
# H4. The 3-4-1 repulsion identity

For every real `θ`, `3 + 4·cos θ + cos (2·θ) = 2·(1 + cos θ)² ≥ 0`
(de la Vallée Poussin's zero-repulsion inequality).
-/

theorem H4_repulsion (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2
      ∧ 0 ≤ 2 * (1 + Real.cos θ) ^ 2 := by
  exact ⟨ by rw [ Real.cos_two_mul ] ; ring, by positivity ⟩

end H4