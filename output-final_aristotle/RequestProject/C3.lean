import RequestProject.C3Base
import RequestProject.C3Feasible
import RequestProject.C3Objective
import RequestProject.C3Pos
import RequestProject.C3Gibbs

open scoped BigOperators

namespace C3

/-!
# C3. Gibbs form of the entropic minimizer (finite Schrödinger bridge)

Over the transport polytope with marginals `μ, ν`, the entropic objective
`F(π) = Σ π c + ε Σ π log(π/r)` has a unique minimizer `π*`, which is strictly
positive and of Gibbs / h-transform form `π*(x,y) = a(x) · r(x,y) e^{-c/ε} · b(y)`.

(Uses the convention `0 · log 0 = 0`, i.e. `Real.log 0 = 0`.)
-/

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable (r c : X × Y → ℝ) (ε : ℝ) (μ : X → ℝ) (ν : Y → ℝ)

theorem C3_bridge
    (hr : ∀ p, 0 < r p) (hε : 0 < ε)
    (hμ : ∀ x, 0 < μ x) (hν : ∀ y, 0 < ν y)
    (hμs : ∑ x, μ x = 1) (hνs : ∑ y, ν y = 1) :
    ∃ π : X × Y → ℝ, feasible μ ν π ∧
      (∀ π', feasible μ ν π' → F r c ε π ≤ F r c ε π') ∧
      (∀ π', feasible μ ν π' →
        (∀ π'', feasible μ ν π'' → F r c ε π' ≤ F r c ε π'') → π' = π) ∧
      (∀ p, 0 < π p) ∧
      (∃ a : X → ℝ, ∃ b : Y → ℝ, (∀ x, 0 < a x) ∧ (∀ y, 0 < b y) ∧
        ∀ x y, π (x, y) = a x * (r (x, y) * Real.exp (- c (x, y) / ε)) * b y) := by
  have hne : {π : X × Y → ℝ | feasible μ ν π}.Nonempty :=
    ⟨_, feasible_indep μ ν (fun x => (hμ x).le) (fun y => (hν y).le) hμs hνs⟩
  obtain ⟨π, hπmem, hπmin⟩ :=
    (feasible_isCompact μ ν (fun x => (hμ x).le) hμs).exists_isMinOn hne
      (F_continuous r c ε hr).continuousOn
  refine ⟨π, hπmem, fun π' hπ' => hπmin hπ', ?_, ?_, ?_⟩
  · -- uniqueness
    intro π' hπ'feas hπ'min
    have hsc := (F_strictConvexOn r c ε hr hε).subset
      (fun q (hq : feasible μ ν q) => hq.1) (feasible_convex μ ν)
    exact hsc.eq_of_isMinOn (fun q hq => hπ'min q hq) hπmin hπ'feas hπmem
  · exact C3_pos r c ε μ ν hr hε hμ hν π hπmem (fun π' hπ' => hπmin hπ')
  · exact C3_gibbs r c ε μ ν hr hε π hπmem (fun π' hπ' => hπmin hπ')
      (C3_pos r c ε μ ν hr hε hμ hν π hπmem (fun π' hπ' => hπmin hπ'))

end C3
