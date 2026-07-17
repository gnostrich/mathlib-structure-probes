import Mathlib

open scoped BigOperators

namespace A2

/-!
# A2. Rank-one polarization is automatically positive

`ω` alternating bilinear, `δ ∈ V`, `N x = ω(x, δ) • δ`.  The twisted quadratic
form `Q x = ω(x, N x)` equals `ω(x, δ)²`, hence is PSD, and its kernel is exactly
`{x : ω(x, δ) = 0}`, which contains the image of `N`.
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (δ : V)

/-- The nilpotent `N x = ω(x, δ) • δ`. -/
noncomputable def N : V →ₗ[ℝ] V :=
  LinearMap.smulRight (ω.flip δ) δ

@[simp] lemma N_apply (x : V) : N ω δ x = ω x δ • δ := by
  simp [N, LinearMap.smulRight_apply, LinearMap.flip_apply]

/-- The twisted quadratic form. -/
noncomputable def Q (x : V) : ℝ := ω x (N ω δ x)

/-
(a) `N ∘ N = 0`.
-/
theorem A2_a (halt : ∀ x, ω x x = 0) : (N ω δ).comp (N ω δ) = 0 := by
  ext x; simp +decide [ *, N ] ;

/-
(b) `Q x = ω(x, δ)² ≥ 0`.
-/
theorem A2_b (x : V) : Q ω δ x = (ω x δ) ^ 2 ∧ 0 ≤ Q ω δ x := by
  unfold Q N;
  simp +decide [ sq ];
  exact mul_self_nonneg _

/-
(c) `Q x = 0 ↔ ω(x, δ) = 0`, and the image of `N` lies in the kernel of `Q`.
-/
theorem A2_c (halt : ∀ x, ω x x = 0) :
    (∀ x, Q ω δ x = 0 ↔ ω x δ = 0) ∧ (∀ x, Q ω δ (N ω δ x) = 0) := by
  constructor <;> intro x <;> simp +decide [ *, Q ]

end A2