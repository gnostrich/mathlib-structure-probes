import Mathlib

open scoped BigOperators

namespace A1

/-!
# A1. Picard–Lefschetz transvection is unipotent and symplectic

`V` a real vector space, `ω` an alternating bilinear form, `δ ∈ V`, and
`T x = x + ω(x, δ) • δ`.  We show `(T - id)² = 0`, `T` is bijective with the
stated inverse, and `T` preserves `ω`.

(Finite-dimensionality is not needed and hence not assumed.)
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (δ : V)

/-- The Picard–Lefschetz transvection `T x = x + ω(x, δ) • δ`. -/
noncomputable def T : V →ₗ[ℝ] V :=
  LinearMap.id + LinearMap.smulRight (ω.flip δ) δ

@[simp] lemma T_apply (x : V) : T ω δ x = x + ω x δ • δ := by
  simp [T, LinearMap.smulRight_apply, LinearMap.flip_apply]

/-- The candidate inverse `T' x = x - ω(x, δ) • δ`. -/
noncomputable def T' : V →ₗ[ℝ] V :=
  LinearMap.id - LinearMap.smulRight (ω.flip δ) δ

@[simp] lemma T'_apply (x : V) : T' ω δ x = x - ω x δ • δ := by
  simp [T', LinearMap.smulRight_apply, LinearMap.flip_apply]

/-
(a) `(T - id) ∘ (T - id) = 0`.
-/
theorem A1_a (halt : ∀ x, ω x x = 0) :
    (T ω δ - LinearMap.id).comp (T ω δ - LinearMap.id) = 0 := by
  ext x;
  simp +decide [ halt, mul_assoc, T ]

/-
(b) `T` is bijective with inverse `T'`.
-/
theorem A1_b (halt : ∀ x, ω x x = 0) :
    Function.Bijective (T ω δ) ∧
      (T ω δ).comp (T' ω δ) = LinearMap.id ∧ (T' ω δ).comp (T ω δ) = LinearMap.id := by
  have h_bijective : Function.Bijective (T ω δ) := by
    refine' ⟨ _, _ ⟩;
    · -- By definition of $T$, we know that $T(x) = x + \omega(x, \delta) \cdot \delta$.
      intro x y hxy
      simp [T_apply] at hxy;
      have := congr_arg ( fun z => ω z δ ) hxy; norm_num [ halt ] at this; simp_all +decide [ add_smul, smul_add, smul_sub, sub_smul ] ;
    · intro y; use y - ω y δ • δ; simp +decide [ T_apply, halt ] ;
  simp_all +decide [ LinearMap.ext_iff, Function.Bijective ]

/-
(c) `T` preserves `ω`.
-/
theorem A1_c (halt : ∀ x, ω x x = 0) (x y : V) :
    ω (T ω δ x) (T ω δ y) = ω x y := by
  have := halt ( δ + y ) ; simp_all +decide [ add_smul, smul_add ] ;
  linear_combination' this * ( ω x ) δ

end A1