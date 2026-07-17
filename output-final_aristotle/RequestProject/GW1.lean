import Mathlib

open scoped BigOperators
open ArithmeticFunction

namespace GW1

/-!
# GW1. The finite Weil functional (statement layer)

For `N ≥ 2`, an abstract archimedean linear functional `A : (ℝ → ℝ) →ₗ[ℝ] ℝ`, and `f : ℝ → ℝ`,
the finite Weil functional is
`W A N f := A f − ∑_{n=2}^{N} (Λ n / √n) · (f (log n) + f (−log n))`.

* (a) `W` is linear in `f`.
* (b) if `f` is even, `W A N f = A f − 2·∑_{n=2}^{N} (Λ n / √n) · f (log n)`.
* (c) the sum ranges effectively over prime powers (`Λ n = 0` unless `n` is a prime power).
* (d) autocorrelation sequences are even: `c_{−m} = c_m`.
-/

/-- The finite Weil functional. -/
noncomputable def W (A : (ℝ → ℝ) →ₗ[ℝ] ℝ) (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  A f - ∑ n ∈ Finset.Icc 2 N,
    (Λ n / Real.sqrt n) * (f (Real.log n) + f (-Real.log n))

/-- (a) Additivity in `f`. -/
theorem GW1_a_add (A : (ℝ → ℝ) →ₗ[ℝ] ℝ) (N : ℕ) (f g : ℝ → ℝ) :
    W A N (f + g) = W A N f + W A N g := by
  simp only [W, map_add, Pi.add_apply]
  rw [Finset.sum_congr rfl (fun n _ =>
      show (Λ n / Real.sqrt n) *
            (f (Real.log n) + g (Real.log n) + (f (-Real.log n) + g (-Real.log n)))
          = (Λ n / Real.sqrt n) * (f (Real.log n) + f (-Real.log n))
            + (Λ n / Real.sqrt n) * (g (Real.log n) + g (-Real.log n)) from by ring),
    Finset.sum_add_distrib]
  ring

/-- (a) Homogeneity in `f`. -/
theorem GW1_a_smul (A : (ℝ → ℝ) →ₗ[ℝ] ℝ) (N : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    W A N (c • f) = c * W A N f := by
  simp only [W, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- (b) Even test functions collapse the two-sided sum. -/
theorem GW1_b (A : (ℝ → ℝ) →ₗ[ℝ] ℝ) (N : ℕ) (f : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) :
    W A N f = A f - 2 * ∑ n ∈ Finset.Icc 2 N, (Λ n / Real.sqrt n) * f (Real.log n) := by
  simp only [W]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [hf]
  ring

/-- (c) The sum ranges effectively over prime powers. -/
theorem GW1_c (A : (ℝ → ℝ) →ₗ[ℝ] ℝ) (N : ℕ) (f : ℝ → ℝ) :
    W A N f = A f - ∑ n ∈ (Finset.Icc 2 N).filter IsPrimePow,
      (Λ n / Real.sqrt n) * (f (Real.log n) + f (-Real.log n)) := by
  simp only [W]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : IsPrimePow n
  · simp [h]
  · simp only [h, if_false]
    have hΛ : Λ n = 0 := by
      rw [← ArithmeticFunction.vonMangoldt_ne_zero_iff] at h
      simpa using h
    rw [hΛ]; simp

/-- The (two-sided) autocorrelation sequence of a finitely supported `x : ℤ →₀ ℝ`. -/
noncomputable def autocorr (x : ℤ →₀ ℝ) (m : ℤ) : ℝ := ∑ᶠ i : ℤ, x i * x (i + m)

/-- (d) Autocorrelation sequences are even. -/
theorem GW1_d (x : ℤ →₀ ℝ) (m : ℤ) : autocorr x (-m) = autocorr x m := by
  unfold autocorr
  rw [← finsum_comp_equiv (Equiv.addRight (-m)) (f := fun i => x i * x (i + m))]
  apply finsum_congr
  intro i
  simp only [Equiv.coe_addRight]
  rw [mul_comm]
  congr 2 <;> ring

end GW1
