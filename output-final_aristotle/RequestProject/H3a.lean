import Mathlib

open scoped BigOperators

namespace H3a

/-!
# H3a. Lee–Yang base pair

Let `a : ℝ` with `a² ≤ 1`.
* (i) For all `z₁, z₂ : ℂ` with `‖z₁‖ < 1` and `‖z₂‖ < 1`, `1 + a·z₁ + a·z₂ + z₁·z₂ ≠ 0`.
* (ii) Every root of `1 + 2a·z + z²` has modulus exactly `1`.
-/

/-
(i) Lee–Yang two-variable nonvanishing on the bidisc.
-/
theorem H3a_i (a : ℝ) (ha : a ^ 2 ≤ 1) (z₁ z₂ : ℂ) (h1 : ‖z₁‖ < 1) (h2 : ‖z₂‖ < 1) :
    1 + (a : ℂ) * z₁ + (a : ℂ) * z₂ + z₁ * z₂ ≠ 0 := by
  by_contra h;
  -- Case 2: If $‖a + z₂‖ > 0$, then from $‖z₁‖ < 1$ we get $‖z₁‖ * ‖a + z₂‖ < ‖a + z₂‖ ≤ ‖1 + a·z₂‖$, contradicting the equality $‖z₁‖ * ‖a + z₂‖ = ‖1 + a·z₂‖$.
  by_cases hz : ‖(a : ℂ) + z₂‖ = 0;
  · norm_num [ show z₂ = -a by { norm_num [ Complex.ext_iff ] at *; constructor <;> linarith } ] at *;
    ring_nf at h; norm_cast at h; nlinarith [ abs_lt.mp h2 ] ;
  · -- Then $‖a + z₂‖ ≤ ‖1 + a·z₂‖$.
    have h_le : ‖(a : ℂ) + z₂‖ ≤ ‖(1 : ℂ) + a * z₂‖ := by
      have h_le : ‖(1 : ℂ) + a * z₂‖^2 - ‖(a : ℂ) + z₂‖^2 = (1 - a^2) * (1 - ‖z₂‖^2) := by
        norm_num [ Complex.normSq, Complex.sq_norm ] ; ring;
      nlinarith [ show 0 ≤ ‖1 + a * z₂‖ by positivity, show 0 ≤ ‖a + z₂‖ by positivity, show 0 ≤ ( 1 - a ^ 2 ) * ( 1 - ‖z₂‖ ^ 2 ) by exact mul_nonneg ( by nlinarith ) ( by nlinarith [ norm_nonneg z₂ ] ) ];
    -- From $1 + a·z₁ + a·z₂ + z₁·z₂ = 0$, we get $z₁·(a + z₂) = -(1 + a·z₂)$, so taking norms $‖z₁‖ * ‖a + z₂‖ = ‖1 + a·z₂‖$.
    have h_norm : ‖z₁‖ * ‖(a : ℂ) + z₂‖ = ‖(1 : ℂ) + a * z₂‖ := by
      rw [ ← norm_mul ] ; rw [ show z₁ * ( a + z₂ ) = - ( 1 + a * z₂ ) by linear_combination' h ] ; norm_num;
      rw [ ← norm_neg ] ; ring;
    nlinarith [ show 0 < ‖ ( a : ℂ ) + z₂‖ from lt_of_le_of_ne ( norm_nonneg _ ) ( Ne.symm hz ) ]

/-
(ii) Both roots of `1 + 2a·z + z²` lie on the unit circle.
-/
theorem H3a_ii (a : ℝ) (ha : a ^ 2 ≤ 1) (z : ℂ) (hz : 1 + 2 * (a : ℂ) * z + z ^ 2 = 0) :
    ‖z‖ = 1 := by
  by_contra h_contra; have hz_ne_zero : z ≠ 0 := by
    aesop_cat;
  simp_all +decide [ Complex.ext_iff, sq ];
  by_cases hz_im : z.im = 0 <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
  · exact h_contra ( by nlinarith [ sq_nonneg ( z.re + a ) ] );
  · grind

end H3a