import Mathlib

open scoped BigOperators

namespace J3

/-!
# J3. One-prime purity ⟺ half-line

The complex zeros of `s ↦ 1 − c·exp(−s·L)` (with `c, L > 0`) are exactly
`{ (log c)/L + (2π k / L)·i : k ∈ ℤ }`; every zero has real part `(log c)/L`, which equals
`1/2` iff `c = exp(L/2)`.
-/

/-
The zero set of the single Euler factor.
-/
theorem J3_zeros (c L : ℝ) (hc : 0 < c) (hL : 0 < L) (s : ℂ) :
    (1 - (c : ℂ) * Complex.exp (-s * (L : ℂ)) = 0) ↔
      ∃ k : ℤ, s = ((Real.log c / L : ℝ) : ℂ)
        + ((2 * Real.pi * (k : ℝ) / L : ℝ) : ℂ) * Complex.I := by
  -- Apply the exponential property to rewrite the equation.
  suffices h_exp : Complex.exp (-s * L) = Complex.exp (-(Real.log c : ℂ)) ↔ ∃ k : ℤ, -s * L = -(Real.log c : ℂ) + k * (2 * Real.pi * Complex.I) by
    convert h_exp using 1;
    · norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Real.exp_neg, Real.exp_log hc ];
      grind;
    · constructor <;> rintro ⟨ k, hk ⟩ <;> use -k <;> push_cast at * <;> ring_nf at * <;> simp_all +decide [ Complex.ext_iff, hL.ne' ]; all_goals grind;
  rw [ Complex.exp_eq_exp_iff_exists_int ]

/-
Every zero has real part `(log c)/L`.
-/
theorem J3_re (c L : ℝ) (hc : 0 < c) (hL : 0 < L) (s : ℂ)
    (hs : 1 - (c : ℂ) * Complex.exp (-s * (L : ℂ)) = 0) :
    s.re = Real.log c / L := by
  obtain ⟨ k, hk ⟩ := J3_zeros c L hc hL s |>.1 hs;
  aesop

/-
The common real part equals `1/2` iff `c = exp(L/2)`.
-/
theorem J3_half (c L : ℝ) (hc : 0 < c) (hL : 0 < L) :
    Real.log c / L = 1 / 2 ↔ c = Real.exp (L / 2) := by
  constructor <;> intro h <;> rw [ div_eq_iff ( ne_of_gt hL ) ] at *;
  · rw [ ← Real.exp_log hc, h, mul_comm ] ; ring;
  · rw [ h, Real.log_exp ] ; ring

end J3