import Mathlib

open scoped BigOperators Matrix ComplexOrder
open Complex

namespace D4

/-!
# D4. Carathéodory–Toeplitz: positive Toeplitz = atomic (the trigonometric Kronecker)

Let `c : ℤ → ℂ` satisfy `c (-m) = conj (c m)`, and let `T` be the `(n+1) × (n+1)` Hermitian
Toeplitz matrix `T j k = c (j - k)`.  If `T` is positive semidefinite with rank `r ≤ n`, then
there are `r` real frequencies `θ_s` and `r` strictly positive weights `ρ_s` with
`c m = ∑ s, ρ_s · exp(i · m · θ_s)` for all `|m| ≤ n`.

NOTE: This is the Carathéodory–Fejér theorem.  Its usual proof relies on the fact that the
kernel polynomial of a rank-deficient positive-semidefinite Toeplitz matrix has all of its
roots on the unit circle (a Fejér–Riesz / positivity-on-the-circle argument), plus Vandermonde
inversion for the weights.  This supporting machinery is not available in Mathlib, so the
statement is recorded faithfully but its proof is left open (`sorry`).  Every other item in
Tiers D and E is fully proved. -/

variable {n : ℕ}

/-- The Hermitian Toeplitz matrix `T j k = c (j - k)`. -/
def toeplitz (c : ℤ → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun j k => c ((j : ℤ) - (k : ℤ))

/-- Carathéodory–Fejér representation. -/
theorem D4_caratheodory (c : ℤ → ℂ)
    (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hPSD : (toeplitz (n := n) c).PosSemidef)
    (r : ℕ) (hr : (toeplitz (n := n) c).rank = r) (hrn : r ≤ n) :
    ∃ (θ : Fin r → ℝ) (ρ : Fin r → ℝ), (∀ s, 0 < ρ s) ∧
      ∀ m : ℤ, |m| ≤ (n : ℤ) →
        c m = ∑ s, (ρ s : ℂ) * Complex.exp ((m : ℂ) * (θ s : ℂ) * Complex.I) := by
  sorry

end D4
