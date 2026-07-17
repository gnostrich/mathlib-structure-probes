import Mathlib

open scoped BigOperators Matrix ComplexOrder
open Complex

namespace F3

/-!
# F3. Annihilator has simple unimodular roots (the hard rung)

Let `T` be an `(r+1) × (r+1)` Hermitian PSD Toeplitz matrix `T j k = c (j−k)` whose leading
`r × r` block is positive definite but which is itself singular.  Let `u` be a nonzero null
vector and `P(z) = ∑ k, u k · z^k`.  Then all roots of `P` lie on the unit circle and are simple.

NOTE: This is the classical hard Carathéodory step; its proof requires the Fejér–Riesz /
positivity-on-the-circle structure of PSD Toeplitz extensions, which is not available in
Mathlib.  The statement is recorded faithfully and its proof is left open (`sorry`), as the
batch instructions explicitly permit for this item.  F1 and F2 already lock the atomicity
pipeline conditionally.
-/

variable {r : ℕ}

/-- The `(r+1) × (r+1)` Hermitian Toeplitz matrix `T j k = c (j − k)`. -/
def toeplitz (c : ℤ → ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun j k => c ((j : ℤ) - (k : ℤ))

/-- The leading `r × r` principal block. -/
def leadingBlock (c : ℤ → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun j k => c ((j : ℤ) - (k : ℤ))

/-- The annihilator polynomial `P(z) = ∑ k, u k · z^k`. -/
noncomputable def annihilator (u : Fin (r + 1) → ℂ) : Polynomial ℂ :=
  ∑ k : Fin (r + 1), Polynomial.C (u k) * Polynomial.X ^ (k : ℕ)

/-- All roots of the annihilator lie on the unit circle and are simple. -/
theorem F3_roots (c : ℤ → ℂ)
    (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hPSD : (toeplitz (r := r) c).PosSemidef)
    (hlead : (leadingBlock (r := r) c).PosDef)
    (hsing : (toeplitz (r := r) c).det = 0)
    (u : Fin (r + 1) → ℂ) (hu : u ≠ 0)
    (hnull : (toeplitz (r := r) c).mulVec u = 0) :
    (∀ z ∈ (annihilator u).roots, ‖z‖ = 1) ∧ (annihilator u).roots.Nodup := by
  sorry

end F3
