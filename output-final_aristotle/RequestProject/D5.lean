import Mathlib
import RequestProject.Horizon

open scoped BigOperators Matrix
open Horizon

namespace D5

/-!
# D5. Weyl perturbation: certified floors survive certified errors

Let `A, E` be `n × n` real symmetric matrices, `λ_min` the infimum of the Rayleigh quotient
over unit vectors (`Horizon.lambdaMin`).  If `λ_min(A) ≥ δ` and `|xᵀEx| ≤ ε` on all unit
vectors `x`, then `λ_min(A + E) ≥ δ − ε`; consequently if `δ > ε` then `A + E` is positive
definite.  (Symmetry is not needed and is omitted; `NeZero n` is needed so the unit sphere is
nonempty.)
-/

variable {n : ℕ} [NeZero n]

/-
(a) The floor drops by at most the certified error.
-/
theorem D5_a (A E : Matrix (Fin n) (Fin n) ℝ) (δ ε : ℝ)
    (hδ : δ ≤ lambdaMin A)
    (hE : ∀ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) → |quadForm E x| ≤ ε) :
    δ - ε ≤ lambdaMin (A + E) := by
  apply le_lambdaMin;
  intro x hx; rw [ quadForm_add ] ; linarith [ abs_le.mp ( hE x hx ), lambdaMin_le_quadForm A hx ] ;

/-
(b) A positive floor with margin certifies positive definiteness of the perturbed matrix.
-/
theorem D5_b (A E : Matrix (Fin n) (Fin n) ℝ) (δ ε : ℝ)
    (hδ : δ ≤ lambdaMin A)
    (hE : ∀ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) → |quadForm E x| ≤ ε)
    (hlt : ε < δ) :
    IsPDq (A + E) := by
  apply Horizon.IsPDq_of_lambdaMin_pos;
  linarith [ D5_a A E δ ε hδ hE ]

end D5