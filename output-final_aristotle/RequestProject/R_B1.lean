import Mathlib
import RequestProject.R_A6

open scoped BigOperators Matrix
open Horizon

namespace TierR

/-- Rational leading principal submatrix, in the same indexing convention as D6. -/
def leadingSubRat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (k : Fin n) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  A.submatrix (fun i => Fin.castLE (by omega) i) (fun i => Fin.castLE (by omega) i)

/-- R-B1: exact executable Sylvester checker. Symmetry is checked as part of the Boolean,
since positivity of leading minors alone characterizes PD only for symmetric matrices. -/
def checkPDq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  decide (Mᵀ = M ∧ ∀ k : Fin n, 0 < (leadingSubRat M k).det)

@[simp] theorem checkPDq_eq_true {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    checkPDq M = true ↔ Mᵀ = M ∧ ∀ k : Fin n, 0 < (leadingSubRat M k).det := by
  simp [checkPDq]

/-- Casting commutes with taking a leading block. -/
theorem leadingSubRat_cast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (k : Fin n) :
    D6.leadingSub (M.map (Rat.cast : ℚ → ℝ)) k =
      (leadingSubRat M k).map (Rat.cast : ℚ → ℝ) := by
  rfl

/-
Soundness of the executable rational checker.
-/
theorem checkPDq_sound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (h : checkPDq M = true) : IsPDq (M.map (Rat.cast : ℚ → ℝ)) := by
  convert D6.sylvester_reverse n ( M.map Rat.cast ) _ _;
  · grind +suggestions;
  · rw [ checkPDq_eq_true ] at h;
    convert h.2 using 1;
    rw [ leadingSubRat_cast ];
    norm_cast

end TierR