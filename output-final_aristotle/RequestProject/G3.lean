import Mathlib
import RequestProject.Horizon
import RequestProject.E3
import RequestProject.G2
import RequestProject.D6

open scoped BigOperators Matrix
open Horizon Real

namespace G3

/-!
# G3. Third horizon window and the newest-binds test

`U(κ,u,v,w)` is the `4 × 4` real symmetric Toeplitz matrix with first row `(κ,u,v,w)`
(diagonal `κ`, distance-1 coupling `u = p=2 atom`, distance-2 coupling `v = p=3 atom`,
distance-3 coupling `w = p=5 atom`).

* (a) Sylvester characterization via the four leading principal minors.
* (b) At the true atoms (`0.4900 < u < 0.4902`, `0.6342 < v < 0.6344`, `0.7197 < w < 0.7198`):
  `κ₀ = 0.790` certifies positive definiteness, and `κ₁ = 0.789` fails it, for all such `u,v,w`.
* (c) NEWEST-BINDS TEST: `κ₁ = 0.789 ≥ 0.7198` — the threshold lies strictly above the newest
  atom's enclosure, so the window binds *jointly*, not by the newest prime alone.
-/

/-- The third-window `4 × 4` form. -/
def U (κ u v w : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![κ, u, v, w; u, κ, u, v; v, u, κ, u; w, v, u, κ]

/-
Closed factored form of the fourth leading principal minor `det U`.
-/
theorem detU_eq (κ u v w : ℝ) :
    (U κ u v w).det = ((κ + w) * (κ + u) - (u + v) ^ 2) * ((κ - w) * (κ - u) - (u - v) ^ 2) := by
  unfold U; norm_num [ Fin.sum_univ_succ, Matrix.det_succ_row_zero ] ; ring;
  simp +decide [ Fin.succAbove ] ; ring!

/-
(a) Sylvester criterion for the four-site form via its four leading principal minors.
-/
theorem G3_a (κ u v w : ℝ) :
    IsPDq (U κ u v w) ↔
      0 < κ ∧ 0 < κ ^ 2 - u ^ 2 ∧ 0 < (κ - v) * (κ ^ 2 + κ * v - 2 * u ^ 2)
        ∧ 0 < (U κ u v w).det := by
  rw [ D6.D6_sylvester ];
  · norm_num [ Fin.forall_fin_succ, D6.leadingSub, U ];
    simp +decide [ Matrix.det_succ_row_zero, Fin.sum_univ_succ ];
    grind;
  · ext i j; fin_cases i <;> fin_cases j <;> rfl;

/-
(b, positive side) `κ₀ = 0.790` certifies positive definiteness across the enclosures.
-/
theorem G3_b_pos (u v w : ℝ) (hu1 : (0.4900 : ℝ) < u) (hu2 : u < 0.4902)
    (hv1 : (0.6342 : ℝ) < v) (hv2 : v < 0.6344) (hw1 : (0.7197 : ℝ) < w) (hw2 : w < 0.7198) :
    IsPDq (U 0.790 u v w) := by
  refine' G3_a _ _ _ _ |>.2 ⟨ _, _, _, _ ⟩ <;> norm_num at *;
  · nlinarith;
  · exact mul_pos ( by linarith ) ( by nlinarith );
  · rw [ detU_eq ];
    exact mul_pos ( by nlinarith ) ( by nlinarith )

/-
(b, negative side) `κ₁ = 0.789` fails positive definiteness across the enclosures.
-/
theorem G3_b_neg (u v w : ℝ) (hu1 : (0.4900 : ℝ) < u) (hu2 : u < 0.4902)
    (hv1 : (0.6342 : ℝ) < v) (hv2 : v < 0.6344) (hw1 : (0.7197 : ℝ) < w) (hw2 : w < 0.7198) :
    ¬ IsPDq (U 0.789 u v w) := by
  rw [ G3_a ];
  norm_num [ detU_eq ];
  exact fun _ _ => mul_nonpos_of_nonneg_of_nonpos ( by nlinarith ) ( by nlinarith )

/-- Certificate at the true atoms `(log 2)/√2, (log 3)/√3, (log 5)/√5`. -/
theorem G3_cert_pos :
    IsPDq (U 0.790 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5)) :=
  G3_b_pos _ _ _ E3.E3_atom2.1 E3.E3_atom2.2 E3.E3_atom3.1 E3.E3_atom3.2 G2.G2_atom5.1 G2.G2_atom5.2

/-- Positivity genuinely fails at `κ₁ = 0.789` for the true atoms. -/
theorem G3_cert_neg :
    ¬ IsPDq (U 0.789 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5)) :=
  G3_b_neg _ _ _ E3.E3_atom2.1 E3.E3_atom2.2 E3.E3_atom3.1 E3.E3_atom3.2 G2.G2_atom5.1 G2.G2_atom5.2

/-- (c) NEWEST-BINDS TEST.  The certified failure threshold `κ₁ = 0.789` lies strictly above the
newest atom's upper enclosure `0.7198`, and the certified positive threshold `κ₀ = 0.790` lies
strictly above `0.7197`: the window binds *jointly*, not by the newest prime alone. -/
theorem G3_newest_binds : (0.7198 : ℝ) ≤ 0.789 ∧ (0.7197 : ℝ) < 0.790 := by
  constructor <;> norm_num

end G3