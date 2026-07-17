import Mathlib
import RequestProject.Horizon
import RequestProject.E3

open scoped BigOperators Matrix
open Horizon Real

namespace E4

/-!
# E4. First horizon window certificate (archimedean + p = 2)

`W(κ, w) = [[κ, -w], [-w, κ]]`.  (a) `W(κ,w)` is PSD iff `κ ≥ |w|`.  (b) With
`w = (log 2)/√2` (enclosed by `0.4900 < w < 0.4902`): every rational `κ ≥ 0.4902` gives a PSD
matrix, and every rational `κ < 0.49` does not.
-/

/-- The first-window `2 × 2` form. -/
def W (κ w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![κ, -w; -w, κ]

/-
(a) PSD threshold: `W(κ,w)` is PSD iff `κ ≥ |w|`.
-/
theorem E4_a (κ w : ℝ) : IsPSDq (W κ w) ↔ |w| ≤ κ := by
  constructor;
  · intro h;
    have := h ( fun i => if i = 0 then 1 else 1 ) ; ( have := h ( fun i => if i = 0 then 1 else -1 ) ; ( norm_num [ Fin.sum_univ_succ, quadForm, W ] at * ; cases abs_cases w <;> nlinarith; ) );
  · intro h x; simp +decide [ W, quadForm ] ; ring_nf;
    cases abs_cases w <;> nlinarith [ sq_nonneg ( x 0 - x 1 ), sq_nonneg ( x 0 + x 1 ) ]

/-
(b, positive side) Any rational `κ ≥ 0.4902` certifies positivity at the first horizon.
-/
theorem E4_b_pos (κ : ℚ) (hκ : (0.4902 : ℚ) ≤ κ) :
    IsPSDq (W (κ : ℝ) (Real.log 2 / Real.sqrt 2)) := by
  refine' fun x => _;
  convert E4_a ( κ : ℝ ) ( Real.log 2 / Real.sqrt 2 ) |>.2 _ x using 1;
  rw [ abs_of_nonneg ( by positivity ) ];
  exact le_trans ( by have := E3.E3_atom2; norm_num1 at *; linarith ) ( Rat.cast_le.mpr hκ )

/-
(b, negative side) Any rational `κ < 0.49` fails positivity at the first horizon.
-/
theorem E4_b_neg (κ : ℚ) (hκ : κ < (0.49 : ℚ)) :
    ¬ IsPSDq (W (κ : ℝ) (Real.log 2 / Real.sqrt 2)) := by
  rw [ E4_a ];
  rw [ abs_of_nonneg ];
  · exact not_le_of_gt ( lt_of_lt_of_le ( by exact lt_of_lt_of_le ( Rat.cast_lt.mpr hκ ) ( by norm_num ) ) ( E3.E3_atom2.1.le ) );
  · positivity

end E4