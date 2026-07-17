import Mathlib
import RequestProject.Horizon
import RequestProject.D6
import RequestProject.E3
import RequestProject.G2
import RequestProject.G4
import RequestProject.G5

open scoped BigOperators Matrix
open Horizon Real

namespace G6

/-!
# G6. Window 4 (5×5) and the joint-binding theorem

`U5 κ u v w x` is the `5 × 5` real symmetric Toeplitz matrix with first row `(κ,u,v,w,x)`.

* (a) Sylvester characterization via the five leading principal minors (reusing D6).  The full
  determinant factors (centrosymmetric split) as `detPlus · detMinus`.
* (b) At the true atoms (`u = atom 2`, `v = atom 3`, `w = atom 5`, `x = atom 7`) with the
  certified enclosures, `κ₀ = 0.921` certifies positive definiteness and `κ₁ = 0.919` fails it.
* (c) Joint-binding theorem: `κ₁ = 0.919` exceeds every single prime atom `(log p)/√p` — anchored
  by the global atom maximum at `p = 7` (G5).
* (d) Threshold growth across windows 2, 3, 4: `0.6 < 0.789 < 0.919`.
-/

/-- The window-4 `5 × 5` symmetric Toeplitz form. -/
def U5 (κ u v w x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![κ, u, v, w, x; u, κ, u, v, w; v, u, κ, u, v; w, v, u, κ, u; x, w, v, u, κ]

/-- The 3×3 (symmetric-block) determinant factor. -/
def detPlus (κ u v w x : ℝ) : ℝ :=
  κ * ((κ + x) * (κ + v) - (u + w) ^ 2) - 2 * v * (v * (κ + v) - u * (u + w))
    + 2 * u * (v * (u + w) - u * (κ + x))

/-- The 2×2 (antisymmetric-block) determinant factor. -/
def detMinus (κ u v w x : ℝ) : ℝ := (κ - x) * (κ - v) - (u - w) ^ 2

/-
Centrosymmetric factorization of the full determinant.
-/
theorem detU5_eq (κ u v w x : ℝ) :
    (U5 κ u v w x).det = detPlus κ u v w x * detMinus κ u v w x := by
  unfold U5; simp +decide [ Matrix.det_succ_row_zero, Matrix.submatrix_apply, Fin.succAbove ] ; ring;
  simp +decide [ Fin.sum_univ_succ, Fin.succAbove ] ; ring!;
  unfold detPlus detMinus; ring;

/-
(a) Sylvester characterization via the five leading principal minors.
-/
theorem G6_a (κ u v w x : ℝ) :
    IsPDq (U5 κ u v w x) ↔
      0 < κ ∧ 0 < κ ^ 2 - u ^ 2
        ∧ 0 < (κ - v) * (κ ^ 2 + κ * v - 2 * u ^ 2)
        ∧ 0 < ((κ + w) * (κ + u) - (u + v) ^ 2) * ((κ - w) * (κ - u) - (u - v) ^ 2)
        ∧ 0 < (U5 κ u v w x).det := by
  convert D6.D6_sylvester ( U5 κ u v w x ) _ using 1;
  · simp +decide [ Fin.forall_fin_succ, D6.leadingSub, U5 ];
    simp +decide [ Matrix.det_succ_row_zero, Fin.sum_univ_succ ];
    simp +decide [ Fin.succAbove ] at *;
    grind;
  · ext i j; fin_cases i <;> fin_cases j <;> rfl;

/-
Helper: the symmetric-block factor `detPlus` is positive across the enclosures (for the
relevant `κ ∈ [0.9, 1]`).
-/
theorem G6_detPlus_pos (κ u v w x : ℝ) (hκ1 : (0.9 : ℝ) ≤ κ) (hκ2 : κ ≤ 1)
    (hu1 : (0.4900 : ℝ) < u) (hu2 : u < 0.4902)
    (hv1 : (0.6342 : ℝ) < v) (hv2 : v < 0.6344) (hw1 : (0.7197 : ℝ) < w) (hw2 : w < 0.7198)
    (hx1 : (0.7354 : ℝ) < x) :
    0 < detPlus κ u v w x := by
  unfold detPlus; ring_nf at *;
  by_contra h_neg;
  nlinarith only [ mul_pos ( sub_pos_of_lt hu1 ) ( sub_pos_of_lt hv1 ), mul_pos ( sub_pos_of_lt hu1 ) ( sub_pos_of_lt hw1 ), mul_pos ( sub_pos_of_lt hu1 ) ( sub_pos_of_lt hx1 ), mul_pos ( sub_pos_of_lt hv1 ) ( sub_pos_of_lt hw1 ), mul_pos ( sub_pos_of_lt hv1 ) ( sub_pos_of_lt hx1 ), mul_pos ( sub_pos_of_lt hw1 ) ( sub_pos_of_lt hx1 ), h_neg, hκ1, hκ2, hu1, hu2, hv1, hv2, hw1, hw2, hx1 ]

/-- (b, positive side) `κ₀ = 0.921` certifies positive definiteness across the enclosures. -/
theorem G6_b_pos (u v w x : ℝ) (hu1 : (0.4900 : ℝ) < u) (hu2 : u < 0.4902)
    (hv1 : (0.6342 : ℝ) < v) (hv2 : v < 0.6344) (hw1 : (0.7197 : ℝ) < w) (hw2 : w < 0.7198)
    (hx1 : (0.7354 : ℝ) < x) (hx2 : x < 0.7356) :
    IsPDq (U5 0.921 u v w x) := by
  rw [G6_a]
  refine ⟨by norm_num, by nlinarith, ?_, ?_, ?_⟩
  · exact mul_pos (by nlinarith) (by nlinarith)
  · exact mul_pos (by nlinarith) (by nlinarith)
  · rw [detU5_eq]
    have hminus : 0 < detMinus 0.921 u v w x := by unfold detMinus; nlinarith
    have hplus : 0 < detPlus 0.921 u v w x :=
      G6_detPlus_pos _ _ _ _ _ (by norm_num) (by norm_num) hu1 hu2 hv1 hv2 hw1 hw2 hx1
    exact mul_pos hplus hminus

/-- (b, negative side) `κ₁ = 0.919` fails positive definiteness across the enclosures. -/
theorem G6_b_neg (u v w x : ℝ) (hu1 : (0.4900 : ℝ) < u) (hu2 : u < 0.4902)
    (hv1 : (0.6342 : ℝ) < v) (hv2 : v < 0.6344) (hw1 : (0.7197 : ℝ) < w) (hw2 : w < 0.7198)
    (hx1 : (0.7354 : ℝ) < x) :
    ¬ IsPDq (U5 0.919 u v w x) := by
  rw [G6_a]
  rintro ⟨_, _, _, _, hdet⟩
  rw [detU5_eq] at hdet
  have hminus : detMinus 0.919 u v w x < 0 := by unfold detMinus; nlinarith
  have hplus : 0 < detPlus 0.919 u v w x :=
    G6_detPlus_pos _ _ _ _ _ (by norm_num) (by norm_num) hu1 hu2 hv1 hv2 hw1 hw2 hx1
  nlinarith [mul_neg_of_pos_of_neg hplus hminus]

/-- Certificate at the true atoms `(log 2)/√2, (log 3)/√3, (log 5)/√5, (log 7)/√7`. -/
theorem G6_cert_pos :
    IsPDq (U5 0.921 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5) (Real.log 7 / Real.sqrt 7)) :=
  G6_b_pos _ _ _ _ E3.E3_atom2.1 E3.E3_atom2.2 E3.E3_atom3.1 E3.E3_atom3.2
    G2.G2_atom5.1 G2.G2_atom5.2 G4.G4_a.1 G4.G4_a.2

/-- Positivity genuinely fails at `κ₁ = 0.919` for the true atoms. -/
theorem G6_cert_neg :
    ¬ IsPDq (U5 0.919 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)
      (Real.log 5 / Real.sqrt 5) (Real.log 7 / Real.sqrt 7)) :=
  G6_b_neg _ _ _ _ E3.E3_atom2.1 E3.E3_atom2.2 E3.E3_atom3.1 E3.E3_atom3.2
    G2.G2_atom5.1 G2.G2_atom5.2 G4.G4_a.1

/-- (c) Joint-binding theorem: the certified threshold `κ₁ = 0.919` exceeds every single prime
atom `(log p)/√p`.  In particular no single prime's atom accounts for the window-4 binding. -/
theorem G6_c (p : ℕ) (hp : p.Prime) : Real.log p / Real.sqrt p < 0.919 := by
  rcases eq_or_ne p 7 with h | h
  · subst h
    have h7 := G4.G4_a.2
    norm_num at h7 ⊢
    linarith
  · have h7 := G4.G4_a.2
    have hlt := G5.G5_c_prime p hp h
    norm_num at h7 ⊢
    linarith

/-- (d) Threshold growth across windows 2 (`κ₁ = 0.6`, E5), 3 (`κ₁ = 0.789`, G3), 4 (`κ₁ = 0.919`). -/
theorem G6_d : (0.6 : ℝ) < 0.789 ∧ (0.789 : ℝ) < 0.919 := by
  constructor <;> norm_num

end G6