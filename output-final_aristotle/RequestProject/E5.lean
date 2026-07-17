import Mathlib
import RequestProject.Horizon
import RequestProject.E3

open scoped BigOperators Matrix
open Horizon Real

namespace E5

/-!
# E5. Second window: three-site certificate (p = 2 and p = 3 both inside)

`V(κ, u, v) = [[κ, u, v], [u, κ, u], [v, u, κ]]`.

* (a) By Sylvester's criterion, `V` is positive definite iff `κ > 0`, `u² < κ²`, and
  `(κ − v)(κ² + κv − 2u²) > 0`.
* (b) With `0.4900 < u < 0.4902` and `0.6342 < v < 0.6344`: `κ₀ = 0.635` certifies positive
  definiteness for all such `u, v`, while `κ₁ = 0.6` fails for all such `u, v`.  (`0.634` fails
  because `v` may exceed it, so `0.635` is the smallest three-decimal certificate.)

The original prompt used the enclosure `0.6343 < v < 0.6344` for `v = (log 3)/√3`, but the true
value is `≈ 0.634284 < 0.6343`; the correct provable enclosure (from `E3.E3_atom3`) is
`0.6342 < v < 0.6344`, which is used here.  The certificate choices `κ₀ = 0.635`, `κ₁ = 0.6`
are unchanged.
-/

/-- The second-window `3 × 3` form. -/
def V (κ u v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![κ, u, v; u, κ, u; v, u, κ]

/-
(a) Sylvester criterion for the three-site form.
-/
theorem E5_a (κ u v : ℝ) :
    IsPDq (V κ u v) ↔ 0 < κ ∧ u ^ 2 < κ ^ 2 ∧ 0 < (κ - v) * (κ ^ 2 + κ * v - 2 * u ^ 2) := by
  constructor <;> intro h;
  · -- Apply PD to x = ![1,0,0] to get κ>0.
    have hκ : 0 < κ := by
      have := h ( fun i => if i = 0 then 1 else 0 ) ; simp_all +decide [ quadForm ] ;
      exact this ( by intros h; simpa using congr_fun h 0 )

    -- Apply PD to x = ![1,1,0] and ![1,-1,0] to get κ>|u|, hence u^2<κ^2.
    have hu : u^2 < κ^2 := by
      have := h ( fun i => if i = 1 then 1 else if i = 0 then -u / κ else 0 ) ; simp_all +decide [ Fin.sum_univ_three ];
      simp_all +decide [ funext_iff, Fin.forall_fin_succ, quadForm ];
      simp_all +decide [ Fin.sum_univ_three, V ];
      nlinarith [ mul_div_cancel₀ ( -u ) hκ.ne' ]

    -- PD implies det>0; since V is symmetric and PD (in the quadratic-form sense), its determinant is positive.
    have h_det : 0 < (κ - v) * (κ^2 + κ * v - 2 * u^2) := by
      have h_det : Matrix.det (V κ u v) > 0 := by
        convert Matrix.PosDef.det_pos _;
        constructor;
        · ext i j; fin_cases i <;> fin_cases j <;> rfl;
        · intro x hx; convert h ( fun i => x i ) _ using 1; simp +decide [ Finsupp.sum_fintype, hx ] ;
          · rfl;
          · exact fun h => hx <| Finsupp.ext fun i => by simpa using congr_fun h i;
      convert h_det.lt using 1 ; norm_num [ Matrix.det_fin_three ] ; ring!;

    exact ⟨hκ, hu, h_det⟩;
  · intro x hx_ne_zero
    have h_pos : 0 < κ * (x 0 + (u * x 1 + v * x 2) / κ) ^ 2 + (κ ^ 2 - u ^ 2) / κ * (x 1 + (u * (κ - v) / (κ ^ 2 - u ^ 2)) * x 2) ^ 2 + (κ * (κ - v) * (κ ^ 2 + κ * v - 2 * u ^ 2)) / (κ ^ 2 - u ^ 2) / κ * (x 2) ^ 2 := by
      by_cases hx2 : x 2 = 0;
      · by_cases hx1 : x 1 = 0 <;> simp_all +decide [ ne_of_gt ];
        · exact sq_pos_of_ne_zero ( show x 0 ≠ 0 from fun h0 => hx_ne_zero <| by ext i; fin_cases i <;> aesop );
        · exact add_pos_of_nonneg_of_pos ( mul_nonneg h.1.le ( sq_nonneg _ ) ) ( mul_pos ( div_pos ( by nlinarith ) h.1 ) ( sq_pos_of_ne_zero hx1 ) );
      · refine' add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg h.1.le ( sq_nonneg _ ) ) ( mul_nonneg ( div_nonneg ( by nlinarith ) h.1.le ) ( sq_nonneg _ ) ) ) ( mul_pos ( div_pos ( div_pos ( by nlinarith ) ( by nlinarith ) ) h.1 ) ( sq_pos_of_ne_zero hx2 ) );
    convert h_pos using 1;
    unfold quadForm V;
    norm_num [ Fin.sum_univ_succ, Fin.sum_univ_zero ];
    grind

/-
(b, positive side) `κ₀ = 0.635` certifies positive definiteness across the enclosures.
-/
theorem E5_b_pos (u v : ℝ) (hu1 : (0.4900 : ℝ) < u) (hu2 : u < 0.4902)
    (hv1 : (0.6342 : ℝ) < v) (hv2 : v < 0.6344) :
    IsPDq (V 0.635 u v) := by
  rw [ E5_a ];
  exact ⟨ by norm_num, by norm_num1 at *; nlinarith, by norm_num1 at *; nlinarith ⟩

/-
(b, negative side) `κ₁ = 0.6` fails positive definiteness across the enclosures.
-/
theorem E5_b_neg (u v : ℝ) (hu1 : (0.4900 : ℝ) < u) (hu2 : u < 0.4902)
    (hv1 : (0.6342 : ℝ) < v) (hv2 : v < 0.6344) :
    ¬ IsPDq (V 0.6 u v) := by
  convert E5_a 0.6 u v |>.not.mpr _ using 1;
  exact fun h => by nlinarith;

/-- The concrete second-horizon certificate at the true atoms `(log 2)/√2`, `(log 3)/√3`. -/
theorem E5_cert_pos :
    IsPDq (V 0.635 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)) :=
  E5_b_pos _ _ E3.E3_atom2.1 E3.E3_atom2.2 E3.E3_atom3.1 E3.E3_atom3.2

/-- Positivity genuinely fails at `κ₁ = 0.6` for the true atoms. -/
theorem E5_cert_neg :
    ¬ IsPDq (V 0.6 (Real.log 2 / Real.sqrt 2) (Real.log 3 / Real.sqrt 3)) :=
  E5_b_neg _ _ E3.E3_atom2.1 E3.E3_atom2.2 E3.E3_atom3.1 E3.E3_atom3.2

end E5