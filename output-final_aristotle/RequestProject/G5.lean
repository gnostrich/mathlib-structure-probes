import Mathlib
import RequestProject.E1
import RequestProject.E2
import RequestProject.E3
import RequestProject.G2
import RequestProject.G4

open scoped BigOperators
open Real

namespace G5

/-!
# G5. The p = 7 atom is the global maximum

* (a) `x ↦ (log x)/√x` is strictly decreasing on `[8, ∞)` (derivative
  `(2 − log x)/(2·x^{3/2}) < 0` since `log x > 2` there, `log 8 = 3·log 2 > 2`).
* (b) for every real `x ≥ 11`, `(log x)/√x ≤ (log 11)/√11`.
* (c) for every prime `p ≠ 7`, `(log p)/√p < (log 7)/√7`; stated over all reals `x ≥ 11`
  (`G5_c_large`) together with the finite orderings `atom(2) < atom(3) < atom(5) < atom(7)`.
-/

/-- The weighted-atom function. -/
noncomputable def atom (x : ℝ) : ℝ := Real.log x / Real.sqrt x

/-
(a) `atom` is strictly decreasing on `[8, ∞)`.
-/
theorem G5_a : StrictAntiOn atom (Set.Ici 8) := by
  refine' fun x hx y hy hxy => _;
  -- By the properties of the derivative, we know that $atom'(x) < 0$ for $x > e^2$.
  have h_deriv_neg : ∀ x ∈ Set.Ioi (Real.exp 2), deriv atom x < 0 := by
    intro x hx
    have h_deriv : deriv atom x = (2 - Real.log x) / (2 * x * Real.sqrt x) := by
      convert HasDerivAt.deriv ( HasDerivAt.div ( Real.hasDerivAt_log ( show x ≠ 0 by linarith [ hx.out, Real.exp_pos 2 ] ) ) ( Real.hasDerivAt_sqrt ( show x ≠ 0 by linarith [ hx.out, Real.exp_pos 2 ] ) ) ( ne_of_gt <| Real.sqrt_pos.mpr <| show 0 < x by linarith [ hx.out, Real.exp_pos 2 ] ) ) using 1 ; ring;
      grind;
    exact h_deriv.symm ▸ div_neg_of_neg_of_pos ( by linarith [ Real.log_exp 2, Real.log_lt_log ( by positivity ) hx ] ) ( mul_pos ( mul_pos two_pos ( lt_trans ( by positivity ) hx ) ) ( Real.sqrt_pos.mpr ( lt_trans ( by positivity ) hx ) ) );
  -- Apply the mean value theorem to the interval $[x, y]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv atom c = (atom y - atom x) / (y - x) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact continuousOn_of_forall_continuousAt fun z hz => ContinuousAt.div ( Real.continuousAt_log ( by linarith [ hx.out, hy.out, hz.1 ] ) ) ( Real.continuous_sqrt.continuousAt ) ( ne_of_gt ( Real.sqrt_pos.mpr ( by linarith [ hx.out, hy.out, hz.1 ] ) ) );
    · exact fun z hz => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_lt ( h_deriv_neg z ( show Real.exp 2 < z by exact lt_of_le_of_lt ( show Real.exp 2 ≤ 8 by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 2:ℝ ) = 1+1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ] ) ( by linarith [ hz.1, hx.out ] ) ) ) ) );
  have := h_deriv_neg c ( show c > Real.exp 2 from lt_of_le_of_lt ( show Real.exp 2 ≤ 8 by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show ( 2:ℝ ) = 1+1 by norm_num, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ] ) ( by linarith [ hc.1.1, hx.out ] ) ) ; rw [ hc.2, div_lt_iff₀ ] at this <;> linarith;

/-- (b) For `x ≥ 11`, `atom x ≤ atom 11`. -/
theorem G5_b (x : ℝ) (hx : 11 ≤ x) : atom x ≤ atom 11 := by
  exact G5_a.antitoneOn (by norm_num : (11 : ℝ) ∈ Set.Ici 8)
    (by simp only [Set.mem_Ici]; linarith : x ∈ Set.Ici 8) hx

/-- The finite orderings of the first four atoms. -/
theorem G5_ord :
    Real.log 2 / Real.sqrt 2 < Real.log 3 / Real.sqrt 3 ∧
    Real.log 3 / Real.sqrt 3 < Real.log 5 / Real.sqrt 5 ∧
    Real.log 5 / Real.sqrt 5 < Real.log 7 / Real.sqrt 7 := by
  refine ⟨?_, ?_, ?_⟩
  · calc Real.log 2 / Real.sqrt 2 < 0.4902 := E3.E3_atom2.2
      _ < 0.6342 := by norm_num
      _ < Real.log 3 / Real.sqrt 3 := E3.E3_atom3.1
  · calc Real.log 3 / Real.sqrt 3 < 0.6344 := E3.E3_atom3.2
      _ < 0.7197 := by norm_num
      _ < Real.log 5 / Real.sqrt 5 := G2.G2_atom5.1
  · calc Real.log 5 / Real.sqrt 5 < 0.7198 := G2.G2_atom5.2
      _ < 0.7354 := by norm_num
      _ < Real.log 7 / Real.sqrt 7 := G4.G4_a.1

/-- (c, real form) For every real `x ≥ 11`, `atom x < atom 7 = (log 7)/√7`. -/
theorem G5_c_large (x : ℝ) (hx : 11 ≤ x) : atom x < Real.log 7 / Real.sqrt 7 := by
  have h1 : atom x ≤ atom 11 := G5_b x hx
  have h2 := G4.G4_c
  simp only [atom] at h1 ⊢
  linarith

/-- (c, prime form) For every prime `p ≠ 7`, `(log p)/√p < (log 7)/√7`. -/
theorem G5_c_prime (p : ℕ) (hp : p.Prime) (hp7 : p ≠ 7) :
    Real.log p / Real.sqrt p < Real.log 7 / Real.sqrt 7 := by
  have hord := G5_ord
  rcases lt_or_gt_of_ne hp7 with h | h
  · interval_cases p <;>
      first
        | (exact absurd hp (by decide))
        | (push_cast; linarith [hord.1, hord.2.1, hord.2.2])
  · have hge : 11 ≤ p := by
      by_contra hlt
      push_neg at hlt
      interval_cases p <;> revert hp <;> decide
    have := G5_c_large (p : ℝ) (by exact_mod_cast hge)
    simpa [atom] using this

end G5