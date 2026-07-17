import Mathlib
import RequestProject.R_A1

open scoped BigOperators Matrix
open Horizon

set_option maxHeartbeats 4000000

namespace TierR

/-
Positive definiteness gives a strictly positive Rayleigh floor in nonzero dimension.
-/
theorem lambdaMin_pos_of_isPDq {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℝ) (hPD : IsPDq M) : 0 < lambdaMin M := by
  -- By definition of IsPDq, for any non-zero vector x, the quadratic form x^T M x is positive.
  have h_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadForm M x := by
    exact hPD;
  -- By definition of $IsPDq$, there exists a constant $c > 0$ such that for all $x$ with $\|x\| = 1$, we have $x^T M x \geq c$.
  obtain ⟨c, hc_pos, hc⟩ : ∃ c > 0, ∀ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) → c ≤ quadForm M x := by
    have h_compact : IsCompact {x : Fin n → ℝ | (∑ i, x i ^ 2 = 1)} := by
      refine' ( Metric.isCompact_iff_isClosed_bounded.mpr _ );
      exact ⟨ isClosed_eq ( continuous_finset_sum _ fun _ _ => Continuous.pow ( continuous_apply _ ) _ ) continuous_const, isBounded_iff_forall_norm_le.mpr ⟨ 1, by rintro x ( hx : ∑ i, x i ^ 2 = 1 ) ; exact pi_norm_le_iff_of_nonneg ( by norm_num ) |>.2 fun i => by simpa [ hx ] using Real.abs_le_sqrt ( Finset.single_le_sum ( fun i _ => sq_nonneg ( x i ) ) ( Finset.mem_univ i ) ) ⟩ ⟩;
    obtain ⟨ c, hc ⟩ := h_compact.exists_isMinOn ⟨ fun _ => 1 / Real.sqrt n, by norm_num [ NeZero.ne, Real.sq_sqrt ] ⟩ ( show ContinuousOn ( fun x : Fin n → ℝ => quadForm M x ) { x : Fin n → ℝ | ∑ i, x i ^ 2 = 1 } from Continuous.continuousOn <| by { unfold quadForm; continuity } );
    exact ⟨ quadForm M c, h_pos c ( by rintro rfl; norm_num at hc ), fun x hx => hc.2 hx ⟩;
  exact lt_of_lt_of_le hc_pos ( le_lambdaMin M hc )

/-- R-A2: a finite Gram matrix together with its symmetry and PD certificate.
The dimension is part of the state through the dependent matrix field. -/
structure GramState where
  dim : ℕ
  M : Matrix (Fin dim) (Fin dim) ℝ
  hsymm : Mᵀ = M
  hpd : IsPDq M
  nonempty : NeZero dim

namespace GramState

/-- A positive `1×1` certified state. -/
def singleton (a : ℝ) (ha : 0 < a) : GramState where
  dim := 1
  M := ![![a]]
  hsymm := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  hpd := by
    intro x hx
    simp [quadForm, Fin.sum_univ_succ]
    have : x 0 ≠ 0 := by
      intro h
      apply hx
      funext i
      fin_cases i
      exact h
    nlinarith [sq_pos_of_ne_zero this]
  nonempty := inferInstance

instance (G : GramState) : NeZero G.dim := G.nonempty

/-- A canonical certified positive lower floor: half the least Rayleigh value. -/
noncomputable def margin (G : GramState) : ℝ := lambdaMin G.M / 2

theorem margin_pos (G : GramState) : 0 < G.margin := by
  exact div_pos ( lambdaMin_pos_of_isPDq G.M G.hpd ) zero_lt_two

/-
The state's margin is a certified floor below its least Rayleigh value.
-/
theorem margin_le (G : GramState) : G.margin ≤ lambdaMin G.M := by
  exact div_le_self ( le_of_lt ( lambdaMin_pos_of_isPDq G.M G.hpd ) ) ( by norm_num )

end GramState
end TierR