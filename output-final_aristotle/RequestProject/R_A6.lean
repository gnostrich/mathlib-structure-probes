import Mathlib
import RequestProject.R_A5
import RequestProject.V5_5

open scoped BigOperators Matrix
open Horizon

set_option maxHeartbeats 4000000

namespace TierR

/-
The first diagonal kernel value is positive, extracted from the audited `M3` certificate.
-/
theorem M3_first_pos : 0 < V5_5.M3 0 0 := by
  convert V5_5.true_kernel_grid_posdef ( fun i => if i = 0 then 1 else 0 ) _ using 1 ; norm_num [ quadForm ];
  exact fun h => by simpa using congr_fun h 0;

noncomputable def gridState1 : GramState :=
  GramState.singleton (V5_5.M3 0 0) M3_first_pos

noncomputable def gridB1 : Fin gridState1.dim → ℝ := fun i =>
  V5_5.M3 ⟨i.val, by simpa [gridState1] using i.isLt⟩ 1
noncomputable def gridD1 : ℝ := V5_5.M3 1 1

/-
First audited Schur gate.
-/
theorem gridGate1 : 0 < schur gridState1.M gridB1 gridD1 := by
  convert border_pd_schur_pos gridState1.M gridState1.hsymm gridB1 gridD1 _;
  intro x hx; simp_all +decide [ IsPDq, border ] ;
  convert V5_5.true_kernel_grid_posdef ( fun i => if h : i.val < 2 then x ⟨ i.val, h ⟩ else 0 ) _ using 1;
  · unfold gridState1 gridB1 gridD1 V5_5.M3; simp +decide [ Fin.sum_univ_succ, quadForm ] ;
    unfold border; simp +decide [ Fin.sum_univ_succ, GramState.singleton ] ;
    exact Or.inl <| Or.inl <| V5_1.G_symm _ _;
  · contrapose! hx; ext i; fin_cases i <;> simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;

noncomputable def gridState2 : GramState := gridState1.expand gridB1 gridD1 gridGate1

@[simp] theorem gridState2_dim : gridState2.dim = 2 := rfl

noncomputable def gridB2 : Fin gridState2.dim → ℝ := fun i =>
  V5_5.M3 ⟨i.val, lt_trans i.isLt (by rw [gridState2_dim]; omega)⟩ 2
noncomputable def gridD2 : ℝ := V5_5.M3 2 2

/-
Second audited Schur gate.
-/
theorem gridGate2 : 0 < schur gridState2.M gridB2 gridD2 := by
  convert border_pd_schur_pos gridState2.M gridState2.hsymm gridB2 gridD2 _;
  intro x hx
  simp_all +decide [ IsPDq, border ];
  convert V5_5.true_kernel_grid_posdef ( fun i => if h : i.val < 3 then x ⟨ i.val, h ⟩ else 0 ) _ using 1;
  · unfold gridState2 gridB2 gridD2 V5_5.M3; simp +decide [ Fin.sum_univ_succ, quadForm ] ;
    unfold border; simp +decide [ Fin.sum_univ_succ, GramState.expand ] ;
    unfold gridState1 gridB1 gridD1 border; simp +decide [ Fin.sum_univ_succ, GramState.singleton ] ;
    unfold V5_5.M3; simp +decide [ Fin.sum_univ_succ, quadForm ] ;
    unfold V5_1.G; ring;
    unfold V5_1.Psi; norm_num [ abs_of_nonneg ] ; ring;
  · contrapose! hx; ext i; fin_cases i <;> simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;

/-- R-A6: the literal singleton/expand/expand reconstruction. -/
noncomputable def trueKernelGridState : GramState :=
  gridState2.expand gridB2 gridD2 gridGate2

/-
The two expansion steps reproduce the audited true kernel matrix exactly.
-/
theorem trueKernelGridState_matrix : trueKernelGridState.M = V5_5.M3 := by
  ext i j;
  fin_cases i <;> fin_cases j <;> simp +decide [ trueKernelGridState, gridState2, gridState1, gridB1, gridB2, gridD1, gridD2, GramState.expand, GramState.singleton, border ]; all_goals exact V5_1.G_symm _ _

/-- Entrance exam: a state obtained purely by singleton then two expansions has dimension three
and, after the dimension equality's dependent transport, matrix `M3`. -/
theorem exists_expanded_true_kernel_state :
    ∃ G : GramState, G.dim = 3 ∧ HEq G.M V5_5.M3 := by
  refine ⟨trueKernelGridState, rfl, ?_⟩
  exact heq_of_eq trueKernelGridState_matrix

/-- The carried certificate and the v5 audited certificate both prove the same claim. -/
theorem trueKernelGridState_certificates :
    IsPDq trueKernelGridState.M ∧ IsPDq V5_5.M3 :=
  ⟨trueKernelGridState.hpd, V5_5.true_kernel_grid_posdef⟩

end TierR