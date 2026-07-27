import RequestProject.C3Base

open scoped BigOperators

namespace C3

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable (μ : X → ℝ) (ν : Y → ℝ)

/-
The independent coupling is feasible: shows the polytope is nonempty.
-/
lemma feasible_indep (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hμs : ∑ x, μ x = 1) (hνs : ∑ y, ν y = 1) :
    feasible μ ν (fun p => μ p.1 * ν p.2) := by
  refine' ⟨ fun p => mul_nonneg ( hμ p.1 ) ( hν p.2 ), _, _ ⟩ <;> simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ]

/-
The feasible set is compact.
-/
lemma feasible_isCompact (hμ : ∀ x, 0 ≤ μ x) (hμs : ∑ x, μ x = 1) :
    IsCompact {π : X × Y → ℝ | feasible μ ν π} := by
  refine' CompactIccSpace.isCompact_Icc.of_isClosed_subset _ _;
  exact 0;
  exact fun p => ∑ x, μ x;
  · unfold feasible;
    simp +decide only [Set.setOf_and, Set.setOf_forall];
    exact IsClosed.inter ( isClosed_iInter fun _ => isClosed_le continuous_const <| continuous_apply _ ) ( IsClosed.inter ( isClosed_iInter fun _ => isClosed_eq ( continuous_finset_sum _ fun _ _ => continuous_apply _ ) <| continuous_const ) ( isClosed_iInter fun _ => isClosed_eq ( continuous_finset_sum _ fun _ _ => continuous_apply _ ) <| continuous_const ) );
  · intro π hπ
    obtain ⟨h_nonneg, h_sum_x, h_sum_y⟩ := hπ
    exact ⟨fun p => h_nonneg p, fun p => by
      exact le_trans ( Finset.single_le_sum ( fun y _ => h_nonneg ( p.1, y ) ) ( Finset.mem_univ p.2 ) ) ( h_sum_x p.1 ▸ Finset.single_le_sum ( fun x _ => hμ x ) ( Finset.mem_univ p.1 ) )⟩

/-
The feasible set is convex.
-/
lemma feasible_convex : Convex ℝ {π : X × Y → ℝ | feasible μ ν π} := by
  intro x hx y hy a b ha hb hab; simp_all +decide [ feasible ];
  simp_all +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  exact ⟨ fun i j => add_nonneg ( mul_nonneg ha ( hx.1 i j ) ) ( mul_nonneg hb ( hy.1 i j ) ), fun i => by rw [ ← add_mul, hab, one_mul ], fun j => by rw [ ← add_mul, hab, one_mul ] ⟩

end C3