import Mathlib

open scoped BigOperators Matrix

/-!
# Horizon: shared definitions for Tier D / Tier E

Self-contained real-quadratic-form notions used by the horizon-positivity items.
For `M : Matrix (Fin n) (Fin n) ℝ` and `x : Fin n → ℝ`, the quadratic form is
`xᵀ M x = ∑ i j, x i * M i j * x j`.
-/

namespace Horizon

variable {n : ℕ}

/-- The quadratic form `xᵀ M x`. -/
def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

/-- `M` is positive semidefinite (quadratic-form definition). -/
def IsPSDq (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ quadForm M x

/-- `M` is positive definite (quadratic-form definition). -/
def IsPDq (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadForm M x

/-- The set of Rayleigh values of `M` over the unit sphere. -/
def valueSet (M : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {r : ℝ | ∃ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) ∧ r = quadForm M x}

/-- The minimal eigenvalue, defined as the infimum of the Rayleigh quotient over unit vectors. -/
noncomputable def lambdaMin (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf (valueSet M)

lemma quadForm_add (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadForm (A + B) x = quadForm A x + quadForm B x := by
  unfold quadForm; simp +decide only [Matrix.add_apply, mul_add] ;
  simp +decide only [add_mul, Finset.sum_add_distrib]

/-
Scaling the vector scales the quadratic form quadratically.
-/
lemma quadForm_smul (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    quadForm M (fun i => c * x i) = c ^ 2 * quadForm M x := by
  unfold quadForm; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring;

/-
The Rayleigh value set is bounded below (elementary entrywise bound).
-/
lemma valueSet_bddBelow (M : Matrix (Fin n) (Fin n) ℝ) : BddBelow (valueSet M) := by
  -- The quadratic form is continuous, and the unit sphere is compact.
  have h_cont : ContinuousOn (fun x : EuclideanSpace ℝ (Fin n) => quadForm M x) (Metric.sphere 0 1) := by
    refine' Continuous.continuousOn _;
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => by exact Continuous.mul ( Continuous.mul ( continuous_apply _ |> Continuous.comp <| continuous_induced_dom ) <| continuous_const ) <| continuous_apply _ |> Continuous.comp <| continuous_induced_dom;
  -- The image of a compact set under a continuous function is also compact.
  have h_compact : IsCompact (Set.image (fun x : EuclideanSpace ℝ (Fin n) => quadForm M x.ofLp) (Metric.sphere 0 1)) := by
    exact IsCompact.image_of_continuousOn ( isCompact_sphere _ _ ) h_cont;
  refine' h_compact.bddBelow.mono _;
  intro x hx; obtain ⟨ y, hy, rfl ⟩ := hx; use EuclideanSpace.equiv ( Fin n ) ℝ |>.symm y; simp_all +decide [ EuclideanSpace.norm_eq ] ;

/-
If `n ≥ 1` the Rayleigh value set is nonempty.
-/
lemma valueSet_nonempty [NeZero n] (M : Matrix (Fin n) (Fin n) ℝ) :
    (valueSet M).Nonempty := by
  exact ⟨ _, ⟨ fun i => if i = 0 then 1 else 0, by aesop, rfl ⟩ ⟩

/-
Every unit-vector value dominates `lambdaMin`.
-/
lemma lambdaMin_le_quadForm (M : Matrix (Fin n) (Fin n) ℝ) {x : Fin n → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) : lambdaMin M ≤ quadForm M x := by
  exact csInf_le ( valueSet_bddBelow M ) ⟨ x, hx, rfl ⟩

/-
A lower bound valid on all unit vectors bounds `lambdaMin` from below.
-/
lemma le_lambdaMin [NeZero n] (M : Matrix (Fin n) (Fin n) ℝ) {c : ℝ}
    (h : ∀ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) → c ≤ quadForm M x) :
    c ≤ lambdaMin M := by
  exact le_csInf ( valueSet_nonempty M ) fun x hx => by rcases hx with ⟨ x, hx₁, rfl ⟩ ; exact h x hx₁;

/-
Positive `lambdaMin` implies positive definiteness.
-/
lemma IsPDq_of_lambdaMin_pos [NeZero n] (M : Matrix (Fin n) (Fin n) ℝ)
    (h : 0 < lambdaMin M) : IsPDq M := by
  intro x hx_nonzero
  set s := ∑ i, x i ^ 2
  have hs_pos : 0 < s := by
    contrapose! hx_nonzero; ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ;
    exact sq_eq_zero_iff.mp ( le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => sq_nonneg ( x i ) ) ( Finset.mem_univ i ) ) hx_nonzero ) ( sq_nonneg ( x i ) ) )
  set u := fun i => x i / Real.sqrt s
  have hu_unit : ∑ i, u i ^ 2 = 1 := by
    simp +zetaDelta at *;
    norm_num [ div_pow, ← Finset.sum_div, hs_pos.le, hs_pos.ne' ]
  have h_quadForm_u : 0 < quadForm M u := by
    exact lt_of_lt_of_le h ( lambdaMin_le_quadForm M hu_unit )
  have h_quadForm_x : quadForm M x = s * quadForm M u := by
    convert quadForm_smul M ( Real.sqrt s ) u using 1;
    · exact congr_arg _ ( funext fun i => by rw [ mul_div_cancel₀ _ ( ne_of_gt ( Real.sqrt_pos.mpr hs_pos ) ) ] );
    · rw [ Real.sq_sqrt hs_pos.le ]
  have h_final : 0 < quadForm M x := by
    exact h_quadForm_x.symm ▸ mul_pos hs_pos h_quadForm_u
  exact h_final

end Horizon