import Mathlib

open scoped BigOperators Matrix

namespace A4

/-!
# A4. Divergence-free antisymmetric flows on K₄ are determined by cycle circulations

The space of antisymmetric divergence-free `4 × 4` real matrices has dimension 3,
and the circulation map to `ℝ³` (here `Fin 3 → ℝ`) is a linear isomorphism.
-/

/-- Antisymmetric, divergence-free `4 × 4` matrices. -/
def W : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := {K | Kᵀ = -K ∧ ∀ i, ∑ j, K i j = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.transpose_add, ha1, hb1, neg_add]
    · intro i; simp only [Matrix.add_apply, Finset.sum_add_distrib, ha2 i, hb2 i, add_zero]
  zero_mem' := by refine ⟨?_, ?_⟩ <;> simp
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.transpose_smul, ha1, smul_neg]
    · intro i; simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, ha2 i, mul_zero]

/-- The circulation map on all matrices. -/
noncomputable def circFull : Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := fun K => ![ K 0 1 + K 1 2 + K 2 0, K 0 1 + K 1 3 + K 3 0, K 0 2 + K 2 3 + K 3 0 ]
  map_add' := by intro a b; funext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro c a; funext i; fin_cases i <;> simp <;> ring

/-- The circulation map restricted to `W`. -/
noncomputable def circ : W →ₗ[ℝ] (Fin 3 → ℝ) := circFull.comp W.subtype

/-- Explicit reconstruction of an antisymmetric divergence-free matrix from circulations. -/
noncomputable def buildK (x : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let a := (x 0 + x 1) / 4
  let b := (x 2 - x 0) / 4
  let e := (x 1 - x 0) / 2 - b
  let c := -a - b
  let d := a - e
  let f := a + b - e
  !![0, a, b, c; -a, 0, d, e; -b, -d, 0, f; -c, -e, -f, 0]

/-
`buildK x` is antisymmetric and divergence-free.
-/
lemma buildK_mem (x : Fin 3 → ℝ) : buildK x ∈ W := by
  unfold buildK W;
  simp +decide [ ← Matrix.ext_iff, Fin.forall_fin_succ ];
  norm_num [ Fin.sum_univ_succ ] ; ring ; norm_num

/-
`buildK` is a right inverse of the circulation map.
-/
lemma circFull_buildK (x : Fin 3 → ℝ) : circFull (buildK x) = x := by
  ext i;
  fin_cases i <;> simp +decide [ circFull, buildK ] <;> ring!

/-
The circulation map is injective on `W`.
-/
lemma circ_injective : Function.Injective circ := by
  -- To show that the circulation map is injective on `W`, we need to show that the only matrix in `W` with zero circulation is the zero matrix.
  have h_zero_circ : ∀ K : W, circ K = 0 → K.1 = 0 := by
    simp +decide [ funext_iff, Fin.forall_fin_succ, circ ];
    unfold circFull W;
    simp +decide [ ← Matrix.ext_iff, Fin.forall_fin_succ ];
    norm_num [ Fin.sum_univ_four ] at * ; intros ; exact ⟨ ⟨ by linarith, by linarith, by linarith, by linarith ⟩, ⟨ by linarith, by linarith, by linarith, by linarith ⟩, ⟨ by linarith, by linarith, by linarith, by linarith ⟩, by linarith, by linarith, by linarith, by linarith ⟩ ;
  intro K L hKL; specialize h_zero_circ ( K - L ) ; simp_all +decide [ sub_eq_zero ] ;

theorem A4_main : Module.finrank ℝ W = 3 ∧ Function.Bijective circ := by
  have hsurj : Function.Surjective circ := by
    intro x
    refine ⟨⟨buildK x, buildK_mem x⟩, ?_⟩
    show circFull (buildK x) = x
    exact circFull_buildK x
  refine ⟨?_, circ_injective, hsurj⟩
  have e : W ≃ₗ[ℝ] (Fin 3 → ℝ) := LinearEquiv.ofBijective circ ⟨circ_injective, hsurj⟩
  simpa using e.finrank_eq

end A4