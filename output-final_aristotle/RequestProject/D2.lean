import Mathlib

open scoped BigOperators Matrix

-- Some proofs in this file (expansion of the double-sum bilinear form) are
-- computationally heavy; raise the elaboration budget accordingly.
set_option maxHeartbeats 1600000

namespace D2

/-!
# D2. Finite Osterwalder–Schrader: reflection positivity builds the transfer operator

`M` is a `(2n) × (2n)` real symmetric PSD matrix, indices encoded as `Fin n ⊕ Fin n`
(`Sum.inl` = negative/reflected side `{-n,…,-1}`, `Sum.inr` = positive side `{1,…,n}`).
The reflection `θ(i) = -i` pairs the reflected positive side against the positive side; the
reflected pairing is `⟨f,g⟩_θ = ∑ i j, f i · M(inl i, inr j) · g j`.

Under reflection positivity (`⟨f,f⟩_θ ≥ 0`) and the block symmetry
`M(inl i, inr j) = M(inl j, inr i)`:

* (a) `⟨·,·⟩_θ` is a symmetric PSD bilinear form;
* (b) the null vectors form a linear subspace and the form descends to a positive definite
  inner product on the quotient.

`M`'s global symmetry and PSD-ness are stated in the original problem but are not needed
(only reflection positivity of the block is used); they are omitted.
-/

variable {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)

/-- The reflected pairing `⟨f,g⟩_θ`. -/
def thetaForm (f g : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, f i * M (Sum.inl i) (Sum.inr j) * g j

/-
Cauchy–Schwarz for the PSD form: a null vector pairs to zero with everything.
-/
lemma thetaForm_cs
    (hsym : ∀ i j, M (Sum.inl i) (Sum.inr j) = M (Sum.inl j) (Sum.inr i))
    (hRP : ∀ f : Fin n → ℝ, 0 ≤ thetaForm M f f)
    (f g : Fin n → ℝ) (hf : thetaForm M f f = 0) :
    thetaForm M f g = 0 := by
  -- By definition of `thetaForm`, we can expand `(f + t • g)`.
  have h_expand (t : ℝ) : (thetaForm M (f + t • g) (f + t • g)) = (thetaForm M f f) + 2 * t * (thetaForm M f g) + t^2 * (thetaForm M g g) := by
    unfold thetaForm; simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, add_mul, mul_add, sq ] ; ring;
    simp +decide [ mul_two, add_comm, add_left_comm, add_assoc, Finset.sum_add_distrib ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ hsym ] );
  by_contra h_nonzero;
  -- Choose $t$ such that $t = -\frac{\thetaForm M f g}{\thetaForm M g g + 1}$.
  set t := -thetaForm M f g / (thetaForm M g g + 1) with ht_def;
  exact h_nonzero ( by nlinarith [ hRP ( f + t • g ), h_expand t, mul_div_cancel₀ ( -thetaForm M f g ) ( show thetaForm M g g + 1 ≠ 0 from by linarith [ hRP g ] ), hRP g ] )

/-
(a) The reflected pairing is a symmetric positive semidefinite bilinear form.
-/
theorem D2_a
    (hsym : ∀ i j, M (Sum.inl i) (Sum.inr j) = M (Sum.inl j) (Sum.inr i))
    (hRP : ∀ f : Fin n → ℝ, 0 ≤ thetaForm M f f) :
    (∀ f g : Fin n → ℝ, thetaForm M f g = thetaForm M g f) ∧
      (∀ f : Fin n → ℝ, 0 ≤ thetaForm M f f) := by
  refine' ⟨ fun f g => _, hRP ⟩;
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ hsym ] ; ring )

/-
(b1) The null vectors form a linear subspace.
-/
theorem D2_b_subspace
    (hsym : ∀ i j, M (Sum.inl i) (Sum.inr j) = M (Sum.inl j) (Sum.inr i))
    (hRP : ∀ f : Fin n → ℝ, 0 ≤ thetaForm M f f) :
    thetaForm M (0 : Fin n → ℝ) 0 = 0 ∧
      (∀ f g : Fin n → ℝ, thetaForm M f f = 0 → thetaForm M g g = 0 →
        thetaForm M (f + g) (f + g) = 0) ∧
      (∀ (c : ℝ) (f : Fin n → ℝ), thetaForm M f f = 0 → thetaForm M (c • f) (c • f) = 0) := by
  refine' ⟨ _, _, _ ⟩;
  · unfold thetaForm; norm_num;
  · -- By definition of thetaForm, we can expand thetaForm M (f + g) (f + g) using bilinearity.
    intros f g hf hg
    have h_expand : thetaForm M (f + g) (f + g) = thetaForm M f f + 2 * thetaForm M f g + thetaForm M g g := by
      unfold thetaForm;
      simp +decide [ add_mul, mul_add, Finset.sum_add_distrib, two_mul, add_assoc ];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ hsym ] ; ring );
    linarith [ thetaForm_cs M hsym hRP f g hf ];
  · intro c f hf; unfold thetaForm at *; simp_all +decide [ mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ]

/-
(b2) The form descends to the quotient by the null subspace.
-/
theorem D2_b_descends
    (hsym : ∀ i j, M (Sum.inl i) (Sum.inr j) = M (Sum.inl j) (Sum.inr i))
    (hRP : ∀ f : Fin n → ℝ, 0 ≤ thetaForm M f f)
    (f f' g g' : Fin n → ℝ)
    (hf : thetaForm M (f - f') (f - f') = 0) (hg : thetaForm M (g - g') (g - g') = 0) :
    thetaForm M f g = thetaForm M f' g' := by
  have h_expand : thetaForm M f g = thetaForm M f' g' + thetaForm M (f - f') g' + thetaForm M f' (g - g') + thetaForm M (f - f') (g - g') := by
    unfold thetaForm; simp +decide [ sub_mul, mul_sub ] ; ring;
  -- By symmetry and bilinearity, thetaForm M (f - f') g' = thetaForm M g' (f - f') and thetaForm M f' (g - g') = thetaForm M (g - g') f'.
  have h_symm : thetaForm M (f - f') g' = thetaForm M g' (f - f') ∧ thetaForm M f' (g - g') = thetaForm M (g - g') f' := by
    exact ⟨ by rw [ D2_a M hsym hRP |>.1 ], by rw [ D2_a M hsym hRP |>.1 ] ⟩;
  linarith [ thetaForm_cs M hsym hRP ( f - f' ) g' hf, thetaForm_cs M hsym hRP ( g - g' ) f' hg, thetaForm_cs M hsym hRP ( f - f' ) ( g - g' ) hf ]

/-
(b3) The descended form is positive definite on the quotient: any vector outside the null
subspace has strictly positive self-pairing.
-/
theorem D2_b_posdef
    (hRP : ∀ f : Fin n → ℝ, 0 ≤ thetaForm M f f)
    (f : Fin n → ℝ) (hf : thetaForm M f f ≠ 0) :
    0 < thetaForm M f f := by
  exact lt_of_le_of_ne ( hRP f ) hf.symm

end D2