import Mathlib
import RequestProject.Horizon

open scoped BigOperators Matrix
open Horizon

-- The reverse direction (Schur-complement induction) is computationally heavy;
-- raise the elaboration budget accordingly.
set_option maxHeartbeats 4000000

namespace D6

/-!
# D6. Sylvester's criterion (rational PD verification engine)

A real symmetric matrix `A` is positive definite iff all its leading principal minors are
positive.  The leading principal submatrix of order `k+1` (for `k : Fin n`) is the top-left
`(k+1) × (k+1)` block.
-/

variable {n : ℕ}

/-- The leading principal submatrix of order `k+1`. -/
def leadingSub (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  A.submatrix (fun i => Fin.castLE (by omega) i) (fun i => Fin.castLE (by omega) i)

/-
Bridge: for a symmetric real matrix, the quadratic-form notion of positive definiteness
agrees with Mathlib's `Matrix.PosDef`.
-/
lemma isPDq_iff_posDef (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) :
    IsPDq A ↔ A.PosDef := by
  constructor <;> intro h;
  · constructor <;> try assumption;
    intro x hx_ne; specialize h ( fun i => x i ) ; simp_all +decide [ Finsupp.sum_fintype, Matrix.mulVec, dotProduct ] ;
    convert h using 1;
  · convert h.2;
    simp +decide [ IsPDq, Finsupp.sum_fintype ];
    constructor <;> intro h x hx;
    · convert h x ( by simpa [ Finsupp.ext_iff ] using hx ) using 1;
    · convert h ( show ( Finsupp.equivFunOnFinite.symm x ) ≠ 0 from by simpa [ Finsupp.ext_iff, funext_iff ] using hx ) using 1

/-
A leading principal submatrix of a symmetric matrix is symmetric.
-/
lemma leadingSub_transpose (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (k : Fin n) :
    (leadingSub A k)ᵀ = leadingSub A k := by
  ext i j; simp +decide [ *, leadingSub ] ;
  exact congr_fun ( congr_fun hA _ ) _

/-
A leading principal submatrix of a positive-definite (quadratic-form) matrix is positive
definite.
-/
lemma leadingSub_isPDq (A : Matrix (Fin n) (Fin n) ℝ) (hPD : IsPDq A) (k : Fin n) :
    IsPDq (leadingSub A k) := by
  intro y hy;
  convert hPD ( fun i => if h : i.val < ( Fin.val k + 1 ) then y ⟨ i.val, h ⟩ else 0 ) _ using 1;
  · convert Finset.sum_subset ?_ ?_ using 1;
    rotate_left;
    exact Finset.univ;
    · exact Finset.Subset.refl _;
    · aesop;
    · unfold quadForm leadingSub;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i : Fin ( k + 1 ) => Fin.castLE ( by linarith [ Fin.is_lt k ] ) i ) Finset.univ ) ) ];
      · rw [ Finset.sum_image ] <;> norm_num;
        · refine' Finset.sum_congr rfl fun i hi => _;
          rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : Fin ( k + 1 ) => Fin.castLE ( by linarith [ Fin.is_lt k ] ) x ) Finset.univ ) ) ];
          · rw [ Finset.sum_image ] <;> norm_num;
            · grind +extAll;
            · exact fun x y h => by simpa [ Fin.ext_iff ] using h;
          · simp +contextual [ Fin.castLE ];
            exact fun x hx h₁ h₂ => False.elim <| hx ⟨ x, by linarith [ Fin.is_lt k, Fin.is_lt x, show ( x : ℕ ) ≤ k from h₁ ] ⟩ rfl;
        · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
      · simp +contextual [ Finset.mem_image ];
        intro x hx; rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ Fin.ext_iff ] ;
        exact fun _ _ => False.elim <| hx ⟨ x, by linarith [ Fin.is_lt x, Fin.is_lt k, show ( x : ℕ ) ≤ k from by assumption ] ⟩ rfl;
  · contrapose! hy; ext i; simp_all +decide [ funext_iff ] ;
    convert hy ⟨ i, by linarith [ Fin.is_lt i, Fin.is_lt k ] ⟩ ( Nat.le_trans ( Nat.le_of_lt_succ ( Fin.is_lt i ) ) ( Nat.le_refl _ ) )

/-
Forward direction of Sylvester's criterion.
-/
lemma sylvester_forward (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (hPD : IsPDq A) :
    ∀ k : Fin n, 0 < (leadingSub A k).det := by
  intro k;
  convert Matrix.PosDef.det_pos _;
  exact isPDq_iff_posDef _ ( leadingSub_transpose _ hA _ ) |>.1 ( leadingSub_isPDq _ hPD _ )

/-
Reverse direction of Sylvester's criterion (the substantial induction).
-/
lemma sylvester_reverse : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), Aᵀ = A →
    (∀ k : Fin n, 0 < (leadingSub A k).det) → IsPDq A := by
  intro n;
  induction' n with n ih <;> intro A hA h;
  · exact fun x hx => False.elim <| hx <| Subsingleton.elim _ _;
  · -- Let B be the top-left n x n submatrix of A, b be the coupling vector, and c be the bottom-right entry of A.
    set B : Matrix (Fin n) (Fin n) ℝ := A.submatrix Fin.castSucc Fin.castSucc
    set b : Fin n → ℝ := fun i => A (Fin.castSucc i) (Fin.last n)
    set c : ℝ := A (Fin.last n) (Fin.last n);
    -- By the induction hypothesis, B is positive definite.
    have hB : IsPDq B := by
      apply ih B;
      · ext i j; simp +decide [ B, hA ] ;
        exact congr_fun ( congr_fun hA _ ) _;
      · intro k;
        convert h ⟨ k, by linarith [ Fin.is_lt k ] ⟩ using 1;
    -- By the properties of determinants, we have $\det(A) = \det(B) \cdot (c - b^T B^{-1} b)$.
    have h_det : Matrix.det A = Matrix.det B * (c - dotProduct b (Matrix.mulVec B⁻¹ b)) := by
      have h_det : Matrix.det A = Matrix.det (Matrix.fromBlocks B (Matrix.of (fun i j => b i)) (Matrix.of (fun i j => b j)) (Matrix.of ![![c]])) := by
        convert rfl;
        convert Matrix.det_reindex_self ( finSumFinEquiv.symm ) _ using 2;
        · ext i j; simp +decide [ finSumFinEquiv ] ;
          rcases i with ( i | i ) <;> rcases j with ( j | j ) <;> norm_num [ Fin.castAdd, Fin.natAdd ];
          · rfl;
          · rfl;
          · exact congr_fun ( congr_fun hA _ ) _;
          · rfl;
        · infer_instance;
      have h_det : Matrix.det (Matrix.fromBlocks B (Matrix.of (fun i j => b i)) (Matrix.of (fun i j => b j)) (Matrix.of ![![c]])) = Matrix.det B * Matrix.det (Matrix.of ![![c]] - Matrix.of (fun i j => b j) * B⁻¹ * Matrix.of (fun i j => b i)) := by
        have h_det : Invertible B := by
          convert Matrix.invertibleOfDetInvertible B;
          refine invertibleOfNonzero ?_;
          convert hB |> fun h => isPDq_iff_posDef B ( by ext i j; simpa [ B ] using congr_fun ( congr_fun hA ( Fin.castSucc i ) ) ( Fin.castSucc j ) ) |>.1 h |>.det_pos.ne' using 1;
        have h_det : Matrix.det (Matrix.fromBlocks B (Matrix.of (fun i j => b i)) (Matrix.of (fun i j => b j)) (Matrix.of ![![c]])) = Matrix.det B * Matrix.det (Matrix.of ![![c]] - Matrix.of (fun i j => b j) * B⁻¹ * Matrix.of (fun i j => b i)) := by
          have h_block : Matrix.fromBlocks B (Matrix.of (fun i j => b i)) (Matrix.of (fun i j => b j)) (Matrix.of ![![c]]) = Matrix.fromBlocks 1 0 (Matrix.of (fun i j => b j) * B⁻¹) 1 * Matrix.fromBlocks B (Matrix.of (fun i j => b i)) 0 (Matrix.of ![![c]] - Matrix.of (fun i j => b j) * B⁻¹ * Matrix.of (fun i j => b i)) := by
            simp +decide [ Matrix.fromBlocks_multiply ]
          rw [ h_block, Matrix.det_mul ];
          norm_num [ Matrix.det_fromBlocks_zero₂₁ ];
        exact h_det;
      simp_all +decide [ Matrix.mul_apply, dotProduct ];
      simp +decide [ Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      exact Or.inl ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
    -- Since $\det(A) > 0$ and $\det(B) > 0$, we have $c - b^T B^{-1} b > 0$.
    have h_pos : c - dotProduct b (Matrix.mulVec B⁻¹ b) > 0 := by
      have h_det_pos : 0 < Matrix.det A := by
        convert h ⟨ n, Nat.lt_succ_self n ⟩ using 1;
      contrapose! h_det_pos;
      convert mul_nonpos_of_nonneg_of_nonpos ( show 0 ≤ Matrix.det B from ?_ ) h_det_pos using 1;
      convert Matrix.PosDef.det_pos ( isPDq_iff_posDef B ( show Bᵀ = B from ?_ ) |>.1 hB ) |> le_of_lt using 1;
      exact Matrix.ext fun i j => by simpa using congr_fun ( congr_fun hA ( Fin.castSucc i ) ) ( Fin.castSucc j ) ;
    -- By completing the square, we can rewrite the quadratic form of A as follows:
    have h_complete_square : ∀ x : Fin (n + 1) → ℝ, quadForm A x = quadForm B (fun i => x (Fin.castSucc i)) + 2 * x (Fin.last n) * dotProduct b (fun i => x (Fin.castSucc i)) + c * x (Fin.last n) ^ 2 := by
      intro x; unfold quadForm; simp +decide [ Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct ] ; ring;
      simp +decide [ Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, B, b, c ] ; ring;
      simp +decide [ mul_two, add_comm, add_left_comm, add_assoc, Finset.sum_add_distrib ];
      exact Finset.sum_congr rfl fun _ _ => by rw [ ← Matrix.transpose_apply A ] ; rw [ hA ] ;
    -- By completing the square, we can rewrite the quadratic form of A as follows: $x^T A x = (x + z w)^T B (x + z w) + s z^2$, where $w = B^{-1} b$ and $s = c - b^T B^{-1} b$.
    have h_complete_square_rewrite : ∀ x : Fin (n + 1) → ℝ, quadForm A x = quadForm B (fun i => x (Fin.castSucc i) + x (Fin.last n) * (Matrix.mulVec B⁻¹ b) i) + (c - dotProduct b (Matrix.mulVec B⁻¹ b)) * x (Fin.last n) ^ 2 := by
      intro x
      rw [h_complete_square];
      unfold quadForm;
      -- By expanding the right-hand side, we can see that it matches the left-hand side.
      have h_expand : ∑ i, ∑ j, (x (Fin.castSucc i) + x (Fin.last n) * (B⁻¹ *ᵥ b) i) * B i j * (x (Fin.castSucc j) + x (Fin.last n) * (B⁻¹ *ᵥ b) j) = ∑ i, ∑ j, x (Fin.castSucc i) * B i j * x (Fin.castSucc j) + 2 * x (Fin.last n) * ∑ i, ∑ j, x (Fin.castSucc i) * B i j * (B⁻¹ *ᵥ b) j + x (Fin.last n) ^ 2 * ∑ i, ∑ j, (B⁻¹ *ᵥ b) i * B i j * (B⁻¹ *ᵥ b) j := by
        simp +decide [ add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib, pow_two ];
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ] ; ring;
        simp +decide [ mul_two, Finset.sum_add_distrib, add_assoc ];
        simp +decide [ mul_add, Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        rw [ Finset.sum_comm ];
        have h_symm : Bᵀ = B := by
          ext i j; simp [B, hA];
          exact congr_fun ( congr_fun hA _ ) _;
        exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [ ← Matrix.ext_iff ] at h_symm; aesop;
      -- By definition of matrix multiplication and the properties of the dot product, we can simplify the expression.
      have h_simplify : ∑ i, ∑ j, x (Fin.castSucc i) * B i j * (B⁻¹ *ᵥ b) j = dotProduct b (fun i => x (Fin.castSucc i)) := by
        have h_simplify : ∑ i, ∑ j, x (Fin.castSucc i) * B i j * (B⁻¹ *ᵥ b) j = ∑ i, x (Fin.castSucc i) * (B.mulVec (B⁻¹ *ᵥ b)) i := by
          simp +decide only [Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc];
        rw [ h_simplify, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv ] <;> norm_num [ dotProduct_comm ];
        · rfl;
        · exact ne_of_gt ( h ⟨ n - 1, Nat.lt_succ_of_le ( Nat.sub_le _ _ ) ⟩ ) |> fun h => by cases n <;> aesop;
      have h_simplify : ∑ i, ∑ j, (B⁻¹ *ᵥ b) i * B i j * (B⁻¹ *ᵥ b) j = dotProduct b (B⁻¹ *ᵥ b) := by
        have h_simplify : ∑ i, ∑ j, (B⁻¹ *ᵥ b) i * B i j * (B⁻¹ *ᵥ b) j = dotProduct (B⁻¹ *ᵥ b) (B.mulVec (B⁻¹ *ᵥ b)) := by
          simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc ];
        rw [ h_simplify, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv ];
        · simp +decide [ dotProduct_comm ];
        · specialize h ⟨ n - 1, Nat.lt_succ_of_le ( Nat.sub_le _ _ ) ⟩ ; rcases n with ( _ | n ) <;> simp_all +decide [ leadingSub ] ;
          exact ne_of_gt h;
      grind +qlia;
    intro x hx_ne_zero
    by_cases hz : x (Fin.last n) = 0;
    · simp_all +decide [ funext_iff, Fin.ext_iff ];
      exact hB _ ( by intro h; exact hx_ne_zero.elim fun i hi => hi <| by cases i using Fin.lastCases <;> simp_all +decide [ funext_iff ] );
    · rw [ h_complete_square_rewrite ];
      refine' add_pos_of_nonneg_of_pos ( _ ) ( mul_pos h_pos ( sq_pos_of_ne_zero hz ) );
      by_cases h : ( fun i => x ( Fin.castSucc i ) + x ( Fin.last n ) * ( B⁻¹ *ᵥ b ) i ) = 0 <;> simp_all +decide [ IsPDq ];
      · unfold quadForm; norm_num;
      · exact le_of_lt ( hB _ h )

/-- Sylvester's criterion: a symmetric matrix is positive definite iff every leading
principal minor is positive. -/
theorem D6_sylvester (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) :
    IsPDq A ↔ ∀ k : Fin n, 0 < (leadingSub A k).det :=
  ⟨sylvester_forward A hA, sylvester_reverse n A hA⟩

end D6