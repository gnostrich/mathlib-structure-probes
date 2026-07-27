import Mathlib
import RequestProject.D6

open scoped BigOperators Matrix
open Horizon

set_option maxHeartbeats 4000000

namespace TierR

variable {n : ℕ}

/-- A symmetric one-site border of `A`, indexed so the old matrix is the top-left block. -/
def border (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
  if hi : i.val < n then
    if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else b ⟨i.val, hi⟩
  else if hj : j.val < n then b ⟨j.val, hj⟩ else d

/-- The scalar Schur complement of the border. -/
noncomputable def schur (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ) : ℝ :=
  d - dotProduct b (A⁻¹ *ᵥ b)

lemma border_old (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ)
    (i j : Fin n) : border A b d (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  simp [border, Fin.is_lt]

lemma border_last_col (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ)
    (i : Fin n) : border A b d (Fin.castSucc i) (Fin.last n) = b i := by
  simp [border, Fin.is_lt]

lemma border_last_row (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ)
    (i : Fin n) : border A b d (Fin.last n) (Fin.castSucc i) = b i := by
  simp [border, Fin.is_lt]

lemma border_corner (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ) :
    border A b d (Fin.last n) (Fin.last n) = d := by
  simp [border]

lemma border_transpose (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A)
    (b : Fin n → ℝ) (d : ℝ) : (border A b d)ᵀ = border A b d := by
  ext i j; by_cases hi : i.val < n <;> by_cases hj : j.val < n <;> simp +decide [ *, border ] ;
  exact congr_fun ( congr_fun hA _ ) _

/-
Completing the square for a symmetric bordered matrix.
-/
lemma border_quadForm_complete (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A)
    (hPD : IsPDq A) (b : Fin n → ℝ) (d : ℝ) (x : Fin (n + 1) → ℝ) :
    quadForm (border A b d) x =
      quadForm A (fun i => x (Fin.castSucc i) + x (Fin.last n) * (A⁻¹ *ᵥ b) i) +
        schur A b d * x (Fin.last n) ^ 2 := by
  by_cases h : IsUnit ( A.det ) <;> simp_all +decide [ Matrix.nonsing_inv_apply_not_isUnit ];
  · unfold quadForm schur;
    have h_complete_square : ∑ i, ∑ j, (x (Fin.castSucc i) + x (Fin.last n) * (A⁻¹ *ᵥ b) i) * A i j * (x (Fin.castSucc j) + x (Fin.last n) * (A⁻¹ *ᵥ b) j) = ∑ i, ∑ j, x (Fin.castSucc i) * A i j * x (Fin.castSucc j) + 2 * x (Fin.last n) * ∑ i, b i * x (Fin.castSucc i) + x (Fin.last n) ^ 2 * ∑ i, b i * (A⁻¹ *ᵥ b) i := by
      have h_complete_square : ∑ i, ∑ j, (x (Fin.castSucc i) + x (Fin.last n) * (A⁻¹ *ᵥ b) i) * A i j * (x (Fin.castSucc j) + x (Fin.last n) * (A⁻¹ *ᵥ b) j) = ∑ i, ∑ j, x (Fin.castSucc i) * A i j * x (Fin.castSucc j) + 2 * x (Fin.last n) * ∑ i, ∑ j, x (Fin.castSucc i) * A i j * (A⁻¹ *ᵥ b) j + x (Fin.last n) ^ 2 * ∑ i, ∑ j, (A⁻¹ *ᵥ b) i * A i j * (A⁻¹ *ᵥ b) j := by
        simp +decide [ add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib, pow_two ];
        simp +decide [ mul_two, add_assoc, Finset.sum_add_distrib ];
        simp +decide [ mul_add, add_assoc, Finset.sum_add_distrib ];
        rw [ Finset.sum_comm ];
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← Matrix.ext_iff ] at hA; aesop;
      have h_complete_square : ∑ i, ∑ j, x (Fin.castSucc i) * A i j * (A⁻¹ *ᵥ b) j = ∑ i, b i * x (Fin.castSucc i) := by
        have h_complete_square : ∑ i, ∑ j, x (Fin.castSucc i) * A i j * (A⁻¹ *ᵥ b) j = ∑ i, x (Fin.castSucc i) * (A.mulVec (A⁻¹ *ᵥ b)) i := by
          simp +decide only [mul_assoc, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _];
        simp_all +decide [ mul_comm, Matrix.mulVec_mulVec ];
      have h_complete_square : ∑ i, ∑ j, (A⁻¹ *ᵥ b) i * A i j * (A⁻¹ *ᵥ b) j = ∑ i, b i * (A⁻¹ *ᵥ b) i := by
        have h_complete_square : ∑ i, ∑ j, (A⁻¹ *ᵥ b) i * A i j * (A⁻¹ *ᵥ b) j = ∑ i, (A⁻¹ *ᵥ b) i * (A.mulVec (A⁻¹ *ᵥ b)) i := by
          simp +decide only [mul_assoc, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _];
        simp_all +decide [ Matrix.mulVec_mulVec, mul_comm ];
      grind;
    simp_all +decide [ Fin.sum_univ_castSucc, border ];
    simp_all +decide [ Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, dotProduct ] ; ring;
    norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, sq ] ; ring;
    simpa [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] using by ring;
  · have := Matrix.exists_mulVec_eq_zero_iff.mpr h;
    obtain ⟨ v, hv, hv' ⟩ := this; specialize hPD v; simp_all +decide [ funext_iff, Matrix.mulVec ] ;
    simp_all +decide [ dotProduct, quadForm ];
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc ]

/-
R-A1(a,c): a positive Schur complement extends a positive-definite matrix.
-/
theorem schur_pos_isPDq (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A)
    (hPD : IsPDq A) (b : Fin n → ℝ) (d : ℝ) (hs : 0 < schur A b d) :
    IsPDq (border A b d) := by
  intro x hx; by_cases hx_last : x ( Fin.last n ) = 0 <;> simp_all +decide [ Matrix.mulVec ] ;
  · convert hPD ( fun i => x ( Fin.castSucc i ) ) _ using 1;
    · convert border_quadForm_complete A hA hPD b d x using 1 ; simp +decide [ hx_last, schur ];
    · exact fun h => hx <| funext fun i => by cases i using Fin.lastCases <;> simp_all +decide [ funext_iff ] ;
  · have h_complete_square : quadForm (border A b d) x = quadForm A (fun i => x (Fin.castSucc i) + x (Fin.last n) * (A⁻¹ *ᵥ b) i) + schur A b d * x (Fin.last n) ^ 2 := by
      convert border_quadForm_complete A hA hPD b d x using 1;
    by_cases h : ( fun i => x ( Fin.castSucc i ) + x ( Fin.last n ) * ( A⁻¹ *ᵥ b ) i ) = 0 <;> simp_all +decide [ Matrix.mulVec ];
    · simp_all +decide [ funext_iff, quadForm ];
      positivity;
    · exact add_pos_of_pos_of_nonneg ( hPD _ h ) ( mul_nonneg hs.le ( sq_nonneg _ ) )

/-
R-A1(b), forward part: a positive-definite border has a positive-definite old block.
-/
theorem border_pd_old_pd (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ)
    (hPD : IsPDq (border A b d)) : IsPDq A := by
  intro x hx_nonzero
  have := hPD (Fin.snoc x 0) (by
  exact fun h => hx_nonzero <| funext fun i => by simpa using congr_fun h ( Fin.castSucc i ) ;);
  unfold quadForm at *;
  simp_all +decide [ Fin.sum_univ_castSucc, border ]

/-
R-A1(b), Schur part: a positive-definite symmetric border has positive Schur complement.
-/
theorem border_pd_schur_pos (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A)
    (b : Fin n → ℝ) (d : ℝ) (hPD : IsPDq (border A b d)) :
    0 < schur A b d := by
  -- Let $x$ be a vector with $x_i = -(A^{-1}b)_i$ for $i < n$ and $x_n = 1$.
  set x : Fin (n + 1) → ℝ := Fin.snoc (fun i => -(A⁻¹ *ᵥ b) i) 1;
  have hx : 0 < quadForm (border A b d) x := by
    exact hPD x ( ne_of_apply_ne ( fun x => x ( Fin.last n ) ) ( by aesop ) );
  rw [ border_quadForm_complete A hA ( border_pd_old_pd A b d hPD ) b d x ] at hx;
  unfold quadForm at hx; aesop;

end TierR