import Mathlib

open scoped BigOperators Matrix

namespace B1

/-!
# B1. Hankel factorization bound

For `m_k = vᵀ Aᵏ v` and the `N × N` Hankel matrix `H_{ij} = m_{i+j}`,
`rank H ≤ dim span{v, Av, …, A^{N-1}v} ≤ n`.
-/

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)

/-- The moment sequence. -/
noncomputable def m (k : ℕ) : ℝ := v ⬝ᵥ (A ^ k *ᵥ v)

/-- The `N × N` Hankel matrix. -/
noncomputable def H (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => m A v ((i : ℕ) + (j : ℕ)))

/-- The Krylov span. -/
noncomputable def krylov (N : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range (fun i : Fin N => A ^ (i : ℕ) *ᵥ v))

theorem B1_bound (N : ℕ) :
    (H A v N).rank ≤ Module.finrank ℝ (krylov A v N) ∧
      Module.finrank ℝ (krylov A v N) ≤ n := by
  refine' And.intro _ ( le_trans ( Submodule.finrank_le _ ) ( by simpa ) );
  -- Write H as O * C, where C has columns the Krylov vectors and O has rows vᵀ Aⁱ.
  set C : Matrix (Fin n) (Fin N) ℝ := Matrix.of (fun a j => (A ^ (j : ℕ) *ᵥ v) a)
  set O : Matrix (Fin N) (Fin n) ℝ := Matrix.of (fun i b => (Matrix.vecMul v (A ^ (i : ℕ))) b);
  -- Then $H = O * C$.
  have hH : H A v N = O * C := by
    ext i j; simp +decide [ H, m, Matrix.mul_apply ] ; ring;
    simp +decide [ O, C, pow_add, Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec ];
    simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
    simp +decide [ Matrix.vecMul, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact?;
  -- By definition of $C$, we know that its columns span the Krylov subspace.
  have hC_span : Submodule.span ℝ (Set.range (fun i : Fin N => A ^ (i : ℕ) *ᵥ v)) = LinearMap.range (Matrix.mulVecLin C) := by
    ext; simp [C];
    simp +decide [ funext_iff, Matrix.mulVec, dotProduct, Submodule.mem_span_range_iff_exists_fun ];
    simp +decide only [mul_comm];
  rw [ show krylov A v N = Submodule.span ℝ ( Set.range fun i : Fin N => A ^ ( i : ℕ ) *ᵥ v ) from rfl, hC_span ];
  rw [ hH ] ; exact Matrix.rank_mul_le_right _ _;

end B1