import Mathlib

open scoped BigOperators Matrix

namespace I2

/-!
# I2. Purity criterion: product vector ⟺ rank one

For a real `m × n` matrix `M`, `(∃ u w, M i j = u i * w j)` iff `rank M ≤ 1`, and
`rank (M Mᵀ) ≤ 1` iff `rank M ≤ 1`.
-/

variable {m n : ℕ}

/-
Product vector ⟺ rank at most one.
-/
theorem I2_iff (M : Matrix (Fin m) (Fin n) ℝ) :
    (∃ (u : Fin m → ℝ) (w : Fin n → ℝ), ∀ i j, M i j = u i * w j) ↔ M.rank ≤ 1 := by
  constructor <;> intro h;
  · obtain ⟨ u, w, h ⟩ := h;
    -- Consider the matrix $M$ as a product of two matrices: $U$ and $W$, where $U$ is an $m \times 1$ matrix and $W$ is a $1 \times n$ matrix.
    set U : Matrix (Fin m) (Fin 1) ℝ := fun i j => u i
    set W : Matrix (Fin 1) (Fin n) ℝ := fun i j => w j
    have h_prod : M = U * W := by
      ext i j; simp [U, W, h];
      simp +decide [ Matrix.mul_apply ];
    exact h_prod ▸ Matrix.rank_mul_le _ _ |> le_trans <| min_le_of_left_le ( Matrix.rank_le_card_width _ );
  · interval_cases _ : Matrix.rank M;
    · simp_all +decide [ Matrix.rank, Submodule.eq_bot_iff ];
      exact ⟨ 0, 0, fun i j => by simpa using congr_fun ( ‹∀ a : Fin n → ℝ, M *ᵥ a = 0› ( Pi.single j 1 ) ) i ⟩;
    · -- Since the rank of $M$ is 1, there exists a nonzero vector $u$ such that the range of $M$ is spanned by $u$.
      obtain ⟨u, hu⟩ : ∃ u : (Fin m) → ℝ, u ≠ 0 ∧ ∀ v ∈ LinearMap.range (Matrix.mulVecLin M), ∃ c : ℝ, v = c • u := by
        obtain ⟨ u, hu ⟩ := finrank_eq_one_iff'.mp ‹_›;
        exact ⟨ u, by simpa using hu.1, fun v hv => by obtain ⟨ c, hc ⟩ := hu.2 ⟨ v, hv ⟩ ; exact ⟨ c, by simpa [ eq_comm ] using congr_arg Subtype.val hc ⟩ ⟩;
      choose! c hc using hu.2;
      exact ⟨ u, fun j => c ( M.mulVec ( Pi.single j 1 ) ), fun i j => by simpa [ mul_comm ] using congr_fun ( hc ( M.mulVec ( Pi.single j 1 ) ) ( Set.mem_range_self _ ) ) i ⟩

/-- `M Mᵀ` has rank ≤ 1 iff `M` has rank ≤ 1. -/
theorem I2_mul_transpose (M : Matrix (Fin m) (Fin n) ℝ) :
    (M * Mᵀ).rank ≤ 1 ↔ M.rank ≤ 1 := by
  rw [Matrix.rank_self_mul_transpose]

end I2