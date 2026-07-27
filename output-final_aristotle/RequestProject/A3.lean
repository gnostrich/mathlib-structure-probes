import Mathlib

open scoped BigOperators Matrix

namespace A3

/-!
# A3. Neutral bulk, chiral cycle (existence)

There is a `3 × 3` real matrix `K` that is antisymmetric, divergence-free
(each row sums to zero), yet has nonzero circulation around the 3-cycle.
-/

theorem A3_exists :
    ∃ K : Matrix (Fin 3) (Fin 3) ℝ,
      Kᵀ = -K ∧ (∀ i, ∑ j, K i j = 0) ∧ K 0 1 + K 1 2 + K 2 0 ≠ 0 := by
  -- Consider the matrix
  use !![0, 1, -1; -1, 0, 1; 1, -1, 0];
  simp +decide [ Fin.forall_fin_succ ];
  norm_num [ Fin.sum_univ_succ, ← List.ofFn_inj ];
  aesop

end A3