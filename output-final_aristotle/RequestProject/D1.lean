import Mathlib
import RequestProject.Horizon

open scoped BigOperators Matrix
open Horizon

namespace D1

/-!
# D1. Horizons nest: the floor only moves one way (Cauchy interlacing, min form)

Let `A` be an `(n+1) × (n+1)` real matrix and `B` the principal submatrix obtained by
deleting the last row and column.  Writing `λ_min(M)` for the infimum of `xᵀMx` over unit
vectors `x` (`Horizon.lambdaMin`), we prove:

* (a) `λ_min(B) ≥ λ_min(A)`;
* (b) if `A` is positive semidefinite then `B` is positive semidefinite.

The matrix `A` is symmetric in the original statement, but symmetry is not needed for either
claim, so it is omitted.  Part (a) requires the deleted matrix `B` to be nonempty (`NeZero n`);
without it the claim fails (e.g. `A = [5]`, `B` empty gives `λ_min B = 0 < 5`).
-/

variable {n : ℕ}

/-- `B` is `A` with its last row and column deleted. -/
def sub (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A.submatrix Fin.castSucc Fin.castSucc

/-
(a) Deleting a horizon can only raise the floor.
-/
theorem D1_a [NeZero n] (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    lambdaMin A ≤ lambdaMin (sub A) := by
  -- Given that $r \in \text{valueSet } (\text{sub } A)$, there exists $y \in \text{Fin } n \to \mathbb{R}$ such that $\sum i, y i^2 = 1$ and $r = \text{quadForm } (\text{sub } A) y$.
  have h_subset : ∀ r ∈ valueSet (sub A), r ∈ valueSet A := by
    intro r hr
    obtain ⟨y, hy⟩ := hr
    use Fin.snoc y 0
    simp [hy];
    simp +decide [ ← hy.1, Fin.sum_univ_castSucc, quadForm, sub ];
  exact le_csInf ( valueSet_nonempty ( sub A ) ) fun r hr => csInf_le ( valueSet_bddBelow A ) ( h_subset r hr ) ;

/-
(b) A principal submatrix of a PSD matrix is PSD.
-/
theorem D1_b (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : IsPSDq A) :
    IsPSDq (sub A) := by
  intro y;
  convert hA ( Fin.snoc y 0 ) using 1;
  unfold quadForm sub; simp +decide [ Fin.sum_univ_castSucc ] ;

end D1