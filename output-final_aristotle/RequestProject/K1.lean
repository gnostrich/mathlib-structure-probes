import Mathlib
import RequestProject.Horizon

open scoped BigOperators Matrix
open Horizon

namespace K1

/-!
# K1. The min-kernel is positive definite (Brownian/archimedean core)

For `0 < t_1 < t_2 < … < t_n`, the matrix `M i j = min (t i) (t j)` is positive definite.

Route (sum-of-squares / telescoping): with `t` strictly increasing and positive,
`min (t i) (t j) = t (min i j) = ∑_{k ≤ min i j} d k` where `d 0 = t 0` and
`d k = t k - t (k-1)` for `k ≥ 1` — all `d k > 0`.  Hence
`xᵀ M x = ∑_k d k · (∑_{i ≥ k} x i)²`, a nonnegative combination of squares; it vanishes only
if every tail sum `∑_{i ≥ k} x i` is zero, forcing `x = 0`.
-/

/-- The min-kernel matrix `M i j = min (t i) (t j)`. -/
def minMat {n : ℕ} (t : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => min (t i) (t j)

theorem K1_posdef {n : ℕ} (t : Fin n → ℝ) (hmono : StrictMono t)
    (hpos : ∀ i, 0 < t i) : IsPDq (minMat t) := by
  rcases n with ( _ | n ) <;> simp_all +decide [ StrictMono ];
  · exact fun x hx => False.elim <| hx <| by ext i; fin_cases i;
  · -- Define the vector $d$ such that $d_0 = t_0$ and $d_k = t_k - t_{k-1}$ for $k \geq 1$.
    set d : Fin (n + 1) → ℝ := fun k => if k = 0 then t 0 else t k - t (k - 1);
    -- By definition of $d$, we know that $min (t i) (t j) = \sum_{k \leq min(i, j)} d k$.
    have h_min : ∀ i j, min (t i) (t j) = ∑ k ∈ Finset.univ.filter (fun k => k ≤ min i j), d k := by
      intro i j
      have h_sum : ∑ k ∈ Finset.univ.filter (fun k => k ≤ min i j), d k = t (min i j) := by
        induction' min i j using Fin.inductionOn with k ih;
        · rw [ Finset.sum_eq_single 0 ] <;> aesop;
        · rw [ show ( Finset.filter ( fun x => x ≤ Fin.succ k ) Finset.univ : Finset ( Fin ( n + 1 ) ) ) = Finset.filter ( fun x => x ≤ Fin.castSucc k ) Finset.univ ∪ { Fin.succ k } from ?_, Finset.sum_union ] <;> norm_num [ ih ];
          · simp +zetaDelta at *;
            rw [ show ( Fin.succ k - 1 : Fin ( n + 1 ) ) = Fin.castSucc k from by simp +decide [ sub_eq_iff_eq_add ] ] ; ring;
          · grind +suggestions;
      cases le_total i j <;> simp_all +decide [ StrictMono.le_iff_le ]; all_goals exact monotone_iff_forall_lt.mpr ( fun a b hab => le_of_lt ( hmono hab ) ) ‹_›;
    -- Substitute $min (t i) (t j)$ with $\sum_{k \leq min(i, j)} d k$ in the quadratic form.
    have h_quadForm : ∀ x : Fin (n + 1) → ℝ, quadForm (minMat t) x = ∑ k, d k * (∑ i ∈ Finset.univ.filter (fun i => k ≤ i), x i) ^ 2 := by
      intro x
      have h_quadForm_step : ∀ i j, x i * min (t i) (t j) * x j = ∑ k, d k * (if k ≤ i then x i else 0) * (if k ≤ j then x j else 0) := by
        intro i j; rw [ h_min i j ] ; simp +decide [ Finset.sum_ite, mul_assoc, mul_comm, mul_left_comm ] ;
        simp +decide [ Finset.mul_sum _ _ _, mul_assoc, Finset.sum_filter ];
        exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> tauto;
      unfold quadForm minMat; simp +decide [ h_quadForm_step, Finset.sum_mul _ _ _ ] ; ring;
      simp +decide [ Finset.sum_ite, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, sq ];
      rw [ Finset.sum_sigma', Finset.sum_sigma' ];
      rw [ Finset.sum_sigma', Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun x hx => ⟨ ⟨ x.snd, x.fst.fst ⟩, x.fst.snd ⟩ ) _ _ _ _ <;> simp +decide;
      · tauto;
      · grind;
      · grind;
    -- Since $d_k > 0$ for all $k$, the quadratic form is a sum of squares with positive coefficients.
    have h_pos : ∀ k, 0 < d k := by
      simp +zetaDelta at *;
      intro k; split_ifs <;> simp_all +decide [ sub_pos ] ;
      convert hmono _;
      rw [ Fin.lt_def ] ; simp +decide [ *, Fin.ext_iff, Fin.coe_sub_one ];
      exact lt_of_le_of_ne ( Nat.zero_le _ ) ( Ne.symm ‹_› );
    intro x hx; contrapose! hx; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg, le_of_lt ] ;
    -- Since $d_k > 0$ for all $k$, the only way for the sum to be non-positive is if each term in the sum is zero.
    have h_zero : ∀ k, (∑ i ∈ Finset.univ.filter (fun i => k ≤ i), x i) = 0 := by
      exact fun k => sq_eq_zero_iff.mp ( by nlinarith only [ hx, h_pos k, Finset.single_le_sum ( fun a _ => mul_nonneg ( le_of_lt ( h_pos a ) ) ( sq_nonneg ( ∑ i with a ≤ i, x i ) ) ) ( Finset.mem_univ k ) ] );
    ext i; have := h_zero i; have := h_zero ( i + 1 ) ; simp_all +decide [ Finset.sum_filter, Finset.sum_range_succ ] ;
    induction' i using Fin.reverseInduction with i IH;
    · specialize h_zero ( Fin.last n ) ; simp_all +decide [ Finset.sum_ite ] ;
    · have := h_zero ( Fin.castSucc i ) ; have := h_zero ( Fin.succ i ) ; simp_all +decide [ Finset.sum_ite, Finset.filter_le_eq_Ici ] ;
      have := h_zero ( Fin.castSucc i ) ; have := h_zero ( Fin.succ i ) ; rw [ show ( Finset.Ici ( Fin.castSucc i ) : Finset ( Fin ( n + 1 ) ) ) = Finset.Ici ( Fin.succ i ) ∪ { Fin.castSucc i } from ?_, Finset.sum_union ] at * <;> norm_num at * ; linarith!;
      ext j; simp [Finset.mem_Ici, Finset.mem_insert];
      exact ⟨ fun h => or_iff_not_imp_left.mpr fun h' => lt_of_le_of_ne h ( Ne.symm h' ), fun h => h.elim ( fun h => h.symm ▸ le_rfl ) fun h => Nat.le_trans ( Nat.le_succ _ ) h ⟩

end K1