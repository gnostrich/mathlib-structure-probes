import Mathlib
import RequestProject.Horizon
import RequestProject.K1
import RequestProject.D5

open scoped BigOperators Matrix
open Horizon

namespace K3

/-!
# K3. Perturbation of the base kernel (margin transfer)

Let `0 < t_1 < … < t_n` and `M i j = min (t i) (t j)`, with `λ_min M = lambdaMin M` (positive by
K1).  For a symmetric `R` with `|xᵀ R x| ≤ ε` on all unit vectors:

* if `ε < λ_min M` then `M + R` is positive definite (via the Weyl lemma D5);
* moreover, if all entries satisfy `|R i j| ≤ δ`, then the operator hypothesis holds with
  `ε = n · δ`, via the entrywise-to-operator Cauchy–Schwarz bound `|xᵀ R x| ≤ n · δ · |x|²`.
-/

variable {n : ℕ}

/-
The entrywise-to-operator bound: `|xᵀ R x| ≤ n · δ` on unit vectors when `|R i j| ≤ δ`.
-/
theorem K3_operator_bound (R : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (hR : ∀ i j, |R i j| ≤ δ) :
    ∀ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) → |quadForm R x| ≤ n * δ := by
  intro x hx;
  -- First use the triangle inequality and entrywise bound to show $|quadForm R x| \leq \delta \cdot (∑ i |x i|)^2$.
  have h1 : |quadForm R x| ≤ δ * (∑ i, |x i|)^2 := by
    -- Apply the triangle inequality to the sum.
    have h_triangle : |quadForm R x| ≤ ∑ i, ∑ j, |x i| * |R i j| * |x j| := by
      exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun j _ => by rw [ abs_mul, abs_mul ] );
    refine le_trans h_triangle ?_;
    push_cast [ pow_two, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by nlinarith only [ abs_nonneg ( x i ), abs_nonneg ( x j ), mul_nonneg ( abs_nonneg ( x i ) ) ( abs_nonneg ( x j ) ), hR i j ] ;
  -- Next, use the Cauchy-Schwarz inequality to show that $(∑ i |x i|)^2 ≤ n * ∑ i |x i|^2$.
  have h2 : (∑ i, |x i|)^2 ≤ n * (∑ i, |x i|^2) := by
    have := ( Finset.univ.sum_le_sum fun i _ => mul_self_nonneg ( |x i| - ( ∑ i : Fin n, |x i| ) / n ) );
    by_cases hn : n = 0 <;> simp_all +decide [ sub_mul, mul_sub ];
    · aesop;
    · simp_all +decide [ ← sq, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      nlinarith [ mul_div_cancel₀ ( ∑ i, |x i| ) ( by positivity : ( n : ℝ ) ≠ 0 ) ];
  simp_all +decide [ mul_comm, sq_abs ];
  exact h1.trans ( mul_le_mul_of_nonneg_left h2 <| le_trans ( abs_nonneg _ ) ( hR ⟨ 0, Nat.pos_of_ne_zero <| by aesop_cat ⟩ ⟨ 0, Nat.pos_of_ne_zero <| by aesop_cat ⟩ ) )

/-
The min-kernel has positive minimal eigenvalue (from K1).
-/
theorem K3_lambdaMin_pos [NeZero n] (t : Fin n → ℝ) (hmono : StrictMono t)
    (hpos : ∀ i, 0 < t i) : 0 < lambdaMin (K1.minMat t) := by
  -- Since `minMat t` is positive definite, for any nonzero vector `x`, `quadForm (minMat t) x > 0`.
  have h_pos_def : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadForm (K1.minMat t) x := by
    apply K1.K1_posdef t hmono hpos;
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin n → ℝ, (∑ i, x₀ i ^ 2 = 1) ∧ quadForm (K1.minMat t) x₀ = lambdaMin (K1.minMat t) := by
    convert ( IsCompact.sInf_mem ?_ <| Horizon.valueSet_nonempty _ );
    any_goals exact K1.minMat t;
    · exact ⟨ fun ⟨ x₀, hx₀₁, hx₀₂ ⟩ => ⟨ x₀, hx₀₁, hx₀₂.symm ⟩, fun ⟨ x₀, hx₀₁, hx₀₂ ⟩ => ⟨ x₀, hx₀₁, hx₀₂.symm ⟩ ⟩;
    · have h_compact : IsCompact {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1} := by
        refine' ( Metric.isCompact_iff_isClosed_bounded.mpr _ );
        exact ⟨ isClosed_eq ( continuous_finset_sum _ fun _ _ => Continuous.pow ( continuous_apply _ ) _ ) continuous_const, isBounded_iff_forall_norm_le.mpr ⟨ 1, fun x hx => by exact pi_norm_le_iff_of_nonneg ( by norm_num ) |>.2 fun i => by simpa using Real.abs_le_sqrt <| show x i ^ 2 ≤ 1 by exact le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( x a ) ) ( Finset.mem_univ i ) ) hx.le ⟩ ⟩;
      convert h_compact.image ( show Continuous fun x : Fin n → ℝ => quadForm ( K1.minMat t ) x from ?_ ) using 1;
      · exact Set.ext fun x => ⟨ fun hx => by obtain ⟨ y, hy, rfl ⟩ := hx; exact ⟨ y, hy, rfl ⟩, fun hx => by obtain ⟨ y, hy, rfl ⟩ := hx; exact ⟨ y, hy, rfl ⟩ ⟩;
      · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => Continuous.mul ( Continuous.mul ( continuous_apply i ) ( continuous_const ) ) ( continuous_apply j );
    · infer_instance;
  exact hx₀.2 ▸ h_pos_def x₀ ( by rintro rfl; norm_num at hx₀ )

/-
Margin transfer: a perturbation with operator norm below the base margin stays PD.
-/
theorem K3_main [NeZero n] (t : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hR : ∀ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) → |quadForm R x| ≤ ε)
    (hε : ε < lambdaMin (K1.minMat t)) :
    IsPDq (K1.minMat t + R) := by
  convert D5.D5_b ( K1.minMat t ) R ( lambdaMin ( K1.minMat t ) ) ε ( le_refl _ ) hR hε using 1

/-- Combined entrywise form: an entrywise `δ`-small perturbation with `n · δ < λ_min` stays PD. -/
theorem K3_entrywise [NeZero n] (t : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (hR : ∀ i j, |R i j| ≤ δ)
    (hδ : (n : ℝ) * δ < lambdaMin (K1.minMat t)) :
    IsPDq (K1.minMat t + R) :=
  K3_main t R ((n : ℝ) * δ) (K3_operator_bound R δ hR) hδ

end K3