import RequestProject.V5_1
import RequestProject.V5_2
import RequestProject.V5_3
import RequestProject.V5_4
import RequestProject.Horizon

open Horizon

namespace V5_5

/-- The genuine screw Gram matrix on the grid `(0.2,0.4,0.6)`. -/
noncomputable def M3 : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  let t : Fin 3 → ℝ := ![0.2, 0.4, 0.6]
  V5_1.G (t i) (t j)

/-
Certified enclosures sufficient for the prime-free certificate.
-/
theorem psi_grid_bounds :
    (0.0543 : ℝ) < V5_1.Psi 0.2 ∧ V5_1.Psi 0.2 < 0.0547 ∧
    (0.0408 : ℝ) < V5_1.Psi 0.4 ∧ V5_1.Psi 0.4 < 0.0413 ∧
    (0.0472 : ℝ) < V5_1.Psi 0.6 ∧ V5_1.Psi 0.6 < 0.0478 := by
  refine' ⟨ _, _, _, _, _ ⟩;
  · rw [ V5_1.Psi_eq_arch ] <;> norm_num [ V5_1.PsiArch ];
    · -- We'll use the exponential property to simplify the expression. Note that $e^{1/10} \approx 1.10517$ and $e^{-1/10} \approx 0.904837$.
      have h_exp : Real.exp (1 / 10) > 1.10517 ∧ Real.exp (1 / 10) < 1.10518 ∧ Real.exp (-1 / 10) > 0.90483 ∧ Real.exp (-1 / 10) < 0.90484 := by
        refine' ⟨ _, _, _, _ ⟩ <;> norm_num [ Real.exp_neg ];
        · -- We can raise both sides to the power of 10 to remove the fraction.
          suffices h_exp : (110517 / 100000 : ℝ) ^ 10 < Real.exp 1 by
            contrapose! h_exp;
            exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 10 );
          exact Real.exp_one_gt_d9.trans_le' <| by norm_num;
        · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
          exact Real.exp_one_lt_d9.trans_le <| by norm_num;
        · rw [ lt_inv_comm₀ ] <;> norm_num;
          · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
            rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            exact Real.exp_one_lt_d9.trans_le <| by norm_num;
          · positivity;
        · rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ];
          · exact lt_of_lt_of_le ( by norm_num [ Finset.sum_range_succ, Nat.factorial ] ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
          · positivity;
      have := V5_2.A_sub_log_pi_bounds; ( have := V5_3.C_bounds; ( have := V5_4.L_point_two; norm_num at * ; nlinarith; ) );
    · exact Real.log_two_gt_d9.trans_le' <| by norm_num;
  · -- Substitute the bounds for $A - \log \pi$, $C$, and $L(0.2)$ into the expression for $\Psi(0.2)$.
    have h_subst : V5_1.Psi 0.2 = 4 * (Real.exp (0.1) + Real.exp (-0.1) - 2) + (0.1) * (V5_1.A - Real.log Real.pi) + (1 / 4) * (V5_1.C - Real.exp (-0.1) * V5_1.L 0.2) := by
      convert V5_1.Psi_eq_arch 0.2 ( by norm_num ) ( ?_ ) using 1;
      · unfold V5_1.PsiArch; norm_num;
      · exact Real.log_two_gt_d9.trans_le' <| by norm_num;
    -- Substitute the bounds for $A - \log \pi$, $C$, and $L(0.2)$ into the expression for $\Psi(0.2)$ and simplify.
    have h_bounds : Real.exp 0.1 < 1.10518 ∧ Real.exp (-0.1) < 0.90484 ∧ V5_1.A - Real.log Real.pi < -5.3720 ∧ V5_1.C < 17.1974 ∧ V5_1.L 0.2 > 16.5671 := by
      refine' ⟨ _, _, _, _, _ ⟩ <;> norm_num [ Real.exp_neg ] at *;
      · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
        rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
        exact Real.exp_one_lt_d9.trans_le <| by norm_num;
      · rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ] at *;
        · exact lt_of_lt_of_le ( by norm_num [ Finset.sum_range_succ, Nat.factorial ] ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
        · positivity;
      · linarith [ V5_2.A_sub_log_pi_bounds ];
      · exact V5_3.C_bounds.2.trans_le <| by norm_num;
      · have := V5_4.L_point_two; norm_num at *; linarith;
    nlinarith [ Real.exp_pos 0.1, Real.exp_pos ( -0.1 ), Real.exp_neg 0.1, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos 0.1 ) ), Real.add_one_le_exp 0.1, Real.add_one_le_exp ( -0.1 ) ];
  · unfold V5_1.Psi;
    unfold V5_1.PsiNonneg;
    unfold V5_1.PsiArch V5_1.primeSum; norm_num [ abs_of_nonneg ] ;
    rw [ show ⌊Real.exp ( 2 / 5 ) ⌋₊ = 1 by
          rw [ Nat.floor_eq_iff ] <;> norm_num [ Real.exp_nonneg ];
          rw [ ← Real.log_lt_log_iff ( by positivity ) ] <;> norm_num;
          exact Real.log_two_gt_d9.trans_le' <| by norm_num ] ; norm_num [ ArithmeticFunction.vonMangoldt ] ; ring_nf ; norm_num [ Real.exp_neg ] at *;
    -- We'll use the fact that $e^{1/5} \approx 1.2214$ and $e^{-1/5} \approx 0.8187$ to simplify the expression.
    have h_exp : 1.2214 < Real.exp (1 / 5) ∧ Real.exp (1 / 5) < 1.2215 := by
      constructor <;> norm_num;
      · -- We can raise both sides to the power of 5 to remove the fraction.
        suffices h_exp : (6107 / 5000 : ℝ) ^ 5 < Real.exp 1 by
          contrapose! h_exp;
          exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 5 );
        exact Real.exp_one_gt_d9.trans_le' <| by norm_num;
      · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
        rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
        exact Real.exp_one_lt_d9.trans_le <| by norm_num;
    have := V5_4.L_point_four;
    have := V5_2.A_sub_log_pi_bounds; ( have := V5_3.C_bounds; ( norm_num at *; nlinarith [ mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 1 / 5 ) ) ) ] ; ) );
  · rw [ V5_1.Psi_eq_arch ] <;> norm_num [ V5_1.PsiArch ];
    · -- Use the bounds for `A - log π`, `C`, and `L(0.4)` to conclude the proof.
      have h_bounds : V5_1.A - Real.log Real.pi < -5.3720 ∧ V5_1.C < 17.1974 ∧ V5_1.L (2 / 5) > 16.3391 := by
        exact ⟨ by linarith [ V5_2.A_sub_log_pi_bounds ], by linarith [ V5_3.C_bounds ], by linarith [ V5_4.L_point_four ] ⟩;
      have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 1 : ℝ ) = ( 1 / 5 ) + ( 1 / 5 ) + ( 1 / 5 ) + ( 1 / 5 ) + ( 1 / 5 ) by ring, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add ] at this ; norm_num at *;
      rw [ Real.exp_neg ];
      field_simp;
      nlinarith [ Real.add_one_le_exp ( 1 / 5 ), pow_pos ( Real.exp_pos ( 1 / 5 ) ) 3, pow_pos ( Real.exp_pos ( 1 / 5 ) ) 4, pow_pos ( Real.exp_pos ( 1 / 5 ) ) 5 ];
    · exact Real.log_two_gt_d9.trans_le' <| by norm_num;
  · rw [ V5_1.Psi_eq_arch ] <;> norm_num;
    · unfold V5_1.PsiArch;
      -- Use the provided bounds for the exponential terms.
      have h_exp_bounds : Real.exp (3 / 10) > 1.349858 ∧ Real.exp (3 / 10) < 1.349859 ∧ Real.exp (-3 / 10) > 0.740818 ∧ Real.exp (-3 / 10) < 0.740819 := by
        refine' ⟨ _, _, _, _ ⟩ <;> norm_num [ Real.exp_neg ];
        · -- We can raise both sides to the power of 10 to remove the fraction.
          suffices h_exp : (674929 / 500000 : ℝ) ^ 10 < Real.exp 3 by
            contrapose! h_exp;
            exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 10 );
          have := Real.exp_one_gt_d9.le ; norm_num1 at * ; rw [ show ( 3 : ℝ ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ];
        · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
          have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 3 : ℝ ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ];
        · rw [ lt_inv_comm₀ ] <;> norm_num;
          · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
            rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show ( 3 : ℝ ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add ] ; nlinarith [ Real.add_one_le_exp 1 ];
          · positivity;
        · rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ];
          · exact lt_of_lt_of_le ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
          · positivity;
      have := V5_4.L_point_six; norm_num at * ; constructor <;> nlinarith [ V5_2.A_sub_log_pi_bounds, V5_3.C_bounds ] ;
    · exact Real.log_two_gt_d9.trans_le' <| by norm_num

/-
The true zeta screw kernel is positive definite on `(0.2,0.4,0.6)`.
-/
theorem true_kernel_grid_margin (x : Fin 3 → ℝ) :
    (0.005 : ℝ) * ∑ i, x i ^ 2 ≤ quadForm M3 x := by
  unfold M3; norm_num [ Fin.sum_univ_succ ] ; ring_nf; norm_num;
  unfold quadForm;
  norm_num [ Fin.sum_univ_succ, V5_1.G ];
  -- By definition of $Psi$, we know that
  have h_psi : V5_1.Psi (1 / 5) = V5_1.Psi 0.2 ∧ V5_1.Psi (2 / 5) = V5_1.Psi 0.4 ∧ V5_1.Psi (3 / 5) = V5_1.Psi 0.6 ∧ V5_1.Psi (-(1 / 5)) = V5_1.Psi 0.2 ∧ V5_1.Psi (-(2 / 5)) = V5_1.Psi 0.4 := by
    norm_num [ V5_1.Psi ];
  have := V5_5.psi_grid_bounds;
  norm_num [ V5_1.Psi_zero ] at *;
  nlinarith [ sq_nonneg ( x 0 + x 1 + x 2 ), sq_nonneg ( x 0 - x 1 ), sq_nonneg ( x 0 - x 2 ), sq_nonneg ( x 1 - x 2 ), mul_self_nonneg ( x 0 + x 1 - x 2 ), mul_self_nonneg ( x 0 - x 1 + x 2 ), mul_self_nonneg ( x 0 + x 1 + x 2 ) ]

/-- The true zeta screw kernel is positive definite on `(0.2,0.4,0.6)`. -/
theorem true_kernel_grid_posdef : IsPDq M3 := by
  intro x hx_nonzero;
  -- By definition of $M3$, we know that $M3 = \sum_{i,j} (Psi(t_i) + Psi(t_j) - Psi(|t_i - t_j|)) * x_i * x_j$.
  have hM3 : quadForm M3 x = 2 * (V5_1.Psi 0.2) * x 0 ^ 2 + 2 * (V5_1.Psi 0.4) * x 1 ^ 2 + 2 * (V5_1.Psi 0.6) * x 2 ^ 2 + 2 * (V5_1.Psi 0.2 + V5_1.Psi 0.4 - V5_1.Psi 0.2) * x 0 * x 1 + 2 * (V5_1.Psi 0.2 + V5_1.Psi 0.6 - V5_1.Psi 0.4) * x 0 * x 2 + 2 * (V5_1.Psi 0.4 + V5_1.Psi 0.6 - V5_1.Psi 0.2) * x 1 * x 2 := by
    unfold M3 quadForm;
    simp +decide [ Fin.sum_univ_three, V5_1.G ] ; ring;
    rw [ show V5_1.Psi ( -1 / 5 ) = V5_1.Psi ( 1 / 5 ) by
          unfold V5_1.Psi; norm_num;, show V5_1.Psi ( -2 / 5 ) = V5_1.Psi ( 2 / 5 ) by
                                                                  unfold V5_1.Psi; norm_num;, show V5_1.Psi 0 = 0 by
                                                                                                                          exact V5_1.Psi_zero ] ; ring;
  by_cases hx0 : x 0 = 0;
  · by_cases hx1 : x 1 = 0 <;> by_cases hx2 : x 2 = 0 <;> simp_all +decide [ funext_iff, Fin.forall_fin_succ ];
    · exact mul_pos ( mul_pos two_pos ( by linarith [ psi_grid_bounds ] ) ) ( sq_pos_of_ne_zero hx2 );
    · exact mul_pos ( mul_pos two_pos ( by linarith [ psi_grid_bounds ] ) ) ( by positivity );
    · have h_pos : 0 < V5_1.Psi 0.4 ∧ 0 < V5_1.Psi 0.6 ∧ V5_1.Psi 0.4 + V5_1.Psi 0.6 - V5_1.Psi 0.2 > 0 := by
        have := V5_5.psi_grid_bounds; norm_num at *; exact ⟨ by linarith, by linarith, by linarith ⟩ ;
      have h_pos : (V5_1.Psi 0.4 + V5_1.Psi 0.6 - V5_1.Psi 0.2) ^ 2 < 4 * V5_1.Psi 0.4 * V5_1.Psi 0.6 := by
        have := V5_5.psi_grid_bounds; norm_num at this; nlinarith;
      nlinarith [ sq_nonneg ( 2 * V5_1.Psi 0.4 * x 1 + ( V5_1.Psi 0.4 + V5_1.Psi 0.6 - V5_1.Psi 0.2 ) * x 2 ), mul_self_pos.2 hx1, mul_self_pos.2 hx2 ];
  · have := psi_grid_bounds;
    nlinarith [ sq_nonneg ( x 0 + x 1 + x 2 ), mul_self_pos.mpr hx0, sq_nonneg ( x 0 - x 1 ), sq_nonneg ( x 0 - x 2 ), sq_nonneg ( x 1 - x 2 ), mul_self_nonneg ( x 0 + x 1 - x 2 ), mul_self_nonneg ( x 0 - x 1 + x 2 ), mul_self_nonneg ( x 1 + x 2 - x 0 ) ]

end V5_5