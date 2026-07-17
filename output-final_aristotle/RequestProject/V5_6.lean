import RequestProject.V5_1
import RequestProject.V5_2
import RequestProject.V5_3
import RequestProject.V5_4
import RequestProject.Horizon

open Horizon

namespace V5_6

noncomputable def M2 : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  let t : Fin 2 → ℝ := ![0.4, 0.9]
  V5_1.G (t i) (t j)

theorem psi_crossing_bounds :
    (0.0408 : ℝ) < V5_1.Psi 0.4 ∧ V5_1.Psi 0.4 < 0.0413 ∧
    (0.0399 : ℝ) < V5_1.Psi 0.5 ∧ V5_1.Psi 0.5 < 0.0405 ∧
    (0.0355 : ℝ) < V5_1.Psi 0.9 ∧ V5_1.Psi 0.9 < 0.0362 := by
  refine' ⟨ _, _, _, _, _ ⟩;
  · rw [ V5_1.Psi_eq_arch ] <;> norm_num;
    · unfold V5_1.PsiArch;
      -- Substitute the numerical bounds for the exponential terms and constants.
      have h_exp_bounds : Real.exp (1 / 5) > 1.221402 ∧ Real.exp (1 / 5) < 1.221403 ∧ Real.exp (-1 / 5) > 0.818730 ∧ Real.exp (-1 / 5) < 0.818731 := by
        refine' ⟨ _, _, _, _ ⟩ <;> norm_num [ Real.exp_neg ];
        · -- We can raise both sides to the power of 5 to remove the fraction.
          suffices h_exp : (610701 / 500000 : ℝ) ^ 5 < Real.exp 1 by
            contrapose! h_exp;
            exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 5 );
          exact Real.exp_one_gt_d9.trans_le' <| by norm_num;
        · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
          exact Real.exp_one_lt_d9.trans_le ( by norm_num );
        · rw [ lt_inv_comm₀ ] <;> norm_num [ Real.exp_pos ];
          rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
          exact Real.exp_one_lt_d9.trans_le ( by norm_num );
        · rw [ inv_lt_comm₀ ] <;> norm_num [ Real.exp_pos ];
          -- We can raise both sides to the power of 5 to remove the reciprocal.
          suffices h_exp : (1000000 / 818731 : ℝ) ^ 5 < Real.exp 1 by
            contrapose! h_exp;
            exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 5 );
          exact Real.exp_one_gt_d9.trans_le' <| by norm_num;
      have := V5_2.A_sub_log_pi_bounds; ( have := V5_3.C_bounds; ( have := V5_4.L_point_four; ( norm_num at * ; nlinarith; ) ) );
    · exact Real.log_two_gt_d9.trans_le' <| by norm_num;
  · rw [ V5_1.Psi_eq_arch ] <;> norm_num;
    · unfold V5_1.PsiArch;
      -- We'll use the fact that $e^{-0.2} \approx 0.818731$ and $e^{0.2} \approx 1.221403$ to simplify the expression.
      have h_exp : Real.exp (-0.2) > 0.818730 ∧ Real.exp (-0.2) < 0.818732 ∧ Real.exp (0.2) > 1.221402 ∧ Real.exp (0.2) < 1.221404 := by
        refine' ⟨ _, _, _, _ ⟩ <;> norm_num [ Real.exp_neg ];
        · rw [ lt_inv_comm₀ ] <;> norm_num;
          · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
            rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
            exact Real.exp_one_lt_d9.trans_le ( by norm_num );
          · positivity;
        · rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ];
          · exact lt_of_lt_of_le ( by norm_num [ Finset.sum_range_succ, Nat.factorial ] ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
          · positivity;
        · -- We can raise both sides to the power of 5 to remove the fraction.
          suffices h_exp : (610701 / 500000 : ℝ) ^ 5 < Real.exp 1 by
            contrapose! h_exp;
            exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 5 );
          exact Real.exp_one_gt_d9.trans_le' <| by norm_num;
        · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
          exact Real.exp_one_lt_d9.trans_le ( by norm_num );
      have := V5_2.A_sub_log_pi_bounds; ( have := V5_3.C_bounds; ( have := V5_4.L_point_four; norm_num at * ; nlinarith; ) );
    · exact Real.log_two_gt_d9.trans_le' <| by norm_num;
  · rw [ V5_1.Psi_eq_arch ] <;> norm_num [ V5_1.PsiArch ];
    · -- We'll use the fact that $e^{1/4} \approx 1.284$ and $e^{-1/4} \approx 0.778$ to approximate the values.
      have h_exp_approx : Real.exp (1 / 4) > 1.284 ∧ Real.exp (1 / 4) < 1.285 ∧ Real.exp (-1 / 4) > 0.778 ∧ Real.exp (-1 / 4) < 0.779 := by
        refine' ⟨ _, _, _, _ ⟩ <;> norm_num [ Real.exp_neg ];
        · -- We can raise both sides to the power of 4 to remove the reciprocal.
          suffices h_exp : (321 / 250 : ℝ) ^ 4 < Real.exp 1 by
            contrapose! h_exp;
            exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 4 );
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
          · exact lt_of_lt_of_le ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
          · positivity;
      have := V5_2.A_sub_log_pi_bounds; ( have := V5_3.C_bounds; ( have := V5_4.L_point_five; norm_num at * ; nlinarith; ) );
    · exact Real.log_two_gt_d9.trans_le' <| by norm_num;
  · rw [ V5_1.Psi_eq_arch ] <;> norm_num;
    · unfold V5_1.PsiArch;
      -- We'll use the fact that $e^{1/4} \approx 1.284$ and $e^{-1/4} \approx 0.779$ to simplify the expression.
      have h_exp : Real.exp (1 / 4) > 1.284025 ∧ Real.exp (1 / 4) < 1.284026 ∧ Real.exp (-1 / 4) > 0.778800 ∧ Real.exp (-1 / 4) < 0.778801 := by
        refine' ⟨ _, _, _, _ ⟩ <;> norm_num [ Real.exp_neg ];
        · -- We can raise both sides to the power of 4 to remove the reciprocal.
          suffices h_exp : (51361 / 40000 : ℝ) ^ 4 < Real.exp 1 by
            contrapose! h_exp;
            exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 4 );
          exact Real.exp_one_gt_d9.trans_le' <| by norm_num;
        · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
          exact Real.exp_one_lt_d9.trans_le ( by norm_num );
        · rw [ lt_inv_comm₀ ] <;> norm_num [ Real.exp_pos ];
          rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
          exact Real.exp_one_lt_d9.trans_le <| by norm_num;
        · rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ];
          · exact lt_of_lt_of_le ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
          · positivity;
      have := V5_4.L_point_five;
      have := V5_2.A_sub_log_pi_bounds; ( have := V5_3.C_bounds; ( norm_num at *; nlinarith; ) );
    · exact Real.log_two_gt_d9.trans_le' <| by norm_num;
  · rw [ V5_1.Psi_first_window ];
    · have h_log2 : 0.693147 < Real.log 2 ∧ Real.log 2 < 0.693148 := by
        exact ⟨ Real.log_two_gt_d9.trans_le' <| by norm_num, Real.log_two_lt_d9.trans_le <| by norm_num ⟩
      have h_sqrt2 : 1.414213 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.414214 := by
        norm_num [ Real.lt_sqrt, Real.sqrt_lt ]
      have h_A_sub_log_pi : -5.3724 < V5_1.A - Real.log Real.pi ∧ V5_1.A - Real.log Real.pi < -5.3720 := by
        convert V5_2.A_sub_log_pi_bounds using 1
      have h_C : 17.1972 < V5_1.C ∧ V5_1.C < 17.1974 := by
        exact V5_3.C_bounds
      have h_L_0_9 : 16.1115 < V5_1.L 0.9 ∧ V5_1.L 0.9 < 16.1118 := by
        exact V5_4.L_point_nine;
      unfold V5_1.PsiArch;
      have h_exp_0_45 : 1.568311 < Real.exp (0.9 / 2) ∧ Real.exp (0.9 / 2) < 1.568313 := by
        constructor <;> norm_num;
        · -- We can raise both sides to the power of 20 to remove the fraction.
          suffices h_exp : (1568311 / 1000000 : ℝ) ^ 20 < Real.exp 9 by
            contrapose! h_exp;
            exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 20 );
          have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 9 = ( Real.exp 1 ) ^ 9 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
        · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
          have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 9 = ( Real.exp 1 ) ^ 9 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
      have h_exp_neg_0_45 : 0.637627 < Real.exp (-0.9 / 2) ∧ Real.exp (-0.9 / 2) < 0.637629 := by
        norm_num [ Real.exp_neg ] at *;
        constructor <;> nlinarith [ Real.exp_pos ( 9 / 20 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 9 / 20 ) ) ) ];
      constructor <;> norm_num at *;
      · field_simp;
        nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_pos ( sub_pos.mpr h_sqrt2.1 ) ( sub_pos.mpr h_exp_0_45.1 ), mul_pos ( sub_pos.mpr h_sqrt2.1 ) ( sub_pos.mpr h_exp_neg_0_45.1 ), mul_pos ( sub_pos.mpr h_exp_0_45.1 ) ( sub_pos.mpr h_exp_neg_0_45.1 ) ];
      · field_simp;
        nlinarith [ mul_pos ( sub_pos.mpr h_exp_0_45.1 ) ( sub_pos.mpr h_exp_neg_0_45.1 ), mul_pos ( sub_pos.mpr h_exp_0_45.1 ) ( sub_pos.mpr h_sqrt2.1 ), mul_pos ( sub_pos.mpr h_exp_neg_0_45.1 ) ( sub_pos.mpr h_sqrt2.1 ) ];
    · exact Real.log_two_lt_d9.le.trans ( by norm_num );
    · norm_num [ Real.lt_log_iff_exp_lt ];
      exact lt_of_le_of_lt ( Real.exp_le_exp.mpr ( show 9 / 10 ≤ 1 by norm_num ) ) ( Real.exp_one_lt_d9.trans_le ( by norm_num ) )

theorem true_kernel_first_prime_posdef : IsPDq M2 := by
  intro x;
  intro hx_ne; by_cases hx0 : x 0 = 0 <;> by_cases hx1 : x 1 = 0 <;> simp_all +decide [ funext_iff, Fin.forall_fin_two ] ;
  · unfold quadForm M2;
    simp_all +decide [ Fin.sum_univ_succ, V5_1.G ];
    have := psi_crossing_bounds; norm_num [ V5_1.Psi_zero ] at *; nlinarith [ mul_self_pos.mpr hx1 ] ;
  · unfold M2; unfold quadForm; norm_num [ Fin.sum_univ_succ, hx0, hx1 ] ;
    unfold V5_1.G; norm_num [ V5_1.Psi_zero ] ; ring_nf; norm_num [ hx0 ] ;
    exact mul_pos ( sq_pos_of_ne_zero hx0 ) ( by linarith [ psi_crossing_bounds ] );
  · -- By definition of $M2$, we know that its entries are given by $G(t_i, t_j)$.
    have hM2 : M2 0 0 = 2 * V5_1.Psi 0.4 ∧ M2 1 1 = 2 * V5_1.Psi 0.9 ∧ M2 0 1 = V5_1.Psi 0.4 + V5_1.Psi 0.9 - V5_1.Psi 0.5 ∧ M2 1 0 = V5_1.Psi 0.4 + V5_1.Psi 0.9 - V5_1.Psi 0.5 := by
      unfold M2 V5_1.G; norm_num [ abs_of_nonneg ] ;
      exact ⟨ by linarith [ V5_1.Psi_zero ], by linarith [ V5_1.Psi_zero ], by unfold V5_1.Psi; norm_num, by ring ⟩;
    -- Substitute the bounds from `psi_crossing_bounds` into the quadratic form.
    have h_bounds : 0.0408 < V5_1.Psi 0.4 ∧ V5_1.Psi 0.4 < 0.0413 ∧ 0.0355 < V5_1.Psi 0.9 ∧ V5_1.Psi 0.9 < 0.0362 ∧ 0.0399 < V5_1.Psi 0.5 ∧ V5_1.Psi 0.5 < 0.0405 := by
      exact ⟨ by linarith [ psi_crossing_bounds.1 ], by linarith [ psi_crossing_bounds.2.1 ], by linarith [ psi_crossing_bounds.2.2.2.2.1 ], by linarith [ psi_crossing_bounds.2.2.2.2.2 ], by linarith [ psi_crossing_bounds.2.2.1 ], by linarith [ psi_crossing_bounds.2.2.2.1 ] ⟩;
    unfold quadForm; norm_num [ hM2 ] ; nlinarith [ mul_self_pos.2 hx0, mul_self_pos.2 hx1, sq_nonneg ( x 0 - x 1 ), sq_nonneg ( x 0 + x 1 ) ] ;

end V5_6