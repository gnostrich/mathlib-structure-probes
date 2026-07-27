import RequestProject.V5_1

namespace V5_4

lemma exp_neg_four_fifths_bounds :
    (0.44932 : ℝ) < Real.exp (-0.8) ∧ Real.exp (-0.8) < 0.44934 := by
  constructor <;> norm_num [ ← Real.exp_eq_exp_ℝ ] at *;
  · -- We can raise both sides to the power of 5 to remove the fraction.
    suffices h_exp : (11233 / 25000 : ℝ) ^ 5 < Real.exp (-4) by
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 5 );
    have := Real.exp_neg_one_gt_d9;
    norm_num1 at *; rw [ show Real.exp ( -4 : ℝ ) = ( Real.exp ( -1 : ℝ ) ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ pow_le_pow_left₀ ( by positivity ) this.le 4 ] ;
  · rw [ Real.exp_neg ];
    rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ] at *;
    · exact lt_of_lt_of_le ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
    · positivity

lemma exp_neg_two_fifths_bounds :
    (0.67031 : ℝ) < Real.exp (-0.4) ∧ Real.exp (-0.4) < 0.67033 := by
  constructor <;> norm_num;
  · -- We can raise both sides to the power of 5 to remove the fraction.
    suffices h_exp : (67031 / 100000 : ℝ) ^ 5 < Real.exp (-2) by
      contrapose! h_exp;
      exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) ( pow_le_pow_left₀ ( by positivity ) h_exp 5 );
    have := Real.exp_neg_one_gt_d9 ; norm_num at * ; rw [ show ( -2 : ℝ ) = -1 + ( -1 ) by norm_num, Real.exp_add ] ; nlinarith [ Real.exp_pos ( -1 ) ];
  · rw [ Real.exp_neg ];
    rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ] at *;
    · exact lt_of_lt_of_le ( by norm_num [ Finset.sum_range_succ, Nat.factorial ] ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
    · positivity

/-
Certified special-value enclosure at `t=0.2`.
-/
theorem L_point_two : (16.5671 : ℝ) < V5_1.L 0.2 ∧ V5_1.L 0.2 < 16.5674 := by
  -- We'll use that $L(0.2)$ is the sum of a geometric series.
  have h_geo_series : V5_1.L 0.2 = ∑' n : ℕ, (Real.exp (-0.4)) ^ n * (1 / ((n : ℝ) + 1 / 4) ^ 2) := by
    exact tsum_congr fun n => by rw [ ← Real.exp_nat_mul ] ; ring;
  -- Let's split the sum into two parts: the sum up to $N=30$ and the sum from $N=31$ to infinity.
  set N := 30
  have h_split : V5_1.L 0.2 = (∑ n ∈ Finset.range (N + 1), (Real.exp (-0.4)) ^ n * (1 / ((n : ℝ) + 1 / 4) ^ 2)) + (∑' n : ℕ, (Real.exp (-0.4)) ^ (n + N + 1) * (1 / ((n + N + 1 : ℝ) + 1 / 4) ^ 2)) := by
    rw [ h_geo_series, ← Summable.sum_add_tsum_nat_add ];
    norm_cast;
    field_simp;
    exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by exact div_le_self ( by positivity ) ( by ring_nf; nlinarith ) ) ( Summable.mul_right _ <| summable_geometric_of_lt_one ( by positivity ) <| by norm_num );
  -- Let's bound the tail of the series.
  have h_tail_bound : (∑' n : ℕ, (Real.exp (-0.4)) ^ (n + N + 1) * (1 / ((n + N + 1 : ℝ) + 1 / 4) ^ 2)) ≤ (Real.exp (-0.4)) ^ (N + 1) / (1 - Real.exp (-0.4)) * (1 / ((N + 1 : ℝ) + 1 / 4) ^ 2) := by
    have h_tail_bound : (∑' n : ℕ, (Real.exp (-0.4)) ^ (n + N + 1) * (1 / ((n + N + 1 : ℝ) + 1 / 4) ^ 2)) ≤ (∑' n : ℕ, (Real.exp (-0.4)) ^ (n + N + 1) * (1 / ((N + 1 : ℝ) + 1 / 4) ^ 2)) := by
      refine' Summable.tsum_le_tsum _ _ _;
      · exact fun n => mul_le_mul_of_nonneg_left ( one_div_le_one_div_of_le ( by positivity ) ( by gcongr ; linarith ) ) ( by positivity );
      · refine' Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => mul_le_of_le_one_right ( by positivity ) <| by rw [ div_le_iff₀ ] <;> ring <;> nlinarith ) _;
        exact Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) ( by norm_num ) ) fun a b h => by simpa using h;
      · exact Summable.mul_right _ ( Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) ( by norm_num ) ) fun a b h => by simpa using h );
    convert h_tail_bound using 1;
    norm_num [ pow_add, tsum_mul_right ];
    rw [ tsum_geometric_of_lt_one ( by positivity ) ( by norm_num ) ] ; ring;
  -- Let's bound the finite sum.
  have h_finite_sum_bound : (∑ n ∈ Finset.range (N + 1), (Real.exp (-0.4)) ^ n * (1 / ((n : ℝ) + 1 / 4) ^ 2)) ≥ (∑ n ∈ Finset.range (N + 1), (0.67031 : ℝ) ^ n * (1 / ((n : ℝ) + 1 / 4) ^ 2)) ∧ (∑ n ∈ Finset.range (N + 1), (Real.exp (-0.4)) ^ n * (1 / ((n : ℝ) + 1 / 4) ^ 2)) ≤ (∑ n ∈ Finset.range (N + 1), (0.67033 : ℝ) ^ n * (1 / ((n : ℝ) + 1 / 4) ^ 2)) := by
    have h_exp_bounds : 0.67031 < Real.exp (-0.4) ∧ Real.exp (-0.4) < 0.67033 := by
      convert V5_4.exp_neg_two_fifths_bounds using 1;
    exact ⟨ Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by norm_num ) h_exp_bounds.1.le _ ) ( by positivity ), Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) h_exp_bounds.2.le _ ) ( by positivity ) ⟩;
  -- Let's bound the tail of the series using the geometric series sum formula.
  have h_tail_bound : (Real.exp (-0.4)) ^ (N + 1) / (1 - Real.exp (-0.4)) * (1 / ((N + 1 : ℝ) + 1 / 4) ^ 2) < 0.00001 := by
    have := exp_neg_two_fifths_bounds;
    rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> norm_num at * ; nlinarith [ pow_le_pow_left₀ ( by positivity ) this.2.le 31 ];
  constructor <;> norm_num at *; all_goals linarith [ show ( 0 : ℝ ) ≤ ∑' n : ℕ, Real.exp ( - ( 2 / 5 ) ) ^ ( n + 30 + 1 ) * ( ( n + 30 + 1 + 1 / 4 ) ^ 2 : ℝ ) ⁻¹ by exact tsum_nonneg fun _ => by positivity ]

/-
Certified special-value enclosure at `t=0.4`.
-/
theorem L_point_four : (16.3391 : ℝ) < V5_1.L 0.4 ∧ V5_1.L 0.4 < 16.3394 := by
  constructor;
  · norm_num [ V5_1.L ];
    refine' lt_of_lt_of_le _ ( Summable.sum_le_tsum ( Finset.range 100 ) ( fun _ _ => by positivity ) _ );
    · -- We'll use the fact that $e^{-0.8} \approx 0.449329$ to approximate the sum.
      have h_exp_approx : Real.exp (-0.8) > 0.44932 := by
        exact V5_4.exp_neg_four_fifths_bounds.1;
      -- We'll use the fact that $e^{-0.8} \approx 0.449329$ to approximate the sum. Let's calculate the sum up to $n = 99$.
      have h_sum_approx : ∑ i ∈ Finset.range 100, (Real.exp (-0.8)) ^ i * ((i + 1 / 4 : ℝ) ^ 2)⁻¹ > 163391 / 10000 := by
        refine' lt_of_lt_of_le _ ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) h_exp_approx.le _ ) ( by positivity ) ) ; norm_num;
      convert h_sum_approx.lt using 2 ; norm_num [ ← Real.exp_nat_mul ] ; ring;
      norm_num;
    · convert V5_1.summable_L ( 2 / 5 ) ( by norm_num ) using 2 ; ring;
  · -- Split the sum at N=16.
    have h_split : V5_1.L 0.4 = ∑ n ∈ Finset.range 16, Real.exp (-2 * n * 0.4) * (1 / ((n : ℝ) + 1 / 4) ^ 2) + ∑' n : ℕ, Real.exp (-2 * (n + 16) * 0.4) * (1 / ((n + 16 : ℝ) + 1 / 4) ^ 2) := by
      unfold V5_1.L;
      rw [ ← Summable.sum_add_tsum_nat_add ] ; norm_cast;
      convert V5_1.summable_L 0.4 ( by norm_num ) using 1;
    -- Bound the tail sum.
    have h_tail : ∑' n : ℕ, Real.exp (-2 * (n + 16) * 0.4) * (1 / ((n + 16 : ℝ) + 1 / 4) ^ 2) ≤ Real.exp (-2 * 16 * 0.4) * (1 / ((16 : ℝ) + 1 / 4) ^ 2) / (1 - Real.exp (-2 * 0.4)) := by
      have h_tail_bound : ∀ n : ℕ, Real.exp (-2 * (n + 16) * 0.4) * (1 / ((n + 16 : ℝ) + 1 / 4) ^ 2) ≤ Real.exp (-2 * 16 * 0.4) * (1 / ((16 : ℝ) + 1 / 4) ^ 2) * (Real.exp (-2 * 0.4)) ^ n := by
        intro n; rw [ ← Real.exp_nat_mul ] ; ring_nf; norm_num;
        rw [ ← Real.exp_add ] ; ring_nf ; norm_num;
        exact mul_le_mul_of_nonneg_left ( by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> nlinarith ) ( by positivity );
      refine' le_trans ( Summable.tsum_le_tsum h_tail_bound _ _ ) _;
      · exact Summable.of_nonneg_of_le ( fun n => by positivity ) h_tail_bound <| Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by norm_num [ Real.exp_lt_one_iff ] ;
      · exact Summable.mul_left _ ( summable_geometric_of_lt_one ( by positivity ) ( by norm_num [ Real.exp_lt_one_iff ] ) );
      · rw [ tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( by norm_num [ Real.exp_lt_one_iff ] ) ] ; ring_nf ; norm_num;
    -- Substitute the bounds from h_exp and h_tail into the expression.
    have h_final : V5_1.L 0.4 < ∑ n ∈ Finset.range 16, (0.44934 : ℝ) ^ n * (1 / ((n : ℝ) + 1 / 4) ^ 2) + (0.44934 ^ 16 * (1 / ((16 : ℝ) + 1 / 4) ^ 2)) / (1 - 0.44934) := by
      refine' h_split.symm ▸ add_lt_add_of_le_of_lt _ _;
      · gcongr;
        rename_i i hi;
        convert pow_le_pow_left₀ ( by positivity ) ( show Real.exp ( -0.8 ) ≤ 0.44934 by exact le_of_lt ( by have := V5_4.exp_neg_four_fifths_bounds; norm_num at *; linarith ) ) i using 1 ; rw [ ← Real.exp_nat_mul ] ; ring;
      · refine' lt_of_le_of_lt h_tail _;
        gcongr <;> norm_num [ Real.exp_neg ] at *;
        · rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ] at *;
          · exact lt_of_lt_of_le ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 100 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
          · positivity;
        · rw [ inv_le_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ] at *;
          · exact le_trans ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
          · positivity;
    exact h_final.trans_le <| by norm_num;

/-
Certified special-value enclosure at `t=0.6`.
-/
theorem L_point_six : (16.2137 : ℝ) < V5_1.L 0.6 ∧ V5_1.L 0.6 < 16.2140 := by
  -- We'll use the fact that $e^{-1.2}$ is approximately $0.3011$ to simplify the expression.
  have h_exp : 0.3011 < Real.exp (-1.2) ∧ Real.exp (-1.2) < 0.3013 := by
    constructor <;> norm_num [ Real.exp_neg ];
    · rw [ lt_inv_comm₀ ] <;> norm_num;
      · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
        rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
        have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 6 = ( Real.exp 1 ) ^ 6 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
      · positivity;
    · rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ];
      · exact lt_of_lt_of_le ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
      · positivity;
  -- Split the sum into the first 10 terms and the rest.
  have h_split : V5_1.L 0.6 = (∑ n ∈ Finset.range 10, (Real.exp (-1.2)) ^ n * (1 / ((n : ℝ) + 1 / 4) ^ 2)) + (∑' n : ℕ, (Real.exp (-1.2)) ^ (n + 10) * (1 / ((n + 10 : ℝ) + 1 / 4) ^ 2)) := by
    unfold V5_1.L; norm_num [ mul_assoc, ← mul_pow ] ; rw [ ← Summable.sum_add_tsum_nat_add ] ; norm_cast;
    congr! 2;
    · rw [ ← Real.exp_nat_mul ] ; ring;
    · exact funext fun n => by rw [ ← Real.exp_nat_mul ] ; push_cast; ring;
    · convert V5_1.summable_L ( 3 / 5 ) ( by norm_num ) using 2 ; ring;
  -- Bound the second sum using the geometric series formula.
  have h_second_sum : (∑' n : ℕ, (Real.exp (-1.2)) ^ (n + 10) * (1 / ((n + 10 : ℝ) + 1 / 4) ^ 2)) ≤ (Real.exp (-1.2)) ^ 10 * (1 / ((10 : ℝ) + 1 / 4) ^ 2) / (1 - Real.exp (-1.2)) := by
    have h_second_sum : (∑' n : ℕ, (Real.exp (-1.2)) ^ (n + 10) * (1 / ((n + 10 : ℝ) + 1 / 4) ^ 2)) ≤ (∑' n : ℕ, (Real.exp (-1.2)) ^ (n + 10) * (1 / ((10 : ℝ) + 1 / 4) ^ 2)) := by
      refine' Summable.tsum_le_tsum _ _ _;
      · exact fun n => mul_le_mul_of_nonneg_left ( one_div_le_one_div_of_le ( by positivity ) ( by ring_nf; nlinarith ) ) ( by positivity );
      · exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => mul_le_of_le_one_right ( by positivity ) <| by rw [ div_le_iff₀ ] <;> ring <;> nlinarith ) <| Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) <| by linarith ) <| by intros a b; aesop;
      · exact Summable.mul_right _ ( Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) ( by linarith ) ) ( by intros a b; aesop ) );
    convert h_second_sum using 1;
    ring;
    rw [ tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( by norm_num ) ];
  constructor <;> norm_num [ Finset.sum_range_succ ] at *;
  · nlinarith [ pow_pos ( sub_pos.mpr h_exp.1 ) 2, pow_pos ( sub_pos.mpr h_exp.1 ) 3, pow_pos ( sub_pos.mpr h_exp.1 ) 4, pow_pos ( sub_pos.mpr h_exp.1 ) 5, pow_pos ( sub_pos.mpr h_exp.1 ) 6, pow_pos ( sub_pos.mpr h_exp.1 ) 7, pow_pos ( sub_pos.mpr h_exp.1 ) 8, pow_pos ( sub_pos.mpr h_exp.1 ) 9, pow_pos ( sub_pos.mpr h_exp.1 ) 10, show ( 0 : ℝ ) ≤ ∑' n : ℕ, Real.exp ( - ( 6 / 5 ) ) ^ ( n + 10 ) * ( ( n + 10 + 1 / 4 ) ^ 2 : ℝ ) ⁻¹ from tsum_nonneg fun _ => by positivity ];
  · rw [ le_div_iff₀ ] at h_second_sum <;> nlinarith [ pow_pos ( sub_pos.mpr h_exp.2 ) 2, pow_pos ( sub_pos.mpr h_exp.2 ) 3, pow_pos ( sub_pos.mpr h_exp.2 ) 4, pow_pos ( sub_pos.mpr h_exp.2 ) 5, pow_pos ( sub_pos.mpr h_exp.2 ) 6, pow_pos ( sub_pos.mpr h_exp.2 ) 7, pow_pos ( sub_pos.mpr h_exp.2 ) 8, pow_pos ( sub_pos.mpr h_exp.2 ) 9 ]

/-
Certified special-value enclosure at `t=0.5`.
-/
theorem L_point_five : (16.2681 : ℝ) < V5_1.L 0.5 ∧ V5_1.L 0.5 < 16.2684 := by
  constructor <;> norm_num [ V5_1.L ] at *;
  · refine' lt_of_lt_of_le _ ( Summable.sum_le_tsum ( Finset.range 100 ) ( fun _ _ => by positivity ) _ );
    · norm_num [ Real.exp_neg, mul_assoc, mul_comm, mul_left_comm ] at *;
      -- We'll use the fact that $e^x$ is strictly increasing to bound the terms involving $e^x$.
      have h_exp_bounds : ∀ x : ℕ, Real.exp x ≥ 2.71828 ^ x ∧ Real.exp x ≤ 2.71829 ^ x := by
        intro x; exact ⟨ by exact le_trans ( pow_le_pow_left₀ ( by norm_num ) ( show ( 2.71828 : ℝ ) ≤ Real.exp 1 by exact Real.exp_one_gt_d9.le.trans' <| by norm_num ) _ ) <| by norm_num [ ← Real.exp_nat_mul ], by exact le_trans ( by norm_num [ ← Real.exp_nat_mul ] ) <| pow_le_pow_left₀ ( by positivity ) ( show ( Real.exp 1 : ℝ ) ≤ 2.71829 by exact Real.exp_one_lt_d9.le.trans <| by norm_num ) _ ⟩ ;
      refine' lt_of_lt_of_le _ ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( h_exp_bounds i |>.2 ) ) ( by positivity ) ) ; norm_num;
    · convert V5_1.summable_L ( 1 / 2 ) ( by norm_num ) using 2 ; ring;
  · -- We'll use the fact that $\sum_{n=8}^{\infty} \frac{e^{-n}}{(n+1/4)^2}$ is very small.
    have h_tail : ∑' n : ℕ, (Real.exp (-(n + 8 : ℝ)) * (1 / ((n + 8 + 1 / 4 : ℝ) ^ 2))) < 1 / 10000 := by
      -- We'll use the fact that $\sum_{n=8}^{\infty} \frac{e^{-n}}{(n+1/4)^2}$ is very small. We can bound it above by a geometric series.
      have h_geo_series : ∑' n : ℕ, (Real.exp (-(n + 8 : ℝ)) * (1 / ((n + 8 + 1 / 4 : ℝ) ^ 2))) ≤ ∑' n : ℕ, (Real.exp (-(n + 8 : ℝ)) * (1 / ((8 + 1 / 4 : ℝ) ^ 2))) := by
        refine' Summable.tsum_le_tsum _ _ _;
        · exact fun i => mul_le_mul_of_nonneg_left ( one_div_le_one_div_of_le ( by positivity ) ( by gcongr ; linarith ) ) ( by positivity );
        · exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => mul_le_of_le_one_right ( by positivity ) <| div_le_one_of_le₀ ( by ring_nf; nlinarith ) <| by positivity ) <| by simpa [ Real.exp_add, Real.exp_neg ] using Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| inv_lt_one_of_one_lt₀ <| Real.exp_one_gt_d9.trans_le' <| by norm_num;
        · exact Summable.mul_right _ <| by simpa [ Real.exp_add, Real.exp_neg ] using Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| inv_lt_one_of_one_lt₀ <| Real.exp_one_gt_d9.trans_le' <| by norm_num;
      -- We'll use the fact that $\sum_{n=8}^{\infty} e^{-n}$ is a geometric series with the first term $e^{-8}$ and common ratio $e^{-1}$.
      have h_geo_series_sum : ∑' n : ℕ, Real.exp (-(n + 8 : ℝ)) = Real.exp (-8) / (1 - Real.exp (-1)) := by
        rw [ div_eq_mul_inv, ← tsum_geometric_of_lt_one ( by positivity ) ( by norm_num ) ];
        rw [ ← tsum_mul_left ] ; exact tsum_congr fun n => by rw [ ← Real.exp_nat_mul ] ; rw [ ← Real.exp_add ] ; ring;
      refine lt_of_le_of_lt h_geo_series ?_;
      rw [ tsum_mul_right, h_geo_series_sum ] ; norm_num [ Real.exp_neg ];
      field_simp;
      rw [ show Real.exp 8 = ( Real.exp 1 ) ^ 8 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; have := Real.exp_one_gt_d9.le ; norm_num1 at * ; nlinarith [ pow_le_pow_left₀ ( by positivity ) this 7, pow_le_pow_left₀ ( by positivity ) this 8 ];
    rw [ ← Summable.sum_add_tsum_nat_add 8 ];
    · norm_num [ Finset.sum_range_succ ] at *;
      have := Real.exp_neg_one_lt_d9 ; norm_num1 at * ; rw [ show ( -2:ℝ ) = -1 + ( -1 ) by norm_num, show ( -3:ℝ ) = -1 + ( -1 ) + ( -1 ) by norm_num, show ( -4:ℝ ) = -1 + ( -1 ) + ( -1 ) + ( -1 ) by norm_num, show ( -5:ℝ ) = -1 + ( -1 ) + ( -1 ) + ( -1 ) + ( -1 ) by norm_num, show ( -6:ℝ ) = -1 + ( -1 ) + ( -1 ) + ( -1 ) + ( -1 ) + ( -1 ) by norm_num, show ( -7:ℝ ) = -1 + ( -1 ) + ( -1 ) + ( -1 ) + ( -1 ) + ( -1 ) + ( -1 ) by norm_num, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add ] ; ring_nf at * ; norm_num at *;
      rw [ show Real.exp ( -5 ) = ( Real.exp ( -1 ) ) ^ 5 by rw [ ← Real.exp_nat_mul ] ; norm_num, show Real.exp ( -6 ) = ( Real.exp ( -1 ) ) ^ 6 by rw [ ← Real.exp_nat_mul ] ; norm_num, show Real.exp ( -7 ) = ( Real.exp ( -1 ) ) ^ 7 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ Real.exp_pos ( -1 ), pow_pos ( Real.exp_pos ( -1 ) ) 2, pow_pos ( Real.exp_pos ( -1 ) ) 3, pow_pos ( Real.exp_pos ( -1 ) ) 4, pow_pos ( Real.exp_pos ( -1 ) ) 5, pow_pos ( Real.exp_pos ( -1 ) ) 6, pow_pos ( Real.exp_pos ( -1 ) ) 7 ] ;
    · have := V5_1.summable_L ( 1 / 2 ) ( by norm_num );
      aesop

/-
Certified special-value enclosure at `t=0.9`.
-/
theorem L_point_nine : (16.1115 : ℝ) < V5_1.L 0.9 ∧ V5_1.L 0.9 < 16.1118 := by
  -- Split the sum into the first 8 terms and the rest.
  have h_split : V5_1.L 0.9 = ∑ n ∈ Finset.range 8, Real.exp (-(2 * n * 0.9)) * (1 / ((n : ℝ) + 1 / 4) ^ 2) + ∑' n : ℕ, Real.exp (-(2 * (n + 8) * 0.9)) * (1 / ((n + 8 : ℝ) + 1 / 4) ^ 2) := by
    unfold V5_1.L; rw [ ← Summable.sum_add_tsum_nat_add ] ; norm_num;
    congr! 2;
    convert V5_1.summable_L 0.9 ( by norm_num ) using 1;
  -- Bound the tail sum using a geometric series.
  have h_tail_bound : ∑' n : ℕ, Real.exp (-(2 * (n + 8) * 0.9)) * (1 / ((n + 8 : ℝ) + 1 / 4) ^ 2) ≤ Real.exp (-(16 * 0.9)) * (1 / ((8 : ℝ) + 1 / 4) ^ 2) / (1 - Real.exp (-(2 * 0.9))) := by
    have h_tail_bound : ∀ n : ℕ, Real.exp (-(2 * (n + 8) * 0.9)) * (1 / ((n + 8 : ℝ) + 1 / 4) ^ 2) ≤ Real.exp (-(16 * 0.9)) * (1 / ((8 : ℝ) + 1 / 4) ^ 2) * (Real.exp (-(2 * 0.9))) ^ n := by
      intro n; rw [ ← Real.exp_nat_mul ] ; ring_nf; norm_num;
      rw [ ← Real.exp_add ] ; exact mul_le_mul ( by norm_num ) ( by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> nlinarith ) ( by positivity ) ( by positivity );
    refine' le_trans ( Summable.tsum_le_tsum h_tail_bound _ _ ) _;
    · exact Summable.of_nonneg_of_le ( fun n => by positivity ) h_tail_bound <| Summable.mul_left _ <| summable_geometric_of_lt_one ( by positivity ) <| by norm_num [ Real.exp_lt_one_iff ] ;
    · exact Summable.mul_left _ ( summable_geometric_of_lt_one ( by positivity ) ( by norm_num [ Real.exp_lt_one_iff ] ) );
    · rw [ tsum_mul_left, tsum_geometric_of_lt_one ( by positivity ) ( by norm_num [ Real.exp_lt_one_iff ] ) ] ; ring_nf ; norm_num;
  -- We'll use the fact that $e^{-1.8} \approx 0.1653$ to simplify the expression.
  have h_exp : Real.exp (-1.8) > 0.1652 ∧ Real.exp (-1.8) < 0.1654 := by
    constructor <;> norm_num [ Real.exp_neg ];
    · rw [ lt_inv_comm₀ ] <;> norm_num;
      · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
        rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
        have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 9 = ( Real.exp 1 ) ^ 9 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
      · positivity;
    · rw [ inv_lt_comm₀, Real.exp_eq_exp_ℝ ] <;> norm_num [ NormedSpace.exp_eq_tsum_div ];
      · exact lt_of_lt_of_le ( by norm_num [ Finset.sum_range_succ, Nat.factorial ] ) ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
      · positivity;
  norm_num [ Finset.sum_range_succ, Real.exp_neg ] at *;
  constructor;
  · rw [ h_split ];
    refine' lt_add_of_lt_of_nonneg _ ( tsum_nonneg fun _ => by positivity );
    rw [ show ( 18 / 5 : ℝ ) = 9 / 5 + 9 / 5 by norm_num, show ( 27 / 5 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 by norm_num, show ( 36 / 5 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 by norm_num, show ( 9 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 by norm_num, show ( 54 / 5 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 by norm_num, show ( 63 / 5 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 by norm_num, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add ] ; norm_num;
    nlinarith [ pow_pos ( sub_pos.mpr h_exp.1 ) 2, pow_pos ( sub_pos.mpr h_exp.1 ) 3, pow_pos ( sub_pos.mpr h_exp.1 ) 4, inv_pos.mpr ( Real.exp_pos 9 ), inv_pos.mpr ( Real.exp_pos ( 54 / 5 ) ), inv_pos.mpr ( Real.exp_pos ( 63 / 5 ) ) ];
  · rw [ show ( 72 / 5 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 by norm_num, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add ] at * ; norm_num at *;
    rw [ show ( 18 / 5 : ℝ ) = 9 / 5 + 9 / 5 by norm_num, Real.exp_add ] at * ; norm_num at *;
    rw [ show ( 27 / 5 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 by norm_num, Real.exp_add, Real.exp_add ] at * ; norm_num at *;
    rw [ show ( 36 / 5 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 by norm_num, Real.exp_add, Real.exp_add, Real.exp_add ] at * ; norm_num at *;
    rw [ show ( 54 / 5 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 by norm_num, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add ] at * ; norm_num at *;
    rw [ show ( 63 / 5 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 by norm_num, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add ] at * ; norm_num at *;
    rw [ show ( 9 : ℝ ) = 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 + 9 / 5 by norm_num, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add ] at * ; norm_num at *;
    rw [ le_div_iff₀ ] at h_tail_bound <;> nlinarith [ pow_pos ( sub_pos.mpr h_exp.2 ) 2, pow_pos ( sub_pos.mpr h_exp.2 ) 3, pow_pos ( sub_pos.mpr h_exp.2 ) 4, pow_pos ( sub_pos.mpr h_exp.2 ) 5, pow_pos ( sub_pos.mpr h_exp.2 ) 6, pow_pos ( sub_pos.mpr h_exp.2 ) 7, pow_pos ( sub_pos.mpr h_exp.2 ) 8 ]

end V5_4