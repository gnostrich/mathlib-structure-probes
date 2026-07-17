import Mathlib
import RequestProject.G1
import RequestProject.V5_1

namespace V5_2

lemma corrected_harmonic_lower (n : ℕ) (hn : 0 < n) :
    (harmonic n : ℝ) - Real.log n - 1 / (2 * n) <
      Real.eulerMascheroniConstant := by
  -- By definition of $a_n$, we know that $a_n$ is strictly increasing for $n > 0$.
  have h_inc : StrictMonoOn (fun n : ℕ => (harmonic n : ℝ) - Real.log n - 1 / (2 * n)) {n : ℕ | 0 < n} := by
    -- We'll use the fact that $a_{n+1} - a_n > 0$ to show that the sequence is strictly increasing.
    have h_diff_pos : ∀ n : ℕ, 0 < n → ((harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1))) - ((harmonic n : ℝ) - Real.log n - 1 / (2 * n)) > 0 := by
      intro n hn; norm_num [ harmonic ] ; ring_nf; norm_num [ hn.ne' ] ;
      -- We'll use the fact that $\log(1 + x) < x - \frac{x^2}{2(1+x)}$ for $x > 0$.
      have h_log_ineq : ∀ x : ℝ, 0 < x → Real.log (1 + x) < x - x^2 / (2 * (1 + x)) := by
        -- Let's choose any $x > 0$ and derive the inequality.
        intro x hx_pos
        have h_deriv : ∀ y ∈ Set.Ioo 0 x, deriv (fun y => Real.log (1 + y) - y + y^2 / (2 * (1 + y))) y < 0 := by
          intro y hy; norm_num [ add_comm, show y + 1 ≠ 0 from by linarith [ hy.1 ] ];
          rw [ inv_eq_one_div, div_sub_one, div_add_div, div_lt_iff₀ ] <;> nlinarith [ hy.1, hy.2, pow_pos hy.1 3 ];
        -- Apply the mean value theorem to the interval $[0, x]$.
        obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 x, deriv (fun y => Real.log (1 + y) - y + y^2 / (2 * (1 + y))) c = (Real.log (1 + x) - x + x^2 / (2 * (1 + x)) - (Real.log (1 + 0) - 0 + 0^2 / (2 * (1 + 0)))) / (x - 0) := by
          have := exists_deriv_eq_slope ( f := fun y => Real.log ( 1 + y ) - y + y ^ 2 / ( 2 * ( 1 + y ) ) ) hx_pos;
          exact this ( ContinuousOn.add ( ContinuousOn.sub ( ContinuousOn.log ( continuousOn_const.add continuousOn_id ) fun y hy => by linarith [ hy.1 ] ) continuousOn_id ) ( ContinuousOn.div ( continuousOn_pow 2 ) ( continuousOn_const.mul ( continuousOn_const.add continuousOn_id ) ) fun y hy => by linarith [ hy.1 ] ) ) ( fun y hy => DifferentiableAt.differentiableWithinAt ( by norm_num [ add_comm, show y + 1 ≠ 0 from by linarith [ hy.1 ] ] ) );
        have := h_deriv c hc.1; rw [ hc.2, div_lt_iff₀ ] at this <;> norm_num at * <;> linarith;
      have := h_log_ineq ( 1 / n ) ( by positivity ) ; simp_all +decide [ add_comm, Finset.sum_range_succ ];
      field_simp at this ⊢;
      rw [ Real.log_div ( by positivity ) ( by positivity ) ] at this ; ring_nf at this ⊢ ; nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ n ) ];
    intro m hm n hn hmn; induction hmn <;> norm_num at *;
    · exact h_diff_pos m hm;
    · grind;
  -- Since $a_n$ is strictly increasing and converges to $\gamma$, we have $a_n < \gamma$ for all $n > 0$.
  have h_lt_gamma : Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - 1 / (2 * n)) Filter.atTop (nhds (Real.eulerMascheroniConstant)) := by
    simpa using Filter.Tendsto.sub ( Real.tendsto_harmonic_sub_log ) ( tendsto_inv_atTop_zero.mul_const ( 1 / 2 : ℝ ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
  exact lt_of_lt_of_le ( h_inc ( show 0 < n by linarith ) ( show 0 < n + 1 by linarith ) ( Nat.lt_succ_self _ ) ) ( le_of_tendsto_of_tendsto tendsto_const_nhds h_lt_gamma <| Filter.eventually_atTop.mpr ⟨ n + 1, fun m hm => h_inc.monotoneOn ( show 0 < n + 1 by linarith ) ( show 0 < m by linarith ) hm ⟩ )

lemma corrected_harmonic_upper (n : ℕ) (hn : 0 < n) :
    Real.eulerMascheroniConstant <
      (harmonic n : ℝ) - Real.log n - 1 / (2 * (n + 1)) := by
  -- By definition of $b_n$, we know that $b_n$ is decreasing and converges to $\gamma$.
  have h_decreasing : ∀ n : ℕ, 0 < n → (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 2)) < (harmonic n : ℝ) - Real.log n - 1 / (2 * (n + 1)) := by
    intros n hn
    have h_log : Real.log (n + 1) = Real.log n + Real.log (1 + 1 / n) := by
      rw [ ← Real.log_mul ( by positivity ) ( by positivity ), mul_add, mul_one_div_cancel ( by positivity ), mul_one ]
    have h_log_approx : Real.log (1 + 1 / n) > 2 / (2 * n + 1) := by
      have h_log_approx : ∀ x : ℝ, 0 < x → Real.log (1 + x) > 2 * x / (1 + x + 1) := by
        intros x hx_pos
        have h_log_approx : ∀ x : ℝ, 0 < x → deriv (fun x => Real.log (1 + x) - 2 * x / (1 + x + 1)) x > 0 := by
          intro x hx_pos; norm_num [ add_comm, mul_comm, ne_of_gt, add_pos, hx_pos ];
          rw [ inv_eq_one_div, div_lt_div_iff₀ ] <;> nlinarith only [ hx_pos ];
        -- Apply the mean value theorem to the interval $[0, x]$.
        obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 x, deriv (fun x => Real.log (1 + x) - 2 * x / (1 + x + 1)) c = (Real.log (1 + x) - 2 * x / (1 + x + 1) - (Real.log (1 + 0) - 2 * 0 / (1 + 0 + 1))) / (x - 0) := by
          have := exists_deriv_eq_slope ( f := fun x => Real.log ( 1 + x ) - 2 * x / ( 1 + x + 1 ) ) hx_pos;
          exact this ( continuousOn_of_forall_continuousAt fun y hy => by exact ContinuousAt.sub ( ContinuousAt.log ( continuousAt_const.add continuousAt_id ) ( by linarith [ hy.1 ] ) ) ( ContinuousAt.div ( continuousAt_const.mul continuousAt_id ) ( continuousAt_const.add continuousAt_id |> ContinuousAt.add <| continuousAt_const ) ( by linarith [ hy.1 ] ) ) ) ( fun y hy => by exact DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.log ( differentiableAt_id.const_add _ ) ( by linarith [ hy.1 ] ) ) ( DifferentiableAt.div ( differentiableAt_id.const_mul _ ) ( differentiableAt_id.const_add _ |> DifferentiableAt.add <| differentiableAt_const _ ) ( by linarith [ hy.1 ] ) ) ) );
        have := h_log_approx c hc.1.1; rw [ hc.2, div_eq_mul_inv ] at this; aesop;
      convert h_log_approx ( 1 / n ) ( by positivity ) using 1 ; ring;
      field_simp
      ring
    have h_reciprocal : 1 / (2 * (n + 2) : ℝ) < 1 / (2 * (n + 1) : ℝ) := by
      gcongr ; linarith
    have h_diff : (harmonic (n + 1) : ℝ) - (harmonic n : ℝ) = 1 / (n + 1 : ℝ) := by
      simp +decide [ harmonic, Finset.sum_range_succ ]
    simp_all +decide [ add_assoc, add_left_comm, add_comm ];
    rw [ div_lt_iff₀ ] at h_log_approx <;> norm_num at * <;> nlinarith [ inv_mul_cancel₀ ( by positivity : ( n : ℝ ) + 1 ≠ 0 ), inv_mul_cancel₀ ( by positivity : ( n : ℝ ) + 2 ≠ 0 ) ];
  -- By definition of $b_n$, we know that $b_n$ converges to $\gamma$.
  have h_converges : Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - 1 / (2 * (n + 1))) Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have h_converges : Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) Filter.atTop (nhds Real.eulerMascheroniConstant) := by
      convert Real.tendsto_harmonic_sub_log using 1;
    simpa using h_converges.sub ( tendsto_one_div_add_atTop_nhds_zero_nat.mul tendsto_const_nhds );
  refine' lt_of_le_of_lt ( le_of_tendsto h_converges _ ) ( h_decreasing n hn );
  refine' Filter.eventually_atTop.mpr ⟨ n + 1, fun m hm => _ ⟩ ; induction hm <;> norm_num at *;
  · ring_nf; norm_num;
  · grind +splitIndPred

lemma log_ten_bounds : (2.302585 : ℝ) < Real.log 10 ∧ Real.log 10 < 2.302586 := by
  constructor
  · rw [Real.lt_log_iff_exp_lt (by norm_num)]
    rw [show (2.302585 : ℝ) = 2 + 0.302585 by norm_num, Real.exp_add,
      show Real.exp (2 : ℝ) = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (0.302585 : ℝ) < 1.3533528 := by
      have h := Real.exp_bound' (x := (0.302585 : ℝ)) (by norm_num) (by norm_num)
        (n := 12) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
      linarith
    calc
      Real.exp 1 ^ 2 * Real.exp 0.302585 <
          (2.7182818286 : ℝ)^2 * Real.exp 0.302585 :=
        mul_lt_mul_of_pos_right (pow_lt_pow_left₀ h1 (by positivity) (by norm_num))
          (by positivity)
      _ < (2.7182818286 : ℝ)^2 * 1.3533528 :=
        mul_lt_mul_of_pos_left h2 (by positivity)
      _ < 10 := by norm_num
  · rw [Real.log_lt_iff_lt_exp (by norm_num)]
    rw [show (2.302586 : ℝ) = 2 + 0.302586 by norm_num, Real.exp_add,
      show Real.exp (2 : ℝ) = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
    have h1 := Real.exp_one_gt_d9
    have h2 : (1.353353 : ℝ) < Real.exp (0.302586 : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      apply lt_of_lt_of_le
        (b := ∑ m ∈ Finset.range 10, (0.302586 : ℝ) ^ m / m.factorial)
      · norm_num [Finset.sum_range_succ, Nat.factorial]
      · exact Summable.sum_le_tsum _ (fun _ _ => by positivity)
          (Real.summable_pow_div_factorial _)
    calc
      (10 : ℝ) < (2.7182818283 : ℝ)^2 * 1.353353 := by norm_num
      _ < Real.exp 1 ^ 2 * 1.353353 :=
        mul_lt_mul_of_pos_right (pow_lt_pow_left₀ h1 (by positivity) (by norm_num))
          (by norm_num)
      _ < Real.exp 1 ^ 2 * Real.exp 0.302586 :=
        mul_lt_mul_of_pos_left h2 (by positivity)

/-- A kernel-checked narrow enclosure of the Euler--Mascheroni constant. -/
theorem gamma_bounds :
    (0.5772 : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < 0.5773 := by
  have hlo := corrected_harmonic_lower 100 (by norm_num)
  have hhi := corrected_harmonic_upper 100 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hlo hhi
  rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow] at hlo hhi
  norm_num [harmonic, Finset.sum_range_succ] at hlo hhi
  exact ⟨by linarith [log_ten_bounds.2], by linarith [log_ten_bounds.1]⟩

/-
A kernel-checked narrow enclosure of `log π`.
-/
theorem log_pi_bounds :
    (1.1447 : ℝ) < Real.log Real.pi ∧ Real.log Real.pi < 1.1448 := by
  constructor
  · rw [Real.lt_log_iff_exp_lt (by positivity)]
    rw [show (1.1447 : ℝ) = 1 + 0.1447 by norm_num, Real.exp_add]
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (0.1447 : ℝ) < 1.15572 := by
      have h := Real.exp_bound' (x := (0.1447 : ℝ)) (by norm_num) (by norm_num)
        (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
      linarith
    calc
      Real.exp 1 * Real.exp 0.1447 < (2.7182818286 : ℝ) * Real.exp 0.1447 :=
        mul_lt_mul_of_pos_right h1 (by positivity)
      _ < (2.7182818286 : ℝ) * 1.15572 := mul_lt_mul_of_pos_left h2 (by norm_num)
      _ < 3.141592 := by norm_num
      _ < Real.pi := Real.pi_gt_d6
  · rw [Real.log_lt_iff_lt_exp (by positivity)]
    rw [show (1.1448 : ℝ) = 1 + 0.1448 by norm_num, Real.exp_add]
    have h1 := Real.exp_one_gt_d9
    have h2 : (1.1558 : ℝ) < Real.exp (0.1448 : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      apply lt_of_lt_of_le
        (b := ∑ m ∈ Finset.range 8, (0.1448 : ℝ) ^ m / m.factorial)
      · norm_num [Finset.sum_range_succ, Nat.factorial]
      · exact Summable.sum_le_tsum _ (fun _ _ => by positivity)
          (Real.summable_pow_div_factorial _)
    calc
      Real.pi < 3.1416 := Real.pi_lt_d4
      _ < (2.7182818283 : ℝ) * 1.1558 := by norm_num
      _ < Real.exp 1 * 1.1558 := mul_lt_mul_of_pos_right h1 (by norm_num)
      _ < Real.exp 1 * Real.exp 0.1448 := mul_lt_mul_of_pos_left h2 (by positivity)

/-
Enclosure of Suzuki's constant `A = Γ'/Γ(1/4)`.
-/
theorem A_bounds : (-4.2276 : ℝ) < V5_1.A ∧ V5_1.A < -4.2273 := by
  constructor <;> norm_num [ V5_1.A ];
  · -- We'll use that π is approximately 3.14159.
    have h_pi : Real.pi < 3.1416 := Real.pi_lt_d4
    have := Real.log_two_lt_d9 ; norm_num at * ; linarith [ gamma_bounds ];
  · have := Real.log_two_gt_d9;
    have := Real.pi_gt_d4;
    have := V5_2.gamma_bounds;
    grind

/-
Enclosure of the linear coefficient in the archimedean screw term.
-/
theorem A_sub_log_pi_bounds :
    (-5.3724 : ℝ) < V5_1.A - Real.log Real.pi ∧
      V5_1.A - Real.log Real.pi < -5.3720 := by
  have := A_bounds; ( have := log_pi_bounds; ( norm_num1 at *; exact ⟨ by linarith, by linarith ⟩ ; ) )

end V5_2