import Mathlib

open scoped BigOperators
open MeasureTheory

namespace T3

/-!
# T3. Log-weighted tail bound

For every integer `N ≥ 2`, `∑_{n = N+1}^∞ (log n)·n^{-3/2} ≤ (2·log N + 4)/√N`.

Route: `g x = (log x)·x^{-3/2}` has derivative `x^{-5/2}·(1 − (3/2)·log x)`, which is negative
for `log x > 2/3`, i.e. for `x ≥ 2`; so `g` is antitone on `[N, ∞)` when `N ≥ 2`.  By the
sum–integral comparison every partial sum is bounded by `∫_N^∞ g = (2·log N + 4)/√N`
(integration by parts: `∫ (log x)·x^{-3/2} dx = -(2 log x + 4)·x^{-1/2}`), and
`Real.tsum_le_of_sum_range_le` upgrades this to the infinite sum since the terms are nonnegative.
-/

theorem T3_log_tail (N : ℕ) (hN : 2 ≤ N) :
    ∑' m : ℕ, Real.log ((m : ℝ) + N + 1) * ((m : ℝ) + N + 1) ^ (-(3 / 2) : ℝ)
      ≤ (2 * Real.log N + 4) / Real.sqrt N := by
  -- We'll use the fact that the sum of a decreasing function over an interval is less than the integral of the function over the same interval.
  have h_sum_le_integral : ∀ K : ℕ, (∑ i ∈ Finset.range K, (Real.log (i + N + 1)) * ((i + N + 1) : ℝ) ^ (-(3 / 2 : ℝ))) ≤ (∫ x in (N : ℝ)..((N + K) : ℝ), (Real.log x) * x ^ (-(3 / 2 : ℝ))) := by
    -- Apply the antitone property to each term in the sum.
    have h_antitone_sum : ∀ K : ℕ, (∑ i ∈ Finset.range K, (Real.log (i + N + 1)) * ((i + N + 1 : ℝ) ^ (-(3 / 2 : ℝ)))) ≤ (∑ i ∈ Finset.range K, ∫ x in (i + N : ℝ)..((i + N + 1) : ℝ), (Real.log x) * x ^ (-(3 / 2 : ℝ))) := by
      intro K
      apply Finset.sum_le_sum
      intro i _
      have h_antitone : ∀ x ∈ Set.Icc (i + N : ℝ) (i + N + 1), (Real.log (i + N + 1)) * ((i + N + 1 : ℝ) ^ (-(3 / 2 : ℝ))) ≤ (Real.log x) * x ^ (-(3 / 2 : ℝ)) := by
        have h_antitone : ∀ x ∈ Set.Icc (i + N : ℝ) (i + N + 1), deriv (fun x => Real.log x * x ^ (-(3 / 2 : ℝ))) x ≤ 0 := by
          intro x hx; norm_num [ show x ≠ 0 by linarith [ hx.1, show ( N : ℝ ) ≥ 2 by norm_cast ] ];
          rw [ show ( - ( 5 / 2 : ℝ ) ) = - ( 3 / 2 : ℝ ) - 1 by norm_num, Real.rpow_sub_one ( by linarith [ hx.1, show ( N : ℝ ) ≥ 2 by norm_cast ] ) ] ; ring_nf ; norm_num;
          rw [ mul_assoc ];
          exact le_mul_of_one_le_right ( mul_nonneg ( inv_nonneg.2 ( by linarith [ hx.1, show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( Real.rpow_nonneg ( by linarith [ hx.1, show ( N : ℝ ) ≥ 2 by norm_cast ] ) _ ) ) ( by nlinarith [ show ( N : ℝ ) ≥ 2 by norm_cast, hx.1, Real.log_two_gt_d9, Real.log_le_log ( by norm_num ) ( show ( x : ℝ ) ≥ 2 by linarith [ hx.1, show ( N : ℝ ) ≥ 2 by norm_cast ] ) ] );
        intro x hx; cases eq_or_lt_of_le hx.2 <;> simp_all +decide [ mul_comm ] ; (
        have := exists_deriv_eq_slope ( f := fun x => x ^ ( - ( 3 / 2 : ℝ ) ) * Real.log x ) ‹_›;
        contrapose! this;
        exact ⟨ continuousOn_of_forall_continuousAt fun y hy => by exact ContinuousAt.mul ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hy.1, show ( i :ℝ ) + N > 0 by positivity ] ) ( Real.continuousAt_log <| by linarith [ hy.1, show ( i :ℝ ) + N > 0 by positivity ] ), fun y hy => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.mul ( DifferentiableAt.rpow ( differentiableAt_id ) ( by norm_num ) <| by linarith [ hy.1, show ( i :ℝ ) + N > 0 by positivity ] ) ( Real.differentiableAt_log <| by linarith [ hy.1, show ( i :ℝ ) + N > 0 by positivity ] ), fun c hc => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_antitone c ( by linarith [ hc.1 ] ) ( by linarith [ hc.2 ] ) ] ⟩);
      refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_antitone ) <;> norm_num;
      apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] );
    convert h_antitone_sum using 2;
    induction ‹_› <;> simp_all +decide [ add_assoc, Finset.sum_range_succ ];
    rename_i k hk;
    rw [ ← hk, ← intervalIntegral.integral_add_adjacent_intervals ] <;> ring;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] );
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] );
  -- Evaluate the integral $\int_{N}^{N+K} \frac{\log x}{x^{3/2}} \, dx$.
  have h_integral_eval : ∀ K : ℕ, (∫ x in (N : ℝ)..((N + K) : ℝ), (Real.log x) * x ^ (-(3 / 2 : ℝ))) = (2 * Real.log N + 4) / Real.sqrt N - (2 * Real.log (N + K) + 4) / Real.sqrt (N + K) := by
    intros K; rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    rotate_right;
    use fun x => - ( 2 * Real.log x + 4 ) / Real.sqrt x;
    · grind +qlia;
    · intro x hx; convert HasDerivAt.div ( HasDerivAt.neg ( HasDerivAt.add ( HasDerivAt.const_mul 2 ( Real.hasDerivAt_log ( show x ≠ 0 from by cases Set.mem_uIcc.mp hx <;> linarith [ ( by norm_cast : ( 2 :ℝ ) ≤ N ) ] ) ) ) ( hasDerivAt_const _ _ ) ) ) ( Real.hasDerivAt_sqrt ( show x ≠ 0 from by cases Set.mem_uIcc.mp hx <;> linarith [ ( by norm_cast : ( 2 :ℝ ) ≤ N ) ] ) ) ( ne_of_gt <| Real.sqrt_pos.mpr <| show 0 < x from by cases Set.mem_uIcc.mp hx <;> linarith [ ( by norm_cast : ( 2 :ℝ ) ≤ N ) ] ) using 1 ; ring;
      by_cases h : Real.sqrt x = 0 <;> simp_all +decide [ sq, mul_assoc, pow_three ] ; ring;
      · exact absurd h <| ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ ( by norm_cast : ( 2 : ℝ ) ≤ N ) ] ;
      · rw [ show x ^ ( -3 / 2 : ℝ ) = x ^ ( -1 / 2 : ℝ ) * x ^ ( -1 : ℝ ) by rw [ ← Real.rpow_add ( by linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ] ; norm_num ] ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg ( by linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] : 0 ≤ x ), Real.rpow_neg_one ] ; ring;
        rw [ ← Real.sqrt_eq_rpow ] ; rw [ show ( Real.sqrt x ) ⁻¹ ^ 3 = ( Real.sqrt x ) ⁻¹ * ( Real.sqrt x ) ⁻¹ ^ 2 by ring, inv_pow, Real.sq_sqrt <| by linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ] ; ring;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.mul ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] ) ) ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by cases Set.mem_uIcc.mp hx <;> linarith [ show ( N : ℝ ) ≥ 2 by norm_cast ] );
  -- Apply the fact that the sum of a decreasing function over an interval is less than the integral of the function over the same interval.
  have h_sum_le_integral : ∀ K : ℕ, (∑ i ∈ Finset.range K, (Real.log (i + N + 1)) * ((i + N + 1) : ℝ) ^ (-(3 / 2 : ℝ))) ≤ (2 * Real.log N + 4) / Real.sqrt N := by
    exact fun K => le_trans ( h_sum_le_integral K ) ( h_integral_eval K ▸ sub_le_self _ ( div_nonneg ( by linarith [ Real.log_nonneg ( show ( N:ℝ ) + K ≥ 1 by norm_cast; linarith ) ] ) ( Real.sqrt_nonneg _ ) ) );
  refine' le_of_tendsto_of_tendsto' ( Summable.hasSum _ |> HasSum.tendsto_sum_nat ) tendsto_const_nhds h_sum_le_integral;
  exact ( summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun _ => mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.rpow_nonneg ( by linarith ) _ ) ) ) |>.2 fun h => absurd ( h.eventually ( Filter.eventually_gt_atTop ( ( 2 * Real.log N + 4 ) / Real.sqrt N ) ) ) fun hh => by obtain ⟨ K, hK ⟩ := hh.exists; linarith [ h_sum_le_integral K ] ;

end T3