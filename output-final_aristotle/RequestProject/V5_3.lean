import RequestProject.V5_1

open scoped BigOperators

namespace V5_3

/-
Certified enclosure of `ζ(2,1/4)` of width `0.0002`.
-/
theorem C_bounds :
    (17.1972 : ℝ) < V5_1.C ∧ V5_1.C < 17.1974 := by
  constructor;
  · -- Let's choose any $N$ and split the sum into the sum up to $N$ and the tail.
    set N := 100
    have h_split : V5_1.C = ∑ n ∈ Finset.range N, (1 / ((n + 1 / 4 : ℝ) ^ 2)) + ∑' n : ℕ, (1 / ((n + N + 1 / 4 : ℝ) ^ 2)) := by
      have h_split : V5_1.C = ∑' n : ℕ, (1 / ((n + 1 / 4 : ℝ) ^ 2)) := by
        rfl;
      rw [ h_split, ← Summable.sum_add_tsum_nat_add ];
      exacts [ by congr; ext; push_cast; ring, by simpa using V5_1.summable_C ];
    -- We'll use the fact that $\sum_{n=N}^{\infty} \frac{1}{(n + 1/4)^2}$ is bounded below by $\sum_{n=N}^{\infty} \frac{1}{(n + 1)(n)}$.
    have h_lower_bound : ∑' n : ℕ, (1 / ((n + N + 1 / 4 : ℝ) ^ 2)) ≥ ∑' n : ℕ, (1 / ((n + N + 1 : ℝ) * (n + N : ℝ))) := by
      refine' Summable.tsum_le_tsum _ _ _;
      · exact fun n => one_div_le_one_div_of_le ( by positivity ) ( by ring_nf; nlinarith );
      · exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by rw [ div_le_div_iff₀ ] <;> norm_num <;> ring <;> nlinarith ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
      · exact_mod_cast V5_1.summable_C.comp_injective ( add_left_injective N );
    -- We'll use the fact that $\sum_{n=N}^{\infty} \frac{1}{(n + 1)(n)}$ is a telescoping series.
    have h_telescoping : ∑' n : ℕ, (1 / ((n + N + 1 : ℝ) * (n + N : ℝ))) = 1 / (N : ℝ) := by
      have h_telescoping : ∀ M : ℕ, ∑ n ∈ Finset.range M, (1 / ((n + N + 1 : ℝ) * (n + N : ℝ))) = 1 / (N : ℝ) - 1 / (M + N : ℝ) := by
        intro M; induction M <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
        grind;
      -- Taking the limit of the partial sum as $M$ approaches infinity, we have:
      have h_limit : Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, (1 / ((n + N + 1 : ℝ) * (n + N : ℝ)))) Filter.atTop (nhds (1 / (N : ℝ))) := by
        simpa only [ h_telescoping ] using by simpa using tendsto_const_nhds.sub ( tendsto_inv_atTop_zero.comp ( show Filter.Tendsto ( fun M : ℕ => ( M : ℝ ) + N ) Filter.atTop ( Filter.atTop ) by exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ;
      exact tendsto_nhds_unique ( by exact ( Summable.hasSum <| by exact ( by by_contra h; exact not_tendsto_atTop_of_tendsto_nhds ( h_limit ) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 h ) ) |> HasSum.tendsto_sum_nat ) h_limit;
    norm_num at * ; linarith;
  · -- We'll use the fact that $\sum_{n=0}^{\infty} \frac{1}{(n+1/4)^2}$ is a convergent p-series with $p=2$.
    have h_pseries : ∑' n : ℕ, (1 / ((n : ℝ) + 1 / 4) ^ 2) = ∑ n ∈ Finset.range 100, (1 / ((n : ℝ) + 1 / 4) ^ 2) + ∑' n : ℕ, (1 / ((n + 100 : ℝ) + 1 / 4) ^ 2) := by
      rw [ ← Summable.sum_add_tsum_nat_add ];
      norm_cast;
      convert V5_1.summable_C using 1;
    -- We'll use the fact that $\sum_{n=100}^{\infty} \frac{1}{(n+1/4)^2}$ is bounded above by $\frac{1}{100-3/4}$.
    have h_bound : ∑' n : ℕ, (1 / ((n + 100 : ℝ) + 1 / 4) ^ 2) ≤ 1 / (100 - 3 / 4 : ℝ) := by
      have h_bound : ∀ n : ℕ, (1 / ((n + 100 : ℝ) + 1 / 4) ^ 2) ≤ (1 / ((n + 100 - 3 / 4 : ℝ) * (n + 100 + 1 / 4 : ℝ))) := by
        exact fun n => one_div_le_one_div_of_le ( by nlinarith only [ show ( n : ℝ ) ≥ 0 by positivity ] ) ( by nlinarith only [ show ( n : ℝ ) ≥ 0 by positivity ] );
      have h_telescope : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / ((n + 100 - 3 / 4 : ℝ) * (n + 100 + 1 / 4 : ℝ))) = 1 / (100 - 3 / 4 : ℝ) - 1 / (N + 100 - 3 / 4 : ℝ) := by
        intro N; induction N <;> norm_num [ Finset.sum_range_succ ] at *;
        grind;
      have h_telescope_limit : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / ((n + 100 - 3 / 4 : ℝ) * (n + 100 + 1 / 4 : ℝ)))) Filter.atTop (nhds (1 / (100 - 3 / 4 : ℝ))) := by
        rw [ Filter.tendsto_congr h_telescope ] ; exact le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) <| by norm_num;
      exact le_of_tendsto_of_tendsto' ( Summable.hasSum ( by exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => h_bound n ) <| by exact ( by exact ( by exact ( by exact ( by exact by { by_contra h; exact not_tendsto_atTop_of_tendsto_nhds ( h_telescope_limit ) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun n => by exact div_nonneg zero_le_one <| mul_nonneg ( by linarith ) <| by linarith ) |>.1 h } ) ) ) ) ) |> HasSum.tendsto_sum_nat ) h_telescope_limit fun N => Finset.sum_le_sum fun _ _ => h_bound _;
    norm_num [ V5_1.C ] at * ; linarith

end V5_3