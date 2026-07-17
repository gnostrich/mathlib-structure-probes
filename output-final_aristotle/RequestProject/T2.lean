import Mathlib

open scoped BigOperators
open MeasureTheory

namespace T2

/-!
# T2. Power-tail bound

For every integer `N ≥ 1`, `∑_{n = N+1}^∞ n^{-3/2} ≤ 2/√N`.

The tail is indexed by `m ↦ n = m + N + 1` (so `m` ranges over `ℕ`).  Route: `x ↦ x^{-3/2}` is
antitone on `[N, ∞)`; by the sum–integral comparison, every partial sum
`∑_{n=N+1}^{K} n^{-3/2} ≤ ∫_N^K x^{-3/2} dx ≤ ∫_N^∞ x^{-3/2} dx = 2/√N`.  Since the terms are
nonnegative, `Real.tsum_le_of_sum_range_le` upgrades this to the infinite sum.
-/

theorem T2_power_tail (N : ℕ) (hN : 1 ≤ N) :
    ∑' m : ℕ, ((m : ℝ) + N + 1) ^ (-(3 / 2) : ℝ) ≤ 2 / Real.sqrt N := by
  have h_bound : ∀ K : ℕ, (∑ m ∈ Finset.range K, ((m : ℝ) + N + 1) ^ (-(3 / 2 : ℝ))) ≤ 2 / Real.sqrt N := by
    -- We'll use the fact that the sum of a series can be bounded by the integral of the function.
    have h_integral_bound : ∀ K : ℕ, (∑ m ∈ Finset.range K, ((m : ℝ) + N + 1) ^ (-(3 / 2 : ℝ))) ≤ ∫ x in (N : ℝ)..(N + K), x ^ (-(3 / 2 : ℝ)) := by
      -- By the properties of the integral, we can bound each term in the sum.
      have h_integral_bound : ∀ m : ℕ, ∫ x in (m + N : ℝ)..((m + 1) + N : ℝ), x ^ (-(3 / 2 : ℝ)) ≥ ((m + N + 1 : ℝ) ^ (-(3 / 2 : ℝ))) := by
        intro m
        have h_integral_bound : ∀ x ∈ Set.Icc (m + N : ℝ) ((m + 1) + N : ℝ), x ^ (-(3 / 2 : ℝ)) ≥ ((m + N + 1 : ℝ) ^ (-(3 / 2 : ℝ))) := by
          intro x hx; rw [ ge_iff_le ] ; rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith [ hx.1, hx.2, show ( N : ℝ ) ≥ 1 by norm_cast ] ;
        refine' le_trans _ ( intervalIntegral.integral_mono_on _ _ _ h_integral_bound ) <;> norm_num;
        apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
        exact fun h => by linarith [ ( by norm_cast : ( 1 : ℝ ) ≤ N ) ] ;
      intro K; convert Finset.sum_le_sum fun i hi => h_integral_bound i using 1; induction K <;> simp_all +decide [ add_assoc, Finset.sum_range_succ ] ; ring;
      rename_i k hk; rw [ ← intervalIntegral.integral_add_adjacent_intervals ] ; ring;
      · norm_num [ add_comm, add_left_comm, add_assoc ] at * ; linarith;
      · apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
        aesop;
      · apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
        exact fun h => by linarith [ ( by norm_cast : ( 1 : ℝ ) ≤ N ) ] ;
    intro K; convert le_trans ( h_integral_bound K ) _ using 1; rw [ integral_rpow ] <;> norm_num;
    · rw [ Real.sqrt_eq_rpow, Real.rpow_neg ( by positivity ), Real.rpow_neg ( by positivity ) ] ; ring_nf ; norm_num;
      positivity;
    · aesop;
  exact le_of_tendsto_of_tendsto' ( Summable.hasSum ( by exact ( by { exact_mod_cast Summable.comp_injective ( Real.summable_nat_rpow.2 <| by norm_num ) ( by intros a b; aesop ) } ) ) |> HasSum.tendsto_sum_nat ) tendsto_const_nhds h_bound

end T2