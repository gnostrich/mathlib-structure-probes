import RequestProject.C3Base

open scoped BigOperators

namespace C3

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-
The zero-coordinate slope term blows up to `-∞`.
-/
lemma logTerm_atBot (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Filter.Tendsto (fun s : ℝ => a * Real.log (s * a / b))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
  refine' Filter.Tendsto.const_mul_atBot ha ( Real.tendsto_log_nhdsNE_zero.comp _ );
  refine' Filter.Tendsto.inf _ _ <;> norm_num [ ha.ne', hb.ne' ];
  · exact Continuous.tendsto' ( by continuity ) _ _ ( by norm_num );
  · aesop

/-
The positive-coordinate slope term converges to the directional derivative.
-/
lemma slope_pos_tendsto (rz ε πz qz : ℝ) (hrz : 0 < rz) (hπz : 0 < πz) :
    Filter.Tendsto
      (fun s : ℝ => (((1 - s) * πz + s * qz) * Real.log (((1 - s) * πz + s * qz) / rz)
          - πz * Real.log (πz / rz)) / s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((qz - πz) * (Real.log (πz / rz) + 1))) := by
  have h_deriv : HasDerivAt (fun s : ℝ => ((1 - s) * πz + s * qz) * Real.log (((1 - s) * πz + s * qz) / rz)) ((qz - πz) * (Real.log (πz / rz) + 1)) 0 := by
    convert HasDerivAt.mul ( HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.mul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ _ ) ) ) ( HasDerivAt.log ( HasDerivAt.div_const ( HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.mul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ _ ) ) ) _ ) _ ) using 1 <;> norm_num [ hrz.ne', hπz.ne' ];
    grind;
  simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero_right

variable (r c : X × Y → ℝ) (ε : ℝ) (μ : X → ℝ) (ν : Y → ℝ)

/-
Any minimizer is strictly positive.
-/
set_option maxHeartbeats 1600000 in
lemma C3_pos (hr : ∀ p, 0 < r p) (hε : 0 < ε) (hμ : ∀ x, 0 < μ x) (hν : ∀ y, 0 < ν y)
    (π : X × Y → ℝ) (hfeas : feasible μ ν π)
    (hmin : ∀ π', feasible μ ν π' → F r c ε π ≤ F r c ε π') :
    ∀ p, 0 < π p := by
  contrapose! hmin;
  -- Let's choose any $p$ such that $\pi(p) \leq 0$.
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : X × Y, π p₀ ≤ 0 := hmin;
  -- Define π_s := fun (s:ℝ) z => (1 - s) * π z + s * q z. For s ∈ Ioo 0 1: π_s s is feasible.
  obtain ⟨q, hq_pos, hq_feas⟩ : ∃ q : X × Y → ℝ, (∀ z, 0 < q z) ∧ (∀ x, ∑ y, q (x, y) = μ x) ∧ (∀ y, ∑ x, q (x, y) = ν y) := by
    refine' ⟨ fun p => μ p.1 * ν p.2 / ( ∑ x, μ x ), _, _, _ ⟩ <;> simp_all +decide [ ne_of_gt, Finset.sum_div _ _ _ ];
    · exact fun x y => Finset.sum_pos ( fun _ _ => hμ _ ) ⟨ x, Finset.mem_univ _ ⟩;
    · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_div, ne_of_gt ( Finset.sum_pos ( fun x _ => hμ x ) ⟨ p₀.1, Finset.mem_univ _ ⟩ ) ];
      intro x; rw [ div_eq_iff ( ne_of_gt ( Finset.sum_pos ( fun _ _ => hμ _ ) ⟨ x, Finset.mem_univ _ ⟩ ) ) ] ; ring;
      have := hfeas.2.1; have := hfeas.2.2; simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ;
      exact Or.inl ( by rw [ ← Finset.sum_congr rfl fun _ _ => this _, Finset.sum_comm, Finset.sum_congr rfl fun _ _ => ‹∀ x : X, ∑ y : Y, π ( x, y ) = μ x› _ ] );
    · simp +decide [ ← Finset.sum_div _ _ _, ← Finset.sum_mul, ne_of_gt ( Finset.sum_pos ( fun x _ => hμ x ) ( Finset.univ_nonempty_iff.mpr ⟨ p₀.1 ⟩ ) ) ];
  -- Show that the slope → atBot as s → 𝓝[>] 0.
  have h_slope_atBot : Filter.Tendsto (fun s : ℝ => ((F r c ε (fun z => (1 - s) * π z + s * q z)) - (F r c ε π)) / s) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
    have h_slope_atBot : Filter.Tendsto (fun s : ℝ => (∑ z, (q z - π z) * c z) + ε * (∑ z ∈ Finset.univ.filter (fun z => 0 < π z), (( (1 - s) * π z + s * q z ) * Real.log ( ( (1 - s) * π z + s * q z ) / r z ) - π z * Real.log (π z / r z)) / s) + ε * (∑ z ∈ Finset.univ.filter (fun z => ¬0 < π z), q z * Real.log (s * q z / r z))) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
      have h_slope_atBot : Filter.Tendsto (fun s : ℝ => (∑ z ∈ Finset.univ.filter (fun z => ¬0 < π z), q z * Real.log (s * q z / r z))) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
        have h_slope_atBot : ∀ z ∈ Finset.univ.filter (fun z => ¬0 < π z), Filter.Tendsto (fun s : ℝ => q z * Real.log (s * q z / r z)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
          intro z hz;
          have := logTerm_atBot ( q z ) ( r z ) ( hq_pos z ) ( hr z );
          exact this;
        have h_slope_atBot : Filter.Tendsto (fun s : ℝ => ∑ z ∈ Finset.univ.filter (fun z => ¬0 < π z), q z * Real.log (s * q z / r z)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
          have h_nonempty : Finset.Nonempty (Finset.univ.filter (fun z => ¬0 < π z)) := by
            exact ⟨ p₀, by simpa using hp₀ ⟩
          have h_slope_atBot : ∀ {S : Finset (X × Y)}, S.Nonempty → (∀ z ∈ S, Filter.Tendsto (fun s : ℝ => q z * Real.log (s * q z / r z)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot) → Filter.Tendsto (fun s : ℝ => ∑ z ∈ S, q z * Real.log (s * q z / r z)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
            intros S hS_nonempty hS_tendsto;
            induction' hS_nonempty using Finset.Nonempty.cons_induction with z hz ih;
            · simpa using hS_tendsto z ( Finset.mem_singleton_self z );
            · simp_all +decide [ Finset.sum_cons ];
              exact Filter.Tendsto.atBot_add_atBot hS_tendsto.1 ‹_›;
          exact h_slope_atBot h_nonempty ‹_›;
        convert h_slope_atBot using 1;
      have h_slope_atBot : Filter.Tendsto (fun s : ℝ => (∑ z ∈ Finset.univ.filter (fun z => 0 < π z), (( (1 - s) * π z + s * q z ) * Real.log ( ( (1 - s) * π z + s * q z ) / r z ) - π z * Real.log (π z / r z)) / s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑ z ∈ Finset.univ.filter (fun z => 0 < π z), (q z - π z) * (Real.log (π z / r z) + 1))) := by
        refine' tendsto_finset_sum _ fun z hz => _;
        convert slope_pos_tendsto ( r z ) ε ( π z ) ( q z ) ( hr z ) ( Finset.mem_filter.mp hz |>.2 ) using 1;
      exact Filter.Tendsto.add_atBot ( tendsto_const_nhds.add ( h_slope_atBot.const_mul ε ) ) ( Filter.Tendsto.const_mul_atBot hε ‹_› );
    refine' h_slope_atBot.congr' _;
    filter_upwards [ self_mem_nhdsWithin ] with s hs;
    simp +decide [ F, Finset.sum_div _ _ _, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm, hs.out.ne' ];
    simp +decide [ Finset.sum_filter, Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_add, add_mul, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, hs.out.ne' ];
    simp +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, hs.out.ne' ] ; ring;
    rw [ ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; split_ifs <;> ring ; linarith;
    · simp +decide [ show π x = 0 by linarith [ hfeas.1 x ] ];
    · grind;
  -- Extract witness: (slope → atBot).eventually (Filter.eventually_lt_atBot 0) gives eventually slope < 0; intersect with `Ioo_mem_nhdsGT_of_mem ⟨le_rfl, one_pos⟩` (a right-nbhd of 0 inside Ioo 0 1) and take `.exists` to get s ∈ Ioo 0 1 with (F(π_s s) - F π)/s < 0.
  obtain ⟨s, hs₀, hs₁⟩ : ∃ s ∈ Set.Ioo 0 1, ((F r c ε (fun z => (1 - s) * π z + s * q z)) - (F r c ε π)) / s < 0 := by
    have := h_slope_atBot.eventually ( Filter.eventually_lt_atBot 0 );
    rcases ( this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ) with h ; obtain ⟨ s, hs₁, hs₂ ⟩ := h.exists ; exact ⟨ s, hs₂, hs₁ ⟩;
  refine' ⟨ fun z => ( 1 - s ) * π z + s * q z, _, _ ⟩ <;> simp_all +decide [ div_lt_iff₀, feasible ];
  simp_all +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  exact ⟨ fun a b => add_nonneg ( mul_nonneg ( sub_nonneg.2 hs₀.2.le ) ( hfeas.1 a b ) ) ( mul_nonneg hs₀.1.le ( le_of_lt ( hq_pos a b ) ) ), fun x => by ring, fun y => by ring ⟩

end C3