import RequestProject.C3Base

open scoped BigOperators Classical

namespace C3

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable (r c : X × Y → ℝ) (ε : ℝ) (μ : X → ℝ) (ν : Y → ℝ)

/-
Marginal-preserving perturbations of a strictly positive feasible point stay
feasible for small `t`.
-/
lemma perturb_feasible (π : X × Y → ℝ) (hpos : ∀ p, 0 < π p) (hfeas : feasible μ ν π)
    (d : X × Y → ℝ) (hd1 : ∀ x, ∑ y, d (x, y) = 0) (hd2 : ∀ y, ∑ x, d (x, y) = 0) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → feasible μ ν (fun p => π p + t * d p) := by
  by_cases h : Nonempty ( X × Y );
  · obtain ⟨δ, δpos, hδ⟩ : ∃ δ > 0, ∀ t : ℝ, abs t < δ → ∀ p, 0 ≤ π p + t * d p := by
      have hδ : ∃ δ > 0, ∀ p : X × Y, |d p| ≤ δ := by
        exact ⟨ ∑ p, |d p| + 1, add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => abs_nonneg _ ) zero_lt_one, fun p => le_add_of_le_of_nonneg ( Finset.single_le_sum ( fun p _ => abs_nonneg ( d p ) ) ( Finset.mem_univ p ) ) zero_le_one ⟩;
      obtain ⟨ δ, δpos, hδ ⟩ := hδ;
      exact ⟨ ( Finset.min' ( Finset.univ.image π ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ h.some ) ⟩ ) / δ, div_pos ( Finset.min'_mem ( Finset.univ.image π ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ h.some ) ⟩ |> fun x => by aesop ) δpos, fun t ht p => by nlinarith [ abs_lt.mp ht, abs_le.mp ( hδ p ), Finset.min'_le _ _ ( Finset.mem_image_of_mem π ( Finset.mem_univ p ) ), mul_div_cancel₀ ( Finset.min' ( Finset.univ.image π ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ h.some ) ⟩ ) δpos.ne' ] ⟩;
    refine' ⟨ δ, δpos, fun t ht => ⟨ fun p => hδ t ht p, fun x => _, fun y => _ ⟩ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
    · simp +decide [ ← Finset.mul_sum _ _ _, hd1, hfeas.2.1 ];
    · simp +decide [ ← Finset.mul_sum _ _ _, hd2, hfeas.2.2 ];
  · simp_all +decide [ feasible ];
    cases isEmpty_or_nonempty X <;> cases isEmpty_or_nonempty Y <;> simp_all +decide;
    · exact ⟨ 1, zero_lt_one ⟩;
    · exact ⟨ 1, zero_lt_one, fun t ht y => hfeas y ⟩;
    · exact ⟨ 1, zero_lt_one, fun t ht x => hfeas x ⟩

/-
First-order stationarity: the objective's directional derivative along any
marginal-preserving direction vanishes at a strictly positive minimizer.
-/
lemma first_order (hr : ∀ p, 0 < r p) (hε : 0 < ε)
    (π : X × Y → ℝ) (hpos : ∀ p, 0 < π p) (hfeas : feasible μ ν π)
    (hmin : ∀ π', feasible μ ν π' → F r c ε π ≤ F r c ε π')
    (d : X × Y → ℝ) (hd1 : ∀ x, ∑ y, d (x, y) = 0) (hd2 : ∀ y, ∑ x, d (x, y) = 0) :
    ∑ p, d p * (c p + ε * (Real.log (π p / r p) + 1)) = 0 := by
  obtain ⟨ δ, δpos, hδ ⟩ := perturb_feasible μ ν π hpos hfeas d hd1 hd2;
  -- By definition of $F$, we know that its derivative at $t = 0$ is given by the sum of the derivatives of its components.
  have h_deriv : HasDerivAt (fun t : ℝ => F r c ε (fun p => π p + t * d p)) (∑ p, d p * (c p + ε * (Real.log (π p / r p) + 1))) 0 := by
    have h_deriv : ∀ p, HasDerivAt (fun t : ℝ => (π p + t * d p) * c p + ε * (π p + t * d p) * Real.log ((π p + t * d p) / r p)) (d p * (c p + ε * (Real.log (π p / r p) + 1))) 0 := by
      intro p; convert HasDerivAt.add ( HasDerivAt.mul ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ _ ) ) ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ _ ) ) ) ) ( HasDerivAt.log ( HasDerivAt.div_const ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ _ ) ) ) _ ) _ ) ) using 1 <;> norm_num ; ring;
      · grind;
      · exact ⟨ ne_of_gt ( hpos p ), ne_of_gt ( hr p ) ⟩;
    convert HasDerivAt.sum fun p _ => h_deriv p using 1;
    ext t; simp +decide [ F, Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
  exact IsLocalMin.deriv_eq_zero ( Filter.eventually_of_mem ( Metric.ball_mem_nhds _ δpos ) fun t ht => by simpa using hmin _ ( hδ t <| by simpa using ht ) ) |> fun h => h_deriv.deriv.symm.trans h

/-- The elementary marginal-preserving 4-cycle direction. -/
noncomputable def cyc (x x' : X) (y y' : Y) : X × Y → ℝ :=
  fun q => (if q = (x, y) then (1 : ℝ) else 0) + (if q = (x', y') then 1 else 0)
         - (if q = (x, y') then 1 else 0) - (if q = (x', y) then 1 else 0)

lemma cyc_row (x x' : X) (y y' : Y) (a : X) : ∑ b, cyc x x' y y' (a, b) = 0 := by
  unfold cyc;
  by_cases ha : a = x <;> by_cases ha' : a = x' <;> simp +decide [ ha, ha', Prod.ext_iff ];
  · by_cases h : x = x' <;> simp_all +decide [ Finset.sum_add_distrib ];
    rw [ Finset.card_filter ] ; aesop;
  · by_cases h : x = x' <;> simp_all +decide [ Finset.sum_add_distrib ];
  · by_cases h : x' = x <;> simp_all +decide [ Finset.sum_add_distrib ]

lemma cyc_col (x x' : X) (y y' : Y) (b : Y) : ∑ a, cyc x x' y y' (a, b) = 0 := by
  unfold cyc;
  by_cases hy : b = y <;> by_cases hy' : b = y' <;> simp +decide [ hy, hy' ];
  · simp +decide [ Finset.sum_add_distrib, Finset.filter_eq', Finset.filter_and, hy.symm, hy'.symm ];
    simp +decide [ Finset.card_filter ];
  · by_cases hy'' : y = y' <;> simp_all +decide [ Finset.filter_eq', Finset.filter_and ];
  · rw [ Finset.card_filter ] ; aesop

lemma cyc_sum (g : X × Y → ℝ) (x x' : X) (y y' : Y) :
    ∑ q, cyc x x' y y' q * g q
      = g (x, y) + g (x', y') - g (x, y') - g (x', y) := by
  unfold cyc;
  simp +decide [ sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib ]

/-
The log-density plus rescaled cost is additively separable (the discrete
harmonic / cocycle condition coming from first-order stationarity).
-/
lemma xi_star (hr : ∀ p, 0 < r p) (hε : 0 < ε)
    (π : X × Y → ℝ) (hpos : ∀ p, 0 < π p) (hfeas : feasible μ ν π)
    (hmin : ∀ π', feasible μ ν π' → F r c ε π ≤ F r c ε π') :
    ∀ x x' y y',
      (c (x, y) / ε + Real.log (π (x, y) / r (x, y)))
        + (c (x', y') / ε + Real.log (π (x', y') / r (x', y')))
      = (c (x, y') / ε + Real.log (π (x, y') / r (x, y')))
        + (c (x', y) / ε + Real.log (π (x', y) / r (x', y))) := by
  intro x x' y y';
  have := first_order r c ε μ ν hr hε π hpos hfeas hmin ( fun q => cyc x x' y y' q ) ?_ ?_ <;> simp_all +decide [ cyc_row, cyc_col, cyc_sum ];
  grind

/-
Any strictly positive minimizer has Gibbs / h-transform form.
-/
lemma C3_gibbs (hr : ∀ p, 0 < r p) (hε : 0 < ε)
    (π : X × Y → ℝ) (hfeas : feasible μ ν π)
    (hmin : ∀ π', feasible μ ν π' → F r c ε π ≤ F r c ε π')
    (hpos : ∀ p, 0 < π p) :
    ∃ a : X → ℝ, ∃ b : Y → ℝ, (∀ x, 0 < a x) ∧ (∀ y, 0 < b y) ∧
      ∀ x y, π (x, y) = a x * (r (x, y) * Real.exp (- c (x, y) / ε)) * b y := by
  by_cases hX : Nonempty X <;> by_cases hY : Nonempty Y <;> simp_all +decide [ mul_assoc, mul_left_comm, mul_comm ];
  · -- Let's choose any $x_0 \in X$ and $y_0 \in Y$.
    obtain ⟨x0, hx0⟩ : ∃ x0 : X, True := by
      exact ⟨ hX.some, trivial ⟩
    obtain ⟨y0, hy0⟩ : ∃ y0 : Y, True := by
      exact ⟨ hY.some, trivial ⟩;
    -- Define ξ(x,y) = c(x,y)/ε + log(π(x,y)/r(x,y)).
    set ξ : X × Y → ℝ := fun p => c p / ε + Real.log (π p / r p);
    -- By definition of ξ, we have ξ(x,y) = α(x) + β(y) for some functions α and β.
    obtain ⟨α, β, hξ⟩ : ∃ α : X → ℝ, ∃ β : Y → ℝ, ∀ x y, ξ (x, y) = α x + β y := by
      have h_add : ∀ x x' y y', ξ (x, y) + ξ (x', y') = ξ (x, y') + ξ (x', y) := by
        apply_rules [ xi_star ];
        · exact fun p => hr p.1 p.2;
        · exact fun p => hpos p.1 p.2;
      exact ⟨ fun x => ξ ( x, y0 ), fun y => ξ ( x0, y ) - ξ ( x0, y0 ), fun x y => by linarith [ h_add x x0 y y0 ] ⟩;
    refine' ⟨ fun x => Real.exp ( α x ), fun x => Real.exp_pos _, fun y => Real.exp ( β y ), fun y => Real.exp_pos _, fun x y => _ ⟩;
    simp +zetaDelta at *;
    have := hξ x y; rw [ show α x = c ( x, y ) / ε + Real.log ( π ( x, y ) / r ( x, y ) ) - β y by linarith ] ; ring_nf; norm_num [ Real.exp_add, Real.exp_sub, Real.exp_neg, Real.exp_log, hpos, hr, hε.ne' ] ; ring;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( hr x y ), ne_of_gt ( Real.exp_pos _ ) ];
  · exact ⟨ fun _ => 1, fun _ => zero_lt_one ⟩;
  · exact ⟨ fun _ => 1, fun _ => zero_lt_one ⟩

end C3