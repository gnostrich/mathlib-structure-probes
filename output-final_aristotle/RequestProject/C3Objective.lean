import RequestProject.C3Base

open scoped BigOperators

namespace C3

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable (r c : X × Y → ℝ) (ε : ℝ)

/-
The objective is continuous.
-/
lemma F_continuous (hr : ∀ p, 0 < r p) : Continuous (F r c ε) := by
  -- We'll use the fact that $t \mapsto t \log(t / k)$ is continuous for $k > 0$.
  have h_cont : ∀ k > 0, Continuous (fun t : ℝ => t * Real.log (t / k)) := by
    intro k hk;
    have h_cont : Continuous (fun t : ℝ => k * ((t / k) * Real.log (t / k))) := by
      exact continuous_const.mul ( Real.continuous_mul_log.comp ( continuous_id.div_const k ) );
    simpa only [ mul_div_cancel₀ _ hk.ne' ] using h_cont.congr fun t => by rw [ ← mul_assoc, mul_div_cancel₀ _ hk.ne' ] ;
  exact Continuous.add ( continuous_finset_sum _ fun p _ => Continuous.mul ( continuous_apply p ) continuous_const ) ( continuous_const.mul ( continuous_finset_sum _ fun p _ => ( h_cont _ ( hr p ) ) |> Continuous.comp <| continuous_apply p ) )

/-
The objective is strictly convex on the nonnegative orthant.
-/
lemma F_strictConvexOn (hr : ∀ p, 0 < r p) (hε : 0 < ε) :
    StrictConvexOn ℝ {π : X × Y → ℝ | ∀ p, 0 ≤ π p} (F r c ε) := by
  refine' ⟨ convex_iff_forall_pos.mpr _, fun x hx y hy hxy a b ha hb hab => _ ⟩;
  · exact fun x hx y hy a b ha hb hab p => add_nonneg ( mul_nonneg ha.le ( hx p ) ) ( mul_nonneg hb.le ( hy p ) );
  · -- Apply the strict convexity of the entropy function to each term in the sum.
    have h_entropy : ∑ p, (a * x p + b * y p) * Real.log ((a * x p + b * y p) / r p) < a * ∑ p, x p * Real.log (x p / r p) + b * ∑ p, y p * Real.log (y p / r p) := by
      -- Apply the strict convexity of the function $g_p(s) = s \log(s / r_p)$ to each term in the sum.
      have h_strict_convex : ∀ p, (a * x p + b * y p) * Real.log ((a * x p + b * y p) / r p) < a * (x p * Real.log (x p / r p)) + b * (y p * Real.log (y p / r p)) ∨ x p = y p := by
        intro p
        by_cases h_eq : x p = y p
        · exact Or.inr h_eq
        · have h_strict_convex : StrictConvexOn ℝ (Set.Ici 0) (fun s => s * Real.log (s / r p)) := by
            have h_jensen : StrictConvexOn ℝ (Set.Ici 0) (fun s => s * Real.log s - s * Real.log (r p)) := by
              apply strictConvexOn_of_deriv2_pos ( convex_Ici 0 );
              · exact ContinuousOn.sub ( Real.continuous_mul_log.continuousOn ) ( continuousOn_id.mul continuousOn_const );
              · simp +zetaDelta at *;
                intro x hx; rw [ Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Ioi_mem_nhds hx ) fun u hu => by { exact HasDerivAt.deriv ( by simpa using HasDerivAt.sub ( Real.hasDerivAt_mul_log hu.out.ne' ) ( HasDerivAt.mul ( hasDerivAt_id u ) ( hasDerivAt_const _ _ ) ) ) } ) ] ; norm_num [ hx.ne' ] ; positivity;
            refine' h_jensen.congr fun s hs => _;
            by_cases hs' : s = 0 <;> simp +decide [ hs', Real.log_div, ne_of_gt ( hr p ) ] ; ring
          exact Or.inl ( h_strict_convex.2 ( hx p ) ( hy p ) h_eq ha hb hab );
      rw [ Finset.mul_sum _ _ _, Finset.mul_sum _ _ _, ← Finset.sum_add_distrib ];
      refine' Finset.sum_lt_sum _ _;
      · grind;
      · grind +revert;
    convert add_lt_add_left ( mul_lt_mul_of_pos_left h_entropy hε ) ( ∑ p, ( a * x p + b * y p ) * c p ) using 1 <;> simp +decide [ F, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_left_comm, mul_add, add_mul, hab ] ; ring;
    ring

end C3