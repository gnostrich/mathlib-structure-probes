import Mathlib

open scoped BigOperators

namespace J2

/-!
# J2. Hermite–Biehler inequality (polynomial case, forward direction)

If `E(z) = ∏_{j} (z − w_j)` has all roots in the open lower half-plane (`Im w_j < 0`), then
`|E(conj z)| < |E z|` for every `z` with `Im z > 0`.  Per factor,
`|z − w|² − |conj z − w|² = −4·(Im z)·(Im w) > 0`.
-/

theorem J2_hermite_biehler (n : ℕ) (hn : 0 < n) (w : Fin n → ℂ)
    (hw : ∀ j, (w j).im < 0) (z : ℂ) (hz : 0 < z.im) :
    ‖∏ j, (starRingEnd ℂ z - w j)‖ < ‖∏ j, (z - w j)‖ := by
  induction hn <;> simp_all +decide [ Fin.prod_univ_succ ];
  · norm_num [ Complex.normSq, Complex.norm_def ];
    rw [ Real.sqrt_lt_sqrt_iff ] <;> nlinarith;
  · rename_i k hk ih;
    refine' mul_lt_mul' _ ( ih _ fun j => hw _ ) _ _;
    · norm_num [ Complex.normSq, Complex.norm_def ];
      exact Real.sqrt_le_sqrt ( by nlinarith [ hw 0 ] );
    · exact Finset.prod_nonneg fun _ _ => norm_nonneg _;
    · exact norm_pos_iff.mpr ( sub_ne_zero.mpr <| by rintro rfl; linarith [ hw 0 ] )

end J2