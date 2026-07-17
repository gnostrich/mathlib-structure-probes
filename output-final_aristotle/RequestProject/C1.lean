import Mathlib

open scoped BigOperators Matrix

namespace C1

/-!
# C1. Kolmogorov's criterion (balance = zero holonomy)

For a positive stochastic matrix `P`, detailed balance (existence of a positive
reversible probability vector) is equivalent to the cycle condition: every cycle
has equal forward and backward weight products.
-/

variable {n : ℕ} [NeZero n] (P : Matrix (Fin n) (Fin n) ℝ)

theorem C1_kolmogorov
    (hpos : ∀ i j, 0 < P i j) (hrow : ∀ i, ∑ j, P i j = 1) :
    (∃ π : Fin n → ℝ, (∀ i, 0 < π i) ∧ (∑ i, π i = 1) ∧
        ∀ i j, π i * P i j = π j * P j i)
    ↔
    (∀ (m : ℕ) [NeZero m] (v : Fin m → Fin n),
        ∏ k : Fin m, P (v k) (v (k + 1)) = ∏ k : Fin m, P (v (k + 1)) (v k)) := by
  constructor;
  · rintro ⟨ π, hπ₁, hπ₂, hπ₃ ⟩ m _ v
    have h_prod : (∏ k, (P (v k) (v (k + 1)))) * (∏ k, (π (v k))) = (∏ k, (P (v (k + 1)) (v k))) * (∏ k, (π (v (k + 1)))) := by
      rw [ ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib ] ; exact Finset.prod_congr rfl fun _ _ => by linarith [ hπ₃ ( v ‹_› ) ( v ( ‹_› + 1 ) ) ] ;
    exact mul_right_cancel₀ ( Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt ( hπ₁ ( v i ) ) ) ( by rw [ show ∏ k : Fin m, π ( v ( k + 1 ) ) = ∏ k : Fin m, π ( v k ) from Equiv.prod_comp ( Equiv.addRight 1 ) fun k => π ( v k ) ] at *; linarith );
  · intro h;
    -- Define $c_i = \frac{P_{0i}}{P_{i0}}$ (positive), $s = \sum_i c_i$ (> 0 by Finset.sum_pos, nonempty since NeZero n), $\pi_i = \frac{c_i}{s}$.
    set c : Fin n → ℝ := fun i => P ⟨0, NeZero.pos n⟩ i / P i ⟨0, NeZero.pos n⟩
    set s := ∑ i, c i
    set π : Fin n → ℝ := fun i => c i / s;
    refine' ⟨ π, _, _, _ ⟩;
    · exact fun i => div_pos ( div_pos ( hpos _ _ ) ( hpos _ _ ) ) ( Finset.sum_pos ( fun _ _ => div_pos ( hpos _ _ ) ( hpos _ _ ) ) Finset.univ_nonempty );
    · rw [ ← Finset.sum_div, div_self <| ne_of_gt <| Finset.sum_pos ( fun _ _ => div_pos ( hpos _ _ ) ( hpos _ _ ) ) Finset.univ_nonempty ];
    · intro i j; specialize h 3 ( fun k => if k = 0 then ⟨ 0, NeZero.pos n ⟩ else if k = 1 then i else j ) ; simp_all +decide [ Fin.prod_univ_succ ] ;
      grind +locals

end C1