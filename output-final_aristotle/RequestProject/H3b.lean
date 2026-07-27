import Mathlib

open scoped BigOperators

namespace H3b

/-!
# H3b. Asano contraction step

If `P(z₁,z₂) = A + B·z₁ + C·z₂ + D·z₁·z₂` (with `D ≠ 0`) is nonzero on the open bidisc, then
`A + D·z` is nonzero on the open disc.
-/

theorem H3b_asano (A B C D : ℂ) (hD : D ≠ 0)
    (hP : ∀ z₁ z₂ : ℂ, ‖z₁‖ < 1 → ‖z₂‖ < 1 → A + B * z₁ + C * z₂ + D * z₁ * z₂ ≠ 0)
    (z : ℂ) (hz : ‖z‖ < 1) : A + D * z ≠ 0 := by
  -- By contradiction, assume $A + D·z = 0$ with $‖z‖ < 1$.
  by_contra h_contra
  have hAD : A / D = -z := by
    grind
  have hAD_norm : ‖A / D‖ < 1 := by
    aesop
  have h_quad : ∀ w : ℂ, ‖w‖ < 1 → A + (B + C) * w + D * w ^ 2 ≠ 0 := by
    exact fun w hw => by convert hP w w hw hw using 1; ring;
  have h_quad_roots : ∃ r₁ r₂ : ℂ, r₁ * r₂ = A / D ∧ ∀ w : ℂ, A + (B + C) * w + D * w ^ 2 = 0 ↔ w = r₁ ∨ w = r₂ := by
    obtain ⟨r₁, r₂, hr⟩ : ∃ r₁ r₂ : ℂ, r₁ + r₂ = -(B + C) / D ∧ r₁ * r₂ = A / D := by
      exact ⟨ ( - ( B + C ) / D ) / 2 - ( ( - ( B + C ) / D ) ^ 2 / 4 - A / D ) ^ ( 1/2 : ℂ ), ( - ( B + C ) / D ) / 2 + ( ( - ( B + C ) / D ) ^ 2 / 4 - A / D ) ^ ( 1/2 : ℂ ), by ring, by ring; rw [ ← Complex.cpow_nat_mul ] ; norm_num; ring ⟩;
    refine' ⟨ r₁, r₂, hr.2, fun w => ⟨ fun hw => _, fun hw => _ ⟩ ⟩ <;> simp_all +decide [ mul_comm, mul_assoc, mul_left_comm, div_eq_mul_inv ]; all_goals grind
  obtain ⟨r₁, r₂, hr⟩ := h_quad_roots
  have h_abs : ‖r₁‖ ≥ 1 ∧ ‖r₂‖ ≥ 1 := by
    exact ⟨ not_lt.mp fun contra => h_quad r₁ contra <| hr.2 r₁ |>.2 <| Or.inl rfl, not_lt.mp fun contra => h_quad r₂ contra <| hr.2 r₂ |>.2 <| Or.inr rfl ⟩
  have h_abs_prod : ‖A / D‖ ≥ 1 := by
    rw [ ← hr.1, norm_mul ] ; nlinarith [ norm_nonneg r₁, norm_nonneg r₂ ] ;
  linarith [hAD_norm, h_abs_prod]

end H3b