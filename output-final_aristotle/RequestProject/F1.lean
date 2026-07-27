import Mathlib

open scoped BigOperators Matrix ComplexOrder
open Complex

namespace F1

/-!
# F1. Rank-one Carathéodory case, complete

Let `T` be an `(n+1) × (n+1)` Hermitian Toeplitz matrix `T j k = c (j−k)` with
`c (−m) = conj (c m)`, positive semidefinite and of rank exactly `1`.  Then there are `θ : ℝ`
and `ρ : ℝ`, `ρ > 0`, with `c m = ρ·exp(i·m·θ)` for all `|m| ≤ n`.

Route (elementary, via vanishing `2 × 2` minors of a rank-`1` matrix):
`c 0 > 0`; every `2 × 2` minor vanishes so `|c m| = c 0` and `c m ^ 2 = c (m−1)·c (m+1)`; hence the
arguments are in arithmetic progression, giving `c m = c 0 · exp(i m θ)` with `θ = arg (c 1)`
(negative `m` follows from Hermitian symmetry).
-/

variable {n : ℕ}

/-- The Hermitian Toeplitz matrix `T j k = c (j − k)`. -/
def toeplitz (c : ℤ → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun j k => c ((j : ℤ) - (k : ℤ))

/-
A rank-`≤ 1` square complex matrix is an outer product `M i j = u i * w j`.
-/
lemma exists_outer {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (h : M.rank ≤ 1) :
    ∃ u w : Fin N → ℂ, ∀ i j, M i j = u i * w j := by
  interval_cases _ : Matrix.rank M <;> simp_all +decide [ Matrix.rank, Submodule.eq_bot_iff ];
  · exact ⟨ 0, 0, fun i j => by simpa using congr_fun ( ‹∀ a : Fin N → ℂ, M *ᵥ a = 0› ( Pi.single j 1 ) ) i ⟩;
  · -- Since the range of $M.mulVecLin$ is one-dimensional, there exists a vector $u$ such that every element of the range is a scalar multiple of $u$.
    obtain ⟨u, hu⟩ : ∃ u : Fin N → ℂ, ∀ v ∈ LinearMap.range M.mulVecLin, ∃ c : ℂ, v = c • u := by
      obtain ⟨ u, hu ⟩ := finrank_eq_one_iff'.mp ‹_›;
      exact ⟨ u, fun v hv => by obtain ⟨ c, hc ⟩ := hu.2 ⟨ v, hv ⟩ ; exact ⟨ c, by simpa [ Subtype.ext_iff ] using hc.symm ⟩ ⟩;
    choose! c hc using hu;
    exact ⟨ u, fun j => c ( M.mulVec ( Pi.single j 1 ) ), fun i j => by simpa [ mul_comm ] using congr_fun ( hc ( M.mulVec ( Pi.single j 1 ) ) ( LinearMap.mem_range_self _ _ ) ) i ⟩

/-
Rank-one Carathéodory representation.
-/
theorem F1_rankone (c : ℤ → ℂ)
    (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hPSD : (toeplitz (n := n) c).PosSemidef)
    (hrank : (toeplitz (n := n) c).rank = 1) :
    ∃ (θ ρ : ℝ), 0 < ρ ∧
      ∀ m : ℤ, |m| ≤ (n : ℤ) → c m = (ρ : ℂ) * Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) := by
  by_cases hn : n = 0;
  · -- Since $c 0$ is real and positive, we can set $\rho = c 0$.
    have h_pos : 0 < (c 0).re := by
      have h_c0_pos : 0 < c 0 := by
        have h_c0_nonneg : 0 ≤ c 0 := by
          have := hPSD.2;
          convert this ( Finsupp.single 0 1 ) using 1 ; simp +decide [ toeplitz ]
        have h_c0_ne_zero : c 0 ≠ 0 := by
          intro h; simp_all +decide [ Matrix.rank, Submodule.eq_bot_iff ] ;
          -- If $c 0 = 0$, then the entire first row and column of $T$ would be zero, contradicting the assumption that $T$ has rank 1.
          have h_contra : ∀ i j : Fin (n + 1), (toeplitz c) i j = 0 := by
            simp_all +decide [ Fin.eq_zero, toeplitz ];
            subst hn; simp_all +decide [ Fin.eq_zero ] ;
          rw [ show ( toeplitz c : Matrix ( Fin ( n + 1 ) ) ( Fin ( n + 1 ) ) ℂ ) = 0 from Matrix.ext h_contra ] at hrank;
          erw [ LinearMap.range_eq_bot.mpr ] at hrank <;> aesop_cat
        exact?;
      convert h_c0_pos using 1;
      norm_num [ Complex.lt_def ];
      exact fun _ => by have := hHerm 0; norm_num [ Complex.ext_iff ] at this; linarith;
    use 0, (c 0).re
    simp [h_pos];
    intro m hm; rw [ show m = 0 by linarith [ abs_le.mp hm ] ] ; simp +decide [ Complex.ext_iff, h_pos.ne' ] ;
    specialize hHerm 0 ; norm_num [ Complex.ext_iff ] at hHerm ; linarith;
  · -- Let $c0 := c 0$.
    set c0 := c 0
    have hc0_real : c0.im = 0 := by
      have := hHerm 0; norm_num [ Complex.ext_iff ] at *; linarith;
    have hc0_pos : 0 < c0.re := by
      by_cases hc0_zero : c0 = 0;
      · -- If $c0 = 0$, then the first row of $T$ would be zero, contradicting the rank being 1.
        have h_row_zero : ∀ k : Fin (n + 1), (toeplitz c) 0 k = 0 := by
          intro k
          have h_row_zero : ∀ x : Fin (n + 1), (toeplitz c) 0 x * starRingEnd ℂ ((toeplitz c) 0 x) = 0 := by
            intro x
            have h_row_zero : (toeplitz c) 0 x * starRingEnd ℂ ((toeplitz c) 0 x) = (toeplitz c) x 0 * (toeplitz c) 0 x := by
              simp +decide [ toeplitz, hHerm ];
              ring;
            obtain ⟨ u, w, h ⟩ := exists_outer ( toeplitz c ) ( by linarith ) ; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
            have := h 0 0; simp_all +decide [ toeplitz ] ;
            grind;
          simp_all +decide [ Complex.ext_iff ];
        have h_contra : ∀ k : Fin (n + 1), c k = 0 := by
          intro k; specialize h_row_zero k; specialize hHerm k; simp_all +decide [ toeplitz ] ;
        have h_contra : ∀ m : ℤ, |m| ≤ n → c m = 0 := by
          intro m hm; cases' abs_cases m with hm₁ hm₁ <;> simp_all +decide [ abs_le ] ;
          · convert h_contra ⟨ m.toNat, by linarith [ Int.toNat_of_nonneg hm₁ ] ⟩ ; aesop;
          · specialize h_contra ⟨ Int.natAbs m, by omega ⟩ ; simp_all +decide [ abs_of_nonpos hm₁.1 ] ;
        have h_contra : ∀ m : Fin (n + 1), ∀ k : Fin (n + 1), (toeplitz c) m k = 0 := by
          exact fun m k => h_contra _ <| abs_le.mpr ⟨ by linarith [ Fin.is_lt m, Fin.is_lt k ], by linarith [ Fin.is_lt m, Fin.is_lt k ] ⟩;
        rw [ show toeplitz c = 0 from Matrix.ext h_contra ] at hrank ; aesop;
      · simp_all +decide [ Complex.ext_iff ];
        have := hPSD.2;
        specialize this ( Finsupp.single 0 1 ) ; simp_all +decide [ Fin.sum_univ_succ, toeplitz ];
        exact lt_of_le_of_ne ( Complex.le_def.mp this |>.1 ) ( Ne.symm hc0_zero )
    have hc0_ne_zero : c0 ≠ 0 := by
      aesop;
    -- Set `q := c 1 / c 0`.
    set q := c 1 / c0
    have hq_norm : ‖q‖ = 1 := by
      -- From `c 1 * c (-1) = (u 1 * w 0)*(u 0 * w 1) = (u 1 * w 1)*(u 0 * w 0) = T 1 1 * T 0 0 = c0^2 = ρ^2`.
      have hc1_c_neg1 : c 1 * c (-1) = c0 ^ 2 := by
        obtain ⟨ u, w, h ⟩ := exists_outer ( toeplitz c ) ( by linarith );
        convert congr_arg₂ ( · * · ) ( h ⟨ 1, Nat.succ_lt_succ ( Nat.pos_of_ne_zero hn ) ⟩ ⟨ 0, Nat.zero_lt_succ _ ⟩ ) ( h ⟨ 0, Nat.zero_lt_succ _ ⟩ ⟨ 1, Nat.succ_lt_succ ( Nat.pos_of_ne_zero hn ) ⟩ ) using 1 ; ring!;
        convert congr_arg₂ ( · * · ) ( h ⟨ 1, Nat.succ_lt_succ ( Nat.pos_of_ne_zero hn ) ⟩ ⟨ 1, Nat.succ_lt_succ ( Nat.pos_of_ne_zero hn ) ⟩ ) ( h ⟨ 0, Nat.zero_lt_succ _ ⟩ ⟨ 0, Nat.zero_lt_succ _ ⟩ ) using 1 ; ring!;
        ring;
      simp_all +decide [ Complex.ext_iff, sq ];
      simp +zetaDelta at *;
      norm_num [ Complex.normSq, Complex.norm_def, hc0_real, hc0_pos.le, hc1_c_neg1 ];
      positivity
    have hq_arg : ∀ m : ℕ, m ≤ n → c m = c0 * q ^ m := by
      obtain ⟨u, w, h_outer⟩ : ∃ u w : Fin (n + 1) → ℂ, ∀ i j, toeplitz c i j = u i * w j := by
        convert exists_outer ( toeplitz c ) ( by linarith ) using 1;
      -- For every `k : Fin n` (so `k` and `k+1` are valid rows/cols), `c 1 = T ⟨k+1⟩ ⟨k⟩ = u (k+1) * w k` and `c 0 = T ⟨k⟩ ⟨k⟩ = u k * w k`. Since `c0 ≠ 0`, `w k ≠ 0` and `u k ≠ 0`, so `u (k+1) = q * u k`.
      have h_u_rec : ∀ k : Fin n, u (⟨k.val + 1, by linarith [Fin.is_lt k]⟩) = q * u (⟨k.val, by linarith [Fin.is_lt k]⟩) := by
        intro k
        have h_u_rec_step : c 1 = u (⟨k.val + 1, by linarith [Fin.is_lt k]⟩) * w (⟨k.val, by linarith [Fin.is_lt k]⟩) ∧ c 0 = u (⟨k.val, by linarith [Fin.is_lt k]⟩) * w (⟨k.val, by linarith [Fin.is_lt k]⟩) := by
          simp_all +decide [ toeplitz ];
          exact ⟨ by simpa using h_outer ⟨ k + 1, by linarith [ Fin.is_lt k ] ⟩ ⟨ k, by linarith [ Fin.is_lt k ] ⟩, by simpa using h_outer ⟨ k, by linarith [ Fin.is_lt k ] ⟩ ⟨ k, by linarith [ Fin.is_lt k ] ⟩ ⟩;
        grind;
      -- By induction, `u m = u 0 * q ^ m`.
      have h_u_ind : ∀ m : Fin (n + 1), u m = u 0 * q ^ (m : ℕ) := by
        intro m; induction m using Fin.inductionOn <;> simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm ] ;
        exact h_u_rec _ ▸ by aesop;
      -- For `m : ℕ` with `m ≤ n`, `c m = T ⟨m⟩ ⟨0⟩ = u m * w 0 = (u 0 * w 0) * q ^ m = c0 * q ^ m` (using `c0 = u 0 * w 0 = T 0 0`).
      intros m hm
      have h_c_m : c m = u (⟨m, by linarith⟩) * w 0 := by
        convert h_outer ⟨ m, by linarith ⟩ 0 using 1;
      rw [ h_c_m, h_u_ind ⟨ m, by linarith ⟩ ];
      convert congr_arg ( · * q ^ m ) ( h_outer 0 0 |> Eq.symm ) using 1 ; ring!;
    -- Let `θ := Complex.arg q`.
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, q = Complex.exp (θ * Complex.I) := by
      rw [ Complex.norm_eq_one_iff ] at hq_norm ; tauto;
    refine' ⟨ θ, c0.re, hc0_pos, fun m hm => _ ⟩ ; rcases Int.eq_nat_or_neg m with ⟨ m, rfl | rfl ⟩ <;> simp_all +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]; all_goals norm_num [ ← Complex.exp_nat_mul, Complex.exp_re, Complex.exp_im ]

end F1