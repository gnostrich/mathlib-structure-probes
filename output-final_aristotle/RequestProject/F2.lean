import Mathlib

open scoped BigOperators Matrix ComplexOrder
open Complex

namespace F2

/-!
# F2. Prony step, conditional

Suppose `c : ℤ → ℂ` with `c (−m) = conj (c m)` admits, on `|m| ≤ n`, an exponential
representation `c m = ∑ s, a s · exp(i·m·θ s)` with `r ≤ n` distinct unimodular nodes
`exp(i θ s)`.  Then:
* (a) the coefficients `a` are uniquely determined (Vandermonde injectivity);
* (b) `c (−m) = conj (c m)` forces every `a s` to be real;
* (c) if additionally the `r × r` Toeplitz section is PSD and the representation is minimal
  (`a s ≠ 0` for all `s`), then every `a s > 0`.
-/

variable {r n : ℕ}

/-- The `r × r` Toeplitz section `[c (j − k)]`. -/
def section' (c : ℤ → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun j k => c ((j : ℤ) - (k : ℤ))

/-
(a) Uniqueness of the coefficients (distinct nodes ⇒ Vandermonde injectivity).
-/
theorem F2_a (hrn : r ≤ n) (θ : Fin r → ℝ)
    (hθ : Function.Injective (fun s => Complex.exp ((θ s : ℂ) * Complex.I)))
    (c : ℤ → ℂ) (a a' : Fin r → ℂ)
    (hrep : ∀ m : ℤ, |m| ≤ (n : ℤ) → c m = ∑ s, a s * Complex.exp ((m : ℂ) * (θ s : ℂ) * Complex.I))
    (hrep' : ∀ m : ℤ, |m| ≤ (n : ℤ) →
      c m = ∑ s, a' s * Complex.exp ((m : ℂ) * (θ s : ℂ) * Complex.I)) :
    a = a' := by
  -- By the properties of the Vandermonde matrix and the distinctness of the nodes, the only solution to the system of equations is $b = 0$.
  have h_vandermonde : ∀ (b : Fin r → ℂ), (∀ m ∈ Finset.range r, ∑ s, b s * (Complex.exp ((θ s : ℂ) * Complex.I)) ^ m = 0) → b = 0 := by
    intros b hb
    have h_vandermonde : Matrix.det (Matrix.of (fun m s : Fin r => (Complex.exp ((θ s : ℂ) * Complex.I)) ^ (m : ℕ))) ≠ 0 := by
      erw [ Matrix.det_transpose, Matrix.det_vandermonde ];
      exact Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne <| hθ.ne <| by aesop;
    have h_vandermonde : Matrix.mulVec (Matrix.of (fun (m : Fin r) (s : Fin r) => (Complex.exp ((θ s : ℂ) * Complex.I)) ^ (m : ℕ))) b = 0 := by
      ext m; specialize hb m; simp_all +decide [ Matrix.mulVec, dotProduct, mul_comm ] ;
    exact Matrix.eq_zero_of_mulVec_eq_zero ‹_› h_vandermonde;
  specialize h_vandermonde ( a - a' ) ; simp_all +decide [ mul_assoc, ← Complex.exp_nat_mul ] ;
  exact sub_eq_zero.mp ( h_vandermonde fun m hm => by simpa [ sub_mul ] using sub_eq_zero.mpr ( hrep m ( by rw [ abs_of_nonneg ] <;> linarith ) |> Eq.symm ) )

/-
(b) Hermitian symmetry forces the coefficients to be real.
-/
theorem F2_b (hrn : r ≤ n) (θ : Fin r → ℝ)
    (hθ : Function.Injective (fun s => Complex.exp ((θ s : ℂ) * Complex.I)))
    (c : ℤ → ℂ) (a : Fin r → ℂ)
    (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hrep : ∀ m : ℤ, |m| ≤ (n : ℤ) →
      c m = ∑ s, a s * Complex.exp ((m : ℂ) * (θ s : ℂ) * Complex.I)) :
    ∀ s, (a s).im = 0 := by
  -- By F2_a, since a and (conj (a s)) both represent c on |m| ≤ n, we have a = (conj (a s)).
  have h_eq : a = fun s => starRingEnd ℂ (a s) := by
    apply F2_a hrn θ hθ c a (fun s => starRingEnd ℂ (a s)) hrep;
    intro m hm;
    have := hHerm m; specialize hrep ( -m ) ; simp_all +decide [ Complex.exp_neg, Complex.exp_ne_zero ] ;
    simpa [ Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.norm_exp ] using congr_arg Star.star hrep;
  intro s; replace h_eq := congr_fun h_eq s; norm_num [ Complex.ext_iff ] at h_eq; linarith;

/-
(c) PSD + minimality forces the coefficients to be strictly positive.
-/
theorem F2_c (hrn : r ≤ n) (θ : Fin r → ℝ)
    (hθ : Function.Injective (fun s => Complex.exp ((θ s : ℂ) * Complex.I)))
    (c : ℤ → ℂ) (a : Fin r → ℂ)
    (hHerm : ∀ m : ℤ, c (-m) = starRingEnd ℂ (c m))
    (hrep : ∀ m : ℤ, |m| ≤ (n : ℤ) →
      c m = ∑ s, a s * Complex.exp ((m : ℂ) * (θ s : ℂ) * Complex.I))
    (hPSD : (section' (r := r) c).PosSemidef) (hmin : ∀ s, a s ≠ 0) :
    ∀ s, 0 < (a s).re := by
  -- Let `z s := Complex.exp ((θ s : ℂ) * Complex.I)` (distinct nodes, `hθ`). Fix `t : Fin r`.
  let z := fun s : Fin r => Complex.exp ((θ s : ℂ) * Complex.I);
  -- By F2_b, every `a s` is real: `(a s).im = 0`, so `(a s : ℂ) = ((a s).re : ℂ)`.
  have ha_real : ∀ s, (a s).im = 0 := by
    apply F2_b hrn θ hθ c a hHerm hrep;
  -- The `r × r` matrix `W s k := Complex.exp ((-(k:ℂ)) * (θ s) * Complex.I) = (conj (z s))^(k:ℕ)` is a Vandermonde matrix in the distinct nodes `conj (z s)`, so `det W ≠ 0` and `W` is invertible.
  have hW_inv : ∀ t : Fin r, ∃ ξ : Fin r → ℂ, (∀ s : Fin r, ∑ k : Fin r, ξ k * (starRingEnd ℂ (z s)) ^ (k : ℕ) = if s = t then 1 else 0) := by
    intro t
    have hW_inv : Invertible (Matrix.of (fun s k : Fin r => (starRingEnd ℂ (z s)) ^ (k : ℕ))) := by
      convert Matrix.invertibleOfDetInvertible _;
      erw [ Matrix.det_vandermonde ];
      refine invertibleOfNonzero ?_;
      simp_all +decide [ Finset.prod_eq_zero_iff, sub_eq_zero ];
      exact fun s t hst => fun h => hst.ne <| hθ <| by simpa using congr_arg Star.star h.symm;
    obtain ⟨ξ, hξ⟩ : ∃ ξ : Fin r → ℂ, Matrix.mulVec (Matrix.of (fun s k : Fin r => (starRingEnd ℂ (z s)) ^ (k : ℕ))) ξ = fun s => if s = t then 1 else 0 := by
      exact ⟨ hW_inv.1.mulVec ( fun s => if s = t then 1 else 0 ), by simp +decide ⟩;
    exact ⟨ ξ, fun s => by simpa [ Matrix.mulVec, dotProduct, mul_comm ] using congr_fun hξ s ⟩;
  -- Compute the PSD quadratic form on `ξ`: `hPSD.2 ξ` gives `0 ≤ star ξ ⬝ᵥ (section' c).mulVec ξ = ∑ j, ∑ k, conj (ξ j) * c (j - k) * ξ k`.
  have h_quad_form : ∀ t : Fin r, ∀ ξ : Fin r → ℂ, (∀ s : Fin r, ∑ k : Fin r, ξ k * (starRingEnd ℂ (z s)) ^ (k : ℕ) = if s = t then 1 else 0) → 0 ≤ ∑ s : Fin r, (a s).re * (∑ k : Fin r, ξ k * (starRingEnd ℂ (z s)) ^ (k : ℕ)) * (∑ j : Fin r, (starRingEnd ℂ (ξ j)) * (z s) ^ (j : ℕ)) := by
    intros t ξ hξ
    have h_quad_form : 0 ≤ ∑ j : Fin r, ∑ k : Fin r, (starRingEnd ℂ (ξ j)) * (section' c) j k * (ξ k) := by
      have := hPSD.2;
      convert this ( Finsupp.equivFunOnFinite.symm ξ ) using 1 ; simp +decide [ Finsupp.sum_fintype ];
    -- Substitute `c (j-k) = ∑ s, a s * exp((j-k)*(θ s)*I)` (from `hrep`, valid since `|j-k| ≤ r-1 ≤ n`), and factor `exp((j-k)*(θ s)*I) = exp(j*(θ s)*I) * exp((-k)*(θ s)*I)`.
    have h_subst : ∀ j k : Fin r, (section' c) j k = ∑ s : Fin r, (a s).re * (z s) ^ (j : ℕ) * (starRingEnd ℂ (z s)) ^ (k : ℕ) := by
      intros j k
      have h_subst : (section' c) j k = ∑ s : Fin r, (a s) * (z s) ^ (j : ℕ) * (starRingEnd ℂ (z s)) ^ (k : ℕ) := by
        convert hrep ( j - k ) _ using 1;
        · simp +zetaDelta at *;
          norm_num [ sub_mul, mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_conj ];
          exact Finset.sum_congr rfl fun _ _ => by rw [ ← Complex.exp_add ] ; ring;
        · exact abs_le.mpr ⟨ by linarith [ Fin.is_lt j, Fin.is_lt k ], by linarith [ Fin.is_lt j, Fin.is_lt k ] ⟩;
      convert h_subst using 2 ; simp +decide [ Complex.ext_iff, ha_real ];
    convert h_quad_form using 1;
    simp +decide only [Finset.mul_sum _ _ _, mul_comm, mul_assoc, h_subst];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  intro t; specialize hW_inv t; obtain ⟨ ξ, hξ ⟩ := hW_inv; specialize h_quad_form t ξ hξ; simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] ;
  -- By the choice of `ξ`, the inner sum is `1` when `s = t` and `0` otherwise, so the whole form equals `a t`.
  have h_inner_sum : ∑ x : Fin r, (starRingEnd ℂ (ξ x)) * (z t) ^ (x : ℕ) = 1 := by
    convert congr_arg Star.star ( hξ t ) using 1 <;> simp +decide [ mul_comm ];
  simp_all +decide [ Complex.ext_iff ];
  exact lt_of_le_of_ne h_quad_form ( Ne.symm ( hmin t ) )

end F2