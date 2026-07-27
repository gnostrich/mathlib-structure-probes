import Mathlib

open scoped BigOperators

namespace I1

/-!
# I1. Euler product = unentanglement (finite form)

Fix `k` distinct primes `p : Fin k → ℕ` and let `N a = ∏ i, (p i)^(a i)`.  A multiplicative
`g` (with `g 1 = 1` and `g (m·n) = g m · g n` for coprime `m, n`) tensor-factorizes:
`g (N a) = ∏ i, g ((p i)^(a i))`.  Conversely, a tensor-factorized array is multiplicative on
coprime products of the given shape.

(The exponent bound `E` of the informal statement is not needed and is omitted.)
-/

/-- `N a = ∏ i, (p i)^(a i)`. -/
def N (k : ℕ) (p : Fin k → ℕ) (a : Fin k → ℕ) : ℕ := ∏ i, (p i) ^ (a i)

/-
Forward: a multiplicative function is a product state over prime modes.
-/
theorem I1_forward (k : ℕ) (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime)
    (hpd : Function.Injective p) (g : ℕ → ℝ) (hg1 : g 1 = 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (a : Fin k → ℕ) :
    g (N k p a) = ∏ i, g ((p i) ^ (a i)) := by
  induction' k with k ih;
  · aesop;
  · unfold N at *; simp_all +decide [ Fin.prod_univ_succ ] ;
    rw [ hmul, ih _ ( fun i => hp _ ) ( hpd.comp ( Fin.succ_injective _ ) ) _ ];
    exact Nat.Coprime.prod_right fun i _ => Nat.Coprime.pow _ _ <| hp 0 |> Nat.Prime.coprime_iff_not_dvd |>.2 fun h => absurd ( hpd <| Nat.prime_dvd_prime_iff_eq ( hp 0 ) ( hp i.succ ) |>.1 h ) ( by simp +decide [ Fin.ext_iff ] )

/-
Converse: a tensor-factorized array is multiplicative on coprime products of prime powers.
-/
theorem I1_converse (k : ℕ) (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime)
    (hpd : Function.Injective p) (g : ℕ → ℝ) (f : Fin k → ℕ → ℝ) (hf0 : ∀ i, f i 0 = 1)
    (hG : ∀ a : Fin k → ℕ, g (N k p a) = ∏ i, f i (a i))
    (a b : Fin k → ℕ) (hcop : Nat.Coprime (N k p a) (N k p b)) :
    g (N k p a * N k p b) = g (N k p a) * g (N k p b) := by
  -- By definition of $N$, we know that $N k p (a + b) = N k p a * N k p b$.
  have hN : N k p (a + b) = N k p a * N k p b := by
    simp +decide [ N, Finset.prod_mul_distrib, pow_add ];
  -- Now for each `i`, `f i (a i + b i) = f i (a i) * f i (b i)`: if `b i = 0`, then `a i + b i = a i` and `f i (b i) = f i 0 = 1` (by `hf0`)); symmetric if `a i = 0`.
  have h_coprime : ∀ i, (a i = 0 ∨ b i = 0) := by
    intro i
    by_contra h_contra
    have h_div : p i ∣ N k p a ∧ p i ∣ N k p b := by
      exact ⟨ dvd_trans ( dvd_pow_self _ ( by tauto ) ) ( Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ) ), dvd_trans ( dvd_pow_self _ ( by tauto ) ) ( Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ) ) ⟩;
    exact Nat.Prime.not_dvd_one ( hp i ) ( hcop.gcd_eq_one ▸ Nat.dvd_gcd h_div.1 h_div.2 );
  simp_all +decide [ Finset.prod_mul_distrib ];
  rw [ ← hN, hG, ← Finset.prod_mul_distrib ] ; congr ; ext i ; cases h_coprime i <;> simp +decide [ * ] ;

end I1