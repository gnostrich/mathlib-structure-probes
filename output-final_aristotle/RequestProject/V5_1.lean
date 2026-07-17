import Mathlib

open scoped BigOperators
open ArithmeticFunction

namespace V5_1

/-- The Hurwitz value `ζ(2,1/4)` in the normalization used by Suzuki. -/
noncomputable def C : ℝ := ∑' n : ℕ, (1 / ((n : ℝ) + 1 / 4) ^ 2)

/-- The Hurwitz--Lerch series in the archimedean screw term. -/
noncomputable def L (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-2 * n * t) * (1 / ((n : ℝ) + 1 / 4) ^ 2)

/-- The constant `Γ'/Γ(1/4)`. -/
noncomputable def A : ℝ :=
  -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2

/-- Suzuki's archimedean screw component. -/
noncomputable def PsiArch (t : ℝ) : ℝ :=
  4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
    (t / 2) * (A - Real.log Real.pi) +
    (1 / 4) * (C - Real.exp (-t / 2) * L t)

/-- The finite prime-power contribution at nonnegative `t`. -/
noncomputable def primeSum (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
    (Λ n / Real.sqrt n) * (t - Real.log n)

/-- The nonnegative-half screw function. -/
noncomputable def PsiNonneg (t : ℝ) : ℝ := PsiArch t - primeSum t

/-- The full screw function, extended evenly. -/
noncomputable def Psi (t : ℝ) : ℝ := PsiNonneg |t|

/-- Krein's Gram kernel. -/
noncomputable def G (t u : ℝ) : ℝ := Psi t + Psi u - Psi (t - u)

theorem summable_C : Summable (fun n : ℕ => (1 / ((n : ℝ) + 1 / 4) ^ 2)) := by
  field_simp;
  exact Summable.mul_left _ <| Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by rw [ inv_le_comm₀ ] <;> norm_num <;> ring <;> nlinarith ) <| summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two

theorem summable_L (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun n : ℕ => Real.exp (-2 * n * t) * (1 / ((n : ℝ) + 1 / 4) ^ 2)) := by
  refine' Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => mul_le_of_le_one_left ( by positivity ) ( Real.exp_le_one_iff.mpr <| by nlinarith ) ) _;
  convert summable_C using 1

theorem L_zero : L 0 = C := by
  unfold L C; norm_num;

theorem PsiArch_zero : PsiArch 0 = 0 := by
  unfold PsiArch; norm_num;
  rw [ L_zero, sub_self ]

theorem Psi_zero : Psi 0 = 0 := by
  convert V5_1.PsiArch_zero using 1;
  unfold Psi PsiNonneg;
  unfold primeSum; norm_num;

/-
On the prime-free window the finite von Mangoldt sum is empty.
-/
theorem primeSum_eq_zero (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t < Real.log 2) :
    primeSum t = 0 := by
  -- Since $e^t < 2$, we have $\lfloor e^t \rfloor \leq 1$.
  have h_floor : ⌊Real.exp t⌋₊ ≤ 1 := by
    exact Nat.le_of_lt_succ <| by rw [ Nat.floor_lt' ] <;> norm_num ; rw [ Real.lt_log_iff_exp_lt ] at * <;> linarith;
  exact Finset.sum_eq_zero fun x hx => by linarith [ Finset.mem_Icc.mp hx ] ;

theorem Psi_eq_arch (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t < Real.log 2) :
    Psi t = PsiArch t := by
  -- Since t > 0, we have |t| = t.
  simp [V5_1.Psi, V5_1.PsiNonneg, ht0, ht2, V5_1.primeSum_eq_zero t ht0 ht2];
  rw [ abs_of_nonneg ht0, V5_1.primeSum_eq_zero t ht0 ht2, sub_zero ]

/-
Between `log 2` and `log 3`, precisely the `n=2` term contributes.
-/
theorem primeSum_first_window (t : ℝ) (ht2 : Real.log 2 ≤ t) (ht3 : t < Real.log 3) :
    primeSum t = (Real.log 2 / Real.sqrt 2) * (t - Real.log 2) := by
  -- By the monotonicity of exp and log and that floor(exp t)=2 satisfies the Icc bounds.
  have h_floor : ⌊Real.exp t⌋₊ = 2 := by
    rw [ Nat.floor_eq_iff ];
    · exact ⟨ by rw [ Real.log_le_iff_le_exp ] at ht2 <;> norm_num at * ; linarith, by rw [ Real.lt_log_iff_exp_lt ] at ht3 <;> norm_num at * ; linarith ⟩;
    · positivity
  simp [h_floor, primeSum];
  exact Or.inl <| ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two

theorem Psi_first_window (t : ℝ) (ht2 : Real.log 2 ≤ t) (ht3 : t < Real.log 3) :
    Psi t = PsiArch t - (Real.log 2 / Real.sqrt 2) * (t - Real.log 2) := by
  rw [ ← primeSum_first_window t ht2 ht3 ];
  unfold Psi PsiNonneg;
  rw [ abs_of_nonneg ( by linarith [ Real.log_nonneg one_le_two ] ) ]

theorem G_symm (t u : ℝ) : G t u = G u t := by
  grind +locals

theorem G_diag (t : ℝ) : G t t = 2 * Psi t := by
  unfold G; ring;
  rw [ V5_1.Psi_zero, sub_zero ]

end V5_1