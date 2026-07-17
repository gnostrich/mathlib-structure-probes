import Mathlib

open scoped BigOperators Matrix

namespace D3

/-!
# D3. Gibbs states satisfy KMS (finite dimensions)

For a Hermitian `H`, `β : ℝ`, the Gibbs state `ω(x) = Tr(e^{-βH} x) / Tr(e^{-βH})` and the
imaginary-time twist `σ(b) = e^{-βH} b e^{βH}` satisfy the KMS identity
`ω(a · σ(b)) = ω(b · a)`.  (Hermiticity of `H` is stated in the original problem but is not
needed for the identity, which rests only on `e^{βH} · e^{-βH} = 1` and cyclicity of the trace;
it is kept as a hypothesis as requested.)
-/

variable {n : ℕ}

/-- `e^{-βH}`, the (unnormalized) Gibbs weight. -/
noncomputable def gibbs (H : Matrix (Fin n) (Fin n) ℂ) (β : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (-((β : ℂ) • H))

/-- The Gibbs state `ω(x) = Tr(e^{-βH} x)/Tr(e^{-βH})`. -/
noncomputable def state (H : Matrix (Fin n) (Fin n) ℂ) (β : ℝ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (gibbs H β * x).trace / (gibbs H β).trace

/-- The imaginary-time twist `σ(b) = e^{-βH} b e^{βH}`. -/
noncomputable def twist (H : Matrix (Fin n) (Fin n) ℂ) (β : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  gibbs H β * b * NormedSpace.exp ((β : ℂ) • H)

/-
The KMS boundary identity: thermal equilibrium states are twisted-trace states.
-/
theorem D3_kms (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (β : ℝ)
    (a b : Matrix (Fin n) (Fin n) ℂ) :
    state H β (a * twist H β b) = state H β (b * a) := by
  norm_num [ state, twist ];
  -- By the properties of the trace and the exponential, we can simplify the expression.
  have h_exp : NormedSpace.exp ((β : ℂ) • H) * NormedSpace.exp (-(β : ℂ) • H) = 1 := by
    rw [ ← Matrix.exp_add_of_commute ];
    · norm_num [ ← add_smul ];
    · simp +decide [ SemiconjBy ];
  simp_all +decide [ ← mul_assoc, ← Matrix.ext_iff ];
  simp_all +decide [ gibbs, Matrix.mul_assoc, Matrix.trace_mul_comm ( NormedSpace.exp ( - ( β • H ) ) ) ];
  simp_all +decide [ ← Matrix.mul_assoc, show NormedSpace.exp ( β • H ) * NormedSpace.exp ( - ( β • H ) ) = 1 from Matrix.ext h_exp ];
  rw [ ← Matrix.trace_mul_comm ] ; simp +decide [ Matrix.mul_assoc ]

end D3