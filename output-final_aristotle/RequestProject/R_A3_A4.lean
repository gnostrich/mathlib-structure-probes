import Mathlib
import RequestProject.R_A2

open scoped BigOperators Matrix
open Horizon

set_option maxHeartbeats 4000000

namespace TierR
namespace GramState

/-- R-A3: extend a certified state by one bordered site, provided its scalar Schur gate is positive. -/
noncomputable def expand (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : 0 < schur G.M b d) : GramState where
  dim := G.dim + 1
  M := border G.M b d
  hsymm := border_transpose G.M G.hsymm b d
  hpd := schur_pos_isPDq G.M G.hsymm G.hpd b d hs
  nonempty := ⟨by omega⟩

@[simp] theorem expand_dim (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : 0 < schur G.M b d) : (G.expand b d hs).dim = G.dim + 1 := rfl

@[simp] theorem expand_old (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : 0 < schur G.M b d) (i j : Fin G.dim) :
    (G.expand b d hs).M (Fin.castSucc i) (Fin.castSucc j) = G.M i j := by
  exact border_old _ _ _ _ _

@[simp] theorem expand_last_col (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : 0 < schur G.M b d) (i : Fin G.dim) :
    (G.expand b d hs).M (Fin.castSucc i) (Fin.last G.dim) = b i := by
  exact border_last_col _ _ _ _

@[simp] theorem expand_last_row (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : 0 < schur G.M b d) (i : Fin G.dim) :
    (G.expand b d hs).M (Fin.last G.dim) (Fin.castSucc i) = b i := by
  exact border_last_row _ _ _ _

@[simp] theorem expand_corner (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : 0 < schur G.M b d) :
    (G.expand b d hs).M (Fin.last G.dim) (Fin.last G.dim) = d := by
  exact border_corner _ _ _

/-- R-A3(c), invariant preservation: expansion always carries a proof for its new matrix. -/
theorem expand_pd (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : 0 < schur G.M b d) : IsPDq (G.expand b d hs).M :=
  (G.expand b d hs).hpd

/-- The canonical nonzero vector exposing a failed Schur gate. -/
noncomputable def haltVector (G : GramState) (b : Fin G.dim → ℝ) :
    Fin (G.dim + 1) → ℝ := Fin.snoc (fun i => -(G.M⁻¹ *ᵥ b) i) 1

/-- R-A4: a nonpositive Schur gate packages an explicit non-PD witness. -/
noncomputable def haltWitness (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : schur G.M b d ≤ 0) :
    {x : Fin (G.dim + 1) → ℝ // x ≠ 0 ∧ quadForm (border G.M b d) x ≤ 0} := by
  refine ⟨haltVector G b, ?_, ?_⟩
  · intro h
    have := congr_fun h (Fin.last G.dim)
    simp [haltVector] at this
  · rw [border_quadForm_complete G.M G.hsymm G.hpd b d]
    simp [haltVector, quadForm]
    exact hs

/-- Honest halt: failure of the strict scalar gate proves that the proposed border is not PD. -/
theorem halt_not_pd (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ)
    (hs : schur G.M b d ≤ 0) : ¬ IsPDq (border G.M b d) := by
  intro h
  obtain ⟨x, hx, hq⟩ := haltWitness G b d hs
  exact (not_lt_of_ge hq) (h x hx)

/-- The strict gate holds exactly when the proposed symmetric border is positive definite. -/
theorem expand_gate_iff_pd (G : GramState) (b : Fin G.dim → ℝ) (d : ℝ) :
    0 < schur G.M b d ↔ IsPDq (border G.M b d) := by
  constructor
  · exact schur_pos_isPDq G.M G.hsymm G.hpd b d
  · exact border_pd_schur_pos G.M G.hsymm b d

end GramState
end TierR
