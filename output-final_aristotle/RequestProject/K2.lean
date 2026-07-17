import Mathlib
import RequestProject.Horizon
import RequestProject.K1

open scoped BigOperators Matrix
open Horizon

namespace K2

/-!
# K2. Screw-to-Gram map and the free case

For an even function `g : ℝ → ℝ` with `g 0 = 0`, the associated Gram kernel is
`G_g(t, s) = g t + g s - g (t - s)`.

* (a) `G_g` is symmetric (needs `g` even), and `G_g(t,t) = 2 · g t` (needs `g 0 = 0`).
* (b) for `g = |·|` and `0 < t_1 < … < t_n`, `[G_g(t_i, t_j)] = [2 · min(t_i, t_j)]`, which is
  positive definite (via K1).
* (c) screw-type functions on a fixed grid form a convex cone: the Gram kernel of `g + h` is
  PSD if both are, and likewise for `c · g` with `c ≥ 0`.
-/

/-- The Gram kernel matrix `G_g(t_i, t_j) = g (t i) + g (t j) - g (t i - t j)` on a grid. -/
def GramMat {n : ℕ} (g : ℝ → ℝ) (t : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => g (t i) + g (t j) - g (t i - t j)

/-- (a) Symmetry of the Gram kernel for an even `g`. -/
theorem K2_a_symm {n : ℕ} (g : ℝ → ℝ) (heven : ∀ x, g (-x) = g x) (t : Fin n → ℝ) :
    (GramMat g t)ᵀ = GramMat g t := by
  ext i j
  simp only [Matrix.transpose_apply, GramMat]
  rw [show t j - t i = -(t i - t j) by ring, heven]; ring

/-- (a) Diagonal of the Gram kernel when `g 0 = 0`. -/
theorem K2_a_diag {n : ℕ} (g : ℝ → ℝ) (h0 : g 0 = 0) (t : Fin n → ℝ) (i : Fin n) :
    GramMat g t i i = 2 * g (t i) := by
  simp only [GramMat]; rw [sub_self, h0]; ring

/-- (b) For `g = |·|` on a positive grid, the Gram kernel is twice the min-kernel. -/
theorem K2_b_eq {n : ℕ} (t : Fin n → ℝ) (hpos : ∀ i, 0 < t i) :
    GramMat (fun x => |x|) t = (2 : ℝ) • K1.minMat t := by
  ext i j
  simp only [GramMat, Matrix.smul_apply, K1.minMat, smul_eq_mul]
  rw [abs_of_pos (hpos i), abs_of_pos (hpos j)]
  rcases le_total (t i) (t j) with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- (b) Consequently the free Gram kernel is positive definite. -/
theorem K2_b_posdef {n : ℕ} (t : Fin n → ℝ) (hmono : StrictMono t) (hpos : ∀ i, 0 < t i) :
    IsPDq (GramMat (fun x => |x|) t) := by
  rw [K2_b_eq t hpos]
  intro x hx
  have h2 : quadForm ((2 : ℝ) • K1.minMat t) x = 2 * quadForm (K1.minMat t) x := by
    simp only [quadForm, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [h2]
  have := K1.K1_posdef t hmono hpos x hx
  linarith

/-- (c) The Gram kernel of a sum is the sum of Gram kernels. -/
theorem K2_c_add_eq {n : ℕ} (g h : ℝ → ℝ) (t : Fin n → ℝ) :
    GramMat (fun x => g x + h x) t = GramMat g t + GramMat h t := by
  ext i j; simp only [GramMat, Matrix.add_apply]; ring

/-- (c) PSD is preserved under sums (convex cone, additivity). -/
theorem K2_c_add {n : ℕ} (g h : ℝ → ℝ) (t : Fin n → ℝ)
    (hg : IsPSDq (GramMat g t)) (hh : IsPSDq (GramMat h t)) :
    IsPSDq (GramMat (fun x => g x + h x) t) := by
  rw [K2_c_add_eq]; intro x; rw [Horizon.quadForm_add]; exact add_nonneg (hg x) (hh x)

/-- (c) PSD is preserved under nonnegative scaling (convex cone, positive homogeneity). -/
theorem K2_c_smul {n : ℕ} (g : ℝ → ℝ) (t : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hg : IsPSDq (GramMat g t)) :
    IsPSDq (GramMat (fun x => c * g x) t) := by
  intro x
  have hq : quadForm (GramMat (fun x => c * g x) t) x = c * quadForm (GramMat g t) x := by
    simp only [quadForm, GramMat]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [hq]; exact mul_nonneg hc (hg x)

end K2
