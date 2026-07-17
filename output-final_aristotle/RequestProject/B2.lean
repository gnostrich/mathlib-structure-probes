import Mathlib

open scoped BigOperators Matrix

namespace B2

/-!
# B2. Kronecker recurrence (scalar): finite Hankel rank ⟹ linear recurrence

If every `N × N` Hankel matrix of `(m_k)` has rank `≤ r`, then there is a nonzero
`(c_0, …, c_r)` with `Σ_j c_j m_{k+j} = 0` for all `k`.
-/

/-- The `N × N` Hankel matrix of a sequence. -/
noncomputable def hankel (m : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => m ((i : ℕ) + (j : ℕ)))

theorem B2_recurrence (m : ℕ → ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hrank : ∀ N, (hankel m N).rank ≤ r) :
    ∃ c : Fin (r + 1) → ℝ, c ≠ 0 ∧ ∀ k : ℕ, ∑ j : Fin (r + 1), c j * m (k + (j : ℕ)) = 0 := by
  -- By definition of $K_N$, we know that $K_N$ is nonempty for each $N$.
  have h_nonempty : ∀ N : ℕ, ∃ c : Fin (r + 1) → ℝ, c ≠ 0 ∧ ∀ i : Fin N, ∑ j : Fin (r + 1), c j * m (i.val + j.val) = 0 := by
    intro N
    have h_subspace : ∃ c : Fin (r + 1) → ℝ, c ≠ 0 ∧ Matrix.mulVec (Matrix.of (fun (i : Fin N) (j : Fin (r + 1)) => m ((i : ℕ) + (j : ℕ)))) c = 0 := by
      have h_rank : Matrix.rank (Matrix.of (fun (i : Fin N) (j : Fin (r + 1)) => m ((i : ℕ) + (j : ℕ)))) ≤ r := by
        convert hrank ( Max.max N ( r + 1 ) ) |> le_trans _ using 1;
        have h_submatrix : ∃ (P : Matrix (Fin N) (Fin (max N (r + 1))) ℝ) (Q : Matrix (Fin (r + 1)) (Fin (max N (r + 1))) ℝ), Matrix.of (fun (i : Fin N) (j : Fin (r + 1)) => m (i.val + j.val)) = P * hankel m (max N (r + 1)) * Q.transpose := by
          refine' ⟨ Matrix.of fun i j => if j = ⟨ i, by linarith [ Fin.is_lt i, Nat.le_max_left N ( r + 1 ), Nat.le_max_right N ( r + 1 ) ] ⟩ then 1 else 0, Matrix.of fun i j => if j = ⟨ i, by linarith [ Fin.is_lt i, Nat.le_max_left N ( r + 1 ), Nat.le_max_right N ( r + 1 ) ] ⟩ then 1 else 0, _ ⟩ ; ext i j ; simp +decide [ Matrix.mul_apply ] ; ring;
          rfl;
        obtain ⟨ P, Q, hPQ ⟩ := h_submatrix; rw [ hPQ ] ; exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _;
      contrapose! h_rank;
      rw [ Matrix.rank ];
      rw [ @LinearMap.finrank_range_of_inj ];
      · norm_num;
      · exact fun x y hxy => Classical.not_not.1 fun h => h_rank ( x - y ) ( sub_ne_zero_of_ne h ) ( by simpa [ sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_neg ] using sub_eq_zero.2 hxy );
    exact ⟨ h_subspace.choose, h_subspace.choose_spec.1, fun i => by simpa only [ Matrix.mulVec, dotProduct, mul_comm ] using congr_fun h_subspace.choose_spec.2 i ⟩;
  choose f hf1 hf2 using h_nonempty;
  -- By normalizing $f_N$, we can ensure that $\|f_N\| = 1$ for all $N$.
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Fin (r + 1) → ℝ, (∀ N, ∑ j, g N j ^ 2 = 1) ∧ (∀ N, ∀ i : Fin N, ∑ j : Fin (r + 1), g N j * m (i.val + j.val) = 0) := by
    use fun N => fun j => f N j / Real.sqrt (∑ j, f N j ^ 2);
    field_simp;
    exact ⟨ fun N => by rw [ ← Finset.sum_div, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _, div_self <| ne_of_gt <| lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) <| Ne.symm <| by intro H; exact hf1 N <| funext fun i => by simpa [ H ] using Finset.sum_eq_zero_iff_of_nonneg ( fun _ _ => sq_nonneg _ ) |>.1 H i ], fun N i => by rw [ ← Finset.sum_div, hf2 N i, zero_div ] ⟩;
  -- By the Bolzano-Weierstrass theorem, the sequence $g_N$ has a convergent subsequence.
  obtain ⟨c, hc⟩ : ∃ c : Fin (r + 1) → ℝ, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => g (subseq n)) Filter.atTop (nhds c) := by
    have h_compact : IsCompact (Set.pi Set.univ fun _ : Fin (r + 1) => Set.Icc (-1 : ℝ) 1) := by
      exact isCompact_univ_pi fun _ => CompactIccSpace.isCompact_Icc;
    have := h_compact.isSeqCompact fun n => show g n ∈ Set.pi Set.univ fun _ => Set.Icc ( -1 ) 1 from fun i _ => ⟨ by nlinarith only [ hg.1 n, Finset.single_le_sum ( fun a _ => sq_nonneg ( g n a ) ) ( Finset.mem_univ i ) ], by nlinarith only [ hg.1 n, Finset.single_le_sum ( fun a _ => sq_nonneg ( g n a ) ) ( Finset.mem_univ i ) ] ⟩ ; aesop;
  obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hc; use c; refine' ⟨ _, _ ⟩ <;> simp_all +decide [ funext_iff ] ;
  · contrapose! hg; simp_all +decide [ tendsto_pi_nhds ] ;
    intro h; have := tendsto_finset_sum _ fun i ( hi : i ∈ Finset.univ ) => Filter.Tendsto.pow ( hsubseq₂ i ) 2; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ;
  · intro k; exact (by
    exact tendsto_nhds_unique ( tendsto_finset_sum _ fun _ _ => Filter.Tendsto.mul ( tendsto_pi_nhds.mp hsubseq₂ _ ) tendsto_const_nhds ) ( tendsto_const_nhds.congr' <| by filter_upwards [ hsubseq₁.tendsto_atTop.eventually_gt_atTop k ] with n hn; rw [ hg.2 _ ⟨ k, by linarith ⟩ ] ));

end B2