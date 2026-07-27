import Mathlib

open scoped BigOperators

namespace A5

/-!
# A5. The origination gauge: splittings form a torsor, automorphisms are unipotent

`0 → D →i M →p A → 0` a short exact sequence of real vector spaces.
(a) a splitting exists; (b) splittings form a torsor under `Hom(A, D)`;
(c) gauge automorphisms are unipotent and form a group isomorphic to `Hom(A, D)`.

(Finite-dimensionality is not needed: vector spaces over a field are projective.)
-/

variable {D M A : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup M] [Module ℝ M]
  [AddCommGroup A] [Module ℝ A]
variable (i : D →ₗ[ℝ] M) (p : M →ₗ[ℝ] A)

/-
`p ∘ i = 0`, from `range i = ker p`.
-/
lemma pi_zero (hex : LinearMap.range i = LinearMap.ker p) : p.comp i = 0 := by
  exact LinearMap.ext fun x => by simpa using LinearMap.mem_ker.mp ( hex ▸ LinearMap.mem_range_self i x ) ;

/-
(a) A splitting exists.
-/
theorem A5_a (hp : Function.Surjective p) :
    ∃ s : A →ₗ[ℝ] M, p.comp s = LinearMap.id := by
  convert ( Module.projective_def.mp ( show Module.Projective ℝ A from inferInstance ) );
  constructor <;> rintro ⟨ s, hs ⟩; all_goals exact?

/-
(b, existence+uniqueness) If `s, s'` are splittings then `s - s' = i ∘ h` for a
unique `h : A →ₗ[ℝ] D`.
-/
theorem A5_b_diff (hi : Function.Injective i)
    (hex : LinearMap.range i = LinearMap.ker p)
    (s s' : A →ₗ[ℝ] M) (hs : p.comp s = LinearMap.id) (hs' : p.comp s' = LinearMap.id) :
    ∃! h : A →ₗ[ℝ] D, s - s' = i.comp h := by
  -- By definition of $h$, we know that for any $a \in A$, $(s - s') a \in \text{range}(i)$.
  have h_range : ∀ a : A, (s - s') a ∈ LinearMap.range i := by
    simp_all +decide [ funext_iff, LinearMap.ext_iff ];
  -- Since $i$ is injective, for each $a \in A$, there exists a unique $d \in D$ such that $i d = (s - s') a$.
  obtain ⟨h, hh⟩ : ∃ h : A →ₗ[ℝ] D, ∀ a : A, i (h a) = (s - s') a := by
    choose h hh using h_range;
    refine' ⟨ { toFun := h, map_add' := _, map_smul' := _ }, hh ⟩ <;> intros <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · exact hi ( by simp +decide [ hh, map_add, sub_add_sub_comm ] );
    · exact hi ( by simp +decide [ hh, smul_sub ] );
  refine' ⟨ h, _, _ ⟩ <;> aesop

/-
(b, converse) `s + i ∘ h` is again a splitting.
-/
theorem A5_b_add (hex : LinearMap.range i = LinearMap.ker p)
    (s : A →ₗ[ℝ] M) (hs : p.comp s = LinearMap.id) (h : A →ₗ[ℝ] D) :
    p.comp (s + i.comp h) = LinearMap.id := by
  simp_all +decide [ LinearMap.ext_iff ];
  exact fun x => LinearMap.mem_ker.mp ( hex ▸ LinearMap.mem_range_self i _ )

/-
(c, unipotent) Every gauge automorphism `φ` satisfies `(φ - id)² = 0`.
-/
theorem A5_c_unipotent (hex : LinearMap.range i = LinearMap.ker p)
    (φ : M ≃ₗ[ℝ] M) (h1 : φ.toLinearMap.comp i = i) (h2 : p.comp φ.toLinearMap = p) :
    (φ.toLinearMap - LinearMap.id).comp (φ.toLinearMap - LinearMap.id) = 0 := by
  simp_all +decide [ funext_iff, LinearMap.ext_iff ];
  intro x
  have h_mem : φ x - x ∈ LinearMap.range i := by
    simp_all +decide [ LinearMap.mem_ker ]
  obtain ⟨d, hd⟩ : ∃ d : D, φ x - x = i d := by
    simpa [ eq_comm ] using h_mem;
  simp_all +decide [ sub_eq_iff_eq_add ]

/-- The group of gauge automorphisms. -/
def G : Subgroup (M ≃ₗ[ℝ] M) where
  carrier := {φ | φ.toLinearMap.comp i = i ∧ p.comp φ.toLinearMap = p}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    rw [LinearMap.ext_iff] at ha1 hb1 ha2 hb2
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at ha1 hb1 ha2 hb2
    refine ⟨LinearMap.ext (fun x => ?_), LinearMap.ext (fun x => ?_)⟩
    · simp only [LinearMap.comp_apply]
      show a (b (i x)) = i x
      rw [hb1 x, ha1 x]
    · simp only [LinearMap.comp_apply]
      show p (a (b x)) = p x
      rw [ha2 (b x), hb2 x]
  one_mem' := by refine ⟨?_, ?_⟩ <;> · ext x; rfl
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    rw [LinearMap.ext_iff] at ha1 ha2
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at ha1 ha2
    refine ⟨LinearMap.ext (fun x => ?_), LinearMap.ext (fun x => ?_)⟩
    · simp only [LinearMap.comp_apply]
      show a.symm (i x) = i x
      conv_lhs => rw [← ha1 x]
      rw [LinearEquiv.symm_apply_apply]
    · simp only [LinearMap.comp_apply]
      show p (a.symm x) = p x
      conv_rhs => rw [← LinearEquiv.apply_symm_apply a x]
      exact (ha2 (a.symm x)).symm

/-
(c, group iso) `G` is isomorphic to the additive group `Hom(A, D)`.
-/
theorem A5_c_group (hi : Function.Injective i)
    (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p) :
    Nonempty (G i p ≃* Multiplicative (A →ₗ[ℝ] D)) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : M →ₗ[ℝ] D, ρ.comp i = LinearMap.id := by
    exact?
  obtain ⟨σ, hσ⟩ : ∃ σ : A →ₗ[ℝ] M, p.comp σ = LinearMap.id := by
    exact?;
  -- Define the map from $G$ to $Hom(A, D)$ by $\varphi \mapsto \rho \circ (\varphi - id) \circ \sigma$.
  have h_map : ∀ φ ∈ G i p, ∃! h : A →ₗ[ℝ] D, (φ.toLinearMap - LinearMap.id) = i.comp (h.comp p) := by
    intro φ hφ
    obtain ⟨h, hh⟩ : ∃ h : A →ₗ[ℝ] D, (φ.toLinearMap - LinearMap.id) = i.comp (h.comp p) := by
      use ρ.comp ((φ.toLinearMap - LinearMap.id).comp σ);
      ext x;
      -- Since $p(x - \sigma(p(x))) = 0$, we have $x - \sigma(p(x)) \in \ker(p) = \operatorname{im}(i)$.
      have h_im : x - σ (p x) ∈ LinearMap.range i := by
        simp_all +decide [ LinearMap.ext_iff ];
      obtain ⟨ y, hy ⟩ := h_im; simp_all +decide [ LinearMap.ext_iff ] ;
      have h_eq : φ (i y) = i y := by
        exact LinearMap.congr_fun hφ.1 y;
      have := hφ.2; simp_all +decide [ LinearMap.ext_iff ] ;
      have h_eq : φ (σ (p x)) - σ (p x) ∈ LinearMap.range i := by
        simp_all +decide [ SetLike.ext_iff ];
      obtain ⟨ z, hz ⟩ := h_eq; simp_all +decide [ sub_eq_iff_eq_add ] ;
      grind +locals
    use h
    constructor
    · exact hh
    · intro h' hh'
      have h_eq : h' ∘ₗ p = h ∘ₗ p := by
        exact LinearMap.ext fun x => hi <| by simpa using congr_arg ( fun f => f x ) ( hh'.symm.trans hh ) ;
      exact LinearMap.ext fun x => by obtain ⟨ y, rfl ⟩ := hp x; simpa using LinearMap.congr_fun h_eq y;
  choose! f hf₁ hf₂ using h_map;
  -- Show that the map $f$ is a group homomorphism.
  have h_hom : ∀ φ ψ : M ≃ₗ[ℝ] M, φ ∈ G i p → ψ ∈ G i p → f (φ * ψ) = f φ + f ψ := by
    intro φ ψ hφ hψ
    have h_eq : (φ * ψ).toLinearMap - LinearMap.id = i.comp ((f φ + f ψ).comp p) := by
      have h_eq : (φ * ψ).toLinearMap - LinearMap.id = (φ.toLinearMap - LinearMap.id) + (ψ.toLinearMap - LinearMap.id) + (φ.toLinearMap - LinearMap.id).comp (ψ.toLinearMap - LinearMap.id) := by
        ext; simp +decide [ sub_mul, mul_sub ] ;
      have h_eq : (φ.toLinearMap - LinearMap.id).comp (ψ.toLinearMap - LinearMap.id) = 0 := by
        simp +decide [ LinearMap.ext_iff, hf₁ φ hφ, hf₁ ψ hψ ];
        intro x; replace hex := SetLike.ext_iff.mp hex ( i ( f ψ ( p x ) ) ) ; simp_all +decide [ LinearMap.mem_ker ] ;
      simp_all +decide [ LinearMap.ext_iff ];
    exact hf₂ _ ( Subgroup.mul_mem _ hφ hψ ) _ h_eq ▸ rfl;
  -- Show that the map $f$ is surjective.
  have h_surj : ∀ h : A →ₗ[ℝ] D, ∃ φ ∈ G i p, f φ = h := by
    intro h
    use LinearEquiv.ofLinear (LinearMap.id + i.comp (h.comp p)) (LinearMap.id - i.comp (h.comp p)) (by
    simp +decide [ LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply ];
    intro x; replace hex := SetLike.ext_iff.mp hex ( i ( h ( p x ) ) ) ; aesop;) (by
    ext x; simp +decide [ sub_mul, mul_add, sub_add_cancel ] ;
    simp +decide [ add_comm, add_left_comm, add_assoc, LinearMap.mem_ker.mp ( show p ( i ( h ( p x ) ) ) = 0 from by rw [ SetLike.ext_iff ] at hex; specialize hex ( i ( h ( p x ) ) ) ; aesop ) ])
    generalize_proofs at *;
    refine' ⟨ _, _ ⟩;
    · constructor <;> ext x <;> simp +decide [ LinearMap.ext_iff ] at *;
      · simp +decide [ show p ( i x ) = 0 from LinearMap.mem_ker.mp ( hex ▸ LinearMap.mem_range_self i x ) ];
      · exact LinearMap.mem_ker.mp ( hex ▸ LinearMap.mem_range_self i _ );
    · rw [ ← hf₂ ];
      all_goals norm_num [ LinearMap.ext_iff ];
      constructor <;> simp +decide [ LinearMap.ext_iff ];
      · intro x; replace hex := SetLike.ext_iff.mp hex ( i x ) ; aesop;
      · exact fun x => LinearMap.mem_ker.mp ( hex ▸ LinearMap.mem_range_self i _ );
  refine' ⟨ _ ⟩;
  refine' { Equiv.ofBijective ( fun x => Multiplicative.ofAdd ( f x.val ) ) ⟨ _, _ ⟩ with .. };
  all_goals simp +decide [ Function.Injective, Function.Surjective, h_hom ];
  · grind +suggestions;
  · exact h_surj

end A5