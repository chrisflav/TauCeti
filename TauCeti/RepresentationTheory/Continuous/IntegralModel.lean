/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.Lattice
public import TauCeti.RepresentationTheory.Continuous.StableLattice
public import TauCeti.Topology.Algebra.Module.LatticeStabilizer

/-!
# Integral models of continuous representations

Let `ρ` be a jointly continuous representation (`TauCeti.ContinuousRep`) of a topological monoid
`Γ` on a module `V` over a ring `E`, and let `O → E` be a ring map, typically the inclusion of a
discrete valuation ring into its fraction field. An *integral model* of `ρ` over `O` is a
`Γ`-stable full lattice `Λ ⊆ V`: a finitely generated `O`-submodule spanning `V` over `E`
(Mathlib's `Submodule.IsLattice E Λ`) and preserved by every `ρ g`. For an `ℓ`-adic Galois
representation on a `ℚ_ℓ`-vector space, an integral model is a `Γ`-stable `ℤ_ℓ`-lattice, the
object whose reductions modulo `ℓⁿ` are the finite-level Galois representations.

This file develops the theory of integral models:

* `Γ` acts on `Λ` by restriction (`TauCeti.GaloisLattice.IntegralModel.toContinuousRep`), jointly
  continuously for the subspace topology.
* Scalar extension recovers the given representation: for a domain `O` with fraction field `E`
  and `Λ` free, `E ⊗[O] Λ ≅ V` equivariantly through the rationalization equivalence
  `Submodule.rationalizationEquiv` (`TauCeti.GaloisLattice.IntegralModel.genericFiberIso`). This
  is stated for `Λ` with its `O`-module topology; over the valuation ring of a field with a
  valuative topology, such as a nonarchimedean local field, the subspace topology on a lattice is
  its module topology (`Submodule.IsLattice.isModuleTopology`), and the valuation ring of a
  nonarchimedean local field is a discrete valuation ring, so every lattice there is free.
* The units of `E` act on integral models by homothety, and integral models are ordered by
  inclusion, with sums and, over a principal ideal domain with fraction field `E`,
  intersections. In a subsingleton space, the zero lattice is the unique integral model
  (`TauCeti.GaloisLattice.IntegralModel.uniqueOfSubsingleton`).
* Integral models pull back along continuous monoid homomorphisms
  (`TauCeti.GaloisLattice.IntegralModel.comp`) and push forward along isomorphisms of continuous
  representations (`TauCeti.GaloisLattice.IntegralModel.map`).
* For a `Γ`-stable subspace `W ⊆ V`, intersecting `Λ` with `W` produces an integral model of the
  subrepresentation (`TauCeti.GaloisLattice.IntegralModel.subrepresentation`, over a Noetherian
  ring with fraction field `E`), projecting `Λ` to `V ⧸ W` produces an integral model of the
  quotient representation (`TauCeti.GaloisLattice.IntegralModel.quotient`), the quotient
  `Λ ⧸ (W ∩ Λ)` is torsion-free, and over a principal ideal domain the short exact sequence
  `0 → W ∩ Λ → Λ → Λ ⧸ (W ∩ Λ) → 0` splits
  (`TauCeti.GaloisLattice.IntegralModel.exists_rightInverse_mkQ_comap`,
  `TauCeti.GaloisLattice.IntegralModel.exists_linearEquiv_prod_subrepresentation_quotient`).
* For a group `Γ` with continuous inversion, the integral dual of a free integral model is an
  integral model of the contragredient representation (`TauCeti.GaloisLattice.IntegralModel.dual`);
  duality strictly reverses inclusion, sends `c • Λ` to `c⁻¹ • Λ.dual`, interchanges sums and
  intersections over a principal ideal domain, and satisfies biduality
  `Λ.map ρ.evalIso = Λ.dual.dual`
  (`TauCeti.GaloisLattice.IntegralModel.map_evalIso_eq_dual_dual`).
* A rank-one character representation `ContinuousRep.ofCharacter χ` over a principal ideal domain
  with fraction field `E` admits an integral model if and only if `χ` takes integral values
  (`TauCeti.GaloisLattice.IntegralModel.nonempty_ofCharacter_iff`); over a discrete valuation ring
  with uniformizer `ϖ`, its integral models are uniquely of the form `ϖᵏ • 1` (`k : ℤ`)
  (`TauCeti.GaloisLattice.IntegralModel.existsUnique_zpow_smul_ofCharacter`), and duality sends
  `c • 1` to `c⁻¹ • 1` for `χ⁻¹`
  (`TauCeti.GaloisLattice.IntegralModel.map_dualOfCharacterIso_dual_smul`).
* A representation of a compact group on a finite-dimensional vector space over a field with a
  valuative topology, such as a nonarchimedean local field, has an integral model over the
  valuation ring (`TauCeti.GaloisLattice.IntegralModel.nonempty`), by the stable-lattice theorem.
  Choosing a basis of a free integral model converts the representation into a continuous matrix
  homomorphism into `GL ι O` (`TauCeti.GaloisLattice.IntegralModel.toGeneralLinearGroupHom`),
  yielding the matrix form of the stable-lattice theorem
  (`TauCeti.ContinuousRep.exists_basis_continuousMonoidHom_generalLinearGroup`).
* Over a discrete valuation ring with fraction field `E`, any two integral models are
  commensurable: `𝔪ᵃ Λ ⊆ Λ'` and `𝔪ᵃ Λ' ⊆ Λ` for some `a`
  (`TauCeti.GaloisLattice.IntegralModel.exists_pow_le`).

## Main definitions

* `TauCeti.GaloisLattice.IntegralModel O ρ`: the integral models of `ρ` over `O`.
* `TauCeti.GaloisLattice.IntegralModel.toContinuousRep`: the restricted action of `Γ` on `Λ`.
* `TauCeti.GaloisLattice.IntegralModel.genericFiberIso`: the equivariant identification of the
  scalar extension `E ⊗[O] Λ` with `V`.
* `TauCeti.GaloisLattice.IntegralModel.comp` and `TauCeti.GaloisLattice.IntegralModel.map`:
  pullback along a continuous monoid homomorphism and pushforward along an isomorphism.
* `TauCeti.GaloisLattice.IntegralModel.subrepresentation` and
  `TauCeti.GaloisLattice.IntegralModel.quotient`: saturated sublattice and quotient integral
  models attached to a `Γ`-stable subspace.
* `TauCeti.GaloisLattice.IntegralModel.dual`: the dual integral model of the contragredient
  representation.
* `TauCeti.GaloisLattice.IntegralModel.ofCharacter`: the standard integral model of an integral
  character line.
* `TauCeti.ContinuousRep.toLinearEquivHom`,
  `TauCeti.GaloisLattice.IntegralModel.toGeneralLinearGroupHom`, and
  `TauCeti.ContinuousRep.exists_basis_continuousMonoidHom_generalLinearGroup`: continuous
  automorphism homomorphism, matrix form in a lattice basis, and matrix form of the
  stable-lattice theorem.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, paragraph after
  Proposition 2.6.
* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *$\hat{G}$-local systems on smooth projective
  curves are potentially automorphic*, Theorem 4.8(ii).
-/

public section

open Module Submodule
open scoped Pointwise TensorProduct

namespace TauCeti.GaloisLattice

section Basic

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] (O : Type*) [CommRing O]
  {E : Type*} [CommRing E] [Algebra O E] {V : Type*} [AddCommGroup V] [Module E V] [Module O V]
  [IsScalarTower O E V] [TopologicalSpace V]

/-- **An integral model** of a continuous representation `ρ` of `Γ` on `V` over the coefficient
ring `O`: a full `O`-lattice in `V` (finitely generated over `O` and spanning `V` over `E`) that
is stable under every `ρ g`. -/
@[ext]
structure IntegralModel (ρ : ContinuousRep Γ E V) where
  /-- The underlying lattice. -/
  lattice : Submodule O V
  /-- The lattice is full: finitely generated over `O` and spanning `V` over `E`. -/
  isLattice : lattice.IsLattice E
  /-- The lattice is stable under the action. -/
  stable : ∀ g, ∀ x ∈ lattice, ρ g x ∈ lattice

attribute [instance] IntegralModel.isLattice

namespace IntegralModel

variable {O} {ρ : ContinuousRep Γ E V}

/-- An integral model is determined by its lattice. -/
theorem lattice_injective : Function.Injective (lattice : IntegralModel O ρ → Submodule O V) :=
  fun _ _ ↦ IntegralModel.ext

/-! ### The restricted action -/

/-- **The restriction of `ρ` to an integral model.** `Γ` acts `O`-linearly on the lattice `Λ`,
and the action is jointly continuous for the subspace topology on `Λ`. -/
def toContinuousRep (Λ : IntegralModel O ρ) : ContinuousRep Γ O Λ.lattice where
  toRepresentation :=
    { toFun g :=
        { toFun x := ⟨ρ g x, Λ.stable g x x.2⟩
          map_add' x y := Subtype.ext (map_add (ρ g) (x : V) y)
          map_smul' a x := Subtype.ext ((ρ g).map_smul_of_tower a (x : V)) }
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }
  continuous_action := (ρ.continuous_action.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- The inclusion of an integral model intertwines its action with the action on `V`. -/
@[simp]
theorem coe_toContinuousRep_apply (Λ : IntegralModel O ρ) (g : Γ) (x : Λ.lattice) :
    (Λ.toContinuousRep g x : V) = ρ g x :=
  (rfl)

/-! ### Homotheties -/

/-- The units of `E` act on integral models by homothety, `c • Λ`. -/
instance : MulAction Eˣ (IntegralModel O ρ) where
  smul c Λ :=
    { lattice := c • Λ.lattice
      isLattice := inferInstance
      stable g x hx := by
        obtain ⟨y, hy, rfl⟩ := (mem_smul_pointwise_iff_exists x c Λ.lattice).mp hx
        rw [LinearMap.map_smul_of_tower]
        exact smul_mem_pointwise_smul _ c _ (Λ.stable g y hy) }
  one_smul Λ := IntegralModel.ext (one_smul _ Λ.lattice)
  mul_smul c d Λ := IntegralModel.ext (mul_smul c d Λ.lattice)

@[simp]
theorem lattice_smul (c : Eˣ) (Λ : IntegralModel O ρ) : (c • Λ).lattice = c • Λ.lattice :=
  (rfl)

/-- Scaling a free integral model by a unit preserves freeness of its underlying lattice. -/
instance free_lattice_smul (c : Eˣ) (Λ : IntegralModel O ρ) [Module.Free O Λ.lattice] :
    Module.Free O (c • Λ).lattice :=
  Submodule.free_smul c Λ.lattice

/-! ### Inclusion, sums and intersections -/

instance : LE (IntegralModel O ρ) where
  le Λ Λ' := Λ.lattice ≤ Λ'.lattice

instance : LT (IntegralModel O ρ) where
  lt Λ Λ' := Λ.lattice < Λ'.lattice

@[simp]
theorem lattice_le_lattice {Λ Λ' : IntegralModel O ρ} : Λ.lattice ≤ Λ'.lattice ↔ Λ ≤ Λ' :=
  .rfl

@[simp]
theorem lattice_lt_lattice {Λ Λ' : IntegralModel O ρ} : Λ.lattice < Λ'.lattice ↔ Λ < Λ' :=
  .rfl

/-- The sum `Λ + Λ'` of two integral models. -/
instance : Max (IntegralModel O ρ) where
  max Λ Λ' :=
    { lattice := Λ.lattice ⊔ Λ'.lattice
      isLattice := inferInstance
      stable g x hx := by
        obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
        rw [map_add]
        exact add_mem (mem_sup_left (Λ.stable g y hy)) (mem_sup_right (Λ'.stable g z hz)) }

@[simp]
theorem lattice_sup (Λ Λ' : IntegralModel O ρ) : (Λ ⊔ Λ').lattice = Λ.lattice ⊔ Λ'.lattice :=
  (rfl)

instance : SemilatticeSup (IntegralModel O ρ) :=
  lattice_injective.semilatticeSup _ .rfl .rfl lattice_sup

end IntegralModel

end Basic

section Inf

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O] [IsDomain O]
  [IsPrincipalIdealRing O] {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [TopologicalSpace V]
  {ρ : ContinuousRep Γ E V}

namespace IntegralModel

/-- The intersection `Λ ∩ Λ'` of two integral models over a principal ideal domain with fraction
field `E`. -/
instance : Min (IntegralModel O ρ) where
  min Λ Λ' :=
    { lattice := Λ.lattice ⊓ Λ'.lattice
      isLattice :=
        have := Module.Finite.of_isLattice (A := E) Λ.lattice
        inferInstance
      stable g x hx := ⟨Λ.stable g x hx.1, Λ'.stable g x hx.2⟩ }

@[simp]
theorem lattice_inf (Λ Λ' : IntegralModel O ρ) : (Λ ⊓ Λ').lattice = Λ.lattice ⊓ Λ'.lattice :=
  (rfl)

instance : Lattice (IntegralModel O ρ) :=
  lattice_injective.lattice _ .rfl .rfl lattice_sup lattice_inf

end IntegralModel

end Inf

section GenericFiber

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O] [IsDomain O]
  [TopologicalSpace O] {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E]
  [TopologicalSpace E] [IsTopologicalSemiring E] [ContinuousSMul O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [TopologicalSpace V]
  [IsModuleTopology E V] {ρ : ContinuousRep Γ E V}

namespace IntegralModel

variable (Λ : IntegralModel O ρ) [Module.Free O Λ.lattice] [IsModuleTopology O Λ.lattice]
  [TopologicalSpace (E ⊗[O] Λ.lattice)] [IsModuleTopology E (E ⊗[O] Λ.lattice)]

/-- **The generic fibre of an integral model.** Extending scalars from `O` to its fraction field
`E` recovers the representation: `E ⊗[O] Λ ≅ V`, sending `a ⊗ x` to `a • x`. -/
noncomputable def genericFiberIso : ContinuousRep.Iso (Λ.toContinuousRep.baseChange E) ρ :=
  .ofEquiv (.mk (rationalizationEquiv Λ.lattice) fun g ↦ by
    ext x
    simp)

omit [IsDomain O] in
@[simp]
theorem genericFiberIso_tmul (a : E) (x : Λ.lattice) :
    Λ.genericFiberIso (a ⊗ₜ x) = a • (x : V) := by
  simp [genericFiberIso]

omit [IsDomain O] in
@[simp]
theorem genericFiberIso_symm_coe (x : Λ.lattice) :
    Λ.genericFiberIso.symm (x : V) = 1 ⊗ₜ x :=
  EquivLike.injective Λ.genericFiberIso <| by simp

end IntegralModel

end GenericFiber

section Existence

open ValuativeRel

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
  {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V]
  [TopologicalSpace V] [IsModuleTopology E V] [FiniteDimensional E V]

/-- **Existence of integral models.** A jointly continuous representation of a compact group on a
finite-dimensional vector space over a field with a valuative topology, for instance a
nonarchimedean local field, has an integral model over the valuation ring `𝒪[E]`. -/
instance IntegralModel.nonempty (ρ : ContinuousRep Γ E V) : Nonempty (IntegralModel 𝒪[E] ρ) :=
  let ⟨L, hL, hρL⟩ := ρ.exists_stable_lattice
  ⟨⟨L, hL, hρL⟩⟩

end Existence

section Commensurable

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [TopologicalSpace V]
  {ρ : ContinuousRep Γ E V}

/-- **Integral models are commensurable.** Over a discrete valuation ring `O` with fraction field
`E`, any two integral models `Λ`, `Λ'` satisfy `𝔪ᵃ Λ ⊆ Λ'` and `𝔪ᵃ Λ' ⊆ Λ` for some `a`, where
`𝔪` is the maximal ideal of `O`. -/
theorem IntegralModel.exists_pow_le (Λ Λ' : IntegralModel O ρ) :
    ∃ a : ℕ, IsLocalRing.maximalIdeal O ^ a • Λ.lattice ≤ Λ'.lattice ∧
      IsLocalRing.maximalIdeal O ^ a • Λ'.lattice ≤ Λ.lattice := by
  obtain ⟨m, hm⟩ := IsLattice.exists_maximalIdeal_pow_smul_le E Λ'.lattice
    (IsLattice.fg (A := E) (M := Λ.lattice))
  obtain ⟨n, hn⟩ := IsLattice.exists_maximalIdeal_pow_smul_le E Λ.lattice
    (IsLattice.fg (A := E) (M := Λ'.lattice))
  -- Powers of the maximal ideal decrease, so `a = max m n` works in both directions.
  refine ⟨max m n, (smul_mono_left ?_).trans hm, (smul_mono_left ?_).trans hn⟩ <;>
    exact Ideal.pow_le_pow_right (by omega)

end Commensurable

section Subsingleton

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O]
  {E : Type*} [CommRing E] [Algebra O E] {V : Type*} [AddCommGroup V] [Module E V] [Module O V]
  [IsScalarTower O E V] [TopologicalSpace V] {ρ : ContinuousRep Γ E V}

namespace IntegralModel

/-- **Dimension-zero uniqueness.** On a subsingleton space, the zero lattice is the unique
integral model of `ρ`. -/
instance uniqueOfSubsingleton [Subsingleton V] : Unique (IntegralModel O ρ) where
  default :=
    { lattice := ⊥
      isLattice := Submodule.isLattice_bot_of_subsingleton E
      stable := fun _ _ _ ↦ Subsingleton.elim _ _ }
  uniq _ := IntegralModel.ext (Subsingleton.elim _ _)

@[simp]
theorem lattice_default_of_subsingleton [Subsingleton V] :
    (default : IntegralModel O ρ).lattice = ⊥ :=
  (rfl)

end IntegralModel

end Subsingleton

section Comp

variable {Γ Γ' : Type*} [Monoid Γ] [TopologicalSpace Γ] [Monoid Γ'] [TopologicalSpace Γ']
  {O : Type*} [CommRing O] {E : Type*} [CommRing E] [Algebra O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [TopologicalSpace V] {ρ : ContinuousRep Γ E V}

namespace IntegralModel

/-- **Pullback of an integral model along a continuous monoid homomorphism.** Restricting `ρ`
along `f : Γ' →ₜ* Γ` preserves every integral model without choosing a basis. -/
def comp (Λ : IntegralModel O ρ) (f : Γ' →ₜ* Γ) : IntegralModel O (ρ.comp f) where
  lattice := Λ.lattice
  isLattice := Λ.isLattice
  stable g x hx := by simpa using Λ.stable (f g) x hx

@[simp]
theorem lattice_comp (Λ : IntegralModel O ρ) (f : Γ' →ₜ* Γ) :
    (Λ.comp f).lattice = Λ.lattice :=
  (rfl)

@[simp]
theorem comp_smul (c : Eˣ) (Λ : IntegralModel O ρ) (f : Γ' →ₜ* Γ) :
    (c • Λ).comp f = c • Λ.comp f :=
  (rfl)

end IntegralModel

end Comp

section Map

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O]
  {E : Type*} [CommRing E] [Algebra O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [TopologicalSpace V]
  {W : Type*} [AddCommGroup W] [Module E W] [Module O W] [IsScalarTower O E W] [TopologicalSpace W]
  {ρ : ContinuousRep Γ E V} {σ : ContinuousRep Γ E W}

namespace IntegralModel

/-- **Pushforward of an integral model along an isomorphism of continuous representations.** -/
def map (Λ : IntegralModel O ρ) (e : ContinuousRep.Iso ρ σ) : IntegralModel O σ where
  lattice := Λ.lattice.map (e.toRepresentationEquiv.toLinearEquiv.toLinearMap.restrictScalars O)
  isLattice := isLattice_map Λ.lattice e.toRepresentationEquiv.toLinearEquiv.toLinearMap
    e.surjective
  stable g y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨ρ g x, Λ.stable g x hx, e.isIntertwining g x⟩

@[simp]
theorem lattice_map (Λ : IntegralModel O ρ) (e : ContinuousRep.Iso ρ σ) :
    (Λ.map e).lattice =
      Λ.lattice.map (e.toRepresentationEquiv.toLinearEquiv.toLinearMap.restrictScalars O) :=
  (rfl)

theorem mem_lattice_map (Λ : IntegralModel O ρ) (e : ContinuousRep.Iso ρ σ) (y : W) :
    y ∈ (Λ.map e).lattice ↔ ∃ x ∈ Λ.lattice, e x = y := by
  simp only [lattice_map, Submodule.mem_map, LinearMap.restrictScalars_apply]
  rfl

@[simp]
theorem map_refl (Λ : IntegralModel O ρ) : Λ.map (.refl ρ) = Λ := by
  ext x
  simp

theorem map_trans {U : Type*} [AddCommGroup U] [Module E U] [Module O U] [IsScalarTower O E U]
    [TopologicalSpace U] {τ : ContinuousRep Γ E U}
    (Λ : IntegralModel O ρ) (e : ContinuousRep.Iso ρ σ) (f : ContinuousRep.Iso σ τ) :
    (Λ.map e).map f = Λ.map (e.trans f) := by
  ext z
  simp only [mem_lattice_map, ContinuousRep.Iso.trans_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩

@[simp]
theorem map_symm_map (Λ : IntegralModel O ρ) (e : ContinuousRep.Iso ρ σ) :
    (Λ.map e).map e.symm = Λ := by
  ext x
  simp only [mem_lattice_map]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

@[simp]
theorem map_map_symm (Λ : IntegralModel O σ) (e : ContinuousRep.Iso ρ σ) :
    (Λ.map e.symm).map e = Λ := by
  ext y
  simp only [mem_lattice_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨e.symm y, ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

@[simp]
theorem map_smul (c : Eˣ) (Λ : IntegralModel O ρ) (e : ContinuousRep.Iso ρ σ) :
    (c • Λ).map e = c • Λ.map e := by
  ext y
  simp only [mem_lattice_map, lattice_smul, mem_smul_pointwise_iff_exists, Units.smul_def]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, (_root_.map_smul e (c : E) x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(c : E) • x, ⟨x, hx, rfl⟩, _root_.map_smul e (c : E) x⟩

@[simp]
theorem map_le_map_iff (e : ContinuousRep.Iso ρ σ) {Λ Λ' : IntegralModel O ρ} :
    Λ.map e ≤ Λ'.map e ↔ Λ ≤ Λ' := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ Submodule.map_mono h⟩
  obtain ⟨y, hy, hyx⟩ := (mem_lattice_map Λ' e (e x)).mp (h ((mem_lattice_map Λ e (e x)).mpr
    ⟨x, hx, rfl⟩))
  exact e.injective hyx ▸ hy

end IntegralModel

end Map

section Subquotient

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O]
  {E : Type*} [CommRing E] [Algebra O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [TopologicalSpace V]
  {ρ : ContinuousRep Γ E V}

namespace IntegralModel

/-- **Quotient integral model.** For a `Γ`-stable subspace `W ⊆ V`, the image of an integral
model `Λ` in `V ⧸ W` is an integral model of the quotient representation `ρ.quotient W hW`. -/
def quotient [ContinuousAdd V] (Λ : IntegralModel O ρ) (W : Submodule E V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) : IntegralModel O (ρ.quotient W hW) where
  lattice := Λ.lattice.map (W.mkQ.restrictScalars O)
  isLattice := inferInstance
  stable g q hq := by
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨ρ g x, Λ.stable g x hx, (ρ.quotient_apply_mk W hW g x).symm⟩

@[simp]
theorem lattice_quotient [ContinuousAdd V] (Λ : IntegralModel O ρ) (W : Submodule E V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) :
    (Λ.quotient W hW).lattice = Λ.lattice.map (W.mkQ.restrictScalars O) :=
  (rfl)

/-- If `W ⊆ V` is `Γ`-stable, then `W ∩ Λ` is a `Γ`-stable `O`-submodule of `Λ`. -/
theorem comap_subtype_stable (Λ : IntegralModel O ρ) (W : Submodule E V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ∀ g, (W.restrictScalars O).comap Λ.lattice.subtype ≤
      ((W.restrictScalars O).comap Λ.lattice.subtype).comap (Λ.toContinuousRep g) :=
  fun g _ hx ↦ hW g hx

/-- **Equivariant identification of `Λ ⧸ (W ∩ Λ)` with the quotient integral model.** -/
noncomputable def quotientEquiv [ContinuousAdd V] (Λ : IntegralModel O ρ) (W : Submodule E V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) :
    (Λ.toContinuousRep.toRepresentation.quotient ((W.restrictScalars O).comap Λ.lattice.subtype)
      (Λ.comap_subtype_stable W hW)).Equiv (Λ.quotient W hW).toContinuousRep.toRepresentation :=
  .mk (Submodule.quotientComapSubtypeEquivMapMkQ W Λ.lattice) fun g ↦ by
    ext x
    change (Submodule.quotientComapSubtypeEquivMapMkQ W Λ.lattice
        (Submodule.Quotient.mk (Λ.toContinuousRep g x)) : V ⧸ W) =
      ρ.quotient W hW g (Submodule.quotientComapSubtypeEquivMapMkQ W Λ.lattice
        (Submodule.Quotient.mk x) : V ⧸ W)
    simp

end IntegralModel

end Subquotient

section SubquotientField

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O]
  {E : Type*} [Field E] [Algebra O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [TopologicalSpace V]
  {ρ : ContinuousRep Γ E V}

namespace IntegralModel

/-- **Saturation of an integral model.** Over a Noetherian ring `O` with fraction field `E`, the
intersection `W ∩ Λ` of an integral model `Λ` with a `Γ`-stable subspace `W ⊆ V` is an integral
model of the subrepresentation `ρ.subrepresentation W hW`. -/
def subrepresentation [IsNoetherianRing O] [IsFractionRing O E] (Λ : IntegralModel O ρ)
    (W : Submodule E V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    IntegralModel O (ρ.subrepresentation W hW) where
  lattice := Λ.lattice.comap (W.subtype.restrictScalars O)
  isLattice := inferInstance
  stable g x hx := by simpa [Submodule.mem_comap] using Λ.stable g x hx

@[simp]
theorem lattice_subrepresentation [IsNoetherianRing O] [IsFractionRing O E]
    (Λ : IntegralModel O ρ) (W : Submodule E V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    (Λ.subrepresentation W hW).lattice = Λ.lattice.comap (W.subtype.restrictScalars O) :=
  (rfl)

/-- **Equivariant homeomorphism between `W ∩ Λ` inside `Λ` and the saturated integral model
`Λ.subrepresentation W hW`.** -/
def subrepresentationIso [IsNoetherianRing O] [IsFractionRing O E] (Λ : IntegralModel O ρ)
    (W : Submodule E V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ContinuousRep.Iso
      (Λ.toContinuousRep.subrepresentation ((W.restrictScalars O).comap Λ.lattice.subtype)
        (Λ.comap_subtype_stable W hW))
      (Λ.subrepresentation W hW).toContinuousRep where
  toRepresentationEquiv := .mk (Submodule.comapSubtypeEquivComapSubtype W Λ.lattice) fun g ↦ by
    ext x
    simp only [LinearMap.comp_apply, ContinuousRep.coe_toRepresentation, coe_toContinuousRep_apply,
      ContinuousRep.coe_subrepresentation_apply]
    change ((W.comapSubtypeEquivComapSubtype Λ.lattice _ : W) : V) =
      ρ g ((W.comapSubtypeEquivComapSubtype Λ.lattice x : W) : V)
    simp
  continuous_toFun := by
    rw [continuous_induced_rng, continuous_induced_rng]
    exact (continuous_subtype_val.comp continuous_subtype_val).congr fun x ↦
      (Submodule.coe_comapSubtypeEquivComapSubtype W Λ.lattice x).symm
  continuous_invFun := by
    rw [continuous_induced_rng, continuous_induced_rng]
    exact (continuous_subtype_val.comp continuous_subtype_val).congr fun y ↦
      (Submodule.coe_comapSubtypeEquivComapSubtype_symm W Λ.lattice y).symm

/-- **Splitting of `0 → W ∩ Λ → Λ → Λ ⧸ (W ∩ Λ) → 0` over a principal ideal domain.** Since
`Λ ⧸ (W ∩ Λ)` is finitely generated and torsion-free over `O`, the quotient map admits an
`O`-linear section. -/
theorem exists_rightInverse_mkQ_comap [IsDomain O] [IsPrincipalIdealRing O] [FaithfulSMul O E]
    (Λ : IntegralModel O ρ) (W : Submodule E V) :
    ∃ s : (Λ.lattice ⧸ (W.restrictScalars O).comap Λ.lattice.subtype) →ₗ[O] Λ.lattice,
      ((W.restrictScalars O).comap Λ.lattice.subtype).mkQ.comp s = LinearMap.id :=
  Submodule.exists_rightInverse_mkQ_comap_subtype (K := E) W Λ.lattice

/-- **Direct-sum decomposition of an integral model along a `Γ`-stable subspace over a principal
ideal domain.** As an `O`-module, `Λ` splits as `(W ∩ Λ) × (image of Λ in V ⧸ W)` compatibly
with the canonical inclusion and projection. -/
theorem exists_linearEquiv_prod_subrepresentation_quotient [IsDomain O] [IsPrincipalIdealRing O]
    [IsFractionRing O E] [ContinuousAdd V] (Λ : IntegralModel O ρ) (W : Submodule E V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ∃ e : Λ.lattice ≃ₗ[O]
        ((Λ.subrepresentation W hW).lattice × (Λ.quotient W hW).lattice),
      (∀ x : Λ.lattice, ((e x).2 : V ⧸ W) = W.mkQ x) ∧
      (∀ y : (Λ.subrepresentation W hW).lattice, (e.symm (y, 0) : V) = y.1) :=
  Submodule.exists_linearEquiv_prod_comap_subtype_map_mkQ (K := E) W Λ.lattice

end IntegralModel

end SubquotientField

section Dual

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  {O : Type*} [CommRing O]
  {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E]
  [TopologicalSpace E] [IsTopologicalSemiring E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [TopologicalSpace V] [IsModuleTopology E V] [FiniteDimensional E V]
  [TopologicalSpace (Module.Dual E V)] [IsModuleTopology E (Module.Dual E V)]
  {ρ : ContinuousRep Γ E V}

namespace IntegralModel

/-- **Dual integral model.** The integral dual `Λ^∨ = {φ ∈ V^∨ | φ(Λ) ⊆ O}` of a free integral
model `Λ` of `ρ` is an integral model of the contragredient continuous representation `ρ.dual`. -/
def dual (Λ : IntegralModel O ρ) [Module.Free O Λ.lattice] : IntegralModel O ρ.dual where
  lattice := Λ.lattice.dualLattice E
  isLattice :=
    have := IsDomain.of_faithfulSMul O E
    inferInstance
  stable g φ hφ := by
    rw [Submodule.mem_dualLattice]
    intro x hx
    rw [ContinuousRep.dual_apply]
    exact (Submodule.mem_dualLattice Λ.lattice φ).mp hφ _ (Λ.stable g⁻¹ x hx)

@[simp]
theorem lattice_dual (Λ : IntegralModel O ρ) [Module.Free O Λ.lattice] :
    Λ.dual.lattice = Λ.lattice.dualLattice E :=
  (rfl)

/-- The underlying lattice of the dual of a free integral model is free. -/
instance free_lattice_dual (Λ : IntegralModel O ρ) [Module.Free O Λ.lattice] :
    Module.Free O Λ.dual.lattice :=
  inferInstanceAs (Module.Free O (Λ.lattice.dualLattice E))

/-- Taking the dual integral model reverses inclusion. -/
theorem dual_anti {Λ Λ' : IntegralModel O ρ} [Module.Free O Λ.lattice] [Module.Free O Λ'.lattice]
    (h : Λ ≤ Λ') : Λ'.dual ≤ Λ.dual :=
  Submodule.dualLattice_antitone E h

/-- Taking the dual integral model strictly reverses inclusion. -/
@[simp]
theorem dual_le_dual_iff {Λ Λ' : IntegralModel O ρ}
    [Module.Free O Λ.lattice] [Module.Free O Λ'.lattice] :
    Λ'.dual ≤ Λ.dual ↔ Λ ≤ Λ' :=
  Submodule.dualLattice_le_dualLattice_iff Λ.lattice Λ'.lattice

/-- A free integral model is uniquely determined by its dual. -/
@[simp]
theorem dual_eq_dual_iff {Λ Λ' : IntegralModel O ρ}
    [Module.Free O Λ.lattice] [Module.Free O Λ'.lattice] :
    Λ.dual = Λ'.dual ↔ Λ = Λ' := by
  simp [IntegralModel.ext_iff, Submodule.dualLattice_eq_dualLattice_iff]

/-- **Homothety scaling of the dual integral model**: `(c • Λ)^∨ = c⁻¹ • Λ^∨`. -/
@[simp]
theorem dual_smul (c : Eˣ) (Λ : IntegralModel O ρ) [Module.Free O Λ.lattice] :
    (c • Λ).dual = c⁻¹ • Λ.dual :=
  IntegralModel.ext (Submodule.dualLattice_smul c Λ.lattice)

/-- **Biduality for integral models.** The canonical biduality isomorphism `ρ.evalIso : ρ ≅ ρ^∨∨`
carries a free integral model `Λ` onto its double dual `(Λ^∨)^∨`. -/
theorem map_evalIso_eq_dual_dual
    [TopologicalSpace (Module.Dual E (Module.Dual E V))]
    [IsModuleTopology E (Module.Dual E (Module.Dual E V))]
    (Λ : IntegralModel O ρ) [Module.Free O Λ.lattice] :
    Λ.map ρ.evalIso = Λ.dual.dual := by
  apply IntegralModel.ext
  have hmap : (Λ.map ρ.evalIso).lattice =
      Λ.lattice.map ((Module.evalEquiv E V).toLinearMap.restrictScalars O) := by
    ext ψ
    simp [lattice_map]
  rw [hmap, lattice_dual, lattice_dual]
  exact Submodule.map_evalEquiv_eq_dualLattice_dualLattice Λ.lattice

section DualPID

variable [IsDomain O] [IsPrincipalIdealRing O]

/-- Over a principal ideal domain, duality sends sums of integral models to intersections. -/
@[simp]
theorem dual_sup (Λ Λ' : IntegralModel O ρ) : (Λ ⊔ Λ').dual = Λ.dual ⊓ Λ'.dual :=
  IntegralModel.ext (Submodule.dualLattice_sup Λ.lattice Λ'.lattice)

/-- Over a principal ideal domain, duality sends intersections of integral models to sums. -/
@[simp]
theorem dual_inf (Λ Λ' : IntegralModel O ρ) : (Λ ⊓ Λ').dual = Λ.dual ⊔ Λ'.dual :=
  IntegralModel.ext (Submodule.dualLattice_inf Λ.lattice Λ'.lattice)

end DualPID

end IntegralModel

end Dual

section OfCharacter

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O]
  {E : Type*} [CommRing E] [Algebra O E] [TopologicalSpace E] [ContinuousMul E]

namespace IntegralModel

/-- **Standard integral model of an integral character line.** When a continuous character
`χ : Γ →ₜ* Eˣ` takes values in the image of `O`, the unit lattice `1 : Submodule O E` is an
integral model of `ContinuousRep.ofCharacter χ`. -/
def ofCharacter (χ : Γ →ₜ* Eˣ) (hχ : ∀ g, (χ g : E) ∈ (1 : Submodule O E)) :
    IntegralModel O (ContinuousRep.ofCharacter χ) where
  lattice := 1
  isLattice := by
    rw [Submodule.one_eq_span]
    exact isLattice_span (Set.finite_singleton 1) (by simp)
  stable g x hx := by
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hχ g)
    obtain ⟨s, rfl⟩ := Submodule.mem_one.mp hx
    rw [ContinuousRep.ofCharacter_apply, ← hr, ← map_mul]
    exact Submodule.mem_one.mpr ⟨r * s, rfl⟩

@[simp]
theorem lattice_ofCharacter (χ : Γ →ₜ* Eˣ) (hχ : ∀ g, (χ g : E) ∈ (1 : Submodule O E)) :
    (ofCharacter χ hχ).lattice = 1 :=
  (rfl)

/-- Over a faithful algebra, the underlying lattice of `ofCharacter χ hχ` is free over `O`. -/
instance free_lattice_ofCharacter [FaithfulSMul O E] (χ : Γ →ₜ* Eˣ)
    (hχ : ∀ g, (χ g : E) ∈ (1 : Submodule O E)) :
    Module.Free O (ofCharacter χ hχ).lattice :=
  inferInstanceAs (Module.Free O (1 : Submodule O E))

end IntegralModel

end OfCharacter

section OfCharacterField

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O]
  {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E] [TopologicalSpace E] [ContinuousMul E]

namespace IntegralModel

/-- A continuous character admitting a free integral model takes integral values. -/
theorem ofCharacter_mem_one {χ : Γ →ₜ* Eˣ} (Λ : IntegralModel O (ContinuousRep.ofCharacter χ))
    [Module.Free O Λ.lattice] (g : Γ) : (χ g : E) ∈ (1 : Submodule O E) := by
  obtain ⟨c, hc⟩ := IsLattice.exists_eq_smul_one Λ.lattice
  have hc_mem : (c : E) ∈ Λ.lattice := by
    rw [hc]
    exact (mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨1, Submodule.mem_one.mpr ⟨1, map_one _⟩, by simp [Units.smul_def]⟩
  have hstab : (χ g : E) * (c : E) ∈ c • (1 : Submodule O E) := by
    simpa [hc, ContinuousRep.ofCharacter_apply] using Λ.stable g (c : E) hc_mem
  obtain ⟨x, hx, hcx⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hstab
  have hEq : x = (χ g : E) := by
    have : (c : E) * x = (c : E) * (χ g : E) := by
      simpa [Units.smul_def, mul_comm] using hcx
    exact mul_left_cancel₀ c.ne_zero this
  exact hEq ▸ hx

/-- **Existence criterion for integral models of a character line.** Over a principal ideal domain
`O` with fraction field `E`, the rank-one representation `ContinuousRep.ofCharacter χ` admits an
integral model if and only if every value `χ g` lies in `O`. -/
theorem nonempty_ofCharacter_iff [IsDomain O] [IsPrincipalIdealRing O] (χ : Γ →ₜ* Eˣ) :
    Nonempty (IntegralModel O (ContinuousRep.ofCharacter χ)) ↔
      ∀ g, (χ g : E) ∈ (1 : Submodule O E) :=
  ⟨fun ⟨Λ⟩ ↦ Λ.ofCharacter_mem_one, fun hχ ↦ ⟨ofCharacter χ hχ⟩⟩

/-- Every free integral model of an integral character line is a homothety translate of the
standard model `ofCharacter χ hχ`. -/
theorem exists_eq_smul_ofCharacter {χ : Γ →ₜ* Eˣ} (hχ : ∀ g, (χ g : E) ∈ (1 : Submodule O E))
    (Λ : IntegralModel O (ContinuousRep.ofCharacter χ)) [Module.Free O Λ.lattice] :
    ∃ c : Eˣ, Λ = c • ofCharacter χ hχ := by
  obtain ⟨c, hc⟩ := IsLattice.exists_eq_smul_one Λ.lattice
  exact ⟨c, IntegralModel.ext hc⟩

/-- **Classification of integral models of a character line over a discrete valuation ring.**
With uniformizer `ϖ`, every integral model of `ContinuousRep.ofCharacter χ` (in particular, of
the trivial representation `χ = 1`) has the form `ϖᵏ • 1` for a unique `k : ℤ`. -/
theorem existsUnique_zpow_smul_ofCharacter [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {χ : Γ →ₜ* Eˣ} (hχ : ∀ g, (χ g : E) ∈ (1 : Submodule O E))
    (Λ : IntegralModel O (ContinuousRep.ofCharacter χ)) :
    ∃! k : ℤ, Λ = (Units.mk0 (algebraMap O E ϖ)
      ((map_ne_zero_iff _ (IsFractionRing.injective O E)).mpr hϖ.ne_zero)) ^ k •
        ofCharacter χ hχ := by
  obtain ⟨k, hk, huniq⟩ := IsLattice.existsUnique_zpow_smul_one (K := E) hϖ Λ.lattice
  exact ⟨k, IntegralModel.ext hk, fun m hm ↦ huniq m (congrArg IntegralModel.lattice hm)⟩

end IntegralModel

end OfCharacterField

section InvOfCharacter

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O]
  {E : Type*} [CommRing E] [Algebra O E] [TopologicalSpace E] [ContinuousMul E]

namespace IntegralModel

/-- If a continuous character of a group takes integral values, so does its inverse character. -/
theorem inv_ofCharacter_mem_one {χ : Γ →ₜ* Eˣ} (hχ : ∀ g, (χ g : E) ∈ (1 : Submodule O E))
    (g : Γ) : ((χ⁻¹ : Γ →ₜ* Eˣ) g : E) ∈ (1 : Submodule O E) := by
  have hinv : ((χ⁻¹ : Γ →ₜ* Eˣ) g : E) = (χ g⁻¹ : E) := by
    change (((χ g)⁻¹ : Eˣ) : E) = (χ g⁻¹ : E)
    rw [← map_inv]
  rw [hinv]
  exact hχ g⁻¹

end IntegralModel

end InvOfCharacter

section DualOfCharacter

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  {O : Type*} [CommRing O]
  {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E]
  [TopologicalSpace E] [IsTopologicalSemiring E]
  [TopologicalSpace (Module.Dual E E)] [IsModuleTopology E (Module.Dual E E)]

namespace IntegralModel

/-- **Duality on the standard integral model of a character line.** Under
`ContinuousRep.dualOfCharacterIso χ : (ofCharacter χ).dual ≅ ofCharacter χ⁻¹`, the dual of the
standard model `1` is the standard model `1` of `χ⁻¹`. -/
theorem map_dualOfCharacterIso_dual (χ : Γ →ₜ* Eˣ) (hχ : ∀ g, (χ g : E) ∈ (1 : Submodule O E)) :
    (ofCharacter χ hχ).dual.map (ContinuousRep.dualOfCharacterIso χ) =
      ofCharacter χ⁻¹ (inv_ofCharacter_mem_one hχ) := by
  apply IntegralModel.ext
  have hmap : ((ofCharacter χ hχ).dual.map (ContinuousRep.dualOfCharacterIso χ)).lattice =
      ((1 : Submodule O E).dualLattice E).map ((Module.Dual.eval E E 1).restrictScalars O) := by
    ext x
    simp only [mem_lattice_map, lattice_dual, lattice_ofCharacter,
      ContinuousRep.dualOfCharacterIso_apply, Submodule.mem_map, LinearMap.restrictScalars_apply,
      Module.Dual.eval_apply]
  rw [hmap, lattice_ofCharacter]
  exact Submodule.map_eval_one_dualLattice_one (R := O) (K := E)

/-- **Duality on homothetic integral models of a character line.** Under
`ContinuousRep.dualOfCharacterIso χ`, the dual of `c • 1` is `c⁻¹ • 1` for `χ⁻¹`. -/
theorem map_dualOfCharacterIso_dual_smul (c : Eˣ) (χ : Γ →ₜ* Eˣ)
    (hχ : ∀ g, (χ g : E) ∈ (1 : Submodule O E)) :
    (c • ofCharacter χ hχ).dual.map (ContinuousRep.dualOfCharacterIso χ) =
      c⁻¹ • ofCharacter χ⁻¹ (inv_ofCharacter_mem_one hχ) := by
  rw [dual_smul, map_smul, map_dualOfCharacterIso_dual]

end IntegralModel

end DualOfCharacter

end TauCeti.GaloisLattice

section ToLinearEquivHom

namespace TauCeti.ContinuousRep

variable {Γ A M : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  [CommRing A] [TopologicalSpace A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [Module.Free A M]

/-- **Continuous homomorphism into linear automorphisms.** A jointly continuous representation of
a group with continuous inversion on a finite free module with its module topology induces a
continuous group homomorphism `Γ →ₜ* (M ≃ₗ[A] M)`. -/
def toLinearEquivHom (ρ : ContinuousRep Γ A M) : Γ →ₜ* (M ≃ₗ[A] M) :=
  let φ : Γ →* (M ≃ₗ[A] M) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv A M).toMonoidHom.comp
      ρ.toRepresentation.asGroupHom
  { toMonoidHom := φ
    continuous_toFun := by
      rw [TauCeti.continuous_linearEquiv_iff]
      have hcont : Continuous fun g : Γ ↦ (ρ g : Module.End A M) := by
        rcases subsingleton_or_nontrivial A with hA | hA
        · have : Subsingleton (Module.End A M) := Module.subsingleton A _
          exact continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
        · let b := Module.Free.chooseBasis A M
          have : Finite (Module.Free.ChooseBasisIndex A M) := Module.Finite.finite_basis b
          exact (b.continuous_iff_apply _).mpr fun i ↦ ρ.continuous_orbit (b i)
      refine ⟨hcont, (hcont.comp continuous_inv).congr fun g ↦ ?_⟩
      ext x
      change ρ g⁻¹ x = ((φ g)⁻¹ : M ≃ₗ[A] M) x
      rw [← map_inv φ g]
      rfl }

@[simp]
theorem coe_toLinearEquivHom (ρ : ContinuousRep Γ A M) (g : Γ) :
    (ρ.toLinearEquivHom g : Module.End A M) = ρ g :=
  (rfl)

@[simp]
theorem toLinearEquivHom_apply (ρ : ContinuousRep Γ A M) (g : Γ) (x : M) :
    ρ.toLinearEquivHom g x = ρ g x :=
  (rfl)

@[simp]
theorem toLinearEquivHom_inv_apply (ρ : ContinuousRep Γ A M) (g : Γ) (x : M) :
    (ρ.toLinearEquivHom g)⁻¹ x = ρ g⁻¹ x := by
  rw [← map_inv]
  rfl

end TauCeti.ContinuousRep

end ToLinearEquivHom

section MatrixForm

open scoped MatrixGroups

namespace TauCeti.GaloisLattice.IntegralModel

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  {O : Type*} [CommRing O] [TopologicalSpace O]
  {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E]
  [TopologicalSpace E] [IsTopologicalSemiring E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [TopologicalSpace V] [IsModuleTopology E V] [FiniteDimensional E V]
  {ρ : ContinuousRep Γ E V}

omit [TopologicalSpace O] [IsFractionRing O E] [IsTopologicalSemiring E] in
/-- Every element of `Γ` lies in the stabilizer of an integral model `Λ`. -/
theorem toLinearEquivHom_mem_stabilizer (Λ : IntegralModel O ρ) (g : Γ) :
    ρ.toLinearEquivHom g ∈ MulAction.stabilizer (V ≃ₗ[E] V) (Λ.lattice : Set V) :=
  TauCeti.mem_stabilizer_set_iff_mapsTo.mpr
    ⟨fun x hx ↦ Λ.stable g x hx, fun x hx ↦ by
      simpa using Λ.stable g⁻¹ x hx⟩

/-- **Continuous matrix representation attached to a basis of an integral model.** Given an
`O`-basis `b` of an integral model `Λ` and a topologically inducing embedding `O → E`, the action
of `Γ` is represented by a continuous group homomorphism `Γ →ₜ* GL ι O`. -/
noncomputable def toGeneralLinearGroupHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : IntegralModel O ρ) (b : Module.Basis ι O Λ.lattice)
    (hO : Topology.IsInducing (algebraMap O E)) : Γ →ₜ* GL ι O where
  toFun g := b.stabilizerContinuousMulEquiv E hO
    ⟨ρ.toLinearEquivHom g, Λ.toLinearEquivHom_mem_stabilizer g⟩
  map_one' := by
    have h1 : (⟨ρ.toLinearEquivHom 1, Λ.toLinearEquivHom_mem_stabilizer 1⟩ :
        MulAction.stabilizer (V ≃ₗ[E] V) (Λ.lattice : Set V)) = 1 :=
      Subtype.ext (map_one ρ.toLinearEquivHom)
    rw [h1, map_one]
  map_mul' g h := by
    have hm : (⟨ρ.toLinearEquivHom (g * h), Λ.toLinearEquivHom_mem_stabilizer (g * h)⟩ :
        MulAction.stabilizer (V ≃ₗ[E] V) (Λ.lattice : Set V)) =
        ⟨ρ.toLinearEquivHom g, Λ.toLinearEquivHom_mem_stabilizer g⟩ *
          ⟨ρ.toLinearEquivHom h, Λ.toLinearEquivHom_mem_stabilizer h⟩ :=
      Subtype.ext (map_mul ρ.toLinearEquivHom g h)
    rw [hm, map_mul]
  continuous_toFun :=
    (b.stabilizerContinuousMulEquiv E hO).continuous.comp
      (ρ.toLinearEquivHom.continuous.subtype_mk _)

/-- Passing from `GL ι O` to `GL ι E` recovers `Module.Basis.toGL` in the extended `E`-basis. -/
@[simp]
theorem map_toGeneralLinearGroupHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : IntegralModel O ρ) (b : Module.Basis ι O Λ.lattice)
    (hO : Topology.IsInducing (algebraMap O E)) (g : Γ) :
    Matrix.GeneralLinearGroup.map (algebraMap O E) (Λ.toGeneralLinearGroupHom b hO g) =
      (b.extendOfIsLattice E).toGL (ρ.toLinearEquivHom g) := by
  change Matrix.GeneralLinearGroup.map (algebraMap O E)
      (b.stabilizerContinuousMulEquiv E hO
        ⟨ρ.toLinearEquivHom g, Λ.toLinearEquivHom_mem_stabilizer g⟩) = _
  simp

/-- In the extended `E`-basis of a lattice basis `b`, the matrix of `ρ g` is the image of the
integral matrix `Λ.toGeneralLinearGroupHom b hO g`. -/
theorem toMatrix_extendOfIsLattice_eq_map_toGeneralLinearGroupHom {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Λ : IntegralModel O ρ) (b : Module.Basis ι O Λ.lattice)
    (hO : Topology.IsInducing (algebraMap O E)) (g : Γ) :
    LinearMap.toMatrix (b.extendOfIsLattice E) (b.extendOfIsLattice E) (ρ g) =
      (Λ.toGeneralLinearGroupHom b hO g : Matrix ι ι O).map (algebraMap O E) := by
  have h := congrArg Units.val (Λ.map_toGeneralLinearGroupHom b hO g)
  simpa only [Matrix.GeneralLinearGroup.map, MonoidHom.coe_ofClass, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Module.Basis.coe_toGL,
    ContinuousRep.coe_toLinearEquivHom] using h.symm

/-- On a subsingleton space, the matrix representation attached to any lattice basis is trivial. -/
theorem toGeneralLinearGroupHom_eq_one_of_subsingleton [Subsingleton V] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Λ : IntegralModel O ρ) (b : Module.Basis ι O Λ.lattice)
    (hO : Topology.IsInducing (algebraMap O E)) :
    Λ.toGeneralLinearGroupHom b hO = 1 := by
  ext g i j
  have h01 : (0 : O) = 1 := by
    have h := congrArg (fun f : ι →₀ O ↦ f i) (b.repr_self i)
    rw [Subsingleton.elim (b i) 0, map_zero] at h
    simpa using h
  have : Subsingleton O := subsingleton_of_zero_eq_one h01
  exact Subsingleton.elim _ _

end TauCeti.GaloisLattice.IntegralModel

namespace TauCeti.ContinuousRep

open ValuativeRel

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [ContinuousInv Γ]
  {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
  [IsPrincipalIdealRing 𝒪[E]]
  {V : Type*} [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V]
  [TopologicalSpace V] [IsModuleTopology E V] [FiniteDimensional E V]

/-- **Matrix form of the stable-lattice theorem.** A jointly continuous representation `ρ` of a
compact group `Γ` with continuous inversion on a finite-dimensional vector space `V` over a field
`E` with a valuative topology whose valuation ring `𝒪[E]` is a principal ideal domain (for
instance any nonarchimedean local field) is represented, in an `E`-basis of `V` of size
`n = finrank E V`, by a continuous group homomorphism `φ : Γ →ₜ* GL (Fin n) 𝒪[E]`. -/
theorem exists_basis_continuousMonoidHom_generalLinearGroup (ρ : ContinuousRep Γ E V) :
    ∃ (b : Module.Basis (Fin (Module.finrank E V)) E V)
      (φ : Γ →ₜ* GL (Fin (Module.finrank E V)) 𝒪[E]),
      ∀ g : Γ,
        Matrix.GeneralLinearGroup.map (algebraMap 𝒪[E] E) (φ g) =
          b.toGL (ρ.toLinearEquivHom g) := by
  let Λ : GaloisLattice.IntegralModel 𝒪[E] ρ := Classical.arbitrary _
  let b₀ : Module.Basis (Fin (Module.finrank E V)) 𝒪[E] Λ.lattice :=
    (Module.finBasis 𝒪[E] Λ.lattice).reindex
      (finCongr (Submodule.finrank_eq_finrank (K := E) Λ.lattice
        (IsLattice.span_eq_top (A := E) (M := Λ.lattice))))
  exact ⟨b₀.extendOfIsLattice E,
    Λ.toGeneralLinearGroupHom b₀ Topology.IsInducing.subtypeVal,
    fun g ↦ Λ.map_toGeneralLinearGroupHom b₀ Topology.IsInducing.subtypeVal g⟩

end TauCeti.ContinuousRep

end MatrixForm

