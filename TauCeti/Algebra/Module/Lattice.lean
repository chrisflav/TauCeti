/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.Lattice
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Submodule
import TauCeti.Algebra.Module.LocalizedModule.Submodule

/-!
# Full submodule lattices

This file provides generic results about full submodules over fraction fields. It relates bases and
ranks of full submodules to their ambient spaces. It also extends integral linear equivalences
between full submodules to rational linear equivalences of their ambient spaces, and proves that
surjective linear maps preserve full lattices over commutative-ring algebras, as do finite
products. Finally, a free full lattice over an integral domain rationalizes to its ambient vector
space over the fraction field.

## Main declarations

* `Module.Basis.span_range_extendOfIsLattice` and `Module.Basis.extendOfIsLattice_repr_coe`: the
  span of an extended lattice basis is the lattice, and the coordinates of a lattice vector in the
  extended basis are the images of its integral coordinates.
* `Module.Basis.toAddSubgroup_eq_closure_range_extendOfIsLattice`: the additive
  closure of an extended lattice basis is the lattice's underlying additive subgroup.
* `TauCeti.Submodule.IsLattice.relIndex_ne_zero`: a full `ℤ`-lattice has finite index in every
  full `ℤ`-lattice.
* `TauCeti.Submodule.IsLattice.relIndex_span_eq_abs_det_mul`: the indices of a full `ℤ`-lattice
  in the `ℤ`-spans of two `ℚ`-bases differ by the determinant of the change of basis.
* `Submodule.toAddSubgroup_submoduleOf`: taking the underlying additive subgroup commutes
  with restricting a submodule to another submodule.
* `Submodule.isLattice_span`: the span of a finite set spanning the ambient module is a full
  lattice.
* `Module.Finite.of_isLattice`: a module containing a full lattice is finite.
* `Submodule.finrank_eq_finrank`: a full lattice and its ambient space have the
  same finrank.
* `Submodule.IsLattice.pi`: the product of a finite family of full lattices is a full lattice.
* `Submodule.IsLattice.prod`: the product of two full lattices is a full lattice.
* `LinearEquiv.extendOfIsLattice`: extension of an `R`-linear equivalence between
  full submodules to their ambient `K`-vector spaces.
* `Submodule.isBaseChange_subtype`: the inclusion of a free full lattice
  submodule into its ambient vector space over the fraction field is a base change.
* `LinearMap.det_eq_algebraMap_det_of_isLattice`: an endomorphism of the ambient space which
  restricts to an endomorphism of a free full lattice has the determinant of that restriction.
* `Submodule.rationalizationEquiv`: the canonical equivalence from the scalar extension
  of a free full lattice submodule to its ambient vector space.
* `Submodule.IsLattice.isLocalizedModule_subtype`: the inclusion of a submodule spanning the
  ambient space over the fraction field, such as a full lattice, is a localization at the nonzero
  divisors.
* `Submodule.IsLattice.exists_ne_zero_smul_mem`: some nonzero multiple of every ambient vector
  lies in such a submodule.
* `Submodule.exists_ne_zero_smul_mem_baseChange`: the same holds for every element of a scalar
  extension and the base change of such a submodule.
* `Submodule.IsLattice.exists_ne_zero_forall_smul_mem`: a single nonzero scalar multiplies a
  finitely generated submodule into a submodule spanning the ambient space over `K`.
* `Submodule.IsLattice.exists_maximalIdeal_pow_smul_le`: over a discrete valuation ring, a power
  of the maximal ideal multiplies a finitely generated submodule into a full lattice.
* `TensorProduct.rationalizationEquiv_baseChange_unitTmulEquiv`: rationalizing that
  unit-tensor lattice returns the scalar extension one started from.
* `Submodule.isLattice_bot_of_subsingleton`: in a subsingleton module the zero submodule is a full
  lattice.
* `Submodule.free_smul` and `Submodule.free_one`: scaling a free submodule by a group element
  preserves freeness, and the unit submodule `1` of a faithful algebra is free.
* `Submodule.zpow_smul_one_le_iff`, `Submodule.IsLattice.exists_eq_smul_one`, and
  `Submodule.IsLattice.existsUnique_zpow_smul_one`: every free full lattice in a fraction field is
  a unit multiple of `1`, and over a discrete valuation ring a unique power of a uniformizer times
  `1`.
* `Submodule.IsLattice.comap_subtype` and `Submodule.IsLattice.map_mkQ`: intersecting a full
  lattice with a subspace (saturation) over a Noetherian ring, and projecting it to the quotient,
  both produce full lattices.
* `Submodule.comapSubtypeEquivComapSubtype` and `Submodule.quotientComapSubtypeEquivMapMkQ`:
  canonical identifications of the saturated sublattice and quotient lattice.
* `Submodule.isTorsionFree_quotient_comap_subtype`,
  `Submodule.exists_rightInverse_mkQ_comap_subtype`, and
  `Submodule.exists_linearEquiv_prod_comap_subtype_map_mkQ`: the quotient of a lattice by a
  saturated sublattice is torsion-free, so over a principal ideal domain the short exact sequence
  splits.

## References

* See N. Bourbaki, *Commutative Algebra*, Chapter VII, §4 for lattice theory over Dedekind domains.
-/

public section

open Module TensorProduct

namespace TauCeti

universe u v w

section

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- The `R`-span of the ambient `K`-basis obtained from an `R`-basis of a lattice is the lattice
itself. -/
theorem _root_.Module.Basis.span_range_extendOfIsLattice {κ : Type*} {N : Submodule R V}
    [N.IsLattice K] (b : Basis κ R N) :
    Submodule.span R (Set.range (b.extendOfIsLattice K)) = N := by
  have hrange : Set.range (b.extendOfIsLattice K) = Set.range (N.subtype ∘ b) :=
    congrArg Set.range (funext fun i ↦ Basis.extendOfIsLattice_apply K b i)
  rw [hrange, Set.range_comp, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- Coordinates of a lattice vector in the extended `K`-basis are the images of its coordinates in
the `R`-basis of the lattice. -/
@[simp]
theorem _root_.Module.Basis.extendOfIsLattice_repr_coe {κ : Type*} {N : Submodule R V}
    [N.IsLattice K] (b : Basis κ R N) (x : N) (i : κ) :
    (b.extendOfIsLattice K).repr (x : V) i = algebraMap R K (b.repr x i) := by
  have h : ((b.extendOfIsLattice K).repr.toLinearMap.restrictScalars R).comp N.subtype =
      (Finsupp.mapRange.linearMap (Algebra.linearMap R K)).comp b.repr.toLinearMap := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply,
      LinearEquiv.coe_toLinearMap, Basis.repr_self, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]
    rw [← Basis.extendOfIsLattice_apply K b j, Basis.repr_self]
  simpa using congr($h x i)

/-- The additive subgroup generated by an extended basis of a full `ℤ`-submodule is the submodule's
underlying additive subgroup. -/
theorem _root_.Module.Basis.toAddSubgroup_eq_closure_range_extendOfIsLattice
    {W : Type*} [AddCommGroup W] [Module ℚ W] {N : Submodule ℤ W} [N.IsLattice ℚ]
    {κ : Type*} (b : Basis κ ℤ N) :
    N.toAddSubgroup = AddSubgroup.closure (Set.range (b.extendOfIsLattice ℚ)) := by
  apply AddSubgroup.toIntSubmodule.injective
  rw [AddSubgroup.toIntSubmodule_closure, Module.Basis.span_range_extendOfIsLattice,
    Submodule.toIntSubmodule_toAddSubgroup, Submodule.restrictScalars_self]

end

section

variable {R A V : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

/-- A module containing a full lattice is finite: the generators of the lattice span it. -/
theorem _root_.Module.Finite.of_isLattice (M : Submodule R V) [M.IsLattice A] :
    Module.Finite A V := by
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg (A := A) (M := M)
  exact ⟨⟨s, by rw [← Submodule.span_span_of_tower R, hs, Submodule.IsLattice.span_eq_top]⟩⟩

end

section

/-- Taking the underlying additive subgroup commutes with restricting a submodule to another
submodule. -/
theorem _root_.Submodule.toAddSubgroup_submoduleOf {R V : Type*} [Ring R] [AddCommGroup V]
    [Module R V] (p q : Submodule R V) :
    (p.submoduleOf q).toAddSubgroup = p.toAddSubgroup.addSubgroupOf q.toAddSubgroup := rfl

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A full `ℤ`-submodule has finite index in every full `ℤ`-submodule: its index is that of its
intersection with it. -/
theorem Submodule.IsLattice.relIndex_ne_zero {N M : Submodule ℤ V} [N.IsLattice ℚ]
    [M.IsLattice ℚ] : N.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  classical
  -- needed for the `IsLattice.inf` instance on `N ⊓ M`
  have := Module.Finite.of_isLattice (R := ℤ) (A := ℚ) N
  have key {P : Submodule ℤ V} [P.IsLattice ℚ] (hle : P ≤ M) :
      P.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
    let bM := Module.Free.chooseBasis ℤ M
    let eM := bM.extendOfIsLattice ℚ
    let bP := (Module.Free.chooseBasis ℤ P).reindex
      (((Module.Free.chooseBasis ℤ P).extendOfIsLattice ℚ).indexEquiv eM)
    have hidx := AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr hle)
      (bP.extendOfIsLattice ℚ) eM bP.toAddSubgroup_eq_closure_range_extendOfIsLattice
      bM.toAddSubgroup_eq_closure_range_extendOfIsLattice
    intro h
    rw [h, Nat.cast_zero, eq_comm, abs_eq_zero] at hidx
    exact (eM.isUnit_det _).ne_zero hidx
  rw [← AddSubgroup.inf_relIndex_right]
  exact key (P := N ⊓ M) inf_le_right

/-- **Indices of a common full sublattice differ by a determinant.** If a full `ℤ`-submodule `N`
lies in the `ℤ`-spans of two `ℚ`-bases `b` and `c`, then its index in the span of `b` is
`|b.det c|` times its index in the span of `c`. -/
theorem Submodule.IsLattice.relIndex_span_eq_abs_det_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : Submodule ℤ V} [N.IsLattice ℚ] (b c : Basis ι ℚ V)
    (hb : N ≤ Submodule.span ℤ (Set.range b)) (hc : N ≤ Submodule.span ℤ (Set.range c)) :
    (N.toAddSubgroup.relIndex (Submodule.span ℤ (Set.range b)).toAddSubgroup : ℚ) =
      |b.det c| * N.toAddSubgroup.relIndex (Submodule.span ℤ (Set.range c)).toAddSubgroup := by
  let bN := (Module.Free.chooseBasis ℤ N).reindex
    (((Module.Free.chooseBasis ℤ N).extendOfIsLattice ℚ).indexEquiv b)
  have hN := bN.toAddSubgroup_eq_closure_range_extendOfIsLattice
  rw [AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr hb) _ b hN
      (Submodule.span_int_eq_addSubgroupClosure _),
    AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr hc) _ c hN
      (Submodule.span_int_eq_addSubgroupClosure _), ← abs_mul, Basis.det_mul_det]

end

section

variable {R : Type*} {K : Type*} {V : Type u} {W : Type v}
variable [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]

/-- Extend an `R`-linear equivalence between full submodules uniquely to their ambient
`K`-vector spaces. -/
noncomputable def _root_.LinearEquiv.extendOfIsLattice {S : Submodule R V} {T : Submodule R W}
    [S.IsLattice K] [T.IsLattice K] [Module.Free R S] (e : S ≃ₗ[R] T) : V ≃ₗ[K] W :=
  let b := Module.Free.chooseBasis R S
  (b.extendOfIsLattice K).equiv ((b.map e).extendOfIsLattice K) (Equiv.refl _)

/-- The ambient extension of a full-submodule equivalence agrees with it on the submodule. -/
@[simp]
theorem _root_.LinearEquiv.extendOfIsLattice_apply {S : Submodule R V} {T : Submodule R W}
    [S.IsLattice K] [T.IsLattice K] [Module.Free R S] (e : S ≃ₗ[R] T) (x : S) :
    LinearEquiv.extendOfIsLattice e (x : V) = (e x : W) := by
  let b := Module.Free.chooseBasis R S
  have h : (LinearEquiv.extendOfIsLattice e).toLinearMap.restrictScalars R ∘ₗ S.subtype =
      T.subtype ∘ₗ e.toLinearMap := by
    apply b.ext
    intro i
    dsimp only [b]
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply,
      LinearEquiv.coe_toLinearMap]
    rw [← Basis.extendOfIsLattice_apply K (Module.Free.chooseBasis R S) i]
    -- Expose the constructed basis equivalence so `Basis.equiv_apply` can identify its values.
    unfold LinearEquiv.extendOfIsLattice
    rw [Basis.equiv_apply, Basis.extendOfIsLattice_apply, Basis.map_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun h x

/-- A `K`-linear equivalence extending a given equivalence of full submodules is the
canonical extension. -/
theorem _root_.LinearEquiv.eq_extendOfIsLattice {S : Submodule R V} {T : Submodule R W}
    [S.IsLattice K] [T.IsLattice K] [Module.Free R S] (e : S ≃ₗ[R] T) (f : V ≃ₗ[K] W)
    (h : ∀ x : S, f (x : V) = (e x : W)) : f = LinearEquiv.extendOfIsLattice e := by
  apply LinearEquiv.toLinearMap_injective
  apply (Module.Free.chooseBasis R S).extendOfIsLattice K |>.ext
  intro i
  rw [Basis.extendOfIsLattice_apply]
  exact (h (Module.Free.chooseBasis R S i)).trans
    (LinearEquiv.extendOfIsLattice_apply e (Module.Free.chooseBasis R S i)).symm

/-- The ambient extension maps the source full submodule onto the target full submodule. -/
theorem _root_.LinearEquiv.extendOfIsLattice_map {S : Submodule R V} {T : Submodule R W}
    [S.IsLattice K] [T.IsLattice K] [Module.Free R S] (e : S ≃ₗ[R] T) :
    S.map ((LinearEquiv.extendOfIsLattice e).restrictScalars R).toLinearMap = T := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hmem : (e (⟨x, hx⟩ : S) : W) ∈ T := (e ⟨x, hx⟩).2
    rw [← LinearEquiv.extendOfIsLattice_apply] at hmem
    simpa only [LinearEquiv.restrictScalars_apply, LinearEquiv.coe_toLinearMap] using hmem
  · intro y hy
    let yT : T := ⟨y, hy⟩
    let xS : S := e.symm yT
    refine ⟨(xS : V), xS.2, ?_⟩
    simpa only [LinearEquiv.restrictScalars_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.extendOfIsLattice_apply] using congr_arg Subtype.val (e.apply_symm_apply yT)

end

end TauCeti

namespace Submodule

section Rationalization

variable {R : Type u} {K : Type v} {V' : Type w}
variable [CommRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V'] [Module R V'] [Module K V'] [IsScalarTower R K V']

/-- The inclusion of a free full lattice submodule into its ambient vector space over the fraction
field exhibits that space as base change from `R` to `K`. (`R` is a domain anyway, embedding in
the field `K`, so no domain hypothesis is needed.) -/
theorem isBaseChange_subtype (S : Submodule R V') [Module.Free R S] [S.IsLattice K] :
    IsBaseChange K S.subtype := by
  have : IsDomain R := (IsFractionRing.injective R K).isDomain (algebraMap R K)
  have : Module.IsTorsionFree R K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (IsFractionRing.injective R K)
  let b := Module.Free.chooseBasis R S
  let e : K ⊗[R] S ≃ₗ[K] V' :=
    (b.baseChange K).equiv (b.extendOfIsLattice K) (Equiv.refl _)
  have hmap : (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R K S 1) =
      S.subtype := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
      LinearEquiv.coe_coe, Submodule.subtype_apply]
    rw [← Module.Basis.baseChange_apply K b i, Basis.equiv_apply,
      Basis.extendOfIsLattice_apply, Equiv.refl_apply]
  exact IsBaseChange.of_equiv e fun x ↦ DFunLike.congr_fun hmap x

/-- The canonical equivalence from the scalar extension of a free full lattice submodule to its
ambient vector space. -/
noncomputable def rationalizationEquiv (S : Submodule R V') [Module.Free R S] [S.IsLattice K] :
    K ⊗[R] S ≃ₗ[K] V' :=
  (isBaseChange_subtype S).equiv

/-- The rationalization equivalence sends a pure tensor to scalar multiplication of the embedded
lattice vector. This equation characterizes the equivalence. -/
@[simp]
theorem rationalizationEquiv_tmul (S : Submodule R V') [Module.Free R S] [S.IsLattice K]
    (k : K) (x : S) : rationalizationEquiv S (k ⊗ₜ[R] x) = k • (x : V') :=
  (isBaseChange_subtype S).equiv_tmul k x

/-- The inverse rationalization equivalence sends an embedded lattice vector to the corresponding
unit pure tensor. -/
@[simp]
theorem rationalizationEquiv_symm_coe (S : Submodule R V') [Module.Free R S] [S.IsLattice K]
    (x : S) : (rationalizationEquiv S).symm (x : V') = 1 ⊗ₜ[R] x :=
  (isBaseChange_subtype S).equiv_symm_apply x

/-- A `K`-linear endomorphism of the ambient space which restricts to an endomorphism `g` of a
free full lattice `S` has the determinant of `g`, read in `K`. -/
theorem _root_.LinearMap.det_eq_algebraMap_det_of_isLattice {S : Submodule R V'}
    [Module.Free R S] [S.IsLattice K] (f : V' →ₗ[K] V') (g : S →ₗ[R] S)
    (h : ∀ x : S, f x = g x) : LinearMap.det f = algebraMap R K (LinearMap.det g) := by
  -- Rationalization identifies `f` with the base change of `g`.
  have := IsDomain.of_faithfulSMul R K
  have hconj : f = (rationalizationEquiv S).toLinearMap ∘ₗ g.baseChange K ∘ₗ
      (rationalizationEquiv S).symm.toLinearMap := by
    rw [← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm]
    ext x
    simp [h]
  rw [hconj, LinearMap.det_conj, LinearMap.det_baseChange]

end Rationalization

section Map

variable {R A : Type*} {V : Type u} {W : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
variable [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]

/-- A surjective linear map over a commutative-ring algebra sends a full lattice to a full
lattice. -/
theorem isLattice_map (S : Submodule R V) [S.IsLattice A] (f : V →ₗ[A] W)
    (hf : Function.Surjective f) : (S.map (f.restrictScalars R)).IsLattice A where
  fg := Submodule.FG.map (f.restrictScalars R)
    _root_.Submodule.IsLattice.fg
  span_eq_top := by
    simp [Submodule.map_coe, Submodule.span_image, _root_.Submodule.IsLattice.span_eq_top,
      LinearMap.range_eq_top.mpr hf]

end Map

section Pi

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {ι : Type*} [Finite ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [∀ i, Module A (V i)] [∀ i, IsScalarTower R A (V i)]

/-- The families all of whose values lie in full lattices form a full lattice of the product. -/
instance IsLattice.pi (M : ∀ i, Submodule R (V i)) [∀ i, (M i).IsLattice A] :
    (Submodule.pi Set.univ M).IsLattice A where
  fg := Submodule.fg_pi fun _ ↦ _root_.Submodule.IsLattice.fg
  span_eq_top := by
    classical
    cases nonempty_fintype ι
    rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hx : x i ∈ Submodule.span A (M i : Set (V i)) := by
      rw [_root_.Submodule.IsLattice.span_eq_top]
      exact Submodule.mem_top
    have hmap : Submodule.map (LinearMap.single A V i) (Submodule.span A (M i : Set (V i))) ≤
        Submodule.span A (Submodule.pi Set.univ M : Set (∀ i, V i)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact Submodule.subset_span (Submodule.le_comap_single_pi M hv)
    exact hmap (Submodule.mem_map_of_mem hx)

end Pi

section Prod

variable {R A V W : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommMonoid V] [Module R V] [Module A V] [IsScalarTower R A V]
  [AddCommMonoid W] [Module R W] [Module A W] [IsScalarTower R A W]

/-- The product of two full lattices is a full lattice of the product. -/
instance IsLattice.prod (M : Submodule R V) (N : Submodule R W) [M.IsLattice A]
    [N.IsLattice A] : (M.prod N).IsLattice A where
  fg := _root_.Submodule.IsLattice.fg.prod _root_.Submodule.IsLattice.fg
  span_eq_top := by
    rw [Submodule.prod_coe, Submodule.span_prod_eq (R := A) M.zero_mem N.zero_mem,
      _root_.Submodule.IsLattice.span_eq_top, _root_.Submodule.IsLattice.span_eq_top,
      Submodule.prod_top]

end Prod

section Span

variable {R A V : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

/-- The `R`-span of a finite set spanning `V` over `A` is a full lattice. In particular every
finite-dimensional vector space contains a lattice, the span of a basis. -/
theorem isLattice_span {s : Set V} (hs : s.Finite) (hspan : span A s = ⊤) :
    (span R s).IsLattice A where
  fg := ⟨hs.toFinset, by simp⟩
  span_eq_top := by rw [span_span_of_tower, hspan]

end Span

section Squeeze

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

open scoped Pointwise in
/-- A submodule `M` of `V` squeezed between `D⁻¹ • N` and `D • N` for a nonzero integer `D` is a
full lattice when `N` is. -/
theorem IsLattice.of_nsmul_mem_of_nsmul_mem {N M : Submodule ℤ V} [N.IsLattice ℚ]
    {D : ℕ} (hD0 : D ≠ 0) (hNM : ∀ v ∈ N, D • v ∈ M) (hMN : ∀ v ∈ M, D • v ∈ N) :
    M.IsLattice ℚ := by
  have hinj : Function.Injective (DistribSMul.toLinearMap ℤ V (D : ℤ)) := fun x y h ↦ by
    simp only [DistribSMul.toLinearMap_apply, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h
    exact smul_right_injective V (Nat.cast_ne_zero.mpr hD0) h
  have hfg : M.FG := fg_of_fg_map_injective _ hinj
    (FG.of_le_of_isNoetherian (T := N) (map_le_iff_le_comap.mpr fun v hv ↦ by
      simpa using hMN v hv))
  let a : ℚˣ := Units.mk0 (D : ℚ) (Nat.cast_ne_zero.mpr hD0)
  refine IsLattice.of_le_of_isLattice_of_fg ℚ (M := a • N) (fun x hx ↦ ?_) hfg
  obtain ⟨v, hv, rfl⟩ := mem_smul_pointwise_iff_exists _ _ _ |>.mp hx
  simpa [a, Units.smul_def, Nat.cast_smul_eq_nsmul] using hNM v hv

end Squeeze

end Submodule

namespace TensorProduct

variable {R : Type u} {K : Type v} {M : Type w}

section CommRing

variable [CommRing R] [CommRing K] [Algebra R K]

/-- The unit pure tensors form a full lattice in the scalar extension of a finite module. -/
instance isLattice_range_mk_one [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    (LinearMap.range (TensorProduct.mk R K M 1)).IsLattice K where
  fg := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  span_eq_top := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => exact add_mem hx hy
    | tmul k m =>
      rw [tmul_eq_smul_one_tmul]
      exact Submodule.smul_mem _ k (Submodule.subset_span ⟨m, rfl⟩)

end CommRing

variable [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- Rationalizing the unit-tensor lattice recovers the scalar extension it sits in: base-changing
the unit-tensor equivalence and then rationalizing is the identity. -/
@[simp]
theorem rationalizationEquiv_baseChange_unitTmulEquiv (x : K ⊗[R] M) :
    Submodule.rationalizationEquiv (LinearMap.range (TensorProduct.mk R K M 1))
        (LinearEquiv.baseChange R K M _ (unitTmulEquiv R K M) x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul k m =>
    rw [LinearEquiv.baseChange_tmul, Submodule.rationalizationEquiv_tmul,
      coe_unitTmulEquiv_apply]
    exact (tmul_eq_smul_one_tmul k m).symm

/-- The bundled form of `rationalizationEquiv_baseChange_unitTmulEquiv`. -/
theorem unitTmulEquiv_baseChange_trans_rationalizationEquiv :
    (LinearEquiv.baseChange R K M _ (unitTmulEquiv R K M)).trans
        (Submodule.rationalizationEquiv (LinearMap.range (TensorProduct.mk R K M 1))) =
      LinearEquiv.refl K (K ⊗[R] M) :=
  LinearEquiv.ext rationalizationEquiv_baseChange_unitTmulEquiv

end TensorProduct

namespace Submodule.IsLattice

universe u v w

variable {R : Type u} {K : Type v} {V' : Type w}
variable [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V'] [Module R V'] [Module K V'] [IsScalarTower R K V']

variable (K) in
omit [IsDomain R] in
/-- Some nonzero multiple of every ambient vector lies in a submodule spanning the ambient space
over the fraction field `K`, in particular in a full lattice submodule. -/
theorem exists_ne_zero_smul_mem (S : Submodule R V') (hS : Submodule.span K (S : Set V') = ⊤)
    (v : V') : ∃ r : R, r ≠ 0 ∧ r • v ∈ S := by
  have := IsDomain.of_faithfulSMul R K
  have hv : v ∈ Submodule.span K (S : Set V') := by
    rw [hS]
    trivial
  obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K
    (S : Set V') v hv
  rw [Submodule.span_eq] at hr
  exact ⟨r, nonZeroDivisors.coe_ne_zero r, hr⟩

variable (K) in
/-- Every element of a scalar extension `T ⊗[R] V'` has a nonzero multiple in the base change of a
submodule spanning `V'` over the fraction field `K`. -/
theorem _root_.Submodule.exists_ne_zero_smul_mem_baseChange {T : Type*} [CommSemiring T]
    [Algebra R T] (S : Submodule R V') (hS : Submodule.span K (S : Set V') = ⊤) (z : T ⊗[R] V') :
    ∃ r : R, r ≠ 0 ∧ r • z ∈ S.baseChange T := by
  induction z using TensorProduct.inductionOn with
  | tmul t x =>
    obtain ⟨r, hr, hrx⟩ := exists_ne_zero_smul_mem K S hS x
    refine ⟨r, hr, ?_⟩
    rw [← TensorProduct.tmul_smul]
    exact Submodule.tmul_mem_baseChange_of_mem t hrx
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨r₁, hr₁, h₁⟩ := h₁
    obtain ⟨r₂, hr₂, h₂⟩ := h₂
    refine ⟨r₂ * r₁, mul_ne_zero hr₂ hr₁, ?_⟩
    rw [smul_add, mul_smul, mul_comm, mul_smul]
    exact add_mem ((S.baseChange T).smul_of_tower_mem r₂ h₁)
      ((S.baseChange T).smul_of_tower_mem r₁ h₂)

variable (K) in
omit [IsDomain R] in
/-- The inclusion of a submodule spanning the ambient space over the fraction field `K`, in
particular of a full lattice submodule, localizes it at the nonzero divisors of `R`. -/
theorem isLocalizedModule_subtype (S : Submodule R V') (hS : Submodule.span K (S : Set V') = ⊤) :
    IsLocalizedModule (nonZeroDivisors R) S.subtype := by
  have := IsDomain.of_faithfulSMul R K
  have := isLocalizedModule_id (nonZeroDivisors R) V' K
  refine ⟨IsLocalizedModule.map_units (LinearMap.id : V' →ₗ[R] V'), ?_, ?_⟩
  · intro v
    obtain ⟨r, hr, hv⟩ := exists_ne_zero_smul_mem K S hS v
    exact ⟨⟨⟨r • v, hv⟩, ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩⟩, rfl⟩
  · intro x y h
    exact ⟨1, by simpa using Subtype.ext h⟩

variable (K) in
omit [IsDomain R] in
/-- The `R`-finrank of a submodule spanning the ambient space over the fraction field `K`, in
particular of a full lattice, equals the `K`-finrank of the ambient space. -/
theorem _root_.Submodule.finrank_eq_finrank (N : Submodule R V')
    (hN : Submodule.span K (N : Set V') = ⊤) :
    Module.finrank R N = Module.finrank K V' := by
  have := IsDomain.of_faithfulSMul R K
  have := isLocalizedModule_subtype K N hN
  rw [IsFractionRing.finrank_right_eq (R := R) (S := K) (N := V'),
    IsLocalizedModule.finrank_eq (nonZeroDivisors R) N.subtype le_rfl]

variable (K) in
omit [IsDomain R] in
/-- **Clearing denominators.** A single nonzero scalar multiplies a finitely generated submodule
into a submodule spanning the ambient space over `K`, such as a full lattice. -/
theorem exists_ne_zero_forall_smul_mem (S : Submodule R V')
    (hS : Submodule.span K (S : Set V') = ⊤) {M : Submodule R V'} (hM : M.FG) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ M, r • x ∈ S := by
  have := IsDomain.of_faithfulSMul R K
  obtain ⟨r, hr, h⟩ := hM.exists_smul_mem_of_le_span (F := K) (nonZeroDivisors R) (M := S)
    (by rw [hS]; exact fun _ _ ↦ Submodule.mem_top)
  exact ⟨r, nonZeroDivisors.ne_zero hr, h⟩

variable (K) in
/-- **Commensurability over a discrete valuation ring.** A power of the maximal ideal multiplies a
finitely generated submodule into a full lattice. -/
theorem exists_maximalIdeal_pow_smul_le [IsDiscreteValuationRing R] (S : Submodule R V')
    [S.IsLattice K] {M : Submodule R V'} (hM : M.FG) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n • M ≤ S := by
  obtain ⟨r, hr0, hr⟩ :=
    exists_ne_zero_forall_smul_mem K S (IsLattice.span_eq_top (A := K) (M := S)) hM
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  -- The ideal `(r)` is a power `(ϖ ^ n) = 𝔪 ^ n` of the maximal ideal.
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (Ideal.span_singleton_eq_bot.not.mpr hr0) hϖ
  have hm : IsLocalRing.maximalIdeal R ^ n = Ideal.span {r} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, hn]
  refine ⟨n, Submodule.smul_le.mpr fun s hs x hx ↦ ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (hm ▸ hs)
  rw [mul_smul]
  exact S.smul_mem c (hr x hx)

end Submodule.IsLattice

namespace Submodule

section Subsingleton

variable {R A V : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommMonoid V] [Module R V] [Module A V] [IsScalarTower R A V]

variable (A) in
/-- In a subsingleton module, the zero submodule is a full lattice. -/
theorem isLattice_bot_of_subsingleton [Subsingleton V] : (⊥ : Submodule R V).IsLattice A where
  fg := fg_bot
  span_eq_top := Subsingleton.elim _ _

end Subsingleton

section FreeSmul

open scoped Pointwise

/-- Scaling a free submodule by a group element preserves freeness. -/
instance free_smul {R G V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [Group G] [DistribMulAction G V] [SMulCommClass G R V]
    (a : G) (M : Submodule R V) [Module.Free R M] :
    Module.Free R (a • M : Submodule R V) :=
  Module.Free.of_equiv
    (M.equivMapOfInjective (DistribSMul.toLinearMap R V a) (MulAction.injective a))

/-- The unit submodule `1 : Submodule R A` of a faithful `R`-algebra is free over `R`. -/
instance free_one {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A] :
    Module.Free R (1 : Submodule R A) :=
  Module.Free.of_equiv
    ((LinearEquiv.ofInjective (Algebra.linearMap R A) (FaithfulSMul.algebraMap_injective R A)).trans
      (LinearEquiv.ofEq _ _ one_eq_range.symm))

end FreeSmul

section RankOne

open scoped Pointwise

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

/-- Scaling the standard lattice `1 : Submodule R K` by a unit of `R` leaves it unchanged. -/
@[simp]
theorem units_map_algebraMap_smul_one (u : Rˣ) :
    (Units.map (algebraMap R K : R →* K) u) • (1 : Submodule R K) = 1 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact mem_one.mpr ⟨(u : R) * r, by simp⟩
  · intro x hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    refine ⟨algebraMap R K ((u⁻¹ : Rˣ) * r), mem_one.mpr ⟨(u⁻¹ : Rˣ) * r, rfl⟩, ?_⟩
    simp [← map_mul, ← mul_assoc]

/-- **Powers of a nonzero nonunit order their multiples of `1` reversely.** -/
theorem zpow_smul_one_le_iff [FaithfulSMul R K] {ϖ : R} (hϖ0 : ϖ ≠ 0) (hϖu : ¬IsUnit ϖ)
    (m n : ℤ) :
    (Units.mk0 (algebraMap R K ϖ)
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr hϖ0)) ^ m •
        (1 : Submodule R K) ≤
      (Units.mk0 (algebraMap R K ϖ)
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr hϖ0)) ^ n •
        (1 : Submodule R K) ↔ n ≤ m := by
  let u : Kˣ := Units.mk0 (algebraMap R K ϖ)
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mpr hϖ0)
  change u ^ m • (1 : Submodule R K) ≤ u ^ n • (1 : Submodule R K) ↔ n ≤ m
  constructor
  · intro h
    by_contra hlt
    have hlt : m < n := not_le.mp hlt
    have hm : ((u ^ m : Kˣ) : K) ∈ u ^ m • (1 : Submodule R K) :=
      (mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨1, mem_one.mpr ⟨1, map_one _⟩, by simp [Units.smul_def]⟩
    obtain ⟨x, hx, hxu⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp (h hm)
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hlt.le)
    have hk0 : k ≠ 0 := by omega
    have hmul : ((u ^ (n - m) : Kˣ) : K) * algebraMap R K r = 1 := by
      have h1 : ((u ^ n : Kˣ) : K) * algebraMap R K r = ((u ^ m : Kˣ) : K) := by
        simpa [Units.smul_def] using hxu
      have h2 : ((u ^ (-m) : Kˣ) : K) * (((u ^ n : Kˣ) : K) * algebraMap R K r) =
          ((u ^ (-m) : Kˣ) : K) * ((u ^ m : Kˣ) : K) := congrArg _ h1
      rw [← mul_assoc, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add, neg_add_cancel,
        zpow_zero, Units.val_one, neg_add_eq_sub] at h2
      exact h2
    have halg : algebraMap R K (ϖ ^ k * r) = algebraMap R K 1 := by
      simpa [u, hk, map_mul, map_pow] using hmul
    have hunit : IsUnit (ϖ ^ k) :=
      isUnit_iff_exists_inv.mpr ⟨r, FaithfulSMul.algebraMap_injective R K halg⟩
    exact hϖu ((isUnit_pow_iff hk0).mp hunit)
  · intro h
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hy
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    refine (mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨algebraMap R K (ϖ ^ k * r), mem_one.mpr ⟨ϖ ^ k * r, rfl⟩, ?_⟩
    have hm : m = n + k := by omega
    simp only [hm, zpow_add, zpow_natCast, Units.smul_def, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_mk0, smul_eq_mul, map_mul, map_pow, u, mul_assoc]

/-- **Rank-one free lattices are unit multiples of `1`.** Every free full `R`-lattice in the
fraction field `K` has the form `c • 1` for some `c : Kˣ`. -/
theorem IsLattice.exists_eq_smul_one [IsFractionRing R K] (L : Submodule R K)
    [L.IsLattice K] [Module.Free R L] :
    ∃ c : Kˣ, L = c • (1 : Submodule R K) := by
  let b := Module.Free.chooseBasis R L
  let σ := (b.extendOfIsLattice K).indexEquiv (Basis.singleton Unit K)
  let e := (b.extendOfIsLattice K).reindex σ
  refine ⟨Units.mk0 (e ()) (e.ne_zero ()), ?_⟩
  have hrange : Set.range (b.extendOfIsLattice K) = {e ()} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      have h : e (σ i) = b.extendOfIsLattice K i := by simp [e]
      rw [← h]
    · rintro rfl
      exact ⟨σ.symm (), by simp [e]⟩
  rw [← b.span_range_extendOfIsLattice (K := K), hrange]
  ext x
  simp only [mem_span_singleton, mem_smul_pointwise_iff_exists, mem_one, Units.smul_def,
    Units.val_mk0, smul_eq_mul, Algebra.smul_def]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨algebraMap R K r, ⟨r, rfl⟩, mul_comm _ _⟩
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, mul_comm _ _⟩

/-- **Rank-one lattices over a discrete valuation ring.** Every full `R`-lattice in the fraction
field `K` of a discrete valuation ring `R` with uniformizer `ϖ` has the form `ϖᵏ • 1` for a unique
`k : ℤ`. -/
theorem IsLattice.existsUnique_zpow_smul_one [IsDomain R] [IsDiscreteValuationRing R]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (L : Submodule R K) [L.IsLattice K] :
    ∃! k : ℤ, L = (Units.mk0 (algebraMap R K ϖ)
      ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero)) ^ k •
        (1 : Submodule R K) := by
  obtain ⟨c, rfl⟩ := IsLattice.exists_eq_smul_one L
  obtain ⟨k, u, hcu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (K := K) hϖ c.ne_zero
  let ϖK : Kˣ := Units.mk0 (algebraMap R K ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero)
  have hc : c = ϖK ^ k * Units.map (algebraMap R K : R →* K) u := by
    apply Units.ext
    simpa [ϖK, Units.smul_def, Algebra.smul_def, mul_comm] using hcu
  refine ⟨k, ?_, fun m hm ↦ ?_⟩
  · rw [hc, mul_smul, units_map_algebraMap_smul_one]
  · rw [hc, mul_smul, units_map_algebraMap_smul_one] at hm
    exact le_antisymm
      ((zpow_smul_one_le_iff (K := K) hϖ.ne_zero hϖ.not_isUnit k m).mp hm.le)
      ((zpow_smul_one_le_iff (K := K) hϖ.ne_zero hϖ.not_isUnit m k).mp hm.ge)

end RankOne

section Subquotient

variable {R K V : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- **Projection of a full lattice to a quotient.** The image of a full lattice `L` in `V ⧸ W` is
a full lattice of `V ⧸ W`. -/
instance IsLattice.map_mkQ (W : Submodule K V) (L : Submodule R V) [L.IsLattice K] :
    (L.map (W.mkQ.restrictScalars R)).IsLattice K :=
  isLattice_map L W.mkQ W.mkQ_surjective

/-- The canonical identification between `W ∩ L` viewed inside `L` and viewed inside `W`. -/
def comapSubtypeEquivComapSubtype (W : Submodule K V) (L : Submodule R V) :
    ((W.restrictScalars R).comap L.subtype : Submodule R L) ≃ₗ[R]
      (L.comap (W.subtype.restrictScalars R) : Submodule R W) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_comapSubtypeEquivComapSubtype (W : Submodule K V) (L : Submodule R V)
    (x : ((W.restrictScalars R).comap L.subtype : Submodule R L)) :
    ((comapSubtypeEquivComapSubtype W L x : W) : V) = (x.1 : V) :=
  (rfl)

@[simp]
theorem coe_comapSubtypeEquivComapSubtype_symm (W : Submodule K V) (L : Submodule R V)
    (y : (L.comap (W.subtype.restrictScalars R) : Submodule R W)) :
    (((comapSubtypeEquivComapSubtype W L).symm y : L) : V) = (y.1 : V) :=
  (rfl)

/-- **Canonical identification of `L ⧸ (W ∩ L)` with the image of `L` in `V ⧸ W`.** -/
noncomputable def quotientComapSubtypeEquivMapMkQ (W : Submodule K V) (L : Submodule R V) :
    (L ⧸ (W.restrictScalars R).comap L.subtype) ≃ₗ[R] L.map (W.mkQ.restrictScalars R) :=
  let f : L →ₗ[R] V ⧸ W := (W.mkQ.restrictScalars R).comp L.subtype
  have hker : LinearMap.ker f = (W.restrictScalars R).comap L.subtype := by
    ext x
    simp [f, Submodule.Quotient.mk_eq_zero]
  have hrange : LinearMap.range f = L.map (W.mkQ.restrictScalars R) := by
    ext y
    simp [f]
  (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

@[simp]
theorem coe_quotientComapSubtypeEquivMapMkQ_mk (W : Submodule K V) (L : Submodule R V) (x : L) :
    (quotientComapSubtypeEquivMapMkQ W L (Submodule.Quotient.mk x) : V ⧸ W) =
      Submodule.Quotient.mk (x : V) :=
  (rfl)

end Subquotient

section SubquotientField

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- **Saturation of a full lattice.** Over a Noetherian ring `R` with fraction field `K`,
intersecting a full `R`-lattice `L` in `V` with a `K`-subspace `W` yields a full `R`-lattice
`W ∩ L` in `W`. -/
instance IsLattice.comap_subtype [IsNoetherianRing R] [IsFractionRing R K]
    (W : Submodule K V) (L : Submodule R V) [L.IsLattice K] :
    (L.comap (W.subtype.restrictScalars R)).IsLattice K where
  fg := by
    have : IsNoetherian R L := isNoetherian_of_isNoetherianRing_of_finite R L
    refine fg_of_fg_map_injective (W.subtype.restrictScalars R) W.injective_subtype ?_
    exact FG.of_le_of_isNoetherian (T := L) (map_comap_le _ _)
  span_eq_top := by
    have := IsDomain.of_faithfulSMul R K
    rw [eq_top_iff]
    rintro w -
    obtain ⟨r, hr0, hr⟩ := IsLattice.exists_ne_zero_smul_mem K L
      (IsLattice.span_eq_top (A := K) (M := L)) (w : V)
    have hrmem : r • w ∈ L.comap (W.subtype.restrictScalars R) := by
      simpa [Submodule.mem_comap] using hr
    have hrK : algebraMap R K r ≠ 0 := by
      simpa [map_eq_zero_iff _ (IsFractionRing.injective R K)] using hr0
    have hw : w = (algebraMap R K r)⁻¹ • (r • w) := by
      rw [← algebraMap_smul K r w, smul_smul, inv_mul_cancel₀ hrK, one_smul]
    rw [hw]
    exact smul_mem _ _ (subset_span hrmem)

/-- **The quotient of a submodule by its intersection with a subspace is torsion-free.** It embeds
into the `K`-vector space `V ⧸ W`, which is torsion-free over `R`. -/
instance isTorsionFree_quotient_comap_subtype [IsDomain R] [FaithfulSMul R K]
    (W : Submodule K V) (L : Submodule R V) :
    Module.IsTorsionFree R (L ⧸ (W.restrictScalars R).comap L.subtype) := by
  have : Module.IsTorsionFree R K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R K)
  have : Module.IsTorsionFree R (V ⧸ W) := Module.IsTorsionFree.trans_faithfulSMul R K (V ⧸ W)
  have h : Function.Injective ((L.map (W.mkQ.restrictScalars R)).subtype.comp
      (quotientComapSubtypeEquivMapMkQ W L).toLinearMap) :=
    (L.map (W.mkQ.restrictScalars R)).injective_subtype.comp
      (quotientComapSubtypeEquivMapMkQ W L).injective
  refine Module.IsTorsionFree.of_smul_eq_zero fun r x hrx ↦ ?_
  have h' : r • ((L.map (W.mkQ.restrictScalars R)).subtype
      (quotientComapSubtypeEquivMapMkQ W L x)) = 0 := by
    rw [← map_smul, ← map_smul, hrx, map_zero, map_zero]
  rcases smul_eq_zero.mp h' with rfl | hx
  · exact Or.inl rfl
  · exact Or.inr (h (by simpa using hx))

/-- **Splitting of `0 → W ∩ L → L → L ⧸ (W ∩ L) → 0` over a principal ideal domain.** Since
`L ⧸ (W ∩ L)` is finitely generated and torsion-free over the principal ideal domain `R`, it is
free and hence projective, so the quotient map admits an `R`-linear section. -/
theorem exists_rightInverse_mkQ_comap_subtype [IsDomain R] [IsPrincipalIdealRing R]
    [FaithfulSMul R K] (W : Submodule K V) (L : Submodule R V) [Module.Finite R L] :
    ∃ s : (L ⧸ (W.restrictScalars R).comap L.subtype) →ₗ[R] L,
      ((W.restrictScalars R).comap L.subtype).mkQ.comp s = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ (Submodule.range_mkQ _)

/-- **Direct-sum decomposition of a lattice along a subspace over a principal ideal domain.**
There is an `R`-linear isomorphism `L ≃ₗ[R] (W ∩ L) × (image of L in V ⧸ W)` whose second
coordinate is the canonical quotient projection and whose inverse sends `W ∩ L` identically into
`L`. -/
theorem exists_linearEquiv_prod_comap_subtype_map_mkQ [IsDomain R] [IsPrincipalIdealRing R]
    [FaithfulSMul R K] (W : Submodule K V) (L : Submodule R V) [Module.Finite R L] :
    ∃ e : L ≃ₗ[R] (L.comap (W.subtype.restrictScalars R) × L.map (W.mkQ.restrictScalars R)),
      (∀ x : L, ((e x).2 : V ⧸ W) = W.mkQ x) ∧
      (∀ y : L.comap (W.subtype.restrictScalars R), (e.symm (y, 0) : V) = y.1) := by
  let p := (W.restrictScalars R).comap L.subtype
  obtain ⟨s, hs⟩ := exists_rightInverse_mkQ_comap_subtype (K := K) W L
  have hmkQ : ∀ q, Submodule.Quotient.mk (p := p) (s q) = q := LinearMap.congr_fun hs
  let e₀ : L ≃ₗ[R] p × (L ⧸ p) :=
    { toFun x := (⟨x - s (p.mkQ x), (Submodule.Quotient.mk_eq_zero p).mp (by
          simp [hmkQ])⟩, p.mkQ x)
      invFun y := (y.1 : L) + s y.2
      left_inv x := sub_add_cancel x (s (p.mkQ x))
      right_inv y := by
        have h0 : (Submodule.Quotient.mk (y.1 : L) : L ⧸ p) = 0 :=
          (Submodule.Quotient.mk_eq_zero p).mpr y.1.2
        apply Prod.ext
        · apply Subtype.ext
          simp [h0, hmkQ]
        · simp [h0, hmkQ]
      map_add' x y := by
        apply Prod.ext
        · apply Subtype.ext
          simp only [Prod.fst_add, Submodule.coe_add, map_add]
          abel
        · simp
      map_smul' r x := by
        apply Prod.ext
        · apply Subtype.ext
          simp [smul_sub]
        · simp }
  let e := e₀.trans
    ((comapSubtypeEquivComapSubtype W L).prodCongr (quotientComapSubtypeEquivMapMkQ W L))
  refine ⟨e, fun x ↦ rfl, fun y ↦ ?_⟩
  simp [e, e₀]

end SubquotientField

end Submodule

