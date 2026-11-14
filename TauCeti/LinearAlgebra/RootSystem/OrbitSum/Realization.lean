/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import Mathlib.LinearAlgebra.RootSystem.Basic

/-!
# Orbit-sum realizations of folded root systems

Let `P` be a root pairing with finitely many roots, `b` a base of `P`, and `σ` an automorphism of
`P`. The distinct orbit sums of `σ` lie in the fixed weight submodule
`LinearMap.fixedSubmodule σ.weightMap` and are indexed by the range subtype
`RootPairing.foldedIndices P σ`.

An **orbit-sum realization** (`RootPairing.OrbitSumRealization P b σ`) packages a reduced
crystallographic root system on `LinearMap.fixedSubmodule σ.weightMap` and its linear dual whose
bilinear pairing is evaluation, whose roots are literally the orbit-sum vectors, and whose simple
roots are the orbit sums of the simple roots of `b`.

Over a domain of characteristic zero, `RootPairing.IsRootSystem.ext` and `RootPairing.Base.ext`
force an orbit-sum realization to be unique (`Subsingleton (P.OrbitSumRealization b σ)`): the
coroot functionals, reflections, and Cartan integers on the fixed space are completely determined
by the orbit-sum root vectors and the evaluation pairing. Moreover, whenever `σ` permutes the
simple roots of `b`, positivity in the folded base agrees with positivity in `b`.

## Main definitions

* `RootPairing.toFoldedIndices`: the orbit sum of a root index packaged as a member of
  `RootPairing.foldedIndices P σ`.
* `RootPairing.OrbitSumRealization`: a reduced crystallographic based root system on the fixed
  weight space and its dual whose roots are the orbit sums and whose base consists of the simple
  orbit sums.
* `RootPairing.OrbitSumRealization.one`: the canonical orbit-sum realization for the identity
  automorphism `1 : P.Aut`.
* `RootPairing.OrbitSumRealization.oneEquiv`: the root-pairing equivalence between `P` and the
  realization of `1 : P.Aut`.
* `RootPairing.OrbitSumRealization.equivOfIntertwine`: the equivalence of orbit-sum realizations
  induced by a root-pairing equivalence intertwining the automorphisms.

## Main results

* `RootPairing.OrbitSumRealization.instSubsingleton`: over an integral domain of characteristic
  zero, at most one orbit-sum realization exists for given `(P, b, σ)`.
* `RootPairing.OrbitSumRealization.coe_mem_posRootCone`: for `σ` permuting `b.support`, the
  positive root cone of any orbit-sum realization embeds into `TauCeti.posRootCone P b`.
* `RootPairing.OrbitSumRealization.isPos_toFoldedIndices_iff` and
  `RootPairing.OrbitSumRealization.isPos_iff_exists`: positivity in the folded base agrees with
  positivity in `b`.
* `RootPairing.OrbitSumRealization.base_map_equivOfIntertwine`: a base-preserving intertwining
  equivalence induces a based equivalence of orbit-sum realizations.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, Claim 1.
-/

public section

namespace RootPairing

open Finset TauCeti

section FoldedIndices

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] (σ : P.Aut)

/-- The orbit sum of `i` packaged as an element of `P.foldedIndices σ`. -/
noncomputable def toFoldedIndices (i : ι) : P.foldedIndices σ :=
  ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩

@[simp]
theorem coe_toFoldedIndices (i : ι) : (P.toFoldedIndices σ i : M) = P.orbitSum σ i :=
  (rfl)

theorem toFoldedIndices_surjective : Function.Surjective (P.toFoldedIndices σ) := fun γ ↦ by
  obtain ⟨i, hi⟩ := (mem_foldedIndices (P := P) (σ := σ)).mp γ.2
  exact ⟨i, Subtype.ext hi⟩

@[simp]
theorem toFoldedIndices_indexEquiv (i : ι) :
    P.toFoldedIndices σ (σ.indexEquiv i) = P.toFoldedIndices σ i :=
  Subtype.ext (P.orbitSum_indexEquiv σ i)

@[simp]
theorem weightMap_coe_foldedIndices (γ : P.foldedIndices σ) : σ.weightMap (γ : M) = (γ : M) := by
  obtain ⟨i, rfl⟩ := P.toFoldedIndices_surjective σ γ
  exact P.weightMap_orbitSum_self σ i

theorem coe_foldedIndices_mem_fixedSubmodule (γ : P.foldedIndices σ) :
    (γ : M) ∈ LinearMap.fixedSubmodule σ.weightMap :=
  LinearMap.mem_fixedSubmodule_iff.mpr (P.weightMap_coe_foldedIndices σ γ)

variable {P σ}

theorem toFoldedIndices_eq_iff {i j : ι} :
    P.toFoldedIndices σ i = P.toFoldedIndices σ j ↔ P.orbitSum σ i = P.orbitSum σ j :=
  Subtype.ext_iff

theorem toFoldedIndices_eq_of_mem {i j : ι} (h : j ∈ P.orbitIndices σ i) :
    P.toFoldedIndices σ j = P.toFoldedIndices σ i :=
  Subtype.ext (orbitSum_eq_of_mem h)

end FoldedIndices

section Structure

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A realization bundles a native based root pairing on the fixed space and its dual. Its roots
are the actual distinct orbit-sum vectors, its pairing is evaluation, and its base consists
exactly of the simple-orbit sums. -/
structure OrbitSumRealization (P : RootPairing ι R M N) [Finite ι]
    (b : P.Base) (σ : P.Aut) where
  /-- The native pairing on the fixed space and its linear dual. -/
  pairing : RootPairing (P.foldedIndices σ) R (LinearMap.fixedSubmodule σ.weightMap)
    (Module.Dual R (LinearMap.fixedSubmodule σ.weightMap))
  /-- Its finite simple base. -/
  base : pairing.Base
  /-- Both root and coroot families span. -/
  rootSystem : pairing.IsRootSystem
  /-- No proportional roots except a root and its negative. -/
  reduced : pairing.IsReduced
  /-- All root-coroot pairings are integers. -/
  crystallographic : pairing.IsCrystallographic
  /-- The perfect pairing is evaluation against the fixed-space dual. -/
  evaluation : ∀ x y, pairing.toLinearMap x y = y x
  /-- Each root is its actual orbit-sum vector in the ambient space. -/
  root_eq : ∀ i, (pairing.root i : M) = (i : M)
  /-- Simple roots are exactly the original simple-orbit sums. -/
  base_eq : ∀ i, i ∈ base.support ↔
    ∃ j ∈ b.support, P.orbitSum σ j = (i : M)

attribute [instance] OrbitSumRealization.rootSystem OrbitSumRealization.reduced
  OrbitSumRealization.crystallographic

namespace OrbitSumRealization

section Basic

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}
  (F : P.OrbitSumRealization b σ)

@[simp]
theorem toLinearMap_apply (x : LinearMap.fixedSubmodule σ.weightMap)
    (y : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)) :
    F.pairing.toLinearMap x y = y x :=
  F.evaluation x y

@[simp]
theorem coe_root (γ : P.foldedIndices σ) : (F.pairing.root γ : M) = (γ : M) :=
  F.root_eq γ

theorem root_apply (γ : P.foldedIndices σ) :
    F.pairing.root γ = ⟨(γ : M), P.coe_foldedIndices_mem_fixedSubmodule σ γ⟩ :=
  Subtype.ext (F.root_eq γ)

theorem coroot'_apply (γ : P.foldedIndices σ) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' γ x = F.pairing.coroot γ x := by
  rw [RootPairing.coroot', LinearMap.flip_apply, F.evaluation]

theorem toFoldedIndices_mem_support {i : ι} (hi : i ∈ b.support) :
    P.toFoldedIndices σ i ∈ F.base.support :=
  (F.base_eq _).mpr ⟨i, hi, rfl⟩

@[simp]
theorem coe_reflectionPerm_self (γ : P.foldedIndices σ) :
    (F.pairing.reflectionPerm γ γ : M) = -(γ : M) := by
  rw [← F.coe_root, root_reflectionPerm, reflection_apply_self, Submodule.coe_neg, F.coe_root]

@[simp]
theorem reflectionPerm_toFoldedIndices_self (i : ι) :
    F.pairing.reflectionPerm (P.toFoldedIndices σ i) (P.toFoldedIndices σ i) =
      P.toFoldedIndices σ (P.reflectionPerm i i) := by
  apply Subtype.ext
  rw [F.coe_reflectionPerm_self, coe_toFoldedIndices, coe_toFoldedIndices,
    orbitSum_reflectionPerm_self]

end Basic

section Uniqueness

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}
  [CharZero R] [IsDomain R]

/-- Over an integral domain of characteristic zero, at most one orbit-sum realization exists for a
given `(P, b, σ)`: the evaluation pairing, orbit-sum root vectors, and simple-orbit base support
uniquely determine the entire realization. -/
instance instSubsingleton : Subsingleton (P.OrbitSumRealization b σ) where
  allEq F₁ F₂ := by
    have he : F₁.pairing.toLinearMap = F₂.pairing.toLinearMap := by
      ext x y
      rw [F₁.evaluation, F₂.evaluation]
    have hr : F₁.pairing.root = F₂.pairing.root := by
      ext γ : 1
      exact Subtype.ext ((F₁.root_eq γ).trans (F₂.root_eq γ).symm)
    have hp : F₁.pairing = F₂.pairing := IsRootSystem.ext he hr
    rcases F₁ with ⟨P₁, b₁, _, _, _, _, _, hbase₁⟩
    rcases F₂ with ⟨P₂, b₂, _, _, _, _, _, hbase₂⟩
    subst hp
    congr 1
    ext γ
    rw [hbase₁, hbase₂]

end Uniqueness

section Positivity

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut} [CharZero R]
  (F : P.OrbitSumRealization b σ)

/-- When `σ` permutes `b.support`, every element of the positive root cone of the folded base lies
in the ambient positive root cone `posRootCone P b`. -/
theorem coe_mem_posRootCone (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} (hx : x ∈ posRootCone F.pairing F.base) :
    (x : M) ∈ posRootCone P b := by
  obtain ⟨f, rfl⟩ := (mem_posRootCone F.pairing F.base).mp hx
  rw [Submodule.coe_sum]
  refine sum_mem fun γ hγ ↦ ?_
  obtain ⟨j, hj, hjγ⟩ := (F.base_eq γ).mp hγ
  rw [Submodule.coe_smul_of_tower, F.coe_root, ← hjγ]
  exact nsmul_mem (orbitSum_mem_posRootCone hσ (b.isPos_of_mem_support hj)) (f γ)

/-- When `σ` permutes `b.support`, the orbit sum of `i` is positive for the folded base if and
only if `i` is positive for `b`. -/
@[simp]
theorem isPos_toFoldedIndices_iff (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (i : ι) :
    F.base.IsPos (P.toFoldedIndices σ i) ↔ b.IsPos i := by
  have hpos {k : ι} (hk : b.IsPos k) : F.base.IsPos (P.toFoldedIndices σ k) := by
    by_contra hneg
    set γ := P.toFoldedIndices σ k
    have hγ' : F.base.IsPos (F.pairing.reflectionPerm γ γ) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots F.pairing F.base γ).mpr
        ((mem_negRoots F.pairing F.base γ).mpr hneg)
    have hmem₁ : P.orbitSum σ k ∈ posRootCone P b := orbitSum_mem_posRootCone hσ hk
    have hmem₂ : -P.orbitSum σ k ∈ posRootCone P b := by
      have hroot : F.pairing.root (F.pairing.reflectionPerm γ γ) ∈ posRootCone F.pairing F.base :=
        root_mem_posRootCone_of_mem_posRoots F.pairing F.base
          ((mem_posRoots F.pairing F.base _).mpr hγ')
      simpa [γ] using F.coe_mem_posRootCone hσ hroot
    exact orbitSum_ne_zero hσ k
      (eq_zero_of_add_eq_zero_of_mem_posRootCone P b hmem₁ hmem₂ (add_neg_cancel _))
  refine ⟨fun h ↦ ?_, hpos⟩
  by_contra hneg
  have hneg' : b.IsPos (P.reflectionPerm i i) :=
    (isPos_reflectionPerm_self_iff_mem_negRoots P b i).mpr ((mem_negRoots P b i).mpr hneg)
  have hpos' : F.base.IsPos
      (F.pairing.reflectionPerm (P.toFoldedIndices σ i) (P.toFoldedIndices σ i)) := by
    rw [F.reflectionPerm_toFoldedIndices_self]
    exact hpos hneg'
  exact reflectionPerm_self_notMem_posRoots F.pairing F.base
    ((mem_posRoots F.pairing F.base _).mpr h) ((mem_posRoots F.pairing F.base _).mpr hpos')

/-- The positive roots of an orbit-sum realization are precisely the orbit sums of the positive
roots of `b`. -/
theorem isPos_iff_exists (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (γ : P.foldedIndices σ) :
    F.base.IsPos γ ↔ ∃ i, b.IsPos i ∧ P.orbitSum σ i = (γ : M) := by
  obtain ⟨i, rfl⟩ := P.toFoldedIndices_surjective σ γ
  refine ⟨fun h ↦ ⟨i, (F.isPos_toFoldedIndices_iff hσ i).mp h, rfl⟩, ?_⟩
  rintro ⟨j, hj, hjEq⟩
  have hEq : P.toFoldedIndices σ j = P.toFoldedIndices σ i := Subtype.ext hjEq
  rw [← hEq, F.isPos_toFoldedIndices_iff hσ j]
  exact hj

end Positivity

section One

section Aux

variable (P : RootPairing ι R M N)

/-- Auxiliary linear equivalence identifying the fixed space of `1 : P.Aut` with `M`. -/
private def fixedSubmoduleOneEquiv : LinearMap.fixedSubmodule (1 : P.Aut).weightMap ≃ₗ[R] M where
  toFun x := x
  invFun m := ⟨m, LinearMap.mem_fixedSubmodule_iff.mpr rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem coe_fixedSubmoduleOneEquiv_symm (m : M) :
    ((fixedSubmoduleOneEquiv P).symm m : M) = m :=
  rfl

/-- Auxiliary contravariant linear equivalence between the dual of the fixed space of `1 : P.Aut`
and `N`. -/
private noncomputable def dualFixedSubmoduleOneEquiv :
    Module.Dual R (LinearMap.fixedSubmodule (1 : P.Aut).weightMap) ≃ₗ[R] N :=
  (fixedSubmoduleOneEquiv P).symm.dualMap.trans P.toLinearMap.flip.toPerfPair.symm

private theorem toLinearMap_dualFixedSubmoduleOneEquiv (m : M)
    (f : Module.Dual R (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)) :
    P.toLinearMap m (dualFixedSubmoduleOneEquiv P f) = f ((fixedSubmoduleOneEquiv P).symm m) := by
  rw [dualFixedSubmoduleOneEquiv, LinearEquiv.trans_apply, LinearMap.apply_toPerfPair_flip]
  rfl

private theorem dualFixedSubmoduleOneEquiv_symm_apply (n : N)
    (x : LinearMap.fixedSubmodule (1 : P.Aut).weightMap) :
    (dualFixedSubmoduleOneEquiv P).symm n x = P.toLinearMap (x : M) n := by
  have h := toLinearMap_dualFixedSubmoduleOneEquiv P (x : M) ((dualFixedSubmoduleOneEquiv P).symm n)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end Aux

variable (P : RootPairing ι R M N) [Finite ι]

/-- Auxiliary bijection between `ι` and `P.foldedIndices 1`. -/
private noncomputable def toFoldedIndicesOneEquiv : ι ≃ P.foldedIndices (1 : P.Aut) :=
  _root_.Equiv.ofBijective (P.toFoldedIndices 1)
    ⟨fun _ _ h ↦ P.root.injective <| by
        simpa only [toFoldedIndices_eq_iff, orbitSum_one] using h,
      P.toFoldedIndices_surjective 1⟩

@[simp]
private theorem coe_toFoldedIndicesOneEquiv (i : ι) :
    (toFoldedIndicesOneEquiv P i : M) = P.root i := by
  change (P.toFoldedIndices 1 i : M) = P.root i
  rw [coe_toFoldedIndices, orbitSum_one]

/-- The root pairing on the fixed space of `1 : P.Aut` and its dual induced by `P`. -/
private noncomputable def onePairing :
    RootPairing (P.foldedIndices 1) R (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
      (Module.Dual R (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)) where
  toLinearMap := Module.Dual.eval R _
  isPerfPair_toLinearMap := by
    refine LinearMap.IsPerfPair.congr P.toLinearMap
      (fixedSubmoduleOneEquiv P) (dualFixedSubmoduleOneEquiv P) _ ?_
    ext m n
    exact dualFixedSubmoduleOneEquiv_symm_apply P n ((fixedSubmoduleOneEquiv P).symm m)
  root := ⟨fun γ ↦ (fixedSubmoduleOneEquiv P).symm (P.root ((toFoldedIndicesOneEquiv P).symm γ)),
    fun _ _ h ↦ (toFoldedIndicesOneEquiv P).symm.injective
      (P.root.injective ((fixedSubmoduleOneEquiv P).symm.injective h))⟩
  coroot := ⟨fun γ ↦ (dualFixedSubmoduleOneEquiv P).symm
      (P.coroot ((toFoldedIndicesOneEquiv P).symm γ)),
    fun _ _ h ↦ (toFoldedIndicesOneEquiv P).symm.injective
      (P.coroot.injective ((dualFixedSubmoduleOneEquiv P).symm.injective h))⟩
  root_coroot_two γ := by
    change (dualFixedSubmoduleOneEquiv P).symm (P.coroot ((toFoldedIndicesOneEquiv P).symm γ))
      ((fixedSubmoduleOneEquiv P).symm (P.root ((toFoldedIndicesOneEquiv P).symm γ))) = 2
    rw [dualFixedSubmoduleOneEquiv_symm_apply, coe_fixedSubmoduleOneEquiv_symm, P.root_coroot_two]
  reflectionPerm γ :=
    (toFoldedIndicesOneEquiv P).symm.trans
      ((P.reflectionPerm ((toFoldedIndicesOneEquiv P).symm γ)).trans (toFoldedIndicesOneEquiv P))
  reflectionPerm_root γ₁ γ₂ := by
    apply (fixedSubmoduleOneEquiv P).injective
    simp only [map_sub, map_smul, _root_.Equiv.trans_apply, Module.Dual.eval_apply]
    change (fixedSubmoduleOneEquiv P)
        ((fixedSubmoduleOneEquiv P).symm (P.root ((toFoldedIndicesOneEquiv P).symm γ₂))) -
      (dualFixedSubmoduleOneEquiv P).symm (P.coroot ((toFoldedIndicesOneEquiv P).symm γ₁))
        ((fixedSubmoduleOneEquiv P).symm (P.root ((toFoldedIndicesOneEquiv P).symm γ₂))) •
      (fixedSubmoduleOneEquiv P)
        ((fixedSubmoduleOneEquiv P).symm (P.root ((toFoldedIndicesOneEquiv P).symm γ₁))) =
      (fixedSubmoduleOneEquiv P) ((fixedSubmoduleOneEquiv P).symm (P.root
        ((toFoldedIndicesOneEquiv P).symm ((toFoldedIndicesOneEquiv P)
          ((P.reflectionPerm ((toFoldedIndicesOneEquiv P).symm γ₁))
            ((toFoldedIndicesOneEquiv P).symm γ₂))))))
    simp only [LinearEquiv.apply_symm_apply, dualFixedSubmoduleOneEquiv_symm_apply,
      coe_fixedSubmoduleOneEquiv_symm, _root_.Equiv.symm_apply_apply]
    exact P.reflectionPerm_root _ _
  reflectionPerm_coroot γ₁ γ₂ := by
    apply (dualFixedSubmoduleOneEquiv P).injective
    simp only [map_sub, map_smul, _root_.Equiv.trans_apply, Module.Dual.eval_apply]
    change (dualFixedSubmoduleOneEquiv P)
        ((dualFixedSubmoduleOneEquiv P).symm (P.coroot ((toFoldedIndicesOneEquiv P).symm γ₂))) -
      (dualFixedSubmoduleOneEquiv P).symm (P.coroot ((toFoldedIndicesOneEquiv P).symm γ₂))
        ((fixedSubmoduleOneEquiv P).symm (P.root ((toFoldedIndicesOneEquiv P).symm γ₁))) •
      (dualFixedSubmoduleOneEquiv P)
        ((dualFixedSubmoduleOneEquiv P).symm (P.coroot ((toFoldedIndicesOneEquiv P).symm γ₁))) =
      (dualFixedSubmoduleOneEquiv P) ((dualFixedSubmoduleOneEquiv P).symm (P.coroot
        ((toFoldedIndicesOneEquiv P).symm ((toFoldedIndicesOneEquiv P)
          ((P.reflectionPerm ((toFoldedIndicesOneEquiv P).symm γ₁))
            ((toFoldedIndicesOneEquiv P).symm γ₂))))))
    simp only [LinearEquiv.apply_symm_apply, dualFixedSubmoduleOneEquiv_symm_apply,
      coe_fixedSubmoduleOneEquiv_symm, _root_.Equiv.symm_apply_apply]
    exact P.reflectionPerm_coroot _ _

private theorem onePairing_root (γ : P.foldedIndices 1) :
    (onePairing P).root γ =
      (fixedSubmoduleOneEquiv P).symm (P.root ((toFoldedIndicesOneEquiv P).symm γ)) :=
  rfl

private theorem onePairing_coroot (γ : P.foldedIndices 1) :
    (onePairing P).coroot γ =
      (dualFixedSubmoduleOneEquiv P).symm (P.coroot ((toFoldedIndicesOneEquiv P).symm γ)) :=
  rfl

private noncomputable def onePairingEquiv : P.Equiv (onePairing P) where
  weightMap := (fixedSubmoduleOneEquiv P).symm.toLinearMap
  coweightMap := (dualFixedSubmoduleOneEquiv P).toLinearMap
  indexEquiv := toFoldedIndicesOneEquiv P
  weight_coweight_transpose := by
    ext f m
    change f ((fixedSubmoduleOneEquiv P).symm m) = P.toLinearMap m (dualFixedSubmoduleOneEquiv P f)
    exact (toLinearMap_dualFixedSubmoduleOneEquiv P m f).symm
  root_weightMap := by
    ext i : 1
    simp only [Function.comp_apply, LinearEquiv.coe_coe, onePairing_root,
      _root_.Equiv.symm_apply_apply]
  coroot_coweightMap := by
    ext γ : 1
    simp only [Function.comp_apply, LinearEquiv.coe_coe, onePairing_coroot,
      LinearEquiv.apply_symm_apply]
  bijective_weightMap := (fixedSubmoduleOneEquiv P).symm.bijective
  bijective_coweightMap := (dualFixedSubmoduleOneEquiv P).bijective

private theorem isRootSystem_onePairing [P.IsRootSystem] : (onePairing P).IsRootSystem where
  span_root_eq_top := by
    have hr : Set.range (onePairing P).root =
        (fixedSubmoduleOneEquiv P).symm '' Set.range P.root := by
      ext v
      simp only [Set.mem_range, Set.mem_image, onePairing_root]
      exact ⟨fun ⟨γ, hγ⟩ ↦ ⟨_, ⟨_, rfl⟩, hγ⟩,
        fun ⟨_, ⟨i, rfl⟩, hv⟩ ↦
          ⟨toFoldedIndicesOneEquiv P i, by simpa [_root_.Equiv.symm_apply_apply] using hv⟩⟩
    rw [hr, ← LinearEquiv.coe_toLinearMap, ← Submodule.map_span,
      IsRootSystem.span_root_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (fixedSubmoduleOneEquiv P).symm.surjective
  span_coroot_eq_top := by
    have hc : Set.range (onePairing P).coroot =
        (dualFixedSubmoduleOneEquiv P).symm '' Set.range P.coroot := by
      ext f
      simp only [Set.mem_range, Set.mem_image, onePairing_coroot]
      exact ⟨fun ⟨γ, hγ⟩ ↦ ⟨_, ⟨_, rfl⟩, hγ⟩,
        fun ⟨_, ⟨i, rfl⟩, hf⟩ ↦
          ⟨toFoldedIndicesOneEquiv P i, by simpa [_root_.Equiv.symm_apply_apply] using hf⟩⟩
    rw [hc, ← LinearEquiv.coe_toLinearMap, ← Submodule.map_span,
      IsRootSystem.span_coroot_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (dualFixedSubmoduleOneEquiv P).symm.surjective

private theorem isCrystallographic_onePairing [P.IsCrystallographic] :
    (onePairing P).IsCrystallographic where
  exists_value γ₁ γ₂ := by
    let e := onePairingEquiv P
    obtain ⟨z, hz⟩ := IsValuedIn.exists_value (S := ℤ) (self := ‹P.IsCrystallographic›)
      (e.indexEquiv.symm γ₁) (e.indexEquiv.symm γ₂)
    refine ⟨z, hz.trans ?_⟩
    simpa using (Hom.pairing e.toHom (i := e.indexEquiv.symm γ₁) (j := e.indexEquiv.symm γ₂)).symm

private theorem isReduced_onePairing [P.IsReduced] : (onePairing P).IsReduced where
  eq_or_eq_neg γ₁ γ₂ hdep := by
    let i₁ := (toFoldedIndicesOneEquiv P).symm γ₁
    let i₂ := (toFoldedIndicesOneEquiv P).symm γ₂
    have hdep' : ¬ LinearIndependent R ![P.root i₁, P.root i₂] := fun hli ↦ hdep <| by
      have hmap := hli.map' (fixedSubmoduleOneEquiv P).symm.toLinearMap
        (fixedSubmoduleOneEquiv P).symm.ker
      convert hmap using 1
      ext k
      fin_cases k <;> rfl
    rcases IsReduced.eq_or_eq_neg (P := P) i₁ i₂ hdep' with h₁ | h₂
    · left
      rw [onePairing_root, onePairing_root]
      exact congrArg (fixedSubmoduleOneEquiv P).symm h₁
    · right
      rw [onePairing_root, onePairing_root, ← map_neg]
      exact congrArg (fixedSubmoduleOneEquiv P).symm h₂

/-- The canonical orbit-sum realization for the identity automorphism `1 : P.Aut`. -/
noncomputable def one [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) :
    P.OrbitSumRealization b 1 where
  pairing := onePairing P
  base := by
    classical
    exact b.map (onePairingEquiv P)
  rootSystem := isRootSystem_onePairing P
  reduced := isReduced_onePairing P
  crystallographic := isCrystallographic_onePairing P
  evaluation _ _ := rfl
  root_eq γ := by
    obtain ⟨i, rfl⟩ := (toFoldedIndicesOneEquiv P).surjective γ
    rw [onePairing_root, _root_.Equiv.symm_apply_apply, coe_fixedSubmoduleOneEquiv_symm,
      coe_toFoldedIndicesOneEquiv]
  base_eq γ := by
    classical
    rw [Base.support_map_eq, Finset.mem_image]
    refine ⟨fun ⟨j, hj, hEq⟩ ↦ ⟨j, hj, ?_⟩, fun ⟨j, hj, hEq⟩ ↦ ⟨j, hj, ?_⟩⟩
    · rw [← hEq, orbitSum_one]
      exact (coe_toFoldedIndicesOneEquiv P j).symm
    · apply Subtype.ext
      rw [orbitSum_one] at hEq
      simpa [onePairingEquiv] using hEq

/-- The root-pairing equivalence between `P` and `(OrbitSumRealization.one P b).pairing`. -/
noncomputable def oneEquiv [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) :
    P.Equiv (one P b).pairing :=
  onePairingEquiv P

end One

section Intertwine

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {b : P.Base} {σ : P.Aut}
  {P₂ : RootPairing ι₂ R M₂ N₂} {b₂ : P₂.Base} {τ : P₂.Aut}

private theorem weightMap_intertwine [P.IsRootSystem] (e : P.Equiv P₂)
    (hσ : ∀ i, e.indexEquiv (σ.indexEquiv i) = τ.indexEquiv (e.indexEquiv i)) (x : M) :
    e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x) := by
  have hcomp : e.weightMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightMap := by
    refine LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P)) fun i ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Hom.root_weightMap_apply, hσ i]
  exact LinearMap.congr_fun hcomp x

private theorem symm_indexEquiv_intertwine (e : P.Equiv P₂)
    (hσ : ∀ i, e.indexEquiv (σ.indexEquiv i) = τ.indexEquiv (e.indexEquiv i)) (j : ι₂) :
    (Equiv.symm P P₂ e).indexEquiv (τ.indexEquiv j) =
      σ.indexEquiv ((Equiv.symm P P₂ e).indexEquiv j) := by
  rw [Equiv.inv_indexEquiv]
  rw [e.indexEquiv.symm_apply_eq, hσ, e.indexEquiv.apply_symm_apply]

/-- Auxiliary linear equivalence between the fixed weight spaces induced by a root-pairing
equivalence intertwining `σ` and `τ`. -/
private noncomputable def fixedSubmoduleEquivOfIntertwine [P.IsRootSystem] [P₂.IsRootSystem]
    (e : P.Equiv P₂)
    (hσ : ∀ i, e.indexEquiv (σ.indexEquiv i) = τ.indexEquiv (e.indexEquiv i)) :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[R] LinearMap.fixedSubmodule τ.weightMap where
  toFun x := ⟨e.weightMap x.1, LinearMap.mem_fixedSubmodule_iff.mpr <| by
    rw [← weightMap_intertwine e hσ, LinearMap.mem_fixedSubmodule_iff.mp x.2]⟩
  invFun y := ⟨(Equiv.symm P P₂ e).weightMap y.1, LinearMap.mem_fixedSubmodule_iff.mpr <| by
    rw [← weightMap_intertwine (Equiv.symm P P₂ e) (symm_indexEquiv_intertwine e hσ),
      LinearMap.mem_fixedSubmodule_iff.mp y.2]⟩
  map_add' x₁ x₂ := Subtype.ext (map_add e.weightMap x₁.1 x₂.1)
  map_smul' r x := Subtype.ext (map_smul e.weightMap r x.1)
  left_inv x := Subtype.ext <| by
    dsimp only
    rw [Equiv.inv_weightMap, LinearEquiv.coe_coe, ← Equiv.weightEquiv_apply,
      e.weightEquiv.symm_apply_apply]
  right_inv y := Subtype.ext <| by
    dsimp only
    rw [Equiv.inv_weightMap, LinearEquiv.coe_coe, ← Equiv.weightEquiv_apply,
      e.weightEquiv.apply_symm_apply]

variable [Finite ι] [Finite ι₂]

/-- Auxiliary bijection between `P.foldedIndices σ` and `P₂.foldedIndices τ` induced by a
root-pairing equivalence intertwining `σ` and `τ`. -/
private noncomputable def foldedIndicesEquivOfIntertwine (e : P.Equiv P₂)
    (hσ : ∀ i, e.indexEquiv (σ.indexEquiv i) = τ.indexEquiv (e.indexEquiv i)) :
    P.foldedIndices σ ≃ P₂.foldedIndices τ where
  toFun γ := ⟨e.weightMap (γ : M), by
    obtain ⟨i, hi⟩ := (mem_foldedIndices (P := P) (σ := σ)).mp γ.2
    exact (mem_foldedIndices (P := P₂) (σ := τ)).mpr
      ⟨e.indexEquiv i, by rw [← P.weightMap_orbitSum e hσ i, hi]⟩⟩
  invFun δ := ⟨(Equiv.symm P P₂ e).weightMap (δ : M₂), by
    obtain ⟨j, hj⟩ := (mem_foldedIndices (P := P₂) (σ := τ)).mp δ.2
    exact (mem_foldedIndices (P := P) (σ := σ)).mpr
      ⟨(Equiv.symm P P₂ e).indexEquiv j, by
        rw [← P₂.weightMap_orbitSum (Equiv.symm P P₂ e) (symm_indexEquiv_intertwine e hσ) j, hj]⟩⟩
  left_inv γ := Subtype.ext <| by
    dsimp only
    rw [Equiv.inv_weightMap, LinearEquiv.coe_coe, ← Equiv.weightEquiv_apply,
      e.weightEquiv.symm_apply_apply]
  right_inv δ := Subtype.ext <| by
    dsimp only
    rw [Equiv.inv_weightMap, LinearEquiv.coe_coe, ← Equiv.weightEquiv_apply,
      e.weightEquiv.apply_symm_apply]

variable [CharZero R] [IsDomain R] [P.IsRootSystem] [P₂.IsRootSystem]
  (F : P.OrbitSumRealization b σ) (G : P₂.OrbitSumRealization b₂ τ)

/-- A root-pairing equivalence `e : P.Equiv P₂` intertwining `σ` and `τ` on root indices restricts
to an equivalence between any orbit-sum realizations `F` of `(P, b, σ)` and `G` of
`(P₂, b₂, τ)`, carrying each fixed weight `x` to `e.weightMap x`. -/
noncomputable def equivOfIntertwine (e : P.Equiv P₂)
    (hσ : ∀ i, e.indexEquiv (σ.indexEquiv i) = τ.indexEquiv (e.indexEquiv i)) :
    F.pairing.Equiv G.pairing :=
  Equiv.mk' F.pairing G.pairing (fixedSubmoduleEquivOfIntertwine e hσ)
    (foldedIndicesEquivOfIntertwine e hσ) fun γ ↦ Subtype.ext <| by
      rw [G.coe_root]
      change e.weightMap (F.pairing.root γ : M) = e.weightMap (γ : M)
      rw [F.coe_root]

@[simp]
theorem coe_equivOfIntertwine_weightMap (e : P.Equiv P₂)
    (hσ : ∀ i, e.indexEquiv (σ.indexEquiv i) = τ.indexEquiv (e.indexEquiv i))
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    ((F.equivOfIntertwine G e hσ).weightMap x : M₂) = e.weightMap (x : M) :=
  (rfl)

@[simp]
theorem coe_equivOfIntertwine_indexEquiv (e : P.Equiv P₂)
    (hσ : ∀ i, e.indexEquiv (σ.indexEquiv i) = τ.indexEquiv (e.indexEquiv i))
    (γ : P.foldedIndices σ) :
    ((F.equivOfIntertwine G e hσ).indexEquiv γ : M₂) = e.weightMap (γ : M) :=
  (rfl)

@[simp]
theorem equivOfIntertwine_indexEquiv_toFoldedIndices (e : P.Equiv P₂)
    (hσ : ∀ i, e.indexEquiv (σ.indexEquiv i) = τ.indexEquiv (e.indexEquiv i)) (i : ι) :
    (F.equivOfIntertwine G e hσ).indexEquiv (P.toFoldedIndices σ i) =
      P₂.toFoldedIndices τ (e.indexEquiv i) :=
  Subtype.ext (P.weightMap_orbitSum e hσ i)

/-- If `e : P.Equiv P₂` intertwines `σ` and `τ` and maps `b.support` bijectively onto
`b₂.support`, then `F.equivOfIntertwine G e hσ` carries `F.base` to `G.base`. -/
theorem base_map_equivOfIntertwine (e : P.Equiv P₂)
    (hσ : ∀ i, e.indexEquiv (σ.indexEquiv i) = τ.indexEquiv (e.indexEquiv i))
    (hbase : ∀ i, i ∈ b.support ↔ e.indexEquiv i ∈ b₂.support) :
    F.base.map (F.equivOfIntertwine G e hσ) = G.base := by
  classical
  ext δ
  rw [Base.support_map_eq, Finset.mem_image, G.base_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨j, hj, hjγ⟩ := (F.base_eq γ).mp hγ
    refine ⟨e.indexEquiv j, (hbase j).mp hj, ?_⟩
    rw [← P.weightMap_orbitSum e hσ j, hjγ, coe_equivOfIntertwine_indexEquiv]
  · rintro ⟨k, hk, hkδ⟩
    set j := e.indexEquiv.symm k
    have hj : j ∈ b.support := (hbase j).mpr (by simpa [j] using hk)
    refine ⟨P.toFoldedIndices σ j, F.toFoldedIndices_mem_support hj, ?_⟩
    rw [F.equivOfIntertwine_indexEquiv_toFoldedIndices G e hσ j]
    apply Subtype.ext
    simpa [j] using hkδ

end Intertwine

end OrbitSumRealization

end Structure

end RootPairing
