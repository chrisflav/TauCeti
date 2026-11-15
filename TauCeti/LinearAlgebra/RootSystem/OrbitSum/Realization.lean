/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.EquivComp
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Orbit-sum realizations of folded root systems

Let `P` be a finite root pairing, `b` a base of `P`, and `σ` an automorphism of `P`. The distinct
orbit sums of `σ` lie in `LinearMap.fixedSubmodule σ.weightMap` and are indexed by
`RootPairing.foldedIndices P σ`. An **orbit-sum realization** (`RootPairing.OrbitSumRealization`)
is a reduced crystallographic root system on that fixed space and its linear dual, paired by
evaluation, with roots the orbit sums and chosen base the simple-orbit sums. Not every `σ : P.Aut`
admits one (`σ = s_α` on `A₁` has orbit sum `0`), and non-orthogonal orbits can share an orbit sum
(`{α₁, α₂}` and `{α₁ + α₂}` under `A₂` reversal). Over a characteristic-zero domain it is unique,
and linear independence of `b.support` forces `σ`-fixed combinations of simple roots to be constant
on `σ`-orbits, identifying positivity, the positive root cone, and the root lattice.

## Main definitions

* `RootPairing.foldedIndex`: the orbit sum of `i` packaged in `P.foldedIndices σ`.
* `RootPairing.OrbitSumRealization`: a reduced crystallographic root system on the fixed space of
  `σ` and its dual whose roots are the orbit sums and whose simple roots are the simple-orbit sums.
* `RootPairing.OrbitSumRealization.equivOne` and `RootPairing.OrbitSumRealization.map`: trivial-fold
  equivalence (`σ = 1`) and transport along equivalences of root pairings.

## Main results

* `RootPairing.OrbitSumRealization.instSubsingleton`: uniqueness over a characteristic-zero domain.
* `RootPairing.orbitSum_eq_orbitSum_iff_of_mem_support`: over a nontrivial ring, simple roots have
  equal orbit sums if and only if they lie in the same `σ`-orbit.
* `RootPairing.OrbitSumRealization.mem_posRootCone_iff`,
  `RootPairing.OrbitSumRealization.isPos_foldedIndex_iff`, and
  `RootPairing.OrbitSumRealization.mem_span_int_range_root_iff`: cone, positivity, and root-lattice
  compatibility on the fixed space.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, §2.
-/

public section

namespace RootPairing

open Finset Set Submodule TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-! ### Packaged folded indices and simple orbits -/

section FoldedIndex

variable (P : RootPairing ι R M N) [Finite ι] (σ : P.Aut)

/-- The orbit sum of `i` under `σ`, packaged as an element of `P.foldedIndices σ`. -/
noncomputable def foldedIndex (i : ι) : P.foldedIndices σ :=
  ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩

@[simp]
theorem coe_foldedIndex (i : ι) : (P.foldedIndex σ i : M) = P.orbitSum σ i := by rw [foldedIndex]

@[simp]
theorem foldedIndex_indexEquiv (i : ι) :
    P.foldedIndex σ (σ.indexEquiv i) = P.foldedIndex σ i :=
  Subtype.ext (P.orbitSum_indexEquiv σ i)

theorem foldedIndex_surjective : Function.Surjective (P.foldedIndex σ) := fun β ↦
  let ⟨i, hi⟩ := mem_foldedIndices.mp β.2; ⟨i, Subtype.ext hi⟩

theorem foldedIndex_reflectionPerm_self (i : ι) :
    (P.foldedIndex σ (P.reflectionPerm i i) : M) = -(P.foldedIndex σ i : M) :=
  P.orbitSum_reflectionPerm_self σ i

variable {P σ}

theorem foldedIndex_eq_of_mem {i j : ι} (h : j ∈ P.orbitIndices σ i) :
    P.foldedIndex σ j = P.foldedIndex σ i :=
  Subtype.ext (orbitSum_eq_of_mem h)

end FoldedIndex

section SimpleOrbits

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
include hσ

omit [Finite ι] in
/-- When `σ` maps `b.support` into itself, membership in `b.support` is invariant under `σ`. -/
theorem Base.indexEquiv_mem_support_iff {i : ι} : σ.indexEquiv i ∈ b.support ↔ i ∈ b.support := by
  classical
  refine ⟨fun hi ↦ ?_, hσ i⟩
  rw [← b.map_eq_of_forall_mem_support hσ, b.support_map_eq, Finset.mem_image] at hi
  obtain ⟨j, hj, hji⟩ := hi
  exact σ.indexEquiv.injective hji ▸ hj

/-- The `σ`-orbit of any simple root of `b` is contained in `b.support`. -/
theorem orbitIndices_subset_support {i : ι} (hi : i ∈ b.support) :
    P.orbitIndices σ i ⊆ b.support := fun _ hj ↦
  (Iff.of_eq ((mem_orbitIndices.mp hj).apply_eq_of_apply_eq (f := (· ∈ b.support)) fun _ ↦
    propext (b.indexEquiv_mem_support_iff hσ))).mp hi

/-- Over a nontrivial ring, two simple roots have the same orbit sum if and only if they belong to
the same `σ`-orbit. -/
theorem orbitSum_eq_orbitSum_iff_of_mem_support [Nontrivial R] {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.orbitSum σ i = P.orbitSum σ j ↔ j ∈ P.orbitIndices σ i := by
  refine ⟨fun heq ↦ ?_, fun hmem ↦ (orbitSum_eq_of_mem hmem).symm⟩
  by_contra hnot
  classical
  let s := P.orbitIndices σ i ∪ P.orbitIndices σ j
  have hs : (s : Set ι) ⊆ b.support := by
    rw [Finset.coe_union]; exact Set.union_subset
      (orbitIndices_subset_support hσ hi) (orbitIndices_subset_support hσ hj)
  let c : ι → R := fun k ↦
    (if k ∈ P.orbitIndices σ i then 1 else 0) - if k ∈ P.orbitIndices σ j then 1 else 0
  have hzero : ∑ k ∈ s, c k • P.root k = 0 := by
    simp_rw [s, c, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_mem, Finset.union_inter_cancel_left, Finset.union_inter_cancel_right,
      ← orbitSum_def, heq, sub_self]
  have hcj := linearIndepOn_iff'.mp b.linearIndepOn_root s c hs hzero j
    (Finset.mem_union_right _ (self_mem_orbitIndices P σ j))
  simp only [c, hnot, self_mem_orbitIndices, ↓reduceIte, zero_sub, neg_eq_zero] at hcj
  exact one_ne_zero hcj

/-- In `b.support`, the fiber of `P.foldedIndex σ` through a simple root `i` is
`P.orbitIndices σ i`. -/
theorem filter_foldedIndex_eq_orbitIndices [Nontrivial R] [DecidableEq (P.foldedIndices σ)]
    {i : ι} (hi : i ∈ b.support) :
    b.support.filter (fun k ↦ P.foldedIndex σ k = P.foldedIndex σ i) = P.orbitIndices σ i := by
  ext k; simp only [Finset.mem_filter, Subtype.ext_iff, coe_foldedIndex]
  exact ⟨fun ⟨hk, hki⟩ ↦ (orbitSum_eq_orbitSum_iff_of_mem_support hσ hi hk).mp hki.symm,
    fun hk ↦ ⟨orbitIndices_subset_support hσ hi hk, orbitSum_eq_of_mem hk⟩⟩

/-- If a `σ`-fixed weight is written as an `R`-linear combination of `b.support`, its coefficients
are constant along every `σ`-orbit in `b.support`. -/
theorem eq_of_mem_orbitIndices_of_sum_smul_root_eq {c : ι → R} {x : M}
    (hx : σ.weightMap x = x) (hc : x = ∑ k ∈ b.support, c k • P.root k) {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ P.orbitIndices σ i) : c j = c i := by
  have hbij : ∑ k ∈ b.support, c k • P.root (σ.indexEquiv k) =
      ∑ l ∈ b.support, c (σ.indexEquiv.symm l) • P.root l :=
    Finset.sum_equiv σ.indexEquiv (fun k ↦ ⟨hσ k, (b.indexEquiv_mem_support_iff hσ).mp⟩)
      fun k _ ↦ by rw [σ.indexEquiv.symm_apply_apply]
  have hdiff : ∑ l ∈ b.support, (c (σ.indexEquiv.symm l) - c l) • P.root l = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← hbij, sub_eq_zero]
    rw [← hc, ← hx, hc, map_sum]
    exact (Finset.sum_congr rfl fun k _ ↦ by
      rw [map_smul, Hom.root_weightMap_apply P P k σ.toHom]).symm
  obtain ⟨n, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hj
  clear hj
  induction n with
  | zero => rfl
  | succ m ih =>
    have hzk := linearIndepOn_iff'.mp b.linearIndepOn_root b.support _ subset_rfl hdiff _
      (hσ _ (orbitIndices_subset_support hσ hi (mem_orbitIndices_iff_exists_pow.mpr ⟨m, rfl⟩)))
    rw [σ.indexEquiv.symm_apply_apply, sub_eq_zero] at hzk
    rw [pow_succ', Equiv.Perm.mul_apply, ← hzk, ih]

/-- Any combination of `b.support` with coefficients constant along `σ`-orbits rewrites as a
combination of the simple-orbit sums `b.support.image (P.foldedIndex σ)`. -/
theorem exists_sum_image_foldedIndex_smul_eq {S : Type*} [Semiring S] [Module S M] [Nontrivial R]
    [DecidableEq (P.foldedIndices σ)] {c : ι → S}
    (hconst : ∀ {i j : ι}, i ∈ b.support → j ∈ P.orbitIndices σ i → c j = c i) :
    ∃ d : P.foldedIndices σ → S,
      ∑ k ∈ b.support, c k • P.root k =
        ∑ β ∈ b.support.image (P.foldedIndex σ), d β • (β : M) := by
  refine ⟨fun β ↦ if h : ∃ i ∈ b.support, P.foldedIndex σ i = β then c h.choose else 0, ?_⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := P.foldedIndex σ)
    (fun i hi ↦ Finset.mem_image_of_mem _ hi)]
  refine Finset.sum_congr rfl fun β hβ ↦ ?_
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hβ
  have hex : ∃ i ∈ b.support, P.foldedIndex σ i = P.foldedIndex σ i₀ := ⟨i₀, hi₀, rfl⟩
  have hc₀ : c hex.choose = c i₀ := hconst hi₀
    ((orbitSum_eq_orbitSum_iff_of_mem_support hσ hi₀ hex.choose_spec.1).mp
      (congrArg Subtype.val hex.choose_spec.2).symm)
  rw [filter_foldedIndex_eq_orbitIndices hσ hi₀, coe_foldedIndex, orbitSum_def]
  simp only [hex, ↓reduceDIte, hc₀, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k hk ↦ by rw [hconst hi₀ hk]

/-- For an automorphism permuting `b.support`, an orbit sum lies in the positive root cone if and
only if its representative root is positive. -/
theorem orbitSum_mem_posRootCone_iff [CharZero R] {i : ι} :
    P.orbitSum σ i ∈ posRootCone P b ↔ b.IsPos i := by
  refine ⟨fun hmem ↦ ?_, orbitSum_mem_posRootCone hσ⟩
  by_contra hni
  have hneg : -P.orbitSum σ i ∈ posRootCone P b := P.orbitSum_reflectionPerm_self σ i ▸
    orbitSum_mem_posRootCone hσ
      ((isPos_reflectionPerm_self_iff_mem_negRoots P b i).mpr ((mem_negRoots P b i).mpr hni))
  exact orbitSum_ne_zero hσ i
    (eq_zero_of_add_eq_zero_of_mem_posRootCone P b hmem hneg (add_neg_cancel _))

end SimpleOrbits

/-! ### Orbit-sum realizations -/

/-- An **orbit-sum realization** of the folding of `(P, b)` by `σ`: a reduced crystallographic root
system on `LinearMap.fixedSubmodule σ.weightMap` and its linear dual, paired by evaluation, whose
roots are the orbit sums `P.foldedIndices σ` and whose simple roots are the orbit sums of the
simple roots of `b`. -/
structure OrbitSumRealization (P : RootPairing ι R M N) [Finite ι] (b : P.Base) (σ : P.Aut) where
  /-- The root pairing on the fixed space and its dual, indexed by the distinct orbit sums. -/
  pairing : RootPairing (P.foldedIndices σ) R
    (LinearMap.fixedSubmodule σ.weightMap)
    (Module.Dual R (LinearMap.fixedSubmodule σ.weightMap))
  /-- The base of the folded root pairing formed by the orbit sums of `b.support`. -/
  base : pairing.Base
  /-- The folded roots and coroots span the fixed space and its dual. -/
  rootSystem : pairing.IsRootSystem
  /-- The folded root pairing is reduced. -/
  reduced : pairing.IsReduced
  /-- The folded root pairing is crystallographic. -/
  crystallographic : pairing.IsCrystallographic
  /-- The pairing map is evaluation of dual functionals on the fixed space. -/
  evaluation (x : LinearMap.fixedSubmodule σ.weightMap)
      (f : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)) :
    pairing.toLinearMap x f = f x
  /-- Each folded root vector is the orbit sum indexing it. -/
  root_eq (β : P.foldedIndices σ) : (pairing.root β : M) = β
  /-- The simple folded roots are the orbit sums of the simple roots of `b`. -/
  base_eq (β : P.foldedIndices σ) :
    β ∈ base.support ↔ ∃ i ∈ b.support, P.orbitSum σ i = β

attribute [instance] OrbitSumRealization.rootSystem OrbitSumRealization.reduced
  OrbitSumRealization.crystallographic

namespace OrbitSumRealization

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}

section Basic

variable (F : P.OrbitSumRealization b σ)

@[simp]
theorem toLinearMap_apply (x : LinearMap.fixedSubmodule σ.weightMap)
    (f : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)) :
    F.pairing.toLinearMap x f = f x :=
  F.evaluation x f

theorem toLinearMap_eq : F.pairing.toLinearMap = LinearMap.id.flip :=
  LinearMap.ext₂ F.evaluation

theorem coroot'_eq_coroot (β : P.foldedIndices σ) :
    F.pairing.coroot' β = F.pairing.coroot β :=
  LinearMap.ext fun x ↦ F.evaluation x (F.pairing.coroot β)

@[simp]
theorem coe_root (β : P.foldedIndices σ) : (F.pairing.root β : M) = (β : M) := F.root_eq β

theorem coe_root_foldedIndex (i : ι) :
    (F.pairing.root (P.foldedIndex σ i) : M) = P.orbitSum σ i :=
  F.root_eq (P.foldedIndex σ i)

@[simp]
theorem mem_support_base_iff (β : P.foldedIndices σ) :
    β ∈ F.base.support ↔ ∃ i ∈ b.support, P.orbitSum σ i = (β : M) :=
  F.base_eq β

theorem foldedIndex_mem_support_base {i : ι} (hi : i ∈ b.support) :
    P.foldedIndex σ i ∈ F.base.support :=
  (F.base_eq _).mpr ⟨i, hi, rfl⟩

theorem support_base_eq [DecidableEq (P.foldedIndices σ)] :
    F.base.support = b.support.image (P.foldedIndex σ) := by
  ext β; simp only [F.base_eq, Finset.mem_image, Subtype.ext_iff, coe_foldedIndex]

end Basic

/-- Over a characteristic-zero integral domain, an orbit-sum realization is uniquely determined by
`(P, b, σ)`: its pairing map is evaluation, its roots are the orbit sums, and its base support is
fixed by `base_eq`. -/
instance instSubsingleton [CharZero R] [IsDomain R] :
    Subsingleton (P.OrbitSumRealization b σ) where
  allEq := fun ⟨p₁, b₁, _, _, _, ev₁, rt₁, bs₁⟩ ⟨p₂, b₂, _, _, _, ev₂, rt₂, bs₂⟩ ↦ by
    obtain rfl : p₁ = p₂ := RootPairing.IsRootSystem.ext
      (LinearMap.ext₂ fun x f ↦ (ev₁ x f).trans (ev₂ x f).symm)
      (by ext β : 1; exact Subtype.ext ((rt₁ β).trans (rt₂ β).symm))
    obtain rfl : b₁ = b₂ := Base.ext (Finset.ext fun β ↦ (bs₁ β).trans (bs₂ β).symm)
    rfl

/-! ### Positive root cone, root lattice, and positivity -/

section Positivity

variable (F : P.OrbitSumRealization b σ) [CharZero R]
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
include hσ

/-- A `σ`-fixed vector lies in the positive root cone of `(F.pairing, F.base)` if and only if its
underlying vector in `M` lies in `posRootCone P b`. -/
theorem mem_posRootCone_iff {x : LinearMap.fixedSubmodule σ.weightMap} :
    x ∈ posRootCone F.pairing F.base ↔ (x : M) ∈ posRootCone P b := by
  classical
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨d, rfl⟩ := (mem_posRootCone F.pairing F.base).mp hx
    rw [Submodule.coe_sum]
    refine sum_mem fun β hβ ↦ ?_
    obtain ⟨i, hi, hiβ⟩ := (F.base_eq β).mp hβ
    rw [Submodule.coe_smul_of_tower, F.coe_root, ← hiβ]
    exact nsmul_mem (orbitSum_mem_posRootCone hσ (b.isPos_of_mem_support hi)) (d β)
  · obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp hx
    obtain ⟨d, hd⟩ := exists_sum_image_foldedIndex_smul_eq hσ (c := c) fun {i j} hi hj ↦ by
      have hcsum : (x : M) = ∑ k ∈ b.support, (c k : R) • P.root k := by
        simp_rw [Nat.cast_smul_eq_nsmul]; exact hc
      exact Nat.cast_injective (eq_of_mem_orbitIndices_of_sum_smul_root_eq hσ
        (LinearMap.mem_fixedSubmodule_iff.mp x.2) hcsum hi hj)
    refine (mem_posRootCone F.pairing F.base).mpr ⟨d, Subtype.ext ?_⟩
    simp_rw [hc, hd, F.support_base_eq, Submodule.coe_sum, Submodule.coe_smul_of_tower, F.coe_root]

/-- A folded root `P.foldedIndex σ i` is positive for `F.base` if and only if `i` is positive for
`b`. -/
@[simp]
theorem isPos_foldedIndex_iff (i : ι) : F.base.IsPos (P.foldedIndex σ i) ↔ b.IsPos i := by
  rw [← mem_posRoots F.pairing F.base, mem_posRoots_iff_root_mem_posRootCone,
    F.mem_posRootCone_iff hσ, F.coe_root_foldedIndex, orbitSum_mem_posRootCone_iff hσ]

/-- A folded root `β` is positive for `F.base` if and only if it is the orbit sum of a positive
root of `(P, b)`. -/
theorem isPos_iff_exists_isPos (β : P.foldedIndices σ) :
    F.base.IsPos β ↔ ∃ i, b.IsPos i ∧ P.orbitSum σ i = (β : M) := by
  obtain ⟨i, rfl⟩ := P.foldedIndex_surjective σ β
  refine ⟨fun h ↦ ⟨i, (F.isPos_foldedIndex_iff hσ i).mp h, rfl⟩, fun ⟨j, hj, hjβ⟩ ↦ ?_⟩
  exact (Subtype.ext hjβ : P.foldedIndex σ j = P.foldedIndex σ i) ▸
    (F.isPos_foldedIndex_iff hσ j).mpr hj

/-- The root lattice of any orbit-sum realization is the intersection of the root lattice of `P`
with the fixed space of `σ`. -/
theorem mem_span_int_range_root_iff {x : LinearMap.fixedSubmodule σ.weightMap} :
    x ∈ span ℤ (range F.pairing.root) ↔ (x : M) ∈ span ℤ (range P.root) := by
  classical
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · induction hx using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨β, rfl⟩ := hy
      obtain ⟨i, hi⟩ := mem_foldedIndices.mp β.2
      rw [F.coe_root, ← hi, orbitSum_def]
      exact sum_mem fun j _ ↦ subset_span (mem_range_self j)
    | zero => exact zero_mem _
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | smul z _ _ h₁ => exact Submodule.smul_mem _ z h₁
  · have hsupp : (x : M) ∈ span ℤ (P.root '' b.support) :=
      span_le.mpr (by rintro _ ⟨i, rfl⟩; exact b.root_mem_span_int i) hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℤ).mp hsupp
    obtain ⟨d, hd⟩ := exists_sum_image_foldedIndex_smul_eq hσ (c := c) fun {i j} hi hj ↦ by
      have hcsum : (x : M) = ∑ k ∈ b.support, (c k : R) • P.root k := by
        simp_rw [Int.cast_smul_eq_zsmul]; exact hc.symm
      exact Int.cast_injective (eq_of_mem_orbitIndices_of_sum_smul_root_eq hσ
        (LinearMap.mem_fixedSubmodule_iff.mp x.2) hcsum hi hj)
    have hx_eq : x = ∑ β ∈ F.base.support, d β • F.pairing.root β := Subtype.ext <| by
      simp_rw [← hc, hd, F.support_base_eq, Submodule.coe_sum, Submodule.coe_smul_of_tower,
        F.coe_root]
    exact hx_eq ▸ sum_mem fun β _ ↦ Submodule.smul_mem _ (d β) (subset_span (mem_range_self β))

end Positivity

end OrbitSumRealization

/-! ### Trivial fold (`σ = 1`) and transport along equivalences -/

section One

variable (P : RootPairing ι R M N) [Finite ι]

/-- The bijection `ι ≃ P.foldedIndices 1` sending `i` to `P.root i`. -/
noncomputable def foldedIndexOneEquiv : ι ≃ P.foldedIndices 1 :=
  _root_.Equiv.ofBijective (P.foldedIndex 1)
    ⟨fun _ _ hij ↦ P.root.injective (by simpa [coe_foldedIndex] using congrArg Subtype.val hij),
      P.foldedIndex_surjective 1⟩

@[simp]
theorem coe_foldedIndexOneEquiv_apply (i : ι) :
    ((P.foldedIndexOneEquiv i : P.foldedIndices 1) : M) = P.root i := by
  rw [foldedIndexOneEquiv]; exact P.orbitSum_one i

variable {P} {b : P.Base} [P.IsRootSystem] [CharZero R] [IsDomain R] (F : P.OrbitSumRealization b 1)

/-- For `σ = 1`, any orbit-sum realization of `(P, b, 1)` is canonically equivalent to `(P, b)`. -/
noncomputable def OrbitSumRealization.equivOne : P.Equiv F.pairing :=
  Equiv.mk' P F.pairing
    { toFun := fun x ↦ ⟨x, LinearMap.mem_fixedSubmodule_iff.mpr rfl⟩, invFun := fun x ↦ x,
      map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
    P.foldedIndexOneEquiv
    fun i ↦ Subtype.ext (by rw [F.coe_root, coe_foldedIndexOneEquiv_apply]; rfl)

@[simp]
theorem OrbitSumRealization.equivOne_indexEquiv : F.equivOne.indexEquiv = P.foldedIndexOneEquiv :=
  by rw [OrbitSumRealization.equivOne]; rfl

theorem OrbitSumRealization.coe_equivOne_weightEquiv (x : M) :
    (F.equivOne.weightEquiv x : M) = x := by rw [OrbitSumRealization.equivOne]; rfl

@[simp]
theorem OrbitSumRealization.map_equivOne : b.map F.equivOne = F.base := by
  classical
  ext β; simp only [b.support_map_eq, F.mem_support_base_iff, Finset.mem_image, equivOne_indexEquiv,
    Subtype.ext_iff, coe_foldedIndexOneEquiv_apply, orbitSum_one]

end One

section Map

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}

/-- An equivalence `e : P.Equiv P₂` maps `LinearMap.fixedSubmodule σ.weightMap` linearly and
bijectively onto `LinearMap.fixedSubmodule (e.autCongr σ).weightMap`. -/
noncomputable def Equiv.fixedSubmoduleEquiv (e : P.Equiv P₂) (σ : P.Aut) :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[R]
      LinearMap.fixedSubmodule (e.autCongr σ).weightMap where
  toFun x := ⟨e.weightEquiv (x : M), LinearMap.mem_fixedSubmodule_iff.mpr <| by
    rw [← Equiv.weightEquiv_apply (e.autCongr σ), Equiv.weightEquiv_autCongr_apply,
      LinearEquiv.symm_apply_apply, Equiv.weightEquiv_apply σ,
      LinearMap.mem_fixedSubmodule_iff.mp x.2]⟩
  invFun y := ⟨e.weightEquiv.symm (y : M₂), LinearMap.mem_fixedSubmodule_iff.mpr <|
    e.weightEquiv.injective <| by
      rw [← Equiv.weightEquiv_apply σ, ← Equiv.weightEquiv_autCongr_apply e σ (y : M₂),
        Equiv.weightEquiv_apply (e.autCongr σ), LinearMap.mem_fixedSubmodule_iff.mp y.2,
        LinearEquiv.apply_symm_apply]⟩
  map_add' x y := Subtype.ext (map_add e.weightEquiv (x : M) (y : M))
  map_smul' r x := Subtype.ext (map_smul e.weightEquiv r (x : M))
  left_inv x := Subtype.ext (e.weightEquiv.symm_apply_apply (x : M))
  right_inv y := Subtype.ext (e.weightEquiv.apply_symm_apply (y : M₂))

@[simp]
theorem Equiv.coe_fixedSubmoduleEquiv_apply (e : P.Equiv P₂) (σ : P.Aut)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (e.fixedSubmoduleEquiv σ x : M₂) = e.weightEquiv x := by rw [Equiv.fixedSubmoduleEquiv]; rfl

variable [Finite ι] [Finite ι₂]

theorem Equiv.weightEquiv_orbitSum (e : P.Equiv P₂) (σ : P.Aut) (i : ι) :
    e.weightEquiv (P.orbitSum σ i) = P₂.orbitSum (e.autCongr σ) (e.indexEquiv i) :=
  (e.weightEquiv_apply _).trans <| weightMap_orbitSum e (σ := σ) (τ := e.autCongr σ)
    (fun _ ↦ by rw [Equiv.indexEquiv_autCongr_apply, _root_.Equiv.symm_apply_apply]) i

/-- An equivalence `e : P.Equiv P₂` identifies the orbit sums of `σ` with those of `e.autCongr σ`.
-/
noncomputable def Equiv.foldedIndicesEquiv (e : P.Equiv P₂) (σ : P.Aut) :
    P.foldedIndices σ ≃ P₂.foldedIndices (e.autCongr σ) where
  toFun β := ⟨e.weightEquiv (β : M), mem_foldedIndices.mpr <|
    let ⟨i, hi⟩ := mem_foldedIndices.mp β.2; ⟨e.indexEquiv i, by rw [← hi, e.weightEquiv_orbitSum]⟩⟩
  invFun γ := ⟨e.weightEquiv.symm (γ : M₂), mem_foldedIndices.mpr <|
    let ⟨j, hj⟩ := mem_foldedIndices.mp γ.2
    ⟨e.indexEquiv.symm j, e.weightEquiv.injective <| by
      rw [e.weightEquiv_orbitSum, e.indexEquiv.apply_symm_apply, e.weightEquiv.apply_symm_apply,
        hj]⟩⟩
  left_inv β := Subtype.ext (e.weightEquiv.symm_apply_apply (β : M))
  right_inv γ := Subtype.ext (e.weightEquiv.apply_symm_apply (γ : M₂))

@[simp]
theorem Equiv.coe_foldedIndicesEquiv_apply (e : P.Equiv P₂) (σ : P.Aut) (β : P.foldedIndices σ) :
    ((e.foldedIndicesEquiv σ β : P₂.foldedIndices (e.autCongr σ)) : M₂) = e.weightEquiv β := by
  rw [Equiv.foldedIndicesEquiv]; rfl

@[simp]
theorem Equiv.coe_foldedIndicesEquiv_symm_apply (e : P.Equiv P₂) (σ : P.Aut)
    (γ : P₂.foldedIndices (e.autCongr σ)) :
    (((e.foldedIndicesEquiv σ).symm γ : P.foldedIndices σ) : M) = e.weightEquiv.symm γ := by
  rw [Equiv.foldedIndicesEquiv]; rfl

@[simp]
theorem Equiv.foldedIndicesEquiv_foldedIndex (e : P.Equiv P₂) (σ : P.Aut) (i : ι) :
    e.foldedIndicesEquiv σ (P.foldedIndex σ i) = P₂.foldedIndex (e.autCongr σ) (e.indexEquiv i) :=
  Subtype.ext (by rw [Equiv.coe_foldedIndicesEquiv_apply, coe_foldedIndex, coe_foldedIndex,
    e.weightEquiv_orbitSum])

namespace OrbitSumRealization

variable {b : P.Base} {σ : P.Aut}

private theorem mapPairing_toLinearMap (e : P.Equiv P₂) (F : P.OrbitSumRealization b σ)
    (x : LinearMap.fixedSubmodule (e.autCongr σ).weightMap)
    (g : Module.Dual R (LinearMap.fixedSubmodule (e.autCongr σ).weightMap)) :
    (F.pairing.map (e.foldedIndicesEquiv σ) (e.fixedSubmoduleEquiv σ)
        (e.fixedSubmoduleEquiv σ).symm.dualMap).toLinearMap x g = g x := by
  simp [RootPairing.map]

private noncomputable def mapPairingEquiv (e : P.Equiv P₂) (F : P.OrbitSumRealization b σ) :
    F.pairing.Equiv
      (F.pairing.map (e.foldedIndicesEquiv σ) (e.fixedSubmoduleEquiv σ)
        (e.fixedSubmoduleEquiv σ).symm.dualMap) :=
  let fE := e.fixedSubmoduleEquiv σ
  let fN := fE.symm.dualMap
  { weightMap := fE.toLinearMap
    coweightMap := fN.symm.toLinearMap
    indexEquiv := e.foldedIndicesEquiv σ
    weight_coweight_transpose := by ext g x; simp [RootPairing.map, fN]
    root_weightMap := funext fun β ↦
      congrArg (fun k ↦ fE (F.pairing.root k)) ((e.foldedIndicesEquiv σ).symm_apply_apply β).symm
    coroot_coweightMap := funext fun γ ↦
      fN.symm_apply_apply (F.pairing.coroot ((e.foldedIndicesEquiv σ).symm γ))
    bijective_weightMap := fE.bijective
    bijective_coweightMap := fN.symm.bijective }

/-- Transport an orbit-sum realization along an equivalence `e : P.Equiv P₂`, conjugating `σ` to
`e.autCongr σ` and pushing `b` forward to `b.map e`. -/
noncomputable def map (e : P.Equiv P₂) (F : P.OrbitSumRealization b σ) :
    P₂.OrbitSumRealization (b.map e) (e.autCongr σ) :=
  let hEquiv := mapPairingEquiv e F
  { pairing := F.pairing.map (e.foldedIndicesEquiv σ) (e.fixedSubmoduleEquiv σ)
      (e.fixedSubmoduleEquiv σ).symm.dualMap
    base := F.base.map hEquiv
    rootSystem := inferInstance
    reduced := ⟨fun γ₁ γ₂ hdep ↦ by
      have hli := hEquiv.toHom.linearIndependent_root_indexEquiv_iff
        hEquiv.bijective_weightMap.injective
        ((e.foldedIndicesEquiv σ).symm γ₁) ((e.foldedIndicesEquiv σ).symm γ₂)
      dsimp only [hEquiv, mapPairingEquiv] at hli
      rw [(e.foldedIndicesEquiv σ).apply_symm_apply,
        (e.foldedIndicesEquiv σ).apply_symm_apply] at hli
      rcases IsReduced.eq_or_eq_neg (P := F.pairing) ((e.foldedIndicesEquiv σ).symm γ₁)
          ((e.foldedIndicesEquiv σ).symm γ₂) (hli.not.mp hdep) with h | h
      · exact .inl (congrArg (e.fixedSubmoduleEquiv σ) h)
      · exact .inr (by simp [RootPairing.map, h])⟩
    crystallographic := hEquiv.toHom.isValuedIn ℤ
    evaluation := mapPairing_toLinearMap e F
    root_eq := fun γ ↦ by simp [RootPairing.map]
    base_eq := fun γ ↦ by
      classical
      rw [F.base.support_map_eq, b.support_map_eq, Finset.mem_image]
      dsimp only [hEquiv, mapPairingEquiv]
      refine ⟨?_, ?_⟩
      · rintro ⟨β, hβ, rfl⟩
        obtain ⟨i, hi, hiβ⟩ := (F.base_eq β).mp hβ
        exact ⟨e.indexEquiv i, Finset.mem_image_of_mem _ hi, by
          rw [Equiv.coe_foldedIndicesEquiv_apply, ← hiβ, e.weightEquiv_orbitSum]⟩
      · rintro ⟨_, hj, hjγ⟩
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact ⟨P.foldedIndex σ i, F.foldedIndex_mem_support_base hi, by
          rw [e.foldedIndicesEquiv_foldedIndex]
          exact Subtype.ext ((P₂.coe_foldedIndex _ _).trans hjγ)⟩ }

/-- Over a characteristic-zero domain, any equivalence `e : P.Equiv P₂` intertwining `σ` and `τ`
induces an equivalence between orbit-sum realizations of `(P, b, σ)` and `(P₂, b₂, τ)`. -/
noncomputable def equivOfEquiv [CharZero R] [IsDomain R] (e : P.Equiv P₂) {b₂ : P₂.Base}
    {τ : P₂.Aut} (hσ : e.autCongr σ = τ)
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) :
    F₁.pairing.Equiv F₂.pairing := by
  cases hσ
  exact Equiv.mk' F₁.pairing F₂.pairing (e.fixedSubmoduleEquiv σ) (e.foldedIndicesEquiv σ)
    fun β ↦ Subtype.ext <| by simp

theorem map_equivOfEquiv [CharZero R] [IsDomain R] (e : P.Equiv P₂) {b₂ : P₂.Base}
    {τ : P₂.Aut} (hb : b.map e = b₂) (hσ : e.autCongr σ = τ)
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) :
    F₁.base.map (equivOfEquiv e hσ F₁ F₂) = F₂.base := by
  classical
  cases hb; cases hσ
  obtain rfl : F₂ = F₁.map e := Subsingleton.elim _ _
  ext γ
  rw [map, F₁.base.support_map_eq, F₁.base.support_map_eq, equivOfEquiv]
  rfl

end OrbitSumRealization

end Map

end RootPairing
