/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.Multilinear
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Continuous multilinear maps on localized modules

Let `R` be a commutative semiring, `S : Submonoid R` a submonoid, and `Rₛ` a localization of `R`
at `S`. Suppose `g i : M i →ₗ[R] Mₛ i` is a finite family of localization maps at `S` into
topological `Rₛ`-modules such that each `g i` is a topological inducing map with open image (for
instance, the inclusion of an open `R`-submodule). Then the unique `Rₛ`-multilinear extension
`IsLocalizedModule.extendMultilinear` of any continuous `R`-multilinear map
`f : ContinuousMultilinearMap R M N` is continuous.

The argument is local: near any tuple `v₀ : ∀ i, Mₛ i`, choose denominators `s i ∈ S` clearing
`v₀ i` into the open image `Set.range (g i)`. The set of tuples `v` with `s i • v i ∈ range (g i)`
for every `i` is an open neighbourhood of `v₀`, on which the extension factors continuously through
`f` and multiplication by `1 / ∏ i, s i`.

## Main definitions

* `IsLocalizedModule.extendContinuousMultilinear`: the unique continuous `Rₛ`-multilinear extension
  of a continuous `R`-multilinear map along a finite family of open-image inducing module
  localizations.

## Main results

* `IsLocalizedModule.continuous_extendMultilinear`: continuity of `extendMultilinear` when each
  `g i` is inducing with open range.
* `IsLocalizedModule.continuousMultilinearMap_ext`,
  `IsLocalizedModule.extendContinuousMultilinear_unique`, and
  `IsLocalizedModule.existsUnique_extendContinuousMultilinear`: uniqueness of the continuous
  `Rₛ`-multilinear extension.
-/

public section

noncomputable section

open Topology

namespace IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable (Rₛ : Type*) [CommSemiring Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
variable {ι : Type*} [Finite ι]
variable {M Mₛ : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (Mₛ i)]
variable [∀ i, Module R (M i)] [∀ i, Module R (Mₛ i)] [∀ i, Module Rₛ (Mₛ i)]
variable [∀ i, IsScalarTower R Rₛ (Mₛ i)]
variable (g : ∀ i, M i →ₗ[R] Mₛ i) [∀ i, IsLocalizedModule S (g i)]
variable {N : Type*} [AddCommMonoid N] [Module Rₛ N]
variable [∀ i, TopologicalSpace (Mₛ i)] [TopologicalSpace N]

include S in
/-- Two continuous `Rₛ`-multilinear maps from localized modules are equal if they agree on all
tuples in the images of the localization maps `g i`. -/
theorem continuousMultilinearMap_ext {F G : ContinuousMultilinearMap Rₛ Mₛ N}
    (h : ∀ m : ∀ i, M i, F (fun i => g i (m i)) = G (fun i => g i (m i))) : F = G :=
  ContinuousMultilinearMap.toMultilinearMap_injective <| multilinearMap_ext S Rₛ g h

variable [Module R N] [IsScalarTower R Rₛ N]
variable [∀ i, TopologicalSpace (M i)]
variable [∀ i, ContinuousConstSMul Rₛ (Mₛ i)] [ContinuousConstSMul Rₛ N]

/-- If each localization map `g i : M i →ₗ[R] Mₛ i` is inducing with open range, then the unique
`Rₛ`-multilinear extension of a continuous `R`-multilinear map `f` is continuous. -/
theorem continuous_extendMultilinear
    (hg_ind : ∀ i, IsInducing (g i)) (hg_open : ∀ i, IsOpen (Set.range (g i)))
    {f : (∀ i, M i) →ₘₗ[R] N} (hf : Continuous f) :
    Continuous (extendMultilinear S Rₛ g f) := by
  cases nonempty_fintype ι
  refine continuous_iff_continuousAt.2 fun v₀ => ?_
  choose rep hv₀ using fun i => IsLocalizedModule.surj S (g i) (v₀ i)
  let s : ι → S := fun i => (rep i).2
  let U : Set (∀ i, Mₛ i) :=
    Set.univ.pi fun i => (fun x : Mₛ i => algebraMap R Rₛ (s i : R) • x) ⁻¹' Set.range (g i)
  have hU_open : IsOpen U :=
    isOpen_set_pi Set.finite_univ fun i _ => (hg_open i).preimage (continuous_const_smul _)
  have hv₀_mem : v₀ ∈ U := fun i _ =>
    ⟨(rep i).1, by dsimp only; rw [← hv₀ i, Submonoid.smul_def, ← algebraMap_smul Rₛ]⟩
  have hcontOn : ContinuousOn (extendMultilinear S Rₛ g f) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    let ψ : U → ∀ i, M i := fun v i => Classical.choose (v.2 i trivial)
    have hψ_spec (v : U) (i : ι) : g i (ψ v i) = algebraMap R Rₛ (s i : R) • v.1 i :=
      Classical.choose_spec (v.2 i trivial)
    have hψ_cont : Continuous ψ := continuous_pi fun i =>
      (hg_ind i).continuous_iff.2 <| by
        simpa only [Function.comp_def, hψ_spec] using
          (continuous_const_smul (algebraMap R Rₛ (s i : R))).comp
            ((continuous_apply i).comp continuous_subtype_val)
    have heq : U.domRestrict (extendMultilinear S Rₛ g f) =
        fun v : U => IsLocalization.mk' Rₛ 1 (∏ i, s i) • f (ψ v) := by
      ext v
      exact extendMultilinear_apply_of_smul_eq S Rₛ g f fun i => by
        rw [Submonoid.smul_def, ← algebraMap_smul Rₛ (s i : R), ← hψ_spec v i]
    rw [heq]
    exact (hf.comp hψ_cont).const_smul _
  exact hcontOn.continuousAt (hU_open.mem_nhds hv₀_mem)

/-- The unique continuous `Rₛ`-multilinear extension of a continuous `R`-multilinear map along a
finite family of inducing localization maps with open range. -/
def extendContinuousMultilinear
    (hg_ind : ∀ i, IsInducing (g i)) (hg_open : ∀ i, IsOpen (Set.range (g i)))
    (f : ContinuousMultilinearMap R M N) : ContinuousMultilinearMap Rₛ Mₛ N where
  toMultilinearMap := extendMultilinear S Rₛ g f.toMultilinearMap
  cont := continuous_extendMultilinear S Rₛ g hg_ind hg_open f.cont

@[simp]
theorem toMultilinearMap_extendContinuousMultilinear
    (hg_ind : ∀ i, IsInducing (g i)) (hg_open : ∀ i, IsOpen (Set.range (g i)))
    (f : ContinuousMultilinearMap R M N) :
    (extendContinuousMultilinear S Rₛ g hg_ind hg_open f).toMultilinearMap =
      extendMultilinear S Rₛ g f.toMultilinearMap :=
  (rfl)

@[simp]
theorem extendContinuousMultilinear_apply_comp
    (hg_ind : ∀ i, IsInducing (g i)) (hg_open : ∀ i, IsOpen (Set.range (g i)))
    (f : ContinuousMultilinearMap R M N) (m : ∀ i, M i) :
    extendContinuousMultilinear S Rₛ g hg_ind hg_open f (fun i => g i (m i)) = f m :=
  extendMultilinear_apply_comp S Rₛ g f.toMultilinearMap m

/-- Any continuous `Rₛ`-multilinear map extending `f` along `g` equals
`extendContinuousMultilinear`. -/
theorem extendContinuousMultilinear_unique
    (hg_ind : ∀ i, IsInducing (g i)) (hg_open : ∀ i, IsOpen (Set.range (g i)))
    (f : ContinuousMultilinearMap R M N) {F : ContinuousMultilinearMap Rₛ Mₛ N}
    (h : ∀ m : ∀ i, M i, F (fun i => g i (m i)) = f m) :
    F = extendContinuousMultilinear S Rₛ g hg_ind hg_open f :=
  continuousMultilinearMap_ext S Rₛ g fun m => by
    rw [h, extendContinuousMultilinear_apply_comp]

include S in
/-- Every continuous `R`-multilinear map on a finite family of open-image inducing module
localizations extends uniquely to a continuous `Rₛ`-multilinear map. -/
theorem existsUnique_extendContinuousMultilinear
    (hg_ind : ∀ i, IsInducing (g i)) (hg_open : ∀ i, IsOpen (Set.range (g i)))
    (f : ContinuousMultilinearMap R M N) :
    ∃! F : ContinuousMultilinearMap Rₛ Mₛ N,
      ∀ m : ∀ i, M i, F (fun i => g i (m i)) = f m :=
  ⟨extendContinuousMultilinear S Rₛ g hg_ind hg_open f,
    extendContinuousMultilinear_apply_comp S Rₛ g hg_ind hg_open f,
    fun _ h => extendContinuousMultilinear_unique S Rₛ g hg_ind hg_open f h⟩

end IsLocalizedModule
