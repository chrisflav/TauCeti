/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Isotopy.Comp
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The full topological mapping class group

For a topological space `M`, the self-homeomorphisms isotopic to the identity through topological
embeddings (`TauCeti.Isotopic`) form a normal subgroup `TauCeti.isotopicToIdSubgroup M` of the
homeomorphism group `M ≃ₜ M`. The closure laws compose on the left: given isotopies `F_t` from
`f` to `id` and `G_t` from `g` to `id`, the homotopy `F_t ∘ g` followed by `G_t` joins `f ∘ g`
to `id`, `f⁻¹ ∘ F_t` joins `id` to `f⁻¹` without requiring `(t, x) ↦ F_t⁻¹ x` to be continuous,
and `h ∘ F_t ∘ h⁻¹` joins `h ∘ f ∘ h⁻¹` to `id`.

The quotient group `TauCeti.MappingClassGroupFull M := (M ≃ₜ M) ⧸ TauCeti.isotopicToIdSubgroup M`
is the full topological mapping class group of `M`: isotopy classes of self-homeomorphisms,
without fixing any boundary pointwise.

## Main definitions

* `TauCeti.isotopicToIdSubgroup M`: the normal subgroup of self-homeomorphisms of `M` isotopic to
  the identity.
* `TauCeti.MappingClassGroupFull M`: the full topological mapping class group `(M ≃ₜ M) ⧸ N`.
* `TauCeti.MappingClassGroupFull.mk`: the quotient homomorphism `M ≃ₜ M →* MappingClassGroupFull M`.
* `TauCeti.MappingClassGroupFull.lift`: the universal property for homomorphisms out of `M ≃ₜ M`
  vanishing on homeomorphisms isotopic to the identity.
* `TauCeti.MappingClassGroupFull.congr`: the group isomorphism induced by a homeomorphism.

## Main results

* `TauCeti.isotopicToIdSubgroup.normal`: `isotopicToIdSubgroup M` is normal in `M ≃ₜ M`.
* `TauCeti.AmbientIsotopy.finalHomeomorph_mem_isotopicToIdSubgroup`: the time-one homeomorphism of
  any ambient isotopy belongs to `isotopicToIdSubgroup M`.
* `TauCeti.MappingClassGroupFull.mk_eq_one_iff` and `mk_eq_mk_iff`: equality in
  `MappingClassGroupFull M` characterizes isotopy between self-homeomorphisms.

## References

* B. Farb and D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Section 2.1.
* D. B. A. Epstein, *Curves on 2-manifolds and isotopies*, Acta Math. 115 (1966), 83–107.
-/

public section

open scoped ContinuousMap

namespace TauCeti

section Subgroup

variable (M : Type*) [TopologicalSpace M]

/-- The subgroup of self-homeomorphisms of `M` isotopic to the identity through topological
embeddings. The group laws compose on the left so that no continuity of time-slice inverses
is needed. -/
def isotopicToIdSubgroup : Subgroup (M ≃ₜ M) where
  carrier := {f | Isotopic (f : C(M, M)) (ContinuousMap.id M)}
  one_mem' := Isotopic.refl _ Topology.IsEmbedding.id
  mul_mem' := by
    rintro f g hf hg
    have hfg : Isotopic ((f : C(M, M)).comp (g : C(M, M)))
        ((ContinuousMap.id M).comp (g : C(M, M))) :=
      hf.precomp_homeomorph g
    exact hfg.trans hg
  inv_mem' := by
    rintro f hf
    have hfi : Isotopic ((f.symm : C(M, M)).comp (f : C(M, M)))
        ((f.symm : C(M, M)).comp (ContinuousMap.id M)) :=
      hf.postcomp_homeomorph f.symm
    have hcomp : (f.symm : C(M, M)).comp (f : C(M, M)) = ContinuousMap.id M := by
      ext x; simp
    have hid : (f.symm : C(M, M)).comp (ContinuousMap.id M) = (f.symm : C(M, M)) := by
      ext x; simp
    rw [hcomp, hid] at hfi
    exact hfi.symm

/-- A self-homeomorphism belongs to `isotopicToIdSubgroup M` iff it is isotopic to `id`. -/
@[simp]
theorem mem_isotopicToIdSubgroup_iff {M : Type*} [TopologicalSpace M] {f : M ≃ₜ M} :
    f ∈ isotopicToIdSubgroup M ↔ Isotopic (f : C(M, M)) (ContinuousMap.id M) :=
  Iff.rfl

/-- Conjugation by any self-homeomorphism preserves isotopy to the identity. -/
instance isotopicToIdSubgroup.normal : (isotopicToIdSubgroup M).Normal where
  conj_mem f hf h := by
    change Isotopic ((h * f * h⁻¹ : M ≃ₜ M) : C(M, M)) (ContinuousMap.id M)
    have hf' : Isotopic (f : C(M, M)) (ContinuousMap.id M) := hf
    have hconj := (hf'.postcomp_homeomorph h).precomp_homeomorph h.symm
    have hl : ((h : C(M, M)).comp (f : C(M, M))).comp (h.symm : C(M, M)) =
        ((h * f * h⁻¹ : M ≃ₜ M) : C(M, M)) := by
      ext x; simp [mul_assoc]
    have hr : ((h : C(M, M)).comp (ContinuousMap.id M)).comp (h.symm : C(M, M)) =
        ContinuousMap.id M := by
      ext x; simp
    rwa [hl, hr] at hconj

end Subgroup

/-- The time-one homeomorphism of any ambient isotopy is isotopic to the identity. -/
theorem AmbientIsotopy.finalHomeomorph_mem_isotopicToIdSubgroup {M : Type*} [TopologicalSpace M]
    (Φ : AmbientIsotopy M) :
    Φ.finalHomeomorph ∈ isotopicToIdSubgroup M := by
  have hiso := (Φ.isotopic Topology.IsEmbedding.id (f := ContinuousMap.id M)).symm
  have hcoe : (Φ.finalHomeomorph : C(M, M)) = Φ.final.comp (ContinuousMap.id M) := by
    ext x; simp
  simpa [mem_isotopicToIdSubgroup_iff, hcoe] using hiso

variable (M : Type*) [TopologicalSpace M]

/-- The **full topological mapping class group** of `M`: self-homeomorphisms of `M` modulo those
isotopic to the identity through topological embeddings. -/
abbrev MappingClassGroupFull : Type _ :=
  (M ≃ₜ M) ⧸ isotopicToIdSubgroup M

namespace MappingClassGroupFull

variable {M}

/-- The quotient homomorphism sending a self-homeomorphism of `M` to its mapping class. -/
@[expose]
def mk (M : Type*) [TopologicalSpace M] : (M ≃ₜ M) →* MappingClassGroupFull M :=
  QuotientGroup.mk' _

/-- Every mapping class in `MappingClassGroupFull M` is represented by a self-homeomorphism. -/
theorem mk_surjective : Function.Surjective (mk M) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of `MappingClassGroupFull.mk` is `isotopicToIdSubgroup M`. -/
@[simp]
theorem ker_mk : (mk M).ker = isotopicToIdSubgroup M :=
  QuotientGroup.ker_mk' _

/-- A self-homeomorphism represents the identity mapping class if and only if it is isotopic to
the identity. -/
theorem mk_eq_one_iff {f : M ≃ₜ M} :
    mk M f = 1 ↔ Isotopic (f : C(M, M)) (ContinuousMap.id M) := by
  rw [← MonoidHom.mem_ker, ker_mk, mem_isotopicToIdSubgroup_iff]

/-- Two self-homeomorphisms represent the same mapping class if and only if they are isotopic. -/
theorem mk_eq_mk_iff {f g : M ≃ₜ M} :
    mk M f = mk M g ↔ Isotopic (f : C(M, M)) (g : C(M, M)) := by
  rw [← div_eq_one, ← map_div, mk_eq_one_iff, div_eq_mul_inv]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hg := h.precomp_homeomorph g
    have hl : ((f * g⁻¹ : M ≃ₜ M) : C(M, M)).comp (g : C(M, M)) = (f : C(M, M)) := by
      ext x; simp
    have hr : (ContinuousMap.id M).comp (g : C(M, M)) = (g : C(M, M)) := by
      ext x; simp
    rwa [hl, hr] at hg
  · have hg := h.precomp_homeomorph g.symm
    have hl : (f : C(M, M)).comp (g.symm : C(M, M)) = ((f * g⁻¹ : M ≃ₜ M) : C(M, M)) := by
      ext x; simp
    have hr : (g : C(M, M)).comp (g.symm : C(M, M)) = ContinuousMap.id M := by
      ext x; simp
    rwa [hl, hr] at hg

/-- The time-one homeomorphism of any ambient isotopy represents the identity mapping class. -/
@[simp]
theorem mk_finalHomeomorph_eq_one (Φ : AmbientIsotopy M) :
    mk M Φ.finalHomeomorph = 1 :=
  (QuotientGroup.eq_one_iff _).mpr Φ.finalHomeomorph_mem_isotopicToIdSubgroup

section Lift

variable {G : Type*} [Group G]

/-- A homomorphism out of `M ≃ₜ M` that is trivial on self-homeomorphisms isotopic to the
identity descends to `MappingClassGroupFull M`. -/
def lift (φ : (M ≃ₜ M) →* G)
    (hφ : ∀ f : M ≃ₜ M, Isotopic (f : C(M, M)) (ContinuousMap.id M) → φ f = 1) :
    MappingClassGroupFull M →* G :=
  QuotientGroup.lift _ φ hφ

/-- The descended homomorphism sends the class of `f` to `φ f`. -/
@[simp]
theorem lift_mk (φ : (M ≃ₜ M) →* G)
    (hφ : ∀ f : M ≃ₜ M, Isotopic (f : C(M, M)) (ContinuousMap.id M) → φ f = 1) (f : M ≃ₜ M) :
    lift φ hφ (mk M f) = φ f :=
  QuotientGroup.lift_mk' _ _ f

/-- The descended homomorphism composed with `mk` equals `φ`. -/
@[simp]
theorem lift_comp_mk (φ : (M ≃ₜ M) →* G)
    (hφ : ∀ f : M ≃ₜ M, Isotopic (f : C(M, M)) (ContinuousMap.id M) → φ f = 1) :
    (lift φ hφ).comp (mk M) = φ :=
  MonoidHom.ext (lift_mk φ hφ)

/-- Two homomorphisms out of `MappingClassGroupFull M` agreeing on every class `mk M f` are
equal. -/
@[ext]
theorem hom_ext {ψ ψ' : MappingClassGroupFull M →* G}
    (h : ψ.comp (mk M) = ψ'.comp (mk M)) : ψ = ψ' :=
  QuotientGroup.monoidHom_ext _ h

/-- The descended homomorphism is unique among homomorphisms whose composite with `mk` is `φ`. -/
theorem eq_lift_iff {φ : (M ≃ₜ M) →* G}
    {hφ : ∀ f : M ≃ₜ M, Isotopic (f : C(M, M)) (ContinuousMap.id M) → φ f = 1}
    {ψ : MappingClassGroupFull M →* G} :
    ψ = lift φ hφ ↔ ψ.comp (mk M) = φ :=
  ⟨fun h => h ▸ lift_comp_mk φ hφ, fun h => hom_ext (h.trans (lift_comp_mk φ hφ).symm)⟩

end Lift

section Congr

variable {N : Type*} [TopologicalSpace N]

private noncomputable def homeomorphCongr (e : M ≃ₜ N) : (M ≃ₜ M) ≃* (N ≃ₜ N) where
  toFun f := e.symm.trans (f.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv f := by ext x; simp
  right_inv g := by ext y; simp
  map_mul' f g := by ext y; simp

/-- A homeomorphism `e : M ≃ₜ N` induces an isomorphism of full topological mapping class
groups by conjugation. -/
noncomputable def congr (e : M ≃ₜ N) :
    MappingClassGroupFull M ≃* MappingClassGroupFull N :=
  QuotientGroup.congr (isotopicToIdSubgroup M) (isotopicToIdSubgroup N) (homeomorphCongr e) <| by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.coe_ofClass, mem_isotopicToIdSubgroup_iff]
    refine ⟨?_, fun hg => ⟨homeomorphCongr e.symm g, ?_, ?_⟩⟩
    · rintro ⟨f, hf, rfl⟩
      have h' := (hf.postcomp_homeomorph e).precomp_homeomorph e.symm
      have hl : ((e : C(M, N)).comp (f : C(M, M))).comp (e.symm : C(N, M)) =
          ((homeomorphCongr e f : N ≃ₜ N) : C(N, N)) := by
        ext y; rfl
      have hr : ((e : C(M, N)).comp (ContinuousMap.id M)).comp (e.symm : C(N, M)) =
          ContinuousMap.id N := by
        ext y; simp
      rwa [hl, hr] at h'
    · have h' := (hg.postcomp_homeomorph e.symm).precomp_homeomorph e
      have hl : ((e.symm : C(N, M)).comp (g : C(N, N))).comp (e : C(M, N)) =
          ((homeomorphCongr e.symm g : M ≃ₜ M) : C(M, M)) := by
        ext x; rfl
      have hr : ((e.symm : C(N, M)).comp (ContinuousMap.id N)).comp (e : C(M, N)) =
          ContinuousMap.id M := by
        ext x; simp
      rwa [hl, hr] at h'
    · ext y; simp [homeomorphCongr]

/-- Transporting a mapping class along `e` conjugates its representative homeomorphism. -/
@[simp]
theorem congr_mk (e : M ≃ₜ N) (f : M ≃ₜ M) :
    congr e (mk M f) = mk N (e.symm.trans (f.trans e)) := by
  simp [congr, mk, homeomorphCongr]

end Congr

end MappingClassGroupFull

end TauCeti
