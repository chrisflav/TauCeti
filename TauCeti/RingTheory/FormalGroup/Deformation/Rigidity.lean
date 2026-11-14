/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Deformation.Marked
public import TauCeti.RingTheory.FormalGroup.Rigidity

import TauCeti.RingTheory.FormalGroup.Frobenius.Factorization
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange
import TauCeti.RingTheory.PowerSeries.Coordinate.Lifting

/-!
# Rigidity of formal group deformations

By Lubin–Tate rigidity (`TauCeti.FormalGroupHom.eq_of_map_mk_eq`), a homomorphism out of a formal
group law whose multiplication by `n ∈ I` factors modulo `I` as `u(X ^ q)` (`q ≠ 0`) over an
`I`-adically Hausdorff ring is uniquely determined by its reduction modulo `I`. Specializing to
coordinate-change isomorphisms `FormalGroup.smulIso φ F` shows that the group of formal
coordinates acts freely on commutative lifts at finite height:

* Two formal coordinates with the same mod-`I` reduction that transport `F` to the same commutative
  formal group law (`φ • F = ψ • F`) are equal (`FormalGroup.eq_of_smul_eq_of_map_mk_eq`).
* Along a surjective local coefficient map `π : A →+* k` onto a field `k` of characteristic `p`
  whose kernel is adically Hausdorff in `A` (in particular over any `𝔪`-adically Hausdorff local
  ring `A`), the reduction kernel `(FormalCoordinate.map π).ker` acts freely on
  `FormalGroupLift π F₀` whenever `F₀` has finite height
  (`TauCeti.FormalGroupLift.smul_left_cancel_of_height_eq`), and the full coordinate group
  `FormalCoordinate A` acts freely on `MarkedFormalGroupLift π F₀`
  (`TauCeti.MarkedFormalGroupLift.smul_left_cancel_of_height_eq`).
* Consequently two lifts represent the same deformation class if and only if there exists a
  *unique* coordinate change carrying one to the other
  (`TauCeti.FormalGroupDeformation.existsUnique_smul_eq_of_height_eq` and
  `TauCeti.MarkedFormalGroupDeformation.existsUnique_smul_eq_of_height_eq`).

Stating the finite-height theorems for any surjective `IsLocalHom` `π : A →+* k` with
`IsHausdorff (RingHom.ker π) A`, before specializing to local rings `(A, 𝔪)`, makes them apply
directly both to complete local rings and to arbitrary Artinian quotients `R ⧸ (ker ρ) ^ (n + 1)`
without assuming `R` is local or Hausdorff.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*,
  Bull. Soc. Math. France 94 (1966).
-/

public section

open PowerSeries TauCeti

namespace FormalGroup

variable {A k : Type*} [CommRing A]

/-- If `A` is `I`-adically Hausdorff and `[n]_F ≡ u(X ^ q)` modulo `I` for `n ∈ I` and `q ≠ 0`,
two formal coordinates with the same mod-`I` reduction that carry the commutative law `F` to the
same formal group law are equal. -/
theorem eq_of_smul_eq_of_map_mk_eq (F : FormalGroup A) [F.IsComm] {I : Ideal A} [IsHausdorff I A]
    {n q : ℕ} (hq : q ≠ 0) (hn : (n : A) ∈ I) (u : FormalCoordinate A)
    (hF : (F.nsmulSeries n).map (Ideal.Quotient.mk I) =
      (expand q hq u.toPowerSeries).map (Ideal.Quotient.mk I))
    {φ ψ : FormalCoordinate A} (hsmul : φ • F = ψ • F)
    (hred : FormalCoordinate.map (Ideal.Quotient.mk I) φ =
      FormalCoordinate.map (Ideal.Quotient.mk I) ψ) :
    φ = ψ := by
  let f₁ : FormalGroupHom F (ψ • F) :=
    { toPowerSeries := φ.toPowerSeries
      zero_constantCoeff := φ.constantCoeff_toPowerSeries
      hom := by
        simpa only [smulIso_toHom_toPowerSeries, hsmul] using (F.smulIso φ).toHom.hom }
  have hred' : f₁.toPowerSeries.map (Ideal.Quotient.mk I) =
      (F.smulIso ψ).toHom.toPowerSeries.map (Ideal.Quotient.mk I) := by
    simpa only [smulIso_toHom_toPowerSeries, FormalCoordinate.toPowerSeries_map] using
      congrArg FormalCoordinate.toPowerSeries hred
  have hf : f₁ = (F.smulIso ψ).toHom :=
    f₁.eq_of_map_mk_eq (F.smulIso ψ).toHom hq hn u hF hred'
  exact FormalCoordinate.ext
    ((congrArg FormalGroupHom.toPowerSeries hf).trans (smulIso_toHom_toPowerSeries ψ F))

/-- Along a surjective local homomorphism `π : A →+* k` onto a field of characteristic `p` with
`IsHausdorff (RingHom.ker π) A`, two formal coordinates with the same reduction along `π` that
transport a commutative law `F` of finite height modulo `ker π` to the same law are equal. -/
theorem eq_of_smul_eq_of_height_eq (F : FormalGroup A) [F.IsComm] [Field k] {p : ℕ}
    [hp : Fact p.Prime] [CharP k p] {π : A →+* k} [IsLocalHom π] (hπ : Function.Surjective π)
    [IsHausdorff (RingHom.ker π) A] {h : ℕ} (hF : (F.map π).height p = h)
    {φ ψ : FormalCoordinate A} (hsmul : φ • F = ψ • F)
    (hred : FormalCoordinate.map π φ = FormalCoordinate.map π ψ) :
    φ = ψ := by
  set e := (F.map π).heightFrobeniusIso hF
  have he : (F.map π).nsmulSeries p =
      expand (p ^ h) (pow_ne_zero h hp.out.ne_zero) e.toHom.toPowerSeries := by
    rw [← FormalGroupHom.comp_iterateFrobeniusHom_toPowerSeries,
      heightFrobeniusIso_comp_iterateFrobeniusHom, nsmulHom_toPowerSeries]
  let u₀ : FormalCoordinate k :=
    { toPowerSeries := e.toHom.toPowerSeries
      constantCoeff_toPowerSeries := e.toHom.zero_constantCoeff
      isUnit_coeff_one := e.isUnit_coeff_one }
  obtain ⟨u, hu⟩ := FormalCoordinate.map_surjective_of_isLocalHom π hπ u₀
  have hp_mem : (p : A) ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hinj := PowerSeries.map_injective (RingHom.kerLift π) (RingHom.kerLift_injective π)
  have hcomp : (RingHom.kerLift π).comp (Ideal.Quotient.mk (RingHom.ker π)) = π :=
    RingHom.ext π.kerLift_mk
  have hF_mk : (F.nsmulSeries p).map (Ideal.Quotient.mk (RingHom.ker π)) =
      (expand (p ^ h) (pow_ne_zero h hp.out.ne_zero) u.toPowerSeries).map
        (Ideal.Quotient.mk (RingHom.ker π)) := by
    refine hinj ?_
    rw [← RingHom.comp_apply, ← PowerSeries.map_comp, ← RingHom.comp_apply, ← PowerSeries.map_comp,
      hcomp, map_nsmulSeries, he, map_expand, ← FormalCoordinate.toPowerSeries_map, hu]
  have hred_mk : FormalCoordinate.map (Ideal.Quotient.mk (RingHom.ker π)) φ =
      FormalCoordinate.map (Ideal.Quotient.mk (RingHom.ker π)) ψ := by
    apply FormalCoordinate.ext
    rw [FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_map]
    refine hinj ?_
    rw [← RingHom.comp_apply, ← PowerSeries.map_comp, ← RingHom.comp_apply, ← PowerSeries.map_comp,
      hcomp]
    simpa only [FormalCoordinate.toPowerSeries_map] using
      congrArg FormalCoordinate.toPowerSeries hred
  exact F.eq_of_smul_eq_of_map_mk_eq (pow_ne_zero h hp.out.ne_zero) hp_mem u hF_mk hsmul hred_mk

end FormalGroup

namespace TauCeti

section KerHausdorff

variable {A k : Type*} [CommRing A] [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {π : A →+* k} [IsLocalHom π] [IsHausdorff (RingHom.ker π) A] {F₀ : FormalGroup k}

/-- **Freeness of ⋆-coordinate changes on lifts.** Along a surjective local homomorphism
`π : A →+* k` with Hausdorff kernel, `(FormalCoordinate.map π).ker` acts freely on lifts of a
finite-height formal group law `F₀`. -/
theorem FormalGroupLift.smul_left_cancel_of_height_eq (hπ : Function.Surjective π)
    {h : ℕ} (hF₀ : F₀.height p = h) (F : FormalGroupLift π F₀)
    {φ ψ : (FormalCoordinate.map π).ker} (hsmul : φ • F = ψ • F) :
    φ = ψ := by
  apply Subtype.ext
  refine F.formalGroup.eq_of_smul_eq_of_height_eq hπ (F.map_eq.symm ▸ hF₀)
    (congrArg FormalGroupLift.formalGroup hsmul) ?_
  rw [MonoidHom.mem_ker.mp φ.property, MonoidHom.mem_ker.mp ψ.property]

/-- The only coordinate in `ker (map π)` fixing a lift of a finite-height law is `1`. -/
theorem FormalGroupLift.eq_one_of_smul_eq_self_of_height_eq (hπ : Function.Surjective π)
    {h : ℕ} (hF₀ : F₀.height p = h) (F : FormalGroupLift π F₀)
    {φ : (FormalCoordinate.map π).ker} (hsmul : φ • F = F) :
    φ = 1 :=
  F.smul_left_cancel_of_height_eq hπ hF₀ (hsmul.trans (one_smul _ F).symm)

/-- **Uniqueness of ⋆-isomorphisms between representatives of a deformation.** When two lifts of a
finite-height formal group law define the same deformation class, there is a unique coordinate in
`ker (map π)` transporting the first to the second. -/
theorem FormalGroupDeformation.existsUnique_smul_eq_of_height_eq (hπ : Function.Surjective π)
    {h : ℕ} (hF₀ : F₀.height p = h) {F G : FormalGroupLift π F₀}
    (heq : (⟦F⟧ : FormalGroupDeformation π F₀) = ⟦G⟧) :
    ∃! φ : (FormalCoordinate.map π).ker, φ • F = G := by
  obtain ⟨φ, hφ, hFG⟩ := (mk_eq_mk_iff F G).mp heq
  refine ⟨⟨φ, MonoidHom.mem_ker.mpr hφ⟩, FormalGroupLift.ext hFG, fun ψ hψ ↦ ?_⟩
  exact F.smul_left_cancel_of_height_eq hπ hF₀ (hψ.trans (FormalGroupLift.ext hFG).symm)

/-- **Freeness of coordinate changes on marked lifts.** Along a surjective local homomorphism
`π : A →+* k` with Hausdorff kernel, the full group `FormalCoordinate A` acts freely on marked
lifts of a finite-height formal group law `F₀`. -/
theorem MarkedFormalGroupLift.smul_left_cancel_of_height_eq (hπ : Function.Surjective π)
    {h : ℕ} (hF₀ : F₀.height p = h) (F : MarkedFormalGroupLift π F₀)
    {φ ψ : FormalCoordinate A} (hsmul : φ • F = ψ • F) :
    φ = ψ := by
  have hF_height : (F.formalGroup.map π).height p = h := by
    rw [← FormalGroup.height_smul F.marking, F.smul_map_eq, hF₀]
  have hmark := congrArg MarkedFormalGroupLift.marking hsmul
  simp only [marking_smul, mul_right_inj, inv_inj] at hmark
  exact F.formalGroup.eq_of_smul_eq_of_height_eq hπ hF_height
    (congrArg MarkedFormalGroupLift.formalGroup hsmul) hmark

/-- When two marked lifts of a finite-height formal group law define the same marked deformation,
there is a unique formal coordinate transporting the first marked lift to the second. -/
theorem MarkedFormalGroupDeformation.existsUnique_smul_eq_of_height_eq
    (hπ : Function.Surjective π) {h : ℕ} (hF₀ : F₀.height p = h)
    {F G : MarkedFormalGroupLift π F₀}
    (heq : (⟦F⟧ : MarkedFormalGroupDeformation π F₀) = ⟦G⟧) :
    ∃! φ : FormalCoordinate A, φ • F = G := by
  rw [eq_comm, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at heq
  obtain ⟨φ, hφ⟩ := heq
  exact ⟨φ, hφ, fun ψ hψ ↦ F.smul_left_cancel_of_height_eq hπ hF₀ (hψ.trans hφ.symm)⟩

end KerHausdorff

section LocalRing

open IsLocalRing

variable {A k : Type*} [CommRing A] [IsLocalRing A] [IsHausdorff (maximalIdeal A) A]
  [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {π : A →+* k} {F₀ : FormalGroup k}

/-- Over an `𝔪`-adically Hausdorff local ring `A` with surjective augmentation `π : A →+* k` onto
a field of characteristic `p`, `(FormalCoordinate.map π).ker` acts freely on lifts of a
finite-height formal group law `F₀`. -/
theorem FormalGroupLift.smul_left_cancel_of_isLocalRing (hπ : Function.Surjective π)
    {h : ℕ} (hF₀ : F₀.height p = h) (F : FormalGroupLift π F₀)
    {φ ψ : (FormalCoordinate.map π).ker} (hsmul : φ • F = ψ • F) :
    φ = ψ := by
  have : IsLocalHom π := .of_surjective π hπ
  have : IsHausdorff (RingHom.ker π) A := by rwa [ker_eq_maximalIdeal π hπ]
  exact F.smul_left_cancel_of_height_eq hπ hF₀ hsmul

/-- Over an `𝔪`-adically Hausdorff local ring `A` with surjective augmentation `π : A →+* k`, two
lifts of a finite-height law define the same deformation only via a unique coordinate in
`ker (map π)`. -/
theorem FormalGroupDeformation.existsUnique_smul_eq_of_isLocalRing (hπ : Function.Surjective π)
    {h : ℕ} (hF₀ : F₀.height p = h) {F G : FormalGroupLift π F₀}
    (heq : (⟦F⟧ : FormalGroupDeformation π F₀) = ⟦G⟧) :
    ∃! φ : (FormalCoordinate.map π).ker, φ • F = G := by
  have : IsLocalHom π := .of_surjective π hπ
  have : IsHausdorff (RingHom.ker π) A := by rwa [ker_eq_maximalIdeal π hπ]
  exact existsUnique_smul_eq_of_height_eq hπ hF₀ heq

/-- Over an `𝔪`-adically Hausdorff local ring `A` with surjective augmentation `π : A →+* k`,
`FormalCoordinate A` acts freely on marked lifts of a finite-height formal group law `F₀`. -/
theorem MarkedFormalGroupLift.smul_left_cancel_of_isLocalRing (hπ : Function.Surjective π)
    {h : ℕ} (hF₀ : F₀.height p = h) (F : MarkedFormalGroupLift π F₀)
    {φ ψ : FormalCoordinate A} (hsmul : φ • F = ψ • F) :
    φ = ψ := by
  have : IsLocalHom π := .of_surjective π hπ
  have : IsHausdorff (RingHom.ker π) A := by rwa [ker_eq_maximalIdeal π hπ]
  exact F.smul_left_cancel_of_height_eq hπ hF₀ hsmul

/-- Over an `𝔪`-adically Hausdorff local ring `A` with surjective augmentation `π : A →+* k`, two
marked lifts of a finite-height law define the same marked deformation only via a unique formal
coordinate. -/
theorem MarkedFormalGroupDeformation.existsUnique_smul_eq_of_isLocalRing
    (hπ : Function.Surjective π) {h : ℕ} (hF₀ : F₀.height p = h)
    {F G : MarkedFormalGroupLift π F₀}
    (heq : (⟦F⟧ : MarkedFormalGroupDeformation π F₀) = ⟦G⟧) :
    ∃! φ : FormalCoordinate A, φ • F = G := by
  have : IsLocalHom π := .of_surjective π hπ
  have : IsHausdorff (RingHom.ker π) A := by rwa [ker_eq_maximalIdeal π hπ]
  exact existsUnique_smul_eq_of_height_eq hπ hF₀ heq

end LocalRing

end TauCeti
