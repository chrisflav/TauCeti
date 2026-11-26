/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Deformation.Universal
-- Proof-only: lifting special-fibre formal coordinates along surjective local homomorphisms.
import TauCeti.RingTheory.PowerSeries.Coordinate.Lifting

/-!
# Automorphism group action on Lubin–Tate universal deformation rings

Let `k` be a field of characteristic `p > 0`, `F₀` a commutative formal group law of finite height
`h` over `k`, and `(R, ρ)` a complete Noetherian local ring with surjective local residue map
`ρ : R →+* k`. Given any universal deformation `Γ` of `F₀` over `R⟦t₁, …, t_{h-1}⟧`, every
special-fibre automorphism `u₀ ∈ MulAction.stabilizer (FormalCoordinate k) F₀` lifts to a unique
local `R`-algebra automorphism `FormalGroup.liftAut u₀` of `R⟦t₁, …, t_{h-1}⟧` together with a
unique formal group isomorphism `Γ.map (liftAut u₀) ≅ Γ` reducing to `u₀` (Lubin–Tate
Proposition 3.3 and §3.4).

## Main results

* `FormalGroup.exists_unique_algHom_of_stabilizer`: existence and uniqueness of the lifted
  endomorphism and connecting isomorphism.
* `FormalGroup.liftAut`: the group homomorphism
  `MulAction.stabilizer (FormalCoordinate k) F₀ →* (R⟦t₁, …, t_{h-1}⟧ ≃ₐ[R] R⟦t₁, …, t_{h-1}⟧)`.
* `FormalGroup.exists_formalGroupIso_map_liftAut`, `FormalGroup.unique_formalGroupIso_map_liftAut`,
  and `FormalGroup.formalGroupIso_map_liftAut_unique`: existence, characterization, and uniqueness
  of the witnessing formal group isomorphism `Γ.map (liftAut u₀) ≅ Γ`.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §3 (Proposition 3.3, §3.4).
-/

public section

noncomputable section

open IsLocalRing MvPowerSeries TauCeti

namespace FormalGroup

private lemma isLocalHom_comp_constantCoeff {σ R k : Type*} [CommRing R] [IsLocalRing R]
    [Field k] (ρ : R →+* k) [IsLocalHom ρ] :
    IsLocalHom (ρ.comp (constantCoeff (σ := σ) (R := R))) where
  map_nonunit f hf := by
    rw [RingHom.comp_apply] at hf
    exact MvPowerSeries.isUnit_iff_constantCoeff.mpr (IsUnit.of_map ρ _ hf)

/-- Uniquely lift a special-fibre automorphism `u₀ ∈ Aut_k(F₀)` to a local `R`-algebra
endomorphism of `R⟦t₁, …, t_{h-1}⟧` together with an isomorphism `Γ.map f ≅ Γ` reducing to
`u₀`. -/
theorem exists_unique_algHom_of_stabilizer
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [CharP k p]
    {ρ : R →+* k} [IsLocalHom ρ] (hρ : Function.Surjective ρ)
    {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    (u₀ : MulAction.stabilizer (FormalCoordinate k) F₀) :
    ∃! f : {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] MvPowerSeries (Fin (h - 1)) R //
        (ρ.comp constantCoeff).comp f.toRingHom = ρ.comp constantCoeff},
      ∃ e : FormalGroupIso (Γ.map f.val.toRingHom) Γ,
        e.toHom.toPowerSeries.map (ρ.comp constantCoeff) = u₀.val.toPowerSeries := by
  let S := MvPowerSeries (Fin (h - 1)) R
  let πS : S →+* k := ρ.comp constantCoeff
  have : IsLocalHom πS := isLocalHom_comp_constantCoeff ρ
  have hπS_surj : Function.Surjective πS := fun y ↦ by
    obtain ⟨r, rfl⟩ := hρ y
    exact ⟨C r, by dsimp [πS]; rw [constantCoeff_C]⟩
  have hπS_R : πS.comp (algebraMap R S) = ρ := by
    ext r
    change ρ (constantCoeff (C r)) = ρ r
    rw [constantCoeff_C]
  have hu₀_inv : u₀.val⁻¹ • F₀ = F₀ := by
    calc u₀.val⁻¹ • F₀ = u₀.val⁻¹ • (u₀.val • F₀) := by rw [u₀.property]
      _ = F₀ := inv_smul_smul _ _
  obtain ⟨u, hu⟩ := FormalCoordinate.map_surjective_of_isLocalHom πS hπS_surj u₀.val
  let G : FormalGroupLift πS F₀ :=
    { formalGroup := u⁻¹ • Γ
      isComm := inferInstance
      map_eq := by rw [FormalGroup.map_smul, map_inv, hu, hΓ, hu₀_inv] }
  let eqv := universalDeformationEquiv hF₀ Γ hΓ hΓord hΓcomp πS hπS_R
  let f := eqv.symm ⟦G⟧
  refine ⟨f, ?_, ?_⟩
  · have hdef : eqv f = ⟦G⟧ := eqv.apply_symm_apply ⟦G⟧
    rw [universalDeformationEquiv_apply, FormalGroupDeformation.map_mk,
      FormalGroupDeformation.mk_eq_mk_iff] at hdef
    obtain ⟨φ, hφ_map, hφ_eq⟩ := hdef
    have hU_eq : (u * φ) • (Γ.map f.val.toRingHom) = Γ := by
      rw [mul_smul, FormalGroupLift.formalGroup_map] at *
      rw [hφ_eq, show G.formalGroup = u⁻¹ • Γ from rfl, smul_inv_smul]
    refine ⟨(FormalGroup.smulIso (u * φ) (Γ.map f.val.toRingHom)).trans
      (formalGroupIsoOfEq hU_eq), ?_⟩
    simp only [FormalGroupIso.trans_toHom, FormalGroupHom.comp_toPowerSeries,
      formalGroupIsoOfEq_toHom_toPowerSeries, FormalGroup.smulIso_toHom_toPowerSeries,
      FormalCoordinate.X_subst_toPowerSeries]
    change PowerSeries.map πS (u * φ).toPowerSeries = u₀.val.toPowerSeries
    rw [← FormalCoordinate.toPowerSeries_map, map_mul, hu, hφ_map, mul_one]
  · rintro g ⟨eg, heg⟩
    apply eqv.injective
    rw [universalDeformationEquiv_apply, eqv.apply_symm_apply,
      FormalGroupDeformation.map_mk, FormalGroupDeformation.mk_eq_mk_iff]
    refine ⟨u⁻¹ * eg.toFormalCoordinate, ?_, ?_⟩
    · have hsub : FormalCoordinate.map πS eg.toFormalCoordinate = u₀.val :=
        FormalCoordinate.ext (by
          rw [FormalCoordinate.toPowerSeries_map, FormalGroupIso.toFormalCoordinate_toPowerSeries]
          exact heg)
      rw [map_mul, map_inv, hu, hsub, inv_mul_cancel]
    · simp only [FormalGroupLift.formalGroup_map, mul_smul, G]
      rw [eg.toFormalCoordinate_smul]

private theorem liftAut_mul_eq
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [CharP k p]
    {ρ : R →+* k} [IsLocalHom ρ] (hρ : Function.Surjective ρ)
    {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    (u₀ v₀ : MulAction.stabilizer (FormalCoordinate k) F₀) :
    (Classical.choose (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp (u₀ * v₀))).val =
      (Classical.choose (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp u₀)).val.comp
        (Classical.choose
          (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp v₀)).val := by
  let S := MvPowerSeries (Fin (h - 1)) R
  let πS : S →+* k := ρ.comp constantCoeff
  let f : MulAction.stabilizer (FormalCoordinate k) F₀ →
      {f : S →ₐ[R] S // πS.comp f.toRingHom = πS} :=
    fun w ↦ Classical.choose (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp w)
  obtain ⟨eu, heu⟩ := (Classical.choose_spec
    (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp u₀)).1
  obtain ⟨ev, hev⟩ := (Classical.choose_spec
    (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp v₀)).1
  let gv : {g : S →ₐ[R] S // πS.comp g.toRingHom = πS} :=
    ⟨(f u₀).val.comp (f v₀).val, by
      ext s
      change πS ((f u₀).val ((f v₀).val s)) = πS s
      exact (RingHom.congr_fun (f u₀).property ((f v₀).val s)).trans
        (RingHom.congr_fun (f v₀).property s)⟩
  have hsrc : ((Γ.map (f v₀).val.toRingHom).map (f u₀).val.toRingHom) =
      Γ.map gv.val.toRingHom := (FormalGroup.map_comp _ _ _).symm
  let e_uv : FormalGroupIso (Γ.map gv.val.toRingHom) Γ :=
    (formalGroupIsoOfEq hsrc.symm).trans ((ev.map (f u₀).val.toRingHom).trans eu)
  have he_uv : e_uv.toHom.toPowerSeries.map πS =
      (u₀ * v₀ : FormalCoordinate k).toPowerSeries := by
    rw [← FormalGroupHom.map_toPowerSeries, ← FormalGroupIso.map_toHom]
    simp only [e_uv, FormalGroupIso.map_trans, FormalGroupIso.trans_toHom,
      FormalGroupHom.comp_toPowerSeries, FormalGroupIso.map_toHom,
      FormalGroupHom.map_toPowerSeries, FormalCoordinate.toPowerSeries_mul]
    have hmap_uv : PowerSeries.map πS
        (PowerSeries.map (f u₀).val.toRingHom ev.toHom.toPowerSeries) =
        PowerSeries.map πS ev.toHom.toPowerSeries :=
      PowerSeries.ext fun k ↦ by
        rw [PowerSeries.coeff_map, PowerSeries.coeff_map, ← RingHom.comp_apply,
          (f u₀).property, ← PowerSeries.coeff_map]
    rw [hmap_uv, formalGroupIsoOfEq_toHom_toPowerSeries,
      PowerSeries.map_X, PowerSeries.X_subst, hev, heu]
  have huniq := (Classical.choose_spec
    (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp (u₀ * v₀))).2
    gv ⟨e_uv, he_uv⟩
  exact congrArg Subtype.val huniq.symm

/-- **Lubin–Tate Proposition 3.3 & §3.4 (automorphism group action).** Given a complete Noetherian
local ring `(R, ρ)` with surjective local residue map `ρ : R →+* k` and a universal deformation `Γ`
of `F₀`, every special-fibre automorphism `u₀ ∈ Aut_k(F₀)` acts via a unique local `R`-algebra
automorphism `liftAut u₀` of `R⟦t₁, …, t_{h-1}⟧` such that `Γ.map (liftAut u₀) ≅ Γ` reduces
to `u₀`. -/
def liftAut
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [CharP k p]
    {ρ : R →+* k} [IsLocalHom ρ] (hρ : Function.Surjective ρ)
    {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k)) :
    MulAction.stabilizer (FormalCoordinate k) F₀ →*
      (MvPowerSeries (Fin (h - 1)) R ≃ₐ[R] MvPowerSeries (Fin (h - 1)) R) := by
  let S := MvPowerSeries (Fin (h - 1)) R
  let πS : S →+* k := ρ.comp constantCoeff
  let f : MulAction.stabilizer (FormalCoordinate k) F₀ →
      {f : S →ₐ[R] S // πS.comp f.toRingHom = πS} :=
    fun u₀ ↦ Classical.choose (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp u₀)
  have hf_one : f 1 = ⟨AlgHom.id R S, by ext x; rfl⟩ :=
    ((Classical.choose_spec
      (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp 1)).2
      ⟨AlgHom.id R S, by ext x; rfl⟩ ⟨FormalGroupIso.refl _, by simp⟩).symm
  have hf_mul : ∀ u₀ v₀, (f (u₀ * v₀)).val = (f u₀).val.comp (f v₀).val :=
    fun u₀ v₀ ↦ liftAut_mul_eq hρ hF₀ Γ hΓ hΓord hΓcomp u₀ v₀
  refine
    { toFun := fun u₀ ↦
        AlgEquiv.ofAlgHom (f u₀).val (f u₀⁻¹).val
          (by rw [← hf_mul, mul_inv_cancel, hf_one])
          (by rw [← hf_mul, inv_mul_cancel, hf_one])
      map_one' := AlgEquiv.ext fun s ↦ by
        change (f 1).val s = s
        rw [hf_one]
        rfl
      map_mul' := fun u₀ v₀ ↦ AlgEquiv.ext fun s ↦ by
        change (f (u₀ * v₀)).val s = (f u₀).val ((f v₀).val s)
        rw [hf_mul]
        rfl }

/-- Applying `liftAut u₀` preserves reduction modulo `ρ ∘ constantCoeff`. -/
@[simp]
theorem liftAut_apply_coe
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [CharP k p]
    {ρ : R →+* k} [IsLocalHom ρ] (hρ : Function.Surjective ρ)
    {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    (u₀ : MulAction.stabilizer (FormalCoordinate k) F₀) :
    (ρ.comp constantCoeff).comp
        ((liftAut hρ hF₀ Γ hΓ hΓord hΓcomp u₀).toAlgHom.toRingHom) =
      ρ.comp constantCoeff := by
  change (ρ.comp constantCoeff).comp
      (Classical.choose
        (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp u₀)).val.toRingHom = _
  exact (Classical.choose (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp u₀)).property

/-- For every special-fibre automorphism `u₀ ∈ Aut_k(F₀)`, there exists a formal group isomorphism
`Γ.map (liftAut u₀) ≅ Γ` whose reduction modulo `ρ ∘ constantCoeff` is `u₀`. -/
theorem exists_formalGroupIso_map_liftAut
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [CharP k p]
    {ρ : R →+* k} [IsLocalHom ρ] (hρ : Function.Surjective ρ)
    {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    (u₀ : MulAction.stabilizer (FormalCoordinate k) F₀) :
    ∃ e : FormalGroupIso
        (Γ.map (liftAut hρ hF₀ Γ hΓ hΓord hΓcomp u₀).toAlgHom.toRingHom) Γ,
      e.toHom.toPowerSeries.map (ρ.comp constantCoeff) = u₀.val.toPowerSeries :=
  (Classical.choose_spec (exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp u₀)).1

/-- Uniqueness in Lubin–Tate Proposition 3.3: any local `R`-algebra endomorphism `g` of
`R⟦t₁, …, t_{h-1}⟧` admitting an isomorphism `Γ.map g ≅ Γ` reducing to `u₀` equals `liftAut u₀`. -/
theorem unique_formalGroupIso_map_liftAut
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [CharP k p]
    {ρ : R →+* k} [IsLocalHom ρ] (hρ : Function.Surjective ρ)
    {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    (u₀ : MulAction.stabilizer (FormalCoordinate k) F₀)
    {g : MvPowerSeries (Fin (h - 1)) R →ₐ[R] MvPowerSeries (Fin (h - 1)) R}
    (hg : (ρ.comp constantCoeff).comp g.toRingHom = ρ.comp constantCoeff)
    (e : FormalGroupIso (Γ.map g.toRingHom) Γ)
    (he : e.toHom.toPowerSeries.map (ρ.comp constantCoeff) = u₀.val.toPowerSeries) :
    g = (liftAut hρ hF₀ Γ hΓ hΓord hΓcomp u₀).toAlgHom := by
  have hu := exists_unique_algHom_of_stabilizer hρ hF₀ Γ hΓ hΓord hΓcomp u₀
  have hg_sub : (⟨g, hg⟩ :
      {g : MvPowerSeries (Fin (h - 1)) R →ₐ[R] MvPowerSeries (Fin (h - 1)) R //
        (ρ.comp constantCoeff).comp g.toRingHom = ρ.comp constantCoeff}) =
      Classical.choose hu :=
    (Classical.choose_spec hu).2 ⟨g, hg⟩ ⟨e, he⟩
  exact congrArg Subtype.val hg_sub

/-- Uniqueness of the witnessing isomorphism `Γ.map (liftAut u₀) ≅ Γ` reducing to `u₀`. -/
theorem formalGroupIso_map_liftAut_unique
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [CharP k p]
    {ρ : R →+* k} [IsLocalHom ρ] (hρ : Function.Surjective ρ)
    {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    (u₀ : MulAction.stabilizer (FormalCoordinate k) F₀)
    (e₁ e₂ : FormalGroupIso
        (Γ.map (liftAut hρ hF₀ Γ hΓ hΓord hΓcomp u₀).toAlgHom.toRingHom) Γ)
    (he₁ : e₁.toHom.toPowerSeries.map (ρ.comp constantCoeff) = u₀.val.toPowerSeries)
    (he₂ : e₂.toHom.toPowerSeries.map (ρ.comp constantCoeff) = u₀.val.toPowerSeries) :
    e₁ = e₂ := by
  let S := MvPowerSeries (Fin (h - 1)) R
  let πS : S →+* k := ρ.comp constantCoeff
  have : IsLocalHom πS := isLocalHom_comp_constantCoeff ρ
  let e_star : FormalGroupIso
      (Γ.map (liftAut hρ hF₀ Γ hΓ hΓord hΓcomp u₀).toAlgHom.toRingHom)
      (Γ.map (liftAut hρ hF₀ Γ hΓ hΓord hΓcomp u₀).toAlgHom.toRingHom) :=
    e₁.trans e₂.symm
  have he_map_eq : e₁.map πS = e₂.map πS := by
    apply FormalGroupIso.ext
    apply FormalGroupHom.ext
    rw [FormalGroupIso.map_toHom, FormalGroupIso.map_toHom,
      FormalGroupHom.map_toPowerSeries, FormalGroupHom.map_toPowerSeries]
    exact he₁.trans he₂.symm
  have he_star : e_star.IsStarIso πS := by
    rw [FormalGroupIso.isStarIso_iff, ← FormalGroupHom.map_toPowerSeries,
      ← FormalGroupIso.map_toHom]
    have hm : e_star.map πS = FormalGroupIso.refl _ := by
      dsimp only [e_star]
      rw [FormalGroupIso.map_trans, FormalGroupIso.map_symm, he_map_eq,
        FormalGroupIso.self_trans_symm]
    rw [hm, FormalGroupIso.refl_toHom, FormalGroupHom.id_toPowerSeries]
  have hht : ((Γ.map (liftAut hρ hF₀ Γ hΓ hΓord hΓcomp u₀).toAlgHom.toRingHom).map πS).height p =
      h := by
    rw [FormalGroup.map_comp, liftAut_apply_coe, hΓ, hF₀]
  have hrefl := FormalGroupIso.eq_of_isStarIso πS e_star (FormalGroupIso.refl _) hht
  have hcomp := congrArg (fun (e : FormalGroupIso _ _) ↦ e.trans e₂) hrefl
  dsimp only [e_star] at hcomp
  rwa [FormalGroupIso.trans_assoc, FormalGroupIso.symm_trans_self,
    FormalGroupIso.trans_refl, FormalGroupIso.refl_trans] at hcomp

end FormalGroup
