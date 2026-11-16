/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.LinearAlgebra.Trace.HattoriStallings.GroupRing

/-!
# Centralizer traces and monoid extensions

This file develops centralizer traces and the coinvariant conjugacy-class trace formula for group
extensions by `ℤ` (the Stacks Project, Section 64.15, Lemmas 64.15.3–64.15.5):

1. **Centralizer traces (Stacks Lemmas 64.15.3–64.15.4).** Given a monoid homomorphism
   `ι : G →* Γ` from a group `G` to a monoid `Γ` and an element `γ ∈ Γ` whose centralizer
   `Z_γ = {g ∈ G | ι g * γ = γ * ι g}` has finite index in `G`, any finitely generated projective
   `Λ[G]`-module `P` carrying a compatible `Λ[Γ]`-action has a well-defined centralizer trace
   `LinearMap.centralizerTrace Λ ι γ P hG ∈ Λ / [Λ, Λ]`. It is invariant under `G`-conjugation
   of `γ` (`LinearMap.centralizerTrace_conj`) and satisfies
   `Tr_Λ(γ, P) = |Z_γ| · Tr^{Z_γ}(γ, P)` when `G` is finite
   (`LinearMap.hattoriStallingsTrace_single_eq_card_nsmul_centralizerTrace`), without inverting
   `|G|` or `|Z_γ|` in `Λ`.
2. **Monoid extensions and coinvariant traces (Stacks Lemma 64.15.5).** For an exact sequence
   `1 → G → Γ → ℤ → 1` (`TauCeti.MonoidExtension`), with positive submonoid
   `E.monoid = {x ∈ Γ | deg x ≥ 0}`, the action of any degree-`n` element on the coinvariants `P_G`
   is independent of the choice of lift, and its Hattori–Stallings trace equals the sum of the
   centralizer traces over the `G`-conjugacy classes of degree `n`
   (`TauCeti.MonoidExtension.hattoriStallingsTrace_coinvariantsAction`).

## References

* The Stacks Project, Section 64.15, Lemmas 64.15.3–64.15.5 (Tags `03U7`–`03U9`).
-/

public section

noncomputable section

open Module MonoidAlgebra TensorProduct

/-! ### Section 1: Centralizer subgroups and centralizer traces (Stacks 64.15.3–64.15.4) -/

namespace MonoidHom

section CentralizerSubgroup

variable {G Γ : Type*} [Group G] [Monoid Γ]

/-- The centralizer in a group `G` of an element `γ` of a monoid `Γ` along a monoid homomorphism
`ι : G →* Γ`. Works for an arbitrary monoid `Γ` (without requiring `γ` to be invertible in `Γ`),
using the invertibility of `ι g` for `g ∈ G`. -/
def centralizerSubgroup (ι : G →* Γ) (γ : Γ) : Subgroup G where
  carrier := {g : G | ι g * γ = γ * ι g}
  mul_mem' {a b} ha hb := by
    change ι (a * b) * γ = γ * ι (a * b)
    rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  one_mem' := by
    change ι 1 * γ = γ * ι 1
    simp
  inv_mem' {a} ha := by
    change ι a⁻¹ * γ = γ * ι a⁻¹
    calc ι a⁻¹ * γ = ι a⁻¹ * (γ * ι a) * ι a⁻¹ := by
          rw [mul_assoc, mul_assoc, ← map_mul ι a a⁻¹, mul_inv_cancel, map_one, mul_one]
      _ = ι a⁻¹ * (ι a * γ) * ι a⁻¹ := by rw [← ha]
      _ = γ * ι a⁻¹ := by
          rw [← mul_assoc (ι a⁻¹), ← map_mul ι a⁻¹ a, inv_mul_cancel, map_one, one_mul]

@[simp]
theorem mem_centralizerSubgroup (ι : G →* Γ) (γ : Γ) (g : G) :
    g ∈ ι.centralizerSubgroup γ ↔ ι g * γ = γ * ι g :=
  Iff.rfl

/-- Conjugation by `g : G` carries `ι.centralizerSubgroup γ` isomorphically onto
`ι.centralizerSubgroup (ι g * γ * ι g⁻¹)`. -/
def centralizerSubgroupConjEquiv (ι : G →* Γ) (g : G) (γ : Γ) :
    ι.centralizerSubgroup γ ≃* ι.centralizerSubgroup (ι g * γ * ι g⁻¹) where
  toFun h := ⟨g * h.1 * g⁻¹, by
    rw [mem_centralizerSubgroup, map_mul, map_mul]
    calc ι g * ι h.1 * ι g⁻¹ * (ι g * γ * ι g⁻¹)
        = ι g * ι h.1 * (ι g⁻¹ * ι g) * γ * ι g⁻¹ := by simp only [mul_assoc]
      _ = ι g * (ι h.1 * γ) * ι g⁻¹ := by
          rw [← map_mul ι g⁻¹ g, inv_mul_cancel, map_one, mul_one]
          simp only [mul_assoc]
      _ = ι g * (γ * ι h.1) * ι g⁻¹ := by rw [h.2]
      _ = ι g * γ * (ι g⁻¹ * ι g) * ι h.1 * ι g⁻¹ := by
          rw [← map_mul ι g⁻¹ g, inv_mul_cancel, map_one, mul_one]
          simp only [mul_assoc]
      _ = ι g * γ * ι g⁻¹ * (ι g * ι h.1 * ι g⁻¹) := by simp only [mul_assoc]⟩
  invFun h' := ⟨g⁻¹ * h'.1 * g, by
    rw [mem_centralizerSubgroup, map_mul, map_mul]
    have hh' : ι h'.1 * (ι g * γ * ι g⁻¹) = ι g * γ * ι g⁻¹ * ι h'.1 := h'.2
    calc ι g⁻¹ * ι h'.1 * ι g * γ
        = ι g⁻¹ * (ι h'.1 * (ι g * γ * ι g⁻¹)) * ι g := by
          simp only [mul_assoc]
          rw [← map_mul ι g⁻¹ g, inv_mul_cancel, map_one, mul_one]
      _ = ι g⁻¹ * (ι g * γ * ι g⁻¹ * ι h'.1) * ι g := by rw [hh']
      _ = (ι g⁻¹ * ι g) * γ * ι g⁻¹ * ι h'.1 * ι g := by simp only [mul_assoc]
      _ = γ * (ι g⁻¹ * ι h'.1 * ι g) := by
          rw [← map_mul ι g⁻¹ g, inv_mul_cancel, map_one, one_mul]
          simp only [mul_assoc]⟩
  left_inv h := Subtype.ext (by group)
  right_inv h' := Subtype.ext (by group)
  map_mul' h₁ h₂ := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

/-- Conjugating `γ` by `ι g` preserves finite index of the centralizer subgroup in `G`. -/
theorem centralizerSubgroup_conj_finiteIndex (ι : G →* Γ) (g : G) (γ : Γ)
    [(ι.centralizerSubgroup γ).FiniteIndex] :
    (ι.centralizerSubgroup (ι g * γ * ι g⁻¹)).FiniteIndex := by
  let e : (G ⧸ ι.centralizerSubgroup γ) ≃ G ⧸ ι.centralizerSubgroup (ι g * γ * ι g⁻¹) :=
    { toFun := Quotient.lift (fun x : G ↦ QuotientGroup.mk (g * x * g⁻¹)) fun x y hxy ↦ by
        apply QuotientGroup.eq.mpr
        have h : x⁻¹ * y ∈ ι.centralizerSubgroup γ := QuotientGroup.leftRel_apply.mp hxy
        have hc := (ι.centralizerSubgroupConjEquiv g γ ⟨x⁻¹ * y, h⟩).2
        have heq : (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹) = g * (x⁻¹ * y) * g⁻¹ := by group
        rw [heq]
        exact hc
      invFun := Quotient.lift (fun y : G ↦ QuotientGroup.mk (g⁻¹ * y * g)) fun x y hxy ↦ by
        apply QuotientGroup.eq.mpr
        have h : x⁻¹ * y ∈ ι.centralizerSubgroup (ι g * γ * ι g⁻¹) :=
          QuotientGroup.leftRel_apply.mp hxy
        have hc := ((ι.centralizerSubgroupConjEquiv g γ).symm ⟨x⁻¹ * y, h⟩).2
        have heq : (g⁻¹ * x * g)⁻¹ * (g⁻¹ * y * g) = g⁻¹ * (x⁻¹ * y) * g := by group
        rw [heq]
        exact hc
      left_inv := fun q ↦ Quotient.inductionOn' q fun x ↦ by
        change QuotientGroup.mk (g⁻¹ * (g * x * g⁻¹) * g) = QuotientGroup.mk x
        have heq : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [heq]
      right_inv := fun q ↦ Quotient.inductionOn' q fun y ↦ by
        change QuotientGroup.mk (g * (g⁻¹ * y * g) * g⁻¹) = QuotientGroup.mk y
        have heq : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        rw [heq] }
  have : Finite (G ⧸ ι.centralizerSubgroup (ι g * γ * ι g⁻¹)) := Finite.of_equiv _ e
  exact Subgroup.finiteIndex_of_finite_quotient

end CentralizerSubgroup

end MonoidHom

namespace MonoidAlgebra

section SingleSMulEnd

variable (Λ : Type*) [Ring Λ] {Γ : Type*} [Monoid Γ]

/-- The `Λ`-linear endomorphism of a `Λ[Γ]`-module given by left multiplication by `single γ 1`.
Works over an arbitrary (possibly noncommutative) ring `Λ` because `single γ 1` commutes with
`single 1 a` in `Λ[Γ]`. -/
def singleSMulEnd (γ : Γ) (P : Type*) [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ Γ) P] [IsScalarTower Λ (MonoidAlgebra Λ Γ) P] :
    Module.End Λ P where
  toFun x := (single γ (1 : Λ) : MonoidAlgebra Λ Γ) • x
  map_add' := smul_add _
  map_smul' a x := by
    simp only [RingHom.id_apply]
    have ha : a • x = (single (1 : Γ) a : MonoidAlgebra Λ Γ) • x := by
      have h1 : (single (1 : Γ) a : MonoidAlgebra Λ Γ) = a • (1 : MonoidAlgebra Λ Γ) := by
        rw [one_def, smul_single, smul_eq_mul, mul_one]
      rw [h1, smul_assoc, one_smul]
    rw [ha, ← mul_smul, single_mul_single, mul_one, one_mul, ← smul_assoc, smul_single,
      smul_eq_mul, mul_one]

@[simp]
theorem singleSMulEnd_apply (γ : Γ) (P : Type*) [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ Γ) P] [IsScalarTower Λ (MonoidAlgebra Λ Γ) P] (x : P) :
    singleSMulEnd Λ γ P x = (single γ (1 : Λ) : MonoidAlgebra Λ Γ) • x :=
  (rfl)

@[simp]
theorem singleSMulEnd_one (P : Type*) [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ Γ) P] [IsScalarTower Λ (MonoidAlgebra Λ Γ) P] :
    singleSMulEnd Λ (1 : Γ) P = .id := by
  ext x
  simp [← one_def]

theorem singleSMulEnd_mul (γ₁ γ₂ : Γ) (P : Type*) [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ Γ) P] [IsScalarTower Λ (MonoidAlgebra Λ Γ) P] :
    singleSMulEnd Λ (γ₁ * γ₂) P = (singleSMulEnd Λ γ₁ P).comp (singleSMulEnd Λ γ₂ P) := by
  ext x
  simp [← mul_smul, single_mul_single]

end SingleSMulEnd

end MonoidAlgebra

namespace LinearMap

section CentralizerTrace

variable {Λ : Type*} [Ring Λ] {G Γ : Type*} [Group G] [Monoid Γ]

variable (Λ) in
/-- The centralizer trace `Tr^{Z_γ}(γ, P) ∈ Λ / [Λ, Λ]` of an element `γ ∈ Γ` acting on a
`Λ[Γ]`-module `P` that is finitely generated and projective over `Λ[G]`, where
`Z_γ = ι.centralizerSubgroup γ` has finite index in `G`. -/
def centralizerTrace (ι : G →* Γ) (γ : Γ) [(ι.centralizerSubgroup γ).FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra Λ Γ) P] [Module (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    TauCeti.cyclicQuotient ℤ Λ :=
  let Z := ι.centralizerSubgroup γ
  letI : Module (MonoidAlgebra Λ Z) P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  have hZ : ∀ (r : MonoidAlgebra Λ Z) (x : P), r • x = mapDomainRingHom Λ Z.subtype r • x :=
    fun _ _ ↦ rfl
  haveI := (Z.restrict_finite_projective (Λ := Λ) P hZ).1
  haveI := (Z.restrict_finite_projective (Λ := Λ) P hZ).2
  have hZΓ : ∀ (r : MonoidAlgebra Λ Z) (x : P),
      r • x = mapDomain (ι.comp Z.subtype) r • x := fun r x ↦ by
    change mapDomainRingHom Λ Z.subtype r • x = _
    rw [hG, mapDomainRingHom_apply, MonoidAlgebra.mapDomain_mapDomain]
    rfl
  groupAlgebraTrace Λ Z P ((ι.comp Z.subtype).singleSMulLinearMap (fun g ↦ g.2) P hZΓ)

/-- Compute `centralizerTrace` in any finite free `Λ[G]`-retract `(i, r)` of `P`. -/
theorem centralizerTrace_eq_of_retract (ι : G →* Γ) (γ : Γ)
    [(ι.centralizerSubgroup γ).FiniteIndex]
    [Fintype (G ⧸ (ι.centralizerSubgroup γ).subtype.range)]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra Λ Γ) P] [Module (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    {n : ℕ} (i : P →ₗ[MonoidAlgebra Λ G] (Fin n → MonoidAlgebra Λ G))
    (r : (Fin n → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] P) (hr : r ∘ₗ i = .id) :
    centralizerTrace Λ ι γ P hG =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin n, ∑ q : G ⧸ (ι.centralizerSubgroup γ).subtype.range,
          (i ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) •
            r (Pi.single k (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) k).coeff q.out⁻¹) := by
  classical
  let Z := ι.centralizerSubgroup γ
  let : Module (MonoidAlgebra Λ Z) P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  have hZ : ∀ (c : MonoidAlgebra Λ Z) (x : P), c • x = mapDomainRingHom Λ Z.subtype c • x :=
    fun _ _ ↦ rfl
  have := (Z.restrict_finite_projective (Λ := Λ) P hZ).1
  have := (Z.restrict_finite_projective (Λ := Λ) P hZ).2
  have hZΓ : ∀ (c : MonoidAlgebra Λ Z) (x : P),
      c • x = mapDomain (ι.comp Z.subtype) c • x := fun c x ↦ by
    change mapDomainRingHom Λ Z.subtype c • x = _
    rw [hG, mapDomainRingHom_apply, MonoidAlgebra.mapDomain_mapDomain]
    rfl
  let : Module (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) :=
    (mapDomainRingHom Λ Z.subtype).toModule
  have : IsScalarTower (MonoidAlgebra Λ Z) (MonoidAlgebra Λ G) (MonoidAlgebra Λ G) :=
    ⟨fun c s t ↦ mul_assoc (mapDomainRingHom Λ Z.subtype c) s t⟩
  let bZ := TauCeti.MonoidAlgebra.basisCosets Λ Z.subtype Z.subtype_injective
  let ePi : (Fin n → MonoidAlgebra Λ G) ≃ₗ[MonoidAlgebra Λ Z]
      (Fin n × (G ⧸ Z.subtype.range) →₀ MonoidAlgebra Λ Z) :=
    { toFun := fun v ↦ Finsupp.equivFunOnFinite.symm fun p ↦ bZ.repr (v p.1) p.2
      invFun := fun w k ↦ bZ.repr.symm (Finsupp.equivFunOnFinite.symm fun q ↦ w (k, q))
      left_inv := fun v ↦ funext fun k ↦ by
        apply bZ.repr.injective
        ext q
        simp
      right_inv := fun w ↦ by ext ⟨k, q⟩; simp
      map_add' := fun u v ↦ by ext ⟨k, q⟩; simp
      map_smul' := fun c v ↦ by ext ⟨k, q⟩; simp }
  let bPi : Basis (Fin n × (G ⧸ Z.subtype.range)) (MonoidAlgebra Λ Z)
      (Fin n → MonoidAlgebra Λ G) :=
    Basis.ofRepr ePi
  let iZ : P →ₗ[MonoidAlgebra Λ Z] (Fin n → MonoidAlgebra Λ G) :=
    { toFun := i
      map_add' := i.map_add
      map_smul' := fun c x ↦ by
        ext k
        simp only [RingHom.id_apply, hZ, i.map_smul, Pi.smul_apply]
        rfl }
  let rZ : (Fin n → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ Z] P :=
    { toFun := r
      map_add' := r.map_add
      map_smul' := fun c v ↦ by
        have hv : c • v = mapDomainRingHom Λ Z.subtype c • v := rfl
        rw [hv, r.map_smul, RingHom.id_apply, hZ] }
  have hrZ : rZ ∘ₗ iZ = .id := LinearMap.ext fun x ↦
    congrArg (fun g : Module.End (MonoidAlgebra Λ G) P ↦ g x) hr
  have hbPi : ∀ p : Fin n × (G ⧸ Z.subtype.range),
      bPi p = Pi.single p.1 (MonoidAlgebra.single p.2.out⁻¹ (1 : Λ)) := by
    intro ⟨k, q⟩
    funext j
    apply bZ.repr.injective
    apply Finsupp.ext
    intro q'
    have hval : ePi (bPi (k, q)) = Finsupp.single (k, q) (1 : MonoidAlgebra Λ Z) :=
      Basis.repr_self bPi (k, q)
    have h1 := DFunLike.congr_fun hval (j, q')
    change bZ.repr (bPi (k, q) j) q' = Finsupp.single (k, q) (1 : MonoidAlgebra Λ Z) (j, q') at h1
    rw [h1, Finsupp.single_apply]
    by_cases hjk : j = k
    · subst hjk
      simp only [Pi.single_eq_same, Prod.mk.injEq, true_and]
      have hbq : MonoidAlgebra.single q.out⁻¹ (1 : Λ) = bZ q :=
        (TauCeti.MonoidAlgebra.basisCosets_apply Λ Z.subtype Z.subtype_injective q).symm
      rw [hbq, bZ.repr_self, Finsupp.single_apply]
    · simp [Ne.symm hjk]
  unfold centralizerTrace
  rw [groupAlgebraTrace_eq_of_retract bPi iZ rZ hrZ, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  rw [hbPi (k, q)]
  have hact : ((ι.comp Z.subtype).singleSMulLinearMap (fun g ↦ g.2) P hZΓ)
      (rZ (Pi.single k (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) =
      (MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) •
        r (Pi.single k (MonoidAlgebra.single q.out⁻¹ (1 : Λ))) :=
    MonoidHom.singleSMulLinearMap_apply (ι.comp Z.subtype) (fun g ↦ g.2) P hZΓ _
  change (bZ.repr (i (((ι.comp Z.subtype).singleSMulLinearMap (fun g ↦ g.2) P hZΓ)
    (rZ (Pi.single k (MonoidAlgebra.single q.out⁻¹ (1 : Λ))))) k) q).coeff 1 = _
  rw [hact]
  exact coeff_one_basisCosets_repr Z
    (i ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) •
      r (Pi.single k (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) k) q

/-- **Stacks Lemma 64.15.4.** For a finite group `G`, the `Λ`-linear Hattori–Stallings trace of
`γ` acting on `P` equals `|Z_γ|` times its centralizer trace `Tr^{Z_γ}(γ, P)`, over an arbitrary
(possibly noncommutative) ring `Λ` and without dividing by `|Z_γ|`. -/
theorem hattoriStallingsTrace_single_eq_card_nsmul_centralizerTrace [Finite G] (ι : G →* Γ)
    (γ : Γ) (P : Type*) [AddCommGroup P] [Module Λ P] [Module (MonoidAlgebra Λ Γ) P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ Γ) P]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := Λ) (G := G) P).1
    haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := Λ) (G := G) P).2
    hattoriStallingsTrace Λ P (singleSMulEnd Λ γ P) =
      Nat.card (ι.centralizerSubgroup γ) • centralizerTrace Λ ι γ P hG := by
  let Z := ι.centralizerSubgroup γ
  let : Module (MonoidAlgebra Λ Z) P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  have hZ : ∀ (c : MonoidAlgebra Λ Z) (x : P), c • x = mapDomainRingHom Λ Z.subtype c • x :=
    fun _ _ ↦ rfl
  have := (Z.restrict_finite_projective (Λ := Λ) P hZ).1
  have := (Z.restrict_finite_projective (Λ := Λ) P hZ).2
  have : IsScalarTower Λ (MonoidAlgebra Λ Z) P := ⟨fun a c x ↦ by
    change mapDomainRingHom Λ Z.subtype (a • c) • x =
      a • (mapDomainRingHom Λ Z.subtype c • x)
    rw [← smul_assoc]
    congr 1
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add c₁ c₂ h₁ h₂ => simp [smul_add, map_add, h₁, h₂]
    | single z b => simp [mapDomainRingHom_apply, smul_single]⟩
  have hZΓ : ∀ (c : MonoidAlgebra Λ Z) (x : P),
      c • x = mapDomain (ι.comp Z.subtype) c • x := fun c x ↦ by
    change mapDomainRingHom Λ Z.subtype c • x = _
    rw [hG, mapDomainRingHom_apply, MonoidAlgebra.mapDomain_mapDomain]
    rfl
  have hf : ((ι.comp Z.subtype).singleSMulLinearMap (fun g ↦ g.2) P hZΓ).restrictScalars Λ =
      singleSMulEnd Λ γ P :=
    LinearMap.ext fun x ↦
      MonoidHom.singleSMulLinearMap_apply (ι.comp Z.subtype) (fun g ↦ g.2) P hZΓ x
  have hmain := hattoriStallingsTrace_restrictScalars_eq_card_nsmul_groupAlgebraTrace (Λ := Λ)
    (G := Z) (P := P) ((ι.comp Z.subtype).singleSMulLinearMap (fun g ↦ g.2) P hZΓ)
  rw [hf] at hmain
  exact hmain

/-- **Stacks Lemma 64.15.3.** Conjugating `γ` by `ι g` (`g ∈ G`) does not change its centralizer
trace. -/
theorem centralizerTrace_conj (ι : G →* Γ) (g : G) (γ : Γ)
    [(ι.centralizerSubgroup γ).FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra Λ Γ) P] [Module (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    haveI := ι.centralizerSubgroup_conj_finiteIndex g γ
    centralizerTrace Λ ι (ι g * γ * ι g⁻¹) P hG = centralizerTrace Λ ι γ P hG := by
  have := ι.centralizerSubgroup_conj_finiteIndex g γ
  let Z := ι.centralizerSubgroup γ
  let Z' := ι.centralizerSubgroup (ι g * γ * ι g⁻¹)
  let e : Z ≃* Z' := ι.centralizerSubgroupConjEquiv g γ
  let mZ : Module (MonoidAlgebra Λ Z) P := Module.compHom P (mapDomainRingHom Λ Z.subtype)
  let mZ' : Module (MonoidAlgebra Λ Z') P := Module.compHom P (mapDomainRingHom Λ Z'.subtype)
  have hZ : ∀ (c : MonoidAlgebra Λ Z) (x : P),
      @SMul.smul _ _ mZ.toSMul c x = mapDomainRingHom Λ Z.subtype c • x := fun _ _ ↦ rfl
  have hZ' : ∀ (c : MonoidAlgebra Λ Z') (x : P),
      @SMul.smul _ _ mZ'.toSMul c x = mapDomainRingHom Λ Z'.subtype c • x := fun _ _ ↦ rfl
  have hfpZ := @Subgroup.restrict_finite_projective Λ _ G _ Z _ P _ _ _ _ mZ hZ
  have hfpZ' := @Subgroup.restrict_finite_projective Λ _ G _ Z' _ P _ _ _ _ mZ' hZ'
  have hZΓ : ∀ (c : MonoidAlgebra Λ Z) (x : P),
      @SMul.smul _ _ mZ.toSMul c x = mapDomain (ι.comp Z.subtype) c • x := fun c x ↦ by
    change mapDomainRingHom Λ Z.subtype c • x = _
    rw [hG, mapDomainRingHom_apply, MonoidAlgebra.mapDomain_mapDomain]
    rfl
  have hZ'Γ : ∀ (c : MonoidAlgebra Λ Z') (x : P),
      @SMul.smul _ _ mZ'.toSMul c x = mapDomain (ι.comp Z'.subtype) c • x := fun c x ↦ by
    change mapDomainRingHom Λ Z'.subtype c • x = _
    rw [hG, mapDomainRingHom_apply, MonoidAlgebra.mapDomain_mapDomain]
    rfl
  let eP : P ≃+ P :=
    { toFun := fun x ↦ (MonoidAlgebra.single (ι g) (1 : Λ) : MonoidAlgebra Λ Γ) • x
      invFun := fun x ↦ (MonoidAlgebra.single (ι g⁻¹) (1 : Λ) : MonoidAlgebra Λ Γ) • x
      left_inv := fun x ↦ by
        dsimp only
        rw [← mul_smul, single_mul_single, mul_one, ← map_mul, inv_mul_cancel, map_one, ← one_def,
          one_smul]
      right_inv := fun x ↦ by
        dsimp only
        rw [← mul_smul, single_mul_single, mul_one, ← map_mul, mul_inv_cancel, map_one, ← one_def,
          one_smul]
      map_add' := smul_add _ }
  have heP : ∀ (c : MonoidAlgebra Λ Z) (x : P),
      eP (@SMul.smul _ _ mZ.toSMul c x) =
        @SMul.smul _ _ mZ'.toSMul (mapDomainRingHom Λ e.toMonoidHom c) (eP x) := by
    intro c x
    rw [hZΓ, hZ'Γ]
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp [map_zero, mapDomain_zero, zero_smul]
    | add c₁ c₂ h₁ h₂ =>
      rw [map_add, mapDomain_add, mapDomain_add, add_smul, add_smul, map_add, h₁, h₂]
    | single z a =>
      rw [mapDomainRingHom_apply, mapDomain_single, mapDomain_single, mapDomain_single]
      change (MonoidAlgebra.single (ι g) (1 : Λ) : MonoidAlgebra Λ Γ) •
          ((MonoidAlgebra.single (ι z.1) a : MonoidAlgebra Λ Γ) • x) =
        (MonoidAlgebra.single (ι (g * z.1 * g⁻¹)) a : MonoidAlgebra Λ Γ) •
          ((MonoidAlgebra.single (ι g) (1 : Λ) : MonoidAlgebra Λ Γ) • x)
      rw [← mul_smul, ← mul_smul, single_mul_single, single_mul_single, one_mul, mul_one,
        ← map_mul, ← map_mul]
      have hmul : g * z.1 * g⁻¹ * g = g * z.1 := by group
      rw [hmul]
  have hcommZ : ∀ h : Z, Commute ((ι.comp Z.subtype) h) γ := fun h ↦ h.2
  have hcommZ' : ∀ h : Z', Commute ((ι.comp Z'.subtype) h) (ι g * γ * ι g⁻¹) := fun h ↦ h.2
  let fZ := @MonoidHom.singleSMulLinearMap Λ _ Z Γ _ _ (ι.comp Z.subtype) γ hcommZ P _ _ mZ hZΓ
  let fZ' := @MonoidHom.singleSMulLinearMap Λ _ Z' Γ _ _ (ι.comp Z'.subtype) (ι g * γ * ι g⁻¹)
    hcommZ' P _ _ mZ' hZ'Γ
  have hf : ∀ x : P, fZ' (eP x) = eP (fZ x) := by
    intro x
    rw [show fZ' (eP x) =
          (MonoidAlgebra.single (ι g * γ * ι g⁻¹) (1 : Λ) : MonoidAlgebra Λ Γ) • eP x from
        MonoidHom.singleSMulLinearMap_apply _ _ _ _ _,
      show fZ x = (MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) • x from
        MonoidHom.singleSMulLinearMap_apply _ _ _ _ _]
    change (MonoidAlgebra.single (ι g * γ * ι g⁻¹) (1 : Λ) : MonoidAlgebra Λ Γ) •
        ((MonoidAlgebra.single (ι g) (1 : Λ) : MonoidAlgebra Λ Γ) • x) =
      (MonoidAlgebra.single (ι g) (1 : Λ) : MonoidAlgebra Λ Γ) •
        ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) • x)
    rw [← mul_smul, ← mul_smul, single_mul_single, single_mul_single, mul_one, mul_assoc,
      mul_assoc, ← map_mul ι g⁻¹ g, inv_mul_cancel, map_one, mul_one]
  exact @groupAlgebraTrace_conj_equiv Λ _ Z Z' _ _ P _ mZ P _ mZ' hfpZ.1 hfpZ.2 hfpZ'.1 hfpZ'.2
    e eP heP fZ fZ' hf

/-- Variant of `centralizerTrace_conj` for elements satisfying `ι g * γ = γ' * ι g`. -/
theorem centralizerTrace_eq_of_conj (ι : G →* Γ) (g : G) {γ γ' : Γ}
    (hγ : ι g * γ = γ' * ι g) [(ι.centralizerSubgroup γ).FiniteIndex]
    [(ι.centralizerSubgroup γ').FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra Λ Γ) P] [Module (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    centralizerTrace Λ ι γ' P hG = centralizerTrace Λ ι γ P hG := by
  have hγ' : γ' = ι g * γ * ι g⁻¹ := by
    calc γ' = γ' * (ι g * ι g⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = (γ' * ι g) * ι g⁻¹ := by rw [mul_assoc]
      _ = ι g * γ * ι g⁻¹ := by rw [← hγ]
  subst hγ'
  exact centralizerTrace_conj ι g γ P hG

section CommutativeCentralizerTrace

variable {A : Type*} [CommRing A]

variable (A) in
/-- Over a commutative ring `A`, the centralizer trace takes scalar values in `A`. -/
def centralizerScalarTrace (ι : G →* Γ) (γ : Γ) [(ι.centralizerSubgroup γ).FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra A Γ) P] [Module (MonoidAlgebra A G) P]
    (hG : ∀ (r : MonoidAlgebra A G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P] : A :=
  TauCeti.cyclicQuotientEquivSelf A (centralizerTrace A ι γ P hG)

theorem centralizerScalarTrace_apply (ι : G →* Γ) (γ : Γ) [(ι.centralizerSubgroup γ).FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra A Γ) P] [Module (MonoidAlgebra A G) P]
    (hG : ∀ (r : MonoidAlgebra A G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P] :
    centralizerScalarTrace A ι γ P hG =
      TauCeti.cyclicQuotientEquivSelf A (centralizerTrace A ι γ P hG) :=
  (rfl)

theorem centralizerScalarTrace_eq_of_retract (ι : G →* Γ) (γ : Γ)
    [(ι.centralizerSubgroup γ).FiniteIndex]
    [Fintype (G ⧸ (ι.centralizerSubgroup γ).subtype.range)]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra A Γ) P] [Module (MonoidAlgebra A G) P]
    (hG : ∀ (r : MonoidAlgebra A G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    {n : ℕ} (i : P →ₗ[MonoidAlgebra A G] (Fin n → MonoidAlgebra A G))
    (r : (Fin n → MonoidAlgebra A G) →ₗ[MonoidAlgebra A G] P) (hr : r ∘ₗ i = .id) :
    centralizerScalarTrace A ι γ P hG =
      ∑ k : Fin n, ∑ q : G ⧸ (ι.centralizerSubgroup γ).subtype.range,
        (i ((MonoidAlgebra.single γ (1 : A) : MonoidAlgebra A Γ) •
          r (Pi.single k (MonoidAlgebra.single q.out⁻¹ (1 : A)))) k).coeff q.out⁻¹ := by
  rw [centralizerScalarTrace, centralizerTrace_eq_of_retract ι γ P hG i r hr,
    TauCeti.cyclicQuotientEquivSelf_mkQ]

/-- Over a commutative ring `A` and a finite group `G`, the `A`-linear projective trace of `γ`
equals `|Z_γ| * centralizerScalarTrace A ι γ P hG`. -/
theorem projectiveTrace_single_eq_card_mul_centralizerScalarTrace [Finite G] (ι : G →* Γ)
    (γ : Γ) (P : Type*) [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A Γ) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A Γ) P]
    [IsScalarTower A (MonoidAlgebra A G) P]
    (hG : ∀ (r : MonoidAlgebra A G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P] :
    haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := A) (G := G) P).1
    haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := A) (G := G) P).2
    projectiveTrace A P (singleSMulEnd A γ P) =
      (Nat.card (ι.centralizerSubgroup γ) : A) * centralizerScalarTrace A ι γ P hG := by
  have := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := A) (G := G) P).1
  have := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := A) (G := G) P).2
  rw [← cyclicQuotientEquivSelf_hattoriStallingsTrace,
    hattoriStallingsTrace_single_eq_card_nsmul_centralizerTrace ι γ P hG, map_nsmul,
    nsmul_eq_mul, centralizerScalarTrace]

/-- Over a commutative ring `A`, `centralizerScalarTrace` is invariant under `G`-conjugation. -/
theorem centralizerScalarTrace_conj (ι : G →* Γ) (g : G) (γ : Γ)
    [(ι.centralizerSubgroup γ).FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra A Γ) P] [Module (MonoidAlgebra A G) P]
    (hG : ∀ (r : MonoidAlgebra A G) (x : P), r • x = mapDomain ι r • x)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P] :
    haveI := ι.centralizerSubgroup_conj_finiteIndex g γ
    centralizerScalarTrace A ι (ι g * γ * ι g⁻¹) P hG = centralizerScalarTrace A ι γ P hG := by
  have := ι.centralizerSubgroup_conj_finiteIndex g γ
  rw [centralizerScalarTrace, centralizerScalarTrace, centralizerTrace_conj ι g γ P hG]

end CommutativeCentralizerTrace

end CentralizerTrace

end LinearMap

/-! ### Section 2: Monoid extensions and coinvariant conjugacy-class sum (Stacks 64.15.5) -/

namespace TauCeti

/-- A short exact sequence of groups `1 → G → Γ → ℤ → 1`, as in Stacks §64.15. Its nonnegative
degree elements form the monoid `E.monoid` containing `G` as its degree-`0` subgroup. -/
structure MonoidExtension (G Γ : Type*) [Group G] [Group Γ] where
  /-- The inclusion `G ↪ Γ` of the kernel. -/
  incl : G →* Γ
  /-- The degree surjection `Γ ↠ ℤ` (written multiplicatively). -/
  proj : Γ →* Multiplicative ℤ
  /-- `incl` is injective. -/
  incl_injective : Function.Injective incl
  /-- `proj` is surjective. -/
  proj_surjective : Function.Surjective proj
  /-- Exactness in the middle: `ker proj = range incl`. -/
  ker_proj : proj.ker = incl.range

namespace MonoidExtension

variable {G Γ : Type*} [Group G] [Group Γ] (E : MonoidExtension G Γ)

/-- The integer degree of an element of `Γ`. -/
def degree (x : Γ) : ℤ :=
  Multiplicative.toAdd (E.proj x)

@[simp]
theorem degree_one : E.degree 1 = 0 := by
  simp [degree]

@[simp]
theorem degree_mul (x y : Γ) : E.degree (x * y) = E.degree x + E.degree y := by
  simp [degree, map_mul]

theorem degree_apply (x : Γ) : E.degree x = Multiplicative.toAdd (E.proj x) :=
  (rfl)

@[simp]
theorem degree_inv (x : Γ) : E.degree x⁻¹ = -E.degree x := by
  simp [degree, map_inv]

@[simp]
theorem degree_pow (x : Γ) (n : ℕ) : E.degree (x ^ n) = n * E.degree x := by
  simp [degree, map_pow]

@[simp]
theorem degree_zpow (x : Γ) (k : ℤ) : E.degree (x ^ k) = k * E.degree x := by
  simp [degree, map_zpow]

@[simp]
theorem degree_incl (g : G) : E.degree (E.incl g) = 0 := by
  have hg : E.incl g ∈ E.proj.ker := by
    rw [E.ker_proj]
    exact ⟨g, rfl⟩
  simp [degree, MonoidHom.mem_ker.mp hg]

theorem degree_eq_zero_iff (x : Γ) : E.degree x = 0 ↔ x ∈ E.incl.range := by
  rw [← E.ker_proj, MonoidHom.mem_ker, degree]
  constructor
  · intro h
    exact (Equiv.eq_symm_apply Multiplicative.toAdd).mpr h
  · intro h
    rw [h]
    rfl

theorem exists_incl_mul_of_degree_eq {x y : Γ} (h : E.degree x = E.degree y) :
    ∃ g : G, x = E.incl g * y := by
  have hdeg : E.degree (x * y⁻¹) = 0 := by simp [h]
  obtain ⟨g, hg⟩ := (E.degree_eq_zero_iff _).mp hdeg
  exact ⟨g, by rw [hg, mul_assoc, inv_mul_cancel, mul_one]⟩

theorem exists_mul_incl_of_degree_eq {x y : Γ} (h : E.degree x = E.degree y) :
    ∃ g : G, x = y * E.incl g := by
  have hdeg : E.degree (y⁻¹ * x) = 0 := by simp [h]
  obtain ⟨g, hg⟩ := (E.degree_eq_zero_iff _).mp hdeg
  exact ⟨g, by rw [hg, ← mul_assoc, mul_inv_cancel, one_mul]⟩

/-- The submonoid `{x ∈ Γ | deg x ≥ 0}` of elements of nonnegative degree. -/
def monoid : Submonoid Γ where
  carrier := {x : Γ | 0 ≤ E.degree x}
  mul_mem' {a b} ha hb := by
    change 0 ≤ E.degree (a * b)
    rw [degree_mul]
    exact add_nonneg ha hb
  one_mem' := by
    change 0 ≤ E.degree 1
    simp

@[simp]
theorem mem_monoid (x : Γ) : x ∈ E.monoid ↔ 0 ≤ E.degree x :=
  Iff.rfl

/-- The inclusion of `G` into the positive submonoid `E.monoid`. -/
def monoidIncl : G →* E.monoid where
  toFun g := ⟨E.incl g, by simp⟩
  map_one' := Subtype.ext (map_one E.incl)
  map_mul' g h := Subtype.ext (map_mul E.incl g h)

@[simp]
theorem coe_monoidIncl (g : G) : (E.monoidIncl g : Γ) = E.incl g :=
  (rfl)

theorem monoidIncl_injective : Function.Injective E.monoidIncl := fun _ _ h ↦
  E.incl_injective (congrArg Subtype.val h)

/-- Elements of `E.monoid` of degree `n : ℕ`. -/
abbrev fiber (n : ℕ) : Type _ :=
  {γ : E.monoid // E.degree γ.1 = n}

theorem fiber_nonempty (n : ℕ) : Nonempty (E.fiber n) := by
  obtain ⟨x, hx⟩ := E.proj_surjective (Multiplicative.ofAdd (n : ℤ))
  have hdeg : E.degree x = n := by
    simp [degree, hx]
  exact ⟨⟨⟨x, by rw [mem_monoid, hdeg]; exact Int.natCast_nonneg n⟩, hdeg⟩⟩

/-- Conjugation of an element of `E.monoid` by `g : G`. -/
def conj (g : G) (γ : E.monoid) : E.monoid :=
  ⟨E.incl g * γ.1 * (E.incl g)⁻¹, by
    rw [mem_monoid, degree_mul, degree_mul, degree_inv, degree_incl, zero_add, neg_zero, add_zero]
    exact γ.2⟩

@[simp]
theorem coe_conj (g : G) (γ : E.monoid) : (E.conj g γ : Γ) = E.incl g * γ.1 * (E.incl g)⁻¹ :=
  (rfl)

theorem conj_eq_monoidIncl_mul (g : G) (γ : E.monoid) :
    E.conj g γ = E.monoidIncl g * γ * E.monoidIncl g⁻¹ :=
  Subtype.ext (by simp [map_inv])

@[simp]
theorem conj_one (γ : E.monoid) : E.conj 1 γ = γ :=
  Subtype.ext (by simp)

theorem conj_mul (g h : G) (γ : E.monoid) : E.conj (g * h) γ = E.conj g (E.conj h γ) :=
  Subtype.ext (by simp [mul_assoc])

theorem degree_conj (g : G) (γ : E.monoid) : E.degree (E.conj g γ).1 = E.degree γ.1 := by
  simp

theorem conj_eq_self_iff (g : G) (γ : E.monoid) :
    E.conj g γ = γ ↔ g ∈ E.monoidIncl.centralizerSubgroup γ := by
  rw [MonoidHom.mem_centralizerSubgroup, Subtype.ext_iff, Subtype.ext_iff]
  change E.incl g * γ.1 * (E.incl g)⁻¹ = γ.1 ↔ E.incl g * γ.1 = γ.1 * E.incl g
  constructor
  · intro h
    calc E.incl g * γ.1 = E.incl g * γ.1 * (E.incl g)⁻¹ * E.incl g := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = γ.1 * E.incl g := by rw [h]
  · intro h
    rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem monoidIncl_mul_conj (g : G) (γ : E.monoid) :
    E.monoidIncl g⁻¹ * E.conj g γ = γ * E.monoidIncl g⁻¹ :=
  Subtype.ext (by simp [mul_assoc])

/-- Conjugation by `g : G` on the degree-`n` fiber `E.fiber n`. -/
def conjFiber (g : G) {n : ℕ} (γ : E.fiber n) : E.fiber n :=
  ⟨E.conj g γ.1, by simp [γ.2]⟩

@[simp]
theorem coe_conjFiber (g : G) {n : ℕ} (γ : E.fiber n) : (E.conjFiber g γ).1 = E.conj g γ.1 :=
  (rfl)

@[simp]
theorem conjFiber_one {n : ℕ} (γ : E.fiber n) : E.conjFiber 1 γ = γ :=
  Subtype.ext (E.conj_one γ.1)

theorem conjFiber_mul (g h : G) {n : ℕ} (γ : E.fiber n) :
    E.conjFiber (g * h) γ = E.conjFiber g (E.conjFiber h γ) :=
  Subtype.ext (E.conj_mul g h γ.1)

/-- The `G`-conjugacy equivalence relation on elements of degree `n`. -/
def conjSetoid (n : ℕ) : Setoid (E.fiber n) where
  r γ₁ γ₂ := ∃ g : G, E.conjFiber g γ₁ = γ₂
  iseqv :=
    { refl := fun γ ↦ ⟨1, E.conjFiber_one γ⟩
      symm := fun {γ₁ γ₂} ⟨g, hg⟩ ↦
        ⟨g⁻¹, by rw [← hg, ← E.conjFiber_mul, inv_mul_cancel, conjFiber_one]⟩
      trans := fun {γ₁ γ₂ γ₃} ⟨g, hg⟩ ⟨h, hh⟩ ↦ ⟨h * g, by rw [E.conjFiber_mul, hg, hh]⟩ }

theorem conjSetoid_iff {n : ℕ} {γ₁ γ₂ : E.fiber n} :
    (E.conjSetoid n).r γ₁ γ₂ ↔ ∃ g : G, E.conjFiber g γ₁ = γ₂ :=
  (Iff.rfl)

/-- The set of `G`-conjugacy classes of elements of degree `n` in `E.monoid`. -/
abbrev ConjClasses (n : ℕ) : Type _ :=
  Quotient (E.conjSetoid n)

/-- Fixing any lift `γ₀` of degree `n`, `g ↦ E.monoidIncl g⁻¹ * γ₀` identifies `G` with
`E.fiber n`. -/
def fiberEquivOfRep {n : ℕ} (γ₀ : E.fiber n) : G ≃ E.fiber n where
  toFun g := ⟨E.monoidIncl g⁻¹ * γ₀.1, by simp [γ₀.2]⟩
  invFun γ := (E.exists_incl_mul_of_degree_eq (γ.2.trans γ₀.2.symm)).choose⁻¹
  left_inv g := by
    dsimp only
    have hdeg : E.degree (E.monoidIncl g⁻¹ * γ₀.1).1 = E.degree γ₀.1.1 := by simp [γ₀.2]
    have hspec := (E.exists_incl_mul_of_degree_eq hdeg).choose_spec
    have hmul : E.incl g⁻¹ * γ₀.1.1 =
        E.incl (E.exists_incl_mul_of_degree_eq hdeg).choose * γ₀.1.1 := hspec
    have hinj : g⁻¹ = (E.exists_incl_mul_of_degree_eq hdeg).choose :=
      E.incl_injective (mul_right_cancel hmul)
    rw [← hinj, inv_inv]
  right_inv γ := by
    apply Subtype.ext
    apply Subtype.ext
    have hspec := (E.exists_incl_mul_of_degree_eq (γ.2.trans γ₀.2.symm)).choose_spec
    change E.incl _⁻¹⁻¹ * γ₀.1 = γ.1
    rw [inv_inv, ← hspec]

instance fiber_finite [Finite G] (n : ℕ) : Finite (E.fiber n) :=
  Finite.of_equiv G (E.fiberEquivOfRep (E.fiber_nonempty n).some)

instance conjClasses_finite [Finite G] (n : ℕ) : Finite (E.ConjClasses n) :=
  Quotient.finite _

/-- Conjugation by an arbitrary element `x ∈ Γ` preserves the normal subgroup `G` and induces a
group automorphism `E.conjAut x : G ≃* G`. -/
def conjAut (x : Γ) : G ≃* G where
  toFun g :=
    (MonoidHom.mem_range.mp ((E.degree_eq_zero_iff (x * E.incl g * x⁻¹)).mp (by simp))).choose
  invFun g :=
    (MonoidHom.mem_range.mp ((E.degree_eq_zero_iff (x⁻¹ * E.incl g * x)).mp (by simp))).choose
  left_inv g := by
    apply E.incl_injective
    have h1 :=
      (MonoidHom.mem_range.mp
        ((E.degree_eq_zero_iff (x * E.incl g * x⁻¹)).mp (by simp))).choose_spec
    have h2 :=
      (MonoidHom.mem_range.mp
        ((E.degree_eq_zero_iff
          (x⁻¹ * E.incl (MonoidHom.mem_range.mp
            ((E.degree_eq_zero_iff (x * E.incl g * x⁻¹)).mp (by simp))).choose * x)).mp
          (by simp))).choose_spec
    rw [h2, h1]
    group
  right_inv g := by
    apply E.incl_injective
    have h1 :=
      (MonoidHom.mem_range.mp
        ((E.degree_eq_zero_iff (x⁻¹ * E.incl g * x)).mp (by simp))).choose_spec
    have h2 :=
      (MonoidHom.mem_range.mp
        ((E.degree_eq_zero_iff
          (x * E.incl (MonoidHom.mem_range.mp
            ((E.degree_eq_zero_iff (x⁻¹ * E.incl g * x)).mp (by simp))).choose * x⁻¹)).mp
          (by simp))).choose_spec
    rw [h2, h1]
    group
  map_mul' g₁ g₂ := by
    apply E.incl_injective
    have h1 :=
      (MonoidHom.mem_range.mp
        ((E.degree_eq_zero_iff (x * E.incl g₁ * x⁻¹)).mp (by simp))).choose_spec
    have h2 :=
      (MonoidHom.mem_range.mp
        ((E.degree_eq_zero_iff (x * E.incl g₂ * x⁻¹)).mp (by simp))).choose_spec
    have h12 :=
      (MonoidHom.mem_range.mp
        ((E.degree_eq_zero_iff (x * E.incl (g₁ * g₂) * x⁻¹)).mp (by simp))).choose_spec
    rw [h12, map_mul E.incl, map_mul E.incl, h1, h2]
    group

theorem incl_conjAut (x : Γ) (g : G) : E.incl (E.conjAut x g) = x * E.incl g * x⁻¹ :=
  (MonoidHom.mem_range.mp ((E.degree_eq_zero_iff (x * E.incl g * x⁻¹)).mp (by simp))).choose_spec

theorem mul_incl_eq (x : Γ) (g : G) : x * E.incl g = E.incl (E.conjAut x g) * x := by
  rw [E.incl_conjAut, mul_assoc, inv_mul_cancel, mul_one]

/-- The `Λ`-linear endomorphism of the coinvariants `P_G` induced by any element of degree `n`
in `E.monoid`. -/
def coinvariantsAction (Λ : Type*) [Ring Λ] (n : ℕ) (P : Type*) [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ E.monoid) P] [Module (MonoidAlgebra Λ G) P]
    [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain E.monoidIncl r • x) :
    Module.End Λ (Coinvariants Λ G P) :=
  let γ₀ := (E.fiber_nonempty n).some
  Coinvariants.mapOfTwisted (singleSMulEnd Λ γ₀.1 P) (E.conjAut γ₀.1.1) fun g p ↦ by
    simp only [singleSMulEnd_apply, hG, mapDomain_single, ← mul_smul, single_mul_single, mul_one]
    congr 2
    exact Subtype.ext (E.mul_incl_eq γ₀.1.1 g)

/-- On coinvariants, `E.coinvariantsAction Λ n P hG` is realized by left multiplication by ANY
degree-`n` element `γ : E.fiber n`. -/
theorem coinvariantsAction_mk (Λ : Type*) [Ring Λ] {n : ℕ} (γ : E.fiber n) (P : Type*)
    [AddCommGroup P] [Module Λ P] [Module (MonoidAlgebra Λ E.monoid) P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain E.monoidIncl r • x) (p : P) :
    E.coinvariantsAction Λ n P hG (Coinvariants.mk (Λ := Λ) (G := G) p) =
      Coinvariants.mk (Λ := Λ) (G := G) ((single γ.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) • p) := by
  let γ₀ := (E.fiber_nonempty n).some
  unfold coinvariantsAction
  rw [Coinvariants.mapOfTwisted_mk, singleSMulEnd_apply]
  obtain ⟨g, hg⟩ := E.exists_incl_mul_of_degree_eq (γ₀.2.trans γ.2.symm)
  have hγ : γ₀.1 = E.monoidIncl g * γ.1 := Subtype.ext hg
  conv_lhs => rw [hγ, ← mul_one (1 : Λ), ← single_mul_single, mul_smul]
  have hstep : (single (E.monoidIncl g) (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      ((single γ.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) • p) =
      (single g (1 : Λ) : MonoidAlgebra Λ G) •
        ((single γ.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) • p) := by
    rw [hG, mapDomain_single]
  rw [hstep, Coinvariants.mk_single_smul]

@[simp]
theorem coinvariantsAction_zero (Λ : Type*) [Ring Λ] (P : Type*) [AddCommGroup P] [Module Λ P]
    [Module (MonoidAlgebra Λ E.monoid) P] [Module (MonoidAlgebra Λ G) P]
    [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain E.monoidIncl r • x) :
    E.coinvariantsAction Λ 0 P hG = .id := by
  ext p
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [E.coinvariantsAction_mk Λ ⟨1, by simp⟩ P hG p]
  simp [← one_def]

theorem coinvariantsAction_add (Λ : Type*) [Ring Λ] (m n : ℕ) (P : Type*) [AddCommGroup P]
    [Module Λ P] [Module (MonoidAlgebra Λ E.monoid) P] [Module (MonoidAlgebra Λ G) P]
    [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain E.monoidIncl r • x) :
    E.coinvariantsAction Λ (m + n) P hG =
      (E.coinvariantsAction Λ m P hG).comp (E.coinvariantsAction Λ n P hG) := by
  obtain ⟨γ₁⟩ := E.fiber_nonempty m
  obtain ⟨γ₂⟩ := E.fiber_nonempty n
  let γ₁₂ : E.fiber (m + n) := ⟨γ₁.1 * γ₂.1, by simp [γ₁.2, γ₂.2]⟩
  ext p
  simp only [LinearMap.comp_apply]
  rw [E.coinvariantsAction_mk Λ γ₁₂ P hG, E.coinvariantsAction_mk Λ γ₂ P hG,
    E.coinvariantsAction_mk Λ γ₁ P hG]
  simp [γ₁₂, ← mul_smul, single_mul_single]

/-- The centralizer trace descends to `G`-conjugacy classes of degree `n` by Stacks
Lemma 64.15.3. -/
def centralizerTraceClass (Λ : Type*) [Ring Λ] [Finite G] (n : ℕ) (P : Type*) [AddCommGroup P]
    [Module (MonoidAlgebra Λ E.monoid) P] [Module (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain E.monoidIncl r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    E.ConjClasses n → TauCeti.cyclicQuotient ℤ Λ :=
  Quotient.lift (fun γ : E.fiber n ↦ LinearMap.centralizerTrace Λ E.monoidIncl γ.1 P hG)
    fun γ₁ γ₂ ⟨g, hg⟩ ↦ by
      have hconj : E.monoidIncl g * γ₁.1 = γ₂.1 * E.monoidIncl g := by
        apply Subtype.ext
        have h1 : E.incl g * γ₁.1.1 * (E.incl g)⁻¹ = γ₂.1.1 :=
          congrArg (fun x : E.fiber n ↦ x.1.1) hg
        calc E.incl g * γ₁.1.1 = E.incl g * γ₁.1.1 * (E.incl g)⁻¹ * E.incl g := by
              rw [mul_assoc, inv_mul_cancel, mul_one]
          _ = γ₂.1.1 * E.incl g := by rw [h1]
      exact (LinearMap.centralizerTrace_eq_of_conj E.monoidIncl g hconj P hG).symm

@[simp]
theorem centralizerTraceClass_mk (Λ : Type*) [Ring Λ] [Finite G] {n : ℕ} (γ : E.fiber n)
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra Λ E.monoid) P]
    [Module (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain E.monoidIncl r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    E.centralizerTraceClass Λ n P hG ⟦γ⟧ = LinearMap.centralizerTrace Λ E.monoidIncl γ.1 P hG :=
  (rfl)

/-- Over a commutative ring `A`, the scalar centralizer trace on `G`-conjugacy classes of degree
`n`. -/
def centralizerScalarTraceClass (A : Type*) [CommRing A] [Finite G] (n : ℕ) (P : Type*)
    [AddCommGroup P] [Module (MonoidAlgebra A E.monoid) P] [Module (MonoidAlgebra A G) P]
    (hG : ∀ (r : MonoidAlgebra A G) (x : P), r • x = mapDomain E.monoidIncl r • x)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (c : E.ConjClasses n) : A :=
  cyclicQuotientEquivSelf A (E.centralizerTraceClass A n P hG c)

@[simp]
theorem centralizerScalarTraceClass_mk (A : Type*) [CommRing A] [Finite G] {n : ℕ} (γ : E.fiber n)
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra A E.monoid) P]
    [Module (MonoidAlgebra A G) P]
    (hG : ∀ (r : MonoidAlgebra A G) (x : P), r • x = mapDomain E.monoidIncl r • x)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P] :
    E.centralizerScalarTraceClass A n P hG ⟦γ⟧ =
      LinearMap.centralizerScalarTrace A E.monoidIncl γ.1 P hG :=
  (rfl)

private theorem coeff_single_one_mul {Λ : Type*} [Ring Λ] (s g : G) (x : MonoidAlgebra Λ G) :
    (single s (1 : Λ) * x).coeff (s * g) = x.coeff g := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp [mul_add, coeff_add, h₁, h₂]
  | single h a =>
    rw [single_mul_single, one_mul, coeff_single, coeff_single]
    by_cases hgh : h = g
    · simp [hgh]
    · have hneq : s * h ≠ s * g := fun heq ↦ hgh (mul_left_cancel heq)
      simp [Finsupp.single_eq_of_ne (Ne.symm hneq), Finsupp.single_eq_of_ne (Ne.symm hgh)]

/-- Simplified retract formula for `centralizerTrace` in a `MonoidExtension`, using normality of
`G` to evaluate at `Pi.single k 1` and conjugate `γ` by coset representatives `q.out`. -/
theorem centralizerTrace_eq_of_retract {Λ : Type*} [Ring Λ] (γ : E.monoid)
    [(E.monoidIncl.centralizerSubgroup γ).FiniteIndex]
    [Fintype (G ⧸ (E.monoidIncl.centralizerSubgroup γ).subtype.range)]
    (P : Type*) [AddCommGroup P] [Module (MonoidAlgebra Λ E.monoid) P]
    [Module (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain E.monoidIncl r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    {m : ℕ} (i : P →ₗ[MonoidAlgebra Λ G] (Fin m → MonoidAlgebra Λ G))
    (r : (Fin m → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] P) (hr : r ∘ₗ i = .id) :
    LinearMap.centralizerTrace Λ E.monoidIncl γ P hG =
      (commutatorSubmodule ℤ Λ).mkQ
        (∑ k : Fin m, ∑ q : G ⧸ (E.monoidIncl.centralizerSubgroup γ).subtype.range,
          (i ((single (E.conj q.out γ) (1 : Λ) : MonoidAlgebra Λ E.monoid) •
            r (Pi.single k 1)) k).coeff 1) := by
  rw [LinearMap.centralizerTrace_eq_of_retract E.monoidIncl γ P hG i r hr]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  have hpi : (Pi.single k (single q.out⁻¹ (1 : Λ)) : Fin m → MonoidAlgebra Λ G) =
      single q.out⁻¹ (1 : Λ) • Pi.single k (1 : MonoidAlgebra Λ G) := by
    ext j
    by_cases hjk : j = k <;> simp [hjk]
  rw [hpi, r.map_smul, hG, mapDomain_single, ← mul_smul, single_mul_single, mul_one]
  conv_lhs => rw [← E.monoidIncl_mul_conj q.out γ, ← mul_one (1 : Λ), ← single_mul_single, mul_smul]
  have hpull : (single (E.monoidIncl q.out⁻¹) (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      ((single (E.conj q.out γ) (1 : Λ) : MonoidAlgebra Λ E.monoid) • r (Pi.single k 1)) =
      (single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
        ((single (E.conj q.out γ) (1 : Λ) : MonoidAlgebra Λ E.monoid) • r (Pi.single k 1)) := by
    rw [hG, mapDomain_single]
  rw [hpull, i.map_smul, Pi.smul_apply, smul_eq_mul]
  have hc := coeff_single_one_mul q.out⁻¹ (1 : G)
    (i ((single (E.conj q.out γ) (1 : Λ) : MonoidAlgebra Λ E.monoid) • r (Pi.single k 1)) k)
  rw [mul_one] at hc
  exact hc

/-- Orbit-stabilizer decomposition of the degree-`n` fiber into `G`-conjugacy classes and cosets
of centralizers. -/
def fiberOrbitEquiv (n : ℕ) :
    (Σ c : E.ConjClasses n,
      G ⧸ (E.monoidIncl.centralizerSubgroup c.out.1).subtype.range) ≃ E.fiber n :=
  Equiv.ofBijective (fun p ↦ E.conjFiber p.2.out p.1.out) <| by
    constructor
    · rintro ⟨c₁, q₁⟩ ⟨c₂, q₂⟩ h
      dsimp only at h
      have hc : c₁ = c₂ := by
        rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
        apply Quotient.sound
        exact ⟨q₂.out⁻¹ * q₁.out, by
          rw [E.conjFiber_mul, h, ← E.conjFiber_mul, inv_mul_cancel, E.conjFiber_one]⟩
      subst hc
      have hfix : E.conj (q₂.out⁻¹ * q₁.out) c₁.out.1 = c₁.out.1 := by
        have h' : E.conjFiber (q₂.out⁻¹ * q₁.out) c₁.out = c₁.out := by
          rw [E.conjFiber_mul, h, ← E.conjFiber_mul, inv_mul_cancel, E.conjFiber_one]
        exact congrArg Subtype.val h'
      have hmem :
          q₂.out⁻¹ * q₁.out ∈ (E.monoidIncl.centralizerSubgroup c₁.out.1).subtype.range :=
        ⟨⟨q₂.out⁻¹ * q₁.out, (E.conj_eq_self_iff _ _).mp hfix⟩, rfl⟩
      have hq : q₁ = q₂ := by
        rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
        exact (QuotientGroup.eq.mpr hmem).symm
      rw [hq]
    · intro γ
      let c : E.ConjClasses n := ⟦γ⟧
      have hc : (E.conjSetoid n).r c.out γ := Quotient.exact (Quotient.out_eq c)
      obtain ⟨g, hg⟩ := hc
      let q : G ⧸ (E.monoidIncl.centralizerSubgroup c.out.1).subtype.range := QuotientGroup.mk g
      refine ⟨⟨c, q⟩, ?_⟩
      dsimp only
      have hmem : q.out⁻¹ * g ∈ (E.monoidIncl.centralizerSubgroup c.out.1).subtype.range :=
        QuotientGroup.eq.mp (Quotient.out_eq q)
      rcases hmem with ⟨z, hz⟩
      have hfix : E.conjFiber (q.out⁻¹ * g) c.out = c.out := by
        apply Subtype.ext
        rw [← hz]
        exact (E.conj_eq_self_iff z.1 c.out.1).mpr z.2
      calc E.conjFiber q.out c.out
          = E.conjFiber q.out (E.conjFiber (q.out⁻¹ * g) c.out) := by rw [hfix]
        _ = E.conjFiber (q.out * (q.out⁻¹ * g)) c.out := (E.conjFiber_mul _ _ _).symm
        _ = E.conjFiber g c.out := by rw [mul_inv_cancel_left]
        _ = γ := hg

/-- **Stacks Lemma 64.15.5.** For a finite group `G` and any `n : ℕ`, the Hattori–Stallings trace
of the degree-`n` action on the coinvariants `P_G` equals the sum of the centralizer traces over
all `G`-conjugacy classes of elements of degree `n` in `E.monoid`. -/
theorem hattoriStallingsTrace_coinvariantsAction {Λ : Type*} [Ring Λ] [Finite G] (n : ℕ)
    (P : Type*) [AddCommGroup P] [Module Λ P] [Module (MonoidAlgebra Λ E.monoid) P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) P]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain E.monoidIncl r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := P)).1
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := P)).2
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G P) (E.coinvariantsAction Λ n P hG) =
      ∑ᶠ c : E.ConjClasses n, E.centralizerTraceClass Λ n P hG c := by
  classical
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := P)).1
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := P)).2
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (E.ConjClasses n) := Fintype.ofFinite _
  have : Fintype (E.fiber n) := Fintype.ofFinite _
  obtain ⟨m, r, i, -, -, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  let iG : Coinvariants Λ G P →ₗ[Λ] (Fin m → Λ) :=
    (Coinvariants.piSelfEquiv Λ G m).toLinearMap ∘ₗ Coinvariants.map i
  let rG : (Fin m → Λ) →ₗ[Λ] Coinvariants Λ G P :=
    Coinvariants.map r ∘ₗ (Coinvariants.piSelfEquiv Λ G m).symm.toLinearMap
  have hrG : rG ∘ₗ iG = .id := by
    ext p
    simp only [LinearMap.comp_apply, LinearMap.id_apply, iG, rG, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Coinvariants.map_mk]
    have hp : r (i p) = p := congrArg (fun g : Module.End (MonoidAlgebra Λ G) P ↦ g p) hr
    rw [hp]
  let γ₀ : E.fiber n := (E.fiber_nonempty n).some
  rw [LinearMap.hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin m)) iG rG hrG,
    Basis.hattoriStallingsTrace_apply, finsum_eq_sum_of_fintype]
  have hRHS : ∀ c : E.ConjClasses n,
      E.centralizerTraceClass Λ n P hG c =
        (commutatorSubmodule ℤ Λ).mkQ
          (∑ k : Fin m,
            ∑ q : G ⧸ (E.monoidIncl.centralizerSubgroup c.out.1).subtype.range,
              (i ((single (E.conj q.out c.out.1) (1 : Λ) : MonoidAlgebra Λ E.monoid) •
                r (Pi.single k 1)) k).coeff 1) := by
    intro c
    have hc : c = ⟦c.out⟧ := (Quotient.out_eq c).symm
    conv_lhs => rw [hc, E.centralizerTraceClass_mk]
    exact E.centralizerTrace_eq_of_retract c.out.1 P hG i r hr
  simp_rw [hRHS]
  rw [← map_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hLHS :
      (Pi.basisFun Λ (Fin m)).repr
        ((iG ∘ₗ E.coinvariantsAction Λ n P hG ∘ₗ rG) (Pi.basisFun Λ (Fin m) k)) k =
      augmentation Λ G
        (i ((single γ₀.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) • r (Pi.single k 1)) k) := by
    simp only [Pi.basisFun_repr, Pi.basisFun_apply, LinearMap.comp_apply, iG, rG,
      LinearEquiv.coe_coe, Coinvariants.piSelfEquiv_symm_single, Coinvariants.map_mk]
    have h1 : (single (1 : G) (1 : Λ) : MonoidAlgebra Λ G) = 1 := one_def.symm
    rw [h1, E.coinvariantsAction_mk Λ γ₀ P hG, Coinvariants.map_mk, Coinvariants.piSelfEquiv_mk]
  rw [hLHS]
  have haug : ∀ x : MonoidAlgebra Λ G, augmentation Λ G x = ∑ g : G, x.coeff g := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => simp [map_add, coeff_add, h₁, h₂, Finset.sum_add_distrib]
    | single h a =>
      rw [augmentation_single, Finset.sum_eq_single h]
      · simp
      · intro g _ hgh
        rw [coeff_single, Finsupp.single_eq_of_ne hgh]
      · intro hh
        exact absurd (Finset.mem_univ h) hh
  rw [haug]
  let F : (Σ c : E.ConjClasses n,
      G ⧸ (E.monoidIncl.centralizerSubgroup c.out.1).subtype.range) → Λ := fun p ↦
    (i ((single (E.conj p.2.out p.1.out.1) (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      r (Pi.single k 1)) k).coeff 1
  have hsig :
      (∑ c : E.ConjClasses n,
        ∑ q : G ⧸ (E.monoidIncl.centralizerSubgroup c.out.1).subtype.range, F ⟨c, q⟩) =
      ∑ p, F p :=
    (Fintype.sum_sigma F).symm
  change ∑ g : G, (i ((single γ₀.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      r (Pi.single k 1)) k).coeff g =
    ∑ c : E.ConjClasses n,
      ∑ q : G ⧸ (E.monoidIncl.centralizerSubgroup c.out.1).subtype.range, F ⟨c, q⟩
  rw [hsig]
  rw [Fintype.sum_equiv (E.fiberOrbitEquiv n) F
    (fun γ : E.fiber n ↦ (i ((single γ.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      r (Pi.single k 1)) k).coeff 1) (fun _ ↦ rfl)]
  rw [← Fintype.sum_equiv (E.fiberEquivOfRep γ₀)
    (fun g : G ↦ (i ((single γ₀.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      r (Pi.single k 1)) k).coeff g) _]
  intro g
  change (i ((single γ₀.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) • r (Pi.single k 1)) k).coeff g =
    (i ((single (E.monoidIncl g⁻¹ * γ₀.1) (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      r (Pi.single k 1)) k).coeff 1
  conv_rhs => rw [← mul_one (1 : Λ), ← single_mul_single, mul_smul]
  have hpull : (single (E.monoidIncl g⁻¹) (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      ((single γ₀.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) • r (Pi.single k 1)) =
      (single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
        ((single γ₀.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) • r (Pi.single k 1)) := by
    rw [hG, mapDomain_single]
  rw [hpull, i.map_smul, Pi.smul_apply, smul_eq_mul]
  have hc := coeff_single_one_mul g⁻¹ g
    (i ((single γ₀.1 (1 : Λ) : MonoidAlgebra Λ E.monoid) • r (Pi.single k 1)) k)
  rw [inv_mul_cancel] at hc
  exact hc.symm

/-- Degree-`1` specialization of Stacks Lemma 64.15.5. -/
theorem hattoriStallingsTrace_coinvariantsAction_one {Λ : Type*} [Ring Λ] [Finite G]
    (P : Type*) [AddCommGroup P] [Module Λ P] [Module (MonoidAlgebra Λ E.monoid) P]
    [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) P]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    (hG : ∀ (r : MonoidAlgebra Λ G) (x : P), r • x = mapDomain E.monoidIncl r • x)
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := P)).1
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := P)).2
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G P) (E.coinvariantsAction Λ 1 P hG) =
      ∑ᶠ c : E.ConjClasses 1, E.centralizerTraceClass Λ 1 P hG c :=
  E.hattoriStallingsTrace_coinvariantsAction 1 P hG

end MonoidExtension

end TauCeti
