/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.AdicCompletion.AlgHom
import Mathlib.RingTheory.Nilpotent.Basic
import TauCeti.RingTheory.AdicCompletion.LocalRing

/-!
# Adic completion at a maximal ideal and localization

Let `R` be a commutative ring and `p` a maximal ideal of `R`. Every localization `Rₚ` of `R` at
`p` has the same quotients by the powers of its maximal ideal as `R` has by the powers of `p`
(`IsLocalization.AtPrime.equivQuotMaximalIdealPow`). Passing to projective limits identifies the
`p`-adic completion of `R` with the maximal-ideal-adic completion of `Rₚ`, without any Noetherian
or finite-generation assumption on `R` or `p`.

We also show that for any ideal `I`, an element of `AdicCompletion I R` is a unit if and only if
its reduction in `R ⧸ I` is a unit. Consequently `AdicCompletion p R` is a local ring for every
maximal ideal `p`, with maximal ideal the kernel of the reduction map `AdicCompletion p R → R ⧸ p`.
When `R` is Noetherian, combining the localization comparison with the dimension and regularity
invariance of local completions (`TauCeti.AdicCompletion.ringKrullDim_eq` and
`TauCeti.AdicCompletion.isRegularLocalRing_iff`) shows that `AdicCompletion p R` has the same
Krull dimension as `Localization.AtPrime p` and is regular if and only if `Localization.AtPrime p`
is regular.

## Main definitions and results

* `AdicCompletion.isUnit_iff_isUnit_evalOneₐ`: an element of `AdicCompletion I R` is a unit if and
  only if its image in `R ⧸ I` is a unit.
* `AdicCompletion.instIsLocalRingOfIsMaximal`: for a maximal ideal `p`, `AdicCompletion p R` is a
  local ring, with maximal ideal `RingHom.ker (evalOneₐ p)`
  (`AdicCompletion.maximalIdeal_eq_ker_evalOneₐ`).
* `AdicCompletion.mapₐ_toAlgHom_bijective` and `AdicCompletion.atPrimeEquiv`: for a maximal ideal
  `p` and a localization `Rₚ` at `p`, the canonical map
  `AdicCompletion p R →ₐ[A] AdicCompletion (IsLocalRing.maximalIdeal Rₚ) Rₚ` is an isomorphism.
* `TauCeti.AdicCompletion.ringKrullDim_eq_of_isLocalization_atPrime`,
  `TauCeti.AdicCompletion.ringKrullDim_eq_atPrime`: over a Noetherian ring, `AdicCompletion p R`
  has the same Krull dimension as `Rₚ` (in particular `Localization.AtPrime p`).
* `TauCeti.AdicCompletion.isRegularLocalRing_iff_of_isLocalization_atPrime`,
  `TauCeti.AdicCompletion.isRegularLocalRing_iff_atPrime`: over a Noetherian ring,
  `AdicCompletion p R` is a regular local ring if and only if `Rₚ` (in particular
  `Localization.AtPrime p`) is.

## References

* M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
* [Stacks Project, Section 10.97](https://stacks.math.columbia.edu/tag/07N9).
-/

public section

namespace AdicCompletion

section UnitsAndLocalRing

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- An element of `R ⧸ I ^ n` whose reduction modulo `I` is a unit is itself a unit, because the
kernel of `R ⧸ I ^ n → R ⧸ I` is nilpotent. -/
private theorem isUnit_evalₐ_of_isUnit_evalOneₐ {x : AdicCompletion I R}
    (hx : IsUnit (evalOneₐ I x)) (n : ℕ) : IsUnit (evalₐ I n x) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : Subsingleton (R ⧸ I ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact isUnit_of_subsingleton _
  · obtain ⟨u, hu⟩ := hx
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : R ⧸ I)
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    -- In `R ⧸ I`, `s * r = 1`, so `1 - s * r ∈ I`, hence `(1 - s * r) ^ n ∈ I ^ n`.
    have hmod : Ideal.Quotient.mk I (1 - s * r) = 0 := by
      have hfac := factor_evalₐ (I := I) (Nat.one_le_iff_ne_zero.mpr hn) x
      have hsr : Ideal.Quotient.mk I s * Ideal.Quotient.mk I r = 1 := by
        have h1 : Ideal.Quotient.mk I s = evalOneₐ I x := by
          rw [← factorₐ_evalₐ_one, ← hfac, ← hs]
          rfl
        rw [h1, hr, ← hu]
        exact Units.mul_inv u
      rw [map_sub, map_one, map_mul, hsr, sub_self]
    have hnil : IsNilpotent (Ideal.Quotient.mk (I ^ n) (1 - s * r)) :=
      ⟨n, by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow (Ideal.Quotient.eq_zero_iff_mem.mp hmod) n⟩
    have hu_prod : IsUnit (Ideal.Quotient.mk (I ^ n) s * Ideal.Quotient.mk (I ^ n) r) := by
      have hsub : Ideal.Quotient.mk (I ^ n) s * Ideal.Quotient.mk (I ^ n) r =
          1 - Ideal.Quotient.mk (I ^ n) (1 - s * r) := by
        rw [← map_mul, ← map_one (Ideal.Quotient.mk (I ^ n)), ← map_sub, sub_sub_cancel]
      rw [hsub]
      exact hnil.isUnit_one_sub
    rw [← hs]
    exact isUnit_of_mul_isUnit_left hu_prod

/-- An element of `AdicCompletion I R` is a unit if and only if its projection in `R ⧸ I` is a
unit. Neither finite generation of `I` nor Noetherianity of `R` is required. -/
theorem isUnit_iff_isUnit_evalOneₐ {x : AdicCompletion I R} :
    IsUnit x ↔ IsUnit (evalOneₐ I x) := by
  refine ⟨fun h ↦ h.map (evalOneₐ I), fun hx ↦ ?_⟩
  -- Each level `evalₐ I n x` is a unit; uniqueness of inverses makes their inverses compatible.
  choose u hu using fun n ↦ isUnit_evalₐ_of_isUnit_evalOneₐ I hx n
  choose r hr using fun n ↦ Ideal.Quotient.mk_surjective (↑(u n)⁻¹ : R ⧸ I ^ n)
  have hcompat {m n : ℕ} (hmn : m ≤ n) :
      Ideal.Quotient.factorPow I hmn (↑(u n)⁻¹) = ↑(u m)⁻¹ := by
    apply Units.eq_inv_of_mul_eq_one_left
    have hmul : Ideal.Quotient.factorPow I hmn (u n * ↑(u n)⁻¹) = 1 := by
      rw [Units.mul_inv, map_one]
    rwa [map_mul, hu n, Ideal.Quotient.factorPow, factor_evalₐ hmn, ← hu m] at hmul
  let c : AdicCauchySequence I R := ⟨r, fun {m n} hmn ↦ by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hr m]
    simpa [← hr n, Ideal.Quotient.factorPow] using (hcompat hmn).symm⟩
  refine isUnit_iff_exists_inv.mpr ⟨mk I R c, ext_evalₐ fun n ↦ ?_⟩
  rw [map_mul, map_one, evalₐ_mk, hr n, ← hu n, Units.mul_inv]

/-- The completion of a commutative ring at a maximal ideal is a local ring, without any
finite-generation or Noetherian hypothesis. -/
instance instIsLocalRingOfIsMaximal (p : Ideal R) [p.IsMaximal] :
    IsLocalRing (AdicCompletion p R) := by
  let _ : Field (R ⧸ p) := Ideal.Quotient.field p
  have : Nontrivial (AdicCompletion p R) :=
    (evalOneₐ_surjective p).nontrivial
  refine IsLocalRing.of_nonunits_add fun x y hx hy ↦ ?_
  rw [mem_nonunits_iff, isUnit_iff_isUnit_evalOneₐ, isUnit_iff_ne_zero, not_not] at hx hy ⊢
  rw [map_add, hx, hy, add_zero]

/-- For a maximal ideal `p`, the maximal ideal of `AdicCompletion p R` is the kernel of the
canonical projection `AdicCompletion p R →ₐ[R] R ⧸ p`. -/
theorem maximalIdeal_eq_ker_evalOneₐ (p : Ideal R) [p.IsMaximal] :
    IsLocalRing.maximalIdeal (AdicCompletion p R) = RingHom.ker (evalOneₐ p) := by
  let _ : Field (R ⧸ p) := Ideal.Quotient.field p
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_isUnit_evalOneₐ,
    isUnit_iff_ne_zero, not_not, RingHom.mem_ker]

end UnitsAndLocalRing

section AtPrime

variable (A : Type*) [CommRing A] {R : Type*} [CommRing R] [Algebra A R]
variable (p : Ideal R) [p.IsMaximal]
variable (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [Algebra A Rₚ] [IsScalarTower A R Rₚ]
variable [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]

variable {A} in
/-- **Completions at a maximal ideal commute with localization.** For a maximal ideal `p` of `R`
and any localization `Rₚ` of `R` at `p`, the map of completions
`AdicCompletion p R →ₐ[A] AdicCompletion (IsLocalRing.maximalIdeal Rₚ) Rₚ` induced by
`R → Rₚ` is bijective. -/
theorem mapₐ_toAlgHom_bijective
    (hp : p ≤ (IsLocalRing.maximalIdeal Rₚ).comap (IsScalarTower.toAlgHom A R Rₚ)) :
    Function.Bijective (mapₐ (IsScalarTower.toAlgHom A R Rₚ) hp) := by
  refine mapₐ_bijective _ hp fun n ↦ ?_
  have heq : Ideal.quotientMap (IsLocalRing.maximalIdeal Rₚ ^ n)
      (IsScalarTower.toAlgHom A R Rₚ).toRingHom
      ((Ideal.pow_right_mono hp n).trans (Ideal.le_comap_pow _ n)) =
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ n).toRingHom := by
    ext x
    simp
  rw [heq]
  exact (IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ n).bijective

/-- **Canonical isomorphism between the completion at a maximal ideal and the completion of its
localization.** For a maximal ideal `p` of an `A`-algebra `R` and a localization `Rₚ` of `R` at
`p`, the localization map induces an `A`-algebra isomorphism
`AdicCompletion p R ≃ₐ[A] AdicCompletion (IsLocalRing.maximalIdeal Rₚ) Rₚ`. -/
noncomputable def atPrimeEquiv :
    AdicCompletion p R ≃ₐ[A] AdicCompletion (IsLocalRing.maximalIdeal Rₚ) Rₚ :=
  have hp : p ≤ (IsLocalRing.maximalIdeal Rₚ).comap (IsScalarTower.toAlgHom A R Rₚ) := by
    rw [← Ideal.map_le_iff_le_comap]
    exact (IsLocalization.AtPrime.map_eq_maximalIdeal p Rₚ).le
  AlgEquiv.ofBijective (mapₐ (IsScalarTower.toAlgHom A R Rₚ) hp) (mapₐ_toAlgHom_bijective p Rₚ hp)

/-- As an algebra homomorphism, `atPrimeEquiv A p Rₚ` is `mapₐ` of the localization map. -/
@[simp]
theorem toAlgHom_atPrimeEquiv :
    (atPrimeEquiv A p Rₚ :
        AdicCompletion p R →ₐ[A] AdicCompletion (IsLocalRing.maximalIdeal Rₚ) Rₚ) =
      mapₐ (IsScalarTower.toAlgHom A R Rₚ)
        (Ideal.map_le_iff_le_comap.mp (IsLocalization.AtPrime.map_eq_maximalIdeal p Rₚ).le) :=
  AlgHom.ext fun _ ↦ rfl

/-- `atPrimeEquiv` extends `algebraMap R Rₚ` along the canonical maps into the completions. -/
@[simp]
theorem atPrimeEquiv_of (x : R) :
    atPrimeEquiv A p Rₚ (of p R x) =
      of (IsLocalRing.maximalIdeal Rₚ) Rₚ (algebraMap R Rₚ x) := by
  change mapₐ _ _ (of p R x) = _
  simp

/-- Modulo the `n`-th power of the maximal ideal, `atPrimeEquiv` is
`IsLocalization.AtPrime.equivQuotMaximalIdealPow`. -/
@[simp]
theorem evalₐ_atPrimeEquiv (n : ℕ) (x : AdicCompletion p R) :
    evalₐ (IsLocalRing.maximalIdeal Rₚ) n (atPrimeEquiv A p Rₚ x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ n (evalₐ p n x) := by
  change evalₐ _ n (mapₐ _ _ x) = _
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ p n x)
  simp [← hr]

/-- On images of elements of `R`, the inverse of `atPrimeEquiv` recovers `of p R`. -/
@[simp]
theorem atPrimeEquiv_symm_of_algebraMap (x : R) :
    (atPrimeEquiv A p Rₚ).symm (of (IsLocalRing.maximalIdeal Rₚ) Rₚ (algebraMap R Rₚ x)) =
      of p R x := by
  rw [← atPrimeEquiv_of A p Rₚ x, AlgEquiv.symm_apply_apply]

end AtPrime

end AdicCompletion

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsMaximal]

/-- Over a Noetherian ring, the completion at a maximal ideal `p` has the same Krull dimension as
any localization `Rₚ` of `R` at `p`. -/
theorem ringKrullDim_eq_of_isLocalization_atPrime (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    ringKrullDim (_root_.AdicCompletion p R) = ringKrullDim Rₚ := by
  have : IsNoetherianRing Rₚ := IsLocalization.isNoetherianRing p.primeCompl Rₚ ‹_›
  rw [ringKrullDim_eq_of_ringEquiv (_root_.AdicCompletion.atPrimeEquiv R p Rₚ).toRingEquiv,
    TauCeti.AdicCompletion.ringKrullDim_eq]

/-- Over a Noetherian ring, the completion at a maximal ideal `p` has the same Krull dimension as
`Localization.AtPrime p`. -/
theorem ringKrullDim_eq_atPrime :
    ringKrullDim (_root_.AdicCompletion p R) = ringKrullDim (Localization.AtPrime p) :=
  ringKrullDim_eq_of_isLocalization_atPrime p (Localization.AtPrime p)

/-- Over a Noetherian ring, the completion at a maximal ideal `p` is a regular local ring if and
only if a localization `Rₚ` of `R` at `p` is a regular local ring. -/
theorem isRegularLocalRing_iff_of_isLocalization_atPrime (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    IsRegularLocalRing (_root_.AdicCompletion p R) ↔ IsRegularLocalRing Rₚ := by
  have : IsNoetherianRing Rₚ := IsLocalization.isNoetherianRing p.primeCompl Rₚ ‹_›
  let e := (_root_.AdicCompletion.atPrimeEquiv R p Rₚ).toRingEquiv
  exact ⟨fun _ ↦ TauCeti.AdicCompletion.isRegularLocalRing_iff.mp (.of_ringEquiv e),
    fun h ↦ have := TauCeti.AdicCompletion.isRegularLocalRing_iff.mpr h; .of_ringEquiv e.symm⟩

/-- Over a Noetherian ring, the completion at a maximal ideal `p` is a regular local ring if and
only if `Localization.AtPrime p` is a regular local ring. -/
theorem isRegularLocalRing_iff_atPrime :
    IsRegularLocalRing (_root_.AdicCompletion p R) ↔
      IsRegularLocalRing (Localization.AtPrime p) :=
  isRegularLocalRing_iff_of_isLocalization_atPrime p (Localization.AtPrime p)

end TauCeti.AdicCompletion
