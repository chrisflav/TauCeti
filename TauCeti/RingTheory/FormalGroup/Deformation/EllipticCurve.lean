/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Char.Two
public import TauCeti.RingTheory.FormalGroup.Deformation.Automorphism
-- Proof-only: characteristic-2 arithmetic, perfect finite fields, and invariant differential.
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Perfect
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
import TauCeti.RingTheory.FormalGroup.Basic
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Universal deformation of a height-two elliptic curve in characteristic two

Following Lubin and Tate (§3.5), let `k` be a field of characteristic `2` and consider the
supersingular elliptic curve `E₀ : Y² + Y = X³` over `k`
(`WeierstrassCurve.supersingularCharTwoCurve`), whose formal group law `E₀.formalGroup` has
height `2`. Over `R⟦t⟧ = MvPowerSeries (Fin 1) R`, the Weierstrass curve

`E_t : Y² + t X Y + Y = X³`

(`WeierstrassCurve.lubinTateEllipticCurve`) defines a formal group law `Γ := E_t.formalGroup`
lifting `E₀.formalGroup` along `ρ ∘ constantCoeff` for any `ρ : R →+* k`. Because the `XY`
coefficient of any Weierstrass formal group law is `-a₁`
(`WeierstrassCurve.coeff_single_zero_add_single_one_formalGroup`), the partial-derivative cocycle
`derivCocycle Γ ρ E₀.formalGroup 0` has order `≥ 2` with degree-`2` homogeneous component
`lazardCocycle 2 k`. Applying `FormalGroup.isUniversal_of_derivCocycle` and `FormalGroup.liftAut`
shows that `E_t.formalGroup` is a universal deformation of `E₀.formalGroup` and carries the action
of `Aut_k(E₀.formalGroup)` by `R`-algebra automorphisms of `R⟦t⟧`. Specializing `R` to
`WittVector 2 k` (and in particular `W(𝔽₄)`, using `GaloisField 2 2`) recovers the classical
height-two elliptic Lubin–Tate example over `W(𝔽₄)⟦t⟧`.

## Main definitions

* `WeierstrassCurve.supersingularCharTwoCurve`: the elliptic curve `Y² + Y = X³` (`a₃ = 1`,
  other `aᵢ = 0`), of height `2` in characteristic `2`.
* `WeierstrassCurve.lubinTateEllipticCurve`: the deformation curve `Y² + t X Y + Y = X³` over
  `R⟦t⟧ = MvPowerSeries (Fin 1) R`.
* `FormalGroup.lubinTateEllipticCurveUniversalEquiv`: the universal deformation equivalence for
  `(lubinTateEllipticCurve R).formalGroup`.
* `FormalGroup.lubinTateEllipticCurveLiftAut`: action of `Aut_k(E₀.formalGroup)` on `R⟦t⟧`.

## Main results

* `WeierstrassCurve.coeff_single_zero_add_single_one_formalGroup`: for every Weierstrass curve `W`,
  the coefficient of `XY` in `(formalGroup W).toPowerSeries` is `-W.a₁`.
* `WeierstrassCurve.height_formalGroup_supersingularCharTwoCurve`: in characteristic `2`, the
  formal group law of `Y² + Y = X³` has height `2`.
* `FormalGroup.lubinTateEllipticCurve_universal_deformation`:
  `(lubinTateEllipticCurve R).formalGroup` is a universal deformation of
  `(supersingularCharTwoCurve k).formalGroup`.
* `FormalGroup.lubinTateEllipticCurveUniversalEquiv_wittVector` and
  `FormalGroup.lubinTateEllipticCurveLiftAut_wittVector`: specialization to `W(k)⟦t⟧` and
  `W(𝔽₄)⟦t⟧`.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §3.5.
-/

public section

noncomputable section

open MvPowerSeries TauCeti

namespace WeierstrassCurve

section General

variable {R : Type*} [CommRing R]

/-- The coefficient of `X Y` in the formal group law of any Weierstrass curve `W` is `-W.a₁`. -/
@[simp]
theorem coeff_single_zero_add_single_one_formalGroup (W : WeierstrassCurve R) :
    coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1)
        (formalGroup W).toPowerSeries =
      -W.a₁ := by
  have h := congrArg (PowerSeries.coeff 1) W.subst_pderiv_formalGroup
  rw [MvPowerSeries.coeff_subst_zero_X, coeff_pderiv] at h
  simp only [Finsupp.single_apply, one_ne_zero, ↓reduceIte, Nat.cast_zero, zero_add,
    mul_one, add_comm] at h
  have hw : formalW W = PowerSeries.X ^ 3 * formalU W := formalW_eq_X_pow_mul_formalU W
  have hxw : PowerSeries.X * formalW W = PowerSeries.X ^ 3 * (PowerSeries.X * formalU W) := by
    rw [hw]; ring
  have hww : formalW W ^ 2 = PowerSeries.X ^ 3 * (PowerSeries.X ^ 3 * formalU W ^ 2) := by
    rw [hw]; ring
  have hrhs : PowerSeries.coeff 1 W.formalInvariantDifferentialDenom = -W.a₁ := by
    rw [formalInvariantDifferentialDenom_def, hxw, hww, hw]
    simp [PowerSeries.coeff_X_pow_mul']
  exact h.trans hrhs

end General

section Curves

/-- The supersingular Weierstrass curve `Y² + Y = X³` (`a₃ = 1`, all other `aᵢ = 0`). -/
@[expose]
def supersingularCharTwoCurve (R : Type*) [CommRing R] : WeierstrassCurve R where
  a₁ := 0
  a₂ := 0
  a₃ := 1
  a₄ := 0
  a₆ := 0

/-- The `a₁` Weierstrass coefficient of `supersingularCharTwoCurve R` is `0`. -/
@[simp]
theorem supersingularCharTwoCurve_a₁ (R : Type*) [CommRing R] :
    (supersingularCharTwoCurve R).a₁ = 0 := rfl

/-- The `a₂` Weierstrass coefficient of `supersingularCharTwoCurve R` is `0`. -/
@[simp]
theorem supersingularCharTwoCurve_a₂ (R : Type*) [CommRing R] :
    (supersingularCharTwoCurve R).a₂ = 0 := rfl

/-- The `a₃` Weierstrass coefficient of `supersingularCharTwoCurve R` is `1`. -/
@[simp]
theorem supersingularCharTwoCurve_a₃ (R : Type*) [CommRing R] :
    (supersingularCharTwoCurve R).a₃ = 1 := rfl

/-- The `a₄` Weierstrass coefficient of `supersingularCharTwoCurve R` is `0`. -/
@[simp]
theorem supersingularCharTwoCurve_a₄ (R : Type*) [CommRing R] :
    (supersingularCharTwoCurve R).a₄ = 0 := rfl

/-- The `a₆` Weierstrass coefficient of `supersingularCharTwoCurve R` is `0`. -/
@[simp]
theorem supersingularCharTwoCurve_a₆ (R : Type*) [CommRing R] :
    (supersingularCharTwoCurve R).a₆ = 0 := rfl

/-- Base change preserves the supersingular curve `Y² + Y = X³`. -/
@[simp]
theorem map_supersingularCharTwoCurve {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    (supersingularCharTwoCurve R).map φ = supersingularCharTwoCurve S := by
  ext <;> simp

/-- The discriminant of `Y² + Y = X³` is `-27`. -/
theorem supersingularCharTwoCurve_Δ (R : Type*) [CommRing R] :
    (supersingularCharTwoCurve R).Δ = -27 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- Over a commutative ring of characteristic `2`, `Y² + Y = X³` has discriminant `1`, hence is
an elliptic curve. -/
instance isElliptic_supersingularCharTwoCurve (k : Type*) [CommRing k] [CharP k 2] :
    (supersingularCharTwoCurve k).IsElliptic where
  isUnit := by
    rw [supersingularCharTwoCurve_Δ]
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    have h1 : (-27 : k) = 1 := by
      calc (-27 : k) = -27 + 14 * (2 : k) := by rw [h2, mul_zero, add_zero]
        _ = 1 := by norm_num
    rw [h1]
    exact isUnit_one

/-- Over a field of characteristic `2`, the formal group law of `Y² + Y = X³` has height `2`. -/
theorem height_formalGroup_supersingularCharTwoCurve (k : Type*) [Field k] [CharP k 2] :
    (formalGroup (supersingularCharTwoCurve k)).height 2 = 2 :=
  (supersingularCharTwoCurve k).height_formalGroup_eq_two_iff_a₁_eq_zero_of_char_two.mpr rfl

/-- The universal deformation curve `E_t : Y² + t X Y + Y = X³` over `R⟦t⟧` (Lubin–Tate §3.5),
where `t = X 0 : MvPowerSeries (Fin 1) R`. -/
@[expose]
def lubinTateEllipticCurve (R : Type*) [CommRing R] :
    WeierstrassCurve (MvPowerSeries (Fin 1) R) where
  a₁ := X 0
  a₂ := 0
  a₃ := 1
  a₄ := 0
  a₆ := 0

/-- The `a₁` Weierstrass coefficient of `lubinTateEllipticCurve R` is `X 0`. -/
@[simp]
theorem lubinTateEllipticCurve_a₁ (R : Type*) [CommRing R] :
    (lubinTateEllipticCurve R).a₁ = X 0 := rfl

/-- The `a₂` Weierstrass coefficient of `lubinTateEllipticCurve R` is `0`. -/
@[simp]
theorem lubinTateEllipticCurve_a₂ (R : Type*) [CommRing R] :
    (lubinTateEllipticCurve R).a₂ = 0 := rfl

/-- The `a₃` Weierstrass coefficient of `lubinTateEllipticCurve R` is `1`. -/
@[simp]
theorem lubinTateEllipticCurve_a₃ (R : Type*) [CommRing R] :
    (lubinTateEllipticCurve R).a₃ = 1 := rfl

/-- The `a₄` Weierstrass coefficient of `lubinTateEllipticCurve R` is `0`. -/
@[simp]
theorem lubinTateEllipticCurve_a₄ (R : Type*) [CommRing R] :
    (lubinTateEllipticCurve R).a₄ = 0 := rfl

/-- The `a₆` Weierstrass coefficient of `lubinTateEllipticCurve R` is `0`. -/
@[simp]
theorem lubinTateEllipticCurve_a₆ (R : Type*) [CommRing R] :
    (lubinTateEllipticCurve R).a₆ = 0 := rfl

/-- Setting `t = 0` and reducing coefficients along `ρ : R →+* k` sends `Y² + t X Y + Y = X³` to
`Y² + Y = X³`. -/
@[simp]
theorem map_comp_constantCoeff_lubinTateEllipticCurve {R k : Type*} [CommRing R] [CommRing k]
    (ρ : R →+* k) :
    (lubinTateEllipticCurve R).map (ρ.comp constantCoeff) = supersingularCharTwoCurve k := by
  ext <;> simp

end Curves

end WeierstrassCurve

namespace FormalGroup

open IsLocalRing WeierstrassCurve

section LubinTateElliptic

private theorem coeff_coeffPartial_lubinTateEllipticCurve_lt_two {R k : Type*} [CommRing R]
    [CommRing k] (ρ : R →+* k) {d : Fin 2 →₀ ℕ} (hd : d.degree < 2) :
    coeff d (coeffPartial ρ 0 (formalGroup (lubinTateEllipticCurve R)).toPowerSeries) = 0 := by
  rw [coeff_coeffPartial]
  have hdeg : d 0 + d 1 < 2 := by rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
  have hcase : d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
    have h01 : (d 0 = 0 ∧ d 1 = 0) ∨ (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
    rcases h01 with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl (Finsupp.ext fun s ↦ by fin_cases s <;> simp [h0, h1])
    · exact Or.inr (Or.inl (Finsupp.ext fun s ↦ by fin_cases s <;> simp [h0, h1]))
    · exact Or.inr (Or.inr (Finsupp.ext fun s ↦ by fin_cases s <;> simp [h0, h1]))
  rcases hcase with rfl | rfl | rfl
  · rw [coeff_zero_eq_constantCoeff_apply, (formalGroup _).zero_constantCoeff, map_zero, map_zero]
  · simp [coeff_one]
  · simp [coeff_one]

/-- The partial-derivative cocycle of `(lubinTateEllipticCurve R).formalGroup` vanishes below
degree `2`. -/
theorem le_order_derivCocycle_lubinTateEllipticCurve {R k : Type*} [CommRing R] [Field k]
    [CharP k 2] (ρ : R →+* k) (i : Fin (2 - 1)) :
    ((2 ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤
      (derivCocycle (formalGroup (lubinTateEllipticCurve R)) ρ
        (formalGroup (supersingularCharTwoCurve k)) i).order := by
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  have hpow : 2 ^ ((0 : Fin (2 - 1)) + 1 : ℕ) = 2 := rfl
  rw [hpow, derivCocycle]
  change ((2 : ℕ) : ℕ∞) ≤ _
  refine le_trans ?_ (le_trans le_add_self le_order_mul)
  rw [le_order_iff]
  intro d hd
  exact coeff_coeffPartial_lubinTateEllipticCurve_lt_two ρ (by exact_mod_cast hd)

private theorem coeff_derivCocycle_lubinTateEllipticCurve_deg_two {R k : Type*} [CommRing R]
    [Field k] [CharP k 2] (ρ : R →+* k) {d : Fin 2 →₀ ℕ} (hdeg : d.degree = 2) :
    coeff d (derivCocycle (formalGroup (lubinTateEllipticCurve R)) ρ
        (formalGroup (supersingularCharTwoCurve k)) 0) =
      if d = Finsupp.single 0 1 + Finsupp.single 1 1 then 1 else 0 := by
  set E₀ := formalGroup (supersingularCharTwoCurve k)
  set Γ := formalGroup (lubinTateEllipticCurve R)
  rw [derivCocycle, coeff_mul, Finset.sum_eq_single (0, d)]
  · have hω₀ : coeff (0 : Fin 2 →₀ ℕ)
        (PowerSeries.subst E₀.toPowerSeries E₀.invariantDifferential) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_subst_of_constantCoeff_zero E₀.zero_constantCoeff,
        E₀.constantCoeff_invariantDifferential, map_one]
    rw [hω₀, one_mul]
    have hdeg' : d 0 + d 1 = 2 := by rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
    have hsplit : d = Finsupp.single 0 2 ∨ d = Finsupp.single 1 2 ∨
        d = Finsupp.single 0 1 + Finsupp.single 1 1 := by
      have h2 : (d 0 = 2 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 2) ∨ (d 0 = 1 ∧ d 1 = 1) := by omega
      rcases h2 with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inl (Finsupp.ext fun s ↦ by fin_cases s <;> simp [h0, h1])
      · exact Or.inr (Or.inl (Finsupp.ext fun s ↦ by fin_cases s <;> simp [h0, h1]))
      · exact Or.inr (Or.inr (Finsupp.ext fun s ↦ by fin_cases s <;> simp [h0, h1]))
    rcases hsplit with rfl | rfl | rfl
    · have hne : Finsupp.single (0 : Fin 2) 2 ≠ Finsupp.single 0 1 + Finsupp.single 1 1 :=
        fun h ↦ by have := DFunLike.congr_fun h 1; simp at this
      simp [hne, coeff_coeffPartial, Γ.coeff_single_zero 2]
    · have hne : Finsupp.single (1 : Fin 2) 2 ≠ Finsupp.single 0 1 + Finsupp.single 1 1 :=
        fun h ↦ by have := DFunLike.congr_fun h 0; simp at this
      simp [hne, coeff_coeffPartial, Γ.coeff_single_one 2]
    · simp only [↓reduceIte, coeff_coeffPartial]
      rw [show coeff (Finsupp.single 0 1 + Finsupp.single 1 1) Γ.toPowerSeries =
          -X 0 from coeff_single_zero_add_single_one_formalGroup _, map_neg, coeff_X]
      simp [CharTwo.neg_eq]
  · rintro ⟨a, b⟩ hab hne
    have ha_add_b : a + b = d := Finset.mem_antidiagonal.mp hab
    have hdeg_b : b.degree < 2 := by
      by_contra hb
      push Not at hb
      have hda : a.degree = 0 := by
        have := congrArg Finsupp.degree ha_add_b; rw [map_add] at this; omega
      have ha0 : a = 0 := by
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hda
        ext s; fin_cases s <;> simp <;> omega
      subst ha0; rw [_root_.zero_add] at ha_add_b; exact hne (Prod.ext rfl ha_add_b)
    rw [coeff_coeffPartial_lubinTateEllipticCurve_lt_two ρ hdeg_b, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_antidiagonal.mpr (_root_.zero_add d)) hmem

/-- In characteristic `2`, the degree-`2` homogeneous component of the partial-derivative cocycle
of `Y² + t X Y + Y = X³` is `lazardCocycle 2 k = X Y`. -/
theorem homogeneousComponent_derivCocycle_lubinTateEllipticCurve {R k : Type*} [CommRing R]
    [Field k] [CharP k 2] (ρ : R →+* k) (i : Fin (2 - 1)) :
    homogeneousComponent (2 ^ (i + 1 : ℕ))
        (derivCocycle (formalGroup (lubinTateEllipticCurve R)) ρ
          (formalGroup (supersingularCharTwoCurve k)) i) =
      ↑(TauCeti.lazardCocycle (2 ^ (i + 1 : ℕ)) k) := by
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  have hpow : 2 ^ ((0 : Fin (2 - 1)) + 1 : ℕ) = 2 := rfl
  rw [hpow]
  have hgcd : TauCeti.lazardGcd 2 = 2 := by
    simpa using TauCeti.lazardGcd_prime_pow Nat.prime_two one_ne_zero
  ext d
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_coe, TauCeti.coeff_lazardCocycle]
  by_cases hdeg : d.degree = 2
  · simp only [hdeg, ↓reduceIte, coeff_derivCocycle_lubinTateEllipticCurve_deg_two ρ hdeg]
    by_cases h11 : d = Finsupp.single 0 1 + Finsupp.single 1 1
    · subst h11; simp [hgcd]
    · have hnot : ¬ (d 0 + d 1 = 2 ∧ d 0 ≠ 0 ∧ d 1 ≠ 0) := fun ⟨_, _, _⟩ ↦
        h11 (Finsupp.ext fun s ↦ by fin_cases s <;> simp <;> omega)
      simp [h11, hnot]
  · have hnot : ¬ (d 0 + d 1 = 2 ∧ d 0 ≠ 0 ∧ d 1 ≠ 0) := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      exact fun h ↦ hdeg h.1
    simp [hdeg, hnot]

/-- **Lubin–Tate §3.5 (elliptic curve universal deformation theorem).** Over any field `k` of
characteristic `2` and ring homomorphism `ρ : R →+* k`, the formal group law of
`E_t : Y² + t X Y + Y = X³` over `R⟦t⟧` is a universal deformation of the height-two formal group
law of `E₀ : Y² + Y = X³` over `k`. -/
theorem lubinTateEllipticCurve_universal_deformation
    {R k : Type*} [CommRing R] [Field k] [CharP k 2] (ρ : R →+* k)
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    Function.Bijective
      (fun f : {f : MvPowerSeries (Fin 1) R →ₐ[R] A //
          π.comp f.toRingHom = ρ.comp constantCoeff} ↦
        FormalGroupDeformation.map f.val.toRingHom f.property
          (⟦⟨formalGroup (lubinTateEllipticCurve R), inferInstance, by
            rw [← map_formalGroup, map_comp_constantCoeff_lubinTateEllipticCurve]⟩⟧ :
            FormalGroupDeformation (ρ.comp constantCoeff)
              (formalGroup (supersingularCharTwoCurve k)))) :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  isUniversal_of_derivCocycle (p := 2) (h := 2)
    (height_formalGroup_supersingularCharTwoCurve k)
    (formalGroup (lubinTateEllipticCurve R))
    (by rw [← map_formalGroup, map_comp_constantCoeff_lubinTateEllipticCurve])
    (le_order_derivCocycle_lubinTateEllipticCurve ρ)
    (homogeneousComponent_derivCocycle_lubinTateEllipticCurve ρ)
    π hπ

/-- Equivalence packaging `FormalGroup.lubinTateEllipticCurve_universal_deformation`. -/
@[expose]
def lubinTateEllipticCurveUniversalEquiv
    {R k : Type*} [CommRing R] [Field k] [CharP k 2] (ρ : R →+* k)
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    {f : MvPowerSeries (Fin 1) R →ₐ[R] A // π.comp f.toRingHom = ρ.comp constantCoeff} ≃
      FormalGroupDeformation π (formalGroup (supersingularCharTwoCurve k)) :=
  Equiv.ofBijective _ (lubinTateEllipticCurve_universal_deformation ρ π hπ)

/-- Action of the automorphism group `Aut_k(E₀.formalGroup)` by `R`-algebra automorphisms of
`R⟦t⟧` preserving the universal deformation `E_t.formalGroup`, for a complete Noetherian local
ring `(R, ρ)` with surjective local residue map `ρ : R →+* k`. -/
def lubinTateEllipticCurveLiftAut
    {R k : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [CharP k 2]
    {ρ : R →+* k} [IsLocalHom ρ] (hρ : Function.Surjective ρ) :
    MulAction.stabilizer (FormalCoordinate k) (formalGroup (supersingularCharTwoCurve k)) →*
      (MvPowerSeries (Fin 1) R ≃ₐ[R] MvPowerSeries (Fin 1) R) :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  liftAut (p := 2) (h := 2) hρ
    (height_formalGroup_supersingularCharTwoCurve k)
    (formalGroup (lubinTateEllipticCurve R))
    (by rw [← map_formalGroup, map_comp_constantCoeff_lubinTateEllipticCurve])
    (le_order_derivCocycle_lubinTateEllipticCurve ρ)
    (homogeneousComponent_derivCocycle_lubinTateEllipticCurve ρ)

end LubinTateElliptic

section WittVectorSpecialization

private lemma maximalIdeal_wittVector_eq_span_p (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [CharP k p] [PerfectRing k p] :
    IsLocalRing.maximalIdeal (WittVector p k) = Ideal.span {(p : WittVector p k)} :=
  (WittVector.irreducible p).maximalIdeal_eq

private lemma isLocalHom_wittVector_constantCoeff (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [CharP k p] [PerfectRing k p] :
    IsLocalHom (WittVector.constantCoeff (p := p) (R := k)) where
  map_nonunit x hx := by
    by_contra hna
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
      maximalIdeal_wittVector_eq_span_p p k, ← WittVector.ker_constantCoeff,
      RingHom.mem_ker] at hna
    exact hx.ne_zero hna

private lemma isAdicComplete_maximalIdeal_wittVector (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [CharP k p] [PerfectRing k p] :
    IsAdicComplete (IsLocalRing.maximalIdeal (WittVector p k)) (WittVector p k) := by
  rw [maximalIdeal_wittVector_eq_span_p p k]
  exact WittVector.isAdicCompleteIdealSpanP

/-- **Lubin–Tate §3.5 over `W(k)⟦t⟧`**: for any perfect field `k` of characteristic `2`,
`E_t : Y² + t X Y + Y = X³` over `W(k)⟦t⟧` is a universal deformation of `E₀ : Y² + Y = X³`
over every complete Noetherian local `W(k)`-algebra `(A, π)`. -/
@[expose]
def lubinTateEllipticCurveUniversalEquiv_wittVector
    (k : Type*) [Field k] [CharP k 2] [PerfectRing k 2]
    {A : Type*} [CommRing A] [Algebra (WittVector 2 k) A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π]
    (hπ : π.comp (algebraMap (WittVector 2 k) A) = WittVector.constantCoeff) :
    {f : MvPowerSeries (Fin 1) (WittVector 2 k) →ₐ[WittVector 2 k] A //
        π.comp f.toRingHom = WittVector.constantCoeff.comp constantCoeff} ≃
      FormalGroupDeformation π (formalGroup (supersingularCharTwoCurve k)) :=
  lubinTateEllipticCurveUniversalEquiv WittVector.constantCoeff π hπ

/-- **Lubin–Tate §3.5 automorphism action over `W(k)⟦t⟧`**: for any perfect field `k` of
characteristic `2` (such as `𝔽₄ = GaloisField 2 2`), `Aut_k(E₀.formalGroup)` acts by
`W(k)`-algebra automorphisms of `W(k)⟦t⟧`. -/
def lubinTateEllipticCurveLiftAut_wittVector
    (k : Type*) [Field k] [CharP k 2] [PerfectRing k 2] :
    MulAction.stabilizer (FormalCoordinate k) (formalGroup (supersingularCharTwoCurve k)) →*
      (MvPowerSeries (Fin 1) (WittVector 2 k) ≃ₐ[WittVector 2 k]
        MvPowerSeries (Fin 1) (WittVector 2 k)) :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsLocalHom (WittVector.constantCoeff (p := 2) (R := k)) :=
    isLocalHom_wittVector_constantCoeff 2 k
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (WittVector 2 k)) (WittVector 2 k) :=
    isAdicComplete_maximalIdeal_wittVector 2 k
  lubinTateEllipticCurveLiftAut (WittVector.constantCoeff_surjective 2)

/-- Specialization of `lubinTateEllipticCurveUniversalEquiv_wittVector` to `k = 𝔽₄`
(`GaloisField 2 2`), giving the universal deformation `Y² + t X Y + Y = X³` over `W(𝔽₄)⟦t⟧`
(Lubin–Tate §3.5). -/
@[expose]
def lubinTateEllipticCurveUniversalEquiv_galoisFieldTwo
    {A : Type*} [CommRing A] [Algebra (WittVector 2 (GaloisField 2 2)) A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (π : A →+* GaloisField 2 2) [IsLocalHom π]
    (hπ : π.comp (algebraMap (WittVector 2 (GaloisField 2 2)) A) = WittVector.constantCoeff) :
    {f : MvPowerSeries (Fin 1) (WittVector 2 (GaloisField 2 2)) →ₐ[
          WittVector 2 (GaloisField 2 2)] A //
        π.comp f.toRingHom = WittVector.constantCoeff.comp constantCoeff} ≃
      FormalGroupDeformation π (formalGroup (supersingularCharTwoCurve (GaloisField 2 2))) :=
  lubinTateEllipticCurveUniversalEquiv_wittVector (GaloisField 2 2) π hπ

/-- Specialization of `lubinTateEllipticCurveLiftAut_wittVector` to `k = 𝔽₄`
(`GaloisField 2 2`), giving the action of `Aut_{𝔽₄}(E₀.formalGroup)` on `W(𝔽₄)⟦t⟧`. -/
def lubinTateEllipticCurveLiftAut_galoisFieldTwo :
    MulAction.stabilizer (FormalCoordinate (GaloisField 2 2))
        (formalGroup (supersingularCharTwoCurve (GaloisField 2 2))) →*
      (MvPowerSeries (Fin 1) (WittVector 2 (GaloisField 2 2)) ≃ₐ[
          WittVector 2 (GaloisField 2 2)]
        MvPowerSeries (Fin 1) (WittVector 2 (GaloisField 2 2))) :=
  lubinTateEllipticCurveLiftAut_wittVector (GaloisField 2 2)

end WittVectorSpecialization

end FormalGroup
