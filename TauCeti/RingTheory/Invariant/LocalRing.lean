/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Teichmuller
public import TauCeti.RingTheory.Perfection
import Mathlib.Algebra.CharP.Defs

/-!
# Invariant subrings of local rings and their residue fields

Let a monoid `M` act by ring endomorphisms on a ring `A`, and let
`A^M = FixedPoints.subring A M` be the invariant subring. An element of `A^M` is a unit in `A^M`
exactly when it is a unit in `A`, because the inverse of a fixed unit is again fixed. Therefore,
whenever `A` is a local ring, `A^M` is again a local ring, the inclusion `A^M → A` is a local
homomorphism, and (when `A` is commutative) the maximal ideal of `A^M` is the contraction of the
maximal ideal of `A`. Neither finiteness of `M` nor Noetherianity of `A` is needed.

Now suppose `H` acts on a commutative local ring `A` inducing the identity on the residue field
`k = A ⧸ 𝔪`.
The induced map `ResidueField A^H → k` is always injective; it is bijective (so `A^H` and `A` have
the same residue field) in two complementary situations:

1. **Invertible order**: if `H` is a finite group whose cardinality is nonzero in `k`, then `|H|` is
   a unit in `A`, and averaging `|H|⁻¹ ∑_{h ∈ H} h • a` lifts every residue class to `A^H`. No
   completeness or perfection hypothesis is needed.
2. **Characteristic `p` with Teichmüller lifts**: if `A` is `𝔪`-adically complete and `k` is a
   perfect ring of prime characteristic `p`, then every Teichmüller representative in `A` is fixed
   by every `h` (by uniqueness of Teichmüller lifts, `Perfection.teichmuller₀_spec`), and the
   Teichmüller representatives surject onto `k`. Here `H` need not be finite or even a group.

Combining the two cases shows that when `A` is a complete local ring with perfect residue field `k`
and a finite group `H` acts trivially on `k`, the natural map `ResidueField A^H → ResidueField A`
is a ring isomorphism (`TauCeti.FixedPoints.residueFieldEquiv`).

We also package the invariant orbit product `∏_{h ∈ H} h • a` as an element of `A^H`
(`TauCeti.FixedPoints.orbitProd`).

## Main definitions

* `TauCeti.FixedPoints.isLocalRing_subring`: `FixedPoints.subring A M` is a local ring when `A` is.
* `TauCeti.FixedPoints.residueFieldEquiv`: `ResidueField A^H ≃+* ResidueField A` for a finite group
  acting trivially on the perfect residue field of a complete local ring.
* `TauCeti.FixedPoints.orbitProd H a`: the orbit product `∏_{h ∈ H} h • a` in
  `FixedPoints.subring A H`.

## Main results

* `TauCeti.FixedPoints.isUnit_subring_iff`: an invariant element is a unit in `A^M` iff it is a
  unit in `A`.
* `TauCeti.FixedPoints.maximalIdeal_subring`: `𝔪_{A^M} = 𝔪_A ∩ A^M`.
* `TauCeti.FixedPoints.residueFieldMap_surjective_of_ne_zero`: residue field surjectivity when
  `|H| ≠ 0` in `ResidueField A`.
* `TauCeti.FixedPoints.smul_teichmuller₀` and
  `TauCeti.FixedPoints.residueFieldMap_surjective_of_charP`: Teichmüller invariance and residue
  field surjectivity in prime characteristic.
* `TauCeti.FixedPoints.residueFieldMap_bijective`: residue field bijection for a complete local
  ring with perfect residue field.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Theorem 7.5.2 (residue field
  surjectivity in the proof of regularity of invariant rings).
-/

public section

open IsLocalRing Ideal

namespace TauCeti.FixedPoints

section UnitsAndLocalRing

variable {M A : Type*} [Monoid M] [Ring A] [MulSemiringAction M A]

/-- An invariant element is a unit in `FixedPoints.subring A M` if and only if it is a unit in `A`:
the inverse of a fixed unit is automatically fixed. -/
@[simp]
theorem isUnit_subring_iff {b : FixedPoints.subring A M} :
    IsUnit b ↔ IsUnit (b : A) := by
  refine ⟨fun h ↦ h.map (FixedPoints.subring A M).subtype, fun ⟨u, hu⟩ ↦ ?_⟩
  have hinv : u.inv ∈ FixedPoints.subring A M := fun m ↦ by
    have hu' : Units.map (MulSemiringAction.toRingHom M A m).toMonoidHom u = u :=
      Units.ext (by simpa [hu] using b.2 m)
    exact congrArg Units.inv hu'
  refine isUnit_iff_exists.mpr ⟨⟨u.inv, hinv⟩, Subtype.ext ?_, Subtype.ext ?_⟩
  · simp [← hu]
  · simp [← hu]

/-- The invariant subring of a local ring under any monoid action by ring endomorphisms is a local
ring. -/
instance isLocalRing_subring [IsLocalRing A] : IsLocalRing (FixedPoints.subring A M) :=
  (FixedPoints.subring A M).isLocalRing_of_unit fun _ _ h ↦ isUnit_subring_iff.mpr h

/-- The inclusion `FixedPoints.subring A M →+* A` is a local homomorphism. -/
instance isLocalHom_subring_subtype :
    IsLocalHom (FixedPoints.subring A M).subtype where
  map_nonunit _ hb := isUnit_subring_iff.mpr hb

end UnitsAndLocalRing

section CommLocalRing

variable {M A : Type*} [Monoid M] [CommRing A] [MulSemiringAction M A]

/-- The algebra map `FixedPoints.subring A M →+* A` is a local homomorphism. -/
instance isLocalHom_algebraMap_subring : IsLocalHom (algebraMap (FixedPoints.subring A M) A) :=
  isLocalHom_subring_subtype

variable [IsLocalRing A]

/-- The maximal ideal of `FixedPoints.subring A M` is the contraction of the maximal ideal of
`A`. -/
theorem maximalIdeal_subring :
    maximalIdeal (FixedPoints.subring A M) =
      (maximalIdeal A).comap (FixedPoints.subring A M).subtype :=
  (maximalIdeal_comap (FixedPoints.subring A M).subtype).symm

/-- Membership in the maximal ideal of `FixedPoints.subring A M` is tested in `A`. -/
theorem mem_maximalIdeal_subring_iff {b : FixedPoints.subring A M} :
    b ∈ maximalIdeal (FixedPoints.subring A M) ↔ (b : A) ∈ maximalIdeal A := by
  rw [maximalIdeal_subring, Ideal.mem_comap]
  rfl

/-- An endomorphism acting trivially on the residue field of a local ring preserves every power of
its maximal ideal. -/
theorem smul_mem_maximalIdeal_pow {m : M}
    (hm : ∀ a : A, residue A (m • a) = residue A a) {n : ℕ} {a : A}
    (ha : a ∈ maximalIdeal A ^ n) : m • a ∈ maximalIdeal A ^ n := by
  let f : A →+* A := MulSemiringAction.toRingHom M A m
  have hf : (maximalIdeal A).map f ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← residue_eq_zero_iff, MulSemiringAction.toRingHom_apply, hm x,
      residue_eq_zero_iff]
    exact hx
  have hpow : (maximalIdeal A ^ n).map f ≤ maximalIdeal A ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hf n
  exact hpow (Ideal.mem_map_of_mem f ha)

end CommLocalRing

section OrbitProd

variable (H : Type*) [Group H] [Finite H] {A : Type*} [CommRing A] [MulSemiringAction H A]

/-- **The invariant orbit product** `∏_{h ∈ H} h • a` as an element of `FixedPoints.subring A H`. -/
noncomputable def orbitProd (a : A) : FixedPoints.subring A H :=
  have := Fintype.ofFinite H
  ⟨∏ h : H, h • a, fun g ↦ Finset.smul_prod_perm a g⟩

/-- The underlying element of `orbitProd H a` in `A` is `∏ h : H, h • a`. -/
@[simp]
theorem coe_orbitProd [Fintype H] (a : A) : (orbitProd H a : A) = ∏ h : H, h • a := by
  classical
  dsimp only [orbitProd]
  exact Finset.prod_congr (by ext; simp) fun _ _ ↦ rfl

/-- The orbit product of `0` is `0`. -/
@[simp]
theorem orbitProd_zero : orbitProd H (0 : A) = 0 := by
  have := Fintype.ofFinite H
  ext
  simp

/-- The orbit product of `1` is `1`. -/
@[simp]
theorem orbitProd_one : orbitProd H (1 : A) = 1 := by
  have := Fintype.ofFinite H
  ext
  simp

/-- The orbit product is multiplicative. -/
theorem orbitProd_mul (a b : A) : orbitProd H (a * b) = orbitProd H a * orbitProd H b := by
  have := Fintype.ofFinite H
  ext
  simp [smul_mul', Finset.prod_mul_distrib]

/-- The orbit product of an invariant element `a` is `a ^ |H|`. -/
theorem coe_orbitProd_of_fixed {a : A} (ha : ∀ h : H, h • a = a) :
    (orbitProd H a : A) = a ^ Nat.card H := by
  have := Fintype.ofFinite H
  rw [coe_orbitProd, Finset.prod_congr rfl fun h _ ↦ ha h, Finset.prod_const, Finset.card_univ,
    Nat.card_eq_fintype_card]

end OrbitProd

section ResidueField

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- **Residue field surjectivity in the tame case.** If a finite group `H` acts trivially on the
residue field of a local ring `A` and `|H| ≠ 0` in `ResidueField A`, then the induced map
`ResidueField A^H → ResidueField A` is surjective (by averaging over `H`). -/
theorem residueFieldMap_surjective_of_ne_zero {H : Type*} [Group H] [Finite H]
    [MulSemiringAction H A] (hres : ∀ (h : H) (a : A), residue A (h • a) = residue A a)
    (hcard : (Nat.card H : ResidueField A) ≠ 0) :
    Function.Surjective (IsLocalRing.ResidueField.map (FixedPoints.subring A H).subtype) := by
  have := Fintype.ofFinite H
  have hunit : IsUnit (Fintype.card H : A) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff]
    simpa [Nat.card_eq_fintype_card] using hcard
  have hunit_sub : IsUnit (Fintype.card H : FixedPoints.subring A H) :=
    isUnit_subring_iff.mpr (by simpa using hunit)
  obtain ⟨v, hv⟩ := hunit_sub
  intro x
  obtain ⟨a, rfl⟩ := residue_surjective x
  let sumA : FixedPoints.subring A H := ⟨∑ h : H, h • a, fun g ↦ by
    rw [Finset.smul_sum]
    simpa [mul_smul] using
      Fintype.sum_equiv (Equiv.mulLeft g) (fun h ↦ (g * h) • a) (fun h ↦ h • a) fun _ ↦ rfl⟩
  let b : FixedPoints.subring A H := v.inv * sumA
  refine ⟨residue (FixedPoints.subring A H) b, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  have hsum : residue A (sumA : A) = (Fintype.card H : ResidueField A) * residue A a := by
    simp only [sumA, map_sum, hres, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hinv : residue A (v.inv : A) * (Fintype.card H : ResidueField A) = 1 := by
    have hmul : (v.inv : A) * (Fintype.card H : A) = 1 := by
      have := congrArg Subtype.val v.inv_val
      simpa [hv] using this
    rw [← map_natCast (residue A), ← map_mul, hmul, map_one]
  rw [Subring.coe_subtype, Subring.coe_mul, map_mul, hsum, ← mul_assoc, hinv, one_mul]

/-- **Teichmüller representatives are fixed by endomorphisms trivial on the residue field.**
Let `A` be a complete local ring with residue field of prime characteristic `p`, and let `M` act on
`A` by ring endomorphisms inducing the identity on `ResidueField A`. Then every Teichmüller lift
`Perfection.teichmuller₀ p (maximalIdeal A) x` is fixed by `M`. -/
theorem smul_teichmuller₀ {M : Type*} [Monoid M] [MulSemiringAction M A]
    [IsAdicComplete (maximalIdeal A) A] {p : ℕ} [Fact p.Prime] [CharP (A ⧸ maximalIdeal A) p]
    (hres : ∀ (m : M) (a : A), residue A (m • a) = residue A a)
    (m : M) (x : Perfection (A ⧸ maximalIdeal A) p) :
    m • Perfection.teichmuller₀ p (maximalIdeal A) x =
      Perfection.teichmuller₀ p (maximalIdeal A) x := by
  symm
  refine Perfection.teichmuller₀_spec fun n ↦ ?_
  obtain ⟨z₀, hz₀⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff (A ⧸ maximalIdeal A) p n x)
  have hmod : Perfection.teichmuller₀ p (maximalIdeal A) x ≡
      z₀ ^ p ^ n [SMOD maximalIdeal A ^ (n + 1)] := Perfection.teichmuller₀_sModEq hz₀
  refine ⟨m • z₀, (hres m z₀).trans hz₀, ?_⟩
  · rw [SModEq.sub_mem] at hmod ⊢
    have hmem := smul_mem_maximalIdeal_pow (hres m) hmod
    rw [smul_sub, smul_pow'] at hmem
    simpa [neg_sub] using neg_mem hmem

/-- **Residue field surjectivity in prime characteristic via Teichmüller lifts.** If `A` is a
complete local ring whose residue field is a perfect ring of prime characteristic `p`, and a monoid
`M` acts trivially on `ResidueField A`, then `ResidueField A^M → ResidueField A` is surjective. -/
theorem residueFieldMap_surjective_of_charP {M : Type*} [Monoid M] [MulSemiringAction M A]
    [IsAdicComplete (maximalIdeal A) A] {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]
    [PerfectRing (ResidueField A) p]
    (hres : ∀ (m : M) (a : A), residue A (m • a) = residue A a) :
    Function.Surjective (IsLocalRing.ResidueField.map (FixedPoints.subring A M).subtype) := by
  have hchar : CharP (A ⧸ maximalIdeal A) p := ‹CharP (ResidueField A) p›
  have hperf : PerfectRing (A ⧸ maximalIdeal A) p := ‹PerfectRing (ResidueField A) p›
  intro y
  have hsurj : Function.Surjective (Perfection.coeffMonoidHom (A ⧸ maximalIdeal A) p 0) :=
    Perfection.coeffMonoidHom_surjective (PerfectRing.bijective_frobenius.surjective) 0
  obtain ⟨x, rfl⟩ := hsurj y
  let t : FixedPoints.subring A M :=
    ⟨Perfection.teichmuller₀ p (maximalIdeal A) x, fun m ↦ smul_teichmuller₀ hres m x⟩
  refine ⟨residue (FixedPoints.subring A M) t, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  exact Perfection.mk_teichmuller₀ x

/-- **Residue field isomorphism for invariants of a complete local ring with perfect residue
field.** If `A` is a complete local ring with perfect residue field and a finite group `H` acts
trivially on `ResidueField A`, then the map `ResidueField A^H → ResidueField A` is bijective. -/
theorem residueFieldMap_bijective {H : Type*} [Group H] [Finite H] [MulSemiringAction H A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    (hres : ∀ (h : H) (a : A), residue A (h • a) = residue A a) :
    Function.Bijective (IsLocalRing.ResidueField.map (FixedPoints.subring A H).subtype) := by
  refine ⟨RingHom.injective _, ?_⟩
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' (ResidueField A)
  · have hpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
    exact residueFieldMap_surjective_of_ne_zero hres (Nat.cast_ne_zero.mpr hpos)
  · have : Fact p.Prime := ⟨hp⟩
    have : ExpChar (ResidueField A) p := ExpChar.prime hp
    exact residueFieldMap_surjective_of_charP (p := p) hres

/-- The ring isomorphism `ResidueField (FixedPoints.subring A H) ≃+* ResidueField A` when `A` is
complete with perfect residue field and `H` is finite acting trivially on `ResidueField A`. -/
noncomputable def residueFieldEquiv {H : Type*} [Group H] [Finite H] [MulSemiringAction H A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    (hres : ∀ (h : H) (a : A), residue A (h • a) = residue A a) :
    ResidueField (FixedPoints.subring A H) ≃+* ResidueField A :=
  RingEquiv.ofBijective _ (residueFieldMap_bijective hres)

/-- The underlying ring homomorphism of `residueFieldEquiv` is the canonical residue field map. -/
@[simp]
theorem coe_residueFieldEquiv {H : Type*} [Group H] [Finite H] [MulSemiringAction H A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    (hres : ∀ (h : H) (a : A), residue A (h • a) = residue A a) :
    (residueFieldEquiv hres : ResidueField (FixedPoints.subring A H) →+* ResidueField A) =
      IsLocalRing.ResidueField.map (FixedPoints.subring A H).subtype := by
  ext x
  rfl

/-- `residueFieldEquiv` maps the residue class of `b ∈ A^H` to the residue class of `(b : A)`. -/
@[simp]
theorem residueFieldEquiv_residue {H : Type*} [Group H] [Finite H] [MulSemiringAction H A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    (hres : ∀ (h : H) (a : A), residue A (h • a) = residue A a)
    (b : FixedPoints.subring A H) :
    residueFieldEquiv hres (residue (FixedPoints.subring A H) b) = residue A (b : A) := by
  rw [residueFieldEquiv, RingEquiv.ofBijective_apply, IsLocalRing.ResidueField.map_residue]
  rfl

/-- Every element of `A` is congruent modulo `maximalIdeal A` to an invariant element of `A^H`. -/
theorem exists_residue_eq {H : Type*} [Group H] [Finite H] [MulSemiringAction H A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    (hres : ∀ (h : H) (a : A), residue A (h • a) = residue A a) (a : A) :
    ∃ b : FixedPoints.subring A H, residue A (b : A) = residue A a := by
  obtain ⟨y, hy⟩ := (residueFieldMap_bijective hres).2 (residue A a)
  obtain ⟨b, rfl⟩ := residue_surjective y
  exact ⟨b, by simpa [IsLocalRing.ResidueField.map_residue] using hy⟩

/-- The residue field of `FixedPoints.subring A H` is perfect when `A` is complete with perfect
residue field and `H` is finite acting trivially on `ResidueField A`. -/
theorem perfectField_residueField {H : Type*} [Group H] [Finite H] [MulSemiringAction H A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    (hres : ∀ (h : H) (a : A), residue A (h • a) = residue A a) :
    PerfectField (ResidueField (FixedPoints.subring A H)) :=
  PerfectField.of_ringEquiv (residueFieldEquiv hres).symm

end ResidueField

end TauCeti.FixedPoints
