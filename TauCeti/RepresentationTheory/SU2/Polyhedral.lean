/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.Algebra.Quaternion.Polyhedral.Icosahedral
public import TauCeti.Algebra.Quaternion.Polyhedral.Octahedral
public import TauCeti.RepresentationTheory.SU2.BinaryDihedral
public import TauCeti.RepresentationTheory.SU2.DefiningRepresentation
import Mathlib.Tactic.FinCases

/-!
# Concrete binary polyhedral subgroups of `SU(2)` and `SL₂(ℂ)`

The `ℝ`-algebra star-embedding `Quaternion.toComplexMatrix` identifies the group `unitary ℍ[ℝ]` of
unit Hamilton quaternions with `TauCeti.SU2 = Matrix.specialUnitaryGroup (Fin 2) ℂ` via
`Quaternion.unitaryEquivSpecialUnitaryGroup`. Pushing the three exceptional unit-quaternion
polyhedral subgroups (`TauCeti.binaryTetrahedralUnitSubgroup`,
`TauCeti.binaryOctahedralUnitSubgroup`, `TauCeti.binaryIcosahedralUnitSubgroup`) across this
isomorphism produces the concrete **binary tetrahedral**, **binary octahedral**, and **binary
icosahedral** subgroups of `SU(2)` of exact orders `24`, `48`, and `120`, together with their
images in `SL₂(ℂ)` under `Matrix.specialUnitaryGroup.toSL`.

Under `Quaternion.unitaryEquivSpecialUnitaryGroup`, the central involution `-1 : unitary ℍ[ℝ]`
becomes `TauCeti.SU2.torusHom (-1) = -I₂`, while the quaternion basis units `i` and `j` match the
existing `SU(2)` generators `TauCeti.SU2.binaryDihedralRotation 2 = diag(I, -I)` and
`TauCeti.SU2.weylElement⁻¹ = !![0, 1; -1, 0]` of `TauCeti.SU2.BinaryDihedral`. Consequently the
quaternion group `Q₈ = binaryDihedralSubgroup 2` sits inside `binaryTetrahedralSubgroup` with index
`3`, and `binaryTetrahedralSubgroup` sits inside `binaryOctahedralSubgroup` (normally, with index
`2`) and inside `binaryIcosahedralSubgroup` (with index `5`).

## Main definitions

* `TauCeti.SU2.tetrahedralOmega`, `TauCeti.SU2.tetrahedralTau`,
  `TauCeti.SU2.octahedralGenerator`, `TauCeti.SU2.icosahedralGenerator`: the explicit `SU(2)`
  polyhedral generators of exact orders `6`, `6`, `8`, and `10`.
* `TauCeti.SU2.binaryTetrahedralSubgroup`, `TauCeti.SU2.binaryOctahedralSubgroup`,
  `TauCeti.SU2.binaryIcosahedralSubgroup`: the concrete subgroups of `SU(2)` of orders `24`, `48`,
  and `120`, with multiplicative equivalences `binaryTetrahedralUnitEquiv`,
  `binaryOctahedralUnitEquiv`, and `binaryIcosahedralUnitEquiv`.
* `TauCeti.SU2.binaryTetrahedralSLSubgroup`, `TauCeti.SU2.binaryOctahedralSLSubgroup`,
  `TauCeti.SU2.binaryIcosahedralSLSubgroup`: their isomorphic images inside `SL₂(ℂ)` under
  `Matrix.specialUnitaryGroup.toSL`.

## Main results

* `<2, 3, 3>`, `<2, 3, 4>`, and `<2, 3, 5>` presentation relations in `SU(2)`, matrix entry
  formulas, and closure characterizations `binaryTetrahedralSubgroup_eq_closure`,
  `binaryTetrahedralSubgroup_eq_closure_coordinates`, `binaryOctahedralSubgroup_eq_closure`, and
  `binaryIcosahedralSubgroup_eq_closure`.
* Exact cardinalities `24`, `48`, and `120` in both `SU(2)` and `SL₂(ℂ)`, together with the
  subgroup chain `binaryDihedralSubgroup 2 ≤ binaryTetrahedralSubgroup ≤ binaryOctahedralSubgroup`
  (normal of relative index `2`) and `binaryTetrahedralSubgroup ≤ binaryIcosahedralSubgroup`
  (relative index `5`).

## References

* J. H. Conway and D. A. Smith, *On Quaternions and Octonions*, A K Peters, 2003, §§3.3–3.4, §6.5.
* H. Choi and H. Lee, *Finite subgroups of `SL(2, ℂ)` and `PSL(2, ℂ)`*, J. Chungcheong Math. Soc.
  **32** (2019), no. 4, 439–457.
-/

public section

open Matrix
open scoped Matrix Quaternion Real

namespace TauCeti.SU2

/-! ### Matching unit-quaternion coordinates with `SU(2)` elements -/

/-- The torus element at `-1 : Circle` has underlying matrix `-1`. -/
theorem coe_torusHom_neg_one : (torusHom (-1) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  rw [coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Under `Quaternion.unitaryEquivSpecialUnitaryGroup`, `-1 : unitary ℍ[ℝ]` corresponds to the
central involution `torusHom (-1)` of `SU(2)`. -/
@[simp]
theorem unitaryEquivSpecialUnitaryGroup_neg_one :
    Quaternion.unitaryEquivSpecialUnitaryGroup (-1) = torusHom (-1) :=
  Subtype.ext <| by
    rw [Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply, Unitary.coe_neg, OneMemClass.coe_one,
      map_neg, map_one, coe_torusHom_neg_one]

/-- Under `Quaternion.unitaryEquivSpecialUnitaryGroup`, the quaternion unit `i` is the quarter-turn
diagonal rotation `binaryDihedralRotation 2 = diag(I, -I)`. -/
theorem unitaryEquivSpecialUnitaryGroup_quaternionUnitI :
    Quaternion.unitaryEquivSpecialUnitaryGroup quaternionUnitI = binaryDihedralRotation 2 :=
  Subtype.ext <| by
    rw [Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply, coe_quaternionUnitI,
      coe_binaryDihedralRotation_eq_toComplexMatrix 2]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Under `Quaternion.unitaryEquivSpecialUnitaryGroup`, the quaternion unit `j` is
`weylElement⁻¹ = !![0, 1; -1, 0]`. -/
theorem unitaryEquivSpecialUnitaryGroup_quaternionUnitJ :
    Quaternion.unitaryEquivSpecialUnitaryGroup quaternionUnitJ = weylElement⁻¹ :=
  Subtype.ext <| by
    rw [Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply, coe_quaternionUnitJ,
      coe_weylElement_inv_eq_toComplexMatrix]

/-! ### Explicit polyhedral generators in `SU(2)` -/

/-- The Hurwitz generator `ω = !![(1 + I)/2, (1 + I)/2; (-1 + I)/2, (1 - I)/2]` of `SU(2)`, image
of `(1 + i + j + k) / 2`. -/
noncomputable def tetrahedralOmega : SU2 :=
  Quaternion.unitaryEquivSpecialUnitaryGroup _root_.TauCeti.tetrahedralOmega

theorem tetrahedralOmega_def :
    tetrahedralOmega =
      Quaternion.unitaryEquivSpecialUnitaryGroup _root_.TauCeti.tetrahedralOmega := (rfl)

/-- The companion `<2, 3, 3>` generator `τ = !![(1 + I)/2, (1 - I)/2; (-1 - I)/2, (1 - I)/2]` of
`SU(2)`, image of `(1 + i + j - k) / 2`. -/
noncomputable def tetrahedralTau : SU2 :=
  Quaternion.unitaryEquivSpecialUnitaryGroup _root_.TauCeti.tetrahedralTau

theorem tetrahedralTau_def :
    tetrahedralTau =
      Quaternion.unitaryEquivSpecialUnitaryGroup _root_.TauCeti.tetrahedralTau := (rfl)

/-- The octahedral generator `r = diag((1 + I)/√2, (1 - I)/√2)` of `SU(2)`, image of
`(1 + i) / √2`. -/
noncomputable def octahedralGenerator : SU2 :=
  Quaternion.unitaryEquivSpecialUnitaryGroup _root_.TauCeti.octahedralGenerator

theorem octahedralGenerator_def :
    octahedralGenerator =
      Quaternion.unitaryEquivSpecialUnitaryGroup _root_.TauCeti.octahedralGenerator := (rfl)

/-- The icosahedral `<2, 3, 5>` generator of `SU(2)`, image of `(φ + j + φ⁻¹ k) / 2`. -/
noncomputable def icosahedralGenerator : SU2 :=
  Quaternion.unitaryEquivSpecialUnitaryGroup _root_.TauCeti.icosahedralGenerator

theorem icosahedralGenerator_def :
    icosahedralGenerator =
      Quaternion.unitaryEquivSpecialUnitaryGroup _root_.TauCeti.icosahedralGenerator := (rfl)

/-- Explicit `2 × 2` complex matrix of `TauCeti.SU2.tetrahedralOmega`. -/
theorem coe_tetrahedralOmega :
    (tetrahedralOmega : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(1 + Complex.I) / 2, (1 + Complex.I) / 2;
        (-1 + Complex.I) / 2, (1 - Complex.I) / 2] := by
  rw [tetrahedralOmega, Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply,
    _root_.TauCeti.coe_tetrahedralOmega, Quaternion.toComplexMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Explicit `2 × 2` complex matrix of `TauCeti.SU2.tetrahedralTau`. -/
theorem coe_tetrahedralTau :
    (tetrahedralTau : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(1 + Complex.I) / 2, (1 - Complex.I) / 2;
        (-1 - Complex.I) / 2, (1 - Complex.I) / 2] := by
  rw [tetrahedralTau, Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply,
    _root_.TauCeti.coe_tetrahedralTau, Quaternion.toComplexMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Explicit `2 × 2` complex matrix of `TauCeti.SU2.octahedralGenerator`. -/
theorem coe_octahedralGenerator :
    (octahedralGenerator : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((1 : ℂ) + Complex.I) / (√2 : ℝ), 0;
        0, ((1 : ℂ) - Complex.I) / (√2 : ℝ)] := by
  rw [octahedralGenerator, Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply,
    _root_.TauCeti.coe_octahedralGenerator, Quaternion.toComplexMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [div_eq_mul_inv] <;> ring

/-- Explicit `2 × 2` complex matrix of `TauCeti.SU2.icosahedralGenerator`. -/
theorem coe_icosahedralGenerator :
    (icosahedralGenerator : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.goldenRatio : ℝ) : ℂ) / 2,
          (1 + ((Real.goldenRatio⁻¹ : ℝ) : ℂ) * Complex.I) / 2;
        (-1 + ((Real.goldenRatio⁻¹ : ℝ) : ℂ) * Complex.I) / 2,
          ((Real.goldenRatio : ℝ) : ℂ) / 2] := by
  rw [icosahedralGenerator, Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply,
    _root_.TauCeti.coe_icosahedralGenerator, Quaternion.toComplexMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

@[simp]
theorem orderOf_tetrahedralOmega : orderOf tetrahedralOmega = 6 :=
  (orderOf_injective Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom
    Quaternion.unitaryEquivSpecialUnitaryGroup.injective
    _root_.TauCeti.tetrahedralOmega).trans _root_.TauCeti.orderOf_tetrahedralOmega

@[simp]
theorem orderOf_tetrahedralTau : orderOf tetrahedralTau = 6 :=
  (orderOf_injective Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom
    Quaternion.unitaryEquivSpecialUnitaryGroup.injective
    _root_.TauCeti.tetrahedralTau).trans _root_.TauCeti.orderOf_tetrahedralTau

@[simp]
theorem orderOf_octahedralGenerator : orderOf octahedralGenerator = 8 :=
  (orderOf_injective Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom
    Quaternion.unitaryEquivSpecialUnitaryGroup.injective
    _root_.TauCeti.octahedralGenerator).trans _root_.TauCeti.orderOf_octahedralGenerator

@[simp]
theorem orderOf_icosahedralGenerator : orderOf icosahedralGenerator = 10 :=
  (orderOf_injective Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom
    Quaternion.unitaryEquivSpecialUnitaryGroup.injective
    _root_.TauCeti.icosahedralGenerator).trans _root_.TauCeti.orderOf_icosahedralGenerator

/-! ### `<2, 3, 3>`, `<2, 3, 4>`, and `<2, 3, 5>` presentation relations in `SU(2)` -/

theorem tetrahedralOmega_pow_three : tetrahedralOmega ^ 3 = torusHom (-1) := by
  rw [tetrahedralOmega, ← map_pow, _root_.TauCeti.tetrahedralOmega_pow_three,
    unitaryEquivSpecialUnitaryGroup_neg_one]

theorem tetrahedralTau_pow_three : tetrahedralTau ^ 3 = torusHom (-1) := by
  rw [tetrahedralTau, ← map_pow, _root_.TauCeti.tetrahedralTau_pow_three,
    unitaryEquivSpecialUnitaryGroup_neg_one]

theorem tetrahedralOmega_mul_tetrahedralTau :
    tetrahedralOmega * tetrahedralTau = weylElement⁻¹ := by
  rw [tetrahedralOmega, tetrahedralTau, ← map_mul,
    _root_.TauCeti.tetrahedralOmega_mul_tetrahedralTau,
    unitaryEquivSpecialUnitaryGroup_quaternionUnitJ]

theorem tetrahedralTau_mul_tetrahedralOmega :
    tetrahedralTau * tetrahedralOmega = binaryDihedralRotation 2 := by
  rw [tetrahedralTau, tetrahedralOmega, ← map_mul,
    _root_.TauCeti.tetrahedralTau_mul_tetrahedralOmega,
    unitaryEquivSpecialUnitaryGroup_quaternionUnitI]

theorem tetrahedralOmega_mul_tetrahedralTau_sq :
    (tetrahedralOmega * tetrahedralTau) ^ 2 = torusHom (-1) := by
  rw [tetrahedralOmega, tetrahedralTau, ← map_mul, ← map_pow,
    _root_.TauCeti.tetrahedralOmega_mul_tetrahedralTau_sq,
    unitaryEquivSpecialUnitaryGroup_neg_one]

theorem octahedralGenerator_sq : octahedralGenerator ^ 2 = binaryDihedralRotation 2 := by
  rw [octahedralGenerator, ← map_pow, _root_.TauCeti.octahedralGenerator_sq,
    unitaryEquivSpecialUnitaryGroup_quaternionUnitI]

theorem octahedralGenerator_pow_four : octahedralGenerator ^ 4 = torusHom (-1) := by
  rw [octahedralGenerator, ← map_pow, _root_.TauCeti.octahedralGenerator_pow_four,
    unitaryEquivSpecialUnitaryGroup_neg_one]

theorem octahedralGenerator_mul_tetrahedralOmega_sq :
    (octahedralGenerator * tetrahedralOmega) ^ 2 = torusHom (-1) := by
  rw [octahedralGenerator, tetrahedralOmega, ← map_mul, ← map_pow,
    _root_.TauCeti.octahedralGenerator_mul_tetrahedralOmega_sq,
    unitaryEquivSpecialUnitaryGroup_neg_one]

theorem octahedralGenerator_inv_conj_tetrahedralOmega :
    octahedralGenerator⁻¹ * tetrahedralOmega * octahedralGenerator = tetrahedralTau := by
  rw [octahedralGenerator, tetrahedralOmega, tetrahedralTau, ← map_inv, ← map_mul, ← map_mul,
    _root_.TauCeti.octahedralGenerator_inv_conj_tetrahedralOmega]

theorem icosahedralGenerator_pow_five : icosahedralGenerator ^ 5 = torusHom (-1) := by
  rw [icosahedralGenerator, ← map_pow, _root_.TauCeti.icosahedralGenerator_pow_five,
    unitaryEquivSpecialUnitaryGroup_neg_one]

theorem icosahedralGenerator_mul_tetrahedralOmega_sq :
    (icosahedralGenerator * tetrahedralOmega) ^ 2 = torusHom (-1) := by
  rw [icosahedralGenerator, tetrahedralOmega, ← map_mul, ← map_pow,
    _root_.TauCeti.icosahedralGenerator_mul_tetrahedralOmega_sq,
    unitaryEquivSpecialUnitaryGroup_neg_one]

theorem icosahedralGenerator_sq_mul_tetrahedralOmega_mul_inv :
    icosahedralGenerator ^ 2 * tetrahedralOmega * icosahedralGenerator⁻¹ = weylElement⁻¹ := by
  rw [icosahedralGenerator, tetrahedralOmega, ← map_pow, ← map_inv, ← map_mul, ← map_mul,
    _root_.TauCeti.icosahedralGenerator_sq_mul_tetrahedralOmega_mul_inv,
    unitaryEquivSpecialUnitaryGroup_quaternionUnitJ]

/-! ### Concrete binary polyhedral subgroups of `SU(2)` -/

/-- **The concrete binary tetrahedral subgroup of `SU(2)` of order `24`**, image of the `24`
Hurwitz units under `Quaternion.unitaryEquivSpecialUnitaryGroup`. -/
noncomputable def binaryTetrahedralSubgroup : Subgroup SU2 :=
  binaryTetrahedralUnitSubgroup.map Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom

theorem binaryTetrahedralSubgroup_def :
    binaryTetrahedralSubgroup =
      binaryTetrahedralUnitSubgroup.map Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom :=
  (rfl)

/-- **The concrete binary octahedral subgroup of `SU(2)` of order `48`.** -/
noncomputable def binaryOctahedralSubgroup : Subgroup SU2 :=
  binaryOctahedralUnitSubgroup.map Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom

theorem binaryOctahedralSubgroup_def :
    binaryOctahedralSubgroup =
      binaryOctahedralUnitSubgroup.map Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom :=
  (rfl)

/-- **The concrete binary icosahedral subgroup of `SU(2)` of order `120`**, image of the `120`
vertices of the unit `600`-cell under `Quaternion.unitaryEquivSpecialUnitaryGroup`. -/
noncomputable def binaryIcosahedralSubgroup : Subgroup SU2 :=
  binaryIcosahedralUnitSubgroup.map Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom

theorem binaryIcosahedralSubgroup_def :
    binaryIcosahedralSubgroup =
      binaryIcosahedralUnitSubgroup.map Quaternion.unitaryEquivSpecialUnitaryGroup.toMonoidHom :=
  (rfl)

/-- Multiplicative equivalence between the Hurwitz unit subgroup of `unitary ℍ[ℝ]` and
`TauCeti.SU2.binaryTetrahedralSubgroup`. -/
noncomputable def binaryTetrahedralUnitEquiv :
    binaryTetrahedralUnitSubgroup ≃* binaryTetrahedralSubgroup :=
  Subgroup.equivMapOfInjective _ _ Quaternion.unitaryEquivSpecialUnitaryGroup.injective

@[simp]
theorem coe_binaryTetrahedralUnitEquiv (u : binaryTetrahedralUnitSubgroup) :
    (binaryTetrahedralUnitEquiv u : SU2) =
      Quaternion.unitaryEquivSpecialUnitaryGroup (u : unitary ℍ[ℝ]) := (rfl)

/-- Multiplicative equivalence between `TauCeti.binaryOctahedralUnitSubgroup` and
`TauCeti.SU2.binaryOctahedralSubgroup`. -/
noncomputable def binaryOctahedralUnitEquiv :
    binaryOctahedralUnitSubgroup ≃* binaryOctahedralSubgroup :=
  Subgroup.equivMapOfInjective _ _ Quaternion.unitaryEquivSpecialUnitaryGroup.injective

@[simp]
theorem coe_binaryOctahedralUnitEquiv (u : binaryOctahedralUnitSubgroup) :
    (binaryOctahedralUnitEquiv u : SU2) =
      Quaternion.unitaryEquivSpecialUnitaryGroup (u : unitary ℍ[ℝ]) := (rfl)

/-- Multiplicative equivalence between `TauCeti.binaryIcosahedralUnitSubgroup` and
`TauCeti.SU2.binaryIcosahedralSubgroup`. -/
noncomputable def binaryIcosahedralUnitEquiv :
    binaryIcosahedralUnitSubgroup ≃* binaryIcosahedralSubgroup :=
  Subgroup.equivMapOfInjective _ _ Quaternion.unitaryEquivSpecialUnitaryGroup.injective

@[simp]
theorem coe_binaryIcosahedralUnitEquiv (u : binaryIcosahedralUnitSubgroup) :
    (binaryIcosahedralUnitEquiv u : SU2) =
      Quaternion.unitaryEquivSpecialUnitaryGroup (u : unitary ℍ[ℝ]) := (rfl)

instance : Finite binaryTetrahedralSubgroup :=
  Finite.of_equiv _ binaryTetrahedralUnitEquiv.toEquiv

instance : Finite binaryOctahedralSubgroup :=
  Finite.of_equiv _ binaryOctahedralUnitEquiv.toEquiv

instance : Finite binaryIcosahedralSubgroup :=
  Finite.of_equiv _ binaryIcosahedralUnitEquiv.toEquiv

/-- **The binary tetrahedral subgroup of `SU(2)` has exact order `24`.** -/
@[simp]
theorem natCard_binaryTetrahedralSubgroup : Nat.card binaryTetrahedralSubgroup = 24 := by
  rw [← Nat.card_congr binaryTetrahedralUnitEquiv.toEquiv, natCard_binaryTetrahedralUnitSubgroup]

/-- **The binary octahedral subgroup of `SU(2)` has exact order `48`.** -/
@[simp]
theorem natCard_binaryOctahedralSubgroup : Nat.card binaryOctahedralSubgroup = 48 := by
  rw [← Nat.card_congr binaryOctahedralUnitEquiv.toEquiv, natCard_binaryOctahedralUnitSubgroup]

/-- **The binary icosahedral subgroup of `SU(2)` has exact order `120`.** -/
@[simp]
theorem natCard_binaryIcosahedralSubgroup : Nat.card binaryIcosahedralSubgroup = 120 := by
  rw [← Nat.card_congr binaryIcosahedralUnitEquiv.toEquiv, natCard_binaryIcosahedralUnitSubgroup]

/-- **The binary tetrahedral subgroup of `SU(2)` is generated by `{ω, τ}`.** -/
theorem binaryTetrahedralSubgroup_eq_closure :
    binaryTetrahedralSubgroup = Subgroup.closure {tetrahedralOmega, tetrahedralTau} := by
  rw [binaryTetrahedralSubgroup, binaryTetrahedralUnitSubgroup_eq_closure, MonoidHom.map_closure]
  simp [tetrahedralOmega, tetrahedralTau]

/-- **The binary tetrahedral subgroup of `SU(2)` is generated by `{i, j, ω}`** in `SU(2)`
coordinates (`binaryDihedralRotation 2`, `weylElement⁻¹`, `tetrahedralOmega`). -/
theorem binaryTetrahedralSubgroup_eq_closure_coordinates :
    binaryTetrahedralSubgroup =
      Subgroup.closure {binaryDihedralRotation 2, weylElement⁻¹, tetrahedralOmega} := by
  rw [binaryTetrahedralSubgroup, binaryTetrahedralUnitSubgroup_eq_closure_coordinates,
    MonoidHom.map_closure]
  simp [unitaryEquivSpecialUnitaryGroup_quaternionUnitI,
    unitaryEquivSpecialUnitaryGroup_quaternionUnitJ, tetrahedralOmega]

/-- **The binary octahedral subgroup of `SU(2)` is generated by `{r, ω}`.** -/
theorem binaryOctahedralSubgroup_eq_closure :
    binaryOctahedralSubgroup = Subgroup.closure {octahedralGenerator, tetrahedralOmega} := by
  rw [binaryOctahedralSubgroup, binaryOctahedralUnitSubgroup_eq_closure, MonoidHom.map_closure]
  simp [octahedralGenerator, tetrahedralOmega]

/-- **The binary icosahedral subgroup of `SU(2)` is generated by `{ζ, ω}`.** -/
theorem binaryIcosahedralSubgroup_eq_closure :
    binaryIcosahedralSubgroup = Subgroup.closure {icosahedralGenerator, tetrahedralOmega} := by
  rw [binaryIcosahedralSubgroup, binaryIcosahedralUnitSubgroup_eq_closure, MonoidHom.map_closure]
  simp [icosahedralGenerator, tetrahedralOmega]

/-! ### Subgroup inclusions and indices in `SU(2)` -/

/-- The quaternion group `Q₈ = binaryDihedralSubgroup 2` sits inside
`binaryTetrahedralSubgroup`. -/
theorem binaryDihedralSubgroup_two_le_binaryTetrahedralSubgroup :
    binaryDihedralSubgroup 2 ≤ binaryTetrahedralSubgroup := by
  rw [binaryDihedralSubgroup_eq_closure 2, binaryTetrahedralSubgroup_eq_closure_coordinates]
  exact Subgroup.closure_mono (by intro x hx; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx ⊢; rcases hx with rfl | rfl <;> simp)

/-- `Q₈ = binaryDihedralSubgroup 2` has relative index `3` in `binaryTetrahedralSubgroup`. -/
@[simp]
theorem relIndex_binaryDihedralSubgroup_two_binaryTetrahedralSubgroup :
    (binaryDihedralSubgroup 2).relIndex binaryTetrahedralSubgroup = 3 := by
  have hmul := (binaryDihedralSubgroup 2).relIndex_mul_card binaryTetrahedralSubgroup
  rw [inf_of_le_left binaryDihedralSubgroup_two_le_binaryTetrahedralSubgroup,
    natCard_binaryDihedralSubgroup 2, natCard_binaryTetrahedralSubgroup] at hmul
  omega

/-- `binaryTetrahedralSubgroup` sits inside `binaryOctahedralSubgroup`. -/
theorem binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup :
    binaryTetrahedralSubgroup ≤ binaryOctahedralSubgroup :=
  Subgroup.map_mono binaryTetrahedralUnitSubgroup_le_binaryOctahedralUnitSubgroup

/-- `binaryTetrahedralSubgroup` has relative index `2` inside `binaryOctahedralSubgroup`. -/
@[simp]
theorem relIndex_binaryTetrahedralSubgroup_binaryOctahedralSubgroup :
    binaryTetrahedralSubgroup.relIndex binaryOctahedralSubgroup = 2 := by
  have hmul := binaryTetrahedralSubgroup.relIndex_mul_card binaryOctahedralSubgroup
  rw [inf_of_le_left binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup,
    natCard_binaryTetrahedralSubgroup, natCard_binaryOctahedralSubgroup] at hmul
  omega

/-- `binaryTetrahedralSubgroup` is normal inside `binaryOctahedralSubgroup`. -/
instance : (binaryTetrahedralSubgroup.subgroupOf binaryOctahedralSubgroup).Normal :=
  Subgroup.normal_of_index_eq_two relIndex_binaryTetrahedralSubgroup_binaryOctahedralSubgroup

/-- `binaryTetrahedralSubgroup` sits inside `binaryIcosahedralSubgroup`. -/
theorem binaryTetrahedralSubgroup_le_binaryIcosahedralSubgroup :
    binaryTetrahedralSubgroup ≤ binaryIcosahedralSubgroup :=
  Subgroup.map_mono binaryTetrahedralUnitSubgroup_le_binaryIcosahedralUnitSubgroup

/-- `binaryTetrahedralSubgroup` has relative index `5` inside `binaryIcosahedralSubgroup`. -/
@[simp]
theorem relIndex_binaryTetrahedralSubgroup_binaryIcosahedralSubgroup :
    binaryTetrahedralSubgroup.relIndex binaryIcosahedralSubgroup = 5 := by
  have hmul := binaryTetrahedralSubgroup.relIndex_mul_card binaryIcosahedralSubgroup
  rw [inf_of_le_left binaryTetrahedralSubgroup_le_binaryIcosahedralSubgroup,
    natCard_binaryTetrahedralSubgroup, natCard_binaryIcosahedralSubgroup] at hmul
  omega

/-! ### Concrete binary polyhedral subgroups of `SL₂(ℂ)` -/

/-- **The concrete binary tetrahedral subgroup of `SL₂(ℂ)` of order `24`.** -/
noncomputable def binaryTetrahedralSLSubgroup :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ) :=
  binaryTetrahedralSubgroup.map Matrix.specialUnitaryGroup.toSL

theorem binaryTetrahedralSLSubgroup_def :
    binaryTetrahedralSLSubgroup =
      binaryTetrahedralSubgroup.map Matrix.specialUnitaryGroup.toSL := (rfl)

/-- **The concrete binary octahedral subgroup of `SL₂(ℂ)` of order `48`.** -/
noncomputable def binaryOctahedralSLSubgroup :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ) :=
  binaryOctahedralSubgroup.map Matrix.specialUnitaryGroup.toSL

theorem binaryOctahedralSLSubgroup_def :
    binaryOctahedralSLSubgroup =
      binaryOctahedralSubgroup.map Matrix.specialUnitaryGroup.toSL := (rfl)

/-- **The concrete binary icosahedral subgroup of `SL₂(ℂ)` of order `120`.** -/
noncomputable def binaryIcosahedralSLSubgroup :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ) :=
  binaryIcosahedralSubgroup.map Matrix.specialUnitaryGroup.toSL

theorem binaryIcosahedralSLSubgroup_def :
    binaryIcosahedralSLSubgroup =
      binaryIcosahedralSubgroup.map Matrix.specialUnitaryGroup.toSL := (rfl)

/-- Multiplicative equivalence between `TauCeti.SU2.binaryTetrahedralSubgroup` and its image in
`SL₂(ℂ)`. -/
noncomputable def binaryTetrahedralSLEquiv :
    binaryTetrahedralSubgroup ≃* binaryTetrahedralSLSubgroup :=
  Subgroup.equivMapOfInjective _ _ Matrix.specialUnitaryGroup.toSL_injective

@[simp]
theorem coe_binaryTetrahedralSLEquiv (g : binaryTetrahedralSubgroup) :
    (binaryTetrahedralSLEquiv g : Matrix.SpecialLinearGroup (Fin 2) ℂ) =
      Matrix.specialUnitaryGroup.toSL (g : SU2) := (rfl)

/-- Multiplicative equivalence between `TauCeti.SU2.binaryOctahedralSubgroup` and its image in
`SL₂(ℂ)`. -/
noncomputable def binaryOctahedralSLEquiv :
    binaryOctahedralSubgroup ≃* binaryOctahedralSLSubgroup :=
  Subgroup.equivMapOfInjective _ _ Matrix.specialUnitaryGroup.toSL_injective

@[simp]
theorem coe_binaryOctahedralSLEquiv (g : binaryOctahedralSubgroup) :
    (binaryOctahedralSLEquiv g : Matrix.SpecialLinearGroup (Fin 2) ℂ) =
      Matrix.specialUnitaryGroup.toSL (g : SU2) := (rfl)

/-- Multiplicative equivalence between `TauCeti.SU2.binaryIcosahedralSubgroup` and its image in
`SL₂(ℂ)`. -/
noncomputable def binaryIcosahedralSLEquiv :
    binaryIcosahedralSubgroup ≃* binaryIcosahedralSLSubgroup :=
  Subgroup.equivMapOfInjective _ _ Matrix.specialUnitaryGroup.toSL_injective

@[simp]
theorem coe_binaryIcosahedralSLEquiv (g : binaryIcosahedralSubgroup) :
    (binaryIcosahedralSLEquiv g : Matrix.SpecialLinearGroup (Fin 2) ℂ) =
      Matrix.specialUnitaryGroup.toSL (g : SU2) := (rfl)

instance : Finite binaryTetrahedralSLSubgroup :=
  Finite.of_equiv _ binaryTetrahedralSLEquiv.toEquiv

instance : Finite binaryOctahedralSLSubgroup :=
  Finite.of_equiv _ binaryOctahedralSLEquiv.toEquiv

instance : Finite binaryIcosahedralSLSubgroup :=
  Finite.of_equiv _ binaryIcosahedralSLEquiv.toEquiv

@[simp]
theorem natCard_binaryTetrahedralSLSubgroup : Nat.card binaryTetrahedralSLSubgroup = 24 := by
  rw [← Nat.card_congr binaryTetrahedralSLEquiv.toEquiv, natCard_binaryTetrahedralSubgroup]

@[simp]
theorem natCard_binaryOctahedralSLSubgroup : Nat.card binaryOctahedralSLSubgroup = 48 := by
  rw [← Nat.card_congr binaryOctahedralSLEquiv.toEquiv, natCard_binaryOctahedralSubgroup]

@[simp]
theorem natCard_binaryIcosahedralSLSubgroup : Nat.card binaryIcosahedralSLSubgroup = 120 := by
  rw [← Nat.card_congr binaryIcosahedralSLEquiv.toEquiv, natCard_binaryIcosahedralSubgroup]

theorem binaryTetrahedralSLSubgroup_le_binaryOctahedralSLSubgroup :
    binaryTetrahedralSLSubgroup ≤ binaryOctahedralSLSubgroup :=
  Subgroup.map_mono binaryTetrahedralSubgroup_le_binaryOctahedralSubgroup

theorem binaryTetrahedralSLSubgroup_le_binaryIcosahedralSLSubgroup :
    binaryTetrahedralSLSubgroup ≤ binaryIcosahedralSLSubgroup :=
  Subgroup.map_mono binaryTetrahedralSubgroup_le_binaryIcosahedralSubgroup

end TauCeti.SU2
