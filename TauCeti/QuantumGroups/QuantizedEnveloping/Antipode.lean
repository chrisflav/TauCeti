/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
public import TauCeti.QuantumGroups.QuantizedEnveloping.Hopf

/-!
# The square, inverse, and divided-power values of the antipode

For a symmetrizable Cartan datum `D : CartanDatum ι X Y` and a generic parameter `q : K`
(`[Fact (IsGenericQuantumParameter q)]`), the antipode `S` of `QuantizedEnvelopingAlgebra D q` is
not an involution. Its square `S²` coincides with the diagonal rescaling automorphism
`rescale D q (antipodeSqScale D q)` sending `Eᵢ ↦ qᵢ⁻² Eᵢ`, `Fᵢ ↦ qᵢ² Fᵢ`, and `K_y ↦ K_y`. Unlike
the rank-one formula `S²(x) = K⁻¹ x K`, expressing `S²` as a diagonal rescaling holds on every
symmetrizable datum `(X, Y)` without requiring a half-sum of positive coroots in `Y`.

Because `rescale D q (antipodeSqScale D q)` is an algebra equivalence, `S` is bijective
(`antipode_bijective`), giving:

* `antipodeEquiv : QuantizedEnvelopingAlgebra D q ≃ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ`;
* explicit generator values for `TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q)`:
  `S⁻¹(Eᵢ) = -Eᵢ Kᵢ⁻¹`, `S⁻¹(Fᵢ) = -Kᵢ Fᵢ`, `S⁻¹(K_y) = K_(-y)`;
* closed formulas for `S(Eᵢ^(n))` and `S(Fᵢ^(n))` on all quantum divided powers.

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.antipodeSqScale`: the unit tuple `i ↦ qᵢ⁻²`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipode_antipode`: `S(S(x)) = rescale D q (i ↦ qᵢ⁻²) x`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipode_bijective` and
  `TauCeti.QuantizedEnvelopingAlgebra.antipodeEquiv`: bijectivity of `S` and the resulting algebra
  isomorphism onto the opposite algebra.
* `TauCeti.QuantizedEnvelopingAlgebra.inverseAntipode_e`,
  `TauCeti.QuantizedEnvelopingAlgebra.inverseAntipode_f`, and
  `TauCeti.QuantizedEnvelopingAlgebra.inverseAntipode_k`: values of `S⁻¹` on generators.
* `TauCeti.QuantizedEnvelopingAlgebra.antipode_quantumDividedPower_e` and
  `TauCeti.QuantizedEnvelopingAlgebra.antipode_quantumDividedPower_f`: values of `S` on quantum
  divided powers.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §§4.8–4.9.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* Generalizes `TauCeti.QuantumGroups.UqSl2.Antipode` from `U_q(sl₂)` to arbitrary symmetrizable
  Cartan data on full lattices `(X, Y)`.
-/

public section

open HopfAlgebra

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K) [Fact (IsGenericQuantumParameter q)]

/-- The tuple of units `i ↦ qᵢ⁻² = (q^(dᵢ))⁻¹ ^ 2` governing the square of the antipode. -/
noncomputable def antipodeSqScale : ι → Kˣ :=
  fun i =>
    (Units.mk0 (q ^ D.symmetrizer i)
      ((Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)).ne_zero)⁻¹ ^ 2

@[simp]
theorem coe_antipodeSqScale (i : ι) :
    ((antipodeSqScale D q i : Kˣ) : K) = (q ^ D.symmetrizer i)⁻¹ ^ 2 := by
  simp [antipodeSqScale]

theorem coe_antipodeSqScale_inv (i : ι) :
    (((antipodeSqScale D q i)⁻¹ : Kˣ) : K) = (q ^ D.symmetrizer i) ^ 2 := by
  simp [antipodeSqScale]

private theorem opComm_antipodeOp_comp_antipodeOp :
    (AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q) =
      (rescale D q (antipodeSqScale D q)).toAlgHom := by
  apply hom_ext
  · intro i
    calc
      ((AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q)) (e D q i) =
          simpleKInv D q i * (e D q i * simpleK D q i) := by
        simp [antipode_mul_antidistrib, mul_assoc]
      _ = (rescale D q (antipodeSqScale D q)).toAlgHom (e D q i) := by
        rw [← mul_assoc, simpleKInv_mul_e, D.cartan_apply_self, smul_mul_assoc, mul_assoc]
        simp [zpow_neg, inv_pow]
  · intro i
    calc
      ((AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q)) (f D q i) =
          simpleKInv D q i * (f D q i * simpleK D q i) := by
        simp [antipode_mul_antidistrib, mul_assoc]
      _ = (rescale D q (antipodeSqScale D q)).toAlgHom (f D q i) := by
        rw [← mul_assoc, simpleKInv_mul_f, D.cartan_apply_self, smul_mul_assoc, mul_assoc]
        simp
  · intro y
    simp

/-- The square of the antipode is the diagonal rescaling automorphism `Eᵢ ↦ qᵢ⁻² Eᵢ`,
`Fᵢ ↦ qᵢ² Fᵢ`, `K_y ↦ K_y`. -/
theorem antipode_antipode (x : QuantizedEnvelopingAlgebra D q) :
    antipode K (antipode K x) = rescale D q (antipodeSqScale D q) x :=
  AlgHom.congr_fun (opComm_antipodeOp_comp_antipodeOp D q) x

/-- `S(S(Eᵢ)) = qᵢ⁻² • Eᵢ`. -/
theorem antipode_antipode_e (i : ι) :
    antipode K (antipode K (e D q i)) = (q ^ D.symmetrizer i)⁻¹ ^ 2 • e D q i := by
  rw [antipode_antipode, rescale_e, coe_antipodeSqScale]

/-- `S(S(Fᵢ)) = qᵢ² • Fᵢ`. -/
theorem antipode_antipode_f (i : ι) :
    antipode K (antipode K (f D q i)) = (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rw [antipode_antipode, rescale_f, coe_antipodeSqScale_inv]

/-- `S(S(K_y)) = K_y`. -/
theorem antipode_antipode_k (y : Y) :
    antipode K (antipode K (k D q y)) = k D q y := by
  rw [antipode_antipode, rescale_k]

/-- The antipode of `QuantizedEnvelopingAlgebra D q` is bijective. -/
theorem antipode_bijective :
    Function.Bijective
      (antipode K : QuantizedEnvelopingAlgebra D q →ₗ[K] QuantizedEnvelopingAlgebra D q) := by
  have h :
      Function.Bijective
        ((antipode K : QuantizedEnvelopingAlgebra D q →ₗ[K] QuantizedEnvelopingAlgebra D q) ∘
          antipode K) := by
    simpa only [Function.comp_def, antipode_antipode] using
      (rescale D q (antipodeSqScale D q)).bijective
  exact ⟨.of_comp h.1, .of_comp h.2⟩

/-- The antipode as an algebra isomorphism onto the opposite algebra. -/
noncomputable def antipodeEquiv :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (antipodeOp D q)
    (MulOpposite.opEquiv.bijective.comp (antipode_bijective D q))

@[simp]
theorem antipodeEquiv_toAlgHom :
    (antipodeEquiv D q).toAlgHom = antipodeOp D q := (rfl)

@[simp]
theorem antipodeEquiv_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeEquiv D q x = MulOpposite.op (antipode K x) := (rfl)

/-- Explicit formula for the inverse antipode in terms of `S` and diagonal rescaling:
`S⁻¹(x) = rescale D q (i ↦ qᵢ²) (S(x))`. -/
theorem inverseAntipode_apply (x : QuantizedEnvelopingAlgebra D q) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) x =
      rescale D q (antipodeSqScale D q)⁻¹ (antipode K x) := by
  apply (antipode_bijective D q).injective
  rw [TauCeti.HopfAlgebra.antipode_inverseAntipode]
  have hcomm :
      antipode K (rescale D q (antipodeSqScale D q)⁻¹ (antipode K x)) =
        rescale D q (antipodeSqScale D q)⁻¹ (antipode K (antipode K x)) := by
    simpa only [rescaleBialgEquiv_apply] using
      (BialgHomClass.map_antipode (rescaleBialgEquiv D q (antipodeSqScale D q)⁻¹)
        (antipode K x)).symm
  rw [hcomm, antipode_antipode, ← rescale_symm, AlgEquiv.symm_apply_apply]

/-- `(antipodeEquiv D q).symm (op x) = S⁻¹(x)`. -/
@[simp]
theorem antipodeEquiv_symm_op (x : QuantizedEnvelopingAlgebra D q) :
    (antipodeEquiv D q).symm (MulOpposite.op x) =
      TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) x := by
  rw [AlgEquiv.symm_apply_eq, antipodeEquiv_apply, MulOpposite.op_inj,
    TauCeti.HopfAlgebra.antipode_inverseAntipode]

/-- `S⁻¹(Eᵢ) = -Eᵢ Kᵢ⁻¹`. -/
@[simp]
theorem inverseAntipode_e (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (e D q i) =
      -(e D q i * simpleKInv D q i) := by
  apply (antipode_bijective D q).injective
  simp [antipode_mul_antidistrib, ← mul_assoc]

/-- `S⁻¹(Fᵢ) = -Kᵢ Fᵢ`. -/
@[simp]
theorem inverseAntipode_f (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (f D q i) =
      -(simpleK D q i * f D q i) := by
  apply (antipode_bijective D q).injective
  simp [antipode_mul_antidistrib, mul_assoc]

/-- `S⁻¹(K_y) = K_(-y)`. -/
@[simp]
theorem inverseAntipode_k (y : Y) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (k D q y) = k D q (-y) := by
  apply (antipode_bijective D q).injective
  simp

/-! ### Antipodes of quantum divided powers -/

/-- Antipode of a raising divided power:
`S(Eᵢ^(n)) = ((-1)^n * qᵢ^(n(n - 1))) • (Kᵢ^(-n) * Eᵢ^(n))`. -/
theorem antipode_quantumDividedPower_e (i : ι) (n : ℕ) :
    antipode K (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (simpleKInv D q i ^ n * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) := by
  have h1 :
      antipode K (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
        quantumDividedPower (q ^ D.symmetrizer i) (-normE D q i) n := by
    have hop := AlgHom.map_quantumDividedPower (antipodeOp D q) (q ^ D.symmetrizer i) (e D q i) n
    rw [antipodeOp_apply, antipodeOp_apply, antipode_e_eq_neg_normE] at hop
    exact (congr_arg MulOpposite.unop hop).trans (MulOpposite.unop_quantumDividedPower _ _ _)
  rw [h1, ← neg_one_smul K (normE D q i), quantumDividedPower_smul, quantumDividedPower_normE,
    smul_smul]

/-- Antipode of a lowering divided power:
`S(Fᵢ^(n)) = ((-1)^n * (qᵢ⁻¹)^(n(n - 1))) • (Fᵢ^(n) * Kᵢ^n)`. -/
theorem antipode_quantumDividedPower_f (i : ι) (n : ℕ) :
    antipode K (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      ((-1 : K) ^ n * ((q ^ D.symmetrizer i)⁻¹) ^ (n * (n - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n * simpleK D q i ^ n) := by
  have h1 :
      antipode K (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
        quantumDividedPower (q ^ D.symmetrizer i) (-normF D q i) n := by
    have hop := AlgHom.map_quantumDividedPower (antipodeOp D q) (q ^ D.symmetrizer i) (f D q i) n
    rw [antipodeOp_apply, antipodeOp_apply, antipode_f_eq_neg_normF] at hop
    exact (congr_arg MulOpposite.unop hop).trans (MulOpposite.unop_quantumDividedPower _ _ _)
  rw [h1, ← neg_one_smul K (normF D q i), quantumDividedPower_smul, quantumDividedPower_normF,
    smul_smul]

end TauCeti.QuantizedEnvelopingAlgebra
