/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantizedEnveloping.Basic

/-!
# Diagonal rescaling automorphisms of quantized enveloping algebras

For any Cartan datum `D : CartanDatum ι X Y` and parameter `q : K`, a family of units
`c : ι → Kˣ` defines a `K`-algebra automorphism `QuantizedEnvelopingAlgebra.rescale D q c` acting
on the generators by `Eᵢ ↦ cᵢ Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ Fᵢ`, and `K_y ↦ K_y`. No genericity assumption on
`q` is required.

When `q ≠ 0`, conjugation by any toral generator `K_y` is the rescaling automorphism with
parameters `cᵢ = q^⟨αᵢ, y⟩` (`TauCeti.QuantizedEnvelopingAlgebra.k_mul_mul_k_neg`).

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.rescale`: the group homomorphism
  `(ι → Kˣ) →* (QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q)`.
* `TauCeti.QuantizedEnvelopingAlgebra.k_mul_mul_k_neg`: for `q ≠ 0`, conjugation `x ↦ K_y x K_(-y)`
  coincides with `rescale D q (fun i => Units.mk0 q hq ^ D.pairing (D.root i) y)`.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §4.6.
* Follows the rank-one pattern in `TauCeti.QuantumGroups.UqSl2.Rescale`.
-/

public section

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

private noncomputable def rescaleAlgHom (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  lift
    { e := fun i => (c i : K) • e D q i
      f := fun i => (((c i)⁻¹ : Kˣ) : K) • f D q i
      k := k D q
      k_zero := k_zero D q
      k_mul_k := k_mul_k D q
      k_mul_e_mul_k_neg := fun y i => by
        rw [mul_smul_comm, smul_mul_assoc, k_mul_e_mul_k_neg, smul_comm]
      k_mul_f_mul_k_neg := fun y i => by
        rw [mul_smul_comm, smul_mul_assoc, k_mul_f_mul_k_neg, smul_comm]
      e_mul_f_sub_f_mul_e_self := fun i => by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, Units.mul_inv, Units.inv_mul, one_smul,
          one_smul, e_mul_f_sub_f_mul_e_self]
      e_mul_f_of_ne := fun {i j} hij => by
        rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (c i : K), e_mul_f_of_ne D q hij]
      serre_e := fun {i j} hij => by
        simp [serreElement_smul, serre_e D q hij]
      serre_f := fun {i j} hij => by
        simp [serreElement_smul, serre_f D q hij] }

@[simp]
private theorem rescaleAlgHom_e (c : ι → Kˣ) (i : ι) :
    rescaleAlgHom D q c (e D q i) = (c i : K) • e D q i :=
  lift_e _ i

@[simp]
private theorem rescaleAlgHom_f (c : ι → Kˣ) (i : ι) :
    rescaleAlgHom D q c (f D q i) = (((c i)⁻¹ : Kˣ) : K) • f D q i :=
  lift_f _ i

@[simp]
private theorem rescaleAlgHom_k (c : ι → Kˣ) (y : Y) :
    rescaleAlgHom D q c (k D q y) = k D q y :=
  lift_k _ y

private theorem rescaleAlgHom_one :
    rescaleAlgHom D q 1 = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp

private theorem rescaleAlgHom_mul (c c' : ι → Kˣ) :
    rescaleAlgHom D q (c * c') = (rescaleAlgHom D q c).comp (rescaleAlgHom D q c') := by
  ext <;> simp [smul_smul, mul_comm]

/-- Diagonal rescaling automorphisms of `QuantizedEnvelopingAlgebra D q`: a family of units
`c : ι → Kˣ` acts by `Eᵢ ↦ cᵢ Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ Fᵢ`, and `K_y ↦ K_y`. -/
noncomputable def rescale :
    (ι → Kˣ) →* (QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q) where
  toFun c :=
    AlgEquiv.ofAlgHom (rescaleAlgHom D q c) (rescaleAlgHom D q c⁻¹)
      (by rw [← rescaleAlgHom_mul, mul_inv_cancel, rescaleAlgHom_one])
      (by rw [← rescaleAlgHom_mul, inv_mul_cancel, rescaleAlgHom_one])
  map_one' := AlgEquiv.coe_toAlgHom_injective (rescaleAlgHom_one D q)
  map_mul' c c' := AlgEquiv.coe_toAlgHom_injective (rescaleAlgHom_mul D q c c')

variable {D q}

@[simp]
theorem rescale_e (c : ι → Kˣ) (i : ι) :
    rescale D q c (e D q i) = (c i : K) • e D q i :=
  rescaleAlgHom_e D q c i

@[simp]
theorem rescale_f (c : ι → Kˣ) (i : ι) :
    rescale D q c (f D q i) = (((c i)⁻¹ : Kˣ) : K) • f D q i :=
  rescaleAlgHom_f D q c i

@[simp]
theorem rescale_k (c : ι → Kˣ) (y : Y) :
    rescale D q c (k D q y) = k D q y :=
  rescaleAlgHom_k D q c y

@[simp]
theorem rescale_symm (c : ι → Kˣ) :
    (rescale D q c).symm = rescale D q c⁻¹ := by
  ext x
  apply (rescale D q c).injective
  rw [AlgEquiv.apply_symm_apply, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    AlgEquiv.one_apply]

/-- Rescaling `Eᵢ^(n)_(qᵢ)` multiplies by `cᵢ ^ n`. -/
@[simp]
theorem rescale_quantumDividedPower_e (c : ι → Kˣ) (i : ι) (n : ℕ) :
    rescale D q c (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      (c i : K) ^ n • quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n := by
  rw [quantumDividedPower_def, map_smul, map_pow, rescale_e, smul_pow, smul_comm,
    ← quantumDividedPower_def]

/-- Rescaling `Fᵢ^(n)_(qᵢ)` multiplies by `(cᵢ⁻¹) ^ n`. -/
@[simp]
theorem rescale_quantumDividedPower_f (c : ι → Kˣ) (i : ι) (n : ℕ) :
    rescale D q c (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      (((c i)⁻¹ : Kˣ) : K) ^ n • quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n := by
  rw [quantumDividedPower_def, map_smul, map_pow, rescale_f, smul_pow, smul_comm,
    ← quantumDividedPower_def]

/-- When `q ≠ 0`, conjugation by `K_y` coincides with the diagonal rescaling automorphism with
parameters `cᵢ = q^⟨αᵢ, y⟩`. -/
theorem k_mul_mul_k_neg (hq : q ≠ 0) (y : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q y * x * k D q (-y) =
      rescale D q (fun i => Units.mk0 q hq ^ D.pairing (D.root i) y) x := by
  let conjHom : QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D q :=
    { toFun := fun z => k D q y * z * k D q (-y)
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_assoc]
      map_zero' := by simp
      map_add' := fun a b => by simp [mul_add, add_mul]
      commutes' := fun r => by simp [Algebra.algebraMap_eq_smul_one] }
  have hEq : conjHom = (rescale D q fun i => Units.mk0 q hq ^ D.pairing (D.root i) y).toAlgHom := by
    ext i
    · simpa [conjHom] using k_mul_e_mul_k_neg D q y i
    · simpa [conjHom, ← zpow_neg] using k_mul_f_mul_k_neg D q y i
    · simp [conjHom, add_comm y, add_neg_cancel_right]
  exact DFunLike.congr_fun hEq x

end TauCeti.QuantizedEnvelopingAlgebra
