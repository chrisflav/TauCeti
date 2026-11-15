/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Supported
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.RingTheory.TensorProduct.IsIntegral

/-!
# Extension of scalars of multivariate polynomials

Under the identification `A ⊗[R] R[X_σ] ≃ A[X_σ]` of `MvPolynomial.algebraTensorAlgEquiv`, the
power `(u - a v) ^ i` of polynomials `u, v` over `R` and a scalar `a` of `A` is the image of the
tensor `∑ₗ (-1)ˡ (i choose l) aˡ ⊗ uⁱ⁻ˡ vˡ`. Contracting the `A`-leg of this tensor against a
linear functional gives a weighted sum of the binomial terms. For `A = R[t]` and `a = t`,
coefficient functionals extract individual terms: the coefficient of `tⁿ` in `(u - t v) ^ i`
is `(-1)ⁿ (i choose n) uⁱ⁻ⁿ vⁿ`.

An element of `R[X_σ] ⊗[R] N` is determined by its coefficients, the images of the coefficient
functionals `MvPolynomial.lcoeff R e` on the polynomial leg.

Evaluating `S[X_ι]` at `1 ⊗ₜ yᵢ` inside `S ⊗[R] A` factors as `(algebraTensorAlgEquiv R S).symm`
followed by `lTensor S (aeval y)`
(`MvPolynomial.aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm`,
`MvPolynomial.aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm`). Consequently, module-finiteness
and integrality of `MvPolynomial.aeval y` are preserved under arbitrary base change `S / R`
(`MvPolynomial.finite_aeval_one_tmul`, `MvPolynomial.isIntegral_aeval_one_tmul`).

Restricting variables to a subset `s : Set σ` commutes with extension of scalars: the base change
`A ⊗[R] supported R s` is canonically isomorphic as an `A`-algebra to `supported A s`
(`MvPolynomial.supportedAlgebraTensorAlgEquiv`), compatibly with ambient coercion and monotone
inclusion of variable sets.

## Main declarations

* `MvPolynomial.algebraTensorAlgEquiv_sum_tmul_pow_mul_pow`: the binomial expansion of
  `(u - a v) ^ i` on the tensor side.
* `MvPolynomial.ext_lid_rTensor_lcoeff`: elements of `R[X_σ] ⊗[R] N` with the same coefficients
  are equal.
* `MvPolynomial.aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm`,
  `MvPolynomial.aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm`: `aeval (1 ⊗ₜ y ·)` factors
  through `MvPolynomial.algebraTensorAlgEquiv` and `Algebra.TensorProduct.lTensor`.
* `MvPolynomial.finite_aeval_one_tmul`, `MvPolynomial.isIntegral_aeval_one_tmul`: scalar extension
  preserves module-finiteness and integrality of `MvPolynomial.aeval`.
* `MvPolynomial.supportedAlgebraTensorAlgEquiv`: `A`-algebra equivalence
  `A ⊗[R] supported R s ≃ₐ[A] supported A s`.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section Binomial

variable {R : Type*} [CommRing R] {σ : Type*} {A : Type*} [CommRing A] [Algebra R A]

/-- The binomial expansion of `(u - a v) ^ i` under `A ⊗[R] R[X_σ] ≃ A[X_σ]`: it is the image of
`∑ₗ (-1)ˡ (i choose l) aˡ ⊗ uⁱ⁻ˡ vˡ`. -/
theorem algebraTensorAlgEquiv_sum_tmul_pow_mul_pow (a : A) (u v : MvPolynomial σ R) (i : ℕ) :
    algebraTensorAlgEquiv R A
        (∑ l ∈ Finset.range (i + 1),
          (((-1) ^ l * (i.choose l : R)) • a ^ l) ⊗ₜ[R] (u ^ (i - l) * v ^ l)) =
      (map (algebraMap R A) u - C a * map (algebraMap R A) v) ^ i := by
  rw [sub_eq_neg_add, add_pow, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [algebraTensorAlgEquiv_tmul, smul_eq_C_mul, Algebra.smul_def]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

end Binomial

section Ext

variable {R : Type*} [CommSemiring R] {σ : Type*} {N : Type*} [AddCommMonoid N] [Module R N]

/-- Elements of `R[X_σ] ⊗[R] N` with the same coefficients are equal. -/
theorem ext_lid_rTensor_lcoeff {x y : MvPolynomial σ R ⊗[R] N}
    (h : ∀ e, TensorProduct.lid R N ((lcoeff R e).rTensor N x) =
      TensorProduct.lid R N ((lcoeff R e).rTensor N y)) : x = y := by
  classical
  have hcoord (e : σ →₀ ℕ) : (basisMonomials σ R).coord e = lcoeff R e :=
    (basisMonomials σ R).ext fun s ↦ by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self]
      simp [coeff_monomial, Finsupp.single_apply]
  apply (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials σ R)).injective
  ext e
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply,
    hcoord, h]

end Ext

section BaseChange

section CommSemiring

variable {ι R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Evaluating polynomials over `S` at `1 ⊗ₜ[R] y i` in `S ⊗[R] A` factors as the `S`-algebra
isomorphism `(algebraTensorAlgEquiv R S).symm` followed by `lTensor S (aeval y)`. -/
theorem aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm {S : Type*} [CommSemiring S]
    [Algebra R S] (y : ι → A) :
    aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i) =
      (Algebra.TensorProduct.lTensor S (aeval (R := R) y)).comp
        (algebraTensorAlgEquiv R S).symm.toAlgHom :=
  algHom_ext fun i ↦ by simp

/-- Evaluating a polynomial over `S` at `1 ⊗ₜ[R] y i` in `S ⊗[R] A` agrees with transporting along
`(algebraTensorAlgEquiv R S).symm` and applying `id_S ⊗ aeval y`. -/
theorem aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm {S : Type*} [CommSemiring S]
    [Algebra R S] (y : ι → A) (p : MvPolynomial ι S) :
    aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i) p =
      Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)
        ((algebraTensorAlgEquiv R S).symm p) := by
  have hl : (Algebra.TensorProduct.lTensor (S := S) S (aeval (R := R) y)).restrictScalars R =
      Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y) := by
    ext <;> simp
  rw [aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, ← AlgHom.restrictScalars_apply R, hl]

private theorem aeval_one_tmul_toRingHom {S : Type*} [CommSemiring S] [Algebra R S] (y : ι → A) :
    (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.comp
        (algebraTensorAlgEquiv R S).symm.toRingHom :=
  RingHom.ext (aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm y)

end CommSemiring

section CommRing

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Module-finiteness of `MvPolynomial.aeval y` is preserved under base change to any `R`-algebra
`S`. -/
theorem finite_aeval_one_tmul (S : Type*) [CommRing S] [Algebra R S] {y : ι → A}
    (hfin : (aeval (R := R) y).Finite) :
    (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).Finite := by
  rw [AlgHom.Finite, aeval_one_tmul_toRingHom]
  exact (RingHom.Finite.tensorProductMap (AlgHom.Finite.id R S) hfin).comp
    (RingHom.Finite.of_surjective _ (algebraTensorAlgEquiv R S).symm.surjective)

/-- Integrality of `MvPolynomial.aeval y` is preserved under base change to any `R`-algebra `S`. -/
theorem isIntegral_aeval_one_tmul (S : Type*) [CommRing S] [Algebra R S] {y : ι → A}
    (hint : (aeval (R := R) y).toRingHom.IsIntegral) :
    (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).toRingHom.IsIntegral := by
  rw [aeval_one_tmul_toRingHom]
  exact RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_of_surjective _ (algebraTensorAlgEquiv R S).symm.surjective)
    (RingHom.IsIntegral.tensorProductMap (f := AlgHom.id R S)
      (RingHom.isIntegral_of_surjective _ Function.surjective_id) hint)

end CommRing

section Supported

variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

variable (R A) in
/-- Extension of scalars of the polynomial subalgebra `MvPolynomial.supported R s` to an
`R`-algebra `A` is canonically isomorphic as an `A`-algebra to `MvPolynomial.supported A s`. -/
noncomputable def supportedAlgebraTensorAlgEquiv (s : Set σ) :
    A ⊗[R] supported R s ≃ₐ[A] supported A s :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) (supportedEquivMvPolynomial s)).trans
    ((algebraTensorAlgEquiv R A).trans (supportedEquivMvPolynomial s).symm)

@[simp]
theorem coe_supportedAlgebraTensorAlgEquiv_tmul (s : Set σ) (a : A) (p : supported R s) :
    (supportedAlgebraTensorAlgEquiv R A s (a ⊗ₜ[R] p) : MvPolynomial σ A) =
      a • map (algebraMap R A) (p : MvPolynomial σ R) := by
  simp only [supportedAlgebraTensorAlgEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom,
    AlgEquiv.coe_refl, id_eq, algebraTensorAlgEquiv_tmul, map_smul, SetLike.val_smul,
    coe_supportedEquivMvPolynomial_symm, ← map_rename, rename_coe_supportedEquivMvPolynomial]

/-- Coercing `supportedAlgebraTensorAlgEquiv` to `MvPolynomial σ A` agrees with applying
`MvPolynomial.algebraTensorAlgEquiv` after `lTensor` of the subalgebra inclusion. -/
theorem coe_supportedAlgebraTensorAlgEquiv_eq (s : Set σ) (u : A ⊗[R] supported R s) :
    (supportedAlgebraTensorAlgEquiv R A s u : MvPolynomial σ A) =
      algebraTensorAlgEquiv R A
        (Algebra.TensorProduct.lTensor (S := A) A (supported R s).val u) := by
  induction u using TensorProduct.inductionOn with
  | tmul a p => simp
  | add x y hx hy => simp [hx, hy]

@[simp]
theorem supportedAlgebraTensorAlgEquiv_symm_mk_map (s : Set σ) (p : supported R s)
    (hp : map (algebraMap R A) (p : MvPolynomial σ R) ∈ supported A s) :
    (supportedAlgebraTensorAlgEquiv R A s).symm ⟨map (algebraMap R A) p, hp⟩ =
      1 ⊗ₜ[R] p := by
  apply (supportedAlgebraTensorAlgEquiv R A s).injective
  apply Subtype.ext
  simp

theorem supportedAlgebraTensorAlgEquiv_symm_X (s : Set σ) {i : σ} (hi : i ∈ s)
    (hx : X i ∈ supported A s := Algebra.subset_adjoin ⟨i, hi, rfl⟩) :
    (supportedAlgebraTensorAlgEquiv R A s).symm ⟨X i, hx⟩ =
      1 ⊗ₜ[R] ⟨X i, Algebra.subset_adjoin ⟨i, hi, rfl⟩⟩ := by
  apply (supportedAlgebraTensorAlgEquiv R A s).injective
  apply Subtype.ext
  simp

/-- `MvPolynomial.supportedAlgebraTensorAlgEquiv` commutes with the canonical inclusions induced by
`s ⊆ t`. -/
@[simp]
theorem supportedAlgebraTensorAlgEquiv_lTensor_inclusion {s t : Set σ} (hst : s ⊆ t)
    (u : A ⊗[R] supported R s) :
    supportedAlgebraTensorAlgEquiv R A t
        (Algebra.TensorProduct.lTensor (S := A) A (Subalgebra.inclusion (supported_mono hst)) u) =
      Subalgebra.inclusion (supported_mono hst) (supportedAlgebraTensorAlgEquiv R A s u) := by
  apply Subtype.ext
  rw [coe_supportedAlgebraTensorAlgEquiv_eq, Subalgebra.coe_inclusion,
    coe_supportedAlgebraTensorAlgEquiv_eq]
  congr 1
  induction u using TensorProduct.inductionOn with
  | tmul a p => simp
  | add x y hx hy => simp [hx, hy]

end Supported

end BaseChange

end MvPolynomial
