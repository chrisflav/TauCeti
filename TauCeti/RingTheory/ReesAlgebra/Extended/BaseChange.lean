/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import TauCeti.RingTheory.ReesAlgebra.BaseChange
public import TauCeti.RingTheory.ReesAlgebra.Extended.Grading

/-!
# Base change of the extended Rees algebra

Let `I` be an ideal of a commutative semiring `R` and let `S` be a commutative `R`-algebra, with
extended ideal `IS = I.map (algebraMap R S)`. Extending scalars from `R` to `S` compares the two
extended Rees algebras:

`S ⊗[R] R[It, t⁻¹] ⟶ S[(IS)t, t⁻¹]`, `s ⊗ f ↦ s • map (algebraMap R S) _ f`.

This comparison factors through Mathlib's Laurent-polynomial pushout isomorphism
`AddMonoidAlgebra.scalarTensorEquiv R S : S ⊗[R] R[T;T⁻¹] ≃ₐ[S] S[T;T⁻¹]`. It is always a
surjective `ℤ`-graded `S`-algebra homomorphism, because `S[(IS)t, t⁻¹]` is generated over `S` by
`invT` and the degree-one monomials `C c * T 1` (`c ∈ IS`). When `S` is flat over `R`, tensoring the
inclusion `R[It, t⁻¹] ⊆ R[T;T⁻¹]` with `S` remains injective, so the comparison is a `ℤ`-graded
`S`-algebra isomorphism; geometrically, the Rees deformation `Spec R[It, t⁻¹] → 𝔸¹_R` commutes with
flat base change. Over commutative rings, restricting to nonnegative degrees recovers
`reesAlgebra.baseChangeHom`.

## Main definitions

* `Ideal.extendedReesAlgebra.baseChangeHom I S`: the comparison
  `S ⊗[R] I.extendedReesAlgebra →ₐ[S] (I.map (algebraMap R S)).extendedReesAlgebra`.
* `Ideal.extendedReesAlgebra.baseChangeGradedAlgHom I S`: the comparison as a `ℤ`-graded `S`-algebra
  homomorphism.
* `Ideal.extendedReesAlgebra.baseChangeEquiv I S`: for flat `S`, the comparison as an `S`-algebra
  isomorphism.
* `Ideal.extendedReesAlgebra.baseChangeGradedAlgHomSymm I S`: for flat `S`, its inverse as a
  `ℤ`-graded `S`-algebra homomorphism.

## Main results

* `Ideal.extendedReesAlgebra.baseChangeHom_tmul` and
  `Ideal.extendedReesAlgebra.coe_baseChangeHom_tmul`: explicit action on pure tensors `s ⊗ₜ f`.
* `Ideal.extendedReesAlgebra.baseChangeHom_surjective`: the comparison is always surjective.
* `Ideal.extendedReesAlgebra.baseChangeHom_injective`: for flat `S`, the comparison is injective.
* `Ideal.extendedReesAlgebra.baseChangeHom_mem_grade_iff`: for flat `S`, the comparison preserves
  and reflects `ℤ`-degrees.
* `reesAlgebra.toExtended_baseChangeHom`: compatibility with `reesAlgebra.baseChangeHom` along
  `reesAlgebra.toExtended`.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, GTM 150, §6.5.
* [The Stacks Project, Section *Blowing up*](https://stacks.math.columbia.edu/tag/01OF).
-/

public section

open LaurentPolynomial
open scoped TensorProduct

namespace Ideal.extendedReesAlgebra

section Semiring

variable {R : Type*} [CommSemiring R] (I : Ideal R) (S : Type*) [CommSemiring S] [Algebra R S]

/-- The composite `S ⊗[R] I.extendedReesAlgebra ⟶ S ⊗[R] R[T;T⁻¹] ≃ₐ[S] S[T;T⁻¹]`, before
restricting its codomain to `(I.map (algebraMap R S)).extendedReesAlgebra`. -/
private noncomputable def toLaurent : S ⊗[R] I.extendedReesAlgebra →ₐ[S] S[T;T⁻¹] :=
  (AddMonoidAlgebra.scalarTensorEquiv R S (M := ℤ)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id S S) I.extendedReesAlgebra.val)

private theorem toLaurent_tmul (s : S) (f : I.extendedReesAlgebra) :
    toLaurent I S (s ⊗ₜ f) =
      s • (map (algebraMap R S) Ideal.le_comap_map f : S[T;T⁻¹]) := by
  simp only [toLaurent, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
    Subalgebra.coe_val, AlgEquiv.toAlgHom_apply, AddMonoidAlgebra.scalarTensorEquiv_tmul,
    coe_map_apply]
  rfl

private theorem toLaurent_mem (x : S ⊗[R] I.extendedReesAlgebra) :
    toLaurent I S x ∈ (I.map (algebraMap R S)).extendedReesAlgebra := by
  induction x using TensorProduct.inductionOn with
  | tmul s f =>
    rw [toLaurent_tmul]
    exact Subalgebra.smul_mem _ (SetLike.coe_mem _) s
  | add x y hx hy => simpa only [map_add] using add_mem hx hy

/-- The base-change comparison
`S ⊗[R] I.extendedReesAlgebra →ₐ[S] (I.map (algebraMap R S)).extendedReesAlgebra`: it sends
`s ⊗ₜ f` to `s • map (algebraMap R S) Ideal.le_comap_map f`. -/
noncomputable def baseChangeHom :
    S ⊗[R] I.extendedReesAlgebra →ₐ[S] (I.map (algebraMap R S)).extendedReesAlgebra :=
  (toLaurent I S).codRestrict _ (toLaurent_mem I S)

private theorem coe_baseChangeHom (x : S ⊗[R] I.extendedReesAlgebra) :
    (baseChangeHom I S x : S[T;T⁻¹]) = toLaurent I S x :=
  (rfl)

/-- On pure tensors, `baseChangeHom I S` scales the mapped element by `s`. -/
@[simp]
theorem baseChangeHom_tmul (s : S) (f : I.extendedReesAlgebra) :
    baseChangeHom I S (s ⊗ₜ f) = s • map (algebraMap R S) Ideal.le_comap_map f :=
  Subtype.ext (toLaurent_tmul I S s f)

/-- Ambient Laurent-polynomial formula for `baseChangeHom I S` on pure tensors. -/
theorem coe_baseChangeHom_tmul (s : S) (f : I.extendedReesAlgebra) :
    (baseChangeHom I S (s ⊗ₜ f) : S[T;T⁻¹]) =
      s • AddMonoidAlgebra.mapRingHom (M := ℤ) (algebraMap R S) (f : R[T;T⁻¹]) := by
  rw [baseChangeHom_tmul, Subalgebra.coe_smul, coe_map_apply]

/-- **The comparison of extended Rees algebras is surjective**: `(IS).extendedReesAlgebra` is
generated over `S` by `invT` and the degree-one monomials `C c * T 1` (`c ∈ IS`). -/
theorem baseChangeHom_surjective : Function.Surjective (baseChangeHom I S) := by
  let φ : S ⊗[R] I.extendedReesAlgebra →ₐ[S] S[T;T⁻¹] :=
    ((I.map (algebraMap R S)).extendedReesAlgebra).val.comp (baseChangeHom I S)
  have hinv : (T (-1) : S[T;T⁻¹]) ∈ φ.range :=
    ⟨1 ⊗ₜ invT I, by simp [φ, coe_invT]⟩
  have hmon {c : S} (hc : c ∈ I.map (algebraMap R S)) : C c * T 1 ∈ φ.range := by
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨a, ha, rfl⟩ := hc
      exact ⟨1 ⊗ₜ monomialDegreeOne ha, by simp [φ, coe_monomialDegreeOne]⟩
    | zero => simp
    | add c d _ _ hc hd => simpa only [map_add, add_mul] using φ.range.add_mem hc hd
    | smul s c _ hc =>
      have hsc := φ.range.smul_mem hc s
      have heq : s • (C c * T 1 : S[T;T⁻¹]) = C (s • c) * T 1 := by
        rw [smul_eq_mul, Algebra.smul_def, LaurentPolynomial.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, map_mul, mul_assoc]
      rwa [heq] at hsc
  have hle : (I.map (algebraMap R S)).extendedReesAlgebra ≤ φ.range := by
    rw [← Ideal.adjoin_C_mul_T_union_invT_eq_extendedReesAlgebra, Set.singleton_union,
      Algebra.adjoin_le_iff]
    rintro _ (rfl | ⟨c, hc, rfl⟩)
    · exact hinv
    · exact hmon hc
  intro f
  obtain ⟨x, hx⟩ := hle f.2
  exact ⟨x, Subtype.ext hx⟩

/-- **The comparison of extended Rees algebras is injective after flat base change**: for flat `S`,
the inclusion `I.extendedReesAlgebra ⊆ R[T;T⁻¹]` remains injective after tensoring with `S`. -/
theorem baseChangeHom_injective [Module.Flat R S] : Function.Injective (baseChangeHom I S) := by
  have hmap : ⇑(Algebra.TensorProduct.map (AlgHom.id S S) I.extendedReesAlgebra.val) =
      ⇑(I.extendedReesAlgebra.val.toLinearMap.lTensor S) :=
    funext fun x ↦ (AlgHom.lTensor_toLinearMap_apply S I.extendedReesAlgebra.val x).symm
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id S S) I.extendedReesAlgebra.val) := by
    rw [hmap]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  intro x y hxy
  refine hinj ((AddMonoidAlgebra.scalarTensorEquiv R S (M := ℤ)).injective ?_)
  simpa only [coe_baseChangeHom, toLaurent, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] using
    congr_arg Subtype.val hxy

/-- `baseChangeHom I S` carries the base change of the degree-`d` piece of `I.extendedReesAlgebra`
into the degree-`d` piece of `(I.map (algebraMap R S)).extendedReesAlgebra`. -/
theorem baseChangeHom_mem_grade {d : ℤ} {x : S ⊗[R] I.extendedReesAlgebra}
    (hx : x ∈ (grade I d).baseChange S) :
    baseChangeHom I S x ∈ grade (I.map (algebraMap R S)) d := by
  rw [Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [TensorProduct.mk_apply, baseChangeHom_tmul, one_smul]
    exact map_mem_grade (algebraMap R S) Ideal.le_comap_map hf
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul s x _ hx => simpa only [map_smul] using Submodule.smul_mem _ s hx

/-- `baseChangeHom I S` packaged as a `ℤ`-graded `S`-algebra homomorphism, for the grading
`d ↦ (grade I d).baseChange S` of the source. -/
noncomputable def baseChangeGradedAlgHom :
    (fun d : ℤ ↦ (grade I d).baseChange S) →ₐᵍ[S] grade (I.map (algebraMap R S)) where
  __ := baseChangeHom I S
  map_mem := baseChangeHom_mem_grade I S

@[simp]
theorem baseChangeGradedAlgHom_apply (x : S ⊗[R] I.extendedReesAlgebra) :
    baseChangeGradedAlgHom I S x = baseChangeHom I S x :=
  (rfl)

/-- The `ℤ`-graded base-change comparison of extended Rees algebras is surjective. -/
theorem baseChangeGradedAlgHom_surjective : Function.Surjective (baseChangeGradedAlgHom I S) :=
  baseChangeHom_surjective I S

variable {I S} in
/-- For flat `S`, the base-change comparison of extended Rees algebras preserves and reflects
`ℤ`-degrees. -/
@[simp]
theorem baseChangeHom_mem_grade_iff [Module.Flat R S] {d : ℤ} {x : S ⊗[R] I.extendedReesAlgebra} :
    baseChangeHom I S x ∈ grade (I.map (algebraMap R S)) d ↔ x ∈ (grade I d).baseChange S :=
  Graded.map_mem_iff_of_injective (baseChangeGradedAlgHom I S) (baseChangeHom_injective I S)

/-- **Extended Rees algebras commute with flat base change**: for flat `S`, the comparison
`S ⊗[R] I.extendedReesAlgebra ≃ₐ[S] (I.map (algebraMap R S)).extendedReesAlgebra` is an `S`-algebra
isomorphism. -/
noncomputable def baseChangeEquiv [Module.Flat R S] :
    S ⊗[R] I.extendedReesAlgebra ≃ₐ[S] (I.map (algebraMap R S)).extendedReesAlgebra :=
  AlgEquiv.ofBijective (baseChangeHom I S)
    ⟨baseChangeHom_injective I S, baseChangeHom_surjective I S⟩

@[simp]
theorem baseChangeEquiv_apply [Module.Flat R S] (x : S ⊗[R] I.extendedReesAlgebra) :
    baseChangeEquiv I S x = baseChangeHom I S x :=
  (rfl)

/-- For flat `S`, the inverse of `baseChangeEquiv I S` as a `ℤ`-graded `S`-algebra homomorphism. -/
noncomputable def baseChangeGradedAlgHomSymm [Module.Flat R S] :
    grade (I.map (algebraMap R S)) →ₐᵍ[S] (fun d : ℤ ↦ (grade I d).baseChange S) where
  __ := (baseChangeEquiv I S).symm.toAlgHom
  map_mem {_ x} hx := by
    rw [← baseChangeHom_mem_grade_iff]
    simpa [← baseChangeEquiv_apply] using hx

@[simp]
theorem baseChangeGradedAlgHomSymm_apply [Module.Flat R S]
    (x : (I.map (algebraMap R S)).extendedReesAlgebra) :
    baseChangeGradedAlgHomSymm I S x = (baseChangeEquiv I S).symm x :=
  (rfl)

@[simp]
theorem baseChangeHom_baseChangeEquiv_symm_apply [Module.Flat R S]
    (x : (I.map (algebraMap R S)).extendedReesAlgebra) :
    baseChangeHom I S ((baseChangeEquiv I S).symm x) = x :=
  (baseChangeEquiv I S).apply_symm_apply x

@[simp]
theorem baseChangeEquiv_symm_baseChangeHom_apply [Module.Flat R S]
    (x : S ⊗[R] I.extendedReesAlgebra) :
    (baseChangeEquiv I S).symm (baseChangeHom I S x) = x :=
  (baseChangeEquiv I S).symm_apply_apply x

theorem baseChangeGradedAlgHom_rightInverse [Module.Flat R S] :
    Function.RightInverse (baseChangeGradedAlgHomSymm I S) (baseChangeGradedAlgHom I S) :=
  (baseChangeEquiv I S).apply_symm_apply

theorem baseChangeGradedAlgHom_leftInverse [Module.Flat R S] :
    Function.LeftInverse (baseChangeGradedAlgHomSymm I S) (baseChangeGradedAlgHom I S) :=
  (baseChangeEquiv I S).symm_apply_apply

end Semiring

end Ideal.extendedReesAlgebra

/-! ### Compatibility with `reesAlgebra.baseChangeHom` -/

namespace reesAlgebra

variable {R : Type*} [CommRing R] (I : Ideal R) (S : Type*) [CommRing S] [Algebra R S]

/-- Embedding `reesAlgebra` into `Ideal.extendedReesAlgebra` commutes with base-change comparison
homomorphisms. -/
theorem toExtended_baseChangeHom (x : S ⊗[R] reesAlgebra I) :
    reesAlgebra.toExtended (I.map (algebraMap R S)) (reesAlgebra.baseChangeHom I S x) =
      Ideal.extendedReesAlgebra.baseChangeHom I S
        (Algebra.TensorProduct.map (AlgHom.id S S) (reesAlgebra.toExtended I) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s f =>
    have hmap : ∀ p : Polynomial R,
        (p.map (algebraMap R S)).toLaurent =
          AddMonoidAlgebra.mapRingHom (M := ℤ) (algebraMap R S) p.toLaurent := fun p ↦ by
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
      | monomial n r =>
        rw [Polynomial.map_monomial, Polynomial.toLaurent_C_mul_T, Polynomial.toLaurent_C_mul_T,
          ← single_eq_C_mul_T, ← single_eq_C_mul_T, AddMonoidAlgebra.mapRingHom_single]
    apply Subtype.ext
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      Ideal.extendedReesAlgebra.coe_baseChangeHom_tmul, reesAlgebra.coe_toExtended,
      reesAlgebra.coe_toExtended, reesAlgebra.coe_baseChangeHom_tmul, Algebra.smul_def,
      Algebra.smul_def, Polynomial.algebraMap_eq, map_mul, Polynomial.toLaurent_C,
      LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hmap]
  | add x y hx hy => simp only [map_add, hx, hy]

end reesAlgebra
