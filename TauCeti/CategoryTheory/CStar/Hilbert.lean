/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.Category
public import TauCeti.CategoryTheory.CStar.Basic

/-!
# Complex Hilbert spaces as a C*-category

`TauCeti.HilbertCat 𝕜` is defined in `TauCeti.Analysis.InnerProductSpace.Category` over an
arbitrary `RCLike` field `𝕜` without C\*-algebra imports. Specializing to `𝕜 = ℂ` equips
`HilbertCat ℂ` with its canonical `TauCeti.CStarCategory` instance: Hom spaces are the Banach
spaces `X →L[ℂ] Y` with the operator norm, composition is contractive, the Hilbert-space adjoint
satisfies `‖f ≫ dagger f‖ = ‖f‖ ^ 2`, and the positive operator
`(ContinuousLinearMap.adjoint f).comp f` admits a self-adjoint continuous-functional-calculus
square root. Consequently, `TauCeti.HilbertCat.FinHilbertCat ℂ` inherits `CStarCategory`
automatically via `TauCeti.fullSubcategoryCStar`.

The abstract endomorphism C\*-algebra `End X` of `X : HilbertCat ℂ` is canonically star-algebra
equivalent (`TauCeti.HilbertCat.endStarAlgEquiv`) — hence isometric and order-isomorphic — to
Mathlib's operator C\*-algebra `X →L[ℂ] X`.
-/

public section

noncomputable section

open CategoryTheory

universe v

namespace TauCeti.HilbertCat

/-- Complex Hilbert spaces and bounded linear operators form a C\*-category. -/
instance instCStarCategory : CStarCategory (HilbertCat.{0, v} ℂ) where
  norm_smul_le c f := norm_smul_le c (f : _ →L[ℂ] _)
  norm_comp_le f g := HilbertCat.norm_comp_le f g
  norm_sq_le_comp_dagger f := (HilbertCat.norm_self_comp_dagger f).symm.le
  exists_comp_dagger_eq {X Y} f := by
    let Tf : X →L[ℂ] Y := f
    have hpos : (0 : X →L[ℂ] X) ≤ (ContinuousLinearMap.adjoint Tf).comp Tf := by
      rw [ContinuousLinearMap.le_def]
      simpa using! ContinuousLinearMap.isPositive_one.adjoint_conj Tf
    let s : X →L[ℂ] X := CFC.sqrt ((ContinuousLinearMap.adjoint Tf).comp Tf)
    refine ⟨s, ?_⟩
    have hsa : ContinuousLinearMap.adjoint s = s :=
      (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
    have hsq : s.comp s = (ContinuousLinearMap.adjoint Tf).comp Tf :=
      CFC.sqrt_mul_sqrt_self _ hpos
    simpa only [comp_eq_comp, dagger_eq_adjoint, hsa] using hsq.symm

/-- The endomorphism C\*-algebra `End X` of `X : HilbertCat ℂ` is canonically star-algebra
equivalent to the operator C\*-algebra `X →L[ℂ] X`, because both multiply in operator order. -/
def endStarAlgEquiv (X : HilbertCat.{0, v} ℂ) : End X ≃⋆ₐ[ℂ] (X →L[ℂ] X) where
  toFun f := f.asHom
  invFun f := End.of f
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- Applying `HilbertCat.endStarAlgEquiv` extracts the underlying continuous linear operator. -/
@[simp] theorem endStarAlgEquiv_apply (X : HilbertCat.{0, v} ℂ) (f : End X) :
    endStarAlgEquiv X f = ConcreteCategory.hom f.asHom := (rfl)

/-- Applying `(HilbertCat.endStarAlgEquiv X).symm` wraps an operator `X →L[ℂ] X` in `End X`. -/
@[simp] theorem endStarAlgEquiv_symm_apply (X : HilbertCat.{0, v} ℂ) (f : X →L[ℂ] X) :
    (endStarAlgEquiv X).symm f = End.of f := (rfl)

/-- The spectral order on `End X` agrees with Mathlib's Loewner order on `X →L[ℂ] X`. -/
@[simp] theorem end_le_iff {X : HilbertCat.{0, v} ℂ} (f g : End X) :
    f ≤ g ↔ ConcreteCategory.hom f.asHom ≤ ConcreteCategory.hom g.asHom :=
  (NonUnitalStarAlgHom.map_le_map_iff (endStarAlgEquiv X) (endStarAlgEquiv X).injective).symm

/-- `End.of f` is nonnegative in `End X` precisely when `f` is positive in the Loewner order on
`X →L[ℂ] X`. -/
theorem end_of_nonneg_iff {X : HilbertCat.{0, v} ℂ} (f : X →L[ℂ] X) :
    0 ≤ End.of (X := X) f ↔ 0 ≤ f :=
  end_le_iff 0 (End.of f)

end TauCeti.HilbertCat
