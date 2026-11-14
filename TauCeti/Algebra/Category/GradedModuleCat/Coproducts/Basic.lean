/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Products
public import TauCeti.CategoryTheory.Linear.Biproduct
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic

/-!
# Coproducts of internally graded modules

The existing degreewise direct sum is a coproduct in `GradedModuleCat`. Its injections
and universal map have internal degree zero, so the underlying direct-sum universal
property lifts from modules to graded modules. The forgetful functor to modules preserves
these coproducts.

The universal property follows `ModuleCat.coproductCoconeIsColimit` in
`Mathlib.Algebra.Category.ModuleCat.Products`. The grading argument is
`InternalGrading.toModule_mem_of_mem_directSumPiece`, as in `GradedModuleCat.freeLift`.

These coproducts provide the sums required for Mathlib's totalization of cochain
bifunctors, including balanced tensor composition of graded bimodule complexes.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v w

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}
  {J : Type w} (M : J → GradedModuleCat.{max w v} 𝒜)

/-- The cofan of the direct-sum injections, each of internal degree zero.
The abbreviation retains the concrete point for computations with direct-sum elements. -/
abbrev coproductCofan : Cofan M where
  pt := directSumObj M
  ι := Discrete.natTrans fun j ↦ by
    classical
    exact ofHom (N := directSumObj M) (DirectSum.lof A J (fun j ↦ M j) j.as)
      (LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
        rw [add_zero, InternalGrading.directSum_piece]
        simpa only [DirectSum.lof_eq_of] using
          InternalGrading.lof_mem_directSumPiece (fun j ↦ (M j).grading) p j.as ⟨x, hx⟩)

/-- The underlying map of a coproduct injection is the direct-sum inclusion. -/
@[simp]
theorem hom_coproductCofan_inj [hJ : DecidableEq J] (j : J) :
    ((coproductCofan M).inj j).hom = DirectSum.lof A J (fun j ↦ M j) j := by
  cases Subsingleton.elim hJ (Classical.decEq J)
  rfl

/-- Membership in a degree piece of the coproduct is componentwise. -/
theorem mem_coproductCofan_pt_piece_iff {p : ℤ} {x : (coproductCofan M).pt} :
    x ∈ (coproductCofan M).pt.grading.piece p ↔
      ∀ j, x j ∈ (M j).grading.piece p := by
  simpa only [InternalGrading.directSum_piece] using
    InternalGrading.mem_directSumPiece_iff (fun j ↦ (M j).grading) p x

/-- Extend a cofan of graded maps along the direct-sum universal property. -/
def coproductDesc (s : Cofan M) : (coproductCofan M).pt ⟶ s.pt := by
  classical
  refine ofHom (DirectSum.toModule A J s.pt fun j ↦ (s.inj j).hom)
    (LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_)
  simpa only [add_zero] using InternalGrading.toModule_mem_of_mem_directSumPiece
    (fun j ↦ (M j).grading) s.pt.grading.piece (fun j ↦ (s.inj j).hom)
    (fun j x hx ↦ map_mem (s.inj j) hx) (by simpa only [InternalGrading.directSum_piece] using hx)

/-- The underlying universal map is the direct-sum universal linear map. -/
@[simp]
theorem hom_coproductDesc [hJ : DecidableEq J] (s : Cofan M) :
    (coproductDesc M s).hom = DirectSum.toModule A J s.pt fun j ↦ (s.inj j).hom := by
  cases Subsingleton.elim hJ (Classical.decEq J)
  rfl

/-- The universal map restricts to the prescribed map on each summand. -/
@[reassoc (attr := simp)]
theorem coproductCofan_inj_desc (s : Cofan M) (j : J) :
    (coproductCofan M).inj j ≫ coproductDesc M s = s.inj j := by
  classical
  apply hom_ext
  apply LinearMap.ext
  intro x
  -- Compute the two underlying maps on a direct-sum generator.
  change DirectSum.toModule A J s.pt (fun j ↦ (s.inj j).hom)
    (DirectSum.lof A J (fun j ↦ M j) j x) = (s.inj j).hom x
  exact DirectSum.toModule_lof A (M := fun j ↦ M j) (φ := fun j ↦ (s.inj j).hom) j x

/-- The direct sum of internally graded modules is their categorical coproduct. -/
def coproductCofanIsColimit : IsColimit (coproductCofan M) := by
  classical
  refine Cofan.IsColimit.mk _ (coproductDesc M) (coproductCofan_inj_desc M) ?_
  intro s f hf
  apply hom_ext
  apply DirectSum.linearMap_ext
  intro j
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (congrArg Hom.hom (hf j)) x
  -- Express the cofan equation and universal map on the same direct-sum generator.
  change f.hom (DirectSum.lof A J (fun j ↦ M j) j x) = (s.inj j).hom x at h
  change f.hom (DirectSum.lof A J (fun j ↦ M j) j x) =
    DirectSum.toModule A J s.pt (fun j ↦ (s.inj j).hom)
      (DirectSum.lof A J (fun j ↦ M j) j x)
  rw [DirectSum.toModule_lof]
  exact h

instance : HasCoproduct M :=
  HasColimit.mk ⟨_, coproductCofanIsColimit M⟩

instance : HasCoproducts.{w} (GradedModuleCat.{max w v} 𝒜) :=
  fun _ ↦ ⟨fun F ↦ hasColimit_of_iso (Discrete.natIsoFunctor (F := F))⟩

instance : PreservesColimit (Discrete.functor M) toModuleCat := by
  classical
  exact preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit M)
    ((Cofan.isColimitMapCoconeEquiv _ _ _).symm
      (ModuleCat.coproductCoconeIsColimit fun j ↦ toModuleCat.obj (M j)))

/-- A degreewise direct sum of projective graded modules is projective, with no finiteness
assumption on the index type. -/
instance projective_directSumObj [∀ j, Projective (M j)] : Projective (directSumObj M) :=
  Projective.of_isColimit_cofan (coproductCofanIsColimit M)

/-- When a family of graded modules admits a categorical biproduct, its degreewise direct sum is
canonically isomorphic to that biproduct. -/
def directSumObjIsoBiproduct [HasBiproduct M] : directSumObj M ≅ ⨁ M :=
  (coproductCofanIsColimit M).coconePointUniqueUpToIso (biproduct.isColimit M)

/-- Composing a direct-sum injection with `(directSumObjIsoBiproduct M).hom` gives `biproduct.ι`. -/
@[reassoc (attr := simp)]
theorem coproductCofan_inj_comp_directSumObjIsoBiproduct_hom [HasBiproduct M] (j : J) :
    (coproductCofan M).inj j ≫ (directSumObjIsoBiproduct M).hom = biproduct.ι M j :=
  (coproductCofanIsColimit M).comp_coconePointUniqueUpToIso_hom (biproduct.isColimit M) ⟨j⟩

/-- Composing `biproduct.ι` with `(directSumObjIsoBiproduct M).inv` gives the direct-sum
injection. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_comp_directSumObjIsoBiproduct_inv [HasBiproduct M] (j : J) :
    biproduct.ι M j ≫ (directSumObjIsoBiproduct M).inv = (coproductCofan M).inj j :=
  (coproductCofanIsColimit M).comp_coconePointUniqueUpToIso_inv (biproduct.isColimit M) ⟨j⟩

/-- Composing `(directSumObjIsoBiproduct M).hom` with `biproduct.π` gives the direct-sum
component projection. -/
@[reassoc (attr := simp)]
theorem directSumObjIsoBiproduct_hom_comp_biproduct_π {J : Type} (M : J → GradedModuleCat.{v} 𝒜)
    [HasBiproduct M] (j : J) :
    (directSumObjIsoBiproduct M).hom ≫ biproduct.π M j = (productFan M).proj j := by
  classical
  refine (coproductCofanIsColimit M).hom_ext fun ⟨i⟩ ↦ ?_
  change (coproductCofan M).inj i ≫ (directSumObjIsoBiproduct M).hom ≫ biproduct.π M j =
    (coproductCofan M).inj i ≫ (productFan M).proj j
  rcases eq_or_ne i j with rfl | hij
  · rw [coproductCofan_inj_comp_directSumObjIsoBiproduct_hom_assoc, biproduct.ι_π_self]
    refine hom_ext (LinearMap.ext fun x ↦ ?_)
    change x = ((productFan M).proj i).hom (((coproductCofan M).inj i).hom x)
    rw [hom_productFan_proj, hom_coproductCofan_inj, DirectSum.lof_eq_of, DirectSum.of_eq_same]
  · rw [coproductCofan_inj_comp_directSumObjIsoBiproduct_hom_assoc, biproduct.ι_π_ne _ hij]
    refine hom_ext (LinearMap.ext fun x ↦ ?_)
    change 0 = ((productFan M).proj j).hom (((coproductCofan M).inj i).hom x)
    rw [hom_productFan_proj, hom_coproductCofan_inj, DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne _ _ _ hij.symm]

/-- Composing `(directSumObjIsoBiproduct M).inv` with `(productFan M).proj` gives `biproduct.π`. -/
@[simp]
theorem directSumObjIsoBiproduct_inv_comp_productFan_proj {J : Type} (M : J → GradedModuleCat.{v} 𝒜)
    [HasBiproduct M] (j : J) :
    (directSumObjIsoBiproduct M).inv ≫ (productFan M).proj j = biproduct.π M j := by
  rw [← directSumObjIsoBiproduct_hom_comp_biproduct_π, Iso.inv_hom_id_assoc]

/-- Reassociated form of `directSumObjIsoBiproduct_inv_comp_productFan_proj`. -/
@[simp]
theorem directSumObjIsoBiproduct_inv_comp_productFan_proj_assoc {J : Type}
    (M : J → GradedModuleCat.{v} 𝒜) [HasBiproduct M] (j : J) {Z : GradedModuleCat.{v} 𝒜}
    (h : M j ⟶ Z) :
    (directSumObjIsoBiproduct M).inv ≫ (productFan M).proj j ≫ h = biproduct.π M j ≫ h := by
  rw [← directSumObjIsoBiproduct_hom_comp_biproduct_π_assoc, Iso.inv_hom_id_assoc]

/-- The dimension of graded maps from a finite degreewise direct sum is the sum of the
Hom dimensions of its summands. The Hom modules must be finite and free over `k`. -/
theorem finrank_hom_directSumObj [Fintype J] [StrongRankCondition k]
    (N : GradedModuleCat.{max w v} 𝒜)
    [∀ j, Module.Free k (M j ⟶ N)] [∀ j, Module.Finite k (M j ⟶ N)] :
    Module.finrank k (directSumObj M ⟶ N) = ∑ j, Module.finrank k (M j ⟶ N) := by
  let _ := HasBiproduct.of_hasCoproduct M
  rw [(Linear.homCongr k (directSumObjIsoBiproduct M) (Iso.refl N)).finrank_eq]
  exact finrank_hom_biproduct k M N

end TauCeti.GradedModuleCat
