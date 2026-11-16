/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import TauCeti.Algebra.Homology.Contraction.Basic
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Direct-sum decompositions and contractions of mapping cones

The mapping cone of the identity morphism `𝟙 K` of a cochain complex `K` is contractible: the
degree `-1` cochain `(mappingCone.snd (𝟙 K)).comp (mappingCone.inl (𝟙 K))` satisfies both the
contracting identity `δ (-1) 0 h = 1` and the side condition `h ∘ h = 0`
(`CochainComplex.mappingCone.idContractingHomotopy`). Consequently, cancelling a direct summand
`mappingCone (𝟙 K)` from a binary biproduct yields a special contraction
(`TauCeti.SpecialContraction.biprodMappingConeIdLeft`,
`TauCeti.SpecialContraction.biprodMappingConeIdRight`) without invoking normalization.

More generally, when a cochain map `φ : K ⟶ K ⊞ M` admits `biprod.fst` as a left inverse
(`φ ≫ biprod.fst = 𝟙 K`), a shear automorphism of `K ⊞ M` transforms `φ` into `biprod.inl`,
identifying `mappingCone φ` with `mappingCone (𝟙 K) ⊞ M`
(`CochainComplex.mappingCone.isoOfCompFstEqId`). Dually, when `φ : L ⊞ M ⟶ L` admits `biprod.inl`
as a right inverse (`biprod.inl ≫ φ = 𝟙 L`), a shear automorphism of `L ⊞ M` transforms `φ` into
`biprod.fst`, identifying `mappingCone φ` with `mappingCone (𝟙 L) ⊞ M⟦1⟧`
(`CochainComplex.mappingCone.isoOfInlCompEqId`). Combining these decompositions with the
contractibility of `mappingCone (𝟙 _)` produces explicit special contractions of `mappingCone φ`
onto `M` or `M⟦1⟧`.

This is the Gaussian-elimination cancellation mechanism for mapping cones of cochain complexes with
an identity block, used in particular to cancel acyclic summands in Khovanov homology.

## Main definitions

* `CochainComplex.mappingCone.idContractingHomotopy`: the canonical square-zero contracting
  homotopy of `mappingCone (𝟙 K)`.
* `CochainComplex.mappingCone.biprodInlIso`, `CochainComplex.mappingCone.biprodFstIso`: the
  direct-sum decompositions of `mappingCone biprod.inl` and `mappingCone biprod.fst`.
* `CochainComplex.mappingCone.isoOfCompFstEqId`, `CochainComplex.mappingCone.isoOfCompSndEqId`,
  `CochainComplex.mappingCone.isoOfInlCompEqId`, `CochainComplex.mappingCone.isoOfInrCompEqId`:
  direct-sum decompositions for mapping cones of split monomorphisms and split epimorphisms into
  and out of binary biproducts.
* `TauCeti.SpecialContraction.biprodMappingConeIdLeft`,
  `TauCeti.SpecialContraction.biprodMappingConeIdRight`: special contractions cancelling a
  `mappingCone (𝟙 _)` summand from a biproduct.
* `TauCeti.SpecialContraction.ofMappingConeCompFstEqId`,
  `TauCeti.SpecialContraction.ofMappingConeCompSndEqId`,
  `TauCeti.SpecialContraction.ofMappingConeInlCompEqId`,
  `TauCeti.SpecialContraction.ofMappingConeInrCompEqId`: special contractions for mapping cones of
  split monomorphisms and split epimorphisms.

## References

* D. Bar-Natan, *Fast Khovanov homology computations*, J. Knot Theory Ramifications 16 (2007),
  Lemma 4.2 (Gaussian elimination for complexes).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Preadditive CochainComplex CochainComplex.HomComplex
  ZeroObject

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C]

section IdHomotopy

/-- The canonical degree `-1` contracting homotopy on `mappingCone (𝟙 K)`, sending the second
coordinate `K^p` into the first coordinate `K^p` in degree `p - 1`. It satisfies `δ h = 1` and
`h ∘ h = 0` on the nose. -/
def idContractingHomotopy (K : CochainComplex C ℤ)
    [HomologicalComplex.HasHomotopyCofiber (𝟙 K)] :
    Cochain (mappingCone (𝟙 K)) (mappingCone (𝟙 K)) (-1) :=
  (snd (𝟙 K)).comp (inl (𝟙 K)) (zero_add (-1))

/-- The differential of `idContractingHomotopy K` is the identity of `mappingCone (𝟙 K)`. -/
@[simp]
theorem δ_idContractingHomotopy (K : CochainComplex C ℤ)
    [HomologicalComplex.HasHomotopyCofiber (𝟙 K)] :
    δ (-1) 0 (idContractingHomotopy K) = Cochain.ofHom (𝟙 (mappingCone (𝟙 K))) := by
  rw [idContractingHomotopy,
    δ_comp (snd (𝟙 K)) (inl (𝟙 K)) (zero_add (-1)) 1 0 0 (by lia) (by lia) (by lia),
    δ_inl, δ_snd]
  simp only [Category.id_comp, Cochain.comp_id, Int.negOnePow_neg,
    Int.negOnePow_one, Units.neg_smul, one_smul, Cochain.neg_comp, neg_neg]
  rw [add_comm, mappingCone.id]

/-- The canonical contracting homotopy on `mappingCone (𝟙 K)` squares to zero. -/
@[simp]
theorem idContractingHomotopy_comp_self (K : CochainComplex C ℤ)
    [HomologicalComplex.HasHomotopyCofiber (𝟙 K)] :
    (idContractingHomotopy K).comp (idContractingHomotopy K)
      (by lia : (-1 : ℤ) + (-1) = -2) = 0 := by
  rw [idContractingHomotopy,
    Cochain.comp_assoc (snd (𝟙 K)) (inl (𝟙 K)) ((snd (𝟙 K)).comp (inl (𝟙 K)) (zero_add (-1)))
      (zero_add (-1)) (by lia : (-1 : ℤ) + (-1) = -2) (by lia),
    ← Cochain.comp_assoc (inl (𝟙 K)) (snd (𝟙 K)) (inl (𝟙 K))
      (add_zero (-1)) (zero_add (-1)) (by lia),
    inl_snd, Cochain.zero_comp, Cochain.comp_zero]

end IdHomotopy

section Biproducts

variable [HasBinaryBiproducts C]

/-- The mapping cone of the first biproduct inclusion `K ⟶ K ⊞ M` decomposes as
`mappingCone (𝟙 K) ⊞ M`. -/
def biprodInlIso (K M : CochainComplex C ℤ) :
    mappingCone (biprod.inl : K ⟶ K ⊞ M) ≅ mappingCone (𝟙 K) ⊞ M where
  hom := biprod.lift
    (map (biprod.inl : K ⟶ K ⊞ M) (𝟙 K) (𝟙 K) biprod.fst (by simp))
    (desc (biprod.inl : K ⟶ K ⊞ M) 0 biprod.snd (by simp))
  inv := biprod.desc
    (map (𝟙 K) (biprod.inl : K ⟶ K ⊞ M) (𝟙 K) biprod.inl (by simp))
    (biprod.inr ≫ inr (biprod.inl : K ⟶ K ⊞ M))
  hom_inv_id := by
    rw [biprod.lift_desc]
    ext p : 1
    refine ext_from (biprod.inl : K ⟶ K ⊞ M) (p + 1) p (by lia) ?_ ?_
    · rw [HomologicalComplex.add_f_apply, Preadditive.comp_add, HomologicalComplex.comp_f,
        HomologicalComplex.comp_f, inl_v_map_f_assoc, inl_v_map_f, inl_v_desc_f_assoc,
        Cochain.zero_v, zero_comp, add_zero, HomologicalComplex.id_f, HomologicalComplex.id_f,
        Category.id_comp, Category.id_comp, Category.comp_id]
    · rw [HomologicalComplex.add_f_apply, Preadditive.comp_add, HomologicalComplex.comp_f,
        HomologicalComplex.comp_f, inr_f_map_f_assoc, inr_f_map_f, inr_f_desc_f_assoc,
        HomologicalComplex.comp_f, ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
        HomologicalComplex.biprod_total_f, HomologicalComplex.id_f, Category.id_comp,
        Category.comp_id]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · refine biprod.hom_ext _ _ ?_ ?_
      · simp only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_fst, Category.comp_id,
          biprod.inl_fst]
        ext p : 1
        refine ext_from (𝟙 K) (p + 1) p (by lia) ?_ ?_
        · simp [HomologicalComplex.comp_f, inl_v_map_f_assoc]
        · simp [HomologicalComplex.comp_f, inr_f_map_f_assoc]
      · simp only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_snd, Category.comp_id,
          biprod.inl_snd]
        ext p : 1
        refine ext_from (𝟙 K) (p + 1) p (by lia) ?_ ?_
        · simp [HomologicalComplex.comp_f, inl_v_map_f_assoc]
        · simp [HomologicalComplex.comp_f, inr_f_map_f_assoc]
    · refine biprod.hom_ext _ _ ?_ ?_
      · simp only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst, Category.comp_id,
          biprod.inr_fst]
        ext p : 1
        simp [HomologicalComplex.comp_f, inr_f_map_f]
      · simp only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_snd, inr_desc,
          Category.comp_id, biprod.inr_snd]

@[reassoc (attr := simp)]
theorem biprodInlIso_hom_fst (K M : CochainComplex C ℤ) :
    (biprodInlIso K M).hom ≫ biprod.fst =
      map (biprod.inl : K ⟶ K ⊞ M) (𝟙 K) (𝟙 K) biprod.fst (by simp) := by
  simp [biprodInlIso]

@[reassoc (attr := simp)]
theorem biprodInlIso_hom_snd (K M : CochainComplex C ℤ) :
    (biprodInlIso K M).hom ≫ biprod.snd =
      desc (biprod.inl : K ⟶ K ⊞ M) 0 biprod.snd (by simp) := by
  simp [biprodInlIso]

@[reassoc (attr := simp)]
theorem inl_biprodInlIso_inv (K M : CochainComplex C ℤ) :
    biprod.inl ≫ (biprodInlIso K M).inv =
      map (𝟙 K) (biprod.inl : K ⟶ K ⊞ M) (𝟙 K) biprod.inl (by simp) := by
  simp [biprodInlIso]

@[reassoc (attr := simp)]
theorem inr_biprodInlIso_inv (K M : CochainComplex C ℤ) :
    biprod.inr ≫ (biprodInlIso K M).inv =
      biprod.inr ≫ inr (biprod.inl : K ⟶ K ⊞ M) := by
  simp [biprodInlIso]

/-- The inclusion of `M⟦1⟧` into `mappingCone (biprod.fst : L ⊞ M ⟶ L)` used in
`CochainComplex.mappingCone.biprodFstIso`. -/
private def biprodFstShiftIncl (L M : CochainComplex C ℤ) :
    M⟦(1 : ℤ)⟧ ⟶ mappingCone (biprod.fst : L ⊞ M ⟶ L) :=
  lift (biprod.fst : L ⊞ M ⟶ L)
    ((Cocycle.ofHom (biprod.inr : M ⟶ L ⊞ M)).leftShift 1 1 (zero_add 1)) 0
    (by
      rw [δ_zero, zero_add]
      ext p q hpq
      simp [Cochain.comp_zero_cochain_v,
        Cochain.leftShift_v _ 1 1 (zero_add 1) p q hpq q (by lia), Cochain.ofHom_v])

@[reassoc (attr := simp)]
private theorem biprodFstShiftIncl_f_fst_v (L M : CochainComplex C ℤ) (p q : ℤ)
    (hpq : p + 1 = q) :
    (biprodFstShiftIncl L M).f p ≫ (fst (biprod.fst : L ⊞ M ⟶ L)).1.v p q hpq =
      -((M.shiftFunctorObjXIso 1 p q hpq.symm).hom ≫ (biprod.inr : M ⟶ L ⊞ M).f q) := by
  rw [biprodFstShiftIncl, lift_f_fst_v]
  simp [Cochain.leftShift_v _ 1 1 (zero_add 1) p q hpq q (by lia)]

@[reassoc (attr := simp)]
private theorem biprodFstShiftIncl_f_snd_v (L M : CochainComplex C ℤ) (p : ℤ) :
    (biprodFstShiftIncl L M).f p ≫ (snd (biprod.fst : L ⊞ M ⟶ L)).v p p (add_zero p) = 0 := by
  rw [biprodFstShiftIncl, lift_f_snd_v, Cochain.zero_v]

private theorem triangle_mor₃_f_eq_neg_fst_v {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ) :
    (triangle φ).mor₃.f p = -((fst φ).1.v p (p + 1) rfl) := by
  dsimp [triangle]
  simp [Cochain.rightShift_v _ 1 0 (zero_add 1) p p (add_zero p) (p + 1) rfl,
    CochainComplex.shiftFunctorObjXIso]

/-- The mapping cone of the first biproduct projection `L ⊞ M ⟶ L` decomposes as
`mappingCone (𝟙 L) ⊞ M⟦1⟧`. -/
def biprodFstIso (L M : CochainComplex C ℤ) :
    mappingCone (biprod.fst : L ⊞ M ⟶ L) ≅ mappingCone (𝟙 L) ⊞ M⟦(1 : ℤ)⟧ where
  hom := biprod.lift
    (map (biprod.fst : L ⊞ M ⟶ L) (𝟙 L) biprod.fst (𝟙 L) (by simp))
    ((triangle (biprod.fst : L ⊞ M ⟶ L)).mor₃ ≫ (biprod.snd : L ⊞ M ⟶ M)⟦(1 : ℤ)⟧')
  inv := biprod.desc
    (map (𝟙 L) (biprod.fst : L ⊞ M ⟶ L) biprod.inl (𝟙 L) (by simp))
    (biprodFstShiftIncl L M)
  hom_inv_id := by
    rw [biprod.lift_desc]
    ext p : 1
    refine ext_to (biprod.fst : L ⊞ M ⟶ L) p (p + 1) rfl ?_ ?_
    · simp [HomologicalComplex.add_f_apply, Preadditive.add_comp, HomologicalComplex.comp_f,
        map_f_fst_v, map_f_fst_v_assoc, biprodFstShiftIncl_f_fst_v, triangle_mor₃_f_eq_neg_fst_v,
        CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso,
        ← Preadditive.comp_add]
    · rw [HomologicalComplex.add_f_apply, Preadditive.add_comp, HomologicalComplex.comp_f,
        HomologicalComplex.comp_f, Category.assoc, map_f_snd_v, map_f_snd_v_assoc,
        Category.assoc, biprodFstShiftIncl_f_snd_v, comp_zero, add_zero,
        HomologicalComplex.id_f, HomologicalComplex.id_f, Category.comp_id, Category.comp_id,
        Category.id_comp]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · refine biprod.hom_ext _ _ ?_ ?_
      · simp only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_fst, Category.comp_id,
          biprod.inl_fst]
        ext p : 1
        refine ext_to (𝟙 L) p (p + 1) rfl ?_ ?_
        · simp [HomologicalComplex.comp_f, map_f_fst_v]
        · simp [HomologicalComplex.comp_f, map_f_snd_v]
      · simp only [biprod.inl_desc_assoc, Category.assoc, biprod.lift_snd, Category.comp_id,
          biprod.inl_snd]
        ext p : 1
        simp [HomologicalComplex.comp_f, triangle_mor₃_f_eq_neg_fst_v, map_f_fst_v_assoc,
          CochainComplex.shiftFunctor_map_f']
    · refine biprod.hom_ext _ _ ?_ ?_
      · simp only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_fst, Category.comp_id,
          biprod.inr_fst]
        ext p : 1
        refine ext_to (𝟙 L) p (p + 1) rfl ?_ ?_
        · simp [HomologicalComplex.comp_f, map_f_fst_v, biprodFstShiftIncl_f_fst_v_assoc]
        · simp [HomologicalComplex.comp_f, map_f_snd_v]
      · simp only [biprod.inr_desc_assoc, Category.assoc, biprod.lift_snd, Category.comp_id,
          biprod.inr_snd]
        ext p : 1
        simp [HomologicalComplex.comp_f, triangle_mor₃_f_eq_neg_fst_v,
          biprodFstShiftIncl_f_fst_v_assoc, CochainComplex.shiftFunctor_map_f',
          CochainComplex.shiftFunctorObjXIso]

@[reassoc (attr := simp)]
theorem biprodFstIso_hom_fst (L M : CochainComplex C ℤ) :
    (biprodFstIso L M).hom ≫ biprod.fst =
      map (biprod.fst : L ⊞ M ⟶ L) (𝟙 L) biprod.fst (𝟙 L) (by simp) := by
  simp [biprodFstIso]

@[reassoc (attr := simp)]
theorem biprodFstIso_hom_snd (L M : CochainComplex C ℤ) :
    (biprodFstIso L M).hom ≫ biprod.snd =
      (triangle (biprod.fst : L ⊞ M ⟶ L)).mor₃ ≫ (biprod.snd : L ⊞ M ⟶ M)⟦(1 : ℤ)⟧' := by
  simp [biprodFstIso]

@[reassoc (attr := simp)]
theorem inl_biprodFstIso_inv (L M : CochainComplex C ℤ) :
    biprod.inl ≫ (biprodFstIso L M).inv =
      map (𝟙 L) (biprod.fst : L ⊞ M ⟶ L) biprod.inl (𝟙 L) (by simp) := by
  simp [biprodFstIso]

/-- The shear automorphism of `K ⊞ M` eliminating the off-diagonal component `g : K ⟶ M` of a
split monomorphism `biprod.lift (𝟙 K) g`. -/
private def shearInl {K M : CochainComplex C ℤ} (g : K ⟶ M) : K ⊞ M ≅ K ⊞ M where
  hom := biprod.desc (biprod.inl - g ≫ biprod.inr) biprod.inr
  inv := biprod.desc (biprod.inl + g ≫ biprod.inr) biprod.inr
  hom_inv_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [Preadditive.sub_comp]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [Preadditive.add_comp]

/-- The shear automorphism of `L ⊞ M` eliminating the off-diagonal component `g : M ⟶ L` of a
split epimorphism `biprod.desc (𝟙 L) g`. -/
private def shearFst {L M : CochainComplex C ℤ} (g : M ⟶ L) : L ⊞ M ≅ L ⊞ M where
  hom := biprod.desc biprod.inl (g ≫ biprod.inl + biprod.inr)
  inv := biprod.desc biprod.inl (biprod.inr - g ≫ biprod.inl)
  hom_inv_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [Preadditive.add_comp]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [Preadditive.sub_comp]

/-- **Split-monomorphism cancellation (left summand).** If `φ : K ⟶ K ⊞ M` satisfies
`φ ≫ biprod.fst = 𝟙 K`, then `mappingCone φ` decomposes as `mappingCone (𝟙 K) ⊞ M`. -/
def isoOfCompFstEqId {K M : CochainComplex C ℤ} {φ : K ⟶ K ⊞ M} (h : φ ≫ biprod.fst = 𝟙 K) :
    mappingCone φ ≅ mappingCone (𝟙 K) ⊞ M :=
  mapIso (Iso.refl K) (shearInl (φ ≫ biprod.snd))
      (by
        have hφ : φ = biprod.lift (𝟙 K) (φ ≫ biprod.snd) := by
          refine biprod.hom_ext _ _ ?_ ?_ <;> simp [h]
        rw [Iso.refl_hom, Category.id_comp, hφ, shearInl]
        simp [biprod.lift_desc]) ≪≫
    biprodInlIso K M

/-- **Split-monomorphism cancellation (right summand).** If `φ : K ⟶ M ⊞ K` satisfies
`φ ≫ biprod.snd = 𝟙 K`, then `mappingCone φ` decomposes as `mappingCone (𝟙 K) ⊞ M`. -/
def isoOfCompSndEqId {K M : CochainComplex C ℤ} {φ : K ⟶ M ⊞ K} (h : φ ≫ biprod.snd = 𝟙 K) :
    mappingCone φ ≅ mappingCone (𝟙 K) ⊞ M :=
  letI : HasBinaryBiproducts (CochainComplex C ℤ) := ⟨fun _ _ ↦ inferInstance⟩
  mapIso (Iso.refl K) (biprod.braiding M K) (by simp) ≪≫
    isoOfCompFstEqId (φ := φ ≫ (biprod.braiding M K).hom) (by simpa [Category.assoc] using h)

/-- **Split-epimorphism cancellation (left summand).** If `φ : L ⊞ M ⟶ L` satisfies
`biprod.inl ≫ φ = 𝟙 L`, then `mappingCone φ` decomposes as `mappingCone (𝟙 L) ⊞ M⟦1⟧`. -/
def isoOfInlCompEqId {L M : CochainComplex C ℤ} {φ : L ⊞ M ⟶ L} (h : biprod.inl ≫ φ = 𝟙 L) :
    mappingCone φ ≅ mappingCone (𝟙 L) ⊞ M⟦(1 : ℤ)⟧ :=
  mapIso (shearFst (biprod.inr ≫ φ)) (Iso.refl L)
      (by
        rw [Iso.refl_hom, Category.comp_id, shearFst]
        refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [h, Preadditive.add_comp]) ≪≫
    biprodFstIso L M

/-- **Split-epimorphism cancellation (right summand).** If `φ : M ⊞ L ⟶ L` satisfies
`biprod.inr ≫ φ = 𝟙 L`, then `mappingCone φ` decomposes as `mappingCone (𝟙 L) ⊞ M⟦1⟧`. -/
def isoOfInrCompEqId {L M : CochainComplex C ℤ} {φ : M ⊞ L ⟶ L} (h : biprod.inr ≫ φ = 𝟙 L) :
    mappingCone φ ≅ mappingCone (𝟙 L) ⊞ M⟦(1 : ℤ)⟧ :=
  letI : HasBinaryBiproducts (CochainComplex C ℤ) := ⟨fun _ _ ↦ inferInstance⟩
  mapIso (biprod.braiding' M L) (Iso.refl L)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]) ≪≫
    isoOfInlCompEqId (φ := (biprod.braiding' M L).inv ≫ φ) (by simpa [Category.assoc] using h)

end Biproducts

end CochainComplex.mappingCone

namespace TauCeti.SpecialContraction

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The mapping cone of the identity morphism of `K` admits a canonical special contraction onto
the zero complex. -/
def mappingConeId [HasZeroObject C] (K : CochainComplex C ℤ)
    [HomologicalComplex.HasHomotopyCofiber (𝟙 K)] :
    SpecialContraction (mappingCone (𝟙 K)) 0 where
  incl := 0
  proj := 0
  homotopy := mappingCone.idContractingHomotopy K
  incl_comp_proj := (Limits.isZero_zero _).eq_of_src _ _
  δ_homotopy := by simp
  incl_comp_homotopy := by simp
  homotopy_comp_proj := by simp
  homotopy_comp_homotopy := by simp

@[simp]
theorem mappingConeId_incl [HasZeroObject C] (K : CochainComplex C ℤ)
    [HomologicalComplex.HasHomotopyCofiber (𝟙 K)] :
    (mappingConeId K).incl = 0 := (rfl)

@[simp]
theorem mappingConeId_proj [HasZeroObject C] (K : CochainComplex C ℤ)
    [HomologicalComplex.HasHomotopyCofiber (𝟙 K)] :
    (mappingConeId K).proj = 0 := (rfl)

@[simp]
theorem mappingConeId_homotopy [HasZeroObject C] (K : CochainComplex C ℤ)
    [HomologicalComplex.HasHomotopyCofiber (𝟙 K)] :
    (mappingConeId K).homotopy = mappingCone.idContractingHomotopy K := (rfl)

variable [HasBinaryBiproducts C]

/-- Cancelling a `mappingCone (𝟙 K)` summand on the left of a binary biproduct yields a special
contraction onto `M`. -/
def biprodMappingConeIdLeft (K M : CochainComplex C ℤ) :
    SpecialContraction (mappingCone (𝟙 K) ⊞ M) M where
  incl := biprod.inr
  proj := biprod.snd
  homotopy :=
    (Cochain.ofHom biprod.fst).comp
      ((mappingCone.idContractingHomotopy K).comp (Cochain.ofHom biprod.inl)
        (by lia : (-1 : ℤ) + 0 = -1))
      (by lia : (0 : ℤ) + (-1) = -1)
  incl_comp_proj := biprod.inr_snd
  δ_homotopy := by
    rw [δ_zero_cochain_comp _ _ 0 (by lia), δ_ofHom, Cochain.zero_comp, smul_zero, add_zero,
      δ_comp_zero_cochain _ _ 0 (by lia), δ_ofHom, Cochain.comp_zero, zero_add,
      mappingCone.δ_idContractingHomotopy, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
    congr 1
    rw [Category.id_comp, eq_sub_iff_add_eq]
    exact biprod.total
  incl_comp_homotopy := by
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, biprod.inr_fst,
      Cochain.ofHom_zero, Cochain.zero_comp]
  homotopy_comp_proj := by
    rw [Cochain.comp_assoc_of_first_is_zero_cochain,
      Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, biprod.inl_snd,
      Cochain.ofHom_zero, Cochain.comp_zero, Cochain.comp_zero]
  homotopy_comp_homotopy := by
    rw [Cochain.comp_assoc_of_first_is_zero_cochain,
      ← Cochain.comp_assoc
        ((mappingCone.idContractingHomotopy K).comp (Cochain.ofHom biprod.inl) (by lia))
        (Cochain.ofHom biprod.fst)
        ((mappingCone.idContractingHomotopy K).comp (Cochain.ofHom biprod.inl) (by lia))
        (by lia : (-1 : ℤ) + 0 = -1) (by lia : (0 : ℤ) + (-1) = -1) (by lia),
      Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, biprod.inl_fst,
      Cochain.comp_id,
      ← Cochain.comp_assoc (mappingCone.idContractingHomotopy K)
        (mappingCone.idContractingHomotopy K) (Cochain.ofHom biprod.inl)
        (by lia : (-1 : ℤ) + (-1) = -2) (by lia : (-1 : ℤ) + 0 = -1) (by lia),
      mappingCone.idContractingHomotopy_comp_self, Cochain.zero_comp, Cochain.comp_zero]

@[simp]
theorem biprodMappingConeIdLeft_incl (K M : CochainComplex C ℤ) :
    (biprodMappingConeIdLeft K M).incl = biprod.inr := (rfl)

@[simp]
theorem biprodMappingConeIdLeft_proj (K M : CochainComplex C ℤ) :
    (biprodMappingConeIdLeft K M).proj = biprod.snd := (rfl)

/-- Cancelling a `mappingCone (𝟙 L)` summand on the right of a binary biproduct yields a special
contraction onto `M`. -/
def biprodMappingConeIdRight (M L : CochainComplex C ℤ) :
    SpecialContraction (M ⊞ mappingCone (𝟙 L)) M :=
  letI : HasBinaryBiproducts (CochainComplex C ℤ) := ⟨fun _ _ ↦ inferInstance⟩
  (biprodMappingConeIdLeft L M).ofIso (biprod.braiding' M (mappingCone (𝟙 L))) (Iso.refl M)

@[simp]
theorem biprodMappingConeIdRight_incl (M L : CochainComplex C ℤ) :
    (biprodMappingConeIdRight M L).incl = biprod.inl := by
  simp [biprodMappingConeIdRight]

@[simp]
theorem biprodMappingConeIdRight_proj (M L : CochainComplex C ℤ) :
    (biprodMappingConeIdRight M L).proj = biprod.fst := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [biprodMappingConeIdRight]

/-- Special contraction of `mappingCone φ` onto `M` when `φ : K ⟶ K ⊞ M` satisfies
`φ ≫ biprod.fst = 𝟙 K`. -/
def ofMappingConeCompFstEqId {K M : CochainComplex C ℤ} {φ : K ⟶ K ⊞ M}
    (h : φ ≫ biprod.fst = 𝟙 K) : SpecialContraction (mappingCone φ) M :=
  (biprodMappingConeIdLeft K M).ofIso (mappingCone.isoOfCompFstEqId h) (Iso.refl M)

/-- Special contraction of `mappingCone φ` onto `M` when `φ : K ⟶ M ⊞ K` satisfies
`φ ≫ biprod.snd = 𝟙 K`. -/
def ofMappingConeCompSndEqId {K M : CochainComplex C ℤ} {φ : K ⟶ M ⊞ K}
    (h : φ ≫ biprod.snd = 𝟙 K) : SpecialContraction (mappingCone φ) M :=
  (biprodMappingConeIdLeft K M).ofIso (mappingCone.isoOfCompSndEqId h) (Iso.refl M)

/-- Special contraction of `mappingCone φ` onto `M⟦1⟧` when `φ : L ⊞ M ⟶ L` satisfies
`biprod.inl ≫ φ = 𝟙 L`. -/
def ofMappingConeInlCompEqId {L M : CochainComplex C ℤ} {φ : L ⊞ M ⟶ L}
    (h : biprod.inl ≫ φ = 𝟙 L) : SpecialContraction (mappingCone φ) (M⟦(1 : ℤ)⟧) :=
  (biprodMappingConeIdLeft L (M⟦(1 : ℤ)⟧)).ofIso (mappingCone.isoOfInlCompEqId h) (Iso.refl _)

/-- Special contraction of `mappingCone φ` onto `M⟦1⟧` when `φ : M ⊞ L ⟶ L` satisfies
`biprod.inr ≫ φ = 𝟙 L`. -/
def ofMappingConeInrCompEqId {L M : CochainComplex C ℤ} {φ : M ⊞ L ⟶ L}
    (h : biprod.inr ≫ φ = 𝟙 L) : SpecialContraction (mappingCone φ) (M⟦(1 : ℤ)⟧) :=
  (biprodMappingConeIdLeft L (M⟦(1 : ℤ)⟧)).ofIso (mappingCone.isoOfInrCompEqId h) (Iso.refl _)

end TauCeti.SpecialContraction
