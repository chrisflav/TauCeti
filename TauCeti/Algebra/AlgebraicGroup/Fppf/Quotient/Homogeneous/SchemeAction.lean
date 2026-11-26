/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Action
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Action

/-!
# Internal group actions on schemes representing fppf homogeneous quotients

Let `G = Spec H` be an affine group scheme over a commutative ring `R`, and let `I` be a Hopf
ideal of `H`. Whenever a scheme `X` over `Spec R` represents the fppf homogeneous quotient
`fppfHomogeneousQuotient H I` via an isomorphism `e : fppfHomogeneousQuotient H I ≅
CommAlgCat.pointsSheaf X`, the left coset action `fppfHomogeneousQuotientAction H I` transfers to
an internal group action `representedQuotientModObj H I e : ModObj G.X X`.

Equivariance descends along morphisms that are locally surjective on fppf sheaves of points
(`isModHom_of_isLocallySurjective_comp`), which implies that `representedQuotientProjection`,
`representedQuotientDesc`, `fppfHomogeneousQuotientSchemeMap`, and `representedQuotientIso` are all
equivariant, that `representedQuotientModObj` is uniquely determined by equivariance of
`representedQuotientProjection`, and that `representedQuotientTranslation` coincides with
`TauCeti.translation`.

## Main declarations

* `CommHopfAlgCat.isModHom_of_isLocallySurjective_comp`: equivariance descends along morphisms
  that are locally surjective on fppf point sheaves.
* `CommHopfAlgCat.representedQuotientModObj`: internal `G`-action on any scheme representing
  `fppfHomogeneousQuotient H I`.
* `CommHopfAlgCat.mul_representedQuotientProjection`,
  `CommHopfAlgCat.representedQuotientModObj_eq_of_comp`: `representedQuotientProjection` is
  equivariant and characterizes `representedQuotientModObj`.
* `CommHopfAlgCat.isModHom_representedQuotientDesc`,
  `CommHopfAlgCat.isModHom_fppfHomogeneousQuotientSchemeMap`,
  `CommHopfAlgCat.isModHom_representedQuotientIso`: equivariance of universal descents and
  canonical comparison morphisms.
* `CommHopfAlgCat.representedQuotientTranslation_eq_translation`: `representedQuotientTranslation`
  agrees with `TauCeti.translation`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§5.c, 7.e.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§14–15.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ModObj
  AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

section RepresentedQuotientAction

variable {R : Type u} [CommRing R]

/-- **Equivariance descends along locally surjective maps of fppf point sheaves.** If `p : G ⟶ X`
is locally surjective on fppf sheaves of points and satisfies `μ[G] ≫ p = G ◁ p ≫ γ[G,X]`,
then any morphism `f : X ⟶ Y` whose composite `p ≫ f` satisfies
`μ[G] ≫ (p ≫ f) = G ◁ (p ≫ f) ≫ γ[G,Y]` is `G`-equivariant. -/
theorem isModHom_of_isLocallySurjective_comp
    {G X Y : Over (Spec (CommRingCat.of R))} [MonObj G] [ModObj G X] [ModObj G Y]
    (p : G ⟶ X) [Sheaf.IsLocallySurjective ((CommAlgCat.pointsSheafFunctor R).map p)]
    (hp : μ[G] ≫ p = G ◁ p ≫ γ[G,X])
    (f : X ⟶ Y) (hf : μ[G] ≫ (p ≫ f) = G ◁ (p ≫ f) ≫ γ[G,Y]) :
    IsModHom G f := by
  refine ⟨(CommAlgCat.pointsSheafFunctor R).map_injective ?_⟩
  refine Sheaf.hom_ext (NatTrans.ext (funext fun ⟨⟨A⟩⟩ ↦ ConcreteCategory.hom_ext _ _ ?_))
  rintro ⟨z⟩
  let T := (algSpec (CommRingCat.of R)).obj (op A)
  let z' : T ⟶ G ⊗ X := z
  change ULift.up (z' ≫ _) = ULift.up (z' ≫ _)
  rw [ULift.up_inj]
  let g : T ⟶ G := z' ≫ fst G X
  let x : T ⟶ X := z' ≫ snd G X
  have hz : lift g x = z' := lift_comp_fst_snd z'
  have hg : z' ≫ γ[G,X] ≫ f = (g • x) ≫ f := by
    rw [← hz, ← Category.assoc, ← Hom.smul_def]
  have hr : z' ≫ G ◁ f ≫ γ[G,Y] = g • (x ≫ f) := by
    rw [← hz, lift_whiskerLeft_assoc, Hom.smul_def]
  rw [hg]
  erw [hr]
  refine congrArg ULift.down ?_
  have hS := Presheaf.imageSieve_mem (CommAlgCat.fppfTopology R)
    ((CommAlgCat.pointsSheafFunctor R).map p).hom
    (ULift.up x : ((CommAlgCat.pointsSheafFunctor R).obj X).obj.obj (op (op A)))
  refine (((isSheaf_iff_isSheaf_of_type _ _).mp
    (CommAlgCat.pointsSheaf Y).property).isSeparated _ hS).ext ?_
  rintro B χ ⟨⟨h⟩, hh⟩
  let h' : (algSpec (CommRingCat.of R)).obj B ⟶ G := h
  have hh' : h' ≫ p = (algSpec (CommRingCat.of R)).map χ ≫ x := congrArg ULift.down hh
  let g' : (algSpec (CommRingCat.of R)).obj B ⟶ G := (algSpec (CommRingCat.of R)).map χ ≫ g
  have hL : (algSpec (CommRingCat.of R)).map χ ≫ (g • x) ≫ f = (g' * h') ≫ (p ≫ f) := by
    calc (algSpec (CommRingCat.of R)).map χ ≫ (g • x) ≫ f
        = ((algSpec (CommRingCat.of R)).map χ ≫ (g • x)) ≫ f := (Category.assoc _ _ _).symm
      _ = (g' • ((algSpec (CommRingCat.of R)).map χ ≫ x)) ≫ f := by rw [ModObj.comp_smul]
      _ = (lift g' (h' ≫ p) ≫ γ[G,X]) ≫ f := by rw [← hh', Hom.smul_def]
      _ = (lift g' h' ≫ G ◁ p ≫ γ[G,X]) ≫ f := by rw [lift_whiskerLeft_assoc]
      _ = (lift g' h' ≫ μ[G] ≫ p) ≫ f := by rw [← hp]
      _ = (g' * h') ≫ (p ≫ f) := by
          rw [← Category.assoc (lift g' h'), ← Hom.mul_def, Category.assoc]
  have hR : (algSpec (CommRingCat.of R)).map χ ≫ (g • (x ≫ f)) =
      (g' * h') ≫ (p ≫ f) := by
    calc (algSpec (CommRingCat.of R)).map χ ≫ (g • (x ≫ f))
        = g' • ((algSpec (CommRingCat.of R)).map χ ≫ (x ≫ f)) := ModObj.comp_smul _ _ _
      _ = lift g' ((h' ≫ p) ≫ f) ≫ γ[G,Y] := by
          rw [← Category.assoc, ← hh', Hom.smul_def]
      _ = lift g' h' ≫ G ◁ (p ≫ f) ≫ γ[G,Y] := by
          rw [Category.assoc, lift_whiskerLeft_assoc]
      _ = (g' * h') ≫ (p ≫ f) := by
          rw [← hf, ← Category.assoc, ← Hom.mul_def]
  exact congrArg ULift.up (hL.trans hR.symm)

variable (H : _root_.CommHopfAlgCat.{u} R)

/-- Extending an `R`-valued point of `H` to `A` matches precomposing the corresponding `Spec R`
section of `Spec H` with `toUnit`. -/
theorem toUnit_comp_unitPoint_mapMulEquiv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{u} R) :
    toUnit ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) ≫
        (Over.homMk (𝟙 (Spec (CommRingCat.of R)))
          (by simp [Scheme.asOver, OverClass.asOver, Over.mk_hom,
            AlgebraicGeometry.specOverSpec_over]) :
          𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
            (Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R))) ≫ Spec.mapMulEquiv g =
      Spec.mapMulEquiv (HopfAlgebra.extendPoint H A g) := by
  have hL : toUnit ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) ≫
      (Over.homMk (𝟙 (Spec (CommRingCat.of R)))
        (by simp [Scheme.asOver, OverClass.asOver, Over.mk_hom,
          AlgebraicGeometry.specOverSpec_over]) :
        𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
          (Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R))) =
      (Spec.map (CommRingCat.ofHom (Algebra.ofId R A).toRingHom)).asOver
        (Spec (CommRingCat.of R)) := by
    apply Over.OverMorphism.ext
    change ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))).hom ≫ 𝟙 _ = _
    rw [Category.comp_id]
    rfl
  rw [← Category.assoc, hL, HopfAlgebra.extendPoint_apply,
    ← CommHopfAlgCat.mapMulEquiv_mapValue H (CommAlgCat.ofHom (Algebra.ofId R A)) g,
    HopfAlgebra.mapPoints_apply]
  rfl

variable (I : HopfIdeal R H) {X : Over (Spec (CommRingCat.of R))}
  (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)

private def representedQuotientActionSheafHom :
    CommAlgCat.pointsSheaf ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⊗ X) ⟶
      CommAlgCat.pointsSheaf X :=
  ⟨{
    app A := ↾fun p ↦ e.hom.hom.app A <|
      Spec.mapMulEquiv.symm
          (p.down ≫ fst ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X) •
        e.inv.hom.app A
          (ULift.up (p.down ≫ snd ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X))
    naturality {A B} χ := by
      ext ⟨p⟩
      let g : (Spec (CommRingCat.of A.unop.unop)).asOver (Spec (CommRingCat.of R)) ⟶
          (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) :=
        p ≫ fst ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X
      let x : (algSpec (CommRingCat.of R)).obj A.unop ⟶ X :=
        p ≫ snd ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X
      have hG : Spec.mapMulEquiv.symm
          (((algSpec (CommRingCat.of R)).map χ.unop ≫ g :
            (Spec (CommRingCat.of B.unop.unop)).asOver (Spec (CommRingCat.of R)) ⟶ _)) =
          HopfAlgebra.mapPoints (H := H) χ.unop.unop (Spec.mapMulEquiv.symm g) := by
        apply Spec.mapMulEquiv.injective
        rw [Spec.mapMulEquiv.apply_symm_apply,
          TauCeti.CommHopfAlgCat.mapMulEquiv_mapValue H χ.unop.unop (Spec.mapMulEquiv.symm g),
          Spec.mapMulEquiv.apply_symm_apply]
        rfl
      have hX := congrArg (fun f ↦ f (ULift.up x)) (e.inv.hom.naturality χ)
      have he := congrArg (fun f ↦ f
        (Spec.mapMulEquiv.symm g • e.inv.hom.app A (ULift.up x))) (e.hom.hom.naturality χ)
      simp only [ConcreteCategory.comp_apply] at hX he
      change e.hom.hom.app B (Spec.mapMulEquiv.symm
          (((algSpec (CommRingCat.of R)).map χ.unop ≫ p) ≫ fst _ _) •
        e.inv.hom.app B
          (ULift.up (((algSpec (CommRingCat.of R)).map χ.unop ≫ p) ≫ snd _ _))) =
        (CommAlgCat.pointsSheaf X).obj.map χ (e.hom.hom.app A
          (Spec.mapMulEquiv.symm g • e.inv.hom.app A (ULift.up x)))
      erw [Category.assoc, Category.assoc, hG, hX, ← map_smul_fppfHomogeneousQuotient, ← he]
      rfl
  }⟩

private def representedQuotientSmul :
    (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⊗ X ⟶ X :=
  (CommAlgCat.fullyFaithfulPointsSheafFunctor R).preimage
    (representedQuotientActionSheafHom H I e)

private theorem representedQuotientSmul_comp_pointsSheaf {A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ}
    (g : (Spec (CommRingCat.of A.unop.unop)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))
    (x : (Spec (CommRingCat.of A.unop.unop)).asOver (Spec (CommRingCat.of R)) ⟶ X) :
    e.inv.hom.app A (ULift.up (lift g x ≫ representedQuotientSmul H I e)) =
      Spec.mapMulEquiv.symm g • e.inv.hom.app A (ULift.up x) := by
  have hpre := congrArg (fun α ↦ α.hom.app A (ULift.up (lift g x)))
    ((CommAlgCat.fullyFaithfulPointsSheafFunctor R).map_preimage
      (representedQuotientActionSheafHom H I e))
  change ((CommAlgCat.pointsSheafFunctor R).map (representedQuotientSmul H I e)).hom.app
      A (ULift.up (lift g x)) = _ at hpre
  rw [CommAlgCat.pointsSheafFunctor_map_hom_app] at hpre
  have happ : (representedQuotientActionSheafHom H I e).hom.app A (ULift.up (lift g x)) =
      e.hom.hom.app A (Spec.mapMulEquiv.symm g • e.inv.hom.app A (ULift.up x)) := by
    change e.hom.hom.app A (Spec.mapMulEquiv.symm (lift g x ≫ fst _ _) •
        e.inv.hom.app A (ULift.up (lift g x ≫ snd _ _))) = _
    rw [lift_fst]
    erw [lift_snd]
  have hinv := congrArg (e.inv.hom.app A) (hpre.trans happ)
  simpa only [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ConcreteCategory.id_apply] using hinv

/-- **The canonical internal group action on a scheme representing `G/N`.** When `e` identifies
`fppfHomogeneousQuotient H I` with the fppf sheaf of points of `X`, the left coset action
`fppfHomogeneousQuotientAction H I` induces a `ModObj` instance on `X` for the affine group
scheme `Spec H`. -/
@[instance_reducible]
def representedQuotientModObj :
    ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X where
  smul := representedQuotientSmul H I e
  one_smul := by
    let G := (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))
    apply (CommAlgCat.pointsSheafFunctor R).map_injective
    refine Sheaf.hom_ext
      (NatTrans.ext (funext fun ⟨⟨A⟩⟩ ↦ ConcreteCategory.hom_ext _ _ ?_))
    rintro ⟨z⟩
    let T := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))
    let z' : T ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ X := z
    change ULift.up (z' ≫ _) = ULift.up (z' ≫ _)
    rw [ULift.up_inj]
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionUnitIso]
    let x : T ⟶ X := z' ≫ snd (𝟙_ _) X
    have hz : z' = lift (toUnit T) x := by
      apply CartesianMonoidalCategory.hom_ext
      · exact toUnit_unique _ _
      · simp [x]
    have hl : z' ≫ η[G] ▷ X ≫ representedQuotientSmul H I e =
        lift (toUnit T ≫ η[G]) x ≫ representedQuotientSmul H I e := by
      rw [hz, lift_whiskerRight_assoc]
    have hr : z' ≫ (λ_ X).hom = x := by
      rw [leftUnitor_hom]
    rw [hl, hr]
    have hinj : Function.Injective (e.inv.hom.app (op (op A))) := by
      have : IsIso (e.inv.hom.app (op (op A))) :=
        inferInstanceAs (IsIso ((((sheafToPresheaf _ _).mapIso e.symm).app (op (op A))).hom))
      exact (ConcreteCategory.bijective_of_isIso _).injective
    apply ULift.up_inj.mp
    apply hinj
    have h1 : Spec.mapMulEquiv.symm (toUnit T ≫ η[G]) = 1 := by
      rw [← Hom.one_def, map_one]
    let := instMulActionPointsFppfHomogeneousQuotient H I (op (op A))
    exact (representedQuotientSmul_comp_pointsSheaf H I e (A := op (op A))
      (toUnit T ≫ η[G]) x).trans (by rw [h1, _root_.one_smul]; rfl)
  mul_smul := by
    let G := (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))
    apply (CommAlgCat.pointsSheafFunctor R).map_injective
    refine Sheaf.hom_ext
      (NatTrans.ext (funext fun ⟨⟨A⟩⟩ ↦ ConcreteCategory.hom_ext _ _ ?_))
    rintro ⟨z⟩
    let T := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))
    let z' : T ⟶ (G ⊗ G) ⊗ X := z
    change ULift.up (z' ≫ _) = ULift.up (z' ≫ _)
    rw [ULift.up_inj]
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionHomRight,
      MonoidalCategory.selfLeftAction_actionAssocIso]
    let g₁ : T ⟶ G := z' ≫ fst (G ⊗ G) X ≫ fst G G
    let g₂ : T ⟶ G := z' ≫ fst (G ⊗ G) X ≫ snd G G
    let x : T ⟶ X := z' ≫ snd (G ⊗ G) X
    have hz : z' = lift (lift g₁ g₂) x := by
      apply CartesianMonoidalCategory.hom_ext
      · apply CartesianMonoidalCategory.hom_ext <;> simp [g₁, g₂]
      · simp [x]
    have hL : z' ≫ μ[G] ▷ X ≫ representedQuotientSmul H I e =
        lift (g₁ * g₂) x ≫ representedQuotientSmul H I e := by
      rw [hz, lift_whiskerRight_assoc, Hom.mul_def]
    have hR : z' ≫ (α_ G G X).hom ≫ G ◁ representedQuotientSmul H I e ≫
        representedQuotientSmul H I e =
        lift g₁ (lift g₂ x ≫ representedQuotientSmul H I e) ≫
          representedQuotientSmul H I e := by
      rw [hz, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
    let := instMulActionPointsFppfHomogeneousQuotient H I (op (op A))
    have heL := representedQuotientSmul_comp_pointsSheaf H I e (A := op (op A)) (g₁ * g₂) x
    have heR := (representedQuotientSmul_comp_pointsSheaf H I e (A := op (op A)) g₁
      (lift g₂ x ≫ representedQuotientSmul H I e)).trans
      ((congrArg (Spec.mapMulEquiv.symm g₁ • ·)
        (representedQuotientSmul_comp_pointsSheaf H I e (A := op (op A)) g₂ x)).trans
        (by rw [← SemigroupAction.mul_smul, ← map_mul]))
    have hinj : Function.Injective (e.inv.hom.app (op (op A))) := by
      have : IsIso (e.inv.hom.app (op (op A))) :=
        inferInstanceAs (IsIso ((((sheafToPresheaf _ _).mapIso e.symm).app (op (op A))).hom))
      exact (ConcreteCategory.bijective_of_isIso _).injective
    exact ULift.up_inj.mp (hinj (by rw [hL, hR]; exact heL.trans heR.symm))

/-- Applying `e.inv` to `g • x` for `representedQuotientModObj` applies `Spec.mapMulEquiv.symm g`
to `e.inv x` via `instSMulPointsFppfHomogeneousQuotient`. -/
@[simp]
theorem fppfHomogeneousQuotient_inv_app_smul
    {A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ}
    (g : (Spec (CommRingCat.of A.unop.unop)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))
    (x : (Spec (CommRingCat.of A.unop.unop)).asOver (Spec (CommRingCat.of R)) ⟶ X) :
    letI := representedQuotientModObj H I e
    e.inv.hom.app A (ULift.up (g • x)) =
      Spec.mapMulEquiv.symm g • e.inv.hom.app A (ULift.up x) :=
  representedQuotientSmul_comp_pointsSheaf H I e g x

/-- **Equivariance of `representedQuotientProjection`.** With `representedQuotientModObj H I e` on
`X`, `representedQuotientProjection H I e` intertwines left multiplication on `Spec H` with the
action on `X`. -/
@[reassoc]
theorem mul_representedQuotientProjection :
    letI := representedQuotientModObj H I e
    μ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))] ≫
        representedQuotientProjection H I e =
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ◁
          representedQuotientProjection H I e ≫
        γ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)),X] := by
  let := representedQuotientModObj H I e
  let G := (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))
  apply (CommAlgCat.pointsSheafFunctor R).map_injective
  refine Sheaf.hom_ext
    (NatTrans.ext (funext fun ⟨⟨A⟩⟩ ↦ ConcreteCategory.hom_ext _ _ ?_))
  rintro ⟨z⟩
  let T := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))
  let z' : T ⟶ G ⊗ G := z
  change ULift.up (z' ≫ _) = ULift.up (z' ≫ _)
  rw [ULift.up_inj]
  let g₁ : T ⟶ G := z' ≫ fst G G
  let g₂ : T ⟶ G := z' ≫ snd G G
  have hL : z' ≫ μ[G] ≫ representedQuotientProjection H I e =
      (g₁ * g₂) ≫ representedQuotientProjection H I e := by
    rw [← lift_comp_fst_snd z', ← Category.assoc, ← Hom.mul_def]
  have hR : z' ≫ G ◁ representedQuotientProjection H I e ≫ γ[G,X] =
      g₁ • (g₂ ≫ representedQuotientProjection H I e) := by
    rw [← lift_comp_fst_snd z', lift_whiskerLeft_assoc, Hom.smul_def]
  let := instMulActionPointsFppfHomogeneousQuotient H I (op (op A))
  have he1 :
      e.inv.hom.app (op (op A)) (ULift.up ((g₁ * g₂) ≫ representedQuotientProjection H I e)) =
        (fppfHomogeneousQuotientProjection H I).app (op (op A))
          (ULift.up (Spec.mapMulEquiv.symm g₁ * Spec.mapMulEquiv.symm g₂)) := by
    have h : (g₁ * g₂) ≫ representedQuotientProjection H I e =
        ((e.hom.hom.app (op (op A))) ((fppfHomogeneousQuotientProjection H I).app (op (op A))
          (ULift.up (Spec.mapMulEquiv.symm (g₁ * g₂))))).down := by
      simpa only [Spec.mapMulEquiv.apply_symm_apply] using
        mapMulEquiv_comp_representedQuotientProjection H I e (Spec.mapMulEquiv.symm (g₁ * g₂))
    erw [h]
    rw [map_mul]
    exact congrArg (fun α ↦ α.hom.app (op (op A))
      ((fppfHomogeneousQuotientProjection H I).app (op (op A))
        (ULift.up (Spec.mapMulEquiv.symm g₁ * Spec.mapMulEquiv.symm g₂)))) e.hom_inv_id
  have he2 : e.inv.hom.app (op (op A))
        (ULift.up (g₁ • (g₂ ≫ representedQuotientProjection H I e))) =
      Spec.mapMulEquiv.symm g₁ • (fppfHomogeneousQuotientProjection H I).app (op (op A))
        (ULift.up (Spec.mapMulEquiv.symm g₂)) := by
    have h : g₂ ≫ representedQuotientProjection H I e =
        ((e.hom.hom.app (op (op A))) ((fppfHomogeneousQuotientProjection H I).app (op (op A))
          (ULift.up (Spec.mapMulEquiv.symm g₂)))).down := by
      simpa only [Spec.mapMulEquiv.apply_symm_apply] using
        mapMulEquiv_comp_representedQuotientProjection H I e (Spec.mapMulEquiv.symm g₂)
    rw [fppfHomogeneousQuotient_inv_app_smul (A := op (op A))]
    erw [h]
    exact congrArg (Spec.mapMulEquiv.symm g₁ • ·) (congrArg (fun α ↦ α.hom.app (op (op A))
      ((fppfHomogeneousQuotientProjection H I).app (op (op A))
        (ULift.up (Spec.mapMulEquiv.symm g₂)))) e.hom_inv_id)
  have hinj : Function.Injective (e.inv.hom.app (op (op A))) := by
    have : IsIso (e.inv.hom.app (op (op A))) :=
      inferInstanceAs (IsIso ((((sheafToPresheaf _ _).mapIso e.symm).app (op (op A))).hom))
    exact (ConcreteCategory.bijective_of_isIso _).injective
  exact ULift.up_inj.mp (hinj (by
    rw [hL, hR]
    exact he1.trans ((smul_fppfHomogeneousQuotientProjection_app H I _ _ _).symm.trans he2.symm)))

/-- If `X` already carries a `ModObj` instance for `Spec H` making
`representedQuotientProjection H I e` equivariant, it agrees with `representedQuotientModObj`. -/
theorem representedQuotientModObj_eq_of_comp
    [m : ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X]
    (hm : μ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))] ≫
        representedQuotientProjection H I e =
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ◁
          representedQuotientProjection H I e ≫
        γ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)),X]) :
    m = representedQuotientModObj H I e := by
  let _ := representedQuotientModObj H I e
  have hhom : @IsModHom (Over (Spec (CommRingCat.of R))) _ _ (Over (Spec (CommRingCat.of R))) _ _
      ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) _ X X m
      (representedQuotientModObj H I e) (𝟙 X) :=
    @isModHom_of_isLocallySurjective_comp R _
      ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) X X _ m
      (representedQuotientModObj H I e) (representedQuotientProjection H I e) inferInstance hm
      (𝟙 X) (by simpa only [Category.comp_id] using mul_representedQuotientProjection H I e)
  have hact := @IsModHom.smul_hom (Over (Spec (CommRingCat.of R))) _ _
    (Over (Spec (CommRingCat.of R))) _ _
    ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) _ X X m
    (representedQuotientModObj H I e) (𝟙 X) hhom
  simp only [Category.comp_id, MonoidalCategory.selfLeftAction_actionHomRight,
    whiskerLeft_id] at hact
  cases m
  congr

/-- **Equivariance of `representedQuotientDesc`.** If `q : Spec H ⟶ Y` intertwines multiplication
with an action of `Spec H` on `Y`, then its descent along `representedQuotientProjection H I e` is
equivariant for `representedQuotientModObj H I e`. -/
theorem isModHom_representedQuotientDesc
    {Y : Over (Spec (CommRingCat.of R))}
    [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) Y]
    (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
    (hq : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
      (n : quotientPointsSubgroup H I A),
      Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q)
    (hact : μ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))] ≫ q =
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ◁ q ≫
        γ[(Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)),Y]) :
    letI := representedQuotientModObj H I e
    IsModHom ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))
      (representedQuotientDesc H I e q hq) := by
  let := representedQuotientModObj H I e
  exact isModHom_of_isLocallySurjective_comp (representedQuotientProjection H I e)
    (mul_representedQuotientProjection H I e) (representedQuotientDesc H I e q hq) (by
      simpa only [representedQuotientProjection_comp_desc] using hact)

/-- **`fppfHomogeneousQuotientSchemeMap` is equivariant** for the canonical
`representedQuotientModObj` actions on its source and target. -/
theorem isModHom_fppfHomogeneousQuotientSchemeMap {J : HopfIdeal R H} (hJI : J ≤ I)
    {Y : Over (Spec (CommRingCat.of R))}
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y) :
    letI := representedQuotientModObj H I e
    letI := representedQuotientModObj H J eJ
    IsModHom ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))
      (fppfHomogeneousQuotientSchemeMap H hJI e eJ) := by
  let := representedQuotientModObj H I e
  let := representedQuotientModObj H J eJ
  exact isModHom_of_isLocallySurjective_comp (representedQuotientProjection H I e)
    (mul_representedQuotientProjection H I e) (fppfHomogeneousQuotientSchemeMap H hJI e eJ) (by
      simpa only [representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap] using
        mul_representedQuotientProjection H J eJ)

/-- **Canonical comparison isomorphisms are equivariant.** -/
theorem isModHom_representedQuotientIso {Y : Over (Spec (CommRingCat.of R))}
    (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y) :
    letI := representedQuotientModObj H I e
    letI := representedQuotientModObj H I e₂
    IsModHom ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)))
      (representedQuotientIso H I e e₂).hom := by
  rw [representedQuotientIso_hom]
  exact isModHom_fppfHomogeneousQuotientSchemeMap H I e (le_refl I) e₂

/-- Left translation by a base-ring point `g` on a representing scheme agrees with
`TauCeti.translation` for the canonical action `representedQuotientModObj`. -/
theorem representedQuotientTranslation_eq_translation
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    representedQuotientTranslation H I e g =
      letI := representedQuotientModObj H I e
      TauCeti.translation X
        ((Over.homMk (𝟙 (Spec (CommRingCat.of R)))
          (by simp [Scheme.asOver, OverClass.asOver, Over.mk_hom,
            AlgebraicGeometry.specOverSpec_over]) :
          𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
            (Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R))) ≫
          Spec.mapMulEquiv g) := by
  let := representedQuotientModObj H I e
  apply Iso.ext
  apply (CommAlgCat.pointsSheafFunctor R).map_injective
  refine Sheaf.hom_ext
    (NatTrans.ext (funext fun ⟨⟨A⟩⟩ ↦ ConcreteCategory.hom_ext _ _ ?_))
  rintro ⟨z⟩
  let T := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))
  let z' : T ⟶ X := z
  change ULift.up (z' ≫ _) = ULift.up (z' ≫ _)
  rw [ULift.up_inj]
  have hinj : Function.Injective (e.inv.hom.app (op (op A))) := by
    have : IsIso (e.inv.hom.app (op (op A))) :=
      inferInstanceAs (IsIso ((((sheafToPresheaf _ _).mapIso e.symm).app (op (op A))).hom))
    exact (ConcreteCategory.bijective_of_isIso _).injective
  apply ULift.up_inj.mp
  apply hinj
  let := instMulActionPointsFppfHomogeneousQuotient H I (op (op A))
  have hL : e.inv.hom.app (op (op A))
        (ULift.up (z' ≫ (representedQuotientTranslation H I e g).hom)) =
      HopfAlgebra.extendPoint H A g • e.inv.hom.app (op (op A)) (ULift.up z') := by
    have hcomp := congrArg (fun α ↦ α.hom.app (op (op A)) (ULift.up z'))
      (pointsSheafFunctor_map_representedQuotientTranslation_hom H I e g)
    have happ : (e.inv ≫ (fppfHomogeneousQuotientTranslation H I g).hom ≫ e.hom).hom.app
          (op (op A)) (ULift.up z') =
        e.hom.hom.app (op (op A)) ((fppfHomogeneousQuotientTranslation H I g).hom.hom.app
          (op (op A)) (e.inv.hom.app (op (op A)) (ULift.up z'))) := rfl
    rw [CommAlgCat.pointsSheafFunctor_map_hom_app, happ] at hcomp
    have hinv := congrArg (e.inv.hom.app (op (op A))) hcomp
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id] at hinv
    simpa only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
      ConcreteCategory.id_apply, fppfHomogeneousQuotientTranslation_hom_app] using hinv
  have hR : e.inv.hom.app (op (op A)) (ULift.up (z' ≫ (TauCeti.translation X
        ((Over.homMk (𝟙 (Spec (CommRingCat.of R)))
          (by simp [Scheme.asOver, OverClass.asOver, Over.mk_hom,
            AlgebraicGeometry.specOverSpec_over]) :
          𝟙_ (Over (Spec (CommRingCat.of R))) ⟶
            (Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of R))) ≫
          Spec.mapMulEquiv g)).hom)) =
      HopfAlgebra.extendPoint H A g • e.inv.hom.app (op (op A)) (ULift.up z') := by
    rw [TauCeti.comp_translation_hom]
    erw [fppfHomogeneousQuotient_inv_app_smul (A := op (op A)),
      toUnit_comp_unitPoint_mapMulEquiv H g A, Spec.mapMulEquiv.symm_apply_apply]
  exact hL.trans hR.symm

end RepresentedQuotientAction

end CommHopfAlgCat
