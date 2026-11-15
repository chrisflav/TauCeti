/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.Basic
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The free braided monoidal category on a tensor signature

Given a tensor signature `S` (generating objects and arbitrary-arity coupons between formal tensor
words, including the empty word), `TauCeti.TensorSignature.FreeBraided S` is the free braided
monoidal category on `S`. Its objects are the formal tensor words `FreeMonoidalCategory S.Obj`.
Its morphisms are formal composites, tensor products and whiskerings of identities, associators,
unitors, braidings, inverse braidings and coupons, modulo the axioms of a braided monoidal category;
neither symmetry nor any equation between coupons is imposed.

The formal-morphism syntax and monoidal relation extend `TauCeti.TensorSignature.FreeMonoidal`
(which follows `Mathlib/CategoryTheory/Monoidal/Free/Basic.lean`, by Markus Himmel) by constructors
for the braiding and its inverse together with naturality and the two hexagon identities.

## Main definitions and results

* `TauCeti.TensorSignature.FreeBraided S`: the free braided monoidal category on `S`, with
  generators `FreeBraided.of` and `FreeBraided.coupon`, and induction principle
  `FreeBraided.Hom.inductionOn`.
* `TauCeti.TensorSignature.FreeMonoidal.toFreeBraided`: the canonical strict monoidal inclusion from
  `S.FreeMonoidal` into `S.FreeBraided`.
* `FreeBraided.lift fo fc`: the strong braided monoidal functor into an arbitrary (not necessarily
  strict) braided monoidal category determined by images `fo` of the generating objects and `fc` of
  the coupons, with identity unit comparison and tensorator, computation rules on generators and
  compatibility `FreeBraided.toFreeBraided_comp_lift` with `FreeMonoidal.lift`.
* `FreeBraided.monoidalNatIso` and `FreeBraided.natTrans_ext`: two strong braided functors out of
  `S.FreeBraided` agreeing up to isomorphism on the generating objects compatibly with every coupon
  are isomorphic by a unique monoidal natural isomorphism extending the given generator
  isomorphisms.
* `FreeBraided.crossingExp`: for a signature whose coupons preserve port length (in particular when
  `S.Coupon` is empty), the integer crossing-exponent sum of a morphism, sending `(β_ X Y).hom` to
  `X.as.length * Y.as.length` and `(β_ X Y).inv` to its negation. Composing two positive crossings
  of generating objects is therefore distinct from the identity
  (`FreeBraided.braiding_of_comp_braiding_of_ne_id`), showing that the braiding of `S.FreeBraided`
  does not satisfy the symmetry axiom whenever `S.Obj` is nonempty.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §3.
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813 (2011), §3.3.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

variable (S : TensorSignature.{u, v})

/-- The free braided monoidal category on a tensor signature `S`. Its objects are the formal tensor
words in the generating objects of `S`. -/
structure FreeBraided where
  /-- The formal tensor word underlying an object of the free braided monoidal category. -/
  as : FreeMonoidalCategory S.Obj

namespace FreeBraided

variable {S}

/-- The object of the free braided monoidal category given by a single generating object. -/
@[expose] def of (a : S.Obj) : S.FreeBraided := ⟨.of a⟩

/-- Formal composites, tensor products and whiskerings of identities, associators, unitors,
braidings, inverse braidings and coupons. -/
inductive Hom : FreeMonoidalCategory S.Obj → FreeMonoidalCategory S.Obj → Type (max u v)
  | id (X) : Hom X X
  | α_hom (X Y Z : FreeMonoidalCategory S.Obj) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : FreeMonoidalCategory S.Obj) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (unit.tensor X) X
  | l_inv (X) : Hom X (unit.tensor X)
  | ρ_hom (X : FreeMonoidalCategory S.Obj) : Hom (X.tensor unit) X
  | ρ_inv (X : FreeMonoidalCategory S.Obj) : Hom X (X.tensor unit)
  | β_hom (X Y : FreeMonoidalCategory S.Obj) : Hom (X.tensor Y) (Y.tensor X)
  | β_inv (X Y : FreeMonoidalCategory S.Obj) : Hom (Y.tensor X) (X.tensor Y)
  | coupon (g : S.Coupon) : Hom (S.src g) (S.tgt g)
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : FreeMonoidalCategory S.Obj) {Y₁ Y₂} (f : Hom Y₁ Y₂) :
      Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : FreeMonoidalCategory S.Obj) :
      Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)

/-- The relation on formal braided morphisms generated by the axioms of a braided monoidal category
and closed under composition, whiskering and tensor products. Neither symmetry nor any coupon
equation is imposed. -/
inductive HomEquiv : ∀ {X Y : FreeMonoidalCategory S.Obj}, Hom X Y → Hom X Y → Prop
  | refl {X Y} (f : Hom X Y) : HomEquiv f f
  | symm {X Y} (f g : Hom X Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : Hom X Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h
  | comp {X Y Z} {f f' : Hom X Y} {g g' : Hom Y Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Hom Y Z) :
      HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Hom Y Z) (X) :
      HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : Hom W X} {g g' : Hom Y Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : Hom X₁ Y₁) (g : Hom X₂ Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : Hom X Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : Hom X Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V} (f : Hom X U) (g : Hom U V) (h : Hom V Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂)
      (g₁ : Hom Y₁ Z₁) (g₂ : Hom Y₂ Z₂) :
      HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂)
      (f₃ : Hom X₃ Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | ρ_naturality {X Y} (f : Hom X Y) :
      HomEquiv ((f.whiskerRight unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | l_naturality {X Y} (f : Hom X Y) :
      HomEquiv ((f.whiskerLeft unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  | pentagon {W X Y Z} :
      HomEquiv
        (((Hom.α_hom W X Y).whiskerRight Z).comp
          ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
        ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} :
      HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)
  | β_hom_inv {X Y} : HomEquiv ((Hom.β_hom X Y).comp (Hom.β_inv X Y)) (Hom.id _)
  | β_inv_hom {X Y} : HomEquiv ((Hom.β_inv X Y).comp (Hom.β_hom X Y)) (Hom.id _)
  | braiding_naturality_right (X : FreeMonoidalCategory S.Obj) {Y Z} (f : Hom Y Z) :
      HomEquiv ((f.whiskerLeft X).comp (Hom.β_hom X Z)) ((Hom.β_hom X Y).comp (f.whiskerRight X))
  | braiding_naturality_left {X Y} (f : Hom X Y) (Z : FreeMonoidalCategory S.Obj) :
      HomEquiv ((f.whiskerRight Z).comp (Hom.β_hom Y Z)) ((Hom.β_hom X Z).comp (f.whiskerLeft Z))
  | hexagon_forward {X Y Z} :
      HomEquiv
        ((Hom.α_hom X Y Z).comp ((Hom.β_hom X (Y.tensor Z)).comp (Hom.α_hom Y Z X)))
        (((Hom.β_hom X Y).whiskerRight Z).comp
          ((Hom.α_hom Y X Z).comp ((Hom.β_hom X Z).whiskerLeft Y)))
  | hexagon_reverse {X Y Z} :
      HomEquiv
        ((Hom.α_inv X Y Z).comp ((Hom.β_hom (X.tensor Y) Z).comp (Hom.α_inv Z X Y)))
        (((Hom.β_hom Y Z).whiskerLeft X).comp
          ((Hom.α_inv X Z Y).comp ((Hom.β_hom X Z).whiskerRight Y)))

/-- Formal braided morphisms are identified when the braided-monoidal axioms make them equal. -/
instance setoidHom (X Y : FreeMonoidalCategory S.Obj) : Setoid (Hom X Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

open HomEquiv

instance : Category.{max u v} S.FreeBraided where
  Hom X Y := Quotient (setoidHom X.as Y.as)
  id X := ⟦Hom.id X.as⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (assoc f g h)

instance : MonoidalCategory S.FreeBraided where
  tensorObj X Y := ⟨X.as.tensor Y.as⟩
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f :=
    Quot.map (fun f ↦ Hom.whiskerLeft X.as f) (fun f f' ↦ .whiskerLeft _ f f') f
  whiskerRight f Y :=
    Quot.map (fun f ↦ Hom.whiskerRight f Y.as) (fun f f' ↦ .whiskerRight f f' _) f
  tensorHom_def := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩
    exact Quotient.sound (tensorHom_def _ _)
  id_tensorHom_id _ _ := Quot.sound id_tensorHom_id
  tensorHom_comp_tensorHom := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact Quotient.sound (tensorHom_comp_tensorHom _ _ _ _)
  whiskerLeft_id X Y := Quot.sound (HomEquiv.whiskerLeft_id X.as Y.as)
  id_whiskerRight X Y := Quot.sound (HomEquiv.id_whiskerRight X.as Y.as)
  tensorUnit := ⟨unit⟩
  associator X Y Z :=
    ⟨⟦Hom.α_hom X.as Y.as Z.as⟧, ⟦Hom.α_inv X.as Y.as Z.as⟧, Quotient.sound α_hom_inv,
      Quotient.sound α_inv_hom⟩
  associator_naturality := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    exact Quotient.sound (associator_naturality _ _ _)
  leftUnitor X :=
    ⟨⟦Hom.l_hom X.as⟧, ⟦Hom.l_inv X.as⟧, Quotient.sound l_hom_inv, Quotient.sound l_inv_hom⟩
  leftUnitor_naturality := by
    rintro _ _ ⟨f⟩
    exact Quotient.sound (l_naturality _)
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X.as⟧, ⟦Hom.ρ_inv X.as⟧, Quotient.sound ρ_hom_inv, Quotient.sound ρ_inv_hom⟩
  rightUnitor_naturality := by
    rintro _ _ ⟨f⟩
    exact Quotient.sound (ρ_naturality _)
  pentagon _ _ _ _ := Quotient.sound pentagon
  triangle _ _ := Quotient.sound triangle

instance : BraidedCategory S.FreeBraided where
  braiding X Y :=
    ⟨⟦Hom.β_hom X.as Y.as⟧, ⟦Hom.β_inv X.as Y.as⟧, Quotient.sound β_hom_inv,
      Quotient.sound β_inv_hom⟩
  braiding_naturality_right := by
    rintro X _ _ ⟨f⟩
    exact Quotient.sound (HomEquiv.braiding_naturality_right X.as f)
  braiding_naturality_left := by
    rintro _ _ ⟨f⟩ Z
    exact Quotient.sound (HomEquiv.braiding_naturality_left f Z.as)
  hexagon_forward _ _ _ := Quotient.sound HomEquiv.hexagon_forward
  hexagon_reverse _ _ _ := Quotient.sound HomEquiv.hexagon_reverse

/-- The morphism of the free braided category represented by a formal braided morphism. -/
abbrev homMk {X Y : S.FreeBraided} (f : Hom X.as Y.as) : X ⟶ Y := ⟦f⟧

/-- The generating morphism given by a coupon, from its source word to its target word. -/
@[expose] def coupon (g : S.Coupon) : (⟨S.src g⟩ : S.FreeBraided) ⟶ ⟨S.tgt g⟩ :=
  homMk (Hom.coupon g)

@[simp]
theorem homMk_id (X : S.FreeBraided) : homMk (Hom.id X.as) = 𝟙 X := rfl

@[simp]
theorem homMk_comp {X Y Z : S.FreeBraided} (f : Hom X.as Y.as) (g : Hom Y.as Z.as) :
    homMk (Y := Z) (f.comp g) = homMk f ≫ homMk g := rfl

@[simp]
theorem homMk_tensor {X₁ Y₁ X₂ Y₂ : S.FreeBraided} (f : Hom X₁.as Y₁.as) (g : Hom X₂.as Y₂.as) :
    homMk (X := X₁ ⊗ X₂) (Y := Y₁ ⊗ Y₂) (f.tensor g) = homMk f ⊗ₘ homMk g := rfl

@[simp]
theorem homMk_whiskerLeft (X : S.FreeBraided) {Y₁ Y₂ : S.FreeBraided} (f : Hom Y₁.as Y₂.as) :
    homMk (X := X ⊗ Y₁) (Y := X ⊗ Y₂) (f.whiskerLeft X.as) = X ◁ homMk f := rfl

@[simp]
theorem homMk_whiskerRight {X₁ X₂ : S.FreeBraided} (f : Hom X₁.as X₂.as) (Y : S.FreeBraided) :
    homMk (X := X₁ ⊗ Y) (Y := X₂ ⊗ Y) (f.whiskerRight Y.as) = homMk f ▷ Y := rfl

@[simp]
theorem homMk_α_hom (X Y Z : S.FreeBraided) :
    homMk (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z)) (Hom.α_hom X.as Y.as Z.as) = (α_ X Y Z).hom :=
  rfl

@[simp]
theorem homMk_α_inv (X Y Z : S.FreeBraided) :
    homMk (X := X ⊗ (Y ⊗ Z)) (Y := (X ⊗ Y) ⊗ Z) (Hom.α_inv X.as Y.as Z.as) = (α_ X Y Z).inv :=
  rfl

@[simp]
theorem homMk_l_hom (X : S.FreeBraided) :
    homMk (X := 𝟙_ _ ⊗ X) (Hom.l_hom X.as) = (λ_ X).hom := rfl

@[simp]
theorem homMk_l_inv (X : S.FreeBraided) :
    homMk (Y := 𝟙_ _ ⊗ X) (Hom.l_inv X.as) = (λ_ X).inv := rfl

@[simp]
theorem homMk_ρ_hom (X : S.FreeBraided) :
    homMk (X := X ⊗ 𝟙_ _) (Hom.ρ_hom X.as) = (ρ_ X).hom := rfl

@[simp]
theorem homMk_ρ_inv (X : S.FreeBraided) :
    homMk (Y := X ⊗ 𝟙_ _) (Hom.ρ_inv X.as) = (ρ_ X).inv := rfl

@[simp]
theorem homMk_β_hom (X Y : S.FreeBraided) :
    homMk (X := X ⊗ Y) (Y := Y ⊗ X) (Hom.β_hom X.as Y.as) = (β_ X Y).hom := rfl

@[simp]
theorem homMk_β_inv (X Y : S.FreeBraided) :
    homMk (X := Y ⊗ X) (Y := X ⊗ Y) (Hom.β_inv X.as Y.as) = (β_ X Y).inv := rfl

@[simp]
theorem homMk_coupon (g : S.Coupon) :
    homMk (X := ⟨S.src g⟩) (Y := ⟨S.tgt g⟩) (Hom.coupon g) = coupon g := rfl

/-- Induction principle for morphisms of the free braided monoidal category: a property of
morphisms holding for identities, associators, unitors, braidings, inverse braidings and coupons,
and stable under composition and whiskering on either side, holds for every morphism. -/
theorem Hom.inductionOn {motive : {X Y : S.FreeBraided} → (X ⟶ Y) → Prop} {X Y : S.FreeBraided}
    (t : X ⟶ Y)
    (id : (X : S.FreeBraided) → motive (𝟙 X))
    (α_hom : (X Y Z : S.FreeBraided) → motive (α_ X Y Z).hom)
    (α_inv : (X Y Z : S.FreeBraided) → motive (α_ X Y Z).inv)
    (l_hom : (X : S.FreeBraided) → motive (λ_ X).hom)
    (l_inv : (X : S.FreeBraided) → motive (λ_ X).inv)
    (ρ_hom : (X : S.FreeBraided) → motive (ρ_ X).hom)
    (ρ_inv : (X : S.FreeBraided) → motive (ρ_ X).inv)
    (β_hom : (X Y : S.FreeBraided) → motive (β_ X Y).hom)
    (β_inv : (X Y : S.FreeBraided) → motive (β_ X Y).inv)
    (coupon : (g : S.Coupon) → motive (FreeBraided.coupon g))
    (comp : {X Y Z : S.FreeBraided} → (f : X ⟶ Y) → (g : Y ⟶ Z) → motive f → motive g →
      motive (f ≫ g))
    (whiskerLeft : (X : S.FreeBraided) → {Y Z : S.FreeBraided} → (f : Y ⟶ Z) → motive f →
      motive (X ◁ f))
    (whiskerRight : {X Y : S.FreeBraided} → (f : X ⟶ Y) → (Z : S.FreeBraided) → motive f →
      motive (f ▷ Z)) :
    motive t := by
  suffices H : ∀ {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y),
      motive (homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) by
    induction t using Quotient.inductionOn with | _ f
    exact H f
  intro X Y f
  induction f with
  | id X => exact id ⟨X⟩
  | α_hom X Y Z => exact α_hom ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact α_inv ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact l_hom ⟨X⟩
  | l_inv X => exact l_inv ⟨X⟩
  | ρ_hom X => exact ρ_hom ⟨X⟩
  | ρ_inv X => exact ρ_inv ⟨X⟩
  | β_hom X Y => exact β_hom ⟨X⟩ ⟨Y⟩
  | β_inv X Y => exact β_inv ⟨X⟩ ⟨Y⟩
  | coupon g => exact coupon g
  | comp f g hf hg => exact comp _ _ hf hg
  | whiskerLeft X f hf => exact whiskerLeft ⟨X⟩ _ hf
  | whiskerRight f X hf => exact whiskerRight _ ⟨X⟩ hf
  | @tensor W X Y Z f g hf hg =>
    have h : (homMk (f.tensor g) : (⟨W.tensor X⟩ : S.FreeBraided) ⟶ ⟨Y.tensor Z⟩) =
        homMk (X := ⟨W⟩) (Y := ⟨Y⟩) f ▷ (⟨X⟩ : S.FreeBraided) ≫
          (⟨Y⟩ : S.FreeBraided) ◁ homMk (X := ⟨X⟩) (Y := ⟨Z⟩) g :=
      Quotient.sound (HomEquiv.tensorHom_def f g)
    rw [h]
    exact comp _ _ (whiskerRight _ _ hf) (whiskerLeft _ _ hg)

/-- Interpreting a formal tensor word via `FreeBraided.of` recovers that word as an object of
`S.FreeBraided`. -/
@[simp]
theorem projectObj_of : ∀ X : FreeMonoidalCategory S.Obj,
    projectObj (of (S := S)) X = ⟨X⟩
  | .of _ => rfl
  | .unit => rfl
  | .tensor X Y => by
    dsimp only [projectObj]
    rw [projectObj_of X, projectObj_of Y]
    rfl

/-- The underlying formal tensor word of `projectObj f X` in `S.FreeBraided` is obtained by
projecting the underlying words `(f a).as`. -/
theorem as_projectObj {α : Type*} (f : α → S.FreeBraided) :
    ∀ X : FreeMonoidalCategory α, (projectObj f X).as = projectObj (fun a ↦ (f a).as) X
  | .of _ => rfl
  | .unit => rfl
  | .tensor X Y => congrArg₂ (· ⊗ ·) (as_projectObj f X) (as_projectObj f Y)

end FreeBraided

namespace FreeMonoidal

variable {S}

/-- Include a raw monoidal morphism expression into the raw braided morphism expressions. -/
def Hom.toBraided : ∀ {X Y : FreeMonoidalCategory S.Obj}, Hom X Y → FreeBraided.Hom X Y
  | _, _, .id X => .id X
  | _, _, .α_hom X Y Z => .α_hom X Y Z
  | _, _, .α_inv X Y Z => .α_inv X Y Z
  | _, _, .l_hom X => .l_hom X
  | _, _, .l_inv X => .l_inv X
  | _, _, .ρ_hom X => .ρ_hom X
  | _, _, .ρ_inv X => .ρ_inv X
  | _, _, .coupon g => .coupon g
  | _, _, .comp f g => f.toBraided.comp g.toBraided
  | _, _, .whiskerLeft X f => f.toBraided.whiskerLeft X
  | _, _, .whiskerRight f X => f.toBraided.whiskerRight X
  | _, _, .tensor f g => f.toBraided.tensor g.toBraided

/-- The raw inclusion from monoidal to braided expressions preserves the monoidal axioms. -/
theorem HomEquiv.toBraided {X Y : FreeMonoidalCategory S.Obj} {f g : Hom X Y}
    (h : HomEquiv f g) : FreeBraided.HomEquiv f.toBraided g.toBraided := by
  induction h with
  | refl f => exact .refl f.toBraided
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | whiskerLeft X _ _ _ ih => exact .whiskerLeft X _ _ ih
  | whiskerRight _ _ X _ ih => exact .whiskerRight _ _ X ih
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
  | tensorHom_def f g => exact .tensorHom_def f.toBraided g.toBraided
  | comp_id f => exact .comp_id f.toBraided
  | id_comp f => exact .id_comp f.toBraided
  | assoc f g h => exact .assoc f.toBraided g.toBraided h.toBraided
  | id_tensorHom_id => exact .id_tensorHom_id
  | tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ =>
    exact .tensorHom_comp_tensorHom f₁.toBraided f₂.toBraided g₁.toBraided g₂.toBraided
  | whiskerLeft_id X Y => exact .whiskerLeft_id X Y
  | id_whiskerRight X Y => exact .id_whiskerRight X Y
  | α_hom_inv => exact .α_hom_inv
  | α_inv_hom => exact .α_inv_hom
  | associator_naturality f₁ f₂ f₃ =>
    exact .associator_naturality f₁.toBraided f₂.toBraided f₃.toBraided
  | ρ_hom_inv => exact .ρ_hom_inv
  | ρ_inv_hom => exact .ρ_inv_hom
  | ρ_naturality f => exact .ρ_naturality f.toBraided
  | l_hom_inv => exact .l_hom_inv
  | l_inv_hom => exact .l_inv_hom
  | l_naturality f => exact .l_naturality f.toBraided
  | pentagon => exact .pentagon
  | triangle => exact .triangle

/-- Interpret a morphism of `S.FreeMonoidal` inside `S.FreeBraided` via `Hom.toBraided`. -/
def toFreeBraidedMap {X Y : S.FreeMonoidal} (f : X ⟶ Y) :
    (⟨X.as⟩ : S.FreeBraided) ⟶ ⟨Y.as⟩ :=
  Quotient.lift (s := setoidHom X.as Y.as) (fun h ↦ FreeBraided.homMk h.toBraided)
    (fun _ _ h ↦ Quotient.sound (HomEquiv.toBraided h)) f

theorem toFreeBraidedMap_id (X : S.FreeMonoidal) :
    toFreeBraidedMap (𝟙 X) = 𝟙 _ := by rfl

theorem toFreeBraidedMap_comp {X Y Z : S.FreeMonoidal} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toFreeBraidedMap (f ≫ g) = toFreeBraidedMap f ≫ toFreeBraidedMap g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rfl

/-- The canonical strict monoidal inclusion from the free monoidal category on `S` into the free
braided monoidal category on `S`. -/
@[expose] def toFreeBraided : S.FreeMonoidal ⥤ S.FreeBraided where
  obj X := ⟨X.as⟩
  map := toFreeBraidedMap
  map_id := toFreeBraidedMap_id
  map_comp := toFreeBraidedMap_comp

theorem toFreeBraided_obj (X : S.FreeMonoidal) :
    (toFreeBraided (S := S)).obj X = ⟨X.as⟩ := rfl

@[simp]
theorem toFreeBraided_obj_of (a : S.Obj) :
    (toFreeBraided (S := S)).obj (of a) = FreeBraided.of a := rfl

@[simp]
theorem toFreeBraided_obj_tensor (X Y : S.FreeMonoidal) :
    (toFreeBraided (S := S)).obj (X ⊗ Y) =
      (toFreeBraided (S := S)).obj X ⊗ (toFreeBraided (S := S)).obj Y := rfl

@[simp]
theorem toFreeBraided_obj_tensorUnit :
    (toFreeBraided (S := S)).obj (𝟙_ S.FreeMonoidal) = 𝟙_ S.FreeBraided := rfl

@[simp]
theorem toFreeBraided_map_homMk {X Y : S.FreeMonoidal} (f : Hom X.as Y.as) :
    (toFreeBraided (S := S)).map (homMk f) = FreeBraided.homMk f.toBraided := by rfl

@[simp]
theorem toFreeBraided_map_coupon (g : S.Coupon) :
    (toFreeBraided (S := S)).map (coupon g) = FreeBraided.coupon g := by rfl

@[simp]
theorem toFreeBraided_map_whiskerLeft (X : S.FreeMonoidal) {Y₁ Y₂ : S.FreeMonoidal}
    (f : Y₁ ⟶ Y₂) :
    (toFreeBraided (S := S)).map (X ◁ f) =
      (toFreeBraided (S := S)).obj X ◁ (toFreeBraided (S := S)).map f := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem toFreeBraided_map_whiskerRight {X₁ X₂ : S.FreeMonoidal} (f : X₁ ⟶ X₂)
    (Y : S.FreeMonoidal) :
    (toFreeBraided (S := S)).map (f ▷ Y) =
      (toFreeBraided (S := S)).map f ▷ (toFreeBraided (S := S)).obj Y := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem toFreeBraided_map_tensorHom {X₁ Y₁ X₂ Y₂ : S.FreeMonoidal}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (toFreeBraided (S := S)).map (f ⊗ₘ g) =
      (toFreeBraided (S := S)).map f ⊗ₘ (toFreeBraided (S := S)).map g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rfl

@[simp]
theorem toFreeBraided_map_associator_hom (X Y Z : S.FreeMonoidal) :
    (toFreeBraided (S := S)).map (α_ X Y Z).hom =
      (α_ ((toFreeBraided (S := S)).obj X) ((toFreeBraided (S := S)).obj Y)
        ((toFreeBraided (S := S)).obj Z)).hom := by rfl

@[simp]
theorem toFreeBraided_map_associator_inv (X Y Z : S.FreeMonoidal) :
    (toFreeBraided (S := S)).map (α_ X Y Z).inv =
      (α_ ((toFreeBraided (S := S)).obj X) ((toFreeBraided (S := S)).obj Y)
        ((toFreeBraided (S := S)).obj Z)).inv := by rfl

theorem toFreeBraided_map_leftUnitor_hom (X : S.FreeMonoidal) :
    (toFreeBraided (S := S)).map (λ_ X).hom =
      (λ_ ((toFreeBraided (S := S)).obj X)).hom := by rfl

theorem toFreeBraided_map_rightUnitor_hom (X : S.FreeMonoidal) :
    (toFreeBraided (S := S)).map (ρ_ X).hom =
      (ρ_ ((toFreeBraided (S := S)).obj X)).hom := by rfl

instance : (toFreeBraided (S := S)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by
        intros
        dsimp only [Iso.refl_hom, toFreeBraided_obj_tensor]
        simp
      μIso_hom_natural_right := by
        intros
        dsimp only [Iso.refl_hom, toFreeBraided_obj_tensor]
        simp
      associativity := by
        intros
        dsimp only [Iso.refl_hom, toFreeBraided_obj_tensor]
        simp
      left_unitality := by
        intros
        dsimp only [Iso.refl_hom, toFreeBraided_obj_tensor, toFreeBraided_obj_tensorUnit]
        simp [toFreeBraided_map_leftUnitor_hom]
      right_unitality := by
        intros
        dsimp only [Iso.refl_hom, toFreeBraided_obj_tensor, toFreeBraided_obj_tensorUnit]
        simp [toFreeBraided_map_rightUnitor_hom] }

@[simp]
theorem toFreeBraided_ε : Functor.LaxMonoidal.ε (toFreeBraided (S := S)) = 𝟙 _ := by rfl

@[simp]
theorem toFreeBraided_η : Functor.OplaxMonoidal.η (toFreeBraided (S := S)) = 𝟙 _ := by rfl

@[simp]
theorem toFreeBraided_μ (X Y : S.FreeMonoidal) :
    Functor.LaxMonoidal.μ (toFreeBraided (S := S)) X Y = 𝟙 _ := by rfl

@[simp]
theorem toFreeBraided_δ (X Y : S.FreeMonoidal) :
    Functor.OplaxMonoidal.δ (toFreeBraided (S := S)) X Y = 𝟙 _ := by rfl

end FreeMonoidal

namespace FreeBraided

variable {S}

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (fo : S.Obj → D)
  (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g))

/-- The interpretation of a formal braided morphism in `D`, given images `fo` of the generating
objects and `fc` of the coupons. -/
private def liftMapAux :
    ∀ {X Y : FreeMonoidalCategory S.Obj}, Hom X Y → (projectObj fo X ⟶ projectObj fo Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, Hom.α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, Hom.l_hom _ => (λ_ _).hom
  | _, _, Hom.l_inv _ => (λ_ _).inv
  | _, _, Hom.ρ_hom _ => (ρ_ _).hom
  | _, _, Hom.ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.β_hom _ _ => (β_ _ _).hom
  | _, _, Hom.β_inv _ _ => (β_ _ _).inv
  | _, _, Hom.coupon g => fc g
  | _, _, Hom.comp f g => liftMapAux f ≫ liftMapAux g
  | _, _, Hom.whiskerLeft X p => projectObj fo X ◁ liftMapAux p
  | _, _, Hom.whiskerRight p X => liftMapAux p ▷ projectObj fo X
  | _, _, Hom.tensor f g => liftMapAux f ⊗ₘ liftMapAux g

/-- The interpretation of formal braided morphisms respects the braided-monoidal axioms. -/
private theorem liftMapAux_sound {X Y : FreeMonoidalCategory S.Obj} {f g : Hom X Y}
    (h : HomEquiv f g) :
    liftMapAux fo fc f = liftMapAux fo fc g := by
  induction h with
  | refl => rfl
  | symm _ _ _ hfg => exact hfg.symm
  | trans _ _ hfg hgh => exact hfg.trans hgh
  | comp _ _ hf hg => simp only [liftMapAux, hf, hg]
  | whiskerLeft _ _ _ _ hf => dsimp only [liftMapAux]; rw [hf]
  | whiskerRight _ _ _ _ hf => dsimp only [liftMapAux]; rw [hf]
  | tensor _ _ hf hg => dsimp only [liftMapAux]; rw [hf, hg]
  | tensorHom_def => exact MonoidalCategory.tensorHom_def _ _
  | comp_id => exact Category.comp_id _
  | id_comp => exact Category.id_comp _
  | assoc => exact Category.assoc _ _ _
  | id_tensorHom_id => exact MonoidalCategory.id_tensorHom_id _ _
  | tensorHom_comp_tensorHom => exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
  | whiskerLeft_id => exact MonoidalCategory.whiskerLeft_id _ _
  | id_whiskerRight => exact MonoidalCategory.id_whiskerRight _ _
  | α_hom_inv => exact Iso.hom_inv_id _
  | α_inv_hom => exact Iso.inv_hom_id _
  | associator_naturality => exact MonoidalCategory.associator_naturality _ _ _
  | ρ_hom_inv => exact Iso.hom_inv_id _
  | ρ_inv_hom => exact Iso.inv_hom_id _
  | ρ_naturality => exact MonoidalCategory.rightUnitor_naturality _
  | l_hom_inv => exact Iso.hom_inv_id _
  | l_inv_hom => exact Iso.inv_hom_id _
  | l_naturality => exact MonoidalCategory.leftUnitor_naturality _
  | pentagon => exact MonoidalCategory.pentagon _ _ _ _
  | triangle => exact MonoidalCategory.triangle _ _
  | β_hom_inv => exact Iso.hom_inv_id _
  | β_inv_hom => exact Iso.inv_hom_id _
  | braiding_naturality_right => exact BraidedCategory.braiding_naturality_right _ _
  | braiding_naturality_left => exact BraidedCategory.braiding_naturality_left _ _
  | hexagon_forward => exact BraidedCategory.hexagon_forward _ _ _
  | hexagon_reverse => exact BraidedCategory.hexagon_reverse _ _ _

/-- The interpretation of morphisms of `S.FreeBraided`, given the images `fo` of the generating
objects and `fc` of the coupons. -/
def liftMap {X Y : S.FreeBraided} (f : X ⟶ Y) : projectObj fo X.as ⟶ projectObj fo Y.as :=
  Quotient.lift (liftMapAux fo fc) (fun _ _ h ↦ liftMapAux_sound fo fc h) f

theorem liftMap_id (X : S.FreeBraided) : liftMap fo fc (𝟙 X) = 𝟙 _ := by rfl

theorem liftMap_comp {X Y Z : S.FreeBraided} (f : X ⟶ Y) (g : Y ⟶ Z) :
    liftMap fo fc (f ≫ g) = liftMap fo fc f ≫ liftMap fo fc g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rfl

/-- The functor out of the free braided monoidal category on `S` determined by the images `fo` of
the generating objects and `fc` of the coupons. It is strong braided monoidal, with identity
tensorator and unit comparison. -/
@[expose] def lift : S.FreeBraided ⥤ D where
  obj X := projectObj fo X.as
  map := liftMap fo fc
  map_id := liftMap_id fo fc
  map_comp := liftMap_comp fo fc

@[simp]
theorem lift_obj_of (a : S.Obj) : (lift fo fc).obj (of a) = fo a := rfl

@[simp]
theorem lift_obj_tensor (X Y : S.FreeBraided) :
    (lift fo fc).obj (X ⊗ Y) = (lift fo fc).obj X ⊗ (lift fo fc).obj Y := rfl

@[simp]
theorem lift_obj_tensorUnit : (lift fo fc).obj (𝟙_ S.FreeBraided) = 𝟙_ D := rfl

@[simp]
theorem lift_map_coupon (g : S.Coupon) : (lift fo fc).map (coupon g) = fc g := by rfl

@[simp]
theorem lift_map_whiskerLeft (X : S.FreeBraided) {Y₁ Y₂ : S.FreeBraided} (f : Y₁ ⟶ Y₂) :
    (lift fo fc).map (X ◁ f) = (lift fo fc).obj X ◁ (lift fo fc).map f := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem lift_map_whiskerRight {X₁ X₂ : S.FreeBraided} (f : X₁ ⟶ X₂) (Y : S.FreeBraided) :
    (lift fo fc).map (f ▷ Y) = (lift fo fc).map f ▷ (lift fo fc).obj Y := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem lift_map_tensorHom {X₁ Y₁ X₂ Y₂ : S.FreeBraided} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (lift fo fc).map (f ⊗ₘ g) = (lift fo fc).map f ⊗ₘ (lift fo fc).map g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rfl

@[simp]
theorem lift_map_associator_hom (X Y Z : S.FreeBraided) :
    (lift fo fc).map (α_ X Y Z).hom =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).hom := by rfl

@[simp]
theorem lift_map_associator_inv (X Y Z : S.FreeBraided) :
    (lift fo fc).map (α_ X Y Z).inv =
      (α_ ((lift fo fc).obj X) ((lift fo fc).obj Y) ((lift fo fc).obj Z)).inv := by rfl

/- The unitor and forward-braiding lemmas are not `@[simp]`: `Functor.LaxMonoidal.left_unitality`,
`right_unitality` and `Functor.map_braiding` simplify in the compatible direction once `lift_ε`,
`lift_μ` and `lift_δ` are `@[simp]`. -/
theorem lift_map_leftUnitor_hom (X : S.FreeBraided) :
    (lift fo fc).map (λ_ X).hom = (λ_ ((lift fo fc).obj X)).hom := by rfl

theorem lift_map_leftUnitor_inv (X : S.FreeBraided) :
    (lift fo fc).map (λ_ X).inv = (λ_ ((lift fo fc).obj X)).inv := by rfl

theorem lift_map_rightUnitor_hom (X : S.FreeBraided) :
    (lift fo fc).map (ρ_ X).hom = (ρ_ ((lift fo fc).obj X)).hom := by rfl

theorem lift_map_rightUnitor_inv (X : S.FreeBraided) :
    (lift fo fc).map (ρ_ X).inv = (ρ_ ((lift fo fc).obj X)).inv := by rfl

theorem lift_map_braiding_hom (X Y : S.FreeBraided) :
    (lift fo fc).map (β_ X Y).hom = (β_ ((lift fo fc).obj X) ((lift fo fc).obj Y)).hom := by rfl

@[simp]
theorem lift_map_braiding_inv (X Y : S.FreeBraided) :
    (lift fo fc).map (β_ X Y).inv = (β_ ((lift fo fc).obj X) ((lift fo fc).obj Y)).inv := by rfl

instance : (lift fo fc).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor]
        simp
      μIso_hom_natural_right := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor]
        simp
      associativity := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor]
        simp
      left_unitality := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
        simp [lift_map_leftUnitor_hom]
      right_unitality := by
        intros
        dsimp only [Iso.refl_hom, lift_obj_tensor, lift_obj_tensorUnit]
        simp [lift_map_rightUnitor_hom] }

@[simp]
theorem lift_ε : Functor.LaxMonoidal.ε (lift fo fc) = 𝟙 _ := by rfl

@[simp]
theorem lift_η : Functor.OplaxMonoidal.η (lift fo fc) = 𝟙 _ := by rfl

@[simp]
theorem lift_μ (X Y : S.FreeBraided) : Functor.LaxMonoidal.μ (lift fo fc) X Y = 𝟙 _ := by rfl

@[simp]
theorem lift_δ (X Y : S.FreeBraided) : Functor.OplaxMonoidal.δ (lift fo fc) X Y = 𝟙 _ := by rfl

instance : (lift fo fc).Braided where
  braided X Y := by
    dsimp only [lift_obj_tensor]
    simp [lift_map_braiding_hom]

/-- Interpreting a raw monoidal expression via `Hom.toBraided` and `FreeBraided.lift` agrees with
interpreting it directly via `FreeMonoidal.lift`. -/
theorem lift_map_toBraided {X Y : FreeMonoidalCategory S.Obj} (f : FreeMonoidal.Hom X Y) :
    (lift fo fc).map (homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f.toBraided) =
      (FreeMonoidal.lift fo fc).map (FreeMonoidal.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) := by
  induction f with
  | id X => exact (liftMap_id fo fc ⟨X⟩).trans (FreeMonoidal.liftMap_id fo fc ⟨X⟩).symm
  | α_hom X Y Z =>
    exact (lift_map_associator_hom fo fc ⟨X⟩ ⟨Y⟩ ⟨Z⟩).trans
      (FreeMonoidal.lift_map_associator_hom fo fc ⟨X⟩ ⟨Y⟩ ⟨Z⟩).symm
  | α_inv X Y Z =>
    exact (lift_map_associator_inv fo fc ⟨X⟩ ⟨Y⟩ ⟨Z⟩).trans
      (FreeMonoidal.lift_map_associator_inv fo fc ⟨X⟩ ⟨Y⟩ ⟨Z⟩).symm
  | l_hom X =>
    exact (lift_map_leftUnitor_hom fo fc ⟨X⟩).trans
      (FreeMonoidal.lift_map_leftUnitor_hom fo fc ⟨X⟩).symm
  | l_inv X =>
    exact (lift_map_leftUnitor_inv fo fc ⟨X⟩).trans
      (FreeMonoidal.lift_map_leftUnitor_inv fo fc ⟨X⟩).symm
  | ρ_hom X =>
    exact (lift_map_rightUnitor_hom fo fc ⟨X⟩).trans
      (FreeMonoidal.lift_map_rightUnitor_hom fo fc ⟨X⟩).symm
  | ρ_inv X =>
    exact (lift_map_rightUnitor_inv fo fc ⟨X⟩).trans
      (FreeMonoidal.lift_map_rightUnitor_inv fo fc ⟨X⟩).symm
  | coupon g =>
    exact (lift_map_coupon fo fc g).trans (FreeMonoidal.lift_map_coupon fo fc g).symm
  | comp f g hf hg =>
    exact (liftMap_comp fo fc (homMk f.toBraided) (homMk g.toBraided)).trans
      ((congrArg₂ (· ≫ ·) hf hg).trans
        (FreeMonoidal.liftMap_comp fo fc (FreeMonoidal.homMk f) (FreeMonoidal.homMk g)).symm)
  | whiskerLeft X f hf =>
    exact (lift_map_whiskerLeft fo fc ⟨X⟩ (homMk f.toBraided)).trans
      ((congrArg (projectObj fo X ◁ ·) hf).trans
        (FreeMonoidal.lift_map_whiskerLeft fo fc ⟨X⟩ (FreeMonoidal.homMk f)).symm)
  | whiskerRight f Y hf =>
    exact (lift_map_whiskerRight fo fc (homMk f.toBraided) ⟨Y⟩).trans
      ((congrArg (· ▷ projectObj fo Y) hf).trans
        (FreeMonoidal.lift_map_whiskerRight fo fc (FreeMonoidal.homMk f) ⟨Y⟩).symm)
  | tensor f g hf hg =>
    exact (lift_map_tensorHom fo fc (homMk f.toBraided) (homMk g.toBraided)).trans
      ((congrArg₂ (· ⊗ₘ ·) hf hg).trans
        (FreeMonoidal.lift_map_tensorHom fo fc (FreeMonoidal.homMk f) (FreeMonoidal.homMk g)).symm)

/-- Restricting `FreeBraided.lift fo fc` along `FreeMonoidal.toFreeBraided` recovers
`FreeMonoidal.lift fo fc`. -/
theorem toFreeBraided_comp_lift :
    FreeMonoidal.toFreeBraided ⋙ lift fo fc = FreeMonoidal.lift fo fc := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) fun {X Y} f ↦ ?_
  induction f using Quotient.inductionOn with | _ f
  exact heq_of_eq (lift_map_toBraided fo fc f)

end Lift

section Uniqueness

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation from a strong monoidal functor out of `S.FreeBraided` to a
lax monoidal one is determined by its components at the generating objects. -/
theorem natTrans_ext {F G : S.FreeBraided ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β] (h : ∀ a, α.app (of a) = β.app (of a)) :
    α = β := by
  ext ⟨X⟩
  induction X with
  | of a => exact h a
  | unit =>
    rw [← cancel_epi (ε F)]
    exact (NatTrans.IsMonoidal.unit (τ := α)).trans (NatTrans.IsMonoidal.unit (τ := β)).symm
  | tensor X Y hX hY =>
    rw [← cancel_epi (μ F ⟨X⟩ ⟨Y⟩)]
    refine (NatTrans.IsMonoidal.tensor (τ := α) ⟨X⟩ ⟨Y⟩).trans ?_
    refine Eq.trans ?_ (NatTrans.IsMonoidal.tensor (τ := β) ⟨X⟩ ⟨Y⟩).symm
    rw [hX, hY]

variable (F G : S.FreeBraided ⥤ D) [F.Monoidal] [G.Monoidal]
  (e : ∀ a, F.obj (of a) ≅ G.obj (of a))

/-- The isomorphism between the images of a formal tensor word under two strong monoidal functors
out of `S.FreeBraided`, induced by isomorphisms `e` at the generating objects together with the
tensorators and unit comparisons of the two functors. -/
def wordIso : ∀ X : FreeMonoidalCategory S.Obj, F.obj ⟨X⟩ ≅ G.obj ⟨X⟩
  | .of a => e a
  | .unit => (Functor.Monoidal.εIso F).symm ≪≫ Functor.Monoidal.εIso G
  | .tensor X Y =>
    (Functor.Monoidal.μIso F ⟨X⟩ ⟨Y⟩).symm ≪≫ (wordIso X ⊗ᵢ wordIso Y) ≪≫
      Functor.Monoidal.μIso G ⟨X⟩ ⟨Y⟩

@[simp]
theorem wordIso_of (a : S.Obj) : wordIso F G e (of a).as = e a := by rfl

@[simp]
theorem wordIso_tensorUnit_hom : (wordIso F G e (𝟙_ S.FreeBraided).as).hom = η F ≫ ε G := by rfl

@[simp]
theorem wordIso_tensor_hom (X Y : S.FreeBraided) :
    (wordIso F G e (X ⊗ Y).as).hom =
      δ F X Y ≫ ((wordIso F G e X.as).hom ⊗ₘ (wordIso F G e Y.as).hom) ≫ μ G X Y := by rfl

end Uniqueness

section BraidedUniqueness

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  {F G : S.FreeBraided ⥤ D} [F.Braided] [G.Braided]
  {e : ∀ a, F.obj (of a) ≅ G.obj (of a)}

/- Composites with tensors of morphisms are folded into a single tensor of composites, so that
the tensorators cancel inside each tensor factor. -/
attribute [local simp] whiskerLeft_comp_tensorHom whiskerLeft_comp_tensorHom_assoc
  whiskerRight_comp_tensorHom whiskerRight_comp_tensorHom_assoc tensorHom_comp_whiskerLeft
  tensorHom_comp_whiskerLeft_assoc tensorHom_comp_whiskerRight tensorHom_comp_whiskerRight_assoc

/-- The isomorphisms `wordIso F G e` between two strong braided functors are natural with respect
to all morphisms of `S.FreeBraided` as soon as they commute with every coupon. -/
theorem map_comp_wordIso_hom
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))
    {X Y : S.FreeBraided} (f : X ⟶ Y) :
    F.map f ≫ (wordIso F G e Y.as).hom = (wordIso F G e X.as).hom ≫ G.map f := by
  induction f using Hom.inductionOn with
  | id X => simp
  -- Cancel the tensorators of `F` on the left and those of `G` on the right; `simp` then reduces
  -- both sides to the naturality of the structural isomorphism.
  | α_hom X Y Z =>
    rw [← cancel_epi (μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z),
      ← cancel_mono (δ G X (Y ⊗ Z) ≫ G.obj X ◁ δ G Y Z)]
    simp [← Functor.OplaxMonoidal.associativity]
  | α_inv X Y Z =>
    rw [← cancel_epi (F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z)),
      ← cancel_mono (δ G (X ⊗ Y) Z ≫ δ G X Y ▷ G.obj Z)]
    simp [← Functor.OplaxMonoidal.associativity_inv]
  | l_hom X =>
    rw [← cancel_epi (ε F ▷ F.obj X ≫ μ F (𝟙_ _) X)]
    simp
    simp [tensorHom_def']
  | l_inv X =>
    rw [← cancel_mono (δ G (𝟙_ _) X ≫ η G ▷ G.obj X)]
    simp
    simp [MonoidalCategory.tensorHom_def, ← Functor.OplaxMonoidal.left_unitality]
  | ρ_hom X =>
    rw [← cancel_epi (F.obj X ◁ ε F ≫ μ F X (𝟙_ _))]
    simp
    simp [MonoidalCategory.tensorHom_def]
  | ρ_inv X =>
    rw [← cancel_mono (δ G X (𝟙_ _) ≫ G.obj X ◁ η G)]
    simp
    simp [tensorHom_def', ← Functor.OplaxMonoidal.right_unitality]
  -- For braidings, naturality of `β_` cancels the tensorators of `F` and `G`; the inverse braiding
  -- case follows by cancelling `(β_ X Y).hom` on both sides.
  | β_hom X Y =>
    simp only [Functor.map_braiding, wordIso_tensor_hom, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, BraidedCategory.braiding_naturality_assoc]
  | β_inv X Y =>
    have hβ : F.map (β_ X Y).hom ≫ (wordIso F G e (Y ⊗ X).as).hom =
        (wordIso F G e (X ⊗ Y).as).hom ≫ G.map (β_ X Y).hom := by
      simp only [Functor.map_braiding, wordIso_tensor_hom, Category.assoc,
        Functor.Monoidal.μ_δ_assoc, BraidedCategory.braiding_naturality_assoc]
    rw [← cancel_epi (F.map (β_ X Y).hom), ← cancel_mono (G.map (β_ X Y).hom)]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp,
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id, hβ]
  | coupon g => exact he g
  | comp _ _ hf hg =>
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg, reassoc_of% hf]
  | whiskerLeft X _ hf =>
    simp only [wordIso_tensor_hom, Functor.Monoidal.map_whiskerLeft, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerLeft_comp_tensorHom_assoc,
      tensorHom_comp_whiskerLeft_assoc, hf]
  | whiskerRight _ X hf =>
    simp only [wordIso_tensor_hom, Functor.Monoidal.map_whiskerRight, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerRight_comp_tensorHom_assoc,
      tensorHom_comp_whiskerRight_assoc, hf]

/-- Two strong braided functors out of `S.FreeBraided` that agree up to isomorphisms `e` on the
generating objects, compatibly with every coupon, are isomorphic by a monoidal natural isomorphism
extending `e`. -/
def monoidalNatIso
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g)) :
    F ≅ G :=
  NatIso.ofComponents (fun X ↦ wordIso F G e X.as) fun f ↦ map_comp_wordIso_hom he f

variable (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
  (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeBraided) :
    (monoidalNatIso he).hom.app X = (wordIso F G e X.as).hom := by rfl

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso he).hom.app (of a) = (e a).hom := by rfl

instance : NatTrans.IsMonoidal (monoidalNatIso he).hom where
  unit := by
    rw [monoidalNatIso_hom_app, wordIso_tensorUnit_hom, Functor.Monoidal.ε_η_assoc]
  tensor X Y := by
    rw [monoidalNatIso_hom_app, wordIso_tensor_hom, Functor.Monoidal.μ_δ_assoc,
      monoidalNatIso_hom_app, monoidalNatIso_hom_app]

end BraidedUniqueness

section CrossingExp

/-- Raw crossing-exponent sum of a formal braided morphism: positive crossings of words `X` and `Y`
contribute `X.length * Y.length`, negative crossings contribute its negation, and structural
monoidal maps and coupons contribute `0`. -/
@[expose] def Hom.crossingExp : ∀ {X Y : FreeMonoidalCategory S.Obj}, Hom X Y → ℤ
  | _, _, .id _ => 0
  | _, _, .α_hom _ _ _ => 0
  | _, _, .α_inv _ _ _ => 0
  | _, _, .l_hom _ => 0
  | _, _, .l_inv _ => 0
  | _, _, .ρ_hom _ => 0
  | _, _, .ρ_inv _ => 0
  | _, _, .β_hom X Y => (X.length : ℤ) * (Y.length : ℤ)
  | _, _, .β_inv X Y => -((X.length : ℤ) * (Y.length : ℤ))
  | _, _, .coupon _ => 0
  | _, _, .comp f g => f.crossingExp + g.crossingExp
  | _, _, .whiskerLeft _ f => f.crossingExp
  | _, _, .whiskerRight f _ => f.crossingExp
  | _, _, .tensor f g => f.crossingExp + g.crossingExp

/-- When every coupon preserves port length, every raw braided morphism preserves port length. -/
theorem Hom.length_eq (hlen : ∀ g : S.Coupon, (S.src g).length = (S.tgt g).length)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    X.length = Y.length := by
  induction f with
  | id => rfl
  | α_hom => simp [Nat.add_assoc]
  | α_inv => simp [Nat.add_assoc]
  | l_hom => simp
  | l_inv => simp
  | ρ_hom => simp
  | ρ_inv => simp
  | β_hom => simp [Nat.add_comm]
  | β_inv => simp [Nat.add_comm]
  | coupon g => exact hlen g
  | comp _ _ hf hg => exact hf.trans hg
  | whiskerLeft _ _ hf => simp [hf]
  | whiskerRight _ _ hf => simp [hf]
  | tensor _ _ hf hg => simp [hf, hg]

/-- When every coupon preserves port length, every morphism of `S.FreeBraided` preserves port
length. -/
theorem length_eq_of_hom (hlen : ∀ g : S.Coupon, (S.src g).length = (S.tgt g).length)
    {X Y : S.FreeBraided} (f : X ⟶ Y) :
    X.as.length = Y.as.length := by
  induction f using Quotient.inductionOn with | _ f
  exact f.length_eq hlen

/-- In a port-length-preserving signature, words of distinct port lengths have no morphisms between
them in `S.FreeBraided`. -/
theorem isEmpty_hom_of_length_ne (hlen : ∀ g : S.Coupon, (S.src g).length = (S.tgt g).length)
    {X Y : S.FreeBraided} (hne : X.as.length ≠ Y.as.length) :
    IsEmpty (X ⟶ Y) :=
  ⟨fun f ↦ hne (length_eq_of_hom hlen f)⟩

/-- When every coupon preserves port length, the crossing-exponent sum respects all axioms of a
braided monoidal category. -/
theorem HomEquiv.crossingExp_eq (hlen : ∀ g : S.Coupon, (S.src g).length = (S.tgt g).length)
    {X Y : FreeMonoidalCategory S.Obj} {f g : Hom X Y} (h : HomEquiv f g) :
    f.crossingExp = g.crossingExp := by
  induction h with
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp _ _ ih₁ ih₂ => simp only [Hom.crossingExp, ih₁, ih₂]
  | whiskerLeft _ _ _ _ ih => exact ih
  | whiskerRight _ _ _ _ ih => exact ih
  | tensor _ _ ih₁ ih₂ => simp only [Hom.crossingExp, ih₁, ih₂]
  | tensorHom_def => rfl
  | comp_id => dsimp only [Hom.crossingExp]; omega
  | id_comp => dsimp only [Hom.crossingExp]; omega
  | assoc => dsimp only [Hom.crossingExp]; omega
  | id_tensorHom_id => rfl
  | tensorHom_comp_tensorHom => dsimp only [Hom.crossingExp]; omega
  | whiskerLeft_id => rfl
  | id_whiskerRight => rfl
  | α_hom_inv => rfl
  | α_inv_hom => rfl
  | associator_naturality => dsimp only [Hom.crossingExp]; omega
  | ρ_hom_inv => rfl
  | ρ_inv_hom => rfl
  | ρ_naturality => dsimp only [Hom.crossingExp]; omega
  | l_hom_inv => rfl
  | l_inv_hom => rfl
  | l_naturality => dsimp only [Hom.crossingExp]; omega
  | pentagon => rfl
  | triangle => rfl
  | β_hom_inv => dsimp only [Hom.crossingExp]; omega
  | β_inv_hom => dsimp only [Hom.crossingExp]; omega
  | braiding_naturality_right X f =>
    dsimp only [Hom.crossingExp]; rw [f.length_eq hlen]; omega
  | braiding_naturality_left f Z =>
    dsimp only [Hom.crossingExp]; rw [f.length_eq hlen]; omega
  | hexagon_forward =>
    dsimp only [Hom.crossingExp]
    rw [tensor_eq_tensor, length_tensorObj, Int.natCast_add, Int.mul_add]; omega
  | hexagon_reverse =>
    dsimp only [Hom.crossingExp]
    rw [tensor_eq_tensor, length_tensorObj, Int.natCast_add, Int.add_mul]; omega

/-- The crossing-exponent sum of a morphism in `S.FreeBraided`, defined whenever every coupon of
`S` preserves port length. -/
def crossingExp (hlen : ∀ g : S.Coupon, (S.src g).length = (S.tgt g).length)
    {X Y : S.FreeBraided} (f : X ⟶ Y) : ℤ :=
  Quotient.lift Hom.crossingExp (fun _ _ h ↦ HomEquiv.crossingExp_eq hlen h) f

section CrossingExpLemmas

variable (hlen : ∀ g : S.Coupon, (S.src g).length = (S.tgt g).length)

@[simp]
theorem crossingExp_homMk {X Y : S.FreeBraided} (f : Hom X.as Y.as) :
    crossingExp hlen (homMk f) = f.crossingExp := (rfl)

@[simp]
theorem crossingExp_id (X : S.FreeBraided) : crossingExp hlen (𝟙 X) = 0 := (rfl)

@[simp]
theorem crossingExp_comp {X Y Z : S.FreeBraided} (f : X ⟶ Y) (g : Y ⟶ Z) :
    crossingExp hlen (f ≫ g) = crossingExp hlen f + crossingExp hlen g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rfl

@[simp]
theorem crossingExp_whiskerLeft (X : S.FreeBraided) {Y Z : S.FreeBraided} (f : Y ⟶ Z) :
    crossingExp hlen (X ◁ f) = crossingExp hlen f := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem crossingExp_whiskerRight {X Y : S.FreeBraided} (f : X ⟶ Y) (Z : S.FreeBraided) :
    crossingExp hlen (f ▷ Z) = crossingExp hlen f := by
  induction f using Quotient.inductionOn
  rfl

@[simp]
theorem crossingExp_tensorHom {W X Y Z : S.FreeBraided} (f : W ⟶ Y) (g : X ⟶ Z) :
    crossingExp hlen (f ⊗ₘ g) = crossingExp hlen f + crossingExp hlen g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rfl

@[simp]
theorem crossingExp_associator_hom (X Y Z : S.FreeBraided) :
    crossingExp hlen (α_ X Y Z).hom = 0 := (rfl)

@[simp]
theorem crossingExp_associator_inv (X Y Z : S.FreeBraided) :
    crossingExp hlen (α_ X Y Z).inv = 0 := (rfl)

@[simp]
theorem crossingExp_leftUnitor_hom (X : S.FreeBraided) :
    crossingExp hlen (λ_ X).hom = 0 := (rfl)

@[simp]
theorem crossingExp_leftUnitor_inv (X : S.FreeBraided) :
    crossingExp hlen (λ_ X).inv = 0 := (rfl)

@[simp]
theorem crossingExp_rightUnitor_hom (X : S.FreeBraided) :
    crossingExp hlen (ρ_ X).hom = 0 := (rfl)

@[simp]
theorem crossingExp_rightUnitor_inv (X : S.FreeBraided) :
    crossingExp hlen (ρ_ X).inv = 0 := (rfl)

@[simp]
theorem crossingExp_coupon (g : S.Coupon) : crossingExp hlen (coupon g) = 0 := (rfl)

@[simp]
theorem crossingExp_braiding_hom (X Y : S.FreeBraided) :
    crossingExp hlen (β_ X Y).hom = (X.as.length : ℤ) * (Y.as.length : ℤ) := (rfl)

@[simp]
theorem crossingExp_braiding_inv (X Y : S.FreeBraided) :
    crossingExp hlen (β_ X Y).inv = -((X.as.length : ℤ) * (Y.as.length : ℤ)) := (rfl)

end CrossingExpLemmas

/-- In a port-length-preserving signature, composing two positive crossings of generating objects
never yields the identity morphism, so the braiding of `S.FreeBraided` does not satisfy the
symmetry axiom whenever `S.Obj` is nonempty. -/
theorem braiding_of_comp_braiding_of_ne_id
    (hlen : ∀ g : S.Coupon, (S.src g).length = (S.tgt g).length) (a b : S.Obj) :
    (β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom ≠ 𝟙 (of a ⊗ of b) := by
  intro h
  have hexp := congrArg (crossingExp hlen) h
  simp [of] at hexp

/-- In a coupon-free signature, two positive crossings of generating objects never cancel to the
identity in `S.FreeBraided`. -/
theorem braiding_of_comp_braiding_of_ne_id_of_isEmpty [IsEmpty S.Coupon] (a b : S.Obj) :
    (β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom ≠ 𝟙 (of a ⊗ of b) :=
  braiding_of_comp_braiding_of_ne_id (fun g ↦ isEmptyElim g) a b

end CrossingExp

end FreeBraided

end TauCeti.TensorSignature
