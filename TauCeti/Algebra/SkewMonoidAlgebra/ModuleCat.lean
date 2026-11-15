/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.Algebra.SkewMonoidAlgebra.EquivariantModule
public import TauCeti.Algebra.SkewMonoidAlgebra.MonoidAlgebra
public import TauCeti.Algebra.SkewMonoidAlgebra.Opposite

/-!
# Categorical equivalences for modules over skew monoid and skew group algebras

Let a monoid `G` act on a ring `A` by ring endomorphisms (`MulSemiringAction G A`). This file
bundles left `A`-modules carrying a semilinear `G`-action (`SMulDistribClass G A`) and their
`A`-linear, `G`-equivariant maps into the preadditive concrete category
`TauCeti.EquivariantModuleCat A G`, and establishes three categorical equivalences:

1. **Left modules (`TauCeti.EquivariantModuleCat.equivalenceModuleSkewMonoidAlgebra`):**
   `EquivariantModuleCat.{w} A G ≌ ModuleCat.{w} (SkewMonoidAlgebra A G)`.
   The forward functor `toModuleSkewMonoidAlgebra` sends `M` to `EquivariantAsModule A G M`, where
   `single g a` acts by `m ↦ a • (g • m)`; the inverse functor `ofModuleSkewMonoidAlgebra` sends a
   left `SkewMonoidAlgebra A G`-module `N` to `EquivariantOfModule A G N`, where `a : A` acts via
   `single 1 a` and `g : G` acts via `single g 1`. Both functors are additive, and `k`-linear when
   `A` is an algebra over a field `k` with `k`-linear `G`-action.

2. **Right modules via the opposite algebra
   (`TauCeti.EquivariantModuleCat.rightModuleSkewMonoidAlgebraEquivalence`):**
   When `G` is a group, right modules over `SkewMonoidAlgebra A G` — i.e., left modules over
   `(SkewMonoidAlgebra A G)ᵐᵒᵖ` — are equivalent to `EquivariantModuleCat.{w} Aᵐᵒᵖ G` by composing
   restriction of scalars along `(TauCeti.skewMonoidAlgebraOpRingEquiv A G).symm` with the inverse
   left-module equivalence over `Aᵐᵒᵖ`. Concretely, `op a : Aᵐᵒᵖ` acts on `n` by `op (single 1 a)`
   (right multiplication by `single 1 a`) and `g : G` acts by `op (single g⁻¹ 1)` (right
   multiplication by `single g⁻¹ 1`).

3. **Comparison with `Rep k G` for trivial actions
   (`TauCeti.EquivariantModuleCat.repEquivalence` and
   `TauCeti.EquivariantModuleCat.toRepCompToModuleMonoidAlgebraIso`):**
   When `A = k` is a commutative ring and `SMulCommClass G k k` holds, the `G`-action on `k` is
   trivial (`TauCeti.smul_eq_self_of_smulCommClass_self`), `EquivariantModuleCat.{w} k G` is
   equivalent to `Rep.{w} k G`, and `toModuleSkewMonoidAlgebra` commutes up to natural isomorphism
   with `Rep.toModuleMonoidAlgebra` along `TauCeti.skewMonoidAlgebraSelfAlgEquiv k G`.

## Main definitions

* `TauCeti.EquivariantModuleCat`: the category of `G`-equivariant left `A`-modules.
* `TauCeti.EquivariantModuleCat.toModuleSkewMonoidAlgebra`,
  `TauCeti.EquivariantModuleCat.ofModuleSkewMonoidAlgebra`,
  `TauCeti.EquivariantModuleCat.equivalenceModuleSkewMonoidAlgebra`: the left-module equivalence.
* `TauCeti.EquivariantModuleCat.rightModuleToEquivariant`,
  `TauCeti.EquivariantModuleCat.rightModuleSkewMonoidAlgebraEquivalence`: the right-module
  equivalence `ModuleCat (SkewMonoidAlgebra A G)ᵐᵒᵖ ≌ EquivariantModuleCat Aᵐᵒᵖ G` for a group `G`.
* `TauCeti.EquivariantModuleCat.repEquivalence`,
  `TauCeti.EquivariantModuleCat.toRepCompToModuleMonoidAlgebraIso`: comparison with `Rep k G` and
  `ModuleCat k[G]` when `A = k`.
-/

public noncomputable section

open CategoryTheory

universe w u v u₀

namespace TauCeti

/-- The category of `G`-equivariant left `A`-modules: `A`-modules carrying a distributive `G`-action
satisfying `g • (a • m) = (g • a) • (g • m)` (`SMulDistribClass G A`), with `A`-linear,
`G`-equivariant morphisms (`TauCeti.EquivariantLinearMap`). -/
structure EquivariantModuleCat (A : Type u) (G : Type v) [Ring A] [Monoid G]
    [MulSemiringAction G A] where
  /-- The underlying carrier type. -/
  carrier : Type w
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module A carrier]
  [isDistribMulAction : DistribMulAction G carrier]
  [isSMulDistribClass : SMulDistribClass G A carrier]

namespace EquivariantModuleCat

section Category

variable {A : Type u} {G : Type v} [Ring A] [Monoid G] [MulSemiringAction G A]

attribute [instance] isAddCommGroup isModule isDistribMulAction isSMulDistribClass

instance : CoeSort (EquivariantModuleCat.{w} A G) (Type w) :=
  ⟨carrier⟩

attribute [coe] carrier

variable (A G) in
/-- Bundle a type carrying `[AddCommGroup M] [Module A M] [DistribMulAction G M]
[SMulDistribClass G A M]` as an object of `EquivariantModuleCat A G`. -/
abbrev of (M : Type w) [AddCommGroup M] [Module A M] [DistribMulAction G M]
    [SMulDistribClass G A M] : EquivariantModuleCat.{w} A G :=
  ⟨M⟩

@[simp]
theorem coe_of (M : Type w) [AddCommGroup M] [Module A M] [DistribMulAction G M]
    [SMulDistribClass G A M] : (of A G M : Type w) = M :=
  (rfl)

/-- The canonical equivariant `A`-module `A` itself, with `A` acting by left multiplication and `G`
acting through `MulSemiringAction G A` (`TauCeti.smulDistribClass_self`). -/
abbrev regular (A : Type u) (G : Type v) [Ring A] [Monoid G] [MulSemiringAction G A] :
    EquivariantModuleCat.{u} A G :=
  of A G A

/-- Morphisms in `EquivariantModuleCat A G`, wrapping `TauCeti.EquivariantLinearMap`. -/
@[ext]
structure Hom (X Y : EquivariantModuleCat.{w} A G) where
  /-- The underlying `A`-linear, `G`-equivariant map. -/
  hom' : EquivariantLinearMap A G X Y

instance : Category (EquivariantModuleCat.{w} A G) where
  Hom := Hom
  id _ := ⟨EquivariantLinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (EquivariantModuleCat.{w} A G)
    (fun X Y ↦ EquivariantLinearMap A G X Y) where
  hom := Hom.hom'
  ofHom := Hom.mk
  id_apply x := EquivariantLinearMap.id_apply x
  comp_apply f g x := EquivariantLinearMap.comp_apply g.hom' f.hom' x

/-- Extract the underlying `EquivariantLinearMap` from a morphism in `EquivariantModuleCat A G`. -/
abbrev Hom.hom {X Y : EquivariantModuleCat.{w} A G} (f : Hom X Y) :
    EquivariantLinearMap A G X Y :=
  ConcreteCategory.hom (C := EquivariantModuleCat.{w} A G) f

/-- Bundle an `EquivariantLinearMap` as a morphism in `EquivariantModuleCat A G`. -/
abbrev ofHom {M M' : Type w} [AddCommGroup M] [Module A M] [DistribMulAction G M]
    [SMulDistribClass G A M] [AddCommGroup M'] [Module A M'] [DistribMulAction G M']
    [SMulDistribClass G A M'] (f : EquivariantLinearMap A G M M') :
    of A G M ⟶ of A G M' :=
  ConcreteCategory.ofHom (C := EquivariantModuleCat.{w} A G) f

theorem hom_ext {X Y : EquivariantModuleCat.{w} A G} {f g : X ⟶ Y} (h : f.hom = g.hom) :
    f = g :=
  Hom.ext h

@[ext]
theorem hom_ext' {X Y : EquivariantModuleCat.{w} A G} {f g : X ⟶ Y}
    (h : ∀ x : X, f.hom x = g.hom x) : f = g :=
  hom_ext (EquivariantLinearMap.ext h)

theorem hom_injective {X Y : EquivariantModuleCat.{w} A G} :
    Function.Injective (Hom.hom : (X ⟶ Y) → EquivariantLinearMap A G X Y) :=
  fun _ _ ↦ hom_ext

@[simp]
theorem hom_id (X : EquivariantModuleCat.{w} A G) :
    (𝟙 X : X ⟶ X).hom = EquivariantLinearMap.id :=
  (rfl)

@[simp]
theorem hom_comp {X Y Z : EquivariantModuleCat.{w} A G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  (rfl)

theorem hom_ofHom {M M' : Type w} [AddCommGroup M] [Module A M] [DistribMulAction G M]
    [SMulDistribClass G A M] [AddCommGroup M'] [Module A M'] [DistribMulAction G M']
    [SMulDistribClass G A M'] (f : EquivariantLinearMap A G M M') :
    (ofHom f).hom = f :=
  (rfl)

theorem ofHom_hom {X Y : EquivariantModuleCat.{w} A G} (f : X ⟶ Y) :
    ConcreteCategory.ofHom (C := EquivariantModuleCat.{w} A G) f.hom = f :=
  (rfl)

@[simp]
theorem ofHom_id {M : Type w} [AddCommGroup M] [Module A M] [DistribMulAction G M]
    [SMulDistribClass G A M] :
    ofHom (EquivariantLinearMap.id : EquivariantLinearMap A G M M) = 𝟙 (of A G M) :=
  (rfl)

@[simp]
theorem ofHom_comp {M M' M'' : Type w} [AddCommGroup M] [Module A M] [DistribMulAction G M]
    [SMulDistribClass G A M] [AddCommGroup M'] [Module A M'] [DistribMulAction G M']
    [SMulDistribClass G A M'] [AddCommGroup M''] [Module A M''] [DistribMulAction G M'']
    [SMulDistribClass G A M''] (f : EquivariantLinearMap A G M M')
    (g : EquivariantLinearMap A G M' M'') :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  (rfl)

/-- Build an isomorphism in `EquivariantModuleCat A G` from an `EquivariantLinearEquiv`. -/
def mkIso {X Y : EquivariantModuleCat.{w} A G} (e : EquivariantLinearEquiv A G X Y) : X ≅ Y where
  hom := ConcreteCategory.ofHom e.toEquivariantLinearMap
  inv := ConcreteCategory.ofHom e.symm.toEquivariantLinearMap
  hom_inv_id := by
    ext x
    simp
  inv_hom_id := by
    ext y
    simp

@[simp]
theorem mkIso_hom_hom {X Y : EquivariantModuleCat.{w} A G}
    (e : EquivariantLinearEquiv A G X Y) :
    (mkIso e).hom.hom = e.toEquivariantLinearMap :=
  (rfl)

@[simp]
theorem mkIso_inv_hom {X Y : EquivariantModuleCat.{w} A G}
    (e : EquivariantLinearEquiv A G X Y) :
    (mkIso e).inv.hom = e.symm.toEquivariantLinearMap :=
  (rfl)

instance {X Y : EquivariantModuleCat.{w} A G} : Zero (X ⟶ Y) :=
  ⟨ConcreteCategory.ofHom 0⟩

instance {X Y : EquivariantModuleCat.{w} A G} : Add (X ⟶ Y) :=
  ⟨fun f g ↦ ConcreteCategory.ofHom (f.hom + g.hom)⟩

instance {X Y : EquivariantModuleCat.{w} A G} : Neg (X ⟶ Y) :=
  ⟨fun f ↦ ConcreteCategory.ofHom (-f.hom)⟩

instance {X Y : EquivariantModuleCat.{w} A G} : Sub (X ⟶ Y) :=
  ⟨fun f g ↦ ConcreteCategory.ofHom (f.hom - g.hom)⟩

instance {X Y : EquivariantModuleCat.{w} A G} : SMul ℕ (X ⟶ Y) :=
  ⟨fun n f ↦ ConcreteCategory.ofHom (n • f.hom)⟩

instance {X Y : EquivariantModuleCat.{w} A G} : SMul ℤ (X ⟶ Y) :=
  ⟨fun z f ↦ ConcreteCategory.ofHom (z • f.hom)⟩

@[simp]
theorem hom_zero (X Y : EquivariantModuleCat.{w} A G) : (0 : X ⟶ Y).hom = 0 :=
  (rfl)

@[simp]
theorem hom_add {X Y : EquivariantModuleCat.{w} A G} (f g : X ⟶ Y) :
    (f + g).hom = f.hom + g.hom :=
  (rfl)

@[simp]
theorem hom_neg {X Y : EquivariantModuleCat.{w} A G} (f : X ⟶ Y) : (-f).hom = -f.hom :=
  (rfl)

@[simp]
theorem hom_sub {X Y : EquivariantModuleCat.{w} A G} (f g : X ⟶ Y) :
    (f - g).hom = f.hom - g.hom :=
  (rfl)

theorem hom_nsmul {X Y : EquivariantModuleCat.{w} A G} (n : ℕ) (f : X ⟶ Y) :
    (n • f).hom = n • f.hom :=
  (rfl)

theorem hom_zsmul {X Y : EquivariantModuleCat.{w} A G} (z : ℤ) (f : X ⟶ Y) :
    (z • f).hom = z • f.hom :=
  (rfl)

instance {X Y : EquivariantModuleCat.{w} A G} : AddCommGroup (X ⟶ Y) :=
  hom_injective.addCommGroup Hom.hom (hom_zero X Y) hom_add hom_neg hom_sub
    (fun f n ↦ hom_nsmul n f) (fun f z ↦ hom_zsmul z f)

instance : Preadditive (EquivariantModuleCat.{w} A G) where
  add_comp _ _ _ _ _ _ := by ext x; simp
  comp_add _ _ _ _ _ _ := by ext x; simp

/-- Forget the `G`-action on an equivariant `A`-module to obtain its underlying `A`-module. -/
instance : HasForget₂ (EquivariantModuleCat.{w} A G) (ModuleCat.{w} A) where
  forget₂ :=
    { obj X := ModuleCat.of A X
      map f := ModuleCat.ofHom f.hom.toLinearMap }

@[simp]
theorem forget₂_obj (X : EquivariantModuleCat.{w} A G) :
    (forget₂ (EquivariantModuleCat.{w} A G) (ModuleCat.{w} A)).obj X = ModuleCat.of A X :=
  (rfl)

@[simp]
theorem forget₂_map_hom {X Y : EquivariantModuleCat.{w} A G} (f : X ⟶ Y) :
    ((forget₂ (EquivariantModuleCat.{w} A G) (ModuleCat.{w} A)).map f).hom = f.hom.toLinearMap :=
  (rfl)

instance : (forget₂ (EquivariantModuleCat.{w} A G) (ModuleCat.{w} A)).Faithful where
  map_injective h := by
    ext x
    exact congrArg (fun φ : ModuleCat.of A _ ⟶ ModuleCat.of A _ ↦ φ.hom x) h

instance : (forget₂ (EquivariantModuleCat.{w} A G) (ModuleCat.{w} A)).Additive where
  map_add := by
    intros
    ext x
    simp

end Category

section LinearOverField

variable {k : Type u₀} [Field k] {A : Type u} {G : Type v} [Ring A] [Algebra k A]
  [Monoid G] [MulSemiringAction G A] [SMulCommClass G k A]

instance {X Y : EquivariantModuleCat.{w} A G} : SMul k (X ⟶ Y) where
  smul r f := ConcreteCategory.ofHom
    { toFun x := algebraMap k A r • f.hom x
      map_add' x y := by rw [map_add, smul_add]
      map_smul' a x := by
        rw [RingHom.id_apply, map_smul, ← mul_smul, Algebra.commutes, mul_smul]
      map_smul_group' g x := by
        rw [LinearMap.coe_mk, AddHom.coe_mk, f.hom.map_smul_group,
          smul_distrib_smul g (algebraMap k A r) (f.hom x), smul_algebraMap] }

@[simp]
theorem hom_smul_apply {X Y : EquivariantModuleCat.{w} A G} (r : k) (f : X ⟶ Y) (x : X) :
    (r • f).hom x = algebraMap k A r • f.hom x :=
  congrFun (EquivariantLinearMap.coe_mk _ _) x

instance {X Y : EquivariantModuleCat.{w} A G} : Module k (X ⟶ Y) where
  one_smul f := by ext x; simp
  mul_smul r s f := by ext x; simp [mul_smul]
  smul_zero r := by ext x; simp
  smul_add r f g := by ext x; simp [smul_add]
  add_smul r s f := by ext x; simp [add_smul]
  zero_smul f := by ext x; simp

/-- When `A` is an algebra over a field `k` with `k`-linear `G`-action, `EquivariantModuleCat A G`
is a `k`-linear category. As in `ModuleCat.linearOverField`, `k` is a field so this instance cannot
collide with the `Linear ℕ` and `Linear ℤ` instances from `Preadditive`. -/
instance : Linear k (EquivariantModuleCat.{w} A G) where
  smul_comp _ _ _ r f g := by ext x; simp
  comp_smul _ _ _ f r g := by ext x; simp

end LinearOverField

/-! ### Left-module equivalence: `EquivariantModuleCat A G ≌ ModuleCat (SkewMonoidAlgebra A G)` -/

section LeftEquivalence

variable {A : Type u} {G : Type v} [Ring A] [Monoid G] [MulSemiringAction G A]

-- `@[expose]` is load-bearing because the statements of `toModuleSkewMonoidAlgebra_map` and the
-- elementwise action formulas speak of morphisms and elements on
-- `(toModuleSkewMonoidAlgebra A G).obj X`.
variable (A G) in
/-- **Forward functor:** convert a `G`-equivariant left `A`-module `X` into the left
`SkewMonoidAlgebra A G`-module `EquivariantAsModule A G X`, where `single g a` acts by
`x ↦ a • (g • x)`. -/
@[expose]
def toModuleSkewMonoidAlgebra :
    EquivariantModuleCat.{w} A G ⥤ ModuleCat.{w} (SkewMonoidAlgebra A G) where
  obj X := ModuleCat.of (SkewMonoidAlgebra A G) (EquivariantAsModule A G X)
  map {X Y} f := ModuleCat.ofHom (EquivariantLinearMap.equivLinearMapAsModule A G X Y f.hom)
  map_id _ := by simp
  map_comp _ _ := by simp

@[simp]
theorem toModuleSkewMonoidAlgebra_obj (X : EquivariantModuleCat.{w} A G) :
    (toModuleSkewMonoidAlgebra A G).obj X =
      ModuleCat.of (SkewMonoidAlgebra A G) (EquivariantAsModule A G X) :=
  (rfl)

theorem toModuleSkewMonoidAlgebra_map {X Y : EquivariantModuleCat.{w} A G} (f : X ⟶ Y) :
    (toModuleSkewMonoidAlgebra A G).map f =
      ModuleCat.ofHom (EquivariantLinearMap.equivLinearMapAsModule A G X Y f.hom) :=
  (rfl)

@[simp]
theorem toModuleSkewMonoidAlgebra_map_hom_apply {X Y : EquivariantModuleCat.{w} A G}
    (f : X ⟶ Y) (x : (toModuleSkewMonoidAlgebra A G).obj X) :
    ((toModuleSkewMonoidAlgebra A G).map f).hom x = EquivariantAsModule.of (f.hom x.val) :=
  EquivariantLinearMap.equivLinearMapAsModule_apply f.hom x

theorem toModuleSkewMonoidAlgebra_map_hom_apply_of {X Y : EquivariantModuleCat.{w} A G}
    (f : X ⟶ Y) (x : X) :
    ((toModuleSkewMonoidAlgebra A G).map f).hom (EquivariantAsModule.of x) =
      EquivariantAsModule.of (f.hom x) :=
  EquivariantLinearMap.equivLinearMapAsModule_apply f.hom (EquivariantAsModule.of x)

variable (A G) in
instance : (toModuleSkewMonoidAlgebra.{w} A G).Additive where
  map_add {X Y f g} := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ EquivariantAsModule.ext ?_)
    rw [ModuleCat.hom_add, LinearMap.add_apply, toModuleSkewMonoidAlgebra_map_hom_apply,
      toModuleSkewMonoidAlgebra_map_hom_apply, toModuleSkewMonoidAlgebra_map_hom_apply,
      hom_add, EquivariantLinearMap.add_apply]
    exact (EquivariantAsModule.val_add _ _).symm

theorem toModuleSkewMonoidAlgebra_obj_single_smul (X : EquivariantModuleCat.{w} A G)
    (g : G) (a : A) (x : X) :
    SkewMonoidAlgebra.single g a •
      (EquivariantAsModule.of x : (toModuleSkewMonoidAlgebra A G).obj X) =
      EquivariantAsModule.of (a • (g • x)) :=
  EquivariantAsModule.single_smul_of g a x

/-- On the canonical equivariant module `regular A G = A`, `(single g 1)` applied after
`(single 1 a)` to `1 ∈ A` produces `g • a`, matching `(single g 1 * single 1 a) • 1 =
single g (g • a) • 1`. -/
theorem toModuleSkewMonoidAlgebra_regular_of_smul_singleOneRingHom_one (g : G) (a : A) :
    SkewMonoidAlgebra.of A G g •
      (SkewMonoidAlgebra.singleOneRingHom (G := G) a •
        (EquivariantAsModule.of (1 : A) :
          (toModuleSkewMonoidAlgebra A G).obj (regular A G))) =
      EquivariantAsModule.of (g • a) :=
  EquivariantAsModule.of_smul_singleOneRingHom_smul_one g a

-- `@[expose]` is load-bearing because the statements of `ofModuleSkewMonoidAlgebra_map` and the
-- elementwise action lemmas depend on `(ofModuleSkewMonoidAlgebra A G).obj N` reducing.
variable (A G) in
/-- **Inverse functor:** convert a left `SkewMonoidAlgebra A G`-module `N` into the `G`-equivariant
left `A`-module `EquivariantOfModule A G N`, where `a : A` acts via `single 1 a` and `g : G` acts
via `single g 1`. -/
@[expose]
def ofModuleSkewMonoidAlgebra :
    ModuleCat.{w} (SkewMonoidAlgebra A G) ⥤ EquivariantModuleCat.{w} A G where
  obj N := of A G (EquivariantOfModule A G N)
  map {N N'} F := ofHom (EquivariantLinearMap.equivLinearMapOfModule A G N N' F.hom)
  map_id _ := by simp
  map_comp _ _ := by simp

@[simp]
theorem ofModuleSkewMonoidAlgebra_obj (N : ModuleCat.{w} (SkewMonoidAlgebra A G)) :
    (ofModuleSkewMonoidAlgebra A G).obj N = of A G (EquivariantOfModule A G N) :=
  (rfl)

theorem ofModuleSkewMonoidAlgebra_map {N N' : ModuleCat.{w} (SkewMonoidAlgebra A G)}
    (F : N ⟶ N') :
    (ofModuleSkewMonoidAlgebra A G).map F =
      ofHom (EquivariantLinearMap.equivLinearMapOfModule A G N N' F.hom) :=
  (rfl)

@[simp]
theorem ofModuleSkewMonoidAlgebra_map_hom_apply {N N' : ModuleCat.{w} (SkewMonoidAlgebra A G)}
    (F : N ⟶ N') (x : (ofModuleSkewMonoidAlgebra A G).obj N) :
    ((ofModuleSkewMonoidAlgebra A G).map F).hom x = EquivariantOfModule.of (F.hom x.val) :=
  EquivariantLinearMap.equivLinearMapOfModule_apply F.hom x

theorem ofModuleSkewMonoidAlgebra_map_hom_apply_of {N N' : ModuleCat.{w} (SkewMonoidAlgebra A G)}
    (F : N ⟶ N') (n : N) :
    ((ofModuleSkewMonoidAlgebra A G).map F).hom (EquivariantOfModule.of n) =
      EquivariantOfModule.of (F.hom n) :=
  EquivariantLinearMap.equivLinearMapOfModule_apply F.hom (EquivariantOfModule.of n)

variable (A G) in
instance : (ofModuleSkewMonoidAlgebra.{w} A G).Additive where
  map_add {N N' f g} := by
    refine hom_ext' fun x ↦ EquivariantOfModule.ext ?_
    rw [hom_add, EquivariantLinearMap.add_apply, ofModuleSkewMonoidAlgebra_map_hom_apply,
      ofModuleSkewMonoidAlgebra_map_hom_apply, ofModuleSkewMonoidAlgebra_map_hom_apply,
      ModuleCat.hom_add, LinearMap.add_apply]
    exact (EquivariantOfModule.val_add _ _).symm

theorem ofModuleSkewMonoidAlgebra_obj_smul_coeff (N : ModuleCat.{w} (SkewMonoidAlgebra A G))
    (a : A) (n : N) :
    a • (EquivariantOfModule.of n : (ofModuleSkewMonoidAlgebra A G).obj N) =
      EquivariantOfModule.of (SkewMonoidAlgebra.singleOneRingHom (G := G) a • n) :=
  (rfl)

theorem ofModuleSkewMonoidAlgebra_obj_smul_group (N : ModuleCat.{w} (SkewMonoidAlgebra A G))
    (g : G) (n : N) :
    g • (EquivariantOfModule.of n : (ofModuleSkewMonoidAlgebra A G).obj N) =
      EquivariantOfModule.of (SkewMonoidAlgebra.single g (1 : A) • n) :=
  EquivariantOfModule.smul_group_of g n

variable (A G) in
/-- Unit isomorphism `𝟭 (EquivariantModuleCat A G) ≅
toModuleSkewMonoidAlgebra A G ⋙ ofModuleSkewMonoidAlgebra A G`. -/
def equivalenceUnitIso :
    𝟭 (EquivariantModuleCat.{w} A G) ≅
      toModuleSkewMonoidAlgebra.{w} A G ⋙ ofModuleSkewMonoidAlgebra.{w} A G :=
  NatIso.ofComponents
    (fun X ↦ mkIso (equivariantOfAsModuleEquiv A G X))
    (fun {X Y} f ↦ hom_ext' fun x ↦ by
      let uX : X ≅ (toModuleSkewMonoidAlgebra A G ⋙ ofModuleSkewMonoidAlgebra A G).obj X :=
        mkIso (equivariantOfAsModuleEquiv A G X)
      let uY : Y ≅ (toModuleSkewMonoidAlgebra A G ⋙ ofModuleSkewMonoidAlgebra A G).obj Y :=
        mkIso (equivariantOfAsModuleEquiv A G Y)
      have hL : (((𝟭 (EquivariantModuleCat.{w} A G)).map f) ≫ uY.hom).hom x =
          EquivariantOfModule.of (EquivariantAsModule.of (f.hom x)) :=
        (EquivariantLinearMap.comp_apply uY.hom.hom f.hom x).trans <|
          (EquivariantLinearEquiv.toEquivariantLinearMap_apply
            (equivariantOfAsModuleEquiv A G Y) (f.hom x)).trans
            (equivariantOfAsModuleEquiv_apply A G (f.hom x))
      have hR : (uX.hom ≫
          (toModuleSkewMonoidAlgebra A G ⋙ ofModuleSkewMonoidAlgebra A G).map f).hom x =
          EquivariantOfModule.of (EquivariantAsModule.of (f.hom x)) :=
        (EquivariantLinearMap.comp_apply
          ((ofModuleSkewMonoidAlgebra A G).map ((toModuleSkewMonoidAlgebra A G).map f)).hom
          uX.hom.hom x).trans <|
          (congrArg (((ofModuleSkewMonoidAlgebra A G).map
            ((toModuleSkewMonoidAlgebra A G).map f)).hom ·) <|
            (EquivariantLinearEquiv.toEquivariantLinearMap_apply
              (equivariantOfAsModuleEquiv A G X) x).trans
              (equivariantOfAsModuleEquiv_apply A G x)).trans <|
          (ofModuleSkewMonoidAlgebra_map_hom_apply_of _ _).trans
            (congrArg EquivariantOfModule.of (toModuleSkewMonoidAlgebra_map_hom_apply_of f x))
      exact hL.trans hR.symm)

theorem equivalenceUnitIso_hom_app_apply
    (X : EquivariantModuleCat.{w} A G) (x : X) :
    ((equivalenceUnitIso A G).hom.app X).hom x =
      EquivariantOfModule.of (EquivariantAsModule.of x) :=
  (EquivariantLinearEquiv.toEquivariantLinearMap_apply
    (equivariantOfAsModuleEquiv A G X) x).trans
    (equivariantOfAsModuleEquiv_apply A G x)

theorem equivalenceUnitIso_inv_app_apply
    (X : EquivariantModuleCat.{w} A G)
    (x : (toModuleSkewMonoidAlgebra A G ⋙ ofModuleSkewMonoidAlgebra A G).obj X) :
    ((equivalenceUnitIso A G).inv.app X).hom x = x.val.val :=
  (EquivariantLinearEquiv.toEquivariantLinearMap_apply
    (equivariantOfAsModuleEquiv A G X).symm x).trans
    (equivariantOfAsModuleEquiv_symm_apply A G x)

variable (A G) in
/-- Counit isomorphism `ofModuleSkewMonoidAlgebra A G ⋙ toModuleSkewMonoidAlgebra A G ≅
𝟭 (ModuleCat (SkewMonoidAlgebra A G))`. -/
def equivalenceCounitIso :
    ofModuleSkewMonoidAlgebra.{w} A G ⋙ toModuleSkewMonoidAlgebra.{w} A G ≅
      𝟭 (ModuleCat.{w} (SkewMonoidAlgebra A G)) :=
  NatIso.ofComponents
    (fun N ↦ (equivariantAsOfModuleLinearEquiv A G N).toModuleIso)
    (fun {N N'} F ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦ by
      have hL : (((ofModuleSkewMonoidAlgebra A G ⋙ toModuleSkewMonoidAlgebra A G).map F) ≫
          (equivariantAsOfModuleLinearEquiv A G N').toModuleIso.hom).hom x =
        F.hom x.val.val :=
        (congrArg (equivariantAsOfModuleLinearEquiv A G N' ·) <|
          (toModuleSkewMonoidAlgebra_map_hom_apply _ x).trans <|
            congrArg EquivariantAsModule.of (ofModuleSkewMonoidAlgebra_map_hom_apply F x.val)).trans
          (equivariantAsOfModuleLinearEquiv_apply A G _)
      have hR : ((equivariantAsOfModuleLinearEquiv A G N).toModuleIso.hom ≫
          (𝟭 _).map F).hom x =
        F.hom x.val.val :=
        congrArg F.hom (equivariantAsOfModuleLinearEquiv_apply A G x)
      exact hL.trans hR.symm)

theorem equivalenceCounitIso_hom_app_apply
    (N : ModuleCat.{w} (SkewMonoidAlgebra A G))
    (x : (ofModuleSkewMonoidAlgebra A G ⋙ toModuleSkewMonoidAlgebra A G).obj N) :
    ((equivalenceCounitIso A G).hom.app N).hom x = x.val.val :=
  equivariantAsOfModuleLinearEquiv_apply A G x

theorem equivalenceCounitIso_inv_app_apply
    (N : ModuleCat.{w} (SkewMonoidAlgebra A G)) (n : N) :
    ((equivalenceCounitIso A G).inv.app N).hom n =
      EquivariantAsModule.of (EquivariantOfModule.of n) :=
  equivariantAsOfModuleLinearEquiv_symm_apply A G n

variable (A G) in
/-- **Equivalence between `G`-equivariant left `A`-modules and left
`SkewMonoidAlgebra A G`-modules.**

`equivalenceModuleSkewMonoidAlgebra_functor` and `equivalenceModuleSkewMonoidAlgebra_inverse`
identify its forward and inverse functors with `toModuleSkewMonoidAlgebra` and
`ofModuleSkewMonoidAlgebra`. -/
def equivalenceModuleSkewMonoidAlgebra :
    EquivariantModuleCat.{w} A G ≌ ModuleCat.{w} (SkewMonoidAlgebra A G) where
  functor := toModuleSkewMonoidAlgebra A G
  inverse := ofModuleSkewMonoidAlgebra A G
  unitIso := equivalenceUnitIso A G
  counitIso := equivalenceCounitIso A G
  functor_unitIso_comp X := ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    (equivalenceCounitIso_hom_app_apply ((toModuleSkewMonoidAlgebra A G).obj X)
      (((toModuleSkewMonoidAlgebra A G).map ((equivalenceUnitIso A G).hom.app X)).hom x)).trans <|
      (congrArg (fun y ↦ EquivariantOfModule.val (EquivariantAsModule.val y))
        (toModuleSkewMonoidAlgebra_map_hom_apply ((equivalenceUnitIso A G).hom.app X) x)).trans <|
      congrArg EquivariantOfModule.val (equivalenceUnitIso_hom_app_apply X x.val)

variable (A G) in
@[simp]
theorem equivalenceModuleSkewMonoidAlgebra_functor :
    (equivalenceModuleSkewMonoidAlgebra.{w} A G).functor = toModuleSkewMonoidAlgebra.{w} A G :=
  (rfl)

variable (A G) in
@[simp]
theorem equivalenceModuleSkewMonoidAlgebra_inverse :
    (equivalenceModuleSkewMonoidAlgebra.{w} A G).inverse = ofModuleSkewMonoidAlgebra.{w} A G :=
  (rfl)

variable (A G) in
instance : (toModuleSkewMonoidAlgebra.{w} A G).IsEquivalence :=
  equivalenceModuleSkewMonoidAlgebra_functor A G ▸
    (equivalenceModuleSkewMonoidAlgebra.{w} A G).isEquivalence_functor

variable (A G) in
instance : (ofModuleSkewMonoidAlgebra.{w} A G).IsEquivalence :=
  equivalenceModuleSkewMonoidAlgebra_inverse A G ▸
    (equivalenceModuleSkewMonoidAlgebra.{w} A G).isEquivalence_inverse

section LinearFunctor

open scoped ModuleCat

variable (k : Type u₀) [Field k] [Algebra k A] [SMulCommClass G k A]

variable (A G) in
instance : (toModuleSkewMonoidAlgebra.{w} A G).Linear k where
  map_smul {X Y} f r := ModuleCat.hom_ext <| LinearMap.ext fun z ↦ by
    have h1 : ((toModuleSkewMonoidAlgebra A G).map (r • f)).hom z =
        EquivariantAsModule.of (algebraMap k A r • f.hom z.val) :=
      (toModuleSkewMonoidAlgebra_map_hom_apply (r • f) z).trans
        (congrArg EquivariantAsModule.of (hom_smul_apply r f z.val))
    have h2 : ((r • (toModuleSkewMonoidAlgebra A G).map f).hom z :
        EquivariantAsModule A G Y) =
        algebraMap k (SkewMonoidAlgebra A G) r •
          EquivariantAsModule.of (A := A) (G := G) (f.hom z.val) :=
      (congrArg (fun l : _ →ₗ[_] _ ↦ l z)
        (ModuleCat.hom_smul r ((toModuleSkewMonoidAlgebra A G).map f))).trans <|
        (LinearMap.smul_apply r _ z).trans <|
        (algebraMap_smul (SkewMonoidAlgebra A G) r _).symm.trans <|
        congrArg (algebraMap k (SkewMonoidAlgebra A G) r • ·)
          (toModuleSkewMonoidAlgebra_map_hom_apply f z)
    have h3 : algebraMap k (SkewMonoidAlgebra A G) r •
        EquivariantAsModule.of (A := A) (G := G) (f.hom z.val) =
        EquivariantAsModule.of (algebraMap k A r • f.hom z.val) :=
      EquivariantAsModule.ext <|
        (EquivariantAsModule.val_single_smul (1 : G) (algebraMap k A r)
          (EquivariantAsModule.of (f.hom z.val))).trans
          (congrArg (algebraMap k A r • ·) (one_smul G (f.hom z.val)))
    exact h1.trans (h2.trans h3).symm

variable (A G) in
instance : (ofModuleSkewMonoidAlgebra.{w} A G).Linear k where
  map_smul {N N'} F r := hom_ext' fun z ↦ EquivariantOfModule.ext <| by
    rw [ofModuleSkewMonoidAlgebra_map_hom_apply, ModuleCat.hom_smul, LinearMap.smul_apply,
      ← algebraMap_smul (SkewMonoidAlgebra A G), hom_smul_apply,
      ofModuleSkewMonoidAlgebra_map_hom_apply]
    exact (EquivariantOfModule.val_smul_coeff (algebraMap k A r) _).symm

end LinearFunctor

end LeftEquivalence

/-! ### Right-module equivalence via `(SkewMonoidAlgebra A G)ᵐᵒᵖ ≃+* SkewMonoidAlgebra Aᵐᵒᵖ G` -/

section RightEquivalence

variable (A : Type u) (G : Type v) [Ring A] [Group G] [MulSemiringAction G A]

/-- Functor converting a right `SkewMonoidAlgebra A G`-module (i.e., a left module over
`(SkewMonoidAlgebra A G)ᵐᵒᵖ`) into a `G`-equivariant left `Aᵐᵒᵖ`-module via restriction of scalars
along `(TauCeti.skewMonoidAlgebraOpRingEquiv A G).symm` followed by `ofModuleSkewMonoidAlgebra`. -/
abbrev rightModuleToEquivariant :
    ModuleCat.{w} (SkewMonoidAlgebra A G)ᵐᵒᵖ ⥤ EquivariantModuleCat.{w} Aᵐᵒᵖ G :=
  ModuleCat.restrictScalars (skewMonoidAlgebraOpRingEquiv A G).symm.toRingHom ⋙
    ofModuleSkewMonoidAlgebra.{w} Aᵐᵒᵖ G

/-- **Right-module equivalence for skew group algebras.** For a group `G`, right modules over
`SkewMonoidAlgebra A G` — represented as left modules over `(SkewMonoidAlgebra A G)ᵐᵒᵖ` — are
equivalent to `G`-equivariant left `Aᵐᵒᵖ`-modules (`EquivariantModuleCat Aᵐᵒᵖ G`) via
`TauCeti.skewMonoidAlgebraOpRingEquiv`. -/
def rightModuleSkewMonoidAlgebraEquivalence :
    ModuleCat.{w} (SkewMonoidAlgebra A G)ᵐᵒᵖ ≌ EquivariantModuleCat.{w} Aᵐᵒᵖ G :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (skewMonoidAlgebraOpRingEquiv A G).symm).trans
    (equivalenceModuleSkewMonoidAlgebra.{w} Aᵐᵒᵖ G).symm

@[simp]
theorem rightModuleSkewMonoidAlgebraEquivalence_functor :
    (rightModuleSkewMonoidAlgebraEquivalence.{w} A G).functor = rightModuleToEquivariant.{w} A G :=
  (rfl)

/-- Under `rightModuleToEquivariant` (the forward functor of
`rightModuleSkewMonoidAlgebraEquivalence`), `op a ∈ Aᵐᵒᵖ` acts on an element `n` of a right
`SkewMonoidAlgebra A G`-module `N` by `op (single 1 a) • n` (right multiplication by `single 1 a`).
-/
@[simp]
theorem rightModuleToEquivariant_obj_smul_coeff
    (N : ModuleCat.{w} (SkewMonoidAlgebra A G)ᵐᵒᵖ) (a : A)
    (x : (rightModuleToEquivariant.{w} A G).obj N) :
    (MulOpposite.op a • x).val =
      MulOpposite.op (SkewMonoidAlgebra.singleOneRingHom (G := G) a) • (x.val : N) := by
  have h : (MulOpposite.op a • x).val =
      ((skewMonoidAlgebraOpRingEquiv A G).symm
        (SkewMonoidAlgebra.singleOneRingHom (G := G) (MulOpposite.op a))) • (x.val : N) :=
    rfl
  rw [h, skewMonoidAlgebraOpRingEquiv_symm_singleOneRingHom, MulOpposite.unop_op]

/-- Under `rightModuleToEquivariant` (the forward functor of
`rightModuleSkewMonoidAlgebraEquivalence`), `g ∈ G` acts on an element `n` of a right
`SkewMonoidAlgebra A G`-module `N` by `op (single g⁻¹ 1) • n` (right multiplication by
`single g⁻¹ 1`). -/
@[simp]
theorem rightModuleToEquivariant_obj_smul_group
    (N : ModuleCat.{w} (SkewMonoidAlgebra A G)ᵐᵒᵖ) (g : G)
    (x : (rightModuleToEquivariant.{w} A G).obj N) :
    (g • x).val =
      MulOpposite.op (SkewMonoidAlgebra.single g⁻¹ (1 : A)) • (x.val : N) := by
  have h : (g • x).val =
      ((skewMonoidAlgebraOpRingEquiv A G).symm
        (SkewMonoidAlgebra.of Aᵐᵒᵖ G g)) • (x.val : N) :=
    rfl
  rw [h, skewMonoidAlgebraOpRingEquiv_symm_of, SkewMonoidAlgebra.of_apply]

end RightEquivalence

/-! ### Comparison with `Rep k G` and `ModuleCat k[G]` for `A = k` -/

section TrivialActionRep

open scoped MonoidAlgebra

variable (k : Type u) (G : Type v) [CommRing k] [Monoid G] [MulSemiringAction G k]
  [SMulCommClass G k k]

-- `@[expose]` is load-bearing because `toRep_obj_ρ_apply` and `toRepCompToModuleMonoidAlgebraIso`
-- typecheck elements against the carrier `((toRep k G).obj X).V = X`.
/-- When `A = k` has a `k`-linear `G`-action (hence trivial by
`TauCeti.smul_eq_self_of_smulCommClass_self`), every object of `EquivariantModuleCat k G` defines
an object of `Rep k G` with the same carrier and `G`-action. -/
@[expose]
def toRep : EquivariantModuleCat.{w} k G ⥤ Rep.{w} k G where
  obj X :=
    letI : SMulCommClass G k X := MulSemiringAction.smulCommClass_of_smulDistribClass k k G X
    Rep.ofDistribMulAction k G X
  map {X Y} f :=
    letI : SMulCommClass G k X := MulSemiringAction.smulCommClass_of_smulDistribClass k k G X
    letI : SMulCommClass G k Y := MulSemiringAction.smulCommClass_of_smulDistribClass k k G Y
    Rep.ofHom
      { __ := f.hom.toLinearMap
        isIntertwining' g := by
          ext x
          exact f.hom.map_smul_group g x }

@[simp]
theorem toRep_obj_ρ_apply (X : EquivariantModuleCat.{w} k G) (g : G) (x : X) :
    ((toRep k G).obj X).ρ g x = g • x :=
  (rfl)

/-- On any `V : Rep k G`, when the `G`-action on `k` commutes with `k` (hence is trivial), `V.ρ g`
satisfies the skew-distributivity law `V.ρ g (r • v) = (g • r) • V.ρ g v`. -/
theorem rep_smul_distrib (V : Rep.{w} k G) (g : G) (r : k) (v : V.V) :
    V.ρ g (r • v) = (g • r) • V.ρ g v := by
  rw [smul_eq_self_of_smulCommClass_self g r, LinearMap.map_smul]

-- `@[expose]` is load-bearing so that `(ofRep k G).obj V` has carrier `V.V` in unit/counit
-- identifications.
/-- Convert an object of `Rep k G` into an object of `EquivariantModuleCat k G` on the same
carrier, using triviality of the `G`-action on `k` (`TauCeti.smul_eq_self_of_smulCommClass_self`)
to supply skew-distributivity (`SMulDistribClass G k`). -/
@[expose]
def ofRep : Rep.{w} k G ⥤ EquivariantModuleCat.{w} k G where
  obj V :=
    letI : DistribMulAction G V.V := .compHom V.V V.ρ
    haveI : SMulDistribClass G k V.V := ⟨rep_smul_distrib k G V⟩
    of k G V.V
  map {V W} φ :=
    letI : DistribMulAction G V.V := .compHom V.V V.ρ
    haveI : SMulDistribClass G k V.V := ⟨rep_smul_distrib k G V⟩
    letI : DistribMulAction G W.V := .compHom W.V W.ρ
    haveI : SMulDistribClass G k W.V := ⟨rep_smul_distrib k G W⟩
    ofHom
      { toLinearMap := φ.hom.toLinearMap
        map_smul_group' g v := Rep.hom_comm_apply φ g v }
  map_id _ := by ext x; simp
  map_comp _ _ := by ext x; simp

private def toRepOfRepEquiv (X : EquivariantModuleCat.{w} k G) :
    EquivariantLinearEquiv k G X ((toRep k G ⋙ ofRep k G).obj X) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_smul_group' _ _ := rfl

/-- **For `A = k` with trivial `G`-action, `EquivariantModuleCat k G` is equivalent to `Rep k G`.**
-/
def repEquivalence : EquivariantModuleCat.{w} k G ≌ Rep.{w} k G where
  functor := toRep k G
  inverse := ofRep k G
  unitIso := NatIso.ofComponents
    (fun X ↦ mkIso (toRepOfRepEquiv k G X))
    (fun {X Y} f ↦ by
      refine hom_ext (EquivariantLinearMap.toLinearMap_injective (LinearMap.ext fun x ↦ ?_))
      have hL : ((((𝟭 _).map f) ≫ (mkIso (toRepOfRepEquiv k G Y)).hom).hom).toLinearMap x =
          f.hom.toLinearMap x :=
        congrArg (fun l : _ →ₗ[k] _ ↦ l x)
          ((EquivariantLinearMap.toLinearMap_comp _ _).trans <|
            congrArg (·.comp f.hom.toLinearMap)
              (EquivariantLinearEquiv.toLinearMap_toEquivariantLinearMap (toRepOfRepEquiv k G Y)))
      have hR : (((mkIso (toRepOfRepEquiv k G X)).hom ≫
          (toRep k G ⋙ ofRep k G).map f).hom).toLinearMap x = f.hom.toLinearMap x :=
        congrArg (fun l : _ →ₗ[k] _ ↦ l x)
          ((EquivariantLinearMap.toLinearMap_comp _ _).trans <|
            congrArg (((ofRep k G).map ((toRep k G).map f)).hom.toLinearMap.comp ·)
              (EquivariantLinearEquiv.toLinearMap_toEquivariantLinearMap (toRepOfRepEquiv k G X)))
      exact hL.trans hR.symm)
  counitIso := NatIso.ofComponents
    (fun V ↦ Rep.mkIso
      { toLinearEquiv := LinearEquiv.refl k V.V
        isIntertwining' _ := by ext x; rfl })
    (fun {V W} φ ↦ Rep.hom_ext <| Representation.IntertwiningMap.ext <|
      (Representation.IntertwiningMap.comp_toLinearMap _ _ _ _ _).trans <|
        (LinearMap.ext fun _ ↦ rfl).trans
          (Representation.IntertwiningMap.comp_toLinearMap _ _ _ _ _).symm)
  functor_unitIso_comp X := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    (Representation.IntertwiningMap.comp_toLinearMap _ _ _ _ _).trans <|
      LinearMap.ext fun x ↦
        congrArg (fun l : _ →ₗ[k] _ ↦ l x)
          (EquivariantLinearEquiv.toLinearMap_toEquivariantLinearMap (toRepOfRepEquiv k G X))

@[simp]
theorem repEquivalence_functor : (repEquivalence.{w} k G).functor = toRep.{w} k G :=
  (rfl)

@[simp]
theorem repEquivalence_inverse : (repEquivalence.{w} k G).inverse = ofRep.{w} k G :=
  (rfl)

private theorem toRep_asModuleEquiv_smul (X : EquivariantModuleCat.{w} k G)
    (s : SkewMonoidAlgebra k G) (y : ((toRep k G).obj X).ρ.asModule) :
    ((toRep k G).obj X).ρ.asModuleEquiv (skewMonoidAlgebraSelfAlgEquiv k G s • y) =
      (s • EquivariantAsModule.of (A := k) (G := G) (M := X)
        (((toRep k G).obj X).ρ.asModuleEquiv y)).val := by
  induction s using SkewMonoidAlgebra.induction_on with
  | zero => simp; rfl
  | add p q hp hq => simp [add_smul, hp, hq]; rfl
  | single g r => simp; rfl

private def toRepCompToModuleMonoidAlgebraLinearEquiv (X : EquivariantModuleCat.{w} k G) :
    ((ModuleCat.restrictScalars (skewMonoidAlgebraSelfAlgEquiv k G).toRingHom).obj
      (Rep.toModuleMonoidAlgebra.obj ((toRep k G).obj X))) ≃ₗ[SkewMonoidAlgebra k G]
      (toModuleSkewMonoidAlgebra k G).obj X where
  toFun y := EquivariantAsModule.of (A := k) (G := G) (M := X)
    (((toRep k G).obj X).ρ.asModuleEquiv y)
  invFun z := ((toRep k G).obj X).ρ.asModuleEquiv.symm z.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' s y := EquivariantAsModule.ext (toRep_asModuleEquiv_smul k G X s y)

/-- **Compatibility of `toModuleSkewMonoidAlgebra` with `Rep.toModuleMonoidAlgebra`.** For `A = k`
with `k`-linear (hence trivial) `G`-action, converting an equivariant `(k, G)`-module to `Rep k G`,
applying `Rep.toModuleMonoidAlgebra`, and restricting scalars along
`TauCeti.skewMonoidAlgebraSelfAlgEquiv k G : SkewMonoidAlgebra k G ≃ₐ[k] k[G]` is naturally
isomorphic to `toModuleSkewMonoidAlgebra k G`. -/
def toRepCompToModuleMonoidAlgebraIso :
    toRep.{w} k G ⋙ Rep.toModuleMonoidAlgebra ⋙
        ModuleCat.restrictScalars (skewMonoidAlgebraSelfAlgEquiv k G).toRingHom ≅
      toModuleSkewMonoidAlgebra.{w} k G :=
  NatIso.ofComponents
    (fun X ↦ (toRepCompToModuleMonoidAlgebraLinearEquiv k G X).toModuleIso)
    (fun {X Y} f ↦ ModuleCat.hom_ext <| LinearMap.ext fun y ↦ EquivariantAsModule.ext <| by
      have hL : ((((toRep.{w} k G ⋙ Rep.toModuleMonoidAlgebra ⋙
            ModuleCat.restrictScalars (skewMonoidAlgebraSelfAlgEquiv k G).toRingHom).map f) ≫
            (toRepCompToModuleMonoidAlgebraLinearEquiv k G Y).toModuleIso.hom).hom y).val =
          f.hom (((toRep k G).obj X).ρ.asModuleEquiv y) :=
        EquivariantLinearMap.toLinearMap_apply f.hom (((toRep k G).obj X).ρ.asModuleEquiv y)
      have hR : (((toRepCompToModuleMonoidAlgebraLinearEquiv k G X).toModuleIso.hom ≫
            (toModuleSkewMonoidAlgebra.{w} k G).map f).hom y).val =
          f.hom (((toRep k G).obj X).ρ.asModuleEquiv y) :=
        congrArg EquivariantAsModule.val
          (toModuleSkewMonoidAlgebra_map_hom_apply_of f (((toRep k G).obj X).ρ.asModuleEquiv y))
      exact hL.trans hR.symm)

end TrivialActionRep

end EquivariantModuleCat

end TauCeti
