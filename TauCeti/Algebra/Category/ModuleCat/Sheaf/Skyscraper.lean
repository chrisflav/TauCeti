/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# The stalk--skyscraper adjunction for sheaves of modules

For a point `x` of a ringed space `(X, R)` with commutative structure sheaf `R`, this file bundles
stalks of `R`-modules at `x` into a functor `SheafOfModules.stalkFunctor R x` to `R_x`-modules,
constructs its right adjoint `SheafOfModules.skyscraper R x`, and characterizes isomorphisms of
sheaves of modules by bijectivity on stalks (`SheafOfModules.isIso_iff_bijective_stalkFunctor_map`).

For an `R_x`-module `M`, the skyscraper module sheaf `(skyscraper R x).obj M` has sections `M` over
each open `U ⊆ X` containing `x` (`SheafOfModules.skyscraperSectionsEquiv`), where a ring section
`r ∈ R(U)` acts through its germ `r_x ∈ R_x`, and vanishes over opens not containing `x`
(`SheafOfModules.subsingleton_skyscraper_obj_of_notMem`). Internally its sections over `U` are
modeled by `PLift (x ∈ U) → M` so restriction maps compose definitionally without classical
decidability assumptions on open sets and without restricting the module universe `v`. Morphisms
from a module sheaf `G` into `(skyscraper R x).obj M` correspond bijectively to `R_x`-linear maps
`G_x ⟶ M` (`SheafOfModules.stalkSkyscraperAdjunction`), using the linear universal property
`PresheafOfModules.stalkLiftCommRing` of module stalks.

## Main declarations

* `SheafOfModules.stalkFunctor`: the stalk at `x` as a functor from sheaves of `R`-modules to
  `ModuleCat (TopCat.Presheaf.stalk R.obj x)`.
* `SheafOfModules.isIso_iff_bijective_stalkFunctor_map`: a morphism of sheaves of modules is an
  isomorphism if and only if it induces a bijection on stalks at every point.
* `SheafOfModules.skyscraper` and `SheafOfModules.skyscraperSectionsEquiv`: the skyscraper sheaf of
  `R`-modules supported at `x`, functorial in an `R_x`-module in any universe, with its section
  identification `Γ((skyscraper R x).obj M, U) ≃+ M` for `x ∈ U` and extensionality principle
  `SheafOfModules.skyscraper_section_ext`.
* `SheafOfModules.stalkSkyscraperHomEquiv` and `SheafOfModules.stalkSkyscraperAdjunction`: the
  adjunction `stalkFunctor R x ⊣ skyscraper R x`.

## References

* [The Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097) (skyscraper sheaves and
  the stalk--skyscraper adjunction).
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Exercise 1.17.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf
open TauCeti.SheafOfModules (ringCatSheaf)

universe u v

noncomputable section

namespace SheafOfModules

section StalkFunctor

variable {X : TopCat.{u}}

section Point

variable (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)

/-- The stalk at `x` of sheaves of `R`-modules, bundled as a functor to `R_x`-modules. -/
-- Its object part identifies the stalk carrier appearing in germ evaluation formulas.
@[expose] def stalkFunctor :
    SheafOfModules.{u} (ringCatSheaf R) ⥤ ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x) where
  obj G := ModuleCat.of ↑(TopCat.Presheaf.stalk R.obj x) ↑(TopCat.Presheaf.stalk G.val.presheaf x)
  map f := ModuleCat.ofHom (PresheafOfModules.stalkMapCommRing (S := R.obj) x f.val)
  map_id G := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun s ↦ ?_
    obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq G.val.presheaf s
    erw [PresheafOfModules.stalkMapCommRing_germ]
    rfl
  map_comp {G₁ G₂ G₃} f g := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun s ↦ ?_
    obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq G₁.val.presheaf s
    exact (PresheafOfModules.stalkMapCommRing_germ (S := R.obj) x (f ≫ g).val U hx m).trans
      ((PresheafOfModules.stalkMapCommRing_germ (S := R.obj) x g.val U hx
        (f.val.app (op U) m)).symm.trans
          (congrArg (PresheafOfModules.stalkMapCommRing (S := R.obj) x g.val)
            (PresheafOfModules.stalkMapCommRing_germ (S := R.obj) x f.val U hx m).symm))

/-- On objects, `stalkFunctor` returns the module stalk over the commutative ring stalk. -/
@[simp]
theorem stalkFunctor_obj_coe (G : SheafOfModules.{u} (ringCatSheaf R)) :
    (↑((stalkFunctor R x).obj G) : Type u) = (↑(TopCat.Presheaf.stalk G.val.presheaf x) : Type u) :=
  (rfl)

/-- On germs, `stalkFunctor` applies the underlying morphism of sections. -/
@[simp]
theorem stalkFunctor_map_germ {G₁ G₂ : SheafOfModules.{u} (ringCatSheaf R)} (f : G₁ ⟶ G₂)
    (U : Opens X) (hx : x ∈ U) (m : G₁.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    ((stalkFunctor R x).map f (germ G₁.val.presheaf U x hx m) =
      germ G₂.val.presheaf U x hx (f.val.app (op U) m)) :=
  PresheafOfModules.stalkMapCommRing_germ (S := R.obj) x f.val U hx m

end Point

/-- The underlying map of `stalkFunctor` agrees with the abelian-sheaf stalk map. -/
theorem coe_stalkFunctor_map {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} {x : X}
    {G₁ G₂ : SheafOfModules.{u} (ringCatSheaf R)} (f : G₁ ⟶ G₂) :
    ⇑((stalkFunctor R x).map f) =
      ⇑((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((toSheaf (ringCatSheaf R)).map f).hom) := by
  funext s
  obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq G₁.val.presheaf s
  erw [stalkFunctor_map_germ, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- A morphism of sheaves of modules is an isomorphism when it is bijective on every stalk. -/
theorem isIso_of_bijective_stalkFunctor_map
    {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    {G₁ G₂ : SheafOfModules.{u} (ringCatSheaf R)}
    (f : G₁ ⟶ G₂) (hf : ∀ x : X, Function.Bijective ((stalkFunctor R x).map f)) :
    IsIso f := by
  have hAb : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toSheaf (ringCatSheaf R)).map f).hom) := fun x ↦ by
    rw [ConcreteCategory.isIso_iff_bijective, ← coe_stalkFunctor_map f]
    exact hf x
  have : IsIso ((toSheaf (ringCatSheaf R)).map f) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ((toSheaf (ringCatSheaf R)).map f)
  exact isIso_of_reflects_iso f (toSheaf (ringCatSheaf R))

/-- A morphism of sheaves of modules is an isomorphism if and only if it is bijective on stalks at
every point. -/
theorem isIso_iff_bijective_stalkFunctor_map
    {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    {G₁ G₂ : SheafOfModules.{u} (ringCatSheaf R)} (f : G₁ ⟶ G₂) :
    IsIso f ↔ ∀ x : X, Function.Bijective ((stalkFunctor R x).map f) :=
  ⟨fun _ x ↦ ConcreteCategory.bijective_of_isIso ((stalkFunctor R x).map f),
    isIso_of_bijective_stalkFunctor_map f⟩

end StalkFunctor

section Skyscraper

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)

private def skyscraperAbPresheaf (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x)) :
    X.Presheaf AddCommGrpCat.{v} where
  obj U := AddCommGrpCat.of (PLift (x ∈ U.unop) → M)
  map i := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun s hx ↦ s ⟨i.unop.le hx.down⟩) fun _ _ ↦ rfl)

private theorem isSheaf_skyscraperAbPresheaf
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (skyscraperAbPresheaf R x M) := by
  intro E U S hS sf hsf
  let V (hx : x ∈ U) : Opens X := (hS x hx).choose
  let i (hx : x ∈ U) : V hx ⟶ U := (hS x hx).choose_spec.choose
  have hi (hx : x ∈ U) : S.arrows (i hx) := (hS x hx).choose_spec.choose_spec.1
  have hxV (hx : x ∈ U) : x ∈ V hx := (hS x hx).choose_spec.choose_spec.2
  let sfHom {W : Opens X} (j : W ⟶ U) (hj : S.arrows j) :
      E ⟶ (skyscraperAbPresheaf R x M).obj (op W) := sf j hj
  refine ⟨AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun (e : E) (hx : PLift (x ∈ U)) ↦
      (sfHom (i hx.down) (hi hx.down) e : PLift (x ∈ V hx.down) → M) ⟨hxV hx.down⟩)
    fun e₁ e₂ ↦ funext fun hx ↦
      congrArg (fun f : PLift (x ∈ V hx.down) → M ↦ f ⟨hxV hx.down⟩)
        ((sfHom (i hx.down) (hi hx.down)).hom.map_add e₁ e₂)), ?_, ?_⟩
  · intro W j hj
    refine AddCommGrpCat.ext fun e ↦ funext fun ⟨hxW⟩ ↦ ?_
    let hx : x ∈ U := j.le hxW
    let p₁ : V hx ⊓ W ⟶ V hx := homOfLE inf_le_left
    let p₂ : V hx ⊓ W ⟶ W := homOfLE inf_le_right
    have hcompat :
        sfHom (i hx) (hi hx) ≫ (skyscraperAbPresheaf R x M).map p₁.op =
          sfHom j hj ≫ (skyscraperAbPresheaf R x M).map p₂.op :=
      hsf p₁ p₂ (hi hx) hj (Subsingleton.elim _ _)
    exact congrArg (fun f : E ⟶ (skyscraperAbPresheaf R x M).obj (op (V hx ⊓ W)) ↦
      (f e : PLift (x ∈ V hx ⊓ W) → M) ⟨⟨hxV hx, hxW⟩⟩) hcompat
  · intro t ht
    refine AddCommGrpCat.ext fun e ↦ funext fun ⟨hx⟩ ↦ ?_
    have hti : t ≫ (skyscraperAbPresheaf R x M).map (i hx).op = sfHom (i hx) (hi hx) :=
      ht (i hx) (hi hx)
    exact congrArg (fun f : E ⟶ (skyscraperAbPresheaf R x M).obj (op (V hx)) ↦
      (f e : PLift (x ∈ V hx) → M) ⟨hxV hx⟩) hti

private local instance skyscraperSectionModule
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x)) (U : (Opens X)ᵒᵖ) :
    Module ((ringCatSheaf R).obj.obj U) (PLift (x ∈ U.unop) → M) where
  smul r s hx := TopCat.Presheaf.germ R.obj U.unop x hx.down (r : R.obj.obj (op U.unop)) • s hx
  one_smul s := funext fun ⟨hx⟩ ↦ by
    change TopCat.Presheaf.germ R.obj U.unop x hx (1 : R.obj.obj (op U.unop)) • s ⟨hx⟩ = s ⟨hx⟩
    rw [map_one, one_smul]
  mul_smul r₁ r₂ s := funext fun ⟨hx⟩ ↦ by
    let r₁' : R.obj.obj (op U.unop) := r₁
    let r₂' : R.obj.obj (op U.unop) := r₂
    change TopCat.Presheaf.germ R.obj U.unop x hx (r₁' * r₂') • s ⟨hx⟩ =
      TopCat.Presheaf.germ R.obj U.unop x hx r₁' •
        TopCat.Presheaf.germ R.obj U.unop x hx r₂' • s ⟨hx⟩
    rw [map_mul, mul_smul]
  smul_zero _ := funext fun _ ↦ smul_zero _
  smul_add _ _ _ := funext fun _ ↦ smul_add _ _ _
  add_smul r₁ r₂ s := funext fun ⟨hx⟩ ↦ by
    let r₁' : R.obj.obj (op U.unop) := r₁
    let r₂' : R.obj.obj (op U.unop) := r₂
    change TopCat.Presheaf.germ R.obj U.unop x hx (r₁' + r₂') • s ⟨hx⟩ =
      TopCat.Presheaf.germ R.obj U.unop x hx r₁' • s ⟨hx⟩ +
        TopCat.Presheaf.germ R.obj U.unop x hx r₂' • s ⟨hx⟩
    rw [map_add, add_smul]
  zero_smul s := funext fun ⟨hx⟩ ↦ by
    change TopCat.Presheaf.germ R.obj U.unop x hx (0 : R.obj.obj (op U.unop)) • s ⟨hx⟩ = 0
    rw [map_zero, zero_smul]

private local instance skyscraperObjModule
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x)) (U : (Opens X)ᵒᵖ) :
    Module ((ringCatSheaf R).obj.obj U) ((skyscraperAbPresheaf R x M).obj U) :=
  skyscraperSectionModule R x M U

private theorem skyscraperAbPresheaf_map_smul
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x))
    ⦃U V : (Opens X)ᵒᵖ⦄ (i : U ⟶ V) (r : (ringCatSheaf R).obj.obj U)
    (s : (skyscraperAbPresheaf R x M).obj U) :
    (skyscraperAbPresheaf R x M).map i (r • s) = (ringCatSheaf R).obj.map i r •
      (skyscraperAbPresheaf R x M).map i s :=
  funext fun ⟨hx⟩ ↦ congrArg (· • (s : PLift (x ∈ U.unop) → M) ⟨i.unop.le hx⟩)
    (TopCat.Presheaf.germ_res_apply R.obj i.unop x hx (r : R.obj.obj (op U.unop))).symm

/-- The skyscraper sheaf of `R`-modules at `x : X` associated to an `R_x`-module `M`, with sections
`M` over opens containing `x` (`skyscraperSectionsEquiv`) and `0` otherwise
(`subsingleton_skyscraper_obj_of_notMem`), functorial in `M`. -/
def skyscraper :
    ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x) ⥤ SheafOfModules.{v} (ringCatSheaf R) where
  obj M :=
    { val := PresheafOfModules.ofPresheaf (skyscraperAbPresheaf R x M)
        (skyscraperAbPresheaf_map_smul R x M)
      isSheaf := isSheaf_skyscraperAbPresheaf R x M }
  map {M N} l :=
    ⟨PresheafOfModules.homMk
      { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
          (fun (s : PLift (x ∈ U.unop) → M) hx ↦ l (s hx))
          fun _ _ ↦ funext fun _ ↦ map_add l.hom _ _)
        naturality _ _ _ := rfl }
      fun U r (s : PLift (x ∈ U.unop) → M) ↦ funext fun ⟨hx⟩ ↦
        l.hom.map_smul (TopCat.Presheaf.germ R.obj U.unop x hx (r : R.obj.obj (op U.unop)))
          (s ⟨hx⟩)⟩
  map_id _ := by
    ext U : 2
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun (s : PLift (x ∈ U.unop) → _) ↦ funext fun _ ↦ rfl
  map_comp _ _ := by
    ext U : 2
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun (s : PLift (x ∈ U.unop) → _) ↦ funext fun _ ↦ rfl

/-- Over an open `U` containing `x`, sections of `(skyscraper R x).obj M` are additively
isomorphic to `M`. -/
def skyscraperSectionsEquiv (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x))
    {U : Opens X} (hx : x ∈ U) :
    (((skyscraper R x).obj M).val.obj (op U)) ≃+ M := by
  unfold skyscraper
  exact
    { toFun s := (s : PLift (x ∈ U) → M) ⟨hx⟩
      invFun m := (fun _ ↦ m : PLift (x ∈ U) → M)
      left_inv s := funext fun ⟨_⟩ ↦ rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }

/-- Construct a section of `(skyscraper R x).obj M` over an open `U` from its value whenever
`x ∈ U` (and `0` automatically when `x ∉ U`). -/
def skyscraperSectionMk (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x))
    {U : Opens X} (f : x ∈ U → M) : ((skyscraper R x).obj M).val.obj (op U) := by
  unfold skyscraper
  exact fun hx ↦ f hx.down

/-- Evaluating `skyscraperSectionMk R x M f` via `skyscraperSectionsEquiv` at `hx : x ∈ U`
returns `f hx`. -/
@[simp]
theorem skyscraperSectionsEquiv_skyscraperSectionMk
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x))
    {U : Opens X} (f : x ∈ U → M) (hx : x ∈ U) :
    skyscraperSectionsEquiv R x M hx (skyscraperSectionMk R x M f) = f hx := by
  unfold skyscraper skyscraperSectionsEquiv skyscraperSectionMk
  rfl

variable {R x} in
/-- Two sections of `(skyscraper R x).obj M` over an open `U` agree as soon as they agree under
`skyscraperSectionsEquiv` whenever `x ∈ U`. -/
theorem skyscraper_section_ext
    {M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x)}
    {U : Opens X} {s₁ s₂ : ((skyscraper R x).obj M).val.obj (op U)}
    (h : ∀ hx : x ∈ U,
      skyscraperSectionsEquiv R x M hx s₁ = skyscraperSectionsEquiv R x M hx s₂) :
    s₁ = s₂ := by
  unfold skyscraper skyscraperSectionsEquiv at *
  exact funext fun ⟨hx⟩ ↦ h hx

/-- A ring section `r ∈ R(U)` acts on `(skyscraper R x).obj M` through its germ `r_x` at `x`. -/
@[simp]
theorem skyscraperSectionsEquiv_smul (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x))
    {U : Opens X} (hx : x ∈ U) (r : R.obj.obj (op U))
    (s : ((skyscraper R x).obj M).val.obj (op U)) :
    skyscraperSectionsEquiv R x M hx (r • s) =
      TopCat.Presheaf.germ R.obj U x hx r • skyscraperSectionsEquiv R x M hx s := by
  unfold skyscraper skyscraperSectionsEquiv
  rfl

/-- Scalar multiplication on `(skyscraper R x).obj M` transports under
`(skyscraperSectionsEquiv R x M hx).symm` to multiplication by the ring germ at `x`. -/
@[simp]
theorem smul_skyscraperSectionsEquiv_symm (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x))
    {U : Opens X} (hx : x ∈ U) (r : R.obj.obj (op U)) (m : M) :
    (r : (ringCatSheaf R).obj.obj (op U)) • (skyscraperSectionsEquiv R x M hx).symm m =
      (skyscraperSectionsEquiv R x M hx).symm (TopCat.Presheaf.germ R.obj U x hx r • m) := by
  unfold skyscraper skyscraperSectionsEquiv
  rfl

/-- The identifications `skyscraperSectionsEquiv` commute with restriction along opens containing
`x`. -/
@[simp]
theorem skyscraperSectionsEquiv_map (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x))
    {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (s : ((skyscraper R x).obj M).val.obj (op V)) :
    skyscraperSectionsEquiv R x M hx (((skyscraper R x).obj M).val.map i.op s) =
      skyscraperSectionsEquiv R x M (i.le hx) s := by
  unfold skyscraper skyscraperSectionsEquiv
  rfl

/-- Functoriality of `skyscraper` acts on sections over `U ∋ x` by applying `l : M ⟶ N`. -/
@[simp]
theorem skyscraperSectionsEquiv_skyscraper_map_app
    {M N : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x)}
    (l : M ⟶ N) {U : Opens X} (hx : x ∈ U) (s : ((skyscraper R x).obj M).val.obj (op U)) :
    skyscraperSectionsEquiv R x N hx (((skyscraper R x).map l).val.app (op U) s) =
      l (skyscraperSectionsEquiv R x M hx s) := by
  unfold skyscraper skyscraperSectionsEquiv
  rfl

/-- Over an open `U` not containing `x`, the sections of `(skyscraper R x).obj M` vanish. -/
theorem subsingleton_skyscraper_obj_of_notMem
    (M : ModuleCat.{v} ↑(TopCat.Presheaf.stalk R.obj x)) {U : Opens X} (hx : x ∉ U) :
    Subsingleton (((skyscraper R x).obj M).val.obj (op U)) :=
  ⟨fun _ _ ↦ skyscraper_section_ext fun h ↦ absurd h hx⟩

end Skyscraper

section Adjunction

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)

private def toSkyscraperHom (G : SheafOfModules.{u} (ringCatSheaf R))
    (M : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) (l : (stalkFunctor R x).obj G ⟶ M) :
    G ⟶ (skyscraper.{u, u} R x).obj M := by
  letI := skyscraperObjModule R x M
  unfold skyscraper
  exact ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun (m : G.val.obj U) (hx : PLift (x ∈ U.unop)) ↦
          l (germ G.val.presheaf U.unop x hx.down m))
        fun m₁ m₂ ↦ funext fun hx ↦
          (congrArg l ((germ G.val.presheaf U.unop x hx.down).hom.map_add m₁ m₂)).trans
            (l.hom.map_add _ _))
      naturality U V i :=
        AddCommGrpCat.ext fun m ↦ funext fun hx ↦
          congrArg l (germ_res_apply G.val.presheaf i.unop x hx.down m) }
    fun U r m ↦ funext fun hx ↦
      (congrArg l (G.val.germ_smul (R := R.obj) x U.unop hx.down
        (r : R.obj.obj (op U.unop)) m)).trans (l.hom.map_smul _ _)⟩

private theorem skyscraperSectionsEquiv_toSkyscraperHom
    (G : SheafOfModules.{u} (ringCatSheaf R))
    (M : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) (l : (stalkFunctor R x).obj G ⟶ M)
    {U : Opens X} (hx : x ∈ U) (m : G.val.obj (op U)) :
    skyscraperSectionsEquiv R x M hx ((toSkyscraperHom R x G M l).val.app (op U) m) =
      l (germ G.val.presheaf U x hx m) := by
  let _ := skyscraperObjModule R x M
  unfold toSkyscraperHom skyscraperSectionsEquiv skyscraper
  rfl

private def fromSkyscraperHomSection {G : SheafOfModules.{u} (ringCatSheaf R)}
    {M : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)} (α : G ⟶ (skyscraper.{u, u} R x).obj M)
    (U : Opens X) (hx : x ∈ U) :
    G.val.obj (op U) →+ M :=
  AddMonoidHom.mk' (fun m ↦ skyscraperSectionsEquiv R x M hx (α.val.app (op U) m)) fun m₁ m₂ ↦ by
    rw [map_add, map_add]

private theorem fromSkyscraperHomSection_res {G : SheafOfModules.{u} (ringCatSheaf R)}
    {M : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)} (α : G ⟶ (skyscraper.{u, u} R x).obj M)
    {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U) (m : G.val.obj (op V)) :
    fromSkyscraperHomSection R x α U hx (G.val.map i.op m) =
      fromSkyscraperHomSection R x α V (i.le hx) m := by
  dsimp [fromSkyscraperHomSection]
  exact (congrArg (skyscraperSectionsEquiv R x M hx)
    (PresheafOfModules.naturality_apply α.val i.op m)).trans
      (skyscraperSectionsEquiv_map R x M i hx (α.val.app (op V) m))

private theorem fromSkyscraperHomSection_smul {G : SheafOfModules.{u} (ringCatSheaf R)}
    {M : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)} (α : G ⟶ (skyscraper.{u, u} R x).obj M)
    (U : Opens X) (hx : x ∈ U) (r : R.obj.obj (op U)) (m : G.val.obj (op U)) :
    fromSkyscraperHomSection R x α U hx (r • m) =
      TopCat.Presheaf.germ R.obj U x hx r • fromSkyscraperHomSection R x α U hx m := by
  dsimp [fromSkyscraperHomSection]
  exact (congrArg (skyscraperSectionsEquiv R x M hx)
    ((α.val.app (op U)).hom.map_smul (r : (ringCatSheaf R).obj.obj (op U)) m)).trans
      (skyscraperSectionsEquiv_smul R x M hx r (α.val.app (op U) m))

/-- Morphisms from the stalk of `G` at `x` to an `R_x`-module `M` correspond bijectively to
morphisms of sheaves of modules from `G` to the skyscraper sheaf `(skyscraper R x).obj M`. -/
def stalkSkyscraperHomEquiv (G : SheafOfModules.{u} (ringCatSheaf R))
    (M : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) :
    ((stalkFunctor R x).obj G ⟶ M) ≃ (G ⟶ (skyscraper.{u, u} R x).obj M) where
  toFun := toSkyscraperHom R x G M
  invFun α := ModuleCat.ofHom (G.val.stalkLiftCommRing (S := R.obj) (T := M) x
    (fromSkyscraperHomSection R x α) (fromSkyscraperHomSection_res R x α)
    (fromSkyscraperHomSection_smul R x α))
  left_inv l := by
    apply ModuleCat.hom_ext
    ext s
    obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq G.val.presheaf s
    exact (G.val.stalkLiftCommRing_germ (S := R.obj) (T := M) x
      (fromSkyscraperHomSection R x (toSkyscraperHom R x G M l))
      (fromSkyscraperHomSection_res R x _) (fromSkyscraperHomSection_smul R x _) U hx m).trans
        (skyscraperSectionsEquiv_toSkyscraperHom R x G M l hx m)
  right_inv α := by
    ext U : 2
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun m ↦ skyscraper_section_ext fun hx ↦ ?_
    exact (skyscraperSectionsEquiv_toSkyscraperHom R x G M
      (ModuleCat.ofHom (G.val.stalkLiftCommRing (S := R.obj) (T := M) x
        (fromSkyscraperHomSection R x α) (fromSkyscraperHomSection_res R x α)
        (fromSkyscraperHomSection_smul R x α))) hx m).trans
      (G.val.stalkLiftCommRing_germ (S := R.obj) (T := M) x
        (fromSkyscraperHomSection R x α)
        (fromSkyscraperHomSection_res R x α) (fromSkyscraperHomSection_smul R x α) U.unop hx m)

/-- The forward map of `stalkSkyscraperHomEquiv` evaluates `l` on germs at `x`. -/
@[simp]
theorem skyscraperSectionsEquiv_stalkSkyscraperHomEquiv
    (G : SheafOfModules.{u} (ringCatSheaf R))
    (M : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) (l : (stalkFunctor R x).obj G ⟶ M)
    {U : Opens X} (hx : x ∈ U) (m : G.val.obj (op U)) :
    skyscraperSectionsEquiv R x M hx ((stalkSkyscraperHomEquiv R x G M l).val.app (op U) m) =
      l (germ G.val.presheaf U x hx m) := by
  unfold stalkSkyscraperHomEquiv
  exact skyscraperSectionsEquiv_toSkyscraperHom R x G M l hx m

/-- The inverse of `stalkSkyscraperHomEquiv` evaluates a morphism into the skyscraper sheaf on
representative sections near `x`. -/
@[simp]
theorem stalkSkyscraperHomEquiv_symm_apply_germ (G : SheafOfModules.{u} (ringCatSheaf R))
    (M : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) (α : G ⟶ (skyscraper.{u, u} R x).obj M)
    (U : Opens X) (hx : x ∈ U) (m : G.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    ((stalkSkyscraperHomEquiv R x G M).symm α (germ G.val.presheaf U x hx m) =
      skyscraperSectionsEquiv R x M hx (α.val.app (op U) m)) := by
  unfold stalkSkyscraperHomEquiv
  exact G.val.stalkLiftCommRing_germ (S := R.obj) (T := M) x (fromSkyscraperHomSection R x α)
    (fromSkyscraperHomSection_res R x α) (fromSkyscraperHomSection_smul R x α) U hx m

/-- Taking the stalk at `x` is left adjoint to forming the skyscraper module sheaf at `x`. -/
def stalkSkyscraperAdjunction : stalkFunctor R x ⊣ skyscraper.{u, u} R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := stalkSkyscraperHomEquiv R x
      homEquiv_naturality_left_symm {G₁ G₂ M} f α := by
        apply ModuleCat.hom_ext
        ext s
        obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq G₁.val.presheaf s
        -- Unfold module composition to compare both sides on the germ of `m`.
        change (stalkSkyscraperHomEquiv R x G₁ M).symm (f ≫ α) (germ G₁.val.presheaf U x hx m) =
          (stalkSkyscraperHomEquiv R x G₂ M).symm α
            ((stalkFunctor R x).map f (germ G₁.val.presheaf U x hx m))
        erw [stalkSkyscraperHomEquiv_symm_apply_germ, stalkFunctor_map_germ,
          stalkSkyscraperHomEquiv_symm_apply_germ]
        rfl
      homEquiv_naturality_right {G M₁ M₂} l g := by
        ext U : 2
        apply ModuleCat.hom_ext
        refine LinearMap.ext fun m ↦ skyscraper_section_ext fun hx ↦ ?_
        exact (skyscraperSectionsEquiv_stalkSkyscraperHomEquiv R x G M₂ (l ≫ g) hx m).trans
          ((skyscraperSectionsEquiv_skyscraper_map_app R x g hx
            ((stalkSkyscraperHomEquiv R x G M₁ l).val.app (op U.unop) m)).trans
              (congrArg g
                (skyscraperSectionsEquiv_stalkSkyscraperHomEquiv R x G M₁ l hx m))).symm }

/-- The hom-set equivalence of `stalkSkyscraperAdjunction` is `stalkSkyscraperHomEquiv`. -/
@[simp]
theorem stalkSkyscraperAdjunction_homEquiv (G : SheafOfModules.{u} (ringCatSheaf R))
    (M : ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) :
    (stalkSkyscraperAdjunction R x).homEquiv G M = stalkSkyscraperHomEquiv R x G M :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) G) M

/-- The unit of `stalkSkyscraperAdjunction` sends a section over `U ∋ x` to its germ at `x`. -/
@[simp]
theorem skyscraperSectionsEquiv_stalkSkyscraperAdjunction_unit
    (G : SheafOfModules.{u} (ringCatSheaf R)) {U : Opens X} (hx : x ∈ U) (m : G.val.obj (op U)) :
    dsimp% only [Functor.id_obj, Functor.comp_obj]
    (skyscraperSectionsEquiv R x ((stalkFunctor R x).obj G) hx
        (((stalkSkyscraperAdjunction R x).unit.app G).val.app (op U) m) =
      germ G.val.presheaf U x hx m) := by
  rw [← Adjunction.homEquiv_id, stalkSkyscraperAdjunction_homEquiv,
    skyscraperSectionsEquiv_stalkSkyscraperHomEquiv]
  rfl

end Adjunction

end SheafOfModules

end
