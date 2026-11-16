/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
import TauCeti.AlgebraicGeometry.Modules.Pullback.Identity
import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Coherence
import TauCeti.AlgebraicGeometry.VectorBundle.Ample
import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Pullback

/-!
# Full faithfulness of formal completion on finite locally free sheaves

Let `X` be a scheme, `I` a quasicoherent sheaf of ideals on `X`, and `X/V(I)` the formal
completion of `X` along `V(I)`. This file establishes the formal-completion criterion for finite
locally free `𝒪_X`-modules (Stacks Project, Lemma 52.15.1, Tag `0EKP`).

For an `𝒪_X`-module `M`, a *formal global section* (`FormalSection X I M`) is a compatible system
of global sections `sₙ : 𝒪_{Xₙ} ⟶ (toScheme X I n)^* M` over the infinitesimal neighbourhoods
`Xₙ = V(I^{n+1})`. Pulling back global sections gives the comparison map
`globalSectionsToFormal X I M : (𝒪_X ⟶ M) → FormalSection X I M`.

Using internal Hom base change for finite locally free sheaves (`pullbackIhomIso`), morphisms
between completed finite locally free sheaves are canonically identified with formal global
sections of their internal Hom (`homCompletionEquivFormalSection`). Consequently, the completion
functor on finite locally free sheaves `completionFunctorFiniteLocallyFree X I` is faithful (resp.
fully faithful) if and only if `globalSectionsToFormal X I E.obj` is injective (resp. bijective)
for every finite locally free sheaf `E` on `X`.

When `X` is quasi-separated and carries an ample line bundle `L`, every finite locally free sheaf
`E` admits a universally exact resolution `0 → E → ⨁ L^{⊗ p} → ⨁ L^{⊗ q}` with `p, q` arbitrarily
large (`FiniteLocallyFreeSheaf.exists_universallyExact_ample_resolution`). Chasing global and
formal sections along this resolution reduces injectivity and bijectivity for all finite locally
free sheaves to the powers `L^{⊗ n}` for `n ≫ 0`. In particular, when `X` is quasi-affine, the
structure sheaf `𝒪_X` is ample, so injectivity or bijectivity of
`Γ(X, 𝒪_X) → limₙ Γ(V(I^{n+1}), 𝒪_{V(I^{n+1})})` already implies faithfulness or full
faithfulness of formal completion on all finite locally free sheaves.

## Main declarations

* `AlgebraicGeometry.Scheme.formalCompletion.FormalSection`: compatible systems of global sections
  of a sheaf of `𝒪_X`-modules over the infinitesimal neighbourhoods `V(I^{n+1})`.
* `AlgebraicGeometry.Scheme.formalCompletion.globalSectionsToFormal`: the canonical map from
  global sections of `M` to formal global sections of `M`.
* `AlgebraicGeometry.Scheme.formalCompletion.structureSectionsToFormal`: the canonical map
  `Γ(X, 𝒪_X) → limₙ Γ(V(I^{n+1}), 𝒪_{V(I^{n+1})})`.
* `AlgebraicGeometry.Scheme.formalCompletion.completionFunctorFiniteLocallyFree`: the completion
  functor from `FiniteLocallyFreeSheaf X` to `CoherentFormalModule (X.formalCompletion I)`.
* `AlgebraicGeometry.Scheme.formalCompletion.homCompletionEquivFormalSection`: natural equivalence
  between morphisms of completed finite locally free sheaves and formal global sections of their
  internal Hom.
* `AlgebraicGeometry.Scheme.formalCompletion.fullyFaithful_completionFunctorFiniteLocallyFree_iff`:
  equivalence `(3) ⇔ (4)` of Stacks `0EKP`.
* `AlgebraicGeometry.Scheme.formalCompletion.bijective_globalSectionsToFormal_of_isAmple` and
  `fullyFaithfulCompletionFunctorFiniteLocallyFreeOfIsAmple`: implications `(2) ⇒ (3) ⇒ (4)` of
  Stacks `0EKP`.
* `AlgebraicGeometry.Scheme.formalCompletion.bijective_globalSectionsToFormal_of_isQuasiAffine` and
  `fullyFaithfulCompletionFunctorFiniteLocallyFreeOfIsQuasiAffine`: implications `(1) ⇒ (3) ⇒ (4)`
  of Stacks `0EKP`.

## References

* [Stacks Project, Lemma 52.15.1](https://stacks.math.columbia.edu/tag/0EKP).
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

namespace AlgebraicGeometry.Scheme.formalCompletion

universe u

noncomputable section

/-! ### Formal global sections -/

section FormalSection

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- A compatible system of global sections of an `𝒪_X`-module `M` over the infinitesimal
neighbourhoods `V(I^{n+1})` of the formal completion `X/V(I)`. -/
@[ext]
structure FormalSection (M : X.Modules) where
  /-- The section at level `n`, as a morphism `𝒪_{Xₙ} ⟶ (toScheme X I n)^* M`. -/
  app : ∀ n, 𝟙_ ((X.formalCompletion I).X n).Modules ⟶
    (Modules.pullback (toScheme X I n)).obj M
  /-- Compatibility with the transition maps `ι n : Xₙ ⟶ X_{n+1}`. -/
  compatible : ∀ n,
    (Modules.pullbackObjUnitIso ((X.formalCompletion I).ι n)).inv ≫
      (Modules.pullback ((X.formalCompletion I).ι n)).map (app (n + 1)) ≫
      (Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
        Modules.pullbackCongr (ι_toScheme X I n)).hom.app M = app n

variable {X I}

/-- Post-composition of a formal global section along a morphism of `𝒪_X`-modules. -/
def FormalSection.map {M N : X.Modules} (f : M ⟶ N) (t : FormalSection X I M) :
    FormalSection X I N where
  app n := t.app n ≫ (Modules.pullback (toScheme X I n)).map f
  compatible n := by
    rw [Functor.map_comp, Category.assoc]
    have hnat := (Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
      Modules.pullbackCongr (ι_toScheme X I n)).hom.naturality f
    dsimp only [Functor.comp_map] at hnat
    rw [hnat, ← Category.assoc, ← Category.assoc, Category.assoc _ ((Modules.pullback _).map _),
      t.compatible n]

@[simp]
lemma FormalSection.map_app {M N : X.Modules} (f : M ⟶ N) (t : FormalSection X I M) (n : ℕ) :
    (t.map f).app n = t.app n ≫ (Modules.pullback (toScheme X I n)).map f := by
  unfold FormalSection.map
  rfl

@[simp]
lemma FormalSection.map_id {M : X.Modules} (t : FormalSection X I M) :
    t.map (𝟙 M) = t := by
  refine FormalSection.ext (funext fun n ↦ ?_)
  simp [FormalSection.map_app]

@[simp]
lemma FormalSection.map_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (t : FormalSection X I M) :
    (t.map f).map g = t.map (f ≫ g) := by
  refine FormalSection.ext (funext fun n ↦ ?_)
  simp [FormalSection.map_app]

/-- Equivalence of formal global sections induced by an isomorphism of `𝒪_X`-modules. -/
def FormalSection.congrIso {M N : X.Modules} (e : M ≅ N) :
    FormalSection X I M ≃ FormalSection X I N where
  toFun := FormalSection.map e.hom
  invFun := FormalSection.map e.inv
  left_inv t := by rw [FormalSection.map_comp, Iso.hom_inv_id, FormalSection.map_id]
  right_inv t := by rw [FormalSection.map_comp, Iso.inv_hom_id, FormalSection.map_id]

private lemma pullbackObjUnitIso_inv_comp_congr {Z Y X : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (hfg : f ≫ g = h) :
    (Modules.pullbackObjUnitIso f).inv ≫
      (Modules.pullback f).map (Modules.pullbackObjUnitIso g).inv ≫
      (Modules.pullbackComp f g ≪≫ Modules.pullbackCongr hfg).hom.app (𝟙_ X.Modules) =
    (Modules.pullbackObjUnitIso h).inv := by
  rw [Iso.trans_hom, NatTrans.comp_app, ← Category.assoc, ← Category.assoc,
    Category.assoc (Modules.pullbackObjUnitIso f).inv, Modules.pullbackObjUnitIso_inv_comp]
  subst hfg
  simp [Modules.pullbackCongr]

variable (X I)

/-- The canonical comparison map sending a global section `s : 𝒪_X ⟶ M` to the compatible system
of its pullbacks along `toScheme X I n : V(I^{n+1}) ⟶ X`. -/
def globalSectionsToFormal (M : X.Modules) (s : 𝟙_ X.Modules ⟶ M) : FormalSection X I M where
  app n := (Modules.pullbackObjUnitIso (toScheme X I n)).inv ≫
    (Modules.pullback (toScheme X I n)).map s
  compatible n := by
    rw [Functor.map_comp, Category.assoc]
    have hnat := (Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
      Modules.pullbackCongr (ι_toScheme X I n)).hom.naturality s
    dsimp only [Functor.comp_map] at hnat
    rw [hnat, ← Category.assoc, ← Category.assoc,
      Category.assoc (Modules.pullbackObjUnitIso _).inv,
      pullbackObjUnitIso_inv_comp_congr _ _ _ (ι_toScheme X I n)]

@[simp]
lemma globalSectionsToFormal_app (M : X.Modules) (s : 𝟙_ X.Modules ⟶ M) (n : ℕ) :
    (globalSectionsToFormal X I M s).app n =
      (Modules.pullbackObjUnitIso (toScheme X I n)).inv ≫
        (Modules.pullback (toScheme X I n)).map s := by
  unfold globalSectionsToFormal
  rfl

lemma globalSectionsToFormal_comp {M N : X.Modules} (f : M ⟶ N) (s : 𝟙_ X.Modules ⟶ M) :
    globalSectionsToFormal X I N (s ≫ f) = (globalSectionsToFormal X I M s).map f := by
  refine FormalSection.ext (funext fun n ↦ ?_)
  simp [globalSectionsToFormal_app, FormalSection.map_app]

/-- Injectivity of `globalSectionsToFormal` is invariant under isomorphism of `𝒪_X`-modules. -/
theorem injective_globalSectionsToFormal_iff_of_iso {M N : X.Modules} (e : M ≅ N) :
    Function.Injective (globalSectionsToFormal X I M) ↔
      Function.Injective (globalSectionsToFormal X I N) := by
  have hcomm (s : 𝟙_ X.Modules ⟶ M) :
      FormalSection.congrIso e (globalSectionsToFormal X I M s) =
        globalSectionsToFormal X I N (s ≫ e.hom) :=
    (globalSectionsToFormal_comp X I e.hom s).symm
  let eqHom : (𝟙_ X.Modules ⟶ M) ≃ (𝟙_ X.Modules ⟶ N) :=
    { toFun := fun s ↦ s ≫ e.hom
      invFun := fun s ↦ s ≫ e.inv
      left_inv := fun s ↦ by dsimp only; rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      right_inv := fun s ↦ by dsimp only; rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] }
  have hfn : (FormalSection.congrIso e) ∘ globalSectionsToFormal X I M =
      globalSectionsToFormal X I N ∘ eqHom := funext hcomm
  rw [← (FormalSection.congrIso e).injective.of_comp_iff (globalSectionsToFormal X I M), hfn,
    Function.Injective.of_comp_iff' _ eqHom.bijective]

/-- Bijectivity of `globalSectionsToFormal` is invariant under isomorphism of `𝒪_X`-modules. -/
theorem bijective_globalSectionsToFormal_iff_of_iso {M N : X.Modules} (e : M ≅ N) :
    Function.Bijective (globalSectionsToFormal X I M) ↔
      Function.Bijective (globalSectionsToFormal X I N) := by
  have hcomm (s : 𝟙_ X.Modules ⟶ M) :
      FormalSection.congrIso e (globalSectionsToFormal X I M s) =
        globalSectionsToFormal X I N (s ≫ e.hom) :=
    (globalSectionsToFormal_comp X I e.hom s).symm
  let eqHom : (𝟙_ X.Modules ⟶ M) ≃ (𝟙_ X.Modules ⟶ N) :=
    { toFun := fun s ↦ s ≫ e.hom
      invFun := fun s ↦ s ≫ e.inv
      left_inv := fun s ↦ by dsimp only; rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      right_inv := fun s ↦ by dsimp only; rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] }
  have hfn : (FormalSection.congrIso e) ∘ globalSectionsToFormal X I M =
      globalSectionsToFormal X I N ∘ eqHom := funext hcomm
  rw [← Function.Bijective.of_comp_iff' (FormalSection.congrIso e).bijective
    (globalSectionsToFormal X I M), hfn,
    Function.Bijective.of_comp_iff (globalSectionsToFormal X I N) eqHom.bijective]

/-- The canonical ring-level map `Γ(X, 𝒪_X) → limₙ Γ(V(I^{n+1}), 𝒪_{V(I^{n+1})})`. -/
def structureSectionsToFormal (r : Γ(X, ⊤)) :
    { s : ∀ n, Γ((X.formalCompletion I).X n, ⊤) //
      ∀ n, ((X.formalCompletion I).ι n).appTop (s (n + 1)) = s n } :=
  ⟨fun n ↦ (toScheme X I n).appTop r, fun n ↦ by
    dsimp only
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, ι_toScheme]⟩

/-- Formal global sections of the structure sheaf `𝒪_X` are canonically equivalent to compatible
systems of global functions on the infinitesimal neighbourhoods `V(I^{n+1})`. -/
def formalSectionUnitEquiv :
    FormalSection X I (𝟙_ X.Modules) ≃
      { s : ∀ n, Γ((X.formalCompletion I).X n, ⊤) //
        ∀ n, ((X.formalCompletion I).ι n).appTop (s (n + 1)) = s n } where
  toFun t :=
    ⟨fun n ↦ (Modules.globalSectionsActionRingEquiv (𝟙_ ((X.formalCompletion I).X n).Modules)).symm
      (End.of (t.app n ≫ (Modules.pullbackObjUnitIso (toScheme X I n)).hom)),
    fun n ↦ by
      refine (Modules.globalSectionsActionRingEquiv
        (𝟙_ ((X.formalCompletion I).X n).Modules)).injective (End.ext ?_)
      rw [Modules.globalSectionsActionRingEquiv_apply,
        Modules.globalSectionsActionRingEquiv_apply,
        Modules.globalSectionsSmul_globalSectionsActionRingEquiv_symm]
      let r1 := (Modules.globalSectionsActionRingEquiv
        (𝟙_ ((X.formalCompletion I).X (n + 1)).Modules)).symm
        (End.of (t.app (n + 1) ≫ (Modules.pullbackObjUnitIso (toScheme X I (n + 1))).hom))
      have hr1 : Modules.globalSectionsSmul (𝟙_ ((X.formalCompletion I).X (n + 1)).Modules) r1 =
          t.app (n + 1) ≫ (Modules.pullbackObjUnitIso (toScheme X I (n + 1))).hom :=
        Modules.globalSectionsSmul_globalSectionsActionRingEquiv_symm _ _
      have hsmul : Modules.globalSectionsSmul (𝟙_ ((X.formalCompletion I).X n).Modules)
          (((X.formalCompletion I).ι n).appTop r1) =
          (Modules.pullbackObjUnitIso ((X.formalCompletion I).ι n)).inv ≫
            (Modules.pullback ((X.formalCompletion I).ι n)).map
              (Modules.globalSectionsSmul (𝟙_ ((X.formalCompletion I).X (n + 1)).Modules) r1) ≫
            (Modules.pullbackObjUnitIso ((X.formalCompletion I).ι n)).hom := by
        rw [Modules.pullback_map_globalSectionsSmul,
          ← Modules.globalSectionsSmul_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
      change Modules.globalSectionsSmul (𝟙_ ((X.formalCompletion I).X n).Modules)
        (((X.formalCompletion I).ι n).appTop r1) =
        t.app n ≫ (Modules.pullbackObjUnitIso (toScheme X I n)).hom
      rw [hsmul, hr1, Functor.map_comp, Category.assoc]
      have hunit : (Modules.pullback ((X.formalCompletion I).ι n)).map
          (Modules.pullbackObjUnitIso (toScheme X I (n + 1))).hom ≫
          (Modules.pullbackObjUnitIso ((X.formalCompletion I).ι n)).hom =
          (Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
            Modules.pullbackCongr (ι_toScheme X I n)).hom.app (𝟙_ X.Modules) ≫
          (Modules.pullbackObjUnitIso (toScheme X I n)).hom := by
        rw [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
          Modules.pullbackObjUnitIso_congr (ι_toScheme X I n),
          ← Modules.pullbackObjUnitIso_comp, Iso.hom_inv_id_app_assoc]
      rw [hunit, ← Category.assoc, ← Category.assoc,
        Category.assoc (Modules.pullbackObjUnitIso _).inv, t.compatible n]⟩
  invFun s :=
    { app n := Modules.globalSectionsSmul (𝟙_ ((X.formalCompletion I).X n).Modules) (s.1 n) ≫
        (Modules.pullbackObjUnitIso (toScheme X I n)).inv
      compatible n := by
        rw [Functor.map_comp, Category.assoc, Modules.pullback_map_globalSectionsSmul,
          ← Modules.globalSectionsSmul_naturality_assoc, s.2 n,
          pullbackObjUnitIso_inv_comp_congr _ _ _ (ι_toScheme X I n)] }
  left_inv t := by
    refine FormalSection.ext (funext fun n ↦ ?_)
    dsimp only
    rw [Modules.globalSectionsSmul_globalSectionsActionRingEquiv_symm, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  right_inv s := by
    ext n
    dsimp only
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Modules.globalSectionsActionRingEquiv_symm_globalSectionsSmul]

lemma formalSectionUnitEquiv_globalSectionsToFormal (r : Γ(X, ⊤)) :
    formalSectionUnitEquiv X I
      (globalSectionsToFormal X I (𝟙_ X.Modules) (Modules.globalSectionsSmul (𝟙_ X.Modules) r)) =
      structureSectionsToFormal X I r := by
  ext n
  dsimp only [formalSectionUnitEquiv, Equiv.coe_fn_mk, structureSectionsToFormal]
  rw [globalSectionsToFormal_app, Category.assoc, Modules.pullback_map_globalSectionsSmul,
    ← Modules.globalSectionsSmul_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  exact Modules.globalSectionsActionRingEquiv_symm_globalSectionsSmul _ _

/-- Injectivity of `globalSectionsToFormal` on `𝒪_X` is equivalent to injectivity of
`Γ(X, 𝒪_X) → limₙ Γ(V(I^{n+1}), 𝒪_{V(I^{n+1})})`. -/
theorem injective_globalSectionsToFormal_unit_iff :
    Function.Injective (globalSectionsToFormal X I (𝟙_ X.Modules)) ↔
      Function.Injective (structureSectionsToFormal X I) := by
  let eqDom : Γ(X, ⊤) ≃ (𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :=
    (Modules.globalSectionsActionRingEquiv (𝟙_ X.Modules)).toEquiv.trans
      { toFun := fun f ↦ f.asHom
        invFun := End.of
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have hfn : (formalSectionUnitEquiv X I) ∘ globalSectionsToFormal X I (𝟙_ X.Modules) ∘ eqDom =
      structureSectionsToFormal X I :=
    funext fun r ↦ by
      change formalSectionUnitEquiv X I
        (globalSectionsToFormal X I (𝟙_ X.Modules)
          ((Modules.globalSectionsActionRingEquiv (𝟙_ X.Modules) r).asHom)) = _
      rw [Modules.globalSectionsActionRingEquiv_apply]
      exact formalSectionUnitEquiv_globalSectionsToFormal X I r
  rw [← hfn, (formalSectionUnitEquiv X I).injective.of_comp_iff,
    Function.Injective.of_comp_iff' _ eqDom.bijective]

/-- Bijectivity of `globalSectionsToFormal` on `𝒪_X` is equivalent to bijectivity of
`Γ(X, 𝒪_X) → limₙ Γ(V(I^{n+1}), 𝒪_{V(I^{n+1})})`. -/
theorem bijective_globalSectionsToFormal_unit_iff :
    Function.Bijective (globalSectionsToFormal X I (𝟙_ X.Modules)) ↔
      Function.Bijective (structureSectionsToFormal X I) := by
  let eqDom : Γ(X, ⊤) ≃ (𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :=
    (Modules.globalSectionsActionRingEquiv (𝟙_ X.Modules)).toEquiv.trans
      { toFun := fun f ↦ f.asHom
        invFun := End.of
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have hfn : (formalSectionUnitEquiv X I) ∘ globalSectionsToFormal X I (𝟙_ X.Modules) ∘ eqDom =
      structureSectionsToFormal X I :=
    funext fun r ↦ by
      change formalSectionUnitEquiv X I
        (globalSectionsToFormal X I (𝟙_ X.Modules)
          ((Modules.globalSectionsActionRingEquiv (𝟙_ X.Modules) r).asHom)) = _
      rw [Modules.globalSectionsActionRingEquiv_apply]
      exact formalSectionUnitEquiv_globalSectionsToFormal X I r
  rw [← hfn, Function.Bijective.of_comp_iff' (formalSectionUnitEquiv X I).bijective,
    Function.Bijective.of_comp_iff _ eqDom.bijective]

/-! ### Finite direct sums and universally exact sequences -/

private lemma injective_globalSectionsToFormal_of_bicone {ι : Type*} [Fintype ι]
    (A : ι → X.Modules) (P : X.Modules)
    (ιP : ∀ i, A i ⟶ P) (πP : ∀ i, P ⟶ A i)
    (htotal : ∑ i : ι, πP i ≫ ιP i = 𝟙 P)
    (hA : ∀ i, Function.Injective (globalSectionsToFormal X I (A i))) :
    Function.Injective (globalSectionsToFormal X I P) := by
  intro s₁ s₂ h
  have hi (i : ι) : s₁ ≫ πP i = s₂ ≫ πP i := by
    apply hA i
    rw [globalSectionsToFormal_comp, globalSectionsToFormal_comp, h]
  calc s₁ = s₁ ≫ 𝟙 P := (Category.comp_id s₁).symm
    _ = s₁ ≫ ∑ i : ι, πP i ≫ ιP i := by rw [htotal]
    _ = ∑ i : ι, (s₁ ≫ πP i) ≫ ιP i := by
      rw [Preadditive.comp_sum]
      exact Finset.sum_congr rfl fun i _ ↦ (Category.assoc _ _ _).symm
    _ = ∑ i : ι, (s₂ ≫ πP i) ≫ ιP i := Finset.sum_congr rfl fun i _ ↦ by rw [hi i]
    _ = s₂ ≫ ∑ i : ι, πP i ≫ ιP i := by
      rw [Preadditive.comp_sum]
      exact Finset.sum_congr rfl fun i _ ↦ Category.assoc _ _ _
    _ = s₂ := by rw [htotal, Category.comp_id]

private lemma bijective_globalSectionsToFormal_of_bicone {ι : Type*} [Fintype ι]
    (A : ι → X.Modules) (P : X.Modules)
    (ιP : ∀ i, A i ⟶ P) (πP : ∀ i, P ⟶ A i)
    (htotal : ∑ i : ι, πP i ≫ ιP i = 𝟙 P)
    (hA : ∀ i, Function.Bijective (globalSectionsToFormal X I (A i))) :
    Function.Bijective (globalSectionsToFormal X I P) := by
  refine ⟨injective_globalSectionsToFormal_of_bicone X I A P ιP πP htotal
    fun i ↦ (hA i).1, fun t ↦ ?_⟩
  choose s hs using fun i ↦ (hA i).2 (t.map (πP i))
  refine ⟨∑ i : ι, s i ≫ ιP i, FormalSection.ext (funext fun n ↦ ?_)⟩
  have hcomp (i : ι) :
      ((Modules.pullbackObjUnitIso (toScheme X I n)).inv ≫
        (Modules.pullback (toScheme X I n)).map (s i)) ≫
        (Modules.pullback (toScheme X I n)).map (ιP i) =
      t.app n ≫ (Modules.pullback (toScheme X I n)).map (πP i ≫ ιP i) := by
    have hsi := congrArg (fun u ↦ u.app n) (hs i)
    simp only [globalSectionsToFormal_app, FormalSection.map_app] at hsi
    rw [hsi, Category.assoc, ← Functor.map_comp]
  calc (globalSectionsToFormal X I P (∑ i : ι, s i ≫ ιP i)).app n
      = (Modules.pullbackObjUnitIso (toScheme X I n)).inv ≫
          ∑ i : ι, (Modules.pullback (toScheme X I n)).map (s i ≫ ιP i) := by
        rw [globalSectionsToFormal_app, Functor.map_sum]
    _ = ∑ i : ι, ((Modules.pullbackObjUnitIso (toScheme X I n)).inv ≫
          (Modules.pullback (toScheme X I n)).map (s i)) ≫
          (Modules.pullback (toScheme X I n)).map (ιP i) := by
        rw [Preadditive.comp_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Functor.map_comp, Category.assoc]
    _ = ∑ i : ι, t.app n ≫ (Modules.pullback (toScheme X I n)).map (πP i ≫ ιP i) :=
        Finset.sum_congr rfl fun i _ ↦ hcomp i
    _ = t.app n ≫ (Modules.pullback (toScheme X I n)).map (∑ i : ι, πP i ≫ ιP i) := by
        rw [Functor.map_sum, Preadditive.comp_sum]
    _ = t.app n := by rw [htotal, CategoryTheory.Functor.map_id, Category.comp_id]

private lemma injective_globalSectionsToFormal_of_universallyExact
    {E P Q : X.Modules} (α : E ⟶ P) (β : P ⟶ Q) (hαβ : α ≫ β = 0)
    (hlim : ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
      Nonempty (IsLimit (KernelFork.ofι ((Modules.pullback g).map α)
        (show (Modules.pullback g).map α ≫ (Modules.pullback g).map β = 0 by
          rw [← Functor.map_comp, hαβ]
          exact (Modules.pullback g).map_zero _ _))))
    (hP : Function.Injective (globalSectionsToFormal X I P)) :
    Function.Injective (globalSectionsToFormal X I E) := by
  obtain ⟨hlimId⟩ := hlim (𝟙 X)
  have hmonoId : Mono ((Modules.pullback (𝟙 X)).map α) := Limits.mono_of_isLimit_fork hlimId
  have hα_eq : α = (Modules.pullbackId X).inv.app E ≫ (Modules.pullback (𝟙 X)).map α ≫
      (Modules.pullbackId X).hom.app P := by
    have hnat := (Modules.pullbackId X).hom.naturality α
    dsimp only [Functor.id_map] at hnat
    rw [hnat, Iso.inv_hom_id_app_assoc]
  have : Mono α := by rw [hα_eq]; infer_instance
  intro s₁ s₂ h
  have h' : s₁ ≫ α = s₂ ≫ α := by
    apply hP
    rw [globalSectionsToFormal_comp, globalSectionsToFormal_comp, h]
  exact (cancel_mono α).mp h'

private lemma bijective_globalSectionsToFormal_of_universallyExact
    {E P Q : X.Modules} (α : E ⟶ P) (β : P ⟶ Q) (hαβ : α ≫ β = 0)
    (hlim : ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
      Nonempty (IsLimit (KernelFork.ofι ((Modules.pullback g).map α)
        (show (Modules.pullback g).map α ≫ (Modules.pullback g).map β = 0 by
          rw [← Functor.map_comp, hαβ]
          exact (Modules.pullback g).map_zero _ _))))
    (hP : Function.Bijective (globalSectionsToFormal X I P))
    (hQ : Function.Injective (globalSectionsToFormal X I Q)) :
    Function.Bijective (globalSectionsToFormal X I E) := by
  refine ⟨injective_globalSectionsToFormal_of_universallyExact X I α β hαβ hlim hP.1, fun t ↦ ?_⟩
  obtain ⟨p, hp⟩ := hP.2 (t.map α)
  have hpβ : p ≫ β = 0 := by
    apply hQ
    rw [globalSectionsToFormal_comp, hp, FormalSection.map_comp, hαβ]
    refine FormalSection.ext (funext fun n ↦ ?_)
    simp [globalSectionsToFormal_app, FormalSection.map_app]
  obtain ⟨hlimId⟩ := hlim (𝟙 X)
  have hnatβ := (Modules.pullbackId X).inv.naturality β
  dsimp only [Functor.id_map] at hnatβ
  have hpβ_id : (p ≫ (Modules.pullbackId X).inv.app P) ≫ (Modules.pullback (𝟙 X)).map β = 0 := by
    rw [Category.assoc, ← hnatβ, ← Category.assoc, hpβ, Limits.zero_comp]
  let fork := KernelFork.ofι (p ≫ (Modules.pullbackId X).inv.app P) hpβ_id
  let e : 𝟙_ X.Modules ⟶ E := hlimId.lift fork ≫ (Modules.pullbackId X).hom.app E
  have heα : e ≫ α = p := by
    have hnatα := (Modules.pullbackId X).hom.naturality α
    dsimp only [Functor.id_map] at hnatα
    have hfac : hlimId.lift fork ≫ (Modules.pullback (𝟙 X)).map α =
        p ≫ (Modules.pullbackId X).inv.app P := hlimId.fac fork .zero
    dsimp only [e]
    rw [Category.assoc, ← hnatα, ← Category.assoc, hfac, Category.assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
    rw [Category.comp_id]
  refine ⟨e, FormalSection.ext (funext fun n ↦ ?_)⟩
  obtain ⟨hlimn⟩ := hlim (toScheme X I n)
  have hmonon : Mono ((Modules.pullback (toScheme X I n)).map α) :=
    Limits.mono_of_isLimit_fork hlimn
  apply (cancel_mono ((Modules.pullback (toScheme X I n)).map α)).mp
  have h1 := congrArg (fun u ↦ u.app n) (globalSectionsToFormal_comp X I α e)
  have h2 := congrArg (fun u ↦ u.app n) hp
  simp only [globalSectionsToFormal_app, FormalSection.map_app] at h1 h2
  rw [globalSectionsToFormal_app, ← h1, heα, h2]

end FormalSection

/-! ### Internal-Hom correspondence on finite locally free sheaves (`(3) ⇔ (4)`) -/

section CompletionFunctor

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The formal completion functor restricted to finite locally free `𝒪_X`-modules. -/
@[expose]
def completionFunctorFiniteLocallyFree :
    FiniteLocallyFreeSheaf X ⥤ CoherentFormalModule (X.formalCompletion I) :=
  FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙ completionFunctor X I

instance : (completionFunctorFiniteLocallyFree X I).Additive where
  map_add := CoherentFormalModule.hom_ext fun _ ↦ (Modules.pullback _).map_add

@[simp]
lemma completionFunctorFiniteLocallyFree_obj_obj (E : FiniteLocallyFreeSheaf X) (n : ℕ) :
    ((completionFunctorFiniteLocallyFree X I).obj E).obj n =
      (Modules.pullback (toScheme X I n)).obj E.obj :=
  (rfl)

@[simp]
lemma completionFunctorFiniteLocallyFree_obj_transitionIso (E : FiniteLocallyFreeSheaf X) (n : ℕ) :
    ((completionFunctorFiniteLocallyFree X I).obj E).transitionIso n =
      (Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
        Modules.pullbackCongr (ι_toScheme X I n)).app E.obj :=
  (rfl)

@[simp]
lemma completionFunctorFiniteLocallyFree_map_app {E F : FiniteLocallyFreeSheaf X} (f : E ⟶ F)
    (n : ℕ) :
    ((completionFunctorFiniteLocallyFree X I).map f).app n =
      (Modules.pullback (toScheme X I n)).map f.hom :=
  (rfl)

@[reassoc]
private lemma pullbackIhomComparison_congr {Z Y : Scheme.{u}} {f' f : Z ⟶ Y} (hf : f' = f)
    (M N : Y.Modules) [M.IsQuasicoherent] :
    (pullbackIhomComparison M f').app N ≫
      (ihom ((Modules.pullback f').obj M)).map ((Modules.pullbackCongr hf).hom.app N) =
    (Modules.pullbackCongr hf).hom.app ((ihom M).obj N) ≫
      (pullbackIhomComparison M f).app N ≫
      (pre ((Modules.pullbackCongr hf).hom.app M)).app ((Modules.pullback f).obj N) := by
  subst hf
  simp [Modules.pullbackCongr]

private lemma pullbackIhomComparison_comp_congr {Z Y W : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ W) (h : Z ⟶ W) (hfg : f ≫ g = h)
    (M N : W.Modules) [M.IsQuasicoherent] :
    (Modules.pullback f).map ((pullbackIhomComparison M g).app N) ≫
      (pullbackIhomComparison ((Modules.pullback g).obj M) f).app ((Modules.pullback g).obj N) ≫
      (ihom ((Modules.pullback f).obj ((Modules.pullback g).obj M))).map
        ((Modules.pullbackComp f g ≪≫ Modules.pullbackCongr hfg).hom.app N) =
    (Modules.pullbackComp f g ≪≫ Modules.pullbackCongr hfg).hom.app ((ihom M).obj N) ≫
      (pullbackIhomComparison M h).app N ≫
      (pre ((Modules.pullbackComp f g ≪≫ Modules.pullbackCongr hfg).hom.app M)).app
        ((Modules.pullback h).obj N) := by
  rw [Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc,
    pullbackIhomComparison_comp_assoc f g M N,
    pre_comm_ihom_map, pullbackIhomComparison_congr_assoc hfg M N, pre_map]
  simp only [NatTrans.comp_app]

@[reassoc]
private lemma pullback_curry_rightUnitor_comp {Z Y : Scheme.{u}} (h : Z ⟶ Y)
    {M N : Y.Modules} [M.IsQuasicoherent] (ψ : M ⟶ N) :
    (Modules.pullbackObjUnitIso h).inv ≫
      (Modules.pullback h).map (curry ((ρ_ M).hom ≫ ψ)) ≫
      (pullbackIhomComparison M h).app N =
    curry ((ρ_ ((Modules.pullback h).obj M)).hom ≫ (Modules.pullback h).map ψ) := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_eq]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    whiskerLeft_pullbackIhomComparison_app_comp_ev]
  have hδ : ((Modules.pullback h).obj M ◁
      (Modules.pullback h).map (curry ((ρ_ M).hom ≫ ψ))) ≫
      inv (Functor.OplaxMonoidal.δ (Modules.pullback h) M ((ihom M).obj N)) =
      inv (Functor.OplaxMonoidal.δ (Modules.pullback h) M (𝟙_ Y.Modules)) ≫
      (Modules.pullback h).map (M ◁ curry ((ρ_ M).hom ≫ ψ)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← Functor.OplaxMonoidal.δ_natural_right,
      IsIso.inv_hom_id_assoc]
  rw [← Category.assoc ((Modules.pullback h).obj M ◁ (Modules.pullback h).map _), hδ,
    Category.assoc, ← Functor.map_comp, whiskerLeft_curry_ihom_ev_app, Functor.map_comp]
  have hru := Functor.OplaxMonoidal.right_unitality (Modules.pullback h) M
  rw [Modules.pullback_η] at hru
  have hleft :
      ((Modules.pullback h).obj M ◁ (Modules.pullbackObjUnitIso h).inv) ≫
        inv (Functor.OplaxMonoidal.δ (Modules.pullback h) M (𝟙_ Y.Modules)) ≫
        (Modules.pullback h).map (ρ_ M).hom =
      (ρ_ ((Modules.pullback h).obj M)).hom := by
    apply (cancel_epi (ρ_ ((Modules.pullback h).obj M)).inv).mp
    rw [Iso.inv_hom_id, ← Category.assoc, ← Category.assoc, hru]
    simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, IsIso.hom_inv_id_assoc,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rw [← Category.assoc, ← Category.assoc, Category.assoc ((Modules.pullback h).obj M ◁ _), hleft]

private lemma curry_rightUnitor_comp_naturality {Z : Scheme.{u}}
    {M₁ M₂ N₁ N₂ : Z.Modules} (eM : M₁ ⟶ M₂) (eN : N₁ ⟶ N₂)
    (φ₁ : M₁ ⟶ N₁) (φ₂ : M₂ ⟶ N₂) :
    curry ((ρ_ M₁).hom ≫ φ₁) ≫ (ihom M₁).map eN =
      curry ((ρ_ M₂).hom ≫ φ₂) ≫ (pre eM).app N₂ ↔
    φ₁ ≫ eN = eM ≫ φ₂ := by
  rw [← curry_natural_right, curry_pre_app, Category.assoc, ← Category.assoc (eM ▷ _),
    rightUnitor_naturality, Category.assoc]
  constructor
  · intro h
    have h' := congrArg uncurry h
    rw [uncurry_curry, uncurry_curry] at h'
    exact (cancel_epi (ρ_ M₁).hom).mp (by simpa only [Category.assoc] using h')
  · intro h
    rw [h]

@[reassoc]
private lemma pullbackIhomIso_inv_comp_comparison {Z Y : Scheme.{u}}
    (G : FiniteLocallyFreeSheaf Y) (f : Z ⟶ Y) (F : Y.Modules) :
    (FiniteLocallyFreeSheaf.pullbackIhomIso G f).inv.app F ≫
      (pullbackIhomComparison G.obj f).app F =
      𝟙 ((ihom ((Modules.pullback f).obj G.obj)).obj ((Modules.pullback f).obj F)) := by
  rw [← FiniteLocallyFreeSheaf.pullbackIhomIso_hom]
  exact (FiniteLocallyFreeSheaf.pullbackIhomIso G f).inv_hom_id_app F

@[reassoc]
private lemma pullbackIhomComparison_comp_iso_inv {Z Y : Scheme.{u}}
    (G : FiniteLocallyFreeSheaf Y) (f : Z ⟶ Y) (F : Y.Modules) :
    (pullbackIhomComparison G.obj f).app F ≫
      (FiniteLocallyFreeSheaf.pullbackIhomIso G f).inv.app F =
      𝟙 ((Modules.pullback f).obj ((ihom G.obj).obj F)) := by
  rw [← FiniteLocallyFreeSheaf.pullbackIhomIso_hom]
  exact (FiniteLocallyFreeSheaf.pullbackIhomIso G f).hom_inv_id_app F

private lemma homCompletionToFormalSection_compatible {G F : FiniteLocallyFreeSheaf X}
    (φ : (completionFunctorFiniteLocallyFree X I).obj G ⟶
      (completionFunctorFiniteLocallyFree X I).obj F) (n : ℕ) :
    let φn : (Modules.pullback (toScheme X I n)).obj G.obj ⟶
        (Modules.pullback (toScheme X I n)).obj F.obj := φ.app n
    let φn1 : (Modules.pullback (toScheme X I (n + 1))).obj G.obj ⟶
        (Modules.pullback (toScheme X I (n + 1))).obj F.obj := φ.app (n + 1)
    (Modules.pullbackObjUnitIso ((X.formalCompletion I).ι n)).inv ≫
      (Modules.pullback ((X.formalCompletion I).ι n)).map
        (curry ((ρ_ _).hom ≫ φn1) ≫
          ((FiniteLocallyFreeSheaf.pullbackIhomIso G (toScheme X I (n + 1))).inv.app F.obj)) ≫
      (Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
        Modules.pullbackCongr (ι_toScheme X I n)).hom.app ((ihom G.obj).obj F.obj) =
    curry ((ρ_ _).hom ≫ φn) ≫
      ((FiniteLocallyFreeSheaf.pullbackIhomIso G (toScheme X I n)).inv.app F.obj) := by
  intro φn φn1
  let ιn := (X.formalCompletion I).ι n
  let fn := toScheme X I n
  let fn1 := toScheme X I (n + 1)
  let τn := Modules.pullbackComp ιn fn1 ≪≫ Modules.pullbackCongr (ι_toScheme X I n)
  have : ((Modules.pullback fn1).obj G.obj).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback fn1 G.obj
  have : IsIso ((pre (τn.hom.app G.obj)).app ((Modules.pullback fn).obj F.obj)) :=
    (NatTrans.isIso_iff_isIso_app _).mp (pre_isIso (τn.app G.obj)) _
  have : IsIso ((pullbackIhomComparison G.obj fn).app F.obj) := by
    rw [← FiniteLocallyFreeSheaf.pullbackIhomIso_hom]
    exact (NatTrans.isIso_iff_isIso_app _).mp
      (FiniteLocallyFreeSheaf.pullbackIhomIso G fn).isIso_hom F.obj
  apply (cancel_mono ((pullbackIhomComparison G.obj fn).app F.obj)).mp
  apply (cancel_mono ((pre (τn.hom.app G.obj)).app ((Modules.pullback fn).obj F.obj))).mp
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
    Category.assoc (curry ((ρ_ _).hom ≫ φn)),
    pullbackIhomIso_inv_comp_comparison_assoc]
  rw [← pullbackIhomComparison_comp_congr ιn fn1 fn (ι_toScheme X I n) G.obj F.obj]
  rw [Functor.map_comp, Category.assoc]
  have hcancel1 {W : ((X.formalCompletion I).X n).Modules}
      (u : (ihom ((Modules.pullback fn1).obj G.obj) ⋙ Modules.pullback ιn).obj
        ((Modules.pullback fn1).obj F.obj) ⟶ W) :
      (Modules.pullback ιn).map
        ((FiniteLocallyFreeSheaf.pullbackIhomIso G fn1).inv.app F.obj) ≫
        (Modules.pullback ιn).map ((pullbackIhomComparison G.obj fn1).app F.obj) ≫ u = u := by
    have h := congrArg (· ≫ u) (show (Modules.pullback ιn).map
        ((FiniteLocallyFreeSheaf.pullbackIhomIso G fn1).inv.app F.obj) ≫
        (Modules.pullback ιn).map ((pullbackIhomComparison G.obj fn1).app F.obj) = 𝟙 _ by
      rw [← Functor.map_comp, pullbackIhomIso_inv_comp_comparison]
      exact (Modules.pullback ιn).map_id _)
    exact (Category.assoc _ _ u).symm.trans (h.trans (Category.id_comp u))
  rw [hcancel1, pullback_curry_rightUnitor_comp_assoc ιn φn1]
  exact (curry_rightUnitor_comp_naturality (τn.hom.app G.obj) (τn.hom.app F.obj)
    ((Modules.pullback ιn).map φn1) φn).mpr (φ.naturality n)

private lemma formalSectionToHomCompletion_naturality {G F : FiniteLocallyFreeSheaf X}
    (s : FormalSection X I ((ihom G.obj).obj F.obj)) (n : ℕ) :
    let ψn : (Modules.pullback (toScheme X I n)).obj G.obj ⟶
        (Modules.pullback (toScheme X I n)).obj F.obj :=
      (ρ_ ((Modules.pullback (toScheme X I n)).obj G.obj)).inv ≫
        uncurry (s.app n ≫ (pullbackIhomComparison G.obj (toScheme X I n)).app F.obj)
    let ψn1 : (Modules.pullback (toScheme X I (n + 1))).obj G.obj ⟶
        (Modules.pullback (toScheme X I (n + 1))).obj F.obj :=
      (ρ_ ((Modules.pullback (toScheme X I (n + 1))).obj G.obj)).inv ≫
        uncurry (s.app (n + 1) ≫ (pullbackIhomComparison G.obj (toScheme X I (n + 1))).app F.obj)
    (Modules.pullback ((X.formalCompletion I).ι n)).map ψn1 ≫
      (Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
        Modules.pullbackCongr (ι_toScheme X I n)).hom.app F.obj =
    (Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
      Modules.pullbackCongr (ι_toScheme X I n)).hom.app G.obj ≫ ψn := by
  intro ψn ψn1
  let ιn := (X.formalCompletion I).ι n
  let fn := toScheme X I n
  let fn1 := toScheme X I (n + 1)
  let τn := Modules.pullbackComp ιn fn1 ≪≫ Modules.pullbackCongr (ι_toScheme X I n)
  have hGn1_qc : ((Modules.pullback fn1).obj G.obj).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback fn1 G.obj
  apply (curry_rightUnitor_comp_naturality (τn.hom.app G.obj) (τn.hom.app F.obj)
    ((Modules.pullback ιn).map ψn1) ψn).mp
  dsimp only [Functor.comp_obj]
  rw [← pullback_curry_rightUnitor_comp ιn ψn1]
  have h1 : curry ((ρ_ ((Modules.pullback fn1).obj G.obj)).hom ≫ ψn1) =
      s.app (n + 1) ≫ (pullbackIhomComparison G.obj fn1).app F.obj := by
    dsimp only [ψn1]
    rw [Iso.hom_inv_id_assoc, curry_uncurry]
  have h0 : curry ((ρ_ ((Modules.pullback fn).obj G.obj)).hom ≫ ψn) =
      s.app n ≫ (pullbackIhomComparison G.obj fn).app F.obj := by
    dsimp only [ψn]
    rw [Iso.hom_inv_id_assoc, curry_uncurry]
  rw [h1, h0, Functor.map_comp, Category.assoc, Category.assoc, Category.assoc,
    pullbackIhomComparison_comp_congr ιn fn1 fn (ι_toScheme X I n) G.obj F.obj,
    ← Category.assoc, ← Category.assoc, ← Category.assoc,
    Category.assoc (Modules.pullbackObjUnitIso ιn).inv, s.compatible n, Category.assoc]

/-- For finite locally free sheaves `G` and `F` on `X`, morphisms between their formal completions
correspond canonically to formal global sections of the internal Hom `𝓗om(G, F)`. -/
def homCompletionEquivFormalSection (G F : FiniteLocallyFreeSheaf X) :
    ((completionFunctorFiniteLocallyFree X I).obj G ⟶
      (completionFunctorFiniteLocallyFree X I).obj F) ≃
      FormalSection X I ((ihom G.obj).obj F.obj) where
  toFun φ :=
    { app n :=
        let φn : (Modules.pullback (toScheme X I n)).obj G.obj ⟶
            (Modules.pullback (toScheme X I n)).obj F.obj := φ.app n
        curry ((ρ_ _).hom ≫ φn) ≫
          ((FiniteLocallyFreeSheaf.pullbackIhomIso G (toScheme X I n)).inv.app F.obj)
      compatible n := homCompletionToFormalSection_compatible X I φ n }
  invFun s :=
    { app n :=
        (ρ_ ((Modules.pullback (toScheme X I n)).obj G.obj)).inv ≫
          uncurry (s.app n ≫ (pullbackIhomComparison G.obj (toScheme X I n)).app F.obj)
      naturality n := formalSectionToHomCompletion_naturality X I s n }
  left_inv φ := CoherentFormalModule.hom_ext fun n ↦ by
    let φn : (Modules.pullback (toScheme X I n)).obj G.obj ⟶
        (Modules.pullback (toScheme X I n)).obj F.obj := φ.app n
    change (ρ_ ((Modules.pullback (toScheme X I n)).obj G.obj)).inv ≫
        uncurry ((curry ((ρ_ _).hom ≫ φn) ≫
          (FiniteLocallyFreeSheaf.pullbackIhomIso G (toScheme X I n)).inv.app F.obj) ≫
          (pullbackIhomComparison G.obj (toScheme X I n)).app F.obj) = φn
    rw [Category.assoc, pullbackIhomIso_inv_comp_comparison, Category.comp_id, uncurry_curry,
      Iso.inv_hom_id_assoc]
  right_inv s := FormalSection.ext (funext fun n ↦ by
    change curry ((ρ_ ((Modules.pullback (toScheme X I n)).obj G.obj)).hom ≫
        (ρ_ ((Modules.pullback (toScheme X I n)).obj G.obj)).inv ≫
          uncurry (s.app n ≫ (pullbackIhomComparison G.obj (toScheme X I n)).app F.obj)) ≫
        (FiniteLocallyFreeSheaf.pullbackIhomIso G (toScheme X I n)).inv.app F.obj = s.app n
    rw [Iso.hom_inv_id_assoc, curry_uncurry, Category.assoc,
      pullbackIhomComparison_comp_iso_inv, Category.comp_id])

lemma homCompletionEquivFormalSection_map {G F : FiniteLocallyFreeSheaf X} (f : G ⟶ F) :
    homCompletionEquivFormalSection X I G F ((completionFunctorFiniteLocallyFree X I).map f) =
      globalSectionsToFormal X I ((ihom G.obj).obj F.obj) (curry ((ρ_ G.obj).hom ≫ f.hom)) := by
  refine FormalSection.ext (funext fun n ↦ ?_)
  change curry ((ρ_ ((Modules.pullback (toScheme X I n)).obj G.obj)).hom ≫
      (Modules.pullback (toScheme X I n)).map f.hom) ≫
      (FiniteLocallyFreeSheaf.pullbackIhomIso G (toScheme X I n)).inv.app F.obj =
    (globalSectionsToFormal X I ((ihom G.obj).obj F.obj) (curry ((ρ_ G.obj).hom ≫ f.hom))).app n
  rw [globalSectionsToFormal_app, ← pullback_curry_rightUnitor_comp (toScheme X I n) f.hom,
    Category.assoc, Category.assoc, pullbackIhomComparison_comp_iso_inv, Category.comp_id]

private def ihomUnitIso (M : X.Modules) : (ihom (𝟙_ X.Modules)).obj M ≅ M where
  hom := (λ_ _).inv ≫ (ihom.ev (𝟙_ X.Modules)).app M
  inv := curry (λ_ M).hom
  hom_inv_id := by
    apply uncurry_injective
    rw [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      whiskerLeft_curry_ihom_ev_app]
    have hnat := leftUnitor_naturality
      ((λ_ ((ihom (𝟙_ X.Modules)).obj M)).inv ≫ (ihom.ev (𝟙_ X.Modules)).app M)
    dsimp only [Functor.id_obj] at hnat
    rw [hnat, Iso.hom_inv_id_assoc, uncurry_id_eq_ev]
  inv_hom_id := by
    have hnat := leftUnitor_inv_naturality (curry (λ_ M).hom)
    rw [← Category.assoc, hnat, Category.assoc, whiskerLeft_curry_ihom_ev_app, Iso.inv_hom_id]

/-- Faithfulness of formal completion on finite locally free sheaves is equivalent to injectivity
of `globalSectionsToFormal` on every finite locally free sheaf. -/
theorem faithful_completionFunctorFiniteLocallyFree_iff :
    (completionFunctorFiniteLocallyFree X I).Faithful ↔
      ∀ E : FiniteLocallyFreeSheaf X, Function.Injective (globalSectionsToFormal X I E.obj) := by
  constructor
  · intro hF E
    let U : FiniteLocallyFreeSheaf X := ⟨𝟙_ X.Modules, (Modules.isFiniteLocallyFree X).prop_unit⟩
    rw [← injective_globalSectionsToFormal_iff_of_iso X I (ihomUnitIso X E.obj)]
    let eqHom : (U ⟶ E) ≃ (𝟙_ X.Modules ⟶ (ihom U.obj).obj E.obj) :=
      { toFun := fun f ↦ curry ((ρ_ U.obj).hom ≫ f.hom)
        invFun := fun s ↦ ObjectProperty.homMk ((ρ_ U.obj).inv ≫ uncurry s)
        left_inv := fun f ↦ ObjectProperty.hom_ext _ (by
          change (ρ_ U.obj).inv ≫ uncurry (curry ((ρ_ U.obj).hom ≫ f.hom)) = f.hom
          rw [uncurry_curry, Iso.inv_hom_id_assoc])
        right_inv := fun s ↦ by
          change curry ((ρ_ U.obj).hom ≫ (ρ_ U.obj).inv ≫ uncurry s) = s
          rw [Iso.hom_inv_id_assoc, curry_uncurry] }
    have hfn : (homCompletionEquivFormalSection X I U E) ∘
        (completionFunctorFiniteLocallyFree X I).map =
        globalSectionsToFormal X I ((ihom U.obj).obj E.obj) ∘ eqHom :=
      funext fun f ↦ homCompletionEquivFormalSection_map X I f
    have hinj : Function.Injective
        ((homCompletionEquivFormalSection X I U E) ∘
          (completionFunctorFiniteLocallyFree X I).map (X := U) (Y := E)) :=
      (homCompletionEquivFormalSection X I U E).injective.comp
        fun _ _ h ↦ hF.map_injective h
    rw [hfn] at hinj
    exact (Function.Injective.of_comp_iff' _ eqHom.bijective).mp hinj
  · intro h
    refine ⟨fun {G F} f₁ f₂ hf ↦ ?_⟩
    let H : FiniteLocallyFreeSheaf X :=
      ⟨(ihom G.obj).obj F.obj,
        (Modules.isMonoidalClosed_isFiniteLocallyFree X).prop_ihom
          G.obj F.obj G.property F.property⟩
    have hf' := congrArg (homCompletionEquivFormalSection X I G F) hf
    rw [homCompletionEquivFormalSection_map, homCompletionEquivFormalSection_map] at hf'
    have hc := h H hf'
    have hu := congrArg uncurry hc
    rw [uncurry_curry, uncurry_curry] at hu
    exact ObjectProperty.hom_ext _ ((cancel_epi (ρ_ G.obj).hom).mp hu)

/-- Explicit `Functor.FullyFaithful` witness for formal completion on finite locally free sheaves
when `globalSectionsToFormal` is bijective for every finite locally free sheaf. -/
@[stacks 0EKP "(3) ⇒ (4)"]
def fullyFaithfulCompletionFunctorFiniteLocallyFreeOfBijective
    (h : ∀ E : FiniteLocallyFreeSheaf X, Function.Bijective (globalSectionsToFormal X I E.obj)) :
    (completionFunctorFiniteLocallyFree X I).FullyFaithful where
  preimage {G F} φ :=
    let H : FiniteLocallyFreeSheaf X :=
      ⟨(ihom G.obj).obj F.obj,
        (Modules.isMonoidalClosed_isFiniteLocallyFree X).prop_ihom
          G.obj F.obj G.property F.property⟩
    let s := (Equiv.ofBijective _ (h H)).symm (homCompletionEquivFormalSection X I G F φ)
    ObjectProperty.homMk ((ρ_ G.obj).inv ≫ uncurry s)
  map_preimage {G F} φ := by
    let H : FiniteLocallyFreeSheaf X :=
      ⟨(ihom G.obj).obj F.obj,
        (Modules.isMonoidalClosed_isFiniteLocallyFree X).prop_ihom
          G.obj F.obj G.property F.property⟩
    apply (homCompletionEquivFormalSection X I G F).injective
    rw [homCompletionEquivFormalSection_map]
    change globalSectionsToFormal X I H.obj
      (curry ((ρ_ G.obj).hom ≫ (ρ_ G.obj).inv ≫
        uncurry ((Equiv.ofBijective _ (h H)).symm
          (homCompletionEquivFormalSection X I G F φ)))) = _
    rw [Iso.hom_inv_id_assoc, curry_uncurry]
    exact (Equiv.ofBijective _ (h H)).apply_symm_apply _
  preimage_map {G F} f := by
    let H : FiniteLocallyFreeSheaf X :=
      ⟨(ihom G.obj).obj F.obj,
        (Modules.isMonoidalClosed_isFiniteLocallyFree X).prop_ihom
          G.obj F.obj G.property F.property⟩
    refine ObjectProperty.hom_ext _ ?_
    change (ρ_ G.obj).inv ≫ uncurry ((Equiv.ofBijective _ (h H)).symm
      (homCompletionEquivFormalSection X I G F
        ((completionFunctorFiniteLocallyFree X I).map f))) = f.hom
    rw [homCompletionEquivFormalSection_map]
    have hsymm : (Equiv.ofBijective _ (h H)).symm
        (globalSectionsToFormal X I H.obj (curry ((ρ_ G.obj).hom ≫ f.hom))) =
        curry ((ρ_ G.obj).hom ≫ f.hom) :=
      (Equiv.ofBijective _ (h H)).symm_apply_apply _
    rw [hsymm, uncurry_curry, Iso.inv_hom_id_assoc]

/-- Formal completion on finite locally free sheaves is fully faithful if and only if
`globalSectionsToFormal` is bijective on every finite locally free sheaf. -/
@[stacks 0EKP "(3) ⇔ (4)"]
theorem fullyFaithful_completionFunctorFiniteLocallyFree_iff :
    Nonempty (completionFunctorFiniteLocallyFree X I).FullyFaithful ↔
      ∀ E : FiniteLocallyFreeSheaf X, Function.Bijective (globalSectionsToFormal X I E.obj) := by
  constructor
  · rintro ⟨hFF⟩ E
    let U : FiniteLocallyFreeSheaf X := ⟨𝟙_ X.Modules, (Modules.isFiniteLocallyFree X).prop_unit⟩
    rw [← bijective_globalSectionsToFormal_iff_of_iso X I (ihomUnitIso X E.obj)]
    let eqHom : (U ⟶ E) ≃ (𝟙_ X.Modules ⟶ (ihom U.obj).obj E.obj) :=
      { toFun := fun f ↦ curry ((ρ_ U.obj).hom ≫ f.hom)
        invFun := fun s ↦ ObjectProperty.homMk ((ρ_ U.obj).inv ≫ uncurry s)
        left_inv := fun f ↦ ObjectProperty.hom_ext _ (by
          change (ρ_ U.obj).inv ≫ uncurry (curry ((ρ_ U.obj).hom ≫ f.hom)) = f.hom
          rw [uncurry_curry, Iso.inv_hom_id_assoc])
        right_inv := fun s ↦ by
          change curry ((ρ_ U.obj).hom ≫ (ρ_ U.obj).inv ≫ uncurry s) = s
          rw [Iso.hom_inv_id_assoc, curry_uncurry] }
    have hfn : (homCompletionEquivFormalSection X I U E) ∘
        (completionFunctorFiniteLocallyFree X I).map =
        globalSectionsToFormal X I ((ihom U.obj).obj E.obj) ∘ eqHom :=
      funext fun f ↦ homCompletionEquivFormalSection_map X I f
    have hbij : Function.Bijective
        ((homCompletionEquivFormalSection X I U E) ∘
          (completionFunctorFiniteLocallyFree X I).map (X := U) (Y := E)) :=
      (homCompletionEquivFormalSection X I U E).bijective.comp hFF.homEquiv.bijective
    rw [hfn] at hbij
    exact (Function.Bijective.of_comp_iff (globalSectionsToFormal X I ((ihom U.obj).obj E.obj))
      eqHom.bijective).mp hbij
  · exact fun h ↦ ⟨fullyFaithfulCompletionFunctorFiniteLocallyFreeOfBijective X I h⟩

end CompletionFunctor

/-! ### Ample line bundle criterion (`(2) ⇒ (3) ⇒ (4)`) -/

section Ample

variable (X : Scheme.{u}) (I : X.IdealSheafData) [QuasiSeparatedSpace X]

omit [QuasiSeparatedSpace X] in
private lemma biproduct_total_hom {ι : Type} [Fintype ι] (A : ι → FiniteLocallyFreeSheaf X) :
    ∑ i : ι, (biproduct.π A i).hom ≫ (biproduct.ι A i).hom = 𝟙 (⨁ A).obj := by
  have htot := congrArg (Modules.isFiniteLocallyFree X).ι.map (biproduct.total (f := A))
  rw [Functor.map_sum, CategoryTheory.Functor.map_id] at htot
  exact htot

/-- If `L` is an ample line bundle on a quasi-separated scheme `X` and `globalSectionsToFormal` is
injective on `L^{⊗ n}` for all sufficiently large `n`, then it is injective on every finite locally
free sheaf on `X`. -/
theorem injective_globalSectionsToFormal_of_isAmple
    {L : InvertibleSheaf X} (hL : (LineBundleClass.mk L).IsAmple)
    (h : ∃ N : ℕ, ∀ n ≥ N, Function.Injective (globalSectionsToFormal X I (L.tensorPow n).obj))
    (E : FiniteLocallyFreeSheaf X) :
    Function.Injective (globalSectionsToFormal X I E.obj) := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨p, _, hNp, _, r, _, α, β, hαβ, hlim⟩ :=
    FiniteLocallyFreeSheaf.exists_universallyExact_ample_resolution hL E N
  let A : Fin r → FiniteLocallyFreeSheaf X :=
    fun _ ↦ (InvertibleSheaf.toFiniteLocallyFree X).obj (L.tensorPow p)
  have hP : Function.Injective (globalSectionsToFormal X I (⨁ A).obj) :=
    injective_globalSectionsToFormal_of_bicone X I (fun i ↦ (A i).obj) (⨁ A).obj
      (fun i ↦ (biproduct.ι A i).hom) (fun i ↦ (biproduct.π A i).hom)
      (biproduct_total_hom X A) (fun _ ↦ hN p hNp)
  exact injective_globalSectionsToFormal_of_universallyExact X I α.hom β.hom
    (congrArg (·.hom) hαβ) hlim hP

/-- If `L` is an ample line bundle on a quasi-separated scheme `X` and `globalSectionsToFormal` is
bijective on `L^{⊗ n}` for all sufficiently large `n`, then it is bijective on every finite locally
free sheaf on `X`. -/
@[stacks 0EKP "(2) ⇒ (3)"]
theorem bijective_globalSectionsToFormal_of_isAmple
    {L : InvertibleSheaf X} (hL : (LineBundleClass.mk L).IsAmple)
    (h : ∃ N : ℕ, ∀ n ≥ N, Function.Bijective (globalSectionsToFormal X I (L.tensorPow n).obj))
    (E : FiniteLocallyFreeSheaf X) :
    Function.Bijective (globalSectionsToFormal X I E.obj) := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨p, q, hNp, hNq, r, s, α, β, hαβ, hlim⟩ :=
    FiniteLocallyFreeSheaf.exists_universallyExact_ample_resolution hL E N
  let A : Fin r → FiniteLocallyFreeSheaf X :=
    fun _ ↦ (InvertibleSheaf.toFiniteLocallyFree X).obj (L.tensorPow p)
  let B : Fin s → FiniteLocallyFreeSheaf X :=
    fun _ ↦ (InvertibleSheaf.toFiniteLocallyFree X).obj (L.tensorPow q)
  have hP : Function.Bijective (globalSectionsToFormal X I (⨁ A).obj) :=
    bijective_globalSectionsToFormal_of_bicone X I (fun i ↦ (A i).obj) (⨁ A).obj
      (fun i ↦ (biproduct.ι A i).hom) (fun i ↦ (biproduct.π A i).hom)
      (biproduct_total_hom X A) (fun _ ↦ hN p hNp)
  have hQ : Function.Injective (globalSectionsToFormal X I (⨁ B).obj) :=
    injective_globalSectionsToFormal_of_bicone X I (fun j ↦ (B j).obj) (⨁ B).obj
      (fun j ↦ (biproduct.ι B j).hom) (fun j ↦ (biproduct.π B j).hom)
      (biproduct_total_hom X B) (fun _ ↦ (hN q hNq).1)
  exact bijective_globalSectionsToFormal_of_universallyExact X I α.hom β.hom
    (congrArg (·.hom) hαβ) hlim hP hQ

/-- If `L` is an ample line bundle on a quasi-separated scheme `X` and `globalSectionsToFormal` is
injective on `L^{⊗ n}` for all sufficiently large `n`, then formal completion on finite locally
free sheaves is faithful. -/
theorem faithful_completionFunctorFiniteLocallyFree_of_isAmple
    {L : InvertibleSheaf X} (hL : (LineBundleClass.mk L).IsAmple)
    (h : ∃ N : ℕ, ∀ n ≥ N, Function.Injective (globalSectionsToFormal X I (L.tensorPow n).obj)) :
    (completionFunctorFiniteLocallyFree X I).Faithful :=
  (faithful_completionFunctorFiniteLocallyFree_iff X I).mpr
    (injective_globalSectionsToFormal_of_isAmple X I hL h)

/-- If `L` is an ample line bundle on a quasi-separated scheme `X` and `globalSectionsToFormal` is
bijective on `L^{⊗ n}` for all sufficiently large `n`, then formal completion on finite locally
free sheaves is fully faithful. -/
@[stacks 0EKP "(2) ⇒ (4)"]
def fullyFaithfulCompletionFunctorFiniteLocallyFreeOfIsAmple
    {L : InvertibleSheaf X} (hL : (LineBundleClass.mk L).IsAmple)
    (h : ∃ N : ℕ, ∀ n ≥ N, Function.Bijective (globalSectionsToFormal X I (L.tensorPow n).obj)) :
    (completionFunctorFiniteLocallyFree X I).FullyFaithful :=
  fullyFaithfulCompletionFunctorFiniteLocallyFreeOfBijective X I
    (bijective_globalSectionsToFormal_of_isAmple X I hL h)

end Ample

/-! ### Quasi-affine criterion (`(1) ⇒ (2) ⇒ (3) ⇒ (4)`) -/

section QuasiAffine

variable (X : Scheme.{u}) (I : X.IdealSheafData) [X.IsQuasiAffine]

omit [X.IsQuasiAffine] in
private lemma nonempty_trivial_tensorPow_iso_unit (n : ℕ) :
    Nonempty (((InvertibleSheaf.trivial X).tensorPow n).obj ≅ 𝟙_ X.Modules) := by
  have h : LineBundleClass.mk ((InvertibleSheaf.trivial X).tensorPow n) = 1 := by
    simp
  exact LineBundleClass.mk_eq_one_iff.mp h

/-- On a quasi-affine scheme `X`, injectivity of `Γ(X, 𝒪_X) → limₙ Γ(V(I^{n+1}), 𝒪_{V(I^{n+1})})`
implies injectivity of `globalSectionsToFormal` for every finite locally free sheaf on `X`. -/
theorem injective_globalSectionsToFormal_of_isQuasiAffine
    (h : Function.Injective (structureSectionsToFormal X I))
    (E : FiniteLocallyFreeSheaf X) :
    Function.Injective (globalSectionsToFormal X I E.obj) := by
  have : QuasiSeparatedSpace X :=
    (AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace X.toSpecΓ).mp inferInstance
  have hunit : Function.Injective (globalSectionsToFormal X I (𝟙_ X.Modules)) :=
    (injective_globalSectionsToFormal_unit_iff X I).mpr h
  have hL : (LineBundleClass.mk (InvertibleSheaf.trivial X)).IsAmple := by
    rw [LineBundleClass.mk_trivial]
    exact LineBundleClass.isAmple_one
  refine injective_globalSectionsToFormal_of_isAmple X I hL ⟨0, fun n _ ↦ ?_⟩ E
  obtain ⟨e⟩ := nonempty_trivial_tensorPow_iso_unit X n
  exact (injective_globalSectionsToFormal_iff_of_iso X I e).mpr hunit

/-- On a quasi-affine scheme `X`, bijectivity of `Γ(X, 𝒪_X) → limₙ Γ(V(I^{n+1}), 𝒪_{V(I^{n+1})})`
implies bijectivity of `globalSectionsToFormal` for every finite locally free sheaf on `X`. -/
@[stacks 0EKP "(1) ⇒ (3)"]
theorem bijective_globalSectionsToFormal_of_isQuasiAffine
    (h : Function.Bijective (structureSectionsToFormal X I))
    (E : FiniteLocallyFreeSheaf X) :
    Function.Bijective (globalSectionsToFormal X I E.obj) := by
  have : QuasiSeparatedSpace X :=
    (AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace X.toSpecΓ).mp inferInstance
  have hunit : Function.Bijective (globalSectionsToFormal X I (𝟙_ X.Modules)) :=
    (bijective_globalSectionsToFormal_unit_iff X I).mpr h
  have hL : (LineBundleClass.mk (InvertibleSheaf.trivial X)).IsAmple := by
    rw [LineBundleClass.mk_trivial]
    exact LineBundleClass.isAmple_one
  refine bijective_globalSectionsToFormal_of_isAmple X I hL ⟨0, fun n _ ↦ ?_⟩ E
  obtain ⟨e⟩ := nonempty_trivial_tensorPow_iso_unit X n
  exact (bijective_globalSectionsToFormal_iff_of_iso X I e).mpr hunit

/-- On a quasi-affine scheme `X`, injectivity of `Γ(X, 𝒪_X) → limₙ Γ(V(I^{n+1}), 𝒪_{V(I^{n+1})})`
implies faithfulness of formal completion on finite locally free sheaves. -/
theorem faithful_completionFunctorFiniteLocallyFree_of_isQuasiAffine
    (h : Function.Injective (structureSectionsToFormal X I)) :
    (completionFunctorFiniteLocallyFree X I).Faithful :=
  (faithful_completionFunctorFiniteLocallyFree_iff X I).mpr
    (injective_globalSectionsToFormal_of_isQuasiAffine X I h)

/-- On a quasi-affine scheme `X`, bijectivity of `Γ(X, 𝒪_X) → limₙ Γ(V(I^{n+1}), 𝒪_{V(I^{n+1})})`
implies full faithfulness of formal completion on finite locally free sheaves. -/
@[stacks 0EKP "(1) ⇒ (4)"]
def fullyFaithfulCompletionFunctorFiniteLocallyFreeOfIsQuasiAffine
    (h : Function.Bijective (structureSectionsToFormal X I)) :
    (completionFunctorFiniteLocallyFree X I).FullyFaithful :=
  fullyFaithfulCompletionFunctorFiniteLocallyFreeOfBijective X I
    (bijective_globalSectionsToFormal_of_isQuasiAffine X I h)

end QuasiAffine

end

end AlgebraicGeometry.Scheme.formalCompletion
