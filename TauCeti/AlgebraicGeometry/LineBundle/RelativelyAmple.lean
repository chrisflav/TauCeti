/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Sections
import TauCeti.AlgebraicGeometry.Modules.Localization
import TauCeti.AlgebraicGeometry.Modules.Sections
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Relatively ample line bundles

Let `f : X ⟶ S` be a morphism of schemes. A line-bundle class `a` on `X` is *relatively ample*
over `S` (`LineBundleClass.IsRelativelyAmple f a`) if for every affine open `U` of `S` the
restriction of `a` to `f⁻¹(U)` is ample.

Along an affine morphism `g : Y ⟶ X`, pulling back a section `s` of an invertible sheaf `M`
gives a section whose nonvanishing locus is `g⁻¹(X_s)` (`nonvanishingLocus_pullbackSections`).
Since inverse images of affine opens under an affine morphism are affine, pulling back an ample
line-bundle class along an affine morphism produces an ample class
(`IsAmple.pullback_of_isAffineHom`); in particular, ampleness is preserved under scheme
isomorphisms and under restriction to basic opens of global functions.

Conversely, on a quasi-compact quasi-separated scheme `X`, if basic opens `X_{rᵢ}` cover `X` and
`a|_{X_{rᵢ}}` is ample for every `i`, then `a` is ample (`IsAmple.of_iSup_basicOpen_eq_top`):
sections of positive powers over `X_{rᵢ}` extend to global sections after multiplication by a
power of `rᵢ`, by the qcqs localization lemma for quasi-coherent modules. From these two
ingredients follow the standard locality and base-change properties of relative ampleness for a
quasi-compact quasi-separated morphism `f : X ⟶ S`:

* over an affine base `S`, relative ampleness is equivalent to absolute ampleness
  (`isRelativelyAmple_iff_isAmple`);
* relative ampleness is Zariski-local on the base (`IsRelativelyAmple.of_forall_exists_isAffineOpen`
  and `IsRelativelyAmple.of_forall_exists_opens`);
* relative ampleness is preserved under arbitrary base change
  (`IsRelativelyAmple.pullback_of_isPullback`).

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple f a`: `a` is ample on `f⁻¹(U)` for
  every affine open `U` of `S`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection`: for `n > 0`, the
  nonvanishing locus of `s^⊗n` equals that of `s`.
* `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_pullbackSections`: pulling back a section of
  an invertible sheaf along `g : Y ⟶ X` pulls back its nonvanishing locus.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isAmple_pow_iff` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_pow_iff`: a class is (relatively)
  ample iff a positive power of it is.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.pullback_of_isAffineHom`: pullback along an
  affine morphism preserves ampleness.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.of_iSup_basicOpen_eq_top`: on a qcqs scheme,
  ampleness can be checked on a cover by basic opens of global functions.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_iff_isAmple`: over an affine base,
  relative ampleness of a qcqs morphism agrees with ampleness.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.of_forall_exists_isAffineOpen` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.of_forall_exists_opens`: relative
  ampleness of a qcqs morphism is Zariski-local on the base.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.pullback_of_isPullback`: relative
  ampleness of a qcqs morphism commutes with arbitrary base change.

## References

* [The Stacks Project, Tag 01VG](https://stacks.math.columbia.edu/tag/01VG) (relatively ample
  invertible sheaves), [Tag 01VK](https://stacks.math.columbia.edu/tag/01VK) (locality on the
  base), and [Tag 0892](https://stacks.math.columbia.edu/tag/0892) (pullback along affine
  morphisms).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §4.6 and
  Proposition 5.1.12.
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 7.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite

universe u

namespace TauCeti.AlgebraicGeometry.SheafOfModules

variable {X Y : Scheme.{u}}

/-- The restriction of an invertible sheaf along an open immersion is invertible. -/
instance isInvertible_restrict (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    [isInvertible Y M] : isInvertible X (M.restrict f) :=
  (isInvertible X).prop_of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
    inferInstance

/-- The monoidal tensor product of two invertible sheaves is invertible. -/
instance isInvertible_tensor (M N : X.Modules) [hM : isInvertible X M] [hN : isInvertible X N] :
    isInvertible X (M ⊗ N) :=
  (isInvertible X).prop_of_iso
    (InvertibleSheaf.tensorProductObjIso ⟨M, hM⟩ ⟨N, hN⟩)
    (InvertibleSheaf.tensorProduct ⟨M, hM⟩ ⟨N, hN⟩).property

/-- Every monoidal tensor power `TauCeti.tensorPow M n` of an invertible sheaf is invertible. -/
instance isInvertible_tensorPow (M : X.Modules) [isInvertible X M] :
    ∀ n : ℕ, isInvertible X (TauCeti.tensorPow M n)
  | 0 => inferInstanceAs (isInvertible X (𝟙_ X.Modules))
  | n + 1 => @isInvertible_tensor X M (TauCeti.tensorPow M n) ‹_› (isInvertible_tensorPow M n)

end TauCeti.AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- For a positive exponent `n`, the nonvanishing locus of the tensor power section `s^⊗n`
equals the nonvanishing locus of `s`. -/
@[simp]
theorem nonvanishingLocus_tensorPowSection {M : X.Modules} [SheafOfModules.isInvertible X M]
    {U : X.Opens} (s : Γ(M, U)) {n : ℕ} (hn : 0 < n) :
    (TauCeti.tensorPow M n).nonvanishingLocus (tensorPowSection s n) = M.nonvanishingLocus s := by
  have hle {W : X.Opens} (t : Γ(M, W)) (k : ℕ) :
      M.nonvanishingLocus t ≤
        (TauCeti.tensorPow M k).nonvanishingLocus (tensorPowSection t k) := by
    let j : M.nonvanishingLocus t ⟶ W := homOfLE (nonvanishingLocus_le t)
    have ht := (le_nonvanishingLocus_iff t j).mp le_rfl
    have htk := bijective_smul_tensorPowSection (M.presheaf.map j.op t)
      (fun W' i ↦ by simpa only [← Functor.map_comp_apply, ← op_comp] using ht W' i) k
    refine (le_nonvanishingLocus_iff (tensorPowSection t k) j).mpr fun W' i ↦ ?_
    simpa only [← map_tensorPowSection, ← Functor.map_comp_apply, ← op_comp] using htk W' i
  refine le_antisymm (fun x hx ↦ ?_) (hle s n)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hxU : x ∈ U := nonvanishingLocus_le _ hx
  obtain ⟨V, t, hxV⟩ := exists_mem_trivialization M x
  let jU : U ⊓ V ⟶ U := homOfLE inf_le_left
  let jV : U ⊓ V ⟶ V := homOfLE inf_le_right
  let e : Γ(M, U ⊓ V) := M.presheaf.map jV.op (trivializationGenerator M t)
  have he : U ⊓ V ≤ M.nonvanishingLocus e := by
    rw [nonvanishingLocus_map, nonvanishingLocus_trivializationGenerator]
    exact le_inf le_rfl inf_le_right
  -- On `U ⊓ V`, write `s = r • e`; then `s^(k+1) = r^(k+1) • e^(k+1)`.
  have hcoord := eq_trivializationCoordinate_smul_map_trivializationGenerator M t jV
    (M.presheaf.map jU.op s)
  set r := trivializationCoordinate M t jV (M.presheaf.map jU.op s)
  have hx' : x ∈ (U ⊓ V) ⊓
      (TauCeti.tensorPow M (k + 1)).nonvanishingLocus (tensorPowSection s (k + 1)) :=
    ⟨⟨hxU, hxV⟩, hx⟩
  rw [← nonvanishingLocus_map jU, map_tensorPowSection, hcoord, tensorPowSection_smul,
    nonvanishingLocus_smul, inf_eq_left.mpr ((X.basicOpen_le _).trans (he.trans (hle e (k + 1)))),
    X.basicOpen_pow r (Nat.succ_pos k)] at hx'
  have hxs : x ∈ M.nonvanishingLocus (M.presheaf.map jU.op s) := by
    rw [hcoord, nonvanishingLocus_smul, inf_eq_left.mpr ((X.basicOpen_le r).trans he)]
    exact hx'
  rw [nonvanishingLocus_map] at hxs
  exact hxs.2

/-- Along an open immersion `f : X ⟶ Y`, the image of the nonvanishing locus of a section of
`M.restrict f` is the nonvanishing locus of the corresponding section of `M`. -/
theorem image_nonvanishingLocus_restrict (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    [SheafOfModules.isInvertible Y M] {U : X.Opens} (s : Γ(M.restrict f, U)) :
    f ''ᵁ (M.restrict f).nonvanishingLocus s =
      M.nonvanishingLocus ((M.restrictAppIso f U).hom s) := by
  have hbij {W : X.Opens} (i : W ⟶ U) :
      (Function.Bijective fun r : Γ(X, W) ↦ r • (M.restrict f).presheaf.map i.op s) ↔
        Function.Bijective fun r : Γ(Y, f ''ᵁ W) ↦
          r • M.presheaf.map (homOfLE (f.image_mono i.le)).op ((M.restrictAppIso f U).hom s) := by
    have hfun : (M.restrictAppIso f W).hom ∘
        (fun r : Γ(X, W) ↦ r • (M.restrict f).presheaf.map i.op s) =
          (fun r : Γ(Y, f ''ᵁ W) ↦
            r • M.presheaf.map (homOfLE (f.image_mono i.le)).op ((M.restrictAppIso f U).hom s)) ∘
              (f.appIso W).inv := by
      ext r
      simp only [Function.comp_apply, smul_restrictAppIso_hom_apply, map_restrictAppIso_hom_apply]
    rw [← Function.Bijective.of_comp_iff'
      (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f W).hom), hfun,
      Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso (f.appIso W).inv)]
  refine le_antisymm ?_ ?_
  · refine (le_nonvanishingLocus_iff ((M.restrictAppIso f U).hom s)
      (homOfLE (f.image_mono (nonvanishingLocus_le s)))).mpr fun V' j ↦ ?_
    have hj := j.le
    rw [Subsingleton.elim j (homOfLE hj)]
    clear j
    obtain ⟨W', rfl⟩ : ∃ W' : X.Opens, f ''ᵁ W' = V' := ⟨f ⁻¹ᵁ V', by
      rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr
        (hj.trans ((f.image_mono (nonvanishingLocus_le s)).trans (f.image_le_opensRange U)))]⟩
    have hW' : W' ≤ (M.restrict f).nonvanishingLocus s := by
      rw [← f.preimage_image_eq ((M.restrict f).nonvanishingLocus s), ← f.preimage_image_eq W']
      exact f.preimage_mono hj
    exact (hbij (homOfLE (hW'.trans (nonvanishingLocus_le s)))).mp
      ((le_nonvanishingLocus_iff s (homOfLE (nonvanishingLocus_le s))).mp le_rfl W' (homOfLE hW'))
  · set N := M.nonvanishingLocus ((M.restrictAppIso f U).hom s)
    have hNU : N ≤ f ''ᵁ U := nonvanishingLocus_le _
    have hpre : f ⁻¹ᵁ N ≤ U := by
      rw [← f.preimage_image_eq U]
      exact f.preimage_mono hNU
    have himg : f ''ᵁ (f ⁻¹ᵁ N) = N := by
      rw [f.image_preimage_eq_opensRange_inf,
        inf_eq_right.mpr (hNU.trans (f.image_le_opensRange U))]
    suffices hN : f ⁻¹ᵁ N ≤ (M.restrict f).nonvanishingLocus s by
      rw [← himg]
      exact f.image_mono hN
    refine (le_nonvanishingLocus_iff s (homOfLE hpre)).mpr fun W' j ↦
      (hbij (j ≫ homOfLE hpre)).mpr ?_
    have hj : f ''ᵁ W' ≤ N := himg ▸ f.image_mono j.le
    exact (le_nonvanishingLocus_iff _ (homOfLE hNU)).mp le_rfl (f ''ᵁ W') (homOfLE hj)

/-- Along an open immersion `f : X ⟶ Y`, the nonvanishing locus of a section of `M.restrict f`
is the preimage of the nonvanishing locus of the corresponding section of `M`. -/
theorem nonvanishingLocus_restrict (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    [SheafOfModules.isInvertible Y M] {U : X.Opens} (s : Γ(M.restrict f, U)) :
    (M.restrict f).nonvanishingLocus s =
      f ⁻¹ᵁ M.nonvanishingLocus ((M.restrictAppIso f U).hom s) := by
  rw [← image_nonvanishingLocus_restrict, f.preimage_image_eq]

/-- Along an open immersion `f : Y ⟶ X`, pulling back a section of an invertible sheaf pulls back
its nonvanishing locus. -/
private theorem nonvanishingLocus_pullbackSections_of_isOpenImmersion (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules) [SheafOfModules.isInvertible X M] {U : X.Opens}
    (s : Γ(M, U)) :
    ((pullback f).obj M).nonvanishingLocus (f.pullbackSections M U s) =
      f ⁻¹ᵁ M.nonvanishingLocus s := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f)
    (pullbackPushforwardAdjunction f) M
  have he := congrArg (fun a ↦ a.app U s) hu
  simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app] at he
  let t : Γ(M.restrict f, f ⁻¹ᵁ U) :=
    (M.restrictAppIso f (f ⁻¹ᵁ U)).inv (M.presheaf.map (homOfLE (f.image_preimage_le U)).op s)
  -- `restrictAppIso` is the identity on underlying section types (`restrict_obj`).
  have ht : (((restrictFunctorIsoPullback f).app M).hom).app (f ⁻¹ᵁ U) t =
      f.pullbackSections M U s := by
    rw [Iso.app_hom, Hom.pullbackSections_apply, ← he]
    rfl
  rw [← ht, nonvanishingLocus_hom_app ((restrictFunctorIsoPullback f).app M),
    nonvanishingLocus_restrict, Iso.inv_hom_id_apply, nonvanishingLocus_map,
    f.preimage_inf, f.preimage_image_eq,
    inf_eq_right.mpr (f.preimage_mono (nonvanishingLocus_le s))]

/-- On the structure sheaf `𝟙_ X.Modules`, pulling back a section along `g : Y ⟶ X` pulls back
its nonvanishing locus. -/
private theorem nonvanishingLocus_pullbackSections_unit (g : Y ⟶ X) {U : X.Opens}
    (s : Γ(𝟙_ X.Modules, U)) :
    ((pullback g).obj (𝟙_ X.Modules)).nonvanishingLocus (g.pullbackSections (𝟙_ X.Modules) U s) =
      g ⁻¹ᵁ (𝟙_ X.Modules).nonvanishingLocus s := by
  let r : Γ(X, U) := s
  -- Sections of `𝟙_ _.Modules` are definitionally regular functions, and `ε` is the identity.
  have hp : (pullbackObjUnitIso g).hom.app (g ⁻¹ᵁ U) (g.pullbackSections (𝟙_ X.Modules) U s) =
      (show Γ(𝟙_ Y.Modules, g ⁻¹ᵁ U) from g.app U r) := by
    have hp₀ := g.pullbackObjUnitIso_hom_app_pullbackSections_ε U r
    rw [sectionsFunctor_ε, sectionsFunctor_ε] at hp₀
    exact hp₀
  rw [← nonvanishingLocus_hom_app (pullbackObjUnitIso g), hp]
  exact (nonvanishingLocus_unit (g.app U r)).trans
    ((Scheme.preimage_basicOpen g r).symm.trans
      (congrArg (g ⁻¹ᵁ ·) (nonvanishingLocus_unit r).symm))

/-- Pulling back a section of an invertible sheaf along a morphism of schemes `g : Y ⟶ X`
pulls back its nonvanishing locus: `Y_{g^* s} = g⁻¹(X_s)`. -/
@[simp]
theorem nonvanishingLocus_pullbackSections (g : Y ⟶ X) (M : X.Modules)
    [hM : SheafOfModules.isInvertible X M] {U : X.Opens} (s : Γ(M, U)) :
    ((pullback g).obj M).nonvanishingLocus (g.pullbackSections M U s) =
      g ⁻¹ᵁ M.nonvanishingLocus s := by
  have hcongr {Z : Scheme.{u}} {g₁ g₂ : Z ⟶ X} (h : g₁ = g₂) :
      ((pullback g₁).obj M).nonvanishingLocus (g₁.pullbackSections M U s) =
        ((pullback g₂).obj M).nonvanishingLocus (g₂.pullbackSections M U s) := by
    subst h
    rfl
  have hcomp {Z W : Scheme.{u}} (f₁ : Z ⟶ W) (f₂ : W ⟶ X) :
      ((pullback f₁).obj ((pullback f₂).obj M)).nonvanishingLocus
        (f₁.pullbackSections _ _ (f₂.pullbackSections M U s)) =
        ((pullback (f₁ ≫ f₂)).obj M).nonvanishingLocus ((f₁ ≫ f₂).pullbackSections M U s) := by
    let c : (pullback (f₁ ≫ f₂)).obj M ≅ (pullback f₁).obj ((pullback f₂).obj M) :=
      ((pullbackComp f₁ f₂).app M).symm
    exact (congrArg
      (((pullback f₁).obj ((pullback f₂).obj M)).nonvanishingLocus (U := (f₁ ≫ f₂) ⁻¹ᵁ U))
      (Hom.pullbackSections_comp f₂ M U f₁ s).symm).trans
        (nonvanishingLocus_hom_app c ((f₁ ≫ f₂).pullbackSections M U s))
  obtain ⟨ι, V, hV, eV⟩ := SheafOfModules.isInvertible_iff_exists_isOpenCover.mp hM
  ext y
  obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hV.iSup_eq_top.symm ▸ TopologicalSpace.Opens.mem_top (g y))
  let φ : (pullback (V i).ι).obj M ≅ 𝟙_ (V i).toScheme.Modules :=
    ((restrictFunctorIsoPullback (V i).ι).app M).symm ≪≫ (eV i).some.symm
  -- Restrict both sides to `g⁻¹(V i)`, where `M` pulls back to the structure sheaf of `V i`.
  suffices hloc : (g ⁻¹ᵁ V i).ι ⁻¹ᵁ
      ((pullback g).obj M).nonvanishingLocus (g.pullbackSections M U s) =
        (g ⁻¹ᵁ V i).ι ⁻¹ᵁ (g ⁻¹ᵁ M.nonvanishingLocus s) from
    congr(⟨y, hyi⟩ ∈ $hloc).to_iff
  rw [← nonvanishingLocus_pullbackSections_of_isOpenImmersion (g ⁻¹ᵁ V i).ι, hcomp,
    hcongr (morphismRestrict_ι g (V i)).symm, ← hcomp,
    ← nonvanishingLocus_hom_app ((pullback (g ∣_ V i)).mapIso φ),
    Functor.mapIso_hom, Hom.pullbackSections_naturality (g ∣_ V i) _ _ φ.hom,
    nonvanishingLocus_pullbackSections_unit (g ∣_ V i),
    nonvanishingLocus_hom_app φ, nonvanishingLocus_pullbackSections_of_isOpenImmersion (V i).ι,
    ← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage]

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {X Y S S' : Scheme.{u}}

/-- The class of the monoidal tensor power `TauCeti.tensorPow L.obj n` is `(mk L) ^ n`. -/
@[simp]
theorem mk_tensorPowObj (L : InvertibleSheaf X) (n : ℕ) :
    mk ⟨TauCeti.tensorPow L.obj n, inferInstance⟩ = mk L ^ n := by
  induction n with
  | zero => exact mk_eq_one_iff.mpr ⟨Iso.refl _⟩
  | succ n ih =>
    rw [pow_succ', ← ih, ← mk_tensorProduct, mk_eq_mk_iff]
    exact ⟨(InvertibleSheaf.tensorProductObjIso L ⟨TauCeti.tensorPow L.obj n, inferInstance⟩).symm⟩

/-- Every positive power `aⁿ` of an ample line-bundle class `a` is ample. -/
theorem IsAmple.pow {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) (h : a.IsAmple) :
    (a ^ n).IsAmple where
  compactSpace := h.compactSpace
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨m, hm, L, hL, s, hx, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus x
    refine ⟨m, hm, ⟨TauCeti.tensorPow L.obj n, inferInstance⟩, ?_,
      Scheme.Modules.tensorPowSection s n, ?_, ?_⟩
    · rw [mk_tensorPowObj, hL, ← pow_mul, mul_comm, pow_mul]
    · rwa [Scheme.Modules.nonvanishingLocus_tensorPowSection s hn]
    · rwa [Scheme.Modules.nonvanishingLocus_tensorPowSection s hn]

/-- For `n > 0`, a power `aⁿ` is ample if and only if `a` is ample. -/
theorem isAmple_pow_iff {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) :
    (a ^ n).IsAmple ↔ a.IsAmple :=
  ⟨IsAmple.of_pow hn, IsAmple.pow hn⟩

/-- **Pullback along an affine morphism preserves ampleness** (Stacks Tag 0892; EGA II,
Proposition 5.1.12). -/
theorem IsAmple.pullback_of_isAffineHom (g : Y ⟶ X) [IsAffineHom g] {a : LineBundleClass X}
    (h : a.IsAmple) : (pullback g a).IsAmple where
  compactSpace := by
    have := h.compactSpace
    exact QuasiCompact.compactSpace_of_compactSpace g
  exists_isAffineOpen_nonvanishingLocus y := by
    obtain ⟨n, hn, L, hL, s, hy, hs⟩ := h.exists_isAffineOpen_nonvanishingLocus (g y)
    let L' : InvertibleSheaf Y := ⟨(Scheme.Modules.pullback g).obj L.obj, inferInstance⟩
    refine ⟨n, hn, L', ?_, g.pullbackSectionsLE L.obj ⊤ ⊤ g.preimage_top.ge s, ?_, ?_⟩
    · rw [← pullback_pow, ← hL, pullback_mk]
      rfl
    · rw [Scheme.Hom.pullbackSectionsLE_apply, Scheme.Modules.nonvanishingLocus_map,
        Scheme.Modules.nonvanishingLocus_pullbackSections]
      exact ⟨trivial, hy⟩
    · rw [Scheme.Hom.pullbackSectionsLE_apply, Scheme.Modules.nonvanishingLocus_map,
        Scheme.Modules.nonvanishingLocus_pullbackSections, top_inf_eq]
      exact hs.preimage g

/-- Pullback along an isomorphism of schemes preserves ampleness. -/
theorem IsAmple.pullback_of_isIso (g : Y ⟶ X) [IsIso g] {a : LineBundleClass X}
    (h : a.IsAmple) : (pullback g a).IsAmple :=
  h.pullback_of_isAffineHom g

/-- Along an isomorphism of schemes `g : Y ⟶ X`, `pullback g a` is ample iff `a` is ample. -/
@[simp]
theorem isAmple_pullback_iff_of_isIso (g : Y ⟶ X) [IsIso g] {a : LineBundleClass X} :
    (pullback g a).IsAmple ↔ a.IsAmple :=
  ⟨fun h ↦ by simpa [pullback_comp] using h.pullback_of_isIso (inv g),
    fun h ↦ h.pullback_of_isIso g⟩

/-- Restricting an ample line-bundle class to the basic open `X_r` of a global function `r`
yields an ample line-bundle class. -/
theorem IsAmple.pullback_basicOpen_ι (r : Γ(X, ⊤)) {a : LineBundleClass X} (h : a.IsAmple) :
    (pullback (X.basicOpen r).ι a).IsAmple :=
  h.pullback_of_isAffineHom (X.basicOpen r).ι

/-- **Ampleness on a qcqs scheme is local on basic opens of global functions.** Let `X` be
quasi-compact and quasi-separated, and let `rᵢ ∈ Γ(X, ⊤)` be global functions whose basic opens
cover `X`. If `a|_{X_{rᵢ}}` is ample for every `i`, then `a` is ample. -/
theorem IsAmple.of_iSup_basicOpen_eq_top [CompactSpace X] [QuasiSeparatedSpace X]
    {ι : Type*} (r : ι → Γ(X, ⊤)) (hcov : ⨆ i, X.basicOpen (r i) = ⊤)
    {a : LineBundleClass X} (h : ∀ i, (pullback (X.basicOpen (r i)).ι a).IsAmple) :
    a.IsAmple where
  compactSpace := inferInstance
  exists_isAffineOpen_nonvanishingLocus x := by
    obtain ⟨L₀, rfl⟩ := mk_surjective a
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcov.symm ▸ TopologicalSpace.Opens.mem_top x)
    let U := X.basicOpen (r i)
    obtain ⟨n, hn, Hn⟩ := (h i).exists_pos_forall_mk_eq ⟨x, hxi⟩
    let L : InvertibleSheaf X := L₀.tensorPow n
    let L_U : InvertibleSheaf U.toScheme := ⟨L.obj.restrict U.ι, inferInstance⟩
    have hL_U : LineBundleClass.mk L_U = pullback U.ι (LineBundleClass.mk L₀) ^ n := by
      rw [← pullback_pow, ← mk_tensorPow, pullback_mk, mk_eq_mk_iff]
      exact ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.obj⟩
    obtain ⟨s₀, hxs₀, hs₀_aff⟩ := Hn L_U hL_U
    -- Read `s₀` as a section `t₀` of `L.obj` over `X.basicOpen (r i)`.
    let t₀ : Γ(L.obj, U) :=
      L.obj.presheaf.map (homOfLE U.ι_image_top.ge).op ((L.obj.restrictAppIso U.ι ⊤).hom s₀)
    have ht₀_eq : L.obj.nonvanishingLocus t₀ = U.ι ''ᵁ L_U.obj.nonvanishingLocus s₀ := by
      rw [Scheme.Modules.image_nonvanishingLocus_restrict, Scheme.Modules.nonvanishingLocus_map,
        inf_eq_right.mpr ((Scheme.Modules.nonvanishingLocus_le _).trans U.ι_image_top.le)]
    have hxt₀ : x ∈ L.obj.nonvanishingLocus t₀ := ht₀_eq ▸ ⟨⟨x, hxi⟩, hxs₀, rfl⟩
    have ht₀_aff : IsAffineOpen (L.obj.nonvanishingLocus t₀) := by
      rw [ht₀_eq, U.ι.isAffineOpen_iff_of_isOpenImmersion]
      exact hs₀_aff
    -- Extend `(r i)^k • t₀` to a global section `s` of `L.obj`, then take `r i • s`.
    have hloc := L.obj.isLocalizedModule_basicOpenRestrict_of_qcqs
      isCompact_univ isQuasiSeparated_univ (r i)
    obtain ⟨⟨s, _, k, rfl⟩, hs⟩ :=
      IsLocalizedModule.surj (Submonoid.powers (r i)) (L.obj.basicOpenRestrict (r i)) t₀
    simp only [Submonoid.smul_def] at hs
    rw [L.obj.basicOpen_smul_def, map_pow, L.obj.basicOpenRestrict_apply] at hs
    have hnv : L.obj.nonvanishingLocus (r i • s) = L.obj.nonvanishingLocus t₀ := by
      rw [Scheme.Modules.nonvanishingLocus_smul,
        ← Scheme.Modules.nonvanishingLocus_map (homOfLE (X.basicOpen_le (r i))), ← hs,
        Scheme.Modules.nonvanishingLocus_smul]
      have hbo :
          X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le (r i))).op (r i) ^ k) = U := by
        rcases eq_or_ne k 0 with rfl | hk
        · rw [pow_zero, X.basicOpen_one]
        · rw [X.basicOpen_pow _ (Nat.pos_of_ne_zero hk), X.basicOpen_res, inf_idem]
      rw [hbo, inf_eq_right.mpr (Scheme.Modules.nonvanishingLocus_le t₀)]
    exact ⟨n, hn, L, mk_tensorPow L₀ n, r i • s, hnv ▸ hxt₀, hnv ▸ ht₀_aff⟩

/-- A line-bundle class `a` on `X` is **relatively ample** over `S` along `f : X ⟶ S` if its
restriction to `f⁻¹(U)` is ample for every affine open `U` of `S`
(Stacks Tag 01VG; EGA II, 4.6.1). -/
def IsRelativelyAmple (f : X ⟶ S) (a : LineBundleClass X) : Prop :=
  ∀ U : S.affineOpens, (pullback (f ⁻¹ᵁ U.1).ι a).IsAmple

/-- Unfolding characterization of `IsRelativelyAmple`. -/
theorem isRelativelyAmple_iff {f : X ⟶ S} {a : LineBundleClass X} :
    a.IsRelativelyAmple f ↔ ∀ U : S.affineOpens, (pullback (f ⁻¹ᵁ U.1).ι a).IsAmple :=
  Iff.rfl

/-- If a positive power `aⁿ` is relatively ample over `S`, then so is `a`. -/
theorem IsRelativelyAmple.of_pow {f : X ⟶ S} {a : LineBundleClass X} {n : ℕ} (hn : 0 < n)
    (h : (a ^ n).IsRelativelyAmple f) : a.IsRelativelyAmple f :=
  fun U ↦ IsAmple.of_pow hn (by simpa only [pullback_pow] using h U)

/-- Every positive power `aⁿ` of a relatively ample line-bundle class `a` is relatively ample. -/
theorem IsRelativelyAmple.pow {f : X ⟶ S} {a : LineBundleClass X} {n : ℕ} (hn : 0 < n)
    (h : a.IsRelativelyAmple f) : (a ^ n).IsRelativelyAmple f :=
  fun U ↦ by simpa only [pullback_pow] using (h U).pow hn

/-- For `n > 0`, `aⁿ` is relatively ample over `S` if and only if `a` is. -/
theorem isRelativelyAmple_pow_iff {f : X ⟶ S} {a : LineBundleClass X} {n : ℕ} (hn : 0 < n) :
    (a ^ n).IsRelativelyAmple f ↔ a.IsRelativelyAmple f :=
  ⟨IsRelativelyAmple.of_pow hn, IsRelativelyAmple.pow hn⟩

/-- **Relative ampleness is Zariski-local on the base** (affine-cover form, Stacks Tag 01VK;
EGA II, Proposition 4.6.6). Let `f : X ⟶ S` be quasi-compact and quasi-separated. If every point
`s : S` lies in an affine open `V` of `S` such that `a|_{f⁻¹(V)}` is ample, then `a` is
relatively ample over `S`. -/
theorem IsRelativelyAmple.of_forall_exists_isAffineOpen {f : X ⟶ S} [QuasiCompact f]
    [QuasiSeparated f] {a : LineBundleClass X}
    (h : ∀ s : S, ∃ V : S.Opens, IsAffineOpen V ∧ s ∈ V ∧ (pullback (f ⁻¹ᵁ V).ι a).IsAmple) :
    a.IsRelativelyAmple f := by
  intro U
  have : CompactSpace (f ⁻¹ᵁ U.1) :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage U.2.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ U.1) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ U.1).2).mp
      (f.isQuasiSeparated_preimage U.2.isQuasiSeparated)
  choose V hV hsV hVamp using fun s : U.1 ↦ h s.1
  -- Near each `s ∈ U`, choose an open that is simultaneously a basic open of `U` and of `V s`.
  choose rU rV hrUV hsrU using fun s : U.1 ↦
    exists_basicOpen_le_affine_inter U.2 (hV s) s.1 ⟨s.2, hsV s⟩
  let gU (s : U.1) : Γ((f ⁻¹ᵁ U.1).toScheme, ⊤) :=
    (f ∣_ U.1).appTop (U.1.topIso.inv (rU s))
  have hgU_img (s : U.1) :
      (f ⁻¹ᵁ U.1).ι ''ᵁ (f ⁻¹ᵁ U.1).toScheme.basicOpen (gU s) = f ⁻¹ᵁ S.basicOpen (rU s) := by
    rw [← Scheme.preimage_basicOpen_top (f ∣_ U.1), image_morphismRestrict_preimage,
      U.1.ι_image_basicOpen_topIso_inv]
  refine IsAmple.of_iSup_basicOpen_eq_top gU ?_ fun s ↦ ?_
  · refine top_unique fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f x.1, x.2⟩, ?_⟩
    have hx : x.1 ∈ (f ⁻¹ᵁ U.1).ι ''ᵁ (f ⁻¹ᵁ U.1).toScheme.basicOpen (gU ⟨f x.1, x.2⟩) := by
      rw [hgU_img]
      exact hsrU ⟨f x.1, x.2⟩
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subtype.ext hyx] at hy
  · let gV : Γ((f ⁻¹ᵁ V s).toScheme, ⊤) := (f ∣_ V s).appTop ((V s).topIso.inv (rV s))
    have hgV_img :
        (f ⁻¹ᵁ V s).ι ''ᵁ (f ⁻¹ᵁ V s).toScheme.basicOpen gV = f ⁻¹ᵁ S.basicOpen (rV s) := by
      rw [← Scheme.preimage_basicOpen_top (f ∣_ V s), image_morphismRestrict_preimage,
        (V s).ι_image_basicOpen_topIso_inv]
    -- Both basic opens have the same open image `f⁻¹(D(rU s)) = f⁻¹(D(rV s))` in `X`.
    have hampV := (hVamp s).pullback_basicOpen_ι gV
    rw [pullback_comp] at hampV ⊢
    set jU := ((f ⁻¹ᵁ U.1).toScheme.basicOpen (gU s)).ι ≫ (f ⁻¹ᵁ U.1).ι
    set jV := ((f ⁻¹ᵁ V s).toScheme.basicOpen gV).ι ≫ (f ⁻¹ᵁ V s).ι
    have hjUV : jU.opensRange = jV.opensRange := by
      simp only [jU, jV, Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hgU_img, hgV_img,
        hrUV s]
    let e : ((f ⁻¹ᵁ U.1).toScheme.basicOpen (gU s)).toScheme ≅
        ((f ⁻¹ᵁ V s).toScheme.basicOpen gV).toScheme :=
      jU.isoOpensRange ≪≫ X.isoOfEq hjUV ≪≫ jV.isoOpensRange.symm
    have he : e.hom ≫ jV = jU := by simp [e, Category.assoc]
    rw [← he, ← pullback_comp]
    exact hampV.pullback_of_isIso e.hom

/-- **Relative ampleness is Zariski-local on the base** (Stacks Tag 01VK). Let `f : X ⟶ S` be
quasi-compact and quasi-separated. If `S` is covered by opens `W` over each of which `a|_{f⁻¹(W)}`
is relatively ample along `f ∣_ W`, then `a` is relatively ample over `S`. -/
theorem IsRelativelyAmple.of_forall_exists_opens {f : X ⟶ S} [QuasiCompact f] [QuasiSeparated f]
    {a : LineBundleClass X}
    (h : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧ (pullback (f ⁻¹ᵁ W).ι a).IsRelativelyAmple (f ∣_ W)) :
    a.IsRelativelyAmple f := by
  refine IsRelativelyAmple.of_forall_exists_isAffineOpen fun s ↦ ?_
  obtain ⟨W, hsW, hW⟩ := h s
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, hVW⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hsW W.isOpen
  have hVW' : V ≤ W := hVW
  let V_W : W.toScheme.affineOpens :=
    ⟨W.ι ⁻¹ᵁ V, (W.ι.isAffineOpen_iff_of_isOpenImmersion).mp (by
      rwa [W.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hVW'])⟩
  refine ⟨V, hV, hsV, ?_⟩
  have hamp := hW V_W
  rw [pullback_comp] at hamp
  set j₁ := ((f ∣_ W) ⁻¹ᵁ V_W.1).ι ≫ (f ⁻¹ᵁ W).ι
  have hj₁ : j₁.opensRange = f ⁻¹ᵁ V := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, image_morphismRestrict_preimage,
      W.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hVW']
  let e : (f ⁻¹ᵁ V).toScheme ≅ ((f ∣_ W) ⁻¹ᵁ V_W.1).toScheme :=
    (X.isoOfEq hj₁).symm ≪≫ j₁.isoOpensRange.symm
  have he : e.hom ≫ j₁ = (f ⁻¹ᵁ V).ι := by simp [e, Category.assoc]
  rw [← he, ← pullback_comp]
  exact hamp.pullback_of_isIso e.hom

/-- Over an affine base `S`, a line-bundle class on the source of a quasi-compact quasi-separated
morphism `f : X ⟶ S` is relatively ample over `S` if and only if it is ample on `X`. -/
@[simp]
theorem isRelativelyAmple_iff_isAmple {f : X ⟶ S} [IsAffine S] [QuasiCompact f]
    [QuasiSeparated f] {a : LineBundleClass X} :
    a.IsRelativelyAmple f ↔ a.IsAmple := by
  have : IsIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, ⟨fun x ↦ ⟨⟨x, trivial⟩, rfl⟩⟩⟩
  refine ⟨fun h ↦ (isAmple_pullback_iff_of_isIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι).mp
    (h ⟨⊤, isAffineOpen_top S⟩),
    fun h ↦ IsRelativelyAmple.of_forall_exists_isAffineOpen
      fun _ ↦ ⟨⊤, isAffineOpen_top S, trivial, h.pullback_of_isIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι⟩⟩

/-- **Relative ampleness is preserved under arbitrary base change** (EGA II, Proposition
4.6.13(iii); Stacks Tag 01VK and Tag 0892). Let `f : X ⟶ S` be quasi-compact and quasi-separated,
and let `X' ⟶ S'` be a pullback of `f` along `h : S' ⟶ S` with projection `g : X' ⟶ X`. If `a`
is relatively ample along `f`, then `pullback g a` is relatively ample along `f' : X' ⟶ S'`. -/
theorem IsRelativelyAmple.pullback_of_isPullback {X' : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    [QuasiSeparated f] {g : X' ⟶ X} {f' : X' ⟶ S'} {h : S' ⟶ S}
    (H : IsPullback g f' f h) {a : LineBundleClass X} (ha : a.IsRelativelyAmple f) :
    (pullback g a).IsRelativelyAmple f' := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) H ‹_›
  have : QuasiSeparated f' := MorphismProperty.of_isPullback (P := @QuasiSeparated) H ‹_›
  refine IsRelativelyAmple.of_forall_exists_isAffineOpen fun s' ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (h s')) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hs'V, hVU⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open hsU (h ⁻¹ᵁ U).isOpen
  refine ⟨V, hV, hs'V, ?_⟩
  have hpb := Scheme.Hom.isPullback_resLE H hVU le_rfl
    (Scheme.Hom.preimage_eq_preimage_inf_of_comp_eq H.w hVU)
  have : IsAffine (Scheme.Opens.toScheme U) := hU
  have : IsAffine (Scheme.Opens.toScheme V) := hV
  have : IsAffineHom (h.resLE U V hVU) := isAffineHom_of_isAffine _
  have hpre : f' ⁻¹ᵁ V ≤ g ⁻¹ᵁ (f ⁻¹ᵁ U) :=
    (Scheme.Hom.preimage_eq_preimage_inf_of_comp_eq H.w hVU).trans_le inf_le_left
  have : IsAffineHom (g.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hpre) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip ‹_›
  have hamp := (ha ⟨U, hU⟩).pullback_of_isAffineHom (g.resLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ V) hpre)
  rwa [pullback_comp, Scheme.Hom.resLE_comp_ι, ← pullback_comp] at hamp

end TauCeti.AlgebraicGeometry.LineBundleClass
