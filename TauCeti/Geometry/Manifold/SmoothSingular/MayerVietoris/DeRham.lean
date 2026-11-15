/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.SmoothSingular.DeRham
public import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris.Basic

/-!
# Mayer–Vietoris compatibility of de Rham integration

For open subsets `U` and `V` of a real `C²` manifold with corners `M`, integration of differential
forms over smooth singular simplices (`TauCeti.deRhamIntegration`) assembles into a morphism of
short complexes `TauCeti.deRhamMayerVietorisShortComplexMap` from the de Rham Mayer–Vietoris short
complex `Ω^•(U ⊔ V) ⟶ Ω^•(U) ⊞ Ω^•(V) ⟶ Ω^•(U ⊓ V)` (`TauCeti.mayerVietorisShortComplex`) to the
cochain Mayer–Vietoris short exact sequence of the smooth singular pushout square on `U ⊔ V`
(`TauCeti.isPushout_smoothSingularSubcomplex_sup`).

From this comparison of Mayer–Vietoris complexes we obtain:

* `TauCeti.mayerVietorisShortComplex_δ_comp_homologyMap_deRhamIntegration`: whenever the de Rham
  Mayer–Vietoris short complex is short exact, its connecting morphism commutes via
  `deRhamIntegration` with the smooth singular cohomology Mayer–Vietoris connecting morphism
  `TauCeti.smoothSupCohomologyMayerVietorisδ`.
* `TauCeti.quasiIso_deRhamIntegration_of_shortExact` and
  `TauCeti.deRhamCohomology.bijective_integration_of_shortExact`: the Mayer–Vietoris union step for
  de Rham integration under short exactness of `mayerVietorisShortComplex I U V`.
* `TauCeti.mayerVietorisShortComplex_shortExact_of_disjoint`,
  `TauCeti.isIso_deRhamIntegration_of_isEmpty`, and
  `TauCeti.quasiIso_deRhamIntegration_of_disjoint`: on any `C²` manifold with corners (without
  finite-dimensionality, Hausdorffness, or `σ`-compactness), disjoint open subsets have a short
  exact de Rham Mayer–Vietoris complex, integration is an isomorphism of cochain complexes on an
  empty manifold, and `deRhamIntegration` preserves quasi-isomorphisms across disjoint binary
  unions.
* `TauCeti.quasiIso_deRhamIntegration_sup`, `TauCeti.deRhamCohomology.bijective_integration_sup`,
  and `TauCeti.deRhamCohomology.integration_mayerVietorisδ`: on a Hausdorff `σ`-compact smooth
  manifold modelled on a finite-dimensional real normed space, `deRhamIntegration` satisfies the
  Mayer–Vietoris union step for arbitrary open subsets `U` and `V` and intertwines
  `TauCeti.deRhamCohomology.mayerVietorisδ` with `TauCeti.smoothSupCohomologyMayerVietorisδ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Proposition 18.13 and
  Theorem 18.14.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped ContDiff

namespace TauCeti

/-! ### Short exactness of the de Rham Mayer–Vietoris complex for disjoint opens -/

section DisjointShortExact

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- **Short exactness of the de Rham Mayer–Vietoris complex for disjoint open subsets.** On any
real `C²` manifold with corners (without finite-dimensionality, Hausdorffness, or `σ`-compactness),
if `U` and `V` are disjoint open subsets of `M`, then `mayerVietorisShortComplex I U V` is short
exact: `U ⊓ V` is empty, so every smooth form on `U ⊓ V` is zero. -/
theorem mayerVietorisShortComplex_shortExact_of_disjoint {U V : Opens M} (hUV : Disjoint U V) :
    (mayerVietorisShortComplex I U V).ShortExact := by
  unfold mayerVietorisShortComplex
  exact HomologicalComplex.moduleCat_shortExact_biprod _
    (fun k ↦ deRhamComplexXIso I k) (fun k ↦ deRhamComplexXIso I k)
    (fun k ↦ deRhamComplexXIso I k) (fun k ↦ deRhamComplexXIso I k) _ _ _
    (fun k ↦ -SmoothForm.mpullback (k := k) (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
      (contMDiff_inclusion _))
    (fun k ↦ deRhamComplex.map_f _ _ k) (fun k ↦ deRhamComplex.map_f _ _ k)
    (fun k ↦ deRhamComplex.map_f _ _ k)
    (fun k ↦ by
      rw [HomologicalComplex.neg_f_apply, Preadditive.neg_comp, deRhamComplex.map_f,
        ← Preadditive.comp_neg]
      ext x
      simp)
    (fun _ ↦ SmoothForm.exact_mayerVietoris U V)
    (fun _ ↦ SmoothForm.injective_mayerVietoris U V)
    fun _ φ ↦ ⟨0, Subtype.ext (funext fun x ↦ False.elim (hUV.le_bot x.2))⟩

end DisjointShortExact

/-! ### Quasi-isomorphism characterization and the empty-manifold base case -/

section EmptyAndIff

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- The integration cochain map `deRhamIntegration I M` is a quasi-isomorphism if and only if the
induced cohomology map `deRhamCohomology.integration I M k` is bijective in every degree `k`. -/
theorem quasiIso_deRhamIntegration_iff :
    QuasiIso (deRhamIntegration I M) ↔
      ∀ k, Function.Bijective (deRhamCohomology.integration I M k) := by
  rw [quasiIso_iff]
  refine forall_congr' fun k ↦ ?_
  rw [quasiIsoAt_iff_isIso_homologyMap, deRhamCohomology.homologyMap_deRhamIntegration,
    ConcreteCategory.isIso_iff_bijective]
  -- `ModuleCat.ofHom` has underlying function `deRhamCohomology.integration I M k`.
  rfl

/-- **Isomorphism of de Rham integration on an empty manifold.** On an empty `C²` manifold, both
the de Rham complex and the smooth singular cochain complex are degreewise trivial, so
`deRhamIntegration I M` is an isomorphism of cochain complexes. -/
instance isIso_deRhamIntegration_of_isEmpty [IsEmpty M] : IsIso (deRhamIntegration I M) := by
  have : ∀ k : ℕ, IsIso ((deRhamIntegration I M).f k) := fun k ↦ by
    have hdom : Subsingleton ((deRhamComplex I M).X k) :=
      ⟨fun a b ↦ (deRhamComplexXIso I k).toLinearEquiv.injective
        (Subtype.ext (funext fun x ↦ isEmptyElim x))⟩
    have hcod : Subsingleton
        ((((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).linearYonedaObj
          ℝ (ModuleCat.of ℝ ℝ)).X k) :=
      ⟨fun f g ↦ (smoothSingularSubcomplex I M : SSet).chainComplex_hom_ext fun σ ↦ by
        open Convexity in
        obtain ⟨t⟩ : Nonempty (StdSimplex ℝ (Fin (k + 1))) := inferInstance
        exact isEmptyElim (((TopCat.of M).toSSetObjEquiv (op (SimplexCategory.mk k)) σ.1) t)⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components (deRhamIntegration I M)

/-- On an empty `C²` manifold, `deRhamIntegration I M` is a quasi-isomorphism. -/
theorem quasiIso_deRhamIntegration_of_isEmpty [IsEmpty M] : QuasiIso (deRhamIntegration I M) :=
  inferInstance

/-- On an empty `C²` manifold, `deRhamCohomology.integration I M k` is bijective in every degree. -/
theorem deRhamCohomology.bijective_integration_of_isEmpty [IsEmpty M] (k : ℕ) :
    Function.Bijective (deRhamCohomology.integration I M k) :=
  (quasiIso_deRhamIntegration_iff I M).1 inferInstance k

end EmptyAndIff

/-! ### Comparison of Mayer–Vietoris short complexes on a `C²` manifold -/

section MayerVietorisComparison

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- **Morphism from the de Rham Mayer–Vietoris short complex to the smooth singular cochain
Mayer–Vietoris short complex.** On `U ⊔ V`, integration of smooth forms followed by restriction to
smooth singular simplices small with respect to `{U, V}` commutes with restrictions to `U`, `V`,
and `U ⊓ V`. -/
def deRhamMayerVietorisShortComplexMap (U V : Opens M) :
    mayerVietorisShortComplex I U V ⟶
      SSet.mayerVietorisCochainShortComplex (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (isPushout_smoothSingularSubcomplex_sup I U V).toCommSq where
  τ₁ := deRhamIntegration I ↥(U ⊔ V) ≫
    SSet.cochainComplexMap (SSet.Subcomplex.homOfLE
      (inf_le_left : smoothSingularSubcomplex I ↥(U ⊔ V) ⊓
        (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex
          ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)] ≤ _))
  τ₂ := biprod.map (deRhamIntegration I U) (deRhamIntegration I V)
  τ₃ := deRhamIntegration I ↥(U ⊓ V)
  comm₁₂ := by
    dsimp [mayerVietorisShortComplex]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst,
        ← SSet.cochainComplexMap_comp, toSmoothSmallSingularSubcomplex_homOfLE_left]
      exact (deRhamIntegration_naturality I U (contMDiff_inclusion (le_sup_left : U ≤ U ⊔ V))).symm
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd,
        ← SSet.cochainComplexMap_comp, toSmoothSmallSingularSubcomplex_homOfLE_left]
      exact (deRhamIntegration_naturality I V (contMDiff_inclusion (le_sup_right : V ≤ U ⊔ V))).symm
  comm₂₃ := by
    dsimp [mayerVietorisShortComplex]
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
      exact (deRhamIntegration_naturality I ↥(U ⊓ V)
        (contMDiff_inclusion (inf_le_left : U ⊓ V ≤ U))).symm
    · simp only [biprod.inr_desc_assoc, Preadditive.neg_comp, biprod.inr_map_assoc,
        biprod.inr_desc, Preadditive.comp_neg, neg_inj]
      exact (deRhamIntegration_naturality I ↥(U ⊓ V)
        (contMDiff_inclusion (inf_le_right : U ⊓ V ≤ V))).symm

/-- First component of `deRhamMayerVietorisShortComplexMap`. -/
@[simp]
theorem deRhamMayerVietorisShortComplexMap_τ₁ (U V : Opens M) :
    (deRhamMayerVietorisShortComplexMap I U V).τ₁ =
      deRhamIntegration I ↥(U ⊔ V) ≫
        SSet.cochainComplexMap (SSet.Subcomplex.homOfLE
          (inf_le_left : smoothSingularSubcomplex I ↥(U ⊔ V) ⊓
            (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex
              ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)] ≤ _)) :=
  -- Unfolds the `τ₁` field of `deRhamMayerVietorisShortComplexMap`.
  by rfl

/-- Middle component of `deRhamMayerVietorisShortComplexMap`. -/
@[simp]
theorem deRhamMayerVietorisShortComplexMap_τ₂ (U V : Opens M) :
    (deRhamMayerVietorisShortComplexMap I U V).τ₂ =
      biprod.map (deRhamIntegration I U) (deRhamIntegration I V) :=
  -- Unfolds the `τ₂` field of `deRhamMayerVietorisShortComplexMap`.
  by rfl

/-- Third component of `deRhamMayerVietorisShortComplexMap`. -/
@[simp]
theorem deRhamMayerVietorisShortComplexMap_τ₃ (U V : Opens M) :
    (deRhamMayerVietorisShortComplexMap I U V).τ₃ = deRhamIntegration I ↥(U ⊓ V) :=
  -- Unfolds the `τ₃` field of `deRhamMayerVietorisShortComplexMap`.
  by rfl

/-- **Compatibility of Mayer–Vietoris connecting morphisms with de Rham integration.** Whenever
`mayerVietorisShortComplex I U V` is short exact, its connecting morphism commutes via
`deRhamIntegration` with the smooth singular cohomology Mayer–Vietoris connecting morphism
`smoothSupCohomologyMayerVietorisδ`. -/
@[reassoc]
theorem mayerVietorisShortComplex_δ_comp_homologyMap_deRhamIntegration {U V : Opens M}
    (hSE : (mayerVietorisShortComplex I U V).ShortExact) (k m : ℕ) (h : k + 1 = m := by lia) :
    hSE.δ k m (ComplexShape.up_mk k m h) ≫
        HomologicalComplex.homologyMap (deRhamIntegration I ↥(U ⊔ V)) m =
      HomologicalComplex.homologyMap (deRhamIntegration I ↥(U ⊓ V)) k ≫
        smoothSupCohomologyMayerVietorisδ I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) U V k m h := by
  let S := ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)]
  have hopen : ∀ i, IsOpen (S i) :=
    (U.isOpen.preimage continuous_subtype_val).vecCons (V.isOpen.preimage continuous_subtype_val)
  have hcov : ⋃ i, S i = Set.univ :=
    ((Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)).iUnion_vecCons_pair _).trans
      (Set.eq_univ_of_forall fun x ↦ x.2)
  let e := subcomplexSmallCohomologyIso (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
    (smoothSingularSubcomplex I ↥(U ⊔ V)) S hopen hcov m
  have he : e.hom = HomologicalComplex.homologyMap
      (SSet.cochainComplexMap (SSet.Subcomplex.homOfLE
        (inf_le_left : smoothSingularSubcomplex I ↥(U ⊔ V) ⊓
          (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex S ≤ _))) m :=
    subcomplexSmallCohomologyIso_hom (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
      (smoothSingularSubcomplex I ↥(U ⊔ V)) S hopen hcov m
  have hτ₁ : HomologicalComplex.homologyMap (deRhamMayerVietorisShortComplexMap I U V).τ₁ m =
      HomologicalComplex.homologyMap (deRhamIntegration I ↥(U ⊔ V)) m ≫ e.hom :=
    (HomologicalComplex.homologyMap_comp (deRhamIntegration I ↥(U ⊔ V)) _ m).trans
      (congrArg (_ ≫ ·) he.symm)
  let hS₂ := SSet.shortExact_mayerVietorisCochainShortComplex (ModuleCat.of ℝ ℝ) ℝ
    (ModuleCat.of ℝ ℝ) (isPushout_smoothSingularSubcomplex_sup I U V)
  have hδ : hS₂.δ k m (ComplexShape.up_mk k m h) =
      smoothSupCohomologyMayerVietorisδ I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) U V k m h ≫
        e.hom :=
    (SSet.mayerVietorisCochainδ_def (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
      (isPushout_smoothSingularSubcomplex_sup I U V) k m h).symm.trans
      ((smoothSupCohomologyMayerVietorisδ_comp_homologyMap I (ModuleCat.of ℝ ℝ) ℝ
        (ModuleCat.of ℝ ℝ) U V k m h).symm.trans (congrArg (_ ≫ ·) he.symm))
  apply (cancel_mono e.hom).1
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hτ₁.symm)).trans
    ((HomologicalComplex.HomologySequence.δ_naturality
      (deRhamMayerVietorisShortComplexMap I U V) hSE hS₂ k m (ComplexShape.up_mk k m h)).trans
      ((congrArg (_ ≫ ·) hδ).trans (Category.assoc _ _ _).symm))

/-- **The Mayer–Vietoris union step for de Rham integration (short-exact form).** If
`mayerVietorisShortComplex I U V` is short exact and `deRhamIntegration` is a quasi-isomorphism on
`U`, `V`, and `U ⊓ V`, then `deRhamIntegration` is a quasi-isomorphism on `U ⊔ V`. -/
theorem quasiIso_deRhamIntegration_of_shortExact {U V : Opens M}
    (hSE : (mayerVietorisShortComplex I U V).ShortExact)
    (hU : QuasiIso (deRhamIntegration I U))
    (hV : QuasiIso (deRhamIntegration I V))
    (hinter : QuasiIso (deRhamIntegration I ↥(U ⊓ V))) :
    QuasiIso (deRhamIntegration I ↥(U ⊔ V)) := by
  let ψ := deRhamMayerVietorisShortComplexMap I U V
  have h₂ : QuasiIso ψ.τ₂ := HomologicalComplex.quasiIso_biprod_map _ _
  have hτ₁ : QuasiIso ψ.τ₁ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₁ ψ hSE
      (SSet.shortExact_mayerVietorisCochainShortComplex (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (isPushout_smoothSingularSubcomplex_sup I U V)) h₂ hinter
  have hsmall := quasiIso_cochainComplexMap_homOfLE_inf_smallSingularSubcomplex
    (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (smoothSingularSubcomplex I ↥(U ⊔ V))
    ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)]
    ((U.isOpen.preimage continuous_subtype_val).vecCons
      (V.isOpen.preimage continuous_subtype_val))
    (((Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)).iUnion_vecCons_pair _).trans
      (Set.eq_univ_of_forall fun x ↦ x.2))
  exact quasiIso_of_comp_right (hφ := hsmall) (hφφ' := hτ₁) _ _

/-- **The Mayer–Vietoris union step for de Rham cohomology integration (short-exact form).** If
`mayerVietorisShortComplex I U V` is short exact and `deRhamCohomology.integration` is bijective in
all degrees on `U`, `V`, and `U ⊓ V`, then it is bijective in all degrees on `U ⊔ V`. -/
theorem deRhamCohomology.bijective_integration_of_shortExact {U V : Opens M}
    (hSE : (mayerVietorisShortComplex I U V).ShortExact)
    (hU : ∀ k, Function.Bijective (deRhamCohomology.integration I U k))
    (hV : ∀ k, Function.Bijective (deRhamCohomology.integration I V k))
    (hinter : ∀ k, Function.Bijective (deRhamCohomology.integration I ↥(U ⊓ V) k))
    (k : ℕ) :
    Function.Bijective (deRhamCohomology.integration I ↥(U ⊔ V) k) :=
  (quasiIso_deRhamIntegration_iff I ↥(U ⊔ V)).1
    (quasiIso_deRhamIntegration_of_shortExact I hSE
      ((quasiIso_deRhamIntegration_iff I U).2 hU)
      ((quasiIso_deRhamIntegration_iff I V).2 hV)
      ((quasiIso_deRhamIntegration_iff I ↥(U ⊓ V)).2 hinter)) k

/-- **Disjoint-union invariance of de Rham integration on a `C²` manifold.** For disjoint open
subsets `U` and `V` of any `C²` manifold with corners (without finite-dimensionality,
Hausdorffness, or `σ`-compactness), if `deRhamIntegration` is a quasi-isomorphism on `U` and on
`V`, then it is a quasi-isomorphism on `U ⊔ V`. -/
theorem quasiIso_deRhamIntegration_of_disjoint {U V : Opens M} (hUV : Disjoint U V)
    (hU : QuasiIso (deRhamIntegration I U))
    (hV : QuasiIso (deRhamIntegration I V)) :
    QuasiIso (deRhamIntegration I ↥(U ⊔ V)) := by
  have : IsEmpty ↥(U ⊓ V) := ⟨fun x ↦ hUV.le_bot x.2⟩
  exact quasiIso_deRhamIntegration_of_shortExact I
    (mayerVietorisShortComplex_shortExact_of_disjoint I hUV) hU hV
    (quasiIso_deRhamIntegration_of_isEmpty I ↥(U ⊓ V))

/-- For disjoint open subsets `U` and `V` of any `C²` manifold with corners, if
`deRhamCohomology.integration` is bijective in all degrees on `U` and on `V`, then it is bijective
in all degrees on `U ⊔ V`. -/
theorem deRhamCohomology.bijective_integration_of_disjoint {U V : Opens M} (hUV : Disjoint U V)
    (hU : ∀ k, Function.Bijective (deRhamCohomology.integration I U k))
    (hV : ∀ k, Function.Bijective (deRhamCohomology.integration I V k))
    (k : ℕ) :
    Function.Bijective (deRhamCohomology.integration I ↥(U ⊔ V) k) :=
  (quasiIso_deRhamIntegration_iff I ↥(U ⊔ V)).1
    (quasiIso_deRhamIntegration_of_disjoint I hUV
      ((quasiIso_deRhamIntegration_iff I U).2 hU)
      ((quasiIso_deRhamIntegration_iff I V).2 hV)) k

end MayerVietorisComparison

/-! ### Mayer–Vietoris union step and connecting-map compatibility on paracompact manifolds -/

section ParacompactSmooth

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **The Mayer–Vietoris union step for de Rham integration.** On a Hausdorff `σ`-compact smooth
manifold modelled on a finite-dimensional real normed space, if `deRhamIntegration` is a
quasi-isomorphism on `U`, `V`, and `U ⊓ V`, then it is a quasi-isomorphism on `U ⊔ V`. -/
theorem quasiIso_deRhamIntegration_sup {U V : Opens M}
    (hU : QuasiIso (deRhamIntegration I U))
    (hV : QuasiIso (deRhamIntegration I V))
    (hinter : QuasiIso (deRhamIntegration I ↥(U ⊓ V))) :
    QuasiIso (deRhamIntegration I ↥(U ⊔ V)) :=
  quasiIso_deRhamIntegration_of_shortExact I (mayerVietorisShortComplex_shortExact U V) hU hV
    hinter

namespace deRhamCohomology

/-- **The Mayer–Vietoris union step for `deRhamCohomology.integration`.** On a Hausdorff
`σ`-compact smooth manifold modelled on a finite-dimensional real normed space, if integration is
bijective in all degrees on `U`, `V`, and `U ⊓ V`, then it is bijective in all degrees on
`U ⊔ V`. -/
theorem bijective_integration_sup {U V : Opens M}
    (hU : ∀ k, Function.Bijective (integration I U k))
    (hV : ∀ k, Function.Bijective (integration I V k))
    (hinter : ∀ k, Function.Bijective (integration I ↥(U ⊓ V) k))
    (k : ℕ) :
    Function.Bijective (integration I ↥(U ⊔ V) k) :=
  bijective_integration_of_shortExact I (mayerVietorisShortComplex_shortExact U V) hU hV hinter k

/-- Categorical form of the compatibility between `deRhamCohomology.mayerVietorisδ` and
`smoothSupCohomologyMayerVietorisδ` under `deRhamIntegration`. -/
@[reassoc]
theorem ofHom_mayerVietorisδ_comp_homologyMap_deRhamIntegration (U V : Opens M) (k : ℕ) :
    ModuleCat.ofHom (mayerVietorisδ I U V k) ≫
        HomologicalComplex.homologyMap (deRhamIntegration I ↥(U ⊔ V)) (k + 1) =
      HomologicalComplex.homologyMap (deRhamIntegration I ↥(U ⊓ V)) k ≫
        smoothSupCohomologyMayerVietorisδ I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
          U V k (k + 1) rfl := by
  rw [ofHom_mayerVietorisδ]
  exact mayerVietorisShortComplex_δ_comp_homologyMap_deRhamIntegration I
    (mayerVietorisShortComplex_shortExact U V) k (k + 1) rfl

/-- **Integration commutes with the Mayer–Vietoris connecting homomorphism.** On a Hausdorff
`σ`-compact smooth manifold modelled on a finite-dimensional real normed space, integrating a
de Rham cohomology class after applying the de Rham Mayer–Vietoris connecting map agrees with
applying the smooth singular cohomology Mayer–Vietoris connecting map after integrating. -/
theorem integration_mayerVietorisδ (U V : Opens M) (k : ℕ)
    (c : deRhamCohomology I (U ⊓ V : Opens M) k) :
    integration I ↥(U ⊔ V) (k + 1) (mayerVietorisδ I U V k c) =
      smoothSupCohomologyMayerVietorisδ I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        U V k (k + 1) rfl (integration I ↥(U ⊓ V) k c) := by
  have h := ofHom_mayerVietorisδ_comp_homologyMap_deRhamIntegration I U V k
  rw [homologyMap_deRhamIntegration, homologyMap_deRhamIntegration] at h
  exact ConcreteCategory.congr_hom h c

end deRhamCohomology

end ParacompactSmooth

end TauCeti
