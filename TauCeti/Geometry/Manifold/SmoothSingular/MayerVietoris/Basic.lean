/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Subcomplex
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision

/-!
# Mayer–Vietoris sequences for smooth singular homology and cohomology

Let `M` be a charted space over a real model with corners `I`, and let `U` and `V` be open subsets
of `M`. For smooth singular simplices, barycentric subdivision preserves smoothness
(`TauCeti.smoothSingularSubcomplex` is affinely stable), so the small-chain and small-cochain
theorems on affinely stable subcomplexes (`TauCeti.subcomplexSmallHomologyIso` and
`TauCeti.subcomplexSmallCohomologyIso`) identify the homology and cohomology of smooth simplices
with those of smooth simplices subordinate to `{U, V}` whenever `U ⊔ V = ⊤`.

Combined with the pushout square formed by the smooth singular subcomplexes of `U ⊓ V`, `U`, `V`,
and the smooth simplices subordinate to `{U, V}` (`TauCeti.isPushout_smoothSingularSubcomplex_inter`
on `M`, and `TauCeti.isPushout_smoothSingularSubcomplex_sup` on `U ⊔ V`), this yields:

* the Mayer–Vietoris long exact sequence in smooth singular homology, its naturality under smooth
  maps, its compatibility with the continuous singular Mayer–Vietoris connecting morphism, and its
  splitting into a direct-sum isomorphism when `U` and `V` are disjoint;
* the dual Mayer–Vietoris long exact sequence in smooth singular cohomology and its compatibility
  with continuous singular cohomology;
* the Mayer–Vietoris step of the smoothing theorem: if the inclusion of smooth singular chains into
  continuous singular chains (or the dual restriction of cochains) is a quasi-isomorphism on `U`,
  `V`, and `U ⊓ V`, then it is a quasi-isomorphism on `U ⊔ V` (and on `M` when `U ⊔ V = ⊤`).

Only `[TopologicalSpace M] [ChartedSpace H M]` is required throughout; no smoothness of transition
maps, finite-dimensionality, or separation assumption is needed.

## Main declarations

* `TauCeti.toSmoothSmallSingularSubcomplex` and `TauCeti.smoothSmallSingularSubcomplexMap`:
  morphisms into and between smooth singular subcomplexes subordinate to covers.
* `TauCeti.isPushout_smoothSingularSubcomplex_inter` and
  `TauCeti.isPushout_smoothSingularSubcomplex_sup`: the pushout squares of smooth singular
  subcomplexes of `U ⊓ V`, `U`, and `V` inside `M` and inside `U ⊔ V`.
* `TauCeti.smoothMayerVietorisδ`, `TauCeti.smoothMayerVietoris_exact₁`,
  `TauCeti.smoothMayerVietoris_exact₂`, `TauCeti.smoothMayerVietoris_exact₃`: the Mayer–Vietoris
  long exact sequence in smooth singular homology, natural via
  `TauCeti.smoothMayerVietorisδ_naturality` and compatible with `TopCat.mayerVietorisδ` via
  `TauCeti.smoothMayerVietorisδ_comp_homologyMap_ι`.
* `TauCeti.smoothCohomologyMayerVietorisδ`, `TauCeti.smoothCohomologyMayerVietoris_exact₁`,
  `TauCeti.smoothCohomologyMayerVietoris_exact₂`, `TauCeti.smoothCohomologyMayerVietoris_exact₃`,
  and `TauCeti.smoothSupCohomologyMayerVietorisδ`: the Mayer–Vietoris long exact sequence in smooth
  singular cohomology, natural via `TauCeti.smoothCohomologyMayerVietorisδ_naturality` and
  compatible with `TopCat.singularCohomologyMayerVietorisδ` via
  `TauCeti.singularCohomologyMayerVietorisδ_comp_homologyMap_ι`.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`,
  `TauCeti.quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top`, and
  `TauCeti.quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι_sup`: the Mayer–Vietoris union
  steps for the inclusion of smooth singular chains and restriction of singular cochains.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7 and
  Theorem 18.14.
* A. Hatcher, *Algebraic Topology*, Sections 2.2 and 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits Topology TopologicalSpace Simplicial Opposite
open scoped ContDiff

universe u v w

namespace TauCeti

/-! ### Monomorphisms and cover-subordinate smooth singular subcomplexes -/

section Subcomplex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]

/-- An injective smooth map induces a monomorphism of smooth singular subcomplexes. -/
theorem mono_smoothSingularSubcomplexMap_of_injective {φ : M → N} (hφ : ContMDiff I J ∞ φ)
    (hinj : Function.Injective φ) : Mono (smoothSingularSubcomplexMap φ hφ) := by
  have hmono : Mono (TopCat.ofHom ⟨φ, hφ.continuous⟩) := (TopCat.mono_iff_injective _).2 hinj
  have : Mono (TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩)) := Functor.map_mono _ _
  have : Mono ((smoothSingularSubcomplex I M).ι ≫
      TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩)) := mono_comp _ _
  exact mono_of_mono_fac (smoothSingularSubcomplexMap_ι hφ)

/-- The inclusion of nested open subsets induces a monomorphism of smooth singular subcomplexes. -/
instance mono_smoothSingularSubcomplexMap_inclusion {U V : Opens M} (h : U ≤ V) :
    Mono (smoothSingularSubcomplexMap (I := I) (J := I) (Opens.inclusion h)
      (contMDiff_inclusion h)) :=
  mono_smoothSingularSubcomplexMap_of_injective (contMDiff_inclusion h) (Set.inclusion_injective h)

/-- The ambient inclusion of an open subset induces a monomorphism of smooth singular
subcomplexes. -/
instance mono_smoothSingularSubcomplexMap_subtypeVal (U : Opens M) :
    Mono (smoothSingularSubcomplexMap (I := I) (J := I) (Subtype.val : U → M)
      contMDiff_subtype_val) :=
  mono_smoothSingularSubcomplexMap_of_injective contMDiff_subtype_val Subtype.val_injective

/-- A smooth map `φ : M → N` taking values in a single member `S i` of a family of subsets of `N`
carries smooth singular simplices of `M` to smooth singular simplices of `N` subordinate to `S`. -/
def toSmoothSmallSingularSubcomplex {ι : Type*} (S : ι → Set N) (φ : M → N)
    (hφ : ContMDiff I J ∞ φ) {i : ι} (hφS : ∀ x, φ x ∈ S i) :
    (smoothSingularSubcomplex I M : SSet) ⟶
      ((smoothSingularSubcomplex J N ⊓ (TopCat.of N).smallSingularSubcomplex S :
        (TopCat.toSSet.obj (TopCat.of N)).Subcomplex) : SSet) :=
  SSet.Subcomplex.lift
    ((smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩))
    (by
      rintro k _ ⟨σ, rfl⟩
      refine ⟨smoothSingularSubcomplex_le_preimage hφ k σ.2, ?_⟩
      rw [TopCat.mem_smallSingularSubcomplex_iff]
      refine ⟨i, ?_⟩
      rintro _ ⟨z, rfl⟩
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app,
        TypeCat.ofHom_apply]
      exact hφS _)

@[reassoc (attr := simp)]
lemma toSmoothSmallSingularSubcomplex_ι {ι : Type*} (S : ι → Set N) (φ : M → N)
    (hφ : ContMDiff I J ∞ φ) {i : ι} (hφS : ∀ x, φ x ∈ S i) :
    toSmoothSmallSingularSubcomplex S φ hφ hφS ≫
        (smoothSingularSubcomplex J N ⊓ (TopCat.of N).smallSingularSubcomplex S).ι =
      (smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩) :=
  SSet.Subcomplex.lift_ι _ _

@[reassoc (attr := simp)]
lemma toSmoothSmallSingularSubcomplex_homOfLE_left {ι : Type*} (S : ι → Set N) (φ : M → N)
    (hφ : ContMDiff I J ∞ φ) {i : ι} (hφS : ∀ x, φ x ∈ S i) :
    toSmoothSmallSingularSubcomplex S φ hφ hφS ≫
        SSet.Subcomplex.homOfLE
          (inf_le_left : smoothSingularSubcomplex J N ⊓ (TopCat.of N).smallSingularSubcomplex S ≤
            smoothSingularSubcomplex J N) =
      smoothSingularSubcomplexMap φ hφ := by
  rw [← cancel_mono (smoothSingularSubcomplex J N).ι, Category.assoc,
    SSet.Subcomplex.homOfLE_ι, toSmoothSmallSingularSubcomplex_ι, smoothSingularSubcomplexMap_ι]

@[reassoc]
lemma toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right {ι : Type*} (S : ι → Set M)
    {W : Opens M} {i : ι} (hW : (W : Set M) ⊆ S i) (hW' : ∀ x : W, x.1 ∈ S i) :
    toSmoothSmallSingularSubcomplex S (Subtype.val : W → M) (contMDiff_subtype_val (I := I)) hW' ≫
      SSet.Subcomplex.homOfLE
        (inf_le_right : smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S ≤
          (TopCat.of M).smallSingularSubcomplex S) =
      (smoothSingularSubcomplex I W).ι ≫
        TopCat.toSmallSingularSubcomplex (X := TopCat.of M) S hW := by
  rw [← cancel_mono ((TopCat.of M).smallSingularSubcomplex S).ι, Category.assoc,
    SSet.Subcomplex.homOfLE_ι, toSmoothSmallSingularSubcomplex_ι, Category.assoc,
    TopCat.toSmallSingularSubcomplex_ι]
  -- `ContinuousMap.subtypeVal` has underlying function `Subtype.val`.
  rfl

/-- A smooth map `φ : M → N` carrying each member `S i` into `T (r i)` induces a map between the
subcomplexes of smooth singular simplices subordinate to `S` and to `T`. -/
def smoothSmallSingularSubcomplexMap {ι κ : Type*} (S : ι → Set M) (T : κ → Set N)
    (φ : M → N) (hφ : ContMDiff I J ∞ φ) (r : ι → κ) (hf : ∀ i, Set.MapsTo φ (S i) (T (r i))) :
    ((smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S :
      (TopCat.toSSet.obj (TopCat.of M)).Subcomplex) : SSet) ⟶
      ((smoothSingularSubcomplex J N ⊓ (TopCat.of N).smallSingularSubcomplex T :
        (TopCat.toSSet.obj (TopCat.of N)).Subcomplex) : SSet) :=
  SSet.Subcomplex.lift
    ((smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S).ι ≫
      TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩))
    (by
      rintro k _ ⟨σ, rfl⟩
      refine ⟨smoothSingularSubcomplex_le_preimage hφ k σ.2.1, ?_⟩
      obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff _ _ _).1 σ.2.2
      rw [TopCat.mem_smallSingularSubcomplex_iff]
      refine ⟨r i, ?_⟩
      rintro _ ⟨z, rfl⟩
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app,
        TypeCat.ofHom_apply]
      exact hf i (hi ⟨z, rfl⟩))

@[reassoc (attr := simp)]
lemma smoothSmallSingularSubcomplexMap_ι {ι κ : Type*} (S : ι → Set M) (T : κ → Set N)
    (φ : M → N) (hφ : ContMDiff I J ∞ φ) (r : ι → κ) (hf : ∀ i, Set.MapsTo φ (S i) (T (r i))) :
    smoothSmallSingularSubcomplexMap S T φ hφ r hf ≫
        (smoothSingularSubcomplex J N ⊓ (TopCat.of N).smallSingularSubcomplex T).ι =
      (smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S).ι ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩) :=
  SSet.Subcomplex.lift_ι _ _

@[reassoc (attr := simp)]
lemma smoothSmallSingularSubcomplexMap_homOfLE_left {ι κ : Type*} (S : ι → Set M) (T : κ → Set N)
    (φ : M → N) (hφ : ContMDiff I J ∞ φ) (r : ι → κ) (hf : ∀ i, Set.MapsTo φ (S i) (T (r i))) :
    smoothSmallSingularSubcomplexMap S T φ hφ r hf ≫
        SSet.Subcomplex.homOfLE inf_le_left =
      SSet.Subcomplex.homOfLE inf_le_left ≫ smoothSingularSubcomplexMap φ hφ := by
  rw [← cancel_mono (smoothSingularSubcomplex J N).ι, Category.assoc, Category.assoc,
    SSet.Subcomplex.homOfLE_ι, smoothSmallSingularSubcomplexMap_ι, smoothSingularSubcomplexMap_ι,
    SSet.Subcomplex.homOfLE_ι_assoc]

@[reassoc (attr := simp)]
lemma smoothSmallSingularSubcomplexMap_homOfLE_right {ι κ : Type*} (S : ι → Set M) (T : κ → Set N)
    (φ : M → N) (hφ : ContMDiff I J ∞ φ) (r : ι → κ) (hf : ∀ i, Set.MapsTo φ (S i) (T (r i))) :
    smoothSmallSingularSubcomplexMap S T φ hφ r hf ≫
        SSet.Subcomplex.homOfLE inf_le_right =
      SSet.Subcomplex.homOfLE inf_le_right ≫
        (TopCat.of M).smallSingularSubcomplexMap S T (TopCat.ofHom ⟨φ, hφ.continuous⟩) r hf := by
  rw [← cancel_mono ((TopCat.of N).smallSingularSubcomplex T).ι, Category.assoc, Category.assoc,
    SSet.Subcomplex.homOfLE_ι, smoothSmallSingularSubcomplexMap_ι,
    TopCat.smallSingularSubcomplexMap_ι, SSet.Subcomplex.homOfLE_ι_assoc]

@[reassoc]
lemma toSmoothSmallSingularSubcomplex_comp_smoothSmallSingularSubcomplexMap
    {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    {K : ModelWithCorners ℝ E'' H''} {P : Type u} [TopologicalSpace P] [ChartedSpace H'' P]
    {E''' H''' : Type*} [NormedAddCommGroup E'''] [NormedSpace ℝ E'''] [TopologicalSpace H''']
    {L : ModelWithCorners ℝ E''' H'''} {Q : Type u} [TopologicalSpace Q] [ChartedSpace H''' Q]
    {ι κ : Type*} (S : ι → Set M) (T : κ → Set N)
    (φ : P → M) (hφ : ContMDiff K I ∞ φ) {i : ι} (hφS : ∀ x, φ x ∈ S i)
    (ψ : M → N) (hψ : ContMDiff I J ∞ ψ) (r : ι → κ) (hf : ∀ a, Set.MapsTo ψ (S a) (T (r a)))
    (g : P → Q) (hg : ContMDiff K L ∞ g)
    (χ : Q → N) (hχ : ContMDiff L J ∞ χ) {j : κ} (hχT : ∀ y, χ y ∈ T j)
    (hcomm : ψ ∘ φ = χ ∘ g) :
    toSmoothSmallSingularSubcomplex S φ hφ hφS ≫
        smoothSmallSingularSubcomplexMap S T ψ hψ r hf =
      smoothSingularSubcomplexMap g hg ≫ toSmoothSmallSingularSubcomplex T χ hχ hχT := by
  rw [← cancel_mono (smoothSingularSubcomplex J N ⊓ (TopCat.of N).smallSingularSubcomplex T).ι,
    Category.assoc, Category.assoc, smoothSmallSingularSubcomplexMap_ι,
    toSmoothSmallSingularSubcomplex_ι_assoc, toSmoothSmallSingularSubcomplex_ι,
    smoothSingularSubcomplexMap_ι_assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  have hfg : TopCat.ofHom ⟨φ, hφ.continuous⟩ ≫ TopCat.ofHom ⟨ψ, hψ.continuous⟩ =
      TopCat.ofHom ⟨g, hg.continuous⟩ ≫ TopCat.ofHom ⟨χ, hχ.continuous⟩ := by
    ext x
    exact congrFun hcomm x
  rw [hfg]

end Subcomplex

/-! ### Pushout squares of smooth singular subcomplexes -/

section Pushout

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- The image in `M` of the smooth singular simplices of an open subset `W` consists of those
smooth singular simplices of `M` whose image lies in `W`. -/
@[simp]
theorem range_ι_comp_toSSet_subtypeVal (W : Opens M) :
    SSet.Subcomplex.range
        ((smoothSingularSubcomplex I W).ι ≫
          TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M)))) =
      smoothSingularSubcomplex I M ⊓
        SSet.Subcomplex.range
          (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M)))) := by
  ext n σ
  -- Infimum of subcomplexes is intersection of their `n`-simplex sets.
  change σ ∈ (SSet.Subcomplex.range _).obj n ↔
    σ ∈ (smoothSingularSubcomplex I M).obj n ∧ σ ∈ (SSet.Subcomplex.range _).obj n
  refine ⟨?_, ?_⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨smoothSingularSubcomplex_le_preimage contMDiff_subtype_val n τ.2, ⟨τ.1, rfl⟩⟩
  · rintro ⟨hσM, hσW⟩
    have hsub : Set.range ((TopCat.of M).toSSetObjEquiv n σ) ⊆ W :=
      (TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M) (W : Set M) n σ).1 hσW
    let τ₀ : (TopCat.toSSet.obj (TopCat.of W)).obj n :=
      ((TopCat.of W).toSSetObjEquiv n).symm
        ⟨Set.codRestrict _ _ fun z ↦ hsub ⟨z, rfl⟩, (map_continuous _).codRestrict _⟩
    have himg : (TopCat.toSSet.map
        (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M)))).app n τ₀ = σ := by
      apply ((TopCat.of M).toSSetObjEquiv n).injective
      ext z
      rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
      simp [τ₀]
      -- Evaluating `subtypeVal` on `Set.codRestrict` recovers the original value.
      rfl
    have hτ₀ : τ₀ ∈ (smoothSingularSubcomplex I W).obj n := by
      rw [mem_smoothSingularSubcomplex_iff, ← ContMDiffOnSubset.subtypeVal_comp_iff]
      convert (mem_smoothSingularSubcomplex_iff σ).1 hσM using 1
      funext x
      simp [τ₀]
    exact ⟨⟨τ₀, hτ₀⟩, himg⟩

/-- For nested open subsets `W ≤ Z` of `M`, the image in `Z` of the smooth singular simplices of
`W` consists of those smooth singular simplices of `Z` whose underlying map takes values in `W`. -/
theorem range_ι_comp_toSSet_inclusion {W Z : Opens M} (hWZ : W ≤ Z) :
    SSet.Subcomplex.range
        ((smoothSingularSubcomplex I W).ι ≫
          TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion hWZ,
            continuous_inclusion (hWZ : (W : Set M) ⊆ Z)⟩)) =
      smoothSingularSubcomplex I Z ⊓
        SSet.Subcomplex.range
          (TopCat.toSSet.map
            (TopCat.ofHom (ContinuousMap.subtypeVal (Subtype.val ⁻¹' (W : Set M) : Set Z)))) := by
  ext n σ
  -- Infimum of subcomplexes is intersection of their `n`-simplex sets.
  change σ ∈ (SSet.Subcomplex.range _).obj n ↔
    σ ∈ (smoothSingularSubcomplex I Z).obj n ∧ σ ∈ (SSet.Subcomplex.range _).obj n
  refine ⟨?_, ?_⟩
  · rintro ⟨τ, rfl⟩
    refine ⟨smoothSingularSubcomplex_le_preimage (contMDiff_inclusion hWZ) n τ.2, ?_⟩
    rw [TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of Z)]
    rintro _ ⟨z, rfl⟩
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app,
      TypeCat.ofHom_apply]
    exact ((TopCat.of W).toSSetObjEquiv n τ.1 z).2
  · rintro ⟨hσZ, hσW⟩
    have hsub : Set.range ((TopCat.of Z).toSSetObjEquiv n σ) ⊆ Subtype.val ⁻¹' (W : Set M) :=
      (TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of Z) _ n σ).1 hσW
    let τ₀ : (TopCat.toSSet.obj (TopCat.of W)).obj n :=
      ((TopCat.of W).toSSetObjEquiv n).symm
        ⟨fun z ↦ ⟨(((TopCat.of Z).toSSetObjEquiv n σ z) : M), hsub ⟨z, rfl⟩⟩,
          (continuous_subtype_val.comp (map_continuous _)).codRestrict _⟩
    have himg : (TopCat.toSSet.map
        (TopCat.ofHom ⟨Opens.inclusion hWZ,
          continuous_inclusion (hWZ : (W : Set M) ⊆ Z)⟩)).app n τ₀ = σ := by
      apply ((TopCat.of Z).toSSetObjEquiv n).injective
      ext z
      rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
      simp [τ₀]
      -- Evaluating the constructed `ContinuousMap` at `z` returns `σ z`.
      rfl
    have hτ₀ : τ₀ ∈ (smoothSingularSubcomplex I W).obj n := by
      rw [← smoothSingularSubcomplex_preimage_inclusion (I := I) hWZ, SSet.Subcomplex.preimage_obj,
        Set.mem_preimage, himg]
      exact hσZ
    exact ⟨⟨τ₀, hτ₀⟩, himg⟩

private lemma bicartSq_range_smoothSingularSubcomplex_subtypeVal (U V : Opens M) :
    SSet.Subcomplex.BicartSq
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊓ V : Opens M) : Set M)))))
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I U).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M)))))
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I V).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (V : Set M)))))
      (smoothSingularSubcomplex I M ⊓
        (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)]) := by
  refine ⟨?_, ?_⟩
  · rw [range_ι_comp_toSSet_subtypeVal, range_ι_comp_toSSet_subtypeVal]
    ext n σ
    -- Lattice operations on subcomplexes act pointwise on their `n`-simplex sets.
    change (σ ∈ (smoothSingularSubcomplex I M).obj n ∧ σ ∈ (SSet.Subcomplex.range _).obj n) ∨
        (σ ∈ (smoothSingularSubcomplex I M).obj n ∧ σ ∈ (SSet.Subcomplex.range _).obj n) ↔
      σ ∈ (smoothSingularSubcomplex I M).obj n ∧
        σ ∈ ((TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)]).obj n
    rw [TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M),
      TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M),
      TopCat.mem_smallSingularSubcomplex_iff]
    simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact and_or_left.symm
  · rw [range_ι_comp_toSSet_subtypeVal, range_ι_comp_toSSet_subtypeVal,
      range_ι_comp_toSSet_subtypeVal]
    ext n σ
    -- Infimum of subcomplexes is intersection of their `n`-simplex sets.
    change (σ ∈ (smoothSingularSubcomplex I M).obj n ∧ σ ∈ (SSet.Subcomplex.range _).obj n) ∧
        (σ ∈ (smoothSingularSubcomplex I M).obj n ∧ σ ∈ (SSet.Subcomplex.range _).obj n) ↔
      σ ∈ (smoothSingularSubcomplex I M).obj n ∧ σ ∈ (SSet.Subcomplex.range _).obj n
    rw [TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M),
      TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M),
      TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M), Opens.coe_inf]
    exact ⟨fun ⟨⟨hs, hu⟩, _, hv⟩ ↦ ⟨hs, Set.subset_inter hu hv⟩,
      fun ⟨hs, huv⟩ ↦ ⟨⟨hs, huv.trans Set.inter_subset_left⟩, hs, huv.trans Set.inter_subset_right⟩⟩

variable (I) in
/-- **Pushout square of smooth singular subcomplexes in `M`.** For open subsets `U` and `V` of `M`,
the smooth singular subcomplexes of `U ⊓ V`, `U`, and `V` form a pushout square with the smooth
singular simplices of `M` lying in `U` or in `V`. -/
theorem isPushout_smoothSingularSubcomplex_inter (U V : Opens M) :
    IsPushout
      (smoothSingularSubcomplexMap (I := I) (J := I)
        (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _))
      (smoothSingularSubcomplexMap (I := I) (J := I)
        (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _))
      (toSmoothSmallSingularSubcomplex ![(U : Set M), (V : Set M)] (Subtype.val : U → M)
        contMDiff_subtype_val
        fun x ↦ Eq.mpr (congrArg ((x : M) ∈ ·)
          (Matrix.cons_val_zero (U : Set M) ![(V : Set M)])) (SetLike.mem_coe.2 x.2))
      (toSmoothSmallSingularSubcomplex ![(U : Set M), (V : Set M)] (Subtype.val : V → M)
        contMDiff_subtype_val
        fun x ↦ Eq.mpr (congrArg ((x : M) ∈ ·)
          ((Matrix.cons_val_one (U : Set M) ![(V : Set M)]).trans
            (Matrix.cons_val_zero (V : Set M) ![]))) (SetLike.mem_coe.2 x.2)) := by
  let fI := (smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫
    TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊓ V : Opens M) : Set M)))
  let fU := (smoothSingularSubcomplex I U).ι ≫
    TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M)))
  let fV := (smoothSingularSubcomplex I V).ι ≫
    TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (V : Set M)))
  let D := smoothSingularSubcomplex I M ⊓
    (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)]
  have : Mono fI := mono_comp _ _
  have : Mono fU := mono_comp _ _
  have : Mono fV := mono_comp _ _
  refine (bicartSq_range_smoothSingularSubcomplex_subtypeVal (I := I) U V).isPushout.of_iso'
    (asIso (SSet.Subcomplex.toRange fI)) (asIso (SSet.Subcomplex.toRange fU))
    (asIso (SSet.Subcomplex.toRange fV)) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (SSet.Subcomplex.range fU).ι]
    -- Composing `toRange` with the subcomplex inclusion recovers `fI`.
    change fI = smoothSingularSubcomplexMap _ _ ≫ fU
    rw [smoothSingularSubcomplexMap_ι_assoc, ← CategoryTheory.Functor.map_comp]
    -- `Subtype.val ∘ Opens.inclusion` is definitionally `Subtype.val`.
    rfl
  · rw [← cancel_mono (SSet.Subcomplex.range fV).ι]
    -- Composing `toRange` with the subcomplex inclusion recovers `fI`.
    change fI = smoothSingularSubcomplexMap _ _ ≫ fV
    rw [smoothSingularSubcomplexMap_ι_assoc, ← CategoryTheory.Functor.map_comp]
    -- `Subtype.val ∘ Opens.inclusion` is definitionally `Subtype.val`.
    rfl
  · rw [← cancel_mono D.ι]
    simp only [D, fU, asIso_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι, toSmoothSmallSingularSubcomplex_ι]
    -- `ContinuousMap.subtypeVal ↑U` has underlying function `Subtype.val`.
    rfl
  · rw [← cancel_mono D.ι]
    simp only [D, fV, asIso_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι, toSmoothSmallSingularSubcomplex_ι]
    -- `ContinuousMap.subtypeVal ↑V` has underlying function `Subtype.val`.
    rfl

private lemma bicartSq_range_smoothSingularSubcomplex_inclusion (U V : Opens M) :
    SSet.Subcomplex.BicartSq
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion (inf_le_sup : U ⊓ V ≤ U ⊔ V),
          continuous_inclusion (inf_le_sup : ((U ⊓ V : Opens M) : Set M) ⊆ U ⊔ V)⟩)))
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I U).ι ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion (le_sup_left : U ≤ U ⊔ V),
          continuous_inclusion (le_sup_left : (U : Set M) ⊆ U ⊔ V)⟩)))
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I V).ι ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion (le_sup_right : V ≤ U ⊔ V),
          continuous_inclusion (le_sup_right : (V : Set M) ⊆ U ⊔ V)⟩)))
      (smoothSingularSubcomplex I ↥(U ⊔ V) ⊓
        (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex
          ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)]) := by
  refine ⟨?_, ?_⟩
  · rw [range_ι_comp_toSSet_inclusion, range_ι_comp_toSSet_inclusion]
    ext n σ
    -- Lattice operations on subcomplexes act pointwise on their `n`-simplex sets.
    change (σ ∈ (smoothSingularSubcomplex I ↥(U ⊔ V)).obj n ∧
          σ ∈ (SSet.Subcomplex.range _).obj n) ∨
        (σ ∈ (smoothSingularSubcomplex I ↥(U ⊔ V)).obj n ∧
          σ ∈ (SSet.Subcomplex.range _).obj n) ↔
      σ ∈ (smoothSingularSubcomplex I ↥(U ⊔ V)).obj n ∧
        σ ∈ ((TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex _).obj n
    rw [TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of ↥(U ⊔ V)),
      TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of ↥(U ⊔ V)),
      TopCat.mem_smallSingularSubcomplex_iff]
    simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact and_or_left.symm
  · rw [range_ι_comp_toSSet_inclusion, range_ι_comp_toSSet_inclusion,
      range_ι_comp_toSSet_inclusion]
    ext n σ
    -- Infimum of subcomplexes is intersection of their `n`-simplex sets.
    change (σ ∈ (smoothSingularSubcomplex I ↥(U ⊔ V)).obj n ∧
          σ ∈ (SSet.Subcomplex.range _).obj n) ∧
        (σ ∈ (smoothSingularSubcomplex I ↥(U ⊔ V)).obj n ∧
          σ ∈ (SSet.Subcomplex.range _).obj n) ↔
      σ ∈ (smoothSingularSubcomplex I ↥(U ⊔ V)).obj n ∧ σ ∈ (SSet.Subcomplex.range _).obj n
    rw [TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of ↥(U ⊔ V)),
      TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of ↥(U ⊔ V)),
      TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of ↥(U ⊔ V)),
      Opens.coe_inf, Set.preimage_inter]
    exact ⟨fun ⟨⟨hs, hu⟩, _, hv⟩ ↦ ⟨hs, Set.subset_inter hu hv⟩,
      fun ⟨hs, huv⟩ ↦ ⟨⟨hs, huv.trans Set.inter_subset_left⟩, hs, huv.trans Set.inter_subset_right⟩⟩

private lemma mono_ι_comp_toSSet_inclusion {W Z : Opens M} (hWZ : W ≤ Z) :
    Mono ((smoothSingularSubcomplex I W).ι ≫
      TopCat.toSSet.map (TopCat.ofHom
        ⟨Opens.inclusion hWZ, continuous_inclusion (hWZ : (W : Set M) ⊆ Z)⟩)) :=
  have : Mono (TopCat.ofHom ⟨Opens.inclusion hWZ, continuous_inclusion (hWZ : (W : Set M) ⊆ Z)⟩) :=
    (TopCat.mono_iff_injective _).2 (Set.inclusion_injective (hWZ : (W : Set M) ⊆ Z))
  have : Mono (TopCat.toSSet.map (TopCat.ofHom
      ⟨Opens.inclusion hWZ, continuous_inclusion (hWZ : (W : Set M) ⊆ Z)⟩)) := Functor.map_mono _ _
  mono_comp _ _

variable (I) in
/-- **Pushout square of smooth singular subcomplexes in `U ⊔ V`.** For any two open subsets `U` and
`V` of `M`, the smooth singular subcomplexes of `U ⊓ V`, `U`, and `V` form a pushout square with
the smooth singular simplices of `U ⊔ V` lying in `U` or in `V`. -/
theorem isPushout_smoothSingularSubcomplex_sup (U V : Opens M) :
    IsPushout
      (smoothSingularSubcomplexMap (I := I) (J := I)
        (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _))
      (smoothSingularSubcomplexMap (I := I) (J := I)
        (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _))
      (toSmoothSmallSingularSubcomplex
        ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)]
        (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _)
        fun x ↦ Eq.mpr (congrArg (Opens.inclusion (le_sup_left : U ≤ U ⊔ V) x ∈ ·)
          (Matrix.cons_val_zero (Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V))
            ![Subtype.val ⁻¹' (V : Set M)])) (SetLike.mem_coe.2 x.2))
      (toSmoothSmallSingularSubcomplex
        ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)]
        (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _)
        fun x ↦ Eq.mpr (congrArg (Opens.inclusion (le_sup_right : V ≤ U ⊔ V) x ∈ ·)
          ((Matrix.cons_val_one (Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V))
            ![Subtype.val ⁻¹' (V : Set M)]).trans
            (Matrix.cons_val_zero (Subtype.val ⁻¹' (V : Set M) : Set ↥(U ⊔ V)) ![])))
          (SetLike.mem_coe.2 x.2)) := by
  have hcI := continuous_inclusion (inf_le_sup : ((U ⊓ V : Opens M) : Set M) ⊆ U ⊔ V)
  have hcU := continuous_inclusion (le_sup_left : (U : Set M) ⊆ U ⊔ V)
  have hcV := continuous_inclusion (le_sup_right : (V : Set M) ⊆ U ⊔ V)
  let fI := (smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫
    TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion (inf_le_sup : U ⊓ V ≤ U ⊔ V), hcI⟩)
  let fU := (smoothSingularSubcomplex I U).ι ≫
    TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion (le_sup_left : U ≤ U ⊔ V), hcU⟩)
  let fV := (smoothSingularSubcomplex I V).ι ≫
    TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion (le_sup_right : V ≤ U ⊔ V), hcV⟩)
  let D := smoothSingularSubcomplex I ↥(U ⊔ V) ⊓
    (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex
      ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)]
  have : Mono fI := mono_ι_comp_toSSet_inclusion (inf_le_sup : U ⊓ V ≤ U ⊔ V)
  have : Mono fU := mono_ι_comp_toSSet_inclusion (le_sup_left : U ≤ U ⊔ V)
  have : Mono fV := mono_ι_comp_toSSet_inclusion (le_sup_right : V ≤ U ⊔ V)
  refine (bicartSq_range_smoothSingularSubcomplex_inclusion (I := I) U V).isPushout.of_iso'
    (asIso (SSet.Subcomplex.toRange fI)) (asIso (SSet.Subcomplex.toRange fU))
    (asIso (SSet.Subcomplex.toRange fV)) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (SSet.Subcomplex.range fU).ι]
    -- Composing `toRange` with the subcomplex inclusion recovers `fI`.
    change fI = smoothSingularSubcomplexMap _ _ ≫ fU
    rw [smoothSingularSubcomplexMap_ι_assoc, ← CategoryTheory.Functor.map_comp]
    -- `Opens.inclusion (le_sup_left) ∘ Opens.inclusion (inf_le_left)` equals `Opens.inclusion`.
    rfl
  · rw [← cancel_mono (SSet.Subcomplex.range fV).ι]
    -- Composing `toRange` with the subcomplex inclusion recovers `fI`.
    change fI = smoothSingularSubcomplexMap _ _ ≫ fV
    rw [smoothSingularSubcomplexMap_ι_assoc, ← CategoryTheory.Functor.map_comp]
    -- `Opens.inclusion (le_sup_right) ∘ Opens.inclusion (inf_le_right)` equals `Opens.inclusion`.
    rfl
  · rw [← cancel_mono D.ι]
    simp only [D, fU, asIso_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι, toSmoothSmallSingularSubcomplex_ι]
  · rw [← cancel_mono D.ι]
    simp only [D, fV, asIso_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι, toSmoothSmallSingularSubcomplex_ι]

end Pushout

/-! ### The Mayer–Vietoris sequence in smooth singular homology -/

section Homology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)

/-- The first map `Hₙ(U ⊓ V) ⟶ Hₙ(U) ⊞ Hₙ(V)` of the Mayer–Vietoris sequence in smooth singular
homology, with components `(i_U)_*` and `-(i_V)_*`. -/
abbrev smoothMayerVietorisToBiprod (U V : Opens M) (n : ℕ) :
    (smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).homology R n ⟶
      (smoothSingularSubcomplex I U : SSet).homology R n ⊞
        (smoothSingularSubcomplex I V : SSet).homology R n :=
  SSet.mayerVietorisToBiprod R
    (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
      (contMDiff_inclusion _))
    (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
      (contMDiff_inclusion _)) n

/-- The second map `Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(M)` of the Mayer–Vietoris sequence in smooth singular
homology, the sum `(j_U)_* + (j_V)_*`. -/
abbrev smoothMayerVietorisFromBiprod (U V : Opens M) (n : ℕ) :
    (smoothSingularSubcomplex I U : SSet).homology R n ⊞
        (smoothSingularSubcomplex I V : SSet).homology R n ⟶
      (smoothSingularSubcomplex I M : SSet).homology R n :=
  SSet.mayerVietorisFromBiprod R
    (smoothSingularSubcomplexMap (Subtype.val : U → M) contMDiff_subtype_val)
    (smoothSingularSubcomplexMap (Subtype.val : V → M) contMDiff_subtype_val) n

@[reassoc (attr := simp)]
lemma smoothMayerVietorisToBiprod_fromBiprod (U V : Opens M) (n : ℕ) :
    smoothMayerVietorisToBiprod I R U V n ≫ smoothMayerVietorisFromBiprod I R U V n = 0 :=
  SSet.mayerVietorisToBiprod_fromBiprod R
    ⟨by
      rw [← smoothSingularSubcomplexMap_comp, ← smoothSingularSubcomplexMap_comp]
      -- Both compositions coerce `x : U ⊓ V` to `M`.
      rfl⟩ n

section Covered

variable {I} {U V : Opens M} (hUV : U ⊔ V = ⊤)

private lemma opens_union_eq_univ (hUV : U ⊔ V = ⊤) :
    (U : Set M) ∪ (V : Set M) = Set.univ := by
  have h := congrArg (SetLike.coe (A := Opens M) (B := M)) hUV
  rwa [Opens.coe_sup, Opens.coe_top] at h

private lemma iUnion_vecCons_opens_eq_univ (hUV : U ⊔ V = ⊤) :
    ⋃ i, ![(U : Set M), (V : Set M)] i = Set.univ :=
  ((U : Set M).iUnion_vecCons_pair (V : Set M)).trans (opens_union_eq_univ hUV)

private abbrev smoothSmallHomologyIso (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (((smoothSingularSubcomplex I M ⊓
      (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] :
        (TopCat.toSSet.obj (TopCat.of M)).Subcomplex) : SSet).chainComplex R).homology n ≅
      (smoothSingularSubcomplex I M : SSet).homology R n :=
  subcomplexSmallHomologyIso R (smoothSingularSubcomplex I M) ![(U : Set M), (V : Set M)]
    (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV) n

private lemma mayerVietorisFromBiprod_comp_smoothSmallHomologyIso (hUV : U ⊔ V = ⊤) (n : ℕ) :
    SSet.mayerVietorisFromBiprod R
        (toSmoothSmallSingularSubcomplex ![(U : Set M), (V : Set M)] (Subtype.val : U → M)
          (contMDiff_subtype_val (I := I))
          fun x ↦ Eq.mpr (congrArg ((x : M) ∈ ·)
            (Matrix.cons_val_zero (U : Set M) ![(V : Set M)])) (SetLike.mem_coe.2 x.2))
        (toSmoothSmallSingularSubcomplex ![(U : Set M), (V : Set M)] (Subtype.val : V → M)
          (contMDiff_subtype_val (I := I))
          fun x ↦ Eq.mpr (congrArg ((x : M) ∈ ·)
            ((Matrix.cons_val_one (U : Set M) ![(V : Set M)]).trans
              (Matrix.cons_val_zero (V : Set M) ![]))) (SetLike.mem_coe.2 x.2)) n ≫
      (smoothSmallHomologyIso (I := I) R hUV n).hom =
    smoothMayerVietorisFromBiprod I R U V n := by
  rw [subcomplexSmallHomologyIso_hom]
  apply biprod.hom_ext' <;>
    simp [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp,
      SSet.homologyMap]

/-- **The Mayer–Vietoris connecting morphism in smooth singular homology.** For open subsets `U`
and `V` of `M` with `U ⊔ V = ⊤`, the connecting morphism `Hₙ(M) ⟶ Hₘ(U ⊓ V)` (`m + 1 = n`) of
smooth singular homology with coefficients in `R`. -/
def smoothMayerVietorisδ (hUV : U ⊔ V = ⊤) (n m : ℕ) (h : m + 1 = n := by lia) :
    (smoothSingularSubcomplex I M : SSet).homology R n ⟶
      (smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).homology R m :=
  (smoothSmallHomologyIso (I := I) R hUV n).inv ≫
    SSet.mayerVietorisδ R (isPushout_smoothSingularSubcomplex_inter I U V) n m h

/-- On the homology of smooth singular simplices lying in `U` or in `V`, the smooth Mayer–Vietoris
connecting morphism restricts to that of the pushout square of smooth singular subcomplexes. -/
@[reassoc (attr := simp)]
lemma homologyMap_comp_smoothMayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) :
    SSet.homologyMap (SSet.Subcomplex.homOfLE
        (inf_le_left : smoothSingularSubcomplex I M ⊓
          (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤
            smoothSingularSubcomplex I M)) R n ≫
      smoothMayerVietorisδ (I := I) R hUV n m h =
    SSet.mayerVietorisδ R (isPushout_smoothSingularSubcomplex_inter I U V) n m h := by
  rw [smoothMayerVietorisδ, SSet.homologyMap,
    ← subcomplexSmallHomologyIso_hom R (smoothSingularSubcomplex I M) ![(U : Set M), (V : Set M)]
      (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV) n,
    Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma smoothMayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    smoothMayerVietorisδ (I := I) R hUV n m h ≫ smoothMayerVietorisToBiprod I R U V m = 0 := by
  simp [smoothMayerVietorisδ]

@[reassoc (attr := simp)]
lemma smoothMayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    smoothMayerVietorisFromBiprod I R U V n ≫ smoothMayerVietorisδ (I := I) R hUV n m h = 0 := by
  rw [← mayerVietorisFromBiprod_comp_smoothSmallHomologyIso (I := I) R hUV n, Category.assoc,
    smoothMayerVietorisδ, Iso.hom_inv_id_assoc,
    SSet.mayerVietorisFromBiprod_δ R _ n m h]

/-- **Exactness of the smooth singular Mayer–Vietoris sequence at `Hₘ(U ⊓ V)`.** -/
lemma smoothMayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (smoothMayerVietorisδ_toBiprod (I := I) R hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₁ R (isPushout_smoothSingularSubcomplex_inter I U V) n m h)
  refine ShortComplex.isoMk (smoothSmallHomologyIso (I := I) R hUV n) (Iso.refl _) (Iso.refl _)
    ?_ (by simp)
  dsimp only
  rw [Iso.refl_hom, Category.comp_id, subcomplexSmallHomologyIso_hom, ← SSet.homologyMap,
    homologyMap_comp_smoothMayerVietorisδ (I := I) R hUV n m h]

include hUV in
/-- **Exactness of the smooth singular Mayer–Vietoris sequence at `Hₙ(U) ⊞ Hₙ(V)`.** -/
lemma smoothMayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (smoothMayerVietorisToBiprod_fromBiprod I R U V n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₂ R (isPushout_smoothSingularSubcomplex_inter I U V) n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (smoothSmallHomologyIso (I := I) R hUV n)
    (by simp) ?_
  dsimp only
  rw [Iso.refl_hom, Category.id_comp, mayerVietorisFromBiprod_comp_smoothSmallHomologyIso]

/-- **Exactness of the smooth singular Mayer–Vietoris sequence at `Hₙ(M)`.** -/
lemma smoothMayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (smoothMayerVietorisFromBiprod_δ (I := I) R hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₃ R (isPushout_smoothSingularSubcomplex_inter I U V) n m h)
  refine ShortComplex.isoMk (Iso.refl _) (smoothSmallHomologyIso (I := I) R hUV n) (Iso.refl _)
    ?_ ?_
  · dsimp only
    rw [Iso.refl_hom, Category.id_comp, mayerVietorisFromBiprod_comp_smoothSmallHomologyIso]
  · dsimp only
    rw [Iso.refl_hom, Category.comp_id, subcomplexSmallHomologyIso_hom, ← SSet.homologyMap,
      homologyMap_comp_smoothMayerVietorisδ (I := I) R hUV n m h]

include hUV in
/-- At degree zero, `H₀(U) ⊞ H₀(V) ⟶ H₀(M)` in smooth singular homology is an epimorphism. -/
lemma epi_smoothMayerVietorisFromBiprod_zero :
    Epi (smoothMayerVietorisFromBiprod I R U V 0) := by
  rw [← mayerVietorisFromBiprod_comp_smoothSmallHomologyIso (I := I) R hUV 0]
  have := SSet.epi_mayerVietorisFromBiprod_zero R
    (isPushout_smoothSingularSubcomplex_inter I U V)
  exact epi_comp _ _

include hUV in
/-- When the smooth singular homology of `M` vanishes in degrees `n + 1` and `n`, the map
`Hₙ(U ⊓ V) ⟶ Hₙ(U) ⊞ Hₙ(V)` is an isomorphism. -/
lemma isIso_smoothMayerVietorisToBiprod_of_isZero (n : ℕ)
    (h₁ : IsZero ((smoothSingularSubcomplex I M : SSet).homology R (n + 1)))
    (h₀ : IsZero ((smoothSingularSubcomplex I M : SSet).homology R n)) :
    IsIso (smoothMayerVietorisToBiprod I R U V n) := by
  have := (smoothMayerVietoris_exact₁ (I := I) R hUV (n + 1) n).mono_g (h₁.eq_of_src _ _)
  have := (smoothMayerVietoris_exact₂ (I := I) R hUV n).epi_f (h₀.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

private lemma isZero_chainComplex_smoothSingularSubcomplex_of_disjoint (hdisj : Disjoint U V) :
    IsZero ((smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).chainComplex R) := by
  have : (smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).HasDimensionLT 0 := by
    refine (SSet.notNonempty_iff_hasDimensionLT_zero _).1 fun ⟨σ⟩ ↦ ?_
    let p := (TopCat.of ↥(U ⊓ V)).toSSetObjEquiv _ σ.1 (Convexity.StdSimplex.single 0)
    exact hdisj.le_bot p.2
  exact SSet.isZero_chainComplex _ R

include hUV in
/-- For a cover of `M` by two disjoint open subsets `U` and `V`, the smooth singular Mayer–Vietoris
map `Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(M)` is an isomorphism in every degree `n`. -/
lemma isIso_smoothMayerVietorisFromBiprod_of_disjoint (hdisj : Disjoint U V) (n : ℕ) :
    IsIso (smoothMayerVietorisFromBiprod I R U V n) := by
  have hZ : ∀ k, IsZero ((smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).homology R k) := fun k ↦
    (HomologicalComplex.homologyFunctor C _ k).map_isZero
      (isZero_chainComplex_smoothSingularSubcomplex_of_disjoint (I := I) R hdisj)
  have : Mono (smoothMayerVietorisFromBiprod I R U V n) :=
    (smoothMayerVietoris_exact₂ (I := I) R hUV n).mono_g ((hZ n).eq_of_src _ _)
  cases n with
  | zero =>
    have := epi_smoothMayerVietorisFromBiprod_zero (I := I) R hUV
    exact isIso_of_mono_of_epi _
  | succ m =>
    have := (smoothMayerVietoris_exact₃ (I := I) R hUV (m + 1) m).epi_f ((hZ m).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _

/-- **Naturality of the smooth singular Mayer–Vietoris connecting morphism** under smooth maps
carrying `U` into `U'` and `V` into `V'`. -/
@[reassoc]
lemma smoothMayerVietorisδ_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
    {U' V' : Opens N} (hUV' : U' ⊔ V' = ⊤) {φ : M → N} (hφ : ContMDiff I J ∞ φ)
    (hfU : Set.MapsTo φ U U') (hfV : Set.MapsTo φ V V') (n m : ℕ) (h : m + 1 = n := by lia) :
    smoothMayerVietorisδ (I := I) R hUV n m h ≫
        SSet.homologyMap (smoothSingularSubcomplexMap
          (fun x : ↥(U ⊓ V) ↦ (⟨φ x.1, hfU x.2.1, hfV x.2.2⟩ : ↥(U' ⊓ V')))
          ((ContMDiff.subtypeVal_comp_iff (U' ⊓ V') _).1
            (hφ.comp (contMDiff_subtype_val (I := I) (U := U ⊓ V))))) R m =
      SSet.homologyMap (smoothSingularSubcomplexMap φ hφ) R n ≫
        smoothMayerVietorisδ (I := J) R hUV' n m h := by
  have hf : ∀ i, Set.MapsTo φ (![(U : Set M), (V : Set M)] i)
      (![(U' : Set N), (V' : Set N)] (id i)) := by
    simp [Fin.forall_fin_two, hfU, hfV]
  have hsmall := subcomplexSmallHomologyIso_naturality R
    (smoothSingularSubcomplex I M) ![(U : Set M), (V : Set M)]
    (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV)
    (smoothSingularSubcomplex J N) ![(U' : Set N), (V' : Set N)]
    (U'.isOpen.vecCons V'.isOpen) (iUnion_vecCons_opens_eq_univ hUV')
    (smoothSmallSingularSubcomplexMap _ _ φ hφ id hf)
    (smoothSingularSubcomplexMap φ hφ)
    (smoothSmallSingularSubcomplexMap_homOfLE_left _ _ φ hφ id hf) n
  have hnat := SSet.mayerVietorisδ_naturality R
    (smoothSingularSubcomplexMap
      (fun x : ↥(U ⊓ V) ↦ (⟨φ x.1, hfU x.2.1, hfV x.2.2⟩ : ↥(U' ⊓ V')))
      ((ContMDiff.subtypeVal_comp_iff (U' ⊓ V') _).1
        (hφ.comp (contMDiff_subtype_val (I := I) (U := U ⊓ V)))))
    (smoothSingularSubcomplexMap (fun x : U ↦ (⟨φ x.1, hfU x.2⟩ : U'))
      ((ContMDiff.subtypeVal_comp_iff U' _).1
        (hφ.comp (contMDiff_subtype_val (I := I) (U := U)))))
    (smoothSingularSubcomplexMap (fun x : V ↦ (⟨φ x.1, hfV x.2⟩ : V'))
      ((ContMDiff.subtypeVal_comp_iff V' _).1
        (hφ.comp (contMDiff_subtype_val (I := I) (U := V)))))
    (smoothSmallSingularSubcomplexMap _ _ φ hφ id hf)
    (isPushout_smoothSingularSubcomplex_inter I U V)
    (isPushout_smoothSingularSubcomplex_inter J U' V')
    -- Restriction of `φ` to `U ⊓ V` followed by inclusion equals inclusion followed by `φ`.
    (by rw [← smoothSingularSubcomplexMap_comp, ← smoothSingularSubcomplexMap_comp]; rfl)
    (by rw [← smoothSingularSubcomplexMap_comp, ← smoothSingularSubcomplexMap_comp]; rfl)
    (toSmoothSmallSingularSubcomplex_comp_smoothSmallSingularSubcomplexMap _ _ _ _ _ _ _ id hf
      _ _ _ _ _ rfl)
    (toSmoothSmallSingularSubcomplex_comp_smoothSmallSingularSubcomplexMap _ _ _ _ _ _ _ id hf
      _ _ _ _ _ rfl) n m h
  rw [smoothMayerVietorisδ, smoothMayerVietorisδ, Category.assoc, hnat, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, SSet.homologyMap, ← Category.assoc, hsmall, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **Compatibility of smooth and continuous singular Mayer–Vietoris connecting morphisms.** The
inclusion of smooth singular chains into continuous singular chains intertwines
`smoothMayerVietorisδ` and `TopCat.mayerVietorisδ`. -/
@[reassoc]
lemma smoothMayerVietorisδ_comp_homologyMap_ι (n m : ℕ) (h : m + 1 = n := by lia) :
    smoothMayerVietorisδ (I := I) R hUV n m h ≫
        SSet.homologyMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R m =
      SSet.homologyMap (smoothSingularSubcomplex I M).ι R n ≫
        TopCat.mayerVietorisδ (X := TopCat.of M) R U.isOpen V.isOpen
          (by simp [← Opens.coe_sup, hUV]) n m h := by
  apply (cancel_epi (smoothSmallHomologyIso (I := I) R hUV n).hom).1
  have hnat := SSet.mayerVietorisδ_naturality R
    (smoothSingularSubcomplex I ↥(U ⊓ V)).ι
    (smoothSingularSubcomplex I U).ι
    (smoothSingularSubcomplex I V).ι
    (SSet.Subcomplex.homOfLE (inf_le_right : smoothSingularSubcomplex I M ⊓
      (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤ _))
    (isPushout_smoothSingularSubcomplex_inter I U V)
    (TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of M)
      (U : Set M) (V : Set M))
    (smoothSingularSubcomplexMap_ι (I := I) (J := I)
      (contMDiff_inclusion (inf_le_left : U ⊓ V ≤ U)))
    (smoothSingularSubcomplexMap_ι (I := I) (J := I)
      (contMDiff_inclusion (inf_le_right : U ⊓ V ≤ V)))
    (toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right (I := I) _ _ _)
    (toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right (I := I) _ _ _) n m h
  have hcomm : SSet.Subcomplex.homOfLE
        (inf_le_left : smoothSingularSubcomplex I M ⊓
          (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤ _) ≫
      (smoothSingularSubcomplex I M).ι =
    SSet.Subcomplex.homOfLE inf_le_right ≫
      ((TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)]).ι := by
    rw [SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι]
  rw [subcomplexSmallHomologyIso_hom, ← SSet.homologyMap,
    homologyMap_comp_smoothMayerVietorisδ_assoc (I := I) R hUV n m h, hnat,
    ← SSet.homologyMap_comp_assoc, hcomm, SSet.homologyMap_comp_assoc,
    TopCat.homologyMap_ι_comp_mayerVietorisδ (X := TopCat.of M) R U.isOpen V.isOpen _ n m h]

end Covered

end Homology

/-! ### The Mayer–Vietoris sequence in smooth singular cohomology -/

section Cohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (Q : C)

/-- The first map `Hⁿ(M) ⟶ Hⁿ(U) ⊞ Hⁿ(V)` of the Mayer–Vietoris sequence in smooth singular
cohomology, with components `(j_U)^*` and `(j_V)^*`. -/
abbrev smoothCohomologyMayerVietorisToBiprod (U V : Opens M) (n : ℕ) :
    (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k Q).homology n ⟶
      (((smoothSingularSubcomplex I U : SSet).chainComplex R).linearYonedaObj k Q).homology n ⊞
        (((smoothSingularSubcomplex I V : SSet).chainComplex R).linearYonedaObj k Q).homology n :=
  SSet.mayerVietorisCochainToBiprod R k Q
    (smoothSingularSubcomplexMap (Subtype.val : U → M) contMDiff_subtype_val)
    (smoothSingularSubcomplexMap (Subtype.val : V → M) contMDiff_subtype_val) n

/-- The second map `Hⁿ(U) ⊞ Hⁿ(V) ⟶ Hⁿ(U ⊓ V)` of the Mayer–Vietoris sequence in smooth singular
cohomology, the difference `(i_U)^* - (i_V)^*`. -/
abbrev smoothCohomologyMayerVietorisFromBiprod (U V : Opens M) (n : ℕ) :
    (((smoothSingularSubcomplex I U : SSet).chainComplex R).linearYonedaObj k Q).homology n ⊞
        (((smoothSingularSubcomplex I V : SSet).chainComplex R).linearYonedaObj k Q).homology n ⟶
      (((smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).chainComplex R).linearYonedaObj
        k Q).homology n :=
  SSet.mayerVietorisCochainFromBiprod R k Q
    (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
      (contMDiff_inclusion _))
    (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
      (contMDiff_inclusion _)) n

@[reassoc (attr := simp)]
lemma smoothCohomologyMayerVietorisToBiprod_fromBiprod (U V : Opens M) (n : ℕ) :
    smoothCohomologyMayerVietorisToBiprod I R k Q U V n ≫
      smoothCohomologyMayerVietorisFromBiprod I R k Q U V n = 0 :=
  SSet.mayerVietorisCochainToBiprod_fromBiprod R k Q
    ⟨by
      rw [← smoothSingularSubcomplexMap_comp, ← smoothSingularSubcomplexMap_comp]
      -- Both compositions coerce `x : U ⊓ V` to `M`.
      rfl⟩ n

/-- **The smooth singular cohomology Mayer–Vietoris connecting morphism on `U ⊔ V`.** For any two
open subsets `U` and `V` of `M`, the connecting morphism `Hⁿ(U ⊓ V) ⟶ Hᵐ(U ⊔ V)` (`n + 1 = m`) in
smooth singular cohomology. -/
def smoothSupCohomologyMayerVietorisδ (U V : Opens M) (n m : ℕ) (h : n + 1 = m := by lia) :
    (((smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).chainComplex R).linearYonedaObj
      k Q).homology n ⟶
    (((smoothSingularSubcomplex I ↥(U ⊔ V) : SSet).chainComplex R).linearYonedaObj
      k Q).homology m :=
  SSet.mayerVietorisCochainδ R k Q (isPushout_smoothSingularSubcomplex_sup I U V) n m h ≫
    (subcomplexSmallCohomologyIso R k Q (smoothSingularSubcomplex I ↥(U ⊔ V))
      ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)]
      ((U.isOpen.preimage continuous_subtype_val).vecCons
        (V.isOpen.preimage continuous_subtype_val))
      (((Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)).iUnion_vecCons_pair _).trans
        (Set.eq_univ_of_forall fun x ↦ x.2)) m).inv

/-- Followed by restriction to the smooth singular simplices of `U ⊔ V` lying in `U` or in `V`,
`smoothSupCohomologyMayerVietorisδ` is the cochain Mayer–Vietoris connecting morphism of the
pushout square on `U ⊔ V`. -/
@[reassoc (attr := simp)]
lemma smoothSupCohomologyMayerVietorisδ_comp_homologyMap (U V : Opens M) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    smoothSupCohomologyMayerVietorisδ I R k Q U V n m h ≫
        HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (SSet.Subcomplex.homOfLE
            (inf_le_left : smoothSingularSubcomplex I ↥(U ⊔ V) ⊓
              (TopCat.of ↥(U ⊔ V)).smallSingularSubcomplex
                ![(Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)), Subtype.val ⁻¹' (V : Set M)] ≤
              smoothSingularSubcomplex I ↥(U ⊔ V)))) m =
      SSet.mayerVietorisCochainδ R k Q (isPushout_smoothSingularSubcomplex_sup I U V) n m h := by
  rw [smoothSupCohomologyMayerVietorisδ, Category.assoc,
    ← subcomplexSmallCohomologyIso_hom R k Q (smoothSingularSubcomplex I ↥(U ⊔ V)) _
      ((U.isOpen.preimage continuous_subtype_val).vecCons
        (V.isOpen.preimage continuous_subtype_val))
      (((Subtype.val ⁻¹' (U : Set M) : Set ↥(U ⊔ V)).iUnion_vecCons_pair _).trans
        (Set.eq_univ_of_forall fun x ↦ x.2)) m,
    Iso.inv_hom_id, Category.comp_id]

section Covered

variable {I} {U V : Opens M} (hUV : U ⊔ V = ⊤)

private abbrev smoothSmallCohomologyIso (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k Q).homology n ≅
      ((((smoothSingularSubcomplex I M ⊓
        (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] :
          (TopCat.toSSet.obj (TopCat.of M)).Subcomplex) : SSet).chainComplex R).linearYonedaObj
        k Q).homology n :=
  subcomplexSmallCohomologyIso R k Q (smoothSingularSubcomplex I M) ![(U : Set M), (V : Set M)]
    (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV) n

private lemma smoothSmallCohomologyIso_hom_comp_mayerVietorisCochainToBiprod
    (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (smoothSmallCohomologyIso (I := I) R k Q hUV n).hom ≫
        SSet.mayerVietorisCochainToBiprod R k Q
          (toSmoothSmallSingularSubcomplex ![(U : Set M), (V : Set M)] (Subtype.val : U → M)
            (contMDiff_subtype_val (I := I))
            fun x ↦ Eq.mpr (congrArg ((x : M) ∈ ·)
              (Matrix.cons_val_zero (U : Set M) ![(V : Set M)])) (SetLike.mem_coe.2 x.2))
          (toSmoothSmallSingularSubcomplex ![(U : Set M), (V : Set M)] (Subtype.val : V → M)
            (contMDiff_subtype_val (I := I))
            fun x ↦ Eq.mpr (congrArg ((x : M) ∈ ·)
              ((Matrix.cons_val_one (U : Set M) ![(V : Set M)]).trans
                (Matrix.cons_val_zero (V : Set M) ![]))) (SetLike.mem_coe.2 x.2)) n =
      smoothCohomologyMayerVietorisToBiprod I R k Q U V n := by
  rw [subcomplexSmallCohomologyIso_hom]
  apply biprod.hom_ext <;>
    simp [← HomologicalComplex.homologyMap_comp, ← SSet.cochainComplexMap_comp]

/-- **The Mayer–Vietoris connecting morphism in smooth singular cohomology.** For open subsets `U`
and `V` of `M` with `U ⊔ V = ⊤`, the connecting morphism `Hⁿ(U ⊓ V) ⟶ Hᵐ(M)` (`n + 1 = m`) in
smooth singular cohomology. -/
def smoothCohomologyMayerVietorisδ (hUV : U ⊔ V = ⊤) (n m : ℕ) (h : n + 1 = m := by lia) :
    (((smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).chainComplex R).linearYonedaObj
      k Q).homology n ⟶
    (((smoothSingularSubcomplex I M : SSet).chainComplex R).linearYonedaObj k Q).homology m :=
  SSet.mayerVietorisCochainδ R k Q (isPushout_smoothSingularSubcomplex_inter I U V) n m h ≫
    (smoothSmallCohomologyIso (I := I) R k Q hUV m).inv

/-- Followed by restriction to the smooth singular simplices lying in `U` or in `V`, the smooth
cohomology Mayer–Vietoris connecting morphism is that of the pushout square of smooth singular
subcomplexes. -/
@[reassoc (attr := simp)]
lemma smoothCohomologyMayerVietorisδ_comp_homologyMap (n m : ℕ) (h : n + 1 = m := by lia) :
    smoothCohomologyMayerVietorisδ (I := I) R k Q hUV n m h ≫
        HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (SSet.Subcomplex.homOfLE
            (inf_le_left : smoothSingularSubcomplex I M ⊓
              (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤
                smoothSingularSubcomplex I M))) m =
      SSet.mayerVietorisCochainδ R k Q (isPushout_smoothSingularSubcomplex_inter I U V) n m h := by
  rw [smoothCohomologyMayerVietorisδ, Category.assoc,
    ← subcomplexSmallCohomologyIso_hom R k Q (smoothSingularSubcomplex I M)
      ![(U : Set M), (V : Set M)] (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV) m,
    Iso.inv_hom_id, Category.comp_id]

@[reassoc (attr := simp)]
lemma smoothCohomologyMayerVietorisδ_toBiprod (n m : ℕ) (h : n + 1 = m := by lia) :
    smoothCohomologyMayerVietorisδ (I := I) R k Q hUV n m h ≫
      smoothCohomologyMayerVietorisToBiprod I R k Q U V m = 0 := by
  rw [← smoothSmallCohomologyIso_hom_comp_mayerVietorisCochainToBiprod (I := I) R k Q hUV m,
    smoothCohomologyMayerVietorisδ, Category.assoc, Iso.inv_hom_id_assoc,
    SSet.mayerVietorisCochainδ_toBiprod R k Q _ n m h]

@[reassoc (attr := simp)]
lemma smoothCohomologyMayerVietorisFromBiprod_δ (n m : ℕ) (h : n + 1 = m := by lia) :
    smoothCohomologyMayerVietorisFromBiprod I R k Q U V n ≫
      smoothCohomologyMayerVietorisδ (I := I) R k Q hUV n m h = 0 := by
  rw [smoothCohomologyMayerVietorisδ,
    SSet.mayerVietorisCochainFromBiprod_δ_assoc R k Q _ n m h, zero_comp]

/-- **Exactness of the smooth singular cohomology Mayer–Vietoris sequence at `Hᵐ(M)`.** -/
lemma smoothCohomologyMayerVietoris_exact₁ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (smoothCohomologyMayerVietorisδ_toBiprod (I := I) R k Q hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietorisCochain_exact₁ R k Q (isPushout_smoothSingularSubcomplex_inter I U V) n m h)
  refine ShortComplex.isoMk (Iso.refl _) (smoothSmallCohomologyIso (I := I) R k Q hUV m).symm
    (Iso.refl _) (by simp [smoothCohomologyMayerVietorisδ]) ?_
  dsimp only
  rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id,
    ← smoothSmallCohomologyIso_hom_comp_mayerVietorisCochainToBiprod (I := I) R k Q hUV m,
    Iso.inv_hom_id_assoc]

include hUV in
/-- **Exactness of the smooth singular cohomology Mayer–Vietoris sequence at `Hⁿ(U) ⊞ Hⁿ(V)`.** -/
lemma smoothCohomologyMayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _
      (smoothCohomologyMayerVietorisToBiprod_fromBiprod I R k Q U V n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietorisCochain_exact₂ R k Q (isPushout_smoothSingularSubcomplex_inter I U V) n)
  refine ShortComplex.isoMk (smoothSmallCohomologyIso (I := I) R k Q hUV n).symm (Iso.refl _)
    (Iso.refl _) ?_ (by simp)
  dsimp only
  rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id,
    ← smoothSmallCohomologyIso_hom_comp_mayerVietorisCochainToBiprod (I := I) R k Q hUV n,
    Iso.inv_hom_id_assoc]

/-- **Exactness of the smooth singular cohomology Mayer–Vietoris sequence at `Hⁿ(U ⊓ V)`.** -/
lemma smoothCohomologyMayerVietoris_exact₃ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (smoothCohomologyMayerVietorisFromBiprod_δ (I := I) R k Q hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietorisCochain_exact₃ R k Q (isPushout_smoothSingularSubcomplex_inter I U V) n m h)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (smoothSmallCohomologyIso (I := I) R k Q hUV m).symm (by simp)
    (by simp [smoothCohomologyMayerVietorisδ])

include hUV in
/-- At degree zero, `H⁰(M) ⟶ H⁰(U) ⊞ H⁰(V)` in smooth singular cohomology is a monomorphism. -/
lemma mono_smoothCohomologyMayerVietorisToBiprod_zero :
    Mono (smoothCohomologyMayerVietorisToBiprod I R k Q U V 0) := by
  have := SSet.mono_mayerVietorisCochainToBiprod_zero R k Q
    (isPushout_smoothSingularSubcomplex_inter I U V)
  rw [← smoothSmallCohomologyIso_hom_comp_mayerVietorisCochainToBiprod (I := I) R k Q hUV 0]
  infer_instance

include hUV in
/-- For a cover of `M` by two disjoint open subsets `U` and `V`, the smooth singular cohomology
Mayer–Vietoris map `Hⁿ(M) ⟶ Hⁿ(U) ⊞ Hⁿ(V)` is an isomorphism in every degree `n`. -/
lemma isIso_smoothCohomologyMayerVietorisToBiprod_of_disjoint (hdisj : Disjoint U V) (n : ℕ) :
    IsIso (smoothCohomologyMayerVietorisToBiprod I R k Q U V n) := by
  have hZ : ∀ j, IsZero ((((smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).chainComplex
      R).linearYonedaObj k Q).homology j) := fun j ↦
    (HomologicalComplex.homologyFunctor _ _ j).map_isZero
      ((ChainComplex.linearYonedaFunctor k Q).map_isZero
        (isZero_chainComplex_smoothSingularSubcomplex_of_disjoint (I := I) R hdisj).op)
  have : Epi (smoothCohomologyMayerVietorisToBiprod I R k Q U V n) :=
    (smoothCohomologyMayerVietoris_exact₂ (I := I) R k Q hUV n).epi_f ((hZ n).eq_of_tgt _ _)
  cases n with
  | zero =>
    have := mono_smoothCohomologyMayerVietorisToBiprod_zero (I := I) R k Q hUV
    exact isIso_of_mono_of_epi _
  | succ m =>
    have := (smoothCohomologyMayerVietoris_exact₁ (I := I) R k Q hUV m (m + 1)).mono_g
      ((hZ m).eq_of_src _ _)
    exact isIso_of_mono_of_epi _

/-- **Naturality of the smooth singular cohomology Mayer–Vietoris connecting morphism** under
smooth maps carrying `U` into `U'` and `V` into `V'`. -/
@[reassoc]
lemma smoothCohomologyMayerVietorisδ_naturality
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
    {U' V' : Opens N} (hUV' : U' ⊔ V' = ⊤) {φ : M → N} (hφ : ContMDiff I J ∞ φ)
    (hfU : Set.MapsTo φ U U') (hfV : Set.MapsTo φ V V') (n m : ℕ) (h : n + 1 = m := by lia) :
    smoothCohomologyMayerVietorisδ (I := J) R k Q hUV' n m h ≫
        HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (smoothSingularSubcomplexMap φ hφ)) m =
      HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (smoothSingularSubcomplexMap
            (fun x : ↥(U ⊓ V) ↦ (⟨φ x.1, hfU x.2.1, hfV x.2.2⟩ : ↥(U' ⊓ V')))
            ((ContMDiff.subtypeVal_comp_iff (U' ⊓ V') _).1
              (hφ.comp (contMDiff_subtype_val (I := I) (U := U ⊓ V)))))) n ≫
        smoothCohomologyMayerVietorisδ (I := I) R k Q hUV n m h := by
  have hf : ∀ i, Set.MapsTo φ (![(U : Set M), (V : Set M)] i)
      (![(U' : Set N), (V' : Set N)] (id i)) := by simp [Fin.forall_fin_two, hfU, hfV]
  have hsmall : (smoothSmallCohomologyIso (I := J) R k Q hUV' m).inv ≫
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smoothSingularSubcomplexMap φ hφ)) m =
    HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smoothSmallSingularSubcomplexMap _ _ φ hφ id hf)) m ≫
      (smoothSmallCohomologyIso (I := I) R k Q hUV m).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact subcomplexSmallCohomologyIso_naturality R k Q (smoothSingularSubcomplex I M)
      ![(U : Set M), (V : Set M)] (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV)
      (smoothSingularSubcomplex J N) ![(U' : Set N), (V' : Set N)] (U'.isOpen.vecCons V'.isOpen)
      (iUnion_vecCons_opens_eq_univ hUV') (smoothSmallSingularSubcomplexMap _ _ φ hφ id hf)
      (smoothSingularSubcomplexMap φ hφ)
      (smoothSmallSingularSubcomplexMap_homOfLE_left _ _ φ hφ id hf) m
  have hnat := SSet.mayerVietorisCochainδ_naturality R k Q
    (smoothSingularSubcomplexMap
      (fun x : ↥(U ⊓ V) ↦ (⟨φ x.1, hfU x.2.1, hfV x.2.2⟩ : ↥(U' ⊓ V')))
      ((ContMDiff.subtypeVal_comp_iff (U' ⊓ V') _).1
        (hφ.comp (contMDiff_subtype_val (I := I) (U := U ⊓ V)))))
    (smoothSingularSubcomplexMap (fun x : U ↦ (⟨φ x.1, hfU x.2⟩ : U'))
      ((ContMDiff.subtypeVal_comp_iff U' _).1
        (hφ.comp (contMDiff_subtype_val (I := I) (U := U)))))
    (smoothSingularSubcomplexMap (fun x : V ↦ (⟨φ x.1, hfV x.2⟩ : V'))
      ((ContMDiff.subtypeVal_comp_iff V' _).1
        (hφ.comp (contMDiff_subtype_val (I := I) (U := V)))))
    (smoothSmallSingularSubcomplexMap _ _ φ hφ id hf)
    (isPushout_smoothSingularSubcomplex_inter I U V)
    (isPushout_smoothSingularSubcomplex_inter J U' V')
    -- Restriction of `φ` to `U ⊓ V` followed by inclusion equals inclusion followed by `φ`.
    (by rw [← smoothSingularSubcomplexMap_comp, ← smoothSingularSubcomplexMap_comp]; rfl)
    (by rw [← smoothSingularSubcomplexMap_comp, ← smoothSingularSubcomplexMap_comp]; rfl)
    (toSmoothSmallSingularSubcomplex_comp_smoothSmallSingularSubcomplexMap _ _ _ _ _ _ _ id hf
      _ _ _ _ _ rfl)
    (toSmoothSmallSingularSubcomplex_comp_smoothSmallSingularSubcomplexMap _ _ _ _ _ _ _ id hf
      _ _ _ _ _ rfl) n m h
  rw [smoothCohomologyMayerVietorisδ, smoothCohomologyMayerVietorisδ, Category.assoc, hsmall,
    ← Category.assoc, hnat, Category.assoc]

/-- **Compatibility of continuous and smooth singular cohomology Mayer–Vietoris connecting
morphisms.** Restriction from continuous singular cochains to smooth singular cochains intertwines
`TopCat.singularCohomologyMayerVietorisδ` and `smoothCohomologyMayerVietorisδ`. -/
@[reassoc]
lemma singularCohomologyMayerVietorisδ_comp_homologyMap_ι (n m : ℕ) (h : n + 1 = m := by lia) :
    TopCat.singularCohomologyMayerVietorisδ (X := TopCat.of M) R k Q U.isOpen V.isOpen
        (by simp [← Opens.coe_sup, hUV]) n m h ≫
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smoothSingularSubcomplex I M).ι) m =
    HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι) n ≫
      smoothCohomologyMayerVietorisδ (I := I) R k Q hUV n m h := by
  apply (cancel_mono (smoothSmallCohomologyIso (I := I) R k Q hUV m).hom).1
  have hnat := SSet.mayerVietorisCochainδ_naturality R k Q
    (smoothSingularSubcomplex I ↥(U ⊓ V)).ι
    (smoothSingularSubcomplex I U).ι
    (smoothSingularSubcomplex I V).ι
    (SSet.Subcomplex.homOfLE (inf_le_right : smoothSingularSubcomplex I M ⊓
      (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤ _))
    (isPushout_smoothSingularSubcomplex_inter I U V)
    (TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of M)
      (U : Set M) (V : Set M))
    (smoothSingularSubcomplexMap_ι (I := I) (J := I)
      (contMDiff_inclusion (inf_le_left : U ⊓ V ≤ U)))
    (smoothSingularSubcomplexMap_ι (I := I) (J := I)
      (contMDiff_inclusion (inf_le_right : U ⊓ V ≤ V)))
    (toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right (I := I) _ _ _)
    (toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right (I := I) _ _ _) n m h
  have hcomm : SSet.Subcomplex.homOfLE
        (inf_le_left : smoothSingularSubcomplex I M ⊓
          (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤ _) ≫
      (smoothSingularSubcomplex I M).ι =
    SSet.Subcomplex.homOfLE inf_le_right ≫
      ((TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)]).ι := by
    rw [SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι]
  rw [Category.assoc, Category.assoc, subcomplexSmallCohomologyIso_hom,
    smoothCohomologyMayerVietorisδ_comp_homologyMap (I := I) R k Q hUV n m h, ← hnat,
    ← HomologicalComplex.homologyMap_comp, ← SSet.cochainComplexMap_comp, hcomm,
    SSet.cochainComplexMap_comp, HomologicalComplex.homologyMap_comp,
    TopCat.singularCohomologyMayerVietorisδ_comp_homologyMap_assoc (X := TopCat.of M)
      R k Q U.isOpen V.isOpen _ n m h]

end Covered

end Cohomology

/-! ### The Mayer–Vietoris union step of the smoothing theorem -/

section Smoothing

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)

private lemma toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right_zero (U V : Opens M) :
    toSmoothSmallSingularSubcomplex ![(U : Set M), (V : Set M)] (Subtype.val : U → M)
        (contMDiff_subtype_val (I := I) (U := U))
        (fun x ↦ Eq.mpr (congrArg ((x : M) ∈ ·)
          (Matrix.cons_val_zero (U : Set M) ![(V : Set M)])) (SetLike.mem_coe.2 x.2)) ≫
      SSet.Subcomplex.homOfLE inf_le_right =
    (smoothSingularSubcomplex I U).ι ≫
      TopCat.toSmallSingularSubcomplex (X := TopCat.of M) ![(U : Set M), (V : Set M)]
        (i := 0) (Matrix.cons_val_zero (U : Set M) ![(V : Set M)]).superset :=
  toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right (I := I) _ _ _

private lemma toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right_one (U V : Opens M) :
    toSmoothSmallSingularSubcomplex ![(U : Set M), (V : Set M)] (Subtype.val : V → M)
        (contMDiff_subtype_val (I := I) (U := V))
        (fun x ↦ Eq.mpr (congrArg ((x : M) ∈ ·)
          ((Matrix.cons_val_one (U : Set M) ![(V : Set M)]).trans
            (Matrix.cons_val_zero (V : Set M) ![]))) (SetLike.mem_coe.2 x.2)) ≫
      SSet.Subcomplex.homOfLE inf_le_right =
    (smoothSingularSubcomplex I V).ι ≫
      TopCat.toSmallSingularSubcomplex (X := TopCat.of M) ![(U : Set M), (V : Set M)]
        (i := 1) (((Matrix.cons_val_one (U : Set M) ![(V : Set M)]).trans
          (Matrix.cons_val_zero (V : Set M) ![])).superset) :=
  toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right (I := I) _ _ _

/-- **The Mayer–Vietoris step of the smoothing theorem on a covered space.** If `U` and `V` are
open subsets covering `M` and the inclusion of smooth singular chains into continuous singular
chains is a quasi-isomorphism on `U`, `V`, and `U ⊓ V`, then it is a quasi-isomorphism on `M`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top
    {U V : Opens M} (hUV : U ⊔ V = ⊤)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hinter : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  let sq₁ := isPushout_smoothSingularSubcomplex_inter I U V
  let sq₂ := TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of M)
    (U : Set M) (V : Set M)
  let φ₁ := SSet.Subcomplex.homOfLE (inf_le_left : smoothSingularSubcomplex I M ⊓
    (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤ _)
  let φ₄ := SSet.Subcomplex.homOfLE (inf_le_right : smoothSingularSubcomplex I M ⊓
    (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤ _)
  have ht := smoothSingularSubcomplexMap_ι (I := I) (J := I)
    (contMDiff_inclusion (inf_le_left : U ⊓ V ≤ U))
  have hl := smoothSingularSubcomplexMap_ι (I := I) (J := I)
    (contMDiff_inclusion (inf_le_right : U ⊓ V ≤ V))
  have hr := toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right_zero I U V
  have hb := toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right_one I U V
  let ψ := SSet.mayerVietorisShortComplexMap R sq₁ sq₂ ht hl hr hb
  have h₁ : QuasiIso ψ.τ₁ :=
    (SSet.mayerVietorisShortComplexMap_τ₁ R sq₁ sq₂ ht hl hr hb).symm ▸ hinter
  have h₂ : QuasiIso ψ.τ₂ :=
    (SSet.mayerVietorisShortComplexMap_τ₂ R sq₁ sq₂ ht hl hr hb).symm ▸
      HomologicalComplex.quasiIso_biprod_map _ _
  have h₃ : QuasiIso (SSet.chainComplexMap φ₄ R) :=
    (SSet.mayerVietorisShortComplexMap_τ₃ R sq₁ sq₂ ht hl hr hb) ▸
      HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
        (SSet.shortExact_mayerVietorisShortComplex R sq₁)
        (SSet.shortExact_mayerVietorisShortComplex R sq₂) h₁ h₂
  have hsmall₁ := quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex R
    (smoothSingularSubcomplex I M) ![(U : Set M), (V : Set M)]
    (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV)
  have hsmall₂ := quasiIso_chainComplexMap_smallSingularSubcomplex_ι (X := TopCat.of M) R
    ![(U : Set M), (V : Set M)] (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV)
  have hcomp : SSet.chainComplexMap φ₁ R ≫ SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R =
      SSet.chainComplexMap φ₄ R ≫
        SSet.chainComplexMap
          ((TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)]).ι R := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι]
  have hprod : QuasiIso (SSet.chainComplexMap φ₁ R ≫
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
    rw [hcomp]; exact quasiIso_comp (hφ := h₃) (hφ' := hsmall₂) _ _
  exact quasiIso_of_comp_left (hφ := hsmall₁) (hφφ' := hprod) _ _

private lemma exists_iso_smoothSingularSubcomplex_opens {W Z : Opens M} {W' : Opens Z}
    (hWZ : W ≤ Z) (hWW' : ∀ y : Z, y ∈ W' ↔ y.1 ∈ W) :
    ∃ (eS : (smoothSingularSubcomplex I W : SSet) ≅ (smoothSingularSubcomplex I W' : SSet))
      (eT : TopCat.toSSet.obj (TopCat.of W) ≅ TopCat.toSSet.obj (TopCat.of W')),
      (smoothSingularSubcomplex I W').ι =
        eS.inv ≫ (smoothSingularSubcomplex I W).ι ≫ eT.hom := by
  let f : W → W' := fun x ↦ ⟨⟨x.1, hWZ x.2⟩, (hWW' _).2 x.2⟩
  let g : W' → W := fun y ↦ ⟨y.1.1, (hWW' y.1).1 y.2⟩
  have hf : ContMDiff I I ∞ f := (ContMDiff.subtypeVal_comp_iff W' f).1 (contMDiff_inclusion hWZ)
  have hg : ContMDiff I I ∞ g :=
    (ContMDiff.subtypeVal_comp_iff W g).1
      ((contMDiff_subtype_val (I := I) (U := Z)).comp (contMDiff_subtype_val (I := I) (U := W')))
  let eTop : TopCat.of W ≅ TopCat.of W' :=
    { hom := TopCat.ofHom ⟨f, hf.continuous⟩
      inv := TopCat.ofHom ⟨g, hg.continuous⟩
      -- `g (f x)` and `f (g y)` have the same underlying point of `M` as `x` and `y`.
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext y; rfl }
  refine ⟨{ hom := smoothSingularSubcomplexMap f hf
            inv := smoothSingularSubcomplexMap g hg
            hom_inv_id := by
              rw [← smoothSingularSubcomplexMap_comp]; exact smoothSingularSubcomplexMap_id
            inv_hom_id := by
              rw [← smoothSingularSubcomplexMap_comp]; exact smoothSingularSubcomplexMap_id },
    TopCat.toSSet.mapIso eTop, ?_⟩
  have hcomm := smoothSingularSubcomplexMap_ι (I := I) (J := I) hg
  have hinv := (TopCat.toSSet.mapIso eTop).inv_hom_id
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv, eTop] at hinv ⊢
  rw [← Category.assoc, hcomm, Category.assoc, hinv, Category.comp_id]

private lemma quasiIso_chainComplexMap_opens {W Z : Opens M} {W' : Opens Z}
    (hWZ : W ≤ Z) (hWW' : ∀ y : Z, y ∈ W' ↔ y.1 ∈ W)
    (hW : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I W).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I W').ι R) := by
  obtain ⟨eS, eT, hι⟩ := exists_iso_smoothSingularSubcomplex_opens I hWZ hWW'
  have hfac : SSet.chainComplexMap (smoothSingularSubcomplex I W').ι R =
      SSet.chainComplexMap eS.inv R ≫ SSet.chainComplexMap (smoothSingularSubcomplex I W).ι R ≫
        SSet.chainComplexMap eT.hom R := by
    rw [hι]; simp [SSet.chainComplexMap]
  rw [hfac]
  have h₁ : QuasiIso (SSet.chainComplexMap eS.inv R) := inferInstance
  have h₂ : QuasiIso (SSet.chainComplexMap eT.hom R) := inferInstance
  have h₁₂ : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I W).ι R ≫
      SSet.chainComplexMap eT.hom R) := quasiIso_comp (hφ := hW) (hφ' := h₂) _ _
  exact quasiIso_comp (hφ := h₁) (hφ' := h₁₂) _ _

/-- **The Mayer–Vietoris union step of the smoothing theorem.** For any two open subsets `U` and
`V` of `M`, if the inclusion of smooth singular chains into continuous singular chains is a
quasi-isomorphism on `U`, `V`, and `U ⊓ V`, then it is a quasi-isomorphism on `U ⊔ V`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup {U V : Opens M}
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hinter : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊔ V)).ι R) := by
  let U' : Opens ↥(U ⊔ V) := U.comap ⟨Subtype.val, continuous_subtype_val⟩
  let V' : Opens ↥(U ⊔ V) := V.comap ⟨Subtype.val, continuous_subtype_val⟩
  have htop : U' ⊔ V' = ⊤ := by ext x; exact ⟨fun _ ↦ trivial, fun _ ↦ x.2⟩
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top I R htop
    (quasiIso_chainComplexMap_opens I R (le_sup_left : U ≤ U ⊔ V) (fun _ ↦ Iff.rfl) hU)
    (quasiIso_chainComplexMap_opens I R (le_sup_right : V ≤ U ⊔ V) (fun _ ↦ Iff.rfl) hV)
    (quasiIso_chainComplexMap_opens I R (inf_le_sup : U ⊓ V ≤ U ⊔ V) (fun _ ↦ Iff.rfl) hinter)

variable (k : Type*) [Ring k] [Linear k C] (Q : C)

/-- **The Mayer–Vietoris step for smooth singular cochains on a covered space.** If `U` and `V` are
open subsets covering `M` and restricting continuous singular cochains to smooth singular chains is
a quasi-isomorphism on `U`, `V`, and `U ⊓ V`, then it is a quasi-isomorphism on `M`. -/
theorem quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top
    {U V : Opens M} (hUV : U ⊔ V = ⊤)
    (hU : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I U).ι))
    (hV : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I V).ι))
    (hinter : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I ↥(U ⊓ V)).ι)) :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I M).ι) := by
  let sq₁ := isPushout_smoothSingularSubcomplex_inter I U V
  let sq₂ := TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of M)
    (U : Set M) (V : Set M)
  let φ₁ := SSet.Subcomplex.homOfLE (inf_le_left : smoothSingularSubcomplex I M ⊓
    (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤ _)
  let φ₄ := SSet.Subcomplex.homOfLE (inf_le_right : smoothSingularSubcomplex I M ⊓
    (TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)] ≤ _)
  have ht := smoothSingularSubcomplexMap_ι (I := I) (J := I)
    (contMDiff_inclusion (inf_le_left : U ⊓ V ≤ U))
  have hl := smoothSingularSubcomplexMap_ι (I := I) (J := I)
    (contMDiff_inclusion (inf_le_right : U ⊓ V ≤ V))
  have hr := toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right_zero I U V
  have hb := toSmoothSmallSingularSubcomplex_subtypeVal_homOfLE_right_one I U V
  let ψ : SSet.mayerVietorisCochainShortComplex R k Q sq₂.toCommSq ⟶
      SSet.mayerVietorisCochainShortComplex R k Q sq₁.toCommSq :=
    { τ₁ := SSet.cochainComplexMap φ₄
      τ₂ := biprod.map (SSet.cochainComplexMap (smoothSingularSubcomplex I U).ι)
        (SSet.cochainComplexMap (smoothSingularSubcomplex I V).ι)
      τ₃ := SSet.cochainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι
      comm₁₂ := by apply biprod.hom_ext <;> simp [φ₄, ← SSet.cochainComplexMap_comp, hr, hb]
      -- `Opens.inclusion` has underlying function `Set.inclusion`.
      comm₂₃ := by apply biprod.hom_ext' <;> (simp [← SSet.cochainComplexMap_comp, ht, hl]; rfl) }
  have h₂ : QuasiIso ψ.τ₂ := HomologicalComplex.quasiIso_biprod_map _ _
  have h₁ : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q) φ₄) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₁ ψ
      (SSet.shortExact_mayerVietorisCochainShortComplex R k Q sq₂)
      (SSet.shortExact_mayerVietorisCochainShortComplex R k Q sq₁) h₂ hinter
  have hsmall₁ := quasiIso_cochainComplexMap_homOfLE_inf_smallSingularSubcomplex R k Q
    (smoothSingularSubcomplex I M) ![(U : Set M), (V : Set M)]
    (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV)
  have hsmall₂ := quasiIso_cochainComplexMap_smallSingularSubcomplex_ι (X := TopCat.of M) R k Q
    ![(U : Set M), (V : Set M)] (U.isOpen.vecCons V.isOpen) (iUnion_vecCons_opens_eq_univ hUV)
  have hcomp : SSet.cochainComplexMap (R := R) (k := k) (M := Q)
        (smoothSingularSubcomplex I M).ι ≫ SSet.cochainComplexMap φ₁ =
      SSet.cochainComplexMap
        ((TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)]).ι ≫
        SSet.cochainComplexMap φ₄ := by
    rw [← SSet.cochainComplexMap_comp, ← SSet.cochainComplexMap_comp,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι]
  have hprod : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
        (smoothSingularSubcomplex I M).ι ≫ SSet.cochainComplexMap φ₁) := by
    rw [hcomp]; exact quasiIso_comp (hφ := hsmall₂) (hφ' := h₁) _ _
  exact quasiIso_of_comp_right (hφ := hsmall₁) (hφφ' := hprod) _ _

private lemma isIso_cochainComplexMap_of_iso {X Y : SSet.{u}} (e : X ≅ Y) :
    IsIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q) e.hom) :=
  ⟨SSet.cochainComplexMap e.inv,
    by rw [← SSet.cochainComplexMap_comp, e.inv_hom_id, SSet.cochainComplexMap_id],
    by rw [← SSet.cochainComplexMap_comp, e.hom_inv_id, SSet.cochainComplexMap_id]⟩

private lemma quasiIso_cochainComplexMap_opens {W Z : Opens M} {W' : Opens Z}
    (hWZ : W ≤ Z) (hWW' : ∀ y : Z, y ∈ W' ↔ y.1 ∈ W)
    (hW : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I W).ι)) :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I W').ι) := by
  obtain ⟨eS, eT, hι⟩ := exists_iso_smoothSingularSubcomplex_opens I hWZ hWW'
  rw [hι, SSet.cochainComplexMap_comp, SSet.cochainComplexMap_comp]
  have : IsIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q) eT.hom) :=
    isIso_cochainComplexMap_of_iso R k Q eT
  have : IsIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q) eS.inv) :=
    isIso_cochainComplexMap_of_iso R k Q eS.symm
  have h₁ : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q) eT.hom) := inferInstance
  have h₂ : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q) eS.inv) := inferInstance
  have h₁₂ : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q) eT.hom ≫
      SSet.cochainComplexMap (smoothSingularSubcomplex I W).ι) :=
    quasiIso_comp (hφ := h₁) (hφ' := hW) _ _
  exact quasiIso_comp (hφ := h₁₂) (hφ' := h₂) _ _

/-- **The Mayer–Vietoris union step for smooth singular cochains.** For any two open subsets `U`
and `V` of `M`, if restricting continuous singular cochains to smooth singular chains is a
quasi-isomorphism on `U`, `V`, and `U ⊓ V`, then it is a quasi-isomorphism on `U ⊔ V`. -/
theorem quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι_sup {U V : Opens M}
    (hU : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I U).ι))
    (hV : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I V).ι))
    (hinter : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I ↥(U ⊓ V)).ι)) :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := Q)
      (smoothSingularSubcomplex I ↥(U ⊔ V)).ι) := by
  let U' : Opens ↥(U ⊔ V) := U.comap ⟨Subtype.val, continuous_subtype_val⟩
  let V' : Opens ↥(U ⊔ V) := V.comap ⟨Subtype.val, continuous_subtype_val⟩
  have htop : U' ⊔ V' = ⊤ := by ext x; exact ⟨fun _ ↦ trivial, fun _ ↦ x.2⟩
  exact quasiIso_cochainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top I R k Q htop
    (quasiIso_cochainComplexMap_opens I R k Q (le_sup_left : U ≤ U ⊔ V) (fun _ ↦ Iff.rfl) hU)
    (quasiIso_cochainComplexMap_opens I R k Q (le_sup_right : V ≤ U ⊔ V) (fun _ ↦ Iff.rfl) hV)
    (quasiIso_cochainComplexMap_opens I R k Q (inf_le_sup : U ⊓ V ≤ U ⊔ V) (fun _ ↦ Iff.rfl)
      hinter)

end Smoothing

end TauCeti
