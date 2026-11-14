/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Stratum
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct

/-!
# Variable-rank Whitney sums and binary biproducts for bundle atlases

Given two variable-rank bundle atlases `A` and `D`, `FiniteRankAtlas.whitneySum A D` glues the
constant-rank Whitney sums of their restrictions to the joint clopen rank bi-strata
`{x : X // (A.rank x, D.rank x) = p}` via `FiniteRankAtlas.ofClopenCores`. Because several input
rank pairs `(m, n)` merge into the same output stratum `m + n`, this requires the clopen-partition
gluing infrastructure rather than stratumwise products.

* `whitneyFst`, `whitneySnd`, `whitneyInl`, and `whitneyInr` assemble the block-coordinate
  projections and inclusions across the joint rank bi-strata without completeness assumptions on
  `𝕜`, forming a `BinaryBicone` with `whitney_total` and `whitneyBiconeIsBilimit`.
* `HasBinaryBiproducts (FiniteRankAtlas 𝕜 X)` equips `FiniteRankAtlas 𝕜 X` with binary biproducts,
  with concrete pairing (`whitneyLift`), copairing (`whitneyDesc`), functorial action
  (`whitneyMap`, `whitneyMapIso`), symmetry, associativity, and zero-unit coherence isomorphisms
  (`whitneyCommIso`, `whitneyAssocIso`, `whitneyZeroLeftIso`, `whitneyZeroRightIso`), trivial-atlas
  compatibility (`whitneySumTrivialIso`), and `@[simp]` rank formulas (`rank_whitneySum`,
  `rank_biprod`).
* `ofCoreWhitneySumIso` shows that the constant-rank embedding `ofCore` preserves concrete Whitney
  sums up to canonical isomorphism intertwining the four bicone legs.
* `whitneySumFiberProdHomeomorph` identifies the reconstructed total space of `whitneySum A D` over
  `X` with the topological fibre product
  `{pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* M. F. Atiyah, *K-Theory*, §1.1–1.2.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Topology VectorBundleCore

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-! ### Variable-rank Whitney sums and binary biproducts -/

/-- The Whitney sum of two variable-rank bundle atlases, assembled over the joint clopen rank
bi-strata `{x : X // (A.rank x, D.rank x) = p}` from constant-rank Whitney sums. -/
-- Expose the glued construction so homs and fibre types reduce over `ofClopenCores`.
@[expose, implicit_reducible]
noncomputable def whitneySum (A D : FiniteRankAtlas 𝕜 X) : FiniteRankAtlas 𝕜 X :=
  ofClopenCores (A.rank.prodMk D.rank) fun p ↦
    (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p).whitneySum
      (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p)

@[simp]
theorem rank_whitneySum (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySum A D).rank = A.rank + D.rank :=
  LocallyConstant.ext fun _ ↦ rfl

/-- Projection of the variable-rank Whitney sum onto its first summand. -/
noncomputable def whitneyFst (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ A :=
  mapClopenCores (A.rank.prodMk D.rank) (fun p ↦
    FiniteRankBundleCore.whitneyFst
      (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p)
      (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p)) ≫
    (A.clopenPullIso (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl)).hom

/-- Projection of the variable-rank Whitney sum onto its second summand. -/
noncomputable def whitneySnd (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ D :=
  mapClopenCores (A.rank.prodMk D.rank) (fun p ↦
    FiniteRankBundleCore.whitneySnd
      (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p)
      (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p)) ≫
    (D.clopenPullIso (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl)).hom

/-- Inclusion of the first summand into the variable-rank Whitney sum. -/
noncomputable def whitneyInl (A D : FiniteRankAtlas 𝕜 X) : A ⟶ whitneySum A D :=
  (A.clopenPullIso (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl)).inv ≫
    mapClopenCores (A.rank.prodMk D.rank) (fun p ↦
      FiniteRankBundleCore.whitneyInl
        (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p)
        (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p))

/-- Inclusion of the second summand into the variable-rank Whitney sum. -/
noncomputable def whitneyInr (A D : FiniteRankAtlas 𝕜 X) : D ⟶ whitneySum A D :=
  (D.clopenPullIso (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl)).inv ≫
    mapClopenCores (A.rank.prodMk D.rank) (fun p ↦
      FiniteRankBundleCore.whitneyInr
        (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p)
        (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p))

@[simp]
theorem fiberMap_whitneyFst (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyFst A D).fiberMap x =
      (LinearMap.fst 𝕜 (Fin (A.rank x) → 𝕜) (Fin (D.rank x) → 𝕜)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap := by
  apply LinearMap.ext
  intro v
  rw [whitneyFst, fiberMap_comp, LinearMap.comp_apply, fiberMap_clopenPullIso_hom_apply,
    fiberMap_mapClopenCores, FiniteRankBundleCore.fiberMap_whitneyFst]
  rfl

@[simp]
theorem fiberMap_whitneySnd (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySnd A D).fiberMap x =
      (LinearMap.snd 𝕜 (Fin (A.rank x) → 𝕜) (Fin (D.rank x) → 𝕜)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap := by
  apply LinearMap.ext
  intro v
  rw [whitneySnd, fiberMap_comp, LinearMap.comp_apply, fiberMap_clopenPullIso_hom_apply,
    fiberMap_mapClopenCores, FiniteRankBundleCore.fiberMap_whitneySnd]
  rfl

@[simp]
theorem fiberMap_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInl A D).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
        (LinearMap.inl 𝕜 (Fin (A.rank x) → 𝕜) (Fin (D.rank x) → 𝕜)) := by
  apply LinearMap.ext
  intro u
  rw [whitneyInl, fiberMap_comp, LinearMap.comp_apply, fiberMap_mapClopenCores,
    FiniteRankBundleCore.fiberMap_whitneyInl]
  exact congrArg (fun u' ↦ (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (u', 0))
    (A.fiberMap_clopenPullIso_inv_apply (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) x u)

@[simp]
theorem fiberMap_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInr A D).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
        (LinearMap.inr 𝕜 (Fin (A.rank x) → 𝕜) (Fin (D.rank x) → 𝕜)) := by
  apply LinearMap.ext
  intro w
  rw [whitneyInr, fiberMap_comp, LinearMap.comp_apply, fiberMap_mapClopenCores,
    FiniteRankBundleCore.fiberMap_whitneyInr]
  exact congrArg (fun w' ↦ (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (0, w'))
    (D.fiberMap_clopenPullIso_inv_apply (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) x w)

@[reassoc (attr := simp)]
theorem whitneyInl_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A := by
  dsimp only [whitneyInl, whitneyFst, whitneySum]
  rw [Category.assoc, ← Category.assoc (mapClopenCores _ _), ← mapClopenCores_comp]
  simp

@[reassoc (attr := simp)]
theorem whitneyInl_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneySnd A D = 0 := by
  dsimp only [whitneyInl, whitneySnd, whitneySum]
  rw [Category.assoc, ← Category.assoc (mapClopenCores _ _), ← mapClopenCores_comp]
  simp

@[reassoc (attr := simp)]
theorem whitneyInr_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneyFst A D = 0 := by
  dsimp only [whitneyInr, whitneyFst, whitneySum]
  rw [Category.assoc, ← Category.assoc (mapClopenCores _ _), ← mapClopenCores_comp]
  simp

@[reassoc (attr := simp)]
theorem whitneyInr_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D := by
  dsimp only [whitneyInr, whitneySnd, whitneySum]
  rw [Category.assoc, ← Category.assoc (mapClopenCores _ _), ← mapClopenCores_comp]
  simp

/-- The variable-rank Whitney sum with its projections and inclusions as a `BinaryBicone`. -/
-- Expose the cone point so leg types reduce to `whitneySum A D`.
@[expose]
noncomputable def whitneyBicone (A D : FiniteRankAtlas 𝕜 X) : BinaryBicone A D where
  pt := whitneySum A D
  fst := whitneyFst A D
  snd := whitneySnd A D
  inl := whitneyInl A D
  inr := whitneyInr A D
  inl_fst := whitneyInl_fst A D
  inl_snd := whitneyInl_snd A D
  inr_fst := whitneyInr_fst A D
  inr_snd := whitneyInr_snd A D

@[simp] theorem whitneyBicone_pt (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).pt = whitneySum A D := (rfl)

@[simp] theorem whitneyBicone_fst (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).fst = whitneyFst A D := (rfl)

@[simp] theorem whitneyBicone_snd (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).snd = whitneySnd A D := (rfl)

@[simp] theorem whitneyBicone_inl (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inl = whitneyInl A D := (rfl)

@[simp] theorem whitneyBicone_inr (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inr = whitneyInr A D := (rfl)

/-- The variable-rank Whitney projections and inclusions resolve the identity. -/
@[simp]
theorem whitney_total (A D : FiniteRankAtlas 𝕜 X) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  dsimp only [whitneyFst, whitneyInl, whitneySnd, whitneyInr, whitneySum]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← mapClopenCores_comp]
  rw [← mapClopenCores_add]
  simp only [FiniteRankBundleCore.whitney_total, mapClopenCores_id]

/-- The variable-rank Whitney bicone is a binary bilimit. -/
noncomputable def whitneyBiconeIsBilimit (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).IsBilimit :=
  isBinaryBilimitOfTotal _ (whitney_total A D)

instance : HasBinaryBiproducts (FiniteRankAtlas 𝕜 X) where
  has_binary_biproduct A D := ⟨⟨whitneyBicone A D, whitneyBiconeIsBilimit A D⟩⟩

/-! ### Pairing, copairing, functoriality, and biproduct comparisons -/

section UniversalProperty

variable {A A' A'' D D' D'' C E : FiniteRankAtlas 𝕜 X}

/-- Pair two morphisms into a concrete variable-rank Whitney sum. -/
noncomputable def whitneyLift (f : E ⟶ A) (g : E ⟶ D) : E ⟶ whitneySum A D :=
  f ≫ whitneyInl A D + g ≫ whitneyInr A D

theorem whitneyLift_def (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g = f ≫ whitneyInl A D + g ≫ whitneyInr A D :=
  (rfl)

@[reassoc (attr := simp)]
theorem whitneyLift_fst (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneyFst A D = f := by
  simp [whitneyLift, Preadditive.add_comp]

@[reassoc (attr := simp)]
theorem whitneyLift_snd (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneySnd A D = g := by
  simp [whitneyLift, Preadditive.add_comp]

/-- Morphisms into `whitneySum A D` are determined by their compositions with the projections. -/
theorem whitneySum_hom_ext {h₁ h₂ : E ⟶ whitneySum A D}
    (hfst : h₁ ≫ whitneyFst A D = h₂ ≫ whitneyFst A D)
    (hsnd : h₁ ≫ whitneySnd A D = h₂ ≫ whitneySnd A D) : h₁ = h₂ :=
  (whitneyBiconeIsBilimit A D).isLimit.hom_ext fun ⟨j⟩ ↦ by cases j <;> assumption

@[reassoc]
theorem comp_whitneyLift (h : C ⟶ E) (f : E ⟶ A) (g : E ⟶ D) :
    h ≫ whitneyLift f g = whitneyLift (h ≫ f) (h ≫ g) := by
  simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

@[simp]
theorem whitneyLift_fst_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyLift (whitneyFst A D) (whitneySnd A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp]
theorem fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) :
    (whitneyLift f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearMap.comp
        ((f.fiberMap x).prod (g.fiberMap x)) := by
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)
  have h : (e.symm.toLinearMap.comp (LinearMap.inl 𝕜 _ _)).comp (f.fiberMap x) +
      (e.symm.toLinearMap.comp (LinearMap.inr 𝕜 _ _)).comp (g.fiberMap x) =
      e.symm.toLinearMap.comp ((f.fiberMap x).prod (g.fiberMap x)) := by
    apply LinearMap.ext
    intro v
    simp [← map_add]
  simp only [whitneyLift, fiberMap_add, fiberMap_comp, fiberMap_whitneyInl, fiberMap_whitneyInr]
  exact h

/-- Copair two morphisms out of a concrete variable-rank Whitney sum. -/
noncomputable def whitneyDesc (f : A ⟶ E) (g : D ⟶ E) : whitneySum A D ⟶ E :=
  whitneyFst A D ≫ f + whitneySnd A D ≫ g

theorem whitneyDesc_def (f : A ⟶ E) (g : D ⟶ E) :
    whitneyDesc f g = whitneyFst A D ≫ f + whitneySnd A D ≫ g :=
  (rfl)

@[reassoc (attr := simp)]
theorem whitneyInl_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInl A D ≫ whitneyDesc f g = f := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyInr_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInr A D ≫ whitneyDesc f g = g := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyLift_desc (f : E ⟶ A) (g : E ⟶ D) (h : A ⟶ C) (k : D ⟶ C) :
    whitneyLift f g ≫ whitneyDesc h k = f ≫ h + g ≫ k := by
  simp [whitneyLift, whitneyDesc, Preadditive.add_comp, Preadditive.comp_add]

/-- Morphisms out of `whitneySum A D` are determined by their compositions with the inclusions. -/
theorem whitneySum_hom_ext' {h₁ h₂ : whitneySum A D ⟶ E}
    (hinl : whitneyInl A D ≫ h₁ = whitneyInl A D ≫ h₂)
    (hinr : whitneyInr A D ≫ h₁ = whitneyInr A D ≫ h₂) : h₁ = h₂ :=
  (whitneyBiconeIsBilimit A D).isColimit.hom_ext fun ⟨j⟩ ↦ by cases j <;> assumption

@[reassoc]
theorem whitneyDesc_comp (f : A ⟶ E) (g : D ⟶ E) (h : E ⟶ C) :
    whitneyDesc f g ≫ h = whitneyDesc (f ≫ h) (g ≫ h) := by
  simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

@[simp]
theorem whitneyDesc_inl_inr (A D : FiniteRankAtlas 𝕜 X) :
    whitneyDesc (whitneyInl A D) (whitneyInr A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp]
theorem fiberMap_whitneyDesc (f : A ⟶ E) (g : D ⟶ E) (x : X) :
    (whitneyDesc f g).fiberMap x =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap := by
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)
  have h : (f.fiberMap x).comp ((LinearMap.fst 𝕜 _ _).comp e.toLinearMap) +
      (g.fiberMap x).comp ((LinearMap.snd 𝕜 _ _).comp e.toLinearMap) =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp e.toLinearMap := by
    apply LinearMap.ext
    intro v
    rfl
  simp only [whitneyDesc, fiberMap_add, fiberMap_comp, fiberMap_whitneyFst, fiberMap_whitneySnd]
  exact h

/-- Direct sum of two morphisms on concrete variable-rank Whitney sums. -/
noncomputable def whitneyMap (f : A ⟶ A') (g : D ⟶ D') :
    whitneySum A D ⟶ whitneySum A' D' :=
  whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g)

theorem whitneyMap_def (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g = whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g) :=
  (rfl)

@[reassoc (attr := simp)]
theorem whitneyMap_fst (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneyFst A' D' = whitneyFst A D ≫ f :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)]
theorem whitneyMap_snd (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneySnd A' D' = whitneySnd A D ≫ g :=
  whitneyLift_snd _ _

@[reassoc (attr := simp)]
theorem whitneyInl_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInl A D ≫ whitneyMap f g = f ≫ whitneyInl A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[reassoc (attr := simp)]
theorem whitneyInr_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInr A D ≫ whitneyMap f g = g ≫ whitneyInr A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_id (A D : FiniteRankAtlas 𝕜 X) :
    whitneyMap (𝟙 A) (𝟙 D) = 𝟙 (whitneySum A D) :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_zero (A A' D D' : FiniteRankAtlas 𝕜 X) :
    whitneyMap (0 : A ⟶ A') (0 : D ⟶ D') = 0 :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_add (f₁ f₂ : A ⟶ A') (g₁ g₂ : D ⟶ D') :
    whitneyMap (f₁ + f₂) (g₁ + g₂) = whitneyMap f₁ g₁ + whitneyMap f₂ g₂ :=
  whitneySum_hom_ext (by simp [Preadditive.comp_add, Preadditive.add_comp])
    (by simp [Preadditive.comp_add, Preadditive.add_comp])

@[simp]
theorem whitneyMap_comp (f₁ : A ⟶ A') (f₂ : A' ⟶ A'') (g₁ : D ⟶ D') (g₂ : D' ⟶ D'') :
    whitneyMap (f₁ ≫ f₂) (g₁ ≫ g₂) = whitneyMap f₁ g₁ ≫ whitneyMap f₂ g₂ :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X) :
    (whitneyMap f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)).symm.toLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearMap) := by
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)
  let e' := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A'.rank x) (D'.rank x)
  have h : e'.symm.toLinearMap.comp
      (((f.fiberMap x).comp ((LinearMap.fst 𝕜 _ _).comp e.toLinearMap)).prod
        ((g.fiberMap x).comp ((LinearMap.snd 𝕜 _ _).comp e.toLinearMap))) =
      e'.symm.toLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp e.toLinearMap) := by
    ext v i
    rfl
  simp only [whitneyMap, fiberMap_whitneyLift, fiberMap_comp, fiberMap_whitneyFst,
    fiberMap_whitneySnd]
  exact h

/-- Direct sum of two variable-rank bundle isomorphisms. -/
noncomputable def whitneyMapIso (e₁ : A ≅ A') (e₂ : D ≅ D') :
    whitneySum A D ≅ whitneySum A' D' where
  hom := whitneyMap e₁.hom e₂.hom
  inv := whitneyMap e₁.inv e₂.inv
  hom_inv_id := by rw [← whitneyMap_comp, e₁.hom_inv_id, e₂.hom_inv_id, whitneyMap_id]
  inv_hom_id := by rw [← whitneyMap_comp, e₁.inv_hom_id, e₂.inv_hom_id, whitneyMap_id]

@[simp]
theorem whitneyMapIso_hom (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).hom = whitneyMap e₁.hom e₂.hom :=
  (rfl)

@[simp]
theorem whitneyMapIso_inv (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).inv = whitneyMap e₁.inv e₂.inv :=
  (rfl)

end UniversalProperty

section Coherence

/-- Symmetry isomorphism exchanging the two summands of a variable-rank Whitney sum. -/
noncomputable def whitneyCommIso (A D : FiniteRankAtlas 𝕜 X) :
    whitneySum A D ≅ whitneySum D A where
  hom := whitneyLift (whitneySnd A D) (whitneyFst A D)
  inv := whitneyLift (whitneySnd D A) (whitneyFst D A)
  hom_inv_id := whitneySum_hom_ext (by simp) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyCommIso_hom (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).hom = whitneyLift (whitneySnd A D) (whitneyFst A D) :=
  (rfl)

@[simp]
theorem whitneyCommIso_inv (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).inv = whitneyLift (whitneySnd D A) (whitneyFst D A) :=
  (rfl)

@[reassoc]
theorem whitneyMap_commIso_hom {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ (whitneyCommIso A' D').hom =
      (whitneyCommIso A D).hom ≫ whitneyMap g f :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Associativity isomorphism regrouping a threefold variable-rank Whitney sum. -/
noncomputable def whitneyAssocIso (A D C : FiniteRankAtlas 𝕜 X) :
    whitneySum (whitneySum A D) C ≅ whitneySum A (whitneySum D C) where
  hom := whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
    (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _))
  inv := whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
    (whitneySnd _ _ ≫ whitneySnd D C)
  hom_inv_id := whitneySum_hom_ext (whitneySum_hom_ext (by simp) (by simp)) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

@[simp]
theorem whitneyAssocIso_hom (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).hom =
      whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
        (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _)) :=
  (rfl)

@[simp]
theorem whitneyAssocIso_inv (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).inv =
      whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
        (whitneySnd _ _ ≫ whitneySnd D C) :=
  (rfl)

@[reassoc]
theorem whitneyMap_assocIso_hom {A A' D D' C C' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (h : C ⟶ C') :
    whitneyMap (whitneyMap f g) h ≫ (whitneyAssocIso A' D' C').hom =
      (whitneyAssocIso A D C).hom ≫ whitneyMap f (whitneyMap g h) :=
  whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

/-- Left unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
noncomputable def whitneyZeroLeftIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum (trivial 𝕜 X 0) A ≅ A where
  hom := whitneySnd (trivial 𝕜 X 0) A
  inv := whitneyInr (trivial 𝕜 X 0) A
  hom_inv_id := whitneySum_hom_ext' (isZero_trivial_zero.eq_of_src _ _) (by simp)
  inv_hom_id := whitneyInr_snd (trivial 𝕜 X 0) A

@[simp]
theorem whitneyZeroLeftIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).hom = whitneySnd (trivial 𝕜 X 0) A :=
  (rfl)

@[simp]
theorem whitneyZeroLeftIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).inv = whitneyInr (trivial 𝕜 X 0) A :=
  (rfl)

@[reassoc]
theorem whitneyMap_zeroLeftIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (g : trivial 𝕜 X 0 ⟶ trivial 𝕜 X 0) (f : A ⟶ A') :
    whitneyMap g f ≫ (whitneyZeroLeftIso A').hom = (whitneyZeroLeftIso A).hom ≫ f := by
  simp only [whitneyZeroLeftIso_hom, whitneyMap_snd]

/-- Right unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
noncomputable def whitneyZeroRightIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum A (trivial 𝕜 X 0) ≅ A where
  hom := whitneyFst A (trivial 𝕜 X 0)
  inv := whitneyInl A (trivial 𝕜 X 0)
  hom_inv_id := whitneySum_hom_ext' (by simp) (isZero_trivial_zero.eq_of_src _ _)
  inv_hom_id := whitneyInl_fst A (trivial 𝕜 X 0)

@[simp]
theorem whitneyZeroRightIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).hom = whitneyFst A (trivial 𝕜 X 0) :=
  (rfl)

@[simp]
theorem whitneyZeroRightIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).inv = whitneyInl A (trivial 𝕜 X 0) :=
  (rfl)

@[reassoc]
theorem whitneyMap_zeroRightIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : trivial 𝕜 X 0 ⟶ trivial 𝕜 X 0) :
    whitneyMap f g ≫ (whitneyZeroRightIso A').hom = (whitneyZeroRightIso A).hom ≫ f := by
  simp only [whitneyZeroRightIso_hom, whitneyMap_fst]

private def coreWhitneySumTrivialIso {Y : Type*} [TopologicalSpace Y] (m n : ℕ) :
    (FiniteRankBundleCore.trivial 𝕜 Y m).whitneySum (FiniteRankBundleCore.trivial 𝕜 Y n) ≅
      FiniteRankBundleCore.trivial 𝕜 Y (m + n) :=
  FiniteRankBundleCore.constIso (fun _ ↦ by simp)
    (ContinuousLinearEquiv.refl 𝕜 (Fin (m + n) → 𝕜))
    fun i j x _ _ ↦ ContinuousLinearMap.ext fun v ↦
      (splitCoords (𝕜 := 𝕜) m n).injective <|
        (FiniteRankBundleCore.splitCoords_coordChange_whitneySum
          (FiniteRankBundleCore.trivial 𝕜 Y m)
          (FiniteRankBundleCore.trivial 𝕜 Y n) i j x v).trans <| by
          rw [FiniteRankBundleCore.coordChange_trivial, FiniteRankBundleCore.coordChange_trivial,
            FiniteRankBundleCore.coordChange_trivial]
          rfl

private theorem fiberMap_coreWhitneySumTrivialIso_hom {Y : Type*} [TopologicalSpace Y]
    (m n : ℕ) (y : Y) :
    (coreWhitneySumTrivialIso (𝕜 := 𝕜) m n).hom.fiberMap y =
      ContinuousLinearMap.id 𝕜 (Fin (m + n) → 𝕜) :=
  FiniteRankBundleCore.fiberMap_constIso_hom _ _ _ y

/-- The Whitney sum of two variable-rank trivial atlases is canonically isomorphic to the trivial
atlas whose rank is the pointwise sum of their ranks. -/
noncomputable def whitneySumTrivialIso (r₁ r₂ : LocallyConstant X ℕ) :
    whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂) ≅ trivial 𝕜 X (r₁ + r₂) :=
  isoClopenCores (r₁.prodMk r₂) (fun p ↦ coreWhitneySumTrivialIso (𝕜 := 𝕜) p.1 p.2) ≪≫
    (trivial 𝕜 X (r₁ + r₂)).clopenPullIso (r₁.prodMk r₂) (fun p ↦ p.1 + p.2) (fun _ ↦ rfl)

@[simp]
theorem fiberMap_whitneySumTrivialIso_hom (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (whitneySumTrivialIso (𝕜 := 𝕜) r₁ r₂).hom.fiberMap x = LinearMap.id := by
  apply LinearMap.ext
  intro v
  have h₁ : (isoClopenCores (r₁.prodMk r₂)
      (fun p ↦ coreWhitneySumTrivialIso (𝕜 := 𝕜) p.1 p.2)).hom.fiberMap x v = v :=
    DFunLike.congr_fun
      ((congrArg (fun f ↦ f.fiberMap x) (isoClopenCores_hom (r₁.prodMk r₂)
        (fun p ↦ coreWhitneySumTrivialIso (𝕜 := 𝕜) p.1 p.2))).trans <|
        (fiberMap_mapClopenCores (r₁.prodMk r₂)
          (fun p ↦ (coreWhitneySumTrivialIso (𝕜 := 𝕜) p.1 p.2).hom) x).trans <|
        congrArg ContinuousLinearMap.toLinearMap
          (fiberMap_coreWhitneySumTrivialIso_hom ((r₁.prodMk r₂) x).1 ((r₁.prodMk r₂) x).2
            (⟨x, rfl⟩ : {y : X // r₁.prodMk r₂ y = r₁.prodMk r₂ x}))) v
  exact (DFunLike.congr_fun (fiberMap_comp
    (isoClopenCores (r₁.prodMk r₂) (fun p ↦ coreWhitneySumTrivialIso (𝕜 := 𝕜) p.1 p.2)).hom
    ((trivial 𝕜 X (r₁ + r₂)).clopenPullIso (r₁.prodMk r₂) (fun p ↦ p.1 + p.2) (fun _ ↦ rfl)).hom
    x) v).trans <| (congrArg _ h₁).trans <|
      (trivial 𝕜 X (r₁ + r₂)).fiberMap_clopenPullIso_hom_apply (r₁.prodMk r₂)
        (fun p ↦ p.1 + p.2) (fun _ ↦ rfl) x v

@[simp]
theorem fiberMap_whitneySumTrivialIso_inv (r₁ r₂ : LocallyConstant X ℕ) (x : X) :
    (whitneySumTrivialIso (𝕜 := 𝕜) r₁ r₂).inv.fiberMap x = LinearMap.id := by
  apply LinearMap.ext
  intro v
  let v' : (whitneySum (trivial 𝕜 X r₁) (trivial 𝕜 X r₂)).Fiber x := v
  exact (congrArg ((whitneySumTrivialIso (𝕜 := 𝕜) r₁ r₂).inv.fiberMap x)
    (DFunLike.congr_fun (fiberMap_whitneySumTrivialIso_hom r₁ r₂ x) v')).symm.trans <|
    (DFunLike.congr_fun (fiberMap_comp _ _ x) v').symm.trans <|
    (DFunLike.congr_fun (congrArg (fun f ↦ f.fiberMap x)
      (whitneySumTrivialIso (𝕜 := 𝕜) r₁ r₂).hom_inv_id) v').trans <|
    DFunLike.congr_fun (fiberMap_id _ x) v'

end Coherence

/-- Canonical isomorphism between the concrete variable-rank Whitney sum and the categorical binary
biproduct `A ⊞ D`. -/
noncomputable def whitneySumIsoBiprod (A D : FiniteRankAtlas 𝕜 X) :
    whitneySum A D ≅ A ⊞ D :=
  biprod.uniqueUpToIso A D (whitneyBiconeIsBilimit A D)

@[reassoc (attr := simp)]
theorem whitneySumIsoBiprod_hom_fst (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).hom ≫ biprod.fst = whitneyFst A D :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem whitneySumIsoBiprod_hom_snd (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).hom ≫ biprod.snd = whitneySnd A D :=
  biprod.lift_snd _ _

@[reassoc (attr := simp)]
theorem inl_whitneySumIsoBiprod_hom (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ (whitneySumIsoBiprod A D).hom = biprod.inl := by
  apply biprod.hom_ext <;> simp [Category.assoc]

@[reassoc (attr := simp)]
theorem inr_whitneySumIsoBiprod_hom (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ (whitneySumIsoBiprod A D).hom = biprod.inr := by
  apply biprod.hom_ext <;> simp [Category.assoc]

@[reassoc (attr := simp)]
theorem whitneySumIsoBiprod_inv_fst (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).inv ≫ whitneyFst A D = biprod.fst := by
  rw [Iso.inv_comp_eq, whitneySumIsoBiprod_hom_fst]

@[reassoc (attr := simp)]
theorem whitneySumIsoBiprod_inv_snd (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).inv ≫ whitneySnd A D = biprod.snd := by
  rw [Iso.inv_comp_eq, whitneySumIsoBiprod_hom_snd]

@[reassoc (attr := simp)]
theorem inl_whitneySumIsoBiprod_inv (A D : FiniteRankAtlas 𝕜 X) :
    biprod.inl ≫ (whitneySumIsoBiprod A D).inv = whitneyInl A D := by
  rw [Iso.comp_inv_eq, inl_whitneySumIsoBiprod_hom]

@[reassoc (attr := simp)]
theorem inr_whitneySumIsoBiprod_inv (A D : FiniteRankAtlas 𝕜 X) :
    biprod.inr ≫ (whitneySumIsoBiprod A D).inv = whitneyInr A D := by
  rw [Iso.comp_inv_eq, inr_whitneySumIsoBiprod_hom]

@[simp]
theorem rank_biprod (A D : FiniteRankAtlas 𝕜 X) :
    (A ⊞ D).rank = A.rank + D.rank :=
  (whitneySumIsoBiprod A D).symm.finiteRankAtlas_rank_eq.trans (rank_whitneySum A D)

/-- The constant-rank embedding `ofCore` preserves concrete Whitney sums up to canonical
isomorphism intertwining the projections and inclusions. -/
noncomputable def ofCoreWhitneySumIso (B B' : FiniteRankBundleCore 𝕜 X) :
    ofCore.obj (B.whitneySum B') ≅ whitneySum (ofCore.obj B) (ofCore.obj B') where
  hom := whitneyLift (ofCore.map (B.whitneyFst B')) (ofCore.map (B.whitneySnd B'))
  inv := whitneyDesc (ofCore.map (B.whitneyInl B')) (ofCore.map (B.whitneyInr B'))
  hom_inv_id := by
    rw [whitneyLift_desc, ← ofCore.map_comp, ← ofCore.map_comp, ← ofCore.map_add,
      FiniteRankBundleCore.whitney_total, ofCore.map_id]
  inv_hom_id := by
    apply whitneySum_hom_ext
    · apply whitneySum_hom_ext' <;> simp [← ofCore.map_comp]
    · apply whitneySum_hom_ext' <;> simp [← ofCore.map_comp]

@[reassoc (attr := simp)]
theorem ofCoreWhitneySumIso_hom_fst (B B' : FiniteRankBundleCore 𝕜 X) :
    (ofCoreWhitneySumIso B B').hom ≫ whitneyFst (ofCore.obj B) (ofCore.obj B') =
      ofCore.map (B.whitneyFst B') :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)]
theorem ofCoreWhitneySumIso_hom_snd (B B' : FiniteRankBundleCore 𝕜 X) :
    (ofCoreWhitneySumIso B B').hom ≫ whitneySnd (ofCore.obj B) (ofCore.obj B') =
      ofCore.map (B.whitneySnd B') :=
  whitneyLift_snd _ _

@[reassoc (attr := simp)]
theorem inl_ofCoreWhitneySumIso_hom (B B' : FiniteRankBundleCore 𝕜 X) :
    ofCore.map (B.whitneyInl B') ≫ (ofCoreWhitneySumIso B B').hom =
      whitneyInl (ofCore.obj B) (ofCore.obj B') := by
  apply whitneySum_hom_ext <;> simp [← ofCore.map_comp]

@[reassoc (attr := simp)]
theorem inr_ofCoreWhitneySumIso_hom (B B' : FiniteRankBundleCore 𝕜 X) :
    ofCore.map (B.whitneyInr B') ≫ (ofCoreWhitneySumIso B B').hom =
      whitneyInr (ofCore.obj B) (ofCore.obj B') := by
  apply whitneySum_hom_ext <;> simp [← ofCore.map_comp]

@[reassoc (attr := simp)]
theorem ofCoreWhitneySumIso_inv_fst (B B' : FiniteRankBundleCore 𝕜 X) :
    (ofCoreWhitneySumIso B B').inv ≫ ofCore.map (B.whitneyFst B') =
      whitneyFst (ofCore.obj B) (ofCore.obj B') := by
  rw [Iso.inv_comp_eq, ofCoreWhitneySumIso_hom_fst]

@[reassoc (attr := simp)]
theorem ofCoreWhitneySumIso_inv_snd (B B' : FiniteRankBundleCore 𝕜 X) :
    (ofCoreWhitneySumIso B B').inv ≫ ofCore.map (B.whitneySnd B') =
      whitneySnd (ofCore.obj B) (ofCore.obj B') := by
  rw [Iso.inv_comp_eq, ofCoreWhitneySumIso_hom_snd]

@[reassoc (attr := simp)]
theorem inl_ofCoreWhitneySumIso_inv (B B' : FiniteRankBundleCore 𝕜 X) :
    whitneyInl (ofCore.obj B) (ofCore.obj B') ≫ (ofCoreWhitneySumIso B B').inv =
      ofCore.map (B.whitneyInl B') := by
  rw [Iso.comp_inv_eq, inl_ofCoreWhitneySumIso_hom]

@[reassoc (attr := simp)]
theorem inr_ofCoreWhitneySumIso_inv (B B' : FiniteRankBundleCore 𝕜 X) :
    whitneyInr (ofCore.obj B) (ofCore.obj B') ≫ (ofCoreWhitneySumIso B B').inv =
      ofCore.map (B.whitneyInr B') := by
  rw [Iso.comp_inv_eq, inr_ofCoreWhitneySumIso_hom]

@[simp]
theorem fiberMap_ofCoreWhitneySumIso_hom (B B' : FiniteRankBundleCore 𝕜 X) (x : X) :
    (ofCoreWhitneySumIso B B').hom.fiberMap x = LinearMap.id := by
  dsimp only [ofCoreWhitneySumIso]
  rw [fiberMap_whitneyLift]
  apply LinearMap.ext
  intro v
  dsimp only [LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.id_apply]
  rw [fiberMap_ofCore_map, fiberMap_ofCore_map, FiniteRankBundleCore.fiberMap_whitneyFst,
    FiniteRankBundleCore.fiberMap_whitneySnd]
  exact (splitCoords (𝕜 := 𝕜) B.rank B'.rank).symm_apply_apply v

@[simp]
theorem fiberMap_ofCoreWhitneySumIso_inv (B B' : FiniteRankBundleCore 𝕜 X) (x : X) :
    (ofCoreWhitneySumIso B B').inv.fiberMap x = LinearMap.id := by
  apply LinearMap.ext
  intro v
  let v' : (ofCore.obj (B.whitneySum B')).Fiber x := v
  exact (congrArg ((ofCoreWhitneySumIso B B').inv.fiberMap x)
    (DFunLike.congr_fun (fiberMap_ofCoreWhitneySumIso_hom B B' x) v')).symm.trans <|
    (DFunLike.congr_fun (fiberMap_comp _ _ x) v').symm.trans <|
    (DFunLike.congr_fun (congrArg (fun f ↦ f.fiberMap x)
      (ofCoreWhitneySumIso B B').hom_inv_id) v').trans <|
    DFunLike.congr_fun (fiberMap_id _ x) v'

/-! ### Total-space fibre-product comparison -/

private noncomputable def whitneyFiberProdInv (A D : FiniteRankAtlas 𝕜 X)
    (pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}) :
    TotalSpace Unit (whitneySum A D).Fiber :=
  ⟨pq.1.1.proj,
    ((splitCoords (𝕜 := 𝕜) (A.rank pq.1.1.proj) (D.rank pq.1.1.proj)).symm
      (pq.1.1.2, fun i ↦ pq.1.2.2 (Fin.cast (congrArg D.rank pq.2) i)) :
        (whitneySum A D).Fiber pq.1.1.proj)⟩

private noncomputable def whitneyFiberProdEquiv (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃
      {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} where
  toFun p := ⟨((whitneyFst A D).totalSpaceMap p, (whitneySnd A D).totalSpaceMap p), by simp⟩
  invFun := whitneyFiberProdInv A D
  left_inv p := by
    rcases p with ⟨x, v⟩
    have hfst := Hom.totalSpaceMap_mk (whitneyFst A D) x v
    have hsnd := Hom.totalSpaceMap_mk (whitneySnd A D) x v
    have hp : (⟨((whitneyFst A D).totalSpaceMap ⟨x, v⟩, (whitneySnd A D).totalSpaceMap ⟨x, v⟩),
        by simp⟩ :
          {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}) =
        ⟨(⟨x, (whitneyFst A D).fiberMap x v⟩, ⟨x, (whitneySnd A D).fiberMap x v⟩), rfl⟩ :=
      Subtype.ext (Prod.ext hfst hsnd)
    dsimp only
    rw [hp]
    dsimp only [whitneyFiberProdInv]
    rw [fiberMap_whitneyFst, fiberMap_whitneySnd]
    exact congrArg (TotalSpace.mk' (E := (whitneySum A D).Fiber) Unit x)
      ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm_apply_apply v)
  right_inv pq := by
    rcases pq with ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, hproj⟩
    dsimp only at hproj
    subst hproj
    apply Subtype.ext
    dsimp only [whitneyFiberProdInv]
    exact Prod.ext
      ((Hom.totalSpaceMap_mk (whitneyFst A D) x₁ _).trans <| congrArg (TotalSpace.mk' _ _) <| by
        rw [fiberMap_whitneyFst]
        exact congrArg Prod.fst ((splitCoords (𝕜 := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply
          (u, fun i ↦ w (Fin.cast rfl i))))
      ((Hom.totalSpaceMap_mk (whitneySnd A D) x₁ _).trans <| congrArg (TotalSpace.mk' _ _) <| by
        rw [fiberMap_whitneySnd]
        exact (congrArg Prod.snd ((splitCoords (𝕜 := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply
          (u, fun i ↦ w (Fin.cast rfl i)))).trans
            (funext fun i ↦ congrArg w (congrFun (Fin.cast_refl _ rfl) i)))

private theorem continuous_whitneyFiberProdInv (A D : FiniteRankAtlas 𝕜 X) :
    Continuous (whitneyFiberProdInv A D) := by
  let c := A.rank.prodMk D.rank
  have hb : Continuous (fun pq :
      {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} ↦
        pq.1.1.proj) :=
    A.continuous_proj.comp (continuous_fst.comp continuous_subtype_val)
  -- Check continuity on each clopen joint rank bi-stratum `c x = (m, n)`.
  unfold whitneyFiberProdInv
  refine (continuous_mk_ofClopenCores_iff c hb
    (fun p ↦ (A.clopenPullCore c Prod.fst (fun _ ↦ rfl) p).whitneySum
      (D.clopenPullCore c Prod.snd (fun _ ↦ rfl) p)) _).2 fun ⟨m, n⟩ ↦ ?_
  let sub : C({x : X // c x = (m, n)}, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let A_p := A.clopenPullCore c Prod.fst (fun _ ↦ rfl) (m, n)
  let D_p := D.clopenPullCore c Prod.snd (fun _ ↦ rfl) (m, n)
  let baseMap : {pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
      pq.1.proj = pq.2.proj} // c pq.1.1.proj = (m, n)} → {x : X // c x = (m, n)} :=
    fun r ↦ ⟨r.1.1.1.proj, r.2⟩
  have hbase : Continuous baseMap := (hb.comp continuous_subtype_val).subtype_mk _
  -- Lift the two factors into the constant-rank core total spaces `A_p` and `D_p`.
  have hA := A.continuous_mk_pullCore_of_proj_eq sub m (fun x ↦ congrArg Prod.fst x.2) hbase
    (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))
    (fun _ ↦ rfl) (hrank := fun r ↦ (congrArg Prod.fst r.2).symm)
  have hD := D.continuous_mk_pullCore_of_proj_eq sub n (fun x ↦ congrArg Prod.snd x.2) hbase
    (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))
    (fun r ↦ r.1.2.symm)
    (hrank := fun r ↦ ((congrArg D.rank r.1.2).symm.trans (congrArg Prod.snd r.2)).symm)
  -- Combine into Mathlib's direct-sum bundle and transport to `(A_p.whitneySum D_p)`.
  have hprod : Continuous (fun r :
      {pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
        pq.1.proj = pq.2.proj} // c pq.1.1.proj = (m, n)} ↦
      (⟨baseMap r, (fun i : Fin m ↦ r.1.1.1.2 (Fin.cast (congrArg Prod.fst r.2).symm i),
        fun j : Fin n ↦ r.1.1.2.2
          (Fin.cast ((congrArg D.rank r.1.2).symm.trans (congrArg Prod.snd r.2)).symm j))⟩ :
            TotalSpace ((Fin m → 𝕜) × (Fin n → 𝕜)) (A_p.core.Fiber ×ᵇ D_p.core.Fiber))) := by
    rw [(FiberBundle.Prod.isInducing_diag (Fin m → 𝕜) A_p.core.Fiber
      (Fin n → 𝕜) D_p.core.Fiber).continuous_iff]
    exact hA.prodMk hD
  refine ((FiniteRankBundleCore.whitneySumTotalSpaceHomeomorph A_p D_p).symm.continuous.comp
    hprod).congr fun r ↦ ?_
  rcases r with ⟨⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, hproj⟩, hp⟩
  dsimp only [c, LocallyConstant.prodMk_apply] at hproj hp
  subst hproj
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
  dsimp only [Function.comp_apply, baseMap]
  rw [FiniteRankBundleCore.whitneySumTotalSpaceHomeomorph_symm_apply,
    FiniteRankBundleCore.whitneySumFiberEquiv_symm_apply]
  rfl

/-- The reconstructed total space of `whitneySum A D` is homeomorphic over `X` to the topological
fibre product of the reconstructed total spaces of `A` and `D` over `X`. -/
noncomputable def whitneySumFiberProdHomeomorph (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃ₜ
      {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} where
  toEquiv := whitneyFiberProdEquiv A D
  continuous_toFun :=
    ((whitneyFst A D).totalSpaceMap.continuous.prodMk
      (whitneySnd A D).totalSpaceMap.continuous).subtype_mk fun _ ↦ by simp
  continuous_invFun := continuous_whitneyFiberProdInv A D

@[simp]
theorem whitneySumFiberProdHomeomorph_apply (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumFiberProdHomeomorph A D p =
      ⟨((whitneyFst A D).totalSpaceMap p, (whitneySnd A D).totalSpaceMap p),
        ((whitneyFst A D).proj_totalSpaceMap p).trans
          ((whitneySnd A D).proj_totalSpaceMap p).symm⟩ :=
  (rfl)

@[simp]
theorem whitneySumFiberProdHomeomorph_symm_apply (A D : FiniteRankAtlas 𝕜 X)
    (x : X) (u : A.Fiber x) (w : D.Fiber x) :
    (whitneySumFiberProdHomeomorph A D).symm ⟨(⟨x, u⟩, ⟨x, w⟩), rfl⟩ =
      ⟨x, (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (u, w)⟩ :=
  (rfl)

end TauCeti.FiniteRankAtlas
