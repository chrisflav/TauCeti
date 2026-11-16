/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.BinaryBiproducts
public import TauCeti.CategoryTheory.Linear.Mat
public import TauCeti.CategoryTheory.Preadditive.Mat

/-!
# Dagger structure and orthogonal additive completion on `Mat_ C`

For a preadditive dagger category `C` with an additive dagger (`DaggerPreadditive C`), Mathlib's
matrix category `Mat_ C` inherits a dagger given by the conjugate transpose
`(dagger f) i j = dagger (f j i)`. This dagger is again additive, and conjugate-linear whenever
`C` is `DaggerLinear R`.

The standard finite biproducts in `Mat_ C` are orthogonal, giving `HasFiniteDaggerBiproducts
(Mat_ C)`, and every object of `Mat_ C` is unitarily isomorphic to the dagger biproduct of the
embeddings of its summands. Any additive dagger-preserving functor `F : C ⥤ D` into a preadditive
dagger category with finite dagger biproducts extends to an additive dagger-preserving functor
`Mat_.daggerLift F : Mat_ C ⥤ D` factoring `F` up to a pointwise unitary natural isomorphism.
This extension is unique up to a unique natural isomorphism, which is pointwise unitary whenever
the given comparison on `C` is pointwise unitary. When `C` already has finite dagger biproducts,
this yields an equivalence `Mat_ C ≌ C` with dagger-preserving functors and pointwise unitary
unit and counit isomorphisms.

## Main definitions and results

* `CategoryTheory.Mat_.instDaggerCategory`, `instDaggerPreadditive`, `instDaggerLinear`:
  conjugate-transpose dagger structure on `Mat_ C`.
* `CategoryTheory.Mat_.hasFiniteDaggerBiproducts`: `Mat_ C` has finite orthogonal biproducts.
* `CategoryTheory.Mat_.isoDaggerBiproductEmbedding`: unitary decomposition of every object of
  `Mat_ C` as a dagger biproduct of embedded objects of `C`.
* `CategoryTheory.Mat_.daggerLift`: extension of an additive dagger-preserving functor `C ⥤ D` to
  `Mat_ C ⥤ D`, together with `daggerLiftIsoLift`, `embeddingDaggerLiftIso`, and
  `daggerLiftUnique` (including unitarity and strict uniqueness).
* `CategoryTheory.Mat_.daggerEquivalenceSelf`: equivalence `Mat_ C ≌ C` when `C` already has
  finite dagger biproducts.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TauCeti

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

namespace Mat_

/-- Finite sums of morphisms in `Mat_ C` are computed entrywise. -/
@[simp] theorem sum_apply {ι : Type*} {M N : Mat_ C} (s : Finset ι) (f : ι → (M ⟶ N))
    (i : M.ι) (j : N.ι) : (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j := by
  let eval : (M ⟶ N) →+ (M.X i ⟶ N.X j) :=
    { toFun := fun g => g i j
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum eval f s

section DaggerStructure

variable [DaggerCategory C] [DaggerPreadditive C]

/-- The conjugate-transpose dagger on `Mat_ C`: `(dagger f) i j = dagger (f j i)`. -/
instance instDaggerCategory : DaggerCategory (Mat_ C) where
  dagger f i j := TauCeti.dagger (f j i)
  dagger_id M := by
    classical
    ext i j
    change TauCeti.dagger ((𝟙 M) j i) = (𝟙 M) i j
    rw [id_apply, id_apply]
    by_cases h : j = i
    · subst h
      simp
    · have h' : i ≠ j := Ne.symm h
      simp [h, h']
  dagger_comp f g := by
    ext i k
    change TauCeti.dagger ((f ≫ g) k i) =
      ∑ j, TauCeti.dagger (g j i) ≫ TauCeti.dagger (f k j)
    simp [comp_apply]
  dagger_dagger f := by
    ext i j
    exact dagger_dagger (f i j)

/-- The dagger on `Mat_ C` acts by taking the transpose and applying the dagger entrywise. -/
@[simp] theorem dagger_apply {M N : Mat_ C} (f : M ⟶ N) (i : N.ι) (j : M.ι) :
    (TauCeti.dagger f) i j = TauCeti.dagger (f j i) := (rfl)

/-- The conjugate-transpose dagger on `Mat_ C` is additive. -/
instance instDaggerPreadditive : DaggerPreadditive (Mat_ C) where
  dagger_add f g := by
    ext i j
    simp

/-- The conjugate-transpose dagger on `Mat_ C` is conjugate-linear when `C` is `DaggerLinear R`. -/
instance instDaggerLinear {R : Type w} [Semiring R] [Star R] [Linear R C] [DaggerLinear R C] :
    DaggerLinear R (Mat_ C) where
  dagger_smul r f := by
    ext i j
    simp

/-- The embedding `C ⥤ Mat_ C` preserves daggers. -/
instance instPreservesDaggerEmbedding : (embedding C).PreservesDagger where
  map_dagger f := by
    ext ⟨⟩ ⟨⟩
    rfl

/-- A monomial isomorphism `Mat_.isoOfEquiv e φ` is unitary whenever each entry `φ i` is unitary. -/
theorem isUnitary_isoOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i))
    (hφ : ∀ i, IsUnitary (φ i).hom) :
    IsUnitary (isoOfEquiv e φ).hom := by
  classical
  refine (isoOfEquiv e φ).isUnitary_hom_iff.mpr ?_
  ext j i
  rw [dagger_apply, isoOfEquiv_hom_apply, isoOfEquiv_inv_apply]
  by_cases h : e i = j
  · simp [h, (φ i).dagger_hom_eq_inv_of_isUnitary (hφ i)]
  · simp [h]

private abbrev sigmaObj {J : Type} [Fintype J] (f : J → Mat_ C) : Mat_ C :=
  ⟨Σ j, (f j).ι, fun p => (f p.1).X p.2⟩

open scoped Classical in
private def sigmaProj {J : Type} [Fintype J] (f : J → Mat_ C) (j : J) :
    sigmaObj f ⟶ f j :=
  fun p y => if h : p = ⟨j, y⟩ then eqToHom (congrArg (sigmaObj f).X h) else 0

open scoped Classical in
private def sigmaIncl {J : Type} [Fintype J] (f : J → Mat_ C) (j : J) :
    f j ⟶ sigmaObj f :=
  fun y p => if h : p = ⟨j, y⟩ then eqToHom (congrArg (sigmaObj f).X h.symm) else 0

open scoped Classical in
/-- The explicit orthogonal sigma-type bicone for a finite family in `Mat_ C`. -/
private def sigmaBicone {J : Type} [Fintype J] (f : J → Mat_ C) : Bicone f where
  pt := sigmaObj f
  π := sigmaProj f
  ι := sigmaIncl f
  ι_π j j' := by
    ext x y
    rw [comp_apply]
    have hsum :
        (∑ p : Σ k, (f k).ι, sigmaIncl f j x p ≫ sigmaProj f j' p y) =
          sigmaIncl f j x ⟨j, x⟩ ≫ sigmaProj f j' ⟨j, x⟩ y := by
      refine Finset.sum_eq_single (⟨j, x⟩ : Σ k, (f k).ι) ?_
        (fun h => (h (Finset.mem_univ _)).elim)
      intro p _ hp
      simp only [sigmaIncl, dite_eq_right hp, Limits.zero_comp]
    rw [hsum]
    change _ = (if h : j = j' then eqToHom (congrArg f h) else 0) x y
    simp only [sigmaIncl, sigmaProj, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    by_cases hj : j = j'
    · subst hj
      rw [dite_eq_left rfl, eqToHom_refl, id_apply]
      by_cases hx : x = y
      · subst hx
        simp
      · have hne : (⟨j, x⟩ : Σ k, (f k).ι) ≠ ⟨j, y⟩ :=
          fun h => hx (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
        rw [dite_eq_right hne, dite_eq_right hx]
    · have hne : (⟨j, x⟩ : Σ k, (f k).ι) ≠ ⟨j', y⟩ := fun h => hj (congrArg Sigma.fst h)
      rw [dite_eq_right hj, dite_eq_right hne, zero_apply]

open scoped Classical in
private theorem sigmaBicone_isOrthogonal {J : Type} [Fintype J] (f : J → Mat_ C) :
    (sigmaBicone f).IsOrthogonal :=
  (Bicone.isOrthogonal_iff _).mpr fun j => by
    change TauCeti.dagger (sigmaIncl f j) = sigmaProj f j
    ext p y
    rw [dagger_apply]
    simp only [sigmaIncl, sigmaProj]
    by_cases h : p = ⟨j, y⟩
    · rw [dite_eq_left h, dite_eq_left h, dagger_eqToHom]
    · rw [dite_eq_right h, dite_eq_right h, dagger_zero]

open scoped Classical in
omit [DaggerCategory C] [DaggerPreadditive C] in
private theorem sigmaBicone_total {J : Type} [Fintype J] (f : J → Mat_ C) :
    ∑ j : J, (sigmaBicone f).π j ≫ (sigmaBicone f).ι j = 𝟙 (sigmaBicone f).pt := by
  change ∑ j : J, sigmaProj f j ≫ sigmaIncl f j = 𝟙 (sigmaObj f)
  ext p q
  rw [sum_apply]
  have h1 :
      (∑ j : J, (sigmaProj f j ≫ sigmaIncl f j) p q) =
      (sigmaProj f p.1 ≫ sigmaIncl f p.1) p q := by
    refine Finset.sum_eq_single p.1 ?_ (fun h => (h (Finset.mem_univ _)).elim)
    intro j _ hj
    rw [comp_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    have hne : p ≠ ⟨j, y⟩ := fun h => hj (congrArg Sigma.fst h).symm
    simp only [sigmaProj, dite_eq_right hne, Limits.zero_comp]
  rw [h1, comp_apply]
  have h2 :
      (∑ y : (f p.1).ι, sigmaProj f p.1 p y ≫ sigmaIncl f p.1 y q) =
      sigmaProj f p.1 p p.2 ≫ sigmaIncl f p.1 p.2 q := by
    refine Finset.sum_eq_single p.2 ?_ (fun h => (h (Finset.mem_univ _)).elim)
    intro y _ hy
    have hne : p ≠ ⟨p.1, y⟩ := fun h => hy (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    simp only [sigmaProj, dite_eq_right hne, Limits.zero_comp]
  rw [h2, id_apply]
  cases p with
  | mk j y =>
    simp only [sigmaProj, sigmaIncl, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    by_cases h : (⟨j, y⟩ : Σ k, (f k).ι) = q
    · subst h
      rw [dite_eq_left rfl]
    · have h' : q ≠ ⟨j, y⟩ := Ne.symm h
      rw [dite_eq_right h', dite_eq_right h]

/-- The matrix category `Mat_ C` has finite orthogonal biproducts. -/
instance hasFiniteDaggerBiproducts : HasFiniteDaggerBiproducts (Mat_ C) where
  out _ :=
    { has_daggerBiproduct := fun f =>
        hasDaggerBiproduct_of_total (sigmaBicone f) (sigmaBicone_isOrthogonal f)
          (sigmaBicone_total f) }

/-- The matrix category `Mat_ C` has binary orthogonal biproducts. -/
instance hasBinaryDaggerBiproducts : HasBinaryDaggerBiproducts (Mat_ C) :=
  hasBinaryDaggerBiproducts_of_finite_daggerBiproducts (Mat_ C)

open scoped Classical in
/-- The projection row from `M : Mat_ C` to its `i`-th embedded summand. -/
private def projRow (M : Mat_ C) (i : M.ι) : M ⟶ (embedding C).obj (M.X i) :=
  fun j _ => if h : j = i then eqToHom (congrArg M.X h) else 0

open scoped Classical in
/-- The inclusion column from the `i`-th embedded summand into `M : Mat_ C`. -/
private def inclCol (M : Mat_ C) (i : M.ι) : (embedding C).obj (M.X i) ⟶ M :=
  fun _ k => if h : i = k then eqToHom (congrArg M.X h) else 0

open scoped Classical in
private theorem dagger_projRow (M : Mat_ C) (i : M.ι) :
    TauCeti.dagger (projRow M i) = inclCol M i := by
  ext u k
  rw [dagger_apply]
  change TauCeti.dagger (if h : k = i then eqToHom (congrArg M.X h) else 0) =
    if h : i = k then eqToHom (congrArg M.X h) else 0
  by_cases h : k = i
  · subst h
    simp
  · have h' : i ≠ k := Ne.symm h
    simp [h, h']

/-- Every object `M : Mat_ C` is canonically isomorphic to the dagger biproduct of the embeddings
of its summands. -/
def isoDaggerBiproductEmbedding (M : Mat_ C) :
    M ≅ daggerBiproduct fun i => (embedding C).obj (M.X i) where
  hom := daggerBiproduct.lift (projRow M)
  inv := daggerBiproduct.desc (inclCol M)
  hom_inv_id := by
    classical
    rw [daggerBiproduct.lift_desc]
    ext j k
    rw [sum_apply, id_apply]
    rw [Finset.sum_eq_single j]
    · rw [comp_apply, Fintype.sum_unique]
      change (if h : j = j then eqToHom (congrArg M.X h) else 0) ≫
          (if h : j = k then eqToHom (congrArg M.X h) else 0) = _
      rw [dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    · intro i _ hi
      rw [comp_apply, Fintype.sum_unique]
      change (if h : j = i then eqToHom (congrArg M.X h) else 0) ≫ _ = 0
      rw [dite_eq_right (Ne.symm hi)]
      exact Limits.zero_comp
    · intro h
      exact (h (Finset.mem_univ _)).elim
  inv_hom_id := by
    classical
    apply daggerBiproduct.hom_ext'
    intro i
    apply daggerBiproduct.hom_ext
    intro j
    simp only [Category.id_comp, Category.assoc, daggerBiproduct.lift_π,
      daggerBiproduct.ι_desc_assoc, daggerBiproduct.ι_π]
    ext u v
    rw [comp_apply, Finset.sum_eq_single i]
    · change (if h : i = i then eqToHom (congrArg M.X h) else 0) ≫
          (if h : i = j then eqToHom (congrArg M.X h) else 0) = _
      rw [dite_eq_left rfl, eqToHom_refl, Category.id_comp]
      by_cases h : i = j
      · subst h
        have huv : u = v := Subsingleton.elim u v
        subst huv
        rw [dite_eq_left rfl, dite_eq_left rfl, eqToHom_refl, eqToHom_refl, id_apply_self]
        rfl
      · rw [dite_eq_right h, dite_eq_right h, zero_apply]
        rfl
    · intro k _ hk
      change (if h : i = k then eqToHom (congrArg M.X h) else 0) ≫ _ = 0
      rw [dite_eq_right (Ne.symm hk)]
      exact Limits.zero_comp
    · intro h
      exact (h (Finset.mem_univ _)).elim

open scoped Classical in
/-- Projecting `isoDaggerBiproductEmbedding M` onto summand `i` gives the `i`-th coordinate row. -/
@[reassoc (attr := simp)] theorem isoDaggerBiproductEmbedding_hom_π (M : Mat_ C) (i : M.ι) :
    (isoDaggerBiproductEmbedding M).hom ≫
      daggerBiproduct.π (fun j => (embedding C).obj (M.X j)) i =
      fun j _ => if h : j = i then eqToHom (congrArg M.X h) else 0 :=
  daggerBiproduct.lift_π _ i

open scoped Classical in
/-- Composing the `i`-th inclusion with `(isoDaggerBiproductEmbedding M).inv` gives the `i`-th
coordinate column. -/
@[reassoc (attr := simp)] theorem ι_isoDaggerBiproductEmbedding_inv (M : Mat_ C) (i : M.ι) :
    daggerBiproduct.ι (fun j => (embedding C).obj (M.X j)) i ≫
      (isoDaggerBiproductEmbedding M).inv =
      fun _ k => if h : i = k then eqToHom (congrArg M.X h) else 0 :=
  daggerBiproduct.ι_desc _ i

/-- The canonical decomposition `isoDaggerBiproductEmbedding M` is unitary. -/
theorem isUnitary_isoDaggerBiproductEmbedding (M : Mat_ C) :
    IsUnitary (isoDaggerBiproductEmbedding M).hom :=
  (isoDaggerBiproductEmbedding M).isUnitary_hom_iff.mpr <| by
    change TauCeti.dagger (daggerBiproduct.lift (projRow M)) = daggerBiproduct.desc (inclCol M)
    rw [daggerBiproduct.dagger_lift]
    congr 1
    funext i
    exact dagger_projRow M i

section MapMat

variable {D : Type u₂} [Category.{v₁} D] [Preadditive D] [DaggerCategory D] [DaggerPreadditive D]

/-- The induced functor `F.mapMat_ : Mat_ C ⥤ Mat_ D` preserves daggers when `F` does. -/
instance instPreservesDaggerMapMat_ (F : C ⥤ D) [F.Additive] [F.PreservesDagger] :
    F.mapMat_.PreservesDagger where
  map_dagger f := by
    ext i j
    exact F.map_dagger (f j i)

end MapMat

end DaggerStructure

section Lift

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [DaggerCategory D]
  [HasFiniteDaggerBiproducts D]

/-- Extension of an additive functor `F : C ⥤ D` to `Mat_ C ⥤ D` using chosen dagger biproducts in
`D`. -/
@[expose] def daggerLift (F : C ⥤ D) [F.Additive] : Mat_ C ⥤ D where
  obj M := daggerBiproduct fun i => F.obj (M.X i)
  map f := daggerBiproduct.matrix fun i j => F.map (f i j)
  map_id M := by
    classical
    apply daggerBiproduct.hom_ext'
    intro i
    apply daggerBiproduct.hom_ext
    intro j
    simp only [Category.comp_id, daggerBiproduct.ι_π, id_apply]
    rw [Category.assoc, daggerBiproduct.matrix_π, daggerBiproduct.ι_desc]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  map_comp f g := by
    rw [daggerBiproduct.matrix_comp_matrix]
    apply daggerBiproduct.hom_ext'
    intro i
    apply daggerBiproduct.hom_ext
    intro k
    simp [comp_apply, F.map_sum]

/-- The object action of `daggerLift F`. -/
@[simp] theorem daggerLift_obj (F : C ⥤ D) [F.Additive] (M : Mat_ C) :
    (daggerLift F).obj M = daggerBiproduct fun i => F.obj (M.X i) := (rfl)

/-- The morphism action of `daggerLift F`. -/
@[simp] theorem daggerLift_map (F : C ⥤ D) [F.Additive] {M N : Mat_ C} (f : M ⟶ N) :
    (daggerLift F).map f = daggerBiproduct.matrix fun i j => F.map (f i j) := (rfl)

/-- `Mat_.daggerLift F` is additive. -/
instance daggerLift_additive (F : C ⥤ D) [F.Additive] : (daggerLift F).Additive where
  map_add {M N} f g := by
    simp only [daggerLift_map, add_apply, F.map_add]
    exact daggerBiproduct.matrix_add (fun i j => F.map (f i j)) (fun i j => F.map (g i j))

/-- `Mat_.daggerLift F` is `R`-linear when `F` is `R`-linear. -/
instance daggerLift_linear {R : Type w} [Semiring R] [Linear R C] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] : (daggerLift F).Linear R where
  map_smul f r := by
    simp only [daggerLift_map, smul_apply, F.map_smul]
    exact daggerBiproduct.matrix_smul r (fun i j => F.map (f i j))

/-- Canonical natural isomorphism `embedding C ⋙ daggerLift F ≅ F`. -/
def embeddingDaggerLiftIso (F : C ⥤ D) [F.Additive] : embedding C ⋙ daggerLift F ≅ F :=
  NatIso.ofComponents
    (fun X =>
      { hom := daggerBiproduct.π (fun i => F.obj (((embedding C).obj X).X i)) default
        inv := daggerBiproduct.ι (fun i => F.obj (((embedding C).obj X).X i)) default
        hom_inv_id := by
          apply daggerBiproduct.hom_ext'
          intro u
          obtain rfl : u = default := Subsingleton.elim u default
          change daggerBiproduct.ι (fun i => F.obj (((embedding C).obj X).X i)) default ≫
              daggerBiproduct.π (fun i => F.obj (((embedding C).obj X).X i)) default ≫
                daggerBiproduct.ι (fun i => F.obj (((embedding C).obj X).X i)) default =
            daggerBiproduct.ι (fun i => F.obj (((embedding C).obj X).X i)) default ≫
              𝟙 (daggerBiproduct fun i => F.obj (((embedding C).obj X).X i))
          rw [daggerBiproduct.ι_π_self_assoc, Category.comp_id]
        inv_hom_id := daggerBiproduct.ι_π_self _ default })
    fun {X Y} f => by
      apply daggerBiproduct.hom_ext'
      intro u
      obtain rfl : u = default := Subsingleton.elim u default
      change daggerBiproduct.ι (fun i => F.obj (((embedding C).obj X).X i)) default ≫
          (daggerBiproduct.matrix fun i j => F.map (((embedding C).map f) i j)) ≫
            daggerBiproduct.π (fun i => F.obj (((embedding C).obj Y).X i)) default =
        daggerBiproduct.ι (fun i => F.obj (((embedding C).obj X).X i)) default ≫
          daggerBiproduct.π (fun i => F.obj (((embedding C).obj X).X i)) default ≫ F.map f
      rw [daggerBiproduct.matrix_π, daggerBiproduct.ι_desc, daggerBiproduct.ι_π_self_assoc]
      rfl

/-- Forward component of `embeddingDaggerLiftIso F`. -/
@[simp] theorem embeddingDaggerLiftIso_hom_app (F : C ⥤ D) [F.Additive] (X : C) :
    (embeddingDaggerLiftIso F).hom.app X =
      daggerBiproduct.π (fun i => F.obj (((embedding C).obj X).X i)) default := (rfl)

/-- Inverse component of `embeddingDaggerLiftIso F`. -/
@[simp] theorem embeddingDaggerLiftIso_inv_app (F : C ⥤ D) [F.Additive] (X : C) :
    (embeddingDaggerLiftIso F).inv.app X =
      daggerBiproduct.ι (fun i => F.obj (((embedding C).obj X).X i)) default := (rfl)

/-- Every component of `embeddingDaggerLiftIso F` is unitary. -/
theorem isUnitary_embeddingDaggerLiftIso (F : C ⥤ D) [F.Additive] (X : C) :
    IsUnitary ((embeddingDaggerLiftIso F).app X).hom :=
  ((embeddingDaggerLiftIso F).app X).isUnitary_hom_iff.mpr (daggerBiproduct.dagger_π _ default)

section DaggerLift

variable [DaggerCategory C] [DaggerPreadditive C]

/-- `Mat_.daggerLift F` preserves daggers when `F` does. -/
instance daggerLift_preservesDagger (F : C ⥤ D) [F.Additive] [F.PreservesDagger] :
    (daggerLift F).PreservesDagger where
  map_dagger f := by
    simp only [daggerLift_map, dagger_apply, F.map_dagger]
    exact (daggerBiproduct.dagger_matrix (fun i j => F.map (f i j))).symm

/-- Every additive functor `L : Mat_ C ⥤ D` sends `M` to the dagger biproduct of the images of its
embedded summands (unitarily when `L` preserves daggers). -/
def additiveObjIsoDaggerBiproduct (L : Mat_ C ⥤ D) [L.Additive] (M : Mat_ C) :
    L.obj M ≅ daggerBiproduct fun i => L.obj ((embedding C).obj (M.X i)) :=
  L.mapIso (isoDaggerBiproductEmbedding M) ≪≫ L.mapDaggerBiproduct _

/-- The decomposition isomorphism `additiveObjIsoDaggerBiproduct` is unitary when `L` preserves
daggers. -/
theorem isUnitary_additiveObjIsoDaggerBiproduct (L : Mat_ C ⥤ D) [L.Additive] [L.PreservesDagger]
    (M : Mat_ C) :
    IsUnitary (additiveObjIsoDaggerBiproduct L M).hom :=
  (L.map_isUnitary (isUnitary_isoDaggerBiproductEmbedding M)).comp
    (L.isUnitary_mapDaggerBiproduct _)

/-- Projecting `additiveObjIsoDaggerBiproduct` onto summand `i`. -/
@[reassoc (attr := simp)] theorem additiveObjIsoDaggerBiproduct_hom_π (L : Mat_ C ⥤ D)
    [L.Additive] (M : Mat_ C) (i : M.ι) :
    (additiveObjIsoDaggerBiproduct L M).hom ≫
      daggerBiproduct.π (fun j => L.obj ((embedding C).obj (M.X j))) i =
      L.map ((isoDaggerBiproductEmbedding M).hom ≫ daggerBiproduct.π _ i) := by
  simp [additiveObjIsoDaggerBiproduct, ← L.map_comp]

/-- Including summand `i` into `(additiveObjIsoDaggerBiproduct L M).inv`. -/
@[reassoc (attr := simp)] theorem ι_additiveObjIsoDaggerBiproduct_inv (L : Mat_ C ⥤ D)
    [L.Additive] (M : Mat_ C) (i : M.ι) :
    daggerBiproduct.ι (fun j => L.obj ((embedding C).obj (M.X j))) i ≫
      (additiveObjIsoDaggerBiproduct L M).inv =
      L.map (daggerBiproduct.ι _ i ≫ (isoDaggerBiproductEmbedding M).inv) := by
  simp [additiveObjIsoDaggerBiproduct, ← L.map_comp]

/-- Naturality of `additiveObjIsoDaggerBiproduct` with respect to matrix morphisms. -/
@[reassoc] theorem additiveObjIsoDaggerBiproduct_naturality (L : Mat_ C ⥤ D)
    [L.Additive] {M N : Mat_ C} (f : M ⟶ N) :
    L.map f ≫ (additiveObjIsoDaggerBiproduct L N).hom =
      (additiveObjIsoDaggerBiproduct L M).hom ≫
        daggerBiproduct.matrix fun i j => L.map ((embedding C).map (f i j)) := by
  classical
  apply daggerBiproduct.hom_ext
  intro j
  rw [Category.assoc, additiveObjIsoDaggerBiproduct_hom_π, ← L.map_comp]
  rw [← cancel_epi (additiveObjIsoDaggerBiproduct L M).inv, Category.assoc,
    Iso.inv_hom_id_assoc]
  apply daggerBiproduct.hom_ext'
  intro i
  rw [ι_additiveObjIsoDaggerBiproduct_inv_assoc, ← L.map_comp,
    daggerBiproduct.matrix_π, daggerBiproduct.ι_desc]
  congr 1
  ext u v
  let ιi : (embedding C).obj (M.X i) ⟶ M :=
    daggerBiproduct.ι (fun k => (embedding C).obj (M.X k)) i ≫ (isoDaggerBiproductEmbedding M).inv
  let πj : N ⟶ (embedding C).obj (N.X j) :=
    (isoDaggerBiproductEmbedding N).hom ≫ daggerBiproduct.π (fun k => (embedding C).obj (N.X k)) j
  change (ιi ≫ f ≫ πj) u v = ((embedding C).map (f i j)) u v
  rw [comp_apply, Finset.sum_eq_single i]
  · rw [comp_apply, Finset.sum_eq_single j]
    · have h1 : ιi u i = 𝟙 (M.X i) :=
        (congrFun (congrFun (ι_isoDaggerBiproductEmbedding_inv M i) u) i).trans (by simp; rfl)
      have h2 : πj j v = 𝟙 (N.X j) :=
        (congrFun (congrFun (isoDaggerBiproductEmbedding_hom_π N j) j) v).trans (by simp; rfl)
      rw [h1, h2]
      change 𝟙 (M.X i) ≫ f i j ≫ 𝟙 (N.X j) = f i j
      simp
    · intro k _ hk
      have h2 : πj k v = 0 :=
        (congrFun (congrFun (isoDaggerBiproductEmbedding_hom_π N j) k) v).trans (by simp [hk]; rfl)
      rw [h2, Limits.comp_zero]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · intro k _ hk
    have h1 : ιi u k = 0 :=
      (congrFun (congrFun (ι_isoDaggerBiproductEmbedding_inv M i) u) k).trans
        (by simp [Ne.symm hk]; rfl)
    rw [h1, Limits.zero_comp]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Any additive functor `L : Mat_ C ⥤ D` equipped with `α : embedding C ⋙ L ≅ F` is canonically
isomorphic to `daggerLift F`. -/
def daggerLiftUnique (F : C ⥤ D) [F.Additive]
    (L : Mat_ C ⥤ D) [L.Additive] (α : embedding C ⋙ L ≅ F) :
    L ≅ daggerLift F :=
  NatIso.ofComponents
    (fun M =>
      additiveObjIsoDaggerBiproduct L M ≪≫
        daggerBiproduct.mapIso fun i => α.app (M.X i))
    fun {M N} f => by
      change L.map f ≫
          ((additiveObjIsoDaggerBiproduct L N).hom ≫
            (daggerBiproduct.mapIso fun i => α.app (N.X i)).hom) =
        ((additiveObjIsoDaggerBiproduct L M).hom ≫
            (daggerBiproduct.mapIso fun i => α.app (M.X i)).hom) ≫
          daggerBiproduct.matrix fun i j => F.map (f i j)
      simp only [daggerBiproduct.mapIso_hom]
      rw [additiveObjIsoDaggerBiproduct_naturality_assoc, daggerBiproduct.matrix_map,
        Category.assoc, daggerBiproduct.map_matrix]
      congr 1
      apply daggerBiproduct.hom_ext'
      intro i
      apply daggerBiproduct.hom_ext
      intro j
      simp only [Category.assoc, daggerBiproduct.matrix_π, daggerBiproduct.ι_desc]
      exact α.hom.naturality (f i j)

/-- Forward component of `daggerLiftUnique F L α`. -/
@[simp] theorem daggerLiftUnique_hom_app (F : C ⥤ D) [F.Additive]
    (L : Mat_ C ⥤ D) [L.Additive] (α : embedding C ⋙ L ≅ F) (M : Mat_ C) :
    (daggerLiftUnique F L α).hom.app M =
      (additiveObjIsoDaggerBiproduct L M).hom ≫
        daggerBiproduct.map fun i => α.hom.app (M.X i) := by
  change (additiveObjIsoDaggerBiproduct L M).hom ≫
    (daggerBiproduct.mapIso fun i => α.app (M.X i)).hom = _
  rw [daggerBiproduct.mapIso_hom]
  rfl

/-- Restricting `daggerLiftUnique F L α` along `embedding C` and composing with
`embeddingDaggerLiftIso F` recovers `α`. -/
theorem daggerLiftUnique_hom_app_embedding (F : C ⥤ D) [F.Additive]
    (L : Mat_ C ⥤ D) [L.Additive] (α : embedding C ⋙ L ≅ F) (X : C) :
    (daggerLiftUnique F L α).hom.app ((embedding C).obj X) ≫
      (embeddingDaggerLiftIso F).hom.app X = α.hom.app X := by
  have hid :
      (isoDaggerBiproductEmbedding ((embedding C).obj X)).hom ≫
        daggerBiproduct.π (fun j => (embedding C).obj (((embedding C).obj X).X j)) default =
        𝟙 ((embedding C).obj X) := by
    ext u v
    obtain rfl : u = default := Subsingleton.elim u default
    obtain rfl : v = default := Subsingleton.elim v default
    exact (congrFun (congrFun (isoDaggerBiproductEmbedding_hom_π ((embedding C).obj X) default)
      default) default).trans (by
        rw [dite_eq_left rfl]
        change 𝟙 X = 𝟙 ((embedding C).obj X) default default
        rw [id_apply, dite_eq_left rfl]
        rfl)
  rw [daggerLiftUnique_hom_app, embeddingDaggerLiftIso_hom_app]
  have hL :
      L.map ((isoDaggerBiproductEmbedding ((embedding C).obj X)).hom ≫
        daggerBiproduct.π (fun j => (embedding C).obj (((embedding C).obj X).X j)) default) =
        𝟙 (L.obj ((embedding C).obj X)) :=
    (congrArg L.map hid).trans (L.map_id _)
  have hcomp :
      ((additiveObjIsoDaggerBiproduct L ((embedding C).obj X)).hom ≫
        daggerBiproduct.map fun i => α.hom.app (((embedding C).obj X).X i)) ≫
        daggerBiproduct.π (fun i => F.obj (((embedding C).obj X).X i)) default =
        L.map ((isoDaggerBiproductEmbedding ((embedding C).obj X)).hom ≫
          daggerBiproduct.π (fun j => (embedding C).obj (((embedding C).obj X).X j)) default) ≫
          α.hom.app (((embedding C).obj X).X default) := by
    rw [Category.assoc, daggerBiproduct.map_π, additiveObjIsoDaggerBiproduct_hom_π_assoc]
  exact hcomp.trans ((congrArg (· ≫ α.hom.app X) hL).trans (Category.id_comp _))

/-- `daggerLiftUnique F L α` is pointwise unitary whenever `L` preserves daggers and `α` is
pointwise unitary. -/
theorem isUnitary_daggerLiftUnique (F : C ⥤ D) [F.Additive]
    (L : Mat_ C ⥤ D) [L.Additive] [L.PreservesDagger] (α : embedding C ⋙ L ≅ F)
    (hα : ∀ X, IsUnitary (α.app X).hom) (M : Mat_ C) :
    IsUnitary ((daggerLiftUnique F L α).app M).hom :=
  (isUnitary_additiveObjIsoDaggerBiproduct L M).comp
    (daggerBiproduct.isUnitary_mapIso _ fun i => hα (M.X i))

/-- Strict uniqueness of the comparison transformation `L ⟶ daggerLift F`: any natural
transformation matching `α` on `embedding C` equals `(daggerLiftUnique F L α).hom`. -/
theorem eq_daggerLiftUnique_hom (F : C ⥤ D) [F.Additive]
    (L : Mat_ C ⥤ D) [L.Additive] (α : embedding C ⋙ L ≅ F)
    (β : L ⟶ daggerLift F)
    (hβ : ∀ X, β.app ((embedding C).obj X) ≫ (embeddingDaggerLiftIso F).hom.app X = α.hom.app X) :
    β = (daggerLiftUnique F L α).hom := by
  classical
  ext M
  apply daggerBiproduct.hom_ext
  intro i
  let p : M ⟶ (embedding C).obj (M.X i) :=
    (isoDaggerBiproductEmbedding M).hom ≫
      daggerBiproduct.π (fun j => (embedding C).obj (M.X j)) i
  have hFp :
      (daggerLift F).map p ≫ (embeddingDaggerLiftIso F).hom.app (M.X i) =
        daggerBiproduct.π (fun j => F.obj (M.X j)) i := by
    apply daggerBiproduct.hom_ext'
    intro j
    rw [daggerLift_map, embeddingDaggerLiftIso_hom_app]
    have hmat :
        (daggerBiproduct.matrix fun a b => F.map (p a b)) ≫
          daggerBiproduct.π (fun b => F.obj (((embedding C).obj (M.X i)).X b)) default =
          daggerBiproduct.desc (fun a => F.map (p a default)) :=
      daggerBiproduct.matrix_π (fun a b => F.map (p a b)) default
    have hstep :
        daggerBiproduct.ι (fun a => F.obj (M.X a)) j ≫
          ((daggerBiproduct.matrix fun a b => F.map (p a b)) ≫
            daggerBiproduct.π (fun b => F.obj (((embedding C).obj (M.X i)).X b)) default) =
          F.map (p j default) := by
      rw [hmat, daggerBiproduct.ι_desc]
    refine hstep.trans ?_
    rw [daggerBiproduct.ι_π]
    by_cases h : j = i
    · subst h
      have hp : p j default = 𝟙 (M.X j) :=
        (congrFun (congrFun (isoDaggerBiproductEmbedding_hom_π M j) j) default).trans (by simp; rfl)
      simp only [↓reduceDIte, eqToHom_refl]
      exact (congrArg F.map hp).trans (F.map_id (M.X j))
    · have hp : p j default = 0 :=
        (congrFun (congrFun (isoDaggerBiproductEmbedding_hom_π M i) j) default).trans
          (by simp [h]; rfl)
      simp only [h, ↓reduceDIte]
      exact (congrArg F.map hp).trans (F.map_zero _ _)
  have hrhs :
      (daggerLiftUnique F L α).hom.app M ≫ daggerBiproduct.π (fun j => F.obj (M.X j)) i =
        (additiveObjIsoDaggerBiproduct L M).hom ≫
          daggerBiproduct.π (fun j => L.obj ((embedding C).obj (M.X j))) i ≫ α.hom.app (M.X i) :=
    (congrArg (· ≫ daggerBiproduct.π (fun j => F.obj (M.X j)) i)
      (daggerLiftUnique_hom_app F L α M)).trans (by rw [Category.assoc, daggerBiproduct.map_π])
  calc
    β.app M ≫ daggerBiproduct.π (fun j => F.obj (M.X j)) i
        = β.app M ≫ (daggerLift F).map p ≫ (embeddingDaggerLiftIso F).hom.app (M.X i) := by
          rw [hFp]
    _ = L.map p ≫ β.app ((embedding C).obj (M.X i)) ≫ (embeddingDaggerLiftIso F).hom.app (M.X i) :=
          by rw [← Category.assoc, ← β.naturality p, Category.assoc]
    _ = L.map p ≫ α.hom.app (M.X i) := by rw [hβ]
    _ = (additiveObjIsoDaggerBiproduct L M).hom ≫
          daggerBiproduct.π (fun j => L.obj ((embedding C).obj (M.X j))) i ≫ α.hom.app (M.X i) := by
          rw [← additiveObjIsoDaggerBiproduct_hom_π_assoc]
    _ = (daggerLiftUnique F L α).hom.app M ≫ daggerBiproduct.π (fun j => F.obj (M.X j)) i :=
          hrhs.symm

/-- Two additive functors `Mat_ C ⥤ D` are naturally isomorphic whenever their restrictions along
`embedding C` are naturally isomorphic; the resulting isomorphism is pointwise unitary if both
functors preserve daggers and the given isomorphism on `C` is unitary. -/
def daggerExt {F G : Mat_ C ⥤ D} [F.Additive] [G.Additive]
    (α : embedding C ⋙ F ≅ embedding C ⋙ G) : F ≅ G :=
  daggerLiftUnique (embedding C ⋙ G) F α ≪≫
    (daggerLiftUnique (embedding C ⋙ G) G (Iso.refl _)).symm

/-- `Mat_.daggerExt` preserves pointwise unitarity. -/
theorem isUnitary_daggerExt {F G : Mat_ C ⥤ D} [F.Additive] [G.Additive]
    [F.PreservesDagger] [G.PreservesDagger] (α : embedding C ⋙ F ≅ embedding C ⋙ G)
    (hα : ∀ X, IsUnitary (α.app X).hom) (M : Mat_ C) :
    IsUnitary ((daggerExt α).app M).hom := by
  have h1 := isUnitary_daggerLiftUnique (embedding C ⋙ G) F α hα M
  have h2 := isUnitary_daggerLiftUnique (embedding C ⋙ G) G (Iso.refl _) (fun _ => IsUnitary.id _) M
  refine h1.comp ?_
  change IsUnitary ((daggerLiftUnique (embedding C ⋙ G) G (Iso.refl _)).app M).inv
  rw [← ((daggerLiftUnique (embedding C ⋙ G) G (Iso.refl _)).app M).dagger_hom_eq_inv_of_isUnitary
    h2]
  exact h2.dagger

end DaggerLift

end Lift

section Comparison

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D] [DaggerCategory D]
  [HasFiniteDaggerBiproducts D]

/-- Comparison natural isomorphism between `Mat_.daggerLift F` and Mathlib's `Mat_.lift F`. -/
def daggerLiftIsoLift (F : C ⥤ D) [F.Additive] : daggerLift F ≅ lift F :=
  NatIso.ofComponents (fun M => daggerBiproduct.isoBiproduct fun i => F.obj (M.X i)) fun f => by
    change (daggerBiproduct.matrix fun i j => F.map (f i j)) ≫
        (daggerBiproduct.isoBiproduct fun i => F.obj (_)).hom =
      (daggerBiproduct.isoBiproduct fun i => F.obj (_)).hom ≫
        biproduct.matrix fun i j => F.map (f i j)
    apply biproduct.hom_ext
    intro j
    apply daggerBiproduct.hom_ext'
    intro i
    simp [daggerBiproduct.isoBiproduct_hom_π,
      daggerBiproduct.matrix_π, daggerBiproduct.ι_isoBiproduct_hom_assoc]

end Comparison

section SelfEquivalence

variable (C) [DaggerCategory C] [DaggerPreadditive C] [HasFiniteDaggerBiproducts C]

private def daggerEquivalenceSelfAux :
    embedding C ⋙ 𝟭 (Mat_ C) ≅ embedding C ⋙ daggerLift (𝟭 C) ⋙ embedding C :=
  Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (embeddingDaggerLiftIso (𝟭 C)).symm (embedding C) ≪≫
        Functor.associator _ _ _

private theorem isUnitary_daggerEquivalenceSelfAux (X : C) :
    IsUnitary ((daggerEquivalenceSelfAux C).app X).hom := by
  have hu : IsUnitary ((embeddingDaggerLiftIso (𝟭 C)).app X).hom :=
    isUnitary_embeddingDaggerLiftIso (𝟭 C) X
  have hinv : IsUnitary ((embeddingDaggerLiftIso (𝟭 C)).symm.app X).hom := by
    change IsUnitary ((embeddingDaggerLiftIso (𝟭 C)).app X).inv
    rw [← ((embeddingDaggerLiftIso (𝟭 C)).app X).dagger_hom_eq_inv_of_isUnitary hu]
    exact hu.dagger
  simpa [daggerEquivalenceSelfAux] using (embedding C).map_isUnitary hinv

/-- A preadditive dagger category that already has finite dagger biproducts is equivalent to
`Mat_ C`, via dagger-preserving functors with pointwise unitary unit and counit isomorphisms. -/
def daggerEquivalenceSelf : Mat_ C ≌ C :=
  Equivalence.mk (daggerLift (𝟭 C)) (embedding C)
    (daggerExt (daggerEquivalenceSelfAux C)) (embeddingDaggerLiftIso (𝟭 C))

/-- The forward functor of `daggerEquivalenceSelf C` is `daggerLift (𝟭 C)`. -/
@[simp] theorem daggerEquivalenceSelf_functor :
    (daggerEquivalenceSelf C).functor = daggerLift (𝟭 C) := (rfl)

/-- The inverse functor of `daggerEquivalenceSelf C` is `embedding C`. -/
@[simp] theorem daggerEquivalenceSelf_inverse :
    (daggerEquivalenceSelf C).inverse = embedding C := (rfl)

/-- The forward functor of `daggerEquivalenceSelf C` preserves daggers. -/
instance instPreservesDaggerEquivalenceSelfFunctor :
    (daggerEquivalenceSelf C).functor.PreservesDagger := by
  rw [daggerEquivalenceSelf_functor]
  infer_instance

/-- The inverse functor of `daggerEquivalenceSelf C` preserves daggers. -/
instance instPreservesDaggerEquivalenceSelfInverse :
    (daggerEquivalenceSelf C).inverse.PreservesDagger := by
  rw [daggerEquivalenceSelf_inverse]
  infer_instance

/-- The unit of `daggerEquivalenceSelf C` is pointwise unitary. -/
theorem isUnitary_daggerEquivalenceSelf_unitIso (M : Mat_ C) :
    IsUnitary ((daggerEquivalenceSelf C).unitIso.app M).hom := by
  let η := daggerExt (daggerEquivalenceSelfAux C)
  let ε := embeddingDaggerLiftIso (𝟭 C)
  have hη : ∀ N : Mat_ C, IsUnitary (η.app N).hom :=
    isUnitary_daggerExt (daggerEquivalenceSelfAux C) (isUnitary_daggerEquivalenceSelfAux C)
  have hη_inv : ∀ N : Mat_ C, IsUnitary (η.app N).inv := fun N => by
    rw [← (η.app N).dagger_hom_eq_inv_of_isUnitary (hη N)]
    exact (hη N).dagger
  have hε : ∀ X : C, IsUnitary (ε.app X).hom := isUnitary_embeddingDaggerLiftIso (𝟭 C)
  have hε_inv : ∀ X : C, IsUnitary (ε.app X).inv := fun X => by
    rw [← (ε.app X).dagger_hom_eq_inv_of_isUnitary (hε X)]
    exact (hε X).dagger
  change IsUnitary ((Equivalence.adjointifyη η ε).app M).hom
  dsimp [Equivalence.adjointifyη, Trans.trans]
  simp only [Category.comp_id]
  exact ((hη M).comp ((embedding C).map_isUnitary (hε_inv ((daggerLift (𝟭 C)).obj M)))).comp
    ((embedding C).map_isUnitary ((daggerLift (𝟭 C)).map_isUnitary (hη_inv M)))

/-- The counit of `daggerEquivalenceSelf C` is pointwise unitary. -/
theorem isUnitary_daggerEquivalenceSelf_counitIso (X : C) :
    IsUnitary ((daggerEquivalenceSelf C).counitIso.app X).hom :=
  isUnitary_embeddingDaggerLiftIso (𝟭 C) X

end SelfEquivalence

end Mat_

end CategoryTheory
