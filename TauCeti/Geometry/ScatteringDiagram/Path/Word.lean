/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Subdivision
public import TauCeti.Geometry.ScatteringDiagram.Path.Product
public import Mathlib.GroupTheory.FreeGroup.Basic
import TauCeti.Data.Finset.Sort

/-!
# Free-group crossing words of admissible polygonal paths

When the members of a finite wall family `W : ι → Set V` have pairwise disjoint relative interiors
(as holds for the codimension-one walls of any `TauCeti.FinitePolyhedralComplex`), an admissible
segment meets at most one wall at each parameter (`WallComplement.subsingleton_crossingWalls`),
because every crossing occurs in the relative interior of its wall. Thus each crossing time produces
a single signed generator `FreeGroup.of i ^ (±1)` with no commutation assumption between coplanar
walls, and multiplying in reverse traversal order yields the path crossing word
`Quiver.Path.crossingWord` in `FreeGroup ι`.

We establish the algebraic and functorial operations on `Quiver.Path.crossingWord` (following
Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, §§2.2–2.5, and
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1 and Appendix C.1):
* **Concatenation, reversal, and path subdivision**: `(p.comp q).crossingWord` multiplies in left
  action order (`q.crossingWord * p.crossingWord`), `p.reverse.crossingWord` inverts the word, and
  `Quiver.Path.IsSubdivision.crossingWord_eq` shows invariance under inserting allowed vertices.
* **Universal property**: whenever wall labels in a group `G` commute on coplanar walls,
  `FreeGroup.lift label (p.crossingWord ν hdisj)` equals `p.wallPathProduct ν label hcomm`
  (`Quiver.Path.lift_crossingWord_eq_wallPathProduct`).
* **Wall deletion**: restricting along an injective index map `f : κ → ι` (in particular, passing
  to a subset of walls or a subcomplex `D.IsSubcomplex C`) applies `FreeGroup.lift` sending retained
  walls to their preimage generators and deleted walls to `1`
  (`Quiver.Path.lift_restrictWallGen_crossingWord`,
  `TauCeti.FinitePolyhedralComplex.IsSubcomplex.lift_crossingWord`).
* **Complex subdivision**: if `C.IsSubdivision D`, allowed vertices and admissible paths for
  `C.walls` are automatically admissible for `D.walls`
  (`TauCeti.FinitePolyhedralComplex.IsSubdivision.wallsPrefunctor`), and `FreeGroup.lift` sending
  each wall `w'` of `C` inside a wall `w` of `D` to `FreeGroup.of w` (or `(FreeGroup.of w)⁻¹` when
  coorientations disagree) and every other wall of `C` to `1` maps `p.crossingWord` to the
  crossing word on `D.walls`
  (`TauCeti.FinitePolyhedralComplex.IsSubdivision.lift_subdivisionWallGen_crossingWord`).
* **Coordinate transport**: continuous affine equivalences and wall-index bijections act on
  `crossingWord` via `FreeGroup.map`, and in particular an `IntegralAffineEquiv` transports
  admissible paths on `C.walls` to `(C.image e).walls` and maps their crossing word by
  `FreeGroup.map (C.wallsEquivImage e)`
  (`TauCeti.FinitePolyhedralComplex.crossingWord_wallsImagePrefunctor`).
-/

public section

noncomputable section

open Set

namespace TauCeti.WallComplement

section RestrictWallGen

variable {ι κ : Type*}

/-- Generator map for wall deletion along `f : κ → ι`: indices in the range of `f` map to a chosen
preimage generator in `FreeGroup κ`, while deleted indices outside `Set.range f` map to `1`. -/
def restrictWallGen (f : κ → ι) (i : ι) : FreeGroup κ :=
  open scoped Classical in
  if h : ∃ k, f k = i then FreeGroup.of h.choose else 1

/-- An injected wall index maps to its own generator under `restrictWallGen`. -/
@[simp]
theorem restrictWallGen_apply_of_injective {f : κ → ι} (hf : Function.Injective f) (k : κ) :
    restrictWallGen f (f k) = FreeGroup.of k := by
  classical
  have hex : ∃ l, f l = f k := ⟨k, rfl⟩
  simp only [restrictWallGen, hex, ↓reduceDIte]
  exact congrArg FreeGroup.of (hf hex.choose_spec)

/-- A wall index outside the range of `f` maps to `1` under `restrictWallGen`. -/
@[simp]
theorem restrictWallGen_of_not_exists {f : κ → ι} {i : ι} (h : ¬∃ k, f k = i) :
    restrictWallGen f i = 1 := by
  classical
  simp only [restrictWallGen, h, ↓reduceDIte]

end RestrictWallGen

section PairwiseDisjoint

variable {V U ι κ : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {W : ι → Set V}

/-- Continuous affine equivalences preserve pairwise disjointness of wall relative interiors. -/
theorem pairwise_disjoint_intrinsicInterior_image
    [AddCommGroup U] [Module ℝ U] [TopologicalSpace U]
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : V ≃ᴬ[ℝ] U) :
    Pairwise fun i j =>
      Disjoint (intrinsicInterior ℝ (e '' W i)) (intrinsicInterior ℝ (e '' W j)) := by
  intro i j hij
  rw [e.intrinsicInterior_image, e.intrinsicInterior_image]
  refine disjoint_left.mpr fun z hzi hzj => ?_
  obtain ⟨x, hx, rfl⟩ := hzi
  obtain ⟨y, hy, hxy⟩ := hzj
  exact (hdisj hij).le_bot ⟨hx, e.injective hxy ▸ hy⟩

/-- Bijective carrier reindexing preserves pairwise disjointness of wall relative interiors. -/
theorem pairwise_disjoint_intrinsicInterior_of_reindex
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) :
    Pairwise fun k l => Disjoint (intrinsicInterior ℝ (W' k)) (intrinsicInterior ℝ (W' l)) := by
  intro k l hkl
  obtain ⟨i, rfl⟩ := σ.surjective k
  obtain ⟨j, rfl⟩ := σ.surjective l
  simpa only [hW] using hdisj (σ.injective.ne_iff.mp hkl)

end PairwiseDisjoint

section Isolated

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {x y : WallComplement W}

/-- When wall relative interiors are pairwise disjoint, an admissible segment meets at most one
wall at any parameter. -/
theorem subsingleton_crossingWalls
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) :
    (crossingWalls x y t : Set ι).Subsingleton := by
  intro i hi j hj
  by_contra hij
  obtain ⟨ht, hwi⟩ := (mem_crossings x y i t).mp ((mem_crossingWalls x y t i).mp hi)
  obtain ⟨_, hwj⟩ := (mem_crossings x y j t).mp ((mem_crossingWalls x y t j).mp hj)
  exact (hdisj hij).le_bot
    ⟨(e.down.crossing_mem_intrinsicInterior ht hwi).2,
      (e.down.crossing_mem_intrinsicInterior ht hwj).2⟩

/-- At most one wall is crossed at each parameter when relative interiors are pairwise disjoint. -/
theorem card_crossingWalls_le_one
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) :
    (crossingWalls x y t).card ≤ 1 :=
  Finset.card_le_one.mpr fun _ hi _ hj => subsingleton_crossingWalls hdisj e t hi hj

/-- Exactly one wall is crossed at each listed crossing time when relative interiors are pairwise
disjoint. -/
theorem card_crossingWalls_eq_one
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) {t : ℝ} (ht : t ∈ orderedCrossingTimes e) :
    (crossingWalls x y t).card = 1 :=
  le_antisymm (card_crossingWalls_le_one hdisj e t)
    (Finset.card_pos.mpr (crossingWalls_nonempty e ht))

/-- Each signed crossing event has at most one element when wall relative interiors are pairwise
disjoint. -/
theorem subsingleton_signedCrossingEvent (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) :
    (signedCrossingEvent ν x y t : Set (ι × ℤ)).Subsingleton := by
  rintro ⟨i, r⟩ ha ⟨j, s⟩ hb
  obtain ⟨hai, rfl⟩ := (mem_signedCrossingEvent ν x y t i r).mp ha
  obtain ⟨hbj, rfl⟩ := (mem_signedCrossingEvent ν x y t j s).mp hb
  obtain rfl : i = j := subsingleton_crossingWalls hdisj e t
    ((mem_crossingWalls x y t i).mpr hai) ((mem_crossingWalls x y t j).mpr hbj)
  rfl

/-- Free-group factor contributed at a single parameter along an admissible segment. -/
def crossingEventWord (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) : FreeGroup ι :=
  (signedCrossingEvent ν x y t).noncommProd (fun a => FreeGroup.of a.1 ^ a.2)
    ((subsingleton_signedCrossingEvent ν hdisj e t).pairwise _)

/-- An empty signed crossing event contributes `1` to the crossing word. -/
@[simp]
theorem crossingEventWord_empty (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) (ht : signedCrossingEvent ν x y t = ∅) :
    crossingEventWord ν hdisj e t = 1 := by
  unfold crossingEventWord
  exact (Finset.noncommProd_congr ht (fun _ _ => rfl) _).trans (Finset.noncommProd_empty _ _)

/-- A singleton signed crossing event `(i, s)` contributes `FreeGroup.of i ^ s`. -/
theorem crossingEventWord_singleton (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) (a : ι × ℤ) (ha : signedCrossingEvent ν x y t = {a}) :
    crossingEventWord ν hdisj e t = FreeGroup.of a.1 ^ a.2 := by
  unfold crossingEventWord
  simp only [ha, Finset.noncommProd_singleton]

/-- Any duplicate-free enumeration of a signed crossing event multiplies to `crossingEventWord`. -/
theorem crossingEventWord_eq_prod (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) (l : List (ι × ℤ)) (hl : l.Nodup)
    (hm : ∀ a, a ∈ l ↔ a ∈ signedCrossingEvent ν x y t) :
    crossingEventWord ν hdisj e t = (l.map fun a => FreeGroup.of a.1 ^ a.2).prod := by
  classical
  have hs : l.toFinset = signedCrossingEvent ν x y t := by ext a; simpa using hm a
  unfold crossingEventWord
  exact (Finset.noncommProd_congr hs.symm (fun _ _ => rfl) _).trans
    (Finset.noncommProd_toFinset l _ _ hl)

/-- Reversing an admissible segment inverts its crossing event word at the reflected parameter. -/
theorem crossingEventWord_reverse (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (e : x ⟶ y) (t : ℝ) :
    crossingEventWord ν hdisj (Quiver.reverse e) t =
      (crossingEventWord ν hdisj e (1 - t))⁻¹ := by
  let S := signedCrossingEvent ν x y (1 - t)
  let f : ι × ℤ → FreeGroup ι := fun a => FreeGroup.of a.1 ^ a.2
  let emb := (Equiv.prodCongr (Equiv.refl ι) (Equiv.neg ℤ)).toEmbedding
  have hc := (subsingleton_signedCrossingEvent ν hdisj e (1 - t)).pairwise
    (fun a b => Commute (f a) (f b))
  have hc' : (S.map emb : Set (ι × ℤ)).Pairwise (fun a b => Commute (f a) (f b)) := by
    rw [Finset.coe_map]
    exact ((subsingleton_signedCrossingEvent ν hdisj e (1 - t)).image _).pairwise _
  calc
    crossingEventWord ν hdisj (Quiver.reverse e) t
      = (S.map emb).noncommProd f hc' :=
        Finset.noncommProd_congr (signedCrossingEvent_swap ν hν e t) (fun _ _ => rfl) _
    _ = S.noncommProd (fun a => f (emb a)) _ := Finset.noncommProd_map S emb f hc'
    _ = (crossingEventWord ν hdisj e (1 - t))⁻¹ := by
        simpa only [f, emb, Equiv.toEmbedding_apply, Equiv.prodCongr_apply, Prod.map_fst,
          Prod.map_snd, Equiv.refl_apply, Equiv.neg_apply, zpow_neg, crossingEventWord, S] using
          Finset.noncommProd_inv S f hc

/-- Free-group crossing word of an admissible segment, with the first crossing rightmost. -/
def segmentCrossingWord (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) : FreeGroup ι :=
  ((orderedCrossingTimes e).reverse.map (crossingEventWord ν hdisj e)).prod

/-- Unfold `segmentCrossingWord` as the reverse-ordered product of event words. -/
theorem segmentCrossingWord_def (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) :
    segmentCrossingWord ν hdisj e =
      ((orderedCrossingTimes e).reverse.map (crossingEventWord ν hdisj e)).prod := (rfl)

/-- Any strictly increasing list containing every crossing time computes the segment crossing word;
extra times contribute `1`. -/
theorem segmentCrossingWord_eq_prod_of_crossingTimes (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (T : List ℝ) (hT : T.Pairwise (· < ·))
    (hcover : ∀ t ∈ orderedCrossingTimes e, t ∈ T) :
    segmentCrossingWord ν hdisj e =
      (T.reverse.map (crossingEventWord ν hdisj e)).prod := by
  classical
  let f := crossingEventWord ν hdisj e
  have hone (t : ℝ) (ht : t ∉ orderedCrossingTimes e) : f t = 1 := by
    apply crossingEventWord_empty
    refine Finset.eq_empty_iff_forall_notMem.mpr fun ⟨j, r⟩ hj => ?_
    exact ht ((mem_orderedCrossingTimes e t).mpr
      ⟨j, ((mem_signedCrossingEvent ν x y t j r).mp hj).1⟩)
  have hs : (orderedCrossingTimes e).toFinset ⊆ T.toFinset :=
    fun t ht => List.mem_toFinset.mpr (hcover t (List.mem_toFinset.mp ht))
  have hS : (orderedCrossingTimes e).toFinset.sort = orderedCrossingTimes e :=
    (Finset.sortedLT_sort _).pairwise.eq_of_mem_iff (pairwise_orderedCrossingTimes e) (by simp)
  have hTsort : T.toFinset.sort = T :=
    (Finset.sortedLT_sort _).pairwise.eq_of_mem_iff hT (by simp)
  rw [segmentCrossingWord_def]
  simp only [List.map_reverse, List.prod_reverse_noncomm, List.map_map, Function.comp_def]
  exact congrArg Inv.inv (by
    simpa only [hS, hTsort] using Finset.prod_map_sort_subset hs (fun t => (f t)⁻¹)
      (fun t _ ht => by rw [hone t (by simpa only [List.mem_toFinset] using ht), inv_one]))

/-- A stationary admissible segment has trivial crossing word. -/
@[simp]
theorem segmentCrossingWord_self (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ x) :
    segmentCrossingWord ν hdisj e = 1 := by
  have ht : orderedCrossingTimes e = [] := List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
    obtain ⟨i, hi⟩ := (mem_orderedCrossingTimes e t).mp ht
    exact x.notMem i (by simpa using ((mem_crossings x x i t).mp hi).2)
  simp [segmentCrossingWord_def, ht]

/-- Reversing an admissible segment inverts its crossing word. -/
@[simp]
theorem segmentCrossingWord_reverse (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (e : x ⟶ y) :
    segmentCrossingWord ν hdisj (Quiver.reverse e) = (segmentCrossingWord ν hdisj e)⁻¹ := by
  simp only [segmentCrossingWord, orderedCrossingTimes_reverse, List.map_reverse,
    List.reverse_reverse, List.map_map, Function.comp_def,
    crossingEventWord_reverse ν hdisj hν, sub_sub_cancel, List.prod_inv_reverse]

section Reindex

variable {κ : Type*} [Finite κ]

/-- Bijective carrier reindexing maps each single-parameter crossing event word by
`FreeGroup.map`. -/
theorem crossingEventWord_reindex (ν' : κ → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (a : x ⟶ y) (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) (t : ℝ) :
    crossingEventWord ν' (pairwise_disjoint_intrinsicInterior_of_reindex hdisj σ hW)
      ((reindexPrefunctor σ hW).map a) t =
      FreeGroup.map σ (crossingEventWord (fun i => ν' (σ i)) hdisj a t) := by
  let S := signedCrossingEvent (fun i => ν' (σ i)) x y t
  let emb := (Equiv.prodCongr σ (Equiv.refl ℤ)).toEmbedding
  let f : κ × ℤ → FreeGroup κ := fun p => FreeGroup.of p.1 ^ p.2
  have hc' : (S.map emb : Set (κ × ℤ)).Pairwise (fun p q => Commute (f p) (f q)) := by
    rw [Finset.coe_map]
    exact ((subsingleton_signedCrossingEvent (fun i => ν' (σ i)) hdisj a t).image _).pairwise _
  calc
    crossingEventWord ν' _ ((reindexPrefunctor σ hW).map a) t
      = (S.map emb).noncommProd f hc' :=
        Finset.noncommProd_congr (signedCrossingEvent_reindex ν' x y σ hW t) (fun _ _ => rfl) _
    _ = S.noncommProd (fun p => f (emb p)) _ := Finset.noncommProd_map S emb f hc'
    _ = FreeGroup.map σ (crossingEventWord (fun i => ν' (σ i)) hdisj a t) := by
        unfold crossingEventWord
        rw [Finset.map_noncommProd]
        refine Finset.noncommProd_congr rfl (fun p _ => ?_) _
        simp [f, emb]

/-- Bijective carrier reindexing maps the crossing word of an admissible segment by
`FreeGroup.map`. -/
theorem segmentCrossingWord_reindex (ν' : κ → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (a : x ⟶ y) (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) :
    segmentCrossingWord ν' (pairwise_disjoint_intrinsicInterior_of_reindex hdisj σ hW)
      ((reindexPrefunctor σ hW).map a) =
      FreeGroup.map σ (segmentCrossingWord (fun i => ν' (σ i)) hdisj a) := by
  rw [segmentCrossingWord_def, orderedCrossingTimes_reindex, segmentCrossingWord_def,
    map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun t _ =>
    crossingEventWord_reindex ν' hdisj a σ hW t)

end Reindex

section Restrict

variable {κ : Type*} {f : κ → ι}

omit [Finite ι] in
private theorem mem_crossings_restrictPrefunctor (k : κ) (t : ℝ) :
    (k, t) ∈ crossings ((restrictPrefunctor W f).obj x) ((restrictPrefunctor W f).obj y) ↔
      (f k, t) ∈ crossings x y := by
  simp only [mem_crossings, Function.comp_apply]

variable [Finite κ]

/-- Deleting walls outside an injective index map `f` sends each crossing event word to the
restricted event word via `FreeGroup.lift (restrictWallGen f)`. -/
theorem lift_restrictWallGen_crossingEventWord (hf : Function.Injective f) (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) (t : ℝ) :
    FreeGroup.lift (restrictWallGen f) (crossingEventWord ν hdisj e t) =
      crossingEventWord (ν ∘ f) (hdisj.comp_of_injective hf)
        ((restrictPrefunctor W f).map e) t := by
  let e' := (restrictPrefunctor W f).map e
  rcases (signedCrossingEvent ν x y t).eq_empty_or_nonempty with hemp | ⟨⟨i, s⟩, his⟩
  · rw [crossingEventWord_empty ν hdisj e t hemp, map_one, eq_comm]
    refine crossingEventWord_empty _ _ e' t
      (Finset.eq_empty_iff_forall_notMem.mpr fun ⟨k, r⟩ hk => ?_)
    obtain ⟨hkt, -⟩ := (mem_signedCrossingEvent (ν ∘ f) _ _ t k r).mp hk
    rw [mem_crossings_restrictPrefunctor] at hkt
    have hfk : (f k, if 0 < ν (f k) (y.val - x.val) then -1 else 1) ∈
        signedCrossingEvent ν x y t :=
      (mem_signedCrossingEvent ν x y t (f k) _).mpr ⟨hkt, rfl⟩
    exact Finset.notMem_empty _ (hemp ▸ hfk)
  · have hsing : signedCrossingEvent ν x y t = {(i, s)} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨his, fun b hb => subsingleton_signedCrossingEvent ν hdisj e t hb his⟩
    obtain ⟨hit, rfl⟩ := (mem_signedCrossingEvent ν x y t i s).mp his
    rw [crossingEventWord_singleton ν hdisj e t _ hsing, map_zpow, FreeGroup.lift_apply_of]
    by_cases hex : ∃ k, f k = i
    · obtain ⟨k, rfl⟩ := hex
      rw [restrictWallGen_apply_of_injective hf, eq_comm]
      have hkt := (mem_crossings_restrictPrefunctor (x := x) (y := y) (f := f) k t).mpr hit
      refine crossingEventWord_singleton _ _ e' t (k, if 0 < ν (f k) (y.val - x.val) then -1 else 1)
        (Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_signedCrossingEvent _ _ _ t k _).mpr
          ⟨hkt, rfl⟩, fun ⟨l, r⟩ hlr => ?_⟩)
      obtain ⟨hlt, rfl⟩ := (mem_signedCrossingEvent (ν ∘ f) _ _ t l r).mp hlr
      rw [mem_crossings_restrictPrefunctor] at hlt
      have hfl : f l = f k := subsingleton_crossingWalls hdisj e t
        ((mem_crossingWalls x y t (f l)).mpr hlt) ((mem_crossingWalls x y t (f k)).mpr hit)
      obtain rfl := hf hfl
      rfl
    · rw [restrictWallGen_of_not_exists hex, one_zpow, eq_comm]
      refine crossingEventWord_empty _ _ e' t
        (Finset.eq_empty_iff_forall_notMem.mpr fun ⟨k, r⟩ hkr => ?_)
      obtain ⟨hkt, -⟩ := (mem_signedCrossingEvent (ν ∘ f) _ _ t k r).mp hkr
      rw [mem_crossings_restrictPrefunctor] at hkt
      exact hex ⟨k, subsingleton_crossingWalls hdisj e t
        ((mem_crossingWalls x y t (f k)).mpr hkt) ((mem_crossingWalls x y t i).mpr hit)⟩

/-- Deleting walls outside an injective index map `f` sends the segment crossing word to the
restricted segment crossing word via `FreeGroup.lift (restrictWallGen f)`. -/
theorem lift_restrictWallGen_segmentCrossingWord (hf : Function.Injective f) (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) :
    FreeGroup.lift (restrictWallGen f) (segmentCrossingWord ν hdisj e) =
      segmentCrossingWord (ν ∘ f) (hdisj.comp_of_injective hf)
        ((restrictPrefunctor W f).map e) := by
  have hcover : ∀ t ∈ orderedCrossingTimes ((restrictPrefunctor W f).map e),
      t ∈ orderedCrossingTimes e := by
    intro t ht
    obtain ⟨k, hk⟩ := (mem_orderedCrossingTimes _ t).mp ht
    rw [mem_crossings_restrictPrefunctor] at hk
    exact (mem_orderedCrossingTimes e t).mpr ⟨f k, hk⟩
  rw [segmentCrossingWord_eq_prod_of_crossingTimes (ν ∘ f) (hdisj.comp_of_injective hf)
    ((restrictPrefunctor W f).map e) (orderedCrossingTimes e) (pairwise_orderedCrossingTimes e)
    hcover, segmentCrossingWord_def, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun t _ =>
    lift_restrictWallGen_crossingEventWord hf ν hdisj e t)

end Restrict

end Isolated

end TauCeti.WallComplement

namespace Quiver.Path

open TauCeti WallComplement

section Isolated

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {x y z : WallComplement W}

/-- Every signed crossing event along an admissible polygonal path is a singleton when wall
relative interiors are pairwise disjoint. -/
theorem subsingleton_of_mem_signedCrossingEvents (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) {S : Finset (ι × ℤ)} (hS : S ∈ p.signedCrossingEvents ν) :
    (S : Set (ι × ℤ)).Subsingleton := by
  induction p with
  | nil => simp at hS
  | cons p e ih =>
    rw [signedCrossingEvents_cons] at hS
    rcases List.mem_append.mp hS with hp | he
    · exact ih hp
    · obtain ⟨t, -, rfl⟩ := (mem_segmentCrossingEvents ν e S).mp he
      exact subsingleton_signedCrossingEvent ν hdisj e t

/-- Every listed signed crossing event along an admissible polygonal path has cardinality `1` when
wall relative interiors are pairwise disjoint. -/
theorem card_eq_one_of_mem_signedCrossingEvents (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) {S : Finset (ι × ℤ)} (hS : S ∈ p.signedCrossingEvents ν) :
    S.card = 1 :=
  le_antisymm (Finset.card_le_one.mpr fun _ ha _ hb =>
      subsingleton_of_mem_signedCrossingEvents ν hdisj p hS ha hb)
    (Finset.card_pos.mpr (p.nonempty_of_mem_signedCrossingEvents ν hS))

/-- Free-group crossing word of an admissible polygonal path for a wall family with pairwise
disjoint relative interiors. Later crossings multiply on the left, and a crossing with positive
normal velocity contributes `(FreeGroup.of i)⁻¹`. -/
def crossingWord (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) : FreeGroup ι :=
  MulOpposite.unop (p.weight (fun e => MulOpposite.op (segmentCrossingWord ν hdisj e)))

/-- The empty admissible polygonal path has trivial crossing word. -/
@[simp]
theorem crossingWord_nil (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j))) :
    (Quiver.Path.nil : AdmissiblePLPath x x).crossingWord ν hdisj = 1 := by
  simp only [crossingWord, weight_nil, MulOpposite.unop_one]

/-- Extending a polygonal path by one segment multiplies on the left by that segment's crossing
word. -/
@[simp]
theorem crossingWord_cons (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    (p.cons e).crossingWord ν hdisj =
      segmentCrossingWord ν hdisj e * p.crossingWord ν hdisj := by
  simp only [crossingWord, weight_cons, MulOpposite.unop_mul, MulOpposite.unop_op]

/-- A single-segment path has the segment crossing word. -/
@[simp]
theorem crossingWord_toPath (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (e : x ⟶ y) :
    e.toPath.crossingWord ν hdisj = segmentCrossingWord ν hdisj e := by
  simp [Quiver.Hom.toPath]

/-- Concatenating admissible polygonal paths multiplies their crossing words in left-action
order. -/
@[simp]
theorem crossingWord_comp (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    (p.comp q).crossingWord ν hdisj = q.crossingWord ν hdisj * p.crossingWord ν hdisj := by
  simp only [crossingWord, weight_comp, MulOpposite.unop_mul]

/-- Reversing an admissible polygonal path inverts its crossing word. -/
@[simp]
theorem crossingWord_reverse (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (p : AdmissiblePLPath x y) :
    p.reverse.crossingWord ν hdisj = (p.crossingWord ν hdisj)⁻¹ := by
  induction p with
  | nil => simp [Quiver.Path.reverse]
  | cons p e ih =>
    simp [Quiver.Path.reverse, ih, segmentCrossingWord_reverse ν hdisj hν, mul_inv_rev]

/-- Express `crossingWord` as the product over reversed signed crossing events. -/
theorem crossingWord_eq_prod_signedCrossingEvents (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) :
    p.crossingWord ν hdisj =
      ((p.signedCrossingEvents ν).reverse.map
        (fun S => (S.toList.map (fun a => FreeGroup.of a.1 ^ a.2)).prod)).prod := by
  classical
  have he {u v : WallComplement W} (e : u ⟶ v) :
      segmentCrossingWord ν hdisj e =
        ((segmentCrossingEvents ν e).reverse.map
          (fun S => (S.toList.map (fun a => FreeGroup.of a.1 ^ a.2)).prod)).prod := by
    simp only [segmentCrossingWord_def, segmentCrossingEvents_def, List.map_reverse, List.map_map]
    congr 2
    exact List.map_congr_left fun t _ =>
      crossingEventWord_eq_prod ν hdisj e t _ (Finset.nodup_toList _) (fun _ => Finset.mem_toList)
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [crossingWord_cons, signedCrossingEvents_cons, List.reverse_append,
      List.map_append, List.prod_append, ih, he]

/-- Flatten the reversed signed crossing events into a single list of signed generators whose
product is `crossingWord`. -/
theorem crossingWord_eq_prod_flatMap (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) :
    p.crossingWord ν hdisj =
      (((p.signedCrossingEvents ν).reverse.flatMap Finset.toList).map
        fun a => FreeGroup.of a.1 ^ a.2).prod := by
  rw [crossingWord_eq_prod_signedCrossingEvents]
  simp [List.flatMap_def, List.prod_flatten, Function.comp_def]

/-- Paths with equal ordered signed crossing events have equal crossing words, even across
different ambient spaces. -/
theorem crossingWord_eq_of_signedCrossingEvents_eq
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] {W' : ι → Set U}
    {ν : ι → V →ₗ[ℝ] ℝ} {ν' : ι → U →ₗ[ℝ] ℝ}
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (hdisj' : Pairwise fun i j =>
      Disjoint (intrinsicInterior ℝ (W' i)) (intrinsicInterior ℝ (W' j)))
    {x' y' : WallComplement W'} (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.signedCrossingEvents ν = q.signedCrossingEvents ν') :
    p.crossingWord ν hdisj = q.crossingWord ν' hdisj' := by
  rw [crossingWord_eq_prod_flatMap, crossingWord_eq_prod_flatMap, hpq]

/-- Positive rescaling of coorientations leaves the crossing word unchanged. -/
@[simp]
theorem crossingWord_smul (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (p : AdmissiblePLPath x y) :
    p.crossingWord (fun i => r i • ν i) hdisj = p.crossingWord ν hdisj :=
  crossingWord_eq_of_signedCrossingEvents_eq hdisj hdisj p p (p.signedCrossingEvents_smul ν r hr)

/-- Subdividing an admissible polygonal path by inserting allowed vertices preserves its crossing
word. -/
theorem IsSubdivision.crossingWord_eq (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    {p q : AdmissiblePLPath x y} (h : p.IsSubdivision q) :
    p.crossingWord ν hdisj = q.crossingWord ν hdisj :=
  crossingWord_eq_of_signedCrossingEvents_eq hdisj hdisj p q (h.signedCrossingEvents_eq ν)

/-- Evaluating `crossingWord` on labels in a group `G` via `FreeGroup.lift` recovers
`Quiver.Path.wallPathProduct` whenever coplanar wall labels commute. -/
@[simp]
theorem lift_crossingWord_eq_wallPathProduct {G : Type*} [Group G]
    (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (p : AdmissiblePLPath x y) :
    FreeGroup.lift label (p.crossingWord ν hdisj) = p.wallPathProduct ν label hcomm := by
  rw [crossingWord_eq_prod_flatMap, wallPathProduct_eq_prod_flatMap, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun a _ => ?_)
  simp

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] in
/-- Transporting an admissible polygonal path by a continuous affine equivalence preserves its
crossing word when coorientations are pulled back by the inverse linear equivalence. -/
theorem crossingWord_affineMap (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).crossingWord
      (fun i => (ν i).comp e.toAffineEquiv.linear.symm.toLinearMap)
      (pairwise_disjoint_intrinsicInterior_image hdisj e) =
      p.crossingWord ν hdisj :=
  crossingWord_eq_of_signedCrossingEvents_eq
    (pairwise_disjoint_intrinsicInterior_image hdisj e) hdisj
    (p.affineMap e) p (p.signedCrossingEvents_affineMap ν e)

variable {κ : Type*} [Finite κ] in
/-- Bijective carrier reindexing maps the crossing word of an admissible polygonal path by
`FreeGroup.map`. -/
theorem crossingWord_reindexPrefunctor (ν' : κ → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) :
    ((reindexPrefunctor σ hW).mapPath p).crossingWord ν'
      (pairwise_disjoint_intrinsicInterior_of_reindex hdisj σ hW) =
      FreeGroup.map σ (p.crossingWord (fun i => ν' (σ i)) hdisj) := by
  induction p with
  | nil => simp
  | cons p a ih =>
    rw [Prefunctor.mapPath_cons, crossingWord_cons, crossingWord_cons, map_mul, ih,
      segmentCrossingWord_reindex]

variable {κ : Type*} [Finite κ] in
/-- Deleting walls outside the range of an injective index map `f : κ → ι` maps the crossing word
by the `FreeGroup.lift` killing deleted generators. -/
theorem lift_restrictWallGen_crossingWord {f : κ → ι} (hf : Function.Injective f)
    (ν : ι → V →ₗ[ℝ] ℝ)
    (hdisj : Pairwise fun i j => Disjoint (intrinsicInterior ℝ (W i)) (intrinsicInterior ℝ (W j)))
    (p : AdmissiblePLPath x y) :
    FreeGroup.lift (restrictWallGen f) (p.crossingWord ν hdisj) =
      ((restrictPrefunctor W f).mapPath p).crossingWord (ν ∘ f) (hdisj.comp_of_injective hf) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Prefunctor.mapPath_cons, crossingWord_cons, crossingWord_cons, map_mul, ih,
      lift_restrictWallGen_segmentCrossingWord hf]

end Isolated

end Quiver.Path

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i}

/-! ### Wall deletion along a subcomplex -/

/-- Passing from a complex `C` to a subcomplex `D` forgets the walls of `C` outside `D` while
retaining all allowed vertices and admissible segments. -/
abbrev IsSubcomplex.wallsPrefunctor {D C : FinitePolyhedralComplex h} (hDC : D.IsSubcomplex C) :
    WallComplement (Subtype.val : C.walls → Set V) ⥤q
      WallComplement (Subtype.val : D.walls → Set V) :=
  WallComplement.restrictPrefunctor Subtype.val hDC.wallsEmbedding

/-- Restricting an admissible polygonal path from `C.walls` to the walls of a subcomplex `D` kills
all wall generators outside `D.walls`. -/
theorem IsSubcomplex.lift_crossingWord {D C : FinitePolyhedralComplex h} (hDC : D.IsSubcomplex C)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y : WallComplement (Subtype.val : C.walls → Set V)} (p : AdmissiblePLPath x y) :
    FreeGroup.lift (WallComplement.restrictWallGen hDC.wallsEmbedding)
      (p.crossingWord ν C.pairwise_disjoint_intrinsicInterior_walls) =
      ((hDC.wallsPrefunctor).mapPath p).crossingWord (ν ∘ hDC.wallsEmbedding)
        D.pairwise_disjoint_intrinsicInterior_walls :=
  p.lift_restrictWallGen_crossingWord hDC.wallsEmbedding.injective ν
    C.pairwise_disjoint_intrinsicInterior_walls

/-! ### Complex subdivision -/

section SubdivisionGen

/-- Generator map on walls induced by subdividing `D` into `C`: each wall `w'` of `C` contained in
a wall `w` of `D` maps to `FreeGroup.of w` when their coorientations agree and to
`(FreeGroup.of w)⁻¹` when they disagree, while walls of `C` contained in no wall of `D` map to
`1`. -/
def subdivisionWallGen {C D : FinitePolyhedralComplex h}
    (νC : C.walls → V →ₗ[ℝ] ℝ) (νD : D.walls → V →ₗ[ℝ] ℝ) (w' : C.walls) : FreeGroup D.walls :=
  open scoped Classical in
  if hw : ∃ w : D.walls, w'.val ⊆ w.val then
    if ∃ v : V, 0 < νC w' v ∧ 0 < νD hw.choose v then
      FreeGroup.of hw.choose
    else
      (FreeGroup.of hw.choose)⁻¹
  else
    1

/-- A wall of `C` contained in no wall of `D` maps to `1` under `subdivisionWallGen`. -/
@[simp]
theorem subdivisionWallGen_of_not_exists {C D : FinitePolyhedralComplex h}
    (νC : C.walls → V →ₗ[ℝ] ℝ) (νD : D.walls → V →ₗ[ℝ] ℝ) {w' : C.walls}
    (hw : ¬∃ w : D.walls, w'.val ⊆ w.val) :
    subdivisionWallGen νC νD w' = 1 := by
  simp only [subdivisionWallGen, hw, ↓reduceDIte]

/-- A wall `w'` of `C` inside a wall `w` of `D` maps to `FreeGroup.of w` when their coorientations
are simultaneously positive on some vector. -/
theorem subdivisionWallGen_of_subset_of_pos {C D : FinitePolyhedralComplex h}
    (νC : C.walls → V →ₗ[ℝ] ℝ) (νD : D.walls → V →ₗ[ℝ] ℝ) {w' : C.walls} {w : D.walls}
    (hw : w'.val ⊆ w.val) (hpos : ∃ v : V, 0 < νC w' v ∧ 0 < νD w v) :
    subdivisionWallGen νC νD w' = FreeGroup.of w := by
  classical
  obtain ⟨hw'c, hw'd⟩ := mem_cellsOfCodimension.mp w'.property
  have hex : ∃ u : D.walls, w'.val ⊆ u.val := ⟨w, hw⟩
  have heq : hex.choose = w := Subtype.ext
    (D.eq_of_mem_cellsOfCodimension_of_subset (C.nonempty w'.val hw'c) hw'd
      hex.choose.property w.property hex.choose_spec hw)
  simp only [subdivisionWallGen, hex, ↓reduceDIte, heq, hpos, ↓reduceIte]

/-- A wall `w'` of `C` inside a wall `w` of `D` maps to `(FreeGroup.of w)⁻¹` when no vector makes
both coorientations positive. -/
theorem subdivisionWallGen_of_subset_of_not_pos {C D : FinitePolyhedralComplex h}
    (νC : C.walls → V →ₗ[ℝ] ℝ) (νD : D.walls → V →ₗ[ℝ] ℝ) {w' : C.walls} {w : D.walls}
    (hw : w'.val ⊆ w.val) (hneg : ¬∃ v : V, 0 < νC w' v ∧ 0 < νD w v) :
    subdivisionWallGen νC νD w' = (FreeGroup.of w)⁻¹ := by
  classical
  obtain ⟨hw'c, hw'd⟩ := mem_cellsOfCodimension.mp w'.property
  have hex : ∃ u : D.walls, w'.val ⊆ u.val := ⟨w, hw⟩
  have heq : hex.choose = w := Subtype.ext
    (D.eq_of_mem_cellsOfCodimension_of_subset (C.nonempty w'.val hw'c) hw'd
      hex.choose.property w.property hex.choose_spec hw)
  simp only [subdivisionWallGen, hex, ↓reduceDIte, heq, hneg, ↓reduceIte]

private theorem exists_ne_zero_smul_eq_of_ker_eq {W : Type*} [AddCommGroup W] [Module ℝ W]
    {f g : W →ₗ[ℝ] ℝ} (hker : LinearMap.ker f = LinearMap.ker g) :
    ∃ c : ℝ, c ≠ 0 ∧ f = c • g := by
  by_cases hg : g = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    have hf : f = 0 := LinearMap.ker_eq_top.mp (by rw [hker, hg, LinearMap.ker_zero])
    simp [hf, hg]
  · obtain ⟨v₀, hv₀⟩ : ∃ v₀, g v₀ ≠ 0 := by
      by_contra! h0
      exact hg (LinearMap.ext h0)
    refine ⟨f v₀ / g v₀, fun hc => hv₀ (LinearMap.mem_ker.mp
      (hker ▸ LinearMap.mem_ker.mpr ((div_eq_zero_iff.mp hc).resolve_right hv₀))),
      LinearMap.ext fun v => ?_⟩
    have hmem : v - (g v / g v₀) • v₀ ∈ LinearMap.ker g := by
      simp [LinearMap.mem_ker, div_mul_cancel₀ _ hv₀]
    have hfmem : f (v - (g v / g v₀) • v₀) = 0 := LinearMap.mem_ker.mp (hker.symm ▸ hmem)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hfmem
    rw [LinearMap.smul_apply, smul_eq_mul, hfmem]
    ring

/-- When `νC w'` is a positive multiple of a nonzero functional `νD w` on a containing wall `w`,
`subdivisionWallGen` returns `FreeGroup.of w`. -/
theorem subdivisionWallGen_of_subset_of_smul_pos {C D : FinitePolyhedralComplex h}
    (νC : C.walls → V →ₗ[ℝ] ℝ) (νD : D.walls → V →ₗ[ℝ] ℝ)
    {w' : C.walls} {w : D.walls} (hνD : νD w ≠ 0)
    (hw : w'.val ⊆ w.val) {c : ℝ} (hc : 0 < c)
    (hν : νC w' = c • νD w) :
    subdivisionWallGen νC νD w' = FreeGroup.of w := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, νD w v₀ ≠ 0 := by
    by_contra! h0
    exact hνD (LinearMap.ext h0)
  refine subdivisionWallGen_of_subset_of_pos νC νD hw ?_
  rcases lt_or_gt_of_ne hv₀ with hneg | hpos
  · refine ⟨-v₀, ?_, by simpa using neg_pos.mpr hneg⟩
    rw [hν, LinearMap.smul_apply, smul_eq_mul, map_neg]
    exact mul_pos hc (neg_pos.mpr hneg)
  · refine ⟨v₀, ?_, hpos⟩
    rw [hν, LinearMap.smul_apply, smul_eq_mul]
    exact mul_pos hc hpos

/-- When `νC w'` is a negative multiple of `νD w` on a containing wall `w`, `subdivisionWallGen`
returns `(FreeGroup.of w)⁻¹`. -/
theorem subdivisionWallGen_of_subset_of_smul_neg {C D : FinitePolyhedralComplex h}
    (νC : C.walls → V →ₗ[ℝ] ℝ) (νD : D.walls → V →ₗ[ℝ] ℝ)
    {w' : C.walls} {w : D.walls} (hw : w'.val ⊆ w.val) {c : ℝ} (hc : c < 0)
    (hν : νC w' = c • νD w) :
    subdivisionWallGen νC νD w' = (FreeGroup.of w)⁻¹ := by
  refine subdivisionWallGen_of_subset_of_not_pos νC νD hw ?_
  rintro ⟨v, hvC, hvD⟩
  rw [hν, LinearMap.smul_apply, smul_eq_mul] at hvC
  linarith [mul_neg_of_neg_of_pos hc hvD]

private theorem subdivisionWallGen_zpow_eq {C D : FinitePolyhedralComplex h}
    (νC : C.walls → V →ₗ[ℝ] ℝ) (νD : D.walls → V →ₗ[ℝ] ℝ)
    {w' : C.walls} {w : D.walls}
    (hνC : LinearMap.ker (νC w') = (affineSpan ℝ w'.val).direction)
    (hνD : LinearMap.ker (νD w) = (affineSpan ℝ w.val).direction)
    (hw : w'.val ⊆ w.val) {v : V} (hv0 : νD w v ≠ 0) :
    subdivisionWallGen νC νD w' ^ (if 0 < νC w' v then (-1 : ℤ) else 1) =
      FreeGroup.of w ^ (if 0 < νD w v then (-1 : ℤ) else 1) := by
  obtain ⟨hw'c, hw'd⟩ := mem_cellsOfCodimension.mp w'.property
  have hsp := D.affineSpan_eq_of_mem_cellsOfCodimension_of_subset
    (C.nonempty w'.val hw'c) hw'd w.property hw
  obtain ⟨c, hc0, hνeq⟩ := exists_ne_zero_smul_eq_of_ker_eq
    ((hνC.trans (congrArg AffineSubspace.direction hsp)).trans hνD.symm)
  rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
  · rw [subdivisionWallGen_of_subset_of_smul_neg νC νD hw hcneg hνeq, hνeq,
      LinearMap.smul_apply, smul_eq_mul]
    rcases lt_or_gt_of_ne hv0 with hvneg | hvpos
    · simp only [mul_pos_of_neg_of_neg hcneg hvneg, ↓reduceIte, not_lt.mpr hvneg.le,
        zpow_neg_one, inv_inv, zpow_one]
    · simp only [not_lt.mpr (mul_neg_of_neg_of_pos hcneg hvpos).le, ↓reduceIte, hvpos,
        zpow_one, zpow_neg_one]
  · rw [subdivisionWallGen_of_subset_of_smul_pos νC νD (fun h0 => hv0 (by simp [h0]))
      hw hcpos hνeq, hνeq, LinearMap.smul_apply, smul_eq_mul]
    simp only [mul_pos_iff_of_pos_left hcpos]

end SubdivisionGen

section Subdivision

variable {C D : FinitePolyhedralComplex h}

/-- In a subdivision `C` of `D`, the union of the walls of `D` is contained in the union of the
walls of `C`. -/
theorem IsSubdivision.iUnion_walls_subset (hCD : C.IsSubdivision D) :
    (⋃ w : D.walls, w.val) ⊆ ⋃ w' : C.walls, w'.val := by
  intro z hz
  obtain ⟨w, hzw⟩ := mem_iUnion.mp hz
  rw [hCD.eq_biUnion_cellsOfCodimension w.property] at hzw
  simp only [mem_iUnion] at hzw
  obtain ⟨w', hw', -, hzw'⟩ := hzw
  exact mem_iUnion.mpr ⟨⟨w', hw'⟩, hzw'⟩

/-- Subdividing a finite polyhedral complex can only enlarge the singular support of its wall
family. -/
theorem IsSubdivision.singularSupport_walls_subset (hCD : C.IsSubdivision D) :
    singularSupport (Subtype.val : D.walls → Set V) ⊆
      singularSupport (Subtype.val : C.walls → Set V) := by
  intro z hz
  rcases mem_singularSupport.mp hz with ⟨w, hzw⟩ | ⟨w₁, w₂, hdir, hzw₁, hzw₂⟩
  · have hwcl : IsClosed w.val :=
      (D.isConvexPolyhedron (mem_cellsOfCodimension.mp w.property).1).isClosed
    rw [← hwcl.sdiff_intrinsicInterior] at hzw
    obtain ⟨hzw, hznot⟩ := hzw
    have hzw' := hzw
    rw [hCD.eq_biUnion_cellsOfCodimension w.property] at hzw'
    simp only [mem_iUnion] at hzw'
    obtain ⟨w', hw'm, hw'w, hzw'⟩ := hzw'
    obtain ⟨hw'c, hw'd⟩ := mem_cellsOfCodimension.mp hw'm
    have hzn' : z ∉ intrinsicInterior ℝ w' := fun hzi =>
      hznot (D.intrinsicInterior_subset_of_mem_cellsOfCodimension_of_subset
        hw'd w.property hw'w hzi)
    have hfr : z ∈ intrinsicFrontier ℝ w' := by
      rw [← (C.isConvexPolyhedron hw'c).isClosed.sdiff_intrinsicInterior]
      exact ⟨hzw', hzn'⟩
    exact mem_singularSupport.mpr (Or.inl ⟨⟨w', hw'm⟩, hfr⟩)
  · rw [hCD.eq_biUnion_cellsOfCodimension w₁.property] at hzw₁
    rw [hCD.eq_biUnion_cellsOfCodimension w₂.property] at hzw₂
    simp only [mem_iUnion] at hzw₁ hzw₂
    obtain ⟨w₁', hw₁'m, hw₁'w, hzw₁'⟩ := hzw₁
    obtain ⟨w₂', hw₂'m, hw₂'w, hzw₂'⟩ := hzw₂
    obtain ⟨hw₁'c, hw₁'d⟩ := mem_cellsOfCodimension.mp hw₁'m
    obtain ⟨hw₂'c, hw₂'d⟩ := mem_cellsOfCodimension.mp hw₂'m
    have hsp₁ := D.affineSpan_eq_of_mem_cellsOfCodimension_of_subset
      (C.nonempty w₁' hw₁'c) hw₁'d w₁.property hw₁'w
    have hsp₂ := D.affineSpan_eq_of_mem_cellsOfCodimension_of_subset
      (C.nonempty w₂' hw₂'c) hw₂'d w₂.property hw₂'w
    exact mem_singularSupport.mpr
      (Or.inr ⟨⟨w₁', hw₁'m⟩, ⟨w₂', hw₂'m⟩, by rwa [hsp₁, hsp₂], hzw₁', hzw₂'⟩)

/-- An allowed vertex for the walls of a subdivision `C` of `D` is also off every wall of `D`. -/
abbrev IsSubdivision.wallComplementMap (hCD : C.IsSubdivision D)
    (x : WallComplement (Subtype.val : C.walls → Set V)) :
    WallComplement (Subtype.val : D.walls → Set V) where
  val := x.val
  notMem w hxw := by
    obtain ⟨w', hw'⟩ := mem_iUnion.mp (hCD.iUnion_walls_subset (mem_iUnion.mpr ⟨w, hxw⟩))
    exact x.notMem w' hw'

/-- Crossing a wall `w` of `D` at parameter `t` is equivalent to crossing some wall `w'` of the
subdivision `C` contained in `w` at parameter `t`. -/
theorem IsSubdivision.mem_crossings_wallComplementMap (hCD : C.IsSubdivision D)
    {x y : WallComplement (Subtype.val : C.walls → Set V)} (w : D.walls) (t : ℝ) :
    (w, t) ∈ WallComplement.crossings (hCD.wallComplementMap x) (hCD.wallComplementMap y) ↔
      ∃ w' : C.walls, w'.val ⊆ w.val ∧ (w', t) ∈ WallComplement.crossings x y := by
  simp only [WallComplement.mem_crossings]
  constructor
  · rintro ⟨ht, hzw⟩
    rw [hCD.eq_biUnion_cellsOfCodimension w.property] at hzw
    simp only [mem_iUnion] at hzw
    obtain ⟨w', hw'm, hw'w, hzw'⟩ := hzw
    exact ⟨⟨w', hw'm⟩, hw'w, ht, hzw'⟩
  · rintro ⟨w', hw'w, ht, hzw'⟩
    exact ⟨ht, hw'w hzw'⟩

/-- An admissible segment for the walls of a subdivision `C` of `D` is admissible for the walls of
`D`. -/
theorem IsSubdivision.admissibleSegment_walls (hCD : C.IsSubdivision D)
    {x y : WallComplement (Subtype.val : C.walls → Set V)}
    (e : WallComplement.AdmissibleSegment x y) :
    WallComplement.AdmissibleSegment (hCD.wallComplementMap x) (hCD.wallComplementMap y) where
  transverse w := by
    rintro ⟨t, ht, htw⟩
    obtain ⟨w', hw'w, hw't⟩ := (hCD.mem_crossings_wallComplementMap w t).mp
      ((WallComplement.mem_crossings _ _ w t).mpr ⟨ht, htw⟩)
    obtain ⟨hw'c, hw'd⟩ := mem_cellsOfCodimension.mp w'.property
    rw [← D.affineSpan_eq_of_mem_cellsOfCodimension_of_subset
      (C.nonempty w'.val hw'c) hw'd w.property hw'w]
    exact e.transverse w' ⟨t, (WallComplement.mem_crossings x y w' t).mp hw't⟩
  regular t ht hsing := e.regular t ht (hCD.singularSupport_walls_subset hsing)

/-- Quiver prefunctor descending allowed vertices and admissible segments from the walls of a
subdivision `C` to the walls of `D`. -/
abbrev IsSubdivision.wallsPrefunctor (hCD : C.IsSubdivision D) :
    WallComplement (Subtype.val : C.walls → Set V) ⥤q
      WallComplement (Subtype.val : D.walls → Set V) where
  obj := hCD.wallComplementMap
  map e := ⟨hCD.admissibleSegment_walls e.down⟩

/-- Descending segments along a complex subdivision commutes with segment reversal. -/
instance (hCD : C.IsSubdivision D) : hCD.wallsPrefunctor.MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Descending an admissible polygonal path along a complex subdivision preserves its continuous
realization. -/
@[simp]
theorem IsSubdivision.toContinuousPath_wallsPrefunctor (hCD : C.IsSubdivision D)
    {x y : WallComplement (Subtype.val : C.walls → Set V)} (p : AdmissiblePLPath x y) :
    ((hCD.wallsPrefunctor).mapPath p).toContinuousPath = p.toContinuousPath := by
  induction p with
  | nil => simp
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Quiver.Path.toContinuousPath_cons, ih]

private theorem IsSubdivision.lift_subdivisionWallGen_crossingEventWord (hCD : C.IsSubdivision D)
    (νC : C.walls → V →ₗ[ℝ] ℝ) (νD : D.walls → V →ₗ[ℝ] ℝ)
    (hνC : ∀ w' : C.walls, LinearMap.ker (νC w') = (affineSpan ℝ w'.val).direction)
    (hνD : ∀ w : D.walls, LinearMap.ker (νD w) = (affineSpan ℝ w.val).direction)
    {x y : WallComplement (Subtype.val : C.walls → Set V)} (e : x ⟶ y) (t : ℝ) :
    FreeGroup.lift (subdivisionWallGen νC νD)
      (WallComplement.crossingEventWord νC C.pairwise_disjoint_intrinsicInterior_walls e t) =
      WallComplement.crossingEventWord νD D.pairwise_disjoint_intrinsicInterior_walls
        (hCD.wallsPrefunctor.map e) t := by
  let hdisjC := C.pairwise_disjoint_intrinsicInterior_walls
  let hdisjD := D.pairwise_disjoint_intrinsicInterior_walls
  let eD := hCD.wallsPrefunctor.map e
  rcases (WallComplement.signedCrossingEvent νC x y t).eq_empty_or_nonempty with hemp |
      ⟨⟨w', s'⟩, hw's⟩
  · rw [WallComplement.crossingEventWord_empty νC hdisjC e t hemp, map_one, eq_comm]
    refine WallComplement.crossingEventWord_empty νD hdisjD eD t
      (Finset.eq_empty_iff_forall_notMem.mpr fun ⟨w, s⟩ hws => ?_)
    obtain ⟨hwt, -⟩ := (WallComplement.mem_signedCrossingEvent νD _ _ t w s).mp hws
    obtain ⟨w₁, -, hw₁t⟩ := (hCD.mem_crossings_wallComplementMap w t).mp hwt
    exact Finset.notMem_empty _ (hemp ▸
      (WallComplement.mem_signedCrossingEvent νC x y t w₁ _).mpr ⟨hw₁t, rfl⟩)
  · have hsing : WallComplement.signedCrossingEvent νC x y t = {(w', s')} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hw's, fun b hb => WallComplement.subsingleton_signedCrossingEvent νC hdisjC e t hb hw's⟩
    obtain ⟨hw't, rfl⟩ := (WallComplement.mem_signedCrossingEvent νC x y t w' s').mp hw's
    obtain ⟨ht, hzw'⟩ := (WallComplement.mem_crossings x y w' t).mp hw't
    rw [WallComplement.crossingEventWord_singleton νC hdisjC e t _ hsing, map_zpow,
      FreeGroup.lift_apply_of]
    by_cases hex : ∃ w : D.walls, w'.val ⊆ w.val
    · obtain ⟨w, hw⟩ := hex
      have hwt := (hCD.mem_crossings_wallComplementMap w t).mpr ⟨w', hw, hw't⟩
      have hsingD : WallComplement.signedCrossingEvent νD
          (hCD.wallComplementMap x) (hCD.wallComplementMap y) t =
          {(w, if 0 < νD w (y.val - x.val) then -1 else 1)} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr
          ⟨(WallComplement.mem_signedCrossingEvent νD _ _ t w _).mpr ⟨hwt, rfl⟩,
            fun ⟨u, r⟩ hur => ?_⟩
        obtain ⟨hut, rfl⟩ := (WallComplement.mem_signedCrossingEvent νD _ _ t u r).mp hur
        obtain rfl : u = w := WallComplement.subsingleton_crossingWalls hdisjD eD t
          ((WallComplement.mem_crossingWalls _ _ t u).mpr hut)
          ((WallComplement.mem_crossingWalls _ _ t w).mpr hwt)
        rfl
      rw [WallComplement.crossingEventWord_singleton νD hdisjD eD t _ hsingD]
      exact subdivisionWallGen_zpow_eq νC νD (hνC w') (hνD w) hw fun hz =>
        eD.down.transverse w ⟨t, ht, hw hzw'⟩ ((hνD w) ▸ LinearMap.mem_ker.mpr hz)
    · rw [subdivisionWallGen_of_not_exists νC νD hex, one_zpow, eq_comm]
      refine WallComplement.crossingEventWord_empty νD hdisjD eD t
        (Finset.eq_empty_iff_forall_notMem.mpr fun ⟨w, s⟩ hws => ?_)
      obtain ⟨hwt, -⟩ := (WallComplement.mem_signedCrossingEvent νD _ _ t w s).mp hws
      obtain ⟨w'', hw''w, hw''t⟩ := (hCD.mem_crossings_wallComplementMap w t).mp hwt
      obtain ⟨-, hzw''⟩ := (WallComplement.mem_crossings x y w'' t).mp hw''t
      have hzint := (e.down.crossing_mem_intrinsicInterior ht hzw').2
      have hsub : w'.val ⊆ w''.val := C.subset_of_mem_intrinsicInterior
        (mem_cellsOfCodimension.mp w'.property).1 (mem_cellsOfCodimension.mp w''.property).1
        hzint hzw''
      exact hex ⟨w, hsub.trans hw''w⟩

/-- Subdividing a complex `D` into `C` maps the crossing word of any admissible polygonal path on
`C.walls` to the crossing word of the same path on `D.walls`, sending each wall of `C` inside a
wall `w` of `D` to `FreeGroup.of w` (or `(FreeGroup.of w)⁻¹` when coorientations disagree) and
sending every newly introduced wall of `C` to `1`. -/
theorem IsSubdivision.lift_subdivisionWallGen_crossingWord (hCD : C.IsSubdivision D)
    (νC : C.walls → V →ₗ[ℝ] ℝ) (νD : D.walls → V →ₗ[ℝ] ℝ)
    (hνC : ∀ w' : C.walls, LinearMap.ker (νC w') = (affineSpan ℝ w'.val).direction)
    (hνD : ∀ w : D.walls, LinearMap.ker (νD w) = (affineSpan ℝ w.val).direction)
    {x y : WallComplement (Subtype.val : C.walls → Set V)} (p : AdmissiblePLPath x y) :
    FreeGroup.lift (subdivisionWallGen νC νD)
      (p.crossingWord νC C.pairwise_disjoint_intrinsicInterior_walls) =
      ((hCD.wallsPrefunctor).mapPath p).crossingWord νD
        D.pairwise_disjoint_intrinsicInterior_walls := by
  have hseg {u v : WallComplement (Subtype.val : C.walls → Set V)} (e : u ⟶ v) :
      FreeGroup.lift (subdivisionWallGen νC νD)
        (WallComplement.segmentCrossingWord νC C.pairwise_disjoint_intrinsicInterior_walls e) =
        WallComplement.segmentCrossingWord νD D.pairwise_disjoint_intrinsicInterior_walls
          (hCD.wallsPrefunctor.map e) := by
    have hcover : ∀ t ∈ WallComplement.orderedCrossingTimes (hCD.wallsPrefunctor.map e),
        t ∈ WallComplement.orderedCrossingTimes e := by
      intro t ht
      obtain ⟨w, hwt⟩ := (WallComplement.mem_orderedCrossingTimes _ t).mp ht
      obtain ⟨w', -, hw't⟩ := (hCD.mem_crossings_wallComplementMap w t).mp hwt
      exact (WallComplement.mem_orderedCrossingTimes e t).mpr ⟨w', hw't⟩
    rw [WallComplement.segmentCrossingWord_eq_prod_of_crossingTimes νD
      D.pairwise_disjoint_intrinsicInterior_walls (hCD.wallsPrefunctor.map e)
      (WallComplement.orderedCrossingTimes e) (WallComplement.pairwise_orderedCrossingTimes e)
      hcover, WallComplement.segmentCrossingWord_def, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun t _ =>
      hCD.lift_subdivisionWallGen_crossingEventWord νC νD hνC hνD e t)
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Prefunctor.mapPath_cons, Quiver.Path.crossingWord_cons, Quiver.Path.crossingWord_cons,
      map_mul, ih, hseg]

end Subdivision

/-! ### Integral affine transport -/

section IntegralAffine

variable {N' U : Type*} [AddCommGroup N'] [NormedAddCommGroup U] [NormedSpace ℝ U]
  {i' : N' →+ U} {h' : Toric.IsIntegralLattice i'}

/-- Carrier equality expressing an image wall of `C.image e` via `e.toContinuousAffineEquiv`. -/
theorem coe_wallsEquivImage_eq_toContinuousAffineEquiv_image (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (w : C.walls) :
    (C.wallsEquivImage e w : Set U) = ⇑e.toContinuousAffineEquiv '' w.val := by
  simp

/-- Quiver prefunctor transporting allowed vertices and admissible segments from the walls of a
finite polyhedral complex `C` to the walls of its image `C.image e` under an integral affine
equivalence `e`. -/
abbrev wallsImagePrefunctor (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') :
    WallComplement (Subtype.val : C.walls → Set V) ⥤q
      WallComplement (Subtype.val : (C.image e).walls → Set U) where
  obj x := (x.map e.toContinuousAffineEquiv).reindex (C.wallsEquivImage e)
    (C.coe_wallsEquivImage_eq_toContinuousAffineEquiv_image e)
  map a := ⟨(a.down.map e.toContinuousAffineEquiv).reindex (C.wallsEquivImage e)
    (C.coe_wallsEquivImage_eq_toContinuousAffineEquiv_image e)⟩

/-- Integral affine transport of wall-complement segments commutes with segment reversal. -/
instance (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') :
    (C.wallsImagePrefunctor e).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Transporting a polygonal path by `wallsImagePrefunctor` factors as continuous affine transport
followed by carrier reindexing along `C.wallsEquivImage e`. -/
theorem wallsImagePrefunctor_mapPath (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h')
    {x y : WallComplement (Subtype.val : C.walls → Set V)} (p : AdmissiblePLPath x y) :
    (C.wallsImagePrefunctor e).mapPath p =
      (WallComplement.reindexPrefunctor (C.wallsEquivImage e)
        (C.coe_wallsEquivImage_eq_toContinuousAffineEquiv_image e)).mapPath
        (p.affineMap e.toContinuousAffineEquiv) := by
  induction p with
  | nil => simp
  | cons p a ih => simp only [Prefunctor.mapPath_cons, Quiver.Path.affineMap_cons, ih]

/-- The continuous realization of a path transported by `wallsImagePrefunctor` is the image of its
continuous realization under `e`. -/
@[simp]
theorem toContinuousPath_wallsImagePrefunctor (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h')
    {x y : WallComplement (Subtype.val : C.walls → Set V)} (p : AdmissiblePLPath x y) :
    ((C.wallsImagePrefunctor e).mapPath p).toContinuousPath =
      p.toContinuousPath.map e.toContinuousAffineEquiv.continuous := by
  rw [C.wallsImagePrefunctor_mapPath e p, Quiver.Path.toContinuousPath_reindexPrefunctor,
    p.toContinuousPath_affineMap]

/-- Transporting an admissible polygonal path on `C.walls` by an `IntegralAffineEquiv` `e` yields
an admissible polygonal path on `(C.image e).walls` whose crossing word, with coorientations
pulled back along `e.toAffineEquiv.linear.symm`, is the image under `FreeGroup.map` of the induced
wall bijection `C.wallsEquivImage e`. -/
theorem crossingWord_wallsImagePrefunctor (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y : WallComplement (Subtype.val : C.walls → Set V)} (p : AdmissiblePLPath x y) :
    ((C.wallsImagePrefunctor e).mapPath p).crossingWord
      (fun w' => (ν ((C.wallsEquivImage e).symm w')).comp
        e.toAffineEquiv.linear.symm.toLinearMap)
      (C.image e).pairwise_disjoint_intrinsicInterior_walls =
      FreeGroup.map (C.wallsEquivImage e)
        (p.crossingWord ν C.pairwise_disjoint_intrinsicInterior_walls) := by
  have haff : e.toContinuousAffineEquiv.toAffineEquiv = e.toAffineEquiv :=
    AffineEquiv.ext fun v => by simp
  have hνeq : (fun w : C.walls => (ν w).comp e.toAffineEquiv.linear.symm.toLinearMap) =
      fun w => (ν w).comp e.toContinuousAffineEquiv.toAffineEquiv.linear.symm.toLinearMap := by
    rw [haff]
  rw [C.wallsImagePrefunctor_mapPath e p]
  have heq := Quiver.Path.crossingWord_reindexPrefunctor
    (fun w' => (ν ((C.wallsEquivImage e).symm w')).comp
      e.toAffineEquiv.linear.symm.toLinearMap)
    (WallComplement.pairwise_disjoint_intrinsicInterior_image
      C.pairwise_disjoint_intrinsicInterior_walls e.toContinuousAffineEquiv)
    (p.affineMap e.toContinuousAffineEquiv) (C.wallsEquivImage e)
    (C.coe_wallsEquivImage_eq_toContinuousAffineEquiv_image e)
  simp only [Equiv.symm_apply_apply] at heq
  rw [hνeq] at heq
  exact heq.trans (congrArg (FreeGroup.map (C.wallsEquivImage e))
    (p.crossingWord_affineMap ν C.pairwise_disjoint_intrinsicInterior_walls
      e.toContinuousAffineEquiv))

end IntegralAffine

end TauCeti.FinitePolyhedralComplex
