/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.CrossingEvents

/-!
# Affine transport and reindexing of admissible polygonal paths

A continuous affine equivalence sends an admissible segment to an admissible
segment for the image wall family. The resulting quiver prefunctor transports
polygonal paths using Mathlib's `Prefunctor.mapPath`. Wall indices, affine
crossing parameters and edge indices are retained, including repeated visits
and simultaneous crossings. With coorientations pulled back by the inverse
linear part, the ordered signed crossing events are preserved identically.
Bijective wall-index equivalences with pointwise equal carriers likewise
transport admissible paths and act on signed crossing events through `Finset.map`.

The construction uses Mathlib's affine-span transport and
`ContinuousAffineEquiv.intrinsicFrontier_image` to transport singular support.
It provides the geometric and signed-event parts of coordinate transport for wall crossings.

The continuous affine path prefunctor and unsigned `Quiver.Path.crossingEvents_affineMap`
and `Quiver.Path.toContinuousPath_affineMap` theorems are adapted from
`Mei/Geometry/Convex/Polyhedron/AffinePath.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

open Set

namespace TauCeti.WallComplement

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V}

/-- Send an allowed vertex to the complement of the image wall family.
This abbreviation keeps the endpoints of transported continuous paths reducible. -/
abbrev map (x : WallComplement W) (e : V ≃ᴬ[ℝ] U) :
    WallComplement (fun i => e '' W i) where
  val := e x.val
  notMem i := by simpa only [e.injective.mem_set_image] using x.notMem i

@[simp]
theorem map_val (x : WallComplement W) (e : V ≃ᴬ[ℝ] U) :
    (x.map e).val = e x.val := (rfl)

/-- Coordinate transport preserves the entire indexed crossing set, at the same parameters. -/
@[simp]
theorem crossings_map (x y : WallComplement W) (e : V ≃ᴬ[ℝ] U) :
    crossings (x.map e) (y.map e) = crossings x y := by
  ext ⟨i, t⟩
  have hline : e (AffineMap.lineMap x.val y.val t) =
      AffineMap.lineMap (e x.val) (e y.val) t := e.toAffineEquiv.apply_lineMap _ _ _
  simp only [mem_crossings, ← hline, e.injective.mem_set_image]

/-- Affine coordinate changes preserve segment transversality and singular-support avoidance. -/
theorem AdmissibleSegment.map {x y : WallComplement W}
    (a : AdmissibleSegment x y) (e : V ≃ᴬ[ℝ] U) :
    AdmissibleSegment (x.map e) (y.map e) where
  transverse i hi := by
    obtain ⟨t, ht, hi⟩ := hi
    have hmeet := (mem_crossings (x.map e) (y.map e) i t).mpr ⟨ht, hi⟩
    rw [crossings_map, mem_crossings] at hmeet
    have htrans := a.transverse i ⟨t, hmeet⟩
    -- Convert the equivalence coercion to the affine-map coercion used by span transport.
    have hcoe : (e.toAffineEquiv.toAffineMap : V → U) = e := by rfl
    rw [map_val, map_val, ← hcoe, ← AffineSubspace.map_span e.toAffineEquiv.toAffineMap,
      AffineSubspace.map_direction]
    have hv : e.toAffineEquiv.linear (y.val - x.val) = e y.val - e x.val :=
      e.toAffineEquiv.toAffineMap.linear_apply_vsub _ _
    rw [hcoe, ← hv]
    exact fun hh => htrans (by simpa only [AffineEquiv.linear_toAffineMap,
      Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hh)
  regular t ht := by
    have hline : e (AffineMap.lineMap x.val y.val t) =
        AffineMap.lineMap (e x.val) (e y.val) t := e.toAffineEquiv.apply_lineMap _ _ _
    have hs : singularSupport (fun i => e '' W i) = e '' singularSupport W :=
      e.singularSupport_image (Equiv.refl ι) (fun _ => rfl)
    simpa only [map_val, ← hline, hs, e.injective.mem_set_image] using a.regular t ht

/-- Coordinate transport preserves the set of wall indices crossed at each parameter. -/
@[simp]
theorem crossingWalls_map [Finite ι] (x y : WallComplement W) (e : V ≃ᴬ[ℝ] U) (t : ℝ) :
    crossingWalls (x.map e) (y.map e) t = crossingWalls x y t := by
  ext i
  simp

/-- Pulling back coorientations along the inverse linear equivalence preserves each signed event. -/
theorem signedCrossingEvent_map [Finite ι] (ν : ι → V →ₗ[ℝ] ℝ)
    (x y : WallComplement W) (e : V ≃ᴬ[ℝ] U) (t : ℝ) :
    signedCrossingEvent (fun i => (ν i).comp e.toAffineEquiv.linear.symm.toLinearMap)
      (x.map e) (y.map e) t = signedCrossingEvent ν x y t := by
  have hv : e.toAffineEquiv.linear (y.val - x.val) = e y.val - e x.val :=
    e.toAffineEquiv.toAffineMap.linear_apply_vsub _ _
  have hvs : e.toAffineEquiv.linear.symm (e y.val - e x.val) = y.val - x.val := by
    rw [← hv]
    exact e.toAffineEquiv.linear.symm_apply_apply _
  ext ⟨i, s⟩
  simp [hvs]

end TauCeti.WallComplement

namespace TauCeti.WallComplement

section ReindexObj

variable {V ι κ : Type*} {W : ι → Set V}

/-- Reindex an allowed vertex along a bijection of wall indices with equal wall carriers. -/
abbrev reindex (x : WallComplement W) (σ : ι ≃ κ) {W' : κ → Set V}
    (hW : ∀ i, W' (σ i) = W i) : WallComplement W' where
  val := x.val
  notMem k := by
    obtain ⟨i, rfl⟩ := σ.surjective k
    simpa only [hW] using x.notMem i

/-- Reindexing wall carriers preserves the underlying ambient point. -/
@[simp]
theorem reindex_val (x : WallComplement W) (σ : ι ≃ κ) {W' : κ → Set V}
    (hW : ∀ i, W' (σ i) = W i) : (x.reindex σ hW).val = x.val := (rfl)

end ReindexObj

variable {V ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V}

/-- Reindexing wall carriers acts on segment crossings through the index bijection. -/
theorem mem_crossings_reindex (x y : WallComplement W) (σ : ι ≃ κ) {W' : κ → Set V}
    (hW : ∀ i, W' (σ i) = W i) (k : κ) (t : ℝ) :
    (k, t) ∈ crossings (x.reindex σ hW) (y.reindex σ hW) ↔ (σ.symm k, t) ∈ crossings x y := by
  obtain ⟨i, rfl⟩ := σ.surjective k
  simp [hW]

/-- Bijective reindexing of equal wall carriers preserves segment admissibility. -/
theorem AdmissibleSegment.reindex {x y : WallComplement W} (a : AdmissibleSegment x y)
    (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) :
    AdmissibleSegment (x.reindex σ hW) (y.reindex σ hW) where
  transverse k hk := by
    obtain ⟨i, rfl⟩ := σ.surjective k
    simpa only [reindex_val, hW] using a.transverse i (by simpa only [hW] using hk)
  regular t ht := by
    have hs : singularSupport W' = singularSupport W := by
      simpa using (ContinuousAffineEquiv.refl ℝ V).singularSupport_image σ
        (fun i => by simpa using hW i)
    simpa only [reindex_val, hs] using a.regular t ht

/-- Quiver prefunctor transporting allowed vertices and admissible segments along a bijection of
wall indices with equal carriers. -/
abbrev reindexPrefunctor (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) :
    WallComplement W ⥤q WallComplement W' where
  obj x := x.reindex σ hW
  map a := ⟨a.down.reindex σ hW⟩

/-- Reindexing wall carriers preserves reversal of segments. -/
instance (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) :
    (reindexPrefunctor σ hW (W := W)).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Reindexing wall carriers preserves the ordered crossing times of each admissible segment. -/
theorem orderedCrossingTimes_reindex [Finite ι] [Finite κ] {x y : WallComplement W} (a : x ⟶ y)
    (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) :
    orderedCrossingTimes ((reindexPrefunctor σ hW).map a) = orderedCrossingTimes a := by
  refine (pairwise_orderedCrossingTimes _).eq_of_mem_iff (pairwise_orderedCrossingTimes a)
    fun t => ?_
  simp only [mem_orderedCrossingTimes, reindexPrefunctor, mem_crossings_reindex]
  exact ⟨fun ⟨k, hk⟩ => ⟨σ.symm k, hk⟩, fun ⟨i, hi⟩ => ⟨σ i, by simpa using hi⟩⟩

/-- Reindexing wall carriers maps each signed crossing event by the index bijection. -/
@[simp]
theorem signedCrossingEvent_reindex [Finite ι] [Finite κ] (ν' : κ → V →ₗ[ℝ] ℝ)
    (x y : WallComplement W) (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) (t : ℝ) :
    signedCrossingEvent ν' (x.reindex σ hW) (y.reindex σ hW) t =
      (signedCrossingEvent (fun i => ν' (σ i)) x y t).map
        (Equiv.prodCongr σ (Equiv.refl ℤ)).toEmbedding := by
  ext ⟨k, s⟩
  obtain ⟨i, rfl⟩ := σ.surjective k
  simp only [mem_signedCrossingEvent, mem_crossings_reindex, Equiv.symm_apply_apply,
    Finset.mem_map, Prod.exists, Equiv.toEmbedding_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.refl_apply, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · exact fun h => ⟨i, s, h, rfl, rfl⟩
  · rintro ⟨j, r, h, rfl, rfl⟩
    exact h

/-- Reindexing wall carriers maps each segment's signed crossing event list by the index
bijection. -/
theorem segmentCrossingEvents_reindex [Finite ι] [Finite κ] (ν' : κ → V →ₗ[ℝ] ℝ)
    {x y : WallComplement W} (a : x ⟶ y) (σ : ι ≃ κ) {W' : κ → Set V}
    (hW : ∀ i, W' (σ i) = W i) :
    segmentCrossingEvents ν' ((reindexPrefunctor σ hW).map a) =
      (segmentCrossingEvents (fun i => ν' (σ i)) a).map
        (Finset.map (Equiv.prodCongr σ (Equiv.refl ℤ)).toEmbedding) := by
  rw [segmentCrossingEvents_def, orderedCrossingTimes_reindex, segmentCrossingEvents_def,
    List.map_map]
  refine List.map_congr_left fun t _ => ?_
  exact signedCrossingEvent_reindex ν' _ _ σ hW t

end TauCeti.WallComplement

namespace ContinuousAffineEquiv

open TauCeti

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V}

/-- The quiver prefunctor that sends vertices and actual segments to their affine images.
Its object map is reducible so transported edges have the expected endpoints. -/
abbrev wallComplementPrefunctor (e : V ≃ᴬ[ℝ] U) :
    WallComplement W ⥤q WallComplement (fun i => e '' W i) where
  obj x := x.map e
  map a := ⟨a.down.map e⟩

@[simp]
theorem wallComplementPrefunctor_obj (e : V ≃ᴬ[ℝ] U) (x : WallComplement W) :
    (e.wallComplementPrefunctor).obj x = x.map e := (rfl)

/-- Affine transport preserves reversal of segments. -/
instance (e : V ≃ᴬ[ℝ] U) : (e.wallComplementPrefunctor (W := W)).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

end ContinuousAffineEquiv

namespace TauCeti.WallComplement

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [Finite ι] {W : ι → Set V} {x y : WallComplement W}

/-- Coordinate transport preserves the ordered crossing times of an admissible segment. -/
theorem orderedCrossingTimes_map (a : x ⟶ y) (e : V ≃ᴬ[ℝ] U) :
    orderedCrossingTimes (e.wallComplementPrefunctor.map a) = orderedCrossingTimes a := by
  refine (pairwise_orderedCrossingTimes _).eq_of_mem_iff (pairwise_orderedCrossingTimes a)
    fun t => ?_
  simp

/-- Coordinate transport preserves the ordered signed crossing events of a segment under pulled-back
coorientations. -/
theorem segmentCrossingEvents_map (ν : ι → V →ₗ[ℝ] ℝ) (a : x ⟶ y) (e : V ≃ᴬ[ℝ] U) :
    segmentCrossingEvents (fun i => (ν i).comp e.toAffineEquiv.linear.symm.toLinearMap)
      (e.wallComplementPrefunctor.map a) = segmentCrossingEvents ν a := by
  rw [segmentCrossingEvents_def, orderedCrossingTimes_map, segmentCrossingEvents_def]
  exact List.map_congr_left fun t _ => signedCrossingEvent_map ν x y e t

end TauCeti.WallComplement

namespace Quiver.Path

open TauCeti

section AffineMap

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V} {x y z : WallComplement W}

/-- Transport the actual segments of an admissible polygonal path to an image wall family. -/
def affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    AdmissiblePLPath (x.map e) (y.map e) :=
  e.wallComplementPrefunctor.mapPath p

/-- Constant paths remain constant after transport. -/
@[simp]
theorem affineMap_nil (e : V ≃ᴬ[ℝ] U) :
    (nil : AdmissiblePLPath x x).affineMap e = nil := (rfl)

/-- Transport acts on each actual segment in a chain. -/
@[simp]
theorem affineMap_cons (p : AdmissiblePLPath x y) (a : y ⟶ z) (e : V ≃ᴬ[ℝ] U) :
    (p.cons a).affineMap e =
      (p.affineMap e).cons (e.wallComplementPrefunctor.map a) := (rfl)

/-- Affine transport commutes with path concatenation. -/
@[simp]
theorem affineMap_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z)
    (e : V ≃ᴬ[ℝ] U) :
    (p.comp q).affineMap e = (p.affineMap e).comp (q.affineMap e) :=
  Prefunctor.mapPath_comp _ _ _

/-- Transport retains the number of segments. -/
@[simp]
theorem length_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).length = p.length :=
  Prefunctor.length_mapPath _ _

/-- Reversing the transported chain is the transport of the reversed chain. -/
@[simp]
theorem affineMap_reverse (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    p.reverse.affineMap e = (p.affineMap e).reverse := by
  induction p with
  | nil => rfl
  | cons p a ih =>
    simp only [reverse, affineMap_comp, Quiver.Hom.toPath, affineMap_cons,
      affineMap_nil, ih]
    congr 2

/-- Every crossing event retains its edge index, wall index and affine parameter. -/
@[simp]
theorem crossingEvents_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).crossingEvents = p.crossingEvents := by
  induction p with
  | nil => simp
  | cons p a ih =>
    ext ⟨j, i, t⟩
    simp only [affineMap_cons, mem_crossingEvents_cons, ih, length_affineMap,
      WallComplement.crossings_map]

/-- Coordinate transport preserves all polygonal signed crossing events under pulled-back
coorientations. -/
theorem signedCrossingEvents_affineMap [Finite ι] (ν : ι → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).signedCrossingEvents
      (fun i => (ν i).comp e.toAffineEquiv.linear.symm.toLinearMap) =
      p.signedCrossingEvents ν := by
  induction p with
  | nil => simp
  | cons p a ih =>
    rw [affineMap_cons, signedCrossingEvents_cons, signedCrossingEvents_cons, ih,
      WallComplement.segmentCrossingEvents_map]

/-- The continuous realization of a transported chain is the image of its realization. -/
@[simp]
theorem toContinuousPath_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).toContinuousPath = p.toContinuousPath.map e.continuous := by
  induction p with
  | nil => ext t; simp [Path.map_coe]
  | @cons y z p a ih =>
    rw [affineMap_cons, toContinuousPath_cons, toContinuousPath_cons, Path.map_trans, ih]
    congr 1
    ext t
    exact (e.toAffineEquiv.apply_lineMap y.val z.val t).symm

end AffineMap

section Reindex

variable {V ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y : WallComplement W}

/-- Reindexing wall carriers preserves the continuous realization of an admissible polygonal
path. -/
@[simp]
theorem toContinuousPath_reindexPrefunctor (p : AdmissiblePLPath x y) (σ : ι ≃ κ)
    {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) :
    ((WallComplement.reindexPrefunctor σ hW).mapPath p).toContinuousPath =
      p.toContinuousPath := by
  induction p with
  | nil => simp
  | cons p a ih => simp only [Prefunctor.mapPath_cons, toContinuousPath_cons, ih]

/-- Reindexing wall carriers maps all polygonal signed crossing events by the index bijection. -/
@[simp]
theorem signedCrossingEvents_reindexPrefunctor [Finite ι] [Finite κ] (ν' : κ → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) (σ : ι ≃ κ) {W' : κ → Set V} (hW : ∀ i, W' (σ i) = W i) :
    ((WallComplement.reindexPrefunctor σ hW).mapPath p).signedCrossingEvents ν' =
      (p.signedCrossingEvents (fun i => ν' (σ i))).map
        (Finset.map (Equiv.prodCongr σ (Equiv.refl ℤ)).toEmbedding) := by
  induction p with
  | nil => simp
  | cons p a ih =>
    rw [Prefunctor.mapPath_cons, signedCrossingEvents_cons, signedCrossingEvents_cons, ih,
      List.map_append, WallComplement.segmentCrossingEvents_reindex]

end Reindex

end Quiver.Path
