/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Intrinsic
public import TauCeti.Analysis.Normed.Affine.Generic
public import TauCeti.Geometry.Convex.PolyhedralComplex.Map

/-!
# Cell covering and codimension transport for polyhedral subdivisions

When a finite polyhedral complex `C` subdivides `D`, every cell of `D` is covered by the cells of
`C` contained in it that have the same affine dimension (`IsSubdivision.eq_biUnion_cells_of_mem`).
Cells of strictly smaller dimension in `C` have proper affine spans inside `affineSpan ℝ P`, so by
`AffineSubspace.exists_direction_le_of_forall_mem` they cannot cover any neighbourhood around a
relative interior point of `P`; closedness of the full-dimensional pieces in `P` and density of
`intrinsicInterior ℝ P` in `P` then cover all of `P`. In particular, each cell of `D` of ambient
codimension `k` (such as a wall for `k = 1` or a joint for `k = 2`) equals the union of the
codimension-`k` cells of `C` contained in it (`IsSubdivision.eq_biUnion_cellsOfCodimension`).

Conversely, in any finite polyhedral complex `D`, a nonempty subset of ambient codimension `k`
inside a codimension-`k` cell has the same affine span
(`affineSpan_eq_of_mem_cellsOfCodimension_of_subset`), and at most one codimension-`k` cell can
contain it (`eq_of_mem_cellsOfCodimension_of_subset`), because the intersection of two distinct
cells of `D` is a face of strictly smaller dimension. Together with the subcomplex cell inclusion
(`IsSubcomplex.cellsOfCodimensionEmbedding`) and the canonical bijection of codimension-`k` cells
induced by an integral affine equivalence (`cellsOfCodimensionEquivImage`), these facts govern how
wall crossings and cochains behave under subcomplex restriction, complex subdivision, and
coordinate change (following Bridgeland, *Scattering diagrams, Hall algebras and stability
conditions*, §§2.2–2.5, and Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Appendix C.1).
-/

public section

open Set

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i}

/-- Distinct cells, bundled as a subtype, have disjoint relative interiors. -/
theorem pairwise_disjoint_intrinsicInterior_cells (C : FinitePolyhedralComplex h) :
    Pairwise fun P Q : C.cells =>
      Disjoint (intrinsicInterior ℝ P.val) (intrinsicInterior ℝ Q.val) :=
  fun P Q hne => C.disjoint_intrinsicInterior P.property Q.property (Subtype.coe_ne_coe.mpr hne)

/-- Distinct cells of ambient codimension `k` have disjoint relative interiors. -/
theorem pairwise_disjoint_intrinsicInterior_cellsOfCodimension
    (C : FinitePolyhedralComplex h) (k : ℕ) :
    Pairwise fun P Q : C.cellsOfCodimension k =>
      Disjoint (intrinsicInterior ℝ P.val) (intrinsicInterior ℝ Q.val) :=
  fun P Q hne => C.disjoint_intrinsicInterior (mem_cellsOfCodimension.mp P.property).1
    (mem_cellsOfCodimension.mp Q.property).1 (Subtype.coe_ne_coe.mpr hne)

/-- Distinct walls of a finite polyhedral complex have disjoint relative interiors. -/
theorem pairwise_disjoint_intrinsicInterior_walls (C : FinitePolyhedralComplex h) :
    Pairwise fun w₁ w₂ : C.walls =>
      Disjoint (intrinsicInterior ℝ w₁.val) (intrinsicInterior ℝ w₂.val) :=
  C.pairwise_disjoint_intrinsicInterior_cellsOfCodimension 1

/-- Every codimension-`k` cell of a subcomplex is a codimension-`k` cell of the ambient complex. -/
theorem IsSubcomplex.cellsOfCodimension_subset {D C : FinitePolyhedralComplex h}
    (hDC : D.IsSubcomplex C) (k : ℕ) :
    D.cellsOfCodimension k ⊆ C.cellsOfCodimension k := by
  intro P hP
  obtain ⟨hPc, hPd⟩ := mem_cellsOfCodimension.mp hP
  exact mem_cellsOfCodimension.mpr ⟨isSubcomplex_iff.mp hDC hPc, hPd⟩

/-- Inclusion of the codimension-`k` cells of a subcomplex into those of the ambient complex. -/
abbrev IsSubcomplex.cellsOfCodimensionEmbedding {D C : FinitePolyhedralComplex h}
    (hDC : D.IsSubcomplex C) (k : ℕ) :
    D.cellsOfCodimension k ↪ C.cellsOfCodimension k where
  toFun P := ⟨P.val, hDC.cellsOfCodimension_subset k P.property⟩
  inj' _ _ hPQ := Subtype.ext (Subtype.mk.inj hPQ)

/-- Subcomplex inclusion preserves the underlying cell carrier. -/
@[simp]
theorem IsSubcomplex.coe_cellsOfCodimensionEmbedding_apply {D C : FinitePolyhedralComplex h}
    (hDC : D.IsSubcomplex C) (k : ℕ) (P : D.cellsOfCodimension k) :
    (hDC.cellsOfCodimensionEmbedding k P : Set V) = P.val := (rfl)

/-- Inclusion of the walls of a subcomplex into those of the ambient complex. -/
abbrev IsSubcomplex.wallsEmbedding {D C : FinitePolyhedralComplex h}
    (hDC : D.IsSubcomplex C) : D.walls ↪ C.walls :=
  hDC.cellsOfCodimensionEmbedding 1

/-- If a nonempty set `Q` of ambient codimension `k` lies in a codimension-`k` cell `P` of `D`,
they have the same affine span. -/
theorem affineSpan_eq_of_mem_cellsOfCodimension_of_subset (D : FinitePolyhedralComplex h)
    {k : ℕ} {Q P : Set V} (hQne : Q.Nonempty)
    (hQdim : Module.finrank ℝ (affineSpan ℝ Q).direction + k = Module.finrank ℝ V)
    (hP : P ∈ D.cellsOfCodimension k) (hQP : Q ⊆ P) :
    affineSpan ℝ Q = affineSpan ℝ P := by
  let := h.finiteDimensional
  have hPdim := (mem_cellsOfCodimension.mp hP).2
  obtain ⟨x, hx⟩ := hQne
  refine AffineSubspace.ext_of_direction_eq
    (Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le (affineSpan_mono ℝ hQP)) (by omega))
    ⟨x, subset_affineSpan ℝ Q hx, subset_affineSpan ℝ P (hQP hx)⟩

/-- If a set `Q` of ambient codimension `k` lies in a codimension-`k` cell `P` of `D`, the relative
interior of `Q` lies in the relative interior of `P`. -/
theorem intrinsicInterior_subset_of_mem_cellsOfCodimension_of_subset
    (D : FinitePolyhedralComplex h) {k : ℕ} {Q P : Set V}
    (hQdim : Module.finrank ℝ (affineSpan ℝ Q).direction + k = Module.finrank ℝ V)
    (hP : P ∈ D.cellsOfCodimension k) (hQP : Q ⊆ P) :
    intrinsicInterior ℝ Q ⊆ intrinsicInterior ℝ P := by
  rcases Q.eq_empty_or_nonempty with rfl | hQne
  · simp
  · exact TauCeti.intrinsicInterior_mono_of_affineSpan_eq hQP
      (D.affineSpan_eq_of_mem_cellsOfCodimension_of_subset hQne hQdim hP hQP)

/-- At most one cell of `D` of ambient codimension `k` contains a given nonempty set whose affine
span has codimension `k`. -/
theorem eq_of_mem_cellsOfCodimension_of_subset (D : FinitePolyhedralComplex h)
    {k : ℕ} {Q P₁ P₂ : Set V} (hQne : Q.Nonempty)
    (hQdim : Module.finrank ℝ (affineSpan ℝ Q).direction + k = Module.finrank ℝ V)
    (hP₁ : P₁ ∈ D.cellsOfCodimension k) (hP₂ : P₂ ∈ D.cellsOfCodimension k)
    (hQP₁ : Q ⊆ P₁) (hQP₂ : Q ⊆ P₂) : P₁ = P₂ := by
  let := h.finiteDimensional
  obtain ⟨hP₁c, hP₁d⟩ := mem_cellsOfCodimension.mp hP₁
  obtain ⟨hP₂c, hP₂d⟩ := mem_cellsOfCodimension.mp hP₂
  have hQP : Q ⊆ P₁ ∩ P₂ := subset_inter hQP₁ hQP₂
  have hne : (P₁ ∩ P₂).Nonempty := hQne.mono hQP
  have hinter : P₁ ∩ P₂ ∈ D.cells := D.inter_mem_cells hP₁c hP₂c hne
  have hconv : Convex ℝ (P₁ ∩ P₂) := (D.isConvexPolyhedron hinter).convex
  have hle : Module.finrank ℝ (vectorSpan ℝ Q) ≤ Module.finrank ℝ (vectorSpan ℝ (P₁ ∩ P₂)) :=
    Submodule.finrank_mono (vectorSpan_mono ℝ hQP)
  rw [← direction_affineSpan, ← direction_affineSpan] at hle
  have heq₁ : P₁ ∩ P₂ = P₁ := by
    by_contra hne₁
    have hlt := TauCeti.finrank_vectorSpan_lt_of_disjoint_intrinsicInterior
      hconv hne inter_subset_left (D.disjoint_intrinsicInterior hinter hP₁c hne₁)
    rw [← direction_affineSpan, ← direction_affineSpan] at hlt
    omega
  have heq₂ : P₁ ∩ P₂ = P₂ := by
    by_contra hne₂
    have hlt := TauCeti.finrank_vectorSpan_lt_of_disjoint_intrinsicInterior
      hconv hne inter_subset_right (D.disjoint_intrinsicInterior hinter hP₂c hne₂)
    rw [← direction_affineSpan, ← direction_affineSpan] at hlt
    omega
  exact heq₁.symm.trans heq₂

/-- In a subdivision `C` of `D`, every relative interior point of a cell `P` of `D` belongs to a
cell of `C` contained in `P` of the same affine dimension. -/
private theorem IsSubdivision.intrinsicInterior_subset_biUnion {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) {P : Set V} (hP : P ∈ D.cells) :
    intrinsicInterior ℝ P ⊆
      ⋃ Q ∈ C.cells, ⋃ (_ : Q ⊆ P ∧
        Module.finrank ℝ (affineSpan ℝ Q).direction =
          Module.finrank ℝ (affineSpan ℝ P).direction), Q := by
  let := h.finiteDimensional
  classical
  let d := Module.finrank ℝ (affineSpan ℝ P).direction
  let Ssame := C.cells.filter fun Q => Q ⊆ P ∧ Module.finrank ℝ (affineSpan ℝ Q).direction = d
  let Slow := C.cells.filter fun Q => Q ⊆ P ∧ Module.finrank ℝ (affineSpan ℝ Q).direction < d
  have hclosed : IsClosed (⋃ Q ∈ Ssame, Q) := Ssame.finite_toSet.isClosed_biUnion fun Q hQ =>
    (C.isConvexPolyhedron (Finset.mem_filter.mp hQ).1).isClosed
  intro x hx
  by_contra hxnot
  have hxnot' : x ∉ ⋃ Q ∈ Ssame, Q := by
    intro hm
    obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp hm
    obtain ⟨hQc, hQP, hQd⟩ := Finset.mem_filter.mp hQ
    exact hxnot (mem_iUnion₂.mpr ⟨Q, hQc, mem_iUnion.mpr ⟨⟨hQP, hQd⟩, hxQ⟩⟩)
  obtain ⟨hxA, hev⟩ := TauCeti.mem_intrinsicInterior_iff_eventually.mp hx
  have hU : {y | y ∈ affineSpan ℝ P → y ∈ P} ∩ (⋃ Q ∈ Ssame, Q)ᶜ ∈ nhds x :=
    Filter.inter_mem hev (hclosed.isOpen_compl.mem_nhds hxnot')
  obtain ⟨⟨Q, hQ⟩, hdir⟩ := AffineSubspace.exists_direction_le_of_forall_mem
    (affineSpan ℝ P) (fun Q : Slow => affineSpan ℝ Q.val) hxA hU fun y hyA ⟨hyP, hynot⟩ => by
      obtain ⟨Q, hQc, hQP, hyQ⟩ := hCD.exists_mem_cells_subset hP (hyP hyA)
      have hle : Module.finrank ℝ (affineSpan ℝ Q).direction ≤ d :=
        Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hQP))
      rcases hle.lt_or_eq with hlt | heq
      · exact ⟨⟨Q, Finset.mem_filter.mpr ⟨hQc, hQP, hlt⟩⟩, subset_affineSpan ℝ Q hyQ⟩
      · exact (hynot (mem_iUnion₂.mpr
          ⟨Q, Finset.mem_filter.mpr ⟨hQc, hQP, heq⟩, hyQ⟩)).elim
  have hlt := (Finset.mem_filter.mp hQ).2.2
  have hge : d ≤ Module.finrank ℝ (affineSpan ℝ Q).direction := Submodule.finrank_mono hdir
  omega

/-- In a subdivision `C` of `D`, every cell `P` of `D` equals the union of the cells of `C`
contained in `P` of the same affine dimension. -/
theorem IsSubdivision.eq_biUnion_cells_of_mem {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) {P : Set V} (hP : P ∈ D.cells) :
    P = ⋃ Q ∈ C.cells, ⋃ (_ : Q ⊆ P ∧
      Module.finrank ℝ (affineSpan ℝ Q).direction =
        Module.finrank ℝ (affineSpan ℝ P).direction), Q := by
  let := h.finiteDimensional
  refine Subset.antisymm (fun y hy => ?_)
    (iUnion₂_subset fun Q _ => iUnion_subset fun hQ => hQ.1)
  have hconv : Convex ℝ P := (D.isConvexPolyhedron hP).convex
  obtain ⟨x₀, hx₀⟩ := (D.nonempty P hP).intrinsicInterior hconv
  have hclosed : IsClosed (⋃ Q ∈ C.cells, ⋃ (_ : Q ⊆ P ∧
      Module.finrank ℝ (affineSpan ℝ Q).direction =
        Module.finrank ℝ (affineSpan ℝ P).direction), Q) :=
    C.cells.finite_toSet.isClosed_biUnion fun Q hQ =>
      isClosed_iUnion_of_finite fun _ => (C.isConvexPolyhedron hQ).isClosed
  -- Approach `y` along the open segment from `x₀ ∈ intrinsicInterior ℝ P` to `y`.
  have hmem : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Ioo (0 : ℝ) 1),
      AffineMap.lineMap y x₀ t ∈ ⋃ Q ∈ C.cells, ⋃ (_ : Q ⊆ P ∧
        Module.finrank ℝ (affineSpan ℝ Q).direction =
          Module.finrank ℝ (affineSpan ℝ P).direction), Q := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine hCD.intrinsicInterior_subset_biUnion hP
      (hconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
        hx₀ (subset_intrinsicClosure hy) ?_)
    exact ⟨t, 1 - t, ht.1, sub_pos.mpr ht.2, add_sub_cancel _ _, by
      simp only [AffineMap.lineMap_apply_module']; module⟩
  have hcont : Continuous (AffineMap.lineMap y x₀ : ℝ → V) := AffineMap.lineMap_continuous
  have htend : Filter.Tendsto (AffineMap.lineMap y x₀)
      (nhdsWithin (0 : ℝ) (Ioo (0 : ℝ) 1)) (nhds y) := by
    simpa only [AffineMap.lineMap_apply_zero] using
      (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have : (nhdsWithin (0 : ℝ) (Ioo (0 : ℝ) 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by simp [closure_Ioo (zero_ne_one' ℝ)])
  exact hclosed.mem_of_tendsto htend hmem

/-- In a subdivision `C` of `D`, every cell of `D` of ambient codimension `k` equals the union of
the codimension-`k` cells of `C` contained in it. -/
theorem IsSubdivision.eq_biUnion_cellsOfCodimension {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) {k : ℕ} {P : Set V} (hP : P ∈ D.cellsOfCodimension k) :
    P = ⋃ Q ∈ C.cellsOfCodimension k, ⋃ (_ : Q ⊆ P), Q := by
  obtain ⟨hPc, hPd⟩ := mem_cellsOfCodimension.mp hP
  ext x
  simp only [mem_iUnion, mem_cellsOfCodimension]
  constructor
  · intro hx
    rw [hCD.eq_biUnion_cells_of_mem hPc] at hx
    simp only [mem_iUnion] at hx
    obtain ⟨Q, hQc, ⟨hQP, hQd⟩, hxQ⟩ := hx
    exact ⟨Q, ⟨hQc, by omega⟩, hQP, hxQ⟩
  · rintro ⟨Q, -, hQP, hxQ⟩
    exact hQP hxQ

section Image

variable {N' W : Type*} [AddCommGroup N'] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {i' : N' →+ W} {h' : Toric.IsIntegralLattice i'}

/-- An integral affine equivalence induces a bijection between the codimension-`k` cells of `C`
and those of `C.image e`. -/
noncomputable def cellsOfCodimensionEquivImage (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (k : ℕ) :
    C.cellsOfCodimension k ≃ (C.image e).cellsOfCodimension k where
  toFun P := ⟨e '' P.val, (C.mem_cellsOfCodimension_image e k _).mpr ⟨P.val, P.property, rfl⟩⟩
  invFun Q := ⟨e.symm '' Q.val, by
    obtain ⟨P, hP, heq⟩ := (C.mem_cellsOfCodimension_image e k Q.val).mp Q.property
    simpa only [← heq, e.symm_image_image] using hP⟩
  left_inv P := Subtype.ext (e.symm_image_image P.val)
  right_inv Q := Subtype.ext (e.image_symm_image Q.val)

/-- The image of a codimension-`k` cell under `cellsOfCodimensionEquivImage` has carrier
`e '' P`. -/
@[simp]
theorem coe_cellsOfCodimensionEquivImage_apply (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (k : ℕ) (P : C.cellsOfCodimension k) :
    (C.cellsOfCodimensionEquivImage e k P : Set W) = e '' P.val := (rfl)

/-- The inverse of `cellsOfCodimensionEquivImage` acts on carriers by `e.symm '' Q`. -/
@[simp]
theorem coe_cellsOfCodimensionEquivImage_symm_apply (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (k : ℕ) (Q : (C.image e).cellsOfCodimension k) :
    ((C.cellsOfCodimensionEquivImage e k).symm Q : Set V) = e.symm '' Q.val := (rfl)

/-- The bijection of walls induced by an integral affine equivalence. -/
noncomputable abbrev wallsEquivImage (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') : C.walls ≃ (C.image e).walls :=
  C.cellsOfCodimensionEquivImage e 1

end Image

end TauCeti.FinitePolyhedralComplex
