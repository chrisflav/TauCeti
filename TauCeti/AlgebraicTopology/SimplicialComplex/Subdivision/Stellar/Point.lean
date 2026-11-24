/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Link
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite

/-!
# Stellar subdivision at an arbitrary point of a realization

Given an abstract simplicial complex `K` and a point `x₀` of its weak realization that is not a
vertex, starring the unique open simplex carrying `x₀` at a fresh vertex `none : Option ι` yields
a simplicial complex `pointStellarSubdivision K x₀ hx` on `Option ι`. Sending `none` to `x₀` and
each old vertex `some i` to `i` extends linearly to a map on barycentric coordinates that
identifies the two polyhedra bijectively. When `K` has finitely many faces, this map is a
homeomorphism `pointStellarSubdivisionHomeomorph` sending the new vertex to `x₀` while preserving
all old vertices.

Because `pointStellarSubdivision` is built from an injective relabeling followed by a stellar
subdivision at a fresh vertex, it preserves finiteness of faces, finiteness of the vertex type,
and the combinatorial manifold property in every dimension.

## Main definitions

* `Finsupp.pointStellarSubdivisionLinearMap`: linear extension sending `none` to `x₀` and `some i`
  to the `i`-th basis vector.
* `AbstractSimplicialComplex.pointStellarSubdivision`: the stellar subdivision of `K` at the
  carrier of a non-vertex point `x₀ : Realization K`.
* `AbstractSimplicialComplex.pointStellarSubdivisionHomeomorph`: the induced homeomorphism when
  `K` has finitely many faces.

## Main results

* `AbstractSimplicialComplex.bijOn_pointStellarSubdivisionLinearMap`: the linear map restricts to
  a bijection of coordinate polyhedra.
* `AbstractSimplicialComplex.isCombinatorialManifold_pointStellarSubdivision`: combinatorial
  manifolds are preserved in every dimension.
* `AbstractSimplicialComplex.exists_pointStellarSubdivision`: for any finite-face complex `K` and
  any point `x₀ : Realization K`, there is a homeomorphic complex preserving finiteness and
  combinatorial-manifold structure in which all old vertices and `x₀` are vertex images.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (starrings and subdivisions).
-/

public section

noncomputable section

open Set Finset TauCeti PreAbstractSimplicialComplex TauCeti.SetLike

namespace Finsupp

variable {ι : Type*}

/-- The linear map on finitely supported functions sending `none` to `x₀` and `some i` to
`Finsupp.single i 1`. -/
def pointStellarSubdivisionLinearMap (x₀ : ι →₀ ℝ) : (Option ι →₀ ℝ) →ₗ[ℝ] (ι →₀ ℝ) :=
  Finsupp.linearCombination ℝ fun o => Option.elim o x₀ fun i => Finsupp.single i (1 : ℝ)

/-- Coordinate formula for `pointStellarSubdivisionLinearMap`. -/
@[simp]
theorem pointStellarSubdivisionLinearMap_apply (x₀ : ι →₀ ℝ) (y : Option ι →₀ ℝ) (i : ι) :
    pointStellarSubdivisionLinearMap x₀ y i = y none * x₀ i + y (Option.some i) := by
  classical
  let L₁ : (Option ι →₀ ℝ) →ₗ[ℝ] ℝ :=
    (Finsupp.lapply i).comp (pointStellarSubdivisionLinearMap x₀)
  let L₂ : (Option ι →₀ ℝ) →ₗ[ℝ] ℝ :=
    x₀ i • Finsupp.lapply Option.none + Finsupp.lapply (Option.some i)
  have hL : L₁ = L₂ := by
    apply Finsupp.lhom_ext
    intro a r
    cases a with
    | none =>
      simp [L₁, L₂, pointStellarSubdivisionLinearMap, mul_comm]
    | some j =>
      simp only [L₁, L₂, LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
        LinearMap.smul_apply, Finsupp.lapply_apply, pointStellarSubdivisionLinearMap,
        Finsupp.linearCombination_single, Option.elim_some, smul_eq_mul,
        Finsupp.single_apply, Option.some.injEq, Option.some_ne_none, ↓reduceIte]
      split_ifs with h <;> simp [h]
  simpa [L₁, L₂, mul_comm] using DFunLike.congr_fun hL y

/-- `pointStellarSubdivisionLinearMap` sends `none` to `x₀`. -/
@[simp]
theorem pointStellarSubdivisionLinearMap_single_none (x₀ : ι →₀ ℝ) (r : ℝ) :
    pointStellarSubdivisionLinearMap x₀ (Finsupp.single Option.none r) = r • x₀ := by
  simp [pointStellarSubdivisionLinearMap]

/-- `pointStellarSubdivisionLinearMap` fixes old basis vectors. -/
@[simp]
theorem pointStellarSubdivisionLinearMap_single_some (x₀ : ι →₀ ℝ) (i : ι) (r : ℝ) :
    pointStellarSubdivisionLinearMap x₀ (Finsupp.single (Option.some i) r) =
      Finsupp.single i r := by
  ext j
  simp [pointStellarSubdivisionLinearMap]

/-- `pointStellarSubdivisionLinearMap` preserves total barycentric mass when `x₀` has mass `1`. -/
@[simp]
theorem sum_pointStellarSubdivisionLinearMap {x₀ : ι →₀ ℝ}
    (hx₀ : x₀.sum (fun _ r => r) = 1) (y : Option ι →₀ ℝ) :
    (pointStellarSubdivisionLinearMap x₀ y).sum (fun _ r => r) = y.sum (fun _ r => r) := by
  let S₁ : (Option ι →₀ ℝ) →ₗ[ℝ] ℝ :=
    (Finsupp.linearCombination ℝ (fun _ : ι => (1 : ℝ))).comp
      (pointStellarSubdivisionLinearMap x₀)
  let S₂ : (Option ι →₀ ℝ) →ₗ[ℝ] ℝ :=
    Finsupp.linearCombination ℝ (fun _ : Option ι => (1 : ℝ))
  have hS : S₁ = S₂ := by
    apply Finsupp.lhom_ext
    intro a r
    cases a with
    | none =>
      have h : (x₀.sum fun _ c => c) = 1 := hx₀
      simp [S₁, S₂, Finsupp.linearCombination_apply, h]
    | some j =>
      simp [S₁, S₂]
  have hy := DFunLike.congr_fun hS y
  simpa [S₁, S₂, Finsupp.linearCombination_apply] using hy

end Finsupp

namespace AbstractSimplicialComplex

universe u

variable {ι : Type u} [DecidableEq ι]

omit [DecidableEq ι] in
private theorem not_support_subset_singleton_of_notMem_range_vertex
    (K : AbstractSimplicialComplex ι) {x₀ : Realization K} (hx : x₀ ∉ range K.vertex) (i : ι) :
    ¬ x₀.val.support ⊆ {i} := by
  intro hsub
  have hne : x₀.val.support.Nonempty := (K.isRelLowerSet_faces (support_mem K x₀)).1
  have hsing : x₀.val.support = {i} := hne.subset_singleton_iff.mp hsub
  have hsum : x₀.val i = 1 := by
    have hs := Realization.sum_eq_one K x₀
    rwa [Finsupp.sum, hsing, Finset.sum_singleton] at hs
  exact hx ⟨i, ((Realization.eq_vertex_iff K x₀ i).mpr hsum).symm⟩

/-- The stellar subdivision of `K` at the carrier face of a non-vertex point `x₀ : Realization K`,
with vertex type `Option ι` where `none` is the new vertex placed at `x₀`. -/
@[expose]
def pointStellarSubdivision (K : AbstractSimplicialComplex ι) (x₀ : Realization K)
    (hx : x₀ ∉ range K.vertex) : AbstractSimplicialComplex (Option ι) where
  toPreAbstractSimplicialComplex :=
    stellarSubdivision (K.toPreAbstractSimplicialComplex.map some)
      (x₀.val.support.image some) none
  singleton_mem v := by
    change ({v} : Finset (Option ι)) ∈ stellarSubdivision
      (K.toPreAbstractSimplicialComplex.map some) (x₀.val.support.image some) none
    cases v with
    | none =>
      rw [singleton_mem_stellarSubdivision_iff]
      exact mem_map_iff.mpr ⟨x₀.val.support, support_mem K x₀, rfl⟩
    | some i =>
      rw [mem_stellarSubdivision_iff_of_notMem (by simp)]
      refine ⟨singleton_mem_map_iff.mpr ⟨i, K.singleton_mem i, rfl⟩, ?_⟩
      intro hsub
      apply K.not_support_subset_singleton_of_notMem_range_vertex hx i
      intro j hj
      have hj' : some j ∈ ({some i} : Finset (Option ι)) :=
        hsub (Finset.mem_image_of_mem some hj)
      simpa using hj'

/-- The underlying pre-simplicial complex of `pointStellarSubdivision` is the stellar
subdivision at the support face of `x₀`. -/
@[simp]
theorem toPreAbstractSimplicialComplex_pointStellarSubdivision (K : AbstractSimplicialComplex ι)
    (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) :
    (pointStellarSubdivision K x₀ hx).toPreAbstractSimplicialComplex =
      stellarSubdivision (K.toPreAbstractSimplicialComplex.map some)
        (x₀.val.support.image some) none :=
  rfl

/-- `pointStellarSubdivision` preserves finiteness of faces. -/
theorem finite_faces_pointStellarSubdivision {K : AbstractSimplicialComplex ι}
    (hfin : K.faces.Finite) (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) :
    (pointStellarSubdivision K x₀ hx).faces.Finite :=
  finite_faces_stellarSubdivision (hfin.image _)

/-- `pointStellarSubdivision` preserves combinatorial manifolds in every dimension. -/
theorem isCombinatorialManifold_pointStellarSubdivision {K : AbstractSimplicialComplex ι}
    {d : ℕ} (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex d)
    (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) :
    IsCombinatorialManifold (pointStellarSubdivision K x₀ hx).toPreAbstractSimplicialComplex d := by
  have hmap : IsCombinatorialManifold (K.toPreAbstractSimplicialComplex.map some) d :=
    (isCombinatorialManifold_map_iff (Option.some_injective ι)).mpr h
  have hnone : ({none} : Finset (Option ι)) ∉ K.toPreAbstractSimplicialComplex.map some := by
    intro hmem
    obtain ⟨w, -, hw⟩ := singleton_mem_map_iff.mp hmem
    exact Option.some_ne_none w hw
  exact hmap.stellarSubdivision hnone

/-- The linear map placing `none` at `x₀` maps the coordinate polyhedron of
`pointStellarSubdivision K x₀ hx` into the coordinate polyhedron of `K`. -/
theorem mapsTo_pointStellarSubdivisionLinearMap (K : AbstractSimplicialComplex ι)
    (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) :
    MapsTo (Finsupp.pointStellarSubdivisionLinearMap x₀.val)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ)
        (pointStellarSubdivision K x₀ hx).toPreAbstractSimplicialComplex).space
      (standardGeometricComplex K).space := by
  intro y hy
  obtain ⟨hypos, hysum, hysupp⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hy
  rw [mem_standardGeometricComplex_space_iff]
  have hsum : (Finsupp.pointStellarSubdivisionLinearMap x₀.val y).sum (fun _ r => r) = 1 :=
    (Finsupp.sum_pointStellarSubdivisionLinearMap (Realization.sum_eq_one K x₀) y).trans hysum
  refine ⟨fun i => ?_, hsum, ?_⟩
  · rw [Finsupp.pointStellarSubdivisionLinearMap_apply]
    exact add_nonneg (mul_nonneg (hypos none) (Realization.nonneg K x₀ i)) (hypos (some i))
  · rw [toPreAbstractSimplicialComplex_pointStellarSubdivision] at hysupp
    by_cases hnone : none ∈ y.support
    · obtain ⟨τ, hτ, hτeq⟩ :=
        mem_map_iff.mp ((mem_stellarSubdivision_iff.mp hysupp).resolve_left (by simp [hnone])).2.2
      apply K.isRelLowerSet_faces.mem_of_le hτ
      · intro i hi
        have hnz := Finsupp.mem_support_iff.mp hi
        rw [Finsupp.pointStellarSubdivisionLinearMap_apply] at hnz
        have hmem : some i ∈ y.support.erase none ∪ x₀.val.support.image some := by
          by_cases h0 : y (some i) = 0
          · have hyx : y none * x₀.val i ≠ 0 := by simpa [h0] using hnz
            exact Finset.mem_union_right _
              (Finset.mem_image_of_mem some
                (Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hyx)))
          · exact Finset.mem_union_left _
              (Finset.mem_erase.mpr ⟨Option.some_ne_none i, Finsupp.mem_support_iff.mpr h0⟩)
        have hsome : some i ∈ τ.image some := hτeq ▸ hmem
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hsome
        exact Option.some_injective ι hji ▸ hj
      · refine Finsupp.support_nonempty_iff.mpr fun hz => ?_
        simp [hz] at hsum
    · have hy0 : y none = 0 := Finsupp.notMem_support_iff.mp hnone
      obtain ⟨τ, hτ, hτeq⟩ :=
        mem_map_iff.mp ((mem_stellarSubdivision_iff_of_notMem hnone).mp hysupp).1
      have hsupp : (Finsupp.pointStellarSubdivisionLinearMap x₀.val y).support = τ := by
        apply Finset.image_injective (Option.some_injective ι)
        rw [hτeq]
        ext u
        cases u with
        | none => simp [hnone]
        | some i => simp [hy0]
      exact hsupp ▸ hτ

/-- `Finsupp.pointStellarSubdivisionLinearMap x₀.val` is injective on the coordinate polyhedron
of `pointStellarSubdivision K x₀ hx`. -/
theorem injOn_pointStellarSubdivisionLinearMap (K : AbstractSimplicialComplex ι)
    (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) :
    InjOn (Finsupp.pointStellarSubdivisionLinearMap x₀.val)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ)
        (pointStellarSubdivision K x₀ hx).toPreAbstractSimplicialComplex).space := by
  intro y₁ hy₁ y₂ hy₂ heq
  obtain ⟨hy₁pos, -, hy₁supp⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hy₁
  obtain ⟨hy₂pos, -, hy₂supp⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hy₂
  rw [toPreAbstractSimplicialComplex_pointStellarSubdivision] at hy₁supp hy₂supp
  have hnoneσ : (none : Option ι) ∉ x₀.val.support.image some := by simp
  obtain ⟨u₁, hu₁σ, hu₁⟩ := exists_notMem_of_mem_stellarSubdivision hnoneσ hy₁supp
  obtain ⟨u₂, hu₂σ, hu₂⟩ := exists_notMem_of_mem_stellarSubdivision hnoneσ hy₂supp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu₁σ
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu₂σ
  have hxi : 0 < x₀.val i := lt_of_le_of_ne (Realization.nonneg K x₀ i)
    (Finsupp.mem_support_iff.mp hi).symm
  have hxj : 0 < x₀.val j := lt_of_le_of_ne (Realization.nonneg K x₀ j)
    (Finsupp.mem_support_iff.mp hj).symm
  have hy₁i : y₁ (some i) = 0 := Finsupp.notMem_support_iff.mp hu₁
  have hy₂j : y₂ (some j) = 0 := Finsupp.notMem_support_iff.mp hu₂
  have hei := DFunLike.congr_fun heq i
  have hej := DFunLike.congr_fun heq j
  simp only [Finsupp.pointStellarSubdivisionLinearMap_apply, hy₁i, hy₂j, add_zero] at hei hej
  have hnone : y₁ none = y₂ none := by nlinarith [hy₁pos (some j), hy₂pos (some i)]
  ext u
  cases u with
  | none => exact hnone
  | some k =>
    have hek := DFunLike.congr_fun heq k
    simp only [Finsupp.pointStellarSubdivisionLinearMap_apply, hnone] at hek
    exact add_left_cancel hek

/-- `Finsupp.pointStellarSubdivisionLinearMap x₀.val` is surjective onto the coordinate polyhedron
of `K`. -/
theorem surjOn_pointStellarSubdivisionLinearMap (K : AbstractSimplicialComplex ι)
    (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) :
    SurjOn (Finsupp.pointStellarSubdivisionLinearMap x₀.val)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ)
        (pointStellarSubdivision K x₀ hx).toPreAbstractSimplicialComplex).space
      (standardGeometricComplex K).space := by
  intro x hxmem
  obtain ⟨hxpos, hxsum, hxsupp⟩ := mem_standardGeometricComplex_space_iff.mp hxmem
  by_cases hsub : x₀.val.support ⊆ x.support
  · have hσne : x₀.val.support.Nonempty := (K.isRelLowerSet_faces (support_mem K x₀)).1
    obtain ⟨a, ha, hmin⟩ := (x₀.val.support : Set ι).exists_min_image
      (fun i => x i / x₀.val i) x₀.val.support.finite_toSet hσne
    have hxa_pos : 0 < x₀.val a := lt_of_le_of_ne (Realization.nonneg K x₀ a)
      (Finsupp.mem_support_iff.mp ha).symm
    let t : ℝ := x a / x₀.val a
    let y : Option ι →₀ ℝ := Finsupp.single none t + Finsupp.mapDomain some (x - t • x₀.val)
    have hynone : y none = t := by
      simp [y, Finsupp.mapDomain_of_notMem_range]
    have hysome (i : ι) : y (some i) = x i - t * x₀.val i := by
      simp [y, Finsupp.mapDomain_apply_of_injective (Option.some_injective ι)]
    have hypos (u : Option ι) : 0 ≤ y u := by
      cases u with
      | none =>
        rw [hynone]
        exact div_nonneg (hxpos a) hxa_pos.le
      | some i =>
        rw [hysome]
        by_cases hi : i ∈ x₀.val.support
        · have hxi_pos : 0 < x₀.val i := lt_of_le_of_ne (Realization.nonneg K x₀ i)
            (Finsupp.mem_support_iff.mp hi).symm
          exact sub_nonneg.mpr ((le_div_iff₀ hxi_pos).mp (hmin i hi))
        · have hxi0 : x₀.val i = 0 := Finsupp.notMem_support_iff.mp hi
          simpa [hxi0] using hxpos i
    have him : Finsupp.pointStellarSubdivisionLinearMap x₀.val y = x := by
      ext i
      rw [Finsupp.pointStellarSubdivisionLinearMap_apply, hynone, hysome]
      ring
    have hysum : y.sum (fun _ r => r) = 1 := by
      rw [← Finsupp.sum_pointStellarSubdivisionLinearMap (Realization.sum_eq_one K x₀) y, him,
        hxsum]
    have hya : some a ∉ y.support := by
      rw [Finsupp.notMem_support_iff, hysome]
      exact sub_eq_zero.mpr (div_mul_cancel₀ (x a) hxa_pos.ne').symm
    have hysub_x : (x - t • x₀.val).support ⊆ x.support := by
      intro i hi
      by_contra hix
      have hxi : x i = 0 := Finsupp.notMem_support_iff.mp hix
      have hx₀i : x₀.val i = 0 := Finsupp.notMem_support_iff.mp fun h => hix (hsub h)
      exact Finsupp.mem_support_iff.mp hi (by simp [hxi, hx₀i])
    have hyface : y.support ∈ (pointStellarSubdivision K x₀ hx).toPreAbstractSimplicialComplex := by
      rw [toPreAbstractSimplicialComplex_pointStellarSubdivision, mem_stellarSubdivision_iff]
      have herase : y.support.erase none = (x - t • x₀.val).support.image some := by
        ext u
        cases u with
        | none => simp
        | some i =>
          simp only [Finset.mem_erase, ne_eq, Option.some_ne_none, not_false_eq_true,
            Finsupp.mem_support_iff, hysome, true_and, Finset.mem_image, Option.some.injEq,
            exists_eq_right, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul]
      have hnot_sub : ¬ x₀.val.support.image some ⊆ y.support := fun h =>
        hya (h (Finset.mem_image_of_mem some ha))
      by_cases hn : none ∈ y.support
      · refine Or.inr ⟨hn, fun h => hnot_sub (h.trans (Finset.erase_subset _ _)), ?_⟩
        refine mem_map_iff.mpr ⟨(x - t • x₀.val).support ∪ x₀.val.support, ?_, ?_⟩
        · exact K.isRelLowerSet_faces.mem_of_le hxsupp (Finset.union_subset hysub_x hsub)
            (hσne.mono Finset.subset_union_right)
        · rw [herase, Finset.image_union]
      · refine Or.inl ⟨hn, ?_, hnot_sub⟩
        refine mem_map_iff.mpr ⟨(x - t • x₀.val).support, ?_, ?_⟩
        · refine K.isRelLowerSet_faces.mem_of_le hxsupp hysub_x ?_
          rw [Finsupp.support_nonempty_iff]
          intro hzero
          have hyz : y = 0 := by
            ext u
            cases u with
            | none => exact Finsupp.notMem_support_iff.mp hn
            | some i =>
              have := DFunLike.congr_fun hzero i
              simpa [hysome] using this
          simp [hyz] at hysum
        · rw [← Finset.erase_eq_of_notMem hn, herase]
    exact ⟨y, Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr ⟨hypos, hysum, hyface⟩, him⟩
  · let y : Option ι →₀ ℝ := Finsupp.mapDomain some x
    have hynone : y none = 0 := by simp [y, Finsupp.mapDomain_of_notMem_range]
    have hysome (i : ι) : y (some i) = x i := by
      simp [y, Finsupp.mapDomain_apply_of_injective (Option.some_injective ι)]
    have hypos (u : Option ι) : 0 ≤ y u := by
      cases u with
      | none => simp [hynone]
      | some i => simp [hysome, hxpos i]
    have hysum : y.sum (fun _ r => r) = 1 := by
      simpa [y] using (Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl) :
        y.sum (fun _ r => r) = x.sum (fun _ r => r)).trans hxsum
    have hysupp_eq : y.support = x.support.image some := by
      ext u
      cases u with
      | none => simp [hynone]
      | some i => simp [hysome]
    have hyface : y.support ∈ (pointStellarSubdivision K x₀ hx).toPreAbstractSimplicialComplex := by
      rw [toPreAbstractSimplicialComplex_pointStellarSubdivision,
        mem_stellarSubdivision_iff_of_notMem (by simp [hysupp_eq])]
      refine ⟨mem_map_iff.mpr ⟨x.support, hxsupp, hysupp_eq.symm⟩, ?_⟩
      intro h
      apply hsub
      intro i hi
      have hsi : some i ∈ x.support.image some := hysupp_eq ▸ h (Finset.mem_image_of_mem some hi)
      simpa using hsi
    have him : Finsupp.pointStellarSubdivisionLinearMap x₀.val y = x := by
      ext i
      rw [Finsupp.pointStellarSubdivisionLinearMap_apply, hynone, hysome]
      simp
    exact ⟨y, Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr ⟨hypos, hysum, hyface⟩, him⟩

/-- `Finsupp.pointStellarSubdivisionLinearMap x₀.val` restricts to a bijection between the
coordinate polyhedron of `pointStellarSubdivision K x₀ hx` and that of `K`. -/
theorem bijOn_pointStellarSubdivisionLinearMap (K : AbstractSimplicialComplex ι)
    (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) :
    BijOn (Finsupp.pointStellarSubdivisionLinearMap x₀.val)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ)
        (pointStellarSubdivision K x₀ hx).toPreAbstractSimplicialComplex).space
      (standardGeometricComplex K).space :=
  ⟨mapsTo_pointStellarSubdivisionLinearMap K x₀ hx,
    injOn_pointStellarSubdivisionLinearMap K x₀ hx,
    surjOn_pointStellarSubdivisionLinearMap K x₀ hx⟩

/-- When `K` has finitely many faces, `pointStellarSubdivision K x₀ hx` has weak realization
homeomorphic to `Realization K`, sending `none` to `x₀` and `some i` to `K.vertex i`. -/
@[expose]
def pointStellarSubdivisionHomeomorph {K : AbstractSimplicialComplex ι}
    (hfin : K.faces.Finite) (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) :
    Realization (pointStellarSubdivision K x₀ hx) ≃ₜ Realization K := by
  let K' := pointStellarSubdivision K x₀ hx
  have hfin' : K'.faces.Finite := finite_faces_pointStellarSubdivision hfin x₀ hx
  have hbij := bijOn_pointStellarSubdivisionLinearMap K x₀ hx
  have hmem (y : Realization K') :
      y.val ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ)
        K'.toPreAbstractSimplicialComplex).space :=
    Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr
      ⟨Realization.nonneg K' y, Realization.sum_eq_one K' y, support_mem K' y⟩
  let f : Realization K' → Realization K := fun y =>
    ⟨Finsupp.pointStellarSubdivisionLinearMap x₀.val y.val, hbij.mapsTo (hmem y)⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · intro y₁ y₂ h
      exact Subtype.ext (hbij.injOn (hmem y₁) (hmem y₂) (congrArg Subtype.val h))
    · intro z
      obtain ⟨y, hy, hyz⟩ := hbij.surjOn z.property
      obtain ⟨hypos, hysum, hyface⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hy
      exact ⟨⟨y, mem_standardGeometricComplex_space_iff.mpr ⟨hypos, hysum, hyface⟩⟩,
        Subtype.ext hyz⟩
  have hc : Continuous f := by
    apply (K.isClosedEmbedding_realization_coe hfin).isEmbedding.continuous_iff.mpr
    apply continuous_pi
    intro i
    have hcoord (u : Option ι) : Continuous (fun y : Realization K' => y.val u) :=
      (continuous_apply u).comp (continuous_realization_coe K')
    simp only [Function.comp_def, f, Finsupp.pointStellarSubdivisionLinearMap_apply]
    exact ((hcoord none).mul continuous_const).add (hcoord (some i))
  let : CompactSpace (Realization K') := K'.compactSpace_realization_of_finite_faces hfin'
  exact (Equiv.ofBijective f hf_bij).toHomeomorphOfContinuousClosed hc hc.isClosedMap

/-- Underlying barycentric coordinates of `pointStellarSubdivisionHomeomorph`. -/
@[simp]
theorem pointStellarSubdivisionHomeomorph_val {K : AbstractSimplicialComplex ι}
    (hfin : K.faces.Finite) (x₀ : Realization K) (hx : x₀ ∉ range K.vertex)
    (y : Realization (pointStellarSubdivision K x₀ hx)) :
    (pointStellarSubdivisionHomeomorph hfin x₀ hx y).val =
      Finsupp.pointStellarSubdivisionLinearMap x₀.val y.val :=
  rfl

/-- `pointStellarSubdivisionHomeomorph` sends the new vertex `none` to `x₀`. -/
@[simp]
theorem pointStellarSubdivisionHomeomorph_vertex_none {K : AbstractSimplicialComplex ι}
    (hfin : K.faces.Finite) (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) :
    pointStellarSubdivisionHomeomorph hfin x₀ hx
      ((pointStellarSubdivision K x₀ hx).vertex none) = x₀ := by
  apply Subtype.ext
  simp [pointStellarSubdivisionHomeomorph_val, vertex_val]

/-- `pointStellarSubdivisionHomeomorph` sends every original vertex `some i` to `K.vertex i`. -/
@[simp]
theorem pointStellarSubdivisionHomeomorph_vertex_some {K : AbstractSimplicialComplex ι}
    (hfin : K.faces.Finite) (x₀ : Realization K) (hx : x₀ ∉ range K.vertex) (i : ι) :
    pointStellarSubdivisionHomeomorph hfin x₀ hx
      ((pointStellarSubdivision K x₀ hx).vertex (some i)) = K.vertex i := by
  apply Subtype.ext
  simp [pointStellarSubdivisionHomeomorph_val, vertex_val]

/-- Given any finite-face complex `K` and any point `x₀ : Realization K`, there is a homeomorphic
finite-face complex preserving combinatorial-manifold structure in every dimension such that `x₀`
and all old vertices of `K` lie in the image of its vertices. -/
theorem exists_pointStellarSubdivision {K : AbstractSimplicialComplex ι}
    (hfin : K.faces.Finite) (x₀ : Realization K) :
    ∃ (ι' : Type u) (_ : DecidableEq ι') (K' : AbstractSimplicialComplex ι')
      (e : Realization K' ≃ₜ Realization K),
      (∀ d, IsCombinatorialManifold K.toPreAbstractSimplicialComplex d →
        IsCombinatorialManifold K'.toPreAbstractSimplicialComplex d) ∧
      K'.faces.Finite ∧
      (Finite ι → Finite ι') ∧
      (∀ i : ι, ∃ j : ι', e (K'.vertex j) = K.vertex i) ∧
      (∃ v₀ : ι', e (K'.vertex v₀) = x₀) := by
  by_cases hx : x₀ ∈ range K.vertex
  · obtain ⟨v₀, hv₀⟩ := hx
    exact ⟨ι, ‹_›, K, Homeomorph.refl _, fun _ h => h, hfin, fun h => h,
      fun i => ⟨i, rfl⟩, ⟨v₀, hv₀⟩⟩
  · refine ⟨Option ι, inferInstance, pointStellarSubdivision K x₀ hx,
      pointStellarSubdivisionHomeomorph hfin x₀ hx,
      fun _ h => isCombinatorialManifold_pointStellarSubdivision h x₀ hx,
      finite_faces_pointStellarSubdivision hfin x₀ hx, fun _ => inferInstance,
      fun i => ⟨some i, pointStellarSubdivisionHomeomorph_vertex_some hfin x₀ hx i⟩,
      ⟨none, pointStellarSubdivisionHomeomorph_vertex_none hfin x₀ hx⟩⟩

end AbstractSimplicialComplex
