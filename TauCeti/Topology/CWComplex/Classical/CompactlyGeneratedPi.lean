/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Isometry
public import TauCeti.Topology.Convenient.CompactlyGenerated
public import TauCeti.Topology.CWComplex.Classical.CompactSupport
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Compactly generated finite products of CW complexes

For arbitrary Hausdorff CW complexes `C i ⊆ X i` indexed by a finite type `ι`, the product
topology on `∀ i, X i` can be strictly coarser than the weak topology of the product cells when
more than one factor has infinitely many cells (Dowker's example). Passing to the compactly
generated refinement `WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i)` restores the
weak topology (Hatcher, Theorem A.6): every continuous map `S → ∀ i, X i` from a compact Hausdorff
space sends the preimage of `univ.pi C` into a product of compact sets in the factors, each of
which lies in a finite subcomplex (`TauCeti.exists_subcomplex_finite_of_isCompact`), where only
finitely many product cells occur.

## Main declarations

* `Topology.WithGeneratedByTopology.instT2Space`: any generated-topology refinement of a Hausdorff
  space is Hausdorff.
* `TauCeti.cwComplexCompactlyGeneratedPi`: the CW structure on
  `WithGeneratedByTopology.equiv ⁻¹' univ.pi C` inside the compactly generated finite product
  `WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i)`.
* `TauCeti.cwComplexCompactlyGeneratedPiUniv`: the global `CWComplex` instance on `univ` when each
  `X i` carries a CW structure on `univ`, with cell equivalence
  `TauCeti.cellCompactlyGeneratedPiUnivEquiv` and `FiniteType` / `Finite` instances.
* `TauCeti.existsMemCompactlyGeneratedPiSubcomplex`: for subcomplexes `E i` of `X i`, the subset of
  tuples having at least one coordinate in `E i` (such as the fat wedge when `E i = {x₀}`) is a
  subcomplex of the compactly generated product.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Appendix, Theorem A.6.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u

/-- Any generated-topology refinement of a Hausdorff space is Hausdorff, as the counit to the
original topology is continuous and injective. -/
instance Topology.WithGeneratedByTopology.instT2Space {ι : Type*} {G : ι → Type*}
    [∀ i, TopologicalSpace (G i)] {Y : Type*} [TopologicalSpace Y] [T2Space Y] :
    T2Space (WithGeneratedByTopology G Y) :=
  T2Space.of_injective_continuous equiv.injective continuous_equiv

namespace TauCeti

section Helpers

variable {ι : Type} [Fintype ι] {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {C : ∀ i, Set (X i)} [∀ i, CWComplex (C i)]

/-- An `n`-cell of a finite indexed product of CW complexes: a tuple of dimensions summing to `n`
together with one cell of each factor of the corresponding dimension. -/
private abbrev PiCell (C : ∀ i, Set (X i)) [∀ i, CWComplex (C i)] (n : ℕ) : Type u :=
  Σ d : {d : ι → ℕ // ∑ i, d i = n}, ∀ i, cell (C i) (d.1 i)

/-- A bijection `(Σ i, Fin (d i)) ≃ Fin n` for a dimension tuple summing to `n`. -/
private def piCellCoordEquiv {n : ℕ} (c : PiCell C n) : (Σ i, Fin (c.1.1 i)) ≃ Fin n :=
  Fintype.equivOfCardEq (by simp [c.1.2])

/-- The sup-norm isometry `(Fin n → ℝ) ≃ᵢ ∀ i, (Fin (d i) → ℝ)` splitting coordinates along
`piCellCoordEquiv`. -/
private def piCellIsometry {n : ℕ} (c : PiCell C n) :
    (Fin n → ℝ) ≃ᵢ ∀ i, (Fin (c.1.1 i) → ℝ) where
  toEquiv :=
    { toFun := fun x i j ↦ x (piCellCoordEquiv c ⟨i, j⟩)
      invFun := fun y k ↦ y ((piCellCoordEquiv c).symm k).1 ((piCellCoordEquiv c).symm k).2
      left_inv := fun x ↦ funext fun k ↦ by simp
      right_inv := fun y ↦ funext fun i ↦ funext fun j ↦ by
        dsimp only
        rw [(piCellCoordEquiv c).symm_apply_apply] }
  isometry_toFun x y := by
    simp only [edist_pi_def, Finset.sup_univ_eq_iSup]
    rw [← iSup_sigma (f := fun s : Σ i, Fin (c.1.1 i) ↦
      edist (x (piCellCoordEquiv c s)) (y (piCellCoordEquiv c s))),
      (piCellCoordEquiv c).iSup_comp (g := fun k ↦ edist (x k) (y k))]

private lemma piCellIsometry_zero {n : ℕ} (c : PiCell C n) : piCellIsometry c 0 = 0 :=
  rfl

/-- The characteristic partial equivalence of a product cell into the compactly generated finite
product. -/
private def piCellMap {n : ℕ} (c : PiCell C n) :
    PartialEquiv (Fin n → ℝ)
      (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i)) :=
  ((piCellIsometry c).toEquiv.transPartialEquiv
    (PartialEquiv.pi fun i ↦ map (c.1.1 i) (c.2 i))).transEquiv
    (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K)).symm

private lemma equiv_piCellMap_apply {n : ℕ} (c : PiCell C n) (x : Fin n → ℝ) (i : ι) :
    WithGeneratedByTopology.equiv (piCellMap c x) i =
      map (c.1.1 i) (c.2 i) (piCellIsometry c x i) :=
  (rfl)

private lemma source_piCellMap (n : ℕ) (c : PiCell C n) :
    (piCellMap c).source = ball 0 1 := by
  rw [piCellMap, PartialEquiv.transEquiv_source, Equiv.transPartialEquiv_source,
    PartialEquiv.pi_source]
  simp only [source_eq]
  have hpi : (univ.pi fun i ↦ ball (0 : Fin (c.1.1 i) → ℝ) 1) = ball 0 1 := by
    simp [ball_pi _ zero_lt_one]
  rw [hpi, ← piCellIsometry_zero c]
  exact ((piCellIsometry c).preimage_ball _ _).trans (by rw [IsometryEquiv.symm_apply_apply])

private lemma image_piCellMap {n : ℕ} (c : PiCell C n) (s : Set (Fin n → ℝ)) :
    piCellMap c '' s =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹'
        ((Pi.map fun i ↦ map (c.1.1 i) (c.2 i)) '' (piCellIsometry c '' s)) := by
  ext y
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨piCellIsometry c x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, hzy⟩
    exact ⟨x, hx, WithGeneratedByTopology.equiv.injective hzy⟩

private lemma image_ball_piCellMap {n : ℕ} (c : PiCell C n) :
    piCellMap c '' ball 0 1 =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹'
        univ.pi fun i ↦ openCell (c.1.1 i) (c.2 i) := by
  rw [image_piCellMap, IsometryEquiv.image_ball, piCellIsometry_zero,
    ball_pi (0 : ∀ i, Fin (c.1.1 i) → ℝ) zero_lt_one]
  congr 1
  ext v
  simp only [mem_image, mem_pi, mem_univ, forall_true_left, openCell, Pi.zero_apply]
  exact ⟨fun ⟨z, hz, hzv⟩ i ↦ ⟨z i, hz i, congrFun hzv i⟩, fun h ↦ by
    choose z hz hzv using h
    exact ⟨z, hz, funext hzv⟩⟩

private lemma image_closedBall_piCellMap {n : ℕ} (c : PiCell C n) :
    piCellMap c '' closedBall 0 1 =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹'
        univ.pi fun i ↦ closedCell (c.1.1 i) (c.2 i) := by
  rw [image_piCellMap, IsometryEquiv.image_closedBall, piCellIsometry_zero,
    closedBall_pi (0 : ∀ i, Fin (c.1.1 i) → ℝ) zero_le_one]
  congr 1
  ext v
  simp only [mem_image, mem_pi, mem_univ, forall_true_left, closedCell, Pi.zero_apply]
  exact ⟨fun ⟨z, hz, hzv⟩ i ↦ ⟨z i, hz i, congrFun hzv i⟩, fun h ↦ by
    choose z hz hzv using h
    exact ⟨z, hz, funext hzv⟩⟩

private lemma image_sphere_piCellMap {n : ℕ} (c : PiCell C n) :
    piCellMap c '' sphere 0 1 =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹'
        {v ∈ univ.pi fun i ↦ closedCell (c.1.1 i) (c.2 i) |
          ∃ i, v i ∈ cellFrontier (c.1.1 i) (c.2 i)} := by
  classical
  rw [image_piCellMap, IsometryEquiv.image_sphere, piCellIsometry_zero, ← closedBall_sdiff_ball,
    closedBall_pi (0 : ∀ i, Fin (c.1.1 i) → ℝ) zero_le_one,
    ball_pi (0 : ∀ i, Fin (c.1.1 i) → ℝ) zero_lt_one]
  congr 1
  ext v
  simp only [mem_image, mem_sdiff, mem_pi, mem_univ, forall_true_left, not_forall,
    Pi.zero_apply, mem_ofPred, closedCell, cellFrontier]
  constructor
  · rintro ⟨z, ⟨hzc, i, hzb⟩, rfl⟩
    refine ⟨fun j ↦ ⟨z j, hzc j, rfl⟩, i, z i, ?_, rfl⟩
    rw [← closedBall_sdiff_ball]
    exact ⟨hzc i, hzb⟩
  · rintro ⟨hvc, i, w, hw, hwi⟩
    choose z hzc hzv using hvc
    rw [← closedBall_sdiff_ball] at hw
    refine ⟨Function.update z i w, ⟨fun j ↦ ?_, i, by simpa using hw.2⟩, funext fun j ↦ ?_⟩
    · by_cases hj : j = i
      · subst hj; simpa using hw.1
      · simpa [hj] using hzc j
    · by_cases hj : j = i
      · subst hj; simpa [Pi.map_apply] using hwi
      · simp [Pi.map_apply, hj, hzv j]

private lemma continuousOn_piCellMap (n : ℕ) (c : PiCell C n) :
    ContinuousOn (piCellMap c) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hraw : Continuous fun x : closedBall (0 : Fin n → ℝ) 1 ↦
      fun i ↦ map (c.1.1 i) (c.2 i) (piCellIsometry c x.1 i) := by
    refine continuous_pi fun i ↦ (continuousOn (c.1.1 i) (c.2 i)).comp_continuous
      ((continuous_apply i).comp ((piCellIsometry c).continuous.comp continuous_subtype_val))
      fun x ↦ ?_
    have hx : piCellIsometry c x.1 ∈ closedBall 0 1 := by
      rw [← piCellIsometry_zero c, mem_closedBall, IsometryEquiv.dist_eq]
      exact x.2
    exact (closedBall_pi (0 : ∀ i, Fin (c.1.1 i) → ℝ) zero_le_one ▸ hx) i trivial
  exact (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := fun K : CompHaus.{u} ↦ K) _).2 hraw

private lemma continuousOn_symm_piCellMap (n : ℕ) (c : PiCell C n) :
    ContinuousOn (piCellMap c).symm (piCellMap c).target := by
  have ht : (piCellMap c).target =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹'
        univ.pi fun i ↦ (map (c.1.1 i) (c.2 i)).target := by
    ext y
    simp [piCellMap, PartialEquiv.transEquiv, Equiv.transPartialEquiv]
  rw [ht]
  have hsymm : ContinuousOn (fun v : ∀ i, X i ↦ fun i ↦ (map (c.1.1 i) (c.2 i)).symm (v i))
      (univ.pi fun i ↦ (map (c.1.1 i) (c.2 i)).target) :=
    continuousOn_pi.2 fun i ↦ (continuousOn_symm (c.1.1 i) (c.2 i)).comp
      (continuous_apply i).continuousOn fun _ hv ↦ hv i trivial
  refine (piCellIsometry c).symm.continuous.comp_continuousOn ?_
  exact hsymm.comp WithGeneratedByTopology.continuous_equiv.continuousOn fun _ hy ↦ hy

private lemma pairwiseDisjoint_piCellMap :
    (univ : Set (Σ n, PiCell C n)).PairwiseDisjoint fun nc ↦ piCellMap nc.2 '' ball 0 1 := by
  rintro ⟨n, d, c⟩ - ⟨n', d', c'⟩ - hne
  rw [Function.onFun, image_ball_piCellMap, image_ball_piCellMap]
  refine disjoint_left.2 fun y hy hy' ↦ hne ?_
  have hcoord (i : ι) : (⟨d.1 i, c i⟩ : Σ m, cell (C i) m) = ⟨d'.1 i, c' i⟩ :=
    eq_of_not_disjoint_openCell
      (not_disjoint_iff.2 ⟨_, hy i trivial, hy' i trivial⟩)
  have hd : d.1 = d'.1 := funext fun i ↦ congrArg Sigma.fst (hcoord i)
  obtain rfl : n = n' := d.2.symm.trans (hd ▸ d'.2)
  obtain rfl : d = d' := Subtype.ext hd
  refine congrArg (fun f ↦ (⟨n, d, f⟩ : Σ m, PiCell C m)) (funext fun i ↦ ?_)
  exact eq_of_heq (Sigma.mk.inj_iff.1 (hcoord i)).2

private lemma mapsTo_piCellMap (n : ℕ) (c : PiCell C n) :
    ∃ I : ∀ m, Finset (PiCell C m),
      MapsTo (piCellMap c) (sphere 0 1) (⋃ (m < n) (c' ∈ I m), piCellMap c' '' closedBall 0 1) := by
  classical
  choose J hJ using fun i ↦ CWComplex.cellFrontier_subset_finite_closedCell (c.1.1 i) (c.2 i)
  let S (i : ι) : Finset (Σ m, cell (C i) m) :=
    insert ⟨c.1.1 i, c.2 i⟩ ((Finset.range (c.1.1 i)).sigma (J i))
  let P := Fintype.piFinset S
  let I (m : ℕ) : Finset (PiCell C m) :=
    (P.subtype fun p ↦ ∑ i, (p i).1 = m).image fun p ↦
      ⟨⟨fun i ↦ (p.1 i).1, p.2⟩, fun i ↦ (p.1 i).2⟩
  refine ⟨I, ?_⟩
  rw [mapsTo_iff_image_subset, image_sphere_piCellMap]
  intro y ⟨hyc, i₀, hyf⟩
  obtain ⟨m₀, hm₀, k₀, hk₀, hyk₀⟩ := by simpa only [mem_iUnion, exists_prop] using hJ i₀ hyf
  let p : ∀ i, Σ m, cell (C i) m := Function.update (fun i ↦ ⟨c.1.1 i, c.2 i⟩) i₀ ⟨m₀, k₀⟩
  have hpP : p ∈ P := Fintype.mem_piFinset.2 fun i ↦ by
    by_cases hi : i = i₀
    · subst hi
      simpa [p, S] using Or.inr ⟨hm₀, hk₀⟩
    · simp [p, hi, S]
  have hlt : ∑ i, (p i).1 < n := by
    rw [← c.1.2]
    refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ i₀, by simp [p, hm₀]⟩
    by_cases hi : i = i₀
    · subst hi; simp [p, hm₀.le]
    · simp [p, hi]
  refine mem_iUnion₂_of_mem hlt ?_
  let c' : PiCell C (∑ i, (p i).1) := ⟨⟨fun i ↦ (p i).1, rfl⟩, fun i ↦ (p i).2⟩
  have hc'I : c' ∈ I (∑ i, (p i).1) :=
    Finset.mem_image.2 ⟨⟨p, rfl⟩, Finset.mem_subtype.2 hpP, rfl⟩
  refine mem_iUnion₂_of_mem hc'I ?_
  rw [image_closedBall_piCellMap]
  intro i _
  dsimp only [c']
  by_cases hi : i = i₀
  · subst hi
    have hpi : p i = ⟨m₀, k₀⟩ := by simp [p]
    rw [hpi]
    exact hyk₀
  · have hpi : p i = ⟨c.1.1 i, c.2 i⟩ := by simp [p, hi]
    rw [hpi]
    exact hyc i trivial

/-- If `A` meets every closed product cell in a closed subset of the compactly generated product,
then its image in `∀ i, X i` meets every closed product cell in a closed subset of the ordinary
product topology (by compactness in the Hausdorff product `∀ i, X i`). -/
private lemma isClosed_inter_closedPiCell_in_pi [∀ i, T2Space (X i)]
    {A : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i))}
    {n : ℕ} (c : PiCell C n) (hA : IsClosed (A ∩ piCellMap c '' closedBall 0 1)) :
    IsClosed ((WithGeneratedByTopology.equiv '' A) ∩
      univ.pi fun i ↦ closedCell (c.1.1 i) (c.2 i)) := by
  have hcomp : IsCompact (A ∩ piCellMap c '' closedBall 0 1) :=
    ((isCompact_closedBall (0 : Fin n → ℝ) 1).image_of_continuousOn
      (continuousOn_piCellMap n c)).of_isClosed_subset hA inter_subset_right
  have himg : WithGeneratedByTopology.equiv '' (A ∩ piCellMap c '' closedBall 0 1) =
      (WithGeneratedByTopology.equiv '' A) ∩ univ.pi fun i ↦ closedCell (c.1.1 i) (c.2 i) := by
    rw [image_closedBall_piCellMap, ← image_inter_preimage]
  rw [← himg]
  exact (hcomp.image WithGeneratedByTopology.continuous_equiv).isClosed

/-- **Hatcher, Theorem A.6**: a subset of `univ.pi C` meeting every closed product cell in a closed
set is closed in the compactly generated product topology. -/
private lemma closed_piCellMap [∀ i, T2Space (X i)]
    (A : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i)))
    (hAC : A ⊆ WithGeneratedByTopology.equiv ⁻¹' univ.pi C)
    (hA : ∀ n (c : PiCell C n), IsClosed (A ∩ piCellMap c '' closedBall 0 1)) :
    IsClosed A := by
  rw [WithGeneratedByTopology.isClosed_iff]
  intro S f
  have hS' : IsCompact (f ⁻¹' univ.pi C) :=
    (isClosed_set_pi fun i _ ↦ RelCWComplex.isClosed (C := C i)).preimage f.continuous |>.isCompact
  choose E hEfin hKE using fun i ↦ exists_subcomplex_finite_of_isCompact (C := C i)
    (hS'.image ((continuous_apply i).comp f.continuous))
    (by rintro _ ⟨s, hs, rfl⟩; exact hs i trivial)
  have (i : ι) : _root_.Finite (Σ m, (E i).I m) := by
    simpa only [CWComplex.Subcomplex.cell_def] using
      CWComplex.finite_cells_of_finite (C := (E i : Set (X i)))
  let A₀ : Set (∀ i, X i) := WithGeneratedByTopology.equiv '' A
  have hpre : f ⁻¹' (WithGeneratedByTopology.equiv.symm ⁻¹' A) =
      f ⁻¹' (A₀ ∩ univ.pi fun i ↦ (E i : Set (X i))) := by
    ext s
    simp only [A₀, mem_preimage, mem_inter_iff, mem_pi, mem_univ, forall_true_left]
    have hmem : WithGeneratedByTopology.equiv.symm (f s) ∈ A ↔ f s ∈ A₀ :=
      ⟨fun h ↦ ⟨_, h, WithGeneratedByTopology.equiv.apply_symm_apply _⟩,
        fun ⟨y, hy, hyf⟩ ↦ hyf ▸ WithGeneratedByTopology.equiv.symm_apply_apply y ▸ hy⟩
    rw [hmem]
    refine ⟨fun hs ↦ ⟨hs, fun i ↦ hKE i ⟨s, ?_, rfl⟩⟩, fun hs ↦ hs.1⟩
    obtain ⟨y, hy, rfl⟩ := hs
    exact hAC hy
  rw [hpre]
  -- Over `univ.pi E`, only finitely many product cells appear, so `A₀ ∩ univ.pi E` is closed.
  have hcov : (univ.pi fun i ↦ (E i : Set (X i))) =
      ⋃ q : ∀ i, Σ m, (E i).I m,
        univ.pi fun i ↦ closedCell (C := C i) (q i).1 (q i).2 := by
    ext v
    simp only [mem_pi, mem_univ, forall_true_left, mem_iUnion]
    conv_lhs => enter [i]; rw [← CWComplex.Subcomplex.union_closedCell (E i), mem_iUnion₂]
    exact ⟨fun h ↦ by choose m j hv using h; exact ⟨fun i ↦ ⟨m i, j i⟩, hv⟩,
      fun ⟨q, hq⟩ i ↦ ⟨(q i).1, (q i).2, hq i⟩⟩
  rw [hcov, inter_iUnion]
  refine (isClosed_iUnion_of_finite fun q ↦ ?_).preimage f.continuous
  exact isClosed_inter_closedPiCell_in_pi
    ⟨⟨fun i ↦ (q i).1, rfl⟩, fun i ↦ (q i).2⟩ (hA _ _)

private lemma iUnion_piCellMap :
    ⋃ (n : ℕ) (c : PiCell C n), piCellMap c '' closedBall 0 1 =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹' univ.pi C := by
  simp_rw [image_closedBall_piCellMap]
  ext y
  simp only [mem_iUnion, mem_preimage, mem_pi, mem_univ, forall_true_left]
  conv_rhs => enter [i]; rw [← CWComplex.union (C := C i), mem_iUnion₂]
  exact ⟨fun ⟨_, c, hy⟩ i ↦ ⟨c.1.1 i, c.2 i, hy i⟩, fun h ↦ by
    choose d c hy using h
    exact ⟨∑ i, d i, ⟨⟨d, rfl⟩, c⟩, hy⟩⟩

end Helpers

section Public

variable {ι : Type} [Fintype ι] {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  [∀ i, T2Space (X i)]

/-- **Compactly generated finite product of CW complexes** (Hatcher, Theorem A.6): for Hausdorff
CW complexes `C i ⊆ X i`, the product `univ.pi C` is a CW complex inside the compactly generated
refinement `WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i)`. -/
@[instance_reducible]
def cwComplexCompactlyGeneratedPi (C : ∀ i, Set (X i)) [∀ i, CWComplex (C i)] :
    CWComplex (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹' univ.pi C) where
  cell := PiCell C
  map _ c := piCellMap c
  source_eq := source_piCellMap
  continuousOn := continuousOn_piCellMap
  continuousOn_symm := continuousOn_symm_piCellMap
  pairwiseDisjoint' := pairwiseDisjoint_piCellMap
  mapsTo' := mapsTo_piCellMap
  closed' := closed_piCellMap
  union' := iUnion_piCellMap

variable [∀ i, CWComplex (univ : Set (X i))]

/-- **Compactly generated finite product of CW complexes on `univ`** (Hatcher, Theorem A.6). -/
@[instance_reducible]
def cwComplexCompactlyGeneratedPiUniv :
    CWComplex (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i))) where
  cell := PiCell fun i ↦ (univ : Set (X i))
  map _ c := piCellMap c
  source_eq := source_piCellMap
  continuousOn := continuousOn_piCellMap
  continuousOn_symm := continuousOn_symm_piCellMap
  pairwiseDisjoint' := pairwiseDisjoint_piCellMap
  mapsTo' := mapsTo_piCellMap
  closed' A _ hA := closed_piCellMap A (by simp) hA
  union' := iUnion_piCellMap.trans (by simp)

attribute [instance] cwComplexCompactlyGeneratedPiUniv

/-- The `n`-cells of the compactly generated finite product `∀ i, X i` are the pairs of a dimension
tuple `d : ι → ℕ` summing to `n` and a cell of `X i` of dimension `d i` for each `i`. -/
def cellCompactlyGeneratedPiUnivEquiv (n : ℕ) :
    cell (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i))) n ≃
      Σ d : {d : ι → ℕ // ∑ i, d i = n}, ∀ i, cell (univ : Set (X i)) (d.1 i) :=
  Equiv.refl _

@[simp]
theorem openCell_cellCompactlyGeneratedPiUnivEquiv_symm {n : ℕ}
    (c : Σ d : {d : ι → ℕ // ∑ i, d i = n}, ∀ i, cell (univ : Set (X i)) (d.1 i)) :
    openCell n ((cellCompactlyGeneratedPiUnivEquiv n).symm c) =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹'
        univ.pi fun i ↦ openCell (c.1.1 i) (c.2 i) :=
  image_ball_piCellMap c

@[simp]
theorem closedCell_cellCompactlyGeneratedPiUnivEquiv_symm {n : ℕ}
    (c : Σ d : {d : ι → ℕ // ∑ i, d i = n}, ∀ i, cell (univ : Set (X i)) (d.1 i)) :
    closedCell n ((cellCompactlyGeneratedPiUnivEquiv n).symm c) =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹'
        univ.pi fun i ↦ closedCell (c.1.1 i) (c.2 i) :=
  image_closedBall_piCellMap c

@[simp]
theorem cellFrontier_cellCompactlyGeneratedPiUnivEquiv_symm {n : ℕ}
    (c : Σ d : {d : ι → ℕ // ∑ i, d i = n}, ∀ i, cell (univ : Set (X i)) (d.1 i)) :
    cellFrontier n ((cellCompactlyGeneratedPiUnivEquiv n).symm c) =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) ⁻¹'
        {v ∈ univ.pi fun i ↦ closedCell (c.1.1 i) (c.2 i) |
          ∃ i, v i ∈ cellFrontier (c.1.1 i) (c.2 i)} :=
  image_sphere_piCellMap c

/-- The compactly generated finite product of CW complexes of finite type is of finite type. -/
instance finiteType_compactlyGeneratedPiUniv
    [∀ i, CWComplex.FiniteType (univ : Set (X i))] :
    CWComplex.FiniteType
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i))) where
  finite_cell n := by
    have (i : ι) (m : ℕ) : _root_.Finite (cell (univ : Set (X i)) m) :=
      CWComplex.FiniteType.finite_cell m
    have : _root_.Finite {d : ι → ℕ // ∑ i, d i = n} :=
      Finite.of_injective
        (f := fun d : {d : ι → ℕ // ∑ i, d i = n} ↦ fun i : ι ↦
          (⟨d.1 i, Nat.lt_succ_of_le <|
            (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans_eq d.2⟩ :
            Fin (n + 1)))
        fun d₁ d₂ h ↦ Subtype.ext <| funext fun i ↦ congrArg Fin.val (congrFun h i)
    exact (cellCompactlyGeneratedPiUnivEquiv n).finite_iff.2 inferInstance

/-- The compactly generated finite product of finite CW complexes is finite. -/
instance finite_compactlyGeneratedPiUniv [∀ i, CWComplex.Finite (univ : Set (X i))] :
    CWComplex.Finite
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i))) := by
  have (i : ι) : _root_.Finite (Σ m, cell (univ : Set (X i)) m) :=
    CWComplex.finite_cells_of_finite (C := (univ : Set (X i)))
  refine CWComplex.finite_of_finite_cells <| Finite.of_surjective
    (f := fun q : ∀ i, Σ m, cell (univ : Set (X i)) m ↦
      ⟨∑ i, (q i).1, (cellCompactlyGeneratedPiUnivEquiv _).symm
        ⟨⟨fun i ↦ (q i).1, rfl⟩, fun i ↦ (q i).2⟩⟩) ?_
  rintro ⟨n, c⟩
  rcases hc : cellCompactlyGeneratedPiUnivEquiv n c with ⟨⟨d, hd⟩, f⟩
  subst hd
  refine ⟨fun i ↦ ⟨d i, f i⟩, Sigma.ext rfl (heq_of_eq ?_)⟩
  dsimp only
  rw [← hc, Equiv.symm_apply_apply]

/-- Given subcomplexes `E i` of `X i`, the tuples having at least one coordinate in `E i` form a
subcomplex of the compactly generated finite product (for instance, the fat wedge when
`E i = {x₀}`). -/
def existsMemCompactlyGeneratedPiSubcomplex
    (E : ∀ i, CWComplex.Subcomplex (univ : Set (X i))) :
    CWComplex.Subcomplex
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i))) :=
  CWComplex.Subcomplex.mk' _
    {y : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i) |
      ∃ i, WithGeneratedByTopology.equiv y i ∈ E i}
    (fun n ↦ {c | ∃ i, (cellCompactlyGeneratedPiUnivEquiv n c).2 i ∈
      (E i).I ((cellCompactlyGeneratedPiUnivEquiv n c).1.1 i)})
    (fun n ⟨c, i, hi⟩ y hy ↦ by
      dsimp only at hy
      rw [← (cellCompactlyGeneratedPiUnivEquiv n).symm_apply_apply c,
        closedCell_cellCompactlyGeneratedPiUnivEquiv_symm] at hy
      exact ⟨i, (E i).closedCell_subset_of_mem hi (hy i trivial)⟩)
    (by
      refine Subset.antisymm (iUnion₂_subset fun n ⟨c, i, hi⟩ y hy ↦ ?_) fun y ⟨i₀, hy₀⟩ ↦ ?_
      · dsimp only at hy
        rw [← (cellCompactlyGeneratedPiUnivEquiv n).symm_apply_apply c,
          openCell_cellCompactlyGeneratedPiUnivEquiv_symm] at hy
        exact ⟨i, (E i).openCell_subset_of_mem hi (hy i trivial)⟩
      · have hopen (i : ι) : ∃ (m : ℕ) (j : cell (univ : Set (X i)) m),
            WithGeneratedByTopology.equiv y i ∈ openCell m j := by
          have hmem : WithGeneratedByTopology.equiv y i ∈
              ⋃ (m : ℕ) (j : cell (univ : Set (X i)) m), openCell m j := by
            rw [CWComplex.iUnion_openCell_eq_complex]
            exact mem_univ _
          exact mem_iUnion₂.1 hmem
        choose d c hyc using hopen
        let pc : PiCell (fun i ↦ (univ : Set (X i))) (∑ i, d i) := ⟨⟨d, rfl⟩, c⟩
        have hi₀ : c i₀ ∈ (E i₀).I (d i₀) :=
          ((E i₀).mem_I_iff_of_mem_openCell (hyc i₀)).2 hy₀
        refine mem_iUnion₂.2 ⟨∑ i, d i, ⟨(cellCompactlyGeneratedPiUnivEquiv _).symm pc,
          i₀, ?_⟩, ?_⟩
        · rw [(cellCompactlyGeneratedPiUnivEquiv (∑ i, d i)).apply_symm_apply]
          exact hi₀
        · rw [openCell_cellCompactlyGeneratedPiUnivEquiv_symm]
          exact fun i _ ↦ hyc i)

@[simp]
theorem coe_existsMemCompactlyGeneratedPiSubcomplex
    (E : ∀ i, CWComplex.Subcomplex (univ : Set (X i))) :
    (existsMemCompactlyGeneratedPiSubcomplex E :
      Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i))) =
      {y : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i) |
        ∃ i, WithGeneratedByTopology.equiv y i ∈ E i} :=
  (rfl)

@[simp]
theorem mem_existsMemCompactlyGeneratedPiSubcomplex_I_iff
    (E : ∀ i, CWComplex.Subcomplex (univ : Set (X i))) {n : ℕ}
    (c : cell (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (∀ i, X i))) n) :
    c ∈ (existsMemCompactlyGeneratedPiSubcomplex E).I n ↔
      ∃ i, (cellCompactlyGeneratedPiUnivEquiv n c).2 i ∈
        (E i).I ((cellCompactlyGeneratedPiUnivEquiv n c).1.1 i) :=
  Iff.rfl

end Public

end TauCeti
