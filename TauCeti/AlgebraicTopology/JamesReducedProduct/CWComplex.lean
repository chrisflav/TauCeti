/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.JamesReducedProduct.Filtration
public import TauCeti.Topology.CWComplex.Classical.CompactlyGeneratedPi
public import TauCeti.Topology.CWComplex.Classical.CWType
public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.CWComplex.Classical.SequentialColimit
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.CWComplex.Classical.Trans
public import TauCeti.Topology.CWComplex.Classical.Zero
import Mathlib.Data.List.OfFn

/-!
# CW structure on the James reduced product and its word-length filtration

Let `X` be a Hausdorff classical CW complex (`CWComplex (univ : Set X)`) pointed at a `0`-cell
`x₀ ∈ CWComplex.skeleton (univ : Set X) 0`. This file constructs the canonical CW structure on the
James reduced product `J X` and on each stage `J_r X` (`TauCeti.JamesReducedProduct.filtration`) of
its word-length filtration, following James (1955) and Hatcher, Section 3.C:

* **Basepoint and fat wedge subcomplexes**: `{x₀}` is a `0`-dimensional subcomplex of `X`
  (`TauCeti.JamesReducedProduct.basepointSubcomplex`), so the fat wedge `fatWedgeSet X x₀ r` of
  tuples with at least one basepoint coordinate is a subcomplex of the compactly generated power
  `k(Xʳ)` (`TauCeti.JamesReducedProduct.fatWedgeSubcomplex`).
* **Inductive CW stages**: `J₀ X` is a one-point discrete CW complex, and gluing the relative CW
  pair `(k(X^(r + 1)), fatWedgeSet X x₀ (r + 1))` along word reduction onto `J_r X` via
  `TauCeti.JamesReducedProduct.isPushout_filtration_succ` makes every `J_r X` Hausdorff
  (`TauCeti.JamesReducedProduct.t2Space_filtration`) and a CW complex on `univ`
  (`TauCeti.JamesReducedProduct.cwComplexFiltrationUniv`) with cellular quotient map
  `mkFiltration r : k(Xʳ) → J_r X` (`TauCeti.JamesReducedProduct.mapsTo_mkFiltration_skeletonLT`).
* **Sequential colimit and subcomplexes**: passing to the sequential colimit
  `TauCeti.JamesReducedProduct.isColimitFiltrationCocone` makes `J X` Hausdorff
  (`TauCeti.JamesReducedProduct.t2Space`) and a CW complex on `univ`
  (`TauCeti.JamesReducedProduct.cwComplexUniv`) in which every `J_r X` is a subcomplex of `J X`
  (`TauCeti.JamesReducedProduct.filtrationSubcomplex`) and of `J_s X` for `r ≤ s`
  (`TauCeti.JamesReducedProduct.filtrationSubcomplexOfLE`), so `(J_(r + 1) X, J_r X)` has the
  homotopy extension property
  (`TauCeti.JamesReducedProduct.hasHomotopyExtensionProperty_filtration`).
* **Cells and finiteness**: the `n`-cells of `J X` correspond to reduced words in the non-basepoint
  cells of `X` whose dimensions sum to `n` (`TauCeti.JamesReducedProduct.cellEquiv`,
  `TauCeti.JamesReducedProduct.cellEquivFreeMonoid`), with `J_r X` consisting of the words of
  length at most `r`. Each `J_r X` is finite when `X` is finite
  (`TauCeti.JamesReducedProduct.finite_filtration`) and of finite type when `X` is of finite type
  (`TauCeti.JamesReducedProduct.finiteType_filtration`), and `J X` itself is of finite type when `X`
  is of finite type with a single `0`-cell (`TauCeti.JamesReducedProduct.finiteType_cwComplexUniv`).

## Main definitions

* `TauCeti.JamesReducedProduct.basepointCell`, `TauCeti.JamesReducedProduct.basepointSubcomplex`:
  the `0`-cell of `X` at `x₀` and the subcomplex `{x₀}` of `X`.
* `TauCeti.JamesReducedProduct.fatWedgeSubcomplex`: the fat wedge as a subcomplex of `k(Xʳ)`.
* `TauCeti.JamesReducedProduct.NonBasepointCell`: the cells of `X` other than the basepoint
  `0`-cell.
* `TauCeti.JamesReducedProduct.cwComplexFiltrationUniv`,
  `TauCeti.JamesReducedProduct.cwComplexUniv`: the CW structures on `univ : Set (J_r X)` and
  `univ : Set (J X)`.
* `TauCeti.JamesReducedProduct.filtrationSubcomplex`,
  `TauCeti.JamesReducedProduct.filtrationSubcomplexOfLE`: `J_r X` as a subcomplex of `J X` and of
  `J_s X` (`r ≤ s`).
* `TauCeti.JamesReducedProduct.cellEquiv`, `TauCeti.JamesReducedProduct.cellEquivFreeMonoid`:
  description of the `n`-cells of `J X` as words of non-basepoint cells of total dimension `n`.

## Main results

* `TauCeti.JamesReducedProduct.t2Space_filtration`, `TauCeti.JamesReducedProduct.t2Space`:
  Hausdorffness of `J_r X` and `J X`.
* `TauCeti.JamesReducedProduct.mapsTo_mkFiltration_skeletonLT`,
  `TauCeti.JamesReducedProduct.mapsTo_mkFiltration_skeleton`: cellularity of `k(Xʳ) → J_r X`.
* `TauCeti.JamesReducedProduct.hasHomotopyExtensionProperty_filtration`: each `J_r X ⊆ J_(r + 1) X`
  has the homotopy extension property.
* `TauCeti.JamesReducedProduct.finite_filtration`,
  `TauCeti.JamesReducedProduct.finiteType_filtration`,
  `TauCeti.JamesReducedProduct.finiteType_cwComplexUniv`: finiteness and finite-type properties.

## References

* I. M. James, *Reduced product spaces*, Ann. of Math. (2) 62 (1955), 170–197.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C, Proposition
  3.C.1.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti.JamesReducedProduct

section BasepointAndFatWedge

variable {X : Type u} {x₀ : X} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

private lemma exists_cell_zero_map_eq (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    ∃ i : cell (univ : Set X) 0, RelCWComplex.map 0 i ![] = x₀ := by
  obtain ⟨m, hm, i, hi⟩ := CWComplex.mem_skeleton_iff.1 hx₀
  obtain rfl : m = 0 := by simpa using hm
  rw [openCell_zero_eq_singleton] at hi
  exact ⟨i, hi.symm⟩

/-- The `0`-cell of `X` whose image is the basepoint `x₀ ∈ CWComplex.skeleton (univ : Set X) 0`. -/
def basepointCell (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) : cell (univ : Set X) 0 :=
  (exists_cell_zero_map_eq hx₀).choose

@[simp]
theorem map_basepointCell (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    RelCWComplex.map 0 (basepointCell hx₀) ![] = x₀ :=
  (exists_cell_zero_map_eq hx₀).choose_spec

@[simp]
theorem openCell_basepointCell (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    openCell 0 (basepointCell hx₀) = {x₀} := by
  rw [openCell_zero_eq_singleton, map_basepointCell]

@[simp]
theorem closedCell_basepointCell (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    closedCell 0 (basepointCell hx₀) = {x₀} := by
  rw [closedCell_zero_eq_singleton, map_basepointCell]

/-- Any open cell of `X` containing `x₀` is the basepoint `0`-cell. -/
theorem eq_basepointCell_of_mem_openCell (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0)
    {m : ℕ} {c : cell (univ : Set X) m} (hx : x₀ ∈ openCell m c) :
    (⟨m, c⟩ : Σ n, cell (univ : Set X) n) = ⟨0, basepointCell hx₀⟩ :=
  eq_of_not_disjoint_openCell (not_disjoint_iff.2 ⟨x₀, hx, by simp⟩)

/-- The `0`-dimensional subcomplex `{x₀}` of `X` when `x₀` lies in the `0`-skeleton. -/
def basepointSubcomplex (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    CWComplex.Subcomplex (univ : Set X) where
  carrier := {x₀}
  I n := {c | (⟨n, c⟩ : Σ m, cell (univ : Set X) m) = ⟨0, basepointCell hx₀⟩}
  closed' := isClosed_singleton
  union' := by
    rw [empty_union]
    refine Subset.antisymm (iUnion₂_subset fun n ⟨c, hc⟩ ↦ ?_) ?_
    · obtain ⟨rfl, hc'⟩ := Sigma.mk.inj_iff.1 hc
      cases eq_of_heq hc'
      simp
    · rw [singleton_subset_iff]
      exact mem_iUnion₂.2 ⟨0, ⟨basepointCell hx₀, rfl⟩, by simp⟩

@[simp]
theorem coe_basepointSubcomplex (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    (basepointSubcomplex hx₀ : Set X) = {x₀} :=
  (rfl)

@[simp]
theorem mem_basepointSubcomplex_I_iff (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {n : ℕ}
    (c : cell (univ : Set X) n) :
    c ∈ (basepointSubcomplex hx₀).I n ↔
      (⟨n, c⟩ : Σ m, cell (univ : Set X) m) = ⟨0, basepointCell hx₀⟩ :=
  Iff.rfl

private lemma fatWedgeSet_eq_coe_existsMem (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0)
    (r : ℕ) :
    fatWedgeSet X x₀ r =
      (existsMemCompactlyGeneratedPiSubcomplex (fun _ : Fin r ↦ basepointSubcomplex hx₀) :
        Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X))) := by
  ext y
  simp [← SetLike.mem_coe, coe_basepointSubcomplex]

/-- The fat wedge inside `k(Xʳ)` as a subcomplex of the compactly generated `r`-th power of `X`. -/
def fatWedgeSubcomplex (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    CWComplex.Subcomplex
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X))) where
  carrier := fatWedgeSet X x₀ r
  I n := (existsMemCompactlyGeneratedPiSubcomplex fun _ : Fin r ↦ basepointSubcomplex hx₀).I n
  closed' := (fatWedgeSet_eq_coe_existsMem hx₀ r).symm ▸
    (existsMemCompactlyGeneratedPiSubcomplex fun _ : Fin r ↦ basepointSubcomplex hx₀).closed
  union' := (existsMemCompactlyGeneratedPiSubcomplex
    fun _ : Fin r ↦ basepointSubcomplex hx₀).union.trans
    (fatWedgeSet_eq_coe_existsMem hx₀ r).symm

@[simp]
theorem coe_fatWedgeSubcomplex (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    (fatWedgeSubcomplex hx₀ r :
      Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X))) =
      fatWedgeSet X x₀ r :=
  (rfl)

@[simp]
theorem mem_fatWedgeSubcomplex_I_iff (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {r n : ℕ}
    (c : cell (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X))) n) :
    c ∈ (fatWedgeSubcomplex hx₀ r).I n ↔
      ∃ i : Fin r,
        (⟨(cellCompactlyGeneratedPiUnivEquiv n c).1.1 i,
          (cellCompactlyGeneratedPiUnivEquiv n c).2 i⟩ : Σ m, cell (univ : Set X) m) =
          ⟨0, basepointCell hx₀⟩ := by
  change c ∈ (existsMemCompactlyGeneratedPiSubcomplex
    fun _ : Fin r ↦ basepointSubcomplex hx₀).I n ↔ _
  simp only [mem_existsMemCompactlyGeneratedPiSubcomplex_I_iff, mem_basepointSubcomplex_I_iff]

/-- The cells of `(X, x₀)` other than the basepoint `0`-cell, paired with their dimensions. -/
abbrev NonBasepointCell (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) : Type u :=
  {e : Σ m, cell (univ : Set X) m // e ≠ ⟨0, basepointCell hx₀⟩}

/-- The `n`-cells of `k(Xʳ)` outside the fat wedge correspond to `r`-tuples of non-basepoint cells
of `(X, x₀)` whose dimensions sum to `n`. -/
def nonFatWedgeCellEquiv (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r n : ℕ) :
    ↥((fatWedgeSubcomplex hx₀ r).I n)ᶜ ≃
      {w : Fin r → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n} where
  toFun c :=
    ⟨fun i ↦ ⟨⟨(cellCompactlyGeneratedPiUnivEquiv n c.1).1.1 i,
        (cellCompactlyGeneratedPiUnivEquiv n c.1).2 i⟩,
      fun h ↦ c.2 ((mem_fatWedgeSubcomplex_I_iff hx₀ c.1).2 ⟨i, h⟩)⟩,
      (cellCompactlyGeneratedPiUnivEquiv n c.1).1.2⟩
  invFun w :=
    ⟨(cellCompactlyGeneratedPiUnivEquiv n).symm
      ⟨⟨fun i ↦ (w.1 i).1.1, w.2⟩, fun i ↦ (w.1 i).1.2⟩,
      fun h ↦ by
        obtain ⟨i, hi⟩ := (mem_fatWedgeSubcomplex_I_iff hx₀ _).1 h
        rw [(cellCompactlyGeneratedPiUnivEquiv n).apply_symm_apply] at hi
        exact (w.1 i).2 hi⟩
  left_inv c := Subtype.ext <| by
    have hpc : (⟨⟨fun i ↦ (cellCompactlyGeneratedPiUnivEquiv n c.1).1.1 i,
        (cellCompactlyGeneratedPiUnivEquiv n c.1).1.2⟩,
      fun i ↦ (cellCompactlyGeneratedPiUnivEquiv n c.1).2 i⟩ :
        Σ d : {d : Fin r → ℕ // ∑ i, d i = n}, ∀ i, cell (univ : Set X) (d.1 i)) =
      cellCompactlyGeneratedPiUnivEquiv n c.1 := by
      rcases cellCompactlyGeneratedPiUnivEquiv n c.1 with ⟨⟨_, _⟩, _⟩
      rfl
    dsimp only
    rw [hpc, (cellCompactlyGeneratedPiUnivEquiv n).symm_apply_apply]
  right_inv w := Subtype.ext <| funext fun i ↦ Subtype.ext <| by
    let q : Σ d : {d : Fin r → ℕ // ∑ i, d i = n}, ∀ i, cell (univ : Set X) (d.1 i) :=
      ⟨⟨fun i ↦ (w.1 i).1.1, w.2⟩, fun i ↦ (w.1 i).1.2⟩
    change (⟨((cellCompactlyGeneratedPiUnivEquiv n)
        ((cellCompactlyGeneratedPiUnivEquiv n).symm q)).1.1 i,
      ((cellCompactlyGeneratedPiUnivEquiv n)
        ((cellCompactlyGeneratedPiUnivEquiv n).symm q)).2 i⟩ : Σ m, cell (univ : Set X) m) =
      (w.1 i).1
    rw [(cellCompactlyGeneratedPiUnivEquiv n).apply_symm_apply]

end BasepointAndFatWedge

section SubsingletonCW

/-- Any classical CW complex on `univ` of a `Subsingleton` space has no positive-dimensional
cells, since open balls of dimension `m + 1` have at least two distinct points. -/
private lemma isEmpty_cell_succ_of_subsingleton {Z : Type u} [TopologicalSpace Z] [Subsingleton Z]
    [CWComplex (univ : Set Z)] (m : ℕ) : IsEmpty (cell (univ : Set Z) (m + 1)) where
  false j := by
    let x₀ : Fin (m + 1) → ℝ := 0
    let x₁ : Fin (m + 1) → ℝ := fun _ ↦ 1 / 2
    have hx₀ : x₀ ∈ (RelCWComplex.map (m + 1) j).source := by
      rw [source_eq]; simp [x₀]
    have hx₁ : x₁ ∈ (RelCWComplex.map (m + 1) j).source := by
      rw [source_eq, mem_ball_zero_iff, pi_norm_lt_iff zero_lt_one]
      intro _
      norm_num [x₁]
    have heq := (RelCWComplex.map (m + 1) j).injOn hx₀ hx₁ (Subsingleton.elim _ _)
    have h0 := congrFun heq 0
    norm_num [x₀, x₁] at h0

end SubsingletonCW

section InductiveStages

variable {X : Type u} {x₀ : X} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- Auxiliary inductive package for the `r`-th filtration stage: Hausdorffness, CW structure on
`univ`, and cellularity of `mkFiltration r`. -/
private structure StageData (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) where
  t2 : T2Space (filtration X x₀ r)
  cw : CWComplex (univ : Set (filtration X x₀ r))
  mapsTo_skeletonLT : ∀ m : ℕ,
    letI := t2
    letI := cw
    MapsTo (mkFiltration (X := X) (x₀ := x₀) r)
      (CWComplex.skeletonLT
        (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X))) m)
      (CWComplex.skeletonLT (univ : Set (filtration X x₀ r)) m)

private def stageDataZero (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) : StageData hx₀ 0 where
  t2 := inferInstance
  cw := CWComplex.ofDiscreteTopology
  mapsTo_skeletonLT m y hy := by
    obtain ⟨p, hpm, _, _⟩ := CWComplex.mem_skeletonLT_iff.1 hy
    have hm : (0 : ℕ∞) < m := (Nat.cast_nonneg p).trans_lt hpm
    have hmem : mkFiltration 0 y ∈
        ⋃ (q : ℕ) (j : cell (univ : Set (filtration X x₀ 0)) q), openCell q j := by
      rw [CWComplex.iUnion_openCell_eq_complex]
      exact mem_univ _
    obtain ⟨q, j, hj⟩ := mem_iUnion₂.1 hmem
    cases q with
    | zero => exact CWComplex.mem_skeletonLT_iff.2 ⟨0, hm, j, hj⟩
    | succ q => exact (isEmpty_cell_succ_of_subsingleton q).elim j

/-- Pushout square presenting `J_(r + 1) X` as `relCWAdjunctionSpace` of the relative CW pair
`(univ, fatWedgeSet X x₀ (r + 1))` along `mkFatWedge r`. -/
private theorem isPushout_relCWBaseInclusion_fatWedge
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    letI : RelCWComplex
        (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
        (fatWedgeSet X x₀ (r + 1)) :=
      (fatWedgeSubcomplex hx₀ (r + 1)).relCWComplex
    IsPushout
      (relCWBaseInclusion
        (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X))))
      (TopCat.ofHom (mkFatWedge (X := X) (x₀ := x₀) r))
      ((TopCat.isoOfHomeo (Homeomorph.Set.univ
          (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))).hom ≫
        TopCat.ofHom
          (X := WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X))
          (mkFiltration (X := X) (x₀ := x₀) (r + 1)))
      ((filtrationDiagram X x₀).map (homOfLE r.le_succ)) := by
  let _ : RelCWComplex
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
      (fatWedgeSet X x₀ (r + 1)) :=
    (fatWedgeSubcomplex hx₀ (r + 1)).relCWComplex
  exact (isPushout_filtration_succ (X := X) (x₀ := x₀) isClosed_singleton r).of_iso'
    (Iso.refl _)
    (TopCat.isoOfHomeo (Homeomorph.Set.univ
      (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X))))
    (Iso.refl _) (Iso.refl _)
    (by ext y; rfl) rfl (Category.comp_id _).symm (by simp)

/-- Relative CW structure on `univ : Set (J_(r + 1) X)` relative to the image of `J_r X`,
transported from `relativeCWPushout` along the pushout isomorphism. -/
@[instance_reducible]
private def relCWComplexFiltrationSucc (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    RelCWComplex (univ : Set (filtration X x₀ (r + 1)))
      (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) :=
  letI : RelCWComplex
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
      (fatWedgeSet X x₀ (r + 1)) :=
    (fatWedgeSubcomplex hx₀ (r + 1)).relCWComplex
  letI := relativeCWPushout
    (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
    (mkFatWedge (X := X) (x₀ := x₀) r)
  let sq := isPushout_relCWBaseInclusion_fatWedge hx₀ r
  let e : relCWAdjunctionSpace
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
      (mkFatWedge (X := X) (x₀ := x₀) r) ≃ₜ filtration X x₀ (r + 1) :=
    TopCat.homeoOfIso sq.isoPushout.symm
  e.isClosedEmbedding.relCWComplex (image_univ.trans e.surjective.range_eq) <| by
    rw [← range_comp]
    exact congrArg range (funext fun w ↦ ConcreteCategory.congr_hom sq.inr_isoPushout_inv w)

/-- Identification of the `n`-cells of `(J_(r + 1) X, J_r X)` with the `n`-cells of `k(X^(r + 1))`
outside the fat wedge. -/
private def relCWComplexFiltrationSuccCellEquiv
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r n : ℕ) :
    (letI := relCWComplexFiltrationSucc hx₀ r;
      cell (univ : Set (filtration X x₀ (r + 1))) n) ≃
      ↥((fatWedgeSubcomplex hx₀ (r + 1)).I n)ᶜ :=
  let eFW := (fatWedgeSubcomplex hx₀ (r + 1)).relCWComplexCellEquiv n
  letI : RelCWComplex
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
      (fatWedgeSet X x₀ (r + 1)) :=
    (fatWedgeSubcomplex hx₀ (r + 1)).relCWComplex
  letI := relativeCWPushout
    (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
    (mkFatWedge (X := X) (x₀ := x₀) r)
  let sq := isPushout_relCWBaseInclusion_fatWedge hx₀ r
  let e : relCWAdjunctionSpace
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
      (mkFatWedge (X := X) (x₀ := x₀) r) ≃ₜ filtration X x₀ (r + 1) :=
    TopCat.homeoOfIso sq.isoPushout.symm
  (e.isClosedEmbedding.relCWComplexCellEquiv _ _ n).trans <|
    (relativeCWPushoutCellEquiv
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
      (mkFatWedge (X := X) (x₀ := x₀) r) n).trans eFW

/-- On the closed unit ball, the characteristic map of a relative `n`-cell of `(J_(r + 1) X, J_r X)`
is the characteristic map of the corresponding cell of `k(X^(r + 1))` followed by
`mkFiltration (r + 1)`. -/
private theorem relCWComplexFiltrationSucc_map_apply
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {r n : ℕ}
    (i : letI := relCWComplexFiltrationSucc hx₀ r; cell (univ : Set (filtration X x₀ (r + 1))) n)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    (letI := relCWComplexFiltrationSucc hx₀ r;
      RelCWComplex.map (C := (univ : Set (filtration X x₀ (r + 1)))) n i x) =
      mkFiltration (r + 1)
        (RelCWComplex.map n (relCWComplexFiltrationSuccCellEquiv hx₀ r n i).1 x) := by
  have hmapFW := fun i' ↦ (fatWedgeSubcomplex hx₀ (r + 1)).map_relCWComplex n i'
  let y₀ := RelCWComplex.map n (relCWComplexFiltrationSuccCellEquiv hx₀ r n i).1 x
  let _ : RelCWComplex
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
      (fatWedgeSet X x₀ (r + 1)) :=
    (fatWedgeSubcomplex hx₀ (r + 1)).relCWComplex
  let _ := relativeCWPushout
    (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
    (mkFatWedge (X := X) (x₀ := x₀) r)
  let sq := isPushout_relCWBaseInclusion_fatWedge hx₀ r
  let e : relCWAdjunctionSpace
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
      (mkFatWedge (X := X) (x₀ := x₀) r) ≃ₜ filtration X x₀ (r + 1) :=
    TopCat.homeoOfIso sq.isoPushout.symm
  let j := e.isClosedEmbedding.relCWComplexCellEquiv _ _ n i
  have h1 : (letI := relCWComplexFiltrationSucc hx₀ r;
      RelCWComplex.map (C := (univ : Set (filtration X x₀ (r + 1)))) n i x) =
      sq.isoPushout.inv (RelCWComplex.map n j x) :=
    congrFun (e.isClosedEmbedding.coe_map_relCWComplex _ _ n i) x
  rw [h1, relativeCWPushout_map_apply]
  have h2 : RelCWComplex.map n (relativeCWPushoutCellEquiv _
      (mkFatWedge (X := X) (x₀ := x₀) r) n j) x = y₀ :=
    congrFun (congrArg PartialEquiv.toFun
      (hmapFW (relativeCWPushoutCellEquiv _ (mkFatWedge (X := X) (x₀ := x₀) r) n j)))
      (x : Fin n → ℝ)
  exact (congrArg (fun y ↦ sq.isoPushout.inv
      (pushout.inl (relCWBaseInclusion _) (TopCat.ofHom (mkFatWedge (X := X) (x₀ := x₀) r))
        ⟨y, mem_univ _⟩)) h2).trans <|
    ConcreteCategory.congr_hom sq.inl_isoPushout_inv ⟨y₀, mem_univ _⟩

private theorem image_relCWComplexFiltrationSucc_map
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {r n : ℕ}
    (i : letI := relCWComplexFiltrationSucc hx₀ r; cell (univ : Set (filtration X x₀ (r + 1))) n)
    {S : Set (Fin n → ℝ)} (hS : S ⊆ closedBall 0 1) :
    (letI := relCWComplexFiltrationSucc hx₀ r;
      RelCWComplex.map (C := (univ : Set (filtration X x₀ (r + 1)))) n i '' S) =
      mkFiltration (r + 1) ''
        (RelCWComplex.map n (relCWComplexFiltrationSuccCellEquiv hx₀ r n i).1 '' S) := by
  rw [← image_comp]
  exact image_congr fun x hx ↦
    relCWComplexFiltrationSucc_map_apply hx₀ i ⟨x, hS hx⟩

/-- Coordinate deletion on skeleta: any point of the `m`-skeleton of `k(X^(r + 1))` lying in the fat
wedge maps under `mkFiltration (r + 1)` into the image of the `m`-skeleton of `J_r X`. -/
private theorem mkFiltration_mem_image_skeletonLT
    {hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0} {r : ℕ} (sd : StageData hx₀ r) {m : ℕ}
    {y : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)}
    (hy_skel : y ∈ (CWComplex.skeletonLT
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X))) m :
        Set _))
    (hy_fw : y ∈ fatWedgeSet X x₀ (r + 1)) :
    letI := sd.t2
    letI := sd.cw
    mkFiltration (r + 1) y ∈ Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ) ''
      (CWComplex.skeletonLT (univ : Set (filtration X x₀ r)) m : Set (filtration X x₀ r)) := by
  have := sd.t2
  let _ := sd.cw
  obtain ⟨p, hpm, c', hyc'⟩ := CWComplex.mem_skeletonLT_iff.1 hy_skel
  obtain ⟨j₀, hj₀⟩ := mem_fatWedgeSet_iff.1 hy_fw
  let pc := cellCompactlyGeneratedPiUnivEquiv p c'
  rw [← (cellCompactlyGeneratedPiUnivEquiv p).symm_apply_apply c',
    openCell_cellCompactlyGeneratedPiUnivEquiv_symm] at hyc'
  have hd0 : pc.1.1 j₀ = 0 :=
    congrArg Sigma.fst (eq_basepointCell_of_mem_openCell hx₀ (hj₀ ▸ hyc' j₀ trivial))
  have hd' : ∑ i : Fin r, pc.1.1 (j₀.succAbove i) = p := by
    have hsum := (Fin.sum_univ_succAbove pc.1.1 j₀).symm
    rwa [hd0, zero_add, pc.1.2] at hsum
  let c_del :
      cell (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X))) p :=
    (cellCompactlyGeneratedPiUnivEquiv p).symm
      ⟨⟨fun i ↦ pc.1.1 (j₀.succAbove i), hd'⟩, fun i ↦ pc.2 (j₀.succAbove i)⟩
  let y_del : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X) :=
    WithGeneratedByTopology.equiv.symm (WithGeneratedByTopology.equiv y ∘ j₀.succAbove)
  have hydel_skel : y_del ∈ CWComplex.skeletonLT
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X))) m := by
    refine CWComplex.mem_skeletonLT_iff.2 ⟨p, hpm, c_del, ?_⟩
    rw [openCell_cellCompactlyGeneratedPiUnivEquiv_symm]
    intro i _
    simpa [y_del] using hyc' (j₀.succAbove i) trivial
  refine ⟨mkFiltration r y_del, sd.mapsTo_skeletonLT m hydel_skel, Subtype.ext ?_⟩
  simp only [coe_mkFiltration_apply, y_del, Equiv.apply_symm_apply]
  refine mk_comp_strictMono_of_eq_basepoint (Fin.strictMono_succAbove j₀) fun i hi ↦ ?_
  simp only [Fin.range_succAbove, mem_compl_iff, mem_singleton_iff, not_not] at hi
  exact hi ▸ hj₀

private theorem t2Space_succ_of_stageData
    {hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0} {r : ℕ} (sd : StageData hx₀ r) :
    T2Space (filtration X x₀ (r + 1)) := by
  have := sd.t2
  let _ : RelCWComplex
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)))
      (fatWedgeSet X x₀ (r + 1)) :=
    (fatWedgeSubcomplex hx₀ (r + 1)).relCWComplex
  exact (TopCat.homeoOfIso (isPushout_relCWBaseInclusion_fatWedge hx₀ r).isoPushout.symm).t2Space

/-- Boundary-compatibility for `relCWComplexTrans` at stage `r + 1`. -/
private theorem cellFrontier_inter_range_subset_skeletonLT
    {hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0} {r : ℕ} (sd : StageData hx₀ r) (n : ℕ)
    (i : letI := relCWComplexFiltrationSucc hx₀ r; cell (univ : Set (filtration X x₀ (r + 1))) n) :
    letI := sd.t2
    letI := sd.cw
    letI := t2Space_succ_of_stageData sd
    letI := relCWComplexFiltrationSucc hx₀ r
    letI : RelCWComplex
        (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) ∅ :=
      (isClosedEmbedding_filtrationInclusion (X := X) (x₀ := x₀) isClosed_singleton
        r.le_succ).relCWComplex image_univ (image_empty _)
    cellFrontier (C := (univ : Set (filtration X x₀ (r + 1)))) n i ∩
        range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ)) ⊆
      skeletonLT (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) n := by
  have := sd.t2
  let _ := sd.cw
  have := t2Space_succ_of_stageData sd
  let _ := relCWComplexFiltrationSucc hx₀ r
  let hf := isClosedEmbedding_filtrationInclusion (X := X) (x₀ := x₀) isClosed_singleton r.le_succ
  let _ : RelCWComplex
      (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) ∅ :=
    hf.relCWComplex image_univ (image_empty _)
  rintro _ ⟨hz_fr, w, rfl⟩
  have hz_im : Set.inclusion (filtration_monotone r.le_succ) w ∈
      mkFiltration (r + 1) '' cellFrontier n (relCWComplexFiltrationSuccCellEquiv hx₀ r n i).1 := by
    simpa only [cellFrontier,
      image_relCWComplexFiltrationSucc_map hx₀ i sphere_subset_closedBall] using hz_fr
  obtain ⟨y, hy_fr, hy_eq⟩ := hz_im
  have hy_skel : y ∈ CWComplex.skeletonLT
      (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X))) n :=
    cellFrontier_subset_skeletonLT n _ hy_fr
  have hy_fw : y ∈ fatWedgeSet X x₀ (r + 1) := by
    have hmem : (mk (WithGeneratedByTopology.equiv y) : JamesReducedProduct X x₀) ∈
        filtration X x₀ r := by
      have hval : (mk (WithGeneratedByTopology.equiv y) : JamesReducedProduct X x₀) = w.1 := by
        simpa only [coe_mkFiltration_apply, Set.coe_inclusion] using congrArg Subtype.val hy_eq
      exact hval ▸ w.2
    exact mem_fatWedgeSet_iff.2 (mk_mem_filtration_iff_exists_eq_basepoint.1 hmem)
  obtain ⟨w', hw'_skel, hw'_eq⟩ := mkFiltration_mem_image_skeletonLT sd hy_skel hy_fw
  obtain ⟨p, hpn, j, hj⟩ := CWComplex.mem_skeletonLT_iff.1 hw'_skel
  refine mem_skeletonLT_iff.2 (.inr ⟨p, hpn,
    (hf.relCWComplexCellEquiv image_univ (image_empty _) p).symm j, ?_⟩)
  rw [hf.openCell_relCWComplex, Equiv.apply_symm_apply]
  exact ⟨w', hj, hw'_eq.trans hy_eq⟩

@[instance_reducible]
private def cwComplexSuccOfStageData {hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0} {r : ℕ}
    (sd : StageData hx₀ r) :
    CWComplex (univ : Set (filtration X x₀ (r + 1))) :=
  letI := sd.t2
  letI := sd.cw
  letI := t2Space_succ_of_stageData sd
  letI := relCWComplexFiltrationSucc hx₀ r
  let hf := isClosedEmbedding_filtrationInclusion (X := X) (x₀ := x₀) isClosed_singleton r.le_succ
  letI : RelCWComplex
      (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) ∅ :=
    hf.relCWComplex image_univ (image_empty _)
  let htrans := relCWComplexTrans (univ : Set (filtration X x₀ (r + 1)))
    (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) ∅
    (cellFrontier_inter_range_subset_skeletonLT sd)
  @RelCWComplex.toCWComplex _ _ _ htrans

private theorem mapsTo_skeletonLT_succ_of_stageData
    {hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0} {r : ℕ} (sd : StageData hx₀ r) (m : ℕ) :
    letI := t2Space_succ_of_stageData sd
    letI := cwComplexSuccOfStageData sd
    MapsTo (mkFiltration (X := X) (x₀ := x₀) (r + 1))
      (CWComplex.skeletonLT
        (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X))) m)
      (CWComplex.skeletonLT (univ : Set (filtration X x₀ (r + 1))) m) := by
  intro y hy
  have := sd.t2
  let _ := sd.cw
  have := t2Space_succ_of_stageData sd
  let hrel := relCWComplexFiltrationSucc hx₀ r
  let hf := isClosedEmbedding_filtrationInclusion (X := X) (x₀ := x₀) isClosed_singleton r.le_succ
  let _ : RelCWComplex
      (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) ∅ :=
    hf.relCWComplex image_univ (image_empty _)
  let hsub := cellFrontier_inter_range_subset_skeletonLT sd
  let eTrans := fun p ↦ relCWComplexTransCellEquiv hsub p
  have hopen_inl := fun p i ↦ openCell_relCWComplexTrans_inl hsub p i
  have hopen_inr := fun p i ↦ openCell_relCWComplexTrans_inr hsub p i
  let _ := cwComplexSuccOfStageData sd
  by_cases hy_fw : y ∈ fatWedgeSet X x₀ (r + 1)
  · obtain ⟨w, hw, hw_eq⟩ := mkFiltration_mem_image_skeletonLT sd hy hy_fw
    obtain ⟨p, hpm, j, hj⟩ := CWComplex.mem_skeletonLT_iff.1 hw
    let i_base := (hf.relCWComplexCellEquiv image_univ (image_empty _) p).symm j
    refine CWComplex.mem_skeletonLT_iff.2 ⟨p, hpm, (eTrans p).symm (.inl i_base), ?_⟩
    change mkFiltration (r + 1) y ∈
      @openCell _ _ _ ∅ (relCWComplexTrans _ _ ∅ hsub) p ((eTrans p).symm (.inl i_base))
    rw [hopen_inl, hf.openCell_relCWComplex, Equiv.apply_symm_apply]
    exact ⟨w, hj, hw_eq⟩
  · obtain ⟨p, hpm, c', hyc'⟩ := CWComplex.mem_skeletonLT_iff.1 hy
    have hc' : c' ∉ (fatWedgeSubcomplex hx₀ (r + 1)).I p := fun hmem ↦
      hy_fw ((fatWedgeSubcomplex hx₀ (r + 1)).openCell_subset_of_mem hmem hyc')
    let i_rel := (relCWComplexFiltrationSuccCellEquiv hx₀ r p).symm ⟨c', hc'⟩
    refine CWComplex.mem_skeletonLT_iff.2 ⟨p, hpm, (eTrans p).symm (.inr i_rel), ?_⟩
    change mkFiltration (r + 1) y ∈
      @openCell _ _ _ ∅ (relCWComplexTrans _ _ ∅ hsub) p ((eTrans p).symm (.inr i_rel))
    rw [hopen_inr]
    change mkFiltration (r + 1) y ∈ @RelCWComplex.map _ _ _ _ hrel p i_rel '' ball 0 1
    rw [image_relCWComplexFiltrationSucc_map hx₀ i_rel ball_subset_closedBall]
    have heq : (relCWComplexFiltrationSuccCellEquiv hx₀ r p i_rel).1 = c' := by
      simp [i_rel]
    rw [heq]
    exact mem_image_of_mem _ hyc'

private def stageDataSucc {hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0} {r : ℕ}
    (sd : StageData hx₀ r) : StageData hx₀ (r + 1) where
  t2 := t2Space_succ_of_stageData sd
  cw := cwComplexSuccOfStageData sd
  mapsTo_skeletonLT := mapsTo_skeletonLT_succ_of_stageData sd

private def stageData (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    ∀ r : ℕ, StageData hx₀ r
  | 0 => stageDataZero hx₀
  | r + 1 => stageDataSucc (stageData hx₀ r)

/-- Each stage `J_r X` of the word-length filtration is Hausdorff when `X` is a Hausdorff CW complex
pointed at a `0`-cell. -/
theorem t2Space_filtration (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    T2Space (filtration X x₀ r) :=
  (stageData hx₀ r).t2

/-- **CW structure on the `r`-th stage `J_r X` of the James filtration.** -/
@[instance_reducible]
def cwComplexFiltrationUniv (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    CWComplex (univ : Set (filtration X x₀ r)) :=
  (stageData hx₀ r).cw

/-- Each stage `J_r X` has CW type. -/
theorem cwType_filtration (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    CWType (filtration X x₀ r) := by
  have := t2Space_filtration hx₀ r
  let _ := cwComplexFiltrationUniv hx₀ r
  infer_instance

/-- **Cellularity of word reduction `k(Xʳ) → J_r X`** (`skeletonLT` form). -/
theorem mapsTo_mkFiltration_skeletonLT (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0)
    (r : ℕ) (m : ℕ) :
    letI := t2Space_filtration hx₀ r
    letI := cwComplexFiltrationUniv hx₀ r
    MapsTo (mkFiltration (X := X) (x₀ := x₀) r)
      (CWComplex.skeletonLT
        (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X))) m)
      (CWComplex.skeletonLT (univ : Set (filtration X x₀ r)) m) :=
  (stageData hx₀ r).mapsTo_skeletonLT m

/-- **Cellularity of word reduction `k(Xʳ) → J_r X`** (`skeleton` form). -/
theorem mapsTo_mkFiltration_skeleton (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0)
    (r : ℕ) (m : ℕ) :
    letI := t2Space_filtration hx₀ r
    letI := cwComplexFiltrationUniv hx₀ r
    MapsTo (mkFiltration (X := X) (x₀ := x₀) r)
      (CWComplex.skeleton
        (univ : Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X))) m)
      (CWComplex.skeleton (univ : Set (filtration X x₀ r)) m) := by
  simpa only [CWComplex.skeleton, ← Nat.cast_add_one] using
    mapsTo_mkFiltration_skeletonLT hx₀ r (m + 1)

/-- Decomposition of the `n`-cells of `J_(r + 1) X` into the `n`-cells of `J_r X` and the relative
`n`-cells of `(J_(r + 1) X, J_r X)`. -/
private def filtrationStageSuccCellEquiv
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r n : ℕ) :
    (letI := cwComplexFiltrationUniv hx₀ (r + 1);
      cell (univ : Set (filtration X x₀ (r + 1))) n) ≃
      (letI := cwComplexFiltrationUniv hx₀ r; cell (univ : Set (filtration X x₀ r)) n) ⊕
        (letI := relCWComplexFiltrationSucc hx₀ r;
          cell (univ : Set (filtration X x₀ (r + 1))) n) :=
  letI := (stageData hx₀ r).t2
  letI := (stageData hx₀ r).cw
  letI := t2Space_succ_of_stageData (stageData hx₀ r)
  letI := relCWComplexFiltrationSucc hx₀ r
  let hf := isClosedEmbedding_filtrationInclusion (X := X) (x₀ := x₀) isClosed_singleton r.le_succ
  letI : RelCWComplex
      (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) ∅ :=
    hf.relCWComplex image_univ (image_empty _)
  (relCWComplexTransCellEquiv
    (cellFrontier_inter_range_subset_skeletonLT (stageData hx₀ r)) n).trans
    (Equiv.sumCongr (hf.relCWComplexCellEquiv image_univ (image_empty _) n) (Equiv.refl _))

/-- The cellular inclusion of `n`-cells of `J_r X` into `n`-cells of `J_(r + 1) X`. -/
def filtrationCellInclusion (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r n : ℕ) :
    (letI := cwComplexFiltrationUniv hx₀ r; cell (univ : Set (filtration X x₀ r)) n) →
      (letI := cwComplexFiltrationUniv hx₀ (r + 1);
        cell (univ : Set (filtration X x₀ (r + 1))) n) :=
  fun i ↦ (filtrationStageSuccCellEquiv hx₀ r n).symm (.inl i)

@[simp]
theorem coe_map_filtrationCellInclusion (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0)
    (r n : ℕ)
    (i : letI := cwComplexFiltrationUniv hx₀ r; cell (univ : Set (filtration X x₀ r)) n) :
    ⇑(letI := cwComplexFiltrationUniv hx₀ (r + 1);
        RelCWComplex.map (C := (univ : Set (filtration X x₀ (r + 1)))) n
          (filtrationCellInclusion hx₀ r n i)) =
      ((filtrationDiagram X x₀).map (homOfLE r.le_succ)) ∘
        (letI := cwComplexFiltrationUniv hx₀ r;
          RelCWComplex.map (C := (univ : Set (filtration X x₀ r))) n i) := by
  have := (stageData hx₀ r).t2
  let _ := (stageData hx₀ r).cw
  have := t2Space_succ_of_stageData (stageData hx₀ r)
  let _ := relCWComplexFiltrationSucc hx₀ r
  let hf := isClosedEmbedding_filtrationInclusion (X := X) (x₀ := x₀) isClosed_singleton r.le_succ
  let _ : RelCWComplex
      (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) ∅ :=
    hf.relCWComplex image_univ (image_empty _)
  change ⇑(@RelCWComplex.map _ _ _ ∅ (relCWComplexTrans _ _ ∅
    (cellFrontier_inter_range_subset_skeletonLT (stageData hx₀ r))) n
    ((relCWComplexTransCellEquiv _ n).symm
      (.inl ((hf.relCWComplexCellEquiv image_univ (image_empty _) n).symm i)))) = _
  rw [map_relCWComplexTrans_inl, hf.coe_map_relCWComplex, Equiv.apply_symm_apply]
  rfl

private theorem openCell_filtrationStageSuccCellEquiv_symm_inr
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {r n : ℕ}
    (b : letI := relCWComplexFiltrationSucc hx₀ r; cell (univ : Set (filtration X x₀ (r + 1))) n) :
    (letI := cwComplexFiltrationUniv hx₀ (r + 1);
      openCell (C := (univ : Set (filtration X x₀ (r + 1)))) n
        ((filtrationStageSuccCellEquiv hx₀ r n).symm (.inr b))) =
      (letI := relCWComplexFiltrationSucc hx₀ r;
        openCell (C := (univ : Set (filtration X x₀ (r + 1)))) n b) := by
  have := (stageData hx₀ r).t2
  let _ := (stageData hx₀ r).cw
  have := t2Space_succ_of_stageData (stageData hx₀ r)
  let _ := relCWComplexFiltrationSucc hx₀ r
  let hf := isClosedEmbedding_filtrationInclusion (X := X) (x₀ := x₀) isClosed_singleton r.le_succ
  let _ : RelCWComplex
      (range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) r.le_succ))) ∅ :=
    hf.relCWComplex image_univ (image_empty _)
  exact openCell_relCWComplexTrans_inr
    (cellFrontier_inter_range_subset_skeletonLT (stageData hx₀ r)) n b

end InductiveStages

section ColimitAndSubcomplexes

variable {X : Type u} {x₀ : X} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- **Hausdorffness of the James reduced product** of a Hausdorff CW complex pointed at a
`0`-cell. -/
theorem t2Space (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    T2Space (JamesReducedProduct X x₀) := by
  let _ (k : ℕ) : CWComplex (univ : Set ((filtrationDiagram X x₀).obj k)) :=
    cwComplexFiltrationUniv hx₀ k
  have (k : ℕ) : T2Space ((filtrationDiagram X x₀).obj k) := t2Space_filtration hx₀ k
  exact t2Space_of_isColimit_cwComplex
    (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
    (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀)

/-- **CW structure on the James reduced product `J X`** of a Hausdorff CW complex pointed at a
`0`-cell, obtained as the sequential colimit of the stages `J_r X` along closed cellular
embeddings. -/
@[instance_reducible]
def cwComplexUniv (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    CWComplex (univ : Set (JamesReducedProduct X x₀)) :=
  letI (k : ℕ) : CWComplex (univ : Set ((filtrationDiagram X x₀).obj k)) :=
    cwComplexFiltrationUniv hx₀ k
  cwComplexOfIsColimit
    (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
    (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀)

/-- The James reduced product of a Hausdorff CW complex pointed at a `0`-cell has CW type. -/
theorem cwType (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    CWType (JamesReducedProduct X x₀) := by
  have := t2Space hx₀
  let _ := cwComplexUniv hx₀
  infer_instance

/-- The `n`-cells of `J₀ X` correspond to `0`-tuples of non-basepoint cells of total dimension `n`
(unique when `n = 0`, empty when `n > 0`). -/
private def filtrationZeroCellEquiv (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    ∀ n : ℕ,
      (letI := cwComplexFiltrationUniv hx₀ 0; cell (univ : Set (filtration X x₀ 0)) n) ≃
        {w : Fin 0 → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n}
  | 0 =>
    letI := t2Space_filtration hx₀ 0
    letI := cwComplexFiltrationUniv hx₀ 0
    haveI : Unique ↑(CWComplex.skeletonLT (univ : Set (filtration X x₀ 0)) ((1 : ℕ) : ℕ∞)) :=
      { default := ⟨default, by
          have hmem : (default : filtration X x₀ 0) ∈
              ⋃ (q : ℕ) (j : cell (univ : Set (filtration X x₀ 0)) q), openCell q j := by
            rw [CWComplex.iUnion_openCell_eq_complex]
            exact mem_univ _
          obtain ⟨q, j, hj⟩ := mem_iUnion₂.1 hmem
          cases q with
          | zero => exact CWComplex.mem_skeletonLT_iff.2 ⟨0, by norm_cast, j, hj⟩
          | succ q => exact (isEmpty_cell_succ_of_subsingleton q).elim j⟩
        uniq := fun x ↦ Subtype.ext (Subsingleton.elim _ _) }
    haveI : Unique (cell (univ : Set (filtration X x₀ 0)) 0) :=
      (zeroCellEquiv (univ : Set (filtration X x₀ 0))).unique
    haveI : Unique {w : Fin 0 → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = 0} :=
      { default := ⟨Fin.elim0, rfl⟩
        uniq := fun ⟨w, _⟩ ↦ Subtype.ext (Subsingleton.elim _ _) }
    Equiv.ofUnique _ _
  | m + 1 =>
    letI := cwComplexFiltrationUniv hx₀ 0
    haveI : IsEmpty (cell (univ : Set (filtration X x₀ 0)) (m + 1)) :=
      isEmpty_cell_succ_of_subsingleton m
    haveI : IsEmpty {w : Fin 0 → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = m + 1} :=
      ⟨fun ⟨_, h⟩ ↦ Nat.succ_ne_zero m h.symm⟩
    Equiv.equivOfIsEmpty _ _

private def extractRight {α β : Type*} : {s : α ⊕ β // s.isRight = true} → β
  | ⟨.inr b, _⟩ => b

private lemma extractRight_eq_of_eq_inr {α β : Type*} {s : α ⊕ β} (hs : s.isRight = true)
    {b : β} (h : s = .inr b) : extractRight ⟨s, hs⟩ = b := by
  cases h
  rfl

private lemma isRight_filtrationStageSuccCellEquiv_of_notMem_range
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {k n : ℕ}
    (c : ↥(range (filtrationCellInclusion hx₀ k n))ᶜ) :
    (filtrationStageSuccCellEquiv hx₀ k n c.1).isRight = true := by
  cases h : filtrationStageSuccCellEquiv hx₀ k n c.1 with
  | inl a =>
    exact (c.2 ⟨a, (filtrationStageSuccCellEquiv hx₀ k n).symm_apply_eq.2 h.symm⟩).elim
  | inr _ => rfl

/-- The new `n`-cells of `J_(k + 1) X` (those outside `range (filtrationCellInclusion hx₀ k n)`)
correspond to the relative `n`-cells of `(J_(k + 1) X, J_k X)`. -/
private def complRangeFiltrationCellInclusionEquiv
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (k n : ℕ) :
    ↥(range (filtrationCellInclusion hx₀ k n))ᶜ ≃
      (letI := relCWComplexFiltrationSucc hx₀ k;
        cell (univ : Set (filtration X x₀ (k + 1))) n) :=
  let eS := filtrationStageSuccCellEquiv hx₀ k n
  { toFun := fun c ↦
      extractRight ⟨eS c.1, isRight_filtrationStageSuccCellEquiv_of_notMem_range hx₀ c⟩
    invFun := fun b ↦ ⟨eS.symm (.inr b), by
      rintro ⟨a, ha⟩
      exact Sum.inl_ne_inr
        ((eS.eq_symm_apply.1 ha.symm).symm.trans (eS.apply_symm_apply (.inr b)))⟩
    left_inv := fun c ↦ Subtype.ext <| by
      have key : ∀ (s : _ ⊕ _) (hs : s.isRight = true), eS c.1 = s →
          eS.symm (.inr (extractRight ⟨s, hs⟩)) = c.1 := by
        rintro (a | b) hs h
        · cases hs
        · exact eS.symm_apply_eq.2 h.symm
      exact key (eS c.1) (isRight_filtrationStageSuccCellEquiv_of_notMem_range hx₀ c) rfl
    right_inv := fun b ↦ extractRight_eq_of_eq_inr _ (eS.apply_symm_apply (.inr b)) }

/-- **Cells of `J X` as tuples of non-basepoint cells** (Hatcher, Proposition 3.C.1): the `n`-cells
of `cwComplexUniv hx₀` are in canonical bijection with pairs `(r, w)` where `w` is an `r`-tuple of
non-basepoint cells of `(X, x₀)` whose dimensions sum to `n`. -/
def cellEquiv (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (n : ℕ) :
    (letI := cwComplexUniv hx₀; cell (univ : Set (JamesReducedProduct X x₀)) n) ≃
      Σ r : ℕ, {w : Fin r → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n} :=
  letI (k : ℕ) : CWComplex (univ : Set ((filtrationDiagram X x₀).obj k)) :=
    cwComplexFiltrationUniv hx₀ k
  (cwComplexOfIsColimitCellEquiv
    (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
    (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) n).trans <|
    (Equiv.sumCongr (filtrationZeroCellEquiv hx₀ n)
      (Equiv.sigmaCongrRight fun k ↦
        (complRangeFiltrationCellInclusionEquiv hx₀ k n).trans <|
          (relCWComplexFiltrationSuccCellEquiv hx₀ k n).trans
            (nonFatWedgeCellEquiv hx₀ (k + 1) n))).trans
      (Equiv.sigmaNatSucc fun r ↦ {w : Fin r → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n}).symm

private lemma sigma_subtype_ext {α : Type*} {P : ∀ r, (Fin r → α) → Prop}
    {r₁ r₂ : ℕ} {w₁ : Fin r₁ → α} {w₂ : Fin r₂ → α} {hw₁ : P r₁ w₁} {hw₂ : P r₂ w₂}
    (hr : r₁ = r₂) (hw : w₁ ≍ w₂) :
    (⟨r₁, ⟨w₁, hw₁⟩⟩ : Σ r, {w : Fin r → α // P r w}) = ⟨r₂, ⟨w₂, hw₂⟩⟩ := by
  subst hr
  cases eq_of_heq hw
  rfl

/-- **Cells of `J X` as reduced words of non-basepoint cells** (Hatcher, Proposition 3.C.1): the
`n`-cells of `cwComplexUniv hx₀` correspond to elements of `FreeMonoid (NonBasepointCell hx₀)` whose
cell dimensions sum to `n`. -/
def cellEquivFreeMonoid (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (n : ℕ) :
    (letI := cwComplexUniv hx₀; cell (univ : Set (JamesReducedProduct X x₀)) n) ≃
      {w : FreeMonoid (NonBasepointCell hx₀) // (w.toList.map (·.1.1)).sum = n} :=
  (cellEquiv hx₀ n).trans
    { toFun := fun ⟨_, w, hw⟩ ↦
        ⟨FreeMonoid.ofList (List.ofFn w), by
          rw [FreeMonoid.toList_ofList, List.map_ofFn, List.sum_ofFn]
          exact hw⟩
      invFun := fun ⟨w, hw⟩ ↦
        ⟨w.toList.length, w.toList.get, by
          conv at hw => rw [← List.ofFn_get w.toList, List.map_ofFn, List.sum_ofFn]
          exact hw⟩
      left_inv := fun ⟨r, w, _⟩ ↦ by
        have h : (⟨(List.ofFn w).length, (List.ofFn w).get⟩ :
            Σ m, Fin m → NonBasepointCell hx₀) = ⟨r, w⟩ :=
          List.equivSigmaTuple.right_inv ⟨r, w⟩
        dsimp only [FreeMonoid.toList_ofList]
        exact sigma_subtype_ext (P := fun r w ↦ ∑ i, (w i).1.1 = n)
          (Sigma.mk.inj_iff.1 h).1 (Sigma.mk.inj_iff.1 h).2
      right_inv := fun ⟨w, _⟩ ↦ Subtype.ext <| by
        simp [List.ofFn_get, FreeMonoid.ofList_toList] }

private lemma cellEquiv_fst_of_inl (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {n : ℕ}
    {c : letI := cwComplexUniv hx₀; cell (univ : Set (JamesReducedProduct X x₀)) n}
    {i₀ : letI := cwComplexFiltrationUniv hx₀ 0; cell (univ : Set (filtration X x₀ 0)) n}
    (he : (letI (k : ℕ) : CWComplex (univ : Set ((filtrationDiagram X x₀).obj k)) :=
        cwComplexFiltrationUniv hx₀ k
      cwComplexOfIsColimitCellEquiv
        (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
        (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) n c) = .inl i₀) :
    (cellEquiv hx₀ n c).1 = 0 := by
  let _ (k : ℕ) : CWComplex (univ : Set ((filtrationDiagram X x₀).obj k)) :=
    cwComplexFiltrationUniv hx₀ k
  have hce : cellEquiv hx₀ n c =
      (Equiv.sigmaNatSucc fun r ↦ {w : Fin r → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n}).symm
        ((Equiv.sumCongr (filtrationZeroCellEquiv hx₀ n)
          (Equiv.sigmaCongrRight fun k ↦
            (complRangeFiltrationCellInclusionEquiv hx₀ k n).trans <|
              (relCWComplexFiltrationSuccCellEquiv hx₀ k n).trans
                (nonFatWedgeCellEquiv hx₀ (k + 1) n)))
          (cwComplexOfIsColimitCellEquiv
            (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
            (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) n c)) := rfl
  rw [hce, he]
  rfl

private lemma cellEquiv_fst_of_inr (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {k n : ℕ}
    {c : letI := cwComplexUniv hx₀; cell (univ : Set (JamesReducedProduct X x₀)) n}
    {j : ↥(range (filtrationCellInclusion hx₀ k n))ᶜ}
    (he : (letI (k : ℕ) : CWComplex (univ : Set ((filtrationDiagram X x₀).obj k)) :=
        cwComplexFiltrationUniv hx₀ k
      cwComplexOfIsColimitCellEquiv
        (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
        (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) n c) =
      .inr ⟨k, j⟩) :
    (cellEquiv hx₀ n c).1 = k + 1 := by
  let _ (k : ℕ) : CWComplex (univ : Set ((filtrationDiagram X x₀).obj k)) :=
    cwComplexFiltrationUniv hx₀ k
  have hce : cellEquiv hx₀ n c =
      (Equiv.sigmaNatSucc fun r ↦ {w : Fin r → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n}).symm
        ((Equiv.sumCongr (filtrationZeroCellEquiv hx₀ n)
          (Equiv.sigmaCongrRight fun k ↦
            (complRangeFiltrationCellInclusionEquiv hx₀ k n).trans <|
              (relCWComplexFiltrationSuccCellEquiv hx₀ k n).trans
                (nonFatWedgeCellEquiv hx₀ (k + 1) n)))
          (cwComplexOfIsColimitCellEquiv
            (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
            (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) n c)) := rfl
  rw [hce, he]
  rfl

private theorem openCell_subset_filtration_cellEquiv_fst
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {n : ℕ}
    (c : letI := cwComplexUniv hx₀; cell (univ : Set (JamesReducedProduct X x₀)) n) :
    (letI := cwComplexUniv hx₀; openCell (C := (univ : Set (JamesReducedProduct X x₀))) n c) ⊆
      filtration X x₀ (cellEquiv hx₀ n c).1 := by
  let _ (k : ℕ) : CWComplex (univ : Set ((filtrationDiagram X x₀).obj k)) :=
    cwComplexFiltrationUniv hx₀ k
  let _ (k : ℕ) : CWComplex (univ : Set (filtration X x₀ k)) :=
    cwComplexFiltrationUniv hx₀ k
  let eColim := cwComplexOfIsColimitCellEquiv
    (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
    (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) n
  rcases he : eColim c with i₀ | ⟨k, j⟩
  · rw [cellEquiv_fst_of_inl hx₀ he, ← eColim.symm_apply_apply c, he]
    rintro _ ⟨x, _, rfl⟩
    have hmap := congrFun
      (coe_map_cwComplexOfIsColimitCellEquiv_symm_inl
        (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
        (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) i₀) x
    exact hmap.symm ▸ (RelCWComplex.map n i₀ x).2
  · rw [cellEquiv_fst_of_inr hx₀ he, ← eColim.symm_apply_apply c, he]
    rintro _ ⟨x, _, rfl⟩
    have hmap := congrFun
      (coe_map_cwComplexOfIsColimitCellEquiv_symm_inr
        (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
        (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) ⟨k, j⟩) x
    exact hmap.symm ▸ (RelCWComplex.map n j.1 x).2

private theorem cellEquiv_fst_le_of_mem_openCell_of_mem_filtration
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {r n : ℕ}
    {c : letI := cwComplexUniv hx₀; cell (univ : Set (JamesReducedProduct X x₀)) n}
    {w : JamesReducedProduct X x₀}
    (hwc : w ∈ (letI := cwComplexUniv hx₀;
      openCell (C := (univ : Set (JamesReducedProduct X x₀))) n c))
    (hwr : w ∈ filtration X x₀ r) : (cellEquiv hx₀ n c).1 ≤ r := by
  let _ (k : ℕ) : CWComplex (univ : Set ((filtrationDiagram X x₀).obj k)) :=
    cwComplexFiltrationUniv hx₀ k
  let _ (k : ℕ) : CWComplex (univ : Set (filtration X x₀ k)) :=
    cwComplexFiltrationUniv hx₀ k
  let eColim := cwComplexOfIsColimitCellEquiv
    (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
    (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) n
  rcases he : eColim c with i₀ | ⟨k, j⟩
  · rw [cellEquiv_fst_of_inl hx₀ he]
    exact Nat.zero_le r
  · rw [cellEquiv_fst_of_inr hx₀ he]
    by_contra! hlt
    have hrk : r ≤ k := Nat.lt_succ_iff.1 hlt
    rw [← eColim.symm_apply_apply c, he] at hwc
    obtain ⟨x, hx_ball, hxc⟩ := hwc
    have hmap := congrFun
      (coe_map_cwComplexOfIsColimitCellEquiv_symm_inr
        (fun k ↦ isClosedEmbedding_filtrationDiagram_map isClosed_singleton (homOfLE k.le_succ))
        (coe_map_filtrationCellInclusion hx₀) (isColimitFiltrationCocone X x₀) ⟨k, j⟩) x
    let z : filtration X x₀ (k + 1) := RelCWComplex.map n j.1 x
    have hxc' : z.1 = w := hmap.symm.trans hxc
    let b := complRangeFiltrationCellInclusionEquiv hx₀ k n j
    have hj_val : j.1 = (filtrationStageSuccCellEquiv hx₀ k n).symm (.inr b) :=
      congrArg Subtype.val
        ((complRangeFiltrationCellInclusionEquiv hx₀ k n).symm_apply_apply j).symm
    have hz_open : z ∈
        (letI := relCWComplexFiltrationSucc hx₀ k;
          openCell (C := (univ : Set (filtration X x₀ (k + 1)))) n b) := by
      rw [← openCell_filtrationStageSuccCellEquiv_symm_inr hx₀ b]
      change z ∈
        RelCWComplex.map n ((filtrationStageSuccCellEquiv hx₀ k n).symm (.inr b)) '' ball 0 1
      rw [← hj_val]
      exact mem_image_of_mem _ hx_ball
    have hz_base : z ∈
        range (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) k.le_succ)) :=
      ⟨⟨w, filtration_monotone hrk hwr⟩, Subtype.ext hxc'.symm⟩
    exact (letI := relCWComplexFiltrationSucc hx₀ k; disjointBase n b).notMem_of_mem_left
      hz_open hz_base

/-- **Each stage `J_r X` is a closed subcomplex of `J X`**, consisting of the cells of word length
at most `r`. -/
def filtrationSubcomplex (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    letI := cwComplexUniv hx₀
    CWComplex.Subcomplex (univ : Set (JamesReducedProduct X x₀)) :=
  letI := cwComplexUniv hx₀
  { carrier := filtration X x₀ r
    I n := {c | (cellEquiv hx₀ n c).1 ≤ r}
    closed' := isClosed_filtration isClosed_singleton r
    union' := by
      rw [empty_union]
      refine Subset.antisymm (iUnion₂_subset fun n ⟨c, hc⟩ ↦
        (openCell_subset_filtration_cellEquiv_fst hx₀ c).trans (filtration_monotone hc))
        fun w hw ↦ ?_
      have hw_univ : w ∈ ⋃ (n : ℕ) (c : cell (univ : Set (JamesReducedProduct X x₀)) n),
          openCell n c := by
        rw [CWComplex.iUnion_openCell_eq_complex]
        exact mem_univ w
      obtain ⟨n, c, hwc⟩ := mem_iUnion₂.1 hw_univ
      exact mem_iUnion₂.2
        ⟨n, ⟨c, cellEquiv_fst_le_of_mem_openCell_of_mem_filtration hx₀ hwc hw⟩, hwc⟩ }

@[simp]
theorem coe_filtrationSubcomplex (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    (letI := cwComplexUniv hx₀;
      (filtrationSubcomplex hx₀ r : Set (JamesReducedProduct X x₀))) = filtration X x₀ r :=
  (rfl)

@[simp]
theorem mem_filtrationSubcomplex_I_iff (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {r n : ℕ}
    (c : letI := cwComplexUniv hx₀; cell (univ : Set (JamesReducedProduct X x₀)) n) :
    c ∈ (letI := cwComplexUniv hx₀; (filtrationSubcomplex hx₀ r).I n) ↔
      (cellEquiv hx₀ n c).1 ≤ r :=
  Iff.rfl

/-- The subcomplexes `J_r X` of `J X` are monotone in `r`. -/
theorem filtrationSubcomplex_monotone (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    letI := cwComplexUniv hx₀
    Monotone (filtrationSubcomplex hx₀) :=
  fun _ _ h ↦ filtration_monotone h

/-- **Each `J_r X` is a closed subcomplex of `J_s X`** (`r ≤ s`). In particular, for `s = r + 1`,
`J_r X` is a subcomplex of `J_(r + 1) X`, making `(J_(r + 1) X, J_r X)` a CW pair via
`Topology.RelCWComplex.Subcomplex.relCWComplex`. -/
def filtrationSubcomplexOfLE (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {r s : ℕ}
    (h : r ≤ s) :
    haveI := t2Space hx₀
    letI := cwComplexUniv hx₀
    CWComplex.Subcomplex (filtrationSubcomplex hx₀ s : Set (JamesReducedProduct X x₀)) :=
  haveI := t2Space hx₀
  letI := cwComplexUniv hx₀
  Subcomplex.ofLE (filtrationSubcomplex_monotone hx₀ h)

@[simp]
theorem coe_filtrationSubcomplexOfLE (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) {r s : ℕ}
    (h : r ≤ s) :
    (haveI := t2Space hx₀;
      letI := cwComplexUniv hx₀;
      (filtrationSubcomplexOfLE hx₀ h : Set (JamesReducedProduct X x₀))) = filtration X x₀ r := by
  have := t2Space hx₀
  let _ := cwComplexUniv hx₀
  exact Subcomplex.coe_ofLE (filtrationSubcomplex_monotone hx₀ h)

/-- **Each inclusion `J_r X ⊆ J_(r + 1) X` has the homotopy extension property** (it is a closed
cofibration). -/
theorem hasHomotopyExtensionProperty_filtration
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    HasHomotopyExtensionProperty
      ((Subtype.val : filtration X x₀ (r + 1) → JamesReducedProduct X x₀) ⁻¹'
        filtration X x₀ r) := by
  have := t2Space hx₀
  let _ := cwComplexUniv hx₀
  let _ := (filtrationSubcomplexOfLE hx₀ r.le_succ).relCWComplex
  have h := hasHomotopyExtensionProperty_base
    (C := (filtrationSubcomplex hx₀ (r + 1) : Set (JamesReducedProduct X x₀)))
  rw [coe_filtrationSubcomplexOfLE] at h
  exact h

end ColimitAndSubcomplexes

section Finiteness

variable {X : Type u} {x₀ : X} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- When `X` is a finite CW complex pointed at a `0`-cell, every stage `J_r X` of the word-length
filtration is a finite CW complex. -/
theorem finite_filtration [CWComplex.Finite (univ : Set X)]
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    haveI := t2Space hx₀
    letI := cwComplexUniv hx₀
    CWComplex.Finite (filtrationSubcomplex hx₀ r : Set (JamesReducedProduct X x₀)) := by
  have := t2Space hx₀
  let _ := cwComplexUniv hx₀
  have : _root_.Finite (Σ m, cell (univ : Set X) m) :=
    CWComplex.finite_cells_of_finite (C := (univ : Set X))
  refine CWComplex.finite_of_finite_cells <| Finite.of_surjective
    (f := fun p : Σ s : Fin (r + 1), Fin s.1 → NonBasepointCell hx₀ ↦
      ⟨∑ i, (p.2 i).1.1,
        ⟨(cellEquiv hx₀ _).symm ⟨p.1.1, ⟨p.2, rfl⟩⟩, by
          simp [Nat.le_of_lt_succ p.1.2]⟩⟩) ?_
  rintro ⟨n, c, hc⟩
  rcases hce : cellEquiv hx₀ n c with ⟨s, w, hw⟩
  subst hw
  have hsr : s < r + 1 := Nat.lt_succ_of_le (by simpa [hce] using hc)
  refine ⟨⟨⟨s, hsr⟩, w⟩, Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))⟩
  dsimp only
  rw [← hce, Equiv.symm_apply_apply]

private lemma finite_nonBasepointCellTuple [CWComplex.FiniteType (univ : Set X)]
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (s n : ℕ) :
    _root_.Finite {w : Fin s → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n} := by
  have (m : ℕ) : _root_.Finite (cell (univ : Set X) m) := CWComplex.FiniteType.finite_cell m
  refine Finite.of_injective
    (f := fun (w : {w : Fin s → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n}) (i : Fin s) ↦
      (⟨⟨(w.1 i).1.1, Nat.lt_succ_of_le
          ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans_eq w.2)⟩,
        (w.1 i).1.2⟩ : Σ m : Fin (n + 1), cell (univ : Set X) m.1)) ?_
  intro w₁ w₂ h
  refine Subtype.ext (funext fun i ↦ Subtype.ext ?_)
  obtain ⟨hm, hc⟩ := Sigma.mk.inj_iff.1 (congrFun h i)
  exact Sigma.ext (Fin.ext_iff.1 hm) hc

/-- When `X` is a CW complex of finite type pointed at a `0`-cell, every stage `J_r X` is of finite
type. -/
theorem finiteType_filtration [CWComplex.FiniteType (univ : Set X)]
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) (r : ℕ) :
    haveI := t2Space hx₀
    letI := cwComplexUniv hx₀
    CWComplex.FiniteType (filtrationSubcomplex hx₀ r : Set (JamesReducedProduct X x₀)) := by
  have := t2Space hx₀
  let _ := cwComplexUniv hx₀
  refine ⟨fun n ↦ ?_⟩
  have (s : Fin (r + 1)) :
      _root_.Finite {w : Fin s.1 → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n} :=
    finite_nonBasepointCellTuple hx₀ s.1 n
  refine Finite.of_injective
    (f := fun (c : (filtrationSubcomplex hx₀ r).I n) ↦
      (⟨⟨(cellEquiv hx₀ n c.1).1, Nat.lt_succ_of_le c.2⟩, (cellEquiv hx₀ n c.1).2⟩ :
        Σ s : Fin (r + 1), {w : Fin s.1 → NonBasepointCell hx₀ // ∑ i, (w i).1.1 = n})) ?_
  intro c₁ c₂ h
  refine Subtype.ext ((cellEquiv hx₀ n).injective ?_)
  obtain ⟨hs, hw⟩ := Sigma.mk.inj_iff.1 h
  exact Sigma.ext (Fin.ext_iff.1 hs) hw

/-- **When `X` is of finite type with a single `0`-cell, `J X` is a CW complex of finite type**
(Hatcher, Section 3.C): every non-basepoint cell has positive dimension, so only words of length at
most `n` contribute `n`-cells. -/
theorem finiteType_cwComplexUniv [CWComplex.FiniteType (univ : Set X)]
    [Subsingleton (cell (univ : Set X) 0)]
    (hx₀ : x₀ ∈ CWComplex.skeleton (univ : Set X) 0) :
    letI := cwComplexUniv hx₀
    CWComplex.FiniteType (univ : Set (JamesReducedProduct X x₀)) := by
  have := t2Space hx₀
  let _ := cwComplexUniv hx₀
  refine ⟨fun n ↦ ?_⟩
  have := finiteType_filtration hx₀ n
  have : _root_.Finite ((filtrationSubcomplex hx₀ n).I n) := by
    rw [← CWComplex.Subcomplex.cell_def]
    exact CWComplex.FiniteType.finite_cell n
  refine Finite.of_injective
    (f := fun c : cell (univ : Set (JamesReducedProduct X x₀)) n ↦
      (⟨c, by
        rcases h : cellEquiv hx₀ n c with ⟨r, w, hw⟩
        have hpos (i : Fin r) : 1 ≤ (w i).1.1 := by
          rcases w i with ⟨⟨m, cm⟩, hne⟩
          by_contra! h0
          obtain rfl : m = 0 := Nat.lt_one_iff.1 h0
          exact hne (Sigma.ext rfl (heq_of_eq (Subsingleton.elim cm (basepointCell hx₀))))
        calc
          (cellEquiv hx₀ n c).1 = r := by rw [h]
          _ = ∑ _ : Fin r, 1 := by simp
          _ ≤ ∑ i : Fin r, (w i).1.1 := Finset.sum_le_sum fun i _ ↦ hpos i
          _ = n := hw⟩ :
        (filtrationSubcomplex hx₀ n).I n))
    fun _ _ h ↦ congrArg Subtype.val h

end Finiteness

end TauCeti.JamesReducedProduct
