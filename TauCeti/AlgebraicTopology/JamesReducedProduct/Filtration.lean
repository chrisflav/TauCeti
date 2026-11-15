/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import TauCeti.AlgebraicTopology.JamesReducedProduct.Basic
public import TauCeti.Topology.Category.TopCat.Limits.Basic
public import TauCeti.Topology.Convenient.CompactlyGenerated
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topology of the word-length filtration of the James reduced product

For a pointed space `(X, x₀)`, the word-length filtration
`J₀ X ⊆ J₁ X ⊆ ⋯ ⊆ J X` (`TauCeti.JamesReducedProduct.filtration`) exhausts the James reduced
product by the images of the powers `Xʳ`. This file establishes its colimit, quotient, and pushout
descriptions:

* **Coherence and sequential colimit** (for any topological space `X`, with no separation
  assumption): `J X` carries the topology coherent with the stages `J_r X`
  (`TauCeti.JamesReducedProduct.isCoherentWith_filtration`), so `J X` is the colimit in `TopCat`
  of the diagram `filtrationDiagram X x₀` of stages and inclusions
  (`TauCeti.JamesReducedProduct.isColimitFiltrationCocone`).
* **First two stages**: `J₀ X` is a one-point discrete space (`Unique (filtration X x₀ 0)`), and
  when `X` is compactly generated, `letter` restricts to a homeomorphism `X ≃ₜ J₁ X`
  (`TauCeti.JamesReducedProduct.letterFiltrationOneHomeomorph`).
* **Subspace and quotient topology** (when `{x₀}` is closed in `X`): a subset of `J_r X` is closed
  in `J X` as soon as its preimage under every continuous family `S → Xʳ` from a compact Hausdorff
  space `S` is closed (`TauCeti.JamesReducedProduct.isClosed_of_subset_filtration`), because any
  word of length `n ≥ r` reducing into `J_r X` has at least `n - r` basepoint coordinates and so
  factors through one of the finitely many order-preserving inclusions `Fin r → Fin n` on a closed
  coord-slice of `Xⁿ`. Consequently:
  * the reduction map `k(Xʳ) → J_r X` from the compactly generated power is a quotient map
    (`TauCeti.JamesReducedProduct.isQuotientMap_mkFiltration`);
  * every inclusion `J_r X ↪ J_s X` (`r ≤ s`) is a closed embedding
    (`TauCeti.JamesReducedProduct.isClosedEmbedding_filtrationInclusion`);
  * `J_(r + 1) X` is the pushout in `TopCat` of the fat wedge
    `{v ∈ k(X^(r + 1)) | ∃ i, v i = x₀} ↪ k(X^(r + 1))` along word reduction onto `J_r X`
    (`TauCeti.JamesReducedProduct.isPushout_filtration_succ`).

The closed-basepoint assumption is necessary for the quotient and closed-embedding statements: if
`X` is the Sierpiński space `{0, 1}` with `{1}` open and `x₀ = 1`, then `{letter 0} ⊆ J₁ X` has
closed preimage `{0}` in `X¹`, while its preimage `{(0, 1), (1, 0)}` in `X²` is not closed because
`(0, 0)` lies in its closure with `mk (0, 0) = (letter 0)² ∉ J₁ X`.

## Main definitions

* `TauCeti.JamesReducedProduct.filtrationDiagram`, `TauCeti.JamesReducedProduct.filtrationCocone`:
  the diagram `J₀ X → J₁ X → ⋯` in `TopCat` and its colimit cocone with vertex `J X`.
* `TauCeti.JamesReducedProduct.letterFiltrationOneHomeomorph`: `X ≃ₜ J₁ X` for compactly generated
  `X`.
* `TauCeti.JamesReducedProduct.mkFiltration`: the continuous surjection `k(Xʳ) → J_r X`.
* `TauCeti.JamesReducedProduct.fatWedgeSet`, `TauCeti.JamesReducedProduct.mkFatWedge`: the fat
  wedge inside `k(X^(r + 1))` and its reduction map to `J_r X`.

## Main results

* `TauCeti.JamesReducedProduct.isCoherentWith_filtration`,
  `TauCeti.JamesReducedProduct.isColimitFiltrationCocone`: `J X` is coherent with and is the
  colimit in `TopCat` of the filtration `J_r X`.
* `TauCeti.JamesReducedProduct.isClosed_of_subset_filtration`: single-stage closedness criterion
  for subsets of `J_r X` when `{x₀}` is closed.
* `TauCeti.JamesReducedProduct.isQuotientMap_mkFiltration`: `k(Xʳ) → J_r X` is a quotient map when
  `{x₀}` is closed.
* `TauCeti.JamesReducedProduct.isClosedEmbedding_filtrationInclusion`: `J_r X ↪ J_s X` is a closed
  embedding when `{x₀}` is closed.
* `TauCeti.JamesReducedProduct.isPushout_filtration_succ`: `J_(r + 1) X` is the pushout of
  `fatWedgeSet ↪ k(X^(r + 1))` along `mkFatWedge` when `{x₀}` is closed.

## References

* I. M. James, *Reduced product spaces*, Ann. of Math. (2) 62 (1955), 170–197.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology

universe u

namespace TauCeti.JamesReducedProduct

section Combinatorics

variable {X : Type u} {x₀ : X}

/-- The zeroth stage `J₀ X = {1}` has a unique element. -/
instance : Unique (filtration X x₀ 0) where
  default := ⟨1, one_mem_filtration 0⟩
  uniq w := Subtype.ext (by simpa [filtration_zero] using w.2)

@[simp]
theorem coe_default_filtration_zero :
    ((default : filtration X x₀ 0) : JamesReducedProduct X x₀) = 1 :=
  (rfl)

/-- Deleting coordinates outside the image of a strictly monotone map `σ : Fin r → Fin n`, when all
deleted coordinates equal the basepoint, preserves the reduced word. -/
theorem mk_comp_strictMono_of_eq_basepoint {r n : ℕ} {σ : Fin r → Fin n} (hσ : StrictMono σ)
    {v : Fin n → X} (hv : ∀ i ∉ range σ, v i = x₀) :
    (mk (v ∘ σ) : JamesReducedProduct X x₀) = mk v := by
  induction n generalizing r with
  | zero =>
    obtain rfl : r = 0 := by
      cases r with
      | zero => rfl
      | succ r => exact Fin.elim0 (σ 0)
    simp
  | succ n ih =>
    conv_rhs => rw [← Fin.cons_self_tail v, mk_cons]
    by_cases h0 : (0 : Fin (n + 1)) ∈ range σ
    · obtain ⟨i₀, hi₀⟩ := h0
      cases r with
      | zero => exact Fin.elim0 i₀
      | succ r =>
        obtain rfl : i₀ = 0 := by
          by_contra hne
          exact (hσ (Fin.pos_iff_ne_zero.2 hne)).not_ge (hi₀ ▸ Fin.zero_le _)
        have hpos (j : Fin r) : σ j.succ ≠ 0 :=
          (hi₀ ▸ hσ (Fin.succ_pos j)).ne'
        let τ : Fin r → Fin n := fun j ↦ (σ j.succ).pred (hpos j)
        have hτ : StrictMono τ := fun j₁ j₂ hj ↦
          Fin.pred_lt_pred_iff.2 (hσ (Fin.strictMono_succ hj))
        have hvτ (k : Fin n) (hk : k ∉ range τ) : Fin.tail v k = x₀ := by
          refine hv k.succ fun ⟨m, hm⟩ ↦ hk ?_
          cases m using Fin.cases with
          | zero => exact absurd (hi₀.symm.trans hm) (Fin.succ_ne_zero k).symm
          | succ j => exact ⟨j, by simp [τ, hm]⟩
        have hcons : v ∘ σ = Fin.cons (v 0) (Fin.tail v ∘ τ) := by
          ext m
          cases m using Fin.cases with
          | zero => simp [hi₀]
          | succ j => simp [τ, Fin.tail]
        rw [hcons, mk_cons, ih hτ hvτ]
    · have hv0 : v 0 = x₀ := hv 0 h0
      have hne (j : Fin r) : σ j ≠ 0 := fun h ↦ h0 ⟨j, h⟩
      let τ : Fin r → Fin n := fun j ↦ (σ j).pred (hne j)
      have hτ : StrictMono τ := fun j₁ j₂ hj ↦ Fin.pred_lt_pred_iff.2 (hσ hj)
      have hvτ (k : Fin n) (hk : k ∉ range τ) : Fin.tail v k = x₀ :=
        hv k.succ fun ⟨j, hj⟩ ↦ hk ⟨j, by simp [τ, hj]⟩
      have hcomp : v ∘ σ = Fin.tail v ∘ τ := funext fun j ↦ by simp [τ, Fin.tail]
      rw [hv0, letter_basepoint, one_mul, hcomp, ih hτ hvτ]

/-- Any word `v : Fin n → X` of length `n ≥ r` whose reduced word lies in `J_r X` restricts along
some strictly monotone map `σ : Fin r → Fin n` outside whose image all coordinates equal `x₀`. -/
theorem exists_strictMono_mk_comp_eq {r n : ℕ} (hrn : r ≤ n) {v : Fin n → X}
    (hv : (mk v : JamesReducedProduct X x₀) ∈ filtration X x₀ r) :
    ∃ σ : Fin r → Fin n,
      StrictMono σ ∧ (∀ i ∉ range σ, v i = x₀) ∧
        (mk (v ∘ σ) : JamesReducedProduct X x₀) = mk v := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun i ↦ v i ≠ x₀
  have hS : S.card ≤ r := by simpa only [mem_filtration_iff, length_mk, S] using hv
  have hSc : r - S.card ≤ Sᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨W, hWSc, hWcard⟩ := Finset.exists_subset_card_eq hSc
  let T : Finset (Fin n) := S ∪ W
  have hTcard : T.card = r := by
    rw [Finset.card_union_of_disjoint (disjoint_compl_right.mono_right hWSc), hWcard]
    omega
  let σ : Fin r → Fin n := T.orderEmbOfFin hTcard
  have hσ : StrictMono σ := (T.orderEmbOfFin hTcard).strictMono
  have hvσ (i : Fin n) (hi : i ∉ range σ) : v i = x₀ := by
    rw [Finset.range_orderEmbOfFin] at hi
    have hiS : i ∉ S := fun h ↦ hi (Finset.mem_coe.2 (Finset.mem_union_left _ h))
    simpa [S] using hiS
  exact ⟨σ, hσ, hvσ, mk_comp_strictMono_of_eq_basepoint hσ hvσ⟩

/-- When no coordinate of `u : Fin r → X` is the basepoint, its reduced word has underlying list
`u 0, …, u (r - 1)`. -/
theorem toList_freeMonoidEquiv_mk_of_ne_basepoint {r : ℕ} {u : Fin r → X} (hu : ∀ i, u i ≠ x₀) :
    (freeMonoidEquiv X x₀ (mk u)).toList = List.ofFn fun i ↦ ⟨u i, hu i⟩ := by
  induction r with
  | zero => simp
  | succ r ih =>
    conv_lhs => rw [← Fin.cons_self_tail u]
    rw [mk_cons, map_mul, FreeMonoid.toList_mul, letter_of_ne (hu 0), MulEquiv.apply_symm_apply,
      FreeMonoid.toList_of, ih (u := Fin.tail u) (fun i ↦ hu i.succ), List.singleton_append,
      List.ofFn_succ]
    rfl

/-- Word reduction is injective on tuples `Fin r → X` having no coordinate equal to the
basepoint. -/
theorem eq_of_mk_eq_mk_of_ne_basepoint {r : ℕ} {u v : Fin r → X} (hu : ∀ i, u i ≠ x₀)
    (hv : ∀ i, v i ≠ x₀) (h : (mk u : JamesReducedProduct X x₀) = mk v) : u = v := by
  have hlist := congrArg (fun w ↦ (freeMonoidEquiv X x₀ w).toList) h
  rw [toList_freeMonoidEquiv_mk_of_ne_basepoint hu,
    toList_freeMonoidEquiv_mk_of_ne_basepoint hv, List.ofFn_inj] at hlist
  exact funext fun i ↦ congrArg Subtype.val (congrFun hlist i)

/-- A word `u : Fin (r + 1) → X` reduces into `J_r X` if and only if at least one of its
coordinates is the basepoint. -/
theorem mk_mem_filtration_iff_exists_eq_basepoint {r : ℕ} {u : Fin (r + 1) → X} :
    (mk u : JamesReducedProduct X x₀) ∈ filtration X x₀ r ↔ ∃ i, u i = x₀ := by
  classical
  rw [mem_filtration_iff, length_mk, Nat.le_iff_lt_add_one]
  refine ⟨fun hlt ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
  · by_contra! hall
    have heq : (Finset.univ.filter fun i ↦ u i ≠ x₀) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ ↦ hall i
    exact hlt.ne ((congrArg Finset.card heq).trans (Finset.card_fin (r + 1)))
  · refine (Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h ↦ ?_⟩).trans_eq
      (Finset.card_fin (r + 1))
    exact (Finset.mem_filter.1 (h (Finset.mem_univ i))).2 hi

end Combinatorics

section Topology

variable {X : Type u} {x₀ : X} [TopologicalSpace X]

/-- The James reduced product carries the topology coherent with the stages `J_r X` of its
word-length filtration. -/
theorem isCoherentWith_filtration : Topology.IsCoherentWith (range (filtration X x₀)) := by
  refine .of_isClosed fun A hA ↦ isClosed_iff.2 fun n S g ↦ ?_
  let h : C(S, filtration X x₀ n) :=
    ⟨fun s ↦ ⟨mk (g s), mk_mem_filtration (g s)⟩, (continuous_mk g.continuous).subtype_mk _⟩
  exact (hA _ ⟨n, rfl⟩).preimage h.continuous

variable (X x₀) in
/-- The sequential diagram `J₀ X → J₁ X → ⋯` of the word-length filtration in `TopCat`. -/
abbrev filtrationDiagram : ℕ ⥤ TopCat.{u} :=
  TopCat.subspaceDiagram (filtration_monotone (X := X) (x₀ := x₀))

variable (X x₀) in
/-- The cocone with vertex `J X` over `filtrationDiagram X x₀` formed by the subspace
inclusions. -/
abbrev filtrationCocone : Cocone (filtrationDiagram X x₀) :=
  TopCat.subspaceCocone (filtration_monotone (X := X) (x₀ := x₀))

variable (X x₀) in
/-- **The James reduced product is the colimit of its word-length filtration** in `TopCat`, with no
separation hypothesis on `X`. -/
def isColimitFiltrationCocone : IsColimit (filtrationCocone X x₀) :=
  TopCat.isColimitOfIsCoherentWith (filtration_monotone (X := X) (x₀ := x₀)) iUnion_filtration
    isCoherentWith_filtration

/-- For a compactly generated space `X`, `letter` restricts to a homeomorphism `X ≃ₜ J₁ X`. -/
def letterFiltrationOneHomeomorph [CompactlyGeneratedSpace X] :
    X ≃ₜ filtration X x₀ 1 :=
  isEmbedding_letter.toHomeomorph.trans (Homeomorph.setCongr filtration_one.symm)

@[simp]
theorem coe_letterFiltrationOneHomeomorph_apply [CompactlyGeneratedSpace X] (x : X) :
    (letterFiltrationOneHomeomorph (x₀ := x₀) x : JamesReducedProduct X x₀) = letter x :=
  IsEmbedding.toHomeomorph_apply_coe isEmbedding_letter x

/-- The continuous surjection `k(Xʳ) → J_r X` sending a tuple in the compactly generated `r`-th
power of `X` to its reduced word. -/
def mkFiltration (r : ℕ) :
    C(WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X), filtration X x₀ r) :=
  haveI : UCompactlyGeneratedSpace.{u}
      (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X)) :=
    (isGeneratedBy_compHaus_iff _).1 inferInstance
  ⟨fun y ↦ ⟨mk (WithGeneratedByTopology.equiv y), mk_mem_filtration _⟩,
    (continuous_mk WithGeneratedByTopology.continuous_equiv).subtype_mk _⟩

@[simp]
theorem coe_mkFiltration_apply (r : ℕ)
    (y : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X)) :
    (mkFiltration (X := X) (x₀ := x₀) r y : JamesReducedProduct X x₀) =
      mk (WithGeneratedByTopology.equiv y) :=
  (rfl)

theorem surjective_mkFiltration (r : ℕ) :
    Function.Surjective (mkFiltration (X := X) (x₀ := x₀) r) := fun ⟨w, hw⟩ ↦ by
  obtain ⟨v, rfl⟩ := exists_mk_eq_of_length_le (mem_filtration_iff.1 hw)
  exact ⟨WithGeneratedByTopology.equiv.symm v, Subtype.ext (by simp)⟩

/-- The **fat wedge** inside `k(Xʳ)`: the tuples having at least one coordinate equal to the
basepoint `x₀`. -/
def fatWedgeSet (X : Type u) (x₀ : X) [TopologicalSpace X] (r : ℕ) :
    Set (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X)) :=
  {y | ∃ i, WithGeneratedByTopology.equiv y i = x₀}

@[simp]
theorem mem_fatWedgeSet_iff {r : ℕ}
    {y : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin r → X)} :
    y ∈ fatWedgeSet X x₀ r ↔ ∃ i, WithGeneratedByTopology.equiv y i = x₀ :=
  Iff.rfl

/-- On the fat wedge inside `k(X^(r + 1))`, word reduction lands in `J_r X`. -/
def mkFatWedge (r : ℕ) :
    C(fatWedgeSet X x₀ (r + 1), filtration X x₀ r) where
  toFun y := ⟨mk (WithGeneratedByTopology.equiv y.1),
    mk_mem_filtration_iff_exists_eq_basepoint.2 y.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp (mkFiltration (r + 1)).continuous).comp
      continuous_subtype_val

@[simp]
theorem coe_mkFatWedge_apply (r : ℕ) (y : fatWedgeSet X x₀ (r + 1)) :
    (mkFatWedge (X := X) (x₀ := x₀) r y : JamesReducedProduct X x₀) =
      mk (WithGeneratedByTopology.equiv y.1) :=
  (rfl)

/-- **Single-stage closedness criterion.** When `{x₀}` is closed in `X`, a subset `F ⊆ J_r X` is
closed in `J X` if and only if its preimage under every continuous family `S → Xʳ` parametrized by
a compact Hausdorff space `S` is closed. -/
theorem isClosed_of_subset_filtration (hx₀ : IsClosed ({x₀} : Set X)) {r : ℕ}
    {F : Set (JamesReducedProduct X x₀)} (hFr : F ⊆ filtration X x₀ r) :
    IsClosed F ↔ ∀ (S : CompHaus.{u}) (g : C(S, Fin r → X)),
      IsClosed ((fun s ↦ (mk (g s) : JamesReducedProduct X x₀)) ⁻¹' F) := by
  refine ⟨fun hF S g ↦ isClosed_iff.1 hF r S g, fun hF ↦ isClosed_iff.2 fun n S g ↦ ?_⟩
  rcases le_total n r with hnr | hrn
  · have hn : n + (r - n) = r := by omega
    let g' : C(S, Fin r → X) :=
      ⟨fun s ↦ Fin.append (g s) (fun _ : Fin (r - n) ↦ x₀) ∘ Fin.cast hn.symm,
        continuous_pi fun i ↦ (continuous_apply (Fin.cast hn.symm i)).comp
          ((Fin.continuous_append n (r - n)).comp (g.continuous.prodMk continuous_const))⟩
    have hpre : (fun s ↦ (mk (g s) : JamesReducedProduct X x₀)) ⁻¹' F =
        (fun s ↦ (mk (g' s) : JamesReducedProduct X x₀)) ⁻¹' F := by
      ext s
      simp [g', mk_comp_cast, mk_append]
    exact hpre ▸ hF S g'
  · -- When `n ≥ r`, any `g s` with `mk (g s) ∈ F ⊆ J_r X` equals `x₀` outside the range of one
    -- of the finitely many strictly monotone inclusions `σ : Fin r → Fin n`.
    let A (σ : Fin r → Fin n) : Set (Fin n → X) := {v | ∀ i ∉ range σ, v i = x₀}
    have hA (σ : Fin r → Fin n) : IsClosed (A σ) := by
      have hAeq : A σ = ⋂ (i : Fin n) (_ : i ∉ range σ), (fun v : Fin n → X ↦ v i) ⁻¹' {x₀} := by
        ext v; simp [A]
      rw [hAeq]
      exact isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ hx₀.preimage (continuous_apply i)
    let π (σ : Fin r → Fin n) : C(Fin n → X, Fin r → X) :=
      ⟨fun v ↦ v ∘ σ, continuous_pi fun j ↦ continuous_apply (σ j)⟩
    have hpre : (fun s ↦ (mk (g s) : JamesReducedProduct X x₀)) ⁻¹' F =
        ⋃ σ : {σ : Fin r → Fin n // StrictMono σ},
          g ⁻¹' A σ.1 ∩ (fun s ↦ (mk (π σ.1 (g s)) : JamesReducedProduct X x₀)) ⁻¹' F := by
      ext s
      simp only [mem_preimage, mem_iUnion, mem_inter_iff]
      refine ⟨fun hs ↦ ?_, fun ⟨σ, hsA, hsF⟩ ↦ ?_⟩
      · obtain ⟨σ, hσ, hvσ, hmk⟩ := exists_strictMono_mk_comp_eq hrn (hFr hs)
        exact ⟨⟨σ, hσ⟩, hvσ, by simpa [π, hmk] using hs⟩
      · rw [← mk_comp_strictMono_of_eq_basepoint σ.2 hsA]
        exact hsF
    rw [hpre]
    exact isClosed_iUnion_of_finite fun σ ↦
      ((hA σ.1).preimage g.continuous).inter (hF S ((π σ.1).comp g))

/-- **Word reduction `k(Xʳ) → J_r X` is a quotient map** when the basepoint `{x₀}` is closed. -/
theorem isQuotientMap_mkFiltration (hx₀ : IsClosed ({x₀} : Set X)) (r : ℕ) :
    IsQuotientMap (mkFiltration (X := X) (x₀ := x₀) r) := by
  refine isQuotientMap_iff_isClosed.2 ⟨surjective_mkFiltration r, fun U ↦ ?_⟩
  refine ⟨fun hU ↦ hU.preimage (mkFiltration r).continuous, fun hU ↦ ?_⟩
  have hclosed : IsClosed ((Subtype.val : filtration X x₀ r → _) '' U) := by
    refine (isClosed_of_subset_filtration hx₀ (Subtype.coe_image_subset _ U)).2 fun S g ↦ ?_
    have hEq : (fun s ↦ (mk (g s) : JamesReducedProduct X x₀)) ⁻¹' (Subtype.val '' U) =
        g ⁻¹' (WithGeneratedByTopology.equiv.symm ⁻¹' (mkFiltration r ⁻¹' U)) := by
      ext s
      simp only [mem_preimage, mem_image]
      refine ⟨fun ⟨w, hwU, hw⟩ ↦ ?_, fun hs ↦ ⟨_, hs, by simp⟩⟩
      have hmk : mkFiltration r (WithGeneratedByTopology.equiv.symm (g s)) = w :=
        Subtype.ext (by simp [hw])
      exact hmk ▸ hwU
    rw [hEq]
    exact (WithGeneratedByTopology.isClosed_iff.1 hU) g
  rw [← preimage_image_eq U Subtype.val_injective]
  exact hclosed.preimage continuous_subtype_val

/-- When `{x₀}` is closed in `X`, every inclusion `J_r X ↪ J_s X` (`r ≤ s`) is a closed
embedding. -/
theorem isClosedEmbedding_filtrationInclusion (hx₀ : IsClosed ({x₀} : Set X)) {r s : ℕ}
    (h : r ≤ s) : IsClosedEmbedding (Set.inclusion (filtration_monotone (X := X) (x₀ := x₀) h)) :=
  ⟨IsEmbedding.inclusion _, by
    rw [range_inclusion]
    exact (isClosed_filtration hx₀ r).preimage continuous_subtype_val⟩

/-- Every bonding morphism of `filtrationDiagram X x₀` is a closed embedding when `{x₀}` is
closed. -/
theorem isClosedEmbedding_filtrationDiagram_map (hx₀ : IsClosed ({x₀} : Set X)) {r s : ℕ}
    (u : r ⟶ s) : IsClosedEmbedding ((filtrationDiagram X x₀).map u) :=
  isClosedEmbedding_filtrationInclusion hx₀ (leOfHom u)

private lemma factorsThrough_mkFiltration_of_pushoutCocone {r : ℕ}
    (s : PushoutCocone
      (TopCat.ofHom (ContinuousMap.subtypeVal (fatWedgeSet X x₀ (r + 1))))
      (TopCat.ofHom (mkFatWedge (X := X) (x₀ := x₀) r))) :
    Function.FactorsThrough s.inl.hom (mkFiltration (X := X) (x₀ := x₀) (r + 1)) := by
  intro (y₁ : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X))
    (y₂ : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X)) hy
  have hmk : (mk (WithGeneratedByTopology.equiv y₁) : JamesReducedProduct X x₀) =
      mk (WithGeneratedByTopology.equiv y₂) := congrArg Subtype.val hy
  by_cases hmem : (mk (WithGeneratedByTopology.equiv y₁) : JamesReducedProduct X x₀) ∈
      filtration X x₀ r
  · have hy₁ : y₁ ∈ fatWedgeSet X x₀ (r + 1) :=
      mk_mem_filtration_iff_exists_eq_basepoint.1 hmem
    have hy₂ : y₂ ∈ fatWedgeSet X x₀ (r + 1) :=
      mk_mem_filtration_iff_exists_eq_basepoint.1 (hmk ▸ hmem)
    have hfw : mkFatWedge r ⟨y₁, hy₁⟩ = mkFatWedge r ⟨y₂, hy₂⟩ := Subtype.ext hmk
    exact (ConcreteCategory.congr_hom s.condition ⟨y₁, hy₁⟩).trans <|
      (congrArg s.inr hfw).trans (ConcreteCategory.congr_hom s.condition ⟨y₂, hy₂⟩).symm
  · have hu₁ : ∀ i, WithGeneratedByTopology.equiv y₁ i ≠ x₀ :=
      fun i hi ↦ hmem (mk_mem_filtration_iff_exists_eq_basepoint.2 ⟨i, hi⟩)
    have hu₂ : ∀ i, WithGeneratedByTopology.equiv y₂ i ≠ x₀ :=
      fun i hi ↦ hmem (hmk.symm ▸ mk_mem_filtration_iff_exists_eq_basepoint.2 ⟨i, hi⟩)
    have heq := WithGeneratedByTopology.equiv.injective
      (eq_of_mk_eq_mk_of_ne_basepoint hu₁ hu₂ hmk)
    exact congrArg s.inl heq

/-- **`J_(r + 1) X` as an adjunction space over `J_r X`** (James 1955; Hatcher, Section 3.C): when
`{x₀}` is closed in `X`, `J_(r + 1) X` is the pushout in `TopCat` of the inclusion of the fat wedge
into `k(X^(r + 1))` along word reduction `mkFatWedge r : fatWedgeSet X x₀ (r + 1) → J_r X`. -/
theorem isPushout_filtration_succ (hx₀ : IsClosed ({x₀} : Set X)) (r : ℕ) :
    IsPushout
      (TopCat.ofHom (ContinuousMap.subtypeVal (fatWedgeSet X x₀ (r + 1))))
      (TopCat.ofHom (mkFatWedge (X := X) (x₀ := x₀) r))
      (TopCat.ofHom (mkFiltration (X := X) (x₀ := x₀) (r + 1)))
      ((filtrationDiagram X x₀).map (homOfLE r.le_succ)) where
  w := by
    ext y
    rfl
  isColimit' := ⟨PushoutCocone.isColimitAux' _ fun s ↦ by
    have hq := isQuotientMap_mkFiltration (X := X) (x₀ := x₀) hx₀ (r + 1)
    have hfib := factorsThrough_mkFiltration_of_pushoutCocone s
    let d : TopCat.of (filtration X x₀ (r + 1)) ⟶ s.pt := TopCat.ofHom (hq.lift s.inl.hom hfib)
    refine ⟨d, ?_, ?_, fun hml _ ↦ ?_⟩
    · ext y
      exact DFunLike.congr_fun (hq.lift_comp s.inl.hom hfib) y
    · ext ⟨w, hw⟩
      obtain ⟨v, rfl⟩ := exists_mk_eq_of_length_le (mem_filtration_iff.1 hw)
      let y : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (Fin (r + 1) → X) :=
        WithGeneratedByTopology.equiv.symm (Fin.cons x₀ v)
      have hy : y ∈ fatWedgeSet X x₀ (r + 1) := ⟨0, by simp [y]⟩
      have hmk_y : mkFiltration (r + 1) y = ⟨mk v, filtration_monotone r.le_succ hw⟩ :=
        Subtype.ext (by simp [y])
      have hfw_y : mkFatWedge r ⟨y, hy⟩ = ⟨mk v, hw⟩ :=
        Subtype.ext (by simp [y])
      calc
        d (((filtrationDiagram X x₀).map (homOfLE r.le_succ)) ⟨mk v, hw⟩)
            = d (mkFiltration (r + 1) y) := congrArg d hmk_y.symm
        _ = s.inl y := DFunLike.congr_fun (hq.lift_comp s.inl.hom hfib) y
        _ = s.inr (mkFatWedge r ⟨y, hy⟩) := ConcreteCategory.congr_hom s.condition ⟨y, hy⟩
        _ = s.inr ⟨mk v, hw⟩ := congrArg s.inr hfw_y
    · ext z
      obtain ⟨y, rfl⟩ := surjective_mkFiltration (r + 1) z
      exact (ConcreteCategory.congr_hom hml y).trans
        (DFunLike.congr_fun (hq.lift_comp s.inl.hom hfib) y).symm⟩

end Topology

end TauCeti.JamesReducedProduct
