/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.LinearAlgebra.TensorCoalgebra.Tree

/-!
# Planar-tree formulas for homological transfer of A-infinity algebras

Let `𝒜` be an `A∞` algebra on `A`, and let `c = (i, p, h)` be a homogeneous special contraction of
`(A, m₁)` onto `(H, d_H)`. The bar-coalgebra perturbation construction (`AInfinityAlgebra.transfer`
and `AInfinityAlgebra.transferInclusion`) produces a transferred `A∞` structure on `H` together with
an extending `A∞` quasi-isomorphism `H ⇝ A`.

This file identifies every component of `transferInclusion` and every higher operation of `transfer`
with the finite Kontsevich--Soibelman and Merkulov sum over reduced planar trees
(`ReducedPlanarTree.Arity n`):

* Each leaf is decorated by the inclusion `c.incl`, each internal vertex of valence `k + 2` by the
  higher operation `𝒜.m (k + 2)` (the unary differential `m₁` never labels an internal vertex), and
  each internal edge by `-c.homotopy`.
* Placing `-c.homotopy` at the root (for `n ≥ 2`, and `c.incl` on the single leaf) defines
  `transferInclusionTree`, whose sum over `ReducedPlanarTree.Arity n` equals
  `(𝒜.transferInclusion c hh hincl hproj).component n` for every `n`.
* Placing `c.proj` at the root defines `transferTree`, whose sum over `ReducedPlanarTree.Arity n`
  equals `(𝒜.transfer c hh hincl hproj).m n` for every `n ≠ 1` (and for all `n` when `d_H = 0`).

Rather than expanding the geometric perturbation series by hand and reassociating tensor-trick
homotopies, the proof uses the coalgebraic fixed-point characterization
`ReducedTensorWords.eq_treeBranchTaylor_iff`: the identity `(1 + δ K) X = δ` shows that
`δ ∘ barMap(transferInclusion) = X ∘ map(i)`, so projecting to single letters turns
`barMap(transferInclusion) = map(i) - K X map(i)` into the fixed-point equation
`f = i ∘ letter + (-h) ∘ (higherTaylor ∘ coalgHom f)`.

When all operations `𝒜.m k` for `k ≥ 3` vanish (in particular when `𝒜` comes from a nonunital DG
algebra), every non-binary tree summand vanishes and the formulas reduce to sums over binary planar
trees (`ReducedPlanarTree.IsBinary`).

## Main definitions

* `TauCeti.AInfinityAlgebra.suspendedTransferInclusionTree`,
  `TauCeti.AInfinityAlgebra.suspendedTransferTree`: the suspended multilinear tree evaluations.
* `TauCeti.AInfinityAlgebra.transferInclusionTree`: the unsuspended multilinear component of the
  extending morphism contributed by a reduced planar tree.
* `TauCeti.AInfinityAlgebra.transferTree`: the unsuspended multilinear operation of the transferred
  `A∞` structure contributed by a reduced planar tree.

## Main results

* `TauCeti.AInfinityAlgebra.taylor_transferInclusion_eq_treeBranchTaylor` and
  `TauCeti.AInfinityAlgebra.taylor_transfer_eq_add_comp_treeVertexTaylor`: Taylor-level planar-tree
  identities for `transferInclusion` and `transfer`.
* `TauCeti.AInfinityAlgebra.component_transferInclusion_eq_sum_arity`:
  `(𝒜.transferInclusion c hh hincl hproj).component n` is the sum of `transferInclusionTree` over
  `ReducedPlanarTree.Arity n`.
* `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_arity`: for `n ≠ 1`,
  `(𝒜.transfer c hh hincl hproj).m n` is the sum of `transferTree` over `ReducedPlanarTree.Arity n`.
* `TauCeti.AInfinityAlgebra.component_transferInclusion_eq_sum_isBinary` and
  `TauCeti.AInfinityAlgebra.m_transfer_eq_sum_isBinary`: specialization to binary planar trees when
  `𝒜.m k = 0` for `k ≥ 3` (with DG algebra corollaries in `TauCeti.IsNonUnitalDGAlgebra`).
* `TauCeti.AInfinityAlgebra.component_three_transferInclusion`: the explicit cubic component `f₃`
  of the extending quasi-isomorphism.
* `TauCeti.AInfinityAlgebra.transferInclusionTree_naturality` and
  `TauCeti.AInfinityAlgebra.transferTree_naturality`: compatibility of individual tree summands with
  strict morphisms intertwining the contractions.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*, Section 6.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 10.3.
* S. A. Merkulov, *Strongly homotopy algebras of a Kähler manifold*, Internat. Math. Res. Notices
  (1999), no. 3, 153--164.
-/

public section

open scoped BigOperators

universe uR uA uH uB uK

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

section TreeOperations

variable {R : Type uR} {A : Type uA} {H : Type uH} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup H] [Module R H]

private theorem koszulTwist_apply_zero {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {GM : InternalGrading R M ℤ} {GN : InternalGrading R N ℤ}
    {f : M →ₗ[R] N} (hf : LinearMap.IsHomogeneous f GM.piece GN.piece 0) (q : ℤ) (x : M) :
    GN.koszulTwist q (f x) = f (GM.koszulTwist q x) := by
  simpa using hf.koszulTwist_apply q x

/-- The arity-`(k + 2)` vertex operation extracted from `𝒜.higherTaylor` is the suspended operation
`𝒜.m (k + 2)`. -/
@[simp]
theorem taylorVertex_higherTaylor (𝒜 : AInfinityAlgebra R A) (k : ℕ) :
    taylorVertex 𝒜.higherTaylor k =
      (𝒜.m (k + 2)).compLinearMap fun i ↦ 𝒜.grading.koszulTwist ((k + 2 : ℤ) - 1 - i) := by
  ext x
  rw [taylorVertex_apply, 𝒜.higherTaylor_of ⟨k + 2, Nat.succ_pos _⟩ (Nat.one_lt_succ_succ k),
    𝒜.taylor_of_tprod, MultilinearMap.compLinearMap_apply]
  dsimp only
  push_cast
  rfl

/-- Each suspended higher vertex operation has degree `1` on the shifted grading `sA`. -/
theorem isHomogeneous_taylorVertex_higherTaylor (𝒜 : AInfinityAlgebra R A) (k : ℕ) :
    MultilinearMap.IsHomogeneous (taylorVertex 𝒜.higherTaylor k)
      (fun _ ↦ (𝒜.grading.shift 1).piece) (𝒜.grading.shift 1).piece 1 := by
  rw [MultilinearMap.isHomogeneous_def]
  intro d x hx
  rw [taylorVertex_apply]
  exact 𝒜.isHomogeneous_higherTaylor.map_mem
    (mem_gradedPiece_of_tprod (𝒜.grading.shift 1) (by omega) x d hx)

variable (𝒜 : AInfinityAlgebra R A) {dH : Module.End R H}
  (c : LinearSpecialContraction 𝒜.differential dH)

/-- The suspended multilinear map `(Fin t.numLeaves → H) →ₘₗ[R] A` attached to a reduced planar
tree `t`: leaves carry `c.incl`, internal vertices of valence `k + 2` carry the suspended operation
`taylorVertex 𝒜.higherTaylor k`, internal edges carry `-c.homotopy`, and any non-leaf root carries
`-c.homotopy` (while the single leaf evaluates to `c.incl`). -/
noncomputable def suspendedTransferInclusionTree (t : ReducedPlanarTree) :
    MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) A :=
  t.evalBranch c.incl (-c.homotopy) (taylorVertex 𝒜.higherTaylor)

theorem suspendedTransferInclusionTree_def (t : ReducedPlanarTree) :
    𝒜.suspendedTransferInclusionTree c t =
      t.evalBranch c.incl (-c.homotopy) (taylorVertex 𝒜.higherTaylor) :=
  (rfl)

/-- The suspended multilinear map `(Fin t.numLeaves → H) →ₘₗ[R] H` attached to a reduced planar
tree `t`: leaves carry `c.incl`, internal vertices of valence `k + 2` carry the suspended operation
`taylorVertex 𝒜.higherTaylor k`, internal edges carry `-c.homotopy`, and the root carries `c.proj`
(vanishing on the single leaf). -/
noncomputable def suspendedTransferTree (t : ReducedPlanarTree) :
    MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) H :=
  c.proj.compMultilinearMap (t.evalVertex c.incl (-c.homotopy) (taylorVertex 𝒜.higherTaylor))

theorem suspendedTransferTree_def (t : ReducedPlanarTree) :
    𝒜.suspendedTransferTree c t =
      c.proj.compMultilinearMap (t.evalVertex c.incl (-c.homotopy) (taylorVertex 𝒜.higherTaylor)) :=
  (rfl)

/-- The unsuspended multilinear component `(Fin t.numLeaves → H) →ₘₗ[R] A` contributed by a reduced
planar tree `t` to the extending `A∞` morphism `transferInclusion`. -/
noncomputable def transferInclusionTree (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) A :=
  (𝒜.suspendedTransferInclusionTree c t).compLinearMap fun i ↦
    GH.koszulTwist ((t.numLeaves : ℤ) - 1 - i)

theorem transferInclusionTree_def (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    𝒜.transferInclusionTree c GH t =
      (𝒜.suspendedTransferInclusionTree c t).compLinearMap fun i ↦
        GH.koszulTwist ((t.numLeaves : ℤ) - 1 - i) :=
  (rfl)

/-- The unsuspended multilinear operation `(Fin t.numLeaves → H) →ₘₗ[R] H` contributed by a reduced
planar tree `t` to the transferred `A∞` structure `transfer`. -/
noncomputable def transferTree (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ H) H :=
  (𝒜.suspendedTransferTree c t).compLinearMap fun i ↦
    GH.koszulTwist ((t.numLeaves : ℤ) - 1 - i)

theorem transferTree_def (GH : InternalGrading R H ℤ) (t : ReducedPlanarTree) :
    𝒜.transferTree c GH t =
      (𝒜.suspendedTransferTree c t).compLinearMap fun i ↦
        GH.koszulTwist ((t.numLeaves : ℤ) - 1 - i) :=
  (rfl)

@[simp]
theorem transferInclusionTree_leaf (GH : InternalGrading R H ℤ) :
    𝒜.transferInclusionTree c GH .leaf =
      MultilinearMap.ofSubsingleton (RingHom.id R) H A (0 : Fin 1) c.incl := by
  ext x
  rw [transferInclusionTree, MultilinearMap.compLinearMap_apply, suspendedTransferInclusionTree,
    ReducedPlanarTree.evalBranch_leaf_apply]
  change c.incl (GH.koszulTwist ((1 : ℤ) - 1 - 0) (x (0 : Fin 1))) = c.incl (x (0 : Fin 1))
  simp [InternalGrading.koszulTwist_zero]

theorem transferInclusionTree_leaf_apply (GH : InternalGrading R H ℤ)
    (x : Fin ReducedPlanarTree.leaf.numLeaves → H) :
    𝒜.transferInclusionTree c GH .leaf x = c.incl (x (0 : Fin 1)) :=
  MultilinearMap.congr_fun (𝒜.transferInclusionTree_leaf c GH) x

@[simp]
theorem transferTree_leaf (GH : InternalGrading R H ℤ) :
    𝒜.transferTree c GH .leaf = 0 := by
  ext x
  simp [transferTree, suspendedTransferTree]

/-! ### Homogeneity of tree summands -/

section Homogeneity

variable {GH : InternalGrading R H ℤ}
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)

include hh hincl in
/-- Every suspended tree summand of `transferInclusion` has degree `0` for the shifted gradings. -/
theorem isHomogeneous_suspendedTransferInclusionTree (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.suspendedTransferInclusionTree c t)
      (fun _ ↦ (GH.shift 1).piece) (𝒜.grading.shift 1).piece 0 :=
  ReducedPlanarTree.isHomogeneous_evalBranch
    (LinearMap.isHomogeneous_shift_piece_iff.2 hincl)
    (LinearMap.isHomogeneous_shift_piece_iff.2 hh).neg
    𝒜.isHomogeneous_taylorVertex_higherTaylor (by ring) t

include hh hincl hproj in
/-- Every suspended tree summand of `transfer` has degree `1` for the shifted gradings. -/
theorem isHomogeneous_suspendedTransferTree (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.suspendedTransferTree c t)
      (fun _ ↦ (GH.shift 1).piece) (GH.shift 1).piece 1 := by
  rw [suspendedTransferTree]
  have hv := ReducedPlanarTree.isHomogeneous_evalVertex
    (LinearMap.isHomogeneous_shift_piece_iff.2 hincl)
    (LinearMap.isHomogeneous_shift_piece_iff.2 hh).neg
    𝒜.isHomogeneous_taylorVertex_higherTaylor (by ring) t
  simpa only [add_zero] using
    (LinearMap.isHomogeneous_shift_piece_iff.2 hproj).compMultilinearMap hv

include hh hincl in
/-- Every unsuspended tree summand of `transferInclusion` has cohomological degree
`1 - t.numLeaves`. -/
theorem isHomogeneous_transferInclusionTree (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.transferInclusionTree c GH t)
      (fun _ ↦ GH.piece) 𝒜.grading.piece (1 - (t.numLeaves : ℤ)) := by
  rw [MultilinearMap.isHomogeneous_def]
  intro d x hx
  have hmem (i : Fin t.numLeaves) :
      GH.koszulTwist ((t.numLeaves : ℤ) - 1 - i) (x i) ∈ (GH.shift 1).piece (d i - 1) := by
    rw [InternalGrading.shift_piece, sub_add_cancel]
    exact GH.koszulTwist_mem_piece (hx i) _
  have hs := (𝒜.isHomogeneous_suspendedTransferInclusionTree c hh hincl t).map_mem
    (fun i ↦ d i - 1) _ hmem
  rw [InternalGrading.shift_piece] at hs
  have hdeg : (∑ i : Fin t.numLeaves, (d i - 1)) + 0 + 1 =
      (∑ i, d i) + (1 - (t.numLeaves : ℤ)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rwa [transferInclusionTree, MultilinearMap.compLinearMap_apply, ← hdeg]

include hh hincl hproj in
/-- Every unsuspended tree summand of `transfer` has cohomological degree `2 - t.numLeaves`. -/
theorem isHomogeneous_transferTree (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (𝒜.transferTree c GH t)
      (fun _ ↦ GH.piece) GH.piece (2 - (t.numLeaves : ℤ)) := by
  rw [MultilinearMap.isHomogeneous_def]
  intro d x hx
  have hmem (i : Fin t.numLeaves) :
      GH.koszulTwist ((t.numLeaves : ℤ) - 1 - i) (x i) ∈ (GH.shift 1).piece (d i - 1) := by
    rw [InternalGrading.shift_piece, sub_add_cancel]
    exact GH.koszulTwist_mem_piece (hx i) _
  have hs := (𝒜.isHomogeneous_suspendedTransferTree c hh hincl hproj t).map_mem
    (fun i ↦ d i - 1) _ hmem
  rw [InternalGrading.shift_piece] at hs
  have hdeg : (∑ i : Fin t.numLeaves, (d i - 1)) + 1 + 1 =
      (∑ i, d i) + (2 - (t.numLeaves : ℤ)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rwa [transferTree, MultilinearMap.compLinearMap_apply, ← hdeg]

/-! ### Coalgebraic fixed-point equation and finite-sum transfer formulas -/

/-- Applying the higher bar differential to the perturbed bar inclusion `i - K X i` recovers
`X ∘ map(i)`, by the perturbation identity `δ K X = δ - X`. -/
theorem higherBarDifferential_comp_barMap_transferInclusion :
    𝒜.higherBarDifferential ∘ₗ (𝒜.transferInclusion c hh hincl hproj).barMap =
      (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential ∘ₗ
        ReducedTensorWords.map (R := R) c.incl := by
  rw [barMap_transferInclusion, LinearMap.comp_sub,
    ← barTensorTrick_homotopy 𝒜 c hh hincl hproj]
  have h := (𝒜.barTensorTrick c hh hincl hproj).comp_homotopy_comp_perturbationSeries_assoc
    𝒜.higherBarDifferential
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj)
    (ReducedTensorWords.map (R := R) c.incl)
  rw [h]
  abel

private theorem letter_comp_perturbationSeries_comp_map_incl :
    letter R A ∘ₗ
        (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential ∘ₗ
        ReducedTensorWords.map (R := R) c.incl =
      𝒜.higherTaylor ∘ₗ coalgHom R (𝒜.transferInclusion c hh hincl hproj).taylor := by
  rw [← 𝒜.higherBarDifferential_comp_barMap_transferInclusion c hh hincl hproj,
    ← LinearMap.comp_assoc, letter_comp_higherBarDifferential, AInfinityHom.barMap_eq_coalgHom]

/-- The Taylor map of `transferInclusion` satisfies the coalgebraic fixed-point equation with leaf
map `c.incl`, edge map `-c.homotopy`, and vertex Taylor map `𝒜.higherTaylor`. -/
theorem taylor_transferInclusion_fixedPoint :
    (𝒜.transferInclusion c hh hincl hproj).taylor =
      c.incl ∘ₗ letter R H +
        (-c.homotopy) ∘ₗ
          (𝒜.higherTaylor ∘ₗ coalgHom R (𝒜.transferInclusion c hh hincl hproj).taylor) := by
  have hK :
      letter R A ∘ₗ
          (c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) ∘ₗ
            (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential ∘ₗ
            ReducedTensorWords.map (R := R) c.incl) =
        c.homotopy ∘ₗ
          (𝒜.higherTaylor ∘ₗ coalgHom R (𝒜.transferInclusion c hh hincl hproj).taylor) := by
    rw [← LinearMap.comp_assoc, c.letter_comp_reducedTensorWordsHomotopy, LinearMap.comp_assoc,
      𝒜.letter_comp_perturbationSeries_comp_map_incl c hh hincl hproj]
  conv_lhs => rw [taylor_transferInclusion]
  rw [LinearMap.comp_sub, letter_comp_map, hK, LinearMap.neg_comp, sub_eq_add_neg]

/-- **Taylor-level planar-tree formula for `transferInclusion`**: its Taylor map is
`treeBranchTaylor c.incl (-c.homotopy) 𝒜.higherTaylor`. -/
theorem taylor_transferInclusion_eq_treeBranchTaylor :
    (𝒜.transferInclusion c hh hincl hproj).taylor =
      treeBranchTaylor c.incl (-c.homotopy) 𝒜.higherTaylor :=
  (eq_treeBranchTaylor_iff c.incl (-c.homotopy) 𝒜.higherTaylor_comp_ofLetter).2
    (𝒜.taylor_transferInclusion_fixedPoint c hh hincl hproj)

/-- **Taylor-level planar-tree formula for `transfer`**: its Taylor map is `d_H` on single letters
plus `c.proj` applied to `treeVertexTaylor c.incl (-c.homotopy) 𝒜.higherTaylor`. -/
theorem taylor_transfer_eq_add_comp_treeVertexTaylor :
    (𝒜.transfer c hh hincl hproj).taylor =
      dH ∘ₗ letter R H + c.proj ∘ₗ treeVertexTaylor c.incl (-c.homotopy) 𝒜.higherTaylor := by
  have hX :
      letter R A ∘ₗ
          (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential ∘ₗ
          ReducedTensorWords.map (R := R) c.incl =
        treeVertexTaylor c.incl (-c.homotopy) 𝒜.higherTaylor := by
    rw [𝒜.letter_comp_perturbationSeries_comp_map_incl c hh hincl hproj,
      𝒜.taylor_transferInclusion_eq_treeBranchTaylor c hh hincl hproj,
      comp_coalgHom_treeBranchTaylor c.incl (-c.homotopy) 𝒜.higherTaylor_comp_ofLetter]
  refine LinearMap.ext fun w ↦ ?_
  have hXw := LinearMap.congr_fun hX w
  simp only [LinearMap.comp_apply] at hXw
  rw [transfer_taylor, LinearMap.comp_apply, letter_transferBarDifferential]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hXw]

/-- **Planar-tree formula for the extending quasi-isomorphism**: for every arity `n`, the
unsuspended component `(𝒜.transferInclusion c hh hincl hproj).component n` is the finite sum over
`n`-leaf reduced planar trees of `transferInclusionTree`. -/
theorem component_transferInclusion_eq_sum_arity (n : ℕ) :
    (𝒜.transferInclusion c hh hincl hproj).component n =
      ∑ t : ReducedPlanarTree.Arity n,
        (𝒜.transferInclusionTree c GH t.val).domDomCongr (finCongr t.property) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [AInfinityHom.component_zero, Fintype.sum_empty]
  · ext x
    rw [AInfinityHom.component_apply _ n hn, transfer_grading,
      𝒜.taylor_transferInclusion_eq_treeBranchTaylor c hh hincl hproj, treeBranchTaylor_of_tprod,
      _root_.sum_apply]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [MultilinearMap.domDomCongr_apply, transferInclusionTree,
      MultilinearMap.compLinearMap_apply, suspendedTransferInclusionTree]
    congr 1
    funext q
    simp [t.property]
    rfl

/-- **Planar-tree formula for the transferred `A∞` operations**: for every arity `n ≠ 1`, the
transferred operation `(𝒜.transfer c hh hincl hproj).m n` is the finite sum over `n`-leaf reduced
planar trees of `transferTree`. -/
theorem m_transfer_eq_sum_arity {n : ℕ} (hn : n ≠ 1) :
    (𝒜.transfer c hh hincl hproj).m n =
      ∑ t : ReducedPlanarTree.Arity n,
        (𝒜.transferTree c GH t.val).domDomCongr (finCongr t.property) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [m_zero, Fintype.sum_empty]
  · have hne : (⟨n, hn0⟩ : {k : ℕ // 0 < k}) ≠ 1 := fun h ↦ hn (congrArg Subtype.val h)
    ext x
    rw [(𝒜.transfer c hh hincl hproj).m_eq_desuspension, transfer_grading,
      AInfinity.desuspension_apply GH _ hn0,
      𝒜.taylor_transfer_eq_add_comp_treeVertexTaylor c hh hincl hproj, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, letter_of_of_ne_one R H hne, map_zero, zero_add,
      treeVertexTaylor_of_tprod, map_sum, _root_.sum_apply]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [MultilinearMap.domDomCongr_apply, transferTree, MultilinearMap.compLinearMap_apply,
      suspendedTransferTree, LinearMap.compMultilinearMap_apply]
    congr 2
    funext q
    simp [t.property]
    rfl

/-- When `d_H = 0` (the minimal-model case), the planar-tree sum formula holds in every arity
`n : ℕ`, including `n = 1` where the single leaf evaluates to zero. -/
theorem m_transfer_eq_sum_arity_of_dH_eq_zero (hdH : dH = 0) (n : ℕ) :
    (𝒜.transfer c hh hincl hproj).m n =
      ∑ t : ReducedPlanarTree.Arity n,
        (𝒜.transferTree c GH t.val).domDomCongr (finCongr t.property) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [m_zero, Fintype.sum_empty]
  · ext x
    rw [(𝒜.transfer c hh hincl hproj).m_eq_desuspension, transfer_grading,
      AInfinity.desuspension_apply GH _ hn0,
      𝒜.taylor_transfer_eq_add_comp_treeVertexTaylor c hh hincl hproj, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.congr_fun hdH _, LinearMap.zero_apply, zero_add,
      LinearMap.comp_apply, treeVertexTaylor_of_tprod, map_sum, _root_.sum_apply]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [MultilinearMap.domDomCongr_apply, transferTree, MultilinearMap.compLinearMap_apply,
      suspendedTransferTree, LinearMap.compMultilinearMap_apply]
    congr 2
    funext q
    simp [t.property]
    rfl

/-! ### Explicit evaluation on corollas and arity-three trees -/

include hincl in
/-- On the `(k + 2)`-input corolla, `transferTree` projects `𝒜.m (k + 2)` applied to the included
inputs: the suspension and desuspension Koszul twists cancel across the degree-zero inclusion. -/
@[simp]
theorem transferTree_corolla_apply (k : ℕ)
    (x : Fin (ReducedPlanarTree.corolla k).numLeaves → H) :
    𝒜.transferTree c GH (ReducedPlanarTree.corolla k) x =
      c.proj (𝒜.m (k + 2) fun i ↦
        c.incl (x (finCongr (ReducedPlanarTree.numLeaves_corolla k).symm i))) := by
  simp only [transferTree, suspendedTransferTree, LinearMap.compMultilinearMap_apply,
    MultilinearMap.compLinearMap_apply, ReducedPlanarTree.evalVertex_corolla,
    MultilinearMap.domDomCongr_apply, taylorVertex_higherTaylor,
    ReducedPlanarTree.numLeaves_corolla]
  congr 1
  congr 1
  funext i
  have hcast : ((finCongr (ReducedPlanarTree.numLeaves_corolla k).symm i :
      Fin (ReducedPlanarTree.corolla k).numLeaves) : ℕ) = i := rfl
  have hq : ((k : ℤ) + 2 - 1 - i) = (((k + 2 : ℕ) : ℤ) - 1 - i) := by push_cast; rfl
  rw [hcast, hq, koszulTwist_apply_zero hincl, GH.koszulTwist_koszulTwist]

include hincl in
/-- On the `(k + 2)`-input corolla, `transferInclusionTree` applies `-c.homotopy` to `𝒜.m (k + 2)`
on the included inputs. -/
@[simp]
theorem transferInclusionTree_corolla_apply (k : ℕ)
    (x : Fin (ReducedPlanarTree.corolla k).numLeaves → H) :
    𝒜.transferInclusionTree c GH (ReducedPlanarTree.corolla k) x =
      -c.homotopy (𝒜.m (k + 2) fun i ↦
        c.incl (x (finCongr (ReducedPlanarTree.numLeaves_corolla k).symm i))) := by
  simp only [transferInclusionTree, suspendedTransferInclusionTree,
    MultilinearMap.compLinearMap_apply, ReducedPlanarTree.evalBranch_corolla,
    LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply,
    LinearMap.neg_apply, taylorVertex_higherTaylor, ReducedPlanarTree.numLeaves_corolla]
  congr 2
  congr 1
  funext i
  have hcast : ((finCongr (ReducedPlanarTree.numLeaves_corolla k).symm i :
      Fin (ReducedPlanarTree.corolla k).numLeaves) : ℕ) = i := rfl
  have hq : ((k : ℤ) + 2 - 1 - i) = (((k + 2 : ℕ) : ℤ) - 1 - i) := by push_cast; rfl
  rw [hcast, hq, koszulTwist_apply_zero hincl, GH.koszulTwist_koszulTwist]

include hh hincl in
private theorem evalVertex_leftBinary_twisted
    (x : Fin ReducedPlanarTree.leftBinary.numLeaves → H) :
    ReducedPlanarTree.leftBinary.evalVertex c.incl (-c.homotopy) (taylorVertex 𝒜.higherTaylor)
        (fun i ↦ GH.koszulTwist ((ReducedPlanarTree.leftBinary.numLeaves : ℤ) - 1 - i) (x i)) =
      let e := finCongr ReducedPlanarTree.numLeaves_leftBinary.symm;
      𝒜.m 2 ![c.homotopy (𝒜.m 2 ![c.incl (x (e 0)), c.incl (x (e 1))]), c.incl (x (e 2))] := by
  dsimp only
  rw [ReducedPlanarTree.evalVertex_leftBinary_apply, taylorVertex_higherTaylor,
    MultilinearMap.compLinearMap_apply, MultilinearMap.compLinearMap_apply, LinearMap.neg_apply]
  set e := finCongr ReducedPlanarTree.numLeaves_leftBinary.symm
  have hnum : (ReducedPlanarTree.leftBinary.numLeaves : ℤ) = ((3 : ℕ) : ℤ) :=
    congrArg Nat.cast ReducedPlanarTree.numLeaves_leftBinary
  have he0 : ((e 0 : Fin ReducedPlanarTree.leftBinary.numLeaves) : ℕ) = 0 := rfl
  have he1 : ((e 1 : Fin ReducedPlanarTree.leftBinary.numLeaves) : ℕ) = 1 := rfl
  have he2 : ((e 2 : Fin ReducedPlanarTree.leftBinary.numLeaves) : ℕ) = 2 := rfl
  rw [hnum, he0, he1, he2]
  congr 1
  rw [funext_iff, Fin.forall_fin_two]
  constructor
  · dsimp only [Matrix.cons_val_zero, Fin.val_zero]
    rw [map_neg, show ((0 : ℕ) : ℤ) + 2 - 1 - ((0 : ℕ) : ℤ) = 1 by norm_num]
    have harg :
        (fun j : Fin 2 ↦ 𝒜.grading.koszulTwist (((0 : ℕ) : ℤ) + 2 - 1 - j)
            (![c.incl (GH.koszulTwist (((3 : ℕ) : ℤ) - 1 - (0 : ℕ)) (x (e 0))),
              c.incl (GH.koszulTwist (((3 : ℕ) : ℤ) - 1 - (1 : ℕ)) (x (e 1)))] j)) =
          ![𝒜.grading.koszulTwist 1 (c.incl (x (e 0))),
            𝒜.grading.koszulTwist 1 (c.incl (x (e 1)))] := by
      rw [funext_iff, Fin.forall_fin_two]
      constructor
      · dsimp only [Matrix.cons_val_zero, Fin.val_zero]
        rw [show ((0 : ℕ) : ℤ) + 2 - 1 - ((0 : ℕ) : ℤ) = 1 by norm_num,
          show ((3 : ℕ) : ℤ) - 1 - ((0 : ℕ) : ℤ) = 2 * 1 by norm_num,
          GH.koszulTwist_two_mul, LinearMap.id_apply]
      · dsimp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.val_one]
        rw [show ((0 : ℕ) : ℤ) + 2 - 1 - ((1 : ℕ) : ℤ) = 0 by norm_num,
          show ((3 : ℕ) : ℤ) - 1 - ((1 : ℕ) : ℤ) = 1 by norm_num,
          InternalGrading.koszulTwist_zero, LinearMap.id_apply, koszulTwist_apply_zero hincl]
    change -𝒜.grading.koszulTwist 1
        (c.homotopy (𝒜.m 2 fun j : Fin 2 ↦ 𝒜.grading.koszulTwist (((0 : ℕ) : ℤ) + 2 - 1 - j)
          (![c.incl (GH.koszulTwist (((3 : ℕ) : ℤ) - 1 - (0 : ℕ)) (x (e 0))),
            c.incl (GH.koszulTwist (((3 : ℕ) : ℤ) - 1 - (1 : ℕ)) (x (e 1)))] j))) = _
    rw [harg, ← koszulTwist_m_two]
    have hh3 : 𝒜.grading.koszulTwist 1
        (c.homotopy (𝒜.grading.koszulTwist 1
          (𝒜.m 2 ![c.incl (x (e 0)), c.incl (x (e 1))]))) =
        -c.homotopy (𝒜.m 2 ![c.incl (x (e 0)), c.incl (x (e 1))]) := by
      have := hh.koszulTwist_apply 1
        (𝒜.grading.koszulTwist 1 (𝒜.m 2 ![c.incl (x (e 0)), c.incl (x (e 1))]))
      simpa [𝒜.grading.koszulTwist_koszulTwist] using this
    rw [hh3, neg_neg]
  · dsimp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.val_one]
    rw [show ((0 : ℕ) : ℤ) + 2 - 1 - ((1 : ℕ) : ℤ) = 0 by norm_num,
      show ((3 : ℕ) : ℤ) - 1 - ((2 : ℕ) : ℤ) = 0 by norm_num]
    simp [InternalGrading.koszulTwist_zero]

include hincl in
private theorem evalVertex_rightBinary_twisted
    (x : Fin ReducedPlanarTree.rightBinary.numLeaves → H) :
    ReducedPlanarTree.rightBinary.evalVertex c.incl (-c.homotopy) (taylorVertex 𝒜.higherTaylor)
        (fun i ↦ GH.koszulTwist ((ReducedPlanarTree.rightBinary.numLeaves : ℤ) - 1 - i) (x i)) =
      let e := finCongr ReducedPlanarTree.numLeaves_rightBinary.symm;
      -𝒜.m 2 ![c.incl (GH.koszulTwist 1 (x (e 0))),
        c.homotopy (𝒜.m 2 ![c.incl (x (e 1)), c.incl (x (e 2))])] := by
  dsimp only
  rw [ReducedPlanarTree.evalVertex_rightBinary_apply, taylorVertex_higherTaylor,
    MultilinearMap.compLinearMap_apply, MultilinearMap.compLinearMap_apply, LinearMap.neg_apply]
  set e := finCongr ReducedPlanarTree.numLeaves_rightBinary.symm
  have hnum : (ReducedPlanarTree.rightBinary.numLeaves : ℤ) = ((3 : ℕ) : ℤ) :=
    congrArg Nat.cast ReducedPlanarTree.numLeaves_rightBinary
  have he0 : ((e 0 : Fin ReducedPlanarTree.rightBinary.numLeaves) : ℕ) = 0 := rfl
  have he1 : ((e 1 : Fin ReducedPlanarTree.rightBinary.numLeaves) : ℕ) = 1 := rfl
  have he2 : ((e 2 : Fin ReducedPlanarTree.rightBinary.numLeaves) : ℕ) = 2 := rfl
  rw [hnum, he0, he1, he2]
  have harg :
      (fun i : Fin 2 ↦ 𝒜.grading.koszulTwist (((0 : ℕ) : ℤ) + 2 - 1 - i)
          (![c.incl (GH.koszulTwist (((3 : ℕ) : ℤ) - 1 - (0 : ℕ)) (x (e 0))),
            -c.homotopy (𝒜.m (0 + 2) fun j : Fin 2 ↦
              𝒜.grading.koszulTwist (((0 : ℕ) : ℤ) + 2 - 1 - j)
                (![c.incl (GH.koszulTwist (((3 : ℕ) : ℤ) - 1 - (1 : ℕ)) (x (e 1))),
                  c.incl (GH.koszulTwist (((3 : ℕ) : ℤ) - 1 - (2 : ℕ)) (x (e 2)))] j))] i)) =
        ![c.incl (GH.koszulTwist 1 (x (e 0))),
          -c.homotopy (𝒜.m 2 ![c.incl (x (e 1)), c.incl (x (e 2))])] := by
    rw [funext_iff, Fin.forall_fin_two]
    constructor
    · dsimp only [Matrix.cons_val_zero, Fin.val_zero]
      rw [show ((0 : ℕ) : ℤ) + 2 - 1 - ((0 : ℕ) : ℤ) = 1 by norm_num,
        show ((3 : ℕ) : ℤ) - 1 - ((0 : ℕ) : ℤ) = 2 * 1 by norm_num,
        GH.koszulTwist_two_mul, LinearMap.id_apply, koszulTwist_apply_zero hincl]
    · dsimp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.val_one]
      rw [show ((0 : ℕ) : ℤ) + 2 - 1 - ((1 : ℕ) : ℤ) = 0 by norm_num,
        InternalGrading.koszulTwist_zero, LinearMap.id_apply]
      refine congrArg (-c.homotopy ·) (congrArg (𝒜.m 2) ?_)
      rw [funext_iff, Fin.forall_fin_two]
      constructor
      · dsimp only [Matrix.cons_val_zero, Fin.val_zero]
        rw [show ((0 : ℕ) : ℤ) + 2 - 1 - ((0 : ℕ) : ℤ) = 1 by norm_num,
          show ((3 : ℕ) : ℤ) - 1 - ((1 : ℕ) : ℤ) = 1 by norm_num,
          koszulTwist_apply_zero hincl, GH.koszulTwist_koszulTwist]
      · dsimp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.val_one]
        rw [show ((0 : ℕ) : ℤ) + 2 - 1 - ((1 : ℕ) : ℤ) = 0 by norm_num,
          show ((3 : ℕ) : ℤ) - 1 - ((2 : ℕ) : ℤ) = 0 by norm_num]
        simp [InternalGrading.koszulTwist_zero]
  have hmul (u v : A) : 𝒜.m 2 ![u, -v] = -𝒜.m 2 ![u, v] := by
    simpa only [mul_apply] using map_neg (𝒜.mul u) v
  change 𝒜.m 2 _ = _
  rw [← hmul]
  exact congrArg (𝒜.m 2) harg

include hh hincl in
/-- On the left-leaning binary tree `((• •) •)`, `transferTree` computes
`p m₂ (h m₂ (i x₀, i x₁), i x₂)`. -/
@[simp]
theorem transferTree_leftBinary_apply (x : Fin ReducedPlanarTree.leftBinary.numLeaves → H) :
    𝒜.transferTree c GH ReducedPlanarTree.leftBinary x =
      c.proj (𝒜.m 2
        ![c.homotopy (𝒜.m 2
            ![c.incl (x (finCongr ReducedPlanarTree.numLeaves_leftBinary.symm 0)),
              c.incl (x (finCongr ReducedPlanarTree.numLeaves_leftBinary.symm 1))]),
          c.incl (x (finCongr ReducedPlanarTree.numLeaves_leftBinary.symm 2))]) := by
  rw [transferTree, MultilinearMap.compLinearMap_apply, suspendedTransferTree,
    LinearMap.compMultilinearMap_apply, 𝒜.evalVertex_leftBinary_twisted c hh hincl x]

include hincl in
/-- On the right-leaning binary tree `(• (• •))`, `transferTree` computes
`-p m₂ (i (τ x₀), h m₂ (i x₁, i x₂))`, with the Koszul twist `τ` on the first input. -/
@[simp]
theorem transferTree_rightBinary_apply (x : Fin ReducedPlanarTree.rightBinary.numLeaves → H) :
    𝒜.transferTree c GH ReducedPlanarTree.rightBinary x =
      -c.proj (𝒜.m 2
        ![c.incl (GH.koszulTwist 1 (x (finCongr ReducedPlanarTree.numLeaves_rightBinary.symm 0))),
          c.homotopy (𝒜.m 2
            ![c.incl (x (finCongr ReducedPlanarTree.numLeaves_rightBinary.symm 1)),
              c.incl (x (finCongr ReducedPlanarTree.numLeaves_rightBinary.symm 2))])]) := by
  rw [transferTree, MultilinearMap.compLinearMap_apply, suspendedTransferTree,
    LinearMap.compMultilinearMap_apply, 𝒜.evalVertex_rightBinary_twisted c hincl x, map_neg]

include hh hincl in
/-- On the left-leaning binary tree `((• •) •)`, `transferInclusionTree` computes
`-h m₂ (h m₂ (i x₀, i x₁), i x₂)`. -/
@[simp]
theorem transferInclusionTree_leftBinary_apply
    (x : Fin ReducedPlanarTree.leftBinary.numLeaves → H) :
    𝒜.transferInclusionTree c GH ReducedPlanarTree.leftBinary x =
      -c.homotopy (𝒜.m 2
        ![c.homotopy (𝒜.m 2
            ![c.incl (x (finCongr ReducedPlanarTree.numLeaves_leftBinary.symm 0)),
              c.incl (x (finCongr ReducedPlanarTree.numLeaves_leftBinary.symm 1))]),
          c.incl (x (finCongr ReducedPlanarTree.numLeaves_leftBinary.symm 2))]) := by
  rw [transferInclusionTree, MultilinearMap.compLinearMap_apply, suspendedTransferInclusionTree,
    ReducedPlanarTree.evalBranch_leftBinary, LinearMap.compMultilinearMap_apply,
    LinearMap.neg_apply, 𝒜.evalVertex_leftBinary_twisted c hh hincl x]

include hincl in
/-- On the right-leaning binary tree `(• (• •))`, `transferInclusionTree` computes
`h m₂ (i (τ x₀), h m₂ (i x₁, i x₂))`. -/
@[simp]
theorem transferInclusionTree_rightBinary_apply
    (x : Fin ReducedPlanarTree.rightBinary.numLeaves → H) :
    𝒜.transferInclusionTree c GH ReducedPlanarTree.rightBinary x =
      c.homotopy (𝒜.m 2
        ![c.incl (GH.koszulTwist 1 (x (finCongr ReducedPlanarTree.numLeaves_rightBinary.symm 0))),
          c.homotopy (𝒜.m 2
            ![c.incl (x (finCongr ReducedPlanarTree.numLeaves_rightBinary.symm 1)),
              c.incl (x (finCongr ReducedPlanarTree.numLeaves_rightBinary.symm 2))])]) := by
  rw [transferInclusionTree, MultilinearMap.compLinearMap_apply, suspendedTransferInclusionTree,
    ReducedPlanarTree.evalBranch_rightBinary, LinearMap.compMultilinearMap_apply,
    LinearMap.neg_apply, 𝒜.evalVertex_rightBinary_twisted c hincl x, map_neg, neg_neg]

/-- The **cubic component of the extending quasi-isomorphism** `transferInclusion`, obtained by
summing `transferInclusionTree` over the three reduced planar trees of arity `3`: the ternary
corolla and the left- and right-leaning binary trees. -/
@[simp]
theorem component_three_transferInclusion (x y z : H) :
    (𝒜.transferInclusion c hh hincl hproj).component 3 ![x, y, z] =
      -c.homotopy (𝒜.m 3 ![c.incl x, c.incl y, c.incl z]) -
        c.homotopy (𝒜.m 2 ![c.homotopy (𝒜.m 2 ![c.incl x, c.incl y]), c.incl z]) +
        c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 x),
          c.homotopy (𝒜.m 2 ![c.incl y, c.incl z])]) := by
  have hcast {m : ℕ} (h : m = 3) (i : Fin 3) : finCongr h (finCongr h.symm i) = i := Fin.ext rfl
  rw [𝒜.component_transferInclusion_eq_sum_arity c hh hincl hproj 3, _root_.sum_apply,
    ReducedPlanarTree.sum_arity_three]
  simp only [MultilinearMap.domDomCongr_apply,
    transferInclusionTree_corolla_apply 𝒜 c hincl,
    transferInclusionTree_leftBinary_apply 𝒜 c hh hincl,
    transferInclusionTree_rightBinary_apply 𝒜 c hincl,
    hcast, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hvec : (fun i : Fin 3 ↦ c.incl (![x, y, z] i)) = ![c.incl x, c.incl y, c.incl z] := by
    funext i; fin_cases i <;> rfl
  have h2 : ![x, y, z] 2 = z := rfl
  rw [hvec, h2]
  abel

/-! ### Specialization to binary planar trees for strict / DG algebras -/

/-- When all operations `𝒜.m k` for `k ≥ 3` vanish, every non-binary tree contributes zero to
`transferInclusionTree`. -/
theorem transferInclusionTree_eq_zero_of_not_isBinary
    (hm : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree} (ht : ¬t.IsBinary) :
    𝒜.transferInclusionTree c GH t = 0 := by
  have hv : ∀ k : ℕ, k ≠ 0 → taylorVertex 𝒜.higherTaylor k = 0 := by
    intro k hk
    rw [taylorVertex_higherTaylor, hm (k + 2) (by omega), MultilinearMap.zero_compLinearMap]
  rw [transferInclusionTree, suspendedTransferInclusionTree,
    ReducedPlanarTree.evalBranch_eq_zero_of_not_isBinary hv ht, MultilinearMap.zero_compLinearMap]

/-- When all operations `𝒜.m k` for `k ≥ 3` vanish, every non-binary tree contributes zero to
`transferTree`. -/
theorem transferTree_eq_zero_of_not_isBinary
    (hm : ∀ k, 3 ≤ k → 𝒜.m k = 0) {t : ReducedPlanarTree} (ht : ¬t.IsBinary) :
    𝒜.transferTree c GH t = 0 := by
  have hv : ∀ k : ℕ, k ≠ 0 → taylorVertex 𝒜.higherTaylor k = 0 := by
    intro k hk
    rw [taylorVertex_higherTaylor, hm (k + 2) (by omega), MultilinearMap.zero_compLinearMap]
  rw [transferTree, suspendedTransferTree,
    ReducedPlanarTree.evalVertex_eq_zero_of_not_isBinary hv ht,
    LinearMap.compMultilinearMap_zero, MultilinearMap.zero_compLinearMap]

/-- **Binary-tree formula for `transferInclusion`**: when `𝒜.m k = 0` for `k ≥ 3`, the arity-`n`
component of `transferInclusion` sums only over binary planar trees of arity `n`. -/
theorem component_transferInclusion_eq_sum_isBinary (hm : ∀ k, 3 ≤ k → 𝒜.m k = 0) (n : ℕ) :
    (𝒜.transferInclusion c hh hincl hproj).component n =
      ∑ t ∈ Finset.univ.filter (fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary),
        (𝒜.transferInclusionTree c GH t.val).domDomCongr (finCongr t.property) := by
  rw [𝒜.component_transferInclusion_eq_sum_arity c hh hincl hproj n,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary)]
  suffices ∑ t ∈ Finset.univ.filter (fun t : ReducedPlanarTree.Arity n ↦ ¬t.val.IsBinary),
      (𝒜.transferInclusionTree c GH t.val).domDomCongr (finCongr t.property) = 0 by
    rw [this, add_zero]
  refine Finset.sum_eq_zero fun t ht ↦ ?_
  rw [Finset.mem_filter] at ht
  rw [𝒜.transferInclusionTree_eq_zero_of_not_isBinary c hm ht.2]
  ext
  rfl

/-- **Binary-tree formula for `transfer`**: when `𝒜.m k = 0` for `k ≥ 3`, the arity-`n` transferred
operation (`n ≠ 1`) sums only over binary planar trees of arity `n`. -/
theorem m_transfer_eq_sum_isBinary (hm : ∀ k, 3 ≤ k → 𝒜.m k = 0) {n : ℕ} (hn : n ≠ 1) :
    (𝒜.transfer c hh hincl hproj).m n =
      ∑ t ∈ Finset.univ.filter (fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary),
        (𝒜.transferTree c GH t.val).domDomCongr (finCongr t.property) := by
  rw [𝒜.m_transfer_eq_sum_arity c hh hincl hproj hn,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary)]
  suffices ∑ t ∈ Finset.univ.filter (fun t : ReducedPlanarTree.Arity n ↦ ¬t.val.IsBinary),
      (𝒜.transferTree c GH t.val).domDomCongr (finCongr t.property) = 0 by
    rw [this, add_zero]
  refine Finset.sum_eq_zero fun t ht ↦ ?_
  rw [Finset.mem_filter] at ht
  rw [𝒜.transferTree_eq_zero_of_not_isBinary c hm ht.2]
  ext
  rfl

/-- When `d_H = 0` and `𝒜.m k = 0` for `k ≥ 3`, the binary-tree formula for `transfer` holds in
every arity `n : ℕ`, including `n = 1`. -/
theorem m_transfer_eq_sum_isBinary_of_dH_eq_zero (hdH : dH = 0)
    (hm : ∀ k, 3 ≤ k → 𝒜.m k = 0) (n : ℕ) :
    (𝒜.transfer c hh hincl hproj).m n =
      ∑ t ∈ Finset.univ.filter (fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary),
        (𝒜.transferTree c GH t.val).domDomCongr (finCongr t.property) := by
  rw [𝒜.m_transfer_eq_sum_arity_of_dH_eq_zero c hh hincl hproj hdH n,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary)]
  suffices ∑ t ∈ Finset.univ.filter (fun t : ReducedPlanarTree.Arity n ↦ ¬t.val.IsBinary),
      (𝒜.transferTree c GH t.val).domDomCongr (finCongr t.property) = 0 by
    rw [this, add_zero]
  refine Finset.sum_eq_zero fun t ht ↦ ?_
  rw [Finset.mem_filter] at ht
  rw [𝒜.transferTree_eq_zero_of_not_isBinary c hm ht.2]
  ext
  rfl

end Homogeneity

end TreeOperations

/-! ### Naturality of individual tree summands -/

section Naturality

variable {R : Type uR} [CommRing R]
  {A : Type uA} {H : Type uH} {B : Type uB} {K : Type uK}
  [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]
  [AddCommGroup B] [Module R B] [AddCommGroup K] [Module R K]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}
  {GH : InternalGrading R H ℤ} {GK : InternalGrading R K ℤ}
  {dH : Module.End R H} {dK : Module.End R K}
  (c : LinearSpecialContraction 𝒜.differential dH)
  (c' : LinearSpecialContraction ℬ.differential dK)

private theorem comp_taylorVertex_higherTaylor (f : AInfinityStrictHom 𝒜 ℬ) (k : ℕ) :
    f.toLinearMap.compMultilinearMap (taylorVertex 𝒜.higherTaylor k) =
      (taylorVertex ℬ.higherTaylor k).compLinearMap fun _ ↦ f.toLinearMap := by
  ext x
  have hm := f.map_m (k + 2) fun i ↦ 𝒜.grading.koszulTwist ((k + 2 : ℤ) - 1 - i) (x i)
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
    taylorVertex_higherTaylor, AInfinityStrictHom.coe_toLinearMap] at hm ⊢
  rw [hm]
  congr 1
  funext i
  exact (koszulTwist_apply_zero f.isHomogeneous ((k + 2 : ℤ) - 1 - i) (x i)).symm

/-- A strict `A∞` morphism intertwining the inclusions and homotopies of two contractions
intertwines every individual tree summand `transferInclusionTree` with a degree-zero retract map
`g`. -/
theorem transferInclusionTree_naturality
    (f : AInfinityStrictHom 𝒜 ℬ) (g : H →ₗ[R] K)
    (hg : LinearMap.IsHomogeneous g GH.piece GK.piece 0)
    (hι : f.toLinearMap ∘ₗ c.incl = c'.incl ∘ₗ g)
    (hη : f.toLinearMap ∘ₗ c.homotopy = c'.homotopy ∘ₗ f.toLinearMap)
    (t : ReducedPlanarTree) :
    f.toLinearMap.compMultilinearMap (𝒜.transferInclusionTree c GH t) =
      (ℬ.transferInclusionTree c' GK t).compLinearMap fun _ ↦ g := by
  have hedge : f.toLinearMap ∘ₗ (-c.homotopy) = (-c'.homotopy) ∘ₗ f.toLinearMap := by
    rw [LinearMap.comp_neg, LinearMap.neg_comp, hη]
  have hsusp := ReducedPlanarTree.comp_evalBranch g f.toLinearMap hι hedge
    (comp_taylorVertex_higherTaylor f) t
  ext x
  have hs := MultilinearMap.congr_fun hsusp fun i ↦
    GH.koszulTwist ((t.numLeaves : ℤ) - 1 - i) (x i)
  simp only [transferInclusionTree, suspendedTransferInclusionTree,
    LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] at hs ⊢
  rw [hs]
  congr 1
  funext i
  exact (koszulTwist_apply_zero hg ((t.numLeaves : ℤ) - 1 - i) (x i)).symm

/-- A strict `A∞` morphism and a degree-zero retract map `g` intertwining the inclusions,
projections, and homotopies of two contractions intertwine every individual tree summand
`transferTree`. -/
theorem transferTree_naturality
    (f : AInfinityStrictHom 𝒜 ℬ) (g : H →ₗ[R] K)
    (hg : LinearMap.IsHomogeneous g GH.piece GK.piece 0)
    (hι : f.toLinearMap ∘ₗ c.incl = c'.incl ∘ₗ g)
    (hπ : g ∘ₗ c.proj = c'.proj ∘ₗ f.toLinearMap)
    (hη : f.toLinearMap ∘ₗ c.homotopy = c'.homotopy ∘ₗ f.toLinearMap)
    (t : ReducedPlanarTree) :
    g.compMultilinearMap (𝒜.transferTree c GH t) =
      (ℬ.transferTree c' GK t).compLinearMap fun _ ↦ g := by
  have hedge : f.toLinearMap ∘ₗ (-c.homotopy) = (-c'.homotopy) ∘ₗ f.toLinearMap := by
    rw [LinearMap.comp_neg, LinearMap.neg_comp, hη]
  have hsusp := ReducedPlanarTree.comp_evalVertex g f.toLinearMap hι hedge
    (comp_taylorVertex_higherTaylor f) t
  ext x
  have hp := LinearMap.congr_fun hπ
    (t.evalVertex c.incl (-c.homotopy) (taylorVertex 𝒜.higherTaylor)
      fun i ↦ GH.koszulTwist ((t.numLeaves : ℤ) - 1 - i) (x i))
  have hs := MultilinearMap.congr_fun hsusp fun i ↦
    GH.koszulTwist ((t.numLeaves : ℤ) - 1 - i) (x i)
  simp only [transferTree, suspendedTransferTree, LinearMap.compMultilinearMap_apply,
    MultilinearMap.compLinearMap_apply, LinearMap.comp_apply] at hp hs ⊢
  rw [hp, hs]
  congr 2
  funext i
  exact (koszulTwist_apply_zero hg ((t.numLeaves : ℤ) - 1 - i) (x i)).symm

end Naturality

end TauCeti.AInfinityAlgebra

/-! ### Specialization to nonunital differential graded algebras -/

namespace TauCeti.IsNonUnitalDGAlgebra

variable {R : Type uR} {A : Type uA} {H : Type uH} [CommRing R]
  [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [AddCommGroup H] [Module R H]
  {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  {d : A →ₗ[R] A} (hDG : IsNonUnitalDGAlgebra 𝒜 d)
  {GH : InternalGrading R H ℤ} {dH : Module.End R H}
  (c : LinearSpecialContraction hDG.toAInfinityAlgebra.differential dH)
  (hh : LinearMap.IsHomogeneous c.homotopy hDG.toAInfinityAlgebra.grading.piece
    hDG.toAInfinityAlgebra.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece hDG.toAInfinityAlgebra.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj hDG.toAInfinityAlgebra.grading.piece GH.piece 0)

/-- For a nonunital DG algebra, the arity-`n` component of `transferInclusion` sums only over binary
planar trees of arity `n` (Kontsevich--Soibelman / Merkulov binary-tree formula). -/
theorem component_transferInclusion_eq_sum_isBinary (n : ℕ) :
    (hDG.toAInfinityAlgebra.transferInclusion c hh hincl hproj).component n =
      ∑ t ∈ Finset.univ.filter (fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary),
        (hDG.toAInfinityAlgebra.transferInclusionTree c GH t.val).domDomCongr
          (finCongr t.property) :=
  hDG.toAInfinityAlgebra.component_transferInclusion_eq_sum_isBinary c hh hincl hproj
    (fun _ hk ↦ hDG.toAInfinityAlgebra_m_of_three_le hk) n

/-- For a nonunital DG algebra, every transferred higher operation (`n ≠ 1`) sums only over binary
planar trees of arity `n` (Kontsevich--Soibelman / Merkulov binary-tree formula). -/
theorem m_transfer_eq_sum_isBinary {n : ℕ} (hn : n ≠ 1) :
    (hDG.toAInfinityAlgebra.transfer c hh hincl hproj).m n =
      ∑ t ∈ Finset.univ.filter (fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary),
        (hDG.toAInfinityAlgebra.transferTree c GH t.val).domDomCongr (finCongr t.property) :=
  hDG.toAInfinityAlgebra.m_transfer_eq_sum_isBinary c hh hincl hproj
    (fun _ hk ↦ hDG.toAInfinityAlgebra_m_of_three_le hk) hn

/-- For a minimal-model transfer (`d_H = 0`) of a nonunital DG algebra, every transferred operation
(`n : ℕ`) sums only over binary planar trees of arity `n`. -/
theorem m_transfer_eq_sum_isBinary_of_dH_eq_zero (hdH : dH = 0) (n : ℕ) :
    (hDG.toAInfinityAlgebra.transfer c hh hincl hproj).m n =
      ∑ t ∈ Finset.univ.filter (fun t : ReducedPlanarTree.Arity n ↦ t.val.IsBinary),
        (hDG.toAInfinityAlgebra.transferTree c GH t.val).domDomCongr (finCongr t.property) :=
  hDG.toAInfinityAlgebra.m_transfer_eq_sum_isBinary_of_dH_eq_zero c hh hincl hproj hdH
    (fun _ hk ↦ hDG.toAInfinityAlgebra_m_of_three_le hk) n

end TauCeti.IsNonUnitalDGAlgebra
