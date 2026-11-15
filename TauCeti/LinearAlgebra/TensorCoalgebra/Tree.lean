/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import TauCeti.Combinatorics.Tree.ReducedPlanar
public import TauCeti.LinearAlgebra.Graded.Multilinear
public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom

/-!
# Planar-tree multilinear operations and coalgebraic fixed points

Given a leaf map `leafMap : N →ₗ[R] M`, an internal-edge operator `edge : M →ₗ[R] M`, and a family
of vertex operations `vertex k : (Fin (k + 2) → M) →ₘₗ[R] M` of arities at least two, every reduced
planar tree `t : ReducedPlanarTree` determines two multilinear maps in `t.numLeaves` variables:

* `ReducedPlanarTree.evalBranch`: places `leafMap` on the input leaves, `vertex k` at each internal
  vertex of valence `k + 2`, `edge` on every internal edge, and `edge` at the root whenever `t` has
  at least two leaves (so on the single leaf it is `leafMap`).
* `ReducedPlanarTree.evalVertex`: vanishes on the single leaf and, on a non-leaf tree, applies the
  root vertex operation directly to the branch evaluations of its children without applying `edge`
  at the root. Postcomposing `evalVertex` with any linear map `rootMap : M →ₗ[R] P` therefore
  decorates the root by `rootMap` while keeping `edge` on all internal edges.

Summing these evaluations over the finite type `ReducedPlanarTree.Arity n` of `n`-leaf reduced
planar trees assembles Taylor maps `ReducedTensorWords.treeBranchTaylor` and
`ReducedTensorWords.treeVertexTaylor` on the reduced tensor coalgebra `Tᶜ(N)`. When
`μ : Tᶜ(M) →ₗ[R] M` vanishes on single letters, expanding the unique coalgebra morphism
`coalgHom R f` over ordered forests (`ReducedPlanarTree.Forest`) identifies
`treeBranchTaylor leafMap edge μ` as the unique solution of the coalgebraic fixed-point equation

`f = leafMap ∘ₗ letter + edge ∘ₗ (μ ∘ₗ coalgHom R f)`,

with `μ ∘ₗ coalgHom R (treeBranchTaylor leafMap edge μ) = treeVertexTaylor leafMap edge μ`. In
homological transfer of `A∞` algebras, this fixed-point equation is satisfied by the Taylor map of
the extending `A∞` quasi-isomorphism, yielding the Kontsevich--Soibelman and Merkulov planar-tree
formulas.

## Main definitions

* `TauCeti.ReducedPlanarTree.evalBranch`: multilinear evaluation of a reduced planar tree with
  `edge` applied at non-leaf roots.
* `TauCeti.ReducedPlanarTree.evalVertex`: multilinear evaluation of a reduced planar tree at its
  root vertex, vanishing on `leaf`.
* `TauCeti.ReducedTensorWords.taylorVertex`: the arity-`(k + 2)` multilinear maps extracted from a
  linear map `Tᶜ(M) →ₗ[R] M`.
* `TauCeti.ReducedTensorWords.treeBranchTaylor`, `TauCeti.ReducedTensorWords.treeVertexTaylor`:
  Taylor maps on `Tᶜ(N)` given by summing tree evaluations over `ReducedPlanarTree.Arity n`.

## Main results

* `TauCeti.ReducedPlanarTree.isHomogeneous_evalBranch`,
  `TauCeti.ReducedPlanarTree.isHomogeneous_evalVertex`: degree tracking for homogeneous leaf, edge,
  and vertex maps.
* `TauCeti.ReducedPlanarTree.evalVertex_eq_zero_of_not_isBinary`,
  `TauCeti.ReducedPlanarTree.evalBranch_eq_zero_of_not_isBinary`: trees with a vertex of arity at
  least three vanish when all operations of arity at least three vanish.
* `TauCeti.ReducedTensorWords.coalgHom_fixedPoint_unique`: uniqueness of solutions to
  `f = g + edge ∘ₗ (μ ∘ₗ coalgHom R f)` when `μ` vanishes on single letters.
* `TauCeti.ReducedTensorWords.comp_coalgHom_treeBranchTaylor`:
  `μ ∘ₗ coalgHom R (treeBranchTaylor leafMap edge μ) = treeVertexTaylor leafMap edge μ`.
* `TauCeti.ReducedTensorWords.eq_treeBranchTaylor_iff`: characterization of
  `treeBranchTaylor leafMap edge μ` by its coalgebraic fixed-point equation.

## References

* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*, Section 6.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Section 10.3.
* S. A. Merkulov, *Strongly homotopy algebras of a Kähler manifold*, Internat. Math. Res. Notices
  (1999), no. 3, 153--164.
-/

public section

open scoped BigOperators DirectSum

universe uR uN uM uP uι

namespace TauCeti

namespace ReducedPlanarTree

section Multilinear

variable {R : Type uR} {N : Type uN} {M : Type uM}
  [CommSemiring R] [AddCommMonoid N] [Module R N] [AddCommMonoid M] [Module R M]

/-- Evaluate a reduced planar tree as a multilinear map `(Fin t.numLeaves → N) →ₘₗ[R] M`, placing
`leafMap` at every leaf, `vertex k` at every internal vertex of valence `k + 2`, and `edge` on every
internal edge as well as at the root of any tree with at least two leaves. -/
def evalBranch (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M) :
    (t : ReducedPlanarTree) → MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ N) M
  | leaf => MultilinearMap.ofSubsingleton (RingHom.id R) N M (0 : Fin 1) leafMap
  | node k children =>
      edge.compMultilinearMap
        (((vertex k).compMultilinearMap
          (fun i ↦ (children i).evalBranch leafMap edge vertex)).domDomCongr finSigmaFinEquiv)

/-- Evaluate a reduced planar tree at its root vertex without applying `edge` at the root. On the
single leaf this vanishes, since `leaf` has no internal vertex. -/
def evalVertex (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M) :
    (t : ReducedPlanarTree) → MultilinearMap (RingHom.id R) (fun _ : Fin t.numLeaves ↦ N) M
  | leaf => 0
  | node k children =>
      ((vertex k).compMultilinearMap
        (fun i ↦ (children i).evalBranch leafMap edge vertex)).domDomCongr finSigmaFinEquiv

@[simp]
theorem evalBranch_leaf (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M) :
    leaf.evalBranch leafMap edge vertex =
      MultilinearMap.ofSubsingleton (RingHom.id R) N M (0 : Fin 1) leafMap :=
  (rfl)

theorem evalBranch_leaf_apply (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M)
    (x : Fin leaf.numLeaves → N) :
    leaf.evalBranch leafMap edge vertex x = leafMap (x (0 : Fin 1)) :=
  (rfl)

@[simp]
theorem evalVertex_leaf (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M) :
    leaf.evalVertex leafMap edge vertex = 0 :=
  (rfl)

@[simp]
theorem evalBranch_node (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M)
    (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    (node k children).evalBranch leafMap edge vertex =
      edge.compMultilinearMap ((node k children).evalVertex leafMap edge vertex) :=
  (rfl)

theorem evalVertex_node (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M)
    (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree) :
    (node k children).evalVertex leafMap edge vertex =
      ((vertex k).compMultilinearMap
        (fun i ↦ (children i).evalBranch leafMap edge vertex)).domDomCongr finSigmaFinEquiv :=
  (rfl)

theorem evalVertex_node_apply (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M)
    (k : ℕ) (children : Fin (k + 2) → ReducedPlanarTree)
    (x : Fin (node k children).numLeaves → N) :
    (node k children).evalVertex leafMap edge vertex x =
      vertex k fun i ↦ (children i).evalBranch leafMap edge vertex
        fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩) :=
  (rfl)

/-- On the `(k + 2)`-input corolla, `evalVertex` applies `vertex k` to `leafMap` on each input. -/
@[simp]
theorem evalVertex_corolla (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M) (k : ℕ) :
    (corolla k).evalVertex leafMap edge vertex =
      ((vertex k).compLinearMap fun _ ↦ leafMap).domDomCongr
        (finCongr (numLeaves_corolla k).symm) := by
  ext x
  change vertex k (fun i ↦ leaf.evalBranch leafMap edge vertex
      fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) =
    vertex k fun i ↦ leafMap (x (finCongr (numLeaves_corolla k).symm i))
  congr 1
  funext i
  rw [evalBranch_leaf_apply]
  refine congrArg leafMap (congrArg x (Fin.ext ?_))
  simp

/-- On the `(k + 2)`-input corolla, `evalBranch` applies `edge` after `vertex k` on the `leafMap`
images of the inputs. -/
@[simp]
theorem evalBranch_corolla (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M) (k : ℕ) :
    (corolla k).evalBranch leafMap edge vertex =
      edge.compMultilinearMap
        (((vertex k).compLinearMap fun _ ↦ leafMap).domDomCongr
          (finCongr (numLeaves_corolla k).symm)) := by
  ext x
  have hv := MultilinearMap.congr_fun (evalVertex_corolla leafMap edge vertex k) x
  change edge ((corolla k).evalVertex leafMap edge vertex x) = _
  rw [hv, LinearMap.compMultilinearMap_apply]

@[simp]
theorem evalBranch_leftBinary (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M) :
    leftBinary.evalBranch leafMap edge vertex =
      edge.compMultilinearMap (leftBinary.evalVertex leafMap edge vertex) :=
  (rfl)

@[simp]
theorem evalVertex_leftBinary_apply (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M)
    (x : Fin leftBinary.numLeaves → N) :
    leftBinary.evalVertex leafMap edge vertex x =
      vertex 0 ![edge (vertex 0 ![leafMap (x (finCongr numLeaves_leftBinary.symm 0)),
          leafMap (x (finCongr numLeaves_leftBinary.symm 1))]),
        leafMap (x (finCongr numLeaves_leftBinary.symm 2))] := by
  change vertex 0 (fun i ↦ (![corolla 0, leaf] i).evalBranch leafMap edge vertex
      fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) = _
  congr 1
  rw [funext_iff, Fin.forall_fin_two]
  refine ⟨?_, congrArg leafMap (congrArg x (Fin.ext (by simp)))⟩
  change (corolla 0).evalBranch leafMap edge vertex
      (fun j ↦ x (finSigmaFinEquiv (n := fun r ↦ (![corolla 0, leaf] r).numLeaves) ⟨0, j⟩)) = _
  rw [evalBranch_corolla, LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.compLinearMap_apply]
  congr 1
  congr 1
  rw [funext_iff, Fin.forall_fin_two]
  exact ⟨congrArg leafMap (congrArg x (Fin.ext (by simp))),
    congrArg leafMap (congrArg x (Fin.ext (by simp)))⟩

@[simp]
theorem evalBranch_rightBinary (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M) :
    rightBinary.evalBranch leafMap edge vertex =
      edge.compMultilinearMap (rightBinary.evalVertex leafMap edge vertex) :=
  (rfl)

@[simp]
theorem evalVertex_rightBinary_apply (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M)
    (x : Fin rightBinary.numLeaves → N) :
    rightBinary.evalVertex leafMap edge vertex x =
      vertex 0 ![leafMap (x (finCongr numLeaves_rightBinary.symm 0)),
        edge (vertex 0 ![leafMap (x (finCongr numLeaves_rightBinary.symm 1)),
          leafMap (x (finCongr numLeaves_rightBinary.symm 2))])] := by
  change vertex 0 (fun i ↦ (![leaf, corolla 0] i).evalBranch leafMap edge vertex
      fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) = _
  congr 1
  rw [funext_iff, Fin.forall_fin_two]
  refine ⟨congrArg leafMap (congrArg x (Fin.ext (by simp))), ?_⟩
  change (corolla 0).evalBranch leafMap edge vertex
      (fun j ↦ x (finSigmaFinEquiv (n := fun r ↦ (![leaf, corolla 0] r).numLeaves) ⟨1, j⟩)) = _
  rw [evalBranch_corolla, LinearMap.compMultilinearMap_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.compLinearMap_apply]
  congr 1
  congr 1
  rw [funext_iff, Fin.forall_fin_two]
  exact ⟨congrArg leafMap (congrArg x (Fin.ext (by simp))),
    congrArg leafMap (congrArg x (Fin.ext (by simp)))⟩

/-- When all vertex operations of arity at least three vanish, every non-binary tree has zero
branch evaluation. -/
theorem evalBranch_eq_zero_of_not_isBinary {leafMap : N →ₗ[R] M} {edge : M →ₗ[R] M}
    {vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M}
    (hvertex : ∀ k : ℕ, k ≠ 0 → vertex k = 0) {t : ReducedPlanarTree} (ht : ¬t.IsBinary) :
    t.evalBranch leafMap edge vertex = 0 := by
  induction t with
  | leaf => exact absurd isBinary_leaf ht
  | node k children ih =>
    rw [isBinary_node, not_and_or] at ht
    ext x
    rw [evalBranch_node, LinearMap.compMultilinearMap_apply, evalVertex_node_apply, zero_apply]
    rcases ht with hk | hchild
    · rw [hvertex k hk, zero_apply, map_zero]
    · push Not at hchild
      obtain ⟨i, hi⟩ := hchild
      have hzero : (children i).evalBranch leafMap edge vertex
          (fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) = 0 := by
        rw [ih i hi, zero_apply]
      rw [(vertex k).map_coord_zero i hzero, map_zero]

/-- When all vertex operations of arity at least three vanish, every non-binary tree has zero
root-vertex evaluation. -/
theorem evalVertex_eq_zero_of_not_isBinary {leafMap : N →ₗ[R] M} {edge : M →ₗ[R] M}
    {vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M}
    (hvertex : ∀ k : ℕ, k ≠ 0 → vertex k = 0) {t : ReducedPlanarTree} (ht : ¬t.IsBinary) :
    t.evalVertex leafMap edge vertex = 0 := by
  cases t with
  | leaf => exact evalVertex_leaf leafMap edge vertex
  | node k children =>
    rw [isBinary_node, not_and_or] at ht
    ext x
    rw [evalVertex_node_apply, zero_apply]
    rcases ht with hk | hchild
    · rw [hvertex k hk, zero_apply]
    · push Not at hchild
      obtain ⟨i, hi⟩ := hchild
      have hzero : (children i).evalBranch leafMap edge vertex
          (fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)) = 0 := by
        rw [evalBranch_eq_zero_of_not_isBinary hvertex hi, zero_apply]
      exact (vertex k).map_coord_zero i hzero

/-- Naturality of `evalBranch` under linear maps intertwining the leaf, edge, and vertex data. -/
theorem comp_evalBranch {N' M' : Type*} [AddCommMonoid N'] [Module R N']
    [AddCommMonoid M'] [Module R M']
    {leafMap : N →ₗ[R] M} {edge : M →ₗ[R] M}
    {vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M}
    {leafMap' : N' →ₗ[R] M'} {edge' : M' →ₗ[R] M'}
    {vertex' : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M') M'}
    (φN : N →ₗ[R] N') (φM : M →ₗ[R] M')
    (hleaf : φM ∘ₗ leafMap = leafMap' ∘ₗ φN)
    (hedge : φM ∘ₗ edge = edge' ∘ₗ φM)
    (hvertex : ∀ k : ℕ,
      φM.compMultilinearMap (vertex k) = (vertex' k).compLinearMap fun _ ↦ φM)
    (t : ReducedPlanarTree) :
    φM.compMultilinearMap (t.evalBranch leafMap edge vertex) =
      (t.evalBranch leafMap' edge' vertex').compLinearMap fun _ ↦ φN := by
  induction t with
  | leaf =>
    ext x
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      evalBranch_leaf_apply, evalBranch_leaf_apply]
    exact LinearMap.congr_fun hleaf (x (0 : Fin 1))
  | node k children ih =>
    ext x
    have hed := LinearMap.congr_fun hedge ((node k children).evalVertex leafMap edge vertex x)
    have hv := MultilinearMap.congr_fun (hvertex k)
      (fun i ↦ (children i).evalBranch leafMap edge vertex fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩))
    simp only [evalBranch_node, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      MultilinearMap.compLinearMap_apply, evalVertex_node_apply] at hed hv ⊢
    rw [hed, hv]
    congr 1
    congr 1
    funext i
    exact MultilinearMap.congr_fun (ih i) fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)

/-- Naturality of `evalVertex` under linear maps intertwining the leaf, edge, and vertex data. -/
theorem comp_evalVertex {N' M' : Type*} [AddCommMonoid N'] [Module R N']
    [AddCommMonoid M'] [Module R M']
    {leafMap : N →ₗ[R] M} {edge : M →ₗ[R] M}
    {vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M}
    {leafMap' : N' →ₗ[R] M'} {edge' : M' →ₗ[R] M'}
    {vertex' : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M') M'}
    (φN : N →ₗ[R] N') (φM : M →ₗ[R] M')
    (hleaf : φM ∘ₗ leafMap = leafMap' ∘ₗ φN)
    (hedge : φM ∘ₗ edge = edge' ∘ₗ φM)
    (hvertex : ∀ k : ℕ,
      φM.compMultilinearMap (vertex k) = (vertex' k).compLinearMap fun _ ↦ φM)
    (t : ReducedPlanarTree) :
    φM.compMultilinearMap (t.evalVertex leafMap edge vertex) =
      (t.evalVertex leafMap' edge' vertex').compLinearMap fun _ ↦ φN := by
  cases t with
  | leaf =>
    ext x
    simp
  | node k children =>
    ext x
    have hv := MultilinearMap.congr_fun (hvertex k)
      (fun i ↦ (children i).evalBranch leafMap edge vertex fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩))
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      evalVertex_node_apply] at hv ⊢
    rw [hv]
    congr 1
    funext i
    exact MultilinearMap.congr_fun (comp_evalBranch φN φM hleaf hedge hvertex (children i))
      fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)

end Multilinear

section Homogeneous

variable {R : Type uR} {ι : Type uι} {N : Type uN} {M : Type uM} {σN σM : Type*}
  [CommSemiring R] [AddCommMonoid ι]
  [AddCommMonoid N] [Module R N] [AddCommMonoid M] [Module R M]
  [SetLike σN N] [SetLike σM M]

private theorem isHomogeneous_domDomCongr {κ κ' : Type*} [Fintype κ] [Fintype κ'] (e : κ ≃ κ')
    {f : MultilinearMap (RingHom.id R) (fun _ : κ ↦ N) M}
    {𝒜 : ι → σN} {ℬ : ι → σM} {q : ι}
    (hf : MultilinearMap.IsHomogeneous f (fun _ ↦ 𝒜) ℬ q) :
    MultilinearMap.IsHomogeneous (f.domDomCongr e) (fun _ ↦ 𝒜) ℬ q := by
  rw [MultilinearMap.isHomogeneous_def] at hf ⊢
  intro d x hx
  have hdeg : ∑ i, d (e i) = ∑ j, d j := Fintype.sum_equiv e _ _ fun _ ↦ rfl
  simpa only [MultilinearMap.domDomCongr_apply, hdeg] using
    hf (fun i ↦ d (e i)) (fun i ↦ x (e i)) fun i ↦ hx (e i)

/-- When `leafMap` has degree `0`, `vertex k` has degree `q`, `edge` has degree `r`, and
`q + r = 0` (as in the suspended bar grading, where `q = 1` and `r = -1`), every branch evaluation
`t.evalBranch` has degree `0`. -/
theorem isHomogeneous_evalBranch
    {leafMap : N →ₗ[R] M} {edge : M →ₗ[R] M}
    {vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M}
    {𝒜 : ι → σN} {ℬ : ι → σM} {q r : ι}
    (hleaf : LinearMap.IsHomogeneous leafMap 𝒜 ℬ 0)
    (hedge : LinearMap.IsHomogeneous edge ℬ ℬ r)
    (hvertex : ∀ k : ℕ, MultilinearMap.IsHomogeneous (vertex k) (fun _ ↦ ℬ) ℬ q)
    (hqr : q + r = 0) (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (t.evalBranch leafMap edge vertex) (fun _ ↦ 𝒜) ℬ 0 := by
  induction t with
  | leaf =>
    rw [MultilinearMap.isHomogeneous_def]
    intro d x hx
    have hd : ∑ i, d i = d (0 : Fin 1) := Fin.sum_univ_one d
    rw [evalBranch_leaf_apply, hd]
    exact hleaf.map_mem (hx (0 : Fin 1))
  | node k children ih =>
    have h0 : (∑ _ : Fin (k + 2), (0 : ι)) + q = q := by rw [Finset.sum_const_zero, zero_add]
    have hv : MultilinearMap.IsHomogeneous ((node k children).evalVertex leafMap edge vertex)
        (fun _ ↦ 𝒜) ℬ q :=
      h0 ▸ isHomogeneous_domDomCongr finSigmaFinEquiv ((hvertex k).compMultilinearMap ih)
    exact hqr ▸ hedge.compMultilinearMap hv

/-- Under the same degree hypotheses as `isHomogeneous_evalBranch`, every root-vertex evaluation
`t.evalVertex` has degree `q`. -/
theorem isHomogeneous_evalVertex [ZeroMemClass σM M]
    {leafMap : N →ₗ[R] M} {edge : M →ₗ[R] M}
    {vertex : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M}
    {𝒜 : ι → σN} {ℬ : ι → σM} {q r : ι}
    (hleaf : LinearMap.IsHomogeneous leafMap 𝒜 ℬ 0)
    (hedge : LinearMap.IsHomogeneous edge ℬ ℬ r)
    (hvertex : ∀ k : ℕ, MultilinearMap.IsHomogeneous (vertex k) (fun _ ↦ ℬ) ℬ q)
    (hqr : q + r = 0) (t : ReducedPlanarTree) :
    MultilinearMap.IsHomogeneous (t.evalVertex leafMap edge vertex) (fun _ ↦ 𝒜) ℬ q := by
  cases t with
  | leaf => exact MultilinearMap.isHomogeneous_zero _ _ _
  | node k children =>
    have ih := fun i ↦ isHomogeneous_evalBranch hleaf hedge hvertex hqr (children i)
    have h0 : (∑ _ : Fin (k + 2), (0 : ι)) + q = q := by rw [Finset.sum_const_zero, zero_add]
    exact h0 ▸ isHomogeneous_domDomCongr finSigmaFinEquiv ((hvertex k).compMultilinearMap ih)

end Homogeneous

end ReducedPlanarTree

/-! ## Tree Taylor maps and the coalgebraic fixed-point equation -/

namespace ReducedTensorWords

section Semiring

variable {R : Type uR} {N : Type uN} {M : Type uM} {P : Type uP}
  [CommSemiring R] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]

/-- Extract the arity-`(k + 2)` multilinear map `(Fin (k + 2) → M) →ₘₗ[R] M` from a linear map
`μ : Tᶜ(M) →ₗ[R] M` on the reduced tensor coalgebra. -/
noncomputable def taylorVertex (μ : ReducedTensorWords R M →ₗ[R] M) (k : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ M) M :=
  (μ ∘ₗ of R M ⟨k + 2, by omega⟩).compMultilinearMap (PiTensorProduct.tprod R)

theorem taylorVertex_def (μ : ReducedTensorWords R M →ₗ[R] M) (k : ℕ) :
    taylorVertex μ k =
      (μ ∘ₗ of R M ⟨k + 2, by omega⟩).compMultilinearMap (PiTensorProduct.tprod R) :=
  (rfl)

@[simp]
theorem taylorVertex_apply (μ : ReducedTensorWords R M →ₗ[R] M) (k : ℕ)
    (x : Fin (k + 2) → M) :
    taylorVertex μ k x = μ (of R M ⟨k + 2, by omega⟩ (PiTensorProduct.tprod R x)) :=
  (rfl)

/-- The Taylor map `Tᶜ(N) →ₗ[R] M` whose arity-`n` component is the sum over all `n`-leaf reduced
planar trees of `ReducedPlanarTree.evalBranch`. -/
noncomputable def treeBranchTaylor (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) : ReducedTensorWords R N →ₗ[R] M :=
  DirectSum.toModule R _ M fun n ↦
    PiTensorProduct.lift
      (∑ t : ReducedPlanarTree.Arity n.1,
        (t.val.evalBranch leafMap edge (taylorVertex μ)).domDomCongr (finCongr t.property))

/-- The Taylor map `Tᶜ(N) →ₗ[R] M` whose arity-`n` component is the sum over all `n`-leaf reduced
planar trees of `ReducedPlanarTree.evalVertex`. -/
noncomputable def treeVertexTaylor (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) : ReducedTensorWords R N →ₗ[R] M :=
  DirectSum.toModule R _ M fun n ↦
    PiTensorProduct.lift
      (∑ t : ReducedPlanarTree.Arity n.1,
        (t.val.evalVertex leafMap edge (taylorVertex μ)).domDomCongr (finCongr t.property))

@[simp]
theorem treeBranchTaylor_of_tprod (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) (n : {n : ℕ // 0 < n}) (x : Fin n.1 → N) :
    treeBranchTaylor leafMap edge μ (of R N n (PiTensorProduct.tprod R x)) =
      ∑ t : ReducedPlanarTree.Arity n.1,
        t.val.evalBranch leafMap edge (taylorVertex μ) (x ∘ Fin.cast t.property) := by
  simp [treeBranchTaylor, toModule_of]
  rfl

@[simp]
theorem treeVertexTaylor_of_tprod (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) (n : {n : ℕ // 0 < n}) (x : Fin n.1 → N) :
    treeVertexTaylor leafMap edge μ (of R N n (PiTensorProduct.tprod R x)) =
      ∑ t : ReducedPlanarTree.Arity n.1,
        t.val.evalVertex leafMap edge (taylorVertex μ) (x ∘ Fin.cast t.property) := by
  simp [treeVertexTaylor, toModule_of]
  rfl

@[simp]
theorem treeVertexTaylor_ofLetter (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) (a : N) :
    treeVertexTaylor leafMap edge μ (ofLetter R N a) = 0 := by
  rw [ofLetter_eq_of_tprod, treeVertexTaylor_of_tprod, Fintype.sum_unique]
  rfl

@[simp]
theorem treeBranchTaylor_ofLetter (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) (a : N) :
    treeBranchTaylor leafMap edge μ (ofLetter R N a) = leafMap a := by
  rw [ofLetter_eq_of_tprod, treeBranchTaylor_of_tprod, Fintype.sum_unique]
  rfl

/-- Splitting `treeBranchTaylor` into the single-leaf term (arity one) and `edge` applied to
`treeVertexTaylor` (arity at least two). -/
theorem treeBranchTaylor_eq_add_comp_treeVertexTaylor (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) :
    treeBranchTaylor leafMap edge μ =
      leafMap ∘ₗ letter R N + edge ∘ₗ treeVertexTaylor leafMap edge μ := by
  refine linearMap_ext R N fun n x ↦ ?_
  by_cases hn : n = 1
  · subst hn
    have hx : of R N 1 (PiTensorProduct.tprod R x) = ofLetter R N (x 0) := by
      rw [ofLetter_eq_of_tprod]
      exact congrArg (of R N 1 ∘ PiTensorProduct.tprod R)
        (funext fun i ↦ congrArg x (Fin.eq_zero i))
    rw [hx, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      treeBranchTaylor_ofLetter, letter_ofLetter, treeVertexTaylor_ofLetter, map_zero, add_zero]
  · rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      letter_of_of_ne_one R N hn, map_zero, zero_add, treeBranchTaylor_of_tprod,
      treeVertexTaylor_of_tprod, map_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rcases t with ⟨t, ht⟩
    cases t with
    | leaf =>
      exact absurd (Subtype.ext ht.symm) hn
    | node k children =>
      rfl

/-! ### Uniqueness of the coalgebraic fixed point -/

private theorem coalgHom_subword_congr {f₁ f₂ : ReducedTensorWords R N →ₗ[R] M}
    {l : ℕ} (x : Fin l → N) :
    ∀ b : ℕ, (∀ c ≤ b, ∀ a : ℕ, f₁ (subword R x a c) = f₂ (subword R x a c)) →
      ∀ a : ℕ, coalgHom R f₁ (subword R x a b) = coalgHom R f₂ (subword R x a b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h a
    rw [coalgHom_subword, coalgHom_subword, h b le_rfl a]
    congr 1
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp only [subword_length_zero, map_zero, LinearMap.zero_apply]
    · rw [h d hd.le a, ih (b - d) (by omega) (fun c hc ↦ h c (by omega)) (a + d)]

/-- If `μ : Tᶜ(M) →ₗ[R] P` vanishes on single letters, then any two linear maps
`f₁, f₂ : Tᶜ(N) →ₗ[R] M` solving `f = g + edge ∘ₗ (μ ∘ₗ coalgHom R f)` are equal. -/
theorem coalgHom_fixedPoint_unique {g : ReducedTensorWords R N →ₗ[R] M} {edge : P →ₗ[R] M}
    {μ : ReducedTensorWords R M →ₗ[R] P} (hμ : μ ∘ₗ ofLetter R M = 0)
    {f₁ f₂ : ReducedTensorWords R N →ₗ[R] M}
    (hf₁ : f₁ = g + edge ∘ₗ (μ ∘ₗ coalgHom R f₁))
    (hf₂ : f₂ = g + edge ∘ₗ (μ ∘ₗ coalgHom R f₂)) :
    f₁ = f₂ := by
  have hμ_letter (y : M) : μ (ofLetter R M y) = 0 := LinearMap.congr_fun hμ y
  have hsub : ∀ (b : ℕ) {l : ℕ} (x : Fin l → N) (a : ℕ),
      f₁ (subword R x a b) = f₂ (subword R x a b) := by
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro l x a
      have hμ_eq : μ (coalgHom R f₁ (subword R x a b)) =
          μ (coalgHom R f₂ (subword R x a b)) := by
        rw [coalgHom_subword, coalgHom_subword, map_add, map_add, hμ_letter, hμ_letter,
          zero_add, zero_add, map_sum, map_sum]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        rw [Finset.mem_range] at hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp only [subword_length_zero, map_zero, LinearMap.zero_apply]
        · rw [ih d hd x a,
            coalgHom_subword_congr x (b - d) (fun c hc a' ↦ ih c (by omega) x a') (a + d)]
      calc f₁ (subword R x a b)
          _ = g (subword R x a b) + edge (μ (coalgHom R f₁ (subword R x a b))) := by
              simpa [LinearMap.add_apply, LinearMap.comp_apply] using
                LinearMap.congr_fun hf₁ (subword R x a b)
          _ = g (subword R x a b) + edge (μ (coalgHom R f₂ (subword R x a b))) := by
              rw [hμ_eq]
          _ = f₂ (subword R x a b) := by
              simpa [LinearMap.add_apply, LinearMap.comp_apply] using
                (LinearMap.congr_fun hf₂ (subword R x a b)).symm
  refine linearMap_ext R N fun n x ↦ ?_
  rw [of_tprod_eq_subword R n.2, hsub n.1 x 0]

/-! ### Forest expansion of `coalgHom (treeBranchTaylor ...)` -/

/-- Evaluate each tree in an ordered forest `ts : Forest m b` on its contiguous slice of the block
starting at position `a` of `x : Fin l → N`. -/
private noncomputable def forestEval (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) {l : ℕ} (x : Fin l → N) (a : ℕ) {m b : ℕ}
    (hab : a + b ≤ l) (ts : ReducedPlanarTree.Forest m b) : Fin m → M :=
  fun i ↦ (ts.val i).evalBranch leafMap edge (taylorVertex μ) fun q ↦
    x ⟨a + (finSigmaFinEquiv (n := fun j ↦ (ts.val j).numLeaves) ⟨i, q⟩).val, by
      have hlt :=
        ((finSigmaFinEquiv (n := fun j ↦ (ts.val j).numLeaves) ⟨i, q⟩).isLt).trans_eq ts.property
      omega⟩

private theorem forestEval_forestConsEquiv (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) {l : ℕ} (x : Fin l → N) (a : ℕ) {m b : ℕ}
    (hm : 0 < m) (hab : a + b ≤ l) (d : Fin b) (t₀ : ReducedPlanarTree.Arity d.val)
    (rest : ReducedPlanarTree.Forest m (b - d.val)) :
    forestEval leafMap edge μ x a hab (ReducedPlanarTree.forestConsEquiv hm b ⟨d, t₀, rest⟩) =
      Fin.cons
        (t₀.val.evalBranch leafMap edge (taylorVertex μ) fun q ↦
          x ⟨a + (Fin.cast t₀.property q).val, by
            have := (Fin.cast t₀.property q).isLt; have := d.isLt; omega⟩)
        (forestEval leafMap edge μ x (a + d.val) (by have := d.isLt; omega) rest) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    dsimp [forestEval]
    congr 1
    funext q
    refine congrArg x (Fin.ext ?_)
    simp
  | succ r =>
    dsimp [forestEval]
    congr 1
    funext q
    refine congrArg x (Fin.ext ?_)
    simp only [finSigmaFinEquiv_apply, Fin.val_succ]
    rw [Fin.sum_univ_succ]
    have h0 : Fin.castLE (Nat.succ_le_succ r.isLt.le) (0 : Fin (r.val + 1)) = 0 := rfl
    have hs (j : Fin r.val) :
        Fin.castLE (Nat.succ_le_succ r.isLt.le) j.succ = (Fin.castLE r.isLt.le j).succ := rfl
    simp only [ReducedPlanarTree.forestConsEquiv_apply_val, h0, Fin.cons_zero, hs, Fin.cons_succ,
      t₀.property]
    omega

/-- On a valid subword of length `b > 0`, `coalgHom R (treeBranchTaylor leafMap edge μ)` expands as
the sum over forest lengths `1 ≤ m ≤ b` and ordered forests `ts : Forest m b` of the pure tensor
words formed by evaluating each tree of `ts` on its slice of inputs. -/
private theorem coalgHom_treeBranchTaylor_subword (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    (μ : ReducedTensorWords R M →ₗ[R] M) {l : ℕ} (x : Fin l → N) {a b : ℕ}
    (hb : 0 < b) (hab : a + b ≤ l) :
    coalgHom R (treeBranchTaylor leafMap edge μ) (subword R x a b) =
      ∑ m ∈ Finset.Icc 1 b,
        if hm : 0 < m then
          ∑ ts : ReducedPlanarTree.Forest m b,
            of R M ⟨m, hm⟩ (PiTensorProduct.tprod R (forestEval leafMap edge μ x a hab ts))
        else 0 := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    let φ : ℕ → ReducedTensorWords R M := fun m ↦
      if hm : 0 < m then
        ∑ ts : ReducedPlanarTree.Forest m b,
          of R M ⟨m, hm⟩ (PiTensorProduct.tprod R (forestEval leafMap edge μ x a hab ts))
      else 0
    -- Evaluate `treeBranchTaylor` on any nonempty subword of `x`.
    have hf_sub {a' c : ℕ} (hc : 0 < c) (hac : a' + c ≤ l) :
        treeBranchTaylor leafMap edge μ (subword R x a' c) =
          ∑ t : ReducedPlanarTree.Arity c,
            t.val.evalBranch leafMap edge (taylorVertex μ) fun q ↦
              x ⟨a' + (Fin.cast t.property q).val, by
                have := (Fin.cast t.property q).isLt; omega⟩ := by
      rw [subword_eq_of_tprod R x hc hac, treeBranchTaylor_of_tprod]
      rfl
    -- The `m = 1` summand matches `ofLetter (f (subword R x a b))` via `forestOneEquiv`.
    have hm1 : ofLetter R M (treeBranchTaylor leafMap edge μ (subword R x a b)) = φ 1 := by
      dsimp only [φ]
      rw [dite_eq_left Nat.one_pos, hf_sub hb hab, map_sum]
      refine Fintype.sum_equiv (ReducedPlanarTree.forestOneEquiv b).symm _ _ fun t ↦ ?_
      rw [ofLetter_eq_of_tprod]
      refine congrArg (of R M 1 ∘ PiTensorProduct.tprod R) (funext fun i ↦ ?_)
      rw [Fin.eq_zero i]
      dsimp [forestEval]
      congr 1
      funext q
      refine congrArg x (Fin.ext ?_)
      simp
    -- Rewrite `coalgHom_subword` and evaluate the tail sum over `d : Fin b`.
    rw [coalgHom_subword, hm1, ← Fin.sum_univ_eq_sum_range]
    have htail :
        (∑ d : Fin b,
          prepend R M (treeBranchTaylor leafMap edge μ (subword R x a d.val))
            (coalgHom R (treeBranchTaylor leafMap edge μ)
              (subword R x (a + d.val) (b - d.val)))) =
          ∑ m ∈ Finset.Icc 1 (b - 1), φ (m + 1) := by
      have hd_term (d : Fin b) :
          prepend R M (treeBranchTaylor leafMap edge μ (subword R x a d.val))
            (coalgHom R (treeBranchTaylor leafMap edge μ)
              (subword R x (a + d.val) (b - d.val))) =
            ∑ m ∈ Finset.Icc 1 (b - 1),
              if hm : 0 < m then
                ∑ t₀ : ReducedPlanarTree.Arity d.val,
                  ∑ rest : ReducedPlanarTree.Forest m (b - d.val),
                    of R M ⟨m + 1, Nat.succ_pos m⟩
                      (PiTensorProduct.tprod R
                        (forestEval leafMap edge μ x a hab
                          (ReducedPlanarTree.forestConsEquiv hm b ⟨d, t₀, rest⟩)))
              else 0 := by
        rcases d with ⟨_ | d, hdlt⟩
        · simp only [subword_length_zero, map_zero, LinearMap.zero_apply]
          symm
          refine Finset.sum_eq_zero fun m _ ↦ ?_
          split_ifs with hm
          · exact Fintype.sum_empty _
          · rfl
        · dsimp only
          rw [hf_sub (Nat.succ_pos d) (by omega),
            ih (b - (d + 1)) (by omega) (by omega) (by omega)]
          have hext :
              (∑ m ∈ Finset.Icc 1 (b - (d + 1)),
                if hm : 0 < m then
                  ∑ ts : ReducedPlanarTree.Forest m (b - (d + 1)),
                    of R M ⟨m, hm⟩ (PiTensorProduct.tprod R
                      (forestEval leafMap edge μ x (a + (d + 1)) (by omega) ts))
                else 0) =
              ∑ m ∈ Finset.Icc 1 (b - 1),
                if hm : 0 < m then
                  ∑ ts : ReducedPlanarTree.Forest m (b - (d + 1)),
                    of R M ⟨m, hm⟩ (PiTensorProduct.tprod R
                      (forestEval leafMap edge μ x (a + (d + 1)) (by omega) ts))
                else 0 := by
            refine Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega)) fun m hm₁ hm₂ ↦ ?_
            rw [Finset.mem_Icc] at hm₁ hm₂
            have hgt : b - (d + 1) < m := by omega
            split_ifs with hm
            · have := ReducedPlanarTree.isEmpty_forest_of_lt hgt
              exact Fintype.sum_empty _
            · rfl
          rw [hext, map_sum]
          refine Finset.sum_congr rfl fun m hm_mem ↦ ?_
          have hm : 0 < m := (Finset.mem_Icc.mp hm_mem).1
          rw [dite_eq_left hm, dite_eq_left hm, map_sum (prepend R M), LinearMap.sum_apply]
          refine Finset.sum_congr rfl fun t₀ _ ↦ ?_
          rw [map_sum]
          refine Finset.sum_congr rfl fun rest _ ↦ ?_
          rw [prepend_of_tprod, forestEval_forestConsEquiv]
      simp_rw [hd_term]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm_mem ↦ ?_
      have hm : 0 < m := (Finset.mem_Icc.mp hm_mem).1
      dsimp only [φ]
      rw [dite_eq_left (Nat.succ_pos m)]
      symm
      rw [← Fintype.sum_equiv (ReducedPlanarTree.forestConsEquiv hm b) _ _ fun _ ↦ rfl,
        Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      rw [dite_eq_left hm, Fintype.sum_prod_type]
    rw [htail]
    change φ 1 + ∑ m ∈ Finset.Icc 1 (b - 1), φ (m + 1) = ∑ m ∈ Finset.Icc 1 b, φ m
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb) with rfl | hb2
    · simp
    · have hshift : ∑ m ∈ Finset.Icc 1 (b - 1), φ (m + 1) = ∑ m ∈ Finset.Icc 2 b, φ m := by
        have h := Finset.sum_Ico_add (f := φ) 1 b 1
        have h1 : Finset.Ico 1 b = Finset.Icc 1 (b - 1) := by
          ext k
          simp only [Finset.mem_Ico, Finset.mem_Icc]
          omega
        have h2 : Finset.Ico (1 + 1) (b + 1) = Finset.Icc 2 b := by
          ext k
          simp only [Finset.mem_Ico, Finset.mem_Icc]
          omega
        rw [h1, h2] at h
        simpa only [Nat.add_comm 1] using h
      rw [hshift]
      have hunion : insert 1 (Finset.Icc 2 b) = Finset.Icc 1 b := by
        ext k
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [← hunion, Finset.sum_insert (by simp)]

/-- **Forest collapse identity**: when `μ : Tᶜ(M) →ₗ[R] M` vanishes on single letters, applying `μ`
to the coalgebra morphism generated by `treeBranchTaylor leafMap edge μ` produces
`treeVertexTaylor leafMap edge μ`. -/
theorem comp_coalgHom_treeBranchTaylor (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    {μ : ReducedTensorWords R M →ₗ[R] M} (hμ : μ ∘ₗ ofLetter R M = 0) :
    μ ∘ₗ coalgHom R (treeBranchTaylor leafMap edge μ) = treeVertexTaylor leafMap edge μ := by
  have hμ1 (y : Fin 1 → M) : μ (of R M 1 (PiTensorProduct.tprod R y)) = 0 := by
    have hy : of R M 1 (PiTensorProduct.tprod R y) = ofLetter R M (y 0) := by
      rw [ofLetter_eq_of_tprod]
      exact congrArg (of R M 1 ∘ PiTensorProduct.tprod R)
        (funext fun i ↦ congrArg y (Fin.eq_zero i))
    rw [hy]
    exact LinearMap.congr_fun hμ (y 0)
  refine linearMap_ext R N fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2,
    coalgHom_treeBranchTaylor_subword leafMap edge μ x n.2 (by omega), map_sum,
    ← of_tprod_eq_subword R n.2, treeVertexTaylor_of_tprod]
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt n.2) with hn1 | hn2
  · have hn_eq : n = 1 := Subtype.ext hn1.symm
    subst hn_eq
    refine Eq.trans (b := 0) ?_ ?_
    · change ∑ m ∈ Finset.Icc 1 1, _ = 0
      rw [Finset.Icc_self, Finset.sum_singleton, dite_eq_left Nat.one_pos, map_sum]
      exact Finset.sum_eq_zero fun _ _ ↦ hμ1 _
    · symm
      rw [Fintype.sum_unique]
      rfl
  · -- Split off `m = 1` (killed by `hμ`) and reindex `m = k + 2` for `k : Fin (n - 1)` via
    -- `ReducedPlanarTree.nodeEquiv`.
    have hunion : Finset.Icc 1 n.1 = insert 1 (Finset.Icc 2 n.1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hunion, Finset.sum_insert (by simp)]
    have hm1_zero :
        μ (if hm : 0 < 1 then
            ∑ ts : ReducedPlanarTree.Forest 1 n.1,
              of R M ⟨1, hm⟩ (PiTensorProduct.tprod R
                (forestEval leafMap edge μ x 0 (by omega) ts))
          else 0) = 0 := by
      rw [dite_eq_left Nat.one_pos, map_sum]
      exact Finset.sum_eq_zero fun _ _ ↦ hμ1 _
    rw [hm1_zero, zero_add]
    -- Reindex `m ∈ Finset.Icc 2 n.1` as `k : Fin (n.1 - 1)` via `m = k.val + 2`.
    let ψ : ℕ → M := fun m ↦
      μ (if hm : 0 < m then
          ∑ ts : ReducedPlanarTree.Forest m n.1,
            of R M ⟨m, hm⟩ (PiTensorProduct.tprod R
              (forestEval leafMap edge μ x 0 (by omega) ts))
        else 0)
    change ∑ m ∈ Finset.Icc 2 n.1, ψ m = _
    have hreindex : ∑ m ∈ Finset.Icc 2 n.1, ψ m = ∑ k : Fin (n.1 - 1), ψ (k.val + 2) := by
      rw [Fin.sum_univ_eq_sum_range (fun k ↦ ψ (k + 2)) (n.1 - 1), ← Nat.Ico_zero_eq_range]
      have h := Finset.sum_Ico_add (f := ψ) 0 (n.1 - 1) 2
      have h2 : Finset.Ico (0 + 2) (n.1 - 1 + 2) = Finset.Icc 2 n.1 := by
        ext k
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      rw [h2] at h
      simpa only [Nat.add_comm 2] using h.symm
    rw [hreindex]
    have hψ :
        ∑ k : Fin (n.1 - 1), ψ (k.val + 2) =
          ∑ p : (Σ k : Fin (n.1 - 1), ReducedPlanarTree.Forest (k.val + 2) n.1),
            (ReducedPlanarTree.nodeEquiv hn2 p).val.evalVertex leafMap edge (taylorVertex μ)
              (x ∘ Fin.cast (ReducedPlanarTree.nodeEquiv hn2 p).property) := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      dsimp only [ψ]
      rw [dite_eq_left (by omega), map_sum]
      refine Finset.sum_congr rfl fun ts _ ↦ ?_
      change μ (of R M ⟨k.val + 2, _⟩ (PiTensorProduct.tprod R
          (forestEval leafMap edge μ x 0 (by omega) ts))) =
        (ReducedPlanarTree.node k.val ts.val).evalVertex leafMap edge (taylorVertex μ)
          (x ∘ Fin.cast ((ReducedPlanarTree.numLeaves_node k.val ts.val).trans ts.property))
      rw [← taylorVertex_apply, ReducedPlanarTree.evalVertex_node_apply]
      congr 1
      funext i
      dsimp [forestEval]
      congr 1
      funext q
      exact congrArg x (Fin.ext (Nat.zero_add _))
    rw [hψ]
    exact Fintype.sum_equiv (ReducedPlanarTree.nodeEquiv hn2) _ _ fun _ ↦ rfl

/-- `treeBranchTaylor leafMap edge μ` satisfies the coalgebraic fixed-point equation whenever `μ`
vanishes on single letters. -/
theorem treeBranchTaylor_fixedPoint (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    {μ : ReducedTensorWords R M →ₗ[R] M} (hμ : μ ∘ₗ ofLetter R M = 0) :
    treeBranchTaylor leafMap edge μ =
      leafMap ∘ₗ letter R N + edge ∘ₗ (μ ∘ₗ coalgHom R (treeBranchTaylor leafMap edge μ)) := by
  rw [comp_coalgHom_treeBranchTaylor leafMap edge hμ,
    ← treeBranchTaylor_eq_add_comp_treeVertexTaylor]

/-- **Coalgebraic fixed-point characterization of planar-tree sums**: when `μ : Tᶜ(M) →ₗ[R] M`
vanishes on single letters, `treeBranchTaylor leafMap edge μ` is the unique linear map
`f : Tᶜ(N) →ₗ[R] M` satisfying `f = leafMap ∘ₗ letter R N + edge ∘ₗ (μ ∘ₗ coalgHom R f)`. -/
theorem eq_treeBranchTaylor_iff (leafMap : N →ₗ[R] M) (edge : M →ₗ[R] M)
    {μ : ReducedTensorWords R M →ₗ[R] M} (hμ : μ ∘ₗ ofLetter R M = 0)
    {f : ReducedTensorWords R N →ₗ[R] M} :
    f = treeBranchTaylor leafMap edge μ ↔
      f = leafMap ∘ₗ letter R N + edge ∘ₗ (μ ∘ₗ coalgHom R f) :=
  ⟨fun hf ↦ hf ▸ treeBranchTaylor_fixedPoint leafMap edge hμ,
   fun hf ↦ coalgHom_fixedPoint_unique hμ hf (treeBranchTaylor_fixedPoint leafMap edge hμ)⟩

end Semiring

end ReducedTensorWords

end TauCeti
