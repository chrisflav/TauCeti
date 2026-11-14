/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Analysis.Normed.Group.Ultra
public import TauCeti.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor

import Mathlib.Basic.Real.Pointwise
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The ultrametric product seminorm and norm on completed tensor products

Let `A` be a commutative ring and `V`, `W` seminormed `A`-modules. The *nonarchimedean product
seminorm* `TauCeti.Huber.BanachModule.productSeminorm A V W` of `u : V ⊗[A] W` is the infimum of
`max_i ‖v_i‖ * ‖w_i‖` over all finite presentations `u = ∑ i, v_i ⊗ₜ w_i` (with the empty maximum
equal to zero). Unlike the archimedean projective seminorm, which sums the termwise products
`‖v_i‖ * ‖w_i‖`, this seminorm takes their maximum and satisfies the strong triangle inequality
`productSeminorm A V W (x + y) ≤ max (productSeminorm A V W x) (productSeminorm A V W y)`. It is
the largest nonarchimedean additive group seminorm on `V ⊗[A] W` bounded on pure tensors by
`‖v‖ * ‖w‖`.

When `A` is a seminormed commutative ring whose action on `V` is bounded, the topology of
`productSeminorm A V W` is coarser than the tensor topology `TauCeti.Huber.banachTensorTopology`,
so `productSeminorm A V W` is uniformly continuous for `TauCeti.Huber.banachTensorUniformSpace`
and extends continuously to `TauCeti.Huber.BanachModule.CompletedTensor.productNorm` on the
completed tensor product `V ⊗̂_A W`.

When `A` is moreover Tate for its norm (`TauCeti.NormedRing.IsTate A`) and both `V` and `W` have
bounded scalar actions, rescaling pure tensors as `v ⊗ₜ w = (ϖ ^ n • v) ⊗ₜ (ϖ ^ (-n) • w)` by a
multiplicative pseudo-uniformiser `ϖ` identifies the tensor topology and uniformity on `V ⊗[A] W`
with those of `productSeminorm A V W` (`hasBasis_banachTensorTopology`,
`banachTensorTopology_eq_productSeminorm`, `banachTensorUniformSpace_eq_productSeminorm`). For
contractive actions (`IsBoundedSMul A V`, `IsBoundedSMul A W`), this equips `V ⊗̂_A W` with a
complete ultrametric `NormedAddCommGroup` structure whose underlying uniformity and additive group
are definitionally those of `CompletedTensor A V W`, whose norm is `productNorm A V W`, and for
which the canonical map `V ⊗[A] W → V ⊗̂_A W` has norm `productSeminorm A V W`.

## Main definitions

* `TauCeti.Huber.BanachModule.productSeminorm A V W`: the nonarchimedean product seminorm on
  `V ⊗[A] W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNorm A V W`: its continuous extension to
  `V ⊗̂_A W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.normedAddCommGroupOfBoundedSMul`: the ultrametric
  norm on `V ⊗̂_A W` for modules with bounded (not necessarily contractive) `A`-actions over a
  Tate ring `A`, compatible with the existing uniformity of `CompletedTensor A V W`.
* `NormedAddCommGroup (CompletedTensor A V W)`, `IsUltrametricDist (CompletedTensor A V W)`,
  `IsBoundedSMul A (CompletedTensor A V W)`: global instances for contractive actions over a Tate
  ring `A`.
* `TauCeti.Huber.BanachModule.CompletedTensor.lidₗᵢ`: the isometric unit equivalence
  `A ⊗̂_A M ≃ₗᵢ[A] M`.

## Main results

* `TauCeti.Huber.BanachModule.productSeminorm_sum_tmul_le` and
  `TauCeti.Huber.BanachModule.exists_sum_tmul_eq_of_productSeminorm_lt`: finite-presentation
  characterisation of `productSeminorm`.
* `TauCeti.Huber.BanachModule.apply_le_mul_productSeminorm` and
  `TauCeti.Huber.BanachModule.le_productSeminorm`: universal property among nonarchimedean
  seminorms.
* `TauCeti.Huber.BanachModule.hasBasis_banachTensorTopology`,
  `TauCeti.Huber.BanachModule.banachTensorTopology_eq_productSeminorm` and
  `TauCeti.Huber.BanachModule.banachTensorUniformSpace_eq_productSeminorm`: agreement of the
  tensor topology and uniformity with those of `productSeminorm` over a Tate ring.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNorm_toCompletion` and
  `TauCeti.Huber.BanachModule.CompletedTensor.norm_lift_le_mul_productNorm`: extension of
  `productSeminorm` and norm bounds on lifted bilinear maps.
* `TauCeti.Huber.BanachModule.CompletedTensor.opNorm_lift_le` and
  `TauCeti.Huber.BanachModule.CompletedTensor.opNorm_map_le`: operator-norm bounds on `lift` and
  `map` over nontrivially normed fields.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  Definitions 2.1.10 and 2.2.7, and Lemma 2.2.9.
-/

public section

open Filter Set TensorProduct Topology UniformSpace
open scoped NNReal Uniformity

namespace TauCeti.Huber.BanachModule

section Algebraic

variable {A V W : Type*} [CommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- The maximum termwise product `max_i ‖v i‖₊ * ‖w i‖₊` of a finite presentation in `V ⊗[A] W`,
with the empty maximum equal to `0` in `ℝ≥0`. -/
private noncomputable def presentationCost {n : ℕ} (v : Fin n → V) (w : Fin n → W) : ℝ :=
  ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ)

variable (A V W) in
/-- The set of maximum costs of all finite presentations `∑ i, v i ⊗ₜ w i = u`. -/
private def maxCosts (u : V ⊗[A] W) : Set ℝ :=
  {c | ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
    ∑ i, v i ⊗ₜ[A] w i = u ∧ presentationCost v w = c}

private theorem presentationCost_nonneg {n : ℕ} (v : Fin n → V) (w : Fin n → W) :
    0 ≤ presentationCost v w :=
  NNReal.coe_nonneg _

private theorem presentationCost_le_iff {n : ℕ} (v : Fin n → V) (w : Fin n → W) {b : ℝ}
    (hb : 0 ≤ b) : presentationCost v w ≤ b ↔ ∀ i, ‖v i‖ * ‖w i‖ ≤ b := by
  lift b to ℝ≥0 using hb
  rw [presentationCost, NNReal.coe_le_coe, Finset.sup_le_iff]
  simp [← NNReal.coe_le_coe]

private theorem norm_mul_le_presentationCost {n : ℕ} (v : Fin n → V) (w : Fin n → W) (i : Fin n) :
    ‖v i‖ * ‖w i‖ ≤ presentationCost v w :=
  (presentationCost_le_iff v w (presentationCost_nonneg v w)).1 le_rfl i

private theorem presentationCost_append_le {n m : ℕ} (v : Fin n → V) (w : Fin n → W)
    (v' : Fin m → V) (w' : Fin m → W) :
    presentationCost (Fin.append v v') (Fin.append w w') ≤
      max (presentationCost v w) (presentationCost v' w') := by
  refine (presentationCost_le_iff _ _ (le_max_of_le_left (presentationCost_nonneg v w))).2 ?_
  refine Fin.addCases (fun i ↦ ?_) fun j ↦ ?_
  · simpa [Fin.append_left] using
      (norm_mul_le_presentationCost v w i).trans (le_max_left _ _)
  · simpa [Fin.append_right] using
      (norm_mul_le_presentationCost v' w' j).trans (le_max_right _ _)

private theorem maxCosts_nonempty (u : V ⊗[A] W) : (maxCosts A V W u).Nonempty := by
  obtain ⟨n, v, w, hu⟩ := TensorProduct.exists_sum_tmul_eq u
  exact ⟨_, n, v, w, hu.symm, rfl⟩

private theorem maxCosts_bddBelow (u : V ⊗[A] W) : BddBelow (maxCosts A V W u) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, v, w, -, rfl⟩
  exact presentationCost_nonneg v w

private theorem sInf_maxCosts_le {n : ℕ} (v : Fin n → V) (w : Fin n → W) :
    sInf (maxCosts A V W (∑ i, v i ⊗ₜ[A] w i)) ≤ presentationCost v w :=
  csInf_le (maxCosts_bddBelow _) ⟨n, v, w, rfl, rfl⟩

private theorem sInf_maxCosts_zero : sInf (maxCosts A V W 0) = 0 := by
  refine le_antisymm ?_ (le_csInf (maxCosts_nonempty 0) ?_)
  · simpa [presentationCost] using
      sInf_maxCosts_le (A := A) (Fin.elim0 : Fin 0 → V) (Fin.elim0 : Fin 0 → W)
  · rintro _ ⟨n, v, w, -, rfl⟩
    exact presentationCost_nonneg v w

private theorem sInf_maxCosts_neg (u : V ⊗[A] W) :
    sInf (maxCosts A V W (-u)) = sInf (maxCosts A V W u) := by
  have key : ∀ x : V ⊗[A] W, sInf (maxCosts A V W (-x)) ≤ sInf (maxCosts A V W x) := fun x ↦ by
    refine le_csInf (maxCosts_nonempty x) ?_
    rintro _ ⟨n, v, w, rfl, rfl⟩
    have hsum : -∑ i, v i ⊗ₜ[A] w i = ∑ i, (-v i) ⊗ₜ[A] w i := by
      simp [Finset.sum_neg_distrib, TensorProduct.neg_tmul]
    rw [hsum]
    refine (sInf_maxCosts_le (A := A) (fun i ↦ -v i) w).trans ?_
    simp [presentationCost]
  exact (key u).antisymm (by simpa using key (-u))

private theorem sInf_maxCosts_add_le (x y : V ⊗[A] W) :
    sInf (maxCosts A V W (x + y)) ≤ max (sInf (maxCosts A V W x)) (sInf (maxCosts A V W y)) := by
  refine le_of_forall_gt fun c hc ↦ ?_
  obtain ⟨_, ⟨n, v, w, rfl, rfl⟩, hvc⟩ :=
    exists_lt_of_csInf_lt (maxCosts_nonempty x) ((le_max_left _ _).trans_lt hc)
  obtain ⟨_, ⟨m, v', w', rfl, rfl⟩, hv'c⟩ :=
    exists_lt_of_csInf_lt (maxCosts_nonempty y) ((le_max_right _ _).trans_lt hc)
  have hsum : (∑ i, v i ⊗ₜ[A] w i) + ∑ j, v' j ⊗ₜ[A] w' j =
      ∑ k, Fin.append v v' k ⊗ₜ[A] Fin.append w w' k := by
    simp [Fin.sum_univ_add]
  rw [hsum]
  exact (sInf_maxCosts_le _ _).trans_lt
    ((presentationCost_append_le v w v' w').trans_lt (max_lt hvc hv'c))

variable (A V W) in
/-- **The nonarchimedean product seminorm** on `V ⊗[A] W`: the infimum of `max_i ‖v i‖ * ‖w i‖`
over all finite presentations `u = ∑ i, v i ⊗ₜ w i` (with the empty maximum equal to zero). -/
noncomputable def productSeminorm : NonarchAddGroupSeminorm (V ⊗[A] W) where
  toFun u := sInf (maxCosts A V W u)
  map_zero' := sInf_maxCosts_zero
  add_le_max' := sInf_maxCosts_add_le
  neg' := sInf_maxCosts_neg

private theorem productSeminorm_apply (u : V ⊗[A] W) :
    productSeminorm A V W u = sInf (maxCosts A V W u) :=
  rfl

/-- The product seminorm of a finite sum of pure tensors is bounded by any nonnegative bound on
its termwise norm products `‖v i‖ * ‖w i‖`. -/
theorem productSeminorm_sum_tmul_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W)
    {b : ℝ} (hb : 0 ≤ b) (h : ∀ i ∈ s, ‖v i‖ * ‖w i‖ ≤ b) :
    productSeminorm A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) ≤ b := by
  let e := s.equivFin
  have hsum : ∑ i ∈ s, v i ⊗ₜ[A] w i = ∑ j : Fin s.card, v (e.symm j) ⊗ₜ[A] w (e.symm j) := by
    rw [← Finset.sum_coe_sort s, ← e.symm.sum_comp]
  rw [hsum, productSeminorm_apply]
  exact (sInf_maxCosts_le _ _).trans <|
    (presentationCost_le_iff _ _ hb).2 fun j ↦ h (e.symm j) (e.symm j).2

/-- A strict upper bound on `productSeminorm A V W u` is witnessed by a finite presentation whose
termwise norm products all lie strictly below `c`. -/
theorem exists_sum_tmul_eq_of_productSeminorm_lt {u : V ⊗[A] W} {c : ℝ}
    (h : productSeminorm A V W u < c) :
    ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
      ∑ i, v i ⊗ₜ[A] w i = u ∧ (∀ i, ‖v i‖ * ‖w i‖ < c) := by
  obtain ⟨_, ⟨n, v, w, hu, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (maxCosts_nonempty u) h
  exact ⟨n, v, w, hu, fun i ↦ (norm_mul_le_presentationCost v w i).trans_lt hc⟩

/-- The product seminorm of a pure tensor is at most the product of the norms of its factors. -/
theorem productSeminorm_tmul_le (v : V) (w : W) :
    productSeminorm A V W (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖ := by
  simpa using productSeminorm_sum_tmul_le {()} (fun _ ↦ v) (fun _ ↦ w) (by positivity)
    fun _ _ ↦ le_rfl

/-- **Universal property of the product seminorm.** Any nonarchimedean additive group seminorm `p`
bounded on the images of pure tensors by `C * (‖v‖ * ‖w‖)` (with `0 ≤ C`) is bounded on the image
of every tensor by `C * productSeminorm A V W u`. -/
theorem apply_le_mul_productSeminorm {G F : Type*} [AddCommGroup G] [FunLike F G ℝ]
    [NonarchAddGroupSeminormClass F G] (p : F) (f : V ⊗[A] W →+ G) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, p (f (v ⊗ₜ[A] w)) ≤ C * (‖v‖ * ‖w‖)) (u : V ⊗[A] W) :
    p (f u) ≤ C * productSeminorm A V W u := by
  rw [productSeminorm_apply, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hC]
  refine le_csInf (maxCosts_nonempty u).smul_set ?_
  rintro _ ⟨_, ⟨n, v, w, rfl, rfl⟩, rfl⟩
  dsimp only
  rw [smul_eq_mul, map_sum]
  suffices ∀ s : Finset (Fin n), p (∑ i ∈ s, f (v i ⊗ₜ[A] w i)) ≤ C * presentationCost v w from
    this Finset.univ
  intro s
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, map_zero]
    exact mul_nonneg hC (presentationCost_nonneg v w)
  | cons i s hi ih =>
    rw [Finset.sum_cons]
    refine (map_add_le_max p _ _).trans (max_le ?_ ih)
    exact (h (v i) (w i)).trans
      (mul_le_mul_of_nonneg_left (norm_mul_le_presentationCost v w i) hC)

/-- `productSeminorm A V W` is the largest nonarchimedean additive group seminorm on `V ⊗[A] W`
bounded on pure tensors by `‖v‖ * ‖w‖`. -/
theorem le_productSeminorm {p : NonarchAddGroupSeminorm (V ⊗[A] W)}
    (h : ∀ v w, p (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖) : p ≤ productSeminorm A V W := fun u ↦ by
  simpa using apply_le_mul_productSeminorm p (AddMonoidHom.id _) zero_le_one
    (by simpa using h) u

/-- If an action on `V` commuting with `A` scales norms by at most `C`, then it scales
`productSeminorm A V W` by at most `C`. -/
theorem productSeminorm_smul_le {S : Type*} [Monoid S] [DistribMulAction S V]
    [SMulCommClass A S V] {s : S} {C : ℝ} (hC : 0 ≤ C) (hs : ∀ v : V, ‖s • v‖ ≤ C * ‖v‖)
    (u : V ⊗[A] W) :
    productSeminorm A V W (s • u) ≤ C * productSeminorm A V W u := by
  let fs : V ⊗[A] W →+ V ⊗[A] W :=
    { toFun z := s • z
      map_zero' := smul_zero s
      map_add' := smul_add s }
  have hpure (v : V) (w : W) :
      productSeminorm A V W (fs (v ⊗ₜ[A] w)) ≤ C * (‖v‖ * ‖w‖) := by
    change productSeminorm A V W ((s • v) ⊗ₜ[A] w) ≤ C * (‖v‖ * ‖w‖)
    exact (productSeminorm_tmul_le (s • v) w).trans <| by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hs v) (norm_nonneg w)
  exact apply_le_mul_productSeminorm (productSeminorm A V W) fs hC hpure u

private theorem productSeminorm_comm_le (u : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W u) ≤ productSeminorm A V W u := by
  simpa using apply_le_mul_productSeminorm (productSeminorm A W V)
    (TensorProduct.comm A V W).toLinearMap.toAddMonoidHom zero_le_one
    (fun v w ↦ by simpa [mul_comm ‖v‖] using productSeminorm_tmul_le (A := A) w v) u

/-- Swapping tensor factors preserves `productSeminorm`. -/
@[simp]
theorem productSeminorm_comm (u : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W u) = productSeminorm A V W u :=
  (productSeminorm_comm_le u).antisymm
    (by simpa using productSeminorm_comm_le (TensorProduct.comm A V W u))

/-- When the left factor is a subsingleton, `productSeminorm` vanishes identically. -/
@[simp]
theorem productSeminorm_eq_zero_of_subsingleton_left [Subsingleton V] (u : V ⊗[A] W) :
    productSeminorm A V W u = 0 := by
  refine le_antisymm ?_ (apply_nonneg _ _)
  have hu : u = ∑ _ ∈ (∅ : Finset Unit), (0 : V) ⊗ₜ[A] (0 : W) :=
    Subsingleton.elim _ _
  rw [hu]
  exact productSeminorm_sum_tmul_le ∅ (fun _ ↦ 0) (fun _ ↦ 0) le_rfl (by simp)

/-- When the right factor is a subsingleton, `productSeminorm` vanishes identically. -/
@[simp]
theorem productSeminorm_eq_zero_of_subsingleton_right [Subsingleton W] (u : V ⊗[A] W) :
    productSeminorm A V W u = 0 := by
  rw [← productSeminorm_comm, productSeminorm_eq_zero_of_subsingleton_left]

/-- On `R ⊗[R] M` for an ultrametric `R`-module `M` with contractive action over a seminormed
commutative ring with `‖1‖ = 1`, `productSeminorm` equals the norm of the image in `M`. -/
@[simp]
theorem productSeminorm_eq_norm_lid {R M : Type*} [SeminormedCommRing R] [NormOneClass R]
    [SeminormedAddCommGroup M] [IsUltrametricDist M] [Module R M] [IsBoundedSMul R M]
    (u : R ⊗[R] M) :
    productSeminorm R R M u = ‖TensorProduct.lid R M u‖ := by
  refine le_antisymm ?_ ?_
  · calc productSeminorm R R M u
        = productSeminorm R R M ((1 : R) ⊗ₜ[R] TensorProduct.lid R M u) := by
          rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
      _ ≤ ‖(1 : R)‖ * ‖TensorProduct.lid R M u‖ := productSeminorm_tmul_le _ _
      _ = ‖TensorProduct.lid R M u‖ := by rw [norm_one, one_mul]
  · let p : NonarchAddGroupSeminorm M :=
      { toFun := norm
        map_zero' := norm_zero
        add_le_max' := IsUltrametricDist.isNonarchimedean_norm
        neg' := norm_neg }
    have hp := apply_le_mul_productSeminorm p (TensorProduct.lid R M).toLinearMap.toAddMonoidHom
      zero_le_one (fun (r : R) (m : M) ↦ by
        change ‖r • m‖ ≤ 1 * (‖r‖ * ‖m‖)
        simpa using norm_smul_le r m) u
    change ‖TensorProduct.lid R M u‖ ≤ 1 * productSeminorm R R M u at hp
    linarith

/-- On `M ⊗[R] R` for an ultrametric `R`-module `M` with contractive action over a seminormed
commutative ring with `‖1‖ = 1`, `productSeminorm` equals the norm of the image in `M`. -/
@[simp]
theorem productSeminorm_eq_norm_rid {R M : Type*} [SeminormedCommRing R] [NormOneClass R]
    [SeminormedAddCommGroup M] [IsUltrametricDist M] [Module R M] [IsBoundedSMul R M]
    (u : M ⊗[R] R) :
    productSeminorm R M R u = ‖TensorProduct.rid R M u‖ := by
  rw [← productSeminorm_comm, productSeminorm_eq_norm_lid, ← TensorProduct.comm_trans_lid,
    LinearEquiv.trans_apply]

/-- In `R ⊗[R] R` for an ultrametric seminormed commutative ring with `‖1‖ = 1`, the product
seminorm of `1 ⊗ₜ c + d ⊗ₜ 1` is `‖c + d‖` (in particular `0` when `d = -c`). -/
theorem productSeminorm_one_tmul_add_tmul_one {R : Type*} [SeminormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] (c d : R) :
    productSeminorm R R R ((1 : R) ⊗ₜ[R] c + d ⊗ₜ[R] (1 : R)) = ‖c + d‖ := by
  simp

end Algebraic

section TensorTopology

/-- `productSeminorm A V W` viewed as an `AddGroupSeminorm` on `V ⊗[A] W`. -/
@[expose]
noncomputable def productAddGroupSeminorm (A V W : Type*) [CommRing A]
    [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W] :
    AddGroupSeminorm (V ⊗[A] W) where
  toFun := productSeminorm A V W
  map_zero' := map_zero _
  add_le' := map_add_le_add _
  neg' := map_neg_eq_map _

/-- The `SeminormedAddCommGroup` structure on `V ⊗[A] W` defined by `productSeminorm A V W`.
This is not an instance: see note [reducible non-instances]. -/
noncomputable abbrev productSeminormedAddCommGroup (A V W : Type*) [CommRing A]
    [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W] :
    SeminormedAddCommGroup (V ⊗[A] W) :=
  (productAddGroupSeminorm A V W).toSeminormedAddCommGroup

variable {A V W : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- If the action of `A` on `V` is bounded, the tensor topology on `V ⊗[A] W` is finer than the
topology induced by `productSeminorm A V W`. -/
theorem banachTensorTopology_le_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    banachTensorTopology A V W ≤
      (productSeminormedAddCommGroup A V W).toUniformSpace.toTopologicalSpace := by
  let : SeminormedAddCommGroup (V ⊗[A] W) := productSeminormedAddCommGroup A V W
  have : IsUltrametricDist (V ⊗[A] W) :=
    .isUltrametricDist_of_isNonarchimedean_norm (map_add_le_max (productSeminorm A V W))
  have hsmul : ContinuousSMul A (V ⊗[A] W) := by
    obtain ⟨C, hC⟩ := hV
    refine TauCeti.continuousSMul_of_norm_smul_le ⟨C, fun a u ↦ ?_⟩
    exact productSeminorm_smul_le (by positivity) (fun v ↦ hC a v) u
  have htmul : Continuous fun p : V × W ↦ p.1 ⊗ₜ[A] p.2 :=
    (TensorProduct.mk A V W).continuous₂_of_bound 1 fun v w ↦ by
      change productSeminorm A V W (v ⊗ₜ[A] w) ≤ 1 * ‖v‖ * ‖w‖
      simpa using productSeminorm_tmul_le (A := A) v w
  exact banachTensorTopology_le IsUltrametricDist.nonarchimedeanAddGroup hsmul htmul

/-- If the action of `A` on `V` is bounded, `productSeminorm A V W` is uniformly continuous for
`banachTensorUniformSpace A V W`. -/
theorem uniformContinuous_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    UniformContinuous[banachTensorUniformSpace A V W, _] (productSeminorm A V W) := by
  have hnhds : @nhds _ (banachTensorTopology A V W) 0 ≤
      @nhds _ (productSeminormedAddCommGroup A V W).toUniformSpace.toTopologicalSpace 0 :=
    nhds_mono (banachTensorTopology_le_productSeminorm hV)
  have hle : 𝓤[banachTensorUniformSpace A V W] ≤
      𝓤[(productSeminormedAddCommGroup A V W).toUniformSpace] := by
    rw [@uniformity_eq_comap_nhds_zero _ (banachTensorUniformSpace A V W) _
      (@IsUniformAddGroup.isRightUniformAddGroup _ (banachTensorUniformSpace A V W) _
        (isUniformAddGroup_banachTensorUniformSpace A V W)),
      @uniformity_eq_comap_nhds_zero _ (productSeminormedAddCommGroup A V W).toUniformSpace _
      (@IsUniformAddGroup.isRightUniformAddGroup _
        (productSeminormedAddCommGroup A V W).toUniformSpace _
        (productSeminormedAddCommGroup A V W).to_isUniformAddGroup),
      banachTensorUniformSpace_toTopologicalSpace]
    exact Filter.comap_mono hnhds
  exact (@uniformContinuous_norm _
    (productSeminormedAddCommGroup A V W).toSeminormedAddGroup).mono_left hle

/-- Auxiliary balancing estimate: for `0 < q < 1` and `0 < x`, if
`x * y < q * η₁ * η₂ / (2 * M₁ * M₂)`, some integer power `q ^ n` simultaneously makes
`M₁ * q ^ n * x < η₁` and `M₂ * q ^ (-n) * y < η₂`. -/
private theorem exists_int_zpow_mul_lt {q M₁ M₂ η₁ η₂ x y : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (hx : 0 < x)
    (hxy : x * y < q * η₁ * η₂ / (2 * M₁ * M₂)) :
    ∃ n : ℤ, M₁ * q ^ n * x < η₁ ∧ M₂ * q ^ (-n) * y < η₂ := by
  obtain ⟨n, ⟨hn₁, hn₂⟩, -⟩ :=
    existsUnique_zpow_mul_mem_Ioc hq0 hq1 (mul_pos (div_pos (by positivity : 0 < 2 * M₁) hη₁) hx)
  refine ⟨n, ?_, ?_⟩
  · have hle : q ^ n * (2 * M₁ * x) ≤ η₁ := by
      have hmul := mul_le_mul_of_nonneg_left hn₂ hη₁.le
      have hsimp : η₁ * (q ^ n * (2 * M₁ / η₁ * x)) = q ^ n * (2 * M₁ * x) := by field_simp
      linarith
    linarith
  · rw [zpow_neg]
    have hqn : 0 < q ^ n := zpow_pos hq0 n
    have hxy' : 2 * M₁ * M₂ * (x * y) < q * η₁ * η₂ :=
      (lt_div_iff₀ (by positivity)).1 hxy |>.trans_eq' (by ring)
    have hn₁' : q * η₁ < q ^ n * (2 * M₁ * x) := by
      have hmul := mul_lt_mul_of_pos_left hn₁ hη₁
      have hsimp : η₁ * (q ^ n * (2 * M₁ / η₁ * x)) = q ^ n * (2 * M₁ * x) := by field_simp
      linarith
    have hkey : (2 * M₁ * x) * (M₂ * y) < (2 * M₁ * x) * (q ^ n * η₂) := by
      have := mul_lt_mul_of_pos_right hn₁' hη₂
      linarith
    have hkey₂ : M₂ * y < q ^ n * η₂ := lt_of_mul_lt_mul_left hkey (by positivity)
    refine lt_of_mul_lt_mul_left ?_ hqn.le
    have hsimp : q ^ n * (M₂ * (q ^ n)⁻¹ * y) = M₂ * y := by field_simp
    linarith

/-- Over a Tate seminormed ring `A`, a pure tensor `v ⊗ₜ w` with small norm product `‖v‖ * ‖w‖`
can be rescaled as `(ϖ ^ n • v) ⊗ₜ (ϖ ^ (-n) • w)` so that both factors lie in prescribed balls. -/
private theorem tmul_mem_of_norm_mul_lt (ϖ : TauCeti.NormedRing.PseudoUniformizer A)
    {C₁ C₂ : ℝ≥0} (hC₁ : ∀ (a : A) (v : V), ‖a • v‖ ≤ C₁ * ‖a‖ * ‖v‖)
    (hC₂ : ∀ (a : A) (w : W), ‖a • w‖ ≤ C₂ * ‖a‖ * ‖w‖)
    {O : Set (V ⊗[A] W)} {η₁ η₂ : ℝ} (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (hO : ∀ {v : V} {w : W}, ‖v‖ < η₁ → ‖w‖ < η₂ → v ⊗ₜ[A] w ∈ O)
    {v : V} {w : W}
    (hvw : ‖v‖ * ‖w‖ <
      ‖(ϖ.unit : A)‖ * η₁ * η₂ / (2 * max (C₁ : ℝ) 1 * max (C₂ : ℝ) 1)) :
    v ⊗ₜ[A] w ∈ O := by
  set q := ‖(ϖ.unit : A)‖
  have hq0 : 0 < q := ϖ.norm_pos
  have hq1 : q < 1 := ϖ.norm_lt_one
  set M₁ : ℝ := max (C₁ : ℝ) 1
  set M₂ : ℝ := max (C₂ : ℝ) 1
  have hM₁ : 0 < M₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbalance (n : ℤ) :
      (((ϖ.unit ^ n : Aˣ) : A) • v) ⊗ₜ[A] (((ϖ.unit ^ (-n) : Aˣ) : A) • w) = v ⊗ₜ[A] w := by
    rw [TensorProduct.smul_tmul, smul_smul, ← Units.val_mul, ← zpow_add, add_neg_cancel,
      zpow_zero, Units.val_one, one_smul]
  have hb₁ (n : ℤ) : ‖((ϖ.unit ^ n : Aˣ) : A) • v‖ ≤ M₁ * q ^ n * ‖v‖ := by
    refine (hC₁ _ v).trans ?_
    rw [ϖ.norm_zpow]
    gcongr
    exact le_max_left _ _
  have hb₂ (n : ℤ) : ‖((ϖ.unit ^ (-n) : Aˣ) : A) • w‖ ≤ M₂ * q ^ (-n) * ‖w‖ := by
    refine (hC₂ _ w).trans ?_
    rw [ϖ.norm_zpow]
    gcongr
    exact le_max_left _ _
  rcases (norm_nonneg v).eq_or_lt with hv0 | hv0
  · rcases (norm_nonneg w).eq_or_lt with hw0 | hw0
    · exact hO (by linarith) (by linarith)
    · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hη₂ (mul_pos hM₂ hw0)) hq1
      rw [← hbalance (-(m : ℤ))]
      refine hO ?_ ?_
      · exact (hb₁ _).trans_lt (by rw [← hv0, mul_zero]; exact hη₁)
      · refine (hb₂ _).trans_lt ?_
        rw [neg_neg, zpow_natCast]
        have := (lt_div_iff₀ (mul_pos hM₂ hw0)).1 hm
        linarith
  · obtain ⟨n, hn₁, hn₂⟩ := exists_int_zpow_mul_lt hq0 hq1 hM₁ hM₂ hη₁ hη₂ hv0 hvw
    rw [← hbalance n]
    exact hO ((hb₁ n).trans_lt hn₁) ((hb₂ n).trans_lt hn₂)

/-- **Agreement of the tensor topology with the product seminorm.** Over a Tate seminormed
commutative ring `A`, if both `V` and `W` have bounded `A`-actions, `banachTensorTopology A V W`
is the topology induced by `productSeminorm A V W`. -/
theorem banachTensorTopology_eq_productSeminorm [TauCeti.NormedRing.IsTate A]
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorTopology A V W =
      (productSeminormedAddCommGroup A V W).toUniformSpace.toTopologicalSpace := by
  let t₁ := (productSeminormedAddCommGroup A V W).toUniformSpace.toTopologicalSpace
  let t₂ := banachTensorTopology A V W
  have hg₁ : @IsTopologicalAddGroup (V ⊗[A] W) t₁ _ :=
    @IsUniformAddGroup.isTopologicalAddGroup _
      (productSeminormedAddCommGroup A V W).toUniformSpace _
      (productSeminormedAddCommGroup A V W).to_isUniformAddGroup
  have hg₂ : @IsTopologicalAddGroup (V ⊗[A] W) t₂ _ :=
    (nonarchimedeanAddGroup_banachTensorTopology A V W).toIsTopologicalAddGroup
  refine IsTopologicalAddGroup.ext hg₂ hg₁
    (le_antisymm (nhds_mono (banachTensorTopology_le_productSeminorm hV)) ?_)
  intro U hU
  obtain ⟨ϖ⟩ := TauCeti.NormedRing.IsTate.nonempty_pseudoUniformizer (R := A)
  obtain ⟨C₁, hC₁⟩ := hV
  obtain ⟨C₂, hC₂⟩ := hW
  obtain ⟨O, hOU⟩ := @NonarchimedeanAddGroup.is_nonarchimedean _ _ t₂
    (nonarchimedeanAddGroup_banachTensorTopology A V W) U hU
  have hcont := (continuous_tmul_banachTensorTopology A V W).tendsto ((0 : V), (0 : W))
  have hO₀ : (O : Set (V ⊗[A] W)) ∈ @nhds _ t₂ (0 ⊗ₜ[A] 0) := by
    simpa using O.isOpen.mem_nhds O.zero_mem
  obtain ⟨B₁, hB₁, B₂, hB₂, hB₁₂⟩ := mem_nhds_prod_iff.mp (hcont hO₀)
  obtain ⟨η₁, hη₁, hη₁B⟩ := Metric.mem_nhds_iff.mp hB₁
  obtain ⟨η₂, hη₂, hη₂B⟩ := Metric.mem_nhds_iff.mp hB₂
  let δ := ‖(ϖ.unit : A)‖ * η₁ * η₂ / (2 * max (C₁ : ℝ) 1 * max (C₂ : ℝ) 1)
  have hδ : 0 < δ := by
    have := ϖ.norm_pos
    have : (0 : ℝ) < max (C₁ : ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have : (0 : ℝ) < max (C₂ : ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    positivity
  let : SeminormedAddCommGroup (V ⊗[A] W) := productSeminormedAddCommGroup A V W
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : V ⊗[A] W) hδ) fun u hu ↦ hOU ?_
  have hu' : productSeminorm A V W u < δ := by
    rw [Metric.mem_ball, dist_zero_right] at hu
    exact hu
  obtain ⟨n, v, w, rfl, hvw⟩ := exists_sum_tmul_eq_of_productSeminorm_lt hu'
  refine O.toAddSubgroup.sum_mem fun i _ ↦ ?_
  exact tmul_mem_of_norm_mul_lt ϖ hC₁ hC₂ hη₁ hη₂
    (fun hv hw ↦ hB₁₂ (Set.mk_mem_prod (hη₁B (by simpa [Metric.mem_ball] using hv))
      (hη₂B (by simpa [Metric.mem_ball] using hw)))) (hvw i)

/-- **Positive-radius balls of `productSeminorm` form a neighbourhood basis of `0`** for
`banachTensorTopology A V W` over a Tate seminormed commutative ring `A`. -/
theorem hasBasis_banachTensorTopology [TauCeti.NormedRing.IsTate A]
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (@nhds _ (banachTensorTopology A V W) 0).HasBasis ((0 : ℝ) < ·)
      fun r ↦ {u | productSeminorm A V W u < r} := by
  rw [banachTensorTopology_eq_productSeminorm hV hW]
  let : SeminormedAddCommGroup (V ⊗[A] W) := productSeminormedAddCommGroup A V W
  exact Metric.nhds_basis_ball.congr (fun _ ↦ Iff.rfl) fun r _ ↦ by
    ext u
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    rfl

/-- **Agreement of the tensor uniformity with the product seminorm.** Over a Tate seminormed
commutative ring `A`, if both `V` and `W` have bounded `A`-actions,
`banachTensorUniformSpace A V W` is the uniformity induced by `productSeminorm A V W`. -/
theorem banachTensorUniformSpace_eq_productSeminorm [TauCeti.NormedRing.IsTate A]
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorUniformSpace A V W =
      (productSeminormedAddCommGroup A V W).toUniformSpace :=
  (isUniformAddGroup_banachTensorUniformSpace A V W).ext
    (productSeminormedAddCommGroup A V W).to_isUniformAddGroup <| by
      rw [banachTensorUniformSpace_toTopologicalSpace,
        banachTensorTopology_eq_productSeminorm hV hW]

end TensorTopology

namespace CompletedTensor

section Extension

variable (A V W : Type*) [CommRing A] [TopologicalSpace A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- **The product norm on the completed tensor product** `V ⊗̂_A W`: the continuous extension of
`productSeminorm A V W` along the completion of `banachTensorUniformSpace A V W`. -/
noncomputable def productNorm : CompletedTensor A V W → ℝ :=
  letI : UniformSpace (V ⊗[A] W) := banachTensorUniformSpace A V W
  fun z ↦ Completion.extension ⇑(productSeminorm A V W) (equivCompletion A V W z)

/-- `productNorm A V W` is uniformly continuous on `V ⊗̂_A W`. -/
@[fun_prop]
theorem uniformContinuous_productNorm : UniformContinuous (productNorm A V W) := by
  let : UniformSpace (V ⊗[A] W) := banachTensorUniformSpace A V W
  exact Completion.uniformContinuous_extension.comp (uniformContinuous_equivCompletion A V W)

/-- `productNorm A V W` is continuous on `V ⊗̂_A W`. -/
@[fun_prop]
theorem continuous_productNorm : Continuous (productNorm A V W) :=
  (uniformContinuous_productNorm A V W).continuous

end Extension

section BoundedLeft

variable {A V W : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- When the action of `A` on `V` is bounded, `productNorm` extends `productSeminorm` along
`toCompletion`. -/
@[simp]
theorem productNorm_toCompletion
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u := by
  let : UniformSpace (V ⊗[A] W) := banachTensorUniformSpace A V W
  change Completion.extension ⇑(productSeminorm A V W)
    (equivCompletion A V W (toCompletion A V W u)) = productSeminorm A V W u
  rw [equivCompletion_toCompletion]
  exact Completion.extension_coe (uniformContinuous_productSeminorm hV) u

/-- When the action of `A` on `V` is bounded, `productNorm` sends `0` to `0`. -/
theorem productNorm_zero (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    productNorm A V W 0 = 0 := by
  rw [← map_zero (toCompletion A V W), productNorm_toCompletion hV, map_zero]

/-- When the action of `A` on `V` is bounded, `productNorm` is nonnegative. -/
theorem productNorm_nonneg (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z : CompletedTensor A V W) : 0 ≤ productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le continuous_const (continuous_productNorm A V W)) fun u ↦ ?_
  rw [productNorm_toCompletion hV]
  exact apply_nonneg (productSeminorm A V W) u

/-- When the action of `A` on `V` is bounded, `productNorm` is invariant under negation. -/
theorem productNorm_neg (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z : CompletedTensor A V W) : productNorm A V W (-z) = productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq ((continuous_productNorm A V W).comp continuous_neg)
      (continuous_productNorm A V W)) fun u ↦ ?_
  rw [← map_neg, productNorm_toCompletion hV, productNorm_toCompletion hV, map_neg_eq_map]

/-- When the action of `A` on `V` is bounded, `productNorm` satisfies the strong triangle
inequality. -/
theorem productNorm_add_le_max (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (x y : CompletedTensor A V W) :
    productNorm A V W (x + y) ≤ max (productNorm A V W x) (productNorm A V W y) := by
  refine (denseRange_toCompletion A V W).induction_on x
    (isClosed_le ((continuous_productNorm A V W).comp (continuous_id.add continuous_const))
      ((continuous_productNorm A V W).max continuous_const)) fun u ↦ ?_
  refine (denseRange_toCompletion A V W).induction_on y
    (isClosed_le ((continuous_productNorm A V W).comp (continuous_const.add continuous_id))
      (continuous_const.max (continuous_productNorm A V W))) fun v ↦ ?_
  rw [← map_add, productNorm_toCompletion hV, productNorm_toCompletion hV,
    productNorm_toCompletion hV]
  exact map_add_le_max (productSeminorm A V W) u v

/-- When the action of `A` on `V` is bounded, `productNorm` on an elementary tensor is at most
`‖v‖ * ‖w‖`. -/
theorem productNorm_tmul_le (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (v : V) (w : W) : productNorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖ := by
  rw [← toCompletion_tmul, productNorm_toCompletion hV]
  exact productSeminorm_tmul_le v w

/-- When the action of `A` on `V` is bounded, `productNorm` on a finite sum of elementary tensors
is bounded by any nonnegative bound on the termwise norm products. -/
theorem productNorm_sum_tmul_le (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ s, ‖v i‖ * ‖w i‖ ≤ b) :
    productNorm A V W (∑ i ∈ s, tmul A V W (v i) (w i)) ≤ b := by
  have hsum : ∑ i ∈ s, tmul A V W (v i) (w i) = toCompletion A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) := by
    simp [map_sum]
  rw [hsum, productNorm_toCompletion hV]
  exact productSeminorm_sum_tmul_le s v w hb h

/-- If a continuous scalar action on `V` commuting with `A` scales norms by at most `C`, then its
extension to `CompletedTensor A V W` scales `productNorm A V W` by at most `C`. -/
theorem productNorm_smul_le (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    {S : Type*} [Monoid S] [DistribMulAction S V] [SMulCommClass A S V] [ContinuousConstSMul S V]
    {s : S} {C : ℝ} (hC : 0 ≤ C) (hs : ∀ v : V, ‖s • v‖ ≤ C * ‖v‖)
    (z : CompletedTensor A V W) :
    productNorm A V W (s • z) ≤ C * productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le ((continuous_productNorm A V W).comp (continuous_const_smul s))
      (continuous_const.mul (continuous_productNorm A V W))) fun u ↦ ?_
  rw [← toCompletion_smul, productNorm_toCompletion hV, productNorm_toCompletion hV]
  exact productSeminorm_smul_le hC hs u

/-- **Pointwise norm bound on continuous linear maps out of `V ⊗̂_A W` in terms of `productNorm`.**
When `A` acts boundedly on `V`, any continuous `A`-linear map `Φ : CompletedTensor A V W →L[A] M`
into an ultrametric seminormed `A`-module satisfying `‖Φ (tmul A V W v w)‖ ≤ C * ‖v‖ * ‖w‖`
(`0 ≤ C`) satisfies `‖Φ z‖ ≤ C * productNorm A V W z` for every `z`. -/
theorem norm_apply_le_mul_productNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    {M : Type*} [SeminormedAddCommGroup M] [IsUltrametricDist M] [Module A M]
    (Φ : CompletedTensor A V W →L[A] M)
    {C : ℝ} (hC : 0 ≤ C) (hΦ : ∀ v w, ‖Φ (tmul A V W v w)‖ ≤ C * ‖v‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    ‖Φ z‖ ≤ C * productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le (continuous_norm.comp Φ.continuous)
      (continuous_const.mul (continuous_productNorm A V W))) fun u ↦ ?_
  rw [productNorm_toCompletion hV]
  let p : NonarchAddGroupSeminorm M :=
    { toFun := norm
      map_zero' := norm_zero
      add_le_max' := IsUltrametricDist.isNonarchimedean_norm
      neg' := norm_neg }
  refine apply_le_mul_productSeminorm p
    (Φ.toLinearMap.comp (toCompletion A V W)).toAddMonoidHom hC (fun v w ↦ ?_) u
  change ‖Φ (toCompletion A V W (v ⊗ₜ[A] w))‖ ≤ C * (‖v‖ * ‖w‖)
  rw [toCompletion_tmul, ← mul_assoc]
  exact hΦ v w

/-- **Pointwise norm bound on `CompletedTensor.lift` in terms of `productNorm`.** When `A` acts
boundedly on `V`, a bilinear map `β : V →ₗ[A] W →ₗ[A] M` into a complete ultrametric normed
`A`-module with continuous action satisfying `‖β v w‖ ≤ C * ‖v‖ * ‖w‖` (`0 ≤ C`) satisfies
`‖lift β hβ z‖ ≤ C * productNorm A V W z` for every `z : CompletedTensor A V W`. -/
theorem norm_lift_le_mul_productNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [ContinuousSMul A M]
    (β : V →ₗ[A] W →ₗ[A] M) (hcont : Continuous fun p : V × W ↦ β p.1 p.2)
    {C : ℝ} (hC : 0 ≤ C) (hβ : ∀ v w, ‖β v w‖ ≤ C * ‖v‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    ‖lift β hcont z‖ ≤ C * productNorm A V W z :=
  norm_apply_le_mul_productNorm hV (lift β hcont) hC (fun v w ↦ by simpa using hβ v w) z

end BoundedLeft

private theorem exists_norm_smul_le {A M : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup M]
    [Module A M] [IsBoundedSMul A M] :
    ∃ C : ℝ≥0, ∀ (a : A) (m : M), ‖a • m‖ ≤ C * ‖a‖ * ‖m‖ :=
  ⟨1, fun a m ↦ by simpa using norm_smul_le a m⟩

section NormedStructure

variable {A V W : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]

/-- Positive-radius open balls of `productNorm A V W` form a neighbourhood basis of `0` in
`CompletedTensor A V W` when `A` is Tate and both actions are bounded. -/
theorem hasBasis_nhds_zero_productNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis ((0 : ℝ) < ·)
      fun r ↦ {z | productNorm A V W z < r} := by
  refine Filter.hasBasis_iff.mpr fun U ↦ ⟨fun hU ↦ ?_, fun ⟨r, hr0, hrU⟩ ↦ ?_⟩
  · obtain ⟨H, hHU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
    have hpre : (toCompletion A V W) ⁻¹' (H : Set (CompletedTensor A V W)) ∈
        @nhds _ (banachTensorTopology A V W) 0 := by
      let : TopologicalSpace (V ⊗[A] W) := banachTensorTopology A V W
      exact (continuous_toCompletion A V W).continuousAt
        (by simpa using H.isOpen.mem_nhds H.zero_mem)
    obtain ⟨r, hr0, hr⟩ := (hasBasis_banachTensorTopology hV hW).mem_iff.mp hpre
    refine ⟨r, hr0, fun z hzr ↦ hHU ?_⟩
    let S : Set (CompletedTensor A V W) :=
      {w | z - w ∈ (H : Set (CompletedTensor A V W)) ∧ productNorm A V W w < r}
    have hS_open : IsOpen S :=
      (H.isOpen.preimage (continuous_const.sub continuous_id)).inter
        (isOpen_lt (continuous_productNorm A V W) continuous_const)
    have hzS : z ∈ S := ⟨by simp, hzr⟩
    obtain ⟨_, ⟨⟨hwH, hwr⟩, u, rfl⟩⟩ :=
      (denseRange_toCompletion A V W).inter_open_nonempty S hS_open ⟨z, hzS⟩
    have huH : toCompletion A V W u ∈ (H : Set (CompletedTensor A V W)) :=
      hr (show productSeminorm A V W u < r by rwa [← productNorm_toCompletion hV])
    simpa using H.add_mem hwH huH
  · exact Filter.mem_of_superset
      ((isOpen_lt (continuous_productNorm A V W) continuous_const).mem_nhds
        (by simpa [productNorm_zero hV] using hr0)) hrU

/-- Over a Tate seminormed commutative ring `A` with bounded actions on `V` and `W`,
`productNorm A V W z = 0` if and only if `z = 0`. -/
theorem productNorm_eq_zero_iff
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    {z : CompletedTensor A V W} :
    productNorm A V W z = 0 ↔ z = 0 := by
  refine ⟨fun hz ↦ ?_, fun h ↦ h ▸ productNorm_zero hV⟩
  by_contra hz0
  obtain ⟨r, hr0, hr⟩ := (hasBasis_nhds_zero_productNorm hV hW).mem_iff.mp
    (compl_singleton_mem_nhds (Ne.symm hz0))
  exact hr (show productNorm A V W z < r from hz ▸ hr0) rfl

/-- `productNorm A V W` viewed as an `AddGroupNorm` on `CompletedTensor A V W` when `A` is Tate and
both scalar actions are bounded. -/
noncomputable def productAddGroupNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    AddGroupNorm (CompletedTensor A V W) where
  toFun := productNorm A V W
  map_zero' := productNorm_zero hV
  add_le' x y := (productNorm_add_le_max hV x y).trans (max_le_add_of_nonneg
    (productNorm_nonneg hV x) (productNorm_nonneg hV y))
  neg' := productNorm_neg hV
  eq_zero_of_map_eq_zero' _ := (productNorm_eq_zero_iff hV hW).mp

/-- Over a Tate seminormed commutative ring `A` with bounded actions on `V` and `W`, the uniformity
of `CompletedTensor A V W` agrees with the metric uniformity of `productAddGroupNorm hV hW`. -/
theorem uniformity_eq_productAddGroupNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    𝓤[(inferInstance : UniformSpace (CompletedTensor A V W))] =
      𝓤[(productAddGroupNorm hV hW).toNormedAddCommGroup.toUniformSpace] := by
  let g := (productAddGroupNorm hV hW).toNormedAddCommGroup
  have hbasis₂ : (@nhds _ g.toUniformSpace.toTopologicalSpace 0).HasBasis ((0 : ℝ) < ·)
      fun r ↦ {z | productNorm A V W z < r} := by
    let : NormedAddCommGroup (CompletedTensor A V W) := g
    exact Metric.nhds_basis_ball.congr (fun _ ↦ Iff.rfl) fun r _ ↦ by
      ext z
      simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
      rfl
  exact congrArg (@UniformSpace.uniformity _)
    (IsUniformAddGroup.ext inferInstance g.toSeminormedAddCommGroup.to_isUniformAddGroup
      ((hasBasis_nhds_zero_productNorm hV hW).eq_of_same_basis hbasis₂))

/-- Over a Tate seminormed commutative ring `A` with bounded actions on `V` and `W`, the uniformity
of `CompletedTensor A V W` has the standard metric description in terms of `productNorm A V W`. -/
theorem uniformity_productNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    𝓤[(inferInstance : UniformSpace (CompletedTensor A V W))] =
      ⨅ ε > 0, Filter.principal {p : CompletedTensor A V W × CompletedTensor A V W |
        productNorm A V W (-p.1 + p.2) < ε} := by
  exact (uniformity_eq_productAddGroupNorm hV hW).trans
    (productAddGroupNorm hV hW).toNormedAddCommGroup.uniformity_dist

/-- **Ultrametric norm on `CompletedTensor A V W` for bounded scalar actions.** Over a Tate
seminormed commutative ring `A`, bounded scalar actions `hV` and `hW` equip `CompletedTensor A V W`
with a `NormedAddCommGroup` structure whose norm is `productNorm A V W` and whose underlying
`UniformSpace` and `AddCommGroup` are definitionally those of `CompletedTensor A V W`. This is not
an instance: see note [reducible non-instances]; for contractive actions (`IsBoundedSMul`), the
global `NormedAddCommGroup` instance below applies automatically. -/
noncomputable abbrev normedAddCommGroupOfBoundedSMul
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    NormedAddCommGroup (CompletedTensor A V W) where
  toAddCommGroup := inferInstance
  norm := productNorm A V W
  dist x y := productNorm A V W (-x + y)
  dist_self x := by rw [neg_add_cancel, productNorm_zero hV]
  dist_comm x y := by rw [← productNorm_neg hV (-x + y), neg_add_rev, neg_neg, add_comm]
  dist_triangle x y z := by
    simpa [add_assoc] using (productNorm_add_le_max hV (-x + y) (-y + z)).trans
      (max_le_add_of_nonneg (productNorm_nonneg hV _) (productNorm_nonneg hV _))
  edist x y := ENNReal.ofReal (productNorm A V W (-x + y))
  edist_dist _ _ := rfl
  toUniformSpace := inferInstance
  uniformity_dist := uniformity_productNorm hV hW
  eq_of_dist_eq_zero {x y} h := neg_add_eq_zero.mp ((productNorm_eq_zero_iff hV hW).mp h)
  dist_eq _ _ := rfl

/-- The norm of `normedAddCommGroupOfBoundedSMul` is `productNorm A V W`. -/
theorem norm_normedAddCommGroupOfBoundedSMul
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    (letI := normedAddCommGroupOfBoundedSMul hV hW; ‖z‖) = productNorm A V W z :=
  rfl

/-- The norm of `normedAddCommGroupOfBoundedSMul` is ultrametric. -/
theorem isUltrametricDist_normedAddCommGroupOfBoundedSMul
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    letI := normedAddCommGroupOfBoundedSMul hV hW
    IsUltrametricDist (CompletedTensor A V W) :=
  let := normedAddCommGroupOfBoundedSMul hV hW
  .isUltrametricDist_of_isNonarchimedean_norm (productNorm_add_le_max hV)

/-- Over a Tate seminormed commutative ring `A` with bounded actions on `V` and `W`, any
seminormed commutative ring `S` acting boundedly on `V` and commuting with `A` acts jointly
continuously on `CompletedTensor A V W`. -/
theorem continuousSMul_of_boundedSMul
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    {S : Type*} [SeminormedCommRing S] [Module S V] [SMulCommClass A S V]
    (hS : ∃ C : ℝ≥0, ∀ (s : S) (v : V), ‖s • v‖ ≤ C * ‖s‖ * ‖v‖) :
    haveI := TauCeti.continuousSMul_of_norm_smul_le hS
    ContinuousSMul S (CompletedTensor A V W) := by
  have := TauCeti.continuousSMul_of_norm_smul_le hS
  let := normedAddCommGroupOfBoundedSMul hV hW
  obtain ⟨C, hC⟩ := hS
  exact TauCeti.continuousSMul_of_norm_smul_le
    ⟨C, fun s z ↦ productNorm_smul_le hV (by positivity) (hC s) z⟩

section Contractive

variable [IsBoundedSMul A V] [IsBoundedSMul A W]

/-- **Complete ultrametric Banach-module norm on `V ⊗̂_A W`** for contractive scalar actions over a
Tate seminormed commutative ring `A`. Its underlying `UniformSpace` and `AddCommGroup` agree
definitionally with those of `CompletedTensor A V W`. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (CompletedTensor A V W) :=
  normedAddCommGroupOfBoundedSMul
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

instance instIsUltrametricDist : IsUltrametricDist (CompletedTensor A V W) := by
  exact isUltrametricDist_normedAddCommGroupOfBoundedSMul exists_norm_smul_le exists_norm_smul_le

/-- The norm on `CompletedTensor A V W` is `productNorm A V W`. -/
theorem norm_def (z : CompletedTensor A V W) : ‖z‖ = productNorm A V W z :=
  rfl

/-- The canonical completion map `V ⊗[A] W → V ⊗̂_A W` sends `u` to an element of norm
`productSeminorm A V W u`. -/
@[simp]
theorem norm_toCompletion (u : V ⊗[A] W) :
    ‖toCompletion A V W u‖ = productSeminorm A V W u := by
  exact productNorm_toCompletion exists_norm_smul_le u

/-- An elementary tensor in `V ⊗̂_A W` has norm at most the product of the norms of its factors. -/
theorem norm_tmul_le (v : V) (w : W) : ‖tmul A V W v w‖ ≤ ‖v‖ * ‖w‖ := by
  exact productNorm_tmul_le exists_norm_smul_le v w

/-- A finite sum of elementary tensors in `V ⊗̂_A W` has norm bounded by any nonnegative bound on
its termwise norm products. -/
theorem norm_sum_tmul_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ s, ‖v i‖ * ‖w i‖ ≤ b) :
    ‖∑ i ∈ s, tmul A V W (v i) (w i)‖ ≤ b := by
  exact productNorm_sum_tmul_le exists_norm_smul_le s v w hb h

instance (priority := low) instIsBoundedSMulLeft {S : Type*} [SeminormedRing S] [Module S V]
    [SMulCommClass A S V] [IsBoundedSMul S V] : IsBoundedSMul S (CompletedTensor A V W) :=
  IsBoundedSMul.of_norm_smul_le fun s z ↦
    productNorm_smul_le exists_norm_smul_le (norm_nonneg s) (norm_smul_le s) z

instance instIsBoundedSMul : IsBoundedSMul A (CompletedTensor A V W) :=
  IsBoundedSMul.of_norm_smul_le fun a z ↦ by
    refine (denseRange_toCompletion A V W).induction_on z
      (isClosed_le (continuous_norm.comp (continuous_const_smul a))
        (continuous_const.mul continuous_norm)) fun u ↦ ?_
    rw [← map_smul, norm_toCompletion, norm_toCompletion]
    exact productSeminorm_smul_le (norm_nonneg a) (norm_smul_le a) u

/-- If `V` is a normed space over a normed field `K` whose action commutes with `A`, then
`V ⊗̂_A W` is a normed `K`-space. -/
noncomputable instance (priority := low) instNormedSpaceLeft {K : Type*} [NormedField K]
    [NormedSpace K V] [SMulCommClass A K V] : NormedSpace K (CompletedTensor A V W) where
  norm_smul_le := norm_smul_le

/-- **Pointwise norm bound on continuous linear maps out of `V ⊗̂_A W`.** Any continuous `A`-linear
map `Φ : CompletedTensor A V W →L[A] M` into an ultrametric seminormed `A`-module satisfying
`‖Φ (tmul A V W v w)‖ ≤ C * ‖v‖ * ‖w‖` (`0 ≤ C`) satisfies `‖Φ z‖ ≤ C * ‖z‖`. -/
theorem norm_apply_le {M : Type*} [SeminormedAddCommGroup M] [IsUltrametricDist M] [Module A M]
    (Φ : CompletedTensor A V W →L[A] M)
    {C : ℝ} (hC : 0 ≤ C) (hΦ : ∀ v w, ‖Φ (tmul A V W v w)‖ ≤ C * ‖v‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    ‖Φ z‖ ≤ C * ‖z‖ := by
  exact norm_apply_le_mul_productNorm exists_norm_smul_le Φ hC hΦ z

/-- **Pointwise norm bound on `CompletedTensor.lift`.** A bilinear map `β : V →ₗ[A] W →ₗ[A] M` into
a complete ultrametric normed `A`-module with continuous action satisfying `‖β v w‖ ≤ C * ‖v‖ * ‖w‖`
(`0 ≤ C`) satisfies `‖lift β hβ z‖ ≤ C * ‖z‖`. -/
theorem norm_lift_le {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [ContinuousSMul A M] (β : V →ₗ[A] W →ₗ[A] M)
    (hcont : Continuous fun p : V × W ↦ β p.1 p.2)
    {C : ℝ} (hC : 0 ≤ C) (hβ : ∀ v w, ‖β v w‖ ≤ C * ‖v‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    ‖lift β hcont z‖ ≤ C * ‖z‖ := by
  exact norm_lift_le_mul_productNorm exists_norm_smul_le β hcont hC hβ z

/-- **Pointwise norm bound on `CompletedTensor.map`.** If `‖f v‖ ≤ C₁ * ‖v‖` and
`‖g w‖ ≤ C₂ * ‖w‖` (with `0 ≤ C₁`, `0 ≤ C₂`), then `‖map f g z‖ ≤ (C₁ * C₂) * ‖z‖`. -/
theorem norm_map_le {V' W' : Type*} [SeminormedAddCommGroup V'] [Module A V']
    [IsBoundedSMul A V'] [SeminormedAddCommGroup W'] [Module A W'] [IsBoundedSMul A W']
    (f : V →L[A] V') (g : W →L[A] W') {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (z : CompletedTensor A V W) :
    ‖map f g z‖ ≤ C₁ * C₂ * ‖z‖ := by
  refine norm_apply_le (map f g) (by positivity) (fun v w ↦ ?_) z
  rw [map_tmul]
  refine (norm_tmul_le (f v) (g w)).trans ?_
  have := mul_le_mul (hf v) (hg w) (norm_nonneg _) (by positivity)
  linarith

end Contractive

end NormedStructure

section Lid

variable {A M : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
  [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M] [Module A M] [IsBoundedSMul A M]

/-- The unit isomorphism `lid A M : A ⊗̂_A M ≃L[A] M` is an isometry on a complete ultrametric
normed `A`-module `M` with contractive action. -/
theorem isometry_lid : Isometry (lid A M) := by
  refine AddMonoidHomClass.isometry_of_norm (lid A M).toLinearEquiv.toAddMonoidHom fun z ↦ ?_
  refine (denseRange_toCompletion A A M).induction_on z
    (isClosed_eq (continuous_norm.comp (lid A M).continuous) continuous_norm) fun u ↦ ?_
  change ‖lid A M (toCompletion A A M u)‖ = ‖toCompletion A A M u‖
  rw [lid_toCompletion, norm_toCompletion, productSeminorm_eq_norm_lid]

variable (A M) in
/-- **The isometric unit equivalence** `A ⊗̂_A M ≃ₗᵢ[A] M` for a complete ultrametric normed
`A`-module `M` with contractive action over a Tate seminormed commutative ring `A`. -/
noncomputable def lidₗᵢ : CompletedTensor A A M ≃ₗᵢ[A] M :=
  { (lid A M).toLinearEquiv with
    norm_map' := fun z ↦ (isometry_lid (A := A) (M := M)).norm_map_of_map_zero (map_zero _) z }

@[simp]
theorem lidₗᵢ_tmul (a : A) (m : M) : lidₗᵢ A M (tmul A A M a m) = a • m :=
  lid_tmul A M a m

@[simp]
theorem lidₗᵢ_symm_apply (m : M) : (lidₗᵢ A M).symm m = tmul A A M 1 m :=
  lid_symm_apply A M m

end Lid

section NormedField

/-- Over a normed field `K` that is Tate (for instance any nontrivially normed field), `V ⊗̂_K W`
is a normed `K`-space. -/
noncomputable instance instNormedSpace {K V W : Type*} [NormedField K]
    [TauCeti.NormedRing.IsTate K] [SeminormedAddCommGroup V] [NormedSpace K V]
    [SeminormedAddCommGroup W] [NormedSpace K W] :
    NormedSpace K (CompletedTensor K V W) where
  norm_smul_le := norm_smul_le

/-- **Operator-norm bound on `CompletedTensor.lift`** over a nontrivially normed field `K`. -/
theorem opNorm_lift_le {K V W M : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup V] [NormedSpace K V] [SeminormedAddCommGroup W] [NormedSpace K W]
    [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M] [NormedSpace K M]
    (β : V →ₗ[K] W →ₗ[K] M) (hcont : Continuous fun p : V × W ↦ β p.1 p.2)
    {C : ℝ} (hC : 0 ≤ C) (hβ : ∀ v w, ‖β v w‖ ≤ C * ‖v‖ * ‖w‖) :
    ‖lift β hcont‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_lift_le β hcont hC hβ)

/-- **Operator-norm bound on `CompletedTensor.map`** over a nontrivially normed field `K`:
`‖f ⊗̂ g‖ ≤ ‖f‖ * ‖g‖`. -/
theorem opNorm_map_le {K V W V' W' : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup V] [NormedSpace K V] [SeminormedAddCommGroup W] [NormedSpace K W]
    [SeminormedAddCommGroup V'] [NormedSpace K V'] [SeminormedAddCommGroup W'] [NormedSpace K W']
    (f : V →L[K] V') (g : W →L[K] W') :
    ‖map f g‖ ≤ ‖f‖ * ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_map_le f g (norm_nonneg f) (norm_nonneg g) f.le_opNorm g.le_opNorm)

end NormedField

end CompletedTensor

end TauCeti.Huber.BanachModule
