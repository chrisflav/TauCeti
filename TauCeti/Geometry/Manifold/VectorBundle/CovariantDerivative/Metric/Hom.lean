/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.RankOne
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Induced Hom connections of metric connections

For connections on bundles `V` and `W`, this module records consequences of metric compatibility
for the induced connection on `Hom` bundles.

* If the connection on the Riemannian bundle `W` is metric and the sections `σ` of `W` and `τ`
  of `V` are parallel at `x`, then the matrix entry `⟪σ, (∇_v A) τ⟫` at `x` is the ordinary
  derivative of `y ↦ ⟪σ y, A y (τ y)⟫`
  (`CovariantDerivative.IsMetricCompatible.inner_hom_apply_eq_mvfderiv_inner`).
* If the connection on the Riemannian bundle `W` is metric, then any curried bilinear bundle map
  `B : V → Hom(W, W)` that is pointwise skew-adjoint in its last two arguments remains
  skew-adjoint after differentiating via `covV.hom (covW.hom covW)`
  (`CovariantDerivative.IsMetricCompatible.inner_hom_hom_of_skew`).
* If the connection on the Riemannian bundle `V` is metric, then the rank-one homomorphisms
  `v ↦ ⟪τ, v⟫ • σ` satisfy the Leibniz rule
  `∇(rankOne σ τ) = rankOne (∇σ) τ + rankOne σ (∇τ)`
  (`CovariantDerivative.IsMetricCompatible.hom_rankOne_apply`).
  In particular they are parallel wherever `σ` and `τ` are.

These are the comparisons for the frames and tensor symmetries induced on `Hom` bundles by metric
connections, following J. M. Lee, *Introduction to Riemannian Manifolds*, second edition,
Chapters 4–5.
-/

public section

open Bundle FiberBundle InnerProductSpace
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section InnerTarget

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle 1 G W I]
  [IsContMDiffRiemannianBundle I 1 G W]
  {covV : CovariantDerivative I F V} {covW : CovariantDerivative I G W}

/-- For a metric connection on the target, the matrix entries of the induced Hom connection
against sections parallel at `x` are the ordinary derivatives of the matrix entries. -/
theorem IsMetricCompatible.inner_hom_apply_eq_mvfderiv_inner (hcov : covW.IsMetricCompatible)
    {A : Π x : M, V x →L[ℝ] W x} {σ : Π x : M, W x} {τ : Π x : M, V x} {x : M}
    (hA : MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun z ↦ V z →L[ℝ] W z) y (A y)) x)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x)
    (hσ₀ : covW σ x = 0) (hτ₀ : covV τ x = 0) (v : TangentSpace I x) :
    ⟪σ x, covV.hom covW A x v (τ x)⟫_ℝ =
      mvfderiv I (fun y ↦ ⟪σ y, A y (τ y)⟫_ℝ) x v := by
  have hp := hcov.mvfderiv_inner_eq (fun _ ↦ v) hσ (hA.clm_bundle_apply hτ)
  simp only [hσ₀, zero_apply, inner_zero_left, zero_add] at hp
  rw [hom_apply covV covW hA hτ, hτ₀, zero_apply, map_zero, sub_zero]
  exact hp.symm

/-- Metric compatibility on `W` preserves skew-adjointness in the last two slots under the
twice-iterated induced connection `covV.hom (covW.hom covW)`. Differentiability of `B` at `x` is
not needed: where `B` is not differentiable, the induced connection vanishes. -/
theorem IsMetricCompatible.inner_hom_hom_of_skew (hcov : covW.IsMetricCompatible)
    {B : Π y : M, V y →L[ℝ] W y →L[ℝ] W y} {x : M}
    (hskew : ∀ y (u : V y) (w₁ w₂ : W y), ⟪B y u w₁, w₂⟫_ℝ = -⟪w₁, B y u w₂⟫_ℝ)
    (v : TangentSpace I x) (u : V x) (w₁ w₂ : W x) :
    ⟪covV.hom (covW.hom covW) B x v u w₁, w₂⟫_ℝ =
      -⟪w₁, covV.hom (covW.hom covW) B x v u w₂⟫_ℝ := by
  by_cases hB : MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] G →L[ℝ] G)
        (E := fun z ↦ V z →L[ℝ] W z →L[ℝ] W z) y (B y)) x
  · set U := extend F u
    set W₁ := extend G w₁
    set W₂ := extend G w₂
    have hUx : U x = u := extend_apply_self F u
    have hW₁x : W₁ x = w₁ := extend_apply_self G w₁
    have hW₂x : W₂ x = w₂ := extend_apply_self G w₂
    have hU : MDiffAt (T% U) x := mdifferentiableAt_extend I F u
    have hW₁ : MDiffAt (T% W₁) x := mdifferentiableAt_extend I G w₁
    have hW₂ : MDiffAt (T% W₂) x := mdifferentiableAt_extend I G w₂
    have hBUW₁ : MDiffAt (T% (fun y ↦ B y (U y) (W₁ y))) x :=
      (hB.clm_bundle_apply hU).clm_bundle_apply hW₁
    have hBUW₂ : MDiffAt (T% (fun y ↦ B y (U y) (W₂ y))) x :=
      (hB.clm_bundle_apply hU).clm_bundle_apply hW₂
    have heq : (fun y ↦ ⟪B y (U y) (W₁ y), W₂ y⟫_ℝ) =
        fun y ↦ ⟪(-(fun q ↦ B q (U q) (W₂ q))) y, W₁ y⟫_ℝ := by
      funext y
      rw [Pi.neg_apply, hskew y (U y) (W₁ y) (W₂ y), inner_neg_left, real_inner_comm]
    have hd₁ := hcov.mvfderiv_inner_eq (fun _ ↦ v) hBUW₁ hW₂
    have hd₂ := hcov.mvfderiv_inner_eq (fun _ ↦ v) (mdifferentiableAt_neg_section hBUW₂) hW₁
    rw [heq] at hd₁
    have hd := hd₁.symm.trans hd₂
    dsimp only at hd
    rw [Pi.neg_apply, covW.isCovariantDerivativeOnUniv.neg hBUW₂,
      neg_apply, inner_neg_left, inner_neg_left,
      hUx, hW₁x, hW₂x, hskew x u w₁ (covW W₂ x v)] at hd
    have h₁ := hom_hom_apply covV covW covW hB hU hW₁ v
    have h₂ := hom_hom_apply covV covW covW hB hU hW₂ v
    rw [hUx, hW₁x] at h₁
    rw [hUx, hW₂x] at h₂
    rw [h₁, h₂, inner_sub_left, inner_sub_left, inner_sub_right, inner_sub_right,
      hskew x (covV U x v) w₁ w₂, hskew x u (covW W₁ x v) w₂,
      real_inner_comm (B x u w₂) (covW W₁ x v),
      real_inner_comm (covW (fun y ↦ B y (U y) (W₂ y)) x v) w₁]
    linarith
  · simp [hom_eq_zero_of_not_mdifferentiableAt covV (covW.hom covW) hB]

end InnerTarget

section RankOne

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [fiberNorm : ∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [targetNorm : ∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W]
  {covV : CovariantDerivative I F V} {covW : CovariantDerivative I G W}

/-- For a metric connection on the source, the induced Hom connection satisfies the Leibniz
rule on rank-one homomorphisms `v ↦ ⟪τ, v⟫ • σ` formed from `C¹` sections. -/
theorem IsMetricCompatible.hom_rankOne_apply (hcov : covV.IsMetricCompatible)
    {σ : Π x : M, W x} {τ : Π x : M, V x} {x : M}
    (hσ : CMDiffAt 1 (T% σ) x) (hτ : CMDiffAt 1 (T% τ) x) (v : TangentSpace I x) :
    covV.hom covW (fun y ↦ rankOne ℝ (σ y) (τ y)) x v =
      rankOne ℝ (covW σ x v) (τ x) + rankOne ℝ (σ x) (covV τ x v) := by
  have hA := (hσ.rankOne_bundle hτ).mdifferentiableAt one_ne_zero
  have hσ' := hσ.mdifferentiableAt one_ne_zero
  have hτ' := hτ.mdifferentiableAt one_ne_zero
  ext u
  have hs : MDiffAt (T% (extend F u)) x := mdifferentiableAt_extend I F u
  have hfun : (fun y ↦ rankOne ℝ (σ y) (τ y) (extend F u y)) =
      (fun y ↦ ⟪τ y, extend F u y⟫_ℝ) • σ := by
    ext y
    simp
  have hp := hcov.mvfderiv_inner_eq (fun _ ↦ v) hτ' hs
  rw [hom_apply_eq_extend covV covW hA, hfun,
    covW.isCovariantDerivativeOnUniv.leibniz hσ' (hτ'.inner_bundle hs)]
  simp only [extend_apply_self] at hp
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    extend_apply_self, rankOne_apply, hp]
  module

/-- Rank-one homomorphisms formed from `C¹` sections parallel at `x` are parallel at `x` for
the induced Hom connection of a metric connection on the source. -/
theorem IsMetricCompatible.hom_rankOne_eq_zero (hcov : covV.IsMetricCompatible)
    {σ : Π x : M, W x} {τ : Π x : M, V x} {x : M}
    (hσ : CMDiffAt 1 (T% σ) x) (hτ : CMDiffAt 1 (T% τ) x)
    (hσ₀ : covW σ x = 0) (hτ₀ : covV τ x = 0) :
    covV.hom covW (fun y ↦ rankOne ℝ (σ y) (τ y)) x = 0 := by
  ext v : 1
  simp [hcov.hom_rankOne_apply hσ hτ, hσ₀, hτ₀]

end RankOne

end CovariantDerivative
