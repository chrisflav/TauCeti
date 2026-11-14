/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import TauCeti.RingTheory.Huber.BanachModule.ProductSeminorm

/-!
# Symmetry, right module structure, and base change for completed tensor products

This file develops symmetry, right scalar extension, functorial base change of continuous linear
maps, and transitivity of completed base change (`cancelBaseChange`) for
`TauCeti.Huber.BanachModule.CompletedTensor`.

## Main definitions

* `TauCeti.Huber.BanachModule.CompletedTensor.comm`: the continuous `A`-linear symmetry equivalence
  `V ⊗̂_A W ≃L[A] W ⊗̂_A V`, together with its contractive Banach-module isometric upgrade `commₗᵢ`.
* `TauCeti.Huber.BanachModule.CompletedTensor.rid`: the right unit equivalence
  `M ⊗̂_A A ≃L[A] M`, together with its contractive isometric upgrade `ridₗᵢ`.
* `TauCeti.Huber.BanachModule.CompletedTensor.RightModule`: scoped instances equipping `V ⊗̂_A W`
  with the right `S`-module structure induced from an `S`-action on `W` commuting with `A`, via
  transport along `comm A V W`, and the `S`-linear symmetry equivalence `commₛ` (`commₛₗᵢ`).
* `TauCeti.Huber.BanachModule.CompletedTensor.baseChange`: scalar extension
  `S ⊗̂_A W →L[S] S ⊗̂_A W'` of a continuous `A`-linear map `W →L[A] W'` along a topological
  `A`-algebra `S`.
* `TauCeti.Huber.BanachModule.CompletedTensor.cancelBaseChange` and `cancelBaseChangeₗᵢ`:
  transitivity of completed base change `M ⊗̂_A (A ⊗̂_R N) ≃L[B] M ⊗̂_R N` (and `≃ₗᵢ[B]`) over Tate
  seminormed commutative rings `R → A`.

## Main results

* `TauCeti.Huber.BanachModule.CompletedTensor.productNorm_comm` and `norm_comm`: symmetry of
  `productNorm` and of the Banach-module norm under `comm`.
* `TauCeti.Huber.BanachModule.CompletedTensor.tmul_smul'`: under `open scoped RightModule`,
  `s • tmul A V W v w = tmul A V W v (s • w)`.
* `TauCeti.Huber.BanachModule.CompletedTensor.map_smul_left`, `baseChange_tmul`, `baseChange_id`,
  `baseChange_comp`, `norm_baseChange_le`, `opNorm_baseChange_le`.
* `TauCeti.Huber.BanachModule.CompletedTensor.cancelBaseChange_tmul` and
  `cancelBaseChange_symm_tmul`.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren der mathematischen
  Wissenschaften 261, Springer, 1984, §2.1.7.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.1–2.2.
-/

public section

open scoped NNReal TensorProduct

namespace TauCeti.Huber.BanachModule.CompletedTensor

section CommAndRid

section Topological

variable {A V W : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup V] [Module A V] [TopologicalSpace V]
  [AddCommGroup W] [Module A W] [TopologicalSpace W]

variable (A V W) in
/-- **Symmetry of the completed tensor product**: the continuous `A`-linear equivalence
`V ⊗̂_A W ≃L[A] W ⊗̂_A V` exchanging the two factors (`comm_tmul`). -/
noncomputable def comm : CompletedTensor A V W ≃L[A] CompletedTensor A W V :=
  .equivOfInverse'
    (lift (tmul A W V).flip (((continuous_tmul A W V).comp continuous_swap).congr fun _ ↦ by simp))
    (lift (tmul A V W).flip (((continuous_tmul A V W).comp continuous_swap).congr fun _ ↦ by simp))
    (ext fun w v ↦ by simp) (ext fun v w ↦ by simp)

@[simp]
theorem comm_tmul (v : V) (w : W) :
    comm A V W (tmul A V W v w) = tmul A W V w v := by
  simp [comm]

@[simp]
theorem comm_symm : (comm A V W).symm = comm A W V :=
  ContinuousLinearEquiv.coe_inj.mp <| ext fun w v ↦ by
    change (comm A V W).symm (tmul A W V w v) = comm A W V (tmul A W V w v)
    rw [comm_tmul]
    exact (comm A V W).symm_apply_eq.mpr (comm_tmul v w).symm

@[simp]
theorem comm_comm (z : CompletedTensor A V W) :
    comm A W V (comm A V W z) = z := by
  rw [← comm_symm]
  exact (comm A V W).symm_apply_apply z

@[simp]
theorem comm_toCompletion (u : V ⊗[A] W) :
    comm A V W (toCompletion A V W u) = toCompletion A W V (TensorProduct.comm A V W u) := by
  induction u using TensorProduct.inductionOn with
  | tmul v w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `comm` intertwines `CompletedTensor.map f g` with `CompletedTensor.map g f`. -/
theorem comm_map {V' W' : Type*} [AddCommGroup V'] [Module A V'] [TopologicalSpace V']
    [AddCommGroup W'] [Module A W'] [TopologicalSpace W']
    (f : V →L[A] V') (g : W →L[A] W') (z : CompletedTensor A V W) :
    comm A V' W' (map f g z) = map g f (comm A V W z) := by
  suffices (comm A V' W').toContinuousLinearMap.comp (map f g) =
      (map g f).comp (comm A V W).toContinuousLinearMap from DFunLike.congr_fun this z
  exact ext fun v w ↦ by simp

variable (A) in
/-- **The right unit isomorphism** `M ⊗̂_A A ≃L[A] M` of a complete Hausdorff nonarchimedean
topological `A`-module `M` with continuous action: it sends `m ⊗ a` to `a • m` (`rid_tmul`), and
its inverse sends `m` to `m ⊗ 1` (`rid_symm_apply`). -/
noncomputable def rid (M : Type*) [AddCommGroup M] [Module A M] [UniformSpace M]
    [IsUniformAddGroup M] [NonarchimedeanAddGroup M] [ContinuousSMul A M] [CompleteSpace M]
    [T0Space M] :
    CompletedTensor A M A ≃L[A] M :=
  (comm A M A).trans (lid A M)

@[simp]
theorem rid_tmul {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
    [NonarchimedeanAddGroup M] [ContinuousSMul A M] [CompleteSpace M] [T0Space M]
    (m : M) (a : A) :
    rid A M (tmul A M A m a) = a • m := by
  simp [rid]

@[simp]
theorem rid_symm_apply {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M]
    [IsUniformAddGroup M] [NonarchimedeanAddGroup M] [ContinuousSMul A M] [CompleteSpace M]
    [T0Space M] (m : M) :
    (rid A M).symm m = tmul A M A m 1 := by
  simp [rid]

@[simp]
theorem rid_toCompletion {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M]
    [IsUniformAddGroup M] [NonarchimedeanAddGroup M] [ContinuousSMul A M] [CompleteSpace M]
    [T0Space M] (u : M ⊗[A] A) :
    rid A M (toCompletion A M A u) = TensorProduct.rid A M u := by
  induction u using TensorProduct.inductionOn with
  | tmul m a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Topological

section Normed

/-- When both `V` and `W` have bounded `A`-actions over a seminormed commutative ring `A`,
`comm A V W` preserves `productNorm`. -/
@[simp]
theorem productNorm_comm {A V W : Type*} [SeminormedCommRing A]
    [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    productNorm A W V (comm A V W z) = productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq ((continuous_productNorm A W V).comp (comm A V W).continuous)
      (continuous_productNorm A V W)) fun u ↦ ?_
  rw [comm_toCompletion, productNorm_toCompletion hW, productNorm_toCompletion hV,
    productSeminorm_comm]

section Contractive

variable {A V W : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V] [IsBoundedSMul A V]
  [SeminormedAddCommGroup W] [Module A W] [IsBoundedSMul A W]

@[simp]
theorem norm_comm (z : CompletedTensor A V W) : ‖comm A V W z‖ = ‖z‖ :=
  productNorm_comm ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩ z

variable (A V W) in
/-- **Isometric symmetry of the completed tensor product** `V ⊗̂_A W ≃ₗᵢ[A] W ⊗̂_A V` for Banach
modules with contractive actions over a Tate seminormed commutative ring `A`. -/
noncomputable def commₗᵢ : CompletedTensor A V W ≃ₗᵢ[A] CompletedTensor A W V :=
  { (comm A V W).toLinearEquiv with
    norm_map' := norm_comm }

@[simp]
theorem commₗᵢ_tmul (v : V) (w : W) :
    commₗᵢ A V W (tmul A V W v w) = tmul A W V w v :=
  comm_tmul v w

@[simp]
theorem commₗᵢ_symm : (commₗᵢ A V W).symm = commₗᵢ A W V := by
  ext z
  exact DFunLike.congr_fun comm_symm z

end Contractive

section RidIsometry

variable {A M : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
  [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M] [Module A M] [IsBoundedSMul A M]

variable (A M) in
/-- **Isometric right unit equivalence** `M ⊗̂_A A ≃ₗᵢ[A] M` for a complete ultrametric normed
`A`-module `M` with contractive action over a Tate seminormed commutative ring `A`. -/
noncomputable def ridₗᵢ : CompletedTensor A M A ≃ₗᵢ[A] M :=
  (commₗᵢ A M A).trans (lidₗᵢ A M)

@[simp]
theorem ridₗᵢ_tmul (m : M) (a : A) : ridₗᵢ A M (tmul A M A m a) = a • m := by
  simp [ridₗᵢ]

@[simp]
theorem ridₗᵢ_symm_apply (m : M) : (ridₗᵢ A M).symm m = tmul A M A m 1 := by
  simp [ridₗᵢ]

end RidIsometry

end Normed

end CommAndRid

/-! ### Right scalar extension via `RightModule` -/

namespace RightModule

section Topological

variable {A V W : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup V] [Module A V] [TopologicalSpace V]
  [AddCommGroup W] [Module A W] [TopologicalSpace W]

/-- Scoped `DistribMulAction S` on `V ⊗̂_A W` induced from a continuous action of `S` on the right
factor `W` commuting with `A`, transported along `comm A V W`. Activate with
`open scoped CompletedTensor.RightModule`. -/
noncomputable scoped instance (priority := low) rightDistribMulAction {S : Type*} [Monoid S]
    [DistribMulAction S W] [SMulCommClass A S W] [ContinuousConstSMul S W] :
    DistribMulAction S (CompletedTensor A V W) :=
  (comm A V W).toLinearEquiv.toAddEquiv.distribMulAction S

scoped instance (priority := low) uniformContinuousConstSMul_right {S : Type*} [Monoid S]
    [DistribMulAction S W] [SMulCommClass A S W] [ContinuousConstSMul S W] :
    UniformContinuousConstSMul S (CompletedTensor A V W) :=
  ⟨fun s ↦ (comm A V W).symm.toContinuousLinearMap.uniformContinuous.comp <|
    (uniformContinuous_const_smul s).comp (comm A V W).toContinuousLinearMap.uniformContinuous⟩

/-- Scoped `Module S` on `V ⊗̂_A W` induced from a continuous `S`-module structure on the right
factor `W` commuting with `A`, transported along `comm A V W`. Activate with
`open scoped CompletedTensor.RightModule`. -/
noncomputable scoped instance (priority := low) rightModule {S : Type*} [Semiring S] [Module S W]
    [SMulCommClass A S W] [ContinuousConstSMul S W] :
    Module S (CompletedTensor A V W) :=
  (comm A V W).toLinearEquiv.toAddEquiv.module S

scoped instance (priority := low) isScalarTower_right {S : Type*} [Monoid S]
    [DistribMulAction S W] [SMulCommClass A S W] [ContinuousConstSMul S W]
    [SMul A S] [IsScalarTower A S W] :
    IsScalarTower A S (CompletedTensor A V W) :=
  ⟨fun a s z ↦ by
    change (comm A V W).symm ((a • s) • comm A V W z) =
      a • (comm A V W).symm (s • comm A V W z)
    rw [smul_assoc, (comm A V W).symm.map_smul]⟩

scoped instance (priority := low) smulCommClass_right {S : Type*} [Monoid S]
    [DistribMulAction S W] [SMulCommClass A S W] [ContinuousConstSMul S W] :
    SMulCommClass A S (CompletedTensor A V W) :=
  ⟨fun a s z ↦ by
    change a • (comm A V W).symm (s • comm A V W z) =
      (comm A V W).symm (s • comm A V W (a • z))
    rw [← (comm A V W).symm.map_smul, (comm A V W).map_smul, smul_comm]⟩

scoped instance (priority := low) smulCommClass_right' {S : Type*} [Monoid S]
    [DistribMulAction S W] [SMulCommClass A S W] [ContinuousConstSMul S W] :
    SMulCommClass S A (CompletedTensor A V W) :=
  .symm _ _ _

end Topological

end RightModule

section RightModuleAPI

open scoped RightModule

section Topological

variable {A V W : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup V] [Module A V] [TopologicalSpace V]
  [AddCommGroup W] [Module A W] [TopologicalSpace W]

/-- Under `open scoped RightModule`, the extended right action of `S` acts on elementary tensors
via `s • (v ⊗ w) = v ⊗ (s • w)`. -/
@[simp]
theorem tmul_smul' {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass A S W]
    [ContinuousConstSMul S W] (s : S) (v : V) (w : W) :
    s • tmul A V W v w = tmul A V W v (s • w) := by
  change (comm A V W).symm (s • comm A V W (tmul A V W v w)) = tmul A V W v (s • w)
  rw [comm_tmul, smul_tmul', comm_symm, comm_tmul]

/-- Under `open scoped RightModule`, `comm A V W` intertwines the right `S`-action on `V ⊗̂_A W`
with the left `S`-action on `W ⊗̂_A V`. -/
@[simp]
theorem comm_smul_right {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass A S W]
    [ContinuousConstSMul S W] (s : S) (z : CompletedTensor A V W) :
    comm A V W (s • z) = s • comm A V W z := by
  change comm A V W ((comm A V W).symm (s • comm A V W z)) = s • comm A V W z
  exact (comm A V W).apply_symm_apply _

/-- **Bimodule commutativity on `V ⊗̂_A W`.** A continuous left action of `S₁` on `V` (commuting
with `A`) commutes with the scoped right action of `S₂` on `W` (commuting with `A`). -/
theorem smul_comm_left_right {S₁ S₂ : Type*} [Monoid S₁] [DistribMulAction S₁ V]
    [SMulCommClass A S₁ V] [ContinuousConstSMul S₁ V] [Monoid S₂] [DistribMulAction S₂ W]
    [SMulCommClass A S₂ W] [ContinuousConstSMul S₂ W]
    (s₁ : S₁) (s₂ : S₂) (z : CompletedTensor A V W) :
    s₁ • (s₂ • z) = s₂ • (s₁ • z) := by
  let l₁ : CompletedTensor A V W →L[A] CompletedTensor A V W :=
    { toFun := fun x ↦ s₁ • (s₂ • x)
      map_add' := fun x y ↦ by simp [smul_add]
      map_smul' := fun a x ↦ by simp [smul_comm a]
      cont := (continuous_const_smul s₁).comp (continuous_const_smul s₂) }
  let l₂ : CompletedTensor A V W →L[A] CompletedTensor A V W :=
    { toFun := fun x ↦ s₂ • (s₁ • x)
      map_add' := fun x y ↦ by simp [smul_add]
      map_smul' := fun a x ↦ by simp [smul_comm a]
      cont := (continuous_const_smul s₂).comp (continuous_const_smul s₁) }
  exact DFunLike.congr_fun (ext (f := l₁) (g := l₂) fun v w ↦ by
    change s₁ • (s₂ • tmul A V W v w) = s₂ • (s₁ • tmul A V W v w)
    rw [tmul_smul', smul_tmul', smul_tmul', tmul_smul']) z

/-- **`S`-linear symmetry of the completed tensor product**: under `open scoped RightModule`,
`comm A V W` upgraded to a continuous `S`-linear equivalence `V ⊗̂_A W ≃L[S] W ⊗̂_A V` from the
right `S`-module structure on `V ⊗̂_A W` to the left `S`-module structure on `W ⊗̂_A V`. -/
noncomputable def commₛ (S A V W : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Semiring S] [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W]
    [Module S W] [SMulCommClass A S W] [ContinuousConstSMul S W] :
    CompletedTensor A V W ≃L[S] CompletedTensor A W V :=
  { (comm A V W).toLinearEquiv.toAddEquiv.linearEquiv S with
    continuous_toFun := (comm A V W).continuous
    continuous_invFun := (comm A V W).symm.continuous }

@[simp]
theorem commₛ_apply {S : Type*} [Semiring S] [Module S W] [SMulCommClass A S W]
    [ContinuousConstSMul S W] (z : CompletedTensor A V W) :
    commₛ S A V W z = comm A V W z :=
  (rfl)

@[simp]
theorem commₛ_symm_apply {S : Type*} [Semiring S] [Module S W] [SMulCommClass A S W]
    [ContinuousConstSMul S W] (z : CompletedTensor A W V) :
    (commₛ S A V W).symm z = (comm A V W).symm z :=
  (rfl)

end Topological

section Normed

variable {A V W : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V] [IsBoundedSMul A V]
  [SeminormedAddCommGroup W] [Module A W] [IsBoundedSMul A W]

namespace RightModule

scoped instance (priority := low) instIsBoundedSMulRight {S : Type*} [SeminormedRing S]
    [Module S W] [SMulCommClass A S W] [IsBoundedSMul S W] :
    IsBoundedSMul S (CompletedTensor A V W) :=
  IsBoundedSMul.of_norm_smul_le fun s z ↦ by
    rw [← norm_comm, comm_smul_right]
    exact (norm_smul_le s (comm A V W z)).trans_eq (by rw [norm_comm])

end RightModule

/-- **`S`-linear isometric symmetry of the completed tensor product** `V ⊗̂_A W ≃ₗᵢ[S] W ⊗̂_A V`
under `open scoped RightModule`. -/
noncomputable def commₛₗᵢ (S A V W : Type*) [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
    [Semiring S] [SeminormedAddCommGroup V] [Module A V] [IsBoundedSMul A V]
    [SeminormedAddCommGroup W] [Module A W] [IsBoundedSMul A W]
    [Module S W] [SMulCommClass A S W] [ContinuousConstSMul S W] :
    CompletedTensor A V W ≃ₗᵢ[S] CompletedTensor A W V :=
  { (commₛ S A V W).toLinearEquiv with
    norm_map' := norm_comm }

@[simp]
theorem commₛₗᵢ_apply {S : Type*} [Semiring S] [Module S W] [SMulCommClass A S W]
    [ContinuousConstSMul S W] (z : CompletedTensor A V W) :
    commₛₗᵢ S A V W z = comm A V W z :=
  (rfl)

@[simp]
theorem commₛₗᵢ_symm_apply {S : Type*} [Semiring S] [Module S W] [SMulCommClass A S W]
    [ContinuousConstSMul S W] (z : CompletedTensor A W V) :
    (commₛₗᵢ S A V W).symm z = (comm A V W).symm z :=
  (rfl)

end Normed

end RightModuleAPI

/-! ### Scalar extension of continuous linear maps (`baseChange`) -/

section BaseChange

section Topological

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- If `f : V →L[A] V'` commutes with a continuous left scalar action `s • ·`, then `map f g`
commutes with the extended left action of `s` on `CompletedTensor A V W`. -/
theorem map_smul_left {V V' W W' S : Type*}
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup V'] [Module A V'] [TopologicalSpace V']
    [AddCommGroup W] [Module A W] [TopologicalSpace W]
    [AddCommGroup W'] [Module A W'] [TopologicalSpace W']
    [Monoid S] [DistribMulAction S V] [SMulCommClass A S V] [ContinuousConstSMul S V]
    [DistribMulAction S V'] [SMulCommClass A S V'] [ContinuousConstSMul S V']
    (f : V →L[A] V') (g : W →L[A] W') (s : S) (hf : ∀ v, f (s • v) = s • f v)
    (z : CompletedTensor A V W) :
    map f g (s • z) = s • map f g z := by
  let l₁ : CompletedTensor A V W →L[A] CompletedTensor A V' W' :=
    { toFun := fun x ↦ map f g (s • x)
      map_add' := fun x y ↦ by simp [smul_add]
      map_smul' := fun a x ↦ by rw [RingHom.id_apply, smul_comm s a, map_smul]
      cont := (map f g).continuous.comp (continuous_const_smul s) }
  let l₂ : CompletedTensor A V W →L[A] CompletedTensor A V' W' :=
    { toFun := fun x ↦ s • map f g x
      map_add' := fun x y ↦ by simp [smul_add]
      map_smul' := fun a x ↦ by rw [RingHom.id_apply, map_smul, smul_comm s a]
      cont := (continuous_const_smul s).comp (map f g).continuous }
  exact DFunLike.congr_fun (ext (f := l₁) (g := l₂) fun v w ↦ by
    change map f g (s • tmul A V W v w) = s • map f g (tmul A V W v w)
    rw [smul_tmul', map_tmul, hf, map_tmul, smul_tmul']) z

/-- **Completed base change of a continuous linear map**: given a topological `A`-algebra `S` and
`g : W →L[A] W'`, `baseChange S g : S ⊗̂_A W →L[S] S ⊗̂_A W'` is `1_S ⊗̂ g` upgraded to a continuous
`S`-linear map. -/
noncomputable def baseChange (S : Type*) [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra A S]
    {W W' : Type*} [AddCommGroup W] [Module A W] [TopologicalSpace W]
    [AddCommGroup W'] [Module A W'] [TopologicalSpace W']
    (g : W →L[A] W') :
    CompletedTensor A S W →L[S] CompletedTensor A S W' :=
  { (map (.id A S) g).toLinearMap with
    map_smul' := fun s z ↦ map_smul_left (.id A S) g s (fun _ ↦ rfl) z
    cont := (map (.id A S) g).continuous }

@[simp]
theorem coe_baseChange (S : Type*) [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra A S]
    {W W' : Type*} [AddCommGroup W] [Module A W] [TopologicalSpace W]
    [AddCommGroup W'] [Module A W'] [TopologicalSpace W']
    (g : W →L[A] W') :
    (baseChange S g : CompletedTensor A S W → CompletedTensor A S W') = map (.id A S) g :=
  (rfl)

@[simp]
theorem baseChange_tmul (S : Type*) [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra A S]
    {W W' : Type*} [AddCommGroup W] [Module A W] [TopologicalSpace W]
    [AddCommGroup W'] [Module A W'] [TopologicalSpace W']
    (g : W →L[A] W') (s : S) (w : W) :
    baseChange S g (tmul A S W s w) = tmul A S W' s (g w) :=
  map_tmul (.id A S) g s w

@[simp]
theorem baseChange_id (S : Type*) [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra A S]
    {W : Type*} [AddCommGroup W] [Module A W] [TopologicalSpace W] :
    baseChange S (.id A W) = ContinuousLinearMap.id S (CompletedTensor A S W) := by
  ext z
  exact DFunLike.congr_fun map_id z

theorem baseChange_comp (S : Type*) [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra A S]
    {W W' W'' : Type*} [AddCommGroup W] [Module A W] [TopologicalSpace W]
    [AddCommGroup W'] [Module A W'] [TopologicalSpace W']
    [AddCommGroup W''] [Module A W''] [TopologicalSpace W'']
    (g₂ : W' →L[A] W'') (g₁ : W →L[A] W') :
    baseChange S (g₂.comp g₁) = (baseChange S g₂).comp (baseChange S g₁) := by
  ext z
  exact DFunLike.congr_fun (map_comp (.id A S) g₂ (.id A S) g₁).symm z |>.symm

end Topological

section Normed

/-- Pointwise norm bound on `CompletedTensor.baseChange`: if `‖g w‖ ≤ C * ‖w‖` (`0 ≤ C`), then
`‖baseChange S g z‖ ≤ C * ‖z‖`. -/
theorem norm_baseChange_le {A S W W' : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
    [SeminormedRing S] [Algebra A S] [IsBoundedSMul A S]
    [SeminormedAddCommGroup W] [Module A W] [IsBoundedSMul A W]
    [SeminormedAddCommGroup W'] [Module A W'] [IsBoundedSMul A W']
    (g : W →L[A] W') {C : ℝ} (hC : 0 ≤ C) (hg : ∀ w, ‖g w‖ ≤ C * ‖w‖)
    (z : CompletedTensor A S W) :
    ‖baseChange S g z‖ ≤ C * ‖z‖ := by
  simpa only [coe_baseChange, one_mul] using
    norm_map_le (.id A S) g zero_le_one hC (fun s ↦ by simp) hg z

/-- Operator-norm bound on `CompletedTensor.baseChange` over nontrivially normed fields `K → L`:
`‖baseChange L g‖ ≤ ‖g‖`. -/
theorem opNorm_baseChange_le {K L W W' : Type*} [NontriviallyNormedField K]
    [NontriviallyNormedField L] [NormedAlgebra K L]
    [SeminormedAddCommGroup W] [NormedSpace K W]
    [SeminormedAddCommGroup W'] [NormedSpace K W']
    (g : W →L[K] W') :
    ‖baseChange L g‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
    (norm_baseChange_le g (norm_nonneg g) g.le_opNorm)

end Normed

end BaseChange

/-! ### Transitivity of completed base change (`cancelBaseChange`) -/

section CancelBaseChange

private theorem tmul_smul_left {A V W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W] (a : A) (v : V) (w : W) :
    tmul A V W (a • v) w = a • tmul A V W v w := by
  rw [(tmul A V W).map_smul, LinearMap.smul_apply]

variable {R A B M N : Type*}
  [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A] [Algebra R A] [IsBoundedSMul R A]
  [Semiring B]
  [SeminormedAddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [IsBoundedSMul R M] [IsBoundedSMul A M]
  [Module B M] [SMulCommClass R B M] [SMulCommClass A B M] [ContinuousConstSMul B M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

private noncomputable def smulRightCLM (m : M) : A →L[R] M where
  toFun a := a • m
  map_add' a₁ a₂ := add_smul a₁ a₂ m
  map_smul' r a := by simp
  cont := continuous_id.smul continuous_const

private noncomputable def cancelBaseChangeBilin :
    M →ₗ[A] CompletedTensor R A N →ₗ[A] CompletedTensor R M N where
  toFun m :=
    { (map (smulRightCLM (R := R) (A := A) m) (.id R N)).toLinearMap with
      map_smul' := fun a z ↦
        map_smul_left (smulRightCLM (R := R) (A := A) m) (.id R N) a
          (fun a' ↦ mul_smul a a' m) z }
  map_add' m₁ m₂ := LinearMap.ext fun z ↦ by
    let l₁ := map (smulRightCLM (R := R) (A := A) (m₁ + m₂)) (.id R N)
    let l₂ := map (smulRightCLM (R := R) (A := A) m₁) (.id R N) +
      map (smulRightCLM (R := R) (A := A) m₂) (.id R N)
    exact DFunLike.congr_fun (ext (f := l₁) (g := l₂) fun a n ↦ by
      simp [l₁, l₂, smulRightCLM, smul_add]) z
  map_smul' a₀ m := LinearMap.ext fun z ↦ by
    let l₁ := map (smulRightCLM (R := R) (A := A) (a₀ • m)) (.id R N)
    let l₂ : CompletedTensor R A N →L[R] CompletedTensor R M N :=
      { toFun := fun x ↦ a₀ • map (smulRightCLM (R := R) (A := A) m) (.id R N) x
        map_add' := fun x y ↦ by simp [smul_add]
        map_smul' := fun r x ↦ by rw [RingHom.id_apply, map_smul, ← smul_comm r a₀]
        cont := (continuous_const_smul a₀).comp
          (map (smulRightCLM (R := R) (A := A) m) (.id R N)).continuous }
    exact DFunLike.congr_fun (ext (f := l₁) (g := l₂) fun a n ↦ by
      change map (smulRightCLM (R := R) (A := A) (a₀ • m)) (.id R N) (tmul R A N a n) =
        a₀ • map (smulRightCLM (R := R) (A := A) m) (.id R N) (tmul R A N a n)
      simp only [map_tmul, ContinuousLinearMap.id_apply, smulRightCLM, ContinuousLinearMap.coe_mk',
        LinearMap.coe_mk, AddHom.coe_mk, smul_tmul']
      rw [← mul_smul, mul_comm, mul_smul]) z

omit [TauCeti.NormedRing.IsTate A] in
private theorem norm_cancelBaseChangeBilin_le (m : M) (z : CompletedTensor R A N) :
    ‖cancelBaseChangeBilin (R := R) (A := A) m z‖ ≤ 1 * ‖m‖ * ‖z‖ := by
  change ‖map (smulRightCLM (R := R) (A := A) m) (.id R N) z‖ ≤ 1 * ‖m‖ * ‖z‖
  simpa only [one_mul, mul_one] using
    norm_map_le (smulRightCLM (R := R) (A := A) m) (.id R N) (norm_nonneg m) zero_le_one
      (fun a ↦ by
        change ‖a • m‖ ≤ ‖m‖ * ‖a‖
        exact (norm_smul_le a m).trans_eq (mul_comm _ _))
      (fun n ↦ by simp) z

private noncomputable def cancelBaseChangeFwd :
    CompletedTensor A M (CompletedTensor R A N) →L[A] CompletedTensor R M N :=
  lift (cancelBaseChangeBilin (R := R) (A := A) (M := M) (N := N))
    (LinearMap.continuous₂_of_bound
      (cancelBaseChangeBilin (R := R) (A := A) (M := M) (N := N))
      1 norm_cancelBaseChangeBilin_le)

omit [TauCeti.NormedRing.IsTate A] in
private theorem cancelBaseChangeFwd_tmul (m : M) (a : A) (n : N) :
    cancelBaseChangeFwd (tmul A M _ m (tmul R A N a n)) = tmul R M N (a • m) n := by
  rw [cancelBaseChangeFwd, lift_tmul]
  exact map_tmul (smulRightCLM (R := R) (A := A) m) (.id R N) a n

private noncomputable def cancelBaseChangeInvBilin :
    M →ₗ[R] N →ₗ[R] CompletedTensor A M (CompletedTensor R A N) where
  toFun m :=
    { toFun := fun n ↦ tmul A M _ m (tmul R A N 1 n)
      map_add' := fun n₁ n₂ ↦ by simp
      map_smul' := fun r n ↦ by
        simp only [RingHom.id_apply]
        rw [(tmul R A N 1).map_smul, ← tmul_smul_left, ← IsScalarTower.algebraMap_smul A r (1 : A),
          ← smul_tmul', (tmul A M _ m).map_smul, ← tmul_smul_left,
          IsScalarTower.algebraMap_smul, ← smul_tmul'] }
  map_add' m₁ m₂ := LinearMap.ext fun n ↦ by simp
  map_smul' r m := LinearMap.ext fun n ↦ by simp [smul_tmul']

private theorem continuousSMul_R_nested :
    ContinuousSMul R (CompletedTensor A M (CompletedTensor R A N)) :=
  continuousSMul_of_boundedSMul
    ⟨1, fun a m ↦ by simpa using norm_smul_le a m⟩
    ⟨1, fun a z ↦ by simpa using norm_smul_le a z⟩
    ⟨1, fun r m ↦ by simpa using norm_smul_le r m⟩

attribute [local instance] continuousSMul_R_nested

private noncomputable def cancelBaseChangeInv :
    CompletedTensor R M N →L[R] CompletedTensor A M (CompletedTensor R A N) :=
  lift (cancelBaseChangeInvBilin (R := R) (A := A) (M := M) (N := N))
    (((continuous_tmul A M _).comp
      (continuous_fst.prodMk
        ((continuous_tmul R A N).comp (continuous_const.prodMk continuous_snd)))).congr
      fun _ ↦ rfl)

private theorem cancelBaseChangeInv_tmul (m : M) (n : N) :
    cancelBaseChangeInv (A := A) (tmul R M N m n) = tmul A M _ m (tmul R A N 1 n) := by
  rw [cancelBaseChangeInv, lift_tmul]
  rfl

private theorem cancelBaseChangeInv_smul_A (a₀ : A) (u : CompletedTensor R M N) :
    cancelBaseChangeInv (A := A) (a₀ • u) = a₀ • cancelBaseChangeInv (A := A) u := by
  let l₁ : CompletedTensor R M N →L[R] CompletedTensor A M (CompletedTensor R A N) :=
    { toFun := fun x ↦ cancelBaseChangeInv (A := A) (a₀ • x)
      map_add' := fun x y ↦ by simp [smul_add]
      map_smul' := fun r x ↦ by rw [RingHom.id_apply, ← smul_comm r a₀, map_smul]
      cont := (cancelBaseChangeInv (A := A)).continuous.comp (continuous_const_smul a₀) }
  let l₂ : CompletedTensor R M N →L[R] CompletedTensor A M (CompletedTensor R A N) :=
    { toFun := fun x ↦ a₀ • cancelBaseChangeInv (A := A) x
      map_add' := fun x y ↦ by simp [smul_add]
      map_smul' := fun r x ↦ by rw [RingHom.id_apply, map_smul, ← smul_comm r a₀]
      cont := (continuous_const_smul a₀).comp (cancelBaseChangeInv (A := A)).continuous }
  exact DFunLike.congr_fun (ext (f := l₁) (g := l₂) fun m n ↦ by
    change cancelBaseChangeInv (A := A) (a₀ • tmul R M N m n) =
      a₀ • cancelBaseChangeInv (A := A) (tmul R M N m n)
    rw [smul_tmul', cancelBaseChangeInv_tmul, cancelBaseChangeInv_tmul, tmul_smul_left]) u

private theorem cancelBaseChangeFwd_inv (u : CompletedTensor R M N) :
    cancelBaseChangeFwd (cancelBaseChangeInv (A := A) u) = u := by
  let compCLM : CompletedTensor R M N →L[R] CompletedTensor R M N :=
    { toFun := fun x ↦ cancelBaseChangeFwd (cancelBaseChangeInv (A := A) x)
      map_add' := fun x y ↦ by simp
      map_smul' := fun r x ↦ by
        simp only [RingHom.id_apply]
        rw [← IsScalarTower.algebraMap_smul A r x, cancelBaseChangeInv_smul_A,
          (cancelBaseChangeFwd (R := R) (A := A)).map_smul, IsScalarTower.algebraMap_smul]
      cont := (cancelBaseChangeFwd (R := R) (A := A)).continuous.comp
        (cancelBaseChangeInv (A := A)).continuous }
  suffices compCLM = ContinuousLinearMap.id R (CompletedTensor R M N) from
    DFunLike.congr_fun this u
  exact ext fun m n ↦ by
    change cancelBaseChangeFwd (cancelBaseChangeInv (A := A) (tmul R M N m n)) = tmul R M N m n
    rw [cancelBaseChangeInv_tmul, cancelBaseChangeFwd_tmul, one_smul]

private theorem cancelBaseChangeInv_fwd
    (w : CompletedTensor A M (CompletedTensor R A N)) :
    cancelBaseChangeInv (A := A) (cancelBaseChangeFwd w) = w := by
  let invA : CompletedTensor R M N →L[A] CompletedTensor A M (CompletedTensor R A N) :=
    { (cancelBaseChangeInv (A := A)).toLinearMap with
      map_smul' := cancelBaseChangeInv_smul_A
      cont := (cancelBaseChangeInv (A := A)).continuous }
  suffices invA.comp cancelBaseChangeFwd = ContinuousLinearMap.id A _ from
    DFunLike.congr_fun this w
  refine ext fun m z ↦ ?_
  let f₁ : CompletedTensor R A N →L[R] CompletedTensor A M (CompletedTensor R A N) :=
    (cancelBaseChangeInv (A := A)).comp (map (smulRightCLM (R := R) (A := A) m) (.id R N))
  let f₂ : CompletedTensor R A N →L[R] CompletedTensor A M (CompletedTensor R A N) :=
    { toFun := tmul A M _ m
      map_add' := map_add _
      map_smul' := fun r x ↦ by
        simp only [RingHom.id_apply]
        have hr : r • x = algebraMap R A r • x := by
          let g₁ : CompletedTensor R A N →L[R] CompletedTensor R A N :=
            { toFun := (r • ·), map_add' := smul_add r,
              map_smul' := fun r' y ↦ smul_comm r r' y, cont := continuous_const_smul r }
          let g₂ : CompletedTensor R A N →L[R] CompletedTensor R A N :=
            { toFun := (algebraMap R A r • ·), map_add' := smul_add _,
              map_smul' := fun r' y ↦ smul_comm (algebraMap R A r) r' y,
              cont := continuous_const_smul _ }
          exact DFunLike.congr_fun (ext (f := g₁) (g := g₂) fun a n ↦ by
            change r • tmul R A N a n = algebraMap R A r • tmul R A N a n
            rw [← tmul_smul_left, ← IsScalarTower.algebraMap_smul A r a, ← smul_tmul']) x
        rw [hr, (tmul A M _ m).map_smul, ← tmul_smul_left, IsScalarTower.algebraMap_smul,
          ← smul_tmul']
      cont := (continuous_tmul A M _).comp (continuous_const.prodMk continuous_id) }
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, cancelBaseChangeFwd, lift_tmul]
  exact DFunLike.congr_fun (ext (f := f₁) (g := f₂) fun a n ↦ by
    have h1 : f₁ (tmul R A N a n) =
        cancelBaseChangeInv (A := A)
          (map (smulRightCLM (R := R) (A := A) m) (.id R N) (tmul R A N a n)) := rfl
    have h2 : f₂ (tmul R A N a n) = tmul A M _ m (tmul R A N a n) := rfl
    rw [h1, h2, map_tmul, ContinuousLinearMap.id_apply]
    change cancelBaseChangeInv (A := A) (tmul R M N (a • m) n) = tmul A M _ m (tmul R A N a n)
    rw [cancelBaseChangeInv_tmul, tmul_smul_left, ← (tmul A M _ m).map_smul, smul_tmul',
      smul_eq_mul, mul_one]) z

private theorem cancelBaseChangeInv_smul_B (b : B) (u : CompletedTensor R M N) :
    cancelBaseChangeInv (A := A) (b • u) = b • cancelBaseChangeInv (A := A) u := by
  let l₁ : CompletedTensor R M N →L[R] CompletedTensor A M (CompletedTensor R A N) :=
    { toFun := fun x ↦ cancelBaseChangeInv (A := A) (b • x)
      map_add' := fun x y ↦ by simp [smul_add]
      map_smul' := fun r x ↦ by rw [RingHom.id_apply, ← smul_comm r b, map_smul]
      cont := (cancelBaseChangeInv (A := A)).continuous.comp (continuous_const_smul b) }
  let l₂ : CompletedTensor R M N →L[R] CompletedTensor A M (CompletedTensor R A N) :=
    { toFun := fun x ↦ b • cancelBaseChangeInv (A := A) x
      map_add' := fun x y ↦ by simp [smul_add]
      map_smul' := fun r x ↦ by rw [RingHom.id_apply, map_smul, ← smul_comm r b]
      cont := (continuous_const_smul b).comp (cancelBaseChangeInv (A := A)).continuous }
  exact DFunLike.congr_fun (ext (f := l₁) (g := l₂) fun m n ↦ by
    change cancelBaseChangeInv (A := A) (b • tmul R M N m n) =
      b • cancelBaseChangeInv (A := A) (tmul R M N m n)
    rw [smul_tmul', cancelBaseChangeInv_tmul, cancelBaseChangeInv_tmul, smul_tmul']) u

private theorem norm_cancelBaseChangeInv_le (u : CompletedTensor R M N) :
    ‖cancelBaseChangeInv (A := A) u‖ ≤ ‖u‖ := by
  refine (denseRange_toCompletion R M N).induction_on u
    (isClosed_le ((continuous_productNorm A M _).comp (cancelBaseChangeInv (A := A)).continuous)
      (continuous_productNorm R M N)) fun x ↦ ?_
  rw [norm_toCompletion]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨k, m, n, rfl, hmn⟩ :=
    exists_sum_tmul_eq_of_productSeminorm_lt (lt_add_of_pos_right (productSeminorm R M N x) hε)
  have hc0 : 0 ≤ productSeminorm R M N (∑ i, m i ⊗ₜ[R] n i) + ε :=
    add_nonneg (apply_nonneg _ _) hε.le
  rw [map_sum, map_sum]
  simpa only [toCompletion_tmul, cancelBaseChangeInv_tmul] using
    norm_sum_tmul_le (A := A) (V := M) (W := CompletedTensor R A N) Finset.univ m
      (fun i ↦ tmul R A N 1 (n i)) hc0 fun i _ ↦ calc
        ‖m i‖ * ‖tmul R A N (1 : A) (n i)‖ ≤ ‖m i‖ * (‖(1 : A)‖ * ‖n i‖) := by
          gcongr; exact norm_tmul_le _ _
        _ = ‖m i‖ * ‖n i‖ := by rw [norm_one, one_mul]
        _ ≤ _ := (hmn i).le

private theorem norm_cancelBaseChangeFwd (w : CompletedTensor A M (CompletedTensor R A N)) :
    ‖cancelBaseChangeFwd w‖ = ‖w‖ := by
  refine le_antisymm ?_ ?_
  · simpa only [one_mul] using norm_apply_le cancelBaseChangeFwd zero_le_one
      (fun m z ↦ by rw [cancelBaseChangeFwd, lift_tmul]; exact norm_cancelBaseChangeBilin_le m z) w
  · calc ‖w‖ = ‖cancelBaseChangeInv (A := A) (cancelBaseChangeFwd w)‖ := by
          rw [cancelBaseChangeInv_fwd]
      _ ≤ ‖cancelBaseChangeFwd w‖ := norm_cancelBaseChangeInv_le _

variable (R A B M N) in
/-- **Isometric transitivity of completed base change** (`cancelBaseChangeₗᵢ`): for Tate seminormed
commutative rings `R → A` and Banach modules `M`, `N` with contractive actions, the natural map
`M ⊗̂_A (A ⊗̂_R N) ≃ₗᵢ[B] M ⊗̂_R N` sending `m ⊗ (a ⊗ n)` to `(a • m) ⊗ n` is a `B`-linear
isometric equivalence. -/
noncomputable def cancelBaseChangeₗᵢ :
    CompletedTensor A M (CompletedTensor R A N) ≃ₗᵢ[B] CompletedTensor R M N :=
  let eSymm : CompletedTensor R M N ≃ₗ[B] CompletedTensor A M (CompletedTensor R A N) :=
    { toFun := cancelBaseChangeInv
      invFun := cancelBaseChangeFwd
      left_inv := cancelBaseChangeFwd_inv
      right_inv := cancelBaseChangeInv_fwd
      map_add' := map_add cancelBaseChangeInv
      map_smul' := cancelBaseChangeInv_smul_B }
  { eSymm.symm with
    norm_map' := norm_cancelBaseChangeFwd }

variable (R A B M N) in
/-- **Transitivity of completed base change** (`cancelBaseChange`): the `B`-linear topological
isomorphism `M ⊗̂_A (A ⊗̂_R N) ≃L[B] M ⊗̂_R N` sending `m ⊗ (a ⊗ n)` to `(a • m) ⊗ n` and with
inverse sending `m ⊗ n` to `m ⊗ (1 ⊗ n)`. -/
noncomputable def cancelBaseChange :
    CompletedTensor A M (CompletedTensor R A N) ≃L[B] CompletedTensor R M N :=
  (cancelBaseChangeₗᵢ R A B M N).toContinuousLinearEquiv

@[simp]
theorem cancelBaseChangeₗᵢ_tmul (m : M) (a : A) (n : N) :
    cancelBaseChangeₗᵢ R A B M N (tmul A M _ m (tmul R A N a n)) = tmul R M N (a • m) n := by
  exact cancelBaseChangeFwd_tmul (R := R) m a n

@[simp]
theorem cancelBaseChangeₗᵢ_symm_tmul (m : M) (n : N) :
    (cancelBaseChangeₗᵢ R A B M N).symm (tmul R M N m n) = tmul A M _ m (tmul R A N 1 n) := by
  exact cancelBaseChangeInv_tmul (A := A) m n

@[simp]
theorem cancelBaseChange_tmul (m : M) (a : A) (n : N) :
    cancelBaseChange R A B M N (tmul A M _ m (tmul R A N a n)) = tmul R M N (a • m) n := by
  exact cancelBaseChangeFwd_tmul (R := R) m a n

@[simp]
theorem cancelBaseChange_symm_tmul (m : M) (n : N) :
    (cancelBaseChange R A B M N).symm (tmul R M N m n) = tmul A M _ m (tmul R A N 1 n) := by
  exact cancelBaseChangeInv_tmul (A := A) m n

end CancelBaseChange

end TauCeti.Huber.BanachModule.CompletedTensor
