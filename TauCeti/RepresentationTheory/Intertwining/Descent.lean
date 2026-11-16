/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.RepresentationTheory.BaseChange

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.LinearMap.BaseChange

/-!
# Algebraic descent of intertwining maps and representation equivalences

Base change of representations along a faithfully flat algebra is faithful on intertwining maps,
and over an algebraic extension of fields every intertwining map (or equivalence) between the
scalar extensions of finite-dimensional representations descends to a finite intermediate field:

* `Representation.IntertwiningMap.baseChange_injective`: base change along a faithfully flat
  algebra is injective on intertwining maps.
* `Representation.IntertwiningMap.eq_of_baseChange_eq`: intertwining maps defined over two
  extensions `E₁, E₂` of `E₀` that agree after base change to a faithfully flat overring `Ω`
  already agree over any common enlargement `E` between `E₁, E₂` and `Ω`.
* `Representation.IntertwiningMap.exists_finiteDimensional_descent`: every intertwining map
  between scalar extensions of finite-dimensional representations along an algebraic field
  extension `Ω / E₀` descends to a finite intermediate field `E₀ ⊆ E ⊆ Ω`.
* `Representation.Equiv.exists_finiteDimensional_descent`: the corresponding descent theorem for
  equivalences of representations.
-/

public section

open IntermediateField
open scoped TensorProduct

namespace Representation

/-- Two-stage `cancelBaseChange` intertwines the twice base-changed representation with the
one-stage base-changed representation. -/
private theorem cancelBaseChange_baseChange_rep {E₀ E Ω G V : Type*}
    [CommRing E₀] [CommRing E] [CommRing Ω]
    [Algebra E₀ E] [Algebra E₀ Ω] [Algebra E Ω] [IsScalarTower E₀ E Ω]
    [Monoid G] [AddCommGroup V] [Module E₀ V]
    (ρ : Representation E₀ G V) (g : G) (z : Ω ⊗[E] (E ⊗[E₀] V)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V
        ((ρ.baseChange E g).baseChange Ω z) =
      ρ.baseChange Ω g (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, hx, hy]
  | tmul c u =>
    induction u using TensorProduct.inductionOn with
    | add u₁ u₂ hu₁ hu₂ =>
      simp only [LinearMap.baseChange_tmul, map_add, TensorProduct.tmul_add] at hu₁ hu₂ ⊢
      rw [hu₁, hu₂]
    | tmul a v =>
      simp only [Representation.baseChange_apply, LinearMap.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

/-- Identifying a linear map conjugated through two-stage `cancelBaseChange` after a further base
change from `E` to `Ω`. -/
private theorem cancelBaseChange_baseChange_cancelBaseChange {E₀ E₁ E Ω V₁ V₂ : Type*}
    [CommRing E₀] [CommRing E₁] [CommRing E] [CommRing Ω]
    [Algebra E₀ E₁] [Algebra E₀ E] [Algebra E₀ Ω]
    [Algebra E₁ E] [Algebra E₁ Ω] [Algebra E Ω]
    [IsScalarTower E₀ E₁ E] [IsScalarTower E₀ E₁ Ω]
    [IsScalarTower E₀ E Ω] [IsScalarTower E₁ E Ω]
    [AddCommGroup V₁] [Module E₀ V₁] [AddCommGroup V₂] [Module E₀ V₂]
    (f : E₁ ⊗[E₀] V₁ →ₗ[E₁] E₁ ⊗[E₀] V₂) (z : Ω ⊗[E] (E ⊗[E₀] V₁)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
      ((((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₂).toLinearMap ∘ₗ
          f.baseChange E ∘ₗ
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            E₀ E₁ E E V₁).symm.toLinearMap).baseChange
        Ω) z) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ Ω Ω V₂
        (f.baseChange Ω
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ Ω Ω V₁).symm
            (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁ z))) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, hx, hy]
  | tmul c u =>
    induction u using TensorProduct.inductionOn with
    | add u₁ u₂ hu₁ hu₂ =>
      simp only [LinearMap.baseChange_tmul, map_add, TensorProduct.tmul_add] at hu₁ hu₂ ⊢
      rw [hu₁, hu₂]
    | tmul e v =>
      -- Expand `f (1 ⊗ v)` as a sum of pure tensors in `E₁ ⊗[E₀] V₂`.
      have hcomm (w : E₁ ⊗[E₀] V₂) :
          TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
            (c ⊗ₜ[E] TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₂ (e ⊗ₜ[E₁] w)) =
          TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ Ω Ω V₂ ((e • c) ⊗ₜ[E₁] w) := by
        induction w using TensorProduct.inductionOn with
        | add w₁ w₂ hw₁ hw₂ =>
          simp only [TensorProduct.tmul_add, map_add, hw₁, hw₂]
        | tmul a v₂ =>
          simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, smul_assoc]
      simp only [LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
      exact hcomm (f (1 ⊗ₜ[E₀] v))

namespace IntertwiningMap

/-- **Base change of intertwining maps is injective along a faithfully flat algebra.** -/
theorem baseChange_injective {R A G V W : Type*}
    [CommRing R] [Ring A] [Algebra R A] [Module.FaithfullyFlat R A]
    [Monoid G] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {σ : Representation R G W} :
    Function.Injective (fun f : IntertwiningMap ρ σ ↦ f.baseChange A) := by
  intro f g h
  have hlin : f.toLinearMap.baseChange A = g.toLinearMap.baseChange A := by
    simpa only [toLinearMap_baseChange] using congrArg toLinearMap h
  exact ext (LinearMap.baseChange_injective (R := R) (A := A) hlin)

/-- **Agreement of descended intertwining maps over a common enlargement.** Let `ρ₁, ρ₂` be
representations over `E₀`, and let `f₁, f₂` be intertwining maps between their base changes to two
extensions `E₁, E₂` contained in a common enlargement `E`. If `f₁` and `f₂` induce the same map
after base change to a faithfully flat `E`-algebra `Ω`, then they already induce the same map over
`E`. -/
theorem eq_of_baseChange_eq {E₀ E₁ E₂ E Ω G V₁ V₂ : Type*}
    [CommRing E₀] [CommRing E₁] [CommRing E₂] [CommRing E] [CommRing Ω]
    [Algebra E₀ E₁] [Algebra E₀ E₂] [Algebra E₀ E] [Algebra E₀ Ω]
    [Algebra E₁ E] [Algebra E₂ E] [Algebra E₁ Ω] [Algebra E₂ Ω] [Algebra E Ω]
    [IsScalarTower E₀ E₁ E] [IsScalarTower E₀ E₂ E] [IsScalarTower E₀ E Ω]
    [IsScalarTower E₀ E₁ Ω] [IsScalarTower E₀ E₂ Ω]
    [IsScalarTower E₁ E Ω] [IsScalarTower E₂ E Ω]
    [Module.FaithfullyFlat E Ω]
    [Monoid G] [AddCommGroup V₁] [Module E₀ V₁] [AddCommGroup V₂] [Module E₀ V₂]
    {ρ₁ : Representation E₀ G V₁} {ρ₂ : Representation E₀ G V₂}
    (f₁ : IntertwiningMap (ρ₁.baseChange E₁) (ρ₂.baseChange E₁))
    (f₂ : IntertwiningMap (ρ₁.baseChange E₂) (ρ₂.baseChange E₂))
    (h : ∀ x : Ω ⊗[E₀] V₁,
      TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ Ω Ω V₂
        (f₁.baseChange Ω
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ Ω Ω V₁).symm x)) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ Ω Ω V₂
        (f₂.baseChange Ω
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ Ω Ω V₁).symm x)))
    (x : E ⊗[E₀] V₁) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₂
      (f₁.baseChange E ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₁).symm x)) =
    TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ E E V₂
      (f₂.baseChange E
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ E E V₁).symm x)) := by
  let g₁ : E ⊗[E₀] V₁ →ₗ[E] E ⊗[E₀] V₂ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₂).toLinearMap ∘ₗ
      f₁.toLinearMap.baseChange E ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₁).symm.toLinearMap
  let g₂ : E ⊗[E₀] V₁ →ₗ[E] E ⊗[E₀] V₂ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ E E V₂).toLinearMap ∘ₗ
      f₂.toLinearMap.baseChange E ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ E E V₁).symm.toLinearMap
  have h1 : ∀ y : E ⊗[E₀] V₁,
      TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₂
        (f₁.baseChange E
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₁).symm y)) =
        g₁ y := fun y ↦ by
    simp only [g₁, LinearMap.comp_apply, LinearEquiv.coe_coe, ← toLinearMap_baseChange,
      coe_toLinearMap]
  have h2 : ∀ y : E ⊗[E₀] V₁,
      TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ E E V₂
        (f₂.baseChange E
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ E E V₁).symm y)) =
        g₂ y := fun y ↦ by
    simp only [g₂, LinearMap.comp_apply, LinearEquiv.coe_coe, ← toLinearMap_baseChange,
      coe_toLinearMap]
  rw [h1, h2]
  suffices g₁ = g₂ by rw [this]
  apply LinearMap.baseChange_injective (R := E) (A := Ω)
  apply LinearMap.ext
  intro z
  apply (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂).injective
  rw [cancelBaseChange_baseChange_cancelBaseChange f₁.toLinearMap z,
    cancelBaseChange_baseChange_cancelBaseChange f₂.toLinearMap z]
  have h' := h (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁ z)
  simpa only [← coe_toLinearMap, toLinearMap_baseChange] using h'

/-- **Algebraic descent of an intertwining map along an algebraic field extension.** Every
intertwining map between the scalar extensions to `Ω` of two finite-dimensional representations
over `E₀` descends to a finite intermediate field `E₀ ⊆ E ⊆ Ω`. -/
theorem exists_finiteDimensional_descent {E₀ Ω G V₁ V₂ : Type*}
    [Field E₀] [Field Ω] [Algebra E₀ Ω] [Algebra.IsAlgebraic E₀ Ω]
    [Monoid G] [AddCommGroup V₁] [Module E₀ V₁] [FiniteDimensional E₀ V₁]
    [AddCommGroup V₂] [Module E₀ V₂] [FiniteDimensional E₀ V₂]
    {ρ₁ : Representation E₀ G V₁} {ρ₂ : Representation E₀ G V₂}
    (f : IntertwiningMap (ρ₁.baseChange Ω) (ρ₂.baseChange Ω)) :
    ∃ (E : IntermediateField E₀ Ω) (_ : FiniteDimensional E₀ E)
      (fE : IntertwiningMap (ρ₁.baseChange E) (ρ₂.baseChange E)),
      ∀ x : Ω ⊗[E₀] V₁,
        TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
          (fE.baseChange Ω
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁).symm x)) = f x := by
  let b₁ := Module.finBasis E₀ V₁
  let b₂ := Module.finBasis E₀ V₂
  let b₁Ω := b₁.baseChange Ω
  let b₂Ω := b₂.baseChange Ω
  let M := LinearMap.toMatrix b₁Ω b₂Ω f.toLinearMap
  let E : IntermediateField E₀ Ω :=
    IntermediateField.adjoin E₀ (Set.range fun p : Fin (Module.finrank E₀ V₂) ×
      Fin (Module.finrank E₀ V₁) ↦ M p.1 p.2)
  have hEfin : FiniteDimensional E₀ E :=
    IntermediateField.finiteDimensional_adjoin fun _ _ ↦ Algebra.IsIntegral.isIntegral _
  let b₁E := b₁.baseChange E
  let b₂E := b₂.baseChange E
  let ME : Matrix (Fin (Module.finrank E₀ V₂)) (Fin (Module.finrank E₀ V₁)) E :=
    fun i j ↦ ⟨M i j, IntermediateField.subset_adjoin E₀ _ ⟨(i, j), rfl⟩⟩
  let gE : E ⊗[E₀] V₁ →ₗ[E] E ⊗[E₀] V₂ := Matrix.toLin b₁E b₂E ME
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
  have hcompat : ∀ x : Ω ⊗[E₀] V₁, e₂ (gE.baseChange Ω (e₁.symm x)) = f x := by
    suffices e₂.toLinearMap ∘ₗ gE.baseChange Ω ∘ₗ e₁.symm.toLinearMap = f.toLinearMap from
      fun x ↦ LinearMap.congr_fun this x
    refine b₁Ω.ext fun j ↦ ?_
    have hf : f.toLinearMap (b₁Ω j) = ∑ i, M i j • b₂Ω i := by
      have h := Matrix.toLin_self b₁Ω b₂Ω M j
      rwa [Matrix.toLin_toMatrix] at h
    rw [hf]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, b₁Ω, e₁, gE]
    rw [Module.Basis.baseChange_apply Ω b₁ j,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul E₀ E Ω 1 (b₁ j),
      LinearMap.baseChange_tmul, ← Module.Basis.baseChange_apply E b₁ j,
      Matrix.toLin_self b₁E b₂E ME j, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Module.Basis.baseChange_apply E b₂ i, Module.Basis.baseChange_apply Ω b₂ i,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simp only [smul_eq_mul, mul_one, Algebra.smul_def, IntermediateField.algebraMap_apply, ME]
  have hinter : ∀ g : G, gE ∘ₗ ρ₁.baseChange E g = ρ₂.baseChange E g ∘ₗ gE := by
    intro g
    apply LinearMap.baseChange_injective (R := E) (A := Ω)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    apply LinearMap.ext
    intro y
    apply e₂.injective
    calc e₂ ((gE.baseChange Ω ∘ₗ (ρ₁.baseChange E g).baseChange Ω) y)
        = e₂ (gE.baseChange Ω (e₁.symm (e₁ ((ρ₁.baseChange E g).baseChange Ω y)))) := by
          simp only [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
      _ = f (ρ₁.baseChange Ω g (e₁ y)) := by
          rw [hcompat, cancelBaseChange_baseChange_rep]
      _ = ρ₂.baseChange Ω g (f (e₁ y)) :=
          LinearMap.congr_fun (f.isIntertwining' g) (e₁ y)
      _ = ρ₂.baseChange Ω g (e₂ (gE.baseChange Ω y)) := by
          rw [← hcompat (e₁ y), LinearEquiv.symm_apply_apply]
      _ = e₂ (((ρ₂.baseChange E g).baseChange Ω ∘ₗ gE.baseChange Ω) y) := by
          rw [LinearMap.comp_apply, cancelBaseChange_baseChange_rep]
  refine ⟨E, hEfin, ⟨gE, hinter⟩, fun x ↦ ?_⟩
  simpa only [← coe_toLinearMap, toLinearMap_baseChange] using hcompat x

end IntertwiningMap

namespace Equiv

/-- Transfer compatibility with an equivalence over `Ω` from a subextension `E₁` to an enlargement
`E` along `cancelBaseChange`. -/
private theorem compat_of_descent {E₀ E₁ E Ω G V₁ V₂ : Type*}
    [CommRing E₀] [CommRing E₁] [CommRing E] [CommRing Ω]
    [Algebra E₀ E₁] [Algebra E₀ E] [Algebra E₀ Ω]
    [Algebra E₁ E] [Algebra E₁ Ω] [Algebra E Ω]
    [IsScalarTower E₀ E₁ E] [IsScalarTower E₀ E₁ Ω]
    [IsScalarTower E₀ E Ω] [IsScalarTower E₁ E Ω]
    [Monoid G] [AddCommGroup V₁] [Module E₀ V₁] [AddCommGroup V₂] [Module E₀ V₂]
    {ρ₁ : Representation E₀ G V₁} {ρ₂ : Representation E₀ G V₂}
    (φ : (ρ₁.baseChange Ω).Equiv (ρ₂.baseChange Ω))
    (f₁ : IntertwiningMap (ρ₁.baseChange E₁) (ρ₂.baseChange E₁))
    (hf₁ : ∀ x : Ω ⊗[E₀] V₁,
      TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ Ω Ω V₂
        (f₁.baseChange Ω
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ Ω Ω V₁).symm x)) =
        φ.toIntertwiningMap x)
    (x : Ω ⊗[E₀] V₁) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
      (((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₂).toLinearMap ∘ₗ
          f₁.toLinearMap.baseChange E ∘ₗ
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            E₀ E₁ E E V₁).symm.toLinearMap).baseChange Ω
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁).symm x)) = φ x := by
  have h1 := cancelBaseChange_baseChange_cancelBaseChange (E := E) (Ω := Ω) f₁.toLinearMap
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁).symm x)
  rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁).apply_symm_apply] at h1
  refine h1.trans ?_
  rw [← IntertwiningMap.toLinearMap_baseChange, IntertwiningMap.coe_toLinearMap]
  exact (hf₁ x).trans (by rw [Representation.Equiv.coe_toIntertwiningMap])

/-- Two `E`-linear maps whose base changes to a faithfully flat `E`-algebra `Ω` agree with mutual
inverses `φ` and `ψ` compose to the identity over `E`. -/
private theorem comp_eq_id_of_compat {E₀ E Ω V₁ V₂ : Type*}
    [CommRing E₀] [CommRing E] [CommRing Ω]
    [Algebra E₀ E] [Algebra E₀ Ω] [Algebra E Ω] [IsScalarTower E₀ E Ω]
    [Module.FaithfullyFlat E Ω]
    [AddCommGroup V₁] [Module E₀ V₁] [AddCommGroup V₂] [Module E₀ V₂]
    (fE : E ⊗[E₀] V₁ →ₗ[E] E ⊗[E₀] V₂) (gE : E ⊗[E₀] V₂ →ₗ[E] E ⊗[E₀] V₁)
    (φ : Ω ⊗[E₀] V₁ → Ω ⊗[E₀] V₂) (ψ : Ω ⊗[E₀] V₂ → Ω ⊗[E₀] V₁)
    (hψφ : ∀ x, ψ (φ x) = x)
    (hf : ∀ x, TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
      (fE.baseChange Ω ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁).symm x)) =
      φ x)
    (hg : ∀ y, TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁
      (gE.baseChange Ω ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂).symm y)) =
      ψ y) :
    gE ∘ₗ fE = LinearMap.id := by
  let eV₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁
  let eV₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
  apply LinearMap.baseChange_injective (R := E) (A := Ω)
  rw [LinearMap.baseChange_comp (g := gE) (f := fE), LinearMap.baseChange_id]
  apply LinearMap.ext
  intro z
  apply eV₁.injective
  calc eV₁ ((gE.baseChange Ω ∘ₗ fE.baseChange Ω) z)
      = eV₁ (gE.baseChange Ω (eV₂.symm (eV₂ (fE.baseChange Ω (eV₁.symm (eV₁ z)))))) := by
        simp only [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
    _ = ψ (φ (eV₁ z)) := by rw [hg, hf]
    _ = eV₁ (LinearMap.id z) := by simp only [LinearMap.id_apply, hψφ]

/-- Given descended intertwining maps `f₁` over `E₁` and `g₂` over `E₂` that lift to an
equivalence `φ` and its inverse `φ.symm` over a faithfully flat `E`-algebra `Ω`, glue them into an
equivalence over `E`. -/
private noncomputable def equivOfDescents {E₀ E₁ E₂ E Ω G V₁ V₂ : Type*}
    [CommRing E₀] [CommRing E₁] [CommRing E₂] [CommRing E] [CommRing Ω]
    [Algebra E₀ E₁] [Algebra E₀ E₂] [Algebra E₀ E] [Algebra E₀ Ω]
    [Algebra E₁ E] [Algebra E₂ E] [Algebra E₁ Ω] [Algebra E₂ Ω] [Algebra E Ω]
    [IsScalarTower E₀ E₁ E] [IsScalarTower E₀ E₂ E] [IsScalarTower E₀ E Ω]
    [IsScalarTower E₀ E₁ Ω] [IsScalarTower E₀ E₂ Ω]
    [IsScalarTower E₁ E Ω] [IsScalarTower E₂ E Ω]
    [Module.FaithfullyFlat E Ω]
    [Monoid G] [AddCommGroup V₁] [Module E₀ V₁] [AddCommGroup V₂] [Module E₀ V₂]
    {ρ₁ : Representation E₀ G V₁} {ρ₂ : Representation E₀ G V₂}
    (φ : (ρ₁.baseChange Ω).Equiv (ρ₂.baseChange Ω))
    (f₁ : IntertwiningMap (ρ₁.baseChange E₁) (ρ₂.baseChange E₁))
    (g₂ : IntertwiningMap (ρ₂.baseChange E₂) (ρ₁.baseChange E₂))
    (hf₁ : ∀ x : Ω ⊗[E₀] V₁,
      TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ Ω Ω V₂
        (f₁.baseChange Ω
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ Ω Ω V₁).symm x)) =
        φ.toIntertwiningMap x)
    (hg₂ : ∀ y : Ω ⊗[E₀] V₂,
      TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ Ω Ω V₁
        (g₂.baseChange Ω
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ Ω Ω V₂).symm y)) =
        φ.symm.toIntertwiningMap y) :
    {φE : (ρ₁.baseChange E).Equiv (ρ₂.baseChange E) //
      ∀ x : Ω ⊗[E₀] V₁,
        TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
          (φE.baseChange Ω
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁).symm x)) =
          φ x} := by
  let eV₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁
  let eV₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
  let fE_lin : E ⊗[E₀] V₁ →ₗ[E] E ⊗[E₀] V₂ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₂).toLinearMap ∘ₗ
      f₁.toLinearMap.baseChange E ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₁ E E V₁).symm.toLinearMap
  let gE_lin : E ⊗[E₀] V₂ →ₗ[E] E ⊗[E₀] V₁ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ E E V₁).toLinearMap ∘ₗ
      g₂.toLinearMap.baseChange E ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E₂ E E V₂).symm.toLinearMap
  have hfE_compat : ∀ x, eV₂ (fE_lin.baseChange Ω (eV₁.symm x)) = φ x :=
    compat_of_descent φ f₁ hf₁
  have hgE_compat : ∀ y, eV₁ (gE_lin.baseChange Ω (eV₂.symm y)) = φ.symm y :=
    compat_of_descent φ.symm g₂ hg₂
  have hgf : gE_lin ∘ₗ fE_lin = LinearMap.id :=
    comp_eq_id_of_compat fE_lin gE_lin φ φ.symm φ.symm_apply_apply hfE_compat hgE_compat
  have hfg : fE_lin ∘ₗ gE_lin = LinearMap.id :=
    comp_eq_id_of_compat gE_lin fE_lin φ.symm φ φ.apply_symm_apply hgE_compat hfE_compat
  let φE_lin : E ⊗[E₀] V₁ ≃ₗ[E] E ⊗[E₀] V₂ := LinearEquiv.ofLinearMap fE_lin gE_lin hfg hgf
  have hinter (g : G) : ∀ x, φE_lin (ρ₁.baseChange E g x) = ρ₂.baseChange E g (φE_lin x) := by
    suffices fE_lin ∘ₗ ρ₁.baseChange E g = ρ₂.baseChange E g ∘ₗ fE_lin from
      fun x ↦ LinearMap.congr_fun this x
    apply LinearMap.baseChange_injective (R := E) (A := Ω)
    rw [LinearMap.baseChange_comp (g := fE_lin) (f := ρ₁.baseChange E g),
      LinearMap.baseChange_comp (g := ρ₂.baseChange E g) (f := fE_lin)]
    apply LinearMap.ext
    intro z
    apply eV₂.injective
    calc eV₂ ((fE_lin.baseChange Ω ∘ₗ (ρ₁.baseChange E g).baseChange Ω) z)
        = eV₂ (fE_lin.baseChange Ω (eV₁.symm (eV₁ ((ρ₁.baseChange E g).baseChange Ω z)))) := by
          simp only [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
      _ = φ (ρ₁.baseChange Ω g (eV₁ z)) := by
          rw [hfE_compat, cancelBaseChange_baseChange_rep]
      _ = ρ₂.baseChange Ω g (φ (eV₁ z)) :=
          LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) (eV₁ z)
      _ = ρ₂.baseChange Ω g (eV₂ (fE_lin.baseChange Ω z)) := by
          rw [← hfE_compat (eV₁ z), LinearEquiv.symm_apply_apply]
      _ = eV₂ (((ρ₂.baseChange E g).baseChange Ω ∘ₗ fE_lin.baseChange Ω) z) := by
          rw [LinearMap.comp_apply, cancelBaseChange_baseChange_rep]
  let φE : (ρ₁.baseChange E).Equiv (ρ₂.baseChange E) :=
    Representation.Equiv.mk φE_lin fun g ↦ LinearMap.ext (hinter g)
  refine ⟨φE, fun x ↦ ?_⟩
  have hbase : ∀ z : Ω ⊗[E] (E ⊗[E₀] V₁), φE.baseChange Ω z = fE_lin.baseChange Ω z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
    | tmul c u =>
      rw [Equiv.baseChange_tmul, LinearMap.baseChange_tmul]
      rfl
  rw [hbase]
  exact hfE_compat x

/-- **Algebraic descent of an equivalence of representations along an algebraic field extension.**
If the scalar extensions of two finite-dimensional representations over `E₀` become equivalent over
an algebraic extension `Ω`, they are already equivalent over a finite intermediate field `E`,
compatibly with the given equivalence over `Ω`. -/
theorem exists_finiteDimensional_descent {E₀ Ω G V₁ V₂ : Type*}
    [Field E₀] [Field Ω] [Algebra E₀ Ω] [Algebra.IsAlgebraic E₀ Ω]
    [Monoid G] [AddCommGroup V₁] [Module E₀ V₁] [FiniteDimensional E₀ V₁]
    [AddCommGroup V₂] [Module E₀ V₂] [FiniteDimensional E₀ V₂]
    {ρ₁ : Representation E₀ G V₁} {ρ₂ : Representation E₀ G V₂}
    (φ : (ρ₁.baseChange Ω).Equiv (ρ₂.baseChange Ω)) :
    ∃ (E : IntermediateField E₀ Ω) (_ : FiniteDimensional E₀ E)
      (φE : (ρ₁.baseChange E).Equiv (ρ₂.baseChange E)),
      ∀ x : Ω ⊗[E₀] V₁,
        TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₂
          (φE.baseChange Ω
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange E₀ E Ω Ω V₁).symm x)) = φ x := by
  obtain ⟨E₁, hE₁, f₁, hf₁⟩ :=
    IntertwiningMap.exists_finiteDimensional_descent φ.toIntertwiningMap
  obtain ⟨E₂, hE₂, g₂, hg₂⟩ :=
    IntertwiningMap.exists_finiteDimensional_descent φ.symm.toIntertwiningMap
  let E : IntermediateField E₀ Ω := E₁ ⊔ E₂
  have hEfin : FiniteDimensional E₀ E := inferInstance
  let _ : Algebra E₁ E := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  let _ : Algebra E₂ E := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
  have : IsScalarTower E₀ E₁ E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower E₀ E₂ E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower E₁ E Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower E₂ E Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨φE, hφE⟩ := equivOfDescents (E := E) φ f₁ g₂ hf₁ hg₂
  exact ⟨E, hEfin, φE, hφE⟩

end Equiv

end Representation
