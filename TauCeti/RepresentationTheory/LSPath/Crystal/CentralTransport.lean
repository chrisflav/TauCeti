/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Central.Transport
public import TauCeti.RepresentationTheory.LSPath.Crystal.HighestWeight

import Mathlib.LinearAlgebra.TensorProduct.Tower
import TauCeti.RepresentationTheory.LSPath.OrbitStable

/-!
# Central transport as strict crystal isomorphisms on `B(λ)`

For a finite reduced root datum `(P, b)`, adding a central weight `χ` (one annihilating every simple
coroot) changes neither the walls through a dominant weight `λ` nor the reflection bonds of
`W / W_λ`, and shifts every realized Lakshmibai–Seshadri path by `t ↦ t • f χ`
(`TauCeti.LSPath.centralTransport`, `TauCeti.PLPath.shiftDistinguished`).

Since simple-coroot heights are invariant under adding a central straight path, central shift
commutes with Littelmann's raising and lowering operators
(`TauCeti.PLPath.raise_shiftDistinguished`) and shifts weights by `χ`. This upgrades
`LSPath.centralTransport` and `PLPath.shiftDistinguished` to strict crystal isomorphisms between
weight-twisted highest-weight crystals:

* **Cast-free general form**: whenever `λ₁ + a₁ = λ₂ + a₂` with dominant `λ₁, λ₂` and central
  weights `a₁, a₂`, `TauCeti.LSPath.centralShiftIso` and `TauCeti.PLPath.centralShiftComponentIso`
  give strict crystal isomorphisms `B(λ₁)^{a₁} ≃ B(λ₂)^{a₂}` whose underlying path maps depend only
  on `λ₂ - λ₁`, satisfying the exact identity, additive composition, and inverse laws on
  `NormalCrystal.StrictIso` without casts.
* **Standard parametrization `T_{λ, χ}^σ`**: specializing to `λ₂ = λ + χ`, `a₁ = σ + χ`, `a₂ = σ`
  gives `TauCeti.LSPath.centralTransportIso` and `TauCeti.PLPath.centralTransportComponentIso` of
  type `B(λ)^{σ + χ} ≃ B(λ + χ)^σ`, whose underlying maps are `LSPath.centralTransport χ` and
  `PLPath.shiftDistinguished _ (f χ)`, independent of `σ`, together with the `σ = 0` specialization
  `TauCeti.LSPath.centralTransportZeroIso : B(λ)^χ ≃ B(λ + χ)`.

## Main definitions

* `TauCeti.LSPath.centralShiftIso`, `TauCeti.LSPath.centralTransportIso`,
  `TauCeti.LSPath.centralTransportZeroIso`: central transport as strict crystal isomorphisms on
  `LSPath.normalCrystal`.
* `TauCeti.PLPath.centralShiftComponentIso`, `TauCeti.PLPath.centralTransportComponentIso`:
  central transport as strict crystal isomorphisms on the operator-generated straight-path
  components `PLPath.normalCrystalComponent`.

## Main results

* `TauCeti.LSPath.toPLPath_centralShiftIso`, `TauCeti.LSPath.coe_centralTransportIso`,
  `TauCeti.PLPath.centralShiftComponentIso_apply`,
  `TauCeti.PLPath.centralTransportComponentIso_apply`: the underlying path map is
  `PLPath.shiftDistinguished` by the central shift, independent of the ambient weight twist `σ`.
* `TauCeti.LSPath.centralShiftIso_refl`, `TauCeti.LSPath.centralShiftIso_trans`,
  `TauCeti.LSPath.centralShiftIso_symm`, `TauCeti.PLPath.centralShiftComponentIso_refl`,
  `TauCeti.PLPath.centralShiftComponentIso_trans`, `TauCeti.PLPath.centralShiftComponentIso_symm`:
  exact strict-isomorphism identity, additive composition, and inverse laws.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499–525, §§2, 4.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

public section

namespace TauCeti

open Module RootPairing Set
open scoped TensorProduct

/-! ### Central transport on `LSPath.normalCrystal` -/

namespace LSPath

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced]

omit [Finite ι] [P.IsReduced] in
private theorem coroot'_sub_eq_zero_of_add_eq_add {lam₁ lam₂ a₁ a₂ : X}
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂) :
    ∀ i ∈ b.support, P.coroot' i (lam₂ - lam₁) = 0 := by
  intro i hi
  have hsub : lam₂ - lam₁ = a₁ - a₂ := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm a₁, hsum]
  rw [hsub, map_sub]
  have h1 : P.coroot' i a₁ = 0 := ha₁ ⟨i, hi⟩
  have h2 : P.coroot' i a₂ = 0 := ha₂ ⟨i, hi⟩
  rw [h1, h2, sub_self]

private theorem length_cast {μ ν : X} (h : μ = ν) (π : LSPath P b μ) :
    (cast (congrArg (LSPath P b) h) π).length = π.length := by
  subst h; rfl

private theorem dir_cast {μ ν : X} (h : μ = ν) (π : LSPath P b μ)
    (j : Fin ((cast (congrArg (LSPath P b) h) π).length + 1)) :
    ((cast (congrArg (LSPath P b) h) π).dir j).1 =
      (π.dir (j.cast (by rw [length_cast h π]))).1 := by
  subst h; rfl

private theorem time_cast {μ ν : X} (h : μ = ν) (π : LSPath P b μ)
    (k : Fin ((cast (congrArg (LSPath P b) h) π).length + 2)) :
    (cast (congrArg (LSPath P b) h) π).time k =
      π.time (k.cast (by rw [length_cast h π])) := by
  subst h; rfl

private theorem toPLPath_cast {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : X →+ V) {μ ν : X} (h : μ = ν) (π : LSPath P b μ) :
    (cast (congrArg (LSPath P b) h) π).toPLPath 𝕜 f = π.toPLPath 𝕜 f := by
  subst h; rfl

private noncomputable def shiftEquiv {lam₁ lam₂ : X}
    (hsub : ∀ i ∈ b.support, P.coroot' i (lam₂ - lam₁) = 0) :
    LSPath P b lam₁ ≃ LSPath P b lam₂ :=
  (centralTransport (lam₂ - lam₁) hsub).trans
    (Equiv.cast (congrArg (LSPath P b) (add_sub_cancel lam₁ lam₂)))

private theorem length_shiftEquiv {lam₁ lam₂ : X}
    (hsub : ∀ i ∈ b.support, P.coroot' i (lam₂ - lam₁) = 0) (π : LSPath P b lam₁) :
    (shiftEquiv hsub π).length = π.length :=
  (length_cast (add_sub_cancel lam₁ lam₂) (centralTransport (lam₂ - lam₁) hsub π)).trans
    (length_centralTransport _ _ _)

private theorem dir_shiftEquiv {lam₁ lam₂ : X}
    (hsub : ∀ i ∈ b.support, P.coroot' i (lam₂ - lam₁) = 0) (π : LSPath P b lam₁)
    (j : Fin ((shiftEquiv hsub π).length + 1)) :
    ((shiftEquiv hsub π).dir j).1 = (π.dir (j.cast (by rw [length_shiftEquiv]))).1 :=
  (dir_cast (add_sub_cancel lam₁ lam₂) (centralTransport (lam₂ - lam₁) hsub π) j).trans
    (dir_centralTransport _ _ _ _)

private theorem time_shiftEquiv {lam₁ lam₂ : X}
    (hsub : ∀ i ∈ b.support, P.coroot' i (lam₂ - lam₁) = 0) (π : LSPath P b lam₁)
    (k : Fin ((shiftEquiv hsub π).length + 2)) :
    (shiftEquiv hsub π).time k = π.time (k.cast (by rw [length_shiftEquiv])) :=
  (time_cast (add_sub_cancel lam₁ lam₂) (centralTransport (lam₂ - lam₁) hsub π) k).trans
    (time_centralTransport _ _ _ _)

private theorem shiftEquiv_eq_centralTransport {lam χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (π : LSPath P b lam) :
    shiftEquiv (lam₁ := lam) (lam₂ := lam + χ) (by simpa [add_sub_cancel_left] using hχ) π =
      centralTransport χ hχ π := by
  apply LSPath.ext
  · apply List.ext_get
    · simp only [List.length_ofFn, length_shiftEquiv, length_centralTransport]
    · intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact Subtype.ext (by simp only [dir_shiftEquiv, dir_centralTransport, Fin.cast_mk])
  · apply List.ext_get
    · simp only [List.length_ofFn, length_shiftEquiv, length_centralTransport]
    · intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn, time_shiftEquiv, time_centralTransport,
        Fin.cast_mk]

private theorem toPLPath_shiftEquiv {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : X →+ V) {lam₁ lam₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b)
    (hsub : ∀ i ∈ b.support, P.coroot' i (lam₂ - lam₁) = 0)
    (hf : InjOn f (range fun w : P.weylGroup ↦ w • lam₁))
    (hS : (range fun w : P.weylGroup ↦ f (w • lam₁)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    (π : LSPath P b lam₁) :
    (shiftEquiv hsub π).toPLPath 𝕜 f =
      PLPath.shiftDistinguished (range fun w : P.weylGroup ↦ f (w • lam₁)) (f (lam₂ - lam₁))
        (π.toPLPath 𝕜 f) :=
  (toPLPath_cast f (add_sub_cancel lam₁ lam₂) (centralTransport (lam₂ - lam₁) hsub π)).trans
    (toPLPath_centralTransport (lam₂ - lam₁) hsub π 𝕜 f hlam₁ hf hS)

private theorem endpoint_toPLPath_shiftEquiv {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : X →+ V) {lam₁ lam₂ : X}
    (hsub : ∀ i ∈ b.support, P.coroot' i (lam₂ - lam₁) = 0) (π : LSPath P b lam₁) :
    ((shiftEquiv hsub π).toPLPath 𝕜 f).endpoint = (π.toPLPath 𝕜 f).endpoint + f (lam₂ - lam₁) :=
  (congrArg PLPath.endpoint
      (toPLPath_cast f (add_sub_cancel lam₁ lam₂) (centralTransport (lam₂ - lam₁) hsub π))).trans
    (endpoint_toPLPath_centralTransport (lam₂ - lam₁) hsub π 𝕜 f)

/-- **Cast-free central transport strict crystal isomorphism.** Whenever `λ₁ + a₁ = λ₂ + a₂` with
dominant weights `λ₁, λ₂` and central weights `a₁, a₂`, keeping the directions and breaks of each
LS path induces a strict crystal isomorphism `B(λ₁)^{a₁} ≃ B(λ₂)^{a₂}` whose underlying path map is
`PLPath.shiftDistinguished` by `λ₂ - λ₁`, independent of `a₁, a₂`. -/
noncomputable def centralShiftIso {lam₁ lam₂ a₁ a₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂) :
    NormalCrystal.StrictIso ((normalCrystal hlam₁).weightTwist a₁ ha₁)
      ((normalCrystal hlam₂).weightTwist a₂ ha₂) where
  toEquiv := shiftEquiv (coroot'_sub_eq_zero_of_add_eq_add ha₁ ha₂ hsum)
  wt_toFun π := by
    let f : X →+ ℚ ⊗[ℤ] X := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
    have hsub := coroot'_sub_eq_zero_of_add_eq_add ha₁ ha₂ hsum
    have hwt : (normalCrystal hlam₂).wt (shiftEquiv hsub π) =
        (normalCrystal hlam₁).wt π + (lam₂ - lam₁) := by
      have hf : f ((normalCrystal hlam₂).wt (shiftEquiv hsub π)) =
          f ((normalCrystal hlam₁).wt π + (lam₂ - lam₁)) := by
        rw [apply_normalCrystal_wt (𝕜 := ℚ) hlam₂ f, endpoint_toPLPath_shiftEquiv f hsub π,
          ← apply_normalCrystal_wt (𝕜 := ℚ) hlam₁ f π, map_add]
      exact P.tensorProduct_mk_injective ℚ
        (by simpa only [f, LinearMap.toAddMonoidHom_coe] using hf)
    have hdiff : lam₂ - lam₁ + a₂ = a₁ := by
      rw [sub_add_eq_add_sub, ← hsum, add_sub_cancel_left]
    simp only [NormalCrystal.weightTwist_wt, Equiv.toFun_as_coe, hwt, add_assoc, hdiff]
  e_toFun i π := by
    let f : X →+ ℚ ⊗[ℤ] X := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
    let F : b.support → Dual ℚ (ℚ ⊗[ℤ] X) := fun j ↦
      TensorProduct.AlgebraTensorModule.lift
        ((LinearMap.id (R := ℚ)).smulRight ((Int.castAddHom ℚ).toIntLinearMap.comp (P.coroot' j)))
    have hF : ∀ (j : b.support) (x : X), F j (f x) = (P.coroot' j x : ℚ) := fun j x ↦ by
      simp [f, F]
    have hsub := coroot'_sub_eq_zero_of_add_eq_add ha₁ ha₂ hsum
    set S : Set (ℚ ⊗[ℤ] X) := range fun w : P.weylGroup ↦ f (w • lam₁)
    have hS : MapsTo (preReflection (f (P.root i)) (F i)) S S := by
      simpa [S, MulAction.orbit, ← range_comp] using
        P.mapsTo_preReflection_image_orbit_weylGroup i.1 (hF i) lam₁
    have hS' : S.Pairwise fun u v ↦ ¬ SameRay ℚ u v :=
      P.pairwise_not_sameRay_range_smul b hF lam₁
    have hFdiff : F i (f (lam₂ - lam₁)) = 0 := by
      rw [hF i, hsub i.1 i.2, Int.cast_zero]
    have hshift (ρ : LSPath P b lam₁) :
        (shiftEquiv hsub ρ).toPLPath ℚ f =
          PLPath.shiftDistinguished S (f (lam₂ - lam₁)) (ρ.toPLPath ℚ f) :=
      toPLPath_shiftEquiv f hlam₁ hsub (P.tensorProduct_mk_injective ℚ).injOn hS' ρ
    have hcomm := PLPath.raise_shiftDistinguished (π.hasDistinguished_toPLPath ℚ f) hS hS' hFdiff
    simp only [NormalCrystal.weightTwist_e, Equiv.toFun_as_coe]
    cases he : (normalCrystal hlam₁).e i π with
    | none =>
      simp only [Option.map_none]
      rw [normalCrystal_e_eq_none_iff (f := f) (F := F) hlam₂ hF,
        hshift π, hcomm,
        (normalCrystal_e_eq_none_iff (f := f) (F := F) hlam₁ hF).mp he,
        Option.map_none]
    | some π' =>
      simp only [Option.map_some]
      rw [normalCrystal_e_eq_some_iff (f := f) (F := F) hlam₂
          (P.tensorProduct_mk_injective ℚ).injOn hF,
        hshift π, hshift π', hcomm,
        toPLPath_of_normalCrystal_e_eq_some (f := f) (F := F) hlam₁ hF he,
        Option.map_some]

@[simp]
theorem length_centralShiftIso {lam₁ lam₂ a₁ a₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂) (π : LSPath P b lam₁) :
    (centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum π).length = π.length :=
  length_shiftEquiv _ π

@[simp]
theorem dir_centralShiftIso {lam₁ lam₂ a₁ a₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂) (π : LSPath P b lam₁)
    (j : Fin ((centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum π).length + 1)) :
    ((centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum π).dir j).1 =
      (π.dir (j.cast (by rw [length_centralShiftIso]))).1 :=
  dir_shiftEquiv _ π j

@[simp]
theorem time_centralShiftIso {lam₁ lam₂ a₁ a₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂) (π : LSPath P b lam₁)
    (k : Fin ((centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum π).length + 2)) :
    (centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum π).time k =
      π.time (k.cast (by rw [length_centralShiftIso])) :=
  time_shiftEquiv _ π k

/-- On realized paths, `LSPath.centralShiftIso` acts by `PLPath.shiftDistinguished` by `λ₂ - λ₁`,
independent of the central twists `a₁, a₂`. -/
theorem toPLPath_centralShiftIso {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : X →+ V) {F : b.support → Dual 𝕜 V}
    {lam₁ lam₂ a₁ a₂ : X} (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂)
    (hf : InjOn f (range fun w : P.weylGroup ↦ w • lam₁))
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (π : LSPath P b lam₁) :
    (centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum π).toPLPath 𝕜 f =
      PLPath.shiftDistinguished (range fun w : P.weylGroup ↦ f (w • lam₁)) (f (lam₂ - lam₁))
        (π.toPLPath 𝕜 f) :=
  toPLPath_shiftEquiv f hlam₁ (coroot'_sub_eq_zero_of_add_eq_add ha₁ ha₂ hsum) hf
    (P.pairwise_not_sameRay_range_smul b hF lam₁) π

/-- **Identity law for central transport**: shifting by `0` is the identity strict isomorphism. -/
@[simp]
theorem centralShiftIso_refl {lam a : X} (hlam : lam ∈ dominantChamber P b)
    (ha : ∀ i : b.support, P.toLinearMap a (P.coroot i) = 0) :
    centralShiftIso hlam hlam ha ha rfl = NormalCrystal.StrictIso.refl _ := by
  apply NormalCrystal.StrictIso.ext
  intro π
  rw [NormalCrystal.StrictIso.refl_apply]
  apply LSPath.ext
  · apply List.ext_get
    · simp only [List.length_ofFn, length_centralShiftIso]
    · intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact Subtype.ext (by simp only [dir_centralShiftIso, Fin.cast_mk])
  · apply List.ext_get
    · simp only [List.length_ofFn, length_centralShiftIso]
    · intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn, time_centralShiftIso, Fin.cast_mk]

/-- **Additive composition law for central transport**: composing two central transport isomorphisms
equals the direct central transport isomorphism. -/
theorem centralShiftIso_trans {lam₁ lam₂ lam₃ a₁ a₂ a₃ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (hlam₃ : lam₃ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (ha₃ : ∀ i : b.support, P.toLinearMap a₃ (P.coroot i) = 0)
    (h₁₂ : lam₁ + a₁ = lam₂ + a₂) (h₂₃ : lam₂ + a₂ = lam₃ + a₃) :
    (centralShiftIso hlam₁ hlam₂ ha₁ ha₂ h₁₂).trans (centralShiftIso hlam₂ hlam₃ ha₂ ha₃ h₂₃) =
      centralShiftIso hlam₁ hlam₃ ha₁ ha₃ (h₁₂.trans h₂₃) := by
  apply NormalCrystal.StrictIso.ext
  intro π
  rw [NormalCrystal.StrictIso.trans_apply]
  apply LSPath.ext
  · apply List.ext_get
    · simp only [List.length_ofFn, length_centralShiftIso]
    · intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact Subtype.ext (by simp only [dir_centralShiftIso, Fin.cast_mk])
  · apply List.ext_get
    · simp only [List.length_ofFn, length_centralShiftIso]
    · intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn, time_centralShiftIso, Fin.cast_mk]

/-- **Inverse law for central transport**: inverting a central transport isomorphism is the reverse
central transport isomorphism. -/
theorem centralShiftIso_symm {lam₁ lam₂ a₁ a₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂) :
    (centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum).symm =
      centralShiftIso hlam₂ hlam₁ ha₂ ha₁ hsum.symm := by
  apply NormalCrystal.StrictIso.ext
  intro π
  apply (centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum).toEquiv.injective
  rw [NormalCrystal.StrictIso.coe_toEquiv, NormalCrystal.StrictIso.apply_symm_apply]
  have hcomp := congrArg (fun ψ ↦ ψ π)
    (centralShiftIso_trans hlam₂ hlam₁ hlam₂ ha₂ ha₁ ha₂ hsum.symm hsum)
  simpa using hcomp.symm

/-- **Central transport `T_{λ, χ}^σ : B(λ)^{σ + χ} ≃ B(λ + χ)^σ`.** Its underlying bijection is
`LSPath.centralTransport χ`, independent of `σ`. -/
noncomputable def centralTransportIso {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    NormalCrystal.StrictIso
      ((normalCrystal hlam).weightTwist (σ + χ) fun i ↦ by simp [map_add, hσ i, hχ i])
      ((normalCrystal (add_mem_dominantChamber P b hlam
        ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge))).weightTwist σ hσ) :=
  centralShiftIso hlam
    (add_mem_dominantChamber P b hlam ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge))
    (fun i ↦ by simp [map_add, hσ i, hχ i]) hσ (by abel)

/-- The underlying map of `T_{λ, χ}^σ` is `LSPath.centralTransport χ`, independent of `σ`. -/
@[simp]
theorem coe_centralTransportIso {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    ⇑(centralTransportIso hlam χ hχ σ hσ) = centralTransport χ fun i hi ↦ hχ ⟨i, hi⟩ := by
  funext π
  exact shiftEquiv_eq_centralTransport (fun i hi ↦ hχ ⟨i, hi⟩) π

/-- On realized paths, `T_{λ, χ}^σ` acts by `PLPath.shiftDistinguished` by `f χ`, independent of
`σ`. -/
theorem toPLPath_centralTransportIso {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : X →+ V) {F : b.support → Dual 𝕜 V}
    {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hf : InjOn f (range fun w : P.weylGroup ↦ w • lam))
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (π : LSPath P b lam) :
    (centralTransportIso hlam χ hχ σ hσ π).toPLPath 𝕜 f =
      PLPath.shiftDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) (f χ)
        (π.toPLPath 𝕜 f) := by
  rw [coe_centralTransportIso]
  exact toPLPath_centralTransport χ (fun i hi ↦ hχ ⟨i, hi⟩) π 𝕜 f hlam hf
    (P.pairwise_not_sameRay_range_smul b hF lam)

/-- On realized paths, `T_{λ, 0}^σ` is the identity. -/
theorem toPLPath_centralTransportIso_zero {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : X →+ V)
    {lam : X} (hlam : lam ∈ dominantChamber P b)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) (π : LSPath P b lam) :
    (centralTransportIso hlam 0 (by simp) σ hσ π).toPLPath 𝕜 f = π.toPLPath 𝕜 f := by
  rw [coe_centralTransportIso]
  exact toPLPath_centralTransport_zero π 𝕜 f

/-- On realized paths, `T_{λ + χ, ψ}^σ ∘ T_{λ, χ}^{σ + ψ}` agrees with `T_{λ, χ + ψ}^σ`. -/
theorem toPLPath_centralTransportIso_comp {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : X →+ V)
    {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (ψ : X) (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) (π : LSPath P b lam) :
    (centralTransportIso (add_mem_dominantChamber P b hlam
          ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge)) ψ hψ σ hσ
        (centralTransportIso hlam χ hχ (σ + ψ) (fun i ↦ by simp [map_add, hσ i, hψ i])
          π)).toPLPath 𝕜 f =
      (centralTransportIso hlam (χ + ψ) (fun i ↦ by simp [map_add, hχ i, hψ i]) σ hσ
        π).toPLPath 𝕜 f := by
  rw [coe_centralTransportIso, coe_centralTransportIso, coe_centralTransportIso]
  exact toPLPath_centralTransport_centralTransport χ (fun i hi ↦ hχ ⟨i, hi⟩) π 𝕜 f
    (fun i hi ↦ hψ ⟨i, hi⟩)

/-- On realized paths, `T_{λ + χ, -χ}^{σ + χ}` agrees with `(T_{λ, χ}^σ)⁻¹`. -/
theorem toPLPath_centralTransportIso_neg {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : X →+ V)
    {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) (π : LSPath P b (lam + χ)) :
    (centralTransportIso (add_mem_dominantChamber P b hlam
          ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge))
        (-χ) (fun i ↦ by simp [hχ i]) (σ + χ) (fun i ↦ by simp [map_add, hσ i, hχ i])
        π).toPLPath 𝕜 f =
      ((centralTransportIso hlam χ hχ σ hσ).symm π).toPLPath 𝕜 f := by
  have hsymm : (centralTransportIso hlam χ hχ σ hσ).symm π =
      (centralTransport χ fun i hi ↦ hχ ⟨i, hi⟩).symm π := by
    apply (centralTransportIso hlam χ hχ σ hσ).toEquiv.injective
    rw [NormalCrystal.StrictIso.coe_toEquiv, NormalCrystal.StrictIso.apply_symm_apply,
      coe_centralTransportIso, Equiv.apply_symm_apply]
  rw [coe_centralTransportIso, hsymm]
  exact toPLPath_centralTransport_neg χ (fun i hi ↦ hχ ⟨i, hi⟩) 𝕜 f π

/-- The `σ = 0` specialization of central transport: a strict crystal isomorphism
`B(λ)^χ ≃ B(λ + χ)` without a residual zero twist on the target. -/
noncomputable def centralTransportZeroIso {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    NormalCrystal.StrictIso ((normalCrystal hlam).weightTwist χ hχ)
      (normalCrystal (add_mem_dominantChamber P b hlam
        ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge))) where
  toEquiv := (centralShiftIso hlam
    (add_mem_dominantChamber P b hlam ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge))
    hχ (by simp : ∀ i : b.support, P.toLinearMap 0 (P.coroot i) = 0) (add_zero _).symm).toEquiv
  wt_toFun π := by
    have h := (centralShiftIso hlam
      (add_mem_dominantChamber P b hlam
        ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge))
      hχ (by simp : ∀ i : b.support, P.toLinearMap 0 (P.coroot i) = 0)
      (add_zero _).symm).wt_apply π
    simpa [NormalCrystal.weightTwist_wt, Equiv.toFun_as_coe] using h
  e_toFun i π := by
    have h := (centralShiftIso hlam
      (add_mem_dominantChamber P b hlam
        ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge))
      hχ (by simp : ∀ i : b.support, P.toLinearMap 0 (P.coroot i) = 0)
      (add_zero _).symm).e_apply i π
    simpa only [NormalCrystal.weightTwist_e, Equiv.toFun_as_coe,
      NormalCrystal.StrictIso.coe_toEquiv] using h

@[simp]
theorem coe_centralTransportZeroIso {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    ⇑(centralTransportZeroIso hlam χ hχ) = centralTransport χ fun i hi ↦ hχ ⟨i, hi⟩ := by
  funext π
  exact shiftEquiv_eq_centralTransport (fun i hi ↦ hχ ⟨i, hi⟩) π

end LSPath

/-! ### Central transport on operator-generated path components -/

namespace PLPath

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

omit [Finite ι] [P.IsReduced] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Module 𝕜 V] in
private theorem mapsTo_add_range_smul {lam χ : X}
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    MapsTo (· + f χ) (range fun w : P.weylGroup ↦ f (w • lam))
      (range fun w : P.weylGroup ↦ f (w • (lam + χ))) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨w, by
    simp only [smul_add, smul_eq_self_of_forall_coroot'_eq_zero b (fun i hi ↦ hχ ⟨i, hi⟩),
      map_add]⟩

/-- **Cast-free central transport on operator-generated straight-path components.** For dominant
weights `λ₁, λ₂` and central weights `a₁, a₂` with `λ₁ + a₁ = λ₂ + a₂`, central shift by
`f (λ₂ - λ₁)` induces a strict crystal isomorphism `B(λ₁)^{a₁} ≃ B(λ₂)^{a₂}` between the
operator-generated components, independent of `a₁, a₂` on underlying paths
(`TauCeti.PLPath.centralShiftComponentIso_apply`). -/
noncomputable def centralShiftComponentIso (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam₁ lam₂ a₁ a₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂) :
    NormalCrystal.StrictIso
      ((normalCrystalComponent hf hF
          ⟨straight 𝕜 (f lam₁),
            isIntegralPath_straight_of_mem_dominantChamber hlam₁ hF⟩).weightTwist a₁ ha₁)
      ((normalCrystalComponent hf hF
          ⟨straight 𝕜 (f lam₂),
            isIntegralPath_straight_of_mem_dominantChamber hlam₂ hF⟩).weightTwist a₂ ha₂) where
  toEquiv :=
    (LSPath.toPLPathComponentIso hf hF hlam₁).toEquiv.symm.trans
      ((LSPath.centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum).toEquiv.trans
        (LSPath.toPLPathComponentIso hf hF hlam₂).toEquiv)
  wt_toFun x := by
    set φ₁ := LSPath.toPLPathComponentIso hf hF hlam₁
    set φ₂ := LSPath.toPLPathComponentIso hf hF hlam₂
    set ψ := LSPath.centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum
    have h₁ := φ₁.symm.wt_apply x
    have h₂ := ψ.wt_apply (φ₁.symm x)
    have h₃ := φ₂.wt_apply (ψ (φ₁.symm x))
    simp only [NormalCrystal.weightTwist_wt, Equiv.toFun_as_coe, Equiv.trans_apply,
      NormalCrystal.StrictIso.coe_toEquiv_symm, NormalCrystal.StrictIso.coe_toEquiv] at h₂ ⊢
    rw [h₃, h₂, h₁]
  e_toFun i x := by
    set φ₁ := LSPath.toPLPathComponentIso hf hF hlam₁
    set φ₂ := LSPath.toPLPathComponentIso hf hF hlam₂
    set ψ := LSPath.centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum
    have h₁ := φ₁.symm.e_apply i x
    have h₂ := ψ.e_apply i (φ₁.symm x)
    have h₃ := φ₂.e_apply i (ψ (φ₁.symm x))
    simp only [NormalCrystal.weightTwist_e, Equiv.toFun_as_coe, Equiv.trans_apply,
      NormalCrystal.StrictIso.coe_toEquiv_symm, NormalCrystal.StrictIso.coe_toEquiv] at h₂ ⊢
    rw [h₃, h₂, h₁, Option.map_map, Option.map_map]
    congr 1
    funext y
    simp [Function.comp_def]

private theorem centralShiftComponentIso_eq (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam₁ lam₂ a₁ a₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂)
    (x : (normalCrystal hf hF).graph.connectedComponentMk
      ⟨straight 𝕜 (f lam₁), isIntegralPath_straight_of_mem_dominantChamber hlam₁ hF⟩) :
    centralShiftComponentIso hf hF hlam₁ hlam₂ ha₁ ha₂ hsum x =
      LSPath.toPLPathComponentIso hf hF hlam₂
        (LSPath.centralShiftIso hlam₁ hlam₂ ha₁ ha₂ hsum
          ((LSPath.toPLPathComponentIso hf hF hlam₁).symm x)) := by
  simp only [centralShiftComponentIso, NormalCrystal.StrictIso.coe_mk, Equiv.trans_apply,
    NormalCrystal.StrictIso.coe_toEquiv, NormalCrystal.StrictIso.coe_toEquiv_symm]

/-- The underlying path function of `PLPath.centralShiftComponentIso` is `PLPath.shiftDistinguished`
by `f (λ₂ - λ₁)`, independent of the central twists `a₁, a₂`. -/
@[simp]
theorem centralShiftComponentIso_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam₁ lam₂ a₁ a₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂)
    (x : (normalCrystal hf hF).graph.connectedComponentMk
      ⟨straight 𝕜 (f lam₁), isIntegralPath_straight_of_mem_dominantChamber hlam₁ hF⟩) :
    (centralShiftComponentIso hf hF hlam₁ hlam₂ ha₁ ha₂ hsum x).1.1 =
      shiftDistinguished (range fun w : P.weylGroup ↦ f (w • lam₁)) (f (lam₂ - lam₁)) x.1.1 := by
  rw [centralShiftComponentIso_eq, LSPath.toPLPathComponentIso_apply]
  set π := (LSPath.toPLPathComponentIso hf hF hlam₁).symm x
  have hx : π.toPLPath 𝕜 f = x.1.1 :=
    (LSPath.toPLPathComponentIso_apply hf hF hlam₁ π).symm.trans
      (congrArg (fun z ↦ z.1.1) ((LSPath.toPLPathComponentIso hf hF hlam₁).apply_symm_apply x))
  rw [← hx]
  exact LSPath.toPLPath_centralShiftIso f hlam₁ hlam₂ ha₁ ha₂ hsum hf.injOn hF π

/-- **Identity law on path components**: shifting by `0` is the identity strict isomorphism. -/
@[simp]
theorem centralShiftComponentIso_refl (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam a : X} (hlam : lam ∈ dominantChamber P b)
    (ha : ∀ i : b.support, P.toLinearMap a (P.coroot i) = 0) :
    centralShiftComponentIso hf hF hlam hlam ha ha rfl = NormalCrystal.StrictIso.refl _ := by
  apply NormalCrystal.StrictIso.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rw [centralShiftComponentIso_apply, sub_self, map_zero, NormalCrystal.StrictIso.refl_apply]
  obtain ⟨π, hπ⟩ := (LSPath.mem_supp_connectedComponentMk_straight_iff hf hF hlam x.1).mp x.2
  rw [← hπ, shiftDistinguished_zero (π.hasDistinguished_toPLPath 𝕜 f)]

/-- **Additive composition law on path components**: composing two central transport isomorphisms
equals the direct central transport isomorphism. -/
theorem centralShiftComponentIso_trans (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam₁ lam₂ lam₃ a₁ a₂ a₃ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (hlam₃ : lam₃ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (ha₃ : ∀ i : b.support, P.toLinearMap a₃ (P.coroot i) = 0)
    (h₁₂ : lam₁ + a₁ = lam₂ + a₂) (h₂₃ : lam₂ + a₂ = lam₃ + a₃) :
    (centralShiftComponentIso hf hF hlam₁ hlam₂ ha₁ ha₂ h₁₂).trans
        (centralShiftComponentIso hf hF hlam₂ hlam₃ ha₂ ha₃ h₂₃) =
      centralShiftComponentIso hf hF hlam₁ hlam₃ ha₁ ha₃ (h₁₂.trans h₂₃) := by
  apply NormalCrystal.StrictIso.ext
  intro x
  rw [NormalCrystal.StrictIso.trans_apply, centralShiftComponentIso_eq,
    centralShiftComponentIso_eq, centralShiftComponentIso_eq,
    NormalCrystal.StrictIso.symm_apply_apply]
  have h := congrArg (fun ψ ↦ ψ ((LSPath.toPLPathComponentIso hf hF hlam₁).symm x))
    (LSPath.centralShiftIso_trans hlam₁ hlam₂ hlam₃ ha₁ ha₂ ha₃ h₁₂ h₂₃)
  rw [NormalCrystal.StrictIso.trans_apply] at h
  exact congrArg (LSPath.toPLPathComponentIso hf hF hlam₃) h

/-- **Inverse law on path components**: inverting a central transport isomorphism is the reverse
central transport isomorphism. -/
theorem centralShiftComponentIso_symm (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam₁ lam₂ a₁ a₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (ha₁ : ∀ i : b.support, P.toLinearMap a₁ (P.coroot i) = 0)
    (ha₂ : ∀ i : b.support, P.toLinearMap a₂ (P.coroot i) = 0)
    (hsum : lam₁ + a₁ = lam₂ + a₂) :
    (centralShiftComponentIso hf hF hlam₁ hlam₂ ha₁ ha₂ hsum).symm =
      centralShiftComponentIso hf hF hlam₂ hlam₁ ha₂ ha₁ hsum.symm := by
  apply NormalCrystal.StrictIso.ext
  intro x
  apply (centralShiftComponentIso hf hF hlam₁ hlam₂ ha₁ ha₂ hsum).toEquiv.injective
  rw [NormalCrystal.StrictIso.coe_toEquiv, NormalCrystal.StrictIso.apply_symm_apply]
  have hcomp := congrArg (fun ψ ↦ ψ x)
    (centralShiftComponentIso_trans hf hF hlam₂ hlam₁ hlam₂ ha₂ ha₁ ha₂ hsum.symm hsum)
  simpa using hcomp.symm

/-- **Central transport `T_{λ, χ}^σ : B(λ)^{σ + χ} ≃ B(λ + χ)^σ`** on the operator-generated
straight-path components. Its underlying path map is `PLPath.shiftDistinguished` by `f χ`,
independent of `σ`. -/
noncomputable def centralTransportComponentIso (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    NormalCrystal.StrictIso
      ((normalCrystalComponent hf hF
          ⟨straight 𝕜 (f lam), isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩).weightTwist
        (σ + χ) fun i ↦ by simp [map_add, hσ i, hχ i])
      ((normalCrystalComponent hf hF
          ⟨straight 𝕜 (f (lam + χ)),
            isIntegralPath_straight_of_mem_dominantChamber
              (add_mem_dominantChamber P b hlam
                ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge)) hF⟩).weightTwist
        σ hσ) :=
  centralShiftComponentIso hf hF hlam
    (add_mem_dominantChamber P b hlam ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge))
    (fun i ↦ by simp [map_add, hσ i, hχ i]) hσ (by abel)

/-- The underlying path map of `T_{λ, χ}^σ` on path components is `PLPath.shiftDistinguished` by
`f χ`, independent of `σ`. -/
@[simp]
theorem centralTransportComponentIso_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (x : (normalCrystal hf hF).graph.connectedComponentMk
      ⟨straight 𝕜 (f lam), isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :
    (centralTransportComponentIso hf hF hlam χ hχ σ hσ x).1.1 =
      shiftDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) (f χ) x.1.1 := by
  simp [centralTransportComponentIso, add_sub_cancel_left]

/-- On underlying paths, `T_{λ, 0}^σ` is the identity. -/
theorem centralTransportComponentIso_zero_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam : X} (hlam : lam ∈ dominantChamber P b)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (x : (normalCrystal hf hF).graph.connectedComponentMk
      ⟨straight 𝕜 (f lam), isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :
    (centralTransportComponentIso hf hF hlam 0 (by simp) σ hσ x).1.1 = x.1.1 := by
  rw [centralTransportComponentIso_apply, map_zero]
  obtain ⟨π, hπ⟩ := (LSPath.mem_supp_connectedComponentMk_straight_iff hf hF hlam x.1).mp x.2
  rw [← hπ, shiftDistinguished_zero (π.hasDistinguished_toPLPath 𝕜 f)]

/-- On underlying paths, `T_{λ + χ, ψ}^σ ∘ T_{λ, χ}^{σ + ψ}` agrees with `T_{λ, χ + ψ}^σ`. -/
theorem centralTransportComponentIso_comp_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (ψ : X) (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (x : (normalCrystal hf hF).graph.connectedComponentMk
      ⟨straight 𝕜 (f lam), isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :
    (centralTransportComponentIso hf hF
        (add_mem_dominantChamber P b hlam
          ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge)) ψ hψ σ hσ
        (centralTransportComponentIso hf hF hlam χ hχ (σ + ψ)
          (fun i ↦ by simp [map_add, hσ i, hψ i]) x)).1.1 =
      (centralTransportComponentIso hf hF hlam (χ + ψ)
        (fun i ↦ by simp [map_add, hχ i, hψ i]) σ hσ x).1.1 := by
  rw [centralTransportComponentIso_apply, centralTransportComponentIso_apply,
    centralTransportComponentIso_apply]
  obtain ⟨π, hπ⟩ := (LSPath.mem_supp_connectedComponentMk_straight_iff hf hF hlam x.1).mp x.2
  rw [← hπ, shiftDistinguished_shiftDistinguished (π.hasDistinguished_toPLPath 𝕜 f)
    (mapsTo_add_range_smul hχ) (P.pairwise_not_sameRay_range_smul b hF (lam + χ)), map_add]

/-- On underlying paths, `T_{λ + χ, -χ}^{σ + χ}` agrees with `(T_{λ, χ}^σ)⁻¹`. -/
theorem centralTransportComponentIso_symm_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (x : (normalCrystal hf hF).graph.connectedComponentMk
      ⟨straight 𝕜 (f (lam + χ)),
        isIntegralPath_straight_of_mem_dominantChamber
          (add_mem_dominantChamber P b hlam
            ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge)) hF⟩) :
    ((centralTransportComponentIso hf hF hlam χ hχ σ hσ).symm x).1.1 =
      (centralTransportComponentIso hf hF
        (add_mem_dominantChamber P b hlam
          ((mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ ⟨i, hi⟩).ge))
        (-χ) (fun i ↦ by simp [hχ i]) (σ + χ) (fun i ↦ by simp [map_add, hσ i, hχ i]) x).1.1 := by
  have h1 := centralTransportComponentIso_apply hf hF hlam χ hχ σ hσ
    ((centralTransportComponentIso hf hF hlam χ hχ σ hσ).symm x)
  rw [NormalCrystal.StrictIso.apply_symm_apply] at h1
  rw [centralTransportComponentIso_apply, map_neg, h1]
  obtain ⟨π, hπ⟩ := (LSPath.mem_supp_connectedComponentMk_straight_iff hf hF hlam
    ((centralTransportComponentIso hf hF hlam χ hχ σ hσ).symm x).1).mp
    ((centralTransportComponentIso hf hF hlam χ hχ σ hσ).symm x).2
  rw [← hπ]
  exact (shiftDistinguished_neg_shiftDistinguished (π.hasDistinguished_toPLPath 𝕜 f)
    (mapsTo_add_range_smul hχ) (P.pairwise_not_sameRay_range_smul b hF (lam + χ))).symm

end PLPath

end TauCeti
