/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Nonlinear
public import TauCeti.Geometry.Manifold.FiberBundle.Vertical

/-!
# The first-jet bundle of a smooth fibre bundle

Let `E` be a fibre bundle over a manifold `B` modelled on `IB`, whose model fibre `F` is a
manifold modelled on `IF`, and let `TauCeti.ManifoldTotalSpace F E` be its total space charted
through the trivializations of `E` and product charts of `B × F`. A **first jet** of `E` at a point
`x : ManifoldTotalSpace F E` is a continuous linear right inverse
`tangentLift : T_{π x} B →L[𝕜] T_x E` to the manifold derivative of the bundle projection at `x`.
No vector-space structure or canonical zero jet exists on `FirstJet IB IF F E x`: in the preferred
product chart at `x`, `FirstJet.chartCoordEquiv` identifies first jets with continuous linear maps
`EB →L[𝕜] EF` via `A ↦ (id, A)`, and changing charts acts by the nonlinear affine transition map
`FirstJet.coordChange` whose inhomogeneous shift depends on the chart.

When `B`, `F` and `E` are `C^1`, each first jet `j` at `x` determines a vertical **contact
projection** `j.contactForm : T_x E →L[𝕜] V_x E` retracting `VerticalBundle.toTangent x` with
kernel equal to the horizontal subspace `range j.tangentLift`. Subtracting two horizontal lifts
lands in `V_x E`, making `FirstJet IB IF F E x` an affine torsor (`AddTorsor`) over the space of
continuous linear maps `T_{π x} B →L[𝕜] V_x E`; in local coordinates the inhomogeneous chart terms
cancel (`FirstJet.coordChange_sub`). Assembling the preferred-chart coordinates in a
`FiberPrebundle` equips `TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E)` with a `C^n` fibre bundle
structure over `ManifoldTotalSpace F E` whenever `B`, `F` and `E` are `C^(n+1)`, with smooth
surjective truncation `TotalSpace.proj : J¹E → E`, smooth composite projection to `B`, and smooth
contact evaluation `FirstJet.contMDiff_contactForm`.

Holonomic prolongation of local and global sections, first-jet connections, and the canonical `C^n`
diffeomorphism with `TauCeti.FirstJetBundle` when `E` is a vector bundle are developed in
`TauCeti.Geometry.Manifold.FiberBundle.FirstJet.Prolongation`.

## Main definitions

* `TauCeti.FirstJet`: the type of first jets of `E` at `x : ManifoldTotalSpace F E`, defined
  intrinsically as continuous linear splittings of `mfderiv proj x`.
* `TauCeti.FirstJet.chartCoordEquiv`: the equivalence `FirstJet IB IF F E x ≃ (EB →L[𝕜] EF)` in
  the preferred chart at `x`.
* `TauCeti.FirstJet.contactForm`: the vertical contact retraction `T_x E →L[𝕜] V_x E` of a first
  jet, and the `AddTorsor (T_{π x} B →L[𝕜] V_x E) (FirstJet IB IF F E x)` instance.
* `TauCeti.FirstJet.coordChange` and `TauCeti.firstJetPrebundle`: the nonlinear affine coordinate
  changes and the resulting `FiberBundle` and `ContMDiffFiberBundle` structures on `J¹E → E`.

## Main results

* `TauCeti.FirstJet.ker_contactForm`: the kernel of `j.contactForm` is `range j.tangentLift`.
* `TauCeti.FirstJet.coordChange_comp`, `TauCeti.FirstJet.coordChange_sub`, and
  `TauCeti.FirstJet.coordChange_eq_firstJetCoordChange`: cocycle law, tensorial difference law, and
  agreement with `TauCeti.firstJetCoordChange`.
* `TauCeti.FirstJet.contMDiffFiberBundle`: `J¹E → E` is a `C^n` fibre bundle when `B`, `F` and `E`
  are `C^(n+1)`.
* `TauCeti.FirstJet.contMDiff_contactForm`: smoothness of contact-form evaluation into `VE`.

## References

* I. M. Anderson, *The Variational Bicomplex*, Chapter 1, §A (jet coordinates and contact forms).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§12.1–12.6, 12.16–12.17 (first-jet bundles and affine torsor structure).
-/

public section

noncomputable section

open Bundle Set Filter ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  (IF : ModelWithCorners 𝕜 EF HF)
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (F : Type*) [TopologicalSpace F] [ChartedSpace HF F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

/-- **A first jet of a fibre bundle `E → B` at `x : ManifoldTotalSpace F E`.** Intrinsically, a
first jet at `x` is a continuous linear horizontal lift `T_{π x} B →L[𝕜] T_x E` splitting the
manifold derivative of the bundle projection at `x`. No zero element or linear structure is assumed
or induced on `FirstJet IB IF F E x`. -/
@[ext]
structure FirstJet (x : ManifoldTotalSpace F E) where
  /-- The horizontal tangent lift `T_{π x} B →L[𝕜] T_x E` associated with the first jet. -/
  tangentLift :
    TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj →L[𝕜]
      TangentSpace (IB.prod IF) x
  /-- The horizontal lift is a right inverse to the manifold derivative of the projection. -/
  mfderiv_proj_comp_tangentLift :
    (mfderiv (IB.prod IF) IB
      (fun y : ManifoldTotalSpace F E ↦
        ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x).comp tangentLift =
      ContinuousLinearMap.id 𝕜
        (TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj)

namespace FirstJet

variable {IB IF F E}

/-- Applying the derivative of the bundle projection to `j.tangentLift u` recovers `u`. -/
@[simp]
theorem mfderiv_proj_tangentLift {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x)
    (u : TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj) :
    mfderiv (IB.prod IF) IB
      (fun y : ManifoldTotalSpace F E ↦ ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x
      (j.tangentLift u) = u :=
  DFunLike.congr_fun j.mfderiv_proj_comp_tangentLift u

/-- Every first-jet horizontal lift is injective. -/
theorem tangentLift_injective {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    Function.Injective j.tangentLift :=
  Function.LeftInverse.injective j.mfderiv_proj_tangentLift

/-- In the preferred chart at `x`, the first coordinate of `j.tangentLift` is the identity. -/
@[simp]
theorem fst_comp_tangentLift {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    (ContinuousLinearMap.fst 𝕜 EB EF).comp j.tangentLift = ContinuousLinearMap.id 𝕜 EB := by
  rw [← ManifoldTotalSpace.mfderiv_proj (IB := IB) (IF := IF) x]
  exact j.mfderiv_proj_comp_tangentLift

/-- Pointwise first coordinate of `j.tangentLift` in the preferred chart at `x`. -/
@[simp]
theorem tangentLift_fst {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) (u : EB) :
    (j.tangentLift u).1 = u :=
  DFunLike.congr_fun j.fst_comp_tangentLift u

variable (IB IF F E) in
/-- **Preferred-chart derivative coordinate of a first jet.** In the preferred product chart at `x`,
a splitting `j` of `fst : EB × EF →L[𝕜] EB` is uniquely determined by its vertical component
`(snd 𝕜 EB EF).comp j.tangentLift : EB →L[𝕜] EF`, with inverse `A ↦ (id 𝕜 EB).prod A`. -/
def chartCoordEquiv (x : ManifoldTotalSpace F E) : FirstJet IB IF F E x ≃ (EB →L[𝕜] EF) where
  toFun j := (ContinuousLinearMap.snd 𝕜 EB EF).comp j.tangentLift
  invFun A :=
    { tangentLift := (ContinuousLinearMap.id 𝕜 EB).prod A
      mfderiv_proj_comp_tangentLift := by
        rw [ManifoldTotalSpace.mfderiv_proj]
        rfl }
  left_inv j := by
    ext u
    exact Prod.ext (j.tangentLift_fst u).symm rfl
  right_inv _ := rfl

/-- `chartCoordEquiv` extracts the vertical component of `j.tangentLift` in the preferred chart. -/
theorem chartCoordEquiv_apply (x : ManifoldTotalSpace F E) (j : FirstJet IB IF F E x) :
    chartCoordEquiv IB IF F E x j = (ContinuousLinearMap.snd 𝕜 EB EF).comp j.tangentLift :=
  (rfl)

@[simp]
theorem tangentLift_chartCoordEquiv_symm (x : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    ((chartCoordEquiv IB IF F E x).symm A).tangentLift =
      (ContinuousLinearMap.id 𝕜 EB).prod A :=
  (rfl)

/-- Reassembling the identity first coordinate with `chartCoordEquiv` recovers `j.tangentLift`. -/
theorem id_prod_chartCoordEquiv {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    (ContinuousLinearMap.id 𝕜 EB).prod (chartCoordEquiv IB IF F E x j) = j.tangentLift :=
  congrArg FirstJet.tangentLift ((chartCoordEquiv IB IF F E x).symm_apply_apply j)

instance instNonempty (x : ManifoldTotalSpace F E) : Nonempty (FirstJet IB IF F E x) :=
  ⟨(chartCoordEquiv IB IF F E x).symm 0⟩

instance instTopologicalSpaceFiber (x : ManifoldTotalSpace F E) :
    TopologicalSpace (FirstJet IB IF F E x) :=
  TopologicalSpace.induced (chartCoordEquiv IB IF F E x) inferInstance

variable (IB IF F E) in
/-- Homeomorphism between the fibre `FirstJet IB IF F E x` and the normed space `EB →L[𝕜] EF` of
derivative coordinates in the preferred chart at `x`. -/
def chartCoordHomeomorph (x : ManifoldTotalSpace F E) :
    FirstJet IB IF F E x ≃ₜ (EB →L[𝕜] EF) :=
  (chartCoordEquiv IB IF F E x).toHomeomorphOfIsInducing ⟨rfl⟩

/-! ### Vertical contact projection and affine torsor structure -/

section ContactAndTorsor

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- **The vertical contact projection `θ₀(j) : T_x E →L[𝕜] V_x E` of a first jet.** It subtracts
the horizontal lift of the projected base tangent vector from a tangent vector at `x`, landing in
`ker (dπ_x) ≃L[𝕜] V_x E`. -/
def contactForm {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    TangentSpace (IB.prod IF) x →L[𝕜] VerticalBundle IB IF F E x :=
  (VerticalBundle.equivKer x).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id 𝕜 (TangentSpace (IB.prod IF) x)) -
      j.tangentLift.comp (mfderiv (IB.prod IF) IB
        (fun y : ManifoldTotalSpace F E ↦
          ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x)).codRestrict _ fun w ↦ by
      rw [LinearMap.mem_ker, sub_apply, comp_apply, id_apply, map_sub,
        ContinuousLinearMap.coe_coe, j.mfderiv_proj_tangentLift, sub_self])

/-- Embedding `j.contactForm w` into `T_x E` gives `w - j.tangentLift (dπ_x w)`. -/
@[simp]
theorem toTangent_contactForm {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x)
    (w : TangentSpace (IB.prod IF) x) :
    VerticalBundle.toTangent x (j.contactForm w) =
      w - j.tangentLift (mfderiv (IB.prod IF) IB
        (fun y : ManifoldTotalSpace F E ↦
          ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x w) :=
  VerticalBundle.toTangent_equivKer_symm x _

/-- Operator form of the splitting `toTangent ∘ contactForm = id - tangentLift ∘ dπ`. -/
theorem toTangent_comp_contactForm {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    (VerticalBundle.toTangent x).comp j.contactForm =
      ContinuousLinearMap.id 𝕜 (TangentSpace (IB.prod IF) x) -
        j.tangentLift.comp (mfderiv (IB.prod IF) IB
          (fun y : ManifoldTotalSpace F E ↦
            ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x) :=
  ContinuousLinearMap.ext (toTangent_contactForm j)

/-- `j.contactForm` retracts the vertical inclusion `VerticalBundle.toTangent x`. -/
@[simp]
theorem contactForm_toTangent {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x)
    (v : VerticalBundle IB IF F E x) :
    j.contactForm (VerticalBundle.toTangent x v) = v := by
  apply VerticalBundle.toTangent_injective x
  rw [toTangent_contactForm, VerticalBundle.mfderiv_proj_toTangent, map_zero, sub_zero]

/-- `j.contactForm ∘ toTangent = id` on the vertical fibre at `x`. -/
@[simp]
theorem contactForm_comp_toTangent {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    j.contactForm.comp (VerticalBundle.toTangent x) =
      ContinuousLinearMap.id 𝕜 (VerticalBundle IB IF F E x) :=
  ContinuousLinearMap.ext (contactForm_toTangent j)

/-- `j.contactForm` vanishes on every horizontal vector `j.tangentLift u`. -/
@[simp]
theorem contactForm_tangentLift {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x)
    (u : TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj) :
    j.contactForm (j.tangentLift u) = 0 := by
  apply VerticalBundle.toTangent_injective x
  rw [map_zero, toTangent_contactForm, j.mfderiv_proj_tangentLift, sub_self]

/-- Operator form of `contactForm_tangentLift`. -/
@[simp]
theorem contactForm_comp_tangentLift {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    j.contactForm.comp j.tangentLift = 0 :=
  ContinuousLinearMap.ext (contactForm_tangentLift j)

/-- **Exactness of the contact splitting.** The kernel of `j.contactForm` is the horizontal image of
`j.tangentLift`. -/
theorem ker_contactForm {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    LinearMap.ker j.contactForm.toLinearMap = LinearMap.range j.tangentLift.toLinearMap := by
  ext w
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, LinearMap.mem_range]
  refine ⟨fun hw ↦ ⟨mfderiv (IB.prod IF) IB
      (fun y : ManifoldTotalSpace F E ↦ ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x w, ?_⟩,
    ?_⟩
  · have h0 := congrArg (VerticalBundle.toTangent x) hw
    rw [toTangent_contactForm, map_zero, sub_eq_zero] at h0
    exact h0.symm
  · rintro ⟨u, rfl⟩
    exact j.contactForm_tangentLift u

/-- In the preferred chart at `x`, `j.contactForm (u, v) = v - A u` where `A` is the chart
derivative coordinate of `j`. -/
theorem contactForm_apply_chart {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x)
    (w : EB × EF) :
    (show EF from j.contactForm w) = w.2 - chartCoordEquiv IB IF F E x j w.1 := by
  have h := congrArg Prod.snd (j.toTangent_contactForm w)
  rw [VerticalBundle.toTangent_apply, ManifoldTotalSpace.mfderiv_proj] at h
  exact h

instance instVAdd (x : ManifoldTotalSpace F E) :
    VAdd (TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj →L[𝕜]
      VerticalBundle IB IF F E x) (FirstJet IB IF F E x) where
  vadd L j :=
    { tangentLift := (VerticalBundle.toTangent x).comp L + j.tangentLift
      mfderiv_proj_comp_tangentLift := by
        rw [comp_add, ← comp_assoc, VerticalBundle.mfderiv_proj_comp_toTangent, zero_comp,
          zero_add, j.mfderiv_proj_comp_tangentLift] }

@[simp]
theorem tangentLift_vadd {x : ManifoldTotalSpace F E}
    (L : TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj →L[𝕜]
      VerticalBundle IB IF F E x)
    (j : FirstJet IB IF F E x) :
    (L +ᵥ j).tangentLift = (VerticalBundle.toTangent x).comp L + j.tangentLift :=
  (rfl)

instance instVSub (x : ManifoldTotalSpace F E) :
    VSub (TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj →L[𝕜]
      VerticalBundle IB IF F E x) (FirstJet IB IF F E x) where
  vsub j₁ j₂ := j₂.contactForm.comp j₁.tangentLift

theorem vsub_def {x : ManifoldTotalSpace F E} (j₁ j₂ : FirstJet IB IF F E x) :
    j₁ -ᵥ j₂ = j₂.contactForm.comp j₁.tangentLift :=
  (rfl)

/-- **Each first-jet fibre `J¹_x E` is an affine torsor over `Hom(T_{π x} B, V_x E)`.** -/
instance instAddTorsor (x : ManifoldTotalSpace F E) :
    AddTorsor (TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj →L[𝕜]
      VerticalBundle IB IF F E x) (FirstJet IB IF F E x) where
  zero_vadd j := by
    ext u
    simp [tangentLift_vadd]
  add_vadd L₁ L₂ j := by
    ext u
    simp [tangentLift_vadd, add_assoc]
  vsub_vadd' j₁ j₂ := by
    ext u
    rw [tangentLift_vadd, add_apply, vsub_def, comp_apply, comp_apply, toTangent_contactForm,
      j₁.mfderiv_proj_tangentLift, sub_add_cancel]
  vadd_vsub' L j := by
    ext u
    rw [vsub_def, comp_apply, tangentLift_vadd, add_apply, map_add, comp_apply,
      contactForm_toTangent, contactForm_tangentLift, add_zero]

/-- Embedding `j₁ -ᵥ j₂` into `T_x E` gives the difference of horizontal lifts
`j₁.tangentLift - j₂.tangentLift`. -/
@[simp]
theorem toTangent_comp_vsub {x : ManifoldTotalSpace F E} (j₁ j₂ : FirstJet IB IF F E x) :
    (VerticalBundle.toTangent x).comp (j₁ -ᵥ j₂) = j₁.tangentLift - j₂.tangentLift := by
  ext u
  rw [comp_apply, vsub_def, comp_apply, toTangent_contactForm, j₁.mfderiv_proj_tangentLift,
    sub_apply]

/-- Translating a jet by `L : T_{π x} B →L[𝕜] V_x E` shifts its contact form by `- L ∘ dπ_x`. -/
@[simp]
theorem contactForm_vadd {x : ManifoldTotalSpace F E}
    (L : TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj →L[𝕜]
      VerticalBundle IB IF F E x)
    (j : FirstJet IB IF F E x) :
    (L +ᵥ j).contactForm =
      j.contactForm - L.comp (mfderiv (IB.prod IF) IB
        (fun y : ManifoldTotalSpace F E ↦
          ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x) := by
  ext w
  apply VerticalBundle.toTangent_injective x
  rw [sub_apply, map_sub, toTangent_contactForm, toTangent_contactForm, tangentLift_vadd,
    add_apply, comp_apply, comp_apply]
  abel

/-- The difference of the contact forms of two jets at `x` factors through `dπ_x` via `j₂ -ᵥ j₁`. -/
theorem contactForm_sub_contactForm {x : ManifoldTotalSpace F E} (j₁ j₂ : FirstJet IB IF F E x) :
    j₁.contactForm - j₂.contactForm =
      (j₂ -ᵥ j₁).comp (mfderiv (IB.prod IF) IB
        (fun y : ManifoldTotalSpace F E ↦
          ((ManifoldTotalSpace.homeomorph F E).symm y).proj) x) := by
  have h := contactForm_vadd (j₂ -ᵥ j₁) j₁
  rw [vsub_vadd] at h
  rw [h, sub_sub_cancel]

/-- In the preferred chart at `x`, `chartCoordEquiv` carries `L +ᵥ j` to `L + chartCoordEquiv x j`
pointwise. -/
theorem chartCoordEquiv_vadd_apply {x : ManifoldTotalSpace F E}
    (L : TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj →L[𝕜]
      VerticalBundle IB IF F E x)
    (j : FirstJet IB IF F E x) (u : EB) :
    chartCoordEquiv IB IF F E x (L +ᵥ j) u =
      (show EF from L u) + chartCoordEquiv IB IF F E x j u := by
  let u' : TangentSpace IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj := u
  have h := DFunLike.congr_fun (tangentLift_vadd L j) u'
  rw [add_apply, comp_apply, VerticalBundle.toTangent_apply] at h
  exact congrArg Prod.snd h

/-- In the preferred chart at `x`, `j₁ -ᵥ j₂` acts pointwise as the difference of
`chartCoordEquiv` coordinates. -/
theorem vsub_apply_chart {x : ManifoldTotalSpace F E} (j₁ j₂ : FirstJet IB IF F E x) (u : EB) :
    (show EF from (j₁ -ᵥ j₂) u) =
      chartCoordEquiv IB IF F E x j₁ u - chartCoordEquiv IB IF F E x j₂ u := by
  let w : EB × EF := j₁.tangentLift u
  have h1 := j₂.contactForm_apply_chart w
  have h2 : w.1 = u := j₁.tangentLift_fst u
  have h3 : w.2 = chartCoordEquiv IB IF F E x j₁ u := rfl
  rw [h2, h3] at h1
  exact h1

end ContactAndTorsor

/-! ### Nonlinear affine coordinate changes and smooth fibre bundle structure -/

section Bundle

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

variable (IB IF F E) in
/-- **First-jet coordinate change on `ManifoldTotalSpace F E`.** It conjugates the graph
`(id 𝕜 EB).prod A` by the base tangent coordinate change from `π j` to `π i` and the total-space
tangent coordinate change from `i` to `j`, then projects onto the vertical factor `EF`. -/
def coordChange (i j x : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) : EB →L[𝕜] EF :=
  (ContinuousLinearMap.snd 𝕜 EB EF).comp
    ((tangentCoordChange (IB.prod IF) i j x).comp
      (((ContinuousLinearMap.id 𝕜 EB).prod A).comp
        (tangentCoordChange IB
          ((ManifoldTotalSpace.homeomorph F E).symm j).proj
          ((ManifoldTotalSpace.homeomorph F E).symm i).proj
          ((ManifoldTotalSpace.homeomorph F E).symm x).proj)))

/-- Explicit formula for `FirstJet.coordChange`. -/
theorem coordChange_apply (i j x : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    coordChange IB IF F E i j x A =
      (ContinuousLinearMap.snd 𝕜 EB EF).comp
        ((tangentCoordChange (IB.prod IF) i j x).comp
          (((ContinuousLinearMap.id 𝕜 EB).prod A).comp
            (tangentCoordChange IB
              ((ManifoldTotalSpace.homeomorph F E).symm j).proj
              ((ManifoldTotalSpace.homeomorph F E).symm i).proj
              ((ManifoldTotalSpace.homeomorph F E).symm x).proj))) :=
  (rfl)

/-- **Intertwining of `FirstJet.coordChange` with tangent coordinate changes.** Because the
tangent coordinate changes of `ManifoldTotalSpace F E` are block-triangular, conjugating a graph
`(id, A)` produces the graph `(id, coordChange i j x A)`. -/
theorem id_prod_coordChange {i j x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source)
    (A : EB →L[𝕜] EF) :
    (ContinuousLinearMap.id 𝕜 EB).prod (coordChange IB IF F E i j x A) =
      (tangentCoordChange (IB.prod IF) i j x).comp
        (((ContinuousLinearMap.id 𝕜 EB).prod A).comp
          (tangentCoordChange IB
            ((ManifoldTotalSpace.homeomorph F E).symm j).proj
            ((ManifoldTotalSpace.homeomorph F E).symm i).proj
            ((ManifoldTotalSpace.homeomorph F E).symm x).proj)) := by
  have hbi : ((ManifoldTotalSpace.homeomorph F E).symm x).proj ∈
      (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.1).2
  have hbj : ((ManifoldTotalSpace.homeomorph F E).symm x).proj ∈
      (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm j).proj).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.2).2
  have hfst : (ContinuousLinearMap.fst 𝕜 EB EF).comp
      ((tangentCoordChange (IB.prod IF) i j x).comp
        (((ContinuousLinearMap.id 𝕜 EB).prod A).comp
          (tangentCoordChange IB
            ((ManifoldTotalSpace.homeomorph F E).symm j).proj
            ((ManifoldTotalSpace.homeomorph F E).symm i).proj
            ((ManifoldTotalSpace.homeomorph F E).symm x).proj))) =
      ContinuousLinearMap.id 𝕜 EB := by
    rw [← comp_assoc, ManifoldTotalSpace.fst_comp_tangentCoordChange hx, comp_assoc,
      ← comp_assoc (ContinuousLinearMap.fst 𝕜 EB EF), fst_comp_prod, id_comp]
    ext u
    exact (tangentCoordChange_comp ⟨⟨hbj, hbi⟩, hbj⟩).trans (tangentCoordChange_self hbj)
  ext u
  · exact (DFunLike.congr_fun hfst u).symm
  · rfl

/-- `FirstJet.coordChange` from a chart to itself is the identity on its source. -/
theorem coordChange_self {i x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source) (A : EB →L[𝕜] EF) :
    coordChange IB IF F E i i x A = A := by
  have hxi : x ∈ (extChartAt (IB.prod IF) i).source := by rwa [extChartAt_source]
  have hbi : ((ManifoldTotalSpace.homeomorph F E).symm x).proj ∈
      (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx).2
  ext u
  simp only [coordChange, comp_apply, tangentCoordChange_self hbi,
    ContinuousLinearMap.prod_apply, id_apply, tangentCoordChange_self hxi, coe_snd']

/-- **Cocycle law for first-jet coordinate changes.** -/
theorem coordChange_comp {i j k x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source ∩
      (chartAt (ModelProd HB HF) k).source) (A : EB →L[𝕜] EF) :
    coordChange IB IF F E j k x (coordChange IB IF F E i j x A) =
      coordChange IB IF F E i k x A := by
  have hxi : x ∈ (extChartAt (IB.prod IF) i).source := by rw [extChartAt_source]; exact hx.1.1
  have hxj : x ∈ (extChartAt (IB.prod IF) j).source := by rw [extChartAt_source]; exact hx.1.2
  have hxk : x ∈ (extChartAt (IB.prod IF) k).source := by rw [extChartAt_source]; exact hx.2
  have hbi : ((ManifoldTotalSpace.homeomorph F E).symm x).proj ∈
      (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.1.1).2
  have hbj : ((ManifoldTotalSpace.homeomorph F E).symm x).proj ∈
      (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm j).proj).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.1.2).2
  have hbk : ((ManifoldTotalSpace.homeomorph F E).symm x).proj ∈
      (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm k).proj).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.2).2
  have hgraph : (ContinuousLinearMap.id 𝕜 EB).prod
      (coordChange IB IF F E j k x (coordChange IB IF F E i j x A)) =
      (ContinuousLinearMap.id 𝕜 EB).prod (coordChange IB IF F E i k x A) := by
    rw [id_prod_coordChange ⟨hx.1.2, hx.2⟩, id_prod_coordChange ⟨hx.1.1, hx.1.2⟩,
      id_prod_coordChange ⟨hx.1.1, hx.2⟩]
    ext u <;>
    · simp only [comp_apply]
      rw [tangentCoordChange_comp ⟨⟨hbk, hbj⟩, hbi⟩, tangentCoordChange_comp ⟨⟨hxi, hxj⟩, hxk⟩]
  simpa only [snd_comp_prod] using congrArg (ContinuousLinearMap.snd 𝕜 EB EF).comp hgraph

/-- **Tensorial difference law for `FirstJet.coordChange`.** At a fixed point `x`, the nonlinear
inhomogeneous term cancels in a difference of derivative coordinates, leaving conjugation by the
base tangent coordinate change and `VerticalBundle.coordChange`. -/
theorem coordChange_sub (i j x : ManifoldTotalSpace F E) (A₁ A₂ : EB →L[𝕜] EF) :
    coordChange IB IF F E i j x A₁ - coordChange IB IF F E i j x A₂ =
      (VerticalBundle.coordChange IB IF F E i j x).comp
        ((A₁ - A₂).comp (tangentCoordChange IB
          ((ManifoldTotalSpace.homeomorph F E).symm j).proj
          ((ManifoldTotalSpace.homeomorph F E).symm i).proj
          ((ManifoldTotalSpace.homeomorph F E).symm x).proj)) := by
  ext u
  simp only [coordChange, sub_apply, comp_apply, VerticalBundle.coordChange_apply, coe_snd',
    ContinuousLinearMap.prod_apply, id_apply]
  rw [← Prod.snd_sub, ← map_sub (tangentCoordChange (IB.prod IF) i j x), Prod.mk_sub_mk, sub_self]

/-- **Agreement with `TauCeti.firstJetCoordChange`.** On boundaryless models, `FirstJet.coordChange`
coincides with the derivative component of `TauCeti.firstJetCoordChange` for the base chart
transition `h` from `π j` to `π i` and the nonlinear fibre transition `g(z, w)` read in the
extended charts of `ManifoldTotalSpace F E`. -/
theorem coordChange_eq_firstJetCoordChange [IB.Boundaryless] [IF.Boundaryless]
    {i j x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source)
    (A : EB →L[𝕜] EF) :
    let ib := ((ManifoldTotalSpace.homeomorph F E).symm i).proj
    let jb := ((ManifoldTotalSpace.homeomorph F E).symm j).proj
    let xb := ((ManifoldTotalSpace.homeomorph F E).symm x).proj
    let h : EB → EB := extChartAt IB ib ∘ (extChartAt IB jb).symm
    let g : EB × EF → EF := fun p ↦
      (extChartAt (IB.prod IF) j ((extChartAt (IB.prod IF) i).symm (h p.1, p.2))).2
    coordChange IB IF F E i j x A =
      (firstJetCoordChange h g (extChartAt IB jb xb) ((extChartAt (IB.prod IF) i x).2, A)).2 := by
  intro ib jb xb h g
  have hxi : x ∈ (extChartAt (IB.prod IF) i).source := by rw [extChartAt_source]; exact hx.1
  have hxj : x ∈ (extChartAt (IB.prod IF) j).source := by rw [extChartAt_source]; exact hx.2
  have hbi : xb ∈ (extChartAt IB ib).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.1).2
  have hbj : xb ∈ (extChartAt IB jb).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.2).2
  let p₀ : EB × EF := (extChartAt IB jb xb, (extChartAt (IB.prod IF) i x).2)
  have hh_pt : h p₀.1 = (extChartAt (IB.prod IF) i x).1 := by
    simp only [h, p₀, Function.comp_apply, (extChartAt IB jb).left_inv hbj,
      ManifoldTotalSpace.extChartAt_fst_of_mem_chart_source hx.1, xb, ib]
  have hh_diff : HasFDerivAt h (tangentCoordChange IB jb ib xb) p₀.1 := by
    rw [← hasFDerivWithinAt_univ, ← IB.range_eq_univ]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hbj, hbi⟩
  have hψ_diff : HasFDerivAt
      (Prod.snd ∘ (extChartAt (IB.prod IF) j ∘ (extChartAt (IB.prod IF) i).symm))
      ((ContinuousLinearMap.snd 𝕜 EB EF).comp (tangentCoordChange (IB.prod IF) i j x))
      (h p₀.1, p₀.2) := by
    rw [hh_pt, Prod.mk.eta, ← hasFDerivWithinAt_univ, ← (IB.prod IF).range_eq_univ]
    exact hasFDerivAt_snd.comp_hasFDerivWithinAt _ (hasFDerivWithinAt_tangentCoordChange ⟨hxi, hxj⟩)
  have hg_raw := hψ_diff.comp p₀
    ((hh_diff.comp p₀ (hasFDerivAt_fst (𝕜 := 𝕜))).prodMk (hasFDerivAt_snd (𝕜 := 𝕜)))
  have hg_fderiv : fderiv 𝕜 g p₀ =
      ((ContinuousLinearMap.snd 𝕜 EB EF).comp (tangentCoordChange (IB.prod IF) i j x)).comp
        (((tangentCoordChange IB jb ib xb).comp (ContinuousLinearMap.fst 𝕜 EB EF)).prod
          (ContinuousLinearMap.snd 𝕜 EB EF)) :=
    hg_raw.fderiv
  ext u
  simp only [firstJetCoordChange_snd_apply, hg_fderiv, hh_diff.fderiv, coordChange, comp_apply,
    ContinuousLinearMap.prod_apply, id_apply, coe_fst', coe_snd', p₀, ib, jb, xb]

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
/-- **Smoothness of first-jet coordinate changes.** When `B`, `F` and `E` are `C^(n+1)`, the affine
map `(x, A) ↦ coordChange i j x A` is `C^n` on the chart overlap product. -/
theorem contMDiffOn_coordChange {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] (i j : ManifoldTotalSpace F E) :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffOn ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) 𝓘(𝕜, EB →L[𝕜] EF) n
      (fun p : ManifoldTotalSpace F E × (EB →L[𝕜] EF) ↦ coordChange IB IF F E i j p.1 p.2)
      (((chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source) ×ˢ univ) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  set U := (chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source
  have hTE := (tangentBundleCore.isContMDiff (I := IB.prod IF)
    (M := ManifoldTotalSpace F E) (n := n)).contMDiffOn_coordChange
    (achart (ModelProd HB HF) i) (achart (ModelProd HB HF) j)
  have hTB₀ := (tangentBundleCore.isContMDiff (I := IB) (M := B) (n := n)).contMDiffOn_coordChange
    (achart HB ((ManifoldTotalSpace.homeomorph F E).symm j).proj)
    (achart HB ((ManifoldTotalSpace.homeomorph F E).symm i).proj)
  have hTB : ContMDiffOn (IB.prod IF) 𝓘(𝕜, EB →L[𝕜] EB) n
      (fun x : ManifoldTotalSpace F E ↦ tangentCoordChange IB
        ((ManifoldTotalSpace.homeomorph F E).symm j).proj
        ((ManifoldTotalSpace.homeomorph F E).symm i).proj
        ((ManifoldTotalSpace.homeomorph F E).symm x).proj) U :=
    hTB₀.comp (ManifoldTotalSpace.contMDiff_proj n F E IB IF).contMDiffOn fun x hx ↦
      ⟨(ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.2).2,
        (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx.1).2⟩
  have hgraph : ContDiff 𝕜 n (fun q :
      (((EB × EF) →L[𝕜] (EB × EF)) × (EB →L[𝕜] EB)) × (EB →L[𝕜] EF) ↦
      (ContinuousLinearMap.id 𝕜 EB).prod q.2) := by
    have heq : (fun q : (((EB × EF) →L[𝕜] (EB × EF)) × (EB →L[𝕜] EB)) × (EB →L[𝕜] EF) ↦
        (ContinuousLinearMap.id 𝕜 EB).prod q.2) =
        fun q ↦ ContinuousLinearMap.inl 𝕜 EB EF +
          (ContinuousLinearMap.inr 𝕜 EB EF).comp q.2 := by
      funext q; ext u <;> simp
    rw [heq]
    exact contDiff_const.add (contDiff_const.clm_comp contDiff_snd)
  have hΦ : ContDiff 𝕜 n (fun q :
      (((EB × EF) →L[𝕜] (EB × EF)) × (EB →L[𝕜] EB)) × (EB →L[𝕜] EF) ↦
      (ContinuousLinearMap.snd 𝕜 EB EF).comp
        (q.1.1.comp (((ContinuousLinearMap.id 𝕜 EB).prod q.2).comp q.1.2))) :=
    contDiff_const.clm_comp (contDiff_fst.fst.clm_comp (hgraph.clm_comp contDiff_fst.snd))
  have hfstU : ContMDiffOn ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) n
      Prod.fst (U ×ˢ (univ : Set (EB →L[𝕜] EF))) := contMDiffOn_fst
  have hpair : ContMDiffOn ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF))
      𝓘(𝕜, (((EB × EF) →L[𝕜] (EB × EF)) × (EB →L[𝕜] EB)) × (EB →L[𝕜] EF)) n
      (fun p : ManifoldTotalSpace F E × (EB →L[𝕜] EF) ↦
        ((tangentCoordChange (IB.prod IF) i j p.1,
          tangentCoordChange IB ((ManifoldTotalSpace.homeomorph F E).symm j).proj
            ((ManifoldTotalSpace.homeomorph F E).symm i).proj
            ((ManifoldTotalSpace.homeomorph F E).symm p.1).proj), p.2)) (U ×ˢ univ) :=
    ((hTE.comp hfstU fun _ hp ↦ hp.1).prodMk_space
      (hTB.comp hfstU fun _ hp ↦ hp.1)).prodMk_space contMDiffOn_snd
  exact hΦ.contMDiff.comp_contMDiffOn hpair

variable (IB IF F E) in
/-- The local pretrivialization of `FirstJet IB IF F E` over the preferred chart source at `i`. -/
def pretrivialization (i : ManifoldTotalSpace F E) :
    Pretrivialization (EB →L[𝕜] EF) (π (EB →L[𝕜] EF) (FirstJet IB IF F E)) where
  toFun p := (p.proj, coordChange IB IF F E p.proj i p.proj (chartCoordEquiv IB IF F E p.proj p.2))
  invFun q := ⟨q.1, (chartCoordEquiv IB IF F E q.1).symm (coordChange IB IF F E i q.1 q.1 q.2)⟩
  source := TotalSpace.proj ⁻¹' (chartAt (ModelProd HB HF) i).source
  target := (chartAt (ModelProd HB HF) i).source ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' := by
    rintro ⟨x, j⟩ hp
    refine congrArg (TotalSpace.mk' (EB →L[𝕜] EF) x)
      ((chartCoordEquiv IB IF F E x).injective ?_)
    rw [Equiv.apply_symm_apply,
      coordChange_comp ⟨⟨mem_chart_source _ x, hp⟩, mem_chart_source _ x⟩,
      coordChange_self (mem_chart_source _ x)]
  right_inv' q hq := Prod.ext rfl <| by
    rw [Equiv.apply_symm_apply,
      coordChange_comp ⟨⟨hq.1, mem_chart_source _ q.1⟩, hq.1⟩, coordChange_self hq.1]
  open_target := (chartAt _ i).open_source.prod isOpen_univ
  baseSet := (chartAt (ModelProd HB HF) i).source
  open_baseSet := (chartAt _ i).open_source
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

end Bundle

end FirstJet

section Prebundle

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- The `FiberPrebundle` assembling the preferred-chart pretrivializations of `FirstJet`. -/
def firstJetPrebundle : FiberPrebundle (EB →L[𝕜] EF) (FirstJet IB IF F E) where
  pretrivializationAtlas := range (FirstJet.pretrivialization IB IF F E)
  pretrivializationAt := FirstJet.pretrivialization IB IF F E
  mem_base_pretrivializationAt := mem_chart_source (ModelProd HB HF)
  pretrivialization_mem_atlas i := ⟨i, rfl⟩
  continuous_trivChange := by
    rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩
    have : IsManifold IB (0 + 1) B := by simpa
    have : IsManifold IF (0 + 1) F := by simpa
    have : ContMDiffFiberBundle (0 + 1) F E IB IF := by simpa
    have hcont := (FirstJet.contMDiffOn_coordChange (IB := IB) (IF := IF) (F := F) (E := E)
      (n := 0) i j).continuousOn
    have hdom : (FirstJet.pretrivialization IB IF F E i).target ∩
        (FirstJet.pretrivialization IB IF F E i).toPartialEquiv.symm ⁻¹'
          (FirstJet.pretrivialization IB IF F E j).source =
        ((chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source) ×ˢ univ := by
      ext ⟨x, A⟩
      simp only [FirstJet.pretrivialization, mem_inter_iff, mem_preimage, mem_prod, mem_univ,
        and_true]
      exact Iff.rfl
    rw [hdom]
    refine (continuousOn_fst.prodMk hcont).congr ?_
    rintro ⟨x, A⟩ ⟨hx, -⟩
    change (x, FirstJet.coordChange IB IF F E x j x
        (FirstJet.chartCoordEquiv IB IF F E x
          ((FirstJet.chartCoordEquiv IB IF F E x).symm (FirstJet.coordChange IB IF F E i x x A)))) =
      (x, FirstJet.coordChange IB IF F E i j x A)
    rw [Equiv.apply_symm_apply,
      FirstJet.coordChange_comp ⟨⟨hx.1, mem_chart_source _ x⟩, hx.2⟩]
  totalSpaceMk_isInducing b := by
    have heq : FirstJet.pretrivialization IB IF F E b ∘ TotalSpace.mk b =
        Prod.mk b ∘ FirstJet.chartCoordEquiv IB IF F E b := by
      funext j
      exact Prod.ext rfl (FirstJet.coordChange_self (mem_chart_source _ b) _)
    rw [heq]
    exact (isEmbedding_prodMkRight b).isInducing.comp ⟨rfl⟩

instance FirstJet.instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E)) :=
  (firstJetPrebundle IB IF F E).totalSpaceTopology

instance FirstJet.instFiberBundle :
    FiberBundle (EB →L[𝕜] EF) (FirstJet IB IF F E) :=
  (firstJetPrebundle IB IF F E).toFiberBundle

end Prebundle

namespace FirstJet

variable {IB IF F E}

section SmoothBundle

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- The preferred trivialization of `FirstJet` at `i` has `(chartAt _ i).source` as base set. -/
@[simp]
theorem trivializationAt_baseSet (i : ManifoldTotalSpace F E) :
    (trivializationAt (EB →L[𝕜] EF) (FirstJet IB IF F E) i).baseSet =
      (chartAt (ModelProd HB HF) i).source :=
  (rfl)

/-- The preferred trivialization of `FirstJet` at `i` applies `coordChange` to `chartCoordEquiv`. -/
theorem trivializationAt_apply_snd (i : ManifoldTotalSpace F E)
    (p : TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E)) :
    (trivializationAt (EB →L[𝕜] EF) (FirstJet IB IF F E) i p).2 =
      coordChange IB IF F E p.proj i p.proj (chartCoordEquiv IB IF F E p.proj p.2) :=
  (rfl)

/-- At its own base point `x`, the preferred trivialization of `FirstJet` is `chartCoordEquiv x`. -/
@[simp]
theorem trivializationAt_self_apply_snd (x : ManifoldTotalSpace F E)
    (j : FirstJet IB IF F E x) :
    (trivializationAt (EB →L[𝕜] EF) (FirstJet IB IF F E) x ⟨x, j⟩).2 =
      chartCoordEquiv IB IF F E x j :=
  coordChange_self (mem_chart_source _ x) _

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
/-- **The first-jet bundle `J¹E → E` of a `C^(n+1)` fibre bundle is a `C^n` fibre bundle.** -/
theorem contMDiffFiberBundle {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffFiberBundle n (EB →L[𝕜] EF) (FirstJet IB IF F E)
      (IB.prod IF) 𝓘(𝕜, EB →L[𝕜] EF) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  refine ⟨?_⟩
  rintro e e' ⟨he⟩ ⟨he'⟩
  rcases he with ⟨_, ⟨i, rfl⟩, rfl⟩
  rcases he' with ⟨_, ⟨j, rfl⟩, rfl⟩
  refine (contMDiffOn_coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j).congr ?_
  rintro ⟨x, A⟩ ⟨hx, -⟩
  change coordChange IB IF F E x j x
    (chartCoordEquiv IB IF F E x ((chartCoordEquiv IB IF F E x).symm
      (coordChange IB IF F E i x x A))) = coordChange IB IF F E i j x A
  rw [Equiv.apply_symm_apply, coordChange_comp ⟨⟨hx.1, mem_chart_source _ x⟩, hx.2⟩]

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance instContMDiffFiberBundle_infty [IsManifold IB ∞ B] [IsManifold IF ∞ F]
    [ContMDiffFiberBundle ∞ F E IB IF] :
    ContMDiffFiberBundle ∞ (EB →L[𝕜] EF) (FirstJet IB IF F E)
      (IB.prod IF) 𝓘(𝕜, EB →L[𝕜] EF) := by
  have : IsManifold IB (∞ + 1) B := by simpa using (inferInstance : IsManifold IB ∞ B)
  have : IsManifold IF (∞ + 1) F := by simpa using (inferInstance : IsManifold IF ∞ F)
  have : ContMDiffFiberBundle (∞ + 1) F E IB IF := by
    simpa using (inferInstance : ContMDiffFiberBundle ∞ F E IB IF)
  exact contMDiffFiberBundle

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance instContMDiffFiberBundle_omega [IsManifold IB ω B] [IsManifold IF ω F]
    [ContMDiffFiberBundle ω F E IB IF] :
    ContMDiffFiberBundle ω (EB →L[𝕜] EF) (FirstJet IB IF F E)
      (IB.prod IF) 𝓘(𝕜, EB →L[𝕜] EF) := by
  have : IsManifold IB (ω + 1) B := by simpa using (inferInstance : IsManifold IB ω B)
  have : IsManifold IF (ω + 1) F := by simpa using (inferInstance : IsManifold IF ω F)
  have : ContMDiffFiberBundle (ω + 1) F E IB IF := by
    simpa using (inferInstance : ContMDiffFiberBundle ω F E IB IF)
  exact contMDiffFiberBundle

/-- **Surjectivity of the truncation `π_{1,0} : J¹E → E`.** -/
theorem surjective_proj :
    Function.Surjective (TotalSpace.proj :
      TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E) → ManifoldTotalSpace F E) :=
  FiberBundle.surjective_proj (EB →L[𝕜] EF) (FirstJet IB IF F E)

/-- The composite base projection `π₁ = π ∘ π_{1,0} : J¹E → B` is `C^m` for every `m`. -/
theorem contMDiff_baseProj (m : ℕ∞ω) :
    ContMDiff ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) IB m
      (fun p : TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E) ↦
        ((ManifoldTotalSpace.homeomorph F E).symm p.proj).proj) :=
  (ManifoldTotalSpace.contMDiff_proj m F E IB IF).comp (Bundle.contMDiff_proj _)

/-- When the fibre `F` is nonempty, the composite projection `J¹E → B` is surjective. -/
theorem surjective_baseProj [Nonempty F] :
    Function.Surjective (fun p : TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E) ↦
      ((ManifoldTotalSpace.homeomorph F E).symm p.proj).proj) :=
  (FiberBundle.surjective_proj F E).comp
    ((ManifoldTotalSpace.homeomorph F E).symm.surjective.comp surjective_proj)

/-- **Chart formula for `contactForm` across preferred trivializations.** In any preferred chart `i`
containing `x`, `j.contactForm w` has vertical trivialization coordinate `w_i.2 - A_i w_i.1`. -/
theorem trivializationAt_contactForm {i x : ManifoldTotalSpace F E}
    (hx : x ∈ (chartAt (ModelProd HB HF) i).source) (j : FirstJet IB IF F E x)
    (w : TangentSpace (IB.prod IF) x) :
    (trivializationAt EF (VerticalBundle IB IF F E) i ⟨x, j.contactForm w⟩).2 =
      (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i ⟨x, w⟩).2.2 -
        (trivializationAt (EB →L[𝕜] EF) (FirstJet IB IF F E) i ⟨x, j⟩).2
          (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i ⟨x, w⟩).2.1 := by
  let w₀ : EB × EF := w
  have hxx : x ∈ (chartAt (ModelProd HB HF) x).source ∩ (chartAt (ModelProd HB HF) i).source :=
    ⟨mem_chart_source _ x, hx⟩
  have hbx : ((ManifoldTotalSpace.homeomorph F E).symm x).proj ∈
      (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hxx.1).2
  have hbi : ((ManifoldTotalSpace.homeomorph F E).symm x).proj ∈
      (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).source := by
    rw [extChartAt_source]; exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hxx.2).2
  have hfst : (tangentCoordChange (IB.prod IF) x i x w₀).1 =
      tangentCoordChange IB ((ManifoldTotalSpace.homeomorph F E).symm x).proj
        ((ManifoldTotalSpace.homeomorph F E).symm i).proj
        ((ManifoldTotalSpace.homeomorph F E).symm x).proj w₀.1 :=
    DFunLike.congr_fun (ManifoldTotalSpace.fst_comp_tangentCoordChange hxx) w₀
  have hprod := DFunLike.congr_fun
    (id_prod_coordChange (IB := IB) (IF := IF) hxx (chartCoordEquiv IB IF F E x j))
    (tangentCoordChange (IB.prod IF) x i x w₀).1
  rw [comp_apply, comp_apply, hfst,
    tangentCoordChange_comp ⟨⟨hbx, hbi⟩, hbx⟩, tangentCoordChange_self hbx, ← hfst] at hprod
  let v₀ : EF := j.contactForm w
  have htriv : (trivializationAt EF (VerticalBundle IB IF F E) i ⟨x, j.contactForm w⟩).2 =
      VerticalBundle.coordChange IB IF F E x i x v₀ :=
    VerticalBundle.trivializationAt_apply_snd i ⟨x, j.contactForm w⟩
  have hinr : (0, VerticalBundle.coordChange IB IF F E x i x v₀) =
      tangentCoordChange (IB.prod IF) x i x (0, v₀) :=
    (VerticalBundle.tangentCoordChange_inr (EF := EF) hxx v₀).symm
  have hv₀ : (0, v₀) =
      w₀ - (ContinuousLinearMap.id 𝕜 EB).prod (chartCoordEquiv IB IF F E x j) w₀.1 :=
    Prod.ext (sub_self w₀.1).symm (j.contactForm_apply_chart w₀)
  rw [htriv]
  exact congrArg Prod.snd (hinr.trans (by rw [hv₀, map_sub, ← hprod]))

/-- **Smoothness of contact evaluation.** Given `C^m` maps `f` into `J¹E` and `v` into `TE` over
the same base map `h : (v y).proj = (f y).proj`, evaluating the contact form produces a `C^m` map
into `VE`. -/
theorem contMDiff_contactForm {M : Type*} {EM : Type*} [NormedAddCommGroup EM]
    [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
    [TopologicalSpace M] [ChartedSpace HM M] {m : ℕ∞ω}
    {f : M → TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E)}
    {v : M → TangentBundle (IB.prod IF) (ManifoldTotalSpace F E)}
    (hf : ContMDiff IM ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) m f)
    (hv : ContMDiff IM (IB.prod IF).tangent m v)
    (h : ∀ y, (v y).proj = (f y).proj) :
    ContMDiff IM ((IB.prod IF).prod 𝓘(𝕜, EF)) m
      (fun y ↦ (⟨(f y).proj, (f y).2.contactForm (h y ▸ (v y).2)⟩ :
        TotalSpace EF (VerticalBundle IB IF F E))) := by
  intro y₀
  have hf_parts := Bundle.contMDiffAt_totalSpace_iff.1 (hf y₀)
  have hv_cast : ContMDiffAt IM (IB.prod IF).tangent m
      (fun y ↦ (⟨(f y).proj, h y ▸ (v y).2⟩ :
        TangentBundle (IB.prod IF) (ManifoldTotalSpace F E))) y₀ := by
    refine (hv y₀).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
    have hmk : ∀ {p₁ p₂ : ManifoldTotalSpace F E} (hp : p₁ = p₂) (w : TangentSpace (IB.prod IF) p₁),
        (⟨p₂, hp ▸ w⟩ : TangentBundle (IB.prod IF) (ManifoldTotalSpace F E)) = ⟨p₁, w⟩ := by
      rintro _ _ rfl _; rfl
    exact hmk (h y) (v y).2
  have hv_coord := (Bundle.contMDiffAt_totalSpace_iff.1 hv_cast).2
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hf_parts.1, ?_⟩
  have hU : (fun y ↦ (f y).proj) ⁻¹' (chartAt (ModelProd HB HF) (f y₀).proj).source ∈ 𝓝 y₀ :=
    hf_parts.1.continuousAt.preimage_mem_nhds
      ((chartAt _ (f y₀).proj).open_source.mem_nhds (mem_chart_source (ModelProd HB HF) _))
  have hΨ : ContDiff 𝕜 m (fun q : (EB × EF) × (EB →L[𝕜] EF) ↦ q.1.2 - q.2 q.1.1) :=
    contDiff_fst.snd.sub (contDiff_snd.clm_apply contDiff_fst.fst)
  refine (hΨ.contMDiff.contMDiffAt.comp y₀
    (hv_coord.prodMk_space hf_parts.2)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with y hy
  exact trivializationAt_contactForm (x := (f y).proj) hy (f y).2 (h y ▸ (v y).2)

end SmoothBundle

end FirstJet

end TauCeti
