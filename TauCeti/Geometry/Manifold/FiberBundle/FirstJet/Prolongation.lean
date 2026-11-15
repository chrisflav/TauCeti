/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.FirstJet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Connection

/-!
# Holonomic prolongation, jet connections, and vector-bundle comparison for `FirstJet`

This file develops the prolongation and connection calculus of `TauCeti.FirstJet` on a smooth
fibre bundle `E → B` and relates `FirstJet` to the linear jet bundle `TauCeti.FirstJetBundle` when
`E` is a vector bundle:

1. **Holonomic prolongation and locality**: a local section `s : B → ManifoldTotalSpace F E`
   prolongs at `b` to `FirstJet.jetAt IB IF s b`, whose horizontal lift agrees with
   `mfderiv IB (IB.prod IF) s b` whenever `s` is differentiable at `b` and `(π ∘ s) =ᶠ[𝓝 b] id`.
   The prolonged point in `J¹E` depends only on the germ of `s` at `b` (`FirstJet.mk_jetAt_congr`),
   is uniquely characterized by the vanishing of the pulled-back contact form
   `j.contactForm ∘ ds_b = 0` (`FirstJet.eq_jetAt_iff_contactForm_comp_mfderiv_eq_zero`), and
   defines a `C^n` map `U → J¹E` whenever `s` is `C^(n+1)` on an open set `U`
   (`FirstJet.contMDiffOn_jetAt`).
2. **Local smooth section realization**: when `IB` and `IF` are boundaryless and `B`, `F` and `E`
   are `C^n`, every first jet `j` at `x` is realized at `π x` by a `C^n` local section on an open
   neighbourhood of `π x` (`FirstJet.exists_contMDiffOn_section_jetAt_eq`).
3. **First-jet connections (Ehresmann splittings)**: a connection `Γ : ∀ x, FirstJet IB IF F E x`
   induces the covariant derivative `j¹s(b) -ᵥ Γ (s b) = (Γ (s b)).contactForm ∘ ds_b`
   (`FirstJet.jetAt_vsub_connection`), and two connections differ by the tensor `Γ₁ -ᵥ Γ₂`
   (`FirstJet.vsub_connection_sub_vsub_connection`).
4. **Vector-bundle comparison**: when `V → B` is a `C^1` vector bundle with normed fibre `F`,
   `FirstJet.diffeomorphFirstJetBundle` is a canonical `C^n` diffeomorphism between
   `TotalSpace (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V)` and
   `TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)`, compatible with base projections,
   `FirstJetBundle.value`, holonomic prolongation, the affine `Hom(TB, V)` torsor action, and
   `FirstJetBundle.covariantDerivative`.

## Main definitions

* `TauCeti.FirstJet.jetAt` and `TauCeti.FirstJet.jet`: holonomic first-jet prolongation of local
  and global sections.
* `TauCeti.FirstJet.toFirstJetBundle`, `TauCeti.FirstJet.ofFirstJetBundle`, and
  `TauCeti.FirstJet.diffeomorphFirstJetBundle`: the canonical `C^n` diffeomorphism identifying
  `FirstJet` of a `C^1` vector bundle `V` with `FirstJetBundle IB F V`.

## Main results

* `TauCeti.FirstJet.mk_jetAt_congr` and
  `TauCeti.FirstJet.eq_jetAt_iff_contactForm_comp_mfderiv_eq_zero`: locality and contact-pullback
  characterization of holonomic first jets.
* `TauCeti.FirstJet.contMDiffOn_jetAt` and `TauCeti.FirstJet.contMDiff_jet`: smoothness of
  holonomic prolongation.
* `TauCeti.FirstJet.exists_contMDiffOn_section_jetAt_eq`: on boundaryless models, every first jet
  is locally realized by a `C^n` local section.
* `TauCeti.FirstJet.jetAt_vsub_connection` and
  `TauCeti.FirstJet.vsub_connection_sub_vsub_connection`: covariant derivative and tensorial
  difference law for general first-jet connections.
* `TauCeti.FirstJet.diffeomorphFirstJetBundle_jet`,
  `TauCeti.FirstJet.diffeomorphFirstJetBundle_vadd`, and
  `TauCeti.FirstJet.covariantDerivative_diffeomorphFirstJetBundle`: compatibility of the
  vector-bundle comparison with prolongation, torsor translation, and linear connections.

## References

* I. M. Anderson, *The Variational Bicomplex*, Chapter 1, §A (holonomic prolongation and contact
  pullback).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§12.1–12.6, 17.1 (prolongation, general jet connections, and linear comparison).
-/

public section

noncomputable section

open Bundle Set Filter ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace TauCeti

section GeneralFiber

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

namespace FirstJet

/-! ### Holonomic prolongation, locality, contact characterization, and local realization -/

section Prolongation

variable (IB IF) in
/-- **Holonomic first jet `j¹s(b)` of a local section `s : B → ManifoldTotalSpace F E` at `b`.**
When `s` is differentiable at `b` and `(π ∘ s) =ᶠ[𝓝 b] id`, its horizontal lift is
`mfderiv IB (IB.prod IF) s b` (`FirstJet.tangentLift_jetAt`), making `jetAt` directly applicable to
local sections on open subsets of `B` even when `E → B` admits no global sections. -/
def jetAt (s : B → ManifoldTotalSpace F E) (b : B) : FirstJet IB IF F E (s b) :=
  (chartCoordEquiv IB IF F E (s b)).symm
    ((ContinuousLinearMap.snd 𝕜 EB EF).comp (mfderiv IB (IB.prod IF) s b))

@[simp]
theorem chartCoordEquiv_jetAt (s : B → ManifoldTotalSpace F E) (b : B) :
    chartCoordEquiv IB IF F E (s b) (jetAt IB IF s b) =
      (ContinuousLinearMap.snd 𝕜 EB EF).comp (mfderiv IB (IB.prod IF) s b) :=
  (chartCoordEquiv IB IF F E (s b)).apply_symm_apply _

/-- For a local section differentiable at `b` with `(π ∘ s) =ᶠ[𝓝 b] id`, the horizontal lift of
`jetAt IB IF s b` is `mfderiv IB (IB.prod IF) s b`. -/
theorem tangentLift_jetAt {s : B → ManifoldTotalSpace F E} {b : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s b)
    (hproj : (fun y ↦ ((ManifoldTotalSpace.homeomorph F E).symm (s y)).proj) =ᶠ[𝓝 b] id) :
    (jetAt IB IF s b).tangentLift = mfderiv IB (IB.prod IF) s b := by
  have hcomp := (ManifoldTotalSpace.hasMFDerivAt_proj (IB := IB) (IF := IF) (s b)).comp b
    hs.hasMFDerivAt
  have hid := (hasMFDerivAt_id (I := IB) b).congr_of_eventuallyEq_abuse hproj
  have hfst : (ContinuousLinearMap.fst 𝕜 EB EF).comp (mfderiv IB (IB.prod IF) s b) =
      ContinuousLinearMap.id 𝕜 EB := hcomp.mfderiv.symm.trans hid.mfderiv
  rw [jetAt, tangentLift_chartCoordEquiv_symm, ← hfst]
  ext u <;> rfl

/-- **Locality of first jets.** Two maps `B → ManifoldTotalSpace F E` with the same germ at `b`
have equal prolonged points in `J¹E`. In particular, modifying a section outside a neighbourhood of
`b` leaves its first jet at `b` unchanged. -/
theorem mk_jetAt_congr {s₁ s₂ : B → ManifoldTotalSpace F E} {b : B}
    (hEq : s₁ =ᶠ[𝓝 b] s₂) :
    (⟨s₁ b, jetAt IB IF s₁ b⟩ : TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E)) =
      ⟨s₂ b, jetAt IB IF s₂ b⟩ := by
  have hmk : ∀ {x₁ x₂ : ManifoldTotalSpace F E} {A₁ A₂ : EB →L[𝕜] EF},
      x₁ = x₂ → A₁ = A₂ →
      (⟨x₁, (chartCoordEquiv IB IF F E x₁).symm A₁⟩ :
        TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E)) =
        ⟨x₂, (chartCoordEquiv IB IF F E x₂).symm A₂⟩ := by
    rintro _ _ _ _ rfl rfl; rfl
  have hmf : (mfderiv IB (IB.prod IF) s₁ b : EB →L[𝕜] EB × EF) = mfderiv IB (IB.prod IF) s₂ b :=
    hEq.mfderiv_eq
  exact hmk hEq.eq_of_nhds (congrArg (ContinuousLinearMap.snd 𝕜 EB EF).comp hmf)

variable (IB IF F) in
/-- **Holonomic first jet `j¹s(b)` of a global section `s : ∀ y, E y` at `b`.** -/
def jet (s : ∀ y, E y) (b : B) :
    FirstJet IB IF F E (ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩) :=
  jetAt IB IF (fun y ↦ ManifoldTotalSpace.homeomorph F E ⟨y, s y⟩) b

/-- When a global section `s : ∀ y, E y` is differentiable at `b`, the horizontal lift of
`jet IB IF F s b` is the manifold derivative of `s` at `b`. -/
theorem tangentLift_jet {s : ∀ y, E y} {b : B}
    (hs : MDifferentiableAt IB (IB.prod IF)
      (fun y ↦ ManifoldTotalSpace.homeomorph F E ⟨y, s y⟩) b) :
    (jet IB IF F s b).tangentLift =
      mfderiv IB (IB.prod IF) (fun y ↦ ManifoldTotalSpace.homeomorph F E ⟨y, s y⟩) b :=
  tangentLift_jetAt hs (Eventually.of_forall fun y ↦ by simp)

section ContactCharacterization

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- **Contact-pullback characterization of holonomic first jets.** For a differentiable local
section `s` at `b`, a first jet `j` at `s b` equals `jetAt IB IF s b` if and only if the
pulled-back contact form `j.contactForm ∘ mfderiv s b` vanishes identically on `T_b B`. -/
theorem eq_jetAt_iff_contactForm_comp_mfderiv_eq_zero {s : B → ManifoldTotalSpace F E} {b : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s b)
    (hproj : (fun y ↦ ((ManifoldTotalSpace.homeomorph F E).symm (s y)).proj) =ᶠ[𝓝 b] id)
    (j : FirstJet IB IF F E (s b)) :
    j = jetAt IB IF s b ↔ j.contactForm.comp (mfderiv IB (IB.prod IF) s b) = 0 := by
  rw [eq_comm, ← vsub_eq_zero_iff_eq, vsub_def, tangentLift_jetAt hs hproj]
  rfl

/-- Chart derivative of a differentiable local section read from a preferred base chart at `π i` to
the total-space chart at `i`. -/
private theorem hasFDerivWithinAt_extChartAt_comp_section {s : B → ManifoldTotalSpace F E} {b : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s b)
    (hproj : (fun y ↦ ((ManifoldTotalSpace.homeomorph F E).symm (s y)).proj) =ᶠ[𝓝 b] id)
    {i : ManifoldTotalSpace F E} (hi : s b ∈ (chartAt (ModelProd HB HF) i).source) :
    HasFDerivWithinAt
      (extChartAt (IB.prod IF) i ∘ s ∘
        (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).symm)
      ((tangentCoordChange (IB.prod IF) (s b) i (s b)).comp
        ((show EB →L[𝕜] EB × EF from mfderiv IB (IB.prod IF) s b).comp
          (tangentCoordChange IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj b b)))
      (range IB) (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj b) := by
  have hsb : ((ManifoldTotalSpace.homeomorph F E).symm (s b)).proj = b := hproj.eq_of_nhds
  have hxi : s b ∈ (extChartAt (IB.prod IF) i).source := by rwa [extChartAt_source]
  have hxx : s b ∈ (extChartAt (IB.prod IF) (s b)).source := mem_extChartAt_source (s b)
  have hbi : b ∈ (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).source := by
    rw [← hsb, extChartAt_source]
    exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hi).2
  have hbb : b ∈ (extChartAt IB b).source := mem_extChartAt_source b
  set z₀ := extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj b
  have hz₀_eq : (extChartAt IB b ∘
      (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).symm) z₀ =
      extChartAt IB b b := by
    simp only [z₀, Function.comp_apply, (extChartAt IB _).left_inv hbi]
  have hs_chart : HasFDerivWithinAt (writtenInExtChartAt IB (IB.prod IF) b s)
      (show EB →L[𝕜] EB × EF from mfderiv IB (IB.prod IF) s b) (range IB)
      ((extChartAt IB b ∘
        (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).symm) z₀) := by
    rw [hz₀_eq]; exact hs.hasMFDerivAt.2
  have hmid := hs_chart.comp z₀ (hasFDerivWithinAt_tangentCoordChange ⟨hbi, hbb⟩)
    (mapsTo_extChartAt_comp_extChartAt_symm IB b _ _)
  have hmid_pt : writtenInExtChartAt IB (IB.prod IF) b s
      ((extChartAt IB b ∘
        (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).symm) z₀) =
      extChartAt (IB.prod IF) (s b) (s b) := by
    simp only [hz₀_eq, writtenInExtChartAt, Function.comp_apply, (extChartAt IB b).left_inv hbb]
  have htot : HasFDerivWithinAt (extChartAt (IB.prod IF) i ∘ (extChartAt (IB.prod IF) (s b)).symm)
      (tangentCoordChange (IB.prod IF) (s b) i (s b)) (range (IB.prod IF))
      (writtenInExtChartAt IB (IB.prod IF) b s ((extChartAt IB b ∘
        (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).symm) z₀)) := by
    rw [hmid_pt]; exact hasFDerivWithinAt_tangentCoordChange ⟨hxx, hxi⟩
  have houter := htot.comp z₀ hmid fun _ _ ↦ by
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe]; exact mem_range_self _
  have hU₁ : (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).symm ⁻¹'
      ((extChartAt IB b).source ∩ s ⁻¹' (extChartAt (IB.prod IF) (s b)).source) ∈ 𝓝[range IB] z₀ :=
    mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds' hbi (Filter.inter_mem
      (extChartAt_source_mem_nhds (I := IB) b)
      (hs.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := IB.prod IF) (s b)))))
  refine houter.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hU₁] with z hz
    simp only [writtenInExtChartAt, Function.comp_apply,
      (extChartAt IB b).left_inv hz.1, (extChartAt (IB.prod IF) (s b)).left_inv hz.2]
  · simp only [z₀, writtenInExtChartAt, Function.comp_apply, (extChartAt IB _).left_inv hbi,
      (extChartAt IB b).left_inv hbb, (extChartAt (IB.prod IF) (s b)).left_inv hxx]

/-- In any preferred chart `i` containing `s b`, the trivialization coordinate of `jetAt IB IF s b`
is the chart derivative of `s` from the base chart at `π i` to the total-space chart at `i`. -/
theorem trivializationAt_jetAt {s : B → ManifoldTotalSpace F E} {b : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s b)
    (hproj : (fun y ↦ ((ManifoldTotalSpace.homeomorph F E).symm (s y)).proj) =ᶠ[𝓝 b] id)
    {i : ManifoldTotalSpace F E} (hi : s b ∈ (chartAt (ModelProd HB HF) i).source) :
    (trivializationAt (EB →L[𝕜] EF) (FirstJet IB IF F E) i ⟨s b, jetAt IB IF s b⟩).2 =
      (ContinuousLinearMap.snd 𝕜 EB EF).comp
        (fderivWithin 𝕜 (extChartAt (IB.prod IF) i ∘ s ∘
            (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).symm)
          (range IB) (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj b)) := by
  have hsb : ((ManifoldTotalSpace.homeomorph F E).symm (s b)).proj = b := hproj.eq_of_nhds
  have hbi : b ∈ (extChartAt IB ((ManifoldTotalSpace.homeomorph F E).symm i).proj).source := by
    rw [← hsb, extChartAt_source]
    exact (ManifoldTotalSpace.proj_mem_of_mem_chart_source hi).2
  have hfderiv := (hasFDerivWithinAt_extChartAt_comp_section hs hproj hi).fderivWithin
    (IB.uniqueDiffOn _ (extChartAt_target_subset_range _ ((extChartAt IB _).map_source hbi)))
  rw [trivializationAt_apply_snd, coordChange_apply, id_prod_chartCoordEquiv,
    tangentLift_jetAt hs hproj, hsb, hfderiv]

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
/-- **Smoothness of holonomic first-jet prolongation.** For a `C^(n+1)` local section `s` on an
open set `U ⊆ B`, the prolonged map `b ↦ ⟨s b, jetAt IB IF s b⟩` is `C^n` on `U`. -/
theorem contMDiffOn_jetAt {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] {s : B → ManifoldTotalSpace F E} {U : Set B}
    (hU : IsOpen U) (hs : ContMDiffOn IB (IB.prod IF) (n + 1) s U)
    (hproj : ∀ b ∈ U, ((ManifoldTotalSpace.homeomorph F E).symm (s b)).proj = b) :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffOn IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) n
      (fun b ↦ (⟨s b, jetAt IB IF s b⟩ :
        TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E))) U := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  intro b₀ hb₀
  have hs_at := (hs b₀ hb₀).contMDiffAt (hU.mem_nhds hb₀)
  refine ContMDiffAt.contMDiffWithinAt
    (Bundle.contMDiffAt_totalSpace_iff.2 ⟨hs_at.of_le le_self_add, ?_⟩)
  have hsb₀ : ((ManifoldTotalSpace.homeomorph F E).symm (s b₀)).proj = b₀ := hproj b₀ hb₀
  have hb₀_src : b₀ ∈ (extChartAt IB b₀).source := mem_extChartAt_source b₀
  have hrep : ContDiffWithinAt 𝕜 (n + 1) (writtenInExtChartAt IB (IB.prod IF) b₀ s)
      (range IB) (extChartAt IB b₀ b₀) :=
    ((by simpa only [← contMDiffWithinAt_univ, contMDiffWithinAt_iff, preimage_univ, univ_inter,
      writtenInExtChartAt] using hs_at :
        ContinuousWithinAt s univ b₀ ∧ _)).2
  have hfderiv : ContMDiffAt IB 𝓘(𝕜, EB →L[𝕜] EB × EF) n
      (fun b ↦ fderivWithin 𝕜 (writtenInExtChartAt IB (IB.prod IF) b₀ s)
        (range IB) (extChartAt IB b₀ b)) b₀ := by
    have hD := contMDiffWithinAt_iff_contDiffWithinAt.2
      (hrep.fderivWithin_right IB.uniqueDiffOn le_rfl
        (extChartAt_target_subset_range b₀ ((extChartAt IB b₀).map_source hb₀_src)))
    rw [← contMDiffWithinAt_univ]
    exact hD.comp b₀ contMDiffAt_extChartAt.contMDiffWithinAt fun b _ ↦ by
      rw [extChartAt_coe]; exact mem_range_self _
  let postSnd : (EB →L[𝕜] EB × EF) →L[𝕜] (EB →L[𝕜] EF) :=
    ContinuousLinearMap.compL 𝕜 EB (EB × EF) EF (ContinuousLinearMap.snd 𝕜 EB EF)
  refine (postSnd.contDiff.contMDiff.contMDiffAt.comp b₀ hfderiv).congr_of_eventuallyEq ?_
  have hV : U ∩ s ⁻¹' (chartAt (ModelProd HB HF) (s b₀)).source ∈ 𝓝 b₀ :=
    Filter.inter_mem (hU.mem_nhds hb₀)
      (hs_at.continuousAt.preimage_mem_nhds
        ((chartAt _ (s b₀)).open_source.mem_nhds (mem_chart_source (ModelProd HB HF) _)))
  filter_upwards [hV] with b hb
  have hmd : MDifferentiableAt IB (IB.prod IF) s b :=
    ((hs b hb.1).contMDiffAt (hU.mem_nhds hb.1)).mdifferentiableAt (by simp)
  rw [trivializationAt_jetAt hmd (eventually_of_mem (hU.mem_nhds hb.1) hproj) hb.2, hsb₀]
  rfl

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
/-- **Smoothness of global section prolongation `b ↦ ⟨s b, j¹s(b)⟩`.** -/
theorem contMDiff_jet {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] {s : ∀ b, E b}
    (hs : ContMDiff IB (IB.prod IF) (n + 1)
      (fun b ↦ ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩)) :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiff IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) n
      (fun b ↦ (⟨ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩, jet IB IF F s b⟩ :
        TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E))) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  rw [← contMDiffOn_univ] at hs ⊢
  exact contMDiffOn_jetAt isOpen_univ hs fun b _ ↦ by simp

end ContactCharacterization

/-! #### Local realization of every first jet by a smooth section -/

/-- Manifold derivative at `b₀ = π x` of the local linear-in-charts section realizing `A`. -/
private theorem hasMFDerivAt_localSection [IB.Boundaryless]
    (x : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    let x₀ := (ManifoldTotalSpace.homeomorph F E).symm x
    let b₀ := x₀.proj
    let e := trivializationAt F E b₀
    let w₀ := (e x₀).2
    let φ : B → EF := fun b ↦ extChartAt IF w₀ w₀ + A (extChartAt IB b₀ b - extChartAt IB b₀ b₀)
    let U : Set B := e.baseSet ∩ (chartAt HB b₀).source ∩ φ ⁻¹' (extChartAt IF w₀).target
    let s : B → ManifoldTotalSpace F E := fun b ↦
      ManifoldTotalSpace.homeomorph F E
        (e.toOpenPartialHomeomorph.symm (b, (extChartAt IF w₀).symm (φ b)))
    IsOpen U → b₀ ∈ U → ContinuousAt s b₀ → s b₀ = x →
      HasMFDerivAt IB (IB.prod IF) s b₀ ((ContinuousLinearMap.id 𝕜 EB).prod A) := by
  intro x₀ b₀ e w₀ φ U s hU_open hb₀_mem hs_cont hs_b₀
  set u₀ := extChartAt IB b₀ b₀
  set z₀ := extChartAt IF w₀ w₀
  refine ⟨hs_cont, ?_⟩
  rw [IB.range_eq_univ, hasFDerivWithinAt_univ]
  have hlin_deriv : HasFDerivAt (fun u : EB ↦ (u, z₀ + A (u - u₀)))
      ((ContinuousLinearMap.id 𝕜 EB).prod A) u₀ :=
    (hasFDerivAt_id u₀).prodMk (HasFDerivAt.const_add z₀
      (A.hasFDerivAt.comp u₀ ((hasFDerivAt_id u₀).sub_const u₀) |>.congr_fderiv (comp_id A)))
  refine hlin_deriv.congr_of_eventuallyEq ?_
  have hu₀_src : b₀ ∈ (extChartAt IB b₀).source := mem_extChartAt_source b₀
  have hnhds : (extChartAt IB b₀).target ∩ (extChartAt IB b₀).symm ⁻¹' U ∈ 𝓝 u₀ := by
    have hmem := Filter.inter_mem (extChartAt_target_mem_nhdsWithin_of_mem
      ((extChartAt IB b₀).map_source hu₀_src))
      (mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds' hu₀_src
        (hU_open.mem_nhds hb₀_mem)))
    rwa [IB.range_eq_univ, nhdsWithin_univ] at hmem
  filter_upwards [hnhds] with u hu
  have hs_b₀_eq : s b₀ = ManifoldTotalSpace.homeomorph F E x₀ :=
    hs_b₀.trans ((ManifoldTotalSpace.homeomorph F E).apply_symm_apply x).symm
  have hbv : ((extChartAt IB b₀).symm u,
      (extChartAt IF w₀).symm (φ ((extChartAt IB b₀).symm u))) ∈ e.target := by
    rw [e.target_eq]; exact ⟨hu.2.1.1, mem_univ _⟩
  have he_inv : trivializationAt F E x₀.proj (e.toOpenPartialHomeomorph.symm
      ((extChartAt IB b₀).symm u, (extChartAt IF w₀).symm (φ ((extChartAt IB b₀).symm u)))) =
      ((extChartAt IB b₀).symm u, (extChartAt IF w₀).symm (φ ((extChartAt IB b₀).symm u))) :=
    e.toOpenPartialHomeomorph.right_inv hbv
  rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, hs_b₀_eq]
  dsimp only [s]
  rw [ManifoldTotalSpace.extChartAt_homeomorph_apply, he_inv]
  change (extChartAt IB b₀ ((extChartAt IB b₀).symm u),
      extChartAt IF w₀ ((extChartAt IF w₀).symm (φ ((extChartAt IB b₀).symm u)))) =
    (u, z₀ + A (u - u₀))
  rw [(extChartAt IB b₀).right_inv hu.1, (extChartAt IF w₀).right_inv hu.2.2]
  dsimp only [φ]
  rw [(extChartAt IB b₀).right_inv hu.1]

/-- **Local smooth section realization of first jets.** When `IB` and `IF` are boundaryless and
`B`, `F` and `E` are `C^n`, every first jet `j` at `x : ManifoldTotalSpace F E` is realized at
`b₀ = π x` by a `C^n` local section `s` defined on an open neighbourhood `U` of `b₀`. -/
theorem exists_contMDiffOn_section_jetAt_eq [IB.Boundaryless] [IF.Boundaryless]
    {n : ℕ∞ω} [IsManifold IB n B] [IsManifold IF n F] [ContMDiffFiberBundle n F E IB IF]
    {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    ∃ (U : Set B) (s : B → ManifoldTotalSpace F E),
      IsOpen U ∧ ((ManifoldTotalSpace.homeomorph F E).symm x).proj ∈ U ∧
      ContMDiffOn IB (IB.prod IF) n s U ∧
      (∀ b ∈ U, ((ManifoldTotalSpace.homeomorph F E).symm (s b)).proj = b) ∧
      (⟨s ((ManifoldTotalSpace.homeomorph F E).symm x).proj,
        jetAt IB IF s ((ManifoldTotalSpace.homeomorph F E).symm x).proj⟩ :
          TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E)) = ⟨x, j⟩ := by
  set x₀ := (ManifoldTotalSpace.homeomorph F E).symm x
  set b₀ := x₀.proj
  set e := trivializationAt F E b₀
  set w₀ := (e x₀).2
  set A := chartCoordEquiv IB IF F E x j
  let φ : B → EF := fun b ↦ extChartAt IF w₀ w₀ + A (extChartAt IB b₀ b - extChartAt IB b₀ b₀)
  let U : Set B := e.baseSet ∩ (chartAt HB b₀).source ∩ φ ⁻¹' (extChartAt IF w₀).target
  let s : B → ManifoldTotalSpace F E := fun b ↦
    ManifoldTotalSpace.homeomorph F E
      (e.toOpenPartialHomeomorph.symm (b, (extChartAt IF w₀).symm (φ b)))
  have hlin : ContDiff 𝕜 n (fun u : EB ↦ extChartAt IF w₀ w₀ + A (u - extChartAt IB b₀ b₀)) :=
    contDiff_const.add (A.contDiff.comp (contDiff_id.sub contDiff_const))
  have hφ_cont : ContMDiffOn IB 𝓘(𝕜, EF) n φ (chartAt HB b₀).source :=
    hlin.contMDiff.comp_contMDiffOn contMDiffOn_extChartAt
  have hU_open : IsOpen U :=
    (hφ_cont.continuousOn.mono inter_subset_right).isOpen_inter_preimage
      (e.open_baseSet.inter (chartAt HB b₀).open_source) (isOpen_extChartAt_target w₀)
  have hφ_b₀ : φ b₀ = extChartAt IF w₀ w₀ := by simp [φ]
  have hb₀_mem : b₀ ∈ U := ⟨⟨mem_baseSet_trivializationAt F E b₀, mem_chart_source HB b₀⟩,
    by rw [mem_preimage, hφ_b₀]; exact mem_extChartAt_target w₀⟩
  have hs_b₀ : s b₀ = x := by
    simp only [s, hφ_b₀, (extChartAt IF w₀).left_inv (mem_extChartAt_source w₀)]
    rw [e.symm_apply_mk_proj (e.mem_source.2 (mem_baseSet_trivializationAt F E b₀))]
    exact (ManifoldTotalSpace.homeomorph F E).apply_symm_apply x
  have hproj : ∀ b ∈ U, ((ManifoldTotalSpace.homeomorph F E).symm (s b)).proj = b := fun b hb ↦ by
    simp only [s, Homeomorph.symm_apply_apply]; exact e.proj_symm_apply' hb.1.1
  have hs_smooth : ContMDiffOn IB (IB.prod IF) n s U := by
    have hF : ContMDiffOn IB IF n (fun b ↦ (extChartAt IF w₀).symm (φ b)) U :=
      (contMDiffOn_extChartAt_symm (x := w₀)).comp (hφ_cont.mono fun _ hb ↦ hb.1.2) fun _ hb ↦ hb.2
    exact (ManifoldTotalSpace.contMDiffOn_trivialization_symm (n := n) e).comp
      (contMDiffOn_id.prodMk hF) fun b hb ↦ by rw [e.target_eq]; exact ⟨hb.1.1, mem_univ _⟩
  have hchart := hasMFDerivAt_localSection x A hU_open hb₀_mem
    ((hs_smooth b₀ hb₀_mem).contMDiffAt (hU_open.mem_nhds hb₀_mem)).continuousAt hs_b₀
  have hmk : ∀ {x₁ x₂ : ManifoldTotalSpace F E} {A₁ A₂ : EB →L[𝕜] EF},
      x₁ = x₂ → A₁ = A₂ →
      (⟨x₁, (chartCoordEquiv IB IF F E x₁).symm A₁⟩ :
        TotalSpace (EB →L[𝕜] EF) (FirstJet IB IF F E)) =
        ⟨x₂, (chartCoordEquiv IB IF F E x₂).symm A₂⟩ := by
    rintro _ _ _ _ rfl rfl; rfl
  refine ⟨U, s, hU_open, hb₀_mem, hs_smooth, hproj, ?_⟩
  refine (hmk hs_b₀ (by rw [hchart.mfderiv, snd_comp_prod])).trans ?_
  exact congrArg (TotalSpace.mk' (EB →L[𝕜] EF) x) ((chartCoordEquiv IB IF F E x).symm_apply_apply j)

/-! #### Trivial bundle over a normed space and concrete jet/contact check -/

section Trivial

/-- For a differentiable function `u : EB → EF` viewed as a section of `Bundle.Trivial EB EF`, the
preferred-chart derivative coordinate of its first jet at `b` is `fderiv 𝕜 u b`. -/
@[simp]
theorem chartCoordEquiv_jet_trivial {u : EB → EF} {b : EB} (hu : DifferentiableAt 𝕜 u b) :
    chartCoordEquiv 𝓘(𝕜, EB) 𝓘(𝕜, EF) EF (Bundle.Trivial EB EF)
      (ManifoldTotalSpace.homeomorph EF (Bundle.Trivial EB EF) ⟨b, u b⟩)
      (jet 𝓘(𝕜, EB) 𝓘(𝕜, EF) EF u b) = fderiv 𝕜 u b := by
  have hcont : ContinuousAt
      (fun y ↦ ManifoldTotalSpace.homeomorph EF (Bundle.Trivial EB EF) ⟨y, u y⟩) b :=
    (ManifoldTotalSpace.homeomorph EF (Bundle.Trivial EB EF)).continuous.continuousAt.comp
      ((Bundle.Trivial.homeomorphProd EB EF).symm.continuous.continuousAt.comp
        (continuousAt_id.prodMk hu.continuousAt))
  have hf : HasMFDerivAt 𝓘(𝕜, EB) (𝓘(𝕜, EB).prod 𝓘(𝕜, EF))
      (fun y ↦ ManifoldTotalSpace.homeomorph EF (Bundle.Trivial EB EF) ⟨y, u y⟩) b
      ((ContinuousLinearMap.id 𝕜 EB).prod (fderiv 𝕜 u b)) := by
    refine ⟨hcont, ?_⟩
    rw [ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ]
    have hrep : writtenInExtChartAt 𝓘(𝕜, EB) (𝓘(𝕜, EB).prod 𝓘(𝕜, EF)) b
        (fun y ↦ ManifoldTotalSpace.homeomorph EF (Bundle.Trivial EB EF) ⟨y, u y⟩) =
        fun y ↦ (y, u y) := by
      funext y
      rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply,
        ManifoldTotalSpace.extChartAt_homeomorph_apply]
      simp
    rw [hrep]
    exact (hasFDerivAt_id b).prodMk hu.hasFDerivAt
  let sTot : EB → ManifoldTotalSpace EF (Bundle.Trivial EB EF) :=
    fun y ↦ ManifoldTotalSpace.homeomorph EF (Bundle.Trivial EB EF) ⟨y, u y⟩
  change chartCoordEquiv 𝓘(𝕜, EB) 𝓘(𝕜, EF) EF (Bundle.Trivial EB EF) (sTot b)
      (jetAt 𝓘(𝕜, EB) 𝓘(𝕜, EF) sTot b) = fderiv 𝕜 u b
  rw [chartCoordEquiv_jetAt, hf.mfderiv]
  ext v
  rfl

/-- Concrete check on `Bundle.Trivial ℝ ℝ`: for `u(x) = x * x` at `x = 1`, the first jet sits over
`(1, 1)` with derivative coordinate `2`, and its contact form vanishes on the prolonged tangent
vector `(1, 2)` while evaluating to `1` on the unit vertical tangent vector `(0, 1)`. -/
theorem jet_sq_trivial_check :
    let u : ℝ → Bundle.Trivial ℝ ℝ _ := fun x : ℝ ↦ x * x
    let j := jet 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ u 1
    ManifoldTotalSpace.diffeomorphProd ∞ ℝ ℝ 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (ManifoldTotalSpace.homeomorph ℝ (Bundle.Trivial ℝ ℝ) ⟨1, u 1⟩) = (1, 1) ∧
      chartCoordEquiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ (Bundle.Trivial ℝ ℝ) _ j 1 = 2 ∧
      (show ℝ from j.contactForm ((1 : ℝ), (2 : ℝ))) = 0 ∧
      (show ℝ from j.contactForm ((0 : ℝ), (1 : ℝ))) = 1 := by
  intro u j
  have hu : DifferentiableAt ℝ u 1 := differentiableAt_id.mul differentiableAt_id
  have hderiv : chartCoordEquiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ (Bundle.Trivial ℝ ℝ) _ j = fderiv ℝ u 1 :=
    chartCoordEquiv_jet_trivial hu
  have hmul : HasFDerivAt u
      ((1 : ℝ) • ContinuousLinearMap.id ℝ ℝ + (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 :=
    (hasFDerivAt_id (1 : ℝ)).mul (hasFDerivAt_id (1 : ℝ))
  have hfderiv_val : ∀ t : ℝ, fderiv ℝ u 1 t = 2 * t := fun t ↦ by
    rw [hmul.fderiv]
    simp only [add_apply, smul_apply, id_apply, smul_eq_mul]
    ring
  refine ⟨by rw [ManifoldTotalSpace.diffeomorphProd_homeomorph]; norm_num [u], ?_, ?_, ?_⟩
  · rw [hderiv, hfderiv_val]; norm_num
  · rw [contactForm_apply_chart, hderiv, hfderiv_val]; norm_num
  · rw [contactForm_apply_chart, hderiv, hfderiv_val]; norm_num

end Trivial

end Prolongation

/-! ### First-jet connections (Ehresmann splittings) -/

section Connection

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- **Covariant derivative of a local section with respect to a first-jet connection
`Γ : ∀ x, FirstJet IB IF F E x`.** Subtracting `Γ (s b)` from `j¹s(b)` in the affine torsor gives
`(Γ (s b)).contactForm ∘ mfderiv s b : T_b B →L[𝕜] V_{s b} E`. -/
theorem jetAt_vsub_connection (Γ : ∀ x : ManifoldTotalSpace F E, FirstJet IB IF F E x)
    {s : B → ManifoldTotalSpace F E} {b : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s b)
    (hproj : (fun y ↦ ((ManifoldTotalSpace.homeomorph F E).symm (s y)).proj) =ᶠ[𝓝 b] id) :
    jetAt IB IF s b -ᵥ Γ (s b) = (Γ (s b)).contactForm.comp (mfderiv IB (IB.prod IF) s b) := by
  rw [vsub_def, tangentLift_jetAt hs hproj]
  rfl

/-- A differentiable local section is horizontal for a first-jet connection `Γ` at `b` if and only
if its covariant derivative `jetAt IB IF s b -ᵥ Γ (s b)` vanishes. -/
theorem jetAt_vsub_connection_eq_zero_iff (Γ : ∀ x : ManifoldTotalSpace F E, FirstJet IB IF F E x)
    {s : B → ManifoldTotalSpace F E} {b : B} :
    jetAt IB IF s b -ᵥ Γ (s b) = 0 ↔ jetAt IB IF s b = Γ (s b) :=
  vsub_eq_zero_iff_eq

/-- **Difference law for first-jet connections.** Two connections `Γ₁, Γ₂` induce covariant
derivatives on `FirstJet` whose difference is the tensor `Γ₁ x -ᵥ Γ₂ x`, independent of the jet
`j`. -/
theorem vsub_connection_sub_vsub_connection
    (Γ₁ Γ₂ : ∀ x : ManifoldTotalSpace F E, FirstJet IB IF F E x)
    {x : ManifoldTotalSpace F E} (j : FirstJet IB IF F E x) :
    (j -ᵥ Γ₂ x) - (j -ᵥ Γ₁ x) = Γ₁ x -ᵥ Γ₂ x := by
  rw [sub_eq_iff_eq_add, add_comm, vsub_add_vsub_cancel]

end Connection

end FirstJet

end GeneralFiber

/-! ### Comparison with `FirstJetBundle` for a smooth vector bundle -/

section VectorBundle

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

namespace FirstJet

variable {IB}

/-- Near the image of `x₀` in its preferred chart, the fibre coordinate of the total-space chart
transition agrees with `FirstJetBundle.fiberCoordChange` along the base chart transition. -/
private theorem snd_extChartAt_comp_symm_eventuallyEq (x₀ i₀ : TotalSpace F V)
    (hbi : x₀.proj ∈ FirstJetBundle.baseSet (H := HB) F V i₀.proj) :
    (Prod.snd ∘ (extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V i₀) ∘
      (extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V x₀)).symm))
      =ᶠ[𝓝[range (IB.prod 𝓘(𝕜, F))]
        (extChartAt IB x₀.proj x₀.proj, (trivializationAt F V x₀.proj x₀).2)]
      fun y : EB × F ↦ FirstJetBundle.fiberCoordChange IB F V x₀.proj i₀.proj
        ((extChartAt IB i₀.proj ∘ (extChartAt IB x₀.proj).symm) y.1) y.2 := by
  have hmaps : MapsTo Prod.fst (range (IB.prod 𝓘(𝕜, F))) (range IB) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨p.1, rfl⟩
  have hU : (Prod.fst ⁻¹' ((extChartAt IB x₀.proj).target ∩
      (extChartAt IB x₀.proj).symm ⁻¹'
        (FirstJetBundle.baseSet (H := HB) F V x₀.proj ∩
          FirstJetBundle.baseSet (H := HB) F V i₀.proj))) ∈
      𝓝[range (IB.prod 𝓘(𝕜, F))]
        (extChartAt IB x₀.proj x₀.proj, (trivializationAt F V x₀.proj x₀).2) := by
    refine (continuous_fst.continuousWithinAt.tendsto_nhdsWithin hmaps) ?_
    refine Filter.inter_mem (extChartAt_target_mem_nhdsWithin (I := IB) x₀.proj) ?_
    exact mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds (I := IB) (x := x₀.proj)
      (((FirstJetBundle.isOpen_baseSet F V x₀.proj).inter
        (FirstJetBundle.isOpen_baseSet F V i₀.proj)).mem_nhds
        ⟨FirstJetBundle.mem_baseSet_self F V x₀.proj, hbi⟩))
  let f : EB × F → F := fun p ↦
    (extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V i₀)
      ((extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V x₀)).symm p)).2
  filter_upwards [hU] with y hy
  have hy_symm : extChartAt IB x₀.proj ((extChartAt IB x₀.proj).symm y.1) = y.1 :=
    (extChartAt IB x₀.proj).right_inv hy.1
  obtain ⟨hy_x₁, hy_x₂⟩ := (FirstJetBundle.mem_baseSet_iff F V).1 hy.2.1
  obtain ⟨hy_i₁, hy_i₂⟩ := (FirstJetBundle.mem_baseSet_iff F V).1 hy.2.2
  have hf_eq : f y = f (extChartAt IB x₀.proj ((extChartAt IB x₀.proj).symm y.1), y.2) :=
    congrArg f (Prod.ext hy_symm.symm rfl)
  have h1 : f y = (trivializationAt F V x₀.proj).coordChangeL 𝕜
      (trivializationAt F V i₀.proj) ((extChartAt IB x₀.proj).symm y.1) y.2 :=
    hf_eq.trans (VerticalBundle.extChartAt_snd_symm_eq_coordChangeL x₀ i₀ hy_x₁ hy_x₂ hy_i₁ y.2)
  have h2 : FirstJetBundle.fiberCoordChange IB F V x₀.proj i₀.proj
      ((extChartAt IB i₀.proj ∘ (extChartAt IB x₀.proj).symm) y.1) y.2 =
      (trivializationAt F V x₀.proj).coordChangeL 𝕜
        (trivializationAt F V i₀.proj) ((extChartAt IB x₀.proj).symm y.1) y.2 := by
    rw [Function.comp_apply, FirstJetBundle.fiberCoordChange_extChartAt hy_i₂,
      ContinuousLinearEquiv.coe_coe]
  exact h1.trans h2.symm

variable [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F V IB]

/-- Fréchet derivative within `range (IB.prod 𝓘(𝕜, F))` of the model-space expression for the
fibre coordinate of a total-space chart transition. -/
private theorem hasFDerivWithinAt_fiberCoordChange_comp (x₀ i₀ : TotalSpace F V)
    (hbi : x₀.proj ∈ FirstJetBundle.baseSet (H := HB) F V i₀.proj) :
    HasFDerivWithinAt
      (fun y : EB × F ↦ FirstJetBundle.fiberCoordChange IB F V x₀.proj i₀.proj
        ((extChartAt IB i₀.proj ∘ (extChartAt IB x₀.proj).symm) y.1) y.2)
      (((fderivWithin 𝕜 (FirstJetBundle.fiberCoordChange IB F V x₀.proj i₀.proj) (range IB)
          (extChartAt IB i₀.proj x₀.proj)).comp
        ((tangentCoordChange IB x₀.proj i₀.proj x₀.proj).comp
          (ContinuousLinearMap.fst 𝕜 EB F))).flip (trivializationAt F V x₀.proj x₀).2 +
        ((trivializationAt F V x₀.proj).coordChangeL 𝕜
          (trivializationAt F V i₀.proj) x₀.proj : F →L[𝕜] F).comp
          (ContinuousLinearMap.snd 𝕜 EB F))
      (range (IB.prod 𝓘(𝕜, F)))
      (extChartAt IB x₀.proj x₀.proj, (trivializationAt F V x₀.proj x₀).2) := by
  let z₀ : EB × F := (extChartAt IB x₀.proj x₀.proj, (trivializationAt F V x₀.proj x₀).2)
  have hbase : HasFDerivWithinAt
      ((extChartAt IB i₀.proj ∘ (extChartAt IB x₀.proj).symm) ∘ Prod.fst)
      ((tangentCoordChange IB x₀.proj i₀.proj x₀.proj).comp (ContinuousLinearMap.fst 𝕜 EB F))
      (range (IB.prod 𝓘(𝕜, F))) z₀ :=
    (hasFDerivWithinAt_tangentCoordChange
      ⟨mem_extChartAt_source x₀.proj,
        FirstJetBundle.mem_extChartAt_source_of_mem_baseSet IB hbi⟩).comp z₀
      (hasFDerivAt_fst.hasFDerivWithinAt (s := range (IB.prod 𝓘(𝕜, F))))
      fun y hy ↦ by rw [ModelWithCorners.range_prod] at hy; exact hy.1
  have hfib : HasFDerivWithinAt (FirstJetBundle.fiberCoordChange IB F V x₀.proj i₀.proj)
      (fderivWithin 𝕜 (FirstJetBundle.fiberCoordChange IB F V x₀.proj i₀.proj) (range IB)
        (extChartAt IB i₀.proj x₀.proj))
      (range IB) ((extChartAt IB i₀.proj ∘ (extChartAt IB x₀.proj).symm) z₀.1) := by
    dsimp only [z₀]
    rw [Function.comp_apply, (extChartAt IB x₀.proj).left_inv (mem_extChartAt_source x₀.proj)]
    exact FirstJetBundle.hasFDerivWithinAt_fiberCoordChange
      (mem_baseSet_trivializationAt F V x₀.proj) hbi
  exact ((hfib.comp z₀ hbase fun y _ ↦ by
    rw [Function.comp_apply, Function.comp_apply, extChartAt_coe]; exact mem_range_self _
  ).clm_apply (hasFDerivAt_snd.hasFDerivWithinAt (s := range (IB.prod 𝓘(𝕜, F))))).congr_fderiv
    (by
      dsimp only [z₀]
      simp only [Function.comp_apply,
        (extChartAt IB x₀.proj).left_inv (mem_extChartAt_source x₀.proj),
        FirstJetBundle.fiberCoordChange_extChartAt
          ((FirstJetBundle.mem_baseSet_iff F V).1 hbi).2, add_comm])

/-- Explicit derivative of the fibre coordinate of a preferred chart transition on
`ManifoldTotalSpace F V` in terms of `FirstJetBundle.fiberCoordChange`. -/
theorem snd_comp_tangentCoordChange_vectorBundle (x₀ i₀ : TotalSpace F V)
    (hx : ManifoldTotalSpace.homeomorph F V x₀ ∈
      (chartAt (ModelProd HB F) (ManifoldTotalSpace.homeomorph F V i₀)).source) :
    (ContinuousLinearMap.snd 𝕜 EB F).comp
      (tangentCoordChange (IB.prod 𝓘(𝕜, F))
        (ManifoldTotalSpace.homeomorph F V x₀)
        (ManifoldTotalSpace.homeomorph F V i₀)
        (ManifoldTotalSpace.homeomorph F V x₀)) =
      ((fderivWithin 𝕜 (FirstJetBundle.fiberCoordChange IB F V x₀.proj i₀.proj) (range IB)
          (extChartAt IB i₀.proj x₀.proj)).comp
        ((tangentCoordChange IB x₀.proj i₀.proj x₀.proj).comp
          (ContinuousLinearMap.fst 𝕜 EB F))).flip (trivializationAt F V x₀.proj x₀).2 +
        ((trivializationAt F V x₀.proj).coordChangeL 𝕜
          (trivializationAt F V i₀.proj) x₀.proj : F →L[𝕜] F).comp
          (ContinuousLinearMap.snd 𝕜 EB F) := by
  have hbi : x₀.proj ∈ FirstJetBundle.baseSet (H := HB) F V i₀.proj := by
    simpa only [FirstJetBundle.mem_baseSet_iff, Homeomorph.symm_apply_apply] using
      ManifoldTotalSpace.proj_mem_of_mem_chart_source hx
  have hxx : ManifoldTotalSpace.homeomorph F V x₀ ∈
      (extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V x₀)).source :=
    mem_extChartAt_source _
  have hxi : ManifoldTotalSpace.homeomorph F V x₀ ∈
      (extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V i₀)).source := by
    rwa [extChartAt_source]
  let y₀ : EB × F := extChartAt (IB.prod 𝓘(𝕜, F)) (ManifoldTotalSpace.homeomorph F V x₀)
    (ManifoldTotalSpace.homeomorph F V x₀)
  have hy₀ : y₀ = (extChartAt IB x₀.proj x₀.proj, (trivializationAt F V x₀.proj x₀).2) := by
    dsimp only [y₀]
    rw [ManifoldTotalSpace.extChartAt_homeomorph_apply,
      (trivializationAt F V x₀.proj).coe_fst' (mem_baseSet_trivializationAt F V x₀.proj),
      extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
  have hLHS := hasFDerivAt_snd.comp_hasFDerivWithinAt y₀
    (hasFDerivWithinAt_tangentCoordChange (I := IB.prod 𝓘(𝕜, F)) ⟨hxx, hxi⟩)
  have hRHS := hy₀ ▸ hasFDerivWithinAt_fiberCoordChange_comp x₀ i₀ hbi
  have heq := hy₀ ▸ snd_extChartAt_comp_symm_eventuallyEq x₀ i₀ hbi
  have hyr := extChartAt_target_subset_range _ ((extChartAt _ _).map_source hxx)
  exact (IB.prod 𝓘(𝕜, F)).uniqueDiffOn _ hyr |>.eq
    (hLHS.congr_of_eventuallyEq heq.symm (heq.self_of_nhdsWithin hyr).symm) hRHS

/-- **Agreement of `FirstJet.coordChange` and `FirstJetBundle.coordChange` on vector bundles.** -/
theorem coordChange_eq_firstJetBundle_coordChange_snd (x₀ i₀ : TotalSpace F V)
    (hx : ManifoldTotalSpace.homeomorph F V x₀ ∈
      (chartAt (ModelProd HB F) (ManifoldTotalSpace.homeomorph F V i₀)).source)
    (A : EB →L[𝕜] F) :
    coordChange IB 𝓘(𝕜, F) F V
      (ManifoldTotalSpace.homeomorph F V x₀)
      (ManifoldTotalSpace.homeomorph F V i₀)
      (ManifoldTotalSpace.homeomorph F V x₀) A =
      (FirstJetBundle.coordChange IB F V x₀.proj i₀.proj x₀.proj
        ((trivializationAt F V x₀.proj x₀).2, A)).2 := by
  have hbi : x₀.proj ∈ (extChartAt IB i₀.proj).source := by
    rw [extChartAt_source]
    simpa only [Homeomorph.symm_apply_apply] using
      (ManifoldTotalSpace.proj_mem_of_mem_chart_source hx).2
  have hbx : x₀.proj ∈ (extChartAt IB x₀.proj).source := mem_extChartAt_source x₀.proj
  rw [coordChange_apply, ← comp_assoc, snd_comp_tangentCoordChange_vectorBundle x₀ i₀ hx,
    FirstJetBundle.coordChange_apply]
  simp only [Homeomorph.symm_apply_apply]
  ext u
  simp only [add_apply, comp_apply, flip_apply, ContinuousLinearMap.prod_apply, id_apply,
    coe_fst', coe_snd']
  rw [tangentCoordChange_comp ⟨⟨hbi, hbx⟩, hbi⟩, tangentCoordChange_self hbi]

variable (IB F V) in
/-- Preferred-chart constructor `(v, A)` of a vector-bundle first jet at `b`. Kept opaque so
unfolding comparison maps never exposes raw `Prod` terms at `FirstJetBundle` type. -/
def mkFirstJetBundle (b : B) (v : F) (A : EB →L[𝕜] F) : FirstJetBundle IB F V b :=
  (v, A)

variable (IB F V) in
/-- Preferred-chart derivative coordinate of `j : FirstJetBundle IB F V b`. Kept opaque so
unfolding comparison maps never applies `Prod.snd` directly at `FirstJetBundle` type. -/
def firstJetBundleSnd {b : B} (j : FirstJetBundle IB F V b) : EB →L[𝕜] F :=
  j.2

/-- Evaluating `FirstJetBundle.value` on `mkFirstJetBundle` recovers the inverse preferred
trivialization at `b`. -/
@[simp]
theorem value_mkFirstJetBundle (b : B) (v : F) (A : EB →L[𝕜] F) :
    FirstJetBundle.value IB F b (mkFirstJetBundle IB F V b v A) =
      (trivializationAt F V b).symm b v :=
  FirstJetBundle.value_apply IB F b (mkFirstJetBundle IB F V b v A)

/-- `firstJetBundleSnd` extracts the derivative coordinate passed to `mkFirstJetBundle`. -/
@[simp]
theorem firstJetBundleSnd_mkFirstJetBundle (b : B) (v : F) (A : EB →L[𝕜] F) :
    firstJetBundleSnd IB F V (mkFirstJetBundle IB F V b v A) = A :=
  (rfl)

/-- Reassembling a jet in `FirstJetBundle` from its `value` coordinate and `firstJetBundleSnd`
recovers the original jet. -/
theorem mkFirstJetBundle_value_firstJetBundleSnd {b : B} (j : FirstJetBundle IB F V b) :
    mkFirstJetBundle IB F V b (trivializationAt F V b ⟨b, FirstJetBundle.value IB F b j⟩).2
      (firstJetBundleSnd IB F V j) = j := by
  refine Prod.ext ?_ rfl
  rw [FirstJetBundle.value_apply]
  exact congrArg Prod.snd
    ((trivializationAt F V b).apply_mk_symm (mem_baseSet_trivializationAt F V b) j.1)

variable (IB F V) in
/-- Forward map of the comparison between `FirstJet` of a vector bundle `V` and `FirstJetBundle`. -/
-- Expose so basepoints reduce definitionally in dependent fibre statements on `FirstJetBundle`.
@[expose]
def toFirstJetBundle (p : TotalSpace (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V)) :
    TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) :=
  let x₀ := (ManifoldTotalSpace.homeomorph F V).symm p.proj
  ⟨x₀.proj, mkFirstJetBundle IB F V x₀.proj (trivializationAt F V x₀.proj x₀).2
    (chartCoordEquiv IB 𝓘(𝕜, F) F V p.proj p.2)⟩

variable (IB F V) in
/-- Inverse map of the comparison between `FirstJet` of a vector bundle `V` and `FirstJetBundle`. -/
-- Expose so basepoints reduce definitionally in dependent fibre statements on `FirstJet`.
@[expose]
def ofFirstJetBundle (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    TotalSpace (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V) :=
  let x := ManifoldTotalSpace.homeomorph F V
    ⟨q.proj, FirstJetBundle.value IB F q.proj q.2⟩
  ⟨x, (chartCoordEquiv IB 𝓘(𝕜, F) F V x).symm (firstJetBundleSnd IB F V q.2)⟩

/-- `toFirstJetBundle` is a left inverse to `ofFirstJetBundle`. -/
theorem toFirstJetBundle_ofFirstJetBundle
    (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    toFirstJetBundle IB F V (ofFirstJetBundle IB F V q) = q := by
  rcases q with ⟨b, qj⟩
  dsimp only [toFirstJetBundle, ofFirstJetBundle]
  let mkJet : TotalSpace F V → (EB →L[𝕜] F) →
      TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) := fun y A ↦
    ⟨y.proj, mkFirstJetBundle IB F V y.proj (trivializationAt F V y.proj y).2 A⟩
  change mkJet ((ManifoldTotalSpace.homeomorph F V).symm
      (ManifoldTotalSpace.homeomorph F V ⟨b, FirstJetBundle.value IB F b qj⟩))
    (chartCoordEquiv IB 𝓘(𝕜, F) F V _
      ((chartCoordEquiv IB 𝓘(𝕜, F) F V _).symm (firstJetBundleSnd IB F V qj))) = ⟨b, qj⟩
  rw [Equiv.apply_symm_apply, Homeomorph.symm_apply_apply]
  exact congrArg (TotalSpace.mk' (F × (EB →L[𝕜] F)) b)
    (mkFirstJetBundle_value_firstJetBundleSnd qj)

/-- `toFirstJetBundle` is injective. -/
theorem toFirstJetBundle_injective : Function.Injective (toFirstJetBundle IB F V) := by
  rintro ⟨x₁, j₁⟩ ⟨x₂, j₂⟩ h
  obtain ⟨⟨b₁, v₁⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph F V).surjective x₁
  obtain ⟨⟨b₂, v₂⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph F V).surjective x₂
  have hb : b₁ = b₂ := by
    simpa only [toFirstJetBundle, Homeomorph.symm_apply_apply] using congrArg TotalSpace.proj h
  subst hb
  dsimp only [toFirstJetBundle] at h
  let mkJet : TotalSpace F V → (EB →L[𝕜] F) →
      TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) := fun y A ↦
    ⟨y.proj, mkFirstJetBundle IB F V y.proj (trivializationAt F V y.proj y).2 A⟩
  change mkJet ((ManifoldTotalSpace.homeomorph F V).symm
      (ManifoldTotalSpace.homeomorph F V ⟨b₁, v₁⟩)) _ =
    mkJet ((ManifoldTotalSpace.homeomorph F V).symm
      (ManifoldTotalSpace.homeomorph F V ⟨b₁, v₂⟩)) _ at h
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at h
  have hfib := TotalSpace.mk_injective b₁ h
  have hv : v₁ = v₂ := by
    have hfst : (trivializationAt F V b₁ ⟨b₁, v₁⟩).2 = (trivializationAt F V b₁ ⟨b₁, v₂⟩).2 :=
      congrArg Prod.fst hfib
    simpa only [(trivializationAt F V b₁).symm_apply_apply_mk (mem_baseSet_trivializationAt F V b₁)]
      using congrArg ((trivializationAt F V b₁).symm b₁) hfst
  subst hv
  have hsnd : chartCoordEquiv IB 𝓘(𝕜, F) F V _ j₁ = chartCoordEquiv IB 𝓘(𝕜, F) F V _ j₂ :=
    congrArg Prod.snd (TotalSpace.mk_injective b₁ h)
  exact congrArg (TotalSpace.mk' (EB →L[𝕜] F) _)
    ((chartCoordEquiv IB 𝓘(𝕜, F) F V _).injective hsnd)

/-- `ofFirstJetBundle` is a left inverse to `toFirstJetBundle`. -/
theorem ofFirstJetBundle_toFirstJetBundle
    (p : TotalSpace (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V)) :
    ofFirstJetBundle IB F V (toFirstJetBundle IB F V p) = p :=
  toFirstJetBundle_injective (toFirstJetBundle_ofFirstJetBundle (toFirstJetBundle IB F V p))

/-- `toFirstJetBundle` is `C^n` for every `n : ℕ∞ω` when `B` and `V` are `C^1`. -/
theorem contMDiff_toFirstJetBundle (n : ℕ∞ω) :
    ContMDiff ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) n
      (toFirstJetBundle IB F V) := by
  intro p₀
  have hp_proj : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) (IB.prod 𝓘(𝕜, F)) n
      TotalSpace.proj p₀ := Bundle.contMDiffAt_proj (IB := IB.prod 𝓘(𝕜, F)) _
  have hbase : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) IB n
      (fun p ↦ (toFirstJetBundle IB F V p).proj) p₀ :=
    (ManifoldTotalSpace.contMDiff_proj n F V IB 𝓘(𝕜, F) p₀.proj).comp p₀ hp_proj
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hbase, ?_⟩
  have hv_coord := (Bundle.contMDiffAt_totalSpace_iff.1
    ((ManifoldTotalSpace.contMDiff_homeomorph_symm n F V IB p₀.proj).comp p₀ hp_proj)).2
  have hA_coord := (Bundle.contMDiffAt_totalSpace_iff.1
    (contMDiffAt_id (I := (IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) (n := n) (x := p₀))).2
  refine (hv_coord.prodMk_space hA_coord).congr_of_eventuallyEq ?_
  have hU : TotalSpace.proj ⁻¹' (chartAt (ModelProd HB F) p₀.proj).source ∈ 𝓝 p₀ :=
    ((FiberBundle.continuous_proj (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V)).isOpen_preimage _
      (chartAt _ p₀.proj).open_source).mem_nhds (mem_chart_source (ModelProd HB F) p₀.proj)
  filter_upwards [hU] with p hp
  let x₀ := (ManifoldTotalSpace.homeomorph F V).symm p.proj
  let i₀ := (ManifoldTotalSpace.homeomorph F V).symm p₀.proj
  have hp' : ManifoldTotalSpace.homeomorph F V x₀ ∈
      (chartAt (ModelProd HB F) (ManifoldTotalSpace.homeomorph F V i₀)).source := by
    simpa only [mem_preimage, x₀, i₀, Homeomorph.apply_symm_apply] using hp
  have hbi := ManifoldTotalSpace.proj_mem_of_mem_chart_source hp'
  simp only [Homeomorph.symm_apply_apply] at hbi
  let r : F × (EB →L[𝕜] F) :=
    ((trivializationAt F V x₀.proj x₀).2, chartCoordEquiv IB 𝓘(𝕜, F) F V p.proj p.2)
  have htriv := FirstJetBundle.trivializationAt_apply_snd (I := IB) (F := F) (V := V)
    i₀.proj (toFirstJetBundle IB F V p)
  have hc := FirstJetBundle.coordChange_apply (I := IB) (F := F) (V := V) x₀.proj i₀.proj x₀.proj r
  refine Prod.ext ?_ ?_
  · change (trivializationAt (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) i₀.proj
        (toFirstJetBundle IB F V p)).2.1 = (trivializationAt F V i₀.proj x₀).2
    exact (congrArg Prod.fst (htriv.trans hc)).trans
      (Trivialization.coordChangeL_apply_snd 𝕜 _ _ (mem_baseSet_trivializationAt F V x₀.proj) hbi.1)
  · change (trivializationAt (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) i₀.proj
        (toFirstJetBundle IB F V p)).2.2 =
      (trivializationAt (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V) p₀.proj p).2
    have hcoord := coordChange_eq_firstJetBundle_coordChange_snd (IB := IB) x₀ i₀ hp'
      (chartCoordEquiv IB 𝓘(𝕜, F) F V p.proj p.2)
    dsimp only [x₀, i₀] at hcoord
    rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at hcoord
    exact (congrArg Prod.snd htriv).trans
      (hcoord.symm.trans (trivializationAt_apply_snd (IB := IB) (IF := 𝓘(𝕜, F)) p₀.proj p).symm)

/-- The bundled value projection `TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) →
TotalSpace F V` is `C^n` at every point `q₀`. -/
private theorem contMDiffAt_value_totalSpace (n : ℕ∞ω)
    (q₀ : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    ContMDiffAt (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) (IB.prod 𝓘(𝕜, F)) n
      (fun q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) ↦
        (⟨q.proj, FirstJetBundle.value IB F q.proj q.2⟩ : TotalSpace F V)) q₀ := by
  have hq_proj : ContMDiffAt (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) IB n TotalSpace.proj q₀ :=
    Bundle.contMDiffAt_proj (IB := IB) _
  have hq_coord := (Bundle.contMDiffAt_totalSpace_iff.1
    (contMDiffAt_id (I := IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) (n := n) (x := q₀))).2
  have hU : TotalSpace.proj ⁻¹' FirstJetBundle.baseSet (H := HB) F V q₀.proj ∈ 𝓝 q₀ :=
    ((FiberBundle.continuous_proj _ (FirstJetBundle IB F V)).isOpen_preimage _
      (FirstJetBundle.isOpen_baseSet F V q₀.proj)).mem_nhds
      (FirstJetBundle.mem_baseSet_self F V q₀.proj)
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hq_proj, ?_⟩
  refine ((ContinuousLinearMap.fst 𝕜 F (EB →L[𝕜] F)).contDiff.contMDiff.contMDiffAt.comp
    q₀ hq_coord).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  obtain ⟨hq₁, _⟩ := (FirstJetBundle.mem_baseSet_iff F V).1 hq
  let r : F × (EB →L[𝕜] F) := q.2
  have htriv := FirstJetBundle.trivializationAt_apply_snd (I := IB) (F := F) (V := V) q₀.proj q
  have hc := FirstJetBundle.coordChange_apply (I := IB) (F := F) (V := V) q.proj q₀.proj q.proj r
  have hval : FirstJetBundle.value IB F q.proj q.2 =
      (trivializationAt F V q.proj).symm q.proj r.1 :=
    FirstJetBundle.value_apply IB F q.proj q.2
  change (trivializationAt F V q₀.proj ⟨q.proj, FirstJetBundle.value IB F q.proj q.2⟩).2 =
    (trivializationAt (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) q₀.proj q).2.1
  rw [hval,
    ← Trivialization.coordChangeL_apply (R := 𝕜) _ _
      ⟨mem_baseSet_trivializationAt F V q.proj, hq₁⟩]
  exact (congrArg Prod.fst (htriv.trans hc)).symm

/-- `ofFirstJetBundle` is `C^n` for every `n : ℕ∞ω` when `B` and `V` are `C^1`. -/
theorem contMDiff_ofFirstJetBundle (n : ℕ∞ω) :
    ContMDiff (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) n
      (ofFirstJetBundle IB F V) := by
  intro q₀
  have hq_coord := (Bundle.contMDiffAt_totalSpace_iff.1
    (contMDiffAt_id (I := IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) (n := n) (x := q₀))).2
  have hU : TotalSpace.proj ⁻¹' FirstJetBundle.baseSet (H := HB) F V q₀.proj ∈ 𝓝 q₀ :=
    ((FiberBundle.continuous_proj _ (FirstJetBundle IB F V)).isOpen_preimage _
      (FirstJetBundle.isOpen_baseSet F V q₀.proj)).mem_nhds
      (FirstJetBundle.mem_baseSet_self F V q₀.proj)
  have hbase : ContMDiffAt (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) (IB.prod 𝓘(𝕜, F)) n
      (fun q ↦ (ofFirstJetBundle IB F V q).proj) q₀ :=
    (ManifoldTotalSpace.contMDiff_homeomorph n F V IB _).comp q₀
      (contMDiffAt_value_totalSpace n q₀)
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hbase, ?_⟩
  refine ((ContinuousLinearMap.snd 𝕜 F (EB →L[𝕜] F)).contDiff.contMDiff.contMDiffAt.comp
    q₀ hq_coord).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  obtain ⟨hq₁, hq₂⟩ := (FirstJetBundle.mem_baseSet_iff F V).1 hq
  let x₀ : TotalSpace F V := ⟨q.proj, FirstJetBundle.value IB F q.proj q.2⟩
  let i₀ : TotalSpace F V := ⟨q₀.proj, FirstJetBundle.value IB F q₀.proj q₀.2⟩
  have hx_chart : ManifoldTotalSpace.homeomorph F V x₀ ∈
      (chartAt (ModelProd HB F) (ManifoldTotalSpace.homeomorph F V i₀)).source := by
    rw [ManifoldTotalSpace.chartAt_homeomorph]
    simp only [Homeomorph.transOpenPartialHomeomorph_source, mem_preimage,
      Homeomorph.symm_apply_apply, OpenPartialHomeomorph.trans_source,
      Trivialization.coe_coe, OpenPartialHomeomorph.prod_source]
    refine ⟨(trivializationAt F V q₀.proj).mem_source.2 hq₁, ?_, mem_univ _⟩
    rwa [(trivializationAt F V q₀.proj).coe_fst' hq₁]
  have htriv := FirstJetBundle.trivializationAt_apply_snd (I := IB) (F := F) (V := V) q₀.proj q
  have h1 := (trivializationAt_apply_snd (IB := IB) (IF := 𝓘(𝕜, F))
    (ofFirstJetBundle IB F V q₀).proj (ofFirstJetBundle IB F V q)).trans
    (congrArg (coordChange IB 𝓘(𝕜, F) F V
        (ManifoldTotalSpace.homeomorph F V x₀)
        (ManifoldTotalSpace.homeomorph F V i₀)
        (ManifoldTotalSpace.homeomorph F V x₀))
      ((chartCoordEquiv IB 𝓘(𝕜, F) F V (ManifoldTotalSpace.homeomorph F V x₀)).apply_symm_apply
        (firstJetBundleSnd IB F V q.2)))
  have h2 := coordChange_eq_firstJetBundle_coordChange_snd (IB := IB) x₀ i₀ hx_chart
    (firstJetBundleSnd IB F V q.2)
  have h3 : (FirstJetBundle.coordChange IB F V x₀.proj i₀.proj x₀.proj
      ((trivializationAt F V x₀.proj x₀).2, firstJetBundleSnd IB F V q.2)).2 =
      (trivializationAt (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) q₀.proj q).2.2 := by
    have hr : ((trivializationAt F V x₀.proj x₀).2, firstJetBundleSnd IB F V q.2) =
        (q.2 : F × (EB →L[𝕜] F)) := mkFirstJetBundle_value_firstJetBundleSnd q.2
    exact (congrArg (fun z ↦ (FirstJetBundle.coordChange IB F V q.proj q₀.proj q.proj z).2)
      hr).trans (congrArg Prod.snd htriv).symm
  change (trivializationAt (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V)
      (ofFirstJetBundle IB F V q₀).proj (ofFirstJetBundle IB F V q)).2 =
    (trivializationAt (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) q₀.proj q).2.2
  exact h1.trans (h2.trans h3)

variable (IB F V) in
/-- **Canonical `C^n` diffeomorphism `J¹V ≃ₘ^n FirstJetBundle IB F V` (`P1.0` comparison).** In
preferred bundle charts, `toFirstJetBundle` simply reassociates `((u, v), A)` to `(u, (v, A))`, so
it is `C^n` for every `n : ℕ∞ω` as soon as `B` and `V` are `C^1`. -/
-- Expose so `(diffeomorphFirstJetBundle IB F V n p).proj` reduces definitionally in fibre types.
@[expose]
def diffeomorphFirstJetBundle (n : ℕ∞ω) :
    TotalSpace (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V)
      ≃ₘ^n⟮(IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F), IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))⟯
      TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) where
  toFun := toFirstJetBundle IB F V
  invFun := ofFirstJetBundle IB F V
  left_inv := ofFirstJetBundle_toFirstJetBundle
  right_inv := toFirstJetBundle_ofFirstJetBundle
  contMDiff_toFun := contMDiff_toFirstJetBundle n
  contMDiff_invFun := contMDiff_ofFirstJetBundle n

@[simp]
theorem coe_diffeomorphFirstJetBundle (n : ℕ∞ω) :
    ⇑(diffeomorphFirstJetBundle IB F V n) = toFirstJetBundle IB F V :=
  (rfl)

@[simp]
theorem coe_diffeomorphFirstJetBundle_symm (n : ℕ∞ω) :
    ⇑(diffeomorphFirstJetBundle IB F V n).symm = ofFirstJetBundle IB F V :=
  (rfl)

/-- `toFirstJetBundle` commutes with projection to `B`. -/
@[simp]
theorem proj_toFirstJetBundle
    (p : TotalSpace (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V)) :
    (toFirstJetBundle IB F V p).proj =
      ((ManifoldTotalSpace.homeomorph F V).symm p.proj).proj :=
  (rfl)

/-- `diffeomorphFirstJetBundle` commutes with projection to `B`. -/
theorem proj_diffeomorphFirstJetBundle (n : ℕ∞ω)
    (p : TotalSpace (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V)) :
    (diffeomorphFirstJetBundle IB F V n p).proj =
      ((ManifoldTotalSpace.homeomorph F V).symm p.proj).proj :=
  (rfl)

/-- `FirstJetBundle.value` after `diffeomorphFirstJetBundle` recovers the underlying vector in
`V (π x)`. -/
theorem value_diffeomorphFirstJetBundle (n : ℕ∞ω)
    (p : TotalSpace (EB →L[𝕜] F) (FirstJet IB 𝓘(𝕜, F) F V)) :
    FirstJetBundle.value IB F _ (diffeomorphFirstJetBundle IB F V n p).2 =
      ((ManifoldTotalSpace.homeomorph F V).symm p.proj).2 := by
  let x₀ := (ManifoldTotalSpace.homeomorph F V).symm p.proj
  change FirstJetBundle.value IB F x₀.proj (toFirstJetBundle IB F V p).2 = x₀.2
  dsimp only [toFirstJetBundle]
  rw [value_mkFirstJetBundle]
  exact (trivializationAt F V x₀.proj).symm_apply_apply_mk
    (mem_baseSet_trivializationAt F V x₀.proj) x₀.2

/-- **Compatibility of `diffeomorphFirstJetBundle` with holonomic prolongation.** -/
theorem diffeomorphFirstJetBundle_jet (n : ℕ∞ω) (s : ∀ b, V b) {b : B}
    (hs : MDifferentiableAt IB (IB.prod 𝓘(𝕜, F))
      (fun y ↦ ManifoldTotalSpace.homeomorph F V ⟨y, s y⟩) b) :
    diffeomorphFirstJetBundle IB F V n
        ⟨ManifoldTotalSpace.homeomorph F V ⟨b, s b⟩, jet IB 𝓘(𝕜, F) F s b⟩ =
      ⟨b, FirstJetBundle.jet IB F s b⟩ := by
  let sTot : B → ManifoldTotalSpace F V := fun y ↦ ManifoldTotalSpace.homeomorph F V ⟨y, s y⟩
  let mkJet : TotalSpace F V → (EB →L[𝕜] F) →
      TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) := fun y A ↦
    ⟨y.proj, mkFirstJetBundle IB F V y.proj (trivializationAt F V y.proj y).2 A⟩
  change mkJet ((ManifoldTotalSpace.homeomorph F V).symm (sTot b))
      (chartCoordEquiv IB 𝓘(𝕜, F) F V (sTot b) (jetAt IB 𝓘(𝕜, F) sTot b)) =
    ⟨b, FirstJetBundle.jet IB F s b⟩
  rw [chartCoordEquiv_jetAt]
  dsimp only [sTot]
  rw [Homeomorph.symm_apply_apply]
  dsimp only [mkJet]
  refine congrArg (TotalSpace.mk' (F × (EB →L[𝕜] F)) b)
    (Prod.ext (FirstJetBundle.jet_fst IB F s b).symm ?_)
  rw [FirstJetBundle.jet_snd]
  have hrep : (Prod.snd ∘ writtenInExtChartAt IB (IB.prod 𝓘(𝕜, F)) b
      (fun y ↦ ManifoldTotalSpace.homeomorph F V ⟨y, s y⟩))
      =ᶠ[𝓝[range IB] extChartAt IB b b] FirstJetBundle.localRep IB F s b := by
    filter_upwards [FirstJetBundle.eventually_extChartAt_symm_mem_baseSet IB
      (FirstJetBundle.mem_baseSet_self F V b)
      (FirstJetBundle.mem_baseSet_self F V b)] with z _
    rw [Function.comp_apply, writtenInExtChartAt, Function.comp_apply, Function.comp_apply,
      ManifoldTotalSpace.extChartAt_homeomorph_apply]
    dsimp only
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq, FirstJetBundle.localRep_apply]
  have hpt : (Prod.snd ∘ writtenInExtChartAt IB (IB.prod 𝓘(𝕜, F)) b
      (fun y ↦ ManifoldTotalSpace.homeomorph F V ⟨y, s y⟩)) (extChartAt IB b b) =
      FirstJetBundle.localRep IB F s b (extChartAt IB b b) := by
    rw [Function.comp_apply, writtenInExtChartAt, Function.comp_apply, Function.comp_apply,
      (extChartAt IB b).left_inv (mem_extChartAt_source b),
      ManifoldTotalSpace.extChartAt_homeomorph_apply]
    dsimp only
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq,
      FirstJetBundle.localRep_extChartAt IB F s (mem_chart_source HB b)]
  have hD := ((hasFDerivAt_snd.comp_hasFDerivWithinAt _ hs.hasMFDerivAt.2).congr_of_eventuallyEq
    hrep.symm hpt.symm).fderivWithin
    (IB.uniqueDiffOn _ (extChartAt_target_subset_range b
      ((extChartAt IB b).map_source (mem_extChartAt_source b))))
  exact hD.symm

/-- **Compatibility of `diffeomorphFirstJetBundle` with the affine `Hom(T_b B, V_b)` torsor
action.** Translating `j` by `L : T_{π x} B →L[𝕜] V_x V` corresponds to adding
`FirstJetBundle.ofDeriv` applied to `(VerticalBundle.equivFiber x) ∘ L`. -/
theorem diffeomorphFirstJetBundle_vadd [∀ b, IsTopologicalAddGroup (V b)]
    [∀ b, ContinuousSMul 𝕜 (V b)] (n : ℕ∞ω) {x : ManifoldTotalSpace F V}
    (L : TangentSpace IB ((ManifoldTotalSpace.homeomorph F V).symm x).proj →L[𝕜]
      VerticalBundle IB 𝓘(𝕜, F) F V x)
    (j : FirstJet IB 𝓘(𝕜, F) F V x) :
    let b := ((ManifoldTotalSpace.homeomorph F V).symm x).proj
    let qj : FirstJetBundle IB F V b := (diffeomorphFirstJetBundle IB F V n ⟨x, j⟩).2
    diffeomorphFirstJetBundle IB F V n ⟨x, L +ᵥ j⟩ =
      ⟨b, FirstJetBundle.ofDeriv IB F b
        ((VerticalBundle.equivFiber x).toContinuousLinearMap.comp L) + qj⟩ := by
  intro b qj
  refine congrArg (TotalSpace.mk' (F × (EB →L[𝕜] F)) b) ?_
  change mkFirstJetBundle IB F V b
      (trivializationAt F V b ((ManifoldTotalSpace.homeomorph F V).symm x)).2
      (chartCoordEquiv IB 𝓘(𝕜, F) F V x (L +ᵥ j)) =
    FirstJetBundle.ofDeriv IB F b
      ((VerticalBundle.equivFiber x).toContinuousLinearMap.comp L) + qj
  rw [FirstJetBundle.ofDeriv_apply]
  refine Prod.ext (zero_add _).symm ?_
  ext u
  let u' : TangentSpace IB b := u
  change chartCoordEquiv IB 𝓘(𝕜, F) F V x (L +ᵥ j) u =
    (((trivializationAt F V b).continuousLinearMapAt 𝕜 b).comp
      ((VerticalBundle.equivFiber x).toContinuousLinearMap.comp L)) u' +
      chartCoordEquiv IB 𝓘(𝕜, F) F V x j u
  rw [chartCoordEquiv_vadd_apply L j u, comp_apply, comp_apply,
    ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _
      (mem_baseSet_trivializationAt F V b), VerticalBundle.equivFiber_apply]
  congr 1
  exact (congrArg Prod.snd ((trivializationAt F V b).apply_mk_symm
    (mem_baseSet_trivializationAt F V b) (show F from L u'))).symm

/-- **Compatibility with linear covariant derivatives (`FirstJetBundle.covariantDerivative`).**
A covariant derivative `cov` on a finite-rank `C^1` vector bundle `V` induces a horizontal lift
section `x ↦ (diffeomorphFirstJetBundle)⁻¹ ⟨π x, horizontalLift x (val x)⟩` of `FirstJet`, and the
resulting torsor difference `j -ᵥ Γ x` matches `FirstJetBundle.covariantDerivative hcov` under
`VerticalBundle.equivFiber`. -/
theorem covariantDerivative_diffeomorphFirstJetBundle [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul 𝕜 (V b)]
    {cov : (∀ b : B, V b) → (∀ b : B, TangentSpace IB b →L[𝕜] V b)} {U : Set B}
    (hcov : IsCovariantDerivativeOn F cov U) {x : ManifoldTotalSpace F V}
    (j : FirstJet IB 𝓘(𝕜, F) F V x) :
    let x₀ := (ManifoldTotalSpace.homeomorph F V).symm x
    let Γx : FirstJet IB 𝓘(𝕜, F) F V x :=
      (chartCoordEquiv IB 𝓘(𝕜, F) F V x).symm
        (FirstJetBundle.horizontalLift hcov x₀.proj x₀.2).2
    (VerticalBundle.equivFiber x).toContinuousLinearMap.comp (j -ᵥ Γx) =
      FirstJetBundle.covariantDerivative hcov x₀.proj
        (diffeomorphFirstJetBundle IB F V 1 ⟨x, j⟩).2 := by
  intro x₀ Γx
  let qj : FirstJetBundle IB F V x₀.proj := (diffeomorphFirstJetBundle IB F V 1 ⟨x, j⟩).2
  have hval : FirstJetBundle.value IB F x₀.proj qj = x₀.2 :=
    value_diffeomorphFirstJetBundle 1 ⟨x, j⟩
  have hdecomp : qj =
      FirstJetBundle.horizontalLift hcov x₀.proj x₀.2 +
        FirstJetBundle.ofDeriv IB F x₀.proj
          (FirstJetBundle.covariantDerivative hcov x₀.proj qj) := by
    simpa only [hval] using
      (FirstJetBundle.horizontalLift_value_add_ofDeriv_covariantDerivative hcov qj).symm
  ext u
  let u₀ : EB := u
  have hsnd : chartCoordEquiv IB 𝓘(𝕜, F) F V x j u₀ =
      (FirstJetBundle.horizontalLift hcov x₀.proj x₀.2).2 u₀ +
        ((trivializationAt F V x₀.proj).continuousLinearMapAt 𝕜 x₀.proj)
          (FirstJetBundle.covariantDerivative hcov x₀.proj qj u) := by
    have h2 : qj.2 = (FirstJetBundle.horizontalLift hcov x₀.proj x₀.2 +
        FirstJetBundle.ofDeriv IB F x₀.proj
          (FirstJetBundle.covariantDerivative hcov x₀.proj qj)).2 := congrArg Prod.snd hdecomp
    have hu := DFunLike.congr_fun h2 u₀
    rw [FirstJetBundle.ofDeriv_apply] at hu
    exact hu
  have hvsub := vsub_apply_chart j Γx u₀
  rw [Equiv.apply_symm_apply, hsnd, add_sub_cancel_left] at hvsub
  rw [comp_apply, ContinuousLinearEquiv.coe_coe, VerticalBundle.equivFiber_apply]
  change (trivializationAt F V x₀.proj).symm x₀.proj (show F from (j -ᵥ Γx) u₀) = _
  rw [hvsub, Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _
      (mem_baseSet_trivializationAt F V x₀.proj),
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F V x₀.proj)]

end FirstJet

end VectorBundle

end TauCeti
