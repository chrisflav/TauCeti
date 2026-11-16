/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import TauCeti.MeasureTheory.Measure.Haar.Quotient.Basic
public import TauCeti.Topology.Algebra.Group.Subgroup

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import TauCeti.MeasureTheory.Group.ModularCharacter
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Disintegration, Lebesgue and Bochner Extensions, and Composition in Stages

This file constructs the fibre kernel `quotientFibreKernel` disintegrating a right Haar measure
`μG` over Weil's quotient measure `quotientMeasure`, extends Weil's quotient integral formula from
`C_c(G, ℝ)` to nonnegative Borel functions (`ℝ≥0∞`-valued) and Bochner-integrable functions into
any real normed space, and proves composition in stages for nested closed subgroups
`H₁ ≤ H₂ ≤ G`.

## Main definitions

* `TauCeti.quotientFibreKernel`: the measurable kernel `H \ G ↝ G` sending a coset `H g` to the
  pushforward of `μH` along `h ↦ h * g`.
* `TauCeti.quotientStageMap`: the closed embedding `(H₁.subgroupOf H₂) \ H₂ → H₁ \ G` into a
  fibre over a coset `q₂ ∈ H₂ \ G`.
* `TauCeti.quotientStageKernel`: the measurable kernel `H₂ \ G ↝ H₁ \ G` pushing forward the
  intermediate quotient measure on `(H₁.subgroupOf H₂) \ H₂`.

## Main results

* `TauCeti.quotientFibreKernel_comp_quotientMeasure`: disintegration identity `κ ∘ₘ ν = μG`.
* `TauCeti.lintegral_quotientMeasure`: Lebesgue integral extension for `AEMeasurable` functions
  `G → ℝ≥0∞`.
* `TauCeti.integrable_iff_quotientMeasure`, `TauCeti.integral_quotientMeasure`: integrability
  criterion and Bochner integral extension for functions into any real normed space `E`.
* `TauCeti.modularCharacter_subgroupOf_eq`: matching modular characters descend to nested
  subgroups `H₁.subgroupOf H₂ ≤ H₂`.
* `TauCeti.quotientStageKernel_comp_quotientMeasure`,
  `TauCeti.lintegral_quotientMeasure_stages`, `TauCeti.integral_quotientMeasure_stages`:
  composition of quotient measures in stages for nested closed subgroups `H₁ ≤ H₂ ≤ G`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, §2.6.
-/

public section

open scoped CompactlySupported ENNReal NNReal ProbabilityTheory Topology
open MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti

section GenericHelpers

/-- If `κ : Q → Measure Z` pulls back along a quotient map `π : X → Q` to pushforwards of a
regular measure `ν` along a jointly continuous family `F : X × Y → Z`, and each `κ q` is finite
on compact sets, then `κ` is Borel measurable. -/
private theorem measurable_kernel_of_isQuotientMap {X Q Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Q] [MeasurableSpace Q] [OpensMeasurableSpace Q]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z]
    {π : X → Q} (hπ : IsQuotientMap π) (ν : Measure Y) [ν.Regular]
    {F : X × Y → Z} (hF : Continuous F)
    {κ : Q → Measure Z}
    (hκ : ∀ x : X, κ (π x) = ν.map (fun y => F (x, y)))
    (hfin : ∀ q : Q, IsFiniteMeasureOnCompacts (κ q)) :
    Measurable κ := by
  have : SigmaCompactSpace Z := sigmaCompactSpace_of_locallyCompact_secondCountable
  let K := CompactExhaustion.choice Z
  refine Measurable.measure_of_isPiSystem_of_iUnion (B := fun n => interior (K n))
    BorelSpace.measurable_eq isPiSystem_isOpen (fun _ => isOpen_interior) ?_ ?_ fun U hU => ?_
  · ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := K.exists_mem_nhds z
    exact ⟨n, mem_interior_iff_mem_nhds.mpr hn⟩
  · intro q n
    have := hfin q
    exact ((measure_mono interior_subset).trans_lt (K.isCompact n).measure_lt_top).ne
  · -- `q ↦ κ q U` is lower semicontinuous because its pullback `x ↦ ν (F (x, ·) ⁻¹' U)` is.
    refine LowerSemicontinuous.measurable ?_
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro r
    rw [← hπ.isOpen_preimage]
    have hls : LowerSemicontinuous fun x : X => κ (π x) U := by
      intro x₀ c hc
      dsimp only at hc ⊢
      have hFx (x : X) : Continuous (fun y : Y => F (x, y)) :=
        hF.comp (continuous_const.prodMk continuous_id)
      have hmap (x : X) : κ (π x) U = ν ((fun y => F (x, y)) ⁻¹' U) := by
        rw [hκ x, Measure.map_apply (hFx x).measurable hU.measurableSet]
      rw [hmap x₀] at hc
      have hopen : IsOpen ((fun y => F (x₀, y)) ⁻¹' U) := hU.preimage (hFx x₀)
      obtain ⟨C, hCsub, hCc, hCr⟩ := hopen.exists_lt_isCompact hc
      have htube : {x₀} ×ˢ C ⊆ F ⁻¹' U := by
        rintro ⟨x, y⟩ ⟨rfl, hyC⟩
        exact hCsub hyC
      obtain ⟨W, V, hWo, -, hx₀W, hCV, hWV⟩ :=
        generalized_tube_lemma isCompact_singleton hCc (hU.preimage hF) htube
      filter_upwards [hWo.mem_nhds (hx₀W rfl)] with x hxW
      rw [hmap x]
      exact hCr.trans_le (measure_mono fun y hyC => hWV ⟨hxW, hCV hyC⟩)
    exact lowerSemicontinuous_iff_isOpen_preimage.mp hls r

/-- Two Borel measures on a second countable locally compact Hausdorff space coincide if `μ₂` is
finite on compacts and `∫⁻ x, ENNReal.ofReal (F x) ∂μ₁ = ENNReal.ofReal (∫ x, F x ∂μ₂)` for
every nonnegative `F : C_c(X, ℝ)`. -/
private theorem measure_eq_of_lintegral_ofReal_eq {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    {μ₁ μ₂ : Measure X} [IsFiniteMeasureOnCompacts μ₂]
    (hlint : ∀ F : C_c(X, ℝ), 0 ≤ F →
      ∫⁻ x, ENNReal.ofReal (F x) ∂μ₁ = ENNReal.ofReal (∫ x, F x ∂μ₂)) :
    μ₁ = μ₂ := by
  have hfin₁ : IsFiniteMeasureOnCompacts μ₁ := by
    refine ⟨fun K hK => ?_⟩
    obtain ⟨η₀, hη1, hηc, -, hη01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
    let η : C_c(X, ℝ) := ⟨η₀, hasCompactSupport_def.mpr hηc⟩
    have hle : μ₁ K ≤ ∫⁻ x, ENNReal.ofReal (η x) ∂μ₁ := by
      calc μ₁ K
          = ∫⁻ x, K.indicator 1 x ∂μ₁ :=
              (lintegral_indicator_one hK.isClosed.measurableSet).symm
        _ ≤ ∫⁻ x, ENNReal.ofReal (η x) ∂μ₁ := by
              refine lintegral_mono fun x => ?_
              by_cases hx : x ∈ K
              · rw [Set.indicator_of_mem hx, Pi.one_apply]
                have h1 : η x = 1 := hη1 hx
                rw [h1, ENNReal.ofReal_one]
              · rw [Set.indicator_of_notMem hx]
                exact bot_le
    exact hle.trans_lt (by rw [hlint η fun x => (hη01 x).1]; exact ENNReal.ofReal_lt_top)
  have : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : μ₁.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ₁
  have : μ₂.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ₂
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f => ?_
  let fℝ : C_c(X, ℝ) :=
    ⟨⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩,
      f.hasCompactSupport.comp_left NNReal.coe_zero⟩
  have hf_nn (x : X) : 0 ≤ fℝ x := NNReal.coe_nonneg (f x)
  have hnn : 0 ≤ ∫ x, fℝ x ∂μ₂ := integral_nonneg hf_nn
  have hlhs : ∫ x, (f x : ℝ) ∂μ₁ = ∫ x, fℝ x ∂μ₁ := rfl
  have hrhs : ∫ x, (f x : ℝ) ∂μ₂ = ∫ x, fℝ x ∂μ₂ := rfl
  rw [hlhs, hrhs, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf_nn)
      fℝ.continuous.measurable.aestronglyMeasurable,
    hlint fℝ hf_nn, ENNReal.toReal_ofReal hnn]

end GenericHelpers

section FibreKernel

private theorem isClosedEmbedding_mulRight_subtype {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (g : G) :
    Topology.IsClosedEmbedding (fun h : H => (h : G) * g) :=
  (Homeomorph.mulRight g).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- **The fibre kernel** `H \ G ↝ G` sending a right coset `q = H g` to the pushforward of `μH`
along `h ↦ h * q.out`. Because `μH` is right-invariant, this measure is independent of the chosen
coset representative `q.out`. -/
noncomputable def quotientFibreKernel (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] :
    Kernel (MulAction.orbitRel.Quotient H G) G where
  toFun q := μH.map (fun h : H => (h : G) * q.out)
  measurable' := by
    have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
    have : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
    have : μH.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μH
    refine measurable_kernel_of_isQuotientMap
      (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).isQuotientMap μH
      (F := fun p : G × H => (p.2 : G) * p.1)
      ((continuous_subtype_val.comp continuous_snd).mul continuous_fst) (fun g => ?_) (fun q => ?_)
    · let h₀ : H := ⟨_, orbitRelQuotient_out_mul_inv_mem H g⟩
      have hrep : (Quotient.mk (MulAction.orbitRel H G) g).out = (h₀ : G) * g := by simp [h₀]
      have hcomp : (fun h : H => (h : G) * ((h₀ : G) * g)) =
          (fun h : H => (h : G) * g) ∘ (· * h₀) := by
        ext h
        simp [mul_assoc]
      rw [hrep, hcomp, ← Measure.map_map (by fun_prop : Measurable fun h : H => (h : G) * g)
        (continuous_mul_const h₀).measurable, map_mul_right_eq_self]
    · refine ⟨fun K hK => ?_⟩
      have hemb := isClosedEmbedding_mulRight_subtype H hH q.out
      rw [hemb.measurableEmbedding.map_apply]
      exact (hemb.isCompact_preimage hK).measure_lt_top

theorem quotientFibreKernel_apply (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    (q : MulAction.orbitRel.Quotient H G) :
    quotientFibreKernel H hH μH q = μH.map (fun h : H => (h : G) * q.out) :=
  (rfl)

@[simp]
theorem quotientFibreKernel_mk (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] (g : G) :
    quotientFibreKernel H hH μH (Quotient.mk'' g) = μH.map (fun h : H => (h : G) * g) := by
  rw [quotientFibreKernel_apply]
  let h₀ : H := ⟨_, orbitRelQuotient_out_mul_inv_mem H g⟩
  have hrep : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = (h₀ : G) * g := by
    simp [h₀]
  rw [hrep]
  have hcomp : (fun h : H => (h : G) * ((h₀ : G) * g)) =
      (fun h : H => (h : G) * g) ∘ (· * h₀) := by
    ext h
    simp [mul_assoc]
  rw [hcomp, ← Measure.map_map (by fun_prop : Measurable fun h : H => (h : G) * g)
    (continuous_mul_const h₀).measurable, map_mul_right_eq_self]

/-- For any measurable `f : G → ℝ≥0∞`, the fibre Lebesgue integral
`q ↦ ∫⁻ h : H, f ((h : G) * q.out) ∂μH` is measurable on `H \ G`. -/
theorem measurable_lintegral_quotientFibre (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun q : MulAction.orbitRel.Quotient H G =>
      ∫⁻ h : H, f ((h : G) * q.out) ∂μH := by
  have heq : (fun q : MulAction.orbitRel.Quotient H G => ∫⁻ h : H, f ((h : G) * q.out) ∂μH) =
      fun q => ∫⁻ x, f x ∂quotientFibreKernel H hH μH q := by
    ext q
    exact ((isClosedEmbedding_mulRight_subtype H hH q.out).measurableEmbedding.lintegral_map
      (μ := μH) f).symm
  rw [heq]
  exact hf.lintegral_kernel

variable (H : Subgroup G) (hH : IsClosed (H : Set G))
  [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
  [BorelSpace (MulAction.orbitRel.Quotient H G)]
  (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
  [μG.IsOpenPosMeasure]
  (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
  [μH.IsOpenPosMeasure]
  (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
    Measure.modularCharacter (G := H) h)

/-- **Disintegration of right Haar measure over Weil's quotient measure:**
`quotientFibreKernel H hH μH ∘ₘ quotientMeasure H hH μG μH hmod = μG`. -/
theorem quotientFibreKernel_comp_quotientMeasure :
    quotientFibreKernel H hH μH ∘ₘ quotientMeasure H hH μG μH hmod = μG := by
  let κ := quotientFibreKernel H hH μH
  let ν := quotientMeasure H hH μG μH hmod
  have hν_fin : IsFiniteMeasureOnCompacts ν :=
    isFiniteMeasureOnCompacts_quotientMeasure H hH μG μH hmod
  refine measure_eq_of_lintegral_ofReal_eq fun f hf0 => ?_
  have hf_meas : AEMeasurable (fun x : G => ENNReal.ofReal (f x)) (κ ∘ₘ ν) :=
    (ENNReal.continuous_ofReal.comp f.continuous).measurable.aemeasurable
  rw [Measure.lintegral_bind κ.aemeasurable hf_meas]
  have hinner (q : MulAction.orbitRel.Quotient H G) :
      ∫⁻ x, ENNReal.ofReal (f x) ∂κ q =
        ENNReal.ofReal (quotientFibreAverage H hH μH f q) := by
    have hemb := isClosedEmbedding_mulRight_subtype H hH q.out
    rw [quotientFibreKernel_apply, hemb.measurableEmbedding.lintegral_map]
    have hint : Integrable (fun h : H => f ((h : G) * q.out)) μH :=
      (f.continuous.comp (continuous_subtype_val.mul continuous_const))
        |>.integrable_of_hasCompactSupport (f.hasCompactSupport.comp_isClosedEmbedding hemb)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun h => hf0 _),
      quotientFibreAverage_apply]
  simp_rw [hinner]
  have havg_nn (q : MulAction.orbitRel.Quotient H G) :
      0 ≤ quotientFibreAverage H hH μH f q := by
    rw [quotientFibreAverage_apply]
    exact integral_nonneg fun h => hf0 _
  rw [← ofReal_integral_eq_lintegral_ofReal (quotientFibreAverage H hH μH f).integrable
      (ae_of_all _ havg_nn),
    integral_quotientFibreAverage_quotientMeasure H hH μG μH hmod f]

/-- **Lebesgue integral extension of Weil's quotient formula** to nonnegative `AEMeasurable`
functions `f : G → ℝ≥0∞`. -/
theorem lintegral_quotientMeasure {f : G → ℝ≥0∞} (hf : AEMeasurable f μG) :
    ∫⁻ g, f g ∂μG =
      ∫⁻ q, (∫⁻ h : H, f ((h : G) * q.out) ∂μH) ∂quotientMeasure H hH μG μH hmod := by
  have hcomp := quotientFibreKernel_comp_quotientMeasure H hH μG μH hmod
  conv_lhs => rw [← hcomp]
  rw [Measure.lintegral_bind (quotientFibreKernel H hH μH).aemeasurable (hcomp.symm ▸ hf)]
  congr 1 with q
  exact (isClosedEmbedding_mulRight_subtype H hH q.out).measurableEmbedding.lintegral_map
    (μ := μH) f

section BochnerExtension

variable {E : Type*} [NormedAddCommGroup E]

/-- **Integrability criterion for Weil's quotient formula:** an `AEStronglyMeasurable` function
`f : G → E` is `μG`-integrable if and only if its restriction to `μH`-almost every fibre is
`μH`-integrable and the fibre `L¹`-norm `q ↦ ∫ h, ‖f (h * q.out)‖ ∂μH` is integrable against the
quotient measure. -/
theorem integrable_iff_quotientMeasure {f : G → E} (hf : AEStronglyMeasurable f μG) :
    Integrable f μG ↔
      (∀ᵐ q ∂quotientMeasure H hH μG μH hmod,
          Integrable (fun h : H => f ((h : G) * q.out)) μH) ∧
        Integrable (fun q => ∫ h : H, ‖f ((h : G) * q.out)‖ ∂μH)
          (quotientMeasure H hH μG μH hmod) := by
  have hcomp := quotientFibreKernel_comp_quotientMeasure H hH μG μH hmod
  conv_lhs => rw [← hcomp]
  rw [Measure.integrable_comp_iff (hcomp.symm ▸ hf)]
  refine and_congr ?_ ?_
  · refine Filter.eventually_congr (ae_of_all _ fun q => ?_)
    exact (isClosedEmbedding_mulRight_subtype H hH q.out).measurableEmbedding.integrable_map_iff
  · have heq : (fun q : MulAction.orbitRel.Quotient H G =>
        ∫ y, ‖f y‖ ∂quotientFibreKernel H hH μH q) =
        fun q => ∫ h : H, ‖f ((h : G) * q.out)‖ ∂μH := by
      ext q
      exact (isClosedEmbedding_mulRight_subtype H hH q.out).measurableEmbedding.integral_map
        (fun y => ‖f y‖)
    rw [heq]

/-- If `f : G → E` is `μG`-integrable, then its restriction to almost every right coset is
`μH`-integrable. -/
theorem ae_integrable_quotientFibre {f : G → E} (hf : Integrable f μG) :
    ∀ᵐ q ∂quotientMeasure H hH μG μH hmod, Integrable (fun h : H => f ((h : G) * q.out)) μH :=
  ((integrable_iff_quotientMeasure H hH μG μH hmod hf.1).mp hf).1

variable [NormedSpace ℝ E]

/-- If `f : G → E` is `μG`-integrable, then its fibre integral
`q ↦ ∫ h : H, f ((h : G) * q.out) ∂μH` is integrable against Weil's quotient measure. -/
theorem integrable_integral_quotientFibre {f : G → E} (hf : Integrable f μG) :
    Integrable (fun q => ∫ h : H, f ((h : G) * q.out) ∂μH)
      (quotientMeasure H hH μG μH hmod) := by
  have hcomp := quotientFibreKernel_comp_quotientMeasure H hH μG μH hmod
  have hf' : Integrable f ((quotientFibreKernel H hH μH ∘ₖ
      Kernel.const Unit (quotientMeasure H hH μG μH hmod)) ()) := by
    simpa [Measure.comp_eq_comp_const_apply, hcomp] using hf
  have hint := hf'.integral_comp
  simp only [Kernel.const_apply] at hint
  have heq : (fun q : MulAction.orbitRel.Quotient H G =>
      ∫ y, f y ∂quotientFibreKernel H hH μH q) =
      fun q => ∫ h : H, f ((h : G) * q.out) ∂μH := by
    ext q
    exact (isClosedEmbedding_mulRight_subtype H hH q.out).measurableEmbedding.integral_map f
  rwa [heq] at hint

/-- **Bochner integral extension of Weil's quotient formula** to integrable functions `f : G → E`
valued in any real normed space `E`. -/
theorem integral_quotientMeasure {f : G → E} (hf : Integrable f μG) :
    ∫ g, f g ∂μG =
      ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂quotientMeasure H hH μG μH hmod := by
  have hcomp := quotientFibreKernel_comp_quotientMeasure H hH μG μH hmod
  have hf' : Integrable f ((quotientFibreKernel H hH μH ∘ₖ
      Kernel.const Unit (quotientMeasure H hH μG μH hmod)) ()) := by
    simpa [Measure.comp_eq_comp_const_apply, hcomp] using hf
  have hint := Kernel.integral_comp hf'
  simp only [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply, hcomp] at hint
  rw [hint]
  congr 1 with q
  exact (isClosedEmbedding_mulRight_subtype H hH q.out).measurableEmbedding.integral_map f

end BochnerExtension

end FibreKernel

section CompositionInStages

/-- If the modular characters of `G` and `H₁`, and of `G` and `H₂`, agree on nested subgroups
`H₁ ≤ H₂`, then the modular characters of `H₂` and `H₁.subgroupOf H₂` agree on
`H₁.subgroupOf H₂`. -/
theorem modularCharacter_subgroupOf_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    {H₁ H₂ : Subgroup G} (h₁₂ : H₁ ≤ H₂)
    [LocallyCompactSpace H₁] [LocallyCompactSpace H₂] [LocallyCompactSpace (H₁.subgroupOf H₂)]
    (hmod₁ : ∀ h : H₁, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₁) h)
    (hmod₂ : ∀ h : H₂, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₂) h)
    (k : H₁.subgroupOf H₂) :
    Measure.modularCharacter (G := H₂) (k : H₂) =
      Measure.modularCharacter (G := H₁.subgroupOf H₂) k := by
  let e₁₂ := Subgroup.subgroupOfContinuousMulEquivOfLe h₁₂
  calc Measure.modularCharacter (G := H₂) (k : H₂)
      = Measure.modularCharacter (G := G) ((k : H₂) : G) := (hmod₂ k).symm
    _ = Measure.modularCharacter (G := G) ((e₁₂ k : H₁) : G) := rfl
    _ = Measure.modularCharacter (G := H₁) (e₁₂ k) := hmod₁ (e₁₂ k)
    _ = Measure.modularCharacter (G := H₁.subgroupOf H₂) k :=
          modularCharacter_continuousMulEquiv e₁₂ k

/-- The fibre inclusion `(H₁.subgroupOf H₂) \ H₂ → H₁ \ G` sending `K h₂ ↦ H₁ (h₂ * g)`. -/
def quotientStageMap {G : Type*} [Group G] {H₁ H₂ : Subgroup G} (_ : H₁ ≤ H₂) (g : G) :
    MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂ → MulAction.orbitRel.Quotient H₁ G :=
  Quotient.lift
    (fun h₂ : H₂ => (Quotient.mk'' ((h₂ : G) * g) : MulAction.orbitRel.Quotient H₁ G))
    fun h₂ h₂' ⟨k, hk⟩ => by
      have hmul : (h₂ : G) = ((⟨(k : H₂), k.2⟩ : H₁) : G) * (h₂' : G) := by
        simpa [Subgroup.smul_def] using congrArg (fun x : H₂ => (x : G)) hk.symm
      rw [hmul, mul_assoc, orbitRelQuotient_mk_mul_left]

@[simp]
theorem quotientStageMap_mk {G : Type*} [Group G] {H₁ H₂ : Subgroup G} (h₁₂ : H₁ ≤ H₂)
    (g : G) (h₂ : H₂) :
    quotientStageMap h₁₂ g (Quotient.mk'' h₂) = Quotient.mk'' ((h₂ : G) * g) :=
  (rfl)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The fibre map `(H₁.subgroupOf H₂) \ H₂ → H₁ \ G` is a closed embedding whenever `H₂` is
closed in `G`. -/
theorem isClosedEmbedding_quotientStageMap {H₁ H₂ : Subgroup G} (hH₂ : IsClosed (H₂ : Set G))
    (h₁₂ : H₁ ≤ H₂) (g : G) :
    Topology.IsClosedEmbedding (quotientStageMap h₁₂ g) := by
  have hπK := MulAction.isOpenQuotientMap_quotientMk (Γ := H₁.subgroupOf H₂) (T := H₂)
  have hπ₁ := MulAction.isOpenQuotientMap_quotientMk (Γ := H₁) (T := G)
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap ?_ ?_ ?_
  · rw [hπK.isQuotientMap.continuous_iff]
    exact continuous_quotient_mk'.comp (continuous_subtype_val.mul continuous_const)
  · intro q₁ q₂ hq
    induction q₁ using Quotient.inductionOn' with | h x =>
    induction q₂ using Quotient.inductionOn' with | h y =>
    have hmem : ((x : G) * g) * ((y : G) * g)⁻¹ ∈ H₁ :=
      (orbitRelQuotient_eq_iff H₁).mp hq
    have hxy : (x : G) * (y : G)⁻¹ ∈ H₁ := by simpa [mul_assoc] using hmem
    have hxy' : x * y⁻¹ ∈ H₁.subgroupOf H₂ := hxy
    exact (orbitRelQuotient_eq_iff (H₁.subgroupOf H₂)).mpr hxy'
  · intro C hC
    rw [← hπ₁.isQuotientMap.isClosed_preimage]
    have hC' : IsClosed ((Quotient.mk (MulAction.orbitRel (H₁.subgroupOf H₂) H₂)) ⁻¹' C) :=
      hC.preimage continuous_quotient_mk'
    have hemb : Topology.IsClosedEmbedding (fun h₂ : H₂ => (h₂ : G) * g) :=
      (Homeomorph.mulRight g).isClosedEmbedding.comp hH₂.isClosedEmbedding_subtypeVal
    have himg : IsClosed ((fun h₂ : H₂ => (h₂ : G) * g) ''
        ((Quotient.mk (MulAction.orbitRel (H₁.subgroupOf H₂) H₂)) ⁻¹' C)) :=
      hemb.isClosedMap _ hC'
    have hpre : (Quotient.mk (MulAction.orbitRel H₁ G)) ⁻¹' (quotientStageMap h₁₂ g '' C) =
        (fun h₂ : H₂ => (h₂ : G) * g) ''
          ((Quotient.mk (MulAction.orbitRel (H₁.subgroupOf H₂) H₂)) ⁻¹' C) := by
      ext x
      constructor
      · rintro ⟨q, hqC, hqx⟩
        induction q using Quotient.inductionOn' with | h h₂ =>
        have hmem : ((h₂ : G) * g) * x⁻¹ ∈ H₁ :=
          (orbitRelQuotient_eq_iff H₁).mp hqx
        have hmem_inv : x * ((h₂ : G) * g)⁻¹ ∈ H₁ := by
          simpa [mul_assoc] using H₁.inv_mem hmem
        let k : H₁.subgroupOf H₂ := ⟨⟨_, h₁₂ hmem_inv⟩, hmem_inv⟩
        let h₂' : H₂ := (k : H₂) * h₂
        refine ⟨h₂', ?_, by simp [h₂', k, mul_assoc]⟩
        have heq_q : Quotient.mk (MulAction.orbitRel (H₁.subgroupOf H₂) H₂) h₂' =
            Quotient.mk'' h₂ :=
          orbitRelQuotient_mk_mul_left (H₁.subgroupOf H₂) k h₂
        rwa [Set.mem_preimage, heq_q]
      · rintro ⟨h₂, hh₂, rfl⟩
        exact ⟨Quotient.mk'' h₂, hh₂, rfl⟩
    rwa [hpre]

variable [LocallyCompactSpace G]

/-- Key identity connecting the stage fibre integral of `F ∈ C_c(H₁ \ G, ℝ)` to the `H₂`-fibre
average of any `C_c(G, ℝ)`-lift `f` of `F`. -/
private theorem integral_stageMap_eq_quotientFibreAverage {H₁ H₂ : Subgroup G}
    (hH₁ : IsClosed (H₁ : Set G)) (hH₂ : IsClosed (H₂ : Set G)) (h₁₂ : H₁ ≤ H₂)
    [MeasurableSpace H₁] [BorelSpace H₁]
    [LocallyCompactSpace H₂] [SecondCountableTopology H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [LocallyCompactSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (H₁.subgroupOf H₂)] [BorelSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    [BorelSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    (μH₁ : Measure H₁) [μH₁.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₁]
    (μH₂ : Measure H₂) [μH₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₂]
    [μH₂.IsOpenPosMeasure]
    (μK : Measure (H₁.subgroupOf H₂)) [μK.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μK]
    [μK.IsOpenPosMeasure]
    (hμK : μK.map (Subgroup.subgroupOfContinuousMulEquivOfLe h₁₂) = μH₁)
    (hmod₁₂ : ∀ k : H₁.subgroupOf H₂, Measure.modularCharacter (G := H₂) (k : H₂) =
      Measure.modularCharacter (G := H₁.subgroupOf H₂) k)
    (f : C_c(G, ℝ)) (g : G) :
    ∫ q₁₂, quotientFibreAverage H₁ hH₁ μH₁ f (quotientStageMap h₁₂ g q₁₂) ∂
        quotientMeasure (H₁.subgroupOf H₂) (@Subgroup.isClosed_subgroupOf _ _ _ H₁ H₂ hH₁)
          μH₂ μK hmod₁₂ =
      quotientFibreAverage H₂ hH₂ μH₂ f (Quotient.mk'' g) := by
  let e₁₂ := Subgroup.subgroupOfContinuousMulEquivOfLe h₁₂
  have he_emb : MeasurableEmbedding (e₁₂ : H₁.subgroupOf H₂ → H₁) :=
    e₁₂.toHomeomorph.measurableEmbedding
  have heq (q₁₂ : MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂) :
      quotientFibreAverage H₁ hH₁ μH₁ f (quotientStageMap h₁₂ g q₁₂) =
        ∫ k : H₁.subgroupOf H₂, f ((((k : H₂) * q₁₂.out : H₂) : G) * g) ∂μK := by
    have hq : quotientStageMap h₁₂ g q₁₂ = Quotient.mk'' ((q₁₂.out : G) * g) := by
      conv_lhs => rw [← Quotient.out_eq' q₁₂]
      rfl
    rw [hq, quotientFibreAverage_mk, ← hμK, he_emb.integral_map]
    congr 1 with k
    simp [e₁₂, mul_assoc]
  simp_rw [heq]
  have hf_cont : Continuous (fun h₂ : H₂ => f ((h₂ : G) * g)) :=
    f.continuous.comp (continuous_subtype_val.mul continuous_const)
  have hf_supp : HasCompactSupport (fun h₂ : H₂ => f ((h₂ : G) * g)) :=
    f.hasCompactSupport.comp_isClosedEmbedding (isClosedEmbedding_mulRight_subtype H₂ hH₂ g)
  rw [← integral_quotientMeasure_of_continuous_hasCompactSupport
    (H₁.subgroupOf H₂) (@Subgroup.isClosed_subgroupOf _ _ _ H₁ H₂ hH₁) μH₂ μK hmod₁₂
    hf_cont hf_supp, quotientFibreAverage_mk]

variable [SecondCountableTopology G]

/-- **The stage kernel** `H₂ \ G ↝ H₁ \ G` for nested closed subgroups `H₁ ≤ H₂ ≤ G`, pushing
forward the intermediate quotient measure on `(H₁.subgroupOf H₂) \ H₂` along
`quotientStageMap h₁₂ q₂.out`. -/
noncomputable def quotientStageKernel {H₁ H₂ : Subgroup G}
    (hH₁ : IsClosed (H₁ : Set G)) (hH₂ : IsClosed (H₂ : Set G)) (h₁₂ : H₁ ≤ H₂)
    [LocallyCompactSpace H₂] [SecondCountableTopology H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [LocallyCompactSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (H₁.subgroupOf H₂)] [BorelSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₁ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₁ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₂ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₂ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    [BorelSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    (μH₂ : Measure H₂) [μH₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₂]
    [μH₂.IsOpenPosMeasure]
    (μK : Measure (H₁.subgroupOf H₂)) [μK.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μK]
    [μK.IsOpenPosMeasure]
    (hmod₁₂ : ∀ k : H₁.subgroupOf H₂, Measure.modularCharacter (G := H₂) (k : H₂) =
      Measure.modularCharacter (G := H₁.subgroupOf H₂) k) :
    Kernel (MulAction.orbitRel.Quotient H₂ G) (MulAction.orbitRel.Quotient H₁ G) where
  toFun q₂ :=
    (quotientMeasure (H₁.subgroupOf H₂) (@Subgroup.isClosed_subgroupOf _ _ _ H₁ H₂ hH₁)
      μH₂ μK hmod₁₂).map (quotientStageMap h₁₂ q₂.out)
  measurable' := by
    have : LocallyCompactSpace (MulAction.orbitRel.Quotient H₁ G) :=
      (MulAction.isOpenQuotientMap_quotientMk (Γ := H₁) (T := G)).locallyCompactSpace
    have : SecondCountableTopology (MulAction.orbitRel.Quotient H₁ G) :=
      (MulAction.isOpenQuotientMap_quotientMk (Γ := H₁) (T := G)).secondCountableTopology
    let hK := @Subgroup.isClosed_subgroupOf _ _ _ H₁ H₂ hH₁
    let ν₁₂ := quotientMeasure (H₁.subgroupOf H₂) hK μH₂ μK hmod₁₂
    have : ν₁₂.Regular := regular_quotientMeasure (H₁.subgroupOf H₂) hK μH₂ μK hmod₁₂
    have hF_cont :
        Continuous fun p : G × MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂ =>
          quotientStageMap h₁₂ p.1 p.2 := by
      have hoq := IsOpenQuotientMap.prodMap (IsOpenQuotientMap.id (X := G))
        (MulAction.isOpenQuotientMap_quotientMk (Γ := H₁.subgroupOf H₂) (T := H₂))
      rw [hoq.isQuotientMap.continuous_iff]
      exact continuous_quotient_mk'.comp
        ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
    refine measurable_kernel_of_isQuotientMap
      (MulAction.isOpenQuotientMap_quotientMk (Γ := H₂) (T := G)).isQuotientMap ν₁₂
      hF_cont (fun g => ?_) (fun q₂ => ?_)
    · let h₂ : H₂ := ⟨_, orbitRelQuotient_out_mul_inv_mem H₂ g⟩
      have hrep : (Quotient.mk (MulAction.orbitRel H₂ G) g).out = (h₂ : G) * g := by simp [h₂]
      have hcomp : quotientStageMap h₁₂ ((h₂ : G) * g) =
          quotientStageMap h₁₂ g ∘ orbitRelQuotientMulRight (H₁.subgroupOf H₂) h₂ := by
        ext q₁₂
        induction q₁₂ using Quotient.inductionOn' with | h x =>
        simp [mul_assoc]
      rw [hrep, hcomp, ← Measure.map_map
        (isClosedEmbedding_quotientStageMap hH₂ h₁₂ g).continuous.measurable
        (orbitRelQuotientMulRight (H₁.subgroupOf H₂) h₂).continuous.measurable,
        map_mulRight_quotientMeasure]
    · refine ⟨fun C hC => ?_⟩
      have hemb := isClosedEmbedding_quotientStageMap hH₂ h₁₂ q₂.out
      rw [hemb.measurableEmbedding.map_apply]
      exact (hemb.isCompact_preimage hC).measure_lt_top

theorem quotientStageKernel_apply {H₁ H₂ : Subgroup G}
    (hH₁ : IsClosed (H₁ : Set G)) (hH₂ : IsClosed (H₂ : Set G)) (h₁₂ : H₁ ≤ H₂)
    [LocallyCompactSpace H₂] [SecondCountableTopology H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [LocallyCompactSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (H₁.subgroupOf H₂)] [BorelSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₁ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₁ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₂ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₂ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    [BorelSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    (μH₂ : Measure H₂) [μH₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₂]
    [μH₂.IsOpenPosMeasure]
    (μK : Measure (H₁.subgroupOf H₂)) [μK.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μK]
    [μK.IsOpenPosMeasure]
    (hmod₁₂ : ∀ k : H₁.subgroupOf H₂, Measure.modularCharacter (G := H₂) (k : H₂) =
      Measure.modularCharacter (G := H₁.subgroupOf H₂) k)
    (q₂ : MulAction.orbitRel.Quotient H₂ G) :
    quotientStageKernel hH₁ hH₂ h₁₂ μH₂ μK hmod₁₂ q₂ =
      (quotientMeasure (H₁.subgroupOf H₂) (@Subgroup.isClosed_subgroupOf _ _ _ H₁ H₂ hH₁)
        μH₂ μK hmod₁₂).map (quotientStageMap h₁₂ q₂.out) :=
  (rfl)

@[simp]
theorem quotientStageKernel_mk {H₁ H₂ : Subgroup G}
    (hH₁ : IsClosed (H₁ : Set G)) (hH₂ : IsClosed (H₂ : Set G)) (h₁₂ : H₁ ≤ H₂)
    [LocallyCompactSpace H₂] [SecondCountableTopology H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [LocallyCompactSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (H₁.subgroupOf H₂)] [BorelSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₁ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₁ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₂ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₂ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    [BorelSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    (μH₂ : Measure H₂) [μH₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₂]
    [μH₂.IsOpenPosMeasure]
    (μK : Measure (H₁.subgroupOf H₂)) [μK.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μK]
    [μK.IsOpenPosMeasure]
    (hmod₁₂ : ∀ k : H₁.subgroupOf H₂, Measure.modularCharacter (G := H₂) (k : H₂) =
      Measure.modularCharacter (G := H₁.subgroupOf H₂) k) (g : G) :
    quotientStageKernel hH₁ hH₂ h₁₂ μH₂ μK hmod₁₂ (Quotient.mk'' g) =
      (quotientMeasure (H₁.subgroupOf H₂) (@Subgroup.isClosed_subgroupOf _ _ _ H₁ H₂ hH₁)
        μH₂ μK hmod₁₂).map (quotientStageMap h₁₂ g) := by
  rw [quotientStageKernel_apply]
  let h₂ : H₂ := ⟨_, orbitRelQuotient_out_mul_inv_mem H₂ g⟩
  have hrep : (Quotient.mk'' g : MulAction.orbitRel.Quotient H₂ G).out = (h₂ : G) * g := by
    simp [h₂]
  have hcomp : quotientStageMap h₁₂ ((h₂ : G) * g) =
      quotientStageMap h₁₂ g ∘ orbitRelQuotientMulRight (H₁.subgroupOf H₂) h₂ := by
    ext q₁₂
    induction q₁₂ using Quotient.inductionOn' with | h x =>
    simp [mul_assoc]
  rw [hrep, hcomp, ← Measure.map_map
    (isClosedEmbedding_quotientStageMap hH₂ h₁₂ g).continuous.measurable
    (orbitRelQuotientMulRight (H₁.subgroupOf H₂) h₂).continuous.measurable,
    map_mulRight_quotientMeasure]

variable [MeasurableSpace G] [BorelSpace G]

/-- **Composition of quotient measures in stages:** for nested closed subgroups `H₁ ≤ H₂ ≤ G`
with matching modular characters, composing `quotientStageKernel` with `ν₂` recovers `ν₁`. -/
theorem quotientStageKernel_comp_quotientMeasure {H₁ H₂ : Subgroup G}
    (hH₁ : IsClosed (H₁ : Set G)) (hH₂ : IsClosed (H₂ : Set G)) (h₁₂ : H₁ ≤ H₂)
    [LocallyCompactSpace H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [LocallyCompactSpace H₂] [SecondCountableTopology H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [LocallyCompactSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (H₁.subgroupOf H₂)] [BorelSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₁ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₁ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₂ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₂ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    [BorelSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH₁ : Measure H₁) [μH₁.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₁]
    [μH₁.IsOpenPosMeasure]
    (μH₂ : Measure H₂) [μH₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₂]
    [μH₂.IsOpenPosMeasure]
    (μK : Measure (H₁.subgroupOf H₂)) [μK.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μK]
    [μK.IsOpenPosMeasure]
    (hμK : μK.map (Subgroup.subgroupOfContinuousMulEquivOfLe h₁₂) = μH₁)
    (hmod₁ : ∀ h : H₁, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₁) h)
    (hmod₂ : ∀ h : H₂, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₂) h) :
    quotientStageKernel hH₁ hH₂ h₁₂ μH₂ μK (modularCharacter_subgroupOf_eq h₁₂ hmod₁ hmod₂) ∘ₘ
        quotientMeasure H₂ hH₂ μG μH₂ hmod₂ =
      quotientMeasure H₁ hH₁ μG μH₁ hmod₁ := by
  have : T2Space (MulAction.orbitRel.Quotient H₁ G) := t2Space_orbitRelQuotient H₁ hH₁
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient H₁ G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H₁) (T := G)).locallyCompactSpace
  have : SecondCountableTopology (MulAction.orbitRel.Quotient H₁ G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H₁) (T := G)).secondCountableTopology
  let hmod₁₂ := modularCharacter_subgroupOf_eq h₁₂ hmod₁ hmod₂
  let hK := @Subgroup.isClosed_subgroupOf _ _ _ H₁ H₂ hH₁
  let κ := quotientStageKernel hH₁ hH₂ h₁₂ μH₂ μK hmod₁₂
  let ν₁ := quotientMeasure H₁ hH₁ μG μH₁ hmod₁
  let ν₂ := quotientMeasure H₂ hH₂ μG μH₂ hmod₂
  let ν₁₂ := quotientMeasure (H₁.subgroupOf H₂) hK μH₂ μK hmod₁₂
  have hν₁_fin : IsFiniteMeasureOnCompacts ν₁ :=
    isFiniteMeasureOnCompacts_quotientMeasure H₁ hH₁ μG μH₁ hmod₁
  have hν₂_fin : IsFiniteMeasureOnCompacts ν₂ :=
    isFiniteMeasureOnCompacts_quotientMeasure H₂ hH₂ μG μH₂ hmod₂
  have hν₁₂_fin : IsFiniteMeasureOnCompacts ν₁₂ :=
    isFiniteMeasureOnCompacts_quotientMeasure (H₁.subgroupOf H₂) hK μH₂ μK hmod₁₂
  refine measure_eq_of_lintegral_ofReal_eq fun F hF0 => ?_
  obtain ⟨f, hfF, -⟩ := exists_quotientFibreAverage_eq H₁ hH₁ μH₁ F
  have hF_meas : AEMeasurable (fun q₁ => ENNReal.ofReal (F q₁)) (κ ∘ₘ ν₂) :=
    (ENNReal.continuous_ofReal.comp F.continuous).measurable.aemeasurable
  rw [Measure.lintegral_bind κ.aemeasurable hF_meas]
  have hinner (q₂ : MulAction.orbitRel.Quotient H₂ G) :
      ∫⁻ q₁, ENNReal.ofReal (F q₁) ∂κ q₂ =
        ENNReal.ofReal (quotientFibreAverage H₂ hH₂ μH₂ f q₂) := by
    have hemb := isClosedEmbedding_quotientStageMap hH₂ h₁₂ q₂.out
    rw [quotientStageKernel_apply, hemb.measurableEmbedding.lintegral_map]
    have hint : Integrable (fun q₁₂ => F (quotientStageMap h₁₂ q₂.out q₁₂)) ν₁₂ :=
      (F.continuous.comp hemb.continuous).integrable_of_hasCompactSupport
        (F.hasCompactSupport.comp_isClosedEmbedding hemb)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => hF0 _), ← hfF]
    have hstage := integral_stageMap_eq_quotientFibreAverage hH₁ hH₂ h₁₂ μH₁ μH₂ μK
      hμK hmod₁₂ f q₂.out
    rw [hstage, Quotient.out_eq']
  simp_rw [hinner]
  have havg_nonneg (q₂ : MulAction.orbitRel.Quotient H₂ G) :
      0 ≤ quotientFibreAverage H₂ hH₂ μH₂ f q₂ := by
    rw [← Quotient.out_eq' q₂,
      ← integral_stageMap_eq_quotientFibreAverage hH₁ hH₂ h₁₂ μH₁ μH₂ μK hμK hmod₁₂ f q₂.out,
      hfF]
    exact integral_nonneg fun _ => hF0 _
  rw [← ofReal_integral_eq_lintegral_ofReal (quotientFibreAverage H₂ hH₂ μH₂ f).integrable
      (ae_of_all _ havg_nonneg),
    integral_quotientFibreAverage_quotientMeasure H₂ hH₂ μG μH₂ hmod₂ f,
    ← integral_quotientFibreAverage_quotientMeasure H₁ hH₁ μG μH₁ hmod₁ f, hfF]

/-- **Composition in stages (Lebesgue integral)** for nested closed subgroups `H₁ ≤ H₂ ≤ G`. -/
theorem lintegral_quotientMeasure_stages {H₁ H₂ : Subgroup G}
    (hH₁ : IsClosed (H₁ : Set G)) (hH₂ : IsClosed (H₂ : Set G)) (h₁₂ : H₁ ≤ H₂)
    [LocallyCompactSpace H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [LocallyCompactSpace H₂] [SecondCountableTopology H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [LocallyCompactSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (H₁.subgroupOf H₂)] [BorelSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₁ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₁ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₂ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₂ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    [BorelSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH₁ : Measure H₁) [μH₁.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₁]
    [μH₁.IsOpenPosMeasure]
    (μH₂ : Measure H₂) [μH₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₂]
    [μH₂.IsOpenPosMeasure]
    (μK : Measure (H₁.subgroupOf H₂)) [μK.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μK]
    [μK.IsOpenPosMeasure]
    (hμK : μK.map (Subgroup.subgroupOfContinuousMulEquivOfLe h₁₂) = μH₁)
    (hmod₁ : ∀ h : H₁, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₁) h)
    (hmod₂ : ∀ h : H₂, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₂) h)
    {F : MulAction.orbitRel.Quotient H₁ G → ℝ≥0∞}
    (hF : AEMeasurable F (quotientMeasure H₁ hH₁ μG μH₁ hmod₁)) :
    ∫⁻ q₁, F q₁ ∂quotientMeasure H₁ hH₁ μG μH₁ hmod₁ =
      ∫⁻ q₂, (∫⁻ q₁₂, F (quotientStageMap h₁₂ q₂.out q₁₂) ∂
        quotientMeasure (H₁.subgroupOf H₂) (@Subgroup.isClosed_subgroupOf _ _ _ H₁ H₂ hH₁)
          μH₂ μK (modularCharacter_subgroupOf_eq h₁₂ hmod₁ hmod₂)) ∂
        quotientMeasure H₂ hH₂ μG μH₂ hmod₂ := by
  have hcomp := quotientStageKernel_comp_quotientMeasure hH₁ hH₂ h₁₂ μG μH₁ μH₂ μK hμK hmod₁ hmod₂
  conv_lhs => rw [← hcomp]
  rw [Measure.lintegral_bind (quotientStageKernel _ _ _ _ _ _).aemeasurable (hcomp.symm ▸ hF)]
  congr 1 with q₂
  rw [quotientStageKernel_apply]
  exact (isClosedEmbedding_quotientStageMap hH₂ h₁₂ q₂.out).measurableEmbedding.lintegral_map F

/-- **Composition in stages (Bochner integral)** for nested closed subgroups `H₁ ≤ H₂ ≤ G` and
integrable functions into any real normed space `E`. -/
theorem integral_quotientMeasure_stages {H₁ H₂ : Subgroup G}
    (hH₁ : IsClosed (H₁ : Set G)) (hH₂ : IsClosed (H₂ : Set G)) (h₁₂ : H₁ ≤ H₂)
    [LocallyCompactSpace H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [LocallyCompactSpace H₂] [SecondCountableTopology H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [LocallyCompactSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (H₁.subgroupOf H₂)] [BorelSpace (H₁.subgroupOf H₂)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₁ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₁ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient H₂ G)]
    [BorelSpace (MulAction.orbitRel.Quotient H₂ G)]
    [MeasurableSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    [BorelSpace (MulAction.orbitRel.Quotient (H₁.subgroupOf H₂) H₂)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH₁ : Measure H₁) [μH₁.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₁]
    [μH₁.IsOpenPosMeasure]
    (μH₂ : Measure H₂) [μH₂.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH₂]
    [μH₂.IsOpenPosMeasure]
    (μK : Measure (H₁.subgroupOf H₂)) [μK.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μK]
    [μK.IsOpenPosMeasure]
    (hμK : μK.map (Subgroup.subgroupOfContinuousMulEquivOfLe h₁₂) = μH₁)
    (hmod₁ : ∀ h : H₁, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₁) h)
    (hmod₂ : ∀ h : H₂, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H₂) h)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : MulAction.orbitRel.Quotient H₁ G → E}
    (hF : Integrable F (quotientMeasure H₁ hH₁ μG μH₁ hmod₁)) :
    ∫ q₁, F q₁ ∂quotientMeasure H₁ hH₁ μG μH₁ hmod₁ =
      ∫ q₂, (∫ q₁₂, F (quotientStageMap h₁₂ q₂.out q₁₂) ∂
        quotientMeasure (H₁.subgroupOf H₂) (@Subgroup.isClosed_subgroupOf _ _ _ H₁ H₂ hH₁)
          μH₂ μK (modularCharacter_subgroupOf_eq h₁₂ hmod₁ hmod₂)) ∂
        quotientMeasure H₂ hH₂ μG μH₂ hmod₂ := by
  have hcomp := quotientStageKernel_comp_quotientMeasure hH₁ hH₂ h₁₂ μG μH₁ μH₂ μK hμK hmod₁ hmod₂
  let κ := quotientStageKernel hH₁ hH₂ h₁₂ μH₂ μK (modularCharacter_subgroupOf_eq h₁₂ hmod₁ hmod₂)
  have hF' : Integrable F ((κ ∘ₖ Kernel.const Unit (quotientMeasure H₂ hH₂ μG μH₂ hmod₂)) ()) := by
    simpa [κ, Measure.comp_eq_comp_const_apply, hcomp] using hF
  have hint := Kernel.integral_comp hF'
  simp only [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply] at hint
  rw [← hcomp, hint]
  congr 1 with q₂
  rw [quotientStageKernel_apply]
  exact (isClosedEmbedding_quotientStageMap hH₂ h₁₂ q₂.out).measurableEmbedding.integral_map F

end CompositionInStages

end TauCeti
