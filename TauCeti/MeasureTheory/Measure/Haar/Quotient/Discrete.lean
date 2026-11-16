/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Quotient
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.MeasureTheory.Measure.Count.Topology
public import TauCeti.MeasureTheory.Measure.Haar.Quotient.Integral
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import TauCeti.MeasureTheory.Group.ModularCharacter
import TauCeti.Topology.Compactness.LocallyCompact

/-!
# Discrete subgroups and the two quotient-measure conventions

When `Γ ≤ G` is a discrete subgroup of a unimodular locally compact group `G`, both `G` and `Γ`
have trivial modular character, so Weil's quotient measure `quotientMeasure` exists on the right
coset space `Γ \ G` with respect to counting measure on `Γ`. Integration over the fibres reduces
to summing over `Γ`-orbits (`MulAction.automorphize`).

Inversion `Γ g ↦ g⁻¹ Γ` defines a homeomorphism `orbitRelQuotientInvHomeomorph : Γ \ G ≃ₜ G ⧸ Γ`
intertwining the right action of `G` on `Γ \ G` with the left action of `G` on `G ⧸ Γ`. When `G`
is unimodular, pushing Weil's quotient measure forward along this homeomorphism produces a
left-`G`-invariant Radon measure on `G ⧸ Γ` satisfying the right-orbit unfolding identity with
`QuotientGroup.automorphize`. Whenever `Γ.op` admits a measurable fundamental domain `𝓕`, this
pushforward measure agrees with the fundamental-domain pushforward `(μG.restrict 𝓕).map mk`.

## Main declarations

* `TauCeti.orbitRelQuotientInvHomeomorph`: the inversion homeomorphism
  `MulAction.orbitRel.Quotient H G ≃ₜ G ⧸ H` sending `H g` to `g⁻¹ H`.
* `TauCeti.smulInvariantMeasure_map_orbitRelQuotientInvHomeomorph_quotientMeasure`: pushing a
  right-invariant quotient measure along inversion yields a left-`G`-invariant measure on `G ⧸ H`.
* `TauCeti.modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology`: matching (trivial)
  modular characters for a unimodular locally compact group and any discrete subgroup.
* `TauCeti.lintegral_quotientMeasure_count`, `TauCeti.integral_quotientMeasure_count`,
  `TauCeti.integral_quotientMeasure_automorphize`: discrete unfolding on `Γ \ G` with respect to
  counting measure on `Γ`.
* `TauCeti.quotientGroup_automorphize_orbitRelQuotientInvHomeomorph`,
  `TauCeti.lintegral_map_orbitRelQuotientInvHomeomorph_automorphize`,
  `TauCeti.integral_map_orbitRelQuotientInvHomeomorph_automorphize`: transferring the unfolding
  identity across inversion to `G ⧸ Γ` and `QuotientGroup.automorphize`.
* `MeasureTheory.IsFundamentalDomain.isFiniteMeasureOnCompacts_map_quotientGroup_mk`: local
  finiteness of the fundamental-domain quotient measure on `G ⧸ Γ`, without assuming finite
  covolume.
* `TauCeti.map_orbitRelQuotientInvHomeomorph_eq_fundamentalDomain`: equality of the inverted
  Weil quotient measure and `(μG.restrict 𝓕).map QuotientGroup.mk`.

## References

* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, §2.6.
-/

public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace TauCeti

/-! ### Inversion homeomorphism between right and left coset spaces -/

section InvHomeomorph

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inversion `H g ↦ g⁻¹ H` is a homeomorphism from the right coset space
`MulAction.orbitRel.Quotient H G` (`H \ G`) to the left coset space `G ⧸ H`. -/
def orbitRelQuotientInvHomeomorph (H : Subgroup G) :
    MulAction.orbitRel.Quotient H G ≃ₜ G ⧸ H where
  toEquiv := QuotientGroup.quotientRightRelEquivQuotientLeftRel (s := H)
  continuous_toFun := by
    rw [(MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).isQuotientMap.continuous_iff]
    exact QuotientGroup.continuous_mk.comp continuous_inv
  continuous_invFun := by
    rw [(QuotientGroup.isOpenQuotientMap_mk (N := H)).isQuotientMap.continuous_iff]
    exact continuous_quot_mk.comp continuous_inv

@[simp]
theorem orbitRelQuotientInvHomeomorph_mk (H : Subgroup G) (g : G) :
    orbitRelQuotientInvHomeomorph H (Quotient.mk (MulAction.orbitRel H G) g) =
      QuotientGroup.mk g⁻¹ := (rfl)

@[simp]
theorem orbitRelQuotientInvHomeomorph_symm_mk (H : Subgroup G) (g : G) :
    (orbitRelQuotientInvHomeomorph H).symm (QuotientGroup.mk g) =
      Quotient.mk (MulAction.orbitRel H G) g⁻¹ := (rfl)

/-- The inversion homeomorphism intertwines right multiplication by `g` on `H \ G` with left
multiplication by `g⁻¹` on `G ⧸ H`. -/
theorem orbitRelQuotientInvHomeomorph_mulRight (H : Subgroup G) (g : G)
    (q : MulAction.orbitRel.Quotient H G) :
    orbitRelQuotientInvHomeomorph H (orbitRelQuotientMulRight H g q) =
      g⁻¹ • orbitRelQuotientInvHomeomorph H q := by
  refine Quotient.inductionOn q fun x => ?_
  rw [orbitRelQuotientMulRight_mk, orbitRelQuotientInvHomeomorph_mk,
    orbitRelQuotientInvHomeomorph_mk, mul_inv_rev]
  rfl

/-- The inverse of `orbitRelQuotientInvHomeomorph` intertwines left multiplication by `g` on
`G ⧸ H` with right multiplication by `g⁻¹` on `H \ G`. -/
theorem orbitRelQuotientInvHomeomorph_symm_smul (H : Subgroup G) (g : G) (x : G ⧸ H) :
    (orbitRelQuotientInvHomeomorph H).symm (g • x) =
      orbitRelQuotientMulRight H g⁻¹ ((orbitRelQuotientInvHomeomorph H).symm x) := by
  refine QuotientGroup.induction_on x fun y => ?_
  have hsmul : g • (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk (g * y) := rfl
  rw [hsmul, orbitRelQuotientInvHomeomorph_symm_mk, orbitRelQuotientInvHomeomorph_symm_mk,
    orbitRelQuotientMulRight_mk, mul_inv_rev]

/-- Pushing a right-`G`-invariant measure on `H \ G` forward along `orbitRelQuotientInvHomeomorph`
yields a left-`G`-invariant measure on `G ⧸ H`. -/
theorem map_smul_map_orbitRelQuotientInvHomeomorph (H : Subgroup G)
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (ν : Measure (MulAction.orbitRel.Quotient H G))
    (hν : ∀ g : G, Measure.map (orbitRelQuotientMulRight H g) ν = ν) (g : G) :
    Measure.map (g • ·) (Measure.map (orbitRelQuotientInvHomeomorph H) ν) =
      Measure.map (orbitRelQuotientInvHomeomorph H) ν := by
  have he : Measurable (orbitRelQuotientInvHomeomorph H) :=
    (orbitRelQuotientInvHomeomorph H).continuous.measurable
  have hsmul : Measurable (fun x : G ⧸ H => g • x) :=
    (continuous_const_smul g).measurable
  have hmr : Measurable (orbitRelQuotientMulRight H g⁻¹) :=
    (orbitRelQuotientMulRight H g⁻¹).continuous.measurable
  rw [Measure.map_map hsmul he]
  have hcomp : ((g • ·) ∘ (orbitRelQuotientInvHomeomorph H)) =
      (orbitRelQuotientInvHomeomorph H) ∘ (orbitRelQuotientMulRight H g⁻¹) := by
    ext q
    simp [orbitRelQuotientInvHomeomorph_mulRight]
  rw [hcomp, ← Measure.map_map he hmr, hν g⁻¹]

/-- Pushing a right-`G`-invariant measure on `H \ G` forward along `orbitRelQuotientInvHomeomorph`
produces a `SMulInvariantMeasure` on `G ⧸ H`. -/
theorem smulInvariantMeasure_map_orbitRelQuotientInvHomeomorph (H : Subgroup G)
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (ν : Measure (MulAction.orbitRel.Quotient H G))
    (hν : ∀ g : G, Measure.map (orbitRelQuotientMulRight H g) ν = ν) :
    SMulInvariantMeasure G (G ⧸ H) (Measure.map (orbitRelQuotientInvHomeomorph H) ν) where
  measure_preimage_smul g s hs := by
    have h := map_smul_map_orbitRelQuotientInvHomeomorph H ν hν g
    have hsmul : Measurable (fun x : G ⧸ H => g • x) := (continuous_const_smul g).measurable
    rw [← Measure.map_apply hsmul hs, h]

/-- Pushing Weil's quotient measure on `H \ G` forward along `orbitRelQuotientInvHomeomorph`
produces a left-`G`-invariant measure on `G ⧸ H`. -/
theorem smulInvariantMeasure_map_orbitRelQuotientInvHomeomorph_quotientMeasure
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    SMulInvariantMeasure G (G ⧸ H)
      (Measure.map (orbitRelQuotientInvHomeomorph H)
        (quotientMeasure H hH μG μH hmod)) :=
  smulInvariantMeasure_map_orbitRelQuotientInvHomeomorph H _
    (map_mulRight_quotientMeasure H hH μG μH hmod)

end InvHomeomorph

/-! ### Unimodularity and discrete subgroups -/

section Unimodular

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A unimodular locally compact group and any discrete subgroup have matching (trivial) modular
characters. -/
theorem modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (Γ : Subgroup G) [DiscreteTopology Γ] (γ : Γ) :
    Measure.modularCharacter (G := G) γ = Measure.modularCharacter (G := Γ) γ := by
  rw [modularCharacter_eq_one_of_isMulRightInvariant (μ := μG) γ,
    modularCharacter_eq_one_of_discreteTopology γ]

end Unimodular

end TauCeti

namespace MeasureTheory.IsFundamentalDomain

/-- For a countable subgroup `Γ` acting on the right on a locally compact group `G`, pushing a
right-invariant locally finite measure `μ` restricted to a fundamental domain `𝓕` forward along
`QuotientGroup.mk` produces a measure finite on compact sets (even when `μ 𝓕 = ⊤`). -/
theorem isFiniteMeasureOnCompacts_map_quotientGroup_mk {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {Γ : Subgroup G} [Countable Γ]
    [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] [T2Space (G ⧸ Γ)]
    {μ : Measure G} [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μ) :
    IsFiniteMeasureOnCompacts ((μ.restrict 𝓕).map (QuotientGroup.mk : G → G ⧸ Γ)) := by
  refine ⟨fun C hC => ?_⟩
  -- Step 1: Lift the compact set `C ⊆ G ⧸ Γ` to a compact closed (hence measurable) set `K' ⊆ G`.
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have hπ : IsOpenQuotientMap π := QuotientGroup.isOpenQuotientMap_mk
  obtain ⟨K, hKc, hCsub⟩ := hπ.isOpenMap.exists_isCompact_subset_image hC
    (by rw [hπ.surjective.range_eq]; exact subset_univ _)
  let K' : Set G := closure K
  have hK'c : IsCompact K' := hKc.closure
  have hK'meas : MeasurableSet K' := isClosed_closure.measurableSet
  have himg_c : IsCompact (π '' K') := hK'c.image QuotientGroup.continuous_mk
  have himg_meas : MeasurableSet (π '' K') := himg_c.isClosed.measurableSet
  have hpre_meas : MeasurableSet (π ⁻¹' (π '' K')) :=
    QuotientGroup.continuous_mk.measurable himg_meas
  -- Step 2: Bound the indicator of the saturated preimage `π ⁻¹' (π '' K')` pointwise by the
  -- `Γ.op`-orbit sum of the indicator of `K'`.
  have hpoint : ∀ x : G,
      (π ⁻¹' (π '' K')).indicator (1 : G → ℝ≥0∞) x ≤
        ∑' γ : Γ.op, K'.indicator (1 : G → ℝ≥0∞) (γ • x) := by
    intro x
    by_cases hx : x ∈ π ⁻¹' (π '' K')
    · rcases hx with ⟨y, hyK', hyx⟩
      obtain ⟨γ, hγ⟩ : ∃ γ : Γ.op, γ • x = y := by
        have hrel : MulAction.orbitRel Γ.op G y x := Quotient.exact' hyx
        exact hrel
      rw [Set.indicator_of_mem (⟨y, hyK', hyx⟩ : x ∈ π ⁻¹' (π '' K')), Pi.one_apply]
      calc (1 : ℝ≥0∞) = K'.indicator (1 : G → ℝ≥0∞) (γ • x) := by
            rw [hγ, Set.indicator_of_mem hyK', Pi.one_apply]
        _ ≤ ∑' γ' : Γ.op, K'.indicator (1 : G → ℝ≥0∞) (γ' • x) :=
            le_tsum (fun γ' : Γ.op => K'.indicator (1 : G → ℝ≥0∞) (γ' • x)) γ
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  -- Step 3: Integrate over the fundamental domain `𝓕` and fold back into `μ K' < ∞`.
  have hbound : ((μ.restrict 𝓕).map π) C ≤ μ K' := by
    calc ((μ.restrict 𝓕).map π) C
        ≤ ((μ.restrict 𝓕).map π) (π '' K') :=
          measure_mono (hCsub.trans (Set.image_mono subset_closure))
      _ = (μ.restrict 𝓕) (π ⁻¹' (π '' K')) :=
          Measure.map_apply QuotientGroup.continuous_mk.measurable himg_meas
      _ = ∫⁻ x in 𝓕, (π ⁻¹' (π '' K')).indicator (1 : G → ℝ≥0∞) x ∂μ := by
          rw [lintegral_indicator_one hpre_meas]
      _ ≤ ∫⁻ x in 𝓕, ∑' γ : Γ.op, K'.indicator (1 : G → ℝ≥0∞) (γ • x) ∂μ :=
          lintegral_mono hpoint
      _ = ∑' γ : Γ.op, ∫⁻ x in 𝓕, K'.indicator (1 : G → ℝ≥0∞) (γ • x) ∂μ := by
          rw [lintegral_tsum]
          intro γ
          exact (measurable_const.indicator hK'meas).comp
            (continuous_const_smul γ).measurable |>.aemeasurable
      _ = ∫⁻ x, K'.indicator (1 : G → ℝ≥0∞) x ∂μ := (h𝓕.lintegral_eq_tsum'' _).symm
      _ = μ K' := lintegral_indicator_one hK'meas
  exact hbound.trans_lt hK'c.measure_lt_top

end MeasureTheory.IsFundamentalDomain

namespace TauCeti

/-! ### Discrete unfolding and equivalence of the left and right quotient conventions -/

section Automorphize

/-- Pulling `QuotientGroup.automorphize f` back along `orbitRelQuotientInvHomeomorph Γ` yields the
left-orbit automorphization `MulAction.automorphize (fun g => f g⁻¹)`. -/
theorem quotientGroup_automorphize_orbitRelQuotientInvHomeomorph
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace M] [AddCommMonoid M]
    (Γ : Subgroup G) (f : G → M) (q : MulAction.orbitRel.Quotient Γ G) :
    QuotientGroup.automorphize f (orbitRelQuotientInvHomeomorph Γ q) =
      MulAction.automorphize (fun g => f g⁻¹) q := by
  refine Quotient.inductionOn q fun g => ?_
  rw [orbitRelQuotientInvHomeomorph_mk]
  have hlhs : QuotientGroup.automorphize f (QuotientGroup.mk g⁻¹) =
      ∑' γ : Γ.op, f (γ • g⁻¹) := rfl
  have hrhs : MulAction.automorphize (fun g => f g⁻¹) (Quotient.mk (MulAction.orbitRel Γ G) g) =
      ∑' γ : Γ, f (((γ : G) * g)⁻¹) := rfl
  rw [hlhs, hrhs]
  let e : Γ ≃ Γ.op := (Equiv.inv Γ).trans Γ.equivOp
  rw [← e.tsum_eq]
  congr 1 with γ
  simp [e, Subgroup.smul_def, MulOpposite.smul_eq_mul_unop, mul_inv_rev]

end Automorphize

section Discrete

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T1Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
  (Γ : Subgroup G) [DiscreteTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  [MeasurableSpace (MulAction.orbitRel.Quotient Γ G)]
  [BorelSpace (MulAction.orbitRel.Quotient Γ G)]

/-- **Discrete unfolding (Lebesgue integral)** on `Γ \ G`: for a discrete subgroup `Γ` of a
unimodular second-countable locally compact group `G`, the integral against `μG` unfolds as the
quotient integral of the `Γ`-orbit sum. -/
theorem lintegral_quotientMeasure_count {f : G → ℝ≥0∞} (hf : AEMeasurable f μG) :
    ∫⁻ g, f g ∂μG =
      ∫⁻ q, ∑' γ : Γ, f ((γ : G) * q.out) ∂
        quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
          (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) := by
  rw [lintegral_quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
    (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) hf]
  congr 1
  ext q
  exact lintegral_count _

/-- **Discrete unfolding (Lebesgue integral, `MulAction.automorphize` form)** on `Γ \ G`. -/
theorem lintegral_quotientMeasure_automorphize {f : G → ℝ≥0∞} (hf : AEMeasurable f μG) :
    ∫⁻ g, f g ∂μG =
      ∫⁻ q, MulAction.automorphize f q ∂
        quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
          (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) := by
  rw [lintegral_quotientMeasure_count μG Γ hf]
  congr 1
  ext q
  conv_rhs => rw [← Quotient.out_eq q]
  rfl

/-- **Discrete unfolding (Bochner integral)** on `Γ \ G`: for a discrete subgroup `Γ` of a
unimodular second-countable locally compact group `G`, the Bochner integral of an integrable
function unfolds as the quotient integral of its `Γ`-orbit sum. -/
theorem integral_quotientMeasure_count {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : G → E} (hf : Integrable f μG) :
    ∫ g, f g ∂μG =
      ∫ q, ∑' γ : Γ, f ((γ : G) * q.out) ∂
        quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
          (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) := by
  by_cases hE : CompleteSpace E
  · have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
    have hae := ae_integrable_quotientFibre Γ Subgroup.isClosed_of_discreteTopology μG
      Measure.count (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) hf
    rw [integral_quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
      (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) hf]
    refine integral_congr_ae ?_
    filter_upwards [hae] with q hq
    rw [integral_countable hq]
    congr 1
    ext γ
    simp
  · simp [integral_of_not_completeSpace hE]

/-- **Discrete unfolding (Bochner integral, `MulAction.automorphize` form)** on `Γ \ G`. -/
theorem integral_quotientMeasure_automorphize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : G → E} (hf : Integrable f μG) :
    ∫ g, f g ∂μG =
      ∫ q, MulAction.automorphize f q ∂
        quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
          (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) := by
  rw [integral_quotientMeasure_count μG Γ hf]
  congr 1
  ext q
  conv_rhs => rw [← Quotient.out_eq q]
  rfl

variable [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

/-- **Right-orbit unfolding (Lebesgue integral)** on `G ⧸ Γ` via the inverted Weil quotient
measure: no fundamental domain is needed. -/
theorem lintegral_map_orbitRelQuotientInvHomeomorph_automorphize {f : G → ℝ≥0∞}
    (hf : AEMeasurable f μG) :
    ∫⁻ g, f g ∂μG =
      ∫⁻ x : G ⧸ Γ, QuotientGroup.automorphize f x ∂
        Measure.map (orbitRelQuotientInvHomeomorph Γ)
          (quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
            (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ)) := by
  have : μG.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μG
  have : μG.IsInvInvariant := μG.isInvInvariant_of_isMulRightInvariant
  have hinv_mp : MeasurePreserving (Inv.inv : G → G) μG μG := Measure.measurePreserving_inv μG
  have hf_inv : AEMeasurable (fun g => f g⁻¹) μG :=
    hf.comp_quasiMeasurePreserving hinv_mp.quasiMeasurePreserving
  calc ∫⁻ g, f g ∂μG
      = ∫⁻ g, f g⁻¹ ∂μG := by
          have h := lintegral_map_equiv (μ := μG) f (MeasurableEquiv.inv G)
          simp only [MeasurableEquiv.inv_apply, ← Measure.inv_def, Measure.inv_eq_self] at h
          exact h
    _ = ∫⁻ q, MulAction.automorphize (fun g => f g⁻¹) q ∂
          quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
            (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) :=
        lintegral_quotientMeasure_automorphize μG Γ hf_inv
    _ = ∫⁻ q, QuotientGroup.automorphize f (orbitRelQuotientInvHomeomorph Γ q) ∂
          quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
            (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) := by
        congr 1
        ext q
        exact (quotientGroup_automorphize_orbitRelQuotientInvHomeomorph Γ f q).symm
    _ = ∫⁻ x : G ⧸ Γ, QuotientGroup.automorphize f x ∂
          Measure.map (orbitRelQuotientInvHomeomorph Γ)
            (quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
              (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ)) := by
        have h := lintegral_map_equiv
          (μ := quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
            (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ))
          (QuotientGroup.automorphize f) (orbitRelQuotientInvHomeomorph Γ).toMeasurableEquiv
        exact h.symm

/-- **Right-orbit unfolding (Bochner integral)** on `G ⧸ Γ` via the inverted Weil quotient
measure: for every integrable `f : G → E`, `∫ g, f g ∂μG` equals the integral of
`QuotientGroup.automorphize f` against `ν.map (orbitRelQuotientInvHomeomorph Γ)`. -/
theorem integral_map_orbitRelQuotientInvHomeomorph_automorphize {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : G → E} (hf : Integrable f μG) :
    ∫ g, f g ∂μG =
      ∫ x : G ⧸ Γ, QuotientGroup.automorphize f x ∂
        Measure.map (orbitRelQuotientInvHomeomorph Γ)
          (quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
            (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ)) := by
  have : μG.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μG
  have : μG.IsInvInvariant := μG.isInvInvariant_of_isMulRightInvariant
  have hinv_mp : MeasurePreserving (Inv.inv : G → G) μG μG := Measure.measurePreserving_inv μG
  have hf_inv : Integrable (fun g => f g⁻¹) μG :=
    (hinv_mp.integrable_comp_emb (MeasurableEquiv.inv G).measurableEmbedding).2 hf
  calc ∫ g, f g ∂μG
      = ∫ g, f g⁻¹ ∂μG := by
          have h := integral_map_equiv (μ := μG) (MeasurableEquiv.inv G) f
          simp only [MeasurableEquiv.inv_apply, ← Measure.inv_def, Measure.inv_eq_self] at h
          exact h
    _ = ∫ q, MulAction.automorphize (fun g => f g⁻¹) q ∂
          quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
            (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) :=
        integral_quotientMeasure_automorphize μG Γ hf_inv
    _ = ∫ q, QuotientGroup.automorphize f (orbitRelQuotientInvHomeomorph Γ q) ∂
          quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
            (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ) := by
        congr 1
        ext q
        exact (quotientGroup_automorphize_orbitRelQuotientInvHomeomorph Γ f q).symm
    _ = ∫ x : G ⧸ Γ, QuotientGroup.automorphize f x ∂
          Measure.map (orbitRelQuotientInvHomeomorph Γ)
            (quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
              (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ)) := by
        have h := integral_map_equiv
          (μ := quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
            (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ))
          (orbitRelQuotientInvHomeomorph Γ).toMeasurableEquiv (QuotientGroup.automorphize f)
        exact h.symm

/-- **Equivalence of the two quotient conventions**: for a discrete subgroup `Γ` of a unimodular
second-countable locally compact group `G`, pushing Weil's quotient measure on `Γ \ G` forward
along `orbitRelQuotientInvHomeomorph Γ` yields the same measure on `G ⧸ Γ` as restricting `μG` to
any fundamental domain `𝓕` for `Γ.op` and pushing forward along `QuotientGroup.mk`. -/
theorem map_orbitRelQuotientInvHomeomorph_eq_fundamentalDomain {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μG) :
    Measure.map (orbitRelQuotientInvHomeomorph Γ)
        (quotientMeasure Γ Subgroup.isClosed_of_discreteTopology μG Measure.count
          (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ)) =
      (μG.restrict 𝓕).map (QuotientGroup.mk : G → G ⧸ Γ) := by
  -- Step 1: Establish regularity of both measures on the second countable locally compact `G ⧸ Γ`.
  have hΓ : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have : T2Space (MulAction.orbitRel.Quotient Γ G) := t2Space_orbitRelQuotient Γ hΓ
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient Γ G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := G)).locallyCompactSpace
  have : SecondCountableTopology (MulAction.orbitRel.Quotient Γ G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := G)).secondCountableTopology
  let e : MulAction.orbitRel.Quotient Γ G ≃ₜ G ⧸ Γ := orbitRelQuotientInvHomeomorph Γ
  have : T2Space (G ⧸ Γ) := e.symm.isEmbedding.t2Space
  have : LocallyCompactSpace (G ⧸ Γ) := QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace
  have : SecondCountableTopology (G ⧸ Γ) := e.symm.isInducing.secondCountableTopology
  let ν := quotientMeasure Γ hΓ μG Measure.count
    (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ)
  have : ν.Regular := regular_quotientMeasure Γ hΓ μG Measure.count
    (modularCharacter_eq_of_isMulRightInvariant_of_discreteTopology μG Γ)
  have : (Measure.map e ν).Regular := Measure.Regular.map e
  have : IsFiniteMeasureOnCompacts ((μG.restrict 𝓕).map (QuotientGroup.mk : G → G ⧸ Γ)) :=
    h𝓕.isFiniteMeasureOnCompacts_map_quotientGroup_mk
  have : ((μG.restrict 𝓕).map (QuotientGroup.mk : G → G ⧸ Γ)).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  -- Step 2: Compare integrals against every `F : C_c(G ⧸ Γ, ℝ)` by lifting `F ∘ e` via the
  -- surjective fibre average and inverting to obtain `f ∈ C_c(G, ℝ)` with `automorphize f = F`.
  refine Measure.ext_of_integral_eq_on_compactlySupported fun F => ?_
  let F' : CompactlySupportedContinuousMap (MulAction.orbitRel.Quotient Γ G) ℝ :=
    ⟨⟨F ∘ e, F.continuous.comp e.continuous⟩, F.hasCompactSupport.comp_homeomorph e⟩
  obtain ⟨f', hf'eq, -⟩ := exists_quotientFibreAverage_eq Γ hΓ Measure.count F'
  let f : G → ℝ := fun g => f' g⁻¹
  have hfc : Continuous f := f'.continuous.comp continuous_inv
  have hfk : HasCompactSupport f := f'.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)
  have hf_int : Integrable f μG := hfc.integrable_of_hasCompactSupport hfk
  have haut : QuotientGroup.automorphize f = F := by
    ext x
    have h1 : QuotientGroup.automorphize f x = MulAction.automorphize f' (e.symm x) := by
      have h0 := quotientGroup_automorphize_orbitRelQuotientInvHomeomorph Γ f (e.symm x)
      simpa [f, e] using h0
    rw [h1]
    have h2 : MulAction.automorphize f' (e.symm x) =
        ∑' γ : Γ, f' ((γ : G) * (e.symm x).out) := by
      conv_lhs => rw [← Quotient.out_eq (e.symm x)]
      rfl
    rw [h2]
    have hfib_int : Integrable (fun γ : Γ => f' ((γ : G) * (e.symm x).out)) Measure.count := by
      have hcont : Continuous (fun γ : Γ => f' ((γ : G) * (e.symm x).out)) :=
        f'.continuous.comp ((continuous_subtype_val).mul continuous_const)
      have hcomp : HasCompactSupport (fun γ : Γ => f' ((γ : G) * (e.symm x).out)) := by
        have hcomp_mul : HasCompactSupport (fun g : G => f' (g * (e.symm x).out)) :=
          f'.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight (e.symm x).out)
        exact hcomp_mul.comp_isClosedEmbedding hΓ.isClosedEmbedding_subtypeVal
      exact hcont.integrable_of_hasCompactSupport hcomp
    have hsum : ∑' γ : Γ, f' ((γ : G) * (e.symm x).out) =
        ∫ γ : Γ, f' ((γ : G) * (e.symm x).out) ∂Measure.count := by
      rw [integral_countable hfib_int]
      congr 1
      ext γ
      simp
    rw [hsum, ← quotientFibreAverage_apply Γ hΓ Measure.count f' (e.symm x), hf'eq]
    simp [F']
  -- Step 3: Both integrals of `F = QuotientGroup.automorphize f` unfold to `∫ g, f g ∂μG`.
  have hL : ∫ x, F x ∂Measure.map e ν = ∫ g, f g ∂μG := by
    rw [← haut]
    exact (integral_map_orbitRelQuotientInvHomeomorph_automorphize μG Γ hf_int).symm
  have hR : ∫ x, F x ∂((μG.restrict 𝓕).map (QuotientGroup.mk : G → G ⧸ Γ)) = ∫ g, f g ∂μG := by
    have hmeas : AEStronglyMeasurable (QuotientGroup.automorphize f)
        ((μG.restrict 𝓕).map (QuotientGroup.mk : G → G ⧸ Γ)) := by
      rw [haut]
      exact F.continuous.aestronglyMeasurable
    rw [← haut]
    exact (QuotientGroup.integral_eq_integral_automorphize h𝓕 hf_int hmeas).symm
  exact hL.trans hR.symm

end Discrete

end TauCeti
