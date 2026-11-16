/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.UrysohnsLemma
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Group.ModularCharacter
import TauCeti.Topology.Compactness.LocallyCompact

/-!
# Weil's quotient measure on homogeneous coset spaces

Let `G` be a locally compact topological group and `H ≤ G` a closed subgroup, acting on `G` by left
multiplication. The space of right cosets `H \ G` is modelled by `MulAction.orbitRel.Quotient H G`,
carrying the quotient topology and the right `G`-action `H x ↦ H (x g)` (`TauCeti.rightCosetMul`).

Inversion `H g ↦ g⁻¹ H` defines a homeomorphism
`TauCeti.rightCosetHomeomorphLeftCoset : MulAction.orbitRel.Quotient H G ≃ₜ G ⧸ H`
intertwining the right `G`-action on `H \ G` with the left `G`-action on `G ⧸ H`.
When `H` is closed in `G`, the quotient `H \ G` is Hausdorff and locally compact (and second
countable when `G` is), without requiring `G` itself to be Hausdorff.

Given a right-invariant Radon measure `μH` on `H`, integration along `H`-orbits defines a
positive linear averaging operator
`TauCeti.quotientAverage : C_c(G, ℝ) →ₚ[ℝ] C_c(H \ G, ℝ)`,
which is surjective whenever `μH` is a right Haar measure. When `μG` is a right Haar measure on `G`
and the modular characters of `G` and `H` agree on `H`, Folland's averaging lemma shows that
`f ↦ ∫ g, f g ∂μG` descends along `quotientAverage` to a positive linear functional on
`C_c(H \ G, ℝ)`. By the Riesz–Markov–Kakutani representation theorem this defines a regular
right-`G`-invariant Radon measure `TauCeti.quotientMeasure` on `H \ G` satisfying Weil's
integration formula

`∫ g, f g ∂μG = ∫ q, (∫ h : H, f (h * q.out) ∂μH) ∂ν`

for all compactly supported continuous `f : G → ℝ`. When `G` is second countable, `ν` is the unique
right-`G`-invariant measure finite on compacts satisfying this formula
(`TauCeti.exists_unique_quotientMeasure`), scales inversely in `μH` and linearly in `μG`, and
(when `G` is Hausdorff) every right-`G`-invariant Radon measure on `H \ G` is a nonnegative scalar
multiple of `ν`.

## Main definitions

* `TauCeti.rightCosetMul`, `TauCeti.rightCosetMulHomeomorph`: right translation `H x ↦ H (x g)` on
  `MulAction.orbitRel.Quotient H G`.
* `TauCeti.rightCosetEquivLeftCoset`, `TauCeti.rightCosetHomeomorphLeftCoset`: the inversion
  equivalence and homeomorphism `H \ G ≃ₜ G ⧸ H` sending `H g ↦ g⁻¹ H`.
* `TauCeti.quotientAverage`: the orbit-averaging positive linear map
  `C_c(G, ℝ) →ₚ[ℝ] C_c(H \ G, ℝ)` sending `f` to `H g ↦ ∫ h : H, f (h * g) ∂μH`.
* `TauCeti.quotientMeasure`: Weil's quotient measure on `MulAction.orbitRel.Quotient H G`, built
  via `RealRMK.rieszMeasure`.

## Main results

* `TauCeti.quotientAverage_surjective`: surjectivity of orbit averaging onto `C_c(H \ G, ℝ)`, with
  nonnegative lifts of nonnegative functions.
* `TauCeti.regular_quotientMeasure`, `TauCeti.isOpenPosMeasure_quotientMeasure`,
  `TauCeti.integral_eq_integral_quotientMeasure`, `TauCeti.map_rightCosetMul_quotientMeasure`:
  regularity, strict positivity on nonempty open sets, Weil's integration formula on compactly
  supported continuous functions, and right `G`-invariance of `quotientMeasure`.
* `TauCeti.exists_unique_quotientMeasure`: existence and uniqueness of Weil's quotient measure on
  second countable locally compact groups.
* `TauCeti.quotientMeasure_smul_right`, `TauCeti.quotientMeasure_smul_left`: scaling laws in the
  Haar measures on `H` and `G`.
* `TauCeti.exists_smul_quotientMeasure_of_map_rightCosetMul_eq`: uniqueness of right-`G`-invariant
  Radon measures on `H \ G` up to a scalar factor.

## References

* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.6 (Lemma 2.48 and
  Theorem 2.49).
* Vladimir Platonov, Andrei Rapinchuk, Igor Rapinchuk, *Algebraic Groups and Number Theory*,
  Theorem 3.64.
-/

public section

open Filter MeasureTheory Set Topology CompactlySupportedContinuousMap
open scoped CompactlySupported ENNReal NNReal Pointwise Topology

namespace TauCeti

/-! ### Right-coset space `H \ G`, right translation, and inversion homeomorphism -/

section RightCosetSpace

variable {G : Type*} [Group G]

/-- Right multiplication `H x ↦ H (x * g)` on the right-coset space
`MulAction.orbitRel.Quotient H G`. -/
def rightCosetMul (H : Subgroup G) (g : G) :
    MulAction.orbitRel.Quotient H G → MulAction.orbitRel.Quotient H G :=
  Quotient.map' (· * g) fun _ _ ⟨h, hh⟩ =>
    ⟨h, by simpa [Subgroup.smul_def, mul_assoc] using congrArg (· * g) hh⟩

@[simp]
theorem rightCosetMul_mk (H : Subgroup G) (g x : G) :
    rightCosetMul H g (Quotient.mk'' x) = Quotient.mk'' (x * g) := by
  rfl

/-- Right translation of a right coset `q` agrees with multiplying its chosen representative `q.out`
on the right. -/
theorem rightCosetMul_eq_mk_out_mul (H : Subgroup G) (g : G)
    (q : MulAction.orbitRel.Quotient H G) :
    rightCosetMul H g q = Quotient.mk'' (q.out * g) := by
  conv_lhs => rw [← Quotient.out_eq' q]
  rfl

@[simp]
theorem rightCosetMul_one (H : Subgroup G) (q : MulAction.orbitRel.Quotient H G) :
    rightCosetMul H 1 q = q := by
  induction q using Quotient.inductionOn' with | h x => simp

@[simp]
theorem rightCosetMul_mul (H : Subgroup G) (g₁ g₂ : G) (q : MulAction.orbitRel.Quotient H G) :
    rightCosetMul H g₂ (rightCosetMul H g₁ q) = rightCosetMul H (g₁ * g₂) q := by
  induction q using Quotient.inductionOn' with | h x =>
    simp [mul_assoc]

/-- Right translation on `H \ G` as a homeomorphism. -/
def rightCosetMulHomeomorph [TopologicalSpace G] [ContinuousMul G] (H : Subgroup G) (g : G) :
    MulAction.orbitRel.Quotient H G ≃ₜ MulAction.orbitRel.Quotient H G where
  toFun := rightCosetMul H g
  invFun := rightCosetMul H g⁻¹
  left_inv q := by simp
  right_inv q := by simp
  continuous_toFun :=
    isQuotientMap_quotient_mk'.continuous_iff.mpr <|
      continuous_quot_mk.comp (continuous_mul_const g)
  continuous_invFun :=
    isQuotientMap_quotient_mk'.continuous_iff.mpr <|
      continuous_quot_mk.comp (continuous_mul_const g⁻¹)

@[simp]
theorem rightCosetMulHomeomorph_apply [TopologicalSpace G] [ContinuousMul G]
    (H : Subgroup G) (g : G) (q : MulAction.orbitRel.Quotient H G) :
    rightCosetMulHomeomorph H g q = rightCosetMul H g q := by
  rfl

@[simp]
theorem rightCosetMulHomeomorph_symm_apply [TopologicalSpace G] [ContinuousMul G]
    (H : Subgroup G) (g : G) (q : MulAction.orbitRel.Quotient H G) :
    (rightCosetMulHomeomorph H g).symm q = rightCosetMul H g⁻¹ q := by
  rfl

@[fun_prop]
theorem continuous_rightCosetMul [TopologicalSpace G] [ContinuousMul G]
    (H : Subgroup G) (g : G) :
    Continuous (rightCosetMul H g) :=
  (rightCosetMulHomeomorph H g).continuous

/-- Equivalence `H \ G ≃ G ⧸ H` induced by inversion `H g ↦ g⁻¹ H`. -/
def rightCosetEquivLeftCoset (H : Subgroup G) :
    MulAction.orbitRel.Quotient H G ≃ G ⧸ H where
  toFun := Quotient.lift (fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ H)) fun x y ⟨h, hh⟩ => by
    have hxy : (h : G) * y = x := hh
    apply QuotientGroup.eq.mpr
    have : x * y⁻¹ = (h : G) := by
      rw [← hxy]
      group
    simp [this]
  invFun := Quotient.lift (fun g : G => (Quotient.mk'' g⁻¹ : MulAction.orbitRel.Quotient H G))
    fun x y hxy => by
      have hmem : x⁻¹ * y ∈ H := QuotientGroup.leftRel_apply.mp hxy
      apply Quotient.sound'
      exact ⟨⟨x⁻¹ * y, hmem⟩, by change (x⁻¹ * y) * y⁻¹ = x⁻¹; group⟩
  left_inv q := by
    induction q using Quotient.inductionOn' with | h g => simp
  right_inv q := by
    induction q using QuotientGroup.induction_on with | H g => simp

@[simp]
theorem rightCosetEquivLeftCoset_mk (H : Subgroup G) (g : G) :
    rightCosetEquivLeftCoset H (Quotient.mk'' g) = (QuotientGroup.mk g⁻¹ : G ⧸ H) := by
  rfl

@[simp]
theorem rightCosetEquivLeftCoset_symm_mk (H : Subgroup G) (g : G) :
    (rightCosetEquivLeftCoset H).symm (QuotientGroup.mk g : G ⧸ H) = Quotient.mk'' g⁻¹ := by
  rfl

/-- Inversion intertwines right translation by `g` on `H \ G` with left translation by `g⁻¹` on
`G ⧸ H`. -/
theorem rightCosetEquivLeftCoset_rightCosetMul (H : Subgroup G) (g : G)
    (q : MulAction.orbitRel.Quotient H G) :
    rightCosetEquivLeftCoset H (rightCosetMul H g q) =
      g⁻¹ • rightCosetEquivLeftCoset H q := by
  induction q using Quotient.inductionOn' with | h x =>
    rw [rightCosetMul_mk, rightCosetEquivLeftCoset_mk, rightCosetEquivLeftCoset_mk, mul_inv_rev]
    rfl

/-- Inversion `H g ↦ g⁻¹ H` is a homeomorphism `H \ G ≃ₜ G ⧸ H` whenever inversion on `G` is
continuous. -/
def rightCosetHomeomorphLeftCoset [TopologicalSpace G] [ContinuousInv G] (H : Subgroup G) :
    MulAction.orbitRel.Quotient H G ≃ₜ G ⧸ H where
  toEquiv := rightCosetEquivLeftCoset H
  continuous_toFun :=
    isQuotientMap_quotient_mk'.continuous_iff.mpr <|
      QuotientGroup.continuous_mk.comp continuous_inv
  continuous_invFun :=
    (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr <|
      continuous_quot_mk.comp continuous_inv

@[simp]
theorem rightCosetHomeomorphLeftCoset_toEquiv [TopologicalSpace G] [ContinuousInv G]
    (H : Subgroup G) :
    (rightCosetHomeomorphLeftCoset H).toEquiv = rightCosetEquivLeftCoset H := by
  rfl

@[simp]
theorem rightCosetHomeomorphLeftCoset_mk [TopologicalSpace G] [ContinuousInv G]
    (H : Subgroup G) (g : G) :
    rightCosetHomeomorphLeftCoset H (Quotient.mk'' g) = (QuotientGroup.mk g⁻¹ : G ⧸ H) := by
  rfl

@[simp]
theorem rightCosetHomeomorphLeftCoset_symm_mk [TopologicalSpace G] [ContinuousInv G]
    (H : Subgroup G) (g : G) :
    (rightCosetHomeomorphLeftCoset H).symm (QuotientGroup.mk g : G ⧸ H) = Quotient.mk'' g⁻¹ := by
  rfl

/-- Internal helper extracting Hausdorffness of `H \ G` from Mathlib's
`t2Space_quotient_mulAction_of_properSMul`. -/
private theorem t2Space_rightCoset_of_isClosed [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsClosed (H : Set G)) :
    T2Space (MulAction.orbitRel.Quotient H G) := by
  have : IsClosed (H : Set G) := hH
  exact t2Space_quotient_mulAction_of_properSMul

/-- Internal helper extracting local compactness of `H \ G` from Mathlib's
`IsOpenQuotientMap.locallyCompactSpace`. -/
private theorem locallyCompactSpace_rightCoset [TopologicalSpace G] [ContinuousMul G]
    [LocallyCompactSpace G] (H : Subgroup G) :
    LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
  (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace

end RightCosetSpace

/-! ### Right Haar measures and the modular character -/

section RightHaar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- The inverse of a right Haar measure is a left Haar measure. -/
private theorem isHaarMeasure_inv_of_isMulRightInvariant (μ : Measure G)
    [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] :
    μ.inv.IsHaarMeasure := by
  have : IsFiniteMeasureOnCompacts μ.inv :=
    { lt_top_of_isCompact K hK := by
        rw [Measure.inv_apply]
        exact hK.inv.measure_lt_top }
  have : μ.inv.IsOpenPosMeasure :=
    { open_pos U hUo hUne := by
        rw [Measure.inv_apply]
        exact hUo.inv.measure_ne_zero μ hUne.inv }
  exact ⟨⟩

/-- Regularity is preserved under inversion of a measure on a topological group. -/
private theorem regular_inv_of_regular (μ : Measure G) [hμ : μ.Regular] : μ.inv.Regular := by
  rw [Measure.inv_def]
  exact hμ.map (Homeomorph.inv G)

/-- Left translation of a compactly supported continuous integrand against a right Haar measure
multiplies the integral by `Measure.modularCharacter g⁻¹`. -/
private theorem integral_mul_left_eq_modularCharacter_inv_smul [LocallyCompactSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {f : G → E} (hf : Continuous f) (hfc : HasCompactSupport f) (g : G) :
    ∫ x, f (g * x) ∂μ = (Measure.modularCharacter g⁻¹ : ℝ) • ∫ x, f x ∂μ := by
  have : μ.inv.IsHaarMeasure := isHaarMeasure_inv_of_isMulRightInvariant μ
  have h1 : ∫ x, f (g * x) ∂μ = ∫ y, f ((y * g⁻¹)⁻¹) ∂μ.inv := by
    rw [integral_inv_measure]
    congr 1 with y
    simp [mul_inv_rev]
  have h2 : ∫ x, f x ∂μ = ∫ y, f y⁻¹ ∂μ.inv := by
    rw [integral_inv_measure]
    simp
  rw [h1, h2]
  exact integral_mul_right_eq_modularCharacter_smul (μ := μ.inv) (hf.comp continuous_inv)
    (hfc.comp_homeomorph (Homeomorph.inv G)) g⁻¹

/-- Inversion formula for a right Haar measure: weighting by `Measure.modularCharacter x⁻¹` makes
inversion preserve the integral of a compactly supported continuous function. -/
private theorem integral_modularCharacter_inv_smul_inv_eq_self [LocallyCompactSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {f : G → E} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ x, (Measure.modularCharacter x⁻¹ : ℝ) • f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  have : μ.inv.IsHaarMeasure := isHaarMeasure_inv_of_isMulRightInvariant μ
  have h1 : ∫ x, (Measure.modularCharacter x⁻¹ : ℝ) • f x⁻¹ ∂μ =
      ∫ y, (Measure.modularCharacter y : ℝ) • f y ∂μ.inv := by
    rw [integral_inv_measure]
  have h2 : ∫ x, f x ∂μ = ∫ y, f y⁻¹ ∂μ.inv := by
    rw [integral_inv_measure]
    simp
  rw [h1, h2]
  exact (integral_inv_eq_integral_modularCharacter_smul (μ := μ.inv) hf hfc).symm

/-- Any regular right-invariant measure is a nonnegative scalar multiple of a regular right Haar
measure. -/
private theorem isMulRightInvariant_eq_smul_of_regular [LocallyCompactSpace G] (μ' μ : Measure G)
    [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] [μ.Regular]
    [μ'.IsMulRightInvariant] [μ'.Regular] :
    ∃ c : ℝ≥0, μ' = c • μ := by
  have : μ.inv.IsHaarMeasure := isHaarMeasure_inv_of_isMulRightInvariant μ
  have : μ.inv.Regular := regular_inv_of_regular μ
  have : μ'.inv.Regular := regular_inv_of_regular μ'
  refine ⟨Measure.haarScalarFactor μ'.inv μ.inv, ?_⟩
  have h := Measure.isMulLeftInvariant_eq_smul_of_regular μ'.inv μ.inv
  have hinv := congrArg Measure.inv h
  rw [Measure.inv_inv, Measure.inv_def, Measure.map_smul, ← Measure.inv_def,
    Measure.inv_inv] at hinv
  · exact hinv
  · exact continuous_inv.aemeasurable

end RightHaar

/-! ### Orbit averaging on `C_c(G, ℝ)` -/

section QuotientAverage

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For a closed subgroup `H` and compact sets `K, U ⊆ G`, the preimage of `K * U⁻¹` in `H` is
compact. -/
private lemma isCompact_preimage_mul_inv {H : Subgroup G} (hH : IsClosed (H : Set G))
    {K U : Set G} (hK : IsCompact K) (hU : IsCompact U) :
    IsCompact (((↑) : H → G) ⁻¹' (K * U⁻¹)) :=
  hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.mul hU.inv)

/-- For compactly supported continuous `f : G → ℝ` and a closed subgroup `H`, each fiber
`h ↦ f (h * g)` has compact support in `H`. -/
private lemma hasCompactSupport_mul_right_subgroup {H : Subgroup G} (hH : IsClosed (H : Set G))
    {f : G → ℝ} (hfc : HasCompactSupport f) (g : G) :
    HasCompactSupport fun h : H => f ((h : G) * g) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_preimage_mul_inv hH hfc isCompact_singleton (U := {g})) fun h hh => ?_
  have hmem : (h : G) * g ∈ tsupport f := subset_tsupport f hh
  exact ⟨(h : G) * g, hmem, g⁻¹, by simp, by group⟩

/-- Continuity of the fiber integral `g ↦ ∫ h : H, f (h * g) ∂μH` for compactly supported
continuous `f`. -/
private lemma continuous_integral_mul_subgroup [LocallyCompactSpace G]
    {H : Subgroup G} (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [IsFiniteMeasureOnCompacts μH]
    {f : G → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous fun g : G => ∫ h : H, f ((h : G) * g) ∂μH := by
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds g₀
  have hKH : IsCompact (((↑) : H → G) ⁻¹' (tsupport f * U⁻¹)) :=
    isCompact_preimage_mul_inv hH hfc hUc
  have hcontOn : ContinuousOn (fun g : G => ∫ h : H, f ((h : G) * g) ∂μH) U := by
    refine continuousOn_integral_of_compact_support hKH ?_ ?_
    · exact (hf.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)).continuousOn
    · intro g h hg hh
      contrapose! hh
      exact ⟨(h : G) * g, subset_tsupport f hh, g⁻¹, Set.inv_mem_inv.mpr hg, by group⟩
  exact hcontOn.continuousAt hU

/-- Orbit averaging along a closed subgroup `H` with respect to a right-invariant locally finite
measure `μH`, as a positive linear map `C_c(G, ℝ) →ₚ[ℝ] C_c(H \ G, ℝ)`. -/
noncomputable def quotientAverage [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] :
    C_c(G, ℝ) →ₚ[ℝ] C_c(MulAction.orbitRel.Quotient H G, ℝ) :=
  PositiveLinearMap.mk₀
    { toFun := fun f =>
        { toFun := Quotient.lift (fun g : G => ∫ h : H, f ((h : G) * g) ∂μH) fun x y ⟨h₀, hh₀⟩ => by
            have hxy : (h₀ : G) * y = x := hh₀
            rw [← hxy]
            simpa [mul_assoc] using
              integral_mul_right_eq_self (fun h : H => f ((h : G) * y)) h₀ (μ := μH)
          continuous_toFun :=
            isQuotientMap_quotient_mk'.continuous_iff.mpr
              (continuous_integral_mul_subgroup hH μH f.continuous f.hasCompactSupport)
          hasCompactSupport' := by
            have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
            refine HasCompactSupport.of_support_subset_isCompact
              (f.hasCompactSupport.image continuous_quot_mk) ?_
            intro q hq
            induction q using Quotient.inductionOn' with | h g =>
              change (∫ h : H, f ((h : G) * g) ∂μH) ≠ 0 at hq
              have hex : ∃ h : H, f ((h : G) * g) ≠ 0 := by
                by_contra hall
                push Not at hall
                exact hq (by simp [hall])
              obtain ⟨h, hh⟩ := hex
              refine ⟨(h : G) * g, subset_tsupport f hh, ?_⟩
              exact Quotient.sound' ⟨h, rfl⟩ }
      map_add' := fun f₁ f₂ => by
        ext q
        induction q using Quotient.inductionOn' with | h g =>
          change ∫ h : H, (f₁ ((h : G) * g) + f₂ ((h : G) * g)) ∂μH =
            (∫ h : H, f₁ ((h : G) * g) ∂μH) + ∫ h : H, f₂ ((h : G) * g) ∂μH
          have hi₁ : Integrable (fun h : H => f₁ ((h : G) * g)) μH :=
            (f₁.continuous.comp
              (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
              (hasCompactSupport_mul_right_subgroup hH f₁.hasCompactSupport g)
          have hi₂ : Integrable (fun h : H => f₂ ((h : G) * g)) μH :=
            (f₂.continuous.comp
              (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
              (hasCompactSupport_mul_right_subgroup hH f₂.hasCompactSupport g)
          exact integral_add hi₁ hi₂
      map_smul' := fun c f => by
        ext q
        induction q using Quotient.inductionOn' with | h g =>
          change ∫ h : H, c * f ((h : G) * g) ∂μH = c * ∫ h : H, f ((h : G) * g) ∂μH
          exact integral_const_mul c _ }
    fun f hf q => by
      induction q using Quotient.inductionOn' with | h g =>
        change 0 ≤ ∫ h : H, f ((h : G) * g) ∂μH
        exact integral_nonneg fun h => hf ((h : G) * g)

@[simp]
theorem quotientAverage_mk [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    (f : C_c(G, ℝ)) (g : G) :
    quotientAverage H hH μH f (Quotient.mk'' g) = ∫ h : H, f ((h : G) * g) ∂μH := by
  rfl

/-- Evaluating `quotientAverage` at a coset `q` integrates `f` along `H * q.out`. -/
theorem quotientAverage_apply [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    (f : C_c(G, ℝ)) (q : MulAction.orbitRel.Quotient H G) :
    quotientAverage H hH μH f q = ∫ h : H, f ((h : G) * q.out) ∂μH := by
  conv_lhs => rw [← Quotient.out_eq' q]
  rfl

/-- The support of `quotientAverage H hH μH f` lies in the image of `tsupport f`. -/
theorem tsupport_quotientAverage_subset [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    (f : C_c(G, ℝ)) :
    tsupport (quotientAverage H hH μH f) ⊆
      (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' tsupport f := by
  have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  have hcomp : IsCompact ((Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' tsupport f) :=
    f.hasCompactSupport.image continuous_quot_mk
  refine closure_minimal ?_ hcomp.isClosed
  intro q hq
  induction q using Quotient.inductionOn' with | h g =>
    change (∫ h : H, f ((h : G) * g) ∂μH) ≠ 0 at hq
    have hex : ∃ h : H, f ((h : G) * g) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hq (by simp [hall])
    obtain ⟨h, hh⟩ := hex
    exact ⟨(h : G) * g, subset_tsupport f hh, Quotient.sound' ⟨h, rfl⟩⟩

/-- Orbit averaging commutes with right translation by `g : G`. -/
theorem quotientAverage_comp_mulRight [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    (f : C_c(G, ℝ)) (g : G) (q : MulAction.orbitRel.Quotient H G) :
    quotientAverage H hH μH
      ⟨⟨fun x => f (x * g), f.continuous.comp (continuous_mul_const g)⟩,
        f.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight g)⟩ q =
      quotientAverage H hH μH f (rightCosetMul H g q) := by
  induction q using Quotient.inductionOn' with | h x =>
    simp only [quotientAverage_mk, rightCosetMul_mk]
    change ∫ h : H, f ((h : G) * x * g) ∂μH = ∫ h : H, f ((h : G) * (x * g)) ∂μH
    congr 1 with h
    rw [mul_assoc]

/-- **Surjectivity of orbit averaging**: every `φ ∈ C_c(H \ G, ℝ)` lifts to some `f ∈ C_c(G, ℝ)`
with `quotientAverage H hH μH f = φ`, and nonnegative `φ` admits a nonnegative lift `f`. -/
theorem exists_quotientAverage_eq [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure] (φ : C_c(MulAction.orbitRel.Quotient H G, ℝ)) :
    ∃ f : C_c(G, ℝ), quotientAverage H hH μH f = φ ∧ (0 ≤ φ → 0 ≤ f) := by
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  -- Lift the compact support of `φ` to a compact subset `D ⊆ G`.
  have hrange : tsupport (φ : MulAction.orbitRel.Quotient H G → ℝ) ⊆
      Set.range (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) := fun q _ =>
    ⟨q.out, Quotient.out_eq' q⟩
  obtain ⟨D, hDc, hDcover⟩ :=
    (isOpenMap_quotient_mk'_mul (Γ := H) (T := G)).exists_isCompact_subset_image
      φ.hasCompactSupport hrange
  -- Choose a compactly supported continuous `η ≥ 0` on `G` equal to `1` on `D`.
  obtain ⟨η₀, hη_one, hη_supp, -, hη_Icc⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hDc isOpen_univ (subset_univ D)
  let η : C_c(G, ℝ) := ⟨η₀, hη_supp⟩
  have hη_nonneg : ∀ x : G, 0 ≤ η x := fun x => (hη_Icc x).1
  let ψ : C_c(MulAction.orbitRel.Quotient H G, ℝ) := quotientAverage H hH μH η
  have hψ_nonneg : ∀ q, 0 ≤ ψ q := fun q => (quotientAverage H hH μH).map_nonneg hη_nonneg q
  -- On `tsupport φ`, the averaged cutoff `ψ` is strictly positive.
  have hψ_pos : ∀ q ∈ tsupport (φ : MulAction.orbitRel.Quotient H G → ℝ), 0 < ψ q := by
    intro q hq
    obtain ⟨g, hgD, rfl⟩ := hDcover hq
    change 0 < ∫ h : H, η ((h : G) * g) ∂μH
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (f := fun h : H => η ((h : G) * g))
      (η.continuous.comp (continuous_subtype_val.mul continuous_const))
      (hasCompactSupport_mul_right_subgroup hH η.hasCompactSupport g)
      (fun h => hη_nonneg _) (x := (1 : H)) ?_
    have h1g : η ((1 : H) * g) = 1 := by
      rw [OneMemClass.coe_one, one_mul]
      exact hη_one hgD
    rw [h1g]
    exact one_ne_zero
  -- Define `f(x) = φ(H x) * η(x) / ψ(H x)` where `ψ(H x) ≠ 0`, and `0` elsewhere.
  let f₀ : G → ℝ := fun x =>
    if ψ (Quotient.mk'' x) = 0 then 0 else φ (Quotient.mk'' x) * η x / ψ (Quotient.mk'' x)
  have hf₀_cont : Continuous f₀ := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : ψ (Quotient.mk'' x) = 0
    · have hx' : (Quotient.mk'' x : MulAction.orbitRel.Quotient H G) ∉ tsupport φ :=
        fun hmem => (hψ_pos _ hmem).ne' hx
      have hVopen : IsOpen ((Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) ⁻¹'
          (tsupport φ)ᶜ) :=
        (isClosed_tsupport (φ : MulAction.orbitRel.Quotient H G → ℝ)).isOpen_compl.preimage
          continuous_quot_mk
      have hev : f₀ =ᶠ[𝓝 x] 0 := by
        filter_upwards [hVopen.mem_nhds hx'] with y hy
        have hφy : φ (Quotient.mk'' y) = 0 := image_eq_zero_of_notMem_tsupport hy
        by_cases hψy : ψ (Quotient.mk'' y) = 0 <;> simp [f₀, hψy, hφy]
      exact continuousAt_const.congr hev.symm
    · have hUopen : IsOpen {y : G | ψ (Quotient.mk'' y) ≠ 0} :=
        isOpen_ne.preimage (ψ.continuous.comp continuous_quot_mk)
      have hev : f₀ =ᶠ[𝓝 x] fun y => φ (Quotient.mk'' y) * η y / ψ (Quotient.mk'' y) := by
        filter_upwards [hUopen.mem_nhds hx] with y hy
        simp [f₀, hy]
      have hca : ContinuousAt (fun y : G => φ (Quotient.mk'' y) * η y / ψ (Quotient.mk'' y)) x :=
        (((φ.continuous.comp continuous_quot_mk).continuousAt.mul η.continuous.continuousAt).div
          (ψ.continuous.comp continuous_quot_mk).continuousAt hx)
      exact hca.congr hev.symm
  have hf₀_supp : HasCompactSupport f₀ := by
    refine HasCompactSupport.of_support_subset_isCompact η.hasCompactSupport fun x hx => ?_
    apply subset_tsupport η
    intro hηx
    apply hx
    by_cases hψx : ψ (Quotient.mk'' x) = 0 <;> simp [f₀, hψx, hηx]
  refine ⟨⟨⟨f₀, hf₀_cont⟩, hf₀_supp⟩, ?_, ?_⟩
  · ext q
    induction q using Quotient.inductionOn' with | h g =>
      rw [quotientAverage_mk]
      change ∫ h : H, f₀ ((h : G) * g) ∂μH = φ (Quotient.mk'' g)
      have hmk : ∀ h : H, (Quotient.mk'' ((h : G) * g) : MulAction.orbitRel.Quotient H G) =
          Quotient.mk'' g := fun h => Quotient.sound' ⟨h, rfl⟩
      by_cases hψg : ψ (Quotient.mk'' g) = 0
      · have hg' : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G) ∉ tsupport φ :=
          fun hmem => (hψ_pos _ hmem).ne' hψg
        have hφg : φ (Quotient.mk'' g) = 0 := image_eq_zero_of_notMem_tsupport hg'
        simp [f₀, hmk, hψg, hφg]
      · have hrew : (fun h : H => f₀ ((h : G) * g)) =
            fun h : H => (φ (Quotient.mk'' g) / ψ (Quotient.mk'' g)) * η ((h : G) * g) := by
          ext h
          simp [f₀, hmk, hψg, mul_div_right_comm]
        rw [hrew, integral_const_mul]
        change (φ (Quotient.mk'' g) / ψ (Quotient.mk'' g)) * ψ (Quotient.mk'' g) =
          φ (Quotient.mk'' g)
        exact div_mul_cancel₀ _ hψg
  · intro hφ x
    change 0 ≤ f₀ x
    by_cases hψx : ψ (Quotient.mk'' x) = 0
    · simp [f₀, hψx]
    · simp only [f₀, hψx, ↓reduceIte]
      exact div_nonneg (mul_nonneg (hφ _) (hη_nonneg x)) (hψ_nonneg _)

/-- Orbit averaging `C_c(G, ℝ) → C_c(H \ G, ℝ)` is surjective. -/
theorem quotientAverage_surjective [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure] :
    Function.Surjective (quotientAverage H hH μH) :=
  fun φ => (exists_quotientAverage_eq H hH μH φ).imp fun _ hf => hf.1

end QuotientAverage

/-! ### Folland's averaging lemma and construction of `quotientMeasure` -/

section Construction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **Folland's averaging lemma** (Folland, §2.6, Lemma 2.48): if the modular characters of `G` and
`H` agree on `H`, and `f ∈ C_c(G, ℝ)` has nonnegative orbit average, then `0 ≤ ∫ g, f g ∂μG`. -/
theorem integral_nonneg_of_quotientAverage_nonneg (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : C_c(G, ℝ)} (hf : 0 ≤ quotientAverage H hH μH f) :
    0 ≤ ∫ g, f g ∂μG := by
  let : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  -- Pick `χ ∈ C_c(H \ G, ℝ)` with `0 ≤ χ` and `χ = 1` on the image of `tsupport f`.
  have hK : IsCompact ((Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' tsupport f) :=
    f.hasCompactSupport.image continuous_quot_mk
  obtain ⟨χ₀, hχ_one, hχ_supp, -, hχ_Icc⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ _)
  let χ : C_c(MulAction.orbitRel.Quotient H G, ℝ) := ⟨χ₀, hχ_supp⟩
  obtain ⟨η, hη_avg, hη_nonneg_imp⟩ := exists_quotientAverage_eq H hH μH χ
  have hη_nonneg : ∀ g : G, 0 ≤ η g := hη_nonneg_imp fun q => (hχ_Icc q).1
  -- Pointwise identity `f g = ∫ h : H, f g * η (h * g) ∂μH`.
  have hpoint : ∀ g : G, f g = ∫ h : H, f g * η ((h : G) * g) ∂μH := by
    intro g
    rw [integral_const_mul]
    change f g = f g * quotientAverage H hH μH η (Quotient.mk'' g)
    rw [hη_avg]
    by_cases hg : g ∈ tsupport f
    · have hmem : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G) ∈
          (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) '' tsupport f := ⟨g, hg, rfl⟩
      have h1 : χ (Quotient.mk'' g) = 1 := hχ_one hmem
      rw [h1, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hg]
  -- Common compact sets in `G` and `H` containing the supports of both two-variable integrands.
  let KG : Set G := tsupport f ∪ tsupport η
  have hKG : IsCompact KG := f.hasCompactSupport.union η.hasCompactSupport
  let KH : Set H := ((↑) : H → G) ⁻¹' (KG * KG⁻¹)
  have hKH : IsCompact KH := isCompact_preimage_mul_inv hH hKG hKG
  have hKH_symm : IsCompact (KH ∪ KH⁻¹) := hKH.union hKH.inv
  -- First Fubini swap: `∫ g, ∫ h, f g * η (h * g) = ∫ h, ∫ g, f g * η (h * g)`.
  have hswap₁ : ∫ g, (∫ h : H, f g * η ((h : G) * g) ∂μH) ∂μG =
      ∫ h : H, (∫ g, f g * η ((h : G) * g) ∂μG) ∂μH := by
    refine integral_integral_swap_of_hasCompactSupport
      (f := fun g (h : H) => f g * η ((h : G) * g)) ?_ ?_
    · exact (f.continuous.comp continuous_fst).mul
        (η.continuous.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst))
    · refine HasCompactSupport.of_support_subset_isCompact (hKG.prod hKH) fun p hp => ?_
      have h1 : f p.1 ≠ 0 := left_ne_zero_of_mul hp
      have h2 : η ((p.2 : G) * p.1) ≠ 0 := right_ne_zero_of_mul hp
      have hgKG : p.1 ∈ KG := Or.inl (subset_tsupport f h1)
      have hhgKG : (p.2 : G) * p.1 ∈ KG := Or.inr (subset_tsupport η h2)
      exact ⟨hgKG, ⟨(p.2 : G) * p.1, hhgKG, p.1⁻¹, Set.inv_mem_inv.mpr hgKG, by group⟩⟩
  -- Left-translate `g ↦ h * g` in the inner `G`-integral using the right-Haar modular character.
  have htrans : ∀ h : H,
      ∫ g, f g * η ((h : G) * g) ∂μG =
        (Measure.modularCharacter (G := G) (h : G)⁻¹ : ℝ) *
          ∫ g, f ((h : G)⁻¹ * g) * η g ∂μG := by
    intro h
    let Fh : G → ℝ := fun g => f ((h : G)⁻¹ * g) * η g
    have hFh_cont : Continuous Fh :=
      (f.continuous.comp (continuous_const_mul _)).mul η.continuous
    have hFh_supp : HasCompactSupport Fh := η.hasCompactSupport.mul_left
    have heq : (fun g => f g * η ((h : G) * g)) = fun g => Fh ((h : G) * g) := by
      ext g
      simp [Fh]
    rw [heq]
    simpa [smul_eq_mul] using
      integral_mul_left_eq_modularCharacter_inv_smul μG hFh_cont hFh_supp (h : G)
  -- Second Fubini swap back to `G` outer, `H` inner.
  have hswap₂ :
      ∫ h : H, (Measure.modularCharacter (G := G) (h : G)⁻¹ : ℝ) *
          (∫ g, f ((h : G)⁻¹ * g) * η g ∂μG) ∂μH =
        ∫ g, (∫ h : H, (Measure.modularCharacter (G := G) (h : G)⁻¹ : ℝ) *
          (f ((h : G)⁻¹ * g) * η g) ∂μH) ∂μG := by
    simp_rw [← integral_const_mul]
    symm
    refine integral_integral_swap_of_hasCompactSupport
      (f := fun g (h : H) => (Measure.modularCharacter (G := G) (h : G)⁻¹ : ℝ) *
        (f ((h : G)⁻¹ * g) * η g)) ?_ ?_
    · exact ((NNReal.continuous_coe.comp continuous_modularCharacter).comp
        (continuous_subtype_val.comp continuous_snd).inv).mul
        ((f.continuous.comp
          ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst)).mul
          (η.continuous.comp continuous_fst))
    · refine HasCompactSupport.of_support_subset_isCompact (hKG.prod hKH_symm) fun p hp => ?_
      have h2 : f ((p.2 : G)⁻¹ * p.1) * η p.1 ≠ 0 := right_ne_zero_of_mul hp
      have hf1 : f ((p.2 : G)⁻¹ * p.1) ≠ 0 := left_ne_zero_of_mul h2
      have hη1 : η p.1 ≠ 0 := right_ne_zero_of_mul h2
      have hgKG : p.1 ∈ KG := Or.inr (subset_tsupport η hη1)
      have hhgKG : (p.2 : G)⁻¹ * p.1 ∈ KG := Or.inl (subset_tsupport f hf1)
      refine ⟨hgKG, Or.inr ?_⟩
      change ((p.2⁻¹ : H) : G) ∈ KG * KG⁻¹
      exact ⟨(p.2 : G)⁻¹ * p.1, hhgKG, p.1⁻¹, Set.inv_mem_inv.mpr hgKG, by simp [mul_assoc]⟩
  -- Apply the modular-character hypothesis and right-Haar inversion on `H`.
  have hinv_inner : ∀ g : G,
      ∫ h : H, (Measure.modularCharacter (G := G) (h : G)⁻¹ : ℝ) *
          (f ((h : G)⁻¹ * g) * η g) ∂μH =
        η g * quotientAverage H hH μH f (Quotient.mk'' g) := by
    intro g
    have hpull : (fun h : H => (Measure.modularCharacter (G := G) (h : G)⁻¹ : ℝ) *
        (f ((h : G)⁻¹ * g) * η g)) =
        fun h : H => η g * ((Measure.modularCharacter (G := H) h⁻¹ : ℝ) *
          f (((h⁻¹ : H) : G) * g)) := by
      ext h
      have hmod' : Measure.modularCharacter (G := G) (h : G)⁻¹ =
          Measure.modularCharacter (G := H) h⁻¹ := by
        simpa [Subgroup.coe_inv] using hmod h⁻¹
      rw [hmod']
      simp
      ring
    rw [hpull, integral_const_mul, quotientAverage_mk]
    congr 1
    simpa [smul_eq_mul] using
      integral_modularCharacter_inv_smul_inv_eq_self μH (f := fun h : H => f ((h : G) * g))
        (f.continuous.comp (continuous_subtype_val.mul continuous_const))
        (hasCompactSupport_mul_right_subgroup hH f.hasCompactSupport g)
  -- Assemble the identity `∫ f dμG = ∫ η * (P f ∘ mk) dμG ≥ 0`.
  have heq : ∫ g, f g ∂μG = ∫ g, η g * quotientAverage H hH μH f (Quotient.mk'' g) ∂μG := by
    calc ∫ g, f g ∂μG
        = ∫ g, (∫ h : H, f g * η ((h : G) * g) ∂μH) ∂μG := by simp_rw [← hpoint]
      _ = ∫ h : H, (∫ g, f g * η ((h : G) * g) ∂μG) ∂μH := hswap₁
      _ = ∫ h : H, (Measure.modularCharacter (G := G) (h : G)⁻¹ : ℝ) *
            (∫ g, f ((h : G)⁻¹ * g) * η g ∂μG) ∂μH := by simp_rw [htrans]
      _ = ∫ g, (∫ h : H, (Measure.modularCharacter (G := G) (h : G)⁻¹ : ℝ) *
            (f ((h : G)⁻¹ * g) * η g) ∂μH) ∂μG := hswap₂
      _ = ∫ g, η g * quotientAverage H hH μH f (Quotient.mk'' g) ∂μG := by simp_rw [hinv_inner]
  rw [heq]
  exact integral_nonneg fun g => mul_nonneg (hη_nonneg g) (hf (Quotient.mk'' g))

/-- If two compactly supported continuous functions on `G` have the same orbit average along `H`,
they have the same integral against `μG`. -/
theorem integral_eq_of_quotientAverage_eq (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f₁ f₂ : C_c(G, ℝ)} (h : quotientAverage H hH μH f₁ = quotientAverage H hH μH f₂) :
    ∫ g, f₁ g ∂μG = ∫ g, f₂ g ∂μG := by
  have hle : ∀ {a b : C_c(G, ℝ)},
      quotientAverage H hH μH a ≤ quotientAverage H hH μH b →
      ∫ g, a g ∂μG ≤ ∫ g, b g ∂μG := by
    intro a b hab
    have h0 : 0 ≤ quotientAverage H hH μH (b - a) := by
      rw [map_sub]
      exact sub_nonneg.mpr hab
    have hi := integral_nonneg_of_quotientAverage_nonneg H hH μG μH hmod h0
    have hsub : ∫ g, (b - a) g ∂μG = (∫ g, b g ∂μG) - ∫ g, a g ∂μG :=
      integral_sub b.integrable a.integrable
    linarith
  exact le_antisymm (hle h.le) (hle h.ge)

/-- The positive linear functional on `C_c(H \ G, ℝ)` induced by `f ↦ ∫ g, f g ∂μG` via
orbit averaging. -/
noncomputable def quotientFunctional (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    C_c(MulAction.orbitRel.Quotient H G, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun φ => ∫ g, (quotientAverage_surjective H hH μH φ).choose g ∂μG
      map_add' := fun φ₁ φ₂ => by
        let f₁ := (quotientAverage_surjective H hH μH φ₁).choose
        let f₂ := (quotientAverage_surjective H hH μH φ₂).choose
        have hf₁ : quotientAverage H hH μH f₁ = φ₁ :=
          (quotientAverage_surjective H hH μH φ₁).choose_spec
        have hf₂ : quotientAverage H hH μH f₂ = φ₂ :=
          (quotientAverage_surjective H hH μH φ₂).choose_spec
        have hsum : quotientAverage H hH μH (f₁ + f₂) = φ₁ + φ₂ := by
          rw [map_add, hf₁, hf₂]
        have heq := integral_eq_of_quotientAverage_eq H hH μG μH hmod
          ((quotientAverage_surjective H hH μH (φ₁ + φ₂)).choose_spec.trans hsum.symm)
        exact heq.trans (integral_add f₁.integrable f₂.integrable)
      map_smul' := fun c φ => by
        let f := (quotientAverage_surjective H hH μH φ).choose
        have hf : quotientAverage H hH μH f = φ :=
          (quotientAverage_surjective H hH μH φ).choose_spec
        have hsmul : quotientAverage H hH μH (c • f) = c • φ := by
          rw [map_smul, hf]
        have heq := integral_eq_of_quotientAverage_eq H hH μG μH hmod
          ((quotientAverage_surjective H hH μH (c • φ)).choose_spec.trans hsmul.symm)
        exact heq.trans (integral_const_mul c _) }
    fun φ hφ => by
      apply integral_nonneg_of_quotientAverage_nonneg H hH μG μH hmod
      rw [(quotientAverage_surjective H hH μH φ).choose_spec]
      exact hφ

@[simp]
theorem quotientFunctional_quotientAverage (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    (f : C_c(G, ℝ)) :
    quotientFunctional H hH μG μH hmod (quotientAverage H hH μH f) = ∫ g, f g ∂μG :=
  integral_eq_of_quotientAverage_eq H hH μG μH hmod
    (quotientAverage_surjective H hH μH (quotientAverage H hH μH f)).choose_spec

/-- **Weil's quotient measure** on the right-coset space `H \ G`, constructed via the
Riesz–Markov–Kakutani representation theorem from `quotientFunctional`. -/
noncomputable def quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    Measure (MulAction.orbitRel.Quotient H G) :=
  letI : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  letI : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  RealRMK.rieszMeasure (quotientFunctional H hH μG μH hmod)

/-- `quotientMeasure` is a regular Borel measure on `H \ G`. -/
theorem regular_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    (quotientMeasure H hH μG μH hmod).Regular := by
  let : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  exact RealRMK.regular_rieszMeasure (quotientFunctional H hH μG μH hmod)

/-- `quotientMeasure` is finite on compact subsets of `H \ G`. -/
theorem isFiniteMeasureOnCompacts_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    IsFiniteMeasureOnCompacts (quotientMeasure H hH μG μH hmod) := by
  have := regular_quotientMeasure H hH μG μH hmod
  infer_instance

/-- `quotientMeasure` gives positive measure to every nonempty open subset of `H \ G`. -/
theorem isOpenPosMeasure_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    (quotientMeasure H hH μG μH hmod).IsOpenPosMeasure := by
  let : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  refine ⟨fun U hU ⟨q, hq⟩ hzero => ?_⟩
  obtain ⟨φ₀, hφ_one, hφ_supp, hφU, hφ_Icc⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton hU
      (singleton_subset_iff.mpr hq)
  let φ : C_c(MulAction.orbitRel.Quotient H G, ℝ) := ⟨φ₀, hφ_supp⟩
  obtain ⟨f, hf_avg, hf_nn⟩ := exists_quotientAverage_eq H hH μH φ
  have hf0 : ∀ g, 0 ≤ f g := hf_nn fun x => (hφ_Icc x).1
  have hf_ne : ∃ g : G, f g ≠ 0 := by
    by_contra hall
    push Not at hall
    have hq0 : φ q = 0 := by
      rw [← hf_avg, quotientAverage_apply]
      simp [hall]
    have hq1 : φ q = 1 := hφ_one rfl
    linarith
  obtain ⟨g₀, hg₀⟩ := hf_ne
  have hpos : 0 < ∫ g, f g ∂μG :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero f.hasCompactSupport hf0 hg₀
  have hint_eq : ∫ x, φ x ∂(quotientMeasure H hH μG μH hmod) = ∫ g, f g ∂μG := by
    rw [show ∫ x, φ x ∂(quotientMeasure H hH μG μH hmod) =
        quotientFunctional H hH μG μH hmod φ from
      RealRMK.integral_rieszMeasure (quotientFunctional H hH μG μH hmod) φ,
      ← hf_avg, quotientFunctional_quotientAverage]
  have hφ_ae0 : (fun x => φ x) =ᵐ[quotientMeasure H hH μG μH hmod] fun _ => 0 := by
    filter_upwards [compl_mem_ae_iff.mpr hzero] with x hx
    exact image_eq_zero_of_notMem_tsupport fun hmem => hx (hφU hmem)
  have hint0 : ∫ x, φ x ∂(quotientMeasure H hH μG μH hmod) = 0 := by
    rw [integral_congr_ae hφ_ae0, integral_zero]
  linarith

/-- Integration against `quotientMeasure` evaluates `quotientFunctional` on every
`φ ∈ C_c(H \ G, ℝ)`. -/
theorem integral_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    (φ : C_c(MulAction.orbitRel.Quotient H G, ℝ)) :
    ∫ q, φ q ∂(quotientMeasure H hH μG μH hmod) = quotientFunctional H hH μG μH hmod φ := by
  let : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  exact RealRMK.integral_rieszMeasure (quotientFunctional H hH μG μH hmod) φ

/-- **Weil's integration formula** for compactly supported continuous functions on `G`. -/
theorem integral_eq_integral_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : G → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ g, f g ∂μG =
      ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂(quotientMeasure H hH μG μH hmod) := by
  let F : C_c(G, ℝ) := ⟨⟨f, hf⟩, hfc⟩
  have h1 := integral_quotientMeasure H hH μG μH hmod (quotientAverage H hH μH F)
  rw [quotientFunctional_quotientAverage] at h1
  calc ∫ g, f g ∂μG = ∫ g, F g ∂μG := rfl
    _ = ∫ q, quotientAverage H hH μH F q ∂(quotientMeasure H hH μG μH hmod) := h1.symm
    _ = ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂(quotientMeasure H hH μG μH hmod) := by
        congr 1 with q
        exact quotientAverage_apply H hH μH F q

/-- `quotientMeasure` is right-`G`-invariant under `rightCosetMul H g`. -/
theorem map_rightCosetMul_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) (g : G) :
    Measure.map (rightCosetMul H g) (quotientMeasure H hH μG μH hmod) =
      quotientMeasure H hH μG μH hmod := by
  let : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  have hreg : (quotientMeasure H hH μG μH hmod).Regular :=
    regular_quotientMeasure H hH μG μH hmod
  have : (Measure.map (rightCosetMul H g) (quotientMeasure H hH μG μH hmod)).Regular :=
    hreg.map (rightCosetMulHomeomorph H g)
  refine Measure.ext_of_integral_eq_on_compactlySupported fun φ => ?_
  obtain ⟨f, rfl⟩ := quotientAverage_surjective H hH μH φ
  rw [integral_map (f := fun q => quotientAverage H hH μH f q)
    (continuous_rightCosetMul H g).aemeasurable
    (quotientAverage H hH μH f).continuous.aestronglyMeasurable]
  simp_rw [← quotientAverage_comp_mulRight H hH μH f g]
  rw [integral_quotientMeasure, quotientFunctional_quotientAverage,
    integral_quotientMeasure, quotientFunctional_quotientAverage]
  exact integral_mul_right_eq_self (f : G → ℝ) g

/-- Uniqueness of `quotientMeasure` among regular Borel measures on `H \ G` satisfying Weil's
integration formula, without requiring second countability. -/
theorem quotientMeasure_eq_of_regular (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {ν : Measure (MulAction.orbitRel.Quotient H G)} [ν.Regular]
    (hν : ∀ f : G → ℝ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μG = ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂ν) :
    ν = quotientMeasure H hH μG μH hmod := by
  let : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  have : (quotientMeasure H hH μG μH hmod).Regular :=
    regular_quotientMeasure H hH μG μH hmod
  refine Measure.ext_of_integral_eq_on_compactlySupported fun φ => ?_
  obtain ⟨f, rfl⟩ := quotientAverage_surjective H hH μH φ
  rw [integral_quotientMeasure, quotientFunctional_quotientAverage]
  simpa only [quotientAverage_apply] using (hν f f.continuous f.hasCompactSupport).symm

/-- **Weil's quotient measure theorem**: for right Haar measures on a second countable locally
compact group `G` and on a closed subgroup `H` with matching modular characters, there is a unique
right-`G`-invariant measure on `H \ G` finite on compact sets satisfying Weil's integration formula
for all compactly supported continuous `f : G → ℝ`. -/
theorem exists_unique_quotientMeasure [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    ∃! ν : Measure (MulAction.orbitRel.Quotient H G), IsFiniteMeasureOnCompacts ν ∧
      (∀ g : G, Measure.map (fun q : MulAction.orbitRel.Quotient H G =>
        (Quotient.mk'' (q.out * g) : MulAction.orbitRel.Quotient H G)) ν = ν) ∧
      ∀ f : G → ℝ, Continuous f → HasCompactSupport f →
        ∫ g, f g ∂μG = ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂ν := by
  let : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  let : SecondCountableTopology (MulAction.orbitRel.Quotient H G) :=
    ContinuousConstSMul.secondCountableTopology
  let : T3Space (MulAction.orbitRel.Quotient H G) := inferInstance
  let : TopologicalSpace.MetrizableSpace (MulAction.orbitRel.Quotient H G) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  refine ⟨quotientMeasure H hH μG μH hmod, ?_, ?_⟩
  · refine ⟨isFiniteMeasureOnCompacts_quotientMeasure H hH μG μH hmod, fun g => ?_,
      fun f hf hfc => integral_eq_integral_quotientMeasure H hH μG μH hmod hf hfc⟩
    simpa only [← rightCosetMul_eq_mk_out_mul] using
      map_rightCosetMul_quotientMeasure H hH μG μH hmod g
  · rintro ν ⟨hfin, -, hform⟩
    have : IsFiniteMeasureOnCompacts ν := hfin
    have : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
    exact quotientMeasure_eq_of_regular H hH μG μH hmod hform

/-! ### Scaling laws and uniqueness among all invariant Radon measures -/

/-- Replacing the right Haar measure `μH` by `c • μH` replaces `quotientMeasure` by
`c⁻¹ • quotientMeasure`. -/
theorem quotientMeasure_smul_right (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    (c : ℝ≥0) [(c • μH).IsOpenPosMeasure] :
    quotientMeasure H hH μG (c • μH) hmod =
      c⁻¹ • quotientMeasure H hH μG μH hmod := by
  have hc : c ≠ 0 := by
    intro h0
    have hne := isOpen_univ.measure_ne_zero (c • μH) Set.univ_nonempty
    simp [h0] at hne
  have : (quotientMeasure H hH μG μH hmod).Regular :=
    regular_quotientMeasure H hH μG μH hmod
  symm
  refine quotientMeasure_eq_of_regular H hH μG (c • μH) hmod fun f hf hfc => ?_
  rw [integral_eq_integral_quotientMeasure H hH μG μH hmod hf hfc]
  simp_rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, integral_const_mul]
  rw [← mul_assoc, NNReal.coe_inv, inv_mul_cancel₀ (NNReal.coe_ne_zero.mpr hc), one_mul]

/-- Replacing the ambient right Haar measure `μG` by `c • μG` replaces `quotientMeasure`
by `c • quotientMeasure`. -/
theorem quotientMeasure_smul_left (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    (c : ℝ≥0) [(c • μG).IsOpenPosMeasure] :
    quotientMeasure H hH (c • μG) μH hmod =
      c • quotientMeasure H hH μG μH hmod := by
  have : (quotientMeasure H hH μG μH hmod).Regular :=
    regular_quotientMeasure H hH μG μH hmod
  symm
  refine quotientMeasure_eq_of_regular H hH (c • μG) μH hmod fun f hf hfc => ?_
  rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_eq_integral_quotientMeasure H hH μG μH hmod hf hfc]

/-- **Uniqueness among all invariant Radon measures** (regular version): every right-`G`-invariant
regular Borel measure on `H \ G` is a nonnegative scalar multiple of `quotientMeasure`. -/
theorem exists_smul_quotientMeasure_of_regular [T2Space G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [μG.IsOpenPosMeasure] [μG.Regular]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {ν : Measure (MulAction.orbitRel.Quotient H G)} [ν.Regular]
    (hν : ∀ g : G, Measure.map (rightCosetMul H g) ν = ν) :
    ∃ c : ℝ≥0, ν = c • quotientMeasure H hH μG μH hmod := by
  let : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  -- Pull back `ν` along `quotientAverage` to a positive linear functional on `C_c(G, ℝ)`.
  let Λ : C_c(G, ℝ) →ₚ[ℝ] ℝ :=
    (integralPositiveLinearMap ν).comp (quotientAverage H hH μH)
  let μ' : Measure G := RealRMK.rieszMeasure Λ
  have hμ'_reg : μ'.Regular := RealRMK.regular_rieszMeasure Λ
  have hμ'_int : ∀ f : C_c(G, ℝ), ∫ g, f g ∂μ' = ∫ q, quotientAverage H hH μH f q ∂ν :=
    fun f => RealRMK.integral_rieszMeasure Λ f
  -- Right-invariance of `ν` makes `μ'` right-`G`-invariant.
  have : μ'.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have : (Measure.map (· * g) μ').Regular := hμ'_reg.map (Homeomorph.mulRight g)
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
    rw [integral_map (f := fun x : G => f x) (continuous_mul_const g).aemeasurable
      f.continuous.aestronglyMeasurable]
    let fg : C_c(G, ℝ) :=
      ⟨⟨fun x => f (x * g), f.continuous.comp (continuous_mul_const g)⟩,
        f.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight g)⟩
    change ∫ x, fg x ∂μ' = ∫ x, f x ∂μ'
    rw [hμ'_int fg, hμ'_int f]
    have hfg : ∀ q, quotientAverage H hH μH fg q =
        quotientAverage H hH μH f (rightCosetMul H g q) :=
      fun q => quotientAverage_comp_mulRight H hH μH f g q
    simp_rw [hfg]
    have hmap := integral_map (f := fun q => quotientAverage H hH μH f q)
      (continuous_rightCosetMul H g).aemeasurable
      (quotientAverage H hH μH f).continuous.aestronglyMeasurable (μ := ν)
    rw [hν g] at hmap
    exact hmap.symm
  -- By Haar uniqueness on `G`, `μ' = c • μG` for some `c : ℝ≥0`.
  obtain ⟨c, hμ'_eq⟩ := isMulRightInvariant_eq_smul_of_regular μ' μG
  refine ⟨c, ?_⟩
  have : (quotientMeasure H hH μG μH hmod).Regular :=
    regular_quotientMeasure H hH μG μH hmod
  refine Measure.ext_of_integral_eq_on_compactlySupported fun φ => ?_
  obtain ⟨f, rfl⟩ := quotientAverage_surjective H hH μH φ
  rw [← hμ'_int f, hμ'_eq, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_quotientMeasure, quotientFunctional_quotientAverage]

/-- **Uniqueness among all invariant Radon measures**: on a second countable locally compact
Hausdorff group `G`, every right-`G`-invariant measure on `H \ G` finite on compact sets is a
nonnegative scalar multiple of `quotientMeasure`. -/
theorem exists_smul_quotientMeasure_of_map_rightCosetMul_eq [T2Space G] [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG] [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {ν : Measure (MulAction.orbitRel.Quotient H G)} [IsFiniteMeasureOnCompacts ν]
    (hν : ∀ g : G, Measure.map (rightCosetMul H g) ν = ν) :
    ∃ c : ℝ≥0, ν = c • quotientMeasure H hH μG μH hmod := by
  let : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_rightCoset_of_isClosed hH
  let : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) := locallyCompactSpace_rightCoset H
  let : SecondCountableTopology (MulAction.orbitRel.Quotient H G) :=
    ContinuousConstSMul.secondCountableTopology
  let : T3Space (MulAction.orbitRel.Quotient H G) := inferInstance
  let : TopologicalSpace.MetrizableSpace (MulAction.orbitRel.Quotient H G) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  let : TopologicalSpace.MetrizableSpace G :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable G
  have : μG.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μG
  have : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  exact exists_smul_quotientMeasure_of_regular H hH μG μH hmod hν

end Construction

end TauCeti
