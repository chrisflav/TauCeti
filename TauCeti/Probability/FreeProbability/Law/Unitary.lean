/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import TauCeti.MeasureTheory.Integral.ContinuousMap
import Mathlib.Topology.TietzeExtension
import TauCeti.MeasureTheory.Group.Circle
import TauCeti.Topology.ContinuousMap.CompactlySupported

/-!
# The circle-valued spectral law of a unitary element in a C⋆-probability space

Let `A` be a unital C⋆-algebra, `φ : A →ₚ[ℂ] ℂ` a positive linear functional, and `u ∈ unitary A`
a unitary element. Because `u` is star-normal and `spectrum ℂ u` lies on the unit circle, the
continuous functional calculus gives a unital ⋆-homomorphism `C(spectrum ℂ u, ℂ) →⋆ₐ[ℂ] A`.
Restricting `f ↦ Re φ (f(u))` to real-valued continuous functions on `spectrum ℂ u` yields a
positive linear functional, represented via the Riesz–Markov–Kakutani theorem by a finite Borel
measure on `spectrum ℂ u`. Pushing forward along the inclusion `spectrum ℂ u → Circle` produces the
**unitary law** `φ.unitaryLaw u : Measure Circle`:

`∫ z : Circle, f z ∂(φ.unitaryLaw u) = φ (cfc f u)` for every `f : ℂ → ℂ` continuous on
`spectrum ℂ u`.

This circle-valued spectral measure is the unitary counterpart of `PositiveLinearMap.law` (defined
on `ℝ` for selfadjoint elements):

* It is concentrated on the preimage of `spectrum ℂ u` in `Circle`, has total mass `φ 1`, and is a
  probability measure when `φ 1 = 1`.
* Its Fourier moments `∫ z : Circle, (z : ℂ) ^ k ∂(φ.unitaryLaw u)` for `k : ℤ` coincide with the
  integer power moments `φ (u ^ k)` of `u` in `unitary A`, and uniquely determine `φ.unitaryLaw u`
  among all finite Borel measures on `Circle` (no auxiliary compact-support hypothesis is needed
  since `Circle` is compact).
* Every finite Borel measure `μ` on `Circle` is realized as the unitary law of the coordinate
  unitary `z ↦ (z : ℂ)` in the commutative C⋆-algebra `C(Circle, ℂ)` with respect to
  `ContinuousMap.integralPositiveLinearMap μ`.

For `u ∉ unitary A`, `φ.unitaryLaw u` is defined to be `0`, matching `PositiveLinearMap.law`.

## Main declarations

* `PositiveLinearMap.unitaryLaw φ u`: the spectral measure on `Circle` of `u` with respect to `φ`,
  equal to `0` when `u ∉ unitary A`.
* `PositiveLinearMap.integral_unitaryLaw`: for `u ∈ unitary A` and `f : ℂ → ℂ` continuous on
  `spectrum ℂ u`, `∫ z : Circle, f z ∂(φ.unitaryLaw u) = φ (cfc f u)`.
* `PositiveLinearMap.eq_unitaryLaw_iff`: for `u ∈ unitary A`, `φ.unitaryLaw u` is the unique finite
  Borel measure on `Circle` integrating every continuous `f : ℂ → ℂ` to `φ (cfc f u)`.
* `PositiveLinearMap.isProbabilityMeasure_unitaryLaw`: `φ.unitaryLaw u` is a probability measure
  when `φ 1 = 1` and `u ∈ unitary A`.
* `PositiveLinearMap.integral_zpow_unitaryLaw`, `PositiveLinearMap.integral_pow_unitaryLaw`,
  `PositiveLinearMap.integral_star_pow_unitaryLaw`: Fourier and power moments of `φ.unitaryLaw u`.
* `PositiveLinearMap.eq_unitaryLaw_iff_forall_integral_zpow` and
  `PositiveLinearMap.unitaryLaw_eq_unitaryLaw_iff_forall_apply_zpow`: Fourier moment determinacy.
* `PositiveLinearMap.unitaryLaw_star`, `PositiveLinearMap.unitaryLaw_zpow`,
  `PositiveLinearMap.unitaryLaw_pow`: equivariance under adjoint and integer/natural powers.
* `PositiveLinearMap.unitaryLaw_integralPositiveLinearMap` and
  `PositiveLinearMap.unitaryLaw_integralPositiveLinearMap_id`: realization of arbitrary finite
  Borel measures on `Circle` in commutative C⋆-algebras.

## Implementation notes

The Riesz–Markov–Kakutani construction and complexification step follow `PositiveLinearMap.law` in
`TauCeti.Probability.FreeProbability.Law.Basic`, replacing the real continuous functional calculus
of a selfadjoint element with the complex continuous functional calculus of a unitary element and
pushing forward along `spectrum ℂ u → Circle`. Fourier moment determinacy uses
`MeasureTheory.Measure.ext_of_forall_integral_zpow_eq` from `TauCeti.MeasureTheory.Group.Circle`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Math. Soc.
  Lecture Note Ser. 335, Cambridge University Press (2006), Lectures 1 and 3.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §1.1.
-/

public section

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ComplexOrder CompactlySupported

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] {u : A}

/-- The canonical embedding of the spectrum of a unitary element into `Circle`. -/
private def spectrumToCircle (hu : u ∈ unitary A) (x : spectrum ℂ u) : Circle :=
  ⟨x.1, mem_sphere_zero_iff_norm.2
    (CStarRing.norm_of_mem_unitary (spectrum_subset_unitary_of_mem_unitary hu x.2))⟩

private lemma coe_spectrumToCircle (hu : u ∈ unitary A) (x : spectrum ℂ u) :
    ((spectrumToCircle hu x : Circle) : ℂ) = x.1 :=
  rfl

private lemma continuous_spectrumToCircle (hu : u ∈ unitary A) :
    Continuous (spectrumToCircle hu) :=
  continuous_subtype_val.subtype_mk _

private lemma measurableEmbedding_spectrumToCircle (hu : u ∈ unitary A) :
    MeasurableEmbedding (spectrumToCircle hu) :=
  ((continuous_spectrumToCircle hu).isClosedEmbedding
    fun _ _ h ↦ Subtype.ext (congrArg (fun z : Circle ↦ (z : ℂ)) h)).measurableEmbedding

variable [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)

/-- The positive real functional `g ↦ Re φ (g(u))` on real continuous functions on `spectrum ℂ u`,
whose Riesz–Markov–Kakutani measure pushes forward to `φ.unitaryLaw u`. -/
private def unitaryLawFunctional (hu : u ∈ unitary A) : C_c(spectrum ℂ u, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun g := (φ (cfcHom (isStarNormal_of_mem_unitary hu)
        (g.toContinuousMap.realToRCLike ℂ))).re
      map_add' g h := by
        simp only [← ContinuousMap.realToRCLikeStarAlgHom_apply]
        rw [CompactlySupportedContinuousMap.toContinuousMap_add,
          map_add, map_add, map_add, Complex.add_re]
      map_smul' c g := by
        simp only [← ContinuousMap.realToRCLikeStarAlgHom_apply]
        rw [CompactlySupportedContinuousMap.toContinuousMap_smul, map_smul,
          ← algebraMap_smul ℂ c (M := C(spectrum ℂ u, ℂ)), map_smul, map_smul]
        simp }
    fun g hg => by
      have hT : 0 ≤ cfcHom (isStarNormal_of_mem_unitary hu)
          (g.toContinuousMap.realToRCLike ℂ) := by
        rw [cfcHom_nonneg_iff]
        intro x
        simpa using hg x
      exact (Complex.nonneg_iff.mp (φ.map_nonneg hT)).1

/-- The spectral measure of a unitary element on `spectrum ℂ u`, before pushing forward to
`Circle`. -/
private def spectrumUnitaryLaw (hu : u ∈ unitary A) : Measure (spectrum ℂ u) :=
  RealRMK.rieszMeasure (unitaryLawFunctional φ hu)

open scoped Classical in
/-- The **unitary law** of an element `u` of a C⋆-algebra with respect to a positive linear
functional `φ`: for `u ∈ unitary A`, the finite Borel measure on `Circle` characterized by
`∫ z : Circle, f z ∂(φ.unitaryLaw u) = φ (cfc f u)` for every `f : ℂ → ℂ` continuous on
`spectrum ℂ u` (`integral_unitaryLaw`, `eq_unitaryLaw_iff`). For `u ∉ unitary A` it is the zero
measure (`unitaryLaw_of_not_mem_unitary`). -/
def unitaryLaw (φ : A →ₚ[ℂ] ℂ) (u : A) : Measure Circle :=
  if hu : u ∈ unitary A then (spectrumUnitaryLaw φ hu).map (spectrumToCircle hu) else 0

private lemma unitaryLaw_of_mem_unitary (hu : u ∈ unitary A) :
    unitaryLaw φ u = (spectrumUnitaryLaw φ hu).map (spectrumToCircle hu) := by
  simp [unitaryLaw, hu]

/-- The unitary law of an element that is not unitary is, by convention, the zero measure. -/
@[simp]
theorem unitaryLaw_of_not_mem_unitary (hu : u ∉ unitary A) : unitaryLaw φ u = 0 := by
  simp [unitaryLaw, hu]

/-- The unitary law of any element is a finite measure on `Circle`. -/
instance (u : A) : IsFiniteMeasure (unitaryLaw φ u) := by
  by_cases hu : u ∈ unitary A
  · rw [unitaryLaw_of_mem_unitary φ hu]
    unfold spectrumUnitaryLaw
    infer_instance
  · rw [unitaryLaw_of_not_mem_unitary φ hu]
    infer_instance

/-- `φ.unitaryLaw u` assigns measure zero to the complement in `Circle` of `spectrum ℂ u`. -/
@[simp]
theorem unitaryLaw_preimage_compl_spectrum (u : A) :
    unitaryLaw φ u (((↑) : Circle → ℂ) ⁻¹' (spectrum ℂ u)ᶜ) = 0 := by
  by_cases hu : u ∈ unitary A
  · rw [unitaryLaw_of_mem_unitary φ hu,
      Measure.map_apply (continuous_spectrumToCircle hu).measurable
        ((spectrum.isClosed u).measurableSet.compl.preimage measurable_subtype_coe)]
    have hempty : spectrumToCircle hu ⁻¹' (((↑) : Circle → ℂ) ⁻¹' (spectrum ℂ u)ᶜ) = ∅ := by
      ext x
      exact ⟨fun hx ↦ hx x.2, False.elim⟩
    simp [hempty]
  · simp [unitaryLaw_of_not_mem_unitary φ hu]

/-- `φ.unitaryLaw u` is concentrated on `{z : Circle | (z : ℂ) ∈ spectrum ℂ u}`. -/
@[simp]
theorem restrict_preimage_spectrum_unitaryLaw (u : A) :
    (unitaryLaw φ u).restrict (((↑) : Circle → ℂ) ⁻¹' spectrum ℂ u) = unitaryLaw φ u :=
  Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (unitaryLaw_preimage_compl_spectrum φ u))

/-- Every `f : ℂ → ℂ` continuous on `spectrum ℂ u` is integrable on `Circle` against
`φ.unitaryLaw u`. -/
theorem integrable_unitaryLaw (u : A) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ u) := by cfc_cont_tac) :
    Integrable (fun z : Circle ↦ f z) (unitaryLaw φ u) := by
  by_cases hu : u ∈ unitary A
  · have : IsFiniteMeasure (spectrumUnitaryLaw φ hu) := by
      unfold spectrumUnitaryLaw
      infer_instance
    rw [unitaryLaw_of_mem_unitary φ hu,
      (measurableEmbedding_spectrumToCircle hu).integrable_map_iff]
    exact hf.domRestrict.integrable_of_compactSpace
  · simp [unitaryLaw_of_not_mem_unitary φ hu]

private lemma ofReal_integral_spectrumUnitaryLaw (hu : u ∈ unitary A) (g : C(spectrum ℂ u, ℝ)) :
    ((∫ x, g x ∂(spectrumUnitaryLaw φ hu) : ℝ) : ℂ) =
      φ (cfcHom (isStarNormal_of_mem_unitary hu) (g.realToRCLike ℂ)) := by
  have h := RealRMK.integral_rieszMeasure (unitaryLawFunctional φ hu) ⟨g, .of_compactSpace _⟩
  rw [CompactlySupportedContinuousMap.coe_mk] at h
  rw [spectrumUnitaryLaw, h]
  have hsa : IsSelfAdjoint (φ (cfcHom (isStarNormal_of_mem_unitary hu) (g.realToRCLike ℂ))) :=
    ((ContinuousMap.isSelfAdjoint_realToRCLike ℂ).map
      (cfcHom (isStarNormal_of_mem_unitary hu))).map' φ
  exact Complex.conj_eq_iff_re.mp hsa.star_eq

private lemma integral_spectrumUnitaryLaw (hu : u ∈ unitary A) (f : C(spectrum ℂ u, ℂ)) :
    ∫ x, f x ∂(spectrumUnitaryLaw φ hu) = φ (cfcHom (isStarNormal_of_mem_unitary hu) f) := by
  have : IsFiniteMeasure (spectrumUnitaryLaw φ hu) := by
    unfold spectrumUnitaryLaw
    infer_instance
  exact (LinearMap.apply_eq_integral_of_forall_realToRCLike
    (φ.toLinearMap.comp (cfcHom (isStarNormal_of_mem_unitary hu)).toLinearMap)
    (fun g ↦ (ofReal_integral_spectrumUnitaryLaw φ hu g).symm) f).symm

/-- Integration against `φ.unitaryLaw u` for `u ∈ unitary A` evaluates `φ` on the complex
continuous functional calculus: `∫ z : Circle, f z ∂(φ.unitaryLaw u) = φ (cfc f u)`.

Unlike `PositiveLinearMap.ofReal_integral_law`, the hypothesis `hu : u ∈ unitary A` cannot be
dropped: for `u = 2 • (1 : ℂ)`, `u` is star-normal with `cfc (fun _ ↦ 1) u = 1`, whereas
`u ∉ unitary ℂ` so `unitaryLaw φ u = 0`. -/
theorem integral_unitaryLaw (hu : u ∈ unitary A) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ u) := by cfc_cont_tac) :
    ∫ z : Circle, f z ∂(unitaryLaw φ u) = φ (cfc f u) := by
  have := isStarNormal_of_mem_unitary hu
  rw [unitaryLaw_of_mem_unitary φ hu, (measurableEmbedding_spectrumToCircle hu).integral_map,
    cfc_apply f u]
  exact integral_spectrumUnitaryLaw φ hu ⟨_, hf.domRestrict⟩

variable {φ} in
/-- For `u ∈ unitary A`, `φ.unitaryLaw u` is the unique finite Borel measure on `Circle`
representing `f ↦ φ (cfc f u)` for all continuous `f : ℂ → ℂ`. -/
theorem eq_unitaryLaw_iff (hu : u ∈ unitary A) {μ : Measure Circle} [IsFiniteMeasure μ] :
    μ = unitaryLaw φ u ↔
      ∀ f : ℂ → ℂ, Continuous f → ∫ z : Circle, f z ∂μ = φ (cfc f u) := by
  refine ⟨fun h f _ ↦ h ▸ integral_unitaryLaw φ hu f, fun h ↦ ?_⟩
  refine Measure.ext_of_integral_eq_on_compactlySupported fun g ↦ Complex.ofReal_injective ?_
  have hcont : Continuous (fun z : Circle ↦ (z : ℂ)) := continuous_subtype_val
  have hemb : IsClosedEmbedding (fun z : Circle ↦ (z : ℂ)) :=
    hcont.isClosedEmbedding Circle.coe_injective
  obtain ⟨G, hG⟩ := g.toContinuousMap.exists_extension hemb
  have hGz (z : Circle) : G (z : ℂ) = g z := congr($hG z)
  have hint : ∫ z : Circle, (G (z : ℂ) : ℂ) ∂μ = ∫ z : Circle, (G (z : ℂ) : ℂ) ∂(unitaryLaw φ u) :=
    (h (fun w ↦ (G w : ℂ)) (Complex.continuous_ofReal.comp G.continuous)).trans
      (integral_unitaryLaw φ hu (fun w ↦ (G w : ℂ))).symm
  simpa only [hGz, integral_complex_ofReal] using hint

/-- The total mass of the unitary law of a unitary element is `φ 1`. -/
theorem ofReal_unitaryLaw_real_univ (hu : u ∈ unitary A) :
    (((unitaryLaw φ u).real univ : ℝ) : ℂ) = φ 1 := by
  have := isStarNormal_of_mem_unitary hu
  simpa [integral_const, Complex.real_smul, cfc_const_one ℂ u] using
    integral_unitaryLaw φ hu (fun _ ↦ 1)

/-- The unitary law of a unitary element with respect to a state (`φ 1 = 1`) is a probability
measure on `Circle`. -/
theorem isProbabilityMeasure_unitaryLaw (hφ : φ 1 = 1) (hu : u ∈ unitary A) :
    IsProbabilityMeasure (unitaryLaw φ u) := by
  refine ⟨?_⟩
  have h := ofReal_unitaryLaw_real_univ φ hu
  rw [hφ, Complex.ofReal_eq_one] at h
  rw [← ofReal_measureReal, h, ENNReal.ofReal_one]

/-- The natural-power moments of `φ.unitaryLaw u` are `φ (u ^ n)`. -/
theorem integral_pow_unitaryLaw (hu : u ∈ unitary A) (n : ℕ) :
    ∫ z : Circle, (z : ℂ) ^ n ∂(unitaryLaw φ u) = φ (u ^ n) := by
  have := isStarNormal_of_mem_unitary hu
  rw [integral_unitaryLaw φ hu (· ^ n), cfc_pow_id u n]

/-- The conjugate natural-power moments of `φ.unitaryLaw u` are `φ (star u ^ n)`. -/
theorem integral_star_pow_unitaryLaw (hu : u ∈ unitary A) (n : ℕ) :
    ∫ z : Circle, star (z : ℂ) ^ n ∂(unitaryLaw φ u) = φ (star u ^ n) := by
  have := isStarNormal_of_mem_unitary hu
  rw [integral_unitaryLaw φ hu (fun w ↦ star w ^ n),
    cfc_pow (fun w : ℂ ↦ star w) n u, cfc_star_id u]

/-- The Fourier (integer-power) moments of `φ.unitaryLaw u` are the unitary group powers
`φ (u ^ k)`. -/
theorem integral_zpow_unitaryLaw (hu : u ∈ unitary A) (k : ℤ) :
    ∫ z : Circle, (z : ℂ) ^ k ∂(unitaryLaw φ u) =
      φ (((⟨u, hu⟩ : unitary A) ^ k : unitary A) : A) := by
  have := isStarNormal_of_mem_unitary hu
  have hcont : ContinuousOn (fun w : ℂ ↦ w ^ k) (spectrum ℂ u) :=
    continuousOn_id.zpow₀ k fun w hw ↦ Or.inl <|
      Circle.coe_ne_zero ⟨w, mem_sphere_zero_iff_norm.2
        (CStarRing.norm_of_mem_unitary (spectrum_subset_unitary_of_mem_unitary hu hw))⟩
  rw [integral_unitaryLaw φ hu (fun w ↦ w ^ k) hcont]
  have hcfc := cfc_zpow (R := ℂ) (Unitary.toUnits ⟨u, hu⟩) k
  rw [← map_zpow (Unitary.toUnits (R := A)) ⟨u, hu⟩ k, Unitary.val_toUnits_apply] at hcfc
  rw [Unitary.val_toUnits_apply] at hcfc
  rw [hcfc]

/-! ### Fourier moment determinacy and pushforward laws -/

variable {φ} in
/-- **Fourier moment determinacy of the unitary law.** For `u ∈ unitary A`, a finite Borel measure
`μ` on `Circle` equals `φ.unitaryLaw u` if and only if all of its integer power moments agree with
those of `u`. -/
theorem eq_unitaryLaw_iff_forall_integral_zpow (hu : u ∈ unitary A) {μ : Measure Circle}
    [IsFiniteMeasure μ] :
    μ = unitaryLaw φ u ↔
      ∀ k : ℤ, ∫ z : Circle, (z : ℂ) ^ k ∂μ =
        φ (((⟨u, hu⟩ : unitary A) ^ k : unitary A) : A) := by
  refine ⟨fun h k ↦ h ▸ integral_zpow_unitaryLaw φ hu k, fun h ↦ ?_⟩
  exact Measure.ext_of_forall_integral_zpow_eq fun k ↦
    (h k).trans (integral_zpow_unitaryLaw φ hu k).symm

/-- Two unitary elements, possibly in different C⋆-algebras and under different positive linear
functionals, have the same unitary law if and only if they have the same integer power moments. -/
theorem unitaryLaw_eq_unitaryLaw_iff_forall_apply_zpow {B : Type*} [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] (ψ : B →ₚ[ℂ] ℂ) {v : B}
    (hu : u ∈ unitary A) (hv : v ∈ unitary B) :
    unitaryLaw φ u = unitaryLaw ψ v ↔
      ∀ k : ℤ, φ (((⟨u, hu⟩ : unitary A) ^ k : unitary A) : A) =
        ψ (((⟨v, hv⟩ : unitary B) ^ k : unitary B) : B) := by
  rw [eq_unitaryLaw_iff_forall_integral_zpow hv]
  simp_rw [integral_zpow_unitaryLaw φ hu]

/-- The unitary law of `star u` is the pushforward of `φ.unitaryLaw u` along inversion on `Circle`
(which agrees with complex conjugation). This holds unconditionally for all `u : A`. -/
theorem unitaryLaw_star (u : A) :
    unitaryLaw φ (star u) = (unitaryLaw φ u).map Inv.inv := by
  by_cases hu : u ∈ unitary A
  · refine ((eq_unitaryLaw_iff_forall_integral_zpow (Unitary.star_mem hu)).2 fun k ↦ ?_).symm
    have hcont : Continuous fun z : Circle ↦ (z : ℂ) ^ k :=
      continuous_subtype_val.zpow₀ k fun z ↦ .inl (Circle.coe_ne_zero z)
    rw [integral_map continuous_inv.aemeasurable hcont.aestronglyMeasurable]
    simp only [Circle.coe_inv, inv_zpow, ← zpow_neg, integral_zpow_unitaryLaw φ hu]
    congr 1
    exact congrArg Subtype.val
      (by rw [Unitary.star_eq_inv ⟨u, hu⟩, inv_zpow, zpow_neg] :
        (⟨u, hu⟩ : unitary A) ^ (-k) = (star ⟨u, hu⟩) ^ k)
  · have hsu : star u ∉ unitary A := mt Unitary.star_mem_iff.mp hu
    simp [unitaryLaw_of_not_mem_unitary φ hu, unitaryLaw_of_not_mem_unitary φ hsu]

/-- The unitary law of the `m`-th unitary power of `u` is the pushforward of `φ.unitaryLaw u`
along `(· ^ m) : Circle → Circle`. -/
theorem unitaryLaw_zpow (hu : u ∈ unitary A) (m : ℤ) :
    unitaryLaw φ (((⟨u, hu⟩ : unitary A) ^ m : unitary A) : A) =
      (unitaryLaw φ u).map (· ^ m) := by
  let U : unitary A := ⟨u, hu⟩
  refine ((eq_unitaryLaw_iff_forall_integral_zpow (U ^ m).2).2 fun k ↦ ?_).symm
  have hcont : Continuous fun z : Circle ↦ (z : ℂ) ^ k :=
    continuous_subtype_val.zpow₀ k fun z ↦ .inl (Circle.coe_ne_zero z)
  rw [integral_map (continuous_zpow m).aemeasurable hcont.aestronglyMeasurable]
  simp only [Circle.coe_zpow, ← zpow_mul, integral_zpow_unitaryLaw φ hu]
  congr 1
  exact congrArg Subtype.val (zpow_mul U m k)

/-- The unitary law of `u ^ n` for `u ∈ unitary A` and `n : ℕ` is the pushforward of
`φ.unitaryLaw u` along `(· ^ n) : Circle → Circle`. -/
theorem unitaryLaw_pow (hu : u ∈ unitary A) (n : ℕ) :
    unitaryLaw φ (u ^ n) = (unitaryLaw φ u).map (· ^ n) := by
  simpa using unitaryLaw_zpow φ hu (n : ℤ)

/-! ### Realization of finite Borel measures on `Circle` -/

section Realization

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- In the commutative C⋆-algebra `C(X, ℂ)` of a compact space `X`, the unitary law of a
`Circle`-valued continuous map `g` (viewed in `C(X, ℂ)`) with respect to integration against a
finite measure `ν` is the pushforward `ν.map g`. -/
theorem unitaryLaw_integralPositiveLinearMap (ν : Measure X) [IsFiniteMeasure ν]
    (g : C(X, Circle)) :
    unitaryLaw (ContinuousMap.integralPositiveLinearMap ν)
      ⟨fun x ↦ (g x : ℂ), continuous_subtype_val.comp g.continuous⟩ = ν.map g := by
  let ug : C(X, ℂ) := ⟨fun x ↦ (g x : ℂ), continuous_subtype_val.comp g.continuous⟩
  have hug : ug ∈ unitary C(X, ℂ) := by
    rw [Unitary.mem_iff]
    constructor <;> ext x <;> simp [ug, ← Circle.coe_inv_eq_conj]
  refine ((eq_unitaryLaw_iff_forall_integral_zpow hug).2 fun k ↦ ?_).symm
  have hcont : Continuous fun z : Circle ↦ (z : ℂ) ^ k :=
    continuous_subtype_val.zpow₀ k fun z ↦ .inl (Circle.coe_ne_zero z)
  rw [integral_map g.continuous.aemeasurable hcont.aestronglyMeasurable,
    ContinuousMap.integralPositiveLinearMap_apply]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  let e : unitary C(X, ℂ) →* ℂˣ :=
    (Units.map (ContinuousMap.evalStarAlgHom ℂ ℂ x).toMonoidHom).comp Unitary.toUnits
  have hex : e ⟨ug, hug⟩ = Circle.toUnits (g x) := by ext; rfl
  have hk : (((⟨ug, hug⟩ ^ k : unitary C(X, ℂ)) : C(X, ℂ)) x) = (e (⟨ug, hug⟩ ^ k) : ℂ) := rfl
  rw [map_zpow, hex, ← map_zpow Circle.toUnits (g x) k] at hk
  simpa only [Circle.toUnits_apply, Units.val_mk0, Circle.coe_zpow] using hk.symm

/-- **Realization of laws on `Circle`.** Every finite Borel measure `μ` on `Circle` is the unitary
law of the coordinate function `z ↦ (z : ℂ)` in `C(Circle, ℂ)` with respect to
`ContinuousMap.integralPositiveLinearMap μ`. -/
theorem unitaryLaw_integralPositiveLinearMap_id (μ : Measure Circle) [IsFiniteMeasure μ] :
    unitaryLaw (ContinuousMap.integralPositiveLinearMap μ)
      ⟨(↑), continuous_subtype_val⟩ = μ := by
  simpa using unitaryLaw_integralPositiveLinearMap μ (ContinuousMap.id Circle)

end Realization

end PositiveLinearMap
