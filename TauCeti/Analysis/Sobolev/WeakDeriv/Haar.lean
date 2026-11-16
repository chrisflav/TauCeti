/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Scaling and Haar-measure invariance of weak derivatives

The defining integration-by-parts identity of `TauCeti.HasWeakLineDerivOn` and
`TauCeti.HasWeakFDerivOn` is linear in the reference measure, so multiplying the measure by any
finite constant preserves weak derivatives, and multiplying by a finite nonzero constant neither
adds nor removes them.

On a locally compact, second-countable real normed space with its Borel σ-algebra, any two
additive Haar measures are finite positive scalar multiples of one another
(`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`). Weak directional and Fréchet derivatives
therefore do not depend on the choice of additive Haar measure.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.smul_measure`, `TauCeti.hasWeakLineDerivOn_smul_measure_iff`:
  scaling the measure in a weak directional derivative.
* `TauCeti.HasWeakFDerivOn.smul_measure`, `TauCeti.hasWeakFDerivOn_smul_measure_iff`:
  scaling the measure in a weak Fréchet derivative.
* `TauCeti.HasWeakLineDerivOn.of_isAddLeftInvariant`,
  `TauCeti.hasWeakLineDerivOn_iff_of_isAddHaarMeasure`: independence of the additive Haar measure
  for weak directional derivatives.
* `TauCeti.HasWeakFDerivOn.of_isAddLeftInvariant`,
  `TauCeti.hasWeakFDerivOn_iff_of_isAddHaarMeasure`: independence of the additive Haar measure
  for weak Fréchet derivatives.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ ν : Measure E} {Ω : Opens E}
  {u u' : E → F} {U : E → E →L[ℝ] F} {v : E}

/-- Multiplying the measure by a finite constant preserves weak directional derivatives. -/
theorem HasWeakLineDerivOn.smul_measure (h : HasWeakLineDerivOn μ Ω u u' v)
    {c : ℝ≥0∞} (hc : c ≠ ∞) : HasWeakLineDerivOn (c • μ) Ω u u' v := by
  refine hasWeakLineDerivOn_iff_testFunction.2
    ⟨h.completeSpace, h.locallyIntegrableOn.smul_measure hc,
      h.locallyIntegrableOn_deriv.smul_measure hc, fun φ => ?_⟩
  rw [integral_smul_measure, integral_smul_measure,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, smul_neg]

/-- Multiplying the measure by a finite nonzero constant leaves weak directional derivatives
unchanged. -/
theorem hasWeakLineDerivOn_smul_measure_iff {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    HasWeakLineDerivOn (c • μ) Ω u u' v ↔ HasWeakLineDerivOn μ Ω u u' v := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have h' := h.smul_measure (ENNReal.inv_ne_top.2 hc0)
  rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] at h'

/-- Multiplying the measure by a finite constant preserves weak Fréchet derivatives. -/
theorem HasWeakFDerivOn.smul_measure (h : HasWeakFDerivOn μ Ω u U)
    {c : ℝ≥0∞} (hc : c ≠ ∞) : HasWeakFDerivOn (c • μ) Ω u U :=
  hasWeakFDerivOn_iff.2 fun w => (hasWeakFDerivOn_iff.1 h w).smul_measure hc

/-- Multiplying the measure by a finite nonzero constant leaves weak Fréchet derivatives
unchanged. -/
theorem hasWeakFDerivOn_smul_measure_iff {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    HasWeakFDerivOn (c • μ) Ω u U ↔ HasWeakFDerivOn μ Ω u U := by
  simp only [hasWeakFDerivOn_iff, hasWeakLineDerivOn_smul_measure_iff hc0 hc]

variable [LocallyCompactSpace E] [SecondCountableTopology E] [BorelSpace E]

/-- A weak directional derivative with respect to an additive Haar measure is also a weak
directional derivative with respect to every translation-invariant measure finite on compact
sets. -/
theorem HasWeakLineDerivOn.of_isAddLeftInvariant [μ.IsAddHaarMeasure] (ν : Measure E)
    [IsFiniteMeasureOnCompacts ν] [ν.IsAddLeftInvariant]
    (h : HasWeakLineDerivOn μ Ω u u' v) : HasWeakLineDerivOn ν Ω u u' v := by
  rw [Measure.isAddLeftInvariant_eq_smul ν μ]
  exact h.smul_measure ENNReal.coe_ne_top

/-- **Haar-measure independence of weak directional derivatives.** Any two additive Haar measures
define the same weak directional derivatives. -/
theorem hasWeakLineDerivOn_iff_of_isAddHaarMeasure [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    HasWeakLineDerivOn μ Ω u u' v ↔ HasWeakLineDerivOn ν Ω u u' v :=
  ⟨fun h => h.of_isAddLeftInvariant ν, fun h => h.of_isAddLeftInvariant μ⟩

/-- A weak Fréchet derivative with respect to an additive Haar measure is also a weak Fréchet
derivative with respect to every translation-invariant measure finite on compact sets. -/
theorem HasWeakFDerivOn.of_isAddLeftInvariant [μ.IsAddHaarMeasure] (ν : Measure E)
    [IsFiniteMeasureOnCompacts ν] [ν.IsAddLeftInvariant]
    (h : HasWeakFDerivOn μ Ω u U) : HasWeakFDerivOn ν Ω u U :=
  hasWeakFDerivOn_iff.2 fun w => (hasWeakFDerivOn_iff.1 h w).of_isAddLeftInvariant ν

/-- **Haar-measure independence of weak Fréchet derivatives.** Any two additive Haar measures
define the same weak Fréchet derivatives. -/
theorem hasWeakFDerivOn_iff_of_isAddHaarMeasure [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    HasWeakFDerivOn μ Ω u U ↔ HasWeakFDerivOn ν Ω u U :=
  ⟨fun h => h.of_isAddLeftInvariant ν, fun h => h.of_isAddLeftInvariant μ⟩

end TauCeti
