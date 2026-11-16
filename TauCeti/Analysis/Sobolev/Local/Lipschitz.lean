/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# Locally Lipschitz maps are in every local `W^{1,p}` class

A map between finite-dimensional real normed spaces that is locally Lipschitz on an open set `Ω`
lies in the local class `W^{1,p}` on every subset `U ⊆ Ω`, for every exponent `p` including `p = ∞`
and `0 ≤ p < 1` (`LocallyLipschitzOn.memWkpLoc_one`), with respect to any additive Haar measure.
In particular, every globally Lipschitz map is in `W^{1,p}_loc` on every set
(`LipschitzWith.memWkpLoc_one`). By Rademacher's theorem its Fréchet derivative is a weak
derivative, and it is locally bounded by the local Lipschitz constants.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.2.3, Theorem 4.5.
-/

public section

open MeasureTheory TopologicalSpace Filter Set

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {U : Set E}

/-- A map between finite-dimensional real normed spaces that is locally Lipschitz on an open set
`Ω` lies in `MemWkpLoc p U 1` on every `U ⊆ Ω`, for every exponent `p`: by Rademacher's theorem its
Fréchet derivative is a weak derivative on `Ω`, and it is bounded on every compact subset of `U` by
a Lipschitz constant on a slightly larger compact neighbourhood. -/
theorem _root_.LocallyLipschitzOn.memWkpLoc_one [FiniteDimensional ℝ F] {Ω : Opens E}
    {u : E → F} (hu : LocallyLipschitzOn (Ω : Set E) u) (hU : U ⊆ Ω) :
    MemWkpLoc p U 1 u μ := by
  refine memWkpLoc_one_iff.2 ⟨(hu.continuousOn.mono hU).memLpLoc, fderiv ℝ u,
    (hu.hasWeakFDerivOn_fderiv (μ := μ)).mono (interior_subset.trans hU),
    memLpLoc_iff.2 fun K hKU hK => ?_⟩
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK (hKU.trans hU)
  obtain ⟨C, hC⟩ := (hu.mono hWΩ).exists_lipschitzOnWith_of_compact hWc
  have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  refine MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact norm_fderiv_le_of_lipschitzOn ℝ (W.isOpen.mem_nhds (hKW hx)) (hC.mono subset_closure)

/-- A globally Lipschitz map between finite-dimensional real normed spaces is in the local class
`W^{1,p}` on every set, for every exponent: its Fréchet derivative is a weak derivative bounded by
the Lipschitz constant. -/
theorem _root_.LipschitzWith.memWkpLoc_one [FiniteDimensional ℝ F] {K : NNReal} {u : E → F}
    (hu : LipschitzWith K u) : MemWkpLoc p U 1 u μ :=
  hu.locallyLipschitz.locallyLipschitzOn.memWkpLoc_one (Ω := ⊤) (subset_univ U)

end TauCeti
