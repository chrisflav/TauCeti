/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# Linear and homeomorphic changes of domain in local Sobolev classes

Precomposition with a measure-preserving homeomorphism preserves and reflects `TauCeti.MemLpLoc`
(`Homeomorph.memLpLoc_comp_of_mapsTo`, `Homeomorph.memLpLoc_comp_iff`). For any continuous linear
equivalence `e : E ≃L[ℝ] E'` between locally compact second-countable real topological vector
spaces (in particular, finite-dimensional real normed spaces) with arbitrary additive Haar measures
`μ` and `ν`, precomposition with `e` preserves and reflects `TauCeti.MemLpLoc`
(`MemLpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memLpLoc_comp_iff`). On
finite-dimensional real normed spaces, the same holds for `TauCeti.MemWkpLoc` of every order `k`
(`MemWkpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memWkpLoc_comp_iff`).

In particular, the local classes on a finite-dimensional real normed space depend neither on the
choice of norm (up to equivalence, e.g. transferring between `ℝ × ℝ` with the supremum norm and
`EuclideanSpace ℝ (Fin 2)`) nor on the normalization of the additive Haar measure.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.
* W. P. Ziemer, *Weakly Differentiable Functions*, §2.2 (changes of variables).
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace

namespace Homeomorph

variable {α β ε : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [NormedAddCommGroup ε]
  {μ : Measure α} {ν : Measure β} {p : ENNReal} {U : Set α} {V : Set β} {f : β → ε}

/-- **Local `Lᵖ` transfer under a measure-preserving homeomorphism.** If `f` is locally `Lᵖ` on `V`
with respect to `ν`, and the measure-preserving homeomorphism `e` maps `U` into `V`, then `f ∘ e`
is locally `Lᵖ` on `U` with respect to `μ`. -/
theorem memLpLoc_comp_of_mapsTo (e : α ≃ₜ β) (he : MeasurePreserving e μ ν)
    (hf : TauCeti.MemLpLoc p V f ν) (hUV : MapsTo e U V) :
    TauCeti.MemLpLoc p U (f ∘ e) μ :=
  TauCeti.memLpLoc_iff.2 fun _ hKU hK =>
    e.memLp_comp_restrict_of_forall_isCompact he
      (fun _ hL hLV => TauCeti.memLpLoc_iff.1 hf _ hLV hL) hK (hKU.trans hUV)

/-- **Local `Lᵖ` equivalence under a measure-preserving homeomorphism.** If `e` is a
measure-preserving homeomorphism with `U = e ⁻¹' V`, then `f ∘ e` is locally `Lᵖ` on `U` with
respect to `μ` exactly when `f` is locally `Lᵖ` on `V` with respect to `ν`. -/
theorem memLpLoc_comp_iff (e : α ≃ₜ β) (he : MeasurePreserving e μ ν) (hUV : U = e ⁻¹' V) :
    TauCeti.MemLpLoc p U (f ∘ e) μ ↔ TauCeti.MemLpLoc p V f ν := by
  refine ⟨fun h => ?_, fun h => e.memLpLoc_comp_of_mapsTo he h (hUV ▸ mapsTo_preimage e V)⟩
  have hsymm : MeasurePreserving e.symm ν μ := he.symm e.toMeasurableEquiv
  have hVU : MapsTo e.symm V U := fun y hy => by simpa [hUV] using hy
  simpa [Function.comp_def] using e.symm.memLpLoc_comp_of_mapsTo hsymm h hVU

end Homeomorph

namespace TauCeti

universe u₁ u₂ v

section ContinuousLinearEquivLp

variable {E : Type u₁} {E' : Type u₂} {F : Type v}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [MeasurableSpace E] [BorelSpace E]
  [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E'] [IsTopologicalAddGroup E']
  [MeasurableSpace E'] [BorelSpace E'] [NormedAddCommGroup F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {p : ENNReal} {U : Set E} {V : Set E'} {f : E' → F}

variable (μ) in
/-- **Linear change of domain in `MemLpLoc`.** Precomposition with any continuous linear
equivalence `e : E ≃L[ℝ] E'` mapping `U` into `V` carries `MemLpLoc p V f ν` into
`MemLpLoc p U (f ∘ e) μ`, for arbitrary additive Haar measures `μ` and `ν`. -/
theorem MemLpLoc.comp_continuousLinearEquiv [LocallyCompactSpace E'] [SecondCountableTopology E']
    (hf : MemLpLoc p V f ν) (e : E ≃L[ℝ] E') (hUV : MapsTo e U V) :
    MemLpLoc p U (f ∘ e) μ :=
  e.toHomeomorph.memLpLoc_comp_of_mapsTo ⟨e.continuous.measurable, rfl⟩
    (hf.of_isAddLeftInvariant (μ.map e)) hUV

/-- **Linear invariance of `MemLpLoc`.** For any continuous linear equivalence `e : E ≃L[ℝ] E'`
with `U = e ⁻¹' V`, `f ∘ e` lies in `MemLpLoc p U · μ` exactly when `f` lies in `MemLpLoc p V · ν`,
for arbitrary additive Haar measures `μ` and `ν`. -/
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_iff [LocallyCompactSpace E]
    [SecondCountableTopology E] [LocallyCompactSpace E'] [SecondCountableTopology E']
    (e : E ≃L[ℝ] E') (hUV : U = e ⁻¹' V) :
    MemLpLoc p U (f ∘ e) μ ↔ MemLpLoc p V f ν := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv μ e (hUV ▸ mapsTo_preimage e V)⟩
  have hVU : MapsTo e.symm V U := fun y hy => by simpa [hUV] using hy
  simpa [Function.comp_def] using h.comp_continuousLinearEquiv ν e.symm hVU

end ContinuousLinearEquivLp

section ContinuousLinearEquivWkp

variable {E : Type u₁} {E' : Type u₂} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {p : ENNReal} {U : Set E} {V : Set E'} {k : ℕ} {f : E' → F}

/-- One inductive step of `TauCeti.MemWkpLoc.comp_continuousLinearEquiv`: combine the weak chain
rule `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv` with the order-`k` transfer `hstep`. -/
private theorem memWkpLoc_succ_comp_continuousLinearEquiv (hf : MemWkpLoc p V (k + 1) f ν)
    (e : E ≃L[ℝ] E') (hUV : MapsTo e U V)
    (hstep : ∀ D : E' → E' →L[ℝ] F, MemWkpLoc p V k D ν → MemWkpLoc p U k (D ∘ e) μ) :
    MemWkpLoc p U (k + 1) (f ∘ e) μ := by
  obtain ⟨hLp, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 hf
  have := hD.completeSpace
  have hint : MapsTo e (interior U) (interior V) := fun x hx =>
    interior_maximal (image_subset_iff.2 (hUV.mono_left interior_subset))
      (e.toHomeomorph.isOpenMap _ isOpen_interior) ⟨x, hx, rfl⟩
  refine memWkpLoc_succ_iff.2 ⟨hLp.comp_continuousLinearEquiv μ e hUV,
    fun x => (D (e x)).comp (e : E →L[ℝ] E'),
    hD.comp_continuousLinearEquiv μ e (by simpa using hint), ?_⟩
  exact (hstep D hDk).clm_comp ((ContinuousLinearMap.compL ℝ E E' F).flip (e : E →L[ℝ] E'))

variable (μ) in
/-- **Linear change of domain in `MemWkpLoc`.** Precomposition with any continuous linear
equivalence `e : E ≃L[ℝ] E'` mapping `U` into `V` carries `MemWkpLoc p V k f ν` into
`MemWkpLoc p U k (f ∘ e) μ`, for every order `k` and arbitrary additive Haar measures `μ` and
`ν`. -/
theorem MemWkpLoc.comp_continuousLinearEquiv (hf : MemWkpLoc p V k f ν) (e : E ≃L[ℝ] E')
    (hUV : MapsTo e U V) : MemWkpLoc p U k (f ∘ e) μ := by
  have aux : ∀ (k : ℕ) {F : Type max u₂ v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E' → F},
      MemWkpLoc p V k f ν → MemWkpLoc p U k (f ∘ e) μ := by
    intro k
    induction k with
    | zero =>
      exact fun hf => memWkpLoc_zero_iff.2 <|
        MemLpLoc.comp_continuousLinearEquiv μ (memWkpLoc_zero_iff.1 hf) e hUV
    | succ k ih => exact fun hf => memWkpLoc_succ_comp_continuousLinearEquiv hf e hUV fun _ => ih
  cases k with
  | zero =>
    exact memWkpLoc_zero_iff.2 <|
      MemLpLoc.comp_continuousLinearEquiv μ (memWkpLoc_zero_iff.1 hf) e hUV
  | succ k => exact memWkpLoc_succ_comp_continuousLinearEquiv hf e hUV fun _ => aux k

/-- **Linear invariance of `MemWkpLoc`.** For any continuous linear equivalence `e : E ≃L[ℝ] E'`
with `U = e ⁻¹' V`, `f ∘ e` lies in `MemWkpLoc p U k · μ` exactly when `f` lies in
`MemWkpLoc p V k · ν`, for every order `k` and arbitrary additive Haar measures `μ` and `ν`. -/
theorem _root_.ContinuousLinearEquiv.memWkpLoc_comp_iff (e : E ≃L[ℝ] E') (hUV : U = e ⁻¹' V) :
    MemWkpLoc p U k (f ∘ e) μ ↔ MemWkpLoc p V k f ν := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv μ e (hUV ▸ mapsTo_preimage e V)⟩
  have hVU : MapsTo e.symm V U := fun y hy => by simpa [hUV] using hy
  simpa [Function.comp_def] using h.comp_continuousLinearEquiv ν e.symm hVU

end ContinuousLinearEquivWkp

end TauCeti
