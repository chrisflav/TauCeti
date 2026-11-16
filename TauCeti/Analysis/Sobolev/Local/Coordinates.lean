/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Complex.OperatorNorm

/-!
# Coordinates of local Sobolev maps

A map into a finite-dimensional real normed space is locally Sobolev of order `k` if and
only if all its coordinates in a finite basis are (`Module.Basis.memWkpLoc_iff`). The same
criterion holds for local `Lᵖ` membership on any topological measure space
(`Module.Basis.memLpLoc_iff`). These criteria allow scalar local estimates to be applied to
vector-valued maps without choosing compatible representatives of their iterated weak derivatives.

The criteria include the zero-dimensional codomain, order zero, and the exponent infinity.
They also show that testing one basis is equivalent to testing every basis.

Dually, for a finite basis `b` of the domain `E`, a weak derivative `D : E → E →L[ℝ] F` lies in
`W^{k,p}_loc(U)` exactly when every directional derivative `x ↦ D x (b i)` does, yielding
`Module.Basis.memWkpLoc_succ_iff` and `Module.Basis.memWkpLoc_one_iff` for arbitrary normed
codomains `F`. For maps on `ℂ`, `TauCeti.memWkpLoc_succ_iff_apply_one_apply_I` specializes this to
`z ↦ D z 1` and `z ↦ D z I`.

On an open set, the precise representative of a locally `Lᵖ` map is reconstructed from the
precise representatives of its coordinates wherever these are continuous
(`Module.Basis.eqOn_preciseRepresentative_sum_repr`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (vector-valued Sobolev spaces).
-/

public noncomputable section

open TauCeti MeasureTheory TopologicalSpace

namespace Module.Basis

section CodomainLp

variable {E F : Type*} [TopologicalSpace E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι]
  {p : ENNReal} {U : Set E} {f : E → F} {μ : Measure E}

/-- Local `Lᵖ` membership can be tested in any finite basis of the codomain. No completeness of the
codomain is needed. -/
theorem memLpLoc_iff (b : Module.Basis ι ℝ F) :
    MemLpLoc p U f μ ↔ ∀ i, MemLpLoc p U (fun x => b.repr (f x) i) μ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  refine ⟨fun h i => h.clm_comp
    ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap), fun h => ?_⟩
  have hs : MemLpLoc p U (fun x => ∑ i, b.repr (f x) i • b i) μ :=
    MemLpLoc.sum _ fun i _ => (h i).smul_const (b i)
  simpa only [b.sum_repr] using hs

end CodomainLp

section CodomainAndDomainWkp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Finite ι] {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} {μ : Measure E}

/-- Local Sobolev membership of every order can be tested in any finite basis of the codomain.
Scalar coordinate witnesses may be chosen independently; finite sums reconstruct the map
in the same Sobolev class. -/
theorem memWkpLoc_iff (b : Module.Basis ι ℝ F) :
    MemWkpLoc p U k f μ ↔ ∀ i, MemWkpLoc p U k (fun x => b.repr (f x) i) μ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemWkpLoc p U k (fun x => ∑ i, b.repr (f x) i • b i) μ :=
      MemWkpLoc.sum _ fun i _ => (h i).smul_const (b i)
    simpa only [b.sum_repr] using hs

/-- Local Sobolev membership at successor order can be tested along any finite basis of the domain:
a map lies in `W^{k+1,p}_loc(U)` exactly when it is locally `Lᵖ` on `U` and has a weak derivative
`D` on `interior U` whose directional derivatives `x ↦ D x (b i)` lie in `W^{k,p}_loc(U)`. -/
theorem memWkpLoc_succ_iff (b : Module.Basis ι ℝ E) :
    MemWkpLoc p U (k + 1) f μ ↔ MemLpLoc p U f μ ∧ ∃ D : E → E →L[ℝ] F,
      HasWeakFDerivOn μ (Opens.interior U) f D ∧
        ∀ i, MemWkpLoc p U k (fun x => D x (b i)) μ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  constructor
  · intro h
    obtain ⟨hf, D, hD, hDk⟩ := TauCeti.memWkpLoc_succ_iff.1 h
    have := hD.completeSpace
    exact ⟨hf, D, hD, fun i => hDk.clm_comp (ContinuousLinearMap.apply ℝ F (b i))⟩
  · rintro ⟨hf, D, hD, hDk⟩
    have := hD.completeSpace
    refine TauCeti.memWkpLoc_succ_iff.2 ⟨hf, D, hD, ?_⟩
    let ℓ : ι → E →L[ℝ] ℝ := fun i =>
      (ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap
    have hD_eq : D = fun x => ∑ i, (ContinuousLinearMap.smulRightL ℝ E F (ℓ i)) (D x (b i)) := by
      ext x v
      simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRightL_apply_apply,
        ContinuousLinearMap.smulRight_apply, ℓ, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearEquiv.coe_coe,
        Module.Basis.equivFunL_apply, ← map_smul, ← map_sum, b.sum_repr]
    rw [hD_eq]
    exact MemWkpLoc.sum _ fun i _ => (hDk i).clm_comp (ContinuousLinearMap.smulRightL ℝ E F (ℓ i))

/-- Order-one local Sobolev membership can be tested along any finite basis of the domain. -/
theorem memWkpLoc_one_iff (b : Module.Basis ι ℝ E) :
    MemWkpLoc p U 1 f μ ↔ MemLpLoc p U f μ ∧ ∃ D : E → E →L[ℝ] F,
      HasWeakFDerivOn μ (Opens.interior U) f D ∧
        ∀ i, MemLpLoc p U (fun x => D x (b i)) μ := by
  simpa only [memWkpLoc_zero_iff] using
    b.memWkpLoc_succ_iff (p := p) (U := U) (k := 0) (f := f) (μ := μ)

end CodomainAndDomainWkp

end Module.Basis

namespace Module.Basis

open TauCeti.MeasureTheory

variable {E F : Type*} [PseudoMetricSpace E] [SecondCountableTopology E] [LocallyCompactSpace E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsUnifLocDoublingMeasure μ]
  [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] {p : ENNReal} {Ω : Opens E} {f : E → F}

/-- On an open set `Ω`, the precise representative of a locally `Lᵖ` map, `1 ≤ p`, whose
coordinates in a finite basis `b` have precise representatives continuous on `Ω`, is the
combination of those precise representatives with the vectors of `b`. -/
theorem eqOn_preciseRepresentative_sum_repr (b : Module.Basis ι ℝ F) (hp : 1 ≤ p)
    (hf : MemLpLoc p Ω f μ)
    (hc : ∀ i, ContinuousOn (preciseRepresentative μ fun z => b.repr (f z) i) Ω) :
    Set.EqOn (preciseRepresentative μ f)
      (fun z => ∑ i, preciseRepresentative μ (fun w => b.repr (f w) i) z • b i) Ω := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  refine eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    (hf.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed) ?_
    (continuousOn_finsetSum _ fun i _ => (hc i).smul continuousOn_const)
  have hcoord : ∀ i, (fun z => b.repr (f z) i) =ᵐ[μ.restrict Ω]
      preciseRepresentative μ fun z => b.repr (f z) i := fun i =>
    (b.memLpLoc_iff.1 hf i).ae_eq_preciseRepresentative hp
  filter_upwards [ae_all_iff.2 hcoord] with z hz
  conv_lhs => rw [← b.sum_repr (f z)]
  exact Finset.sum_congr rfl fun i _ => by rw [← hz i]

end Module.Basis

/-! ### Local Sobolev classes through the two partial derivatives -/

namespace TauCeti

open Complex TopologicalSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ENNReal} {U : Set ℂ} {k : ℕ}

/-- **Assembling a weak derivative from its partial derivatives.** A locally `L^q` map with a
weak derivative `D` on the interior of `U` whose partial derivatives `z ↦ D z 1` and `z ↦ D z I`
lie in `W^{k,q}_loc(U)` lies in `W^{k+1,q}_loc(U)`. The derivative `D` is rebuilt from its two
partial derivatives with `ContinuousLinearMap.smulRightL`. -/
theorem MemLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn {ξ : ℂ → V} {D : ℂ → ℂ →L[ℝ] V}
    (hξ : MemLpLoc q U ξ) (hD : HasWeakFDerivOn volume (Opens.interior U) ξ D)
    (h1 : MemWkpLoc q U k fun z => D z 1) (hI : MemWkpLoc q U k fun z => D z I) :
    MemWkpLoc q U (k + 1) ξ := by
  have := hD.completeSpace
  refine memWkpLoc_succ_iff.2 ⟨hξ, D, hD, ?_⟩
  rw [ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM D]
  exact (h1.clm_comp _).add (hI.clm_comp _)

/-- **Local Sobolev classes through partial derivatives.** A map lies in `W^{k+1,q}_loc(U)`
exactly when it is locally `L^q` on `U` and has a weak derivative on the interior of `U` whose
partial derivatives `z ↦ D z 1` and `z ↦ D z I` lie in `W^{k,q}_loc(U)`. -/
theorem memWkpLoc_succ_iff_apply_one_apply_I {ξ : ℂ → V} :
    MemWkpLoc q U (k + 1) ξ ↔ MemLpLoc q U ξ ∧ ∃ D : ℂ → ℂ →L[ℝ] V,
      HasWeakFDerivOn volume (Opens.interior U) ξ D ∧
        (MemWkpLoc q U k fun z => D z 1) ∧ MemWkpLoc q U k fun z => D z I := by
  refine ⟨fun h => ?_, fun ⟨hξ, D, hD, h1, hI⟩ =>
    hξ.memWkpLoc_succ_of_hasWeakFDerivOn hD h1 hI⟩
  obtain ⟨hξ, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 h
  have := hD.completeSpace
  exact ⟨hξ, D, hD, hDk.clm_comp (ContinuousLinearMap.apply ℝ V 1),
    hDk.clm_comp (ContinuousLinearMap.apply ℝ V I)⟩

end TauCeti
