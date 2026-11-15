/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The bundled Sobolev embedding `H^s(E, F) →L[ℂ] C₀(E, F)`

For a finite-dimensional real inner product space `E`, a complex Hilbert space `F` and a real
order `s > dim E / 2`, every element of the Bessel-potential space `H^s(E, F)` agrees almost
everywhere with a continuous function vanishing at infinity
(`TemperedDistribution.MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`). Because two continuous
functions that agree almost everywhere with respect to Lebesgue measure coincide everywhere, this
representative is unique and depends complex-linearly on the Sobolev function.

This file bundles the representative as a continuous linear map
`BesselPotentialSpace.toZeroAtInfty : H^s(E, F) →L[ℂ] C₀(E, F)`, with operator norm bounded by the
`L²` norm of `(1 + ‖ξ‖ ^ 2) ^ (-s / 2)`, and records that on `H^s(E) = H^s(E, ℂ)` it turns the
algebra product `BesselPotentialSpace.mulCLM` into the pointwise product on `C₀(E, ℂ)`.

## Main declarations

* `BesselPotentialSpace.toZeroAtInfty`: the Sobolev embedding `H^s(E, F) →L[ℂ] C₀(E, F)` for
  `2s > dim E`.
* `BesselPotentialSpace.coeFn_toLp_inclusion_ae_eq_toZeroAtInfty`,
  `BesselPotentialSpace.toZeroAtInfty_eq_iff`: `toZeroAtInfty hs u` is the unique function in
  `C₀(E, F)` agreeing almost everywhere with the `L²` function of `u`.
* `BesselPotentialSpace.toZeroAtInfty_injective`: the continuous representative determines the
  Sobolev function.
* `BesselPotentialSpace.opNorm_toZeroAtInfty_le`: the operator norm bound
  `‖toZeroAtInfty hs‖ ≤ ‖(1 + ‖ξ‖ ^ 2) ^ (-s / 2)‖₂`.
* `BesselPotentialSpace.toZeroAtInfty_mulCLM`: on `H^s(E)`, the embedding preserves multiplication.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3.
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1.
-/

public section

noncomputable section

open MeasureTheory Module TemperedDistribution
open scoped ENNReal FourierTransform SchwartzMap ZeroAtInfty BesselPotentialSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace BesselPotentialSpace

section Hilbert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {r s : ℝ}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem nonneg_of_finrank_lt (hs : finrank ℝ E < 2 * s) : 0 ≤ s := by
  have := (finrank ℝ E).cast_nonneg (α := ℝ)
  linarith

/-- Two continuous functions vanishing at infinity that represent the same Sobolev function
coincide. -/
private theorem eq_of_ae_eq {h : 0 ≤ s} {u : H^{s}(E, F)} {g g' : C₀(E, F)}
    (hg : ⇑(inclusion h u).toLp =ᵐ[volume] g) (hg' : ⇑(inclusion h u).toLp =ᵐ[volume] g') :
    g = g' :=
  ZeroAtInftyContinuousMap.ext <| congrFun <|
    (Continuous.ae_eq_iff_eq (volume : Measure E) g.continuous g'.continuous).mp
      (hg.symm.trans hg')

/-- The continuous representative vanishing at infinity of `u ∈ H^s(E, F)`, as a complex-linear
map. -/
private def toZeroAtInftyₗ (hs : finrank ℝ E < 2 * s) : H^{s}(E, F) →ₗ[ℂ] C₀(E, F) where
  toFun u :=
    ((memSobolev_toLp_inclusion (nonneg_of_finrank_lt hs) u
      ).exists_zeroAtInftyContinuousMap_ae_eq hs).choose
  map_add' u v := by
    have h := nonneg_of_finrank_lt hs
    refine eq_of_ae_eq
      ((memSobolev_toLp_inclusion h (u + v)).exists_zeroAtInftyContinuousMap_ae_eq hs).choose_spec
      ?_
    filter_upwards [coeFn_toLp_inclusion_add h u v,
      ((memSobolev_toLp_inclusion h u).exists_zeroAtInftyContinuousMap_ae_eq hs).choose_spec,
      ((memSobolev_toLp_inclusion h v).exists_zeroAtInftyContinuousMap_ae_eq hs).choose_spec]
      with x hadd hu hv
    rw [hadd, Pi.add_apply, hu, hv, _root_.add_apply]
  map_smul' c u := by
    have h := nonneg_of_finrank_lt hs
    refine eq_of_ae_eq
      ((memSobolev_toLp_inclusion h (c • u)).exists_zeroAtInftyContinuousMap_ae_eq hs).choose_spec
      ?_
    filter_upwards [coeFn_toLp_inclusion_smul h c u,
      ((memSobolev_toLp_inclusion h u).exists_zeroAtInftyContinuousMap_ae_eq hs).choose_spec]
      with x hsmul hu
    rw [hsmul, Pi.smul_apply, hu, RingHom.id_apply, _root_.smul_apply]

private theorem coeFn_toLp_inclusion_ae_eq_toZeroAtInftyₗ (hs : finrank ℝ E < 2 * s)
    (u : H^{s}(E, F)) :
    ⇑(inclusion (nonneg_of_finrank_lt hs) u).toLp =ᵐ[volume] toZeroAtInftyₗ hs u :=
  ((memSobolev_toLp_inclusion (nonneg_of_finrank_lt hs) u
    ).exists_zeroAtInftyContinuousMap_ae_eq hs).choose_spec

private theorem norm_toZeroAtInftyₗ_apply_le (hs : finrank ℝ E < 2 * s) (u : H^{s}(E, F))
    (x : E) :
    ‖toZeroAtInftyₗ hs u x‖ ≤
      (eLpNorm (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 volume).toReal * ‖u‖ := by
  have h := nonneg_of_finrank_lt hs
  have hu := memSobolev_toLp_inclusion h u
  obtain ⟨v, hv⟩ := hu.fourier_memL1 hs
  -- Identify the continuous representative with `𝓕⁻ v`, then bound the Fourier integral by `‖v‖₁`.
  have heq := Lp.eq_fourierInv_of_ae_eq hv (map_continuous (toZeroAtInftyₗ hs u))
    (coeFn_toLp_inclusion_ae_eq_toZeroAtInftyₗ hs u)
  rw [congrFun heq x, Real.fourierInv_eq_fourier_comp_neg]
  refine (Real.norm_fourier_le_integral_norm _ x).trans ?_
  rw [integral_neg_eq_self (fun ξ : E ↦ ‖(v : E → F) ξ‖)]
  have hbound := hu.integral_norm_pow_mul_norm_le (j := 0) (by simpa using hs) hv
  simpa only [pow_zero, one_mul, Nat.cast_zero, sub_zero,
    toBesselPotentialSpace_memSobolev_toLp_inclusion] using hbound

/-- **The Sobolev embedding `H^s(E, F) →L[ℂ] C₀(E, F)`** for `2s > dim E`: the continuous linear
map sending each Bessel-potential function to its unique continuous representative vanishing at
infinity. -/
def toZeroAtInfty (hs : finrank ℝ E < 2 * s) : H^{s}(E, F) →L[ℂ] C₀(E, F) :=
  (toZeroAtInftyₗ hs).mkContinuous
    (eLpNorm (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 volume).toReal fun u ↦ by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦
        norm_toZeroAtInftyₗ_apply_le hs u x

/-- The `L²` function of `u ∈ H^s(E, F)`, `2s > dim E`, agrees almost everywhere with
`toZeroAtInfty hs u`. -/
theorem coeFn_toLp_inclusion_ae_eq_toZeroAtInfty (hs : finrank ℝ E < 2 * s) (h : 0 ≤ s)
    (u : H^{s}(E, F)) :
    ⇑(inclusion h u).toLp =ᵐ[volume] toZeroAtInfty hs u :=
  coeFn_toLp_inclusion_ae_eq_toZeroAtInftyₗ hs u

/-- `toZeroAtInfty hs u` is the unique function in `C₀(E, F)` agreeing almost everywhere with the
`L²` function of `u`. -/
theorem toZeroAtInfty_eq_iff (hs : finrank ℝ E < 2 * s) (h : 0 ≤ s) (u : H^{s}(E, F))
    (g : C₀(E, F)) :
    toZeroAtInfty hs u = g ↔ ⇑(inclusion h u).toLp =ᵐ[volume] g :=
  ⟨fun hg ↦ hg ▸ coeFn_toLp_inclusion_ae_eq_toZeroAtInfty hs h u,
    eq_of_ae_eq (coeFn_toLp_inclusion_ae_eq_toZeroAtInfty hs h u)⟩

/-- Every continuous function agreeing almost everywhere with the `L²` function of `u ∈ H^s(E, F)`
coincides pointwise with `toZeroAtInfty hs u`. -/
theorem coe_toZeroAtInfty_eq_of_ae_eq (hs : finrank ℝ E < 2 * s) {h : 0 ≤ s} {u : H^{s}(E, F)}
    {v : E → F} (hv : Continuous v) (hae : ⇑(inclusion h u).toLp =ᵐ[volume] v) :
    ⇑(toZeroAtInfty hs u) = v :=
  (Continuous.ae_eq_iff_eq (volume : Measure E) (toZeroAtInfty hs u).continuous hv).mp
    ((coeFn_toLp_inclusion_ae_eq_toZeroAtInfty hs h u).symm.trans hae)

/-- The Sobolev embedding `H^s(E, F) → C₀(E, F)` is injective: the continuous representative
determines the Sobolev function. -/
theorem toZeroAtInfty_injective (hs : finrank ℝ E < 2 * s) :
    Function.Injective (toZeroAtInfty (E := E) (F := F) hs) := by
  intro u v huv
  have h := nonneg_of_finrank_lt hs
  refine toLp_inclusion_injective h (Lp.ext ?_)
  exact (coeFn_toLp_inclusion_ae_eq_toZeroAtInfty hs h u).trans
    (huv ▸ (coeFn_toLp_inclusion_ae_eq_toZeroAtInfty hs h v).symm)

/-- Pointwise bound on the continuous representative of `u ∈ H^s(E, F)`. -/
theorem norm_toZeroAtInfty_apply_le (hs : finrank ℝ E < 2 * s) (u : H^{s}(E, F)) (x : E) :
    ‖toZeroAtInfty hs u x‖ ≤
      (eLpNorm (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 volume).toReal * ‖u‖ :=
  norm_toZeroAtInftyₗ_apply_le hs u x

/-- Supremum norm bound on `toZeroAtInfty hs u`. -/
theorem norm_toZeroAtInfty_le (hs : finrank ℝ E < 2 * s) (u : H^{s}(E, F)) :
    ‖toZeroAtInfty hs u‖ ≤
      (eLpNorm (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 volume).toReal * ‖u‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le (by positivity)).2 (norm_toZeroAtInfty_apply_le hs u)

/-- Operator norm bound on the Sobolev embedding `H^s(E, F) →L[ℂ] C₀(E, F)`. -/
theorem opNorm_toZeroAtInfty_le (hs : finrank ℝ E < 2 * s) :
    ‖toZeroAtInfty (E := E) (F := F) hs‖ ≤
      (eLpNorm (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 volume).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- Lowering the Sobolev order does not change the continuous representative. -/
@[simp]
theorem toZeroAtInfty_inclusion (hr : finrank ℝ E < 2 * r) (h : r ≤ s) (u : H^{s}(E, F)) :
    toZeroAtInfty hr (inclusion h u) =
      toZeroAtInfty (hr.trans_le (mul_le_mul_of_nonneg_left h zero_le_two)) u := by
  have hr0 := nonneg_of_finrank_lt hr
  refine (toZeroAtInfty_eq_iff hr hr0 (inclusion h u) _).2 ?_
  rw [inclusion_inclusion h hr0]
  exact coeFn_toLp_inclusion_ae_eq_toZeroAtInfty _ (hr0.trans h) u

/-- On Schwartz functions, `toZeroAtInfty` is the underlying function. -/
@[simp]
theorem coe_toZeroAtInfty_toBesselPotentialSpaceCLM (hs : finrank ℝ E < 2 * s) (φ : 𝓢(E, F)) :
    ⇑(toZeroAtInfty hs (SchwartzMap.toBesselPotentialSpaceCLM s 2 φ)) = ⇑φ := by
  have h := nonneg_of_finrank_lt hs
  refine coe_toZeroAtInfty_eq_of_ae_eq hs (h := h) φ.continuous ?_
  rw [inclusion_toBesselPotentialSpaceCLM, SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero]
  exact φ.coeFn_toLp 2 volume

@[simp]
theorem toZeroAtInfty_toBesselPotentialSpaceCLM_apply (hs : finrank ℝ E < 2 * s) (φ : 𝓢(E, F))
    (x : E) :
    toZeroAtInfty hs (SchwartzMap.toBesselPotentialSpaceCLM s 2 φ) x = φ x :=
  congrFun (coe_toZeroAtInfty_toBesselPotentialSpaceCLM hs φ) x

end Hilbert

section Algebra

variable {s : ℝ}

/-- On `H^s(E)`, `2s > dim E`, the Sobolev embedding into `C₀(E, ℂ)` turns `mulCLM` into pointwise
multiplication. -/
@[simp]
theorem toZeroAtInfty_mulCLM (hs : finrank ℝ E < 2 * s) (u v : H^{s}(E)) :
    toZeroAtInfty hs (mulCLM hs u v) = toZeroAtInfty hs u * toZeroAtInfty hs v := by
  have h := nonneg_of_finrank_lt hs
  refine (toZeroAtInfty_eq_iff hs h _ _).2 ?_
  filter_upwards [coeFn_toLp_inclusion_mulCLM hs h u v,
    coeFn_toLp_inclusion_ae_eq_toZeroAtInfty hs h u,
    coeFn_toLp_inclusion_ae_eq_toZeroAtInfty hs h v] with x hmul hu hv
  rw [hmul, hu, hv, _root_.mul_apply]

theorem toZeroAtInfty_mulCLM_apply (hs : finrank ℝ E < 2 * s) (u v : H^{s}(E)) (x : E) :
    toZeroAtInfty hs (mulCLM hs u v) x = toZeroAtInfty hs u x * toZeroAtInfty hs v x := by
  rw [toZeroAtInfty_mulCLM, _root_.mul_apply]

end Algebra

end BesselPotentialSpace
