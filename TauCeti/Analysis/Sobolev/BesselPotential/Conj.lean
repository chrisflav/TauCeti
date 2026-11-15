/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty
public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Complex conjugation and the real subspace of `H^{s,p}(E)`

Mathlib defines the Bessel-potential space `H^{s,p}(E, F)` as a complex normed space, with scalar
multiplication `BesselPotentialSpace.instSMul` for any scalar type `R` acting through `ℂ`. This
file first registers the matching `IsScalarTower R ℂ`, `SMulCommClass`, `Module R` and
`NormedSpace R` instances on `H^{s,p}(E, F)` so that restricting scalars to `ℝ` uses the same
action on `toDistr` and `toLp`.

On complex-valued functions (`F = ℂ`), pointwise complex conjugation acts on Schwartz space
`𝓢(E, ℂ)` as a real-linear continuous equivalence `SchwartzMap.conjCLE` exchanging the Fourier
transform and its inverse. Dualizing `T ↦ (φ ↦ star (T (star ∘ φ)))` gives a real-linear continuous
equivalence `TemperedDistribution.conjCLE` on `𝓢'(E, ℂ)`. Because the Bessel symbol
`ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)` is real and even, `TemperedDistribution.conjCLE` commutes with
`besselPotential` at every real order `s`. Consequently it restricts on `H^{s,p}(E)` to an
involutive real-linear isometry equivalence `BesselPotentialSpace.conjLIE`.

Its fixed-point locus `BesselPotentialSpace.realSubmodule E s p` is the closed real Banach subspace
of real-valued Bessel-potential distributions, providing the Lie-algebra model space for
circle-valued Sobolev gauge groups.

## Main declarations

* `SchwartzMap.conjCLE`: pointwise complex conjugation `𝓢(E, ℂ) ≃L[ℝ] 𝓢(E, ℂ)`, exchanging `𝓕`
  and `𝓕⁻` (`SchwartzMap.conjCLE_fourier`, `SchwartzMap.conjCLE_fourierInv`).
* `TemperedDistribution.conjCLE`: complex conjugation `𝓢'(E, ℂ) ≃L[ℝ] 𝓢'(E, ℂ)`, commuting with
  `besselPotential` (`TemperedDistribution.besselPotential_conjCLE`).
* `BesselPotentialSpace.conjLIE`: complex conjugation `H^{s,p}(E) ≃ₗᵢ[ℝ] H^{s,p}(E)`, compatible
  with order inclusions, `toZeroAtInfty` and `mulCLM`.
* `BesselPotentialSpace.reCLM`, `BesselPotentialSpace.imCLM`: the real and imaginary part
  projections `H^{s,p}(E) →L[ℝ] H^{s,p}(E)`.
* `BesselPotentialSpace.realSubmodule`, `BesselPotentialSpace.RealSubspace`: the closed real
  subspace `{u ∈ H^{s,p}(E) | conj u = u}` and its bundled real Banach space carrier, together
  with compatibility with `TemperedDistribution.realSobolevFunctions`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3.
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1.
-/

public section

noncomputable section

open MeasureTheory Module FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap ZeroAtInfty BesselPotentialSpace ComplexConjugate

namespace BesselPotentialSpace

section RealScalars

variable {E F R : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

instance [SMul R ℂ] [SMul R 𝓢'(E, F)] [SMul R (Lp F p (volume : Measure E))]
    [IsScalarTower R ℂ 𝓢'(E, F)] [IsScalarTower R ℂ (Lp F p (volume : Measure E))] :
    IsScalarTower R ℂ H^{s, p}(E, F) where
  smul_assoc c z f := ext (smul_assoc c z f.toDistr)

instance [SMul R ℂ] [SMul R 𝓢'(E, F)] [SMul R (Lp F p (volume : Measure E))]
    [IsScalarTower R ℂ 𝓢'(E, F)] [IsScalarTower R ℂ (Lp F p (volume : Measure E))]
    [SMulCommClass R ℂ 𝓢'(E, F)] : SMulCommClass R ℂ H^{s, p}(E, F) where
  smul_comm c z f := ext (smul_comm c z f.toDistr)

instance [SMul R ℂ] [SMul R 𝓢'(E, F)] [SMul R (Lp F p (volume : Measure E))]
    [IsScalarTower R ℂ 𝓢'(E, F)] [IsScalarTower R ℂ (Lp F p (volume : Measure E))]
    [SMulCommClass ℂ R 𝓢'(E, F)] : SMulCommClass ℂ R H^{s, p}(E, F) where
  smul_comm z c f := ext (smul_comm z c f.toDistr)

-- Priority 950 sits below `BesselPotentialSpace`'s `Module ℂ` (1000) and above
-- `Module.complexToReal` (900), ensuring `Module ℝ` agrees definitionally with `instSMul`.
/-- Scalar module structure on `H^{s,p}(E, F)` compatible with `BesselPotentialSpace.instSMul`. -/
instance (priority := 950) instModuleOfIsScalarTower [Semiring R] [SMul R ℂ] [Module R 𝓢'(E, F)]
    [SMul R (Lp F p (volume : Measure E))]
    [IsScalarTower R ℂ 𝓢'(E, F)] [IsScalarTower R ℂ (Lp F p (volume : Measure E))] :
    Module R H^{s, p}(E, F) where
  one_smul f := ext (one_smul R f.toDistr)
  mul_smul a b f := ext (mul_smul a b f.toDistr)
  smul_zero a := ext (smul_zero a)
  smul_add a f g := ext (smul_add a f.toDistr g.toDistr)
  add_smul a b f := ext (add_smul a b f.toDistr)
  zero_smul f := ext (zero_smul R f.toDistr)

/-- Normed-space structure over `R` (in particular `ℝ`) on `H^{s,p}(E, F)` compatible with
`BesselPotentialSpace.instSMul`. -/
instance (priority := 950) instNormedSpaceOfIsScalarTower [NormedField R] [SMul R ℂ]
    [Module R 𝓢'(E, F)] [NormedSpace R F] [IsScalarTower R ℂ 𝓢'(E, F)] [IsScalarTower R ℂ F] :
    NormedSpace R H^{s, p}(E, F) where
  norm_smul_le c f := by
    rw [← norm_toLp_eq, ← norm_toLp_eq, toLp_smul]
    exact norm_smul_le c f.toLp

end RealScalars

end BesselPotentialSpace

namespace SchwartzMap

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise complex conjugation on Schwartz space `𝓢(E, ℂ)`, as a continuous real-linear
equivalence. -/
def conjCLE : 𝓢(E, ℂ) ≃L[ℝ] 𝓢(E, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ))
    (postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ))
    (fun φ ↦ by ext x; simp [postcompCLM_apply])
    (fun φ ↦ by ext x; simp [postcompCLM_apply])

@[simp]
theorem conjCLE_apply (φ : 𝓢(E, ℂ)) (x : E) : conjCLE φ x = star (φ x) := by
  rfl

@[simp]
theorem conjCLE_conjCLE (φ : 𝓢(E, ℂ)) : conjCLE (conjCLE φ) = φ :=
  conjCLE.left_inv φ

@[simp]
theorem conjCLE_symm : (conjCLE (E := E)).symm = conjCLE := by
  rfl

theorem conjCLE_smul (c : ℂ) (φ : 𝓢(E, ℂ)) : conjCLE (c • φ) = star c • conjCLE φ := by
  ext x
  simp

/-- Multiplying by a real function of temperate growth commutes with complex conjugation on
`𝓢(E, ℂ)`. -/
theorem conjCLE_smulLeftCLM_ofReal {g : E → ℝ} (hg : g.HasTemperateGrowth) (φ : 𝓢(E, ℂ)) :
    conjCLE (smulLeftCLM ℂ (fun x ↦ (g x : ℂ)) φ) =
      smulLeftCLM ℂ (fun x ↦ (g x : ℂ)) (conjCLE φ) := by
  have hg' : (fun x ↦ (g x : ℂ)).HasTemperateGrowth := Complex.ofRealCLM.hasTemperateGrowth.comp hg
  ext x
  simp [smulLeftCLM_apply_apply hg']

end Basic

section Fourier

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- Complex conjugation on Schwartz space turns the Fourier transform into the inverse Fourier
transform: `conj (∫ e^{-2πi⟪x, ξ⟫} φ(x) dx) = ∫ e^{2πi⟪x, ξ⟫} conj(φ(x)) dx`. -/
theorem conjCLE_fourier (φ : 𝓢(E, ℂ)) : conjCLE (𝓕 φ) = 𝓕⁻ (conjCLE φ) := by
  ext ξ
  rw [conjCLE_apply, fourier_coe, fourierInv_coe, Real.fourier_eq, Real.fourierInv_eq,
    Complex.star_def, ← integral_conj]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp [Circle.smul_def, mul_comm]

/-- Complex conjugation on Schwartz space turns the inverse Fourier transform into the Fourier
transform. -/
theorem conjCLE_fourierInv (φ : 𝓢(E, ℂ)) : conjCLE (𝓕⁻ φ) = 𝓕 (conjCLE φ) := by
  apply conjCLE.injective
  rw [conjCLE_conjCLE, conjCLE_fourier, conjCLE_conjCLE]

/-- For a real even symbol `g`, the adjoint Bessel/Fourier multiplier `φ ↦ 𝓕 (g • 𝓕⁻ φ)` commutes
with `conjCLE`. -/
theorem conjCLE_fourier_smulLeftCLM_fourierInv_of_even {g : E → ℝ} (hg : g.HasTemperateGrowth)
    (heven : ∀ x, g (-x) = g x) (φ : 𝓢(E, ℂ)) :
    conjCLE (𝓕 (smulLeftCLM ℂ (fun x ↦ (g x : ℂ)) (𝓕⁻ φ))) =
      𝓕 (smulLeftCLM ℂ (fun x ↦ (g x : ℂ)) (𝓕⁻ (conjCLE φ))) := by
  have hg' : (fun x ↦ (g x : ℂ)).HasTemperateGrowth := Complex.ofRealCLM.hasTemperateGrowth.comp hg
  have h1 : conjCLE (𝓕 (smulLeftCLM ℂ (fun x ↦ (g x : ℂ)) (𝓕⁻ φ))) =
      𝓕⁻ (smulLeftCLM ℂ (fun x ↦ (g x : ℂ)) (𝓕 (conjCLE φ))) := by
    rw [conjCLE_fourier, conjCLE_smulLeftCLM_ofReal hg, conjCLE_fourierInv]
  rw [h1]
  ext y
  rw [fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg, fourier_coe]
  refine congrArg (fun f : E → ℂ ↦ 𝓕 f y) (funext fun ξ ↦ ?_)
  simp [smulLeftCLM_apply_apply hg', fourierInv_coe, Real.fourierInv_eq_fourier_neg, fourier_coe,
    heven]

end Fourier

end SchwartzMap

namespace TemperedDistribution

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Complex conjugation of a tempered distribution `T ∈ 𝓢'(E, ℂ)`, defined by
`(conjAux T) φ = star (T (star ∘ φ))`. -/
private def conjAux (T : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ) :=
  ContinuousLinearMap.mk
    { toFun φ := star (T (SchwartzMap.conjCLE φ))
      map_add' φ ψ := by simp [map_add]
      map_smul' c φ := by simp [SchwartzMap.conjCLE_smul] }
    ((Complex.conjCLE.continuous.comp T.continuous).comp SchwartzMap.conjCLE.continuous)

private theorem conjAux_apply (T : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) :
    conjAux T φ = star (T (SchwartzMap.conjCLE φ)) :=
  rfl

private def conjCLM : 𝓢'(E, ℂ) →L[ℝ] 𝓢'(E, ℂ) where
  toFun := conjAux
  map_add' S T := by ext φ; simp [conjAux_apply]
  map_smul' r T := by ext φ; simp [conjAux_apply, Complex.real_smul, Complex.conj_ofReal]
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval fun φ ↦
    Complex.conjCLE.continuous.comp
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ (SchwartzMap.conjCLE φ)).continuous

/-- Complex conjugation on tempered distributions `𝓢'(E, ℂ)`, as an involutive real-linear
continuous equivalence characterized by `(conjCLE T) φ = star (T (SchwartzMap.conjCLE φ))`. -/
def conjCLE : 𝓢'(E, ℂ) ≃L[ℝ] 𝓢'(E, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse conjCLM conjCLM
    (fun T ↦ by ext φ; simp [conjCLM, conjAux_apply])
    (fun T ↦ by ext φ; simp [conjCLM, conjAux_apply])

@[simp]
theorem conjCLE_apply (T : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) :
    conjCLE T φ = star (T (SchwartzMap.conjCLE φ)) := by
  rfl

@[simp]
theorem conjCLE_conjCLE (T : 𝓢'(E, ℂ)) : conjCLE (conjCLE T) = T :=
  conjCLE.left_inv T

@[simp]
theorem conjCLE_symm : (conjCLE (E := E)).symm = conjCLE := by
  rfl

theorem conjCLE_smul (c : ℂ) (T : 𝓢'(E, ℂ)) : conjCLE (c • T) = star c • conjCLE T := by
  ext φ
  simp

end Basic

section Fourier

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- On an `Lᵖ` function, distributional complex conjugation agrees with pointwise complex
conjugation in `Lᵖ`. -/
theorem conjCLE_toTemperedDistribution_Lp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Lp ℂ p (volume : Measure E)) :
    conjCLE (u : 𝓢'(E, ℂ)) =
      ((Complex.conjCLE.toContinuousLinearMap.compLp u : Lp ℂ p (volume : Measure E)) :
        𝓢'(E, ℂ)) := by
  ext φ
  rw [conjCLE_apply, Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
    Complex.star_def, ← integral_conj]
  refine integral_congr_ae
    ((Complex.conjCLE.toContinuousLinearMap.coeFn_compLp u).mono fun x hx ↦ ?_)
  simp [hx]

/-- The Bessel potential operator commutes with complex conjugation of tempered distributions,
since its symbol `ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)` is real and even. -/
@[simp]
theorem besselPotential_conjCLE (s : ℝ) (T : 𝓢'(E, ℂ)) :
    besselPotential E ℂ s (conjCLE T) = conjCLE (besselPotential E ℂ s T) := by
  ext φ
  simp only [besselPotential, fourierMultiplierCLM_apply_apply, conjCLE_apply]
  rw [SchwartzMap.conjCLE_fourier_smulLeftCLM_fourierInv_of_even
    (g := fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)) (by fun_prop) (fun x ↦ by simp)]

end Fourier

end TemperedDistribution

namespace BesselPotentialSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

section Conj

variable {r s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def conjMap (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : H^{s, p}(E)) : H^{s, p}(E) where
  toDistr := TemperedDistribution.conjCLE u.toDistr
  toLp := Complex.conjCLE.toContinuousLinearMap.compLp u.toLp
  bessel_toDistr_eq_toLp := by
    rw [besselPotential_conjCLE, u.bessel_toDistr_eq_toLp, conjCLE_toTemperedDistribution_Lp]

private theorem conjMap_conjMap (u : H^{s, p}(E)) :
    conjMap s p (conjMap s p u) = u :=
  ext (TemperedDistribution.conjCLE_conjCLE u.toDistr)

private theorem norm_conjMap_le (u : H^{s, p}(E)) : ‖conjMap s p u‖ ≤ ‖u‖ := by
  rw [← norm_toLp_eq, ← norm_toLp_eq]
  exact (ContinuousLinearMap.norm_compLp_le _ u.toLp).trans
    (mul_le_of_le_one_left (norm_nonneg u.toLp)
      Complex.conjLIE.toLinearIsometry.norm_toContinuousLinearMap_le)

variable (E s p) in
/-- **Complex conjugation on `H^{s,p}(E)`**: the involutive real-linear isometry equivalence
acting by `TemperedDistribution.conjCLE` on distributions and pointwise conjugation on `toLp`. -/
def conjLIE : H^{s, p}(E) ≃ₗᵢ[ℝ] H^{s, p}(E) where
  toFun := conjMap s p
  invFun := conjMap s p
  left_inv := conjMap_conjMap
  right_inv := conjMap_conjMap
  map_add' u v := ext (map_add TemperedDistribution.conjCLE u.toDistr v.toDistr)
  map_smul' c u := ext (map_smul TemperedDistribution.conjCLE c u.toDistr)
  norm_map' u := le_antisymm (norm_conjMap_le u)
    (by simpa [conjMap_conjMap] using norm_conjMap_le (conjMap s p u))

@[simp]
theorem toDistr_conjLIE (u : H^{s, p}(E)) :
    (conjLIE E s p u).toDistr = TemperedDistribution.conjCLE u.toDistr := by
  rfl

@[simp]
theorem toLp_conjLIE (u : H^{s, p}(E)) :
    (conjLIE E s p u).toLp = Complex.conjCLE.toContinuousLinearMap.compLp u.toLp := by
  rfl

@[simp]
theorem conjLIE_conjLIE (u : H^{s, p}(E)) : conjLIE E s p (conjLIE E s p u) = u :=
  (conjLIE E s p).left_inv u

@[simp]
theorem conjLIE_symm : (conjLIE E s p).symm = conjLIE E s p := by
  rfl

theorem conjLIE_smul (c : ℂ) (u : H^{s, p}(E)) :
    conjLIE E s p (c • u) = star c • conjLIE E s p u :=
  ext (TemperedDistribution.conjCLE_smul c u.toDistr)

/-- Lowering the Sobolev order commutes with complex conjugation. -/
@[simp]
theorem inclusion_conjLIE (h : r ≤ s) (u : H^{s}(E)) :
    inclusion h (conjLIE E s 2 u) = conjLIE E r 2 (inclusion h u) :=
  ext (by simp)

/-- The `L²` function of `inclusion h (conjLIE E s 2 u)` is almost everywhere the complex
conjugate of that of `inclusion h u`. -/
theorem coeFn_toLp_inclusion_conjLIE (h : r ≤ s) (u : H^{s}(E)) :
    ⇑(inclusion h (conjLIE E s 2 u)).toLp =ᵐ[volume] fun x ↦ star ((inclusion h u).toLp x) := by
  rw [inclusion_conjLIE, toLp_conjLIE]
  exact Complex.conjCLE.toContinuousLinearMap.coeFn_compLp (inclusion h u).toLp

/-- On `H^s(E)`, `2s > dim E`, the Sobolev embedding into `C₀(E, ℂ)` turns `conjLIE` into the
`Star` operation (pointwise complex conjugation). -/
@[simp]
theorem toZeroAtInfty_conjLIE (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) :
    toZeroAtInfty hs (conjLIE E s 2 u) = star (toZeroAtInfty hs u) := by
  have h0 : 0 ≤ s := by have := (finrank ℝ E).cast_nonneg (α := ℝ); linarith
  refine (toZeroAtInfty_eq_iff hs h0 _ _).2 ?_
  filter_upwards [coeFn_toLp_inclusion_conjLIE h0 u,
    coeFn_toLp_inclusion_ae_eq_toZeroAtInfty hs h0 u] with x hconj hu
  rw [hconj, hu, ZeroAtInftyContinuousMap.star_apply]

theorem toZeroAtInfty_conjLIE_apply (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) (x : E) :
    toZeroAtInfty hs (conjLIE E s 2 u) x = star (toZeroAtInfty hs u x) := by
  rw [toZeroAtInfty_conjLIE, ZeroAtInftyContinuousMap.star_apply]

/-- Complex conjugation on the Sobolev algebra `H^s(E)`, `2s > dim E`, is multiplicative. -/
theorem conjLIE_mulCLM (hs : finrank ℝ E < 2 * s) (u v : H^{s}(E)) :
    conjLIE E s 2 (mulCLM hs u v) = mulCLM hs (conjLIE E s 2 u) (conjLIE E s 2 v) := by
  apply toZeroAtInfty_injective hs
  simp

end Conj

section RealPartAndSubmodule

variable {r s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (E s p) in
/-- The real-part projection `u ↦ (u + conj u) / 2` on `H^{s,p}(E)`, as a continuous real-linear
map. -/
def reCLM : H^{s, p}(E) →L[ℝ] H^{s, p}(E) :=
  (2⁻¹ : ℝ) • (.id ℝ H^{s, p}(E) + (conjLIE E s p).toContinuousLinearEquiv.toContinuousLinearMap)

variable (E s p) in
/-- The imaginary-part projection `u ↦ -i (u - conj u) / 2` on `H^{s,p}(E)`, as a continuous
real-linear map taking values in the real locus of `H^{s,p}(E)`. -/
def imCLM : H^{s, p}(E) →L[ℝ] H^{s, p}(E) :=
  (2⁻¹ : ℝ) •
    (((ContinuousLinearMap.lsmul ℂ ℂ (-Complex.I)).restrictScalars ℝ) ∘L
      (.id ℝ H^{s, p}(E) - (conjLIE E s p).toContinuousLinearEquiv.toContinuousLinearMap))

theorem reCLM_apply (u : H^{s, p}(E)) :
    reCLM E s p u = (2⁻¹ : ℝ) • (u + conjLIE E s p u) := by
  rfl

theorem imCLM_apply (u : H^{s, p}(E)) :
    imCLM E s p u = (2⁻¹ : ℝ) • ((-Complex.I) • (u - conjLIE E s p u)) := by
  rfl

@[simp]
theorem conjLIE_reCLM (u : H^{s, p}(E)) : conjLIE E s p (reCLM E s p u) = reCLM E s p u := by
  rw [reCLM_apply, map_smul, map_add, conjLIE_conjLIE, add_comm]

@[simp]
theorem conjLIE_imCLM (u : H^{s, p}(E)) : conjLIE E s p (imCLM E s p u) = imCLM E s p u := by
  rw [imCLM_apply, map_smul, conjLIE_smul, map_sub, conjLIE_conjLIE]
  simp [sub_eq_add_neg, add_comm]

/-- Decomposition `u = reCLM u + i • imCLM u` in `H^{s,p}(E)`. -/
theorem reCLM_add_I_smul_imCLM (u : H^{s, p}(E)) :
    reCLM E s p u + Complex.I • imCLM E s p u = u := by
  rw [reCLM_apply, imCLM_apply, smul_comm Complex.I (2⁻¹ : ℝ), smul_smul,
    mul_neg, Complex.I_mul_I, neg_neg, one_smul, ← smul_add, add_add_sub_cancel,
    ← two_smul ℝ u, smul_smul]
  norm_num

@[simp]
theorem toZeroAtInfty_reCLM_apply (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) (x : E) :
    toZeroAtInfty hs (reCLM E s 2 u) x = ((toZeroAtInfty hs u x).re : ℂ) := by
  rw [reCLM_apply, (toZeroAtInfty hs).map_smul_of_tower, map_add, toZeroAtInfty_conjLIE]
  apply Complex.ext <;> simp
  ring

@[simp]
theorem toZeroAtInfty_imCLM_apply (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) (x : E) :
    toZeroAtInfty hs (imCLM E s 2 u) x = ((toZeroAtInfty hs u x).im : ℂ) := by
  rw [imCLM_apply, (toZeroAtInfty hs).map_smul_of_tower, map_smul, map_sub, toZeroAtInfty_conjLIE]
  apply Complex.ext <;> simp
  ring

variable (E s p) in
/-- **The real Bessel-potential subspace** `{u ∈ H^{s,p}(E) | conjLIE u = u}`, as a real submodule
of `H^{s,p}(E)`. -/
def realSubmodule : Submodule ℝ H^{s, p}(E) :=
  LinearMap.eqLocus (conjLIE E s p).toLinearEquiv.toLinearMap LinearMap.id

@[simp]
theorem mem_realSubmodule {u : H^{s, p}(E)} :
    u ∈ realSubmodule E s p ↔ conjLIE E s p u = u :=
  Iff.rfl

theorem reCLM_mem_realSubmodule (u : H^{s, p}(E)) : reCLM E s p u ∈ realSubmodule E s p :=
  conjLIE_reCLM u

theorem imCLM_mem_realSubmodule (u : H^{s, p}(E)) : imCLM E s p u ∈ realSubmodule E s p :=
  conjLIE_imCLM u

@[simp]
theorem reCLM_eq_self_of_mem_realSubmodule {u : H^{s, p}(E)} (hu : u ∈ realSubmodule E s p) :
    reCLM E s p u = u := by
  rw [reCLM_apply, mem_realSubmodule.1 hu, ← two_smul ℝ u, smul_smul]
  norm_num

/-- The real submodule of `H^{s,p}(E)` is closed, hence a real Banach space. -/
theorem isClosed_realSubmodule (E : Type*) [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : IsClosed (realSubmodule E s p : Set H^{s, p}(E)) :=
  isClosed_eq (conjLIE E s p).continuous continuous_id

instance : CompleteSpace (realSubmodule E s p) :=
  (isClosed_realSubmodule E s p).isComplete.completeSpace_coe

-- Carried as its own type rather than a bare `Subtype` so its topology and uniformity come
-- uniquely from `NormedAddCommGroup` across `module` boundaries.
/-- **The real Bessel-potential Banach space** `{u ∈ H^{s,p}(E) | conjLIE E s p u = u}` of
real-valued Bessel-potential distributions. -/
def RealSubspace (E : Type*) [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : Type _ :=
  realSubmodule E s p

instance : NormedAddCommGroup (RealSubspace E s p) :=
  inferInstanceAs (NormedAddCommGroup (realSubmodule E s p))

instance : NormedSpace ℝ (RealSubspace E s p) :=
  inferInstanceAs (NormedSpace ℝ (realSubmodule E s p))

/-- The isometric `ℝ`-linear inclusion of `RealSubspace E s p` into `H^{s,p}(E)`. -/
def RealSubspace.valLI : RealSubspace E s p →ₗᵢ[ℝ] H^{s, p}(E) where
  toLinearMap := (realSubmodule E s p).subtype
  norm_map' _ := rfl

/-- The continuous `ℝ`-linear inclusion of `RealSubspace E s p` into `H^{s,p}(E)`. -/
def RealSubspace.valCLM : RealSubspace E s p →L[ℝ] H^{s, p}(E) :=
  RealSubspace.valLI.toContinuousLinearMap

@[simp]
theorem RealSubspace.valCLM_apply (f : RealSubspace E s p) :
    RealSubspace.valCLM f = RealSubspace.valLI f := by rfl

/-- Construct an element of `RealSubspace E s p` from `u ∈ realSubmodule E s p`. -/
def RealSubspace.mk (u : H^{s, p}(E)) (hu : u ∈ realSubmodule E s p) : RealSubspace E s p :=
  ⟨u, hu⟩

@[simp]
theorem RealSubspace.valLI_mk (u : H^{s, p}(E)) (hu : u ∈ realSubmodule E s p) :
    RealSubspace.valLI (RealSubspace.mk u hu) = u := by rfl

theorem RealSubspace.valLI_mem (f : RealSubspace E s p) :
    RealSubspace.valLI f ∈ realSubmodule E s p := f.2

@[ext]
theorem RealSubspace.ext {f g : RealSubspace E s p}
    (h : RealSubspace.valLI f = RealSubspace.valLI g) : f = g :=
  Subtype.ext h

theorem RealSubspace.range_valLI :
    Set.range (RealSubspace.valLI (E := E) (s := s) (p := p)) = realSubmodule E s p :=
  Subtype.range_coe

instance : CompleteSpace (RealSubspace E s p) :=
  (RealSubspace.valLI (E := E) (s := s) (p := p)).isometry.isUniformInducing.completeSpace
    (RealSubspace.range_valLI (E := E) (s := s) (p := p) ▸
      (isClosed_realSubmodule E s p).isComplete)

/-- Imaginary-part projection onto `RealSubspace E s p`. -/
def RealSubspace.imCLM : H^{s, p}(E) →L[ℝ] RealSubspace E s p :=
  LinearMap.mkContinuous
    ((BesselPotentialSpace.imCLM E s p).toLinearMap.codRestrict (realSubmodule E s p)
      imCLM_mem_realSubmodule)
    ‖BesselPotentialSpace.imCLM E s p‖ fun u ↦ (BesselPotentialSpace.imCLM E s p).le_opNorm u

@[simp]
theorem RealSubspace.valLI_imCLM_apply (u : H^{s, p}(E)) :
    RealSubspace.valLI (RealSubspace.imCLM u) = BesselPotentialSpace.imCLM E s p u := by rfl

private theorem inclusion_mem_realSubmodule (h : r ≤ s) (f : RealSubspace E s 2) :
    BesselPotentialSpace.inclusion h (RealSubspace.valLI f) ∈ realSubmodule E r 2 := by
  rw [mem_realSubmodule, ← inclusion_conjLIE, mem_realSubmodule.1 f.valLI_mem]

/-- Lowering the Sobolev order restricts to a continuous `ℝ`-linear map on `RealSubspace`. -/
def RealSubspace.inclusion (h : r ≤ s) : RealSubspace E s 2 →L[ℝ] RealSubspace E r 2 :=
  LinearMap.mkContinuous
    ((((BesselPotentialSpace.inclusion (E := E) (F := ℂ) h).restrictScalars ℝ).toLinearMap.comp
      (realSubmodule E s 2).subtype).codRestrict (realSubmodule E r 2)
      (inclusion_mem_realSubmodule h))
    ‖BesselPotentialSpace.inclusion (E := E) (F := ℂ) h‖ fun f ↦
      (BesselPotentialSpace.inclusion h).le_opNorm (RealSubspace.valLI f)

@[simp]
theorem RealSubspace.valLI_inclusion_apply (h : r ≤ s) (f : RealSubspace E s 2) :
    RealSubspace.valLI (RealSubspace.inclusion h f) =
      BesselPotentialSpace.inclusion h (RealSubspace.valLI f) := by rfl

/-- For `u ∈ realSubmodule E s 2` and `2s > dim E`, the continuous representative
`toZeroAtInfty hs u` has zero imaginary part everywhere. -/
theorem im_toZeroAtInfty_eq_zero_of_mem_realSubmodule (hs : finrank ℝ E < 2 * s)
    {u : H^{s}(E)} (hu : u ∈ realSubmodule E s 2) (x : E) :
    (toZeroAtInfty hs u x).im = 0 := by
  have h := congrArg (fun g : C₀(E, ℂ) ↦ (g x).im) (toZeroAtInfty_conjLIE hs u)
  rw [mem_realSubmodule.1 hu, ZeroAtInftyContinuousMap.star_apply, Complex.star_def,
    Complex.conj_im] at h
  linarith

/-- For `u ∈ realSubmodule E s 2` and `2s > dim E`, `toZeroAtInfty hs u` equals its real part
everywhere. -/
theorem toZeroAtInfty_apply_eq_re_of_mem_realSubmodule (hs : finrank ℝ E < 2 * s)
    {u : H^{s}(E)} (hu : u ∈ realSubmodule E s 2) (x : E) :
    toZeroAtInfty hs u x = ((toZeroAtInfty hs u x).re : ℂ) := by
  apply Complex.ext <;> simp [im_toZeroAtInfty_eq_zero_of_mem_realSubmodule hs hu x]

/-- For `u ∈ realSubmodule E s 2` and `2s > dim E`, the real part of `toZeroAtInfty hs u` lies in
`TemperedDistribution.realSobolevFunctions E s 2`. -/
theorem re_toZeroAtInfty_mem_realSobolevFunctions (hs : finrank ℝ E < 2 * s)
    {u : H^{s}(E)} (hu : u ∈ realSubmodule E s 2) :
    (fun x ↦ (toZeroAtInfty hs u x).re) ∈ realSobolevFunctions E s 2 := by
  have h0 : 0 ≤ s := by have := (finrank ℝ E).cast_nonneg (α := ℝ); linarith
  refine mem_realSobolevFunctions_of_ae_eq_ofReal (memSobolev_toLp_inclusion h0 u) ?_
  filter_upwards [coeFn_toLp_inclusion_ae_eq_toZeroAtInfty hs h0 u] with x hx
  rw [hx]
  exact toZeroAtInfty_apply_eq_re_of_mem_realSubmodule hs hu x

/-- Every real `Lᵖ` function whose complexification lies in `H^{s,p}(E)` determines an element of
`realSubmodule E s p`. -/
theorem toBesselPotentialSpace_mem_realSubmodule_of_ofReal {u : Lp ℝ p (volume : Measure E)}
    (hu : MemSobolev s p (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u))) :
    hu.toBesselPotentialSpace ∈ realSubmodule E s p := by
  rw [mem_realSubmodule]
  apply ext
  rw [toDistr_conjLIE, MemSobolev.toBesselPotentialSpace_toDistr,
    conjCLE_toTemperedDistribution_Lp]
  congr 1
  refine Lp.ext ?_
  filter_upwards [
    Complex.conjCLE.toContinuousLinearMap.coeFn_compLp (Complex.ofRealCLM.compLp u),
    Complex.ofRealCLM.coeFn_compLp u] with x hconj hreal
  rw [hconj, hreal]
  simp

/-- Every continuous function in `realSobolevFunctions E s 2`, `2s > dim E`, is the real part of
`toZeroAtInfty hs u` for an element `u ∈ realSubmodule E s 2`. -/
theorem exists_mem_realSubmodule_toZeroAtInfty_eq_ofReal (hs : finrank ℝ E < 2 * s) {f : E → ℝ}
    (hf_cont : Continuous f) (hf : f ∈ realSobolevFunctions E s 2) :
    ∃ u ∈ realSubmodule E s 2, ∀ x, toZeroAtInfty hs u x = (f x : ℂ) := by
  have h0 : 0 ≤ s := by have := (finrank ℝ E).cast_nonneg (α := ℝ); linarith
  obtain ⟨v, hvf, hv⟩ := mem_realSobolevFunctions.1 hf
  refine ⟨hv.toBesselPotentialSpace, toBesselPotentialSpace_mem_realSubmodule_of_ofReal hv, ?_⟩
  have hae : ⇑(inclusion h0 hv.toBesselPotentialSpace).toLp =ᵐ[volume] fun x ↦ (f x : ℂ) := by
    rw [toLp_inclusion_toBesselPotentialSpace h0 hv rfl]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp v, hvf] with x hv' hfx
    rw [hv', Complex.ofRealCLM_apply, hfx]
  have heq := coe_toZeroAtInfty_eq_of_ae_eq hs (Complex.continuous_ofReal.comp hf_cont) hae
  exact congrFun heq

end RealPartAndSubmodule

end BesselPotentialSpace
