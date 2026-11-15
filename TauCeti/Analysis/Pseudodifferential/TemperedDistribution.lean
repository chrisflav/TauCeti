/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Lp
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier

/-!
# Extension of uniform pseudodifferential operators to tempered distributions

For a symbol `a ∈ S^m_{1,0}` on `ℝⁿ` whose derivative bounds hold uniformly in the position `x`
(`TauCeti.Symbol.IsUniform`), the right quantization `Op_R(c)` maps Schwartz space continuously to
itself (`TauCeti.Symbol.quantizeRightUniformCLM`). Reflecting the frequency variable
`a⁻(x, ξ) = a(x, -ξ)` (`TauCeti.Symbol.reflectFrequency`) gives the formal bilinear transpose of
`Op(a)` on scalar Schwartz functions:

`∫ φ(x) (Op(c) u)(x) dx = ∫ (Op_R(c⁻) φ)(y) u(y) dy`.

Precomposing scalar tempered distributions with `Op_R(c⁻)` and expanding finite-dimensional
coefficient spaces `V` and `W` in bases defines a continuous linear map
`TauCeti.Symbol.quantizeTemperedCLM a ha : 𝓢'(ℝⁿ, V) →L[ℂ] 𝓢'(ℝⁿ, W)` without requiring compact
spatial support or inner product structures on `V` and `W`.

Because every identity on `𝓢'(ℝⁿ, W)` is tested directly on Schwartz functions via `Op_R(a⁻)`, all
algebraic and analytic compatibility properties hold unconditionally across `𝓢'`, including on
non-Schwartz-dense spaces such as `L^∞` and `B^s_{∞,∞}`:

* `TauCeti.Symbol.quantizeTemperedCLM_toTemperedDistribution`: on Schwartz functions `Op(a)` agrees
  with `TauCeti.Symbol.quantizeUniformCLM`.
* `TauCeti.Symbol.quantizeTemperedCLM_lp`: when `m < -n`, `Op(a)` agrees on `Lᵖ(ℝⁿ; V)` for every
  `1 ≤ p ≤ ∞` (including `p = 1` and `p = ∞`) with the Schur integral operator
  `TauCeti.Symbol.quantizeLp`.
* `TauCeti.Symbol.quantizeTemperedCLM_fourierMultiplierCLM_of_coefficient_eq` and
  `TauCeti.Symbol.quantizeTemperedCLM_besselPotential`: exact right composition `Op(a) ∘ g(D) =
  Op(g(ξ / 2π) a)` on `𝓢'`, in particular `Op(a) ∘ J^t = Op(a ⟨ξ / 2π⟩^t)`.
* `TauCeti.Symbol.lineDerivOp_quantizeTemperedCLM`: the spatial derivative commutator
  `∂_j (Op(a) u) = Op(a) (∂_j u) + Op(∂_{x_j} a) u` on `𝓢'`.
* `TauCeti.Symbol.postcomp_quantizeTemperedCLM`, `TauCeti.Symbol.quantizeTemperedCLM_postcomp`, and
  `TauCeti.Symbol.quantizeTemperedCLM_const`: naturality with respect to continuous linear maps of
  the fibre spaces `V` and `W`, and quantization of constant symbols.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1–§3.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.6 and
  Theorem 18.1.7.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Filter
open scoped SchwartzMap ENNReal NNReal RealInnerProductSpace LineDeriv ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ}

/-! ### Frequency reflection of a symbol -/

section ReflectFrequency

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

private theorem coordinateDeriv_comp_neg {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {g : CoordinateSpace n → A} (hg : ContDiff ℝ ∞ g) (β : List (Fin n)) (ξ : CoordinateSpace n) :
    coordinateDeriv β (fun η ↦ g (-η)) ξ = (-1 : ℝ) ^ β.length • coordinateDeriv β g (-ξ) := by
  induction β generalizing ξ with
  | nil => simp
  | cons j js ih =>
    have hfun : coordinateDeriv js (fun η ↦ g (-η)) =
        fun η ↦ (-1 : ℝ) ^ js.length • coordinateDeriv js g (-η) := funext ih
    have hdiff : DifferentiableAt ℝ (coordinateDeriv js g) (-ξ) :=
      ((hg.coordinateDeriv js).differentiable (by simp)) (-ξ)
    have hf : HasFDerivAt (fun η ↦ (-1 : ℝ) ^ js.length • coordinateDeriv js g (-η))
        ((-1 : ℝ) ^ js.length • -(fderiv ℝ (coordinateDeriv js g) (-ξ))) ξ :=
      ((hdiff.hasFDerivAt.comp ξ (hasFDerivAt_id ξ).neg).const_smul
        ((-1 : ℝ) ^ js.length)).congr_fderiv (by
          ext v
          simp)
    rw [coordinateDeriv_cons, hfun, hf.fderiv, List.length_cons, pow_succ]
    simp [coordinateDeriv_cons]

private theorem mixedDeriv_comp_neg_snd {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {a : CoordinateSpace n × CoordinateSpace n → A} (ha : ContDiff ℝ ∞ a) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p : CoordinateSpace n × CoordinateSpace n ↦ a (p.1, -p.2)) x ξ =
      (-1 : ℝ) ^ β.length • mixedDeriv α β a x (-ξ) := by
  have hinner : (fun y ↦ coordinateDeriv β (fun η ↦ a (y, -η)) ξ) =
      (-1 : ℝ) ^ β.length • fun y ↦ coordinateDeriv β (fun η ↦ a (y, η)) (-ξ) :=
    funext fun y ↦ coordinateDeriv_comp_neg (ha.comp (contDiff_const.prodMk contDiff_id)) β ξ
  rw [mixedDeriv_def, hinner, coordinateDeriv_const_smul, mixedDeriv_def, Pi.smul_apply]

/-- The symbol `a⁻(x, ξ) = a(x, -ξ)` obtained by reflecting the frequency variable. -/
def reflectFrequency (a : Symbol n V W m) : Symbol n V W m where
  coefficient p := a.coefficient (p.1, -p.2)
  contDiff_coefficient := a.contDiff_coefficient.comp (contDiff_fst.prodMk contDiff_snd.neg)
  exists_bound K hK α β := by
    obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α β
    refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
    rw [mixedDeriv_comp_neg_snd a.contDiff_coefficient, norm_smul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul]
    simpa only [norm_neg] using hC x hx (-ξ)

@[simp]
theorem coefficient_reflectFrequency (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    a.reflectFrequency.coefficient p = a.coefficient (p.1, -p.2) :=
  (rfl)

@[simp]
theorem reflectFrequency_reflectFrequency (a : Symbol n V W m) :
    a.reflectFrequency.reflectFrequency = a :=
  Symbol.ext (funext fun p ↦ by simp)

theorem IsUniform.neg {a : Symbol n V W m} (ha : a.IsUniform) : (-a).IsUniform := by
  simpa using ha.smul (-1)

theorem IsUniform.sub {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) :
    (a - b).IsUniform := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

/-- Reflecting the frequency variable preserves uniform symbol estimates. -/
theorem IsUniform.reflectFrequency {a : Symbol n V W m} (ha : a.IsUniform) :
    a.reflectFrequency.IsUniform :=
  isUniform_iff.2 fun α β ↦ by
    obtain ⟨C, hC0, hC⟩ := isUniform_iff.1 ha α β
    refine ⟨C, hC0, fun x ξ ↦ ?_⟩
    rw [show a.reflectFrequency.coefficient = fun p ↦ a.coefficient (p.1, -p.2) from rfl,
      mixedDeriv_comp_neg_snd a.contDiff_coefficient, norm_smul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul]
    simpa only [norm_neg] using hC x (-ξ)

@[simp]
theorem reflectFrequency_add (a b : Symbol n V W m) :
    (a + b).reflectFrequency = a.reflectFrequency + b.reflectFrequency :=
  Symbol.ext (funext fun _ ↦ rfl)

@[simp]
theorem reflectFrequency_smul (c : ℂ) (a : Symbol n V W m) :
    (c • a).reflectFrequency = c • a.reflectFrequency :=
  Symbol.ext (funext fun _ ↦ rfl)

@[simp]
theorem reflectFrequency_zero : (0 : Symbol n V W m).reflectFrequency = 0 :=
  Symbol.ext (funext fun _ ↦ rfl)

@[simp]
theorem reflectFrequency_inclusion (h : m ≤ m') (a : Symbol n V W m) :
    (inclusion h a).reflectFrequency = inclusion h a.reflectFrequency :=
  Symbol.ext (funext fun p ↦ by simp)

@[simp]
theorem spatialDeriv_reflectFrequency (j : Fin n) (a : Symbol n V W m) :
    spatialDeriv j a.reflectFrequency = (spatialDeriv j a).reflectFrequency :=
  Symbol.ext (funext fun ⟨x, ξ⟩ ↦ by simp)

@[simp]
theorem reflectFrequency_map {V' W' : Type*} [NormedAddCommGroup V'] [NormedSpace ℂ V']
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] (Φ : (V →L[ℂ] W) →L[ℝ] (V' →L[ℂ] W'))
    (a : Symbol n V W m) :
    (a.map Φ).reflectFrequency = a.reflectFrequency.map Φ :=
  Symbol.ext (funext fun p ↦ by simp)

private theorem quantizeRightUniformCLM_congr {c : Symbol n V W m} (hc : c.IsUniform)
    {d : Symbol n V W m'} (hd : d.IsUniform) (h : c.coefficient = d.coefficient) :
    quantizeRightUniformCLM c hc = quantizeRightUniformCLM d hd := by
  ext u x
  simp [quantizeRightUniformCLM_apply, h]

private theorem quantizeRightUniformCLM_sum {ι : Type*} (s : Finset ι)
    (c : ι → Symbol n V W m) (hc : ∀ i, (c i).IsUniform) :
    quantizeRightUniformCLM (∑ i ∈ s, c i) (IsUniform.sum fun i _ ↦ hc i) =
      ∑ i ∈ s, quantizeRightUniformCLM (c i) (hc i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [quantizeRightUniformCLM_congr _ (isUniform_zero (m := m)) (by simp),
      quantizeRightUniformCLM_zero, Finset.sum_empty]
  | insert i₀ s hi₀ ih =>
    have hs : (∑ i ∈ s, c i).IsUniform := IsUniform.sum fun i _ ↦ hc i
    rw [quantizeRightUniformCLM_congr _ ((hc i₀).add hs) (by simp [Finset.sum_insert hi₀]),
      quantizeRightUniformCLM_add (hc i₀) hs, ih, Finset.sum_insert hi₀]

end ReflectFrequency

/-! ### Scalar transpose and tempered quantization -/

section Scalar

private theorem mul_clm_apply_comm (T : ℂ →L[ℂ] ℂ) (z w : ℂ) : z * T w = T z * w := by
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_comm z w, ← smul_eq_mul, map_smul, smul_eq_mul,
    mul_comm]

/-- The double integrand `φ(x) exp(2πi ⟪ζ, x⟫) c(x, 2πζ) (𝓕 u ζ)` of the scalar transpose
identity is integrable on `ℝⁿ × ℝⁿ`. -/
private theorem integrable_scalarTransposeIntegrand {c : Symbol n ℂ ℂ m} (hc : c.IsUniform)
    (φ u : 𝓢(CoordinateSpace n, ℂ)) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      φ q.1 * (𝐞 ⟪q.2, q.1⟫ • c.coefficient (q.1, (2 * π) • q.2) (𝓕 u q.2)))
      (volume.prod volume) := by
  obtain ⟨C, -, hC⟩ := hc.exists_bound_coefficient
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      φ q.1 * (𝐞 ⟪q.2, q.1⟫ • c.coefficient (q.1, (2 * π) • q.2) (𝓕 u q.2)) := by
    have h₂ : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
        c.coefficient (q.1, (2 * π) • q.2) :=
      c.contDiff_coefficient.continuous.comp (by fun_prop)
    exact (φ.continuous.comp continuous_fst).mul
      ((Real.continuous_fourierChar.comp (continuous_snd.inner continuous_fst)).smul
        (h₂.clm_apply ((𝓕 u).continuous.comp continuous_snd)))
  refine ((φ.integrable.norm.mul_prod
    ((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m)).const_mul C).mono'
    hcont.aestronglyMeasurable (.of_forall fun ⟨x, ζ⟩ ↦ ?_)
  rw [norm_mul, Circle.norm_smul]
  calc ‖φ x‖ * ‖c.coefficient (x, (2 * π) • ζ) (𝓕 u ζ)‖
      ≤ ‖φ x‖ * (‖c.coefficient (x, (2 * π) • ζ)‖ * ‖𝓕 u ζ‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖φ x‖ * (C * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) := by
        gcongr; exact hC _ _
    _ = C * (‖φ x‖ * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖)) := by ring

/-- **Scalar bilinear transpose.** For a uniform scalar symbol `c`, `Op_R(c⁻)` is the transpose of
`Op(c)` for the bilinear pairing `(φ, u) ↦ ∫ φ(x) u(x) dx` on Schwartz space. -/
private theorem integral_mul_quantizeUniformCLM {c : Symbol n ℂ ℂ m} (hc : c.IsUniform)
    (φ u : 𝓢(CoordinateSpace n, ℂ)) :
    ∫ x, φ x * quantizeUniformCLM c hc u x =
      ∫ y, quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ y * u y := by
  set ψ := quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ
  have hLHS : ∫ x, φ x * quantizeUniformCLM c hc u x =
      ∫ x, ∫ ζ, φ x * (𝐞 ⟪ζ, x⟫ • c.coefficient (x, (2 * π) • ζ) (𝓕 u ζ)) := by
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    dsimp only
    rw [quantizeUniformCLM_apply, quantizeSchwartzValue_def, ← smul_eq_mul,
      ← integral_smul (φ x)]
    rfl
  have hFψ (ζ : CoordinateSpace n) :
      (𝓕⁻ ψ) ζ * 𝓕 u ζ = ∫ x, φ x * (𝐞 ⟪ζ, x⟫ • c.coefficient (x, (2 * π) • ζ) (𝓕 u ζ)) := by
    rw [SchwartzMap.fourierInv_coe, fourierInv_eq_fourier_neg, ← SchwartzMap.fourier_coe,
      fourier_quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ (-ζ),
      Real.fourier_eq, ← integral_mul_const]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [coefficient_reflectFrequency, smul_neg, neg_neg, inner_neg_right,
      Circle.smul_def, smul_eq_mul]
    rw [real_inner_comm x ζ, mul_assoc, ← mul_clm_apply_comm (c.coefficient (x, (2 * π) • ζ))]
    ring
  calc ∫ x, φ x * quantizeUniformCLM c hc u x
      = ∫ ζ, ∫ x, φ x * (𝐞 ⟪ζ, x⟫ • c.coefficient (x, (2 * π) • ζ) (𝓕 u ζ)) := by
        rw [hLHS, integral_integral_swap (integrable_scalarTransposeIntegrand hc φ u)]
    _ = ∫ ζ, (𝓕⁻ ψ) ζ * 𝓕 u ζ := integral_congr_ae (.of_forall fun ζ ↦ (hFψ ζ).symm)
    _ = ∫ y, 𝓕 (𝓕⁻ ψ) y * u y := (SchwartzMap.integral_fourier_mul_eq (𝓕⁻ ψ) u).symm
    _ = ∫ y, ψ y * u y := by rw [FourierTransform.fourier_fourierInv_eq]

/-- Scalar quantization on `𝓢'(ℝⁿ, ℂ)` by precomposition with `Op_R(c⁻)`. -/
private def quantizeTemperedScalar (c : Symbol n ℂ ℂ m) (hc : c.IsUniform) :
    𝓢'(CoordinateSpace n, ℂ) →L[ℂ] 𝓢'(CoordinateSpace n, ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ (quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency)

private theorem quantizeTemperedScalar_apply (c : Symbol n ℂ ℂ m) (hc : c.IsUniform)
    (u : 𝓢'(CoordinateSpace n, ℂ)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    quantizeTemperedScalar c hc u φ =
      u (quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ) :=
  (rfl)

private theorem quantizeTemperedScalar_toTemperedDistribution {c : Symbol n ℂ ℂ m}
    (hc : c.IsUniform) (u : 𝓢(CoordinateSpace n, ℂ)) :
    quantizeTemperedScalar c hc (u : 𝓢'(CoordinateSpace n, ℂ)) =
      (quantizeUniformCLM c hc u : 𝓢'(CoordinateSpace n, ℂ)) := by
  ext φ
  simp only [quantizeTemperedScalar_apply, SchwartzMap.coe_apply, smul_eq_mul]
  exact (integral_mul_quantizeUniformCLM hc φ u).symm

/-- Row and column `L¹` bounds on `quantizationKernel` for a uniform symbol of order `m < -n`. -/
private theorem exists_row_col_lintegral_quantizationKernel_le {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {a : Symbol n V W m} (ha : a.IsUniform) (hm : m < -n) :
    ∃ B : ℝ≥0, (∀ x, ∫⁻ y, ‖quantizationKernel a.coefficient x y‖ₑ ≤ B) ∧
      ∀ y, ∫⁻ x, ‖quantizationKernel a.coefficient x y‖ₑ ≤ B := by
  have hweight : Integrable (fun ξ : CoordinateSpace n ↦ (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
    simpa only [neg_neg] using integrable_rpow_neg_one_add_norm_sq
      (μ := (volume : Measure (CoordinateSpace n))) (r := -m)
      (by rw [finrank_euclideanSpace_fin]; linarith)
  obtain ⟨C₀, hC₀, hc₀⟩ := isUniform_iff.1 ha [] []
  choose Cj hCj hcj using fun j : Fin n ↦ isUniform_iff.1 ha [] (List.replicate (n + 1) j)
  set A := (C₀ + ∑ j, Cj j) * ∫ ξ : CoordinateSpace n, (1 + ‖ξ‖ ^ 2) ^ (m / 2)
  have hb₀ (x : CoordinateSpace n) : ∫ ξ, ‖a.coefficient (x, ξ)‖ ≤ A := by
    refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) (hweight.const_mul C₀)
      (ae_of_all _ fun ξ ↦ by simpa using hc₀ x ξ)).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ hCj j))
      (integral_nonneg fun _ ↦ by positivity)
  have hb₁ (x : CoordinateSpace n) (j : Fin n) :
      ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) j) a.coefficient x ξ‖ ≤ A * 1 ^ (n + 1) := by
    rw [one_pow, mul_one]
    refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) (hweight.const_mul (Cj j))
      (ae_of_all _ fun ξ ↦ (hcj j x ξ).trans
        (mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ (by
          rw [List.length_replicate]; push_cast; linarith)) (hCj j)))).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right
      ((Finset.single_le_sum (fun i _ ↦ hCj i) (Finset.mem_univ j)).trans
        (le_add_of_nonneg_left hC₀)) (integral_nonneg fun _ ↦ by positivity)
  refine ⟨Real.toNNReal (2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * A *
    (∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹) * 1 ^ n), fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [ENNReal.ofNNReal_toNNReal]
    exact a.lintegral_enorm_quantizationKernel_right_le hm one_pos (hb₀ x) (hb₁ x)
  · rw [ENNReal.ofNNReal_toNNReal]
    exact a.lintegral_enorm_quantizationKernel_left_le hm one_pos hb₀ hb₁ y

/-- For `m < -n`, `1 ≤ p ≤ ∞`, `φ ∈ 𝓢` and `g ∈ Lᵖ`, `(x, y) ↦ φ(x) K_c(x, y) g(y)` is integrable
on `ℝⁿ × ℝⁿ`. -/
private theorem integrable_mul_quantizationKernel_prod {c : Symbol n ℂ ℂ m} (hc : c.IsUniform)
    (hm : m < -n) {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (φ : 𝓢(CoordinateSpace n, ℂ))
    (g : Lp ℂ p (volume : Measure (CoordinateSpace n))) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      φ q.1 * quantizationKernel c.coefficient q.1 q.2 (g q.2)) (volume.prod volume) := by
  have : (1 - p⁻¹)⁻¹.HolderConjugate p := (ENNReal.HolderConjugate.inv_one_sub_inv' hp.out).symm
  obtain ⟨B, hrow, hcol⟩ := exists_row_col_lintegral_quantizationKernel_le hc hm
  set K₀ : CoordinateSpace n → CoordinateSpace n → ℝ →L[ℝ] ℝ := fun x y ↦
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ‖quantizationKernel c.coefficient x y‖
  have hK₀_meas : AEStronglyMeasurable (Function.uncurry K₀) (volume.prod volume) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ
      (ContinuousLinearMap.id ℝ ℝ)).continuous.comp_aestronglyMeasurable
      (c.continuous_quantizationKernel hm).norm.aestronglyMeasurable
  have hK₀_enorm (x y : CoordinateSpace n) :
      ‖K₀ x y‖ₑ = ‖quantizationKernel c.coefficient x y‖ₑ := by
    dsimp only [K₀]
    rw [← ofReal_norm, ← ofReal_norm, ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_id, one_mul, norm_norm]
  have hrow₀ : ∀ᵐ x ∂volume, ∫⁻ y, ‖K₀ x y‖ₑ ≤ B := by simp_rw [hK₀_enorm]; exact ae_of_all _ hrow
  have hcol₀ : ∀ᵐ y ∂volume, ∫⁻ x, ‖K₀ x y‖ₑ ≤ B := by simp_rw [hK₀_enorm]; exact ae_of_all _ hcol
  have hK_meas : AEStronglyMeasurable (Function.uncurry (quantizationKernel c.coefficient))
      (volume.prod volume) :=
    (c.continuous_quantizationKernel hm).aestronglyMeasurable
  have hH_meas : AEStronglyMeasurable
      (fun q : CoordinateSpace n × CoordinateSpace n ↦
        φ q.1 * quantizationKernel c.coefficient q.1 q.2 (g q.2)) (volume.prod volume) :=
    (φ.continuous.comp continuous_fst).aestronglyMeasurable.mul
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hK_meas
        (Lp.memLp g).aestronglyMeasurable.comp_snd)
  refine (integrable_prod_iff hH_meas).2 ⟨?_, ?_⟩
  · filter_upwards [ae_integrable_apply_of_memLp hK_meas (Lp.memLp g) hp.out
      (ae_of_all _ hrow) (ae_of_all _ hcol)] with x hx
    exact hx.const_mul (φ x)
  · have hF : MemLp (fun x ↦ ∫ y, K₀ x y ‖g y‖) p volume :=
      memLp_integral_apply hK₀_meas (Lp.memLp g).norm hp.out hrow₀ hcol₀
    refine (memLp_one_iff_integrable.1 ((φ.memLp (1 - p⁻¹)⁻¹).norm.mul hF)).mono'
      hH_meas.norm.integral_prod_right' ?_
    filter_upwards [ae_integrable_apply_of_memLp hK₀_meas (Lp.memLp g).norm hp.out hrow₀ hcol₀]
      with x hx
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), Pi.mul_apply,
      ← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
      (hx.const_mul ‖φ x‖) (ae_of_all _ fun y ↦ ?_)
    simp only [K₀, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans_eq (mul_comm _ _)) (norm_nonneg _)

/-- When `m < -n`, `Op_R(c⁻) φ` agrees almost everywhere with the transposed kernel integral
`y ↦ ∫ x, K_c(x, y) (φ x)`. -/
private theorem quantizeRightUniformCLM_reflectFrequency_ae_eq {c : Symbol n ℂ ℂ m}
    (hc : c.IsUniform) (hm : m < -n) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (⇑(quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ) : CoordinateSpace n → ℂ)
      =ᵐ[volume] fun y ↦ ∫ x, quantizationKernel c.coefficient x y (φ x) := by
  obtain ⟨B, hrow, hcol⟩ := exists_row_col_lintegral_quantizationKernel_le hc hm
  have hKT_meas : AEStronglyMeasurable
      (Function.uncurry fun y x ↦ quantizationKernel c.coefficient x y) (volume.prod volume) :=
    ((c.continuous_quantizationKernel hm).comp continuous_swap).aestronglyMeasurable
  have hloc : LocallyIntegrable (fun y ↦ ∫ x, quantizationKernel c.coefficient x y (φ x)) volume :=
    (memLp_integral_apply hKT_meas (φ.memLp 1) le_rfl (ae_of_all _ hcol)
      (ae_of_all _ hrow)).locallyIntegrable le_rfl
  set ψ := quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ
  refine (ψ.coeFn_toLp 1 volume).symm.trans
    (Lp.ae_eq_of_toTemperedDistribution_apply_eq (ψ.toLp 1 volume) hloc fun u ↦ ?_)
  simp only [Lp.toTemperedDistribution_toLp_eq, SchwartzMap.toTemperedDistributionCLM_apply_apply,
    smul_eq_mul]
  calc ∫ y, u y * ψ y = ∫ y, ψ y * u y := integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _)
    _ = ∫ x, φ x * quantizeUniformCLM c hc u x := (integral_mul_quantizeUniformCLM hc φ u).symm
    _ = ∫ x, ∫ y, φ x * quantizationKernel c.coefficient x y (u.toLp 1 volume y) := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [quantizeUniformCLM_apply,
          quantizeSchwartzValue_eq_integral_quantizationKernel (c.integrable_coefficient hm x),
          ← smul_eq_mul, ← integral_smul]
        refine integral_congr_ae ((u.coeFn_toLp 1 volume).mono fun y hy ↦ ?_)
        dsimp only
        rw [hy, smul_eq_mul]
    _ = ∫ y, ∫ x, φ x * quantizationKernel c.coefficient x y (u.toLp 1 volume y) :=
        integral_integral_swap (integrable_mul_quantizationKernel_prod hc hm φ (u.toLp 1 volume))
    _ = ∫ y, u y * ∫ x, quantizationKernel c.coefficient x y (φ x) := by
        refine integral_congr_ae ((u.coeFn_toLp 1 volume).mono fun y hy ↦ ?_)
        dsimp only
        rw [hy]
        simp_rw [mul_clm_apply_comm (quantizationKernel c.coefficient _ y) (φ _) (u y)]
        rw [integral_mul_const, mul_comm]

private theorem quantizeTemperedScalar_lp {c : Symbol n ℂ ℂ m} (hc : c.IsUniform) (hm : m < -n)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : Lp ℂ p (volume : Measure (CoordinateSpace n))) :
    quantizeTemperedScalar c hc (g : 𝓢'(CoordinateSpace n, ℂ)) =
      (c.quantizeLp p hm hc g : 𝓢'(CoordinateSpace n, ℂ)) := by
  ext φ
  rw [quantizeTemperedScalar_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]
  calc ∫ y, quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ y * g y
      = ∫ y, (∫ x, quantizationKernel c.coefficient x y (φ x)) * g y := by
        refine integral_congr_ae
          ((quantizeRightUniformCLM_reflectFrequency_ae_eq hc hm φ).mono fun y hy ↦ ?_)
        dsimp only
        rw [hy]
    _ = ∫ y, ∫ x, φ x * quantizationKernel c.coefficient x y (g y) := by
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        simp_rw [mul_clm_apply_comm (quantizationKernel c.coefficient _ y) (φ _) (g y)]
        rw [integral_mul_const]
    _ = ∫ x, ∫ y, φ x * quantizationKernel c.coefficient x y (g y) :=
        (integral_integral_swap (integrable_mul_quantizationKernel_prod hc hm φ g)).symm
    _ = ∫ x, φ x * c.quantizeLp p hm hc g x := by
        refine integral_congr_ae ((coeFn_quantizeLp (a := c) (hm := hm) (ha := hc) g).mono
          fun x hx ↦ ?_)
        dsimp only
        rw [hx, ← smul_eq_mul, ← integral_smul]
        rfl

private theorem quantizeTemperedScalar_fourierMultiplierCLM {c : Symbol n ℂ ℂ m} (hc : c.IsUniform)
    {d : Symbol n ℂ ℂ m'} (hd : d.IsUniform) {g : CoordinateSpace n → ℂ}
    (hg : g.HasTemperateGrowth)
    (hcoeff : ∀ p, d.coefficient p = g ((2 * π)⁻¹ • p.2) • c.coefficient p)
    (u : 𝓢'(CoordinateSpace n, ℂ)) :
    quantizeTemperedScalar c hc (TemperedDistribution.fourierMultiplierCLM ℂ g u) =
      quantizeTemperedScalar d hd u := by
  ext φ
  rw [quantizeTemperedScalar_apply, quantizeTemperedScalar_apply,
    TemperedDistribution.fourierMultiplierCLM_apply_apply]
  congr 1
  set ψ : 𝓢(CoordinateSpace n, ℂ) :=
    quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ
  set h : 𝓢(CoordinateSpace n, ℂ) := SchwartzMap.smulLeftCLM ℂ g (𝓕⁻ ψ)
  set χ₁ : 𝓢(CoordinateSpace n, ℂ) := 𝓕 h
  set χ₂ : 𝓢(CoordinateSpace n, ℂ) :=
    quantizeRightUniformCLM d.reflectFrequency hd.reflectFrequency φ
  have hF : 𝓕 χ₁ = 𝓕 χ₂ := by
    ext ζ
    have h₁ : 𝓕 χ₁ ζ = g (-ζ) * 𝓕 ψ ζ := by
      have hinv : (𝓕⁻ χ₁ : 𝓢(CoordinateSpace n, ℂ)) = h :=
        FourierTransform.fourierInv_fourier_eq h
      have hneg := congrArg (fun f : 𝓢(CoordinateSpace n, ℂ) ↦ f (-ζ)) hinv
      simp only [SchwartzMap.fourierInv_coe, fourierInv_eq_fourier_neg, neg_neg,
        ← SchwartzMap.fourier_coe, h, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul] at hneg
      exact hneg
    rw [h₁, fourier_quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ ζ,
      fourier_quantizeRightUniformCLM d.reflectFrequency hd.reflectFrequency φ ζ,
      Real.fourier_eq, Real.fourier_eq, ← smul_eq_mul, ← integral_smul]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    have h2π : (2 * π)⁻¹ • -((2 * π) • ζ) = -ζ := by
      rw [smul_neg, inv_smul_smul₀ two_pi_pos.ne']
    simp only [coefficient_reflectFrequency, hcoeff, h2π, smul_apply, smul_comm (g (-ζ))]
  calc χ₁ = 𝓕⁻ (𝓕 χ₁) := (FourierTransform.fourierInv_fourier_eq χ₁).symm
    _ = 𝓕⁻ (𝓕 χ₂) := by rw [hF]
    _ = χ₂ := FourierTransform.fourierInv_fourier_eq χ₂

private theorem integral_mul_quantizeRightUniformCLM_reflectFrequency {c : Symbol n ℂ ℂ m}
    (hc : c.IsUniform) (φ u : 𝓢(CoordinateSpace n, ℂ)) :
    ∫ x, u x * quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ x =
      ∫ x, φ x * quantizeUniformCLM c hc u x :=
  (integral_congr_ae (.of_forall fun _ ↦ mul_comm _ _)).trans
    (integral_mul_quantizeUniformCLM hc φ u).symm

private theorem lineDerivOp_quantizeRightUniformCLM_scalar {c : Symbol n ℂ ℂ m} (hc : c.IsUniform)
    (j : Fin n) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    ∂_{EuclideanSpace.single j (1 : ℝ)}
        (quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ) =
      quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency
          (∂_{EuclideanSpace.single j (1 : ℝ)} φ) +
        quantizeRightUniformCLM (spatialDeriv j c).reflectFrequency
          (hc.spatialDeriv j).reflectFrequency φ := by
  set e := EuclideanSpace.single j (1 : ℝ)
  set ψ := quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency φ
  set ψ₁ := ∂_{e} ψ
  set ψ₂ := quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency (∂_{e} φ) +
    quantizeRightUniformCLM (spatialDeriv j c).reflectFrequency
      (hc.spatialDeriv j).reflectFrequency φ
  have hdist : (ψ₁.toLp 1 volume : 𝓢'(CoordinateSpace n, ℂ)) =
      (ψ₂.toLp 1 volume : 𝓢'(CoordinateSpace n, ℂ)) := by
    ext u
    simp only [Lp.toTemperedDistribution_toLp_eq,
      SchwartzMap.toTemperedDistributionCLM_apply_apply]
    calc ∫ x, u x • ψ₁ x
        = -∫ x, ∂_{e} u x • ψ x := SchwartzMap.integral_smul_lineDerivOp_right_eq_neg_left u ψ e
      _ = -∫ x, φ x * quantizeUniformCLM c hc (∂_{e} u) x := by
          simp only [smul_eq_mul]
          rw [integral_mul_quantizeRightUniformCLM_reflectFrequency]
      _ = -(∫ x, φ x • ∂_{e} (quantizeUniformCLM c hc u) x) +
            ∫ x, φ x * quantizeUniformCLM (spatialDeriv j c) (hc.spatialDeriv j) u x := by
          have hcomm (x : CoordinateSpace n) :
              φ x * quantizeUniformCLM c hc (∂_{e} u) x =
                φ x • ∂_{e} (quantizeUniformCLM c hc u) x -
                  φ x * quantizeUniformCLM (spatialDeriv j c) (hc.spatialDeriv j) u x := by
            have hx := congrArg (fun f : 𝓢(CoordinateSpace n, ℂ) ↦ f x)
              (lineDerivOp_quantizeUniformCLM c hc j u)
            simp only [add_apply, smul_eq_mul] at hx ⊢
            linear_combination -(φ x) * hx
          simp_rw [hcomm]
          have hint₁ : Integrable (fun x ↦ φ x • ∂_{e} (quantizeUniformCLM c hc u) x) :=
            φ.integrable.smul_of_top_left (∂_{e} (quantizeUniformCLM c hc u)).memLp_top
          have hint₂ : Integrable (fun x ↦
              φ x * quantizeUniformCLM (spatialDeriv j c) (hc.spatialDeriv j) u x) :=
            φ.integrable.smul_of_top_left
              (quantizeUniformCLM (spatialDeriv j c) (hc.spatialDeriv j) u).memLp_top
          rw [integral_sub hint₁ hint₂]
          ring
      _ = ∫ x, u x • ψ₂ x := by
          rw [SchwartzMap.integral_smul_lineDerivOp_right_eq_neg_left φ (quantizeUniformCLM c hc u)
            e, neg_neg]
          simp only [ψ₂, add_apply, smul_eq_mul, mul_add]
          have hint₃ : Integrable (fun x ↦
              u x * quantizeRightUniformCLM c.reflectFrequency hc.reflectFrequency (∂_{e} φ) x) :=
            u.integrable.smul_of_top_left (quantizeRightUniformCLM _ _ (∂_{e} φ)).memLp_top
          have hint₄ : Integrable (fun x ↦
              u x * quantizeRightUniformCLM (spatialDeriv j c).reflectFrequency
                (hc.spatialDeriv j).reflectFrequency φ x) :=
            u.integrable.smul_of_top_left (quantizeRightUniformCLM _ _ φ).memLp_top
          rw [← integral_mul_quantizeRightUniformCLM_reflectFrequency hc (∂_{e} φ) u,
            ← integral_mul_quantizeRightUniformCLM_reflectFrequency (hc.spatialDeriv j) φ u,
            ← integral_add hint₃ hint₄]
  have hae : (⇑ψ₁ : CoordinateSpace n → ℂ) =ᵐ[volume] ⇑ψ₂ :=
    (ψ₁.coeFn_toLp 1 volume).symm.trans
      (by rw [Lp.toTemperedDistribution_injective hdist]; exact ψ₂.coeFn_toLp 1 volume)
  exact SchwartzMap.ext (congrFun ((ψ₁.continuous.ae_eq_iff_eq volume ψ₂.continuous).1 hae))

private theorem quantizeRightUniformCLM_const_id (φ : 𝓢(CoordinateSpace n, ℂ)) :
    quantizeRightUniformCLM (const (ContinuousLinearMap.id ℂ ℂ))
      (isUniform_const (ContinuousLinearMap.id ℂ ℂ)) φ = φ := by
  have hF : 𝓕 (quantizeRightUniformCLM (const (ContinuousLinearMap.id ℂ ℂ))
      (isUniform_const (ContinuousLinearMap.id ℂ ℂ)) φ) = 𝓕 φ := by
    ext ζ
    rw [fourier_quantizeRightUniformCLM]
    simp [SchwartzMap.fourier_coe]
  calc _ = 𝓕⁻ (𝓕 (quantizeRightUniformCLM (const (ContinuousLinearMap.id ℂ ℂ))
          (isUniform_const _) φ)) := (FourierTransform.fourierInv_fourier_eq _).symm
    _ = 𝓕⁻ (𝓕 φ) := by rw [hF]
    _ = φ := FourierTransform.fourierInv_fourier_eq φ

end Scalar

/-! ### Vector-valued tempered quantization -/

section VectorValued

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℂ U]

private theorem postcomp_apply_apply {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (L : A →L[ℂ] B)
    (u : 𝓢'(CoordinateSpace n, A)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) L u φ = L (u φ) :=
  (rfl)

private def coordCLM (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (i : Fin (Module.finrank ℂ X)) : X →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℂ X).coord i)

private def basisVecCLM (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [FiniteDimensional ℂ X] (i : Fin (Module.finrank ℂ X)) : ℂ →L[ℂ] X :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (Module.finBasis ℂ X i)

private theorem sum_basisVecCLM_coordCLM {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [FiniteDimensional ℂ X] (x : X) :
    ∑ i, basisVecCLM X i (coordCLM X i x) = x := by
  simp [basisVecCLM, coordCLM, Module.Basis.coord_apply]

/-- The continuous `ℝ`-linear map extracting the `(v, ℓ)` scalar operator `z ↦ z • ℓ (T v)` from
`T : A →L[ℂ] B`. -/
private def entryMap {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (v : A) (ℓ : B →L[ℂ] ℂ) :
    (A →L[ℂ] B) →L[ℝ] (ℂ →L[ℂ] ℂ) :=
  ((ContinuousLinearMap.compL ℂ ℂ B ℂ ℓ).comp
    ((ContinuousLinearMap.compL ℂ ℂ A B).flip
      ((ContinuousLinearMap.id ℂ ℂ).smulRight v))).restrictScalars ℝ

private theorem entryMap_apply_apply {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (v : A) (ℓ : B →L[ℂ] ℂ) (T : A →L[ℂ] B) (z : ℂ) :
    entryMap v ℓ T z = z * ℓ (T v) := by
  simp [entryMap, smul_eq_mul]

private theorem sum_basisVecCLM_entryMap (T : V →L[ℂ] W) (x : V) :
    ∑ i, ∑ j, basisVecCLM W j
      (entryMap (Module.finBasis ℂ V i) (coordCLM W j) T (coordCLM V i x)) = T x := by
  have hrow (i : Fin (Module.finrank ℂ V)) :
      ∑ j, basisVecCLM W j
        (entryMap (Module.finBasis ℂ V i) (coordCLM W j) T (coordCLM V i x)) =
        coordCLM V i x • T (Module.finBasis ℂ V i) := by
    calc ∑ j, basisVecCLM W j
          (entryMap (Module.finBasis ℂ V i) (coordCLM W j) T (coordCLM V i x))
        = coordCLM V i x •
            ∑ j, basisVecCLM W j (coordCLM W j (T (Module.finBasis ℂ V i))) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp [entryMap_apply_apply, basisVecCLM, mul_smul]
      _ = coordCLM V i x • T (Module.finBasis ℂ V i) := by
          rw [sum_basisVecCLM_coordCLM]
  simp_rw [hrow, ← map_smul, ← map_sum]
  simpa [basisVecCLM] using congrArg T (sum_basisVecCLM_coordCLM x)

/-- **Extension of uniform pseudodifferential operators to tempered distributions.** For a symbol
`a` of order `m` on `ℝⁿ` between finite-dimensional complex normed spaces whose derivative bounds
are uniform in the position (`TauCeti.Symbol.IsUniform`), `a.quantizeTemperedCLM ha` is the
continuous linear extension `𝓢'(ℝⁿ, V) →L[ℂ] 𝓢'(ℝⁿ, W)` of `TauCeti.Symbol.quantizeUniformCLM`. -/
def quantizeTemperedCLM (a : Symbol n V W m) (ha : a.IsUniform) :
    𝓢'(CoordinateSpace n, V) →L[ℂ] 𝓢'(CoordinateSpace n, W) :=
  ∑ i, ∑ j,
    (PointwiseConvergenceCLM.postcomp _ (basisVecCLM W j)).comp
      ((quantizeTemperedScalar
          (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))) (ha.map _)).comp
        (PointwiseConvergenceCLM.postcomp _ (coordCLM V i)))

private theorem quantizeTemperedCLM_apply (a : Symbol n V W m) (ha : a.IsUniform)
    (u : 𝓢'(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    a.quantizeTemperedCLM ha u φ =
      ∑ i, ∑ j, basisVecCLM W j (coordCLM V i (u (quantizeRightUniformCLM
        (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency
        (ha.map _).reflectFrequency φ))) := by
  simp only [quantizeTemperedCLM, sum_apply, ContinuousLinearMap.comp_apply, postcomp_apply_apply,
    quantizeTemperedScalar_apply]

private theorem sum_basisVecCLM_quantizeUniformCLM_entry [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) (ha : a.IsUniform) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    ∑ i, ∑ j, basisVecCLM W j (quantizeUniformCLM
        (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))) (ha.map _)
        (u.postcompCLM (coordCLM V i)) x) = quantizeUniformCLM a ha u x := by
  have hFu (i : Fin (Module.finrank ℂ V)) (ζ : CoordinateSpace n) :
      𝓕 (u.postcompCLM (coordCLM V i)) ζ = coordCLM V i (𝓕 u ζ) := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq,
      ← (coordCLM V i).integral_comp_comm ((Real.fourierIntegral_convergent_iff ζ).2 u.integrable)]
    exact integral_congr_ae (.of_forall fun y ↦ by simp)
  have hentry (i : Fin (Module.finrank ℂ V)) (j : Fin (Module.finrank ℂ W)) :
      basisVecCLM W j (quantizeUniformCLM
        (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))) (ha.map _)
        (u.postcompCLM (coordCLM V i)) x) =
        ∫ ζ, 𝐞 ⟪ζ, x⟫ • basisVecCLM W j (entryMap (Module.finBasis ℂ V i) (coordCLM W j)
          (a.coefficient (x, (2 * π) • ζ)) (coordCLM V i (𝓕 u ζ))) ∧
      Integrable (fun ζ : CoordinateSpace n ↦ 𝐞 ⟪ζ, x⟫ •
        basisVecCLM W j (entryMap (Module.finBasis ℂ V i) (coordCLM W j)
          (a.coefficient (x, (2 * π) • ζ)) (coordCLM V i (𝓕 u ζ)))) := by
    obtain ⟨C', -, hC'⟩ :=
      (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).exists_bound_coefficient_slice x
    have hint' := integrable_quantizeSchwartzValue_integrand
      ((a.map (entryMap (Module.finBasis ℂ V i)
        (coordCLM W j))).continuous_coefficient_slice x).aestronglyMeasurable
      hC' (𝓕 (u.postcompCLM (coordCLM V i)))
    have hcongr (ζ : CoordinateSpace n) :
        basisVecCLM W j (𝐞 ⟪ζ, x⟫ •
          (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).coefficient
            (x, (2 * π) • ζ) (𝓕 (u.postcompCLM (coordCLM V i)) ζ)) =
        𝐞 ⟪ζ, x⟫ • basisVecCLM W j (entryMap (Module.finBasis ℂ V i) (coordCLM W j)
          (a.coefficient (x, (2 * π) • ζ)) (coordCLM V i (𝓕 u ζ))) := by
      rw [Circle.smul_def, map_smul, ← Circle.smul_def, coefficient_map, hFu]
    refine ⟨?_, ((basisVecCLM W j).integrable_comp hint').congr (.of_forall hcongr)⟩
    rw [quantizeUniformCLM_apply, quantizeSchwartzValue_def,
      ← (basisVecCLM W j).integral_comp_comm hint']
    exact integral_congr_ae (.of_forall hcongr)
  simp_rw [(hentry _ _).1]
  rw [← Finset.sum_congr rfl fun i _ ↦
      integral_finsetSum Finset.univ (fun j _ ↦ (hentry i j).2),
    ← integral_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum Finset.univ fun j _ ↦ (hentry i j).2,
    quantizeUniformCLM_apply, quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  simp_rw [← Finset.smul_sum, sum_basisVecCLM_entryMap]

/-- **Compatibility with Schwartz quantization.** On a Schwartz function `u`,
`a.quantizeTemperedCLM ha` agrees with `a.quantizeUniformCLM ha`. -/
@[simp]
theorem quantizeTemperedCLM_toTemperedDistribution (a : Symbol n V W m) (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeTemperedCLM ha (u : 𝓢'(CoordinateSpace n, V)) =
      (quantizeUniformCLM a ha u : 𝓢'(CoordinateSpace n, W)) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  have : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
  ext φ
  have hpost (i : Fin (Module.finrank ℂ V)) :
      PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) (coordCLM V i)
        (u : 𝓢'(CoordinateSpace n, V)) =
        (u.postcompCLM (coordCLM V i) : 𝓢'(CoordinateSpace n, ℂ)) := by
    ext ψ
    rw [postcomp_apply_apply, ← SchwartzMap.toTemperedDistributionCLM_postcompCLM_apply]
  have hpostW (i : Fin (Module.finrank ℂ V)) (j : Fin (Module.finrank ℂ W)) :
      PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) (basisVecCLM W j)
        (quantizeUniformCLM (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))) (ha.map _)
          (u.postcompCLM (coordCLM V i)) : 𝓢'(CoordinateSpace n, ℂ)) φ =
        ((quantizeUniformCLM (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))) (ha.map _)
          (u.postcompCLM (coordCLM V i))).postcompCLM (basisVecCLM W j) :
            𝓢'(CoordinateSpace n, W)) φ := by
    rw [postcomp_apply_apply, ← SchwartzMap.toTemperedDistributionCLM_postcompCLM_apply]
  simp only [quantizeTemperedCLM, sum_apply, ContinuousLinearMap.comp_apply,
    hpost, quantizeTemperedScalar_toTemperedDistribution, hpostW]
  simp only [← sum_apply, ← map_sum]
  congr 2
  ext x
  simpa using sum_basisVecCLM_quantizeUniformCLM_entry a ha u x

/-- Two uniform symbols with the same coefficient induce the same operator on `𝓢'`, even when
considered at different orders. -/
theorem quantizeTemperedCLM_congr {a : Symbol n V W m} (ha : a.IsUniform)
    {b : Symbol n V W m'} (hb : b.IsUniform) (h : a.coefficient = b.coefficient) :
    a.quantizeTemperedCLM ha = b.quantizeTemperedCLM hb := by
  ext u φ
  simp only [quantizeTemperedCLM_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  set E := entryMap (Module.finBasis ℂ V i) (coordCLM W j)
  rw [quantizeRightUniformCLM_congr (ha.map E).reflectFrequency (hb.map E).reflectFrequency
    (funext fun p ↦ by simp [h])]

/-- The tempered quantization is additive in the symbol. -/
theorem quantizeTemperedCLM_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) :
    (a + b).quantizeTemperedCLM (ha.add hb) =
      a.quantizeTemperedCLM ha + b.quantizeTemperedCLM hb := by
  ext u φ
  rw [add_apply, add_apply, quantizeTemperedCLM_apply, quantizeTemperedCLM_apply,
    quantizeTemperedCLM_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  set E := entryMap (Module.finBasis ℂ V i) (coordCLM W j)
  rw [quantizeRightUniformCLM_congr ((ha.add hb).map E).reflectFrequency
      (((ha.map E).reflectFrequency).add ((hb.map E).reflectFrequency))
      (funext fun p ↦ by simp),
    quantizeRightUniformCLM_add (ha.map E).reflectFrequency (hb.map E).reflectFrequency,
    add_apply, map_add, map_add, map_add]

/-- The tempered quantization is homogeneous in the symbol. -/
theorem quantizeTemperedCLM_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) :
    (c • a).quantizeTemperedCLM (ha.smul c) = c • a.quantizeTemperedCLM ha := by
  ext u φ
  rw [smul_apply, smul_apply, quantizeTemperedCLM_apply, quantizeTemperedCLM_apply,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  set E := entryMap (Module.finBasis ℂ V i) (coordCLM W j)
  rw [quantizeRightUniformCLM_congr ((ha.smul c).map E).reflectFrequency
      (((ha.map E).reflectFrequency).smul c)
      (funext fun p ↦ ContinuousLinearMap.ext fun z ↦ by
        simp [E, entryMap_apply_apply]; ring),
    quantizeRightUniformCLM_smul (ha.map E).reflectFrequency c,
    smul_apply, map_smul, map_smul, map_smul]

/-- The zero symbol quantizes to `0` on tempered distributions. -/
@[simp]
theorem quantizeTemperedCLM_zero (h : (0 : Symbol n V W m).IsUniform) :
    (0 : Symbol n V W m).quantizeTemperedCLM h = 0 := by
  simpa using quantizeTemperedCLM_smul h 0

/-- The tempered quantization commutes with negation of the symbol. -/
theorem quantizeTemperedCLM_neg {a : Symbol n V W m} (ha : a.IsUniform) :
    (-a).quantizeTemperedCLM ha.neg = -a.quantizeTemperedCLM ha := by
  rw [quantizeTemperedCLM_congr ha.neg (ha.smul (-1)) (by ext p; simp),
    quantizeTemperedCLM_smul ha (-1), neg_one_smul]

/-- The tempered quantization commutes with subtraction of uniform symbols. -/
theorem quantizeTemperedCLM_sub {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) :
    (a - b).quantizeTemperedCLM (ha.sub hb) =
      a.quantizeTemperedCLM ha - b.quantizeTemperedCLM hb := by
  rw [quantizeTemperedCLM_congr (ha.sub hb) (ha.add hb.neg) (by simp [sub_eq_add_neg]),
    quantizeTemperedCLM_add ha hb.neg, quantizeTemperedCLM_neg hb, sub_eq_add_neg]

/-- The tempered quantization commutes with finite sums of uniform symbols. -/
theorem quantizeTemperedCLM_sum {ι : Type*} (s : Finset ι) (a : ι → Symbol n V W m)
    (ha : ∀ i, (a i).IsUniform) :
    (∑ i ∈ s, a i).quantizeTemperedCLM (IsUniform.sum fun i _ ↦ ha i) =
      ∑ i ∈ s, (a i).quantizeTemperedCLM (ha i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [quantizeTemperedCLM_congr _ (isUniform_zero (m := m)) (by simp),
      quantizeTemperedCLM_zero, Finset.sum_empty]
  | insert i₀ s hi₀ ih =>
    have hs : (∑ i ∈ s, a i).IsUniform := IsUniform.sum fun i _ ↦ ha i
    rw [quantizeTemperedCLM_congr _ ((ha i₀).add hs) (by simp [Finset.sum_insert hi₀]),
      quantizeTemperedCLM_add (ha i₀) hs, ih, Finset.sum_insert hi₀]

/-- The tempered quantization does not depend on the order at which the symbol is considered. -/
theorem quantizeTemperedCLM_inclusion {a : Symbol n V W m} (ha : a.IsUniform) (h : m ≤ m') :
    (inclusion h a).quantizeTemperedCLM (ha.inclusion h) = a.quantizeTemperedCLM ha :=
  quantizeTemperedCLM_congr (ha.inclusion h) ha (coefficient_inclusion h a)

private theorem quantizationKernel_map_entryMap [CompleteSpace W] (a : Symbol n V W m)
    (hm : m < -n) (i : Fin (Module.finrank ℂ V)) (j : Fin (Module.finrank ℂ W))
    (x y : CoordinateSpace n) :
    quantizationKernel
      (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).coefficient x y =
      entryMap (Module.finBasis ℂ V i) (coordCLM W j)
        (quantizationKernel a.coefficient x y) := by
  have hint := integrable_quantizationKernel_integrand (a.integrable_coefficient hm x) y
  rw [quantizationKernel_def, quantizationKernel_def,
    ← (entryMap (Module.finBasis ℂ V i) (coordCLM W j)).integral_comp_comm hint]
  refine integral_congr_ae (.of_forall fun ζ ↦ ContinuousLinearMap.ext fun z ↦ ?_)
  simp [Circle.smul_def, entryMap_apply_apply]
  ring

private theorem sum_compLp_quantizeLp_entry [CompleteSpace W]
    (a : Symbol n V W m) (hm : m < -n) (ha : a.IsUniform) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp V p (volume : Measure (CoordinateSpace n))) :
    ∑ i, ∑ j, (basisVecCLM W j).compLp
      (((a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).quantizeLp p hm (ha.map _))
        ((coordCLM V i).compLp f)) = a.quantizeLp p hm ha f := by
  set F : Fin (Module.finrank ℂ V) → Fin (Module.finrank ℂ W) →
      Lp W p (volume : Measure (CoordinateSpace n)) := fun i j ↦
    (basisVecCLM W j).compLp
      (((a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).quantizeLp p hm (ha.map _))
        ((coordCLM V i).compLp f))
  have hae_ij (i : Fin (Module.finrank ℂ V)) (j : Fin (Module.finrank ℂ W)) : ∀ᵐ x ∂volume,
      F i j x =
        ∫ y, basisVecCLM W j (entryMap (Module.finBasis ℂ V i) (coordCLM W j)
          (quantizationKernel a.coefficient x y) (coordCLM V i (f y))) ∧
      Integrable (fun y ↦ basisVecCLM W j (entryMap (Module.finBasis ℂ V i) (coordCLM W j)
        (quantizationKernel a.coefficient x y) (coordCLM V i (f y)))) := by
    obtain ⟨Bij, hrow_ij, hcol_ij⟩ := exists_row_col_lintegral_quantizationKernel_le
      (ha.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))) hm
    filter_upwards [(basisVecCLM W j).coeFn_compLp _,
      coeFn_quantizeLp (a := a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j)))
        (hm := hm) (ha := ha.map _) ((coordCLM V i).compLp f),
      ae_integrable_apply_of_memLp ((a.map (entryMap (Module.finBasis ℂ V i)
          (coordCLM W j))).continuous_quantizationKernel hm).aestronglyMeasurable
        (Lp.memLp ((coordCLM V i).compLp f)) (Fact.out : 1 ≤ p)
        (ae_of_all _ hrow_ij) (ae_of_all _ hcol_ij)] with x hx₁ hx₂ hx_int
    have hcongr : (fun y ↦ basisVecCLM W j (quantizationKernel
          (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).coefficient x y
          (((coordCLM V i).compLp f) y))) =ᵐ[volume]
        fun y ↦ basisVecCLM W j (entryMap (Module.finBasis ℂ V i) (coordCLM W j)
          (quantizationKernel a.coefficient x y) (coordCLM V i (f y))) :=
      ((coordCLM V i).coeFn_compLp f).mono fun y hy ↦ by
        dsimp only
        rw [quantizationKernel_map_entryMap a hm i j x y, hy]
    refine ⟨?_, ((basisVecCLM W j).integrable_comp hx_int).congr hcongr⟩
    rw [hx₁, hx₂, ← (basisVecCLM W j).integral_comp_comm hx_int]
    exact integral_congr_ae hcongr
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ ∑ j, F i j),
    eventually_all.2 fun i ↦ Lp.coeFn_finsetSum Finset.univ (fun j ↦ F i j),
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ hae_ij i j,
    coeFn_quantizeLp (a := a) (hm := hm) (ha := ha) f] with x hsum₁ hsum₂ hij hx
  rw [hsum₁, hx, Finset.sum_apply]
  calc ∑ i, (∑ j, F i j) x
      = ∑ i, ∑ j, ∫ y, basisVecCLM W j (entryMap (Module.finBasis ℂ V i) (coordCLM W j)
          (quantizationKernel a.coefficient x y) (coordCLM V i (f y))) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hsum₂ i, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ ↦ (hij i j).1
    _ = ∫ y, ∑ i, ∑ j, basisVecCLM W j (entryMap (Module.finBasis ℂ V i) (coordCLM W j)
          (quantizationKernel a.coefficient x y) (coordCLM V i (f y))) := by
        rw [← Finset.sum_congr rfl fun i _ ↦
            integral_finsetSum Finset.univ (fun j _ ↦ (hij i j).2),
          ← integral_finsetSum Finset.univ fun i _ ↦
            integrable_finsetSum Finset.univ fun j _ ↦ (hij i j).2]
    _ = ∫ y, quantizationKernel a.coefficient x y (f y) := by
        simp_rw [sum_basisVecCLM_entryMap]

/-- **Compatibility with `quantizeLp`.** When `m < -n`, `a.quantizeTemperedCLM ha` agrees on every
`Lᵖ(ℝⁿ; V)` (`1 ≤ p ≤ ∞`) with the Schur integral operator `a.quantizeLp p hm ha`. -/
theorem quantizeTemperedCLM_lp [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    (hm : m < -n) (ha : a.IsUniform) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp V p (volume : Measure (CoordinateSpace n))) :
    a.quantizeTemperedCLM ha (f : 𝓢'(CoordinateSpace n, V)) =
      (a.quantizeLp p hm ha f : 𝓢'(CoordinateSpace n, W)) := by
  have hpostV (i : Fin (Module.finrank ℂ V)) :
      PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) (coordCLM V i)
        (f : 𝓢'(CoordinateSpace n, V)) =
        ((coordCLM V i).compLp f : 𝓢'(CoordinateSpace n, ℂ)) := by
    ext φ
    exact (Lp.toTemperedDistribution_compLp_apply (coordCLM V i) f φ).symm
  have hpostW (g : Lp ℂ p (volume : Measure (CoordinateSpace n))) (j : Fin (Module.finrank ℂ W)) :
      PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) (basisVecCLM W j)
        (g : 𝓢'(CoordinateSpace n, ℂ)) =
        ((basisVecCLM W j).compLp g : 𝓢'(CoordinateSpace n, W)) := by
    ext φ
    exact (Lp.toTemperedDistribution_compLp_apply (basisVecCLM W j) g φ).symm
  simp only [quantizeTemperedCLM, sum_apply, ContinuousLinearMap.comp_apply,
    hpostV, quantizeTemperedScalar_lp _ hm, hpostW]
  simp_rw [← Lp.toTemperedDistribution_sum, sum_compLp_quantizeLp_entry a hm ha f]

/-- **Exact right composition with a scalar Fourier multiplier on `𝓢'`.** If `g` has temperate
growth and `b` is a uniform symbol with `b(x, ξ) = g(ξ / 2π) a(x, ξ)`, then
`Op(a) (g(D) u) = Op(b) u` for every tempered distribution `u`. -/
theorem quantizeTemperedCLM_fourierMultiplierCLM_of_coefficient_eq
    {a : Symbol n V W m} (ha : a.IsUniform) {b : Symbol n V W m'} (hb : b.IsUniform)
    {g : CoordinateSpace n → ℂ} (hg : g.HasTemperateGrowth)
    (hcoeff : ∀ p, b.coefficient p = g ((2 * π)⁻¹ • p.2) • a.coefficient p)
    (u : 𝓢'(CoordinateSpace n, V)) :
    a.quantizeTemperedCLM ha (TemperedDistribution.fourierMultiplierCLM V g u) =
      b.quantizeTemperedCLM hb u := by
  simp only [quantizeTemperedCLM, sum_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  have hpost : PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) (coordCLM V i)
      (TemperedDistribution.fourierMultiplierCLM V g u) =
      TemperedDistribution.fourierMultiplierCLM ℂ g
        (PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) (coordCLM V i) u) := rfl
  rw [hpost]
  exact quantizeTemperedScalar_fourierMultiplierCLM (ha.map _) (hb.map _) hg
    (fun p ↦ ContinuousLinearMap.ext fun z ↦ by
      simp [entryMap_apply_apply, hcoeff p]; ring) _

/-- **Exact right composition with the Bessel potential on `𝓢'`.** For every uniform symbol `a` of
order `m`, real `t`, and `u ∈ 𝓢'(ℝⁿ, V)`,
`Op(a) (J^t u) = Op(a ∘ ⟨ξ / 2π⟩^t) u`. -/
theorem quantizeTemperedCLM_besselPotential (a : Symbol n V W m) (ha : a.IsUniform) (t : ℝ)
    (u : 𝓢'(CoordinateSpace n, V)) :
    a.quantizeTemperedCLM ha (TemperedDistribution.besselPotential (CoordinateSpace n) V t u) =
      (a.comp (besselPotential t)).quantizeTemperedCLM
        (ha.comp (isUniform_besselPotential t)) u := by
  rw [TemperedDistribution.besselPotential]
  exact quantizeTemperedCLM_fourierMultiplierCLM_of_coefficient_eq ha
    (ha.comp (isUniform_besselPotential t)) (by fun_prop)
    (fun p ↦ by simp [ContinuousLinearMap.comp_smul]) u

/-- **Spatial derivative commutator on `𝓢'`.** For every uniform symbol `a`, coordinate index `j`,
and tempered distribution `u`, `∂_j (Op(a) u) = Op(a) (∂_j u) + Op(∂_{x_j} a) u`. -/
theorem lineDerivOp_quantizeTemperedCLM (a : Symbol n V W m) (ha : a.IsUniform) (j : Fin n)
    (u : 𝓢'(CoordinateSpace n, V)) :
    ∂_{EuclideanSpace.single j (1 : ℝ)} (a.quantizeTemperedCLM ha u) =
      a.quantizeTemperedCLM ha (∂_{EuclideanSpace.single j (1 : ℝ)} u) +
        (spatialDeriv j a).quantizeTemperedCLM (ha.spatialDeriv j) u := by
  ext (φ : 𝓢(CoordinateSpace n, ℂ))
  simp only [TemperedDistribution.lineDerivOp_apply_apply, add_apply, quantizeTemperedCLM_apply,
    map_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  set E := entryMap (Module.finBasis ℂ V i) (coordCLM W k)
  rw [← map_neg (basisVecCLM W k), ← map_neg (basisVecCLM W k), ← map_add (basisVecCLM W k)]
  congr 1
  rw [lineDerivOp_quantizeRightUniformCLM_scalar (ha.map E) j φ,
    quantizeRightUniformCLM_congr (((ha.spatialDeriv j).map E).reflectFrequency)
      ((ha.map E).spatialDeriv j).reflectFrequency
      (congrArg Symbol.coefficient
        (congrArg reflectFrequency (spatialDeriv_map E a j).symm)),
    map_add, map_add]
  abel

private theorem sum_reflectFrequency_postcomp (L : W →L[ℂ] U) (a : Symbol n V W m)
    (i : Fin (Module.finrank ℂ V)) (k : Fin (Module.finrank ℂ U)) :
    ∑ j, coordCLM U k (L (Module.finBasis ℂ W j)) •
        (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency =
      ((a.map ((ContinuousLinearMap.compL ℂ V W U L).restrictScalars ℝ)).map
        (entryMap (Module.finBasis ℂ V i) (coordCLM U k))).reflectFrequency := by
  refine Symbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun z ↦ ?_)
  simp only [coefficient_sum, Finset.sum_apply, FunLike.coe_sum, coefficient_smul,
    Pi.smul_apply, smul_apply, coefficient_reflectFrequency, coefficient_map, entryMap_apply_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  calc ∑ j, coordCLM U k (L (Module.finBasis ℂ W j)) *
        (z * coordCLM W j (a.coefficient (p.1, -p.2) (Module.finBasis ℂ V i)))
      = z * ∑ j, coordCLM U k (L (basisVecCLM W j
          (coordCLM W j (a.coefficient (p.1, -p.2) (Module.finBasis ℂ V i))))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [basisVecCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
          map_smul, smul_eq_mul]
        ring
    _ = z * coordCLM U k (L (a.coefficient (p.1, -p.2) (Module.finBasis ℂ V i))) := by
        rw [← map_sum (coordCLM U k), ← map_sum L, sum_basisVecCLM_coordCLM]

/-- **Postcomposition naturality.** Applying `L : W →L[ℂ] U` to `Op(a) u` equals `Op(L ∘ a) u`. -/
theorem postcomp_quantizeTemperedCLM (L : W →L[ℂ] U) (a : Symbol n V W m) (ha : a.IsUniform)
    (u : 𝓢'(CoordinateSpace n, V)) :
    PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) L (a.quantizeTemperedCLM ha u) =
      (a.map ((ContinuousLinearMap.compL ℂ V W U L).restrictScalars ℝ)).quantizeTemperedCLM
        (ha.map _) u := by
  ext φ
  rw [postcomp_apply_apply, quantizeTemperedCLM_apply, quantizeTemperedCLM_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_sum]
  have hL (j : Fin (Module.finrank ℂ W)) (z : ℂ) :
      L (basisVecCLM W j z) =
        ∑ k, basisVecCLM U k (coordCLM U k (L (Module.finBasis ℂ W j)) * z) := by
    conv_lhs => rw [← sum_basisVecCLM_coordCLM (L (basisVecCLM W j z))]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [basisVecCLM, smul_eq_mul, mul_comm]
  simp_rw [hL]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp_rw [← map_sum (basisVecCLM U k), ← smul_eq_mul, ← map_smul (coordCLM V i),
    ← map_sum (coordCLM V i), ← map_smul u, ← map_sum u]
  congr 3
  have hR := congrArg (fun T ↦ T φ) (quantizeRightUniformCLM_sum Finset.univ
    (fun j ↦ coordCLM U k (L (Module.finBasis ℂ W j)) •
      (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency)
    (fun j ↦ ((ha.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency).smul
      (coordCLM U k (L (Module.finBasis ℂ W j)))))
  rw [sum_apply] at hR
  have hterm (j : Fin (Module.finrank ℂ W)) :
      quantizeRightUniformCLM
        (coordCLM U k (L (Module.finBasis ℂ W j)) •
          (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency)
        (((ha.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency).smul
          (coordCLM U k (L (Module.finBasis ℂ W j)))) φ =
        coordCLM U k (L (Module.finBasis ℂ W j)) •
          quantizeRightUniformCLM
            (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency
            (ha.map _).reflectFrequency φ := by
    rw [quantizeRightUniformCLM_smul, smul_apply]
  simp_rw [hterm] at hR
  rw [← hR, quantizeRightUniformCLM_congr _ _
    (congrArg Symbol.coefficient (sum_reflectFrequency_postcomp L a i k))]

private theorem sum_reflectFrequency_precomp (M : U →L[ℂ] V) (a : Symbol n V W m)
    (k : Fin (Module.finrank ℂ U)) (j : Fin (Module.finrank ℂ W)) :
    ∑ i, coordCLM V i (M (Module.finBasis ℂ U k)) •
        (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency =
      ((a.map (((ContinuousLinearMap.compL ℂ U V W).flip M).restrictScalars ℝ)).map
        (entryMap (Module.finBasis ℂ U k) (coordCLM W j))).reflectFrequency := by
  refine Symbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun z ↦ ?_)
  simp only [coefficient_sum, Finset.sum_apply, FunLike.coe_sum, coefficient_smul,
    Pi.smul_apply, smul_apply, coefficient_reflectFrequency, coefficient_map, entryMap_apply_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  calc ∑ i, coordCLM V i (M (Module.finBasis ℂ U k)) *
        (z * coordCLM W j (a.coefficient (p.1, -p.2) (Module.finBasis ℂ V i)))
      = z * coordCLM W j (a.coefficient (p.1, -p.2)
          (∑ i, basisVecCLM V i (coordCLM V i (M (Module.finBasis ℂ U k))))) := by
        rw [map_sum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [basisVecCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
          map_smul, smul_eq_mul]
        ring
    _ = z * coordCLM W j (a.coefficient (p.1, -p.2) (M (Module.finBasis ℂ U k))) := by
        rw [sum_basisVecCLM_coordCLM]

/-- **Precomposition naturality.** Applying `Op(a)` to `M u` (`M : U →L[ℂ] V`) equals
`Op(a ∘ M) u`. -/
theorem quantizeTemperedCLM_postcomp (M : U →L[ℂ] V) (a : Symbol n V W m) (ha : a.IsUniform)
    (u : 𝓢'(CoordinateSpace n, U)) :
    a.quantizeTemperedCLM ha (PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) M u) =
      (a.map (((ContinuousLinearMap.compL ℂ U V W).flip M).restrictScalars ℝ)).quantizeTemperedCLM
        (ha.map _) u := by
  ext φ
  rw [quantizeTemperedCLM_apply, quantizeTemperedCLM_apply]
  have hM (i : Fin (Module.finrank ℂ V)) (ψ : 𝓢(CoordinateSpace n, ℂ)) :
      coordCLM V i ((PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) M u) ψ) =
        ∑ k, coordCLM U k (u (coordCLM V i (M (Module.finBasis ℂ U k)) • ψ)) := by
    rw [postcomp_apply_apply]
    conv_lhs => rw [← sum_basisVecCLM_coordCLM (u ψ)]
    simp only [basisVecCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [mul_comm, ← smul_eq_mul, ← map_smul (coordCLM U k), ← map_smul u]
  simp_rw [hM]
  have hswap (i : Fin (Module.finrank ℂ V)) :
      (∑ j, basisVecCLM W j (∑ k, coordCLM U k
        (u (coordCLM V i (M (Module.finBasis ℂ U k)) •
          quantizeRightUniformCLM
            (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency
            (ha.map _).reflectFrequency φ)))) =
      ∑ k, ∑ j, basisVecCLM W j (coordCLM U k
        (u (coordCLM V i (M (Module.finBasis ℂ U k)) •
          quantizeRightUniformCLM
            (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency
            (ha.map _).reflectFrequency φ))) := by
    simp_rw [map_sum]
    exact Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp_rw [← map_sum (basisVecCLM W j), ← map_sum (coordCLM U k), ← map_sum u]
  congr 3
  have hR := congrArg (fun T ↦ T φ) (quantizeRightUniformCLM_sum Finset.univ
    (fun i ↦ coordCLM V i (M (Module.finBasis ℂ U k)) •
      (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency)
    (fun i ↦ ((ha.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency).smul
      (coordCLM V i (M (Module.finBasis ℂ U k)))))
  rw [sum_apply] at hR
  have hterm (i : Fin (Module.finrank ℂ V)) :
      quantizeRightUniformCLM
        (coordCLM V i (M (Module.finBasis ℂ U k)) •
          (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency)
        (((ha.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency).smul
          (coordCLM V i (M (Module.finBasis ℂ U k)))) φ =
        coordCLM V i (M (Module.finBasis ℂ U k)) •
          quantizeRightUniformCLM
            (a.map (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency
            (ha.map _).reflectFrequency φ := by
    rw [quantizeRightUniformCLM_smul, smul_apply]
  simp_rw [hterm] at hR
  rw [← hR, quantizeRightUniformCLM_congr _ _
    (congrArg Symbol.coefficient (sum_reflectFrequency_precomp M a k j))]

/-- A constant symbol `T` quantizes on tempered distributions to postcomposition with `T`. -/
@[simp]
theorem quantizeTemperedCLM_const (T : V →L[ℂ] W) :
    (const T : Symbol n V W 0).quantizeTemperedCLM (isUniform_const T) =
      PointwiseConvergenceCLM.postcomp 𝓢(CoordinateSpace n, ℂ) T := by
  ext u φ
  rw [quantizeTemperedCLM_apply, postcomp_apply_apply]
  have hR (i : Fin (Module.finrank ℂ V)) (j : Fin (Module.finrank ℂ W)) :
      quantizeRightUniformCLM
        ((const T : Symbol n V W 0).map
          (entryMap (Module.finBasis ℂ V i) (coordCLM W j))).reflectFrequency
        ((isUniform_const T).map _).reflectFrequency φ =
        coordCLM W j (T (Module.finBasis ℂ V i)) • φ := by
    set c₀ := coordCLM W j (T (Module.finBasis ℂ V i))
    rw [quantizeRightUniformCLM_congr _
        ((isUniform_const (n := n) (ContinuousLinearMap.id ℂ ℂ)).smul c₀)
        (funext fun p ↦ ContinuousLinearMap.ext fun z ↦ by
          simp [c₀, entryMap_apply_apply]; ring),
      quantizeRightUniformCLM_smul (isUniform_const (n := n) (ContinuousLinearMap.id ℂ ℂ)) c₀,
      smul_apply, quantizeRightUniformCLM_const_id]
  refine (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_).trans
    (sum_basisVecCLM_entryMap T (u φ))
  rw [hR i j, map_smul, map_smul, smul_eq_mul, mul_comm, ← entryMap_apply_apply]

end VectorValued

end Symbol

end TauCeti
