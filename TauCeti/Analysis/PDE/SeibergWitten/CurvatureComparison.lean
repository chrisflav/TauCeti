/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Rescaling
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.MeasureTheory.Measure.Haar.LinearMap

/-!
# The cutoff current and the curvature current against test forms

Let `(a, α)` be an abelian Higgs pair with `a = i b`, on a finite-dimensional real normed space
`E` of dimension `2 + n` carrying an almost complex structure `J`. Its cutoff current
`Θ = i F_a + d(χ(|α|²) τ)` (`TauCeti.SeibergWitten.cutoffCurrent`) differs from the curvature
current `i F_a = -db` by the exact form `d(χ(|α|²) τ)`. In Taubes's passage from Seiberg–Witten
solutions to pseudoholomorphic curves, `Θ / 2π` is the current that converges to the limiting
curve, and this file shows that `Θ` and `i F_a` have the same pairings with test forms up to an
error controlled by two integrals: that of `|1 - |α|²|` and that of `|∂bar_a α|`.

For a compactly supported test form `ζ` of degree `n`, integration by parts gives

`∫ (Θ - i F_a) ∧ ζ = ∫ χ(|α|²) τ ∧ dζ`

(`TauCeti.SeibergWitten.integral_cutoffCurrent_add_extDeriv_wedge_eq`, and locally
`TauCeti.SeibergWitten.integral_cutoffCurrent_add_extDeriv_wedge_eq_of_contDiffAt` when `(b, α)` is
only smooth on `tsupport ζ`). By the
modulus-potential decomposition `χ(|α|²) τ = d^c_J H(|α|²) + E`
(`TauCeti.SeibergWitten.cutoffPhaseForm_eq_twistedDifferential_add`), a second integration by
parts moves the derivative in `d^c_J H(|α|²)` onto `dζ`
(`TauCeti.AlmostComplexStructure.integral_twistedDifferential_wedge_eq`). The pointwise bounds
`|H(s)| ≤ |s - 1| / c` and `|E| ≤ (2 / √c) |∂bar_a α|`, for a cutoff `χ` vanishing below `c`,
then give

`|∫ (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c ∫_K |1 - |α|²| + A₁ / √c ∫_K |∂bar_a α|)`

(`TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le`). Here `K` is a
compact set containing the support of `ζ`, `A₁` bounds `|dζ|` and `A₂` bounds the derivative of
`dζ`, so `A₁` and `A₂` are controlled by the `C²` norm of `ζ`. The constant `C` depends only on
`J` and on the basis used to integrate top-degree forms. For a family of fields with
`∫_K |1 - |α|²| = O(h²)` and `∫_K |∂bar_a α| = O(h)`, the right side is `O(h)` for each fixed
test form, so `Θ / 2π` and `i F_a / 2π` have the same weak limits as `h → 0`. For
large-parameter Seiberg–Witten solutions, with `h = (2r)^(-1/2)`, these are the scales of the
coarse estimates on `1 - |α|²` and `∂bar_a α`.

When `J : E → E →L[ℝ] E` is a varying `C¹` almost complex structure on `K`, integrating
`d^c_J H(|α|²) ∧ dζ` by parts differentiates `(-J)^* dζ` and picks up `‖J‖` and `‖DJ‖` alongside
`A₁` and `A₂` (`Module.Basis.exists_abs_integral_twistedDifferentialForm_wedge_le`), giving the
varying-`J` `L¹` and `L²` comparisons
(`TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_of_fderiv_le`,
`TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_sqrt`). On a normal
splitting `E × N` where `J` is `C²` near the `J`-holomorphic zero section `E × {0}`, the normal
dilations `δ_a^* J` have scale-independent `C¹` bounds on compact sets for small `a ≠ 0`
(`TauCeti.exists_eventually_norm_normalDilation_le_of_isOpen`), while partial-dilation Haar
scaling (`MeasureTheory.Measure.setIntegral_comp_prod_smul_right`) divides the unrescaled integrals
over `δ_a(K)` by `|a| ^ finrank ℝ N`. This compares the pulled-back difference `δ_a^* (Θ - i F_a)`
against test forms uniformly as `a → 0`
(`exists_eventually_abs_integral_cutoffCurrent_add_extDeriv_normalDilation_wedge_le`,
`tendsto_integral_cutoffCurrent_add_extDeriv_normalDilation_wedge_zero`).

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {χ : ℝ → ℝ} {ζ : E → E [⋀^Fin n]→L[ℝ] ℝ}

omit [FiniteDimensional ℝ E] in
/-- **The cutoff current against a test form.** For a compactly supported C1 test form `ζ` of
degree `n` on a space of dimension `2 + n`, the pairing of `Θ - i F_a = Θ + db` with `ζ` is the
pairing of the cutoff phase form `χ(|α|²) τ` with `dζ`. Top-degree coefficients are taken on a
basis `e` and integrated against its Haar measure. -/
theorem integral_cutoffCurrent_add_extDeriv_wedge_eq (e : Module.Basis (Fin (2 + n)) ℝ E)
    (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hζ : ContDiff ℝ 1 ζ) (hc : HasCompactSupport ζ) :
    ∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar =
      ∫ x, wedge (cutoffPhaseForm χ b α x) (extDeriv ζ x) (e ∘ Fin.cast (by omega)) ∂e.addHaar := by
  have h := e.integral_extDeriv_wedge_eq_integral_wedge_extDeriv (by omega)
    (contDiff_cutoffPhaseForm hα hb hχ hχ₀) hζ hc
  -- The index cast `1 + 1 + n = 2 + n` is the identity.
  have e₁ : ⇑e ∘ Fin.cast (show 1 + 1 + n = 2 + n by omega) = ⇑e := rfl
  rw [e₁, pow_one, neg_neg, one_mul] at h
  simpa only [cutoffCurrent_apply, sub_add_cancel] using h

variable (J : AlmostComplexStructure E)

/-- **Comparison of the cutoff current with the curvature current.** There is a constant `C`,
depending only on `J` and the basis `e`, with the following property. Let `χ` vanish below
`c > 0` with `|χ| ≤ 1`, and let `ζ` be a `C²` test form of degree `n` supported in a compact set
`K`, with `|dζ| ≤ A₁` and `|D(dζ)| ≤ A₂`. Then

`|∫ (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c ∫_K |1 - |α|²| + A₁ / √c ∫_K |∂bar_a α|)`,

where `Θ - i F_a = Θ + db`. Top-degree coefficients are taken on `e` and integrated against its
Haar measure. -/
theorem exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le
    (e : Module.Basis (Fin (2 + n)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃χ : ℝ → ℝ⦄ ⦃b : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → ℂ⦄
      ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃c A₁ A₂ : ℝ⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ → ContDiff ℝ 2 α →
      ContDiff ℝ 1 b → ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ x, ‖extDeriv ζ x‖ ≤ A₁) → (∀ x, ‖fderiv ℝ (extDeriv ζ) x‖ ≤ A₂) →
      |∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar| ≤
        C * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e.addHaar +
          A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e.addHaar) := by
  let e₁ := e.reindex (finCongr (by omega : 2 + n = 1 + (n + 1)))
  obtain ⟨C₁, hC₁, hIA⟩ := J.exists_abs_integral_twistedDifferential_wedge_le e₁
  obtain ⟨C₂, _, hIB⟩ := e₁.exists_abs_integral_wedge_le
  refine ⟨max C₁ (2 * C₂), by positivity, ?_⟩
  intro χ b α ζ K c A₁ A₂ hc hχc hχ₁ hχ hα hb hζ hK hζK hA₁ hA₂
  have hχ₀ : χ =ᶠ[𝓝 0] 0 := (eventually_lt_nhds hc).mono hχc
  have hcζ : HasCompactSupport ζ := hK.of_isClosed_subset (isClosed_tsupport ζ) hζK
  set η := extDeriv ζ
  have hη : ContDiff ℝ 1 η := contDiff_extDeriv hζ (by norm_num)
  have hcη : HasCompactSupport η := hcζ.extDeriv
  -- Outside `K` the form `dζ` vanishes.
  have hηK : tsupport η ⊆ K := tsupport_extDeriv_subset.trans hζK
  have hη0 (x) (hx : x ∉ K) : η x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK h)
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hA₂0 : 0 ≤ A₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hA₂ 0)
  -- The modulus potential `H(|α|²)` and the decomposition `χ(|α|²) τ = d^c_J H(|α|²) + E`.
  set H := modulusPotential χ
  have hH (t : ℝ) : HasDerivAt H (χ t / t) t := hasDerivAt_modulusPotential hχ.continuous hχ₀ t
  have hs : ContDiff ℝ 1 fun y ↦ normSq (α y) := by
    simp_rw [normSq_eq_norm_sq]
    exact (contDiff_norm_sq ℝ).comp (hα.of_le one_le_two)
  have hg : ContDiff ℝ 1 fun y ↦ H (normSq (α y)) :=
    (contDiff_modulusPotential hχ.continuous hχ₀).comp hs
  have hdec (x : E) : cutoffPhaseForm χ b α x =
      J.twistedDifferential (fun y ↦ H (normSq (α y))) x + cutoffDBarForm J χ b α x :=
    cutoffPhaseForm_eq_twistedDifferential_add J (hH _) (hχc 0 hc)
      (hα.differentiable two_ne_zero x)
  -- Reduce to the pairing of the cutoff phase form with `dζ`, evaluated on `e₁`.
  have he₁ : ⇑e ∘ Fin.cast (show 1 + (n + 1) = 2 + n by omega) = ⇑e₁ :=
    (e.reindex_finCongr_comp_cast _ rfl).symm
  have hμ : e₁.addHaar = e.addHaar := Module.Basis.addHaar_reindex _ _
  rw [integral_cutoffCurrent_add_extDeriv_wedge_eq e hα hb hχ hχ₀ (hζ.of_le one_le_two) hcζ, he₁,
    ← hμ]
  set g := fun y ↦ H (normSq (α y))
  set A := fun x ↦ wedge (J.twistedDifferential g x) (η x) e₁
  set B := fun x ↦ wedge (cutoffDBarForm J χ b α x) (η x) e₁
  have hcw (φ : E → E [⋀^Fin 1]→L[ℝ] ℝ) : HasCompactSupport fun x ↦ wedge (φ x) (η x) e₁ :=
    hcη.wedge_left.comp_left (g := fun ω : E [⋀^Fin (1 + (n + 1))]→L[ℝ] ℝ ↦ ω e₁) rfl
  have hA : Integrable A e₁.addHaar :=
    (((J.contDiff_twistedDifferential (n := 0) hg (by simp)).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcw _)
  have hT : Integrable (fun x ↦ wedge (cutoffPhaseForm χ b α x) (η x) e₁) e₁.addHaar :=
    (((contDiff_cutoffPhaseForm (n := 0) (by simpa using hα.of_le one_le_two)
      (hb.of_le zero_le_one) (hχ.of_le zero_le_one) hχ₀).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcw _)
  have hsplit (x : E) : wedge (cutoffPhaseForm χ b α x) (η x) e₁ = A x + B x := by
    simp only [A, B, hdec, wedge_add_left, ContinuousAlternatingMap.add_apply]
  have hB : Integrable B e₁.addHaar :=
    (hT.sub hA).congr (Eventually.of_forall fun x ↦ by
      rw [Pi.sub_apply, hsplit, add_sub_cancel_left])
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hA hB]
  -- The `d^c_J H(|α|²)` term, by `|H(s)| ≤ |s - 1| / c`.
  have hA' : |∫ x, A x ∂e₁.addHaar| ≤
      C₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) :=
    calc |∫ x, A x ∂e₁.addHaar|
        ≤ C₁ * (A₂ * ∫ x in K, |normSq (α x) - 1| / c ∂e₁.addHaar) :=
          hIA hg hη hK hηK
            (((hs.continuous.sub continuous_const).abs.div_const c).continuousOn
              |>.integrableOn_compact hK)
            (fun x _ ↦ abs_modulusPotential_le hc (fun t _ ht ↦ hχc t ht) hχ₁ (normSq_nonneg _))
            hA₂
      _ = _ := by
          rw [integral_div]
          ring
  -- The correction term `E = 2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J`, by `|E| ≤ (2 / √c) |∂bar_a α|`.
  have hB' : |∫ x, B x ∂e₁.addHaar| ≤
      2 * C₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar) :=
    calc |∫ x, B x ∂e₁.addHaar|
        ≤ C₂ * (A₁ * ∫ x in K, 2 / √c * ‖covariantDBar J b α x‖ ∂e₁.addHaar) :=
          hIB hK.measurableSet hη0
            ((continuous_const.mul (continuous_covariantDBar J (hα.of_le one_le_two)
              hb.continuous).norm).continuousOn.integrableOn_compact hK)
            (fun x _ ↦ norm_cutoffDBarForm_le J hc (fun t _ ht ↦ hχc t ht) hχ₁ b α x) hA₁
      _ = _ := by
          rw [integral_const_mul]
          ring
  calc |∫ x, A x ∂e₁.addHaar + ∫ x, B x ∂e₁.addHaar|
      ≤ |∫ x, A x ∂e₁.addHaar| + |∫ x, B x ∂e₁.addHaar| := abs_add_le _ _
    _ ≤ C₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) +
        2 * C₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar) := add_le_add hA' hB'
    _ ≤ _ := by
        rw [mul_add]
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]

/-! ### Varying almost complex structures and `L²` bounds -/

section VaryingAlmostComplex

omit [FiniteDimensional ℝ E] in
private theorem integrable_wedge_of_contDiffAt {k l : ℕ}
    (b : Module.Basis (Fin (k + l)) ℝ E) {φ : E → E [⋀^Fin k]→L[ℝ] ℝ}
    {η : E → E [⋀^Fin l]→L[ℝ] ℝ} (hφ : ∀ x ∈ tsupport η, ContDiffAt ℝ 0 φ x)
    (hη : ContDiff ℝ 0 η) (hcη : HasCompactSupport η) :
    Integrable (fun x ↦ wedge (φ x) (η x) b) b.addHaar := by
  refine Continuous.integrable_of_hasCompactSupport ?_
    (hcη.wedge_left.comp_left (g := fun ω : E [⋀^Fin (k + l)]→L[ℝ] ℝ ↦ ω b) rfl)
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : x ∈ tsupport η
  · have hw : ContDiffAt ℝ 0 (fun y ↦ wedge (φ y) (η y)) x := by
      simpa only [wedge_def] using contDiffAt_const.pairedWedge (hφ x hx) hη.contDiffAt
    exact (ContinuousAlternatingMap.apply ℝ E ℝ b).continuous.continuousAt.comp hw.continuousAt
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy, wedge_def]

omit [FiniteDimensional ℝ E] in
private theorem integral_extDeriv_wedge_eq_of_contDiffAt
    (e : Module.Basis (Fin (2 + n)) ℝ E) {φ : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    (hφ : ∀ x ∈ tsupport ζ, ContDiffAt ℝ 1 φ x) (hζ : ContDiff ℝ 1 ζ)
    (hc : HasCompactSupport ζ) :
    ∫ x, wedge (extDeriv φ x) (ζ x) e ∂e.addHaar =
      ∫ x, wedge (φ x) (extDeriv ζ x) (e ∘ Fin.cast (by omega)) ∂e.addHaar := by
  have hm₀ : 2 + n = (1 + n) + 1 := by omega
  have hm₁ : 2 + n = 1 + (n + 1) := by omega
  set ω := fun x ↦ wedge (φ x) (ζ x)
  have hω : ContDiff ℝ 1 ω := by
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    by_cases hx : x ∈ tsupport ζ
    · simpa only [ω, wedge_def] using contDiffAt_const.pairedWedge (hφ x hx) hζ.contDiffAt
    · refine (contDiffAt_const (c := (0 : E [⋀^Fin (1 + n)]→L[ℝ] ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport ζ).isOpen_compl.mem_nhds hx] with y hy
      simp [ω, image_eq_zero_of_notMem_tsupport hy, wedge_def]
  let e₀ : Module.Basis (Fin ((1 + n) + 1)) ℝ E := e.reindex (finCongr hm₀)
  let e₁ : Module.Basis (Fin (1 + (n + 1))) ℝ E := e.reindex (finCongr hm₁)
  obtain ⟨hint₀, hzero₀⟩ := e₀.integral_extDeriv_eq_zero hω hc.wedge_left
  rw [e.addHaar_reindex] at hint₀ hzero₀
  have hB : Integrable (fun x ↦ wedge (φ x) (extDeriv ζ x) e₁) e.addHaar :=
    e.addHaar_reindex (finCongr hm₁) ▸ integrable_wedge_of_contDiffAt e₁
      (fun x hx ↦ (hφ x (tsupport_extDeriv_subset hx)).of_le zero_le_one)
      (contDiff_extDeriv hζ le_rfl) hc.extDeriv
  have he₁ : ⇑e ∘ Fin.cast hm₁.symm = ⇑e₁ := (e.reindex_finCongr_comp_cast _ rfl).symm
  have hL (x : E) : wedge (extDeriv φ x) (ζ x) e =
      extDeriv ω x e₀ + wedge (φ x) (extDeriv ζ x) e₁ := by
    by_cases hx : x ∈ tsupport ζ
    · have h := extDeriv_pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        ((hφ x hx).differentiableAt one_ne_zero) (hζ.differentiable one_ne_zero x) e₀
      have c₁ : ⇑e₀ ∘ Fin.cast (by omega : 1 + 1 + n = (1 + n) + 1) = ⇑e := by ext i; simp [e₀]
      have c₂ : ⇑e₀ ∘ Fin.cast (by omega : 1 + (n + 1) = (1 + n) + 1) = ⇑e₁ := by
        ext i; simp [e₀, e₁]
      simp only [← wedge_def, c₁, c₂, pow_one, neg_one_smul] at h
      linarith
    · have h0ω : ω =ᶠ[𝓝 x] 0 := by
        filter_upwards [(isClosed_tsupport ζ).isOpen_compl.mem_nhds hx] with y hy
        simp [ω, image_eq_zero_of_notMem_tsupport hy, wedge_def]
      have hedω : extDeriv ω x = 0 := by
        rw [h0ω.extDeriv_eq, Pi.zero_def, extDeriv, fderiv_const_apply 0,
          ← alternatizeUncurryFinCLM_apply, ContinuousLinearMap.map_zero]
      have hx' : x ∉ tsupport (extDeriv ζ) := fun h ↦ hx (tsupport_extDeriv_subset h)
      simp [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx', hedω,
        wedge_def]
  rw [he₁, integral_congr_ae (Eventually.of_forall hL), integral_add hint₀ hB, hzero₀, zero_add]

omit [FiniteDimensional ℝ E] in
/-- **Localized integration by parts for the cutoff current against a test form.** It suffices that
`α` be `C²` and `b` be `C¹` on `tsupport ζ`, rather than globally on `E`. -/
theorem integral_cutoffCurrent_add_extDeriv_wedge_eq_of_contDiffAt
    (e : Module.Basis (Fin (2 + n)) ℝ E) (hα : ∀ x ∈ tsupport ζ, ContDiffAt ℝ 2 α x)
    (hb : ∀ x ∈ tsupport ζ, ContDiffAt ℝ 1 b x) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hζ : ContDiff ℝ 1 ζ) (hc : HasCompactSupport ζ) :
    ∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar =
      ∫ x, wedge (cutoffPhaseForm χ b α x) (extDeriv ζ x) (e ∘ Fin.cast (by omega)) ∂e.addHaar := by
  have h := integral_extDeriv_wedge_eq_of_contDiffAt e
    (fun x hx ↦ contDiffAt_cutoffPhaseForm (hα x hx) (hb x hx) hχ hχ₀) hζ hc
  simpa only [cutoffCurrent_apply, sub_add_cancel] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem contDiffAt_modulusPotential_normSq {x : E} (hα : ContDiffAt ℝ 2 α x)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) :
    ContDiffAt ℝ 1 (fun y ↦ modulusPotential χ (normSq (α y))) x := by
  have hs : ContDiffAt ℝ 1 (fun y ↦ normSq (α y)) x := by
    simp_rw [normSq_eq_norm_sq]
    exact (contDiff_norm_sq ℝ).contDiffAt.comp x (hα.of_le one_le_two)
  exact (contDiff_modulusPotential hχ.continuous hχ₀).contDiffAt.comp x hs

omit [FiniteDimensional ℝ E] in
private theorem integral_cutoffPhaseForm_wedge_eq_add
    (e₁ : Module.Basis (Fin (1 + (n + 1))) ℝ E) {J : E → E →L[ℝ] E}
    {η : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ}
    (hα : ∀ x ∈ tsupport η, ContDiffAt ℝ 2 α x) (hb : ∀ x ∈ tsupport η, ContDiffAt ℝ 1 b x)
    (hJ : ∀ x ∈ tsupport η, ContDiffAt ℝ 1 J x) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    ∫ x, wedge (cutoffPhaseForm χ b α x) (η x) e₁ ∂e₁.addHaar =
      (∫ x, wedge (twistedDifferentialForm J
          (fun y ↦ modulusPotential χ (normSq (α y))) x) (η x) e₁ ∂e₁.addHaar) +
        ∫ x, wedge (cutoffPhaseForm χ b α x - twistedDifferentialForm J
          (fun y ↦ modulusPotential χ (normSq (α y))) x) (η x) e₁ ∂e₁.addHaar := by
  set g := fun y ↦ modulusPotential χ (normSq (α y))
  have hA : Integrable (fun x ↦ wedge (twistedDifferentialForm J g x) (η x) e₁) e₁.addHaar :=
    integrable_wedge_of_contDiffAt e₁
      (fun x hx ↦ contDiffAt_twistedDifferentialForm
        (contDiffAt_modulusPotential_normSq (hα x hx) hχ hχ₀) ((hJ x hx).of_le zero_le_one)
        (by simp)) (hη.of_le zero_le_one) hcη
  have hT : Integrable (fun x ↦ wedge (cutoffPhaseForm χ b α x) (η x) e₁) e₁.addHaar :=
    integrable_wedge_of_contDiffAt e₁
      (fun x hx ↦ (contDiffAt_cutoffPhaseForm (hα x hx) (hb x hx) hχ hχ₀).of_le zero_le_one)
      (hη.of_le zero_le_one) hcη
  set B := fun x ↦ wedge (cutoffPhaseForm χ b α x - twistedDifferentialForm J g x) (η x) e₁
  have hsplit (x : E) : wedge (cutoffPhaseForm χ b α x) (η x) e₁ =
      wedge (twistedDifferentialForm J g x) (η x) e₁ + B x := by
    have hadd : cutoffPhaseForm χ b α x =
        twistedDifferentialForm J g x +
          (cutoffPhaseForm χ b α x - twistedDifferentialForm J g x) :=
      (add_sub_cancel _ _).symm
    conv_lhs => rw [hadd, wedge_add_left, ContinuousAlternatingMap.add_apply]
  have hB : Integrable B e₁.addHaar :=
    (hT.sub hA).congr (Eventually.of_forall fun x ↦ by
      rw [Pi.sub_apply, hsplit, add_sub_cancel_left])
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hA hB]

private theorem combine_l1_curvature_bounds {C₁ C₂ M A₁ c I₁ I₂ X Y : ℝ} (_ : 0 < c)
    (_ : 0 ≤ M) (_ : 0 ≤ A₁) (_ : 0 ≤ I₁) (_ : 0 ≤ I₂)
    (hX : |X| ≤ C₁ * (M * (I₁ / c))) (hY : |Y| ≤ C₂ * (A₁ * (2 / √c * I₂))) :
    |X + Y| ≤ max C₁ (2 * C₂) * (M / c * I₁ + A₁ / √c * I₂) := by
  refine (abs_add_le _ _).trans ((add_le_add hX hY).trans ?_)
  rw [mul_add]
  refine add_le_add ?_ ?_
  · calc C₁ * (M * (I₁ / c)) = C₁ * (M / c * I₁) := by ring
      _ ≤ max C₁ (2 * C₂) * (M / c * I₁) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc C₂ * (A₁ * (2 / √c * I₂)) = 2 * C₂ * (A₁ / √c * I₂) := by ring
      _ ≤ max C₁ (2 * C₂) * (A₁ / √c * I₂) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

omit [FiniteDimensional ℝ E] in
/-- **Comparison of the cutoff current with the curvature current for a varying `C¹` almost complex
structure.** There is a constant `C ≥ 0`, depending only on the basis `e`, such that whenever `χ`
vanishes below `c > 0` with `|χ| ≤ 1`, `ζ` is a `C²` `n`-form supported in a compact set `K`, `α` is
`C²` on `K`, `b` and `J` are `C¹` on `K`, `J` squares to `-1` on `K` with `‖J‖ ≤ M₀` and
`‖DJ‖ ≤ M₁` on `K`, and `‖dζ‖ ≤ A₁` and `‖D(dζ)‖ ≤ A₂` on `K`,

`|∫ (Θ - i F_a) ∧ ζ| ≤ C * ((M₀^(n+1) A₂ + (n+1) M₀^n M₁ A₁) / c * ∫_K ||α|² - 1| +
  A₁ / √c * ∫_K ‖∂bar_{J, a} α‖)`. -/
theorem exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_of_fderiv_le
    (e : Module.Basis (Fin (2 + n)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃J : E → E →L[ℝ] E⦄ ⦃χ : ℝ → ℝ⦄ ⦃b : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → ℂ⦄
      ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃c M₀ M₁ A₁ A₂ : ℝ⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ →
      (∀ x ∈ K, ContDiffAt ℝ 2 α x) → (∀ x ∈ K, ContDiffAt ℝ 1 b x) →
      ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ x ∈ K, ContDiffAt ℝ 1 J x) → (∀ x ∈ K, ∀ v, J x (J x v) = -v) →
      (∀ x ∈ K, ‖J x‖ ≤ M₀) → (∀ x ∈ K, ‖fderiv ℝ J x‖ ≤ M₁) →
      (∀ x ∈ K, ‖extDeriv ζ x‖ ≤ A₁) → (∀ x ∈ K, ‖fderiv ℝ (extDeriv ζ) x‖ ≤ A₂) →
      |∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar| ≤
        C * ((M₀ ^ (n + 1) * A₂ + (n + 1) * M₀ ^ n * M₁ * A₁) / c *
            (∫ x in K, |normSq (α x) - 1| ∂e.addHaar) +
          A₁ / √c * ∫ x in K, ‖covariantDBarField J b α x‖ ∂e.addHaar) := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis e
  let e₁ := e.reindex (finCongr (by omega : 2 + n = 1 + (n + 1)))
  obtain ⟨C₁, _, hIA⟩ := e₁.exists_abs_integral_twistedDifferentialForm_wedge_le
  obtain ⟨C₂, _, hIB⟩ := e₁.exists_abs_integral_wedge_le
  refine ⟨max C₁ (2 * C₂), by positivity, ?_⟩
  intro J χ b α ζ K c M₀ M₁ A₁ A₂ hc hχc hχ₁ hχ hα hb hζ hK hζK hJ hJsq hJ₀ hJ₁ hA₁ hA₂
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp [image_eq_zero_of_notMem_tsupport fun hx ↦ hζK hx, wedge_def]
  have : 0 ≤ M₀ := (norm_nonneg _).trans (hJ₀ x₀ hx₀)
  have : 0 ≤ M₁ := (ContinuousLinearMap.opNorm_nonneg _).trans (hJ₁ x₀ hx₀)
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ x₀ hx₀)
  have : 0 ≤ A₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hA₂ x₀ hx₀)
  have hχ₀ : χ =ᶠ[𝓝 0] 0 := (eventually_lt_nhds hc).mono hχc
  have hcζ : HasCompactSupport ζ := hK.of_isClosed_subset (isClosed_tsupport ζ) hζK
  set η := extDeriv ζ
  have hη : ContDiff ℝ 1 η := contDiff_extDeriv hζ (by norm_num)
  have hηK : tsupport η ⊆ K := tsupport_extDeriv_subset.trans hζK
  have hη0 (x : E) (hx : x ∉ K) : η x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK h)
  have hA₁_all (x : E) : ‖η x‖ ≤ A₁ := by
    by_cases hx : x ∈ K; exacts [hA₁ x hx, by rw [hη0 x hx, norm_zero]; exact hA₁0]
  have he₁ : ⇑e ∘ Fin.cast (by omega : 1 + (n + 1) = 2 + n) = ⇑e₁ :=
    (e.reindex_finCongr_comp_cast _ rfl).symm
  rw [integral_cutoffCurrent_add_extDeriv_wedge_eq_of_contDiffAt e (fun x hx ↦ hα x (hζK hx))
      (fun x hx ↦ hb x (hζK hx)) hχ hχ₀ (hζ.of_le one_le_two) hcζ, he₁,
    ← e.addHaar_reindex (finCongr (by omega : 2 + n = 1 + (n + 1))),
    integral_cutoffPhaseForm_wedge_eq_add e₁ (fun x hx ↦ hα x (hηK hx))
      (fun x hx ↦ hb x (hηK hx)) (fun x hx ↦ hJ x (hηK hx)) hχ hχ₀ hη hcζ.extDeriv]
  have hint₁ : IntegrableOn (fun x ↦ |normSq (α x) - 1| / c) K e₁.addHaar :=
    ((continuousOn_of_forall_continuousAt fun x hx ↦
      (((continuous_normSq.continuousAt.comp (hα x hx).continuousAt).sub
        continuousAt_const).abs.div_const c)).integrableOn_compact hK)
  have hA' := hIA (fun x hx ↦ contDiffAt_modulusPotential_normSq (hα x hx) hχ hχ₀)
    hη hK hηK hJ hJsq hint₁
    (fun x _ ↦ abs_modulusPotential_le hc (fun t _ ht ↦ hχc t ht) hχ₁ (normSq_nonneg _))
    hJ₀ hJ₁ hA₁ hA₂
  rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, integral_div, e.addHaar_reindex] at hA'
  have hint₂ : IntegrableOn (fun x ↦ 2 / √c * ‖covariantDBarField J b α x‖) K e₁.addHaar :=
    ((continuousOn_of_forall_continuousAt fun x hx ↦ continuousAt_const.mul
      (continuousAt_covariantDBarField (hJ x hx).continuousAt ((hα x hx).of_le one_le_two)
        (hb x hx).continuousAt).norm).integrableOn_compact hK)
  have hB' := hIB hK.measurableSet hη0 hint₂ (fun x hx ↦
    norm_cutoffPhaseForm_sub_twistedDifferentialForm_le hc (fun t _ ht ↦ hχc t ht) hχ₁
      (hasDerivAt_modulusPotential hχ.continuous hχ₀ _) ((hα x hx).differentiableAt two_ne_zero))
    hA₁_all
  rw [integral_const_mul, e.addHaar_reindex] at hB'
  rw [e.addHaar_reindex]
  exact combine_l1_curvature_bounds hc (by positivity) hA₁0
    (setIntegral_nonneg hK.measurableSet fun _ _ ↦ abs_nonneg _)
    (setIntegral_nonneg hK.measurableSet fun _ _ ↦ norm_nonneg _) hA' hB'

omit [FiniteDimensional ℝ E] in
/-- **`L²` comparison of the cutoff current with the curvature current for a varying `C¹` almost
complex structure.** Applying Cauchy–Schwarz on `K` bounds the `∂bar` error term by
`(A₁ / √c) √(μ K) √(∫_K ‖∂bar_{J, a} α‖²)`. -/
theorem exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_sqrt
    (e : Module.Basis (Fin (2 + n)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃J : E → E →L[ℝ] E⦄ ⦃χ : ℝ → ℝ⦄ ⦃b : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → ℂ⦄
      ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃c M₀ M₁ A₁ A₂ : ℝ⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ →
      (∀ x ∈ K, ContDiffAt ℝ 2 α x) → (∀ x ∈ K, ContDiffAt ℝ 1 b x) →
      ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ x ∈ K, ContDiffAt ℝ 1 J x) → (∀ x ∈ K, ∀ v, J x (J x v) = -v) →
      (∀ x ∈ K, ‖J x‖ ≤ M₀) → (∀ x ∈ K, ‖fderiv ℝ J x‖ ≤ M₁) →
      (∀ x ∈ K, ‖extDeriv ζ x‖ ≤ A₁) → (∀ x ∈ K, ‖fderiv ℝ (extDeriv ζ) x‖ ≤ A₂) →
      |∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar| ≤
        C * ((M₀ ^ (n + 1) * A₂ + (n + 1) * M₀ ^ n * M₁ * A₁) / c *
            (∫ x in K, |normSq (α x) - 1| ∂e.addHaar) +
          A₁ / √c * (√(e.addHaar.real K) *
            √(∫ x in K, ‖covariantDBarField J b α x‖ ^ 2 ∂e.addHaar))) := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis e
  obtain ⟨C, hC, hL1⟩ := exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_of_fderiv_le e
  refine ⟨C, hC, ?_⟩
  intro J χ b α ζ K c M₀ M₁ A₁ A₂ hc hχc hχ₁ hχ hα hb hζ hK hζK hJ hJsq hJ₀ hJ₁ hA₁ hA₂
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hζ0 (x : E) : ζ x = 0 := image_eq_zero_of_notMem_tsupport fun hx ↦ hζK hx
    simp [hζ0, wedge_def]
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ x₀ hx₀)
  set f := fun x ↦ ‖covariantDBarField J b α x‖
  have hf_cont : ContinuousOn f K := continuousOn_of_forall_continuousAt fun x hx ↦
    (continuousAt_covariantDBarField (hJ x hx).continuousAt ((hα x hx).of_le one_le_two)
      (hb x hx).continuousAt).norm
  have : IsFiniteMeasure (e.addHaar.restrict K) := isFiniteMeasure_restrict.2 hK.measure_ne_top
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf_cont
  have hf_lp : MemLp f 2 (e.addHaar.restrict K) :=
    MemLp.of_bound (hf_cont.aestronglyMeasurable hK.measurableSet) B
      (ae_restrict_of_forall_mem hK.measurableSet hB)
  have hcs : ∫ x in K, f x ∂e.addHaar ≤
      √(e.addHaar.real K) * √(∫ x in K, f x ^ 2 ∂e.addHaar) :=
    (le_abs_self _).trans
      (abs_setIntegral_le_sqrt_measureReal_mul_sqrt_setIntegral_sq hK.measure_ne_top hf_lp)
  refine (hL1 hc hχc hχ₁ hχ hα hb hζ hK hζK hJ hJsq hJ₀ hJ₁ hA₁ hA₂).trans ?_
  gcongr

end VaryingAlmostComplex

/-! ### Normal-dilated curvature comparison along `E × N` -/

section NormalDilation

private theorem norm_prodMap_id_smul_le {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (a : ℝ) :
    ‖(ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)‖ ≤ max 1 |a| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  have hv : ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)) v =
      (v.1, a • v.2) := rfl
  rw [hv, Prod.norm_def, norm_smul, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · calc ‖v.1‖ = 1 * ‖v.1‖ := (one_mul _).symm
      _ ≤ max 1 |a| * ‖v‖ := mul_le_mul (le_max_left _ _) (norm_fst_le v) (norm_nonneg _)
          (by positivity)
  · exact mul_le_mul (le_max_right _ _) (norm_snd_le v) (norm_nonneg _) (by positivity)

/-- **Pullback of the cutoff current under normal dilation.** Pulling `(b, α)` back along
`δ_a(p) = (p.1, a • p.2)` pulls `cutoffCurrent χ b α` back as a two-form. -/
theorem cutoffCurrent_normalDilation {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup N] [NormedSpace ℝ N] {χ : ℝ → ℝ}
    {b : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ} {α : F × N → ℂ} {a : ℝ} {p : F × N}
    (hα : ContDiffAt ℝ 2 α (p.1, a • p.2)) (hb : ContDiffAt ℝ 1 b (p.1, a • p.2))
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) :
    cutoffCurrent χ
        (fun q : F × N ↦ (b (q.1, a • q.2)).compContinuousLinearMap
          ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)))
        (fun q : F × N ↦ α (q.1, a • q.2)) p =
      (cutoffCurrent χ b α (p.1, a • p.2)).compContinuousLinearMap
        ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)) := by
  let S : (F × N) →L[ℝ] F × N :=
    (ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)
  have hαS : ContDiffAt ℝ 2 α (S p) := hα
  have hbS : ContDiffAt ℝ 1 b (S p) := hb
  have h := cutoffCurrent_comp (f := ⇑S) (y := p) hαS hbS hχ hχ₀ S.contDiff.contDiffAt
  simp only [S.fderiv] at h
  exact h

/-- **Pullback of `Θ - i F_a = Θ + db` under normal dilation.** -/
theorem cutoffCurrent_add_extDeriv_normalDilation {F N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N] {χ : ℝ → ℝ}
    {b : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ} {α : F × N → ℂ} {a : ℝ} {p : F × N}
    (hα : ContDiffAt ℝ 2 α (p.1, a • p.2)) (hb : ContDiffAt ℝ 1 b (p.1, a • p.2))
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) :
    cutoffCurrent χ
        (fun q : F × N ↦ (b (q.1, a • q.2)).compContinuousLinearMap
          ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)))
        (fun q : F × N ↦ α (q.1, a • q.2)) p +
      extDeriv (fun q : F × N ↦ (b (q.1, a • q.2)).compContinuousLinearMap
          ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N))) p =
      (cutoffCurrent χ b α (p.1, a • p.2) + extDeriv b (p.1, a • p.2)).compContinuousLinearMap
        ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)) := by
  let S : (F × N) →L[ℝ] F × N :=
    (ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)
  have hbS : DifferentiableAt ℝ b (S p) := hb.differentiableAt one_ne_zero
  have hdb : extDeriv (fun q : F × N ↦ (b (q.1, a • q.2)).compContinuousLinearMap S) p =
      (extDeriv b (p.1, a • p.2)).compContinuousLinearMap S :=
    S.extDeriv_pullback hbS
  rw [cutoffCurrent_normalDilation hα hb hχ hχ₀]
  dsimp only [S] at hdb
  rw [hdb]
  ext v
  simp

/-- **Intertwining of `∂bar` under normal dilation.** For `a ≠ 0`, the `(0, 1)`-covariant derivative
of `(δ_a^* b, α ∘ δ_a)` with respect to `δ_a^* J` at `p` is `∂bar_{J, a} α (p.1, a • p.2)`
precomposed with `(v, w) ↦ (v, a • w)`. -/
theorem covariantDBarField_normalDilation {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (J : F × N → F × N →L[ℝ] F × N)
    {b : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ} {α : F × N → ℂ} {a : ℝ} (ha : a ≠ 0) {p : F × N}
    (hα : DifferentiableAt ℝ α (p.1, a • p.2)) :
    covariantDBarField (normalDilation J a)
        (fun q : F × N ↦ (b (q.1, a • q.2)).compContinuousLinearMap
          ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)))
        (fun q : F × N ↦ α (q.1, a • q.2)) p =
      (covariantDBarField J b α (p.1, a • p.2)).comp
        ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)) := by
  let S : (F × N) →L[ℝ] F × N :=
    (ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)
  have hαS : DifferentiableAt ℝ α (S p) := hα
  have hJ : (fderiv ℝ (⇑S) p).comp (normalDilation J a p) = (J (S p)).comp (fderiv ℝ (⇑S) p) := by
    rw [S.fderiv]
    exact prodMap_comp_normalDilation J ha p
  have h := covariantDBarField_comp_of_comp_eq (b := b) hαS S.differentiableAt hJ
  simp only [S.fderiv] at h
  exact h

/-- **Pointwise operator-norm bound on `∂bar` under normal dilation.** For `a ≠ 0`,
`‖∂bar_{δ_a^* J, δ_a^* a}(α ∘ δ_a)(p)‖ ≤ max 1 |a| ‖∂bar_{J, a} α (p.1, a • p.2)‖`. In particular,
when `|a| ≤ 1` the operator norm does not grow under normal dilation. -/
theorem norm_covariantDBarField_normalDilation_le {F N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N] (J : F × N → F × N →L[ℝ] F × N)
    {b : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ} {α : F × N → ℂ} {a : ℝ} (ha : a ≠ 0) {p : F × N}
    (hα : DifferentiableAt ℝ α (p.1, a • p.2)) :
    ‖covariantDBarField (normalDilation J a)
        (fun q : F × N ↦ (b (q.1, a • q.2)).compContinuousLinearMap
          ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)))
        (fun q : F × N ↦ α (q.1, a • q.2)) p‖ ≤
      max 1 |a| * ‖covariantDBarField J b α (p.1, a • p.2)‖ := by
  rw [covariantDBarField_normalDilation J ha hα, mul_comm]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_prodMap_id_smul_le a) (ContinuousLinearMap.opNorm_nonneg _))

private theorem sqrt_setIntegral_covariantDBarField_normalDilation_sq_le {F N : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    [MeasurableSpace N] [BorelSpace N] (μ : Measure (F × N)) [μ.IsAddHaarMeasure]
    {J : F × N → F × N →L[ℝ] F × N} {b : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ}
    {α : F × N → ℂ} {K : Set (F × N)} {a : ℝ} (ha : a ≠ 0) (ha₁ : |a| ≤ 1) (hK : IsCompact K)
    (hα : ∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ContDiffAt ℝ 2 α q)
    (hb : ∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ContDiffAt ℝ 1 b q)
    (hJ : ∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ContDiffAt ℝ 1 J q) :
    √(∫ p in K, ‖covariantDBarField (normalDilation J a)
        (fun q ↦ (b (q.1, a • q.2)).compContinuousLinearMap
          ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)))
        (fun q ↦ α (q.1, a • q.2)) p‖ ^ 2 ∂μ) ≤
      √((∫ q in (fun p : F × N ↦ (p.1, a • p.2)) '' K,
          ‖covariantDBarField J b α q‖ ^ 2 ∂μ) / |a| ^ Module.finrank ℝ N) := by
  let S : (F × N) →L[ℝ] F × N :=
    (ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)
  set b_a : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ :=
    fun q ↦ (b (q.1, a • q.2)).compContinuousLinearMap S
  have hb_a (p : F × N) (hp : p ∈ K) : ContDiffAt ℝ 1 b_a p :=
    (compContinuousLinearMapCLM S).contDiff.contDiffAt.comp p
      ((hb _ (mem_image_of_mem _ hp)).comp p S.contDiff.contDiffAt)
  have hint_lhs : IntegrableOn
      (fun p ↦ ‖covariantDBarField (normalDilation J a) b_a (fun q ↦ α (q.1, a • q.2)) p‖ ^ 2)
      K μ :=
    (continuousOn_of_forall_continuousAt fun p hp ↦
      ((continuousAt_covariantDBarField
        (contDiffAt_normalDilation (hJ _ (mem_image_of_mem _ hp))).continuousAt
        (((hα _ (mem_image_of_mem _ hp)).comp p S.contDiff.contDiffAt).of_le one_le_two)
        (hb_a p hp).continuousAt).norm.pow 2)).integrableOn_compact hK
  have hint_rhs : IntegrableOn
      (fun p : F × N ↦ ‖covariantDBarField J b α (p.1, a • p.2)‖ ^ 2) K μ :=
    (continuousOn_of_forall_continuousAt fun p hp ↦
      (((continuousAt_covariantDBarField (hJ _ (mem_image_of_mem _ hp)).continuousAt
        ((hα _ (mem_image_of_mem _ hp)).of_le one_le_two)
        (hb _ (mem_image_of_mem _ hp)).continuousAt).comp_of_eq
        (S.continuous.continuousAt (x := p)) rfl).norm.pow 2)).integrableOn_compact hK
  refine Real.sqrt_le_sqrt ?_
  calc ∫ p in K, ‖covariantDBarField (normalDilation J a) b_a
          (fun q ↦ α (q.1, a • q.2)) p‖ ^ 2 ∂μ
      ≤ ∫ p in K, ‖covariantDBarField J b α (p.1, a • p.2)‖ ^ 2 ∂μ := by
        refine setIntegral_mono_on hint_lhs hint_rhs hK.measurableSet fun p hp ↦ ?_
        have hn := norm_covariantDBarField_normalDilation_le J ha
          ((hα _ (mem_image_of_mem _ hp)).differentiableAt two_ne_zero) (b := b)
        rw [max_eq_left ha₁, one_mul] at hn
        exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by
        rw [Measure.setIntegral_comp_prod_smul_right μ ha
          (fun q ↦ ‖covariantDBarField J b α q‖ ^ 2) K, smul_eq_mul, inv_mul_eq_div]

private theorem combine_normalDilation_bounds {C₀ M₀ M₁ A₁ A₂ c sK R₁ Q R₂ : ℝ} (_ : 0 ≤ C₀)
    (_ : 0 < c) (_ : 0 ≤ sK) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (_ : 0 ≤ R₁) (_ : 0 ≤ R₂)
    (hQ : Q ≤ R₂) :
    C₀ * ((M₀ ^ (n + 1) * A₂ + (n + 1) * M₀ ^ n * M₁ * A₁) / c * R₁ + A₁ / √c * (sK * Q)) ≤
      (C₀ * max (max (M₀ ^ (n + 1) / c) ((n + 1) * M₀ ^ n * M₁ / c)) (sK / √c)) *
        ((A₁ + A₂) * R₁ + A₁ * R₂) := by
  set K₁ := max (M₀ ^ (n + 1) / c) ((n + 1) * M₀ ^ n * M₁ / c)
  set K₂ := sK / √c
  have hcoef₁ : (M₀ ^ (n + 1) * A₂ + (n + 1) * M₀ ^ n * M₁ * A₁) / c ≤ K₁ * (A₁ + A₂) :=
    calc (M₀ ^ (n + 1) * A₂ + (n + 1) * M₀ ^ n * M₁ * A₁) / c
        = (M₀ ^ (n + 1) / c) * A₂ + ((n + 1) * M₀ ^ n * M₁ / c) * A₁ := by ring
      _ ≤ K₁ * A₂ + K₁ * A₁ := add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hA₂)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hA₁)
      _ = K₁ * (A₁ + A₂) := by ring
  calc C₀ * ((M₀ ^ (n + 1) * A₂ + (n + 1) * M₀ ^ n * M₁ * A₁) / c * R₁ + A₁ / √c * (sK * Q))
      ≤ C₀ * (K₁ * (A₁ + A₂) * R₁ + A₁ / √c * (sK * R₂)) := by gcongr
    _ = C₀ * (K₁ * ((A₁ + A₂) * R₁) + K₂ * (A₁ * R₂)) := by simp only [K₂]; ring
    _ ≤ C₀ * (max K₁ K₂ * ((A₁ + A₂) * R₁) + max K₁ K₂ * (A₁ * R₂)) := by
          gcongr; exacts [le_max_left _ _, le_max_right _ _]
    _ = (C₀ * max K₁ K₂) * ((A₁ + A₂) * R₁ + A₁ * R₂) := by ring

private theorem abs_integral_normalDilation_wedge_le_aux {F N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] [MeasurableSpace N]
    [BorelSpace N] (e : Module.Basis (Fin (2 + n)) ℝ (F × N)) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hL2 : ∀ ⦃J' : F × N → F × N →L[ℝ] F × N⦄ ⦃χ : ℝ → ℝ⦄
      ⦃b' : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α' : F × N → ℂ⦄
      ⦃ζ : F × N → (F × N) [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set (F × N)⦄ ⦃c M₀ M₁ A₁ A₂ : ℝ⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ →
      (∀ p ∈ K, ContDiffAt ℝ 2 α' p) → (∀ p ∈ K, ContDiffAt ℝ 1 b' p) →
      ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ p ∈ K, ContDiffAt ℝ 1 J' p) → (∀ p ∈ K, ∀ v, J' p (J' p v) = -v) →
      (∀ p ∈ K, ‖J' p‖ ≤ M₀) → (∀ p ∈ K, ‖fderiv ℝ J' p‖ ≤ M₁) →
      (∀ p ∈ K, ‖extDeriv ζ p‖ ≤ A₁) → (∀ p ∈ K, ‖fderiv ℝ (extDeriv ζ) p‖ ≤ A₂) →
      |∫ p, wedge (cutoffCurrent χ b' α' p + extDeriv b' p) (ζ p) e ∂e.addHaar| ≤
        C₀ * ((M₀ ^ (n + 1) * A₂ + (n + 1) * M₀ ^ n * M₁ * A₁) / c *
            (∫ p in K, |normSq (α' p) - 1| ∂e.addHaar) +
          A₁ / √c * (√(e.addHaar.real K) *
            √(∫ p in K, ‖covariantDBarField J' b' α' p‖ ^ 2 ∂e.addHaar))))
    {J : F × N → F × N →L[ℝ] F × N} {χ : ℝ → ℝ} {b : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ}
    {α : F × N → ℂ} {ζ : F × N → (F × N) [⋀^Fin n]→L[ℝ] ℝ} {K : Set (F × N)}
    {a c M₀ M₁ A₁ A₂ : ℝ} (ha : a ≠ 0) (ha₁ : |a| ≤ 1) (hc : 0 < c) (hχc : ∀ t < c, χ t = 0)
    (hχ₁ : ∀ t, |χ t| ≤ 1) (hχ : ContDiff ℝ 1 χ)
    (hα : ∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ContDiffAt ℝ 2 α q)
    (hb : ∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ContDiffAt ℝ 1 b q)
    (hJ : ∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ContDiffAt ℝ 1 J q)
    (hJsq : ∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ∀ v, J q (J q v) = -v)
    (hJa₀ : ∀ p ∈ K, ‖normalDilation J a p‖ ≤ M₀)
    (hJa₁ : ∀ p ∈ K, ‖fderiv ℝ (normalDilation J a) p‖ ≤ M₁)
    (hζ : ContDiff ℝ 2 ζ) (hK : IsCompact K) (hζK : tsupport ζ ⊆ K)
    (hA₁ : ∀ p ∈ K, ‖extDeriv ζ p‖ ≤ A₁) (hA₂ : ∀ p ∈ K, ‖fderiv ℝ (extDeriv ζ) p‖ ≤ A₂) :
    |∫ p, wedge
        ((cutoffCurrent χ b α (p.1, a • p.2) +
            extDeriv b (p.1, a • p.2)).compContinuousLinearMap
          ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)))
        (ζ p) e ∂e.addHaar| ≤
      (C₀ * max (max (M₀ ^ (n + 1) / c) ((n + 1) * M₀ ^ n * M₁ / c))
          (√(e.addHaar.real K) / √c)) *
        ((A₁ + A₂) *
            ((∫ q in (fun p : F × N ↦ (p.1, a • p.2)) '' K, |normSq (α q) - 1| ∂e.addHaar) /
              |a| ^ Module.finrank ℝ N) +
          A₁ * √((∫ q in (fun p : F × N ↦ (p.1, a • p.2)) '' K,
              ‖covariantDBarField J b α q‖ ^ 2 ∂e.addHaar) / |a| ^ Module.finrank ℝ N)) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · have hζ0 (p : F × N) : ζ p = 0 := image_eq_zero_of_notMem_tsupport fun hp ↦ hζK hp
    simp [hζ0, wedge_def]
  let S : (F × N) →L[ℝ] F × N :=
    (ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)
  set b_a : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ :=
    fun q ↦ (b (q.1, a • q.2)).compContinuousLinearMap S
  set α_a : F × N → ℂ := fun q ↦ α (q.1, a • q.2)
  have hχ₀ : χ =ᶠ[𝓝 0] 0 := (eventually_lt_nhds hc).mono hχc
  have hlhs : (∫ p, wedge ((cutoffCurrent χ b α (p.1, a • p.2) +
      extDeriv b (p.1, a • p.2)).compContinuousLinearMap S) (ζ p) e ∂e.addHaar) =
        ∫ p, wedge (cutoffCurrent χ b_a α_a p + extDeriv b_a p) (ζ p) e ∂e.addHaar := by
    refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
    by_cases hp : p ∈ tsupport ζ
    · have hpS : (p.1, a • p.2) ∈ (fun q : F × N ↦ (q.1, a • q.2)) '' K :=
        mem_image_of_mem _ (hζK hp)
      dsimp only
      rw [← cutoffCurrent_add_extDeriv_normalDilation (hα _ hpS) (hb _ hpS) hχ hχ₀]
    · simp [image_eq_zero_of_notMem_tsupport hp, wedge_def]
  have hb_a (p : F × N) (hp : p ∈ K) : ContDiffAt ℝ 1 b_a p :=
    (compContinuousLinearMapCLM S).contDiff.contDiffAt.comp p
      ((hb _ (mem_image_of_mem _ hp)).comp p S.contDiff.contDiffAt)
  have hmain := hL2 (α' := α_a) hc hχc hχ₁ hχ
    (fun p hp ↦ (hα _ (mem_image_of_mem _ hp)).comp p S.contDiff.contDiffAt) hb_a hζ hK hζK
    (fun p hp ↦ contDiffAt_normalDilation (hJ _ (mem_image_of_mem _ hp)))
    (fun p hp ↦ normalDilation_apply_normalDilation_apply ha (hJsq _ (mem_image_of_mem _ hp)))
    hJa₀ hJa₁ hA₁ hA₂
  rw [hlhs]
  refine hmain.trans ?_
  rw [Measure.setIntegral_comp_prod_smul_right e.addHaar ha (fun q ↦ |normSq (α q) - 1|) K,
    smul_eq_mul, inv_mul_eq_div]
  exact combine_normalDilation_bounds hC₀ hc (Real.sqrt_nonneg _)
    ((norm_nonneg _).trans (hA₁ p₀ hp₀)) ((ContinuousLinearMap.opNorm_nonneg _).trans (hA₂ p₀ hp₀))
    (div_nonneg (setIntegral_nonneg (hK.image S.continuous).measurableSet fun _ _ ↦ abs_nonneg _)
      (by positivity))
    (Real.sqrt_nonneg _)
    (sqrt_setIntegral_covariantDBarField_normalDilation_sq_le e.addHaar ha ha₁ hK hα hb hJ)

/-- **Uniform normal-dilated curvature comparison on a compact set.** Let `J` be `C²` and square to
`-1` on an open set `Ω ⊆ F × N`, let the zero section `F × {0}` be `J`-holomorphic where it meets
`Ω`, let `χ` be a `C¹` cutoff vanishing below `c > 0` with `|χ| ≤ 1`, and let `K ⊆ F × N` be
compact with `(p.1, 0) ∈ Ω` for all `p ∈ K`. Then there is a scale-independent constant `C ≥ 0`
such that for all sufficiently small `a ≠ 0` and all pairs `(b, α)` smooth on `δ_a(K)` and `C²`
test `n`-forms `ζ` supported in `K` with `‖dζ‖ ≤ A₁` and `‖D(dζ)‖ ≤ A₂` on `K`, the pairing of
`δ_a^* (Θ - i F_a)` with `ζ` is bounded by `C` times
`(A₁ + A₂) |a|^(-finrank N) ∫_{δ_a(K)} ||α|² - 1| + A₁ √(|a|^(-finrank N) ∫_{δ_a(K)} ‖∂bar α‖²)`. -/
theorem exists_eventually_abs_integral_cutoffCurrent_add_extDeriv_normalDilation_wedge_le
    {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] [MeasurableSpace N] [BorelSpace N]
    (e : Module.Basis (Fin (2 + n)) ℝ (F × N)) {Ω K : Set (F × N)}
    {J : F × N → F × N →L[ℝ] F × N} {c : ℝ} (hΩ : IsOpen Ω) (hJ : ContDiffOn ℝ 2 J Ω)
    (hJsq : ∀ q ∈ Ω, ∀ v, J q (J q v) = -v)
    (hJ₀ : ∀ z, (z, 0) ∈ Ω → ∀ v, (J (z, 0) (v, 0)).2 = 0)
    (hc : 0 < c) (hχc : ∀ t < c, χ t = 0) (hχ₁ : ∀ t, |χ t| ≤ 1) (hχ : ContDiff ℝ 1 χ)
    (hK : IsCompact K) (hKΩ : ∀ p ∈ K, (p.1, 0) ∈ Ω) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ a : ℝ in 𝓝[≠] 0,
      ∀ ⦃b : F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : F × N → ℂ⦄
        ⦃ζ : F × N → (F × N) [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃A₁ A₂ : ℝ⦄,
        (∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ContDiffAt ℝ 2 α q) →
        (∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ContDiffAt ℝ 1 b q) →
        ContDiff ℝ 2 ζ → tsupport ζ ⊆ K →
        (∀ p ∈ K, ‖extDeriv ζ p‖ ≤ A₁) → (∀ p ∈ K, ‖fderiv ℝ (extDeriv ζ) p‖ ≤ A₂) →
        |∫ p, wedge
            ((cutoffCurrent χ b α (p.1, a • p.2) +
                extDeriv b (p.1, a • p.2)).compContinuousLinearMap
              ((ContinuousLinearMap.id ℝ F).prodMap (a • ContinuousLinearMap.id ℝ N)))
            (ζ p) e ∂e.addHaar| ≤
          C * ((A₁ + A₂) *
              ((∫ q in (fun p : F × N ↦ (p.1, a • p.2)) '' K, |normSq (α q) - 1| ∂e.addHaar) /
                |a| ^ Module.finrank ℝ N) +
            A₁ * √((∫ q in (fun p : F × N ↦ (p.1, a • p.2)) '' K,
                ‖covariantDBarField J b α q‖ ^ 2 ∂e.addHaar) / |a| ^ Module.finrank ℝ N)) := by
  obtain ⟨C₀, hC₀, hL2⟩ := exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le_sqrt e
  obtain ⟨M₀, M₁, _, _, hev⟩ :=
    exists_eventually_norm_normalDilation_le_of_isOpen hΩ hJ hJ₀ hK hKΩ
  refine ⟨C₀ * max (max (M₀ ^ (n + 1) / c) ((n + 1) * M₀ ^ n * M₁ / c))
    (√(e.addHaar.real K) / √c), by positivity, ?_⟩
  have ha_le : ∀ᶠ a : ℝ in 𝓝[≠] 0, |a| ≤ 1 :=
    nhdsWithin_le_nhds (continuous_abs.continuousAt.eventually
      (Iic_mem_nhds (by norm_num : |(0 : ℝ)| < 1)))
  filter_upwards [self_mem_nhdsWithin, ha_le, hev] with a ha ha₁ ⟨haΩ, hJa₀, hJa₁⟩
  intro b α ζ A₁ A₂ hα hb hζ hζK hA₁ hA₂
  have hJ_img : ∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ContDiffAt ℝ 1 J q := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hJ.of_le one_le_two).contDiffAt (hΩ.mem_nhds (haΩ p hp))
  have hJsq_img : ∀ q ∈ (fun p : F × N ↦ (p.1, a • p.2)) '' K, ∀ v, J q (J q v) = -v := by
    rintro _ ⟨p, hp, rfl⟩
    exact hJsq _ (haΩ p hp)
  exact abs_integral_normalDilation_wedge_le_aux e hC₀ hL2 ha ha₁ hc hχc hχ₁ hχ hα hb
    hJ_img hJsq_img hJa₀ hJa₁ hζ hK hζK hA₁ hA₂

/-- **Weak-limit equivalence of the normal-dilated cutoff and curvature currents.** Along any
family of scales `a i → 0` (`a i ≠ 0`) for which `|a i|^(-finrank N) ∫_{δ_{a i}(K)} ||α i|² - 1|`
and `|a i|^(-finrank N) ∫_{δ_{a i}(K)} ‖∂bar_{J, b i} (α i)‖²` both tend to `0` (in codimension
`finrank N = 2`, whenever both unrescaled integrals on `δ_{a i}(K)` are `O(h_i²)` with
`h_i / a_i → 0`), the pairing of `δ_{a i}^* (Θ_i - i F_{a_i})` with any fixed `C²` test form `ζ`
supported in `K` tends to `0`. -/
theorem tendsto_integral_cutoffCurrent_add_extDeriv_normalDilation_wedge_zero
    {ι F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] [MeasurableSpace N] [BorelSpace N] {l : Filter ι}
    (e : Module.Basis (Fin (2 + n)) ℝ (F × N)) {Ω K : Set (F × N)}
    {J : F × N → F × N →L[ℝ] F × N} {c : ℝ} {a : ι → ℝ}
    {b : ι → F × N → (F × N) [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → F × N → ℂ}
    {ζ : F × N → (F × N) [⋀^Fin n]→L[ℝ] ℝ}
    (hΩ : IsOpen Ω) (hJ : ContDiffOn ℝ 2 J Ω) (hJsq : ∀ q ∈ Ω, ∀ v, J q (J q v) = -v)
    (hJ₀ : ∀ z, (z, 0) ∈ Ω → ∀ v, (J (z, 0) (v, 0)).2 = 0)
    (hc : 0 < c) (hχc : ∀ t < c, χ t = 0) (hχ₁ : ∀ t, |χ t| ≤ 1) (hχ : ContDiff ℝ 1 χ)
    (hK : IsCompact K) (hKΩ : ∀ p ∈ K, (p.1, 0) ∈ Ω) (hζ : ContDiff ℝ 2 ζ) (hζK : tsupport ζ ⊆ K)
    (ha : Tendsto a l (𝓝[≠] 0))
    (hα : ∀ᶠ i in l, ∀ q ∈ (fun p : F × N ↦ (p.1, a i • p.2)) '' K, ContDiffAt ℝ 2 (α i) q)
    (hb : ∀ᶠ i in l, ∀ q ∈ (fun p : F × N ↦ (p.1, a i • p.2)) '' K, ContDiffAt ℝ 1 (b i) q)
    (hI₁ : Tendsto (fun i ↦
        (∫ q in (fun p : F × N ↦ (p.1, a i • p.2)) '' K, |normSq (α i q) - 1| ∂e.addHaar) /
          |a i| ^ Module.finrank ℝ N) l (𝓝 0))
    (hI₂ : Tendsto (fun i ↦
        (∫ q in (fun p : F × N ↦ (p.1, a i • p.2)) '' K,
          ‖covariantDBarField J (b i) (α i) q‖ ^ 2 ∂e.addHaar) /
          |a i| ^ Module.finrank ℝ N) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ p, wedge
        ((cutoffCurrent χ (b i) (α i) (p.1, a i • p.2) +
            extDeriv (b i) (p.1, a i • p.2)).compContinuousLinearMap
          ((ContinuousLinearMap.id ℝ F).prodMap (a i • ContinuousLinearMap.id ℝ N)))
        (ζ p) e ∂e.addHaar) l (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ :=
    exists_eventually_abs_integral_cutoffCurrent_add_extDeriv_normalDilation_wedge_le e hΩ hJ hJsq
      hJ₀ hc hχc hχ₁ hχ hK hKΩ
  have hη : ContDiff ℝ 1 (extDeriv ζ) := contDiff_extDeriv hζ (by norm_num)
  obtain ⟨A₁, hA₁⟩ := hK.exists_bound_of_continuousOn hη.continuous.continuousOn
  obtain ⟨A₂, hA₂⟩ := hK.exists_bound_of_continuousOn
    (hη.fderiv_right (m := 0) (by norm_num)).continuous.continuousOn
  have htend : Tendsto (fun i ↦ C * ((A₁ + A₂) *
      ((∫ q in (fun p : F × N ↦ (p.1, a i • p.2)) '' K, |normSq (α i q) - 1| ∂e.addHaar) /
        |a i| ^ Module.finrank ℝ N) +
      A₁ * √((∫ q in (fun p : F × N ↦ (p.1, a i • p.2)) '' K,
        ‖covariantDBarField J (b i) (α i) q‖ ^ 2 ∂e.addHaar) /
          |a i| ^ Module.finrank ℝ N))) l (𝓝 0) := by
    have h0 : C * ((A₁ + A₂) * 0 + A₁ * √0) = 0 := by simp
    rw [← h0]
    exact ((hI₁.const_mul (A₁ + A₂)).add
      ((Real.continuous_sqrt.continuousAt.tendsto.comp hI₂).const_mul A₁)).const_mul C
  refine squeeze_zero_norm' ?_ htend
  filter_upwards [ha.eventually hbound, hα, hb] with i hi hαi hbi
  rw [Real.norm_eq_abs]
  exact hi hαi hbi hζ hζK hA₁ hA₂

end NormalDilation

end TauCeti.SeibergWitten
