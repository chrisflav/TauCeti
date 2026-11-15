/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.HarmonicMajorant
import TauCeti.Analysis.Complex.PowerSeries.Parseval

/-!
# The analytic unit-disk Hardy space and its isometric equivalence with boundary Hardy space

This file constructs the classical analytic Hardy space `H²(𝔻)` (`TauCeti.DiskHardySpace`) directly
on the open unit disk `Metric.ball (0 : ℂ) 1` and identifies it isometrically with the boundary
Hardy space `TauCeti.HardySpace` on `UnitAddCircle`.

An element `F : DiskHardySpace` is a function `Metric.ball (0 : ℂ) 1 → ℂ` that extends
holomorphically to `Metric.ball (0 : ℂ) 1` and whose squared modulus `z ↦ ‖F z‖ ^ 2` admits a real
harmonic majorant on `Metric.ball (0 : ℂ) 1`. Storing values only on `Metric.ball (0 : ℂ) 1` makes
elements extensional on the disk without exterior junk data and avoids any topology conflict with
compact-open convergence on `holomorphicFunctions`.

The norm on `DiskHardySpace` is defined **intrinsically** from the harmonic-majorant condition:
`‖F‖ = √(sInf ((fun u : ℂ → ℝ ↦ u 0) '' {u | F.IsHarmonicMajorant u}))`.
Using Parseval's identity on concentric interior circles
(`TauCeti.hasSum_norm_sq_taylorCoeff_mul_pow`) and the Poisson least-harmonic-majorant theorem
(`TauCeti.HardySpace.harmonicMajorant_le_of_harmonicOnNhd`), we construct the Taylor/radial
boundary-value map `DiskHardySpace.boundaryValue`, prove that
`HardySpace.diskHardyEquiv : HardySpace ≃ₗᵢ[ℂ] DiskHardySpace` is a complex-linear isometric
equivalence, endow `DiskHardySpace` with its Hilbert-space structure, and equate `‖F‖ ^ 2` with
both the value at `0` of the pointwise least harmonic majorant `F.leastHarmonicMajorant` and the
supremum of interior squared circle means `Real.circleAverage (fun w ↦ ‖F.extend w‖ ^ 2) 0 r` over
`r ∈ [0, 1)`.

## Main declarations

* `TauCeti.DiskHardySpace`: holomorphic functions on `Metric.ball (0 : ℂ) 1` whose squared modulus
  admits a real harmonic majorant.
* `TauCeti.DiskHardySpace.IsHarmonicMajorant`, `TauCeti.DiskHardySpace.extend`,
  `TauCeti.DiskHardySpace.of`: harmonic-majorant predicate, zero extension to `ℂ`, and ambient
  constructor.
* `Norm DiskHardySpace`, `NormedAddCommGroup DiskHardySpace`,
  `InnerProductSpace ℂ DiskHardySpace`, `CompleteSpace DiskHardySpace`: the intrinsic
  harmonic-majorant norm and resulting complex Hilbert-space structure.
* `TauCeti.DiskHardySpace.boundaryValue` and `TauCeti.HardySpace.diskHardyEquiv`: boundary `H²`
  recovery and the linear isometric equivalence `HardySpace ≃ₗᵢ[ℂ] DiskHardySpace`.
* `TauCeti.DiskHardySpace.leastHarmonicMajorant`,
  `TauCeti.DiskHardySpace.leastHarmonicMajorant_le`,
  `TauCeti.DiskHardySpace.norm_sq_eq_sInf`,
  `TauCeti.DiskHardySpace.leastHarmonicMajorant_zero`,
  `TauCeti.DiskHardySpace.norm_sq_eq_sSup_circleAverage`: pointwise least harmonic majorant and
  three-way characterization of the squared Hardy norm.
* `TauCeti.DiskHardySpace.tendsto_eLpNorm_extend_sub_boundaryValue` and
  `TauCeti.DiskHardySpace.eq_coe_boundaryValue_of_tendsto_eLpNorm`: radial `L²` convergence to and
  uniqueness of the boundary value.

## References

* P. L. Duren, *Theory of Hᵖ Spaces*, Academic Press (1970), Chapter 1 and §2.6.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), §§17.6–17.11.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990).
-/

public section

noncomputable section

open Complex Filter InnerProductSpace MeasureTheory Metric Nat Set Topology
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- The analytic Hardy space `H²(𝔻)` on the open unit disk `Metric.ball (0 : ℂ) 1`: complex-valued
functions on `Metric.ball (0 : ℂ) 1` that admit a holomorphic ambient representative on the disk
and a real harmonic majorant of their squared modulus. -/
structure DiskHardySpace where
  /-- The underlying function on the open unit disk. -/
  toFun : ball (0 : ℂ) 1 → ℂ
  /-- Existence of an ambient holomorphic representative on `ball (0 : ℂ) 1`. -/
  exists_differentiableOn' :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball (0 : ℂ) 1) ∧ ∀ z : ball (0 : ℂ) 1, g z = toFun z
  /-- Existence of a real harmonic majorant of `z ↦ ‖toFun z‖ ^ 2` on `ball (0 : ℂ) 1`. -/
  exists_harmonicMajorant' :
    ∃ u : ℂ → ℝ, HarmonicOnNhd u (ball (0 : ℂ) 1) ∧ ∀ z : ball (0 : ℂ) 1, ‖toFun z‖ ^ 2 ≤ u z

namespace DiskHardySpace

instance : FunLike DiskHardySpace (ball (0 : ℂ) 1) ℂ where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[simp]
theorem coe_mk (f : ball (0 : ℂ) 1 → ℂ) (hd hm) : (mk f hd hm : ball (0 : ℂ) 1 → ℂ) = f :=
  (rfl)

@[ext]
theorem ext {F G : DiskHardySpace} (h : ∀ z : ball (0 : ℂ) 1, F z = G z) : F = G :=
  DFunLike.ext F G h

/-- Canonical ambient representative of `F : DiskHardySpace` on `ℂ`, obtained by extending by `0`
outside `Metric.ball (0 : ℂ) 1`. -/
def extend (F : DiskHardySpace) : ℂ → ℂ :=
  Function.extend Subtype.val (F : ball (0 : ℂ) 1 → ℂ) (fun _ ↦ 0)

@[simp]
theorem extend_coe (F : DiskHardySpace) (z : ball (0 : ℂ) 1) : F.extend z = F z :=
  Subtype.val_injective.extend_apply _ _ z

theorem extend_apply_of_mem (F : DiskHardySpace) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    F.extend w = F ⟨w, hw⟩ :=
  F.extend_coe ⟨w, hw⟩

@[simp]
theorem extend_apply_of_notMem (F : DiskHardySpace) {w : ℂ} (hw : w ∉ ball (0 : ℂ) 1) :
    F.extend w = 0 := by
  rw [extend, Function.extend_apply']
  rintro ⟨z, rfl⟩
  exact hw z.2

/-- The zero extension of `F : DiskHardySpace` is holomorphic on `Metric.ball (0 : ℂ) 1`. -/
theorem differentiableOn_extend (F : DiskHardySpace) :
    DifferentiableOn ℂ F.extend (ball (0 : ℂ) 1) := by
  obtain ⟨g, hg, hgf⟩ := F.exists_differentiableOn'
  exact hg.congr fun w hw ↦ (F.extend_apply_of_mem hw).trans (hgf ⟨w, hw⟩).symm

/-- The zero extension of `F : DiskHardySpace` is complex analytic on `Metric.ball (0 : ℂ) 1`. -/
theorem analyticOnNhd_extend (F : DiskHardySpace) :
    AnalyticOnNhd ℂ F.extend (ball (0 : ℂ) 1) :=
  F.differentiableOn_extend.analyticOnNhd isOpen_ball

/-- Every `F : DiskHardySpace` is continuous on `Metric.ball (0 : ℂ) 1`. -/
theorem continuous_coe (F : DiskHardySpace) : Continuous (F : ball (0 : ℂ) 1 → ℂ) := by
  have h := F.differentiableOn_extend.continuousOn.comp_continuous continuous_subtype_val
    fun z ↦ z.2
  simpa only [Function.comp_def, extend_coe] using h

/-- A real function `u : ℂ → ℝ` is a harmonic majorant of `F : DiskHardySpace` if `u` is harmonic
on `Metric.ball (0 : ℂ) 1` and dominates `z ↦ ‖F z‖ ^ 2` throughout the disk. -/
def IsHarmonicMajorant (F : DiskHardySpace) (u : ℂ → ℝ) : Prop :=
  HarmonicOnNhd u (ball (0 : ℂ) 1) ∧ ∀ z : ball (0 : ℂ) 1, ‖F z‖ ^ 2 ≤ u z

theorem isHarmonicMajorant_iff_extend {F : DiskHardySpace} {u : ℂ → ℝ} :
    F.IsHarmonicMajorant u ↔
      HarmonicOnNhd u (ball (0 : ℂ) 1) ∧ ∀ w ∈ ball (0 : ℂ) 1, ‖F.extend w‖ ^ 2 ≤ u w := by
  refine ⟨fun ⟨hu, hle⟩ ↦ ⟨hu, fun w hw ↦ ?_⟩, fun ⟨hu, hle⟩ ↦ ⟨hu, fun z ↦ ?_⟩⟩
  · rw [F.extend_apply_of_mem hw]
    exact hle ⟨w, hw⟩
  · rw [← F.extend_coe z]
    exact hle z z.2

theorem exists_isHarmonicMajorant (F : DiskHardySpace) :
    ∃ u : ℂ → ℝ, F.IsHarmonicMajorant u :=
  F.exists_harmonicMajorant'

theorem apply_zero_nonneg_of_isHarmonicMajorant {F : DiskHardySpace} {u : ℂ → ℝ}
    (hu : F.IsHarmonicMajorant u) : 0 ≤ u 0 :=
  (sq_nonneg _).trans (hu.2 ⟨0, mem_ball_self zero_lt_one⟩)

theorem bddBelow_image_eval_zero_isHarmonicMajorant (F : DiskHardySpace) :
    BddBelow ((fun u : ℂ → ℝ ↦ u 0) '' {u | F.IsHarmonicMajorant u}) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact apply_zero_nonneg_of_isHarmonicMajorant hu

/-- Restrict an ambient holomorphic function `g : ℂ → ℂ` on `Metric.ball (0 : ℂ) 1` admitting a
real harmonic majorant of `‖g ·‖ ^ 2` to an element of `DiskHardySpace`. -/
def of (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hm : ∃ u : ℂ → ℝ, HarmonicOnNhd u (ball (0 : ℂ) 1) ∧
      ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ^ 2 ≤ u w) : DiskHardySpace where
  toFun z := g z
  exists_differentiableOn' := ⟨g, hg, fun _ ↦ rfl⟩
  exists_harmonicMajorant' :=
    let ⟨u, hu, hgu⟩ := hm
    ⟨u, hu, fun z ↦ hgu z z.2⟩

@[simp]
theorem of_apply (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1)) (hm)
    (z : ball (0 : ℂ) 1) : of g hg hm z = g z :=
  (rfl)

theorem eqOn_extend_of (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1)) (hm) :
    EqOn (of g hg hm).extend g (ball (0 : ℂ) 1) :=
  fun _ hw ↦ (of g hg hm).extend_apply_of_mem hw

/-! ### Complex vector space structure -/

instance : Zero DiskHardySpace where
  zero :=
    { toFun := 0
      exists_differentiableOn' := ⟨0, differentiableOn_const 0, fun _ ↦ rfl⟩
      exists_harmonicMajorant' :=
        ⟨0, harmonicOnNhd_const 0, fun _ ↦ by simp⟩ }

/-- Pointwise sum of two `DiskHardySpace` functions admits a real harmonic majorant on the unit
disk. -/
theorem exists_harmonicMajorant_add (F G : DiskHardySpace) :
    ∃ w : ℂ → ℝ, HarmonicOnNhd w (ball (0 : ℂ) 1) ∧
      ∀ z : ball (0 : ℂ) 1, ‖F z + G z‖ ^ 2 ≤ w z := by
  obtain ⟨u, hu, hFu⟩ := F.exists_isHarmonicMajorant
  obtain ⟨v, hv, hGv⟩ := G.exists_isHarmonicMajorant
  refine ⟨(2 : ℝ) • u + (2 : ℝ) • v,
    (hu.const_smul (c := (2 : ℝ))).add (hv.const_smul (c := (2 : ℝ))), fun z ↦ ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have htri : ‖F z + G z‖ ≤ ‖F z‖ + ‖G z‖ := norm_add_le _ _
  have h1 : ‖F z + G z‖ ^ 2 ≤ (‖F z‖ + ‖G z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hsq : (‖F z‖ + ‖G z‖) ^ 2 ≤ 2 * ‖F z‖ ^ 2 + 2 * ‖G z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖F z‖ - ‖G z‖)]
  linarith [hFu z, hGv z]

instance : Add DiskHardySpace where
  add F G :=
    { toFun := ⇑F + ⇑G
      exists_differentiableOn' :=
        ⟨F.extend + G.extend, F.differentiableOn_extend.add G.differentiableOn_extend,
          fun z ↦ by simp⟩
      exists_harmonicMajorant' := exists_harmonicMajorant_add F G }

instance : Neg DiskHardySpace where
  neg F :=
    { toFun := -⇑F
      exists_differentiableOn' := ⟨-F.extend, F.differentiableOn_extend.neg, fun z ↦ by simp⟩
      exists_harmonicMajorant' := by
        obtain ⟨u, hu, hFu⟩ := F.exists_isHarmonicMajorant
        exact ⟨u, hu, fun z ↦ by simpa using hFu z⟩ }

instance : Sub DiskHardySpace where
  sub F G :=
    { toFun := ⇑F - ⇑G
      exists_differentiableOn' :=
        ⟨F.extend - G.extend, F.differentiableOn_extend.sub G.differentiableOn_extend,
          fun z ↦ by simp⟩
      exists_harmonicMajorant' := by
        obtain ⟨w, hw, hle⟩ := exists_harmonicMajorant_add F (-G)
        refine ⟨w, hw, fun z ↦ ?_⟩
        have hz : ‖F z - G z‖ ^ 2 = ‖F z + (-G).toFun z‖ ^ 2 := by
          rw [sub_eq_add_neg]; rfl
        exact hz.trans_le (hle z) }

instance : SMul ℂ DiskHardySpace where
  smul c F :=
    { toFun := c • ⇑F
      exists_differentiableOn' :=
        ⟨c • F.extend, F.differentiableOn_extend.const_smul c, fun z ↦ by simp⟩
      exists_harmonicMajorant' := by
        obtain ⟨u, hu, hFu⟩ := F.exists_isHarmonicMajorant
        refine ⟨‖c‖ ^ 2 • u, hu.const_smul (c := ‖c‖ ^ 2), fun z ↦ ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_left (hFu z) (sq_nonneg ‖c‖) }

instance : SMul ℕ DiskHardySpace where
  smul n F :=
    { toFun := n • ⇑F
      exists_differentiableOn' :=
        ⟨(n : ℂ) • F.extend, F.differentiableOn_extend.const_smul (n : ℂ),
          fun z ↦ by simp⟩
      exists_harmonicMajorant' := by
        obtain ⟨u, hu, hFu⟩ := F.exists_isHarmonicMajorant
        refine ⟨(n : ℝ) ^ 2 • u, hu.const_smul (c := (n : ℝ) ^ 2), fun z ↦ ?_⟩
        simp only [Pi.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast, smul_eq_mul,
          mul_pow]
        exact mul_le_mul_of_nonneg_left (hFu z) (sq_nonneg (n : ℝ)) }

instance : SMul ℤ DiskHardySpace where
  smul n F :=
    { toFun := n • ⇑F
      exists_differentiableOn' :=
        ⟨(n : ℂ) • F.extend, F.differentiableOn_extend.const_smul (n : ℂ),
          fun z ↦ by simp⟩
      exists_harmonicMajorant' := by
        obtain ⟨u, hu, hFu⟩ := F.exists_isHarmonicMajorant
        refine ⟨(n : ℝ) ^ 2 • u, hu.const_smul (c := (n : ℝ) ^ 2), fun z ↦ ?_⟩
        simp only [Pi.smul_apply, zsmul_eq_mul, norm_mul, Complex.norm_intCast, smul_eq_mul,
          mul_pow, sq_abs]
        exact mul_le_mul_of_nonneg_left (hFu z) (sq_nonneg (n : ℝ)) }

@[simp] theorem coe_zero : ((0 : DiskHardySpace) : ball (0 : ℂ) 1 → ℂ) = 0 := (rfl)
@[simp] theorem zero_apply (z : ball (0 : ℂ) 1) : (0 : DiskHardySpace) z = 0 := (rfl)
@[simp] theorem coe_add (F G : DiskHardySpace) :
    ((F + G : DiskHardySpace) : ball (0 : ℂ) 1 → ℂ) = ⇑F + ⇑G := (rfl)
@[simp] theorem add_apply (F G : DiskHardySpace) (z : ball (0 : ℂ) 1) :
    (F + G) z = F z + G z := (rfl)
@[simp] theorem coe_neg (F : DiskHardySpace) :
    ((-F : DiskHardySpace) : ball (0 : ℂ) 1 → ℂ) = -⇑F := (rfl)
@[simp] theorem neg_apply (F : DiskHardySpace) (z : ball (0 : ℂ) 1) : (-F) z = -F z := (rfl)
@[simp] theorem coe_sub (F G : DiskHardySpace) :
    ((F - G : DiskHardySpace) : ball (0 : ℂ) 1 → ℂ) = ⇑F - ⇑G := (rfl)
@[simp] theorem sub_apply (F G : DiskHardySpace) (z : ball (0 : ℂ) 1) :
    (F - G) z = F z - G z := (rfl)
@[simp] theorem coe_smul (c : ℂ) (F : DiskHardySpace) :
    ((c • F : DiskHardySpace) : ball (0 : ℂ) 1 → ℂ) = c • ⇑F := (rfl)
@[simp] theorem smul_apply (c : ℂ) (F : DiskHardySpace) (z : ball (0 : ℂ) 1) :
    (c • F) z = c * F z := (rfl)

instance : AddCommGroup DiskHardySpace :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module ℂ DiskHardySpace :=
  DFunLike.coe_injective.module ℂ ⟨⟨DFunLike.coe, coe_zero⟩, coe_add⟩ coe_smul

/-! ### Intrinsic harmonic-majorant norm -/

/-- The norm on `DiskHardySpace`, defined intrinsically as the square root of the infimum of `u 0`
over all real harmonic majorants `u` of `‖F ·‖ ^ 2` on `Metric.ball (0 : ℂ) 1`. -/
instance : Norm DiskHardySpace where
  norm F := √(sInf ((fun u : ℂ → ℝ ↦ u 0) '' {u | F.IsHarmonicMajorant u}))

theorem norm_def (F : DiskHardySpace) :
    ‖F‖ = √(sInf ((fun u : ℂ → ℝ ↦ u 0) '' {u | F.IsHarmonicMajorant u})) :=
  (rfl)

/-! ### Boundary-value construction via Taylor coefficients -/

/-- The `n`-th Taylor coefficient `(n !)⁻¹ * iteratedDeriv n F.extend 0` of `F : DiskHardySpace`
at the origin. -/
def taylorCoeff (F : DiskHardySpace) (n : ℕ) : ℂ :=
  (n ! : ℂ)⁻¹ * iteratedDeriv n F.extend 0

/-- The Taylor coefficients of any `F : DiskHardySpace` at the origin are square-summable, with
`∑' n, ‖F.taylorCoeff n‖ ^ 2 ≤ u 0` for every harmonic majorant `u` of `F`. -/
theorem summable_and_tsum_norm_sq_taylorCoeff_le {F : DiskHardySpace} {u : ℂ → ℝ}
    (hu : F.IsHarmonicMajorant u) :
    Summable (fun n : ℕ ↦ ‖F.taylorCoeff n‖ ^ 2) ∧
      (∑' n : ℕ, ‖F.taylorCoeff n‖ ^ 2) ≤ u 0 := by
  obtain ⟨hu_harm, hu_le⟩ := isHarmonicMajorant_iff_extend.mp hu
  have hB : ∀ r ∈ Ico (0 : ℝ) 1, Real.circleAverage (fun w ↦ ‖F.extend w‖ ^ 2) 0 r ≤ u 0 := by
    intro r hr
    have hr' : |r| < 1 := by rw [abs_of_nonneg hr.1]; exact hr.2
    exact circleAverage_le_of_harmonicOnNhd
      ((F.differentiableOn_extend.continuousOn.norm).pow 2) hu_harm hu_le hr'
  have h := summable_and_tsum_norm_sq_taylorCoeff_le_of_circleAverage_le
    zero_lt_one F.differentiableOn_extend hB
  simpa only [taylorCoeff, one_pow, mul_one] using h

theorem summable_norm_sq_taylorCoeff (F : DiskHardySpace) :
    Summable fun n : ℕ ↦ ‖F.taylorCoeff n‖ ^ 2 := by
  obtain ⟨u, hu⟩ := F.exists_isHarmonicMajorant
  exact (summable_and_tsum_norm_sq_taylorCoeff_le hu).1

/-- The boundary Hardy element `F.boundaryValue : HardySpace` whose Fourier coefficients on
`UnitAddCircle` are the Taylor coefficients of `F` at the origin. -/
def boundaryValue (F : DiskHardySpace) : HardySpace :=
  hardyBasis.repr.symm ⟨F.taylorCoeff, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using F.summable_norm_sq_taylorCoeff)⟩

@[simp]
theorem hardyBasis_repr_boundaryValue (F : DiskHardySpace) (n : ℕ) :
    hardyBasis.repr F.boundaryValue n = F.taylorCoeff n := by
  simp [boundaryValue]

theorem fourierCoeff_boundaryValue (F : DiskHardySpace) (n : ℕ) :
    fourierCoeff (F.boundaryValue : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n =
      F.taylorCoeff n := by
  rw [← hardyBasis_repr, hardyBasis_repr_boundaryValue]

@[simp]
theorem diskFunction_boundaryValue_apply (F : DiskHardySpace) (z : ball (0 : ℂ) 1) :
    F.boundaryValue.diskFunction z = F z := by
  rw [HardySpace.diskFunction_def]
  simp_rw [F.fourierCoeff_boundaryValue, taylorCoeff]
  have h := Complex.taylorSeries_eq_on_ball' z.2 F.differentiableOn_extend
  simpa only [sub_zero, F.extend_coe z] using h

theorem eqOn_diskFunction_boundaryValue_extend (F : DiskHardySpace) :
    EqOn F.boundaryValue.diskFunction F.extend (ball (0 : ℂ) 1) := by
  intro w hw
  rw [F.extend_apply_of_mem hw]
  exact F.diskFunction_boundaryValue_apply ⟨w, hw⟩

end DiskHardySpace

namespace HardySpace

/-- Send a boundary Hardy element `x : HardySpace` to its holomorphic disk function in
`DiskHardySpace`, witnessed by its canonical harmonic majorant `x.harmonicMajorant`. -/
def toDiskHardy (x : HardySpace) : DiskHardySpace :=
  DiskHardySpace.of x.diskFunction x.differentiableOn_diskFunction
    ⟨x.harmonicMajorant, x.harmonicOnNhd_harmonicMajorant,
      fun _ hw ↦ x.norm_diskFunction_sq_le_harmonicMajorant hw⟩

@[simp]
theorem toDiskHardy_apply (x : HardySpace) (z : ball (0 : ℂ) 1) :
    x.toDiskHardy z = x.diskFunction z :=
  (rfl)

theorem extend_toDiskHardy_of_mem (x : HardySpace) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    x.toDiskHardy.extend w = x.diskFunction w :=
  x.toDiskHardy.extend_apply_of_mem hw

theorem toDiskHardy_injective : Function.Injective toDiskHardy := by
  intro x y hxy
  have heq : EqOn (x - y).diskFunction 0 (ball (0 : ℂ) 1) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hsub : x - y = x + (-1 : ℂ) • y := by rw [sub_eq_add_neg, ← neg_one_smul ℂ y]
    have hz := congrArg (fun F : DiskHardySpace ↦ F ⟨w, hw⟩) hxy
    simp only [toDiskHardy_apply] at hz
    rw [hsub, diskFunction_add x ((-1 : ℂ) • y) hw1, diskFunction_smul, hz]
    simp
  exact sub_eq_zero.mp ((x - y).eqOn_diskFunction_zero_iff.mp heq)

/-- The complex-linear equivalence between boundary `HardySpace` and `DiskHardySpace`, prior to
installing the normed structure on `DiskHardySpace`. -/
def diskHardyLinearEquiv : HardySpace ≃ₗ[ℂ] DiskHardySpace where
  toFun := toDiskHardy
  map_add' x y := by
    ext z
    exact x.diskFunction_add y (mem_ball_zero_iff.mp z.2)
  map_smul' c x := by
    ext z
    exact x.diskFunction_smul c
  invFun := DiskHardySpace.boundaryValue
  left_inv x := by
    apply toDiskHardy_injective
    ext z
    exact x.toDiskHardy.diskFunction_boundaryValue_apply z
  right_inv F := by
    ext z
    exact F.diskFunction_boundaryValue_apply z

@[simp]
theorem boundaryValue_toDiskHardy (x : HardySpace) : x.toDiskHardy.boundaryValue = x :=
  diskHardyLinearEquiv.left_inv x

@[simp]
theorem toDiskHardy_boundaryValue (F : DiskHardySpace) : F.boundaryValue.toDiskHardy = F :=
  diskHardyLinearEquiv.right_inv F

theorem isLeast_image_eval_zero_isHarmonicMajorant_toDiskHardy (x : HardySpace) :
    IsLeast ((fun u : ℂ → ℝ ↦ u 0) '' {u | x.toDiskHardy.IsHarmonicMajorant u}) (‖x‖ ^ 2) := by
  refine ⟨⟨x.harmonicMajorant,
      ⟨x.harmonicOnNhd_harmonicMajorant, fun z ↦ x.norm_diskFunction_sq_le_harmonicMajorant z.2⟩,
      x.harmonicMajorant_zero⟩, ?_⟩
  rintro _ ⟨u, ⟨hu, hle⟩, rfl⟩
  exact x.norm_sq_le_harmonic_majorant_zero hu fun w hw ↦ hle ⟨w, hw⟩

@[simp]
theorem norm_toDiskHardy (x : HardySpace) : ‖x.toDiskHardy‖ = ‖x‖ := by
  rw [DiskHardySpace.norm_def,
    (isLeast_image_eval_zero_isHarmonicMajorant_toDiskHardy x).csInf_eq,
    Real.sqrt_sq (norm_nonneg x)]

end HardySpace

namespace DiskHardySpace

/-- Linear equivalence `DiskHardySpace ≃ₗ[ℂ] HardySpace` given by `boundaryValue`. -/
private def boundaryValueLinearEquiv : DiskHardySpace ≃ₗ[ℂ] HardySpace :=
  HardySpace.diskHardyLinearEquiv.symm

theorem boundaryValue_injective : Function.Injective boundaryValue :=
  boundaryValueLinearEquiv.injective

@[simp]
theorem boundaryValue_zero : (0 : DiskHardySpace).boundaryValue = 0 :=
  boundaryValueLinearEquiv.map_zero

@[simp]
theorem boundaryValue_add (F G : DiskHardySpace) :
    (F + G).boundaryValue = F.boundaryValue + G.boundaryValue :=
  boundaryValueLinearEquiv.map_add F G

@[simp]
theorem boundaryValue_neg (F : DiskHardySpace) : (-F).boundaryValue = -F.boundaryValue :=
  boundaryValueLinearEquiv.map_neg F

@[simp]
theorem boundaryValue_sub (F G : DiskHardySpace) :
    (F - G).boundaryValue = F.boundaryValue - G.boundaryValue :=
  boundaryValueLinearEquiv.map_sub F G

@[simp]
theorem boundaryValue_smul (c : ℂ) (F : DiskHardySpace) :
    (c • F).boundaryValue = c • F.boundaryValue :=
  boundaryValueLinearEquiv.map_smul c F

/-- The intrinsic harmonic-majorant norm on `DiskHardySpace` equals the `L²` norm of the boundary
value in `HardySpace`. -/
theorem norm_eq_norm_boundaryValue (F : DiskHardySpace) : ‖F‖ = ‖F.boundaryValue‖ := by
  conv_lhs => rw [← HardySpace.toDiskHardy_boundaryValue F]
  exact HardySpace.norm_toDiskHardy F.boundaryValue

theorem norm_boundaryValue (F : DiskHardySpace) : ‖F.boundaryValue‖ = ‖F‖ :=
  F.norm_eq_norm_boundaryValue.symm

@[simp]
theorem norm_coe_boundaryValue (F : DiskHardySpace) :
    ‖(F.boundaryValue : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖ = ‖F‖ :=
  F.norm_boundaryValue

/-! ### Hilbert-space structure on `DiskHardySpace` -/

private theorem norm_neg_add_eq_dist_boundaryValue (F G : DiskHardySpace) :
    ‖-F + G‖ = dist F.boundaryValue G.boundaryValue := by
  rw [norm_eq_norm_boundaryValue, boundaryValue_add, boundaryValue_neg,
    ← NormedAddCommGroup.dist_eq]

instance : NormedAddCommGroup DiskHardySpace where
  dist_self F := by
    rw [norm_neg_add_eq_dist_boundaryValue]
    exact dist_self _
  dist_comm F G := by
    rw [norm_neg_add_eq_dist_boundaryValue, norm_neg_add_eq_dist_boundaryValue]
    exact dist_comm _ _
  dist_triangle F G H := by
    rw [norm_neg_add_eq_dist_boundaryValue, norm_neg_add_eq_dist_boundaryValue,
      norm_neg_add_eq_dist_boundaryValue]
    exact dist_triangle _ _ _
  eq_of_dist_eq_zero {F G} h := by
    rw [norm_neg_add_eq_dist_boundaryValue, dist_eq_zero] at h
    exact boundaryValue_injective h

instance : Inner ℂ DiskHardySpace where
  inner F G := ⟪F.boundaryValue, G.boundaryValue⟫_ℂ

theorem inner_def (F G : DiskHardySpace) : ⟪F, G⟫_ℂ = ⟪F.boundaryValue, G.boundaryValue⟫_ℂ :=
  (rfl)

instance : InnerProductSpace ℂ DiskHardySpace where
  norm_smul_le c F := by
    rw [norm_eq_norm_boundaryValue, boundaryValue_smul, norm_eq_norm_boundaryValue, norm_smul]
  norm_sq_eq_re_inner F := by
    rw [norm_eq_norm_boundaryValue, inner_def,
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) F.boundaryValue]
  conj_inner_symm F G := by
    rw [inner_def, inner_def, InnerProductSpace.conj_inner_symm]
  add_left F G H := by
    rw [inner_def, boundaryValue_add, InnerProductSpace.add_left, inner_def, inner_def]
  smul_left F G c := by
    rw [inner_def, boundaryValue_smul,
      InnerProductSpace.smul_left F.boundaryValue G.boundaryValue c, inner_def]

end DiskHardySpace

namespace HardySpace

/-- **Boundary–disk Hardy Hilbert-space isomorphism.** Sending `x : HardySpace` to its holomorphic
disk function `x.toDiskHardy` is a complex-linear isometric equivalence onto `DiskHardySpace` with
inverse `DiskHardySpace.boundaryValue`. -/
def diskHardyEquiv : HardySpace ≃ₗᵢ[ℂ] DiskHardySpace :=
  { diskHardyLinearEquiv with
    norm_map' := norm_toDiskHardy }

@[simp]
theorem diskHardyEquiv_apply (x : HardySpace) (z : ball (0 : ℂ) 1) :
    diskHardyEquiv x z = x.diskFunction z :=
  (rfl)

@[simp]
theorem coe_diskHardyEquiv_symm :
    (diskHardyEquiv.symm : DiskHardySpace → HardySpace) = DiskHardySpace.boundaryValue :=
  (rfl)

theorem diskHardyEquiv_symm_apply (F : DiskHardySpace) :
    diskHardyEquiv.symm F = F.boundaryValue :=
  (rfl)

theorem extend_diskHardyEquiv_of_mem (x : HardySpace) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (diskHardyEquiv x).extend w = x.diskFunction w :=
  x.extend_toDiskHardy_of_mem hw

end HardySpace

namespace DiskHardySpace

instance : CompleteSpace DiskHardySpace :=
  HardySpace.diskHardyEquiv.symm.toIsometryEquiv.completeSpace

/-! ### Least harmonic majorants, radial `L²` means, and boundary recovery -/

/-- The canonical real harmonic majorant of `F : DiskHardySpace`, given by the Poisson integral of
its squared boundary modulus `t ↦ ‖F.boundaryValue t‖ ^ 2`. -/
def leastHarmonicMajorant (F : DiskHardySpace) : ℂ → ℝ :=
  F.boundaryValue.harmonicMajorant

theorem leastHarmonicMajorant_def (F : DiskHardySpace) (w : ℂ) :
    F.leastHarmonicMajorant w = F.boundaryValue.harmonicMajorant w :=
  (rfl)

@[simp]
theorem leastHarmonicMajorant_diskHardyEquiv (x : HardySpace) :
    (HardySpace.diskHardyEquiv x).leastHarmonicMajorant = x.harmonicMajorant := by
  have hb : (HardySpace.diskHardyEquiv x).boundaryValue = x :=
    HardySpace.boundaryValue_toDiskHardy x
  funext w
  rw [leastHarmonicMajorant_def, hb]

/-- `F.leastHarmonicMajorant` is harmonic on `Metric.ball (0 : ℂ) 1`. -/
theorem harmonicOnNhd_leastHarmonicMajorant (F : DiskHardySpace) :
    HarmonicOnNhd F.leastHarmonicMajorant (ball (0 : ℂ) 1) :=
  F.boundaryValue.harmonicOnNhd_harmonicMajorant

/-- `F.leastHarmonicMajorant` is a harmonic majorant of `F`. -/
theorem isHarmonicMajorant_leastHarmonicMajorant (F : DiskHardySpace) :
    F.IsHarmonicMajorant F.leastHarmonicMajorant :=
  ⟨F.harmonicOnNhd_leastHarmonicMajorant, fun z ↦ by
    rw [← F.diskFunction_boundaryValue_apply z]
    exact F.boundaryValue.norm_diskFunction_sq_le_harmonicMajorant z.2⟩

/-- **Pointwise minimality of `leastHarmonicMajorant`.** Every harmonic majorant `u` of `F`
satisfies `F.leastHarmonicMajorant w ≤ u w` at every point `w ∈ Metric.ball (0 : ℂ) 1`. -/
theorem leastHarmonicMajorant_le (F : DiskHardySpace) {u : ℂ → ℝ} (hu : F.IsHarmonicMajorant u)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    F.leastHarmonicMajorant w ≤ u w := by
  refine F.boundaryValue.harmonicMajorant_le_of_harmonicOnNhd hu.1 (fun z hz ↦ ?_) hw
  rw [F.diskFunction_boundaryValue_apply ⟨z, hz⟩]
  exact hu.2 ⟨z, hz⟩

/-- **Uniqueness of the pointwise least harmonic majorant on the unit disk.** Any harmonic majorant
`u` of `F` that is pointwise bounded above on `Metric.ball (0 : ℂ) 1` by every harmonic majorant of
`F` agrees with `F.leastHarmonicMajorant` throughout `Metric.ball (0 : ℂ) 1`. -/
theorem eqOn_leastHarmonicMajorant_of_le (F : DiskHardySpace) {u : ℂ → ℝ}
    (hu : F.IsHarmonicMajorant u)
    (hmin : ∀ v : ℂ → ℝ, F.IsHarmonicMajorant v → ∀ w ∈ ball (0 : ℂ) 1, u w ≤ v w) :
    EqOn u F.leastHarmonicMajorant (ball (0 : ℂ) 1) :=
  fun _ hw ↦ le_antisymm
    (hmin F.leastHarmonicMajorant F.isHarmonicMajorant_leastHarmonicMajorant _ hw)
    (F.leastHarmonicMajorant_le hu hw)

/-- Evaluating `F.leastHarmonicMajorant` at the origin gives `‖F‖ ^ 2`. -/
@[simp]
theorem leastHarmonicMajorant_zero (F : DiskHardySpace) :
    F.leastHarmonicMajorant 0 = ‖F‖ ^ 2 := by
  rw [leastHarmonicMajorant_def, HardySpace.harmonicMajorant_zero, norm_eq_norm_boundaryValue]

/-- `‖F‖ ^ 2` is the least element of `{u 0 | F.IsHarmonicMajorant u}`. -/
theorem isLeast_image_eval_zero_isHarmonicMajorant (F : DiskHardySpace) :
    IsLeast ((fun u : ℂ → ℝ ↦ u 0) '' {u | F.IsHarmonicMajorant u}) (‖F‖ ^ 2) := by
  rw [norm_eq_norm_boundaryValue]
  simpa only [HardySpace.toDiskHardy_boundaryValue] using
    HardySpace.isLeast_image_eval_zero_isHarmonicMajorant_toDiskHardy F.boundaryValue

/-- The squared norm on `DiskHardySpace` equals the infimum of `u 0` over all harmonic majorants
`u` of `F`. -/
theorem norm_sq_eq_sInf (F : DiskHardySpace) :
    ‖F‖ ^ 2 = sInf ((fun u : ℂ → ℝ ↦ u 0) '' {u | F.IsHarmonicMajorant u}) :=
  F.isLeast_image_eval_zero_isHarmonicMajorant.csInf_eq.symm

/-- For `r ∈ (-1, 1)`, the squared circle mean of `F.extend` at radius `r` agrees with that of
`F.boundaryValue.diskFunction`. -/
theorem circleAverage_norm_sq_extend (F : DiskHardySpace) {r : ℝ} (hr : |r| < 1) :
    Real.circleAverage (fun w ↦ ‖F.extend w‖ ^ 2) 0 r =
      Real.circleAverage (fun w ↦ ‖F.boundaryValue.diskFunction w‖ ^ 2) 0 r := by
  refine Real.circleAverage_congr_sphere fun w hw ↦ ?_
  have hw_ball : w ∈ ball (0 : ℂ) 1 := sphere_subset_ball hr hw
  rw [F.eqOn_diskFunction_boundaryValue_extend hw_ball]

/-- As `r → 1⁻`, the squared circle means of `F.extend` converge to `‖F‖ ^ 2`. -/
theorem tendsto_circleAverage_norm_sq_extend (F : DiskHardySpace) :
    Tendsto (fun r : ℝ ↦ Real.circleAverage (fun w ↦ ‖F.extend w‖ ^ 2) 0 r)
      (𝓝[<] 1) (𝓝 (‖F‖ ^ 2)) := by
  rw [norm_eq_norm_boundaryValue]
  refine F.boundaryValue.tendsto_circleAverage_norm_sq_diskFunction.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
  exact (F.circleAverage_norm_sq_extend (abs_lt.mpr hr)).symm

/-- `‖F‖ ^ 2` is the least upper bound of the interior squared circle means on `[0, 1)`. -/
theorem isLUB_image_circleAverage_norm_sq_extend (F : DiskHardySpace) :
    IsLUB ((fun r : ℝ ↦ Real.circleAverage (fun w ↦ ‖F.extend w‖ ^ 2) 0 r) '' Ico 0 1)
      (‖F‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    dsimp only
    have hr' : |r| < 1 := by rw [abs_of_nonneg hr.1]; exact hr.2
    rw [F.circleAverage_norm_sq_extend hr', ← F.leastHarmonicMajorant_zero]
    exact F.boundaryValue.circleAverage_norm_sq_diskFunction_le_of_harmonic_majorant
      F.harmonicOnNhd_leastHarmonicMajorant
      (fun w hw ↦ by
        rw [F.diskFunction_boundaryValue_apply ⟨w, hw⟩]
        exact F.isHarmonicMajorant_leastHarmonicMajorant.2 ⟨w, hw⟩)
      hr'
  · intro B hB
    refine le_of_tendsto F.tendsto_circleAverage_norm_sq_extend ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
    exact hB ⟨r, ⟨hr.1.le, hr.2⟩, rfl⟩

/-- **Radial-mean characterization of the Hardy norm.** On `DiskHardySpace`, `‖F‖ ^ 2` equals the
supremum over `r ∈ [0, 1)` of the squared circle means
`Real.circleAverage (fun w ↦ ‖F.extend w‖ ^ 2) 0 r`. -/
theorem norm_sq_eq_sSup_circleAverage (F : DiskHardySpace) :
    ‖F‖ ^ 2 =
      sSup ((fun r : ℝ ↦ Real.circleAverage (fun w ↦ ‖F.extend w‖ ^ 2) 0 r) '' Ico 0 1) :=
  F.isLUB_image_circleAverage_norm_sq_extend.csSup_eq (nonempty_Ico.mpr zero_lt_one |>.image _)
    |>.symm

/-- Pointwise growth bound on `DiskHardySpace`: `‖F z‖ ≤ ‖F‖ / √(1 - ‖(z : ℂ)‖ ^ 2)`. -/
theorem norm_apply_le (F : DiskHardySpace) (z : ball (0 : ℂ) 1) :
    ‖F z‖ ≤ ‖F‖ / √(1 - ‖(z : ℂ)‖ ^ 2) := by
  rw [← F.diskFunction_boundaryValue_apply z, norm_eq_norm_boundaryValue]
  exact F.boundaryValue.norm_diskFunction_le (mem_ball_zero_iff.mp z.2)

/-- **Radial `L²` boundary convergence.** The circle restrictions `t ↦ F.extend (r * toCircle t)`
converge in `L²(UnitAddCircle)` to `F.boundaryValue` as `r → 1⁻`. -/
theorem tendsto_eLpNorm_extend_sub_boundaryValue (F : DiskHardySpace) :
    Tendsto (fun r : ℝ ↦ eLpNorm
      (fun t : AddCircle (1 : ℝ) ↦ F.extend (r * AddCircle.toCircle t) -
        (F.boundaryValue : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t)
      2 AddCircle.haarAddCircle) (𝓝[<] 1) (𝓝 0) := by
  refine F.boundaryValue.tendsto_eLpNorm_diskFunction_sub.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
  have hr' : |r| < 1 := abs_lt.mpr hr
  refine eLpNorm_congr_ae (Eventually.of_forall fun t ↦ ?_)
  dsimp only
  have hw : (r : ℂ) * (AddCircle.toCircle t : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hr'
  rw [F.eqOn_diskFunction_boundaryValue_extend hw]

/-- **Uniqueness of radial `L²` boundary limits.** Any
`g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))` to which the radial circle restrictions
`t ↦ F.extend (r * toCircle t)` converge in `L²` as `r → 1⁻` must equal
`(F.boundaryValue : Lp ℂ 2 _)`. -/
theorem eq_coe_boundaryValue_of_tendsto_eLpNorm (F : DiskHardySpace)
    {g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))}
    (hg : Tendsto (fun r : ℝ ↦ eLpNorm
      (fun t : AddCircle (1 : ℝ) ↦ F.extend (r * AddCircle.toCircle t) - g t)
      2 AddCircle.haarAddCircle) (𝓝[<] 1) (𝓝 0)) :
    g = (F.boundaryValue : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) := by
  let μ := AddCircle.haarAddCircle (T := 1)
  let b : Lp ℂ 2 μ := F.boundaryValue
  have hle : ∀ r : ℝ, edist g b ≤
      eLpNorm (fun t : AddCircle (1 : ℝ) ↦ F.extend (r * AddCircle.toCircle t) - b t) 2 μ +
        eLpNorm (fun t : AddCircle (1 : ℝ) ↦ F.extend (r * AddCircle.toCircle t) - g t) 2 μ := by
    intro r
    have hfun : (⇑g - ⇑b : AddCircle (1 : ℝ) → ℂ) =
        (fun t ↦ F.extend (r * AddCircle.toCircle t) - b t) -
          (fun t ↦ F.extend (r * AddCircle.toCircle t) - g t) := by
      ext t
      simp only [Pi.sub_apply]
      ring
    calc
      edist g b = eLpNorm (⇑g - ⇑b) 2 μ := Lp.edist_def g b
      _ = eLpNorm ((fun t : AddCircle (1 : ℝ) ↦ F.extend (r * AddCircle.toCircle t) - b t) -
            (fun t : AddCircle (1 : ℝ) ↦ F.extend (r * AddCircle.toCircle t) - g t)) 2 μ :=
        congrArg (fun h ↦ eLpNorm h 2 μ) hfun
      _ ≤ eLpNorm (fun t : AddCircle (1 : ℝ) ↦ F.extend (r * AddCircle.toCircle t) - b t) 2 μ +
            eLpNorm (fun t : AddCircle (1 : ℝ) ↦ F.extend (r * AddCircle.toCircle t) - g t) 2 μ :=
        eLpNorm_sub_le one_le_two
  have hsum := F.tendsto_eLpNorm_extend_sub_boundaryValue.add hg
  rw [add_zero] at hsum
  exact edist_le_zero.mp (ge_of_tendsto hsum (Eventually.of_forall hle))

/-! ### Explicit examples on `DiskHardySpace` -/

/-- The `n`-th orthonormal monomial `(z ↦ z ^ n)` in `DiskHardySpace`, image of `hardyBasis n`
under `HardySpace.diskHardyEquiv`. -/
def monomial (n : ℕ) : DiskHardySpace :=
  HardySpace.diskHardyEquiv (hardyBasis n)

@[simp]
theorem monomial_apply (n : ℕ) (z : ball (0 : ℂ) 1) : monomial n z = (z : ℂ) ^ n := by
  simp [monomial]

@[simp]
theorem boundaryValue_monomial (n : ℕ) : (monomial n).boundaryValue = hardyBasis n := by
  rw [monomial, ← HardySpace.diskHardyEquiv_symm_apply, LinearIsometryEquiv.symm_apply_apply]

theorem norm_monomial (n : ℕ) : ‖monomial n‖ = 1 := by
  rw [monomial, HardySpace.diskHardyEquiv.norm_map, norm_hardyBasis]

@[simp]
theorem leastHarmonicMajorant_monomial (n : ℕ) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (monomial n).leastHarmonicMajorant w = 1 := by
  rw [monomial, leastHarmonicMajorant_diskHardyEquiv, HardySpace.harmonicMajorant_hardyBasis n hw]

/-- `monomial 1` (`z ↦ z`) vanishes at the origin while having Hardy norm `1`, separating the
Hardy norm `√((monomial 1).leastHarmonicMajorant 0)` from `‖monomial 1 0‖`. -/
theorem monomial_one_apply_zero_and_norm :
    monomial 1 ⟨0, mem_ball_self zero_lt_one⟩ = 0 ∧ ‖monomial 1‖ = 1 :=
  ⟨by simp, norm_monomial 1⟩

/-- For `monomial 0 + monomial 1` (`z ↦ 1 + z`), the squared Hardy norm is `2` and the least
harmonic majorant on `Metric.ball (0 : ℂ) 1` is `w ↦ 2 + 2 * w.re`. -/
theorem norm_sq_and_leastHarmonicMajorant_monomial_zero_add_one :
    ‖monomial 0 + monomial 1‖ ^ 2 = 2 ∧
      ∀ w ∈ ball (0 : ℂ) 1,
        (monomial 0 + monomial 1).leastHarmonicMajorant w = 2 + 2 * w.re := by
  have heq : monomial 0 + monomial 1 =
      HardySpace.diskHardyEquiv (hardyBasis 0 + hardyBasis 1) :=
    (HardySpace.diskHardyEquiv.map_add (hardyBasis 0) (hardyBasis 1)).symm
  refine ⟨?_, fun w hw ↦ ?_⟩
  · rw [heq, HardySpace.diskHardyEquiv.norm_map, sq,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)]
    · rw [norm_hardyBasis, norm_hardyBasis]
      norm_num
    · exact (orthonormal_iff_ite.mp hardyBasis.orthonormal 0 1).trans (by simp)
  · rw [heq, leastHarmonicMajorant_diskHardyEquiv,
      HardySpace.harmonicMajorant_hardyBasis_zero_add_one hw]

end DiskHardySpace

end TauCeti

end
