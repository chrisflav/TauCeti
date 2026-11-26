/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
public import TauCeti.Analysis.Sobolev.Conformal
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv
public import TauCeti.MeasureTheory.Function.Lp.Multiplication

import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian.Power
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace

/-!
# Scalar and vector Cauchy--Riemann resolvent operators on `ℝ²`

Via the volume-preserving identification `TauCeti.euclideanPlaneEquivProd` between `ℝ²`
(`EuclideanSpace ℝ (Fin 2)`) and `ℝ × ℝ`, the Bessel potential resolvent
`(1 - Δ)⁻¹ : L²(ℝ²) → H²(ℝ²)` (`BesselPotentialSpace.shiftedLaplacianRpowEquiv`)
induces bounded operators `T_val`, `T_s`, `T_t`, `T_ss`, `T_st`, `T_ts`, `T_tt` on
`L²(ℝ × ℝ, ℝ)` satisfying `-(T_ss + T_tt) + T_val = id` and `T_st = T_ts`,
with `T_val`, `T_s`, `T_t` factoring through `H¹(ℝ²)`.

Lifting these scalar operators coordinatewise to a finite-dimensional real Banach space `V` yields
`liftOp V T`, which commutes with every constant linear map `J₀ : V →L[ℝ] V`.
When `J₀² = -id`, the triple
`(P_val, P_s, P_t) = (-(liftOp V T_s - J₀ ∘ liftOp V T_t), ...)`
solves `P_s + J₀ P_t = id - liftOp V T_val`, carries Schwartz data to smooth planes, and composes
with compactly supported smooth cutoffs to give compact operators by Rellich's theorem
(`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real ContinuousLinearMap
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace LineDeriv Laplacian

namespace TauCeti.ConformalSobolev.PlaneResolvent

section ScalarPlane

/-! ### Plane identification and scalar resolvent operators -/

private abbrev E₂ := EuclideanSpace ℝ (Fin 2)

private noncomputable def e₂ : E₂ ≃ᵐ ℝ × ℝ :=
  TauCeti.euclideanPlaneEquivProd

private theorem he₂ :
    MeasurePreserving e₂ (volume : Measure E₂) (volume : Measure (ℝ × ℝ)) :=
  TauCeti.measurePreserving_euclideanPlaneEquivProd

private theorem he₂_symm :
    MeasurePreserving e₂.symm (volume : Measure (ℝ × ℝ)) (volume : Measure E₂) :=
  he₂.symm _

private noncomputable def e₂CLE : E₂ ≃L[ℝ] ℝ × ℝ where
  toFun y := (y 0, y 1)
  invFun z := WithLp.toLp 2 ![z.1, z.2]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    ext i
    fin_cases i <;> rfl
  right_inv _ := rfl
  continuous_toFun :=
    (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.prodMk
      (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous
  continuous_invFun := (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    (continuous_pi fun i ↦ by fin_cases i <;> [exact continuous_fst; exact continuous_snd])

private theorem e₂CLE_coe : (e₂CLE : E₂ → ℝ × ℝ) = e₂ :=
  funext fun y ↦ (TauCeti.euclideanPlaneEquivProd_apply y).symm

private theorem e₂CLE_symm_coe : (e₂CLE.symm : ℝ × ℝ → E₂) = e₂.symm :=
  funext fun z ↦ (TauCeti.euclideanPlaneEquivProd_symm_apply z).symm

private noncomputable def b₂ : OrthonormalBasis (Fin 2) ℝ E₂ :=
  EuclideanSpace.basisFun (Fin 2) ℝ

private theorem e₂CLE_symm_fst : e₂CLE.symm (1, 0) = b₂ 0 := by
  ext i
  rw [b₂, EuclideanSpace.basisFun_apply]
  change (WithLp.toLp 2 ![(1 : ℝ), 0] : E₂) i = _
  fin_cases i <;> simp

private theorem e₂CLE_symm_snd : e₂CLE.symm (0, 1) = b₂ 1 := by
  ext i
  rw [b₂, EuclideanSpace.basisFun_apply]
  change (WithLp.toLp 2 ![(0 : ℝ), 1] : E₂) i = _
  fin_cases i <;> simp

private theorem fderiv_comp_e₂_symm_fst {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E₂ → W} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    fderiv ℝ (f ∘ e₂.symm) z (1, 0) = fderiv ℝ f (e₂.symm z) (b₂ 0) := by
  have hc : HasFDerivAt (f ∘ e₂CLE.symm)
      ((fderiv ℝ f (e₂CLE.symm z)).comp (e₂CLE.symm : ℝ × ℝ →L[ℝ] E₂)) z :=
    (hf (e₂CLE.symm z)).hasFDerivAt.comp z e₂CLE.symm.hasFDerivAt
  rw [← e₂CLE_symm_coe]
  simpa [e₂CLE_symm_fst] using congrFun (congrArg DFunLike.coe hc.fderiv) (1, 0)

private theorem fderiv_comp_e₂_symm_snd {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E₂ → W} (hf : Differentiable ℝ f) (z : ℝ × ℝ) :
    fderiv ℝ (f ∘ e₂.symm) z (0, 1) = fderiv ℝ f (e₂.symm z) (b₂ 1) := by
  have hc : HasFDerivAt (f ∘ e₂CLE.symm)
      ((fderiv ℝ f (e₂CLE.symm z)).comp (e₂CLE.symm : ℝ × ℝ →L[ℝ] E₂)) z :=
    (hf (e₂CLE.symm z)).hasFDerivAt.comp z e₂CLE.symm.hasFDerivAt
  rw [← e₂CLE_symm_coe]
  simpa [e₂CLE_symm_snd] using congrFun (congrArg DFunLike.coe hc.fderiv) (0, 1)

/-- The canonical isometric isomorphism `L²(ℝ², W) ≃ₗᵢ[ℝ] L²(ℝ × ℝ, W)` induced by
`TauCeti.euclideanPlaneEquivProd`. -/
noncomputable def planeEquiv (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] :
    Lp W 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≃ₗᵢ[ℝ]
      Lp W 2 (volume : Measure (ℝ × ℝ)) :=
  Lp.compMeasurePreservingₗᵢEquiv ℝ he₂_symm he₂
    (.of_forall fun y ↦ e₂.symm_apply_apply y)

private theorem coeFn_planeEquiv {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (u : Lp W 2 (volume : Measure E₂)) :
    (planeEquiv W u : ℝ × ℝ → W) =ᵐ[volume] u ∘ e₂.symm :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv ℝ he₂_symm he₂ _ u

private noncomputable def resH2 :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] H^{(0 : ℝ) - 2 * (-1)}(E₂, ℂ) :=
  ((BesselPotentialSpace.shiftedLaplacianRpowEquiv (E := E₂) (F := ℂ) one_pos (-1) 0)
      : H^{0}(E₂, ℂ) →L[ℂ] H^{(0 : ℝ) - 2 * (-1)}(E₂, ℂ)).restrictScalars ℝ ∘L
    ((BesselPotentialSpace.toLpₗᵢ E₂ ℂ 0 2).symm.toContinuousLinearEquiv
      : Lp ℂ 2 (volume : Measure E₂) →L[ℂ] H^{0}(E₂, ℂ)).restrictScalars ℝ ∘L
    (Lp.ofRealLI ℂ 2 (volume : Measure E₂)).toContinuousLinearMap ∘L
    (planeEquiv ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem toDistr_resH2 (f : Lp ℝ 2 (volume : Measure (ℝ × ℝ))) :
    (resH2 f).toDistr = TemperedDistribution.laplacianResolvent ℂ 1
      ((Lp.ofRealLI ℂ 2 (volume : Measure E₂) ((planeEquiv ℝ).symm f) :
        Lp ℂ 2 (volume : Measure E₂)) : 𝓢'(E₂, ℂ)) := by
  simp [resH2, TemperedDistribution.shiftedLaplacianRpow_neg_one]

/-- The resolvent `(1 - Δ)⁻¹` viewed as a bounded map
`L²(ℝ × ℝ, ℝ) → H¹(EuclideanSpace ℝ (Fin 2), ℂ)`. -/
noncomputable def resH1_val :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] H^{1}(EuclideanSpace ℝ (Fin 2), ℂ) :=
  (BesselPotentialSpace.inclusion (by norm_num : (1 : ℝ) ≤ 0 - 2 * (-1))).restrictScalars ℝ
    ∘L resH2

private noncomputable def resH1_deriv (i : Fin 2) :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] H^{1}(E₂, ℂ) :=
  (BesselPotentialSpace.lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top
      (b₂ i)).restrictScalars ℝ ∘L
    (BesselPotentialSpace.inclusion
      (by norm_num : ((1 : ℝ) + 1) ≤ 0 - 2 * (-1))).restrictScalars ℝ ∘L
    resH2

private noncomputable def resH0_deriv (i j : Fin 2) :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] H^{0}(E₂, ℂ) :=
  (BesselPotentialSpace.lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top
      (b₂ i)).restrictScalars ℝ ∘L
    (BesselPotentialSpace.lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top
      (b₂ j)).restrictScalars ℝ ∘L
    (BesselPotentialSpace.inclusion
      (by norm_num : (((0 : ℝ) + 1) + 1) ≤ 0 - 2 * (-1))).restrictScalars ℝ ∘L
    resH2

/-- Projection from `H¹(ℝ², ℂ)` to real-valued `L²(ℝ × ℝ, ℝ)` via real parts and
`planeEquiv`. -/
noncomputable def fromH1 :
    H^{1}(EuclideanSpace ℝ (Fin 2), ℂ) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  (planeEquiv ℝ).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    Lp.reCLM ℂ 2 (volume : Measure E₂) ∘L
    (BesselPotentialSpace.inclusionLp (E := E₂) (G := ℂ) zero_le_one).restrictScalars ℝ

private noncomputable def fromH0 :
    H^{0}(E₂, ℂ) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  (planeEquiv ℝ).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    Lp.reCLM ℂ 2 (volume : Measure E₂) ∘L
    (BesselPotentialSpace.inclusionLp (E := E₂) (G := ℂ) le_rfl).restrictScalars ℝ

private theorem fromH1_eq_fromH0_inclusion (u : H^{1}(E₂, ℂ)) :
    fromH1 u = fromH0 (BesselPotentialSpace.inclusion zero_le_one u) := by
  simp [fromH1, fromH0]

/-- The scalar resolvent `(1 - Δ)⁻¹` on `L²(ℝ × ℝ, ℝ)`. -/
noncomputable def T_val :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  fromH1 ∘L resH1_val

private noncomputable def T_s :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  fromH1 ∘L resH1_deriv 0

private noncomputable def T_t :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  fromH1 ∘L resH1_deriv 1

private noncomputable def T_ss :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  fromH0 ∘L resH0_deriv 0 0

/-- The mixed second derivative `∂_s ∂_t (1 - Δ)⁻¹` on `L²(ℝ × ℝ, ℝ)`. -/
noncomputable def T_st :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  fromH0 ∘L resH0_deriv 0 1

private noncomputable def T_ts :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  fromH0 ∘L resH0_deriv 1 0

/-- The second `t`-derivative `∂_t ∂_t (1 - Δ)⁻¹` on `L²(ℝ × ℝ, ℝ)`. -/
noncomputable def T_tt :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  fromH0 ∘L resH0_deriv 1 1

private theorem T_st_eq_T_ts : T_st = T_ts := by
  have h : resH0_deriv 0 1 = resH0_deriv 1 0 := by
    ext1 f
    refine BesselPotentialSpace.ext ?_
    simp only [resH0_deriv, comp_apply, coe_restrictScalars',
      BesselPotentialSpace.toDistr_lineDerivCLM, BesselPotentialSpace.toDistr_inclusion]
    exact TemperedDistribution.lineDerivOp_comm _ (b₂ 0) (b₂ 1)
  rw [T_st, T_ts, h]

private theorem neg_T_ss_add_T_tt_add_T_val :
    -(T_ss + T_tt) + T_val =
      ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume : Measure (ℝ × ℝ))) := by
  ext1 f
  set g : Lp ℂ 2 (volume : Measure E₂) :=
    Lp.ofRealLI ℂ 2 (volume : Measure E₂) ((planeEquiv ℝ).symm f)
  set gH0 : H^{0}(E₂, ℂ) := (BesselPotentialSpace.toLpₗᵢ E₂ ℂ 0 2).symm g
  have hgH0 : gH0.toDistr = (g : 𝓢'(E₂, ℂ)) := by
    rw [← BesselPotentialSpace.toTemperedDistribution_toLp_zero]
    simp [gH0]
  have h0 : -(resH0_deriv 0 0 f + resH0_deriv 1 1 f) +
      BesselPotentialSpace.inclusion zero_le_one (resH1_val f) = gH0 := by
    refine BesselPotentialSpace.ext ?_
    have hlap : (resH0_deriv 0 0 f + resH0_deriv 1 1 f).toDistr = Δ (resH2 f).toDistr := by
      rw [BesselPotentialSpace.toDistr_add, TemperedDistribution.laplacian_eq_sum b₂,
        Fin.sum_univ_two]
      simp [resH0_deriv]
    rw [BesselPotentialSpace.toDistr_add, BesselPotentialSpace.toDistr_neg, hlap,
      resH1_val, comp_apply, coe_restrictScalars', BesselPotentialSpace.toDistr_inclusion,
      BesselPotentialSpace.toDistr_inclusion, toDistr_resH2, hgH0]
    simpa [one_smul] using
      TemperedDistribution.neg_laplacian_laplacianResolvent_add_smul (E := E₂) (F := ℂ) one_pos
        (g : 𝓢'(E₂, ℂ))
  have h1 := congrArg fromH0 h0
  rw [map_add, map_neg, map_add, ← fromH1_eq_fromH0_inclusion] at h1
  have hlp : gH0.toLp = g :=
    (BesselPotentialSpace.toLpₗᵢ_apply gH0).symm.trans
      ((BesselPotentialSpace.toLpₗᵢ E₂ ℂ 0 2).apply_symm_apply g)
  have hfrom : fromH0 gH0 = f := by
    rw [fromH0, comp_apply, comp_apply, coe_restrictScalars',
      BesselPotentialSpace.inclusionLp_zero, hlp]
    simp [g]
  simpa [T_ss, T_tt, T_val, hfrom] using h1

private theorem ae_fromH1 {u : H^{1}(E₂, ℂ)} {F : E₂ → ℂ}
    (hu : ⇑(BesselPotentialSpace.inclusionLp zero_le_one u) =ᵐ[volume] F) :
    ⇑(fromH1 u) =ᵐ[volume] fun z ↦ Complex.re (F (e₂.symm z)) := by
  have hu_re : (fun y ↦ RCLike.re (BesselPotentialSpace.inclusionLp zero_le_one u y))
      =ᵐ[volume] fun y ↦ Complex.re (F y) :=
    hu.mono fun y hy ↦ by dsimp only; rw [hy, RCLike.re_eq_complex_re]
  have hre : ⇑(Lp.reCLM ℂ 2 (volume : Measure E₂)
      (BesselPotentialSpace.inclusionLp zero_le_one u)) =ᵐ[volume] fun y ↦ Complex.re (F y) :=
    (Lp.coeFn_reCLM _).trans hu_re
  exact ((coeFn_planeEquiv _).trans (he₂_symm.quasiMeasurePreserving.ae_eq_comp hre)).trans
    (.of_forall fun _ ↦ rfl)

private theorem ae_fromH0 {u : H^{0}(E₂, ℂ)} {F : E₂ → ℂ}
    (hu : ⇑(BesselPotentialSpace.inclusionLp le_rfl u) =ᵐ[volume] F) :
    ⇑(fromH0 u) =ᵐ[volume] fun z ↦ Complex.re (F (e₂.symm z)) := by
  have hu_re : (fun y ↦ RCLike.re (BesselPotentialSpace.inclusionLp le_rfl u y))
      =ᵐ[volume] fun y ↦ Complex.re (F y) :=
    hu.mono fun y hy ↦ by dsimp only; rw [hy, RCLike.re_eq_complex_re]
  have hre : ⇑(Lp.reCLM ℂ 2 (volume : Measure E₂)
      (BesselPotentialSpace.inclusionLp le_rfl u)) =ᵐ[volume] fun y ↦ Complex.re (F y) :=
    (Lp.coeFn_reCLM _).trans hu_re
  exact ((coeFn_planeEquiv _).trans (he₂_symm.quasiMeasurePreserving.ae_eq_comp hre)).trans
    (.of_forall fun _ ↦ rfl)

private theorem re_fderiv_postcomp {F : E₂ → ℂ} (hF : Differentiable ℝ F) (y v : E₂) :
    Complex.re (fderiv ℝ F y v) = fderiv ℝ (fun x ↦ Complex.re (F x)) y v := by
  have hfd : HasFDerivAt (fun x ↦ Complex.re (F x))
      (Complex.reCLM.comp (fderiv ℝ F y)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hF y).hasFDerivAt
  simpa using (congrFun (congrArg DFunLike.coe hfd.fderiv) v).symm

private theorem schwartz_resH2_eq (φ : 𝓢(E₂, ℝ)) :
    resH2 (planeEquiv ℝ (φ.toLp 2)) =
      SchwartzMap.toBesselPotentialSpaceCLM ((0 : ℝ) - 2 * (-1)) 2
        (SchwartzMap.laplacianResolvent 1 (φ.postcompCLM Complex.ofRealCLM)) := by
  set φℂ : 𝓢(E₂, ℂ) := φ.postcompCLM Complex.ofRealCLM
  have hφℂ : Lp.ofRealLI ℂ 2 (volume : Measure E₂) ((planeEquiv ℝ).symm
      (planeEquiv ℝ (φ.toLp 2))) = φℂ.toLp 2 := by
    rw [LinearIsometryEquiv.symm_apply_apply]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_ofRealLI (𝕜 := ℂ) (φ.toLp 2), SchwartzMap.coeFn_toLp φ 2 volume,
      SchwartzMap.coeFn_toLp φℂ 2 volume] with y h₁ h₂ h₃
    simp [h₁, h₂, h₃, φℂ]
  refine BesselPotentialSpace.ext ?_
  rw [toDistr_resH2, hφℂ, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.laplacianResolvent_toTemperedDistributionCLM_eq one_pos φℂ

private theorem schwartz_T_first_ae (φ : 𝓢(E₂, ℝ)) :
    let ζ : 𝓢(E₂, ℝ) := (SchwartzMap.laplacianResolvent 1
      (φ.postcompCLM Complex.ofRealCLM)).postcompCLM Complex.reCLM
    let ψ : ℝ × ℝ → ℝ := ζ ∘ e₂.symm
    T_val (planeEquiv ℝ (φ.toLp 2)) =ᵐ[volume] ψ ∧
      T_s (planeEquiv ℝ (φ.toLp 2)) =ᵐ[volume] (fun z ↦ fderiv ℝ ψ z (1, 0)) ∧
      T_t (planeEquiv ℝ (φ.toLp 2)) =ᵐ[volume] (fun z ↦ fderiv ℝ ψ z (0, 1)) := by
  set ζℂ : 𝓢(E₂, ℂ) := SchwartzMap.laplacianResolvent 1 (φ.postcompCLM Complex.ofRealCLM)
  set ζ : 𝓢(E₂, ℝ) := ζℂ.postcompCLM Complex.reCLM
  set ψ : ℝ × ℝ → ℝ := ζ ∘ e₂.symm
  have hres := schwartz_resH2_eq φ
  have hvalH1 : resH1_val (planeEquiv ℝ (φ.toLp 2)) =
      SchwartzMap.toBesselPotentialSpaceCLM 1 2 ζℂ := by
    rw [resH1_val, comp_apply, coe_restrictScalars', hres,
      BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]
  have hinc1 : (BesselPotentialSpace.inclusion (by norm_num : ((1 : ℝ) + 1) ≤ 0 - 2 * (-1))
      (resH2 (planeEquiv ℝ (φ.toLp 2)))) =
      SchwartzMap.toBesselPotentialSpaceCLM ((1 : ℝ) + 1) 2 ζℂ := by
    rw [hres, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]
  have hinc2a : ⇑(BesselPotentialSpace.inclusionLp (by norm_num : (0 : ℝ) ≤ 1 + 1)
      (BesselPotentialSpace.inclusion (by norm_num : ((1 : ℝ) + 1) ≤ 0 - 2 * (-1))
        (resH2 (planeEquiv ℝ (φ.toLp 2))))) =ᵐ[volume] ⇑ζℂ := by
    rw [hinc1, BesselPotentialSpace.inclusionLp_toBesselPotentialSpaceCLM]
    exact SchwartzMap.coeFn_toLp ζℂ 2 volume
  have hζℂd : Differentiable ℝ (ζℂ : E₂ → ℂ) :=
    (ζℂ.smooth 1).differentiable one_ne_zero
  have hζd : Differentiable ℝ (ζ : E₂ → ℝ) := (ζ.smooth 1).differentiable one_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · have hvalLp : ⇑(BesselPotentialSpace.inclusionLp zero_le_one
        (resH1_val (planeEquiv ℝ (φ.toLp 2)))) =ᵐ[volume] ⇑ζℂ := by
      rw [hvalH1, BesselPotentialSpace.inclusionLp_toBesselPotentialSpaceCLM]
      exact SchwartzMap.coeFn_toLp ζℂ 2 volume
    exact ae_fromH1 hvalLp
  · have hsH1 := BesselPotentialSpace.coeFn_inclusionLp_lineDerivCLM_ae_eq_fderiv
      ENNReal.one_lt_two ENNReal.ofNat_ne_top zero_le_one (ζℂ.smooth 1) hinc2a (b₂ 0)
    refine (ae_fromH1 hsH1).trans (.of_forall fun z ↦ ?_)
    dsimp only
    rw [re_fderiv_postcomp hζℂd, show (fun x ↦ Complex.re (ζℂ x)) = ζ from rfl,
      fderiv_comp_e₂_symm_fst hζd]
  · have htH1 := BesselPotentialSpace.coeFn_inclusionLp_lineDerivCLM_ae_eq_fderiv
      ENNReal.one_lt_two ENNReal.ofNat_ne_top zero_le_one (ζℂ.smooth 1) hinc2a (b₂ 1)
    refine (ae_fromH1 htH1).trans (.of_forall fun z ↦ ?_)
    dsimp only
    rw [re_fderiv_postcomp hζℂd, show (fun x ↦ Complex.re (ζℂ x)) = ζ from rfl,
      fderiv_comp_e₂_symm_snd hζd]

private theorem schwartz_T_second_ae (φ : 𝓢(E₂, ℝ)) :
    let ζ : 𝓢(E₂, ℝ) := (SchwartzMap.laplacianResolvent 1
      (φ.postcompCLM Complex.ofRealCLM)).postcompCLM Complex.reCLM
    let ψ : ℝ × ℝ → ℝ := ζ ∘ e₂.symm
    T_ss (planeEquiv ℝ (φ.toLp 2)) =ᵐ[volume]
        (fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ ψ w (1, 0)) z (1, 0)) ∧
      T_st (planeEquiv ℝ (φ.toLp 2)) =ᵐ[volume]
        (fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ ψ w (0, 1)) z (1, 0)) ∧
      T_ts (planeEquiv ℝ (φ.toLp 2)) =ᵐ[volume]
        (fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ ψ w (1, 0)) z (0, 1)) ∧
      T_tt (planeEquiv ℝ (φ.toLp 2)) =ᵐ[volume]
        (fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ ψ w (0, 1)) z (0, 1)) := by
  set ζℂ : 𝓢(E₂, ℂ) := SchwartzMap.laplacianResolvent 1 (φ.postcompCLM Complex.ofRealCLM)
  set ζ : 𝓢(E₂, ℝ) := ζℂ.postcompCLM Complex.reCLM
  set ψ : ℝ × ℝ → ℝ := ζ ∘ e₂.symm
  have hinc0 :
      (BesselPotentialSpace.inclusion (by norm_num : (((0 : ℝ) + 1) + 1) ≤ 0 - 2 * (-1))
        (resH2 (planeEquiv ℝ (φ.toLp 2)))) =
      SchwartzMap.toBesselPotentialSpaceCLM (((0 : ℝ) + 1) + 1) 2 ζℂ := by
    rw [schwartz_resH2_eq φ, BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM]
  have hinc2b : ⇑(BesselPotentialSpace.inclusionLp (by norm_num : (0 : ℝ) ≤ (0 + 1) + 1)
      (BesselPotentialSpace.inclusion (by norm_num : (((0 : ℝ) + 1) + 1) ≤ 0 - 2 * (-1))
        (resH2 (planeEquiv ℝ (φ.toLp 2))))) =ᵐ[volume] ⇑ζℂ := by
    rw [hinc0, BesselPotentialSpace.inclusionLp_toBesselPotentialSpaceCLM]
    exact SchwartzMap.coeFn_toLp ζℂ 2 volume
  have h2H0 (i j : Fin 2) : ⇑(BesselPotentialSpace.inclusionLp le_rfl
      (resH0_deriv i j (planeEquiv ℝ (φ.toLp 2)))) =ᵐ[volume]
      fun y ↦ fderiv ℝ (fun w ↦ fderiv ℝ ζℂ w (b₂ j)) y (b₂ i) := by
    have hin := BesselPotentialSpace.coeFn_inclusionLp_lineDerivCLM_ae_eq_fderiv
      ENNReal.one_lt_two ENNReal.ofNat_ne_top (s := (0 : ℝ) + 1) (by norm_num)
      (ζℂ.smooth 1) hinc2b (b₂ j)
    have hcd : ContDiff ℝ 1 fun w ↦ fderiv ℝ ζℂ w (b₂ j) :=
      ((ζℂ.smooth 2).fderiv_right (by norm_num)).clm_apply contDiff_const
    exact BesselPotentialSpace.coeFn_inclusionLp_lineDerivCLM_ae_eq_fderiv
      ENNReal.one_lt_two ENNReal.ofNat_ne_top le_rfl hcd hin (b₂ i)
  have hζℂd : Differentiable ℝ (ζℂ : E₂ → ℂ) :=
    (ζℂ.smooth 1).differentiable one_ne_zero
  have hζd : Differentiable ℝ (ζ : E₂ → ℝ) := (ζ.smooth 1).differentiable one_ne_zero
  have hζℂd2 (j : Fin 2) : Differentiable ℝ (fun w ↦ fderiv ℝ ζℂ w (b₂ j)) :=
    (((ζℂ.smooth 2).fderiv_right (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero
  have hζd2 (j : Fin 2) : Differentiable ℝ (fun w ↦ fderiv ℝ ζ w (b₂ j)) :=
    (((ζ.smooth 2).fderiv_right (by norm_num)).clm_apply contDiff_const).differentiable one_ne_zero
  have hre2 (j : Fin 2) : (fun x ↦ Complex.re (fderiv ℝ ζℂ x (b₂ j))) =
      fun x ↦ fderiv ℝ ζ x (b₂ j) :=
    funext fun x ↦ re_fderiv_postcomp hζℂd x (b₂ j)
  have hψs :
      (fun w ↦ fderiv ℝ ψ w (1, 0)) = (fun y ↦ fderiv ℝ ζ y (b₂ 0)) ∘ e₂.symm :=
    funext fun w ↦ fderiv_comp_e₂_symm_fst hζd w
  have hψt :
      (fun w ↦ fderiv ℝ ψ w (0, 1)) = (fun y ↦ fderiv ℝ ζ y (b₂ 1)) ∘ e₂.symm :=
    funext fun w ↦ fderiv_comp_e₂_symm_snd hζd w
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (ae_fromH0 (h2H0 0 0)).trans (.of_forall fun z ↦ ?_)
    dsimp only
    rw [re_fderiv_postcomp (hζℂd2 0), hre2 0, hψs, fderiv_comp_e₂_symm_fst (hζd2 0)]
  · refine (ae_fromH0 (h2H0 0 1)).trans (.of_forall fun z ↦ ?_)
    dsimp only
    rw [re_fderiv_postcomp (hζℂd2 1), hre2 1, hψt, fderiv_comp_e₂_symm_fst (hζd2 1)]
  · refine (ae_fromH0 (h2H0 1 0)).trans (.of_forall fun z ↦ ?_)
    dsimp only
    rw [re_fderiv_postcomp (hζℂd2 0), hre2 0, hψs, fderiv_comp_e₂_symm_snd (hζd2 0)]
  · refine (ae_fromH0 (h2H0 1 1)).trans (.of_forall fun z ↦ ?_)
    dsimp only
    rw [re_fderiv_postcomp (hζℂd2 1), hre2 1, hψt, fderiv_comp_e₂_symm_snd (hζd2 1)]

/-- Any continuous compactly supported map on `ℝ × ℝ` lies in `L∞(ℝ × ℝ)`. -/
theorem memLp_top_of_continuous_of_hasCompactSupport {W : Type*} [NormedAddCommGroup W]
    {f : ℝ × ℝ → W} (hf : Continuous f) (hfc : HasCompactSupport f) :
    MemLp f ∞ (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨C, hC⟩ := hfc.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine memLp_top_of_bound hf.aestronglyMeasurable (max C 0) (.of_forall fun z ↦ ?_)
  by_cases hz : z ∈ tsupport f
  · exact (hC z hz).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact le_max_right _ _

private theorem isCompactOperator_multiplicationOperator_comp_fromH1 {χ₀ : ℝ × ℝ → ℝ}
    (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀) (hχ₀c : HasCompactSupport χ₀) :
    IsCompactOperator
      (Lp.multiplicationOperator (E := ℝ) (p := 2)
        ((memLp_top_of_continuous_of_hasCompactSupport hχ₀.continuous hχ₀c).toLp χ₀) ∘L
        fromH1) := by
  have hχR_cd : ContDiff ℝ (⊤ : ℕ∞) (χ₀ ∘ e₂) := by
    rw [← e₂CLE_coe]
    exact hχ₀.comp e₂CLE.contDiff
  have hχR_supp : HasCompactSupport (χ₀ ∘ e₂) := by
    rw [← e₂CLE_coe]
    exact hχ₀c.comp_homeomorph e₂CLE.toHomeomorph
  set χR : 𝓢(E₂, ℝ) := hχR_supp.toSchwartzMap hχR_cd
  set χC : 𝓢(E₂, ℂ) := χR.postcompCLM Complex.ofRealCLM
  have hχR_fun : (χR : E₂ → ℝ) = χ₀ ∘ e₂ :=
    funext (hχR_supp.toSchwartzMap_toFun hχR_cd)
  have hχC_fun : (χC : E₂ → ℂ) = fun y ↦ ((χ₀ (e₂ y) : ℝ) : ℂ) := by
    ext y
    simp [χC, hχR_fun]
  have hχ₀_mem : MemLp χ₀ ∞ (volume : Measure (ℝ × ℝ)) :=
    memLp_top_of_continuous_of_hasCompactSupport hχ₀.continuous hχ₀c
  set A : H^{1}(E₂, ℂ) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
    Lp.multiplicationOperator (hχ₀_mem.toLp χ₀) ∘L fromH1
  set B : H^{1}(E₂, ℂ) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
    fromH0 ∘L
      (BesselPotentialSpace.inclusion (by norm_num : (0 : ℝ) ≤ 1) ∘L
        BesselPotentialSpace.smulLeftCLM 1 χC).restrictScalars ℝ
  have hAB : A = B := by
    have hdense :=
      SchwartzMap.denseRange_toBesselPotentialSpaceCLM (E := E₂) (F := ℂ) (p := 2) 1
        ENNReal.ofNat_ne_top
    refine ContinuousLinearMap.ext fun v ↦
      hdense.induction_on v (isClosed_eq A.continuous B.continuous) fun u ↦ ?_
    refine Lp.ext ?_
    have hu : (BesselPotentialSpace.inclusion (by norm_num : (0 : ℝ) ≤ 1)
        (BesselPotentialSpace.smulLeftCLM 1 χC
          (SchwartzMap.toBesselPotentialSpaceCLM 1 2 u))) =
        SchwartzMap.toBesselPotentialSpaceCLM 0 2
          (SchwartzMap.smulLeftCLM ℂ (χC : E₂ → ℂ) u) := by
      refine BesselPotentialSpace.ext ?_
      rw [BesselPotentialSpace.toDistr_inclusion, BesselPotentialSpace.toDistr_smulLeftCLM,
        SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
        SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
        TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq]
    have hA_ae : ⇑(A (SchwartzMap.toBesselPotentialSpaceCLM 1 2 u)) =ᵐ[volume]
        fun z ↦ χ₀ z * Complex.re (u (e₂.symm z)) := by
      have h1 := Lp.multiplicationOperator_ae (hχ₀_mem.toLp χ₀)
        (fromH1 (SchwartzMap.toBesselPotentialSpaceCLM 1 2 u))
      have h2 := hχ₀_mem.coeFn_toLp
      have h5 : ⇑(BesselPotentialSpace.inclusionLp zero_le_one
          (SchwartzMap.toBesselPotentialSpaceCLM 1 2 u)) =ᵐ[volume] ⇑u := by
        rw [BesselPotentialSpace.inclusionLp_toBesselPotentialSpaceCLM]
        exact SchwartzMap.coeFn_toLp u 2 volume
      have h345 := ae_fromH1 h5
      filter_upwards [h1, h2, h345] with z hz1 hz2 hz3
      dsimp only [A, comp_apply]
      rw [hz1, hz2, hz3, smul_eq_mul]
    have hB_ae : ⇑(B (SchwartzMap.toBesselPotentialSpaceCLM 1 2 u)) =ᵐ[volume]
        fun z ↦ χ₀ z * Complex.re (u (e₂.symm z)) := by
      have h3 : ⇑(BesselPotentialSpace.inclusionLp le_rfl
          (BesselPotentialSpace.inclusion zero_le_one
            (BesselPotentialSpace.smulLeftCLM 1 χC (SchwartzMap.toBesselPotentialSpaceCLM 1 2 u))))
          =ᵐ[volume] fun y ↦ χC y * u y := by
        rw [hu, BesselPotentialSpace.inclusionLp_toBesselPotentialSpaceCLM]
        exact (SchwartzMap.coeFn_toLp _ 2 volume).trans (.of_forall fun y ↦
          SchwartzMap.smulLeftCLM_apply_apply χC.hasTemperateGrowth u y)
      refine (ae_fromH0 h3).mono fun z hz ↦ ?_
      dsimp only [B, comp_apply, coe_restrictScalars'] at hz ⊢
      rw [hz, hχC_fun]
      simp [Complex.ofReal_re]
    exact hA_ae.trans hB_ae.symm
  change IsCompactOperator A
  rw [hAB]
  exact (BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM (E := E₂) (F := ℂ)
    χC zero_lt_one).clm_comp fromH0

end ScalarPlane

section VectorParametrix

/-! ### Vector lift and frozen-coefficient parametrix -/

private theorem zero_compLpL {W₁ W₂ : Type*} [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]
    [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] :
    (0 : W₁ →L[ℝ] W₂).compLpL 2 (volume : Measure (ℝ × ℝ)) = 0 := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [(0 : W₁ →L[ℝ] W₂).coeFn_compLpL f,
    Lp.coeFn_zero (E := W₂) (p := 2) (μ := (volume : Measure (ℝ × ℝ)))] with z hz1 hz2
  rw [hz1, zero_apply, zero_apply, hz2, Pi.zero_apply]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable (V) in
/-- Coordinatewise lift of a bounded scalar operator
`T : L²(ℝ × ℝ, ℝ) →L[ℝ] L²(ℝ × ℝ, ℝ)`
to `L²(ℝ × ℝ, V)` via `Module.finBasis ℝ V`. -/
noncomputable def liftOp
    (T : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (ℝ × ℝ))) :
    Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 (volume : Measure (ℝ × ℝ)) :=
  let b := Module.finBasis ℝ V
  ∑ i, ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2
      (volume : Measure (ℝ × ℝ))).comp
    (T.comp ((b.coord i).toContinuousLinearMap.compLpL 2 (volume : Measure (ℝ × ℝ))))

private theorem liftOp_add
    (S T : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (ℝ × ℝ))) :
    liftOp V (S + T) = liftOp V S + liftOp V T := by
  simp [liftOp, comp_add, add_comp, Finset.sum_add_distrib]

private theorem liftOp_neg
    (T : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (ℝ × ℝ))) :
    liftOp V (-T) = -liftOp V T := by
  simp [liftOp, comp_neg, neg_comp, Finset.sum_neg_distrib]

private theorem liftOp_id :
    liftOp V (ContinuousLinearMap.id ℝ _) = ContinuousLinearMap.id ℝ _ := by
  ext1 f
  simpa [liftOp] using (TauCeti.eq_sum_basis_compLpL (Module.finBasis ℝ V) f).symm

/-- Compactness of multiplying `liftOp V (fromH1 ∘L H)` on the left by a smooth compactly
supported cutoff `χ₀`. -/
theorem multiplicationOperator_comp_liftOp_fromH1
    {χ₀ : ℝ × ℝ → ℝ} (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀)
    (hχ₀c : HasCompactSupport χ₀)
    (H : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ]
      H^{1}(EuclideanSpace ℝ (Fin 2), ℂ)) :
    IsCompactOperator
      (Lp.multiplicationOperator (E := V) (p := 2)
          ((memLp_top_of_continuous_of_hasCompactSupport hχ₀.continuous hχ₀c).toLp χ₀) ∘L
        liftOp V (fromH1 ∘L H)) := by
  set a := (memLp_top_of_continuous_of_hasCompactSupport hχ₀.continuous hχ₀c).toLp χ₀
  set b := Module.finBasis ℝ V
  have hcomp : Lp.multiplicationOperator (E := V) (p := 2) a ∘L liftOp V (fromH1 ∘L H) =
      ∑ i, ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 volume).comp
        (((Lp.multiplicationOperator (E := ℝ) (p := 2) a ∘L fromH1) ∘L H).comp
          ((b.coord i).toContinuousLinearMap.compLpL 2 volume)) := by
    ext1 f
    rw [comp_apply, liftOp, sum_apply, map_sum, sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [comp_apply]
    exact (ContinuousLinearMap.compLpL_multiplicationOperator _ a _).symm
  rw [hcomp]
  refine Finset.sum_induction _
    (fun (op : Lp V 2 volume →L[ℝ] Lp V 2 volume) ↦ IsCompactOperator op)
    (fun _ _ ha hb ↦ ha.add hb) isCompactOperator_zero fun i _ ↦ ?_
  have h1 := isCompactOperator_multiplicationOperator_comp_fromH1 hχ₀ hχ₀c
  exact ((h1.comp_clm H).comp_clm
    ((b.coord i).toContinuousLinearMap.compLpL 2 volume)).clm_comp
    ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 volume)

variable (V) in
/-- Value component `-(T_s - J₀ T_t)` of the frozen-coefficient parametrix on
`L²(ℝ × ℝ, V)`. -/
noncomputable def P_val (J₀ : V →L[ℝ] V) :
    Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 (volume : Measure (ℝ × ℝ)) :=
  -(liftOp V T_s - (J₀.compLpL 2 (volume : Measure (ℝ × ℝ))).comp (liftOp V T_t))

variable (V) in
/-- First `s`-derivative component `-(T_ss - J₀ T_ts)` of the frozen-coefficient parametrix. -/
noncomputable def P_s (J₀ : V →L[ℝ] V) :
    Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 (volume : Measure (ℝ × ℝ)) :=
  -(liftOp V T_ss - (J₀.compLpL 2 (volume : Measure (ℝ × ℝ))).comp (liftOp V T_ts))

variable (V) in
/-- First `t`-derivative component `-(T_st - J₀ T_tt)` of the frozen-coefficient parametrix. -/
noncomputable def P_t (J₀ : V →L[ℝ] V) :
    Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 (volume : Measure (ℝ × ℝ)) :=
  -(liftOp V T_st - (J₀.compLpL 2 (volume : Measure (ℝ × ℝ))).comp (liftOp V T_tt))

/-- When `J₀² = -id`, the frozen-coefficient parametrix solves
`P_s + J₀ P_t = id - liftOp V T_val`. -/
theorem P_s_add_compLpL_P_t {J₀ : V →L[ℝ] V}
    (hJ₀ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ V) :
    P_s V J₀ + (J₀.compLpL 2 (volume : Measure (ℝ × ℝ))).comp (P_t V J₀) =
      ContinuousLinearMap.id ℝ _ - liftOp V T_val := by
  have hJ₀L : (J₀.compLpL 2 (volume : Measure (ℝ × ℝ))).comp
      (J₀.compLpL 2 (volume : Measure (ℝ × ℝ))) =
      -ContinuousLinearMap.id ℝ (Lp V 2 (volume : Measure (ℝ × ℝ))) := by
    rw [ContinuousLinearMap.compLpL_comp_compLpL, hJ₀]
    ext1 f
    refine Lp.ext ?_
    filter_upwards [(-ContinuousLinearMap.id ℝ V).coeFn_compLpL (p := 2) (μ := volume) f,
      Lp.coeFn_neg f] with z hz1 hz2
    simp only [neg_apply, id_apply]
    rw [hz1, hz2, neg_apply, id_apply, Pi.neg_apply]
  have h1 : P_s V J₀ + (J₀.compLpL 2 volume).comp (P_t V J₀) =
      -(liftOp V T_ss + liftOp V T_tt) := by
    rw [P_s, P_t, comp_neg, comp_sub, ← comp_assoc, hJ₀L, neg_comp, id_comp, sub_neg_eq_add,
      T_st_eq_T_ts]
    abel
  rw [h1, ← liftOp_add]
  have h2 := congrArg (liftOp V) neg_T_ss_add_T_tt_add_T_val
  rw [liftOp_add, liftOp_neg, liftOp_id] at h2
  exact eq_sub_of_add_eq h2

/-- Multiplying `P_val V J₀` on the left by a smooth compactly supported cutoff `χ₀` yields a
compact operator on `L²(ℝ × ℝ, V)`. -/
theorem isCompactOperator_multiplicationOperator_comp_P_val
    {χ₀ : ℝ × ℝ → ℝ} (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀)
    (hχ₀c : HasCompactSupport χ₀) (J₀ : V →L[ℝ] V) :
    IsCompactOperator
      (Lp.multiplicationOperator (E := V) (p := 2)
          ((memLp_top_of_continuous_of_hasCompactSupport hχ₀.continuous hχ₀c).toLp χ₀) ∘L
        P_val V J₀) := by
  set a := (memLp_top_of_continuous_of_hasCompactSupport hχ₀.continuous hχ₀c).toLp χ₀
  have h1 : IsCompactOperator
      (Lp.multiplicationOperator (E := V) (p := 2) a ∘L liftOp V T_s) :=
    multiplicationOperator_comp_liftOp_fromH1 (V := V) hχ₀ hχ₀c (resH1_deriv 0)
  have h2 : IsCompactOperator
      (Lp.multiplicationOperator (E := V) (p := 2) a ∘L liftOp V T_t) :=
    multiplicationOperator_comp_liftOp_fromH1 (V := V) hχ₀ hχ₀c (resH1_deriv 1)
  have hcomm :
      Lp.multiplicationOperator (E := V) (p := 2) a ∘L
          J₀.compLpL 2 (volume : Measure (ℝ × ℝ)) =
        J₀.compLpL 2 (volume : Measure (ℝ × ℝ)) ∘L
          Lp.multiplicationOperator (E := V) (p := 2) a := by
    ext1 f
    exact (ContinuousLinearMap.compLpL_multiplicationOperator J₀ a f).symm
  have heq : Lp.multiplicationOperator (E := V) (p := 2) a ∘L P_val V J₀ =
      -(Lp.multiplicationOperator (E := V) (p := 2) a ∘L liftOp V T_s -
        (J₀.compLpL 2 (volume : Measure (ℝ × ℝ))).comp
          (Lp.multiplicationOperator (E := V) (p := 2) a ∘L liftOp V T_t)) := by
    rw [P_val, comp_neg, comp_sub, ← comp_assoc, hcomm, comp_assoc]
  rw [heq]
  exact (h1.sub (h2.clm_comp (J₀.compLpL 2 (volume : Measure (ℝ × ℝ))))).neg

/-- Multiplying `liftOp V T_val` on the left by a `C^∞` compactly supported function gives a
compact operator on `L²(ℝ × ℝ, V)`. -/
theorem isCompactOperator_multiplicationOperator_comp_liftOp_T_val {χ₀ : ℝ × ℝ → ℝ}
    (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀) (hχ₀c : HasCompactSupport χ₀) :
    IsCompactOperator
      (Lp.multiplicationOperator (E := V) (p := 2)
        ((memLp_top_of_continuous_of_hasCompactSupport hχ₀.continuous hχ₀c).toLp χ₀) ∘L
        liftOp V T_val) :=
  multiplicationOperator_comp_liftOp_fromH1 (V := V) hχ₀ hχ₀c resH1_val

/-- Pointwise bound `‖P_t V J₀ f z‖ ≤ ‖liftOp V T_st f z‖ + M_J ‖liftOp V T_tt f z‖`
a.e., uniform across all `J₀` with `‖J₀‖ ≤ M_J`. -/
theorem norm_P_t_apply_le {J₀ : V →L[ℝ] V} {M_J : ℝ} (hM : ‖J₀‖ ≤ M_J)
    (f : Lp V 2 (volume : Measure (ℝ × ℝ))) :
    ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      ‖P_t V J₀ f z‖ ≤ ‖liftOp V T_st f z‖ + M_J * ‖liftOp V T_tt f z‖ := by
  have h1 := Lp.coeFn_neg (liftOp V T_st f - J₀.compLpL 2 volume (liftOp V T_tt f))
  have h2 := Lp.coeFn_sub (liftOp V T_st f) (J₀.compLpL 2 volume (liftOp V T_tt f))
  have h3 := J₀.coeFn_compLpL (p := 2) (μ := (volume : Measure (ℝ × ℝ))) (liftOp V T_tt f)
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [P_t, neg_apply, sub_apply, comp_apply, hz1, Pi.neg_apply, hz2, Pi.sub_apply, hz3,
    norm_neg]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  exact (J₀.le_opNorm _).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

/-- On a Schwartz tuple `φ : Fin d → 𝓢(ℝ², ℝ)`, the triple `(P_val, P_s, P_t)` applied to
`∑ i, planeEquiv (φ i) • b_i` equals a.e. the jet `(ξ, ∂_s ξ, ∂_t ξ)` of a smooth map
`ξ`. -/
theorem schwartz_P_ae (J₀ : V →L[ℝ] V)
    (φ : Fin (Module.finrank ℝ V) → 𝓢(EuclideanSpace ℝ (Fin 2), ℝ)) :
    ∃ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ ∧
      let f₀ : Lp V 2 (volume : Measure (ℝ × ℝ)) :=
        ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Module.finBasis ℝ V i)).compLpL 2 volume
          (planeEquiv ℝ ((φ i).toLp 2))
      P_val V J₀ f₀ =ᵐ[volume] ξ ∧
        P_s V J₀ f₀ =ᵐ[volume] (fun z ↦ fderiv ℝ ξ z (1, 0)) ∧
        P_t V J₀ f₀ =ᵐ[volume] (fun z ↦ fderiv ℝ ξ z (0, 1)) := by
  let b := Module.finBasis ℝ V
  let f₀ : Lp V 2 (volume : Measure (ℝ × ℝ)) :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 volume
      (planeEquiv ℝ ((φ i).toLp 2))
  let ζs := fun i ↦ (SchwartzMap.laplacianResolvent 1
    ((φ i).postcompCLM Complex.ofRealCLM)).postcompCLM Complex.reCLM
  let ψs : Fin (Module.finrank ℝ V) → ℝ × ℝ → ℝ :=
    fun i ↦ (ζs i : E₂ → ℝ) ∘ e₂.symm
  have hψ_cd (i : Fin (Module.finrank ℝ V)) : ContDiff ℝ (⊤ : ℕ∞) (ψs i) := by
    have hcd := (ζs i).smooth (⊤ : ℕ∞)
    dsimp only [ψs]
    rw [← e₂CLE_symm_coe]
    exact hcd.comp e₂CLE.symm.contDiff
  let Ψ : ℝ × ℝ → V := fun z ↦ ∑ i, ψs i z • b i
  have hΨ_cd : ContDiff ℝ (⊤ : ℕ∞) Ψ :=
    ContDiff.sum fun i _ ↦ (hψ_cd i).smul contDiff_const
  let ξ : ℝ × ℝ → V := fun z ↦ -(fderiv ℝ Ψ z (1, 0) - J₀ (fderiv ℝ Ψ z (0, 1)))
  have hξ_cd : ContDiff ℝ (⊤ : ℕ∞) ξ :=
    (((hΨ_cd.fderiv_right (by simp)).clm_apply contDiff_const).sub
      (J₀.contDiff.comp ((hΨ_cd.fderiv_right (by simp)).clm_apply contDiff_const))).neg
  refine ⟨ξ, hξ_cd, ?_⟩
  have hT_ae (T : Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ]
        Lp ℝ 2 (volume : Measure (ℝ × ℝ)))
      {g : Fin (Module.finrank ℝ V) → ℝ × ℝ → ℝ}
      (hg : ∀ i, T (planeEquiv ℝ ((φ i).toLp 2)) =ᵐ[volume] g i) :
      liftOp V T f₀ =ᵐ[volume] fun z ↦ ∑ i, g i z • b i := by
    have hsum : liftOp V T f₀ =
        ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 volume
          (T (planeEquiv ℝ ((φ i).toLp 2))) := by
      dsimp only [f₀]
      rw [liftOp, sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hcoord : (b.coord i).toContinuousLinearMap.compLpL 2 volume
          (∑ j, (ContinuousLinearMap.toSpanSingleton ℝ (b j)).compLpL 2 volume
            (planeEquiv ℝ ((φ j).toLp 2))) = planeEquiv ℝ ((φ i).toLp 2) := by
        simp only [map_sum, ContinuousLinearMap.compLpL_compLpL]
        rw [Finset.sum_eq_single i]
        · have h1 : (b.coord i).toContinuousLinearMap.comp
              (ContinuousLinearMap.toSpanSingleton ℝ (b i)) = ContinuousLinearMap.id ℝ ℝ := by
            ext1; simp
          rw [h1, ContinuousLinearMap.id_compLpL, id_apply]
        · intro j _ hji
          have h0 : (b.coord i).toContinuousLinearMap.comp
              (ContinuousLinearMap.toSpanSingleton ℝ (b j)) = 0 := by
            ext1; simp [hji]
          rw [h0, zero_compLpL, zero_apply]
        · simp
      rw [comp_apply, comp_apply, hcoord]
    rw [hsum]
    refine (Lp.coeFn_finsetSum Finset.univ _).trans ?_
    have hterm : ∀ i, ⇑((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 volume
        (T (planeEquiv ℝ ((φ i).toLp 2)))) =ᵐ[volume] fun z ↦ g i z • b i := fun i ↦ by
      filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL
        (T (planeEquiv ℝ ((φ i).toLp 2))), hg i] with z hz1 hz2
      rw [hz1, hz2]
      rfl
    filter_upwards [ae_all_iff.2 hterm] with z hz
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ hz i
  have hS := hT_ae T_s fun i ↦ (schwartz_T_first_ae (φ i)).2.1
  have hT := hT_ae T_t fun i ↦ (schwartz_T_first_ae (φ i)).2.2
  have hSS := hT_ae T_ss fun i ↦ (schwartz_T_second_ae (φ i)).1
  have hST := hT_ae T_st fun i ↦ (schwartz_T_second_ae (φ i)).2.1
  have hTS := hT_ae T_ts fun i ↦ (schwartz_T_second_ae (φ i)).2.2.1
  have hTT := hT_ae T_tt fun i ↦ (schwartz_T_second_ae (φ i)).2.2.2
  have hΨ_deriv (z v : ℝ × ℝ) :
      fderiv ℝ Ψ z v = ∑ i, fderiv ℝ (ψs i) z v • b i := by
    have hfd : HasFDerivAt Ψ (∑ i, (fderiv ℝ (ψs i) z).smulRight (b i)) z :=
      HasFDerivAt.fun_sum fun i _ ↦
        ((hψ_cd i).differentiable (by simp) z).hasFDerivAt.smul_const (b i)
    simp [hfd.fderiv]
  have hξ_eq : (-((fun w ↦ ∑ i, fderiv ℝ (ψs i) w (1, 0) • b i) -
      fun w ↦ J₀ (∑ i, fderiv ℝ (ψs i) w (0, 1) • b i))) = ξ := by
    ext w
    simp [ξ, hΨ_deriv]
  have hξ_deriv (e z : ℝ × ℝ) :
      fderiv ℝ ξ z e = -(∑ i, fderiv ℝ (fun w ↦ fderiv ℝ (ψs i) w (1, 0)) z e • b i -
        J₀ (∑ i, fderiv ℝ (fun w ↦ fderiv ℝ (ψs i) w (0, 1)) z e • b i)) := by
    have hfd1 : HasFDerivAt (fun w ↦ ∑ i, fderiv ℝ (ψs i) w (1, 0) • b i)
        (∑ i, (fderiv ℝ (fun w ↦ fderiv ℝ (ψs i) w (1, 0)) z).smulRight (b i)) z :=
      HasFDerivAt.fun_sum fun i _ ↦
        ((((hψ_cd i).fderiv_right (m := 2) (by simp)).clm_apply contDiff_const).differentiable
          (by simp) z).hasFDerivAt.smul_const (b i)
    have hfd2 : HasFDerivAt (fun w ↦ J₀ (∑ i, fderiv ℝ (ψs i) w (0, 1) • b i))
        (J₀.comp (∑ i, (fderiv ℝ (fun w ↦ fderiv ℝ (ψs i) w (0, 1)) z).smulRight (b i)))
        z :=
      J₀.hasFDerivAt.comp z (HasFDerivAt.fun_sum fun i _ ↦
        ((((hψ_cd i).fderiv_right (m := 2) (by simp)).clm_apply contDiff_const).differentiable
          (by simp) z).hasFDerivAt.smul_const (b i))
    have hfd := (hfd1.sub hfd2).neg
    rw [hξ_eq] at hfd
    simpa using congrFun (congrArg DFunLike.coe hfd.fderiv) e
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_neg (liftOp V T_s f₀ - J₀.compLpL 2 volume (liftOp V T_t f₀)),
      Lp.coeFn_sub (liftOp V T_s f₀) (J₀.compLpL 2 volume (liftOp V T_t f₀)),
      J₀.coeFn_compLpL (p := 2) (μ := (volume : Measure (ℝ × ℝ))) (liftOp V T_t f₀),
      hS, hT] with z hz1 hz2 hz3 hz4 hz5
    rw [P_val, neg_apply, sub_apply, comp_apply, hz1, Pi.neg_apply, hz2, Pi.sub_apply, hz3,
      hz4, hz5]
    simp [ξ, hΨ_deriv, ψs, ζs]
  · have hST' : liftOp V T_ts f₀ =ᵐ[volume]
        fun z ↦ ∑ i, fderiv ℝ (fun w ↦ fderiv ℝ (ψs i) w (0, 1)) z (1, 0) • b i := by
      rw [← T_st_eq_T_ts]; exact hST
    filter_upwards [Lp.coeFn_neg (liftOp V T_ss f₀ - J₀.compLpL 2 volume (liftOp V T_ts f₀)),
      Lp.coeFn_sub (liftOp V T_ss f₀) (J₀.compLpL 2 volume (liftOp V T_ts f₀)),
      J₀.coeFn_compLpL (p := 2) (μ := (volume : Measure (ℝ × ℝ))) (liftOp V T_ts f₀),
      hSS, hST'] with z hz1 hz2 hz3 hz4 hz5
    rw [P_s, neg_apply, sub_apply, comp_apply, hz1, Pi.neg_apply, hz2, Pi.sub_apply, hz3,
      hz4, hz5, hξ_deriv]
  · have hTS' : liftOp V T_st f₀ =ᵐ[volume]
        fun z ↦ ∑ i, fderiv ℝ (fun w ↦ fderiv ℝ (ψs i) w (1, 0)) z (0, 1) • b i := by
      rw [T_st_eq_T_ts]; exact hTS
    filter_upwards [Lp.coeFn_neg (liftOp V T_st f₀ - J₀.compLpL 2 volume (liftOp V T_tt f₀)),
      Lp.coeFn_sub (liftOp V T_st f₀) (J₀.compLpL 2 volume (liftOp V T_tt f₀)),
      J₀.coeFn_compLpL (p := 2) (μ := (volume : Measure (ℝ × ℝ))) (liftOp V T_tt f₀),
      hTS', hTT] with z hz1 hz2 hz3 hz4 hz5
    rw [P_t, neg_apply, sub_apply, comp_apply, hz1, Pi.neg_apply, hz2, Pi.sub_apply, hz3,
      hz4, hz5, hξ_deriv]

end VectorParametrix

end TauCeti.ConformalSobolev.PlaneResolvent
