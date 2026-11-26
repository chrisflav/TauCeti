/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Conformal

import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.PlaneResolvent
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.MeasureTheory.Function.Lp.Multiplication

/-!
# Local right parametrix on compact subsets of a conformal planar domain

Let `U ⊆ ℝ × ℝ` be an open set with conformal weight `ρ` (`IsWeight`), and let
`D = ∂s + J(z) ∂t + C(z)` be a first-order Cauchy--Riemann operator with `J` continuous on `U`
satisfying `J(z)² = -id` and `C` essentially bounded on `U`. Given any `C²` compactly supported
cutoff `β₀` with `tsupport β₀ ⊆ U` and tolerance `ε > 0`, this file constructs a bounded
operator `P : L²(U, V) → W^{1,2}_0(U, V)` (`TauCeti.ConformalSobolev.H1`) such that
`D ∘ P = β₀ • id + K + E` with `K` compact and `‖E‖ ≤ ε`
(`TauCeti.ConformalSobolev.exists_jetOperator_firstOrderJetCoeff_comp_eq_smul_add`).

In the Fredholm theory of the linearized Floer operator on the pair of pants `S = ℂ ∖ {0, 1}`,
this supplies the interior piece of a right parametrix on `S`: after splicing the local
parametrices of the three cylindrical ends, the remaining compact core is handled by choosing
`β₀ = 1 - ∑_q β_q`.

## Construction

1. **Localization and Rellich compactness.** Using the planar resolvent operators from
   `PlaneResolvent`, multiplying by a `C²` compactly supported cutoff `β` with `tsupport β ⊆ U`
   sends `(P_val, P_s, P_t)` into `H1 V U ρ`, verified by density of Schwartz functions on `ℝ²`.
   Every zeroth-order error (`∂s β • P_val`, `∂t β • J P_val`, `β √ρ C P_val`,
   `β U_val`) factors through multiplication by a compactly supported smooth function
   on `H¹(ℝ²)`, hence is compact by Rellich's theorem.
2. **Freezing coefficients via a lattice partition.** Cover `tsupport β₀` by a fine grid
   partition of scale `δ` built from `TauCeti.latticeBump₁`, freezing `J` at grid centers
   `z_k ∈ U`. Since the operators `U_st`, `U_tt` are independent of `k` and the partition weights
   are nonnegative and sum to at most `1`, the variable-coefficient error
   `∑_k γ_k(z) (J(z) - J(z_k)) P_t(J(z_k)) h(z)` has `L²` norm bounded independently of `δ` and
   of the number of grid cells, hence is at most `ε` for `δ` small enough by uniform continuity
   of `J` on a compact neighborhood of `tsupport β₀`.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real ContinuousLinearMap
open scoped ENNReal NNReal SchwartzMap

namespace TauCeti.ConformalSobolev

open PlaneResolvent

section LocalParametrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private noncomputable def cutoffCoeff (ρ β : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    V × V × V →L[ℝ] V × V × V :=
  (√(ρ z) * β z) • ((ContinuousLinearMap.inl ℝ V (V × V)).comp
      (ContinuousLinearMap.fst ℝ V (V × V))) +
    ((ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inl ℝ V V)).comp
      (β z • ((ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))) +
        fderiv ℝ β z (1, 0) • ContinuousLinearMap.fst ℝ V (V × V)) +
    ((ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inr ℝ V V)).comp
      (β z • ((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))) +
        fderiv ℝ β z (0, 1) • ContinuousLinearMap.fst ℝ V (V × V))

omit [FiniteDimensional ℝ V] in
private theorem cutoffCoeff_apply (ρ β : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (p : V × V × V) :
    cutoffCoeff ρ β z p =
      ((√(ρ z) * β z) • p.1,
        β z • p.2.1 + fderiv ℝ β z (1, 0) • p.1,
        β z • p.2.2 + fderiv ℝ β z (0, 1) • p.1) := by
  ext <;> simp [cutoffCoeff]

omit [FiniteDimensional ℝ V] in
private theorem memLp_cutoffCoeff {U : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
    (hρ : IsWeight U ρ) {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ U) :
    MemLp (cutoffCoeff (V := V) ρ β) ∞ (volume.restrict U) := by
  have hsqrt : Continuous fun z ↦ √(ρ z) * β z :=
    (hρ.continuousOn.sqrt.mul hβ.continuous.continuousOn).continuous_of_tsupport_subset
      hρ.isOpen ((tsupport_mul_subset_right (f := fun z ↦ √(ρ z)) (g := β)).trans hβU)
  have hcont : Continuous (cutoffCoeff (V := V) ρ β) := by
    have hd := hβ.continuous_fderiv (by norm_num)
    unfold cutoffCoeff
    fun_prop
  have hsupp : HasCompactSupport (cutoffCoeff (V := V) ρ β) := by
    refine HasCompactSupport.of_support_subset_isCompact hβc.isCompact fun z hz ↦
      by_contra fun hnot ↦ hz ?_
    have hev : β =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hnot
    refine ContinuousLinearMap.ext fun p ↦ ?_
    simp [cutoffCoeff_apply, hev.eq_of_nhds, hev.fderiv_eq]
  exact (memLp_top_of_continuous_of_hasCompactSupport hcont hsupp).restrict U

private noncomputable def jetTripleCLM (J₀ : V →L[ℝ] V) :
    Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ]
      Lp (V × V × V) 2 (volume : Measure (ℝ × ℝ)) :=
  (ContinuousLinearMap.inl ℝ V (V × V)).compLpL 2 volume ∘L P_val V J₀ +
    ((ContinuousLinearMap.inr ℝ V (V × V)).comp
      (ContinuousLinearMap.inl ℝ V V)).compLpL 2 volume ∘L P_s V J₀ +
    ((ContinuousLinearMap.inr ℝ V (V × V)).comp
      (ContinuousLinearMap.inr ℝ V V)).compLpL 2 volume ∘L P_t V J₀

private theorem coeFn_jetTripleCLM (J₀ : V →L[ℝ] V)
    (f : Lp V 2 (volume : Measure (ℝ × ℝ))) :
    (jetTripleCLM J₀ f : ℝ × ℝ → V × V × V) =ᵐ[volume]
      fun z ↦ (P_val V J₀ f z, P_s V J₀ f z, P_t V J₀ f z) := by
  have h1 := Lp.coeFn_add
    (((ContinuousLinearMap.inl ℝ V (V × V)).compLpL 2 volume (P_val V J₀ f) +
      ((ContinuousLinearMap.inr ℝ V (V × V)).comp
        (ContinuousLinearMap.inl ℝ V V)).compLpL 2 volume (P_s V J₀ f)))
    (((ContinuousLinearMap.inr ℝ V (V × V)).comp
      (ContinuousLinearMap.inr ℝ V V)).compLpL 2 volume (P_t V J₀ f))
  have h2 := Lp.coeFn_add
    ((ContinuousLinearMap.inl ℝ V (V × V)).compLpL 2 volume (P_val V J₀ f))
    (((ContinuousLinearMap.inr ℝ V (V × V)).comp
      (ContinuousLinearMap.inl ℝ V V)).compLpL 2 volume (P_s V J₀ f))
  have h3 := (ContinuousLinearMap.inl ℝ V (V × V)).coeFn_compLpL (p := 2)
    (μ := (volume : Measure (ℝ × ℝ))) (P_val V J₀ f)
  have h4 := ((ContinuousLinearMap.inr ℝ V (V × V)).comp
    (ContinuousLinearMap.inl ℝ V V)).coeFn_compLpL (p := 2)
    (μ := (volume : Measure (ℝ × ℝ))) (P_s V J₀ f)
  have h5 := ((ContinuousLinearMap.inr ℝ V (V × V)).comp
    (ContinuousLinearMap.inr ℝ V V)).coeFn_compLpL (p := 2)
    (μ := (volume : Measure (ℝ × ℝ))) (P_t V J₀ f)
  filter_upwards [h1, h2, h3, h4, h5] with z hz1 hz2 hz3 hz4 hz5
  simp only [jetTripleCLM, add_apply, comp_apply, hz1, Pi.add_apply, hz2, hz3, hz4, hz5]
  ext <;> simp

private noncomputable def unrestrictedLocalParametrix {U : Set (ℝ × ℝ)}
    {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight U ρ) {β : ℝ × ℝ → ℝ}
    (hβ : ContDiff ℝ 2 β) (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ U)
    (J₀ : V →L[ℝ] V) :
    Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp (V × V × V) 2 (volume.restrict U) :=
  Lp.operatorMultiplication 2 ((memLp_cutoffCoeff hρ hβ hβc hβU).toLp (cutoffCoeff ρ β)) ∘L
    LpToLpRestrictCLM (ℝ × ℝ) (V × V × V) ℝ volume 2 U ∘L
    jetTripleCLM J₀

private theorem coeFn_unrestrictedLocalParametrix {U : Set (ℝ × ℝ)}
    {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight U ρ) {β : ℝ × ℝ → ℝ}
    (hβ : ContDiff ℝ 2 β) (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ U)
    (J₀ : V →L[ℝ] V) (f : Lp V 2 (volume : Measure (ℝ × ℝ))) :
    (unrestrictedLocalParametrix hρ hβ hβc hβU J₀ f : ℝ × ℝ → V × V × V)
      =ᵐ[volume.restrict U]
      fun z ↦ cutoffCoeff ρ β z (P_val V J₀ f z, P_s V J₀ f z, P_t V J₀ f z) := by
  set a := (memLp_cutoffCoeff (V := V) hρ hβ hβc hβU).toLp (cutoffCoeff ρ β)
  set g := LpToLpRestrictCLM (ℝ × ℝ) (V × V × V) ℝ volume 2 U (jetTripleCLM J₀ f)
  have h1 := Lp.operatorMultiplication_ae a g
  have h2 := (memLp_cutoffCoeff (V := V) hρ hβ hβc hβU).coeFn_toLp
  have h3 := LpToLpRestrictCLM_coeFn ℝ U (jetTripleCLM J₀ f)
  have h4 := ae_restrict_of_ae (s := U) (coeFn_jetTripleCLM J₀ f)
  filter_upwards [h1, h2, h3, h4] with z hz1 hz2 hz3 hz4
  change ⇑(Lp.operatorMultiplication 2 a g) z = _
  rw [hz1, hz2, hz3, hz4]

private theorem unrestrictedLocalParametrix_schwartz_mem_jetSubmodule
    {U : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight U ρ) {β : ℝ × ℝ → ℝ}
    (hβ : ContDiff ℝ 2 β) (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ U)
    (J₀ : V →L[ℝ] V)
    (φ : Fin (Module.finrank ℝ V) → 𝓢(EuclideanSpace ℝ (Fin 2), ℝ)) :
    unrestrictedLocalParametrix hρ hβ hβc hβU J₀
        (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Module.finBasis ℝ V i)).compLpL 2 volume
          (planeEquiv ℝ ((φ i).toLp 2))) ∈
      jetSubmodule V U ρ := by
  obtain ⟨ξ, hξ_cd, hPval_ae, hPs_ae, hPt_ae⟩ := schwartz_P_ae J₀ φ
  have htest : (fun z ↦ β z • ξ z) ∈ testSection V U :=
    mem_testSection_iff.2 ⟨hβ.smul (hξ_cd.of_le (by simp)), hβc.smul_right,
      (tsupport_smul_subset_left β ξ).trans hβU⟩
  refine mem_jetSubmodule_iff.2 ⟨fun z ↦ β z • ξ z, htest, ?_⟩
  filter_upwards [coeFn_unrestrictedLocalParametrix hρ hβ hβc hβU J₀ _,
    ae_restrict_of_ae hPval_ae, ae_restrict_of_ae hPs_ae, ae_restrict_of_ae hPt_ae]
    with z hP h0 hs ht
  rw [hP, h0, hs, ht, cutoffCoeff_apply, jet_apply]
  have hfd : fderiv ℝ (fun w ↦ β w • ξ w) z =
      β z • fderiv ℝ ξ z + (fderiv ℝ β z).smulRight (ξ z) :=
    fderiv_fun_smul (hβ.differentiable (by norm_num) z) (hξ_cd.differentiable (by simp) z)
  simp [hfd, smul_smul, mul_comm (√(ρ z))]

private theorem real_mul_div_lt {ε d P L x : ℝ} (hε : 0 < ε) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hx0 : 0 ≤ x) (hx : x < ε / ((d + 1) * (P + 1) * (L + 1))) (hd : 0 ≤ d) :
    L * x < ε / ((d + 1) * (P + 1)) := by
  have h1 : 0 < L + 1 := by positivity
  calc L * x ≤ (L + 1) * x := mul_le_mul_of_nonneg_right (by linarith) hx0
    _ < (L + 1) * (ε / ((d + 1) * (P + 1) * (L + 1))) := mul_lt_mul_of_pos_left hx h1
    _ = ε / ((d + 1) * (P + 1)) := by
      have hpos : L + 1 ≠ 0 := h1.ne'
      field_simp [hpos]

private theorem real_sum_const_lt {ε P : ℝ} {d : ℕ} (hε : 0 < ε) (hP : 0 ≤ P) :
    (d : ℝ) * (ε / ((↑d + 1) * (P + 1))) < ε / (P + 1) := by
  have hd : (d : ℝ) < ↑d + 1 := lt_add_one _
  have hp : 0 < P + 1 := by positivity
  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
  calc (d : ℝ) * ε = ε * d := mul_comm _ _
    _ < ε * (↑d + 1) := mul_lt_mul_of_pos_left hd hε
    _ = (ε / (P + 1)) * ((↑d + 1) * (P + 1)) := by
      have hp0 : P + 1 ≠ 0 := hp.ne'
      field_simp [hp0]

private theorem real_mul_lt_of_lt_div_add_one {ε P x : ℝ} (hP : 0 ≤ P) (hx0 : 0 ≤ x)
    (hx : x < ε / (P + 1)) : P * x < ε := by
  have hp : 0 < P + 1 := by positivity
  calc P * x ≤ (P + 1) * x := mul_le_mul_of_nonneg_right (by linarith) hx0
    _ < (P + 1) * (ε / (P + 1)) := mul_lt_mul_of_pos_left hx hp
    _ = ε := mul_div_cancel₀ _ hp.ne'

private theorem unrestrictedLocalParametrix_mem_H1 {U : Set (ℝ × ℝ)}
    {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight U ρ) {β : ℝ × ℝ → ℝ}
    (hβ : ContDiff ℝ 2 β) (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ U)
    (J₀ : V →L[ℝ] V) (f : Lp V 2 (volume : Measure (ℝ × ℝ))) :
    unrestrictedLocalParametrix hρ hβ hβc hβU J₀ f ∈ H1 V U ρ := by
  set d := Module.finrank ℝ V
  let b := Module.finBasis ℝ V
  let P := unrestrictedLocalParametrix hρ hβ hβc hβU J₀
  have hmem : P f ∈ closure (jetSubmodule V U ρ : Set _) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hdense :
        DenseRange fun φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℝ) ↦ planeEquiv ℝ (φ.toLp 2) :=
      (planeEquiv ℝ).surjective.denseRange.comp
        (SchwartzMap.denseRange_toLpCLM (E := EuclideanSpace ℝ (Fin 2)) (F := ℝ)
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ENNReal.ofNat_ne_top)
        (planeEquiv ℝ).continuous
    choose φ hφ using fun i : Fin d ↦ by
      have hδ : 0 < ε / ((↑d + 1) * (‖P‖ + 1) *
          (‖(ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2
            (volume : Measure (ℝ × ℝ))‖ + 1)) :=
        by positivity
      exact hdense.exists_dist_lt ((b.coord i).toContinuousLinearMap.compLpL 2 volume f) hδ
    let f₀ : Lp V 2 (volume : Measure (ℝ × ℝ)) :=
      ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2 volume
        (planeEquiv ℝ ((φ i).toLp 2))
    have hf_dist : dist (P f₀) (P f) < ε := by
      have hf_sub : dist f₀ f ≤ ∑ i : Fin d,
          ‖(ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2
              (volume : Measure (ℝ × ℝ))‖ *
            dist (planeEquiv ℝ ((φ i).toLp 2))
              ((b.coord i).toContinuousLinearMap.compLpL 2 volume f) := by
        rw [dist_eq_norm]
        conv_lhs => rw [TauCeti.eq_sum_basis_compLpL b f]
        rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        rw [← map_sub, dist_eq_norm]
        exact ContinuousLinearMap.le_opNorm
          ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2
            (volume : Measure (ℝ × ℝ))) _
      have h_f0 : dist f₀ f < ε / (‖P‖ + 1) := by
        refine hf_sub.trans_lt ?_
        by_cases hd : d = 0
        · have : ∑ i : Fin d,
              ‖(ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL 2
                  (volume : Measure (ℝ × ℝ))‖ *
                dist (planeEquiv ℝ ((φ i).toLp 2))
                  ((b.coord i).toContinuousLinearMap.compLpL 2 volume f) = 0 :=
            Finset.sum_eq_zero fun i _ ↦ (Nat.not_lt_zero i.val (hd ▸ i.isLt)).elim
          rw [this]; positivity
        · have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
          refine lt_trans (Finset.sum_lt_sum_of_nonempty
            (g := fun _ : Fin d ↦ ε / ((↑d + 1) * (‖P‖ + 1)))
            Finset.univ_nonempty fun i _ ↦ ?_) ?_
          · refine real_mul_div_lt hε (norm_nonneg P) (norm_nonneg _) dist_nonneg ?_
              (Nat.cast_nonneg d)
            rw [dist_comm]; exact hφ i
          · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            exact real_sum_const_lt hε (norm_nonneg P)
      have h1 : dist (P f₀) (P f) ≤ ‖P‖ * dist f₀ f := by
        rw [dist_eq_norm, dist_eq_norm, ← P.map_sub]
        exact P.le_opNorm _
      exact h1.trans_lt (real_mul_lt_of_lt_div_add_one (norm_nonneg P) dist_nonneg h_f0)
    have hf₀_mem : P f₀ ∈ (jetSubmodule V U ρ : Set _) := by
      dsimp only [P, f₀, b]
      exact SetLike.mem_coe.2
        (unrestrictedLocalParametrix_schwartz_mem_jetSubmodule hρ hβ hβc hβU J₀ φ)
    exact ⟨P f₀, hf₀_mem, dist_comm (P f) (P f₀) ▸ hf_dist⟩
  exact (isClosed_H1 (V := V) (U := U) (ρ := ρ)).closure_subset_iff.2 jetSubmodule_le_H1 hmem

omit [FiniteDimensional ℝ V] in
private noncomputable def extLp {U : Set (ℝ × ℝ)} (hU : IsOpen U) :
    Lp V 2 (volume.restrict U) →L[ℝ] Lp V 2 (volume : Measure (ℝ × ℝ)) :=
  (TauCeti.castLpₗᵢ (E := V) (p := 2) (𝕜 := ℝ)
      Measure.restrict_univ).toLinearIsometry.toContinuousLinearMap ∘L
    (TauCeti.extendByZeroLpₗᵢ (F := V) (p := 2) ℝ volume hU.measurableSet.nullMeasurableSet
      (subset_univ U)).toContinuousLinearMap

omit [FiniteDimensional ℝ V] in
private theorem norm_extLp_le {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : Lp V 2 (volume.restrict U)) :
    ‖extLp (V := V) hU h‖ ≤ ‖h‖ := by
  dsimp only [extLp]
  rw [comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]

omit [FiniteDimensional ℝ V] in
private theorem coeFn_extLp_restrict {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : Lp V 2 (volume.restrict U)) :
    (extLp (V := V) hU h : ℝ × ℝ → V) =ᵐ[volume.restrict U] h := by
  have h1 := ae_restrict_of_ae (μ := volume) (s := U)
    (TauCeti.coeFn_castLpₗᵢ_extendByZeroLpₗᵢ (F := V) (p := 2) ℝ
      hU.measurableSet.nullMeasurableSet h)
  filter_upwards [h1, ae_restrict_mem hU.measurableSet] with z hz hzU
  dsimp only [extLp, comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]
  rw [hz, Set.indicator_of_mem hzU]

private noncomputable def localParametrix {U : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
    (hρ : IsWeight U ρ) {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ U) (J₀ : V →L[ℝ] V) :
    Lp V 2 (volume.restrict U) →L[ℝ] H1 V U ρ :=
  ((unrestrictedLocalParametrix hρ hβ hβc hβU J₀).comp (extLp hρ.isOpen)).codRestrict
    (H1 V U ρ) (fun _ ↦ unrestrictedLocalParametrix_mem_H1 hρ hβ hβc hβU J₀ _)

private theorem localParametrix_piece {U : Set (ℝ × ℝ)} {ρ : ℝ × ℝ → ℝ}
    (hρ : IsWeight U ρ) {J C : ℝ × ℝ → V →L[ℝ] V}
    (hM : MemLp (fun z ↦ firstOrderJetCoeff (J z) (C z)) ∞ (volume.restrict U))
    (hJc : ContinuousOn J U) {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 2 β)
    (hβc : HasCompactSupport β) (hβU : tsupport β ⊆ U)
    {J₀ : V →L[ℝ] V} (hJ₀ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ V) :
    ∃ K E : Lp V 2 (volume.restrict U) →L[ℝ] Lp V 2 (volume.restrict U),
      IsCompactOperator K ∧
      (∀ h : Lp V 2 (volume.restrict U),
        (E h : ℝ × ℝ → V) =ᵐ[volume.restrict U]
          fun z ↦ β z • (J z - J₀) (P_t V J₀ (extLp hρ.isOpen h) z)) ∧
      ∀ h : Lp V 2 (volume.restrict U),
        (jetOperator (volume.restrict U) (fun z ↦ firstOrderJetCoeff (J z) (C z))
            ((localParametrix hρ hβ hβc hβU J₀ h : _) : _) :
            ℝ × ℝ → V) =ᵐ[volume.restrict U]
          fun z ↦ β z • h z + K h z + E h z := by
  set extU := extLp (V := V) hρ.isOpen
  have hE_mem : MemLp (fun z ↦ β z • (J z - J₀)) ∞ (volume.restrict U) := by
    have hc : Continuous fun z ↦ β z • (J z - J₀) :=
      (hβ.continuous.continuousOn.smul (hJc.sub continuousOn_const)).continuous_of_tsupport_subset
        hρ.isOpen ((tsupport_smul_subset_left β _).trans hβU)
    exact (memLp_top_of_continuous_of_hasCompactSupport hc hβc.smul_right).restrict U
  set E : Lp V 2 (volume.restrict U) →L[ℝ] Lp V 2 (volume.restrict U) :=
    Lp.operatorMultiplication 2 (hE_mem.toLp (fun z ↦ β z • (J z - J₀))) ∘L
      LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U ∘L P_t V J₀ ∘L extU
  obtain ⟨χ₀, hχ₀, -, hχ₀1, hχ₀c, -⟩ :=
    hβc.isCompact.exists_contDiff_cutoff_eventuallyEq_one hρ.isOpen hβU
  have hχ₀_cd : ContDiff ℝ (⊤ : ℕ∞) χ₀ := hχ₀
  have hχ₀_mem : MemLp χ₀ ∞ (volume : Measure (ℝ × ℝ)) :=
    memLp_top_of_continuous_of_hasCompactSupport hχ₀.continuous hχ₀c
  set aχ₀ := hχ₀_mem.toLp χ₀
  have hχ₀_tsupp : ∀ z ∈ tsupport β, χ₀ z = 1 := fun z hz ↦ (hχ₀1 z hz).self_of_nhds
  have hC_mem : MemLp C ∞ (volume.restrict U) := by
    let Φ : (V × V × V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
      (ContinuousLinearMap.compL ℝ V (V × V × V) V).flip
        (ContinuousLinearMap.inl ℝ V (V × V))
    have hcomp : C = Φ ∘ fun z ↦ firstOrderJetCoeff (J z) (C z) := by
      ext z v; simp [Φ]
    rw [hcomp]
    exact Φ.comp_memLp' hM
  have hsqrt : Continuous fun z ↦ √(ρ z) * β z :=
    (hρ.continuousOn.sqrt.mul hβ.continuous.continuousOn).continuous_of_tsupport_subset
      hρ.isOpen ((tsupport_mul_subset_right (f := fun z ↦ √(ρ z)) (g := β)).trans hβU)
  have hsqrt_mem : MemLp (fun z ↦ √(ρ z) * β z) ∞ (volume.restrict U) :=
    (memLp_top_of_continuous_of_hasCompactSupport hsqrt hβc.mul_left).restrict U
  have hnegβ_mem :
      MemLp (fun z ↦ (-β z) • ContinuousLinearMap.id ℝ V) ∞ (volume.restrict U) :=
    (memLp_top_of_continuous_of_hasCompactSupport (hβ.continuous.neg.smul continuous_const)
      hβc.neg.smul_right).restrict U
  let M_val : ℝ × ℝ → V →L[ℝ] V := fun z ↦
    fderiv ℝ β z (1, 0) • ContinuousLinearMap.id ℝ V +
      fderiv ℝ β z (0, 1) • J z + (√(ρ z) * β z) • C z
  have hMval_mem : MemLp M_val ∞ (volume.restrict U) := by
    have hd := hβ.continuous_fderiv (by norm_num)
    have hc1 : MemLp (fun z ↦ fderiv ℝ β z (1, 0) • ContinuousLinearMap.id ℝ V) ∞
        (volume.restrict U) :=
      (memLp_top_of_continuous_of_hasCompactSupport
        ((hd.clm_apply continuous_const).smul continuous_const)
        (hβc.fderiv_apply (𝕜 := ℝ) (1, 0)).smul_right).restrict U
    have hc2 : MemLp (fun z ↦ fderiv ℝ β z (0, 1) • J z) ∞ (volume.restrict U) := by
      have hcd : Continuous fun z ↦ fderiv ℝ β z (0, 1) • J z :=
        ((hd.clm_apply continuous_const).continuousOn.smul hJc).continuous_of_tsupport_subset
          hρ.isOpen ((tsupport_smul_subset_left _ J).trans
            ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hβU))
      exact (memLp_top_of_continuous_of_hasCompactSupport hcd
        (hβc.fderiv_apply (𝕜 := ℝ) (0, 1)).smul_right).restrict U
    exact (hc1.add hc2).add (hsqrt_mem.smul hC_mem)
  set C₁ :
      Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 (volume : Measure (ℝ × ℝ)) :=
    Lp.multiplicationOperator aχ₀ ∘L liftOp V T_val
  set C₂ :
      Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 (volume : Measure (ℝ × ℝ)) :=
    Lp.multiplicationOperator aχ₀ ∘L P_val V J₀
  set K₁ : Lp V 2 (volume.restrict U) →L[ℝ] Lp V 2 (volume.restrict U) :=
    (Lp.operatorMultiplication 2 (hnegβ_mem.toLp _) ∘L
      LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U) ∘L (C₁ ∘L extU)
  set K₂ : Lp V 2 (volume.restrict U) →L[ℝ] Lp V 2 (volume.restrict U) :=
    (Lp.operatorMultiplication 2 (hMval_mem.toLp M_val) ∘L
      LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U) ∘L (C₂ ∘L extU)
  have hC₁ : IsCompactOperator C₁ :=
    isCompactOperator_multiplicationOperator_comp_liftOp_T_val (V := V) hχ₀_cd hχ₀c
  have hC₂ : IsCompactOperator C₂ :=
    isCompactOperator_multiplicationOperator_comp_P_val (V := V) hχ₀_cd hχ₀c J₀
  have hK₁ : IsCompactOperator K₁ :=
    (hC₁.comp_clm extU).clm_comp
      (Lp.operatorMultiplication 2 (hnegβ_mem.toLp _) ∘L
        LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U)
  have hK₂ : IsCompactOperator K₂ :=
    (hC₂.comp_clm extU).clm_comp
      (Lp.operatorMultiplication 2 (hMval_mem.toLp M_val) ∘L
        LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U)
  have hE_ae (h : Lp V 2 (volume.restrict U)) :
      (E h : ℝ × ℝ → V) =ᵐ[volume.restrict U]
        fun z ↦ β z • (J z - J₀) (P_t V J₀ (extU h) z) := by
    have h1 := Lp.operatorMultiplication_ae (hE_mem.toLp (fun z ↦ β z • (J z - J₀)))
      (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U (P_t V J₀ (extU h)))
    filter_upwards [h1, hE_mem.coeFn_toLp, LpToLpRestrictCLM_coeFn ℝ U (P_t V J₀ (extU h))]
      with z hz1 hz2 hz3
    simp only [E, comp_apply, hz1, hz2, hz3, sub_apply, smul_apply]
  refine ⟨K₁ + K₂, E, hK₁.add hK₂, hE_ae, fun h ↦ ?_⟩
  have hK₁_ae : (K₁ h : ℝ × ℝ → V) =ᵐ[volume.restrict U]
      fun z ↦ (-β z) • liftOp V T_val (extU h) z := by
    have h1 := Lp.operatorMultiplication_ae (hnegβ_mem.toLp _)
      (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U (C₁ (extU h)))
    have h3 := LpToLpRestrictCLM_coeFn ℝ U (C₁ (extU h))
    have h4 := ae_restrict_of_ae (s := U)
      (Lp.multiplicationOperator_ae aχ₀ (liftOp V T_val (extU h)))
    filter_upwards [h1, hnegβ_mem.coeFn_toLp, h3, h4, ae_restrict_of_ae hχ₀_mem.coeFn_toLp]
      with z hz1 hz2 hz3 hz4 hz5
    dsimp only [K₁, C₁]
    rw [comp_apply, comp_apply, comp_apply, hz1, hz2, hz3, comp_apply, hz4, hz5]
    by_cases hzb : z ∈ tsupport β
    · simp [hχ₀_tsupp z hzb]
    · simp [image_eq_zero_of_notMem_tsupport hzb]
  have hK₂_ae : (K₂ h : ℝ × ℝ → V) =ᵐ[volume.restrict U]
      fun z ↦ M_val z (P_val V J₀ (extU h) z) := by
    have h1 := Lp.operatorMultiplication_ae (hMval_mem.toLp M_val)
      (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U (C₂ (extU h)))
    have h3 := LpToLpRestrictCLM_coeFn ℝ U (C₂ (extU h))
    have h4 := ae_restrict_of_ae (s := U)
      (Lp.multiplicationOperator_ae aχ₀ (P_val V J₀ (extU h)))
    filter_upwards [h1, hMval_mem.coeFn_toLp, h3, h4, ae_restrict_of_ae hχ₀_mem.coeFn_toLp]
      with z hz1 hz2 hz3 hz4 hz5
    dsimp only [K₂, C₂]
    rw [comp_apply, comp_apply, comp_apply, hz1, hz2, hz3, comp_apply, hz4, hz5]
    by_cases hzb : z ∈ tsupport β
    · simp [hχ₀_tsupp z hzb]
    · have hev : β =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hzb
      simp [M_val, hev.eq_of_nhds, hev.fderiv_eq]
  have hP := ae_restrict_of_ae (s := U) (Lp.ext_iff.1 (congrArg
    (fun op : Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ]
        Lp V 2 (volume : Measure (ℝ × ℝ)) ↦ op (extU h))
    (P_s_add_compLpL_P_t (V := V) hJ₀)))
  have hP_lhs := ae_restrict_of_ae (s := U) (Lp.coeFn_add (P_s V J₀ (extU h))
    (J₀.compLpL 2 volume (P_t V J₀ (extU h))))
  have hP_rhs := ae_restrict_of_ae (s := U) (Lp.coeFn_sub (extU h) (liftOp V T_val (extU h)))
  have hP_J₀ := ae_restrict_of_ae (s := U)
    (J₀.coeFn_compLpL (p := 2) (μ := (volume : Measure (ℝ × ℝ))) (P_t V J₀ (extU h)))
  filter_upwards [coeFn_jetOperator hM ((localParametrix hρ hβ hβc hβU J₀ h : _) : _),
    coeFn_unrestrictedLocalParametrix hρ hβ hβc hβU J₀ (extU h),
    Lp.coeFn_add (K₁ h) (K₂ h), hK₁_ae, hK₂_ae, hE_ae h, hP, hP_lhs, hP_rhs, hP_J₀,
    coeFn_extLp_restrict hρ.isOpen h]
    with z hzD hzpar hzK hzK₁ hzK₂ hzE hzP hzPl hzPr hzPJ hzext
  have hPs_sum : P_s V J₀ (extU h) z + J₀ (P_t V J₀ (extU h) z) =
      extU h z - liftOp V T_val (extU h) z := by
    rw [add_apply, comp_apply, sub_apply, id_apply, hzPl, Pi.add_apply, hzPJ, hzPr,
      Pi.sub_apply] at hzP
    exact hzP
  have hPs' : P_s V J₀ (extU h) z =
      extU h z - liftOp V T_val (extU h) z - J₀ (P_t V J₀ (extU h) z) :=
    eq_sub_of_add_eq hPs_sum
  have hpar' : (((localParametrix hρ hβ hβc hβU J₀ h : H1 V U ρ) :
        Lp (V × V × V) 2 (volume.restrict U)) z) =
      cutoffCoeff ρ β z (P_val V J₀ (extU h) z, P_s V J₀ (extU h) z, P_t V J₀ (extU h) z) :=
    hzpar
  rw [hzD, hpar', cutoffCoeff_apply, firstOrderJetCoeff_apply, add_apply, hzK, Pi.add_apply,
    hzK₁, hzK₂, hzE, ← hzext, hPs']
  dsimp only [M_val]
  simp only [add_apply, smul_apply, id_apply, sub_apply, map_add, map_smul,
    smul_sub, neg_smul]
  abel

open scoped Classical in
/-- **Local right parametrix on a compact subset of a conformal planar domain.**
Given an open set `U ⊆ ℝ × ℝ` with conformal weight `ρ`, a first-order Cauchy--Riemann
operator `∂s + J ∂t + C` on `H1 V U ρ` with `J` continuous on `U` satisfying `J(z)² = -id`,
any `C²` compactly supported cutoff `β₀` with `tsupport β₀ ⊆ U`, and any `ε > 0`, there
exists a bounded operator `P : L²(U, V) → H1 V U ρ` such that
`D ∘ P = β₀ • id + K + E` with `K` compact and `‖E‖ ≤ ε`. -/
theorem exists_jetOperator_firstOrderJetCoeff_comp_eq_smul_add {U : Set (ℝ × ℝ)}
    {ρ : ℝ × ℝ → ℝ}
    (hρ : IsWeight U ρ) {J C : ℝ × ℝ → V →L[ℝ] V}
    (hM : MemLp (fun z ↦ firstOrderJetCoeff (J z) (C z)) ∞ (volume.restrict U))
    (hJc : ContinuousOn J U) (hJsq : ∀ z ∈ U, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    {β₀ : ℝ × ℝ → ℝ} (hβ₀ : ContDiff ℝ 2 β₀) (hβ₀c : HasCompactSupport β₀)
    (hβ₀U : tsupport β₀ ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : Lp V 2 (volume.restrict U) →L[ℝ] H1 V U ρ)
      (K E : Lp V 2 (volume.restrict U) →L[ℝ] Lp V 2 (volume.restrict U)),
      IsCompactOperator K ∧ ‖E‖ ≤ ε ∧ ∀ h : Lp V 2 (volume.restrict U),
        (jetOperator (volume.restrict U) (fun z ↦ firstOrderJetCoeff (J z) (C z))
            ((P h : H1 V U ρ) : Lp (V × V × V) 2 (volume.restrict U)) : ℝ × ℝ → V)
          =ᵐ[volume.restrict U] fun z ↦ β₀ z • h z + K h z + E h z := by
  obtain ⟨r₀, hr₀, hr₀U⟩ :=
    hβ₀c.isCompact.exists_cthickening_subset_open hρ.isOpen hβ₀U
  let K₁ : Set (ℝ × ℝ) := Metric.cthickening r₀ (tsupport β₀)
  have hK₁c : IsCompact K₁ := hβ₀c.isCompact.cthickening
  obtain ⟨M_J0, hM_J0⟩ := hK₁c.exists_bound_of_continuousOn (hJc.mono hr₀U)
  let M_J : ℝ := max M_J0 0
  have hM_J0_nonneg : 0 ≤ M_J := le_max_right _ _
  have hM_J_bound : ∀ z ∈ K₁, ‖J z‖ ≤ M_J :=
    fun z hz ↦ (hM_J0 z hz).trans (le_max_left _ _)
  have hJuc : UniformContinuousOn J K₁ :=
    hK₁c.uniformContinuousOn_of_continuous (hJc.mono hr₀U)
  obtain ⟨M_β0, hM_β0⟩ :=
    hβ₀c.isCompact.exists_bound_of_continuousOn hβ₀.continuous.continuousOn
  let M_β : ℝ := max M_β0 0
  have hM_β_nonneg : 0 ≤ M_β := le_max_right _ _
  have hM_β_bound : ∀ z, |β₀ z| ≤ M_β := fun z ↦ by
    by_cases hz : z ∈ tsupport β₀
    · simpa only [Real.norm_eq_abs] using (hM_β0 z hz).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
      exact hM_β_nonneg
  let C_op : ℝ := M_β * (‖liftOp V T_st‖ + M_J * ‖liftOp V T_tt‖) + 1
  have hC_op : 0 < C_op := by
    have : 0 ≤ M_β * (‖liftOp V T_st‖ + M_J * ‖liftOp V T_tt‖) := by positivity
    linarith
  let η : ℝ := ε / C_op
  have hη : 0 < η := div_pos hε hC_op
  obtain ⟨δ₁, hδ₁, hJδ₁⟩ := Metric.uniformContinuousOn_iff.1 hJuc η hη
  let δ : ℝ := min (r₀ / 2) (δ₁ / 2)
  have hδ : 0 < δ := lt_min (half_pos hr₀) (half_pos hδ₁)
  obtain ⟨R0, hR0⟩ := hβ₀c.isCompact.isBounded.subset_closedBall 0
  let R : ℝ := max R0 0
  have hR : tsupport β₀ ⊆ Metric.closedBall 0 R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let N : ℤ := ⌈R / δ + 1⌉
  have hN : R / δ + 1 ≤ N := Int.le_ceil _
  let γ : ℤ × ℤ → ℝ × ℝ → ℝ := fun k z ↦
    TauCeti.latticeBump₁ (z.1 / δ - k.1) * TauCeti.latticeBump₁ (z.2 / δ - k.2)
  let F_raw : Finset (ℤ × ℤ) := Finset.Icc (-N) N ×ˢ Finset.Icc (-N) N
  let F' : Finset (ℤ × ℤ) :=
    F_raw.filter fun k ↦ (tsupport β₀ ∩ Function.support (γ k)).Nonempty
  let center : ℤ × ℤ → ℝ × ℝ := fun k ↦ (δ * k.1, δ * k.2)
  have hγ_nonneg : ∀ k z, 0 ≤ γ k z := fun k z ↦
    mul_nonneg (TauCeti.latticeBump₁_nonneg _) (TauCeti.latticeBump₁_nonneg _)
  have hγ_dist : ∀ {k z}, γ k z ≠ 0 → dist z (center k) < 2 * δ := by
    intro k z hnz
    have ha1 := TauCeti.abs_lt_one_of_latticeBump₁_ne_zero (left_ne_zero_of_mul hnz)
    have ha2 := TauCeti.abs_lt_one_of_latticeBump₁_ne_zero (right_ne_zero_of_mul hnz)
    have hdx : |z.1 - δ * k.1| < δ := by
      rw [show z.1 - δ * k.1 = δ * (z.1 / δ - k.1) by field_simp, abs_mul, abs_of_pos hδ]
      exact mul_lt_of_lt_one_right hδ ha1
    have hdy : |z.2 - δ * k.2| < δ := by
      rw [show z.2 - δ * k.2 = δ * (z.2 / δ - k.2) by field_simp, abs_mul, abs_of_pos hδ]
      exact mul_lt_of_lt_one_right hδ ha2
    exact max_lt (hdx.trans (lt_two_mul_self hδ)) (hdy.trans (lt_two_mul_self hδ))
  have hcenter_K₁ : ∀ k ∈ F', center k ∈ K₁ := by
    intro k hk
    obtain ⟨w, hw_supp, hw_nz⟩ := (Finset.mem_filter.1 hk).2
    have hdr : dist (center k) w ≤ r₀ := by
      rw [dist_comm]
      exact (hγ_dist hw_nz).le.trans (by linarith [min_le_left (r₀ / 2) (δ₁ / 2)])
    exact Metric.mem_cthickening_of_dist_le (center k) w r₀ (tsupport β₀) hw_supp hdr
  have hγ_cd : ∀ k : ℤ × ℤ, ContDiff ℝ 2 (fun z ↦ β₀ z * γ k z) := fun k ↦ by
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : ℝ × ℝ ↦ TauCeti.latticeBump₁ (z.1 / δ - k.1)) :=
      TauCeti.contDiff_latticeBump₁.comp ((contDiff_fst.div_const δ).sub contDiff_const)
    have h2 : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : ℝ × ℝ ↦ TauCeti.latticeBump₁ (z.2 / δ - k.2)) :=
      TauCeti.contDiff_latticeBump₁.comp ((contDiff_snd.div_const δ).sub contDiff_const)
    exact hβ₀.mul ((h1.mul h2).of_le (by simp))
  have hγ_supp : ∀ k : ℤ × ℤ, HasCompactSupport (fun z ↦ β₀ z * γ k z) :=
    fun _ ↦ hβ₀c.mul_right
  have hγ_U : ∀ k : ℤ × ℤ, tsupport (fun z ↦ β₀ z * γ k z) ⊆ U := fun k ↦
    (tsupport_mul_subset_left (f := β₀) (g := γ k)).trans hβ₀U
  have hsum_γ_le : ∀ z, ∑ k ∈ F', γ k z ≤ 1 := fun z ↦ by
    let A := F'.image Prod.fst
    let B := F'.image Prod.snd
    calc ∑ k ∈ F', γ k z
        ≤ ∑ k ∈ A ×ˢ B, γ k z :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun k hk ↦ Finset.mem_product.2
            ⟨Finset.mem_image_of_mem _ hk, Finset.mem_image_of_mem _ hk⟩)
            (fun k _ _ ↦ hγ_nonneg k z)
      _ = (∑ i ∈ A, TauCeti.latticeBump₁ (z.1 / δ - i)) *
            (∑ j ∈ B, TauCeti.latticeBump₁ (z.2 / δ - j)) := by
          rw [Finset.sum_product, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.mul_sum]
      _ ≤ 1 * 1 := by
          refine mul_le_mul ?_ ?_
            (Finset.sum_nonneg fun _ _ ↦ TauCeti.latticeBump₁_nonneg _) zero_le_one
          · have hs1 := TauCeti.hasSum_latticeBump₁_sub (z.1 / δ)
            exact (hs1.summable.sum_le_tsum A fun _ _ ↦ TauCeti.latticeBump₁_nonneg _).trans_eq
              hs1.tsum_eq
          · have hs2 := TauCeti.hasSum_latticeBump₁_sub (z.2 / δ)
            exact (hs2.summable.sum_le_tsum B fun _ _ ↦ TauCeti.latticeBump₁_nonneg _).trans_eq
              hs2.tsum_eq
      _ = 1 := one_mul 1
  have hsum_mul_γ : ∀ z, ∑ k ∈ F', β₀ z * γ k z = β₀ z := fun z ↦ by
    by_cases hz : z ∈ tsupport β₀
    · rw [← Finset.mul_sum]
      have hz_ball : ‖z‖ ≤ R := by simpa using hR hz
      have hsub_coord : ∀ {x : ℝ} (_ : |x| ≤ R) (i : ℤ),
          TauCeti.latticeBump₁ (x / δ - i) ≠ 0 → i ∈ Finset.Icc (-N) N := by
        intro x hx i hi
        have ha := TauCeti.abs_lt_one_of_latticeBump₁_ne_zero hi
        have hbi : |(i : ℝ)| ≤ N := calc
          |(i : ℝ)| = |(x / δ) - (x / δ - i)| := by ring_nf
          _ ≤ |x / δ| + |x / δ - i| := abs_sub _ _
          _ ≤ R / δ + 1 := by
              gcongr
              rw [abs_div, abs_of_pos hδ]
              exact div_le_div_of_nonneg_right hx hδ.le
          _ ≤ N := hN
        obtain ⟨hlo, hhi⟩ := abs_le.1 hbi
        exact Finset.mem_Icc.2 ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
      have hsub1 := hsub_coord
        ((Real.norm_eq_abs z.1).symm.trans_le ((norm_fst_le z).trans hz_ball))
      have hsub2 := hsub_coord
        ((Real.norm_eq_abs z.2).symm.trans_le ((norm_snd_le z).trans hz_ball))
      have hsum_raw : ∑ k ∈ F_raw, γ k z = 1 := by
        have hs1 : ∑ i ∈ Finset.Icc (-N) N, TauCeti.latticeBump₁ (z.1 / δ - i) = 1 := by
          rw [← (TauCeti.hasSum_latticeBump₁_sub (z.1 / δ)).tsum_eq]
          exact (tsum_eq_sum fun i hi ↦ by_contra fun hne ↦ hi (hsub1 i hne)).symm
        have hs2 : ∑ j ∈ Finset.Icc (-N) N, TauCeti.latticeBump₁ (z.2 / δ - j) = 1 := by
          rw [← (TauCeti.hasSum_latticeBump₁_sub (z.2 / δ)).tsum_eq]
          exact (tsum_eq_sum fun j hj ↦ by_contra fun hne ↦ hj (hsub2 j hne)).symm
        calc ∑ k ∈ F_raw, γ k z
            = (∑ i ∈ Finset.Icc (-N) N, TauCeti.latticeBump₁ (z.1 / δ - i)) *
                (∑ j ∈ Finset.Icc (-N) N, TauCeti.latticeBump₁ (z.2 / δ - j)) := by
              rw [Finset.sum_product, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [Finset.mul_sum]
          _ = 1 * 1 := by rw [hs1, hs2]
          _ = 1 := one_mul 1
      have hsum_F : ∑ k ∈ F', γ k z = ∑ k ∈ F_raw, γ k z :=
        Finset.sum_filter_of_ne fun k _ hne ↦ ⟨z, hz, hne⟩
      rw [hsum_F, hsum_raw, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hpiece : ∀ k ∈ F',
      ∃ K_k E_k : Lp V 2 (volume.restrict U) →L[ℝ] Lp V 2 (volume.restrict U),
      IsCompactOperator K_k ∧
      (∀ h : Lp V 2 (volume.restrict U),
        (E_k h : ℝ × ℝ → V) =ᵐ[volume.restrict U] fun z ↦ (β₀ z * γ k z) •
          (J z - J (center k)) (P_t V (J (center k)) (extLp hρ.isOpen h) z)) ∧
      ∀ h : Lp V 2 (volume.restrict U),
        (jetOperator (volume.restrict U) (fun z ↦ firstOrderJetCoeff (J z) (C z))
            ((localParametrix hρ (hγ_cd k) (hγ_supp k) (hγ_U k) (J (center k)) h : _) : _) :
            ℝ × ℝ → V) =ᵐ[volume.restrict U]
          fun z ↦ (β₀ z * γ k z) • h z + K_k h z + E_k h z := fun k hk ↦
    localParametrix_piece hρ hM hJc (hγ_cd k) (hγ_supp k) (hγ_U k)
      (hJsq (center k) (hr₀U (hcenter_K₁ k hk)))
  choose K_k E_k hK_cp hE_ae hD_ae using hpiece
  let P : Lp V 2 (volume.restrict U) →L[ℝ] H1 V U ρ :=
    ∑ k ∈ F'.attach,
      localParametrix hρ (hγ_cd k.val) (hγ_supp k.val) (hγ_U k.val) (J (center k.val))
  let K : Lp V 2 (volume.restrict U) →L[ℝ] Lp V 2 (volume.restrict U) :=
    ∑ k ∈ F'.attach, K_k k.val k.property
  let E : Lp V 2 (volume.restrict U) →L[ℝ] Lp V 2 (volume.restrict U) :=
    ∑ k ∈ F'.attach, E_k k.val k.property
  have hK : IsCompactOperator K :=
    Finset.sum_induction _ (fun (op : Lp V 2 _ →L[ℝ] Lp V 2 _) ↦ IsCompactOperator op)
      (fun _ _ ha hb ↦ ha.add hb) isCompactOperator_zero fun k _ ↦ hK_cp k.val k.property
  have hE_norm : ‖E‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun h ↦ ?_
    set G₁ : Lp V 2 (volume.restrict U) :=
      LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U (liftOp V T_st (extLp hρ.isOpen h))
    set G₂ : Lp V 2 (volume.restrict U) :=
      LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 U (liftOp V T_tt (extLp hρ.isOpen h))
    have hG₁_ae :
        (G₁ : ℝ × ℝ → V) =ᵐ[volume.restrict U] liftOp V T_st (extLp hρ.isOpen h) :=
      LpToLpRestrictCLM_coeFn ℝ U _
    have hG₂_ae :
        (G₂ : ℝ × ℝ → V) =ᵐ[volume.restrict U] liftOp V T_tt (extLp hρ.isOpen h) :=
      LpToLpRestrictCLM_coeFn ℝ U _
    have hPt_all : ∀ k : F', ∀ᵐ z ∂(volume.restrict U),
        ‖P_t V (J (center k.val)) (extLp hρ.isOpen h) z‖ ≤
          ‖G₁ z‖ + M_J * ‖G₂ z‖ :=
      fun k ↦ by
        filter_upwards [ae_restrict_of_ae (norm_P_t_apply_le
          (hM_J_bound (center k.val) (hcenter_K₁ k.val k.property)) (extLp hρ.isOpen h)),
          hG₁_ae, hG₂_ae] with z hz hz1 hz2
        simpa [hz1, hz2] using hz
    have hE_sum_ae : ⇑(E h) =ᵐ[volume.restrict U]
        ∑ k ∈ F'.attach, fun z ↦ ⇑(E_k k.val k.property h) z := by
      change ⇑((∑ k ∈ F'.attach, E_k k.val k.property) h) =ᵐ[volume.restrict U] _
      rw [sum_apply]
      exact (Lp.coeFn_finsetSum F'.attach _).trans (.of_forall fun _ ↦ rfl)
    have hE_pt : ∀ᵐ z ∂(volume.restrict U),
        ‖E h z‖ ≤ (M_β * η) * (‖G₁ z‖ + M_J * ‖G₂ z‖) := by
      filter_upwards [hE_sum_ae, ae_all_iff.2 fun k : F' ↦ hE_ae k.val k.property h,
        ae_all_iff.2 hPt_all] with z hz_sum hz_term hz_pt
      rw [hz_sum, Finset.sum_apply]
      calc ‖∑ k ∈ F'.attach, ⇑(E_k k.val k.property h) z‖
          ≤ ∑ k ∈ F'.attach, ‖E_k k.val k.property h z‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ F'.attach,
              (M_β * η) * γ k.val z * (‖G₁ z‖ + M_J * ‖G₂ z‖) := by
            refine Finset.sum_le_sum fun k _ ↦ ?_
            rw [hz_term k, norm_smul, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (hγ_nonneg k.val z)]
            by_cases hzb : z ∈ tsupport β₀
            · by_cases hgz : γ k.val z = 0
              · simp [hgz]
              · have hzK₁ : z ∈ K₁ := Metric.self_subset_cthickening (tsupport β₀) hzb
                have hdist : dist z (center k.val) < δ₁ :=
                  (hγ_dist hgz).trans_le (by linarith [min_le_right (r₀ / 2) (δ₁ / 2)])
                have hJdiff : ‖J z - J (center k.val)‖ < η := by
                  simpa only [dist_eq_norm] using
                    hJδ₁ z hzK₁ (center k.val) (hcenter_K₁ k.val k.property) hdist
                calc |β₀ z| * γ k.val z * ‖(J z - J (center k.val))
                        (P_t V (J (center k.val)) (extLp hρ.isOpen h) z)‖
                    ≤ |β₀ z| * γ k.val z *
                        (‖J z - J (center k.val)‖ *
                          ‖P_t V (J (center k.val)) (extLp hρ.isOpen h) z‖) :=
                      mul_le_mul_of_nonneg_left ((J z - J (center k.val)).le_opNorm _)
                        (mul_nonneg (abs_nonneg _) (hγ_nonneg k.val z))
                  _ ≤ M_β * γ k.val z * (η * (‖G₁ z‖ + M_J * ‖G₂ z‖)) :=
                      mul_le_mul
                        (mul_le_mul_of_nonneg_right (hM_β_bound z) (hγ_nonneg k.val z))
                        (mul_le_mul hJdiff.le (hz_pt k) (norm_nonneg _) hη.le)
                        (by positivity) (mul_nonneg hM_β_nonneg (hγ_nonneg k.val z))
                  _ = (M_β * η) * γ k.val z * (‖G₁ z‖ + M_J * ‖G₂ z‖) := by ring
            · simp only [image_eq_zero_of_notMem_tsupport hzb, abs_zero, zero_mul]
              exact mul_nonneg (mul_nonneg (mul_nonneg hM_β_nonneg hη.le) (hγ_nonneg k.val z))
                (add_nonneg (norm_nonneg _) (mul_nonneg hM_J0_nonneg (norm_nonneg _)))
        _ = (M_β * η) * (∑ k ∈ F'.attach, γ k.val z) *
              (‖G₁ z‖ + M_J * ‖G₂ z‖) := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ = (M_β * η) * (∑ k ∈ F', γ k z) * (‖G₁ z‖ + M_J * ‖G₂ z‖) := by
            rw [Finset.sum_attach F' (fun k ↦ γ k z)]
        _ ≤ (M_β * η) * 1 * (‖G₁ z‖ + M_J * ‖G₂ z‖) := by gcongr; exact hsum_γ_le z
        _ = (M_β * η) * (‖G₁ z‖ + M_J * ‖G₂ z‖) := by ring
    have heLp : eLpNorm (E h) 2 (volume.restrict U) ≤
        ENNReal.ofReal (M_β * η) * (eLpNorm G₁ 2 (volume.restrict U) +
          ENNReal.ofReal M_J * eLpNorm G₂ 2 (volume.restrict U)) := by
      have h1 : eLpNorm (E h) 2 (volume.restrict U) ≤ eLpNorm
          ((M_β * η) • fun z ↦ ‖G₁ z‖ + M_J • ‖G₂ z‖) 2 (volume.restrict U) :=
        eLpNorm_mono_ae (Lp.aestronglyMeasurable (E h)) (hE_pt.mono fun z hz ↦ by
          have hnn : 0 ≤ (M_β * η) * (‖G₁ z‖ + M_J * ‖G₂ z‖) := by positivity
          simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg hnn] using hz)
      have h2 := eLpNorm_const_smul (M_β * η) (fun z ↦ ‖G₁ z‖ + M_J • ‖G₂ z‖) 2
        (volume.restrict U)
      rw [Real.eNorm_of_nonneg (mul_nonneg hM_β_nonneg hη.le)] at h2
      have h3 : eLpNorm (fun z ↦ ‖G₁ z‖ + M_J • ‖G₂ z‖) 2 (volume.restrict U) ≤
          eLpNorm (fun z ↦ ‖G₁ z‖) 2 (volume.restrict U) +
            eLpNorm (M_J • fun z ↦ ‖G₂ z‖) 2 (volume.restrict U) :=
        eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h4 := eLpNorm_const_smul M_J (fun z ↦ ‖G₂ z‖) 2 (volume.restrict U)
      rw [Real.eNorm_of_nonneg hM_J0_nonneg, eLpNorm_norm _ (Lp.aestronglyMeasurable G₂)] at h4
      rw [h4, eLpNorm_norm _ (Lp.aestronglyMeasurable G₁)] at h3
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left h3 bot_le)
    have hnorm : ‖E h‖ ≤ (M_β * η) * (‖G₁‖ + M_J * ‖G₂‖) := by
      have hne : ENNReal.ofReal (M_β * η) * (eLpNorm G₁ 2 (volume.restrict U) +
          ENNReal.ofReal M_J * eLpNorm G₂ 2 (volume.restrict U)) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.add_ne_top.2 ⟨(Lp.memLp G₁).eLpNorm_ne_top,
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp G₂).eLpNorm_ne_top⟩)
      have htoReal := ENNReal.toReal_mono hne heLp
      rw [← Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_add (Lp.memLp G₁).eLpNorm_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp G₂).eLpNorm_ne_top),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hM_β_nonneg hη.le),
        ENNReal.toReal_ofReal hM_J0_nonneg, ← Lp.norm_def, ← Lp.norm_def] at htoReal
      exact htoReal
    have hG₁ : ‖G₁‖ ≤ ‖liftOp V T_st‖ * ‖h‖ :=
      (norm_Lp_toLp_restrict_le U _).trans
        (((liftOp V T_st).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_extLp_le hρ.isOpen h)
          (norm_nonneg _)))
    have hG₂ : ‖G₂‖ ≤ ‖liftOp V T_tt‖ * ‖h‖ :=
      (norm_Lp_toLp_restrict_le U _).trans
        (((liftOp V T_tt).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_extLp_le hρ.isOpen h)
          (norm_nonneg _)))
    calc ‖E h‖
        ≤ (M_β * η) * (‖liftOp V T_st‖ * ‖h‖ + M_J * (‖liftOp V T_tt‖ * ‖h‖)) :=
          hnorm.trans (mul_le_mul_of_nonneg_left (add_le_add hG₁
            (mul_le_mul_of_nonneg_left hG₂ hM_J0_nonneg)) (mul_nonneg hM_β_nonneg hη.le))
      _ = M_β * (‖liftOp V T_st‖ + M_J * ‖liftOp V T_tt‖) * η * ‖h‖ := by ring
      _ ≤ C_op * η * ‖h‖ := by gcongr; linarith
      _ = ε * ‖h‖ := by rw [show C_op * η = ε from mul_div_cancel₀ ε hC_op.ne']
  refine ⟨P, K, E, hK, hE_norm, fun h ↦ ?_⟩
  set D := jetOperator (volume.restrict U) (fun z ↦ firstOrderJetCoeff (J z) (C z))
  have hDP : D ((P h : H1 V U ρ) : Lp (V × V × V) 2 (volume.restrict U)) =
      ∑ k ∈ F'.attach, D ((localParametrix hρ (hγ_cd k.val) (hγ_supp k.val) (hγ_U k.val)
        (J (center k.val)) h : H1 V U ρ) : Lp (V × V × V) 2 (volume.restrict U)) := by
    have hP_coe : ((P h : H1 V U ρ) : Lp (V × V × V) 2 (volume.restrict U)) =
        ∑ k ∈ F'.attach, ((localParametrix hρ (hγ_cd k.val) (hγ_supp k.val) (hγ_U k.val)
          (J (center k.val)) h : H1 V U ρ) : Lp (V × V × V) 2 (volume.restrict U)) := by
      simp [P]
    rw [hP_coe, map_sum]
  have hDP_ae :
      ⇑(D ((P h : H1 V U ρ) : Lp (V × V × V) 2 (volume.restrict U))) =ᵐ[volume.restrict U]
      ∑ k ∈ F'.attach, fun z ↦ ⇑(D ((localParametrix hρ (hγ_cd k.val) (hγ_supp k.val)
        (hγ_U k.val) (J (center k.val)) h : H1 V U ρ) :
        Lp (V × V × V) 2 (volume.restrict U))) z := by
    rw [hDP]; exact (Lp.coeFn_finsetSum F'.attach _).trans (.of_forall fun _ ↦ rfl)
  have hK_ae : ⇑(K h) =ᵐ[volume.restrict U]
      ∑ k ∈ F'.attach, fun z ↦ ⇑(K_k k.val k.property h) z := by
    change ⇑((∑ k ∈ F'.attach, K_k k.val k.property) h) =ᵐ[volume.restrict U] _
    rw [sum_apply]
    exact (Lp.coeFn_finsetSum F'.attach _).trans (.of_forall fun _ ↦ rfl)
  have hE_ae' : ⇑(E h) =ᵐ[volume.restrict U]
      ∑ k ∈ F'.attach, fun z ↦ ⇑(E_k k.val k.property h) z := by
    change ⇑((∑ k ∈ F'.attach, E_k k.val k.property) h) =ᵐ[volume.restrict U] _
    rw [sum_apply]
    exact (Lp.coeFn_finsetSum F'.attach _).trans (.of_forall fun _ ↦ rfl)
  filter_upwards [hDP_ae, hK_ae, hE_ae', ae_all_iff.2 fun k : F' ↦ hD_ae k.val k.property h]
    with z hzD hzK hzE hzterm
  rw [hzD, hzK, hzE]
  simp only [Finset.sum_apply]
  have hsum_step : (∑ k ∈ F'.attach, ⇑(D ((localParametrix hρ (hγ_cd k.val) (hγ_supp k.val)
      (hγ_U k.val) (J (center k.val)) h : H1 V U ρ) :
      Lp (V × V × V) 2 (volume.restrict U))) z) =
      ∑ k ∈ F'.attach, ((β₀ z * γ k.val z) • h z + ⇑(K_k k.val k.property h) z +
        ⇑(E_k k.val k.property h) z) :=
    Finset.sum_congr rfl fun k _ ↦ hzterm k
  rw [hsum_step, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_smul,
    Finset.sum_attach (f := fun k ↦ β₀ z * γ k z), hsum_mul_γ z]

end LocalParametrix

end TauCeti.ConformalSobolev
