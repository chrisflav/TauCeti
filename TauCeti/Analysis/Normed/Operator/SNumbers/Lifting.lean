/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.Normed.Module.Ball.Surjection

/-!
# Pietsch's lifting identity

The Kolmogorov numbers of `T : E →L[𝕜] F` are the approximation numbers of `T ∘L Q`, where `Q` is
the canonical contractive surjection from scalar-valued `ℓ¹` on the closed unit ball of `E` onto
`E`. Thus Kolmogorov numbers become approximation numbers after presenting the Banach domain as a
metric quotient of its canonical `ℓ¹` space, dual to Pietsch's embedding identity for Gelfand
numbers.

The lower bound holds for every metric quotient map onto the domain over any nontrivially normed
field, with seminormed spaces and no completeness assumptions: precomposing with a metric quotient
map preserves Kolmogorov numbers, and Kolmogorov numbers are bounded by approximation numbers.

For the reverse bound over a complete densely normed field, any subspace `V ≤ F` of rank at most
`n` whose quotient norm `‖V.mkQL ∘L T‖` is small brings the image of the closed unit ball of `E`
uniformly close to `V`. Because `V` is finite-dimensional over a complete scalar field, `V` is
complete even when `F` is not, so uniformly bounded approximants inside `V` sum on `ℓ¹` to an
operator of rank at most `n` close in operator norm to `T ∘L Q`. Completeness of `𝕜` is essential:
over an incomplete field such as `ℚ`, a one-dimensional subspace can be dense in an
infinite-dimensional codomain, collapsing `d₁` to zero while `a₁` remains positive.

## Main declarations

* `ContinuousLinearMap.kolmogorovNumber_le_singularValue`: Kolmogorov numbers are bounded by
  approximation numbers over every nontrivially normed field.
* `ContinuousLinearMap.kolmogorovNumber_le_singularValue_comp`: Kolmogorov numbers are bounded by
  approximation numbers after precomposition with any metric quotient map.
* `ContinuousLinearMap.kolmogorovNumber_comp_unitBallSurjection`: precomposing with
  `TauCeti.unitBallSurjection` preserves Kolmogorov numbers.
* `ContinuousLinearMap.singularValue_comp_unitBallSurjection`: **Pietsch's lifting identity**,
  `(T ∘L TauCeti.unitBallSurjection 𝕜 E).singularValue n = T.kolmogorovNumber n`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped ENNReal NNReal

namespace ContinuousLinearMap

section LowerBound

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Kolmogorov numbers are bounded by approximation numbers over any nontrivially normed field,
without completeness assumptions. -/
theorem kolmogorovNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n ≤ T.singularValue n := by
  refine le_singularValue_iff.mpr fun R hR ↦ ?_
  have h := R.kolmogorovNumber_add_le (T - R) n
  simpa [kolmogorovNumber_eq_zero_of_rank_le hR] using h

/-- Kolmogorov numbers are bounded by approximation numbers after precomposition with any metric
quotient map onto the domain. -/
theorem kolmogorovNumber_le_singularValue_comp (T : F →L[𝕜] G) {Q : E →L[𝕜] F}
    (hQ₁ : ‖Q‖ ≤ 1) (hQ : ∀ r, Metric.ball (0 : F) r ⊆ Q '' Metric.ball 0 r) (n : ℕ) :
    T.kolmogorovNumber n ≤ (T ∘L Q).singularValue n :=
  T.kolmogorovNumber_comp_of_ball_subset_image_ball hQ₁ hQ n ▸
    (T ∘L Q).kolmogorovNumber_le_singularValue n

end LowerBound

section Invariance

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Precomposing with `TauCeti.unitBallSurjection` preserves Kolmogorov numbers. -/
@[simp]
theorem kolmogorovNumber_comp_unitBallSurjection (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L TauCeti.unitBallSurjection 𝕜 E).kolmogorovNumber n = T.kolmogorovNumber n :=
  T.kolmogorovNumber_comp_of_ball_subset_image_ball (TauCeti.norm_unitBallSurjection_le 𝕜 E)
    (TauCeti.ball_subset_image_unitBallSurjection_ball 𝕜 E) n

end Invariance

section Lifting

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Pietsch's lifting identity.** Kolmogorov numbers are the approximation numbers after
precomposition with the canonical surjection from `ℓ¹` of the closed unit ball of the domain. -/
theorem singularValue_comp_unitBallSurjection (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L TauCeti.unitBallSurjection 𝕜 E).singularValue n = T.kolmogorovNumber n := by
  let Q := TauCeti.unitBallSurjection 𝕜 E
  refine le_antisymm
    (le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_)
    (T.kolmogorovNumber_le_singularValue_comp (TauCeti.norm_unitBallSurjection_le 𝕜 E)
      (TauCeti.ball_subset_image_unitBallSurjection_ball 𝕜 E) n)
  obtain ⟨V, hV, hVc⟩ := exists_nnnorm_mkQL_comp_lt_of_kolmogorovNumber_lt hc
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  have happrox (x : Metric.closedBall (0 : E) 1) :
      ∃ w : V, ‖T x.1 - (w : F)‖₊ ≤ c ∧ ‖w‖₊ ≤ ‖T‖₊ + c := by
    have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    have hx_lt : ‖V.mkQL (T x.1)‖ < (c : ℝ) :=
      (((V.mkQL ∘L T).le_opNorm x.1).trans (mul_le_of_le_one_right (norm_nonneg _) hx)).trans_lt
        (NNReal.coe_lt_coe.mpr hVc)
    obtain ⟨y, hy, hyn⟩ := Submodule.Quotient.norm_mk_lt (V.mkQL (T x.1)) (sub_pos.mpr hx_lt)
    have hw_mem : T x.1 - y ∈ V := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [sub_eq_zero] using hy.symm
    have hyn' : ‖y‖₊ ≤ c := by
      rw [← NNReal.coe_le_coe, coe_nnNorm]
      linarith
    have hTx : ‖T x.1‖ ≤ ‖T‖ :=
      (T.le_opNorm x.1).trans (mul_le_of_le_one_right (norm_nonneg T) hx)
    refine ⟨⟨T x.1 - y, hw_mem⟩, ?_, ?_⟩
    · simpa [sub_sub_cancel] using hyn'
    · rw [← NNReal.coe_le_coe, coe_nnNorm, ← Submodule.norm_coe, NNReal.coe_add, coe_nnNorm]
      exact (norm_sub_le (T x.1) y).trans (by linarith)
  choose w hw_err hw_bound using happrox
  let L₀ := coprodLpOne (fun x ↦ toSpanSingleton 𝕜 (w x)) (‖T‖₊ + c) fun x ↦ by
    simpa [← NNReal.coe_le_coe, coe_nnNorm] using hw_bound x
  let L := V.subtypeL ∘L L₀
  have hL_rank : L.rank ≤ n := by
    have hrange : LinearMap.range L.toLinearMap ≤ V :=
      (LinearMap.range_comp_le_range L₀.toLinearMap V.subtype).trans_eq V.range_subtype
    exact (Submodule.rank_mono hrange).trans hV
  classical
  refine ((T ∘L Q).singularValue_le_nnnorm_sub hL_rank).trans ?_
  refine (T ∘L Q - L).opNNNorm_le_of_lp_single c fun x a ↦ ?_
  calc ‖(T ∘L Q - L) (lp.single 1 x a)‖₊
      = ‖a • (T x.1 - (w x : F))‖₊ := by
        simp [Q, L, L₀, smul_sub]
    _ = ‖a‖₊ * ‖T x.1 - (w x : F)‖₊ := nnNorm_smul a _
    _ ≤ c * ‖a‖₊ := by
        rw [mul_comm]
        gcongr
        exact hw_err x

end Lifting

end ContinuousLinearMap
