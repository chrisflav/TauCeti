/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import TauCeti.Analysis.Normed.Ring.ProdSubProd
import TauCeti.Analysis.SpecialFunctions.Exp.ImaginaryTaylor
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation

/-!
# The Lindeberg–Feller central limit theorem

Let `X n i`, for `n : ℕ` and `i : ι n` with `ι n` finite, be real random variables, the `n`th row
living on a probability space `(Ω n, P n)`, such that

* for each `n`, the row `X n` is independent;
* each `X n i` is centred and square integrable;
* the row variances `∑ i, Var[X n i; P n]` converge to a limiting variance `v : ℝ≥0`;
* the **Lindeberg condition** holds: for every `ε > 0`,
  `∑ i, E[X n i ^ 2; ε ≤ |X n i|] → 0` as `n → ∞`.

Then the row sums `∑ i, X n i` converge in distribution to the centred Gaussian law with variance
`v` (including the degenerate case `v = 0`). Neither boundedness nor identical distribution is
assumed, and different rows need not live on a common space, which is what makes the theorem apply
to triangular arrays such as sums of independent indicators with varying success probabilities.

The main consequence proved here is the central limit theorem for bounded independent summands
whose variance tends to infinity: if every centred summand `X n i - E[X n i]` is bounded by a
fixed constant `C` and `∑ i, Var[X n i] → ∞`, then the centred row sum divided by its standard
deviation converges in distribution to the standard Gaussian law. Sums of independent Bernoulli
variables with diverging variance are the basic example.

## Main results

* `MeasureTheory.MemLp.norm_charFun_sub_one_sub_le`: the truncation estimate
  `‖φ_X t - (1 - t² E[X²] / 2)‖ ≤ |t|³ ε E[X²] / 6 + t² E[X²; ε ≤ |X|]` for a centred `X ∈ L²`.
* `MeasureTheory.MemLp.norm_charFun_sub_exp_le`: the global Gaussian comparison
  `‖φ_X t - exp (-t² E[X²] / 2)‖ ≤ t² E[X²] / √2` for a centred `X ∈ L²`.
* `TauCeti.Probability.norm_prod_charFun_sub_exp_le`: the product of the characteristic
  functions of one row is close to `exp (-t² V / 2)`, where `V = ∑ i, E[Y i ^ 2]`, with an
  explicit error.
* `ProbabilityTheory.HasLaw.tendstoInDistribution_sum_of_lindeberg`: the Lindeberg–Feller theorem
  (sufficiency direction) for any limiting variance `v : ℝ≥0`.
* `ProbabilityTheory.HasLaw.tendstoInDistribution_sum_sub_div_sqrt_of_abs_sub_le`: the central
  limit theorem for uniformly bounded independent summands with diverging variance.

## Implementation notes

The proof goes through characteristic functions and Lévy's continuity theorem, as in Mathlib's
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`. Writing `σᵢ² = E[X n i ^ 2]` and
`V = ∑ i, σᵢ²`, each factor `φ_{X n i} t` is compared with `exp (-t² σᵢ² / 2)` rather than with
`1 - t² σᵢ² / 2`: both have norm at most `1`, and the product of the Gaussian factors is exactly
`exp (-t² V / 2)`. The error `(t² σᵢ² / 2) ^ 2 / 2` from `exp (-u) ≈ 1 - u` is summed using
`σᵢ² ≤ ε² + E[X n i ^ 2; ε ≤ |X n i|]`, so the intermediate statement `maxᵢ σᵢ² → 0` is never
needed separately, and `exp (-t² V / 2) → exp (-t² v / 2)` covers both `v > 0` and `v = 0`
uniformly.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Section 27, Theorem 27.2.
* J. W. Lindeberg, Eine neue Herleitung des Exponentialgesetzes in der
  Wahrscheinlichkeitsrechnung, *Mathematische Zeitschrift* 15 (1922), 211–225.
* W. Feller, Über den zentralen Grenzwertsatz der Wahrscheinlichkeitsrechnung,
  *Mathematische Zeitschrift* 40 (1935), 521–559.

## Tags

central limit theorem, Lindeberg condition, triangular array
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Real Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}

/-- The characteristic function of a centred random variable `X` with finite variance agrees
with `1 - t² E[X²] / 2` up to an error controlled by `ε` and the truncated second moment
`E[X²; ε ≤ |X|]`. -/
theorem MemLp.norm_charFun_sub_one_sub_le (hX : MemLp X 2 P) (h0 : P[X] = 0) (t : ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ‖charFun (P.map X) t - (1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2)‖ ≤
      |t| ^ 3 * ε / 6 * ∫ ω, X ω ^ 2 ∂P +
        t ^ 2 * ∫ ω, ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω ∂P := by
  have hm : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
  have hint1 : Integrable X P := hX.integrable one_le_two
  have hint2 : Integrable (fun ω ↦ X ω ^ 2) P := hX.integrable_sq
  have hind := hX.integrable_indicator_sq ε
  have hexp : Integrable (fun ω ↦ Complex.exp (↑(t * X ω) * Complex.I)) P := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun ω ↦ ?_)
    exact (Complex.norm_exp_ofReal_mul_I _).le
  have ha : Integrable (fun ω ↦ 1 - (t * X ω) ^ 2 / 2) P :=
    ((integrable_const 1).sub ((hint2.const_mul (t ^ 2)).div_const 2)).congr
      (ae_of_all _ fun ω ↦ by simp [mul_pow])
  have hb : Integrable (fun ω ↦ t * X ω) P := hint1.const_mul t
  have hF : Integrable
      (fun ω ↦ ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ↑(t * X ω) * Complex.I) P :=
    ha.ofReal.add (hb.ofReal.mul_const _)
  -- the characteristic function and the quadratic polynomial as expectations
  have hφ : charFun (P.map X) t = ∫ ω, Complex.exp (↑(t * X ω) * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hm (by fun_prop)]
    simp
  have hE : ((1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 : ℝ) : ℂ) =
      ∫ ω, (((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ↑(t * X ω) * Complex.I) ∂P := by
    rw [integral_add ha.ofReal (hb.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal, integral_const_mul, h0,
      integral_sub (integrable_const _) ((hint2.const_mul (t ^ 2)).div_const 2 |>.congr
        (ae_of_all _ fun ω ↦ by simp [mul_pow]))]
    simp [integral_div, mul_pow, integral_const_mul]
  have hE' : (1 - (t : ℂ) ^ 2 * ((∫ ω, X ω ^ 2 ∂P : ℝ) : ℂ) / 2) =
      ∫ ω, (((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ↑(t * X ω) * Complex.I) ∂P := by
    rw [← hE]
    push_cast
    ring
  have hbd : Integrable (fun ω ↦ |t| ^ 3 * ε / 6 * X ω ^ 2 +
      t ^ 2 * ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω) P :=
    (hint2.const_mul _).add (hind.const_mul _)
  rw [hφ, hE', ← integral_sub hexp hF, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hint2.const_mul _) (hind.const_mul _)]
  refine norm_integral_le_of_norm_le hbd (ae_of_all _ fun ω ↦ ?_)
  -- pointwise: the cubic bound where `|X| < ε`, the quadratic bound where `ε ≤ |X|`
  have hrw : Complex.exp (↑(t * X ω) * Complex.I) -
      (((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ↑(t * X ω) * Complex.I) =
      Complex.exp (↑(t * X ω) * Complex.I) -
        (1 + ↑(t * X ω) * Complex.I - ↑(t * X ω) ^ 2 / 2) := by
    push_cast
    ring
  rw [hrw]
  have h3 : 0 ≤ |t| ^ 3 * ε / 6 * X ω ^ 2 := by positivity
  by_cases hω : ε ≤ |X ω|
  · rw [Set.indicator_of_mem (s := {ω | ε ≤ |X ω|}) hω]
    have := TauCeti.norm_exp_ofReal_mul_I_sub_le_sq (t * X ω)
    rw [mul_pow] at this
    linarith
  · rw [Set.indicator_of_notMem (s := {ω | ε ≤ |X ω|}) hω, mul_zero, add_zero]
    refine (TauCeti.norm_exp_ofReal_mul_I_sub_le_cube (t * X ω)).trans ?_
    have hX3 : |X ω| ^ 3 ≤ ε * X ω ^ 2 := by
      rw [← sq_abs (X ω), pow_succ, mul_comm]
      gcongr
      exact (not_le.mp hω).le
    rw [abs_mul, mul_pow]
    have ht3 : 0 ≤ |t| ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hX3 ht3]

/-- The characteristic function of a centred square-integrable random variable `X` differs from the
matching Gaussian characteristic function `exp (-t² E[X²] / 2)` by at most `t² E[X²] / √2`. -/
theorem MemLp.norm_charFun_sub_exp_le (hX : MemLp X 2 P) (h0 : P[X] = 0) (t : ℝ) :
    ‖charFun (P.map X) t - (Real.exp (-(t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2)) : ℂ)‖ ≤
      t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / √2 := by
  set σ : ℝ := ∫ ω, X ω ^ 2 ∂P
  set R : ℝ := t ^ 2 * σ / 2
  have : 0 ≤ σ := integral_nonneg fun _ ↦ sq_nonneg _
  have hR0 : 0 ≤ R := by positivity
  have hm : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
  have hint1 : Integrable (fun ω ↦ t * X ω) P := (hX.integrable one_le_two).const_mul t
  have hφ : charFun (P.map X) t = ∫ ω, Complex.exp (↑(t * X ω) * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hm (by fun_prop)]; simp
  have hexp : Integrable (fun ω ↦ Complex.exp (↑(t * X ω) * Complex.I)) P :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop)
      (ae_of_all _ fun ω ↦ (Complex.norm_exp_ofReal_mul_I _).le)
  have hlin : Integrable (fun ω ↦ (1 : ℂ) + ↑(t * X ω) * Complex.I) P :=
    (integrable_const 1).add (hint1.ofReal.mul_const _)
  have hlin_int : ∫ ω, ((1 : ℂ) + ↑(t * X ω) * Complex.I) ∂P = 1 := by
    rw [integral_add (integrable_const 1) (hint1.ofReal.mul_const _), integral_const,
      probReal_univ, one_smul, integral_mul_const, integral_complex_ofReal, integral_const_mul, h0]
    simp
  set w : ℂ := charFun (P.map X) t - 1
  set r : ℝ := 1 - Real.exp (-R)
  have hw_norm : ‖w‖ ≤ R := by
    have hhi : Integrable (fun ω ↦ (t * X ω) ^ 2 / 2) P := by
      simpa only [mul_pow] using (hX.integrable_sq.const_mul (t ^ 2)).div_const 2
    have hw_eq : w = ∫ ω, (Complex.exp (↑(t * X ω) * Complex.I) -
        (1 + ↑(t * X ω) * Complex.I)) ∂P := by rw [integral_sub hexp hlin, ← hφ, hlin_int]
    rw [hw_eq]
    refine (norm_integral_le_of_norm_le hhi (ae_of_all _ fun ω ↦ ?_)).trans_eq ?_
    · have h2 := TauCeti.norm_exp_ofReal_mul_I_sub_sum_le 2 (t * X ω)
      have hs : ∑ k ∈ Finset.range 2, ((↑(t * X ω) : ℂ) * Complex.I) ^ k / (Nat.factorial k : ℂ) =
          1 + ↑(t * X ω) * Complex.I := by simp [Finset.sum_range_succ]
      rw [hs, sq_abs] at h2
      simpa [Nat.factorial] using h2
    · simp only [mul_pow, integral_div, integral_const_mul, R, σ]
  have hw_re : w.re ≤ 0 := by
    have hle : (charFun (P.map X) t).re ≤ 1 :=
      (Complex.re_le_norm _).trans (norm_charFun_le_one t)
    simp only [w, Complex.sub_re, Complex.one_re]; linarith
  have hr0 : 0 ≤ r := sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith))
  have hrR : r ≤ R := by linarith [Real.add_one_le_exp (-R)]
  have hwr : charFun (P.map X) t - (Real.exp (-R) : ℂ) = w + (r : ℂ) := by
    simp only [w, r]; push_cast; ring
  rw [hwr]
  have hsq : ‖w + (r : ℂ)‖ ^ 2 ≤ (t ^ 2 * σ / √2) ^ 2 := by
    have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg w]
    have hR2 : (t ^ 2 * σ) ^ 2 / 2 = 2 * R ^ 2 := by simp only [R]; ring
    rw [Complex.sq_norm, Complex.normSq_apply] at hw2 ⊢
    rw [div_pow, Real.sq_sqrt zero_le_two, hR2]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hr0 hw_re]
  exact le_of_sq_le_sq hsq (by positivity)

end MeasureTheory

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Row estimate for the Lindeberg–Feller theorem: for a finite family of centred
square-integrable random variables with summed second moment `V = ∑ i, E[Y i ^ 2]`, the product
of their characteristic functions is within `(|t|³ ε / 6 + t⁴ ε² / 8) V + (t² + t⁴ V / 8) Lε`
of `exp (-t² V / 2)`, where `Lε = ∑ i, E[Y i ^ 2; ε ≤ |Y i|]` is the Lindeberg sum. -/
theorem norm_prod_charFun_sub_exp_le {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ}
    (hL2 : ∀ i, MemLp (Y i) 2 P) (h0 : ∀ i, P[Y i] = 0) (t ε : ℝ) :
    ‖∏ i, charFun (P.map (Y i)) t -
        (Real.exp (-(t ^ 2 * (∑ i, ∫ ω, Y i ω ^ 2 ∂P) / 2)) : ℂ)‖ ≤
      (|t| ^ 3 * ε / 6 + t ^ 4 / 8 * ε ^ 2) * (∑ i, ∫ ω, Y i ω ^ 2 ∂P) +
        (t ^ 2 + t ^ 4 / 8 * (∑ i, ∫ ω, Y i ω ^ 2 ∂P)) *
          (∑ i, ∫ ω, ({ω | ε ≤ |Y i ω|}.indicator fun ω ↦ Y i ω ^ 2) ω ∂P) := by
  set σ : ι → ℝ := fun i ↦ ∫ ω, Y i ω ^ 2 ∂P
  set Li : ι → ℝ := fun i ↦ ∫ ω, ({ω | ε ≤ |Y i ω|}.indicator fun ω ↦ Y i ω ^ 2) ω ∂P
  set L : ℝ := ∑ i, Li i
  have hσ0 (i : ι) : 0 ≤ σ i := integral_nonneg fun _ ↦ sq_nonneg _
  have hprod : (Real.exp (-(t ^ 2 * (∑ i, σ i) / 2)) : ℂ) =
      ∏ i, ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum]; congr 2
    rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hprod]
  refine (norm_prod_sub_prod_le_sum_norm_sub _ (fun i _ ↦ norm_charFun_le_one t) fun i _ ↦ by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    nlinarith [hσ0 i, sq_nonneg t]).trans ?_
  rcases le_or_gt 0 ε with hε | hε
  · have hσL (i : ι) : σ i ≤ ε ^ 2 + L := ((hL2 i).integral_sq_le_sq_add_integral_indicator ε).trans
      (by linarith [Finset.single_le_sum (f := Li) (fun j _ ↦ integral_nonneg fun _ ↦
        Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _) (Finset.mem_univ i)])
    have hterm (i : ι) : ‖charFun (P.map (Y i)) t - ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ)‖ ≤
        |t| ^ 3 * ε / 6 * σ i + t ^ 2 * Li i + t ^ 4 / 8 * (ε ^ 2 + L) * σ i := by
      have h3 : ‖(1 - (t : ℂ) ^ 2 * (σ i : ℂ) / 2) - ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ)‖ ≤
          (t ^ 2 * σ i / 2) ^ 2 / 2 := by
        have hcast : (1 - (t : ℂ) ^ 2 * (σ i : ℂ) / 2) = ((1 - t ^ 2 * σ i / 2 : ℝ) : ℂ) := by
          push_cast; rfl
        rw [hcast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
          abs_of_nonneg (by linarith [Real.add_one_le_exp (-(t ^ 2 * σ i / 2))])]
        nlinarith [Real.exp_le_one_add_add_sq_div_two_of_nonpos
          (by nlinarith [hσ0 i, sq_nonneg t] : -(t ^ 2 * σ i / 2) ≤ 0)]
      nlinarith [(hL2 i).norm_charFun_sub_one_sub_le (h0 i) t hε,
        mul_le_mul_of_nonneg_right (hσL i) (hσ0 i), pow_nonneg (sq_nonneg t) 2,
        norm_sub_le_norm_sub_add_norm_sub (charFun (P.map (Y i)) t)
          (1 - (t : ℂ) ^ 2 * (σ i : ℂ) / 2) ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ)]
    refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  · have hL_eq : L = ∑ i, σ i := Finset.sum_congr rfl fun i _ ↦
      integral_congr_ae (ae_of_all _ fun _ ↦ Set.indicator_of_mem (hε.le.trans (abs_nonneg _)) _)
    have hV0 : 0 ≤ ∑ i, σ i := Finset.sum_nonneg fun i _ ↦ hσ0 i
    have hsqrt2 : (1 : ℝ) / √2 ≤ 17 / 18 := (div_le_iff₀ (Real.sqrt_pos.2 zero_lt_two)).2
      (by nlinarith [Real.sq_sqrt zero_le_two, Real.sqrt_nonneg 2])
    have hsum : ∑ i, ‖charFun (P.map (Y i)) t - ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ)‖ ≤
        17 / 18 * t ^ 2 * ∑ i, σ i := by
      refine (Finset.sum_le_sum fun i _ ↦ (hL2 i).norm_charFun_sub_exp_le (h0 i) t).trans ?_
      rw [← Finset.sum_div, ← Finset.mul_sum]
      simpa only [one_div_mul_eq_div, mul_assoc] using
        mul_le_mul_of_nonneg_right hsqrt2 (mul_nonneg (sq_nonneg t) hV0)
    have hq : 0 ≤ t ^ 2 * (1 / 18 + |t| * ε / 6 + t ^ 2 * ε ^ 2 / 8) :=
      mul_nonneg (sq_nonneg t) (by nlinarith [sq_nonneg (3 * |t| * ε + 2), sq_abs t])
    have hpow : |t| ^ 3 = t ^ 2 * |t| := by rw [pow_succ', sq_abs, mul_comm]
    have ht4 : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [hL_eq, hpow, ht4]
    nlinarith [hsum, mul_nonneg hq hV0, mul_nonneg (sq_nonneg (t ^ 2)) (sq_nonneg (∑ i, σ i))]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)} {P : (n : ℕ) → Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (P n)]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Y : Ω' → ℝ}

/-- **Lindeberg–Feller central limit theorem** (sufficiency direction). Let `X n i`, `i : ι n`,
be a triangular array of real random variables, the `n`th row on its own probability space
`(Ω n, P n)`. Suppose the rows are independent, centred and square integrable, with row variances
`∑ i, Var[X n i; P n]` converging to `v : ℝ≥0`. If the Lindeberg condition
`∑ i, E[X n i ^ 2; ε ≤ |X n i|] → 0` holds for every `ε > 0`, then the row sums converge in
distribution to a centred Gaussian random variable `Y` with variance `v` (including the degenerate
case `v = 0`). -/
theorem HasLaw.tendstoInDistribution_sum_of_lindeberg {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {X : (n : ℕ) → ι n → Ω n → ℝ} {v : ℝ≥0}
    (hY : HasLaw Y (gaussianReal 0 v) P')
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hL2 : ∀ n i, MemLp (X n i) 2 (P n))
    (h0 : ∀ n i, (P n)[X n i] = 0)
    (hvar : Tendsto (fun n ↦ ∑ i, Var[X n i; P n]) atTop (𝓝 (v : ℝ)))
    (hlind : ∀ ε > 0, Tendsto
      (fun n ↦ ∑ i, (P n)[{ω | ε ≤ |X n i ω|}.indicator (fun ω ↦ X n i ω ^ 2)]) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop Y P P' where
  forall_aemeasurable n :=
    Finset.aemeasurable_fun_sum _ fun i _ ↦ (hL2 n i).aestronglyMeasurable.aemeasurable
  tendsto := by
    have hm n i : AEMeasurable (X n i) (P n) := (hL2 n i).aestronglyMeasurable.aemeasurable
    set V : ℕ → ℝ := fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂(P n)
    have hV : Tendsto V atTop (𝓝 (v : ℝ)) := hvar.congr fun n ↦
      Finset.sum_congr rfl fun i _ ↦ variance_of_integral_eq_zero (hm n i) (h0 n i)
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    rw! [hY.map_eq]
    have hexp : Tendsto (fun n ↦ ((Real.exp (-(t ^ 2 * V n / 2)) : ℝ) : ℂ)) atTop
        (𝓝 (charFun (gaussianReal 0 v) t)) := by
      have hG : charFun (gaussianReal 0 v) t = ((Real.exp (-(t ^ 2 * (v : ℝ) / 2)) : ℝ) : ℂ) := by
        rw [charFun_gaussianReal]; push_cast; ring_nf
      rw [hG]
      exact ((by fun_prop : Continuous fun x : ℝ ↦
        ((Real.exp (-(t ^ 2 * x / 2)) : ℝ) : ℂ)).tendsto (v : ℝ)).comp hV
    suffices hdiff : Tendsto (fun n ↦ ∏ i, charFun ((P n).map (X n i)) t -
        ((Real.exp (-(t ^ 2 * V n / 2)) : ℝ) : ℂ)) atTop (𝓝 0) by
      simpa only [ProbabilityMeasure.coe_mk, (hindep _).charFun_map_fun_sum_eq_prod (hm _),
        Finset.prod_apply, sub_add_cancel, zero_add] using hdiff.add hexp
    rw [tendsto_zero_iff_norm_tendsto_zero]
    set M : ℝ := (v : ℝ) + 1
    set C : ℝ := (|t| ^ 3 + t ^ 4) * M + t ^ 2
    have hC0 : 0 ≤ C := by positivity
    refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
    set ε := min 1 (δ / (2 * (C + 1)))
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hCε : C * ε < δ / 2 := (mul_le_mul_of_nonneg_left (min_le_right _ _) hC0).trans_lt
      (by rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]; nlinarith)
    have hLC := by simpa only [mul_zero] using (hlind ε hε0).const_mul C
    filter_upwards [hLC (Iio_mem_nhds (half_pos hδ)), hV (Iic_mem_nhds (lt_add_one (v : ℝ)))]
      with n hn (hVn : V n ≤ M)
    set L : ℝ := ∑ i, ∫ ω, ({ω | ε ≤ |X n i ω|}.indicator fun ω ↦ X n i ω ^ 2) ω ∂(P n)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    refine (norm_prod_charFun_sub_exp_le (hL2 n) (h0 n) t ε).trans_lt ?_
    have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ ↦
      integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
    have h3 : 0 ≤ |t| ^ 3 * M := by positivity
    have h4 : 0 ≤ t ^ 4 * M := by positivity
    have h1 : (|t| ^ 3 * ε / 6 + t ^ 4 / 8 * ε ^ 2) * V n ≤ C * ε := by
      calc (|t| ^ 3 * ε / 6 + t ^ 4 / 8 * ε ^ 2) * V n
          ≤ (|t| ^ 3 * ε / 6 + t ^ 4 / 8 * ε ^ 2) * M := by gcongr
        _ ≤ (|t| ^ 3 * ε / 6 + t ^ 4 / 8 * ε) * M := by gcongr; nlinarith
        _ ≤ C * ε := by nlinarith [sq_nonneg t, hε0]
    have h2 : (t ^ 2 + t ^ 4 / 8 * V n) * L ≤ C * L := mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left hVn (by positivity : 0 ≤ t ^ 4 / 8)]) hL0
    have hn' : C * L < δ / 2 := hn
    exact (add_le_add h1 h2).trans_lt (by linarith)

/-- **Central limit theorem for bounded summands with diverging variance.** Let the rows of the
triangular array `X n i`, `i : ι n`, be independent, the `n`th row on its own probability space
`(Ω n, P n)`, and suppose every centred summand is bounded: `|X n i - E[X n i]| ≤ C` almost
surely, for one constant `C`. If the row variance `∑ i, Var[X n i]` tends to infinity, then the
centred row sum divided by its standard deviation converges in distribution to a standard Gaussian
random variable `Y`.

For sums of independent indicators of events `A n i` with probabilities `p n i`, the centred
summands are bounded by `1`, so the conclusion holds as soon as `∑ i, p n i (1 - p n i) → ∞`. -/
theorem HasLaw.tendstoInDistribution_sum_sub_div_sqrt_of_abs_sub_le {ι : ℕ → Type*}
    [∀ n, Fintype (ι n)] {X : (n : ℕ) → ι n → Ω n → ℝ}
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hm : ∀ n i, AEMeasurable (X n i) (P n))
    {C : ℝ} (hC : ∀ n i, ∀ᵐ ω ∂(P n), |X n i ω - (P n)[X n i]| ≤ C)
    (hvar : Tendsto (fun n ↦ ∑ i, Var[X n i; P n]) atTop atTop) :
    TendstoInDistribution
      (fun n ω ↦ (∑ i, (X n i ω - (P n)[X n i])) / √(∑ i, Var[X n i; P n])) atTop Y
      P P' := by
  set s : ℕ → ℝ := fun n ↦ √(∑ i, Var[X n i; P n]) with hs
  have hs0 n : 0 ≤ s n := Real.sqrt_nonneg _
  have hcL2 n i : MemLp (fun ω ↦ X n i ω - (P n)[X n i]) 2 (P n) :=
    MemLp.of_bound ((hm n i).sub_const _).aestronglyMeasurable C
      ((hC n i).mono fun ω h ↦ by rwa [Real.norm_eq_abs])
  have hL2 n i : MemLp (X n i) 2 (P n) :=
    ((hcL2 n i).add (memLp_const ((P n)[X n i]))).ae_eq (.of_forall fun ω ↦ sub_add_cancel _ _)
  set Z : (n : ℕ) → ι n → Ω n → ℝ := fun n i ω ↦ (X n i ω - (P n)[X n i]) / s n with hZ
  have hsum : (fun n ω ↦ (∑ i, (X n i ω - (P n)[X n i])) / √(∑ i, Var[X n i; P n])) =
      fun n ω ↦ ∑ i, Z n i ω := by ext n ω; simp only [hZ, hs, Finset.sum_div]
  rw [hsum]
  have hZL2 n i : MemLp (Z n i) 2 (P n) := by
    simpa only [hZ, div_eq_mul_inv] using (hcL2 n i).mul_const (s n)⁻¹
  have hZ0 n i : (P n)[Z n i] = 0 := by
    simp only [hZ]
    rw [integral_div, integral_sub ((hL2 n i).integrable one_le_two) (integrable_const _)]
    simp
  have hs_top : Tendsto s atTop atTop := Real.tendsto_sqrt_atTop.comp hvar
  have hZindep n : iIndepFun (Z n) (P n) := by
    have h := (hindep n).comp (fun (i : ι n) (x : ℝ) ↦ (x - ∫ ω, X n i ω ∂(P n)) / s n)
      fun i ↦ (measurable_id.sub_const _).div_const _
    simpa only [hZ, Function.comp_def] using h
  refine hY.tendstoInDistribution_sum_of_lindeberg hZindep hZL2 hZ0 ?_ fun ε hε ↦ ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hvar.eventually_gt_atTop 0] with n hn
    have hVZ i : Var[Z n i; P n] = Var[X n i; P n] / s n ^ 2 := by
      simp only [hZ, div_eq_mul_inv, variance_mul_const,
        variance_sub_const (hm n i).aestronglyMeasurable, inv_pow]
    simp only [hVZ, ← Finset.sum_div, hs, Real.sq_sqrt hn.le, NNReal.coe_one]
    exact (div_self hn.ne').symm
  · have hCs : Tendsto (fun n ↦ C / s n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hs_top
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hCs (Iio_mem_nhds hε)] with n hn
    symm
    refine Finset.sum_eq_zero fun i _ ↦ integral_eq_zero_of_ae ?_
    filter_upwards [hC n i] with ω hω
    have hZle : |Z n i ω| < ε := by
      calc |Z n i ω| = |X n i ω - (P n)[X n i]| / s n := by
            simp only [hZ, abs_div, abs_of_nonneg (hs0 n)]
        _ ≤ C / s n := div_le_div_of_nonneg_right hω (hs0 n)
        _ < ε := hn
    rw [Pi.zero_apply, Set.indicator_of_notMem (s := {ω | ε ≤ |Z n i ω|}) (not_le.mpr hZle)]

end ProbabilityTheory
