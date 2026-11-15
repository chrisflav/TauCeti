/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Nonpositive
public import TauCeti.NumberTheory.LSeries.Lerch.Series

import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Differential relations, nonpositive-integer rationality, and polylogarithm bridges

On the open unit disc `‖z‖ < 1`, the Euler-type differential operator

`lerchLoweringOp c f z = z * deriv f z + c * f z`

lowers the `s` parameter of `lerchSeries` by `1` whenever `c` avoids nonpositive integers:
`(z ∂_z + c) Φ(z, s, c) = Φ(z, s - 1, c)`. Combined with the `c`-derivative raising relation
`∂_c Φ(z, s, c) = -s Φ(z, s + 1, c)` on `Complex.slitPlane`, this yields the second-order Lerch
partial differential equation `(z ∂_z + c) (∂_c Φ(z, s, c)) = -s Φ(z, s, c)`.

Starting from `Φ(z, 0, c) = (1 - z)⁻¹`, iterating `lerchLoweringOp c` `m` times defines a global
rational function `lerchNegNat m c z = P_m(c, z) / (1 - z) ^ (m + 1)` that agrees with
`lerchSeries z (-m) c` on `‖z‖ < 1` whenever `∀ n : ℕ, (n : ℂ) + c ≠ 0`, is jointly analytic on
`{p : ℂ × ℂ | p.2 ≠ 1}`, and has a pole of exact order `m + 1` with leading coefficient `m!` at
`z = 1` for every `c ∈ ℂ`. At `c = 1`, multiplying by `z` recovers `TauCeti.Polylog.polylog` both in
weight `1` on `‖z‖ < 1` and in all nonpositive integer weights `-m` on all of `ℂ`.

## Main definitions and results

* `TauCeti.lerchLoweringOp`: the operator `z * deriv f z + c * f z`.
* `TauCeti.lerchSeries_lowering`, `TauCeti.lerchLoweringOp_iterate_lerchSeries`: the `s`-lowering
  relation `(z ∂_z + c) Φ(z, s, c) = Φ(z, s - 1, c)` and its iterates.
* `TauCeti.lerchSeries_pde`: `(z ∂_z + c) (∂_c Φ(z, s, c)) = -s Φ(z, s, c)`.
* `TauCeti.lerchNegNat`, `TauCeti.lerchNegNatNum`: rational continuation of `Φ(z, -m, c)` and its
  polynomial numerator in `z`.
* `TauCeti.lerchSeries_neg_nat`, `TauCeti.lerchNegNat_eq_div`, `TauCeti.lerchNegNat_one`:
  agreement with `lerchSeries`, rational closed form `(lerchNegNatNum m c).eval z / (1 - z)^(m+1)`,
  and explicit `m = 1` formula `c / (1 - z) + z / (1 - z) ^ 2`.
* `TauCeti.analyticOnNhd_lerchNegNat`, `TauCeti.tendsto_one_sub_pow_mul_lerchNegNat_nhdsNE_one`:
  joint holomorphy away from `z = 1` and exact pole leading coefficient `m!`.
* `TauCeti.mul_lerchSeries_one_one`, `TauCeti.mul_lerchNegNat_one_eq_polylog`,
  `TauCeti.mul_lerchSeries_neg_nat_one`: specialization bridges to `TauCeti.Polylog.polylog`.

## References

* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function I. Zeta integrals*,
  Forum Math. **24** (2012), 1–48, §3.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  Res. Math. Sci. **3** (2016), Paper No. 2, §§2 and 6.
-/

public section

open Complex Filter Metric Polynomial Set
open scoped Topology

namespace TauCeti

/-! ### The `s`-lowering operator and the Lerch PDE -/

/-- The Euler-type differential operator `(z ∂_z + c) f(z) = z * deriv f z + c * f z` that lowers
the `s` parameter of `lerchSeries` by `1`. -/
noncomputable def lerchLoweringOp (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv f z + c * f z

@[simp]
theorem lerchLoweringOp_apply (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    lerchLoweringOp c f z = z * deriv f z + c * f z :=
  (rfl)

theorem lerchLoweringOp_congr_nhds {c z : ℂ} {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 z] g) :
    lerchLoweringOp c f z = lerchLoweringOp c g z := by
  simp only [lerchLoweringOp, h.deriv_eq, h.eq_of_nhds]

/-- Lowering relation in `s`: on `‖z‖ < 1`, if `c` avoids nonpositive integers
(`∀ n : ℕ, n + c ≠ 0`), then `(z ∂_z + c) Φ(z, s, c) = Φ(z, s - 1, c)`. -/
theorem lerchSeries_lowering {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchLoweringOp c (fun w => lerchSeries w s c) z = lerchSeries z (s - 1) c := by
  rw [lerchLoweringOp, deriv_lerchSeries_left hz s c, ← tsum_mul_left, lerchSeries_def,
    ← tsum_mul_left]
  have hsum1 : Summable fun n : ℕ =>
      z * ((n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c))) :=
    (Summable.of_norm (by simpa using summable_norm_lerchSeries_mul_log_pow hz s c 1 0)).mul_left z
  have hsum2 : Summable fun n : ℕ => c * lerchSeriesTerm n z s c :=
    (summable_lerchSeriesTerm hz s c).mul_left c
  rw [← hsum1.tsum_add hsum2, lerchSeries_def]
  refine tsum_congr fun n => ?_
  have hpow : z * ((n : ℂ) * z ^ (n - 1)) = (n : ℂ) * z ^ n := by
    cases n with
    | zero => simp
    | succ m => simp [pow_succ']; ring
  have hbase : ((n : ℂ) + c) * Complex.exp (-s * Complex.log (n + c)) =
      Complex.exp (-(s - 1) * Complex.log (n + c)) := by
    have hexp : (n : ℂ) + c = Complex.exp (Complex.log (n + c)) := (Complex.exp_log (hc n)).symm
    nth_rw 1 [hexp]
    rw [← Complex.exp_add]
    congr 1
    ring
  calc z * ((n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c))) +
        c * lerchSeriesTerm n z s c
      = z ^ n * (((n : ℂ) + c) * Complex.exp (-s * Complex.log (n + c))) := by
        rw [lerchSeriesTerm_apply]
        linear_combination Complex.exp (-s * Complex.log (n + c)) * hpow
    _ = lerchSeriesTerm n z (s - 1) c := by rw [hbase, lerchSeriesTerm_apply]

/-- Iterating `lerchLoweringOp c` `m` times lowers `s` by `m`:
`(z ∂_z + c)^[m] Φ(z, s, c) = Φ(z, s - m, c)` on `‖z‖ < 1` when `∀ n : ℕ, n + c ≠ 0`. -/
theorem lerchLoweringOp_iterate_lerchSeries (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    (lerchLoweringOp c)^[m] (fun w => lerchSeries w s c) z = lerchSeries z (s - m) c := by
  induction m generalizing z s with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hloc : (lerchLoweringOp c)^[m] (fun w => lerchSeries w s c) =ᶠ[𝓝 z]
        (fun w => lerchSeries w (s - m) c) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
      exact ih (mem_ball_zero_iff.mp hw) s
    rw [lerchLoweringOp_congr_nhds hloc, lerchSeries_lowering hz (s - m) hc]
    congr 1
    · push_cast; ring

/-- The second-order Lerch partial differential equation on `‖z‖ < 1`, `c ∈ Complex.slitPlane`:
`(z ∂_z + c) (∂_c Φ(z, s, c)) = -s Φ(z, s, c)`. -/
theorem lerchSeries_pde {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ} (hc : c ∈ Complex.slitPlane) :
    lerchLoweringOp c (fun w => deriv (fun u => lerchSeries w s u) c) z =
      -s * lerchSeries z s c := by
  have hloc : (fun w => deriv (fun u => lerchSeries w s u) c) =ᶠ[𝓝 z]
      (fun w => -s * lerchSeries w (s + 1) c) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
    exact deriv_lerchSeries_right (mem_ball_zero_iff.mp hw) s hc
  have hc_ne : ∀ n : ℕ, (n : ℂ) + c ≠ 0 := fun n =>
    slitPlane_ne_zero (ofReal_add_mem_slitPlane hc (Nat.cast_nonneg n))
  rw [lerchLoweringOp_congr_nhds hloc, lerchLoweringOp, deriv_const_mul_field]
  have hlow := lerchSeries_lowering hz (s + 1) hc_ne
  rw [lerchLoweringOp, add_sub_cancel_right] at hlow
  linear_combination -s * hlow

/-! ### Rationality and pole structure at nonpositive integers `s = -m` -/

/-- Global rational function representing the Lerch transcendent at nonpositive integer order
`s = -m`, defined by iterating `lerchLoweringOp c` on `(1 - z)⁻¹`. Values at the pole `z = 1` are
totalized via `deriv` and carry no regularity assertion there. -/
noncomputable def lerchNegNat (m : ℕ) (c z : ℂ) : ℂ :=
  (lerchLoweringOp c)^[m] (fun w => (1 - w)⁻¹) z

@[simp]
theorem lerchNegNat_zero (c z : ℂ) : lerchNegNat 0 c z = (1 - z)⁻¹ :=
  (rfl)

theorem lerchNegNat_succ (m : ℕ) (c z : ℂ) :
    lerchNegNat (m + 1) c z = lerchLoweringOp c (lerchNegNat m c) z :=
  congrFun (Function.iterate_succ_apply' (lerchLoweringOp c) m (fun w => (1 - w)⁻¹)) z

/-- On `‖z‖ < 1`, whenever `c` avoids nonpositive integers, `lerchSeries z (-m) c` coincides with
the global rational function `lerchNegNat m c z`. -/
theorem lerchSeries_neg_nat (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) {c : ℂ}
    (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchSeries z (-(m : ℂ)) c = lerchNegNat m c z := by
  have heq : ∀ k : ℕ, ∀ {w : ℂ}, ‖w‖ < 1 →
      (lerchLoweringOp c)^[k] (fun u => lerchSeries u 0 c) w = lerchNegNat k c w := by
    intro k
    induction k with
    | zero => intro w hw; exact lerchSeries_zero_mid hw c
    | succ k ih =>
      intro w hw
      rw [Function.iterate_succ_apply', lerchNegNat_succ]
      refine lerchLoweringOp_congr_nhds ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw)] with u hu
      exact ih (mem_ball_zero_iff.mp hu)
  have hiter := lerchLoweringOp_iterate_lerchSeries m hz 0 hc
  rw [zero_sub] at hiter
  exact hiter.symm.trans (heq m hz)

/-- Polynomial numerator in `z` of
`lerchNegNat m c z = (lerchNegNatNum m c).eval z / (1 - z) ^ (m + 1)`, defined recursively by
`P_0(c) = 1` and `P_{m+1}(c) = X (1 - X) P_m'(c) + (c (1 - X) + (m + 1) X) P_m(c)`. -/
noncomputable def lerchNegNatNum : ℕ → ℂ → ℂ[X]
  | 0, _ => 1
  | m + 1, c =>
      X * (1 - X) * Polynomial.derivative (lerchNegNatNum m c) +
        (C c * (1 - X) + ((m + 1 : ℕ) : ℂ[X]) * X) * lerchNegNatNum m c

@[simp]
theorem lerchNegNatNum_zero (c : ℂ) : lerchNegNatNum 0 c = 1 :=
  (rfl)

theorem lerchNegNatNum_succ (m : ℕ) (c : ℂ) :
    lerchNegNatNum (m + 1) c =
      X * (1 - X) * Polynomial.derivative (lerchNegNatNum m c) +
        (C c * (1 - X) + ((m + 1 : ℕ) : ℂ[X]) * X) * lerchNegNatNum m c :=
  (rfl)

/-- At `z = 1`, the numerator polynomial `lerchNegNatNum m c` evaluates to `m!` independently of
`c`, witnessing that no cancellation with `(1 - z) ^ (m + 1)` occurs. -/
@[simp]
theorem eval_one_lerchNegNatNum (m : ℕ) (c : ℂ) :
    (lerchNegNatNum m c).eval 1 = (m.factorial : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih => simp [lerchNegNatNum_succ, ih, Nat.factorial_succ]

/-- Away from the pole `z = 1`, `lerchNegNat m c z` equals the rational function
`(lerchNegNatNum m c).eval z / (1 - z) ^ (m + 1)`. -/
private theorem lerchNegNat_eq_div_of_ne_one (m : ℕ) (c : ℂ) {z : ℂ} (hz : z ≠ 1) :
    lerchNegNat m c z = (lerchNegNatNum m c).eval z / (1 - z) ^ (m + 1) := by
  induction m generalizing z with
  | zero => simp [div_eq_inv_mul]
  | succ m ih =>
    have hne : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
    have hlocal : lerchNegNat m c =ᶠ[𝓝 z]
        fun w : ℂ => (lerchNegNatNum m c).eval w / (1 - w) ^ (m + 1) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw using ih hw
    have hd := ((lerchNegNatNum m c).hasDerivAt z).div
      (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id' z)).pow (m + 1)) (pow_ne_zero _ hne)
    rw [lerchNegNat_succ, lerchLoweringOp, (hd.congr_of_eventuallyEq hlocal).deriv, ih hz]
    dsimp only [Pi.sub_apply, Pi.pow_apply]
    simp only [lerchNegNatNum_succ, Nat.add_sub_cancel, eval_add, eval_mul, eval_sub, eval_one,
      eval_X, eval_C, eval_natCast]
    push_cast
    simp only [pow_succ]
    field_simp
    ring

/-- Removing the pole `(1 - z) ^ (m + 1)` at `z = 1` yields the nonzero leading coefficient `m!`
for every `c ∈ ℂ`. -/
theorem tendsto_one_sub_pow_mul_lerchNegNat_nhdsNE_one (m : ℕ) (c : ℂ) :
    Tendsto (fun z : ℂ => (1 - z) ^ (m + 1) * lerchNegNat m c z)
      (𝓝[≠] 1) (𝓝 (m.factorial : ℂ)) := by
  have hcont : Continuous fun z : ℂ => (lerchNegNatNum m c).eval z :=
    (lerchNegNatNum m c).continuous
  have hlim : Tendsto (fun z : ℂ => (lerchNegNatNum m c).eval z)
      (𝓝[≠] 1) (𝓝 (m.factorial : ℂ)) := by
    simpa only [eval_one_lerchNegNatNum] using
      (hcont.tendsto (1 : ℂ)).mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 1)
  have : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  rw [lerchNegNat_eq_div_of_ne_one m c hz]
  field_simp

/-- Totalization at `z = 1` never makes `lerchNegNat m c` continuous there. -/
theorem not_continuousAt_lerchNegNat_one (m : ℕ) (c : ℂ) :
    ¬ ContinuousAt (lerchNegNat m c) 1 := by
  intro hc
  have hzero : Tendsto (fun z : ℂ => (1 - z) ^ (m + 1) * lerchNegNat m c z) (𝓝[≠] 1) (𝓝 0) := by
    have hcont : ContinuousAt (fun z : ℂ => (1 - z) ^ (m + 1) * lerchNegNat m c z) 1 :=
      (((continuous_const.sub continuous_id').pow (m + 1)).continuousAt).mul hc
    simpa using hcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
  have heq := tendsto_nhds_unique hzero (tendsto_one_sub_pow_mul_lerchNegNat_nhdsNE_one m c)
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m) : (m.factorial : ℂ) ≠ 0) heq.symm

/-- Rational closed form for `lerchNegNat m c z`, valid for all `c, z ∈ ℂ` (including at the
totalized pole `z = 1`, where both sides equal `0`). -/
theorem lerchNegNat_eq_div (m : ℕ) (c z : ℂ) :
    lerchNegNat m c z = (lerchNegNatNum m c).eval z / (1 - z) ^ (m + 1) := by
  by_cases hz : z = 1
  · subst hz
    simp only [sub_self, zero_pow (Nat.succ_ne_zero m), div_zero]
    induction m with
    | zero => simp
    | succ m ih =>
      rw [lerchNegNat_succ, lerchLoweringOp, ih, mul_zero, add_zero,
        deriv_zero_of_not_differentiableAt
          (mt DifferentiableAt.continuousAt (not_continuousAt_lerchNegNat_one m c)),
        mul_zero]
  · exact lerchNegNat_eq_div_of_ne_one m c hz

/-- Joint analyticity of `(c, z) ↦ lerchNegNat m c z` on `{p : ℂ × ℂ | p.2 ≠ 1}`. -/
theorem analyticOnNhd_lerchNegNat (m : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => lerchNegNat m p.1 p.2) {p : ℂ × ℂ | p.2 ≠ 1} := by
  have hopen : IsOpen {p : ℂ × ℂ | p.2 ≠ 1} := isOpen_ne.preimage continuous_snd
  induction m with
  | zero =>
    intro p (hp : p.2 ≠ 1)
    have h1 : AnalyticAt ℂ (fun _ : ℂ × ℂ => (1 : ℂ)) p := analyticAt_const
    exact (h1.div (h1.sub analyticAt_snd) (sub_ne_zero.mpr hp.symm)).congr
      (Eventually.of_forall fun q => (one_div (1 - q.2)))
  | succ m ih =>
    intro p (hp : p.2 ≠ 1)
    have hpart : AnalyticAt ℂ
        (fun q : ℂ × ℂ => (fderiv ℂ (fun r : ℂ × ℂ => lerchNegNat m r.1 r.2) q) (0, 1)) p :=
      ((ContinuousLinearMap.apply ℂ ℂ ((0 : ℂ), (1 : ℂ))).analyticAt _).comp (ih p hp).fderiv
    have hcomb : AnalyticAt ℂ
        (fun q : ℂ × ℂ => q.2 * (fderiv ℂ (fun r : ℂ × ℂ => lerchNegNat m r.1 r.2) q) (0, 1) +
          q.1 * lerchNegNat m q.1 q.2) p :=
      (analyticAt_snd.mul hpart).add (analyticAt_fst.mul (ih p hp))
    refine hcomb.congr ?_
    filter_upwards [hopen.mem_nhds hp] with q hq
    have hf := (ih q hq).differentiableAt.hasFDerivAt.comp q.2
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) q.1 q.2)
    have hder : deriv (lerchNegNat m q.1) q.2 =
        (fderiv ℂ (fun r : ℂ × ℂ => lerchNegNat m r.1 r.2) q) (0, 1) := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply] using hf.hasDerivAt.deriv
    simp [lerchNegNat_succ, lerchLoweringOp, hder]

/-- Explicit closed form at `m = 1` (`s = -1`), valid for all `c, z ∈ ℂ` (including at `z = 1`,
where both sides equal `0`):
`lerchNegNat 1 c z = c / (1 - z) + z / (1 - z) ^ 2`. -/
theorem lerchNegNat_one (c z : ℂ) :
    lerchNegNat 1 c z = c / (1 - z) + z / (1 - z) ^ 2 := by
  by_cases hz : z = 1
  · subst hz; simp [lerchNegNat_eq_div]
  · have : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    rw [lerchNegNat_eq_div]
    simp only [lerchNegNatNum_succ, lerchNegNatNum_zero, derivative_one, mul_zero, zero_add,
      mul_one, Nat.cast_one, eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_X]
    field_simp
    ring

/-- On `‖z‖ < 1`, if `∀ n : ℕ, n + c ≠ 0`, then
`lerchSeries z (-1) c = c / (1 - z) + z / (1 - z) ^ 2`. -/
theorem lerchSeries_neg_one {z : ℂ} (hz : ‖z‖ < 1) {c : ℂ} (hc : ∀ n : ℕ, (n : ℂ) + c ≠ 0) :
    lerchSeries z (-1) c = c / (1 - z) + z / (1 - z) ^ 2 := by
  simpa using (lerchSeries_neg_nat 1 hz hc).trans (lerchNegNat_one c z)

/-! ### Specialization bridges to `TauCeti.Polylog.polylog` -/

/-- Weight-one polylogarithm bridge on the open unit disc `‖z‖ < 1`:
`z * lerchSeries z 1 1 = Polylog.polylog 1 z = -log (1 - z)`. -/
theorem mul_lerchSeries_one_one {z : ℂ} (hz : ‖z‖ < 1) :
    z * lerchSeries z 1 1 = Polylog.polylog 1 z := by
  rw [← (Polylog.hasSum_polylog_one hz).tsum_eq, lerchSeries_def, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hn0 : (n : ℂ) + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [lerchSeriesTerm_apply, neg_one_mul, Complex.exp_neg, Complex.exp_log hn0, pow_succ',
    div_eq_mul_inv, mul_assoc]

/-- Global nonpositive-weight polylogarithm bridge: for every `m : ℕ` and every `z ∈ ℂ` (including
the totalized value at `z = 1`), `z * lerchNegNat m 1 z = Polylog.polylog (-m) z`. -/
theorem mul_lerchNegNat_one_eq_polylog (m : ℕ) (z : ℂ) :
    z * lerchNegNat m 1 z = Polylog.polylog (-(m : ℤ)) z := by
  induction m generalizing z with
  | zero => simp [div_eq_mul_inv]
  | succ m ih =>
    by_cases hz : z = 1
    · subst hz
      rw [lerchNegNat_eq_div, Polylog.polylog_neg_nat_eq_div]
      simp
    · have hloc : Polylog.polylog (-(m : ℤ)) =ᶠ[𝓝 z] fun w => w * lerchNegNat m 1 w :=
        Eventually.of_forall fun w => (ih w).symm
      have hd_lerch : DifferentiableAt ℂ (lerchNegNat m 1) z :=
        (analyticOnNhd_lerchNegNat m (1, z) hz).differentiableAt.comp z
          ((differentiableAt_const (1 : ℂ)).prodMk differentiableAt_id)
      have hd := (hasDerivAt_id' z).mul hd_lerch.hasDerivAt
      rw [Polylog.polylog_neg_nat_succ, (hd.congr_of_eventuallyEq hloc).deriv,
        lerchNegNat_succ, lerchLoweringOp]
      ring

/-- Nonpositive-weight polylogarithm bridge for `lerchSeries` on the open unit disc `‖z‖ < 1`:
`z * lerchSeries z (-m) 1 = Polylog.polylog (-m) z`. -/
theorem mul_lerchSeries_neg_nat_one (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * lerchSeries z (-(m : ℂ)) 1 = Polylog.polylog (-(m : ℤ)) z := by
  have hc : ∀ n : ℕ, (n : ℂ) + 1 ≠ 0 := fun n h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [lerchSeries_neg_nat m hz hc, mul_lerchNegNat_one_eq_polylog]

end TauCeti
