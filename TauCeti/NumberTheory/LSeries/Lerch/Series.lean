/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.Complex.SlitPlane

import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Lerch transcendent series, compact convergence, and boundary specializations

For `z, s, c ∈ ℂ` with `‖z‖ < 1`, the Lerch transcendent is given by the power-Dirichlet series

`Φ(z, s, c) = ∑' n : ℕ, z ^ n * exp (-s * log (n + c))`,

using Mathlib's principal logarithm `Complex.log`. Because `(n + c).re → +∞` as `n → ∞`, the tail
factors `exp (-s * log (n + c))` and `(log (n + c)) ^ k` grow at most polynomially in `n`
uniformly on bounded `(s, c)` sets, so the geometric factor `z ^ n` makes the series and all of its
termwise derivatives converge absolutely and uniformly on compact subsets with `‖z‖ < 1`.

When `c ∈ Complex.slitPlane`, every shifted base `n + c` stays off the nonpositive real branch cut
`(-∞, 0]`, so each term is jointly holomorphic in `(z, s, c)` and Osgood's lemma upgrades uniform
convergence to joint analyticity of `Φ` on `{p : ℂ × ℂ × ℂ | ‖p.1‖ < 1 ∧ p.2.2 ∈ slitPlane}`. In
`z` and `s` alone, `Φ(z, s, c)` is analytic on `ball 0 1` and entire in `s` for arbitrary `c ∈ ℂ`.

On the closed unit disc `‖z‖ ≤ 1`, the series converges absolutely and uniformly in the half-plane
`1 < s.re`. At `z = exp (2 * π * I * a)` with real `a` and `c = 1`, multiplying by `z` recovers
Mathlib's periodic zeta function `HurwitzZeta.expZeta a s`, while at `z = 1` and `c = a ∈ (0, 1]`
it recovers `HurwitzZeta.hurwitzZeta a s`. Along the positive radial segment `r → 1⁻`, `Φ(r, s, c)`
tends to the Hurwitz series `∑' n : ℕ, exp (-s * log (n + c))` for `1 < s.re` and diverges in norm
at `s = 0`.

## Main definitions and results

* `TauCeti.lerchSeries`: the defining series `∑' n : ℕ, z ^ n * exp (-s * log (n + c))`.
* `TauCeti.summable_norm_lerchSeries_mul_log_pow`, `TauCeti.summable_lerchSeriesTerm`:
  absolute convergence on `‖z‖ < 1` for arbitrary `s, c ∈ ℂ`.
* `TauCeti.tendstoUniformlyOn_lerchSeries_deriv_term`, `TauCeti.tendstoUniformlyOn_lerchSeries`:
  compact-uniform convergence of the series and its weighted derivative series on `{p | ‖p.1‖ < 1}`.
* `TauCeti.lerchSeries_zero_mid`, `TauCeti.lerchSeries_shift`, `TauCeti.lerchSeries_shift_nat`:
  closed form `(1 - z)⁻¹` at `s = 0` and the `c`-shift identities.
* `TauCeti.hasDerivAt_lerchSeries_left`, `TauCeti.hasDerivAt_lerchSeries_mid`,
  `TauCeti.hasDerivAt_lerchSeries_right`: termwise `z`-, `s`-, and `c`-derivatives, including the
  `s`-raising relation `∂_c Φ(z, s, c) = -s Φ(z, s + 1, c)`.
* `TauCeti.analyticOnNhd_lerchSeries`, `TauCeti.differentiableOn_lerchSeries`,
  `AnalyticAt.lerchSeries`: joint holomorphy on `‖z‖ < 1`, `c ∈ Complex.slitPlane`.
* `TauCeti.continuousOn_lerchSeries_closedBall`, `TauCeti.expZeta_eq_mul_lerchSeries`,
  `TauCeti.hurwitzZeta_eq_lerchSeries`: closed-disc continuity and Mathlib Hurwitz/periodic-zeta
  comparisons for `1 < s.re`.
* `TauCeti.tendsto_lerchSeries_nhdsLT_one`, `TauCeti.tendsto_norm_lerchSeries_zero_nhdsLT_one`:
  radial Hurwitz limit for `1 < s.re` and norm divergence at `s = 0`.

## References

* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function I. Zeta integrals*,
  Forum Math. **24** (2012), 1–48, §1 (1.1)–(1.3) and §3.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function II. Analytic continuation*,
  Forum Math. **24** (2012), 49–84, §2 and §5.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  Res. Math. Sci. **3** (2016), Paper No. 2, §§1–2 and §6.
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti

/-- Individual `n`-th term `z ^ n * exp (-s * log (n + c))` of the Lerch transcendent series,
using Mathlib's principal logarithm. -/
noncomputable def lerchSeriesTerm (n : ℕ) (z s c : ℂ) : ℂ :=
  z ^ n * Complex.exp (-s * Complex.log (n + c))

@[simp]
theorem lerchSeriesTerm_apply (n : ℕ) (z s c : ℂ) :
    lerchSeriesTerm n z s c = z ^ n * Complex.exp (-s * Complex.log (n + c)) :=
  (rfl)

/-- The Lerch transcendent defining series `Φ(z, s, c) = ∑' n : ℕ, z ^ n * exp (-s * log (n + c))`,
using Mathlib's principal logarithm `Complex.log`. It converges absolutely for all `s, c : ℂ`
whenever `‖z‖ < 1`, and defines a jointly holomorphic function on
`‖z‖ < 1`, `s ∈ ℂ`, `c ∈ Complex.slitPlane`. Outside its convergence domain the `tsum` takes the
junk value `0` and carries no analytic-continuation meaning. -/
noncomputable def lerchSeries (z s c : ℂ) : ℂ :=
  ∑' n : ℕ, lerchSeriesTerm n z s c

theorem lerchSeries_def (z s c : ℂ) :
    lerchSeries z s c = ∑' n : ℕ, lerchSeriesTerm n z s c :=
  (rfl)

/-! ### Polynomial tail bounds and compact-uniform convergence -/

/-- For `1 ≤ ‖w‖ ≤ A`, both `‖log w‖` and `‖exp (-s * log w)‖` are controlled by powers of `A`. -/
private lemma norm_log_and_exp_neg_mul_log_le {w s : ℂ} {A B : ℝ} (hw1 : 1 ≤ ‖w‖) (hwA : ‖w‖ ≤ A)
    (hB : 0 ≤ B) (hs : ‖s‖ ≤ B) :
    ‖Complex.log w‖ ≤ A + Real.pi ∧
      ‖Complex.exp (-s * Complex.log w)‖ ≤ Real.exp (B * Real.pi) * A ^ ⌈B⌉₊ := by
  have hA1 : 1 ≤ A := hw1.trans hwA
  have hlog0 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw1
  have hlogA : Real.log ‖w‖ ≤ Real.log A := Real.log_le_log (zero_lt_one.trans_le hw1) hwA
  refine ⟨?_, ?_⟩
  · have hle : Real.log ‖w‖ ≤ A :=
      (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hw1)).trans (by linarith)
    calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
          norm_le_abs_re_add_abs_im _
      _ = Real.log ‖w‖ + |w.arg| := by rw [log_re, log_im, abs_of_nonneg hlog0]
      _ ≤ A + Real.pi := add_le_add hle (abs_arg_le_pi w)
  · have hre : (-s * Complex.log w).re ≤ B * Real.pi + ⌈B⌉₊ * Real.log A := by
      rw [mul_re, neg_re, neg_im, log_re, log_im]
      have h1 : -s.re * Real.log ‖w‖ ≤ ⌈B⌉₊ * Real.log A :=
        calc -s.re * Real.log ‖w‖ ≤ |s.re| * Real.log ‖w‖ :=
              mul_le_mul_of_nonneg_right (neg_le_abs _) hlog0
          _ ≤ B * Real.log A := mul_le_mul ((abs_re_le_norm s).trans hs) hlogA hlog0 hB
          _ ≤ ⌈B⌉₊ * Real.log A :=
              mul_le_mul_of_nonneg_right (Nat.le_ceil B) (hlog0.trans hlogA)
      have h2 : s.im * w.arg ≤ B * Real.pi :=
        (le_abs_self _).trans <| (abs_mul _ _).le.trans <|
          mul_le_mul ((abs_im_le_norm s).trans hs) (abs_arg_le_pi w) (abs_nonneg _) hB
      linarith
    rw [Complex.norm_exp]
    calc Real.exp ((-s * Complex.log w).re)
        ≤ Real.exp (B * Real.pi + ⌈B⌉₊ * Real.log A) := Real.exp_le_exp.mpr hre
      _ = Real.exp (B * Real.pi) * A ^ ⌈B⌉₊ := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans_le hA1)]

/-- Uniform polynomial bound on `‖log (n + c) ^ k * exp (-s * log (n + c))‖` once `M + 1 ≤ n`. -/
private lemma norm_log_pow_mul_exp_neg_mul_log_le {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) (k : ℕ)
    {n : ℕ} (hn : M + 1 ≤ n) {s c : ℂ} (hs : ‖s‖ ≤ B) (hc : ‖c‖ ≤ M) :
    ‖Complex.log (n + c) ^ k * Complex.exp (-s * Complex.log (n + c))‖ ≤
      (1 + M + Real.pi) ^ k * Real.exp (B * Real.pi) * (1 + M) ^ ⌈B⌉₊ *
        (n : ℝ) ^ (k + ⌈B⌉₊) := by
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlow : 1 ≤ ‖(n : ℂ) + c‖ := by
    have h := norm_sub_le ((n : ℂ) + c) c
    rw [add_sub_cancel_right, Complex.norm_natCast] at h
    linarith
  have hup : ‖(n : ℂ) + c‖ ≤ (1 + M) * n := by
    calc ‖(n : ℂ) + c‖ ≤ ‖(n : ℂ)‖ + ‖c‖ := norm_add_le _ _
      _ ≤ n + M := by rw [Complex.norm_natCast]; gcongr
      _ ≤ (1 + M) * n := by nlinarith
  obtain ⟨hlog, hexp⟩ := norm_log_and_exp_neg_mul_log_le hlow hup hB hs
  have hlog' : ‖Complex.log (n + c)‖ ≤ (1 + M + Real.pi) * n :=
    hlog.trans (by nlinarith [Real.pi_pos])
  rw [norm_mul, norm_pow]
  calc ‖Complex.log (n + c)‖ ^ k * ‖Complex.exp (-s * Complex.log (n + c))‖
      ≤ ((1 + M + Real.pi) * n) ^ k * (Real.exp (B * Real.pi) * ((1 + M) * n) ^ ⌈B⌉₊) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hlog' k) hexp (by positivity) (by positivity)
    _ = (1 + M + Real.pi) ^ k * Real.exp (B * Real.pi) * (1 + M) ^ ⌈B⌉₊ *
          (n : ℝ) ^ (k + ⌈B⌉₊) := by rw [mul_pow, mul_pow, pow_add]; ring

/-- Summable geometric-polynomial majorant for Lerch series and derivative tails on bounded
parameter sets with `‖z‖ ≤ r < 1`. -/
private lemma exists_eventually_norm_lerch_bound {r B M : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (d k : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ᶠ n : ℕ in atTop, ∀ {z s c : ℂ},
      ‖z‖ ≤ r → ‖s‖ ≤ B → ‖c‖ ≤ M →
      ‖(n : ℂ) ^ d * z ^ (n - d) * Complex.log (n + c) ^ k *
          Complex.exp (-s * Complex.log (n + c))‖ ≤ u n := by
  let ρ : ℝ := (r + 1) / 2
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by dsimp only [ρ]; linarith
  have hrρ : r ≤ ρ := by dsimp only [ρ]; linarith
  set C : ℝ := (1 + M + Real.pi) ^ k * Real.exp (B * Real.pi) * (1 + M) ^ ⌈B⌉₊ * (ρ ^ d)⁻¹
  refine ⟨fun n => C * ((n : ℝ) ^ (d + k + ⌈B⌉₊) * ρ ^ n), ?_, ?_⟩
  · exact (summable_pow_mul_geometric_of_norm_lt_one (d + k + ⌈B⌉₊)
      (by rwa [Real.norm_of_nonneg hρ0.le])).mul_left C
  · filter_upwards [eventually_ge_atTop (max d (⌈M⌉₊ + 1))] with n hn z s c hz hs hc
    have hnd : d ≤ n := (le_max_left _ _).trans hn
    have hnM : M + 1 ≤ n := by
      have : (⌈M⌉₊ + 1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
      linarith [Nat.le_ceil M]
    have hpow_z : ‖z ^ (n - d)‖ ≤ (ρ ^ d)⁻¹ * ρ ^ n := by
      rw [norm_pow]
      calc ‖z‖ ^ (n - d) ≤ ρ ^ (n - d) := pow_le_pow_left₀ (norm_nonneg z) (hz.trans hrρ) _
        _ = (ρ ^ d)⁻¹ * ρ ^ n := by
            rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero d hρ0.ne'), ← pow_add, Nat.add_sub_of_le hnd]
    have htail := norm_log_pow_mul_exp_neg_mul_log_le hB hM k hnM hs hc
    rw [mul_assoc (_ * _), norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    calc (n : ℝ) ^ d * ‖z ^ (n - d)‖ *
          ‖Complex.log (n + c) ^ k * Complex.exp (-s * Complex.log (n + c))‖
        ≤ (n : ℝ) ^ d * ((ρ ^ d)⁻¹ * ρ ^ n) *
            ((1 + M + Real.pi) ^ k * Real.exp (B * Real.pi) * (1 + M) ^ ⌈B⌉₊ *
              (n : ℝ) ^ (k + ⌈B⌉₊)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow_z (by positivity)) htail
            (norm_nonneg _) (by positivity)
      _ = C * ((n : ℝ) ^ (d + k + ⌈B⌉₊) * ρ ^ n) := by
          simp only [C, add_assoc, pow_add]; ring

/-- For `‖z‖ < 1` and any `s, c ∈ ℂ` and `d, k : ℕ`, the weighted Lerch derivative series
`n ^ d * z ^ (n - d) * log (n + c) ^ k * exp (-s * log (n + c))` is absolutely summable. -/
theorem summable_norm_lerchSeries_mul_log_pow {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) (d k : ℕ) :
    Summable fun n : ℕ =>
      ‖(n : ℂ) ^ d * z ^ (n - d) * Complex.log (n + c) ^ k *
        Complex.exp (-s * Complex.log (n + c))‖ := by
  obtain ⟨u, hu, hbound⟩ := exists_eventually_norm_lerch_bound (norm_nonneg z) hz
    (norm_nonneg s) (norm_nonneg c) d k
  exact Summable.of_norm_bounded_eventually_nat hu <| hbound.mono fun n hn => by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hn le_rfl le_rfl le_rfl

/-- For `‖z‖ < 1` and any `s, c ∈ ℂ`, the defining Lerch series converges absolutely. -/
theorem summable_lerchSeriesTerm {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    Summable fun n : ℕ => lerchSeriesTerm n z s c := by
  refine .of_norm ?_
  simpa [lerchSeriesTerm] using summable_norm_lerchSeries_mul_log_pow hz s c 0 0

/-- On any compact subset `K ⊆ {p : ℂ × ℂ × ℂ | ‖p.1‖ < 1}`, every weighted derivative series
`n ^ d * z ^ (n - d) * log (n + c) ^ k * exp (-s * log (n + c))` converges uniformly. -/
theorem tendstoUniformlyOn_lerchSeries_deriv_term {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hz : ∀ p ∈ K, ‖p.1‖ < 1) (d k : ℕ) :
    TendstoUniformlyOn
      (fun N (p : ℂ × ℂ × ℂ) => ∑ n ∈ Finset.range N,
        (n : ℂ) ^ d * p.1 ^ (n - d) * Complex.log (n + p.2.2) ^ k *
          Complex.exp (-p.2.1 * Complex.log (n + p.2.2)))
      (fun p : ℂ × ℂ × ℂ => ∑' n : ℕ,
        (n : ℂ) ^ d * p.1 ^ (n - d) * Complex.log (n + p.2.2) ^ k *
          Complex.exp (-p.2.1 * Complex.log (n + p.2.2)))
      atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨p₀, hp₀, hmax_z⟩ := hK.exists_isMaxOn hKne continuous_fst.norm.continuousOn
  obtain ⟨B₀, hB₀⟩ := (hK.image (continuous_fst.comp continuous_snd)).isBounded.exists_norm_le
  obtain ⟨M₀, hM₀⟩ := (hK.image (continuous_snd.comp continuous_snd)).isBounded.exists_norm_le
  obtain ⟨u, hu, hbound⟩ := exists_eventually_norm_lerch_bound (norm_nonneg p₀.1) (hz p₀ hp₀)
    (le_max_right B₀ 0) (le_max_right M₀ 0) d k
  refine tendstoUniformlyOn_tsum_nat_eventually hu (hbound.mono fun n hn p hp => ?_)
  exact hn (hmax_z hp) ((hB₀ _ (mem_image_of_mem _ hp)).trans (le_max_left _ _))
    ((hM₀ _ (mem_image_of_mem _ hp)).trans (le_max_left _ _))

/-- On any compact subset `K ⊆ {p : ℂ × ℂ × ℂ | ‖p.1‖ < 1}`, the partial sums of `lerchSeries`
converge uniformly to `lerchSeries`. -/
theorem tendstoUniformlyOn_lerchSeries {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hz : ∀ p ∈ K, ‖p.1‖ < 1) :
    TendstoUniformlyOn
      (fun N (p : ℂ × ℂ × ℂ) => ∑ n ∈ Finset.range N, lerchSeriesTerm n p.1 p.2.1 p.2.2)
      (fun p : ℂ × ℂ × ℂ => lerchSeries p.1 p.2.1 p.2.2) atTop K := by
  simpa [lerchSeries, lerchSeriesTerm] using tendstoUniformlyOn_lerchSeries_deriv_term hK hz 0 0

/-! ### Elementary identities and the `c`-shift -/

/-- At `z = 0`, only the `n = 0` term survives (`0 ^ 0 = 1`), giving `exp (-s * log c)`. -/
@[simp]
theorem lerchSeries_zero_left (s c : ℂ) :
    lerchSeries 0 s c = Complex.exp (-s * Complex.log c) := by
  rw [lerchSeries, tsum_eq_single 0]
  · simp [lerchSeriesTerm]
  · intro n hn
    simp [lerchSeriesTerm, zero_pow hn]

/-- At `s = 0`, every logarithmic weight reduces to `1` and `lerchSeries z 0 c = (1 - z)⁻¹` on the
open unit disc `‖z‖ < 1`, independently of `c`. -/
theorem lerchSeries_zero_mid {z : ℂ} (hz : ‖z‖ < 1) (c : ℂ) :
    lerchSeries z 0 c = (1 - z)⁻¹ := by
  simpa [lerchSeries, lerchSeriesTerm] using tsum_geometric_of_norm_lt_one hz

/-- Shifting the `c` parameter by `1` peels off the `n = 0` term `exp (-s * log c)`. -/
theorem lerchSeries_shift {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    lerchSeries z s c = Complex.exp (-s * Complex.log c) + z * lerchSeries z s (c + 1) := by
  rw [lerchSeries, (summable_lerchSeriesTerm hz s c).tsum_eq_zero_add]
  simp only [lerchSeriesTerm, pow_zero, one_mul, Nat.cast_zero, zero_add, pow_succ', mul_assoc]
  rw [tsum_mul_left, lerchSeries]
  congr 2
  refine tsum_congr fun n => ?_
  simp only [lerchSeriesTerm, Nat.cast_add, Nat.cast_one]
  ring_nf

/-- Iterated `c`-shift separating the first `N` terms of `lerchSeries`. -/
theorem lerchSeries_shift_nat {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) (N : ℕ) :
    lerchSeries z s c =
      (∑ j ∈ Finset.range N, z ^ j * Complex.exp (-s * Complex.log (j + c))) +
        z ^ N * lerchSeries z s (c + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, lerchSeries_shift hz s (c + N)]
    push_cast
    have hlog : (N : ℂ) + c = c + N := add_comm _ _
    rw [hlog, mul_add, ← mul_assoc, ← pow_succ, add_assoc, add_assoc]

/-! ### Termwise derivatives and joint holomorphy -/

/-- Termwise `z`-derivative of `lerchSeries` on the open unit disc `‖z‖ < 1`. -/
theorem hasDerivAt_lerchSeries_left {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasDerivAt (fun w => lerchSeries w s c)
      (∑' n : ℕ, (n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c))) z := by
  let r : ℝ := (1 - ‖z‖) / 2
  have hr : 0 < r := by positivity
  obtain ⟨u, hu, hbound⟩ := exists_eventually_norm_lerch_bound (by positivity : 0 ≤ ‖z‖ + r)
    (by dsimp only [r]; linarith) (norm_nonneg s) (norm_nonneg c) 1 0
  have hunif' : TendstoUniformlyOn
      (fun N w => ∑ n ∈ Finset.range N,
        (n : ℂ) * w ^ (n - 1) * Complex.exp (-s * Complex.log (n + c)))
      (fun w => ∑' n : ℕ, (n : ℂ) * w ^ (n - 1) * Complex.exp (-s * Complex.log (n + c)))
      atTop (ball z r) := by
    refine tendstoUniformlyOn_tsum_nat_eventually hu (hbound.mono fun n hn w hw => ?_)
    have hw' : ‖w‖ ≤ ‖z‖ + r := by
      have h1 := norm_le_norm_add_norm_sub' w z
      have h2 : ‖w - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
      linarith
    simpa [mul_assoc] using hn hw' le_rfl le_rfl
  refine hasDerivAt_of_tendstoUniformlyOn isOpen_ball hunif'
    (Eventually.of_forall fun N w _ =>
      HasDerivAt.fun_sum fun n _ => (hasDerivAt_pow n w).mul_const _)
    (fun w hw => ?_) (mem_ball_self hr)
  have hw1 : ‖w‖ < 1 := by
    have h1 := norm_le_norm_add_norm_sub' w z
    have h2 : ‖w - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
    dsimp only [r] at h2; linarith
  exact (summable_lerchSeriesTerm hw1 s c).hasSum.tendsto_sum_nat

/-- Termwise formula for `deriv (lerchSeries · s c) z` on `‖z‖ < 1`. -/
theorem deriv_lerchSeries_left {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    deriv (fun w => lerchSeries w s c) z =
      ∑' n : ℕ, (n : ℂ) * z ^ (n - 1) * Complex.exp (-s * Complex.log (n + c)) :=
  (hasDerivAt_lerchSeries_left hz s c).deriv

/-- Termwise `s`-derivative of `lerchSeries` on `‖z‖ < 1`:
`∂_s Φ(z, s, c) = -∑' n : ℕ, z ^ n * log (n + c) * exp (-s * log (n + c))`. -/
theorem hasDerivAt_lerchSeries_mid {z : ℂ} (hz : ‖z‖ < 1) (s c : ℂ) :
    HasDerivAt (fun w => lerchSeries z w c)
      (-∑' n : ℕ, z ^ n * Complex.log (n + c) * Complex.exp (-s * Complex.log (n + c))) s := by
  obtain ⟨u, hu, hbound⟩ := exists_eventually_norm_lerch_bound (norm_nonneg z) hz
    (by positivity : 0 ≤ ‖s‖ + 1) (norm_nonneg c) 0 1
  have hunif' : TendstoUniformlyOn
      (fun N w => ∑ n ∈ Finset.range N,
        -(z ^ n * Complex.log (n + c) * Complex.exp (-w * Complex.log (n + c))))
      (fun w => ∑' n : ℕ,
        -(z ^ n * Complex.log (n + c) * Complex.exp (-w * Complex.log (n + c))))
      atTop (ball s 1) := by
    refine tendstoUniformlyOn_tsum_nat_eventually hu (hbound.mono fun n hn w hw => ?_)
    have hw' : ‖w‖ ≤ ‖s‖ + 1 := by
      have h1 := norm_le_norm_add_norm_sub' w s
      have h2 : ‖w - s‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
      linarith
    simpa [mul_assoc, mul_left_comm] using hn le_rfl hw' le_rfl
  rw [← tsum_neg]
  refine hasDerivAt_of_tendstoUniformlyOn isOpen_ball hunif'
    (Eventually.of_forall fun N w _ => HasDerivAt.fun_sum fun n _ => ?_)
    (fun w _ => (summable_lerchSeriesTerm hz w c).hasSum.tendsto_sum_nat) (mem_ball_self one_pos)
  exact (((hasDerivAt_id' w).neg.mul_const (Complex.log (n + c))).cexp.const_mul
    (z ^ n)).congr_deriv (by simp; ring)

/-- Derivative of `lerchSeries` in `c` on `Complex.slitPlane` (`s`-raising relation):
`∂_c Φ(z, s, c) = -s Φ(z, s + 1, c)`. -/
theorem hasDerivAt_lerchSeries_right {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : c ∈ Complex.slitPlane) :
    HasDerivAt (fun w => lerchSeries z s w) (-s * lerchSeries z (s + 1) c) c := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp isOpen_slitPlane c hc
  obtain ⟨u, hu, hbound⟩ := exists_eventually_norm_lerch_bound (norm_nonneg z) hz
    (by positivity : 0 ≤ ‖s + 1‖) (by positivity : 0 ≤ ‖c‖ + δ / 2) 0 0
  have hunif' : TendstoUniformlyOn
      (fun N w => ∑ n ∈ Finset.range N, -s * lerchSeriesTerm n z (s + 1) w)
      (fun w => ∑' n : ℕ, -s * lerchSeriesTerm n z (s + 1) w)
      atTop (ball c (δ / 2)) := by
    refine tendstoUniformlyOn_tsum_nat_eventually (hu.mul_left ‖s‖)
      (hbound.mono fun n hn w hw => ?_)
    have hw' : ‖w‖ ≤ ‖c‖ + δ / 2 := by
      have h1 := norm_le_norm_add_norm_sub' w c
      have h2 : ‖w - c‖ < δ / 2 := by simpa [mem_ball, dist_eq_norm] using hw
      linarith
    have h1 : ‖lerchSeriesTerm n z (s + 1) w‖ ≤ u n := by
      simpa using hn le_rfl (le_rfl : ‖s + 1‖ ≤ ‖s + 1‖) hw'
    rw [norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
  rw [lerchSeries_def, ← tsum_mul_left]
  refine hasDerivAt_of_tendstoUniformlyOn isOpen_ball hunif'
    (Eventually.of_forall fun N w hw => HasDerivAt.fun_sum fun n _ => ?_)
    (fun w _ => (summable_lerchSeriesTerm hz s w).hasSum.tendsto_sum_nat)
    (mem_ball_self (half_pos hδ))
  have hnw : (n : ℂ) + w ∈ Complex.slitPlane :=
    ofReal_add_mem_slitPlane (hball (ball_subset_ball (by linarith) hw)) (Nat.cast_nonneg n)
  have hlog : HasDerivAt (fun x => Complex.log ((n : ℂ) + x)) (((n : ℂ) + w)⁻¹ * 1) w :=
    (Complex.hasStrictDerivAt_log hnw).hasDerivAt.comp w ((hasDerivAt_id' w).const_add (n : ℂ))
  refine ((hlog.const_mul (-s)).cexp.const_mul (z ^ n)).congr_deriv ?_
  have hinv : ((n : ℂ) + w)⁻¹ = Complex.exp (-Complex.log (n + w)) := by
    rw [Complex.exp_neg, Complex.exp_log (slitPlane_ne_zero hnw)]
  calc z ^ n * (Complex.exp (-s * Complex.log (n + w)) * (-s * (((n : ℂ) + w)⁻¹ * 1)))
      = -s * (z ^ n * (Complex.exp (-s * Complex.log (n + w)) *
          Complex.exp (-Complex.log (n + w)))) := by rw [hinv]; ring
    _ = -s * lerchSeriesTerm n z (s + 1) w := by
        rw [lerchSeriesTerm_apply, ← Complex.exp_add]
        congr 3
        ring

/-- Raising relation for the `c`-derivative:
`deriv (lerchSeries z s ·) c = -s * lerchSeries z (s + 1) c` for `‖z‖ < 1` and
`c ∈ Complex.slitPlane`. -/
theorem deriv_lerchSeries_right {z : ℂ} (hz : ‖z‖ < 1) (s : ℂ) {c : ℂ}
    (hc : c ∈ Complex.slitPlane) :
    deriv (fun w => lerchSeries z s w) c = -s * lerchSeries z (s + 1) c :=
  (hasDerivAt_lerchSeries_right hz s hc).deriv

/-- For fixed `s, c ∈ ℂ`, `z ↦ lerchSeries z s c` is analytic on the open unit disc `ball 0 1`. -/
theorem analyticOnNhd_lerchSeries_left (s c : ℂ) :
    AnalyticOnNhd ℂ (fun z => lerchSeries z s c) (ball 0 1) :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (hasDerivAt_lerchSeries_left (mem_ball_zero_iff.mp hz) s c).differentiableAt
      |>.differentiableWithinAt)
    isOpen_ball

/-- For fixed `z` with `‖z‖ < 1` and arbitrary `c ∈ ℂ`, `s ↦ lerchSeries z s c` is entire. -/
theorem differentiable_lerchSeries_mid {z : ℂ} (hz : ‖z‖ < 1) (c : ℂ) :
    Differentiable ℂ (fun s => lerchSeries z s c) :=
  fun s => (hasDerivAt_lerchSeries_mid hz s c).differentiableAt

/-- Joint analyticity of `lerchSeries` in its three complex arguments at any `v : Fin 3 → ℂ` with
`‖v 0‖ < 1` and `v 2 ∈ Complex.slitPlane`, proved via Osgood's lemma. -/
theorem analyticAt_lerchSeries_pi {v : Fin 3 → ℂ} (hv0 : ‖v 0‖ < 1)
    (hv2 : v 2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun w : Fin 3 → ℂ => lerchSeries (w 0) (w 1) (w 2)) v := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp isOpen_slitPlane (v 2) hv2
  let r : ℝ := min ((1 - ‖v 0‖) / 2) (δ / 2)
  have hr : 0 < r := lt_min (by positivity) (half_pos hδ)
  have hr0 : r ≤ (1 - ‖v 0‖) / 2 := min_le_left _ _
  have hr2 : r ≤ δ / 2 := min_le_right _ _
  have hV_lt : ∀ w ∈ closedBall v r, ‖w 0‖ < 1 ∧ w 2 ∈ Complex.slitPlane := by
    intro w hw
    have hw0 : dist (w 0) (v 0) ≤ r := (dist_le_pi_dist w v 0).trans (mem_closedBall.mp hw)
    have hw2 : dist (w 2) (v 2) ≤ r := (dist_le_pi_dist w v 2).trans (mem_closedBall.mp hw)
    refine ⟨?_, hball (mem_ball.mpr (hw2.trans_lt (by linarith)))⟩
    have := norm_le_norm_add_norm_sub' (w 0) (v 0)
    rw [dist_eq_norm] at hw0
    linarith
  obtain ⟨u, hu, hbound⟩ := exists_eventually_norm_lerch_bound (by positivity : 0 ≤ ‖v 0‖ + r)
    (by linarith) (by positivity : 0 ≤ ‖v 1‖ + r) (by positivity : 0 ≤ ‖v 2‖ + r) 0 0
  have hunif : TendstoUniformlyOn
      (fun N w => ∑ n ∈ Finset.range N, lerchSeriesTerm n (w 0) (w 1) (w 2))
      (fun w => lerchSeries (w 0) (w 1) (w 2)) atTop (closedBall v r) := by
    refine tendstoUniformlyOn_tsum_nat_eventually hu (hbound.mono fun n hn w hw => ?_)
    have hcoord (i : Fin 3) : ‖w i‖ ≤ ‖v i‖ + r := by
      have h1 := norm_le_norm_add_norm_sub' (w i) (v i)
      have h2 : ‖w i - v i‖ ≤ r := by
        simpa [dist_eq_norm] using (dist_le_pi_dist w v i).trans (mem_closedBall.mp hw)
      linarith
    simpa [lerchSeriesTerm] using hn (hcoord 0) (hcoord 1) (hcoord 2)
  have hcont : ContinuousOn (fun w : Fin 3 → ℂ => lerchSeries (w 0) (w 1) (w 2))
      (closedBall v r) := by
    refine hunif.continuousOn (Frequently.of_forall fun N => ?_)
    induction N with
    | zero => simp [continuousOn_const]
    | succ N ih =>
      simp_rw [Finset.sum_range_succ]
      refine ih.add fun w hw => ContinuousAt.continuousWithinAt ?_
      have hnw : (N : ℂ) + w 2 ∈ Complex.slitPlane :=
        ofReal_add_mem_slitPlane (hV_lt w hw).2 (Nat.cast_nonneg N)
      unfold lerchSeriesTerm
      refine ((continuous_apply 0).continuousAt.pow N).mul (ContinuousAt.cexp ?_)
      exact (continuous_apply 1).continuousAt.neg.mul
        ((continuousAt_const.add (continuous_apply 2).continuousAt).clog hnw)
  refine hcont.analyticAt_of_differentiableAt_update (closedBall_mem_nhds v hr) ?_
  intro w hw i
  fin_cases i
  · simpa using (hasDerivAt_lerchSeries_left (hV_lt w hw).1 (w 1) (w 2)).differentiableAt
  · simpa using (hasDerivAt_lerchSeries_mid (hV_lt w hw).1 (w 1) (w 2)).differentiableAt
  · simpa using (hasDerivAt_lerchSeries_right (hV_lt w hw).1 (w 1) (hV_lt w hw).2).differentiableAt

end TauCeti

/-- Simultaneous analytic substitution into the three arguments of `TauCeti.lerchSeries`. -/
theorem AnalyticAt.lerchSeries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g h : E → ℂ} {p : E} (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hh : AnalyticAt ℂ h p) (hfp : ‖f p‖ < 1) (hhp : h p ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun q => TauCeti.lerchSeries (f q) (g q) (h q)) p := by
  have ha : AnalyticAt ℂ (fun q => ![f q, g q, h q]) p := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    fin_cases i
    · simpa using hf
    · simpa using hg
    · simpa using hh
  exact (TauCeti.analyticAt_lerchSeries_pi (v := ![f p, g p, h p]) hfp hhp).comp
    (f := fun q => ![f q, g q, h q]) ha

namespace TauCeti

/-- Joint analyticity of `lerchSeries` on `{p : ℂ × ℂ × ℂ | ‖p.1‖ < 1 ∧ p.2.2 ∈ slitPlane}`. -/
theorem analyticOnNhd_lerchSeries :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => lerchSeries p.1 p.2.1 p.2.2)
      {p : ℂ × ℂ × ℂ | ‖p.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane} :=
  fun _ hp => analyticAt_fst.lerchSeries (analyticAt_fst.comp analyticAt_snd)
    (analyticAt_snd.comp analyticAt_snd) hp.1 hp.2

/-- Joint complex differentiability of `lerchSeries` on
`{p : ℂ × ℂ × ℂ | ‖p.1‖ < 1 ∧ p.2.2 ∈ slitPlane}`. -/
theorem differentiableOn_lerchSeries :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => lerchSeries p.1 p.2.1 p.2.2)
      {p : ℂ × ℂ × ℂ | ‖p.1‖ < 1 ∧ p.2.2 ∈ Complex.slitPlane} :=
  analyticOnNhd_lerchSeries.differentiableOn

/-! ### Closed-disc convergence, periodic/Hurwitz specializations, and radial limits -/

/-- For `1 < s.re` and arbitrary `c ∈ ℂ`, the Hurwitz-type tail `‖exp (-s * log (n + c))‖` is
summable. -/
theorem summable_norm_exp_neg_mul_log {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable fun n : ℕ => ‖Complex.exp (-s * Complex.log (n + c))‖ := by
  set C : ℝ := Real.exp (|s.im| * Real.pi) * (2 : ℝ) ^ s.re
  have hu : Summable fun n : ℕ => C * (n : ℝ) ^ (-s.re) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left C
  refine Summable.of_norm_bounded_eventually_nat hu ?_
  filter_upwards [eventually_ge_atTop (2 * (⌈‖c‖⌉₊ + 1))] with n hn
  have hn_cast : 2 * (‖c‖ + 1) ≤ (n : ℝ) := by
    have : (2 * (⌈‖c‖⌉₊ + 1) : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Nat.le_ceil ‖c‖]
  have hn2 : (0 : ℝ) < (n : ℝ) / 2 := by linarith [norm_nonneg c]
  have hlow : (n : ℝ) / 2 ≤ ‖(n : ℂ) + c‖ := by
    have h := norm_sub_le ((n : ℂ) + c) c
    rw [add_sub_cancel_right, Complex.norm_natCast] at h
    linarith
  have hlog : Real.log ((n : ℝ) / 2) ≤ Real.log ‖(n : ℂ) + c‖ := Real.log_le_log hn2 hlow
  have hre : (-s * Complex.log (n + c)).re ≤ |s.im| * Real.pi - s.re * Real.log ((n : ℝ) / 2) := by
    rw [mul_re, neg_re, neg_im, log_re, log_im]
    have h1 : -s.re * Real.log ‖(n : ℂ) + c‖ ≤ -s.re * Real.log ((n : ℝ) / 2) :=
      mul_le_mul_of_nonpos_left hlog (by linarith)
    have h2 : s.im * ((n : ℂ) + c).arg ≤ |s.im| * Real.pi :=
      (le_abs_self _).trans <| (abs_mul _ _).le.trans <|
        mul_le_mul_of_nonneg_left (abs_arg_le_pi _) (abs_nonneg _)
    linarith
  rw [Real.norm_of_nonneg (norm_nonneg _), Complex.norm_exp]
  calc Real.exp ((-s * Complex.log (n + c)).re)
      ≤ Real.exp (|s.im| * Real.pi + -s.re * Real.log ((n : ℝ) / 2)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (|s.im| * Real.pi) * ((n : ℝ) / 2) ^ (-s.re) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hn2]
        congr 2; ring
    _ = C * (n : ℝ) ^ (-s.re) := by
        rw [div_eq_mul_inv, Real.mul_rpow (by linarith) (by positivity),
          Real.inv_rpow zero_le_two, Real.rpow_neg zero_le_two, inv_inv]
        simp only [C]; ring

/-- On the closed unit disc `‖z‖ ≤ 1`, the Lerch series converges absolutely whenever `1 < s.re`. -/
theorem summable_lerchSeriesTerm_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re)
    (c : ℂ) : Summable fun n : ℕ => lerchSeriesTerm n z s c := by
  refine .of_norm_bounded (summable_norm_exp_neg_mul_log hs c) fun n => ?_
  rw [lerchSeriesTerm, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) hz)

/-- For `1 < s.re` and arbitrary `c ∈ ℂ`, `z ↦ lerchSeries z s c` is continuous on the closed unit
disc `closedBall 0 1`. -/
theorem continuousOn_lerchSeries_closedBall {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    ContinuousOn (fun z => lerchSeries z s c) (closedBall 0 1) := by
  refine continuousOn_tsum (fun n => by unfold lerchSeriesTerm; fun_prop)
    (summable_norm_exp_neg_mul_log hs c) fun n z hz => ?_
  rw [mem_closedBall_zero_iff] at hz
  rw [lerchSeriesTerm, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) hz)

/-- Comparison with Mathlib's periodic zeta function `HurwitzZeta.expZeta`: for `a : ℝ` and
`1 < s.re`, `expZeta a s = exp (2 * π * I * a) * lerchSeries (exp (2 * π * I * a)) s 1`. -/
theorem expZeta_eq_mul_lerchSeries (a : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.expZeta a s =
      Complex.exp (2 * Real.pi * I * a) *
        lerchSeries (Complex.exp (2 * Real.pi * I * a)) s 1 := by
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; linarith
  have hsum := (hasSum_nat_add_iff' 1).mpr (HurwitzZeta.hasSum_expZeta_of_one_lt_re a hs)
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, Complex.exp_zero,
    Complex.zero_cpow hs0, div_zero, sub_zero] at hsum
  let z : ℂ := Complex.exp (2 * Real.pi * I * a)
  rw [← hsum.tsum_eq, lerchSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hn0 : ((n : ℂ) + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  calc Complex.exp (2 * Real.pi * I * a * ↑(n + 1)) / (↑(n + 1) : ℂ) ^ s
      = z * z ^ n * (((n : ℂ) + 1) ^ (-s)) := by
        push_cast
        rw [mul_add, mul_one, Complex.exp_add, mul_comm (2 * Real.pi * I * a) (n : ℂ),
          Complex.exp_nat_mul, Complex.cpow_neg, div_eq_mul_inv]
        dsimp only [z]; ring
    _ = z * lerchSeriesTerm n z s 1 := by
        rw [lerchSeriesTerm, Complex.cpow_def_of_ne_zero hn0, mul_comm (Complex.log _) (-s),
          mul_assoc]

/-- Comparison with Mathlib's Hurwitz zeta function `HurwitzZeta.hurwitzZeta` on `a ∈ Ioc 0 1` and
`1 < s.re`: `hurwitzZeta a s = lerchSeries 1 s a`. -/
theorem hurwitzZeta_eq_lerchSeries {a : ℝ} (ha : a ∈ Ioc 0 1) {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.hurwitzZeta a s = lerchSeries 1 s a := by
  rw [← (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (Ioc_subset_Icc_self ha) hs).tsum_eq,
    lerchSeries]
  refine tsum_congr fun n => ?_
  have hna : (n : ℂ) + a ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [ha.1]
  rw [lerchSeriesTerm, one_pow, one_mul, one_div, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero hna, mul_comm]

/-- Radial Hurwitz limit: for `1 < s.re` and arbitrary `c ∈ ℂ`, as `r → 1⁻` along `(0, 1)`,
`lerchSeries r s c` converges to the Hurwitz series `∑' n : ℕ, exp (-s * log (n + c))`. -/
theorem tendsto_lerchSeries_nhdsLT_one {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Tendsto (fun r : ℝ => lerchSeries r s c) (𝓝[<] 1)
      (𝓝 (∑' n : ℕ, Complex.exp (-s * Complex.log (n + c)))) := by
  have h1 : lerchSeries 1 s c = ∑' n : ℕ, Complex.exp (-s * Complex.log (n + c)) := by
    simp [lerchSeries, lerchSeriesTerm]
  rw [← h1]
  have hcont := (continuousOn_lerchSeries_closedBall hs c) 1 (by simp)
  refine hcont.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
  · simpa using (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr.1.le]
    exact hr.2.le

/-- Radial norm divergence at `s = 0`: as `r → 1⁻`, `‖lerchSeries r 0 c‖ → +∞` for every `c ∈ ℂ`. -/
theorem tendsto_norm_lerchSeries_zero_nhdsLT_one (c : ℂ) :
    Tendsto (fun r : ℝ => ‖lerchSeries r 0 c‖) (𝓝[<] 1) atTop := by
  have hsub : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun r : ℝ => 1 - r) := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : r < 1) using sub_pos.mpr hr
  refine (tendsto_inv_nhdsGT_zero.comp hsub).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  have hr_norm : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.1.le]
    exact hr.2
  rw [Function.comp_apply, lerchSeries_zero_mid hr_norm c, norm_inv, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (sub_pos.mpr hr.2).le]

end TauCeti
