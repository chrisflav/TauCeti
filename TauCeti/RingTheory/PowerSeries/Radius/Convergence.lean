/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Radius.Basic
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Convergence of power series in extensions and the convergence-point radius

Let `f = ∑ aₙ Xⁿ` be a power series over a normed ring `R` and let `A` be a seminormed ring over
`R` with norm-preserving scalar multiplication and a multiplicative norm (`‖r • x‖ = ‖r‖ ‖x‖` and
`‖x * y‖ = ‖x‖ ‖y‖`), such as a normed field extension `L / K`. For `n ≥ 1` the `n`-th term of
`f(x) = ∑ aₙ • xⁿ` has norm `‖aₙ • xⁿ‖ = ‖aₙ‖ ‖x‖ⁿ`. Consequently:

* if `∑ aₙ • xⁿ` is summable at `x : A`, its terms tend to zero, so `f` is restricted at `‖x‖` and
  `‖x‖ₑ ≤ f.radius` (`PowerSeries.isRestricted_of_summable_smul_pow`,
  `PowerSeries.le_radius_of_summable_smul_pow`), with neither completeness nor an ultrametric
  hypothesis;
* in any complete target `A` with bounded scalar action, `∑ aₙ • xⁿ` is absolutely summable and
  sums to `f.evalAt x` at every `x` with `‖x‖ₑ < f.radius`
  (`PowerSeries.summable_norm_smul_pow_of_lt_radius`, `PowerSeries.hasSum_evalAt_of_lt_radius`);
* when `A` is complete and ultrametric, summability of `∑ aₙ • xⁿ` at `x` is equivalent to
  `f.IsRestricted ‖x‖` (`PowerSeries.summable_smul_pow_iff_isRestricted`). At a restricted radius
  `r`, the series converges on the entire closed ball `{y : A | ‖y‖ ≤ r}` with the Gauss-norm
  evaluation bound `‖f.evalAt y‖ ≤ gaussNorm norm r f`
  (`PowerSeries.IsRestricted.summable_smul_pow`, `PowerSeries.IsRestricted.hasSum_evalAt`,
  `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm`), and conversely convergence throughout
  `{y : A | ‖y‖ ≤ r}` implies `f.IsRestricted r` whenever `r` is attained by a norm in `A`
  (`PowerSeries.forall_norm_le_summable_iff_isRestricted`).

Because `PowerSeries.radius f` is an intrinsic invariant of the coefficient norms, it does not
change when an extension is introduced. The supremum of `‖x‖ₑ` over the convergence points `x : A`
is defined separately as `PowerSeries.convergencePointRadius A f`. It never exceeds `f.radius`
(`PowerSeries.convergencePointRadius_le_radius`), so `∑ aₙ • xⁿ` converges absolutely at every `x`
strictly inside `f.convergencePointRadius A` without any ultrametric assumption
(`PowerSeries.summable_smul_pow_of_lt_convergencePointRadius`,
`PowerSeries.hasSum_evalAt_of_lt_convergencePointRadius`), and it equals `f.radius` when `A` is
complete and its positive norms are dense in `(0, ∞)`
(`PowerSeries.convergencePointRadius_eq_radius_of_Ioi_subset_closure`,
`PowerSeries.convergencePointRadius_eq_radius`). When the norms of `A` omit an open interval
`(r₁, r₂)` containing `f.radius`, `f.convergencePointRadius A ≤ r₁ < f.radius`
(`PowerSeries.convergencePointRadius_lt_radius_of_lt_radius_of_radius_lt`); in particular, when the
nonzero norms of `A` lie in `{b ^ m | m : ℤ}` with `b > 1` and `f.radius = b ^ t` for a
non-integer `t`, the convergence-point radius rounds down to `b ^ ⌊t⌋` whenever that norm is
attained and is strictly smaller than `f.radius`
(`PowerSeries.convergencePointRadius_le_ofReal_zpow_floor`,
`PowerSeries.convergencePointRadius_eq_ofReal_zpow_floor`,
`PowerSeries.convergencePointRadius_lt_radius_of_forall_intCast_ne`).

## Main definitions

* `PowerSeries.convergencePointRadius A f`: the supremum in `ℝ≥0∞` of `‖x‖ₑ` over the points
  `x : A` at which `∑ aₙ • xⁿ` is summable.

## Main results

* `PowerSeries.tendsto_smul_pow_atTop_nhds_zero_iff_isRestricted` and
  `PowerSeries.summable_smul_pow_iff_isRestricted`: term decay, and in a complete ultrametric
  target summability, at `x` are equivalent to `f.IsRestricted ‖x‖`.
* `PowerSeries.forall_norm_le_summable_iff_isRestricted` and
  `PowerSeries.forall_norm_le_hasSum_evalAt_iff_isRestricted`: closed-ball convergence at an
  attained radius `r` is equivalent to `f.IsRestricted r`.
* `PowerSeries.IsRestricted.norm_evalAt_le_gaussNorm`: `‖f.evalAt y‖ ≤ gaussNorm norm r f` on the
  closed ball `{y | ‖y‖ ≤ r}` at a restricted radius `r`.
* `PowerSeries.convergencePointRadius_le_iff`, `PowerSeries.lt_convergencePointRadius_iff`, and
  `PowerSeries.not_summable_smul_pow_of_convergencePointRadius_lt`: universal property and exterior
  divergence for `convergencePointRadius`.
* `PowerSeries.convergencePointRadius_le_radius`,
  `PowerSeries.summable_smul_pow_of_lt_convergencePointRadius`, and
  `PowerSeries.hasSum_evalAt_of_lt_convergencePointRadius`: upper bound by `f.radius` and interior
  convergence.
* `PowerSeries.convergencePointRadius_eq_radius_of_forall_exists_lt_norm_lt`,
  `PowerSeries.convergencePointRadius_eq_radius_of_Ioi_subset_closure`, and
  `PowerSeries.convergencePointRadius_eq_radius`: equality when the positive norms of a complete
  target are dense in `(0, ∞)`.
* `PowerSeries.convergencePointRadius_le_of_radius_lt`,
  `PowerSeries.convergencePointRadius_lt_radius_of_lt_radius_of_radius_lt`,
  `PowerSeries.convergencePointRadius_le_ofReal_zpow_floor`,
  `PowerSeries.convergencePointRadius_eq_ofReal_zpow_floor`, and
  `PowerSeries.convergencePointRadius_lt_radius_of_forall_intCast_ne`: gap bounds and discrete-norm
  rounding, with strict inequality `f.convergencePointRadius A < f.radius` across norm gaps.
* `PowerSeries.min_convergencePointRadius_le_convergencePointRadius_add` and
  `PowerSeries.min_convergencePointRadius_le_convergencePointRadius_mul`: ultrametric sum and
  product bounds.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §1.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 6 §1.
-/

public section

namespace PowerSeries

open Filter
open scoped NNReal ENNReal Topology

section Pointwise

section NormSMul

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMulZeroClass R A]
  [NormSMulClass R A] [NormMulClass A] {f : R⟦X⟧} {x : A} {r : ℝ}

/-- When `A` has a multiplicative norm and norm-preserving scalar multiplication, the terms
`aₙ • xⁿ` tend to zero if and only if `f` is restricted at `‖x‖`. -/
theorem tendsto_smul_pow_atTop_nhds_zero_iff_isRestricted :
    Tendsto (fun n ↦ coeff n f • x ^ n) atTop (𝓝 0) ↔ f.IsRestricted ‖x‖ := by
  rw [tendsto_iff_norm_sub_tendsto_zero, isRestricted_iff']
  refine tendsto_congr' ?_
  -- `‖xⁿ‖ = ‖x‖ⁿ` needs `n ≥ 1` without `NormOneClass A`.
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [sub_zero, norm_smul]
  refine congrArg (‖coeff n f‖ * ·) ?_
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k _ ih => rw [pow_succ x k, norm_mul, ih, ← pow_succ]

/-- Summability of `∑ aₙ • xⁿ` at `x` implies that `f` is restricted at `‖x‖`. -/
theorem isRestricted_of_summable_smul_pow (h : Summable fun n ↦ coeff n f • x ^ n) :
    f.IsRestricted ‖x‖ :=
  tendsto_smul_pow_atTop_nhds_zero_iff_isRestricted.mp h.tendsto_atTop_zero

/-- If `∑ aₙ • xⁿ` is summable at `x`, then `‖x‖ₑ ≤ f.radius`. -/
theorem le_radius_of_summable_smul_pow (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.radius := by
  simpa using le_radius_of_isRestricted (isRestricted_of_summable_smul_pow h)

/-- If `∑ aₙ • yⁿ` is summable at every point `y` of the closed ball `{y : A | ‖y‖ ≤ r}` and `r`
is attained by a norm in `A`, then `f` is restricted at `r`. -/
theorem isRestricted_of_forall_norm_le_summable
    (h : ∀ y : A, ‖y‖ ≤ r → Summable fun n ↦ coeff n f • y ^ n) (hr : ∃ x : A, ‖x‖ = r) :
    f.IsRestricted r := by
  obtain ⟨x, rfl⟩ := hr
  exact isRestricted_of_summable_smul_pow (h x le_rfl)

end NormSMul

section Interior

/-- Strictly inside `f.radius`, the terms `aₙ • xⁿ` are absolutely summable in any seminormed ring
with a bounded scalar action. -/
theorem summable_norm_smul_pow_of_lt_radius {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMulZeroClass R A] [IsBoundedSMul R A] {f : R⟦X⟧} {x : A} (hx : ‖x‖ₑ < f.radius) :
    Summable fun n ↦ ‖coeff n f • x ^ n‖ := by
  obtain ⟨r, hxr, hrf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hx
  have hf : f.IsRestricted r := isRestricted_of_lt_radius (by simpa using hrf)
  have hxr' : |‖x‖| < |(r : ℝ)| := by
    rw [abs_norm, abs_of_nonneg r.coe_nonneg, ← coe_nnNorm]
    exact NNReal.coe_lt_coe.mpr (eNorm_lt_coe.mp hxr)
  exact summable_norm_smul_pow_of_summable_norm_mul_pow (hf.summable_norm_coeff_mul_pow hxr')

/-- Strictly inside `f.radius`, the series `∑ aₙ • xⁿ` is summable in any complete seminormed ring
with a bounded scalar action. -/
theorem summable_smul_pow_of_lt_radius {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMulZeroClass R A] [IsBoundedSMul R A] [CompleteSpace A] {f : R⟦X⟧} {x : A}
    (hx : ‖x‖ₑ < f.radius) : Summable fun n ↦ coeff n f • x ^ n :=
  (summable_norm_smul_pow_of_lt_radius hx).of_norm

/-- Strictly inside `f.radius`, the series `∑ aₙ • xⁿ` sums to `f.evalAt x` in any complete
seminormed algebra with a bounded scalar action. -/
theorem hasSum_evalAt_of_lt_radius {R A : Type*} [NormedCommRing R] [SeminormedRing A]
    [Algebra R A] [IsBoundedSMul R A] [CompleteSpace A] {f : R⟦X⟧} {x : A}
    (hx : ‖x‖ₑ < f.radius) : HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) :=
  hasSum_evalAt_of_summable_norm (summable_norm_smul_pow_of_lt_radius hx)

end Interior

section Ultrametric

/-- In a complete ultrametric seminormed target with bounded scalar action, a series `f` restricted
at `r` is summable at every point `y` of the closed ball `{y | ‖y‖ ≤ r}`. -/
theorem IsRestricted.summable_smul_pow {R A : Type*} [NormedRing R] [SeminormedRing A]
    [SMulZeroClass R A] [IsBoundedSMul R A] [IsUltrametricDist A] [CompleteSpace A]
    {f : R⟦X⟧} {r : ℝ} (hf : f.IsRestricted r) {y : A} (hy : ‖y‖ ≤ r) :
    Summable fun n ↦ coeff n f • y ^ n :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (hf.tendsto_smul_pow hy)

/-- In an ultrametric normed algebra with `‖1‖ = 1`, the value of a series restricted at `r` on the
closed ball `{y | ‖y‖ ≤ r}` is bounded in norm by the Gauss norm at `r`. -/
theorem IsRestricted.norm_evalAt_le_gaussNorm {R A : Type*} [NormedCommRing R] [NormedRing A]
    [NormOneClass A] [Algebra R A] [IsBoundedSMul R A] [IsUltrametricDist A]
    {f : R⟦X⟧} {r : ℝ} (hf : f.IsRestricted r) {y : A} (hy : ‖y‖ ≤ r) :
    ‖f.evalAt y‖ ≤ gaussNorm norm r f :=
  PowerSeries.norm_evalAt_le_gaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf) hy

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [Module R A]
  [NormSMulClass R A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
  {f : R⟦X⟧} {x : A} {r : ℝ}

/-- **Ultrametric pointwise convergence criterion.** In a complete ultrametric target with a
multiplicative norm and norm-preserving scalar multiplication, `∑ aₙ • xⁿ` is summable at `x` if
and only if `f` is restricted at `‖x‖`. -/
theorem summable_smul_pow_iff_isRestricted :
    (Summable fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted ‖x‖ :=
  ⟨isRestricted_of_summable_smul_pow, fun hf ↦ hf.summable_smul_pow le_rfl⟩

/-- **Closed-ball convergence characterization.** When the radius `r` is attained by a norm in a
complete ultrametric target `A`, `∑ aₙ • yⁿ` is summable throughout `{y : A | ‖y‖ ≤ r}` if and only
if `f` is restricted at `r`. -/
theorem forall_norm_le_summable_iff_isRestricted (hr : ∃ x : A, ‖x‖ = r) :
    (∀ y : A, ‖y‖ ≤ r → Summable fun n ↦ coeff n f • y ^ n) ↔ f.IsRestricted r :=
  ⟨fun h ↦ isRestricted_of_forall_norm_le_summable h hr, fun hf _ hy ↦ hf.summable_smul_pow hy⟩

/-- When the radius `r` is attained by a norm in a complete ultrametric seminormed algebra `A`, the
series `∑ aₙ • yⁿ` sums to `f.evalAt y` throughout `{y : A | ‖y‖ ≤ r}` if and only if `f` is
restricted at `r`. -/
theorem forall_norm_le_hasSum_evalAt_iff_isRestricted {R A : Type*} [NormedCommRing R]
    [SeminormedRing A] [Algebra R A] [NormSMulClass R A] [NormMulClass A]
    [IsUltrametricDist A] [CompleteSpace A] {f : R⟦X⟧} {r : ℝ} (hr : ∃ x : A, ‖x‖ = r) :
    (∀ y : A, ‖y‖ ≤ r → HasSum (fun n ↦ coeff n f • y ^ n) (f.evalAt y)) ↔ f.IsRestricted r :=
  ⟨fun h ↦ isRestricted_of_forall_norm_le_summable (fun y hy ↦ (h y hy).summable) hr,
    fun hf _ hy ↦ hf.hasSum_evalAt hy⟩

end Ultrametric

end Pointwise

section ConvergencePointRadius

section Semiring

variable {R : Type*} [Semiring R]

/-- The *convergence-point radius* of a power series `f = ∑ aₙ Xⁿ` in a seminormed target `A`: the
supremum, in `ℝ≥0∞`, of `‖x‖ₑ` over the points `x : A` at which `∑ aₙ • xⁿ` is summable. Unlike
`PowerSeries.radius`, this quantity depends on the norms attained in `A`. -/
noncomputable def convergencePointRadius (A : Type*) [SeminormedRing A] [SMul R A] (f : R⟦X⟧) :
    ℝ≥0∞ :=
  ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ

/-- The convergence-point radius as the supremum of `‖x‖ₑ` over convergence points `x : A`. -/
theorem convergencePointRadius_def (A : Type*) [SeminormedRing A] [SMul R A] (f : R⟦X⟧) :
    f.convergencePointRadius A = ⨆ (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n), ‖x‖ₑ :=
  (rfl)

/-- Every convergence point `x : A` of `f` has extended norm at most
`f.convergencePointRadius A`. -/
theorem le_convergencePointRadius_of_summable {A : Type*} [SeminormedRing A] [SMul R A] {f : R⟦X⟧}
    {x : A} (h : Summable fun n ↦ coeff n f • x ^ n) :
    ‖x‖ₑ ≤ f.convergencePointRadius A :=
  le_iSup₂ (f := fun (x : A) (_ : Summable fun n ↦ coeff n f • x ^ n) ↦ ‖x‖ₑ) x h

/-- The convergence-point radius is at most `r` if and only if every convergence point `x : A` of
`f` has extended norm at most `r`. -/
theorem convergencePointRadius_le_iff {A : Type*} [SeminormedRing A] [SMul R A] {f : R⟦X⟧}
    {r : ℝ≥0∞} :
    f.convergencePointRadius A ≤ r ↔
      ∀ x : A, (Summable fun n ↦ coeff n f • x ^ n) → ‖x‖ₑ ≤ r :=
  iSup₂_le_iff

/-- A bound `r` is strictly below `f.convergencePointRadius A` if and only if `f` is summable at
some point `x : A` of extended norm strictly above `r`. -/
theorem lt_convergencePointRadius_iff {A : Type*} [SeminormedRing A] [SMul R A] {f : R⟦X⟧}
    {r : ℝ≥0∞} :
    r < f.convergencePointRadius A ↔
      ∃ x : A, (Summable fun n ↦ coeff n f • x ^ n) ∧ r < ‖x‖ₑ := by
  simp only [convergencePointRadius, lt_iSup_iff, exists_prop]

/-- A power series is not summable at any point `x : A` of extended norm strictly above
`f.convergencePointRadius A`. -/
theorem not_summable_smul_pow_of_convergencePointRadius_lt {A : Type*} [SeminormedRing A]
    [SMul R A] {f : R⟦X⟧} {x : A} (h : f.convergencePointRadius A < ‖x‖ₑ) :
    ¬Summable fun n ↦ coeff n f • x ^ n :=
  fun hs ↦ (le_convergencePointRadius_of_summable hs).not_gt h

/-- Extending scalars along an algebra homomorphism does not change the convergence-point radius in
any target with a compatible scalar action. -/
@[simp]
theorem convergencePointRadius_map_algebraMap {R S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] (A : Type*) [SeminormedRing A] [SMul R A] [MulAction S A]
    [IsScalarTower R S A] (f : R⟦X⟧) :
    (f.map (algebraMap R S)).convergencePointRadius A = f.convergencePointRadius A := by
  simp [convergencePointRadius, coeff_map, IsScalarTower.algebraMap_smul]

/-- The zero series converges at every point of `A`, so its convergence-point radius is
`⨆ x : A, ‖x‖ₑ`. -/
theorem convergencePointRadius_zero_eq_iSup (A : Type*) [SeminormedRing A] [SMulWithZero R A] :
    (0 : R⟦X⟧).convergencePointRadius A = ⨆ x : A, ‖x‖ₑ := by
  refine iSup_congr fun x ↦ iSup_pos ?_
  simp

/-- A polynomial converges at every point of `A`, so its convergence-point radius is
`⨆ x : A, ‖x‖ₑ`. -/
theorem convergencePointRadius_coe_eq_iSup (A : Type*) [SeminormedRing A] [SMulWithZero R A]
    (p : Polynomial R) : (p : R⟦X⟧).convergencePointRadius A = ⨆ x : A, ‖x‖ₑ := by
  refine iSup_congr fun x ↦ iSup_pos <|
    summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn ↦ ?_
  rw [Finset.mem_range, not_lt] at hn
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- Over a nontrivially normed field `L`, the zero series has infinite convergence-point radius. -/
@[simp]
theorem convergencePointRadius_zero (L : Type*) [NontriviallyNormedField L] [SMulWithZero R L] :
    (0 : R⟦X⟧).convergencePointRadius L = ⊤ := by
  rw [convergencePointRadius_zero_eq_iSup]
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨x, hx⟩ := NormedField.exists_lt_nnNorm L r
  exact (by rw [eNorm_eq_nnNorm]; exact ENNReal.coe_le_coe.mpr hx.le : (r : ℝ≥0∞) ≤ ‖x‖ₑ).trans
    (le_iSup _ x)

/-- Over a nontrivially normed field `L`, polynomials have infinite convergence-point radius. -/
@[simp]
theorem convergencePointRadius_coe (L : Type*) [NontriviallyNormedField L] [SMulWithZero R L]
    (p : Polynomial R) : (p : R⟦X⟧).convergencePointRadius L = ⊤ := by
  rw [convergencePointRadius_coe_eq_iSup, ← convergencePointRadius_zero_eq_iSup (R := R),
    convergencePointRadius_zero]

/-- Over a nontrivially normed field `L`, the constant series `1` has infinite convergence-point
radius. -/
@[simp]
theorem convergencePointRadius_one (L : Type*) [NontriviallyNormedField L] [SMulWithZero R L] :
    (1 : R⟦X⟧).convergencePointRadius L = ⊤ := by
  rw [← Polynomial.coe_one, convergencePointRadius_coe]

/-- Over a nontrivially normed field `L`, constant series have infinite convergence-point
radius. -/
@[simp]
theorem convergencePointRadius_C (L : Type*) [NontriviallyNormedField L] [SMulWithZero R L]
    (a : R) : (C a).convergencePointRadius L = ⊤ := by
  rw [← Polynomial.coe_C, convergencePointRadius_coe]

/-- Over a nontrivially normed field `L`, the variable `X` has infinite convergence-point radius. -/
@[simp]
theorem convergencePointRadius_X (L : Type*) [NontriviallyNormedField L] [SMulWithZero R L] :
    (X : R⟦X⟧).convergencePointRadius L = ⊤ := by
  rw [← Polynomial.coe_X, convergencePointRadius_coe]

/-- Over a nontrivially normed field `L`, monomials have infinite convergence-point radius. -/
@[simp]
theorem convergencePointRadius_monomial (L : Type*) [NontriviallyNormedField L]
    [SMulWithZero R L] (n : ℕ) (a : R) :
    (monomial n a).convergencePointRadius L = ⊤ := by
  rw [← Polynomial.coe_monomial, convergencePointRadius_coe]

end Semiring

/-- Negating a power series preserves its convergence-point radius. -/
@[simp]
theorem convergencePointRadius_neg {R A : Type*} [Ring R] [SeminormedRing A] [Module R A]
    (f : R⟦X⟧) : (-f).convergencePointRadius A = f.convergencePointRadius A := by
  simp only [convergencePointRadius, map_neg, neg_smul, summable_neg_iff]

/-- An entire series converges at every point of a complete target `A` with bounded scalar action,
so its convergence-point radius in `A` is `⨆ x : A, ‖x‖ₑ`. -/
theorem IsEntire.convergencePointRadius_eq_iSup {R : Type*} [NormedRing R] {f : R⟦X⟧}
    (hf : f.IsEntire) (A : Type*) [SeminormedRing A] [SMulZeroClass R A] [IsBoundedSMul R A]
    [CompleteSpace A] :
    f.convergencePointRadius A = ⨆ x : A, ‖x‖ₑ :=
  iSup_congr fun x ↦ iSup_pos <|
    summable_smul_pow_of_lt_radius (by rw [radius_eq_top_iff.mpr hf]; exact eNorm_lt_top)

/-- Over a complete nontrivially normed field `L` with bounded scalar action, an entire series has
infinite convergence-point radius. -/
theorem IsEntire.convergencePointRadius_eq_top {R : Type*} [NormedRing R] {f : R⟦X⟧}
    (hf : f.IsEntire) (L : Type*) [NontriviallyNormedField L] [SMulZeroClass R L]
    [IsBoundedSMul R L] [CompleteSpace L] :
    f.convergencePointRadius L = ⊤ := by
  rw [hf.convergencePointRadius_eq_iSup]
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨x, hx⟩ := NormedField.exists_lt_nnNorm L r
  exact (by rw [eNorm_eq_nnNorm]; exact ENNReal.coe_le_coe.mpr hx.le : (r : ℝ≥0∞) ≤ ‖x‖ₑ).trans
    (le_iSup _ x)

section Comparison

variable {R A : Type*} [NormedRing R] [SeminormedRing A] {f : R⟦X⟧}

/-- **Upper bound by the intrinsic radius.** When `A` has a multiplicative norm and norm-preserving
scalar multiplication, the convergence-point radius in `A` is at most `f.radius`. -/
theorem convergencePointRadius_le_radius [SMulZeroClass R A] [NormSMulClass R A] [NormMulClass A] :
    f.convergencePointRadius A ≤ f.radius :=
  iSup₂_le fun _ hx ↦ le_radius_of_summable_smul_pow hx

/-- Strictly inside `f.convergencePointRadius A`, the terms `aₙ • xⁿ` are absolutely summable in
any seminormed module ring with a multiplicative norm and norm-preserving scalar multiplication. -/
theorem summable_norm_smul_pow_of_lt_convergencePointRadius [Module R A] [NormSMulClass R A]
    [NormMulClass A] {x : A} (hx : ‖x‖ₑ < f.convergencePointRadius A) :
    Summable fun n ↦ ‖coeff n f • x ^ n‖ :=
  summable_norm_smul_pow_of_lt_radius (hx.trans_le convergencePointRadius_le_radius)

/-- Strictly inside `f.convergencePointRadius A`, the series `∑ aₙ • xⁿ` is summable in any
complete seminormed module ring with a multiplicative norm and norm-preserving scalar
multiplication. -/
theorem summable_smul_pow_of_lt_convergencePointRadius [Module R A] [NormSMulClass R A]
    [NormMulClass A] [CompleteSpace A] {x : A} (hx : ‖x‖ₑ < f.convergencePointRadius A) :
    Summable fun n ↦ coeff n f • x ^ n :=
  summable_smul_pow_of_lt_radius (hx.trans_le convergencePointRadius_le_radius)

/-- Strictly inside `f.convergencePointRadius A`, the series `∑ aₙ • xⁿ` sums to `f.evalAt x` in
any complete seminormed algebra with a multiplicative norm and norm-preserving scalar
multiplication. -/
theorem hasSum_evalAt_of_lt_convergencePointRadius {R A : Type*} [NormedCommRing R]
    [SeminormedRing A] [Algebra R A] [NormSMulClass R A] [NormMulClass A] [CompleteSpace A]
    {f : R⟦X⟧} {x : A} (hx : ‖x‖ₑ < f.convergencePointRadius A) :
    HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) :=
  hasSum_evalAt_of_lt_radius (hx.trans_le convergencePointRadius_le_radius)

/-- **Lower bound from dense positive norms.** In a complete target `A` with bounded scalar action
whose norms separate any two radii `0 ≤ r₁ < r₂`, `f.radius ≤ f.convergencePointRadius A`. -/
theorem le_convergencePointRadius_of_forall_exists_lt_norm_lt [SMulZeroClass R A]
    [IsBoundedSMul R A] [CompleteSpace A]
    (hdense : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → r₁ < r₂ → ∃ x : A, r₁ < ‖x‖ ∧ ‖x‖ < r₂) :
    f.radius ≤ f.convergencePointRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  obtain ⟨s, hrs, hsf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  obtain ⟨x, hrx, hxs⟩ := hdense r s r.coe_nonneg (mod_cast hrs)
  have hx_lt : ‖x‖ₑ < f.radius := by
    refine (eNorm_lt_coe.mpr ?_).trans hsf
    rw [← NNReal.coe_lt_coe, coe_nnNorm]
    exact hxs
  have hrx' : (r : ℝ≥0∞) ≤ ‖x‖ₑ := by
    rw [eNorm_eq_nnNorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]
    exact hrx.le
  exact hrx'.trans (le_convergencePointRadius_of_summable (summable_smul_pow_of_lt_radius hx_lt))

/-- **Equality for dense positive norms**, interval form. In a complete target `A` with a
multiplicative norm and norm-preserving scalar multiplication in which every interval `(r₁, r₂)`
with `0 ≤ r₁ < r₂` contains a norm of `A`, the convergence-point radius equals `f.radius`. -/
theorem convergencePointRadius_eq_radius_of_forall_exists_lt_norm_lt [Module R A]
    [NormSMulClass R A] [NormMulClass A] [CompleteSpace A]
    (hdense : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → r₁ < r₂ → ∃ x : A, r₁ < ‖x‖ ∧ ‖x‖ < r₂) :
    f.convergencePointRadius A = f.radius :=
  le_antisymm convergencePointRadius_le_radius
    (le_convergencePointRadius_of_forall_exists_lt_norm_lt hdense)

/-- **Equality for dense positive norms**, closure form. When `A` is complete, has a multiplicative
norm and norm-preserving scalar multiplication, and the nonzero norms of `A` are dense in `(0, ∞)`,
`f.convergencePointRadius A = f.radius`. -/
theorem convergencePointRadius_eq_radius_of_Ioi_subset_closure [Module R A] [NormSMulClass R A]
    [NormMulClass A] [CompleteSpace A]
    (hdense : Set.Ioi (0 : ℝ) ⊆ closure (Set.range (norm : A → ℝ) \ {0})) :
    f.convergencePointRadius A = f.radius := by
  refine convergencePointRadius_eq_radius_of_forall_exists_lt_norm_lt fun r₁ r₂ hr₀ hr ↦ ?_
  have hm : (r₁ + r₂) / 2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  obtain ⟨_, ⟨⟨x, rfl⟩, -⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (hdense hm) ((r₂ - r₁) / 2) (by linarith)
  rw [Real.dist_eq, abs_sub_lt_iff] at hdist
  exact ⟨x, by linarith, by linarith⟩

/-- **Equality over a complete densely normed field.** In any complete densely normed field `L`
on which `R` acts linearly with norm-preserving scalar multiplication (for instance `ℂ` or
`ℂ_[p]`), the convergence-point radius equals `f.radius`. -/
@[simp]
theorem convergencePointRadius_eq_radius (L : Type*) [DenselyNormedField L] [Module R L]
    [NormSMulClass R L] [CompleteSpace L] (f : R⟦X⟧) :
    f.convergencePointRadius L = f.radius :=
  convergencePointRadius_eq_radius_of_forall_exists_lt_norm_lt fun _ _ hr₀ hr ↦
    DenselyNormedField.lt_norm_lt _ _ hr₀ hr

/-- **Gap bound on the convergence-point radius.** If no element of `A` has extended norm in the
open interval `(r₁, r₂)` and `f.radius < r₂`, every convergence point of `f` in `A` has extended
norm at most `r₁`, so `f.convergencePointRadius A ≤ r₁`. -/
theorem convergencePointRadius_le_of_radius_lt [SMulZeroClass R A] [NormSMulClass R A]
    [NormMulClass A] {r₁ r₂ : ℝ≥0∞} (hgap : ∀ x : A, r₁ < ‖x‖ₑ → r₂ ≤ ‖x‖ₑ)
    (hr : f.radius < r₂) :
    f.convergencePointRadius A ≤ r₁ :=
  iSup₂_le fun x hx ↦ le_of_not_gt fun hrx ↦
    ((hgap x hrx).trans (le_radius_of_summable_smul_pow hx)).not_gt hr

/-- **Strict inequality across a norm gap.** If no element of `A` has extended norm in `(r₁, r₂)`
and `r₁ < f.radius < r₂`, then `f.convergencePointRadius A < f.radius`. -/
theorem convergencePointRadius_lt_radius_of_lt_radius_of_radius_lt [SMulZeroClass R A]
    [NormSMulClass R A] [NormMulClass A] {r₁ r₂ : ℝ≥0∞}
    (hgap : ∀ x : A, r₁ < ‖x‖ₑ → r₂ ≤ ‖x‖ₑ) (hr₁ : r₁ < f.radius) (hr₂ : f.radius < r₂) :
    f.convergencePointRadius A < f.radius :=
  (convergencePointRadius_le_of_radius_lt hgap hr₂).trans_lt hr₁

end Comparison

section DiscreteValueGroup

variable {R A : Type*} [NormedRing R] [SeminormedRing A] {f : R⟦X⟧} {b : ℝ}

/-- **Discrete norm rounding.** If every nonzero norm in `A` is an integer power of `b > 1` and
`f.radius = ENNReal.ofReal (b ^ t)`, then
`f.convergencePointRadius A ≤ ENNReal.ofReal (b ^ ⌊t⌋)`. -/
theorem convergencePointRadius_le_ofReal_zpow_floor [SMulZeroClass R A] [NormSMulClass R A]
    [NormMulClass A] (hb : 1 < b)
    (hdisc : Set.range (norm : A → ℝ) \ {0} ⊆ Set.range fun m : ℤ ↦ b ^ m) {t : ℝ}
    (hr : f.radius = ENNReal.ofReal (b ^ t)) :
    f.convergencePointRadius A ≤ ENNReal.ofReal (b ^ ⌊t⌋) := by
  refine convergencePointRadius_le_of_radius_lt
    (fun _ hx ↦ TauCeti.ofReal_zpow_add_one_le_eNorm_of_lt hb hdisc hx) ?_
  rw [hr, ← Real.rpow_intCast b (⌊t⌋ + 1)]
  refine (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (zero_lt_one.trans hb) _)).mpr ?_
  exact (Real.rpow_lt_rpow_left_iff hb).mpr (mod_cast Int.lt_floor_add_one t)

/-- **Exact convergence-point radius at non-integral exponents.** Suppose `A` is complete, every
nonzero norm in `A` is an integer power of `b > 1`, and `f.radius` is `ENNReal.ofReal (b ^ t)` for
a non-integer real `t`. If `b ^ ⌊t⌋` is attained by a norm in `A`, then
`f.convergencePointRadius A = ENNReal.ofReal (b ^ ⌊t⌋)`. -/
theorem convergencePointRadius_eq_ofReal_zpow_floor [Module R A] [NormSMulClass R A]
    [NormMulClass A] [CompleteSpace A] (hb : 1 < b)
    (hdisc : Set.range (norm : A → ℝ) \ {0} ⊆ Set.range fun m : ℤ ↦ b ^ m) {t : ℝ}
    (ht : ∀ m : ℤ, (m : ℝ) ≠ t) (hatt : b ^ ⌊t⌋ ∈ Set.range (norm : A → ℝ))
    (hr : f.radius = ENNReal.ofReal (b ^ t)) :
    f.convergencePointRadius A = ENNReal.ofReal (b ^ ⌊t⌋) := by
  refine le_antisymm (convergencePointRadius_le_ofReal_zpow_floor hb hdisc hr) ?_
  obtain ⟨x, hx⟩ := hatt
  have hxe : ‖x‖ₑ = ENNReal.ofReal (b ^ ⌊t⌋) := by rw [← ofReal_norm, hx]
  have hlt : ‖x‖ₑ < f.radius := by
    rw [hxe, hr, ← Real.rpow_intCast b ⌊t⌋]
    refine (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (zero_lt_one.trans hb) t)).mpr ?_
    exact (Real.rpow_lt_rpow_left_iff hb).mpr ((Int.floor_le t).lt_of_ne (ht ⌊t⌋))
  exact hxe ▸ le_convergencePointRadius_of_summable (summable_smul_pow_of_lt_radius hlt)

/-- If every nonzero norm in `A` is an integer power of `b > 1` and `f.radius` is
`ENNReal.ofReal (b ^ t)` for a non-integer real `t`, the convergence-point radius in `A` is
strictly smaller than `f.radius`. -/
theorem convergencePointRadius_lt_radius_of_forall_intCast_ne [SMulZeroClass R A]
    [NormSMulClass R A] [NormMulClass A] (hb : 1 < b)
    (hdisc : Set.range (norm : A → ℝ) \ {0} ⊆ Set.range fun m : ℤ ↦ b ^ m) {t : ℝ}
    (ht : ∀ m : ℤ, (m : ℝ) ≠ t) (hr : f.radius = ENNReal.ofReal (b ^ t)) :
    f.convergencePointRadius A < f.radius := by
  refine (convergencePointRadius_le_ofReal_zpow_floor hb hdisc hr).trans_lt ?_
  rw [hr, ← Real.rpow_intCast b ⌊t⌋]
  refine (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (zero_lt_one.trans hb) t)).mpr ?_
  exact (Real.rpow_lt_rpow_left_iff hb).mpr ((Int.floor_le t).lt_of_ne (ht ⌊t⌋))

end DiscreteValueGroup

section UltrametricConvergencePointRadius

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [Module R A]
  [NormSMulClass R A] [NormMulClass A] [IsUltrametricDist A] [CompleteSpace A]
  {f g : R⟦X⟧}

/-- In a complete ultrametric target, `f.convergencePointRadius A` is the supremum of `‖x‖ₑ` over
the points `x : A` at which `f` is restricted at `‖x‖`. -/
theorem convergencePointRadius_eq_iSup_isRestricted :
    f.convergencePointRadius A = ⨆ (x : A) (_ : f.IsRestricted ‖x‖), ‖x‖ₑ := by
  simp only [convergencePointRadius, summable_smul_pow_iff_isRestricted]

/-- Any operation preserving restrictedness at every radius satisfies the ultrametric min bound on
convergence-point radii. -/
private theorem min_convergencePointRadius_le_of_forall_isRestricted {f g h : R⟦X⟧}
    (H : ∀ r : ℝ, f.IsRestricted r → g.IsRestricted r → h.IsRestricted r) :
    min (f.convergencePointRadius A) (g.convergencePointRadius A) ≤
      h.convergencePointRadius A := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  obtain ⟨hrf, hrg⟩ := lt_min_iff.mp hr
  obtain ⟨x, hsf, hrx⟩ := lt_convergencePointRadius_iff.mp hrf
  obtain ⟨y, hsg, hry⟩ := lt_convergencePointRadius_iff.mp hrg
  have hrf' := isRestricted_of_summable_smul_pow hsf
  have hrg' := isRestricted_of_summable_smul_pow hsg
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · have hg_x :=
      TauCeti.PowerSeries.isRestricted_of_abs_le (c := ‖x‖) hrg' (by simpa [abs_norm] using hxy)
    exact hrx.le.trans
      (le_convergencePointRadius_of_summable ((H ‖x‖ hrf' hg_x).summable_smul_pow le_rfl))
  · have hf_y :=
      TauCeti.PowerSeries.isRestricted_of_abs_le (c := ‖y‖) hrf' (by simpa [abs_norm] using hyx)
    exact hry.le.trans
      (le_convergencePointRadius_of_summable ((H ‖y‖ hf_y hrg').summable_smul_pow le_rfl))

/-- In a complete ultrametric target, the convergence-point radius of a sum is at least the minimum
of the two convergence-point radii. -/
theorem min_convergencePointRadius_le_convergencePointRadius_add (f g : R⟦X⟧) :
    min (f.convergencePointRadius A) (g.convergencePointRadius A) ≤
      (f + g).convergencePointRadius A :=
  min_convergencePointRadius_le_of_forall_isRestricted fun _ hf hg ↦ hf.add hg

/-- In a complete ultrametric target with a multiplicative norm and norm-preserving scalar
multiplication, the convergence-point radius of a product is at least the minimum of the two
convergence-point radii. -/
theorem min_convergencePointRadius_le_convergencePointRadius_mul (f g : R⟦X⟧) :
    min (f.convergencePointRadius A) (g.convergencePointRadius A) ≤
      (f * g).convergencePointRadius A := by
  by_cases hex : ∃ x : A, 0 < ‖x‖
  · obtain ⟨x, hx0⟩ := hex
    -- A point `x : A` of positive norm transfers the ultrametric norm bound from `A` to `R`.
    have : IsUltrametricDist R :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b ↦ by
        refine le_of_mul_le_mul_right ?_ hx0
        rw [← norm_smul, add_smul, max_mul_of_nonneg _ _ hx0.le, ← norm_smul, ← norm_smul]
        exact IsUltrametricDist.norm_add_le_max (a • x) (b • x)
    exact min_convergencePointRadius_le_of_forall_isRestricted fun _ hf hg ↦ hf.mul hg
  · push Not at hex
    have h0 : f.convergencePointRadius A ≤ 0 :=
      iSup₂_le fun x _ ↦ by
        rw [← ofReal_norm, le_antisymm (hex x) (norm_nonneg x), ENNReal.ofReal_zero]
    exact (min_le_of_left_le h0).trans zero_le

end UltrametricConvergencePointRadius

end ConvergencePointRadius

end PowerSeries
