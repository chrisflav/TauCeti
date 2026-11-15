/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Cutoff
public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.NumberTheory.NewtonPolygon.Weierstrass
public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.RingTheory.Valuation.NormNormalization

/-!
# Zeros of entire series on spheres and discs from slope multiplicities

Let `K` be a complete ultrametric normed field whose norm comes from a real additive valuation
`v` with base `b > 1`, so `‖x‖ = b ^ (-v x)` for `x ≠ 0`. The *multiplicity* of a zero `x` of a
power series `f` is the order at zero of its Taylor translate `taylor x f = f(x + T)`
(`PowerSeries.taylor`); for an entire series it is the order of the good zero of `f` at `x`
(`PowerSeries.isGoodZero_iff_order_taylor_eq`), and it is `0` exactly when `f(x) ≠ 0`
(`PowerSeries.order_taylor_ne_zero_iff`).

When `K` is algebraically closed, the zeros of a nonzero entire series `f` on the sphere
`‖x‖ = b ^ σ`, counted with multiplicity, number exactly the multiplicity of the slope `σ` in the
Newton polygon of `f`:

`newtonSlopeMultiplicity f v σ = ∑ᶠ x ∈ sphere 0 (b ^ σ), order (taylor x f)`
(`PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_finsum_order_taylor`).

Summing over the finitely many slopes up to a real cutoff `c`, the length of the cutoff slope list
`f.newtonSlopesLe v c` counts the nonzero zeros of `f` of norm at most `b ^ c` with multiplicity
(`PowerSeries.IsEntire.length_newtonSlopesLe_eq_finsum_order_taylor`), and `f.newtonSlopesLt v c`
counts those of norm strictly below `b ^ c`
(`PowerSeries.IsEntire.length_newtonSlopesLt_eq_finsum_order_taylor`); when `constantCoeff f ≠ 0`,
zero is not a root and these sums range over the closed and open discs `closedBall 0 (b ^ c)` and
`ball 0 (b ^ c)`.

A slope of positive multiplicity is the negated valuation of an actual zero
(`PowerSeries.IsEntire.exists_norm_eq_and_evalAt_eq_zero`). This zero is read off a Weierstrass
preparation at the radius `b ^ σ`: the prepared polynomial carries the finite unit edges of slope
`σ`, so it has a root of norm `b ^ σ`. The count then follows by splitting off the factor
`(X - x) ^ h` at such a zero, which has slope `σ` with multiplicity `h`
(`PowerSeries.newtonSlopeMultiplicity_X_sub_C_pow`), since slope multiplicities
of entire series add under products (`PowerSeries.IsEntire.newtonSlopeMultiplicity_mul`) and so do
orders of zeros. Algebraic closedness is needed for the existence of zeros: over `ℚ_p` the
polynomial `1 - X ^ 2 / p` has slope `-1 / 2` with multiplicity two but no zero.

These counts apply to Fredholm series `det (1 - T u)` of compact operators, whose zeros are the
inverses of the nonzero eigenvalues.

## Main results

* `PowerSeries.IsEntire.exists_norm_eq_and_evalAt_eq_zero`: a slope of positive multiplicity comes
  from a zero on the corresponding sphere.
* `PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_finsum_order_taylor`: the multiplicity of a
  slope counts the zeros on the corresponding sphere with multiplicity.
* `PowerSeries.IsEntire.length_newtonSlopesLe_eq_finsum_order_taylor`,
  `PowerSeries.IsEntire.length_newtonSlopesLt_eq_finsum_order_taylor`: cutoff slope list lengths
  count nonzero zeros in punctured closed and open discs with multiplicity.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 3.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open TauCeti

namespace PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K⟦X⟧}

include hb hv

omit [IsUltrametricDist K] in
/-- Every zero of a nonzero entire series on the sphere `‖x‖ = b ^ σ` contributes positively to the
slope multiplicity at `σ`. Algebraic closedness is not needed. -/
theorem IsEntire.newtonSlopeMultiplicity_ne_zero_of_evalAt_eq_zero (hf : f.IsEntire) (hf0 : f ≠ 0)
    {x : K} {σ : ℝ} (hx : ‖x‖ = b ^ σ) (hfx : f.evalAt x = 0) :
    f.newtonSlopeMultiplicity v σ ≠ 0 := by
  obtain ⟨h, hh, hfxh⟩ := hf.exists_pos_isGoodZero_of_evalAt_eq_zero hf0 hfx
  obtain ⟨g, hg, rfl, -⟩ := hf.isGoodZero_iff.mp hfxh
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hf0
  rw [((isEntire_X.sub (isEntire_C x)).pow h).newtonSlopeMultiplicity_mul v hb hv hg
    (left_ne_zero_of_mul hf0) hg0,
    newtonSlopeMultiplicity_X_sub_C_pow v (fun _ ↦ v.top_iff.mp)
      ((v.norm_eq_rpow_iff hb hv).mp hx)]
  omega

/-- **Zeros at every slope.** Over a complete algebraically closed ultrametric field, if the slope
`σ` has positive multiplicity in the Newton polygon of an entire series `f`, then `f` has a zero
on the sphere `‖x‖ = b ^ σ`. -/
theorem IsEntire.exists_norm_eq_and_evalAt_eq_zero [IsAlgClosed K] (hf : f.IsEntire) {σ : ℝ}
    (hσ : f.newtonSlopeMultiplicity v σ ≠ 0) : ∃ x : K, ‖x‖ = b ^ σ ∧ f.evalAt x = 0 := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hσ (newtonSlopeMultiplicity_zero v σ)
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  obtain ⟨l, j, hface⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hf0 σ
  have hlj : l < j := by
    rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface] at hσ
    omega
  -- Prepare `f = e * ω` at the radius `b ^ σ`, at the right end `j` of the face of slope `σ`.
  have hfd := isDistinguished_of_isFiniteFace v hb hv (hf.isRestricted _) hface
  obtain ⟨e, ω, he, hω, heω⟩ :=
    hfd.exists_isUnit_isMonicOfDegree_mul_eq hfd.coeff_ne_zero.isUnit hc (hf.isRestricted _)
  -- The unit edge of `f` at `l` has slope `σ`, and `ω` has the same edge.
  have hl : l ∈ finiteEdges (f.newtonPolygon v) := by
    have hmem : l ∈ Set.Ico l j := ⟨le_rfl, hlj⟩
    rw [← hface.setOf_unitSlope_eq (f.isConvexSeq_newtonPolygon v)] at hmem
    exact hmem.1
  have hlω := (mem_finiteEdges_newtonPolygon_iff_of_isUnit_mul v hb hv hfd he
    hω.natDegree_eq.le heω l).mpr ⟨hl, hlj⟩
  have hslope : unitSlope (ω.newtonPolygon v) l = σ :=
    (unitSlope_newtonPolygon_eq_of_isUnit_mul v hb hv hfd he hω.natDegree_eq.le heω hl
      hlj).trans (hface.unitSlope_eq le_rfl hlj)
  have hmem : σ ∈ ω.newtonSlopes v := (Polynomial.mem_newtonSlopes ω v).mpr ⟨l, hlω, hslope⟩
  -- Over an algebraically closed field the slope `σ` of `ω` comes from a root of norm `b ^ σ`.
  rw [Polynomial.newtonSlopes_eq_map_roots (fun _ ↦ v.top_iff.mp) (IsAlgClosed.splits ω)]
    at hmem
  obtain ⟨x, hx, hxσ⟩ := Multiset.mem_map.mp hmem
  obtain ⟨hxroot, hx0⟩ := Multiset.mem_filter.mp hx
  have hxnorm : ‖x‖ = b ^ σ := by rw [hv x hx0, hxσ]
  refine ⟨x, hxnorm, ?_⟩
  rw [← heω, IsRestricted.evalAt_mul e.2 (TauCeti.PowerSeries.isRestricted_polynomial _)
    hxnorm.le, evalAt_coe, Polynomial.coe_aeval_eq_eval,
    ((Polynomial.mem_roots hω.monic.ne_zero).mp hxroot).eq_zero, mul_zero]

/-- The zeros of a nonzero entire series on a sphere, with their orders, add up to the
multiplicity of the corresponding slope. This is the joint finiteness and counting statement,
proved by splitting off one zero at a time. -/
private theorem exists_finset_newtonSlopeMultiplicity_eq_sum [IsAlgClosed K]
    (σ : ℝ) : ∀ (n : ℕ) (f : K⟦X⟧), f.IsEntire → f ≠ 0 → f.newtonSlopeMultiplicity v σ = n →
      ∃ s : Finset K, (∀ x, x ∈ s ↔ ‖x‖ = b ^ σ ∧ f.evalAt x = 0) ∧
        (n : ℕ∞) = ∑ x ∈ s, (PowerSeries.taylor x f).order := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hf0 hn
  -- A zero `x` of order `h` on the sphere splits off a factor of slope `σ` and multiplicity `h`.
  have split {x : K} (hx : ‖x‖ = b ^ σ) (hfx : f.evalAt x = 0) :
      ∃ h g, 0 < h ∧ f.IsGoodZero x h ∧ g.IsEntire ∧ g ≠ 0 ∧ g.evalAt x ≠ 0 ∧
        f = (X - C x) ^ h * g ∧ n = h + g.newtonSlopeMultiplicity v σ := by
    obtain ⟨h, hh, hfxh⟩ := hf.exists_pos_isGoodZero_of_evalAt_eq_zero hf0 hfx
    obtain ⟨g, hg, rfl, hgx⟩ := hf.isGoodZero_iff.mp hfxh
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hf0 (mul_zero _)
    refine ⟨h, g, hh, hfxh, hg, hg0, hgx.ne_zero, rfl, ?_⟩
    rw [← hn, ((isEntire_X.sub (isEntire_C x)).pow h).newtonSlopeMultiplicity_mul v hb hv hg
      (left_ne_zero_of_mul hf0) hg0,
      newtonSlopeMultiplicity_X_sub_C_pow v (fun _ ↦ v.top_iff.mp)
        ((v.norm_eq_rpow_iff hb hv).mp hx)]
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · -- With no slope `σ`, there is no zero on the sphere.
    refine ⟨∅, fun x ↦ ⟨fun hx ↦ absurd hx (Finset.notMem_empty x), fun ⟨hx, hfx⟩ ↦ ?_⟩, by simp⟩
    obtain ⟨h, g, hh, -, -, -, -, -, hhg⟩ := split hx hfx
    omega
  obtain ⟨x, hx, hfx⟩ := hf.exists_norm_eq_and_evalAt_eq_zero v hb hv (hn ▸ hnpos.ne')
  obtain ⟨h, g, hh, hfxh, hg, hg0, hgx, rfl, hhg⟩ := split hx hfx
  obtain ⟨s, hs, hsum⟩ := ih (g.newtonSlopeMultiplicity v σ) (by omega) g hg hg0 rfl
  have hlin : (X - C x : K⟦X⟧).IsEntire := isEntire_X.sub (isEntire_C x)
  have hfac : ((X - C x) ^ h : K⟦X⟧).IsEntire := hlin.pow h
  have hxs : x ∉ s := fun hxs ↦ hgx ((hs x).mp hxs).2
  -- Away from `x` the factor `(X - x) ^ h` is a unit, so `f` and `g` have the same zeros there.
  have hord {y : K} (hy : y ≠ x) :
      (PowerSeries.taylor y ((X - C x) ^ h * g)).order = (PowerSeries.taylor y g).order := by
    obtain ⟨k, hk⟩ := hg.exists_isGoodZero hg0 y
    have hunit : IsUnit (((X - C x) ^ h : K⟦X⟧).evalAt y) := by
      rw [hlin.evalAt_pow, evalAt_X_sub_C]
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hy)).pow h
    rw [isGoodZero_iff_order_taylor_eq.mp hk, mul_comm,
      isGoodZero_iff_order_taylor_eq.mp ((hg.isGoodZero_mul_iff_of_isUnit hfac hunit).mpr hk)]
  refine ⟨insert x s, fun y ↦ ?_, ?_⟩
  · rw [Finset.mem_insert, hs y, hfac.evalAt_mul hg, hlin.evalAt_pow, evalAt_X_sub_C, mul_eq_zero,
      pow_eq_zero_iff hh.ne', sub_eq_zero, Algebra.algebraMap_self_apply]
    constructor
    · rintro (rfl | ⟨hy, hgy⟩)
      exacts [⟨hx, .inl rfl⟩, ⟨hy, .inr hgy⟩]
    · rintro ⟨hy, rfl | hgy⟩
      exacts [.inl rfl, .inr ⟨hy, hgy⟩]
  · rw [Finset.sum_insert hxs, isGoodZero_iff_order_taylor_eq.mp hfxh,
      Finset.sum_congr rfl fun y hy ↦ hord (ne_of_mem_of_not_mem hy hxs), ← hsum, hhg]
    exact Nat.cast_add _ _

/-- **Slope multiplicities count zeros.** Over a complete algebraically closed ultrametric
field, the multiplicity of the slope `σ` in the Newton polygon of a nonzero entire series `f` is
the number of zeros of `f` on the sphere `‖x‖ = b ^ σ`, each counted with its multiplicity, the
order of the Taylor translate `taylor x f`. -/
theorem IsEntire.newtonSlopeMultiplicity_eq_finsum_order_taylor [IsAlgClosed K]
    (hf : f.IsEntire) (hf0 : f ≠ 0) (σ : ℝ) :
    (f.newtonSlopeMultiplicity v σ : ℕ∞) =
      ∑ᶠ x ∈ Metric.sphere (0 : K) (b ^ σ), (PowerSeries.taylor x f).order := by
  obtain ⟨s, hs, hsum⟩ := exists_finset_newtonSlopeMultiplicity_eq_sum v hb hv σ _ f hf hf0 rfl
  rw [hsum, finsum_mem_eq_sum_of_inter_support_eq]
  ext x
  simp only [Set.mem_inter_iff, mem_sphere_iff_norm, sub_zero, Function.mem_support,
    Finset.mem_coe, hs x, order_taylor_ne_zero_iff, and_self_right]

/-- Fiberwise summation of zero multiplicities over spheres inside a punctured disc. -/
private theorem finsum_punctured_order_taylor_eq [IsAlgClosed K]
    (hf : f.IsEntire) (hf0 : f ≠ 0) {c : ℝ} {p q : ℝ → Prop}
    (hp : ∀ σ, p σ → σ ≤ c)
    (hpq : ∀ x : K, x ≠ 0 → (p (-(v x).untop₀) ↔ q ‖x‖)) :
    ((∑ᶠ σ ∈ {σ | p σ}, f.newtonSlopeMultiplicity v σ : ℕ) : ℕ∞) =
      ∑ᶠ x ∈ {x : K | x ≠ 0 ∧ q ‖x‖}, (PowerSeries.taylor x f).order := by
  classical
  have hb0 : 0 < b := zero_lt_one.trans hb
  set t : Finset ℝ := (f.newtonSlopesLe v c).toFinset.filter p
  have hsph (σ : ℝ) := exists_finset_newtonSlopeMultiplicity_eq_sum v hb hv σ _ f hf hf0 rfl
  let s : ℝ → Finset K := fun σ ↦ (hsph σ).choose
  have hs_mem (σ : ℝ) (x : K) : x ∈ s σ ↔ ‖x‖ = b ^ σ ∧ f.evalAt x = 0 := (hsph σ).choose_spec.1 x
  have hs_sum (σ : ℝ) :
      (f.newtonSlopeMultiplicity v σ : ℕ∞) = ∑ x ∈ s σ, (PowerSeries.taylor x f).order :=
    (hsph σ).choose_spec.2
  have hmult : ∑ᶠ σ ∈ {σ | p σ}, f.newtonSlopeMultiplicity v σ =
      ∑ σ ∈ t, f.newtonSlopeMultiplicity v σ := by
    rw [finsum_mem_eq_sum_of_inter_support_eq]
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, ne_eq, Finset.mem_coe,
      t, Finset.mem_filter, List.mem_toFinset, hf.mem_newtonSlopesLe_iff v hb hv]
    exact ⟨fun ⟨hpσ, hne⟩ ↦ ⟨⟨⟨hp σ hpσ, hne⟩, hpσ⟩, hne⟩, fun ⟨⟨_, hpσ⟩, hne⟩ ↦ ⟨hpσ, hne⟩⟩
  have hdisj : (t : Set ℝ).PairwiseDisjoint s := fun σ₁ _ σ₂ _ hne ↦
    Finset.disjoint_left.mpr fun x hx₁ hx₂ ↦ hne ((Real.rpow_right_inj hb0 hb.ne').mp
      (((hs_mem σ₁ x).mp hx₁).1.symm.trans ((hs_mem σ₂ x).mp hx₂).1))
  rw [hmult, Nat.cast_sum, Finset.sum_congr rfl fun σ _ ↦ hs_sum σ, ← Finset.sum_biUnion hdisj,
    eq_comm, finsum_mem_eq_sum_of_inter_support_eq]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, order_taylor_ne_zero_iff,
    Finset.mem_coe, Finset.mem_biUnion, t, Finset.mem_filter, List.mem_toFinset,
    hf.mem_newtonSlopesLe_iff v hb hv]
  constructor
  · rintro ⟨⟨hx0, hxq⟩, hfx⟩
    have hxs : x ∈ s (-(v x).untop₀) := (hs_mem _ x).mpr ⟨hv x hx0, hfx⟩
    have hord : (PowerSeries.taylor x f).order ≠ 0 := order_taylor_ne_zero_iff.mpr hfx
    have hne : f.newtonSlopeMultiplicity v (-(v x).untop₀) ≠ 0 := by
      rw [← Nat.cast_ne_zero (R := ℕ∞), hs_sum]
      exact fun hsum0 ↦ hord (Finset.sum_eq_zero_iff.mp hsum0 x hxs)
    have hpσ : p (-(v x).untop₀) := (hpq x hx0).mpr hxq
    exact ⟨⟨-(v x).untop₀, ⟨⟨hp _ hpσ, hne⟩, hpσ⟩, hxs⟩, hfx⟩
  · rintro ⟨⟨σ, ⟨_, hpσ⟩, hxs⟩, hfx⟩
    have hxnorm : ‖x‖ = b ^ σ := ((hs_mem σ x).mp hxs).1
    have hx0 : x ≠ 0 := norm_pos_iff.mp (hxnorm ▸ Real.rpow_pos_of_pos hb0 σ)
    have hσeq : -(v x).untop₀ = σ :=
      (Real.rpow_right_inj hb0 hb.ne').mp ((hv x hx0).symm.trans hxnorm)
    exact ⟨⟨hx0, (hpq x hx0).mp (hσeq ▸ hpσ)⟩, hfx⟩

/-- **Cutoff slope counts count nonzero zeros in closed discs.** Over a complete algebraically
closed ultrametric field, the length of `f.newtonSlopesLe v c` for a nonzero entire series `f` is
the number of nonzero zeros of `f` of norm at most `b ^ c`, counted with multiplicity. -/
theorem IsEntire.length_newtonSlopesLe_eq_finsum_order_taylor [IsAlgClosed K]
    (hf : f.IsEntire) (hf0 : f ≠ 0) (c : ℝ) :
    ((f.newtonSlopesLe v c).length : ℕ∞) =
      ∑ᶠ x ∈ {x : K | x ≠ 0 ∧ ‖x‖ ≤ b ^ c}, (PowerSeries.taylor x f).order := by
  rw [hf.length_newtonSlopesLe_eq_finsum_newtonSlopeMultiplicity v hb hv c]
  exact finsum_punctured_order_taylor_eq (p := (· ≤ c)) (q := (· ≤ b ^ c))
    v hb hv hf hf0 (fun _ h ↦ h) fun x hx0 ↦ by rw [hv x hx0, Real.rpow_le_rpow_left_iff hb]

/-- **Strict cutoff slope counts count nonzero zeros in open discs.** Over a complete algebraically
closed ultrametric field, the length of `f.newtonSlopesLt v c` for a nonzero entire series `f` is
the number of nonzero zeros of `f` of norm strictly below `b ^ c`, counted with multiplicity. -/
theorem IsEntire.length_newtonSlopesLt_eq_finsum_order_taylor [IsAlgClosed K]
    (hf : f.IsEntire) (hf0 : f ≠ 0) (c : ℝ) :
    ((f.newtonSlopesLt v c).length : ℕ∞) =
      ∑ᶠ x ∈ {x : K | x ≠ 0 ∧ ‖x‖ < b ^ c}, (PowerSeries.taylor x f).order := by
  rw [hf.length_newtonSlopesLt_eq_finsum_newtonSlopeMultiplicity v hb hv c]
  exact finsum_punctured_order_taylor_eq (p := (· < c)) (q := (· < b ^ c))
    v hb hv hf hf0 (fun _ h ↦ h.le) fun x hx0 ↦ by rw [hv x hx0, Real.rpow_lt_rpow_left_iff hb]

/-- When `constantCoeff f ≠ 0`, `0` is not a zero of `f`, so the length of `f.newtonSlopesLe v c`
counts all zeros of `f` in `Metric.closedBall 0 (b ^ c)` with multiplicity. -/
theorem IsEntire.length_newtonSlopesLe_eq_finsum_closedBall_order_taylor [IsAlgClosed K]
    (hf : f.IsEntire) (h0 : constantCoeff f ≠ 0) (c : ℝ) :
    ((f.newtonSlopesLe v c).length : ℕ∞) =
      ∑ᶠ x ∈ Metric.closedBall (0 : K) (b ^ c), (PowerSeries.taylor x f).order := by
  have hf0 : f ≠ 0 := fun h ↦ h0 (by simp [h])
  have hz0 : f.order = 0 :=
    by simpa using (PowerSeries.order_eq_nat (n := 0)).mpr ⟨by simpa using h0, by simp⟩
  rw [hf.length_newtonSlopesLe_eq_finsum_order_taylor v hb hv hf0 c]
  refine finsum_congr fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [hz0]
  · simp [hx0]

/-- When `constantCoeff f ≠ 0`, `0` is not a zero of `f`, so the length of `f.newtonSlopesLt v c`
counts all zeros of `f` in `Metric.ball 0 (b ^ c)` with multiplicity. -/
theorem IsEntire.length_newtonSlopesLt_eq_finsum_ball_order_taylor [IsAlgClosed K]
    (hf : f.IsEntire) (h0 : constantCoeff f ≠ 0) (c : ℝ) :
    ((f.newtonSlopesLt v c).length : ℕ∞) =
      ∑ᶠ x ∈ Metric.ball (0 : K) (b ^ c), (PowerSeries.taylor x f).order := by
  have hf0 : f ≠ 0 := fun h ↦ h0 (by simp [h])
  have hz0 : f.order = 0 :=
    by simpa using (PowerSeries.order_eq_nat (n := 0)).mpr ⟨by simpa using h0, by simp⟩
  rw [hf.length_newtonSlopesLt_eq_finsum_order_taylor v hb hv hf0 c]
  refine finsum_congr fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [hz0]
  · simp [hx0]

end PowerSeries
