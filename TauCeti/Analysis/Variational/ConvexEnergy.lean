/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.LocallyConvex.WeakSpace
public import TauCeti.Analysis.Variational.DirectMethod
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.Convex.Function.Basic
import TauCeti.Analysis.Convex.StrictConvexSpace
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.WeakSpace

/-!
# Convex energies: weak lower semicontinuity, bounded sublevels, and minimization

This file supplies the normed-space convex-energy API for the direct method of the calculus of
variations over `ℝ` or `ℂ`:

* **Weak lower semicontinuity of standard convex energies**: norm powers `‖·‖ ^ p` (`1 ≤ p`),
  natural norm powers `‖·‖ ^ n`, norms `‖·‖`, operator energies `‖D ·‖ ^ p`, `‖D ·‖ ^ n` (in
  particular the quadratic energy `‖D ·‖ ^ 2`), and shifted norm powers `‖· - x₀‖ ^ p`.
  Finite sums of convex energies and weakly continuous linear or real-linear functionals live at
  full locally convex generality in `TauCeti.Analysis.LocallyConvex.WeakSpace`.
* **Bounded sublevels of norm-power energies**: norm powers `‖·‖ ^ p` (`0 < p`), nonzero natural
  powers `‖·‖ ^ n`, shifted norm powers `‖· - x₀‖ ^ p`, and superlinearly coerced perturbations
  `c * ‖·‖ ^ p + g ·` (`0 < c`, `1 < p`) for any linearly lower-bounded `g` (in particular any
  continuous real-linear functional or `RCLike.re (ℓ ·)`). These live here rather than in
  `BoundedSublevels` to keep the bornological layer free of real-power dependencies.
* **Direct-method minimization for quasiconvex and strictly convex energies**: on a nonempty
  norm-closed real-convex set in a reflexive space, a norm-lower-semicontinuous quasiconvex
  energy with bounded sublevels attains its minimum and has a weakly compact (and convex)
  minimizer set (`TauCeti.exists_isMinOn_of_quasiconvexOn_of_isClosed`,
  `TauCeti.isCompact_toWeakSpace_minimizers_of_quasiconvexOn_of_isClosed`); strict convexity
  gives uniqueness (`TauCeti.existsUnique_isMinOn_of_strictConvexOn_of_isClosed`). In any
  reflexive strictly convex space—and in particular every uniformly convex Banach space or
  Hilbert space via Milman–Pettis—`c * ‖·‖ ^ p + f ·` (`0 < c`, `1 < p`) and distance to a point
  `‖· - x₀‖` have unique minimizers on every nonempty closed real-convex set.
* **Sharpness of convexity**: in any inner-product space admitting an infinite orthonormal family,
  the concave energy `-(‖·‖ ^ p)` (`0 < p`) is not weakly lower semicontinuous at `0` and
  `‖·‖ ^ p` is not weakly continuous at `0`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Corollary 3.9 and §5.1.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
* V. Ivrii, *Partial Differential Equations*, §13.1.
-/

public section

open Bornology Filter NormedSpace RCLike Set Topology

namespace TauCeti

section WeakLSC

variable {𝕜 V W : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- For every exponent `1 ≤ p`, the `p`-th power of the norm is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm {p : ℝ} (hp : 1 ≤ p) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 V ↦ ‖(toWeakSpace 𝕜 V).symm u‖ ^ p := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  have : IsScalarTower ℝ 𝕜 V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact (convexOn_norm_rpow (E := V) hp).quasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm
    (continuous_norm.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hp)).lowerSemicontinuous

/-- Every natural power of the norm is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_norm_pow_comp_toWeakSpace_symm (n : ℕ) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 V ↦ ‖(toWeakSpace 𝕜 V).symm u‖ ^ n := by
  cases n with
  | zero =>
    simpa only [pow_zero] using (lowerSemicontinuous_const (α := WeakSpace 𝕜 V) (z := (1 : ℝ)))
  | succ k =>
    have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    simpa only [Real.rpow_natCast] using
      lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := V) hk

/-- The norm is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_norm_comp_toWeakSpace_symm :
    LowerSemicontinuous fun u : WeakSpace 𝕜 V ↦ ‖(toWeakSpace 𝕜 V).symm u‖ := by
  simpa only [pow_one] using lowerSemicontinuous_norm_pow_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := V) 1

/-- For a bounded linear operator `D : V →L[𝕜] W` and `1 ≤ p`, the energy `u ↦ ‖D u‖ ^ p` is
weakly lower semicontinuous. -/
theorem lowerSemicontinuous_norm_apply_rpow_comp_toWeakSpace_symm (D : V →L[𝕜] W)
    {p : ℝ} (hp : 1 ≤ p) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 V ↦ ‖D ((toWeakSpace 𝕜 V).symm u)‖ ^ p :=
  (lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := W) hp).comp
    (WeakSpace.map D).continuous

/-- For a bounded linear operator `D : V →L[𝕜] W` and `n : ℕ`, the energy `u ↦ ‖D u‖ ^ n`
(in particular the quadratic energy `‖D u‖ ^ 2`) is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_norm_apply_pow_comp_toWeakSpace_symm (D : V →L[𝕜] W) (n : ℕ) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 V ↦ ‖D ((toWeakSpace 𝕜 V).symm u)‖ ^ n :=
  (lowerSemicontinuous_norm_pow_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := W) n).comp
    (WeakSpace.map D).continuous

/-- For a bounded linear operator `D : V →L[𝕜] W`, the seminorm energy `u ↦ ‖D u‖` is weakly
lower semicontinuous. -/
theorem lowerSemicontinuous_norm_apply_comp_toWeakSpace_symm (D : V →L[𝕜] W) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 V ↦ ‖D ((toWeakSpace 𝕜 V).symm u)‖ :=
  (lowerSemicontinuous_norm_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := W)).comp
    (WeakSpace.map D).continuous

/-- For any centre `x₀ : V` and `1 ≤ p`, the shifted norm power `u ↦ ‖u - x₀‖ ^ p` is weakly
lower semicontinuous. -/
theorem lowerSemicontinuous_norm_sub_rpow_comp_toWeakSpace_symm (x₀ : V) {p : ℝ} (hp : 1 ≤ p) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 V ↦ ‖(toWeakSpace 𝕜 V).symm u - x₀‖ ^ p := by
  have hsub : Continuous fun u : WeakSpace 𝕜 V ↦ u - toWeakSpace 𝕜 V x₀ :=
    continuous_id.sub continuous_const
  simpa only [Function.comp_def, map_sub, LinearEquiv.symm_apply_apply] using
    (lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := V) hp).comp hsub

end WeakLSC

section BoundedSublevels

/-- Any positive real power of the norm has bounded sublevels on every admissible set. -/
theorem hasBoundedSublevelsOn_norm_rpow {V : Type*} [SeminormedAddGroup V] {S : Set V}
    {p : ℝ} (hp : 0 < p) :
    HasBoundedSublevelsOn (fun u : V ↦ ‖u‖ ^ p) S := by
  rw [hasBoundedSublevelsOn_iff_forall_exists_le_of_le_norm]
  intro b
  refine ⟨max 0 b ^ p⁻¹, fun u _ hu ↦ ?_⟩
  calc b ≤ max 0 b := le_max_right 0 b
    _ = (max 0 b ^ p⁻¹) ^ p := (Real.rpow_inv_rpow (le_max_left 0 b) hp.ne').symm
    _ ≤ ‖u‖ ^ p := Real.rpow_le_rpow (Real.rpow_nonneg (le_max_left 0 b) _) hu hp.le

/-- Any nonzero natural power of the norm has bounded sublevels on every admissible set. -/
theorem hasBoundedSublevelsOn_norm_pow {V : Type*} [SeminormedAddGroup V] {S : Set V}
    {n : ℕ} (hn : n ≠ 0) :
    HasBoundedSublevelsOn (fun u : V ↦ ‖u‖ ^ n) S := by
  have hpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  simpa only [Real.rpow_natCast] using hasBoundedSublevelsOn_norm_rpow (V := V) (S := S) hpos

/-- Any positive real power of the distance to a fixed point `x₀` has bounded sublevels on every
admissible set. -/
theorem hasBoundedSublevelsOn_norm_sub_rpow {V : Type*} [SeminormedAddGroup V] {S : Set V}
    (x₀ : V) {p : ℝ} (hp : 0 < p) :
    HasBoundedSublevelsOn (fun u : V ↦ ‖u - x₀‖ ^ p) S := by
  rw [hasBoundedSublevelsOn_iff_forall_exists_le_of_le_norm]
  intro b
  refine ⟨‖x₀‖ + max 0 b ^ p⁻¹, fun u _ hu ↦ ?_⟩
  have hsub : max 0 b ^ p⁻¹ ≤ ‖u - x₀‖ := by
    have htri : ‖u‖ ≤ ‖u - x₀‖ + ‖x₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (u - x₀) x₀
    linarith
  calc b ≤ max 0 b := le_max_right 0 b
    _ = (max 0 b ^ p⁻¹) ^ p := (Real.rpow_inv_rpow (le_max_left 0 b) hp.ne').symm
    _ ≤ ‖u - x₀‖ ^ p := Real.rpow_le_rpow (Real.rpow_nonneg (le_max_left 0 b) _) hsub hp.le

/-- Superlinear norm growth (`1 < p`, `0 < c`) dominates any perturbation bounded below by a
linear multiple of the norm, giving bounded sublevels on `S`. -/
theorem hasBoundedSublevelsOn_const_mul_norm_rpow_add_of_le {V : Type*} [SeminormedAddGroup V]
    {S : Set V} {g : V → ℝ} {c p : ℝ} (hc : 0 < c) (hp : 1 < p)
    {C : ℝ} (hg : ∀ u ∈ S, -(C * ‖u‖) ≤ g u) :
    HasBoundedSublevelsOn (fun u : V ↦ c * ‖u‖ ^ p + g u) S := by
  rw [hasBoundedSublevelsOn_iff_forall_exists_le_of_le_norm]
  have hp1 : 0 < p - 1 := sub_pos.2 hp
  intro b
  set C₀ : ℝ := max 0 C
  set M : ℝ := (C₀ + 1) / c
  have hM : 0 ≤ M := div_nonneg (by positivity) hc.le
  refine ⟨max 1 (max b (M ^ (p - 1)⁻¹)), fun u huS hu ↦ ?_⟩
  have h1 : 1 ≤ ‖u‖ := (le_max_left _ _).trans hu
  have hb : b ≤ ‖u‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hu
  have hR : M ^ (p - 1)⁻¹ ≤ ‖u‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans hu
  have hpow : M ≤ ‖u‖ ^ (p - 1) := by
    calc M = (M ^ (p - 1)⁻¹) ^ (p - 1) := (Real.rpow_inv_rpow hM hp1.ne').symm
      _ ≤ ‖u‖ ^ (p - 1) := Real.rpow_le_rpow (Real.rpow_nonneg hM _) hR hp1.le
  have hcm : C₀ + 1 ≤ c * ‖u‖ ^ (p - 1) := by
    rwa [div_le_iff₀ hc, mul_comm] at hpow
  have hsplit : ‖u‖ ^ p = ‖u‖ * ‖u‖ ^ (p - 1) := by
    have hpos : 0 < ‖u‖ := zero_lt_one.trans_le h1
    conv_lhs => rw [← add_sub_cancel 1 p, add_comm 1 (p - 1)]
    rw [Real.rpow_add hpos, Real.rpow_one, mul_comm]
  have hgu : -(C₀ * ‖u‖) ≤ g u :=
    (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_right 0 C) (norm_nonneg u))).trans (hg u huS)
  have hdom : ‖u‖ ≤ c * ‖u‖ ^ p - C₀ * ‖u‖ := by
    rw [hsplit]
    nlinarith [norm_nonneg u]
  linarith

/-- Superlinear norm growth (`1 < p`, `0 < c`) dominates any continuous real-linear functional,
giving bounded sublevels on every admissible set. -/
theorem hasBoundedSublevelsOn_const_mul_norm_rpow_add_linear {V : Type*}
    [SeminormedAddCommGroup V] [NormedSpace ℝ V] {S : Set V} {c p : ℝ} (hc : 0 < c) (hp : 1 < p)
    (f : V →L[ℝ] ℝ) :
    HasBoundedSublevelsOn (fun u : V ↦ c * ‖u‖ ^ p + f u) S :=
  hasBoundedSublevelsOn_const_mul_norm_rpow_add_of_le hc hp fun u _ ↦
    neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using f.le_opNorm u)

/-- Superlinear norm growth (`1 < p`, `0 < c`) dominates the real part of any continuous
`𝕜`-linear functional, giving bounded sublevels on every admissible set. -/
theorem hasBoundedSublevelsOn_const_mul_norm_rpow_add_re_eval {𝕜 V : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] {S : Set V} {c p : ℝ} (hc : 0 < c) (hp : 1 < p)
    (ℓ : StrongDual 𝕜 V) :
    HasBoundedSublevelsOn (fun u : V ↦ c * ‖u‖ ^ p + re (ℓ u)) S :=
  hasBoundedSublevelsOn_const_mul_norm_rpow_add_of_le hc hp fun u _ ↦
    neg_le_of_abs_le ((abs_re_le_norm (ℓ u)).trans (ℓ.le_opNorm u))

end BoundedSublevels

section DirectMethodConvex

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]

/-- **Direct method for quasiconvex (in particular convex) energies.** On a nonempty norm-closed
real-convex set in a reflexive seminormed space, a norm-lower-semicontinuous quasiconvex energy
with bounded sublevels attains its minimum. -/
theorem exists_isMinOn_of_quasiconvexOn_of_isClosed {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hSclosed : IsClosed S) (hE : QuasiconvexOn ℝ S E)
    (hlsc : LowerSemicontinuousOn E S) (hb : HasBoundedSublevelsOn E S) :
    ∃ u ∈ S, IsMinOn E S u := by
  have hSw : IsClosed (toWeakSpace 𝕜 V '' S) := by
    rw [← hSclosed.closure_eq, hE.convex.toWeakSpace_closure 𝕜]
    exact isClosed_closure
  exact exists_isMinOn_of_weak_closed hV hne hSw
    (hE.lowerSemicontinuousOn_comp_toWeakSpace_symm hlsc) hb

/-- **Direct method for strictly convex energies.** On a nonempty norm-closed real-convex set in
a reflexive seminormed space, a norm-lower-semicontinuous strictly convex energy with bounded
sublevels has a unique minimizer. -/
theorem existsUnique_isMinOn_of_strictConvexOn_of_isClosed {β : Type*} [LinearOrder β]
    [AddCommMonoid β] [IsOrderedAddMonoid β] [Module ℝ β] [PosSMulMono ℝ β]
    {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hSclosed : IsClosed S) (hE : StrictConvexOn ℝ S E)
    (hlsc : LowerSemicontinuousOn E S) (hb : HasBoundedSublevelsOn E S) :
    ∃! u, u ∈ S ∧ IsMinOn E S u := by
  obtain ⟨u, hu, hmin⟩ :=
    exists_isMinOn_of_quasiconvexOn_of_isClosed hV hne hSclosed hE.convexOn.quasiconvexOn hlsc hb
  exact ⟨u, ⟨hu, hmin⟩, fun v ⟨hv, hminv⟩ ↦ hE.eq_of_isMinOn hminv hmin hv hu⟩

/-- On a norm-closed real-convex set in a reflexive seminormed space, the set of minimizers of a
norm-lower-semicontinuous quasiconvex energy with bounded sublevels is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_quasiconvexOn_of_isClosed {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hSclosed : IsClosed S) (hE : QuasiconvexOn ℝ S E)
    (hlsc : LowerSemicontinuousOn E S) (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  have hSw : IsClosed (toWeakSpace 𝕜 V '' S) := by
    rw [← hSclosed.closure_eq, hE.convex.toWeakSpace_closure 𝕜]
    exact isClosed_closure
  exact isCompact_toWeakSpace_minimizers hV hSw
    (hE.lowerSemicontinuousOn_comp_toWeakSpace_symm hlsc) hb

end DirectMethodConvex

section StrictAndUniformConvex

/-- In a reflexive strictly convex normed space, every superlinear norm-power energy with a
continuous real-linear perturbation `v ↦ c * ‖v‖ ^ p + f v` (`0 < c`, `1 < p`) has a unique
minimizer on every nonempty closed real-convex set. -/
theorem existsUnique_isMinOn_const_mul_norm_rpow_add_linear {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    [StrictConvexSpace ℝ V] (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {S : Set V} (hne : S.Nonempty) (hSclosed : IsClosed S) (hSconv : Convex ℝ S)
    {c p : ℝ} (hc : 0 < c) (hp : 1 < p) (f : V →L[ℝ] ℝ) :
    ∃! u, u ∈ S ∧ IsMinOn (fun v : V ↦ c * ‖v‖ ^ p + f v) S u := by
  have hstrict : StrictConvexOn ℝ S fun v : V ↦ c * ‖v‖ ^ p + f v := by
    have hpow : StrictConvexOn ℝ S fun v : V ↦ c * ‖v‖ ^ p := by
      simpa only [smul_eq_mul] using
        ((strictConvexOn_norm_rpow (E := V) hp).subset (subset_univ S) hSconv).smul hc
    exact hpow.add_convexOn (f.toLinearMap.convexOn hSconv)
  have hcont : Continuous fun v : V ↦ c * ‖v‖ ^ p + f v :=
    (continuous_const.mul
      (continuous_norm.rpow_const fun _ ↦ Or.inr (zero_lt_one.trans hp).le)).add f.continuous
  exact existsUnique_isMinOn_of_strictConvexOn_of_isClosed hV hne hSclosed hstrict
    (hcont.lowerSemicontinuous.lowerSemicontinuousOn S)
    (hasBoundedSublevelsOn_const_mul_norm_rpow_add_linear hc hp f)

/-- **Best approximation in reflexive strictly convex spaces.** Every point `x₀` in a reflexive
strictly convex normed space has a unique closest point in every nonempty closed real-convex
set `S`. -/
theorem existsUnique_isMinOn_norm_sub {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    [StrictConvexSpace ℝ V] (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {S : Set V} (hne : S.Nonempty) (hSclosed : IsClosed S) (hSconv : Convex ℝ S) (x₀ : V) :
    ∃! u, u ∈ S ∧ IsMinOn (fun v : V ↦ ‖v - x₀‖) S u := by
  have hstrict : StrictConvexOn ℝ S fun v : V ↦ ‖v - x₀‖ ^ (2 : ℝ) := by
    have htr := (strictConvexOn_norm_rpow (E := V) one_lt_two).translate_right (-x₀)
    have heq : ((fun x : V ↦ ‖x‖ ^ (2 : ℝ)) ∘ fun z ↦ -x₀ + z) =
        fun v : V ↦ ‖v - x₀‖ ^ (2 : ℝ) := by
      ext v
      rw [Function.comp_apply, neg_add_eq_sub]
    rw [heq] at htr
    exact htr.subset (subset_univ S) hSconv
  have hcont : Continuous fun v : V ↦ ‖v - x₀‖ ^ (2 : ℝ) :=
    (continuous_id.sub continuous_const).norm.rpow_const fun _ ↦ Or.inr zero_le_two
  obtain ⟨u, ⟨hu, hmin⟩, huniq⟩ := existsUnique_isMinOn_of_strictConvexOn_of_isClosed hV hne
    hSclosed hstrict (hcont.lowerSemicontinuous.lowerSemicontinuousOn S)
    (hasBoundedSublevelsOn_norm_sub_rpow x₀ zero_lt_two)
  have hiff : ∀ w : V, IsMinOn (fun v : V ↦ ‖v - x₀‖) S w ↔
      IsMinOn (fun v : V ↦ ‖v - x₀‖ ^ (2 : ℝ)) S w := fun w ↦ by
    refine ⟨fun hw y hy ↦ Real.rpow_le_rpow (norm_nonneg _) (hw hy) zero_le_two,
      fun hw y hy ↦ (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) zero_lt_two).1 (hw hy)⟩
  exact ⟨u, ⟨hu, (hiff u).2 hmin⟩, fun v ⟨hv, hminv⟩ ↦ huniq v ⟨hv, (hiff v).1 hminv⟩⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [UniformConvexSpace V]

/-- In a uniformly convex Banach space (for instance any Hilbert space over `ℝ` or `ℂ`), every
superlinear norm-power energy with a continuous real-linear perturbation `v ↦ c * ‖v‖ ^ p + f v`
(`0 < c`, `1 < p`) has a unique minimizer on every nonempty closed real-convex set. -/
theorem existsUnique_isMinOn_const_mul_norm_rpow_add_linear_of_uniformConvexSpace
    {S : Set V} (hne : S.Nonempty) (hSclosed : IsClosed S) (hSconv : Convex ℝ S)
    {c p : ℝ} (hc : 0 < c) (hp : 1 < p) (f : V →L[ℝ] ℝ) :
    ∃! u, u ∈ S ∧ IsMinOn (fun v : V ↦ c * ‖v‖ ^ p + f v) S u :=
  existsUnique_isMinOn_const_mul_norm_rpow_add_linear
    (surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := ℝ))
    hne hSclosed hSconv hc hp f

/-- **Best approximation in uniformly convex Banach spaces.** Every point `x₀` in a uniformly
convex Banach space has a unique closest point in every nonempty closed real-convex set `S`. -/
theorem existsUnique_isMinOn_norm_sub_of_uniformConvexSpace
    {S : Set V} (hne : S.Nonempty) (hSclosed : IsClosed S) (hSconv : Convex ℝ S) (x₀ : V) :
    ∃! u, u ∈ S ∧ IsMinOn (fun v : V ↦ ‖v - x₀‖) S u :=
  existsUnique_isMinOn_norm_sub
    (surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := ℝ))
    hne hSclosed hSconv x₀

end StrictAndUniformConvex

section ConcaveCounterexample

variable {ι 𝕜 H : Type*} [Infinite ι] [RCLike 𝕜] [SeminormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- Concavity breaks weak lower semicontinuity: in an inner-product space admitting an infinite
orthonormal family, `u ↦ -(‖u‖ ^ p)` (`0 < p`, covering `-‖u‖` and `-‖u‖²`) is not weakly lower
semicontinuous at `0`. -/
theorem not_lowerSemicontinuousAt_neg_norm_rpow_comp_toWeakSpace_symm_zero
    {e : ι → H} (he : Orthonormal 𝕜 e) {p : ℝ} (hp : 0 < p) :
    ¬ LowerSemicontinuousAt
      (fun u : WeakSpace 𝕜 H ↦ -(‖(toWeakSpace 𝕜 H).symm u‖ ^ p))
      (toWeakSpace 𝕜 H 0) := by
  intro hlsc
  have hzero : -(‖(toWeakSpace 𝕜 H).symm (toWeakSpace 𝕜 H 0)‖ ^ p) = 0 := by
    simp [Real.zero_rpow hp.ne']
  have hev : ∀ᶠ i in cofinite, (-1 : ℝ) < -(‖e i‖ ^ p) := by
    have hlt : (-1 : ℝ) < -(‖(toWeakSpace 𝕜 H).symm (toWeakSpace 𝕜 H 0)‖ ^ p) := by
      rw [hzero]
      norm_num
    simpa only [LinearEquiv.symm_apply_apply] using
      he.tendsto_toWeakSpace_zero_cofinite.eventually (hlsc (-1) hlt)
  obtain ⟨i, hi⟩ := hev.exists
  have hnorm : ‖e i‖ = 1 := he.1 i
  rw [hnorm, Real.one_rpow] at hi
  exact lt_irrefl (-1 : ℝ) hi

/-- In an inner-product space admitting an infinite orthonormal family, `u ↦ ‖u‖ ^ p` (`0 < p`)
is not weakly continuous at `0`, showing that weak lower semicontinuity of `‖·‖ ^ p` (`1 ≤ p`)
is strictly weaker than weak continuity. -/
theorem not_continuousAt_norm_rpow_comp_toWeakSpace_symm_zero
    {e : ι → H} (he : Orthonormal 𝕜 e) {p : ℝ} (hp : 0 < p) :
    ¬ ContinuousAt
      (fun u : WeakSpace 𝕜 H ↦ ‖(toWeakSpace 𝕜 H).symm u‖ ^ p)
      (toWeakSpace 𝕜 H 0) :=
  fun hcont ↦ not_lowerSemicontinuousAt_neg_norm_rpow_comp_toWeakSpace_symm_zero he hp
    hcont.neg.lowerSemicontinuousAt

end ConcaveCounterexample

end TauCeti
