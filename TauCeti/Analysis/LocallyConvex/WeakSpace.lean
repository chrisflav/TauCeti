/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Analysis.Convex.Function.Basic
import TauCeti.Analysis.LocallyConvex.Mazur

/-!
# Weak lower semicontinuity of quasiconvex and convex functions

In a locally convex space over `ℝ` or `ℂ`, a real-convex set has the same closure in the original
and in the weak topology (`Convex.toWeakSpace_closure`). This file develops two consequences for
lower semicontinuity in the weak topology:

* **Topological weak lower semicontinuity**
  (`QuasiconvexOn.lowerSemicontinuousOn_comp_toWeakSpace_symm`,
  `QuasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm`,
  `TauCeti.lowerSemicontinuousOn_sum_comp_toWeakSpace_symm`): a lower semicontinuous quasiconvex
  function on an arbitrary (not necessarily closed) real-convex set is lower semicontinuous for
  the weak topology on that set. Since convex functions are quasiconvex (`ConvexOn.quasiconvexOn`),
  this covers lower semicontinuous convex functions and their finite sums, and applying it to a
  continuous real-linear functional `f` and `-f` shows that every continuous real-linear functional
  is weakly continuous even when the space is complex
  (`ContinuousLinearMap.continuous_comp_toWeakSpace_symm`, alongside
  `ContinuousLinearMap.continuous_re_comp_toWeakSpace_symm` for `StrongDual 𝕜 E`).
* **Pointwise weak lower semicontinuity and Mazur recovery sequences**: when lower semicontinuity
  is known only at the single weak limit point `x` (`LowerSemicontinuousWithinAt f s x`),
  quasiconvexity already yields `f x ≤ liminf (f ∘ u) l` along any nontrivial filter
  (`QuasiconvexOn.le_liminf_of_tendsto_weak`, `QuasiconvexOn.coe_le_liminf_of_tendsto_weak`).
  Without any lower semicontinuity assumption, for a real-valued convex function and a weakly
  convergent sequence `u n ⇀ x` at a point with a countable neighbourhood basis, applying Mazur's
  lemma (`TauCeti.exists_tendsto_sum_smul_of_tendsto_weak`) to tails of a `liminf`-realizing
  subsequence produces a strongly convergent recovery sequence `v n → x` in `s` with
  `limsup (f (v n) : EReal) ≤ liminf (f (u n) : EReal)`
  (`ConvexOn.exists_tendsto_limsup_le_liminf_of_tendsto_weak`). Passing to a `liminf`-realizing
  subsequence is essential: convex combinations from tails of an oscillating sequence only
  control the upper limit.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Corollary 3.9.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
-/

public section

open Filter Set Topology

section QuasiconvexOn

namespace QuasiconvexOn

variable {𝕜 E β : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E] {s : Set E} {f : E → β}

/-- **Weak lower semicontinuity on a convex set.** A lower semicontinuous quasiconvex function on
an arbitrary (not necessarily closed) real-convex subset `s` of a locally convex space is lower
semicontinuous for the weak topology on `s`. -/
theorem lowerSemicontinuousOn_comp_toWeakSpace_symm [LinearOrder β]
    (hf : QuasiconvexOn ℝ s f) (hlsc : LowerSemicontinuousOn f s) :
    LowerSemicontinuousOn (fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u))
      (toWeakSpace 𝕜 E '' s) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hlsc ⊢
  intro c
  obtain ⟨w, hw, hsw⟩ := hlsc c
  have hcl : s ∩ closure {x ∈ s | f x ≤ c} = {x ∈ s | f x ≤ c} := by
    refine subset_antisymm ?_ (subset_inter (fun _ hx ↦ hx.1) subset_closure)
    have hsub : {x ∈ s | f x ≤ c} ⊆ w := by
      intro x hx
      have hx' : x ∈ s ∩ f ⁻¹' Iic c := hx
      rw [hsw] at hx'
      exact hx'.2
    calc s ∩ closure {x ∈ s | f x ≤ c} ⊆ s ∩ w :=
          inter_subset_inter_right s (closure_minimal hsub hw)
      _ = {x ∈ s | f x ≤ c} := hsw.symm
  refine ⟨closure (toWeakSpace 𝕜 E '' {x ∈ s | f x ≤ c}), isClosed_closure, ?_⟩
  rw [← (hf c).toWeakSpace_closure 𝕜, ← image_inter (toWeakSpace 𝕜 E).injective, hcl]
  ext u
  simp only [(toWeakSpace 𝕜 E).image_eq_preimage_symm, mem_inter_iff, mem_preimage, mem_Iic,
    mem_ofPred_eq]

/-- **Weak lower semicontinuity.** A lower semicontinuous quasiconvex function on a locally convex
space is lower semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_comp_toWeakSpace_symm [LinearOrder β]
    (hf : QuasiconvexOn ℝ univ f) (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u) := by
  have h :=
    hf.lowerSemicontinuousOn_comp_toWeakSpace_symm (𝕜 := 𝕜) (hlsc.lowerSemicontinuousOn univ)
  simpa only [image_univ_of_surjective (toWeakSpace 𝕜 E).surjective,
    lowerSemicontinuousOn_univ_iff] using h

/-- If a quasiconvex function is lower semicontinuous within `s` at `x` and `u` converges
weakly to `x` along a nontrivial filter while eventually remaining in `{y ∈ s | f y ≤ c}`, then
`f x ≤ c`. -/
theorem le_of_eventually_le_of_tendsto_weak [LinearOrder β] {ι : Type*} {l : Filter ι} [NeBot l]
    (hf : QuasiconvexOn ℝ s f) {u : ι → E} {x : E}
    (hlsc : LowerSemicontinuousWithinAt f s x) (hu : ∀ᶠ i in l, u i ∈ s)
    (hlim : Tendsto (fun i ↦ toWeakSpace 𝕜 E (u i)) l (𝓝 (toWeakSpace 𝕜 E x)))
    {c : β} (hc : ∀ᶠ i in l, f (u i) ≤ c) : f x ≤ c := by
  have hxcl : x ∈ closure {y ∈ s | f y ≤ c} := by
    have hmem : toWeakSpace 𝕜 E x ∈ closure (toWeakSpace 𝕜 E '' {y ∈ s | f y ≤ c}) :=
      mem_closure_of_tendsto hlim <| (hu.and hc).mono fun _ hi ↦ mem_image_of_mem _ hi
    rw [← (hf c).toWeakSpace_closure 𝕜] at hmem
    exact (toWeakSpace 𝕜 E).injective.mem_set_image.mp hmem
  by_contra hnot
  have hlt : c < f x := lt_of_not_ge hnot
  obtain ⟨U, hUopen, hxU, hUs⟩ := mem_nhdsWithin.1 (hlsc c hlt)
  obtain ⟨y, hyU, hys, hyc⟩ := mem_closure_iff.1 hxcl U hUopen hxU
  exact not_lt_of_ge hyc (hUs ⟨hyU, hys⟩)

/-- **Pointwise weak lower semicontinuity along a convergent energy family.** If a quasiconvex
function is lower semicontinuous within `s` at `x`, `u` converges weakly to `x` along a
nontrivial filter while eventually staying in `s`, and `f ∘ u` converges to `r`, then `f x ≤ r`. -/
theorem le_of_tendsto_weak [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {ι : Type*} {l : Filter ι} [NeBot l] (hf : QuasiconvexOn ℝ s f) {u : ι → E} {x : E}
    (hlsc : LowerSemicontinuousWithinAt f s x) (hu : ∀ᶠ i in l, u i ∈ s)
    (hlim : Tendsto (fun i ↦ toWeakSpace 𝕜 E (u i)) l (𝓝 (toWeakSpace 𝕜 E x)))
    {r : β} (hflim : Tendsto (f ∘ u) l (𝓝 r)) : f x ≤ r := by
  by_contra hnot
  have hlt : r < f x := lt_of_not_ge hnot
  by_cases hmid : ∃ c : β, r < c ∧ c < f x
  · obtain ⟨c, hrc, hcfx⟩ := hmid
    have hc : ∀ᶠ i in l, f (u i) ≤ c :=
      (hflim.eventually (Iio_mem_nhds hrc)).mono fun _ hi ↦ le_of_lt hi
    exact not_le_of_gt hcfx (hf.le_of_eventually_le_of_tendsto_weak hlsc hu hlim hc)
  · have hIio : Iio (f x) = Iic r := by
      ext y
      simp only [mem_Iio, mem_Iic]
      exact ⟨fun hy ↦ not_lt.1 fun hry ↦ hmid ⟨y, hry, hy⟩, fun hy ↦ lt_of_le_of_lt hy hlt⟩
    have hc : ∀ᶠ i in l, f (u i) ≤ r := by
      have hmem : Iic r ∈ 𝓝 r := hIio ▸ Iio_mem_nhds hlt
      exact hflim hmem
    exact hnot (hf.le_of_eventually_le_of_tendsto_weak hlsc hu hlim hc)

/-- **Filter weak lower semicontinuity (`liminf` form).** If a quasiconvex function into a
conditionally complete linear order is lower semicontinuous within `s` at `x`, and `u`
converges weakly to `x` along a nontrivial filter while eventually staying in `s`, then
`f x ≤ liminf (f ∘ u) l`. -/
theorem le_liminf_of_tendsto_weak [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
    [OrderTopology β] {ι : Type*} {l : Filter ι} [NeBot l]
    (hf : QuasiconvexOn ℝ s f) {u : ι → E} {x : E}
    (hlsc : LowerSemicontinuousWithinAt f s x) (hu : ∀ᶠ i in l, u i ∈ s)
    (hlim : Tendsto (fun i ↦ toWeakSpace 𝕜 E (u i)) l (𝓝 (toWeakSpace 𝕜 E x)))
    (hc : IsCoboundedUnder (· ≥ ·) l (f ∘ u) := by isBoundedDefault)
    (hb : IsBoundedUnder (· ≥ ·) l (f ∘ u) := by isBoundedDefault) :
    f x ≤ liminf (f ∘ u) l := by
  -- Pass to the refined filter along which `f ∘ u` converges to its `liminf`.
  have hcl : MapClusterPt (liminf (f ∘ u) l) l (f ∘ u) := MapClusterPt.liminf hc hb
  let l' : Filter ι := l ⊓ comap (f ∘ u) (𝓝 (liminf (f ∘ u) l))
  have : NeBot l' := by
    rw [MapClusterPt, ClusterPt, ← Filter.push_pull'] at hcl
    exact (map_neBot_iff (f ∘ u)).1 (by simpa only [inf_comm] using hcl)
  exact hf.le_of_tendsto_weak hlsc (hu.filter_mono inf_le_left)
    (hlim.mono_left inf_le_left) (tendsto_comap.mono_left inf_le_right)

/-- **Weak lower semicontinuity in `EReal` for real-valued quasiconvex functions.** Taking the
lower limit in `EReal` drops boundedness side conditions on `f ∘ u` so that energies unbounded
above or below are handled uniformly. -/
theorem coe_le_liminf_of_tendsto_weak {ι : Type*} {l : Filter ι} [NeBot l]
    {f : E → ℝ} (hf : QuasiconvexOn ℝ s f) {u : ι → E} {x : E}
    (hlsc : LowerSemicontinuousWithinAt f s x) (hu : ∀ᶠ i in l, u i ∈ s)
    (hlim : Tendsto (fun i ↦ toWeakSpace 𝕜 E (u i)) l (𝓝 (toWeakSpace 𝕜 E x))) :
    (f x : EReal) ≤ liminf (fun i ↦ (f (u i) : EReal)) l := by
  have hq : QuasiconvexOn ℝ s (fun y ↦ (f y : EReal)) := by
    intro c
    induction c using EReal.rec with
    | bot =>
      have : {y ∈ s | (f y : EReal) ≤ ⊥} = ∅ := by
        ext y
        simp
      rw [this]
      exact convex_empty
    | coe r =>
      simpa only [EReal.coe_le_coe_iff] using hf r
    | top =>
      simpa only [le_top, and_true, ofPred_mem_eq] using hf.convex
  have hlsc' : LowerSemicontinuousWithinAt (fun y ↦ (f y : EReal)) s x := by
    intro b hb
    induction b using EReal.rec with
    | bot =>
      exact Filter.Eventually.of_forall fun y ↦ EReal.bot_lt_coe (f y)
    | coe r =>
      exact (hlsc r (EReal.coe_lt_coe_iff.1 hb)).mono fun _ hy ↦ EReal.coe_lt_coe_iff.2 hy
    | top =>
      exact (not_lt_of_ge le_top hb).elim
  exact hq.le_liminf_of_tendsto_weak hlsc' hu hlim

end QuasiconvexOn

/-- A finite sum of real-convex functions whose sum is lower semicontinuous on a real-convex set
`s` is weakly lower semicontinuous on `s`. Individual summands need not be lower semicontinuous
on their own. -/
theorem TauCeti.lowerSemicontinuousOn_sum_comp_toWeakSpace_symm {𝕜 E β ι : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] [Module ℝ β] [PosSMulMono ℝ β]
    {t : Finset ι} {s : Set E} (hs : Convex ℝ s) {f : ι → E → β}
    (hconv : ∀ i ∈ t, ConvexOn ℝ s (f i))
    (hlsc : LowerSemicontinuousOn (fun x ↦ ∑ i ∈ t, f i x) s) :
    LowerSemicontinuousOn
      (fun u : WeakSpace 𝕜 E ↦ ∑ i ∈ t, f i ((toWeakSpace 𝕜 E).symm u))
      (toWeakSpace 𝕜 E '' s) :=
  (TauCeti.convexOn_sum hs hconv).quasiconvexOn.lowerSemicontinuousOn_comp_toWeakSpace_symm hlsc

end QuasiconvexOn

section RealLinear

/-- The real part of a continuous `𝕜`-linear functional is weakly continuous. -/
theorem ContinuousLinearMap.continuous_re_comp_toWeakSpace_symm {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] (ℓ : StrongDual 𝕜 E) :
    Continuous fun u : WeakSpace 𝕜 E ↦ RCLike.re (ℓ ((toWeakSpace 𝕜 E).symm u)) :=
  RCLike.continuous_re.comp (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip ℓ)

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- Every continuous real-linear functional on a locally convex space over `ℝ` or `ℂ` is
continuous for the weak topology over `𝕜`. -/
theorem ContinuousLinearMap.continuous_comp_toWeakSpace_symm (f : E →L[ℝ] ℝ) :
    Continuous fun u : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm u) := by
  rw [continuous_iff_lower_upperSemicontinuous]
  refine ⟨(f.toLinearMap.convexOn
    convex_univ).quasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm
      f.continuous.lowerSemicontinuous, ?_⟩
  have hneg : LowerSemicontinuous fun u : WeakSpace 𝕜 E ↦ (-f) ((toWeakSpace 𝕜 E).symm u) :=
    ((-f).toLinearMap.convexOn
      convex_univ).quasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm
      (-f).continuous.lowerSemicontinuous
  intro u y hy
  filter_upwards [hneg u (-y) (neg_lt_neg hy)] with v hv
  exact lt_of_neg_lt_neg hv

end RealLinear

section MazurRecovery

namespace ConvexOn

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- **Mazur recovery sequence.** For a real-valued convex function `f` on `s` and a sequence `u`
eventually in `s` converging weakly to `x` at a point with a countable neighbourhood basis,
applying Mazur's lemma to tails of a `liminf`-realizing subsequence yields a sequence `v` in `s`
converging to `x` in the original topology with
`limsup (f (v n) : EReal) ≤ liminf (f (u n) : EReal)`. No lower semicontinuity is assumed. -/
theorem exists_tendsto_limsup_le_liminf_of_tendsto_weak {s : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ s f) {u : ℕ → E} {x : E} [IsCountablyGenerated (𝓝 x)]
    (hu : ∀ᶠ n in atTop, u n ∈ s)
    (hlim : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    ∃ v : ℕ → E, (∀ n, v n ∈ s) ∧ Tendsto v atTop (𝓝 x) ∧
      limsup (fun n ↦ (f (v n) : EReal)) atTop ≤
        liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  -- Extract a subsequence realizing the `EReal` lower limit and shift it into `s`.
  obtain ⟨φ, hφ_lim, hφ_top⟩ :=
    exists_seq_tendsto_liminf (f := atTop) (u := fun n ↦ (f (u n) : EReal))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hφ_top.eventually hu)
  let ψ : ℕ → ℕ := fun k ↦ φ (K + k)
  have hshift : Tendsto (fun k ↦ K + k) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat K
  have hψ_mem : ∀ k, u (ψ k) ∈ s := fun k ↦ hK (K + k) (Nat.le_add_right K k)
  have hψ_lim : Tendsto (fun k ↦ (f (u (ψ k)) : EReal)) atTop
      (𝓝 (liminf (fun n ↦ (f (u n) : EReal)) atTop)) := hφ_lim.comp hshift
  have hψ_weak : Tendsto (fun k ↦ toWeakSpace 𝕜 E (u (ψ k))) atTop (𝓝 (toWeakSpace 𝕜 E x)) :=
    hlim.comp (hφ_top.comp hshift)
  -- Apply Mazur's lemma to the tails of `u ∘ ψ` and bound `f` by Jensen's inequality.
  obtain ⟨t, w, hw, hsum, hv_lim⟩ :=
    TauCeti.exists_tendsto_sum_smul_of_tendsto_weak hψ_weak
  refine ⟨fun n ↦ ∑ i ∈ t n, w n i • u (ψ (n + i)),
    fun n ↦ hf.1.sum_mem (hw n) (hsum n) fun i _ ↦ hψ_mem (n + i), hv_lim, ?_⟩
  refine le_of_forall_gt_imp_ge_of_dense fun b hb ↦ ?_
  obtain ⟨r, hLr, hrb⟩ := EReal.exists_between_coe_real hb
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hψ_lim (Iio_mem_nhds hLr))
  have hbound : ∀ᶠ n in atTop,
      (f (∑ i ∈ t n, w n i • u (ψ (n + i))) : EReal) ≤ (r : EReal) := by
    refine eventually_atTop.2 ⟨N, fun n hn ↦ EReal.coe_le_coe_iff.2 ?_⟩
    calc f (∑ i ∈ t n, w n i • u (ψ (n + i)))
        ≤ ∑ i ∈ t n, w n i * f (u (ψ (n + i))) := by
          simpa only [smul_eq_mul] using
            hf.map_sum_le (hw n) (hsum n) fun i _ ↦ hψ_mem (n + i)
      _ ≤ ∑ i ∈ t n, w n i * r :=
          Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
            (EReal.coe_le_coe_iff.1 (le_of_lt (hN (n + i) (hn.trans (Nat.le_add_right n i)))))
            (hw n i hi)
      _ = r := by rw [← Finset.sum_mul, hsum n, one_mul]
  exact (limsup_le_of_le (by isBoundedDefault) hbound).trans hrb.le

end ConvexOn

end MazurRecovery
