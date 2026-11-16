/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
import TauCeti.Order.Filter.Extr

/-!
# Basic closure properties of convex and quasiconvex functions

This file collects elementary algebraic facts for convex, strictly convex, and quasiconvex
functions:

* `StrictConvexOn.comp_affineMap_of_injective` — an injective affine pullback preserves strict
  convexity, adapted from the
  [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/ContactMeasure.lean#L993).
* `StrictConvexOn.smul` — scaling by a positive scalar preserves strict convexity.
* `TauCeti.convexOn_sum` — a finite sum of convex functions on a convex set is convex.
* `QuasiconvexOn.convex_minimizers` — the set of minimizers of a quasiconvex function on its
  domain is convex.
-/

public section

open Set

/-- An injective affine change of variables preserves strict convexity on the preimage. -/
theorem StrictConvexOn.comp_affineMap_of_injective
    {𝕜 E F β : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
    {S : Set E} {v : E → β} (hv : StrictConvexOn 𝕜 S v) (A : F →ᵃ[𝕜] E)
    (hA : Function.Injective A) : StrictConvexOn 𝕜 (A ⁻¹' S) (v ∘ A) := by
  refine ⟨hv.1.affine_preimage A, fun a ha b hb hab p q hp hq hpq => ?_⟩
  simp only [Function.comp_apply, Convex.combo_affine_apply hpq]
  exact hv.2 ha hb (fun h => hab (hA h)) hp hq hpq

/-- Scaling a strictly convex function by a positive scalar preserves strict convexity. -/
theorem StrictConvexOn.smul {𝕜 E β : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] [AddCommMonoid β] [PartialOrder β]
    [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f : E → β}
    {c : 𝕜} (hc : 0 < c) (hf : StrictConvexOn 𝕜 s f) :
    StrictConvexOn 𝕜 s fun x ↦ c • f x :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab ↦
    calc c • f (a • x + b • y) < c • (a • f x + b • f y) :=
          smul_lt_smul_of_pos_left (hf.2 hx hy hxy ha hb hab) hc
      _ = a • c • f x + b • c • f y := by rw [smul_add, smul_comm c, smul_comm c]⟩

namespace TauCeti

/-- A finite sum of convex functions on a convex set is convex on that set. -/
theorem convexOn_sum {ι 𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] [AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β] [DistribMulAction 𝕜 β]
    {s : Set E} (hs : Convex 𝕜 s) {t : Finset ι} {f : ι → E → β}
    (hf : ∀ i ∈ t, ConvexOn 𝕜 s (f i)) :
    ConvexOn 𝕜 s fun x ↦ ∑ i ∈ t, f i x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨hs, fun _ _ _ _ _ _ _ _ _ ↦ ?_⟩
    simp
  | insert i t hi ih =>
    have h1 := hf i (Finset.mem_insert_self i t)
    have h2 := ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi, Pi.add_def] using h1.add h2

end TauCeti

/-- The set of minimizers of a quasiconvex function on its domain is convex. -/
theorem QuasiconvexOn.convex_minimizers {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] [Preorder β] {s : Set E} {f : E → β}
    (hf : QuasiconvexOn 𝕜 s f) : Convex 𝕜 {x ∈ s | IsMinOn f s x} := by
  obtain hempty | ⟨u, hu, hmin⟩ := {x ∈ s | IsMinOn f s x}.eq_empty_or_nonempty
  · rw [hempty]
    exact convex_empty
  · rw [hmin.minimizers_eq_sublevel hu]
    exact hf (f u)
