/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.Compactness.CountablyCompact

/-!
# Convergence and quotient induction in the weak topology

A family converges in `WeakSpace 𝕜 E` exactly when its values under every continuous linear
functional converge (`TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto`). This lets
weak convergence be used without unfolding the definition of `WeakSpace` as a `WeakBilin` space.
No injectivity of the duality pairing is needed, since the weak topology is induced by the
evaluations. Sequential closedness of `toWeakSpace 𝕜 E '' S` unfolds directly to a statement on
sequences in `E` (`TauCeti.isSeqClosed_toWeakSpace_iff`).

When the scalar ring `𝕜` is `T₀`, every continuous linear functional on `E` factors through
`SeparationQuotient E`, so `WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)` induces the weak topology
from that of the separated quotient (`WeakSpace.isInducing_map_mkCLM`) and transfers weak
convergence, weak compactness, weak sequential compactness, and weak closures between `E` and
`SeparationQuotient E`.

When the weak topology is Hausdorff, weak convergence implies convergence in the original topology
for families that eventually stay in a compact set
(`TauCeti.tendsto_of_tendsto_toWeakSpace_of_isCompact`): on a compact set the two topologies agree.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- A family converges weakly exactly when its values under every continuous linear functional
converge. -/
theorem tendsto_toWeakSpace_iff_forall_eval_tendsto {α : Type*} {l : Filter α} {u : α → E}
    {x : E} :
    Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) l (𝓝 (toWeakSpace 𝕜 E x)) ↔
      ∀ f : StrongDual 𝕜 E, Tendsto (fun n ↦ f (u n)) l (𝓝 (f x)) :=
  (IsInducing.induced _).tendsto_nhds_iff.trans tendsto_pi_nhds

/-- The weak image of `S` is sequentially closed if and only if weak limits of sequences in `S`
belong to `S`. -/
theorem isSeqClosed_toWeakSpace_iff {S : Set E} :
    IsSeqClosed (toWeakSpace 𝕜 E '' S) ↔
      ∀ ⦃u : ℕ → E⦄ ⦃v : E⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E v)) → v ∈ S := by
  refine ⟨fun h u v hu hlim ↦ ?_, fun h u w hu hlim ↦ ?_⟩
  · obtain ⟨v', hv', heq⟩ :=
      h (fun n ↦ mem_image_of_mem (toWeakSpace 𝕜 E) (hu n)) hlim
    exact (toWeakSpace 𝕜 E).injective heq ▸ hv'
  · obtain ⟨v, rfl⟩ := (toWeakSpace 𝕜 E).surjective w
    choose x hx hux using hu
    exact mem_image_of_mem (toWeakSpace 𝕜 E) (h hx (by simpa only [hux] using hlim))

/-- If the weak topology is Hausdorff, a family that eventually stays in a compact set and
converges weakly to `a` converges to `a` in the original topology. -/
theorem tendsto_of_tendsto_toWeakSpace_of_isCompact [T2Space (WeakSpace 𝕜 E)] {α : Type*}
    {l : Filter α} {K : Set E} (hK : IsCompact K) {u : α → E} (hu : ∀ᶠ n in l, u n ∈ K) {a : E}
    (h : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) l (𝓝 (toWeakSpace 𝕜 E a))) :
    Tendsto u l (𝓝 a) := by
  refine hK.tendsto_nhds_of_unique_mapClusterPt hu fun y _ hy ↦ (toWeakSpace 𝕜 E).injective ?_
  -- A cluster point in the original topology is a weak cluster point, and the weak topology is
  -- Hausdorff.
  have hy' : MapClusterPt (toWeakSpace 𝕜 E y) l (fun n ↦ toWeakSpace 𝕜 E (u n)) :=
    hy.tendsto_comp ((toWeakSpaceCLM 𝕜 E).continuous.tendsto y)
  exact eq_of_nhds_neBot (hy'.neBot.mono (inf_le_inf_left _ h))

end TauCeti

namespace WeakSpace

variable {𝕜 E F : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- `WeakSpace.map` intertwines `toWeakSpace` with the underlying continuous linear map. -/
@[simp]
theorem map_toWeakSpace [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
    (f : E →L[𝕜] F) (x : E) :
    WeakSpace.map f (toWeakSpace 𝕜 E x) = toWeakSpace 𝕜 F (f x) :=
  (rfl)

/-- `WeakSpace.map f` is surjective if and only if `f` is surjective. -/
theorem map_surjective_iff [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
    {f : E →L[𝕜] F} :
    Function.Surjective (WeakSpace.map f) ↔ Function.Surjective f := by
  refine ⟨fun hf y ↦ ?_, fun hf y ↦ ?_⟩
  · obtain ⟨w, hw⟩ := hf (toWeakSpace 𝕜 F y)
    obtain ⟨x, rfl⟩ := (toWeakSpace 𝕜 E).surjective w
    exact ⟨x, (toWeakSpace 𝕜 F).injective (by simpa only [map_toWeakSpace] using hw)⟩
  · obtain ⟨x, hx⟩ := hf ((toWeakSpace 𝕜 F).symm y)
    exact ⟨toWeakSpace 𝕜 E x, by simp [hx]⟩

/-- Pushing `toWeakSpace 𝕜 E '' s` along `WeakSpace.map f` gives the weak image of `f '' s`. -/
theorem image_map_toWeakSpace [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
    (f : E →L[𝕜] F) (s : Set E) :
    WeakSpace.map f '' (toWeakSpace 𝕜 E '' s) = toWeakSpace 𝕜 F '' (f '' s) := by
  simp_rw [← image_comp, Function.comp_def, map_toWeakSpace]

section SeparationQuotient

variable [T0Space 𝕜] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]

/-- When `𝕜` is `T₀`, pushing forward to `SeparationQuotient E` induces the weak topology on
`WeakSpace 𝕜 E`, because every continuous `𝕜`-linear functional factors through the separation
quotient. -/
theorem isInducing_map_mkCLM :
    IsInducing (WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)) := by
  let q := WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)
  rw [isInducing_iff_nhds]
  intro z
  obtain ⟨x, rfl⟩ := (toWeakSpace 𝕜 E).surjective z
  refine le_antisymm (tendsto_iff_comap.mp (q.continuous.tendsto _)) ?_
  rw [← tendsto_id']
  have hid : (id : WeakSpace 𝕜 E → WeakSpace 𝕜 E) =
      fun w ↦ toWeakSpace 𝕜 E ((toWeakSpace 𝕜 E).symm w) :=
    funext fun w ↦ ((toWeakSpace 𝕜 E).apply_symm_apply w).symm
  rw [hid, TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto]
  intro f
  have hq : Tendsto
      (fun w ↦ toWeakSpace 𝕜 (SeparationQuotient E)
        ((toWeakSpace 𝕜 (SeparationQuotient E)).symm (q w)))
      (comap q (𝓝 (q (toWeakSpace 𝕜 E x))))
      (𝓝 (toWeakSpace 𝕜 (SeparationQuotient E) (SeparationQuotient.mkCLM 𝕜 E x))) := by
    simp_rw [LinearEquiv.apply_symm_apply, ← map_toWeakSpace]
    exact tendsto_comap
  have hf := TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.mp hq
    (SeparationQuotient.liftCLM f fun _ _ h ↦ (h.map f.continuous).eq)
  have hfun (w : WeakSpace 𝕜 E) :
      SeparationQuotient.liftCLM f (fun _ _ h ↦ (h.map f.continuous).eq)
        ((toWeakSpace 𝕜 (SeparationQuotient E)).symm (q w)) =
        f ((toWeakSpace 𝕜 E).symm w) := by
    conv_lhs => rw [← (toWeakSpace 𝕜 E).apply_symm_apply w]
    rw [map_toWeakSpace, LinearEquiv.symm_apply_apply, SeparationQuotient.mkCLM_apply,
      SeparationQuotient.liftCLM_mk]
  simpa only [hfun, SeparationQuotient.mkCLM_apply, SeparationQuotient.liftCLM_mk] using hf

/-- When `𝕜` is `T₀`, a family converges weakly in `E` if and only if its image under
`SeparationQuotient.mkCLM 𝕜 E` converges weakly in `SeparationQuotient E`. -/
theorem tendsto_toWeakSpace_mkCLM_iff {α : Type*} {l : Filter α} {u : α → E} {x : E} :
    Tendsto (fun n ↦ toWeakSpace 𝕜 (SeparationQuotient E) (SeparationQuotient.mkCLM 𝕜 E (u n)))
      l (𝓝 (toWeakSpace 𝕜 (SeparationQuotient E) (SeparationQuotient.mkCLM 𝕜 E x))) ↔
      Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) l (𝓝 (toWeakSpace 𝕜 E x)) := by
  simpa only [Function.comp_def, map_toWeakSpace] using
    ((isInducing_map_mkCLM (𝕜 := 𝕜) (E := E)).tendsto_nhds_iff
      (f := fun n ↦ toWeakSpace 𝕜 E (u n)) (y := toWeakSpace 𝕜 E x)).symm

/-- When `𝕜` is `T₀`, `WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E)` commutes with topological
closure. -/
theorem image_map_mkCLM_closure (s : Set (WeakSpace 𝕜 E)) :
    WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E) '' closure s =
      closure (WeakSpace.map (SeparationQuotient.mkCLM 𝕜 E) '' s) := by
  rw [(isInducing_map_mkCLM (𝕜 := 𝕜) (E := E)).closure_eq_preimage_closure_image,
    (map_surjective_iff.2 SeparationQuotient.surjective_mk).image_preimage]

/-- When `𝕜` is `T₀`, a set in `E` is weakly compact if and only if its image in
`SeparationQuotient E` is weakly compact. -/
theorem isCompact_toWeakSpace_mkCLM_iff {s : Set E} :
    IsCompact (toWeakSpace 𝕜 (SeparationQuotient E) '' (SeparationQuotient.mkCLM 𝕜 E '' s)) ↔
      IsCompact (toWeakSpace 𝕜 E '' s) := by
  rw [← image_map_toWeakSpace, ← (isInducing_map_mkCLM (𝕜 := 𝕜) (E := E)).isCompact_iff]

/-- When `𝕜` is `T₀`, a set in `E` is weakly sequentially compact if and only if its image in
`SeparationQuotient E` is weakly sequentially compact. -/
theorem isSeqCompact_toWeakSpace_mkCLM_iff {s : Set E} :
    IsSeqCompact (toWeakSpace 𝕜 (SeparationQuotient E) '' (SeparationQuotient.mkCLM 𝕜 E '' s)) ↔
      IsSeqCompact (toWeakSpace 𝕜 E '' s) := by
  rw [← image_map_toWeakSpace, ← (isInducing_map_mkCLM (𝕜 := 𝕜) (E := E)).isSeqCompact_iff]

/-- When `𝕜` is `T₀`, a set in `E` has weakly compact closure if and only if its image in
`SeparationQuotient E` has weakly compact closure. -/
theorem isCompact_closure_toWeakSpace_mkCLM_iff {s : Set E} :
    IsCompact (closure (toWeakSpace 𝕜 (SeparationQuotient E) ''
      (SeparationQuotient.mkCLM 𝕜 E '' s))) ↔
      IsCompact (closure (toWeakSpace 𝕜 E '' s)) := by
  rw [← image_map_toWeakSpace, ← image_map_mkCLM_closure,
    ← (isInducing_map_mkCLM (𝕜 := 𝕜) (E := E)).isCompact_iff]

/-- When `𝕜` is `T₀`, a vector lies in the weak closure of `s` if and only if its image in
`SeparationQuotient E` lies in the weak closure of `SeparationQuotient.mkCLM 𝕜 E '' s`. -/
theorem mem_closure_toWeakSpace_mkCLM_iff {s : Set E} {x : E} :
    toWeakSpace 𝕜 (SeparationQuotient E) (SeparationQuotient.mkCLM 𝕜 E x) ∈
      closure (toWeakSpace 𝕜 (SeparationQuotient E) ''
        (SeparationQuotient.mkCLM 𝕜 E '' s)) ↔
      toWeakSpace 𝕜 E x ∈ closure (toWeakSpace 𝕜 E '' s) := by
  rw [(isInducing_map_mkCLM (𝕜 := 𝕜) (E := E)).closure_eq_preimage_closure_image,
    mem_preimage, image_map_toWeakSpace, map_toWeakSpace]

end SeparationQuotient

end WeakSpace
