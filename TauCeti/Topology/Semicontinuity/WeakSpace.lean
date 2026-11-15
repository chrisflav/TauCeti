/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Topology.Semicontinuity.Sequential

/-!
# Sequential lower semicontinuity in the weak topology

In any topological module `V` over a topological commutative semiring `𝕜`, sequential lower
semicontinuity of `E : V → β` on `WeakSpace 𝕜 V` (either globally or on `toWeakSpace 𝕜 V '' S`)
unfolds directly to statements along weakly convergent sequences in `V` without mentioning
`(toWeakSpace 𝕜 V).symm`:

* Into any preorder, strict lower bounds persist along weakly convergent sequences
  (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff`,
  `TauCeti.seqLowerSemicontinuous_toWeakSpace_iff`).
* Into a complete linear order, `E v ≤ liminf (E ∘ u) atTop` along weakly convergent sequences
  (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf`,
  `TauCeti.seqLowerSemicontinuous_toWeakSpace_iff_le_liminf`), and for `E : V → ℝ` via coercion to
  `EReal` (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_real_iff_le_liminf_ereal`,
  `TauCeti.seqLowerSemicontinuous_toWeakSpace_real_iff_le_liminf_ereal`).
* Into a linear order with `ClosedIciTopology`, convergent energy sequences satisfy `E v ≤ r` at a
  weak limit `v` (`TauCeti.SeqLowerSemicontinuousOn.le_of_tendsto_toWeakSpace`,
  `TauCeti.SeqLowerSemicontinuous.le_of_tendsto_toWeakSpace`).
* Into a linear order, sequential weak lower semicontinuity is equivalent to sequential weak
  closedness of all sublevels
  (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel`,
  `TauCeti.seqLowerSemicontinuous_toWeakSpace_iff_isSeqClosed_sublevel`).
-/

public section

open Filter Set Topology

namespace TauCeti

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- Sequential weak lower semicontinuity of `E` on `S` is equivalent to persistence of strict lower
bounds along sequences in `S` converging weakly to a point of `S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff {β : Type*} [Preorder β]
    {E : V → β} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ v ∈ S, ∀ b < E v, ∀ ⦃u : ℕ → V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        ∀ᶠ n in atTop, b < E (u n) := by
  rw [seqLowerSemicontinuousOn_iff]
  refine ⟨fun h v hv b hb u hu hlim ↦ ?_, fun h w hw b hb u' hu' hlim ↦ ?_⟩
  · simpa only [LinearEquiv.symm_apply_apply] using
      h (toWeakSpace 𝕜 V v) (mem_image_of_mem _ hv) b
        (by simpa only [LinearEquiv.symm_apply_apply] using hb)
        (fun n ↦ mem_image_of_mem _ (hu n)) hlim
  · obtain ⟨v, hv, rfl⟩ := hw
    choose u hu huu' using hu'
    simpa only [← huu', LinearEquiv.symm_apply_apply] using
      h v hv b (by simpa only [LinearEquiv.symm_apply_apply] using hb) hu
        (by simpa only [huu'] using hlim)

/-- Global sequential weak lower semicontinuity of `E` is equivalent to persistence of strict lower
bounds along weakly convergent sequences in `V`. -/
theorem seqLowerSemicontinuous_toWeakSpace_iff {β : Type*} [Preorder β] {E : V → β} :
    SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ↔
      ∀ v : V, ∀ b < E v, ∀ ⦃u : ℕ → V⦄,
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        ∀ᶠ n in atTop, b < E (u n) := by
  simpa only [← seqLowerSemicontinuousOn_univ_iff,
    image_univ_of_surjective (toWeakSpace 𝕜 V).surjective, mem_univ, forall_const,
    true_implies] using
    seqLowerSemicontinuousOn_toWeakSpace_iff (𝕜 := 𝕜) (V := V) (E := E) (S := univ)

/-- If `E` is sequentially weakly lower semicontinuous on `S`, `v ∈ S`, `b < E v`, and `u n ∈ S`
converges weakly to `v`, then eventually `b < E (u n)`. -/
theorem SeqLowerSemicontinuousOn.eventually_lt_toWeakSpace {β : Type*} [Preorder β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {v : V} (hv : v ∈ S) {b : β} (hb : b < E v) {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    ∀ᶠ n in atTop, b < E (u n) :=
  seqLowerSemicontinuousOn_toWeakSpace_iff.1 hE v hv b hb hu huv

/-- Global form of `TauCeti.SeqLowerSemicontinuousOn.eventually_lt_toWeakSpace`. -/
theorem SeqLowerSemicontinuous.eventually_lt_toWeakSpace {β : Type*} [Preorder β]
    {E : V → β}
    (hE : SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)))
    {v : V} {b : β} (hb : b < E v) {u : ℕ → V}
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    ∀ᶠ n in atTop, b < E (u n) :=
  seqLowerSemicontinuous_toWeakSpace_iff.1 hE v b hb huv

/-- Into a complete linear order, sequential weak lower semicontinuity of `E` on `S` is equivalent
to `E v ≤ liminf (E ∘ u) atTop` along sequences in `S` converging weakly to `v ∈ S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf
    {β : Type*} [CompleteLinearOrder β] {E : V → β} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ v ∈ S, ∀ ⦃u : ℕ → V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        E v ≤ liminf (fun n ↦ E (u n)) atTop := by
  rw [seqLowerSemicontinuousOn_iff_le_liminf]
  refine ⟨fun h v hv u hu hlim ↦ ?_, fun h w hw u' hu' hlim ↦ ?_⟩
  · simpa only [LinearEquiv.symm_apply_apply] using
      h (toWeakSpace 𝕜 V v) (mem_image_of_mem _ hv) (fun n ↦ mem_image_of_mem _ (hu n)) hlim
  · obtain ⟨v, hv, rfl⟩ := hw
    choose u hu huu' using hu'
    simpa only [← huu', LinearEquiv.symm_apply_apply] using
      h v hv hu (by simpa only [huu'] using hlim)

/-- Along any sequence in `S` converging weakly to `v ∈ S`, a sequentially weakly lower
semicontinuous function into a complete linear order satisfies `E v ≤ liminf (E ∘ u) atTop`. -/
theorem SeqLowerSemicontinuousOn.le_liminf_toWeakSpace
    {β : Type*} [CompleteLinearOrder β] {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {v : V} (hv : v ∈ S) {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    E v ≤ liminf (fun n ↦ E (u n)) atTop :=
  seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf.1 hE v hv hu huv

/-- Into a complete linear order, global sequential weak lower semicontinuity of `E` is equivalent
to `E v ≤ liminf (E ∘ u) atTop` along weakly convergent sequences in `V`. -/
theorem seqLowerSemicontinuous_toWeakSpace_iff_le_liminf
    {β : Type*} [CompleteLinearOrder β] {E : V → β} :
    SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ↔
      ∀ v : V, ∀ ⦃u : ℕ → V⦄,
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        E v ≤ liminf (fun n ↦ E (u n)) atTop := by
  simpa only [← seqLowerSemicontinuousOn_univ_iff,
    image_univ_of_surjective (toWeakSpace 𝕜 V).surjective, mem_univ, forall_const,
    true_implies] using
    seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf (𝕜 := 𝕜) (V := V) (E := E) (S := univ)

/-- Global form of `TauCeti.SeqLowerSemicontinuousOn.le_liminf_toWeakSpace`. -/
theorem SeqLowerSemicontinuous.le_liminf_toWeakSpace
    {β : Type*} [CompleteLinearOrder β] {E : V → β}
    (hE : SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)))
    {v : V} {u : ℕ → V}
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    E v ≤ liminf (fun n ↦ E (u n)) atTop :=
  seqLowerSemicontinuous_toWeakSpace_iff_le_liminf.1 hE v huv

/-- A real-valued energy `E` is sequentially weakly lower semicontinuous on `S` if and only if
`(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop` along sequences in `S` converging weakly
to `v ∈ S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_real_iff_le_liminf_ereal
    {E : V → ℝ} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ v ∈ S, ∀ ⦃u : ℕ → V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop :=
  seqLowerSemicontinuousOn_coe_ereal_iff.symm.trans
    (seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf (E := fun u ↦ (E u : EReal)))

/-- Along any sequence in `S` converging weakly to `v ∈ S`, a sequentially weakly lower
semicontinuous real-valued energy satisfies
`(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop`. -/
theorem SeqLowerSemicontinuousOn.le_liminf_ereal_toWeakSpace
    {E : V → ℝ} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {v : V} (hv : v ∈ S) {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop :=
  seqLowerSemicontinuousOn_toWeakSpace_real_iff_le_liminf_ereal.1 hE v hv hu huv

/-- A real-valued energy `E` is globally sequentially weakly lower semicontinuous if and only if
`(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop` along weakly convergent sequences in
`V`. -/
theorem seqLowerSemicontinuous_toWeakSpace_real_iff_le_liminf_ereal {E : V → ℝ} :
    SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ↔
      ∀ v : V, ∀ ⦃u : ℕ → V⦄,
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop :=
  seqLowerSemicontinuous_coe_ereal_iff.symm.trans
    (seqLowerSemicontinuous_toWeakSpace_iff_le_liminf (E := fun u ↦ (E u : EReal)))

/-- Global form of `TauCeti.SeqLowerSemicontinuousOn.le_liminf_ereal_toWeakSpace`. -/
theorem SeqLowerSemicontinuous.le_liminf_ereal_toWeakSpace {E : V → ℝ}
    (hE : SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)))
    {v : V} {u : ℕ → V}
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v))) :
    (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop :=
  seqLowerSemicontinuous_toWeakSpace_real_iff_le_liminf_ereal.1 hE v huv

/-- If `E` is sequentially weakly lower semicontinuous on `S`, `u n ∈ S` converges weakly to
`v ∈ S`, and `E (u n)` converges to `r` in a linear order with `ClosedIciTopology`, then
`E v ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto_toWeakSpace
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {v : V} (hv : v ∈ S) {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)))
    {r : β} (hEu : Tendsto (fun n ↦ E (u n)) atTop (𝓝 r)) :
    E v ≤ r := by
  simpa only [LinearEquiv.symm_apply_apply] using
    hE.le_of_tendsto (mem_image_of_mem _ hv) (fun n ↦ mem_image_of_mem _ (hu n)) huv
      (by simpa only [LinearEquiv.symm_apply_apply] using hEu)

/-- Global form of `TauCeti.SeqLowerSemicontinuousOn.le_of_tendsto_toWeakSpace`. -/
theorem SeqLowerSemicontinuous.le_of_tendsto_toWeakSpace
    {β : Type*} [LinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β}
    (hE : SeqLowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)))
    {v : V} {u : ℕ → V}
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)))
    {r : β} (hEu : Tendsto (fun n ↦ E (u n)) atTop (𝓝 r)) :
    E v ≤ r :=
  (hE.seqLowerSemicontinuousOn _).le_of_tendsto_toWeakSpace (mem_univ v) (fun _ ↦ mem_univ _)
    huv hEu

/-- On a sequentially weakly closed set `S`, sequential weak lower semicontinuity into a linear
order is equivalent to sequential weak closedness of every relative sublevel
`{u ∈ S | E u ≤ b}`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S)) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ b, IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have heq (b : β) : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} := by
    ext w
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage, mem_ofPred_eq]
  simp_rw [seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel hS, heq]

/-- Relative sublevels `{u ∈ S | E u ≤ b}` of a sequentially weakly lower semicontinuous function
into a linear order on a sequentially weakly closed set `S` are sequentially weakly closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_toWeakSpace_sublevel
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S)) (b : β) :
    IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
  (seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel hS).1 hE b

/-- Global sequential weak lower semicontinuity into a linear order is equivalent to sequential weak
closedness of every sublevel `{u | E u ≤ b}`. -/
theorem seqLowerSemicontinuous_toWeakSpace_iff_isSeqClosed_sublevel
    {β : Type*} [LinearOrder β] {E : V → β} :
    SeqLowerSemicontinuous (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u)) ↔
      ∀ b, IsSeqClosed (toWeakSpace 𝕜 V '' {u | E u ≤ b}) := by
  have huniv : IsSeqClosed (toWeakSpace 𝕜 V '' (univ : Set V)) := by
    rw [image_univ_of_surjective (toWeakSpace 𝕜 V).surjective]
    exact isClosed_univ.isSeqClosed
  simpa only [← seqLowerSemicontinuousOn_univ_iff,
    image_univ_of_surjective (toWeakSpace 𝕜 V).surjective, mem_univ, true_and] using
    seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel (E := E) huniv

/-- Sublevels `{u | E u ≤ b}` of a globally sequentially weakly lower semicontinuous function into a
linear order are sequentially weakly closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_toWeakSpace_sublevel
    {β : Type*} [LinearOrder β] {E : V → β}
    (hE : SeqLowerSemicontinuous (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u)))
    (b : β) :
    IsSeqClosed (toWeakSpace 𝕜 V '' {u | E u ≤ b}) :=
  seqLowerSemicontinuous_toWeakSpace_iff_isSeqClosed_sublevel.1 hE b

end TauCeti
