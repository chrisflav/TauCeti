/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Analysis.Normed.Module.DoubleDual
public import TauCeti.Topology.Semicontinuity.WeakSpace
public import Mathlib.Analysis.RCLike.Basic
import TauCeti.Analysis.Variational.DirectMethod
import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# The sequential direct method in the weak topology

In a reflexive seminormed space over `ℝ` or `ℂ`, Kaplansky–Whitley upgrades sequential weak
closedness and sequential weak lower semicontinuity to their topological counterparts on every
norm-bounded set (`TauCeti.isClosed_toWeakSpace_iff_isSeqClosed_of_isBounded` and
`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isBounded` in
`TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian`; general weak sequential lower
semicontinuity characterizations live in `TauCeti.Topology.Semicontinuity.WeakSpace`).

Consequently, the direct method holds under purely sequential weak hypotheses without assuming the
admissible set `S` is topologically weakly closed:

* `TauCeti.isCompact_toWeakSpace_sublevel_of_isSeqClosed` and
  `TauCeti.exists_isMinOn_of_isSeqClosed`: without assuming the energy is bounded below, on a
  sequentially weakly closed set every norm-bounded sublevel of a sequentially weakly lower
  semicontinuous energy into a linear order is weakly compact, an energy with bounded sublevels on
  a nonempty sequentially weakly closed set attains its minimum, and its minimizer set is weakly
  compact (`TauCeti.isCompact_toWeakSpace_minimizers_of_isSeqClosed`).
* `TauCeti.exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence` and
  `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`: when `E '' S` is bounded below in a
  conditionally complete lattice equipped with a topology and a norm-bounded minimizing sequence in
  a sequentially weakly closed set `S` exists, the sequence has a weakly convergent subsequence
  whose limit is an admissible minimizer; when at most one admissible minimizer exists, the entire
  minimizing sequence converges weakly to it
  (`TauCeti.tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence`).

Neither completeness of `V` nor point-separation of the seminorm is assumed.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, Theorem 4.
* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.8, Theorem 2.8.14.
-/

public section

open Bornology Filter NormedSpace Set Topology

namespace TauCeti

section LinearOrder

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

/-- On a sequentially weakly closed set in a reflexive seminormed space over `ℝ` or `ℂ`, a
norm-bounded sublevel of a sequentially weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
  isCompact_toWeakSpace_of_isSeqClosed_of_isBounded hV hb
    (hE.isSeqClosed_toWeakSpace_sublevel hS b)

/-- **Local sublevel sequential direct method.** In a reflexive seminormed space over `ℝ` or `ℂ`,
if a single nonempty norm-bounded sublevel `{u ∈ S | E u ≤ b}` is sequentially weakly closed and `E`
is sequentially weakly lower semicontinuous on that sublevel alone, then `E` attains its minimum on
all of `S`. -/
theorem exists_isMinOn_of_isSeqClosed_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {b : β} (hsub : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u :=
  exists_isMinOn_of_weak_closed_sublevel hV
    ((isClosed_toWeakSpace_iff_isSeqClosed_of_isBounded hV hb).2 hsub)
    ((seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isBounded hV hb).1 hE)
    hne hb

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, a single nonempty norm-bounded sublevel
suffices for the sequential direct method on a sequentially weakly closed admissible set. -/
theorem exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u :=
  exists_isMinOn_of_isSeqClosed_sublevel hV
    (hE.isSeqClosed_toWeakSpace_sublevel hS b)
    (hE.mono (image_mono fun _ hx ↦ hx.1)) hne hb

/-- **Sequential direct method (sublevel form).** A sequentially weakly lower semicontinuous energy
with bounded sublevels on a nonempty sequentially weakly closed set in a reflexive seminormed space
over `ℝ` or `ℂ` attains its minimum. Neither topological weak closedness of `S` nor boundedness
below of `E` is assumed. -/
theorem exists_isMinOn_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the set of minimizers of a sequentially weakly lower semicontinuous energy on a sequentially
weakly closed set in a reflexive seminormed space over `ℝ` or `ℂ` is norm-bounded, then that set of
minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_image_minimizers_of_isBounded
    (isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE) hb

/-- For a sequentially weakly lower semicontinuous energy with bounded sublevels on a sequentially
weakly closed set in a reflexive seminormed space over `ℝ` or `ℂ`, the set of minimizers is weakly
compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  hb.isCompact_image_minimizers (isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE)

end LinearOrder

section MinimizingSequence

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Subsequential convergence of bounded minimizing sequences.** In a reflexive seminormed space
over `ℝ` or `ℂ`, every norm-bounded minimizing sequence in a sequentially weakly closed set for a
sequentially weakly lower semicontinuous energy bounded below has a subsequence converging weakly to
an admissible minimizer. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, v ∈ S → (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v := by
  obtain ⟨v, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure
    (isCompact_closure_toWeakSpace hreflexive hb) mem_range_self
  have hvS : v ∈ S := hseqclosed (fun n ↦ hu (φ n)) hlim
  have hEv : E v ≤ sInf (E '' S) :=
    hseqlsc hvS (fun n ↦ hu (φ n)) hlim (hminseq.comp hφ.tendsto_atTop)
  exact ⟨v, hvS, φ, hφ, hlim, fun w hw ↦ hEv.trans (csInf_le hbelow (mem_image_of_mem E hw))⟩

/-- **The sequential direct method.** In a reflexive seminormed space over `ℝ` or `ℂ`, an energy
bounded below on a sequentially weakly closed set, sequentially weakly lower semicontinuous along
convergent energy sequences, attains its minimum on `S` as soon as one norm-bounded minimizing
sequence exists. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, v ∈ S → (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hvS, -, -, -, hmin⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc hu hb hminseq
  exact ⟨v, hvS, hmin⟩

/-- **Full-sequence weak convergence to a unique minimizer.** Under the hypotheses of the sequential
direct method, if at most one admissible point `v` can minimize `E` on `S` (`∀ w ∈ S, IsMinOn E S w
→ w = v`), then `v` is an admissible minimizer and the entire norm-bounded minimizing sequence
converges weakly to `v` without passing to a subsequence. -/
theorem tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃w : ℕ → V⦄ ⦃z : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V z)) → z ∈ S)
    (hseqlsc : ∀ ⦃w : ℕ → V⦄ ⦃z : V⦄ ⦃r : β⦄, z ∈ S → (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V z)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E z ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))))
    {v : V} (huniq : ∀ w ∈ S, IsMinOn E S w → w = v) :
    v ∈ S ∧ IsMinOn E S v ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  obtain ⟨v₀, hv₀S, -, -, -, hv₀min⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc hu hb hminseq
  obtain rfl := huniq v₀ hv₀S hv₀min
  refine ⟨hv₀S, hv₀min, tendsto_of_subseq_tendsto fun ns hns ↦ ?_⟩
  obtain ⟨ψ, -, hnsψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨w, hwS, σ, -, hlim, hwmin⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc (fun n ↦ hu (ns (ψ n)))
      (hb.subset (range_comp_subset_range _ _))
      (hminseq.comp hnsψ.tendsto_atTop)
  exact ⟨ψ ∘ σ, huniq w hwS hwmin ▸ hlim⟩

namespace SeqLowerSemicontinuousOn

/-- Bundled-predicate form of
`TauCeti.exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence` using
`IsSeqClosed` and `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v :=
  TauCeti.exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
    hreflexive hbelow (isSeqClosed_toWeakSpace_iff.1 hS)
    (fun _ _ _ hv hw hlim hEu ↦ hE.le_of_tendsto_toWeakSpace hv hw hlim hEu) hu hb hminseq

/-- Bundled-predicate form of `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence` using
`IsSeqClosed` and `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v :=
  TauCeti.exists_isMinOn_of_bounded_minimizing_sequence hreflexive hbelow
    (isSeqClosed_toWeakSpace_iff.1 hS)
    (fun _ _ _ hv hw hlim hEu ↦ hE.le_of_tendsto_toWeakSpace hv hw hlim hEu) hu hb hminseq

/-- Bundled-predicate form of
`TauCeti.tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence` using `IsSeqClosed`
and `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))))
    {v : V} (huniq : ∀ w ∈ S, IsMinOn E S w → w = v) :
    v ∈ S ∧ IsMinOn E S v ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) :=
  TauCeti.tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence
    hreflexive hbelow (isSeqClosed_toWeakSpace_iff.1 hS)
    (fun _ _ _ hv hw hlim hEu ↦ hE.le_of_tendsto_toWeakSpace hv hw hlim hEu) hu hb hminseq huniq

end SeqLowerSemicontinuousOn

end MinimizingSequence

end TauCeti
