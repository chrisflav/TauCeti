/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Topology.Sets.Opens
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Sobolev.WeakDeriv.Haar
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local vector-valued Lebesgue and Sobolev classes

`TauCeti.MemLpLoc p U f μ` requires `Lᵖ` membership on every compact subset of `U` with respect
to `μ` (defaulting to `volume`), for a function `f : E → F` on a topological measure space `E`
with values in a normed additive commutative group `F`.
`TauCeti.MemWkpLoc p U k f μ` requires iterated weak derivatives through order `k` on
`interior U`, with `Lᵖ` bounds on every compact subset of `U` itself, for a function `f : E → F`
between real normed spaces. On open sets this is the usual local Sobolev class `W^{k,p}_loc(Ω; F)`;
for non-open sets reaching a boundary (such as half-discs in `ℂ`), the `Lᵖ` bounds reach the
boundary while test functions stay in the interior. Derivatives take values in iterated continuous
linear maps, rather than scalar jets.
These predicates concern actual functions; almost-everywhere changes do not affect membership.
They impose no global integrability condition on the possibly unbounded domain.
Global `Lᵖ` membership on a set implies local membership there (`MeasureTheory.MemLp.memLpLoc`).

This file supplies restriction to arbitrary subsets (also combined with a change of the function
off the subset), linearity, scalar-function multiples of a fixed vector in an arbitrary Banach
space (`TauCeti.MemLpLoc.smul_const`, `TauCeti.MemWkpLoc.smul_const`), continuous-linear
composition, pairing of fields of continuous linear maps into product maps, multiplication of local
`Lᵖ` functions by continuous factors (with extension by zero for factors supported in the domain),
composition of local `Lᵖ` operator families with continuous ones, pairing, pointwise product maps
of operator fields, decreasing the integrability exponent, decreasing the derivative order, scaling
and additive Haar-measure independence of the reference measure, and almost-everywhere strong
measurability on locally closed sets (`TauCeti.MemLpLoc.aestronglyMeasurable`).
On an open set, local `Lᵖ` membership is detected on the open subsets with compact closure inside
it. For continuous functions, local `Lᵖ` membership is automatic, so membership in `MemWkpLoc` at
successor order reduces to the existence of a weak derivative in the preceding class
(`ContinuousOn.memWkpLoc_succ_iff`, `ContinuousOn.memWkpLoc_one_iff_of_isOpen`).
Differentiability on an open set with a continuous (or locally `Lᵖ` and locally integrable)
derivative gives membership at order one (`DifferentiableOn.memWkpLoc_one`,
`DifferentiableOn.memWkpLoc_one_of_continuousOn_fderiv`), smoothness on an open neighbourhood gives
membership at every order without requiring a global smooth extension, and smooth maps on the whole
space are in every class on every set.
Conversely, if `g` is `Cᵏ` on an open set `Ω` and agrees almost everywhere there with
`u ∈ MemWkpLoc p Ω (k + m)`, then `fderiv ℝ g` is a weak derivative of `u`
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`, for `k ≥ 1`) and
`iteratedFDeriv ℝ k g ∈ MemWkpLoc p Ω m` (`TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`).
On a relatively open subset `Ω ∩ {0 ≤ im}` of the closed upper half-plane in `ℂ`, the interior is
`Ω ∩ {0 < im}` (`TauCeti.interior_inter_setOf_im_nonneg`), and since the real axis is null, local
`Lᵖ` membership there is detected on the upper halves `W ∩ {0 < im}`
(`TopologicalSpace.Opens.upperHalf`) of the open `W` with compact closure inside `Ω`
(`TauCeti.memLpLoc_inter_setOf_im_nonneg_iff`).
On locally closed sets, local `L¹` membership is identified with local integrability, supplying
the native weak-derivative hypotheses.
On open domains, with `1 ≤ p`, a locally `Lᵖ` function agrees almost everywhere with its precise
representative, and every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in
`MemWkpLoc p Ω k`; at order one, it is locally `Lᵖ`.
`TauCeti.WeakDerivChainLe` compares the `Lᵖ` norms of two planar maps and, recursively, of every
pair of their weak derivatives through a given order.
In positive order, completeness is inherited from the native weak-derivative predicate; the
definitions admit every real normed codomain without an additional typeclass assumption.
The continuous-linear composition result requires a complete target, as does the native
weak-derivative result it uses.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and their elementary operations).
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Mathematica 240 (2018), §2 (vector-valued first-order Sobolev spaces).
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-! ### Local `Lᵖ` classes on topological measure spaces -/

section MemLpLoc

variable {E F : Type*} [TopologicalSpace E] [MeasurableSpace E] [NormedAddCommGroup F]
  {p q : ENNReal} {U V : Set E} {f g : E → F} {μ ν : Measure E}

/-- A function is locally `Lᵖ` on `U` with respect to `μ` when it belongs to `Lᵖ` on every compact
subset of `U`. On a set reaching a boundary, those compact subsets include the boundary. -/
def MemLpLoc (p : ENNReal) (U : Set E) (f : E → F) (μ : Measure E := by volume_tac) : Prop :=
  ∀ K : Set E, K ⊆ U → IsCompact K → MemLp f p (μ.restrict K)

/-- Local `Lᵖ` membership is characterized by `Lᵖ` membership on every compact subset. -/
theorem memLpLoc_iff : MemLpLoc p U f μ ↔
    ∀ K : Set E, K ⊆ U → IsCompact K → MemLp f p (μ.restrict K) := Iff.rfl

/-- Local integrability restricts to any smaller set. -/
theorem MemLpLoc.mono_set (hf : MemLpLoc p U f μ) (hVU : V ⊆ U) : MemLpLoc p V f μ :=
  fun K hK hc => hf K (hK.trans hVU) hc

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_of_closure_subset (hf : MemLpLoc p U f μ) (hV : IsCompact (closure V))
    (hVU : closure V ⊆ U) : MemLp f p (μ.restrict V) :=
  (hf _ hVU hV).mono_measure (Measure.restrict_mono subset_closure le_rfl)

/-- A function that is `Lᵖ` on `U` is locally `Lᵖ` there. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc (hf : MemLp f p (μ.restrict U)) :
    MemLpLoc p U f μ :=
  fun _ hK _ => hf.mono_measure (Measure.restrict_mono hK le_rfl)

/-- Almost-everywhere equality on `U` preserves local `Lᵖ` membership. -/
theorem MemLpLoc.congr_ae (hf : MemLpLoc p U f μ)
    (hfg : f =ᵐ[μ.restrict U] g) : MemLpLoc p U g μ := by
  intro K hK hc
  exact (hf K hK hc).ae_eq (ae_mono (Measure.restrict_mono_set μ hK) hfg)

/-- Restricting to a subset preserves local `Lᵖ` membership of any function agreeing with the
original one on that subset. -/
theorem MemLpLoc.congr_mono [T2Space E] [OpensMeasurableSpace E] (hf : MemLpLoc p U f μ)
    (hgf : Set.EqOn g f V) (hVU : V ⊆ U) :
    MemLpLoc p V g μ := fun K hK hc => (hf K (hK.trans hVU) hc).ae_eq <| by
  filter_upwards [ae_restrict_mem hc.measurableSet] with z hz using (hgf (hK hz)).symm

/-- Compact subsets have finite measure, so decreasing the exponent preserves local membership.
In particular this passes from the infinity endpoint to every finite exponent. -/
theorem MemLpLoc.mono_exponent [IsFiniteMeasureOnCompacts μ] (hf : MemLpLoc p U f μ)
    (hqp : q ≤ p) : MemLpLoc q U f μ := by
  intro K hK hc
  have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  exact (hf K hK hc).mono_exponent hqp

/-- Multiplying the measure by a finite constant preserves local `Lᵖ` membership. -/
theorem MemLpLoc.smul_measure (hf : MemLpLoc p U f μ) {c : ENNReal} (hc : c ≠ ⊤) :
    MemLpLoc p U f (c • μ) := fun K hK hcK => by
  rw [Measure.restrict_smul]
  exact (hf K hK hcK).smul_measure hc

/-- Multiplying the measure by a finite nonzero constant leaves local `Lᵖ` membership unchanged. -/
theorem memLpLoc_smul_measure_iff {c : ENNReal} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    MemLpLoc p U f (c • μ) ↔ MemLpLoc p U f μ := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have h' := h.smul_measure (ENNReal.inv_ne_top.2 hc0)
  rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] at h'

/-- Local `Lᵖ` membership with respect to an additive Haar measure passes to every
translation-invariant measure finite on compact sets. -/
theorem MemLpLoc.of_isAddLeftInvariant {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] [ν.IsAddLeftInvariant]
    {U : Set G} {f : G → F} (hf : MemLpLoc p U f μ) : MemLpLoc p U f ν := by
  rw [Measure.isAddLeftInvariant_eq_smul ν μ]
  exact hf.smul_measure ENNReal.coe_ne_top

/-- **Haar-measure independence of local `Lᵖ` classes.** Any two additive Haar measures on a
locally compact second-countable topological additive group define the same local `Lᵖ` classes. -/
theorem memLpLoc_iff_of_isAddHaarMeasure {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {μ ν : Measure G}
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {U : Set G} {f : G → F} :
    MemLpLoc p U f μ ↔ MemLpLoc p U f ν :=
  ⟨fun h => h.of_isAddLeftInvariant ν, fun h => h.of_isAddLeftInvariant μ⟩

/-- A locally `Lᵖ` function on a locally closed set in a locally compact second-countable space is
almost everywhere strongly measurable there, for every exponent `p` (including `0 ≤ p < 1`). -/
theorem MemLpLoc.aestronglyMeasurable [LocallyCompactSpace E] [SecondCountableTopology E]
    (hf : MemLpLoc p U f μ) (hU : IsLocallyClosed U) :
    AEStronglyMeasurable f (μ.restrict U) := by
  rcases hU with ⟨O, Z, hO, hZ, rfl⟩
  choose K hKc hxK hKO using fun x : O => exists_compact_subset hO x.2
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : O => interior (K x)) (fun _ => isOpen_interior)
  have hOeq : O = ⋃ x ∈ T, interior (K x) := by
    rw [hT]
    exact Set.Subset.antisymm (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxK ⟨y, hy⟩⟩)
      (Set.iUnion_subset fun x => interior_subset.trans (hKO x))
  have hUeq : O ∩ Z = ⋃ x : T, (K x.1 ∩ Z) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    refine ⟨fun ⟨hyO, hyZ⟩ => ?_, fun ⟨x, hyK, hyZ⟩ => ⟨hKO x.1 hyK, hyZ⟩⟩
    rw [hOeq] at hyO
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.1 hyO
    exact ⟨⟨x, hxT⟩, interior_subset hyx, hyZ⟩
  have : Countable T := hTc.to_subtype
  rw [hUeq, aestronglyMeasurable_iUnion_iff]
  intro x
  exact (hf _ (Set.inter_subset_inter_left Z (hKO x.1))
    ((hKc x.1).inter_right hZ)).aestronglyMeasurable

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_restrict_of_isCompact_closure (hf : MemLpLoc p U f μ) {W : Set E}
    (hWc : IsCompact (closure W)) (hWU : closure W ⊆ U) : MemLp f p (μ.restrict W) :=
  (hf _ hWU hWc).mono_measure (Measure.restrict_mono subset_closure le_rfl)

/-- On an open set `Ω`, a function that agrees almost everywhere with an `Lᵖ` function on every
open `W` whose closure is compact and contained in `Ω` is locally `Lᵖ` on `Ω`. -/
theorem memLpLoc_of_forall_opens [LocallyCompactSpace E] [RegularSpace E] {Ω : Opens E}
    (h : ∀ W : Opens E, IsCompact (closure (W : Set E)) → closure (W : Set E) ⊆ Ω →
      ∃ g : E → F, MemLp g p (μ.restrict (W : Set E)) ∧ g =ᵐ[μ.restrict W] f) :
    MemLpLoc p Ω f μ := by
  refine fun K hKΩ hK => ?_
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨g, hg, hgf⟩ := h ⟨W, hWo⟩ hWc hWΩ
  exact (hg.ae_eq hgf).mono_measure (Measure.restrict_mono hKW le_rfl)

/-- A function that is `Lᵖ` on a set `W` is locally `Lᵖ` on every set `U` contained in `W` up to a
null set, including on compact subsets of `U` that leave `W`. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc_of_ae_le {W : Set E}
    (hf : MemLp f p (μ.restrict W)) (hUW : U ≤ᵐ[μ] W) : MemLpLoc p U f μ :=
  memLpLoc_iff.2 fun _ hK _ => hf.mono_measure
    (Measure.restrict_mono_ae ((Filter.EventuallySubset.of_subset hK).trans hUW))

end MemLpLoc

section MemLpLocNormed

variable {E F G : Type*} [TopologicalSpace E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]
  {p q : ENNReal} {U V : Set E} {f g : E → F} {μ : Measure E}

/-- The zero function belongs to every local `Lᵖ` class. -/
@[simp]
theorem memLpLoc_zero : MemLpLoc p U (0 : E → F) μ := fun _ _ _ => MemLp.zero

/-- Local `Lᵖ` membership is closed under addition. -/
theorem MemLpLoc.add (hf : MemLpLoc p U f μ) (hg : MemLpLoc p U g μ) :
    MemLpLoc p U (f + g) μ := fun K hK hc => (hf K hK hc).add (hg K hK hc)

/-- Local `Lᵖ` membership is closed under negation. -/
theorem MemLpLoc.neg (hf : MemLpLoc p U f μ) : MemLpLoc p U (-f) μ :=
  fun K hK hc => (hf K hK hc).neg

/-- Local `Lᵖ` membership is closed under subtraction. -/
theorem MemLpLoc.sub (hf : MemLpLoc p U f μ) (hg : MemLpLoc p U g μ) :
    MemLpLoc p U (f - g) μ := fun K hK hc => (hf K hK hc).sub (hg K hK hc)

/-- A function continuous on `U` is locally `Lᵖ` there, with no global bound required. -/
theorem _root_.ContinuousOn.memLpLoc [T2Space E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (hf : ContinuousOn f U) : MemLpLoc p U f μ :=
  fun _K hK hc => (hf.mono hK).memLp_restrict_of_subset_isCompact
    hc hc.measurableSet subset_rfl p

/-- Every constant function is locally `Lᵖ` for all exponents, including infinity. -/
@[simp]
theorem memLpLoc_const [IsFiniteMeasureOnCompacts μ] (c : F) : MemLpLoc p U (fun _ : E => c) μ :=
  fun _ _ hc =>
    have : IsFiniteMeasure (μ.restrict _) := ⟨by simpa using hc.measure_lt_top⟩
    memLp_const c

/-- A locally `Lᵖ` function on a locally closed set is locally integrable when `1 ≤ p`.
This supplies the local integrability hypothesis used by the weak-derivative API. -/
theorem MemLpLoc.locallyIntegrableOn [LocallyCompactSpace E] [IsFiniteMeasureOnCompacts μ]
    (hf : MemLpLoc p U f μ) (hp : 1 ≤ p) (hU : IsLocallyClosed U) :
    LocallyIntegrableOn f U μ :=
  (locallyIntegrableOn_iff hU).2 fun K hK hc =>
    memLp_one_iff_integrable.1 ((hf.mono_exponent hp) K hK hc)

/-- On a locally closed set, local `L¹` membership is exactly local integrability. -/
theorem memLpLoc_one_iff_locallyIntegrableOn [LocallyCompactSpace E] (hU : IsLocallyClosed U) :
    MemLpLoc 1 U f μ ↔ LocallyIntegrableOn f U μ :=
  ⟨fun hf => (locallyIntegrableOn_iff hU).2 fun K hK hc =>
      memLp_one_iff_integrable.1 (hf K hK hc),
    fun hf _K hK hc => memLp_one_iff_integrable.2 (hf.integrableOn_compact_subset hK hc)⟩

/-- A finite sum of locally `Lᵖ` functions is locally `Lᵖ`, without a completeness assumption. -/
theorem MemLpLoc.sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, MemLpLoc p U (f i) μ) : MemLpLoc p U (fun z => ∑ i ∈ s, f i z) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using (memLpLoc_zero (p := p) (U := U) (μ := μ))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Real scalar multiplication preserves local `Lᵖ` membership. -/
theorem MemLpLoc.const_smul (hf : MemLpLoc p U f μ) (c : ℝ) : MemLpLoc p U (c • f) μ :=
  fun K hK hc => (hf K hK hc).const_smul c

/-- A continuous linear map on the codomain preserves local `Lᵖ` membership. -/
theorem MemLpLoc.clm_comp (hf : MemLpLoc p U f μ) (A : F →L[ℝ] G) :
    MemLpLoc p U (fun z => A (f z)) μ :=
  fun K hK hc => A.comp_memLp' (hf K hK hc)

/-- Multiplying a fixed vector in any real normed space by a locally `Lᵖ` scalar function gives a
locally `Lᵖ` vector-valued function, with no basis or separability assumption on the target. -/
theorem MemLpLoc.smul_const {a : E → ℝ} (ha : MemLpLoc p U a μ) (v : F) :
    MemLpLoc p U (fun x => a x • v) μ :=
  ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- Pairing two locally `Lᵖ` fields of continuous linear maps into their product map preserves
local `Lᵖ` membership. -/
theorem MemLpLoc.clm_prod {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {A : E → E' →L[ℝ] F} {B : E → E' →L[ℝ] G} (hA : MemLpLoc p U A μ) (hB : MemLpLoc p U B μ) :
    MemLpLoc p U (fun z => (A z).prod (B z)) μ := by
  convert (hA.clm_comp (ContinuousLinearMap.compL ℝ E' F (F × G)
    (ContinuousLinearMap.inl ℝ F G))).add
      (hB.clm_comp (ContinuousLinearMap.compL ℝ E' G (F × G) (ContinuousLinearMap.inr ℝ F G)))
    using 1
  funext z
  ext v <;> simp

/-- Composing a locally `Lᵖ` operator family on the left with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_clm_comp [T2Space E] [OpensMeasurableSpace E]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : E → G →L[ℝ] H} {B : E → F →L[ℝ] G} (hB : MemLpLoc p U B μ) (hA : ContinuousOn A U) :
    MemLpLoc p U (fun z => A z ∘L B z) μ :=
  memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 hB K hKU hK).clm_comp_of_continuousOn
    (hA.mono hKU) hK hK.measurableSet subset_rfl

/-- Composing a locally `Lᵖ` operator family on the right with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_comp_continuousOn [T2Space E] [OpensMeasurableSpace E]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {B : E → G →L[ℝ] H} {A : E → F →L[ℝ] G} (hB : MemLpLoc p U B μ) (hA : ContinuousOn A U) :
    MemLpLoc p U (fun z => B z ∘L A z) μ :=
  memLpLoc_iff.2 fun K hKU hK => (ContinuousLinearMap.compL ℝ F G H).memLp_of_bilin p
    (memLpLoc_iff.1 hB K hKU hK)
    ((hA.mono hKU).memLp_top_restrict_of_subset_isCompact hK hK.measurableSet subset_rfl)

/-- **Hölder's inequality on compact subsets**: a locally `Lᵖ` field of continuous linear maps
applied to a locally `L^q` field is locally integrable on a locally closed set when
`1/p + 1/q ≤ 1`. -/
theorem MemLpLoc.locallyIntegrableOn_clm_apply [LocallyCompactSpace E]
    [IsFiniteMeasureOnCompacts μ] {A : E → F →L[ℝ] G} {w : E → F}
    (hA : MemLpLoc p U A μ) (hw : MemLpLoc q U w μ) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hU : IsLocallyClosed U) : LocallyIntegrableOn (fun z => A z (w z)) U μ := by
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  exact MemLpLoc.locallyIntegrableOn
    (fun K hK hc => (ContinuousLinearMap.id ℝ (F →L[ℝ] G)).memLp_of_bilin _ (hA K hK hc)
      (hw K hK hc))
    (ENNReal.one_le_inv.2 hpq) hU

open TauCeti.MeasureTheory in
/-- A locally `Lᵖ` function on an open set `Ω`, with `1 ≤ p`, agrees almost everywhere on `Ω` with
its precise representative. -/
theorem MemLpLoc.ae_eq_preciseRepresentative {X : Type*} [PseudoMetricSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ]
    [CompleteSpace F] {Ω : Opens X} {f : X → F} (hp : 1 ≤ p) (hu : MemLpLoc p Ω f μ) :
    f =ᵐ[μ.restrict Ω] preciseRepresentative μ f :=
  ae_eq_restrict_preciseRepresentative Ω.isOpen
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)

/-- A continuous linear change of codomain preserves and reflects local `Lᵖ` membership. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memLpLoc_iff (e : F ≃L[ℝ] G) :
    MemLpLoc p U (fun z => e (f z)) μ ↔ MemLpLoc p U f μ := by
  constructor
  · intro h
    simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
      h.clm_comp e.symm.toContinuousLinearMap
  · exact fun h => h.clm_comp e.toContinuousLinearMap

/-- A factor continuous on `U` preserves local `Lᵖ` membership on `U`, since it is bounded on
every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_smul [T2Space E] [OpensMeasurableSpace E]
    {χ : E → ℝ} (hf : MemLpLoc p U f μ) (hχ : ContinuousOn χ U) :
    MemLpLoc p U (fun z => χ z • f z) μ :=
  memLpLoc_iff.2 fun K hK hc =>
    ((hχ.mono hK).memLp_top_restrict_of_subset_isCompact hc hc.measurableSet subset_rfl).smul
      (memLpLoc_iff.1 hf K hK hc)

/-- A locally `Lᵖ` field of continuous linear maps applied to a map continuous on `U` is locally
`Lᵖ` on `U`, since the map is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_apply_continuousOn [T2Space E] [OpensMeasurableSpace E]
    {A : E → F →L[ℝ] G} (hA : MemLpLoc p U A μ) (hf : ContinuousOn f U) :
    MemLpLoc p U (fun z => A z (f z)) μ :=
  memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 hA K hK hc).of_bilin (fun B x => B x) 1
      ((hf.mono hK).memLp_top_restrict_of_subset_isCompact hc hc.measurableSet subset_rfl)
      isBoundedBilinearMap_apply.continuous
      (.of_forall fun z => by simpa using (A z).le_opNNNorm (f z))

/-- A continuous factor supported in `U` extends a local `Lᵖ` function on `U` by zero to a local
`Lᵖ` function on the whole space: on a compact set `K` the product only sees
`K ∩ tsupport χ`, a compact subset of `U`. -/
theorem MemLpLoc.continuous_smul_of_tsupport_subset [T2Space E] [OpensMeasurableSpace E]
    {χ : E → ℝ} (hf : MemLpLoc p U f μ)
    (hχ : Continuous χ) (hsupp : tsupport χ ⊆ U) :
    MemLpLoc p Set.univ (fun z => χ z • f z) μ := by
  have hT := hf.continuousOn_smul hχ.continuousOn
  have hcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have heq : (fun z => χ z • f z) = (tsupport χ).indicator (fun z => χ z • f z) := by
    refine (Set.indicator_eq_self.2 ?_).symm
    exact (Function.support_smul_subset_left χ f).trans (subset_tsupport χ)
  rw [heq, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet,
    Measure.restrict_restrict hcl.measurableSet]
  exact memLpLoc_iff.1 hT _ (Set.inter_subset_left.trans hsupp) (hK.inter_left hcl)

/-- A continuous compactly supported factor whose support meets the closed set `T` inside `S`
makes a function in `MemLpLoc 1 S` integrable on `T`, even though `T` may be unbounded or leave
`S`. -/
theorem MemLpLoc.integrableOn_smul [T2Space E] [OpensMeasurableSpace E]
    {S T : Set E} {h : E → F} (hh : MemLpLoc 1 S h μ)
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hT : IsClosed T)
    (hfS : tsupport f ∩ T ⊆ S) : IntegrableOn (fun z => f z • h z) T μ := by
  have hK : IsCompact (tsupport f ∩ T) := hfc.isCompact.inter_right hT
  have hhK : IntegrableOn h (tsupport f ∩ T) μ :=
    memLp_one_iff_integrable.1 (hh _ hfS hK)
  refine (hhK.continuousOn_smul hf.continuousOn hK).of_forall_sdiff_eq_zero hT.measurableSet
    fun z hz => ?_
  simp [image_eq_zero_of_notMem_tsupport fun h => hz.2 ⟨h, hz.1⟩]

end MemLpLocNormed

/-! ### Local `Lᵖ` on planar half-discs -/

section PlanarHalfPlane

variable {F : Type*} [NormedAddCommGroup F] {p : ENNReal} {f : ℂ → F}

/-- **Local `Lᵖ` on a half-disc through upper halves.** A function is locally `Lᵖ` on
`Ω ∩ {0 ≤ im}`, up to the real axis, exactly when it is `Lᵖ` on the upper half `W ∩ {0 < im}` of
every open `W` whose closure is compact and contained in `Ω`. The real axis is null, so the
compact sets reaching it see no more than these upper halves. -/
theorem memLpLoc_inter_setOf_im_nonneg_iff {Ω : Opens ℂ} :
    MemLpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) f ↔
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        MemLp f p (volume.restrict (W.upperHalf : Set ℂ)) := by
  refine ⟨fun hf W hWc hWΩ => ?_, fun h => memLpLoc_iff.2 fun K hKU hK => ?_⟩
  · have hK : IsCompact (closure (W : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) :=
      hWc.inter_right (isClosed_le continuous_const Complex.continuous_im)
    refine (memLpLoc_iff.1 hf _ (Set.inter_subset_inter_left _ hWΩ) hK).mono_measure
      (Measure.restrict_mono ?_ le_rfl)
    intro z hz
    obtain ⟨hzW, hz0⟩ := Opens.mem_upperHalf.1 hz
    exact ⟨subset_closure hzW, hz0.le⟩
  · obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen
      (hKU.trans Set.inter_subset_left)
    refine (h ⟨W, hWo⟩ hWc hWΩ).mono_measure (Measure.restrict_mono_ae ?_)
    filter_upwards [(Complex.setOf_le_im_ae_eq 0).subset] with z hz hzK
    exact Opens.mem_upperHalf.2 ⟨hKW hzK, hz (hKU hzK).2⟩

end PlanarHalfPlane

/-! ### Local Sobolev classes `MemWkpLoc` -/

universe u v w

section MemWkpLoc

variable {E : Type u} {F : Type v} {G : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p q : ENNReal} {U V : Set E} {Ω : Opens E} {k l : ℕ} {f g : E → F} {μ ν : Measure E}

/-- Auxiliary recursion for `MemWkpLoc` with codomain in `Type max u v`, so that passing from
`F` to `E →L[ℝ] F` stays in the same universe. -/
private def MemWkpLocAux (p : ENNReal) (U : Set E) :
    (k : ℕ) → {F : Type max u v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (E → F) →
    Measure E → Prop
  | 0, _, _, _, f, μ => MemLpLoc p U f μ
  | k + 1, F, _, _, f, μ => MemLpLoc p U f μ ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧ MemWkpLocAux p U k D μ

private theorem memWkpLocAux_congr_univ :
    ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F},
      MemWkpLocAux.{u, max u v} p U k f μ ↔ MemWkpLocAux.{u, v} p U k f μ
  | 0, _, _, _, _ => Iff.rfl
  | k + 1, _, _, _, _ => and_congr_right fun _ => exists_congr fun _ =>
      and_congr_right fun _ => memWkpLocAux_congr_univ k

/-- The iterated weak derivatives through order `k` exist on `interior U` and are `Lᵖ` on
every compact subset of `U`, including compact sets reaching its boundary.
The first derivative takes values in `E →L[ℝ] F`; higher derivatives iterate this construction.
No integrability at infinity or boundary trace is required. -/
def MemWkpLoc (p : ENNReal) (U : Set E) :
    (k : ℕ) → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (E → F) →
    (μ : Measure E := by volume_tac) → Prop
  | 0, _, _, _, f, μ => MemLpLoc p U f μ
  | k + 1, F, _, _, f, μ => MemLpLoc p U f μ ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧
        MemWkpLocAux.{u, v} p U k D μ

private theorem memWkpLoc_iff_aux {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} :
    MemWkpLoc.{u, max u v} p U k f μ ↔ MemWkpLocAux.{u, v} p U k f μ := by
  cases k with
  | zero => exact Iff.rfl
  | succ k => exact and_congr_right fun _ => exists_congr fun _ =>
      and_congr_right fun _ => memWkpLocAux_congr_univ k

/-- At order zero the local Sobolev class is exactly the local `Lᵖ` class. -/
@[simp]
theorem memWkpLoc_zero_iff : MemWkpLoc p U 0 f μ ↔ MemLpLoc p U f μ := Iff.rfl

/-- The successor-order characterization supplies a weak derivative in the preceding class. -/
theorem memWkpLoc_succ_iff : MemWkpLoc p U (k + 1) f μ ↔ MemLpLoc p U f μ ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧
      MemWkpLoc p U k D μ :=
  and_congr_right fun _ => exists_congr fun _ =>
    and_congr_right fun _ => memWkpLoc_iff_aux.symm

/-- On an open domain, the successor-order weak derivative is tested on the domain itself. -/
theorem memWkpLoc_succ_iff_of_isOpen : MemWkpLoc p Ω (k + 1) f μ ↔ MemLpLoc p Ω f μ ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ MemWkpLoc p Ω k D μ := by
  simp only [memWkpLoc_succ_iff, Opens.interior_coe]

/-- At order one, local Sobolev membership is local `Lᵖ` membership of the function and of a weak
derivative on the interior. -/
theorem memWkpLoc_one_iff : MemWkpLoc p U 1 f μ ↔ MemLpLoc p U f μ ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧ MemLpLoc p U D μ := Iff.rfl

/-- On an open domain, order-one local Sobolev membership is local `Lᵖ` membership of the function
and of a weak derivative on that domain. -/
theorem memWkpLoc_one_iff_of_isOpen : MemWkpLoc p Ω 1 f μ ↔ MemLpLoc p Ω f μ ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ MemLpLoc p Ω D μ := by
  simp only [memWkpLoc_one_iff, Opens.interior_coe]

/-- Every local Sobolev function is locally `Lᵖ`. -/
theorem MemWkpLoc.memLpLoc (hf : MemWkpLoc p U k f μ) : MemLpLoc p U f μ := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

/-- A positive-order local Sobolev function has a weak derivative of the preceding order. -/
theorem MemWkpLoc.exists_weakFDeriv (hf : MemWkpLoc p U (k + 1) f μ) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧
      MemWkpLoc p U k D μ := (memWkpLoc_succ_iff.1 hf).2

/-- On an open domain, positive-order membership gives a weak derivative on that domain. -/
theorem MemWkpLoc.exists_weakFDeriv_of_isOpen (hf : MemWkpLoc p Ω (k + 1) f μ) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ MemWkpLoc p Ω k D μ :=
  (memWkpLoc_succ_iff_of_isOpen.mp hf).2

/-- Positive-order membership retains the completeness required by weak derivatives. -/
theorem MemWkpLoc.completeSpace (hf : MemWkpLoc p U (k + 1) f μ) : CompleteSpace F := by
  obtain ⟨D, hD, _⟩ := hf.exists_weakFDeriv
  exact hD.completeSpace

/-- Restriction preserves the interior weak derivatives and the bounds on compact subsets. -/
theorem MemWkpLoc.mono (hf : MemWkpLoc p U k f μ) (hVU : V ⊆ U) :
    MemWkpLoc p V k f μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F},
      MemWkpLoc p U k f μ → MemWkpLoc p V k f μ := by
    intro k
    induction k with
    | zero => exact fun hf => hf.mono_set hVU
    | succ k ih =>
      intro F _ _ f hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), ih hk⟩
  cases k with
  | zero => exact hf.mono_set hVU
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), aux k hk⟩

/-- Almost-everywhere changes of the function preserve its local Sobolev class. -/
theorem MemWkpLoc.congr_ae (hf : MemWkpLoc p U k f μ)
    (hfg : f =ᵐ[μ.restrict U] g) : MemWkpLoc p U k g μ := by
  cases k with
  | zero => exact hf.congr_ae hfg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.congr_ae hfg, D,
      hD.congr_ae (ae_mono (Measure.restrict_mono_set μ interior_subset) hfg), hk⟩

/-- Restricting to a subset preserves the local Sobolev class of any function agreeing with the
original one on that subset. -/
theorem MemWkpLoc.congr_mono [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hgf : Set.EqOn g f V) (hVU : V ⊆ U) :
    MemWkpLoc p V k g μ := by
  cases k with
  | zero => exact MemLpLoc.congr_mono hf hgf hVU
  | succ k =>
    obtain ⟨-, D, hD, hk⟩ := memWkpLoc_succ_iff.1 (hf.mono hVU)
    exact memWkpLoc_succ_iff.2 ⟨hf.memLpLoc.congr_mono hgf hVU, D, hD.congr_ae <| by
      filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz using
        (hgf (interior_subset hz)).symm, hk⟩

/-- The local Sobolev class only depends on the values on the set. -/
theorem MemWkpLoc.congr [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hgf : Set.EqOn g f U) : MemWkpLoc p U k g μ :=
  hf.congr_mono hgf subset_rfl

/-- Every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in `MemWkpLoc p Ω k`, not only
the one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memWkpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω (k + 1) f μ) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn μ Ω f D) :
    MemWkpLoc p Ω k D μ := by
  obtain ⟨D', hD', hD'k⟩ := hf.exists_weakFDeriv_of_isOpen
  exact hD'k.congr_ae (hD'.ae_eq hD)

/-- Every weak derivative of a member of `MemWkpLoc p Ω 1` is locally `Lᵖ` on `Ω`, not only the
one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memLpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω 1 f μ) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn μ Ω f D) :
    MemLpLoc p Ω D μ :=
  memWkpLoc_zero_iff.1 (hf.memWkpLoc_of_hasWeakFDerivOn hD)

/-- Decreasing the integrability exponent preserves each local derivative order. -/
theorem MemWkpLoc.mono_exponent [IsFiniteMeasureOnCompacts μ] (hf : MemWkpLoc p U k f μ)
    (hqp : q ≤ p) : MemWkpLoc q U k f μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F},
      MemWkpLoc p U k f μ → MemWkpLoc q U k f μ := by
    intro k
    induction k with
    | zero => exact fun hf => MemLpLoc.mono_exponent hf hqp
    | succ k ih =>
      intro F _ _ f hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.mono_exponent hqp, D, hD, ih hk⟩
  cases k with
  | zero => exact MemLpLoc.mono_exponent hf hqp
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_exponent hqp, D, hD, aux k hk⟩

/-- Dropping the top derivative preserves local Sobolev membership. -/
theorem MemWkpLoc.of_succ (hf : MemWkpLoc p U (k + 1) f μ) : MemWkpLoc p U k f μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F},
      MemWkpLoc p U (k + 1) f μ → MemWkpLoc p U k f μ := by
    intro k
    induction k with
    | zero => exact fun hf => hf.memLpLoc
    | succ k ih =>
      intro F _ _ f hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp, D, hD, ih hk⟩
  cases k with
  | zero => exact hf.memLpLoc
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp, D, hD, aux k hk⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLoc.of_le (hf : MemWkpLoc p U k f μ) (hlk : l ≤ k) : MemWkpLoc p U l f μ := by
  induction hlk with
  | refl => exact hf
  | step _ ih => exact ih hf.of_succ

/-- Multiplying the measure by a finite constant preserves every local Sobolev class. -/
theorem MemWkpLoc.smul_measure (hf : MemWkpLoc p U k f μ) {c : ENNReal} (hc : c ≠ ⊤) :
    MemWkpLoc p U k f (c • μ) := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F},
      MemWkpLoc p U k f μ → MemWkpLoc p U k f (c • μ) := by
    intro k
    induction k with
    | zero => exact fun hf => MemLpLoc.smul_measure hf hc
    | succ k ih =>
      intro F _ _ f hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.smul_measure hc, D, hD.smul_measure hc, ih hk⟩
  cases k with
  | zero => exact MemLpLoc.smul_measure hf hc
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.smul_measure hc, D, hD.smul_measure hc, aux k hk⟩

/-- Multiplying the measure by a finite nonzero constant leaves every local Sobolev class
unchanged. -/
theorem memWkpLoc_smul_measure_iff {c : ENNReal} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    MemWkpLoc p U k f (c • μ) ↔ MemWkpLoc p U k f μ := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have h' := h.smul_measure (ENNReal.inv_ne_top.2 hc0)
  rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] at h'

/-- Local Sobolev membership with respect to an additive Haar measure passes to every
translation-invariant measure finite on compact sets. -/
theorem MemWkpLoc.of_isAddLeftInvariant [LocallyCompactSpace E] [SecondCountableTopology E]
    [BorelSpace E] [μ.IsAddHaarMeasure] (ν : Measure E) [IsFiniteMeasureOnCompacts ν]
    [ν.IsAddLeftInvariant] (hf : MemWkpLoc p U k f μ) : MemWkpLoc p U k f ν := by
  rw [Measure.isAddLeftInvariant_eq_smul ν μ]
  exact hf.smul_measure ENNReal.coe_ne_top

/-- **Haar-measure independence of local Sobolev classes.** Any two additive Haar measures on a
locally compact second-countable real normed space define the same local Sobolev classes of every
order. -/
theorem memWkpLoc_iff_of_isAddHaarMeasure [LocallyCompactSpace E] [SecondCountableTopology E]
    [BorelSpace E] [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    MemWkpLoc p U k f μ ↔ MemWkpLoc p U k f ν :=
  ⟨fun h => h.of_isAddLeftInvariant ν, fun h => h.of_isAddLeftInvariant μ⟩

/-- The zero function lies in every local Sobolev class with complete codomain. -/
@[simp]
theorem memWkpLoc_zero_fun [CompleteSpace F] : MemWkpLoc p U k (0 : E → F) μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F], MemWkpLoc p U k (0 : E → F) μ := by
    intro k
    induction k with
    | zero => exact memLpLoc_zero
    | succ k ih => exact memWkpLoc_succ_iff.2 ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, ih⟩
  cases k with
  | zero => exact memLpLoc_zero
  | succ k => exact memWkpLoc_succ_iff.2 ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, aux k⟩

/-- Local Sobolev membership is closed under addition. -/
theorem MemWkpLoc.add [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hg : MemWkpLoc p U k g μ) : MemWkpLoc p U k (f + g) μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F},
      MemWkpLoc p U k f μ → MemWkpLoc p U k g μ → MemWkpLoc p U k (f + g) μ := by
    intro k
    induction k with
    | zero => exact fun hf hg => MemLpLoc.add hf hg
    | succ k ih =>
      intro F _ _ f g hf hg
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      obtain ⟨hq, D', hD', hk'⟩ := memWkpLoc_succ_iff.1 hg
      exact memWkpLoc_succ_iff.2 ⟨hp.add hq, D + D', hD.add hD', ih hk hk'⟩
  cases k with
  | zero => exact MemLpLoc.add hf hg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    obtain ⟨hq, D', hD', hk'⟩ := memWkpLoc_succ_iff.1 hg
    exact memWkpLoc_succ_iff.2 ⟨hp.add hq, D + D', hD.add hD', aux k hk hk'⟩

/-- Local Sobolev membership is closed under negation. -/
theorem MemWkpLoc.neg (hf : MemWkpLoc p U k f μ) : MemWkpLoc p U k (-f) μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F},
      MemWkpLoc p U k f μ → MemWkpLoc p U k (-f) μ := by
    intro k
    induction k with
    | zero => exact fun hf => MemLpLoc.neg hf
    | succ k ih =>
      intro F _ _ f hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.neg, -D, hD.neg, ih hk⟩
  cases k with
  | zero => exact MemLpLoc.neg hf
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.neg, -D, hD.neg, aux k hk⟩

/-- Local Sobolev membership is closed under subtraction. -/
theorem MemWkpLoc.sub [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hg : MemWkpLoc p U k g μ) : MemWkpLoc p U k (f - g) μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Real scalar multiplication preserves local Sobolev membership. -/
theorem MemWkpLoc.const_smul (hf : MemWkpLoc p U k f μ) (c : ℝ) :
    MemWkpLoc p U k (c • f) μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F},
      MemWkpLoc p U k f μ → MemWkpLoc p U k (c • f) μ := by
    intro k
    induction k with
    | zero => exact fun hf => MemLpLoc.const_smul hf c
    | succ k ih =>
      intro F _ _ f hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.const_smul c, c • D, hD.const_smul c, ih hk⟩
  cases k with
  | zero => exact MemLpLoc.const_smul hf c
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.const_smul c, c • D, hD.const_smul c, aux k hk⟩

/-- Continuous linear maps of the codomain preserve all local weak derivative orders. -/
theorem MemWkpLoc.clm_comp [OpensMeasurableSpace E] [CompleteSpace G] (hf : MemWkpLoc p U k f μ)
    (A : F →L[ℝ] G) : MemWkpLoc p U k (fun z => A (f z)) μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} {G : Type max u w} [NormedAddCommGroup F]
      [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {f : E → F} (A : F →L[ℝ] G),
      MemWkpLoc p U k f μ → MemWkpLoc p U k (fun z => A (f z)) μ := by
    intro k
    induction k with
    | zero => exact fun A hf => MemLpLoc.clm_comp hf A
    | succ k ih =>
      intro F G _ _ _ _ _ f A hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
        ih ((ContinuousLinearMap.compL ℝ E F G) A) hk⟩
  cases k with
  | zero => exact MemLpLoc.clm_comp hf A
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
      aux k ((ContinuousLinearMap.compL ℝ E F G) A) hk⟩

/-- Multiplying a fixed vector in any real Banach space by a local Sobolev scalar function gives a
local Sobolev vector-valued function of the same order, with no basis or separability assumption
on the target. -/
theorem MemWkpLoc.smul_const [OpensMeasurableSpace E] [CompleteSpace F] {a : E → ℝ}
    (ha : MemWkpLoc p U k a μ) (v : F) : MemWkpLoc p U k (fun x => a x • v) μ :=
  ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- **Pairs of local Sobolev maps.** Two maps in the local Sobolev class of order `k` pair to a map
in the same class, with values in the product. -/
theorem MemWkpLoc.prodMk [OpensMeasurableSpace E] [CompleteSpace F] [CompleteSpace G] {g : E → G}
    (hf : MemWkpLoc p U k f μ) (hg : MemWkpLoc p U k g μ) :
    MemWkpLoc p U k (fun z => (f z, g z)) μ := by
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext z <;> simp

/-- **Products of operator fields.** If two fields of continuous linear maps are in the local
Sobolev class of order `k`, so is their pointwise product map `(A z).prodMap (B z)`. -/
theorem MemWkpLoc.prodMap [OpensMeasurableSpace E] {E₁ E₂ E₃ E₄ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄]
    [CompleteSpace E₄] {A : E → E₁ →L[ℝ] E₂} {B : E → E₃ →L[ℝ] E₄} (hA : MemWkpLoc p U k A μ)
    (hB : MemWkpLoc p U k B μ) : MemWkpLoc p U k (fun z => (A z).prodMap (B z)) μ := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.prodMapL ℝ E₁ E₂ E₃ E₄)

/-- A continuous linear change of codomain preserves and reflects every local weak
Sobolev order. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memWkpLoc_iff [OpensMeasurableSpace E] (e : F ≃L[ℝ] G) :
    MemWkpLoc p U k (fun z => e (f z)) μ ↔ MemWkpLoc p U k f μ := by
  cases k with
  | zero =>
    simpa only [memWkpLoc_zero_iff] using
      (e.comp_memLpLoc_iff (p := p) (U := U) (f := f) (μ := μ))
  | succ k =>
    constructor
    · intro h
      have : CompleteSpace G := h.completeSpace
      have : CompleteSpace F :=
        (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
      simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
        h.clm_comp e.symm.toContinuousLinearMap
    · intro h
      have : CompleteSpace F := h.completeSpace
      have : CompleteSpace G :=
        (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mp inferInstance
      exact h.clm_comp e.toContinuousLinearMap

/-- Finite sums of local Sobolev functions remain in the same class. -/
theorem MemWkpLoc.sum [OpensMeasurableSpace E] {ι : Type*} [CompleteSpace F] (s : Finset ι)
    {f : ι → E → F} (hf : ∀ i ∈ s, MemWkpLoc p U k (f i) μ) :
    MemWkpLoc p U k (fun z => ∑ i ∈ s, f i z) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using
      (memWkpLoc_zero_fun (p := p) (U := U) (k := k) (F := F) (μ := μ))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- For a continuous function on `U`, local `Lᵖ` membership is automatic, so membership in
`MemWkpLoc p U (k + 1)` is equivalent to having a weak derivative on `interior U` in
`MemWkpLoc p U k`. -/
theorem _root_.ContinuousOn.memWkpLoc_succ_iff [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (hf : ContinuousOn f U) :
    MemWkpLoc p U (k + 1) f μ ↔
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧ MemWkpLoc p U k D μ :=
  ⟨fun h => (TauCeti.memWkpLoc_succ_iff.1 h).2,
    fun h => TauCeti.memWkpLoc_succ_iff.2 ⟨hf.memLpLoc, h⟩⟩

/-- For a continuous function on `U`, membership in `MemWkpLoc p U 1` is equivalent to having a
locally `Lᵖ` weak derivative on `interior U`. -/
theorem _root_.ContinuousOn.memWkpLoc_one_iff [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (hf : ContinuousOn f U) :
    MemWkpLoc p U 1 f μ ↔
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧ MemLpLoc p U D μ :=
  hf.memWkpLoc_succ_iff

/-- For a continuous function on an open set `Ω`, membership in `MemWkpLoc p Ω 1` is equivalent to
having a locally `Lᵖ` weak derivative on `Ω`. -/
theorem _root_.ContinuousOn.memWkpLoc_one_iff_of_isOpen [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (hf : ContinuousOn f Ω) :
    MemWkpLoc p Ω 1 f μ ↔ ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ MemLpLoc p Ω D μ := by
  simpa only [Opens.interior_coe] using hf.memWkpLoc_one_iff (p := p) (μ := μ)

section Haar

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

/-- Constant functions belong to every local Sobolev class. -/
@[simp]
theorem memWkpLoc_const [CompleteSpace F] (c : F) : MemWkpLoc p U k (fun _ : E => c) μ := by
  cases k with
  | zero => exact memLpLoc_const c
  | succ k =>
    refine memWkpLoc_succ_iff.2 ⟨memLpLoc_const c, 0, ?_, memWkpLoc_zero_fun⟩
    apply hasWeakFDerivOn_iff.mpr
    exact fun v => hasWeakLineDerivOn_const (μ := μ) (Ω := Opens.interior U) (v := v) c

/-- A function differentiable on an open set `Ω` whose classical derivative is locally integrable
and locally `Lᵖ` on `Ω` lies in `MemWkpLoc p Ω 1`, with weak derivative `fderiv ℝ f`. -/
theorem _root_.DifferentiableOn.memWkpLoc_one [CompleteSpace F] (hf : DifferentiableOn ℝ f Ω)
    (hli : LocallyIntegrableOn (fderiv ℝ f) Ω μ) (hD : MemLpLoc p Ω (fderiv ℝ f) μ) :
    MemWkpLoc p Ω 1 f μ :=
  memWkpLoc_one_iff_of_isOpen.2
    ⟨hf.continuousOn.memLpLoc, fderiv ℝ f,
      hasWeakFDerivOn_of_differentiableOn hli fun _ hx =>
        hf.differentiableAt (Ω.isOpen.mem_nhds hx),
      hD⟩

/-- A function differentiable on an open set `Ω` with continuous derivative lies in
`MemWkpLoc p Ω 1` for every exponent `p`, including `0 ≤ p < 1` and `p = ∞`, with weak
derivative `fderiv ℝ f`. -/
theorem _root_.DifferentiableOn.memWkpLoc_one_of_continuousOn_fderiv [CompleteSpace F]
    (hf : DifferentiableOn ℝ f Ω) (hD : ContinuousOn (fderiv ℝ f) Ω) :
    MemWkpLoc p Ω 1 f μ :=
  hf.memWkpLoc_one (hD.locallyIntegrableOn Ω.isOpen.measurableSet) hD.memLpLoc

/-- A map that is `Cᵏ` on an open neighbourhood of `U` has locally `Lᵖ` weak derivatives
through order `k` on `U`, with bounds reaching its boundary, for every exponent. -/
theorem _root_.ContDiffOn.memWkpLoc [CompleteSpace F]
    (hf : ContDiffOn ℝ k f (Ω : Set E)) (hU : U ⊆ Ω) : MemWkpLoc p U k f μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] {f : E → F}, ContDiffOn ℝ k f (Ω : Set E) → MemWkpLoc p U k f μ := by
    intro k
    induction k with
    | zero => exact fun hf => (hf.continuousOn.mono hU).memLpLoc
    | succ k ih =>
      intro F _ _ _ f hf
      have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) :=
        hf.fderiv_of_isOpen Ω.isOpen (by simp)
      refine memWkpLoc_succ_iff.2 ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, ih hD⟩
      exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)
  cases k with
  | zero => exact (hf.continuousOn.mono hU).memLpLoc
  | succ k =>
    have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) := hf.fderiv_of_isOpen Ω.isOpen (by simp)
    refine memWkpLoc_succ_iff.2 ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, aux k hD⟩
    exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)

/-- A `Cᵏ` map on the whole space is in the local class `W^{k,p}` on every set, for every
exponent. -/
theorem _root_.ContDiff.memWkpLoc [CompleteSpace F] (hf : ContDiff ℝ k f) :
    MemWkpLoc p U k f μ :=
  hf.contDiffOn.memWkpLoc (Ω := ⊤) ((Set.subset_univ U).trans_eq Opens.coe_top.symm)

/-! ### Classical derivatives of `Cᵏ` representatives -/

/-- **The derivative of a `C¹` representative is a weak derivative.** If `g` is `C¹` on `Ω` and
agrees almost everywhere on `Ω` with `u ∈ MemWkpLoc p Ω (k + 1)`, then `fderiv ℝ g` is a weak
derivative of `u` on `Ω` and lies in `MemWkpLoc p Ω k`. By uniqueness of weak derivatives
(`TauCeti.HasWeakFDerivOn.ae_eq`), every weak derivative of `u` on `Ω` agrees with `fderiv ℝ g`
almost everywhere on `Ω`. -/
theorem MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn {u : E → F}
    (hu : MemWkpLoc p Ω (k + 1) u μ) (hg : ContDiffOn ℝ 1 g Ω) (hug : u =ᵐ[μ.restrict Ω] g) :
    HasWeakFDerivOn μ Ω u (fderiv ℝ g) ∧ MemWkpLoc p Ω k (fderiv ℝ g) μ := by
  have := hu.completeSpace
  have hg' : HasWeakFDerivOn μ Ω g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv_of_isOpen
  exact ⟨hg'.congr_ae hug.symm, hDk.congr_ae ((hD.congr_ae hug).ae_eq hg')⟩

private theorem iteratedFDeriv_succ_of_contDiffOn {m : ℕ} {u : E → F}
    (hu : MemWkpLoc p Ω (k + 1 + m) u μ) (hg : ContDiffOn ℝ (k + 1) g Ω)
    (hug : u =ᵐ[μ.restrict Ω] g)
    (hstep : ∀ D : E → E →L[ℝ] F, MemWkpLoc p Ω (k + m) D μ → ContDiffOn ℝ k D Ω →
      MemWkpLoc p Ω m (iteratedFDeriv ℝ k D) μ) :
    MemWkpLoc p Ω m (iteratedFDeriv ℝ (k + 1) g) μ := by
  rw [Nat.add_right_comm] at hu
  obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn
    (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
  have hgk : ContDiffOn ℝ k (fderiv ℝ g) Ω := hg.fderiv_of_isOpen Ω.isOpen le_rfl
  have heq : iteratedFDeriv ℝ (k + 1) g =
      fun z => (continuousMultilinearCurryRightEquiv' ℝ k E F).symm
        (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
    ext1 z
    exact iteratedFDeriv_succ_eq_comp_right
  rw [heq]
  exact (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.toContinuousLinearEquiv
    |>.comp_memWkpLoc_iff.2 (hstep _ hDk hgk)

/-- **Iterated derivatives of a `Cᵏ` representative.** If `g` is `Cᵏ` on `Ω` and agrees almost
everywhere on `Ω` with `u ∈ MemWkpLoc p Ω (k + m)`, then `iteratedFDeriv ℝ k g` lies in
`MemWkpLoc p Ω m`. No restriction on `p` is needed. -/
theorem MemWkpLoc.iteratedFDeriv_of_contDiffOn {m : ℕ} {u : E → F}
    (hu : MemWkpLoc p Ω (k + m) u μ) (hg : ContDiffOn ℝ k g Ω) (hug : u =ᵐ[μ.restrict Ω] g) :
    MemWkpLoc p Ω m (iteratedFDeriv ℝ k g) μ := by
  have aux : ∀ (k : ℕ) {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {u g : E → F},
      MemWkpLoc p Ω (k + m) u μ → ContDiffOn ℝ k g Ω → u =ᵐ[μ.restrict Ω] g →
      MemWkpLoc p Ω m (iteratedFDeriv ℝ k g) μ := by
    intro k
    induction k with
    | zero =>
      intro F _ _ u g hu _ hug
      rw [iteratedFDeriv_zero_eq_comp]
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff.2
        ((Nat.zero_add m ▸ hu).congr_ae hug)
    | succ k ih =>
      exact fun hu hg hug => iteratedFDeriv_succ_of_contDiffOn hu hg hug fun _ hD hDc =>
        ih hD hDc (Filter.EventuallyEq.refl _ _)
  cases k with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff.2
      ((Nat.zero_add m ▸ hu).congr_ae hug)
  | succ k =>
    exact iteratedFDeriv_succ_of_contDiffOn hu hg hug fun _ hD hDc =>
      aux k hD hDc (Filter.EventuallyEq.refl _ _)

end Haar

end MemWkpLoc

/-! ### Bounds for chains of weak derivatives -/

section WeakDerivChainLe

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ENNReal} {C : ENNReal} {S T : Set ℂ} {m : ℕ} {f g : ℂ → F}

/-- `WeakDerivChainLe p S T C m f g` bounds the iterated weak derivatives of `f` through order `m`
by those of `g`: the `Lᵖ(S)` norm of `f` is at most `C` times the `Lᵖ(T)` norm of `g`, and for
every weak derivative `Df` of `f` on the interior of `S` and every weak derivative `Dg` of `g` on
the interior of `T`, the pair `Df`, `Dg` satisfies the same through order `m - 1`. Since the
quantification is over all weak derivatives, the bound holds for every choice of the iterated
derivatives `D^i f` and `D^i g`, `i ≤ m`. -/
def WeakDerivChainLe (p : ENNReal) (S T : Set ℂ) (C : ENNReal) :
    (m : ℕ) → {F : Type*} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℂ → F) → (ℂ → F) →
      Prop
  | 0, _, _, _, f, g => eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T)
  | m + 1, F, _, _, f, g =>
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg

/-- At order zero the chain bound is the `Lᵖ` bound. -/
@[simp]
theorem weakDerivChainLe_zero_iff :
    WeakDerivChainLe p S T C 0 f g ↔
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) :=
  Iff.rfl

/-- At a successor order the chain bound is the `Lᵖ` bound together with the chain bound for
every pair of weak derivatives. -/
theorem weakDerivChainLe_succ_iff :
    WeakDerivChainLe p S T C (m + 1) f g ↔
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg :=
  Iff.rfl

/-- A chain bound gives the `Lᵖ` bound at order zero. -/
theorem WeakDerivChainLe.eLpNorm_le (h : WeakDerivChainLe p S T C m f g) :
    eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

/-- A chain bound passes to every pair of weak derivatives, one order lower. -/
theorem WeakDerivChainLe.weakFDeriv (h : WeakDerivChainLe p S T C (m + 1) f g)
    {Df Dg : ℂ → ℂ →L[ℝ] F} (hf : HasWeakFDerivOn volume (Opens.interior S) f Df)
    (hg : HasWeakFDerivOn volume (Opens.interior T) g Dg) : WeakDerivChainLe p S T C m Df Dg :=
  h.2 Df Dg hf hg

end WeakDerivChainLe

end TauCeti
