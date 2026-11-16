/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Topology.Algebra.Group.Quotient

import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
import TauCeti.Topology.Algebra.GroupAction.SliceChart

/-!
# Slice charts and smooth orbit trivializations for submersion quotients

Let a group `G` modelled on a normed space over a nontrivially normed field `𝕜` act on a
boundaryless manifold `M`, and suppose the orbit space `MulAction.orbitRel.Quotient G M` carries a
charted-space structure for which the orbit projection `Quotient.mk (MulAction.orbitRel G M)` is a
`C^n` submersion. This file establishes two general properties of such submersion quotients,
requiring neither freeness nor properness nor finite dimensionality:

* **Arbitrary slice charts** (`TauCeti.isLocalDiffeomorph_quotientMk_slice_of_isSubmersion`): any
  slice `σ : S → M` whose slice map `(g, s) ↦ g • σ s` is injective and a `C^n` local
  diffeomorphism on `G × U` (for an open set `U ⊆ S`) descends to a `C^n` local diffeomorphism
  `U → M ⧸ G`.
* **Smooth orbit trivializations** (`TauCeti.orbitTrivializationPartialDiffeomorph`): when `G` is a
  `C^n` Lie group acting `C^n`-smoothly on `M`, any `C^n` equivariant map `u : π⁻¹ W → G` over an
  open set `W ⊆ M ⧸ G` upgrades the topological trivialization `TauCeti.orbitTrivialization` to a
  `C^n` partial diffeomorphism `M → (M ⧸ G) × G` intertwining the `G`-action with left
  multiplication on `G`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 21.
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003, §1.
-/

public section

noncomputable section

open Function Manifold Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction G M]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace 𝕜 EQ]
  {HQ : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners 𝕜 EQ HQ}
  [ChartedSpace HQ (MulAction.orbitRel.Quotient G M)]

/-- **Transverse slices give local diffeomorphisms into any submersion quotient.** Suppose the orbit
projection `M → M ⧸ G` is a `C^n` submersion for a charted-space structure on `M ⧸ G`. For any
open subset `U` of a charted space `S` and any slice `σ : S → M` whose slice map `(g, s) ↦ g • σ s`
is injective and a `C^n` local diffeomorphism on `G × U`, the induced map `U → M ⧸ G` is a `C^n`
local diffeomorphism. -/
theorem isLocalDiffeomorph_quotientMk_slice_of_isSubmersion {n : ℕ∞ω}
    (hsubm : IsSubmersion I IQ n (Quotient.mk (MulAction.orbitRel G M)))
    {FS : Type*} [NormedAddCommGroup FS] [NormedSpace 𝕜 FS]
    {KS : Type*} [TopologicalSpace KS] {JS : ModelWithCorners 𝕜 FS KS}
    {S : Type*} [TopologicalSpace S] [ChartedSpace KS S]
    {σ : S → M} {U : TopologicalSpace.Opens S}
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ (U : Set S)))
    (hloc : IsLocalDiffeomorphOn (IG.prod JS) I n (fun p : G × S ↦ p.1 • σ p.2)
      (univ ×ˢ (U : Set S))) :
    IsLocalDiffeomorph JS IQ n
      (fun s : U ↦ Quotient.mk (MulAction.orbitRel G M) (σ s)) := by
  intro s₀
  have : Nonempty U := ⟨s₀⟩
  let φ : U → MulAction.orbitRel.Quotient G M :=
    fun s ↦ Quotient.mk (MulAction.orbitRel G M) (σ s)
  have hopen : IsOpenEmbedding φ :=
    MulAction.isOpenEmbedding_quotientMk_slice U.isOpen hinj hloc.isLocalHomeomorphOn
  -- `σ` is `C^n` on `U` as the restriction of the slice map to `{1} × U`.
  have hσ : ContMDiff JS I n (fun s : U ↦ σ s) := by
    have h1 : ContMDiff JS I n (fun s : U ↦ (1 : G) • σ s) :=
      hloc.contMDiffOn.comp_contMDiff
        (contMDiff_const.prodMk contMDiff_subtype_val) fun s ↦ ⟨mem_univ _, s.2⟩
    simpa only [one_smul] using h1
  let ψ := hopen.toOpenPartialHomeomorph φ
  have hcont_symm : ContMDiffOn IQ JS n ψ.symm ψ.target := by
    rintro _ ⟨s, -, rfl⟩
    refine ContMDiffAt.contMDiffWithinAt ?_
    -- Smoothness of `ψ.symm` at `[σ s]` is detected after precomposing with the submersion `π`.
    refine ((hsubm.isSubmersionAt (σ s)).contMDiffAt_comp_iff le_rfl).1 ?_
    obtain ⟨t, ht, -, hev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff (I := IG) (J := JS)
      U.isOpen hinj hloc contMDiffAt_id s.2 rfl
    classical
    let T : M → U := fun y ↦ if hy : t y ∈ (U : Set S) then ⟨t y, hy⟩ else s
    have hT : ContMDiffAt I JS n T (σ s) := by
      rw [← ContMDiffAt.subtypeVal_comp_iff]
      refine ht.congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      simp only [Function.comp_apply, T, hy.1, ↓reduceDIte]
    refine hT.congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    have hqt : φ ⟨t y, hy.1⟩ = Quotient.mk (MulAction.orbitRel G M) y := (hy.2 _ hy.1).2 rfl
    simp only [Function.comp_apply, T, hy.1, ↓reduceDIte, ← hqt]
    exact hopen.toOpenPartialHomeomorph_left_inv φ (x := ⟨t y, hy.1⟩)
  let Φ : PartialDiffeomorph JS IQ U (MulAction.orbitRel.Quotient G M) n :=
    { toPartialEquiv := ψ.toPartialEquiv
      open_source := ψ.open_source
      open_target := ψ.open_target
      contMDiffOn_toFun := (hsubm.contMDiff.comp hσ).contMDiffOn
      contMDiffOn_invFun := hcont_symm }
  exact Φ.isLocalDiffeomorphAt JS IQ n (mem_univ s₀)

/-- **Smooth orbit trivializations.** Let a Lie group `G` act `C^n`-smoothly on a boundaryless
manifold `M`, and suppose `Quotient.mk (MulAction.orbitRel G M) : M → M ⧸ G` is a `C^n` submersion.
Over an open set `W ⊆ M ⧸ G`, any `C^n` equivariant map `u : π⁻¹ W → G` upgrades
`TauCeti.orbitTrivialization` to a `C^n` partial diffeomorphism `M → (M ⧸ G) × G` intertwining
the `G`-action with left multiplication on `G`. -/
def orbitTrivializationPartialDiffeomorph {n : ℕ∞ω} [LieGroup IG n G] [ContMDiffSMul IG I n G M]
    (hsubm : IsSubmersion I IQ n (Quotient.mk (MulAction.orbitRel G M)))
    (W : Set (MulAction.orbitRel.Quotient G M)) (hW : IsOpen W)
    (u : M → G) (hu : ContMDiffOn I IG n u (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W))
    (hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (MulAction.orbitRel G M) ⁻¹' W, u (g • x) = g * u x) :
    PartialDiffeomorph I (IQ.prod IG) M (MulAction.orbitRel.Quotient G M × G) n :=
  haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup IG n
  haveI : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := IG) (I' := I) n
  let tr := orbitTrivialization W hW u hu.continuousOn hu_smul
  have htr_src : tr.source = Quotient.mk (MulAction.orbitRel G M) ⁻¹' W := by
    rw [tr.source_eq, orbitTrivialization_baseSet]
  have htr_tgt : tr.target = W ×ˢ univ := by
    rw [tr.target_eq, orbitTrivialization_baseSet]
  { toPartialEquiv := tr.toPartialEquiv.copy
      (fun x ↦ (Quotient.mk (MulAction.orbitRel G M) x, u x))
      (funext fun x ↦ orbitTrivialization_apply (W := W) (hW := hW) (u := u)
        (hu := hu.continuousOn) (hu_smul := hu_smul) x)
      tr.toPartialEquiv.symm rfl
      (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W) htr_src
      (W ×ˢ univ) htr_tgt
    open_source := hW.preimage hsubm.contMDiff.continuous
    open_target := hW.prod isOpen_univ
    contMDiffOn_toFun := hsubm.contMDiff.contMDiffOn.prodMk hu
    contMDiffOn_invFun := by
      -- The local section `q ↦ (u q.out)⁻¹ • q.out` is `C^n` on `W` because its pullback along the
      -- submersion `Quotient.mk` agrees with `x ↦ (u x)⁻¹ • x` on `π⁻¹ W`.
      have hsec : ContMDiffOn IQ I n
          (fun q : MulAction.orbitRel.Quotient G M ↦ (u q.out)⁻¹ • q.out) W := by
        intro q hq
        induction q using Quotient.inductionOn with
        | h x =>
          refine ContMDiffAt.contMDiffWithinAt ?_
          refine ((hsubm.isSubmersionAt x).contMDiffAt_comp_iff le_rfl).1 ?_
          have hpre : IsOpen (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W) :=
            hW.preimage hsubm.contMDiff.continuous
          have hbase : ContMDiffAt I I n (fun y : M ↦ (u y)⁻¹ • y) x :=
            (hu.inv.smul contMDiffOn_id).contMDiffAt (hpre.mem_nhds hq)
          refine hbase.congr_of_eventuallyEq ?_
          filter_upwards [hpre.mem_nhds hq] with y hy
          obtain ⟨g, hg⟩ : ∃ g : G, g • y = (Quotient.mk (MulAction.orbitRel G M) y).out :=
            MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1
              (Quotient.exact (Quotient.out_eq _)))
          rw [Function.comp_apply, ← hg, hu_smul g y hy, mul_inv_rev, mul_smul, inv_smul_smul]
      have hinv : ContMDiffOn (IQ.prod IG) I n
          (fun p : MulAction.orbitRel.Quotient G M × G ↦ p.2 • (u p.1.out)⁻¹ • p.1.out)
          (W ×ˢ univ) :=
        contMDiffOn_snd.smul (hsec.comp contMDiffOn_fst fun _ hp ↦ hp.1)
      refine hinv.congr fun p hp ↦ ?_
      have hout : Quotient.mk (MulAction.orbitRel G M) p.1.out ∈ W := by
        simpa only [Quotient.out_eq] using hp.1
      have hsymm := orbitTrivialization_symm_apply_mk (W := W) (hW := hW) (u := u)
        (hu := hu.continuousOn) (hu_smul := hu_smul) hout p.2
      rw [Quotient.out_eq, mul_smul] at hsymm
      exact hsymm }

section OrbitTrivializationPartialDiffeomorphSimp

variable {n : ℕ∞ω} [LieGroup IG n G] [ContMDiffSMul IG I n G M]
  (hsubm : IsSubmersion I IQ n (Quotient.mk (MulAction.orbitRel G M)))
  (W : Set (MulAction.orbitRel.Quotient G M)) (hW : IsOpen W)
  (u : M → G) (hu : ContMDiffOn I IG n u (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W))
  (hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (MulAction.orbitRel G M) ⁻¹' W, u (g • x) = g * u x)

/-- The source of `orbitTrivializationPartialDiffeomorph` is the preimage of `W`. -/
@[simp]
theorem orbitTrivializationPartialDiffeomorph_source :
    (orbitTrivializationPartialDiffeomorph hsubm W hW u hu hu_smul).source =
      Quotient.mk (MulAction.orbitRel G M) ⁻¹' W :=
  (rfl)

/-- The target of `orbitTrivializationPartialDiffeomorph` is `W ×ˢ univ`. -/
@[simp]
theorem orbitTrivializationPartialDiffeomorph_target :
    (orbitTrivializationPartialDiffeomorph hsubm W hW u hu hu_smul).target = W ×ˢ univ :=
  (rfl)

/-- `orbitTrivializationPartialDiffeomorph` sends `x` to `(⟦x⟧, u x)`. -/
@[simp]
theorem orbitTrivializationPartialDiffeomorph_apply (x : M) :
    orbitTrivializationPartialDiffeomorph hsubm W hW u hu hu_smul x =
      (Quotient.mk (MulAction.orbitRel G M) x, u x) :=
  (rfl)

/-- The inverse of `orbitTrivializationPartialDiffeomorph` sends `(⟦x⟧, g)` to
`(g * (u x)⁻¹) • x`. -/
@[simp]
theorem orbitTrivializationPartialDiffeomorph_symm_apply_mk {x : M}
    (hx : Quotient.mk (MulAction.orbitRel G M) x ∈ W) (g : G) :
    (orbitTrivializationPartialDiffeomorph hsubm W hW u hu hu_smul).toPartialEquiv.symm
      (Quotient.mk (MulAction.orbitRel G M) x, g) = (g * (u x)⁻¹) • x := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup IG n
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := IG) (I' := I) n
  exact orbitTrivialization_symm_apply_mk (W := W) (hW := hW) (u := u)
    (hu := hu.continuousOn) (hu_smul := hu_smul) hx g

/-- `orbitTrivializationPartialDiffeomorph` intertwines the `G`-action on `M` with left
multiplication on the fibre `G`. -/
theorem orbitTrivializationPartialDiffeomorph_apply_smul (g : G) {x : M}
    (hx : Quotient.mk (MulAction.orbitRel G M) x ∈ W) :
    orbitTrivializationPartialDiffeomorph hsubm W hW u hu hu_smul (g • x) =
      ((orbitTrivializationPartialDiffeomorph hsubm W hW u hu hu_smul x).1,
        g * (orbitTrivializationPartialDiffeomorph hsubm W hW u hu hu_smul x).2) := by
  simp only [orbitTrivializationPartialDiffeomorph_apply, hu_smul g x hx,
    MulAction.orbitRel.Quotient.quotient_smul_eq]

end OrbitTrivializationPartialDiffeomorphSimp

end TauCeti
