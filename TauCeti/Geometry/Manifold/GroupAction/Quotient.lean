/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Manifold.GroupAction.Orbit
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.Submersion.Descent
public import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.Slice
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# The quotient manifold theorem for free proper smooth Lie group actions

Let a finite-dimensional boundaryless real Lie group `G` act smoothly, freely, and properly on a
finite-dimensional boundaryless real smooth manifold `M`. Equip the orbit space
`MulAction.orbitRel.Quotient G M` with its quotient topology. Then:

1. Around every point `x : M` of trivial stabilizer, a transverse chart slice gives an open slice
   `U ⊆ ℝ^{dim M - dim G}` and a smooth map `σ : ℝ^{dim M - dim G} → M` with `σ 0 = x` whose tube
   map `(g, u) ↦ g • σ u` is injective and a smooth local diffeomorphism on `G × U`
   (`TauCeti.exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice`).
2. Gluing the open embeddings `u ↦ [σ u] : U → M ⧸ G` via
   `TauCeti.chartedSpaceOfIsOpenEmbedding` endows `MulAction.orbitRel.Quotient G M` with a named
   atlas `TauCeti.freeProperQuotientChartedSpace` modelled on
   `Fin (finrank ℝ E - finrank ℝ EG) → ℝ`, making it a smooth manifold
   (`TauCeti.isManifold_freeProperQuotient`) for which the orbit projection is a smooth submersion
   with uniform fibre complement `EG`
   (`TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
   `TauCeti.isSubmersion_quotientMk_freeProperQuotient`) whose differential at `x` has kernel equal
   to the orbit tangent space `𝔤 · x` (`TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`).
   Separation (`t2Space_quotient_mulAction_of_properSMul`) and second countability
   (`ContinuousConstSMul.secondCountableTopology`) of the quotient topology are already global
   Mathlib instances.
3. Smoothness of maps out of `M ⧸ G`, smooth descent of `G`-invariant maps and equivariant maps, and
   immersion descent follow from the surjective submersion property
   (`TauCeti.contMDiff_comp_quotientMk_freeProperQuotient_iff`,
   `TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`,
   `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`,
   `TauCeti.isImmersion_orbitRelQuotientLift_freeProperQuotient_iff`).
4. Any smooth manifold structure on `M ⧸ G` making the orbit projection a smooth submersion is
   canonically diffeomorphic to `TauCeti.freeProperQuotientChartedSpace` by the identity
   (`TauCeti.exists_diffeomorph_freeProperQuotient_apply_eq_self`), with equal maximal atlas when
   both use the standard Euclidean model (`TauCeti.maximalAtlas_freeProperQuotient_eq`). In
   particular, when `G` carries the discrete topology, the identity is a smooth diffeomorphism
   with Mathlib's covering-quotient atlas `MulAction.instChartedSpaceQuotient`
   (`TauCeti.exists_diffeomorph_freeProperQuotient_instChartedSpaceQuotient`).
5. Every orbit admits an open neighbourhood over which the orbit projection trivializes smoothly and
   `G`-equivariantly as a `Bundle.Trivialization G (Quotient.mk (MulAction.orbitRel G M))`
   (`TauCeti.exists_orbitTrivialization_freeProperQuotient`).

The atlas `TauCeti.freeProperQuotientChartedSpace` is `@[instance_reducible]` rather than a global
`instance`, since its Euclidean model `Fin (finrank ℝ E - finrank ℝ EG) → ℝ` depends on `I` and
`IG` and would otherwise compete with `MulAction.instChartedSpaceQuotient` for discrete groups.
All constructions allow `M` to be empty except `TauCeti.finrank_le_of_freeProperQuotient`.

## Main declarations

* `TauCeti.orbitTangent_le_ker_mfderiv`: a map constant along an orbit kills its orbit tangent
  space.
* `TauCeti.exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice`: smooth slice tubes around free
  points of proper actions.
* `TauCeti.freeProperQuotientChartedSpace`: the slice-glued smooth atlas on `M ⧸ G`.
* `TauCeti.isManifold_freeProperQuotient`,
  `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
  `TauCeti.isSubmersion_quotientMk_freeProperQuotient`,
  `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`: manifold structure, submersion property, and
  vertical tangent kernel of the orbit projection.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: existential form of the quotient manifold
  theorem.
* `TauCeti.contMDiff_orbitRelQuotientLift_freeProperQuotient_iff`,
  `TauCeti.contMDiff_orbitRelQuotientMap_freeProperQuotient`,
  `TauCeti.isImmersion_orbitRelQuotientLift_freeProperQuotient_iff`: smooth and immersion descent.
* `TauCeti.maximalAtlas_freeProperQuotient_eq`,
  `TauCeti.exists_diffeomorph_freeProperQuotient_apply_eq_self`,
  `TauCeti.exists_diffeomorph_freeProperQuotient_instChartedSpaceQuotient`: uniqueness and
  compatibility with discrete quotients.
* `TauCeti.exists_orbitTrivialization_freeProperQuotient`: smooth `G`-equivariant local
  trivializations of the orbit projection.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.31 and Theorem 21.10 (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto (2003),
  Theorem 1.21.
-/

public section

noncomputable section

open Function Set Filter Module Manifold Bundle Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] lieGroupOne
attribute [local instance] contMDiffSMulOneOfInfty

/-! ### Infinitesimal invariance and slice tubes at free points -/

section Infinitesimal

variable {EG HG G E H M : Type*}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M]

/-- Any map constant along the orbit of `x` annihilates the orbit tangent space `𝔤 · x` in its
manifold derivative at `x`. Differentiability of `f` at `x` is not required: when `f` is not
differentiable at `x`, `mfderiv` vanishes and its kernel is the whole tangent space. -/
theorem orbitTangent_le_ker_mfderiv {EN HN N : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {f : M → N} {x : M} (hf : ∀ g : G, f (g • x) = f x) :
    (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤ (mfderiv I J f x).ker := by
  by_cases hfd : MDifferentiableAt I J f x
  · rintro v hv
    obtain ⟨ξ, rfl⟩ := (InfinitesimalAction.mem_orbitTangent_iff _ x).1 hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, InfinitesimalAction.fundamental_apply,
      fundamentalVectorField_apply]
    have hcomp := mfderiv_comp_apply_of_eq (1 : G) hfd
      (ContMDiffSMul.mdifferentiableAt_smul_const (I := IG) (I' := I) x 1) (one_smul G x) ξ
    rw [← hcomp]
    have hconst : (f ∘ fun g : G ↦ g • x) =ᶠ[𝓝 (1 : G)] fun _ ↦ f x :=
      Eventually.of_forall hf
    rw [hconst.mfderiv_eq (I := IG) (I' := J), mfderiv_const]
    rfl
  · simp [mfderiv_zero_of_not_mdifferentiableAt hfd]

end Infinitesimal

section SliceTube

variable {EG HG G E H M : Type*}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M]

/-- At a point of trivial stabilizer on a Hausdorff manifold, the isotropy Lie subalgebra
`𝔤_x` vanishes. -/
theorem isotropy_eq_bot_of_stabilizer_eq_bot [T2Space M] {x : M}
    (hx : MulAction.stabilizer G x = ⊥) :
    haveI := FiniteDimensional.completeSpace ℝ EG
    haveI := FiniteDimensional.completeSpace ℝ E
    (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ := by
  have := FiniteDimensional.completeSpace ℝ EG
  have := FiniteDimensional.completeSpace ℝ E
  exact (isImmersion_smul_const_iff (I := IG) (I' := I)).1
    (isImmersion_smul_const_of_stabilizer_eq_bot hx)

/-- At a point of trivial stabilizer on a Hausdorff manifold, the orbit tangent space `𝔤 · x` has
the dimension of the Lie group model space `EG`. -/
theorem finrank_orbitTangent_of_stabilizer_eq_bot [T2Space M] {x : M}
    (hx : MulAction.stabilizer G x = ⊥) :
    haveI := FiniteDimensional.completeSpace ℝ EG
    haveI := FiniteDimensional.completeSpace ℝ E
    finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) = finrank ℝ EG := by
  have := FiniteDimensional.completeSpace ℝ EG
  have := FiniteDimensional.completeSpace ℝ E
  rw [(InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_of_isotropy_eq_bot x
    (isotropy_eq_bot_of_stabilizer_eq_bot hx)]
  exact finrank_tangentSpace (I := IG) (1 : G)

include IG I in
/-- If a smooth action on a Hausdorff manifold has a point of trivial stabilizer, the dimension of
the Lie group is at most the dimension of the manifold. -/
theorem finrank_le_of_stabilizer_eq_bot [T2Space M] {x : M}
    (hx : MulAction.stabilizer G x = ⊥) : finrank ℝ EG ≤ finrank ℝ E := by
  have := FiniteDimensional.completeSpace ℝ EG
  have := FiniteDimensional.completeSpace ℝ E
  calc finrank ℝ EG
      = finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) :=
        (finrank_orbitTangent_of_stabilizer_eq_bot hx).symm
    _ ≤ finrank ℝ (TangentSpace I x) := Submodule.finrank_le _
    _ = finrank ℝ E := finrank_tangentSpace x

/-- **Smooth slice tubes at free points of proper actions.** Around any point `x : M` of trivial
stabilizer under a proper smooth action of `G`, there are an open neighbourhood `U` of `0` in
`Fin (finrank ℝ E - finrank ℝ EG) → ℝ` and a smooth slice `σ` on `U` sending `0` to `x` such that
the tube map `(g, u) ↦ g • σ u` is injective and a smooth local diffeomorphism on `G × U`. -/
theorem exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice [ProperSMul G M] {x : M}
    (hx : MulAction.stabilizer G x = ⊥) :
    ∃ (U : Set (Fin (finrank ℝ E - finrank ℝ EG) → ℝ))
      (σ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M),
      IsOpen U ∧ 0 ∈ U ∧ σ 0 = x ∧
      ContMDiffOn 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞ σ U ∧
      InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
        (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  have := FiniteDimensional.completeSpace ℝ EG
  have := FiniteDimensional.completeSpace ℝ E
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  set d := finrank ℝ E - finrank ℝ EG
  let V : Submodule ℝ E := (InfinitesimalAction.fundamental IG G I M).orbitTangent x
  obtain ⟨W, hW⟩ := V.exists_isCompl
  have hVW := Submodule.finrank_sup_add_finrank_inf_eq V W
  have hVdim : finrank ℝ V = finrank ℝ EG := finrank_orbitTangent_of_stabilizer_eq_bot hx
  rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, add_zero, hVdim] at hVW
  have hWdim : finrank ℝ W = finrank ℝ (Fin d → ℝ) := by
    rw [Module.finrank_fin_fun]
    omega
  let eW : (Fin d → ℝ) ≃L[ℝ] W := (ContinuousLinearEquiv.ofFinrankEq hWdim).symm
  let τ : (Fin d → ℝ) → E := fun u ↦ extChartAt I x x + eW u
  let σ : (Fin d → ℝ) → M := fun u ↦ (extChartAt I x).symm (τ u)
  have hσ0 : σ 0 = x := by simp [σ, τ]
  have hτ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) ∞ τ :=
    (contDiff_const.add (W.subtypeL.comp eW.toContinuousLinearMap).contDiff).contMDiff
  let U₀ : Set (Fin d → ℝ) := τ ⁻¹' (extChartAt I x).target
  have hU₀ : IsOpen U₀ := (isOpen_extChartAt_target x).preimage hτ.continuous
  have h0U₀ : (0 : Fin d → ℝ) ∈ U₀ := by simp [U₀, τ]
  have hσU₀ : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I ∞ σ U₀ :=
    (contMDiffOn_extChartAt_symm x).comp hτ.contMDiffOn fun _ hu ↦ hu
  -- Transport the chart-slice local diffeomorphism from `G × W` to `G × (Fin d → ℝ)`.
  have hlocW := isLocalDiffeomorphAt_smul_extChartAt_symm (I := IG) (I' := I)
    (isotropy_eq_bot_of_stabilizer_eq_bot hx) hW
  let Φ : (G × (Fin d → ℝ)) ≃ₘ⟮IG.prod 𝓘(ℝ, Fin d → ℝ), IG.prod 𝓘(ℝ, W)⟯ (G × W) :=
    { toEquiv := (Equiv.refl G).prodCongr eW.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (eW.contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (eW.symm.contDiff.contMDiff.comp contMDiff_snd) }
  have hΦ10 : Φ (1, 0) = (1, 0) := Prod.ext rfl (map_zero eW)
  have hloc0 : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin d → ℝ)) I ∞
      (fun p : G × (Fin d → ℝ) ↦ p.1 • σ p.2) (1, 0) :=
    (Φ.isLocalDiffeomorph (1, 0)).comp (hg := hΦ10.symm ▸ hlocW)
  have hev := hloc0.eventually_forall_smul_slice
  obtain ⟨N, hN, hinjN⟩ := hloc0.exists_mem_nhds_injOn
  have hσ_cont : ContinuousAt σ 0 := (hσU₀.contMDiffAt (hU₀.mem_nhds h0U₀)).continuousAt
  obtain ⟨U₁, hU₁, hinjU₁⟩ :=
    ProperSMul.exists_mem_nhds_injOn_smul_slice hσ_cont (hσ0.symm ▸ hx) hN hinjN
  obtain ⟨U, hU_sub, hU_open, h0U⟩ :=
    mem_nhds_iff.1 (inter_mem (hU₀.mem_nhds h0U₀) (inter_mem hev hU₁))
  exact ⟨U, σ, hU_open, h0U, hσ0, hσU₀.mono fun _ hu ↦ (hU_sub hu).1,
    hinjU₁.mono (prod_mono_right fun _ hu ↦ (hU_sub hu).2.2),
    fun ⟨⟨g, _⟩, _, hu⟩ ↦ (hU_sub hu).2.1 g⟩

end SliceTube

/-! ### The quotient manifold structure -/

section QuotientManifold

variable {EG HG E H : Type*}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (IG : ModelWithCorners ℝ EG HG) (G M : Type*)
  [IG.Boundaryless] [I.Boundaryless]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

private theorem sliceTubeSpec (x : M) :
    ∃ (U : Set (Fin (finrank ℝ E - finrank ℝ EG) → ℝ))
      (σ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M),
      IsOpen U ∧ 0 ∈ U ∧ σ 0 = x ∧
      ContMDiffOn 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞ σ U ∧
      InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
        (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2) (univ ×ˢ U) :=
  exists_isOpen_injOn_isLocalDiffeomorphOn_smul_slice (IG := IG) (I := I)
    (isCancelSMul_iff_stabilizer_eq_bot.mp ‹IsCancelSMul G M› x)

private def sliceOpen (x : M) : TopologicalSpace.Opens (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) :=
  ⟨(sliceTubeSpec I IG G M x).choose, (sliceTubeSpec I IG G M x).choose_spec.choose_spec.1⟩

private def sliceMap (x : M) : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M :=
  (sliceTubeSpec I IG G M x).choose_spec.choose

private theorem zero_mem_sliceOpen (x : M) : (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈
    sliceOpen I IG G M x :=
  (sliceTubeSpec I IG G M x).choose_spec.choose_spec.2.1

private theorem sliceMap_zero (x : M) : sliceMap I IG G M x 0 = x :=
  (sliceTubeSpec I IG G M x).choose_spec.choose_spec.2.2.1

private theorem contMDiffOn_sliceMap (x : M) :
    ContMDiffOn 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞
      (sliceMap I IG G M x) (sliceOpen I IG G M x) :=
  (sliceTubeSpec I IG G M x).choose_spec.choose_spec.2.2.2.1

private theorem injOn_smul_sliceMap (x : M) :
    InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • sliceMap I IG G M x p.2)
      (univ ×ˢ sliceOpen I IG G M x) :=
  (sliceTubeSpec I IG G M x).choose_spec.choose_spec.2.2.2.2.1

private theorem isLocalDiffeomorphOn_smul_sliceMap (x : M) :
    IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
      (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • sliceMap I IG G M x p.2)
      (univ ×ˢ sliceOpen I IG G M x) :=
  (sliceTubeSpec I IG G M x).choose_spec.choose_spec.2.2.2.2.2

private def quotientPiece (x : M) (u : sliceOpen I IG G M x) : MulAction.orbitRel.Quotient G M :=
  Quotient.mk (MulAction.orbitRel G M) (sliceMap I IG G M x u)

private theorem isOpenEmbedding_quotientPiece (x : M) :
    IsOpenEmbedding (quotientPiece I IG G M x) :=
  MulAction.isOpenEmbedding_quotientMk_slice (sliceOpen I IG G M x).2
    (injOn_smul_sliceMap I IG G M x)
    (isLocalDiffeomorphOn_smul_sliceMap I IG G M x).isLocalHomeomorphOn

private theorem quotientPiece_cover (q : MulAction.orbitRel.Quotient G M) :
    ∃ (x : M) (u : sliceOpen I IG G M x), quotientPiece I IG G M x u = q :=
  Quotient.inductionOn q fun x ↦
    ⟨x, ⟨0, zero_mem_sliceOpen I IG G M x⟩, congrArg (Quotient.mk _) (sliceMap_zero I IG G M x)⟩

private theorem quotientPiece_deck (x y : M) (u : sliceOpen I IG G M x)
    (v : sliceOpen I IG G M y) (huv : quotientPiece I IG G M x u = quotientPiece I IG G M y v) :
    ∃ T : sliceOpen I IG G M x → sliceOpen I IG G M y,
      ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ T u ∧
      quotientPiece I IG G M y ∘ T =ᶠ[𝓝 u] quotientPiece I IG G M x := by
  let K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  have hf : ContMDiffAt K I ∞ (fun u' : sliceOpen I IG G M x ↦ sliceMap I IG G M x u') u :=
    ((contMDiffOn_sliceMap I IG G M x).contMDiffAt
      ((sliceOpen I IG G M x).2.mem_nhds u.2)).comp u contMDiff_subtype_val.contMDiffAt
  obtain ⟨t, ht, -, hev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff
    (sliceOpen I IG G M y).2 (injOn_smul_sliceMap I IG G M y)
    (isLocalDiffeomorphOn_smul_sliceMap I IG G M y) hf v.2 huv.symm
  classical
  let T : sliceOpen I IG G M x → sliceOpen I IG G M y :=
    fun u' ↦ if h : t u' ∈ sliceOpen I IG G M y then ⟨t u', h⟩ else v
  refine ⟨T, (ContMDiffAt.subtypeVal_comp_iff (sliceOpen I IG G M y) T u).1 ?_, ?_⟩
  · refine ht.congr_of_eventuallyEq ?_
    filter_upwards [hev] with u' hu'
    have hmem : t u' ∈ sliceOpen I IG G M y := hu'.1
    simp [T, hmem]
  · filter_upwards [hev] with u' hu'
    have hmem : t u' ∈ sliceOpen I IG G M y := hu'.1
    simp only [comp_apply, quotientPiece, T, hmem, ↓reduceDIte]
    exact (hu'.2 (t u') hu'.1).2 rfl

/-- The smooth quotient atlas on `MulAction.orbitRel.Quotient G M` for a free proper smooth action
of a Lie group `G` on `M`, glued from transverse slice embeddings into the orbit space. It is
`@[instance_reducible]` rather than a global `instance` because its model depends on `I` and `IG`
and would compete with `MulAction.instChartedSpaceQuotient` for discrete groups. -/
@[instance_reducible]
def freeProperQuotientChartedSpace :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding (H := Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
    (isOpenEmbedding_quotientPiece I IG G M) (quotientPiece_cover I IG G M)

/-- The orbit space of a free proper smooth action, equipped with
`TauCeti.freeProperQuotientChartedSpace`, is a smooth manifold of dimension
`finrank ℝ E - finrank ℝ EG`. -/
theorem isManifold_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding (isOpenEmbedding_quotientPiece I IG G M)
    (quotientPiece_cover I IG G M) (quotientPiece_deck I IG G M)

include I IG G M in
/-- If a Lie group acts freely, properly, and smoothly on a nonempty manifold `M`, then
`dim G ≤ dim M`. -/
theorem finrank_le_of_freeProperQuotient [Nonempty M] : finrank ℝ EG ≤ finrank ℝ E := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  obtain ⟨x⟩ := ‹Nonempty M›
  exact finrank_le_of_stabilizer_eq_bot (IG := IG) (I := I)
    (isCancelSMul_iff_stabilizer_eq_bot.mp ‹IsCancelSMul G M› x)

/-- The orbit projection of a free proper smooth action is smooth. -/
theorem contMDiff_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG G M
  let d := finrank ℝ E - finrank ℝ EG
  let K := 𝓘(ℝ, Fin d → ℝ)
  intro x
  let U := sliceOpen I IG G M x
  let u₀ : U := ⟨0, zero_mem_sliceOpen I IG G M x⟩
  let ψ₀ : G × (Fin d → ℝ) → M := fun p ↦ p.1 • sliceMap I IG G M x p.2
  have hψ₀ : IsLocalDiffeomorphAt (IG.prod K) I ∞ ψ₀ (1, 0) :=
    isLocalDiffeomorphOn_smul_sliceMap I IG G M x ⟨(1, 0), mem_univ _, u₀.2⟩
  have hψ₀_zero : ψ₀ (1, 0) = x := by simp [ψ₀, sliceMap_zero]
  rw [← hψ₀_zero, ← hψ₀.contMDiffAt_comp_iff le_rfl]
  have hφ_loc : IsLocalDiffeomorphAt K K ∞ (quotientPiece I IG G M x) u₀ :=
    isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding (isOpenEmbedding_quotientPiece I IG G M)
      (quotientPiece_cover I IG G M) (quotientPiece_deck I IG G M) x u₀
  classical
  let r : (Fin d → ℝ) → U := fun u ↦ if hu : u ∈ U then ⟨u, hu⟩ else u₀
  have hr0 : (r ∘ Prod.snd) ((1 : G), (0 : Fin d → ℝ)) = u₀ := by simp [r, u₀]
  have hr : ContMDiffAt K K ∞ r 0 := by
    refine (ContMDiffAt.subtypeVal_comp_iff U r 0).1 (contMDiffAt_id.congr_of_eventuallyEq ?_)
    filter_upwards [U.2.mem_nhds u₀.2] with u hu
    have hu' : u ∈ U := hu
    simp [r, hu']
  have hcomp : ContMDiffAt (IG.prod K) K ∞
      (quotientPiece I IG G M x ∘ r ∘ Prod.snd) ((1 : G), (0 : Fin d → ℝ)) :=
    hφ_loc.contMDiffAt.comp_of_eq (hr.comp ((1 : G), (0 : Fin d → ℝ)) contMDiffAt_snd) hr0
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_univ.prod U.2).mem_nhds ⟨mem_univ (1 : G), u₀.2⟩] with p hp
  have hp2 : p.2 ∈ U := hp.2
  simp [ψ₀, quotientPiece, r, hp2, MulAction.orbitRel.Quotient.quotient_smul_eq]

/-- The orbit projection of a free proper smooth action is a smooth submersion with uniform fibre
complement `EG`, the model vector space of the acting Lie group. -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    IsSubmersionOfComplement EG I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG G M
  let d := finrank ℝ E - finrank ℝ EG
  let K := 𝓘(ℝ, Fin d → ℝ)
  let qmk := Quotient.mk (MulAction.orbitRel G M)
  have hqmk := contMDiff_quotientMk_freeProperQuotient I IG G M
  rw [Manifold.isSubmersionOfComplement_iff]
  intro x
  have : Nonempty M := ⟨x⟩
  have hle_dim : finrank ℝ EG ≤ finrank ℝ E := finrank_le_of_freeProperQuotient I IG G M
  let U := sliceOpen I IG G M x
  let u₀ : U := ⟨0, zero_mem_sliceOpen I IG G M x⟩
  let f_slice : U → M := fun u ↦ sliceMap I IG G M x u
  have hf_zero : f_slice u₀ = x := sliceMap_zero I IG G M x
  have hf : ContMDiffAt K I ∞ f_slice u₀ :=
    ((contMDiffOn_sliceMap I IG G M x).contMDiffAt (U.2.mem_nhds u₀.2)).comp u₀
      contMDiff_subtype_val.contMDiffAt
  have hφ_loc : IsLocalDiffeomorphAt K K ∞ (quotientPiece I IG G M x) u₀ :=
    isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding (isOpenEmbedding_quotientPiece I IG G M)
      (quotientPiece_cover I IG G M) (quotientPiece_deck I IG G M) x u₀
  have hsurj : Surjective (mfderiv I K qmk x) := by
    have := FiniteDimensional.completeSpace ℝ E
    intro w
    obtain ⟨v, hv⟩ := (hφ_loc.mfderivToContinuousLinearEquiv (by simp)).surjective w
    refine ⟨mfderiv K I f_slice u₀ v, ?_⟩
    rw [← mfderiv_comp_apply_of_eq u₀ (hqmk.contMDiffAt.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp)) hf_zero v]
    exact hv
  let eEG : (Fin (finrank ℝ E - finrank ℝ (Fin d → ℝ)) → ℝ) ≃L[ℝ] EG :=
    ContinuousLinearEquiv.ofFinrankEq <| by
      rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
      omega
  exact (IsSubmersionAtOfComplement.congr_F eEG).mp
    (hqmk.contMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv
      isOpen_univ (mem_univ x) (by simp) hsurj)

/-- The orbit projection of a free proper smooth action is a smooth submersion onto
`MulAction.orbitRel.Quotient G M`. -/
theorem isSubmersion_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) :=
  letI := freeProperQuotientChartedSpace I IG G M
  (isSubmersionOfComplement_quotientMk_freeProperQuotient I IG G M).isSubmersion

/-- **Vertical tangent spaces of the orbit projection.** At every point `x : M`, the kernel of the
differential of the orbit projection `M → M ⧸ G` is the orbit tangent space `𝔤 · x`. -/
theorem ker_mfderiv_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace I IG G M
    haveI := FiniteDimensional.completeSpace ℝ EG
    haveI := FiniteDimensional.completeSpace ℝ E
    ∀ x : M, (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG G M
  have := FiniteDimensional.completeSpace ℝ EG
  have := FiniteDimensional.completeSpace ℝ E
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  let K := 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  let qmk := Quotient.mk (MulAction.orbitRel G M)
  intro x
  have hle : (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤ (mfderiv I K qmk x).ker :=
    orbitTangent_le_ker_mfderiv fun g ↦ MulAction.orbitRel.Quotient.quotient_smul_eq
  have hsurj := (isSubmersion_quotientMk_freeProperQuotient I IG G M).surjective_mfderiv
    (by simp : (∞ : ℕ∞ω) ≠ 0) x
  have hfree := isCancelSMul_iff_stabilizer_eq_bot.mp ‹IsCancelSMul G M› x
  have hle_dim := finrank_le_of_stabilizer_eq_bot (IG := IG) (I := I) hfree
  have hker_dim : finrank ℝ (mfderiv I K qmk x).ker =
      finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) := by
    rw [(mfderiv I K qmk x).toLinearMap.finrank_ker_eq_sub_of_surjective hsurj,
      finrank_tangentSpace, finrank_tangentSpace, Module.finrank_fin_fun,
      finrank_orbitTangent_of_stabilizer_eq_bot hfree]
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hker_dim.symm).symm

end QuotientManifold

/-- **The Quotient Manifold Theorem for Free Proper Smooth Actions** (Lee Theorem 21.10,
Meinrenken Theorem 1.21). If a finite-dimensional boundaryless real Lie group `G` acts smoothly,
freely, and properly on a finite-dimensional boundaryless real smooth manifold `M`, then the orbit
space `MulAction.orbitRel.Quotient G M` with its quotient topology admits a smooth manifold
structure of dimension `finrank ℝ E - finrank ℝ EG` for which the quotient projection is a smooth
submersion. -/
theorem exists_freeProperQuotient_isSubmersion
    {E H M EG HG G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG] [TopologicalSpace HG]
    {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless]
    [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
    [MulAction G M] [ProperSMul G M]
    (hsm : ContMDiff (IG.prod I) I ∞ (fun gx : G × M ↦ gx.1 • gx.2))
    (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    ∃ cs : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M) ∧
      IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) := by
  have : ContMDiffSMul IG I ∞ G M := ⟨hsm⟩
  have : IsCancelSMul G M := isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  exact ⟨freeProperQuotientChartedSpace I IG G M, isManifold_freeProperQuotient I IG G M,
    isSubmersion_quotientMk_freeProperQuotient I IG G M⟩

/-! ### Smooth descent, equivariant maps, and immersions -/

section Descent

variable {EG HG G E H M : Type*}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **Universal property of the smooth orbit quotient.** For `m ≤ ∞`, a map out of
`MulAction.orbitRel.Quotient G M` is `C^m` if and only if its composite with the orbit projection
is `C^m`. -/
theorem contMDiff_comp_quotientMk_freeProperQuotient_iff
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {m : ℕ∞ω} (hm : m ≤ ∞) {g : MulAction.orbitRel.Quotient G M → N} :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiff I J m (g ∘ Quotient.mk (MulAction.orbitRel G M)) ↔
      ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) J m g :=
  letI := freeProperQuotientChartedSpace I IG G M
  (isSubmersion_quotientMk_freeProperQuotient I IG G M).contMDiff_comp_iff
    Quotient.mk_surjective hm

/-- **Smooth descent of invariant maps.** For `m ≤ ∞`, the quotient lift
`MulAction.orbitRelQuotientLift f hf` of a `G`-invariant map `f : M → N` is `C^m` if and only if
`f` is `C^m`. -/
theorem contMDiff_orbitRelQuotientLift_freeProperQuotient_iff
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {m : ℕ∞ω} (hm : m ≤ ∞) {f : M → N} (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace I IG G M
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) J m
      (MulAction.orbitRelQuotientLift f hf) ↔ ContMDiff I J m f := by
  let := freeProperQuotientChartedSpace I IG G M
  rw [← contMDiff_comp_quotientMk_freeProperQuotient_iff (IG := IG) (I := I) hm,
    MulAction.orbitRelQuotientLift_comp_mk]

/-- **Functoriality on equivariant smooth maps.** An equivariant `C^m` (`m ≤ ∞`) map
`φ : M →ₑ[σ] M'` between two free proper smooth Lie group actions descends to a `C^m` map
`MulActionHom.orbitRelQuotientMap φ` between their smooth orbit quotients. -/
theorem contMDiff_orbitRelQuotientMap_freeProperQuotient
    {EG' HG' G' E' H' M' : Type*}
    [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
    [TopologicalSpace HG'] {IG' : ModelWithCorners ℝ EG' HG'} [IG'.Boundaryless]
    [TopologicalSpace G'] [ChartedSpace HG' G'] [Group G'] [LieGroup IG' ∞ G']
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [ProperSMul G' M'] [IsCancelSMul G' M']
    {σ : G → G'} {φ : M →ₑ[σ] M'} {m : ℕ∞ω} (hm : m ≤ ∞) (hφ : ContMDiff I I' m φ) :
    letI := freeProperQuotientChartedSpace I IG G M
    letI := freeProperQuotientChartedSpace I' IG' G' M'
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ EG') → ℝ) m φ.orbitRelQuotientMap := by
  let := freeProperQuotientChartedSpace I IG G M
  let := freeProperQuotientChartedSpace I' IG' G' M'
  refine (contMDiff_comp_quotientMk_freeProperQuotient_iff (IG := IG) (I := I) hm).1 ?_
  rw [MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_quotientMk_freeProperQuotient I' IG' G' M').of_le hm).comp hφ

/-- **Immersion criterion for descended maps.** Let `1 ≤ m ≤ ∞` and let `N` be a finite-dimensional
boundaryless real `C^m` manifold. The quotient lift `MulAction.orbitRelQuotientLift f hf` of a
`G`-invariant map `f : M → N` is a `C^m` immersion if and only if `f` is `C^m` and the kernel of
`mfderiv I J f x` at every `x : M` is the orbit tangent space `𝔤 · x`. -/
theorem isImmersion_orbitRelQuotientLift_freeProperQuotient_iff
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
    [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace HN N] {m : ℕ∞ω} [IsManifold J m N]
    (hm1 : 1 ≤ m) (hm : m ≤ ∞) {f : M → N} (hf : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := freeProperQuotientChartedSpace I IG G M
    haveI := FiniteDimensional.completeSpace ℝ EG
    haveI := FiniteDimensional.completeSpace ℝ E
    IsImmersion 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) J m
      (MulAction.orbitRelQuotientLift f hf) ↔
    ContMDiff I J m f ∧
      ∀ x : M, (mfderiv I J f x).ker =
        (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace I IG G M
  have := (isManifold_freeProperQuotient I IG G M).of_le hm
  have := FiniteDimensional.completeSpace ℝ EG
  have := FiniteDimensional.completeSpace ℝ E
  have hsub := (isSubmersion_quotientMk_freeProperQuotient I IG G M).of_le hm
  rw [hsub.isImmersion_iff_ker_mfderiv_comp Quotient.mk_surjective hm1,
    MulAction.orbitRelQuotientLift_comp_mk]
  simp_rw [ker_mfderiv_quotientMk_freeProperQuotient I IG G M]

end Descent

/-! ### Uniqueness and compatibility with discrete quotients -/

section Uniqueness

variable {EG HG G E H M : Type*}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **Uniqueness of the smooth quotient maximal atlas.** Any smooth manifold structure on
`MulAction.orbitRel.Quotient G M` modelled on `Fin (finrank ℝ E - finrank ℝ EG) → ℝ` for which the
orbit projection is a smooth submersion has the same `C^∞` maximal atlas as
`TauCeti.freeProperQuotientChartedSpace`. -/
theorem maximalAtlas_freeProperQuotient_eq
    (c : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M))
    (hcM : letI := c; IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M))
    (hc : letI := c; IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M))) :
    (letI := freeProperQuotientChartedSpace I IG G M;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) =
    (letI := c;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) :=
  ChartedSpace.maximalAtlas_eq_of_isSubmersion
    (freeProperQuotientChartedSpace I IG G M) c
    (isManifold_freeProperQuotient I IG G M) hcM
    Quotient.mk_surjective
    (isSubmersion_quotientMk_freeProperQuotient I IG G M) hc

/-- **Uniqueness of the smooth quotient up to canonical diffeomorphism.** For any smooth atlas on
`MulAction.orbitRel.Quotient G M` (with arbitrary model `JQ`) making the orbit projection a smooth
submersion, the identity map is a smooth diffeomorphism from
`TauCeti.freeProperQuotientChartedSpace` to that atlas. -/
theorem exists_diffeomorph_freeProperQuotient_apply_eq_self
    {EQ HQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {JQ : ModelWithCorners ℝ EQ HQ}
    (c : ChartedSpace HQ (MulAction.orbitRel.Quotient G M))
    (hc : letI := c; IsSubmersion I JQ ∞ (Quotient.mk (MulAction.orbitRel G M))) :
    ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) JQ
      (MulAction.orbitRel.Quotient G M) _ (freeProperQuotientChartedSpace I IG G M)
      (MulAction.orbitRel.Quotient G M) _ c ∞,
      ∀ q, e q = q :=
  ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion
    (freeProperQuotientChartedSpace I IG G M) c
    Quotient.mk_surjective
    (isSubmersion_quotientMk_freeProperQuotient I IG G M) hc

/-- **Compatibility with discrete group quotients.** When the Lie group `G` carries the discrete
topology, its proper action is properly discontinuous (`ProperSMul.properlyDiscontinuousSMul`), and
the identity of `MulAction.orbitRel.Quotient G M` is a smooth diffeomorphism between
`TauCeti.freeProperQuotientChartedSpace` and Mathlib's covering-map quotient atlas
`MulAction.instChartedSpaceQuotient`. -/
theorem exists_diffeomorph_freeProperQuotient_instChartedSpaceQuotient [DiscreteTopology G] :
    haveI : ProperlyDiscontinuousSMul G M := ProperSMul.properlyDiscontinuousSMul G M
    haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
    haveI : LocallyCompactSpace H := I.locallyCompactSpace
    haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
    ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I
      (MulAction.orbitRel.Quotient G M) _ (freeProperQuotientChartedSpace I IG G M)
      (MulAction.orbitRel.Quotient G M) _ (MulAction.instChartedSpaceQuotient (H := H)) ∞,
      ∀ q, e q = q := by
  have := FiniteDimensional.completeSpace ℝ E
  have : ProperlyDiscontinuousSMul G M := ProperSMul.properlyDiscontinuousSMul G M
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : ContMDiffConstSMul I ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := IG)⟩
  have hq : IsLocalDiffeomorph I I ∞ (Quotient.mk (MulAction.orbitRel G M)) :=
    isLocalDiffeomorph_quotientMk (I := I) (n := ∞) (G := G) (M := M)
  exact exists_diffeomorph_freeProperQuotient_apply_eq_self
    (MulAction.instChartedSpaceQuotient (H := H))
    (hq.contMDiff.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun x ↦
      ((hq x).mfderivToContinuousLinearEquiv (by simp)).surjective).isSubmersion

end Uniqueness

/-! ### Smooth equivariant local trivializations -/

section Trivialization

variable {EG HG G E H M : Type*}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless]
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **Local principal-bundle trivializations of the orbit projection** (Meinrenken Theorem 1.21).
Every orbit `q : MulAction.orbitRel.Quotient G M` of a free proper smooth Lie group action admits
an open neighbourhood `e.baseSet` over which the orbit projection trivializes smoothly and
`G`-equivariantly as a `Bundle.Trivialization G (Quotient.mk (MulAction.orbitRel G M))`. -/
theorem exists_orbitTrivialization_freeProperQuotient
    (q : MulAction.orbitRel.Quotient G M) :
    letI := freeProperQuotientChartedSpace I IG G M
    ∃ e : Trivialization G (Quotient.mk (MulAction.orbitRel G M)),
      q ∈ e.baseSet ∧
      ContMDiffOn I (𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ).prod IG) ∞ e e.source ∧
      ContMDiffOn (𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ).prod IG) I ∞
        e.toOpenPartialHomeomorph.symm e.target ∧
      ∀ g : G, ∀ z ∈ e.source, e (g • z) = ((e z).1, g * (e z).2) := by
  let := freeProperQuotientChartedSpace I IG G M
  have := isManifold_freeProperQuotient I IG G M
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup IG ∞
  let d := finrank ℝ E - finrank ℝ EG
  let K := 𝓘(ℝ, Fin d → ℝ)
  let qmk := Quotient.mk (MulAction.orbitRel G M)
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  let U := sliceOpen I IG G M x
  let σ := sliceMap I IG G M x
  let S : Set (G × (Fin d → ℝ)) := univ ×ˢ (U : Set (Fin d → ℝ))
  have hS : IsOpen S := isOpen_univ.prod U.2
  let ψ : G × (Fin d → ℝ) → M := fun p ↦ p.1 • σ p.2
  have hinj := injOn_smul_sliceMap I IG G M x
  have hloc := isLocalDiffeomorphOn_smul_sliceMap I IG G M x
  let W : Set (MulAction.orbitRel.Quotient G M) := range (quotientPiece I IG G M x)
  have hW : IsOpen W := (isOpenEmbedding_quotientPiece I IG G M x).isOpen_range
  have hxW : qmk x ∈ W :=
    ⟨⟨0, zero_mem_sliceOpen I IG G M x⟩, congrArg qmk (sliceMap_zero I IG G M x)⟩
  -- The preimage of the slice chart image `W` in `M` is the open slice tube `ψ '' (G × U)`.
  have hpre : qmk ⁻¹' W = ψ '' S := by
    ext z
    simp only [W, quotientPiece, S, ψ, mem_preimage, mem_range, Subtype.exists,
      SetLike.mem_coe, mem_image, Prod.exists, mem_prod, mem_univ, true_and]
    constructor
    · rintro ⟨s, hs, hsz⟩
      obtain ⟨g, hg⟩ :=
        MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hsz.symm))
      exact ⟨g, s, hs, hg⟩
    · rintro ⟨g, s, hs, rfl⟩
      exact ⟨s, hs, MulAction.orbitRel.Quotient.quotient_smul_eq.symm⟩
  have : Nonempty (G × (Fin d → ℝ)) := ⟨(1, 0)⟩
  let u : M → G := fun z ↦ (invFunOn ψ S z).1
  have hinv : ContMDiffOn I (IG.prod K) ∞ (invFunOn ψ S) (qmk ⁻¹' W) :=
    hpre ▸ hloc.contMDiffOn_invFunOn hS hinj
  have hu : ContMDiffOn I IG ∞ u (qmk ⁻¹' W) := contMDiff_fst.comp_contMDiffOn hinv
  have hu_smul : ∀ g : G, ∀ z ∈ qmk ⁻¹' W, u (g • z) = g * u z := by
    intro g z hz
    rw [hpre] at hz
    obtain ⟨⟨h, s⟩, ⟨-, hs⟩, rfl⟩ := hz
    have h1 : invFunOn ψ S (ψ (h, s)) = (h, s) := hinj.leftInvOn_invFunOn ⟨mem_univ _, hs⟩
    have h2 : invFunOn ψ S (ψ (g * h, s)) = (g * h, s) :=
      hinj.leftInvOn_invFunOn ⟨mem_univ _, hs⟩
    have hmul : g • ψ (h, s) = ψ (g * h, s) := by simp [ψ, mul_smul]
    simp only [u, hmul, h1, h2]
  let e := orbitTrivialization W hW u hu.continuousOn hu_smul
  have he_src : e.source = qmk ⁻¹' W := by rw [e.source_eq, orbitTrivialization_baseSet]
  have he_tgt : e.target = W ×ˢ univ := by rw [e.target_eq, orbitTrivialization_baseSet]
  refine ⟨e, by simpa [e] using hxW, ?_, ?_, fun g z hz ↦ ?_⟩
  · refine (((contMDiff_quotientMk_freeProperQuotient I IG G M).contMDiffOn).prodMk
      (he_src ▸ hu)).congr fun z _ ↦ ?_
    exact orbitTrivialization_apply z
  · intro p hp
    refine ContMDiffAt.contMDiffWithinAt ?_
    rw [he_tgt] at hp
    obtain ⟨z, hz : qmk z = p.1⟩ := Quotient.mk_surjective p.1
    have hzW : qmk z ∈ W := hz.symm ▸ hp.1
    have hid_sub : IsSubmersionOfComplement PUnit.{1} IG IG ∞ (@id G) :=
      IsSubmersionOfComplement.id
    have hsub_prod : IsSubmersionAt (I.prod IG) (K.prod IG) ∞ (Prod.map qmk id) (z, p.2) :=
      ((isSubmersion_quotientMk_freeProperQuotient I IG G M).isSubmersionAt z).prodMap
        (hid_sub.isSubmersion.isSubmersionAt p.2)
    have hmap_eq : Prod.map qmk id (z, p.2) = p := Prod.ext hz rfl
    rw [← hmap_eq, ← hsub_prod.contMDiffAt_comp_iff le_rfl]
    have hopen_pre : IsOpen ((qmk ⁻¹' W) ×ˢ (univ : Set G)) :=
      (hW.preimage continuous_quot_mk).prod isOpen_univ
    have hmem_pre : (z, p.2) ∈ (qmk ⁻¹' W) ×ˢ (univ : Set G) := ⟨hzW, mem_univ _⟩
    have hformula : ContMDiffAt (I.prod IG) I ∞ (fun q : M × G ↦ (q.2 * (u q.1)⁻¹) • q.1)
        (z, p.2) :=
      (contMDiffAt_snd.mul ((hu.contMDiffAt
        ((hW.preimage continuous_quot_mk).mem_nhds hzW)).comp (z, p.2)
        contMDiffAt_fst).inv).smul contMDiffAt_fst
    refine hformula.congr_of_eventuallyEq ?_
    filter_upwards [hopen_pre.mem_nhds hmem_pre] with q hq
    exact orbitTrivialization_symm_apply_mk hq.1 q.2
  · exact orbitTrivialization_apply_smul g (mem_preimage.1 (he_src ▸ hz))

end Trivialization

end TauCeti

