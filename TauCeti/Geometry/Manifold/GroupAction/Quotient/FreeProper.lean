/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.GroupAction.Quotient.Basic

import TauCeti.Geometry.Lie.Basic
import TauCeti.Geometry.Lie.FundamentalVectorField.OrbitMap
import TauCeti.Geometry.Lie.Subgroup.Stabilizer
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
import TauCeti.Geometry.Manifold.Instances.Quotient
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.Submersion.Descent
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Topology.Algebra.GroupAction.SliceChart
import TauCeti.Topology.Algebra.ProperAction.TransverseSlice

/-!
# Quotient manifolds of free proper Lie group actions

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on a
finite-dimensional boundaryless smooth real manifold `M`. This file constructs the canonical smooth
manifold structure on the orbit space `MulAction.orbitRel.Quotient G M`, retaining its quotient
topology, of dimension `dim M - dim G` (**the quotient manifold theorem**). Neither `M` nor `G` is
assumed to be Hausdorff or second countable (Hausdorffness of `G` and `M` follows from the Lie
group structure and properness), the model of `G` need not be assumed boundaryless, and `M` may be
empty.

At every point `x : M` with trivial stabilizer, the isotropy algebra `𝔤_x` vanishes
(`TauCeti.Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot`), so a complement of the orbit
tangent space `𝔤 · x` in `T_x M` has dimension `dim M - dim G` and defines a smooth chart slice
`σ : (Fin (dim M - dim G) → ℝ) → M` through `x` whose slice map `(g, v) ↦ g • σ v` is a local
diffeomorphism near `(1, 0)` (`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`). Equivariance
spreads the local diffeomorphism property to `G × U` and properness makes it injective on `G × U`
after shrinking `U` (`ProperSMul.exists_mem_nhds_injOn_smul_slice`), giving
`TauCeti.exists_isLocalDiffeomorphOn_smul_slice`.

Gluing along the induced open embeddings `U → M ⧸ G`
(`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`,
`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`, `TauCeti.chartedSpaceOfIsOpenEmbedding`)
produces the smooth atlas `TauCeti.freeProperQuotientChartedSpace` (marked `@[instance_reducible]`,
not installed globally, so it never collides with `MulAction.instChartedSpaceQuotient` for discrete
actions). For this atlas, the orbit projection is a surjective smooth submersion with complement
`EG` and tangent kernel `𝔤 · x`, arbitrary transverse slices are local diffeomorphisms into `M ⧸ G`,
the orbit projection admits smooth `G`-equivariant local trivializations, smooth maps and
immersions descend, and any surjective smooth submersion with the `G`-orbits as fibres identifies
`M ⧸ G` diffeomorphically with its target — yielding uniqueness of the quotient smooth structure,
agreement with the discrete-action quotient atlas, and the trivial-group specialization `M ⧸ G ≃ M`.

## Main declarations

* `TauCeti.exists_isLocalDiffeomorphOn_smul_slice`: existence of a smooth injective transverse slice
  through any free point of a proper Lie group action.
* `TauCeti.exists_contMDiffOn_smul_eq_mul_of_stabilizer_eq_bot`: existence of a smooth equivariant
  map `u : π⁻¹ W → G` over an open orbit neighbourhood of any free point.
* `TauCeti.freeProperQuotientChartedSpace`, `TauCeti.isManifold_freeProperQuotient`,
  `TauCeti.isSubmersionOfComplement_quotientMk_freeProperQuotient`,
  `TauCeti.ker_mfderiv_quotientMk_freeProperQuotient`,
  `TauCeti.exists_freeProperQuotient_isSubmersion`: the quotient manifold theorem.
* `TauCeti.isLocalDiffeomorph_quotientMk_slice`, `TauCeti.exists_smoothOrbitTrivialization`:
  arbitrary transverse slices and smooth `G`-equivariant local trivializations.
* `TauCeti.contMDiffAt_freeProperQuotientLift_iff`, `TauCeti.contMDiff_freeProperQuotientLift_iff`,
  `TauCeti.isImmersion_freeProperQuotientLift_iff`, `TauCeti.contMDiff_freeProperQuotientMap`:
  smooth descent along the orbit projection.
* `TauCeti.freeProperQuotientDiffeomorphOfIsSubmersion`,
  `TauCeti.exists_diffeomorph_freeProperQuotient_apply_eq_self`,
  `TauCeti.maximalAtlas_freeProperQuotient_eq`,
  `TauCeti.exists_diffeomorph_freeProperQuotient_discrete_apply_eq_self`,
  `TauCeti.freeProperQuotientDiffeomorphSelf`: universal property, uniqueness, discrete-action
  agreement, and trivial-group specialization.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.10 (the
  quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21.
-/

public section

noncomputable section

open Function Manifold Module Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MulAction G M] [ContMDiffSMul IG I ∞ G M] [ProperSMul G M]

/-! ### Transverse slices and smooth equivariant maps at free points -/

private theorem isotropy_eq_bot_of_stabilizer_eq_bot (x : M)
    (hfree : MulAction.stabilizer G x = ⊥) :
    (InfinitesimalAction.fundamental IG G I M).isotropy x = ⊥ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := IG) (I' := I) ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  have : Subsingleton (MulAction.stabilizer G x) := by
    rw [hfree]
    infer_instance
  exact (Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := IG) (I' := I)).1 inferInstance

private theorem finrank_orbitTangent_eq_of_stabilizer_eq_bot (x : M)
    (hfree : MulAction.stabilizer G x = ⊥) :
    finrank ℝ ((InfinitesimalAction.fundamental IG G I M).orbitTangent x) = finrank ℝ EG := by
  have hiso := isotropy_eq_bot_of_stabilizer_eq_bot (IG := IG) (I := I) x hfree
  have hsum :=
    (InfinitesimalAction.fundamental IG G I M).finrank_orbitTangent_add_finrank_isotropy x
  have hzero : finrank ℝ ((InfinitesimalAction.fundamental IG G I M).isotropy x) = 0 := by
    have : Subsingleton ((InfinitesimalAction.fundamental IG G I M).isotropy x) :=
      ⟨fun a b ↦ Subtype.ext (by
        have ha : a.1 = 0 := by simpa [hiso] using a.2
        have hb : b.1 = 0 := by simpa [hiso] using b.2
        rw [ha, hb])⟩
    exact finrank_zero_of_subsingleton
  rw [hzero, add_zero] at hsum
  exact hsum

/-- **Existence of an injective transverse slice at a free point.** Let a finite-dimensional real
Lie group `G` act smoothly and properly on a finite-dimensional boundaryless smooth real manifold
`M`, and let `x : M` have trivial stabilizer. Then there is a smooth map
`σ : (Fin (dim M - dim G) → ℝ) → M` with `σ 0 = x` and an open neighbourhood `U` of `0` such that
the slice map `(g, v) ↦ g • σ v` is injective and a smooth local diffeomorphism on `G × U`. -/
theorem exists_isLocalDiffeomorphOn_smul_slice (x : M) (hfree : MulAction.stabilizer G x = ⊥) :
    ∃ (σ : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M)
      (U : Set (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)),
      IsOpen U ∧ 0 ∈ U ∧ σ 0 = x ∧
      ContMDiffOn 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞ σ U ∧
      InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
        (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let d := finrank ℝ E - finrank ℝ EG
  let V : Submodule ℝ E := (InfinitesimalAction.fundamental IG G I M).orbitTangent x
  have hiso := isotropy_eq_bot_of_stabilizer_eq_bot (IG := IG) (I := I) x hfree
  have horb : finrank ℝ V = finrank ℝ EG :=
    finrank_orbitTangent_eq_of_stabilizer_eq_bot (IG := IG) (I := I) x hfree
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  have hdim : finrank ℝ (Fin d → ℝ) = finrank ℝ W := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hW
    rw [finrank_fin_fun]
    omega
  let e : (Fin d → ℝ) ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq hdim
  let τ : (Fin d → ℝ) → E := fun v ↦ extChartAt I x x + (e v : E)
  let σ : (Fin d → ℝ) → M := fun v ↦ (extChartAt I x).symm (τ v)
  have hσ0 : σ 0 = x := by simp [σ, τ]
  have hτ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, E) ∞ τ :=
    (contDiff_const.add (W.subtypeL.comp e.toContinuousLinearMap).contDiff).contMDiff
  let U₀ : Set (Fin d → ℝ) := τ ⁻¹' (extChartAt I x).target
  have hU₀ : IsOpen U₀ := (isOpen_extChartAt_target x).preimage hτ.continuous
  have h0U₀ : (0 : Fin d → ℝ) ∈ U₀ := by simp [U₀, τ]
  have hσU₀ : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I ∞ σ U₀ :=
    (contMDiffOn_extChartAt_symm x).comp hτ.contMDiffOn fun _ hv ↦ hv
  -- Precompose the chart-slice local diffeomorphism on `G × W` with `id × e`.
  let T : (G × (Fin d → ℝ)) ≃ₘ^∞⟮IG.prod 𝓘(ℝ, Fin d → ℝ), IG.prod 𝓘(ℝ, W)⟯ (G × W) :=
    { toEquiv := (Equiv.refl G).prodCongr e.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk (e.contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk (e.symm.contDiff.contMDiff.comp contMDiff_snd) }
  have hT0 : T (1, 0) = (1, 0) := Prod.ext rfl (map_zero e)
  have hloc0 : IsLocalDiffeomorphAt (IG.prod 𝓘(ℝ, Fin d → ℝ)) I ∞
      (fun p : G × (Fin d → ℝ) ↦ p.1 • σ p.2) (1, 0) :=
    IsLocalDiffeomorphAt.comp (f := T)
      (g := fun p : G × W ↦ p.1 • (extChartAt I x).symm (extChartAt I x x + p.2))
      (hf := T.isLocalDiffeomorph (1, 0))
      (hg := hT0.symm ▸ isLocalDiffeomorphAt_smul_extChartAt_symm (I := IG) (I' := I) hiso hW)
  -- Equivariance spreads local diffeomorphism to `G × U₁`;
  -- properness gives injectivity on `G × U₂`.
  have hU₁ := hloc0.eventually_forall_smul_slice
  have hinjΦ : InjOn (fun p : G × (Fin d → ℝ) ↦ p.1 • σ p.2) hloc0.localInverse.target :=
    fun p hp q hq hpq ↦ by
      rw [← hloc0.localInverse_left_inv hp, ← hloc0.localInverse_left_inv hq]
      exact congrArg hloc0.localInverse hpq
  obtain ⟨U₂, hU₂, hinj₂⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice
    (hσU₀.contMDiffAt (hU₀.mem_nhds h0U₀)).continuousAt (hσ0.symm ▸ hfree)
    (hloc0.localInverse.open_target.mem_nhds hloc0.localInverse_mem_target) hinjΦ
  obtain ⟨U, hUsub, hUopen, h0U⟩ :=
    mem_nhds_iff.1 (inter_mem (hU₀.mem_nhds h0U₀) (inter_mem hU₁ hU₂))
  exact ⟨σ, U, hUopen, h0U, hσ0, hσU₀.mono fun _ hv ↦ (hUsub hv).1,
    hinj₂.mono (prod_mono_right fun _ hv ↦ (hUsub hv).2.2), fun ⟨⟨g, v⟩, _, hv⟩ ↦ (hUsub hv).2.1 g⟩

/-- **Smooth equivariant maps near free points.** At any point `x : M` with trivial stabilizer of a
smooth proper action of a finite-dimensional real Lie group `G`, there is an open neighbourhood `W`
of the orbit `[x]` in `M ⧸ G` and a smooth map `u : M → G` on `π⁻¹ W` satisfying `u x = 1` and
`u (g • y) = g * u y` for all `g : G` and `y ∈ π⁻¹ W`. -/
theorem exists_contMDiffOn_smul_eq_mul_of_stabilizer_eq_bot (x : M)
    (hfree : MulAction.stabilizer G x = ⊥) :
    ∃ (W : Set (MulAction.orbitRel.Quotient G M)),
      IsOpen W ∧ Quotient.mk (MulAction.orbitRel G M) x ∈ W ∧
      ∃ u : M → G, ContMDiffOn I IG ∞ u (Quotient.mk (MulAction.orbitRel G M) ⁻¹' W) ∧
        u x = 1 ∧
        ∀ (g : G), ∀ y ∈ Quotient.mk (MulAction.orbitRel G M) ⁻¹' W, u (g • y) = g * u y := by
  obtain ⟨σ, U, hU, h0U, hσ0, -, hinj, hloc⟩ :=
    exists_isLocalDiffeomorphOn_smul_slice (IG := IG) (I := I) x hfree
  let Ψ : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M := fun p ↦ p.1 • σ p.2
  have hopen := MulAction.isOpenEmbedding_quotientMk_slice hU hinj hloc.isLocalHomeomorphOn
  let W : Set (MulAction.orbitRel.Quotient G M) :=
    range fun v : U ↦ Quotient.mk (MulAction.orbitRel G M) (σ v)
  have hpre : Quotient.mk (MulAction.orbitRel G M) ⁻¹' W = Ψ '' (univ ×ˢ U) := by
    ext y
    constructor
    · rintro ⟨⟨v, hv⟩, hvy⟩
      obtain ⟨g, hg⟩ : ∃ g : G, g • σ v = y := Quotient.exact hvy.symm
      exact ⟨(g, v), ⟨mem_univ _, hv⟩, hg⟩
    · rintro ⟨⟨g, v⟩, ⟨-, hv⟩, rfl⟩
      exact ⟨⟨v, hv⟩, Quotient.sound ⟨g⁻¹, by simp [Ψ]⟩⟩
  let Φ := hloc.partialDiffeomorphOfInjOn (isOpen_univ.prod hU) hinj
  have htarget : Φ.target = Quotient.mk (MulAction.orbitRel G M) ⁻¹' W := by
    rw [IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target, hpre]
  refine ⟨W, hopen.isOpen_range, ⟨⟨0, h0U⟩, by simp [hσ0]⟩,
    fun y ↦ (Φ.toPartialEquiv.symm y).1, ?_, ?_, ?_⟩
  · rw [← htarget]
    exact contMDiff_fst.comp_contMDiffOn Φ.contMDiffOn_invFun
  · have hxΦ : Φ (1, 0) = x := by simp [Φ, hσ0]
    have hleft := Φ.toPartialEquiv.left_inv (x := (1, 0)) (by simp [Φ, h0U])
    rw [← hxΦ]
    exact congrArg Prod.fst hleft
  · intro g y hy
    have hyT : y ∈ Φ.target := htarget.symm ▸ hy
    have hsrc : Φ.toPartialEquiv.symm y ∈ univ ×ˢ U := by
      simpa only [Φ, IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source] using
        Φ.toPartialEquiv.map_target hyT
    have hgy_src : (g * (Φ.toPartialEquiv.symm y).1, (Φ.toPartialEquiv.symm y).2) ∈ Φ.source := by
      rw [IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source]
      exact ⟨mem_univ _, hsrc.2⟩
    have hgy : Φ (g * (Φ.toPartialEquiv.symm y).1, (Φ.toPartialEquiv.symm y).2) = g • y := by
      have hright : Φ (Φ.toPartialEquiv.symm y) = y := Φ.toPartialEquiv.right_inv hyT
      simp only [Φ, IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn, mul_smul] at hright ⊢
      rw [hright]
    have hleft := Φ.toPartialEquiv.left_inv hgy_src
    rw [hgy] at hleft
    exact congrArg Prod.fst hleft

/-! ### The quotient manifold theorem -/

section QuotientManifold

variable [IsCancelSMul G M]
variable (IG G I M)

private structure FreeSlice (x : M) where
  toFun : (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) → M
  domain : TopologicalSpace.Opens (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
  zero_mem : (0 : Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∈ domain
  map_zero : toFun 0 = x
  contMDiffOn : ContMDiffOn 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞ toFun domain
  injOn : InjOn (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • toFun p.2)
    (univ ×ˢ (domain : Set _))
  isLocalDiffeomorphOn : IsLocalDiffeomorphOn
    (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) I ∞
    (fun p : G × (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ↦ p.1 • toFun p.2)
    (univ ×ˢ (domain : Set _))

private def freeSlice (x : M) : FreeSlice IG G I M x :=
  let h := exists_isLocalDiffeomorphOn_smul_slice (IG := IG) (I := I) x
    (isCancelSMul_iff_stabilizer_eq_bot.mp ‹_› x)
  { toFun := h.choose
    domain := ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩
    zero_mem := h.choose_spec.choose_spec.2.1
    map_zero := h.choose_spec.choose_spec.2.2.1
    contMDiffOn := h.choose_spec.choose_spec.2.2.2.1
    injOn := h.choose_spec.choose_spec.2.2.2.2.1
    isLocalDiffeomorphOn := h.choose_spec.choose_spec.2.2.2.2.2 }

private def sliceQuotientMap (x : M) :
    (freeSlice IG G I M x).domain → MulAction.orbitRel.Quotient G M :=
  fun v ↦ Quotient.mk (MulAction.orbitRel G M) ((freeSlice IG G I M x).toFun v)

private theorem sliceQuotientMap_isOpenEmbedding (x : M) :
    IsOpenEmbedding (sliceQuotientMap IG G I M x) :=
  MulAction.isOpenEmbedding_quotientMk_slice (freeSlice IG G I M x).domain.isOpen
    (freeSlice IG G I M x).injOn (freeSlice IG G I M x).isLocalDiffeomorphOn.isLocalHomeomorphOn

private theorem sliceQuotientMap_cover (q : MulAction.orbitRel.Quotient G M) :
    ∃ (x : M) (v : (freeSlice IG G I M x).domain), sliceQuotientMap IG G I M x v = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    exact ⟨x, ⟨0, (freeSlice IG G I M x).zero_mem⟩,
      by simp [sliceQuotientMap, (freeSlice IG G I M x).map_zero]⟩

private theorem sliceQuotientMap_deck (x y : M) (u : (freeSlice IG G I M x).domain)
    (v : (freeSlice IG G I M y).domain)
    (hxy : sliceQuotientMap IG G I M x u = sliceQuotientMap IG G I M y v) :
    ∃ T : (freeSlice IG G I M x).domain → (freeSlice IG G I M y).domain,
      ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ T u ∧
      sliceQuotientMap IG G I M y ∘ T =ᶠ[𝓝 u] sliceQuotientMap IG G I M x := by
  have hσu : ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I ∞
      ((freeSlice IG G I M x).toFun ∘ Subtype.val) u :=
    ((freeSlice IG G I M x).contMDiffOn.contMDiffAt
      ((freeSlice IG G I M x).domain.isOpen.mem_nhds u.2)).comp u
      contMDiff_subtype_val.contMDiffAt
  obtain ⟨t, ht, -, hev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff (I := IG)
    (freeSlice IG G I M y).domain.isOpen (freeSlice IG G I M y).injOn
    (freeSlice IG G I M y).isLocalDiffeomorphOn hσu v.2 hxy.symm
  classical
  let T : (freeSlice IG G I M x).domain → (freeSlice IG G I M y).domain :=
    fun z ↦ if hz : t z ∈ ((freeSlice IG G I M y).domain : Set _) then ⟨t z, hz⟩ else v
  refine ⟨T, ?_, ?_⟩
  · rw [← ContMDiffAt.subtypeVal_comp_iff]
    refine ht.congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    simp only [Function.comp_apply, T, hz.1, ↓reduceDIte]
  · filter_upwards [hev] with z hz
    simpa only [Function.comp_apply, sliceQuotientMap, T, hz.1, ↓reduceDIte] using
      (hz.2 _ hz.1).2 rfl

/-- The canonical charted-space structure on the orbit space `MulAction.orbitRel.Quotient G M` of a
free proper smooth Lie group action, retaining its quotient topology and modelled on
`Fin (dim M - dim G) → ℝ`.

Marked `@[instance_reducible]` rather than `instance` so it does not conflict with
`MulAction.instChartedSpaceQuotient` for discrete actions. -/
@[instance_reducible]
def freeProperQuotientChartedSpace :
    ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M) :=
  chartedSpaceOfIsOpenEmbedding (sliceQuotientMap_isOpenEmbedding IG G I M)
    (sliceQuotientMap_cover IG G I M)

/-- The orbit space of a free proper smooth Lie group action, equipped with
`TauCeti.freeProperQuotientChartedSpace`, is a smooth manifold of dimension `dim M - dim G`. -/
theorem isManifold_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ (MulAction.orbitRel.Quotient G M) :=
  isManifold_chartedSpaceOfIsOpenEmbedding (sliceQuotientMap_isOpenEmbedding IG G I M)
    (sliceQuotientMap_cover IG G I M) (sliceQuotientMap_deck IG G I M)

/-- The orbit projection `M → M ⧸ G` is smooth for `TauCeti.freeProperQuotientChartedSpace`. -/
theorem contMDiff_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG G I M
  intro x
  let S := freeSlice IG G I M x
  have hloc := S.isLocalDiffeomorphOn ⟨(1, 0), mem_univ _, S.zero_mem⟩
  have h10 : (1 : G) • S.toFun 0 = x := by simp [S.map_zero]
  have hinv : ContMDiffAt I (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) ∞
      hloc.localInverse x :=
    (congrArg (ContMDiffAt I (IG.prod 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) ∞
      hloc.localInverse) h10).mp hloc.contMDiffAt_localInverse
  have hinv_x : hloc.localInverse x = (1, 0) :=
    (congrArg hloc.localInverse h10.symm).trans
      (hloc.localInverse_left_inv hloc.localInverse_mem_target)
  have hmemU : ∀ᶠ y in 𝓝 x, (hloc.localInverse y).2 ∈ (S.domain : Set _) :=
    (continuousAt_snd.comp hinv.continuousAt).preimage_mem_nhds
      (S.domain.isOpen.mem_nhds (by rw [Function.comp_apply, hinv_x]; exact S.zero_mem))
  have hmemS : ∀ᶠ y in 𝓝 x, y ∈ hloc.localInverse.source :=
    hloc.localInverse_open_source.mem_nhds
      ((congrArg (· ∈ hloc.localInverse.source) h10).mp hloc.localInverse_mem_source)
  classical
  let v : M → S.domain := fun y ↦
    if hy : (hloc.localInverse y).2 ∈ (S.domain : Set _) then
      ⟨(hloc.localInverse y).2, hy⟩
    else ⟨0, S.zero_mem⟩
  have hv : ContMDiffAt I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ v x := by
    rw [← ContMDiffAt.subtypeVal_comp_iff]
    refine (contMDiffAt_snd.comp x hinv).congr_of_eventuallyEq ?_
    filter_upwards [hmemU] with y hy
    simp only [Function.comp_apply, v, hy, ↓reduceDIte]
  have hφ : ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ (sliceQuotientMap IG G I M x) :=
    contMDiff_chartedSpaceOfIsOpenEmbedding (sliceQuotientMap_isOpenEmbedding IG G I M)
      (sliceQuotientMap_cover IG G I M) (sliceQuotientMap_deck IG G I M) x
  refine ((hφ (v x)).comp x hv).congr_of_eventuallyEq ?_
  filter_upwards [hmemU, hmemS] with y hyU hyS
  have hright : (hloc.localInverse y).1 • S.toFun (hloc.localInverse y).2 = y :=
    hloc.localInverse_right_inv hyS
  simp only [Function.comp_apply, sliceQuotientMap, v, hyU, ↓reduceDIte]
  exact Quotient.sound ⟨(hloc.localInverse y).1, hright⟩

/-- The differential of the orbit projection `M → M ⧸ G` is surjective at every point `x : M`. -/
theorem surjective_mfderiv_quotientMk_freeProperQuotient (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    Surjective (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x) := by
  let := freeProperQuotientChartedSpace IG G I M
  let S := freeSlice IG G I M x
  let u₀ : S.domain := ⟨0, S.zero_mem⟩
  let s : S.domain → M := S.toFun ∘ Subtype.val
  have hs0 : s u₀ = x := S.map_zero
  have hs : MDifferentiableAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I s u₀ :=
    ((S.contMDiffOn.contMDiffAt (S.domain.isOpen.mem_nhds u₀.2)).comp u₀
      contMDiff_subtype_val.contMDiffAt).mdifferentiableAt (by simp)
  have hq : MDifferentiableAt I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x :=
    (contMDiff_quotientMk_freeProperQuotient IG G I M x).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp_of_eq hq hs hs0
  have hloc := isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding
    (sliceQuotientMap_isOpenEmbedding IG G I M) (sliceQuotientMap_cover IG G I M)
    (sliceQuotientMap_deck IG G I M) x u₀
  have hsurj : Surjective (mfderiv 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (sliceQuotientMap IG G I M x) u₀) :=
    (hloc.isInvertible_mfderiv (by simp)).surjective
  have hsurj_comp : Surjective ((mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) (s u₀)).comp
      (mfderiv 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I s u₀)) := by
    rw [← hcomp]
    exact hsurj
  rw [← hs0]
  exact Surjective.of_comp hsurj_comp

/-- The orbit projection `M → M ⧸ G` is a smooth submersion with complement `EG`. This holds also
when `M` is empty. -/
theorem isSubmersionOfComplement_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    IsSubmersionOfComplement EG I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient IG G I M
  by_cases hM : Nonempty M
  · obtain ⟨x⟩ := hM
    have hle : finrank ℝ EG ≤ finrank ℝ E := by
      rw [← finrank_orbitTangent_eq_of_stabilizer_eq_bot (IG := IG) (I := I) x
        (isCancelSMul_iff_stabilizer_eq_bot.mp ‹_› x)]
      exact Submodule.finrank_le _
    have hcont := contMDiff_quotientMk_freeProperQuotient IG G I M
    have hsubm := hcont.isSubmersionOfComplement_of_surjective_mfderiv (by simp)
      (surjective_mfderiv_quotientMk_freeProperQuotient IG G I M)
    have hdim :
        finrank ℝ (Fin (finrank ℝ E - finrank ℝ (Fin (finrank ℝ E - finrank ℝ EG) → ℝ)) → ℝ) =
          finrank ℝ EG := by
      rw [finrank_fin_fun, finrank_fin_fun]
      omega
    exact hsubm.trans_F (ContinuousLinearEquiv.ofFinrankEq hdim)
  · rw [isSubmersionOfComplement_iff]
    exact fun x ↦ (hM ⟨x⟩).elim

/-- The orbit projection `M → M ⧸ G` is a smooth submersion. -/
theorem isSubmersion_quotientMk_freeProperQuotient :
    letI := freeProperQuotientChartedSpace IG G I M
    IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M)) := by
  let := freeProperQuotientChartedSpace IG G I M
  exact (isSubmersionOfComplement_quotientMk_freeProperQuotient IG G I M).isSubmersion

/-- **Tangent kernel of the orbit projection.** At every point `x : M`, the kernel of the
differential of the orbit projection `M → M ⧸ G` is the orbit tangent space `𝔤 · x`. -/
theorem ker_mfderiv_quotientMk_freeProperQuotient (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      (Quotient.mk (MulAction.orbitRel G M)) x).ker =
      (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace IG G I M
  have : CompleteSpace EG := FiniteDimensional.completeSpace ℝ EG
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  -- The orbit map `g ↦ g • x` projects to a constant map, so `𝔤 · x` lies in the kernel.
  have hconst : Quotient.mk (MulAction.orbitRel G M) ∘ (fun g : G ↦ g • x) =
      fun _ ↦ Quotient.mk (MulAction.orbitRel G M) ((1 : G) • x) :=
    funext fun g ↦ Quotient.sound (by rw [one_smul]; exact ⟨g, rfl⟩)
  have hcomp : (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M)) ((1 : G) • x)).comp
      (mfderiv IG I (fun g : G ↦ g • x) 1) = 0 := by
    rw [← mfderiv_comp_of_eq
      ((contMDiff_quotientMk_freeProperQuotient IG G I M x).mdifferentiableAt (by simp))
      ((ContMDiffSMul.contMDiff_smul_const (I := IG) (I' := I) (n := ∞) x).mdifferentiable
        (by simp) 1) (one_smul G x),
      hconst, mfderiv_const]
  have hle : (InfinitesimalAction.fundamental IG G I M).orbitTangent x ≤
      (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M)) x).ker := by
    have hle1 : (InfinitesimalAction.fundamental IG G I M).orbitTangent ((1 : G) • x) ≤
        (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
          (Quotient.mk (MulAction.orbitRel G M)) ((1 : G) • x)).ker := by
      rw [← range_mfderiv_smul_const (I := IG) (G := G) (I' := I) x (1 : G)]
      rintro _ ⟨w, rfl⟩
      exact congrArg (· w) hcomp
    rw [one_smul] at hle1
    exact hle1
  -- Both subspaces have dimension `dim G`.
  have horb := finrank_orbitTangent_eq_of_stabilizer_eq_bot (IG := IG) (I := I) x
    (isCancelSMul_iff_stabilizer_eq_bot.mp ‹_› x)
  have hdim_le : finrank ℝ EG ≤ finrank ℝ E := horb ▸ Submodule.finrank_le _
  have hker_dim :
      finrank ℝ (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M)) x).ker = finrank ℝ EG := by
    have hadd := LinearMap.finrank_range_add_finrank_ker
      (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M)) x).toLinearMap
    have hrange : LinearMap.range
        (mfderiv I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
          (Quotient.mk (MulAction.orbitRel G M)) x).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.2 (surjective_mfderiv_quotientMk_freeProperQuotient IG G I M x)
    have hcod : finrank ℝ (TangentSpace 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
        (Quotient.mk (MulAction.orbitRel G M) x)) = finrank ℝ E - finrank ℝ EG :=
      finrank_fin_fun ℝ
    have hdom : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
    rw [hrange, finrank_top, hcod, hdom] at hadd
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [horb, hker_dim])).symm

include IG in
/-- **The quotient manifold theorem.** The orbit space of a free proper smooth action of a
finite-dimensional real Lie group `G` on a finite-dimensional boundaryless smooth real manifold `M`
admits a smooth atlas of dimension `dim M - dim G`, retaining its quotient topology, for which the
orbit projection is a smooth submersion. Neither manifold needs to be assumed Hausdorff or second
countable, and `M` may be empty. -/
theorem exists_freeProperQuotient_isSubmersion :
    ∃ cs : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M),
      letI := cs
      IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞ (MulAction.orbitRel.Quotient G M) ∧
      IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) :=
  ⟨freeProperQuotientChartedSpace IG G I M,
    isManifold_freeProperQuotient IG G I M,
    isSubmersion_quotientMk_freeProperQuotient IG G I M⟩

/-! ### Arbitrary slice charts and smooth local trivializations -/

/-- Any transverse injective slice into `M` induces a smooth local diffeomorphism into the free
proper quotient manifold `M ⧸ G`. -/
theorem isLocalDiffeomorph_quotientMk_slice
    {FS : Type*} [NormedAddCommGroup FS] [NormedSpace ℝ FS]
    {KS : Type*} [TopologicalSpace KS] {JS : ModelWithCorners ℝ FS KS}
    {S : Type*} [TopologicalSpace S] [ChartedSpace KS S]
    {σ : S → M} {U : TopologicalSpace.Opens S}
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ (U : Set S)))
    (hloc : IsLocalDiffeomorphOn (IG.prod JS) I ∞ (fun p : G × S ↦ p.1 • σ p.2)
      (univ ×ˢ (U : Set S))) :
    letI := freeProperQuotientChartedSpace IG G I M
    IsLocalDiffeomorph JS 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (fun s : U ↦ Quotient.mk (MulAction.orbitRel G M) (σ s)) :=
  letI := freeProperQuotientChartedSpace IG G I M
  isLocalDiffeomorph_quotientMk_slice_of_isSubmersion
    (isSubmersion_quotientMk_freeProperQuotient IG G I M) hinj hloc

/-- **Smooth principal-bundle local trivializations.** Around every point `x : M`, the orbit
projection `M → M ⧸ G` admits a smooth `G`-equivariant partial diffeomorphism
`Φ : M → (M ⧸ G) × G` over an open neighbourhood `W` of `[x]`, sending `y ∈ π⁻¹ W` to
`([y], (Φ y).2)` and intertwining `g • y` with left multiplication `g * ·` on `G`. -/
theorem exists_smoothOrbitTrivialization (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    ∃ (W : Set (MulAction.orbitRel.Quotient G M)),
      IsOpen W ∧ Quotient.mk (MulAction.orbitRel G M) x ∈ W ∧
      ∃ Φ : PartialDiffeomorph I (𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ).prod IG) M
          (MulAction.orbitRel.Quotient G M × G) ∞,
        Φ.source = Quotient.mk (MulAction.orbitRel G M) ⁻¹' W ∧
        Φ.target = W ×ˢ univ ∧
        (∀ y, (Φ y).1 = Quotient.mk (MulAction.orbitRel G M) y) ∧
        (Φ x).2 = 1 ∧
        ∀ (g : G), ∀ y ∈ Φ.source, Φ (g • y) = ((Φ y).1, g * (Φ y).2) := by
  let := freeProperQuotientChartedSpace IG G I M
  obtain ⟨W, hW, hxW, u, hu, hux, hu_smul⟩ :=
    exists_contMDiffOn_smul_eq_mul_of_stabilizer_eq_bot (IG := IG) (I := I) x
      (isCancelSMul_iff_stabilizer_eq_bot.mp ‹_› x)
  exact ⟨W, hW, hxW,
    orbitTrivializationPartialDiffeomorph (isSubmersion_quotientMk_freeProperQuotient IG G I M)
      W hW u hu hu_smul,
    orbitTrivializationPartialDiffeomorph_source _ W hW u hu hu_smul,
    orbitTrivializationPartialDiffeomorph_target _ W hW u hu hu_smul,
    fun y ↦ by simp,
    by simp [hux],
    fun g y hy ↦ orbitTrivializationPartialDiffeomorph_apply_smul
      (isSubmersion_quotientMk_freeProperQuotient IG G I M) W hW u hu hu_smul g
      (mem_preimage.1 (by simpa only [orbitTrivializationPartialDiffeomorph_source] using hy))⟩

/-! ### Smooth descent along the free proper quotient -/

section Descent

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  {f : M → N} {hf : ∀ (g : G) (x : M), f (g • x) = f x} {m : ℕ∞ω}

/-- A `G`-invariant map descends to a map that is `C^m` at the orbit `[x]` (for `m ≤ ∞`) exactly
when the original map is `C^m` at `x`. -/
theorem contMDiffAt_freeProperQuotientLift_iff (hm : m ≤ ∞) (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) IN m
      (MulAction.orbitRelQuotientLift f hf) (Quotient.mk (MulAction.orbitRel G M) x) ↔
      ContMDiffAt I IN m f x := by
  let := freeProperQuotientChartedSpace IG G I M
  rw [← ((isSubmersion_quotientMk_freeProperQuotient IG G I M).isSubmersionAt
      x).contMDiffAt_comp_iff hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- A `G`-invariant map descends to a `C^m` map on the free proper quotient (for `m ≤ ∞`) exactly
when the original map is `C^m`. -/
theorem contMDiff_freeProperQuotientLift_iff (hm : m ≤ ∞) :
    letI := freeProperQuotientChartedSpace IG G I M
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) IN m
      (MulAction.orbitRelQuotientLift f hf) ↔ ContMDiff I IN m f := by
  let := freeProperQuotientChartedSpace IG G I M
  rw [← (isSubmersion_quotientMk_freeProperQuotient IG G I M).contMDiff_comp_iff
      Quotient.mk_surjective hm, MulAction.orbitRelQuotientLift_comp_mk]

/-- A `G`-invariant map into a finite-dimensional boundaryless smooth manifold descends to a smooth
immersion on the free proper quotient exactly when it is smooth and its differential kills precisely
the orbit tangent space `𝔤 · x` at every point `x : M`. -/
theorem isImmersion_freeProperQuotientLift_iff [FiniteDimensional ℝ EN] [IN.Boundaryless]
    [IsManifold IN ∞ N] :
    letI := freeProperQuotientChartedSpace IG G I M
    IsImmersion 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) IN ∞
      (MulAction.orbitRelQuotientLift f hf) ↔
      ContMDiff I IN ∞ f ∧
        ∀ x, (mfderiv I IN f x).ker =
          (InfinitesimalAction.fundamental IG G I M).orbitTangent x := by
  let := freeProperQuotientChartedSpace IG G I M
  have := isManifold_freeProperQuotient IG G I M
  rw [(isSubmersion_quotientMk_freeProperQuotient IG G I M).isImmersion_iff_ker_mfderiv_comp
      Quotient.mk_surjective (by simp), MulAction.orbitRelQuotientLift_comp_mk]
  simp_rw [ker_mfderiv_quotientMk_freeProperQuotient IG G I M]

/-- An equivariant `C^m` map (`m ≤ ∞`) between two free proper Lie group actions descends to a `C^m`
map between their quotient manifolds. -/
theorem contMDiff_freeProperQuotientMap
    {EG' : Type*} [NormedAddCommGroup EG'] [NormedSpace ℝ EG'] [FiniteDimensional ℝ EG']
    {HG' : Type*} [TopologicalSpace HG'] (IG' : ModelWithCorners ℝ EG' HG')
    (G' : Type*) [TopologicalSpace G'] [ChartedSpace HG' G'] [Group G'] [LieGroup IG' ∞ G']
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [I'.Boundaryless]
    (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [MulAction G' M'] [ContMDiffSMul IG' I' ∞ G' M'] [ProperSMul G' M'] [IsCancelSMul G' M']
    {σ : G → G'} {φ : M →ₑ[σ] M'} (hm : m ≤ ∞) (hφ : ContMDiff I I' m φ) :
    letI := freeProperQuotientChartedSpace IG G I M
    letI := freeProperQuotientChartedSpace IG' G' I' M'
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' - finrank ℝ EG') → ℝ) m
      (MulActionHom.orbitRelQuotientMap φ) := by
  let := freeProperQuotientChartedSpace IG G I M
  let := freeProperQuotientChartedSpace IG' G' I' M'
  rw [← (isSubmersion_quotientMk_freeProperQuotient IG G I M).contMDiff_comp_iff
      Quotient.mk_surjective hm, MulActionHom.orbitRelQuotientMap_comp_mk]
  exact ((contMDiff_quotientMk_freeProperQuotient IG' G' I' M').of_le hm).comp hφ

end Descent

/-! ### Universal property, uniqueness and comparisons -/

section Uniqueness

/-- **Universal diffeomorphism characterization of the free proper quotient.** If `p : M → N` is a
surjective smooth submersion whose fibres are precisely the `G`-orbits, then `p` induces a smooth
diffeomorphism `M ⧸ G ≃ₘ^∞ N`. -/
def freeProperQuotientDiffeomorphOfIsSubmersion
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (p : M → N) (hp : IsSubmersion I IN ∞ p) (hp_surj : Surjective p)
    (hp_fib : ∀ x y : M, p x = p y ↔ MulAction.orbitRel G M x y) :
    letI := freeProperQuotientChartedSpace IG G I M
    MulAction.orbitRel.Quotient G M ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ), IN⟯ N :=
  letI := freeProperQuotientChartedSpace IG G I M
  have hinv : ∀ (g : G) (x : M), p (g • x) = p x :=
    fun g x ↦ (hp_fib _ _).2 ⟨g, rfl⟩
  have hbij : Bijective (MulAction.orbitRelQuotientLift p hinv) :=
    ⟨fun q₁ q₂ hq ↦ by
        induction q₁ using Quotient.inductionOn with
        | h x =>
          induction q₂ using Quotient.inductionOn with
          | h y =>
            rw [MulAction.orbitRelQuotientLift_mk, MulAction.orbitRelQuotientLift_mk] at hq
            exact Quotient.sound ((hp_fib x y).1 hq),
      fun y ↦ let ⟨x, hx⟩ := hp_surj y; ⟨Quotient.mk _ x, by
        rw [MulAction.orbitRelQuotientLift_mk]
        exact hx⟩⟩
  (Equiv.ofBijective (MulAction.orbitRelQuotientLift p hinv) hbij).diffeomorphOfSubmersions
    (isSubmersion_quotientMk_freeProperQuotient IG G I M)
    Quotient.mk_surjective hp hp_surj MulAction.orbitRelQuotientLift_comp_mk

/-- `freeProperQuotientDiffeomorphOfIsSubmersion` sends the orbit `[x]` to `p x`. -/
@[simp]
theorem freeProperQuotientDiffeomorphOfIsSubmersion_apply_mk
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (p : M → N) (hp : IsSubmersion I IN ∞ p) (hp_surj : Surjective p)
    (hp_fib : ∀ x y : M, p x = p y ↔ MulAction.orbitRel G M x y) (x : M) :
    freeProperQuotientDiffeomorphOfIsSubmersion IG G I M p hp hp_surj hp_fib
      (Quotient.mk (MulAction.orbitRel G M) x) = p x := by
  let := freeProperQuotientChartedSpace IG G I M
  exact (Equiv.diffeomorphOfSubmersions_apply _ _ _ _ _ _ _).trans
    (MulAction.orbitRelQuotientLift_mk x)

/-- **Uniqueness up to identity diffeomorphism.** Any other charted-space structure on `M ⧸ G`
(even with a different model) for which the orbit projection is a smooth submersion is smoothly
diffeomorphic to `TauCeti.freeProperQuotientChartedSpace` by the identity. -/
theorem exists_diffeomorph_freeProperQuotient_apply_eq_self
    {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
    {HQ : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ}
    (b : ChartedSpace HQ (MulAction.orbitRel.Quotient G M))
    (hb : letI := b; IsSubmersion I IQ ∞ (Quotient.mk (MulAction.orbitRel G M))) :
    ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) IQ
        (MulAction.orbitRel.Quotient G M) _ (freeProperQuotientChartedSpace IG G I M)
        (MulAction.orbitRel.Quotient G M) _ b ∞,
      ∀ q, e q = q :=
  ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion
    (freeProperQuotientChartedSpace IG G I M) b Quotient.mk_surjective
    (isSubmersion_quotientMk_freeProperQuotient IG G I M) hb

/-- **Uniqueness of the maximal atlas.** Any smooth manifold atlas on `M ⧸ G` with the same model
`Fin (dim M - dim G) → ℝ` making the orbit projection a smooth submersion has the same maximal
smooth atlas as `TauCeti.freeProperQuotientChartedSpace`. -/
theorem maximalAtlas_freeProperQuotient_eq
    (b : ChartedSpace (Fin (finrank ℝ E - finrank ℝ EG) → ℝ) (MulAction.orbitRel.Quotient G M))
    (hmb : letI := b; IsManifold 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (MulAction.orbitRel.Quotient G M))
    (hb : letI := b; IsSubmersion I 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
      (Quotient.mk (MulAction.orbitRel G M))) :
    (letI := freeProperQuotientChartedSpace IG G I M;
      IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
        (MulAction.orbitRel.Quotient G M)) =
      (letI := b;
        IsManifold.maximalAtlas 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) ∞
          (MulAction.orbitRel.Quotient G M)) :=
  ChartedSpace.maximalAtlas_eq_of_isSubmersion (freeProperQuotientChartedSpace IG G I M) b
    Quotient.mk_surjective (isManifold_freeProperQuotient IG G I M) hmb
    (isSubmersion_quotientMk_freeProperQuotient IG G I M) hb

/-- **Agreement with the discrete-action quotient atlas.** When the action is also properly
discontinuous, `TauCeti.freeProperQuotientChartedSpace` and Mathlib's
`MulAction.instChartedSpaceQuotient` are smoothly diffeomorphic by the identity. -/
theorem exists_diffeomorph_freeProperQuotient_discrete_apply_eq_self
    [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [T2Space M] [LocallyCompactSpace M] :
    ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
        𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ) I
        (MulAction.orbitRel.Quotient G M) _ (freeProperQuotientChartedSpace IG G I M)
        (MulAction.orbitRel.Quotient G M) _ MulAction.instChartedSpaceQuotient ∞,
      ∀ q, e q = q := by
  have : ContMDiffConstSMul I ∞ G M :=
    ⟨fun g ↦ ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := I) (n := ∞) g⟩
  have hsubm : IsSubmersion I I ∞ (Quotient.mk (MulAction.orbitRel G M)) :=
    (isSubmersionOfComplement_iff (F := Unit).2 fun x ↦
      (isLocalDiffeomorph_quotientMk (I := I) (n := ∞) (G := G) x).isSubmersionAtOfComplement_comp
        (IsSubmersionOfComplement.id.isSubmersionAt _)).isSubmersion
  exact exists_diffeomorph_freeProperQuotient_apply_eq_self IG G I M
    MulAction.instChartedSpaceQuotient hsubm

/-- **Trivial-group specialization.** When `G` is trivial, the free proper quotient `M ⧸ G` is
canonically smoothly diffeomorphic to `M`, sending `[x]` to `x`. -/
def freeProperQuotientDiffeomorphSelf [Subsingleton G] :
    letI := freeProperQuotientChartedSpace IG G I M
    MulAction.orbitRel.Quotient G M ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ EG) → ℝ), I⟯ M :=
  freeProperQuotientDiffeomorphOfIsSubmersion IG G I M id IsSubmersion.id surjective_id
    fun x y ↦ ⟨fun h ↦ ⟨1, (one_smul G y).trans h.symm⟩,
      fun ⟨g, hg⟩ ↦ by simpa [Subsingleton.elim g 1] using hg.symm⟩

/-- `freeProperQuotientDiffeomorphSelf` sends `[x]` to `x`. -/
@[simp]
theorem freeProperQuotientDiffeomorphSelf_apply_mk [Subsingleton G] (x : M) :
    freeProperQuotientDiffeomorphSelf IG G I M (Quotient.mk (MulAction.orbitRel G M) x) = x :=
  freeProperQuotientDiffeomorphOfIsSubmersion_apply_mk IG G I M id IsSubmersion.id surjective_id
    _ x

/-- The inverse of `freeProperQuotientDiffeomorphSelf` is the orbit projection. -/
@[simp]
theorem freeProperQuotientDiffeomorphSelf_symm_apply [Subsingleton G] (x : M) :
    letI := freeProperQuotientChartedSpace IG G I M
    (freeProperQuotientDiffeomorphSelf IG G I M).symm x =
      Quotient.mk (MulAction.orbitRel G M) x := by
  let := freeProperQuotientChartedSpace IG G I M
  exact (freeProperQuotientDiffeomorphSelf IG G I M).injective (by simp)

end Uniqueness

end QuotientManifold

end TauCeti
