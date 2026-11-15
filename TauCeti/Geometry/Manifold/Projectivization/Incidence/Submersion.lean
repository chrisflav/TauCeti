/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Manifold.Projectivization.Incidence.Universal
public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
public import TauCeti.Topology.Algebra.Projectivization.Incidence

import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# Full-rank projective incidence families and their proper submersions

Let `c : B → ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)` be a `C^r` (`1 ≤ r`) family of
homogeneous polynomial tuples parametrized by a boundaryless `C^r` manifold `B` over `𝕜` (`ℝ` or
`ℂ`, with complete model space `EB`), and suppose that `c b` lies in the full-rank parameter locus
`TauCeti.complexProjectiveFullRankParams (n + 1) d` for every `b : B`: at every solution point of
the projective zero locus of `c b`, the cone Jacobian is surjective.

Around any incidence point `(b₀, L₀) ∈ complexProjectiveFamily c` with `L₀ ∈ affineOpen i`, the
vertical derivative of the ratio-chart equations `a ↦ projectiveIncidenceChartEquations i a (c b₀)`
at `affineChart i L₀` is surjective. Splitting `Fin n → ℂ` into its kernel
`Fin (n - |ι|) → ℂ` and the equation space `ι → ℂ`, the combined coordinate map
`(u, a) ↦ ((u, P a), projectiveIncidenceChartEquations i a (c (e_B⁻¹ u)))` has an upper-triangular
block derivative over `𝕜` with an explicit continuous linear inverse—requiring no
finite-dimensionality of `EB`. Applying `TauCeti.ContDiffOn.exists_openPartialHomeomorph` yields
ambient `C^r` slice charts (`TauCeti.ComplexProjectiveFamily.sliceChartAt`) that simultaneously:

* flatten `complexProjectiveFamily c ⊆ B × ℙ ℂ (Fin (n + 1) → ℂ)` onto `univ ×ˢ {0}`, equipping
  `complexProjectiveFamily c` with a boundaryless `C^r` manifold structure
  (`TauCeti.ComplexProjectiveFamily.chartedSpace`, `TauCeti.ComplexProjectiveFamily.isManifold`)
  modelled on `EB × (Fin (n - |ι|) → ℂ)` for which the ambient inclusion is a `C^r` smooth
  embedding with normal model `ι → ℂ`
  (`TauCeti.ComplexProjectiveFamily.isSmoothEmbedding_subtypeVal`); and
* preserve the base coordinate `(extChartAt IB b₀) b` in the first component, making the projection
  `complexProjectiveFamily c → B` a proper `C^r` submersion with fiber model
  `Fin (n - |ι|) → ℂ` (`TauCeti.ComplexProjectiveFamily.isSubmersionOfComplement_fst`,
  `TauCeti.ComplexProjectiveFamily.isSubmersion_fst`).

Specializing `c` to the open inclusion of `TauCeti.complexProjectiveFullRankParamsOpens (n + 1) d`
at analytic regularity `r = ω` over `ℂ` equips the universal full-rank family
`TauCeti.complexProjectiveFullRankFamily (n + 1) d` with a global complex analytic (and real
smooth) `ChartedSpace` instance whose projection to `complexProjectiveFullRankParamsOpens (n + 1) d`
is a proper holomorphic (and real `C^r`) submersion.

Finally, the submanifold universal property upgrades the topological comparisons of
`TauCeti.Topology.Algebra.Projectivization.Incidence`:

* the classifying map `complexProjectiveFamily c → complexProjectiveIncidence (n + 1) d` and smooth
  reparametrization `ComplexProjectiveFamily.baseChange c f` are `C^r`;
* for each `b : B`, the inclusion of `complexProjectiveZeroLocus` into `complexProjectiveFamily c`
  is a `C^r` embedding (holomorphic when `𝕜 = ℂ, r = ω`), and over finite-dimensional real bases
  `ComplexProjectiveFamily.fiberHomeomorph c b` upgrades to a `C^r` diffeomorphism onto the regular
  fiber (`TauCeti.ComplexProjectiveFamily.fiberDiffeomorph`);
* over finite-dimensional real bases, `ComplexProjectiveFamily.pullbackHomeomorph` upgrades to a
  `C^r` diffeomorphism between `complexProjectiveFamily (c ∘ f)` and the transverse fiber product
  `{z : A × complexProjectiveFamily c // f z.1 = z.2.1.1}`
  (`TauCeti.ComplexProjectiveFamily.pullbackDiffeomorph`).

## Main declarations

* `TauCeti.ComplexProjectiveFamily.chartedSpace`, `TauCeti.ComplexProjectiveFamily.isManifold`,
  `TauCeti.ComplexProjectiveFamily.isSmoothEmbedding_subtypeVal`: submanifold structure and ambient
  embedding of a full-rank `C^r` projective incidence family.
* `TauCeti.ComplexProjectiveFamily.isSubmersionOfComplement_fst`,
  `TauCeti.ComplexProjectiveFamily.isSubmersion_fst`: the family projection to `B` is a `C^r`
  submersion with complement `Fin (n - |ι|) → ℂ`.
* `TauCeti.complexProjectiveFullRankFamily`,
  `TauCeti.instChartedSpaceComplexProjectiveFullRankFamily`,
  `TauCeti.isSubmersion_fst_complexProjectiveFullRankFamily`: global complex analytic manifold
  structure and proper submersion of the universal full-rank family.
* `TauCeti.ComplexProjectiveFamily.isSmoothEmbedding_fiberInclusion`,
  `TauCeti.ComplexProjectiveFamily.fiberDiffeomorph`,
  `TauCeti.ComplexProjectiveFamily.pullbackDiffeomorph`: smooth/holomorphic fiber embedding and
  regular-fiber / transverse-fiber-product diffeomorphisms.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §2, for holomorphic
  submersions and families of projective submanifolds.
* C. Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Chapter 9, for proper smooth
  families of projective varieties.
-/

public section

open Filter Function Module MvPolynomial Projectivization Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization Topology

namespace TauCeti

/-! ### Scalar restriction for complex zero-locus embeddings -/

section ZeroLocusRestrictScalars

variable {ι : Type*} [Fintype ι] {n : ℕ} {d : ι → ℕ}
  {p : ι → MvPolynomial (Fin (n + 1)) ℂ}

private theorem isImmersionAtOfComplement_restrictScalars
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {E E' F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E]
    [IsScalarTower 𝕜 ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace 𝕜 E']
    [IsScalarTower 𝕜 ℂ E'] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F]
    [IsScalarTower 𝕜 ℂ F] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace E' N] {r : ℕ∞ω}
    [IsManifold 𝓘(ℂ, E) r M] [IsManifold 𝓘(ℂ, E') r N] {f : M → N} {x : M}
    (h : Manifold.IsImmersionAtOfComplement F 𝓘(ℂ, E) 𝓘(ℂ, E') r f x) :
    Manifold.IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E') r f x := by
  have : IsManifold 𝓘(𝕜, E) r M := (‹IsManifold 𝓘(ℂ, E) r M›).restrictScalars 𝕜
  have : IsManifold 𝓘(𝕜, E') r N := (‹IsManifold 𝓘(ℂ, E') r N›).restrictScalars 𝕜
  have hdom := (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).1 h.domChart_mem_maximalAtlas
  have hcod := (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).1 h.codChart_mem_maximalAtlas
  have hdom' : h.domChart ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) r M := by
    rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    have h1 := hdom.1.restrictScalars 𝕜
    have h2 := hdom.2.restrictScalars 𝕜
    rw [modelWithCornersSelf_restrictScalars] at h1 h2
    exact ⟨h1, h2⟩
  have hcod' : h.codChart ∈ IsManifold.maximalAtlas 𝓘(𝕜, E') r N := by
    rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    have h1 := hcod.1.restrictScalars 𝕜
    have h2 := hcod.2.restrictScalars 𝕜
    rw [modelWithCornersSelf_restrictScalars] at h1 h2
    exact ⟨h1, h2⟩
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts (h.equiv.restrictScalars' 𝕜)
    h.domChart h.codChart h.mem_domChart_source h.mem_codChart_source hdom' hcod'
    h.source_subset_preimage_source fun u hu ↦ ?_
  have hu' : u ∈ (h.domChart.extend 𝓘(ℂ, E)).target := by simpa using hu
  simpa using h.writtenInCharts hu'

/-- The inclusion of the smooth part of a complex projective zero locus into `ℂℙⁿ` is a `C^r`
embedding over any normed base field `𝕜` acting on `ℂ` (in particular over `ℂ` and `ℝ`). -/
theorem isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus_of_normedAlgebra
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (hp : ∀ k, (p k).IsHomogeneous (d k)) {s V : Set (ℙ ℂ (Fin (n + 1) → ℂ))}
    (hV : IsOpen V) (hs : s = complexProjectiveZeroLocus p ∩ V)
    (hrank : ∀ L ∈ s, Surjective (jacobiMatrixAt p L.rep).mulVec) (r : ℕ∞ω) :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    Manifold.IsSmoothEmbedding 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ) 𝓘(𝕜, Fin n → ℂ) r
      (Subtype.val : s → ℙ ℂ (Fin (n + 1) → ℂ)) := by
  let := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
  have := isManifold_complexProjectiveZeroLocus hp hV hs hrank r
  have himm : Manifold.IsImmersionOfComplement (ι → ℂ) 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ)
      𝓘(𝕜, Fin n → ℂ) r (Subtype.val : s → ℙ ℂ (Fin (n + 1) → ℂ)) := fun x ↦
    isImmersionAtOfComplement_restrictScalars
      (isImmersionOfComplement_subtypeVal_complexProjectiveZeroLocus hp hV hs hrank r x)
  exact ⟨himm.isImmersion, Topology.IsEmbedding.subtypeVal⟩

end ZeroLocusRestrictScalars

namespace ComplexProjectiveFamily

/-! ### Set-theoretic classifying and fiber maps -/

section Maps

variable {ι B : Type*} {N : ℕ} {d : ι → ℕ}

/-- The classifying map sending an incidence pair `(b, L)` of `complexProjectiveFamily c` to
`(c b, L)` in the universal incidence variety `complexProjectiveIncidence N d`. -/
def classifyingMap (c : B → ∀ k, homogeneousSubmodule (Fin N) ℂ (d k))
    (x : complexProjectiveFamily c) : complexProjectiveIncidence N d :=
  ⟨(c x.1.1, x.1.2), mem_complexProjectiveIncidence.mpr (mem_complexProjectiveFamily.mp x.2)⟩

@[simp]
theorem coe_classifyingMap (c : B → ∀ k, homogeneousSubmodule (Fin N) ℂ (d k))
    (x : complexProjectiveFamily c) :
    (classifyingMap c x :
      (∀ k, homogeneousSubmodule (Fin N) ℂ (d k)) × ℙ ℂ (Fin N → ℂ)) =
      (c x.1.1, x.1.2) :=
  (rfl)

/-- Inclusion of the projective zero locus at `b` into the total space `complexProjectiveFamily c`
over `b`. -/
def fiberInclusion [TopologicalSpace B] (c : B → ∀ k, homogeneousSubmodule (Fin N) ℂ (d k)) (b : B)
    (L : complexProjectiveZeroLocus fun k ↦ (c b k : MvPolynomial (Fin N) ℂ)) :
    complexProjectiveFamily c :=
  (fiberHomeomorph c b L).1

@[simp]
theorem coe_fiberInclusion [TopologicalSpace B]
    (c : B → ∀ k, homogeneousSubmodule (Fin N) ℂ (d k)) (b : B)
    (L : complexProjectiveZeroLocus fun k ↦ (c b k : MvPolynomial (Fin N) ℂ)) :
    (fiberInclusion c b L : B × ℙ ℂ (Fin N → ℂ)) = (b, L.1) :=
  coe_fiberHomeomorph_apply c b L

end Maps

/-! ### Parametric chart equations and upper-triangular coordinate equivalences -/

section Aux

variable {ι : Type*} {n : ℕ}

private abbrev CoeffSpace (n : ℕ) (d : ι → ℕ) :=
  ∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ

private noncomputable def evalChartEqns (d : ι → ℕ) (i : Fin (n + 1)) :
    (Fin n → ℂ) × CoeffSpace n d → ι → ℂ :=
  fun q ↦ projectiveIncidenceChartEquations i q.1 ((homogeneousFamilyCoeffEquiv d).symm q.2)

private theorem evalChartEqns_apply (d : ι → ℕ) (i : Fin (n + 1)) (a : Fin n → ℂ)
    (c : ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) :
    evalChartEqns d i (a, homogeneousFamilyCoeffEquiv d c) =
      projectiveIncidenceChartEquations i a c := by
  simp [evalChartEqns]

private theorem contDiff_evalChartEqns [Fintype ι] (d : ι → ℕ) (i : Fin (n + 1))
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (r : ℕ∞ω) :
    ContDiff 𝕜 r (evalChartEqns d i) :=
  ((contDiff_iff_contDiffAt.2 fun q ↦
    (analyticAt_projectiveIncidenceChartEquations_comp
      (homogeneousFamilyCoeffEquiv d).symm.toContinuousLinearMap i q).contDiffAt :
      ContDiff ℂ r (evalChartEqns d i))).restrict_scalars 𝕜

private theorem hasFDerivAt_projectiveIncidenceChartEquations_left [Finite ι]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {d : ι → ℕ} (i : Fin (n + 1))
    (c₀ : ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) (a₀ : Fin n → ℂ) :
    HasFDerivAt (fun a ↦ projectiveIncidenceChartEquations i a c₀)
      ((fderiv ℂ (fun a ↦ projectiveIncidenceChartEquations i a c₀) a₀).restrictScalars 𝕜) a₀ := by
  cases nonempty_fintype ι
  have heq : (fun a ↦ projectiveIncidenceChartEquations i a c₀) =
      fun a ↦ evalChartEqns d i (a, homogeneousFamilyCoeffEquiv d c₀) := by
    funext a
    exact (evalChartEqns_apply d i a c₀).symm
  have hdiff : DifferentiableAt ℂ (fun a ↦ projectiveIncidenceChartEquations i a c₀) a₀ := by
    rw [heq]
    exact ((contDiff_evalChartEqns (𝕜 := ℂ) d i 1).contDiffAt.differentiableAt one_ne_zero).comp a₀
      (differentiableAt_id.prodMk (differentiableAt_const _))
  exact hdiff.hasFDerivAt.restrictScalars 𝕜

private theorem surjective_fderiv_vertical [Finite ι] {B : Type*} {d : ι → ℕ}
    {c : B → ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)}
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) {i : Fin (n + 1)} (hi : z.1.2 ∈ affineOpen i) :
    Surjective (fderiv ℂ (fun a ↦ projectiveIncidenceChartEquations i a (c z.1.1))
      (affineChart i z.1.2)) := by
  cases nonempty_fintype ι
  have hmem := mem_complexProjectiveFamily.mp z.2
  have hjac := (mem_complexProjectiveFullRankParams_iff_forall_zeroLocus.mp (hrank z.1.1))
    z.1.2 hmem
  have hiff := surjective_fderiv_eval_dehomogenize_affineChart_iff i
    (fun k ↦ (mem_homogeneousSubmodule _ _).mp (c z.1.1 k).2) hmem hi
  simpa only [projectiveIncidenceChartEquations_apply] using hiff.mpr hjac

/-- The block upper-triangular continuous linear equivalence
`(u, a) ↦ ((u, (α a).1), B u + (α a).2)` with explicit inverse
`((w, v), y) ↦ (w, α⁻¹ (v, y - B w))`. -/
private def upperTriangularEquiv {𝕜 EB W V Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (α : W ≃L[𝕜] V × Y) (B : EB →L[𝕜] Y) :
    (EB × W) ≃L[𝕜] (EB × V) × Y :=
  let u := ContinuousLinearMap.fst 𝕜 EB W
  let αa := α.toContinuousLinearMap.comp (ContinuousLinearMap.snd 𝕜 EB W)
  let L : (EB × W) →L[𝕜] (EB × V) × Y :=
    (u.prod ((ContinuousLinearMap.fst 𝕜 V Y).comp αa)).prod
      (B.comp u + (ContinuousLinearMap.snd 𝕜 V Y).comp αa)
  let p₁ := ContinuousLinearMap.fst 𝕜 (EB × V) Y
  let p₂ := ContinuousLinearMap.snd 𝕜 (EB × V) Y
  let w := (ContinuousLinearMap.fst 𝕜 EB V).comp p₁
  let v := (ContinuousLinearMap.snd 𝕜 EB V).comp p₁
  let R : ((EB × V) × Y) →L[𝕜] EB × W :=
    w.prod (α.symm.toContinuousLinearMap.comp (v.prod (p₂ - B.comp w)))
  ContinuousLinearEquiv.equivOfInverse L R
    (fun p ↦ by simp [L, R, u, αa, p₁, p₂, w, v])
    (fun q ↦ by simp [L, R, u, αa, p₁, p₂, w, v])

@[simp]
private theorem upperTriangularEquiv_apply {𝕜 EB W V Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (α : W ≃L[𝕜] V × Y) (B : EB →L[𝕜] Y) (p : EB × W) :
    upperTriangularEquiv α B p = ((p.1, (α p.2).1), B p.1 + (α p.2).2) :=
  (rfl)

private noncomputable def baseChart {𝕜 EB HB B : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
    {IB : ModelWithCorners 𝕜 EB HB} [IB.Boundaryless]
    [TopologicalSpace B] [ChartedSpace HB B] (b₀ : B) : OpenPartialHomeomorph B EB :=
  (chartAt HB b₀).transHomeomorph IB.toHomeomorph

private theorem baseChart_toPartialEquiv {𝕜 EB HB B : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
    {IB : ModelWithCorners 𝕜 EB HB} [IB.Boundaryless]
    [TopologicalSpace B] [ChartedSpace HB B] (b₀ : B) :
    (baseChart (IB := IB) b₀).toPartialEquiv = extChartAt IB b₀ := by
  apply PartialEquiv.ext
  · intro _; rfl
  · intro _; rfl
  · simp [baseChart]

private theorem baseChart_target {𝕜 EB HB B : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
    {IB : ModelWithCorners 𝕜 EB HB} [IB.Boundaryless]
    [TopologicalSpace B] [ChartedSpace HB B] (b₀ : B) :
    (baseChart (IB := IB) b₀).target = (extChartAt IB b₀).target :=
  congrArg PartialEquiv.target (baseChart_toPartialEquiv (IB := IB) b₀)

end Aux

/-! ### Parametric slice charts and submanifold structure -/

section ParametricSlice

variable {ι : Type*} [Fintype ι] {n : ℕ} {d : ι → ℕ}
  {𝕜 EB HB B : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [CompleteSpace EB]
  [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [IB.Boundaryless]
  [TopologicalSpace B] [ChartedSpace HB B]
  {r : ℕ∞ω} [IsManifold IB r B]
  {c : B → ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)}

/-- Splitting `Fin n → ℂ` at an incidence point `z` into the vertical tangent space
`Fin (n - |ι|) → ℂ` and the equation values `ι → ℂ`. -/
private noncomputable def verticalSplit
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) {i : Fin (n + 1)} (hi : z.1.2 ∈ affineOpen i) :
    (Fin n → ℂ) ≃L[ℂ] (Fin (n - Fintype.card ι) → ℂ) × (ι → ℂ) := by
  let D := fderiv ℂ (fun a ↦ projectiveIncidenceChartEquations i a (c z.1.1))
    (affineChart i z.1.2)
  have hsurj : Surjective D := surjective_fderiv_vertical hrank z hi
  have hD : D.range = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hker : D.ker.ClosedComplemented := D.ker_closedComplemented_of_finiteDimensional_range
  have hdim : Module.finrank ℂ D.ker = Module.finrank ℂ (Fin (n - Fintype.card ι) → ℂ) := by
    have h := LinearMap.finrank_range_add_finrank_ker (D : (Fin n → ℂ) →ₗ[ℂ] ι → ℂ)
    rw [hD, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun] at h
    rw [Module.finrank_fin_fun]
    omega
  exact (D.implicitCoordEquiv hD hker).trans
    ((ContinuousLinearEquiv.prodComm ℂ _ _).trans
      ((ContinuousLinearEquiv.ofFinrankEq hdim).prodCongr (ContinuousLinearEquiv.refl ℂ _)))

omit [TopologicalSpace B] in
@[simp]
private theorem verticalSplit_apply_snd
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) {i : Fin (n + 1)} (hi : z.1.2 ∈ affineOpen i)
    (v : Fin n → ℂ) :
    (verticalSplit hrank z hi v).2 =
      fderiv ℂ (fun a ↦ projectiveIncidenceChartEquations i a (c z.1.1))
        (affineChart i z.1.2) v := by
  simp [verticalSplit]

private noncomputable def ambCoordChart (b₀ : B) (i : Fin (n + 1)) :
    OpenPartialHomeomorph (B × ℙ ℂ (Fin (n + 1) → ℂ)) (EB × (Fin n → ℂ)) :=
  (baseChart (IB := IB) b₀).prod (affineOpenPartialHomeomorph i)

omit [NormedAlgebra 𝕜 ℂ] [CompleteSpace EB] in
private theorem ambCoordChart_source (b₀ : B) (i : Fin (n + 1)) :
    (ambCoordChart (IB := IB) b₀ i).source =
      (baseChart (IB := IB) b₀).source ×ˢ affineOpen i := by
  simp [ambCoordChart]

omit [NormedAlgebra 𝕜 ℂ] [CompleteSpace EB] in
private theorem ambCoordChart_target (b₀ : B) (i : Fin (n + 1)) :
    (ambCoordChart (IB := IB) b₀ i).target =
      (baseChart (IB := IB) b₀).target ×ˢ univ := by
  simp [ambCoordChart]

omit [NormedAlgebra 𝕜 ℂ] [CompleteSpace EB] in
private theorem ambCoordChart_apply (b₀ : B) (i : Fin (n + 1))
    (p : B × ℙ ℂ (Fin (n + 1) → ℂ)) :
    ambCoordChart (IB := IB) b₀ i p =
      (baseChart (IB := IB) b₀ p.1, affineChart i p.2) := by
  simp [ambCoordChart]

omit [NormedAlgebra 𝕜 ℂ] [CompleteSpace EB] in
private theorem ambCoordChart_symm_apply (b₀ : B) (i : Fin (n + 1))
    (q : EB × (Fin n → ℂ)) :
    (ambCoordChart (IB := IB) b₀ i).symm q =
      ((baseChart (IB := IB) b₀).symm q.1, (affineChart i).symm q.2) := by
  simp [ambCoordChart]

private noncomputable def coordEqns (b₀ : B) (i : Fin (n + 1))
    (c : B → ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) :
    EB × (Fin n → ℂ) → ι → ℂ :=
  fun q ↦ projectiveIncidenceChartEquations i q.2 (c ((baseChart (IB := IB) b₀).symm q.1))

omit [CompleteSpace EB] in
private theorem contDiffOn_coordEqns
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (b₀ : B) (i : Fin (n + 1)) :
    ContDiffOn 𝕜 r (coordEqns (IB := IB) b₀ i c)
      ((baseChart (IB := IB) b₀).target ×ˢ (univ : Set (Fin n → ℂ))) := by
  have hcoeff : ContMDiff IB 𝓘(𝕜, CoeffSpace n d) r (homogeneousFamilyCoeffEquiv d ∘ c) := by
    simpa only [coe_homogeneousFamilyCoeffDiffeomorph] using
      (homogeneousFamilyCoeffDiffeomorph 𝕜 d r).contMDiff.comp hc
  have hbase : ContMDiffOn 𝓘(𝕜, EB) 𝓘(𝕜, CoeffSpace n d) r
      (fun u ↦ homogeneousFamilyCoeffEquiv d (c ((baseChart (IB := IB) b₀).symm u)))
      (baseChart (IB := IB) b₀).target := by
    rw [baseChart_target]
    exact hcoeff.comp_contMDiffOn (contMDiffOn_extChartAt_symm b₀)
  have hpair : ContDiffOn 𝕜 r
      (fun q : EB × (Fin n → ℂ) ↦
        (q.2, homogeneousFamilyCoeffEquiv d (c ((baseChart (IB := IB) b₀).symm q.1))))
      ((baseChart (IB := IB) b₀).target ×ˢ (univ : Set (Fin n → ℂ))) :=
    contDiff_snd.contDiffOn.prodMk
      ((contMDiffOn_iff_contDiffOn.mp hbase).comp contDiff_fst.contDiffOn fun _ hq ↦ hq.1)
  have heq : coordEqns (IB := IB) b₀ i c =
      fun q ↦ evalChartEqns d i
        (q.2, homogeneousFamilyCoeffEquiv d (c ((baseChart (IB := IB) b₀).symm q.1))) := by
    funext q
    exact (evalChartEqns_apply d i q.2 _).symm
  rw [heq]
  exact (contDiff_evalChartEqns (𝕜 := 𝕜) d i r).comp_contDiffOn hpair

private noncomputable def coordMap
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) {i : Fin (n + 1)} (hi : z.1.2 ∈ affineOpen i) :
    EB × (Fin n → ℂ) → (EB × (Fin (n - Fintype.card ι) → ℂ)) × (ι → ℂ) :=
  let _ := hc
  fun q ↦ ((q.1, (verticalSplit hrank z hi q.2).1), coordEqns (IB := IB) z.1.1 i c q)

private theorem exists_coordChart (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) {i : Fin (n + 1)} (hi : z.1.2 ∈ affineOpen i) :
    let s := (baseChart (IB := IB) z.1.1).target ×ˢ (univ : Set (Fin n → ℂ))
    let q₀ : EB × (Fin n → ℂ) := (baseChart (IB := IB) z.1.1 z.1.1, affineChart i z.1.2)
    ∃ Θ : OpenPartialHomeomorph (EB × (Fin n → ℂ))
        ((EB × (Fin (n - Fintype.card ι) → ℂ)) × (ι → ℂ)),
      (Θ : _ → _) = coordMap hc hrank z hi ∧ q₀ ∈ Θ.source ∧ Θ.source ⊆ s ∧
        ContDiffOn 𝕜 r Θ.symm Θ.target := by
  intro s q₀
  have hs : IsOpen s := (baseChart (IB := IB) z.1.1).open_target.prod isOpen_univ
  have hb₀ : z.1.1 ∈ (baseChart (IB := IB) z.1.1).source := by
    simp [baseChart, mem_chart_source]
  have hq₀ : q₀ ∈ s := ⟨(baseChart (IB := IB) z.1.1).map_source hb₀, trivial⟩
  have hF : ContDiffOn 𝕜 r (coordEqns (IB := IB) z.1.1 i c) s :=
    contDiffOn_coordEqns hc z.1.1 i
  let α := (verticalSplit hrank z hi).restrictScalars' 𝕜
  let L₁ : (EB × (Fin n → ℂ)) →L[𝕜] EB × (Fin (n - Fintype.card ι) → ℂ) :=
    (ContinuousLinearMap.fst 𝕜 EB (Fin n → ℂ)).prod
      ((ContinuousLinearMap.fst 𝕜 (Fin (n - Fintype.card ι) → ℂ) (ι → ℂ)).comp
        (α.toContinuousLinearMap.comp (ContinuousLinearMap.snd 𝕜 EB (Fin n → ℂ))))
  have hcoord : coordMap hc hrank z hi = fun q ↦ (L₁ q, coordEqns (IB := IB) z.1.1 i c q) := by
    funext q
    simp [coordMap, L₁, α]
  have hg : ContDiffOn 𝕜 r (coordMap hc hrank z hi) s := by
    rw [hcoord]
    exact L₁.contDiff.contDiffOn.prodMk hF
  have hr0 : r ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hr
  have hFdiff : DifferentiableAt 𝕜 (coordEqns (IB := IB) z.1.1 i c) q₀ :=
    (hF.differentiableOn hr0).differentiableAt (hs.mem_nhds hq₀)
  let DF := fderiv 𝕜 (coordEqns (IB := IB) z.1.1 i c) q₀
  let B : EB →L[𝕜] ι → ℂ := DF.comp (ContinuousLinearMap.inl 𝕜 EB (Fin n → ℂ))
  have hslice : DF.comp (ContinuousLinearMap.inr 𝕜 EB (Fin n → ℂ)) =
      (fderiv ℂ (fun a ↦ projectiveIncidenceChartEquations i a (c z.1.1))
        (affineChart i z.1.2)).restrictScalars 𝕜 := by
    have hleft : (fun a ↦ coordEqns (IB := IB) z.1.1 i c (q₀.1, a)) =
        fun a ↦ projectiveIncidenceChartEquations i a (c z.1.1) := by
      funext a
      simp only [coordEqns, q₀, (baseChart (IB := IB) z.1.1).left_inv hb₀]
    have h1 : HasFDerivAt (fun a ↦ coordEqns (IB := IB) z.1.1 i c (q₀.1, a))
        (DF.comp (ContinuousLinearMap.inr 𝕜 EB (Fin n → ℂ))) q₀.2 :=
      hFdiff.hasFDerivAt.comp q₀.2 (hasFDerivAt_prodMk_right q₀.1 q₀.2)
    rw [hleft] at h1
    exact h1.unique (hasFDerivAt_projectiveIncidenceChartEquations_left i (c z.1.1) q₀.2)
  have hderiv : (upperTriangularEquiv α B : _ →L[𝕜] _) =
      fderiv 𝕜 (coordMap hc hrank z hi) q₀ := by
    symm
    rw [hcoord]
    refine (L₁.hasFDerivAt.prodMk hFdiff.hasFDerivAt).fderiv.trans (ContinuousLinearMap.ext ?_)
    rintro ⟨δu, δa⟩
    have hsplit : DF (δu, δa) = B δu + (α δa).2 := by
      have hadd : (δu, δa) = (δu, 0) + (0, δa) := by simp
      rw [hadd, map_add]
      have hinr := congrFun (congrArg DFunLike.coe hslice) δa
      simpa [B, α] using congrArg (B δu + ·) hinr
    simp only [ContinuousLinearMap.prod_apply]
    exact Prod.ext (by simp [L₁]) hsplit
  exact TauCeti.ContDiffOn.exists_openPartialHomeomorph hg hs hq₀ hr hderiv

/-- The ambient `C^r` slice chart around a point `z` of a full-rank projective incidence family
`complexProjectiveFamily c`, evaluated in the preferred affine chart `(exists_mem_affineOpen
z.1.2).choose`. Its first coordinate preserves `(extChartAt IB z.1.1) p.1`, and its second
coordinate is `projectiveIncidenceChartEquations`. -/
noncomputable def sliceChartAt (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) :
    OpenPartialHomeomorph (B × ℙ ℂ (Fin (n + 1) → ℂ))
      ((EB × (Fin (n - Fintype.card ι) → ℂ)) × (ι → ℂ)) :=
  (ambCoordChart (IB := IB) z.1.1 (exists_mem_affineOpen z.1.2).choose).trans
    (exists_coordChart hr hc hrank z (exists_mem_affineOpen z.1.2).choose_spec).choose

/-- Every point `z` of `complexProjectiveFamily c` belongs to the source of its slice chart. -/
theorem mem_sliceChartAt_source (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) :
    (z : B × ℙ ℂ (Fin (n + 1) → ℂ)) ∈ (sliceChartAt hr hc hrank z).source := by
  have hspec := (exists_coordChart hr hc hrank z
    (exists_mem_affineOpen z.1.2).choose_spec).choose_spec
  rw [sliceChartAt, OpenPartialHomeomorph.trans_source, ambCoordChart_source]
  refine ⟨⟨by simp [baseChart, mem_chart_source],
    (exists_mem_affineOpen z.1.2).choose_spec⟩, ?_⟩
  rw [mem_preimage, ambCoordChart_apply]
  exact hspec.2.1

private theorem sliceChartAt_source_subset (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) {p : B × ℙ ℂ (Fin (n + 1) → ℂ)}
    (hp : p ∈ (sliceChartAt hr hc hrank z).source) :
    p.1 ∈ (chartAt HB z.1.1).source ∧
      p.2 ∈ affineOpen (exists_mem_affineOpen z.1.2).choose := by
  rw [sliceChartAt, OpenPartialHomeomorph.trans_source] at hp
  simpa [ambCoordChart, baseChart] using hp.1

/-- On its source, the first component of `sliceChartAt` records `extChartAt IB z.1.1 p.1` in its
first factor, and the second component evaluates `projectiveIncidenceChartEquations`. -/
theorem sliceChartAt_apply_of_mem_source (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) {p : B × ℙ ℂ (Fin (n + 1) → ℂ)}
    (hp : p ∈ (sliceChartAt hr hc hrank z).source) :
    (sliceChartAt hr hc hrank z p).1.1 = extChartAt IB z.1.1 p.1 ∧
      (sliceChartAt hr hc hrank z p).2 =
        projectiveIncidenceChartEquations (exists_mem_affineOpen z.1.2).choose
          (affineChart (exists_mem_affineOpen z.1.2).choose p.2) (c p.1) := by
  have hspec := (exists_coordChart hr hc hrank z
    (exists_mem_affineOpen z.1.2).choose_spec).choose_spec
  have hp_src := sliceChartAt_source_subset hr hc hrank z hp
  have hb : p.1 ∈ (baseChart (IB := IB) z.1.1).source := by simpa [baseChart] using hp_src.1
  have happ : sliceChartAt hr hc hrank z p =
      ((baseChart (IB := IB) z.1.1 p.1,
        (verticalSplit hrank z (exists_mem_affineOpen z.1.2).choose_spec
          (affineChart (exists_mem_affineOpen z.1.2).choose p.2)).1),
        projectiveIncidenceChartEquations (exists_mem_affineOpen z.1.2).choose
          (affineChart (exists_mem_affineOpen z.1.2).choose p.2) (c p.1)) := by
    rw [sliceChartAt, OpenPartialHomeomorph.trans_apply, ambCoordChart_apply, hspec.1]
    simp only [coordMap, coordEqns, (baseChart (IB := IB) z.1.1).left_inv hb]
  rw [happ]
  exact ⟨congrFun (congrArg PartialEquiv.toFun (baseChart_toPartialEquiv (IB := IB) z.1.1)) p.1,
    rfl⟩

/-- **The parametric slice chart flattens `complexProjectiveFamily c` onto `univ ×ˢ {0}`.** -/
theorem isSliceChart_sliceChartAt (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) :
    IsSliceChart (sliceChartAt hr hc hrank z)
      ((univ : Set (EB × (Fin (n - Fintype.card ι) → ℂ))) ×ˢ ({0} : Set (ι → ℂ)))
      (complexProjectiveFamily c) := by
  refine isSliceChart_iff.2 fun p hp ↦ ?_
  have hp_src := sliceChartAt_source_subset hr hc hrank z hp
  have hval := (sliceChartAt_apply_of_mem_source hr hc hrank z hp).2
  have hmem : p ∈ complexProjectiveFamily c ↔
      (c p.1, p.2) ∈ complexProjectiveIncidence (n + 1) d := by
    rw [← Prod.eta p, mem_complexProjectiveFamily, mem_complexProjectiveIncidence]
  rw [hmem, mem_complexProjectiveIncidence_iff_projectiveIncidenceChartEquations_eq_zero
    (c p.1) hp_src.2]
  simp [hval]

private theorem contMDiffOn_sliceChartAt (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) :
    letI : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
      (Projectivization.instIsManifold r).restrictScalars 𝕜
    ContMDiffOn (IB.prod 𝓘(𝕜, Fin n → ℂ))
      𝓘(𝕜, (EB × (Fin (n - Fintype.card ι) → ℂ)) × (ι → ℂ)) r
      (sliceChartAt hr hc hrank z) (sliceChartAt hr hc hrank z).source := by
  have : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
    (Projectivization.instIsManifold r).restrictScalars 𝕜
  set i := (exists_mem_affineOpen z.1.2).choose
  have hi : z.1.2 ∈ affineOpen i := (exists_mem_affineOpen z.1.2).choose_spec
  have hspec := (exists_coordChart hr hc hrank z hi).choose_spec
  have heB : ContMDiffOn IB 𝓘(𝕜, EB) r (baseChart (IB := IB) z.1.1)
      (baseChart (IB := IB) z.1.1).source := by
    have hfun : ⇑(baseChart (IB := IB) z.1.1) = ⇑(extChartAt IB z.1.1) :=
      congrArg PartialEquiv.toFun (baseChart_toPartialEquiv (IB := IB) z.1.1)
    have hsrc : (baseChart (IB := IB) z.1.1).source = (chartAt HB z.1.1).source := by
      simp [baseChart]
    rw [hfun, hsrc]
    exact contMDiffOn_extChartAt
  have haff : ContMDiffOn 𝓘(𝕜, Fin n → ℂ) 𝓘(𝕜, Fin n → ℂ) r (affineChart (K := ℂ) i)
      (affineOpen (K := ℂ) i) := by
    simpa using contMDiffOn_of_mem_maximalAtlas
      (affineOpenPartialHomeomorph_mem_maximalAtlas (𝕜 := ℂ) (I := 𝓘(𝕜, Fin n → ℂ)) (r := r) i)
  have hamb : ContMDiffOn (IB.prod 𝓘(𝕜, Fin n → ℂ)) 𝓘(𝕜, EB × (Fin n → ℂ)) r
      (ambCoordChart (IB := IB) z.1.1 i) (ambCoordChart (IB := IB) z.1.1 i).source := by
    rw [ambCoordChart_source]
    have h1 : ContMDiffOn (IB.prod 𝓘(𝕜, Fin n → ℂ)) 𝓘(𝕜, EB) r
        (fun p : B × ℙ ℂ (Fin (n + 1) → ℂ) ↦ baseChart (IB := IB) z.1.1 p.1)
        ((baseChart (IB := IB) z.1.1).source ×ˢ affineOpen i) :=
      heB.comp contMDiff_fst.contMDiffOn fun _ hp ↦ hp.1
    have h2 : ContMDiffOn (IB.prod 𝓘(𝕜, Fin n → ℂ)) 𝓘(𝕜, Fin n → ℂ) r
        (fun p : B × ℙ ℂ (Fin (n + 1) → ℂ) ↦ affineChart i p.2)
        ((baseChart (IB := IB) z.1.1).source ×ˢ affineOpen i) :=
      haff.comp contMDiff_snd.contMDiffOn fun _ hp ↦ hp.2
    exact (h1.prodMk_space h2).congr fun p _ ↦ ambCoordChart_apply z.1.1 i p
  let α := (verticalSplit hrank z hi).restrictScalars' 𝕜
  let L₁ : (EB × (Fin n → ℂ)) →L[𝕜] EB × (Fin (n - Fintype.card ι) → ℂ) :=
    (ContinuousLinearMap.fst 𝕜 EB (Fin n → ℂ)).prod
      ((ContinuousLinearMap.fst 𝕜 (Fin (n - Fintype.card ι) → ℂ) (ι → ℂ)).comp
        (α.toContinuousLinearMap.comp (ContinuousLinearMap.snd 𝕜 EB (Fin n → ℂ))))
  have hg : ContMDiffOn 𝓘(𝕜, EB × (Fin n → ℂ))
      𝓘(𝕜, (EB × (Fin (n - Fintype.card ι) → ℂ)) × (ι → ℂ)) r
      (exists_coordChart hr hc hrank z hi).choose
      ((baseChart (IB := IB) z.1.1).target ×ˢ (univ : Set (Fin n → ℂ))) := by
    rw [hspec.1, contMDiffOn_iff_contDiffOn]
    have hcoord : coordMap hc hrank z hi = fun q ↦ (L₁ q, coordEqns (IB := IB) z.1.1 i c q) := by
      funext q
      simp [coordMap, L₁, α]
    rw [hcoord]
    exact L₁.contDiff.contDiffOn.prodMk (contDiffOn_coordEqns hc z.1.1 i)
  rw [sliceChartAt, OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source]
  exact hg.comp (hamb.mono inter_subset_left) fun _ hp ↦ hspec.2.2.1 hp.2

private theorem contMDiffOn_sliceChartAt_symm (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) :
    letI : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
      (Projectivization.instIsManifold r).restrictScalars 𝕜
    ContMDiffOn 𝓘(𝕜, (EB × (Fin (n - Fintype.card ι) → ℂ)) × (ι → ℂ))
      (IB.prod 𝓘(𝕜, Fin n → ℂ)) r
      (sliceChartAt hr hc hrank z).symm (sliceChartAt hr hc hrank z).target := by
  have : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
    (Projectivization.instIsManifold r).restrictScalars 𝕜
  set i := (exists_mem_affineOpen z.1.2).choose
  have hi : z.1.2 ∈ affineOpen i := (exists_mem_affineOpen z.1.2).choose_spec
  have hspec := (exists_coordChart hr hc hrank z hi).choose_spec
  have heB_symm : ContMDiffOn 𝓘(𝕜, EB) IB r (baseChart (IB := IB) z.1.1).symm
      (baseChart (IB := IB) z.1.1).target := by
    have hinv : ⇑(baseChart (IB := IB) z.1.1).symm = ⇑(extChartAt IB z.1.1).symm :=
      congrArg PartialEquiv.invFun (baseChart_toPartialEquiv (IB := IB) z.1.1)
    rw [hinv, baseChart_target]
    exact contMDiffOn_extChartAt_symm z.1.1
  have haff_symm : ContMDiff 𝓘(𝕜, Fin n → ℂ) 𝓘(𝕜, Fin n → ℂ) r (affineChart (K := ℂ) i).symm := by
    rw [← contMDiffOn_univ]
    simpa using contMDiffOn_symm_of_mem_maximalAtlas
      (affineOpenPartialHomeomorph_mem_maximalAtlas (𝕜 := ℂ) (I := 𝓘(𝕜, Fin n → ℂ)) (r := r) i)
  have hamb_symm : ContMDiffOn 𝓘(𝕜, EB × (Fin n → ℂ)) (IB.prod 𝓘(𝕜, Fin n → ℂ)) r
      (ambCoordChart (IB := IB) z.1.1 i).symm (ambCoordChart (IB := IB) z.1.1 i).target := by
    rw [ambCoordChart_target]
    have h1 : ContMDiffOn 𝓘(𝕜, EB × (Fin n → ℂ)) IB r
        (fun q : EB × (Fin n → ℂ) ↦ (baseChart (IB := IB) z.1.1).symm q.1)
        ((baseChart (IB := IB) z.1.1).target ×ˢ univ) :=
      heB_symm.comp contDiff_fst.contMDiff.contMDiffOn fun _ hq ↦ hq.1
    exact (h1.prodMk (haff_symm.comp contDiff_snd.contMDiff).contMDiffOn).congr fun q _ ↦
      ambCoordChart_symm_apply z.1.1 i q
  have hΘ_symm : ContMDiffOn 𝓘(𝕜, (EB × (Fin (n - Fintype.card ι) → ℂ)) × (ι → ℂ))
      𝓘(𝕜, EB × (Fin n → ℂ)) r
      (exists_coordChart hr hc hrank z hi).choose.symm
      (exists_coordChart hr hc hrank z hi).choose.target :=
    contMDiffOn_iff_contDiffOn.mpr hspec.2.2.2
  rw [sliceChartAt, OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.trans_target]
  exact hamb_symm.comp (hΘ_symm.mono inter_subset_left) fun _ hv ↦ hv.2

/-- **The `C^r` manifold atlas of a full-rank projective incidence family.** Let `c` be a `C^r`
(`1 ≤ r`) full-rank family of homogeneous polynomial tuples over a boundaryless manifold `B` with
complete model space `EB`. The slice charts `TauCeti.ComplexProjectiveFamily.sliceChartAt` induce a
chart atlas on `complexProjectiveFamily c` modelled on `EB × (Fin (n - |ι|) → ℂ)`. -/
@[instance_reducible]
noncomputable def chartedSpace (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) :
    ChartedSpace (EB × (Fin (n - Fintype.card ι) → ℂ)) (complexProjectiveFamily c) :=
  linearSliceChartedSpace (sliceChartAt hr hc hrank) (isSliceChart_sliceChartAt hr hc hrank)
    (mem_sliceChartAt_source hr hc hrank)

/-- **A full-rank `C^r` projective incidence family is a boundaryless `C^r` manifold.** -/
theorem isManifold (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) :
    letI := chartedSpace hr hc hrank
    IsManifold 𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) r (complexProjectiveFamily c) := by
  have : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
    (Projectivization.instIsManifold r).restrictScalars 𝕜
  exact isManifold_linearSliceChartedSpace (sliceChartAt hr hc hrank)
    (isSliceChart_sliceChartAt hr hc hrank)
    (fun z _ hp ↦ (contMDiffOn_sliceChartAt hr hc hrank z).contMDiffAt
      ((OpenPartialHomeomorph.open_source _).mem_nhds hp))
    (fun z _ hv ↦ (contMDiffOn_sliceChartAt_symm hr hc hrank z).contMDiffAt
      ((OpenPartialHomeomorph.open_target _).mem_nhds hv))
    (mem_sliceChartAt_source hr hc hrank)

private noncomputable def ambientModelEquiv
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (z : complexProjectiveFamily c) :
    ((EB × (Fin (n - Fintype.card ι) → ℂ)) × (ι → ℂ)) ≃L[𝕜] EB × (Fin n → ℂ) :=
  (ContinuousLinearEquiv.prodAssoc 𝕜 EB (Fin (n - Fintype.card ι) → ℂ) (ι → ℂ)).trans
    ((ContinuousLinearEquiv.refl 𝕜 EB).prodCongr
      ((verticalSplit hrank z (exists_mem_affineOpen z.1.2).choose_spec).symm.restrictScalars' 𝕜))

/-- **The ambient inclusion of a full-rank projective incidence family is a `C^r` immersion with
normal model `ι → ℂ`.** -/
theorem isImmersionOfComplement_subtypeVal (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) :
    letI := chartedSpace hr hc hrank
    letI : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
      (Projectivization.instIsManifold r).restrictScalars 𝕜
    Manifold.IsImmersionOfComplement (ι → ℂ)
      𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) (IB.prod 𝓘(𝕜, Fin n → ℂ)) r
      (Subtype.val : complexProjectiveFamily c → B × ℙ ℂ (Fin (n + 1) → ℂ)) := by
  have : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
    (Projectivization.instIsManifold r).restrictScalars 𝕜
  exact isImmersionOfComplement_subtypeVal_linearSliceChartedSpace_of_boundaryless
    (sliceChartAt hr hc hrank) (isSliceChart_sliceChartAt hr hc hrank)
    (ambientModelEquiv hrank)
    (contMDiffOn_sliceChartAt hr hc hrank)
    (contMDiffOn_sliceChartAt_symm hr hc hrank)
    (mem_sliceChartAt_source hr hc hrank)

/-- **A full-rank projective incidence family is a `C^r` embedded submanifold of
`B × ℙ ℂ (Fin (n + 1) → ℂ)`.** -/
theorem isSmoothEmbedding_subtypeVal (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) :
    letI := chartedSpace hr hc hrank
    letI : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
      (Projectivization.instIsManifold r).restrictScalars 𝕜
    Manifold.IsSmoothEmbedding
      𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) (IB.prod 𝓘(𝕜, Fin n → ℂ)) r
      (Subtype.val : complexProjectiveFamily c → B × ℙ ℂ (Fin (n + 1) → ℂ)) := by
  let := chartedSpace hr hc hrank
  have : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
    (Projectivization.instIsManifold r).restrictScalars 𝕜
  exact ⟨(isImmersionOfComplement_subtypeVal hr hc hrank).isImmersion,
    Topology.IsEmbedding.subtypeVal⟩

/-- **The projection of a full-rank `C^r` projective incidence family to its base is a `C^r`
submersion with fiber model `Fin (n - |ι|) → ℂ`.** For `𝕜 = ℂ` and `r = ω`, this is a proper
holomorphic submersion; for `𝕜 = ℝ`, a proper real `C^r` submersion. -/
theorem isSubmersionOfComplement_fst (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) :
    letI := chartedSpace hr hc hrank
    Manifold.IsSubmersionOfComplement (Fin (n - Fintype.card ι) → ℂ)
      𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) IB r
      (fun x : complexProjectiveFamily c ↦ x.1.1) := by
  let := chartedSpace hr hc hrank
  have := isManifold hr hc hrank
  refine Manifold.isSubmersionOfComplement_iff.mpr fun z ↦ ?_
  let dom := @chartAt _ _ _ _ (chartedSpace hr hc hrank) z
  refine Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt
    (continuous_fst.comp continuous_subtype_val).continuousAt
    (ContinuousLinearEquiv.refl 𝕜 (EB × (Fin (n - Fintype.card ι) → ℂ)))
    dom (chartAt HB z.1.1) (mem_chart_source _ z) (mem_chart_source _ z.1.1)
    (IsManifold.chart_mem_maximalAtlas z) (IsManifold.chart_mem_maximalAtlas z.1.1) ?_
  intro v hv
  have hv' : v ∈ dom.target := by simpa using hv
  have hy_dom : dom.symm v ∈ dom.source := dom.map_target hv'
  have hdom_eq : dom = linearSliceChart (sliceChartAt hr hc hrank)
      (isSliceChart_sliceChartAt hr hc hrank) z :=
    linearSliceChartedSpace_chartAt _ _ _ z
  have hdom_src : dom.source = Subtype.val ⁻¹' (sliceChartAt hr hc hrank z).source := by
    rw [hdom_eq, linearSliceChart_source]
  have hy_slice : (dom.symm v : B × ℙ ℂ (Fin (n + 1) → ℂ)) ∈
      (sliceChartAt hr hc hrank z).source := by
    rwa [hdom_src] at hy_dom
  have hfst := (sliceChartAt_apply_of_mem_source hr hc hrank z hy_slice).1
  have hdom_apply : dom (dom.symm v) = (sliceChartAt hr hc hrank z (dom.symm v).1).1 := by
    rw [hdom_eq, linearSliceChart_apply]
  have hv1 : v.1 = extChartAt IB z.1.1 (dom.symm v).1.1 :=
    (congrArg Prod.fst (dom.right_inv hv')).symm.trans ((congrArg Prod.fst hdom_apply).trans hfst)
  simpa [extChartAt] using hv1.symm

/-- **The projection of a full-rank `C^r` projective incidence family to its base is a `C^r`
submersion.** -/
theorem isSubmersion_fst (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) :
    letI := chartedSpace hr hc hrank
    Manifold.IsSubmersion 𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) IB r
      (fun x : complexProjectiveFamily c ↦ x.1.1) := by
  let := chartedSpace hr hc hrank
  exact (isSubmersionOfComplement_fst hr hc hrank).isSubmersion

/-! ### Smoothness of classifying, base-change, and fiber maps -/

/-- The classifying map of a full-rank `C^r` projective incidence family into the universal
incidence variety is `C^r`. -/
theorem contMDiff_classifyingMap (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) :
    letI := chartedSpace hr hc hrank
    letI : IsManifold
        𝓘(𝕜, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
          Fintype.card ι) → ℂ) r
        (complexProjectiveIncidence (n + 1) d) :=
      (instIsManifoldComplexProjectiveIncidence d r).restrictScalars 𝕜
    ContMDiff 𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ))
      𝓘(𝕜, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ) r
      (classifyingMap c) := by
  let := chartedSpace hr hc hrank
  have := isManifold hr hc hrank
  have : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
    (Projectivization.instIsManifold r).restrictScalars 𝕜
  have : ∀ k, IsManifold 𝓘(𝕜, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) r
      (homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) := fun k ↦
    (instIsManifoldHomogeneousSubmodule (d k) r).restrictScalars 𝕜
  have : IsManifold
      𝓘(𝕜, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ) r
      (complexProjectiveIncidence (n + 1) d) :=
    (instIsManifoldComplexProjectiveIncidence d r).restrictScalars 𝕜
  have hemb := isSmoothEmbedding_subtypeVal hr hc hrank
  refine (isSmoothEmbedding_subtypeVal_complexProjectiveIncidence 𝕜 d r).contMDiff_iff_comp.mpr ?_
  have hcomp : Subtype.val ∘ classifyingMap c =
      fun x : complexProjectiveFamily c ↦ (c x.1.1, x.1.2) := by
    funext x
    simp
  rw [hcomp]
  exact (hc.comp (contMDiff_fst.comp hemb.contMDiff)).prodMk (contMDiff_snd.comp hemb.contMDiff)

/-- A `C^r` base change `f : A → B` induces a `C^r` map of full-rank projective incidence
families. -/
theorem contMDiff_baseChange {EA HA A : Type*}
    [NormedAddCommGroup EA] [NormedSpace 𝕜 EA] [CompleteSpace EA]
    [TopologicalSpace HA] {IA : ModelWithCorners 𝕜 EA HA} [IA.Boundaryless]
    [TopologicalSpace A] [ChartedSpace HA A] [IsManifold IA r A]
    (hr : 1 ≤ r) (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    {f : A → B} (hf : ContMDiff IA IB r f) :
    letI := chartedSpace hr hc hrank
    letI := chartedSpace hr (hc.comp hf) (fun a ↦ hrank (f a))
    ContMDiff 𝓘(𝕜, EA × (Fin (n - Fintype.card ι) → ℂ))
      𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) r (baseChange c f) := by
  let := chartedSpace hr hc hrank
  let := chartedSpace hr (hc.comp hf) (fun a ↦ hrank (f a))
  have := isManifold hr hc hrank
  have := isManifold hr (hc.comp hf) (fun a ↦ hrank (f a))
  have : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
    (Projectivization.instIsManifold r).restrictScalars 𝕜
  have hembA := isSmoothEmbedding_subtypeVal hr (hc.comp hf) (fun a ↦ hrank (f a))
  have hembB := isSmoothEmbedding_subtypeVal hr hc hrank
  refine hembB.contMDiff_iff_comp.mpr ?_
  have hcomp : Subtype.val ∘ baseChange c f =
      fun x : complexProjectiveFamily (c ∘ f) ↦ (f x.1.1, x.1.2) := by
    funext x
    simp
  rw [hcomp]
  exact (hf.comp (contMDiff_fst.comp hembA.contMDiff)).prodMk (contMDiff_snd.comp hembA.contMDiff)

/-- The inclusion of the projective zero locus at `b` into a full-rank `C^r` projective incidence
family is `C^r` (holomorphic when `𝕜 = ℂ` and `r = ω`). -/
theorem contMDiff_fiberInclusion (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) (b : B) :
    let hp : ∀ k, ((c b k : MvPolynomial (Fin (n + 1)) ℂ)).IsHomogeneous (d k) :=
      fun k ↦ (mem_homogeneousSubmodule _ _).mp (c b k).2
    let hzb : ∀ L ∈ complexProjectiveZeroLocus (fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)),
        Surjective (jacobiMatrixAt (fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)) L.rep).mulVec :=
      mem_complexProjectiveFullRankParams_iff_forall_zeroLocus.mp (hrank b)
    letI := complexProjectiveZeroLocusChartedSpace hp isOpen_univ (inter_univ _).symm hzb
    letI := chartedSpace hr hc hrank
    letI : IsManifold 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ) r
        (complexProjectiveZeroLocus fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)) :=
      (isManifold_complexProjectiveZeroLocus hp isOpen_univ (inter_univ _).symm hzb r
        ).restrictScalars 𝕜
    ContMDiff 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ)
      𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) r (fiberInclusion c b) := by
  intro hp hzb
  let := complexProjectiveZeroLocusChartedSpace hp isOpen_univ (inter_univ _).symm hzb
  let := chartedSpace hr hc hrank
  have := isManifold hr hc hrank
  have : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
    (Projectivization.instIsManifold r).restrictScalars 𝕜
  have : IsManifold 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ) r
      (complexProjectiveZeroLocus fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)) :=
    (isManifold_complexProjectiveZeroLocus hp isOpen_univ (inter_univ _).symm hzb r
      ).restrictScalars 𝕜
  have hZ := isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus_of_normedAlgebra 𝕜 hp
    isOpen_univ (inter_univ _).symm hzb r
  refine (isSmoothEmbedding_subtypeVal hr hc hrank).contMDiff_iff_comp.mpr ?_
  have hcomp : Subtype.val ∘ fiberInclusion c b = fun L ↦ (b, L.1) := by
    funext L
    simp
  rw [hcomp]
  exact contMDiff_const.prodMk hZ.contMDiff

/-- Over a finite-dimensional base `B`, the inclusion of the projective zero locus at `b` into
`complexProjectiveFamily c` is a `C^r` smooth embedding (holomorphic embedding when
`𝕜 = ℂ, r = ω`). -/
theorem isSmoothEmbedding_fiberInclusion [FiniteDimensional 𝕜 ℂ] [FiniteDimensional 𝕜 EB]
    (hr : 1 ≤ r) (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) (b : B) :
    let hp : ∀ k, ((c b k : MvPolynomial (Fin (n + 1)) ℂ)).IsHomogeneous (d k) :=
      fun k ↦ (mem_homogeneousSubmodule _ _).mp (c b k).2
    let hzb : ∀ L ∈ complexProjectiveZeroLocus (fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)),
        Surjective (jacobiMatrixAt (fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)) L.rep).mulVec :=
      mem_complexProjectiveFullRankParams_iff_forall_zeroLocus.mp (hrank b)
    letI := complexProjectiveZeroLocusChartedSpace hp isOpen_univ (inter_univ _).symm hzb
    letI := chartedSpace hr hc hrank
    letI : IsManifold 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ) r
        (complexProjectiveZeroLocus fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)) :=
      (isManifold_complexProjectiveZeroLocus hp isOpen_univ (inter_univ _).symm hzb r
        ).restrictScalars 𝕜
    Manifold.IsSmoothEmbedding 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ)
      𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) r (fiberInclusion c b) := by
  intro hp hzb
  let := complexProjectiveZeroLocusChartedSpace hp isOpen_univ (inter_univ _).symm hzb
  let := chartedSpace hr hc hrank
  have := isManifold hr hc hrank
  have : IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ)) :=
    (Projectivization.instIsManifold r).restrictScalars 𝕜
  have : IsManifold 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ) r
      (complexProjectiveZeroLocus fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)) :=
    (isManifold_complexProjectiveZeroLocus hp isOpen_univ (inter_univ _).symm hzb r
      ).restrictScalars 𝕜
  have : FiniteDimensional 𝕜 (Fin (n - Fintype.card ι) → ℂ) :=
    Module.Finite.trans ℂ (Fin (n - Fintype.card ι) → ℂ)
  have hZ := isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus_of_normedAlgebra 𝕜 hp
    isOpen_univ (inter_univ _).symm hzb r
  have hemb := isSmoothEmbedding_subtypeVal hr hc hrank
  have hr0 : r ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hr
  have hsnd : ContMDiff 𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) 𝓘(𝕜, Fin n → ℂ) r
      (fun x : complexProjectiveFamily c ↦ x.1.2) :=
    contMDiff_snd.comp hemb.contMDiff
  have hcomp_imm : Manifold.IsImmersion 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ) 𝓘(𝕜, Fin n → ℂ) r
      ((fun x : complexProjectiveFamily c ↦ x.1.2) ∘ fiberInclusion c b) := by
    have heq : ((fun x : complexProjectiveFamily c ↦ x.1.2) ∘ fiberInclusion c b) =
        Subtype.val := by
      funext L
      exact congrArg Prod.snd (coe_fiberInclusion c b L)
    rw [heq]
    exact hZ.isImmersion
  have himm : Manifold.IsImmersion 𝓘(𝕜, Fin (n - Fintype.card ι) → ℂ)
      𝓘(𝕜, EB × (Fin (n - Fintype.card ι) → ℂ)) r (fiberInclusion c b) :=
    (contMDiff_fiberInclusion hr hc hrank b).isImmersion_of_isImmersion_comp hr
      (fun x ↦ (hsnd (fiberInclusion c b x)).mdifferentiableAt hr0) hcomp_imm
  exact ⟨himm, Topology.IsEmbedding.subtypeVal.comp (fiberHomeomorph c b).isEmbedding⟩

end ParametricSlice

/-! ### Regular-fiber and transverse-pullback diffeomorphisms over real bases -/

section RealComparisons

variable {ι : Type*} [Fintype ι] {n : ℕ} {d : ι → ℕ}
  {EA HA A EB HB B : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA]
  [TopologicalSpace HA] {IA : ModelWithCorners ℝ EA HA} [IA.Boundaryless]
  [TopologicalSpace A] [ChartedSpace HA A]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  [TopologicalSpace B] [ChartedSpace HB B]
  {r : ℕ∞ω} [IsManifold IA r A] [IsManifold IB r B]
  {c : B → ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)}

/-- Every base point `b : B` is a regular value of the projection of a full-rank `C^r` projective
incidence family (`1 ≤ r`). -/
theorem isRegularValue_fst (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) ℝ ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) (b : B) :
    letI := chartedSpace hr hc hrank
    IsRegularValue 𝓘(ℝ, EB × (Fin (n - Fintype.card ι) → ℂ)) IB
      (fun x : complexProjectiveFamily c ↦ x.1.1) b := by
  let := chartedSpace hr hc hrank
  have := isManifold hr hc hrank
  have hr0 : r ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hr
  exact isRegularValue_iff.mpr fun x _ ↦
    isRegularPoint_iff.mpr ((isSubmersion_fst hr hc hrank).surjective_mfderiv hr0 x)

/-- **Regular-fiber comparison.** Over a finite-dimensional boundaryless `C^r` real base `B`
(`1 ≤ r`), `TauCeti.ComplexProjectiveFamily.fiberHomeomorph c b` upgrades to a `C^r`
diffeomorphism between the projective zero locus at `b` (equipped with its complex slice atlas
viewed over `ℝ`) and the actual fiber `{x : complexProjectiveFamily c // x.1.1 = b}` (equipped
with `TauCeti.regularFiberChartedSpace`). -/
noncomputable def fiberDiffeomorph (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) ℝ ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) (b : B) :
    let hp : ∀ k, ((c b k : MvPolynomial (Fin (n + 1)) ℂ)).IsHomogeneous (d k) :=
      fun k ↦ (mem_homogeneousSubmodule _ _).mp (c b k).2
    let hzb : ∀ L ∈ complexProjectiveZeroLocus (fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)),
        Surjective (jacobiMatrixAt (fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)) L.rep).mulVec :=
      mem_complexProjectiveFullRankParams_iff_forall_zeroLocus.mp (hrank b)
    letI := complexProjectiveZeroLocusChartedSpace hp isOpen_univ (inter_univ _).symm hzb
    letI := chartedSpace hr hc hrank
    letI := isManifold hr hc hrank
    letI := regularFiberChartedSpace hr (isSubmersion_fst hr hc hrank).contMDiff
      BoundarylessManifold.isInteriorPoint (isRegularValue_fst hr hc hrank b)
    Diffeomorph 𝓘(ℝ, Fin (n - Fintype.card ι) → ℂ)
      𝓘(ℝ, Fin (finrank ℝ (EB × (Fin (n - Fintype.card ι) → ℂ)) - finrank ℝ EB) → ℝ)
      (complexProjectiveZeroLocus fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ))
      {x : complexProjectiveFamily c // x.1.1 = b} r := by
  intro hp hzb
  letI := complexProjectiveZeroLocusChartedSpace hp isOpen_univ (inter_univ _).symm hzb
  letI := chartedSpace hr hc hrank
  have := isManifold hr hc hrank
  have : IsManifold 𝓘(ℝ, Fin (n - Fintype.card ι) → ℂ) r
      (complexProjectiveZeroLocus fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)) :=
    (isManifold_complexProjectiveZeroLocus hp isOpen_univ (inter_univ _).symm hzb r
      ).restrictScalars ℝ
  have : FiniteDimensional ℝ (EB × (Fin (n - Fintype.card ι) → ℂ)) := inferInstance
  have hfst := (isSubmersion_fst hr hc hrank).contMDiff
  have hreg := isRegularValue_fst hr hc hrank b
  letI := regularFiberChartedSpace hr hfst BoundarylessManifold.isInteriorPoint hreg
  have := isManifold_regularFiber hr hfst BoundarylessManifold.isInteriorPoint hreg
  have hRF := isSmoothEmbedding_coe_regularFiber hr hfst BoundarylessManifold.isInteriorPoint hreg
  have hZ := isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus_of_normedAlgebra ℝ hp
    isOpen_univ (inter_univ _).symm hzb r
  have hemb := isSmoothEmbedding_subtypeVal hr hc hrank
  refine { (fiberHomeomorph c b).toEquiv with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · refine hRF.contMDiff_iff_comp.mpr ?_
    exact (contMDiff_fiberInclusion hr hc hrank b).congr fun L ↦ by simp [fiberInclusion]
  · refine hZ.contMDiff_iff_comp.mpr ?_
    exact (contMDiff_snd.comp (hemb.contMDiff.comp hRF.contMDiff)).congr fun x ↦ by simp

@[simp]
theorem fiberDiffeomorph_toHomeomorph (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) ℝ ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d) (b : B) :
    let hp : ∀ k, ((c b k : MvPolynomial (Fin (n + 1)) ℂ)).IsHomogeneous (d k) :=
      fun k ↦ (mem_homogeneousSubmodule _ _).mp (c b k).2
    let hzb : ∀ L ∈ complexProjectiveZeroLocus (fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)),
        Surjective (jacobiMatrixAt (fun k ↦ (c b k : MvPolynomial (Fin (n + 1)) ℂ)) L.rep).mulVec :=
      mem_complexProjectiveFullRankParams_iff_forall_zeroLocus.mp (hrank b)
    letI := complexProjectiveZeroLocusChartedSpace hp isOpen_univ (inter_univ _).symm hzb
    letI := chartedSpace hr hc hrank
    letI := isManifold hr hc hrank
    letI := regularFiberChartedSpace hr (isSubmersion_fst hr hc hrank).contMDiff
      BoundarylessManifold.isInteriorPoint (isRegularValue_fst hr hc hrank b)
    (fiberDiffeomorph hr hc hrank b).toHomeomorph = fiberHomeomorph c b := by
  intro hp hzb
  let := complexProjectiveZeroLocusChartedSpace hp isOpen_univ (inter_univ _).symm hzb
  let := chartedSpace hr hc hrank
  have := isManifold hr hc hrank
  let := regularFiberChartedSpace hr (isSubmersion_fst hr hc hrank).contMDiff
    BoundarylessManifold.isInteriorPoint (isRegularValue_fst hr hc hrank b)
  ext1 L
  rfl

omit [FiniteDimensional ℝ EA] [IA.Boundaryless] [IsManifold IA r A] in
/-- Any map `f : A → B` is transverse to the submersion `fst : complexProjectiveFamily c → B` of a
full-rank `C^r` projective incidence family (`1 ≤ r`). -/
theorem transverse_fst (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) ℝ ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    (f : A → B) :
    letI := chartedSpace hr hc hrank
    ∀ p : A × complexProjectiveFamily c, f p.1 = p.2.1.1 →
      (mfderiv IA IB f p.1).range ⊔
        (((tangentSpaceCast IB p.2.1.1 (f p.1)).toContinuousLinearMap).comp
          (mfderiv 𝓘(ℝ, EB × (Fin (n - Fintype.card ι) → ℂ)) IB
            (fun x : complexProjectiveFamily c ↦ x.1.1) p.2)).range = ⊤ := by
  let := chartedSpace hr hc hrank
  have := isManifold hr hc hrank
  have hr0 : r ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hr
  intro p _
  have hsurj : Surjective
      (((tangentSpaceCast IB p.2.1.1 (f p.1)).toContinuousLinearMap).comp
        (mfderiv 𝓘(ℝ, EB × (Fin (n - Fintype.card ι) → ℂ)) IB
          (fun x : complexProjectiveFamily c ↦ x.1.1) p.2)) := by
    rw [ContinuousLinearMap.coe_comp]
    exact (tangentSpaceCast IB p.2.1.1 (f p.1)).surjective.comp
      ((isSubmersion_fst hr hc hrank).surjective_mfderiv hr0 p.2)
  rw [LinearMap.range_eq_top.mpr hsurj, sup_top_eq]

/-- **Transverse pullback comparison.** Over finite-dimensional boundaryless `C^r` real bases `A`
and `B` (`1 ≤ r`), any `C^r` map `f : A → B` is transverse to the submersion
`complexProjectiveFamily c → B`, and `TauCeti.ComplexProjectiveFamily.pullbackHomeomorph` upgrades
to a `C^r` diffeomorphism between `complexProjectiveFamily (c ∘ f)` and the transverse fiber
product `{z : A × complexProjectiveFamily c // f z.1 = z.2.1.1}`. -/
noncomputable def pullbackDiffeomorph (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) ℝ ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    {f : A → B} (hf : ContMDiff IA IB r f) :
    letI := chartedSpace hr hc hrank
    letI := chartedSpace hr (hc.comp hf) (fun a ↦ hrank (f a))
    letI := isManifold hr hc hrank
    letI := transverseFiberProductChartedSpace hr hf (isSubmersion_fst hr hc hrank).contMDiff
      (transverse_fst hr hc hrank f)
    Diffeomorph 𝓘(ℝ, EA × (Fin (n - Fintype.card ι) → ℂ))
      𝓘(ℝ, Fin (finrank ℝ EA + finrank ℝ (EB × (Fin (n - Fintype.card ι) → ℂ)) -
        finrank ℝ EB) → ℝ)
      (complexProjectiveFamily (c ∘ f))
      {z : A × complexProjectiveFamily c // f z.1 = z.2.1.1} r := by
  letI := chartedSpace hr hc hrank
  letI := chartedSpace hr (hc.comp hf) (fun a ↦ hrank (f a))
  have := isManifold hr hc hrank
  have := isManifold hr (hc.comp hf) (fun a ↦ hrank (f a))
  have hfst := (isSubmersion_fst hr hc hrank).contMDiff
  have htrans := transverse_fst (IA := IA) hr hc hrank f
  letI := transverseFiberProductChartedSpace hr hf hfst htrans
  have := isManifold_transverseFiberProduct hr hf hfst htrans
  have hFP := isSmoothEmbedding_coe_transverseFiberProduct hr hf hfst htrans
  have hembA := isSmoothEmbedding_subtypeVal hr (hc.comp hf) (fun a ↦ hrank (f a))
  have hembB := isSmoothEmbedding_subtypeVal hr hc hrank
  refine { (pullbackHomeomorph c f hf.continuous).toEquiv with
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · refine hFP.contMDiff_iff_comp.mpr ?_
    exact ((contMDiff_fst.comp hembA.contMDiff).prodMk
      (contMDiff_baseChange hr hc hrank hf)).congr fun x ↦ by
        simp only [Function.comp_apply, Homeomorph.coe_toEquiv]
        exact Prod.ext (pullbackHomeomorph_apply_fst c f hf.continuous x)
          (pullbackHomeomorph_apply_snd c f hf.continuous x)
  · refine hembA.contMDiff_iff_comp.mpr ?_
    exact ((contMDiff_fst.comp hFP.contMDiff).prodMk
      (contMDiff_snd.comp (hembB.contMDiff.comp (contMDiff_snd.comp hFP.contMDiff)))).congr
        fun z ↦ by simp

@[simp]
theorem pullbackDiffeomorph_toHomeomorph (hr : 1 ≤ r)
    (hc : ContMDiff IB (homogeneousFamilyModel (Fin (n + 1)) ℝ ℂ d) r c)
    (hrank : ∀ b, c b ∈ complexProjectiveFullRankParams (n + 1) d)
    {f : A → B} (hf : ContMDiff IA IB r f) :
    letI := chartedSpace hr hc hrank
    letI := chartedSpace hr (hc.comp hf) (fun a ↦ hrank (f a))
    letI := isManifold hr hc hrank
    letI := transverseFiberProductChartedSpace hr hf (isSubmersion_fst hr hc hrank).contMDiff
      (transverse_fst hr hc hrank f)
    (pullbackDiffeomorph hr hc hrank hf).toHomeomorph = pullbackHomeomorph c f hf.continuous := by
  let := chartedSpace hr hc hrank
  let := chartedSpace hr (hc.comp hf) (fun a ↦ hrank (f a))
  have := isManifold hr hc hrank
  let := transverseFiberProductChartedSpace hr hf (isSubmersion_fst hr hc hrank).contMDiff
    (transverse_fst hr hc hrank f)
  ext1 x
  rfl

end RealComparisons

end ComplexProjectiveFamily

/-! ### The universal full-rank projective incidence family -/

section UniversalFullRank

/-- **The universal full-rank projective incidence family.** Over the open locus
`TauCeti.complexProjectiveFullRankParamsOpens N d` of coefficient families whose projective zero
locus has surjective cone Jacobian at every point, this is the incidence family cut out by the
open inclusion of parameters. -/
abbrev complexProjectiveFullRankFamily {ι : Type*} (N : ℕ) (d : ι → ℕ) :
    Set (complexProjectiveFullRankParamsOpens N d × ℙ ℂ (Fin N → ℂ)) :=
  complexProjectiveFamily
    (Subtype.val : complexProjectiveFullRankParamsOpens N d →
      ∀ k, homogeneousSubmodule (Fin N) ℂ (d k))

/-- The projection of `TauCeti.complexProjectiveFullRankFamily` to the open full-rank parameter
locus is proper. -/
theorem isProperMap_fst_complexProjectiveFullRankFamily {ι : Type*} {N : ℕ} (d : ι → ℕ) :
    IsProperMap fun x : complexProjectiveFullRankFamily N d ↦ x.1.1 :=
  ComplexProjectiveFamily.isProperMap_fst _ continuous_subtype_val

variable {ι : Type*} [Fintype ι] {n : ℕ} (d : ι → ℕ)

/-- The global complex analytic chart atlas on `TauCeti.complexProjectiveFullRankFamily (n + 1) d`,
modelled on `(∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) × (Fin (n - |ι|) → ℂ)`. -/
noncomputable instance instChartedSpaceComplexProjectiveFullRankFamily :
    ChartedSpace
      ((∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) × (Fin (n - Fintype.card ι) → ℂ))
      (complexProjectiveFullRankFamily (n + 1) d) :=
  ComplexProjectiveFamily.chartedSpace (IB := homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d)
    (r := ω) le_top contMDiff_subtype_val
    (fun b ↦ mem_complexProjectiveFullRankParamsOpens.mp b.2)

/-- The universal full-rank projective incidence family is a complex `C^r` (and analytic)
manifold for every `r : ℕ∞ω`. -/
instance instIsManifoldComplexProjectiveFullRankFamily (r : ℕ∞ω) :
    IsManifold
      𝓘(ℂ, (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) ×
        (Fin (n - Fintype.card ι) → ℂ)) r
      (complexProjectiveFullRankFamily (n + 1) d) :=
  (ComplexProjectiveFamily.isManifold (IB := homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d)
    (r := ω) le_top contMDiff_subtype_val
    (fun b ↦ mem_complexProjectiveFullRankParamsOpens.mp b.2)).of_le le_top

/-- With the same complex charts, the universal full-rank projective incidence family is a real
`C^r` manifold for every `r : ℕ∞ω`. -/
instance instIsManifoldComplexProjectiveFullRankFamilyReal (r : ℕ∞ω) :
    IsManifold
      𝓘(ℝ, (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) ×
        (Fin (n - Fintype.card ι) → ℂ)) r
      (complexProjectiveFullRankFamily (n + 1) d) :=
  (instIsManifoldComplexProjectiveFullRankFamily d r).restrictScalars ℝ

/-- **The universal full-rank projective incidence projection is a `C^r` submersion** (holomorphic
for `𝕜 = ℂ, r = ω` and real smooth for `𝕜 = ℝ`) with fiber model `Fin (n - |ι|) → ℂ`. -/
theorem isSubmersionOfComplement_fst_complexProjectiveFullRankFamily
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (r : ℕ∞ω) :
    letI : IsManifold
        𝓘(𝕜, (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) ×
          (Fin (n - Fintype.card ι) → ℂ)) r
        (complexProjectiveFullRankFamily (n + 1) d) :=
      (instIsManifoldComplexProjectiveFullRankFamily d r).restrictScalars 𝕜
    letI : ∀ k, IsManifold 𝓘(𝕜, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) r
        (homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) := fun k ↦
      (instIsManifoldHomogeneousSubmodule (d k) r).restrictScalars 𝕜
    Manifold.IsSubmersionOfComplement (Fin (n - Fintype.card ι) → ℂ)
      𝓘(𝕜, (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) ×
        (Fin (n - Fintype.card ι) → ℂ))
      (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r
      (fun x : complexProjectiveFullRankFamily (n + 1) d ↦ x.1.1) := by
  have : IsManifold
      𝓘(𝕜, (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) ×
        (Fin (n - Fintype.card ι) → ℂ)) r
      (complexProjectiveFullRankFamily (n + 1) d) :=
    (instIsManifoldComplexProjectiveFullRankFamily d r).restrictScalars 𝕜
  have : ∀ k, IsManifold 𝓘(𝕜, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) r
      (homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) := fun k ↦
    (instIsManifoldHomogeneousSubmodule (d k) r).restrictScalars 𝕜
  refine Manifold.isSubmersionOfComplement_iff.mpr fun z ↦ ?_
  let dom := chartAt
    ((∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) × (Fin (n - Fintype.card ι) → ℂ)) z
  let cod := chartAt (ModelPi fun k ↦ {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) z.1.1
  refine Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt
    (continuous_fst.comp continuous_subtype_val).continuousAt
    (ContinuousLinearEquiv.refl 𝕜 _) dom cod (mem_chart_source _ z) (mem_chart_source _ z.1.1)
    (IsManifold.chart_mem_maximalAtlas z) (IsManifold.chart_mem_maximalAtlas z.1.1) ?_
  intro v hv
  have hv' : v ∈ dom.target := by simpa using hv
  have hy_dom : dom.symm v ∈ dom.source := dom.map_target hv'
  let sliceFam := ComplexProjectiveFamily.sliceChartAt
    (IB := homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d)
    (r := ω) le_top contMDiff_subtype_val
    (fun b ↦ mem_complexProjectiveFullRankParamsOpens.mp b.2)
  have hdom_eq : dom = linearSliceChart sliceFam
      (ComplexProjectiveFamily.isSliceChart_sliceChartAt
        (IB := homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d)
        (r := ω) le_top contMDiff_subtype_val
        (fun b ↦ mem_complexProjectiveFullRankParamsOpens.mp b.2)) z :=
    linearSliceChartedSpace_chartAt _ _ _ z
  have hdom_src : dom.source = Subtype.val ⁻¹' (sliceFam z).source := by
    rw [hdom_eq, linearSliceChart_source]
  have hy_slice : (dom.symm v :
      complexProjectiveFullRankParamsOpens (n + 1) d × ℙ ℂ (Fin (n + 1) → ℂ)) ∈
        (sliceFam z).source := by
    rwa [hdom_src] at hy_dom
  have hfst := (ComplexProjectiveFamily.sliceChartAt_apply_of_mem_source
    (IB := homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d)
    (r := ω) le_top contMDiff_subtype_val
    (fun b ↦ mem_complexProjectiveFullRankParamsOpens.mp b.2) z hy_slice).1
  have hdom_apply : dom (dom.symm v) = (sliceFam z (dom.symm v).1).1 := by
    rw [hdom_eq, linearSliceChart_apply]
  have hv1 : v.1 = extChartAt (homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d) z.1.1
      (dom.symm v).1.1 :=
    (congrArg Prod.fst (dom.right_inv hv')).symm.trans ((congrArg Prod.fst hdom_apply).trans hfst)
  simpa [extChartAt, homogeneousFamilyModel] using hv1.symm

/-- **The universal full-rank projective incidence projection is a `C^r` submersion.** -/
theorem isSubmersion_fst_complexProjectiveFullRankFamily
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (r : ℕ∞ω) :
    letI : IsManifold
        𝓘(𝕜, (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) ×
          (Fin (n - Fintype.card ι) → ℂ)) r
        (complexProjectiveFullRankFamily (n + 1) d) :=
      (instIsManifoldComplexProjectiveFullRankFamily d r).restrictScalars 𝕜
    letI : ∀ k, IsManifold 𝓘(𝕜, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) r
        (homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) := fun k ↦
      (instIsManifoldHomogeneousSubmodule (d k) r).restrictScalars 𝕜
    Manifold.IsSubmersion
      𝓘(𝕜, (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) ×
        (Fin (n - Fintype.card ι) → ℂ))
      (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r
      (fun x : complexProjectiveFullRankFamily (n + 1) d ↦ x.1.1) := by
  have : IsManifold
      𝓘(𝕜, (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) ×
        (Fin (n - Fintype.card ι) → ℂ)) r
      (complexProjectiveFullRankFamily (n + 1) d) :=
    (instIsManifoldComplexProjectiveFullRankFamily d r).restrictScalars 𝕜
  have : ∀ k, IsManifold 𝓘(𝕜, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) r
      (homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) := fun k ↦
    (instIsManifoldHomogeneousSubmodule (d k) r).restrictScalars 𝕜
  exact (isSubmersionOfComplement_fst_complexProjectiveFullRankFamily d 𝕜 r).isSubmersion

end UniversalFullRank

end TauCeti
