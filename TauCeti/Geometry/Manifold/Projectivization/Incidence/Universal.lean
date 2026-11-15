/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Submersion
public import TauCeti.Geometry.Manifold.Instances.HomogeneousSubmodule
public import TauCeti.Geometry.Manifold.ModelTransport.LinearSlice
public import TauCeti.Geometry.Manifold.Projectivization.Incidence.Basic
public import TauCeti.Geometry.Manifold.Projectivization.ZeroLocus

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# The universal projective incidence variety as a complex submanifold

For a finite family of degrees `d : ι → ℕ` in `n + 1` homogeneous variables, the universal
incidence variety `TauCeti.complexProjectiveIncidence (n + 1) d` consists of pairs `(c, L)` of a
coefficient family `c : ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)` and a projective line
`L ∈ ℙ ℂ (Fin (n + 1) → ℂ)` at which all equations `c k` vanish. Unlike an individual zero locus
`complexProjectiveZeroLocus`, the universal incidence variety is smooth at *every* point, including
over singular or empty fibers: in any standard affine chart `U_i`, varying `X_i ^ (d k)` already
makes the joint derivative of the chart equations surjective
(`TauCeti.surjective_fderiv_projectiveIncidenceChartEquations_comp`).

Applying the complemented-kernel holomorphic implicit function theorem to those chart equations
produces ambient analytic slice charts `TauCeti.complexProjectiveIncidenceSliceChart` on
`(∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ)`. Through
`TauCeti.linearSliceChartedSpace`, they equip `complexProjectiveIncidence (n + 1) d` with a global
`ChartedSpace` instance of pure complex dimension `dim_ℂ C + n - |ι|` (where `C` is the monomial
coefficient space `∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ`), making it an analytic
manifold over `ℂ` (and a smooth manifold over `ℝ`) whose inclusion into the ambient product is a
`C^r` embedding with normal model `ι → ℂ`.

At an incidence point `(c, L)` with `L ∈ affineOpen i`, the tangent space of the universal
incidence variety is the kernel of the differential of the chart equations, and its normal space is
canonically isomorphic to `ι → ℂ`. Combining this tangent description with the linear parameter
projection criterion `TauCeti.surjective_parameterProj_projectiveIncidenceChartEquations_iff` shows
that the first projection `complexProjectiveIncidence (n + 1) d → ∀ k, homogeneousSubmodule ...` is
a holomorphic (or `C^r`, `1 ≤ r`) submersion at `(c, L)` if and only if the cone Jacobian of `c` at
`L.rep` is surjective (`TauCeti.isSubmersionAt_fst_complexProjectiveIncidence_iff`).

## Main declarations

* `TauCeti.complexProjectiveIncidenceSliceChart`: ambient analytic slice chart flattening
  `complexProjectiveIncidence (n + 1) d` near `(c, L)` (`L ∈ affineOpen i`).
* `TauCeti.instChartedSpaceComplexProjectiveIncidence`: global complex coordinates on
  `complexProjectiveIncidence (n + 1) d`.
* `TauCeti.instIsManifoldComplexProjectiveIncidence` and
  `TauCeti.instIsManifoldComplexProjectiveIncidenceReal`: `C^r` manifold instances over `ℂ` and
  `ℝ`.
* `TauCeti.isImmersionOfComplement_subtypeVal_complexProjectiveIncidence` and
  `TauCeti.isSmoothEmbedding_subtypeVal_complexProjectiveIncidence`: the inclusion into the ambient
  product is a `C^r` immersion with complement `ι → ℂ` and a `C^r` embedding.
* `TauCeti.complexProjectiveIncidenceEmbedding`,
  `TauCeti.tangentRange_complexProjectiveIncidenceEmbedding`, and
  `TauCeti.complexProjectiveIncidenceNormalSpaceEquiv`: bundled embedding, tangent space as the
  kernel of the chart-equation differential, and normal-space isomorphism onto `ι → ℂ`.
* `TauCeti.isSubmersionAt_fst_complexProjectiveIncidence_iff`: the universal projection to
  coefficients is a `C^r` (`1 ≤ r`) complex submersion at `x` precisely when the cone Jacobian is
  surjective at `x`.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Lecture 14, for smoothness of the universal
  incidence correspondence and the Jacobian criterion for its projection.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §2, for holomorphic
  slice charts of projective submanifolds.
-/

public section

open Filter Function MvPolynomial Projectivization Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization Topology

namespace TauCeti

namespace ComplexProjectiveIncidence

section General

variable {ι : Type*} {n : ℕ}

/-- The monomial-coefficient vector space for homogeneous polynomial families of degrees `d` in
`n + 1` variables. -/
private abbrev CoeffSpace (n : ℕ) (d : ι → ℕ) :=
  ∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ

/-- The ambient product of the native homogeneous polynomial family space and projective space. -/
private abbrev Amb (n : ℕ) (d : ι → ℕ) :=
  (∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ)

/-- The inverse monomial-coefficient equivalence as a continuous linear parametrization of the
homogeneous polynomial family space. -/
private noncomputable abbrev coeffParam (d : ι → ℕ) :
    CoeffSpace n d →L[ℂ] ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k) :=
  (homogeneousFamilyCoeffEquiv (σ := Fin (n + 1)) (R := ℂ) d).symm.toContinuousLinearMap

/-- The universal incidence equations in the `i`-th affine chart and monomial-coefficient
coordinates. -/
private noncomputable abbrev chartEqns (d : ι → ℕ) (i : Fin (n + 1)) :
    (Fin n → ℂ) × CoeffSpace n d → ι → ℂ :=
  fun q ↦ projectiveIncidenceChartEquations i q.1 (coeffParam d q.2)

/-- The coordinate chart on the ambient product sending `(c, L)` (`L ∈ affineOpen i`) to
`(affineChart i L, homogeneousFamilyCoeffEquiv d c)`. -/
private noncomputable def ambChart (d : ι → ℕ) (i : Fin (n + 1)) :
    OpenPartialHomeomorph (Amb n d) ((Fin n → ℂ) × CoeffSpace n d) :=
  ((homogeneousFamilyCoeffEquiv d).toHomeomorph.toOpenPartialHomeomorph.prod
    (affineOpenPartialHomeomorph i)).transHomeomorph (Homeomorph.prodComm _ _)

private theorem ambChart_apply (d : ι → ℕ) (i : Fin (n + 1)) (p : Amb n d) :
    ambChart d i p = (affineChart i p.2, homogeneousFamilyCoeffEquiv d p.1) := by
  simp [ambChart]

private theorem ambChart_symm_apply (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d) :
    (ambChart d i).symm q =
      ((homogeneousFamilyCoeffEquiv d).symm q.2, (affineChart i).symm q.1) := by
  simp [ambChart]

private theorem ambChart_source (d : ι → ℕ) (i : Fin (n + 1)) :
    (ambChart d i).source = univ ×ˢ affineOpen i := by
  simp [ambChart]

private theorem ambChart_target (d : ι → ℕ) (i : Fin (n + 1)) :
    (ambChart d i).target = univ := by
  simp [ambChart]

end General

section FintypeContDiff

variable {ι : Type*} [Fintype ι] {n : ℕ}

private theorem contDiff_chartEqns (d : ι → ℕ) (i : Fin (n + 1)) {r : ℕ∞ω} :
    ContDiff ℂ r (chartEqns d i) :=
  contDiff_iff_contDiffAt.2 fun q ↦
    (analyticAt_projectiveIncidenceChartEquations_comp (coeffParam d) i q).contDiffAt

end FintypeContDiff

section Finite

variable {ι : Type*} [Finite ι] {n : ℕ}

private theorem hasStrictFDerivAt_chartEqns (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d) :
    HasStrictFDerivAt (chartEqns d i) (fderiv ℂ (chartEqns d i) q) q := by
  cases nonempty_fintype ι
  exact (contDiff_chartEqns d i (r := 1)).contDiffAt.hasStrictFDerivAt_fderiv one_ne_zero

private theorem surjective_fderiv_chartEqns (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d) :
    Surjective (fderiv ℂ (chartEqns d i) q) := by
  cases nonempty_fintype ι
  exact surjective_fderiv_projectiveIncidenceChartEquations_comp (coeffParam d)
    (by simpa [coeffParam] using
      (homogeneousFamilyCoeffEquiv (σ := Fin (n + 1)) (R := ℂ) d).symm.surjective) i q.1 q.2

private theorem range_fderiv_chartEqns (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d) :
    (fderiv ℂ (chartEqns d i) q).range = ⊤ :=
  LinearMap.range_eq_top.2 (surjective_fderiv_chartEqns d i q)

private theorem fderiv_chartEqns_ambChart (d : ι → ℕ) (i : Fin (n + 1)) (p : Amb n d) :
    fderiv ℂ (chartEqns d i) (ambChart d i p) =
      (fderiv ℂ (fun a ↦ projectiveIncidenceChartEquations i a p.1)
        (affineChart i p.2)).coprod
        ((projectiveIncidenceChartEquations (d := d) i (affineChart i p.2)).comp
          (coeffParam d)) := by
  cases nonempty_fintype ι
  have h := (hasFDerivAt_projectiveIncidenceChartEquations_comp (coeffParam d) i
    (affineChart i p.2) (homogeneousFamilyCoeffEquiv d p.1)).fderiv
  have hparam : coeffParam d (homogeneousFamilyCoeffEquiv d p.1) = p.1 :=
    (homogeneousFamilyCoeffEquiv (σ := Fin (n + 1)) (R := ℂ) d).symm_apply_apply p.1
  rw [← ambChart_apply d i p, hparam] at h
  exact h

end Finite

section Fintype

variable {ι : Type*} [Fintype ι] {n : ℕ}

private theorem card_add_finrank_ker_fderiv_chartEqns (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d) :
    Fintype.card ι + Module.finrank ℂ (fderiv ℂ (chartEqns d i) q).ker =
      Module.finrank ℂ (CoeffSpace n d) + n := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℂ (chartEqns d i) q : (Fin n → ℂ) × CoeffSpace n d →ₗ[ℂ] ι → ℂ)
  rw [range_fderiv_chartEqns d i q, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

private theorem card_le_finrank_add (d : ι → ℕ) :
    Fintype.card ι ≤ Module.finrank ℂ (CoeffSpace n d) + n := by
  have := card_add_finrank_ker_fderiv_chartEqns (n := n) d 0 0
  omega

private theorem contMDiffOn_ambChart {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (d : ι → ℕ) (i : Fin (n + 1)) (r : ℕ∞ω)
    [IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ))] :
    ContMDiffOn ((homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d).prod 𝓘(𝕜, Fin n → ℂ))
      𝓘(𝕜, (Fin n → ℂ) × CoeffSpace n d) r (ambChart d i) (ambChart d i).source := by
  have hproj : ContMDiffOn 𝓘(𝕜, Fin n → ℂ) 𝓘(𝕜, Fin n → ℂ) r (affineChart (K := ℂ) i)
      (affineOpen (K := ℂ) i) := by
    simpa using contMDiffOn_of_mem_maximalAtlas
      (affineOpenPartialHomeomorph_mem_maximalAtlas (𝕜 := ℂ) (I := 𝓘(𝕜, Fin n → ℂ)) (r := r) i)
  rw [ambChart_source]
  have h1 : ContMDiffOn ((homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d).prod 𝓘(𝕜, Fin n → ℂ))
      𝓘(𝕜, Fin n → ℂ) r (fun p : Amb n d ↦ affineChart i p.2) (univ ×ˢ affineOpen i) :=
    hproj.comp contMDiff_snd.contMDiffOn fun _ hp ↦ hp.2
  have h2 : ContMDiffOn ((homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d).prod 𝓘(𝕜, Fin n → ℂ))
      𝓘(𝕜, CoeffSpace n d) r
      (fun p : Amb n d ↦
        homogeneousFamilyCoeffDiffeomorph (σ := Fin (n + 1)) (𝕜' := ℂ) 𝕜 d r p.1)
      (univ ×ˢ affineOpen i) :=
    ((homogeneousFamilyCoeffDiffeomorph (σ := Fin (n + 1)) (𝕜' := ℂ) 𝕜 d r).contMDiff.comp
      contMDiff_fst).contMDiffOn
  exact (h1.prodMk_space h2).congr fun p _ ↦ by simp [ambChart_apply]

private theorem contMDiff_ambChart_symm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] (d : ι → ℕ) (i : Fin (n + 1)) (r : ℕ∞ω)
    [IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ))] :
    ContMDiff 𝓘(𝕜, (Fin n → ℂ) × CoeffSpace n d)
      ((homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d).prod 𝓘(𝕜, Fin n → ℂ)) r
      (ambChart d i).symm := by
  have hproj : ContMDiff 𝓘(𝕜, Fin n → ℂ) 𝓘(𝕜, Fin n → ℂ) r (affineChart (K := ℂ) i).symm := by
    rw [← contMDiffOn_univ]
    simpa using contMDiffOn_symm_of_mem_maximalAtlas
      (affineOpenPartialHomeomorph_mem_maximalAtlas (𝕜 := ℂ) (I := 𝓘(𝕜, Fin n → ℂ)) (r := r) i)
  have hfun : ⇑(ambChart d i).symm = fun q : (Fin n → ℂ) × CoeffSpace n d ↦
      ((homogeneousFamilyCoeffDiffeomorph (σ := Fin (n + 1)) (𝕜' := ℂ) 𝕜 d r).symm q.2,
        (affineChart i).symm q.1) := by
    ext1 q
    simp [ambChart_symm_apply]
  rw [hfun]
  exact ((homogeneousFamilyCoeffDiffeomorph (σ := Fin (n + 1)) (𝕜' := ℂ) 𝕜 d r).symm.contMDiff.comp
    contDiff_snd.contMDiff).prodMk (hproj.comp contDiff_fst.contMDiff)

private noncomputable def implicitChart (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d) :
    OpenPartialHomeomorph ((Fin n → ℂ) × CoeffSpace n d)
      ((ι → ℂ) × (fderiv ℂ (chartEqns d i) q).ker) :=
  (hasStrictFDerivAt_chartEqns d i q).implicitToOpenPartialHomeomorphOfComplemented _ _
    (range_fderiv_chartEqns d i q)
    (ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _)

private noncomputable def implicitSource (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d) : Set ((Fin n → ℂ) × CoeffSpace n d) :=
  (hasStrictFDerivAt_chartEqns d i q).implicitCoordSource (range_fderiv_chartEqns d i q)
    (ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _)

private theorem isOpen_implicitSource (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d) : IsOpen (implicitSource d i q) :=
  (hasStrictFDerivAt_chartEqns d i q).isOpen_implicitCoordSource _ _

private noncomputable def coordEquiv (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d) :
    ((ι → ℂ) × (fderiv ℂ (chartEqns d i) q).ker) ≃L[ℂ]
      (Fin (Module.finrank ℂ (CoeffSpace n d) + n - Fintype.card ι) → ℂ) × (ι → ℂ) :=
  (ContinuousLinearEquiv.prodComm ℂ _ _).trans
    ((ContinuousLinearEquiv.ofFinrankEq (by
      have := card_add_finrank_ker_fderiv_chartEqns d i q
      rw [Module.finrank_fin_fun]
      omega)).prodCongr (ContinuousLinearEquiv.refl ℂ _))

private noncomputable def modelEquiv (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (d : ι → ℕ) :
    ((Fin (Module.finrank ℂ (CoeffSpace n d) + n - Fintype.card ι) → ℂ) × (ι → ℂ)) ≃L[𝕜]
      CoeffSpace n d × (Fin n → ℂ) :=
  (ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℂ) (by
    have := card_le_finrank_add (n := n) d
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]
    omega)).restrictScalars' 𝕜

@[simp]
private theorem coordEquiv_apply_snd (d : ι → ℕ) (i : Fin (n + 1))
    (q : (Fin n → ℂ) × CoeffSpace n d)
    (v : (ι → ℂ) × (fderiv ℂ (chartEqns d i) q).ker) :
    (coordEquiv d i q v).2 = v.1 :=
  (rfl)

end Fintype

end ComplexProjectiveIncidence

open ComplexProjectiveIncidence

section SliceChart

variable {ι : Type*} [Fintype ι] {n : ℕ} {d : ι → ℕ}

/-- **The ambient slice chart of the universal projective incidence variety.** For any coefficient
family `c` and projective point `L ∈ affineOpen i`, this is an analytic chart of
`(∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ)` around `(c, L)` whose
second component evaluates `TauCeti.projectiveIncidenceChartEquations i (affineChart i ·) ·` and
which therefore flattens `TauCeti.complexProjectiveIncidence (n + 1) d` onto `univ ×ˢ {0}`. -/
noncomputable def complexProjectiveIncidenceSliceChart
    (c : ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k))
    {i : Fin (n + 1)} {L : ℙ ℂ (Fin (n + 1) → ℂ)} (hi : L ∈ affineOpen i) :
    OpenPartialHomeomorph
      ((∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ))
      ((Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ) × (ι → ℂ)) :=
  let q := ambChart d i (c, L)
  let _ := hi
  (ambChart d i).trans
    (((implicitChart d i q).restrOpen (implicitSource d i q)
      (isOpen_implicitSource d i q)).transHomeomorph (coordEquiv d i q).toHomeomorph)

variable (c : ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k))
  {i : Fin (n + 1)} {L : ℙ ℂ (Fin (n + 1) → ℂ)} (hi : L ∈ affineOpen i)

private theorem coe_complexProjectiveIncidenceSliceChart :
    ⇑(complexProjectiveIncidenceSliceChart c hi) =
      coordEquiv d i (ambChart d i (c, L)) ∘ implicitChart d i (ambChart d i (c, L)) ∘
        ambChart d i := by
  rw [complexProjectiveIncidenceSliceChart, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.transHomeomorph_apply, OpenPartialHomeomorph.coe_restrOpen,
    ContinuousLinearEquiv.coe_toHomeomorph]
  rfl

private theorem coe_complexProjectiveIncidenceSliceChart_symm :
    ⇑(complexProjectiveIncidenceSliceChart c hi).symm =
      (ambChart d i).symm ∘ (implicitChart d i (ambChart d i (c, L))).symm ∘
        (coordEquiv d i (ambChart d i (c, L))).symm := by
  rw [complexProjectiveIncidenceSliceChart, OpenPartialHomeomorph.coe_trans_symm,
    OpenPartialHomeomorph.transHomeomorph_symm_apply, OpenPartialHomeomorph.coe_restrOpen_symm,
    ContinuousLinearEquiv.coe_symm_toHomeomorph]

private theorem complexProjectiveIncidenceSliceChart_source :
    (complexProjectiveIncidenceSliceChart c hi).source =
      (univ ×ˢ affineOpen i) ∩ ambChart d i ⁻¹'
        ((implicitChart d i (ambChart d i (c, L))).source ∩
          implicitSource d i (ambChart d i (c, L))) := by
  rw [complexProjectiveIncidenceSliceChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.transHomeomorph_source, OpenPartialHomeomorph.restrOpen_source,
    ambChart_source]

private theorem complexProjectiveIncidenceSliceChart_target :
    (complexProjectiveIncidenceSliceChart c hi).target =
      (coordEquiv d i (ambChart d i (c, L))).symm ⁻¹'
        ((implicitChart d i (ambChart d i (c, L))).target ∩
          (implicitChart d i (ambChart d i (c, L))).symm ⁻¹'
            implicitSource d i (ambChart d i (c, L))) := by
  rw [complexProjectiveIncidenceSliceChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.transHomeomorph_target, OpenPartialHomeomorph.restrOpen_toPartialEquiv,
    ambChart_target]
  simp

/-- The second component of `TauCeti.complexProjectiveIncidenceSliceChart` evaluates the ratio-chart
incidence equations. -/
@[simp]
theorem complexProjectiveIncidenceSliceChart_apply_snd
    (p : (∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ)) :
    (complexProjectiveIncidenceSliceChart c hi p).2 =
      projectiveIncidenceChartEquations i (affineChart i p.2) p.1 := by
  rw [coe_complexProjectiveIncidenceSliceChart, comp_apply, coordEquiv_apply_snd, comp_apply,
    implicitChart, HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_fst]
  simp [chartEqns, coeffParam, ambChart_apply]

/-- The source of `TauCeti.complexProjectiveIncidenceSliceChart` lies over `affineOpen i`. -/
theorem complexProjectiveIncidenceSliceChart_source_subset :
    (complexProjectiveIncidenceSliceChart c hi).source ⊆ univ ×ˢ affineOpen i := by
  rw [complexProjectiveIncidenceSliceChart_source]
  exact inter_subset_left

/-- The ambient slice chart is defined at its centre `(c, L)`. -/
theorem mem_complexProjectiveIncidenceSliceChart_source :
    (c, L) ∈ (complexProjectiveIncidenceSliceChart c hi).source := by
  rw [complexProjectiveIncidenceSliceChart_source]
  exact ⟨⟨trivial, hi⟩,
    (hasStrictFDerivAt_chartEqns d i _).mem_implicitToOpenPartialHomeomorphOfComplemented_source
      _ _,
    (hasStrictFDerivAt_chartEqns d i _).mem_implicitCoordSource _ _⟩

/-- **The ambient slice chart flattens the universal incidence variety.** -/
theorem isSliceChart_complexProjectiveIncidenceSliceChart :
    IsSliceChart (complexProjectiveIncidenceSliceChart c hi)
      ((univ : Set (Fin (Module.finrank ℂ
        (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n - Fintype.card ι) → ℂ)) ×ˢ
        ({0} : Set (ι → ℂ)))
      (complexProjectiveIncidence (n + 1) d) := by
  refine isSliceChart_iff.2 fun p hp ↦ ?_
  have hpi : p.2 ∈ affineOpen i :=
    (complexProjectiveIncidenceSliceChart_source_subset c hi hp).2
  rw [← Prod.eta p, mem_complexProjectiveIncidence_iff_projectiveIncidenceChartEquations_eq_zero
    p.1 hpi]
  simp

/-- The ambient slice chart is `C^r` over any normed base field `𝕜` acting on `ℂ` (in particular
holomorphic for `𝕜 = ℂ, r = ω` and real smooth for `𝕜 = ℝ`). -/
theorem contMDiffOn_complexProjectiveIncidenceSliceChart
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (r : ℕ∞ω)
    [IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ))] :
    ContMDiffOn ((homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d).prod 𝓘(𝕜, Fin n → ℂ))
      𝓘(𝕜, (Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ) × (ι → ℂ)) r
      (complexProjectiveIncidenceSliceChart c hi)
      (complexProjectiveIncidenceSliceChart c hi).source := by
  intro p hp
  have hp_amb : p ∈ (ambChart d i).source := by
    rw [ambChart_source]
    exact complexProjectiveIncidenceSliceChart_source_subset c hi hp
  have hamb : ContMDiffAt ((homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d).prod 𝓘(𝕜, Fin n → ℂ))
      𝓘(𝕜, (Fin n → ℂ) × CoeffSpace n d) r (ambChart d i) p :=
    (contMDiffOn_ambChart d i r).contMDiffAt ((ambChart d i).open_source.mem_nhds hp_amb)
  let q := ambChart d i (c, L)
  have himp : ContDiffAt ℂ r (coordEquiv d i q ∘ implicitChart d i q) (ambChart d i p) :=
    (coordEquiv d i q).contDiff.contDiffAt.comp _
      ((hasStrictFDerivAt_chartEqns d i q).contDiffAt_implicitToOpenPartialHomeomorphOfComplemented
        (contDiff_chartEqns d i).contDiffAt _ _)
  rw [coe_complexProjectiveIncidenceSliceChart]
  exact ((himp.restrict_scalars 𝕜).contMDiffAt.comp p hamb).contMDiffWithinAt

/-- The inverse of `TauCeti.complexProjectiveIncidenceSliceChart` is `C^r` on its target over any
normed base field `𝕜` acting on `ℂ`. -/
theorem contMDiffOn_complexProjectiveIncidenceSliceChart_symm
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (r : ℕ∞ω)
    [IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ))] :
    ContMDiffOn
      𝓘(𝕜, (Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ) × (ι → ℂ))
      ((homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d).prod 𝓘(𝕜, Fin n → ℂ)) r
      (complexProjectiveIncidenceSliceChart c hi).symm
      (complexProjectiveIncidenceSliceChart c hi).target := by
  intro v hv
  rw [complexProjectiveIncidenceSliceChart_target] at hv
  obtain ⟨hvt, hvs⟩ := hv
  let q := ambChart d i (c, L)
  have hq := hasStrictFDerivAt_chartEqns d i q
  have hinv : ContDiffAt ℂ r ((implicitChart d i q).symm ∘ (coordEquiv d i q).symm) v :=
    (hq.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_mem
      _ _ hvt hvs (contDiff_chartEqns d i).contDiffAt).comp v
        (coordEquiv d i q).symm.contDiff.contDiffAt
  rw [coe_complexProjectiveIncidenceSliceChart_symm]
  exact (((contMDiff_ambChart_symm (𝕜 := 𝕜) d i r).contMDiffAt).comp v
    (hinv.restrict_scalars 𝕜).contMDiffAt).contMDiffWithinAt

end SliceChart

/-! ### Global manifold structure and ambient embedding -/

section ManifoldAndEmbedding

variable {ι : Type*} [Fintype ι] {n : ℕ} {d : ι → ℕ}

/-- The preferred ambient slice chart at a point `z` of `TauCeti.complexProjectiveIncidence`,
evaluated in `(exists_mem_affineOpen z.1.2).choose`. -/
noncomputable def ComplexProjectiveIncidence.sliceChartAt (n : ℕ) (d : ι → ℕ)
    (z : complexProjectiveIncidence (n + 1) d) :
    OpenPartialHomeomorph
      ((∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ))
      ((Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ) × (ι → ℂ)) :=
  complexProjectiveIncidenceSliceChart z.1.1 (exists_mem_affineOpen z.1.2).choose_spec

/-- The preferred ambient slice chart at `z` flattens `TauCeti.complexProjectiveIncidence` onto
`univ ×ˢ {0}`. -/
theorem ComplexProjectiveIncidence.isSliceChart_sliceChartAt (n : ℕ) (d : ι → ℕ)
    (z : complexProjectiveIncidence (n + 1) d) :
    IsSliceChart (ComplexProjectiveIncidence.sliceChartAt n d z)
      ((univ : Set (Fin (Module.finrank ℂ
        (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n - Fintype.card ι) → ℂ)) ×ˢ
        ({0} : Set (ι → ℂ)))
      (complexProjectiveIncidence (n + 1) d) :=
  isSliceChart_complexProjectiveIncidenceSliceChart z.1.1
    (exists_mem_affineOpen z.1.2).choose_spec

/-- Every point `z` of `TauCeti.complexProjectiveIncidence` belongs to the source of its preferred
ambient slice chart. -/
theorem ComplexProjectiveIncidence.mem_sliceChartAt_source (n : ℕ) (d : ι → ℕ)
    (z : complexProjectiveIncidence (n + 1) d) :
    (z : (∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ)) ∈
      (ComplexProjectiveIncidence.sliceChartAt n d z).source :=
  mem_complexProjectiveIncidenceSliceChart_source z.1.1
    (exists_mem_affineOpen z.1.2).choose_spec

/-- The global complex chart atlas on `TauCeti.complexProjectiveIncidence (n + 1) d`, induced by
`TauCeti.complexProjectiveIncidenceSliceChart` in the preferred affine chart at each projective
point. -/
noncomputable instance instChartedSpaceComplexProjectiveIncidence (d : ι → ℕ) :
    ChartedSpace
      (Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ)
      (complexProjectiveIncidence (n + 1) d) :=
  linearSliceChartedSpace (ComplexProjectiveIncidence.sliceChartAt n d)
    (ComplexProjectiveIncidence.isSliceChart_sliceChartAt n d)
    (ComplexProjectiveIncidence.mem_sliceChartAt_source n d)

/-- The universal projective incidence variety is an analytic (and `C^r`) complex manifold of pure
dimension `dim_ℂ C + n - |ι|`. -/
instance instIsManifoldComplexProjectiveIncidence (d : ι → ℕ) (r : ℕ∞ω) :
    IsManifold
      𝓘(ℂ, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ) r
      (complexProjectiveIncidence (n + 1) d) :=
  isManifold_linearSliceChartedSpace (ComplexProjectiveIncidence.sliceChartAt n d)
    (ComplexProjectiveIncidence.isSliceChart_sliceChartAt n d)
    (fun z _ hp ↦ (contMDiffOn_complexProjectiveIncidenceSliceChart (𝕜 := ℂ) z.1.1
      (exists_mem_affineOpen z.1.2).choose_spec r).contMDiffAt
        ((OpenPartialHomeomorph.open_source _).mem_nhds hp))
    (fun z _ hv ↦ (contMDiffOn_complexProjectiveIncidenceSliceChart_symm (𝕜 := ℂ) z.1.1
      (exists_mem_affineOpen z.1.2).choose_spec r).contMDiffAt
        ((OpenPartialHomeomorph.open_target _).mem_nhds hv))
    (ComplexProjectiveIncidence.mem_sliceChartAt_source n d)

/-- With the same complex charts, the universal projective incidence variety is a real `C^r`
manifold. -/
instance instIsManifoldComplexProjectiveIncidenceReal (d : ι → ℕ) (r : ℕ∞ω) :
    IsManifold
      𝓘(ℝ, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ) r
      (complexProjectiveIncidence (n + 1) d) :=
  (instIsManifoldComplexProjectiveIncidence d r).restrictScalars ℝ

section Embedding

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (d : ι → ℕ) (r : ℕ∞ω)
  [IsManifold 𝓘(𝕜, Fin n → ℂ) r (ℙ ℂ (Fin (n + 1) → ℂ))]
  [∀ k, IsManifold 𝓘(𝕜, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) r
    (homogeneousSubmodule (Fin (n + 1)) ℂ (d k))]

/-- **The inclusion of the universal projective incidence variety is an immersion with normal model
`ι → ℂ`.** Taking `𝕜 = ℂ` gives the holomorphic/complex `C^r` immersion; taking `𝕜 = ℝ` gives the
underlying real `C^r` immersion. -/
theorem isImmersionOfComplement_subtypeVal_complexProjectiveIncidence :
    Manifold.IsImmersionOfComplement (ι → ℂ)
      𝓘(𝕜, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ)
      ((homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d).prod 𝓘(𝕜, Fin n → ℂ)) r
      (Subtype.val : complexProjectiveIncidence (n + 1) d →
        (∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ)) :=
  isImmersionOfComplement_subtypeVal_linearSliceChartedSpace_of_boundaryless
    (ComplexProjectiveIncidence.sliceChartAt n d)
    (ComplexProjectiveIncidence.isSliceChart_sliceChartAt n d)
    (fun _ ↦ modelEquiv 𝕜 d)
    (fun z ↦ contMDiffOn_complexProjectiveIncidenceSliceChart (𝕜 := 𝕜) z.1.1
      (exists_mem_affineOpen z.1.2).choose_spec r)
    (fun z ↦ contMDiffOn_complexProjectiveIncidenceSliceChart_symm (𝕜 := 𝕜) z.1.1
      (exists_mem_affineOpen z.1.2).choose_spec r)
    (ComplexProjectiveIncidence.mem_sliceChartAt_source n d)

/-- **The universal projective incidence variety is an embedded submanifold of the ambient
product.** -/
theorem isSmoothEmbedding_subtypeVal_complexProjectiveIncidence :
    Manifold.IsSmoothEmbedding
      𝓘(𝕜, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ)
      ((homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d).prod 𝓘(𝕜, Fin n → ℂ)) r
      (Subtype.val : complexProjectiveIncidence (n + 1) d →
        (∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ)) :=
  isSmoothEmbedding_subtypeVal_linearSliceChartedSpace_of_boundaryless
    (ComplexProjectiveIncidence.sliceChartAt n d)
    (ComplexProjectiveIncidence.isSliceChart_sliceChartAt n d)
    (fun _ ↦ modelEquiv 𝕜 d)
    (fun z ↦ contMDiffOn_complexProjectiveIncidenceSliceChart (𝕜 := 𝕜) z.1.1
      (exists_mem_affineOpen z.1.2).choose_spec r)
    (fun z ↦ contMDiffOn_complexProjectiveIncidenceSliceChart_symm (𝕜 := 𝕜) z.1.1
      (exists_mem_affineOpen z.1.2).choose_spec r)
    (ComplexProjectiveIncidence.mem_sliceChartAt_source n d)

/-- The projection of the universal projective incidence variety to the homogeneous polynomial
family space is `C^r` (holomorphic for `𝕜 = ℂ, r = ω` and real smooth for `𝕜 = ℝ`). -/
theorem contMDiff_fst_complexProjectiveIncidence :
    ContMDiff
      𝓘(𝕜, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ)
      (homogeneousFamilyModel (Fin (n + 1)) 𝕜 ℂ d) r
      (fun x : complexProjectiveIncidence (n + 1) d ↦ x.1.1) :=
  contMDiff_fst.comp (isSmoothEmbedding_subtypeVal_complexProjectiveIncidence 𝕜 d r).contMDiff

/-- The projection of the universal projective incidence variety to projective space is `C^r`. -/
theorem contMDiff_snd_complexProjectiveIncidence :
    ContMDiff
      𝓘(𝕜, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ)
      𝓘(𝕜, Fin n → ℂ) r
      (fun x : complexProjectiveIncidence (n + 1) d ↦ x.1.2) :=
  contMDiff_snd.comp (isSmoothEmbedding_subtypeVal_complexProjectiveIncidence 𝕜 d r).contMDiff

end Embedding

end ManifoldAndEmbedding

/-! ### Tangent space, normal space, and the Jacobian submersion criterion -/

section TangentAndSubmersion

private theorem eventually_chartEquations_eq_zero {ι : Type*} {n : ℕ} {d : ι → ℕ}
    {i : Fin (n + 1)} (z : complexProjectiveIncidence (n + 1) d) (hi : z.1.2 ∈ affineOpen i) :
    ∀ᶠ y : complexProjectiveIncidence (n + 1) d in 𝓝 z,
      projectiveIncidenceChartEquations i (affineChart i y.1.2) y.1.1 = 0 := by
  filter_upwards [(continuous_subtype_val.snd.continuousAt).preimage_mem_nhds
    ((isOpen_affineOpen i).mem_nhds hi)] with y hy
  exact (mem_complexProjectiveIncidence_iff_projectiveIncidenceChartEquations_eq_zero y.1.1 hy).1
    y.2

variable {ι : Type*} [Fintype ι] {n : ℕ} {d : ι → ℕ}

/-- The inclusion of `TauCeti.complexProjectiveIncidence (n + 1) d` into the ambient product as a
bundled `TauCeti.SmoothEmbedding` over `ℂ`. -/
noncomputable def complexProjectiveIncidenceEmbedding (d : ι → ℕ) (r : ℕ∞ω) :
    SmoothEmbedding
      𝓘(ℂ, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ)
      ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ)) r
      (complexProjectiveIncidence (n + 1) d)
      ((∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ)) where
  toContMDiffMap :=
    ⟨Subtype.val, (isSmoothEmbedding_subtypeVal_complexProjectiveIncidence ℂ d r).contMDiff⟩
  isSmoothEmbedding_toFun := isSmoothEmbedding_subtypeVal_complexProjectiveIncidence ℂ d r

@[simp]
theorem coe_complexProjectiveIncidenceEmbedding (d : ι → ℕ) (r : ℕ∞ω) :
    ⇑(complexProjectiveIncidenceEmbedding (n := n) d r) = Subtype.val :=
  (rfl)

private theorem bijective_mfderiv_ambChart {i : Fin (n + 1)} {p : Amb n d}
    (hi : p.2 ∈ affineOpen i) :
    Bijective (mfderiv ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ))
      𝓘(ℂ, (Fin n → ℂ) × CoeffSpace n d) (ambChart d i) p) := by
  let IA := (homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ)
  let Φ : PartialDiffeomorph IA 𝓘(ℂ, (Fin n → ℂ) × CoeffSpace n d) (Amb n d)
      ((Fin n → ℂ) × CoeffSpace n d) 1 :=
    { toPartialEquiv := (ambChart d i).toPartialEquiv
      open_source := (ambChart d i).open_source
      open_target := (ambChart d i).open_target
      contMDiffOn_toFun := contMDiffOn_ambChart (𝕜 := ℂ) d i 1
      contMDiffOn_invFun := (contMDiff_ambChart_symm (𝕜 := ℂ) d i 1).contMDiffOn }
  have hp : p ∈ Φ.source := by simpa [Φ, ambChart_source] using hi
  exact ((isLocalDiffeomorphAt_of_eqOn (Φ := Φ) hp (eqOn_refl _ _)).isInvertible_mfderiv
    one_ne_zero).bijective

private theorem mfderiv_chartEquations_eq {i : Fin (n + 1)} {p : Amb n d}
    (hi : p.2 ∈ affineOpen i) :
    mfderiv ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ)) 𝓘(ℂ, ι → ℂ)
      (fun w : Amb n d ↦ projectiveIncidenceChartEquations i (affineChart i w.2) w.1) p =
      (fderiv ℂ (chartEqns d i) (ambChart d i p)).comp
        (mfderiv ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ))
          𝓘(ℂ, (Fin n → ℂ) × CoeffSpace n d) (ambChart d i) p) := by
  let IA := (homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ)
  have hp : p ∈ (ambChart d i).source := by
    rw [ambChart_source]
    exact ⟨trivial, hi⟩
  have hamb : MDifferentiableAt IA 𝓘(ℂ, (Fin n → ℂ) × CoeffSpace n d) (ambChart d i) p :=
    ((contMDiffOn_ambChart (𝕜 := ℂ) d i 1).contMDiffAt
      ((ambChart d i).open_source.mem_nhds hp)).mdifferentiableAt one_ne_zero
  have heqns := (hasStrictFDerivAt_chartEqns d i (ambChart d i p)).hasFDerivAt.hasMFDerivAt
  have hfun : (fun w : Amb n d ↦ projectiveIncidenceChartEquations i (affineChart i w.2) w.1) =
      chartEqns d i ∘ ambChart d i := by
    funext w
    simp [chartEqns, coeffParam, ambChart_apply]
  rw [hfun, (heqns.comp p hamb.hasMFDerivAt).mfderiv]
  rfl

private theorem isRegularPoint_chartEquations {i : Fin (n + 1)}
    (z : complexProjectiveIncidence (n + 1) d) (hi : z.1.2 ∈ affineOpen i) :
    IsRegularPoint ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ))
      𝓘(ℂ, ι → ℂ)
      (fun w : Amb n d ↦ projectiveIncidenceChartEquations i (affineChart i w.2) w.1) z.1 := by
  rw [isRegularPoint_iff, mfderiv_chartEquations_eq hi]
  exact (surjective_fderiv_chartEqns d i _).comp (bijective_mfderiv_ambChart hi).surjective

private theorem finrank_add_finrank_eq_amb (d : ι → ℕ) :
    Module.finrank ℂ (Fin (Module.finrank ℂ (CoeffSpace n d) + n - Fintype.card ι) → ℂ) +
      Module.finrank ℂ (ι → ℂ) =
      Module.finrank ℂ (CoeffSpace n d × (Fin n → ℂ)) := by
  have := card_le_finrank_add (n := n) d
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun,
    Module.finrank_fintype_fun_eq_card]
  omega

/-- **The tangent space of the universal projective incidence variety.** At an incidence point `z`
with `z.1.2 ∈ affineOpen i`, the tangent range of the inclusion into the ambient product is the
kernel of the differential of `TauCeti.projectiveIncidenceChartEquations`. -/
theorem tangentRange_complexProjectiveIncidenceEmbedding {r : ℕ∞ω} (hr : r ≠ 0)
    (z : complexProjectiveIncidence (n + 1) d) {i : Fin (n + 1)} (hi : z.1.2 ∈ affineOpen i) :
    (complexProjectiveIncidenceEmbedding d r).tangentRange z hr =
      (mfderiv ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ)) 𝓘(ℂ, ι → ℂ)
        (fun w : (∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ) ↦
          projectiveIncidenceChartEquations i (affineChart i w.2) w.1) z.1).ker :=
  SmoothEmbedding.tangentRange_eq_ker_mfderiv _ z hr
    (eventually_chartEquations_eq_zero z hi)
    (isRegularPoint_chartEquations z hi)
    (finrank_add_finrank_eq_amb d)

/-- **Exactness of the tangent sequence of the universal projective incidence variety.** -/
theorem exact_mfderiv_subtypeVal_complexProjectiveIncidence
    (z : complexProjectiveIncidence (n + 1) d) {i : Fin (n + 1)} (hi : z.1.2 ∈ affineOpen i) :
    Exact
      (mfderiv
        𝓘(ℂ, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
          Fintype.card ι) → ℂ)
        ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ))
        Subtype.val z)
      (mfderiv ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ)) 𝓘(ℂ, ι → ℂ)
        (fun w : (∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ) ↦
          projectiveIncidenceChartEquations i (affineChart i w.2) w.1) z.1) :=
  LinearMap.exact_iff.2 (tangentRange_complexProjectiveIncidenceEmbedding (r := 1) one_ne_zero z
    hi).symm

/-- **The normal space of the universal projective incidence variety.** At an incidence point `z`
with `z.1.2 ∈ affineOpen i`, the differential of the ratio-chart incidence equations identifies the
normal space of `complexProjectiveIncidence (n + 1) d` with `ι → ℂ`. -/
noncomputable def complexProjectiveIncidenceNormalSpaceEquiv {r : ℕ∞ω} (hr : r ≠ 0)
    (z : complexProjectiveIncidence (n + 1) d) {i : Fin (n + 1)} (hi : z.1.2 ∈ affineOpen i) :
    (complexProjectiveIncidenceEmbedding d r).NormalSpace z hr ≃L[ℂ] (ι → ℂ) :=
  SmoothEmbedding.normalSpaceEquivOfLevel _ z hr
    (eventually_chartEquations_eq_zero z hi)
    (isRegularPoint_chartEquations z hi)
    (finrank_add_finrank_eq_amb d)

@[simp]
theorem complexProjectiveIncidenceNormalSpaceEquiv_normalClass {r : ℕ∞ω} (hr : r ≠ 0)
    (z : complexProjectiveIncidence (n + 1) d) {i : Fin (n + 1)} (hi : z.1.2 ∈ affineOpen i)
    (v : TangentSpace ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ)) z.1) :
    complexProjectiveIncidenceNormalSpaceEquiv hr z hi
        ((complexProjectiveIncidenceEmbedding d r).normalClass z hr v) =
      mfderiv ((homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d).prod 𝓘(ℂ, Fin n → ℂ)) 𝓘(ℂ, ι → ℂ)
        (fun w : (∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)) × ℙ ℂ (Fin (n + 1) → ℂ) ↦
          projectiveIncidenceChartEquations i (affineChart i w.2) w.1) z.1 v :=
  SmoothEmbedding.normalSpaceEquivOfLevel_normalClass _ _ _ _ _ _ v

private theorem surjective_mfderiv_fst_iff_parameterProj
    (x : complexProjectiveIncidence (n + 1) d) {i : Fin (n + 1)} (hi : x.1.2 ∈ affineOpen i) :
    Surjective
      (mfderiv
        𝓘(ℂ, Fin (Module.finrank ℂ (CoeffSpace n d) + n - Fintype.card ι) → ℂ)
        (homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d)
        (fun y : complexProjectiveIncidence (n + 1) d ↦ y.1.1) x) ↔
      Surjective
        ((fderiv ℂ (fun a ↦ projectiveIncidenceChartEquations i a x.1.1)
          (affineChart i x.1.2)).parameterProj
          ((projectiveIncidenceChartEquations (d := d) i (affineChart i x.1.2)).comp
            (coeffParam d))) := by
  let IM := 𝓘(ℂ, Fin (Module.finrank ℂ (CoeffSpace n d) + n - Fintype.card ι) → ℂ)
  let IC := homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d
  let IA := IC.prod 𝓘(ℂ, Fin n → ℂ)
  let EC := homogeneousFamilyCoeffDiffeomorph (σ := Fin (n + 1)) (𝕜' := ℂ) ℂ d 1
  have hEC_bij := (EC.isInvertible_mfderiv one_ne_zero (x := x.1.1)).bijective
  have hfst_diff : MDifferentiableAt IM IC
      (fun y : complexProjectiveIncidence (n + 1) d ↦ y.1.1) x :=
    (contMDiff_fst_complexProjectiveIncidence ℂ d 1 x).mdifferentiableAt one_ne_zero
  have hcomp_iff :
      Surjective (mfderiv IM IC (fun y : complexProjectiveIncidence (n + 1) d ↦ y.1.1) x) ↔
        Surjective (mfderiv IM 𝓘(ℂ, CoeffSpace n d)
          (EC ∘ fun y : complexProjectiveIncidence (n + 1) d ↦ y.1.1) x) := by
    rw [mfderiv_comp x (EC.contMDiff.mdifferentiableAt one_ne_zero) hfst_diff,
      ContinuousLinearMap.coe_comp]
    exact ⟨hEC_bij.surjective.comp, fun h y ↦ by
      obtain ⟨u, hu⟩ := h (mfderiv _ _ EC x.1.1 y)
      exact ⟨u, hEC_bij.injective hu⟩⟩
  rw [hcomp_iff]
  have hsub_diff : MDifferentiableAt IM IA Subtype.val x :=
    ((isSmoothEmbedding_subtypeVal_complexProjectiveIncidence ℂ d 1).contMDiff x).mdifferentiableAt
      one_ne_zero
  have hamb_diff : MDifferentiableAt IA 𝓘(ℂ, (Fin n → ℂ) × CoeffSpace n d) (ambChart d i) x.1 :=
    ((contMDiffOn_ambChart (𝕜 := ℂ) d i 1).contMDiffAt
      ((ambChart d i).open_source.mem_nhds (by rw [ambChart_source]; exact ⟨trivial, hi⟩))
      ).mdifferentiableAt one_ne_zero
  have hfactor : EC ∘ (fun y : complexProjectiveIncidence (n + 1) d ↦ y.1.1) =
      (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (CoeffSpace n d)) ∘ ambChart d i ∘ Subtype.val := by
    funext y
    simp [EC, ambChart_apply]
  rw [hfactor, mfderiv_comp x (ContinuousLinearMap.snd ℂ _ _).mdifferentiableAt
    (hamb_diff.comp x hsub_diff), mfderiv_comp x hamb_diff hsub_diff]
  have hsnd (w : (Fin n → ℂ) × CoeffSpace n d) :
      mfderiv 𝓘(ℂ, (Fin n → ℂ) × CoeffSpace n d) 𝓘(ℂ, CoeffSpace n d)
        (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (CoeffSpace n d))
        ((ambChart d i ∘ Subtype.val) x) w = w.2 :=
    congrFun (congrArg DFunLike.coe
      ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) (CoeffSpace n d)).hasFDerivAt
        (x := (ambChart d i ∘ Subtype.val) x)).hasMFDerivAt.mfderiv) w
  have hexact := LinearMap.exact_iff.1 (exact_mfderiv_subtypeVal_complexProjectiveIncidence x hi)
  have hker_iff (q : (Fin n → ℂ) × CoeffSpace n d) :
      (∃ u, mfderiv IA 𝓘(ℂ, (Fin n → ℂ) × CoeffSpace n d) (ambChart d i) x.1
        (mfderiv IM IA Subtype.val x u) = q) ↔
        q ∈ (fderiv ℂ (chartEqns d i) (ambChart d i x.1)).ker := by
    obtain ⟨v, hv⟩ := (bijective_mfderiv_ambChart hi).surjective q
    have h1 : (∃ u, mfderiv IA 𝓘(ℂ, (Fin n → ℂ) × CoeffSpace n d) (ambChart d i) x.1
        (mfderiv IM IA Subtype.val x u) = q) ↔
        v ∈ LinearMap.range (mfderiv IM IA Subtype.val x).toLinearMap := by
      rw [← hv]
      exact exists_congr fun u ↦ (bijective_mfderiv_ambChart hi).injective.eq_iff
    rw [h1, ← hexact, LinearMap.mem_ker, LinearMap.mem_ker]
    have h2 : mfderiv IA 𝓘(ℂ, ι → ℂ)
        (fun w : Amb n d ↦ projectiveIncidenceChartEquations i (affineChart i w.2) w.1) x.1 v =
        fderiv ℂ (chartEqns d i) (ambChart d i x.1) q :=
      (congrFun (congrArg DFunLike.coe (mfderiv_chartEquations_eq hi)) v).trans
        (congrArg (fderiv ℂ (chartEqns d i) (ambChart d i x.1)) hv)
    exact h2 ▸ Iff.rfl
  have hfderiv := fderiv_chartEqns_ambChart d i x.1
  constructor
  · intro hsurj b
    obtain ⟨u, hu⟩ := hsurj b
    refine ⟨⟨mfderiv IA _ (ambChart d i) x.1 (mfderiv IM IA Subtype.val x u),
      hfderiv ▸ (hker_iff _).1 ⟨u, rfl⟩⟩, ?_⟩
    exact (ContinuousLinearMap.parameterProj_apply _ _ _).trans ((hsnd _).symm.trans hu)
  · intro hsurj b
    obtain ⟨⟨q, hq⟩, hqb⟩ := hsurj b
    obtain ⟨u, hu⟩ := (hker_iff q).2 (hfderiv.symm ▸ hq)
    refine ⟨u, ?_⟩
    exact (hsnd _).trans ((congrArg Prod.snd hu).trans
      ((ContinuousLinearMap.parameterProj_apply _ _ ⟨q, hq⟩).symm.trans hqb))

/-- **The Jacobian submersion criterion for the universal projective incidence variety.** For
`1 ≤ r` (including the holomorphic case `r = ω`), the projection
`TauCeti.complexProjectiveIncidence (n + 1) d → ∀ k, homogeneousSubmodule (Fin (n + 1)) ℂ (d k)` is
a `C^r` complex submersion at `x` if and only if the cone Jacobian of the equations `x.1.1` at
`x.1.2.rep` is surjective. -/
theorem isSubmersionAt_fst_complexProjectiveIncidence_iff {r : ℕ∞ω} (hr : 1 ≤ r)
    (x : complexProjectiveIncidence (n + 1) d) :
    Manifold.IsSubmersionAt
      𝓘(ℂ, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ)
      (homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d) r
      (fun y : complexProjectiveIncidence (n + 1) d ↦ y.1.1) x ↔
      Surjective
        (jacobiMatrixAt (fun k ↦ (x.1.1 k : MvPolynomial (Fin (n + 1)) ℂ)) x.1.2.rep).mulVec := by
  have hfst : MDifferentiableOn
      𝓘(ℂ, Fin (Module.finrank ℂ (∀ k, {s : Fin (n + 1) →₀ ℕ // s.degree = d k} → ℂ) + n -
        Fintype.card ι) → ℂ)
      (homogeneousFamilyModel (Fin (n + 1)) ℂ ℂ d)
      (fun y : complexProjectiveIncidence (n + 1) d ↦ y.1.1) univ :=
    ((contMDiff_fst_complexProjectiveIncidence ℂ d 1).mdifferentiable
      one_ne_zero).mdifferentiableOn
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x.1.2
  rw [isSubmersionAt_iff_surjective_mfderiv_of_mdifferentiableOn hfst isOpen_univ (mem_univ x) hr,
    surjective_mfderiv_fst_iff_parameterProj x hi]
  have htotal :=
    fderiv_chartEqns_ambChart d i x.1 ▸ surjective_fderiv_chartEqns d i (ambChart d i x.1)
  rw [ContinuousLinearMap.parameterProj_surjective_iff _ _ htotal]
  simpa only [projectiveIncidenceChartEquations_apply] using
    surjective_fderiv_eval_dehomogenize_affineChart_iff i
      (fun k ↦ (mem_homogeneousSubmodule _ _).mp (x.1.1 k).2)
      (mem_complexProjectiveIncidence.mp x.2) hi

end TangentAndSubmersion

end TauCeti
