/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import TauCeti.Geometry.Manifold.IsManifold.Pi
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.Algebra.MvPolynomial.HomogeneousSubmodule

/-!
# The coefficient space of homogeneous polynomials as an analytic manifold

For finitely many variables `σ`, the space `homogeneousSubmodule σ R n` of homogeneous polynomials
of degree `n` carries the module topology, identified by `TauCeti.homogeneousCoeffEquiv n` with the
function space `{s : σ →₀ ℕ // s.degree = n} → R` of monomial coefficients. Pulling back the
self-charted structure of that function space along `homogeneousCoeffEquiv n`
(`Homeomorph.pullbackChartedSpace`) equips `homogeneousSubmodule σ R n` with a single global chart
without choosing a norm on the polynomial submodule.

Over a nontrivially normed field `𝕜` (with `[Fintype σ] [DecidableEq σ]`), this makes
`homogeneousSubmodule σ 𝕜 n` a `C^r` manifold at every order of smoothness `r`, including the
analytic order `ω`, and turns `homogeneousCoeffEquiv n` into a `C^r` diffeomorphism
(`TauCeti.homogeneousCoeffDiffeomorph`). When `𝕜` is a normed algebra over `ℝ` (such as `ℂ`), the
same global chart makes `homogeneousSubmodule σ 𝕜 n` a real `C^r` manifold as well. Finite families
`∀ k, homogeneousSubmodule σ 𝕜 (d k)` of homogeneous equations then inherit the product manifold
structure `TauCeti.homogeneousFamilyModel`, and a map into such a family is `C^r` precisely when
each of its monomial coefficients is `C^r` (`TauCeti.contMDiff_homogeneousFamily_iff`).

## Main declarations

* `TauCeti.instChartedSpaceHomogeneousSubmodule`: the global monomial-coefficient chart on
  `homogeneousSubmodule σ R n`.
* `TauCeti.instIsManifoldHomogeneousSubmodule`, `TauCeti.instIsManifoldHomogeneousSubmoduleReal`:
  `homogeneousSubmodule σ 𝕜 n` is a `C^r` manifold over `𝕜` and, for `[NormedAlgebra ℝ 𝕜]`, over
  `ℝ`.
* `TauCeti.homogeneousCoeffDiffeomorph`: `homogeneousCoeffEquiv n` as a `C^r` diffeomorphism.
* `TauCeti.homogeneousFamilyCoeffEquiv`: the product monomial-coefficient continuous linear
  equivalence on `∀ k, homogeneousSubmodule σ R (d k)`.
* `TauCeti.homogeneousFamilyModel`: the product `ModelWithCorners` on a finite family of
  homogeneous polynomial spaces.
* `TauCeti.homogeneousFamilyCoeffDiffeomorph`: `homogeneousFamilyCoeffEquiv d` as a `C^r`
  diffeomorphism.
* `TauCeti.contMDiff_homogeneousSubmodule_iff` and `TauCeti.contMDiff_homogeneousFamily_iff`:
  smoothness of maps into homogeneous polynomial spaces in terms of their monomial coefficients.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Lecture 1, for parameter spaces of homogeneous
  polynomials in monomial coordinates.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Chapter I, §1, for
  atlases pulled back along a homeomorphism.
-/

public section

open MvPolynomial Set
open scoped ContDiff Manifold

namespace TauCeti

section ChartedSpace

variable {σ R : Type*} [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [Finite σ]

/-- The homogeneous polynomials of degree `n` in finitely many variables form a charted space
modelled on their monomial-coefficient space `{s : σ →₀ ℕ // s.degree = n} → R`, by pulling back the
identity chart along `TauCeti.homogeneousCoeffEquiv n`. -/
noncomputable instance instChartedSpaceHomogeneousSubmodule (n : ℕ) :
    ChartedSpace ({s : σ →₀ ℕ // s.degree = n} → R) (homogeneousSubmodule σ R n) :=
  (homogeneousCoeffEquiv n).toHomeomorph.pullbackChartedSpace

/-- In the global monomial-coefficient chart, `chartAt` at any base point evaluates
`TauCeti.homogeneousCoeffEquiv n`. -/
@[mfld_simps]
theorem chartAt_homogeneousSubmodule_apply {n : ℕ} (p q : homogeneousSubmodule σ R n) :
    chartAt ({s : σ →₀ ℕ // s.degree = n} → R) p q = homogeneousCoeffEquiv n q := by
  simp

/-- The inverse of `chartAt` on `homogeneousSubmodule σ R n` is the inverse monomial-coefficient
equivalence. -/
@[mfld_simps]
theorem chartAt_homogeneousSubmodule_symm_apply {n : ℕ} (p : homogeneousSubmodule σ R n)
    (a : {s : σ →₀ ℕ // s.degree = n} → R) :
    (chartAt ({s : σ →₀ ℕ // s.degree = n} → R) p).symm a = (homogeneousCoeffEquiv n).symm a := by
  simp

/-- Every global monomial-coefficient chart is defined on the whole submodule. -/
@[mfld_simps]
theorem chartAt_homogeneousSubmodule_source {n : ℕ} (p : homogeneousSubmodule σ R n) :
    (chartAt ({s : σ →₀ ℕ // s.degree = n} → R) p).source = univ := by
  simp

/-- Every global monomial-coefficient chart has the whole coefficient space as target. -/
@[mfld_simps]
theorem chartAt_homogeneousSubmodule_target {n : ℕ} (p : homogeneousSubmodule σ R n) :
    (chartAt ({s : σ →₀ ℕ // s.degree = n} → R) p).target = univ := by
  simp

/-- The continuous linear equivalence identifying a family of homogeneous polynomials of degrees `d`
with its family of monomial-coefficient functions. -/
noncomputable def homogeneousFamilyCoeffEquiv {ι : Type*} (d : ι → ℕ) :
    (∀ k, homogeneousSubmodule σ R (d k)) ≃L[R]
      ∀ k, {s : σ →₀ ℕ // s.degree = d k} → R :=
  ContinuousLinearEquiv.piCongrRight fun k ↦ homogeneousCoeffEquiv (d k)

@[simp]
theorem homogeneousFamilyCoeffEquiv_apply {ι : Type*} {d : ι → ℕ}
    (c : ∀ k, homogeneousSubmodule σ R (d k)) (k : ι)
    (s : {s : σ →₀ ℕ // s.degree = d k}) :
    homogeneousFamilyCoeffEquiv d c k s = (c k : MvPolynomial σ R).coeff s := by
  simp [homogeneousFamilyCoeffEquiv]

@[simp]
theorem homogeneousFamilyCoeffEquiv_symm_apply {ι : Type*} {d : ι → ℕ}
    (a : ∀ k, {s : σ →₀ ℕ // s.degree = d k} → R) (k : ι) :
    (homogeneousFamilyCoeffEquiv d).symm a k = (homogeneousCoeffEquiv (d k)).symm (a k) := by
  simp [homogeneousFamilyCoeffEquiv]

end ChartedSpace

section Manifold

variable {σ 𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedSpace 𝕜 𝕜'] [Fintype σ] [DecidableEq σ]

/-- Over a nontrivially normed field `𝕜`, the degree-`n` homogeneous polynomials form a `C^r`
manifold at every smoothness order `r`, including `ω`. -/
instance instIsManifoldHomogeneousSubmodule (n : ℕ) (r : ℕ∞ω) :
    IsManifold 𝓘(𝕜, {s : σ →₀ ℕ // s.degree = n} → 𝕜) r (homogeneousSubmodule σ 𝕜 n) :=
  (homogeneousCoeffEquiv n).toHomeomorph.pullback_isManifold _ r

/-- Over a normed `ℝ`-algebra `𝕜` (such as `ℂ`), the degree-`n` homogeneous polynomials also form
a real `C^r` manifold with the same monomial-coefficient chart. -/
instance instIsManifoldHomogeneousSubmoduleReal [NormedAlgebra ℝ 𝕜] (n : ℕ) (r : ℕ∞ω) :
    IsManifold 𝓘(ℝ, {s : σ →₀ ℕ // s.degree = n} → 𝕜) r (homogeneousSubmodule σ 𝕜 n) :=
  (instIsManifoldHomogeneousSubmodule n r).restrictScalars ℝ

@[mfld_simps]
theorem extChartAt_homogeneousSubmodule_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 𝕜'] {n : ℕ} (p q : homogeneousSubmodule σ 𝕜' n) :
    extChartAt 𝓘(𝕜, {s : σ →₀ ℕ // s.degree = n} → 𝕜') p q = homogeneousCoeffEquiv n q := by
  simp [extChartAt]

@[mfld_simps]
theorem extChartAt_homogeneousSubmodule_symm_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 𝕜'] {n : ℕ} (p : homogeneousSubmodule σ 𝕜' n)
    (a : {s : σ →₀ ℕ // s.degree = n} → 𝕜') :
    (extChartAt 𝓘(𝕜, {s : σ →₀ ℕ // s.degree = n} → 𝕜') p).symm a =
      (homogeneousCoeffEquiv n).symm a := by
  simp [extChartAt]

/-- The monomial-coefficient equivalence `TauCeti.homogeneousCoeffEquiv n`, upgraded to a `C^r`
diffeomorphism over any normed base field `𝕜` acting on `𝕜'`. Taking `𝕜 = 𝕜'` gives the native
analytic diffeomorphism; taking `𝕜 = ℝ` and `𝕜' = ℂ` gives the underlying real smooth
diffeomorphism. -/
noncomputable def homogeneousCoeffDiffeomorph (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 𝕜'] (n : ℕ) (r : ℕ∞ω) :
    homogeneousSubmodule σ 𝕜' n ≃ₘ^r⟮𝓘(𝕜, {s : σ →₀ ℕ // s.degree = n} → 𝕜'),
      𝓘(𝕜, {s : σ →₀ ℕ // s.degree = n} → 𝕜')⟯ ({s : σ →₀ ℕ // s.degree = n} → 𝕜') :=
  (homogeneousCoeffEquiv n).toHomeomorph.pullbackDiffeomorph _ r

@[simp]
theorem coe_homogeneousCoeffDiffeomorph (n : ℕ) (r : ℕ∞ω) :
    ⇑(homogeneousCoeffDiffeomorph (σ := σ) (𝕜' := 𝕜') 𝕜 n r) = homogeneousCoeffEquiv n := by
  simp [homogeneousCoeffDiffeomorph]

@[simp]
theorem coe_homogeneousCoeffDiffeomorph_symm (n : ℕ) (r : ℕ∞ω) :
    ⇑(homogeneousCoeffDiffeomorph (σ := σ) (𝕜' := 𝕜') 𝕜 n r).symm =
      (homogeneousCoeffEquiv n).symm := by
  simp [homogeneousCoeffDiffeomorph]

@[simp]
theorem homogeneousCoeffDiffeomorph_toHomeomorph (n : ℕ) (r : ℕ∞ω) :
    (homogeneousCoeffDiffeomorph (σ := σ) (𝕜' := 𝕜') 𝕜 n r).toHomeomorph =
      (homogeneousCoeffEquiv n).toHomeomorph := by
  simp [homogeneousCoeffDiffeomorph]

section Smoothness

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ} {r : ℕ∞ω} {f : M → homogeneousSubmodule σ 𝕜' n} {t : Set M} {x : M}

/-- A map into `homogeneousSubmodule σ 𝕜' n` is `C^r` within a set at a point if and only if each
of its monomial coefficients is `C^r` within that set at that point. -/
theorem contMDiffWithinAt_homogeneousSubmodule_iff :
    ContMDiffWithinAt I 𝓘(𝕜, {s : σ →₀ ℕ // s.degree = n} → 𝕜') r f t x ↔
      ∀ s : {s : σ →₀ ℕ // s.degree = n},
        ContMDiffWithinAt I 𝓘(𝕜, 𝕜') r (fun m ↦ (f m : MvPolynomial σ 𝕜').coeff s) t x := by
  rw [← (homogeneousCoeffDiffeomorph 𝕜 n r).contMDiffWithinAt_diffeomorph_comp_iff le_rfl,
    contMDiffWithinAt_pi_module_iff]
  simp only [Function.comp_def, coe_homogeneousCoeffDiffeomorph, homogeneousCoeffEquiv_apply]

/-- A map into `homogeneousSubmodule σ 𝕜' n` is `C^r` at a point if and only if each of its
monomial coefficients is `C^r` there. -/
theorem contMDiffAt_homogeneousSubmodule_iff :
    ContMDiffAt I 𝓘(𝕜, {s : σ →₀ ℕ // s.degree = n} → 𝕜') r f x ↔
      ∀ s : {s : σ →₀ ℕ // s.degree = n},
        ContMDiffAt I 𝓘(𝕜, 𝕜') r (fun m ↦ (f m : MvPolynomial σ 𝕜').coeff s) x :=
  contMDiffWithinAt_homogeneousSubmodule_iff

/-- A map into `homogeneousSubmodule σ 𝕜' n` is `C^r` on a set if and only if each of its monomial
coefficients is `C^r` on that set. -/
theorem contMDiffOn_homogeneousSubmodule_iff :
    ContMDiffOn I 𝓘(𝕜, {s : σ →₀ ℕ // s.degree = n} → 𝕜') r f t ↔
      ∀ s : {s : σ →₀ ℕ // s.degree = n},
        ContMDiffOn I 𝓘(𝕜, 𝕜') r (fun m ↦ (f m : MvPolynomial σ 𝕜').coeff s) t := by
  simp only [ContMDiffOn, contMDiffWithinAt_homogeneousSubmodule_iff]
  exact ⟨fun h s y hy ↦ h y hy s, fun h y hy s ↦ h s y hy⟩

/-- A map into `homogeneousSubmodule σ 𝕜' n` is `C^r` if and only if each of its monomial
coefficients is `C^r`. -/
theorem contMDiff_homogeneousSubmodule_iff :
    ContMDiff I 𝓘(𝕜, {s : σ →₀ ℕ // s.degree = n} → 𝕜') r f ↔
      ∀ s : {s : σ →₀ ℕ // s.degree = n},
        ContMDiff I 𝓘(𝕜, 𝕜') r fun m ↦ (f m : MvPolynomial σ 𝕜').coeff s := by
  simp only [ContMDiff, contMDiffAt_homogeneousSubmodule_iff]
  exact forall_comm

end Smoothness

section Family

variable {ι : Type*} [Fintype ι]

/-- The product `ModelWithCorners` on a finite family `∀ k, homogeneousSubmodule σ R (d k)` of
homogeneous polynomial spaces over `R`, regarded over a normed scalar field `𝕜`. For `R = 𝕜` this
is the native `𝕜`-analytic model; for `𝕜 = ℝ` and `R = ℂ` it is the underlying real smooth
model. -/
noncomputable abbrev homogeneousFamilyModel (σ 𝕜 R : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup R] [NormedSpace 𝕜 R] [Fintype σ] [DecidableEq σ]
    {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    ModelWithCorners 𝕜 (∀ k, {s : σ →₀ ℕ // s.degree = d k} → R)
      (ModelPi fun k ↦ {s : σ →₀ ℕ // s.degree = d k} → R) :=
  ModelWithCorners.pi fun k ↦ 𝓘(𝕜, {s : σ →₀ ℕ // s.degree = d k} → R)

/-- The product monomial-coefficient equivalence `TauCeti.homogeneousFamilyCoeffEquiv d`, upgraded
to a `C^r` diffeomorphism between `∀ k, homogeneousSubmodule σ 𝕜' (d k)` (with
`TauCeti.homogeneousFamilyModel`) and `∀ k, {s : σ →₀ ℕ // s.degree = d k} → 𝕜'`. -/
noncomputable def homogeneousFamilyCoeffDiffeomorph (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 𝕜'] (d : ι → ℕ) (r : ℕ∞ω) :
    Diffeomorph (homogeneousFamilyModel σ 𝕜 𝕜' d)
      𝓘(𝕜, ∀ k, {s : σ →₀ ℕ // s.degree = d k} → 𝕜')
      (∀ k, homogeneousSubmodule σ 𝕜' (d k))
      (∀ k, {s : σ →₀ ℕ // s.degree = d k} → 𝕜') r where
  toEquiv := (homogeneousFamilyCoeffEquiv d).toEquiv
  contMDiff_toFun := contMDiff_pi_module_iff.2 fun k ↦ by
    simpa [homogeneousFamilyCoeffEquiv, Function.comp_def] using
      (homogeneousCoeffDiffeomorph 𝕜 (d k) r).contMDiff.comp contMDiff_apply
  contMDiff_invFun := contMDiff_pi_iff.2 fun k ↦ by
    simpa [Function.comp_def] using
      (homogeneousCoeffDiffeomorph 𝕜 (d k) r).symm.contMDiff.comp
        (ContinuousLinearMap.proj (R := 𝕜)
          (φ := fun k ↦ {s : σ →₀ ℕ // s.degree = d k} → 𝕜') k).contDiff.contMDiff

@[simp]
theorem coe_homogeneousFamilyCoeffDiffeomorph (d : ι → ℕ) (r : ℕ∞ω) :
    ⇑(homogeneousFamilyCoeffDiffeomorph (σ := σ) (𝕜' := 𝕜') 𝕜 d r) =
      homogeneousFamilyCoeffEquiv d := by
  funext c
  rfl

@[simp]
theorem coe_homogeneousFamilyCoeffDiffeomorph_symm (d : ι → ℕ) (r : ℕ∞ω) :
    ⇑(homogeneousFamilyCoeffDiffeomorph (σ := σ) (𝕜' := 𝕜') 𝕜 d r).symm =
      (homogeneousFamilyCoeffEquiv d).symm := by
  funext a
  rfl

@[simp]
theorem homogeneousFamilyCoeffDiffeomorph_toHomeomorph (d : ι → ℕ) (r : ℕ∞ω) :
    (homogeneousFamilyCoeffDiffeomorph (σ := σ) (𝕜' := 𝕜') 𝕜 d r).toHomeomorph =
      (homogeneousFamilyCoeffEquiv d).toHomeomorph := by
  ext1 c
  rfl

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {d : ι → ℕ} {r : ℕ∞ω} {c : M → ∀ k, homogeneousSubmodule σ 𝕜' (d k)} {t : Set M} {x : M}

/-- A family of homogeneous polynomials parametrized by `M` is `C^r` within a set at a point if
and only if all of its monomial coefficients are `C^r` within that set at that point. -/
theorem contMDiffWithinAt_homogeneousFamily_iff :
    ContMDiffWithinAt I (homogeneousFamilyModel σ 𝕜 𝕜' d) r c t x ↔
      ∀ (k : ι) (s : {s : σ →₀ ℕ // s.degree = d k}),
        ContMDiffWithinAt I 𝓘(𝕜, 𝕜') r (fun m ↦ (c m k : MvPolynomial σ 𝕜').coeff s) t x := by
  rw [contMDiffWithinAt_pi_iff]
  exact forall_congr' fun _ ↦ contMDiffWithinAt_homogeneousSubmodule_iff

/-- A family of homogeneous polynomials parametrized by `M` is `C^r` at a point if and only if all
of its monomial coefficients are `C^r` there. -/
theorem contMDiffAt_homogeneousFamily_iff :
    ContMDiffAt I (homogeneousFamilyModel σ 𝕜 𝕜' d) r c x ↔
      ∀ (k : ι) (s : {s : σ →₀ ℕ // s.degree = d k}),
        ContMDiffAt I 𝓘(𝕜, 𝕜') r (fun m ↦ (c m k : MvPolynomial σ 𝕜').coeff s) x :=
  contMDiffWithinAt_homogeneousFamily_iff

/-- A family of homogeneous polynomials parametrized by `M` is `C^r` on a set if and only if all of
its monomial coefficients are `C^r` on that set. -/
theorem contMDiffOn_homogeneousFamily_iff :
    ContMDiffOn I (homogeneousFamilyModel σ 𝕜 𝕜' d) r c t ↔
      ∀ (k : ι) (s : {s : σ →₀ ℕ // s.degree = d k}),
        ContMDiffOn I 𝓘(𝕜, 𝕜') r (fun m ↦ (c m k : MvPolynomial σ 𝕜').coeff s) t := by
  rw [contMDiffOn_pi_iff]
  exact forall_congr' fun _ ↦ contMDiffOn_homogeneousSubmodule_iff

/-- A family of homogeneous polynomials parametrized by `M` is `C^r` if and only if all of its
monomial coefficients are `C^r`. -/
theorem contMDiff_homogeneousFamily_iff :
    ContMDiff I (homogeneousFamilyModel σ 𝕜 𝕜' d) r c ↔
      ∀ (k : ι) (s : {s : σ →₀ ℕ // s.degree = d k}),
        ContMDiff I 𝓘(𝕜, 𝕜') r fun m ↦ (c m k : MvPolynomial σ 𝕜').coeff s := by
  rw [contMDiff_pi_iff]
  exact forall_congr' fun _ ↦ contMDiff_homogeneousSubmodule_iff

end Family

end Manifold

end TauCeti
