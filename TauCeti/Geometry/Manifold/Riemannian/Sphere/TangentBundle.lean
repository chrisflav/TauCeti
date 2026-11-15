/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The tangent bundle of the sphere, its radial splitting, and multiplication from tangent frames

Let `E` be a real inner product space of dimension `n + 1`, and let `Sⁿ = sphere (0 : E) 1` carry
Mathlib's stereographic analytic manifold structure and `TauCeti.sphereRoundMetric`. At each point
`x ∈ Sⁿ`, the differential of the inclusion `Sⁿ → E` identifies `TangentSpace (𝓡 n) x`
isometrically with the orthogonal complement `(ℝ ∙ (x : E))ᗮ` (`TauCeti.sphereTangentEquiv`).

This file lifts that fibrewise identification to the smooth and analytic bundle level and derives
the geometric constructions it governs:

1. **Ambient characterization of smooth tangent maps.** Reading a tangent vector in `E` via
   `TauCeti.sphereTangentEquiv` is the differential of the analytic inclusion `Sⁿ → E`, while the
   left-inverse tangential lift `TauCeti.sphereTangentialLift x u` of an ambient vector `u ∈ E`
   coincides with the round Riemannian gradient at `x` of the linear height function
   `q ↦ ⟪u, q⟫` (`TauCeti.sphereTangentialLift_eq_mgradient`). Expanding `u` in an orthonormal basis
   of `E` shows that `sphereTangentialLift` is `C^ω`, hence `C^m` for every `m : ℕ∞ω` along any
   `C^m` maps from an arbitrary charted space (`TauCeti.contMDiffWithinAt_sphereTangentialLift`).
   Consequently, a map into `TangentBundle (𝓡 n) Sⁿ` is `C^m` if and only if its base map and
   ambient vector component in `E` are `C^m` (`TauCeti.contMDiff_tangentBundle_sphere_iff`).

2. **The orthogonal-complement subbundle and the radial-normal splitting.** Pushing local
   orthonormal tangent frames forward along `sphereTangentEquiv` equips the family of hyperplanes
   `TauCeti.sphereOrthogonalSubbundle x = (ℝ ∙ (x : E))ᗮ` inside the trivial bundle `Sⁿ × E` with
   `C^m` local subbundle frames
   (`TauCeti.hasLocalContMDiffSubbundleFrames_sphereOrthogonalSubbundle`) and yields a `C^m`
   diffeomorphism `TauCeti.sphereTangentSubbundleDiffeomorph` from `TangentBundle (𝓡 n) Sⁿ` onto
   the subbundle total space. Its orthogonal complement is the rank-`1` radial normal subbundle
   `TauCeti.sphereNormalSubbundle x = ℝ ∙ (x : E)`, globally framed by `x ↦ x`
   (`TauCeti.hasLocalContMDiffSubbundleFrames_sphereNormalSubbundle`) and complementary in every
   fibre (`TauCeti.isCompl_sphereOrthogonalSubbundle_sphereNormalSubbundle`). Adjoining the radial
   coordinate gives the `C^m` diffeomorphism `TauCeti.sphereTangentRadialDiffeomorph` between
   `TangentBundle (𝓡 n) Sⁿ × ℝ` and `Sⁿ × E` expressing `TSⁿ ⊕ ε¹ ≃ Sⁿ × E`.

3. **Orthogonal families and strict-unit H-space multiplications from tangent frames.** Given a
   basepoint `e₀ ∈ Sⁿ` and any `C^m` tangent frame `v` on `Sⁿ`, fibrewise Gram–Schmidt
   orthonormalization (`ContMDiff.gramSchmidtNormed_bundle`) followed by prepending the unit radius
   vector produces at each `x ∈ Sⁿ` an orthonormal basis `TauCeti.sphereFrameOrthonormalBasis` of
   `E`. Sending the basis at `e₀` to the basis at `x` defines a `C^m` family of linear isometry
   equivalences `TauCeti.sphereFrameIsometry` of `E` (hence, on `ℝⁿ⁺¹`, a continuous map
   `TauCeti.sphereFrameOrthogonalMatrix` into `O(n + 1)` with `C^m` matrix entries, landing in
   `SO(n + 1)` whenever `1 ≤ n`) that equals the identity at `e₀` and sends `e₀` to `x`. Acting on
   the second factor defines a `C^m` multiplication `TauCeti.sphereFrameMul : Sⁿ → Sⁿ → Sⁿ` with
   `e₀` as a strict two-sided identity and diffeomorphic left translations.

## Main definitions

* `TauCeti.sphereTangentialLift`: orthogonal projection of an ambient vector in `E` onto `(x : E)ᗮ`,
  lifted to `TangentSpace (𝓡 n) x` via `(sphereTangentEquiv x).symm`.
* `TauCeti.sphereOrthogonalSubbundle`, `TauCeti.sphereNormalSubbundle`: the complementary
  hyperplane `(ℝ ∙ (x : E))ᗮ` and radial line `ℝ ∙ (x : E)` subbundles of `Sⁿ × E`.
* `TauCeti.sphereTangentSubbundleDiffeomorph`: the `C^m` diffeomorphism between
  `TangentBundle (𝓡 n) Sⁿ` and the total space of `sphereOrthogonalSubbundle`.
* `TauCeti.sphereTangentRadialDiffeomorph`: the `C^m` radial-normal splitting diffeomorphism
  `TangentBundle (𝓡 n) Sⁿ × ℝ ≃ₘ^m Sⁿ × E`.
* `TauCeti.sphereFrameOrthonormalBasis`, `TauCeti.sphereFrameIsometry`, `TauCeti.sphereFrameMul`:
  the orthonormal ambient frame, normalized linear-isometry family, and strict-unit `C^m`
  multiplication on `Sⁿ` induced by a `C^m` tangent frame.
* `TauCeti.sphereBasepoint`, `TauCeti.sphereFrameOrthogonalMatrix`: the standard north pole of
  `Sⁿ ⊂ ℝⁿ⁺¹` and the map `Sⁿ → O(n + 1)` (with `C^m` matrix entries, landing in `SO(n + 1)` for
  `1 ≤ n`) associated to a `C^m` tangent frame.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
* A. Hatcher, *Vector Bundles and K-Theory*, §§1.1 and 2.3 (tangent bundle of `Sⁿ`, stable
  triviality `TSⁿ ⊕ ε¹ ≃ εⁿ⁺¹`, and H-space multiplications from framings).
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Princeton University Press (1974), §3.
-/

public section

open Bundle InnerProductSpace Metric Module Set
open scoped ContDiff Manifold Matrix

noncomputable section

namespace TauCeti

section AmbientTangent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] {m : ℕ∞ω}

/-- Reading a tangent vector of the unit sphere in the ambient space `E` through
`TauCeti.sphereTangentEquiv` is `C^m` on the tangent bundle for every smoothness exponent `m`. -/
theorem contMDiff_coe_sphereTangentEquiv :
    ContMDiff (𝓡 n).tangent 𝓘(ℝ, E) m
      (fun q : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦ (sphereTangentEquiv q.proj q.2 : E)) := by
  have htan : ContMDiff (𝓡 n).tangent (𝓘(ℝ, E).prod 𝓘(ℝ, E)) m
      (fun q : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
        TotalSpace.mk' E (q.proj : E)
          (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) q.proj q.2)) :=
    (contMDiff_coe_sphere (E := E) (n := n) (m := ω)).mfderiv_apply_sectionAlong
      contMDiff_id le_top
  refine fun q ↦ ((Bundle.contMDiffAt_totalSpace_iff.mp (htan q)).2).congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun r ↦ ?_
  dsimp only
  have hmem : (r.proj : E) ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (q.proj : E)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, chartAt_self_eq]
    exact mem_univ _
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (q.proj : E)) hmem,
    TangentBundle.continuousLinearMapAt_model_space]
  exact coe_sphereTangentEquiv_apply r.proj r.2

/-- Orthogonal projection of an ambient vector `u : E` onto `(ℝ ∙ (x : E))ᗮ`, transported to
`TangentSpace (𝓡 n) x` through `(sphereTangentEquiv x).symm`. -/
def sphereTangentialLift (x : sphere (0 : E) 1) : E →L[ℝ] TangentSpace (𝓡 n) x :=
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  (sphereTangentEquiv x).symm.toLinearIsometry.toContinuousLinearMap.comp
    (ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto

/-- Applying `TauCeti.sphereTangentEquiv` to `TauCeti.sphereTangentialLift x u` recovers the
orthogonal projection of `u` onto `(ℝ ∙ (x : E))ᗮ`. -/
@[simp]
theorem sphereTangentEquiv_sphereTangentialLift (x : sphere (0 : E) 1) (u : E) :
    sphereTangentEquiv x (sphereTangentialLift (n := n) x u) =
      (letI : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
      (ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto u) := by
  simp only [sphereTangentialLift, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply]

/-- Read back in `E`, `TauCeti.sphereTangentialLift x u` is the tangential component
`u - ⟪x, u⟫ x` of `u`. -/
theorem coe_sphereTangentEquiv_sphereTangentialLift (x : sphere (0 : E) 1) (u : E) :
    (sphereTangentEquiv x (sphereTangentialLift (n := n) x u) : E) =
      u - inner ℝ (x : E) u • (x : E) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  rw [sphereTangentEquiv_sphereTangentialLift, Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ (norm_eq_of_mem_sphere x)]

/-- If `u` is already orthogonal to `x`, `TauCeti.sphereTangentialLift x u` reads back as `u` in
the ambient space `E`. -/
theorem coe_sphereTangentEquiv_sphereTangentialLift_of_inner_eq_zero {x : sphere (0 : E) 1} {u : E}
    (hu : inner ℝ (x : E) u = 0) :
    (sphereTangentEquiv x (sphereTangentialLift (n := n) x u) : E) = u := by
  rw [coe_sphereTangentEquiv_sphereTangentialLift, hu, zero_smul, sub_zero]

/-- `TauCeti.sphereTangentialLift x` is a left inverse to reading `TangentSpace (𝓡 n) x` in `E`. -/
theorem sphereTangentialLift_coe_sphereTangentEquiv (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    sphereTangentialLift x (sphereTangentEquiv x v : E) = v := by
  apply (sphereTangentEquiv x).injective
  apply Subtype.ext
  exact coe_sphereTangentEquiv_sphereTangentialLift_of_inner_eq_zero
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (sphereTangentEquiv x v).2)

/-- The tangential lift of the outward unit radius vector `x` at `x` vanishes. -/
@[simp]
theorem sphereTangentialLift_self (x : sphere (0 : E) 1) :
    sphereTangentialLift (n := n) x (x : E) = 0 := by
  apply (sphereTangentEquiv x).injective
  apply Subtype.ext
  rw [coe_sphereTangentEquiv_sphereTangentialLift, real_inner_self_eq_norm_sq,
    norm_eq_of_mem_sphere x, one_pow, one_smul, sub_self, map_zero, Submodule.coe_zero]

/-- **The tangential lift of a constant ambient vector is a height gradient.** At `x ∈ Sⁿ`, lifting
`u ∈ E` tangentially agrees with the round Riemannian gradient of the height function
`q ↦ ⟪u, q⟫`. -/
theorem sphereTangentialLift_eq_mgradient (x : sphere (0 : E) 1) (u : E) :
    sphereTangentialLift x u =
      Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ u (q : E)) x := by
  apply (sphereTangentEquiv x).injective
  apply Subtype.ext
  rw [coe_sphereTangentEquiv_sphereTangentialLift, coe_sphereTangentEquiv_apply,
    ← mvfderiv_apply_eq_mfderiv_apply, mvfderiv_coe_mgradient_inner_coe_sphere, real_inner_comm]

/-- Lifting a `C^m` ambient vector map along a `C^m` base map into the unit sphere produces a
`C^m` map into `TangentBundle (𝓡 n) Sⁿ`, at every smoothness order `m` (including `m = 0`). -/
theorem contMDiffWithinAt_sphereTangentialLift {b : P → sphere (0 : E) 1} {u : P → E}
    {s : Set P} {p₀ : P} (hb : ContMDiffWithinAt IP (𝓡 n) m b s p₀)
    (hu : ContMDiffWithinAt IP 𝓘(ℝ, E) m u s p₀) :
    ContMDiffWithinAt IP (𝓡 n).tangent m
      (fun p ↦ (⟨b p, sphereTangentialLift (b p) (u p)⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) s p₀ := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  let eE := stdOrthonormalBasis ℝ E
  have hgrad (j : Fin (finrank ℝ E)) :
      ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x : sphere (0 : E) 1 ↦
          (⟨x, Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ (eE j) (q : E)) x⟩ :
            TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
    have hheight : ContMDiff (𝓡 n) 𝓘(ℝ) (ω + 1)
        (fun q : sphere (0 : E) 1 ↦ inner ℝ (eE j) (q : E)) :=
      (innerSL ℝ (eE j)).contDiff.comp_contMDiff contMDiff_coe_sphere
    exact (Manifold.contMDiff_mgradient (n := ω) hheight).of_le le_top
  have hsum := ContMDiffWithinAt.sum_sectionAlong (F := EuclideanSpace ℝ (Fin n))
    (V := TangentSpace (𝓡 n)) Finset.univ
    (fun j p ↦ inner ℝ (eE j) (u p) •
      Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ (eE j) (q : E)) (b p))
    hb fun j _ ↦ by
      have hc : ContMDiffWithinAt IP 𝓘(ℝ) m (fun p ↦ inner ℝ (eE j) (u p)) s p₀ :=
        ((innerSL ℝ (eE j)).contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt p₀ hu)
      exact hc.smul_totalSpace ((hgrad j (b p₀)).comp_contMDiffWithinAt p₀ hb)
  have heq (p : P) :
      (⟨b p, sphereTangentialLift (b p) (u p)⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)) =
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (b p)
          (∑ j, inner ℝ (eE j) (u p) • Manifold.mgradient (𝓡 n)
            (fun q : sphere (0 : E) 1 ↦ inner ℝ (eE j) (q : E)) (b p)) := by
    apply congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (b p))
    conv_lhs => rw [← eE.sum_repr' (u p)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, sphereTangentialLift_eq_mgradient]
  exact hsum.congr (fun p _ ↦ heq p) (heq p₀)

/-- Pointwise `C^m` smoothness of `TauCeti.sphereTangentialLift` along `C^m` maps. -/
theorem contMDiffAt_sphereTangentialLift {b : P → sphere (0 : E) 1} {u : P → E} {p₀ : P}
    (hb : ContMDiffAt IP (𝓡 n) m b p₀) (hu : ContMDiffAt IP 𝓘(ℝ, E) m u p₀) :
    ContMDiffAt IP (𝓡 n).tangent m
      (fun p ↦ (⟨b p, sphereTangentialLift (b p) (u p)⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) p₀ :=
  contMDiffWithinAt_sphereTangentialLift hb hu

/-- Setwise `C^m` smoothness of `TauCeti.sphereTangentialLift` along `C^m` maps. -/
theorem contMDiffOn_sphereTangentialLift {b : P → sphere (0 : E) 1} {u : P → E} {s : Set P}
    (hb : ContMDiffOn IP (𝓡 n) m b s) (hu : ContMDiffOn IP 𝓘(ℝ, E) m u s) :
    ContMDiffOn IP (𝓡 n).tangent m
      (fun p ↦ (⟨b p, sphereTangentialLift (b p) (u p)⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) s :=
  fun p hp ↦ contMDiffWithinAt_sphereTangentialLift (hb p hp) (hu p hp)

/-- Global `C^m` smoothness of `TauCeti.sphereTangentialLift` along `C^m` maps. -/
theorem contMDiff_sphereTangentialLift {b : P → sphere (0 : E) 1} {u : P → E}
    (hb : ContMDiff IP (𝓡 n) m b) (hu : ContMDiff IP 𝓘(ℝ, E) m u) :
    ContMDiff IP (𝓡 n).tangent m
      (fun p ↦ (⟨b p, sphereTangentialLift (b p) (u p)⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
  fun p ↦ contMDiffAt_sphereTangentialLift (hb p) (hu p)

/-- **Ambient characterization of `C^m` maps into `TangentBundle (𝓡 n) Sⁿ` within a set.** A map
`p ↦ ⟨b p, v p⟩` into the tangent bundle of the unit sphere is `C^m` within `s` at `p₀` if and
only if its base map `b` and ambient vector map `p ↦ (sphereTangentEquiv (b p) (v p) : E)` are
`C^m` within `s` at `p₀`. -/
theorem contMDiffWithinAt_tangentBundle_sphere_iff {b : P → sphere (0 : E) 1}
    {v : ∀ p, TangentSpace (𝓡 n) (b p)} {s : Set P} {p₀ : P} :
    ContMDiffWithinAt IP (𝓡 n).tangent m
        (fun p ↦ (⟨b p, v p⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) s p₀ ↔
      ContMDiffWithinAt IP (𝓡 n) m b s p₀ ∧
        ContMDiffWithinAt IP 𝓘(ℝ, E) m (fun p ↦ (sphereTangentEquiv (b p) (v p) : E)) s p₀ := by
  refine ⟨fun h ↦ ⟨(Bundle.contMDiffAt_proj (TangentSpace (𝓡 n))).comp_contMDiffWithinAt p₀ h,
    (contMDiff_coe_sphereTangentEquiv _).comp_contMDiffWithinAt p₀ h⟩, fun ⟨hb, hv⟩ ↦ ?_⟩
  simpa only [sphereTangentialLift_coe_sphereTangentEquiv] using
    contMDiffWithinAt_sphereTangentialLift hb hv

/-- **Ambient characterization of `C^m` maps into `TangentBundle (𝓡 n) Sⁿ` at a point.** -/
theorem contMDiffAt_tangentBundle_sphere_iff {b : P → sphere (0 : E) 1}
    {v : ∀ p, TangentSpace (𝓡 n) (b p)} {p₀ : P} :
    ContMDiffAt IP (𝓡 n).tangent m
        (fun p ↦ (⟨b p, v p⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) p₀ ↔
      ContMDiffAt IP (𝓡 n) m b p₀ ∧
        ContMDiffAt IP 𝓘(ℝ, E) m (fun p ↦ (sphereTangentEquiv (b p) (v p) : E)) p₀ := by
  simp only [← contMDiffWithinAt_univ, contMDiffWithinAt_tangentBundle_sphere_iff]

/-- **Ambient characterization of `C^m` maps into `TangentBundle (𝓡 n) Sⁿ` on a set.** -/
theorem contMDiffOn_tangentBundle_sphere_iff {b : P → sphere (0 : E) 1}
    {v : ∀ p, TangentSpace (𝓡 n) (b p)} {s : Set P} :
    ContMDiffOn IP (𝓡 n).tangent m
        (fun p ↦ (⟨b p, v p⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) s ↔
      ContMDiffOn IP (𝓡 n) m b s ∧
        ContMDiffOn IP 𝓘(ℝ, E) m (fun p ↦ (sphereTangentEquiv (b p) (v p) : E)) s :=
  ⟨fun h ↦ ⟨fun p hp ↦ (contMDiffWithinAt_tangentBundle_sphere_iff.mp (h p hp)).1,
      fun p hp ↦ (contMDiffWithinAt_tangentBundle_sphere_iff.mp (h p hp)).2⟩,
    fun ⟨hb, hv⟩ p hp ↦ contMDiffWithinAt_tangentBundle_sphere_iff.mpr ⟨hb p hp, hv p hp⟩⟩

/-- **Ambient characterization of global `C^m` maps into `TangentBundle (𝓡 n) Sⁿ`.** -/
theorem contMDiff_tangentBundle_sphere_iff {b : P → sphere (0 : E) 1}
    {v : ∀ p, TangentSpace (𝓡 n) (b p)} :
    ContMDiff IP (𝓡 n).tangent m
        (fun p ↦ (⟨b p, v p⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      ContMDiff IP (𝓡 n) m b ∧
        ContMDiff IP 𝓘(ℝ, E) m (fun p ↦ (sphereTangentEquiv (b p) (v p) : E)) :=
  ⟨fun h ↦ ⟨fun p ↦ (contMDiffAt_tangentBundle_sphere_iff.mp (h p)).1,
      fun p ↦ (contMDiffAt_tangentBundle_sphere_iff.mp (h p)).2⟩,
    fun ⟨hb, hv⟩ p ↦ contMDiffAt_tangentBundle_sphere_iff.mpr ⟨hb p, hv p⟩⟩

/-- A vector field on the unit sphere is `C^m` if and only if its ambient reading in `E` via
`TauCeti.sphereTangentEquiv` is `C^m`. -/
theorem contMDiff_vectorField_sphere_iff
    {V : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x} :
    ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, V x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      ContMDiff (𝓡 n) 𝓘(ℝ, E) m (fun x ↦ (sphereTangentEquiv x (V x) : E)) := by
  rw [contMDiff_tangentBundle_sphere_iff]
  exact and_iff_right contMDiff_id

end AmbientTangent

/-! ### The orthogonal-complement subbundle and radial-normal bundle splitting -/

section SubbundleAndSplitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hyperplane subbundle `x ↦ (ℝ ∙ (x : E))ᗮ` inside the trivial ambient bundle `Sⁿ × E`. -/
def sphereOrthogonalSubbundle (x : sphere (0 : E) 1) :
    Submodule ℝ (Bundle.Trivial (sphere (0 : E) 1) E x) :=
  (ℝ ∙ (x : E))ᗮ

/-- `TauCeti.sphereOrthogonalSubbundle x` is the orthogonal complement of `ℝ ∙ (x : E)`. -/
theorem sphereOrthogonalSubbundle_def (x : sphere (0 : E) 1) :
    sphereOrthogonalSubbundle x = (ℝ ∙ (x : E))ᗮ :=
  (rfl)

/-- An ambient vector `u ∈ E` lies in `TauCeti.sphereOrthogonalSubbundle x` iff `⟪x, u⟫ = 0`. -/
@[simp]
theorem mem_sphereOrthogonalSubbundle_iff {x : sphere (0 : E) 1} {u : E} :
    u ∈ sphereOrthogonalSubbundle x ↔ inner ℝ (x : E) u = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

/-- The rank-`1` radial normal subbundle `x ↦ ℝ ∙ (x : E)` inside the trivial bundle `Sⁿ × E`. -/
def sphereNormalSubbundle (x : sphere (0 : E) 1) :
    Submodule ℝ (Bundle.Trivial (sphere (0 : E) 1) E x) :=
  ℝ ∙ (x : E)

/-- `TauCeti.sphereNormalSubbundle x` is the radial line `ℝ ∙ (x : E)`. -/
theorem sphereNormalSubbundle_def (x : sphere (0 : E) 1) :
    sphereNormalSubbundle x = (ℝ ∙ (x : E)) :=
  (rfl)

/-- An ambient vector `u ∈ E` lies in `TauCeti.sphereNormalSubbundle x` iff `u ∈ ℝ ∙ (x : E)`. -/
@[simp]
theorem mem_sphereNormalSubbundle_iff {x : sphere (0 : E) 1} {u : E} :
    u ∈ sphereNormalSubbundle x ↔ u ∈ ℝ ∙ (x : E) :=
  Iff.rfl

/-- At every point `x ∈ Sⁿ`, the tangent hyperplane `TauCeti.sphereOrthogonalSubbundle x` and the
radial normal line `TauCeti.sphereNormalSubbundle x` are complementary in `E`. -/
theorem isCompl_sphereOrthogonalSubbundle_sphereNormalSubbundle (x : sphere (0 : E) 1) :
    IsCompl (sphereOrthogonalSubbundle x) (sphereNormalSubbundle x) :=
  (ℝ ∙ (x : E)).isCompl_orthogonal.symm

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- `TauCeti.sphereTangentEquiv` viewed with codomain `TauCeti.sphereOrthogonalSubbundle x`. -/
def sphereTangentToOrthogonalSubbundle (x : sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] sphereOrthogonalSubbundle x :=
  sphereTangentEquiv x

/-- In ambient coordinates, `TauCeti.sphereTangentToOrthogonalSubbundle` agrees with
`TauCeti.sphereTangentEquiv`. -/
@[simp]
theorem coe_sphereTangentToOrthogonalSubbundle_apply (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    (sphereTangentToOrthogonalSubbundle x v : E) = (sphereTangentEquiv x v : E) := by
  dsimp only [sphereTangentToOrthogonalSubbundle, sphereOrthogonalSubbundle]
  rfl

/-- Reading the inverse of `TauCeti.sphereTangentToOrthogonalSubbundle` in `E` recovers the
ambient vector. -/
theorem coe_sphereTangentEquiv_sphereTangentToOrthogonalSubbundle_symm (x : sphere (0 : E) 1)
    (w : sphereOrthogonalSubbundle x) :
    (sphereTangentEquiv (n := n) x ((sphereTangentToOrthogonalSubbundle x).symm w) : E) =
      (w : E) := by
  rw [← coe_sphereTangentToOrthogonalSubbundle_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Pushing local orthonormal frames of `TangentSpace (𝓡 n)` forward through
`TauCeti.sphereTangentEquiv` gives `C^m` local subbundle frames of
`TauCeti.sphereOrthogonalSubbundle` at every smoothness order `m`. -/
theorem hasLocalContMDiffSubbundleFrames_sphereOrthogonalSubbundle (m : ℕ∞ω) :
    HasLocalContMDiffSubbundleFrames (𝓡 n) m E (Fin n)
      (sphereOrthogonalSubbundle (E := E)) := by
  rw [hasLocalContMDiffSubbundleFrames_iff]
  intro x₀
  let _ : IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ω) le_top
  obtain ⟨U, hU, hx₀U, u₀, hu₀, -⟩ := exists_isLocalFrameOn_orthonormal
    (I := 𝓡 n) (F := EuclideanSpace ℝ (Fin n)) (V := TangentSpace (𝓡 n)) (n := m) x₀
  let idx : Fin n ≃ Fin (finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)).symm
  let u : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x := fun i x ↦ u₀ (idx i) x
  let X : Fin n → (x : sphere (0 : E) 1) → Bundle.Trivial (sphere (0 : E) 1) E x :=
    fun i x ↦ (sphereTangentEquiv x (u i x) : E)
  have hXm (i : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) m (T% (X i)) U := by
    intro x hx
    rw [Bundle.contMDiffWithinAt_totalSpace_iff]
    exact ⟨contMDiffWithinAt_id,
      (contMDiffOn_tangentBundle_sphere_iff.mp (hu₀.contMDiffOn (idx i))).2 x hx⟩
  refine ⟨U, hU, hx₀U, X, ⟨fun i ↦ (hXm i).continuousOn, fun {x} hx ↦ ?_, fun {x} hx ↦ ?_⟩, hXm⟩
  · have hli : LinearIndependent ℝ (fun i ↦ u i x) :=
      (hu₀.linearIndependent hx).comp idx idx.injective
    exact hli.map' ((ℝ ∙ (x : E))ᗮ.subtype.comp (sphereTangentEquiv x).toLinearEquiv.toLinearMap)
      (LinearMap.ker_eq_bot_of_injective
        (Subtype.val_injective.comp (sphereTangentEquiv x).injective))
  · have hspan_u : Submodule.span ℝ (range (fun i ↦ u i x)) = ⊤ := by
      have hrng : range (fun i ↦ u i x) = range (fun j ↦ u₀ j x) :=
        idx.surjective.range_comp (fun j ↦ u₀ j x)
      rw [hrng]
      exact top_unique (hu₀.generating hx)
    have himg : range (X · x) =
        ((ℝ ∙ (x : E))ᗮ.subtype.comp (sphereTangentEquiv x).toLinearEquiv.toLinearMap) ''
          range (fun i ↦ u i x) := by
      rw [← range_comp]
      rfl
    rw [himg, ← Submodule.map_span, hspan_u, Submodule.map_comp,
      Submodule.map_top, LinearEquiv.range, Submodule.map_subtype_top]
    rfl

/-- **Smooth isomorphism of `TangentBundle (𝓡 n) Sⁿ` with the orthogonal-complement subbundle.**
Equipped with the subbundle topology and the `C^m` vector-bundle atlas generated by local frames,
`TotalSpace (Fin n → ℝ) sphereOrthogonalSubbundle` is `C^m`-diffeomorphic to
`TangentBundle (𝓡 n) Sⁿ` via `TauCeti.sphereTangentToOrthogonalSubbundle`. -/
def sphereTangentSubbundleDiffeomorph (m : ℕ∞ω) :
    letI := subbundleTopology E (F' := Fin n → ℝ) (sphereOrthogonalSubbundle (E := E))
    letI := (hasLocalContMDiffSubbundleFrames_sphereOrthogonalSubbundle (E := E) (n := n)
      m).fiberBundle
    TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m⟮(𝓡 n).tangent, (𝓡 n).prod 𝓘(ℝ, Fin n → ℝ)⟯
      TotalSpace (Fin n → ℝ) (fun x ↦ sphereOrthogonalSubbundle (E := E) x) :=
  let hV := hasLocalContMDiffSubbundleFrames_sphereOrthogonalSubbundle (E := E) (n := n) m
  letI := subbundleTopology E (F' := Fin n → ℝ) (sphereOrthogonalSubbundle (E := E))
  letI := hV.fiberBundle
  letI := hV.vectorBundle
  letI := hV.contMDiffVectorBundle
  { toFun := fun q ↦ ⟨q.proj, sphereTangentToOrthogonalSubbundle q.proj q.2⟩
    invFun := fun q ↦ ⟨q.proj, (sphereTangentToOrthogonalSubbundle q.proj).symm q.2⟩
    left_inv := fun ⟨x, v⟩ ↦
      congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x)
        ((sphereTangentToOrthogonalSubbundle x).symm_apply_apply v)
    right_inv := fun ⟨x, w⟩ ↦
      congrArg (TotalSpace.mk' (Fin n → ℝ) (E := fun y ↦ sphereOrthogonalSubbundle y) x)
        ((sphereTangentToOrthogonalSubbundle x).apply_symm_apply w)
    contMDiff_toFun := fun q ↦ by
      have hw : ContMDiffAt (𝓡 n).tangent ((𝓡 n).prod 𝓘(ℝ, E)) m
          (fun r : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
            (⟨r.proj, (sphereTangentToOrthogonalSubbundle r.proj r.2 : E)⟩ :
              TotalSpace E (Bundle.Trivial (sphere (0 : E) 1) E))) q :=
        Bundle.contMDiffAt_totalSpace_iff.mpr
          ⟨(Bundle.contMDiff_proj (TangentSpace (𝓡 n))).contMDiffAt,
            contMDiff_coe_sphereTangentEquiv q⟩
      exact hV.contMDiffAt_totalSpace_mk hw fun r ↦
        (sphereTangentToOrthogonalSubbundle r.proj r.2).2
    contMDiff_invFun := by
      have hinc := hV.contMDiff_totalSpace_inclusion
      have h2 : ContMDiff ((𝓡 n).prod 𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ, E) m
          (fun q : TotalSpace (Fin n → ℝ) (fun x ↦ sphereOrthogonalSubbundle (E := E) x) ↦
            (q.2 : E)) :=
        fun q ↦ (Bundle.contMDiffAt_totalSpace_iff.mp (hinc q)).2
      refine contMDiff_tangentBundle_sphere_iff.mpr
        ⟨fun q ↦ (Bundle.contMDiffAt_totalSpace_iff.mp (hinc q)).1, ?_⟩
      refine h2.congr fun q ↦ ?_
      exact congrArg Subtype.val
        ((sphereTangentToOrthogonalSubbundle q.proj).apply_symm_apply q.2) }

/-- Evaluation formula for `TauCeti.sphereTangentSubbundleDiffeomorph`. -/
@[simp]
theorem sphereTangentSubbundleDiffeomorph_apply (m : ℕ∞ω)
    (q : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    (letI := subbundleTopology E (F' := Fin n → ℝ) (sphereOrthogonalSubbundle (E := E))
    letI := (hasLocalContMDiffSubbundleFrames_sphereOrthogonalSubbundle (E := E) (n := n)
      m).fiberBundle
    sphereTangentSubbundleDiffeomorph (E := E) (n := n) m q) =
      ⟨q.proj, sphereTangentToOrthogonalSubbundle q.proj q.2⟩ :=
  (rfl)

/-- Evaluation formula for `(TauCeti.sphereTangentSubbundleDiffeomorph m).symm`. -/
@[simp]
theorem sphereTangentSubbundleDiffeomorph_symm_apply (m : ℕ∞ω)
    (q : TotalSpace (Fin n → ℝ) (fun x ↦ sphereOrthogonalSubbundle (E := E) x)) :
    (letI := subbundleTopology E (F' := Fin n → ℝ) (sphereOrthogonalSubbundle (E := E))
    letI := (hasLocalContMDiffSubbundleFrames_sphereOrthogonalSubbundle (E := E) (n := n)
      m).fiberBundle
    (sphereTangentSubbundleDiffeomorph (E := E) (n := n) m).symm q) =
      ⟨q.proj, (sphereTangentToOrthogonalSubbundle q.proj).symm q.2⟩ :=
  (rfl)

/-- The outward unit radius section `x ↦ (x : E)` globally frames `TauCeti.sphereNormalSubbundle`
at every smoothness order `m`. -/
theorem hasLocalContMDiffSubbundleFrames_sphereNormalSubbundle (m : ℕ∞ω) :
    HasLocalContMDiffSubbundleFrames (𝓡 n) m E (Fin 1)
      (sphereNormalSubbundle (E := E)) := by
  rw [hasLocalContMDiffSubbundleFrames_iff]
  intro x₀
  let X : Fin 1 → (x : sphere (0 : E) 1) → Bundle.Trivial (sphere (0 : E) 1) E x :=
    fun _ x ↦ (x : E)
  have hXm (i : Fin 1) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) m (T% (X i)) univ := by
    intro x _
    rw [Bundle.contMDiffWithinAt_totalSpace_iff]
    exact ⟨contMDiffWithinAt_id, (contMDiff_coe_sphere (E := E) (n := n) x).contMDiffWithinAt⟩
  refine ⟨univ, isOpen_univ, mem_univ x₀, X,
    ⟨fun i ↦ (hXm i).continuousOn, fun {x} _ ↦ ?_, fun {x} _ ↦ ?_⟩, hXm⟩
  · refine Fintype.linearIndependent_iff.mpr fun g hg i ↦ ?_
    rw [Fin.sum_univ_one] at hg
    rw [Fin.eq_zero i]
    exact (smul_eq_zero.mp hg).resolve_right (ne_zero_of_mem_unit_sphere x)
  · rw [range_const]
    rfl

/-- **Radial-normal splitting of the trivial ambient bundle over the unit sphere.** Adjoining the
outward unit normal `x` to `TangentSpace (𝓡 n) x` gives a `C^m` diffeomorphism
`TangentBundle (𝓡 n) Sⁿ × ℝ ≃ₘ^m Sⁿ × E` at every smoothness order `m`, sending
`(⟨x, v⟩, t)` to `(x, dι_x(v) + t • x)` with inverse
`(x, u) ↦ (⟨x, sphereTangentialLift x u⟩, ⟪x, u⟫)`. -/
def sphereTangentRadialDiffeomorph (m : ℕ∞ω) :
    (TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ)
      ≃ₘ^m⟮(𝓡 n).tangent.prod 𝓘(ℝ), (𝓡 n).prod 𝓘(ℝ, E)⟯
      (sphere (0 : E) 1 × E) where
  toFun p := (p.1.proj, (sphereTangentEquiv p.1.proj p.1.2 : E) + p.2 • (p.1.proj : E))
  invFun p := (⟨p.1, sphereTangentialLift p.1 p.2⟩, inner ℝ (p.1 : E) p.2)
  left_inv := fun ⟨⟨x, v⟩, t⟩ ↦ by
    refine Prod.ext (congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x) ?_) ?_
    · dsimp only
      rw [map_add, sphereTangentialLift_coe_sphereTangentEquiv, map_smul,
        sphereTangentialLift_self, smul_zero, add_zero]
    · dsimp only
      rw [inner_add_right,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp (sphereTangentEquiv x v).2,
        real_inner_smul_right, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x,
        one_pow, mul_one, zero_add]
  right_inv := fun ⟨x, u⟩ ↦ by
    refine Prod.ext rfl ?_
    dsimp only
    rw [coe_sphereTangentEquiv_sphereTangentialLift (n := n), sub_add_cancel]
  contMDiff_toFun := by
    have hproj : ContMDiff ((𝓡 n).tangent.prod 𝓘(ℝ)) (𝓡 n) m (fun p :
        TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ ↦ p.1.proj) :=
      (Bundle.contMDiff_proj (TangentSpace (𝓡 n))).comp contMDiff_fst
    have hv : ContMDiff ((𝓡 n).tangent.prod 𝓘(ℝ)) 𝓘(ℝ, E) m (fun p :
        TangentBundle (𝓡 n) (sphere (0 : E) 1) × ℝ ↦ (sphereTangentEquiv p.1.proj p.1.2 : E)) :=
      contMDiff_coe_sphereTangentEquiv.comp contMDiff_fst
    exact hproj.prodMk (hv.add (contMDiff_snd.smul (contMDiff_coe_sphere.comp hproj)))
  contMDiff_invFun := by
    have hlift : ContMDiff ((𝓡 n).prod 𝓘(ℝ, E)) (𝓡 n).tangent m
        (fun p : sphere (0 : E) 1 × E ↦
          (⟨p.1, sphereTangentialLift p.1 p.2⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
      contMDiff_sphereTangentialLift contMDiff_fst contMDiff_snd
    have hrad : ContMDiff ((𝓡 n).prod 𝓘(ℝ, E)) 𝓘(ℝ) m
        (fun p : sphere (0 : E) 1 × E ↦ inner ℝ (p.1 : E) p.2) :=
      (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).contDiff.comp_contMDiff
        ((contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space contMDiff_snd)
    exact hlift.prodMk hrad

/-- Evaluation formula for `TauCeti.sphereTangentRadialDiffeomorph`. -/
@[simp]
theorem sphereTangentRadialDiffeomorph_apply (m : ℕ∞ω) (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) (t : ℝ) :
    sphereTangentRadialDiffeomorph m (⟨x, v⟩, t) =
      (x, (sphereTangentEquiv x v : E) + t • (x : E)) :=
  (rfl)

/-- Evaluation formula for `(TauCeti.sphereTangentRadialDiffeomorph m).symm`: decomposes `u ∈ E`
into its tangential lift and its radial inner product `⟪x, u⟫`. -/
@[simp]
theorem sphereTangentRadialDiffeomorph_symm_apply (m : ℕ∞ω) (x : sphere (0 : E) 1) (u : E) :
    (sphereTangentRadialDiffeomorph (n := n) m).symm (x, u) =
      (⟨x, sphereTangentialLift x u⟩, inner ℝ (x : E) u) :=
  (rfl)

/-- **Pythagorean identity for the radial-normal splitting.** Because `dι_x(v)` is orthogonal to
the unit radius vector `x` and `sphereTangentEquiv x` is an isometry, the ambient squared norm of
`dι_x(v) + t • x` equals `‖v‖ ^ 2 + t ^ 2`. -/
theorem norm_sq_sphereTangentRadial (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) (t : ℝ) :
    ‖(sphereTangentEquiv x v : E) + t • (x : E)‖ ^ 2 = ‖v‖ ^ 2 + t ^ 2 := by
  have horth : inner ℝ (sphereTangentEquiv x v : E) (t • (x : E)) = 0 := by
    rw [real_inner_smul_right, real_inner_comm,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (sphereTangentEquiv x v).2, mul_zero]
  rw [norm_add_sq_real, horth, mul_zero, add_zero, Submodule.norm_coe,
    LinearIsometryEquiv.norm_map, norm_smul, norm_eq_of_mem_sphere x, mul_one, Real.norm_eq_abs,
    sq_abs]

end SubbundleAndSplitting

/-! ### Orthogonal families and strict-unit H-space multiplications from tangent frames -/

section FrameMultiplication

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- Prepending the unit vector `x` to an orthonormal tangent frame at `x` read in `E` produces an
orthonormal family of `n + 1` vectors in `E`. -/
theorem orthonormal_finCons_coe_sphereTangentEquiv (x : sphere (0 : E) 1)
    {u : Fin n → TangentSpace (𝓡 n) x} (hu : Orthonormal ℝ u) :
    Orthonormal ℝ (Fin.cons (x : E) fun i ↦ (sphereTangentEquiv x (u i) : E)) := by
  refine ⟨fun k ↦ ?_, fun {i j} hij ↦ ?_⟩
  · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · rw [Fin.cons_zero]
      exact norm_eq_of_mem_sphere x
    · rw [Fin.cons_succ, Submodule.norm_coe, LinearIsometryEquiv.norm_map]
      exact hu.1 i
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact (hij rfl).elim
    · rw [Fin.cons_zero, Fin.cons_succ]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (sphereTangentEquiv x (u j)).2
    · rw [Fin.cons_succ, Fin.cons_zero, real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (sphereTangentEquiv x (u i)).2
    · rw [Fin.cons_succ, Fin.cons_succ, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
      exact hu.2 fun h ↦ hij (congrArg Fin.succ h)

/-- Given a pointwise linearly independent family of tangent vectors `v` on `Sⁿ`, fibrewise
Gram–Schmidt orthonormalization followed by prepending the unit radius vector yields an
orthonormal basis of `E` at every point `x ∈ Sⁿ`. -/
def sphereFrameOrthonormalBasis
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (x : sphere (0 : E) 1) :
    OrthonormalBasis (Fin (n + 1)) ℝ E :=
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  let horth := orthonormal_finCons_coe_sphereTangentEquiv x (gramSchmidtNormed_orthonormal (hli x))
  (basisOfOrthonormalOfCardEqFinrank horth
    ((Fintype.card_fin (n + 1)).trans (Fact.out : finrank ℝ E = n + 1).symm)).toOrthonormalBasis
    (by rwa [coe_basisOfOrthonormalOfCardEqFinrank])

/-- The `0`-th vector of `TauCeti.sphereFrameOrthonormalBasis` at `x` is the outward unit radius
vector `(x : E)`. -/
@[simp]
theorem sphereFrameOrthonormalBasis_zero
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (x : sphere (0 : E) 1) :
    sphereFrameOrthonormalBasis v hli x 0 = (x : E) := by
  rw [sphereFrameOrthonormalBasis, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfOrthonormalOfCardEqFinrank, Fin.cons_zero]

/-- The `(i + 1)`-th vector of `TauCeti.sphereFrameOrthonormalBasis` at `x` is the `i`-th
Gram–Schmidt vector of `v · x` read in `E`. -/
@[simp]
theorem sphereFrameOrthonormalBasis_succ
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (x : sphere (0 : E) 1) (i : Fin n) :
    sphereFrameOrthonormalBasis v hli x i.succ =
      (sphereTangentEquiv x (gramSchmidtNormed ℝ (fun j ↦ v j x) i) : E) := by
  rw [sphereFrameOrthonormalBasis, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfOrthonormalOfCardEqFinrank, Fin.cons_succ]

/-- The `C^m` family of linear isometry equivalences of `E` normalized at a basepoint `e₀ ∈ Sⁿ`,
sending `sphereFrameOrthonormalBasis v hli e₀` to `sphereFrameOrthonormalBasis v hli x`. -/
def sphereFrameIsometry (e₀ : sphere (0 : E) 1)
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (x : sphere (0 : E) 1) :
    E ≃ₗᵢ[ℝ] E :=
  (sphereFrameOrthonormalBasis v hli e₀).repr.trans
    (sphereFrameOrthonormalBasis v hli x).repr.symm

/-- Explicit rank-one expansion of `TauCeti.sphereFrameIsometry`: it sends `y ∈ E` to
`∑ k, ⟪b(e₀)_k, y⟫ • b(x)_k`. -/
theorem sphereFrameIsometry_apply (e₀ : sphere (0 : E) 1)
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (x : sphere (0 : E) 1) (y : E) :
    sphereFrameIsometry e₀ v hli x y =
      ∑ k : Fin (n + 1),
        inner ℝ (sphereFrameOrthonormalBasis v hli e₀ k) y •
          sphereFrameOrthonormalBasis v hli x k := by
  conv_lhs => rw [← (sphereFrameOrthonormalBasis v hli e₀).sum_repr' y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, sphereFrameIsometry, LinearIsometryEquiv.trans_apply,
    OrthonormalBasis.repr_self, OrthonormalBasis.repr_symm_single]

/-- At the basepoint `e₀`, `TauCeti.sphereFrameIsometry` is the identity isometry of `E`. -/
@[simp]
theorem sphereFrameIsometry_self (e₀ : sphere (0 : E) 1)
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) :
    sphereFrameIsometry e₀ v hli e₀ = LinearIsometryEquiv.refl ℝ E := by
  ext y
  rw [sphereFrameIsometry, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- `TauCeti.sphereFrameIsometry` at `x` carries the basepoint `e₀` to `x`. -/
@[simp]
theorem sphereFrameIsometry_apply_basepoint (e₀ : sphere (0 : E) 1)
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (x : sphere (0 : E) 1) :
    sphereFrameIsometry e₀ v hli x (e₀ : E) = (x : E) := by
  have h0 : (e₀ : E) = sphereFrameOrthonormalBasis v hli e₀ 0 :=
    (sphereFrameOrthonormalBasis_zero v hli e₀).symm
  rw [h0, sphereFrameIsometry, LinearIsometryEquiv.trans_apply,
    OrthonormalBasis.repr_self, OrthonormalBasis.repr_symm_single,
    sphereFrameOrthonormalBasis_zero]

/-- Each vector of `TauCeti.sphereFrameOrthonormalBasis` varies `C^m` on the unit sphere whenever
the input tangent frame `v` is `C^m`. -/
theorem contMDiff_sphereFrameOrthonormalBasis {m : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (k : Fin (n + 1)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) m (fun x ↦ sphereFrameOrthonormalBasis v hli x k) := by
  let _ : IsContMDiffRiemannianBundle (𝓡 n) m (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
    IsContMDiffRiemannianBundle.of_le (n := ω) le_top
  refine Fin.cases ?_ (fun i ↦ ?_) k
  · simpa only [sphereFrameOrthonormalBasis_zero] using
      (contMDiff_coe_sphere (E := E) (n := n) (m := m))
  · have hg : ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, gramSchmidtNormed ℝ (fun j ↦ v j x) i⟩ :
          TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
      ContMDiff.gramSchmidtNormed_bundle (b := id) i (fun j _ ↦ hv j)
        fun x ↦ (hli x).linearIndepOn _
    simpa only [sphereFrameOrthonormalBasis_succ] using
      contMDiff_vectorField_sphere_iff.mp hg

/-- **Smoothness of the normalized isometry family.** If `v` is a `C^m` tangent frame on `Sⁿ`, then
`x ↦ sphereFrameIsometry e₀ v hli x` is `C^m` into `E →L[ℝ] E`. -/
theorem contMDiff_sphereFrameIsometry {m : ℕ∞ω} (e₀ : sphere (0 : E) 1)
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) m
      (fun x ↦ (sphereFrameIsometry e₀ v hli x).toLinearIsometry.toContinuousLinearMap) := by
  have heq : (fun x ↦ (sphereFrameIsometry e₀ v hli x).toLinearIsometry.toContinuousLinearMap) =
      fun x ↦ ∑ k : Fin (n + 1),
        ContinuousLinearMap.smulRightL ℝ E E
          (innerSL ℝ (sphereFrameOrthonormalBasis v hli e₀ k))
          (sphereFrameOrthonormalBasis v hli x k) := by
    funext x
    ext y
    simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      sphereFrameIsometry_apply, sum_apply, ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [heq]
  exact contMDiff_finsetSum fun k _ ↦
    (ContinuousLinearMap.smulRightL ℝ E E _).contDiff.comp_contMDiff
      (contMDiff_sphereFrameOrthonormalBasis hv hli k)

private theorem exists_orthogonalMatrix_det_eq_sphereFrameIsometry {m : ℕ∞ω}
    (e₀ : sphere (0 : E) 1) {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) :
    ∃ M : sphere (0 : E) 1 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      Continuous (fun y ↦ (M y).det) ∧
      (∀ y, (M y).det =
        LinearMap.det (sphereFrameIsometry e₀ v hli y).toLinearIsometry.toLinearMap) ∧
      ∀ y, M y ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ := by
  let eStd : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (sphereFrameOrthonormalBasis v hli e₀).repr
  let M : sphere (0 : E) 1 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun y ↦
    (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ)).symm
      ((eStd.symm.trans ((sphereFrameIsometry e₀ v hli y).trans eStd)
        ).toLinearIsometry.toContinuousLinearMap)
  refine ⟨M, ?_, fun y ↦ ?_, fun y ↦ ?_⟩
  · have hR := (contMDiff_sphereFrameIsometry e₀ hv hli).continuous
    have hconj : Continuous fun y : sphere (0 : E) 1 ↦
        ((eStd.symm.trans ((sphereFrameIsometry e₀ v hli y).trans eStd)
          ).toLinearIsometry.toContinuousLinearMap) := by
      have hpost := (ContinuousLinearMap.compL ℝ E E (EuclideanSpace ℝ (Fin (n + 1)))
        eStd.toLinearIsometry.toContinuousLinearMap).continuous.comp hR
      exact ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (n + 1))) E
        (EuclideanSpace ℝ (Fin (n + 1)))).flip
        eStd.symm.toLinearIsometry.toContinuousLinearMap).continuous.comp hpost
    exact Continuous.matrix_det (Matrix.continuous_toEuclideanCLM_symm.comp hconj)
  · rw [← Matrix.det_toEuclideanCLM, StarAlgEquiv.apply_symm_apply, ContinuousLinearMap.det]
    have hlin : ((eStd.symm.trans ((sphereFrameIsometry e₀ v hli y).trans eStd)
        ).toLinearIsometry.toContinuousLinearMap :
          EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) =
        (eStd.toLinearEquiv : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) ∘ₗ
          (sphereFrameIsometry e₀ v hli y).toLinearIsometry.toLinearMap ∘ₗ
          (eStd.toLinearEquiv.symm : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] E) := rfl
    rw [hlin]
    exact LinearMap.det_conj _ eStd.toLinearEquiv
  · rw [Matrix.mem_unitaryGroup_iff_inner_toEuclideanCLM]
    intro a b
    rw [StarAlgEquiv.apply_symm_apply]
    exact (eStd.symm.trans ((sphereFrameIsometry e₀ v hli y).trans eStd)).inner_map_map a b

/-- On a sphere of dimension `n ≥ 1`, `TauCeti.sphereFrameIsometry` has determinant `1` at every
point. -/
theorem det_sphereFrameIsometry_eq_one {m : ℕ∞ω} (hn : 1 ≤ n) (e₀ : sphere (0 : E) 1)
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (x : sphere (0 : E) 1) :
    LinearMap.det (sphereFrameIsometry e₀ v hli x).toLinearIsometry.toLinearMap = 1 := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  have hrank : 1 < Module.rank ℝ E := by
    rw [← finrank_eq_rank, Fact.out (p := finrank ℝ E = n + 1)]
    exact_mod_cast Nat.succ_lt_succ hn
  obtain ⟨M, hM_cont, hM_det, hM_orth⟩ :=
    exists_orthogonalMatrix_det_eq_sphereFrameIsometry e₀ hv hli
  have hM_e₀ : (M e₀).det = 1 := by
    rw [hM_det, sphereFrameIsometry_self]
    exact LinearMap.det_id
  rw [← hM_det]
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup (hM_orth x) with h1 | hm1
  · exact h1
  · exfalso
    let _ : PreconnectedSpace (sphere (0 : E) 1) :=
      Subtype.preconnectedSpace (isPreconnected_sphere hrank 0 1)
    have hmem : (0 : ℝ) ∈ (fun y ↦ (M y).det) '' univ :=
      isPreconnected_univ.intermediate_value (mem_univ x) (mem_univ e₀) hM_cont.continuousOn
        (by rw [hm1, hM_e₀]; exact ⟨by norm_num, by norm_num⟩)
    obtain ⟨y, -, hy0⟩ := hmem
    rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup (hM_orth y) with h | h <;> linarith

/-- **Strict-unit `C^m` multiplication on `Sⁿ` from a `C^m` tangent frame.** Given a basepoint
`e₀ ∈ Sⁿ` and a `C^m` tangent frame `v`, multiplying `x` and `y` by applying
`sphereFrameIsometry e₀ v hli x` to `y` defines an H-space multiplication with strict two-sided
unit `e₀`. -/
def sphereFrameMul (e₀ : sphere (0 : E) 1)
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x))
    (x y : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  (sphereFrameIsometry e₀ v hli x).unitSphereEquiv y

/-- Read in the ambient space `E`, `TauCeti.sphereFrameMul` applies `TauCeti.sphereFrameIsometry`
at `x` to `y`. -/
@[simp]
theorem coe_sphereFrameMul (e₀ : sphere (0 : E) 1)
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x))
    (x y : sphere (0 : E) 1) :
    ((sphereFrameMul e₀ v hli x y : sphere (0 : E) 1) : E) =
      sphereFrameIsometry e₀ v hli x y :=
  LinearIsometryEquiv.coe_unitSphereEquiv_apply _ _

/-- `e₀` is a strict left identity for `TauCeti.sphereFrameMul`. -/
@[simp]
theorem sphereFrameMul_left_id (e₀ : sphere (0 : E) 1)
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (y : sphere (0 : E) 1) :
    sphereFrameMul e₀ v hli e₀ y = y := by
  ext
  simp only [coe_sphereFrameMul, sphereFrameIsometry_self]
  rfl

/-- `e₀` is a strict right identity for `TauCeti.sphereFrameMul`. -/
@[simp]
theorem sphereFrameMul_right_id (e₀ : sphere (0 : E) 1)
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (x : sphere (0 : E) 1) :
    sphereFrameMul e₀ v hli x e₀ = x := by
  ext
  simp only [coe_sphereFrameMul, sphereFrameIsometry_apply_basepoint]

/-- Left translation by any `x ∈ Sⁿ` under `TauCeti.sphereFrameMul` is a bijection (in fact, the
isometric diffeomorphism `(sphereFrameIsometry e₀ v hli x).unitSphereDiffeomorph m`). -/
theorem bijective_sphereFrameMul_left (e₀ : sphere (0 : E) 1)
    (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (x : sphere (0 : E) 1) :
    Function.Bijective (sphereFrameMul e₀ v hli x) :=
  (sphereFrameIsometry e₀ v hli x).unitSphereEquiv.bijective

/-- **Joint `C^m` smoothness of the frame multiplication `Sⁿ × Sⁿ → Sⁿ`.** -/
theorem contMDiff_uncurry_sphereFrameMul {m : ℕ∞ω} (e₀ : sphere (0 : E) 1)
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))))
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) :
    ContMDiff ((𝓡 n).prod (𝓡 n)) (𝓡 n) m
      (Function.uncurry (sphereFrameMul e₀ v hli)) := by
  have hval : ContMDiff ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, E) m
      (fun p : sphere (0 : E) 1 × sphere (0 : E) 1 ↦
        (sphereFrameIsometry e₀ v hli p.1).toLinearIsometry.toContinuousLinearMap (p.2 : E)) :=
    ((contMDiff_sphereFrameIsometry e₀ hv hli).comp contMDiff_fst).clm_apply
      (contMDiff_coe_sphere.comp contMDiff_snd)
  have hmem (p : sphere (0 : E) 1 × sphere (0 : E) 1) :
      (sphereFrameIsometry e₀ v hli p.1).toLinearIsometry.toContinuousLinearMap (p.2 : E) ∈
        sphere (0 : E) 1 := by
    simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    exact ((sphereFrameIsometry e₀ v hli p.1).map_mem_unitSphere_iff _).mpr p.2.2
  refine (hval.codRestrict_sphere hmem).congr fun p ↦ ?_
  exact Subtype.ext (LinearIsometryEquiv.coe_unitSphereEquiv_apply _ _)

end FrameMultiplication

/-! ### Specialization to Euclidean spheres and `O(n + 1)` / `SO(n + 1)` -/

section EuclideanSphere

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- The standard basepoint `e₀ = (1, 0, …, 0)` of the unit `n`-sphere in `ℝⁿ⁺¹`. -/
def sphereBasepoint (n : ℕ) : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- In `ℝⁿ⁺¹`, `TauCeti.sphereBasepoint n` is the `0`-th standard basis vector
`EuclideanSpace.single 0 1`. -/
@[simp]
theorem coe_sphereBasepoint (n : ℕ) :
    (sphereBasepoint n : EuclideanSpace ℝ (Fin (n + 1))) = EuclideanSpace.single 0 1 :=
  (rfl)

/-- The orthogonal-matrix framing `Sⁿ → O(n + 1)` induced by a tangent frame `v` on the unit
sphere of `ℝⁿ⁺¹`, normalized at `TauCeti.sphereBasepoint n`. -/
def sphereFrameOrthogonalMatrix {n : ℕ}
    (v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x))
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
  ⟨(Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ)).symm
      (sphereFrameIsometry (sphereBasepoint n) v hli x).toLinearIsometry.toContinuousLinearMap, by
    rw [Matrix.mem_unitaryGroup_iff_inner_toEuclideanCLM]
    intro a b
    rw [StarAlgEquiv.apply_symm_apply]
    exact (sphereFrameIsometry (sphereBasepoint n) v hli x).inner_map_map a b⟩

/-- Acting on `ℝⁿ⁺¹` via `Matrix.UnitaryGroup.toLinearIsometryEquiv` recovers
`TauCeti.sphereFrameIsometry`. -/
@[simp]
theorem toLinearIsometryEquiv_sphereFrameOrthogonalMatrix {n : ℕ}
    (v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x))
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    letI := finrank_euclideanSpace_fin_succ_fact n
    Matrix.UnitaryGroup.toLinearIsometryEquiv (sphereFrameOrthogonalMatrix v hli x) =
      sphereFrameIsometry (sphereBasepoint n) v hli x := by
  let _ := finrank_euclideanSpace_fin_succ_fact n
  ext y : 1
  have h := DFunLike.congr_fun
    ((Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ)).apply_symm_apply
      (sphereFrameIsometry (sphereBasepoint n) v hli x).toLinearIsometry.toContinuousLinearMap) y
  simpa only [sphereFrameOrthogonalMatrix, Matrix.UnitaryGroup.toLinearIsometryEquiv_apply,
    Matrix.toEuclideanCLM_apply, Matrix.toLpLin_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry] using h

/-- At `TauCeti.sphereBasepoint n`, `TauCeti.sphereFrameOrthogonalMatrix` is the identity
orthogonal matrix `1`. -/
@[simp]
theorem sphereFrameOrthogonalMatrix_basepoint {n : ℕ}
    (v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) :
    sphereFrameOrthogonalMatrix v hli (sphereBasepoint n) = 1 := by
  let _ := finrank_euclideanSpace_fin_succ_fact n
  apply Matrix.UnitaryGroup.toLinearIsometryEquiv_injective
  rw [toLinearIsometryEquiv_sphereFrameOrthogonalMatrix, sphereFrameIsometry_self, map_one]
  rfl

/-- Evaluating `TauCeti.sphereFrameOrthogonalMatrix` on the standard first basis vector recovers
the point `x ∈ Sⁿ`. -/
theorem mulVec_single_zero_sphereFrameOrthogonalMatrix {n : ℕ}
    (v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x)
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x))
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (sphereFrameOrthogonalMatrix v hli x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ
        Pi.single 0 1 =
      (x : EuclideanSpace ℝ (Fin (n + 1))).ofLp := by
  let _ := finrank_euclideanSpace_fin_succ_fact n
  have h := congrArg WithLp.ofLp (DFunLike.congr_fun
    (toLinearIsometryEquiv_sphereFrameOrthogonalMatrix v hli x)
    (sphereBasepoint n : EuclideanSpace ℝ (Fin (n + 1))))
  have h0 : (sphereBasepoint n : EuclideanSpace ℝ (Fin (n + 1))).ofLp = Pi.single 0 1 := by
    ext k
    simp [sphereBasepoint, Pi.single_apply]
  simpa only [Matrix.UnitaryGroup.toLinearIsometryEquiv_apply, WithLp.ofLp_toLp, h0,
    sphereFrameIsometry_apply_basepoint] using h

/-- Every entry of `TauCeti.sphereFrameOrthogonalMatrix` is a `C^m` function on `Sⁿ` whenever the
input tangent frame `v` is `C^m`. -/
theorem contMDiff_sphereFrameOrthogonalMatrix_apply {n : ℕ} {m : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, v i x⟩ :
        TangentBundle (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))))
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) (i j : Fin (n + 1)) :
    ContMDiff (𝓡 n) 𝓘(ℝ) m
      (fun x ↦ (sphereFrameOrthogonalMatrix v hli x :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j) := by
  let _ := finrank_euclideanSpace_fin_succ_fact n
  let entryLM : (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) →ₗ[ℝ] ℝ :=
    (LinearMap.proj j).comp ((LinearMap.proj i).comp
      (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ)).symm.toAlgEquiv.toLinearEquiv.toLinearMap)
  let entryCLM : (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ] ℝ :=
    { toLinearMap := entryLM, cont := entryLM.continuous_of_finiteDimensional }
  exact entryCLM.contDiff.comp_contMDiff
    (contMDiff_sphereFrameIsometry (sphereBasepoint n) hv hli)

/-- `TauCeti.sphereFrameOrthogonalMatrix` is continuous into `O(n + 1)` whenever the tangent frame
`v` is `C^m`. -/
theorem continuous_sphereFrameOrthogonalMatrix {n : ℕ} {m : ℕ∞ω}
    {v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, v i x⟩ :
        TangentBundle (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))))
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x)) :
    Continuous (sphereFrameOrthogonalMatrix v hli) := by
  let _ := finrank_euclideanSpace_fin_succ_fact n
  exact (Matrix.continuous_toEuclideanCLM_symm.comp
    (contMDiff_sphereFrameIsometry (sphereBasepoint n) hv hli).continuous).subtype_mk _

/-- Whenever `1 ≤ n` and `v` is a `C^m` tangent frame on `Sⁿ`,
`TauCeti.sphereFrameOrthogonalMatrix` lands in `SO(n + 1)`. -/
theorem mem_specialOrthogonalGroup_sphereFrameOrthogonalMatrix {n : ℕ} {m : ℕ∞ω} (hn : 1 ≤ n)
    {v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, v i x⟩ :
        TangentBundle (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))))
    (hli : ∀ x, LinearIndependent ℝ (fun i ↦ v i x))
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (sphereFrameOrthogonalMatrix v hli x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) ∈
      Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ := by
  let _ := finrank_euclideanSpace_fin_succ_fact n
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨(sphereFrameOrthogonalMatrix v hli x).2, ?_⟩
  rw [← Matrix.UnitaryGroup.det_toLinearIsometryEquiv,
    toLinearIsometryEquiv_sphereFrameOrthogonalMatrix]
  exact det_sphereFrameIsometry_eq_one hn (sphereBasepoint n) hv hli x

end EuclideanSphere

end TauCeti
