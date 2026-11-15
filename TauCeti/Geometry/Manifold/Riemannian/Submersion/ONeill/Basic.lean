/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Prod
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# O'Neill's fundamental tensors

For a Riemannian submersion, the fundamental tensors measure the parts of the
Levi-Civita derivative that exchange the horizontal and vertical distributions.
`oneillA` takes the horizontal part of its first argument, while `oneillT` takes
its vertical part. Both are continuous bilinear maps on each tangent space,
not differential operators on freely chosen extensions of tangent vectors.

The construction uses the induced endomorphism connection to differentiate the
native horizontal orthogonal projection. The evaluation theorems identify it with
O'Neill's formulas on differentiable vector fields. For a fixed first argument, both tensors—and
their covariant derivatives under the iterated induced connection—are skew-adjoint, by metric
compatibility of the Levi-Civita connection (`inner_oneillA`, `inner_oneillT`,
`inner_hom_hom_oneillA`, `inner_hom_hom_oneillT`). Both tensors are smooth sections of the native
iterated Hom bundle, with covariant-derivative evaluation formulas `hom_hom_oneillA_apply` and
`hom_hom_oneillT_apply`, and both vanish identically for the first projection of a Riemannian
product (`TauCeti.oneillA_fst`, `TauCeti.oneillT_fst`).

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13
  (1966), 459–469, §1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2.

The construction uses `CovariantDerivative.hom_apply` and the native smooth
orthogonal projections from `Submersion.Smoothness`.
-/

public section

open Bundle Manifold
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

local notation "∇" => CovariantDerivative.leviCivitaConnection I M

private def exchangeTensor (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (ContinuousLinearMap.compL ℝ _ _ _
    ((mfderiv I J f x).ker.starProjection - (mfderiv I J f x).kerᗮ.starProjection)).comp
      ((CovariantDerivative.leviCivitaConnection I M).hom
        (CovariantDerivative.leviCivitaConnection I M)
        (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x)

/-- O'Neill's horizontal fundamental tensor, as a continuous bilinear map.
Its defining field formula is `oneillA_apply`. -/
def oneillA (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (exchangeTensor (I := I) (J := J) (f := f) x).comp
    ((h.horizontalLift x).toContinuousLinearMap ∘L mfderiv I J f x)

/-- O'Neill's vertical fundamental tensor, as a continuous bilinear map.
Its defining field formula is `oneillT_apply`. -/
def oneillT (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (exchangeTensor (I := I) (J := J) (f := f) x).comp
    (ContinuousLinearMap.id ℝ _ -
      (h.horizontalLift x).toContinuousLinearMap ∘L mfderiv I J f x)

include h

private theorem exchangeTensor_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    exchangeTensor (I := I) (J := J) (f := f) x v (Y x) =
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x v) +
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x v) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let P := fun y ↦ (mfderiv I J f y).kerᗮ.starProjection
  let Q := fun y ↦ (mfderiv I J f y).ker.starProjection
  let cov := CovariantDerivative.leviCivitaConnection I M
  have hP := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hPY := hP.clm_bundle_apply hY
  have hsplit : (fun y ↦ Q y (Y y)) = Y - fun y ↦ P y (Y y) := by
    ext y
    simp only [P, Q, Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply, Pi.sub_apply]
    abel
  have hQY : cov (fun y ↦ Q y (Y y)) x v =
      cov Y x v - cov (fun y ↦ P y (Y y)) x v := by
    rw [hsplit, cov.isCovariantDerivativeOnUniv.sub hY hPY]
    rfl
  have hPP (w : TangentSpace I x) : P x (P x w) = P x w :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  have hQP (w : TangentSpace I x) : Q x (P x w) = 0 := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Submodule.starProjection_orthogonal_apply_eq_zero
        (Submodule.starProjection_apply_mem (mfderiv I J f x).kerᗮ w)
  dsimp only [P, Q, cov] at hPP hQP hQY
  simp only [exchangeTensor, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    sub_apply, CovariantDerivative.hom_apply _ _ hP hY,
    map_sub, hPP, hQP]
  rw [hQY, map_sub]
  abel

/-- The horizontal fundamental tensor has O'Neill's field formula
`A_X Y = v ∇_(hX)(hY) + h ∇_(hX)(vY)`. Only differentiability of `Y` at
this point is needed; the direction is a tangent vector, not an extended field. -/
theorem oneillA_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    h.oneillA x v (Y x) =
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x
          ((mfderiv I J f x).kerᗮ.starProjection v)) +
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x
          ((mfderiv I J f x).kerᗮ.starProjection v)) := by
  simpa only [oneillA, h.horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply] using
    h.exchangeTensor_apply hY ((mfderiv I J f x).kerᗮ.starProjection v)

/-- The vertical fundamental tensor has O'Neill's field formula
`T_X Y = h ∇_(vX)(vY) + v ∇_(vX)(hY)`. -/
theorem oneillT_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    h.oneillT x v (Y x) =
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x
          ((mfderiv I J f x).ker.starProjection v)) +
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x
          ((mfderiv I J f x).ker.starProjection v)) := by
  simpa only [oneillT, h.id_sub_horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply, add_comm] using
    h.exchangeTensor_apply hY ((mfderiv I J f x).ker.starProjection v)

private theorem inner_exchangeTensor_add_inner {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (u : TangentSpace I x) :
    ⟪exchangeTensor (I := I) (J := J) (f := f) x u (Y x), Z x⟫_ℝ +
      ⟪Y x, exchangeTensor (I := I) (J := J) (f := f) x u (Z x)⟫_ℝ = 0 := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hV := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hH := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hzero (U W : Π y : M, TangentSpace I y) :
      (fun y ↦ ⟪(mfderiv I J f y).ker.starProjection (U y),
        (mfderiv I J f y).kerᗮ.starProjection (W y)⟫_ℝ) = fun _ ↦ 0 := by
    funext y
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.starProjection_apply_mem _ _) (Submodule.starProjection_apply_mem _ _)
  have hmetric := CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M)
  have hzero₂ : (fun y ↦ ⟪(mfderiv I J f y).kerᗮ.starProjection (Y y),
      (mfderiv I J f y).ker.starProjection (Z y)⟫_ℝ) = fun _ ↦ 0 :=
    (funext fun _ ↦ real_inner_comm _ _).trans (hzero Z Y)
  have h₁ := hmetric.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const
    (hV.clm_bundle_apply hY) (hH.clm_bundle_apply hZ)
    (Filter.EventuallyEq.of_eq (hzero Y Z)) u
  have h₂ := hmetric.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const
    (hH.clm_bundle_apply hY) (hV.clm_bundle_apply hZ)
    (Filter.EventuallyEq.of_eq hzero₂) u
  rw [h.exchangeTensor_apply hY, h.exchangeTensor_apply hZ]
  simp only [inner_add_left, inner_add_right, Submodule.starProjection_orthogonal,
    sub_apply, ContinuousLinearMap.id_apply, inner_sub_left,
    inner_sub_right, Submodule.inner_starProjection_left_eq_right] at h₁ h₂ ⊢
  linarith

/-- For a fixed first argument, O'Neill's horizontal tensor is skew-adjoint. -/
theorem inner_oneillA (x : M) (u v w : TangentSpace I x) :
    ⟪h.oneillA x u v, w⟫_ℝ = -⟪v, h.oneillA x u w⟫_ℝ := by
  have hskew := h.inner_exchangeTensor_add_inner
    (FiberBundle.mdifferentiableAt_extend I E v) (FiberBundle.mdifferentiableAt_extend I E w)
    ((mfderiv I J f x).kerᗮ.starProjection u)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [FiberBundle.extend_apply_self, oneillA, h.horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply] using hskew

/-- For a fixed first argument, O'Neill's vertical tensor is skew-adjoint. -/
theorem inner_oneillT (x : M) (u v w : TangentSpace I x) :
    ⟪h.oneillT x u v, w⟫_ℝ = -⟪v, h.oneillT x u w⟫_ℝ := by
  have hskew := h.inner_exchangeTensor_add_inner
    (FiberBundle.mdifferentiableAt_extend I E v) (FiberBundle.mdifferentiableAt_extend I E w)
    ((mfderiv I J f x).ker.starProjection u)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [FiberBundle.extend_apply_self, oneillT, h.id_sub_horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply] using hskew

/-- The covariant derivative of O'Neill's `A`-tensor remains skew-adjoint in its last two
arguments. -/
theorem inner_hom_hom_oneillA (x : M) (w u v z : TangentSpace I x) :
    ⟪∇.hom (∇.hom ∇) h.oneillA x w u v, z⟫_ℝ =
      -⟪v, ∇.hom (∇.hom ∇) h.oneillA x w u z⟫_ℝ :=
  (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).inner_hom_hom_of_skew
    h.inner_oneillA w u v z

/-- The covariant derivative of O'Neill's `T`-tensor remains skew-adjoint in its last two
arguments. -/
theorem inner_hom_hom_oneillT (x : M) (w u v z : TangentSpace I x) :
    ⟪∇.hom (∇.hom ∇) h.oneillT x w u v, z⟫_ℝ =
      -⟪v, ∇.hom (∇.hom ∇) h.oneillT x w u z⟫_ℝ :=
  (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).inner_hom_hom_of_skew
    h.inner_oneillT w u v z

section Smoothness

private theorem contMDiff_exchangeTensor_apply
    {X Y : Π x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X))
    (hY : ContMDiff I I.tangent ∞ (T% Y)) :
    ContMDiff I I.tangent ∞
      (T% (fun x ↦ exchangeTensor (I := I) (J := J) (f := f) x (X x) (Y x))) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hP := h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  have hD₁ := ∇.contMDiff_apply hX ((hP.clm_bundle_apply hY).of_le (by simp))
  have hD₂ := ∇.contMDiff_apply hX ((hQ.clm_bundle_apply hY).of_le (by simp))
  refine ((hQ.clm_bundle_apply hD₁).add_section (hP.clm_bundle_apply hD₂)).congr ?_
  intro x
  exact congrArg (TotalSpace.mk' E x)
    (h.exchangeTensor_apply (hY.mdifferentiableAt (by simp)) (X x))

variable [T2Space M]

/-- The horizontal fundamental tensor is a smooth section of the native bilinear Hom bundle. -/
theorem contMDiff_oneillA :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
        x (h.oneillA x)) := by
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hPX := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).clm_bundle_apply hX
  simpa only [oneillA, h.horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply] using
    h.contMDiff_exchangeTensor_apply hPX hY

/-- The vertical fundamental tensor is a smooth section of the native bilinear Hom bundle. -/
theorem contMDiff_oneillT :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
        x (h.oneillT x)) := by
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hQX := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply hX
  simpa only [oneillT, h.id_sub_horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply] using
    h.contMDiff_exchangeTensor_apply hQX hY

/-- O'Neill's horizontal fundamental tensor is pointwise differentiable as a section of the
iterated Hom bundle. -/
theorem mdifferentiableAt_oneillA {x : M} :
    MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) y
        (h.oneillA y)) x := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact (h.contMDiff_oneillA x).mdifferentiableAt (by simp)

/-- O'Neill's vertical fundamental tensor is pointwise differentiable as a section of the iterated
Hom bundle. -/
theorem mdifferentiableAt_oneillT {x : M} :
    MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) y
        (h.oneillT y)) x := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact (h.contMDiff_oneillT x).mdifferentiableAt (by simp)

/-- Evaluation of the covariant derivative of O'Neill's `A`-tensor on differentiable vector fields,
with differentiation direction `w` preceding the tensor slots `U x` and `V x`. -/
theorem hom_hom_oneillA_apply {U V : Π y : M, TangentSpace I y} {x : M}
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) (w : TangentSpace I x) :
    ∇.hom (∇.hom ∇) h.oneillA x w (U x) (V x) =
      ∇ (fun y ↦ h.oneillA y (U y) (V y)) x w -
        h.oneillA x (∇ U x w) (V x) - h.oneillA x (U x) (∇ V x w) :=
  CovariantDerivative.hom_hom_apply ∇ ∇ ∇ h.mdifferentiableAt_oneillA hU hV w

/-- Evaluation of the covariant derivative of O'Neill's `T`-tensor on differentiable vector fields,
with differentiation direction `w` preceding the tensor slots `U x` and `V x`. -/
theorem hom_hom_oneillT_apply {U V : Π y : M, TangentSpace I y} {x : M}
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) (w : TangentSpace I x) :
    ∇.hom (∇.hom ∇) h.oneillT x w (U x) (V x) =
      ∇ (fun y ↦ h.oneillT y (U y) (V y)) x w -
        h.oneillT x (∇ U x w) (V x) - h.oneillT x (U x) (∇ V x w) :=
  CovariantDerivative.hom_hom_apply ∇ ∇ ∇ h.mdifferentiableAt_oneillT hU hV w

end Smoothness

omit [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- The first argument of `A` depends only on its horizontal component. -/
@[simp] theorem oneillA_starProjection_orthogonal_ker (x : M) (v : TangentSpace I x) :
    h.oneillA x ((mfderiv I J f x).kerᗮ.starProjection v) = h.oneillA x v := by
  simp only [oneillA, h.horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

/-- The first argument of `T` depends only on its vertical component. -/
@[simp] theorem oneillT_starProjection_ker (x : M) (v : TangentSpace I x) :
    h.oneillT x ((mfderiv I J f x).ker.starProjection v) = h.oneillT x v := by
  simp only [oneillT, h.id_sub_horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

/-- `A` vanishes on vertical first arguments. -/
@[simp] theorem oneillA_starProjection_ker (x : M) (v : TangentSpace I x) :
    h.oneillA x ((mfderiv I J f x).ker.starProjection v) = 0 := by
  simp only [oneillA, h.horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply,
    Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  simp

/-- `T` vanishes on horizontal first arguments. -/
@[simp] theorem oneillT_starProjection_orthogonal_ker (x : M) (v : TangentSpace I x) :
    h.oneillT x ((mfderiv I J f x).kerᗮ.starProjection v) = 0 := by
  simp only [oneillT, h.id_sub_horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply,
    Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  simp

/-- `A_v` vanishes when `v` is vertical. -/
theorem oneillA_eq_zero_of_mem_ker {x : M} {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    h.oneillA x v = 0 := by
  rw [← Submodule.starProjection_eq_self_iff.mpr hv, h.oneillA_starProjection_ker]

/-- `T_v` vanishes when `v` is horizontal. -/
theorem oneillT_eq_zero_of_mem_orthogonal_ker {x : M} {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    h.oneillT x v = 0 := by
  rw [← Submodule.starProjection_eq_self_iff.mpr hv, h.oneillT_starProjection_orthogonal_ker]

end TauCeti.IsRiemannianSubmersion

section Product

open Bundle Manifold
open scoped ContDiff Manifold TauCeti

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

private theorem prodVectorField_extend_projections (p : M × N) (v : TangentSpace (I.prod J) p) :
    let Y₁ := FiberBundle.extend E (Manifold.tangentSpaceProdEquiv p v).1
    let Y₂ := FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p v).2
    Manifold.prodVectorField Y₁ Y₂ p = v ∧
      (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).kerᗮ.starProjection
        (Manifold.prodVectorField Y₁ Y₂ q)) = Manifold.prodVectorField Y₁ 0 ∧
      (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).ker.starProjection
        (Manifold.prodVectorField Y₁ Y₂ q)) = Manifold.prodVectorField 0 Y₂ := by
  refine ⟨?_, funext fun q ↦ ?_, funext fun q ↦ ?_⟩
  · apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [Manifold.tangentSpaceProdEquiv_prodVectorField, FiberBundle.extend_apply_self,
      FiberBundle.extend_apply_self, Prod.mk.eta]
  · rw [starProjection_orthogonal_ker_fst]
    apply (Manifold.tangentSpaceProdEquiv q).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, Manifold.tangentSpaceProdEquiv_prodVectorField,
      Manifold.tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply]
  · rw [starProjection_ker_fst]
    apply (Manifold.tangentSpaceProdEquiv q).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, Manifold.tangentSpaceProdEquiv_prodVectorField,
      Manifold.tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply]

variable
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

private theorem exchangeTensor_fst (p : M × N) :
    IsRiemannianSubmersion.exchangeTensor (I := I.prod J) (J := I) (f := @Prod.fst M N) p = 0 := by
  ext u v
  have ⟨hYp, hH, hV⟩ := prodVectorField_extend_projections p v
  have hY₁ : MDiffAt (T% (FiberBundle.extend E (Manifold.tangentSpaceProdEquiv p v).1)) p.1 :=
    FiberBundle.mdifferentiableAt_extend I E _
  have hY₂ : MDiffAt (T% (FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p v).2)) p.2 :=
    FiberBundle.mdifferentiableAt_extend J F _
  have h0M : MDiffAt (T% (0 : Π x : M, TangentSpace I x)) p.1 :=
    mdifferentiableAt_zeroSection ℝ (TangentSpace I)
  have h0N : MDiffAt (T% (0 : Π y : N, TangentSpace J y)) p.2 :=
    mdifferentiableAt_zeroSection ℝ (TangentSpace J)
  conv_lhs => rw [← hYp]
  rw [(isRiemannianSubmersion_fst (I := I) (J := J)).exchangeTensor_apply
      (Manifold.mdifferentiableAt_prodVectorField hY₁ hY₂) u,
    hH, hV, starProjection_ker_fst, starProjection_orthogonal_ker_fst]
  apply (Manifold.tangentSpaceProdEquiv p).injective
  simp only [zero_apply, map_add, map_zero, ContinuousLinearEquiv.apply_symm_apply,
    Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField hY₁ h0N,
    Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField h0M hY₂,
    (CovariantDerivative.leviCivitaConnection I M).zero,
    (CovariantDerivative.leviCivitaConnection J N).zero, Pi.zero_apply]
  ext <;> simp

/-- O'Neill's horizontal tensor `A` vanishes identically for the first projection of a Riemannian
product. -/
@[simp]
theorem oneillA_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillA p = 0 := by
  simp [IsRiemannianSubmersion.oneillA, exchangeTensor_fst]

/-- O'Neill's vertical tensor `T` vanishes identically for the first projection of a Riemannian
product. -/
@[simp]
theorem oneillT_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillT p = 0 := by
  simp [IsRiemannianSubmersion.oneillT, exchangeTensor_fst]

end TauCeti

end Product
