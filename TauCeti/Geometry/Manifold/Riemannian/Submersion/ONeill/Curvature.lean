/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's curvature equations for a Riemannian submersion

Let `h : IsRiemannianSubmersion I J f` be a Riemannian submersion `f : M → N` between smooth
Riemannian manifolds, with Levi-Civita connections `∇ := leviCivitaConnection I M` and
`leviCivitaConnection J N`, fundamental tensors `A` and `T`
(`IsRiemannianSubmersion.oneillA` and `IsRiemannianSubmersion.oneillT`), and orthogonal horizontal
and vertical projections `𝓗 := (mfderiv I J f ·).kerᗮ.starProjection` and
`𝓥 := (mfderiv I J f ·).ker.starProjection`. Covariant derivatives of `A` and `T` are formed with
the twice-iterated induced `Hom` connection, ordered with the differentiation direction `w` before
the two tensor slots `u, v`:
`(∇_w A)_u v := ∇.hom (∇.hom ∇) h.oneillA x w u v` and
`(∇_w T)_u v := ∇.hom (∇.hom ∇) h.oneillT x w u v`.

With Lee's curvature sign convention `R(X, Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z` (so the unit
sphere has sectional curvature `+1`), this file establishes O'Neill's curvature and
sectional-curvature equations containing at least one horizontal vector (O'Neill's equations `{1}`,
`{2}`, `{3}`, `{4}` and Corollaries 1–2; the four-vertical fibre Gauss equation `{0}` and vertical
sectional-curvature formula are omitted):

* **Three vertical, one horizontal (`{1}`)**
  (`inner_curvatureTensor_of_mem_ker_of_mem_orthogonal_ker`):
  for vertical `v₁, v₂, v₃` and horizontal `u`,
  `⟪R(v₁, v₂)v₃, u⟫ = ⟪(∇_{v₁} T)_{v₂} v₃, u⟫ - ⟪(∇_{v₂} T)_{v₁} v₃, u⟫`.
* **Two horizontal, two vertical (`{2}`)**
  (`inner_curvatureTensor_horizontal_vertical_vertical_horizontal` and
  `inner_curvatureTensor_horizontal_horizontal_vertical_vertical`):
  for horizontal `u₁, u₂` and vertical `v₁, v₂`,
  `⟪R(u₁, v₁)v₂, u₂⟫ = ⟪(∇_{u₁} T)_{v₁} v₂, u₂⟫ + ⟪(∇_{v₁} A)_{u₁} u₂, v₂⟫ +
    ⟪A_{u₁} v₁, A_{u₂} v₂⟫ - ⟪T_{v₁} u₁, T_{v₂} u₂⟫`, and
  `⟪R(u₁, u₂)v₁, v₂⟫ = ⟪(∇_{u₂} T)_{v₁} v₂, u₁⟫ - ⟪(∇_{u₁} T)_{v₁} v₂, u₂⟫ -
    2⟪(∇_{v₁} A)_{u₁} u₂, v₂⟫ + ⟪A_{u₂} v₁, A_{u₁} v₂⟫ - ⟪A_{u₁} v₁, A_{u₂} v₂⟫ +
    ⟪T_{v₁} u₁, T_{v₂} u₂⟫ - ⟪T_{v₁} u₂, T_{v₂} u₁⟫`.
* **Mixed sectional curvature** (`sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker`):
  for horizontal `u` and vertical `v`,
  `K_M(u, v) = (⟪(∇_u T)_v v, u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² ‖v‖²)`, reducing to
  `‖A_u v‖² / (‖u‖² ‖v‖²) ≥ 0` when `T` vanishes near `x` (totally geodesic fibres).
* **Three horizontal, one vertical (`{3}`)**
  (`inner_curvatureTensor_of_mem_orthogonal_ker_of_mem_ker`):
  for horizontal `u, v, w` and vertical `z`,
  `⟪R(u, v)w, z⟫ = -⟪(∇_w A)_u v, z⟫ - ⟪A_u v, T_z w⟫ + ⟪A_v w, T_z u⟫ + ⟪A_w u, T_z v⟫`.
* **Four horizontal (`{4}`) and horizontal sectional curvature**
  (`starProjection_orthogonal_ker_curvatureTensor_of_mem_orthogonal_ker`,
  `inner_curvatureTensor_of_mem_orthogonal_ker`, and
  `sectionalCurvature_mfderiv_of_mem_orthogonal_ker`):
  for horizontal `u, v, w, z`, `⟪R(u, v)w, z⟫` equals
  `⟪R^N(df u, df v)(df w), df z⟫ + 2⟪A_u v, A_w z⟫ - ⟪A_v w, A_u z⟫ + ⟪A_u w, A_v z⟫`,
  whence `K_N(df u, df v) = K_M(u, v) + 3 ‖A_u v‖² / det(Gram(u, v))` and, on orthonormal
  horizontal fields `X, Y`, `K_N(df X, df Y) = K_M(X, Y) + (3 / 4) ‖𝓥 [X, Y]‖²`. In particular, a
  Riemannian submersion never decreases sectional curvature on horizontal planes, with equality if
  and only if `A_u v = 0`.

Equations involving only `M`'s curvature tensor assume `[T2Space M]` without `[T2Space N]`;
`[T2Space N]` enters only when `N`'s pointwise curvature tensor or sectional curvature is formed.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 1 (`{1}`–`{4}`) and Corollaries 1–2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D (Theorem 9.28b–f and
  Corollary 9.29b–c).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7–8 (sign conventions for curvature and sectional curvature).
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Manifold Set VectorField
open scoped ContDiff InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

section Gram

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f) {x : M}
include h

private theorem det_gram_horizontalLift (a b : TangentSpace J (f x)) :
    (Matrix.gram ℝ ![h.horizontalLift x a, h.horizontalLift x b]).det =
      (Matrix.gram ℝ ![a, b]).det := by
  simp only [Matrix.real_det_gram_fin_two, (h.horizontalLift x).inner_map_map]

private theorem det_gram_mfderiv_of_mem_orthogonal_ker {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (Matrix.gram ℝ ![mfderiv I J f x u, mfderiv I J f x v]).det =
      (Matrix.gram ℝ ![u, v]).det := by
  rw [← h.det_gram_horizontalLift, h.horizontalLift_mfderiv_of_mem x hu,
    h.horizontalLift_mfderiv_of_mem x hv]

end Gram

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

local notation "∇" => leviCivitaConnection I M

-- Regularity conversions used by `mlieBracket` and `IsMetricCompatible`.
local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

/-! ### Local extensions and regularity helpers -/

section LocalHelpers

variable {x : M}
include h

/-- Extend a horizontal vector at `x` to a basic horizontal lift that is smooth on an open
neighbourhood of `x`, without requiring `[T2Space N]`. -/
private theorem exists_contMDiffOn_horizontalLift_eq {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    ∃ (W : Set N) (B : Π z : N, TangentSpace J z),
      IsOpen W ∧ f x ∈ W ∧ CMDiff[W] ∞ (T% B) ∧
      CMDiff[f ⁻¹' W] ∞ (T% (fun y ↦ h.horizontalLift y (B (f y)))) ∧
      h.horizontalLift x (B (f x)) = u := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let : ContMDiffVectorBundle ∞ F (TangentSpace J : N → Type _) J :=
    TangentBundle.contMDiffVectorBundle
  set B : Π z : N, TangentSpace J z := FiberBundle.extend F (mfderiv I J f x u)
  obtain ⟨s, hs, hBs⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) J F (mfderiv I J f x u)
  exact ⟨interior s, B, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
    hBs.mono interior_subset,
    h.contMDiffOn_horizontalLift isOpen_interior (hBs.mono interior_subset) (by simp),
    by simp [B, FiberBundle.extend_apply_self, h.horizontalLift_mfderiv_of_mem x hu]⟩

end LocalHelpers

variable [T2Space M]

section SmoothCovHelpers

variable {x : M}

omit [T2Space M] in
private theorem mdifferentiableAt_leviCivitaConnection_of_contMDiffOn
    {U : Set M} (hUopen : IsOpen U) (hxU : x ∈ U)
    {Y Z : Π y : M, TangentSpace I y}
    (hY : CMDiff[U] ∞ (T% Y)) (hZ : CMDiff[U] ∞ (T% Z)) :
    MDiffAt (T% (fun y ↦ ∇ Y y (Z y))) x := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact (((CovariantDerivative.contMDiffOn_leviCivitaConnection (n := ∞) (m := ∞) (k := ∞)
    hUopen le_rfl le_rfl (by simpa using hY)).clm_bundle_apply hZ).contMDiffAt
    (hUopen.mem_nhds hxU)).mdifferentiableAt (by simp)

end SmoothCovHelpers

/-! ### Three vertical vectors and one horizontal vector -/

section VerticalThree

variable {x : M}
include h

/-- Extend a vertical vector at `x` to a globally smooth vertical vector field on `M`. -/
private theorem exists_contMDiff_mem_ker {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    ∃ V : Π y : M, TangentSpace I y, CMDiff ∞ (T% V) ∧ V x = v ∧
      ∀ y, V y ∈ (mfderiv I J f y).ker := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  obtain ⟨s, hs, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  refine ⟨fun y ↦ (mfderiv I J f y).ker.starProjection (s y),
    (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply hs,
    Submodule.starProjection_eq_self_iff.mpr hv,
    fun _ ↦ Submodule.starProjection_apply_mem _ _⟩

/-- Evaluate `𝓗 (∇_{V₁ x} (∇_{V₂} V₃))` for globally smooth vertical fields `V₁, V₂, V₃`. -/
private theorem starProjection_orthogonal_ker_second_vertical
    {V₁ V₂ V₃ : Π y : M, TangentSpace I y}
    (hV₂ : CMDiff ∞ (T% V₂)) (hV₃ : CMDiff ∞ (T% V₃))
    (hV₁v : ∀ y, V₁ y ∈ (mfderiv I J f y).ker)
    (hV₂v : ∀ y, V₂ y ∈ (mfderiv I J f y).ker)
    (hV₃v : ∀ y, V₃ y ∈ (mfderiv I J f y).ker) :
    (mfderiv I J f x).kerᗮ.starProjection (∇ (fun y ↦ ∇ V₃ y (V₂ y)) x (V₁ x)) =
      (mfderiv I J f x).kerᗮ.starProjection
          (∇.hom (∇.hom ∇) h.oneillT x (V₁ x) (V₂ x) (V₃ x)) +
        h.oneillT x ((mfderiv I J f x).ker.starProjection (∇ V₂ x (V₁ x))) (V₃ x) +
        h.oneillT x (V₂ x) ((mfderiv I J f x).ker.starProjection (∇ V₃ x (V₁ x))) +
        h.oneillT x (V₁ x) ((mfderiv I J f x).ker.starProjection (∇ V₃ x (V₂ x))) := by
  have hW : MDiffAt (T% (fun y ↦ ∇ V₃ y (V₂ y))) x :=
    ((∇.contMDiff_apply hV₂ hV₃) x).mdifferentiableAt (by simp)
  have hPW : (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (∇ V₃ y (V₂ y))) =
      fun y ↦ h.oneillT y (V₂ y) (V₃ y) :=
    funext fun y ↦ h.starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillT_of_mem_ker
      ((hV₃ y).mdifferentiableAt (by simp)) (.of_forall hV₃v) (hV₂v y)
  have hstep := h.starProjection_orthogonal_ker_leviCivitaConnection_of_mem_ker hW (hV₁v x)
  have heval := h.hom_hom_oneillT_apply ((hV₂ x).mdifferentiableAt (by simp))
    ((hV₃ x).mdifferentiableAt (by simp)) (V₁ x)
  have hTcov : ∇ (fun y ↦ h.oneillT y (V₂ y) (V₃ y)) x (V₁ x) =
      ∇.hom (∇.hom ∇) h.oneillT x (V₁ x) (V₂ x) (V₃ x) +
        h.oneillT x (∇ V₂ x (V₁ x)) (V₃ x) +
        h.oneillT x (V₂ x) (∇ V₃ x (V₁ x)) := by
    rw [heval]
    abel
  have hp₁ : (mfderiv I J f x).kerᗮ.starProjection
      (h.oneillT x (∇ V₂ x (V₁ x)) (V₃ x)) =
      h.oneillT x ((mfderiv I J f x).ker.starProjection (∇ V₂ x (V₁ x))) (V₃ x) := by
    rw [← h.oneillT_starProjection_ker,
      Submodule.starProjection_eq_self_iff.mpr
        (h.oneillT_apply_mem_orthogonal_ker _ (hV₃v x))]
  rw [hstep, hPW, hTcov, map_add, map_add, hp₁, h.starProjection_orthogonal_ker_oneillT]

/-- **O'Neill's curvature equation on three vertical vectors (`{1}`, vector form).**
For vertical tangent vectors `v₁, v₂, v₃`, the horizontal component `𝓗 (R(v₁, v₂)v₃)` equals
`𝓗 ((∇_{v₁} T)_{v₂} v₃ - (∇_{v₂} T)_{v₁} v₃)`. -/
theorem starProjection_orthogonal_ker_curvatureTensor_of_mem_ker
    {v₁ v₂ v₃ : TangentSpace I x}
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hv₂ : v₂ ∈ (mfderiv I J f x).ker)
    (hv₃ : v₃ ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection (∇.curvatureTensor x v₁ v₂ v₃) =
      (mfderiv I J f x).kerᗮ.starProjection
        (∇.hom (∇.hom ∇) h.oneillT x v₁ v₂ v₃ -
          ∇.hom (∇.hom ∇) h.oneillT x v₂ v₁ v₃) := by
  obtain ⟨V₁, hV₁, rfl, hV₁v⟩ := h.exists_contMDiff_mem_ker hv₁
  obtain ⟨V₂, hV₂, rfl, hV₂v⟩ := h.exists_contMDiff_mem_ker hv₂
  obtain ⟨V₃, hV₃, rfl, hV₃v⟩ := h.exists_contMDiff_mem_ker hv₃
  -- Evaluate the three terms of `R(V₁, V₂)V₃ = ∇_{V₁} ∇_{V₂} V₃ - ∇_{V₂} ∇_{V₁} V₃ -
  -- ∇_{[V₁, V₂]} V₃`.
  have h₁₂ := h.starProjection_orthogonal_ker_second_vertical hV₂ hV₃ hV₁v hV₂v hV₃v (x := x)
  have h₂₁ := h.starProjection_orthogonal_ker_second_vertical hV₁ hV₃ hV₂v hV₁v hV₃v (x := x)
  have htor := ((CovariantDerivative.torsion_eq_zero_iff ∇).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I))
    ((hV₁ x).mdifferentiableAt (by simp)) ((hV₂ x).mdifferentiableAt (by simp))
  have hbr_mem : mlieBracket I V₁ V₂ x ∈ (mfderiv I J f x).ker :=
    (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv
      (by simp [minSmoothness_of_isRCLikeNormedField])
      ((hV₁ x).mdifferentiableAt (by simp)) ((hV₂ x).mdifferentiableAt (by simp))
      (.of_forall hV₁v) (.of_forall hV₂v)
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (∇ V₃ x (mlieBracket I V₁ V₂ x)) =
      h.oneillT x ((mfderiv I J f x).ker.starProjection (∇ V₂ x (V₁ x))) (V₃ x) -
        h.oneillT x ((mfderiv I J f x).ker.starProjection (∇ V₁ x (V₂ x))) (V₃ x) := by
    rw [h.starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillT_of_mem_ker
        ((hV₃ x).mdifferentiableAt (by simp)) (.of_forall hV₃v) hbr_mem,
      ← htor, ← h.oneillT_starProjection_ker, map_sub, map_sub, sub_apply]
  rw [∇.curvatureTensor_apply x hV₁ hV₂ hV₃, CovariantDerivative.curvatureOperator_apply,
    map_sub, map_sub, h₁₂, h₂₁, hbr, map_sub]
  abel

/-- **O'Neill's curvature equation on three vertical and one horizontal vector (`{1}`).** For
vertical `v₁, v₂, v₃` and horizontal `u`,
`⟪R(v₁, v₂)v₃, u⟫ = ⟪(∇_{v₁} T)_{v₂} v₃, u⟫ - ⟪(∇_{v₂} T)_{v₁} v₃, u⟫`. -/
theorem inner_curvatureTensor_of_mem_ker_of_mem_orthogonal_ker
    {v₁ v₂ v₃ u : TangentSpace I x}
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hv₂ : v₂ ∈ (mfderiv I J f x).ker)
    (hv₃ : v₃ ∈ (mfderiv I J f x).ker) (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    ⟪∇.curvatureTensor x v₁ v₂ v₃, u⟫_ℝ =
      ⟪∇.hom (∇.hom ∇) h.oneillT x v₁ v₂ v₃, u⟫_ℝ -
        ⟪∇.hom (∇.hom ∇) h.oneillT x v₂ v₁ v₃, u⟫_ℝ := by
  rw [← Submodule.starProjection_eq_self_iff.mpr hu,
    ← Submodule.inner_starProjection_left_eq_right,
    h.starProjection_orthogonal_ker_curvatureTensor_of_mem_ker hv₁ hv₂ hv₃,
    Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hu, inner_sub_left]

end VerticalThree

/-! ### Two horizontal and two vertical vectors, and mixed sectional curvature -/

section Mixed

variable {x : M}
include h

private theorem inner_second_cov_vertical_along_horizontal
    {V₁ V₂ : Π y : M, TangentSpace I y}
    (hV₁ : CMDiff ∞ (T% V₁)) (hV₂ : CMDiff ∞ (T% V₂))
    (hV₁v : ∀ y, V₁ y ∈ (mfderiv I J f y).ker)
    (hV₂v : ∀ y, V₂ y ∈ (mfderiv I J f y).ker)
    {u₁ u₂ : TangentSpace I x}
    (hu₁ : u₁ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ) :
    ⟪∇ (fun y ↦ ∇ V₂ y (V₁ y)) x u₁, u₂⟫_ℝ =
      ⟪∇.hom (∇.hom ∇) h.oneillT x u₁ (V₁ x) (V₂ x), u₂⟫_ℝ +
        ⟪h.oneillT x ((mfderiv I J f x).ker.starProjection (∇ V₁ x u₁)) (V₂ x), u₂⟫_ℝ +
        ⟪h.oneillT x (V₁ x) ((mfderiv I J f x).ker.starProjection (∇ V₂ x u₁)), u₂⟫_ℝ +
        ⟪h.oneillA x u₁ ((mfderiv I J f x).ker.starProjection (∇ V₂ x (V₁ x))), u₂⟫_ℝ := by
  have hW : MDiffAt (T% (fun y ↦ ∇ V₂ y (V₁ y))) x :=
    ((∇.contMDiff_apply hV₁ hV₂) x).mdifferentiableAt (by simp)
  have hPW : (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (∇ V₂ y (V₁ y))) =
      fun y ↦ h.oneillT y (V₁ y) (V₂ y) :=
    funext fun y ↦ h.starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillT_of_mem_ker
      ((hV₂ y).mdifferentiableAt (by simp)) (.of_forall hV₂v) (hV₁v y)
  have hstep := h.starProjection_orthogonal_ker_leviCivitaConnection_of_mem_orthogonal_ker hW hu₁
  have heval := h.hom_hom_oneillT_apply ((hV₁ x).mdifferentiableAt (by simp))
    ((hV₂ x).mdifferentiableAt (by simp)) u₁
  have hTcov : ∇ (fun y ↦ h.oneillT y (V₁ y) (V₂ y)) x u₁ =
      ∇.hom (∇.hom ∇) h.oneillT x u₁ (V₁ x) (V₂ x) +
        h.oneillT x (∇ V₁ x u₁) (V₂ x) + h.oneillT x (V₁ x) (∇ V₂ x u₁) := by
    rw [heval]
    abel
  conv_lhs =>
    rw [← Submodule.starProjection_eq_self_iff.mpr hu₂,
      ← Submodule.inner_starProjection_left_eq_right]
  rw [hstep, hPW, inner_add_left, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hu₂, hTcov, inner_add_left, inner_add_left,
    ← h.oneillT_starProjection_ker x (∇ V₁ x u₁),
    ← h.inner_oneillT_starProjection_ker_of_mem_orthogonal_ker (V₁ x) (∇ V₂ x u₁) hu₂]

private theorem inner_second_cov_vertical_along_basic_horizontal
    {W : Set N} (hWopen : IsOpen W) (hfxW : f x ∈ W)
    {B₁ : Π z : N, TangentSpace J z} (hB₁W : CMDiff[W] ∞ (T% B₁))
    {V₂ : Π y : M, TangentSpace I y} (hV₂ : CMDiff ∞ (T% V₂))
    (hV₂v : ∀ y, V₂ y ∈ (mfderiv I J f y).ker)
    {v₁ u₂ : TangentSpace I x}
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ) :
    let X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
    ⟪∇ (fun y ↦ ∇ V₂ y (X₁ y)) x v₁, u₂⟫_ℝ =
      -⟪∇.hom (∇.hom ∇) h.oneillA x v₁ (X₁ x) u₂, V₂ x⟫_ℝ -
        ⟪h.oneillA x (X₁ x) v₁, h.oneillA x u₂ (V₂ x)⟫_ℝ +
        ⟪h.oneillA x (X₁ x) ((mfderiv I J f x).ker.starProjection (∇ V₂ x v₁)), u₂⟫_ℝ +
        ⟪h.oneillT x v₁ ((mfderiv I J f x).ker.starProjection (∇ V₂ x (X₁ x))), u₂⟫_ℝ := by
  intro X₁
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hUopen : IsOpen (f ⁻¹' W) := hWopen.preimage h.isSubmersion.contMDiff.continuous
  have hX₁U : CMDiff[f ⁻¹' W] ∞ (T% X₁) := h.contMDiffOn_horizontalLift hWopen hB₁W (by simp)
  have hX₁d : MDiffAt (T% X₁) x :=
    (hX₁U.contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp)
  have hV₂X₁d : MDiffAt (T% (fun y ↦ ∇ V₂ y (X₁ y))) x :=
    mdifferentiableAt_leviCivitaConnection_of_contMDiffOn hUopen hfxW
      (hV₂.contMDiffOn.mono (subset_univ _)) hX₁U
  -- Project `∇_{v₁} ∇_{X₁} V₂` horizontally via `𝓗 (∇_{X₁} V₂) = A_{X₁} V₂`.
  have hPW : (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (∇ V₂ y (X₁ y))) =
      fun y ↦ h.oneillA y (X₁ y) (V₂ y) :=
    funext fun y ↦
      h.starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillA_of_mem_orthogonal_ker
        ((hV₂ y).mdifferentiableAt (by simp)) (.of_forall hV₂v)
        (h.horizontalLift_mem_orthogonal_ker y _)
  have hstep := h.starProjection_orthogonal_ker_leviCivitaConnection_of_mem_ker hV₂X₁d hv₁
  have heval := h.hom_hom_oneillA_apply hX₁d ((hV₂ x).mdifferentiableAt (by simp)) v₁
  have hAcov : ∇ (fun y ↦ h.oneillA y (X₁ y) (V₂ y)) x v₁ =
      ∇.hom (∇.hom ∇) h.oneillA x v₁ (X₁ x) (V₂ x) +
        h.oneillA x (∇ X₁ x v₁) (V₂ x) + h.oneillA x (X₁ x) (∇ V₂ x v₁) := by
    rw [heval]
    abel
  -- Expand `A_{∇_{v₁} X₁} V₂` using `∇_{v₁} X₁ = A_{X₁} v₁ + T_{v₁} X₁` and skew-adjointness.
  have hX₁v₁ := h.leviCivitaConnection_horizontalLift_of_mem_ker
    ((hB₁W.contMDiffAt (hWopen.mem_nhds hfxW)).of_le (by simp)) hv₁
  have hAA : ⟪h.oneillA x (∇ X₁ x v₁) (V₂ x), u₂⟫_ℝ =
      -⟪h.oneillA x (X₁ x) v₁, h.oneillA x u₂ (V₂ x)⟫_ℝ := by
    rw [hX₁v₁, map_add, add_apply,
      h.oneillA_eq_zero_of_mem_ker
        (h.oneillT_apply_mem_ker v₁ (h.horizontalLift_mem_orthogonal_ker x _)),
      zero_apply, add_zero, h.inner_oneillA,
      h.oneillA_antisymm (h.oneillA_apply_mem_orthogonal_ker (X₁ x) hv₁) hu₂,
      inner_neg_right, neg_neg, real_inner_comm (h.oneillA x u₂ (V₂ x)),
      h.inner_oneillA, neg_neg]
  conv_lhs =>
    rw [← Submodule.starProjection_eq_self_iff.mpr hu₂,
      ← Submodule.inner_starProjection_left_eq_right]
  rw [hstep, hPW, inner_add_left, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hu₂, hAcov, inner_add_left, inner_add_left,
    h.inner_hom_hom_oneillA x, real_inner_comm (V₂ x), hAA,
    ← h.inner_oneillA_starProjection_ker_of_mem_orthogonal_ker (X₁ x) (∇ V₂ x v₁) hu₂]
  ring

/-- **O'Neill's mixed curvature equation (`{2}`, `⟪R(u₁, v₁)v₂, u₂⟫`).** For horizontal `u₁, u₂`
and vertical `v₁, v₂`, `⟪R(u₁, v₁)v₂, u₂⟫` equals
`⟪(∇_{u₁} T)_{v₁} v₂, u₂⟫ + ⟪(∇_{v₁} A)_{u₁} u₂, v₂⟫ + ⟪A_{u₁} v₁, A_{u₂} v₂⟫`
minus `⟪T_{v₁} u₁, T_{v₂} u₂⟫`. -/
theorem inner_curvatureTensor_horizontal_vertical_vertical_horizontal
    {u₁ u₂ v₁ v₂ : TangentSpace I x}
    (hu₁ : u₁ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ)
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hv₂ : v₂ ∈ (mfderiv I J f x).ker) :
    ⟪∇.curvatureTensor x u₁ v₁ v₂, u₂⟫_ℝ =
      ⟪∇.hom (∇.hom ∇) h.oneillT x u₁ v₁ v₂, u₂⟫_ℝ +
        ⟪∇.hom (∇.hom ∇) h.oneillA x v₁ u₁ u₂, v₂⟫_ℝ +
        ⟪h.oneillA x u₁ v₁, h.oneillA x u₂ v₂⟫_ℝ -
        ⟪h.oneillT x v₁ u₁, h.oneillT x v₂ u₂⟫_ℝ := by
  obtain ⟨W, B₁, hWopen, hfxW, hB₁W, hX₁U, hX₁x⟩ := h.exists_contMDiffOn_horizontalLift_eq hu₁
  obtain ⟨V₁, hV₁, rfl, hV₁v⟩ := h.exists_contMDiff_mem_ker hv₁
  obtain ⟨V₂, hV₂, rfl, hV₂v⟩ := h.exists_contMDiff_mem_ker hv₂
  set X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
  have hX₁x' : X₁ x = u₁ := hX₁x
  have hUopen : IsOpen (f ⁻¹' W) := hWopen.preimage h.isSubmersion.contMDiff.continuous
  have hcurv : ∇.curvatureTensor x u₁ (V₁ x) (V₂ x) = ∇.curvatureOperator X₁ V₁ V₂ x := by
    rw [← hX₁x]
    exact ∇.curvatureTensor_apply_of_contMDiffOn x hUopen hfxW hX₁U hV₁.contMDiffOn
      hV₂.contMDiffOn
  -- `ht₁`, `ht₂`, `ht₃` evaluate `∇_{X₁} ∇_{V₁} V₂`, `∇_{V₁} ∇_{X₁} V₂`, and `∇_{[X₁, V₁]} V₂`.
  have ht₁ := h.inner_second_cov_vertical_along_horizontal hV₁ hV₂ hV₁v hV₂v hu₁ hu₂
  have ht₂ := h.inner_second_cov_vertical_along_basic_horizontal hWopen hfxW hB₁W hV₂ hV₂v hv₁ hu₂
  have hbr := h.mlieBracket_horizontalLift_of_eventually_mem_ker
    ((hB₁W.contMDiffAt (hWopen.mem_nhds hfxW)).of_le (by simp))
    ((hV₁ x).mdifferentiableAt (by simp)) (.of_forall hV₁v)
  have hbr_mem : mlieBracket I X₁ V₁ x ∈ (mfderiv I J f x).ker := by
    rw [hbr]
    exact sub_mem (Submodule.starProjection_apply_mem _ _)
      (h.oneillT_apply_mem_ker (V₁ x) (h.horizontalLift_mem_orthogonal_ker x _))
  have ht₃ : ⟪∇ V₂ x (mlieBracket I X₁ V₁ x), u₂⟫_ℝ =
      ⟪h.oneillT x ((mfderiv I J f x).ker.starProjection (∇ V₁ x u₁)) (V₂ x), u₂⟫_ℝ +
        ⟪h.oneillT x (V₁ x) u₁, h.oneillT x (V₂ x) u₂⟫_ℝ := by
    have hTT : ⟪h.oneillT x (h.oneillT x (V₁ x) u₁) (V₂ x), u₂⟫_ℝ =
        -⟪h.oneillT x (V₁ x) u₁, h.oneillT x (V₂ x) u₂⟫_ℝ := by
      rw [h.oneillT_comm (h.oneillT_apply_mem_ker (V₁ x) hu₁) hv₂, h.inner_oneillT]
    conv_lhs =>
      rw [← Submodule.starProjection_eq_self_iff.mpr hu₂,
        ← Submodule.inner_starProjection_left_eq_right]
    rw [h.starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillT_of_mem_ker
        ((hV₂ x).mdifferentiableAt (by simp)) (.of_forall hV₂v) hbr_mem,
      hbr, hX₁x, map_sub, sub_apply, inner_sub_left, hTT, sub_neg_eq_add]
  dsimp only at ht₂
  rw [hX₁x] at ht₂
  rw [hcurv, CovariantDerivative.curvatureOperator_apply, hX₁x', inner_sub_left, inner_sub_left,
    ht₁, ht₂, ht₃]
  linarith

/-- **O'Neill's companion mixed curvature equation (`{2}`, `⟪R(u₁, u₂)v₁, v₂⟫`).** For horizontal
`u₁, u₂` and vertical `v₁, v₂`,
`⟪R(u₁, u₂)v₁, v₂⟫ = ⟪(∇_{u₂} T)_{v₁} v₂, u₁⟫ - ⟪(∇_{u₁} T)_{v₁} v₂, u₂⟫ -
  2⟪(∇_{v₁} A)_{u₁} u₂, v₂⟫ + ⟪A_{u₂} v₁, A_{u₁} v₂⟫ - ⟪A_{u₁} v₁, A_{u₂} v₂⟫ +
  ⟪T_{v₁} u₁, T_{v₂} u₂⟫ - ⟪T_{v₁} u₂, T_{v₂} u₁⟫`. -/
theorem inner_curvatureTensor_horizontal_horizontal_vertical_vertical
    {u₁ u₂ v₁ v₂ : TangentSpace I x}
    (hu₁ : u₁ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ)
    (hv₁ : v₁ ∈ (mfderiv I J f x).ker) (hv₂ : v₂ ∈ (mfderiv I J f x).ker) :
    ⟪∇.curvatureTensor x u₁ u₂ v₁, v₂⟫_ℝ =
      ⟪∇.hom (∇.hom ∇) h.oneillT x u₂ v₁ v₂, u₁⟫_ℝ -
        ⟪∇.hom (∇.hom ∇) h.oneillT x u₁ v₁ v₂, u₂⟫_ℝ -
        2 * ⟪∇.hom (∇.hom ∇) h.oneillA x v₁ u₁ u₂, v₂⟫_ℝ +
        ⟪h.oneillA x u₂ v₁, h.oneillA x u₁ v₂⟫_ℝ -
        ⟪h.oneillA x u₁ v₁, h.oneillA x u₂ v₂⟫_ℝ +
        ⟪h.oneillT x v₁ u₁, h.oneillT x v₂ u₂⟫_ℝ -
        ⟪h.oneillT x v₁ u₂, h.oneillT x v₂ u₁⟫_ℝ := by
  -- Combine the first Bianchi identity on `(u₁, u₂, v₁)` with the `{2}` formula and the
  -- alternating property of `𝓥 ((∇_{v₁} A)_{u₁} u₂)`.
  have hmetric := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hbianchi := congrArg (fun q ↦ ⟪q, v₂⟫_ℝ)
    (∇.curvatureTensor_cyclic_eq_zero (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)
      x u₁ u₂ v₁)
  simp only [inner_add_left, inner_zero_left] at hbianchi
  have hs₁ : ⟪∇.curvatureTensor x u₂ v₁ u₁, v₂⟫_ℝ =
      -⟪∇.curvatureTensor x u₂ v₁ v₂, u₁⟫_ℝ := by
    rw [hmetric.inner_curvatureTensor_eq_neg, real_inner_comm]
  have hs₂ : ⟪∇.curvatureTensor x v₁ u₁ u₂, v₂⟫_ℝ =
      ⟪∇.curvatureTensor x u₁ v₁ v₂, u₂⟫_ℝ := by
    rw [∇.curvatureTensor_antisymm x v₁ u₁, LinearMap.neg_apply, inner_neg_left,
      hmetric.inner_curvatureTensor_eq_neg, neg_neg, real_inner_comm]
  have hAalt := h.inner_hom_hom_oneillA_antisymm_of_mem_orthogonal_ker_of_mem_ker v₁ hu₂ hu₁ hv₂
  rw [hs₁, hs₂,
    h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hu₂ hu₁ hv₁ hv₂,
    h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hu₁ hu₂ hv₁ hv₂,
    hAalt] at hbianchi
  linarith

/-- Specialization of O'Neill's mixed curvature equation to the sectional-curvature numerator
`⟪R(u, v)v, u⟫` of a horizontal vector `u` and a vertical vector `v`. -/
theorem inner_curvatureTensor_self_of_mem_orthogonal_ker_of_mem_ker
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    ⟪∇.curvatureTensor x u v v, u⟫_ℝ =
      ⟪∇.hom (∇.hom ∇) h.oneillT x u v v, u⟫_ℝ +
        ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2 := by
  rw [h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hu hu hv hv,
    h.inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker v hu hv,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, add_zero]

/-- **O'Neill's mixed sectional curvature formula.** For a horizontal vector `u` and a vertical
vector `v`,
`K_M(u, v) = (⟪(∇_u T)_v v, u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² ‖v‖²)`.
When either vector is zero, both sides vanish by the totalized quotient convention. -/
theorem sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    ∇.sectionalCurvature (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v =
      (⟪∇.hom (∇.hom ∇) h.oneillT x u v v, u⟫_ℝ +
        ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2) / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  rw [CovariantDerivative.sectionalCurvature_apply,
    h.inner_curvatureTensor_self_of_mem_orthogonal_ker_of_mem_ker hu hv,
    Matrix.real_det_gram_fin_two, Submodule.inner_left_of_mem_orthogonal hv hu,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, zero_pow two_ne_zero, sub_zero]

/-- When O'Neill's vertical tensor `T` vanishes in a neighbourhood of `x` (totally geodesic fibres
near `x`), the sectional curvature of a mixed horizontal-vertical plane at `x` is
`‖A_u v‖² / (‖u‖² ‖v‖²)`. -/
theorem sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    ∇.sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v =
      ‖h.oneillA x u v‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  have hcovT : ∇.hom (∇.hom ∇) h.oneillT x = 0 := by
    rw [(∇.hom (∇.hom ∇)).isCovariantDerivativeOnUniv.congr_of_eventuallyEq (σ' := 0)
        h.mdifferentiableAt_oneillT (mdifferentiableAt_zeroSection ℝ _) univ_mem hT,
      (∇.hom (∇.hom ∇)).zero, Pi.zero_apply]
  rw [h.sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker hu hv, hcovT, hT.self_of_nhds]
  simp

/-- When O'Neill's vertical tensor `T` vanishes near `x`, every mixed horizontal-vertical plane at
`x` has nonnegative sectional curvature. -/
theorem sectionalCurvature_nonneg_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    0 ≤ ∇.sectionalCurvature
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v := by
  rw [h.sectionalCurvature_of_mem_orthogonal_ker_of_mem_ker_of_eventually_oneillT_eq_zero hT hu hv]
  positivity

end Mixed

/-! ### Three horizontal vectors and one vertical vector -/

section HorizontalThree

variable {x : M}
include h

private theorem inner_second_cov_basic_horizontal_along_vertical_along_horizontal
    {W : Set N} (hWopen : IsOpen W) (hfxW : f x ∈ W)
    {B₁ : Π z : N, TangentSpace J z} (hB₁W : CMDiff[W] ∞ (T% B₁))
    {V : Π y : M, TangentSpace I y} (hV : CMDiff ∞ (T% V))
    (hVv : ∀ y, V y ∈ (mfderiv I J f y).ker)
    {u₃ u₂ : TangentSpace I x}
    (hu₃ : u₃ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ) :
    let X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
    ⟪∇ (fun y ↦ ∇ X₁ y (V y)) x u₃, u₂⟫_ℝ =
      -⟪∇.hom (∇.hom ∇) h.oneillA x u₃ (X₁ x) u₂, V x⟫_ℝ -
        ⟪V x, h.oneillA x
          (h.horizontalLift x (leviCivitaConnection J N B₁ (f x) (mfderiv I J f x u₃))) u₂⟫_ℝ +
        ⟪h.oneillA x (X₁ x) ((mfderiv I J f x).ker.starProjection (∇ V x u₃)), u₂⟫_ℝ +
        ⟪h.oneillA x u₂ u₃, h.oneillT x (V x) (X₁ x)⟫_ℝ := by
  intro X₁
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hUopen : IsOpen (f ⁻¹' W) := hWopen.preimage h.isSubmersion.contMDiff.continuous
  have hX₁U : CMDiff[f ⁻¹' W] ∞ (T% X₁) := h.contMDiffOn_horizontalLift hWopen hB₁W (by simp)
  have hX₁d : MDiffAt (T% X₁) x :=
    (hX₁U.contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp)
  have hVd : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hAd : MDiffAt (T% (fun y ↦ h.oneillA y (X₁ y) (V y))) x :=
    (h.mdifferentiableAt_oneillA.clm_bundle_apply hX₁d).clm_bundle_apply hVd
  have hTd : MDiffAt (T% (fun y ↦ h.oneillT y (V y) (X₁ y))) x :=
    (h.mdifferentiableAt_oneillT.clm_bundle_apply hVd).clm_bundle_apply hX₁d
  have hX₁Vd : MDiffAt (T% (fun y ↦ ∇ X₁ y (V y))) x :=
    mdifferentiableAt_leviCivitaConnection_of_contMDiffOn hUopen hfxW hX₁U
      (hV.contMDiffOn.mono (subset_univ _))
  -- Near `x`, rewrite `∇_V X₁ = A_{X₁} V + T_V X₁` and differentiate along `u₃`.
  have heqU : (fun y ↦ ∇ X₁ y (V y)) =ᶠ[𝓝 x]
      (fun y ↦ h.oneillA y (X₁ y) (V y)) + fun y ↦ h.oneillT y (V y) (X₁ y) := by
    filter_upwards [hUopen.mem_nhds hfxW] with y hy
    exact h.leviCivitaConnection_horizontalLift_of_mem_ker
      ((hB₁W.contMDiffAt (hWopen.mem_nhds hy)).of_le (by simp)) (hVv y)
  have hcongr := ∇.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hX₁Vd (mdifferentiableAt_add_section hAd hTd) univ_mem heqU
  have hAcov : ∇ (fun y ↦ h.oneillA y (X₁ y) (V y)) x u₃ =
      ∇.hom (∇.hom ∇) h.oneillA x u₃ (X₁ x) (V x) +
        h.oneillA x (∇ X₁ x u₃) (V x) + h.oneillA x (X₁ x) (∇ V x u₃) := by
    rw [h.hom_hom_oneillA_apply hX₁d hVd u₃]
    abel
  -- Simplify `A_{∇_{u₃} X₁} V` and `⟪∇_{u₃} (T_V X₁), u₂⟫`.
  have hX₁u₃ := h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
    ((hB₁W.contMDiffAt (hWopen.mem_nhds hfxW)).of_le (by simp)) hu₃
  have hA_X₁u₃ : ⟪h.oneillA x (∇ X₁ x u₃) (V x), u₂⟫_ℝ =
      -⟪V x, h.oneillA x
        (h.horizontalLift x (leviCivitaConnection J N B₁ (f x) (mfderiv I J f x u₃))) u₂⟫_ℝ := by
    rw [hX₁u₃, map_add, add_apply,
      h.oneillA_eq_zero_of_mem_ker
        (h.oneillA_apply_mem_ker u₃ (h.horizontalLift_mem_orthogonal_ker x _)),
      zero_apply, add_zero, h.inner_oneillA]
  have hTcov : ⟪∇ (fun y ↦ h.oneillT y (V y) (X₁ y)) x u₃, u₂⟫_ℝ =
      ⟪h.oneillA x u₂ u₃, h.oneillT x (V x) (X₁ x)⟫_ℝ := by
    conv_lhs =>
      rw [← Submodule.starProjection_eq_self_iff.mpr hu₂,
        ← Submodule.inner_starProjection_left_eq_right]
    rw [h.starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillA_of_mem_orthogonal_ker hTd
        (.of_forall fun y ↦ h.oneillT_apply_mem_ker (V y) (h.horizontalLift_mem_orthogonal_ker y _))
        hu₃,
      h.inner_oneillA, h.oneillA_antisymm hu₃ hu₂, inner_neg_right, neg_neg, real_inner_comm]
  rw [hcongr, ∇.isCovariantDerivativeOnUniv.add hAd hTd, add_apply,
    inner_add_left, hAcov, inner_add_left, inner_add_left,
    h.inner_hom_hom_oneillA x, real_inner_comm (V x), hA_X₁u₃,
    ← h.inner_oneillA_starProjection_ker_of_mem_orthogonal_ker (X₁ x) (∇ V x u₃) hu₂, hTcov]
  ring

private theorem inner_second_cov_basic_horizontal_along_horizontal_along_vertical
    {W : Set N} (hWopen : IsOpen W) (hfxW : f x ∈ W)
    {B₁ B₃ : Π z : N, TangentSpace J z}
    (hB₁W : CMDiff[W] ∞ (T% B₁)) (hB₃W : CMDiff[W] ∞ (T% B₃))
    {v u₂ : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ) :
    let X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
    let X₃ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₃ (f y))
    ⟪∇ (fun y ↦ ∇ X₁ y (X₃ y)) x v, u₂⟫_ℝ =
      -⟪v, h.oneillA x (h.horizontalLift x (leviCivitaConnection J N B₁ (f x) (B₃ (f x)))) u₂⟫_ℝ -
        ⟪h.oneillA x (X₃ x) (X₁ x), h.oneillT x v u₂⟫_ℝ := by
  intro X₁ X₃
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  have hUopen : IsOpen (f ⁻¹' W) := hWopen.preimage h.isSubmersion.contMDiff.continuous
  have hX₁U : CMDiff[f ⁻¹' W] ∞ (T% X₁) := h.contMDiffOn_horizontalLift hWopen hB₁W (by simp)
  have hX₃U : CMDiff[f ⁻¹' W] ∞ (T% X₃) := h.contMDiffOn_horizontalLift hWopen hB₃W (by simp)
  have hB₁₃W : CMDiff[W] ∞ (T% (fun z ↦ leviCivitaConnection J N B₁ z (B₃ z))) :=
    (CovariantDerivative.contMDiffOn_leviCivitaConnection (n := ∞) (m := ∞) (k := ∞)
      hWopen le_rfl le_rfl (by simpa using hB₁W)).clm_bundle_apply hB₃W
  have hL₁₃d :
      MDiffAt (T% (fun y ↦ h.horizontalLift y (leviCivitaConnection J N B₁ (f y) (B₃ (f y))))) x :=
    (h.contMDiffAt_horizontalLift (hB₁₃W.contMDiffAt (hWopen.mem_nhds hfxW))
      (by simp)).mdifferentiableAt (by simp)
  have hAd : MDiffAt (T% (fun y ↦ h.oneillA y (X₃ y) (X₁ y))) x :=
    (h.mdifferentiableAt_oneillA.clm_bundle_apply
      ((hX₃U.contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp))).clm_bundle_apply
      ((hX₁U.contMDiffAt (hUopen.mem_nhds hfxW)).mdifferentiableAt (by simp))
  have hX₁₃d : MDiffAt (T% (fun y ↦ ∇ X₁ y (X₃ y))) x :=
    mdifferentiableAt_leviCivitaConnection_of_contMDiffOn hUopen hfxW hX₁U hX₃U
  have heqU : (fun y ↦ ∇ X₁ y (X₃ y)) =ᶠ[𝓝 x]
      (fun y ↦ h.horizontalLift y (leviCivitaConnection J N B₁ (f y) (B₃ (f y)))) +
        fun y ↦ h.oneillA y (X₃ y) (X₁ y) := by
    filter_upwards [hUopen.mem_nhds hfxW] with y hy
    have hstep := h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
      ((hB₁W.contMDiffAt (hWopen.mem_nhds hy)).of_le (by simp))
      (h.horizontalLift_mem_orthogonal_ker y (B₃ (f y)))
    rw [h.mfderiv_horizontalLift] at hstep
    exact hstep
  have hcongr := ∇.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hX₁₃d (mdifferentiableAt_add_section hL₁₃d hAd) univ_mem heqU
  have hLpart := h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
    (B := fun z ↦ leviCivitaConnection J N B₁ z (B₃ z))
    ((hB₁₃W.contMDiffAt (hWopen.mem_nhds hfxW)).of_le (by simp)) hv
  have hApart := h.starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillT_of_mem_ker hAd
    (.of_forall fun y ↦ h.oneillA_apply_mem_ker (X₃ y) (h.horizontalLift_mem_orthogonal_ker y _)) hv
  rw [hcongr, ∇.isCovariantDerivativeOnUniv.add hL₁₃d hAd, add_apply]
  conv_lhs =>
    rw [← Submodule.starProjection_eq_self_iff.mpr hu₂,
      ← Submodule.inner_starProjection_left_eq_right]
  rw [map_add, hLpart, hApart, inner_add_left, h.inner_oneillA, h.inner_oneillT]
  ring

/-- **O'Neill's curvature equation on three horizontal and one vertical vector (`{3}`).** For
horizontal `u, v, w` and vertical `z`,
`⟪R(u, v)w, z⟫ = -⟪(∇_w A)_u v, z⟫ - ⟪A_u v, T_z w⟫ + ⟪A_v w, T_z u⟫ + ⟪A_w u, T_z v⟫`. -/
theorem inner_curvatureTensor_of_mem_orthogonal_ker_of_mem_ker
    {u v w z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).ker) :
    ⟪∇.curvatureTensor x u v w, z⟫_ℝ =
      -⟪∇.hom (∇.hom ∇) h.oneillA x w u v, z⟫_ℝ -
        ⟪h.oneillA x u v, h.oneillT x z w⟫_ℝ +
        ⟪h.oneillA x v w, h.oneillT x z u⟫_ℝ +
        ⟪h.oneillA x w u, h.oneillT x z v⟫_ℝ := by
  -- Swap pairs to `⟪R(w, z)u, v⟫` so only one vertical extension and two local basic horizontal
  -- extensions are differentiated.
  have hswap := (CovariantDerivative.isMetricCompatible_leviCivitaConnection
    (I := I) (M := M)).inner_curvatureTensor_swap_pairs
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) x u v w z
  obtain ⟨W₁, B₁, hW₁, hfxW₁, hB₁, hX₁U₁, hX₁x⟩ := h.exists_contMDiffOn_horizontalLift_eq hu
  obtain ⟨W₃, B₃, hW₃, hfxW₃, hB₃, hX₃U₃, hX₃x⟩ := h.exists_contMDiffOn_horizontalLift_eq hw
  obtain ⟨V, hV, rfl, hVv⟩ := h.exists_contMDiff_mem_ker hz
  set W : Set N := W₁ ∩ W₃
  have hWopen : IsOpen W := hW₁.inter hW₃
  have hfxW : f x ∈ W := ⟨hfxW₁, hfxW₃⟩
  have hUopen : IsOpen (f ⁻¹' W) := hWopen.preimage h.isSubmersion.contMDiff.continuous
  set X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
  set X₃ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₃ (f y))
  have hX₃x' : X₃ x = w := hX₃x
  have hcurv : ∇.curvatureTensor x w (V x) u = ∇.curvatureOperator X₃ V X₁ x := by
    rw [← hX₃x, ← hX₁x]
    exact ∇.curvatureTensor_apply_of_contMDiffOn x hUopen hfxW
      (hX₃U₃.mono (preimage_mono inter_subset_right)) hV.contMDiffOn
      (hX₁U₁.mono (preimage_mono inter_subset_left))
  -- `ht₁`, `ht₂`, `ht₃` evaluate `∇_{X₃} ∇_V X₁`, `∇_V ∇_{X₃} X₁`, and `∇_{[X₃, V]} X₁`.
  have ht₁ := h.inner_second_cov_basic_horizontal_along_vertical_along_horizontal hWopen hfxW
    (hB₁.mono inter_subset_left) hV hVv hw hv
  have ht₂ := h.inner_second_cov_basic_horizontal_along_horizontal_along_vertical hWopen hfxW
    (hB₁.mono inter_subset_left) (hB₃.mono inter_subset_right) hz hv
  have hdfw : B₃ (f x) = mfderiv I J f x w := by
    rw [← hX₃x, h.mfderiv_horizontalLift]
  have hbr := h.mlieBracket_horizontalLift_of_eventually_mem_ker
    ((hB₃.contMDiffAt (hW₃.mem_nhds hfxW₃)).of_le (by simp))
    ((hV x).mdifferentiableAt (by simp)) (.of_forall hVv)
  have hbr_mem : mlieBracket I X₃ V x ∈ (mfderiv I J f x).ker := by
    rw [hbr]
    exact sub_mem (Submodule.starProjection_apply_mem _ _)
      (h.oneillT_apply_mem_ker (V x) (h.horizontalLift_mem_orthogonal_ker x _))
  have ht₃ : ⟪∇ X₁ x (mlieBracket I X₃ V x), v⟫_ℝ =
      ⟪h.oneillA x u ((mfderiv I J f x).ker.starProjection (∇ V x w)), v⟫_ℝ +
        ⟪h.oneillA x u v, h.oneillT x (V x) w⟫_ℝ := by
    have hAX₁ := h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
      ((hB₁.contMDiffAt (hW₁.mem_nhds hfxW₁)).of_le (by simp)) hbr_mem
    have hAT : ⟪h.oneillA x u (h.oneillT x (V x) w), v⟫_ℝ =
        -⟪h.oneillA x u v, h.oneillT x (V x) w⟫_ℝ := by
      rw [h.inner_oneillA, real_inner_comm]
    conv_lhs =>
      rw [← Submodule.starProjection_eq_self_iff.mpr hv,
        ← Submodule.inner_starProjection_left_eq_right]
    rw [hAX₁, hbr, hX₁x, hX₃x, map_sub,
      inner_sub_left, hAT, sub_neg_eq_add]
  dsimp only at ht₁ ht₂
  rw [hX₁x] at ht₁
  rw [hX₁x, hX₃x, hdfw] at ht₂
  rw [hswap, hcurv, CovariantDerivative.curvatureOperator_apply, hX₃x',
    inner_sub_left, inner_sub_left, ht₁, ht₂, ht₃]
  linarith

end HorizontalThree

/-! ### Four horizontal vectors and horizontal sectional curvature -/

section HorizontalFour

variable {x : M}
include h

private theorem starProjection_orthogonal_ker_second_basic_horizontal
    (B₁ : Π z : N, TangentSpace J z) {B₂ Bw : Π z : N, TangentSpace J z}
    (hB₂ : CMDiff ∞ (T% B₂)) (hBw : CMDiff ∞ (T% Bw)) :
    let U₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
    let U₂ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₂ (f y))
    let Z : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Bw (f y))
    (mfderiv I J f x).kerᗮ.starProjection (∇ (fun y ↦ ∇ Z y (U₂ y)) x (U₁ x)) =
      h.horizontalLift x
          (leviCivitaConnection J N (fun z ↦ leviCivitaConnection J N Bw z (B₂ z)) (f x)
            (B₁ (f x))) +
        h.oneillA x (U₁ x) (h.oneillA x (U₂ x) (Z x)) := by
  intro U₁ U₂ Z
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  have hU₂ : CMDiff ∞ (T% U₂) := h.contMDiff_horizontalLift hB₂ (by simp)
  have hZ : CMDiff ∞ (T% Z) := h.contMDiff_horizontalLift hBw (by simp)
  have hBw₂ : CMDiff ∞ (T% (fun z ↦ leviCivitaConnection J N Bw z (B₂ z))) :=
    (leviCivitaConnection J N).contMDiff_apply hB₂ hBw
  have hL :
      CMDiff ∞ (T% (fun y ↦ h.horizontalLift y (leviCivitaConnection J N Bw (f y) (B₂ (f y))))) :=
    h.contMDiff_horizontalLift hBw₂ (by simp)
  have hA : MDiffAt (T% (fun y ↦ h.oneillA y (U₂ y) (Z y))) x :=
    (h.mdifferentiableAt_oneillA.clm_bundle_apply
      ((hU₂ x).mdifferentiableAt (by simp))).clm_bundle_apply ((hZ x).mdifferentiableAt (by simp))
  have hsplit : (fun y ↦ ∇ Z y (U₂ y)) =
      (fun y ↦ h.horizontalLift y (leviCivitaConnection J N Bw (f y) (B₂ (f y)))) +
        fun y ↦ h.oneillA y (U₂ y) (Z y) := by
    funext y
    have hstep := h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
      ((hBw (f y)).of_le (by simp)) (h.horizontalLift_mem_orthogonal_ker y (B₂ (f y)))
    rw [h.mfderiv_horizontalLift] at hstep
    exact hstep
  have hAterm :=
    h.starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillA_of_mem_orthogonal_ker
      hA (.of_forall fun y ↦ h.oneillA_apply_mem_ker (U₂ y)
        (h.horizontalLift_mem_orthogonal_ker y (Bw (f y))))
      (h.horizontalLift_mem_orthogonal_ker x (B₁ (f x)))
  rw [hsplit, ∇.isCovariantDerivativeOnUniv.add ((hL x).mdifferentiableAt (by simp)) hA,
    add_apply, map_add,
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
      (Y := fun z ↦ leviCivitaConnection J N Bw z (B₂ z)) ((hBw₂ (f x)).of_le (by simp))
      (h.horizontalLift_mem_orthogonal_ker x (B₁ (f x))),
    h.mfderiv_horizontalLift, hAterm]

variable [T2Space N]

omit [T2Space M] in
/-- Extend a horizontal vector at `x` to the global horizontal lift of a smooth vector field on
`N`. -/
private theorem exists_contMDiff_horizontalLift_eq {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    ∃ B : Π z : N, TangentSpace J z, CMDiff ∞ (T% B) ∧
      CMDiff ∞ (T% (fun y ↦ h.horizontalLift y (B (f y)))) ∧
      B (f x) = mfderiv I J f x u ∧
      h.horizontalLift x (B (f x)) = u := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  obtain ⟨B, hB, hBx⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ (mfderiv I J f x u)
  refine ⟨B, hB, h.contMDiff_horizontalLift hB (by simp), hBx, ?_⟩
  rw [hBx, h.horizontalLift_mfderiv_of_mem x hu]

/-- **O'Neill's horizontal curvature equation (`{4}`, vector form).** For horizontal `u, v, w`,
`𝓗 (R(u, v)w)` equals
`horizontalLift (R^N(df u, df v)(df w)) - 2 A_w (A_u v) + A_u (A_v w) - A_v (A_u w)`. -/
theorem starProjection_orthogonal_ker_curvatureTensor_of_mem_orthogonal_ker
    {u v w : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    (mfderiv I J f x).kerᗮ.starProjection (∇.curvatureTensor x u v w) =
      h.horizontalLift x
          ((leviCivitaConnection J N).curvatureTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v)
            (mfderiv I J f x w)) -
        (2 : ℝ) • h.oneillA x w (h.oneillA x u v) +
        h.oneillA x u (h.oneillA x v w) -
        h.oneillA x v (h.oneillA x u w) := by
  obtain ⟨Bu, hBu, hX, hBux, hXx⟩ := h.exists_contMDiff_horizontalLift_eq hu
  obtain ⟨Bv, hBv, hY, hBvx, hYx⟩ := h.exists_contMDiff_horizontalLift_eq hv
  obtain ⟨Bw, hBw, hZ, hBwx, hZx⟩ := h.exists_contMDiff_horizontalLift_eq hw
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Bu (f y))
  set Y : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Bv (f y))
  set Z : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Bw (f y))
  -- Evaluate `𝓗 (∇_{[X, Y]} Z)` via `[X, Y] = horizontalLift [Bu, Bv] + 2 A_X Y`.
  have hbr_term : (mfderiv I J f x).kerᗮ.starProjection (∇ Z x (mlieBracket I X Y x)) =
      h.horizontalLift x (leviCivitaConnection J N Bw (f x) (mlieBracket J Bu Bv (f x))) +
        (2 : ℝ) • h.oneillA x (Z x) (h.oneillA x (X x) (Y x)) := by
    rw [h.mlieBracket_horizontalLift ((hBu (f x)).of_le (by simp)) ((hBv (f x)).of_le (by simp)),
      map_add, map_smul, map_add, map_smul,
      h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
        ((hBw (f x)).of_le (by simp)) (h.horizontalLift_mem_orthogonal_ker x _),
      h.mfderiv_horizontalLift,
      h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
        ((hBw (f x)).of_le (by simp))
        (h.oneillA_apply_mem_ker (X x) (h.horizontalLift_mem_orthogonal_ker x _))]
  have hcovN_curv :
      (leviCivitaConnection J N).curvatureTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v)
        (mfderiv I J f x w) =
        leviCivitaConnection J N (fun z ↦ leviCivitaConnection J N Bw z (Bv z)) (f x) (Bu (f x)) -
          leviCivitaConnection J N (fun z ↦ leviCivitaConnection J N Bw z (Bu z)) (f x) (Bv (f x)) -
          leviCivitaConnection J N Bw (f x) (mlieBracket J Bu Bv (f x)) := by
    rw [← hBux, ← hBvx, ← hBwx, (leviCivitaConnection J N).curvatureTensor_apply (f x) hBu hBv hBw,
      CovariantDerivative.curvatureOperator_apply]
  -- Combine `h₁` (`∇_X ∇_Y Z`), `h₂` (`∇_Y ∇_X Z`), and `hbr_term` (`∇_[X, Y] Z`).
  have h₁ := h.starProjection_orthogonal_ker_second_basic_horizontal Bu hBv hBw (x := x)
  have h₂ := h.starProjection_orthogonal_ker_second_basic_horizontal Bv hBu hBw (x := x)
  dsimp only at h₁ h₂
  have hXx' : X x = u := hXx
  have hYx' : Y x = v := hYx
  have hZx' : Z x = w := hZx
  conv_lhs => rw [← hXx', ← hYx', ← hZx', ∇.curvatureTensor_apply x hX hY hZ,
    CovariantDerivative.curvatureOperator_apply, map_sub, map_sub]
  rw [h₁, h₂, hbr_term, hXx', hYx', hZx', hXx, hYx, hZx, hcovN_curv, map_sub, map_sub]
  abel

/-- **O'Neill's horizontal curvature equation on four horizontal vectors (`{4}`).** For horizontal
`u, v, w, z`, `⟪R(u, v)w, z⟫` equals
`⟪R^N(df u, df v)(df w), df z⟫ + 2⟪A_u v, A_w z⟫ - ⟪A_v w, A_u z⟫ + ⟪A_u w, A_v z⟫`. -/
theorem inner_curvatureTensor_of_mem_orthogonal_ker
    {u v w z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪∇.curvatureTensor x u v w, z⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureTensor (f x)
          (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w),
          mfderiv I J f x z⟫_ℝ +
        2 * ⟪h.oneillA x u v, h.oneillA x w z⟫_ℝ -
        ⟪h.oneillA x v w, h.oneillA x u z⟫_ℝ +
        ⟪h.oneillA x u w, h.oneillA x v z⟫_ℝ := by
  have hliftz : ⟪h.horizontalLift x
      ((leviCivitaConnection J N).curvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w)),
      z⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureTensor (f x)
          (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w),
        mfderiv I J f x z⟫_ℝ := by
    conv_lhs => rw [← h.horizontalLift_mfderiv_of_mem x hz]
    exact (h.horizontalLift x).inner_map_map _ _
  conv_lhs =>
    rw [← Submodule.starProjection_eq_self_iff.mpr hz,
      ← Submodule.inner_starProjection_left_eq_right]
  rw [h.starProjection_orthogonal_ker_curvatureTensor_of_mem_orthogonal_ker hu hv hw,
    inner_sub_left, inner_add_left, inner_sub_left, real_inner_smul_left, hliftz,
    h.inner_oneillA x w (h.oneillA x u v) z,
    h.inner_oneillA x u (h.oneillA x v w) z,
    h.inner_oneillA x v (h.oneillA x u w) z]
  ring

/-- O'Neill's horizontal curvature equation phrased directly on horizontal lifts of four base
tangent vectors. -/
theorem inner_curvatureTensor_horizontalLift (x : M) (a b c d : TangentSpace J (f x)) :
    ⟪∇.curvatureTensor x (h.horizontalLift x a) (h.horizontalLift x b) (h.horizontalLift x c),
        h.horizontalLift x d⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureTensor (f x) a b c, d⟫_ℝ +
        2 * ⟪h.oneillA x (h.horizontalLift x a) (h.horizontalLift x b),
          h.oneillA x (h.horizontalLift x c) (h.horizontalLift x d)⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x b) (h.horizontalLift x c),
          h.oneillA x (h.horizontalLift x a) (h.horizontalLift x d)⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x a) (h.horizontalLift x c),
          h.oneillA x (h.horizontalLift x b) (h.horizontalLift x d)⟫_ℝ := by
  simpa only [h.mfderiv_horizontalLift] using
    h.inner_curvatureTensor_of_mem_orthogonal_ker
      (h.horizontalLift_mem_orthogonal_ker x a) (h.horizontalLift_mem_orthogonal_ker x b)
      (h.horizontalLift_mem_orthogonal_ker x c) (h.horizontalLift_mem_orthogonal_ker x d)

/-- Specialization of O'Neill's four-horizontal curvature equation (`{4}`) to the base and ambient
sectional-curvature numerators:
`⟪R^N(df u, df v)(df v), df u⟫ = ⟪R(u, v)v, u⟫ + 3 ‖A_u v‖²`. -/
theorem inner_curvatureTensor_mfderiv_self_of_mem_orthogonal_ker {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x v),
        mfderiv I J f x u⟫_ℝ =
      ⟪∇.curvatureTensor x u v v, u⟫_ℝ + 3 * ‖h.oneillA x u v‖ ^ 2 := by
  have hcurv := h.inner_curvatureTensor_of_mem_orthogonal_ker hu hv hv hu
  rw [h.oneillA_self hv, inner_zero_left, h.oneillA_antisymm hv hu, inner_neg_right,
    real_inner_self_eq_norm_sq] at hcurv
  linarith

/-- **O'Neill's horizontal sectional curvature formula.** For any horizontal tangent vectors
`u, v`,
`K_N(df u, df v) = K_M(u, v) + 3 ‖A_u v‖² / det(Gram(u, v))`.
No linear-independence hypothesis is needed: on linearly dependent pairs the Gram determinant
vanishes and both sides are zero. -/
theorem sectionalCurvature_mfderiv_of_mem_orthogonal_ker {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      ∇.sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 / (Matrix.gram ℝ ![u, v]).det := by
  rw [CovariantDerivative.sectionalCurvature_apply, CovariantDerivative.sectionalCurvature_apply,
    h.inner_curvatureTensor_mfderiv_self_of_mem_orthogonal_ker hu hv,
    h.det_gram_mfderiv_of_mem_orthogonal_ker hu hv, add_div]

/-- **O'Neill's horizontal sectional curvature formula on horizontal lifts.** -/
theorem sectionalCurvature_eq_sectionalCurvature_horizontalLift_add (x : M)
    (a b : TangentSpace J (f x)) :
    (leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x) a b =
      ∇.sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x
          (h.horizontalLift x a) (h.horizontalLift x b) +
        3 * ‖h.oneillA x (h.horizontalLift x a) (h.horizontalLift x b)‖ ^ 2 /
          (Matrix.gram ℝ ![a, b]).det := by
  simpa only [h.mfderiv_horizontalLift, h.det_gram_horizontalLift] using
    h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker
      (h.horizontalLift_mem_orthogonal_ker x a) (h.horizontalLift_mem_orthogonal_ker x b)

/-- **O'Neill's horizontal sectional curvature formula on an orthonormal horizontal pair:**
`K_N(df u, df v) = K_M(u, v) + 3 ‖A_u v‖²`. -/
theorem sectionalCurvature_mfderiv_of_orthonormal {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (huv : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      ∇.sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv,
    Matrix.gram_eq_one_iff_orthonormal.mpr huv, Matrix.det_one, div_one]

/-- **O'Neill's horizontal sectional curvature formula in Lie-bracket form.** For vector fields
`X, Y` differentiable at `x` and horizontal near `x`,
`K_N(df (X x), df (Y x)) = K_M(X x, Y x) + (3 / 4) ‖𝓥 [X, Y]‖² / det(Gram(X x, Y x))`. -/
theorem sectionalCurvature_mfderiv_eq_add_three_quarters_norm_starProjection_ker_mlieBracket_sq_div
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      ∇.sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        3 / 4 * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 /
          (Matrix.gram ℝ ![X x, Y x]).det := by
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hXh.self_of_nhds hYh.self_of_nhds,
    h.starProjection_ker_mlieBracket hX hY hXh hYh, norm_smul, Real.norm_ofNat]
  ring

/-- **O'Neill's horizontal sectional curvature formula on orthonormal horizontal fields:**
`K_N(df (X x), df (Y x)) = K_M(X x, Y x) + (3 / 4) ‖𝓥 [X, Y]‖²`. -/
theorem sectionalCurvature_mfderiv_eq_add_three_quarters_norm_starProjection_ker_mlieBracket_sq
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    (hXY : Orthonormal ℝ ![X x, Y x]) :
    (leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      ∇.sectionalCurvature
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        3 / 4 * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_eq_add_three_quarters_norm_starProjection_ker_mlieBracket_sq_div
      hX hY hXh hYh,
    Matrix.gram_eq_one_iff_orthonormal.mpr hXY, Matrix.det_one, div_one]

/-- **A Riemannian submersion is sectional-curvature nondecreasing on horizontal planes.** -/
theorem sectionalCurvature_le_sectionalCurvature_mfderiv {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    ∇.sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v ≤
      (leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) := by
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv]
  exact le_add_of_nonneg_right
    (div_nonneg (by positivity) (Matrix.posSemidef_gram ℝ ![u, v]).det_nonneg)

/-- For any horizontal vectors `u, v`, the base sectional curvature equals the ambient sectional
curvature if and only if O'Neill's integrability tensor `A_u v` vanishes. On linearly dependent
horizontal pairs both sides hold automatically. -/
theorem sectionalCurvature_mfderiv_eq_iff {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      ∇.sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v ↔
      h.oneillA x u v = 0 := by
  by_cases huv : LinearIndependent ℝ ![u, v]
  · have hdet : 0 < (Matrix.gram ℝ ![u, v]).det :=
      (Matrix.posDef_gram_of_linearIndependent huv).det_pos
    rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv, add_eq_left,
      div_eq_zero_iff, or_iff_left hdet.ne', mul_eq_zero, or_iff_right (by norm_num),
      sq_eq_zero_iff, norm_eq_zero]
  · have hdet : (Matrix.gram ℝ ![u, v]).det = 0 :=
      not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr huv)
    have hA : h.oneillA x u v = 0 := by
      by_cases hu₀ : u = 0
      · simp [hu₀]
      · obtain ⟨c, hc⟩ := not_forall.mp ((LinearIndependent.pair_iff' hu₀).not.mp huv)
        rw [← not_not.mp hc, map_smul, h.oneillA_self hu, smul_zero]
    rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv, hdet, div_zero, add_zero, hA]
    simp

/-- A lower sectional-curvature bound on horizontal two-planes at `x` passes to all two-planes of
the base at `f x`. -/
theorem le_sectionalCurvature_of_forall_mem_orthogonal_ker {κ : ℝ}
    (hκ : ∀ u v : TangentSpace I x,
      u ∈ (mfderiv I J f x).kerᗮ → v ∈ (mfderiv I J f x).kerᗮ →
      LinearIndependent ℝ ![u, v] →
      κ ≤ ∇.sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v)
    {a b : TangentSpace J (f x)} (hab : LinearIndependent ℝ ![a, b]) :
    κ ≤ (leviCivitaConnection J N).sectionalCurvature
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x) a b := by
  have hlift_ind : LinearIndependent ℝ ![h.horizontalLift x a, h.horizontalLift x b] := by
    rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, h.det_gram_horizontalLift]
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hab
  refine (hκ _ _ (h.horizontalLift_mem_orthogonal_ker x a)
    (h.horizontalLift_mem_orthogonal_ker x b) hlift_ind).trans ?_
  simpa only [h.mfderiv_horizontalLift] using
    h.sectionalCurvature_le_sectionalCurvature_mfderiv
      (h.horizontalLift_mem_orthogonal_ker x a) (h.horizontalLift_mem_orthogonal_ker x b)

end HorizontalFour

end TauCeti.IsRiemannianSubmersion
