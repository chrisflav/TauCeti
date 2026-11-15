/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
import TauCeti.Geometry.Manifold.Distribution.Kernel

/-!
# Levi-Civita connection decomposition for a Riemannian submersion

Let `h : IsRiemannianSubmersion I J f` be a Riemannian submersion `f : M → N` with horizontal lift
`IsRiemannianSubmersion.horizontalLift`, O'Neill tensors `A` and `T`
(`IsRiemannianSubmersion.oneillA` and `IsRiemannianSubmersion.oneillT`), and orthogonal horizontal
and vertical projections `𝓗 := (mfderiv I J f ·).kerᗮ.starProjection` and
`𝓥 := (mfderiv I J f ·).ker.starProjection`.

The Levi-Civita derivative and Lie brackets of basic horizontal vector fields
`X y = h.horizontalLift y (B (f y))` decompose completely into base differentiation and O'Neill's
tensors:

* Along a horizontal vector `u ∈ (mfderiv I J f x).kerᗮ`,
  `∇_u X = h.horizontalLift x (∇^N_(df u) B) + A_u (X x)`.
* Along a vertical vector `w ∈ (mfderiv I J f x).ker`,
  `∇_w X = A_(X x) w + T_w (X x)`.
* Along an arbitrary tangent vector `u`, summing the two components expresses `∇_u X` in terms of
  `∇^N_(df u) B`, `A`, and `T`.
* For two basic horizontal lifts `X₁, X₂`, `[X₁, X₂] x = h.horizontalLift x ([B₁, B₂] (f x)) +
  2 A_(X₁ x) (X₂ x)`; for a vertical field `V`, `[X, V] x = 𝓥 (∇_(X x) V) - T_(V x) (X x)`.
* For an arbitrary differentiable field `W`, `𝓗 (∇_u W) = 𝓗 (∇_u (𝓗 W)) + A_u (𝓥 (W x)) +
  T_u (𝓥 (W x))`.

These decompositions supply the second-derivative and Lie-bracket inputs for O'Neill's curvature
equations in `TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Curvature` and for
horizontal-geodesic theory (specializing to trivial `A` and `T` on Riemannian products via
`TauCeti.oneillA_fst` and `TauCeti.oneillT_fst` in `ONeill/Basic.lean`). All basic-field and
general-field connection and bracket formulas require only `CMDiffAt 1` at `f x` (or `MDiffAt` at
`x`) with no Hausdorff assumption; `[T2Space M]` enters only in the differentiated alternating laws
for `(∇_w A)_u v := ∇.hom (∇.hom ∇) h.oneillA x w u v` (`∇ := leviCivitaConnection I M`).

## Main results

* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker`:
  `∇_u X` for a basic horizontal field `X` and horizontal `u`.
* `starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker` and
  `leviCivitaConnection_horizontalLift_of_mem_ker`: `𝓗 (∇_w X)` and `∇_w X` for a basic horizontal
  field `X` and vertical `w`.
* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`:
  `∇_u X` for a basic horizontal field `X` and arbitrary tangent vector `u`.
* `TauCeti.IsRiemannianSubmersion.mlieBracket_horizontalLift` and
  `TauCeti.IsRiemannianSubmersion.mlieBracket_horizontalLift_of_eventually_mem_ker`:
  Lie brackets of basic horizontal lifts with basic horizontal and vertical fields.
* `TauCeti.IsRiemannianSubmersion.starProjection_orthogonal_ker_leviCivitaConnection` and its
  vertical/horizontal specializations: `𝓗 (∇_u W)` for an arbitrary differentiable field `W`.
* `TauCeti.IsRiemannianSubmersion.inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker` and
  `inner_hom_hom_oneillA_antisymm_of_mem_orthogonal_ker_of_mem_ker`: vertical component of `∇_w A`
  is alternating on horizontal vectors.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Lemmas 1, 2, and 4.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C (equations 9.24).
-/

public section

open Bundle CovariantDerivative Filter Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold Topology

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

local notation "∇" => leviCivitaConnection I M

-- These regularity indices are propositionally, but not definitionally, equal to two.
local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

section BasicFields

variable {B : Π y : N, TangentSpace J y} {x : M}
include h

private theorem mdifferentiableAt_horizontalLift_of_contMDiffAt_one
    (hB : CMDiffAt 1 (T% B) (f x)) :
    MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    rw [one_add_one_eq_two]
    exact .of_le (by norm_cast)
  exact (h.contMDiffAt_horizontalLift hB (by norm_num)).mdifferentiableAt one_ne_zero

/-- **O'Neill's horizontal connection formula.** Differentiating a basic horizontal field
`y ↦ h.horizontalLift y (B (f y))` along a horizontal tangent vector `u` gives the lifted base
derivative plus O'Neill's `A`-tensor. -/
theorem leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
    (hB : CMDiffAt 1 (T% B) (f x)) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    ∇ (fun y ↦ h.horizontalLift y (B (f y))) x u =
      h.horizontalLift x (leviCivitaConnection J N B (f x) (mfderiv I J f x u)) +
        h.oneillA x u (h.horizontalLift x (B (f x))) := by
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB
  conv_lhs =>
    rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
      (∇ (fun y ↦ h.horizontalLift y (B (f y))) x u), add_comm]
  rw [h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
      hB hu,
    h.oneillA_apply_of_eventually_mem_orthogonal_ker hXd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) u,
    Submodule.starProjection_eq_self_iff.mpr hu]

/-- **O'Neill's Lemma 2 (horizontal part).** For a basic horizontal field `X` and a vertical
tangent vector `w`, the horizontal part `𝓗 (∇_w X)` equals `A_(X x) w`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
    (hB : CMDiffAt 1 (T% B) (f x)) {w : TangentSpace I x}
    (hw : w ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        (∇ (fun y ↦ h.horizontalLift y (B (f y))) x w) =
      h.oneillA x (h.horizontalLift x (B (f x))) w := by
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  have hXd : MDiffAt (T% X) x := h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB
  obtain ⟨V, hVd, rfl, hVv⟩ := h.exists_vertical_extension hw
  have htor := ((torsion_eq_zero_iff _).mp (torsion_leviCivitaConnection_eq_zero I)) hXd hVd
  have hbr_mem : mlieBracket I X V x ∈ (mfderiv I J f x).ker :=
    (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
      (by simp [minSmoothness_of_isRCLikeNormedField]) hXd hVd (hB.mdifferentiableAt one_ne_zero)
      (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) (.of_forall hVv)
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (mlieBracket I X V x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (by rwa [Submodule.orthogonal_orthogonal])
  have hAV := h.oneillA_apply_of_eventually_mem_ker hVd (.of_forall hVv) (X x)
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)] at hAV
  have hproj := congrArg (mfderiv I J f x).kerᗮ.starProjection htor
  rw [map_sub, hbr, sub_eq_zero] at hproj
  rw [← hproj, ← hAV]

/-- **O'Neill's vertical-horizontal connection formula.** Differentiating a basic horizontal field
`X` along a vertical vector `w` gives `A_(X x) w + T_w (X x)`. -/
theorem leviCivitaConnection_horizontalLift_of_mem_ker
    (hB : CMDiffAt 1 (T% B) (f x)) {w : TangentSpace I x}
    (hw : w ∈ (mfderiv I J f x).ker) :
    ∇ (fun y ↦ h.horizontalLift y (B (f y))) x w =
      h.oneillA x (h.horizontalLift x (B (f x))) w +
        h.oneillT x w (h.horizontalLift x (B (f x))) := by
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB
  conv_lhs =>
    rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
      (∇ (fun y ↦ h.horizontalLift y (B (f y))) x w), add_comm]
  rw [h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker hB hw,
    h.oneillT_apply_of_eventually_mem_orthogonal_ker hXd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) w,
    Submodule.starProjection_eq_self_iff.mpr hw]

/-- **O'Neill's full connection formula on basic horizontal fields.** For any tangent vector `u`,
the Levi-Civita derivative of `X y = h.horizontalLift y (B (f y))` along `u` decomposes into the
lifted base derivative along `df u` together with the three `A` and `T` terms. -/
theorem leviCivitaConnection_horizontalLift (hB : CMDiffAt 1 (T% B) (f x))
    (u : TangentSpace I x) :
    ∇ (fun y ↦ h.horizontalLift y (B (f y))) x u =
      h.horizontalLift x (leviCivitaConnection J N B (f x) (mfderiv I J f x u)) +
        h.oneillA x u (h.horizontalLift x (B (f x))) +
        h.oneillA x (h.horizontalLift x (B (f x))) ((mfderiv I J f x).ker.starProjection u) +
        h.oneillT x u (h.horizontalLift x (B (f x))) := by
  have huh : (mfderiv I J f x).kerᗮ.starProjection u ∈ (mfderiv I J f x).kerᗮ :=
    Submodule.starProjection_apply_mem _ _
  have huv : (mfderiv I J f x).ker.starProjection u ∈ (mfderiv I J f x).ker :=
    Submodule.starProjection_apply_mem _ _
  have hdf : mfderiv I J f x ((mfderiv I J f x).kerᗮ.starProjection u) = mfderiv I J f x u :=
    DFunLike.congr_fun (mfderiv I J f x).comp_starProjection_orthogonal_ker u
  conv_lhs => rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal u, add_comm]
  rw [map_add,
    h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker hB huh,
    h.leviCivitaConnection_horizontalLift_of_mem_ker hB huv,
    hdf, h.oneillA_starProjection_orthogonal_ker, h.oneillT_starProjection_ker]
  abel

/-- **O'Neill's Lie-bracket decomposition on basic horizontal lifts.** For base vector fields
`B₁, B₂` that are `C¹` at `f x`, the Lie bracket of their horizontal lifts equals the horizontal
lift of `[B₁, B₂]` plus `2 • A_(X₁ x) (X₂ x)`. -/
theorem mlieBracket_horizontalLift {B₁ B₂ : Π y : N, TangentSpace J y}
    (hB₁ : CMDiffAt 1 (T% B₁) (f x)) (hB₂ : CMDiffAt 1 (T% B₂) (f x)) :
    mlieBracket I (fun y ↦ h.horizontalLift y (B₁ (f y)))
        (fun y ↦ h.horizontalLift y (B₂ (f y))) x =
      h.horizontalLift x (mlieBracket J B₁ B₂ (f x)) +
        (2 : ℝ) • h.oneillA x (h.horizontalLift x (B₁ (f x)))
          (h.horizontalLift x (B₂ (f x))) := by
  conv_lhs =>
    rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
      (mlieBracket I (fun y ↦ h.horizontalLift y (B₁ (f y)))
        (fun y ↦ h.horizontalLift y (B₂ (f y))) x), add_comm]
  rw [← h.horizontalLift_mfderiv,
    h.mfderiv_mlieBracket_horizontalLift hB₁ hB₂,
    h.starProjection_ker_mlieBracket
      (h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB₁)
      (h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB₂)
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)]

/-- The Lie bracket of a basic horizontal field `X` with a field `V` which is vertical near `x` is
vertical and equals `𝓥 (∇_(X x) V) - T_(V x) (X x)`. -/
theorem mlieBracket_horizontalLift_of_eventually_mem_ker (hB : CMDiffAt 1 (T% B) (f x))
    {V : Π y : M, TangentSpace I y} (hVd : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) :
    mlieBracket I (fun y ↦ h.horizontalLift y (B (f y))) V x =
      (mfderiv I J f x).ker.starProjection (∇ V x (h.horizontalLift x (B (f x)))) -
        h.oneillT x (V x) (h.horizontalLift x (B (f x))) := by
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB
  have htor := ((torsion_eq_zero_iff _).mp (torsion_leviCivitaConnection_eq_zero I)) hXd hVd
  have hAV := h.oneillA_apply_of_eventually_mem_ker hVd hVv (h.horizontalLift x (B (f x)))
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)] at hAV
  have hdecompV := ((add_comm _ _).trans
    ((mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal
      (∇ V x (h.horizontalLift x (B (f x)))))).symm
  rw [← hAV] at hdecompV
  have hVX := h.leviCivitaConnection_horizontalLift_of_mem_ker hB hVv.self_of_nhds
  conv_lhs => rw [← htor, hdecompV, hVX]
  abel

end BasicFields

section GeneralFields

variable {x : M}
include h

/-- Along a vertical vector `v`, the horizontal component `𝓗 (∇_v V)` of the Levi-Civita derivative
of a field `V` vertical near `x` equals `T_v (V x)`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillT_of_mem_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker)
    {v : TangentSpace I x} (hv : v ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection (∇ V x v) = h.oneillT x v (V x) := by
  simpa only [Submodule.starProjection_eq_self_iff.mpr hv] using
    (h.oneillT_apply_of_eventually_mem_ker hV hVv v).symm

/-- Along a horizontal vector `u`, the horizontal component `𝓗 (∇_u V)` of the Levi-Civita
derivative of a field `V` vertical near `x` equals `A_u (V x)`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_eq_oneillA_of_mem_orthogonal_ker
    {V : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker)
    {u : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    (mfderiv I J f x).kerᗮ.starProjection (∇ V x u) = h.oneillA x u (V x) := by
  simpa only [Submodule.starProjection_eq_self_iff.mpr hu] using
    (h.oneillA_apply_of_eventually_mem_ker hV hVv u).symm

/-- For any vector field `W` differentiable at `x` and any tangent vector `u`, the horizontal
component of `∇_u W` decomposes into `𝓗 (∇_u (𝓗 W)) + A_u (𝓥 (W x)) + T_u (𝓥 (W x))`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection
    {W : Π y : M, TangentSpace I y} (hW : MDiffAt (T% W) x) (u : TangentSpace I x) :
    (mfderiv I J f x).kerᗮ.starProjection (∇ W x u) =
      (mfderiv I J f x).kerᗮ.starProjection
          (∇ (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y)) x u) +
        h.oneillA x u ((mfderiv I J f x).ker.starProjection (W x)) +
        h.oneillT x u ((mfderiv I J f x).ker.starProjection (W x)) := by
  have hPW := h.mdifferentiableAt_starProjection_orthogonal_ker_apply hW
  have hQW := h.mdifferentiableAt_starProjection_ker_apply hW
  have hsplit : W = (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y)) +
      fun y ↦ (mfderiv I J f y).ker.starProjection (W y) :=
    funext fun y ↦ ((add_comm _ _).trans
      ((mfderiv I J f y).ker.starProjection_add_starProjection_orthogonal (W y))).symm
  have hAQ := h.oneillA_apply_of_eventually_mem_ker hQW
    (.of_forall fun _ ↦ Submodule.starProjection_apply_mem _ _) u
  have hTQ := h.oneillT_apply_of_eventually_mem_ker hQW
    (.of_forall fun _ ↦ Submodule.starProjection_apply_mem _ _) u
  have hQW_u : (mfderiv I J f x).kerᗮ.starProjection
      (∇ (fun y ↦ (mfderiv I J f y).ker.starProjection (W y)) x u) =
    h.oneillA x u ((mfderiv I J f x).ker.starProjection (W x)) +
      h.oneillT x u ((mfderiv I J f x).ker.starProjection (W x)) := by
    conv_lhs =>
      rw [← (mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal u, add_comm]
    rw [map_add, map_add, ← hAQ, ← hTQ]
  conv_lhs => rw [hsplit]
  rw [∇.isCovariantDerivativeOnUniv.add hPW hQW, add_apply, map_add, hQW_u, add_assoc]

/-- Along a vertical vector `v`, the horizontal component of `∇_v W` equals
`𝓗 (∇_v (𝓗 W)) + T_v (𝓥 (W x))`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_of_mem_ker
    {W : Π y : M, TangentSpace I y} (hW : MDiffAt (T% W) x) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection (∇ W x v) =
      (mfderiv I J f x).kerᗮ.starProjection
          (∇ (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y)) x v) +
        h.oneillT x v ((mfderiv I J f x).ker.starProjection (W x)) := by
  rw [h.starProjection_orthogonal_ker_leviCivitaConnection hW v,
    h.oneillA_eq_zero_of_mem_ker hv, zero_apply, add_zero]

/-- Along a horizontal vector `u`, the horizontal component of `∇_u W` equals
`𝓗 (∇_u (𝓗 W)) + A_u (𝓥 (W x))`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_of_mem_orthogonal_ker
    {W : Π y : M, TangentSpace I y} (hW : MDiffAt (T% W) x) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    (mfderiv I J f x).kerᗮ.starProjection (∇ W x u) =
      (mfderiv I J f x).kerᗮ.starProjection
          (∇ (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (W y)) x u) +
        h.oneillA x u ((mfderiv I J f x).ker.starProjection (W x)) := by
  rw [h.starProjection_orthogonal_ker_leviCivitaConnection hW u,
    h.oneillT_eq_zero_of_mem_orthogonal_ker hu, zero_apply, add_zero]

end GeneralFields

section TensorDerivative

variable [T2Space M] {x : M}
include h

/-- **O'Neill's Lemma 4 (diagonal case).** For a horizontal vector `u` and a vertical vector `z`,
the vertical component of `(∇_w A)_u u` vanishes: `⟪(∇_w A)_u u, z⟫ = 0`. -/
theorem inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker
    (w : TangentSpace I x) {u z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).ker) :
    ⟪∇.hom (∇.hom ∇) h.oneillA x w u u, z⟫_ℝ = 0 := by
  obtain ⟨X, hXd, rfl, hXh⟩ := h.exists_horizontal_extension hu
  have hAA : (fun y ↦ h.oneillA y (X y) (X y)) = 0 :=
    funext fun y ↦ h.oneillA_self (hXh y)
  have heval := h.hom_hom_oneillA_apply hXd hXd w
  rw [hAA, ∇.zero, Pi.zero_apply, zero_apply] at heval
  set p := (mfderiv I J f x).kerᗮ.starProjection (∇ X x w)
  set q := (mfderiv I J f x).ker.starProjection (∇ X x w)
  have hp : p ∈ (mfderiv I J f x).kerᗮ := Submodule.starProjection_apply_mem _ _
  have hq : q ∈ (mfderiv I J f x).ker := Submodule.starProjection_apply_mem _ _
  have hsplit : ∇ X x w = q + p :=
    ((mfderiv I J f x).ker.starProjection_add_starProjection_orthogonal (∇ X x w)).symm
  rw [heval, hsplit, map_add, add_apply, map_add,
    h.oneillA_eq_zero_of_mem_ker hq, zero_apply, zero_add,
    h.oneillA_antisymm hp (hXh x)]
  have hcancel :
      (0 : TangentSpace I x) - -h.oneillA x (X x) p -
        (h.oneillA x (X x) q + h.oneillA x (X x) p) =
      -h.oneillA x (X x) q := by abel
  rw [hcancel, inner_neg_left,
    Submodule.inner_left_of_mem_orthogonal hz (h.oneillA_apply_mem_orthogonal_ker (X x) hq),
    neg_zero]

/-- **O'Neill's Lemma 4 (alternating form).** For horizontal `u₁, u₂` and vertical `z`,
`⟪(∇_w A)_{u₁} u₂, z⟫ = -⟪(∇_w A)_{u₂} u₁, z⟫`. -/
theorem inner_hom_hom_oneillA_antisymm_of_mem_orthogonal_ker_of_mem_ker
    (w : TangentSpace I x) {u₁ u₂ z : TangentSpace I x}
    (hu₁ : u₁ ∈ (mfderiv I J f x).kerᗮ) (hu₂ : u₂ ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).ker) :
    ⟪∇.hom (∇.hom ∇) h.oneillA x w u₁ u₂, z⟫_ℝ =
      -⟪∇.hom (∇.hom ∇) h.oneillA x w u₂ u₁, z⟫_ℝ := by
  have hsum := h.inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker w (add_mem hu₁ hu₂) hz
  simp only [map_add, add_apply, inner_add_left,
    h.inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker w hu₁ hz,
    h.inner_hom_hom_oneillA_self_of_mem_orthogonal_ker_of_mem_ker w hu₂ hz,
    zero_add, add_zero] at hsum
  linarith

end TensorDerivative

end TauCeti.IsRiemannianSubmersion
