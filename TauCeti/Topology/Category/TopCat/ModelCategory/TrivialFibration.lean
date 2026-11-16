/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.ModelCategory.SmallObject

import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
import TauCeti.Topology.CWComplex.Classical.Sphere.Basic
import TauCeti.Topology.Homotopy.Extension.Ball
import TauCeti.Topology.Homotopy.SerreFibration.CWComplex
import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# Trivial fibrations in the Quillen–Serre model structure on `TopCat`

This file proves the identification
`TauCeti.TopCat.modelCategoryQuillen.rlp_I`:
a morphism `p : E ⟶ B` in `TopCat` has the right lifting property with respect to the disk
boundary inclusions `I = {∂𝔻 n ⟶ 𝔻 n | n : ℕ}` if and only if `p` is both a Serre fibration and
a weak homotopy equivalence.

## Structure of the proof

1. **`I.rlp ≤ serreFibrations`** (`TauCeti.TopCat.modelCategoryQuillen.rlp_I_le_serreFibrations`):
   Given `p ∈ I.rlp`, we establish the homotopy lifting property for every cube `Iⁿ`. Using the
   time-reversed radial projection of `closedBall (0 : Fin n → ℝ) 1` onto the top and sides of its
   cylinder (`TauCeti.ballRadialProjection`), which has a global continuous inverse
   `(t, y) ↦ (1 / (1 + t)) • y`, we first lift over the top-and-sides copy of `Iⁿ` extending the
   initial lift on `{0} × ∂Iⁿ`, glue with the initial lift on `{0} × Iⁿ`, and then lift over the
   full cylinder `I × Iⁿ ≃ₜ Iⁿ⁺¹` extending the resulting map on `∂(I × Iⁿ)`.
2. **`I.rlp ≤ weakEquivalences`** (`TauCeti.TopCat.modelCategoryQuillen.rlp_I_le_weakEquivalences`):
   Lifting against `∂I⁰ ↪ I⁰` and `∂I¹ ↪ I¹` gives bijectivity on path components; lifting against
   `∂Iⁿ⁺¹ ↪ Iⁿ⁺¹` and `∂Iⁿ⁺² ↪ Iⁿ⁺²` gives surjectivity and injectivity on `π_{n+1}`.
3. **`serreFibrations ⊓ weakEquivalences ≤ I.rlp`**
   (`TauCeti.TopCat.modelCategoryQuillen.serreFibrations_inf_weakEquivalences_le_rlp_I`):
   By `TauCeti.TopCat.isWeakHomotopyEquivalence_iff_of_mem_serreFibrations`, every fibre of a
   trivial Serre fibration is nonempty and weakly contractible. In dimension `0`, lifting uses
   nonemptiness of fibres. In dimension `m + 1`, we linearly contract `𝔻 (m + 1)` to a boundary
   point `s₀`, lift the resulting homotopy on the CW complex `∂𝔻 (m + 1)` along `p`, extend the
   time-`1` map `∂𝔻 (m + 1) ⟶ p.fiber (g s₀)` over `𝔻 (m + 1)` using weak contractibility of the
   fibre, and apply relative homotopy lifting
   (`TauCeti.TopCat.exists_lift_closedBall_of_mem_serreFibrations`) to the time-reversed
   contraction.

## References

* M. Hovey, *Model Categories*, AMS Mathematical Surveys and Monographs 63 (1999),
  Section 2.4 (Proposition 2.4.10 and Theorem 2.4.19).
* D. G. Quillen, *Homotopical Algebra*, Lecture Notes in Mathematics 43, Springer (1967),
  Chapter II, Section 3.
-/

public section

noncomputable section

open CategoryTheory MorphismProperty Metric Set

universe u

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B}

/-! ### Lifting against cube boundaries from `I.rlp` -/

section RlpI

open scoped Topology Topology.Homotopy
open unitInterval

/-- A morphism in `modelCategoryQuillen.I.rlp` lifts every map on a finite cube `Iⁿ` extending a
prescribed lift on its boundary `∂Iⁿ`. -/
private lemma exists_lift_cube_of_mem_rlp_I (hp : modelCategoryQuillen.I.{u}.rlp p) (n : ℕ)
    (f : C(Cube.boundary (Fin n), E)) (g : C(I^(Fin n), B))
    (hfg : ∀ x : Cube.boundary (Fin n), p (f x) = g x) :
    ∃ G : C(I^(Fin n), E), p ∘ G = g ∧ ∀ x : Cube.boundary (Fin n), G x = f x := by
  let e : TopCat.disk.{u} n ≃ₜ I^(Fin n) := diskHomeomorphCube.{u} n
  let bdMap : C(TopCat.diskBoundary.{u} n, Cube.boundary (Fin n)) :=
    ⟨fun s ↦ ⟨e (TopCat.diskBoundaryInclusion n s),
      (diskHomeomorphCube_mem_boundary_iff _).2 ⟨s, rfl⟩⟩, by fun_prop⟩
  let top : TopCat.diskBoundary.{u} n ⟶ E := TopCat.ofHom (f.comp bdMap)
  let bot : TopCat.disk.{u} n ⟶ B :=
    TopCat.ofHom (g.comp (e : C(TopCat.disk.{u} n, I^(Fin n))))
  have sq : CommSq top (TopCat.diskBoundaryInclusion n) p bot :=
    ⟨by ext s; exact hfg (bdMap s)⟩
  have : HasLiftingProperty (TopCat.diskBoundaryInclusion.{u} n) p :=
    hp _ (modelCategoryQuillen.diskBoundaryInclusion_mem_I n)
  let l : TopCat.disk.{u} n ⟶ E := sq.lift
  refine ⟨l.hom.comp (e.symm : C(I^(Fin n), TopCat.disk.{u} n)), funext fun y ↦ ?_, fun x ↦ ?_⟩
  · change p (l (e.symm y)) = g y
    refine (ConcreteCategory.congr_hom sq.fac_right (e.symm y)).trans ?_
    change g (e (e.symm y)) = g y
    rw [e.apply_symm_apply]
  · obtain ⟨s, hs⟩ := (diskHomeomorphCube_mem_boundary_iff (e.symm x.1)).1
      (by simp [e])
    have h := ConcreteCategory.congr_hom sq.fac_left s
    change l (TopCat.diskBoundaryInclusion n s) = f (bdMap s) at h
    have hbd : bdMap s = x := Subtype.ext (by
      change e (TopCat.diskBoundaryInclusion n s) = x.1
      rw [hs, e.apply_symm_apply])
    change l (e.symm x.1) = f x
    rw [← hs, h, hbd]

/-- A morphism in `modelCategoryQuillen.I.rlp` lifts every homotopy on `I × Iⁿ` extending a
prescribed lift on the boundary `Cube.prodBoundary (Fin n) = ({0, 1} × Iⁿ) ∪ (I × ∂Iⁿ)`. -/
private lemma exists_lift_prodBoundary_of_mem_rlp_I (hp : modelCategoryQuillen.I.{u}.rlp p) (n : ℕ)
    (f : C(Cube.prodBoundary (Fin n), E)) (H : C(I × I^(Fin n), B))
    (hf : ∀ x : Cube.prodBoundary (Fin n), p (f x) = H x) :
    ∃ G : C(I × I^(Fin n), E), p ∘ G = H ∧ ∀ x : Cube.prodBoundary (Fin n), G x = f x := by
  let e : (I^(Fin (n + 1))) ≃ₜ I × I^(Fin n) := cubeSplitHomeomorph n
  let bdMap : C(Cube.boundary (Fin (n + 1)), Cube.prodBoundary (Fin n)) :=
    ⟨fun y ↦ ⟨e y.1, cubeSplitHomeomorph_mem_prodBoundary_iff.2 y.2⟩, by fun_prop⟩
  obtain ⟨G', hG', hG'f⟩ := exists_lift_cube_of_mem_rlp_I hp (n + 1) (f.comp bdMap) (H.comp e)
    fun y ↦ hf (bdMap y)
  refine ⟨G'.comp e.symm, funext fun x ↦ ?_, fun x ↦ ?_⟩
  · simpa [e] using congrFun hG' (e.symm x)
  · have hmem : e.symm x.1 ∈ Cube.boundary (Fin (n + 1)) :=
      cubeSplitHomeomorph_symm_mem_boundary x.2
    have h := hG'f ⟨e.symm x.1, hmem⟩
    have hbd : bdMap ⟨e.symm x.1, hmem⟩ = x := Subtype.ext (e.apply_symm_apply x.1)
    simpa [hbd] using h

/-! ### Time-reversed radial projection onto the top and sides of a ball cylinder -/

section TopAndSides

variable {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace ℝ E']

/-- Time-reversed radial projection of `closedBall (0 : E') 1` onto the top and sides
`{1} × D ∪ I × S` of the cylinder `I × D`, obtained by applying `TauCeti.ballRadialProjection` at
height `1` and reversing the interval coordinate with `unitInterval.symm`. -/
private def ballTopRadialMap :
    C(closedBall (0 : E') 1, I × closedBall (0 : E') 1) where
  toFun x := (σ ⟨(ballRadialProjection ((1 : I), x)).1,
      (ballRadialProjection_spec ((1 : I), x)).1⟩,
    ⟨(ballRadialProjection ((1 : I), x)).2,
      (ballRadialProjection_spec ((1 : I), x)).2.1⟩)
  continuous_toFun := by
    have hc : Continuous fun x : closedBall (0 : E') 1 ↦ ballRadialProjection ((1 : I), x) :=
      continuous_ballRadialProjection.comp (continuous_const.prodMk continuous_id)
    exact (unitInterval.continuous_symm.comp (hc.fst.subtype_mk _)).prodMk (hc.snd.subtype_mk _)

/-- On the unit sphere, `ballTopRadialMap` sends `x` to `(0, x)`. -/
private lemma ballTopRadialMap_of_mem_sphere {x : closedBall (0 : E') 1}
    (hx : (x : E') ∈ sphere (0 : E') 1) :
    ballTopRadialMap x = (0, x) := by
  have hmem : ((1 : I), x) ∈
      cylinderExtensionDomain (Subtype.val ⁻¹' sphere (0 : E') 1 : Set (closedBall (0 : E') 1)) :=
    mem_cylinderExtensionDomain_of_mem hx
  have h := ballRadialProjection_eq_self ((1 : I), x) hmem
  apply Prod.ext
  · apply Subtype.ext
    change (1 : ℝ) - (ballRadialProjection ((1 : I), x)).1 = (0 : I)
    rw [congrArg Prod.fst h]
    norm_num
  · exact Subtype.ext (congrArg Prod.snd h)

/-- Global continuous left inverse `(t, y) ↦ (1 / (1 + t)) • y` to `ballTopRadialMap` on the top
and sides `{1} × D ∪ I × S` of the cylinder. -/
private def ballTopRadialInv : C(I × closedBall (0 : E') 1, closedBall (0 : E') 1) where
  toFun p := ⟨(1 / (1 + (p.1 : ℝ))) • (p.2 : E'), by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
    have hpos : 0 < 1 + (p.1 : ℝ) := by linarith [p.1.2.1]
    have hge : 1 ≤ 1 + (p.1 : ℝ) := by linarith [p.1.2.1]
    rw [abs_of_pos (one_div_pos.2 hpos), one_div_mul_eq_div]
    exact (div_le_one hpos).2 ((mem_closedBall_zero_iff.1 p.2.2).trans hge)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hne : ∀ p : I × closedBall (0 : E') 1, 1 + (p.1 : ℝ) ≠ 0 :=
      fun p ↦ by linarith [p.1.2.1]
    exact (continuous_const.div (continuous_const.add (continuous_subtype_val.comp continuous_fst))
      hne).smul (continuous_subtype_val.comp continuous_snd)

private lemma ballTopRadialInv_zero (y : closedBall (0 : E') 1) :
    ballTopRadialInv ((0 : I), y) = y := by
  apply Subtype.ext
  change (1 / (1 + (0 : ℝ))) • (y : E') = y
  norm_num

/-- On the top face `{1} × D` and on the sides `I × S`, `ballTopRadialInv` is a right inverse to
`ballTopRadialMap`. -/
private lemma ballTopRadialMap_ballTopRadialInv {t : I} {y : closedBall (0 : E') 1}
    (h : t = 1 ∨ (y : E') ∈ sphere (0 : E') 1) :
    ballTopRadialMap (ballTopRadialInv (t, y)) = (t, y) := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have h1t_pos : 0 < 1 + (t : ℝ) := by linarith
  have hnorm_y : ‖(y : E')‖ ≤ 1 := mem_closedBall_zero_iff.1 y.2
  have hnorm_inv : 2 * ‖(ballTopRadialInv (t, y) : E')‖ = 2 * ‖(y : E')‖ / (1 + (t : ℝ)) := by
    change 2 * ‖(1 / (1 + (t : ℝ))) • (y : E')‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 h1t_pos)]
    ring
  have hden : ballRadialDen ((1 : I), ballTopRadialInv (t, y)) = 2 / (1 + (t : ℝ)) := by
    rw [ballRadialDen_def, Icc.coe_one, hnorm_inv]
    norm_num
    rcases h with rfl | hy
    · rw [Icc.coe_one]
      have hle : 2 * ‖(y : E')‖ / (1 + (1 : ℝ)) ≤ 1 := by
        rw [div_le_one (by norm_num : (0 : ℝ) < 1 + 1)]
        linarith
      rw [max_eq_left hle]
      norm_num
    · rw [mem_sphere_zero_iff_norm.1 hy, mul_one]
      have hge : 1 ≤ 2 / (1 + (t : ℝ)) := by
        rw [le_div_iff₀ h1t_pos]
        linarith
      exact max_eq_right hge
  apply Prod.ext
  · apply Subtype.ext
    change (1 : ℝ) - (ballRadialProjection ((1 : I), ballTopRadialInv (t, y))).1 = t
    rw [ballRadialProjection_def, hden, Icc.coe_one]
    field_simp [h1t_pos.ne']
    ring
  · apply Subtype.ext
    change (ballRadialProjection ((1 : I), ballTopRadialInv (t, y))).2 = y
    rw [ballRadialProjection_def, hden]
    change (2 / (2 / (1 + (t : ℝ)))) • ((1 / (1 + (t : ℝ))) • (y : E')) = y
    rw [smul_smul]
    have hmul : 2 / (2 / (1 + (t : ℝ))) * (1 / (1 + (t : ℝ))) = 1 := by
      field_simp [h1t_pos.ne']
    rw [hmul, one_smul]

end TopAndSides

/-! ### `I.rlp ≤ serreFibrations` and `I.rlp ≤ weakEquivalences` -/

namespace modelCategoryQuillen

/-- Every morphism with the right lifting property with respect to the disk boundary inclusions
`∂𝔻 n ⟶ 𝔻 n` is a Serre fibration. -/
theorem rlp_I_le_serreFibrations : modelCategoryQuillen.I.{u}.rlp ≤ serreFibrations.{u} := by
  intro E B p hp
  rw [mem_serreFibrations_iff_cube]
  intro n f H hH
  let e : (I^(Fin n)) ≃ₜ closedBall (0 : Fin n → ℝ) 1 := cubeHomeomorphClosedBall (Fin n)
  have he (y : I^(Fin n)) : (e y : Fin n → ℝ) ∈ sphere 0 1 ↔ y ∈ Cube.boundary (Fin n) := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_cubeHomeomorphClosedBall_eq_one_iff y
  let Φ : C(I^(Fin n), I × I^(Fin n)) :=
    ⟨fun z ↦ ((ballTopRadialMap (e z)).1, e.symm (ballTopRadialMap (e z)).2), by fun_prop⟩
  have hΦ_bd {z : I^(Fin n)} (hz : z ∈ Cube.boundary (Fin n)) : Φ z = (0, z) := by
    change ((ballTopRadialMap (e z)).1, e.symm (ballTopRadialMap (e z)).2) = (0, z)
    rw [ballTopRadialMap_of_mem_sphere ((he z).2 hz)]
    simp
  -- Step 1: lift `H ∘ Φ` over `Iⁿ` extending `f` on `∂Iⁿ`.
  obtain ⟨L₁, hL₁H, hL₁f⟩ := exists_lift_cube_of_mem_rlp_I hp n
    (f.comp ⟨Subtype.val, continuous_subtype_val⟩) (H.comp Φ) fun z ↦ by
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      rw [hΦ_bd z.2]
      exact (hH z.1).symm
  -- Step 2: glue `f` on `{0} × Iⁿ` with `L₁ ∘ e.symm ∘ ballTopRadialInv ∘ (id × e)` on
  -- `{1} × Iⁿ ∪ I × ∂Iⁿ` to obtain a lift on the boundary of `I × Iⁿ`.
  let topMap : C(Cube.prodBoundary (Fin n), E) :=
    ⟨fun x ↦ L₁ (e.symm (ballTopRadialInv (x.1.1, e x.1.2))), by fun_prop⟩
  let botMap : C(Cube.prodBoundary (Fin n), E) :=
    ⟨fun x ↦ f x.1.2, by fun_prop⟩
  let bFun : Cube.prodBoundary (Fin n) → E := fun x ↦ if x.1.1 = 0 then botMap x else topMap x
  have hbCont : Continuous bFun := by
    let S₀ : Set (Cube.prodBoundary (Fin n)) := {x | x.1.1 = 0}
    let S₁ : Set (Cube.prodBoundary (Fin n)) :=
      {x | x.1.1 = 1 ∨ x.1.2 ∈ Cube.boundary (Fin n)}
    have hcover : S₀ ∪ S₁ = univ := by
      ext x
      simp only [S₀, S₁, mem_union, mem_ofPred_eq, mem_univ, iff_true]
      rcases Cube.mem_prodBoundary_iff.1 x.2 with (h0 | h1) | hb
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr hb)
    have hS₀ : IsClosed S₀ :=
      isClosed_singleton.preimage (continuous_fst.comp continuous_subtype_val)
    have hS₁ : IsClosed S₁ :=
      (isClosed_singleton.preimage (continuous_fst.comp continuous_subtype_val)).union
        (Cube.isClosed_boundary.preimage (continuous_snd.comp continuous_subtype_val))
    rw [← continuousOn_univ, ← hcover]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hS₀ hS₁
    · refine botMap.continuous.continuousOn.congr fun x hx ↦ ?_
      have h0 : x.1.1 = 0 := hx
      simp [bFun, h0]
    · refine topMap.continuous.continuousOn.congr fun x hx ↦ ?_
      by_cases h0 : x.1.1 = 0
      · rcases hx with h1 | hb
        · exact absurd (h0.symm.trans h1) zero_ne_one
        · simp only [bFun, h0, ↓reduceIte, botMap, topMap, ContinuousMap.coe_mk]
          rw [ballTopRadialInv_zero, e.symm_apply_apply]
          exact (hL₁f ⟨x.1.2, hb⟩).symm
      · simp [bFun, h0]
  have hbProj (x : Cube.prodBoundary (Fin n)) : p (bFun x) = H x.1 := by
    by_cases h0 : x.1.1 = 0
    · simp only [bFun, h0, ↓reduceIte, botMap, ContinuousMap.coe_mk]
      have hx : x.1 = (0, x.1.2) := Prod.ext h0 rfl
      rw [hx]
      exact (hH x.1.2).symm
    · simp only [bFun, h0, ↓reduceIte, topMap, ContinuousMap.coe_mk]
      have htop : x.1.1 = 1 ∨ (e x.1.2 : Fin n → ℝ) ∈ sphere 0 1 := by
        rcases Cube.mem_prodBoundary_iff.1 x.2 with (h0' | h1) | hb
        · exact absurd h0' h0
        · exact Or.inl h1
        · exact Or.inr ((he x.1.2).2 hb)
      have hL := congrFun hL₁H (e.symm (ballTopRadialInv (x.1.1, e x.1.2)))
      have hΦinv : Φ (e.symm (ballTopRadialInv (x.1.1, e x.1.2))) = x.1 := by
        change ((ballTopRadialMap (e (e.symm (ballTopRadialInv (x.1.1, e x.1.2))))).1,
          e.symm (ballTopRadialMap (e (e.symm (ballTopRadialInv (x.1.1, e x.1.2))))).2) = x.1
        rw [e.apply_symm_apply, ballTopRadialMap_ballTopRadialInv htop, e.symm_apply_apply]
      simpa [hΦinv] using hL
  -- Step 3: lift `H` over `I × Iⁿ` extending `bFun` on its boundary.
  obtain ⟨G, hGH, hGb⟩ := exists_lift_prodBoundary_of_mem_rlp_I hp n ⟨bFun, hbCont⟩ H hbProj
  refine ⟨G, hGH, fun z ↦ ?_⟩
  have h := hGb ⟨(0, z), Cube.mk_zero_mem_prodBoundary z⟩
  simpa [bFun, botMap] using h

/-- Every morphism in `I.rlp` belongs to `J.rlp`. -/
theorem rlp_I_le_rlp_J : modelCategoryQuillen.I.{u}.rlp ≤ J.{u}.rlp := by
  rw [rlp_J]
  exact rlp_I_le_serreFibrations

/-- Every morphism with the right lifting property with respect to the disk boundary inclusions
`∂𝔻 n ⟶ 𝔻 n` is a weak homotopy equivalence. -/
theorem rlp_I_le_weakEquivalences : modelCategoryQuillen.I.{u}.rlp ≤ weakEquivalences.{u} := by
  intro E B p hp
  rw [mem_weakEquivalences_iff, ContinuousMap.isWeakHomotopyEquivalence_iff_joined]
  refine ⟨?_, ?_, fun n a ↦ ⟨?_, ?_⟩⟩
  · -- Surjectivity on path components (in fact surjectivity on points), via `∂I⁰ ↪ I⁰`.
    intro b
    have hempty : IsEmpty (Cube.boundary (Fin 0)) :=
      Set.isEmpty_coe_sort.2 Cube.boundary_eq_empty
    obtain ⟨G, hG, -⟩ := exists_lift_cube_of_mem_rlp_I hp 0
      ⟨isEmptyElim, continuous_of_discreteTopology⟩ (ContinuousMap.const _ b)
      fun x ↦ isEmptyElim x
    exact ⟨G 0, by rw [← Function.comp_apply (f := p), hG]; exact Joined.refl b⟩
  · -- Injectivity on path components, via `∂I¹ ↪ I¹`.
    intro a₁ a₂ ⟨γ⟩
    let fFun : Cube.boundary (Fin 1) → E := fun y ↦ if y.1 0 = 0 then a₁ else a₂
    have hfCont : Continuous fFun := by
      let S₀ : Set (Cube.boundary (Fin 1)) := {y | y.1 0 = 0}
      let S₁ : Set (Cube.boundary (Fin 1)) := {y | y.1 0 = 1}
      have hcover : S₀ ∪ S₁ = univ := by
        ext y
        simpa [S₀, S₁] using Cube.boundary_fin_one_iff.1 y.2
      have hS₀ : IsClosed S₀ :=
        isClosed_singleton.preimage ((continuous_apply 0).comp continuous_subtype_val)
      have hS₁ : IsClosed S₁ :=
        isClosed_singleton.preimage ((continuous_apply 0).comp continuous_subtype_val)
      rw [← continuousOn_univ, ← hcover]
      refine ContinuousOn.union_of_isClosed ?_ ?_ hS₀ hS₁
      · refine (continuousOn_const (c := a₁)).congr fun y hy ↦ ?_
        have h0 : y.1 0 = 0 := hy
        simp [fFun, h0]
      · refine (continuousOn_const (c := a₂)).congr fun y hy ↦ ?_
        have h1 : y.1 0 = 1 := hy
        have hne : y.1 0 ≠ 0 := by rw [h1]; exact one_ne_zero
        simp [fFun, hne]
    obtain ⟨G, -, hGf⟩ := exists_lift_cube_of_mem_rlp_I hp 1 ⟨fFun, hfCont⟩
      ⟨fun y ↦ γ (y 0), by fun_prop⟩ fun y ↦ by
        rcases Cube.boundary_fin_one_iff.1 y.2 with h0 | h1
        · simp [fFun, h0, γ.source]
        · simp [fFun, h1, γ.target]
    refine ⟨⟨⟨fun t ↦ G (fun _ ↦ t), by fun_prop⟩, ?_, ?_⟩⟩
    · have h0 := hGf ⟨fun _ ↦ 0, Cube.boundary_fin_one_iff.2 (Or.inl rfl)⟩
      simpa [fFun] using h0
    · have h1 := hGf ⟨fun _ ↦ 1, Cube.boundary_fin_one_iff.2 (Or.inr rfl)⟩
      simpa [fFun, one_ne_zero] using h1
  · -- Injectivity on `π_{n+1}(E, a)`, via `∂(I × Iⁿ⁺¹) ↪ I × Iⁿ⁺¹`.
    intro c₁ c₂ hc
    induction c₁ using Quotient.inductionOn with | h α => ?_
    induction c₂ using Quotient.inductionOn with | h β => ?_
    rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk] at hc
    obtain ⟨H⟩ := Quotient.exact hc
    let bFun : Cube.prodBoundary (Fin (n + 1)) → E :=
      fun x ↦ if x.1.1 = 0 then α x.1.2 else if x.1.1 = 1 then β x.1.2 else a
    have hbCont : Continuous bFun := by
      let S₀ : Set (Cube.prodBoundary (Fin (n + 1))) := {x | x.1.1 = 0}
      let S₁ : Set (Cube.prodBoundary (Fin (n + 1))) := {x | x.1.1 = 1}
      let S₂ : Set (Cube.prodBoundary (Fin (n + 1))) :=
        {x | x.1.2 ∈ Cube.boundary (Fin (n + 1))}
      have hcover : (S₀ ∪ S₁) ∪ S₂ = univ := by
        ext x
        simpa [S₀, S₁, S₂] using Cube.mem_prodBoundary_iff.1 x.2
      have hS₀ : IsClosed S₀ :=
        isClosed_singleton.preimage (continuous_fst.comp continuous_subtype_val)
      have hS₁ : IsClosed S₁ :=
        isClosed_singleton.preimage (continuous_fst.comp continuous_subtype_val)
      have hS₂ : IsClosed S₂ :=
        Cube.isClosed_boundary.preimage (continuous_snd.comp continuous_subtype_val)
      rw [← continuousOn_univ, ← hcover]
      refine ContinuousOn.union_of_isClosed ?_ ?_ (hS₀.union hS₁) hS₂
      · refine ContinuousOn.union_of_isClosed ?_ ?_ hS₀ hS₁
        · refine (α.1.continuous.comp
              (continuous_snd.comp continuous_subtype_val)).continuousOn.congr fun x hx ↦ ?_
          have h0 : x.1.1 = 0 := hx
          simp [bFun, h0]
        · refine (β.1.continuous.comp
              (continuous_snd.comp continuous_subtype_val)).continuousOn.congr fun x hx ↦ ?_
          have h1 : x.1.1 = 1 := hx
          simp [bFun, h1]
      · refine (continuousOn_const (c := a)).congr fun x hx ↦ ?_
        have hb : x.1.2 ∈ Cube.boundary (Fin (n + 1)) := hx
        by_cases h0 : x.1.1 = 0
        · simp only [bFun, h0, ↓reduceIte]
          exact α.2 _ hb
        · by_cases h1 : x.1.1 = 1
          · simp only [bFun, h1, one_ne_zero, ↓reduceIte]
            exact β.2 _ hb
          · simp [bFun, h0, h1]
    have hbProj (x : Cube.prodBoundary (Fin (n + 1))) : p (bFun x) = H x.1 := by
      by_cases h0 : x.1.1 = 0
      · have hx : x.1 = (0, x.1.2) := Prod.ext h0 rfl
        change p (if x.1.1 = 0 then α x.1.2 else if x.1.1 = 1 then β x.1.2 else a) = H x.1
        simp only [h0, ↓reduceIte]
        rw [hx, H.apply_zero]
        exact (GenLoop.map_apply p.hom rfl α x.1.2).symm
      · by_cases h1 : x.1.1 = 1
        · have hx : x.1 = (1, x.1.2) := Prod.ext h1 rfl
          change p (if x.1.1 = 0 then α x.1.2 else if x.1.1 = 1 then β x.1.2 else a) = H x.1
          simp only [h1, one_ne_zero, ↓reduceIte]
          rw [hx, H.apply_one]
          exact (GenLoop.map_apply p.hom rfl β x.1.2).symm
        · have hb : x.1.2 ∈ Cube.boundary (Fin (n + 1)) := by
            rcases Cube.mem_prodBoundary_iff.1 x.2 with (h0' | h1') | hb
            · exact absurd h0' h0
            · exact absurd h1' h1
            · exact hb
          simp only [bFun, h0, h1, ↓reduceIte]
          rw [H.eq_fst x.1.1 hb]
          exact (congrArg p (α.2 x.1.2 hb)).symm.trans (GenLoop.map_apply p.hom rfl α x.1.2).symm
    obtain ⟨L, -, hLb⟩ := exists_lift_prodBoundary_of_mem_rlp_I hp (n + 1) ⟨bFun, hbCont⟩
      H.toContinuousMap hbProj
    refine Quotient.sound (GenLoop.homotopic_of_continuousMap L (fun y ↦ ?_) (fun y ↦ ?_)
      fun t y hy ↦ ?_)
    · simpa [bFun] using hLb ⟨(0, y), Cube.mk_zero_mem_prodBoundary y⟩
    · simpa [bFun, one_ne_zero] using hLb ⟨(1, y), Cube.mk_mem_prodBoundary (Or.inl rfl)⟩
    · have h := hLb ⟨(t, y), Cube.mk_mem_prodBoundary (Or.inr hy)⟩
      by_cases h0 : t = 0
      · rw [h, h0]
        simpa [bFun] using α.2 y hy
      · by_cases h1 : t = 1
        · rw [h, h1]
          simpa [bFun, one_ne_zero] using β.2 y hy
        · simpa [bFun, h0, h1] using h
  · -- Surjectivity on `π_{n+1}(B, p a)`, via `∂Iⁿ⁺¹ ↪ Iⁿ⁺¹`.
    intro c
    induction c using Quotient.inductionOn with | h γ => ?_
    obtain ⟨G, hG, hGf⟩ := exists_lift_cube_of_mem_rlp_I hp (n + 1)
      (ContinuousMap.const _ a) γ.1 fun y ↦ (γ.2 y.1 y.2).symm
    let α : Ω^ (Fin (n + 1)) E a := ⟨G, fun y hy ↦ hGf ⟨y, hy⟩⟩
    refine ⟨⟦α⟧, ?_⟩
    rw [HomotopyGroup.map_mk]
    congr 1
    exact GenLoop.ext _ _ fun y ↦ (GenLoop.map_apply p.hom rfl α y).trans (congrFun hG y)

end modelCategoryQuillen

end RlpI

/-! ### Disk extensions into weakly contractible spaces -/

section DiskExtension

open scoped Topology Topology.Homotopy
open unitInterval

/-- Any map from the boundary sphere `∂𝔻 (m + 1)` into a path-connected space with trivial
positive-dimensional homotopy groups extends over the disk `𝔻 (m + 1)`. -/
private lemma exists_disk_extension_of_subsingleton_homotopyGroup {F : TopCat.{u}}
    [PathConnectedSpace F]
    (hF : ∀ (k : ℕ) (x : F), Subsingleton (HomotopyGroup (Fin (k + 1)) F x))
    (m : ℕ) (φ : TopCat.diskBoundary.{u} (m + 1) ⟶ F) :
    ∃ Φ : TopCat.disk.{u} (m + 1) ⟶ F, TopCat.diskBoundaryInclusion (m + 1) ≫ Φ = φ := by
  cases m with
  | zero =>
    let e : TopCat.disk.{u} 1 ≃ₜ I^(Fin 1) := diskHomeomorphCube.{u} 1
    obtain ⟨s₀, hs₀⟩ := (diskHomeomorphCube_mem_boundary_iff (e.symm (fun _ ↦ 0))).1
      (by rw [e.apply_symm_apply]; exact Cube.boundary_fin_one_iff.2 (Or.inl rfl))
    obtain ⟨s₁, hs₁⟩ := (diskHomeomorphCube_mem_boundary_iff (e.symm (fun _ ↦ 1))).1
      (by rw [e.apply_symm_apply]; exact Cube.boundary_fin_one_iff.2 (Or.inr rfl))
    let γ : Path (φ s₀) (φ s₁) := PathConnectedSpace.somePath (φ s₀) (φ s₁)
    refine ⟨TopCat.ofHom ⟨fun z ↦ γ (e z 0),
      γ.continuous.comp ((continuous_apply 0).comp e.continuous)⟩, ?_⟩
    ext s
    have hmem := (diskHomeomorphCube_mem_boundary_iff (TopCat.diskBoundaryInclusion 1 s)).2 ⟨s, rfl⟩
    have hinj := (TopCat.mono_iff_injective (TopCat.diskBoundaryInclusion.{u} 1)).1 inferInstance
    rcases Cube.boundary_fin_one_iff.1 hmem with h0 | h1
    · have heq : e (TopCat.diskBoundaryInclusion 1 s) = fun _ ↦ 0 :=
        funext fun i ↦ by rw [Subsingleton.elim i 0]; exact h0
      have hs : s = s₀ := hinj (e.injective (by rw [heq, hs₀, e.apply_symm_apply]))
      change γ (e (TopCat.diskBoundaryInclusion 1 s) 0) = φ s
      rw [h0, hs, γ.source]
    · have heq : e (TopCat.diskBoundaryInclusion 1 s) = fun _ ↦ 1 :=
        funext fun i ↦ by rw [Subsingleton.elim i 0]; exact h1
      have hs : s = s₁ := hinj (e.injective (by rw [heq, hs₁, e.apply_symm_apply]))
      change γ (e (TopCat.diskBoundaryInclusion 1 s) 0) = φ s
      rw [h1, hs, γ.target]
  | succ k =>
    let x₀ : F := φ (ULift.up (sphereNorthPole (k + 1)))
    let p₀ : Ω^ (Fin (k + 1)) F x₀ :=
      (GenLoop.sphereEquiv (k + 1) F x₀).symm ⟨φ.hom.comp ⟨ULift.up, continuous_uliftUp⟩, rfl⟩
    have hmap : GenLoop.diskBoundaryMap p₀ = φ := by
      ext s
      rw [GenLoop.diskBoundaryMap_apply, ← GenLoop.coe_sphereEquiv_apply, Equiv.apply_symm_apply]
      rfl
    have htriv : (⟦p₀⟧ : HomotopyGroup (Fin (k + 1)) F x₀) =
        (1 : HomotopyGroup (Fin (k + 1)) F x₀) :=
      (hF k x₀).elim _ _
    have hnull : φ.hom.Nullhomotopic := by
      rw [← hmap]
      exact (HomotopyGroup.mk_eq_one_iff_nullhomotopic_diskBoundaryMap p₀).1 htriv
    exact (TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq φ).1 hnull

end DiskExtension

/-! ### `serreFibrations ⊓ weakEquivalences ≤ I.rlp` and the headline characterization -/

namespace modelCategoryQuillen

open scoped Topology Topology.Homotopy
open unitInterval

/-- Every trivial Serre fibration (that is, a Serre fibration which is also a weak homotopy
equivalence) has the right lifting property with respect to all disk boundary inclusions
`∂𝔻 n ⟶ 𝔻 n`. -/
theorem serreFibrations_inf_weakEquivalences_le_rlp_I :
    serreFibrations.{u} ⊓ weakEquivalences.{u} ≤ modelCategoryQuillen.I.{u}.rlp := by
  rintro E B p ⟨hp, hw⟩
  rw [mem_rlp_I_iff]
  intro n
  rw [mem_weakEquivalences_iff] at hw
  have hfib := (isWeakHomotopyEquivalence_iff_of_mem_serreFibrations hp).1 hw
  refine ⟨fun {f g} sq ↦ ?_⟩
  cases n with
  | zero =>
    obtain ⟨e⟩ := (hfib (g (diskCenter 0))).1
    refine ⟨⟨{ l := TopCat.ofHom (ContinuousMap.const _ e.1), fac_left := ?_, fac_right := ?_ }⟩⟩
    · ext s
      exact isEmptyElim s
    · ext z
      have hz : z = diskCenter 0 :=
        ULift.ext (Subtype.ext (PiLp.ext fun i ↦ isEmptyElim i))
      rw [hz]
      exact Set.mem_singleton_iff.1 e.2
  | succ m =>
    -- Choose a base point `s₀ ∈ ∂𝔻 (m + 1)` and contract `𝔻 (m + 1)` linearly onto `s₀`.
    let s₀ : TopCat.diskBoundary.{u} (m + 1) := Classical.arbitrary _
    let z₀ : TopCat.disk.{u} (m + 1) := TopCat.diskBoundaryInclusion (m + 1) s₀
    let b₀ : B := g z₀
    let c : C(I × TopCat.disk.{u} (m + 1), TopCat.disk.{u} (m + 1)) :=
      ⟨fun q ↦ ULift.up ⟨(1 - (q.1 : ℝ)) • (q.2.down : EuclideanSpace ℝ (Fin (m + 1))) +
          (q.1 : ℝ) • (z₀.down : EuclideanSpace ℝ (Fin (m + 1))),
        convex_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 q.2.down.2 z₀.down.2
          (sub_nonneg.2 q.1.2.2) q.1.2.1 (sub_add_cancel 1 _)⟩, by fun_prop⟩
    have hc0 (z : TopCat.disk.{u} (m + 1)) : c (0, z) = z := by
      apply ULift.ext; apply Subtype.ext; change (1 - (0 : ℝ)) • _ + (0 : ℝ) • _ = _
      simp
    have hc1 (z : TopCat.disk.{u} (m + 1)) : c (1, z) = z₀ := by
      apply ULift.ext; apply Subtype.ext; change (1 - (1 : ℝ)) • _ + (1 : ℝ) • _ = _
      simp
    -- Lift the homotopy `g ∘ c` restricted to the CW complex `∂𝔻 (m + 1)` starting at `f`.
    have hHLP : HasHomotopyLiftingProperty p (TopCat.diskBoundary.{u} (m + 1)) := by
      let _ := sphereCWComplex (Fintype.card_fin (m + 1))
      exact (Homeomorph.ulift : TopCat.diskBoundary.{u} (m + 1) ≃ₜ
          sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).hasHomotopyLiftingProperty_iff.2
        (hasHomotopyLiftingProperty_of_mem_serreFibrations hp)
    let Hbd : C(I × TopCat.diskBoundary.{u} (m + 1), B) :=
      ⟨fun q ↦ g (c (q.1, TopCat.diskBoundaryInclusion (m + 1) q.2)), by fun_prop⟩
    obtain ⟨L, hLH, hL0⟩ := hHLP f.hom Hbd fun s ↦ by
      change g (c (0, TopCat.diskBoundaryInclusion (m + 1) s)) = p (f s)
      rw [hc0]
      exact (ConcreteCategory.congr_hom sq.w s).symm
    -- At `t = 1`, `L (1, ·)` lands in the weakly contractible fibre `p.fiber b₀`, so it extends
    -- over `𝔻 (m + 1)`.
    have hL1 (s : TopCat.diskBoundary.{u} (m + 1)) : p (L (1, s)) = b₀ := by
      have h := congrFun hLH (1, s)
      simpa [Hbd, hc1, b₀] using h
    let φ : TopCat.diskBoundary.{u} (m + 1) ⟶ p.fiber b₀ :=
      TopCat.ofHom ⟨fun s ↦ ⟨L (1, s), hL1 s⟩, by fun_prop⟩
    obtain ⟨e₀⟩ := (hfib b₀).1
    have : PathConnectedSpace (p.fiber b₀) :=
      (TauCeti.pathConnectedSpace_iff_subsingleton_homotopyGroup_zero e₀).2 ((hfib b₀).2 e₀ 0)
    obtain ⟨Φ, hΦ⟩ := exists_disk_extension_of_subsingleton_homotopyGroup
      (fun k x ↦ (hfib b₀).2 x (k + 1)) m φ
    -- Transport the time-reversed contraction to `closedBall (0 : Fin (m + 1) → ℝ) 1` and apply
    -- relative homotopy lifting.
    let e : TopCat.disk.{u} (m + 1) ≃ₜ closedBall (0 : Fin (m + 1) → ℝ) 1 :=
      diskHomeomorphClosedBall.{u} (m + 1)
    let A : Set (closedBall (0 : Fin (m + 1) → ℝ) 1) := Subtype.val ⁻¹' sphere 0 1
    have htoBd_mem (y : A) :
        (e.symm y.1).down.1 ∈ sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
      rw [mem_sphere_zero_iff_norm, ← mem_range_diskBoundaryInclusion_iff,
        ← norm_diskHomeomorphClosedBall_eq_one_iff]
      change ‖(e (e.symm y.1) : Fin (m + 1) → ℝ)‖ = 1
      rw [e.apply_symm_apply]
      exact mem_sphere_zero_iff_norm.1 y.2
    let toBd : C(A, TopCat.diskBoundary.{u} (m + 1)) :=
      ⟨fun y ↦ ULift.up ⟨(e.symm y.1).down.1, htoBd_mem y⟩,
        continuous_uliftUp.comp ((continuous_subtype_val.comp
          (continuous_uliftDown.comp (e.symm.continuous.comp continuous_subtype_val))).subtype_mk
          htoBd_mem)⟩
    have htoBd_incl (y : A) : TopCat.diskBoundaryInclusion (m + 1) (toBd y) = e.symm y.1 :=
      ULift.ext (Subtype.ext rfl)
    have htoBd_apply (s : TopCat.diskBoundary.{u} (m + 1)) :
        toBd ⟨e (TopCat.diskBoundaryInclusion (m + 1) s),
          mem_sphere_zero_iff_norm.2 ((norm_diskHomeomorphClosedBall_eq_one_iff _).2 ⟨s, rfl⟩)⟩ =
          s := by
      have hinj := (TopCat.mono_iff_injective (TopCat.diskBoundaryInclusion.{u} (m + 1))).1
        inferInstance
      exact hinj ((htoBd_incl _).trans (e.symm_apply_apply _))
    classical
    let fCylFun : cylinderExtensionDomain A → E := fun q ↦
      if hy : q.1.2 ∈ A then L (σ q.1.1, toBd ⟨q.1.2, hy⟩) else (Φ (e.symm q.1.2)).1
    have hfCylCont : Continuous fCylFun := by
      let S₀ : Set (cylinderExtensionDomain A) := {q | q.1.1 = 0}
      let S₁ : Set (cylinderExtensionDomain A) := {q | q.1.2 ∈ A}
      have hcover : S₀ ∪ S₁ = univ := by
        ext q
        simpa [S₀, S₁] using mem_cylinderExtensionDomain_iff.1 q.2
      have hS₀ : IsClosed S₀ :=
        isClosed_singleton.preimage (continuous_fst.comp continuous_subtype_val)
      have hS₁ : IsClosed S₁ :=
        (isClosed_sphere.preimage continuous_subtype_val).preimage
          (continuous_snd.comp continuous_subtype_val)
      rw [← continuousOn_univ, ← hcover]
      refine ContinuousOn.union_of_isClosed ?_ ?_ hS₀ hS₁
      · refine (continuous_subtype_val.comp
            (Φ.hom.continuous.comp (e.symm.continuous.comp
              (continuous_snd.comp continuous_subtype_val)))).continuousOn.congr fun q hq ↦ ?_
        have hq0 : q.1.1 = 0 := hq
        by_cases hy : q.1.2 ∈ A
        · simp only [fCylFun, hy, ↓reduceDIte, hq0, symm_zero]
          have hφs := ConcreteCategory.congr_hom hΦ (toBd ⟨q.1.2, hy⟩)
          change Φ (TopCat.diskBoundaryInclusion (m + 1) (toBd ⟨q.1.2, hy⟩)) =
            φ (toBd ⟨q.1.2, hy⟩) at hφs
          rw [htoBd_incl] at hφs
          exact (congrArg Subtype.val hφs).symm
        · simp [fCylFun, hy]
      · refine continuousOn_iff_continuous_domRestrict.2 <|
          (L.continuous.comp ((unitInterval.continuous_symm.comp
            (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))).prodMk
            (toBd.continuous.comp ((continuous_snd.comp
              (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
              fun q : S₁ ↦ q.2)))).congr fun q ↦ ?_
        have hy : q.1.1.2 ∈ A := q.2
        simp [fCylFun, hy]
    let K : C(I × closedBall (0 : Fin (m + 1) → ℝ) 1, B) :=
      ⟨fun q ↦ g (c (σ q.1, e.symm q.2)), by fun_prop⟩
    have hfCylProj (q : cylinderExtensionDomain A) : p (fCylFun q) = K q.1 := by
      by_cases hy : q.1.2 ∈ A
      · simp only [fCylFun, hy, ↓reduceDIte]
        have h := congrFun hLH (σ q.1.1, toBd ⟨q.1.2, hy⟩)
        simpa [Hbd, K, htoBd_incl] using h
      · have hq0 : q.1.1 = 0 := (mem_cylinderExtensionDomain_iff.1 q.2).resolve_right hy
        simp only [fCylFun, hy, ↓reduceDIte]
        change p (Φ (e.symm q.1.2)).1 = g (c (σ q.1.1, e.symm q.1.2))
        rw [hq0, symm_zero, hc1]
        exact Set.mem_singleton_iff.1 (Φ (e.symm q.1.2)).2
    obtain ⟨G, hGK, hGf⟩ := exists_lift_closedBall_of_mem_serreFibrations hp
      ⟨fCylFun, hfCylCont⟩ K hfCylProj
    let l : TopCat.disk.{u} (m + 1) ⟶ E :=
      TopCat.ofHom ⟨fun z ↦ G (1, e z), G.continuous.comp (continuous_const.prodMk e.continuous)⟩
    refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
    · ext s
      have hsA : e (TopCat.diskBoundaryInclusion (m + 1) s) ∈ A :=
        mem_sphere_zero_iff_norm.2 ((norm_diskHomeomorphClosedBall_eq_one_iff _).2 ⟨s, rfl⟩)
      have h := hGf ⟨(1, e (TopCat.diskBoundaryInclusion (m + 1) s)),
        mem_cylinderExtensionDomain_of_mem hsA⟩
      change G (1, e (TopCat.diskBoundaryInclusion (m + 1) s)) = f s
      rw [h]
      simp only [ContinuousMap.coe_mk, fCylFun, hsA, ↓reduceDIte, symm_one, htoBd_apply]
      exact hL0 s
    · ext z
      change p (G (1, e z)) = g z
      have h := congrFun hGK (1, e z)
      simpa [K, hc0] using h

/-- **Characterization of trivial fibrations in the Quillen–Serre model structure on `TopCat`.**
A morphism has the right lifting property with respect to all disk boundary inclusions
`∂𝔻 n ⟶ 𝔻 n` if and only if it is both a Serre fibration and a weak homotopy equivalence. -/
theorem rlp_I : modelCategoryQuillen.I.{u}.rlp = serreFibrations.{u} ⊓ weakEquivalences.{u} :=
  le_antisymm (le_inf rlp_I_le_serreFibrations rlp_I_le_weakEquivalences)
    serreFibrations_inf_weakEquivalences_le_rlp_I

end modelCategoryQuillen

end TauCeti.TopCat
