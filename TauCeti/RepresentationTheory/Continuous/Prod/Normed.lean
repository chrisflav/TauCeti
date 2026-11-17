/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Prod
public import TauCeti.RepresentationTheory.Continuous.Prod.Basic

/-!
# Operator-norm and bounded-convergence properties of product representations

For any normed field `𝕜` and arbitrary topological `𝕜`-vector spaces, continuity of a binary or
arbitrary indexed product into the topology of bounded convergence (the operator-norm topology on
seminormed spaces) is equivalent to continuity of every factor
(`ContRepresentation.continuous_prod_iff`, `ContRepresentation.continuous_pi_iff`). On seminormed
spaces over a nontrivially normed field `𝕜`, the product representation satisfies
`‖(π.prod ρ) g‖ = max ‖π g‖ ‖ρ g‖` (`ContRepresentation.norm_prod_apply`), and for a finite index
type `ι`, `‖pi π g‖ ≤ C ↔ ∀ i, ‖π i g‖ ≤ C` for `0 ≤ C`
(`ContRepresentation.norm_pi_apply_le_iff`).

These results are separated from `TauCeti.RepresentationTheory.Continuous.Prod.Basic` so that
purely algebraic and topological consumers (such as `TopRep` and continuous cohomology) do not
pull normed-space typeclass instances into their environment.

## Main results

* `ContRepresentation.continuous_prod_iff` and `ContRepresentation.continuous_pi_iff`:
  continuity into the topology of bounded convergence holds iff every factor is continuous.
* `ContRepresentation.norm_prod_apply`, `ContRepresentation.norm_pi_apply`,
  `ContRepresentation.norm_pi_apply_le_iff`, and `ContRepresentation.norm_apply_le_norm_pi`:
  operator-norm formulas for binary and finite indexed products.
-/

public section

namespace ContRepresentation

section ProdTopology

open Filter Topology

variable {𝕜 G V W : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module 𝕜 V]
  [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module 𝕜 W]

/-- The binary product `π.prod ρ` is continuous for the topology of bounded convergence (the
operator-norm topology on seminormed spaces) if and only if both factors are. -/
theorem continuous_prod_iff (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W) :
    Continuous (π.prod ρ) ↔ Continuous π ∧ Continuous ρ := by
  constructor
  · intro h
    refine ⟨continuous_iff_continuousAt.mpr fun g₀ ↦ ?_,
      continuous_iff_continuousAt.mpr fun g₀ ↦ ?_⟩
    · rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
        ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
      rintro ⟨S, U⟩ ⟨hS, hU⟩
      have hg₀ := ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff.mp
        (tendsto_sub_nhds_zero_iff.mpr (h.continuousAt (x := g₀)))
      refine (hg₀ (ContinuousLinearMap.inl 𝕜 V W '' S, Prod.fst ⁻¹' U)
        ⟨hS.image (ContinuousLinearMap.inl 𝕜 V W),
          continuous_fst.continuousAt (by simpa using hU)⟩).mono fun g hg v hv ↦ ?_
      simpa using hg (v, 0) ⟨v, hv, rfl⟩
    · rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
        ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
      rintro ⟨S, U⟩ ⟨hS, hU⟩
      have hg₀ := ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff.mp
        (tendsto_sub_nhds_zero_iff.mpr (h.continuousAt (x := g₀)))
      refine (hg₀ (ContinuousLinearMap.inr 𝕜 V W '' S, Prod.snd ⁻¹' U)
        ⟨hS.image (ContinuousLinearMap.inr 𝕜 V W),
          continuous_snd.continuousAt (by simpa using hU)⟩).mono fun g hg w hw ↦ ?_
      simpa using hg (0, w) ⟨w, hw, rfl⟩
  · rintro ⟨hπ, hρ⟩
    refine continuous_iff_continuousAt.mpr fun g₀ ↦ ?_
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
      ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
    rintro ⟨S, U⟩ ⟨hS, hU⟩
    rw [← Prod.mk_zero_zero, nhds_prod_eq, Filter.mem_prod_iff] at hU
    obtain ⟨U₁, hU₁, U₂, hU₂, hUsub⟩ := hU
    have h1 := ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff.mp
      (tendsto_sub_nhds_zero_iff.mpr (hπ.continuousAt (x := g₀)))
      (ContinuousLinearMap.fst 𝕜 V W '' S, U₁)
      ⟨hS.image (ContinuousLinearMap.fst 𝕜 V W), hU₁⟩
    have h2 := ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff.mp
      (tendsto_sub_nhds_zero_iff.mpr (hρ.continuousAt (x := g₀)))
      (ContinuousLinearMap.snd 𝕜 V W '' S, U₂)
      ⟨hS.image (ContinuousLinearMap.snd 𝕜 V W), hU₂⟩
    filter_upwards [h1, h2] with g hg₁ hg₂ p hp
    exact hUsub (by simpa [prod_apply_apply] using ⟨hg₁ p.1 ⟨p, hp, rfl⟩, hg₂ p.2 ⟨p, hp, rfl⟩⟩)

end ProdTopology

section ProdNormed

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [Monoid G]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The operator norm of `(π.prod ρ) g` is `max ‖π g‖ ‖ρ g‖`. -/
@[simp]
theorem norm_prod_apply (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)
    (g : G) : ‖(π.prod ρ) g‖ = max ‖π g‖ ‖ρ g‖ := by
  rw [prod_apply]
  exact ContinuousLinearMap.opNorm_prodMap (π g) (ρ g)

end ProdNormed

section PiTopology

open Filter Topology

variable {𝕜 G ι : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, IsTopologicalAddGroup (V i)] [∀ i, Module 𝕜 (V i)]

/-- An indexed product `pi π` (over an arbitrary, possibly infinite index type `ι`) is continuous
for the topology of bounded convergence (the operator-norm topology when `ι` is finite and the
`V i` are seminormed) if and only if every factor `π i` is. -/
theorem continuous_pi_iff (π : ∀ i, ContRepresentation 𝕜 G (V i)) :
    Continuous (pi π) ↔ ∀ i, Continuous (π i) := by
  classical
  constructor
  · intro h i
    refine continuous_iff_continuousAt.mpr fun g₀ ↦ ?_
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
      ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
    rintro ⟨S, U⟩ ⟨hS, hU⟩
    let L : V i →L[𝕜] (∀ j, V j) := ContinuousLinearMap.single 𝕜 V i
    have hg₀ := ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff.mp
      (tendsto_sub_nhds_zero_iff.mpr (h.continuousAt (x := g₀)))
    refine (hg₀ (L '' S, (fun x : ∀ j, V j ↦ x i) ⁻¹' U)
      ⟨hS.image L, (continuous_apply i).continuousAt (by simpa using hU)⟩).mono
      fun g hg v hv ↦ ?_
    simpa [L, Pi.single_eq_same] using hg (L v) ⟨v, hv, rfl⟩
  · intro h
    refine continuous_iff_continuousAt.mpr fun g₀ ↦ ?_
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
      ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]
    rintro ⟨S, U⟩ ⟨hS, hU⟩
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hIfin, W, hW, hWU⟩ := hU
    have hmem : ∀ i ∈ I, ∀ᶠ g in 𝓝 g₀,
        ∀ v ∈ ContinuousLinearMap.proj (R := 𝕜) i '' S,
          (π i g - π i g₀) v ∈ W i := fun i _ ↦
      ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff.mp
        (tendsto_sub_nhds_zero_iff.mpr ((h i).continuousAt (x := g₀)))
        (ContinuousLinearMap.proj (R := 𝕜) i '' S, W i)
        ⟨hS.image (ContinuousLinearMap.proj (R := 𝕜) i), hW i⟩
    filter_upwards [(hIfin.eventually_all.mpr hmem)] with g hg x hx
    exact hWU fun i hi ↦ by simpa [pi_apply_apply] using hg i hi (x i) ⟨x, hx, rfl⟩

end PiTopology

section PiNormed

variable {𝕜 G ι : Type*} [NontriviallyNormedField 𝕜] [Monoid G] [Fintype ι]
  {V : ι → Type*} [∀ i, SeminormedAddCommGroup (V i)] [∀ i, NormedSpace 𝕜 (V i)]

/-- For a finite index type, the operator norm of `pi π g` equals the supremum norm
`‖fun i ↦ π i g‖`. -/
@[simp]
theorem norm_pi_apply (π : ∀ i, ContRepresentation 𝕜 G (V i)) (g : G) :
    ‖pi π g‖ = ‖fun i ↦ π i g‖ := by
  rw [pi_apply]
  exact ContinuousLinearMap.opNorm_pi_comp_proj (fun i ↦ π i g)

/-- For a finite index type and `0 ≤ C`, the operator norm of `pi π g` is at most `C` if and only
if every factor satisfies `‖π i g‖ ≤ C`. -/
theorem norm_pi_apply_le_iff (π : ∀ i, ContRepresentation 𝕜 G (V i)) {C : ℝ}
    (hC : 0 ≤ C) (g : G) : ‖pi π g‖ ≤ C ↔ ∀ i, ‖π i g‖ ≤ C := by
  rw [norm_pi_apply, pi_norm_le_iff_of_nonneg hC]

/-- The operator norm of each factor is bounded by the operator norm of a finite product. -/
theorem norm_apply_le_norm_pi (π : ∀ i, ContRepresentation 𝕜 G (V i)) (g : G) (i : ι) :
    ‖π i g‖ ≤ ‖pi π g‖ :=
  (norm_pi_apply_le_iff π (norm_nonneg _) g).mp le_rfl i

end PiNormed

end ContRepresentation
