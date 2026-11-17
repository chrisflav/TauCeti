/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Baire.LocallyCompactRegular
public import TauCeti.Analysis.LocallyConvex.StrongOperatorTopology
public import TauCeti.RepresentationTheory.Continuous.Prod.Basic
public import TauCeti.RepresentationTheory.Continuous.RestrictScalars.Basic
public import TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# Strong continuity, local operator bounds, and joint continuity

A continuous representation `π` of a topological monoid is *strongly continuous* when every
orbit `g ↦ π g v` is continuous. This is weaker than continuity of `g ↦ π g` into the continuous
linear endomorphisms, which carry the topology of uniform convergence on bounded sets (the
operator-norm topology on a normed space): translation by `ℝ` on `L²(ℝ)` is strongly continuous
but not continuous. In finite dimensions the two notions agree by Mathlib's `continuous_clm_apply`,
which is how finite-dimensional pieces of a strongly continuous representation become genuine
continuous representations.

This file develops the core theory of strongly continuous representations across three regimes:

1. **Permanence of orbit and strong continuity** (for arbitrary topological `R`-modules, with no
   norm assumptions): trivial actions, norm-continuous actions, restriction along continuous monoid
   homomorphisms (including subgroups, with a converse for open subgroups) and conjugation
   `MulAut.conj`, scalar restriction (`ContRepresentation.restrictScalars`, covering realification
   `ℂ → ℝ` and forgetting scalars to `ℤ`), binary and arbitrary indexed products
   (`ContRepresentation.prod`, `ContRepresentation.pi`), subrepresentations, quotients, continuous
   intertwiners, and equivalences. For a group with continuous multiplication, continuity of a
   single orbit everywhere is equivalent to continuity at `1`
   (`ContRepresentation.continuous_apply_iff_continuousAt_one`), and global lower/upper
   semicontinuity of `g ↦ ‖π g v‖` propagates from `1` via right translation
   (`ContRepresentation.lowerSemicontinuous_norm_apply_of_lowerSemicontinuousAt_one`,
   `ContRepresentation.upperSemicontinuous_norm_apply_of_upperSemicontinuousAt_one`).
2. **Local operator-norm bounds and joint continuity without completeness or barrelledness** (for
   seminormed spaces over a nontrivially normed field `𝕜`):
   * *Monoid criterion* (`ContRepresentation.continuous_apply_prod_iff`, Bernstein–Krötz
     Lemma 2.3): `(g, v) ↦ π g v` is jointly continuous if and only if `π` is strongly
     continuous and locally uniformly operator-norm bounded.
   * *Group propagation* (`ContRepresentation.eventually_nhds_norm_le_of_eventually_nhds_one`,
     `ContRepresentation.exists_norm_le_of_isCompact_of_eventually_nhds_one`,
     `ContRepresentation.continuous_apply_prod_iff_of_group`): for a group with continuous
     multiplication, a norm bound on a single neighborhood of `1` propagates to every point and
     every compact set.
   * *Baire group regime* (`ContRepresentation.exists_nhds_one_norm_le_of_baireSpace`,
     `ContRepresentation.exists_norm_le_of_isCompact_of_baireSpace`,
     `ContRepresentation.continuous_apply_prod_of_baireSpace`): when `G` is a Baire space with
     continuous multiplication (automatically satisfied by every locally compact `R1Space` group
     via `Mathlib.Topology.Baire.LocallyCompactRegular`, and every completely pseudometrizable
     group via `Mathlib.Topology.Baire.CompleteMetrizable`), lower semicontinuity of `g ↦ ‖π g v‖`
     at `1` already propagates globally and produces local and compact operator-norm bounds, and
     strong continuity at `1` implies joint continuity, with **no** barrelledness or completeness
     assumption on `V`.
3. **Barrelled-space regime** (`[BarrelledSpace 𝕜 V]`, automatically synthesized from
   `[CompleteSpace V]`, Bernstein–Krötz Remark 2.4(a)–(b)): works for arbitrary topological
   monoids and non-Baire topological groups via Banach–Steinhaus, yielding uniform operator-norm
   bounds on compact sets (`ContRepresentation.exists_norm_le_of_isCompact_upperSemicontinuousOn`,
   `ContRepresentation.exists_norm_le_of_isCompact_continuousOn`,
   `ContRepresentation.exists_norm_le_of_isCompact`), on compact neighborhoods in weakly locally
   compact spaces (`ContRepresentation.exists_compact_nhds_norm_le`), and at points with countably
   generated neighborhood filters
   (`ContRepresentation.exists_nhds_norm_le_of_isCountablyGenerated`), together with joint
   continuity in each case.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), Lemma 2.3 and Remark 2.4.
-/

public section

open Filter Topology

namespace ContRepresentation

section SubrepresentationQuotient

variable {R G V : Type*} [Ring R] [Monoid G] [TopologicalSpace G] [AddCommGroup V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  {π : ContRepresentation R G V} {W : Submodule R V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- Restricting a strongly continuous representation to an invariant submodule gives a strongly
continuous representation. -/
theorem continuous_subrepresentation_apply (hπ : ∀ v, Continuous fun g ↦ π g v) (w : W) :
    Continuous fun g ↦ subrepresentation π W hW g w := by
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  simpa only [Function.comp_def, coe_subrepresentation_apply] using hπ w

/-- Descending a strongly continuous representation to the quotient by an invariant submodule
gives a strongly continuous representation. -/
theorem continuous_quotient_apply (hπ : ∀ v, Continuous fun g ↦ π g v) (x : V ⧸ W) :
    Continuous fun g ↦ quotient π W hW g x := by
  obtain ⟨v, rfl⟩ := W.mkQ_surjective x
  simp only [Submodule.mkQ_apply, quotient_apply_mk]
  exact W.mkQL.continuous.comp (hπ v)

end SubrepresentationQuotient

/-! ### Permanence of orbit and strong continuity -/

section Permanence

variable {R G V : Type*} [Ring R] [Monoid G] [TopologicalSpace G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]

/-- Every orbit of the trivial representation is continuous. -/
theorem continuous_trivial_apply (R G V : Type*) [Ring R] [Monoid G] [TopologicalSpace G]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V] (v : V) :
    Continuous fun g : G ↦ trivial R G V g v :=
  continuous_const

/-- Continuity into the topology of bounded convergence (the operator-norm topology on seminormed
spaces) implies strong continuity. -/
theorem continuous_apply_of_continuous {𝕜 : Type*} [NormedField 𝕜]
    [Module 𝕜 V] [ContinuousSMul 𝕜 V] {π : ContRepresentation 𝕜 G V}
    (hπ : Continuous π) (v : V) :
    Continuous fun g ↦ π g v :=
  (continuous_eval_const v).comp hπ

/-- Restricting a continuous representation along a continuous monoid homomorphism preserves
continuity of each orbit. Taking `φ = H.subtype` gives restriction to any subgroup (open, closed,
or arbitrary). -/
theorem continuous_restrict_apply {H : Type*} [Monoid H] [TopologicalSpace H]
    {π : ContRepresentation R G V} (φ : H →* G) (hφ : Continuous φ) {v : V}
    (hv : Continuous fun g ↦ π g v) :
    Continuous fun h ↦ π.restrict φ h v :=
  hv.comp hφ

/-- Restricting scalars does not change continuity of any orbit. -/
theorem continuous_restrictScalars_apply_iff (S : Type*) [Ring S] [Module S V]
    [LinearMap.CompatibleSMul V V S R] (π : ContRepresentation R G V) (v : V) :
    (Continuous fun g ↦ π.restrictScalars S g v) ↔ Continuous fun g ↦ π g v := by
  simp only [restrictScalars_apply_apply]

/-- An orbit of a binary product representation is continuous if and only if both factor orbits are
continuous. -/
theorem continuous_prod_apply_iff {W : Type*} [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [Module R W] (π : ContRepresentation R G V)
    (ρ : ContRepresentation R G W) (v : V × W) :
    (Continuous fun g ↦ (π.prod ρ) g v) ↔
      (Continuous fun g ↦ π g v.1) ∧ Continuous fun g ↦ ρ g v.2 := by
  simp only [prod_apply_apply]
  exact continuous_prodMk

/-- A binary product representation is strongly continuous if and only if both factors are strongly
continuous. -/
theorem forall_continuous_prod_apply_iff {W : Type*} [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [Module R W] (π : ContRepresentation R G V)
    (ρ : ContRepresentation R G W) :
    (∀ v, Continuous fun g ↦ (π.prod ρ) g v) ↔
      (∀ v, Continuous fun g ↦ π g v) ∧ ∀ w, Continuous fun g ↦ ρ g w := by
  refine ⟨fun h ↦ ⟨fun v ↦ ((continuous_prod_apply_iff π ρ (v, 0)).mp (h (v, 0))).1,
    fun w ↦ ((continuous_prod_apply_iff π ρ (0, w)).mp (h (0, w))).2⟩, ?_⟩
  rintro ⟨hπ, hρ⟩ v
  exact (continuous_prod_apply_iff π ρ v).mpr ⟨hπ v.1, hρ v.2⟩

/-- An orbit of an arbitrary indexed product representation is continuous if and only if every
coordinate orbit is continuous. -/
theorem continuous_pi_apply_iff {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, Module R (E i)]
    (π : ∀ i, ContRepresentation R G (E i)) (x : ∀ i, E i) :
    (Continuous fun g ↦ pi π g x) ↔ ∀ i, Continuous fun g ↦ π i g (x i) := by
  rw [_root_.continuous_pi_iff]
  simp only [pi_apply_apply]

/-- An arbitrary indexed product representation is strongly continuous if and only if every factor
is strongly continuous. -/
theorem forall_continuous_pi_apply_iff {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, Module R (E i)]
    (π : ∀ i, ContRepresentation R G (E i)) :
    (∀ x, Continuous fun g ↦ pi π g x) ↔ ∀ i v, Continuous fun g ↦ π i g v := by
  classical
  refine ⟨fun h i v ↦ ?_, fun h x ↦ (continuous_pi_apply_iff π x).mpr fun i ↦ h i (x i)⟩
  simpa [Pi.single_eq_same] using
    (continuous_pi_apply_iff π (Pi.single i v)).mp (h (Pi.single i v)) i

end Permanence

section Intertwiner

variable {R G V W : Type*} [Ring R] [Monoid G] [TopologicalSpace G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module R W]
  {π : ContRepresentation R G V} {ρ : ContRepresentation R G W}

/-- A continuous intertwining map carries vectors with continuous orbits to vectors with
continuous orbits. -/
theorem _root_.ContIntertwiningMap.continuous_apply (f : π →ⁱL ρ) {v : V}
    (hv : Continuous fun g ↦ π g v) :
    Continuous fun g ↦ ρ g (f v) := by
  have heq : (fun g ↦ ρ g (f v)) = fun g ↦ f (π g v) :=
    funext fun g ↦ (f.isIntertwining g v).symm
  rw [heq]
  exact f.continuous.comp hv

/-- A surjective continuous intertwining map pushes strong continuity forward. -/
theorem _root_.ContIntertwiningMap.continuous_apply_of_surjective (f : π →ⁱL ρ)
    (hf : Function.Surjective f) (hπ : ∀ v, Continuous fun g ↦ π g v) (w : W) :
    Continuous fun g ↦ ρ g w := by
  obtain ⟨v, rfl⟩ := hf w
  exact f.continuous_apply (hπ v)

/-- Along an inducing continuous intertwining map, an orbit in the domain is continuous if and only
if its image orbit in the codomain is continuous. -/
theorem _root_.ContIntertwiningMap.continuous_apply_iff_of_isInducing (f : π →ⁱL ρ)
    (hf : Topology.IsInducing f) (v : V) :
    (Continuous fun g ↦ π g v) ↔ Continuous fun g ↦ ρ g (f v) := by
  refine ⟨f.continuous_apply, fun h ↦ ?_⟩
  rw [hf.continuous_iff]
  have heq : f ∘ (fun g ↦ π g v) = fun g ↦ ρ g (f v) :=
    funext fun g ↦ f.isIntertwining g v
  rwa [heq]

/-- An equivalence of continuous representations preserves continuity of individual orbits. -/
theorem Equiv.continuous_apply_iff (e : π.Equiv ρ) (v : V) :
    (Continuous fun g ↦ ρ g (e v)) ↔ Continuous fun g ↦ π g v :=
  (e.toContIntertwiningMap.continuous_apply_iff_of_isInducing
    e.toContinuousLinearEquiv.toHomeomorph.isInducing v).symm

/-- An equivalence of continuous representations preserves strong continuity. -/
theorem Equiv.forall_continuous_apply_iff (e : π.Equiv ρ) :
    (∀ w, Continuous fun g ↦ ρ g w) ↔ ∀ v, Continuous fun g ↦ π g v :=
  ⟨fun h v ↦ (e.continuous_apply_iff v).mp (h (e v)), fun h w ↦ by
    simpa [Equiv.apply_symm_apply] using (e.continuous_apply_iff (e.symm w)).mpr (h (e.symm w))⟩

end Intertwiner

/-! ### Orbit continuity for groups -/

section GroupOrbits

variable {R G V : Type*} [Ring R] [Group G] [TopologicalSpace G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]

/-- For a group with continuous multiplication, continuity of a single orbit `g ↦ π g v` at `1`
implies global continuity of that orbit. Continuous inversion is not needed. -/
theorem continuous_apply_of_continuousAt_one [ContinuousMul G] {π : ContRepresentation R G V}
    {v : V} (hv : ContinuousAt (fun g ↦ π g v) 1) :
    Continuous fun g ↦ π g v := by
  refine continuous_iff_continuousAt.mpr fun g₀ ↦ ?_
  have hmul : ContinuousAt (fun g ↦ g₀⁻¹ * g) g₀ :=
    (continuous_const.mul continuous_id).continuousAt
  have hcomp : ContinuousAt (fun g ↦ π g₀ (π (g₀⁻¹ * g) v)) g₀ :=
    (π g₀).continuous.continuousAt.comp (hv.comp_of_eq hmul (inv_mul_cancel g₀))
  refine hcomp.congr (Eventually.of_forall fun g ↦ ?_)
  dsimp only
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    mul_inv_cancel_left]

/-- For a group with continuous multiplication, a single orbit is continuous everywhere if and only
if it is continuous at `1`. -/
theorem continuous_apply_iff_continuousAt_one [ContinuousMul G] (π : ContRepresentation R G V)
    (v : V) :
    (Continuous fun g ↦ π g v) ↔ ContinuousAt (fun g ↦ π g v) 1 :=
  ⟨fun h ↦ h.continuousAt, continuous_apply_of_continuousAt_one⟩

/-- For an open subgroup `H` of a group with continuous multiplication, an orbit is continuous on
`H` if and only if it is continuous on the whole group `G`. -/
theorem continuous_restrict_subtype_iff_of_isOpen [ContinuousMul G] {H : Subgroup G}
    (hH : IsOpen (H : Set G)) (π : ContRepresentation R G V) (v : V) :
    (Continuous fun h : H ↦ π.restrict H.subtype h v) ↔ Continuous fun g ↦ π g v := by
  refine ⟨fun h ↦ continuous_apply_of_continuousAt_one ?_,
    continuous_restrict_apply H.subtype continuous_subtype_val⟩
  have hwithin : ContinuousWithinAt (fun g ↦ π g v) (H : Set G) 1 :=
    (continuousWithinAt_iff_continuousAt_domRestrict
      (fun g ↦ π g v) H.one_mem).mpr h.continuousAt
  exact hwithin.continuousAt (hH.mem_nhds H.one_mem)

/-- Conjugating a representation by a group element preserves continuity of every orbit, assuming
only continuous multiplication. -/
theorem continuous_restrict_conj_apply_iff [ContinuousMul G] (π : ContRepresentation R G V)
    (a : G) (v : V) :
    (Continuous fun g ↦ π.restrict (MulAut.conj a).toMonoidHom g v) ↔
      Continuous fun g ↦ π g v := by
  refine ⟨fun h ↦ ?_,
    fun h ↦ h.comp ((continuous_const.mul continuous_id).mul continuous_const)⟩
  have hconj : Continuous fun g : G ↦ a⁻¹ * g * a :=
    (continuous_const.mul continuous_id).mul continuous_const
  have heq : (fun g ↦ π g v) =
      (fun g ↦ π.restrict (MulAut.conj a).toMonoidHom g v) ∘ (fun g ↦ a⁻¹ * g * a) := by
    funext g
    simp only [Function.comp_apply, restrict_apply_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [mul_assoc, mul_inv_cancel_right, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [heq]
  exact h.comp hconj

/-- For a group with continuous inversion, `g ↦ π g⁻¹ v` is continuous if and only if
`g ↦ π g v` is continuous. -/
theorem continuous_inv_apply_iff [ContinuousInv G] (π : ContRepresentation R G V) (v : V) :
    (Continuous fun g ↦ π g⁻¹ v) ↔ Continuous fun g ↦ π g v :=
  (Homeomorph.inv G).comp_continuous_iff' (f := fun g ↦ π g v)

end GroupOrbits

section GroupSemicontinuity

variable {R G V : Type*} [Ring R] [Group G] [TopologicalSpace G] [ContinuousMul G]
  [SeminormedAddCommGroup V] [Module R V]

/-- For a group with continuous multiplication, lower semicontinuity of every pointwise norm
`g ↦ ‖π g v‖` at `1` propagates to global lower semicontinuity via right translation
`π g v = π (g * g₀⁻¹) (π g₀ v)`. -/
theorem lowerSemicontinuous_norm_apply_of_lowerSemicontinuousAt_one
    {π : ContRepresentation R G V}
    (hπ : ∀ v : V, LowerSemicontinuousAt (fun g ↦ ‖π g v‖) 1) (v : V) :
    LowerSemicontinuous fun g ↦ ‖π g v‖ := by
  intro g₀ y hy
  have hmul : Tendsto (fun g ↦ g * g₀⁻¹) (𝓝 g₀) (𝓝 1) := by
    have hcont : Continuous fun g : G ↦ g * g₀⁻¹ := continuous_id.mul continuous_const
    simpa [mul_inv_cancel] using (hcont.continuousAt (x := g₀)).tendsto
  have h1 : y < ‖π 1 (π g₀ v)‖ := by simpa using hy
  refine (hmul.eventually (hπ (π g₀ v) y h1)).mono fun g hg ↦ ?_
  have heq : π (g * g₀⁻¹) (π g₀ v) = π g v := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      inv_mul_cancel_right]
  dsimp only at hg ⊢
  rwa [heq] at hg

/-- For a group with continuous multiplication, upper semicontinuity of every pointwise norm
`g ↦ ‖π g v‖` at `1` propagates to global upper semicontinuity via right translation
`π g v = π (g * g₀⁻¹) (π g₀ v)`. -/
theorem upperSemicontinuous_norm_apply_of_upperSemicontinuousAt_one
    {π : ContRepresentation R G V}
    (hπ : ∀ v : V, UpperSemicontinuousAt (fun g ↦ ‖π g v‖) 1) (v : V) :
    UpperSemicontinuous fun g ↦ ‖π g v‖ := by
  intro g₀ y hy
  have hmul : Tendsto (fun g ↦ g * g₀⁻¹) (𝓝 g₀) (𝓝 1) := by
    have hcont : Continuous fun g : G ↦ g * g₀⁻¹ := continuous_id.mul continuous_const
    simpa [mul_inv_cancel] using (hcont.continuousAt (x := g₀)).tendsto
  have h1 : ‖π 1 (π g₀ v)‖ < y := by simpa using hy
  refine (hmul.eventually (hπ (π g₀ v) y h1)).mono fun g hg ↦ ?_
  have heq : π (g * g₀⁻¹) (π g₀ v) = π g v := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      inv_mul_cancel_right]
  dsimp only at hg ⊢
  rwa [heq] at hg

end GroupSemicontinuity

/-! ### Local operator-norm bounds and joint continuity (no completeness or barrelledness) -/

section Normed

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

section Monoid

variable [Monoid G] [TopologicalSpace G]

/-- **Equicontinuity / joint continuity criterion (Bernstein–Krötz, Lemma 2.3).** The action
`(g, v) ↦ π g v` of a topological monoid on a seminormed space is jointly continuous if and only
if `π` is strongly continuous and locally uniformly operator-norm bounded around every point of
`G`. No completeness or barrelledness on `V` is needed. -/
theorem continuous_apply_prod_iff (π : ContRepresentation 𝕜 G V) :
    Continuous (fun p : G × V ↦ π p.1 p.2) ↔
      (∀ v : V, Continuous fun g ↦ π g v) ∧
        ∀ g₀ : G, ∃ U ∈ 𝓝 g₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ U, ‖π g‖ ≤ C :=
  ContinuousLinearMap.continuous_uncurry_iff (T := π)

end Monoid

section Group

variable [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- In a group with continuous multiplication, an operator-norm bound near `1` propagates to a
neighborhood of every `g₀ : G` by left translation. No strong continuity or continuous inversion
is needed. -/
theorem eventually_nhds_norm_le_of_eventually_nhds_one (π : ContRepresentation 𝕜 G V) {C : ℝ}
    (hC : ∀ᶠ g in 𝓝 (1 : G), ‖π g‖ ≤ C) (g₀ : G) :
    ∀ᶠ g in 𝓝 g₀, ‖π g‖ ≤ ‖π g₀‖ * C := by
  have hmul : Tendsto (fun g ↦ g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    have hcont : Continuous fun g : G ↦ g₀⁻¹ * g := continuous_const.mul continuous_id
    simpa [inv_mul_cancel] using (hcont.continuousAt (x := g₀)).tendsto
  refine (hmul.eventually hC).mono fun g hg ↦ ?_
  have hEq : π g = (π g₀).comp (π (g₀⁻¹ * g)) := by
    rw [← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel_left]
  rw [hEq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left hg (norm_nonneg _))

/-- Existential form of `eventually_nhds_norm_le_of_eventually_nhds_one`: a uniform operator-norm
bound on some neighborhood of `1` yields a nonnegative uniform bound on a neighborhood of every
point `g₀ : G`. -/
theorem exists_nhds_norm_le_of_exists_nhds_one_norm_le (π : ContRepresentation 𝕜 G V)
    (h : ∃ U ∈ 𝓝 (1 : G), ∃ C : ℝ, ∀ g ∈ U, ‖π g‖ ≤ C) (g₀ : G) :
    ∃ U ∈ 𝓝 g₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ U, ‖π g‖ ≤ C := by
  obtain ⟨U, hU, C, hC⟩ := h
  have hC₀ : 0 ≤ C := (norm_nonneg (π 1)).trans (hC 1 (mem_of_mem_nhds hU))
  refine ⟨{g | ‖π g‖ ≤ ‖π g₀‖ * C},
    eventually_nhds_norm_le_of_eventually_nhds_one π (eventually_of_mem hU hC) g₀,
    ‖π g₀‖ * C, mul_nonneg (norm_nonneg _) hC₀, fun _ hg ↦ hg⟩

/-- In a group with continuous multiplication, an operator-norm bound near `1` yields a uniform
nonnegative operator-norm bound on every compact subset `K`. No strong continuity, barrelledness,
or completeness is needed. -/
theorem exists_norm_le_of_isCompact_of_eventually_nhds_one (π : ContRepresentation 𝕜 G V)
    {C : ℝ} (hC : ∀ᶠ g in 𝓝 (1 : G), ‖π g‖ ≤ C) {K : Set G} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g ∈ K, ‖π g‖ ≤ M := by
  have hcov := hK.elim_nhds_subcover (fun g₀ ↦ {g : G | ‖π g‖ ≤ ‖π g₀‖ * C})
    fun g₀ _ ↦ eventually_nhds_norm_le_of_eventually_nhds_one π hC g₀
  obtain ⟨t, -, hKt⟩ := hcov
  have hC₀ : 0 ≤ C := (norm_nonneg (π 1)).trans (hC.self_of_nhds)
  refine ⟨(t.sup fun g₀ ↦ ‖π g₀‖₊ * ⟨C, hC₀⟩ : NNReal),
    NNReal.coe_nonneg _, fun g hg ↦ ?_⟩
  obtain ⟨g₀, hg₀t, hgU⟩ := Set.mem_iUnion₂.mp (hKt hg)
  have hle : ‖π g₀‖₊ * ⟨C, hC₀⟩ ≤ t.sup fun x ↦ ‖π x‖₊ * ⟨C, hC₀⟩ :=
    Finset.le_sup (f := fun x ↦ ‖π x‖₊ * ⟨C, hC₀⟩) hg₀t
  exact hgU.trans (by exact_mod_cast hle)

/-- **Group joint continuity criterion.** For a group with continuous multiplication acting on a
seminormed space, `(g, v) ↦ π g v` is jointly continuous if and only if every orbit is continuous
at `1` and `π` is uniformly operator-norm bounded on some neighborhood of `1`. No completeness,
barrelledness, or continuous inversion is needed. -/
theorem continuous_apply_prod_iff_of_group (π : ContRepresentation 𝕜 G V) :
    Continuous (fun p : G × V ↦ π p.1 p.2) ↔
      (∀ v : V, ContinuousAt (fun g ↦ π g v) 1) ∧
        ∃ U ∈ 𝓝 (1 : G), ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ U, ‖π g‖ ≤ C := by
  rw [continuous_apply_prod_iff]
  refine ⟨fun ⟨hπ, hB⟩ ↦ ⟨fun v ↦ (hπ v).continuousAt, hB 1⟩, ?_⟩
  rintro ⟨hπ, U, hU, C, -, hC⟩
  exact ⟨fun v ↦ continuous_apply_of_continuousAt_one (hπ v),
    fun g₀ ↦ exists_nhds_norm_le_of_exists_nhds_one_norm_le π ⟨U, hU, C, hC⟩ g₀⟩

/-! ### Baire group regime (no barrelledness or completeness on `V`) -/

/-- On a Baire group with continuous multiplication (for instance, any locally compact `R1Space`
group or any completely pseudometrizable group), lower semicontinuity of every pointwise norm
`g ↦ ‖π g v‖` at `1` implies a uniform operator-norm bound on a neighborhood of `1`, with no
barrelledness or completeness on `V`. -/
theorem exists_nhds_one_norm_le_of_baireSpace [BaireSpace G] {π : ContRepresentation 𝕜 G V}
    (hπ : ∀ v : V, LowerSemicontinuousAt (fun g ↦ ‖π g v‖) 1) :
    ∃ U ∈ 𝓝 (1 : G), ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ U, ‖π g‖ ≤ C := by
  obtain ⟨U, hUopen, ⟨g₀, hg₀⟩, C, hC₀, hC⟩ :=
    ContinuousLinearMap.exists_nonempty_open_norm_le (T := π)
      (lowerSemicontinuous_norm_apply_of_lowerSemicontinuousAt_one hπ)
  refine ⟨(g₀ * ·) ⁻¹' U,
    (hUopen.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using hg₀),
    ‖π g₀⁻¹‖ * C, mul_nonneg (norm_nonneg _) hC₀, fun h hh ↦ ?_⟩
  have hEq : π h = (π g₀⁻¹).comp (π (g₀ * h)) := by
    rw [← ContinuousLinearMap.mul_def, ← map_mul, inv_mul_cancel_left]
  rw [hEq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (hC (g₀ * h) hh) (norm_nonneg _))

/-- On a Baire group with continuous multiplication, lower semicontinuity of `g ↦ ‖π g v‖` at `1`
yields a uniform operator-norm bound on a neighborhood of every point `g₀ : G`, with no
barrelledness or completeness on `V`. -/
theorem exists_nhds_norm_le_of_baireSpace [BaireSpace G] {π : ContRepresentation 𝕜 G V}
    (hπ : ∀ v : V, LowerSemicontinuousAt (fun g ↦ ‖π g v‖) 1) (g₀ : G) :
    ∃ U ∈ 𝓝 g₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ U, ‖π g‖ ≤ C := by
  obtain ⟨U, hU, C, -, hC⟩ := exists_nhds_one_norm_le_of_baireSpace hπ
  exact exists_nhds_norm_le_of_exists_nhds_one_norm_le π ⟨U, hU, C, hC⟩ g₀

/-- On a Baire group with continuous multiplication, lower semicontinuity of `g ↦ ‖π g v‖` at `1`
yields a uniform operator-norm bound on every compact set `K`, with no barrelledness or
completeness on `V`. -/
theorem exists_norm_le_of_isCompact_of_baireSpace [BaireSpace G] {π : ContRepresentation 𝕜 G V}
    (hπ : ∀ v : V, LowerSemicontinuousAt (fun g ↦ ‖π g v‖) 1) {K : Set G} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ‖π g‖ ≤ C := by
  obtain ⟨U, hU, C, -, hC⟩ := exists_nhds_one_norm_le_of_baireSpace hπ
  exact exists_norm_le_of_isCompact_of_eventually_nhds_one π (eventually_of_mem hU hC) hK

/-- On a Baire group with continuous multiplication (for instance, any locally compact `R1Space`
group such as a Hausdorff Lie group, or any completely pseudometrizable group), strong continuity
at `1` implies joint continuity of `(g, v) ↦ π g v`, with **no** barrelledness or completeness
assumption on `V`. -/
theorem continuous_apply_prod_of_baireSpace [BaireSpace G] {π : ContRepresentation 𝕜 G V}
    (hπ : ∀ v : V, ContinuousAt (fun g ↦ π g v) 1) :
    Continuous fun p : G × V ↦ π p.1 p.2 :=
  (continuous_apply_prod_iff_of_group π).mpr
    ⟨hπ, exists_nhds_one_norm_le_of_baireSpace fun v ↦ (hπ v).norm.lowerSemicontinuousAt⟩

end Group

/-! ### Barrelled-space regime (arbitrary monoids and non-Baire groups) -/

section Barrelled

variable [BarrelledSpace 𝕜 V] [TopologicalSpace G]

section MonoidBarrelled

variable [Monoid G]

/-- **Uniform operator-norm bound on compact sets (upper semicontinuous form).** For a continuous
representation of a topological monoid on a barrelled seminormed space (in particular, any
Banach space), upper semicontinuity of `g ↦ ‖π g v‖` on a compact set `K` yields a uniform
nonnegative operator-norm bound on `K`. -/
theorem exists_norm_le_of_isCompact_upperSemicontinuousOn {π : ContRepresentation 𝕜 G V}
    {K : Set G} (hK : IsCompact K)
    (hπ : ∀ v : V, UpperSemicontinuousOn (fun g ↦ ‖π g v‖) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ‖π g‖ ≤ C :=
  ContinuousLinearMap.exists_norm_le_of_isCompact_upperSemicontinuousOn hK hπ

/-- **Uniform operator-norm bound on compact sets (Bernstein–Krötz, Remark 2.4(b)).** On a
barrelled seminormed space (in particular, any Banach space), strong continuity on a compact set
`K` yields a uniform nonnegative operator-norm bound on `K`. -/
theorem exists_norm_le_of_isCompact_continuousOn {π : ContRepresentation 𝕜 G V}
    {K : Set G} (hK : IsCompact K) (hπ : ∀ v : V, ContinuousOn (fun g ↦ π g v) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ‖π g‖ ≤ C :=
  ContinuousLinearMap.exists_norm_le_of_isCompact_continuousOn hK hπ

/-- On a barrelled seminormed space (in particular, any Banach space), a strongly continuous
representation has a uniform nonnegative operator-norm bound on every compact set `K`. -/
theorem exists_norm_le_of_isCompact {π : ContRepresentation 𝕜 G V}
    (hπ : ∀ v : V, Continuous fun g ↦ π g v) {K : Set G} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ‖π g‖ ≤ C :=
  exists_norm_le_of_isCompact_continuousOn hK fun v ↦ (hπ v).continuousOn

/-- On a weakly locally compact topological monoid acting on a barrelled seminormed space (in
particular, any Banach space), upper semicontinuity of `g ↦ ‖π g v‖` yields a compact
neighborhood of every point with a uniform operator-norm bound. -/
theorem exists_compact_nhds_norm_le [WeaklyLocallyCompactSpace G] {π : ContRepresentation 𝕜 G V}
    (hπ : ∀ v : V, UpperSemicontinuous fun g ↦ ‖π g v‖) (g₀ : G) :
    ∃ K ∈ 𝓝 g₀, IsCompact K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ‖π g‖ ≤ C :=
  ContinuousLinearMap.exists_compact_nhds_norm_le (T := π) hπ g₀

/-- At a point `g₀` with a countably generated neighborhood filter (for instance, in any
first-countable space), upper semicontinuity of `g ↦ ‖π g v‖` at `g₀` on a barrelled seminormed
space implies a uniform operator-norm bound on some neighborhood of `g₀`. -/
theorem exists_nhds_norm_le_of_isCountablyGenerated {π : ContRepresentation 𝕜 G V} {g₀ : G}
    [(𝓝 g₀).IsCountablyGenerated]
    (hπ : ∀ v : V, UpperSemicontinuousAt (fun g ↦ ‖π g v‖) g₀) :
    ∃ U ∈ 𝓝 g₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ U, ‖π g‖ ≤ C :=
  ContinuousLinearMap.exists_nhds_norm_le_of_isCountablyGenerated (T := π) hπ

/-- On a barrelled seminormed space (in particular, any Banach space), strong continuity on a
compact set `K` implies joint continuity on `K ×ˢ Set.univ`. -/
theorem continuousOn_apply_prod_of_isCompact {π : ContRepresentation 𝕜 G V} {K : Set G}
    (hK : IsCompact K) (hπ : ∀ v : V, ContinuousOn (fun g ↦ π g v) K) :
    ContinuousOn (fun p : G × V ↦ π p.1 p.2) (K ×ˢ Set.univ) :=
  ContinuousLinearMap.continuousOn_uncurry_of_isCompact hK hπ

/-- **Joint continuity on weakly locally compact monoids (Bernstein–Krötz, Remark 2.4(a)).** A
strongly continuous representation of a weakly locally compact monoid on a barrelled seminormed
space (in particular, any Banach space) is jointly continuous. -/
theorem continuous_apply_prod_of_weaklyLocallyCompact [WeaklyLocallyCompactSpace G]
    {π : ContRepresentation 𝕜 G V} (hπ : ∀ v : V, Continuous fun g ↦ π g v) :
    Continuous fun p : G × V ↦ π p.1 p.2 :=
  ContinuousLinearMap.continuous_uncurry_of_weaklyLocallyCompact (T := π) hπ

/-- **Joint continuity on first-countable monoids.** A strongly continuous representation of a
first-countable monoid on a barrelled seminormed space (in particular, any Banach space) is
jointly continuous. -/
theorem continuous_apply_prod_of_firstCountable [FirstCountableTopology G]
    {π : ContRepresentation 𝕜 G V} (hπ : ∀ v : V, Continuous fun g ↦ π g v) :
    Continuous fun p : G × V ↦ π p.1 p.2 :=
  ContinuousLinearMap.continuous_uncurry_of_firstCountable (T := π) hπ

end MonoidBarrelled

section GroupBarrelled

variable [Group G] [ContinuousMul G]

/-- For a group with continuous multiplication acting on a barrelled seminormed space (in
particular, any Banach space), upper semicontinuity of `g ↦ ‖π g v‖` at `1` yields a uniform
nonnegative operator-norm bound on every compact set `K`. -/
theorem exists_norm_le_of_isCompact_of_upperSemicontinuousAt_one {π : ContRepresentation 𝕜 G V}
    (hπ : ∀ v : V, UpperSemicontinuousAt (fun g ↦ ‖π g v‖) 1) {K : Set G} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ‖π g‖ ≤ C :=
  exists_norm_le_of_isCompact_upperSemicontinuousOn hK fun v ↦
    (upperSemicontinuous_norm_apply_of_upperSemicontinuousAt_one hπ v).upperSemicontinuousOn K

/-- For a group with continuous multiplication whose neighborhood filter at `1` is countably
generated (including non-Baire first-countable groups such as `ℚ` or `⊕ ℤ/2ℤ`), strong
continuity at `1` on a barrelled seminormed space (in particular, any Banach space) implies joint
continuity everywhere. -/
theorem continuous_apply_prod_of_isCountablyGenerated_one [(𝓝 (1 : G)).IsCountablyGenerated]
    {π : ContRepresentation 𝕜 G V} (hπ : ∀ v : V, ContinuousAt (fun g ↦ π g v) 1) :
    Continuous fun p : G × V ↦ π p.1 p.2 :=
  (continuous_apply_prod_iff_of_group π).mpr
    ⟨hπ, exists_nhds_norm_le_of_isCountablyGenerated fun v ↦ (hπ v).norm.upperSemicontinuousAt⟩

end GroupBarrelled

end Barrelled

end Normed

end ContRepresentation
