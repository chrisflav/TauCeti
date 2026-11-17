/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import TauCeti.RepresentationTheory.RestrictScalars

/-!
# Restricting the scalars of a continuous representation

A continuous representation `π` of a monoid `G` on a topological `R`-module `V` is also a
continuous representation over any ring `S` acting on `V` compatibly with `R`, in the sense of
`LinearMap.CompatibleSMul V V S R`: every continuous `R`-linear operator restricts to a continuous
`S`-linear operator with the same underlying function. `ContRepresentation.restrictScalars` and
`ContIntertwiningMap.restrictScalars` package this observation.

Two key instances are `S = ℝ` for a complex representation (`R = ℂ`, realification, so that
`ℝ`-linear machinery such as strongly continuous one-parameter groups applies without changing
operators or norms) and `S = ℤ` for an arbitrary topological `R`-module (forgetting scalars to the
underlying topological abelian group, via `LinearMap.CompatibleSMul.intModule`).

This file stays at the level of arbitrary topological `R`-modules without importing normed-space
machinery. Operator-norm invariance and continuity into the operator-norm topology live in
`TauCeti.RepresentationTheory.Continuous.RestrictScalars.Normed`.

## Main definitions

* `ContRepresentation.restrictScalars`: a continuous representation over `R`, read over a
  compatible ring `S`.
* `ContIntertwiningMap.restrictScalars`: a continuous intertwining map over `R`, read over a
  compatible ring `S`.

## Main results

* `ContRepresentation.restrictScalars_apply_apply` and
  `ContRepresentation.toRepresentation_restrictScalars`: evaluation and interaction with
  `toRepresentation`.
-/

public section

open ContRepresentation

namespace ContRepresentation

section Ring

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]
variable (S : Type*) [Ring S] [Module S V] [LinearMap.CompatibleSMul V V S R]

/-- A continuous representation on a topological `R`-module, read as a continuous representation
over a compatible ring `S`: each action operator is restricted via
`ContinuousLinearMap.restrictScalars S`. -/
def restrictScalars (π : ContRepresentation R G V) : ContRepresentation S G V :=
  ofMonoidHom
    { toFun g := (π g).restrictScalars S
      map_one' := ContinuousLinearMap.ext fun v ↦ by simp
      map_mul' g h := ContinuousLinearMap.ext fun v ↦ by simp }

/-- Each action operator of `π.restrictScalars S` is the scalar restriction of the corresponding
operator of `π`. -/
theorem restrictScalars_apply (π : ContRepresentation R G V) (g : G) :
    π.restrictScalars S g = (π g).restrictScalars S :=
  (rfl)

/-- The action of `π.restrictScalars S` on vectors agrees with the action of `π`. -/
@[simp]
theorem restrictScalars_apply_apply (π : ContRepresentation R G V) (g : G) (v : V) :
    π.restrictScalars S g v = π g v :=
  (rfl)

/-- Forgetting continuity commutes with restricting scalars. -/
theorem toRepresentation_restrictScalars (π : ContRepresentation R G V) :
    (π.restrictScalars S).toRepresentation = π.toRepresentation.restrictScalars S := by
  ext g v
  rw [Representation.restrictScalars_apply]
  rfl

/-- Restricting scalars of the trivial continuous representation yields the trivial continuous
representation. -/
@[simp]
theorem restrictScalars_trivial :
    (trivial R G V).restrictScalars S = trivial S G V :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl

/-- Restricting scalars commutes with restriction along a monoid homomorphism. -/
@[simp]
theorem restrictScalars_restrict {H : Type*} [Monoid H] (π : ContRepresentation R G V)
    (φ : H →* G) :
    (π.restrict φ).restrictScalars S = (π.restrictScalars S).restrict φ :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl

/-- Restricting scalars to the same ring leaves a continuous representation unchanged. -/
@[simp]
theorem restrictScalars_self (π : ContRepresentation R G V) :
    π.restrictScalars R = π :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl

/-- Restricting scalars along two compatible steps agrees with restricting in one step. -/
@[simp]
theorem restrictScalars_restrictScalars (T : Type*) [Ring T] [Module T V]
    [LinearMap.CompatibleSMul V V T S] [LinearMap.CompatibleSMul V V T R]
    (π : ContRepresentation R G V) :
    (π.restrictScalars S).restrictScalars T = π.restrictScalars T :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl

/-- Restricting scalars is injective on continuous representations. -/
theorem restrictScalars_injective :
    Function.Injective
      (restrictScalars S : ContRepresentation R G V → ContRepresentation S G V) :=
  fun _ _ h ↦ DFunLike.ext _ _ fun g ↦ ContinuousLinearMap.ext fun v ↦
    congrArg (fun ρ : ContRepresentation S G V ↦ ρ g v) h

/-- Restricting scalars does not change the underlying set of invariant vectors. -/
theorem mem_invariants_restrictScalars_iff (π : ContRepresentation R G V) {v : V} :
    v ∈ (π.restrictScalars S).invariants ↔ v ∈ π.invariants :=
  Iff.rfl

end Ring

end ContRepresentation

namespace ContIntertwiningMap

variable {R G V W U : Type*} [Ring R] [Monoid G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module R W]
  [AddCommGroup U] [TopologicalSpace U] [IsTopologicalAddGroup U] [Module R U]
variable (S : Type*) [Ring S]
  [Module S V] [LinearMap.CompatibleSMul V V S R]
  [Module S W] [LinearMap.CompatibleSMul W W S R]
  [LinearMap.CompatibleSMul V W S R]

/-- A continuous intertwining map over `R`, read as a continuous intertwining map over a compatible
ring `S`. -/
def restrictScalars {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    (f : π₁ →ⁱL π₂) : π₁.restrictScalars S →ⁱL π₂.restrictScalars S where
  __ := f.toContinuousLinearMap.restrictScalars S
  isIntertwining' g :=
    ContinuousLinearMap.ext fun v ↦ DFunLike.congr_fun (f.isIntertwining' g) v

/-- Restricting scalars does not change the underlying function of an intertwining map. -/
@[simp]
theorem restrictScalars_apply {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    (f : π₁ →ⁱL π₂) (v : V) : f.restrictScalars S v = f v :=
  (rfl)

/-- Restricting scalars sends the identity intertwining map to the identity. -/
@[simp]
theorem restrictScalars_id {π : ContRepresentation R G V} :
    (ContIntertwiningMap.id : π →ⁱL π).restrictScalars S = ContIntertwiningMap.id :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Restricting scalars commutes with composition of continuous intertwining maps. -/
@[simp]
theorem restrictScalars_comp [Module S U] [LinearMap.CompatibleSMul U U S R]
    [LinearMap.CompatibleSMul W U S R] [LinearMap.CompatibleSMul V U S R]
    {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {π₃ : ContRepresentation R G U} (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) :
    (f.comp g).restrictScalars S = (f.restrictScalars S).comp (g.restrictScalars S) :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Restricting scalars is injective on continuous intertwining maps. -/
theorem restrictScalars_injective {π₁ : ContRepresentation R G V}
    {π₂ : ContRepresentation R G W} :
    Function.Injective (restrictScalars S : (π₁ →ⁱL π₂) → _) :=
  fun _ _ h ↦ ext <| ContinuousLinearMap.ext fun v ↦
    congrArg (fun k : π₁.restrictScalars S →ⁱL π₂.restrictScalars S ↦ k v) h

end ContIntertwiningMap
