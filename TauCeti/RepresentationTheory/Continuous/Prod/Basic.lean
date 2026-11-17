/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.RepresentationTheory.Continuous.RestrictScalars.Basic

/-!
# Products of continuous representations

This file constructs the binary product `ContRepresentation.prod` and the indexed product
`ContRepresentation.pi` of continuous representations of a monoid `G`, acting factor by factor
with the product topology on the underlying module. It also equips both constructions with their
universal continuous intertwining maps (`fst`, `snd`, `prod`, `inl`, `inr`, `prodMap`, `proj`,
`pi`, `piMap`) and basic compatibilities (`trivial`, `restrict`, `restrictScalars`, `invariants`).

This file stays at the level of arbitrary topological `R`-modules without importing normed-space
machinery. Continuity into the topology of bounded convergence and operator-norm formulas on
seminormed spaces live in `TauCeti.RepresentationTheory.Continuous.Prod.Normed`.

## Main definitions

* `ContRepresentation.prod`: binary product `π.prod ρ` acting on `V × W`.
* `ContRepresentation.pi`: arbitrary indexed product `pi π` acting on `∀ i, V i`.
* `ContIntertwiningMap.fst`, `ContIntertwiningMap.snd`, `ContIntertwiningMap.prod`,
  `ContIntertwiningMap.inl`, `ContIntertwiningMap.inr`, `ContIntertwiningMap.prodMap`: universal
  intertwiners for binary products.
* `ContIntertwiningMap.proj`, `ContIntertwiningMap.pi`, `ContIntertwiningMap.piMap`: universal
  intertwiners for indexed products.
-/

public section

open ContRepresentation

namespace ContRepresentation

section Prod

variable {R G V W : Type*} [Ring R] [Monoid G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module R W]

/-- The binary product of two continuous representations, acting componentwise on `V × W`. -/
def prod (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    ContRepresentation R G (V × W) :=
  ofMonoidHom
    { toFun g := (π g).prodMap (ρ g)
      map_one' := ContinuousLinearMap.ext fun _ ↦ Prod.ext (by simp) (by simp)
      map_mul' g h := ContinuousLinearMap.ext fun _ ↦ Prod.ext (by simp) (by simp) }

/-- Each action operator of `π.prod ρ` is the product map of the factor operators. -/
theorem prod_apply (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) (g : G) :
    (π.prod ρ) g = (π g).prodMap (ρ g) :=
  (rfl)

/-- The product representation acts componentwise on `V × W`. -/
@[simp]
theorem prod_apply_apply (π : ContRepresentation R G V) (ρ : ContRepresentation R G W)
    (g : G) (v : V × W) : (π.prod ρ) g v = (π g v.1, ρ g v.2) :=
  (rfl)

/-- Forgetting continuity commutes with binary products. -/
theorem toRepresentation_prod (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    (π.prod ρ).toRepresentation = π.toRepresentation.prod ρ.toRepresentation := by
  ext g v <;> rfl

/-- The binary product of trivial representations is the trivial representation. -/
@[simp]
theorem prod_trivial :
    (trivial R G V).prod (trivial R G W) = trivial R G (V × W) :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl

/-- Restriction along a monoid homomorphism commutes with binary products. -/
@[simp]
theorem prod_restrict {H : Type*} [Monoid H] (π : ContRepresentation R G V)
    (ρ : ContRepresentation R G W) (φ : H →* G) :
    (π.prod ρ).restrict φ = (π.restrict φ).prod (ρ.restrict φ) :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl

/-- Restricting scalars commutes with binary products. -/
@[simp]
theorem prod_restrictScalars (S : Type*) [Ring S]
    [Module S V] [LinearMap.CompatibleSMul V V S R]
    [Module S W] [LinearMap.CompatibleSMul W W S R]
    [LinearMap.CompatibleSMul (V × W) (V × W) S R]
    (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    (π.prod ρ).restrictScalars S = (π.restrictScalars S).prod (ρ.restrictScalars S) :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp

/-- A pair `(v, w)` is invariant for `π.prod ρ` if and only if each component is invariant. -/
theorem mem_invariants_prod_iff (π : ContRepresentation R G V) (ρ : ContRepresentation R G W)
    {v : V × W} :
    v ∈ (π.prod ρ).invariants ↔ v.1 ∈ π.invariants ∧ v.2 ∈ ρ.invariants := by
  simp only [mem_invariants, prod_apply_apply, Prod.ext_iff, forall_and]

end Prod

section Pi

variable {R G ι : Type*} [Ring R] [Monoid G] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, IsTopologicalAddGroup (V i)] [∀ i, Module R (V i)]

/-- The indexed product of a family of continuous representations, acting factor by factor on
`∀ i, V i` with the product topology. -/
def pi (π : ∀ i, ContRepresentation R G (V i)) : ContRepresentation R G (∀ i, V i) :=
  ofMonoidHom
    { toFun g := ContinuousLinearMap.pi fun i ↦ (π i g).comp (ContinuousLinearMap.proj i)
      map_one' := ContinuousLinearMap.ext fun x ↦ funext fun i ↦ by simp
      map_mul' g h := ContinuousLinearMap.ext fun x ↦ funext fun i ↦ by simp }

/-- Each action operator of `pi π` is the product of the factor operators. -/
theorem pi_apply (π : ∀ i, ContRepresentation R G (V i)) (g : G) :
    pi π g = ContinuousLinearMap.pi fun i ↦ (π i g).comp (ContinuousLinearMap.proj i) :=
  (rfl)

/-- The indexed product representation acts factor by factor on `∀ i, V i`. -/
@[simp]
theorem pi_apply_apply (π : ∀ i, ContRepresentation R G (V i)) (g : G)
    (x : ∀ i, V i) (i : ι) : pi π g x i = π i g (x i) :=
  (rfl)

/-- The indexed product of trivial representations is the trivial representation. -/
@[simp]
theorem pi_trivial :
    pi (fun i ↦ trivial R G (V i)) = trivial R G (∀ i, V i) :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ funext fun _ ↦ rfl

/-- Restriction along a monoid homomorphism commutes with indexed products. -/
@[simp]
theorem pi_restrict {H : Type*} [Monoid H] (π : ∀ i, ContRepresentation R G (V i))
    (φ : H →* G) :
    (pi π).restrict φ = pi fun i ↦ (π i).restrict φ :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ funext fun _ ↦ rfl

/-- Restricting scalars commutes with indexed products. -/
@[simp]
theorem pi_restrictScalars (S : Type*) [Ring S]
    [∀ i, Module S (V i)] [∀ i, LinearMap.CompatibleSMul (V i) (V i) S R]
    [LinearMap.CompatibleSMul (∀ i, V i) (∀ i, V i) S R]
    (π : ∀ i, ContRepresentation R G (V i)) :
    (pi π).restrictScalars S = pi fun i ↦ (π i).restrictScalars S :=
  DFunLike.ext _ _ fun _ ↦ ContinuousLinearMap.ext fun _ ↦ funext fun _ ↦ by simp

/-- A vector in `∀ i, V i` is invariant for `pi π` iff each coordinate is invariant. -/
theorem mem_invariants_pi_iff (π : ∀ i, ContRepresentation R G (V i)) {x : ∀ i, V i} :
    x ∈ (pi π).invariants ↔ ∀ i, x i ∈ (π i).invariants := by
  simp only [mem_invariants, funext_iff, pi_apply_apply]
  exact forall_comm

end Pi

end ContRepresentation

namespace ContIntertwiningMap

section Prod

variable {R G V W U X : Type*} [Ring R] [Monoid G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module R W]
  [AddCommGroup U] [TopologicalSpace U] [IsTopologicalAddGroup U] [Module R U]
  [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [Module R X]

/-- First projection from a binary product representation. -/
def fst (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    π.prod ρ →ⁱL π where
  __ := ContinuousLinearMap.fst R V W
  isIntertwining' _ := ContinuousLinearMap.ext fun _ ↦ rfl

/-- Evaluation of the first projection from a binary product. -/
@[simp]
theorem fst_apply (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) (v : V × W) :
    fst π ρ v = v.1 :=
  (rfl)

/-- Second projection from a binary product representation. -/
def snd (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    π.prod ρ →ⁱL ρ where
  __ := ContinuousLinearMap.snd R V W
  isIntertwining' _ := ContinuousLinearMap.ext fun _ ↦ rfl

/-- Evaluation of the second projection from a binary product. -/
@[simp]
theorem snd_apply (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) (v : V × W) :
    snd π ρ v = v.2 :=
  (rfl)

/-- Pairing of two continuous intertwining maps into a binary product representation. -/
def prod {σ : ContRepresentation R G U} {π : ContRepresentation R G V}
    {ρ : ContRepresentation R G W} (f : σ →ⁱL π) (g : σ →ⁱL ρ) :
    σ →ⁱL π.prod ρ where
  __ := f.toContinuousLinearMap.prod g.toContinuousLinearMap
  isIntertwining' x := ContinuousLinearMap.ext fun u ↦
    Prod.ext (f.isIntertwining x u) (g.isIntertwining x u)

/-- Evaluation of the pairing of two continuous intertwining maps. -/
@[simp]
theorem prod_apply {σ : ContRepresentation R G U} {π : ContRepresentation R G V}
    {ρ : ContRepresentation R G W} (f : σ →ⁱL π) (g : σ →ⁱL ρ) (u : U) :
    f.prod g u = (f u, g u) :=
  (rfl)

/-- Composing a pairing with `fst` recovers the first factor. -/
@[simp]
theorem fst_comp_prod {σ : ContRepresentation R G U} {π : ContRepresentation R G V}
    {ρ : ContRepresentation R G W} (f : σ →ⁱL π) (g : σ →ⁱL ρ) :
    (fst π ρ).comp (f.prod g) = f :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Composing a pairing with `snd` recovers the second factor. -/
@[simp]
theorem snd_comp_prod {σ : ContRepresentation R G U} {π : ContRepresentation R G V}
    {ρ : ContRepresentation R G W} (f : σ →ⁱL π) (g : σ →ⁱL ρ) :
    (snd π ρ).comp (f.prod g) = g :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Left inclusion into a binary product representation. -/
def inl (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    π →ⁱL π.prod ρ :=
  ContIntertwiningMap.prod .id 0

/-- Evaluation of the left inclusion into a binary product. -/
@[simp]
theorem inl_apply (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) (v : V) :
    inl π ρ v = (v, 0) :=
  (rfl)

/-- Right inclusion into a binary product representation. -/
def inr (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    ρ →ⁱL π.prod ρ :=
  ContIntertwiningMap.prod 0 .id

/-- Evaluation of the right inclusion into a binary product. -/
@[simp]
theorem inr_apply (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) (w : W) :
    inr π ρ w = (0, w) :=
  (rfl)

/-- Projecting the left inclusion onto the first factor gives the identity. -/
@[simp]
theorem fst_comp_inl (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    (fst π ρ).comp (inl π ρ) = .id :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Projecting the left inclusion onto the second factor gives zero. -/
@[simp]
theorem snd_comp_inl (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    (snd π ρ).comp (inl π ρ) = 0 :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Projecting the right inclusion onto the first factor gives zero. -/
@[simp]
theorem fst_comp_inr (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    (fst π ρ).comp (inr π ρ) = 0 :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Projecting the right inclusion onto the second factor gives the identity. -/
@[simp]
theorem snd_comp_inr (π : ContRepresentation R G V) (ρ : ContRepresentation R G W) :
    (snd π ρ).comp (inr π ρ) = .id :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Product of two continuous intertwining maps acting componentwise. -/
def prodMap {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G U}
    {ρ₁ : ContRepresentation R G W} {ρ₂ : ContRepresentation R G X}
    (f : π₁ →ⁱL π₂) (g : ρ₁ →ⁱL ρ₂) :
    π₁.prod ρ₁ →ⁱL π₂.prod ρ₂ :=
  (f.comp (fst π₁ ρ₁)).prod (g.comp (snd π₁ ρ₁))

/-- Evaluation of the product of two continuous intertwining maps. -/
@[simp]
theorem prodMap_apply {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G U}
    {ρ₁ : ContRepresentation R G W} {ρ₂ : ContRepresentation R G X}
    (f : π₁ →ⁱL π₂) (g : ρ₁ →ⁱL ρ₂) (p : V × W) :
    f.prodMap g p = (f p.1, g p.2) :=
  (rfl)

/-- Naturality of the first projection with respect to `prodMap`. -/
@[simp]
theorem fst_comp_prodMap {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G U}
    {ρ₁ : ContRepresentation R G W} {ρ₂ : ContRepresentation R G X}
    (f : π₁ →ⁱL π₂) (g : ρ₁ →ⁱL ρ₂) :
    (fst π₂ ρ₂).comp (f.prodMap g) = f.comp (fst π₁ ρ₁) :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Naturality of the second projection with respect to `prodMap`. -/
@[simp]
theorem snd_comp_prodMap {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G U}
    {ρ₁ : ContRepresentation R G W} {ρ₂ : ContRepresentation R G X}
    (f : π₁ →ⁱL π₂) (g : ρ₁ →ⁱL ρ₂) :
    (snd π₂ ρ₂).comp (f.prodMap g) = g.comp (snd π₁ ρ₁) :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

end Prod

section Pi

variable {R G ι : Type*} [Ring R] [Monoid G] {U : Type*}
  [AddCommGroup U] [TopologicalSpace U] [IsTopologicalAddGroup U] [Module R U]
  {V W : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, TopologicalSpace (V i)]
  [∀ i, IsTopologicalAddGroup (V i)] [∀ i, Module R (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, TopologicalSpace (W i)]
  [∀ i, IsTopologicalAddGroup (W i)] [∀ i, Module R (W i)]

/-- Projection from an indexed product representation onto its `i`-th factor. -/
def proj (π : ∀ i, ContRepresentation R G (V i)) (i : ι) :
    ContRepresentation.pi π →ⁱL π i where
  __ := ContinuousLinearMap.proj i
  isIntertwining' _ := ContinuousLinearMap.ext fun _ ↦ rfl

/-- Evaluation of a projection from an indexed product representation. -/
@[simp]
theorem proj_apply (π : ∀ i, ContRepresentation R G (V i)) (i : ι) (x : ∀ i, V i) :
    proj π i x = x i :=
  (rfl)

/-- Universal map into an indexed product representation from a family of intertwiners. -/
def pi {σ : ContRepresentation R G U} {π : ∀ i, ContRepresentation R G (V i)}
    (f : ∀ i, σ →ⁱL π i) : σ →ⁱL ContRepresentation.pi π where
  __ := ContinuousLinearMap.pi fun i ↦ (f i).toContinuousLinearMap
  isIntertwining' g := ContinuousLinearMap.ext fun u ↦ funext fun i ↦ (f i).isIntertwining g u

/-- Evaluation of the universal map into an indexed product representation. -/
@[simp]
theorem pi_apply {σ : ContRepresentation R G U} {π : ∀ i, ContRepresentation R G (V i)}
    (f : ∀ i, σ →ⁱL π i) (u : U) (i : ι) :
    pi f u i = f i u :=
  (rfl)

/-- Composing the universal map `pi f` with `proj π i` recovers `f i`. -/
@[simp]
theorem proj_comp_pi {σ : ContRepresentation R G U} {π : ∀ i, ContRepresentation R G (V i)}
    (f : ∀ i, σ →ⁱL π i) (i : ι) :
    (proj π i).comp (pi f) = f i :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

/-- Product of a family of continuous intertwining maps acting coordinatewise. -/
def piMap {π : ∀ i, ContRepresentation R G (V i)} {ρ : ∀ i, ContRepresentation R G (W i)}
    (f : ∀ i, π i →ⁱL ρ i) : ContRepresentation.pi π →ⁱL ContRepresentation.pi ρ :=
  pi fun i ↦ (f i).comp (proj π i)

/-- Evaluation of the coordinatewise product `piMap f`. -/
@[simp]
theorem piMap_apply {π : ∀ i, ContRepresentation R G (V i)}
    {ρ : ∀ i, ContRepresentation R G (W i)}
    (f : ∀ i, π i →ⁱL ρ i) (x : ∀ i, V i) (i : ι) :
    piMap f x i = f i (x i) :=
  (rfl)

/-- Naturality of the projections with respect to `piMap`. -/
@[simp]
theorem proj_comp_piMap {π : ∀ i, ContRepresentation R G (V i)}
    {ρ : ∀ i, ContRepresentation R G (W i)}
    (f : ∀ i, π i →ⁱL ρ i) (i : ι) :
    (proj ρ i).comp (piMap f) = (f i).comp (proj π i) :=
  ext <| ContinuousLinearMap.ext fun _ ↦ rfl

end Pi

end ContIntertwiningMap
