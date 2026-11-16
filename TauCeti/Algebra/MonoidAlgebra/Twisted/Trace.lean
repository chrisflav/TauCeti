/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
-- Private: weighted complex norm-squared sums are used only inside the Parseval positivity proofs.
import TauCeti.Basic.Complex.BigOperators

/-!
# Functoriality, canonical trace, and adjoint on twisted monoid algebras

For a normalized factor set `α : G → G → kˣ` on a monoid `G`, the twisted monoid algebra
`k_α[G] = TauCeti.twistedMonoidAlgebra k G α` has a distinguished `k`-basis `of g` (`g : G`).
This file builds three structural pieces on top of `TauCeti.Algebra.MonoidAlgebra.Twisted.Basic`:

* **Functoriality**: a monoid homomorphism `f : G →* H` pulling a factor set `β` on `H` back to `α`
  induces an algebra homomorphism `TauCeti.TwistedMonoidAlgebra.map f hf : k_α[G] →ₐ[k] k_β[H]`
  sending `of g` to `of (f g)`, with coordinate action `Finsupp.mapDomain f`. For a finite monoid
  `G`, the trace of an induced endomorphism `map f hf` counts the fixed points of `f`
  (`TauCeti.TwistedMonoidAlgebra.trace_map`).
* **Canonical scalar trace**: the linear functional `TauCeti.TwistedMonoidAlgebra.scalarTrace`
  extracting the coefficient of `of 1 = 1` in the `G`-basis. For a group `G`, it is a tracial
  functional (`scalarTrace_mul_comm`) whose bilinear multiplication pairing is nondegenerate
  (`forall_scalarTrace_mul_eq_zero_iff`), because `IsFactorSet.apply_inv_eq_inv_apply` makes
  `α g g⁻¹ = α g⁻¹ g` a unit. It is preserved by `map f hf` whenever `f` has trivial kernel
  (`scalarTrace_map`), and annihilates `map f hf x * of h` whenever `h ∉ Set.range f`
  (`scalarTrace_map_mul_of_eq_zero`).
* **Canonical adjoint and Parseval positivity**: when `G` is a group and `k` is a commutative
  star-semiring, the conjugate-linear involution `TauCeti.TwistedMonoidAlgebra.adjoint` sends
  `∑ c_g • of g` to `∑ star c_g • of g⁻¹`. It reverses products whenever
  `star (α g h : k) = (α h⁻¹ g⁻¹ : k)` (`adjoint_mul`), commutes with `map` (`adjoint_map`), and
  intertwines `scalarTrace` with `star` (`scalarTrace_adjoint`). Over `ℂ`, when `α g⁻¹ g = 1` for
  all `g` (unitary basis elements), `scalarTrace (adjoint x * x)` is the sum of squared moduli of
  the coordinates of `x` (`scalarTrace_adjoint_mul_self`), hence nonnegative and faithful
  (`scalarTrace_adjoint_mul_self_nonneg`, `scalarTrace_adjoint_mul_self_eq_zero_iff`).

## References

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

open scoped ComplexConjugate ComplexOrder

namespace TauCeti.TwistedMonoidAlgebra

/-- Over a commutative ring `k`, the twisted monoid algebra `twistedMonoidAlgebra k G α` inherits
a `Ring` structure from its ambient endomorphism ring whose underlying `Semiring` agrees
definitionally with `Subalgebra.toSemiring`. -/
noncomputable instance instRing {k G : Type*} [CommRing k] [Monoid G]
    (α : G → G → kˣ) [IsFactorSet α] : Ring (twistedMonoidAlgebra k G α) :=
  @Subalgebra.toRing k (Module.End k (G →₀ k)) _ _ _ (twistedMonoidAlgebra k G α)

/-! ### Functoriality along monoid homomorphisms -/

section Map

variable {k G H : Type*} [CommSemiring k] [Monoid G] [Monoid H]
  {α : G → G → kˣ} [IsFactorSet α] {β : H → H → kˣ} [IsFactorSet β]

/-- The algebra homomorphism `k_α[G] →ₐ[k] k_β[H]` induced by a monoid homomorphism `f : G →* H`
along which `β` pulls back to `α`, sending `of g` to `of (f g)`. -/
noncomputable def map (f : G →* H) (hf : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂)) :
    twistedMonoidAlgebra k G α →ₐ[k] twistedMonoidAlgebra k H β :=
  lift (fun g ↦ of (f g)) (by rw [map_one, of_one])
    (fun g₁ g₂ ↦ by rw [of_mul_of, ← hf, map_mul])

/-- `map f hf` sends the basis element `of g` to `of (f g)`. -/
@[simp]
theorem map_of (f : G →* H) (hf : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂)) (g : G) :
    map f hf (of g) = of (f g) :=
  lift_of ..

/-- `map` acts on basis coordinates by `Finsupp.mapDomain f`. -/
theorem basis_repr_map (f : G →* H) (hf : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂))
    (x : twistedMonoidAlgebra k G α) :
    (basis k H β).repr (map f hf x) = Finsupp.mapDomain f ((basis k G α).repr x) := by
  have hlin :
      (basis k H β).repr.toLinearMap.comp (map f hf).toLinearMap =
        (Finsupp.lmapDomain k k f).comp (basis k G α).repr.toLinearMap := by
    refine (basis k G α).ext fun g ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap,
      Finsupp.lmapDomain_apply, Module.Basis.repr_self, Finsupp.mapDomain_single]
    rw [basis_apply, map_of, ← basis_apply, Module.Basis.repr_self]
  exact LinearMap.congr_fun hlin x

/-- When `f` is injective, `map f hf` preserves the coordinate at `g` as the coordinate at `f g`. -/
theorem basis_repr_map_apply_of_injective (f : G →* H)
    (hf : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂)) (hinj : Function.Injective f)
    (x : twistedMonoidAlgebra k G α) (g : G) :
    (basis k H β).repr (map f hf x) (f g) = (basis k G α).repr x g := by
  rw [basis_repr_map]
  exact Finsupp.mapDomain_apply_of_injective hinj _ g

/-- Every coordinate of `map f hf x` outside `Set.range f` is zero. -/
theorem basis_repr_map_of_notMem_range (f : G →* H)
    (hf : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂)) {h : H} (hh : h ∉ Set.range f)
    (x : twistedMonoidAlgebra k G α) :
    (basis k H β).repr (map f hf x) h = 0 := by
  rw [basis_repr_map]
  exact Finsupp.mapDomain_of_notMem_range _ h hh

/-- An injective monoid homomorphism induces an injective algebra homomorphism on twisted monoid
algebras. -/
theorem map_injective (f : G →* H) (hf : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂))
    (hinj : Function.Injective f) : Function.Injective (map f hf) := by
  intro x y hxy
  apply (basis k G α).repr.injective
  apply Finsupp.mapDomain_injective hinj
  rw [← basis_repr_map f hf, ← basis_repr_map f hf, hxy]

end Map

/-- For a finite monoid `G`, the trace of the algebra endomorphism `map f hf` on `k_α[G]` equals
the number of fixed points of `f` in `G`. -/
theorem trace_map {k G : Type*} [CommSemiring k] [Monoid G] [Finite G]
    {α : G → G → kˣ} [IsFactorSet α] (f : G →* G)
    (hf : ∀ g₁ g₂ : G, α g₁ g₂ = α (f g₁) (f g₂)) :
    LinearMap.trace k (twistedMonoidAlgebra k G α) (map f hf).toLinearMap =
      (Nat.card {g : G // f g = g} : k) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rw [LinearMap.trace_eq_matrix_trace k (basis k G α), Matrix.trace]
  have hdiag : ∀ g : G,
      LinearMap.toMatrix (basis k G α) (basis k G α) (map f hf).toLinearMap g g =
        if f g = g then (1 : k) else 0 := by
    intro g
    rw [LinearMap.toMatrix_apply, basis_apply, AlgHom.toLinearMap_apply, map_of, ← basis_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
  simp only [Matrix.diag_apply, hdiag, Finset.sum_boole, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-! ### Canonical scalar trace -/

section ScalarTrace

variable {k G : Type*} [CommSemiring k] [Monoid G] {α : G → G → kˣ} [IsFactorSet α]

/-- The **canonical scalar trace** on `k_α[G]`, extracting the coefficient of `of 1 = 1` in the
canonical `G`-basis `TauCeti.TwistedMonoidAlgebra.basis`. -/
noncomputable def scalarTrace : twistedMonoidAlgebra k G α →ₗ[k] k :=
  (Finsupp.lapply (1 : G)).comp (basis k G α).repr.toLinearMap

/-- Unfolding `scalarTrace` as the `1`-coordinate in `basis k G α`. -/
theorem scalarTrace_apply (x : twistedMonoidAlgebra k G α) :
    scalarTrace x = (basis k G α).repr x 1 :=
  (rfl)

/-- `scalarTrace` sends `1` to `1`. -/
@[simp]
theorem scalarTrace_one : scalarTrace (1 : twistedMonoidAlgebra k G α) = 1 := by
  rw [scalarTrace_apply, ← of_one, ← basis_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- `scalarTrace` acts as the identity on scalar multiples of `1`. -/
@[simp]
theorem scalarTrace_algebraMap (c : k) :
    scalarTrace (algebraMap k (twistedMonoidAlgebra k G α) c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, scalarTrace_one, smul_eq_mul, mul_one]

/-- Every non-identity basis element has scalar trace `0`. -/
theorem scalarTrace_of_ne_one {g : G} (hg : g ≠ 1) :
    scalarTrace (of g : twistedMonoidAlgebra k G α) = 0 := by
  rw [scalarTrace_apply, ← basis_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hg.symm]

/-- The scalar trace of `of g` is `1` if `g = 1` and `0` otherwise. -/
theorem scalarTrace_of [DecidableEq G] (g : G) :
    scalarTrace (of g : twistedMonoidAlgebra k G α) = if g = 1 then 1 else 0 := by
  rw [scalarTrace_apply, ← basis_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- `scalarTrace (of g * of h)` vanishes whenever `g * h ≠ 1`. -/
theorem scalarTrace_of_mul_of_ne_one {g h : G} (hgh : g * h ≠ 1) :
    scalarTrace ((of g : twistedMonoidAlgebra k G α) * of h) = 0 := by
  rw [of_mul_of, map_smul, scalarTrace_of_ne_one hgh, smul_zero]

/-- `map f hf` preserves `scalarTrace` whenever `1` is the only preimage of `1` under `f`. -/
theorem scalarTrace_map {H : Type*} [Monoid H] {β : H → H → kˣ} [IsFactorSet β]
    (f : G →* H) (hf : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂))
    (hf1 : ∀ g : G, f g = 1 → g = 1) (x : twistedMonoidAlgebra k G α) :
    scalarTrace (map f hf x) = scalarTrace x := by
  classical
  have hlin : scalarTrace.comp (map f hf).toLinearMap = scalarTrace := by
    refine (basis k G α).ext fun g ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, basis_apply, map_of,
      scalarTrace_of]
    by_cases hg : g = 1
    · simp [hg]
    · have hfg : f g ≠ 1 := fun h ↦ hg (hf1 g h)
      simp [hg, hfg]
  exact LinearMap.congr_fun hlin x

end ScalarTrace

section ScalarTraceGroup

variable {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ} [IsFactorSet α]

/-- `scalarTrace (of g * of g⁻¹)` equals the factor set value `α g g⁻¹`. -/
theorem scalarTrace_of_mul_of_inv (g : G) :
    scalarTrace ((of g : twistedMonoidAlgebra k G α) * of g⁻¹) = (α g g⁻¹ : k) := by
  simp [of_mul_of]

/-- `scalarTrace (of g⁻¹ * of g)` equals the factor set value `α g⁻¹ g`. -/
theorem scalarTrace_of_inv_mul_of (g : G) :
    scalarTrace ((of g⁻¹ : twistedMonoidAlgebra k G α) * of g) = (α g⁻¹ g : k) := by
  simp [of_mul_of]

/-- **The canonical scalar trace on a twisted group algebra is tracial.** -/
theorem scalarTrace_mul_comm (x y : twistedMonoidAlgebra k G α) :
    scalarTrace (x * y) = scalarTrace (y * x) := by
  have hbil :
      (LinearMap.mul k (twistedMonoidAlgebra k G α)).compr₂ scalarTrace =
        ((LinearMap.mul k (twistedMonoidAlgebra k G α)).compr₂ scalarTrace).flip := by
    refine (basis k G α).ext fun g ↦ (basis k G α).ext fun h ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.mul_apply', basis_apply]
    by_cases hgh : g * h = 1
    · have hh : h = g⁻¹ := eq_inv_of_mul_eq_one_right hgh
      subst hh
      simp [IsFactorSet.apply_inv_eq_inv_apply α g]
    · have hhg : h * g ≠ 1 := fun h1 ↦ hgh (by rw [eq_inv_of_mul_eq_one_left h1, mul_inv_cancel])
      rw [scalarTrace_of_mul_of_ne_one hgh, scalarTrace_of_mul_of_ne_one hhg]
  exact LinearMap.congr_fun₂ hbil x y

/-- Pairing `x` with `of g⁻¹` under `scalarTrace` extracts the `g`-coordinate of `x` scaled by the
unit `α g g⁻¹`. -/
theorem scalarTrace_mul_of_inv (x : twistedMonoidAlgebra k G α) (g : G) :
    scalarTrace (x * of g⁻¹) = (α g g⁻¹ : k) * (basis k G α).repr x g := by
  have hlin :
      scalarTrace.comp (LinearMap.mulRight k (of g⁻¹)) =
        ((α g g⁻¹ : k) • Finsupp.lapply g).comp (basis k G α).repr.toLinearMap := by
    refine (basis k G α).ext fun h ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, basis_apply,
      LinearEquiv.coe_toLinearMap, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul]
    rw [← basis_apply, Module.Basis.repr_self]
    by_cases hhg : h = g
    · subst hhg
      simp
    · have hne : h * g⁻¹ ≠ 1 := fun h1 ↦ hhg (eq_of_mul_inv_eq_one h1)
      rw [basis_apply, scalarTrace_of_mul_of_ne_one hne, Finsupp.single_eq_of_ne (Ne.symm hhg),
        mul_zero]
  exact LinearMap.congr_fun hlin x

/-- **Nondegeneracy of the canonical scalar trace** on a twisted group algebra: `x` pairs to zero
with every element if and only if `x = 0`. -/
theorem forall_scalarTrace_mul_eq_zero_iff {x : twistedMonoidAlgebra k G α} :
    (∀ y : twistedMonoidAlgebra k G α, scalarTrace (x * y) = 0) ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx y ↦ by simp [hx]⟩
  apply (basis k G α).repr.injective
  ext g
  have hg := hx (of g⁻¹)
  rw [scalarTrace_mul_of_inv] at hg
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  calc
    (basis k G α).repr x g =
        (((α g g⁻¹)⁻¹ : kˣ) : k) * ((α g g⁻¹ : k) * (basis k G α).repr x g) := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    _ = 0 := by rw [hg, mul_zero]

/-- If `f : G →* H` is a monoid homomorphism from a group `G` and `h ∉ Set.range f`, then
multiplying any element of the image of `map f hf` by `of h` kills the scalar trace. -/
theorem scalarTrace_map_mul_of_eq_zero {H : Type*} [Monoid H] {β : H → H → kˣ} [IsFactorSet β]
    (f : G →* H) (hf : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂))
    {h : H} (hh : h ∉ Set.range f) (x : twistedMonoidAlgebra k G α) :
    scalarTrace (map f hf x * of h) = 0 := by
  have hlin : (scalarTrace.comp (LinearMap.mulRight k (of h))).comp (map f hf).toLinearMap = 0 := by
    refine (basis k G α).ext fun g ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply,
      basis_apply, map_of, LinearMap.zero_apply]
    refine scalarTrace_of_mul_of_ne_one fun h1 ↦ hh ⟨g⁻¹, ?_⟩
    calc
      f g⁻¹ = f g⁻¹ * (f g * h) := by rw [h1, mul_one]
      _ = f (g⁻¹ * g) * h := by rw [← mul_assoc, ← map_mul]
      _ = h := by rw [inv_mul_cancel, map_one, one_mul]
  exact LinearMap.congr_fun hlin x

end ScalarTraceGroup

/-! ### Canonical conjugate-linear adjoint and Parseval positivity -/

section Adjoint

variable {k G : Type*} [CommSemiring k] [StarRing k] [Group G]
  {α : G → G → kˣ} [IsFactorSet α]

/-- The **canonical conjugate-linear adjoint** on a twisted group algebra `k_α[G]`, sending
`∑ c_g • of g` to `∑ star c_g • of g⁻¹`. -/
noncomputable def adjoint :
    twistedMonoidAlgebra k G α →ₛₗ[starRingEnd k] twistedMonoidAlgebra k G α where
  toFun x := ((basis k G α).repr x).sum fun g c ↦ star c • of g⁻¹
  map_add' x y := by
    rw [map_add]
    exact Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by rw [star_add, add_smul])
  map_smul' c x := by
    rw [map_smul]
    simp only [starRingEnd_apply]
    rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (fun _ _ ↦ by simp)]
    rw [Finsupp.sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [Finsupp.smul_apply, smul_eq_mul, star_mul, mul_comm, mul_smul]

/-- `adjoint` sends the basis element `of g` to `of g⁻¹`. -/
@[simp]
theorem adjoint_of (g : G) :
    adjoint (of g : twistedMonoidAlgebra k G α) = of g⁻¹ := by
  simp [adjoint, ← basis_apply]

/-- `adjoint` fixes `1`. -/
@[simp]
theorem adjoint_one : adjoint (1 : twistedMonoidAlgebra k G α) = 1 := by
  rw [← of_one, adjoint_of, inv_one, of_one]

/-- `adjoint` conjugates scalar multiples of `1`. -/
@[simp]
theorem adjoint_algebraMap (c : k) :
    adjoint (algebraMap k (twistedMonoidAlgebra k G α) c) =
      algebraMap k (twistedMonoidAlgebra k G α) (star c) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, starRingEnd_apply, adjoint_one,
    Algebra.algebraMap_eq_smul_one]

/-- `adjoint` conjugates basis coordinates and inverts the group index. -/
theorem basis_repr_adjoint (x : twistedMonoidAlgebra k G α) (g : G) :
    (basis k G α).repr (adjoint x) g = star ((basis k G α).repr x g⁻¹) := by
  classical
  simp only [adjoint, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.sum, map_sum, map_smul,
    ← basis_apply, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero]
  have heq : ∀ h : G, (h⁻¹ = g) ↔ (h = g⁻¹) := fun h ↦ inv_eq_iff_eq_inv
  simp_rw [heq, Finset.sum_ite_eq']
  by_cases hg : g⁻¹ ∈ ((basis k G α).repr x).support
  · simp [hg]
  · simp [hg, Finsupp.notMem_support_iff.mp hg]

/-- `adjoint` is an involution. -/
@[simp]
theorem adjoint_adjoint (x : twistedMonoidAlgebra k G α) : adjoint (adjoint x) = x := by
  apply (basis k G α).repr.injective
  ext g
  simp [basis_repr_adjoint]

/-- `adjoint` reverses multiplication whenever the factor set satisfies
`star (α g h : k) = (α h⁻¹ g⁻¹ : k)`. -/
theorem adjoint_mul (hα : ∀ g h : G, star (α g h : k) = (α h⁻¹ g⁻¹ : k))
    (x y : twistedMonoidAlgebra k G α) :
    adjoint (x * y) = adjoint y * adjoint x := by
  rw [← (basis k G α).linearCombination_repr x, ← (basis k G α).linearCombination_repr y,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_assoc, mul_smul_comm,
    map_smulₛₗ, starRingEnd_apply, basis_apply, of_mul_of, adjoint_of, mul_inv_rev, smul_smul,
    star_mul, hα, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ ↦ Finset.sum_congr rfl fun h _ ↦ ?_
  congr 1
  ac_rfl

/-- `adjoint` commutes with every algebra homomorphism `map f hf` induced by a group
homomorphism. -/
theorem adjoint_map {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
    (f : G →* H) (hf : ∀ g₁ g₂ : G, α g₁ g₂ = β (f g₁) (f g₂))
    (x : twistedMonoidAlgebra k G α) :
    adjoint (map f hf x) = map f hf (adjoint x) := by
  rw [← (basis k G α).linearCombination_repr x, Finsupp.linearCombination_apply]
  simp [Finsupp.sum, map_sum, map_smul, map_smulₛₗ, basis_apply, map_of, adjoint_of, map_inv]

/-- `scalarTrace` intertwines `adjoint` with `star`. -/
@[simp]
theorem scalarTrace_adjoint (x : twistedMonoidAlgebra k G α) :
    scalarTrace (adjoint x) = star (scalarTrace x) := by
  rw [scalarTrace_apply, basis_repr_adjoint, inv_one, scalarTrace_apply]

/-- **Sesquilinear Parseval formula** for `scalarTrace (adjoint x * y)` in the `G`-basis. -/
theorem scalarTrace_adjoint_mul (x y : twistedMonoidAlgebra k G α) :
    scalarTrace (adjoint x * y) =
      ((basis k G α).repr x).sum fun g z ↦
        star z * ((α g⁻¹ g : k) * (basis k G α).repr y g) := by
  conv_lhs => rw [← (basis k G α).linearCombination_repr x, Finsupp.linearCombination_apply]
  rw [Finsupp.sum, map_sum, Finset.sum_mul, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [map_smulₛₗ, starRingEnd_apply, basis_apply, adjoint_of, smul_mul_assoc, map_smul,
    smul_eq_mul, scalarTrace_mul_comm, scalarTrace_mul_of_inv,
    IsFactorSet.apply_inv_eq_inv_apply α g]

end Adjoint

section ParsevalComplex

variable {G : Type*} [Group G] {α : G → G → ℂˣ} [IsFactorSet α]

/-- **Parseval identity** for a complex twisted group algebra with unitary basis elements
(`α g⁻¹ g = 1`): `scalarTrace (adjoint x * x)` equals the sum of squared moduli of the coordinates
of `x`. -/
theorem scalarTrace_adjoint_mul_self (hinv : ∀ g : G, α g⁻¹ g = 1)
    (x : twistedMonoidAlgebra ℂ G α) :
    scalarTrace (adjoint x * x) =
      ((((basis ℂ G α).repr x).sum fun _ z ↦ Complex.normSq z : ℝ) : ℂ) := by
  rw [scalarTrace_adjoint_mul]
  simpa [hinv] using (Finsupp.ofReal_sum_normSq_mul ((basis ℂ G α).repr x) 1).symm

/-- **Positivity of the canonical scalar trace** for a complex twisted group algebra with unitary
basis elements (`α g⁻¹ g = 1`). -/
theorem scalarTrace_adjoint_mul_self_nonneg (hinv : ∀ g : G, α g⁻¹ g = 1)
    (x : twistedMonoidAlgebra ℂ G α) :
    0 ≤ scalarTrace (adjoint x * x) := by
  rw [scalarTrace_adjoint_mul_self hinv, Complex.zero_le_real]
  exact Finsupp.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

/-- **Faithfulness of the canonical scalar trace** for a complex twisted group algebra with unitary
basis elements (`α g⁻¹ g = 1`): `scalarTrace (adjoint x * x) = 0` if and only if `x = 0`. -/
theorem scalarTrace_adjoint_mul_self_eq_zero_iff (hinv : ∀ g : G, α g⁻¹ g = 1)
    {x : twistedMonoidAlgebra ℂ G α} :
    scalarTrace (adjoint x * x) = 0 ↔ x = 0 := by
  rw [scalarTrace_adjoint_mul_self hinv, Complex.ofReal_eq_zero]
  have h0 := Finsupp.sum_normSq_mul_eq_zero_iff ((basis ℂ G α).repr x) (w := 1)
    (fun _ ↦ zero_le_one)
  simp only [Pi.one_apply, mul_one, ne_eq, one_ne_zero, not_false_eq_true, forall_const] at h0
  rw [h0]
  exact ⟨fun h ↦ (basis ℂ G α).repr.injective (Finsupp.ext fun g ↦ by simpa using h g),
    fun hx g ↦ by simp [hx]⟩

end ParsevalComplex

end TauCeti.TwistedMonoidAlgebra
