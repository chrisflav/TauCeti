/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.LinearAlgebra.Alternating.Derivation
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.TensorProduct.Hom

/-!
# Scalar extension of alternating maps

Let `R` be a commutative ring, `S` a commutative `R`-algebra, and `M`, `N` be `R`-modules. Every
alternating map `ω : M [⋀^Fin n]→ₗ[R] N` extends canonically to an `S`-alternating map
`ω.baseChange S : (S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N)` satisfying
`ω.baseChange S (fun i ↦ s i ⊗ₜ m i) = (∏ i, s i) ⊗ₜ ω m` (`AlternatingMap.baseChange_apply_tmul`).
No flatness or freeness assumption is needed: the map is constructed by transferring
`LinearMap.baseChange S` along `exteriorPower.alternatingMapLinearEquiv` and the exterior-power
base-change identification `TauCeti.exteriorPower.equivBaseChange`.

Scalar extension commutes with interior products (`AlternatingMap.baseChange_curryLeft`),
pre- and post-composition with linear maps (`AlternatingMap.baseChange_compLinearMap`,
`AlternatingMap.baseChange_compAlternatingMap`), and the induced derivation on alternating maps
(`AlternatingMap.baseChange_alternatingDerivation`).

When `M` is finitely generated and projective over `R`, its exterior powers `⋀[R]^n M` are also
finitely generated and projective, so the `R`-linear map
`AlternatingMap.baseChangeHom R S M N n` exhibits `(S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N)` as the
base change of `M [⋀^Fin n]→ₗ[R] N` (`AlternatingMap.isBaseChange_baseChangeHom`), yielding the
`S`-linear equivalence `AlternatingMap.baseChangeEquiv`.

## Main definitions

* `AlternatingMap.baseChange`: scalar extension of an alternating map.
* `AlternatingMap.baseChangeHom`: scalar extension as an `R`-linear map.
* `AlternatingMap.baseChangeEquiv`: the comparison isomorphism
  `S ⊗[R] (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[S] ((S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N))` for finite
  projective `M`.

## Main results

* `AlternatingMap.ext_tmul`: two `S`-alternating maps out of `S ⊗[R] M` agree if they agree on
  tuples of pure tensors `1 ⊗ₜ m i`.
* `AlternatingMap.baseChange_apply_tmul`: evaluation of `ω.baseChange S` on tuples of pure
  tensors.
* `AlternatingMap.baseChange_curryLeft`, `AlternatingMap.baseChange_alternatingDerivation`:
  compatibility with interior products and derivations.
* `AlternatingMap.isBaseChange_baseChangeHom`: `baseChangeHom` is a base change when `M` is
  finite projective.
-/

public section

open scoped TensorProduct

namespace AlternatingMap

/-- Scalar multiplication on alternating maps inherits scalar towers from the codomain. -/
instance instIsScalarTower {R S T M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Monoid S] [Monoid T] [SMul S T]
    [DistribMulAction S N] [DistribMulAction T N]
    [SMulCommClass R S N] [SMulCommClass R T N] [IsScalarTower S T N] :
    IsScalarTower S T (M [⋀^ι]→ₗ[R] N) where
  smul_assoc s t f := ext fun v ↦ smul_assoc s t (f v)

/-- Two `S`-alternating maps on finitely many arguments out of `S ⊗[R] M` agree as soon as they
agree on tuples of pure tensors `1 ⊗ₜ[R] m i`. -/
theorem ext_tmul {R S M P ι : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module S P] [Finite ι]
    {f g : (S ⊗[R] M) [⋀^ι]→ₗ[S] P}
    (h : ∀ m : ι → M, f (fun i ↦ (1 : S) ⊗ₜ[R] m i) = g (fun i ↦ (1 : S) ⊗ₜ[R] m i)) :
    f = g := by
  classical
  have := Fintype.ofFinite ι
  -- Induct on the finite set `s` of coordinates not yet reduced to pure tensors `1 ⊗ₜ m`.
  suffices ∀ (s : Finset ι) (v : ι → S ⊗[R] M),
      (∀ i ∉ s, ∃ m : M, v i = (1 : S) ⊗ₜ[R] m) → f v = g v by
    ext v
    exact this Finset.univ v fun _ hi ↦ absurd (Finset.mem_univ _) hi
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro v hv
    choose m hm using fun i ↦ hv i (Finset.notMem_empty i)
    have hv' : v = fun i ↦ (1 : S) ⊗ₜ[R] m i := funext hm
    rw [hv', h m]
  | insert j s hj ih =>
    intro v hv
    have hrest : ∀ i ∉ s, i ≠ j → ∃ m : M, v i = (1 : S) ⊗ₜ[R] m :=
      fun i his hij ↦ hv i (by simp [Finset.mem_insert, his, hij])
    have hstep : ∀ x : S ⊗[R] M, f (Function.update v j x) = g (Function.update v j x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a m =>
        have ha : a ⊗ₜ[R] m = a • ((1 : S) ⊗ₜ[R] m) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [ha, f.map_update_smul, g.map_update_smul]
        congr 1
        refine ih _ fun i his ↦ ?_
        by_cases hij : i = j
        · subst hij; exact ⟨m, Function.update_self i _ v⟩
        · simpa [Function.update_of_ne hij] using hrest i his hij
      | add x y hx hy =>
        rw [f.map_update_add, g.map_update_add, hx, hy]
    simpa [Function.update_eq_self] using hstep (v j)

variable {R : Type*} (S : Type*) {M N : Type*}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Extend scalars on an alternating map `ω : M [⋀^Fin n]→ₗ[R] N` along `R → S`, giving an
`S`-alternating map `(S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N)`. -/
noncomputable def baseChange {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) :
    (S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N) :=
  (exteriorPower.alternatingMapLinearEquiv (R := S) (M := S ⊗[R] M) (N := S ⊗[R] N)).symm
    (((exteriorPower.alternatingMapLinearEquiv (R := R) (M := M) (N := N) ω).baseChange S).comp
      (TauCeti.exteriorPower.equivBaseChange S n).toLinearMap)

/-- Evaluating `ω.baseChange S` on a tuple of pure tensors multiplies the scalar coefficients and
tensors with the value of `ω`. -/
@[simp]
theorem baseChange_apply_tmul {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) (s : Fin n → S) (m : Fin n → M) :
    ω.baseChange S (fun i ↦ s i ⊗ₜ[R] m i) = (∏ i, s i) ⊗ₜ[R] ω m := by
  simp [baseChange]

/-- Evaluating `ω.baseChange S` on pure tensors with unit scalar coefficients. -/
theorem baseChange_apply_one_tmul {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) (m : Fin n → M) :
    ω.baseChange S (fun i ↦ (1 : S) ⊗ₜ[R] m i) = (1 : S) ⊗ₜ[R] ω m := by
  simp

/-- Scalar extension sends the zero alternating map to zero. -/
@[simp]
theorem baseChange_zero {n : ℕ} : (0 : M [⋀^Fin n]→ₗ[R] N).baseChange S = 0 := by
  refine ext_tmul fun m ↦ ?_
  simp

/-- Scalar extension of alternating maps is additive. -/
@[simp]
theorem baseChange_add {n : ℕ} (ω₁ ω₂ : M [⋀^Fin n]→ₗ[R] N) :
    (ω₁ + ω₂).baseChange S = ω₁.baseChange S + ω₂.baseChange S := by
  refine ext_tmul fun m ↦ ?_
  simp [TensorProduct.tmul_add]

/-- Scalar extension of alternating maps preserves negation. -/
@[simp]
theorem baseChange_neg {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) :
    (-ω).baseChange S = -ω.baseChange S := by
  refine ext_tmul fun m ↦ ?_
  simp [TensorProduct.tmul_neg]

/-- Scalar extension of alternating maps preserves subtraction. -/
@[simp]
theorem baseChange_sub {n : ℕ} (ω₁ ω₂ : M [⋀^Fin n]→ₗ[R] N) :
    (ω₁ - ω₂).baseChange S = ω₁.baseChange S - ω₂.baseChange S := by
  refine ext_tmul fun m ↦ ?_
  simp [TensorProduct.tmul_sub]

/-- Scalar extension of alternating maps is `R`-linear. -/
@[simp]
theorem baseChange_smul {n : ℕ} (r : R) (ω : M [⋀^Fin n]→ₗ[R] N) :
    (r • ω).baseChange S = r • ω.baseChange S := by
  refine ext_tmul fun m ↦ ?_
  simp [TensorProduct.tmul_smul]

/-- Scalar extension commutes with interior products on pure tensors. -/
theorem baseChange_curryLeft {n : ℕ} (ω : M [⋀^Fin (n + 1)]→ₗ[R] N) (s : S) (x : M) :
    (ω.baseChange S).curryLeft (s ⊗ₜ[R] x) = s • (ω.curryLeft x).baseChange S := by
  refine ext_tmul fun m ↦ ?_
  have hcons : Matrix.vecCons (s ⊗ₜ[R] x) (fun i : Fin n ↦ (1 : S) ⊗ₜ[R] m i) =
      fun i : Fin (n + 1) ↦ Matrix.vecCons s (fun _ ↦ (1 : S)) i ⊗ₜ[R] Matrix.vecCons x m i := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp
  rw [curryLeft_apply_apply, hcons, baseChange_apply_tmul, smul_apply, baseChange_apply_one_tmul,
    curryLeft_apply_apply, Fin.prod_univ_succ]
  simp [TensorProduct.smul_tmul']

/-- Scalar extension commutes with precomposition by a linear map. -/
theorem baseChange_compLinearMap {M' : Type*} [AddCommGroup M'] [Module R M'] {n : ℕ}
    (f : M' →ₗ[R] M) (ω : M [⋀^Fin n]→ₗ[R] N) :
    (ω.compLinearMap f).baseChange S = (ω.baseChange S).compLinearMap (f.baseChange S) := by
  refine ext_tmul fun m ↦ ?_
  simp

/-- Scalar extension commutes with postcomposition by a linear map. -/
theorem baseChange_compAlternatingMap {N' : Type*} [AddCommGroup N'] [Module R N'] {n : ℕ}
    (g : N →ₗ[R] N') (ω : M [⋀^Fin n]→ₗ[R] N) :
    (g.compAlternatingMap ω).baseChange S =
      (g.baseChange S).compAlternatingMap (ω.baseChange S) := by
  refine ext_tmul fun m ↦ ?_
  simp

/-- Scalar extension commutes with the derivation induced by a linear endomorphism. -/
theorem baseChange_alternatingDerivation {n : ℕ} (f : M →ₗ[R] M) (ω : M [⋀^Fin n]→ₗ[R] N) :
    (f.alternatingDerivation ω).baseChange S =
      (f.baseChange S).alternatingDerivation (ω.baseChange S) := by
  refine ext_tmul fun m ↦ ?_
  rw [baseChange_apply_one_tmul, LinearMap.alternatingDerivation_apply,
    LinearMap.alternatingDerivation_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hupd : Function.update (fun j : Fin n ↦ (1 : S) ⊗ₜ[R] m j) i
      (f.baseChange S ((1 : S) ⊗ₜ[R] m i)) =
      fun j : Fin n ↦ (1 : S) ⊗ₜ[R] Function.update m i (f (m i)) j := by
    ext j
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij]
  rw [hupd, baseChange_apply_one_tmul]

variable (R M N)

/-- Scalar extension of alternating maps, packaged as an `R`-linear map. -/
noncomputable def baseChangeHom (n : ℕ) :
    (M [⋀^Fin n]→ₗ[R] N) →ₗ[R] ((S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N)) where
  toFun := baseChange S
  map_add' := baseChange_add S
  map_smul' := baseChange_smul S

/-- `baseChangeHom` sends an alternating map `ω` to `ω.baseChange S`. -/
@[simp]
theorem baseChangeHom_apply {n : ℕ} (ω : M [⋀^Fin n]→ₗ[R] N) :
    baseChangeHom R S M N n ω = ω.baseChange S :=
  (rfl)

/-- **Alternating maps out of a finite projective module commute with base change.** If `M` is
finitely generated and projective over `R`, then `AlternatingMap.baseChangeHom R S M N n` exhibits
`(S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N)` as the base change of `M [⋀^Fin n]→ₗ[R] N` along `R → S`. -/
theorem isBaseChange_baseChangeHom [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    IsBaseChange S (baseChangeHom R S M N n) := by
  let e₁ : (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] (⋀[R]^n M →ₗ[R] N) :=
    exteriorPower.alternatingMapLinearEquiv
  let e₂ : (S ⊗[R] ⋀[R]^n M →ₗ[S] S ⊗[R] N) ≃ₗ[S] ((S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N)) :=
    (LinearEquiv.congrLeft (S ⊗[R] N) S (TauCeti.exteriorPower.equivBaseChange S n).symm).trans
      exteriorPower.alternatingMapLinearEquiv.symm
  have hlin : IsBaseChange S (LinearMap.baseChangeHom R S (⋀[R]^n M) N) :=
    LinearMap.isBaseChange_baseChangeHom R S (⋀[R]^n M) N
  let e : S ⊗[R] (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[S] ((S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N)) :=
    (e₁.baseChange R S _ _).trans (hlin.equiv.trans e₂)
  refine IsBaseChange.of_equiv e fun ω ↦ ?_
  refine ext_tmul fun m ↦ ?_
  -- Unfold the composite equivalence `e` on `1 ⊗ₜ ω` to evaluate on `1 ⊗ₜ m i`.
  change (e₂ (hlin.equiv (1 ⊗ₜ[R] e₁ ω))) (fun i ↦ (1 : S) ⊗ₜ[R] m i) = _
  rw [IsBaseChange.equiv_tmul, one_smul]
  simp [e₁, e₂, baseChange]

/-- The `S`-linear equivalence
`S ⊗[R] (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[S] ((S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N))` for a finitely
generated projective `R`-module `M`. -/
noncomputable def baseChangeEquiv [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    S ⊗[R] (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[S] ((S ⊗[R] M) [⋀^Fin n]→ₗ[S] (S ⊗[R] N)) :=
  (isBaseChange_baseChangeHom R S M N n).equiv

/-- `baseChangeEquiv` sends a pure tensor `s ⊗ₜ ω` to `s • ω.baseChange S`. -/
@[simp]
theorem baseChangeEquiv_tmul [Module.Finite R M] [Module.Projective R M] (n : ℕ) (s : S)
    (ω : M [⋀^Fin n]→ₗ[R] N) :
    baseChangeEquiv R S M N n (s ⊗ₜ[R] ω) = s • ω.baseChange S :=
  (isBaseChange_baseChangeHom R S M N n).equiv_tmul s ω

end AlternatingMap
