/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Module.Projective.Trans
public import TauCeti.Algebra.MonoidAlgebra.Augmentation
public import TauCeti.Algebra.MonoidAlgebra.Basis
public import TauCeti.Algebra.MonoidAlgebra.CosetBasis
public import TauCeti.LinearAlgebra.Trace.HattoriStallings.Basic

/-!
# Hattori–Stallings traces for group rings and coinvariants

For a ring `Λ` (not necessarily commutative) and a group `G`, taking the coefficient at `1 ∈ G`
sends commutators in `Λ[G]` into `[Λ, Λ]` and hence induces an additive homomorphism

```text
ε : Λ[G] / [Λ[G], Λ[G]] →+ Λ / [Λ, Λ]
```

(`MonoidAlgebra.cyclicCoeffOne`). Composing `ε` with the Hattori–Stallings trace on a finitely
generated projective left `Λ[G]`-module `P` defines the group-ring trace
`LinearMap.groupAlgebraTrace Λ G P` (written `Tr^G` in Stacks §64.15).

For a finite-index subgroup `H ≤ G`, restricting `P` to `Λ[H]` multiplies the group-ring trace by
the index `[G : H]` (`LinearMap.groupAlgebraTrace_restrictSubgroup`). When `G` is finite,
restricting to `Λ` gives `Tr_Λ(u, P) = |G| · Tr^G(u, P)`
(`LinearMap.hattoriStallingsTrace_restrictScalars_eq_card_nsmul_groupAlgebraTrace`), without
inverting `|G|` in `Λ`.

We also construct the coinvariants `MonoidAlgebra.Coinvariants Λ G P` of a left `Λ[G]`-module over
an arbitrary ring `Λ` (Mathlib's `Representation.Coinvariants` requires a commutative ring; we
record the linear equivalence with it over commutative rings). When `P` is finite projective over
`Λ[G]`, its coinvariants `P_G` are finite projective over `Λ`, and the trace of the induced
endomorphism `u_G` is the image of `Tr_{Λ[G]}(u, P)` under the augmentation map
`Λ[G] / [Λ[G], Λ[G]] →+ Λ / [Λ, Λ]` (`MonoidAlgebra.Coinvariants.hattoriStallingsTrace_map`).

## Main definitions

* `TauCeti.cyclicQuotientMap`: functoriality of `R / [R, R]` under ring homomorphisms.
* `TauCeti.cyclicQuotientEquivSelf`: identification `A / [A, A] ≃+ A` for a commutative ring `A`.
* `TauCeti.cyclicQuotientSMul`: the action of a central commutative ring `A` on `Λ / [Λ, Λ]`.
* `MonoidAlgebra.cyclicCoeffOne`: the identity-coefficient homomorphism
  `Λ[G] / [Λ[G], Λ[G]] →+ Λ / [Λ, Λ]`.
* `LinearMap.groupAlgebraTrace`: the group-ring Hattori–Stallings trace `Tr^G = ε ∘ Tr_HS`.
* `LinearMap.groupAlgebraScalarTrace`: the scalar-valued specialization of `Tr^G` over a
  commutative ring `A`.
* `MonoidAlgebra.Coinvariants`: coinvariants of a left `Λ[G]`-module over an arbitrary ring `Λ`.

## References

* The Stacks Project, Section 64.15, Lemmas 64.15.1–64.15.2 (Tags `03U5`–`03U6`).
-/

public section

noncomputable section

open Module MonoidAlgebra TensorProduct

namespace TauCeti

section CyclicQuotient

variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

/-- A ring homomorphism descends to an additive homomorphism on additive cyclic quotients. -/
def cyclicQuotientMap (f : R →+* S) : cyclicQuotient ℤ R →+ cyclicQuotient ℤ S :=
  (Submodule.liftQ (commutatorSubmodule ℤ R)
    ((commutatorSubmodule ℤ S).mkQ.comp f.toAddMonoidHom.toIntLinearMap) <|
      (commutatorSubmodule_le_ker_iff _).2 fun x y ↦ by
        change (commutatorSubmodule ℤ S).mkQ (f (x * y)) =
          (commutatorSubmodule ℤ S).mkQ (f (y * x))
        rw [map_mul f, map_mul f, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        exact mul_sub_mul_mem_commutatorSubmodule ℤ S (f x) (f y)).toAddMonoidHom

/-- Evaluation of `cyclicQuotientMap` on a cyclic class. -/
theorem cyclicQuotientMap_mkQ (f : R →+* S) (x : R) :
    cyclicQuotientMap f ((commutatorSubmodule ℤ R).mkQ x) =
      (commutatorSubmodule ℤ S).mkQ (f x) :=
  (rfl)

/-- `cyclicQuotientMap` preserves the identity ring homomorphism. -/
@[simp]
theorem cyclicQuotientMap_id :
    cyclicQuotientMap (RingHom.id R) = AddMonoidHom.id (cyclicQuotient ℤ R) := by
  ext x
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply]
  exact cyclicQuotientMap_mkQ (RingHom.id R) r

/-- `cyclicQuotientMap` preserves composition of ring homomorphisms. -/
@[simp]
theorem cyclicQuotientMap_comp (g : S →+* T) (f : R →+* S) :
    cyclicQuotientMap (g.comp f) = (cyclicQuotientMap g).comp (cyclicQuotientMap f) := by
  ext x
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, AddMonoidHom.comp_apply, cyclicQuotientMap_mkQ,
    cyclicQuotientMap_mkQ, cyclicQuotientMap_mkQ, RingHom.comp_apply]

/-- Over a commutative ring the commutator submodule is zero. -/
@[simp]
theorem commutatorSubmodule_eq_bot (k A : Type*) [Semiring k] [CommRing A] [Module k A] :
    commutatorSubmodule k A = ⊥ := by
  rw [← LinearMap.ker_id (R := k) (M := A)]
  exact le_antisymm
    ((commutatorSubmodule_le_ker_iff (LinearMap.id : A →ₗ[k] A)).2 fun x y ↦ mul_comm x y)
    bot_le

/-- The additive cyclic quotient of a commutative ring is canonically isomorphic to the ring. -/
def cyclicQuotientEquivSelf (A : Type*) [CommRing A] : cyclicQuotient ℤ A ≃+ A :=
  (Submodule.quotEquivOfEqBot (commutatorSubmodule ℤ A) (commutatorSubmodule_eq_bot ℤ A)).toAddEquiv

/-- Evaluating `cyclicQuotientEquivSelf` on a cyclic class recovers the element. -/
theorem cyclicQuotientEquivSelf_mkQ (A : Type*) [CommRing A] (a : A) :
    cyclicQuotientEquivSelf A ((commutatorSubmodule ℤ A).mkQ a) = a :=
  (rfl)

/-- The inverse of `cyclicQuotientEquivSelf` is the quotient projection. -/
@[simp]
theorem cyclicQuotientEquivSelf_symm_apply (A : Type*) [CommRing A] (a : A) :
    (cyclicQuotientEquivSelf A).symm a = (commutatorSubmodule ℤ A).mkQ a :=
  (rfl)

/-- On commutative rings `cyclicQuotientMap` corresponds to the ring homomorphism itself. -/
@[simp]
theorem cyclicQuotientEquivSelf_cyclicQuotientMap {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : cyclicQuotient ℤ A) :
    cyclicQuotientEquivSelf B (cyclicQuotientMap f x) = f (cyclicQuotientEquivSelf A x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

section CentralSMul

variable (A Λ : Type*) [CommRing A] [Ring Λ] [Algebra A Λ]

/-- Scalar multiplication by a central commutative ring `A` on the additive cyclic quotient
`Λ / [Λ, Λ]`. Kept as an explicit family of additive homomorphisms rather than a global `Module`
instance to avoid a diamond with the canonical `Module ℤ` structure on the quotient. -/
def cyclicQuotientSMul (a : A) : cyclicQuotient ℤ Λ →+ cyclicQuotient ℤ Λ :=
  (Submodule.liftQ (commutatorSubmodule ℤ Λ)
    ((commutatorSubmodule ℤ Λ).mkQ.comp
      ({ toFun := fun x ↦ algebraMap A Λ a * x
         map_add' := mul_add _
         map_smul' := fun n x ↦ by
           simp only [RingHom.id_apply]
           exact mul_smul_comm n (algebraMap A Λ a) x } : Λ →ₗ[ℤ] Λ)) <|
      (commutatorSubmodule_le_ker_iff _).2 fun x y ↦ by
        change (commutatorSubmodule ℤ Λ).mkQ (algebraMap A Λ a * (x * y)) =
          (commutatorSubmodule ℤ Λ).mkQ (algebraMap A Λ a * (y * x))
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        have h : algebraMap A Λ a * (x * y) - algebraMap A Λ a * (y * x) =
            (algebraMap A Λ a * x) * y - y * (algebraMap A Λ a * x) := by
          rw [mul_assoc (algebraMap A Λ a) x y, ← mul_assoc y (algebraMap A Λ a) x,
            ← Algebra.commutes a y, mul_assoc]
        rw [h]
        exact mul_sub_mul_mem_commutatorSubmodule ℤ Λ _ _).toAddMonoidHom

/-- Action of `cyclicQuotientSMul` on a cyclic class. -/
theorem cyclicQuotientSMul_mkQ (a : A) (x : Λ) :
    cyclicQuotientSMul A Λ a ((commutatorSubmodule ℤ Λ).mkQ x) =
      (commutatorSubmodule ℤ Λ).mkQ (algebraMap A Λ a * x) :=
  (rfl)

@[simp]
theorem cyclicQuotientSMul_zero (x : cyclicQuotient ℤ Λ) :
    cyclicQuotientSMul A Λ 0 x = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, cyclicQuotientSMul_mkQ, map_zero, zero_mul, map_zero]

@[simp]
theorem cyclicQuotientSMul_one (x : cyclicQuotient ℤ Λ) :
    cyclicQuotientSMul A Λ 1 x = x := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, cyclicQuotientSMul_mkQ, map_one, one_mul]

theorem cyclicQuotientSMul_add (a b : A) (x : cyclicQuotient ℤ Λ) :
    cyclicQuotientSMul A Λ (a + b) x =
      cyclicQuotientSMul A Λ a x + cyclicQuotientSMul A Λ b x := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, cyclicQuotientSMul_mkQ, cyclicQuotientSMul_mkQ,
    cyclicQuotientSMul_mkQ, map_add, add_mul, map_add]

theorem cyclicQuotientSMul_mul (a b : A) (x : cyclicQuotient ℤ Λ) :
    cyclicQuotientSMul A Λ (a * b) x =
      cyclicQuotientSMul A Λ a (cyclicQuotientSMul A Λ b x) := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, cyclicQuotientSMul_mkQ, cyclicQuotientSMul_mkQ,
    cyclicQuotientSMul_mkQ, map_mul (algebraMap A Λ), mul_assoc]

theorem cyclicQuotientSMul_sum {ι : Type*} (s : Finset ι) (f : ι → A)
    (x : cyclicQuotient ℤ Λ) :
    cyclicQuotientSMul A Λ (∑ i ∈ s, f i) x =
      ∑ i ∈ s, cyclicQuotientSMul A Λ (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, cyclicQuotientSMul_add, ih, Finset.sum_insert hi]

/-- Over a commutative algebra `Λ`, `cyclicQuotientSMul` agrees with multiplication by
`algebraMap A Λ a`. -/
@[simp]
theorem cyclicQuotientEquivSelf_cyclicQuotientSMul {A Λ : Type*} [CommRing A] [CommRing Λ]
    [Algebra A Λ] (a : A) (x : cyclicQuotient ℤ Λ) :
    cyclicQuotientEquivSelf Λ (cyclicQuotientSMul A Λ a x) =
      algebraMap A Λ a * cyclicQuotientEquivSelf Λ x := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, cyclicQuotientSMul_mkQ, cyclicQuotientEquivSelf_mkQ,
    cyclicQuotientEquivSelf_mkQ]

end CentralSMul

end CyclicQuotient

end TauCeti

namespace LinearMap

section SemilinearAndBaseChange

variable {R S : Type*} [Ring R] [Ring S]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- Transporting an endomorphism along a semilinear equivalence over mutually inverse ring
homomorphisms transports its Hattori–Stallings trace along the induced map on cyclic quotients. -/
theorem hattoriStallingsTrace_conj_semilinear [Module.Finite R M] [Module.Projective R M]
    [Module.Finite S N] [Module.Projective S N] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (e : M ≃ₛₗ[σ] N) (f : Module.End R M) :
    hattoriStallingsTrace S N
        (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) =
      TauCeti.cyclicQuotientMap σ (hattoriStallingsTrace R M f) := by
  classical
  obtain ⟨n, r, i, -, -, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let eF : (Fin n → R) ≃ₛₗ[σ] (Fin n → S) :=
    { toFun := fun v k ↦ σ (v k)
      invFun := fun w k ↦ σ' (w k)
      left_inv := fun v ↦ funext fun k ↦ RingHomInvPair.comp_apply_eq
      right_inv := fun w ↦ funext fun k ↦ RingHomInvPair.comp_apply_eq₂
      map_add' := fun u v ↦ funext fun k ↦ map_add σ (u k) (v k)
      map_smul' := fun a v ↦ funext fun k ↦ map_mul σ a (v k) }
  let i' : N →ₗ[S] (Fin n → S) := eF.toLinearMap.comp (i.comp e.symm.toLinearMap)
  let r' : (Fin n → S) →ₗ[S] N := e.toLinearMap.comp (r.comp eF.symm.toLinearMap)
  have hr' : r' ∘ₗ i' = .id := by
    ext x
    change e (r (eF.symm (eF (i (e.symm x))))) = x
    rw [eF.symm_apply_apply]
    have hrx : r (i (e.symm x)) = e.symm x := congrArg (fun g : Module.End R M ↦ g (e.symm x)) hr
    rw [hrx, e.apply_symm_apply]
  rw [hattoriStallingsTrace_eq_of_retract (Pi.basisFun S (Fin n)) i' r' hr',
    hattoriStallingsTrace_eq_of_retract (Pi.basisFun R (Fin n)) i r hr,
    Basis.hattoriStallingsTrace_apply, Basis.hattoriStallingsTrace_apply,
    TauCeti.cyclicQuotientMap_mkQ]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have heF : eF.symm (Pi.single k (1 : S)) = Pi.single k (1 : R) := by
    ext j
    by_cases hjk : j = k <;> simp [eF, hjk]
  simp only [Pi.basisFun_repr, Pi.basisFun_apply, comp_apply, i', r', LinearEquiv.coe_coe, heF,
    e.symm_apply_apply]
  rfl

/-- Over a commutative ring, identifying `A / [A, A]` with `A` turns the Hattori–Stallings trace
into `LinearMap.projectiveTrace`. -/
@[simp]
theorem cyclicQuotientEquivSelf_hattoriStallingsTrace {A P : Type*} [CommRing A] [AddCommGroup P]
    [Module A P] [Module.Finite A P] [Module.Projective A P] (f : Module.End A P) :
    TauCeti.cyclicQuotientEquivSelf A (hattoriStallingsTrace A P f) = projectiveTrace A P f := by
  rw [hattoriStallingsTrace_eq_projectiveTrace, TauCeti.cyclicQuotientEquivSelf_mkQ]

/-- Extending scalars of a finite projective module over a commutative ring `A` to an arbitrary
`A`-algebra `Λ` carries the Hattori–Stallings trace along `algebraMap A Λ`. -/
theorem hattoriStallingsTrace_baseChange {A Λ P : Type*} [CommRing A] [Ring Λ] [Algebra A Λ]
    [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P]
    (f : Module.End A P) :
    hattoriStallingsTrace Λ (Λ ⊗[A] P) (f.baseChange Λ) =
      TauCeti.cyclicQuotientMap (algebraMap A Λ) (hattoriStallingsTrace A P f) := by
  classical
  obtain ⟨n, r, i, -, -, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  let eF : Λ ⊗[A] (Fin n → A) ≃ₗ[Λ] (Fin n → Λ) :=
    LinearEquiv.ofLinearMap
      (AlgebraTensorModule.lift
        { toFun := fun l ↦
            { toFun := fun v k ↦ l * algebraMap A Λ (v k)
              map_add' := fun u v ↦ funext fun k ↦ by simp [mul_add]
              map_smul' := fun a v ↦ funext fun k ↦ by
                change l * algebraMap A Λ (a * v k) = a • (l * algebraMap A Λ (v k))
                rw [map_mul, Algebra.smul_def, ← mul_assoc, ← Algebra.commutes a l, mul_assoc] }
          map_add' := fun l₁ l₂ ↦ by ext v k; simp [add_mul]
          map_smul' := fun l₁ l₂ ↦ by ext v k; simp [mul_assoc] })
      { toFun := fun w ↦ ∑ k : Fin n, w k ⊗ₜ[A] Pi.single k (1 : A)
        map_add' := fun u v ↦ by simp [Finset.sum_add_distrib, add_tmul]
        map_smul' := fun l w ↦ by simp [Finset.smul_sum, smul_tmul'] }
      (by
        apply LinearMap.ext
        intro w
        funext j
        simp only [comp_apply, id_apply, coe_mk, AddHom.coe_mk, map_sum,
          AlgebraTensorModule.lift_apply, Finset.sum_apply]
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hkj
          simp [Pi.single_eq_of_ne (Ne.symm hkj)]
        · intro hj
          exact absurd (Finset.mem_univ j) hj)
      (by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp [map_add, hx, hy]
        | tmul l v =>
          change ∑ k : Fin n, (l * algebraMap A Λ (v k)) ⊗ₜ[A] Pi.single k (1 : A) = l ⊗ₜ[A] v
          have hv : v = ∑ k : Fin n, v k • Pi.single k (1 : A) := by
            ext j; simp [Pi.single_apply]
          conv_rhs => rw [hv, tmul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [← Algebra.commutes (v k) l, ← Algebra.smul_def, smul_tmul])
  let i' : Λ ⊗[A] P →ₗ[Λ] (Fin n → Λ) := eF.toLinearMap ∘ₗ i.baseChange Λ
  let r' : (Fin n → Λ) →ₗ[Λ] Λ ⊗[A] P := r.baseChange Λ ∘ₗ eF.symm.toLinearMap
  have hr' : r' ∘ₗ i' = .id := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul l p =>
      change r.baseChange Λ (eF.symm (eF (i.baseChange Λ (l ⊗ₜ[A] p)))) = l ⊗ₜ[A] p
      rw [eF.symm_apply_apply, baseChange_tmul, baseChange_tmul]
      have hp : r (i p) = p := congrArg (fun g : Module.End A P ↦ g p) hr
      rw [hp]
  rw [hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin n)) i' r' hr',
    hattoriStallingsTrace_eq_of_retract (Pi.basisFun A (Fin n)) i r hr,
    Basis.hattoriStallingsTrace_apply, Basis.hattoriStallingsTrace_apply,
    TauCeti.cyclicQuotientMap_mkQ]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have heF_symm : eF.symm (Pi.single k (1 : Λ)) = (1 : Λ) ⊗ₜ[A] Pi.single k (1 : A) := by
    change ∑ j : Fin n, (Pi.single k (1 : Λ) j) ⊗ₜ[A] Pi.single j (1 : A) =
      (1 : Λ) ⊗ₜ[A] Pi.single k (1 : A)
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hjk
      simp [Pi.single_eq_of_ne hjk]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  simp only [Pi.basisFun_repr, Pi.basisFun_apply, comp_apply, i', r', LinearEquiv.coe_coe,
    heF_symm, baseChange_tmul]
  change (1 : Λ) * algebraMap A Λ (i (f (r (Pi.single k 1))) k) =
    algebraMap A Λ (i (f (r (Pi.single k 1))) k)
  rw [one_mul]

end SemilinearAndBaseChange

end LinearMap

namespace MonoidAlgebra

section CyclicCoeffOne

variable {Λ : Type*} [Ring Λ] {G H : Type*} [Group G] [Group H]

/-- In a group ring over an arbitrary ring, the identity coefficient of a commutator is a sum of
commutators in the base ring. -/
theorem coeff_one_mul_sub_mul_mem_commutatorSubmodule (x y : MonoidAlgebra Λ G) :
    (x * y - y * x).coeff 1 ∈ TauCeti.commutatorSubmodule ℤ Λ := by
  induction x using induction_linear with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
    have h : ((x₁ + x₂) * y - y * (x₁ + x₂)).coeff 1 =
        (x₁ * y - y * x₁).coeff 1 + (x₂ * y - y * x₂).coeff 1 := by
      simp [add_mul, mul_add, sub_add_sub_comm]
    rw [h]
    exact add_mem hx₁ hx₂
  | single g a =>
    induction y using induction_linear with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      have h : (single g a * (y₁ + y₂) - (y₁ + y₂) * single g a).coeff 1 =
          (single g a * y₁ - y₁ * single g a).coeff 1 +
            (single g a * y₂ - y₂ * single g a).coeff 1 := by
        simp [add_mul, mul_add, sub_add_sub_comm]
      rw [h]
      exact add_mem hy₁ hy₂
    | single h b =>
      classical
      rw [single_mul_single, single_mul_single, coeff_sub, coeff_single, coeff_single]
      have hiff : g * h = 1 ↔ h * g = 1 := by
        constructor <;> intro hgh
        · rw [eq_inv_of_mul_eq_one_right hgh, inv_mul_cancel]
        · rw [eq_inv_of_mul_eq_one_right hgh, inv_mul_cancel]
      by_cases hgh : g * h = 1
      · simp only [hgh, hiff.mp hgh, Finsupp.sub_apply, Finsupp.single_eq_same]
        exact TauCeti.mul_sub_mul_mem_commutatorSubmodule ℤ Λ a b
      · have hhg : h * g ≠ 1 := hiff.not.mp hgh
        simp [Finsupp.single_eq_of_ne (Ne.symm hgh), Finsupp.single_eq_of_ne (Ne.symm hhg)]

variable (Λ G) in
/-- The identity-coefficient additive homomorphism `ε : Λ[G] / [Λ[G], Λ[G]] →+ Λ / [Λ, Λ]`,
defined over any ring `Λ` and any group `G`. -/
def cyclicCoeffOne :
    TauCeti.cyclicQuotient ℤ (MonoidAlgebra Λ G) →+ TauCeti.cyclicQuotient ℤ Λ :=
  (Submodule.liftQ (TauCeti.commutatorSubmodule ℤ (MonoidAlgebra Λ G))
    ((TauCeti.commutatorSubmodule ℤ Λ).mkQ.comp
      ((Finsupp.applyAddHom (1 : G)).comp coeffAddEquiv.toAddMonoidHom).toIntLinearMap) <|
      (TauCeti.commutatorSubmodule_le_ker_iff _).2 fun x y ↦ by
        change (TauCeti.commutatorSubmodule ℤ Λ).mkQ ((x * y).coeff 1) =
          (TauCeti.commutatorSubmodule ℤ Λ).mkQ ((y * x).coeff 1)
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        simpa [coeff_sub] using coeff_one_mul_sub_mul_mem_commutatorSubmodule x y).toAddMonoidHom

/-- `cyclicCoeffOne` evaluates on a cyclic class by taking the coefficient at `1`. -/
theorem cyclicCoeffOne_mkQ (x : MonoidAlgebra Λ G) :
    cyclicCoeffOne Λ G ((TauCeti.commutatorSubmodule ℤ (MonoidAlgebra Λ G)).mkQ x) =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ (x.coeff 1) :=
  (rfl)

/-- `cyclicCoeffOne` is invariant under monoid isomorphisms `G ≃* H`. -/
@[simp]
theorem cyclicCoeffOne_cyclicQuotientMap_mapDomainRingEquiv (e : G ≃* H)
    (x : TauCeti.cyclicQuotient ℤ (MonoidAlgebra Λ G)) :
    cyclicCoeffOne Λ H
        (TauCeti.cyclicQuotientMap
          (mapDomainRingEquiv Λ e : MonoidAlgebra Λ G →+* MonoidAlgebra Λ H) x) =
      cyclicCoeffOne Λ G x := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, TauCeti.cyclicQuotientMap_mkQ, cyclicCoeffOne_mkQ, cyclicCoeffOne_mkQ]
  congr 1
  change (mapDomainRingEquiv Λ e r).coeff 1 = r.coeff 1
  rw [coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
  change r.coeff (e.symm 1) = r.coeff 1
  rw [map_one]

/-- `cyclicCoeffOne` is natural with respect to ring homomorphisms `f : Λ →+* Λ'`. -/
@[simp]
theorem cyclicCoeffOne_cyclicQuotientMap_mapRingHom {Λ' : Type*} [Ring Λ'] (f : Λ →+* Λ')
    (x : TauCeti.cyclicQuotient ℤ (MonoidAlgebra Λ G)) :
    cyclicCoeffOne Λ' G (TauCeti.cyclicQuotientMap (mapRingHom G f) x) =
      TauCeti.cyclicQuotientMap f (cyclicCoeffOne Λ G x) := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, TauCeti.cyclicQuotientMap_mkQ, cyclicCoeffOne_mkQ, cyclicCoeffOne_mkQ,
    TauCeti.cyclicQuotientMap_mkQ]
  simp [mapRingHom]

end CyclicCoeffOne

section NoncommSubgroupRestriction

variable {Λ : Type*} [Semiring Λ] {G : Type*} [Group G]

/-- Restricting a finitely generated projective `Λ[G]`-module to a finite-index subgroup `H ≤ G`
yields a finitely generated projective `Λ[H]`-module, over an arbitrary (possibly noncommutative)
semiring `Λ`. -/
theorem _root_.Subgroup.restrict_finite_projective (H : Subgroup G) [H.FiniteIndex]
    (P : Type*) [AddCommMonoid P] [Module (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    [Module (MonoidAlgebra Λ H) P]
    (hP : ∀ (r : MonoidAlgebra Λ H) (x : P), r • x = mapDomainRingHom Λ H.subtype r • x) :
    Module.Finite (MonoidAlgebra Λ H) P ∧ Module.Projective (MonoidAlgebra Λ H) P := by
  let : Module (MonoidAlgebra Λ H) (MonoidAlgebra Λ G) :=
    (mapDomainRingHom Λ H.subtype).toModule
  have : IsScalarTower (MonoidAlgebra Λ H) (MonoidAlgebra Λ G) (MonoidAlgebra Λ G) :=
    ⟨fun r s t ↦ mul_assoc (mapDomainRingHom Λ H.subtype r) s t⟩
  have : IsScalarTower (MonoidAlgebra Λ H) (MonoidAlgebra Λ G) P :=
    ⟨fun r s x ↦ by rw [hP r (s • x), ← mul_smul]; rfl⟩
  let b := TauCeti.MonoidAlgebra.basisCosets Λ H.subtype H.subtype_injective
  have : Finite (G ⧸ H.subtype.range) := by
    rw [Subgroup.range_subtype]
    infer_instance
  have : Module.Free (MonoidAlgebra Λ H) (MonoidAlgebra Λ G) := .of_basis b
  have : Module.Finite (MonoidAlgebra Λ H) (MonoidAlgebra Λ G) := .of_basis b
  exact ⟨.trans (MonoidAlgebra Λ G) P, .trans (MonoidAlgebra Λ G) P⟩

/-- A finitely generated projective `Λ[G]`-module for a finite group `G` is finitely generated and
projective over `Λ`, with no commutativity assumption on `Λ`. -/
theorem finite_projective_of_monoidAlgebra [Finite G] (P : Type*) [AddCommMonoid P]
    [Module Λ P] [Module (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    Module.Finite Λ P ∧ Module.Projective Λ P := by
  have : Module.Free Λ (MonoidAlgebra Λ G) := .of_basis (MonoidAlgebra.basis G Λ)
  have : Module.Finite Λ (MonoidAlgebra Λ G) := .of_basis (MonoidAlgebra.basis G Λ)
  exact ⟨.trans (MonoidAlgebra Λ G) P, .trans (MonoidAlgebra Λ G) P⟩

end NoncommSubgroupRestriction

end MonoidAlgebra

namespace LinearMap

section GroupAlgebraTrace

variable {Λ : Type*} [Ring Λ] {G H : Type*} [Group G] [Group H]
variable {P Q : Type*} [AddCommGroup P] [Module (MonoidAlgebra Λ G) P]
variable [AddCommGroup Q] [Module (MonoidAlgebra Λ G) Q]

variable (Λ G P) in
/-- The group-ring Hattori–Stallings trace `Tr^G = ε ∘ Tr_HS` on a finitely generated projective
left `Λ[G]`-module, taking values in the additive cyclic quotient `Λ / [Λ, Λ]`. -/
def groupAlgebraTrace [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] :
    Module.End (MonoidAlgebra Λ G) P →+ TauCeti.cyclicQuotient ℤ Λ :=
  (MonoidAlgebra.cyclicCoeffOne Λ G).comp (hattoriStallingsTrace (MonoidAlgebra Λ G) P)

@[simp]
theorem groupAlgebraTrace_apply [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] (f : Module.End (MonoidAlgebra Λ G) P) :
    groupAlgebraTrace Λ G P f =
      MonoidAlgebra.cyclicCoeffOne Λ G (hattoriStallingsTrace (MonoidAlgebra Λ G) P f) :=
  (rfl)

/-- Compute `groupAlgebraTrace` in any finite free `Λ[G]`-retract. -/
theorem groupAlgebraTrace_eq_of_retract [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] {F : Type*} [AddCommGroup F]
    [Module (MonoidAlgebra Λ G) F] {ι : Type*} [Fintype ι]
    (b : Basis ι (MonoidAlgebra Λ G) F) (i : P →ₗ[MonoidAlgebra Λ G] F)
    (r : F →ₗ[MonoidAlgebra Λ G] P) (hr : r ∘ₗ i = .id)
    (f : Module.End (MonoidAlgebra Λ G) P) :
    groupAlgebraTrace Λ G P f =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (∑ k : ι, (b.repr (i (f (r (b k)))) k).coeff 1) := by
  rw [groupAlgebraTrace_apply, hattoriStallingsTrace_eq_of_retract b i r hr,
    Basis.hattoriStallingsTrace_apply, MonoidAlgebra.cyclicCoeffOne_mkQ, coeff_sum]
  congr 1
  exact map_sum (Finsupp.applyAddHom (1 : G)) _ _

/-- Compute `groupAlgebraTrace` in any finite `Λ[G]`-basis. -/
theorem groupAlgebraTrace_eq_of_basis [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] {ι : Type*} [Fintype ι]
    (b : Basis ι (MonoidAlgebra Λ G) P) (f : Module.End (MonoidAlgebra Λ G) P) :
    groupAlgebraTrace Λ G P f =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ (∑ k : ι, (b.repr (f (b k)) k).coeff 1) := by
  simpa using groupAlgebraTrace_eq_of_retract b .id .id (by simp) f

/-- On the rank-one free module `Λ[G]`, the group-ring trace of a `Λ[G]`-linear endomorphism `f`
is the cyclic class of the identity coefficient of `f 1`. -/
theorem groupAlgebraTrace_self_apply (f : Module.End (MonoidAlgebra Λ G) (MonoidAlgebra Λ G)) :
    groupAlgebraTrace Λ G (MonoidAlgebra Λ G) f =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ ((f 1).coeff 1) := by
  rw [groupAlgebraTrace_eq_of_basis (Basis.singleton Unit (MonoidAlgebra Λ G))]
  simp

/-- Cyclicity of the group-ring trace across finite projective `Λ[G]`-modules. -/
theorem groupAlgebraTrace_comp_comm [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q] (f : P →ₗ[MonoidAlgebra Λ G] Q)
    (g : Q →ₗ[MonoidAlgebra Λ G] P) :
    groupAlgebraTrace Λ G P (g ∘ₗ f) = groupAlgebraTrace Λ G Q (f ∘ₗ g) := by
  rw [groupAlgebraTrace_apply, groupAlgebraTrace_apply, hattoriStallingsTrace_comp_comm]

/-- Invariance of the group-ring trace under `Λ[G]`-linear conjugation. -/
theorem groupAlgebraTrace_conj [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q] (f : Module.End (MonoidAlgebra Λ G) P)
    (e : P ≃ₗ[MonoidAlgebra Λ G] Q) :
    groupAlgebraTrace Λ G Q (e.conjRingEquiv f) = groupAlgebraTrace Λ G P f := by
  simp only [groupAlgebraTrace_apply, hattoriStallingsTrace_conj]

/-- Additivity of the group-ring trace on products. -/
theorem groupAlgebraTrace_prodMap [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q] (f : Module.End (MonoidAlgebra Λ G) P)
    (g : Module.End (MonoidAlgebra Λ G) Q) :
    groupAlgebraTrace Λ G (P × Q) (f.prodMap g) =
      groupAlgebraTrace Λ G P f + groupAlgebraTrace Λ G Q g := by
  simp only [groupAlgebraTrace_apply, hattoriStallingsTrace_prodMap, map_add]

/-- Additivity of the group-ring trace from a decomposition of the identity. -/
theorem groupAlgebraTrace_eq_add_of_id_decomposition {R' : Type*} [AddCommGroup R']
    [Module (MonoidAlgebra Λ G) R'] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ G) Q]
    [Module.Projective (MonoidAlgebra Λ G) Q] [Module.Finite (MonoidAlgebra Λ G) R']
    [Module.Projective (MonoidAlgebra Λ G) R']
    (i : P →ₗ[MonoidAlgebra Λ G] R') (r : R' →ₗ[MonoidAlgebra Λ G] P)
    (j : Q →ₗ[MonoidAlgebra Λ G] R') (s : R' →ₗ[MonoidAlgebra Λ G] Q)
    (h : i ∘ₗ r + j ∘ₗ s = .id) (f : Module.End (MonoidAlgebra Λ G) R') :
    groupAlgebraTrace Λ G R' f =
      groupAlgebraTrace Λ G P (r ∘ₗ f ∘ₗ i) + groupAlgebraTrace Λ G Q (s ∘ₗ f ∘ₗ j) := by
  simp only [groupAlgebraTrace_apply, hattoriStallingsTrace_eq_add_of_id_decomposition i r j s h,
    map_add]

/-- The group-ring trace vanishes on a subsingleton module. -/
theorem groupAlgebraTrace_eq_zero_of_subsingleton [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Subsingleton P]
    (f : Module.End (MonoidAlgebra Λ G) P) :
    groupAlgebraTrace Λ G P f = 0 := by
  simp only [groupAlgebraTrace_apply, hattoriStallingsTrace_eq_zero_of_subsingleton, map_zero]

/-- Conjugating along an additive equivalence intertwining `Λ[G]` and `Λ[H]` via a group
isomorphism `e : G ≃* H` preserves the group-ring trace. -/
theorem groupAlgebraTrace_conj_equiv {Q' : Type*} [AddCommGroup Q']
    [Module (MonoidAlgebra Λ H) Q'] [Module.Finite (MonoidAlgebra Λ G) P]
    [Module.Projective (MonoidAlgebra Λ G) P] [Module.Finite (MonoidAlgebra Λ H) Q']
    [Module.Projective (MonoidAlgebra Λ H) Q'] (e : G ≃* H) (eP : P ≃+ Q')
    (heP : ∀ (r : MonoidAlgebra Λ G) (x : P),
      eP (r • x) = mapDomainRingHom Λ e.toMonoidHom r • eP x)
    (f : Module.End (MonoidAlgebra Λ G) P) (f' : Module.End (MonoidAlgebra Λ H) Q')
    (hf : ∀ x, f' (eP x) = eP (f x)) :
    groupAlgebraTrace Λ H Q' f' = groupAlgebraTrace Λ G P f := by
  have := RingHomInvPair.of_ringEquiv (mapDomainRingEquiv Λ e)
  have := RingHomInvPair.of_ringEquiv_symm (mapDomainRingEquiv Λ e)
  let eL : P ≃ₛₗ[(mapDomainRingEquiv Λ e : MonoidAlgebra Λ G →+* MonoidAlgebra Λ H)] Q' :=
    { eP with map_smul' := fun r x ↦ heP r x }
  have hf' : f' = eL.toLinearMap.comp (f.comp eL.symm.toLinearMap) := by
    ext y
    obtain ⟨x, rfl⟩ := eP.surjective y
    change f' (eP x) = eP (f (eP.symm (eP x)))
    rw [eP.symm_apply_apply, hf]
  rw [hf', groupAlgebraTrace_apply, hattoriStallingsTrace_conj_semilinear,
    MonoidAlgebra.cyclicCoeffOne_cyclicQuotientMap_mapDomainRingEquiv, ← groupAlgebraTrace_apply]

/-- The identity coefficient of the `q`-th coordinate of `x : Λ[G]` in the coset basis
`basisCosets Λ K.subtype K.subtype_injective` is `x.coeff q.out⁻¹`. -/
theorem coeff_one_basisCosets_repr (K : Subgroup G) (x : MonoidAlgebra Λ G)
    (q : G ⧸ K.subtype.range) :
    letI := (mapDomainRingHom Λ K.subtype).toModule
    ((TauCeti.MonoidAlgebra.basisCosets Λ K.subtype K.subtype_injective).repr x q).coeff 1 =
      x.coeff q.out⁻¹ := by
  classical
  let : Module (MonoidAlgebra Λ K) (MonoidAlgebra Λ G) :=
    (mapDomainRingHom Λ K.subtype).toModule
  let b := TauCeti.MonoidAlgebra.basisCosets Λ K.subtype K.subtype_injective
  have hsum : x = (b.repr x).sum fun q' c ↦
      mapDomainRingHom Λ K.subtype c * MonoidAlgebra.single q'.out⁻¹ 1 := by
    conv_lhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun q' _ ↦ ?_
    rw [TauCeti.MonoidAlgebra.basisCosets_apply]
    rfl
  conv_rhs => rw [hsum]
  rw [Finsupp.sum, coeff_sum]
  change _ = Finsupp.applyAddHom q.out⁻¹ (∑ i ∈ (b.repr x).support, _)
  rw [map_sum]
  simp only [Finsupp.applyAddHom_apply]
  rw [Finset.sum_eq_single q]
  · simp only [mapDomainRingHom_apply]
    have hmul : ∀ c : MonoidAlgebra Λ K,
        (mapDomain K.subtype c * MonoidAlgebra.single q.out⁻¹ (1 : Λ)).coeff q.out⁻¹ =
          c.coeff 1 := by
      intro c
      induction c using induction_linear with
      | zero => simp
      | add c₁ c₂ h₁ h₂ =>
        rw [mapDomain_add, add_mul, coeff_add, coeff_add, Finsupp.add_apply, Finsupp.add_apply,
          h₁, h₂]
      | single k a =>
        rw [mapDomain_single, single_mul_single, mul_one, coeff_single, coeff_single]
        have hk : (k : G) * q.out⁻¹ = q.out⁻¹ ↔ k = 1 := by
          constructor
          · intro h
            exact Subtype.ext (mul_eq_right.mp h)
          · rintro rfl
            simp
        by_cases hk1 : k = 1
        · simp [hk1]
        · have hk' : (k : G) * q.out⁻¹ ≠ q.out⁻¹ := mt hk.mp hk1
          simp [Finsupp.single_eq_of_ne (Ne.symm hk'), Finsupp.single_eq_of_ne (Ne.symm hk1)]
    exact (hmul _).symm
  · intro q' _ hq'
    simp only [mapDomainRingHom_apply]
    have hzero : ∀ c : MonoidAlgebra Λ K,
        (mapDomain K.subtype c * MonoidAlgebra.single q'.out⁻¹ (1 : Λ)).coeff q.out⁻¹ = 0 := by
      intro c
      induction c using induction_linear with
      | zero => simp
      | add c₁ c₂ h₁ h₂ =>
        rw [mapDomain_add, add_mul, coeff_add, Finsupp.add_apply, h₁, h₂, add_zero]
      | single k a =>
        rw [mapDomain_single, single_mul_single, mul_one, coeff_single]
        refine Finsupp.single_eq_of_ne ?_
        intro h
        apply hq'
        have h' : q.out⁻¹ = (k : G) * q'.out⁻¹ := h
        have hmem : q'.out⁻¹ * q.out ∈ K.subtype.range := by
          have : (k : G)⁻¹ = q'.out⁻¹ * q.out := by
            calc (k : G)⁻¹ = (k : G)⁻¹ * ((k : G) * q'.out⁻¹) * q.out := by
                  rw [← h', mul_assoc, inv_mul_cancel, mul_one]
              _ = q'.out⁻¹ * q.out := by simp
          exact ⟨k⁻¹, by simpa using this⟩
        have hrel : QuotientGroup.mk (s := K.subtype.range) q'.out =
            QuotientGroup.mk (s := K.subtype.range) q.out := by
          rw [QuotientGroup.eq]
          exact hmem
        simpa [Quotient.out_eq] using hrel
    exact hzero _
  · intro hq
    simp [Finsupp.notMem_support_iff.mp hq]

/-- **Subgroup restriction multiplies the group-ring trace by the index.** For a finite-index
subgroup `K ≤ G` and a `Λ[G]`-linear endomorphism `f` of a finite projective `Λ[G]`-module `P`,
restricting scalars to `Λ[K]` multiplies `Tr^G` by `[G : K]`. -/
theorem groupAlgebraTrace_restrictSubgroup (K : Subgroup G) [K.FiniteIndex]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    [Module (MonoidAlgebra Λ K) P]
    (hact : ∀ (r : MonoidAlgebra Λ K) (x : P), r • x = mapDomainRingHom Λ K.subtype r • x)
    (f : Module.End (MonoidAlgebra Λ G) P) (fK : Module.End (MonoidAlgebra Λ K) P)
    (hf : ∀ x, fK x = f x) :
    haveI := (K.restrict_finite_projective (Λ := Λ) P hact).1
    haveI := (K.restrict_finite_projective (Λ := Λ) P hact).2
    groupAlgebraTrace Λ K P fK = K.index • groupAlgebraTrace Λ G P f := by
  classical
  have := (K.restrict_finite_projective (Λ := Λ) P hact).1
  have := (K.restrict_finite_projective (Λ := Λ) P hact).2
  let : Module (MonoidAlgebra Λ K) (MonoidAlgebra Λ G) :=
    (mapDomainRingHom Λ K.subtype).toModule
  have : IsScalarTower (MonoidAlgebra Λ K) (MonoidAlgebra Λ G) (MonoidAlgebra Λ G) :=
    ⟨fun r s t ↦ mul_assoc (mapDomainRingHom Λ K.subtype r) s t⟩
  have : IsScalarTower (MonoidAlgebra Λ K) (MonoidAlgebra Λ G) P :=
    ⟨fun r s x ↦ by rw [hact r (s • x), ← mul_smul]; rfl⟩
  obtain ⟨n, r, i, -, -, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  let bK := TauCeti.MonoidAlgebra.basisCosets Λ K.subtype K.subtype_injective
  have : Fintype (G ⧸ K.subtype.range) := by
    have : Finite (G ⧸ K.subtype.range) := by rw [Subgroup.range_subtype]; infer_instance
    exact Fintype.ofFinite _
  let ePi : (Fin n → MonoidAlgebra Λ G) ≃ₗ[MonoidAlgebra Λ K]
      (Fin n × (G ⧸ K.subtype.range) →₀ MonoidAlgebra Λ K) :=
    { toFun := fun v ↦ Finsupp.equivFunOnFinite.symm fun p ↦ bK.repr (v p.1) p.2
      invFun := fun w k ↦ bK.repr.symm (Finsupp.equivFunOnFinite.symm fun q ↦ w (k, q))
      left_inv := fun v ↦ funext fun k ↦ by
        apply bK.repr.injective
        ext q
        simp
      right_inv := fun w ↦ by
        ext ⟨k, q⟩
        simp
      map_add' := fun u v ↦ by
        ext ⟨k, q⟩
        simp
      map_smul' := fun c v ↦ by
        ext ⟨k, q⟩
        simp }
  let bPi : Basis (Fin n × (G ⧸ K.subtype.range)) (MonoidAlgebra Λ K)
      (Fin n → MonoidAlgebra Λ G) :=
    Basis.ofRepr ePi
  let iK : P →ₗ[MonoidAlgebra Λ K] (Fin n → MonoidAlgebra Λ G) :=
    { toFun := i
      map_add' := i.map_add
      map_smul' := fun c x ↦ by
        ext k
        simp only [RingHom.id_apply, hact, i.map_smul, Pi.smul_apply]
        rfl }
  let rK : (Fin n → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ K] P :=
    { toFun := r
      map_add' := r.map_add
      map_smul' := fun c v ↦ by
        have hv : c • v = mapDomainRingHom Λ K.subtype c • v := rfl
        rw [hv, r.map_smul, RingHom.id_apply, hact] }
  have hrK : rK ∘ₗ iK = .id := LinearMap.ext fun x ↦
    congrArg (fun g : Module.End (MonoidAlgebra Λ G) P ↦ g x) hr
  rw [groupAlgebraTrace_eq_of_retract bPi iK rK hrK fK,
    groupAlgebraTrace_eq_of_retract (Pi.basisFun (MonoidAlgebra Λ G) (Fin n)) i r hr f]
  have hbPi : ∀ p : Fin n × (G ⧸ K.subtype.range),
      bPi p = Pi.single p.1 (MonoidAlgebra.single p.2.out⁻¹ (1 : Λ)) := by
    intro ⟨k, q⟩
    funext j
    apply bK.repr.injective
    apply Finsupp.ext
    intro q'
    have hval : ePi (bPi (k, q)) = Finsupp.single (k, q) (1 : MonoidAlgebra Λ K) :=
      Basis.repr_self bPi (k, q)
    have h1 := DFunLike.congr_fun hval (j, q')
    change bK.repr (bPi (k, q) j) q' = Finsupp.single (k, q) (1 : MonoidAlgebra Λ K) (j, q') at h1
    rw [h1, Finsupp.single_apply]
    by_cases hjk : j = k
    · subst hjk
      simp only [Pi.single_eq_same, Prod.mk.injEq, true_and]
      have hbq : MonoidAlgebra.single q.out⁻¹ (1 : Λ) = bK q :=
        (TauCeti.MonoidAlgebra.basisCosets_apply Λ K.subtype K.subtype_injective q).symm
      rw [hbq, bK.repr_self, Finsupp.single_apply]
    · simp [Ne.symm hjk]
  have hterm : ∀ (k : Fin n) (q : G ⧸ K.subtype.range),
      (bPi.repr (iK (fK (rK (bPi (k, q))))) (k, q)).coeff 1 =
        (i (f (r (Pi.single k 1))) k).coeff 1 := by
    intro k q
    rw [hbPi (k, q)]
    have hpi : (Pi.single k (MonoidAlgebra.single q.out⁻¹ (1 : Λ)) : Fin n → MonoidAlgebra Λ G) =
        MonoidAlgebra.single q.out⁻¹ (1 : Λ) • Pi.single k (1 : MonoidAlgebra Λ G) := by
      ext j
      by_cases hjk : j = k <;> simp [hjk]
    change (bK.repr (i (fK (r (Pi.single k (MonoidAlgebra.single q.out⁻¹ 1)))) k) q).coeff 1 = _
    rw [hf, hpi, r.map_smul, f.map_smul, i.map_smul, Pi.smul_apply, smul_eq_mul,
      coeff_one_basisCosets_repr]
    simp
  rw [Fintype.sum_prod_type]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← nsmul_eq_mul, map_nsmul]
  have hcard : Fintype.card (G ⧸ K.subtype.range) = K.index := by
    rw [← Nat.card_eq_fintype_card, Subgroup.range_subtype, ← Subgroup.index_eq_card]
  rw [hcard]
  simp only [Pi.basisFun_repr, Pi.basisFun_apply]

/-- **Stacks Lemma 64.15.1 / 64.15.2.** For a finite group `G` and a `Λ[G]`-linear endomorphism
`f` of a finitely generated projective `Λ[G]`-module `P`, the `Λ`-trace is `|G|` times the
group-ring trace `Tr^G(f, P)`, with no commutativity hypothesis on `Λ` and no division by `|G|`. -/
theorem hattoriStallingsTrace_restrictScalars_eq_card_nsmul_groupAlgebraTrace [Finite G]
    [Module Λ P] [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    (f : Module.End (MonoidAlgebra Λ G) P) :
    haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := Λ) (G := G) P).1
    haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := Λ) (G := G) P).2
    hattoriStallingsTrace Λ P (f.restrictScalars Λ) =
      Nat.card G • groupAlgebraTrace Λ G P f := by
  classical
  have := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := Λ) (G := G) P).1
  have := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := Λ) (G := G) P).2
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, r, i, -, -, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  let ePi : (Fin n → MonoidAlgebra Λ G) ≃ₗ[Λ] (Fin n × G →₀ Λ) :=
    { toFun := fun v ↦ Finsupp.equivFunOnFinite.symm fun p ↦ (v p.1).coeff p.2
      invFun := fun w k ↦ MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g ↦ w (k, g))
      left_inv := fun v ↦ funext fun k ↦ MonoidAlgebra.ext (Finsupp.ext fun g ↦ by simp)
      right_inv := fun w ↦ by ext ⟨k, g⟩; simp
      map_add' := fun u v ↦ by ext ⟨k, g⟩; simp
      map_smul' := fun a v ↦ by ext ⟨k, g⟩; simp }
  let bPi : Basis (Fin n × G) Λ (Fin n → MonoidAlgebra Λ G) := Basis.ofRepr ePi
  have hbPi : ∀ p : Fin n × G, bPi p = Pi.single p.1 (MonoidAlgebra.single p.2 (1 : Λ)) := by
    intro ⟨k, g⟩
    funext j
    refine MonoidAlgebra.ext (Finsupp.ext fun g' ↦ ?_)
    have hval : ePi (bPi (k, g)) = Finsupp.single (k, g) (1 : Λ) := Basis.repr_self bPi (k, g)
    have h1 := DFunLike.congr_fun hval (j, g')
    change (bPi (k, g) j).coeff g' = Finsupp.single (k, g) (1 : Λ) (j, g') at h1
    rw [h1, Finsupp.single_apply]
    by_cases hjk : j = k
    · subst hjk
      simp only [Pi.single_eq_same, coeff_single, Prod.mk.injEq, true_and]
      by_cases hgg' : g = g'
      · simp [hgg']
      · simp [Finsupp.single_eq_of_ne (Ne.symm hgg'), hgg']
    · simp [Ne.symm hjk]
  have hrΛ : r.restrictScalars Λ ∘ₗ i.restrictScalars Λ = .id :=
    LinearMap.ext fun x ↦ congrArg (fun g : Module.End (MonoidAlgebra Λ G) P ↦ g x) hr
  rw [hattoriStallingsTrace_eq_of_retract bPi (i.restrictScalars Λ) (r.restrictScalars Λ) hrΛ,
    Basis.hattoriStallingsTrace_apply,
    groupAlgebraTrace_eq_of_retract (Pi.basisFun (MonoidAlgebra Λ G) (Fin n)) i r hr f,
    Fintype.sum_prod_type]
  have hterm : ∀ (k : Fin n) (g : G),
      bPi.repr ((i.restrictScalars Λ) ((f.restrictScalars Λ) ((r.restrictScalars Λ) (bPi (k, g)))))
        (k, g) = (i (f (r (Pi.single k (1 : MonoidAlgebra Λ G)))) k).coeff 1 := by
    intro k g
    rw [hbPi (k, g)]
    have hpi : (Pi.single k (MonoidAlgebra.single g (1 : Λ)) : Fin n → MonoidAlgebra Λ G) =
        MonoidAlgebra.single g (1 : Λ) • Pi.single k (1 : MonoidAlgebra Λ G) := by
      ext j
      by_cases hjk : j = k <;> simp [hjk]
    change (i (f (r (Pi.single k (MonoidAlgebra.single g 1)))) k).coeff g = _
    rw [hpi, r.map_smul, f.map_smul, i.map_smul, Pi.smul_apply, smul_eq_mul]
    simp
  simp only [LinearMap.comp_apply, hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← nsmul_eq_mul, map_nsmul, Nat.card_eq_fintype_card]
  simp only [Pi.basisFun_repr, Pi.basisFun_apply]

end GroupAlgebraTrace

section CommutativeScalarTrace

variable {A : Type*} [CommRing A] {G H : Type*} [Group G] [Group H]
variable {P Q : Type*} [AddCommGroup P] [Module (MonoidAlgebra A G) P]
variable [AddCommGroup Q] [Module (MonoidAlgebra A G) Q]

variable (A G P) in
/-- Over a commutative ring `A`, the group-ring trace `Tr^G` takes scalar values in `A`. -/
def groupAlgebraScalarTrace [Module.Finite (MonoidAlgebra A G) P]
    [Module.Projective (MonoidAlgebra A G) P] :
    Module.End (MonoidAlgebra A G) P →+ A :=
  (TauCeti.cyclicQuotientEquivSelf A).toAddMonoidHom.comp (groupAlgebraTrace A G P)

theorem groupAlgebraScalarTrace_apply [Module.Finite (MonoidAlgebra A G) P]
    [Module.Projective (MonoidAlgebra A G) P] (f : Module.End (MonoidAlgebra A G) P) :
    groupAlgebraScalarTrace A G P f =
      TauCeti.cyclicQuotientEquivSelf A (groupAlgebraTrace A G P f) :=
  (rfl)

theorem mkQ_groupAlgebraScalarTrace [Module.Finite (MonoidAlgebra A G) P]
    [Module.Projective (MonoidAlgebra A G) P] (f : Module.End (MonoidAlgebra A G) P) :
    (TauCeti.commutatorSubmodule ℤ A).mkQ (groupAlgebraScalarTrace A G P f) =
      groupAlgebraTrace A G P f :=
  (TauCeti.cyclicQuotientEquivSelf A).symm_apply_apply _

/-- Compute `groupAlgebraScalarTrace` in any finite free `A[G]`-retract. -/
theorem groupAlgebraScalarTrace_eq_of_retract [Module.Finite (MonoidAlgebra A G) P]
    [Module.Projective (MonoidAlgebra A G) P] {F : Type*} [AddCommGroup F]
    [Module (MonoidAlgebra A G) F] {ι : Type*} [Fintype ι]
    (b : Basis ι (MonoidAlgebra A G) F) (i : P →ₗ[MonoidAlgebra A G] F)
    (r : F →ₗ[MonoidAlgebra A G] P) (hr : r ∘ₗ i = .id)
    (f : Module.End (MonoidAlgebra A G) P) :
    groupAlgebraScalarTrace A G P f = ∑ k : ι, (b.repr (i (f (r (b k)))) k).coeff 1 := by
  rw [groupAlgebraScalarTrace_apply, groupAlgebraTrace_eq_of_retract b i r hr f,
    TauCeti.cyclicQuotientEquivSelf_mkQ]

/-- On `A[G]` itself, `groupAlgebraScalarTrace f = (f 1).coeff 1`. -/
@[simp]
theorem groupAlgebraScalarTrace_self_apply
    (f : Module.End (MonoidAlgebra A G) (MonoidAlgebra A G)) :
    groupAlgebraScalarTrace A G (MonoidAlgebra A G) f = (f 1).coeff 1 := by
  rw [groupAlgebraScalarTrace_apply, groupAlgebraTrace_self_apply,
    TauCeti.cyclicQuotientEquivSelf_mkQ]

/-- Over a commutative ring `A`, `Tr_A(f, P) = |G| * Tr_A^G(f, P)`. -/
theorem projectiveTrace_restrictScalars_eq_card_mul_groupAlgebraScalarTrace [Finite G]
    [Module A P] [IsScalarTower A (MonoidAlgebra A G) P]
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (f : Module.End (MonoidAlgebra A G) P) :
    haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := A) (G := G) P).1
    haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := A) (G := G) P).2
    projectiveTrace A P (f.restrictScalars A) =
      (Nat.card G : A) * groupAlgebraScalarTrace A G P f := by
  have := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := A) (G := G) P).1
  have := (MonoidAlgebra.finite_projective_of_monoidAlgebra (Λ := A) (G := G) P).2
  rw [← cyclicQuotientEquivSelf_hattoriStallingsTrace,
    hattoriStallingsTrace_restrictScalars_eq_card_nsmul_groupAlgebraTrace, map_nsmul,
    nsmul_eq_mul, groupAlgebraScalarTrace_apply]

/-- Over a commutative ring `A`, `groupAlgebraScalarTrace` is invariant under conjugation along a
group isomorphism `e : G ≃* H`. -/
theorem groupAlgebraScalarTrace_conj_equiv {Q' : Type*} [AddCommGroup Q']
    [Module (MonoidAlgebra A H) Q'] [Module.Finite (MonoidAlgebra A G) P]
    [Module.Projective (MonoidAlgebra A G) P] [Module.Finite (MonoidAlgebra A H) Q']
    [Module.Projective (MonoidAlgebra A H) Q'] (e : G ≃* H) (eP : P ≃+ Q')
    (heP : ∀ (r : MonoidAlgebra A G) (x : P),
      eP (r • x) = mapDomainRingHom A e.toMonoidHom r • eP x)
    (f : Module.End (MonoidAlgebra A G) P) (f' : Module.End (MonoidAlgebra A H) Q')
    (hf : ∀ x, f' (eP x) = eP (f x)) :
    groupAlgebraScalarTrace A H Q' f' = groupAlgebraScalarTrace A G P f := by
  rw [groupAlgebraScalarTrace_apply, groupAlgebraScalarTrace_apply,
    groupAlgebraTrace_conj_equiv e eP heP f f' hf]

end CommutativeScalarTrace

end LinearMap

namespace MonoidAlgebra

section Coinvariants

variable (Λ G P : Type*) [Ring Λ] [Monoid G] [AddCommGroup P] [Module Λ P]
  [Module (MonoidAlgebra Λ G) P]

/-- The `Λ`-submodule of a left `Λ[G]`-module `P` generated by all differences
`single g 1 • p - p`. Works over an arbitrary (possibly noncommutative) ring `Λ`. -/
def coinvariantsSubmodule : Submodule Λ P :=
  Submodule.span Λ (Set.range fun gp : G × P ↦ single gp.1 (1 : Λ) • gp.2 - gp.2)

/-- The coinvariants `P_G = P / ⟨single g 1 • p - p⟩` of a left `Λ[G]`-module over an arbitrary
ring `Λ`. -/
abbrev Coinvariants := P ⧸ coinvariantsSubmodule Λ G P

namespace Coinvariants

variable {Λ G P}

/-- The canonical quotient projection `P →ₗ[Λ] P_G`. -/
def mk : P →ₗ[Λ] Coinvariants Λ G P :=
  (coinvariantsSubmodule Λ G P).mkQ

theorem mk_surjective : Function.Surjective (mk (Λ := Λ) (G := G) (P := P)) :=
  Submodule.Quotient.mk_surjective _

theorem sub_mem_coinvariantsSubmodule (g : G) (p : P) :
    single g (1 : Λ) • p - p ∈ coinvariantsSubmodule Λ G P :=
  Submodule.subset_span ⟨(g, p), rfl⟩

@[simp]
theorem mk_single_smul (g : G) (p : P) :
    mk (Λ := Λ) (G := G) (single g (1 : Λ) • p) = mk (Λ := Λ) (G := G) p :=
  (Submodule.Quotient.eq _).mpr (sub_mem_coinvariantsSubmodule g p)

@[simp]
theorem mk_single_smul_eq [IsScalarTower Λ (MonoidAlgebra Λ G) P] (g : G) (a : Λ) (p : P) :
    mk (Λ := Λ) (G := G) (single g a • p) = a • mk (Λ := Λ) (G := G) p := by
  have h : single g a = a • single g (1 : Λ) := by simp
  rw [h, smul_assoc, map_smul, mk_single_smul]

/-- Universal property of coinvariants: a `Λ`-linear map killing `single g 1 • p - p` descends to
`P_G`. -/
def lift {W : Type*} [AddCommGroup W] [Module Λ W] (f : P →ₗ[Λ] W)
    (hf : ∀ (g : G) (p : P), f (single g (1 : Λ) • p) = f p) :
    Coinvariants Λ G P →ₗ[Λ] W :=
  Submodule.liftQ (coinvariantsSubmodule Λ G P) f <| by
    rw [coinvariantsSubmodule, Submodule.span_le]
    rintro _ ⟨⟨g, p⟩, rfl⟩
    simp [hf g p]

@[simp]
theorem lift_mk {W : Type*} [AddCommGroup W] [Module Λ W] (f : P →ₗ[Λ] W)
    (hf : ∀ (g : G) (p : P), f (single g (1 : Λ) • p) = f p) (p : P) :
    lift f hf (mk (Λ := Λ) (G := G) p) = f p :=
  (rfl)

@[ext high]
theorem hom_ext {W : Type*} [AddCommGroup W] [Module Λ W]
    {f g : Coinvariants Λ G P →ₗ[Λ] W}
    (h : f.comp (mk (Λ := Λ) (G := G)) = g.comp (mk (Λ := Λ) (G := G))) : f = g :=
  Submodule.linearMap_qext _ h

/-- Any `Λ`-linear map `f : P →ₗ[Λ] Q` that intertwines the `G`-action via a map `α : G → G`
descends to a `Λ`-linear map on coinvariants `P_G →ₗ[Λ] Q_G`. -/
def mapOfTwisted {Q : Type*} [AddCommGroup Q] [Module Λ Q] [Module (MonoidAlgebra Λ G) Q]
    (f : P →ₗ[Λ] Q) (α : G → G)
    (hα : ∀ (g : G) (p : P), f (single g (1 : Λ) • p) = single (α g) (1 : Λ) • f p) :
    Coinvariants Λ G P →ₗ[Λ] Coinvariants Λ G Q :=
  lift ((mk (Λ := Λ) (G := G)).comp f) fun g p ↦ by
    simp [hα g p]

@[simp]
theorem mapOfTwisted_mk {Q : Type*} [AddCommGroup Q] [Module Λ Q] [Module (MonoidAlgebra Λ G) Q]
    (f : P →ₗ[Λ] Q) (α : G → G)
    (hα : ∀ (g : G) (p : P), f (single g (1 : Λ) • p) = single (α g) (1 : Λ) • f p) (p : P) :
    mapOfTwisted f α hα (mk (Λ := Λ) (G := G) p) = mk (Λ := Λ) (G := G) (f p) :=
  (rfl)

/-- Functoriality of coinvariants on `Λ[G]`-linear maps. -/
def map {Q : Type*} [AddCommGroup Q] [Module Λ Q] [Module (MonoidAlgebra Λ G) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]
    (f : P →ₗ[MonoidAlgebra Λ G] Q) :
    Coinvariants Λ G P →ₗ[Λ] Coinvariants Λ G Q :=
  mapOfTwisted (f.restrictScalars Λ) id fun g p ↦ f.map_smul (single g (1 : Λ)) p

@[simp]
theorem map_mk {Q : Type*} [AddCommGroup Q] [Module Λ Q] [Module (MonoidAlgebra Λ G) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]
    (f : P →ₗ[MonoidAlgebra Λ G] Q) (p : P) :
    map f (mk (Λ := Λ) (G := G) p) = mk (Λ := Λ) (G := G) (f p) :=
  (rfl)

@[simp]
theorem map_id [IsScalarTower Λ (MonoidAlgebra Λ G) P] :
    map (Λ := Λ) (G := G) (P := P) (LinearMap.id : P →ₗ[MonoidAlgebra Λ G] P) = LinearMap.id := by
  ext p
  rfl

@[simp]
theorem map_comp {Q R' : Type*} [AddCommGroup Q] [Module Λ Q] [Module (MonoidAlgebra Λ G) Q]
    [AddCommGroup R'] [Module Λ R'] [Module (MonoidAlgebra Λ G) R']
    [IsScalarTower Λ (MonoidAlgebra Λ G) P] [IsScalarTower Λ (MonoidAlgebra Λ G) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ G) R']
    (g : Q →ₗ[MonoidAlgebra Λ G] R') (f : P →ₗ[MonoidAlgebra Λ G] Q) :
    map (g ∘ₗ f) = (map g).comp (map f) := by
  ext p
  rfl

/-- Over a commutative ring, `MonoidAlgebra.Coinvariants` is canonically isomorphic to Mathlib's
`Representation.Coinvariants`. -/
def equivRepresentationCoinvariants {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module (MonoidAlgebra A G) M] [IsScalarTower A (MonoidAlgebra A G) M] :
    Coinvariants A G M ≃ₗ[A] (Representation.ofModule' (k := A) (G := G) M).Coinvariants :=
  Submodule.quotEquivOfEq _ _ (by
    simp only [coinvariantsSubmodule, Representation.Coinvariants.ker]
    rfl)

/-- The coinvariants of the regular left module `Λ[G]` are canonically isomorphic to `Λ` via the
augmentation map `∑ a_g g ↦ ∑ a_g`. -/
def selfEquiv (Λ G : Type*) [Ring Λ] [Monoid G] :
    Coinvariants Λ G (MonoidAlgebra Λ G) ≃ₗ[Λ] Λ :=
  LinearEquiv.ofLinearMap
    (lift (augmentationLinearMap Λ G) fun g x ↦ by
      simp [smul_eq_mul, map_mul])
    ((mk (Λ := Λ) (G := G)).comp
      ({ toFun := fun a ↦ single (1 : G) a
         map_add' := fun a b ↦ by simp [single_add]
         map_smul' := fun a b ↦ by simp [smul_single, smul_eq_mul] } : Λ →ₗ[Λ] MonoidAlgebra Λ G))
    (by
      ext
      simp)
    (by
      apply hom_ext
      apply LinearMap.ext
      intro x
      induction x using induction_linear with
      | zero => simp
      | add x y hx hy => simp [map_add, hx, hy]
      | single g a =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, lift_mk, augmentationLinearMap_apply,
          augmentation_single]
        have h1 : single g a = single g (1 : Λ) • single (1 : G) a := by
          simp [smul_eq_mul, single_mul_single]
        change mk (Λ := Λ) (G := G) (single (1 : G) a) = mk (Λ := Λ) (G := G) (single g a)
        conv_rhs => rw [h1]
        rw [mk_single_smul])

@[simp]
theorem selfEquiv_mk (x : MonoidAlgebra Λ G) :
    selfEquiv Λ G (mk (Λ := Λ) (G := G) x) = augmentation Λ G x :=
  augmentationLinearMap_apply Λ G x

@[simp]
theorem selfEquiv_symm_apply (a : Λ) :
    (selfEquiv Λ G).symm a = mk (Λ := Λ) (G := G) (single (1 : G) a) :=
  (rfl)

/-- Coinvariants commute with finite products of left `Λ[G]`-modules. -/
def piEquiv (Λ G : Type*) [Ring Λ] [Monoid G] {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ k, AddCommGroup (M k)] [∀ k, Module Λ (M k)]
    [∀ k, Module (MonoidAlgebra Λ G) (M k)] :
    Coinvariants Λ G (∀ k, M k) ≃ₗ[Λ] (∀ k, Coinvariants Λ G (M k)) := by
  classical
  refine LinearEquiv.ofLinearMap
    (lift
      { toFun := fun v k ↦ mk (Λ := Λ) (G := G) (v k)
        map_add' := fun u v ↦ funext fun k ↦ map_add _ _ _
        map_smul' := fun a v ↦ funext fun k ↦ map_smul _ _ _ }
      fun g v ↦ funext fun k ↦ mk_single_smul g (v k))
    { toFun := fun w ↦ ∑ k : ι,
        lift ((mk (Λ := Λ) (G := G)).comp (LinearMap.single Λ M k)) (fun g x ↦ by
          have h : LinearMap.single Λ M k (single g (1 : Λ) • x) =
              single g (1 : Λ) • LinearMap.single Λ M k x := by
            funext j
            by_cases hjk : j = k
            · subst hjk
              simp [Pi.single_eq_same]
            · simp [Pi.single_eq_of_ne hjk]
          change mk (Λ := Λ) (G := G) (LinearMap.single Λ M k (single g (1 : Λ) • x)) = _
          rw [h, mk_single_smul]
          rfl) (w k)
      map_add' := fun u v ↦ by simp [Finset.sum_add_distrib]
      map_smul' := fun a w ↦ by simp [Finset.smul_sum] }
    (by
      apply LinearMap.ext
      intro w
      funext j
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk,
        map_sum, Finset.sum_apply]
      rw [Finset.sum_eq_single j]
      · obtain ⟨x, hx⟩ := mk_surjective (Λ := Λ) (G := G) (w j)
        rw [← hx]
        simp
      · intro k _ hkj
        obtain ⟨x, hx⟩ := mk_surjective (Λ := Λ) (G := G) (w k)
        rw [← hx]
        simp [Pi.single_eq_of_ne (Ne.symm hkj)]
      · intro hj
        exact absurd (Finset.mem_univ j) hj)
    (by
      apply hom_ext
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, LinearMap.id_apply, lift_mk, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← map_sum]
      congr 1
      funext j
      simp [Finset.sum_apply])

@[simp]
theorem piEquiv_mk {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ k, AddCommGroup (M k)] [∀ k, Module Λ (M k)]
    [∀ k, Module (MonoidAlgebra Λ G) (M k)]
    (v : ∀ k, M k) (k : ι) :
    piEquiv Λ G M (mk (Λ := Λ) (G := G) v) k = mk (Λ := Λ) (G := G) (v k) :=
  (rfl)

/-- Coinvariants of `Fin n → Λ[G]` are canonically isomorphic to `Fin n → Λ` via entrywise
augmentation. -/
def piSelfEquiv (Λ G : Type*) [Ring Λ] [Monoid G] (n : ℕ) :
    Coinvariants Λ G (Fin n → MonoidAlgebra Λ G) ≃ₗ[Λ] (Fin n → Λ) :=
  (piEquiv Λ G (fun _ : Fin n ↦ MonoidAlgebra Λ G)).trans
    (LinearEquiv.piCongrRight fun _ ↦ selfEquiv Λ G)

@[simp]
theorem piSelfEquiv_mk {n : ℕ} (v : Fin n → MonoidAlgebra Λ G) (k : Fin n) :
    piSelfEquiv Λ G n (mk (Λ := Λ) (G := G) v) k = augmentation Λ G (v k) :=
  selfEquiv_mk (v k)

@[simp]
theorem piSelfEquiv_symm_single {n : ℕ} (k : Fin n) (a : Λ) :
    (piSelfEquiv Λ G n).symm (Pi.single k a) =
      mk (Λ := Λ) (G := G) (Pi.single k (single (1 : G) a)) := by
  apply (piSelfEquiv Λ G n).injective
  rw [LinearEquiv.apply_symm_apply]
  ext j
  by_cases hjk : j = k <;> simp [hjk]

/-- Coinvariants of a finitely generated projective `Λ[G]`-module are finitely generated and
projective over `Λ`. -/
theorem finite_projective [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P] :
    Module.Finite Λ (Coinvariants Λ G P) ∧ Module.Projective Λ (Coinvariants Λ G P) := by
  obtain ⟨n, r, i, -, -, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  let iG : Coinvariants Λ G P →ₗ[Λ] (Fin n → Λ) :=
    (piSelfEquiv Λ G n).toLinearMap ∘ₗ map i
  let rG : (Fin n → Λ) →ₗ[Λ] Coinvariants Λ G P :=
    map r ∘ₗ (piSelfEquiv Λ G n).symm.toLinearMap
  have hrG : rG ∘ₗ iG = .id := by
    ext p
    simp only [LinearMap.comp_apply, LinearMap.id_apply, iG, rG, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, map_mk]
    have hp : r (i p) = p := congrArg (fun g : Module.End (MonoidAlgebra Λ G) P ↦ g p) hr
    rw [hp]
  have hsurj : Function.Surjective rG :=
    Function.RightInverse.surjective fun x ↦ congrArg (fun g : Module.End Λ _ ↦ g x) hrG
  exact ⟨Module.Finite.of_surjective rG hsurj, Module.Projective.of_split iG rG hrG⟩

/-- **Stacks Lemma 64.15.2 (coinvariant trace via augmentation).** For a `Λ[G]`-linear
endomorphism `f` of a finite projective `Λ[G]`-module `P`, the Hattori–Stallings trace of the
induced map on `P_G` is the image of `Tr_{Λ[G]}(f, P)` under the augmentation map. -/
theorem hattoriStallingsTrace_map [IsScalarTower Λ (MonoidAlgebra Λ G) P]
    [Module.Finite (MonoidAlgebra Λ G) P] [Module.Projective (MonoidAlgebra Λ G) P]
    (f : Module.End (MonoidAlgebra Λ G) P) :
    haveI := (finite_projective (Λ := Λ) (G := G) (P := P)).1
    haveI := (finite_projective (Λ := Λ) (G := G) (P := P)).2
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G P) (map f) =
      TauCeti.cyclicQuotientMap (augmentation Λ G)
        (LinearMap.hattoriStallingsTrace (MonoidAlgebra Λ G) P f) := by
  classical
  have := (finite_projective (Λ := Λ) (G := G) (P := P)).1
  have := (finite_projective (Λ := Λ) (G := G) (P := P)).2
  obtain ⟨n, r, i, -, -, hr⟩ := Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ G) P
  let iG : Coinvariants Λ G P →ₗ[Λ] (Fin n → Λ) :=
    (piSelfEquiv Λ G n).toLinearMap ∘ₗ map i
  let rG : (Fin n → Λ) →ₗ[Λ] Coinvariants Λ G P :=
    map r ∘ₗ (piSelfEquiv Λ G n).symm.toLinearMap
  have hrG : rG ∘ₗ iG = .id := by
    ext p
    simp only [LinearMap.comp_apply, LinearMap.id_apply, iG, rG, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, map_mk]
    have hp : r (i p) = p := congrArg (fun g : Module.End (MonoidAlgebra Λ G) P ↦ g p) hr
    rw [hp]
  rw [LinearMap.hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin n)) iG rG hrG,
    LinearMap.hattoriStallingsTrace_eq_of_retract (Pi.basisFun (MonoidAlgebra Λ G) (Fin n)) i r hr,
    Basis.hattoriStallingsTrace_apply, Basis.hattoriStallingsTrace_apply,
    TauCeti.cyclicQuotientMap_mkQ]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Pi.basisFun_repr, Pi.basisFun_apply, LinearMap.comp_apply, iG, rG,
    LinearEquiv.coe_coe, piSelfEquiv_symm_single, map_mk, piSelfEquiv_mk]
  rfl

end Coinvariants

end Coinvariants

end MonoidAlgebra
