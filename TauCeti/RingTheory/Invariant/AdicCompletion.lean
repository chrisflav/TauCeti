/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import TauCeti.RingTheory.AdicCompletion.AtPrime
public import TauCeti.RingTheory.AdicCompletion.ChineseRemainder
public import TauCeti.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RingTheory.Ideal.Pointwise

/-!
# Adic completions of invariant rings at maximal ideals

Let a finite group `G` act on a commutative `k`-algebra `B` with Noetherian invariant subalgebra
`A` such that `B` is finite as an `A`-module, and let `Q` be a maximal ideal of `B` contracting to
`P = Q ∩ A`. Even when `G` has order divisible by the residue characteristic of `Q` or acts with
nontrivial inertia at `Q`, the formal neighbourhood of `P` in `Spec A` depends only on the
decomposition group `MulAction.stabilizer G Q` and its action on `AdicCompletion Q B`:

1. Flatness of `AdicCompletion P A` over `A` (`AdicCompletion.flat_of_isNoetherian`) together with
   finite-group invariant base change (`Representation.invariantsBaseChangeEquiv`) identifies
   `AdicCompletion P A` with the `G`-fixed subalgebra of
   `AdicCompletion P A ⊗[A] B ≃ₐ[A] AdicCompletion (P.map (algebraMap A B)) B`.
2. The radical of `P.map (algebraMap A B)` is the intersection of the `G`-orbit of `Q`, a finite
   family of pairwise coprime maximal ideals of `B`, so the Chinese remainder theorem for adic
   completions (`AdicCompletion.equivPiOfRadicalEqIInf`) decomposes
   `AdicCompletion (P.map (algebraMap A B)) B` into `∀ R : MulAction.orbit G Q, AdicCompletion R B`.
3. By Shapiro's lemma on the transitive `G`-set `MulAction.orbit G Q`, projecting to the `Q`-factor
   identifies the `G`-fixed tuples with the `MulAction.stabilizer G Q`-fixed points of
   `AdicCompletion Q B`.

Applying this both to `(A, G)` and to `(C, H)` for any subgroup `H` containing
`MulAction.stabilizer G Q` and any intermediate `H`-invariant ring `C` shows that the canonical map
`AdicCompletion (Q.under A) A →ₐ[k] AdicCompletion (Q.under C) C` is an isomorphism; in particular
`Localization.AtPrime (Q.under A)` and `Localization.AtPrime (Q.under C)` have the same Krull
dimension and each is a regular local ring if and only if the other is.

## Main definitions and results

* `AdicCompletion.instMulSemiringActionStabilizer`, `AdicCompletion.instSMulCommClassStabilizer`:
  the stabilizer `MulAction.stabilizer G J` of an ideal `J` acts on `AdicCompletion J B` by
  `R`-algebra automorphisms.
* `AdicCompletion.ofTensorProduct_bijective_of_finite`: universe-polymorphic bijectivity of
  `AdicCompletion I A ⊗[A] M →ₗ[AdicCompletion I A] AdicCompletion I M` for finite modules over a
  Noetherian ring.
* `AdicCompletion.tensorAlgebraEquivMap`: for a finite `A`-algebra `B` over a Noetherian ring `A`,
  the canonical `A`-algebra isomorphism
  `AdicCompletion I A ⊗[A] B ≃ₐ[A] AdicCompletion (I.map (algebraMap A B)) B`.
* `AdicCompletion.stabilizerFixedPointsEquiv`: the canonical `k`-algebra isomorphism
  `AdicCompletion (Q.under A) A ≃ₐ[k] FixedPoints.subalgebra k (AdicCompletion Q B)
  (MulAction.stabilizer G Q)`.
* `AdicCompletion.underInvariantsEquivOfStabilizerLE`: for `MulAction.stabilizer G Q ≤ H` and an
  intermediate `H`-invariant ring `C`, the canonical `k`-algebra isomorphism
  `AdicCompletion (Q.under A) A ≃ₐ[k] AdicCompletion (Q.under C) C`.
* `TauCeti.AdicCompletion.ringKrullDim_atPrime_under_eq_of_stabilizer_le`,
  `TauCeti.AdicCompletion.isRegularLocalRing_atPrime_under_iff_of_stabilizer_le`: comparison of
  Krull dimension and regularity of the localizations at `Q.under A` and `Q.under C`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Chapter V, § 5, Exercise 8.
* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Chapter 7.
* M. Demazure, A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, § 2.
-/

public section

open scoped Pointwise
open Function TensorProduct

namespace AdicCompletion

section StabilizerAction

variable {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B]

/-- Pushing an ideal forward along `MulSemiringAction.toAlgEquiv R B g` gives `g • J`. -/
theorem map_toAlgEquiv_eq_smul (R : Type*) [CommRing R] [Algebra R B] [SMulCommClass G R B]
    (g : G) (J : Ideal B) :
    J.map (MulSemiringAction.toAlgEquiv R B g) = g • J := by
  rw [Ideal.pointwise_smul_def, Ideal.map, Ideal.map]
  rfl

/-- The action of `MulAction.stabilizer G J` on `AdicCompletion J B` by ring automorphisms. -/
noncomputable def stabilizerRingAut (G : Type*) [Group G] [MulSemiringAction G B] (J : Ideal B) :
    MulAction.stabilizer G J →* RingAut (AdicCompletion J B) where
  toFun h := (congrₐ (MulSemiringAction.toAlgEquiv ℤ B (h : G))
    ((map_toAlgEquiv_eq_smul ℤ (h : G) J).trans (MulAction.mem_stabilizer_iff.mp h.2))).toRingEquiv
  map_one' := RingEquiv.toRingHom_injective <| RingHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
    simp [← hb]
  map_mul' h₁ h₂ := RingEquiv.toRingHom_injective <| RingHom.ext fun x ↦ ext_evalₐ fun n ↦ by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
    simp [← hb, mul_smul]

/-- The stabilizer of an ideal `J` acts on the completion `AdicCompletion J B` by ring
automorphisms. -/
noncomputable instance instMulSemiringActionStabilizer (J : Ideal B) :
    MulSemiringAction (MulAction.stabilizer G J) (AdicCompletion J B) :=
  MulSemiringAction.compHom (AdicCompletion J B) (stabilizerRingAut G J)

/-- As an `R`-algebra equivalence, the action of `h : MulAction.stabilizer G J` on
`AdicCompletion J B` is `congrₐ` of `MulSemiringAction.toAlgEquiv R B (h : G)`. -/
theorem smul_stabilizer_eq_congrₐ (R : Type*) [CommRing R] [Algebra R B] [SMulCommClass G R B]
    {J : Ideal B} (h : MulAction.stabilizer G J) (x : AdicCompletion J B) :
    h • x = congrₐ (MulSemiringAction.toAlgEquiv R B (h : G))
      ((map_toAlgEquiv_eq_smul R (h : G) J).trans (MulAction.mem_stabilizer_iff.mp h.2)) x :=
  ext_evalₐ fun n ↦ by
    change evalₐ J n (congrₐ (MulSemiringAction.toAlgEquiv ℤ B (h : G)) _ x) = _
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
    simp [← hb]

/-- The stabilizer action on `AdicCompletion J B` extends the action on `B`. -/
@[simp]
theorem smul_of_stabilizer {J : Ideal B} (h : MulAction.stabilizer G J) (b : B) :
    h • of J B b = of J B ((h : G) • b) := by
  rw [smul_stabilizer_eq_congrₐ ℤ h, congrₐ_of]
  rfl

/-- If `G` acts `R`-linearly on `B`, then `MulAction.stabilizer G J` acts `R`-linearly on
`AdicCompletion J B`. -/
instance instSMulCommClassStabilizer (R : Type*) [CommRing R] [Algebra R B] [SMulCommClass G R B]
    (J : Ideal B) :
    SMulCommClass (MulAction.stabilizer G J) R (AdicCompletion J B) where
  smul_comm h r x := by
    rw [smul_stabilizer_eq_congrₐ R h, map_smul, smul_stabilizer_eq_congrₐ R h]

end StabilizerAction

section TensorAlgebra

variable {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- Universe-polymorphic form of
`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`: over a Noetherian ring `A`,
`ofTensorProduct I M` is bijective for any finite `A`-module `M` in any universe. -/
theorem ofTensorProduct_bijective_of_finite (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    Function.Bijective (ofTensorProduct I M) := by
  -- Present `M` as a quotient `(Fin n → A) ⧸ ker p`, which lives in `A`'s universe.
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A M
  let M₀ := (Fin n → A) ⧸ LinearMap.ker p
  let e : M₀ ≃ₗ[A] M := p.quotKerEquivOfSurjective hp
  have : Module.Finite A M₀ := Module.Finite.equiv e.symm
  let eTens : AdicCompletion I A ⊗[A] M₀ ≃ₗ[AdicCompletion I A] AdicCompletion I A ⊗[A] M :=
    AlgebraTensorModule.congr (LinearEquiv.refl (AdicCompletion I A) _) e
  have hnat := LinearMap.congr_fun (ofTensorProduct_naturality I e.toLinearMap)
  have he_map : Function.Bijective (map I e.toLinearMap) :=
    ⟨fun x y hxy ↦ by
        have := congrArg (map I e.symm.toLinearMap) hxy
        simpa [map_comp_apply] using this,
      fun y ↦ ⟨map I e.symm.toLinearMap y, by simp [map_comp_apply]⟩⟩
  have hfac : (ofTensorProduct I M : AdicCompletion I A ⊗[A] M → AdicCompletion I M) =
      map I e.toLinearMap ∘ ofTensorProduct I M₀ ∘ eTens.symm := funext fun z ↦ by
    have hz := hnat (eTens.symm z)
    change map I e.toLinearMap (ofTensorProduct I M₀ (eTens.symm z)) =
      ofTensorProduct I M (eTens (eTens.symm z)) at hz
    rw [eTens.apply_symm_apply] at hz
    exact hz.symm
  rw [hfac]
  exact he_map.comp
    ((ofTensorProduct_bijective_of_finite_of_isNoetherian I M₀).comp eTens.symm.bijective)

/-- For a finite `A`-algebra `B` over a Noetherian ring `A`, the canonical `A`-algebra map
`AdicCompletion I A ⊗[A] B →ₐ[A] AdicCompletion (I.map (algebraMap A B)) B` is an isomorphism. -/
noncomputable def tensorAlgebraEquivMap (B : Type*) [CommRing B] [Algebra A B]
    [Module.Finite A B] :
    AdicCompletion I A ⊗[A] B ≃ₐ[A] AdicCompletion (I.map (algebraMap A B)) B := by
  let J : Ideal B := I.map (algebraMap A B)
  have hIJ : I ≤ J.comap (Algebra.ofId A B) :=
    fun _ ha ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap A B) ha)
  let ψ : AdicCompletion I A ⊗[A] B →ₐ[A] AdicCompletion J B :=
    Algebra.TensorProduct.lift (mapₐ (Algebra.ofId A B) hIJ)
      (IsScalarTower.toAlgHom A B (AdicCompletion J B)) fun _ _ ↦ Commute.all _ _
  -- Compare module completion `AdicCompletion I B` with ring completion `AdicCompletion J B`.
  have hmem (n : ℕ) (b : B) :
      b ∈ (I ^ n • ⊤ : Submodule A B) ↔ b ∈ (J ^ n • ⊤ : Submodule B B) := by
    rw [← Submodule.restrictScalars_mem A ((J ^ n • ⊤ : Submodule B B))]
    simp [J, Ideal.map_pow]
  let q (n : ℕ) : B ⧸ (I ^ n • ⊤ : Submodule A B) →ₗ[A] B ⧸ (J ^ n • ⊤ : Submodule B B) :=
    (I ^ n • ⊤ : Submodule A B).liftQ
      ((Submodule.mkQ (J ^ n • ⊤ : Submodule B B)).restrictScalars A) fun b hb ↦
        LinearMap.mem_ker.mpr <| (Submodule.Quotient.mk_eq_zero _).mpr ((hmem n b).mp hb)
  have hq (n : ℕ) : Function.Bijective (q n) := by
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨b₁, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b₂, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
      rw [← sub_eq_zero, ← map_sub, ← Submodule.Quotient.mk_sub] at hxy
      exact (Submodule.Quotient.mk_eq_zero _).mpr <|
        (hmem n _).mpr ((Submodule.Quotient.mk_eq_zero _).mp hxy)
    · obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk b, rfl⟩
  let eqv (n : ℕ) := LinearEquiv.ofBijective (q n) (hq n)
  let fwd : AdicCompletion I B →ₗ[A] AdicCompletion J B :=
    { toFun := fun w ↦ ⟨fun n ↦ q n (eval I B n w), fun {m n} hmn ↦ by
        dsimp only
        obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (eval I B n w)
        have hprop : transitionMap I B hmn (eval I B n w) = eval I B m w := w.2 hmn
        rw [← hb] at hprop ⊢
        rw [← hprop]
        rfl⟩
      map_add' := fun x y ↦ AdicCompletion.ext fun n ↦ map_add (q n) _ _
      map_smul' := fun a x ↦ AdicCompletion.ext fun n ↦ map_smul (q n) a _ }
  have hfwd : Function.Bijective fwd := by
    refine ⟨fun w₁ w₂ hw ↦ AdicCompletion.ext fun n ↦ (hq n).1 (congrArg (eval J B n) hw),
      fun z ↦ ⟨⟨fun n ↦ (eqv n).symm (eval J B n z), fun {m n} hmn ↦ (eqv m).injective ?_⟩, ?_⟩⟩
    · dsimp only
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ ((eqv n).symm (eval J B n z))
      have hzn : eval J B n z = Submodule.Quotient.mk b := by
        have h1 := ((eqv n).apply_symm_apply (eval J B n z)).symm
        rwa [← hb] at h1
      have hzm : transitionMap J B hmn (eval J B n z) = eval J B m z := z.2 hmn
      rw [hzn] at hzm
      rw [← hb, (eqv m).apply_symm_apply, ← hzm]
      rfl
    · ext n
      exact (eqv n).apply_symm_apply (eval J B n z)
  have hlin : ψ.toLinearMap = fwd.comp ((ofTensorProduct I B).restrictScalars A) := by
    refine TensorProduct.ext' fun x b ↦ ?_
    obtain ⟨c, rfl⟩ := mk_surjective I A x
    refine ext_evalₐ fun n ↦ ?_
    let cn : A := c.1 n
    have heval_eq : eval J B n (fwd (ofTensorProduct I B (mk I A c ⊗ₜ[A] b))) =
        eval J B n (of J B (algebraMap A B cn * b)) := by
      change q n ((mk I A c).val n • (of I B b).val n) = _
      have hsmul : (mk I A c).val n • (of I B b).val n =
          (Submodule.Quotient.mk (cn • b) : B ⧸ (I ^ n • ⊤ : Submodule A B)) :=
        (Submodule.Quotient.mk_smul (I ^ n • ⊤ : Submodule A B) cn b).symm
      rw [hsmul]
      exact congrArg Submodule.Quotient.mk (Algebra.smul_def cn b)
    have hevalₐ_rhs : evalₐ J n (fwd (ofTensorProduct I B (mk I A c ⊗ₜ[A] b))) =
        Ideal.Quotient.mk (J ^ n) (algebraMap A B cn * b) := by
      have hJtop : (J ^ n • ⊤ : Ideal B) = J ^ n := by ext; simp
      have hcongr := congrArg (Ideal.quotientEquivAlgOfEq B hJtop) heval_eq
      exact hcongr.trans (evalₐ_of J n (algebraMap A B cn * b))
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hevalₐ_rhs]
    simp [ψ, cn]
  refine AlgEquiv.ofBijective ψ ?_
  have hfun : (ψ : AdicCompletion I A ⊗[A] B → AdicCompletion J B) = fwd ∘ ofTensorProduct I B :=
    funext fun z ↦ LinearMap.congr_fun hlin z
  rw [hfun]
  exact hfwd.comp (ofTensorProduct_bijective_of_finite I B)

/-- On pure tensors, `tensorAlgebraEquivMap` multiplies the mapped completion element by the image
of `b`. -/
@[simp]
theorem tensorAlgebraEquivMap_tmul (B : Type*) [CommRing B] [Algebra A B] [Module.Finite A B]
    (x : AdicCompletion I A) (b : B) :
    tensorAlgebraEquivMap I B (x ⊗ₜ[A] b) =
      mapₐ (I := I) (I' := I.map (algebraMap A B)) (Algebra.ofId A B)
        (fun _ ha ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap A B) ha)) x *
        of (I.map (algebraMap A B)) B b := by
  dsimp only [tensorAlgebraEquivMap]
  rw [AlgEquiv.ofBijective_apply, Algebra.TensorProduct.lift_tmul]
  rfl

end TensorAlgebra

section Invariants

variable (k : Type*) [CommRing k]
variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
  [IsScalarTower k A B] [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G k B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]

omit [Algebra k A] [IsScalarTower k A B] [IsNoetherianRing A] [Module.Finite A B]
  [FaithfulSMul A B] [Finite G] [Algebra.IsInvariant A B G] in
/-- The extended ideal `I.map (algebraMap A B)` is stable under `MulSemiringAction.toAlgEquiv`. -/
theorem map_map_algebraMap_toAlgEquiv (I : Ideal A) (g : G) :
    (I.map (algebraMap A B)).map (MulSemiringAction.toAlgEquiv k B g) =
      I.map (algebraMap A B) := by
  rw [map_toAlgEquiv_eq_smul k g, Ideal.pointwise_smul_def, Ideal.map_map]
  congr 1
  ext a
  exact smul_algebraMap g a

variable {k} in
/-- Over a Noetherian invariant ring `A` of a finite group `G` acting on a finite `A`-algebra `B`,
the map `AdicCompletion I A →ₐ[k] AdicCompletion (I.map (algebraMap A B)) B` is injective and its
range consists precisely of the `G`-invariant elements. -/
theorem mapₐ_invariants_injective_and_mem_range_iff (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G k B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (I : Ideal A) :
    Function.Injective (mapₐ (I := I) (I' := I.map (algebraMap A B))
      ((Algebra.ofId A B).restrictScalars k)
      (fun _ ha ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap A B) ha))) ∧
      ∀ y : AdicCompletion (I.map (algebraMap A B)) B,
        y ∈ Set.range (mapₐ (I := I) (I' := I.map (algebraMap A B))
          ((Algebra.ofId A B).restrictScalars k)
          (fun _ ha ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap A B) ha))) ↔
          ∀ g : G, congrₐ (MulSemiringAction.toAlgEquiv k B g)
            (map_map_algebraMap_toAlgEquiv (G := G) k I g) y = y := by
  let ρ : Representation A G B := Representation.ofDistribMulAction A G B
  -- Identify `A` with `ρ.invariants` using `FaithfulSMul A B` and `Algebra.IsInvariant A B G`.
  have hinv_mem (a : A) : algebraMap A B a ∈ ρ.invariants := fun g ↦ smul_algebraMap g a
  let eInv : A ≃ₗ[A] ρ.invariants := LinearEquiv.ofBijective
    ((Algebra.linearMap A B).codRestrict ρ.invariants hinv_mem)
    ⟨fun a₁ a₂ h ↦ FaithfulSMul.algebraMap_injective A B (congrArg Subtype.val h),
      fun ⟨b, hb⟩ ↦ by
        obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) b hb
        exact ⟨a, Subtype.ext ha⟩⟩
  let eBase : AdicCompletion I A ≃ₗ[AdicCompletion I A]
      (ρ.baseChange (AdicCompletion I A)).invariants :=
    (AlgebraTensorModule.rid A (AdicCompletion I A) (AdicCompletion I A)).symm.trans <|
      (AlgebraTensorModule.congr (LinearEquiv.refl (AdicCompletion I A) _) eInv).trans <|
        ρ.invariantsBaseChangeEquiv
  have heInv1 : (eInv 1 : B) = 1 := map_one (algebraMap A B)
  have heBase (x : AdicCompletion I A) :
      ((eBase x : (ρ.baseChange (AdicCompletion I A)).invariants) : AdicCompletion I A ⊗[A] B) =
        x ⊗ₜ[A] 1 := by
    simp [eBase, heInv1]
  let eAlg := tensorAlgebraEquivMap I B
  have hmap_eq (x : AdicCompletion I A) :
      mapₐ (I := I) (I' := I.map (algebraMap A B)) ((Algebra.ofId A B).restrictScalars k)
        (fun _ ha ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap A B) ha)) x =
        eAlg (x ⊗ₜ[A] 1) := by
    rw [tensorAlgebraEquivMap_tmul]
    refine ext_evalₐ fun n ↦ ?_
    simp only [map_mul, evalₐ_of, map_one, mul_one, evalₐ_mapₐ]
    rfl
  have hequiv (g : G) (z : AdicCompletion I A ⊗[A] B) :
      congrₐ (MulSemiringAction.toAlgEquiv k B g) (map_map_algebraMap_toAlgEquiv (G := G) k I g)
          (eAlg z) =
        eAlg ((ρ.baseChange (AdicCompletion I A)) g z) := by
    refine TensorProduct.inductionOn z (fun x b ↦ ?_) (fun z₁ z₂ hz₁ hz₂ ↦ ?_)
    · rw [Representation.baseChange_apply, LinearMap.baseChange_tmul, tensorAlgebraEquivMap_tmul,
        tensorAlgebraEquivMap_tmul, map_mul, congrₐ_of]
      congr 1
      refine ext_evalₐ fun n ↦ ?_
      simp only [evalₐ_congrₐ, evalₐ_mapₐ]
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
      simp [← ha, smul_algebraMap]
    · simp [map_add, hz₁, hz₂]
  refine ⟨fun x₁ x₂ hx ↦ eBase.injective <| Subtype.ext <| eAlg.injective ?_, fun y ↦ ?_⟩
  · rwa [heBase, heBase, ← hmap_eq, ← hmap_eq]
  · obtain ⟨z, rfl⟩ := eAlg.surjective y
    simp only [hequiv, EmbeddingLike.apply_eq_iff_eq, ← Representation.mem_invariants]
    constructor
    · rintro ⟨x, hx⟩
      rw [hmap_eq] at hx
      have hzx : x ⊗ₜ[A] (1 : B) = z := eAlg.injective hx
      rw [← hzx, ← heBase]
      exact (eBase x).2
    · intro hz
      refine ⟨eBase.symm ⟨z, hz⟩, ?_⟩
      rw [hmap_eq, ← heBase, LinearEquiv.apply_symm_apply]

omit [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B] in
/-- For a maximal ideal `Q` of `B` and `P = Q.under A`, the radical of `P.map (algebraMap A B)` is
the intersection of the `G`-orbit of `Q`. -/
private theorem radical_map_under_eq_iInf_orbit (Q : Ideal B) [Q.IsMaximal] :
    ((Q.under A).map (algebraMap A B)).radical =
      ⨅ R : MulAction.orbit G Q, (R : Ideal B) := by
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have hPmax : (Q.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Q
  refine le_antisymm ?_ ?_
  · refine le_iInf fun ⟨R, hR⟩ ↦ ?_
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hR
    have hRmax : R.IsMaximal := hg ▸ inferInstance
    rw [hRmax.isPrime.radical_le_iff, Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← hg,
      Ideal.under_smul]
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf fun M ⟨hPM, hMprime⟩ ↦ ?_
    have hunder : Q.under A = M.under A :=
      hPmax.eq_of_le (hMprime.comap (algebraMap A B)).ne_top (Ideal.map_le_iff_le_comap.mp hPM)
    obtain ⟨g, rfl⟩ := Ideal.exists_smul_eq_of_under_eq A G Q M hunder
    exact iInf_le (fun R : MulAction.orbit G Q ↦ (R : Ideal B))
      ⟨g • Q, MulAction.mem_orbit Q g⟩

variable (A G) in
/-- **Completed-local invariants and decomposition groups.** Let `A` be the Noetherian invariant
ring of a finite group `G` acting on a finite `A`-algebra `B`, and let `Q` be a maximal ideal of
`B`. The canonical map `AdicCompletion (Q.under A) A →ₐ[k] AdicCompletion Q B` lands in the
`MulAction.stabilizer G Q`-fixed subalgebra and restricts to a `k`-algebra isomorphism
`AdicCompletion (Q.under A) A ≃ₐ[k] FixedPoints.subalgebra k (AdicCompletion Q B)
(MulAction.stabilizer G Q)`. -/
noncomputable def stabilizerFixedPointsEquiv (Q : Ideal B) [Q.IsMaximal] :
    AdicCompletion (Q.under A) A ≃ₐ[k]
      FixedPoints.subalgebra k (AdicCompletion Q B) (MulAction.stabilizer G Q) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Finite (MulAction.orbit G Q) := Finite.of_surjective
    (fun g : G ↦ (⟨g • Q, MulAction.mem_orbit Q g⟩ : MulAction.orbit G Q))
    fun ⟨_, hR⟩ ↦ let ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hR; ⟨g, Subtype.ext hg⟩
  let P := Q.under A
  have hMax (R : MulAction.orbit G Q) : (R : Ideal B).IsMaximal := by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp R.2
    exact hg ▸ inferInstance
  have hCop : Pairwise (IsCoprime on fun R : MulAction.orbit G Q ↦ (R : Ideal B)) :=
    fun R₁ R₂ hne ↦ by
      have := hMax R₁
      have := hMax R₂
      exact Ideal.isCoprime_of_isMaximal (Subtype.coe_ne_coe.mpr hne)
  let crt := equivPiOfRadicalEqIInf k (fun R : MulAction.orbit G Q ↦ (R : Ideal B)) hCop
    (radical_map_under_eq_iInf_orbit (A := A) (G := G) Q)
  obtain ⟨hι_inj, hι_range⟩ := mapₐ_invariants_injective_and_mem_range_iff (k := k) (B := B) G P
  let ι : AdicCompletion P A →ₐ[k] AdicCompletion (P.map (algebraMap A B)) B :=
    mapₐ (I := P) (I' := P.map (algebraMap A B)) ((Algebra.ofId A B).restrictScalars k)
      (fun _ ha ↦ Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap A B) ha))
  let R₀ : MulAction.orbit G Q := ⟨Q, MulAction.mem_orbit_self Q⟩
  let π : AdicCompletion P A →ₐ[k] AdicCompletion Q B :=
    mapₐ (I := P) (I' := Q) ((Algebra.ofId A B).restrictScalars k)
      (fun _ ha ↦ Ideal.mem_comap.mpr ha)
  have hπ_ι (x : AdicCompletion P A) :
      π x = mapₐ (I := P.map (algebraMap A B)) (I' := Q) (AlgHom.id k B)
        (Ideal.map_le_iff_le_comap.mpr fun _ ha ↦ Ideal.mem_comap.mpr ha) (ι x) := by
    refine ext_evalₐ fun n ↦ ?_
    simp only [π, ι, evalₐ_mapₐ]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ P n x)
    simp [← ha]
  -- Every orbit coordinate of `crt (ι x)` is a `G`-translate of `π x`.
  have hcoord (x : AdicCompletion P A) (R : MulAction.orbit G Q) (g : G) (hg : g • Q = R.1) :
      crt (ι x) R = congrₐ (MulSemiringAction.toAlgEquiv k B g)
        ((map_toAlgEquiv_eq_smul k g Q).trans hg) (π x) := by
    have hfix := (hι_range (ι x)).mp ⟨x, rfl⟩ g
    refine ext_evalₐ fun n ↦ ?_
    dsimp only [crt]
    rw [equivPiOfRadicalEqIInf_apply, ← hfix, hπ_ι]
    simp only [P, evalₐ_mapₐ, evalₐ_congrₐ]
    obtain ⟨b, hb⟩ :=
      Ideal.Quotient.mk_surjective (evalₐ ((Q.under A).map (algebraMap A B)) n (ι x))
    simp [← hb]
  have hπ_eq (x : AdicCompletion P A) : π x = crt (ι x) R₀ := by
    rw [hcoord x R₀ 1 (one_smul G Q)]
    refine ext_evalₐ fun n ↦ ?_
    rw [evalₐ_congrₐ]
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ Q n (π x))
    simp [← hb]
  have hinv_orbit (g : G) (R : MulAction.orbit G Q) :
      g⁻¹ • (R : Ideal B) ∈ MulAction.orbit G Q := by
    obtain ⟨g', hg'⟩ := MulAction.mem_orbit_iff.mp R.2
    exact MulAction.mem_orbit_iff.mpr ⟨g⁻¹ * g', by simp [← hg', mul_smul]⟩
  -- Action compatibility of the CRT coordinates across the `G`-orbit.
  have hcrt_smul (g : G) (y : AdicCompletion (P.map (algebraMap A B)) B)
      (R : MulAction.orbit G Q) :
      crt (congrₐ (MulSemiringAction.toAlgEquiv k B g)
          (map_map_algebraMap_toAlgEquiv (G := G) k P g) y) R =
        congrₐ (MulSemiringAction.toAlgEquiv k B g)
          ((map_toAlgEquiv_eq_smul k g (g⁻¹ • (R : Ideal B))).trans (smul_inv_smul g R.1))
          (crt y ⟨g⁻¹ • (R : Ideal B), hinv_orbit g R⟩) := by
    refine ext_evalₐ fun n ↦ ?_
    dsimp only [crt]
    simp only [P, equivPiOfRadicalEqIInf_apply, evalₐ_congrₐ, evalₐ_mapₐ]
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ ((Q.under A).map (algebraMap A B)) n y)
    simp [← hb]
  have hπ_mem (x : AdicCompletion P A) :
      π x ∈ FixedPoints.subalgebra k (AdicCompletion Q B) (MulAction.stabilizer G Q) := fun h ↦ by
    rw [smul_stabilizer_eq_congrₐ k h,
      ← hcoord x R₀ (h : G) (MulAction.mem_stabilizer_iff.mp h.2), ← hπ_eq]
  refine AlgEquiv.ofBijective (π.codRestrict _ hπ_mem) ⟨fun x₁ x₂ hx ↦ ?_, fun z ↦ ?_⟩
  · apply hι_inj (crt.injective (funext fun R ↦ ?_))
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp R.2
    rw [hcoord x₁ R g hg, hcoord x₂ R g hg, show π x₁ = π x₂ from congrArg Subtype.val hx]
  · -- Induce `z` from `MulAction.stabilizer G Q` across `MulAction.orbit G Q` (Shapiro's lemma).
    choose σ hσ using fun R : MulAction.orbit G Q ↦ MulAction.mem_orbit_iff.mp R.2
    let w : ∀ R : MulAction.orbit G Q, AdicCompletion (R : Ideal B) B := fun R ↦
      congrₐ (MulSemiringAction.toAlgEquiv k B (σ R))
        ((map_toAlgEquiv_eq_smul k (σ R) Q).trans (hσ R)) z.1
    have hw_indep (R : MulAction.orbit G Q) (g : G) (hg : g • Q = R.1) :
        congrₐ (MulSemiringAction.toAlgEquiv k B g)
          ((map_toAlgEquiv_eq_smul k g Q).trans hg) z.1 = w R := by
      let h : MulAction.stabilizer G Q := ⟨g⁻¹ * σ R,
        MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, hσ R, ← hg, inv_smul_smul])⟩
      have hz : h • z.1 = z.1 := z.2 h
      refine ext_evalₐ fun n ↦ ?_
      rw [← hz, smul_stabilizer_eq_congrₐ k h]
      dsimp only [w]
      simp only [evalₐ_congrₐ]
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ Q n z.1)
      simp [← hb, h, mul_smul]
    have hw_inv (g : G) :
        congrₐ (MulSemiringAction.toAlgEquiv k B g)
          (map_map_algebraMap_toAlgEquiv (G := G) k P g) (crt.symm w) = crt.symm w := by
      apply crt.injective (funext fun R ↦ ?_)
      rw [hcrt_smul, crt.apply_symm_apply]
      let R' : MulAction.orbit G Q := ⟨g⁻¹ • R.1, hinv_orbit g R⟩
      have hmul : (g * σ R') • Q = R.1 := by
        rw [mul_smul, hσ R']
        exact smul_inv_smul g R.1
      rw [← hw_indep R (g * σ R') hmul]
      refine ext_evalₐ fun n ↦ ?_
      change evalₐ R.1 n (congrₐ (MulSemiringAction.toAlgEquiv k B g) _ (w R')) = _
      dsimp only [w]
      simp only [evalₐ_congrₐ]
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ Q n z.1)
      simp [← hb, mul_smul]
    obtain ⟨x, hx⟩ := (hι_range (crt.symm w)).mpr hw_inv
    refine ⟨x, Subtype.ext ?_⟩
    change π x = z.1
    rw [hπ_eq, hx, crt.apply_symm_apply, ← hw_indep R₀ 1 (one_smul G Q)]
    refine ext_evalₐ fun n ↦ ?_
    rw [evalₐ_congrₐ]
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ Q n z.1)
    simp [R₀, ← hb]

variable (A G) in
/-- Underlying algebra homomorphism of `stabilizerFixedPointsEquiv`. -/
@[simp]
theorem coe_stabilizerFixedPointsEquiv_apply (Q : Ideal B) [Q.IsMaximal]
    (x : AdicCompletion (Q.under A) A) :
    (stabilizerFixedPointsEquiv k A G Q x : AdicCompletion Q B) =
      mapₐ (I := Q.under A) (I' := Q) ((Algebra.ofId A B).restrictScalars k)
        (fun _ ha ↦ Ideal.mem_comap.mpr ha) x := by
  rfl

variable (A) in
/-- **Completed-local comparison with intermediate stabilizer invariants.** Let `H` be a subgroup
of `G` containing `MulAction.stabilizer G Q`, and let `C` be an intermediate `H`-invariant ring
between `A` and `B`. Then the canonical homomorphism `A → C` induces a `k`-algebra isomorphism
`AdicCompletion (Q.under A) A ≃ₐ[k] AdicCompletion (Q.under C) C`. -/
noncomputable def underInvariantsEquivOfStabilizerLE (Q : Ideal B) [Q.IsMaximal]
    {H : Subgroup G} (hH : MulAction.stabilizer G Q ≤ H)
    (C : Type*) [CommRing C] [Algebra k C] [Algebra A C] [Algebra C B]
    [IsScalarTower k A C] [IsScalarTower A C B] [FaithfulSMul C B]
    [SMulCommClass H C B] [Algebra.IsInvariant C B H] :
    AdicCompletion (Q.under A) A ≃ₐ[k] AdicCompletion (Q.under C) C := by
  have : IsScalarTower k C B := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply k A B, IsScalarTower.algebraMap_apply k A C,
      ← IsScalarTower.algebraMap_apply A C B]
  have : SMulCommClass H k B := ⟨fun h r b ↦ smul_comm (h : G) r b⟩
  have : IsNoetherian A B := inferInstance
  have hAC_inj : Function.Injective (IsScalarTower.toAlgHom A C B).toLinearMap :=
    FaithfulSMul.algebraMap_injective C B
  have : IsNoetherian A C := isNoetherian_of_injective _ hAC_inj
  have : Module.Finite A C := Module.IsNoetherian.finite A C
  have : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
  have hunder : Q.under A ≤ (Q.under C).comap (IsScalarTower.toAlgHom k A C) := fun a ha ↦ by
    change algebraMap C B (algebraMap A C a) ∈ Q
    rwa [← IsScalarTower.algebraMap_apply A C B]
  let f : AdicCompletion (Q.under A) A →ₐ[k] AdicCompletion (Q.under C) C :=
    mapₐ (IsScalarTower.toAlgHom k A C) hunder
  let eA := stabilizerFixedPointsEquiv k A G Q
  let eC := stabilizerFixedPointsEquiv k C H Q
  have hf_comp (x : AdicCompletion (Q.under A) A) : (eC (f x) : AdicCompletion Q B) = eA x := by
    rw [coe_stabilizerFixedPointsEquiv_apply, coe_stabilizerFixedPointsEquiv_apply]
    refine ext_evalₐ fun n ↦ ?_
    simp only [f, evalₐ_mapₐ]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ (Q.under A) n x)
    simp [← ha, ← IsScalarTower.algebraMap_apply A C B]
  refine AlgEquiv.ofBijective f ⟨fun x₁ x₂ hx ↦ eA.injective <| Subtype.ext ?_, fun y ↦ ?_⟩
  · rw [← hf_comp, ← hf_comp, hx]
  · have hy_mem : (eC y : AdicCompletion Q B) ∈
        FixedPoints.subalgebra k (AdicCompletion Q B) (MulAction.stabilizer G Q) := fun g ↦ by
      let gH : MulAction.stabilizer H Q := ⟨⟨g.1, hH g.2⟩, g.2⟩
      have hyg := (eC y).2 gH
      refine (ext_evalₐ fun n ↦ ?_).trans hyg
      change evalₐ Q n (congrₐ (MulSemiringAction.toAlgEquiv ℤ B g.1) _ (eC y).1) =
        evalₐ Q n (congrₐ (MulSemiringAction.toAlgEquiv ℤ B (gH : H)) _ (eC y).1)
      rw [evalₐ_congrₐ, evalₐ_congrₐ]
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ Q n (eC y).1)
      simp [← hb, gH]
    refine ⟨eA.symm ⟨eC y, hy_mem⟩, eC.injective <| Subtype.ext ?_⟩
    rw [hf_comp, eA.apply_symm_apply]

variable (A) in
/-- As an algebra homomorphism, `underInvariantsEquivOfStabilizerLE` is `mapₐ` of `A →ₐ[k] C`. -/
@[simp]
theorem toAlgHom_underInvariantsEquivOfStabilizerLE (Q : Ideal B) [Q.IsMaximal]
    {H : Subgroup G} (hH : MulAction.stabilizer G Q ≤ H)
    (C : Type*) [CommRing C] [Algebra k C] [Algebra A C] [Algebra C B]
    [IsScalarTower k A C] [IsScalarTower A C B] [FaithfulSMul C B]
    [SMulCommClass H C B] [Algebra.IsInvariant C B H] :
    (underInvariantsEquivOfStabilizerLE k A Q hH C :
        AdicCompletion (Q.under A) A →ₐ[k] AdicCompletion (Q.under C) C) =
      mapₐ (IsScalarTower.toAlgHom k A C) (fun a ha ↦ by
        change algebraMap C B (algebraMap A C a) ∈ Q
        rwa [← IsScalarTower.algebraMap_apply A C B]) :=
  AlgHom.ext fun _ ↦ rfl

variable (A) in
/-- On canonical images of elements of `A`, `underInvariantsEquivOfStabilizerLE` applies
`algebraMap A C`. -/
@[simp]
theorem underInvariantsEquivOfStabilizerLE_of (Q : Ideal B) [Q.IsMaximal]
    {H : Subgroup G} (hH : MulAction.stabilizer G Q ≤ H)
    (C : Type*) [CommRing C] [Algebra k C] [Algebra A C] [Algebra C B]
    [IsScalarTower k A C] [IsScalarTower A C B] [FaithfulSMul C B]
    [SMulCommClass H C B] [Algebra.IsInvariant C B H] (a : A) :
    underInvariantsEquivOfStabilizerLE k A Q hH C (of (Q.under A) A a) =
      of (Q.under C) C (algebraMap A C a) := by
  change mapₐ _ _ (of (Q.under A) A a) = _
  simp

end Invariants

end AdicCompletion

namespace TauCeti.AdicCompletion

open scoped Pointwise

variable (A : Type*) {B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [Module.Finite A B] [FaithfulSMul A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]

/-- Under the hypotheses of `AdicCompletion.underInvariantsEquivOfStabilizerLE`, the localizations
of `A` and `C` below a maximal ideal `Q` of `B` have the same Krull dimension. -/
theorem ringKrullDim_atPrime_under_eq_of_stabilizer_le (Q : Ideal B) [Q.IsMaximal]
    {H : Subgroup G} (hH : MulAction.stabilizer G Q ≤ H)
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [FaithfulSMul C B] [SMulCommClass H C B] [Algebra.IsInvariant C B H] :
    ringKrullDim (Localization.AtPrime (Q.under A)) =
      ringKrullDim (Localization.AtPrime (Q.under C)) := by
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have : Algebra.IsIntegral C B := Algebra.IsInvariant.isIntegral C B H
  have : (Q.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Q
  have : (Q.under C).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := C) Q
  have : IsNoetherian A C :=
    isNoetherian_of_injective (IsScalarTower.toAlgHom A C B).toLinearMap
      (FaithfulSMul.algebraMap_injective C B)
  have : Module.Finite A C := Module.IsNoetherian.finite A C
  have : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  rw [← ringKrullDim_eq_atPrime (Q.under A), ← ringKrullDim_eq_atPrime (Q.under C)]
  exact ringKrullDim_eq_of_ringEquiv
    (_root_.AdicCompletion.underInvariantsEquivOfStabilizerLE A A Q hH C).toRingEquiv

/-- Under the hypotheses of `AdicCompletion.underInvariantsEquivOfStabilizerLE`, the localization
of `A` at `Q.under A` is a regular local ring if and only if the localization of `C` at `Q.under C`
is a regular local ring. -/
theorem isRegularLocalRing_atPrime_under_iff_of_stabilizer_le (Q : Ideal B) [Q.IsMaximal]
    {H : Subgroup G} (hH : MulAction.stabilizer G Q ≤ H)
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [FaithfulSMul C B] [SMulCommClass H C B] [Algebra.IsInvariant C B H] :
    IsRegularLocalRing (Localization.AtPrime (Q.under A)) ↔
      IsRegularLocalRing (Localization.AtPrime (Q.under C)) := by
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have : Algebra.IsIntegral C B := Algebra.IsInvariant.isIntegral C B H
  have : (Q.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Q
  have : (Q.under C).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := C) Q
  have : IsNoetherian A C :=
    isNoetherian_of_injective (IsScalarTower.toAlgHom A C B).toLinearMap
      (FaithfulSMul.algebraMap_injective C B)
  have : Module.Finite A C := Module.IsNoetherian.finite A C
  have : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  rw [← isRegularLocalRing_iff_atPrime (Q.under A), ← isRegularLocalRing_iff_atPrime (Q.under C)]
  let e := (_root_.AdicCompletion.underInvariantsEquivOfStabilizerLE A A Q hH C).toRingEquiv
  exact ⟨fun h ↦ h.of_ringEquiv e, fun h ↦ h.of_ringEquiv e.symm⟩

end TauCeti.AdicCompletion
