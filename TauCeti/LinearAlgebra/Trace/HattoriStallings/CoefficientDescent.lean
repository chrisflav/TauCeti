/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coset.Card
public import TauCeti.LinearAlgebra.Trace.HattoriStallings.DiagonalTensor

/-!
# Coefficient Descent for Centralizer and Coinvariant Traces

This file establishes base-change compatibility and prime-power coefficient descent for centralizer
and coinvariant Hattori–Stallings traces, following Stacks Project, Section 64.15 (Lemma 64.15.9).

## Main definitions

* `MonoidAlgebra.TrivialAction Λ`: a wrapper around `Λ` equipped with the trivial
  `MonoidAlgebra Λ Γ`-action (`single γ a • x = a • x`), providing base change `P ⊗[A] Λ` as
  `DiagonalTensor A Λ P (TrivialAction Λ)`.

## Main results

* `ZMod.castHom_eq_of_mul_eq_of_not_pow_dvd`: cancelling a factor `d` with `ℓ^(v+1) ∤ d` when
  reducing an equality in `ZMod (ℓ ^ (n + v))` modulo `ℓ ^ n`.
* `LinearMap.centralizerTrace_baseChange`, `LinearMap.centralizerScalarTrace_baseChange`:
  base-change compatibility of the centralizer trace along any algebra map `A →+* Λ`.
* `LinearMap.castHom_centralizerScalarTrace_eq_of_projectiveTrace_eq` and
  `LinearMap.centralizerScalarTrace_zmod_baseChange_eq_of_projectiveTrace_eq`:
  Stacks Lemma 64.15.9 at a single element `γ` — equality of `ZMod (ℓ ^ (n + v))`-linear
  projective traces implies equality of centralizer traces modulo `ℓ ^ n`, provided
  `ℓ ^ (v + 1) ∤ |Z_γ|`.
* `TauCeti.MonoidExtension.hattoriStallingsTrace_diagonalTensor_eq_of_projectiveTrace_eq`:
  full diagonal-coinvariant coefficient descent over an arbitrary (possibly noncommutative)
  `ZMod (ℓ ^ n)`-algebra `Λ` when `ℓ ^ (v + 1) ∤ |G|`.

## References

* [Stacks Project, Lemma 64.15.9 (Tag 03UD)](https://stacks.math.columbia.edu/tag/03UD)
-/

@[expose] public section

noncomputable section

/-! ### Section 1: Prime-power cancellation in `ZMod` -/

namespace ZMod

/-- If `ℓ` is prime, `ℓ ^ (v + 1) ∤ d`, and `d * x = d * y` in `ZMod (ℓ ^ (n + v))`, then `x` and
`y` have the same reduction in `ZMod (ℓ ^ n)`. -/
theorem castHom_eq_of_mul_eq_of_not_pow_dvd {ℓ n v d : ℕ} (hℓ : ℓ.Prime)
    (hnd : ¬ ℓ ^ (v + 1) ∣ d) {x y : ZMod (ℓ ^ (n + v))}
    (hxy : (d : ZMod (ℓ ^ (n + v))) * x = (d : ZMod (ℓ ^ (n + v))) * y) :
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n)) x =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n)) y := by
  have : NeZero (ℓ ^ (n + v)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hnd (dvd_zero _)
  let z : ZMod (ℓ ^ (n + v)) := x - y
  have hdz : (d : ZMod (ℓ ^ (n + v))) * z = 0 := by
    simp only [z, mul_sub, sub_eq_zero]
    exact hxy
  have hcast : ((d * z.val : ℕ) : ZMod (ℓ ^ (n + v))) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, hdz]
  have hdvd : ℓ ^ (n + v) ∣ d * z.val :=
    (ZMod.natCast_eq_zero_iff (d * z.val) (ℓ ^ (n + v))).mp hcast
  have hfac : d.factorization ℓ ≤ v := by
    by_contra hlt
    have hge : v + 1 ≤ d.factorization ℓ := Nat.lt_of_not_ge hlt
    exact hnd ((pow_dvd_pow ℓ hge).trans (Nat.ordProj_dvd d ℓ))
  have hcop : Nat.Coprime (ℓ ^ (n + v)) (ordCompl[ℓ] d) :=
    (Nat.coprime_ordCompl hℓ hd0).pow_left (n + v)
  have hdvd_split : ℓ ^ (n + v) ∣ (ordProj[ℓ] d * z.val) * ordCompl[ℓ] d := by
    have hmul : (ordProj[ℓ] d * z.val) * ordCompl[ℓ] d = d * z.val := by
      calc (ordProj[ℓ] d * z.val) * ordCompl[ℓ] d
          = (ordProj[ℓ] d * ordCompl[ℓ] d) * z.val := by ring
        _ = d * z.val := by rw [Nat.ordProj_mul_ordCompl_eq_self]
    rwa [hmul]
  have hdvd_proj : ℓ ^ (n + v) ∣ ordProj[ℓ] d * z.val :=
    hcop.dvd_of_dvd_mul_right hdvd_split
  have hdvd_v : ℓ ^ n * ℓ ^ v ∣ z.val * ℓ ^ v := by
    have h1 : ℓ ^ (n + v) ∣ ℓ ^ v * z.val :=
      hdvd_proj.trans (mul_dvd_mul_right (pow_dvd_pow ℓ hfac) z.val)
    calc ℓ ^ n * ℓ ^ v = ℓ ^ (n + v) := (pow_add ℓ n v).symm
      _ ∣ ℓ ^ v * z.val := h1
      _ = z.val * ℓ ^ v := mul_comm _ _
  have hdvd_n : ℓ ^ n ∣ z.val :=
    (mul_dvd_mul_iff_right (pow_ne_zero v hℓ.ne_zero)).mp hdvd_v
  have hz0 : ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n)) z = 0 := by
    rw [← ZMod.natCast_zmod_val z, map_natCast]
    exact (ZMod.natCast_eq_zero_iff z.val (ℓ ^ n)).mpr hdvd_n
  have hsub : ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n)) x -
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n)) y = 0 := by
    rw [← map_sub]
    exact hz0
  exact sub_eq_zero.mp hsub

end ZMod

/-! ### Section 2: Trivial monoid-algebra module and base change -/

namespace MonoidAlgebra

/-- Wrapper around `Λ` equipped with the trivial `MonoidAlgebra Λ Γ`-action (`single γ a • x =
a • x`). Used to realize base change `P ⊗[A] Λ` as `DiagonalTensor A Λ P (TrivialAction Λ)`
without colliding with any module structure on `Λ` itself. -/
structure TrivialAction (Λ : Type*) where
  /-- Underlying element of `Λ`. -/
  val : Λ

namespace TrivialAction

@[ext]
theorem ext {Λ : Type*} {x y : TrivialAction Λ} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

section AddCommGroup

variable {Λ : Type*} [AddCommGroup Λ]

instance instAddCommGroup : AddCommGroup (TrivialAction Λ) where
  add x y := ⟨x.val + y.val⟩
  zero := ⟨0⟩
  neg x := ⟨-x.val⟩
  sub x y := ⟨x.val - y.val⟩
  nsmul n x := ⟨n • x.val⟩
  zsmul n x := ⟨n • x.val⟩
  add_assoc x y z := ext (add_assoc x.val y.val z.val)
  zero_add x := ext (zero_add x.val)
  add_zero x := ext (add_zero x.val)
  nsmul_zero x := ext (AddMonoid.nsmul_zero x.val)
  nsmul_succ n x := ext (AddMonoid.nsmul_succ n x.val)
  zsmul_zero' x := ext (SubNegMonoid.zsmul_zero' x.val)
  zsmul_succ' n x := ext (SubNegMonoid.zsmul_succ' n x.val)
  zsmul_neg' n x := ext (SubNegMonoid.zsmul_neg' n x.val)
  neg_add_cancel x := ext (neg_add_cancel x.val)
  sub_eq_add_neg x y := ext (sub_eq_add_neg x.val y.val)
  add_comm x y := ext (add_comm x.val y.val)

@[simp]
theorem val_zero : (0 : TrivialAction Λ).val = 0 := (rfl)

@[simp]
theorem val_add (x y : TrivialAction Λ) : (x + y).val = x.val + y.val := (rfl)

@[simp]
theorem val_neg (x : TrivialAction Λ) : (-x).val = -x.val := (rfl)

@[simp]
theorem val_sub (x y : TrivialAction Λ) : (x - y).val = x.val - y.val := (rfl)

/-- Any `R`-module structure on `Λ` transfers to `TrivialAction Λ`. For `R = ℤ`, this agrees
definitionally with `AddCommGroup.toIntModule`. -/
instance instModule {R : Type*} [Semiring R] [Module R Λ] : Module R (TrivialAction Λ) where
  smul r x := ⟨r • x.val⟩
  one_smul x := ext (one_smul R x.val)
  mul_smul r s x := ext (mul_smul r s x.val)
  smul_zero r := ext (smul_zero r)
  smul_add r x y := ext (smul_add r x.val y.val)
  add_smul r s x := ext (add_smul r s x.val)
  zero_smul x := ext (zero_smul R x.val)

@[simp]
theorem val_smul {R : Type*} [Semiring R] [Module R Λ] (r : R) (x : TrivialAction Λ) :
    (r • x).val = r • x.val :=
  (rfl)

instance instIsScalarTower {R S : Type*} [Semiring R] [Semiring S] [SMul R S]
    [Module R Λ] [Module S Λ] [IsScalarTower R S Λ] :
    IsScalarTower R S (TrivialAction Λ) where
  smul_assoc r s x := ext (smul_assoc r s x.val)

end AddCommGroup

section Ring

variable {Λ : Type*} [Ring Λ]

/-- Canonical `Λ`-linear equivalence `TrivialAction Λ ≃ₗ[Λ] Λ`. -/
def equivSelf (Λ : Type*) [Ring Λ] : TrivialAction Λ ≃ₗ[Λ] Λ where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance instFinite : Module.Finite Λ (TrivialAction Λ) :=
  Module.Finite.equiv (equivSelf Λ).symm

instance instProjective : Module.Projective Λ (TrivialAction Λ) :=
  Module.Projective.of_equiv (equivSelf Λ).symm

/-- Ring homomorphism `MonoidAlgebra Λ Γ →+* Module.End ℤ (TrivialAction Λ)` sending `single γ a`
to left multiplication by `a`. -/
def trivialActionHom (Λ Γ : Type*) [Ring Λ] [Monoid Γ] :
    MonoidAlgebra Λ Γ →+* Module.End ℤ (TrivialAction Λ) :=
  liftNCRingHom
    { toFun := fun r ↦
        { toFun := fun x ↦ r • x
          map_add' := smul_add r
          map_smul' := fun n x ↦ by simp only [RingHom.id_apply, smul_comm n r x] }
      map_one' := by ext x; simp
      map_mul' := fun r s ↦ by ext x; simp [mul_smul]
      map_zero' := by ext x; simp
      map_add' := fun r s ↦ by ext x; simp [add_smul] }
    (1 : Γ →* Module.End ℤ (TrivialAction Λ))
    (fun r _ ↦ by
      ext x
      simp)

/-- Trivial `MonoidAlgebra Λ Γ`-module structure on `TrivialAction Λ`. -/
instance instModuleMonoidAlgebra {Γ : Type*} [Monoid Γ] :
    Module (MonoidAlgebra Λ Γ) (TrivialAction Λ) :=
  Module.compHom (TrivialAction Λ) (trivialActionHom Λ Γ)

@[simp]
theorem single_smul {Γ : Type*} [Monoid Γ] (γ : Γ) (a : Λ) (x : TrivialAction Λ) :
    (single γ a : MonoidAlgebra Λ Γ) • x = a • x := by
  change (trivialActionHom Λ Γ (single γ a)) x = a • x
  rw [trivialActionHom, liftNCRingHom_single]
  simp

instance instIsScalarTowerMonoidAlgebra {Γ : Type*} [Monoid Γ] :
    IsScalarTower Λ (MonoidAlgebra Λ Γ) (TrivialAction Λ) where
  smul_assoc r u x := by
    induction u using MonoidAlgebra.induction_linear with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => simp [add_smul, smul_add, h₁, h₂]
    | single γ a => simp [smul_single, mul_smul]

theorem smul_eq_mapDomain {G Γ : Type*} [Monoid G] [Monoid Γ] (ι : G →* Γ)
    (r : MonoidAlgebra Λ G) (x : TrivialAction Λ) :
    r • x = mapDomain ι r • x := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r₁ r₂ h₁ h₂ => simp [add_smul, mapDomain_add, h₁, h₂]
  | single g a => simp [mapDomain_single]

@[simp]
theorem singleSMulEnd_eq_id {Γ : Type*} [Monoid Γ] (γ : Γ) :
    singleSMulEnd Λ γ (TrivialAction Λ) = .id := by
  ext x
  simp [singleSMulEnd_apply]

theorem hattoriStallingsTrace_singleSMulEnd {Γ : Type*} [Monoid Γ] (γ : Γ) :
    LinearMap.hattoriStallingsTrace Λ (TrivialAction Λ)
        (singleSMulEnd Λ γ (TrivialAction Λ)) =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ 1 := by
  rw [singleSMulEnd_eq_id]
  let b : Module.Basis Unit Λ (TrivialAction Λ) :=
    (Module.Basis.singleton Unit Λ).map (equivSelf Λ).symm
  rw [LinearMap.hattoriStallingsTrace_id_of_basis b]
  simp

theorem projectiveTrace_singleSMulEnd {Λ Γ : Type*} [CommRing Λ] [Monoid Γ] (γ : Γ) :
    LinearMap.projectiveTrace Λ (TrivialAction Λ) (singleSMulEnd Λ γ (TrivialAction Λ)) = 1 := by
  rw [← LinearMap.cyclicQuotientEquivSelf_hattoriStallingsTrace,
    hattoriStallingsTrace_singleSMulEnd, TauCeti.cyclicQuotientEquivSelf_mkQ]

end Ring

end TrivialAction

end MonoidAlgebra

/-! ### Section 3: Base change and Stacks Lemma 64.15.9 -/

namespace LinearMap

open MonoidAlgebra MonoidAlgebra.DiagonalTensor MonoidAlgebra.TrivialAction

section BaseChange

variable {A Λ G Γ : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] [Group G] [Monoid Γ]

/-- Base-change compatibility of the centralizer trace along an `A`-algebra `Λ` (possibly
noncommutative): the centralizer trace on `P ⊗[A] Λ` equals the image of the `A`-valued centralizer
trace of `P` in `Λ / [Λ, Λ]`. -/
theorem centralizerTrace_baseChange (ι : G →* Γ) (γ : Γ)
    [(ι.centralizerSubgroup γ).FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A Γ) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A Γ) P]
    [IsScalarTower A (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P), r • p = mapDomain ι r • p)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P] :
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P)
      (M := TrivialAction Λ) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P)
      (M := TrivialAction Λ) (G := G)).2
    centralizerTrace Λ ι γ (DiagonalTensor A Λ P (TrivialAction Λ))
        (DiagonalTensor.smul_eq_mapDomain ι hPG (TrivialAction.smul_eq_mapDomain ι)) =
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
        (algebraMap A Λ (centralizerScalarTrace A ι γ P hPG)) := by
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P)
    (M := TrivialAction Λ) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P)
    (M := TrivialAction Λ) (G := G)).2
  rw [centralizerTrace_diagonalTensor ι γ P hPG (TrivialAction Λ)
      (TrivialAction.smul_eq_mapDomain ι),
    TrivialAction.hattoriStallingsTrace_singleSMulEnd,
    TauCeti.cyclicQuotientSMul_mkQ, mul_one]

/-- Commutative base-change compatibility of `centralizerScalarTrace`. -/
theorem centralizerScalarTrace_baseChange {Λ : Type*} [CommRing Λ] [Algebra A Λ]
    (ι : G →* Γ) (γ : Γ) [(ι.centralizerSubgroup γ).FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A Γ) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A Γ) P]
    [IsScalarTower A (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P), r • p = mapDomain ι r • p)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P] :
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P)
      (M := TrivialAction Λ) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P)
      (M := TrivialAction Λ) (G := G)).2
    centralizerScalarTrace Λ ι γ (DiagonalTensor A Λ P (TrivialAction Λ))
        (DiagonalTensor.smul_eq_mapDomain ι hPG (TrivialAction.smul_eq_mapDomain ι)) =
      algebraMap A Λ (centralizerScalarTrace A ι γ P hPG) := by
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P)
    (M := TrivialAction Λ) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P)
    (M := TrivialAction Λ) (G := G)).2
  rw [centralizerScalarTrace_apply, centralizerTrace_baseChange ι γ P hPG,
    TauCeti.cyclicQuotientEquivSelf_mkQ]

end BaseChange

section Stacks64_15_9

variable {G Γ : Type*} [Group G] [Monoid Γ]

/-- **Stacks Lemma 64.15.9 (centralizer trace form).** Let `ℓ` be prime, `G` a finite group,
`ι : G →* Γ`, and `γ : Γ` such that `ℓ ^ (v + 1) ∤ |Z_γ|`. If two finite projective
`ZMod (ℓ ^ (n + v))[G]`-modules `P` and `Q` with compatible `Γ`-actions have equal
`ZMod (ℓ ^ (n + v))`-linear projective traces for `γ`, then their centralizer traces become equal
after reduction modulo `ℓ ^ n`. -/
theorem castHom_centralizerScalarTrace_eq_of_projectiveTrace_eq {ℓ n v : ℕ} (hℓ : ℓ.Prime)
    [Finite G] (ι : G →* Γ) (γ : Γ)
    (hnd : ¬ ℓ ^ (v + 1) ∣ Nat.card (ι.centralizerSubgroup γ))
    (P : Type*) [AddCommGroup P] [Module (ZMod (ℓ ^ (n + v))) P]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) Γ) P]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) Γ) P]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    (hPG : ∀ (r : MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) (p : P), r • p = mapDomain ι r • p)
    [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [Module.Projective (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    (Q : Type*) [AddCommGroup Q] [Module (ZMod (ℓ ^ (n + v))) Q]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) Γ) Q]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) Γ) Q]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    (hQG : ∀ (r : MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) (q : Q), r • q = mapDomain ι r • q)
    [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    [Module.Projective (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    (htr :
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) P).1
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) P).2
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) Q).1
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) Q).2
      projectiveTrace (ZMod (ℓ ^ (n + v))) P (singleSMulEnd (ZMod (ℓ ^ (n + v))) γ P) =
        projectiveTrace (ZMod (ℓ ^ (n + v))) Q (singleSMulEnd (ZMod (ℓ ^ (n + v))) γ Q)) :
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n))
        (centralizerScalarTrace (ZMod (ℓ ^ (n + v))) ι γ P hPG) =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n))
        (centralizerScalarTrace (ZMod (ℓ ^ (n + v))) ι γ Q hQG) := by
  have hP := projectiveTrace_single_eq_card_mul_centralizerScalarTrace ι γ P hPG
  have hQ := projectiveTrace_single_eq_card_mul_centralizerScalarTrace ι γ Q hQG
  have hmul :
      (Nat.card (ι.centralizerSubgroup γ) : ZMod (ℓ ^ (n + v))) *
          centralizerScalarTrace (ZMod (ℓ ^ (n + v))) ι γ P hPG =
        (Nat.card (ι.centralizerSubgroup γ) : ZMod (ℓ ^ (n + v))) *
          centralizerScalarTrace (ZMod (ℓ ^ (n + v))) ι γ Q hQG := by
    rw [← hP, ← hQ]
    exact htr
  exact ZMod.castHom_eq_of_mul_eq_of_not_pow_dvd hℓ hnd hmul

/-- **Stacks Lemma 64.15.9 (base-change form).** Under the hypotheses of
`castHom_centralizerScalarTrace_eq_of_projectiveTrace_eq`, the centralizer traces of `γ` on the
mod-`ℓ ^ n` base changes `P ⊗[ZMod (ℓ^(n+v))] ZMod (ℓ^n)` and `Q ⊗[ZMod (ℓ^(n+v))] ZMod (ℓ^n)`
are equal. -/
theorem centralizerScalarTrace_zmod_baseChange_eq_of_projectiveTrace_eq {ℓ n v : ℕ}
    (hℓ : ℓ.Prime) [Finite G] [Algebra (ZMod (ℓ ^ (n + v))) (ZMod (ℓ ^ n))]
    (ι : G →* Γ) (γ : Γ)
    (hnd : ¬ ℓ ^ (v + 1) ∣ Nat.card (ι.centralizerSubgroup γ))
    (P : Type*) [AddCommGroup P] [Module (ZMod (ℓ ^ (n + v))) P]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) Γ) P]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) Γ) P]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    (hPG : ∀ (r : MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) (p : P), r • p = mapDomain ι r • p)
    [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [Module.Projective (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    (Q : Type*) [AddCommGroup Q] [Module (ZMod (ℓ ^ (n + v))) Q]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) Γ) Q]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) Γ) Q]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    (hQG : ∀ (r : MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) (q : Q), r • q = mapDomain ι r • q)
    [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    [Module.Projective (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    (htr :
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) P).1
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) P).2
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) Q).1
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) Q).2
      projectiveTrace (ZMod (ℓ ^ (n + v))) P (singleSMulEnd (ZMod (ℓ ^ (n + v))) γ P) =
        projectiveTrace (ZMod (ℓ ^ (n + v))) Q (singleSMulEnd (ZMod (ℓ ^ (n + v))) γ Q)) :
    haveI := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := ZMod (ℓ ^ n))
      (P := P) (M := TrivialAction (ZMod (ℓ ^ n))) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := ZMod (ℓ ^ n))
      (P := P) (M := TrivialAction (ZMod (ℓ ^ n))) (G := G)).2
    haveI := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := ZMod (ℓ ^ n))
      (P := Q) (M := TrivialAction (ZMod (ℓ ^ n))) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := ZMod (ℓ ^ n))
      (P := Q) (M := TrivialAction (ZMod (ℓ ^ n))) (G := G)).2
    centralizerScalarTrace (ZMod (ℓ ^ n)) ι γ
        (DiagonalTensor (ZMod (ℓ ^ (n + v))) (ZMod (ℓ ^ n)) P (TrivialAction (ZMod (ℓ ^ n))))
        (DiagonalTensor.smul_eq_mapDomain ι hPG (TrivialAction.smul_eq_mapDomain ι)) =
      centralizerScalarTrace (ZMod (ℓ ^ n)) ι γ
        (DiagonalTensor (ZMod (ℓ ^ (n + v))) (ZMod (ℓ ^ n)) Q (TrivialAction (ZMod (ℓ ^ n))))
        (DiagonalTensor.smul_eq_mapDomain ι hQG (TrivialAction.smul_eq_mapDomain ι)) := by
  have := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := ZMod (ℓ ^ n))
    (P := P) (M := TrivialAction (ZMod (ℓ ^ n))) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := ZMod (ℓ ^ n))
    (P := P) (M := TrivialAction (ZMod (ℓ ^ n))) (G := G)).2
  have := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := ZMod (ℓ ^ n))
    (P := Q) (M := TrivialAction (ZMod (ℓ ^ n))) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := ZMod (ℓ ^ n))
    (P := Q) (M := TrivialAction (ZMod (ℓ ^ n))) (G := G)).2
  rw [centralizerScalarTrace_baseChange ι γ P hPG, centralizerScalarTrace_baseChange ι γ Q hQG]
  have hmap : algebraMap (ZMod (ℓ ^ (n + v))) (ZMod (ℓ ^ n)) =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n)) :=
    Subsingleton.elim _ _
  rw [hmap]
  exact castHom_centralizerScalarTrace_eq_of_projectiveTrace_eq hℓ ι γ hnd P hPG Q hQG htr

end Stacks64_15_9

end LinearMap

/-! ### Section 4: Diagonal coinvariant coefficient descent (Stacks 64.15.8 + 64.15.9) -/

namespace TauCeti

namespace MonoidExtension

open _root_.MonoidAlgebra _root_.MonoidAlgebra.DiagonalTensor

/-- **Stacks Lemmas 64.15.8 + 64.15.9.** Let `E : MonoidExtension G Γ` with `G` finite and
`ℓ ^ (v + 1) ∤ |G|` for a prime `ℓ`, and let `Λ` be an arbitrary (possibly noncommutative)
`ZMod (ℓ ^ n)`-algebra equipped with the induced `ZMod (ℓ ^ (n + v))`-algebra structure. If two
finite projective `ZMod (ℓ ^ (n + v))[G]`-modules `P` and `Q` with `E.monoid`-actions have equal
projective traces for every `γ ∈ E.fiber k`, then for every finite projective `Λ`-module `M` with
`E.monoid`-action, the degree-`k` actions on `(M ⊗ P)_G` and `(M ⊗ Q)_G` have the same
Hattori–Stallings trace in `Λ / [Λ, Λ]`. -/
theorem hattoriStallingsTrace_diagonalTensor_eq_of_projectiveTrace_eq
    {G Γ : Type*} [Group G] [Group Γ] [Finite G] (E : MonoidExtension G Γ)
    {ℓ n v : ℕ} (hℓ : ℓ.Prime) (hndG : ¬ ℓ ^ (v + 1) ∣ Nat.card G)
    {Λ : Type*} [Ring Λ] [Algebra (ZMod (ℓ ^ (n + v))) (ZMod (ℓ ^ n))]
    [Algebra (ZMod (ℓ ^ n)) Λ] [Algebra (ZMod (ℓ ^ (n + v))) Λ]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (ZMod (ℓ ^ n)) Λ]
    (k : ℕ)
    (P : Type*) [AddCommGroup P] [Module (ZMod (ℓ ^ (n + v))) P]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) E.monoid) P]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) E.monoid) P]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    (hPG : ∀ (r : MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) (p : P),
      r • p = mapDomain E.monoidIncl r • p)
    [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    [Module.Projective (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) P]
    (Q : Type*) [AddCommGroup Q] [Module (ZMod (ℓ ^ (n + v))) Q]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) E.monoid) Q]
    [Module (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) E.monoid) Q]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    (hQG : ∀ (r : MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) (q : Q),
      r • q = mapDomain E.monoidIncl r • q)
    [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    [Module.Projective (MonoidAlgebra (ZMod (ℓ ^ (n + v))) G) Q]
    (M : Type*) [AddCommGroup M] [Module (ZMod (ℓ ^ (n + v))) M] [Module Λ M]
    [IsScalarTower (ZMod (ℓ ^ (n + v))) Λ M]
    [Module (MonoidAlgebra Λ E.monoid) M] [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) M]
    [Module (MonoidAlgebra Λ G) M] [IsScalarTower Λ (MonoidAlgebra Λ G) M]
    (hMG : ∀ (r : MonoidAlgebra Λ G) (m : M), r • m = mapDomain E.monoidIncl r • m)
    [Module.Finite Λ M] [Module.Projective Λ M]
    (htr : ∀ γ : E.fiber k,
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) P).1
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) P).2
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) Q).1
      haveI := (MonoidAlgebra.finite_projective_of_monoidAlgebra
        (Λ := ZMod (ℓ ^ (n + v))) (G := G) Q).2
      LinearMap.projectiveTrace (ZMod (ℓ ^ (n + v))) P
          (singleSMulEnd (ZMod (ℓ ^ (n + v))) γ.1 P) =
        LinearMap.projectiveTrace (ZMod (ℓ ^ (n + v))) Q
          (singleSMulEnd (ZMod (ℓ ^ (n + v))) γ.1 Q)) :
    haveI := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := Λ)
      (P := P) (M := M) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := Λ)
      (P := P) (M := M) (G := G)).2
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ P M)).1
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ P M)).2
    haveI := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := Λ)
      (P := Q) (M := M) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := Λ)
      (P := Q) (M := M) (G := G)).2
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ Q M)).1
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ Q M)).2
    LinearMap.hattoriStallingsTrace Λ
        (Coinvariants Λ G (DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ P M))
        (E.coinvariantsAction Λ k (DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ P M)
          (DiagonalTensor.smul_eq_mapDomain E.monoidIncl hPG hMG)) =
      LinearMap.hattoriStallingsTrace Λ
        (Coinvariants Λ G (DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ Q M))
        (E.coinvariantsAction Λ k (DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ Q M)
          (DiagonalTensor.smul_eq_mapDomain E.monoidIncl hQG hMG)) := by
  have := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := Λ)
    (P := P) (M := M) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := Λ)
    (P := P) (M := M) (G := G)).2
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G)
    (P := DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ P M)).1
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G)
    (P := DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ P M)).2
  have := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := Λ)
    (P := Q) (M := M) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := ZMod (ℓ ^ (n + v))) (Λ := Λ)
    (P := Q) (M := M) (G := G)).2
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G)
    (P := DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ Q M)).1
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G)
    (P := DiagonalTensor (ZMod (ℓ ^ (n + v))) Λ Q M)).2
  rw [E.hattoriStallingsTrace_coinvariantsAction_diagonalTensor k P hPG M hMG,
    E.hattoriStallingsTrace_coinvariantsAction_diagonalTensor k Q hQG M hMG]
  refine finsum_congr fun c ↦ ?_
  obtain ⟨γ, rfl⟩ := Quotient.exists_rep c
  rw [E.centralizerScalarTraceClass_mk, E.centralizerScalarTraceClass_mk]
  have hndZ : ¬ ℓ ^ (v + 1) ∣ Nat.card (E.monoidIncl.centralizerSubgroup γ.1) := fun h ↦
    hndG (h.trans (Subgroup.card_subgroup_dvd_card (E.monoidIncl.centralizerSubgroup γ.1)))
  have hcast := LinearMap.castHom_centralizerScalarTrace_eq_of_projectiveTrace_eq hℓ E.monoidIncl
    γ.1 hndZ P hPG Q hQG (htr γ)
  have hmap : algebraMap (ZMod (ℓ ^ (n + v))) (ZMod (ℓ ^ n)) =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n v)) (ZMod (ℓ ^ n)) :=
    Subsingleton.elim _ _
  have halg :
      algebraMap (ZMod (ℓ ^ (n + v))) Λ
          (LinearMap.centralizerScalarTrace (ZMod (ℓ ^ (n + v))) E.monoidIncl γ.1 P hPG) =
        algebraMap (ZMod (ℓ ^ (n + v))) Λ
          (LinearMap.centralizerScalarTrace (ZMod (ℓ ^ (n + v))) E.monoidIncl γ.1 Q hQG) := by
    rw [IsScalarTower.algebraMap_apply (ZMod (ℓ ^ (n + v))) (ZMod (ℓ ^ n)) Λ,
      IsScalarTower.algebraMap_apply (ZMod (ℓ ^ (n + v))) (ZMod (ℓ ^ n)) Λ, hmap, hcast]
  obtain ⟨r, hr⟩ :=
    (commutatorSubmodule ℤ Λ).mkQ_surjective (E.hattoriStallingsTraceClass Λ k M ⟦γ⟧)
  rw [← hr, cyclicQuotientSMul_mkQ, cyclicQuotientSMul_mkQ, halg]

end MonoidExtension

end TauCeti

/-! ### Section 5: Non-vacuity and instance-diamond checks -/

section Examples

open MonoidAlgebra MonoidAlgebra.DiagonalTensor MonoidAlgebra.TrivialAction

/-- `DiagonalTensor ℤ ℤ P M` has no `Module ℤ` diamond with `AddCommGroup.toIntModule`. -/
example (P M : Type*) [AddCommGroup P] [AddCommGroup M] :
    (inferInstance : Module ℤ (DiagonalTensor ℤ ℤ P M)) =
      AddCommGroup.toIntModule (DiagonalTensor ℤ ℤ P M) :=
  rfl

/-- `TrivialAction ℤ` has no `Module ℤ` diamond with `AddCommGroup.toIntModule`. -/
example :
    (inferInstance : Module ℤ (TrivialAction ℤ)) =
      AddCommGroup.toIntModule (TrivialAction ℤ) :=
  rfl

/-- Non-vacuity with `|G| = 0` in the coefficient ring and `M` non-projective over `A`:
`A = ZMod 4`, `Λ = ZMod 2`, `G = Multiplicative (ZMod 2)` (so `|G| = 2`), `P = A[G]`, and
`M = TrivialAction (ZMod 2)` (not projective over `ZMod 4`, projective over `ZMod 2`). -/
example [Algebra (ZMod 4) (ZMod 2)] :
    let G := Multiplicative (ZMod 2)
    Module.Finite (MonoidAlgebra (ZMod 2) G)
        (DiagonalTensor (ZMod 4) (ZMod 2) (MonoidAlgebra (ZMod 4) G) (TrivialAction (ZMod 2))) ∧
      Module.Projective (MonoidAlgebra (ZMod 2) G)
        (DiagonalTensor (ZMod 4) (ZMod 2) (MonoidAlgebra (ZMod 4) G) (TrivialAction (ZMod 2))) := by
  dsimp only
  exact DiagonalTensor.finite_projective (A := ZMod 4)

/-- Noncommutative non-vacuity of Stacks Lemma 64.15.7 with `A = ZMod 2`,
`Λ = Matrix (Fin 2) (Fin 2) (ZMod 2)`, and `G = Γ = Multiplicative (ZMod 2)` (`|G| = 0` in `A`). -/
example (γ : Multiplicative (ZMod 2)) :
    let A := ZMod 2
    let Λ := Matrix (Fin 2) (Fin 2) (ZMod 2)
    let G := Multiplicative (ZMod 2)
    let P := MonoidAlgebra A G
    let M := TrivialAction Λ
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).2
    LinearMap.centralizerTrace Λ (MonoidHom.id G) γ (DiagonalTensor A Λ P M)
        (DiagonalTensor.smul_eq_mapDomain (MonoidHom.id G)
          (fun _ _ ↦ by simp) (TrivialAction.smul_eq_mapDomain (MonoidHom.id G))) =
      TauCeti.cyclicQuotientSMul A Λ
        (LinearMap.centralizerScalarTrace A (MonoidHom.id G) γ P (fun _ _ ↦ by simp))
        (LinearMap.hattoriStallingsTrace Λ M (singleSMulEnd Λ γ M)) :=
  LinearMap.centralizerTrace_diagonalTensor (MonoidHom.id (Multiplicative (ZMod 2))) γ
    (MonoidAlgebra (ZMod 2) (Multiplicative (ZMod 2))) (fun _ _ ↦ by simp)
    (TrivialAction (Matrix (Fin 2) (Fin 2) (ZMod 2)))
    (TrivialAction.smul_eq_mapDomain (MonoidHom.id (Multiplicative (ZMod 2))))

end Examples
