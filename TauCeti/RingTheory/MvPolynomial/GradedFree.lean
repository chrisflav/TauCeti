/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import TauCeti.Algebra.Category.GradedModuleCat.Retract
public import TauCeti.Algebra.Module.GradedModule.Free
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Graded freeness of projective modules and retracts over positively weighted polynomial rings

Give `MvPolynomial σ R` its `ℤ`-grading `weightedHomogeneousSubmodule R w` from strictly positive
weights `w : σ → ℤ` (`∀ i, 0 < w i`). Then every negative-weight piece vanishes, and the
weight-zero piece is the isomorphic copy of `R` embedded as constant polynomials.

When the coefficient ring `R` is a principal ideal domain (for instance `R = ℤ`), `MvPolynomial σ R`
satisfies the hypotheses of the connected graded projective freeness theorem:

* every finitely generated projective graded `MvPolynomial σ R`-module `P` — and in particular every
  graded module that is an `MvPolynomial σ R`-linear retract of `J → MvPolynomial σ R` for finite
  `J` — admits a finite homogeneous `MvPolynomial σ R`-basis;
* the image `LinearMap.range p` of any degree-zero idempotent endomorphism `p` of
  `J → MvPolynomial σ R` (with shifts `s : J → ℤ`) admits a finite homogeneous
  `MvPolynomial σ R`-basis, and `p` splits homogeneously as `ι ∘ₗ π = p`, `π ∘ₗ ι = id` through
  `Fin n → MvPolynomial σ R`;
* categorically in `GradedModuleCat (weightedHomogeneousSubmodule R w)`, every retract (and every
  idempotent endomorphism) of a finite biproduct of shifted regular modules is isomorphic to (and
  splits through) a finite biproduct of shifted regular modules.

The variable set `σ` may be arbitrary (including empty, such as `Fin 0`, where `MvPolynomial σ R`
is concentrated in degree zero and isomorphic to `R`).

## Main results

* `MvPolynomial.exists_homogeneous_basis_of_projective` and
  `MvPolynomial.exists_homogeneous_basis_of_retract_pi`: finitely generated projective graded
  modules and graded retracts of finite products over `MvPolynomial σ R` have finite homogeneous
  bases when `R` is a PID and `∀ i, 0 < w i`.
* `MvPolynomial.exists_homogeneous_basis_range_idempotent`: the image of a degree-zero idempotent on
  `J → MvPolynomial σ R` has a finite homogeneous basis.
* `MvPolynomial.exists_homogeneous_split_idempotent`: explicit homogeneous factorization
  `π.comp ι = id`, `ι.comp π = p` through `Fin n → MvPolynomial σ R`.
* `MvPolynomial.exists_iso_biproduct_shift_of_retract` and
  `MvPolynomial.exists_split_biproduct_shift_of_idempotent`: the categorical counterparts in
  `GradedModuleCat (weightedHomogeneousSubmodule R w)`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open TauCeti

namespace MvPolynomial

universe uR uσ uJ uM

section PID

variable {R : Type uR} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {σ : Type uσ} {w : σ → ℤ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- **Graded freeness of finitely generated projective modules over a positively weighted polynomial
ring over a PID.** Let `R` be a principal ideal domain and `w : σ → ℤ` be strictly positive weights
(`∀ i, 0 < w i`). Every finitely generated projective graded `MvPolynomial σ R`-module `P` has a
finite homogeneous `MvPolynomial σ R`-basis. -/
theorem exists_homogeneous_basis_of_projective (hw : ∀ i, 0 < w i)
    {P : Type uM} [AddCommGroup P] [Module R P] [Module (MvPolynomial σ R) P]
    [IsScalarTower R (MvPolynomial σ R) P]
    [Module.Finite (MvPolynomial σ R) P] [Module.Projective (MvPolynomial σ R) P]
    (G : InternalGrading R P ℤ) [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) G.piece] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (MvPolynomial σ R) P) (d : Fin n → ℤ),
      ∀ i, b i ∈ G.piece (d i) :=
  G.exists_homogeneous_basis_of_projective (weightedHomogeneousSubmodule R w)
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero (fun i ↦ (hw i).le) hm)
    (weightedHomogeneousSubmodule_zero_le_range hw)
    (algebraMap_eq R σ ▸ MvPolynomial.C_injective σ R)

/-- **Graded freeness of retracts over a positively weighted polynomial ring over a PID.** Let
`R` be a principal ideal domain and `w : σ → ℤ` be strictly positive weights (`∀ i, 0 < w i`).
Every graded `MvPolynomial σ R`-module `P` admitting a linear inclusion
`ι₀ : P →ₗ[MvPolynomial σ R] (J → MvPolynomial σ R)` with a linear left inverse `π₀` for a finite
index type `J` has a finite homogeneous `MvPolynomial σ R`-basis. -/
theorem exists_homogeneous_basis_of_retract_pi (hw : ∀ i, 0 < w i)
    {J : Type uJ} [Finite J]
    {P : Type uM} [AddCommGroup P] [Module R P] [Module (MvPolynomial σ R) P]
    [IsScalarTower R (MvPolynomial σ R) P]
    (G : InternalGrading R P ℤ) [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) G.piece]
    (ι₀ : P →ₗ[MvPolynomial σ R] (J → MvPolynomial σ R))
    (π₀ : (J → MvPolynomial σ R) →ₗ[MvPolynomial σ R] P)
    (hsplit : π₀ ∘ₗ ι₀ = LinearMap.id) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (MvPolynomial σ R) P) (d : Fin n → ℤ),
      ∀ i, b i ∈ G.piece (d i) :=
  G.exists_homogeneous_basis_of_retract_pi (weightedHomogeneousSubmodule R w)
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero (fun i ↦ (hw i).le) hm)
    (weightedHomogeneousSubmodule_zero_le_range hw)
    (algebraMap_eq R σ ▸ MvPolynomial.C_injective σ R) ι₀ π₀ hsplit

/-- **Homogeneous basis for the image of a degree-zero idempotent over `MvPolynomial σ R`.** Let
`R` be a principal ideal domain and `w : σ → ℤ` be strictly positive weights. For any finite index
type `J`, shifts `s : J → ℤ`, and degree-zero idempotent endomorphism `p` of
`J → MvPolynomial σ R`, the image `LinearMap.range p` admits a finite homogeneous
`MvPolynomial σ R`-basis `b` of degrees `d : Fin n → ℤ`, meaning
`(b i).val j ∈ weightedHomogeneousSubmodule R w (d i - s j)` for all `i` and `j`. -/
theorem exists_homogeneous_basis_range_idempotent (hw : ∀ i, 0 < w i)
    {J : Type uJ} [Finite J] (s : J → ℤ)
    (p : (J → MvPolynomial σ R) →ₗ[MvPolynomial σ R] (J → MvPolynomial σ R))
    (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → MvPolynomial σ R),
      (∀ j, v j ∈ weightedHomogeneousSubmodule R w (q - s j)) →
      ∀ j, p v j ∈ weightedHomogeneousSubmodule R w (q - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (MvPolynomial σ R) (LinearMap.range p)) (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ weightedHomogeneousSubmodule R w (d i - s j) :=
  InternalGrading.exists_homogeneous_basis_range_idempotent (weightedHomogeneousSubmodule R w) s
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero (fun i ↦ (hw i).le) hm)
    (weightedHomogeneousSubmodule_zero_le_range hw)
    (algebraMap_eq R σ ▸ MvPolynomial.C_injective σ R) p hp hhom

/-- **Explicit homogeneous splitting of a degree-zero idempotent over `MvPolynomial σ R`.** Under
the hypotheses of `exists_homogeneous_basis_range_idempotent`, `p` factors as `ι.comp π = p` and
`π.comp ι = LinearMap.id` through a finite shifted product `Fin n → MvPolynomial σ R` of degrees
`d : Fin n → ℤ`, with both `ι` and `π` preserving weighted degrees. -/
theorem exists_homogeneous_split_idempotent (hw : ∀ i, 0 < w i)
    {J : Type uJ} [Finite J] (s : J → ℤ)
    (p : (J → MvPolynomial σ R) →ₗ[MvPolynomial σ R] (J → MvPolynomial σ R))
    (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → MvPolynomial σ R),
      (∀ j, v j ∈ weightedHomogeneousSubmodule R w (q - s j)) →
      ∀ j, p v j ∈ weightedHomogeneousSubmodule R w (q - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R] (J → MvPolynomial σ R))
      (π : (J → MvPolynomial σ R) →ₗ[MvPolynomial σ R] (Fin n → MvPolynomial σ R)),
      π.comp ι = LinearMap.id ∧ ι.comp π = p ∧
      (∀ (q : ℤ) (u : Fin n → MvPolynomial σ R),
        (∀ i, u i ∈ weightedHomogeneousSubmodule R w (q - d i)) →
        ∀ j, ι u j ∈ weightedHomogeneousSubmodule R w (q - s j)) ∧
      (∀ (q : ℤ) (v : J → MvPolynomial σ R),
        (∀ j, v j ∈ weightedHomogeneousSubmodule R w (q - s j)) →
        ∀ i, π v i ∈ weightedHomogeneousSubmodule R w (q - d i)) :=
  InternalGrading.exists_homogeneous_split_idempotent (weightedHomogeneousSubmodule R w) s
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero (fun i ↦ (hw i).le) hm)
    (weightedHomogeneousSubmodule_zero_le_range hw)
    (algebraMap_eq R σ ▸ MvPolynomial.C_injective σ R) p hp hhom

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- Every retract of a finite biproduct of shifted regular `MvPolynomial σ R`-modules in
`GradedModuleCat (weightedHomogeneousSubmodule R w)` is again isomorphic to a finite biproduct of
shifted regular modules, when `R` is a PID and `∀ i, 0 < w i`. -/
theorem exists_iso_biproduct_shift_of_retract (hw : ∀ i, 0 < w i)
    {J : Type} [Finite J] (s : J → ℤ)
    {P : GradedModuleCat.{max uR uσ} (weightedHomogeneousSubmodule R w)}
    (h : CategoryTheory.Retract P
      (⨁ fun j : J ↦
        (GradedModuleCat.regular (𝒜 := weightedHomogeneousSubmodule R w)).shiftObj (s j))) :
    ∃ (n : ℕ) (d : Fin n → ℤ),
      Nonempty (P ≅ ⨁ fun i : Fin n ↦
        (GradedModuleCat.regular (𝒜 := weightedHomogeneousSubmodule R w)).shiftObj (d i)) :=
  GradedModuleCat.exists_iso_biproduct_shift_of_retract (weightedHomogeneousSubmodule R w) s
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero (fun i ↦ (hw i).le) hm)
    (weightedHomogeneousSubmodule_zero_le_range hw)
    (algebraMap_eq R σ ▸ MvPolynomial.C_injective σ R) h

/-- Every degree-zero idempotent endomorphism of a finite biproduct of shifted regular
`MvPolynomial σ R`-modules splits through a finite biproduct of shifted regular modules, when `R`
is a PID and `∀ i, 0 < w i`. -/
theorem exists_split_biproduct_shift_of_idempotent (hw : ∀ i, 0 < w i)
    {J : Type} [Finite J] (s : J → ℤ)
    (e : (⨁ fun j : J ↦
        (GradedModuleCat.regular (𝒜 := weightedHomogeneousSubmodule R w)).shiftObj (s j)) ⟶
      ⨁ fun j : J ↦
        (GradedModuleCat.regular (𝒜 := weightedHomogeneousSubmodule R w)).shiftObj (s j))
    (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (⨁ fun i : Fin n ↦
          (GradedModuleCat.regular (𝒜 := weightedHomogeneousSubmodule R w)).shiftObj (d i)) ⟶
        ⨁ fun j : J ↦
          (GradedModuleCat.regular (𝒜 := weightedHomogeneousSubmodule R w)).shiftObj (s j))
      (π : (⨁ fun j : J ↦
          (GradedModuleCat.regular (𝒜 := weightedHomogeneousSubmodule R w)).shiftObj (s j)) ⟶
        ⨁ fun i : Fin n ↦
          (GradedModuleCat.regular (𝒜 := weightedHomogeneousSubmodule R w)).shiftObj (d i)),
      ι ≫ π = 𝟙 _ ∧ π ≫ ι = e :=
  GradedModuleCat.exists_split_biproduct_shift_of_idempotent (weightedHomogeneousSubmodule R w) s
    (fun _ hm ↦ weightedHomogeneousSubmodule_eq_bot_of_lt_zero (fun i ↦ (hw i).le) hm)
    (weightedHomogeneousSubmodule_zero_le_range hw)
    (algebraMap_eq R σ ▸ MvPolynomial.C_injective σ R) e he

end PID

section Examples

attribute [local instance] MvPolynomial.weightedGradedAlgebra

-- Specialization to integral polynomial rings with even positive weights `2 * (i + 1)` (including
-- `N = 0`).
example (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → MvPolynomial (Fin N) ℤ) →ₗ[MvPolynomial (Fin N) ℤ]
      (Fin m → MvPolynomial (Fin N) ℤ))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : Fin m → MvPolynomial (Fin N) ℤ),
      (∀ j, v j ∈ weightedHomogeneousSubmodule ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ))
        (d - s j)) →
      ∀ j, p v j ∈ weightedHomogeneousSubmodule ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ))
        (d - s j)) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (MvPolynomial (Fin N) ℤ) (LinearMap.range p))
      (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈
        weightedHomogeneousSubmodule ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ)) (d i - s j) :=
  exists_homogeneous_basis_range_idempotent (fun _ ↦ by omega) s p hp hhom

-- Check 1a: For `p = 0`, the image has the empty basis (`n = 0`).
example (N m : ℕ) (s : Fin m → ℤ) :
    let A := MvPolynomial (Fin N) ℤ
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) A (LinearMap.range (0 : (Fin m → A) →ₗ[A] (Fin m → A))))
      (d : Fin n → ℤ),
      n = 0 ∧ ∀ i j, (b i).val j ∈
        weightedHomogeneousSubmodule ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ)) (d i - s j) := by
  intro A
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent (R := ℤ)
    (w := fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ)) (fun _ ↦ by omega) s
    (0 : (Fin m → A) →ₗ[A] (Fin m → A)) (LinearMap.zero_comp 0)
    (fun _ _ _ _ ↦ Submodule.zero_mem _)
  refine ⟨n, b, d, ?_, hb⟩
  by_contra hn
  have i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have : Subsingleton (LinearMap.range (0 : (Fin m → A) →ₗ[A] (Fin m → A))) := by
    rw [LinearMap.range_zero]
    infer_instance
  exact b.ne_zero i₀ (Subsingleton.elim _ _)

-- Helper: any homogeneous unit of a positively weighted integral polynomial ring has degree `0`.
private theorem eq_zero_of_isUnit_of_mem_weightedHomogeneous {N : ℕ}
    {u v : MvPolynomial (Fin N) ℤ} (huv : u * v = 1) {k : ℤ}
    (hu : u ∈ weightedHomogeneousSubmodule ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ)) k) :
    k = 0 := by
  have hu0 : u ≠ 0 := left_ne_zero_of_mul (huv.symm ▸ one_ne_zero)
  rcases lt_trichotomy k 0 with hlt | rfl | hgt
  · have hbot := weightedHomogeneousSubmodule_eq_bot_of_lt_zero (R := ℤ)
      (w := fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ)) (fun _ ↦ by omega) hlt
    exact False.elim (hu0 ((Submodule.mem_bot ℤ).mp (hbot ▸ hu)))
  · rfl
  · have hu_hom : IsWeightedHomogeneous (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ)) u k :=
      (mem_weightedHomogeneousSubmodule ℤ _ k u).mp hu
    have hev := congrArg (eval₂Hom (RingHom.id ℤ) (fun _ : Fin N ↦ (0 : ℤ))) huv
    rw [map_mul, map_one, coe_eval₂Hom,
      hu_hom.eval₂_eq_zero (by omega) _ (fun _ _ ↦ rfl), zero_mul] at hev
    exact False.elim (zero_ne_one hev)

-- Check 1b: For `p = id` on a rank-one summand of shift `3`, any homogeneous basis produced has
-- rank `1` and basis vector of degree `3`.
example (N : ℕ) :
    let A := MvPolynomial (Fin N) ℤ
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) A (LinearMap.range (LinearMap.id : (Fin 1 → A) →ₗ[A] (Fin 1 → A))))
      (d : Fin n → ℤ),
      ∃ hn : n = 1, d (hn ▸ 0) = 3 ∧ ∀ i j, (b i).val j ∈
        weightedHomogeneousSubmodule ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ))
          (d i - ![3] j) := by
  intro A
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent (R := ℤ)
    (w := fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ)) (fun _ ↦ by omega) ![3]
    (LinearMap.id : (Fin 1 → A) →ₗ[A] (Fin 1 → A)) (LinearMap.id_comp LinearMap.id)
    (fun _ _ hv ↦ hv)
  have eRange : LinearMap.range (LinearMap.id : (Fin 1 → A) →ₗ[A] (Fin 1 → A)) ≃ₗ[A] (Fin 1 → A) :=
    LinearEquiv.ofTop _ LinearMap.range_id
  have hn : n = 1 := by
    simpa using Fintype.card_eq.mpr ⟨(b.map eRange).indexEquiv (Pi.basisFun A (Fin 1))⟩
  subst hn
  refine ⟨1, b, d, rfl, ?_, hb⟩
  dsimp only
  let e1 : LinearMap.range (LinearMap.id : (Fin 1 → A) →ₗ[A] (Fin 1 → A)) :=
    ⟨fun _ ↦ 1, ⟨fun _ ↦ 1, rfl⟩⟩
  have hcomb := b.sum_repr e1
  rw [Fin.sum_univ_one] at hcomb
  have hval := congrFun (congrArg Subtype.val hcomb) 0
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, e1] at hval
  have hk : d 0 - 3 = 0 :=
    eq_zero_of_isUnit_of_mem_weightedHomogeneous (mul_comm _ _ |>.trans hval) (hb 0 0)
  omega

-- Check 2: For `p = diag(1, 0)` on shifts `![a, b]`, the image has homogeneous basis `![1, 0]` of
-- degree `a`, independently of `b`.
example (N : ℕ) (a b : ℤ) :
    let A := MvPolynomial (Fin N) ℤ
    let p : (Fin 2 → A) →ₗ[A] (Fin 2 → A) :=
      (LinearMap.single A (fun _ : Fin 2 ↦ A) 0).comp (LinearMap.proj 0)
    p.comp p = p ∧
      (∀ (q : ℤ) (v : Fin 2 → A),
        (∀ j, v j ∈ weightedHomogeneousSubmodule ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ))
          (q - ![a, b] j)) →
        ∀ j, p v j ∈ weightedHomogeneousSubmodule ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ))
          (q - ![a, b] j)) ∧
      ∃ (B : Module.Basis (Fin 1) A (LinearMap.range p)),
        (B 0).val = ![1, 0] ∧ ∀ j, (B 0).val j ∈
          weightedHomogeneousSubmodule ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ))
            (a - ![a, b] j) := by
  intro A p
  refine ⟨LinearMap.ext fun v ↦ funext fun j ↦ by fin_cases j <;> simp [p],
    fun q v hv j ↦ ?_, ?_⟩
  · fin_cases j
    · simpa [p] using hv 0
    · simp [p]
  · let f : A →ₗ[A] LinearMap.range p :=
      p.rangeRestrict.comp (LinearMap.single A (fun _ : Fin 2 ↦ A) 0)
    let g : LinearMap.range p →ₗ[A] A :=
      (LinearMap.proj 0 : (Fin 2 → A) →ₗ[A] A).comp (LinearMap.range p).subtype
    have hfg : f.comp g = LinearMap.id := LinearMap.ext fun ⟨y, v, hv⟩ ↦
      Subtype.ext <| funext fun j ↦ by fin_cases j <;> simp [f, g, ← hv, p]
    have hgf : g.comp f = LinearMap.id := LinearMap.ext fun r ↦ by simp [f, g, p]
    let B : Module.Basis (Fin 1) A (LinearMap.range p) :=
      (Module.Basis.singleton (Fin 1) A).map (LinearEquiv.ofLinearMap f g hfg hgf)
    have hB0 : (B 0).val = ![1, 0] := funext fun j ↦ by
      fin_cases j <;> simp [B, f, p]
    refine ⟨B, hB0, fun j ↦ ?_⟩
    rw [hB0]
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, sub_self]
      exact isWeightedHomogeneous_one ℤ (fun i : Fin N ↦ 2 * ((i : ℕ) + 1 : ℤ))
    · simp

-- Check 3: For `N + 1` variables, shifts `![2, 0]`, and `p(x, y) = (x, X 0 * x)`, `p` is a
-- degree-zero idempotent and its image has homogeneous basis `![1, X 0]` of degree `2`.
example (N : ℕ) :
    let A := MvPolynomial (Fin (N + 1)) ℤ
    let w : Fin (N + 1) → ℤ := fun i ↦ 2 * ((i : ℕ) + 1 : ℤ)
    let p : (Fin 2 → A) →ₗ[A] (Fin 2 → A) :=
      (LinearMap.single A (fun _ : Fin 2 ↦ A) 0 +
        (LinearMap.single A (fun _ : Fin 2 ↦ A) 1).comp (LinearMap.mulLeft A (X 0))).comp
        (LinearMap.proj 0)
    p.comp p = p ∧
      (∀ (q : ℤ) (v : Fin 2 → A),
        (∀ j, v j ∈ weightedHomogeneousSubmodule ℤ w (q - ![2, 0] j)) →
        ∀ j, p v j ∈ weightedHomogeneousSubmodule ℤ w (q - ![2, 0] j)) ∧
      ∃ (B : Module.Basis (Fin 1) A (LinearMap.range p)),
        (B 0).val = ![1, X 0] ∧ ∀ j, (B 0).val j ∈
          weightedHomogeneousSubmodule ℤ w (2 - ![2, 0] j) := by
  intro A w p
  refine ⟨LinearMap.ext fun v ↦ funext fun j ↦ by fin_cases j <;> simp [p],
    fun q v hv j ↦ ?_, ?_⟩
  · fin_cases j
    · simpa [p] using hv 0
    · have hX : IsWeightedHomogeneous w (X 0 : A) 2 := by
        simpa [w] using isWeightedHomogeneous_X ℤ w 0
      have hv0 : IsWeightedHomogeneous w (v 0) (q - 2) :=
        (mem_weightedHomogeneousSubmodule ℤ w (q - 2) (v 0)).mp (hv 0)
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero, p,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply, LinearMap.add_apply,
        LinearMap.coe_single, LinearMap.mulLeft_apply, Pi.add_apply,
        Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), Pi.single_eq_same, zero_add]
      have hdeg : 2 + (q - 2) = q := by omega
      exact (mem_weightedHomogeneousSubmodule ℤ w q _).mpr (hdeg ▸ hX.mul hv0)
  · let f : A →ₗ[A] LinearMap.range p :=
      p.rangeRestrict.comp (LinearMap.single A (fun _ : Fin 2 ↦ A) 0)
    let g : LinearMap.range p →ₗ[A] A :=
      (LinearMap.proj 0 : (Fin 2 → A) →ₗ[A] A).comp (LinearMap.range p).subtype
    have hfg : f.comp g = LinearMap.id := LinearMap.ext fun ⟨y, v, hv⟩ ↦
      Subtype.ext <| funext fun j ↦ by fin_cases j <;> simp [f, g, ← hv, p]
    have hgf : g.comp f = LinearMap.id := LinearMap.ext fun r ↦ by simp [f, g, p]
    let B : Module.Basis (Fin 1) A (LinearMap.range p) :=
      (Module.Basis.singleton (Fin 1) A).map (LinearEquiv.ofLinearMap f g hfg hgf)
    have hB0 : (B 0).val = ![1, X 0] := funext fun j ↦ by
      fin_cases j <;> simp [B, f, p]
    refine ⟨B, hB0, fun j ↦ ?_⟩
    rw [hB0]
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, sub_self]
      exact isWeightedHomogeneous_one ℤ w
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero]
      exact (mem_weightedHomogeneousSubmodule ℤ w 2 _).mpr
        (by simpa [w] using isWeightedHomogeneous_X ℤ w 0)

end Examples

end MvPolynomial
