/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.StarModuleCat.ComplexDescent
public import TauCeti.Algebra.MvPolynomial.Conjugation
public import TauCeti.Geometry.Variational.PolynomialJet.Basic

/-!
# Conjugation, real descent, and field evaluations on polynomial jets

Over a commutative star semiring `R`, a map `σ : α → β` of field labels induces the
coefficient-and-generator conjugation `PolynomialJet.conj σ : PolynomialJet R ι α →+*
PolynomialJet R ι β`: it conjugates scalar constants by `starRingEnd R`, fixes every base
coordinate `X (Sum.inl j)`, and sends each field-jet coordinate `X (Sum.inr (a, I))` to
`X (Sum.inr (σ a, I))` at the same symmetric multi-index `I`. When `σ : α → α` is involutive,
`PolynomialJet.conj σ` is an involutive `starRingEnd R`-semilinear ring endomorphism; for `σ = id`
it describes real-indexed fields, while for `σ = Sum.swap` on `β ⊕ β` it swaps paired field and
conjugate-field generators `(ψ, ψ̄)`.

Because `PolynomialJet.conj σ` preserves every multi-index `I`, it preserves each finite-order
subalgebra `PolynomialJet.stage R ι α r` (`PolynomialJet.stageConj`) and commutes with both
`PolynomialJet.totalDeriv` and `PolynomialJet.stageDeriv`. Under `MvPolynomial.aeval` into a
commutative star `R`-algebra `A`, conjugation commutes with `star` on every jet expression if and
only if the assigned base coordinates are self-adjoint and `star (u a I) = u (σ a) I`
(`PolynomialJet.star_aeval_polynomialJet_iff`).

Over `ℝ` and `ℂ`, complexifying the real jet algebra and its finite stages intertwines
`TauCeti.tmulConj` with `PolynomialJet.conj id` and commutes with base-changed total
differentiation (`PolynomialJet.stageComplexificationEquiv`,
`PolynomialJet.complexificationStageIso`). Conversely, for any `σ : α → α` the fixed jet
expressions form an `ℝ`-subalgebra `PolynomialJet.realSubalgebra ι σ` closed under total
differentiation (`PolynomialJet.realTotalDeriv`), whose underlying `ℝ`-submodule is
`TauCeti.realPoints (conjₛₗ σ)` and whose complexification recovers `PolynomialJet ℂ ι α` once `σ`
is involutive (`PolynomialJet.realSubalgebraEquiv`), with finite-stage counterparts
`PolynomialJet.realStageSubalgebra`, `PolynomialJet.realStageDeriv`, and
`PolynomialJet.realStageSubalgebraEquiv`. No Hermitian metric on the field space is used anywhere.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, §A, for symmetric jet coordinates
  and total derivatives.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2, for real forms via
  conjugate-linear involutions.
-/

public section

open CategoryTheory MvPolynomial
open scoped TensorProduct

universe u v

namespace TauCeti
namespace PolynomialJet

noncomputable section

section StarRing

variable {R ι α β γ : Type*} [CommSemiring R] [StarRing R]

/-- Coefficient-and-generator conjugation on polynomial jets: scalars are conjugated by
`starRingEnd R`, base coordinates `X (Sum.inl j)` are fixed, and field-jet coordinates
`X (Sum.inr (a, I))` are sent to `X (Sum.inr (σ a, I))`. -/
def conj (σ : α → β) : PolynomialJet R ι α →+* PolynomialJet R ι β :=
  (rename (Sum.map id (Prod.map σ id))).toRingHom.comp (MvPolynomial.map (starRingEnd R))

@[simp]
theorem conj_C (σ : α → β) (c : R) :
    conj (ι := ι) σ (C c) = C (star c) := by
  simp [conj, starRingEnd_apply]

@[simp]
theorem conj_smul (σ : α → β) (c : R) (p : PolynomialJet R ι α) :
    conj σ (c • p) = star c • conj σ p := by
  rw [smul_eq_C_mul, map_mul, conj_C, ← smul_eq_C_mul]

@[simp]
theorem conj_X_base (σ : α → β) (j : ι) :
    conj (R := R) σ (X (Sum.inl j)) = X (Sum.inl j) := by
  simp [conj]

@[simp]
theorem conj_X_field (σ : α → β) (a : α) (I : ι →₀ ℕ) :
    conj (R := R) σ (X (Sum.inr (a, I))) = X (Sum.inr (σ a, I)) := by
  simp [conj]

/-- `PolynomialJet.conj σ` is uniquely determined by its action on scalar constants, base
coordinates, and field-jet coordinates. -/
theorem conj_unique (σ : α → β) (K : PolynomialJet R ι α →+* PolynomialJet R ι β)
    (hC : ∀ c : R, K (C c) = C (star c))
    (hx : ∀ j : ι, K (X (Sum.inl j)) = X (Sum.inl j))
    (hu : ∀ (a : α) (I : ι →₀ ℕ), K (X (Sum.inr (a, I))) = X (Sum.inr (σ a, I))) :
    K = conj σ := by
  apply MvPolynomial.ringHom_ext
  · exact fun c ↦ (hC c).trans (conj_C σ c).symm
  · rintro (j | ⟨a, I⟩) <;> simp [hx, hu]

@[simp]
theorem conj_id (p : PolynomialJet R ι α) :
    conj (id : α → α) p = MvPolynomial.map (starRingEnd R) p := by
  have h : conj (R := R) (ι := ι) (id : α → α) = MvPolynomial.map (starRingEnd R) :=
    (conj_unique id (MvPolynomial.map (starRingEnd R))
      (fun c ↦ by simp [starRingEnd_apply])
      (fun j ↦ by simp)
      (fun a I ↦ by simp)).symm
  exact congr($h p)

/-- `PolynomialJet.conj σ` bundled as a `starRingEnd R`-semilinear map. -/
def conjₛₗ (σ : α → β) : PolynomialJet R ι α →ₛₗ[starRingEnd R] PolynomialJet R ι β where
  toFun := conj σ
  map_add' := map_add (conj σ)
  map_smul' := conj_smul σ

@[simp]
theorem coe_conjₛₗ (σ : α → β) :
    ⇑(conjₛₗ (R := R) (ι := ι) σ) = ⇑(conj σ) := (rfl)

theorem conjₛₗ_apply (σ : α → β) (p : PolynomialJet R ι α) :
    conjₛₗ σ p = conj σ p := (rfl)

/-- Composing two jet conjugations cancels scalar conjugation and composes the field-label maps. -/
theorem conj_comp_conj (τ : β → γ) (σ : α → β) (p : PolynomialJet R ι α) :
    conj τ (conj σ p) = rename (Sum.map id (Prod.map (τ ∘ σ) id)) p := by
  have h : (conj (R := R) (ι := ι) τ).comp (conj σ) =
      (rename (Sum.map id (Prod.map (τ ∘ σ) id))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · rintro (j | ⟨a, I⟩) <;> simp
  exact congr($h p)

/-- When `σ : α → α` is involutive, `PolynomialJet.conj σ` is an involution. -/
theorem conj_conj {σ : α → α} (hσ : Function.Involutive σ) (p : PolynomialJet R ι α) :
    conj σ (conj σ p) = p := by
  have hid : Sum.map (id : ι → ι) (Prod.map (σ ∘ σ) (id : (ι →₀ ℕ) → ι →₀ ℕ)) = id := by
    ext (j | ⟨a, I⟩)
    · rfl
    · simp [hσ a]
  rw [conj_comp_conj, hid, rename_id_apply]

@[simp]
theorem conj_swap_conj_swap (p : PolynomialJet R ι (α ⊕ α)) :
    conj Sum.swap (conj Sum.swap p) = p :=
  conj_conj Sum.swap_swap p

theorem conj_involutive {σ : α → α} (hσ : Function.Involutive σ) :
    Function.Involutive (conj (R := R) (ι := ι) σ) :=
  conj_conj hσ

theorem conjₛₗ_involutive {σ : α → α} (hσ : Function.Involutive σ) :
    Function.Involutive (conjₛₗ (R := R) (ι := ι) σ) :=
  conj_conj hσ

/-- Jet conjugation preserves every finite-order stage because the multi-index of each field
generator is unchanged. -/
theorem conj_mem_stage (σ : α → β) {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) : conj σ p ∈ stage R ι β r :=
  rename_field_mem_stage σ (map_mem_stage (starRingEnd R) hp)

/-- Along an injective field-label map, `PolynomialJet.conj` reflects and preserves stage
membership. -/
theorem conj_mem_stage_iff {σ : α → β} (hσ : Function.Injective σ) {r : ℕ}
    {p : PolynomialJet R ι α} :
    conj σ p ∈ stage R ι β r ↔ p ∈ stage R ι α r := by
  rw [conj, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    rename_field_mem_stage_iff hσ,
    map_mem_stage_iff (Function.Involutive.injective starRingEnd_self_apply)]

@[simp]
theorem conj_swap_mem_stage_iff {r : ℕ} {p : PolynomialJet R ι (α ⊕ α)} :
    conj Sum.swap p ∈ stage R ι (α ⊕ α) r ↔ p ∈ stage R ι (α ⊕ α) r :=
  conj_mem_stage_iff (Function.Involutive.injective Sum.swap_swap)

/-- Jet conjugation restricted to the finite-order subalgebra `PolynomialJet.stage R ι α r`. -/
def stageConj (σ : α → β) (r : ℕ) : stage R ι α r →+* stage R ι β r where
  toFun p := ⟨conj σ (p : PolynomialJet R ι α), conj_mem_stage σ p.property⟩
  map_one' := Subtype.ext (map_one (conj σ))
  map_mul' p q := Subtype.ext (map_mul (conj σ) (p : PolynomialJet R ι α) q)
  map_zero' := Subtype.ext (map_zero (conj σ))
  map_add' p q := Subtype.ext (map_add (conj σ) (p : PolynomialJet R ι α) q)

@[simp]
theorem coe_stageConj (σ : α → β) (r : ℕ) (p : stage R ι α r) :
    (stageConj σ r p : PolynomialJet R ι β) = conj σ (p : PolynomialJet R ι α) := (rfl)

@[simp]
theorem stageConj_smul (σ : α → β) (r : ℕ) (c : R) (p : stage R ι α r) :
    stageConj σ r (c • p) = star c • stageConj σ r p :=
  Subtype.ext (conj_smul σ c (p : PolynomialJet R ι α))

/-- Finite-stage jet conjugation bundled as a `starRingEnd R`-semilinear map. -/
def stageConjₛₗ (σ : α → β) (r : ℕ) :
    stage R ι α r →ₛₗ[starRingEnd R] stage R ι β r where
  toFun := stageConj σ r
  map_add' := map_add (stageConj σ r)
  map_smul' := stageConj_smul σ r

@[simp]
theorem coe_stageConjₛₗ (σ : α → β) (r : ℕ) :
    ⇑(stageConjₛₗ (R := R) (ι := ι) σ r) = ⇑(stageConj σ r) := (rfl)

theorem stageConj_conj {σ : α → α} (hσ : Function.Involutive σ) (r : ℕ) (p : stage R ι α r) :
    stageConj σ r (stageConj σ r p) = p :=
  Subtype.ext (conj_conj hσ (p : PolynomialJet R ι α))

theorem stageConj_involutive {σ : α → α} (hσ : Function.Involutive σ) (r : ℕ) :
    Function.Involutive (stageConj (R := R) (ι := ι) σ r) :=
  stageConj_conj hσ r

theorem stageConjₛₗ_involutive {σ : α → α} (hσ : Function.Involutive σ) (r : ℕ) :
    Function.Involutive (stageConjₛₗ (R := R) (ι := ι) σ r) :=
  stageConj_conj hσ r

/-- Finite-stage conjugation commutes with stage inclusions. -/
@[simp]
theorem stageConj_inclusion (σ : α → β) {r s : ℕ} (hrs : r ≤ s) (p : stage R ι α r) :
    stageConj σ s (Subalgebra.inclusion (stage_mono hrs) p) =
      Subalgebra.inclusion (stage_mono hrs) (stageConj σ r p) :=
  Subtype.ext rfl

/-- Jet conjugation commutes with total differentiation in every base direction. -/
@[simp]
theorem conj_totalDeriv (σ : α → β) (i : ι) (p : PolynomialJet R ι α) :
    conj σ (totalDeriv i p) = totalDeriv i (conj σ p) := by
  rw [conj, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_totalDeriv,
    rename_field_totalDeriv]
  rfl

/-- Finite-stage jet conjugation commutes with `PolynomialJet.stageDeriv`. -/
@[simp]
theorem stageConj_stageDeriv (σ : α → β) (i : ι) (r : ℕ) (p : stage R ι α r) :
    stageConj σ (r + 1) (stageDeriv i r p) = stageDeriv i r (stageConj σ r p) :=
  Subtype.ext (by simp [conj_totalDeriv])

end StarRing

section StarEvaluation

variable {R ι α A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [StarRing R] [StarRing A] [StarModule R A]

/-- Applying `star` to a polynomial jet evaluation conjugates the assigned base coordinates,
conjugates the assigned field-jet values, and applies coefficient conjugation `conj id`. -/
theorem star_aeval_eq (x : ι → A) (u : α → (ι →₀ ℕ) → A) (p : PolynomialJet R ι α) :
    star (aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) p) =
      aeval (Sum.elim (fun j ↦ star (x j)) (fun aI ↦ star (u aI.1 aI.2))) (conj id p) := by
  have hfun : (fun v : ι ⊕ α × (ι →₀ ℕ) ↦ star (Sum.elim x (fun aI ↦ u aI.1 aI.2) v)) =
      Sum.elim (fun j ↦ star (x j)) (fun aI ↦ star (u aI.1 aI.2)) := by
    ext (j | ⟨a, I⟩) <;> rfl
  rw [MvPolynomial.star_aeval, conj_id, hfun]

/-- Evaluating polynomial jets commutes with `star` via `PolynomialJet.conj σ` whenever the base
coordinates are self-adjoint and `star (u a I) = u (σ a) I`. -/
theorem star_aeval_polynomialJet (σ : α → α) (x : ι → A) (u : α → (ι →₀ ℕ) → A)
    (hx : ∀ j, star (x j) = x j)
    (hu : ∀ a I, star (u a I) = u (σ a) I)
    (p : PolynomialJet R ι α) :
    star (aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) p) =
      aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) (conj σ p) := by
  have hfun : (fun v ↦ star (Sum.elim x (fun aI ↦ u aI.1 aI.2) v)) =
      Sum.elim x (fun aI ↦ u aI.1 aI.2) ∘ Sum.map id (Prod.map σ id) := by
    ext (j | ⟨a, I⟩)
    · exact hx j
    · exact hu a I
  rw [MvPolynomial.star_aeval, conj, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, aeval_rename, hfun]

/-- An evaluation of polynomial jets intertwines `star` with `PolynomialJet.conj σ` on every jet
expression if and only if all base coordinates are self-adjoint and `star (u a I) = u (σ a) I`. -/
theorem star_aeval_polynomialJet_iff (σ : α → α) (x : ι → A) (u : α → (ι →₀ ℕ) → A) :
    (∀ p : PolynomialJet R ι α,
      star (aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) p) =
        aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) (conj σ p)) ↔
      (∀ j, star (x j) = x j) ∧ (∀ a I, star (u a I) = u (σ a) I) := by
  constructor
  · intro h
    exact ⟨fun j ↦ by simpa using h (X (Sum.inl j)),
      fun a I ↦ by simpa using h (X (Sum.inr (a, I)))⟩
  · rintro ⟨hx, hu⟩ p
    exact star_aeval_polynomialJet σ x u hx hu p

/-- A `conj σ`-invariant polynomial jet expression evaluates to a self-adjoint element under any
conjugation-compatible field evaluation. -/
theorem isSelfAdjoint_aeval_of_conj_eq_self {σ : α → α} {x : ι → A} {u : α → (ι →₀ ℕ) → A}
    (hx : ∀ j, IsSelfAdjoint (x j)) (hu : ∀ a I, star (u a I) = u (σ a) I)
    {p : PolynomialJet R ι α} (hp : conj σ p = p) :
    IsSelfAdjoint (aeval (Sum.elim x (fun aI ↦ u aI.1 aI.2)) p) := by
  rw [IsSelfAdjoint, star_aeval_polynomialJet σ x u (fun j ↦ (hx j).star_eq) hu, hp]

end StarEvaluation

section ComplexDescent

variable {ι : Type u} {α : Type v}

/-- Complexifying `PolynomialJet ℝ ι α` intertwines `TauCeti.tmulConj` with `conj id`. -/
theorem algebraTensorAlgEquiv_tmulConj_eq_conj_id (u : ℂ ⊗[ℝ] PolynomialJet ℝ ι α) :
    MvPolynomial.algebraTensorAlgEquiv ℝ ℂ (tmulConj (PolynomialJet ℝ ι α) u) =
      conj id (MvPolynomial.algebraTensorAlgEquiv ℝ ℂ u) := by
  rw [MvPolynomial.algebraTensorAlgEquiv_tmulConj, conj_id]

/-- Complexifying real polynomial jets intertwines the base-changed real total derivative with the
complex total derivative. -/
@[simp]
theorem algebraTensorAlgEquiv_baseChange_totalDeriv (i : ι) (u : ℂ ⊗[ℝ] PolynomialJet ℝ ι α) :
    MvPolynomial.algebraTensorAlgEquiv ℝ ℂ
        ((totalDeriv (R := ℝ) (α := α) i).toLinearMap.baseChange ℂ u) =
      totalDeriv i (MvPolynomial.algebraTensorAlgEquiv ℝ ℂ u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c p => simp
  | add x y hx hy => simp [hx, hy]

variable (ι α) in
/-- Complexification of the finite-order jet algebra `PolynomialJet.stage ℝ ι α r` as a `ℂ`-algebra
isomorphism with `PolynomialJet.stage ℂ ι α r`. -/
def stageComplexificationEquiv (r : ℕ) :
    ℂ ⊗[ℝ] stage ℝ ι α r ≃ₐ[ℂ] stage ℂ ι α r :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ)
      (Subalgebra.equivOfEq _ _ (stage_eq_supported ℝ ι α r))).trans
    ((MvPolynomial.supportedAlgebraTensorAlgEquiv ℝ ℂ _).trans
      (Subalgebra.equivOfEq _ _ (stage_eq_supported ℂ ι α r)).symm)

@[simp]
theorem coe_stageComplexificationEquiv_tmul (r : ℕ) (c : ℂ) (p : stage ℝ ι α r) :
    (stageComplexificationEquiv ι α r (c ⊗ₜ[ℝ] p) : PolynomialJet ℂ ι α) =
      c • MvPolynomial.map (algebraMap ℝ ℂ) (p : PolynomialJet ℝ ι α) := by
  simp [stageComplexificationEquiv]

/-- `PolynomialJet.stageComplexificationEquiv` intertwines `TauCeti.tmulConj` with
`PolynomialJet.stageConj id r`. -/
@[simp]
theorem stageComplexificationEquiv_tmulConj (r : ℕ) (u : ℂ ⊗[ℝ] stage ℝ ι α r) :
    stageComplexificationEquiv ι α r (tmulConj (stage ℝ ι α r) u) =
      stageConj id r (stageComplexificationEquiv ι α r u) := by
  have hconj : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ :=
    RingHom.ext Complex.conj_ofReal
  induction u using TensorProduct.inductionOn with
  | tmul c p =>
    apply Subtype.ext
    simp [MvPolynomial.map_map, hconj]
  | add x y hx hy => simp [hx, hy]

/-- `PolynomialJet.stageComplexificationEquiv` intertwines the base-changed real `stageDeriv` with
the complex `stageDeriv`. -/
@[simp]
theorem stageComplexificationEquiv_baseChange_stageDeriv (i : ι) (r : ℕ)
    (u : ℂ ⊗[ℝ] stage ℝ ι α r) :
    stageComplexificationEquiv ι α (r + 1)
        ((stageDeriv (R := ℝ) (α := α) i r).baseChange ℂ u) =
      stageDeriv i r (stageComplexificationEquiv ι α r u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c p =>
    apply Subtype.ext
    simp
  | add x y hx hy => simp [hx, hy]

/-- `PolynomialJet.stageComplexificationEquiv` commutes with stage inclusions. -/
@[simp]
theorem stageComplexificationEquiv_lTensor_inclusion {r s : ℕ} (hrs : r ≤ s)
    (u : ℂ ⊗[ℝ] stage ℝ ι α r) :
    stageComplexificationEquiv ι α s
        (Algebra.TensorProduct.lTensor (S := ℂ) ℂ (Subalgebra.inclusion (stage_mono hrs)) u) =
      Subalgebra.inclusion (stage_mono hrs) (stageComplexificationEquiv ι α r u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c p =>
    apply Subtype.ext
    simp
  | add x y hx hy => simp [hx, hy]

variable (ι) in
/-- The `ℝ`-subalgebra of complex polynomial jet expressions fixed by `PolynomialJet.conj σ`.
No involutivity assumption on `σ` is needed to form the subalgebra; involutivity enters when
recovering `PolynomialJet ℂ ι α` by complexification (`PolynomialJet.realSubalgebraEquiv`). -/
def realSubalgebra (σ : α → α) : Subalgebra ℝ (PolynomialJet ℂ ι α) where
  carrier := {p | conj σ p = p}
  mul_mem' {p q} (hp : conj σ p = p) (hq : conj σ q = q) := by
    rw [Set.mem_ofPred_eq, map_mul, hp, hq]
  one_mem' := map_one (conj σ)
  add_mem' {p q} (hp : conj σ p = p) (hq : conj σ q = q) := by
    rw [Set.mem_ofPred_eq, map_add, hp, hq]
  zero_mem' := map_zero (conj σ)
  algebraMap_mem' r := by
    rw [Set.mem_ofPred_eq, IsScalarTower.algebraMap_apply ℝ ℂ (PolynomialJet ℂ ι α),
      MvPolynomial.algebraMap_eq, conj_C]
    simp

@[simp]
theorem mem_realSubalgebra {σ : α → α} {p : PolynomialJet ℂ ι α} :
    p ∈ realSubalgebra ι σ ↔ conj σ p = p := (Iff.rfl)

/-- The underlying `ℝ`-submodule of `PolynomialJet.realSubalgebra ι σ` is `TauCeti.realPoints` of
`PolynomialJet.conjₛₗ σ`. -/
@[simp]
theorem realSubalgebra_toSubmodule (σ : α → α) :
    (realSubalgebra ι σ).toSubmodule = realPoints (conjₛₗ (R := ℂ) (ι := ι) σ) := by
  ext p
  simp

variable (ι) in
/-- The `ℝ`-subalgebra of finite-stage complex polynomial jets fixed by
`PolynomialJet.stageConj σ r`. -/
def realStageSubalgebra (σ : α → α) (r : ℕ) : Subalgebra ℝ (stage ℂ ι α r) where
  carrier := {p | stageConj σ r p = p}
  mul_mem' {p q} (hp : stageConj σ r p = p) (hq : stageConj σ r q = q) := by
    rw [Set.mem_ofPred_eq, map_mul, hp, hq]
  one_mem' := map_one (stageConj σ r)
  add_mem' {p q} (hp : stageConj σ r p = p) (hq : stageConj σ r q = q) := by
    rw [Set.mem_ofPred_eq, map_add, hp, hq]
  zero_mem' := map_zero (stageConj σ r)
  algebraMap_mem' c := by
    rw [Set.mem_ofPred_eq, IsScalarTower.algebraMap_apply ℝ ℂ (stage ℂ ι α r),
      Algebra.algebraMap_eq_smul_one, stageConj_smul, map_one]
    simp

@[simp]
theorem mem_realStageSubalgebra {σ : α → α} {r : ℕ} {p : stage ℂ ι α r} :
    p ∈ realStageSubalgebra ι σ r ↔ stageConj σ r p = p := (Iff.rfl)

theorem mem_realStageSubalgebra_iff_conj {σ : α → α} {r : ℕ} {p : stage ℂ ι α r} :
    p ∈ realStageSubalgebra ι σ r ↔ conj σ (p : PolynomialJet ℂ ι α) = p := by
  rw [mem_realStageSubalgebra, Subtype.ext_iff, coe_stageConj]

@[simp]
theorem realStageSubalgebra_toSubmodule (σ : α → α) (r : ℕ) :
    (realStageSubalgebra ι σ r).toSubmodule =
      realPoints (stageConjₛₗ (R := ℂ) (ι := ι) σ r) := by
  ext p
  simp

/-- Total differentiation restricts to an `ℝ`-derivation on `PolynomialJet.realSubalgebra ι σ`. -/
def realTotalDeriv (σ : α → α) (i : ι) :
    Derivation ℝ (realSubalgebra ι σ) (realSubalgebra ι σ) where
  toFun p := ⟨totalDeriv i p.1, by rw [mem_realSubalgebra, conj_totalDeriv, p.2]⟩
  map_add' p q := Subtype.ext (map_add (totalDeriv i) p.1 q.1)
  map_smul' r p := Subtype.ext (by
    simp only [RingHom.id_apply, SetLike.val_smul, ← Complex.coe_smul, (totalDeriv i).map_smul])
  map_one_eq_zero' := Subtype.ext (Derivation.map_one_eq_zero (totalDeriv i))
  leibniz' p q := Subtype.ext (Derivation.leibniz (totalDeriv i) p.1 q.1)

@[simp]
theorem coe_realTotalDeriv (σ : α → α) (i : ι) (p : realSubalgebra ι σ) :
    (realTotalDeriv σ i p : PolynomialJet ℂ ι α) = totalDeriv i (p : PolynomialJet ℂ ι α) := (rfl)

/-- Finite-stage total differentiation restricts to an `ℝ`-linear map between consecutive fixed
stages `PolynomialJet.realStageSubalgebra ι σ r`. -/
def realStageDeriv (σ : α → α) (i : ι) (r : ℕ) :
    realStageSubalgebra ι σ r →ₗ[ℝ] realStageSubalgebra ι σ (r + 1) where
  toFun p := ⟨stageDeriv i r p.1, by rw [mem_realStageSubalgebra, stageConj_stageDeriv, p.2]⟩
  map_add' p q := Subtype.ext (map_add (stageDeriv i r) p.1 q.1)
  map_smul' c p := Subtype.ext (by
    simp only [RingHom.id_apply, SetLike.val_smul, ← Complex.coe_smul, (stageDeriv i r).map_smul])

@[simp]
theorem coe_realStageDeriv (σ : α → α) (i : ι) (r : ℕ) (p : realStageSubalgebra ι σ r) :
    (realStageDeriv σ i r p : stage ℂ ι α (r + 1)) = stageDeriv i r (p : stage ℂ ι α r) := (rfl)

/-- Canonical `ℝ`-algebra inclusion of a fixed finite stage into `PolynomialJet.realSubalgebra`. -/
def realStageInclusion (σ : α → α) (r : ℕ) :
    realStageSubalgebra ι σ r →ₐ[ℝ] realSubalgebra ι σ where
  toFun p := ⟨(p : PolynomialJet ℂ ι α),
    mem_realSubalgebra.mpr (mem_realStageSubalgebra_iff_conj.mp p.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_realStageInclusion (σ : α → α) (r : ℕ) (p : realStageSubalgebra ι σ r) :
    (realStageInclusion σ r p : PolynomialJet ℂ ι α) = (p : PolynomialJet ℂ ι α) := (rfl)

@[simp]
theorem realStageInclusion_realStageDeriv (σ : α → α) (i : ι) (r : ℕ)
    (p : realStageSubalgebra ι σ r) :
    realStageInclusion σ (r + 1) (realStageDeriv σ i r p) =
      realTotalDeriv σ i (realStageInclusion σ r p) := by
  apply Subtype.ext
  simp

variable (ι α) in
/-- For `σ = id`, the fixed-point subalgebra `PolynomialJet.realSubalgebra ι id` is canonically
isomorphic as an `ℝ`-algebra to `PolynomialJet ℝ ι α`. -/
def realSubalgebraIdEquiv :
    PolynomialJet ℝ ι α ≃ₐ[ℝ] realSubalgebra ι (id : α → α) :=
  AlgEquiv.ofBijective
    ((MvPolynomial.mapAlgHom (Algebra.ofId ℝ ℂ)).codRestrict (realSubalgebra ι id) fun q ↦ by
      rw [mem_realSubalgebra, conj_id]
      exact (MvPolynomial.map_starRingEnd_complex_eq_self_iff_exists_real _).mpr ⟨q, rfl⟩)
    ⟨fun p q hpq ↦ MvPolynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
        (congrArg Subtype.val hpq),
      fun p ↦ by
        have hp : MvPolynomial.map (starRingEnd ℂ) (p : PolynomialJet ℂ ι α) = p := by
          simpa using mem_realSubalgebra.mp p.property
        obtain ⟨q, hq⟩ :=
          (MvPolynomial.map_starRingEnd_complex_eq_self_iff_exists_real _).mp hp
        exact ⟨q, Subtype.ext hq⟩⟩

@[simp]
theorem coe_realSubalgebraIdEquiv_apply (p : PolynomialJet ℝ ι α) :
    (realSubalgebraIdEquiv ι α p : PolynomialJet ℂ ι α) = MvPolynomial.map (algebraMap ℝ ℂ) p :=
  (rfl)

@[simp]
theorem realTotalDeriv_realSubalgebraIdEquiv (i : ι) (p : PolynomialJet ℝ ι α) :
    realTotalDeriv id i (realSubalgebraIdEquiv ι α p) =
      realSubalgebraIdEquiv ι α (totalDeriv i p) :=
  Subtype.ext (map_totalDeriv (algebraMap ℝ ℂ) i p).symm

/-- When `σ : α → α` is involutive, `PolynomialJet ℂ ι α` is canonically the complexification of
`PolynomialJet.realSubalgebra ι σ` as a `ℂ`-algebra, upgrading `TauCeti.realPointsEquiv`. -/
def realSubalgebraEquiv {σ : α → α} (hσ : Function.Involutive σ) :
    ℂ ⊗[ℝ] realSubalgebra ι σ ≃ₐ[ℂ] PolynomialJet ℂ ι α :=
  AlgEquiv.ofBijective
    (Algebra.TensorProduct.lift (Algebra.ofId ℂ (PolynomialJet ℂ ι α))
      (realSubalgebra ι σ).val fun _ _ ↦ Commute.all _ _)
    (by
      let eSub : (realSubalgebra ι σ).toSubmodule ≃ₗ[ℝ]
          realPoints (conjₛₗ (R := ℂ) (ι := ι) σ) :=
        LinearEquiv.ofEq _ _ (realSubalgebra_toSubmodule σ)
      let eLin : ℂ ⊗[ℝ] realSubalgebra ι σ ≃ₗ[ℂ] PolynomialJet ℂ ι α :=
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) eSub).trans
          (realPointsEquiv (conjₛₗ_involutive (R := ℂ) (ι := ι) hσ))
      have heq : ⇑(Algebra.TensorProduct.lift (Algebra.ofId ℂ (PolynomialJet ℂ ι α))
          (realSubalgebra ι σ).val fun _ _ ↦ Commute.all _ _) = ⇑eLin := by
        ext u : 1
        induction u using TensorProduct.inductionOn with
        | tmul c p =>
          simp [eLin, eSub, Algebra.smul_def]
        | add x y hx hy => simp [hx, hy]
      rw [heq]
      exact eLin.bijective)

@[simp]
theorem realSubalgebraEquiv_tmul {σ : α → α} (hσ : Function.Involutive σ) (c : ℂ)
    (p : realSubalgebra ι σ) :
    realSubalgebraEquiv hσ (c ⊗ₜ[ℝ] p) = c • (p : PolynomialJet ℂ ι α) := by
  simp [realSubalgebraEquiv, Algebra.smul_def]

theorem conjRealPart_mem_realSubalgebra {σ : α → α} (hσ : Function.Involutive σ)
    (p : PolynomialJet ℂ ι α) :
    conjRealPart (conjₛₗ σ) p ∈ realSubalgebra ι σ := by
  simpa using conjRealPart_mem (conjₛₗ_involutive hσ) p

theorem conjImaginaryPart_mem_realSubalgebra {σ : α → α} (hσ : Function.Involutive σ)
    (p : PolynomialJet ℂ ι α) :
    conjImaginaryPart (conjₛₗ σ) p ∈ realSubalgebra ι σ := by
  simpa using conjImaginaryPart_mem (conjₛₗ_involutive hσ) p

/-- The inverse of `PolynomialJet.realSubalgebraEquiv` decomposes any complex jet expression into
its real and imaginary parts `TauCeti.conjRealPart` and `TauCeti.conjImaginaryPart`. -/
theorem realSubalgebraEquiv_symm_apply {σ : α → α} (hσ : Function.Involutive σ)
    (p : PolynomialJet ℂ ι α) :
    (realSubalgebraEquiv hσ).symm p =
      1 ⊗ₜ[ℝ] (⟨conjRealPart (conjₛₗ σ) p, conjRealPart_mem_realSubalgebra hσ p⟩ :
          realSubalgebra ι σ) +
        Complex.I ⊗ₜ[ℝ] (⟨conjImaginaryPart (conjₛₗ σ) p,
          conjImaginaryPart_mem_realSubalgebra hσ p⟩ : realSubalgebra ι σ) := by
  rw [AlgEquiv.symm_apply_eq, map_add, realSubalgebraEquiv_tmul, realSubalgebraEquiv_tmul,
    one_smul]
  exact (conjRealPart_add_I_smul_conjImaginaryPart p).symm

/-- `PolynomialJet.realSubalgebraEquiv` intertwines `TauCeti.tmulConj` with
`PolynomialJet.conj σ`. -/
@[simp]
theorem realSubalgebraEquiv_tmulConj {σ : α → α} (hσ : Function.Involutive σ)
    (u : ℂ ⊗[ℝ] realSubalgebra ι σ) :
    realSubalgebraEquiv hσ (tmulConj (realSubalgebra ι σ) u) =
      conj σ (realSubalgebraEquiv hσ u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c p => simp [mem_realSubalgebra.mp p.property]
  | add x y hx hy => simp [hx, hy]

/-- `PolynomialJet.realSubalgebraEquiv` intertwines the base-changed real total derivative with the
complex total derivative. -/
@[simp]
theorem realSubalgebraEquiv_baseChange_realTotalDeriv {σ : α → α} (hσ : Function.Involutive σ)
    (i : ι) (u : ℂ ⊗[ℝ] realSubalgebra ι σ) :
    realSubalgebraEquiv hσ ((realTotalDeriv σ i).toLinearMap.baseChange ℂ u) =
      totalDeriv i (realSubalgebraEquiv hσ u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c p => simp
  | add x y hx hy => simp [hx, hy]

/-- Finite-stage version of `PolynomialJet.realSubalgebraEquiv`: when `σ` is involutive,
`PolynomialJet.stage ℂ ι α r` is canonically the complexification of
`PolynomialJet.realStageSubalgebra ι σ r`. -/
def realStageSubalgebraEquiv {σ : α → α} (hσ : Function.Involutive σ) (r : ℕ) :
    ℂ ⊗[ℝ] realStageSubalgebra ι σ r ≃ₐ[ℂ] stage ℂ ι α r :=
  AlgEquiv.ofBijective
    (Algebra.TensorProduct.lift (Algebra.ofId ℂ (stage ℂ ι α r))
      (realStageSubalgebra ι σ r).val fun _ _ ↦ Commute.all _ _)
    (by
      let eSub : (realStageSubalgebra ι σ r).toSubmodule ≃ₗ[ℝ]
          realPoints (stageConjₛₗ (R := ℂ) (ι := ι) σ r) :=
        LinearEquiv.ofEq _ _ (realStageSubalgebra_toSubmodule σ r)
      let eLin : ℂ ⊗[ℝ] realStageSubalgebra ι σ r ≃ₗ[ℂ] stage ℂ ι α r :=
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) eSub).trans
          (realPointsEquiv (stageConjₛₗ_involutive (R := ℂ) (ι := ι) hσ r))
      have heq : ⇑(Algebra.TensorProduct.lift (Algebra.ofId ℂ (stage ℂ ι α r))
          (realStageSubalgebra ι σ r).val fun _ _ ↦ Commute.all _ _) = ⇑eLin := by
        ext u : 1
        induction u using TensorProduct.inductionOn with
        | tmul c p =>
          simp [eLin, eSub, Algebra.smul_def]
        | add x y hx hy => simp [hx, hy]
      rw [heq]
      exact eLin.bijective)

@[simp]
theorem realStageSubalgebraEquiv_tmul {σ : α → α} (hσ : Function.Involutive σ) (r : ℕ)
    (c : ℂ) (p : realStageSubalgebra ι σ r) :
    realStageSubalgebraEquiv hσ r (c ⊗ₜ[ℝ] p) = c • (p : stage ℂ ι α r) := by
  simp [realStageSubalgebraEquiv, Algebra.smul_def]

@[simp]
theorem realStageSubalgebraEquiv_tmulConj {σ : α → α} (hσ : Function.Involutive σ) (r : ℕ)
    (u : ℂ ⊗[ℝ] realStageSubalgebra ι σ r) :
    realStageSubalgebraEquiv hσ r (tmulConj (realStageSubalgebra ι σ r) u) =
      stageConj σ r (realStageSubalgebraEquiv hσ r u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c p =>
    simp [stageConj_smul, mem_realStageSubalgebra.mp p.property]
  | add x y hx hy => simp [hx, hy]

/-- `PolynomialJet.realStageSubalgebraEquiv` intertwines the base-changed real finite-stage
derivative with the complex `stageDeriv`. -/
@[simp]
theorem realStageSubalgebraEquiv_baseChange_realStageDeriv {σ : α → α}
    (hσ : Function.Involutive σ) (i : ι) (r : ℕ) (u : ℂ ⊗[ℝ] realStageSubalgebra ι σ r) :
    realStageSubalgebraEquiv hσ (r + 1) ((realStageDeriv σ i r).baseChange ℂ u) =
      stageDeriv i r (realStageSubalgebraEquiv hσ r u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c p => simp
  | add x y hx hy => simp [hx, hy]

variable (ι) in
/-- Each finite-order complex polynomial jet stage equipped with `PolynomialJet.stageConj σ r` as an
object of `TauCeti.StarModuleCat ℂ`. -/
abbrev stageStarModuleCat {σ : α → α} (hσ : Function.Involutive σ) (r : ℕ) :
    StarModuleCat.{max u v} ℂ :=
  let starS : StarAddMonoid (stage ℂ ι α r) :=
    { star := stageConj σ r
      star_involutive := stageConj_involutive hσ r
      star_add := map_add (stageConj σ r) }
  { toModuleCat := ModuleCat.of ℂ (stage ℂ ι α r)
    starAddMonoid := starS
    starModule := @StarModule.mk ℂ (stage ℂ ι α r) _ starS.toStar _
      fun z p ↦ stageConj_smul σ r z p }

/-- Finite-stage total differentiation as a morphism in `TauCeti.StarModuleCat ℂ`. -/
def stageDerivHom {σ : α → α} (hσ : Function.Involutive σ) (i : ι) (r : ℕ) :
    stageStarModuleCat ι hσ r ⟶ stageStarModuleCat ι hσ (r + 1) :=
  StarModuleCat.ofHom (stageDeriv i r) fun p ↦ (stageConj_stageDeriv σ i r p).symm

@[simp]
theorem stageDerivHom_hom {σ : α → α} (hσ : Function.Involutive σ) (i : ι) (r : ℕ) :
    (stageDerivHom hσ i r).hom = stageDeriv i r := (rfl)

variable (ι α) in
/-- Isomorphism in `TauCeti.StarModuleCat ℂ` identifying the categorical complexification
`TauCeti.complexificationFunctor.obj (ModuleCat.of ℝ (stage ℝ ι α r))` with
`PolynomialJet.stageStarModuleCat` for `σ = id`. -/
def complexificationStageIso (r : ℕ) :
    complexificationFunctor.obj (ModuleCat.of ℝ (stage ℝ ι α r)) ≅
      stageStarModuleCat ι (Function.involutive_iff_iter_2_eq_id.mpr rfl :
        Function.Involutive (id : α → α)) r :=
  StarModuleCat.isoMk (stageComplexificationEquiv ι α r).toLinearEquiv
    (stageComplexificationEquiv_tmulConj r)

@[simp]
theorem complexificationStageIso_hom_hom (r : ℕ) :
    (complexificationStageIso ι α r).hom.hom =
      (stageComplexificationEquiv ι α r).toLinearMap :=
  StarModuleCat.isoMk_hom_hom _ _

@[simp]
theorem complexificationStageIso_inv_hom (r : ℕ) :
    (complexificationStageIso ι α r).inv.hom =
      (stageComplexificationEquiv ι α r).symm.toLinearMap :=
  StarModuleCat.isoMk_inv_hom _ _

/-- Categorical naturality of `PolynomialJet.complexificationStageIso` with respect to finite-stage
total differentiation: applying `TauCeti.complexificationFunctor` to the real `stageDeriv` agrees
with `PolynomialJet.stageDerivHom`. -/
theorem complexificationFunctor_map_stageDeriv_comp_hom (i : ι) (r : ℕ) :
    complexificationFunctor.map (ModuleCat.ofHom (stageDeriv (R := ℝ) (α := α) i r)) ≫
        (complexificationStageIso ι α (r + 1)).hom =
      (complexificationStageIso ι α r).hom ≫
        stageDerivHom (Function.involutive_iff_iter_2_eq_id.mpr rfl :
          Function.Involutive (id : α → α)) i r := by
  apply StarModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro z p
  rw [StarModuleCat.hom_comp, StarModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, complexificationFunctor_map_tmul, complexificationStageIso_hom_hom,
    complexificationStageIso_hom_hom, stageDerivHom_hom]
  apply Subtype.ext
  simp

end ComplexDescent

end

end PolynomialJet
end TauCeti
