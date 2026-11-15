/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Variational.PolynomialJet.Conjugation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Conjugate-paired complex field jets and real-component comparison

In variational field theories with complex fields (such as complex scalar, Schrödinger, or
Klein–Gordon fields), jet expressions are written either in conjugate-paired generators `(ψ, ψ̄)`
indexed by `β ⊕ β` with conjugation `PolynomialJet.conj Sum.swap`, or in two real-component
families `(u₁, u₂)` related by `ψ = u₁ + i u₂` and `ψ̄ = u₁ - i u₂` with coefficient conjugation
`PolynomialJet.conj id`.

`PolynomialJet.pairedToRealEquiv` formalizes this Wirtinger substitution as a `ℂ`-algebra
automorphism of `PolynomialJet ℂ ι (β ⊕ β)` with explicit inverse `(u₁, u₂) ↦ ((ψ + ψ̄)/2,
-i (ψ - ψ̄)/2)`. Because the substitution is `ℂ`-linear in field generators of identical multi-index
`I`, it preserves every finite jet stage (`PolynomialJet.stagePairedToRealEquiv`), commutes with
total differentiation in all base directions, and intertwines `PolynomialJet.conj Sum.swap` with
`PolynomialJet.conj id` (`PolynomialJet.stagePairedToRealStarIso`).

Passing to `conj Sum.swap`-fixed points yields the canonical `ℝ`-algebra isomorphism
`PolynomialJet.pairedRealJetEquiv : realSubalgebra ι Sum.swap ≃ₐ[ℝ] PolynomialJet ℝ ι (β ⊕ β)` and
its finite-stage counterpart `PolynomialJet.stagePairedRealJetEquiv`, commuting with total
differentiation and matching paired `(ψ, ψ̄)` evaluations in any commutative star `ℂ`-algebra with
evaluations on self-adjoint components `(u₁, u₂)`. When a derivation `D` commutes with `star`,
prolongation of `ψ` automatically prolongs the paired assignment `(ψ, star ∘ ψ)`
(`Derivation.aeval_paired_polynomialJet`). No Hermitian metric on the field space is used.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, §A, for symmetric jet coordinates
  and total derivatives.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2, for real forms via
  conjugate-linear involutions.
-/

public section

open CategoryTheory MvPolynomial

universe u v

namespace TauCeti
namespace PolynomialJet

noncomputable section

section Prolongation

variable {R ι β A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [Star A]

open Classical in
/-- When a derivation `D : Derivation R A A` commutes with `star` and prolongs a field family `ψ`,
it automatically prolongs the conjugate-paired family `(ψ, star ∘ ψ)` and intertwines `D` with
`PolynomialJet.totalDeriv`. -/
theorem _root_.Derivation.aeval_paired_polynomialJet (D : Derivation R A A)
    (hD : ∀ a : A, D (star a) = star (D a)) (i : ι) (x : ι → A)
    (ψ : β → (ι →₀ ℕ) → A)
    (hx : ∀ j, D (x j) = if i = j then 1 else 0)
    (hψ : ∀ b I, D (ψ b I) = ψ b (I + Finsupp.single i 1))
    (p : PolynomialJet R ι (β ⊕ β)) :
    D (aeval (Sum.elim x (fun aI ↦ Sum.elim ψ (fun b I ↦ star (ψ b I)) aI.1 aI.2)) p) =
      aeval (Sum.elim x (fun aI ↦ Sum.elim ψ (fun b I ↦ star (ψ b I)) aI.1 aI.2))
        (totalDeriv i p) := by
  refine D.aeval_polynomialJet i x (Sum.elim ψ (fun b I ↦ star (ψ b I))) hx ?_ p
  rintro (b | b) I
  · exact hψ b I
  · simp only [Sum.elim_inr, hD, hψ]

end Prolongation

section PairedFields

variable {ι : Type u} {β : Type v}

private def pairedToRealHom (ι β : Type*) :
    PolynomialJet ℂ ι (β ⊕ β) →ₐ[ℂ] PolynomialJet ℂ ι (β ⊕ β) :=
  aeval (Sum.elim (fun j ↦ X (Sum.inl j))
    (fun aI ↦ match aI.1 with
      | Sum.inl b => X (Sum.inr (Sum.inl b, aI.2)) + C Complex.I * X (Sum.inr (Sum.inr b, aI.2))
      | Sum.inr b => X (Sum.inr (Sum.inl b, aI.2)) - C Complex.I * X (Sum.inr (Sum.inr b, aI.2))))

private def realToPairedHom (ι β : Type*) :
    PolynomialJet ℂ ι (β ⊕ β) →ₐ[ℂ] PolynomialJet ℂ ι (β ⊕ β) :=
  aeval (Sum.elim (fun j ↦ X (Sum.inl j))
    (fun aI ↦ match aI.1 with
      | Sum.inl b =>
        C (2⁻¹ : ℂ) * (X (Sum.inr (Sum.inl b, aI.2)) + X (Sum.inr (Sum.inr b, aI.2)))
      | Sum.inr b =>
        C (-(Complex.I / 2)) * (X (Sum.inr (Sum.inl b, aI.2)) - X (Sum.inr (Sum.inr b, aI.2)))))

variable (ι β) in
/-- The Wirtinger `ℂ`-algebra automorphism on `PolynomialJet ℂ ι (β ⊕ β)` relating conjugate-paired
field jets `(ψ, ψ̄)` to real-component field jets `(u₁, u₂)`: it fixes base coordinates, sends
`ψ_{b, I} = X (Sum.inr (Sum.inl b, I))` to `u_{1, b, I} + i u_{2, b, I}`, and sends
`ψ̄_{b, I} = X (Sum.inr (Sum.inr b, I))` to `u_{1, b, I} - i u_{2, b, I}`. -/
def pairedToRealEquiv :
    PolynomialJet ℂ ι (β ⊕ β) ≃ₐ[ℂ] PolynomialJet ℂ ι (β ⊕ β) :=
  AlgEquiv.ofAlgHom (pairedToRealHom ι β) (realToPairedHom ι β)
    (algHom_ext fun v ↦ by
      have hI : (C Complex.I : PolynomialJet ℂ ι (β ⊕ β)) * C Complex.I = -1 := by
        rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
      have h2 : (C (2⁻¹ : ℂ) : PolynomialJet ℂ ι (β ⊕ β)) * 2 = 1 := by
        rw [← map_ofNat C 2, ← map_mul]
        norm_num
      have hdiv : (C (Complex.I / 2) : PolynomialJet ℂ ι (β ⊕ β)) =
          C (2⁻¹ : ℂ) * C Complex.I := by
        rw [← map_mul]
        congr 1
        ring
      rcases v with j | ⟨b | b, I⟩
      · simp [pairedToRealHom, realToPairedHom]
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, realToPairedHom, pairedToRealHom,
          aeval_X, Sum.elim_inr, map_mul, map_add, algHom_C, MvPolynomial.algebraMap_eq]
        linear_combination (norm := ring)
          (X (Sum.inr (Sum.inl b, I)) : PolynomialJet ℂ ι (β ⊕ β)) * h2
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, realToPairedHom, pairedToRealHom,
          aeval_X, Sum.elim_inr, map_mul, map_sub, map_neg, algHom_C, MvPolynomial.algebraMap_eq,
          hdiv]
        linear_combination (norm := ring)
          -(C (2⁻¹ : ℂ) * 2 * X (Sum.inr (Sum.inr b, I))) * hI +
            (X (Sum.inr (Sum.inr b, I)) : PolynomialJet ℂ ι (β ⊕ β)) * h2)
    (algHom_ext fun v ↦ by
      have hI : (C Complex.I : PolynomialJet ℂ ι (β ⊕ β)) * C Complex.I = -1 := by
        rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
      have h2 : (C (2⁻¹ : ℂ) : PolynomialJet ℂ ι (β ⊕ β)) * 2 = 1 := by
        rw [← map_ofNat C 2, ← map_mul]
        norm_num
      have hdiv : (C (Complex.I / 2) : PolynomialJet ℂ ι (β ⊕ β)) =
          C (2⁻¹ : ℂ) * C Complex.I := by
        rw [← map_mul]
        congr 1
        ring
      rcases v with j | ⟨b | b, I⟩
      · simp [pairedToRealHom, realToPairedHom]
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, pairedToRealHom, realToPairedHom,
          aeval_X, Sum.elim_inr, map_add, map_mul, map_neg, algHom_C, MvPolynomial.algebraMap_eq,
          hdiv]
        linear_combination (norm := ring)
          -C (2⁻¹ : ℂ) * (X (Sum.inr (Sum.inl b, I)) - X (Sum.inr (Sum.inr b, I))) * hI +
            (X (Sum.inr (Sum.inl b, I)) : PolynomialJet ℂ ι (β ⊕ β)) * h2
      · simp only [AlgHom.comp_apply, AlgHom.id_apply, pairedToRealHom, realToPairedHom,
          aeval_X, Sum.elim_inr, map_sub, map_mul, map_neg, algHom_C, MvPolynomial.algebraMap_eq,
          hdiv]
        linear_combination (norm := ring)
          C (2⁻¹ : ℂ) * (X (Sum.inr (Sum.inl b, I)) - X (Sum.inr (Sum.inr b, I))) * hI +
            (X (Sum.inr (Sum.inr b, I)) : PolynomialJet ℂ ι (β ⊕ β)) * h2)

@[simp]
theorem pairedToRealEquiv_C (c : ℂ) :
    pairedToRealEquiv ι β (C c) = C c := by
  rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, MvPolynomial.algebraMap_eq]

@[simp]
theorem pairedToRealEquiv_symm_C (c : ℂ) :
    (pairedToRealEquiv ι β).symm (C c) = C c := by
  rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, MvPolynomial.algebraMap_eq]

@[simp]
theorem pairedToRealEquiv_X_base (j : ι) :
    pairedToRealEquiv ι β (X (Sum.inl j)) = X (Sum.inl j) := by
  simp [pairedToRealEquiv, pairedToRealHom]

@[simp]
theorem pairedToRealEquiv_X_inl (b : β) (I : ι →₀ ℕ) :
    pairedToRealEquiv ι β (X (Sum.inr (Sum.inl b, I))) =
      X (Sum.inr (Sum.inl b, I)) + C Complex.I * X (Sum.inr (Sum.inr b, I)) := by
  simp [pairedToRealEquiv, pairedToRealHom]

@[simp]
theorem pairedToRealEquiv_X_inr (b : β) (I : ι →₀ ℕ) :
    pairedToRealEquiv ι β (X (Sum.inr (Sum.inr b, I))) =
      X (Sum.inr (Sum.inl b, I)) - C Complex.I * X (Sum.inr (Sum.inr b, I)) := by
  simp [pairedToRealEquiv, pairedToRealHom]

@[simp]
theorem pairedToRealEquiv_symm_X_base (j : ι) :
    (pairedToRealEquiv ι β).symm (X (Sum.inl j)) = X (Sum.inl j) := by
  simp [pairedToRealEquiv, realToPairedHom]

@[simp]
theorem pairedToRealEquiv_symm_X_inl (b : β) (I : ι →₀ ℕ) :
    (pairedToRealEquiv ι β).symm (X (Sum.inr (Sum.inl b, I))) =
      C (2⁻¹ : ℂ) * (X (Sum.inr (Sum.inl b, I)) + X (Sum.inr (Sum.inr b, I))) := by
  simp [pairedToRealEquiv, realToPairedHom]

@[simp]
theorem pairedToRealEquiv_symm_X_inr (b : β) (I : ι →₀ ℕ) :
    (pairedToRealEquiv ι β).symm (X (Sum.inr (Sum.inr b, I))) =
      -(C (Complex.I / 2) * (X (Sum.inr (Sum.inl b, I)) - X (Sum.inr (Sum.inr b, I)))) := by
  simp [pairedToRealEquiv, realToPairedHom]

/-- `PolynomialJet.pairedToRealEquiv` intertwines paired field conjugation `conj Sum.swap` with
real-component conjugation `conj id`. -/
@[simp]
theorem pairedToRealEquiv_conj_swap (p : PolynomialJet ℂ ι (β ⊕ β)) :
    pairedToRealEquiv ι β (conj Sum.swap p) = conj id (pairedToRealEquiv ι β p) := by
  have h : (pairedToRealEquiv ι β).toRingEquiv.toRingHom.comp (conj Sum.swap) =
      (conj id).comp (pairedToRealEquiv ι β).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · rintro (j | ⟨b | b, I⟩) <;>
        simp [RingHom.comp_apply, sub_eq_add_neg]
  exact congr($h p)

theorem pairedToRealEquiv_symm_conj_id (p : PolynomialJet ℂ ι (β ⊕ β)) :
    (pairedToRealEquiv ι β).symm (conj id p) = conj Sum.swap ((pairedToRealEquiv ι β).symm p) := by
  apply (pairedToRealEquiv ι β).injective
  simp

/-- `PolynomialJet.pairedToRealEquiv` commutes with total differentiation in every base
direction. -/
@[simp]
theorem pairedToRealEquiv_totalDeriv (i : ι) (p : PolynomialJet ℂ ι (β ⊕ β)) :
    pairedToRealEquiv ι β (totalDeriv i p) = totalDeriv i (pairedToRealEquiv ι β p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    have hv : pairedToRealEquiv ι β (totalDeriv i (X v)) =
        totalDeriv i (pairedToRealEquiv ι β (X v)) := by
      rcases v with j | ⟨b | b, I⟩
      · simp [apply_ite (pairedToRealEquiv ι β)]
      · simp [Derivation.leibniz]
      · simp [Derivation.leibniz]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hv]

@[simp]
theorem pairedToRealEquiv_symm_totalDeriv (i : ι) (p : PolynomialJet ℂ ι (β ⊕ β)) :
    (pairedToRealEquiv ι β).symm (totalDeriv i p) =
      totalDeriv i ((pairedToRealEquiv ι β).symm p) := by
  apply (pairedToRealEquiv ι β).injective
  simp

theorem pairedToRealEquiv_mem_stage {r : ℕ} {p : PolynomialJet ℂ ι (β ⊕ β)}
    (hp : p ∈ stage ℂ ι (β ⊕ β) r) : pairedToRealEquiv ι β p ∈ stage ℂ ι (β ⊕ β) r := by
  rw [stage_eq_supported] at hp
  induction hp using Algebra.adjoin_induction with
  | mem v hv =>
    obtain ⟨j | ⟨b | b, I⟩, hj, rfl⟩ := hv
    · simp
    · rw [pairedToRealEquiv_X_inl]
      exact add_mem (X_field_mem_stage r (Sum.inl b) I hj)
        (mul_mem ((stage ℂ ι (β ⊕ β) r).algebraMap_mem Complex.I)
          (X_field_mem_stage r (Sum.inr b) I hj))
    · rw [pairedToRealEquiv_X_inr]
      exact sub_mem (X_field_mem_stage r (Sum.inl b) I hj)
        (mul_mem ((stage ℂ ι (β ⊕ β) r).algebraMap_mem Complex.I)
          (X_field_mem_stage r (Sum.inr b) I hj))
  | algebraMap c =>
    rw [AlgEquiv.commutes]
    exact (stage ℂ ι (β ⊕ β) r).algebraMap_mem c
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy

theorem pairedToRealEquiv_symm_mem_stage {r : ℕ} {p : PolynomialJet ℂ ι (β ⊕ β)}
    (hp : p ∈ stage ℂ ι (β ⊕ β) r) :
    (pairedToRealEquiv ι β).symm p ∈ stage ℂ ι (β ⊕ β) r := by
  rw [stage_eq_supported] at hp
  induction hp using Algebra.adjoin_induction with
  | mem v hv =>
    obtain ⟨j | ⟨b | b, I⟩, hj, rfl⟩ := hv
    · simp
    · rw [pairedToRealEquiv_symm_X_inl]
      exact mul_mem ((stage ℂ ι (β ⊕ β) r).algebraMap_mem (2⁻¹ : ℂ))
        (add_mem (X_field_mem_stage r (Sum.inl b) I hj)
          (X_field_mem_stage r (Sum.inr b) I hj))
    · rw [pairedToRealEquiv_symm_X_inr]
      exact neg_mem (mul_mem ((stage ℂ ι (β ⊕ β) r).algebraMap_mem (Complex.I / 2))
        (sub_mem (X_field_mem_stage r (Sum.inl b) I hj)
          (X_field_mem_stage r (Sum.inr b) I hj)))
  | algebraMap c =>
    rw [AlgEquiv.commutes]
    exact (stage ℂ ι (β ⊕ β) r).algebraMap_mem c
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy

@[simp]
theorem pairedToRealEquiv_mem_stage_iff {r : ℕ} {p : PolynomialJet ℂ ι (β ⊕ β)} :
    pairedToRealEquiv ι β p ∈ stage ℂ ι (β ⊕ β) r ↔ p ∈ stage ℂ ι (β ⊕ β) r :=
  ⟨fun h ↦ (pairedToRealEquiv ι β).symm_apply_apply p ▸ pairedToRealEquiv_symm_mem_stage h,
    pairedToRealEquiv_mem_stage⟩

variable (ι β) in
/-- Finite-stage restriction of `PolynomialJet.pairedToRealEquiv`. -/
def stagePairedToRealEquiv (r : ℕ) :
    stage ℂ ι (β ⊕ β) r ≃ₐ[ℂ] stage ℂ ι (β ⊕ β) r where
  toFun p := ⟨pairedToRealEquiv ι β (p : PolynomialJet ℂ ι (β ⊕ β)),
    pairedToRealEquiv_mem_stage p.property⟩
  invFun p := ⟨(pairedToRealEquiv ι β).symm (p : PolynomialJet ℂ ι (β ⊕ β)),
    pairedToRealEquiv_symm_mem_stage p.property⟩
  left_inv p := Subtype.ext ((pairedToRealEquiv ι β).symm_apply_apply p)
  right_inv p := Subtype.ext ((pairedToRealEquiv ι β).apply_symm_apply p)
  map_mul' p q := Subtype.ext (map_mul (pairedToRealEquiv ι β) (p : PolynomialJet ℂ ι (β ⊕ β)) q)
  map_add' p q := Subtype.ext (map_add (pairedToRealEquiv ι β) (p : PolynomialJet ℂ ι (β ⊕ β)) q)
  commutes' c := Subtype.ext (AlgEquiv.commutes (pairedToRealEquiv ι β) c)

@[simp]
theorem coe_stagePairedToRealEquiv (r : ℕ) (p : stage ℂ ι (β ⊕ β) r) :
    (stagePairedToRealEquiv ι β r p : PolynomialJet ℂ ι (β ⊕ β)) =
      pairedToRealEquiv ι β (p : PolynomialJet ℂ ι (β ⊕ β)) := (rfl)

@[simp]
theorem stagePairedToRealEquiv_stageDeriv (i : ι) (r : ℕ) (p : stage ℂ ι (β ⊕ β) r) :
    stagePairedToRealEquiv ι β (r + 1) (stageDeriv i r p) =
      stageDeriv i r (stagePairedToRealEquiv ι β r p) := by
  apply Subtype.ext
  simp [pairedToRealEquiv_totalDeriv]

variable (ι β) in
/-- Isomorphism in `TauCeti.StarModuleCat ℂ` between the conjugate-paired stage
`stageStarModuleCat` (with `σ = Sum.swap`) and the real-component stage (with `σ = id`). -/
def stagePairedToRealStarIso (r : ℕ) :
    stageStarModuleCat ι
        (Function.involutive_iff_iter_2_eq_id.mpr (funext Sum.swap_swap) :
          Function.Involutive (@Sum.swap β β)) r ≅
      stageStarModuleCat ι
        (Function.involutive_iff_iter_2_eq_id.mpr rfl :
          Function.Involutive (id : β ⊕ β → β ⊕ β)) r :=
  StarModuleCat.isoMk (stagePairedToRealEquiv ι β r).toLinearEquiv fun p ↦ by
    apply Subtype.ext
    change (stagePairedToRealEquiv ι β r (stageConj Sum.swap r p) :
        PolynomialJet ℂ ι (β ⊕ β)) =
      (stageConj id r (stagePairedToRealEquiv ι β r p) : PolynomialJet ℂ ι (β ⊕ β))
    simp only [coe_stagePairedToRealEquiv, coe_stageConj, pairedToRealEquiv_conj_swap]

@[simp]
theorem stagePairedToRealStarIso_hom_hom (r : ℕ) :
    (stagePairedToRealStarIso ι β r).hom.hom =
      (stagePairedToRealEquiv ι β r).toLinearMap :=
  StarModuleCat.isoMk_hom_hom _ _

@[simp]
theorem stagePairedToRealStarIso_inv_hom (r : ℕ) :
    (stagePairedToRealStarIso ι β r).inv.hom =
      (stagePairedToRealEquiv ι β r).symm.toLinearMap :=
  StarModuleCat.isoMk_inv_hom _ _

/-- Categorical naturality of `PolynomialJet.stagePairedToRealStarIso` with respect to
`PolynomialJet.stageDerivHom`. -/
theorem stageDerivHom_comp_stagePairedToRealStarIso_hom (i : ι) (r : ℕ) :
    stageDerivHom (Function.involutive_iff_iter_2_eq_id.mpr (funext Sum.swap_swap) :
        Function.Involutive (@Sum.swap β β)) i r ≫
        (stagePairedToRealStarIso ι β (r + 1)).hom =
      (stagePairedToRealStarIso ι β r).hom ≫
        stageDerivHom (Function.involutive_iff_iter_2_eq_id.mpr rfl :
          Function.Involutive (id : β ⊕ β → β ⊕ β)) i r := by
  apply StarModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  rw [StarModuleCat.hom_comp, StarModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, stagePairedToRealStarIso_hom_hom, stagePairedToRealStarIso_hom_hom,
    stageDerivHom_hom, stageDerivHom_hom]
  exact stagePairedToRealEquiv_stageDeriv i r p

variable (ι β) in
/-- `ℝ`-algebra isomorphism between `conj Sum.swap`-invariant complex polynomial jets in `(ψ, ψ̄)`
and real polynomial jets in `(u₁, u₂)`. -/
def pairedRealJetEquiv :
    realSubalgebra ι (@Sum.swap β β) ≃ₐ[ℝ] PolynomialJet ℝ ι (β ⊕ β) :=
  (AlgEquiv.ofAlgHom
    (((pairedToRealEquiv ι β).toAlgHom.restrictScalars ℝ).comp
      (realSubalgebra ι (@Sum.swap β β)).val
      |>.codRestrict (realSubalgebra ι (id : β ⊕ β → β ⊕ β)) fun p ↦ by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Subalgebra.coe_val,
          AlgEquiv.coe_toAlgHom, mem_realSubalgebra]
        rw [← pairedToRealEquiv_conj_swap, mem_realSubalgebra.mp p.property])
    ((((pairedToRealEquiv ι β).symm.toAlgHom.restrictScalars ℝ).comp
      (realSubalgebra ι (id : β ⊕ β → β ⊕ β)).val).codRestrict
      (realSubalgebra ι (@Sum.swap β β)) fun p ↦ by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Subalgebra.coe_val,
          AlgEquiv.coe_toAlgHom, mem_realSubalgebra]
        rw [← pairedToRealEquiv_symm_conj_id, mem_realSubalgebra.mp p.property])
    (AlgHom.ext fun p ↦ Subtype.ext ((pairedToRealEquiv ι β).apply_symm_apply p))
    (AlgHom.ext fun p ↦ Subtype.ext ((pairedToRealEquiv ι β).symm_apply_apply p))).trans
    (realSubalgebraIdEquiv ι (β ⊕ β)).symm

@[simp]
theorem map_pairedRealJetEquiv (p : realSubalgebra ι (@Sum.swap β β)) :
    MvPolynomial.map (algebraMap ℝ ℂ) (pairedRealJetEquiv ι β p) =
      pairedToRealEquiv ι β (p : PolynomialJet ℂ ι (β ⊕ β)) := by
  rw [← coe_realSubalgebraIdEquiv_apply]
  exact congrArg Subtype.val
    ((realSubalgebraIdEquiv ι (β ⊕ β)).apply_symm_apply
      ⟨pairedToRealEquiv ι β (p : PolynomialJet ℂ ι (β ⊕ β)), by
        rw [mem_realSubalgebra, ← pairedToRealEquiv_conj_swap, mem_realSubalgebra.mp p.property]⟩)

/-- `PolynomialJet.pairedRealJetEquiv` intertwines restricted paired total differentiation with the
real total derivative on `(u₁, u₂)`. -/
@[simp]
theorem pairedRealJetEquiv_realTotalDeriv (i : ι) (p : realSubalgebra ι (@Sum.swap β β)) :
    pairedRealJetEquiv ι β (realTotalDeriv Sum.swap i p) =
      totalDeriv i (pairedRealJetEquiv ι β p) := by
  apply MvPolynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
  rw [map_pairedRealJetEquiv, map_totalDeriv, map_pairedRealJetEquiv, coe_realTotalDeriv,
    pairedToRealEquiv_totalDeriv]

@[simp]
theorem pairedRealJetEquiv_mem_stage_iff {r : ℕ} (p : realSubalgebra ι (@Sum.swap β β)) :
    pairedRealJetEquiv ι β p ∈ stage ℝ ι (β ⊕ β) r ↔
      (p : PolynomialJet ℂ ι (β ⊕ β)) ∈ stage ℂ ι (β ⊕ β) r := by
  rw [← map_mem_stage_iff Complex.ofReal_injective (f := algebraMap ℝ ℂ), map_pairedRealJetEquiv]
  exact pairedToRealEquiv_mem_stage_iff

variable (ι β) in
/-- Finite-stage `ℝ`-algebra isomorphism between `stageConj Sum.swap r`-invariant complex polynomial
jets in `(ψ, ψ̄)` and `PolynomialJet.stage ℝ ι (β ⊕ β) r`. -/
def stagePairedRealJetEquiv (r : ℕ) :
    realStageSubalgebra ι (@Sum.swap β β) r ≃ₐ[ℝ] stage ℝ ι (β ⊕ β) r :=
  AlgEquiv.ofBijective
    ((((pairedRealJetEquiv ι β).toAlgHom.comp (realStageInclusion Sum.swap r)).codRestrict
      (stage ℝ ι (β ⊕ β) r)) fun p ↦ by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, pairedRealJetEquiv_mem_stage_iff,
          coe_realStageInclusion]
        exact p.1.property)
    (⟨fun p q hpq ↦ by
      have h1 : realStageInclusion Sum.swap r p = realStageInclusion Sum.swap r q :=
        (pairedRealJetEquiv ι β).injective (congrArg Subtype.val hpq)
      exact Subtype.ext (Subtype.ext
        ((coe_realStageInclusion _ _ p).symm.trans
          ((congrArg Subtype.val h1).trans (coe_realStageInclusion _ _ q)))),
    fun q ↦ by
      let p₀ := (pairedRealJetEquiv ι β).symm (q : PolynomialJet ℝ ι (β ⊕ β))
      have hp₀_stage : (p₀ : PolynomialJet ℂ ι (β ⊕ β)) ∈ stage ℂ ι (β ⊕ β) r := by
        rw [← pairedRealJetEquiv_mem_stage_iff, AlgEquiv.apply_symm_apply]
        exact q.property
      let p₁ : realStageSubalgebra ι (@Sum.swap β β) r :=
        ⟨⟨p₀, hp₀_stage⟩,
          mem_realStageSubalgebra_iff_conj.mpr (mem_realSubalgebra.mp p₀.property)⟩
      have hp₁ : realStageInclusion Sum.swap r p₁ = p₀ :=
        Subtype.ext (coe_realStageInclusion _ _ p₁)
      refine ⟨p₁, Subtype.ext ?_⟩
      simpa only [AlgHom.coe_codRestrict, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hp₁] using
        (pairedRealJetEquiv ι β).apply_symm_apply (q : PolynomialJet ℝ ι (β ⊕ β))⟩ :
      Function.Bijective _)

@[simp]
theorem coe_stagePairedRealJetEquiv (r : ℕ) (p : realStageSubalgebra ι (@Sum.swap β β) r) :
    (stagePairedRealJetEquiv ι β r p : PolynomialJet ℝ ι (β ⊕ β)) =
      pairedRealJetEquiv ι β (realStageInclusion Sum.swap r p) := (rfl)

@[simp]
theorem stagePairedRealJetEquiv_realStageDeriv (i : ι) (r : ℕ)
    (p : realStageSubalgebra ι (@Sum.swap β β) r) :
    stagePairedRealJetEquiv ι β (r + 1) (realStageDeriv Sum.swap i r p) =
      stageDeriv i r (stagePairedRealJetEquiv ι β r p) := by
  apply Subtype.ext
  simp

section PairedEvaluation

variable {A : Type*} [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- Evaluating a complex jet expression `p` at `(ψ, star ∘ ψ)` where `ψ = u₁ + I • u₂` with
self-adjoint `u₁, u₂` agrees with evaluating `PolynomialJet.pairedToRealEquiv ι β p` at `(u₁, u₂)`.
-/
theorem aeval_paired_eq_aeval_pairedToRealEquiv (x : ι → A) (u₁ u₂ : β → (ι →₀ ℕ) → A)
    (hu₁ : ∀ b I, star (u₁ b I) = u₁ b I)
    (hu₂ : ∀ b I, star (u₂ b I) = u₂ b I)
    (p : PolynomialJet ℂ ι (β ⊕ β)) :
    aeval (Sum.elim x (fun aI ↦
        Sum.elim (fun b I ↦ u₁ b I + Complex.I • u₂ b I)
          (fun b I ↦ star (u₁ b I + Complex.I • u₂ b I)) aI.1 aI.2)) p =
      aeval (Sum.elim x (fun aI ↦ Sum.elim u₁ u₂ aI.1 aI.2)) (pairedToRealEquiv ι β p) := by
  have h : aeval (Sum.elim x (fun aI ↦
        Sum.elim (fun b I ↦ u₁ b I + Complex.I • u₂ b I)
          (fun b I ↦ star (u₁ b I + Complex.I • u₂ b I)) aI.1 aI.2)) =
      (aeval (Sum.elim x (fun aI ↦ Sum.elim u₁ u₂ aI.1 aI.2))).comp
        (pairedToRealEquiv ι β).toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro (j | ⟨b | b, I⟩)
    · simp
    · simp [Algebra.smul_def]
    · simp only [aeval_X, Sum.elim_inr, Sum.elim_inl, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        pairedToRealEquiv_X_inr, map_sub, map_mul, algHom_C, star_add, star_smul, hu₁ b I,
        hu₂ b I, Complex.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg]
      rw [Algebra.smul_def]
  exact congr($h p)

/-- For any complex field-jet assignment `ψ : β → (ι →₀ ℕ) → A`, decomposing `ψ` into its real and
imaginary parts `TauCeti.conjRealPart` and `TauCeti.conjImaginaryPart` identifies paired `(ψ, ψ̄)`
evaluation of `p` with component evaluation of `PolynomialJet.pairedToRealEquiv ι β p`. -/
theorem aeval_paired_eq_aeval_conjRealPart (x : ι → A) (ψ : β → (ι →₀ ℕ) → A)
    (p : PolynomialJet ℂ ι (β ⊕ β)) :
    let starₗ : A →ₛₗ[starRingEnd ℂ] A := (starLinearEquiv ℂ (A := A)).toLinearMap
    aeval (Sum.elim x (fun aI ↦ Sum.elim ψ (fun b I ↦ star (ψ b I)) aI.1 aI.2)) p =
      aeval (Sum.elim x (fun aI ↦
          Sum.elim (fun b I ↦ conjRealPart starₗ (ψ b I))
            (fun b I ↦ conjImaginaryPart starₗ (ψ b I)) aI.1 aI.2))
        (pairedToRealEquiv ι β p) := by
  intro starₗ
  have hstar : Function.Involutive starₗ := star_star
  have hre (b : β) (I : ι →₀ ℕ) : star (conjRealPart starₗ (ψ b I)) =
      conjRealPart starₗ (ψ b I) :=
    mem_realPoints.mp (conjRealPart_mem hstar (ψ b I))
  have him (b : β) (I : ι →₀ ℕ) : star (conjImaginaryPart starₗ (ψ b I)) =
      conjImaginaryPart starₗ (ψ b I) :=
    mem_realPoints.mp (conjImaginaryPart_mem hstar (ψ b I))
  have hdecomp (b : β) (I : ι →₀ ℕ) :
      conjRealPart starₗ (ψ b I) + Complex.I • conjImaginaryPart starₗ (ψ b I) = ψ b I :=
    conjRealPart_add_I_smul_conjImaginaryPart (ψ b I)
  simpa only [hdecomp] using aeval_paired_eq_aeval_pairedToRealEquiv x
    (fun b I ↦ conjRealPart starₗ (ψ b I)) (fun b I ↦ conjImaginaryPart starₗ (ψ b I))
    hre him p

/-- For a `conj Sum.swap`-invariant jet expression `p`, paired `(ψ, ψ̄)` evaluation at
`ψ = u₁ + I • u₂` equals real polynomial evaluation of `PolynomialJet.pairedRealJetEquiv ι β p` at
the self-adjoint components `(u₁, u₂)`. -/
theorem aeval_paired_eq_aeval_pairedRealJetEquiv [Algebra ℝ A] [IsScalarTower ℝ ℂ A]
    (x : ι → A) (u₁ u₂ : β → (ι →₀ ℕ) → A)
    (hu₁ : ∀ b I, star (u₁ b I) = u₁ b I)
    (hu₂ : ∀ b I, star (u₂ b I) = u₂ b I)
    (p : realSubalgebra ι (@Sum.swap β β)) :
    aeval (Sum.elim x (fun aI ↦
        Sum.elim (fun b I ↦ u₁ b I + Complex.I • u₂ b I)
          (fun b I ↦ star (u₁ b I + Complex.I • u₂ b I)) aI.1 aI.2))
        (p : PolynomialJet ℂ ι (β ⊕ β)) =
      aeval (R := ℝ) (Sum.elim x (fun aI ↦ Sum.elim u₁ u₂ aI.1 aI.2))
        (pairedRealJetEquiv ι β p) := by
  rw [aeval_paired_eq_aeval_pairedToRealEquiv x u₁ u₂ hu₁ hu₂, ← map_pairedRealJetEquiv,
    aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq ℝ ℂ A, ← aeval_def]

end PairedEvaluation

end PairedFields

end

end PolynomialJet
end TauCeti
