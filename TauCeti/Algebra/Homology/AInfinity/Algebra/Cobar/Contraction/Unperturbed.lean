/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.Augmentation
import TauCeti.LinearAlgebra.TensorAlgebra.Projection
import Mathlib.Tactic.Abel

/-!
# The unperturbed cobar--bar contraction

Let `𝒜` be an `A∞` algebra on a graded module `A` over any commutative ring `R`, and split the
bar differential on `Tᶜ(sA)` as `b = b₁ + b_{≥ 2}` (`barDifferential_eq_unary_add_higher`).
The unary bar differential `b₁` makes `Tᶜ(sA)` into a noncounital differential graded coalgebra
(`TauCeti.AInfinityAlgebra.isNonCounitalDGCoalgebra_unaryBar`), whose cobar construction
`(Ω Tᶜ(sA), d₀)` is the unperturbed cobar--bar complex.

This file constructs an explicit special contraction

`TauCeti.AInfinityAlgebra.cobarUnaryContraction 𝒜`

of `(Ω Tᶜ(sA), d₀)` onto `(R × A, (0, 𝒜.differential))` over any commutative ring `R`, with no
field, flatness, or boundedness hypotheses.  The contracting homotopy `h` merges the first two
tensor factors whenever the first factor is a single letter:

`h (s⁻¹ v₁ * s⁻¹ v₂ * w) = s⁻¹ (prepend (σ_sA (letter v₁)) v₂) * w`,

and vanishes on tensor lengths `0` and `1`.

## Main definitions

* `TauCeti.AInfinityAlgebra.cobarUnaryContraction`: the unperturbed special contraction of
  `(Ω Tᶜ(sA), d₀)` onto `(R × A, (0, 𝒜.differential))`.

## Main results

* `TauCeti.AInfinityAlgebra.isNonCounitalDGCoalgebra_unaryBar`: `Tᶜ(sA)` with the unary bar
  differential is a noncounital DG coalgebra.
* `TauCeti.AInfinityAlgebra.cobarUnaryContraction_incl`: the inclusion sends `(r, a)` to
  `algebraMap R _ r + 𝒜.toCobarBar.linearPart a`.
* `TauCeti.AInfinityAlgebra.fst_cobarUnaryContraction_proj`: the scalar coordinate of the
  projection is the canonical cobar augmentation.
* `TauCeti.AInfinityAlgebra.cobarUnaryContraction_homotopy_tprod_add_two`: explicit formula for the
  contracting homotopy on pure tensors of length `k + 2`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, for the contracting homotopy of `Ω B A`.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
-/

public section

open scoped BigOperators TensorProduct
open TensorAlgebra TauCeti.InternalGrading

namespace TauCeti.AInfinityAlgebra

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### The unary bar coalgebra and auxiliary word identities -/

/-- The reduced tensor words `Tᶜ(sA)` with deconcatenation and the unary bar differential form a
noncounital differential graded coalgebra. -/
theorem isNonCounitalDGCoalgebra_unaryBar (𝒜 : AInfinityAlgebra R A) :
    IsNonCounitalDGCoalgebra (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential where
  coassoc := ReducedTensorWords.deconcatenation_coassoc R A
  isHomogeneous_comul := ReducedTensorWords.isHomogeneous_deconcatenation _
  map_mem hc := by
    rw [ReducedTensorWords.grading_piece] at hc ⊢
    exact 𝒜.isHomogeneous_unaryBarDifferential.map_mem hc
  sq_zero c := LinearMap.congr_fun 𝒜.unaryBarDifferential_comp_self c
  comul_differential := by
    rw [ReducedTensorWords.koszulTwist_grading, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.add_comp]
    exact ReducedTensorWords.isGradedCoderivation_iff.1
      𝒜.isGradedCoderivation_unaryBarDifferential

/-- Reassembling the first-letter cuts of a reduced tensor word removes its length-one part. -/
private theorem lift_prepend_letter_deconcatenation (v : ReducedTensorWords R A) :
    TensorProduct.lift (ReducedTensorWords.prepend R A)
        (TensorProduct.map (ReducedTensorWords.letter R A) LinearMap.id
          (ReducedTensorWords.deconcatenation R A v)) =
      v - ReducedTensorWords.ofLetter R A (ReducedTensorWords.letter R A v) := by
  have h : TensorProduct.lift (ReducedTensorWords.prepend R A) ∘ₗ
      TensorProduct.map (ReducedTensorWords.letter R A) LinearMap.id ∘ₗ
        ReducedTensorWords.deconcatenation R A =
      LinearMap.id - ReducedTensorWords.ofLetter R A ∘ₗ ReducedTensorWords.letter R A := by
    refine ReducedTensorWords.linearMap_ext R A fun ⟨n, hn⟩ x ↦ ?_
    match n with
    | 0 => exact absurd hn (lt_irrefl 0)
    | 1 =>
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
      rw [ReducedTensorWords.of_tprod_eq_subword R hn, ReducedTensorWords.subword_one R A x hn]
      simp
    | m + 2 =>
      have hx : ReducedTensorWords.of R A ⟨m + 2, hn⟩ (PiTensorProduct.tprod R x) =
          ReducedTensorWords.prepend R A (x 0)
            (ReducedTensorWords.of R A ⟨m + 1, Nat.succ_pos m⟩
              (PiTensorProduct.tprod R fun i : Fin (m + 1) ↦ x i.succ)) := by
        rw [ReducedTensorWords.prepend_of_tprod]
        exact ReducedTensorWords.of_tprod_congr R A _ rfl fun i ↦ by
          refine Fin.cases ?_ ?_ i <;> simp
      have hkill : TensorProduct.map (ReducedTensorWords.letter R A) LinearMap.id ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R A)
            (ReducedTensorWords.prepend R A (x 0)) = 0 := by
        ext u w
        simp
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, hx,
        ReducedTensorWords.deconcatenation_prepend, map_add, ReducedTensorWords.letter_prepend,
        map_zero, sub_zero]
      have h0 : TensorProduct.map (ReducedTensorWords.letter R A) LinearMap.id
          (LinearMap.rTensor (ReducedTensorWords R A) (ReducedTensorWords.prepend R A (x 0))
            (ReducedTensorWords.deconcatenation R A
              (ReducedTensorWords.of R A ⟨m + 1, Nat.succ_pos m⟩
                (PiTensorProduct.tprod R fun i : Fin (m + 1) ↦ x i.succ)))) = 0 :=
        LinearMap.congr_fun hkill _
      rw [h0, map_zero, add_zero, TensorProduct.map_tmul, ReducedTensorWords.letter_ofLetter,
        LinearMap.id_apply, TensorProduct.lift.tmul]
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using
    LinearMap.congr_fun h v

/-- The unary bar differential acts on a prepended word by the Koszul-signed Leibniz rule. -/
private theorem unaryBarDifferential_prepend (𝒜 : AInfinityAlgebra R A) (a : A)
    (w : ReducedTensorWords R A) :
    𝒜.unaryBarDifferential (ReducedTensorWords.prepend R A a w) =
      ReducedTensorWords.prepend R A (𝒜.m 1 ![a]) w +
        ReducedTensorWords.prepend R A ((𝒜.grading.shift 1).koszulTwist 1 a)
          (𝒜.unaryBarDifferential w) := by
  have h : 𝒜.unaryBarDifferential ∘ₗ ReducedTensorWords.prepend R A a =
      ReducedTensorWords.prepend R A (𝒜.m 1 ![a]) +
        ReducedTensorWords.prepend R A ((𝒜.grading.shift 1).koszulTwist 1 a) ∘ₗ
          𝒜.unaryBarDifferential := by
    refine ReducedTensorWords.linearMap_ext R A fun ⟨n, hn⟩ y ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [ReducedTensorWords.prepend_of_tprod]
    dsimp only
    rw [𝒜.unaryBarDifferential_of_tprod, 𝒜.unaryBarDifferential_of_tprod, map_sum,
      Finset.sum_range_succ', add_comm]
    congr 1
    · rw [ReducedTensorWords.prepend_of_tprod]
      exact ReducedTensorWords.of_tprod_congr R A _ rfl fun i ↦ by
        refine Fin.cases ?_ ?_ i <;> simp
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [ReducedTensorWords.prepend_of_tprod]
      exact ReducedTensorWords.of_tprod_congr R A _ rfl fun i ↦ by
        refine Fin.cases ?_ ?_ i <;> simp
  simpa only [LinearMap.comp_apply, LinearMap.add_apply] using LinearMap.congr_fun h w

/-- The differential anticommutes with the suspended Koszul twist. -/
private theorem differential_koszulTwist_shift_one (𝒜 : AInfinityAlgebra R A) (a : A) :
    𝒜.m 1 ![(𝒜.grading.shift 1).koszulTwist 1 a] =
      -(𝒜.grading.shift 1).koszulTwist 1 (𝒜.m 1 ![a]) := by
  have hd : LinearMap.IsHomogeneous 𝒜.differential (𝒜.grading.shift 1).piece
      (𝒜.grading.shift 1).piece 1 := by
    rw [LinearMap.isHomogeneous_def]
    intro p x hx
    rw [InternalGrading.shift_piece] at hx ⊢
    rw [add_right_comm]
    exact 𝒜.differential_mem_piece hx
  have h := hd.koszulTwist_apply 1 a
  simp only [mul_one, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
    neg_one_smul, differential_apply] at h
  exact (neg_eq_iff_eq_neg.2 h).symm

/-- Checking equality of linear maps out of `TensorAlgebra R C` on length `0`, length `1`, and
products `ι v₁ * ι v₂ * w`. -/
private theorem tensorAlgebra_linearMap_ext_three {C N : Type*}
    [AddCommMonoid C] [Module R C] [AddCommMonoid N] [Module R N]
    {f g : TensorAlgebra R C →ₗ[R] N}
    (h0 : f 1 = g 1) (h1 : ∀ v, f (ι R v) = g (ι R v))
    (h2 : ∀ v₁ v₂ w, f (ι R v₁ * ι R v₂ * w) = g (ι R v₁ * ι R v₂ * w)) : f = g :=
  TensorAlgebra.linearMap_ext_tprod fun n x ↦ by
    match n with
    | 0 => simpa [TensorAlgebra.tprod_apply] using h0
    | 1 => simpa [TensorAlgebra.tprod_apply] using h1 (x 0)
    | k + 2 =>
      have ht : TensorAlgebra.tprod R C (k + 2) x =
          ι R (x 0) * ι R (x 1) * TensorAlgebra.tprod R C k (fun i ↦ x i.succ.succ) := by
        simp [TensorAlgebra.tprod_apply, List.ofFn_succ, mul_assoc]
      rw [ht]
      exact h2 _ _ _

/-- The Koszul automorphism of the cobar algebra negates and twists a desuspended generator. -/
private theorem koszulTwistAlgEquiv_cobar_ι (𝒜 : AInfinityAlgebra R A)
    (v : ReducedTensorWords R A) :
    koszulTwistAlgEquiv
        (tensorAlgebraPiece ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1))) 1
        (ι R v) =
      -ι R ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 v) := by
  rw [koszulTwistAlgEquiv_apply, koszulTwist_tensorAlgebraPiece_ι,
    InternalGrading.koszulTwist_shift]
  simp

/-! ### The unperturbed special contraction on `(Ω Tᶜ(sA), d₀)` -/

section Unperturbed

variable (𝒜 : AInfinityAlgebra R A)

/-- The canonical augmentations of the unary and full cobar constructions agree pointwise. -/
theorem cobarAugmentation_unaryBar_eq (x : TensorAlgebra R (ReducedTensorWords R A)) :
    𝒜.isNonCounitalDGCoalgebra_unaryBar.cobarAugmentation x =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation x := by
  have h : 𝒜.isNonCounitalDGCoalgebra_unaryBar.cobarAugmentation.toGradedAlgHom.toAlgHom =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.toGradedAlgHom.toAlgHom := by
    apply TensorAlgebra.hom_ext
    ext c
    simp
  exact AlgHom.congr_fun h x

/-- The inclusion `R × A ⟶ Ω Tᶜ(sA)` sending `(r, a)` to `r + toCobarBar.linearPart a`. -/
private noncomputable def cobarIncl :
    R × A →ₗ[R] TensorAlgebra R (ReducedTensorWords R A) :=
  (Algebra.linearMap R _).coprod 𝒜.toCobarBar.linearPart

private theorem cobarIncl_apply (r : R) (a : A) :
    cobarIncl 𝒜 (r, a) = algebraMap R _ r + 𝒜.toCobarBar.linearPart a := (rfl)

private theorem toCobarBar_linearPart_apply (a : A) :
    𝒜.toCobarBar.linearPart a =
      ι R (ReducedTensorWords.ofLetter R A ((𝒜.grading.shift 1).koszulTwist 1 a)) := by
  rw [AInfinityHom.linearPart_apply, taylor_toCobarBar, LinearMap.comp_apply,
    ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_ofLetter]

/-- The `A`-coordinate of the unperturbed projection `Ω Tᶜ(sA) ⟶ R × A`. -/
private noncomputable def cobarProjA :
    TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] A :=
  (𝒜.grading.shift 1).koszulTwist 1 ∘ₗ ReducedTensorWords.letter R A ∘ₗ
    (TensorPower.oneEquiv R (ReducedTensorWords R A)).toLinearMap ∘ₗ
      TensorAlgebra.tensorPowerProjection 1

private theorem cobarProjA_algebraMap (r : R) :
    cobarProjA 𝒜 (algebraMap R _ r) = 0 := by
  simp [cobarProjA]

private theorem cobarProjA_one : cobarProjA 𝒜 1 = 0 := by
  simpa using cobarProjA_algebraMap 𝒜 1

private theorem cobarProjA_ι (v : ReducedTensorWords R A) :
    cobarProjA 𝒜 (ι R v) = (𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A v) := by
  simp [cobarProjA, TauCeti.TensorPower.oneEquiv_tprod]

private theorem cobarProjA_ι_mul_ι_mul (v₁ v₂ : ReducedTensorWords R A)
    (w : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarProjA 𝒜 (ι R v₁ * ι R v₂ * w) = 0 := by
  have h : cobarProjA 𝒜 ∘ₗ LinearMap.mulLeft R (ι R v₁ * ι R v₂) = 0 := by
    refine TensorAlgebra.linearMap_ext_tprod fun n x ↦ ?_
    have ht : ι R v₁ * ι R v₂ * TensorAlgebra.tprod R _ n x =
        TensorAlgebra.tprod R _ (n + 2) (Fin.cons v₁ (Fin.cons v₂ x)) := by
      simp [TensorAlgebra.tprod_apply, List.ofFn_succ, mul_assoc]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply, ht,
      cobarProjA, TensorAlgebra.tensorPowerProjection_tprod]
    rw [dite_eq_right (by omega)]
    simp
  exact LinearMap.congr_fun h w

private theorem cobarProjA_mul (x y : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarProjA 𝒜 (x * y) =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation x • cobarProjA 𝒜 y +
        𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation y • cobarProjA 𝒜 x := by
  let ε := 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.toGradedAlgHom.toAlgHom.toLinearMap
  have hxy : ∀ y, cobarProjA 𝒜 ∘ₗ LinearMap.mulRight R y =
      ε.smulRight (cobarProjA 𝒜 y) + ε y • cobarProjA 𝒜 := by
    intro y
    refine TensorAlgebra.linearMap_ext_tprod fun m f ↦ ?_
    have hy : cobarProjA 𝒜 ∘ₗ LinearMap.mulLeft R (TensorAlgebra.tprod R _ m f) =
        ε (TensorAlgebra.tprod R _ m f) • cobarProjA 𝒜 +
          ε.smulRight (cobarProjA 𝒜 (TensorAlgebra.tprod R _ m f)) := by
      refine TensorAlgebra.linearMap_ext_tprod fun n g ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.smulRight_apply]
      cases m with
      | zero =>
        have h1 : TensorAlgebra.tprod R _ 0 f = 1 := by simp [TensorAlgebra.tprod_apply]
        have hε1 : ε 1 = 1 := by
          -- Evaluate the linear map view of the augmentation on `1`.
          change 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation 1 = 1
          exact map_one _
        rw [h1, one_mul, hε1, one_smul, cobarProjA_one, smul_zero, add_zero]
      | succ m' =>
        cases n with
        | zero =>
          have h1 : TensorAlgebra.tprod R _ 0 g = 1 := by simp [TensorAlgebra.tprod_apply]
          have hε1 : ε 1 = 1 := by
            -- Evaluate the linear map view of the augmentation on `1`.
            change 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation 1 = 1
            exact map_one _
          rw [h1, mul_one, cobarProjA_one, smul_zero, zero_add, hε1, one_smul]
        | succ n' =>
          rw [TensorAlgebra.tprod_mul_tprod]
          have hf : ε (TensorAlgebra.tprod R _ (m' + 1) f) = 0 :=
            𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation_tprod_of_pos (Nat.succ_pos m') f
          have hg : ε (TensorAlgebra.tprod R _ (n' + 1) g) = 0 :=
            𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation_tprod_of_pos (Nat.succ_pos n') g
          rw [hf, hg, zero_smul, zero_smul, add_zero]
          simp only [cobarProjA, LinearMap.comp_apply, TensorAlgebra.tensorPowerProjection_tprod]
          rw [dite_eq_right (by omega)]
          simp
    simpa [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun hy y
  simpa [ε, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.add_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply] using LinearMap.congr_fun (hxy y) x

private theorem cobarProjA_mul_of_augmentation_eq_zero
    {x y : TensorAlgebra R (ReducedTensorWords R A)}
    (hx : 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation x = 0)
    (hy : 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation y = 0) :
    cobarProjA 𝒜 (x * y) = 0 := by
  rw [cobarProjA_mul, hx, hy]
  simp

/-- The unperturbed projection `Ω Tᶜ(sA) ⟶ R × A`: augmentation in the first coordinate and
`cobarProjA` in the second. -/
private noncomputable def cobarProj₀ :
    TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] R × A :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.toGradedAlgHom.toAlgHom.toLinearMap.prod
    (cobarProjA 𝒜)

private theorem cobarProj₀_apply (x : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarProj₀ 𝒜 x = (𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation x, cobarProjA 𝒜 x) := (rfl)

private theorem update_tail_succ_succ {α : Type*} {k : ℕ} (x : Fin (k + 2) → α) (j : Fin k)
    (w : α) :
    (fun l : Fin k ↦ Function.update x j.succ.succ w l.succ.succ) =
      Function.update (fun l : Fin k ↦ x l.succ.succ) j w := by
  funext l
  by_cases hlj : l = j
  · subst hlj; simp
  · rw [Function.update_of_ne hlj,
      Function.update_of_ne (fun h ↦ hlj (Fin.succ_injective _ (Fin.succ_injective _ h)))]

private noncomputable def cobarHomotopyFun (k : ℕ) (x : Fin (k + 2) → ReducedTensorWords R A) :
    TensorAlgebra R (ReducedTensorWords R A) :=
  ι R (ReducedTensorWords.prepend R A
    ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A (x 0))) (x 1)) *
    TensorAlgebra.tprod R _ k (fun i : Fin k ↦ x i.succ.succ)

private theorem cobarHomotopyFun_update_add (k : ℕ) (x : Fin (k + 2) → ReducedTensorWords R A)
    (i : Fin (k + 2)) (u v : ReducedTensorWords R A) :
    cobarHomotopyFun 𝒜 k (Function.update x i (u + v)) =
      cobarHomotopyFun 𝒜 k (Function.update x i u) +
        cobarHomotopyFun 𝒜 k (Function.update x i v) := by
  refine Fin.cases ?_ (fun i' ↦ Fin.cases ?_ (fun j ↦ ?_) i') i
  · have htail : ∀ w, (fun l : Fin k ↦ Function.update x 0 w l.succ.succ) =
        fun l : Fin k ↦ x l.succ.succ := fun w ↦
      funext fun l ↦ Function.update_of_ne (Fin.succ_ne_zero _) w x
    have h1 : ∀ w, Function.update x 0 w 1 = x 1 := fun w ↦
      Function.update_of_ne (show (1 : Fin (k + 2)) ≠ 0 by simp) w x
    simp only [cobarHomotopyFun, htail, h1, Function.update_self, map_add, LinearMap.add_apply,
      add_mul]
  · have htail : ∀ w, (fun l : Fin k ↦ Function.update x 1 w l.succ.succ) =
        fun l : Fin k ↦ x l.succ.succ := fun w ↦ funext fun l ↦
      Function.update_of_ne (show l.succ.succ ≠ (1 : Fin (k + 2)) by simp [Fin.ext_iff]) w x
    have h0 : ∀ w, Function.update x 1 w 0 = x 0 := fun w ↦
      Function.update_of_ne (show (0 : Fin (k + 2)) ≠ 1 by simp) w x
    simp only [cobarHomotopyFun, htail, h0, Fin.succ_zero_eq_one, Function.update_self, map_add,
      add_mul]
  · have h0 : ∀ w, Function.update x j.succ.succ w 0 = x 0 := fun w ↦
      Function.update_of_ne (Fin.succ_ne_zero j.succ).symm w x
    have h1 : ∀ w, Function.update x j.succ.succ w 1 = x 1 := fun w ↦
      Function.update_of_ne (show (1 : Fin (k + 2)) ≠ j.succ.succ by simp [Fin.ext_iff]) w x
    simp only [cobarHomotopyFun, h0, h1, update_tail_succ_succ, MultilinearMap.map_update_add,
      mul_add]

private theorem cobarHomotopyFun_update_smul (k : ℕ) (x : Fin (k + 2) → ReducedTensorWords R A)
    (i : Fin (k + 2)) (r : R) (u : ReducedTensorWords R A) :
    cobarHomotopyFun 𝒜 k (Function.update x i (r • u)) =
      r • cobarHomotopyFun 𝒜 k (Function.update x i u) := by
  refine Fin.cases ?_ (fun i' ↦ Fin.cases ?_ (fun j ↦ ?_) i') i
  · have htail : ∀ w, (fun l : Fin k ↦ Function.update x 0 w l.succ.succ) =
        fun l : Fin k ↦ x l.succ.succ := fun w ↦
      funext fun l ↦ Function.update_of_ne (Fin.succ_ne_zero _) w x
    have h1 : ∀ w, Function.update x 0 w 1 = x 1 := fun w ↦
      Function.update_of_ne (show (1 : Fin (k + 2)) ≠ 0 by simp) w x
    simp only [cobarHomotopyFun, htail, h1, Function.update_self, map_smul, LinearMap.smul_apply,
      smul_mul_assoc]
  · have htail : ∀ w, (fun l : Fin k ↦ Function.update x 1 w l.succ.succ) =
        fun l : Fin k ↦ x l.succ.succ := fun w ↦ funext fun l ↦
      Function.update_of_ne (show l.succ.succ ≠ (1 : Fin (k + 2)) by simp [Fin.ext_iff]) w x
    have h0 : ∀ w, Function.update x 1 w 0 = x 0 := fun w ↦
      Function.update_of_ne (show (0 : Fin (k + 2)) ≠ 1 by simp) w x
    simp only [cobarHomotopyFun, htail, h0, Fin.succ_zero_eq_one, Function.update_self, map_smul,
      smul_mul_assoc]
  · have h0 : ∀ w, Function.update x j.succ.succ w 0 = x 0 := fun w ↦
      Function.update_of_ne (Fin.succ_ne_zero j.succ).symm w x
    have h1 : ∀ w, Function.update x j.succ.succ w 1 = x 1 := fun w ↦
      Function.update_of_ne (show (1 : Fin (k + 2)) ≠ j.succ.succ by simp [Fin.ext_iff]) w x
    simp only [cobarHomotopyFun, h0, h1, update_tail_succ_succ, MultilinearMap.map_update_smul,
      RingHom.id_apply, mul_smul_comm]

/-- The length-`(k + 2)` multilinear map building the contracting homotopy `h`. -/
private noncomputable def cobarHomotopyMultilinear (k : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ ReducedTensorWords R A)
      (TensorAlgebra R (ReducedTensorWords R A)) where
  toFun := cobarHomotopyFun 𝒜 k
  map_update_add' x i u v := by convert cobarHomotopyFun_update_add 𝒜 k x i u v
  map_update_smul' x i r u := by
    rw [RingHom.id_apply]
    convert cobarHomotopyFun_update_smul 𝒜 k x i r u

/-- The contracting homotopy `h : Ω Tᶜ(sA) ⟶ Ω Tᶜ(sA)` of the unperturbed cobar--bar
contraction: it merges the first two tensor factors whenever the first is a single letter, and
vanishes in tensor lengths `0` and `1`. -/
private noncomputable def cobarHomotopy :
    Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
  DirectSum.toModule R ℕ (TensorAlgebra R (ReducedTensorWords R A))
    (fun n ↦ match n with
      | 0 => 0
      | 1 => 0
      | k + 2 => PiTensorProduct.lift (cobarHomotopyMultilinear 𝒜 k)) ∘ₗ
    TensorAlgebra.toDirectSum.toLinearMap

private theorem cobarHomotopy_one : cobarHomotopy 𝒜 1 = 0 := by
  have h1 : (1 : TensorAlgebra R (ReducedTensorWords R A)) =
      TensorAlgebra.tprod R _ 0 Fin.elim0 := by
    simp [TensorAlgebra.tprod_apply]
  rw [h1, cobarHomotopy, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TensorAlgebra.toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  rfl

private theorem cobarHomotopy_algebraMap (r : R) : cobarHomotopy 𝒜 (algebraMap R _ r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, cobarHomotopy_one, smul_zero]

private theorem cobarHomotopy_ι (v : ReducedTensorWords R A) : cobarHomotopy 𝒜 (ι R v) = 0 := by
  have h1 : ι R v = TensorAlgebra.tprod R _ 1 (fun _ ↦ v) := by
    simp [TensorAlgebra.tprod_apply]
  rw [h1, cobarHomotopy, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TensorAlgebra.toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  rfl

private theorem cobarHomotopy_tprod_add_two (k : ℕ) (x : Fin (k + 2) → ReducedTensorWords R A) :
    cobarHomotopy 𝒜 (TensorAlgebra.tprod R _ (k + 2) x) =
      ι R (ReducedTensorWords.prepend R A
        ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A (x 0))) (x 1)) *
        TensorAlgebra.tprod R _ k (fun i : Fin k ↦ x i.succ.succ) := by
  rw [cobarHomotopy, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TensorAlgebra.toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  exact PiTensorProduct.lift.tprod _

private theorem cobarHomotopy_ι_mul_ι_mul (v₁ v₂ : ReducedTensorWords R A)
    (w : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarHomotopy 𝒜 (ι R v₁ * ι R v₂ * w) =
      ι R (ReducedTensorWords.prepend R A
        ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A v₁)) v₂) * w := by
  have h : cobarHomotopy 𝒜 ∘ₗ LinearMap.mulLeft R (ι R v₁ * ι R v₂) =
      LinearMap.mulLeft R (ι R (ReducedTensorWords.prepend R A
        ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A v₁)) v₂)) := by
    refine TensorAlgebra.linearMap_ext_tprod fun k y ↦ ?_
    have ht : ι R v₁ * ι R v₂ * TensorAlgebra.tprod R _ k y =
        TensorAlgebra.tprod R _ (k + 2) (Fin.cons v₁ (Fin.cons v₂ y)) := by
      simp [TensorAlgebra.tprod_apply, List.ofFn_succ, mul_assoc]
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ht,
      cobarHomotopy_tprod_add_two]
    simp
  exact LinearMap.congr_fun h w

private theorem cobarHomotopy_ι_mul_of_letter_eq_zero {u : ReducedTensorWords R A}
    (hu : ReducedTensorWords.letter R A u = 0)
    (w : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarHomotopy 𝒜 (ι R u * w) = 0 := by
  have h : cobarHomotopy 𝒜 ∘ₗ LinearMap.mulLeft R (ι R u) = 0 := by
    refine TensorAlgebra.linearMap_ext_tprod fun n y ↦ ?_
    cases n with
    | zero =>
      simp [TensorAlgebra.tprod_apply, cobarHomotopy_ι]
    | succ k =>
      have ht : ι R u * TensorAlgebra.tprod R _ (k + 1) y =
          ι R u * ι R (y 0) * TensorAlgebra.tprod R _ k (fun i ↦ y i.succ) := by
        simp [TensorAlgebra.tprod_apply, List.ofFn_succ, mul_assoc]
      rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply, ht,
        cobarHomotopy_ι_mul_ι_mul, hu]
      simp
  exact LinearMap.congr_fun h w

/-- Applying `h` to a cobar coproduct term `(ι ∘ σ_C ⊗ ι) (Δ v)` followed by `w` recovers
`(ι v - ι (ofLetter (letter v))) * w`. -/
private theorem cobarHomotopy_cobarQuadratic_mul (v : ReducedTensorWords R A)
    (w : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarHomotopy 𝒜
        (LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A))
          (TensorProduct.map
            (ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) (ι R)
            (ReducedTensorWords.deconcatenation R A v)) * w) =
      (ι R v - ι R (ReducedTensorWords.ofLetter R A (ReducedTensorWords.letter R A v))) * w := by
  have hq : ∀ z : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A,
      cobarHomotopy 𝒜 (LinearMap.mul' R _
        (TensorProduct.map
          (ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) (ι R) z) * w) =
        ι R (TensorProduct.lift (ReducedTensorWords.prepend R A)
          (TensorProduct.map (ReducedTensorWords.letter R A) LinearMap.id z)) * w := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul u₁ u₂ =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply,
        cobarHomotopy_ι_mul_ι_mul, ReducedTensorWords.koszulTwist_grading,
        ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
        ReducedTensorWords.letter_comp_map, InternalGrading.koszulTwist_koszulTwist,
        LinearMap.id_apply, TensorProduct.lift.tmul]
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, add_mul, h₁, h₂]
  rw [hq, lift_prepend_letter_deconcatenation, map_sub]

/-- Left-multiplying a cobar coproduct term by `ι (σ_C v₁)` and right-multiplying by `w`, then
applying `h`, prepends `letter v₁` to the first factor of the coproduct. -/
private theorem cobarHomotopy_ι_mul_cobarQuadratic_mul (v₁ v₂ : ReducedTensorWords R A)
    (w : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarHomotopy 𝒜
        (ι R ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 v₁) *
          (LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A))
            (TensorProduct.map
              (ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) (ι R)
              (ReducedTensorWords.deconcatenation R A v₂)) * w)) =
      LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A))
        (TensorProduct.map
          (ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) (ι R)
          (LinearMap.rTensor (ReducedTensorWords R A)
            (ReducedTensorWords.prepend R A
              ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A v₁)))
            (ReducedTensorWords.deconcatenation R A v₂))) * w := by
  have hq : ∀ z : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A,
      cobarHomotopy 𝒜
        (ι R ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 v₁) *
          (LinearMap.mul' R _
            (TensorProduct.map
              (ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) (ι R) z) *
            w)) =
        LinearMap.mul' R _
          (TensorProduct.map
            (ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) (ι R)
            (LinearMap.rTensor (ReducedTensorWords R A)
              (ReducedTensorWords.prepend R A
                ((𝒜.grading.shift 1).koszulTwist 1
                  (ReducedTensorWords.letter R A v₁))) z)) * w := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul u₁ u₂ =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply,
        LinearMap.rTensor_tmul]
      rw [← mul_assoc, ← mul_assoc, mul_assoc (ι R _ * ι R _), cobarHomotopy_ι_mul_ι_mul]
      simp only [ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_prepend,
        ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
        ReducedTensorWords.letter_comp_map, LinearMap.comp_apply,
        InternalGrading.koszulTwist_koszulTwist, mul_assoc]
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, mul_add, add_mul, h₁, h₂]
  exact hq _

private theorem cobarAugmentation_cobarHomotopy (x : TensorAlgebra R (ReducedTensorWords R A)) :
    𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation (cobarHomotopy 𝒜 x) = 0 := by
  have h : 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.toGradedAlgHom.toAlgHom.toLinearMap ∘ₗ
      cobarHomotopy 𝒜 = 0 := by
    refine tensorAlgebra_linearMap_ext_three ?_ (fun v ↦ ?_) (fun v₁ v₂ w ↦ ?_)
    · simp [cobarHomotopy_one]
    · simp [cobarHomotopy_ι]
    · simp only [LinearMap.comp_apply, LinearMap.zero_apply, cobarHomotopy_ι_mul_ι_mul,
        AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom]
      -- Expose the augmentation morphism so `map_mul` and `cobarAugmentation_ι` apply.
      change 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation
        (ι R (ReducedTensorWords.prepend R A _ v₂) * w) = 0
      rw [map_mul, 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι, zero_mul]
  exact LinearMap.congr_fun h x

private theorem cobarUnary_proj_comp_dM :
    cobarProj₀ 𝒜 ∘ₗ cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential =
      LinearMap.prodMap (0 : Module.End R R) 𝒜.differential ∘ₗ cobarProj₀ 𝒜 := by
  have haug_d (x : TensorAlgebra R (ReducedTensorWords R A)) :
      𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation
        (cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
          (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential x) = 0 := by
    rw [← cobarAugmentation_unaryBar_eq 𝒜]
    exact 𝒜.isNonCounitalDGCoalgebra_unaryBar.cobarAugmentation.map_d x
  refine tensorAlgebra_linearMap_ext_three ?_ (fun v ↦ ?_) (fun v₁ v₂ w ↦ ?_)
  · refine Prod.ext ?_ ?_ <;>
      simp only [LinearMap.comp_apply, cobarProj₀_apply, LinearMap.prodMap_apply,
        LinearMap.zero_apply, cobarDifferential_one, map_zero, cobarProjA_one,
        Prod.fst_zero, Prod.snd_zero]
  · refine Prod.ext (by simpa [cobarProj₀_apply] using haug_d (ι R v)) ?_
    simp only [LinearMap.comp_apply, cobarProj₀_apply, LinearMap.prodMap_apply,
      cobarDifferential_ι, map_sub, Prod.snd_sub, cobarProjA_ι]
    have hq : ∀ z : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A,
        cobarProjA 𝒜 (LinearMap.mul' R _
          (TensorProduct.map
            (ι R ∘ₗ (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1) (ι R) z)) =
          0 := fun z ↦ by
      induction z using TensorProduct.inductionOn with
      | tmul u₁ u₂ => simpa using cobarProjA_ι_mul_ι_mul 𝒜 _ u₂ 1
      | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]
    rw [hq, zero_sub, ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
      letter_comp_unaryBarDifferential, LinearMap.comp_apply, LinearMap.comp_apply,
      taylor_ofLetter, differential_apply, differential_koszulTwist_shift_one]
  · refine Prod.ext (by simpa [cobarProj₀_apply] using haug_d _) ?_
    simp only [LinearMap.comp_apply, cobarProj₀_apply, LinearMap.prodMap_apply,
      cobarProjA_ι_mul_ι_mul, map_zero]
    rw [mul_assoc, cobarDifferential_mul_eq, map_add]
    have h2 : 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation (ι R v₂ * w) = 0 := by
      rw [map_mul, 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι, zero_mul]
    have h3 : 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation
        (koszulTwistAlgEquiv
          (tensorAlgebraPiece ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1)))
          1 (ι R v₁)) = 0 := by
      rw [koszulTwistAlgEquiv_cobar_ι, map_neg,
        𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι, neg_zero]
    rw [cobarProjA_mul_of_augmentation_eq_zero 𝒜 (haug_d _) h2,
      cobarProjA_mul_of_augmentation_eq_zero 𝒜 h3 (haug_d _), add_zero]

private theorem cobarUnary_d_homotopy_mul (v₁ v₂ : ReducedTensorWords R A)
    (w : TensorAlgebra R (ReducedTensorWords R A)) :
    let d₀ := cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential
    let a := ReducedTensorWords.letter R A v₁
    let σ := (𝒜.grading.shift 1).koszulTwist 1
    let σC := (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1
    d₀ (cobarHomotopy 𝒜 (ι R v₁ * ι R v₂ * w)) =
      ι R (ReducedTensorWords.ofLetter R A a) * ι R v₂ * w +
      LinearMap.mul' R _ (TensorProduct.map (ι R ∘ₗ σC) (ι R)
        (LinearMap.rTensor (ReducedTensorWords R A) (ReducedTensorWords.prepend R A (σ a))
          (ReducedTensorWords.deconcatenation R A v₂))) * w +
      ι R (ReducedTensorWords.prepend R A (σ (𝒜.m 1 ![a])) v₂) * w -
      ι R (ReducedTensorWords.prepend R A a (𝒜.unaryBarDifferential v₂)) * w -
      ι R (ReducedTensorWords.prepend R A a (σC v₂)) * d₀ w := by
  intro d₀ a σ σC
  dsimp only [d₀]
  rw [cobarHomotopy_ι_mul_ι_mul, cobarDifferential_mul_eq, cobarDifferential_ι,
    ReducedTensorWords.deconcatenation_prepend, map_add, map_add,
    TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply,
    ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_ofLetter,
    InternalGrading.koszulTwist_koszulTwist, unaryBarDifferential_prepend,
    differential_koszulTwist_shift_one, InternalGrading.koszulTwist_koszulTwist,
    map_add, map_neg, koszulTwistAlgEquiv_cobar_ι,
    ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_prepend,
    InternalGrading.koszulTwist_koszulTwist]
  simp only [a, σ, σC, ReducedTensorWords.koszulTwist_grading, LinearMap.neg_apply, map_neg,
    sub_mul, add_mul, neg_mul]
  abel

private theorem cobarUnary_homotopy_d_mul (v₁ v₂ : ReducedTensorWords R A)
    (w : TensorAlgebra R (ReducedTensorWords R A)) :
    let d₀ := cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential
    let a := ReducedTensorWords.letter R A v₁
    let σ := (𝒜.grading.shift 1).koszulTwist 1
    let σC := (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1
    cobarHomotopy 𝒜 (d₀ (ι R v₁ * ι R v₂ * w)) =
      (ι R v₁ - ι R (ReducedTensorWords.ofLetter R A a)) * (ι R v₂ * w) -
      ι R (ReducedTensorWords.prepend R A (σ (𝒜.m 1 ![a])) v₂) * w -
      LinearMap.mul' R _ (TensorProduct.map (ι R ∘ₗ σC) (ι R)
        (LinearMap.rTensor (ReducedTensorWords R A) (ReducedTensorWords.prepend R A (σ a))
          (ReducedTensorWords.deconcatenation R A v₂))) * w +
      ι R (ReducedTensorWords.prepend R A a (𝒜.unaryBarDifferential v₂)) * w +
      ι R (ReducedTensorWords.prepend R A a (σC v₂)) * d₀ w := by
  intro d₀ a σ σC
  dsimp only [d₀]
  rw [mul_assoc, cobarDifferential_mul_eq, cobarDifferential_mul_eq, koszulTwistAlgEquiv_cobar_ι,
    koszulTwistAlgEquiv_cobar_ι, cobarDifferential_ι, cobarDifferential_ι]
  simp only [sub_mul, mul_add, mul_sub, neg_mul, mul_neg, neg_neg, map_add, map_sub, map_neg]
  rw [cobarHomotopy_cobarQuadratic_mul, cobarHomotopy_ι_mul_cobarQuadratic_mul,
    ← mul_assoc (ι R (𝒜.unaryBarDifferential v₁)), cobarHomotopy_ι_mul_ι_mul,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R A), letter_comp_unaryBarDifferential,
    LinearMap.comp_apply, LinearMap.comp_apply, taylor_ofLetter,
    ← mul_assoc (ι R (σC v₁)), cobarHomotopy_ι_mul_ι_mul,
    ← mul_assoc (ι R (σC v₁)), cobarHomotopy_ι_mul_ι_mul]
  have hσa : σ (ReducedTensorWords.letter R A (σC v₁)) = a := by
    simp [σC, σ, a, ReducedTensorWords.koszulTwist_grading,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R A)]
  rw [hσa]
  simp only [a, σ, σC, sub_mul]
  abel

private theorem cobarUnary_homotopy_eq_on_mul (v₁ v₂ : ReducedTensorWords R A)
    (w : TensorAlgebra R (ReducedTensorWords R A)) :
    let d₀ := cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential
    d₀ (cobarHomotopy 𝒜 (ι R v₁ * ι R v₂ * w)) +
        cobarHomotopy 𝒜 (d₀ (ι R v₁ * ι R v₂ * w)) =
      ι R v₁ * ι R v₂ * w := by
  intro d₀
  rw [cobarUnary_d_homotopy_mul 𝒜 v₁ v₂ w, cobarUnary_homotopy_d_mul 𝒜 v₁ v₂ w]
  simp only [sub_mul, mul_assoc]
  abel

private theorem cobarUnary_dM_comp_incl :
    cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential ∘ₗ cobarIncl 𝒜 =
      cobarIncl 𝒜 ∘ₗ LinearMap.prodMap (0 : Module.End R R) 𝒜.differential := by
  apply LinearMap.ext
  rintro ⟨r, a⟩
  simp only [LinearMap.comp_apply, cobarIncl_apply, LinearMap.prodMap_apply, LinearMap.zero_apply,
    map_add, cobarDifferential_algebraMap, zero_add, toCobarBar_linearPart_apply,
    cobarDifferential_ι, ReducedTensorWords.deconcatenation_ofLetter, map_zero, zero_sub,
    unaryBarDifferential_ofLetter, differential_koszulTwist_shift_one, differential_apply,
    map_neg, neg_neg]

private theorem cobarUnary_proj_comp_incl :
    cobarProj₀ 𝒜 ∘ₗ cobarIncl 𝒜 = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨r, a⟩
  refine Prod.ext ?_ ?_
  · simp [cobarProj₀_apply, cobarIncl_apply]
  · simp [cobarProj₀_apply, cobarIncl_apply, cobarProjA_algebraMap, cobarProjA_ι,
      ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_ofLetter]

private theorem cobarUnary_homotopy_eq :
    cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential ∘ₗ cobarHomotopy 𝒜 +
      cobarHomotopy 𝒜 ∘ₗ cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential =
      LinearMap.id - cobarIncl 𝒜 ∘ₗ cobarProj₀ 𝒜 := by
  refine tensorAlgebra_linearMap_ext_three ?_ (fun v ↦ ?_) (fun v₁ v₂ w ↦ ?_)
  · simp [cobarHomotopy_one, cobarProj₀_apply, cobarIncl_apply, cobarProjA_one]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, cobarHomotopy_ι, map_zero, zero_add, cobarDifferential_ι, map_sub,
      sub_zero, cobarProj₀_apply, cobarIncl_apply,
      𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι, cobarProjA_ι,
      toCobarBar_linearPart_apply, InternalGrading.koszulTwist_koszulTwist]
    simpa using cobarHomotopy_cobarQuadratic_mul 𝒜 v 1
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, cobarProj₀_apply, cobarIncl_apply, cobarProjA_ι_mul_ι_mul, map_mul,
      𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation_ι, zero_mul, map_zero, add_zero,
      sub_zero]
    exact cobarUnary_homotopy_eq_on_mul 𝒜 v₁ v₂ w

private theorem cobarUnary_proj_comp_homotopy :
    cobarProj₀ 𝒜 ∘ₗ cobarHomotopy 𝒜 = 0 := by
  refine tensorAlgebra_linearMap_ext_three ?_ (fun v ↦ ?_) (fun v₁ v₂ w ↦ ?_)
  · simp [cobarHomotopy_one]
  · simp [cobarHomotopy_ι]
  · refine Prod.ext (cobarAugmentation_cobarHomotopy 𝒜 _) ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, cobarProj₀_apply,
      cobarHomotopy_ι_mul_ι_mul]
    have h : cobarProjA 𝒜 ∘ₗ LinearMap.mulLeft R
        (ι R (ReducedTensorWords.prepend R A
          ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A v₁)) v₂)) = 0 := by
      refine TensorAlgebra.linearMap_ext_tprod fun n y ↦ ?_
      cases n with
      | zero =>
        simp [TensorAlgebra.tprod_apply, cobarProjA_ι]
      | succ k =>
        have ht : ι R (ReducedTensorWords.prepend R A
            ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A v₁)) v₂) *
            TensorAlgebra.tprod R _ (k + 1) y =
          ι R (ReducedTensorWords.prepend R A
            ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A v₁)) v₂) *
            ι R (y 0) * TensorAlgebra.tprod R _ k (fun i ↦ y i.succ) := by
          simp [TensorAlgebra.tprod_apply, List.ofFn_succ, mul_assoc]
        rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply, ht,
          cobarProjA_ι_mul_ι_mul]
    exact LinearMap.congr_fun h w

private theorem cobarUnary_homotopy_comp_homotopy :
    cobarHomotopy 𝒜 ∘ₗ cobarHomotopy 𝒜 = 0 := by
  refine tensorAlgebra_linearMap_ext_three ?_ (fun v ↦ ?_) (fun v₁ v₂ w ↦ ?_)
  · simp [cobarHomotopy_one]
  · simp [cobarHomotopy_ι]
  · simp only [LinearMap.comp_apply, LinearMap.zero_apply, cobarHomotopy_ι_mul_ι_mul]
    exact cobarHomotopy_ι_mul_of_letter_eq_zero 𝒜 (ReducedTensorWords.letter_prepend _ _) w

/-- The unperturbed special contraction of `(Ω Tᶜ(sA), d₀)` onto `(R × A, (0, 𝒜.differential))`. -/
noncomputable def cobarUnaryContraction :
    LinearSpecialContraction
      (cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential)
      (LinearMap.prodMap (0 : Module.End R R) 𝒜.differential) where
  incl := cobarIncl 𝒜
  proj := cobarProj₀ 𝒜
  homotopy := cobarHomotopy 𝒜
  dM_comp_incl := cobarUnary_dM_comp_incl 𝒜
  proj_comp_dM := cobarUnary_proj_comp_dM 𝒜
  proj_comp_incl := cobarUnary_proj_comp_incl 𝒜
  dM_comp_homotopy_add_homotopy_comp_dM := cobarUnary_homotopy_eq 𝒜
  homotopy_comp_incl := LinearMap.ext fun ⟨_, _⟩ ↦ by
    simp [cobarIncl_apply, cobarHomotopy_algebraMap, cobarHomotopy_ι]
  proj_comp_homotopy := cobarUnary_proj_comp_homotopy 𝒜
  homotopy_comp_homotopy := cobarUnary_homotopy_comp_homotopy 𝒜

/-- The inclusion of the unperturbed cobar--bar contraction sends `(r, a)` to
`algebraMap R _ r + 𝒜.toCobarBar.linearPart a`. -/
@[simp]
theorem cobarUnaryContraction_incl (r : R) (a : A) :
    𝒜.cobarUnaryContraction.incl (r, a) = algebraMap R _ r + 𝒜.toCobarBar.linearPart a :=
  (rfl)

/-- The scalar coordinate of the unperturbed cobar--bar projection is the canonical cobar
augmentation. -/
@[simp]
theorem fst_cobarUnaryContraction_proj (x : TensorAlgebra R (ReducedTensorWords R A)) :
    (𝒜.cobarUnaryContraction.proj x).1 =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation x :=
  (rfl)

/-- The contracting homotopy of `cobarUnaryContraction` annihilates `1`. -/
@[simp]
theorem cobarUnaryContraction_homotopy_one :
    𝒜.cobarUnaryContraction.homotopy 1 = 0 :=
  cobarHomotopy_one 𝒜

/-- The contracting homotopy of `cobarUnaryContraction` annihilates scalars. -/
@[simp]
theorem cobarUnaryContraction_homotopy_algebraMap (r : R) :
    𝒜.cobarUnaryContraction.homotopy (algebraMap R _ r) = 0 :=
  cobarHomotopy_algebraMap 𝒜 r

/-- The contracting homotopy of `cobarUnaryContraction` annihilates generators. -/
@[simp]
theorem cobarUnaryContraction_homotopy_ι (v : ReducedTensorWords R A) :
    𝒜.cobarUnaryContraction.homotopy (ι R v) = 0 :=
  cobarHomotopy_ι 𝒜 v

/-- Formula for the contracting homotopy of `cobarUnaryContraction` on a pure tensor of length
`k + 2`. -/
theorem cobarUnaryContraction_homotopy_tprod_add_two (k : ℕ)
    (x : Fin (k + 2) → ReducedTensorWords R A) :
    𝒜.cobarUnaryContraction.homotopy (TensorAlgebra.tprod R _ (k + 2) x) =
      ι R (ReducedTensorWords.prepend R A
        ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A (x 0))) (x 1)) *
        TensorAlgebra.tprod R _ k (fun i : Fin k ↦ x i.succ.succ) :=
  cobarHomotopy_tprod_add_two 𝒜 k x

/-- The contracting homotopy of `cobarUnaryContraction` maps into the augmentation ideal. -/
@[simp]
theorem cobarAugmentation_cobarUnaryContraction_homotopy
    (x : TensorAlgebra R (ReducedTensorWords R A)) :
    𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation (𝒜.cobarUnaryContraction.homotopy x) = 0 :=
  cobarAugmentation_cobarHomotopy 𝒜 x

end Unperturbed

end TauCeti.AInfinityAlgebra
