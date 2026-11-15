/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Inverse
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Cohomology
public import TauCeti.Algebra.Homology.Contraction.Linear.TensorProduct
public import TauCeti.Algebra.Homology.Contraction.Perturbation
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.BicofreeHom

/-!
# Homological transfer of A-infinity bimodules

Let `M` be an `(A, B)` `A∞` bimodule over `A∞` algebras `A` and `B`, and let `(i, p, h)` be a
special contraction of `(M, m_{0,0})` onto a graded module `(N, d_N)`, with `h` of degree `-1` and
`i`, `p` of degree zero.  The bimodule is stored on its cofree bar bicomodule
`(Tᶜ(sA) ⊗ sM) ⊗ Tᶜ(sB)` by a square-zero degree-one coderivation `D` over the bar differentials
`b_A` and `b_B`.  Split `D = D₀ + δ`, where

`D₀ = (b_A ⊗ 1 + τ_A ⊗ m_{0,0}) ⊗ 1 + (1 ⊗ b_B) ∘ (τ_{A,M} ⊗ 1)`

(`TauCeti.AInfinityBimodule.unaryBarDifferential`) only involves the unary bimodule differential,
with `τ_A` and `τ_{A,M}` the Koszul twists of `Tᶜ(sA)` and `Tᶜ(sA) ⊗ sM`, and the *higher* part
`δ` (`TauCeti.AInfinityBimodule.higherBarDifferential`) applies the operations `b_{i,j}` with
`i + j ≥ 1` to inner subwords.  Thus `δ` strictly lowers total word length `i + j`; it commutes
with the right coaction of `Tᶜ(sB)`, and intertwines the left coaction of `Tᶜ(sA)` up to the Koszul
twist `τ_A`.

Tensoring `(i, p, h)` first on the left with `(Tᶜ(sA), b_A)` and then on the right with
`(Tᶜ(sB), b_B)` produces the special contraction

`((1 ⊗ i) ⊗ 1, (1 ⊗ p) ⊗ 1, (τ_A ⊗ h) ⊗ 1)`

of `(Tᶜ(sA) ⊗ sM) ⊗ Tᶜ(sB)` onto `(Tᶜ(sA) ⊗ sN) ⊗ Tᶜ(sB)` for the unary bar differentials
(`TauCeti.AInfinityBimodule.barContraction`).  Because `(τ_A ⊗ h) ⊗ 1` preserves both word lengths,
`δ ∘ ((τ_A ⊗ h) ⊗ 1)` strictly lowers total word length and is therefore locally nilpotent, so the
perturbation operator `X = (1 + δ ((τ_A ⊗ h) ⊗ 1))⁻¹ δ` exists.  Moreover both `δ` and
`(τ_A ⊗ h) ⊗ 1` twist the left coaction by `τ_A`; since `τ_A² = 1`, their composite
`δ ((τ_A ⊗ h) ⊗ 1)` and its inverse `(1 + δ ((τ_A ⊗ h) ⊗ 1))⁻¹` commute strictly with both
coactions.  Hence:

* `X` commutes strictly with the right coaction and twists the left coaction by `τ_A`, so the
  perturbed differential `D' = D₀' + ((1 ⊗ p) ⊗ 1) X ((1 ⊗ i) ⊗ 1)` is again a square-zero
  coderivation over `b_A` and `b_B`, giving the *transferred* `A∞` bimodule structure on `N`
  (`TauCeti.AInfinityBimodule.transfer`) with unary differential `d_N`;
* in the perturbed inclusion `i' = (1 ⊗ i) ⊗ 1 - ((τ_A ⊗ h) ⊗ 1) X ((1 ⊗ i) ⊗ 1)` and projection
  `p' = (1 ⊗ p) ⊗ 1 - ((1 ⊗ p) ⊗ 1) X ((τ_A ⊗ h) ⊗ 1)`, the two Koszul twists `τ_A` cancel again,
  so `i'` and `p'` commute strictly with both coactions and define quasi-isomorphisms of `A∞`
  bimodules (`TauCeti.AInfinityBimodule.transferInclusion` and
  `TauCeti.AInfinityBimodule.transferProjection`) with linear parts `i` and `p`, satisfying
  `p' ∘ i' = id`.

The architecture parallels `TauCeti.AInfinityRightModule.transfer` in
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Transfer`.

## Main definitions

* `TauCeti.AInfinityBimodule.unaryBarDifferential`: the unary part of a bimodule bar differential.
* `TauCeti.AInfinityBimodule.higherBarDifferential`: the higher part `D - D₀` of the bar
  differential.
* `TauCeti.AInfinityBimodule.barContraction`: the special contraction of two-sided bar
  constructions induced by a special contraction of the bimodule carrier.
* `TauCeti.AInfinityBimodule.transferBarDifferential`: the perturbed bar differential `D'`.
* `TauCeti.AInfinityBimodule.transferContraction`: the perturbed contraction of bar bicomodules.
* `TauCeti.AInfinityBimodule.transfer`: the transferred `(A, B)` `A∞` bimodule structure on `N`.
* `TauCeti.AInfinityBimodule.transferInclusion` and
  `TauCeti.AInfinityBimodule.transferProjection`: the extending and projecting morphisms of `A∞`
  bimodules.

## Main results

* `TauCeti.AInfinityBimodule.isUnit_one_add_higherBarDifferential_mul`: the invertibility
  hypothesis for the basic perturbation lemma on the two-sided bar bicomodule.
* `TauCeti.AInfinityBimodule.barDifferential_transfer` and
  `TauCeti.AInfinityBimodule.differential_transfer`: the bar and unary differentials of the
  transferred bimodule.
* `TauCeti.AInfinityBimodule.linearPart_transferInclusion`,
  `TauCeti.AInfinityBimodule.linearPart_transferProjection`, and
  `TauCeti.AInfinityBimodule.transferProjection_comp_transferInclusion`: the linear parts of the
  transfer morphisms are `i` and `p`, and the projection retracts the inclusion.
* `TauCeti.AInfinityBimodule.isQuasiIso_transferInclusion` and
  `TauCeti.AInfinityBimodule.isQuasiIso_transferProjection`: both transfer morphisms are
  quasi-isomorphisms.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

open scoped TensorProduct

universe uR uA uB uM uN

namespace TauCeti

open TensorWords

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace AInfinityBimodule

attribute [local instance] Comodule.cofree

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-! ### Homogeneity and coaction helpers for two-sided bar operators -/

/-- A homogeneous map `f : P → Q` tensored with identities on both word factors has the same degree
between the two-sided bar gradings. -/
theorem isHomogeneous_lTensor_rTensor {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] {GP : InternalGrading R P ℤ} {GQ : InternalGrading R Q ℤ}
    {q : ℤ} {f : P →ₗ[R] Q} (hf : LinearMap.IsHomogeneous f GP.piece GQ.piece q) :
    LinearMap.IsHomogeneous ((f.lTensor (TensorWords R A)).rTensor (TensorWords R B))
      (barGrading AA BB GP).piece (barGrading AA BB GQ).piece q := by
  let WA := TensorWords.grading (AA.grading.shift 1)
  let WB := TensorWords.grading (BB.grading.shift 1)
  have hf' : LinearMap.IsHomogeneous f (GP.shift 1).piece (GQ.shift 1).piece q :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hf
  rw [barGrading_def, barGrading_def, LinearMap.lTensor_def, LinearMap.rTensor_def]
  simpa only [zero_add, add_zero] using
    ((LinearMap.isHomogeneous_id WA.piece).tensorProduct hf').tensorProduct
      (LinearMap.isHomogeneous_id WB.piece)

/-- A homogeneous map `f : P → Q` tensored with the Koszul twist on the left word factor and the
identity on the right word factor has the same degree between the two-sided bar gradings. -/
theorem isHomogeneous_map_koszulTwist_rTensor {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] {GP : InternalGrading R P ℤ} {GQ : InternalGrading R Q ℤ}
    {q : ℤ} (r : ℤ) {f : P →ₗ[R] Q} (hf : LinearMap.IsHomogeneous f GP.piece GQ.piece q) :
    LinearMap.IsHomogeneous
      ((TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist r) f).rTensor
        (TensorWords R B))
      (barGrading AA BB GP).piece (barGrading AA BB GQ).piece q := by
  let WA := TensorWords.grading (AA.grading.shift 1)
  let WB := TensorWords.grading (BB.grading.shift 1)
  have hτ : LinearMap.IsHomogeneous (WA.koszulTwist r) WA.piece WA.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
      simpa only [add_zero] using WA.koszulTwist_mem_piece hx r
  have hf' : LinearMap.IsHomogeneous f (GP.shift 1).piece (GQ.shift 1).piece q :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hf
  rw [barGrading_def, barGrading_def, LinearMap.rTensor_def]
  simpa only [zero_add, add_zero] using
    (hτ.tensorProduct hf').tensorProduct (LinearMap.isHomogeneous_id WB.piece)

/-- A map `(τ_A ⊗ f) ⊗ 1` intertwines the extended left coactions with `τ_A ⊗ -`. -/
private theorem leftCoact_comp_map_koszulTwist_rTensor {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (f : P →ₗ[R] Q) :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) Q) ∘ₗ
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) f).rTensor
        (TensorWords R B) =
    TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
      ((TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) f).rTensor
        (TensorWords R B)) ∘ₗ
      Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) P) := by
  have hτ : Coalgebra.comul ∘ₗ (TensorWords.grading (AA.grading.shift 1)).koszulTwist 1 =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
        ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) ∘ₗ Coalgebra.comul := by
    rw [koszulTwist_grading, comul_eq_deconcatenation, deconcatenation_natural]
  simpa only [LinearMap.lTensor_id, LinearMap.id_comp] using
    Comodule.leftCoactRTensor_comp_lTensor_comp_rTensor_map (N := TensorWords R B)
      (N' := TensorWords R B) hτ f LinearMap.id

/-- Composing two maps that each intertwine left coactions up to an involutive Koszul twist gives a
map commuting strictly with the left coactions. -/
private theorem leftCoact_comp_comp_of_koszulTwist {X Y Z : Type*}
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y] [AddCommMonoid Z] [Module R Z]
    {δX : X →ₗ[R] TensorWords R A ⊗[R] X} {δY : Y →ₗ[R] TensorWords R A ⊗[R] Y}
    {δZ : Z →ₗ[R] TensorWords R A ⊗[R] Z} {G : Y →ₗ[R] Z} {F : X →ₗ[R] Y}
    (hG : δZ ∘ₗ G =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) G ∘ₗ δY)
    (hF : δY ∘ₗ F =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) F ∘ₗ δX) :
    δZ ∘ₗ (G ∘ₗ F) = (G ∘ₗ F).lTensor (TensorWords R A) ∘ₗ δX := by
  rw [← LinearMap.comp_assoc, hG, LinearMap.comp_assoc, hF, ← LinearMap.comp_assoc,
    ← TensorProduct.map_comp, InternalGrading.koszulTwist_comp_self, LinearMap.lTensor_def]

/-! ### The unary and higher parts of the bar differential -/

section Unary

variable (AA BB) (G : InternalGrading R M ℤ) (d : Module.End R M)

/-- The **unary part** `(b_A ⊗ 1 + τ_A ⊗ d) ⊗ 1 + (1 ⊗ b_B) ∘ (τ_{A,M} ⊗ 1)` of a bimodule bar
differential with unary operation `d`: the left bar differential `b_A`, the operator `d` twisted
past the left word, and the right bar differential `b_B` twisted past both the left word and the
suspended module input.  For an `A∞` bimodule and `d = m_{0,0}` this is the part of the bar
differential using no higher bimodule operations. -/
noncomputable def unaryBarDifferential :
    Module.End R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :=
  (AA.coaugmentedBarDifferential.rTensor M +
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) d).rTensor
    (TensorWords R B) +
    BB.coaugmentedBarDifferential.lTensor (TensorWords R A ⊗[R] M) ∘ₗ
      (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (G.shift 1)).koszulTwist
        1).rTensor (TensorWords R B)

/-- Defining formula for `unaryBarDifferential`. -/
theorem unaryBarDifferential_def :
    unaryBarDifferential AA BB G d =
      (AA.coaugmentedBarDifferential.rTensor M +
          TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) d).rTensor
        (TensorWords R B) +
        BB.coaugmentedBarDifferential.lTensor (TensorWords R A ⊗[R] M) ∘ₗ
          (((TensorWords.grading (AA.grading.shift 1)).tensorProduct (G.shift 1)).koszulTwist
            1).rTensor (TensorWords R B) :=
  (rfl)

/-- The unary bar differential evaluated on a pure tensor `(w ⊗ x) ⊗ v`. -/
@[simp]
theorem unaryBarDifferential_tmul (w : TensorWords R A) (x : M) (v : TensorWords R B) :
    unaryBarDifferential AA BB G d ((w ⊗ₜ[R] x) ⊗ₜ[R] v) =
      (AA.coaugmentedBarDifferential w ⊗ₜ[R] x +
          (TensorWords.grading (AA.grading.shift 1)).koszulTwist 1 w ⊗ₜ[R] d x) ⊗ₜ[R] v +
        ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1 w ⊗ₜ[R]
          (G.shift 1).koszulTwist 1 x) ⊗ₜ[R] BB.coaugmentedBarDifferential v := by
  simp [unaryBarDifferential_def, InternalGrading.koszulTwist_tensorProduct, TensorProduct.add_tmul]

/-- On the two empty words, the unary bar differential applies `d` to the module input. -/
theorem unaryBarDifferential_one_tmul_tmul_one (x : M) :
    unaryBarDifferential AA BB G d
      (((1 : TensorWords R A) ⊗ₜ[R] x) ⊗ₜ[R] (1 : TensorWords R B)) =
      ((1 : TensorWords R A) ⊗ₜ[R] d x) ⊗ₜ[R] (1 : TensorWords R B) := by
  simp

/-- The unary part is the bicomodule coderivation generated by `d ∘ taylorProj`. -/
theorem unaryBarDifferential_eq_gradedCoderiv :
    unaryBarDifferential AA BB G d = gradedCoderiv AA BB G (d ∘ₗ taylorProj R A B M) := by
  set πB := (TensorProduct.rid R (TensorWords R A ⊗[R] M)).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := TensorWords R B)).lTensor (TensorWords R A ⊗[R] M)
  have hπB : Comodule.leftCofreeCoact R (TensorWords R A) M ∘ₗ πB =
      πB.lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) :=
    Comodule.comp_rid_comp_lTensor_eq_lTensor_comp_leftCoactRTensor _ _
  have hL : leftTaylor AA (d ∘ₗ taylorProj R A B M) =
      (AA.coaugmentedBarDifferential.rTensor M +
        TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) d) ∘ₗ πB := by
    rw [leftTaylor_def, taylorProj_def, ← koszulTwist_grading]
    set τ := (TensorWords.grading (AA.grading.shift 1)).koszulTwist 1
    have h1 : TensorProduct.map τ
          (d ∘ₗ Comodule.leftCofreeCounit R (TensorWords R A) M ∘ₗ πB) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) =
      TensorProduct.map τ d ∘ₗ πB := by
      calc
        TensorProduct.map τ (d ∘ₗ Comodule.leftCofreeCounit R (TensorWords R A) M ∘ₗ πB) ∘ₗ
            Comodule.leftCoactRTensor (TensorWords R B)
              (Comodule.leftCofreeCoact R (TensorWords R A) M)
          = TensorProduct.map τ d ∘ₗ
              (Comodule.leftCofreeCounit R (TensorWords R A) M).lTensor (TensorWords R A) ∘ₗ
              (πB.lTensor (TensorWords R A) ∘ₗ
                Comodule.leftCoactRTensor (TensorWords R B)
                  (Comodule.leftCofreeCoact R (TensorWords R A) M)) := by
            simp only [← LinearMap.comp_assoc, LinearMap.map_comp_lTensor]
        _ = TensorProduct.map τ d ∘ₗ
              ((Comodule.leftCofreeCounit R (TensorWords R A) M).lTensor (TensorWords R A) ∘ₗ
                Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ πB := by
            rw [← hπB]
            simp only [LinearMap.comp_assoc]
        _ = TensorProduct.map τ d ∘ₗ πB := by
            rw [Comodule.lTensor_leftCofreeCounit_comp_leftCofreeCoact, LinearMap.id_comp]
    rw [h1, LinearMap.add_comp, add_comm]
  rw [gradedCoderiv_def, ← Comodule.cofreeCoact_def, hL, LinearMap.rTensor_comp,
    LinearMap.comp_assoc, Comodule.rTensor_rid_comp_lTensor_counit_comp_cofreeCoact,
    LinearMap.comp_id, ← koszulTwist_grading, ← InternalGrading.koszulTwist_tensorProduct,
    unaryBarDifferential_def]

/-- The unary part is a left graded coderivation over the bar differential of `AA`. -/
theorem isLeftGradedCoderivationOver_unaryBarDifferential :
    Comodule.IsLeftGradedCoderivationOver
      (Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M))
      (TensorWords.grading (AA.grading.shift 1)) 1 AA.coaugmentedBarDifferential
      (unaryBarDifferential AA BB G d) := by
  rw [unaryBarDifferential_eq_gradedCoderiv]
  exact isLeftGradedCoderivationOver_gradedCoderiv AA BB G _

/-- The unary part is a right graded coderivation over the bar differential of `BB`. -/
theorem isGradedCoderivationOver_unaryBarDifferential :
    Comodule.IsGradedCoderivationOver (barGrading AA BB G) 1 BB.coaugmentedBarDifferential
      (unaryBarDifferential AA BB G d) := by
  rw [unaryBarDifferential_eq_gradedCoderiv]
  exact isGradedCoderivationOver_gradedCoderiv AA BB G _

variable {d}

/-- The unary part has degree one when `d` has degree one for the suspended grading. -/
theorem isHomogeneous_unaryBarDifferential
    (hd : LinearMap.IsHomogeneous d (G.shift 1).piece (G.shift 1).piece 1) :
    LinearMap.IsHomogeneous (unaryBarDifferential AA BB G d) (barGrading AA BB G).piece
      (barGrading AA BB G).piece 1 := by
  rw [unaryBarDifferential_eq_gradedCoderiv]
  refine isHomogeneous_gradedCoderiv AA BB G ?_
  have hproj : LinearMap.IsHomogeneous (taylorProj R A B M) (barGrading AA BB G).piece
      (G.shift 1).piece 0 := by
    simpa only [LinearMap.comp_id] using
      isHomogeneous_taylorProj_comp (LinearMap.isHomogeneous_id (barGrading AA BB G).piece)
  simpa only [zero_add] using hd.comp hproj

/-- The unary part squares to zero when `d` has degree one and squares to zero. -/
theorem unaryBarDifferential_comp_self
    (hd : LinearMap.IsHomogeneous d (G.shift 1).piece (G.shift 1).piece 1)
    (hdd : d ∘ₗ d = 0) :
    unaryBarDifferential AA BB G d ∘ₗ unaryBarDifferential AA BB G d = 0 := by
  refine (barDifferential_sq_iff_taylor_comp_eq_zero G (unaryBarDifferential AA BB G d)
    (isHomogeneous_unaryBarDifferential AA BB G hd)
    (isLeftGradedCoderivationOver_unaryBarDifferential AA BB G d)
    (isGradedCoderivationOver_unaryBarDifferential AA BB G d)).2 ?_
  have ht : taylorProj R A B M ∘ₗ unaryBarDifferential AA BB G d = d ∘ₗ taylorProj R A B M := by
    rw [unaryBarDifferential_eq_gradedCoderiv, taylorProj_comp_gradedCoderiv]
  rw [← LinearMap.comp_assoc, ht, LinearMap.comp_assoc, ht, ← LinearMap.comp_assoc, hdd,
    LinearMap.zero_comp]

end Unary

variable (MM : AInfinityBimodule AA BB M)

/-- The unary differential of an `A∞` bimodule has degree one for the suspended grading. -/
private theorem isHomogeneous_differential_shift :
    LinearMap.IsHomogeneous MM.differential (MM.grading.shift 1).piece
      (MM.grading.shift 1).piece 1 :=
  LinearMap.isHomogeneous_shift_piece_iff.2 MM.isHomogeneous_differential

/-- The **higher part** of the bar differential of an `A∞` bimodule: the difference `D - D₀`
between the bar differential and its unary part. -/
noncomputable def higherBarDifferential :
    Module.End R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :=
  MM.barDifferential - unaryBarDifferential AA BB MM.grading MM.differential

/-- The higher part is the bar differential minus its unary part. -/
theorem higherBarDifferential_def :
    MM.higherBarDifferential =
      MM.barDifferential - unaryBarDifferential AA BB MM.grading MM.differential :=
  (rfl)

/-- The bar differential is the sum of its unary and higher parts. -/
theorem unaryBarDifferential_add_higherBarDifferential :
    unaryBarDifferential AA BB MM.grading MM.differential + MM.higherBarDifferential =
      MM.barDifferential :=
  add_sub_cancel _ _

/-- The higher part vanishes on the two empty algebra words. -/
@[simp]
theorem higherBarDifferential_one_tmul_tmul_one (x : M) :
    MM.higherBarDifferential
      (((1 : TensorWords R A) ⊗ₜ[R] x) ⊗ₜ[R] (1 : TensorWords R B)) = 0 := by
  rw [higherBarDifferential_def, LinearMap.sub_apply, barDifferential_one_tmul_tmul_one,
    unaryBarDifferential_one_tmul_tmul_one, sub_self]

/-- The higher part has degree one. -/
theorem isHomogeneous_higherBarDifferential :
    LinearMap.IsHomogeneous MM.higherBarDifferential (barGrading AA BB MM.grading).piece
      (barGrading AA BB MM.grading).piece 1 :=
  MM.isHomogeneous_barDifferential.sub
    (isHomogeneous_unaryBarDifferential AA BB MM.grading MM.isHomogeneous_differential_shift)

/-- The higher part commutes with the right coaction: it is the difference of two right
coderivations over the bar differential of `BB`. -/
theorem coact_comp_higherBarDifferential :
    Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) ∘ₗ MM.higherBarDifferential =
      MM.higherBarDifferential.rTensor (TensorWords R B) ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R B)
          (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) := by
  refine LinearMap.ext fun z ↦ ?_
  simp only [higherBarDifferential_def, LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
    MM.isGradedCoderivation_barDifferential.coact_apply z,
    (isGradedCoderivationOver_unaryBarDifferential AA BB MM.grading MM.differential).coact_apply z,
    LinearMap.rTensor_sub]
  abel

/-- The higher part intertwines the left coaction up to the Koszul twist on `Tᶜ(sA)`: it is the
difference of two left coderivations over the bar differential of `AA`. -/
theorem leftCoact_comp_higherBarDifferential :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ MM.higherBarDifferential =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          MM.higherBarDifferential ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) := by
  let : AddCommGroup (TensorWords R A) := inferInstance
  let : AddCommGroup (TensorWords R A ⊗[R] ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)) :=
    inferInstance
  refine LinearMap.ext fun z ↦ ?_
  have h1 := MM.isLeftGradedCoderivation_barDifferential.coact_apply z
  have h2 := (isLeftGradedCoderivationOver_unaryBarDifferential AA BB MM.grading
    MM.differential).coact_apply z
  have hsub : TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
      MM.higherBarDifferential =
    TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
      MM.barDifferential -
    TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
      (unaryBarDifferential AA BB MM.grading MM.differential) :=
    TensorProduct.ext' fun w y ↦ by
      rw [higherBarDifferential_def, TensorProduct.map_tmul, LinearMap.sub_apply,
        TensorProduct.tmul_sub, ← TensorProduct.map_tmul, ← TensorProduct.map_tmul,
        ← LinearMap.sub_apply]
  simp only [higherBarDifferential_def, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, h1, h2]
  rw [← higherBarDifferential_def, hsub, LinearMap.sub_apply]
  abel

/-- On pure tensor words of lengths `(i, j)`, the higher bar differential strictly lowers total
word length `i + j`. -/
theorem higherBarDifferential_of_tprod_mem_bicofreeFiltration
    (i j : ℕ) (a : Fin i → A) (x : M) (b : Fin j → B) :
    MM.higherBarDifferential
      ((of R A i (PiTensorProduct.tprod R a) ⊗ₜ[R] x) ⊗ₜ[R]
        of R B j (PiTensorProduct.tprod R b)) ∈
      bicofreeFiltration R A B M (i + j) := by
  let δR : Comodule.Hom R (TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :=
    ⟨MM.higherBarDifferential, MM.coact_comp_higherBarDifferential.symm⟩
  set τ := (TensorWords.grading (AA.grading.shift 1)).koszulTwist 1 with hτ_def
  set φ := Comodule.leftCofreeCounit R (TensorWords R A) M ∘ₗ
    (TensorProduct.rid R (TensorWords R A ⊗[R] M)).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := TensorWords R B)).lTensor (TensorWords R A ⊗[R] M) ∘ₗ
        MM.higherBarDifferential
  have hφ : φ ((1 ⊗ₜ x) ⊗ₜ 1) = 0 := by
    simp [φ]
  have hδ : MM.higherBarDifferential =
      ((τ.rTensor M).rTensor (TensorWords R B)) ∘ₗ (Comodule.bicofreeLift φ).toLinearMap := by
    have heq := congrArg Comodule.Hom.toLinearMap
      (δR.eq_cofreeLift_of_leftCoact τ MM.leftCoact_comp_higherBarDifferential)
    have hmap : TensorProduct.map τ φ = τ.rTensor M ∘ₗ φ.lTensor (TensorWords R A) := by
      rw [LinearMap.rTensor_def, LinearMap.lTensor_def, ← TensorProduct.map_comp,
        LinearMap.comp_id, LinearMap.id_comp]
    simpa only [δR, φ, Comodule.bicofreeLift_toLinearMap, Comodule.Hom.cofreeLift_toLinearMap,
      Comodule.cofree_coact, Comodule.cofreeCoact_def, hmap, LinearMap.comp_assoc,
      LinearMap.rTensor_comp] using heq
  rw [hδ, LinearMap.comp_apply, of_tprod_eq_subword R a, of_tprod_eq_subword R b,
    Comodule.Hom.coe_toLinearMap, bicofreeLift_apply_subword, Finset.sum_range_succ',
    Finset.sum_range_succ _ i, subword_length_zero R b (Nat.zero_le j), Nat.zero_add i,
    Nat.sub_self, subword_length_zero R a le_rfl, hφ, TensorProduct.tmul_zero,
    TensorProduct.zero_tmul, add_zero, map_add, map_sum, map_sum]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun r hr ↦ ?_)
    (Submodule.sum_mem _ fun l hl ↦ ?_)
  · rw [map_sum]
    refine Submodule.sum_mem _ fun l hl ↦ ?_
    rw [Finset.mem_range] at hr hl
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, hτ_def, koszulTwist_grading, map_subword]
    exact subword_tmul_tmul_subword_mem_bicofreeFiltration _ 0 l _ b (0 + (r + 1)) (j - (r + 1))
      (by omega)
  · rw [Finset.mem_range] at hl
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, hτ_def, koszulTwist_grading, map_subword]
    exact subword_tmul_tmul_subword_mem_bicofreeFiltration _ 0 l _ b 0 j (by omega)

/-- **Local nilpotence.**  Followed by any operator `(map g ⊗ k) ⊗ 1` preserving both word lengths,
the higher bar differential strictly lowers total word length and is therefore locally nilpotent. -/
theorem exists_pow_higherBarDifferential_comp_apply_eq_zero
    (g : Module.End R A) (k : Module.End R M)
    (z : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :
    ∃ n, ((MM.higherBarDifferential ∘ₗ
      (TensorProduct.map (TensorWords.map g) k).rTensor (TensorWords R B)) ^ n) z = 0 :=
  exists_pow_apply_eq_zero_of_of_tprod_mem_bicofreeFiltration _
    (fun i j a x b ↦ by
      rw [LinearMap.comp_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, map_of_tprod]
      exact MM.higherBarDifferential_of_tprod_mem_bicofreeFiltration i j _ (k x) b) z

/-- The unit hypothesis for the perturbation lemma: `1 + δ ((map g ⊗ k) ⊗ 1)` is invertible. -/
theorem isUnit_one_add_higherBarDifferential_mul (g : Module.End R A) (k : Module.End R M) :
    IsUnit (1 + MM.higherBarDifferential *
      (TensorProduct.map (TensorWords.map g) k).rTensor (TensorWords R B)) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
    (MM.exists_pow_higherBarDifferential_comp_apply_eq_zero g k)

/-! ### The bar contraction and the perturbation -/

section Transfer

variable {GN : InternalGrading R N ℤ} {dN : Module.End R N}
  (c : LinearSpecialContraction MM.differential dN)
  (hh : LinearMap.IsHomogeneous c.homotopy MM.grading.piece MM.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GN.piece MM.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj MM.grading.piece GN.piece 0)

include hh hincl hproj in
/-- Contracting equations for the two-sided bar extension of a special contraction, transferred
from `LinearSpecialContraction.lTensor` followed by `LinearSpecialContraction.rTensor`. -/
private theorem barContraction_spec :
    let incl := (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B)
    let proj := (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B)
    let hom := (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
      c.homotopy).rTensor (TensorWords R B)
    let dM₀ := unaryBarDifferential AA BB MM.grading MM.differential
    let dN₀ := unaryBarDifferential AA BB GN dN
    (dM₀ ∘ₗ incl = incl ∘ₗ dN₀) ∧ (proj ∘ₗ dM₀ = dN₀ ∘ₗ proj) ∧ (proj ∘ₗ incl = LinearMap.id) ∧
      (dM₀ ∘ₗ hom + hom ∘ₗ dM₀ = LinearMap.id - incl ∘ₗ proj) ∧
      (hom ∘ₗ incl = 0) ∧ (proj ∘ₗ hom = 0) ∧ (hom ∘ₗ hom = 0) := by
  dsimp only
  let WA := TensorWords.grading (AA.grading.shift 1)
  have hbA : LinearMap.IsHomogeneous AA.coaugmentedBarDifferential WA.piece WA.piece 1 := by
    simpa only [WA, TensorWords.grading_piece] using AA.isHomogeneous_coaugmentedBarDifferential
  let cL := c.lTensor hbA
  have hhL : LinearMap.IsHomogeneous cL.homotopy
      (WA.tensorProduct (MM.grading.shift 1)).piece
      (WA.tensorProduct (MM.grading.shift 1)).piece (-1) := by
    simpa only [cL, LinearSpecialContraction.lTensor_homotopy,
      LinearContraction.lTensor_homotopy] using
      c.toLinearContraction.isHomogeneous_lTensor_homotopy hbA
        (LinearMap.isHomogeneous_shift_piece_iff.2 hh)
  have hinclL : LinearMap.IsHomogeneous cL.incl
      (WA.tensorProduct (GN.shift 1)).piece (WA.tensorProduct (MM.grading.shift 1)).piece 0 := by
    simpa only [cL, LinearSpecialContraction.lTensor_incl, LinearContraction.lTensor_incl] using
      c.toLinearContraction.isHomogeneous_lTensor_incl hbA
        (LinearMap.isHomogeneous_shift_piece_iff.2 hincl)
  have hprojL : LinearMap.IsHomogeneous cL.proj
      (WA.tensorProduct (MM.grading.shift 1)).piece (WA.tensorProduct (GN.shift 1)).piece 0 := by
    simpa only [cL, LinearSpecialContraction.lTensor_proj, LinearContraction.lTensor_proj] using
      c.toLinearContraction.isHomogeneous_lTensor_proj hbA
        (LinearMap.isHomogeneous_shift_piece_iff.2 hproj)
  let cR := cL.rTensor hhL hinclL hprojL BB.coaugmentedBarDifferential
  have hcR_incl : cR.incl = (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
    simp [cR, cL]
  have hcR_proj : cR.proj = (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
    simp [cR, cL]
  have hcR_hom : cR.homotopy = (TensorProduct.map (WA.koszulTwist 1) c.homotopy).rTensor
      (TensorWords R B) := by
    simp [cR, cL]
  refine ⟨by simpa only [WA, hcR_incl, ← unaryBarDifferential_def] using cR.dM_comp_incl,
    by simpa only [WA, hcR_proj, ← unaryBarDifferential_def] using cR.proj_comp_dM,
    by simpa only [hcR_proj, hcR_incl] using cR.proj_comp_incl,
    LinearMap.ext fun z ↦ ?_,
    by simpa only [WA, hcR_hom, hcR_incl] using cR.homotopy_comp_incl,
    by simpa only [WA, hcR_proj, hcR_hom] using cR.proj_comp_homotopy,
    by simpa only [WA, hcR_hom] using cR.homotopy_comp_homotopy⟩
  rw [LinearMap.sub_apply, LinearMap.id_apply, eq_sub_iff_add_eq]
  -- Convert `cR`'s contracting identity to an additive identity under `cR`'s `AddCommGroup`
  -- instance before transporting to `barCarrierAddCommGroup`, whose `AddCommMonoid`s coincide.
  have h_add {Z : Type _} {W : Type _} [AddCommGroup Z] [Module R Z]
      [AddCommGroup W] [Module R W] {dZ : Module.End R Z} {dW : Module.End R W}
      (c' : LinearSpecialContraction dZ dW) (w : Z) :
      (dZ ∘ₗ c'.homotopy + c'.homotopy ∘ₗ dZ) w + (c'.incl ∘ₗ c'.proj) w = w := by
    rw [c'.dM_comp_homotopy_add_homotopy_comp_dM, LinearMap.sub_apply, LinearMap.id_apply,
      sub_add_cancel]
  simpa only [WA, hcR_hom, hcR_incl, hcR_proj, ← unaryBarDifferential_def] using h_add cR z

/-- The **bar contraction**: a special contraction `(i, p, h)` of `(M, m_{0,0})` onto `(N, d_N)`
induces the special contraction `((1 ⊗ i) ⊗ 1, (1 ⊗ p) ⊗ 1, (τ_A ⊗ h) ⊗ 1)` of the two-sided bar
constructions for the unary parts of the bar differentials. -/
noncomputable def barContraction :
    LinearSpecialContraction (unaryBarDifferential AA BB MM.grading MM.differential)
      (unaryBarDifferential AA BB GN dN) where
  incl := (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B)
  proj := (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B)
  homotopy := (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
    c.homotopy).rTensor (TensorWords R B)
  dM_comp_incl := (MM.barContraction_spec c hh hincl hproj).1
  proj_comp_dM := (MM.barContraction_spec c hh hincl hproj).2.1
  proj_comp_incl := (MM.barContraction_spec c hh hincl hproj).2.2.1
  dM_comp_homotopy_add_homotopy_comp_dM := (MM.barContraction_spec c hh hincl hproj).2.2.2.1
  homotopy_comp_incl := (MM.barContraction_spec c hh hincl hproj).2.2.2.2.1
  proj_comp_homotopy := (MM.barContraction_spec c hh hincl hproj).2.2.2.2.2.1
  homotopy_comp_homotopy := (MM.barContraction_spec c hh hincl hproj).2.2.2.2.2.2

/-- The inclusion of the bar contraction is `(1 ⊗ i) ⊗ 1`. -/
@[simp]
theorem barContraction_incl :
    (MM.barContraction c hh hincl hproj).incl =
      (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) :=
  (rfl)

/-- The projection of the bar contraction is `(1 ⊗ p) ⊗ 1`. -/
@[simp]
theorem barContraction_proj :
    (MM.barContraction c hh hincl hproj).proj =
      (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) :=
  (rfl)

/-- The homotopy of the bar contraction is `(τ_A ⊗ h) ⊗ 1`. -/
@[simp]
theorem barContraction_homotopy :
    (MM.barContraction c hh hincl hproj).homotopy =
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
        c.homotopy).rTensor (TensorWords R B) :=
  (rfl)

/-- The bar contraction's inclusion has degree zero in the total suspended grading. -/
theorem isHomogeneous_barContraction_incl :
    LinearMap.IsHomogeneous (MM.barContraction c hh hincl hproj).incl
      (barGrading AA BB GN).piece (barGrading AA BB MM.grading).piece 0 := by
  rw [barContraction_incl]
  exact isHomogeneous_lTensor_rTensor hincl

/-- The bar contraction's projection has degree zero in the total suspended grading. -/
theorem isHomogeneous_barContraction_proj :
    LinearMap.IsHomogeneous (MM.barContraction c hh hincl hproj).proj
      (barGrading AA BB MM.grading).piece (barGrading AA BB GN).piece 0 := by
  rw [barContraction_proj]
  exact isHomogeneous_lTensor_rTensor hproj

/-- The bar contraction's homotopy has degree `-1` in the total suspended grading. -/
theorem isHomogeneous_barContraction_homotopy :
    LinearMap.IsHomogeneous (MM.barContraction c hh hincl hproj).homotopy
      (barGrading AA BB MM.grading).piece (barGrading AA BB MM.grading).piece (-1) := by
  rw [barContraction_homotopy]
  exact isHomogeneous_map_koszulTwist_rTensor 1 hh

/-- The source unary bar differential is square-zero. -/
theorem unaryBarDifferential_differential_comp_self :
    unaryBarDifferential AA BB MM.grading MM.differential ∘ₗ
      unaryBarDifferential AA BB MM.grading MM.differential = 0 :=
  unaryBarDifferential_comp_self AA BB MM.grading MM.isHomogeneous_differential_shift
    MM.differential_comp_self_eq_zero

/-- The higher part is a perturbation of the unary part: `(D₀ + δ)² = D₀²`. -/
theorem unaryBarDifferential_add_higherBarDifferential_comp_self :
    (unaryBarDifferential AA BB MM.grading MM.differential + MM.higherBarDifferential) ∘ₗ
        (unaryBarDifferential AA BB MM.grading MM.differential + MM.higherBarDifferential) =
      unaryBarDifferential AA BB MM.grading MM.differential ∘ₗ
        unaryBarDifferential AA BB MM.grading MM.differential := by
  rw [unaryBarDifferential_add_higherBarDifferential, barDifferential_sq,
    MM.unaryBarDifferential_differential_comp_self]

/-- The unit hypothesis of the perturbation lemma for the bar contraction. -/
theorem isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy :
    IsUnit (1 + MM.higherBarDifferential * (MM.barContraction c hh hincl hproj).homotopy) := by
  rw [barContraction_homotopy, koszulTwist_grading]
  exact MM.isUnit_one_add_higherBarDifferential_mul ((AA.grading.shift 1).koszulTwist 1)
    c.homotopy

/-- The perturbation operator `X = (1 + δ H)⁻¹ δ` commutes with the right coactions. -/
theorem coact_comp_perturbationSeries :
    Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) ∘ₗ
      (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential =
    ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential).rTensor
        (TensorWords R B) ∘ₗ
      Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) := by
  let δ : Comodule.Hom R (TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :=
    ⟨MM.higherBarDifferential, MM.coact_comp_higherBarDifferential.symm⟩
  let H := Comodule.Hom.cofreeMap (C := TensorWords R B)
    (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) c.homotopy)
  let U := Comodule.Hom.id R (TensorWords R B)
    ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) + δ.comp H
  have hX := ((Comodule.Hom.ringInverse U).comp δ).map_coact_eq
  rw [Comodule.Hom.comp_toLinearMap, Comodule.Hom.ringInverse_toLinearMap] at hX
  rw [LinearSpecialContraction.perturbationSeries_def, barContraction_homotopy]
  exact hX.symm

/-- The perturbation operator `X = (1 + δ H)⁻¹ δ` intertwines the left coactions up to the Koszul
twist `τ_A`, because `δ H` commutes strictly with the left coaction. -/
theorem leftCoact_comp_perturbationSeries :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ
      (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential =
    TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
      ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential) ∘ₗ
      Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) := by
  set δL := Comodule.leftCoactRTensor (TensorWords R B)
    (Comodule.leftCofreeCoact R (TensorWords R A) M)
  set H := (MM.barContraction c hh hincl hproj).homotopy with hH_def
  have hH : δL ∘ₗ H =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1) H ∘ₗ δL := by
    rw [hH_def, barContraction_homotopy]
    exact leftCoact_comp_map_koszulTwist_rTensor c.homotopy
  have hδH : δL ∘ₗ (MM.higherBarDifferential ∘ₗ H) =
      (MM.higherBarDifferential ∘ₗ H).lTensor (TensorWords R A) ∘ₗ δL :=
    leftCoact_comp_comp_of_koszulTwist MM.leftCoact_comp_higherBarDifferential hH
  have hU_coact : δL ∘ₗ (1 + MM.higherBarDifferential * H) =
      (1 + MM.higherBarDifferential * H).lTensor (TensorWords R A) ∘ₗ δL := by
    rw [Module.End.one_eq_id, Module.End.mul_eq_comp, LinearMap.comp_add, LinearMap.lTensor_add,
      LinearMap.add_comp, LinearMap.comp_id, LinearMap.lTensor_id, LinearMap.id_comp, hδH]
  have hU := MM.isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy c hh hincl hproj
  have hinv : δL ∘ₗ Ring.inverse (1 + MM.higherBarDifferential * H) =
      (Ring.inverse (1 + MM.higherBarDifferential * H)).lTensor (TensorWords R A) ∘ₗ δL :=
    Comodule.leftCoact_comp_of_comp_eq_id hU_coact
      (Ring.inverse_mul_cancel _ hU) (Ring.mul_inverse_cancel _ hU)
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_eq_comp,
    ← LinearMap.comp_assoc, hinv, LinearMap.comp_assoc, MM.leftCoact_comp_higherBarDifferential,
    ← LinearMap.comp_assoc, LinearMap.lTensor_comp_map]

/-- The perturbation operator has degree one. -/
theorem isHomogeneous_perturbationSeries :
    LinearMap.IsHomogeneous
      ((MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential)
      (barGrading AA BB MM.grading).piece (barGrading AA BB MM.grading).piece 1 := by
  have hH := MM.isHomogeneous_barContraction_homotopy c hh hincl hproj
  have hδH : LinearMap.IsHomogeneous
      (MM.higherBarDifferential * (MM.barContraction c hh hincl hproj).homotopy)
      (barGrading AA BB MM.grading).piece (barGrading AA BB MM.grading).piece 0 := by
    rw [Module.End.mul_eq_comp]
    simpa only [neg_add_cancel] using MM.isHomogeneous_higherBarDifferential.comp hH
  have hinv := hδH.ringInverse_one_add fun z ↦ by
    rw [Module.End.mul_eq_comp, barContraction_homotopy, koszulTwist_grading]
    exact MM.exists_pow_higherBarDifferential_comp_apply_eq_zero
      ((AA.grading.shift 1).koszulTwist 1) c.homotopy z
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_eq_comp]
  simpa only [add_zero] using hinv.comp MM.isHomogeneous_higherBarDifferential

/-- The perturbation operator vanishes on the two empty algebra words. -/
@[simp]
theorem perturbationSeries_one_tmul_tmul_one (x : M) :
    (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential
      (((1 : TensorWords R A) ⊗ₜ[R] x) ⊗ₜ[R] (1 : TensorWords R B)) = 0 := by
  rw [LinearSpecialContraction.perturbationSeries_def, mul_apply_eq_comp,
    higherBarDifferential_one_tmul_tmul_one, map_zero]

/-! ### The transferred bimodule -/

/-- The **transferred bar differential**: the perturbed differential
`D' = D₀' + ((1 ⊗ p) ⊗ 1) X ((1 ⊗ i) ⊗ 1)` of `(Tᶜ(sA) ⊗ sN) ⊗ Tᶜ(sB)`. -/
noncomputable def transferBarDifferential :
    Module.End R ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) :=
  (MM.barContraction c hh hincl hproj).perturbedDifferential MM.higherBarDifferential

/-- Defining formula for `transferBarDifferential`. -/
theorem transferBarDifferential_def :
    MM.transferBarDifferential c hh hincl hproj =
      unaryBarDifferential AA BB GN dN +
        (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) ∘ₗ
          (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
  rw [transferBarDifferential, LinearSpecialContraction.perturbedDifferential_def,
    barContraction_incl, barContraction_proj]

/-- The **perturbed bar contraction**: the basic perturbation lemma applied to `barContraction`
and `higherBarDifferential`. -/
noncomputable def transferContraction :
    LinearSpecialContraction
      (unaryBarDifferential AA BB MM.grading MM.differential + MM.higherBarDifferential)
      (MM.transferBarDifferential c hh hincl hproj) :=
  (MM.barContraction c hh hincl hproj).perturb MM.higherBarDifferential
    MM.unaryBarDifferential_add_higherBarDifferential_comp_self
    (MM.isUnit_one_add_higherBarDifferential_mul_barContraction_homotopy c hh hincl hproj)

/-- The inclusion of the perturbed bar contraction is
`i' = (1 ⊗ i) ⊗ 1 - ((τ_A ⊗ h) ⊗ 1) X ((1 ⊗ i) ⊗ 1)`. -/
theorem transferContraction_incl :
    (MM.transferContraction c hh hincl hproj).incl =
      (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) -
        (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          c.homotopy).rTensor (TensorWords R B) ∘ₗ
          (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B) := by
  rw [transferContraction, LinearSpecialContraction.perturb_incl, barContraction_incl,
    barContraction_homotopy]

/-- The projection of the perturbed bar contraction is
`p' = (1 ⊗ p) ⊗ 1 - ((1 ⊗ p) ⊗ 1) X ((τ_A ⊗ h) ⊗ 1)`. -/
theorem transferContraction_proj :
    (MM.transferContraction c hh hincl hproj).proj =
      (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) -
        (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) ∘ₗ
          (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
              c.homotopy).rTensor (TensorWords R B) := by
  rw [transferContraction, LinearSpecialContraction.perturb_proj, barContraction_proj,
    barContraction_homotopy]

/-- The homotopy of the perturbed bar contraction is
`h' = (τ_A ⊗ h) ⊗ 1 - ((τ_A ⊗ h) ⊗ 1) X ((τ_A ⊗ h) ⊗ 1)`. -/
theorem transferContraction_homotopy :
    (MM.transferContraction c hh hincl hproj).homotopy =
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
        c.homotopy).rTensor (TensorWords R B) -
        (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          c.homotopy).rTensor (TensorWords R B) ∘ₗ
          (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
            (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
              c.homotopy).rTensor (TensorWords R B) := by
  rw [transferContraction, LinearSpecialContraction.perturb_homotopy, barContraction_homotopy]

/-- The perturbed inclusion commutes with the right coactions. -/
theorem coact_comp_transferContraction_incl :
    Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) ∘ₗ
      (MM.transferContraction c hh hincl hproj).incl =
    (MM.transferContraction c hh hincl hproj).incl.rTensor (TensorWords R B) ∘ₗ
      Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) := by
  refine LinearMap.ext fun z ↦ ?_
  have hi := LinearMap.congr_fun
    (Comodule.Hom.cofreeMap (C := TensorWords R B)
      (c.incl.lTensor (TensorWords R A))).map_coact_eq.symm
  have hh' := LinearMap.congr_fun
    (Comodule.Hom.cofreeMap (C := TensorWords R B)
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
        c.homotopy)).map_coact_eq.symm
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  simp only [Comodule.Hom.cofreeMap_toLinearMap, ← LinearMap.rTensor_def,
    LinearMap.comp_apply] at hi hh' hX
  simp only [transferContraction_incl, LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
    LinearMap.rTensor_sub, hi, hh', hX, LinearMap.rTensor_comp_apply]

/-- The perturbed projection commutes with the right coactions. -/
theorem coact_comp_transferContraction_proj :
    Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) ∘ₗ
      (MM.transferContraction c hh hincl hproj).proj =
    (MM.transferContraction c hh hincl hproj).proj.rTensor (TensorWords R B) ∘ₗ
      Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) := by
  refine LinearMap.ext fun z ↦ ?_
  have hp := LinearMap.congr_fun
    (Comodule.Hom.cofreeMap (C := TensorWords R B)
      (c.proj.lTensor (TensorWords R A))).map_coact_eq.symm
  have hh' := LinearMap.congr_fun
    (Comodule.Hom.cofreeMap (C := TensorWords R B)
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
        c.homotopy)).map_coact_eq.symm
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  simp only [Comodule.Hom.cofreeMap_toLinearMap, ← LinearMap.rTensor_def,
    LinearMap.comp_apply] at hp hh' hX
  simp only [transferContraction_proj, LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
    LinearMap.rTensor_sub, hp, hh', hX, LinearMap.rTensor_comp_apply]

/-- The perturbed inclusion commutes strictly with the extended left coactions: the two Koszul
twists from `(τ_A ⊗ h) ⊗ 1` and `X` cancel. -/
theorem leftCoact_comp_transferContraction_incl :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ
      (MM.transferContraction c hh hincl hproj).incl =
    (MM.transferContraction c hh hincl hproj).incl.lTensor (TensorWords R A) ∘ₗ
      Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) := by
  let : AddCommGroup (TensorWords R A) := inferInstance
  let : AddCommGroup (TensorWords R A ⊗[R] ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)) :=
    inferInstance
  let : AddCommGroup (TensorWords R A ⊗[R] ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B)) :=
    inferInstance
  have hi := Comodule.leftCoactRTensor_comp_lTensor_rTensor
    (C := TensorWords R A) (D := TensorWords R B) c.incl
  have hHX := leftCoact_comp_comp_of_koszulTwist
    (leftCoact_comp_map_koszulTwist_rTensor (AA := AA) (B := B) c.homotopy)
    (MM.leftCoact_comp_perturbationSeries c hh hincl hproj)
  set H := (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
    c.homotopy).rTensor (TensorWords R B)
  set X := (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential
  set iBar := (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B)
  have hHXi : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ (H ∘ₗ X ∘ₗ iBar) =
      (H ∘ₗ X ∘ₗ iBar).lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) N) := by
    calc
      Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ (H ∘ₗ X ∘ₗ iBar)
        = (Comodule.leftCoactRTensor (TensorWords R B)
            (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ (H ∘ₗ X)) ∘ₗ iBar := by
          simp only [LinearMap.comp_assoc]
      _ = (H ∘ₗ X).lTensor (TensorWords R A) ∘ₗ
            (Comodule.leftCoactRTensor (TensorWords R B)
              (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ iBar) := by
          rw [hHX, LinearMap.comp_assoc]
      _ = (H ∘ₗ X ∘ₗ iBar).lTensor (TensorWords R A) ∘ₗ
            Comodule.leftCoactRTensor (TensorWords R B)
              (Comodule.leftCofreeCoact R (TensorWords R A) N) := by
          rw [hi]
          simp only [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
  rw [transferContraction_incl, LinearMap.comp_sub, LinearMap.lTensor_sub, LinearMap.sub_comp, hi,
    hHXi]

/-- The perturbed projection commutes strictly with the extended left coactions: the two Koszul
twists from `X` and `(τ_A ⊗ h) ⊗ 1` cancel. -/
theorem leftCoact_comp_transferContraction_proj :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ
      (MM.transferContraction c hh hincl hproj).proj =
    (MM.transferContraction c hh hincl hproj).proj.lTensor (TensorWords R A) ∘ₗ
      Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) := by
  let : AddCommGroup (TensorWords R A) := inferInstance
  let : AddCommGroup (TensorWords R A ⊗[R] ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)) :=
    inferInstance
  let : AddCommGroup (TensorWords R A ⊗[R] ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B)) :=
    inferInstance
  have hp := Comodule.leftCoactRTensor_comp_lTensor_rTensor
    (C := TensorWords R A) (D := TensorWords R B) c.proj
  have hXH := leftCoact_comp_comp_of_koszulTwist
    (MM.leftCoact_comp_perturbationSeries c hh hincl hproj)
    (leftCoact_comp_map_koszulTwist_rTensor (AA := AA) (B := B) c.homotopy)
  have hpXH : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ
      ((c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) ∘ₗ
        (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
          (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
            c.homotopy).rTensor (TensorWords R B)) =
    ((c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B) ∘ₗ
      (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential ∘ₗ
        (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist 1)
          c.homotopy).rTensor (TensorWords R B)).lTensor (TensorWords R A) ∘ₗ
      Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) := by
    rw [← LinearMap.comp_assoc, hp, LinearMap.comp_assoc, hXH, ← LinearMap.comp_assoc,
      ← LinearMap.lTensor_comp]
  rw [transferContraction_proj, LinearMap.comp_sub, LinearMap.lTensor_sub, LinearMap.sub_comp, hp,
    hpXH]

/-- The transferred bar differential is a left graded coderivation over the bar differential of
`AA`: it is the unary part for `d_N` plus `((1 ⊗ p) ⊗ 1) X ((1 ⊗ i) ⊗ 1)`, which twists the left
coaction by `τ_A`. -/
theorem isLeftGradedCoderivationOver_transferBarDifferential :
    Comodule.IsLeftGradedCoderivationOver
      (Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N))
      (TensorWords.grading (AA.grading.shift 1)) 1 AA.coaugmentedBarDifferential
      (MM.transferBarDifferential c hh hincl hproj) := by
  have hp := Comodule.leftCoactRTensor_comp_lTensor_rTensor
    (C := TensorWords R A) (D := TensorWords R B) c.proj
  have hi := Comodule.leftCoactRTensor_comp_lTensor_rTensor
    (C := TensorWords R A) (D := TensorWords R B) c.incl
  have hX := MM.leftCoact_comp_perturbationSeries c hh hincl hproj
  set pBar := (c.proj.lTensor (TensorWords R A)).rTensor (TensorWords R B)
  set X := (MM.barContraction c hh hincl hproj).perturbationSeries MM.higherBarDifferential
  set iBar := (c.incl.lTensor (TensorWords R A)).rTensor (TensorWords R B)
  set τ := (TensorWords.grading (AA.grading.shift 1)).koszulTwist 1
  have hpXi : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ (pBar ∘ₗ X ∘ₗ iBar) =
      TensorProduct.map τ (pBar ∘ₗ X ∘ₗ iBar) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) N) := by
    calc
      Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ (pBar ∘ₗ X ∘ₗ iBar)
        = pBar.lTensor (TensorWords R A) ∘ₗ
            (Comodule.leftCoactRTensor (TensorWords R B)
              (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ X) ∘ₗ iBar := by
          rw [← LinearMap.comp_assoc (X ∘ₗ iBar), hp]
          simp only [LinearMap.comp_assoc]
      _ = pBar.lTensor (TensorWords R A) ∘ₗ TensorProduct.map τ X ∘ₗ
            (Comodule.leftCoactRTensor (TensorWords R B)
              (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ iBar) := by
          rw [hX]
          simp only [LinearMap.comp_assoc]
      _ = TensorProduct.map τ (pBar ∘ₗ X ∘ₗ iBar) ∘ₗ
            Comodule.leftCoactRTensor (TensorWords R B)
              (Comodule.leftCofreeCoact R (TensorWords R A) N) := by
          rw [hi]
          simp only [← LinearMap.comp_assoc, LinearMap.lTensor_comp_map,
            LinearMap.map_comp_lTensor]
  rw [Comodule.isLeftGradedCoderivationOver_iff_coact_apply]
  intro z
  have hD := (isLeftGradedCoderivationOver_unaryBarDifferential AA BB GN dN).coact_apply z
  have hpXi' := LinearMap.congr_fun hpXi z
  simp only [LinearMap.comp_apply] at hpXi'
  rw [transferBarDifferential_def, LinearMap.add_apply, map_add, hD, LinearMap.comp_apply,
    LinearMap.comp_apply, hpXi', TensorProduct.map_add_right, LinearMap.add_apply, add_assoc]

/-- The transferred bar differential is a right graded coderivation over the bar differential of
`BB`. -/
theorem isGradedCoderivationOver_transferBarDifferential :
    Comodule.IsGradedCoderivationOver (barGrading AA BB GN) 1 BB.coaugmentedBarDifferential
      (MM.transferBarDifferential c hh hincl hproj) := by
  have hp := LinearMap.congr_fun
    (Comodule.Hom.cofreeMap (C := TensorWords R B)
      (c.proj.lTensor (TensorWords R A))).map_coact_eq.symm
  have hi := LinearMap.congr_fun
    (Comodule.Hom.cofreeMap (C := TensorWords R B)
      (c.incl.lTensor (TensorWords R A))).map_coact_eq.symm
  have hX := LinearMap.congr_fun (MM.coact_comp_perturbationSeries c hh hincl hproj)
  have hD := (isGradedCoderivationOver_unaryBarDifferential AA BB GN dN).coact_apply
  simp only [Comodule.Hom.cofreeMap_toLinearMap, ← LinearMap.rTensor_def,
    LinearMap.comp_apply] at hp hi hX
  rw [Comodule.isGradedCoderivationOver_iff_coact_apply]
  intro z
  simp only [transferBarDifferential_def, LinearMap.add_apply, LinearMap.comp_apply, map_add, hD,
    hp, hi, hX, LinearMap.rTensor_add, LinearMap.rTensor_comp_apply]
  abel

/-- The transferred bar differential squares to zero. -/
@[simp]
theorem transferBarDifferential_comp_self :
    MM.transferBarDifferential c hh hincl hproj ∘ₗ MM.transferBarDifferential c hh hincl hproj =
      0 :=
  LinearSpecialContraction.perturbedDifferential_comp_perturbedDifferential_eq_zero _ _
    MM.unaryBarDifferential_add_higherBarDifferential_comp_self
    MM.unaryBarDifferential_differential_comp_self

include hincl hproj in
/-- The differential of the retract has degree one for the suspended grading. -/
private theorem isHomogeneous_dN_shift :
    LinearMap.IsHomogeneous dN (GN.shift 1).piece (GN.shift 1).piece 1 :=
  LinearMap.isHomogeneous_shift_piece_iff.2 <| c.isHomogeneous_dN MM.isHomogeneous_differential
    hincl hproj

/-- The transferred bar differential has degree one. -/
theorem isHomogeneous_transferBarDifferential :
    LinearMap.IsHomogeneous (MM.transferBarDifferential c hh hincl hproj)
      (barGrading AA BB GN).piece (barGrading AA BB GN).piece 1 := by
  rw [transferBarDifferential_def]
  have hpXi := (isHomogeneous_lTensor_rTensor hproj).comp
    ((MM.isHomogeneous_perturbationSeries c hh hincl hproj).comp
      (isHomogeneous_lTensor_rTensor hincl))
  simpa only [zero_add, add_zero] using
    (isHomogeneous_unaryBarDifferential AA BB GN
      (MM.isHomogeneous_dN_shift c hincl hproj)).add hpXi

/-- The **transferred `(A, B)` `A∞` bimodule** on the retract `N` of a special contraction of
`(M, m_{0,0})`: its bar differential is the transferred bar differential. -/
noncomputable def transfer : AInfinityBimodule AA BB N :=
  ofBarDifferential GN (MM.transferBarDifferential c hh hincl hproj)
    (MM.isHomogeneous_transferBarDifferential c hh hincl hproj)
    (MM.isLeftGradedCoderivationOver_transferBarDifferential c hh hincl hproj)
    (MM.isGradedCoderivationOver_transferBarDifferential c hh hincl hproj)
    (by rw [transferBarDifferential_comp_self, LinearMap.comp_zero])

/-- The transferred bimodule carries the grading of the retract. -/
@[simp]
theorem transfer_grading : (MM.transfer c hh hincl hproj).grading = GN :=
  ofBarDifferential_grading ..

/-- The bar differential of the transferred bimodule is the transferred bar differential. -/
@[simp]
theorem barDifferential_transfer :
    (MM.transfer c hh hincl hproj).barDifferential = MM.transferBarDifferential c hh hincl hproj :=
  ofBarDifferential_barDifferential ..

/-- The unary differential of the transferred bimodule is the differential `d_N` of the retract. -/
@[simp]
theorem differential_transfer : (MM.transfer c hh hincl hproj).differential = dN := by
  ext y
  rw [differential_apply, taylor_apply, barDifferential_transfer, transferBarDifferential_def]
  simp [TensorWords.counit_eq_counit, TensorWords.counit_one]

/-! ### The extending and projecting morphisms -/

/-- The perturbed inclusion has degree zero. -/
theorem isHomogeneous_transferContraction_incl :
    LinearMap.IsHomogeneous (MM.transferContraction c hh hincl hproj).incl
      (barGrading AA BB GN).piece (barGrading AA BB MM.grading).piece 0 := by
  rw [transferContraction_incl]
  have hhXi := (isHomogeneous_map_koszulTwist_rTensor 1 hh).comp
    ((MM.isHomogeneous_perturbationSeries c hh hincl hproj).comp
      (isHomogeneous_lTensor_rTensor hincl))
  simpa only [zero_add, add_neg_cancel] using (isHomogeneous_lTensor_rTensor hincl).sub hhXi

/-- The perturbed projection has degree zero. -/
theorem isHomogeneous_transferContraction_proj :
    LinearMap.IsHomogeneous (MM.transferContraction c hh hincl hproj).proj
      (barGrading AA BB MM.grading).piece (barGrading AA BB GN).piece 0 := by
  rw [transferContraction_proj]
  have hpXh := (isHomogeneous_lTensor_rTensor hproj).comp
    ((MM.isHomogeneous_perturbationSeries c hh hincl hproj).comp
      (isHomogeneous_map_koszulTwist_rTensor 1 hh))
  simpa only [zero_add, neg_add_cancel] using (isHomogeneous_lTensor_rTensor hproj).sub hpXh

/-- The **extending morphism** of `A∞` bimodules from the transferred bimodule to `M`: its bar map
is the perturbed inclusion `i'`. -/
noncomputable def transferInclusion :
    AInfinityBimoduleHom (MM.transfer c hh hincl hproj) MM where
  barHom := ⟨(MM.transferContraction c hh hincl hproj).incl,
    (MM.coact_comp_transferContraction_incl c hh hincl hproj).symm⟩
  leftCoact_comp_barMap := MM.leftCoact_comp_transferContraction_incl c hh hincl hproj
  isHomogeneous_barMap := by
    rw [transfer_grading]
    exact MM.isHomogeneous_transferContraction_incl c hh hincl hproj
  barDifferential_comp_barMap := by
    rw [barDifferential_transfer, ← unaryBarDifferential_add_higherBarDifferential]
    exact (MM.transferContraction c hh hincl hproj).dM_comp_incl

/-- The bar map of the extending morphism is the perturbed inclusion. -/
@[simp]
theorem barMap_transferInclusion :
    (MM.transferInclusion c hh hincl hproj).barMap =
      (MM.transferContraction c hh hincl hproj).incl :=
  (rfl)

/-- The **projecting morphism** of `A∞` bimodules from `M` to the transferred bimodule: its bar map
is the perturbed projection `p'`. -/
noncomputable def transferProjection :
    AInfinityBimoduleHom MM (MM.transfer c hh hincl hproj) where
  barHom := ⟨(MM.transferContraction c hh hincl hproj).proj,
    (MM.coact_comp_transferContraction_proj c hh hincl hproj).symm⟩
  leftCoact_comp_barMap := MM.leftCoact_comp_transferContraction_proj c hh hincl hproj
  isHomogeneous_barMap := by
    rw [transfer_grading]
    exact MM.isHomogeneous_transferContraction_proj c hh hincl hproj
  barDifferential_comp_barMap := by
    rw [barDifferential_transfer, ← unaryBarDifferential_add_higherBarDifferential]
    exact (MM.transferContraction c hh hincl hproj).proj_comp_dM.symm

/-- The bar map of the projecting morphism is the perturbed projection. -/
@[simp]
theorem barMap_transferProjection :
    (MM.transferProjection c hh hincl hproj).barMap =
      (MM.transferContraction c hh hincl hproj).proj :=
  (rfl)

/-- The linear part of the extending morphism is the inclusion of the contraction. -/
@[simp]
theorem linearPart_transferInclusion :
    (MM.transferInclusion c hh hincl hproj).linearPart = c.incl := by
  ext y
  simp [AInfinityBimoduleHom.linearPart_apply, AInfinityBimoduleHom.taylor_def,
    transferContraction_incl, TensorWords.counit_eq_counit, TensorWords.counit_one]

/-- The linear part of the projecting morphism is the projection of the contraction. -/
@[simp]
theorem linearPart_transferProjection :
    (MM.transferProjection c hh hincl hproj).linearPart = c.proj := by
  ext x
  simp [AInfinityBimoduleHom.linearPart_apply, AInfinityBimoduleHom.taylor_def,
    transferContraction_proj, TensorWords.counit_eq_counit, TensorWords.counit_one,
    koszulTwist_grading]

/-- The projecting morphism is a left inverse of the extending morphism. -/
@[simp]
theorem transferProjection_comp_transferInclusion :
    (MM.transferProjection c hh hincl hproj).comp (MM.transferInclusion c hh hincl hproj) =
      AInfinityBimoduleHom.id _ :=
  AInfinityBimoduleHom.barMap_injective <| by
    rw [AInfinityBimoduleHom.barMap_comp, barMap_transferProjection, barMap_transferInclusion,
      AInfinityBimoduleHom.barMap_id]
    exact (MM.transferContraction c hh hincl hproj).proj_comp_incl

/-- The extending morphism is a quasi-isomorphism: its linear part is the inclusion of a
contraction. -/
theorem isQuasiIso_transferInclusion : (MM.transferInclusion c hh hincl hproj).IsQuasiIso := by
  rw [AInfinityBimoduleHom.isQuasiIso_iff, linearPart_transferInclusion]
  refine ⟨fun x _ hx ↦ ?_, fun y hy ↦ ⟨c.proj y, ?_, ?_⟩⟩
  · obtain ⟨y, hy⟩ := hx
    rw [differential_transfer]
    exact ⟨c.proj y, by rw [← c.proj_dM_apply, hy, c.proj_incl_apply]⟩
  · rw [LinearMap.mem_ker, differential_transfer, ← c.proj_dM_apply, LinearMap.mem_ker.1 hy,
      map_zero]
  · rw [c.incl_proj_apply, LinearMap.mem_ker.1 hy, map_zero, sub_zero, sub_sub_cancel]
    exact ⟨c.homotopy y, rfl⟩

/-- The projecting morphism is a quasi-isomorphism. -/
theorem isQuasiIso_transferProjection : (MM.transferProjection c hh hincl hproj).IsQuasiIso :=
  (MM.isQuasiIso_transferInclusion c hh hincl hproj).of_precomp <| by
    rw [transferProjection_comp_transferInclusion]
    exact AInfinityBimoduleHom.isQuasiIso_id _

end Transfer

end AInfinityBimodule

end TauCeti
