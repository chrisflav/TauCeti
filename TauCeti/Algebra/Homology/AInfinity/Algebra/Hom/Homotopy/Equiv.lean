/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Lift
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology

/-!
# Homotopy equivalences and homotopy inverses of A-infinity algebras

An `A∞` morphism `f : A ⟶ B` is a *homotopy equivalence* (`TauCeti.AInfinityHom.IsHomotopyEquiv`)
when there exists an `A∞` morphism `g : B ⟶ A` together with homotopies from `g ∘ f` to `id_A` and
from `f ∘ g` to `id_B`.  Passing to arity one shows that `f.linearPart` then has a graded
chain-homotopy inverse (`TauCeti.AInfinityHom.LinearHomotopyInverse`), and passing to cohomology
shows that `f` is a quasi-isomorphism.

Over any commutative ring `R`, the converse holds at the chain-homotopy level: every graded
chain-homotopy inverse `c` of `f.linearPart` lifts to an `A∞` morphism
`c.homotopyInverse : B ⟶ A` with arity-one component `c.inv`, together with homotopies
`c.compHomotopyInverse` from `f ∘ c.homotopyInverse` to `id_B` and `c.homotopyInverseComp` from
`c.homotopyInverse ∘ f` to `id_A`.  Starting from `g₁ = c.inv` and `h₁ = c.rightHomotopy`, at
filtration step `n + 1` the bar-differential defect `b_A ∘ G_n - G_n ∘ b_B` and the right-homotopy
defect `f.barMap ∘ G_n - id - (b_B ∘ H_n + H_n ∘ b_B)` vanish up to length `n`, land in single
letters on length `n + 1`, and satisfy coupled unary cocycle equations solved simultaneously by
`TauCeti.AInfinityHom.LinearHomotopyInverse.exists_relative_coboundary`.  Taking the filtration
limit yields `c.homotopyInverse` and `c.compHomotopyInverse`, and lifting the whiskered homotopy
`f ∘ (g ∘ f) = (f ∘ g) ∘ f ∼ id_B ∘ f = f ∘ id_A` across `f` via
`TauCeti.AInfinityHom.LinearHomotopyInverse.liftHomotopy` yields `c.homotopyInverseComp`.

Over a field `K`, the unary complex of every `A∞` algebra contracts onto its cohomology
(`TauCeti.AInfinityAlgebra.cohomologyContraction`), so the linear part of every quasi-isomorphism
admits a graded chain-homotopy inverse (`TauCeti.AInfinityHom.IsQuasiIso.linearHomotopyInverse`).
Consequently, over a field, an `A∞` morphism is a homotopy equivalence if and only if it is a
quasi-isomorphism (`TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`).

## Main definitions

* `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyInverse`,
  `TauCeti.AInfinityHom.LinearHomotopyInverse.compHomotopyInverse` and
  `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyInverseComp`: the `A∞` homotopy inverse
  extending a graded chain-homotopy inverse of `f.linearPart`, together with its right and left
  homotopies.
* `TauCeti.AInfinityHom.IsHomotopyEquiv`: an `A∞` morphism admitting a two-sided `A∞` homotopy
  inverse.
* `TauCeti.AInfinityHom.IsQuasiIso.linearHomotopyInverse`,
  `TauCeti.AInfinityHom.IsQuasiIso.homotopyInverse`,
  `TauCeti.AInfinityHom.IsQuasiIso.compHomotopyInverse` and
  `TauCeti.AInfinityHom.IsQuasiIso.homotopyInverseComp`: the homotopy inverse of a
  quasi-isomorphism over a field.

## Main results

* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_nonempty_linearHomotopyInverse` and
  `TauCeti.AInfinityHom.isHomotopyEquiv_iff_exists_linearPart`: over any commutative ring, `f` is
  an `A∞` homotopy equivalence if and only if `f.linearPart` admits a graded chain-homotopy
  inverse.
* `TauCeti.AInfinityHom.IsHomotopyEquiv.isQuasiIso`: every `A∞` homotopy equivalence is a
  quasi-isomorphism.
* `TauCeti.AInfinityHom.IsHomotopyEquiv.comp`: `A∞` homotopy equivalences are closed under
  composition.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: over a field, an `A∞` morphism is a
  homotopy equivalence if and only if it is a quasi-isomorphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1, Section 1.3.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), Sections 1--2.
-/

public section

namespace TauCeti

universe uR uA uB uC

namespace AInfinityHom

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

namespace LinearHomotopyInverse

/-! ### Obstruction construction of the A-infinity homotopy inverse -/

section HomotopyInverse

variable {f : AInfinityHom AA BB}

private structure ObstructionStage (f : AInfinityHom AA BB) (n : ℕ) where
  g : ReducedTensorWords R B →ₗ[R] A
  h : ReducedTensorWords R B →ₗ[R] B
  isHomogeneous_g :
    LinearMap.IsHomogeneous g
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0
  isHomogeneous_h :
    LinearMap.IsHomogeneous h
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1)
  barDifferential_eq : ∀ z ∈ ReducedTensorWords.filtration R B n,
    AA.taylor (ReducedTensorWords.coalgHom R g z) = g (BB.barDifferential z)
  homotopy_eq : ∀ z ∈ ReducedTensorWords.filtration R B n,
    f.taylor (ReducedTensorWords.coalgHom R g z) - ReducedTensorWords.letter R B z =
      BB.taylor (ReducedTensorWords.gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ ReducedTensorWords.coalgHom R g) LinearMap.id h z) +
        h (BB.barDifferential z)

private noncomputable def obstructionStageOne (c : f.LinearHomotopyInverse) :
    ObstructionStage f 1 where
  g := c.inv ∘ₗ ReducedTensorWords.letter R B
  h := c.rightHomotopy ∘ₗ ReducedTensorWords.letter R B
  isHomogeneous_g := by
    simpa only [zero_add] using
      ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 c.isHomogeneous_inv).comp
        (ReducedTensorWords.isHomogeneous_letter (BB.grading.shift 1))
  isHomogeneous_h := by
    simpa only [zero_add] using
      ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 c.isHomogeneous_rightHomotopy).comp
        (ReducedTensorWords.isHomogeneous_letter (BB.grading.shift 1))
  barDifferential_eq z hz := by
    rw [← sub_eq_zero]
    change ((AA.taylor ∘ₗ ReducedTensorWords.coalgHom R (c.inv ∘ₗ ReducedTensorWords.letter R B)) -
      (c.inv ∘ₗ ReducedTensorWords.letter R B) ∘ₗ BB.barDifferential) z = 0
    refine ReducedTensorWords.apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_) z
      hz
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      ReducedTensorWords.coalgHom_ofLetter, ReducedTensorWords.letter_ofLetter,
      AA.taylor_ofLetter, BB.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply]
    rw [← LinearMap.comp_apply AA.differential c.inv b, c.differential_comp_inv,
      LinearMap.comp_apply, sub_self]
  homotopy_eq z hz := by
    rw [← sub_eq_zero]
    change ((f.taylor ∘ₗ ReducedTensorWords.coalgHom R (c.inv ∘ₗ ReducedTensorWords.letter R B) -
        ReducedTensorWords.letter R B) -
      (BB.taylor ∘ₗ ReducedTensorWords.gradedCoderivAlong (BB.grading.shift 1) 1 _ LinearMap.id
          (c.rightHomotopy ∘ₗ ReducedTensorWords.letter R B) +
        (c.rightHomotopy ∘ₗ ReducedTensorWords.letter R B) ∘ₗ BB.barDifferential)) z = 0
    refine ReducedTensorWords.apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_) z
      hz
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.zero_apply, ReducedTensorWords.coalgHom_ofLetter,
      ReducedTensorWords.gradedCoderivAlong_ofLetter, ReducedTensorWords.letter_ofLetter,
      ← linearPart_apply, BB.taylor_ofLetter, BB.barDifferential_ofLetter,
      ← AInfinityAlgebra.differential_apply]
    have hb : f.linearPart (c.inv b) - b =
        BB.differential (c.rightHomotopy b) + c.rightHomotopy (BB.differential b) := by
      simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.id_apply] using LinearMap.congr_fun c.linearPart_comp_inv_sub_id b
    rw [hb, sub_self]

private noncomputable def obstructionStageZero (c : f.LinearHomotopyInverse) :
    ObstructionStage f 0 :=
  { c.obstructionStageOne with
    barDifferential_eq := fun z hz ↦ c.obstructionStageOne.barDifferential_eq z
      (ReducedTensorWords.filtration_monotone R B (Nat.zero_le 1) hz)
    homotopy_eq := fun z hz ↦ c.obstructionStageOne.homotopy_eq z
      (ReducedTensorWords.filtration_monotone R B (Nat.zero_le 1) hz) }

private noncomputable abbrev stageBarMap {n : ℕ} (s : ObstructionStage f n) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  ReducedTensorWords.coalgHom R s.g

private noncomputable abbrev stageHomotopy {n : ℕ} (s : ObstructionStage f n) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  ReducedTensorWords.gradedCoderivAlong (BB.grading.shift 1) 1
    (f.barMap ∘ₗ stageBarMap s) LinearMap.id s.h

private noncomputable def stageE {n : ℕ} (s : ObstructionStage f n) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  AA.barDifferential ∘ₗ stageBarMap s - stageBarMap s ∘ₗ BB.barDifferential

private noncomputable def stageK {n : ℕ} (s : ObstructionStage f n) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  f.barMap ∘ₗ stageBarMap s - LinearMap.id -
    (BB.barDifferential ∘ₗ stageHomotopy s + stageHomotopy s ∘ₗ BB.barDifferential)

private theorem isGradedCoderivationAlong_stageE {n : ℕ} (s : ObstructionStage f n) :
    ReducedTensorWords.IsGradedCoderivationAlong (BB.grading.shift 1) 1
      (stageBarMap s) (stageBarMap s) (stageE s) :=
  (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom
    (ReducedTensorWords.isCoalgHom_coalgHom s.g)
    (ReducedTensorWords.isHomogeneous_coalgHom s.isHomogeneous_g)).sub
    ((ReducedTensorWords.isCoalgHom_coalgHom s.g).comp_isGradedCoderivation
      BB.isGradedCoderivation_barDifferential)

private theorem letter_stageE_apply {n : ℕ} (s : ObstructionStage f n)
    (z : ReducedTensorWords R B) :
    ReducedTensorWords.letter R A (stageE s z) =
      AA.taylor (stageBarMap s z) - s.g (BB.barDifferential z) := by
  rw [stageE, stageBarMap, LinearMap.sub_apply, map_sub, LinearMap.comp_apply,
    LinearMap.comp_apply, ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    AA.letter_comp_barDifferential, ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    ReducedTensorWords.letter_comp_coalgHom]

private theorem letter_stageE_eq_zero {n : ℕ} (s : ObstructionStage f n)
    {z : ReducedTensorWords R B} (hz : z ∈ ReducedTensorWords.filtration R B n) :
    ReducedTensorWords.letter R A (stageE s z) = 0 := by
  rw [letter_stageE_apply, s.barDifferential_eq z hz, sub_self]

private theorem stageE_eq_zero {n : ℕ} (s : ObstructionStage f n)
    {z : ReducedTensorWords R B} (hz : z ∈ ReducedTensorWords.filtration R B n) :
    stageE s z = 0 :=
  (isGradedCoderivationAlong_stageE s).apply_eq_zero_of_mem_filtration
    (fun _ hw ↦ letter_stageE_eq_zero s hw) hz

private theorem stageE_eq_ofLetter {n : ℕ} (s : ObstructionStage f n)
    {z : ReducedTensorWords R B} (hz : z ∈ ReducedTensorWords.filtration R B (n + 1)) :
    stageE s z =
      ReducedTensorWords.ofLetter R A (ReducedTensorWords.letter R A (stageE s z)) :=
  (isGradedCoderivationAlong_stageE s).apply_eq_ofLetter_of_mem_filtration_succ
    (fun _ hw ↦ letter_stageE_eq_zero s hw) hz

private theorem letter_stageK_apply {n : ℕ} (s : ObstructionStage f n)
    (z : ReducedTensorWords R B) :
    ReducedTensorWords.letter R B (stageK s z) =
      f.taylor (stageBarMap s z) - ReducedTensorWords.letter R B z -
        (BB.taylor (stageHomotopy s z) + s.h (BB.barDifferential z)) := by
  rw [stageK, stageHomotopy, stageBarMap, LinearMap.sub_apply, LinearMap.sub_apply,
    LinearMap.add_apply, map_sub, map_sub, map_add, LinearMap.comp_apply, LinearMap.id_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R B) f.barMap, ← f.taylor_def,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R B) BB.barDifferential,
    BB.letter_comp_barDifferential,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R B)
      (ReducedTensorWords.gradedCoderivAlong _ _ _ _ _),
    ReducedTensorWords.letter_comp_gradedCoderivAlong]

private theorem letter_stageK_eq_zero {n : ℕ} (s : ObstructionStage f n)
    {z : ReducedTensorWords R B} (hz : z ∈ ReducedTensorWords.filtration R B n) :
    ReducedTensorWords.letter R B (stageK s z) = 0 := by
  rw [letter_stageK_apply, s.homotopy_eq z hz, sub_self]

private theorem stageK_eq_ofLetter {n : ℕ} (s : ObstructionStage f n)
    {z : ReducedTensorWords R B} (hz : z ∈ ReducedTensorWords.filtration R B (n + 1)) :
    stageK s z =
      ReducedTensorWords.ofLetter R B (ReducedTensorWords.letter R B (stageK s z)) := by
  have hFG_coalg := f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom s.g)
  have hFG_hom : LinearMap.IsHomogeneous (f.barMap ∘ₗ stageBarMap s)
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using
      f.isHomogeneous_barMap.comp (ReducedTensorWords.isHomogeneous_coalgHom s.isHomogeneous_g)
  have hH_cod := ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong
    (BB.grading.shift 1) 1 hFG_coalg (ReducedTensorWords.isCoalgHom_id B) s.h
  have hH_hom := ReducedTensorWords.isHomogeneous_gradedCoderivAlong (q := 1) hFG_hom
    (LinearMap.isHomogeneous_id _) s.isHomogeneous_h
  have hFG_int : ∀ w ∈ ReducedTensorWords.filtration R B n,
      BB.barDifferential ((f.barMap ∘ₗ stageBarMap s) w) =
        (f.barMap ∘ₗ stageBarMap s) (BB.barDifferential w) := fun w hw ↦ by
    have he := stageE_eq_zero s hw
    simp only [stageE, LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero] at he
    rw [LinearMap.comp_apply, LinearMap.comp_apply, f.barDifferential_barMap, he]
  have hK_van : ∀ m ≤ n, ∀ w ∈ ReducedTensorWords.filtration R B m, stageK s w = 0 := by
    intro m hm
    induction m with
    | zero =>
        intro w hw
        rw [ReducedTensorWords.filtration_zero, Submodule.mem_bot] at hw
        rw [hw, map_zero]
    | succ m ih =>
        intro w hw
        have hm' : m ≤ n := Nat.le_of_succ_le hm
        have hstep := hH_cod.sub_comp_add_comp_eq_ofLetter hH_hom (by decide)
          BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential (by decide)
          BB.isGradedCoderivation_barDifferential hFG_coalg (ReducedTensorWords.isCoalgHom_id B)
          hFG_hom
          (fun u hu ↦ hFG_int u (ReducedTensorWords.filtration_monotone R B hm' hu))
          (fun _ _ ↦ rfl) (ih hm') hw
        change stageK s w =
          ReducedTensorWords.ofLetter R B (ReducedTensorWords.letter R B (stageK s w)) at hstep
        rw [hstep, letter_stageK_eq_zero s (ReducedTensorWords.filtration_monotone R B hm hw),
          map_zero]
  exact hH_cod.sub_comp_add_comp_eq_ofLetter hH_hom (by decide)
    BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential (by decide)
    BB.isGradedCoderivation_barDifferential hFG_coalg (ReducedTensorWords.isCoalgHom_id B)
    hFG_hom hFG_int (fun _ _ ↦ rfl) (hK_van n le_rfl) hz

private theorem isHomogeneous_stageE_and_stageK {n : ℕ} (s : ObstructionStage f n) :
    LinearMap.IsHomogeneous (stageE s)
        (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
        (ReducedTensorWords.gradedPiece (AA.grading.shift 1)) 1 ∧
      LinearMap.IsHomogeneous (stageK s)
        (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
        (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 := by
  have hG_hom := ReducedTensorWords.isHomogeneous_coalgHom s.isHomogeneous_g
  have hE₁ : LinearMap.IsHomogeneous (AA.barDifferential ∘ₗ stageBarMap s)
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1)) 1 := by
    simpa only [zero_add] using AA.isHomogeneous_barDifferential.comp hG_hom
  have hE₂ : LinearMap.IsHomogeneous (stageBarMap s ∘ₗ BB.barDifferential)
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1)) 1 := by
    simpa only [add_zero] using hG_hom.comp BB.isHomogeneous_barDifferential
  have hFG_hom : LinearMap.IsHomogeneous (f.barMap ∘ₗ stageBarMap s)
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp hG_hom
  have hH_hom := ReducedTensorWords.isHomogeneous_gradedCoderivAlong (q := 1) hFG_hom
    (LinearMap.isHomogeneous_id _) s.isHomogeneous_h
  have hbH : LinearMap.IsHomogeneous (BB.barDifferential ∘ₗ stageHomotopy s)
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [neg_add_cancel] using BB.isHomogeneous_barDifferential.comp hH_hom
  have hHb : LinearMap.IsHomogeneous (stageHomotopy s ∘ₗ BB.barDifferential)
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_neg_cancel] using hH_hom.comp BB.isHomogeneous_barDifferential
  exact ⟨hE₁.sub hE₂, (hFG_hom.sub (LinearMap.isHomogeneous_id _)).sub (hbH.add hHb)⟩

private theorem stageTop_closed {n : ℕ} (s : ObstructionStage f n) :
    AA.differential ∘ₗ
        (-((ReducedTensorWords.letter R A ∘ₗ stageE s) ∘ₗ
          ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩)) +
      (1 : ℤˣ) •
        ((-((ReducedTensorWords.letter R A ∘ₗ stageE s) ∘ₗ
            ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩)) ∘ₗ
          BB.unaryBarDifferential) = 0 := by
  have hsq : AA.barDifferential ∘ₗ stageE s + stageE s ∘ₗ BB.barDifferential = 0 :=
    LinearMap.ext fun w ↦ by
      have hA : AA.barDifferential (AA.barDifferential (stageBarMap s w)) = 0 :=
        LinearMap.congr_fun AA.barDifferential_sq (stageBarMap s w)
      have hB : BB.barDifferential (BB.barDifferential w) = 0 :=
        LinearMap.congr_fun BB.barDifferential_sq w
      simp only [stageE, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.zero_apply, map_sub]
      rw [hA, hB, map_zero, zero_sub, sub_zero, neg_add_cancel]
  refine LinearMap.ext fun z ↦ ?_
  have hz := ReducedTensorWords.lengthProj_mem_filtration R B ⟨n + 1, n.succ_pos⟩ z
  have hPz := congrArg (ReducedTensorWords.letter R A)
    (LinearMap.congr_fun hsq (ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩ z))
  have hwE : ∀ w ∈ ReducedTensorWords.filtration R B n,
      (ReducedTensorWords.letter R A ∘ₗ stageE s) w = 0 :=
    fun _ hw ↦ letter_stageE_eq_zero s hw
  rw [LinearMap.zero_apply, map_zero, LinearMap.add_apply, map_add, LinearMap.comp_apply,
    LinearMap.comp_apply, ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    AA.letter_comp_barDifferential, stageE_eq_ofLetter s hz, AA.taylor_ofLetter,
    ← AA.differential_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R A) (stageE s) (BB.barDifferential _),
    BB.apply_barDifferential_lengthProj hwE z] at hPz
  simp only [one_smul, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, map_neg,
    LinearMap.zero_apply] at hPz ⊢
  rw [← neg_add, hPz, neg_zero]

private theorem stageTop_rel {n : ℕ} (s : ObstructionStage f n) :
    BB.differential ∘ₗ
        (-((ReducedTensorWords.letter R B ∘ₗ stageK s) ∘ₗ
          ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩)) -
      (1 : ℤˣ) •
        ((-((ReducedTensorWords.letter R B ∘ₗ stageK s) ∘ₗ
            ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩)) ∘ₗ
          BB.unaryBarDifferential) =
      f.linearPart ∘ₗ
        (-((ReducedTensorWords.letter R A ∘ₗ stageE s) ∘ₗ
          ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩)) := by
  have hrel : BB.barDifferential ∘ₗ stageK s - stageK s ∘ₗ BB.barDifferential =
      f.barMap ∘ₗ stageE s :=
    LinearMap.ext fun w ↦ by
      have hB₁ : BB.barDifferential (BB.barDifferential (stageHomotopy s w)) = 0 :=
        LinearMap.congr_fun BB.barDifferential_sq (stageHomotopy s w)
      have hB₂ : BB.barDifferential (BB.barDifferential w) = 0 :=
        LinearMap.congr_fun BB.barDifferential_sq w
      simp only [stageK, stageE, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.id_apply, map_sub, map_add, f.barDifferential_barMap]
      rw [hB₁, hB₂, map_zero]
      abel
  refine LinearMap.ext fun z ↦ ?_
  have hz := ReducedTensorWords.lengthProj_mem_filtration R B ⟨n + 1, n.succ_pos⟩ z
  have hPz := congrArg (ReducedTensorWords.letter R B)
    (LinearMap.congr_fun hrel (ReducedTensorWords.lengthProj R B ⟨n + 1, n.succ_pos⟩ z))
  have hwK : ∀ w ∈ ReducedTensorWords.filtration R B n,
      (ReducedTensorWords.letter R B ∘ₗ stageK s) w = 0 :=
    fun _ hw ↦ letter_stageK_eq_zero s hw
  rw [LinearMap.sub_apply, map_sub, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R B) BB.barDifferential,
    BB.letter_comp_barDifferential,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R B) f.barMap, ← f.taylor_def,
    stageK_eq_ofLetter s hz, stageE_eq_ofLetter s hz, BB.taylor_ofLetter,
    ← BB.differential_apply, ← linearPart_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R B) (stageK s) (BB.barDifferential _),
    BB.apply_barDifferential_lengthProj hwK z] at hPz
  simp only [one_smul, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
    map_neg] at hPz ⊢
  rw [← hPz]
  abel

private theorem exists_stageDelta (c : f.LinearHomotopyInverse) {n : ℕ}
    (s : ObstructionStage f n) :
    ∃ (Δg : ReducedTensorWords R B →ₗ[R] A) (Δh : ReducedTensorWords R B →ₗ[R] B),
      LinearMap.IsHomogeneous Δg
        (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 ∧
      LinearMap.IsHomogeneous Δh
        (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) ∧
      (∀ w ∈ ReducedTensorWords.filtration R B n, Δg w = 0 ∧ Δh w = 0) ∧
      (∀ z ∈ ReducedTensorWords.filtration R B (n + 1),
        AA.differential (Δg z) - Δg (BB.unaryBarDifferential z) =
          -ReducedTensorWords.letter R A (stageE s z)) ∧
      (∀ z ∈ ReducedTensorWords.filtration R B (n + 1),
        f.linearPart (Δg z) - (BB.differential (Δh z) + Δh (BB.unaryBarDifferential z)) =
          -ReducedTensorWords.letter R B (stageK s z)) := by
  have hP := ReducedTensorWords.isHomogeneous_lengthProj (BB.grading.shift 1) ⟨n + 1, n.succ_pos⟩
  have hEK := isHomogeneous_stageE_and_stageK s
  have hΦ₀ := ((ReducedTensorWords.isHomogeneous_letter (AA.grading.shift 1)).comp hEK.1).comp hP
  rw [add_zero, zero_add, show (1 : ℤ) = (-1 + 1) + 1 by decide] at hΦ₀
  have hΨ₀ := ((ReducedTensorWords.isHomogeneous_letter (BB.grading.shift 1)).comp hEK.2).comp hP
  rw [add_zero, zero_add, show (0 : ℤ) = -1 + 1 by decide] at hΨ₀
  obtain ⟨ξ, η, hξ_hom, hη_hom, hvan, hξ_eq, hη_eq⟩ :=
    c.exists_relative_coboundary BB.unaryBarDifferential 1 hΦ₀.neg hΨ₀.neg
      (stageTop_closed s) (stageTop_rel s)
  rw [neg_add_cancel] at hξ_hom
  refine ⟨ξ, -η, hξ_hom, hη_hom.neg, fun w hw ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have hPw := ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R B
      (n := ⟨n + 1, n.succ_pos⟩) n.lt_succ_self hw
    have hv := hvan w (by simp only [LinearMap.neg_apply, LinearMap.comp_apply, hPw, map_zero,
        neg_zero])
      (by simp only [LinearMap.neg_apply, LinearMap.comp_apply, hPw, map_zero, neg_zero])
    exact ⟨hv.1, by rw [LinearMap.neg_apply, hv.2, neg_zero]⟩
  · have hz' := LinearMap.congr_fun hξ_eq z
    have hwE : ∀ w ∈ ReducedTensorWords.filtration R B n,
        (ReducedTensorWords.letter R A ∘ₗ stageE s) w = 0 :=
      fun _ hw ↦ letter_stageE_eq_zero s hw
    simpa only [one_smul, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      ReducedTensorWords.apply_lengthProj_of_mem_filtration R B hwE hz] using hz'
  · have hz' := LinearMap.congr_fun hη_eq z
    have hwK : ∀ w ∈ ReducedTensorWords.filtration R B n,
        (ReducedTensorWords.letter R B ∘ₗ stageK s) w = 0 :=
      fun _ hw ↦ letter_stageK_eq_zero s hw
    simp only [one_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      ReducedTensorWords.apply_lengthProj_of_mem_filtration R B hwK hz] at hz'
    simp only [LinearMap.neg_apply, map_neg]
    rw [← hz']
    abel

private theorem stageDelta_barMap_succ {n : ℕ} (s : ObstructionStage f n)
    {Δg : ReducedTensorWords R B →ₗ[R] A}
    (hΔg_van : ∀ w ∈ ReducedTensorWords.filtration R B n, Δg w = 0)
    {z : ReducedTensorWords R B} (hz : z ∈ ReducedTensorWords.filtration R B (n + 1)) :
    ReducedTensorWords.coalgHom R (s.g + Δg) z =
      stageBarMap s z + ReducedTensorWords.ofLetter R A (Δg z) := by
  have hcod := (ReducedTensorWords.isCoalgHom_coalgHom (s.g + Δg)).isGradedCoderivationAlong_sub
    (G := BB.grading.shift 1) (ReducedTensorWords.isCoalgHom_coalgHom s.g)
  have hsub := hcod.apply_eq_ofLetter_of_mem_filtration_succ (n := n)
    (fun w hw ↦ by
      rw [LinearMap.sub_apply, map_sub,
        ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
        ReducedTensorWords.letter_comp_coalgHom,
        ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
        ReducedTensorWords.letter_comp_coalgHom, LinearMap.add_apply,
        hΔg_van w hw, add_zero, sub_self]) hz
  rw [LinearMap.sub_apply, map_sub,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    ReducedTensorWords.letter_comp_coalgHom,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    ReducedTensorWords.letter_comp_coalgHom, LinearMap.add_apply, add_sub_cancel_left] at hsub
  exact eq_add_of_sub_eq' hsub

private theorem stageDelta_homotopy_succ {n : ℕ} (s : ObstructionStage f n)
    {Δg : ReducedTensorWords R B →ₗ[R] A} {Δh : ReducedTensorWords R B →ₗ[R] B}
    (hΔg_van : ∀ w ∈ ReducedTensorWords.filtration R B n, Δg w = 0)
    (hΔh_van : ∀ w ∈ ReducedTensorWords.filtration R B n, Δh w = 0)
    {z : ReducedTensorWords R B} (hz : z ∈ ReducedTensorWords.filtration R B (n + 1)) :
    ReducedTensorWords.gradedCoderivAlong (BB.grading.shift 1) 1
        (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (s.g + Δg)) LinearMap.id (s.h + Δh) z =
      stageHomotopy s z + ReducedTensorWords.ofLetter R B (Δh z) := by
  have hG_eq : ∀ w ∈ ReducedTensorWords.filtration R B n,
      ReducedTensorWords.coalgHom R (s.g + Δg) w = stageBarMap s w := fun w hw ↦
    (ReducedTensorWords.isCoalgHom_coalgHom _).apply_eq_of_mem_filtration
      (ReducedTensorWords.isCoalgHom_coalgHom s.g)
      (fun u hu ↦ by
        rw [← LinearMap.comp_apply (ReducedTensorWords.letter R A),
          ReducedTensorWords.letter_comp_coalgHom,
          ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
          ReducedTensorWords.letter_comp_coalgHom, LinearMap.add_apply, hΔg_van u hu, add_zero]) hw
  have h₁ := ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom (s.g + Δg)))
    (ReducedTensorWords.isCoalgHom_id B) (s.h + Δh)
  have h₂ := ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
    (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom s.g))
    (ReducedTensorWords.isCoalgHom_id B) s.h
  have hsub := h₁.sub_apply_eq_ofLetter_of_mem_filtration_succ h₂
    (fun w hw ↦ by rw [LinearMap.comp_apply, LinearMap.comp_apply, hG_eq w hw])
    (fun _ _ ↦ rfl)
    (fun w hw ↦ by
      rw [← LinearMap.comp_apply (ReducedTensorWords.letter R B),
        ReducedTensorWords.letter_comp_gradedCoderivAlong,
        ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
        ReducedTensorWords.letter_comp_gradedCoderivAlong, LinearMap.add_apply,
        hΔh_van w hw, add_zero]) hz
  rw [map_sub,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
    ReducedTensorWords.letter_comp_gradedCoderivAlong,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
    ReducedTensorWords.letter_comp_gradedCoderivAlong, LinearMap.add_apply,
    add_sub_cancel_left] at hsub
  exact eq_add_of_sub_eq' hsub

private noncomputable def obstructionStageSucc (c : f.LinearHomotopyInverse) {n : ℕ}
    (s : ObstructionStage f n) :
    { s' : ObstructionStage f (n + 1) //
      ∀ w ∈ ReducedTensorWords.filtration R B n, s'.g w = s.g w ∧ s'.h w = s.h w } := by
  let hex := c.exists_stageDelta s
  let Δg := hex.choose
  let Δh := hex.choose_spec.choose
  have hΔ := hex.choose_spec.choose_spec
  refine ⟨⟨s.g + Δg, s.h + Δh, s.isHomogeneous_g.add hΔ.1, s.isHomogeneous_h.add hΔ.2.1,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩, fun w hw ↦ ?_⟩
  · rw [stageDelta_barMap_succ s (fun w hw ↦ (hΔ.2.2.1 w hw).1) hz, map_add, AA.taylor_ofLetter,
      ← AA.differential_apply, LinearMap.add_apply,
      BB.apply_barDifferential_of_mem_filtration_succ (fun w hw ↦ (hΔ.2.2.1 w hw).1) hz]
    exact sub_eq_zero.1 <| by
      calc AA.taylor (stageBarMap s z) + AA.differential (Δg z) -
            (s.g (BB.barDifferential z) + Δg (BB.unaryBarDifferential z))
          = (AA.taylor (stageBarMap s z) - s.g (BB.barDifferential z)) +
              (AA.differential (Δg z) - Δg (BB.unaryBarDifferential z)) := by abel
        _ = 0 := by rw [← letter_stageE_apply, hΔ.2.2.2.1 z hz, add_neg_cancel]
  · rw [stageDelta_barMap_succ s (fun w hw ↦ (hΔ.2.2.1 w hw).1) hz,
      stageDelta_homotopy_succ s (fun w hw ↦ (hΔ.2.2.1 w hw).1) (fun w hw ↦ (hΔ.2.2.1 w hw).2) hz,
      map_add, map_add, ← linearPart_apply, BB.taylor_ofLetter, ← BB.differential_apply,
      LinearMap.add_apply,
      BB.apply_barDifferential_of_mem_filtration_succ (fun w hw ↦ (hΔ.2.2.1 w hw).2) hz]
    exact sub_eq_zero.1 <| by
      calc f.taylor (stageBarMap s z) + f.linearPart (Δg z) - ReducedTensorWords.letter R B z -
            (BB.taylor (stageHomotopy s z) + BB.differential (Δh z) +
              (s.h (BB.barDifferential z) + Δh (BB.unaryBarDifferential z)))
          = (f.taylor (stageBarMap s z) - ReducedTensorWords.letter R B z -
              (BB.taylor (stageHomotopy s z) + s.h (BB.barDifferential z))) +
            (f.linearPart (Δg z) - (BB.differential (Δh z) + Δh (BB.unaryBarDifferential z))) := by
              abel
        _ = 0 := by rw [← letter_stageK_apply, hΔ.2.2.2.2 z hz, add_neg_cancel]
  · exact ⟨by rw [LinearMap.add_apply, (hΔ.2.2.1 w hw).1, add_zero],
      by rw [LinearMap.add_apply, (hΔ.2.2.1 w hw).2, add_zero]⟩

private noncomputable def obstructionStageSeq (c : f.LinearHomotopyInverse) :
    ∀ n : ℕ, ObstructionStage f n
  | 0 => c.obstructionStageZero
  | 1 => c.obstructionStageOne
  | n + 2 => (c.obstructionStageSucc (c.obstructionStageSeq (n + 1))).1

private theorem obstructionStageSeq_g_stabilises (c : f.LinearHomotopyInverse) (n : ℕ) :
    ∀ z ∈ ReducedTensorWords.filtration R B n,
      (c.obstructionStageSeq (n + 1)).g z = (c.obstructionStageSeq n).g z := by
  cases n with
  | zero => intro _ _; rfl
  | succ n =>
      intro z hz
      exact ((c.obstructionStageSucc (c.obstructionStageSeq (n + 1))).2 z hz).1

private theorem obstructionStageSeq_h_stabilises (c : f.LinearHomotopyInverse) (n : ℕ) :
    ∀ z ∈ ReducedTensorWords.filtration R B n,
      (c.obstructionStageSeq (n + 1)).h z = (c.obstructionStageSeq n).h z := by
  cases n with
  | zero => intro _ _; rfl
  | succ n =>
      intro z hz
      exact ((c.obstructionStageSucc (c.obstructionStageSeq (n + 1))).2 z hz).2

private noncomputable abbrev obstructionLimitG (c : f.LinearHomotopyInverse) :
    ReducedTensorWords R B →ₗ[R] A :=
  ReducedTensorWords.filtrationLimit R fun n ↦ (c.obstructionStageSeq n).g

private noncomputable abbrev obstructionLimitH (c : f.LinearHomotopyInverse) :
    ReducedTensorWords R B →ₗ[R] B :=
  ReducedTensorWords.filtrationLimit R fun n ↦ (c.obstructionStageSeq n).h

private theorem homotopyInverse_barDifferential_eq (c : f.LinearHomotopyInverse) :
    AA.taylor ∘ₗ ReducedTensorWords.coalgHom R c.obstructionLimitG =
      c.obstructionLimitG ∘ₗ BB.barDifferential :=
  LinearMap.ext fun z ↦ by
    obtain ⟨k, hz⟩ := ReducedTensorWords.exists_mem_filtration R B z
    have hG : ReducedTensorWords.coalgHom R c.obstructionLimitG z =
        ReducedTensorWords.coalgHom R (c.obstructionStageSeq k).g z :=
      (ReducedTensorWords.isCoalgHom_coalgHom _).apply_eq_of_mem_filtration
        (ReducedTensorWords.isCoalgHom_coalgHom _)
        (fun _ hw ↦ by
          rw [← LinearMap.comp_apply (ReducedTensorWords.letter R A),
            ReducedTensorWords.letter_comp_coalgHom,
            ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
            ReducedTensorWords.letter_comp_coalgHom]
          exact ReducedTensorWords.filtrationLimit_apply_of_mem_filtration
            c.obstructionStageSeq_g_stabilises hw) hz
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hG,
      ReducedTensorWords.filtrationLimit_apply_of_mem_filtration
        c.obstructionStageSeq_g_stabilises (BB.barDifferential_mem_filtration hz)]
    exact (c.obstructionStageSeq k).barDifferential_eq _ hz

/-- **The `A∞` homotopy inverse** extending a graded chain-homotopy inverse `c` of `f.linearPart`.
Its suspended Taylor components are the filtration limit of the obstruction stages built from
`c`. -/
noncomputable def homotopyInverse (c : f.LinearHomotopyInverse) : AInfinityHom BB AA :=
  ofTaylor c.obstructionLimitG
    (ReducedTensorWords.isHomogeneous_filtrationLimit c.obstructionStageSeq_g_stabilises
      fun n ↦ (c.obstructionStageSeq n).isHomogeneous_g)
    c.homotopyInverse_barDifferential_eq

/-- The linear part of `c.homotopyInverse` is `c.inv`. -/
@[simp]
theorem linearPart_homotopyInverse (c : f.LinearHomotopyInverse) :
    c.homotopyInverse.linearPart = c.inv :=
  LinearMap.ext fun b ↦ by
    rw [linearPart_apply, homotopyInverse, taylor_ofTaylor,
      ReducedTensorWords.filtrationLimit_apply_of_mem_filtration
        c.obstructionStageSeq_g_stabilises (ReducedTensorWords.ofLetter_mem_filtration R B b)]
    change (c.inv ∘ₗ ReducedTensorWords.letter R B) (ReducedTensorWords.ofLetter R B b) = c.inv b
    rw [LinearMap.comp_apply, ReducedTensorWords.letter_ofLetter]

private noncomputable abbrev rightHomotopyCoderiv (c : f.LinearHomotopyInverse) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  ReducedTensorWords.gradedCoderivAlong (BB.grading.shift 1) 1
    (f.comp c.homotopyInverse).barMap (AInfinityHom.id BB).barMap c.obstructionLimitH

private theorem comp_homotopyInverse_eq (c : f.LinearHomotopyInverse) :
    (f.comp c.homotopyInverse).taylor - (AInfinityHom.id BB).taylor =
      BB.taylor ∘ₗ c.rightHomotopyCoderiv +
        (ReducedTensorWords.letter R B ∘ₗ c.rightHomotopyCoderiv) ∘ₗ BB.barDifferential :=
  LinearMap.ext fun z ↦ by
    obtain ⟨k, hz⟩ := ReducedTensorWords.exists_mem_filtration R B z
    have hG : ∀ w ∈ ReducedTensorWords.filtration R B k,
        c.homotopyInverse.barMap w =
          ReducedTensorWords.coalgHom R (c.obstructionStageSeq k).g w := fun w hw ↦ by
      rw [homotopyInverse, barMap_ofTaylor]
      exact (ReducedTensorWords.isCoalgHom_coalgHom _).apply_eq_of_mem_filtration
        (ReducedTensorWords.isCoalgHom_coalgHom _)
        (fun _ hu ↦ by
          rw [← LinearMap.comp_apply (ReducedTensorWords.letter R A),
            ReducedTensorWords.letter_comp_coalgHom,
            ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
            ReducedTensorWords.letter_comp_coalgHom]
          exact ReducedTensorWords.filtrationLimit_apply_of_mem_filtration
            c.obstructionStageSeq_g_stabilises hu) hw
    have hH : c.rightHomotopyCoderiv z =
        ReducedTensorWords.gradedCoderivAlong (BB.grading.shift 1) 1
          (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (c.obstructionStageSeq k).g) LinearMap.id
          (c.obstructionStageSeq k).h z :=
      (ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
        (f.comp c.homotopyInverse).isCoalgHom_barMap (AInfinityHom.id BB).isCoalgHom_barMap _)
        |>.apply_eq_of_mem_filtration
          (ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
            (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom _))
            (ReducedTensorWords.isCoalgHom_id B) _)
          (fun w hw ↦ by rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply, hG w hw])
          (fun w _ ↦ by rw [barMap_id])
          (fun _ hw ↦ by
            rw [← LinearMap.comp_apply (ReducedTensorWords.letter R B),
              ReducedTensorWords.letter_comp_gradedCoderivAlong,
              ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
              ReducedTensorWords.letter_comp_gradedCoderivAlong]
            exact ReducedTensorWords.filtrationLimit_apply_of_mem_filtration
              c.obstructionStageSeq_h_stabilises hw) hz
    rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      taylor_comp, LinearMap.comp_apply, hG z hz, taylor_id, hH,
      ReducedTensorWords.letter_comp_gradedCoderivAlong,
      ReducedTensorWords.filtrationLimit_apply_of_mem_filtration
        c.obstructionStageSeq_h_stabilises (BB.barDifferential_mem_filtration hz)]
    exact (c.obstructionStageSeq k).homotopy_eq z hz

/-- **The right homotopy `f ∘ c.homotopyInverse ∼ id_B`.** -/
noncomputable def compHomotopyInverse (c : f.LinearHomotopyInverse) :
    Homotopy (f.comp c.homotopyInverse) (AInfinityHom.id BB) :=
  Homotopy.ofCoderivation c.rightHomotopyCoderiv
    (ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong (BB.grading.shift 1) 1
      (f.comp c.homotopyInverse).isCoalgHom_barMap (AInfinityHom.id BB).isCoalgHom_barMap _)
    (ReducedTensorWords.isHomogeneous_gradedCoderivAlong
      (f.comp c.homotopyInverse).isHomogeneous_barMap (AInfinityHom.id BB).isHomogeneous_barMap
      (ReducedTensorWords.isHomogeneous_filtrationLimit c.obstructionStageSeq_h_stabilises
        fun n ↦ (c.obstructionStageSeq n).isHomogeneous_h))
    c.comp_homotopyInverse_eq

/-- The arity-one component of `c.compHomotopyInverse` is `c.rightHomotopy`. -/
@[simp]
theorem linearHomotopy_compHomotopyInverse (c : f.LinearHomotopyInverse) :
    c.compHomotopyInverse.linearHomotopy = c.rightHomotopy :=
  LinearMap.ext fun b ↦ by
    rw [Homotopy.linearHomotopy_apply, compHomotopyInverse, Homotopy.taylor_ofCoderivation,
      ReducedTensorWords.letter_comp_gradedCoderivAlong,
      ReducedTensorWords.filtrationLimit_apply_of_mem_filtration
        c.obstructionStageSeq_h_stabilises (ReducedTensorWords.ofLetter_mem_filtration R B b)]
    change (c.rightHomotopy ∘ₗ ReducedTensorWords.letter R B)
      (ReducedTensorWords.ofLetter R B b) = c.rightHomotopy b
    rw [LinearMap.comp_apply, ReducedTensorWords.letter_ofLetter]

/-- **The left homotopy `c.homotopyInverse ∘ f ∼ id_A`.**  It is obtained by lifting the whiskered
right homotopy `f ∘ (g ∘ f) = (f ∘ g) ∘ f ∼ id_B ∘ f = f ∘ id_A` across `f`. -/
noncomputable def homotopyInverseComp (c : f.LinearHomotopyInverse) :
    Homotopy (c.homotopyInverse.comp f) (AInfinityHom.id AA) :=
  c.liftHomotopy <|
    Homotopy.cast (f.comp_assoc c.homotopyInverse f)
      ((f.id_comp).trans (f.comp_id).symm) (c.compHomotopyInverse.compLeft f)

/-- On cohomology, `c.homotopyInverse` is a right inverse of `f`. -/
@[simp]
theorem cohomologyMap_comp_homotopyInverse (c : f.LinearHomotopyInverse) :
    f.cohomologyMap.comp c.homotopyInverse.cohomologyMap = NonUnitalAlgHom.id R BB.Cohomology := by
  simpa only [cohomologyMap_comp, cohomologyMap_id] using
    c.compHomotopyInverse.cohomologyMap_eq

/-- On cohomology, `c.homotopyInverse` is a left inverse of `f`. -/
@[simp]
theorem cohomologyMap_homotopyInverse_comp (c : f.LinearHomotopyInverse) :
    c.homotopyInverse.cohomologyMap.comp f.cohomologyMap = NonUnitalAlgHom.id R AA.Cohomology := by
  simpa only [cohomologyMap_comp, cohomologyMap_id] using
    c.homotopyInverseComp.cohomologyMap_eq

end HomotopyInverse

end LinearHomotopyInverse

/-! ### Homotopy equivalences of A-infinity algebras -/

/-- An `A∞` morphism `f : A ⟶ B` is a **homotopy equivalence** when there exists an `A∞` morphism
`g : B ⟶ A` together with homotopies `g ∘ f ∼ id_A` and `f ∘ g ∼ id_B`. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
      Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB))

/-- Unfold `IsHomotopyEquiv`. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ g : AInfinityHom BB AA,
        Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
          Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB)) :=
  Iff.rfl

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv :=
  ⟨AInfinityHom.id AA,
    ⟨Homotopy.cast (id_comp _).symm rfl (Homotopy.refl _)⟩,
    ⟨Homotopy.cast (id_comp _).symm rfl (Homotopy.refl _)⟩⟩

/-- Every `A∞` isomorphism is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv := by
  obtain ⟨g, hgf, hfg⟩ := (isIso_def f).1 hf
  exact ⟨g, ⟨Homotopy.cast hgf.symm rfl (Homotopy.refl _)⟩,
    ⟨Homotopy.cast hfg.symm rfl (Homotopy.refl _)⟩⟩

/-- Every `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨g, ⟨h₁⟩, ⟨h₂⟩⟩ := hf
  have hgf := h₁.cohomologyMap_eq
  rw [cohomologyMap_comp, cohomologyMap_id] at hgf
  have hfg := h₂.cohomologyMap_eq
  rw [cohomologyMap_comp, cohomologyMap_id] at hfg
  rw [isQuasiIso_def]
  refine Function.bijective_iff_has_inverse.2 ⟨g.cohomologyMap, fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [← NonUnitalAlgHom.comp_apply, hgf, NonUnitalAlgHom.coe_id, id_eq]
  · rw [← NonUnitalAlgHom.comp_apply, hfg, NonUnitalAlgHom.coe_id, id_eq]

/-- Every graded chain-homotopy inverse of `f.linearPart` makes `f` an `A∞` homotopy
equivalence. -/
theorem LinearHomotopyInverse.isHomotopyEquiv {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) : f.IsHomotopyEquiv :=
  ⟨c.homotopyInverse, ⟨c.homotopyInverseComp⟩, ⟨c.compHomotopyInverse⟩⟩

/-- If `f.linearPart` admits a graded chain-homotopy inverse, then `f` is a quasi-isomorphism. -/
theorem LinearHomotopyInverse.isQuasiIso {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) : f.IsQuasiIso :=
  c.isHomotopyEquiv.isQuasiIso

/-- The `A∞` homotopy inverse built from `c` is itself a homotopy equivalence. -/
theorem LinearHomotopyInverse.isHomotopyEquiv_homotopyInverse {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) : c.homotopyInverse.IsHomotopyEquiv :=
  ⟨f, ⟨c.compHomotopyInverse⟩, ⟨c.homotopyInverseComp⟩⟩

/-- The `A∞` homotopy inverse built from `c` is a quasi-isomorphism. -/
theorem LinearHomotopyInverse.isQuasiIso_homotopyInverse {f : AInfinityHom AA BB}
    (c : f.LinearHomotopyInverse) : c.homotopyInverse.IsQuasiIso :=
  c.isHomotopyEquiv_homotopyInverse.isQuasiIso

/-- The linear part of an `A∞` homotopy equivalence admits a graded chain-homotopy inverse. -/
theorem IsHomotopyEquiv.nonempty_linearHomotopyInverse {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) : Nonempty f.LinearHomotopyInverse := by
  obtain ⟨_, ⟨h₁⟩, ⟨h₂⟩⟩ := hf
  exact ⟨LinearHomotopyInverse.ofHomotopy h₁ h₂⟩

/-- **Over any commutative ring, an `A∞` morphism is a homotopy equivalence if and only if its
linear part admits a graded chain-homotopy inverse.** -/
theorem isHomotopyEquiv_iff_nonempty_linearHomotopyInverse (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ Nonempty f.LinearHomotopyInverse :=
  ⟨IsHomotopyEquiv.nonempty_linearHomotopyInverse, fun ⟨c⟩ ↦ c.isHomotopyEquiv⟩

/-- Unpacked characterization of `A∞` homotopy equivalences in terms of `f.linearPart`. -/
theorem isHomotopyEquiv_iff_exists_linearPart (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ (g₁ : B →ₗ[R] A) (hL : Module.End R A) (hR : Module.End R B),
        LinearMap.IsHomogeneous g₁ BB.grading.piece AA.grading.piece 0 ∧
        AA.differential ∘ₗ g₁ = g₁ ∘ₗ BB.differential ∧
        LinearMap.IsHomogeneous hL AA.grading.piece AA.grading.piece (-1) ∧
        g₁ ∘ₗ f.linearPart - LinearMap.id =
          AA.differential ∘ₗ hL + hL ∘ₗ AA.differential ∧
        LinearMap.IsHomogeneous hR BB.grading.piece BB.grading.piece (-1) ∧
        f.linearPart ∘ₗ g₁ - LinearMap.id =
          BB.differential ∘ₗ hR + hR ∘ₗ BB.differential := by
  rw [isHomotopyEquiv_iff_nonempty_linearHomotopyInverse]
  exact ⟨fun ⟨c⟩ ↦ ⟨c.inv, c.leftHomotopy, c.rightHomotopy, c.isHomogeneous_inv,
      c.differential_comp_inv, c.isHomogeneous_leftHomotopy, c.inv_comp_linearPart_sub_id,
      c.isHomogeneous_rightHomotopy, c.linearPart_comp_inv_sub_id⟩,
    fun ⟨g₁, hL, hR, hg₁, hd, hhL, hL_eq, hhR, hR_eq⟩ ↦
      ⟨⟨g₁, hg₁, hd, hL, hhL, hL_eq, hR, hhR, hR_eq⟩⟩⟩

/-- Homotopy equivalences of `A∞` algebras are closed under composition. -/
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨cg⟩ := hg.nonempty_linearHomotopyInverse
  obtain ⟨cf⟩ := hf.nonempty_linearHomotopyInverse
  exact (cg.comp cf).isHomotopyEquiv

end CommRing

/-! ### Homotopy inverses of quasi-isomorphisms over a field -/

section Field

variable {K : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [Field K]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]
  {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B} {CC : AInfinityAlgebra K C}

namespace IsQuasiIso

private noncomputable def linearInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) : B →ₗ[K] A :=
  AA.cohomologyContraction.incl ∘ₗ hf.cohomologyLinearEquiv.symm.toLinearMap ∘ₗ
    BB.cohomologyContraction.proj

private theorem proj_comp_linearPart_comp_incl {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    BB.cohomologyContraction.proj ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.incl =
      hf.cohomologyLinearEquiv.toLinearMap :=
  LinearMap.ext fun x ↦ by
    have hx := AA.cohomologyContraction_incl_mem_cycles x
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      BB.cohomologyContraction_proj_of_mem_cycles (f.linearPart_mem_cycles hx),
      ← f.cohomologyMap_cohomologyClass hx, AA.cohomologyClass_cohomologyContraction_incl,
      LinearEquiv.coe_coe, hf.cohomologyLinearEquiv_apply]

private theorem isHomogeneous_linearInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearMap.IsHomogeneous hf.linearInv BB.grading.piece AA.grading.piece 0 := by
  have he : LinearMap.IsHomogeneous hf.cohomologyLinearEquiv.symm.toLinearMap
      BB.cohomologyGrading.piece AA.cohomologyGrading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hc ↦ by
      rw [add_zero, LinearEquiv.coe_coe, ← hf.cohomologyMapInv_apply]
      exact hf.cohomologyMapInv_mem_cohomologyGrading_piece hc
  simpa only [linearInv, add_zero] using
    AA.isHomogeneous_cohomologyContraction_incl.comp
      (he.comp BB.isHomogeneous_cohomologyContraction_proj)

private theorem differential_linearInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AA.differential ∘ₗ hf.linearInv = 0 ∧ hf.linearInv ∘ₗ BB.differential = 0 :=
  ⟨LinearMap.ext fun y ↦ by
      have h := LinearMap.congr_fun AA.cohomologyContraction.dM_comp_incl
        (hf.cohomologyLinearEquiv.symm (BB.cohomologyContraction.proj y))
      simpa only [linearInv, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply,
        map_zero] using h,
    LinearMap.ext fun y ↦ by
      have h := LinearMap.congr_fun BB.cohomologyContraction.proj_comp_dM y
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
      simp only [linearInv, LinearMap.comp_apply, LinearMap.zero_apply, h, map_zero]⟩

private theorem linearInv_comp_linearPart_sub_id {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.linearInv ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ
          (hf.linearInv ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.homotopy -
            AA.cohomologyContraction.homotopy) +
        (hf.linearInv ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.homotopy -
          AA.cohomologyContraction.homotopy) ∘ₗ AA.differential := by
  refine LinearMap.ext fun x ↦ ?_
  have hinv_f_incl :
      hf.linearInv (f.linearPart (AA.cohomologyContraction.incl
        (AA.cohomologyContraction.proj x))) =
        AA.cohomologyContraction.incl (AA.cohomologyContraction.proj x) := by
    have h := LinearMap.congr_fun hf.proj_comp_linearPart_comp_incl
      (AA.cohomologyContraction.proj x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
    simp only [linearInv, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h, LinearEquiv.symm_apply_apply]
  have hsplit : AA.differential (AA.cohomologyContraction.homotopy x) +
      AA.cohomologyContraction.homotopy (AA.differential x) =
      x - AA.cohomologyContraction.incl (AA.cohomologyContraction.proj x) := by
    simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
      using LinearMap.congr_fun AA.cohomologyContraction.dM_comp_homotopy_add_homotopy_comp_dM x
  have hx : x = AA.cohomologyContraction.incl (AA.cohomologyContraction.proj x) +
      (AA.differential (AA.cohomologyContraction.homotopy x) +
        AA.cohomologyContraction.homotopy (AA.differential x)) :=
    (eq_sub_iff_add_eq'.1 hsplit).symm
  have hd_inv : AA.differential
      (hf.linearInv (f.linearPart (AA.cohomologyContraction.homotopy x))) = 0 :=
    LinearMap.congr_fun hf.differential_linearInv.1
      (f.linearPart (AA.cohomologyContraction.homotopy x))
  have hinv_d : hf.linearInv
      (f.linearPart (AA.differential (AA.cohomologyContraction.homotopy x))) = 0 := by
    rw [← LinearMap.comp_apply f.linearPart AA.differential, ← f.differential_comp_linearPart,
      LinearMap.comp_apply]
    exact LinearMap.congr_fun hf.differential_linearInv.2
      (f.linearPart (AA.cohomologyContraction.homotopy x))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_sub, hd_inv, zero_sub]
  conv_lhs => rw [hx, map_add, map_add, map_add, map_add, hinv_f_incl, hinv_d, zero_add]
  abel

private theorem linearPart_comp_linearInv_sub_id {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.linearPart ∘ₗ hf.linearInv - LinearMap.id =
      BB.differential ∘ₗ
          (BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ hf.linearInv -
            BB.cohomologyContraction.homotopy) +
        (BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ hf.linearInv -
          BB.cohomologyContraction.homotopy) ∘ₗ BB.differential := by
  refine LinearMap.ext fun y ↦ ?_
  have hproj_f_inv :
      BB.cohomologyContraction.proj (f.linearPart (hf.linearInv y)) =
        BB.cohomologyContraction.proj y := by
    have h := LinearMap.congr_fun hf.proj_comp_linearPart_comp_incl
      (hf.cohomologyLinearEquiv.symm (BB.cohomologyContraction.proj y))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
    simp only [linearInv, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h, LinearEquiv.apply_symm_apply]
  have hsplit_inv :
      BB.differential (BB.cohomologyContraction.homotopy (f.linearPart (hf.linearInv y))) +
        BB.cohomologyContraction.homotopy (BB.differential (f.linearPart (hf.linearInv y))) =
        f.linearPart (hf.linearInv y) -
          BB.cohomologyContraction.incl
            (BB.cohomologyContraction.proj (f.linearPart (hf.linearInv y))) := by
    simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
      using LinearMap.congr_fun BB.cohomologyContraction.dM_comp_homotopy_add_homotopy_comp_dM
        (f.linearPart (hf.linearInv y))
  have hy : BB.differential (BB.cohomologyContraction.homotopy y) =
      y - BB.cohomologyContraction.incl (BB.cohomologyContraction.proj y) -
        BB.cohomologyContraction.homotopy (BB.differential y) :=
    eq_sub_of_add_eq <| by
      simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.id_apply]
        using LinearMap.congr_fun BB.cohomologyContraction.dM_comp_homotopy_add_homotopy_comp_dM y
  have hd_f_inv : BB.differential (f.linearPart (hf.linearInv y)) = 0 := by
    rw [← LinearMap.comp_apply BB.differential f.linearPart, f.differential_comp_linearPart,
      LinearMap.comp_apply,
      show AA.differential (hf.linearInv y) = 0 from
        LinearMap.congr_fun hf.differential_linearInv.1 y,
      map_zero]
  have hinv_dy : hf.linearInv (BB.differential y) = 0 :=
    LinearMap.congr_fun hf.differential_linearInv.2 y
  rw [hd_f_inv, map_zero, add_zero, hproj_f_inv] at hsplit_inv
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_sub, hinv_dy, map_zero, zero_sub]
  rw [hsplit_inv, hy]
  abel

/-- Over a field, the linear part of every quasi-isomorphism admits a graded chain-homotopy
inverse, built from the contractions of the unary complexes onto cohomology. -/
noncomputable def linearHomotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.LinearHomotopyInverse where
  inv := hf.linearInv
  isHomogeneous_inv := hf.isHomogeneous_linearInv
  differential_comp_inv := hf.differential_linearInv.1.trans hf.differential_linearInv.2.symm
  leftHomotopy := hf.linearInv ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.homotopy -
    AA.cohomologyContraction.homotopy
  isHomogeneous_leftHomotopy := by
    have h := hf.isHomogeneous_linearInv.comp
      (f.isHomogeneous_linearPart.comp AA.isHomogeneous_cohomologyContraction_homotopy)
    rw [add_zero, add_zero] at h
    exact h.sub AA.isHomogeneous_cohomologyContraction_homotopy
  inv_comp_linearPart_sub_id := hf.linearInv_comp_linearPart_sub_id
  rightHomotopy := BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ hf.linearInv -
    BB.cohomologyContraction.homotopy
  isHomogeneous_rightHomotopy := by
    have h := BB.isHomogeneous_cohomologyContraction_homotopy.comp
      (f.isHomogeneous_linearPart.comp hf.isHomogeneous_linearInv)
    rw [add_zero, zero_add] at h
    exact h.sub BB.isHomogeneous_cohomologyContraction_homotopy
  linearPart_comp_inv_sub_id := hf.linearPart_comp_linearInv_sub_id

/-- **An `A∞` homotopy inverse of a quasi-isomorphism over a field.** -/
noncomputable def homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityHom BB AA :=
  hf.linearHomotopyInverse.homotopyInverse

/-- **The right homotopy `f ∘ hf.homotopyInverse ∼ id_B` for a quasi-isomorphism over a
field.** -/
noncomputable def compHomotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (f.comp hf.homotopyInverse) (AInfinityHom.id BB) :=
  hf.linearHomotopyInverse.compHomotopyInverse

/-- **The left homotopy `hf.homotopyInverse ∘ f ∼ id_A` for a quasi-isomorphism over a
field.** -/
noncomputable def homotopyInverseComp {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (hf.homotopyInverse.comp f) (AInfinityHom.id AA) :=
  hf.linearHomotopyInverse.homotopyInverseComp

/-- The map induced on cohomology by `hf.homotopyInverse` is `hf.cohomologyMapInv`. -/
@[simp]
theorem cohomologyMap_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInverse.cohomologyMap = hf.cohomologyMapInv := by
  ext c
  have h := DFunLike.congr_fun hf.compHomotopyInverse.cohomologyMap_eq c
  simp only [cohomologyMap_comp, cohomologyMap_id, NonUnitalAlgHom.comp_apply,
    NonUnitalAlgHom.coe_id, id_eq] at h
  have hinv := DFunLike.congr_fun hf.cohomologyMapInv_comp_cohomologyMap
    (hf.homotopyInverse.cohomologyMap c)
  simp only [NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.coe_id, id_eq] at hinv
  rw [← hinv, h]

/-- The homotopy inverse of a quasi-isomorphism over a field is again a quasi-isomorphism. -/
theorem isQuasiIso_homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyInverse.IsQuasiIso :=
  hf.linearHomotopyInverse.isQuasiIso_homotopyInverse

/-- Over a field, every quasi-isomorphism of `A∞` algebras is a homotopy equivalence. -/
theorem isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) : f.IsHomotopyEquiv :=
  hf.linearHomotopyInverse.isHomotopyEquiv

/-- Over a field, lift a homotopy `Homotopy (f.comp u) (f.comp v)` across a quasi-isomorphism
`f`. -/
noncomputable def liftHomotopy {f : AInfinityHom AA BB} (hf : f.IsQuasiIso)
    {u v : AInfinityHom CC AA} (h : Homotopy (f.comp u) (f.comp v)) : Homotopy u v :=
  hf.linearHomotopyInverse.liftHomotopy h

/-- Over a field, postcomposing with a quasi-isomorphism reflects and preserves the existence of a
homotopy. -/
theorem nonempty_homotopy_comp_left_iff {f : AInfinityHom AA BB} (hf : f.IsQuasiIso)
    (u v : AInfinityHom CC AA) :
    Nonempty (Homotopy (f.comp u) (f.comp v)) ↔ Nonempty (Homotopy u v) :=
  hf.linearHomotopyInverse.nonempty_homotopy_comp_left_iff u v

end IsQuasiIso

/-- **Whitehead's theorem for `A∞` algebras over a field:** an `A∞` morphism is a homotopy
equivalence if and only if it is a quasi-isomorphism. -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end Field

end AInfinityHom

end TauCeti
