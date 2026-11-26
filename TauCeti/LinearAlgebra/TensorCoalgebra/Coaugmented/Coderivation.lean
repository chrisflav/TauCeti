/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Graded.Insertion
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Grading
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Taylor
public import TauCeti.LinearAlgebra.TensorCoalgebra.Primitives

/-!
# General graded coderivations of the coaugmented tensor coalgebra

`TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Taylor` establishes the Taylor correspondence for
`q`-twisted graded coderivations of the coaugmented tensor coalgebra
`Tᶜ(M) = ⨁_{n ≥ 0} M^{⊗n}` that annihilate the empty word.  For a general `q`-twisted graded
coderivation `b`, however, `b 1` need not vanish: its length-one component `m₀ := letter (b 1)`
is a curvature element in `M`, and `b 1` equals `ofLetter m₀` because the counit of any value
vanishes and the co-Leibniz rule kills higher components of `b 1`.

This file removes the coaugmentation-preservation restriction.  Every element `m₀ ∈ M` generates
a nullary insertion coderivation `TauCeti.TensorWords.insertGradedCoderiv G q m₀`, sending a
tensor word `w` with coproduct `Δ w = ∑ w₁ ⊗ w₂` to
`∑ (τ(w₁) * ofLetter m₀) * w₂`, where `τ = TensorWords.map (G.koszulTwist q)`.
Adding this nullary coderivation to the zero-extended reduced Taylor expansion of
`F ∘ reducedInclusion` yields the general graded Taylor expansion
`TauCeti.TensorWords.gradedCoderiv G F q` for any Taylor map `F : TensorWords R M →ₗ[R] M`, and
gives the linear equivalence `TauCeti.TensorWords.taylorEquiv` between all `q`-twisted graded
coderivations of `Tᶜ(M)` and `TensorWords R M →ₗ[R] M`.

We also show that the square of a `q`-twisted graded coderivation anticommuting with `τ`—in
particular, a homogeneous degree-`1` coderivation at `q = 1`—is an ungraded (`0`-twisted)
coderivation of `Tᶜ(M)`, hence vanishes identically if and only if its letter component
`letter ∘ (b ∘ b)` vanishes.

## Main definitions

* `TauCeti.TensorWords.ofLetter` and `TauCeti.TensorWords.letter`: the single-letter inclusion
  and projection on `TensorWords R M`.
* `TauCeti.TensorWords.gradedCoderivations`: the submodule of all `q`-twisted graded coderivations
  of `TensorWords R M`, without requiring `b 1 = 0`.
* `TauCeti.TensorWords.insertGradedCoderiv`: the nullary insertion coderivation `δ(m₀)` inserting
  `m₀` between every cut of a word with Koszul sign on the prefix.
* `TauCeti.TensorWords.gradedCoderiv`: the graded Taylor expansion of an arbitrary Taylor map
  `F : TensorWords R M →ₗ[R] M`.
* `TauCeti.TensorWords.taylorEquiv`: the linear equivalence between `gradedCoderivations G q` and
  `TensorWords R M →ₗ[R] M`.

## Main results

* `TauCeti.TensorWords.IsGradedCoderivation.eq_of_letter_comp_eq`: a `q`-twisted graded
  coderivation of `TensorWords R M` is uniquely determined by `letter ∘ₗ b`.
* `TauCeti.TensorWords.isGradedCoderivation_insertGradedCoderiv`: `insertGradedCoderiv G q m₀` is
  a `q`-twisted graded coderivation sending `1` to `ofLetter m₀`.
* `TauCeti.TensorWords.isHomogeneous_gradedCoderiv` and
  `TauCeti.TensorWords.IsGradedCoderivation.isHomogeneous_iff`: homogeneity of `b` is equivalent
  to homogeneity of its Taylor map `letter ∘ₗ b`.
* `TauCeti.TensorWords.IsGradedCoderivation.comp_self_eq_zero_iff_letter_comp_eq_zero`: an odd
  graded coderivation squares to zero if and only if `letter ∘ₗ (b ∘ₗ b) = 0`.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace TensorWords

section Letter

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Include a single letter into the coaugmented tensor coalgebra as a word of length one. -/
noncomputable def ofLetter : M →ₗ[R] TensorWords R M :=
  of R M 1 ∘ₗ (TauCeti.TensorPower.oneEquiv R M).symm.toLinearMap

/-- Read the length-one component of a tensor word as an element of `M`. -/
noncomputable def letter : TensorWords R M →ₗ[R] M :=
  (TauCeti.TensorPower.oneEquiv R M).toLinearMap ∘ₗ component R M 1

variable {R M}

/-- Definition of `ofLetter` via `of R M 1` and `TauCeti.TensorPower.oneEquiv`. -/
theorem ofLetter_def :
    ofLetter R M = of R M 1 ∘ₗ (TauCeti.TensorPower.oneEquiv R M).symm.toLinearMap := (rfl)

/-- A single letter is the pure tensor word of length one on that letter. -/
theorem ofLetter_eq_of_tprod (a : M) :
    ofLetter R M a = of R M 1 (PiTensorProduct.tprod R fun _ ↦ a) := by
  rw [ofLetter_def, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TauCeti.TensorPower.oneEquiv_symm_apply]

/-- Including a single reduced letter agrees with including it directly into tensor words. -/
@[simp]
theorem reducedInclusion_ofLetter (a : M) :
    reducedInclusion R M (ReducedTensorWords.ofLetter R M a) = ofLetter R M a := by
  rw [ReducedTensorWords.ofLetter_eq_of_tprod, reducedInclusion_of, ofLetter_eq_of_tprod]
  rfl

/-- Composition of `reducedInclusion` and `ReducedTensorWords.ofLetter` is `ofLetter`. -/
theorem reducedInclusion_comp_ofLetter :
    reducedInclusion R M ∘ₗ ReducedTensorWords.ofLetter R M = ofLetter R M :=
  LinearMap.ext (reducedInclusion_ofLetter (R := R) (M := M))

/-- Projecting a single letter to reduced tensor words gives the reduced single letter. -/
@[simp]
theorem reducedProjection_ofLetter (a : M) :
    reducedProjection R M (ofLetter R M a) = ReducedTensorWords.ofLetter R M a := by
  rw [← reducedInclusion_ofLetter, reducedProjection_reducedInclusion]

/-- The length-one component of a single letter is that letter under `oneEquiv`. -/
theorem component_one_ofLetter (a : M) :
    component R M 1 (ofLetter R M a) = (TauCeti.TensorPower.oneEquiv R M).symm a := by
  rw [ofLetter_def, LinearMap.comp_apply, component_of, LinearEquiv.coe_coe]

/-- Every component of a single letter away from length one vanishes. -/
@[simp]
theorem component_ofLetter_of_ne {n : ℕ} (hn : n ≠ 1) (a : M) :
    component R M n (ofLetter R M a) = 0 := by
  rw [ofLetter_def, LinearMap.comp_apply, component_of_of_ne R M hn.symm]

/-- A single letter is annihilated by the counit. -/
@[simp]
theorem counit_ofLetter (a : M) : counit R M (ofLetter R M a) = 0 := by
  rw [← reducedInclusion_ofLetter, counit_reducedInclusion]

/-- The letter of a tensor word is its length-one component read through `oneEquiv`. -/
theorem letter_apply (w : TensorWords R M) :
    letter R M w = TauCeti.TensorPower.oneEquiv R M (component R M 1 w) := (rfl)

/-- Reading the letter of an included reduced word agrees with `ReducedTensorWords.letter`. -/
@[simp]
theorem letter_reducedInclusion (w : ReducedTensorWords R M) :
    letter R M (reducedInclusion R M w) = ReducedTensorWords.letter R M w := by
  rw [letter_apply, component_reducedInclusion, dite_eq_left Nat.one_pos,
    ReducedTensorWords.letter_apply]
  rfl

/-- `letter` composed with `reducedInclusion` is `ReducedTensorWords.letter`. -/
theorem letter_comp_reducedInclusion :
    letter R M ∘ₗ reducedInclusion R M = ReducedTensorWords.letter R M :=
  LinearMap.ext (letter_reducedInclusion (R := R) (M := M))

/-- `letter` factors through `reducedProjection`. -/
theorem letter_eq_reduced_comp_reducedProjection :
    letter R M = ReducedTensorWords.letter R M ∘ₗ reducedProjection R M := by
  refine LinearMap.ext fun w ↦ ?_
  rw [letter_apply, LinearMap.comp_apply, ReducedTensorWords.letter_apply,
    component_reducedProjection]
  rfl

/-- The empty word has no letter component. -/
@[simp]
theorem letter_one : letter R M (1 : TensorWords R M) = 0 := by
  rw [letter_eq_reduced_comp_reducedProjection, LinearMap.comp_apply, reducedProjection_one,
    map_zero]

/-- A word of length zero has no letter component. -/
theorem letter_of_zero (z : TensorPower R 0 M) : letter R M (of R M 0 z) = 0 := by
  rw [letter_apply, component_of_of_ne R M Nat.zero_ne_one, map_zero]

/-- A word of length different from one has no letter component. -/
@[simp]
theorem letter_of_of_ne {n : ℕ} (hn : n ≠ 1) (z : TensorPower R n M) :
    letter R M (of R M n z) = 0 := by
  rw [letter_apply, component_of_of_ne R M hn, map_zero]

/-- A word of length one has letter equal to its single entry. -/
@[simp]
theorem letter_of_one (x : Fin 1 → M) :
    letter R M (of R M 1 (PiTensorProduct.tprod R x)) = x 0 := by
  rw [letter_apply, component_of, TauCeti.TensorPower.oneEquiv_tprod]

/-- Reading the letter of `ofLetter R M a` returns `a`. -/
@[simp]
theorem letter_ofLetter (a : M) : letter R M (ofLetter R M a) = a := by
  rw [← reducedInclusion_ofLetter, letter_reducedInclusion, ReducedTensorWords.letter_ofLetter]

/-- `letter` retracts `ofLetter`. -/
@[simp]
theorem letter_comp_ofLetter : letter R M ∘ₗ ofLetter R M = LinearMap.id :=
  LinearMap.ext (letter_ofLetter (R := R) (M := M))

/-- Deconcatenation of a single letter yields its two outer cuts. -/
@[simp]
theorem deconcatenation_ofLetter (a : M) :
    deconcatenation R M (ofLetter R M a) =
      (1 : TensorWords R M) ⊗ₜ[R] ofLetter R M a +
        ofLetter R M a ⊗ₜ[R] (1 : TensorWords R M) := by
  rw [ofLetter_def, LinearMap.comp_apply, deconcatenation_of_length_one]

/-- A block of length one is the corresponding single letter. -/
theorem subword_one {n : ℕ} (z : Fin n → M) {a : ℕ} (ha : a < n) :
    subword R z a 1 = ofLetter R M (z ⟨a, ha⟩) := by
  rw [← reducedInclusion_subword R z Nat.one_pos, ReducedTensorWords.subword_one R M z ha,
    reducedInclusion_ofLetter]

/-- A block of length other than one has no letter component. -/
theorem letter_subword_of_ne_one {n : ℕ} (z : Fin n → M) (a : ℕ) {b : ℕ} (hb : b ≠ 1) :
    letter R M (subword R z a b) = 0 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · by_cases ha : a ≤ n
    · rw [subword_length_zero R z ha, letter_one]
    · rw [subword_eq_zero_of_lt_add R z (by omega), map_zero]
  · rw [← reducedInclusion_subword R z hb0, letter_reducedInclusion,
      ReducedTensorWords.letter_subword_of_ne_one R M z a hb]

/-- Mapping a single letter applies the linear map to that letter. -/
@[simp]
theorem map_ofLetter {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (a : M) :
    map f (ofLetter R M a) = ofLetter R N (f a) := by
  rw [← reducedInclusion_ofLetter, ← LinearMap.comp_apply (map f), map_comp_reducedInclusion,
    LinearMap.comp_apply, ReducedTensorWords.map_ofLetter, reducedInclusion_ofLetter]

/-- Reading off the letter of a letterwise-mapped word applies the linear map to its letter. -/
@[simp]
theorem letter_comp_map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    letter R N ∘ₗ map f = f ∘ₗ letter R M := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, map_of_tprod]
  rcases eq_or_ne n 1 with rfl | hn
  · simp
  · simp [hn]

end Letter

section GradedLetter

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- A homogeneous letter defines a tensor word of the same total degree. -/
theorem ofLetter_mem_gradedPiece (G : InternalGrading R M ℤ) {p : ℤ} {a : M}
    (ha : a ∈ G.piece p) : ofLetter R M a ∈ gradedPiece G p := by
  rw [← reducedInclusion_ofLetter]
  exact mem_gradedPiece_of_reducedInclusion (ReducedTensorWords.ofLetter_mem_gradedPiece G ha)

/-- Including single letters has total degree zero. -/
theorem isHomogeneous_ofLetter (G : InternalGrading R M ℤ) :
    LinearMap.IsHomogeneous (ofLetter R M) G.piece (gradedPiece G) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p a ha
  rw [add_zero]
  exact ofLetter_mem_gradedPiece G ha

/-- Projecting onto single letters has total degree zero. -/
theorem isHomogeneous_letter (G : InternalGrading R M ℤ) :
    LinearMap.IsHomogeneous (letter R M) (gradedPiece G) G.piece 0 := by
  rw [letter_eq_reduced_comp_reducedProjection]
  simpa only [add_zero] using
    (ReducedTensorWords.isHomogeneous_letter G).comp (isHomogeneous_reducedProjection G)

end GradedLetter

section SubmoduleAndDeterminedness

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- The `R`-submodule of all `q`-twisted graded coderivations of the coaugmented tensor coalgebra
`TensorWords R M`.  Unlike `coaugmentationPreservingGradedCoderivations`, elements are not required
to annihilate the empty word. -/
noncomputable def gradedCoderivations (G : InternalGrading R M ℤ) (q : ℤ) :
    Submodule R (TensorWords R M →ₗ[R] TensorWords R M) where
  carrier := {b | IsGradedCoderivation G q b}
  zero_mem' := by
    change IsGradedCoderivation G q 0
    rw [isGradedCoderivation_iff]
    simp
  add_mem' {b₁ b₂} hb₁ hb₂ := by
    change IsGradedCoderivation G q (b₁ + b₂)
    rw [isGradedCoderivation_iff]
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add,
      hb₁.deconcatenation_apply, hb₂.deconcatenation_apply,
      LinearMap.rTensor_add, LinearMap.lTensor_add]
    abel
  smul_mem' r b hb := by
    change IsGradedCoderivation G q (r • b)
    rw [isGradedCoderivation_iff]
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
      hb.deconcatenation_apply, LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]

/-- Membership in `gradedCoderivations G q` is the `q`-twisted co-Leibniz identity. -/
@[simp]
theorem mem_gradedCoderivations (G : InternalGrading R M ℤ) {q : ℤ}
    {b : TensorWords R M →ₗ[R] TensorWords R M} :
    b ∈ gradedCoderivations G q ↔ IsGradedCoderivation G q b :=
  Iff.rfl

/-- Every coaugmentation-preserving graded coderivation is a graded coderivation. -/
theorem coaugmentationPreservingGradedCoderivations_le (G : InternalGrading R M ℤ) (q : ℤ) :
    coaugmentationPreservingGradedCoderivations G q ≤ gradedCoderivations G q :=
  fun b hb ↦ ((mem_coaugmentationPreservingGradedCoderivations G q b).1 hb).1

/-- If a `q`-twisted graded coderivation has vanishing letter component, then all of its positive-
length components vanish as well, by induction on the output length using the co-Leibniz rule. -/
private theorem IsGradedCoderivation.component_succ_comp_eq_zero {G : InternalGrading R M ℤ}
    {q : ℤ} {b : TensorWords R M →ₗ[R] TensorWords R M} (hb : IsGradedCoderivation G q b)
    (hl : letter R M ∘ₗ b = 0) (k : ℕ) :
    component R M (k + 1) ∘ₗ b = 0 := by
  induction k with
  | zero =>
    refine LinearMap.ext fun w ↦ ?_
    have hw := LinearMap.congr_fun hl w
    rw [LinearMap.comp_apply, LinearMap.zero_apply, letter_apply] at hw
    have hcomp := congrArg (TauCeti.TensorPower.oneEquiv R M).symm hw
    rw [LinearEquiv.symm_apply_apply, map_zero] at hcomp
    exact hcomp
  | succ k ih =>
    refine LinearMap.ext fun w ↦ ?_
    have hdec := LinearMap.congr_fun (map_component_comp_deconcatenation R M (k + 1) 1) (b w)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      hb.deconcatenation_apply w, map_add] at hdec
    have h₁ : TensorProduct.map (component R M (k + 1)) (component R M 1)
        (LinearMap.rTensor (TensorWords R M) b (deconcatenation R M w)) = 0 := by
      have hmap : TensorProduct.map (component R M (k + 1)) (component R M 1) ∘ₗ
          LinearMap.rTensor (TensorWords R M) b =
          TensorProduct.map (component R M (k + 1) ∘ₗ b) (component R M 1) := by
        apply TensorProduct.ext'
        intro u v
        simp
      rw [← LinearMap.comp_apply (TensorProduct.map _ _), hmap, ih, TensorProduct.map_zero_left,
        LinearMap.zero_apply]
    have h₂ : TensorProduct.map (component R M (k + 1)) (component R M 1)
        (LinearMap.lTensor (TensorWords R M) b
          (LinearMap.rTensor (TensorWords R M) (map (G.koszulTwist q))
            (deconcatenation R M w))) = 0 := by
      have hc1 : component R M 1 ∘ₗ b = 0 := by
        refine LinearMap.ext fun z ↦ ?_
        have hz := LinearMap.congr_fun hl z
        rw [LinearMap.comp_apply, LinearMap.zero_apply, letter_apply] at hz
        have hcomp := congrArg (TauCeti.TensorPower.oneEquiv R M).symm hz
        rwa [LinearEquiv.symm_apply_apply, map_zero] at hcomp
      have hmap : TensorProduct.map (component R M (k + 1)) (component R M 1) ∘ₗ
          LinearMap.lTensor (TensorWords R M) b =
          TensorProduct.map (component R M (k + 1)) (component R M 1 ∘ₗ b) := by
        apply TensorProduct.ext'
        intro u v
        simp
      rw [← LinearMap.comp_apply (TensorProduct.map _ _), hmap, hc1, TensorProduct.map_zero_right,
        LinearMap.zero_apply]
    rw [h₁, h₂, add_zero] at hdec
    exact (TensorPower.mulEquiv (R := R) (M := M)).symm.injective
      (hdec.symm.trans (map_zero _).symm)

/-- A `q`-twisted graded coderivation whose letter component vanishes is identically zero. -/
theorem IsGradedCoderivation.eq_zero_of_letter_comp_eq_zero {G : InternalGrading R M ℤ} {q : ℤ}
    {b : TensorWords R M →ₗ[R] TensorWords R M} (hb : IsGradedCoderivation G q b)
    (hl : letter R M ∘ₗ b = 0) : b = 0 := by
  refine LinearMap.ext fun w ↦ DirectSum.ext_component R fun n ↦ ?_
  rw [LinearMap.zero_apply, ← DirectSum.apply_eq_component, ← DirectSum.apply_eq_component,
    ← component_apply, ← component_apply, map_zero]
  cases n with
  | zero =>
    have hε : counit R M (b w) = 0 := hb.counit_apply w
    rw [TensorWords.counit_apply] at hε
    exact (TensorPower.algebraMap₀ (R := R) (M := M)).symm.injective
      (hε.trans (map_zero _).symm)
  | succ k =>
    exact LinearMap.congr_fun (hb.component_succ_comp_eq_zero hl k) w

/-- A `q`-twisted graded coderivation vanishes if and only if its letter component vanishes. -/
theorem IsGradedCoderivation.eq_zero_iff_letter_comp_eq_zero {G : InternalGrading R M ℤ} {q : ℤ}
    {b : TensorWords R M →ₗ[R] TensorWords R M} (hb : IsGradedCoderivation G q b) :
    b = 0 ↔ letter R M ∘ₗ b = 0 :=
  ⟨fun h ↦ by rw [h, LinearMap.comp_zero], hb.eq_zero_of_letter_comp_eq_zero⟩

/-- A `q`-twisted graded coderivation of `TensorWords R M` is uniquely determined by its letter
component. -/
theorem IsGradedCoderivation.eq_of_letter_comp_eq {G : InternalGrading R M ℤ} {q : ℤ}
    {b₁ b₂ : TensorWords R M →ₗ[R] TensorWords R M}
    (hb₁ : IsGradedCoderivation G q b₁) (hb₂ : IsGradedCoderivation G q b₂)
    (hl : letter R M ∘ₗ b₁ = letter R M ∘ₗ b₂) : b₁ = b₂ := by
  have hb₁' : b₁ ∈ gradedCoderivations G q := (mem_gradedCoderivations G).2 hb₁
  have hb₂' : (-1 : R) • b₂ ∈ gradedCoderivations G q :=
    (gradedCoderivations G q).smul_mem (-1) ((mem_gradedCoderivations G).2 hb₂)
  have hadd : IsGradedCoderivation G q (b₁ + (-1 : R) • b₂) :=
    (mem_gradedCoderivations G).1 ((gradedCoderivations G q).add_mem hb₁' hb₂')
  have hzero := hadd.eq_zero_of_letter_comp_eq_zero <| by
    rw [LinearMap.comp_add, LinearMap.comp_smul, hl]
    calc
      letter R M ∘ₗ b₂ + (-1 : R) • (letter R M ∘ₗ b₂)
          = ((1 : R) + (-1 : R)) • (letter R M ∘ₗ b₂) := by rw [add_smul, one_smul]
      _ = 0 := by rw [add_neg_cancel, zero_smul]
  calc
    b₁ = b₁ + ((-1 : R) + (1 : R)) • b₂ := by rw [neg_add_cancel, zero_smul, add_zero]
    _ = (b₁ + (-1 : R) • b₂) + (1 : R) • b₂ := by rw [add_smul, add_assoc]
    _ = b₂ := by rw [hzero, zero_add, one_smul]

/-- Any `q`-twisted graded coderivation maps the empty word to a single letter: namely,
`b 1 = ofLetter R M (letter R M (b 1))`. -/
theorem IsGradedCoderivation.apply_one_eq_ofLetter {G : InternalGrading R M ℤ} {q : ℤ}
    {b : TensorWords R M →ₗ[R] TensorWords R M} (hb : IsGradedCoderivation G q b) :
    b 1 = ofLetter R M (letter R M (b 1)) := by
  refine DirectSum.ext_component R fun n ↦ ?_
  rw [← DirectSum.apply_eq_component, ← DirectSum.apply_eq_component,
    ← component_apply, ← component_apply]
  rcases n with _ | _ | k
  · have hε : counit R M (b 1) = 0 := hb.counit_apply 1
    rw [TensorWords.counit_apply] at hε
    have hc : component R M 0 (b 1) = 0 :=
      (TensorPower.algebraMap₀ (R := R) (M := M)).symm.injective
        (hε.trans (map_zero _).symm)
    rw [hc, component_ofLetter_of_ne (by decide)]
  · rw [component_one_ofLetter, letter_apply, LinearEquiv.symm_apply_apply]
  · have h1 (m : ℕ) (hm : 0 ≠ m) : component R M m (1 : TensorWords R M) = 0 := by
      rw [one_eq_of_zero, component_of_of_ne R M hm]
    have hdec := LinearMap.congr_fun (map_component_comp_deconcatenation R M (k + 1) 1) (b 1)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      hb.deconcatenation_apply 1, deconcatenation_one] at hdec
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_one, map_add,
      TensorProduct.map_tmul, h1 1 (by omega), h1 (k + 1) (by omega),
      TensorProduct.tmul_zero, TensorProduct.zero_tmul, add_zero] at hdec
    have hcomp : component R M (k + 1 + 1) (b 1) = 0 :=
      (TensorPower.mulEquiv (R := R) (M := M)).symm.injective
        (hdec.symm.trans (map_zero _).symm)
    rw [hcomp, component_ofLetter_of_ne (by omega)]

end SubmoduleAndDeterminedness

section InsertGradedCoderiv

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- The linear map multiplying a tensor word on the left and right of a single letter:
`u ⊗ₜ v ↦ (u * ofLetter m₀) * v`. -/
private noncomputable def insertWord (R : Type uR) (M : Type uM)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    (TensorWords R M ⊗[R] M) ⊗[R] TensorWords R M →ₗ[R] TensorWords R M :=
  LinearMap.mul' R (TensorWords R M) ∘ₗ
    LinearMap.rTensor (TensorWords R M)
      (LinearMap.mul' R (TensorWords R M) ∘ₗ LinearMap.lTensor (TensorWords R M) (ofLetter R M))

private theorem insertWord_tmul (u : TensorWords R M) (m₀ : M) (v : TensorWords R M) :
    insertWord R M ((u ⊗ₜ[R] m₀) ⊗ₜ[R] v) = (u * ofLetter R M m₀) * v := by
  simp [insertWord]

/-- On pure tensor words, `insertWord` produces the concatenation subword of length `i + 1 + j`. -/
private theorem insertWord_of_tprod {i j : ℕ} (a : Fin i → M) (m₀ : M) (b : Fin j → M) :
    insertWord R M ((of R M i (PiTensorProduct.tprod R a) ⊗ₜ[R] m₀) ⊗ₜ[R]
        of R M j (PiTensorProduct.tprod R b)) =
      of R M (i + 1 + j) (PiTensorProduct.tprod R
        (Fin.append (Fin.append a (fun _ : Fin 1 ↦ m₀)) b)) := by
  rw [insertWord_tmul, ofLetter_eq_of_tprod, of_tprod_mul_of_tprod, of_tprod_mul_of_tprod]

private theorem of_tprod_cast {m n : ℕ} (h : m = n) (x : Fin m → M) :
    of R M m (PiTensorProduct.tprod R x) =
      of R M n (PiTensorProduct.tprod R (x ∘ Fin.cast h.symm)) := by
  subst h
  rfl

private theorem fin_append_lt {N : Type*} {a b : ℕ} (u : Fin a → N) (v : Fin b → N)
    {k : Fin (a + b)} (hk : k.val < a) : Fin.append u v k = u ⟨k.val, hk⟩ := by
  have hk' : k = Fin.castAdd b ⟨k.val, hk⟩ := Fin.ext rfl
  exact (congrArg (Fin.append u v) hk').trans (Fin.append_left u v _)

private theorem fin_append_ge {N : Type*} {a b : ℕ} (u : Fin a → N) (v : Fin b → N)
    {k : Fin (a + b)} (hk : a ≤ k.val) : Fin.append u v k = v ⟨k.val - a, by omega⟩ := by
  have hk' : k = Fin.natAdd a ⟨k.val - a, by omega⟩ := Fin.ext (by simp [Nat.add_sub_of_le hk])
  exact (congrArg (Fin.append u v) hk').trans (Fin.append_right u v _)

private theorem fin_append_lt_mk {N : Type*} {a b : ℕ} (u : Fin a → N) (v : Fin b → N)
    {k : ℕ} (hk : k < a) (hkab : k < a + b) :
    Fin.append u v ⟨k, hkab⟩ = u ⟨k, hk⟩ :=
  fin_append_lt u v (k := ⟨k, hkab⟩) hk

private theorem fin_append_ge_mk {N : Type*} {a b : ℕ} (u : Fin a → N) (v : Fin b → N)
    {k : ℕ} (hk : a ≤ k) (hkab : k < a + b) :
    Fin.append u v ⟨k, hkab⟩ = v ⟨k - a, by omega⟩ :=
  fin_append_ge u v (k := ⟨k, hkab⟩) hk

/-- Helper reindexing lemma: a single letter at position `i` separates cuts before `i` (falling in
`a`) from cuts after `i` (falling in `b`). -/
private theorem deconcatenation_insertWord_tprod {i j : ℕ} (a : Fin i → M) (m₀ : M)
    (b : Fin j → M) :
    deconcatenation R M (insertWord R M
        ((of R M i (PiTensorProduct.tprod R a) ⊗ₜ[R] m₀) ⊗ₜ[R]
          of R M j (PiTensorProduct.tprod R b))) =
      (∑ c ∈ Finset.range (i + 1),
          subword R a 0 c ⊗ₜ[R]
            ((subword R a c (i - c) * ofLetter R M m₀) * subword R b 0 j)) +
        ∑ k ∈ Finset.range (j + 1),
          ((subword R a 0 i * ofLetter R M m₀) * subword R b 0 k) ⊗ₜ[R]
            subword R b k (j - k) := by
  let u : Fin (i + 1 + j) → M := Fin.append (Fin.append a (fun _ : Fin 1 ↦ m₀)) b
  have hu : insertWord R M ((of R M i (PiTensorProduct.tprod R a) ⊗ₜ[R] m₀) ⊗ₜ[R]
        of R M j (PiTensorProduct.tprod R b)) = subword R u 0 (i + 1 + j) := by
    rw [insertWord_of_tprod, of_tprod_eq_subword]
  have hsub_left (c : ℕ) (hc : c ≤ i) : subword R u 0 c = subword R a 0 c := by
    refine subword_congr R u a (by omega) (by omega) fun k hk ↦ ?_
    simp only [u, Nat.zero_add]
    rw [fin_append_lt_mk _ _ (by omega : k < i + 1), fin_append_lt_mk _ _ (by omega : k < i)]
  have hsub_right_mid (c : ℕ) (hc : c ≤ i) :
      subword R u c (i + 1 + j - c) =
        (subword R a c (i - c) * ofLetter R M m₀) * subword R b 0 j := by
    rw [subword_eq_of_tprod R u (by omega), subword_eq_of_tprod R a (by omega),
      subword_eq_of_tprod R b (by omega), ofLetter_eq_of_tprod, of_tprod_mul_of_tprod,
      of_tprod_mul_of_tprod]
    have hlen : i + 1 + j - c = i - c + 1 + j := by omega
    rw [of_tprod_cast hlen]
    refine of_tprod_congr R M fun l ↦ ?_
    simp only [u, Function.comp_apply, Fin.val_cast]
    rcases lt_or_ge l.val (i - c + 1) with hl | hl
    · rw [fin_append_lt_mk _ _ (by omega : c + l.val < i + 1),
        fin_append_lt_mk _ _ (by omega : l.val < i - c + 1)]
      rcases lt_or_ge l.val (i - c) with hl' | hl'
      · rw [fin_append_lt_mk _ _ (by omega : c + l.val < i),
          fin_append_lt_mk _ _ hl']
      · rw [fin_append_ge_mk _ _ (by omega : i ≤ c + l.val),
          fin_append_ge_mk _ _ hl']
    · rw [fin_append_ge_mk _ _ (by omega : i + 1 ≤ c + l.val),
        fin_append_ge_mk _ _ hl]
      exact congrArg b (Fin.ext (by simp; omega))
  have hsub_left_mid (k : ℕ) (hk : k ≤ j) :
      subword R u 0 (i + 1 + k) =
        (subword R a 0 i * ofLetter R M m₀) * subword R b 0 k := by
    rw [subword_eq_of_tprod R u (by omega), subword_eq_of_tprod R a (by omega),
      subword_eq_of_tprod R b (by omega), ofLetter_eq_of_tprod, of_tprod_mul_of_tprod,
      of_tprod_mul_of_tprod]
    refine of_tprod_congr R M fun l ↦ ?_
    simp only [u, Nat.zero_add]
    rcases lt_or_ge l.val (i + 1) with hl | hl
    · rw [fin_append_lt_mk _ _ hl, fin_append_lt_mk _ _ hl]
    · rw [fin_append_ge_mk _ _ hl, fin_append_ge_mk _ _ hl]
  have hsub_right (k : ℕ) (hk : k ≤ j) :
      subword R u (i + 1 + k) (i + 1 + j - (i + 1 + k)) = subword R b k (j - k) := by
    rw [show i + 1 + j - (i + 1 + k) = j - k by omega]
    refine subword_congr R u b (by omega) (by omega) fun l _ ↦ ?_
    simp only [u]
    rw [fin_append_ge_mk _ _ (by omega : i + 1 ≤ i + 1 + k + l)]
    exact congrArg b (Fin.ext (by simp; omega))
  rw [hu, deconcatenation_subword,
    show i + 1 + j + 1 = (i + 1) + (j + 1) by omega, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun c hc ↦ ?_
    have hc' : c ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
    rw [Nat.zero_add, hsub_left c hc', hsub_right_mid c hc']
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.zero_add, hsub_left_mid k hk', hsub_right k hk']

/-- Deconcatenation of `(u * ofLetter R M m₀) * v` splits cleanly into cuts inside `u` (with the
suffix glued onto `ofLetter m₀ * v`) and cuts inside `v` (with `u * ofLetter m₀` glued onto the
prefix). -/
theorem deconcatenation_mul_ofLetter_mul (u : TensorWords R M) (m₀ : M) (v : TensorWords R M) :
    deconcatenation R M ((u * ofLetter R M m₀) * v) =
      LinearMap.lTensor (TensorWords R M)
          ((LinearMap.mul R (TensorWords R M)).flip v ∘ₗ
            (LinearMap.mul R (TensorWords R M)).flip (ofLetter R M m₀)) (deconcatenation R M u) +
        LinearMap.rTensor (TensorWords R M)
          (LinearMap.mul R (TensorWords R M) (u * ofLetter R M m₀)) (deconcatenation R M v) := by
  let R₁ : (TensorWords R M ⊗[R] M) ⊗[R] TensorWords R M →ₗ[R]
      TensorWords R M ⊗[R] TensorWords R M :=
    LinearMap.lTensor (TensorWords R M) (insertWord R M) ∘ₗ
      (TensorProduct.assoc R (TensorWords R M)
        (TensorWords R M ⊗[R] M) (TensorWords R M)).toLinearMap ∘ₗ
      LinearMap.rTensor (TensorWords R M)
        ((TensorProduct.assoc R (TensorWords R M) (TensorWords R M) M).toLinearMap ∘ₗ
          LinearMap.rTensor M (deconcatenation R M))
  let R₂ : (TensorWords R M ⊗[R] M) ⊗[R] TensorWords R M →ₗ[R]
      TensorWords R M ⊗[R] TensorWords R M :=
    LinearMap.rTensor (TensorWords R M)
        (LinearMap.mul' R (TensorWords R M) ∘ₗ
          LinearMap.rTensor (TensorWords R M)
            (LinearMap.mul' R (TensorWords R M) ∘ₗ
              LinearMap.lTensor (TensorWords R M) (ofLetter R M))) ∘ₗ
      (TensorProduct.assoc R (TensorWords R M ⊗[R] M) (TensorWords R M)
        (TensorWords R M)).symm.toLinearMap ∘ₗ
      LinearMap.lTensor (TensorWords R M ⊗[R] M) (deconcatenation R M)
  have hR₁ (u : TensorWords R M) (m₀ : M) (v : TensorWords R M) :
      R₁ ((u ⊗ₜ[R] m₀) ⊗ₜ[R] v) =
        LinearMap.lTensor (TensorWords R M)
          ((LinearMap.mul R (TensorWords R M)).flip v ∘ₗ
            (LinearMap.mul R (TensorWords R M)).flip (ofLetter R M m₀))
          (deconcatenation R M u) := by
    simp only [R₁, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
    induction deconcatenation R M u using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, insertWord_tmul,
        LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.mul_apply']
    | add x y hx hy =>
      simp only [TensorProduct.add_tmul, map_add, hx, hy]
  have hR₂ (u : TensorWords R M) (m₀ : M) (v : TensorWords R M) :
      R₂ ((u ⊗ₜ[R] m₀) ⊗ₜ[R] v) =
        LinearMap.rTensor (TensorWords R M)
          (LinearMap.mul R (TensorWords R M) (u * ofLetter R M m₀))
          (deconcatenation R M v) := by
    simp only [R₂, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe]
    induction deconcatenation R M v using TensorProduct.inductionOn with
    | tmul c d =>
      simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        LinearMap.comp_apply, LinearMap.mul'_apply, LinearMap.mul_apply']
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy]
  have heq : deconcatenation R M ∘ₗ insertWord R M = R₁ + R₂ := by
    refine linearMap_ext_threefold R M fun i j a m₀ b ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, hR₁, hR₂]
    rw [deconcatenation_insertWord_tprod]
    simp only [of_tprod_eq_subword, deconcatenation_subword, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun c _ ↦ ?_
      simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply, LinearMap.flip_apply,
        LinearMap.mul_apply', Nat.zero_add]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [LinearMap.rTensor_tmul, LinearMap.mul_apply', Nat.zero_add]
  have h := LinearMap.congr_fun heq ((u ⊗ₜ[R] m₀) ⊗ₜ[R] v)
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, insertWord_tmul, hR₁, hR₂] using h

/-- The **nullary insertion coderivation** associated to an element `m₀ ∈ M`: on a word `w`, it
slices `w` at every cut `w = w₁ ⊗ w₂` and returns `∑ (τ(w₁) * ofLetter m₀) * w₂`,
where `τ = TensorWords.map (G.koszulTwist q)`.  In particular, it sends `1` to `ofLetter R M m₀`
and is a `q`-twisted graded coderivation of `TensorWords R M`. -/
noncomputable def insertGradedCoderiv (G : InternalGrading R M ℤ) (q : ℤ) (m₀ : M) :
    TensorWords R M →ₗ[R] TensorWords R M :=
  LinearMap.mul' R (TensorWords R M) ∘ₗ
    LinearMap.rTensor (TensorWords R M)
      ((LinearMap.mul R (TensorWords R M)).flip (ofLetter R M m₀) ∘ₗ
        map (G.koszulTwist q)) ∘ₗ
    deconcatenation R M

/-- The defining formula of `insertGradedCoderiv`. -/
theorem insertGradedCoderiv_def (G : InternalGrading R M ℤ) (q : ℤ) (m₀ : M) :
    insertGradedCoderiv G q m₀ =
      LinearMap.mul' R (TensorWords R M) ∘ₗ
        LinearMap.rTensor (TensorWords R M)
          ((LinearMap.mul R (TensorWords R M)).flip (ofLetter R M m₀) ∘ₗ
            map (G.koszulTwist q)) ∘ₗ
        deconcatenation R M := (rfl)

/-- The nullary insertion coderivation of `0` is zero. -/
@[simp]
theorem insertGradedCoderiv_zero (G : InternalGrading R M ℤ) (q : ℤ) :
    insertGradedCoderiv G q 0 = 0 := by
  simp [insertGradedCoderiv_def]

/-- The nullary insertion coderivation is additive in `m₀`. -/
@[simp]
theorem insertGradedCoderiv_add (G : InternalGrading R M ℤ) (q : ℤ) (m₀ m₀' : M) :
    insertGradedCoderiv G q (m₀ + m₀') =
      insertGradedCoderiv G q m₀ + insertGradedCoderiv G q m₀' := by
  refine LinearMap.ext fun w ↦ ?_
  simp only [insertGradedCoderiv_def, LinearMap.comp_apply, LinearMap.add_apply]
  induction deconcatenation R M w using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply, LinearMap.flip_apply,
      LinearMap.mul_apply', LinearMap.mul'_apply, map_add, LinearMap.add_apply, add_mul]
  | add x y hx hy =>
    rw [map_add (LinearMap.rTensor _ _), map_add (LinearMap.mul' _ _), hx, hy,
      map_add (LinearMap.rTensor _ _), map_add (LinearMap.mul' _ _),
      map_add (LinearMap.rTensor _ _), map_add (LinearMap.mul' _ _)]
    abel

/-- The nullary insertion coderivation is `R`-linear in `m₀`. -/
@[simp]
theorem insertGradedCoderiv_smul (G : InternalGrading R M ℤ) (q : ℤ) (c : R) (m₀ : M) :
    insertGradedCoderiv G q (c • m₀) = c • insertGradedCoderiv G q m₀ := by
  refine LinearMap.ext fun w ↦ ?_
  simp only [insertGradedCoderiv_def, LinearMap.comp_apply, LinearMap.smul_apply]
  induction deconcatenation R M w using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply, LinearMap.flip_apply,
      LinearMap.mul_apply', LinearMap.mul'_apply, map_smul, LinearMap.smul_apply,
      smul_mul_assoc]
  | add x y hx hy =>
    rw [map_add (LinearMap.rTensor _ _), map_add (LinearMap.mul' _ _), hx, hy,
      map_add (LinearMap.rTensor _ _), map_add (LinearMap.mul' _ _), smul_add]

/-- The nullary insertion coderivation sends the empty word to the single letter `ofLetter m₀`. -/
@[simp]
theorem insertGradedCoderiv_one (G : InternalGrading R M ℤ) (q : ℤ) (m₀ : M) :
    insertGradedCoderiv G q m₀ (1 : TensorWords R M) = ofLetter R M m₀ := by
  simp [insertGradedCoderiv_def]

/-- On a pure tensor word, `insertGradedCoderiv` sums over all `n + 1` insertion positions `p`,
inserting `ofLetter m₀` between the twisted prefix of length `p` and the suffix of length `n - p`.
-/
theorem insertGradedCoderiv_of_tprod (G : InternalGrading R M ℤ) (q : ℤ) (m₀ : M)
    {n : ℕ} (x : Fin n → M) :
    insertGradedCoderiv G q m₀ (of R M n (PiTensorProduct.tprod R x)) =
      ∑ p ∈ Finset.range (n + 1),
        (map (G.koszulTwist q) (subword R x 0 p) * ofLetter R M m₀) * subword R x p (n - p) := by
  rw [insertGradedCoderiv_def, LinearMap.comp_apply, LinearMap.comp_apply, of_tprod_eq_subword,
    deconcatenation_subword, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply, LinearMap.flip_apply,
    LinearMap.mul_apply', LinearMap.mul'_apply, Nat.zero_add]

/-- On homogeneous inputs `x : ℕ → M`, `insertGradedCoderiv G q m₀` inserts `m₀` at each
position `p ∈ Finset.range (n + 1)` using `replaceBlock x p 0 m₀`, scaled by
`(-1)^(q * ∑_{i < p} d i)`. -/
theorem insertGradedCoderiv_of_tprod_of_homogeneous_nat (G : InternalGrading R M ℤ) (q : ℤ)
    (m₀ : M) {n : ℕ} (d : ℕ → ℤ) (x : ℕ → M) (hx : ∀ i < n, x i ∈ G.piece (d i)) :
    insertGradedCoderiv G q m₀ (of R M n (PiTensorProduct.tprod R fun i : Fin n ↦ x i)) =
      ∑ p ∈ Finset.range (n + 1),
        negOnePowCast R (q * ∑ i ∈ Finset.range p, d i) •
          of R M (p + 1 + (n - p))
            (PiTensorProduct.tprod R fun j : Fin (p + 1 + (n - p)) ↦
              replaceBlock x p 0 m₀ j) := by
  rw [insertGradedCoderiv_of_tprod]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have hsub₁ : subword R (fun i : Fin n ↦ x i) 0 p ∈
      gradedPiece G (∑ i ∈ Finset.range p, d i) := by
    rw [subword_eq_of_tprod R _ (by omega), ← Fin.sum_univ_eq_sum_range d p]
    refine mem_gradedPiece_of_tprod G _ (fun j : Fin p ↦ d j.val) fun j ↦ ?_
    dsimp only
    rw [Nat.zero_add]
    exact hx j.val (by omega)
  rw [map_koszulTwist_apply_of_mem G hsub₁ q, smul_mul_assoc, smul_mul_assoc,
    ← negOnePowCast_eq_intCast]
  congr 1
  rw [subword_eq_of_tprod R _ (by omega), subword_eq_of_tprod R _ (by omega),
    ofLetter_eq_of_tprod, of_tprod_mul_of_tprod, of_tprod_mul_of_tprod]
  refine of_tprod_congr R M fun j ↦ ?_
  rcases lt_or_ge j.val (p + 1) with hj | hj
  · rw [fin_append_lt _ _ hj]
    rcases lt_or_ge j.val p with hjp | hjp
    · rw [fin_append_lt _ _ hjp, replaceBlock_of_lt _ _ _ _ hjp]
      exact congrArg x (Nat.zero_add _)
    · have hjp' : j.val = p := by omega
      rw [fin_append_ge _ _ hjp, hjp', replaceBlock_self]
  · rw [fin_append_ge _ _ hj, replaceBlock_of_gt _ _ _ _ (by omega : p < j.val)]
    have hidx : p + (j.val - (p + 1)) = j.val + 0 - 1 := by omega
    dsimp only
    rw [hidx]

/-- On a word of length zero the letter component of `insertGradedCoderiv G q m₀` is
`counit w • m₀`, and on every word of positive length it vanishes. -/
@[simp]
theorem letter_comp_insertGradedCoderiv (G : InternalGrading R M ℤ) (q : ℤ) (m₀ : M) :
    letter R M ∘ₗ insertGradedCoderiv G q m₀ = (counit R M).smulRight m₀ := by
  refine linearMap_ext R M fun n x ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hone : of R M 0 (PiTensorProduct.tprod R x) = (1 : TensorWords R M) := by
      rw [one_eq_of_zero]
      exact of_tprod_congr R M fun i ↦ i.elim0
    rw [LinearMap.comp_apply, LinearMap.smulRight_apply, hone, insertGradedCoderiv_one,
      letter_ofLetter, counit_one, one_smul]
  · rw [LinearMap.comp_apply, LinearMap.smulRight_apply, counit_of_of_ne_zero R M hn.ne',
      zero_smul, insertGradedCoderiv_of_tprod, map_sum]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    rw [map_subword, subword_eq_of_tprod R _ (by omega), subword_eq_of_tprod R _ (by omega),
      ofLetter_eq_of_tprod, of_tprod_mul_of_tprod, of_tprod_mul_of_tprod,
      letter_of_of_ne (by omega)]

/-- The nullary insertion coderivation satisfies the `q`-twisted co-Leibniz identity for any
`m₀ : M`. -/
@[simp]
theorem isGradedCoderivation_insertGradedCoderiv (G : InternalGrading R M ℤ) (q : ℤ)
    (m₀ : M) : IsGradedCoderivation G q (insertGradedCoderiv G q m₀) := by
  let τ := map (G.koszulTwist q)
  let δ := insertGradedCoderiv G q m₀
  let φ : TensorWords R M ⊗[R] TensorWords R M →ₗ[R] TensorWords R M :=
    LinearMap.mul' R (TensorWords R M) ∘ₗ
      LinearMap.rTensor (TensorWords R M)
        ((LinearMap.mul R (TensorWords R M)).flip (ofLetter R M m₀) ∘ₗ τ)
  have hδ : δ = φ ∘ₗ deconcatenation R M := rfl
  have hdecφ (z : TensorWords R M ⊗[R] TensorWords R M) :
      deconcatenation R M (φ z) =
        (LinearMap.rTensor (TensorWords R M) τ ∘ₗ
            LinearMap.lTensor (TensorWords R M) φ ∘ₗ
            (TensorProduct.assoc R (TensorWords R M) (TensorWords R M)
              (TensorWords R M)).toLinearMap ∘ₗ
            LinearMap.rTensor (TensorWords R M) (deconcatenation R M)) z +
          (LinearMap.rTensor (TensorWords R M) φ ∘ₗ
            (TensorProduct.assoc R (TensorWords R M) (TensorWords R M)
              (TensorWords R M)).symm.toLinearMap ∘ₗ
            LinearMap.lTensor (TensorWords R M) (deconcatenation R M)) z := by
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [φ, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.flip_apply,
        LinearMap.mul_apply', LinearMap.mul'_apply]
      rw [deconcatenation_mul_ofLetter_mul]
      have hnat : deconcatenation R M (τ u) =
          TensorProduct.map τ τ (deconcatenation R M u) :=
        LinearMap.congr_fun (deconcatenation_natural (G.koszulTwist q)) u
      congr 1
      · rw [hnat]
        simp only [LinearEquiv.coe_coe]
        induction deconcatenation R M u using TensorProduct.inductionOn with
        | tmul a b =>
          simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply,
            LinearMap.flip_apply, LinearMap.mul_apply', TensorProduct.assoc_tmul,
            LinearMap.rTensor_tmul, LinearMap.mul'_apply]
        | add x y hx hy =>
          simp only [map_add, TensorProduct.add_tmul, hx, hy]
      · simp only [LinearMap.lTensor_tmul, LinearEquiv.coe_coe]
        induction deconcatenation R M v using TensorProduct.inductionOn with
        | tmul c d =>
          simp only [LinearMap.rTensor_tmul, LinearMap.mul_apply', TensorProduct.assoc_symm_tmul,
            LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.mul'_apply]
        | add x y hx hy =>
          simp only [map_add, TensorProduct.tmul_add, hx, hy]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel
  rw [isGradedCoderivation_iff]
  refine LinearMap.ext fun w ↦ ?_
  have hcoassoc := LinearMap.congr_fun (deconcatenation_coassoc R M) w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcoassoc
  change deconcatenation R M (δ w) = _
  rw [hδ, LinearMap.comp_apply, hdecφ]
  change _ + _ =
    LinearMap.rTensor (TensorWords R M) δ (deconcatenation R M w) +
      LinearMap.lTensor (TensorWords R M) δ
        (LinearMap.rTensor (TensorWords R M) τ (deconcatenation R M w))
  have h₁ :
      (LinearMap.rTensor (TensorWords R M) φ ∘ₗ
          (TensorProduct.assoc R (TensorWords R M) (TensorWords R M)
            (TensorWords R M)).symm.toLinearMap ∘ₗ
          LinearMap.lTensor (TensorWords R M) (deconcatenation R M))
        (deconcatenation R M w) =
      LinearMap.rTensor (TensorWords R M) δ (deconcatenation R M w) := by
    have hcomp : LinearMap.rTensor (TensorWords R M) φ ∘ₗ
        LinearMap.rTensor (TensorWords R M) (deconcatenation R M) =
        LinearMap.rTensor (TensorWords R M) δ := by
      rw [← LinearMap.rTensor_comp, hδ]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hcoassoc, LinearEquiv.symm_apply_apply,
      ← LinearMap.comp_apply (LinearMap.rTensor _ φ), hcomp]
  have h₂ :
      (LinearMap.rTensor (TensorWords R M) τ ∘ₗ
          LinearMap.lTensor (TensorWords R M) φ ∘ₗ
          (TensorProduct.assoc R (TensorWords R M) (TensorWords R M)
            (TensorWords R M)).toLinearMap ∘ₗ
          LinearMap.rTensor (TensorWords R M) (deconcatenation R M))
        (deconcatenation R M w) =
      LinearMap.lTensor (TensorWords R M) δ
        (LinearMap.rTensor (TensorWords R M) τ (deconcatenation R M w)) := by
    have hcomp : LinearMap.lTensor (TensorWords R M) φ ∘ₗ
        LinearMap.lTensor (TensorWords R M) (deconcatenation R M) =
        LinearMap.lTensor (TensorWords R M) δ := by
      rw [← LinearMap.lTensor_comp, hδ]
    have hcomm : LinearMap.rTensor (TensorWords R M) τ ∘ₗ
        LinearMap.lTensor (TensorWords R M) δ =
        LinearMap.lTensor (TensorWords R M) δ ∘ₗ
          LinearMap.rTensor (TensorWords R M) τ :=
      TensorProduct.ext' fun x y ↦ by simp
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hcoassoc, ← LinearMap.comp_apply (LinearMap.lTensor _ φ), hcomp,
      ← LinearMap.comp_apply (LinearMap.rTensor _ τ), hcomm, LinearMap.comp_apply]
  rw [h₁, h₂, add_comm]

/-- If `m₀` is homogeneous of degree `r`, then `insertGradedCoderiv G q m₀` is homogeneous of
degree `r` in the total letter degree. -/
theorem isHomogeneous_insertGradedCoderiv (G : InternalGrading R M ℤ) (q : ℤ) {r : ℤ}
    {m₀ : M} (hm₀ : m₀ ∈ G.piece r) :
    LinearMap.IsHomogeneous (insertGradedCoderiv G q m₀) (gradedPiece G) (gradedPiece G) r := by
  have hmul' : LinearMap.IsHomogeneous (LinearMap.mul' R (TensorWords R M))
      ((grading G).tensorProduct (grading G)).piece (grading G).piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro D z hz
    rw [add_zero]
    refine InternalGrading.tensorProduct_piece_le (grading G) (grading G)
      (C := ((grading G).piece D).comap (LinearMap.mul' R (TensorWords R M)))
      (fun p u hu v hv ↦ ?_) hz
    change LinearMap.mul' R (TensorWords R M) (u ⊗ₜ[R] v) ∈ (grading G).piece D
    rw [LinearMap.mul'_apply, grading_piece]
    rw [grading_piece] at hu hv
    simpa only [add_sub_cancel] using mul_mem_gradedPiece G hu hv
  have hmul₀ : LinearMap.IsHomogeneous
      ((LinearMap.mul R (TensorWords R M)).flip (ofLetter R M m₀))
      (grading G).piece (grading G).piece r := by
    rw [LinearMap.isHomogeneous_def]
    intro p u hu
    rw [grading_piece] at hu ⊢
    simpa only [LinearMap.flip_apply, LinearMap.mul_apply'] using
      mul_mem_gradedPiece G hu (ofLetter_mem_gradedPiece G hm₀)
  have htau : LinearMap.IsHomogeneous (map (G.koszulTwist q))
      (grading G).piece (grading G).piece 0 := by
    rw [← koszulTwist_grading]
    exact (grading G).isHomogeneous_koszulTwist q
  rw [insertGradedCoderiv_def, ← grading_piece]
  simpa only [zero_add, add_zero] using
    hmul'.comp (((hmul₀.comp htau).rTensor (grading G)).comp (isHomogeneous_deconcatenation G))

end InsertGradedCoderiv

section GradedCoderiv

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- The graded Taylor expansion of a general linear map `F : TensorWords R M →ₗ[R] M` on the
coaugmented tensor coalgebra: the zero-extended reduced Taylor expansion of
`F ∘ reducedInclusion`, plus the nullary insertion coderivation of `F 1`. -/
noncomputable def gradedCoderiv (G : InternalGrading R M ℤ) (F : TensorWords R M →ₗ[R] M)
    (q : ℤ) : TensorWords R M →ₗ[R] TensorWords R M :=
  extendReduced (ReducedTensorWords.gradedCoderiv G (F ∘ₗ reducedInclusion R M) q) +
    insertGradedCoderiv G q (F 1)

/-- The defining formula of `gradedCoderiv`. -/
theorem gradedCoderiv_def (G : InternalGrading R M ℤ) (F : TensorWords R M →ₗ[R] M)
    (q : ℤ) :
    gradedCoderiv G F q =
      extendReduced (ReducedTensorWords.gradedCoderiv G (F ∘ₗ reducedInclusion R M) q) +
        insertGradedCoderiv G q (F 1) := (rfl)

/-- Every general graded Taylor expansion is a `q`-twisted graded coderivation of `TensorWords`. -/
@[simp]
theorem isGradedCoderivation_gradedCoderiv (G : InternalGrading R M ℤ)
    (F : TensorWords R M →ₗ[R] M) (q : ℤ) :
    IsGradedCoderivation G q (gradedCoderiv G F q) :=
  (gradedCoderivations G q).add_mem
    (isGradedCoderivation_extendReduced
      (ReducedTensorWords.isGradedCoderivation_gradedCoderiv G (F ∘ₗ reducedInclusion R M) q))
    (isGradedCoderivation_insertGradedCoderiv G q (F 1))

/-- Reading off the letter component of `gradedCoderiv G F q` recovers `F`. -/
@[simp]
theorem letter_comp_gradedCoderiv (G : InternalGrading R M ℤ) (F : TensorWords R M →ₗ[R] M)
    (q : ℤ) : letter R M ∘ₗ gradedCoderiv G F q = F := by
  refine LinearMap.ext fun w ↦ ?_
  change letter R M (gradedCoderiv G F q w) = F w
  rw [gradedCoderiv_def, LinearMap.add_apply, map_add, extendReduced_apply,
    ← LinearMap.comp_apply (letter R M) (reducedInclusion R M), letter_comp_reducedInclusion]
  change (ReducedTensorWords.letter R M ∘ₗ
      ReducedTensorWords.gradedCoderiv G (F ∘ₗ reducedInclusion R M) q)
        (reducedProjection R M w) +
      (letter R M ∘ₗ insertGradedCoderiv G q (F 1)) w = F w
  rw [ReducedTensorWords.letter_comp_gradedCoderiv, letter_comp_insertGradedCoderiv,
    LinearMap.comp_apply, LinearMap.smulRight_apply]
  calc
    F (reducedInclusion R M (reducedProjection R M w)) + counit R M w • F 1
      = F (reducedInclusion R M (reducedProjection R M w) +
          algebraMap R (TensorWords R M) (counit R M w)) := by
        rw [map_add, Algebra.algebraMap_eq_smul_one, map_smul]
    _ = F w := by rw [reducedInclusion_reducedProjection_add_algebraMap_counit]

/-- `gradedCoderiv G F q` sends the empty word to the single letter `ofLetter (F 1)`. -/
@[simp]
theorem gradedCoderiv_one (G : InternalGrading R M ℤ) (F : TensorWords R M →ₗ[R] M)
    (q : ℤ) : gradedCoderiv G F q (1 : TensorWords R M) = ofLetter R M (F 1) := by
  simp [gradedCoderiv_def]

/-- On a word of positive length, `gradedCoderiv G F q` is the reduced Taylor expansion of
`F ∘ reducedInclusion` together with the nullary insertion coderivation of `F 1`. -/
theorem gradedCoderiv_of_pos (G : InternalGrading R M ℤ) (F : TensorWords R M →ₗ[R] M)
    (q : ℤ) {n : ℕ} (hn : 0 < n) (z : TensorPower R n M) :
    gradedCoderiv G F q (of R M n z) =
      reducedInclusion R M
          (ReducedTensorWords.gradedCoderiv G (F ∘ₗ reducedInclusion R M) q
            (ReducedTensorWords.of R M ⟨n, hn⟩ z)) +
        insertGradedCoderiv G q (F 1) (of R M n z) := by
  rw [gradedCoderiv_def, LinearMap.add_apply, extendReduced_of _ hn]

/-- When `F 1 = 0`, the general graded Taylor expansion reduces to the zero-extended reduced
Taylor expansion. -/
theorem gradedCoderiv_of_apply_one_eq_zero (G : InternalGrading R M ℤ)
    {F : TensorWords R M →ₗ[R] M} (q : ℤ) (h₁ : F 1 = 0) :
    gradedCoderiv G F q =
      extendReduced (ReducedTensorWords.gradedCoderiv G (F ∘ₗ reducedInclusion R M) q) := by
  rw [gradedCoderiv_def, h₁, insertGradedCoderiv_zero, add_zero]

/-- Any `q`-twisted graded coderivation of `TensorWords` is the graded Taylor expansion of its
letter component. -/
theorem IsGradedCoderivation.eq_gradedCoderiv {G : InternalGrading R M ℤ} {q : ℤ}
    {b : TensorWords R M →ₗ[R] TensorWords R M} (hb : IsGradedCoderivation G q b) :
    b = gradedCoderiv G (letter R M ∘ₗ b) q :=
  hb.eq_of_letter_comp_eq (isGradedCoderivation_gradedCoderiv G (letter R M ∘ₗ b) q)
    (letter_comp_gradedCoderiv G (letter R M ∘ₗ b) q).symm

/-- If `F : TensorWords R M →ₗ[R] M` raises total degree by `r`, then so does
`gradedCoderiv G F q`, independently of `q`. -/
theorem isHomogeneous_gradedCoderiv {G : InternalGrading R M ℤ} {F : TensorWords R M →ₗ[R] M}
    (q r : ℤ) (hF : LinearMap.IsHomogeneous F (gradedPiece G) G.piece r) :
    LinearMap.IsHomogeneous (gradedCoderiv G F q) (gradedPiece G) (gradedPiece G) r := by
  have hFred : LinearMap.IsHomogeneous (F ∘ₗ reducedInclusion R M)
      (ReducedTensorWords.gradedPiece G) G.piece r := by
    rw [LinearMap.isHomogeneous_def]
    intro D w hw
    exact hF.map_mem (mem_gradedPiece_of_reducedInclusion hw)
  have hm₀ : F 1 ∈ G.piece r := by
    simpa only [zero_add] using hF.map_mem (one_mem_gradedPiece G)
  rw [gradedCoderiv_def]
  exact (isHomogeneous_extendReduced
      (ReducedTensorWords.isHomogeneous_gradedCoderiv G _ q r hFred)).add
    (isHomogeneous_insertGradedCoderiv G q hm₀)

/-- A `q`-twisted graded coderivation of `TensorWords` is homogeneous of degree `r` if and only
if its letter component is homogeneous of degree `r`. -/
theorem IsGradedCoderivation.isHomogeneous_iff_letter_comp {G : InternalGrading R M ℤ} {q : ℤ}
    {b : TensorWords R M →ₗ[R] TensorWords R M} (hb : IsGradedCoderivation G q b) (r : ℤ) :
    LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) r ↔
      LinearMap.IsHomogeneous (letter R M ∘ₗ b) (gradedPiece G) G.piece r := by
  constructor
  · intro h
    simpa only [add_zero] using (isHomogeneous_letter G).comp h
  · intro h
    exact hb.eq_gradedCoderiv ▸ isHomogeneous_gradedCoderiv q r h

/-- The Taylor correspondence for general `q`-twisted graded coderivations of `TensorWords`:
the linear equivalence identifying `gradedCoderivations G q` with `TensorWords R M →ₗ[R] M`
via `b ↦ letter R M ∘ₗ b` and `F ↦ gradedCoderiv G F q`. -/
noncomputable def taylorEquiv (G : InternalGrading R M ℤ) (q : ℤ) :
    gradedCoderivations G q ≃ₗ[R] (TensorWords R M →ₗ[R] M) where
  toFun b := letter R M ∘ₗ b.val
  invFun F := ⟨gradedCoderiv G F q,
    (mem_gradedCoderivations G).mpr (isGradedCoderivation_gradedCoderiv G F q)⟩
  left_inv b := by
    have hb : IsGradedCoderivation G q b.val := (mem_gradedCoderivations G).mp b.property
    exact Subtype.ext hb.eq_gradedCoderiv.symm
  right_inv F := letter_comp_gradedCoderiv G F q
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := LinearMap.comp_smul _ _ _

/-- The forward direction of `taylorEquiv` reads off the letter component. -/
@[simp]
theorem taylorEquiv_apply (G : InternalGrading R M ℤ) (q : ℤ)
    (b : gradedCoderivations G q) :
    taylorEquiv G q b = letter R M ∘ₗ b.val := (rfl)

/-- The inverse direction of `taylorEquiv` is the general graded Taylor expansion. -/
@[simp]
theorem taylorEquiv_symm_apply (G : InternalGrading R M ℤ) (q : ℤ)
    (F : TensorWords R M →ₗ[R] M) :
    ((taylorEquiv G q).symm F).val = gradedCoderiv G F q := (rfl)

/-- The general graded Taylor expansion is additive in the Taylor map. -/
@[simp]
theorem gradedCoderiv_add (G : InternalGrading R M ℤ) (F₁ F₂ : TensorWords R M →ₗ[R] M)
    (q : ℤ) :
    gradedCoderiv G (F₁ + F₂) q = gradedCoderiv G F₁ q + gradedCoderiv G F₂ q :=
  congrArg Subtype.val (map_add (taylorEquiv G q).symm F₁ F₂)

/-- The general graded Taylor expansion is `R`-linear in the Taylor map. -/
@[simp]
theorem gradedCoderiv_smul (G : InternalGrading R M ℤ) (c : R) (F : TensorWords R M →ₗ[R] M)
    (q : ℤ) :
    gradedCoderiv G (c • F) q = c • gradedCoderiv G F q :=
  congrArg Subtype.val (map_smul (taylorEquiv G q).symm c F)

/-- The general graded Taylor expansion of the zero Taylor map is zero. -/
@[simp]
theorem gradedCoderiv_zero_left (G : InternalGrading R M ℤ) (q : ℤ) :
    gradedCoderiv G (0 : TensorWords R M →ₗ[R] M) q = 0 :=
  congrArg Subtype.val (map_zero (taylorEquiv G q).symm)

end GradedCoderiv

section OddSquare

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- The square of a `q`-twisted graded coderivation anticommuting with the letterwise Koszul
twist is an untwisted (`0`-twisted) coderivation of `TensorWords`. -/
theorem IsGradedCoderivation.isGradedCoderivation_zero_comp_self {G : InternalGrading R M ℤ}
    {q : ℤ} {b : TensorWords R M →ₗ[R] TensorWords R M} (hb : IsGradedCoderivation G q b)
    (hodd : b ∘ₗ map (G.koszulTwist q) + map (G.koszulTwist q) ∘ₗ b = 0) :
    IsGradedCoderivation G 0 (b ∘ₗ b) := by
  rw [isGradedCoderivation_iff]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, LinearMap.add_apply, G.koszulTwist_zero, map_id,
    LinearMap.rTensor_id, LinearMap.id_apply]
  rw [hb.deconcatenation_apply (b z), hb.deconcatenation_apply z]
  have hτ : map (G.koszulTwist q) ∘ₗ map (G.koszulTwist q) = LinearMap.id := by
    rw [← map_comp, InternalGrading.koszulTwist_comp_self, map_id]
  have h := LinearMap.congr_fun (LinearMap.rTensor_add_lTensor_comp_rTensor_comp_self b
    (map (G.koszulTwist q)) b hτ hodd) (deconcatenation R M z)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add] at h ⊢
  rw [← h]
  abel

/-- A homogeneous endomorphism of `TensorWords` of degree `r` anticommutes with the letterwise
Koszul twist of parameter `q` whenever `(-1) ^ (q * r) = -1`. -/
theorem anticommute_map_koszulTwist_of_isHomogeneous {G : InternalGrading R M ℤ}
    {b : TensorWords R M →ₗ[R] TensorWords R M} {q r : ℤ}
    (hb : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1) :
    b ∘ₗ map (G.koszulTwist q) + map (G.koszulTwist q) ∘ₗ b = 0 := by
  have hb' : LinearMap.IsHomogeneous b (grading G).piece (grading G).piece r := by
    simpa only [grading_piece] using hb
  have h := hb'.koszulTwist_comp_eq_smul q
  rw [koszulTwist_grading, hqr] at h
  calc
    b ∘ₗ map (G.koszulTwist q) + map (G.koszulTwist q) ∘ₗ b
      = (1 : R) • (b ∘ₗ map (G.koszulTwist q)) +
          (-1 : R) • (b ∘ₗ map (G.koszulTwist q)) := by rw [one_smul, h]
    _ = ((1 : R) + (-1 : R)) • (b ∘ₗ map (G.koszulTwist q)) := (add_smul _ _ _).symm
    _ = 0 := by rw [add_neg_cancel, zero_smul]

/-- The square of a homogeneous `q`-twisted graded coderivation of `TensorWords` is an untwisted
(`0`-twisted) coderivation whenever `(-1) ^ (q * r) = -1`. -/
theorem IsGradedCoderivation.isGradedCoderivation_zero_comp_self_of_isHomogeneous
    {G : InternalGrading R M ℤ} {q r : ℤ} {b : TensorWords R M →ₗ[R] TensorWords R M}
    (hb : IsGradedCoderivation G q b)
    (hhom : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1) :
    IsGradedCoderivation G 0 (b ∘ₗ b) :=
  hb.isGradedCoderivation_zero_comp_self (anticommute_map_koszulTwist_of_isHomogeneous hhom hqr)

/-- A homogeneous `q`-twisted graded coderivation of `TensorWords` with `(-1) ^ (q * r) = -1`
squares to zero if and only if its square has vanishing letter component. -/
theorem IsGradedCoderivation.comp_self_eq_zero_iff_letter_comp_eq_zero
    {G : InternalGrading R M ℤ} {q r : ℤ} {b : TensorWords R M →ₗ[R] TensorWords R M}
    (hb : IsGradedCoderivation G q b)
    (hhom : LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) r)
    (hqr : (((q * r).negOnePow : ℤ) : R) = -1) :
    b ∘ₗ b = 0 ↔ letter R M ∘ₗ (b ∘ₗ b) = 0 :=
  (hb.isGradedCoderivation_zero_comp_self_of_isHomogeneous hhom hqr).eq_zero_iff_letter_comp_eq_zero

/-- The degree-one graded Taylor expansion `b = gradedCoderiv G F 1` of a degree-one Taylor map `F`
squares to zero if and only if `F ∘ₗ b = 0`. -/
theorem gradedCoderiv_comp_self_eq_zero_iff {G : InternalGrading R M ℤ}
    {F : TensorWords R M →ₗ[R] M} (hF : LinearMap.IsHomogeneous F (gradedPiece G) G.piece 1) :
    gradedCoderiv G F 1 ∘ₗ gradedCoderiv G F 1 = 0 ↔ F ∘ₗ gradedCoderiv G F 1 = 0 := by
  have hb := isGradedCoderivation_gradedCoderiv G F 1
  have hhom := isHomogeneous_gradedCoderiv 1 1 hF
  have hiff := hb.comp_self_eq_zero_iff_letter_comp_eq_zero hhom (by norm_num)
  rwa [← LinearMap.comp_assoc, letter_comp_gradedCoderiv] at hiff

end OddSquare

end TensorWords

end TauCeti
