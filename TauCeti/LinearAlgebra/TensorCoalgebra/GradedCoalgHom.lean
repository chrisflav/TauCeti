/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Graded coalgebra morphisms of reduced tensor coalgebras

Let `M` and `N` carry internal integer gradings `G` and `H`, and give their reduced tensor
coalgebras `Tᶜ(M)` and `Tᶜ(N)` the total letter degree.  This file combines the ungraded
correspondence between coalgebra morphisms `Tᶜ(M) ⟶ Tᶜ(N)` and their Taylor components
(`TauCeti.ReducedTensorWords.coalgHomEquivTaylor`) with the grading, and with graded
coderivations.

First, the Taylor expansion `coalgHom f` of a degree-zero family of components `f` is itself of
degree zero: each word `f(B₁) ⋯ f(B_k)` produced from a cut of a homogeneous word into blocks has
the total degree of the word.

Second, for linear maps `F F' : Tᶜ(M) ⟶ Tᶜ(N)`, a *coderivation along* `F` and `F'` with twist
parameter `q` is a linear map `D : Tᶜ(M) ⟶ Tᶜ(N)` satisfying

`Δ ∘ D = (D ⊗ F') ∘ Δ + (F ⊗ D) ∘ (τ ⊗ 1) ∘ Δ`,

with `τ` the letterwise Koszul twist of `Tᶜ(M)` of parameter `q`.  Such a map is determined by its
letter component, by induction along the conilpotence filtration, whatever `F` and `F'` are.
Coderivations along a pair of maps are stable under composition with coalgebra morphisms on
either side.  Three instances drive the applications: if `F` and `F'` are coalgebra morphisms then
`F - F'` is an untwisted coderivation along `F` and `F'`; if `F` has degree zero and `b_M`, `b_N`
are graded coderivations then `b_N ∘ F` and `F ∘ b_M` are coderivations along `F` and `F`; and if
`D` is an odd coderivation along `F` and `F'`, and both maps intertwine odd coderivations `b_M` and
`b_N`, then `b_N ∘ D + D ∘ b_M` is an untwisted coderivation along `F` and `F'`.  More generally,
if `D` has degree `p` and twist parameter `p`, and `b_M`, `b_N` have degree and twist parameter
one, then the graded commutator `b_N ∘ D - (-1)^p D ∘ b_M` is a coderivation along `F` and `F'`
with twist parameter `p + 1`; this is the differential of the complex of coderivations along `F`
and `F'`.

Hence a degree-zero coalgebra morphism `F` intertwines two `q`-twisted graded coderivations
`b_M` of `Tᶜ(M)` and `b_N` of `Tᶜ(N)` as soon as it does so after projection onto single letters:
`b_N ∘ F = F ∘ b_M` if and only if `π ∘ b_N ∘ F = π ∘ F ∘ b_M`, where `π : Tᶜ(N) ⟶ N` is the
letter projection.  Applied to bar constructions, this is the statement that an `A∞` morphism is
determined by, and may be constructed from, Taylor components satisfying the suspended component
equation.  In the same way, the homotopy equation `F - F' = b_N ∘ D + D ∘ b_M` for an odd
coderivation `D` along coalgebra morphisms holds as soon as it holds on letter components; this
is the component equation of a homotopy between `A∞` morphisms.

## Main definitions

* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong`: the co-Leibniz rule of a coderivation
  along a pair of maps.
* `TauCeti.ReducedTensorWords.gradedCoderivAlong`: the coderivation along a pair of coalgebra
  morphisms with prescribed Taylor components.
* `TauCeti.ReducedTensorWords.gradedCoderivAlongEquivTaylor`: coderivations along a pair of
  coalgebra morphisms are in bijection with their Taylor components.

## Main results

* `TauCeti.ReducedTensorWords.isHomogeneous_coalgHom`: the Taylor expansion of degree-zero
  components has degree zero.
* `TauCeti.ReducedTensorWords.isHomogeneous_filtrationLimit`: the limit of a filtration-stabilising
  sequence of homogeneous linear maps of a fixed degree has that degree.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.apply_eq_of_mem_filtration` and
  `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.eq_of_letter_comp_eq`: a coderivation
  along a pair of maps is determined on each filtration step by its letter component and the two
  maps on that step, hence globally by its letter component.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.apply_eq_ofLetter_of_mem_filtration_succ`:
  a coderivation along a pair of maps whose letter component vanishes up to length `n` sends words
  of length at most `n + 1` to single letters.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong`,
  `TauCeti.ReducedTensorWords.letter_comp_gradedCoderivAlong` and
  `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivAlong`: `gradedCoderivAlong` is a
  coderivation along coalgebra morphisms with the prescribed Taylor components and degree.
* `TauCeti.ReducedTensorWords.IsCoalgHom.isGradedCoderivationAlong_sub`: the difference of two
  coalgebra morphisms is a coderivation along them.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.comp_sub_negOnePow_smul_comp`: the graded
  commutator of a coderivation along a pair of maps with coderivations intertwined by them.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.comp_add_comp`: its special case for an
  odd coderivation along a pair of maps and odd coderivations intertwined by them.
* `TauCeti.ReducedTensorWords.IsCoalgHom.comp_eq_comp_iff_letter_comp_eq`: a degree-zero coalgebra
  morphism intertwines two graded coderivations exactly when it does so on letter components.
* `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.sub_eq_comp_add_comp_iff`: the homotopy
  equation holds exactly when it holds on letter components, and
  `TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.sub_comp_add_comp_eq_ofLetter`: when the
  intertwining and homotopy equations hold up to length `n`, the homotopy defect on length `n + 1`
  lies in single letters.
* `TauCeti.ReducedTensorWords.IsCoalgHom.isHomogeneous_linearEquiv_symm`: the inverse of a
  degree-zero coalgebra automorphism is homogeneous of degree zero.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uL uM uN uP

namespace TauCeti

namespace ReducedTensorWords

section FiltrationLimit

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- If a sequence of linear maps out of reduced tensor words stabilises along the conilpotence
filtration and every map in the sequence is homogeneous of degree `q`, then its filtration limit is
homogeneous of degree `q`. -/
theorem isHomogeneous_filtrationLimit {ι σM σN : Type*} [AddMonoid ι]
    [SetLike σM (ReducedTensorWords R M)] [SetLike σN N] {𝒜 : ι → σM} {ℬ : ι → σN} {q : ι}
    {f : ℕ → ReducedTensorWords R M →ₗ[R] N}
    (hf : ∀ n, ∀ z ∈ filtration R M n, f (n + 1) z = f n z)
    (hhom : ∀ n, LinearMap.IsHomogeneous (f n) 𝒜 ℬ q) :
    LinearMap.IsHomogeneous (filtrationLimit R f) 𝒜 ℬ q := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  rw [filtrationLimit_apply_of_mem_filtration hf hn]
  exact (hhom n).map_mem hz

end FiltrationLimit

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}

/-- The Taylor expansion of components of degree zero has degree zero: every word
`f(B₁) ⋯ f(B_k)` it produces from a homogeneous word has the total degree of that word. -/
theorem isHomogeneous_coalgHom {f : ReducedTensorWords R M →ₗ[R] N}
    (hf : LinearMap.IsHomogeneous f (gradedPiece G) H.piece 0) :
    LinearMap.IsHomogeneous (coalgHom R f) (gradedPiece G) (gradedPiece H) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  rw [add_zero]
  refine gradedPiece_induction (motive := fun w ↦ coalgHom R f w ∈ gradedPiece H D) hz ?_ ?_ ?_
  · intro n hn 𝒟 x hx hD
    -- Extend the degrees to absolute positions, and induct on the length of a block.
    set g : ℕ → ℤ := fun k ↦ if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hg
    have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
    have key : ∀ b a : ℕ, a + b ≤ n →
        coalgHom R f (subword R x a b) ∈ gradedPiece H (∑ j ∈ Finset.range b, g (a + j)) := by
      intro b
      induction b using Nat.strong_induction_on with
      | _ b ih =>
        intro a hab
        rw [coalgHom_subword]
        refine add_mem ?_ (Submodule.sum_mem _ fun d hd ↦ ?_)
        · refine ofLetter_mem_gradedPiece H ?_
          simpa only [add_zero] using hf.map_mem (subword_mem_gradedPiece x g hxg a b)
        · rw [Finset.mem_range] at hd
          rcases Nat.eq_zero_or_pos d with rfl | hd0
          · rw [subword_length_zero, map_zero, LinearMap.map_zero₂]
            exact zero_mem _
          · have hsum : ∑ j ∈ Finset.range b, g (a + j) =
                (∑ j ∈ Finset.range d, g (a + j)) +
                  ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
              rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
              simp only [Nat.add_assoc]
            rw [hsum]
            refine prepend_mem_gradedPiece ?_ (ih (b - d) (by omega) (a + d) (by omega))
            simpa only [add_zero] using
              hf.map_mem (subword_mem_gradedPiece x g hxg a d)
    have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D := by
      rw [← hD, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
    rw [of_tprod_eq_subword R hn, ← hsum]
    exact key n 0 (by omega)
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-! ### Coderivations along coalgebra morphisms -/

/-- A *graded coderivation along* `F` and `F'` with twist parameter `q`, also called an
`(F, F')`-coderivation: a linear map `D : Tᶜ(M) ⟶ Tᶜ(N)` satisfying the co-Leibniz rule

`Δ ∘ D = (D ⊗ F') ∘ Δ + (F ⊗ D) ∘ (τ ⊗ 1) ∘ Δ`,

in which `τ = ReducedTensorWords.map (InternalGrading.koszulTwist G q)` is the letterwise Koszul
twist of the source and acts on the left half of every cut.  On a word `z` of homogeneous letters,
summing over the cuts `w₁ ⊗ w₂` of `z`,

`Δ (D z) = ∑ (D w₁ ⊗ F' w₂ + (-1)^(q * |w₁|) • (F w₁ ⊗ D w₂))`.

For `F = F' = id` this is `IsGradedCoderivation G q`.  Homogeneity of `D` is not part of the
condition. -/
def IsGradedCoderivationAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) : Prop :=
  deconcatenation R N ∘ₗ D =
    TensorProduct.map D F' ∘ₗ deconcatenation R M +
      TensorProduct.map F D ∘ₗ
        LinearMap.rTensor (ReducedTensorWords R M)
          (ReducedTensorWords.map (R := R) (G.koszulTwist q)) ∘ₗ deconcatenation R M

/-- The co-Leibniz identity of a coderivation along a pair of maps, as a reusable `Iff`: this
exposes the body of the predicate to consumers in other modules. -/
theorem isGradedCoderivationAlong_iff {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} :
    IsGradedCoderivationAlong G q F F' D ↔
      deconcatenation R N ∘ₗ D =
        TensorProduct.map D F' ∘ₗ deconcatenation R M +
          TensorProduct.map F D ∘ₗ
            LinearMap.rTensor (ReducedTensorWords R M)
              (ReducedTensorWords.map (R := R) (G.koszulTwist q)) ∘ₗ deconcatenation R M :=
  Iff.rfl

/-- The co-Leibniz identity of a coderivation along a pair of maps, applied to an element. -/
theorem IsGradedCoderivationAlong.deconcatenation_apply {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (z : ReducedTensorWords R M) :
    deconcatenation R N (D z) =
      TensorProduct.map D F' (deconcatenation R M z) +
        TensorProduct.map F D
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist q)) (deconcatenation R M z)) :=
  LinearMap.congr_fun hD z

/-- The coderivations along the identity on both sides are the graded coderivations. -/
theorem isGradedCoderivationAlong_id_id_iff {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} :
    IsGradedCoderivationAlong G q LinearMap.id LinearMap.id b ↔ IsGradedCoderivation G q b := by
  rw [isGradedCoderivationAlong_iff, isGradedCoderivation_iff, ← LinearMap.rTensor_def,
    ← LinearMap.lTensor_def, LinearMap.comp_assoc]

/-- Two coderivations along pairs of maps that agree on `filtration R M n`, and whose letter
components agree on `filtration R M n`, agree on `filtration R M n`: deconcatenation sends words of
length at most `k + 1` into `filtration k ⊗ filtration k`, and the letterwise Koszul twist preserves
`filtration k`. -/
theorem IsGradedCoderivationAlong.apply_eq_of_mem_filtration {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ z ∈ filtration R M n, F₁ z = F₂ z)
    (hF' : ∀ z ∈ filtration R M n, F₁' z = F₂' z)
    (hl : ∀ z ∈ filtration R M n, letter R N (D₁ z) = letter R N (D₂ z))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D₁ z = D₂ z := by
  induction n generalizing z with
  | zero =>
      rw [filtration_zero] at hz
      rw [(Submodule.mem_bot R).1 hz, map_zero, map_zero]
  | succ n ih =>
      have hmono := filtration_monotone R M n.le_succ
      have ihD : ∀ u ∈ filtration R M n, D₁ u = D₂ u := fun u hu ↦
        ih (fun w hw ↦ hF w (hmono hw)) (fun w hw ↦ hF' w (hmono hw))
          (fun w hw ↦ hl w (hmono hw)) hu
      refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (hl z hz)
      obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
      rw [h₁.deconcatenation_apply, h₂.deconcatenation_apply, ← hw]
      clear hw
      induction w using TensorProduct.inductionOn with
      | tmul u v =>
          simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
            LinearMap.rTensor_tmul]
          rw [ihD _ u.2, ihD _ v.2, hF' _ (hmono v.2),
            hF _ (hmono ((isCoalgHom_map _).mem_filtration u.2))]
      | add u v hu hv =>
          simp only [map_add] at hu hv ⊢
          rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- A coderivation along a pair of maps is determined by its letter component: two
coderivations along the same pair of maps whose letter components agree are equal.  This is an
induction along the conilpotence filtration of the source, and it holds for arbitrary `F`
and `F'`. -/
theorem IsGradedCoderivationAlong.eq_of_letter_comp_eq {q : ℤ}
    {F F' D₁ D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F F' D₁) (h₂ : IsGradedCoderivationAlong G q F F' D₂)
    (hl : letter R N ∘ₗ D₁ = letter R N ∘ₗ D₂) : D₁ = D₂ := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  exact h₁.apply_eq_of_mem_filtration h₂ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun w _ ↦ LinearMap.congr_fun hl w) hn

/-- The zero map is a coderivation along every pair of maps. -/
theorem isGradedCoderivationAlong_zero (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    IsGradedCoderivationAlong G q F F' 0 := by
  rw [isGradedCoderivationAlong_iff, TensorProduct.map_zero_left, TensorProduct.map_zero_right,
    LinearMap.comp_zero, LinearMap.zero_comp, LinearMap.zero_comp, add_zero]

/-- A coderivation along a pair of maps whose letter component vanishes on `filtration R M n`
vanishes on `filtration R M n`. -/
theorem IsGradedCoderivationAlong.apply_eq_zero_of_mem_filtration {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    (hl : ∀ z ∈ filtration R M n, letter R N (D z) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) : D z = 0 :=
  hD.apply_eq_of_mem_filtration (isGradedCoderivationAlong_zero G q F F')
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun w hw ↦ by rw [hl w hw, LinearMap.zero_apply, map_zero]) hz

/-- A coderivation along a pair of maps whose letter component vanishes on `filtration R M n` sends
every word in `filtration R M (n + 1)` into single letters: every proper cut of such a word has both
halves in `filtration R M n`, where the coderivation already vanishes. -/
theorem IsGradedCoderivationAlong.apply_eq_ofLetter_of_mem_filtration_succ {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) {n : ℕ}
    (hl : ∀ z ∈ filtration R M n, letter R N (D z) = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D z = ofLetter R N (letter R N (D z)) := by
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  rw [deconcatenation_ofLetter, hD.deconcatenation_apply]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.rTensor_tmul]
      rw [hD.apply_eq_zero_of_mem_filtration hl u.2, hD.apply_eq_zero_of_mem_filtration hl v.2,
        TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [add_add_add_comm, hu, hv, add_zero]

/-- The co-Leibniz rule of a coderivation along a pair of maps only depends on the parity of the
twist parameter: negating it changes nothing. -/
@[simp]
theorem isGradedCoderivationAlong_neg_iff {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} :
    IsGradedCoderivationAlong G (-q) F F' D ↔ IsGradedCoderivationAlong G q F F' D := by
  rw [isGradedCoderivationAlong_iff, isGradedCoderivationAlong_iff,
    InternalGrading.koszulTwist_neg]

/-! ### Taylor expansion of coderivations along coalgebra morphisms -/

/-- The length-`n` component of the Taylor expansion `gradedCoderivAlong G q F F' h`: either the
whole word is collapsed to `h(x₁ ⋯ xₙ)`, or a nonempty first block of `d` letters is split off and
either collapsed by `h` in front of `F'` on the rest or mapped by the twisted Taylor component of
`F` in front of the recursive expansion of the rest. -/
private noncomputable def gradedCoderivAlongComponent (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    (n : ℕ) → TensorPower R n M →ₗ[R] ReducedTensorWords R N
  | n =>
    (if hn : 0 < n then ofLetter R N ∘ₗ h ∘ₗ of R M ⟨n, hn⟩ else 0) +
      ∑ d : Fin n, if hd : 0 < d.1 then
        (TensorProduct.lift ((prepend R N).compl₁₂ (h ∘ₗ of R M ⟨d.1, hd⟩)
            (F' ∘ₗ of R M ⟨n - d.1, by have := d.isLt; omega⟩)) +
          TensorProduct.lift ((prepend R N).compl₁₂
            ((letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)) ∘ₗ
              of R M ⟨d.1, hd⟩)
            (gradedCoderivAlongComponent G q F F' h (n - d.1)))) ∘ₗ
          TensorPower.splitAt R M n d.1 d.2.le
        else 0
termination_by n => n
decreasing_by have := d.isLt; omega

/-- The Taylor expansion of a linear map `h : Tᶜ(M) ⟶ N` as a `q`-twisted coderivation along
coalgebra morphisms `F` and `F'`.  On a word, it sums `f(τ B₁) ⋯ f(τ B_{i-1}) h(B_i) f'(B_{i+1}) ⋯`
over all cuts into consecutive nonempty blocks and all choices of active block `B_i`, where `f` and
`f'` are the Taylor components of `F` and `F'` and `τ` is the letterwise Koszul twist of parameter
`q`. -/
noncomputable def gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦ gradedCoderivAlongComponent G q F F' h n.1

/-- The recursive evaluation rule of `gradedCoderivAlong` on a pure tensor word. -/
private theorem gradedCoderivAlong_of_tprod (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    gradedCoderivAlong G q F F' h (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ofLetter R N (h (subword R x 0 n)) +
        ∑ d ∈ Finset.range n,
          (prepend R N (h (subword R x 0 d)) (F' (subword R x d (n - d))) +
            prepend R N
              ((letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
                (subword R x 0 d))
              (gradedCoderivAlong G q F F' h (subword R x d (n - d)))) := by
  rw [gradedCoderivAlong, toModule_of, gradedCoderivAlongComponent, dite_eq_left hn,
    ← of_tprod_eq_subword R hn x]
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
  congr 1
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rcases Nat.eq_zero_or_pos d.1 with hd | hd
  · rw [dite_eq_right (by omega), hd]
    simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero]
  · have _ := d.isLt
    have hleft : of R M ⟨d.1, hd⟩
        (PiTensorProduct.tprod R fun i : Fin d.1 ↦ x (Fin.castLE d.2.le i)) =
        subword R x 0 d.1 := by
      rw [subword_eq_of_tprod R x hd (by omega)]
      exact of_tprod_congr R M hd rfl fun j ↦ congrArg x (Fin.ext (by simp))
    rw [dite_eq_left hd, subword_eq_of_tprod R x (a := d.1) (b := n - d.1) (by omega) (by omega),
      toModule_of]
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      TensorPower.splitAt_tprod, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    rw [hleft]

/-- The recursive evaluation rule of `gradedCoderivAlong` on a block of a tensor word. -/
theorem gradedCoderivAlong_subword (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) {n : ℕ} (x : Fin n → M) (a b : ℕ) :
    gradedCoderivAlong G q F F' h (subword R x a b) =
      ofLetter R N (h (subword R x a b)) +
        ∑ d ∈ Finset.range b,
          (prepend R N (h (subword R x a d)) (F' (subword R x (a + d) (b - d))) +
            prepend R N
              ((letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
                (subword R x a d))
              (gradedCoderivAlong G q F F' h (subword R x (a + d) (b - d)))) := by
  by_cases hb_ab : 0 < b ∧ a + b ≤ n
  · obtain ⟨hb, hab⟩ := hb_ab
    have hy : ∀ c d : ℕ, c + d ≤ b → subword R (fun j : Fin b ↦ x ⟨a + j.1, by omega⟩) c d =
        subword R x (a + c) d := fun c d hcd ↦
      subword_congr R _ x hcd (by omega) fun j _ ↦ congrArg x (Fin.ext (by simp only; omega))
    have hx := congrArg (gradedCoderivAlong G q F F' h) (subword_eq_of_tprod R x hb hab)
    rw [hx, gradedCoderivAlong_of_tprod G q F F' h hb, hy 0 b (by omega), Nat.add_zero]
    congr 1
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rw [hy 0 d (by omega), hy d (b - d) (by omega), Nat.add_zero]
  · have hzero : subword R x a b = 0 := by
      rcases not_and_or.1 hb_ab with hb | hab
      · rw [show b = 0 by omega, subword_length_zero]
      · exact subword_eq_zero_of_lt_add R x (by omega)
    rw [hzero, map_zero, map_zero, map_zero, zero_add]
    refine (Finset.sum_eq_zero fun d hd ↦ ?_).symm
    rw [Finset.mem_range] at hd
    rcases not_and_or.1 hb_ab with hb | hab
    · omega
    · rw [subword_eq_zero_of_lt_add R x (a := a + d) (by omega)]
      simp only [map_zero, add_zero]

/-- The Taylor expansion `gradedCoderivAlong` recovers the prescribed Taylor components. -/
@[simp]
theorem letter_comp_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) :
    letter R N ∘ₗ gradedCoderivAlong G q F F' h = h := by
  refine linearMap_ext R M fun n x ↦ ?_
  rw [LinearMap.comp_apply, of_tprod_eq_subword R n.2, gradedCoderivAlong_subword, map_add, map_sum,
    letter_ofLetter]
  simp only [map_add, letter_prepend, add_zero, Finset.sum_const_zero]

/-- On a single letter, `gradedCoderivAlong` is the single letter given by the arity-one Taylor
component. -/
@[simp]
theorem gradedCoderivAlong_ofLetter (G : InternalGrading R M ℤ) (q : ℤ)
    (F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (h : ReducedTensorWords R M →ₗ[R] N) (a : M) :
    gradedCoderivAlong G q F F' h (ofLetter R M a) = ofLetter R N (h (ofLetter R M a)) := by
  have h1 := gradedCoderivAlong_subword G q F F' h (fun _ : Fin 1 ↦ a) 0 1
  rw [subword_one R M _ Nat.one_pos, Finset.sum_range_one] at h1
  simpa only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero] using h1

/-- Reindex a triangular double sum of pure tensors by the total prefix length `e = d + c`. -/
private theorem sum_tmul_add_sum_range_sub {P Q : Type*} [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q] (b : ℕ) (u₀ : ℕ → P) (u : ℕ → ℕ → P) (v : ℕ → Q)
    (hu0 : ∀ d, u d 0 = 0) :
    (∑ d ∈ Finset.range b,
        (u₀ d ⊗ₜ[R] v d + ∑ c ∈ Finset.range (b - d), u d c ⊗ₜ[R] v (d + c))) =
      ∑ e ∈ Finset.range b, (u₀ e + ∑ d ∈ Finset.range e, u d (e - d)) ⊗ₜ[R] v e := by
  rw [Finset.sum_add_distrib, ← Finset.sum_range_diag_flip, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Finset.sum_range_succ, Nat.sub_self, hu0, TensorProduct.zero_tmul, add_zero,
    TensorProduct.add_tmul, TensorProduct.sum_tmul]
  congr 1
  exact Finset.sum_congr rfl fun d hd ↦ by
    rw [Finset.mem_range] at hd
    rw [Nat.add_sub_of_le hd.le]

/-- Deconcatenation of one recursive summand of `gradedCoderivAlong_subword`. -/
private theorem deconcatenation_gradedCoderivAlong_term (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N)
    {n : ℕ} (x : Fin n → M) {b a d : ℕ} (hd : d < b)
    (ih : 0 < d →
      deconcatenation R N (gradedCoderivAlong G q F F' h (subword R x (a + d) (b - d))) =
        TensorProduct.map (gradedCoderivAlong G q F F' h) F'
            (deconcatenation R M (subword R x (a + d) (b - d))) +
          TensorProduct.map (F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
            (gradedCoderivAlong G q F F' h)
            (deconcatenation R M (subword R x (a + d) (b - d)))) :
    let D := gradedCoderivAlong G q F F' h
    let Fτ := F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)
    deconcatenation R N (prepend R N (h (subword R x a d)) (F' (subword R x (a + d) (b - d))) +
        prepend R N ((letter R N ∘ₗ Fτ) (subword R x a d)) (D (subword R x (a + d) (b - d)))) =
      (ofLetter R N (h (subword R x a d)) ⊗ₜ[R] F' (subword R x (a + d) (b - d)) +
        ∑ c ∈ Finset.range (b - d),
          (prepend R N (h (subword R x a d)) (F' (subword R x (a + d) c)) +
            prepend R N ((letter R N ∘ₗ Fτ) (subword R x a d)) (D (subword R x (a + d) c))) ⊗ₜ[R]
            F' (subword R x (a + (d + c)) (b - (d + c)))) +
      (ofLetter R N ((letter R N ∘ₗ Fτ) (subword R x a d)) ⊗ₜ[R]
          D (subword R x (a + d) (b - d)) +
        ∑ c ∈ Finset.range (b - d),
          prepend R N ((letter R N ∘ₗ Fτ) (subword R x a d)) (Fτ (subword R x (a + d) c)) ⊗ₜ[R]
            D (subword R x (a + (d + c)) (b - (d + c)))) := by
  intro D Fτ
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero,
      TensorProduct.zero_tmul, Finset.sum_const_zero]
  · rw [map_add, deconcatenation_prepend, deconcatenation_prepend, hF'.deconcatenation_apply,
      ih hd0, map_add, map_deconcatenation_subword, map_deconcatenation_subword,
      map_deconcatenation_subword, map_sum, map_sum, map_sum, ← Finset.sum_add_distrib]
    simp only [LinearMap.rTensor_tmul, TensorProduct.add_tmul, Finset.sum_add_distrib,
      Nat.add_assoc, Nat.sub_sub]
    ac_rfl

/-- Deconcatenation of `gradedCoderivAlong` on a block of a tensor word, when `F` and `F'` are
coalgebra morphisms. -/
private theorem deconcatenation_gradedCoderivAlong_subword (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N)
    {n : ℕ} (x : Fin n → M) (b a : ℕ) :
    deconcatenation R N (gradedCoderivAlong G q F F' h (subword R x a b)) =
      TensorProduct.map (gradedCoderivAlong G q F F' h) F'
          (deconcatenation R M (subword R x a b)) +
        TensorProduct.map (F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
          (gradedCoderivAlong G q F F' h) (deconcatenation R M (subword R x a b)) := by
  set D := gradedCoderivAlong G q F F' h
  set Fτ := F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q)
  have hFτ : IsCoalgHom R Fτ := hF.comp (isCoalgHom_map _)
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rw [gradedCoderivAlong_subword, map_add, deconcatenation_ofLetter, zero_add, map_sum,
      map_deconcatenation_subword, map_deconcatenation_subword,
      Finset.sum_congr rfl fun d hd ↦ deconcatenation_gradedCoderivAlong_term G q hF' h x
        (Finset.mem_range.1 hd) (fun hd0 ↦ ih (b - d) (by have := Finset.mem_range.1 hd; omega)
          (a + d)),
      Finset.sum_add_distrib,
      sum_tmul_add_sum_range_sub b (fun d ↦ ofLetter R N (h (subword R x a d)))
        (fun d c ↦ prepend R N (h (subword R x a d)) (F' (subword R x (a + d) c)) +
          prepend R N ((letter R N ∘ₗ Fτ) (subword R x a d)) (D (subword R x (a + d) c)))
        (fun e ↦ F' (subword R x (a + e) (b - e)))
        (fun _ ↦ by simp only [subword_length_zero, map_zero, add_zero]),
      sum_tmul_add_sum_range_sub b (fun d ↦ ofLetter R N ((letter R N ∘ₗ Fτ) (subword R x a d)))
        (fun d c ↦ prepend R N ((letter R N ∘ₗ Fτ) (subword R x a d)) (Fτ (subword R x (a + d) c)))
        (fun e ↦ D (subword R x (a + e) (b - e)))
        (fun _ ↦ by simp only [subword_length_zero, map_zero])]
    congr 1
    · exact Finset.sum_congr rfl fun e _ ↦ by rw [← gradedCoderivAlong_subword]
    · refine Finset.sum_congr rfl fun e _ ↦ ?_
      have heq : Fτ (subword R x a e) = ofLetter R N ((letter R N ∘ₗ Fτ) (subword R x a e)) +
          ∑ d ∈ Finset.range e,
            prepend R N ((letter R N ∘ₗ Fτ) (subword R x a d))
              (Fτ (subword R x (a + d) (e - d))) := by
        nth_rw 1 [hFτ.eq_coalgHom]; rw [coalgHom_subword, ← hFτ.eq_coalgHom]
      rw [← heq]

/-- When `F` and `F'` are coalgebra morphisms, `gradedCoderivAlong G q F F' h` is a `q`-twisted
coderivation along `F` and `F'`. -/
theorem isGradedCoderivationAlong_gradedCoderivAlong (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N) :
    IsGradedCoderivationAlong G q F F' (gradedCoderivAlong G q F F' h) := by
  rw [isGradedCoderivationAlong_iff, LinearMap.rTensor_def, ← LinearMap.comp_assoc,
    ← TensorProduct.map_comp, LinearMap.comp_id]
  refine linearMap_ext R M fun n x ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, of_tprod_eq_subword R n.2]
  exact deconcatenation_gradedCoderivAlong_subword G q hF hF' h x n.1 0

/-- A coderivation along coalgebra morphisms `F` and `F'` is the Taylor expansion of its own Taylor
components. -/
theorem IsGradedCoderivationAlong.eq_gradedCoderivAlong {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') :
    D = gradedCoderivAlong G q F F' (letter R N ∘ₗ D) :=
  hD.eq_of_letter_comp_eq (isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' _)
    (letter_comp_gradedCoderivAlong G q F F' _).symm

/-- Coderivations along coalgebra morphisms `F` and `F'` are in bijection with their Taylor
components, the linear maps from tensor words to letters. -/
noncomputable def gradedCoderivAlongEquivTaylor (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') :
    {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N //
      IsGradedCoderivationAlong G q F F' D} ≃
      (ReducedTensorWords R M →ₗ[R] N) where
  toFun D := letter R N ∘ₗ D.1
  invFun h := ⟨gradedCoderivAlong G q F F' h,
    isGradedCoderivationAlong_gradedCoderivAlong G q hF hF' h⟩
  left_inv D := Subtype.ext (D.2.eq_gradedCoderivAlong hF hF').symm
  right_inv h := letter_comp_gradedCoderivAlong G q F F' h

/-- Applying `gradedCoderivAlongEquivTaylor` projects onto single letters. -/
@[simp]
theorem gradedCoderivAlongEquivTaylor_apply (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F')
    (D : {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N //
      IsGradedCoderivationAlong G q F F' D}) :
    gradedCoderivAlongEquivTaylor G q hF hF' D = letter R N ∘ₗ D.1 :=
  (rfl)

/-- The inverse of `gradedCoderivAlongEquivTaylor` is `gradedCoderivAlong`. -/
@[simp]
theorem gradedCoderivAlongEquivTaylor_symm_apply (G : InternalGrading R M ℤ) (q : ℤ)
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hF' : IsCoalgHom R F') (h : ReducedTensorWords R M →ₗ[R] N) :
    ((gradedCoderivAlongEquivTaylor G q hF hF').symm h).1 = gradedCoderivAlong G q F F' h :=
  (rfl)

/-- If `F` and `F'` have degree zero and `h` has degree `p`, then `gradedCoderivAlong G q F F' h`
has degree `p`, independently of the twist parameter `q`. -/
theorem isHomogeneous_gradedCoderivAlong {q p : ℤ}
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {h : ReducedTensorWords R M →ₗ[R] N}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF' : LinearMap.IsHomogeneous F' (gradedPiece G) (gradedPiece H) 0)
    (hh : LinearMap.IsHomogeneous h (gradedPiece G) H.piece p) :
    LinearMap.IsHomogeneous (gradedCoderivAlong G q F F' h) (gradedPiece G) (gradedPiece H) p := by
  have hτ : LinearMap.IsHomogeneous (ReducedTensorWords.map (R := R) (G.koszulTwist q))
      (gradedPiece G) (gradedPiece G) 0 :=
    isHomogeneous_map G G (LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
      simpa only [add_zero] using G.koszulTwist_mem_piece ha q)
  have hfτ : LinearMap.IsHomogeneous
      (letter R N ∘ₗ F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist q))
      (gradedPiece G) H.piece 0 := by
    simpa only [add_zero] using (isHomogeneous_letter H).comp (hF.comp hτ)
  refine LinearMap.isHomogeneous_def.2 fun D z hz ↦ gradedPiece_induction
    (motive := fun w ↦ gradedCoderivAlong G q F F' h w ∈ gradedPiece H (D + p)) hz ?_
    (fun _ _ _ _ hu hv ↦ by rw [map_add]; exact add_mem hu hv)
    (fun c _ _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hu)
  intro n hn 𝒟 x hx hD
  set g : ℕ → ℤ := fun k ↦ if hk : k < n then 𝒟 ⟨k, hk⟩ else 0 with hg
  have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
  have key : ∀ b a : ℕ, a + b ≤ n → gradedCoderivAlong G q F F' h (subword R x a b) ∈
      gradedPiece H ((∑ j ∈ Finset.range b, g (a + j)) + p) := fun b ↦ by
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro a hab
      rw [gradedCoderivAlong_subword]
      refine add_mem (ofLetter_mem_gradedPiece H (hh.map_mem (subword_mem_gradedPiece x g hxg a b)))
        (Submodule.sum_mem _ fun d hd ↦ ?_)
      rw [Finset.mem_range] at hd
      rcases Nat.eq_zero_or_pos d with rfl | _
      · simp only [subword_length_zero, map_zero, LinearMap.zero_apply, add_zero, zero_mem]
      · have hsplit : ∑ j ∈ Finset.range b, g (a + j) = (∑ j ∈ Finset.range d, g (a + j)) +
            ∑ j ∈ Finset.range (b - d), g (a + d + j) := by
          rw [← Nat.add_sub_cancel' hd.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
          simp only [Nat.add_assoc]
        rw [hsplit]
        exact add_mem
          (by rw [add_right_comm]
              refine prepend_mem_gradedPiece (hh.map_mem (subword_mem_gradedPiece x g hxg a d)) ?_
              simpa only [add_zero] using hF'.map_mem (subword_mem_gradedPiece x g hxg (a + d) _))
          (by rw [add_assoc]
              refine prepend_mem_gradedPiece ?_ (ih (b - d) (by omega) (a + d) (by omega))
              simpa only [add_zero] using hfτ.map_mem (subword_mem_gradedPiece x g hxg a d))
  have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D :=
    (Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n).symm.trans
      ((Finset.sum_congr rfl fun i _ ↦ by simp [hg]).trans hD)
  rw [of_tprod_eq_subword R hn, ← hsum]
  exact key n 0 (by omega)

/-- The sum of two coderivations along the same pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.add {q : ℤ}
    {F F' D D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hD' : IsGradedCoderivationAlong G q F F' D') :
    IsGradedCoderivationAlong G q F F' (D + D') := by
  rw [isGradedCoderivationAlong_iff] at hD hD' ⊢
  rw [TensorProduct.map_add_left, TensorProduct.map_add_right, LinearMap.comp_add, hD, hD',
    LinearMap.add_comp, LinearMap.add_comp]
  abel

/-- A scalar multiple of a coderivation along a pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.smul {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (r : R) :
    IsGradedCoderivationAlong G q F F' (r • D) := by
  rw [isGradedCoderivationAlong_iff] at hD ⊢
  rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, LinearMap.comp_smul, hD,
    LinearMap.smul_comp, LinearMap.smul_comp, smul_add]

/-- Following a coderivation along `F` and `F'` by a coalgebra morphism `K` gives a coderivation
along `K ∘ F` and `K ∘ F'`. -/
theorem IsCoalgHom.comp_isGradedCoderivationAlong {P : Type uP} [AddCommMonoid P] [Module R P]
    {K : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R P} (hK : IsCoalgHom R K) {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) :
    IsGradedCoderivationAlong G q (K ∘ₗ F) (K ∘ₗ F') (K ∘ₗ D) := by
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [hK.deconcatenation_apply, hD.deconcatenation_apply, map_add, ← LinearMap.comp_apply
    (TensorProduct.map K K), ← TensorProduct.map_comp, ← LinearMap.comp_apply
    (TensorProduct.map K K), ← TensorProduct.map_comp]

/-- Precomposing a coderivation along `F` and `F'` with a degree-zero coalgebra morphism `K`
gives a coderivation along `F ∘ K` and `F' ∘ K`: the morphism commutes with the letterwise Koszul
twists. -/
theorem IsGradedCoderivationAlong.comp_isCoalgHom {L : Type uL} [AddCommMonoid L] [Module R L]
    {E : InternalGrading R L ℤ} {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    {K : ReducedTensorWords R L →ₗ[R] ReducedTensorWords R M} (hK : IsCoalgHom R K)
    (hK₀ : LinearMap.IsHomogeneous K (gradedPiece E) (gradedPiece G) 0) :
    IsGradedCoderivationAlong E q (F ∘ₗ K) (F' ∘ₗ K) (D ∘ₗ K) := by
  -- A degree-zero map commutes with the letterwise Koszul twists.
  have hτ : ∀ z, ReducedTensorWords.map (R := R) (G.koszulTwist q) (K z) =
      K (ReducedTensorWords.map (R := R) (E.koszulTwist q) z) := fun z ↦ by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hK₀.map_koszulTwist_comp q) z
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [hD.deconcatenation_apply, hK.deconcatenation_apply]
  induction deconcatenation R L z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply, hτ]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- A coalgebra morphism `F` followed by a graded coderivation of the target is a coderivation
along `F` and `F`, provided `F` has degree zero. -/
theorem IsGradedCoderivation.comp_isCoalgHom {q : ℤ}
    {b : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N} (hb : IsGradedCoderivation H q b)
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) :
    IsGradedCoderivationAlong G q F F (b ∘ₗ F) := by
  simpa only [LinearMap.id_comp] using
    ((isGradedCoderivationAlong_id_id_iff (G := H)).2 hb).comp_isCoalgHom hF hF₀

/-- A graded coderivation of the source followed by a coalgebra morphism `F` is a coderivation
along `F` and `F`. -/
theorem IsCoalgHom.comp_isGradedCoderivation {q : ℤ}
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hb : IsGradedCoderivation G q b) :
    IsGradedCoderivationAlong G q F F (F ∘ₗ b) := by
  simpa only [LinearMap.comp_id] using
    hF.comp_isGradedCoderivationAlong ((isGradedCoderivationAlong_id_id_iff (G := G)).2 hb)

/-! ### Intertwining graded coderivations -/

/-- A degree-zero coalgebra morphism intertwines a `q`-twisted graded coderivation of `Tᶜ(M)`
with one of `Tᶜ(N)` as soon as it does so after projection onto single letters: both composites
are coderivations along `F` and `F`. -/
theorem IsCoalgHom.comp_eq_comp_of_letter_comp_eq
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {q : ℤ}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G q bM) (hbN : IsGradedCoderivation H q bN)
    (hl : letter R N ∘ₗ bN ∘ₗ F = letter R N ∘ₗ F ∘ₗ bM) : bN ∘ₗ F = F ∘ₗ bM :=
  (hbN.comp_isCoalgHom hF hF₀).eq_of_letter_comp_eq (hF.comp_isGradedCoderivation hbM) hl

/-- A degree-zero coalgebra morphism intertwines a `q`-twisted graded coderivation of `Tᶜ(M)`
with one of `Tᶜ(N)` if and only if it does so after projection onto single letters. -/
theorem IsCoalgHom.comp_eq_comp_iff_letter_comp_eq
    {F : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0) {q : ℤ}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G q bM) (hbN : IsGradedCoderivation H q bN) :
    bN ∘ₗ F = F ∘ₗ bM ↔ letter R N ∘ₗ bN ∘ₗ F = letter R N ∘ₗ F ∘ₗ bM :=
  ⟨fun h ↦ by rw [h], hF.comp_eq_comp_of_letter_comp_eq hF₀ hbM hbN⟩

/-! ### Differences of coalgebra morphisms and odd coderivations -/

section Difference

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N] {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}

/-- The negation of a coderivation along a pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.neg {q : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) :
    IsGradedCoderivationAlong G q F F' (-D) := by
  have heq : (-1 : R) • D = -D := LinearMap.ext fun z ↦ neg_one_smul R (D z)
  exact heq ▸ hD.smul (-1 : R)

/-- The difference of two coderivations along the same pair of maps is a coderivation along them. -/
theorem IsGradedCoderivationAlong.sub {q : ℤ}
    {F F' D D' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D) (hD' : IsGradedCoderivationAlong G q F F' D') :
    IsGradedCoderivationAlong G q F F' (D - D') := by
  let : AddCommGroup (ReducedTensorWords R N) := inferInstance
  rw [sub_eq_add_neg]
  exact hD.add hD'.neg

/-- Two coderivations along pairs of maps agreeing on `filtration R M n`, whose letter components
also agree on `filtration R M n`, differ on `filtration R M (n + 1)` only in single letters. -/
theorem IsGradedCoderivationAlong.sub_apply_eq_ofLetter_of_mem_filtration_succ {q : ℤ}
    {F₁ F₁' D₁ F₂ F₂' D₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (h₁ : IsGradedCoderivationAlong G q F₁ F₁' D₁)
    (h₂ : IsGradedCoderivationAlong G q F₂ F₂' D₂) {n : ℕ}
    (hF : ∀ z ∈ filtration R M n, F₁ z = F₂ z)
    (hF' : ∀ z ∈ filtration R M n, F₁' z = F₂' z)
    (hl : ∀ z ∈ filtration R M n, letter R N (D₁ z) = letter R N (D₂ z))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    D₁ z - D₂ z = ofLetter R N (letter R N (D₁ z - D₂ z)) := by
  have hD : ∀ w ∈ filtration R M n, D₁ w = D₂ w := fun _ hw ↦
    h₁.apply_eq_of_mem_filtration h₂ hF hF' hl hw
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  rw [deconcatenation_ofLetter, map_sub, sub_eq_zero, h₁.deconcatenation_apply,
    h₂.deconcatenation_apply]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.rTensor_tmul]
      rw [hD u.1 u.2, hD v.1 v.2, hF' v.1 v.2, hF _ ((isCoalgHom_map _).mem_filtration u.2)]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [add_add_add_comm, hu, hv, add_add_add_comm]

/-- The difference of two coalgebra morphisms `F` and `F'` is an untwisted coderivation along `F`
and `F'`: `Δ (F - F') = ((F - F') ⊗ F' + F ⊗ (F - F')) Δ`. -/
theorem IsCoalgHom.isGradedCoderivationAlong_sub
    {F F' : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} (hF : IsCoalgHom R F)
    (hF' : IsCoalgHom R F') : IsGradedCoderivationAlong G 0 F F' (F - F') := by
  rw [isGradedCoderivationAlong_iff, InternalGrading.koszulTwist_zero, ReducedTensorWords.map_id,
    LinearMap.rTensor_id, LinearMap.id_comp]
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, map_sub]
  rw [hF.deconcatenation_apply, hF'.deconcatenation_apply]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.sub_apply, TensorProduct.sub_tmul,
        TensorProduct.tmul_sub]
      abel
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

/-- On a word in `filtration R M (n + 1)`, the graded commutator `b_N ∘ D - (-1)^(q r) D ∘ b_M`
satisfies the `(t + q)`-twisted co-Leibniz rule along `F` and `F'` as soon as `F` and `F'`
intertwine `b_M` and `b_N` on `filtration R M n`. -/
private theorem IsGradedCoderivationAlong.deconcatenation_comp_sub_smul_comp_of_mem_filtration_succ
    {t q r s : ℤ} {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G t F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (t * s).negOnePow = (q * r).negOnePow)
    (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    {n : ℕ} (hF : ∀ w ∈ filtration R M n, bN (F w) = F (bM w))
    (hF' : ∀ w ∈ filtration R M n, bN (F' w) = F' (bM w))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N ((bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) z) =
      TensorProduct.map (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) F'
          (deconcatenation R M z) +
        TensorProduct.map F (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM))
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (G.koszulTwist (t + q))) (deconcatenation R M z)) := by
  set c : R := (((q * r).negOnePow : ℤ) : R) with hc
  have hτF : ∀ w, ReducedTensorWords.map (R := R) (H.koszulTwist q) (F w) =
      F (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) := fun w ↦ by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hF₀.map_koszulTwist_comp q) w
  have hτD : ∀ w, ReducedTensorWords.map (R := R) (H.koszulTwist q) (D w) =
      c • D (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) := fun w ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hD₁.map_koszulTwist_comp q) w
  have hτb : ∀ w, ReducedTensorWords.map (R := R) (G.koszulTwist t) (bM w) =
      c • bM (ReducedTensorWords.map (R := R) (G.koszulTwist t) w) := fun w ↦ by
    simpa only [hs, LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hbM₁.map_koszulTwist_comp t) w
  have hττ : ∀ w, ReducedTensorWords.map (R := R) (G.koszulTwist q)
      (ReducedTensorWords.map (R := R) (G.koszulTwist t) w) =
        ReducedTensorWords.map (R := R) (G.koszulTwist (t + q)) w := fun w ↦ by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp, add_comm]
  have hττ' : ∀ w, ReducedTensorWords.map (R := R) (G.koszulTwist t)
      (ReducedTensorWords.map (R := R) (G.koszulTwist q) w) =
        ReducedTensorWords.map (R := R) (G.koszulTwist (t + q)) w := fun w ↦ by
    rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp, InternalGrading.koszulTwist_comp]
  have hcc : ∀ x : ReducedTensorWords R N ⊗[R] ReducedTensorWords R N, c • c • x = x := fun x ↦ by
    rw [smul_smul, hc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
      Int.cast_one, one_smul]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [map_sub, map_smul, hbN.deconcatenation_apply, hD.deconcatenation_apply,
    hD.deconcatenation_apply, hbM.deconcatenation_apply]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have hFu := hF _ ((isCoalgHom_map (G.koszulTwist t)).mem_filtration u.2)
      have hF'v := hF' _ v.2
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, map_add, map_smul,
        TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, hτF, hτD, hτb, hττ, hττ',
        hFu, hF'v, TensorProduct.tmul_sub, TensorProduct.sub_tmul, TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul', smul_add, hcc]
      abel
  | add u v hu hv =>
      simp only [map_add, smul_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

/-- Let `D` be a coderivation along `F` and `F'` with twist parameter `t` and of degree `r`, where
`F` has degree zero and both `F` and `F'` intertwine coderivations `b_M` of `Tᶜ(M)` and `b_N` of
`Tᶜ(N)` with twist parameter `q`, with `b_M` of degree `s`.  If `(-1)^(t s) = (-1)^(q r)`, then the
graded commutator `b_N ∘ D - (-1)^(q r) D ∘ b_M` is a coderivation along `F` and `F'` with twist
parameter `t + q`.  On each cut, the cross terms cancel in pairs because `D` commutes with the
twist of parameter `q`, and `b_M` with that of parameter `t`, up to this common sign.  For
transformations of degree `p` this is the differential of the complex of coderivations along `F`
and `F'`. -/
theorem IsGradedCoderivationAlong.comp_sub_negOnePow_smul_comp {t q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G t F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (t * s).negOnePow = (q * r).negOnePow)
    (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF : bN ∘ₗ F = F ∘ₗ bM) (hF' : bN ∘ₗ F' = F' ∘ₗ bM) :
    IsGradedCoderivationAlong G (t + q) F F'
      (bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM)) := by
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  exact hD.deconcatenation_comp_sub_smul_comp_of_mem_filtration_succ hD₁ hbM hbM₁ hs hbN
    hF₀ (fun w _ ↦ LinearMap.congr_fun hF w) (fun w _ ↦ LinearMap.congr_fun hF' w)
    (filtration_monotone R M n.le_succ hn)

/-- Let `D` be an odd coderivation along `F` and `F'`, where `F` has degree zero and both `F` and
`F'` intertwine odd graded coderivations `b_M` of `Tᶜ(M)` and `b_N` of `Tᶜ(N)`.  Then
`b_N ∘ D + D ∘ b_M` is an untwisted coderivation along `F` and `F'`.  This is the case of
`IsGradedCoderivationAlong.comp_sub_negOnePow_smul_comp` where all twists agree and both signs
are `-1`. -/
theorem IsGradedCoderivationAlong.comp_add_comp {q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = -1)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF : bN ∘ₗ F = F ∘ₗ bM) (hF' : bN ∘ₗ F' = F' ∘ₗ bM) :
    IsGradedCoderivationAlong G 0 F F' (bN ∘ₗ D + D ∘ₗ bM) := by
  have h := hD.comp_sub_negOnePow_smul_comp hD₁ hbM hbM₁ (hs.trans hr.symm) hbN hF₀ hF hF'
  have he : bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM) = bN ∘ₗ D + D ∘ₗ bM :=
    LinearMap.ext fun z ↦ by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, hr, Units.val_neg,
        Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul, sub_neg_eq_add]
  rw [he] at h
  have hτ : G.koszulTwist (q + q) = G.koszulTwist 0 := by
    rw [← InternalGrading.koszulTwist_comp, InternalGrading.koszulTwist_comp_self,
      InternalGrading.koszulTwist_zero]
  rwa [isGradedCoderivationAlong_iff, hτ, ← isGradedCoderivationAlong_iff] at h

/-- **The homotopy equation is determined by its letter component.**  Under the hypotheses of
`IsGradedCoderivationAlong.comp_add_comp`, if `F'` is also a coalgebra morphism, then
`F - F' = b_N ∘ D + D ∘ b_M` holds as soon as it holds after projection onto single letters. -/
theorem IsGradedCoderivationAlong.sub_eq_comp_add_comp_iff {q r s : ℤ}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = -1)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hFc : IsCoalgHom R F) (hF'c : IsCoalgHom R F')
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF : bN ∘ₗ F = F ∘ₗ bM) (hF' : bN ∘ₗ F' = F' ∘ₗ bM) :
    F - F' = bN ∘ₗ D + D ∘ₗ bM ↔
      letter R N ∘ₗ (F - F') = letter R N ∘ₗ (bN ∘ₗ D + D ∘ₗ bM) :=
  ⟨fun h ↦ by rw [h], (hFc.isGradedCoderivationAlong_sub hF'c).eq_of_letter_comp_eq
    (hD.comp_add_comp hD₁ hr hbM hbM₁ hs hbN hF₀ hF hF')⟩

/-- When `F` and `F'` intertwine `b_M` and `b_N` on `filtration R M n` and the homotopy defect
`F - F' - (b_N ∘ D + D ∘ b_M)` vanishes on `filtration R M n`, the defect sends every word in
`filtration R M (n + 1)` into single letters. -/
theorem IsGradedCoderivationAlong.sub_comp_add_comp_eq_ofLetter
    {q r s : ℤ} {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hD : IsGradedCoderivationAlong G q F F' D)
    (hD₁ : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) r)
    (hr : (q * r).negOnePow = -1)
    (hbM : IsGradedCoderivation G q bM)
    (hbM₁ : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) s)
    (hs : (q * s).negOnePow = -1) (hbN : IsGradedCoderivation H q bN)
    (hFc : IsCoalgHom R F) (hF'c : IsCoalgHom R F')
    (hF₀ : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    {n : ℕ} (hF : ∀ w ∈ filtration R M n, bN (F w) = F (bM w))
    (hF' : ∀ w ∈ filtration R M n, bN (F' w) = F' (bM w))
    (hsub : ∀ w ∈ filtration R M n, (F - F' - (bN ∘ₗ D + D ∘ₗ bM)) w = 0)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    (F - F' - (bN ∘ₗ D + D ∘ₗ bM)) z =
      ofLetter R N (letter R N ((F - F' - (bN ∘ₗ D + D ∘ₗ bM)) z)) := by
  let : AddCommGroup (ReducedTensorWords R N) := inferInstance
  have he : bN ∘ₗ D - ((((q * r).negOnePow : ℤ) : R)) • (D ∘ₗ bM) = bN ∘ₗ D + D ∘ₗ bM :=
    LinearMap.ext fun w ↦ by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, hr, Units.val_neg,
        Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul, sub_neg_eq_add]
  have hτ : G.koszulTwist (q + q) = LinearMap.id := by
    rw [← InternalGrading.koszulTwist_comp, InternalGrading.koszulTwist_comp_self]
  have hΔ₁ := (hFc.isGradedCoderivationAlong_sub (G := G) hF'c).deconcatenation_apply z
  rw [InternalGrading.koszulTwist_zero, ReducedTensorWords.map_id, LinearMap.rTensor_id] at hΔ₁
  have hΔ₂ := hD.deconcatenation_comp_sub_smul_comp_of_mem_filtration_succ hD₁ hbM hbM₁
    (hs.trans hr.symm) hbN hF₀ hF hF' hz
  rw [he, hτ, ReducedTensorWords.map_id, LinearMap.rTensor_id] at hΔ₂
  refine eq_of_deconcatenation_eq_of_letter_eq R N ?_ (letter_ofLetter R N _).symm
  rw [deconcatenation_ofLetter]
  change deconcatenation R N ((F - F') z - (bN ∘ₗ D + D ∘ₗ bM) z) = 0
  rw [map_sub, hΔ₁, hΔ₂]
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, TensorProduct.map_tmul,
        LinearMap.id_apply]
      have hu : (F - F') u.1 - (bN ∘ₗ D + D ∘ₗ bM) u.1 = 0 := hsub u.1 u.2
      have hv : (F - F') v.1 - (bN ∘ₗ D + D ∘ₗ bM) v.1 = 0 := hsub v.1 v.2
      rw [sub_eq_zero.1 hu, sub_eq_zero.1 hv, sub_self]
  | add u v hu hv =>
      simp only [map_add, LinearMap.id_apply] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1
      · abel
      · rw [add_zero]

end Difference

/-! ### Inverses -/

section Inverse

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The inverse of a degree-zero linear equivalence of reduced tensor coalgebras which is a
coalgebra morphism is again homogeneous of degree zero. -/
theorem IsCoalgHom.isHomogeneous_linearEquiv_symm {G : InternalGrading R M ℤ}
    {H : InternalGrading R N ℤ} {e : ReducedTensorWords R M ≃ₗ[R] ReducedTensorWords R N}
    (he : IsCoalgHom R e.toLinearMap)
    (he₀ : LinearMap.IsHomogeneous e.toLinearMap (gradedPiece G) (gradedPiece H) 0) :
    LinearMap.IsHomogeneous e.symm.toLinearMap (gradedPiece H) (gradedPiece G) 0 := by
  -- No independence of the total-degree pieces is available, so the inverse is not read off a
  -- decomposition.  Instead `e` is corrected by the letterwise inverse of its arity-one
  -- component `e₁` to a coalgebra endomorphism `U` fixing every letter; `U` preserves each
  -- total-degree piece and, being the identity up to a filtration-lowering map, maps it onto
  -- itself.
  -- The arity-one component `e₁` is a degree-zero linear equivalence of the letters.
  set e₁ : M ≃ₗ[R] N := LinearEquiv.ofBijective _ he.letter_comp_comp_ofLetter_bijective
  have he₁ : LinearMap.IsHomogeneous e₁.toLinearMap G.piece H.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p a ha
    have h := (isHomogeneous_letter H).map_mem (he₀.map_mem (ofLetter_mem_gradedPiece G ha))
    rw [add_zero, add_zero] at h
    rw [add_zero]
    exact h
  have he₁' := (isHomogeneous_map H G he₁.linearEquiv_symm)
  -- The correction `U` is a degree-zero coalgebra endomorphism fixing every letter.
  set U := ReducedTensorWords.map (R := R) e₁.symm.toLinearMap ∘ₗ e.toLinearMap with hUdef
  have hU : IsCoalgHom R U := (isCoalgHom_map _).comp he
  have hU₁ : U ∘ₗ ofLetter R M = ofLetter R M := he.map_symm_comp_comp_ofLetter _
  have hU₀ := he₁'.comp he₀
  rw [zero_add] at hU₀
  rw [LinearMap.isHomogeneous_def]
  intro D w hw
  rw [add_zero]
  have hw' : ReducedTensorWords.map (R := R) e₁.symm.toLinearMap w ∈ gradedPiece G D := by
    simpa only [add_zero] using he₁'.map_mem hw
  have hp : (gradedPiece G D).map U ≤ gradedPiece G D := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [add_zero] using hU₀.map_mem hz
  have hw'' : ReducedTensorWords.map (R := R) e₁.symm.toLinearMap w ∈ (gradedPiece G D).map U := by
    rw [hU.map_eq_of_map_le (p := gradedPiece G D) hU₁ hp]
    exact hw'
  obtain ⟨z, hz, hUz⟩ := hw''
  have hez : e z = w := by
    have h := congrArg (ReducedTensorWords.map (R := R) e₁.toLinearMap) hUz
    rwa [hUdef, LinearMap.comp_apply, map_map_symm, map_map_symm, LinearEquiv.coe_coe] at h
  rw [← hez, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact hz

end Inverse

end ReducedTensorWords

end TauCeti
