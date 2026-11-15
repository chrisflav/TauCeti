/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Bicofree
public import TauCeti.LinearAlgebra.End.LocallyNilpotent
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic

/-!
# Filtration and bijective morphisms of cofree bicomodules over tensor words

Let `Tᶜ(A)` and `Tᶜ(B)` be coaugmented tensor coalgebras with deconcatenation.  The cofree
bicomodule `(Tᶜ(A) ⊗ M) ⊗ Tᶜ(B)` carries an increasing exhaustive filtration
`TauCeti.TensorWords.bicofreeFiltration` by total word length `i + j < n`.

* Any endomorphism sending every pure word of lengths `(i, j)` into filtration level `i + j`
  strictly lowers total word length, hence is locally nilpotent
  (`TauCeti.TensorWords.exists_pow_apply_eq_zero_of_of_tprod_mem_bicofreeFiltration`).
* Any bicomodule morphism `F : (Tᶜ(A) ⊗ M) ⊗ Tᶜ(B) ⟶ (Tᶜ(A) ⊗ N) ⊗ Tᶜ(B)` expands a pair of words
  by cutting both at every position; the summand with empty inner cuts applies the restriction of
  `F` to `(1 ⊗ x) ⊗ 1`, and every other summand strictly lowers total word length.  Consequently
  `F` is bijective as soon as its restriction `(1 ⊗ x) ⊗ 1 ↦ (1 ⊗ g x) ⊗ 1` is given by a
  bijective linear map `g` (`TauCeti.Comodule.Hom.bijective_of_apply_one_tmul_tmul_one`).

These are the two-sided counterparts of `TauCeti.Comodule.Hom.bijective_of_apply_tmul_one` in
`TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.CofreeHom`; they underlie homological transfer
and invertibility of morphisms for `A∞` bimodules.

## Main definitions

* `TauCeti.TensorWords.bicofreeFiltration`: the submodule of `(Tᶜ(A) ⊗ M) ⊗ Tᶜ(B)` spanned by
  pairs of words of total length `< n`.

## Main results

* `TauCeti.TensorWords.exists_pow_apply_eq_zero_of_of_tprod_mem_bicofreeFiltration`: an
  endomorphism strictly lowering total word length on pure tensor words is locally nilpotent.
* `TauCeti.Comodule.Hom.bijective_of_apply_one_tmul_tmul_one`: a morphism of cofree
  `(Tᶜ(A), Tᶜ(B))`-bicomodules is bijective when its restriction to the two empty words is.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uM uN

attribute [local instance] Comodule.cofree

namespace TensorWords

section Semiring

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
  [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid M] [Module R M]

variable (R A B M) in
/-- The submodule of `(Tᶜ(A) ⊗ M) ⊗ Tᶜ(B)` built from pairs of words of total length `< n`. -/
noncomputable def bicofreeFiltration (n : ℕ) :
    Submodule R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :=
  ⨆ i ∈ Finset.range n, ⨆ j ∈ Finset.range (n - i),
    LinearMap.range (TensorProduct.map ((of R A i).rTensor M) (of R B j))

/-- Defining presentation of `bicofreeFiltration` as the supremum of word-length pieces with
`i + j < n`. -/
theorem bicofreeFiltration_def (n : ℕ) :
    bicofreeFiltration R A B M n =
      ⨆ i ∈ Finset.range n, ⨆ j ∈ Finset.range (n - i),
        LinearMap.range (TensorProduct.map ((of R A i).rTensor M) (of R B j)) :=
  (rfl)

/-- No pair of words has total length `< 0`. -/
@[simp]
theorem bicofreeFiltration_zero : bicofreeFiltration R A B M 0 = ⊥ := by
  simp [bicofreeFiltration_def]

/-- The total-word-length filtration is monotone. -/
theorem bicofreeFiltration_mono {m n : ℕ} (h : m ≤ n) :
    bicofreeFiltration R A B M m ≤ bicofreeFiltration R A B M n := by
  refine iSup₂_le fun i hi ↦ iSup₂_le fun j hj ↦ ?_
  rw [Finset.mem_range] at hi hj
  exact le_biSup (fun i ↦ ⨆ j ∈ Finset.range (n - i),
      LinearMap.range (TensorProduct.map ((of R A i).rTensor M) (of R B j)))
    (Finset.mem_range.2 (by omega)) |>.trans' <|
    le_biSup (fun j ↦ LinearMap.range (TensorProduct.map ((of R A i).rTensor M) (of R B j)))
      (Finset.mem_range.2 (by omega))

/-- The image of `(A^⊗i ⊗ M) ⊗ B^⊗j` lies in filtration level `n` whenever `i + j < n`. -/
theorem map_of_mem_bicofreeFiltration {i j n : ℕ} (hij : i + j < n)
    (y : (TensorPower R i A ⊗[R] M) ⊗[R] TensorPower R j B) :
    TensorProduct.map ((of R A i).rTensor M) (of R B j) y ∈ bicofreeFiltration R A B M n := by
  refine Submodule.mem_iSup_of_mem i <| Submodule.mem_iSup_of_mem (Finset.mem_range.2 (by omega)) <|
    Submodule.mem_iSup_of_mem j <| Submodule.mem_iSup_of_mem (Finset.mem_range.2 (by omega)) ?_
  exact LinearMap.mem_range_self _ y

/-- A pure tensor of words of lengths `i` and `j` lies in filtration level `n` when `i + j < n`. -/
theorem of_tmul_tmul_of_mem_bicofreeFiltration {i j n : ℕ} (hij : i + j < n)
    (u : TensorPower R i A) (x : M) (v : TensorPower R j B) :
    (of R A i u ⊗ₜ[R] x) ⊗ₜ[R] of R B j v ∈ bicofreeFiltration R A B M n :=
  map_of_mem_bicofreeFiltration hij ((u ⊗ₜ x) ⊗ₜ v)

/-- Subwords of lengths `l₁` and `l₂` around a module element lie in filtration level `n` whenever
`l₁ + l₂ < n`. -/
theorem subword_tmul_tmul_subword_mem_bicofreeFiltration {m₁ m₂ : ℕ}
    (a : Fin m₁ → A) (b₁ l₁ : ℕ) (x : M) (b : Fin m₂ → B) (b₂ l₂ : ℕ) {n : ℕ}
    (hl : l₁ + l₂ < n) :
    (subword R a b₁ l₁ ⊗ₜ[R] x) ⊗ₜ[R] subword R b b₂ l₂ ∈ bicofreeFiltration R A B M n := by
  by_cases h₁ : b₁ + l₁ ≤ m₁
  · by_cases h₂ : b₂ + l₂ ≤ m₂
    · rw [subword_eq_of_tprod R a h₁, subword_eq_of_tprod R b h₂]
      exact of_tmul_tmul_of_mem_bicofreeFiltration hl _ _ _
    · rw [subword_eq_zero_of_lt_add R b (by omega), TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
  · rw [subword_eq_zero_of_lt_add R a (by omega), TensorProduct.zero_tmul, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _

/-- A submodule contains `bicofreeFiltration R A B M n` as soon as it contains every pure tensor of
letter tuples of total length `< n`. -/
theorem bicofreeFiltration_le {n : ℕ}
    {P : Submodule R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)}
    (h : ∀ {i j : ℕ}, i + j < n → ∀ (a : Fin i → A) (x : M) (b : Fin j → B),
      (of R A i (PiTensorProduct.tprod R a) ⊗ₜ[R] x) ⊗ₜ[R]
        of R B j (PiTensorProduct.tprod R b) ∈ P) :
    bicofreeFiltration R A B M n ≤ P := by
  refine iSup₂_le fun i hi ↦ iSup₂_le fun j hj ↦ ?_
  rw [Finset.mem_range] at hi hj
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.inductionOn with
  | tmul ux v =>
    induction ux using TensorProduct.inductionOn with
    | tmul u x =>
      induction u using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        induction v using PiTensorProduct.induction_on with
        | smul_tprod s b =>
          rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
            map_smul, map_smul, TensorProduct.map_tmul, LinearMap.rTensor_tmul]
          exact P.smul_mem r (P.smul_mem s (h (by omega) a x b))
        | add v v' hv hv' =>
          rw [TensorProduct.tmul_add, map_add]
          exact P.add_mem hv hv'
      | add u u' hu hu' =>
        rw [TensorProduct.add_tmul, TensorProduct.add_tmul, map_add]
        exact P.add_mem hu hu'
    | add ux ux' hux hux' =>
      rw [TensorProduct.add_tmul, map_add]
      exact P.add_mem hux hux'
  | add y y' hy hy' =>
    rw [map_add]
    exact P.add_mem hy hy'

/-- Every element of `(Tᶜ(A) ⊗ M) ⊗ Tᶜ(B)` lies in some level of the total-word-length
filtration. -/
theorem exists_mem_bicofreeFiltration
    (z : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :
    ∃ n, z ∈ bicofreeFiltration R A B M n := by
  induction z using TensorProduct.inductionOn with
  | tmul y v =>
    induction y using TensorProduct.inductionOn with
    | tmul u x =>
      induction u using DirectSum.induction_on with
      | zero =>
        exact ⟨0, by
          rw [TensorProduct.zero_tmul, TensorProduct.zero_tmul]
          exact Submodule.zero_mem _⟩
      | of i u' =>
        induction v using DirectSum.induction_on with
        | zero =>
          exact ⟨0, by rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _⟩
        | of j v' =>
          refine ⟨i + j + 1, ?_⟩
          have h := of_tmul_tmul_of_mem_bicofreeFiltration (R := R) (Nat.lt_succ_self (i + j))
            u' x v'
          rwa [of_def, of_def, DirectSum.lof_eq_of, DirectSum.lof_eq_of] at h
        | add v₁ v₂ hv₁ hv₂ =>
          obtain ⟨n₁, hn₁⟩ := hv₁
          obtain ⟨n₂, hn₂⟩ := hv₂
          exact ⟨max n₁ n₂, by
            rw [TensorProduct.tmul_add]
            exact Submodule.add_mem _ (bicofreeFiltration_mono (le_max_left _ _) hn₁)
              (bicofreeFiltration_mono (le_max_right _ _) hn₂)⟩
      | add u₁ u₂ hu₁ hu₂ =>
        obtain ⟨n₁, hn₁⟩ := hu₁
        obtain ⟨n₂, hn₂⟩ := hu₂
        exact ⟨max n₁ n₂, by
          rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
          exact Submodule.add_mem _ (bicofreeFiltration_mono (le_max_left _ _) hn₁)
            (bicofreeFiltration_mono (le_max_right _ _) hn₂)⟩
    | add y₁ y₂ hy₁ hy₂ =>
      obtain ⟨n₁, hn₁⟩ := hy₁
      obtain ⟨n₂, hn₂⟩ := hy₂
      exact ⟨max n₁ n₂, by
        rw [TensorProduct.add_tmul]
        exact Submodule.add_mem _ (bicofreeFiltration_mono (le_max_left _ _) hn₁)
          (bicofreeFiltration_mono (le_max_right _ _) hn₂)⟩
  | add z₁ z₂ hz₁ hz₂ =>
    obtain ⟨n₁, hn₁⟩ := hz₁
    obtain ⟨n₂, hn₂⟩ := hz₂
    exact ⟨max n₁ n₂, Submodule.add_mem _ (bicofreeFiltration_mono (le_max_left _ _) hn₁)
      (bicofreeFiltration_mono (le_max_right _ _) hn₂)⟩

/-- **Local nilpotence from total word length.**  If an endomorphism `f` of `(Tᶜ(A) ⊗ M) ⊗ Tᶜ(B)`
sends every pure tensor of words of lengths `(i, j)` into `bicofreeFiltration R A B M (i + j)`,
then every element is killed by some power of `f`. -/
theorem exists_pow_apply_eq_zero_of_of_tprod_mem_bicofreeFiltration
    (f : Module.End R ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B))
    (hf : ∀ (i j : ℕ) (a : Fin i → A) (x : M) (b : Fin j → B),
      f ((of R A i (PiTensorProduct.tprod R a) ⊗ₜ[R] x) ⊗ₜ[R]
        of R B j (PiTensorProduct.tprod R b)) ∈ bicofreeFiltration R A B M (i + j))
    (z : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :
    ∃ n, (f ^ n) z = 0 := by
  have hstep (n : ℕ) :
      bicofreeFiltration R A B M (n + 1) ≤ (bicofreeFiltration R A B M n).comap f :=
    bicofreeFiltration_le fun hij a x b ↦
      bicofreeFiltration_mono (by omega) (hf _ _ a x b)
  have hnil (n : ℕ) : ∀ w ∈ bicofreeFiltration R A B M n, (f ^ n) w = 0 := by
    induction n with
    | zero =>
      intro w hw
      rw [bicofreeFiltration_zero, Submodule.mem_bot] at hw
      rw [hw, map_zero]
    | succ n ih =>
      intro w hw
      rw [pow_succ, _root_.mul_apply_eq_comp]
      exact ih (f w) (hstep n hw)
  obtain ⟨n, hn⟩ := exists_mem_bicofreeFiltration z
  exact ⟨n, hnil n z hn⟩

/-- A bicofree lift expands a pair of subwords by cutting both at every position. -/
theorem bicofreeLift_apply_subword {N : Type uN} [AddCommMonoid N] [Module R N]
    (φ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] N)
    {m₁ m₂ : ℕ} (a : Fin m₁ → A) (b₁ l₁ : ℕ) (x : M) (b : Fin m₂ → B) (b₂ l₂ : ℕ) :
    Comodule.bicofreeLift φ ((subword R a b₁ l₁ ⊗ₜ[R] x) ⊗ₜ[R] subword R b b₂ l₂) =
      ∑ r ∈ Finset.range (l₂ + 1), ∑ l ∈ Finset.range (l₁ + 1),
        (subword R a b₁ l ⊗ₜ[R]
          φ ((subword R a (b₁ + l) (l₁ - l) ⊗ₜ[R] x) ⊗ₜ[R] subword R b b₂ r)) ⊗ₜ[R]
            subword R b (b₂ + r) (l₂ - r) := by
  have h := congrArg (fun k ↦ k ((subword R a b₁ l₁ ⊗ₜ[R] x) ⊗ₜ[R] subword R b b₂ l₂))
    (Comodule.bicofreeLift_toLinearMap φ)
  simp only [Comodule.Hom.coe_toLinearMap, LinearMap.comp_apply, Comodule.cofreeCoact_def,
    LinearMap.lTensor_tmul, comul_eq_deconcatenation, deconcatenation_subword,
    TensorProduct.tmul_sum, map_sum, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
    LinearMap.rTensor_tmul, Comodule.leftCoactRTensor_tmul, Comodule.leftCofreeCoact_tmul,
    TensorProduct.sum_tmul, TensorProduct.assoc_tmul] at h
  exact h

end Semiring

/-! ### Bijectivity of bicofree morphisms -/

section Ring

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
  [CommRing R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid M] [Module R M]

private noncomputable local instance :
    AddCommGroup ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :=
  Module.addCommMonoidToAddCommGroup R

/-- A cofree bicomodule endomorphism fixing `(1 ⊗ x) ⊗ 1` moves a pair of words of total length at
most `n` by pairs of words of total length `< n`. -/
private theorem sub_mem_bicofreeFiltration
    {G : Comodule.Hom R (TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)}
    (hGl : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ G.toLinearMap =
      G.toLinearMap.lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M))
    (hG : ∀ x : M, G ((1 ⊗ₜ x) ⊗ₜ 1) = (1 ⊗ₜ x) ⊗ₜ 1) {n : ℕ}
    {z : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B}
    (hz : z ∈ bicofreeFiltration R A B M (n + 1)) :
    G z - z ∈ bicofreeFiltration R A B M n := by
  set φ := Comodule.leftCofreeCounit R (TensorWords R A) M ∘ₗ
    (TensorProduct.rid R (TensorWords R A ⊗[R] M)).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := TensorWords R B)).lTensor (TensorWords R A ⊗[R] M) ∘ₗ
        G.toLinearMap
  have hφ : ∀ x : M, φ ((1 ⊗ₜ x) ⊗ₜ 1) = x := fun x ↦ by
    simp [φ, Comodule.Hom.coe_toLinearMap, hG x]
  have hGφ : G = Comodule.bicofreeLift φ := (Comodule.bicofreeLift_counit_comp G hGl).symm
  refine bicofreeFiltration_le (P := (bicofreeFiltration R A B M n).comap
    (G.toLinearMap - LinearMap.id)) (fun {i j} hij a x b ↦ ?_) hz
  rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, Comodule.Hom.coe_toLinearMap,
    of_tprod_eq_subword R a, of_tprod_eq_subword R b, hGφ, bicofreeLift_apply_subword,
    Finset.sum_range_succ', Finset.sum_range_succ _ i, subword_length_zero R b (Nat.zero_le j),
    Nat.zero_add i, Nat.sub_self, subword_length_zero R a le_rfl, hφ x, Nat.zero_add, Nat.sub_zero,
    ← add_assoc, add_sub_cancel_right]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun r hr ↦ Submodule.sum_mem _ fun l hl ↦ ?_)
    (Submodule.sum_mem _ fun l hl ↦ ?_)
  · rw [Finset.mem_range] at hr hl
    exact subword_tmul_tmul_subword_mem_bicofreeFiltration a 0 l _ b (0 + (r + 1)) (j - (r + 1))
      (by omega)
  · rw [Finset.mem_range] at hl
    exact subword_tmul_tmul_subword_mem_bicofreeFiltration a 0 l _ b 0 j (by omega)

/-- A cofree bicomodule endomorphism fixing `(1 ⊗ x) ⊗ 1` is bijective. -/
private theorem bijective_of_apply_one_tmul_tmul_one_eq
    {G : Comodule.Hom R (TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)}
    (hGl : Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) M) ∘ₗ G.toLinearMap =
      G.toLinearMap.lTensor (TensorWords R A) ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M))
    (hG : ∀ x : M, G ((1 ⊗ₜ x) ⊗ₜ 1) = (1 ⊗ₜ x) ⊗ₜ 1) : Function.Bijective G :=
  Module.End.bijective_of_sub_mem_filtration (p := bicofreeFiltration R A B M) (f := G.toLinearMap)
    bicofreeFiltration_zero exists_mem_bicofreeFiltration
    fun _ _ hw ↦ sub_mem_bicofreeFiltration hGl hG hw

end Ring

end TensorWords

namespace Comodule.Hom

/-- A morphism of cofree `(Tᶜ(A), Tᶜ(B))`-bicomodules is bijective when its restriction to the two
empty words, `(1 ⊗ x) ⊗ 1 ↦ (1 ⊗ g x) ⊗ 1`, is given by a bijective linear map `g`. -/
theorem bijective_of_apply_one_tmul_tmul_one {R : Type uR} {A : Type uA} {B : Type uB}
    {M : Type uM} {N : Type uN} [CommRing R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (F : Comodule.Hom R (TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B))
    (hFl : leftCoactRTensor (TensorWords R B) (leftCofreeCoact R (TensorWords R A) N) ∘ₗ
        F.toLinearMap =
      F.toLinearMap.lTensor (TensorWords R A) ∘ₗ
        leftCoactRTensor (TensorWords R B) (leftCofreeCoact R (TensorWords R A) M))
    {g : M →ₗ[R] N} (hg : Function.Bijective g)
    (hF : ∀ x : M, F ((1 ⊗ₜ x) ⊗ₜ 1) = (1 ⊗ₜ g x) ⊗ₜ 1) :
    Function.Bijective F := by
  set e := LinearEquiv.ofBijective g hg
  set E : ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) ≃ₗ[R]
      ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) :=
    (e.lTensor (TensorWords R A)).rTensor (TensorWords R B)
  set G := (cofreeMap (C := TensorWords R B)
    (e.symm.toLinearMap.lTensor (TensorWords R A))).comp F
  have hGl : leftCoactRTensor (TensorWords R B) (leftCofreeCoact R (TensorWords R A) M) ∘ₗ
      G.toLinearMap =
    G.toLinearMap.lTensor (TensorWords R A) ∘ₗ
      leftCoactRTensor (TensorWords R B) (leftCofreeCoact R (TensorWords R A) M) := by
    rw [comp_toLinearMap, cofreeMap_toLinearMap, ← LinearMap.comp_assoc,
      leftCoactRTensor_comp_lTensor_rTensor, LinearMap.comp_assoc, hFl, ← LinearMap.comp_assoc,
      ← LinearMap.lTensor_comp]
  have hG : ∀ x : M, G ((1 ⊗ₜ x) ⊗ₜ 1) = (1 ⊗ₜ x) ⊗ₜ 1 := fun x ↦ by
    simp [G, hF, e]
  have hFG : ⇑F = ⇑E ∘ ⇑G := by
    funext z
    simp only [G, E, Function.comp_apply, comp_apply, cofreeMap_apply]
    exact (E.apply_symm_apply _).symm
  rw [hFG]
  exact E.bijective.comp (TensorWords.bijective_of_apply_one_tmul_tmul_one_eq hGl hG)

end Comodule.Hom

end TauCeti
