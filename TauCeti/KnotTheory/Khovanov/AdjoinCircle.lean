/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Mark
public import TauCeti.KnotTheory.PDCode.Reidemeister.Circle

/-!
# Adjoining a disjoint circle to a Khovanov complex

Adjoining an isolated crossing-free circle to a diagram tensors every state module by the
rank-two Frobenius algebra `V = R[X]/(X²)`, whose generators `1` and `X` lie in quantum degrees
`+1` and `-1`. At the level of circle tensors, for any injective index map `ι : σ → τ` with a
single omitted circle `ν : τ`, the maps
* `birthOne := fiberwiseMul ι` (degree `+1`),
* `birthX := circleX ν ∘ fiberwiseMul ι` (degree `-1`),
* `deathOne := fiberwiseSplit ι ∘ circleX ν` (degree `-1`),
* `deathX := fiberwiseSplit ι` (degree `+1`)

form a binary biproduct decomposition of `CircleTensor R τ` into two copies of `CircleTensor R σ`.
When a collapse map `f : τ → σ` fixes `ι` and sends `ν` to a circle `c₀`, merging along `f` sends
`(1, X)` on the new circle to `(id, circleX c₀)`, and dually splitting along `f` sends `1` and `X`
on `c₀` to `(circleX c₀, id)`.

Applying this decomposition vertexwise to a planar PD-code `D` and its adjoined-circle code
`D.adjoinCircle` produces direct-sum splittings of:
* the cube of resolutions (`TauCeti.PDCode.adjoinCircleResolutionCubeIso`),
* the unnormalized Khovanov bracket (`TauCeti.PDCode.adjoinCircleKhovanovBracketIso`),
* the normalized Khovanov complex (`TauCeti.OrientedPDCode.adjoinCircleKhovanovComplexIso`), and
* the bigraded Khovanov homology (`TauCeti.OrientedPDCode.adjoinCircleKhovanovHomologyIso`).

For any mark `p` on `D`, collapsing the adjoined circle onto the circle through `p` induces a
merge cube map `TauCeti.PDCode.adjoinCircleCollapseMerge` and a split cube map
`TauCeti.PDCode.adjoinCircleCollapseSplit` whose components on the two summands are the identity
and the `X`-action `TauCeti.PDCode.resolutionCubeMarkX`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §4.2.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.5.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Finset PiTensorProduct DualNumber

/-! ### Single-complement circle-tensor splitting -/

namespace TauCeti.Khovanov

section Semiring

variable {R : Type*} [CommSemiring R]

/-- On the labelling basis, merging along an injection `ι` places `1` (`false`) on every circle
outside the range of `ι` and keeps the input label on every `ι i`. -/
theorem fiberwiseMul_circleBasis_of_injective {σ τ : Type*} [Fintype σ] [Finite τ] [DecidableEq τ]
    {ι : σ → τ} (hι : Function.Injective ι) (l : σ → Bool) :
    fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) ι (circleBasis R σ l) =
      circleBasis R τ fun y ↦ decide (∃ i, ι i = y ∧ l i = true) := by
  let := Fintype.ofFinite τ
  rw [fiberwiseMul_circleBasis]
  have hle : ∀ y, #{i | ι i = y ∧ l i = true} ≤ 1 := fun y ↦
    Finset.card_le_one.mpr fun a ha b hb ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hι (ha.1.trans hb.1.symm)
  exact ite_eq_left_iff.mpr fun h ↦ absurd hle h

private theorem decide_exists_eq_of_injective {σ τ : Type*} [Fintype σ] [DecidableEq τ]
    {ι : σ → τ} (hι : Function.Injective ι) (p : σ → Bool) (i : σ) :
    decide (∃ i', ι i' = ι i ∧ p i' = true) = p i := by
  cases hpi : p i
  · exact decide_eq_false fun ⟨i', hi', hp'⟩ ↦ by
      obtain rfl := hι hi'
      rw [hpi] at hp'
      exact Bool.noConfusion hp'
  · exact decide_eq_true ⟨i, rfl, hpi⟩

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

/-- On the labelling basis, splitting along an injection `ι` with unique omitted circle `ν`
extracts the coefficient of `X` (`true`) on `ν` and restricts the remaining labels along `ι`. -/
theorem fiberwiseSplit_circleBasis_of_singleComplement {ι : σ → τ} (hι : Function.Injective ι)
    {ν : τ} (hν : ν ∉ Set.range ι) (hcov : ∀ y, y = ν ∨ y ∈ Set.range ι) (k : τ → Bool) :
    fiberwiseSplit (R := R) ι (circleBasis R τ k) =
      if k ν then circleBasis R σ (k ∘ ι) else 0 := by
  classical
  refine (circleBasis R σ).ext_elem fun l ↦ ?_
  rw [circleBasis_repr_fiberwiseSplit]
  have hle : ∀ j, #{i | ι i = j ∧ (!l i) = true} ≤ 1 := fun j ↦
    Finset.card_le_one.mpr fun a ha b hb ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hι (ha.1.trans hb.1.symm)
  rw [ite_eq_left_iff.mpr fun h ↦ absurd hle h, Module.Basis.repr_self, Finsupp.single_apply]
  have hnone : ¬∃ i, ι i = ν ∧ (!l i) = true := fun ⟨i, hi, _⟩ ↦ hν ⟨i, hi⟩
  have heq : (k = fun j ↦ !decide (∃ i, ι i = j ∧ (!l i) = true)) ↔
      (k ν = true ∧ k ∘ ι = l) := by
    constructor
    · intro hk
      refine ⟨?_, ?_⟩
      · have h1 := congrFun hk ν
        rwa [decide_eq_false hnone, Bool.not_false] at h1
      · funext i
        have h1 := congrFun hk (ι i)
        rwa [decide_exists_eq_of_injective hι (fun j ↦ !l j) i, Bool.not_not] at h1
    · rintro ⟨hkν, hki⟩
      funext j
      rcases hcov j with rfl | ⟨i, rfl⟩
      · rw [decide_eq_false hnone, Bool.not_false, hkν]
      · rw [decide_exists_eq_of_injective hι (fun j ↦ !l j) i, Bool.not_not]
        exact congrFun hki i
  by_cases hkn : k ν = true
  · rw [ite_eq_left_iff.mpr fun h ↦ absurd hkn h, Module.Basis.repr_self, Finsupp.single_apply]
    have hiff : (k = fun j ↦ !decide (∃ i, ι i = j ∧ (!l i) = true)) ↔ k ∘ ι = l :=
      heq.trans (and_iff_right hkn)
    simp only [hiff]
  · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hkn, map_zero, Finsupp.zero_apply]
    exact ite_eq_right_iff.mpr fun hk ↦ absurd (heq.mp hk).1 hkn

/-- Applying `fiberwiseSplit ι` to the image of `fiberwiseMul ι` vanishes whenever `ι` omits at
least one circle `ν`. -/
theorem fiberwiseSplit_fiberwiseMul_of_notMem_range {ι : σ → τ} {ν : τ} (hν : ν ∉ Set.range ι)
    (x : CircleTensor R σ) :
    fiberwiseSplit (R := R) ι (fiberwiseMul (A := fun _ ↦ R[ε]) ι x) = 0 := by
  classical
  have hlin :
      (fiberwiseSplit (R := R) ι).comp
        (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) ι).toLinearMap = 0 := by
    refine (circleBasis R σ).ext fun l ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    refine (circleBasis R σ).ext_elem fun k ↦ ?_
    rw [circleBasis_repr_fiberwiseSplit, map_zero, Finsupp.zero_apply]
    split_ifs with hk
    · rw [fiberwiseMul_circleBasis]
      split_ifs with hl
      · rw [Module.Basis.repr_self, Finsupp.single_apply]
        refine ite_eq_right_iff.mpr fun hfun ↦ ?_
        have h1 := congrFun hfun ν
        have hnone1 : ¬∃ i, ι i = ν ∧ l i = true := fun ⟨i, hi, _⟩ ↦ hν ⟨i, hi⟩
        have hnone2 : ¬∃ i, ι i = ν ∧ (!k i) = true := fun ⟨i, hi, _⟩ ↦ hν ⟨i, hi⟩
        rw [decide_eq_false hnone1, decide_eq_false hnone2, Bool.not_false] at h1
        exact Bool.noConfusion h1
      · simp
    · rfl
  exact LinearMap.congr_fun hlin x

/-- When `ι` is an injection with unique omitted circle `ν`, multiplying by `X` on `ν` between
`fiberwiseMul ι` and `fiberwiseSplit ι` recovers the identity. -/
theorem fiberwiseSplit_circleX_fiberwiseMul {ι : σ → τ} (hι : Function.Injective ι) {ν : τ}
    (hν : ν ∉ Set.range ι) (hcov : ∀ y, y = ν ∨ y ∈ Set.range ι) (x : CircleTensor R σ) :
    fiberwiseSplit (R := R) ι (circleX R ν (fiberwiseMul (A := fun _ ↦ R[ε]) ι x)) = x := by
  classical
  have hlin :
      (fiberwiseSplit (R := R) ι).comp ((circleX R ν).comp
        (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) ι).toLinearMap) = LinearMap.id := by
    refine (circleBasis R σ).ext fun l ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    rw [fiberwiseMul_circleBasis_of_injective hι l, circleX_circleBasis]
    have hnone : ¬∃ i, ι i = ν ∧ l i = true := fun ⟨i, hi, _⟩ ↦ hν ⟨i, hi⟩
    rw [decide_eq_false hnone, ite_eq_right_iff.mpr Bool.noConfusion,
      fiberwiseSplit_circleBasis_of_singleComplement hι hν hcov, Function.update_self,
      ite_eq_left_iff.mpr fun h ↦ absurd rfl h]
    congr 1
    funext i
    have hne : ι i ≠ ν := fun h ↦ hν ⟨i, h⟩
    simp only [Function.comp_apply, Function.update_of_ne hne]
    exact decide_exists_eq_of_injective hι l i
  exact LinearMap.congr_fun hlin x

/-- Completeness of the single-complement decomposition: every tensor over `τ` splits as the sum
of its `1`-component and its `X`-component at the omitted circle `ν`. -/
theorem fiberwiseMul_fiberwiseSplit_circleX_add {ι : σ → τ} (hι : Function.Injective ι) {ν : τ}
    (hν : ν ∉ Set.range ι) (hcov : ∀ y, y = ν ∨ y ∈ Set.range ι) (y : CircleTensor R τ) :
    fiberwiseMul (A := fun _ ↦ R[ε]) ι (fiberwiseSplit (R := R) ι (circleX R ν y)) +
      circleX R ν (fiberwiseMul (A := fun _ ↦ R[ε]) ι (fiberwiseSplit (R := R) ι y)) = y := by
  classical
  have hlin :
      ((fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) ι).toLinearMap.comp
          ((fiberwiseSplit (R := R) ι).comp (circleX R ν)) +
        (circleX R ν).comp ((fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) ι).toLinearMap.comp
          (fiberwiseSplit (R := R) ι))) = LinearMap.id := by
    refine (circleBasis R τ).ext fun k ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.id_apply]
    rw [circleX_circleBasis, fiberwiseSplit_circleBasis_of_singleComplement hι hν hcov]
    cases hk : k ν
    · rw [ite_eq_right_iff.mpr Bool.noConfusion, ite_eq_right_iff.mpr Bool.noConfusion,
        map_zero, map_zero, add_zero,
        fiberwiseSplit_circleBasis_of_singleComplement hι hν hcov, Function.update_self,
        ite_eq_left_iff.mpr fun h ↦ absurd rfl h, fiberwiseMul_circleBasis_of_injective hι]
      congr 1
      funext j
      rcases hcov j with rfl | ⟨i, rfl⟩
      · have hnone : ¬∃ i, ι i = j ∧ Function.update k j true (ι i) = true :=
          fun ⟨i, hi, _⟩ ↦ hν ⟨i, hi⟩
        simp only [Function.comp_apply]
        rw [decide_eq_false hnone, hk]
      · have hne : ι i ≠ ν := fun h ↦ hν ⟨i, h⟩
        simp only [Function.comp_apply]
        rw [decide_exists_eq_of_injective hι (fun i' ↦ Function.update k ν true (ι i')) i,
          Function.update_of_ne hne]
    · rw [ite_eq_left_iff.mpr fun h ↦ absurd rfl h, ite_eq_left_iff.mpr fun h ↦ absurd rfl h,
        map_zero, map_zero, zero_add, fiberwiseMul_circleBasis_of_injective hι, circleX_circleBasis]
      have hnone : ¬∃ i, ι i = ν ∧ k (ι i) = true := fun ⟨i, hi, _⟩ ↦ hν ⟨i, hi⟩
      simp only [Function.comp_apply]
      rw [decide_eq_false hnone, ite_eq_right_iff.mpr Bool.noConfusion]
      congr 1
      funext j
      rcases hcov j with rfl | ⟨i, rfl⟩
      · simp [hk]
      · have hne : ι i ≠ ν := fun h ↦ hν ⟨i, h⟩
        rw [Function.update_of_ne hne, decide_exists_eq_of_injective hι (fun i' ↦ k (ι i')) i]
  exact LinearMap.congr_fun hlin y

section Collapse

variable [DecidableEq σ]

/-- Merging along a left inverse `f` of `ι` cancels `fiberwiseMul ι`. -/
theorem fiberwiseMul_fiberwiseMul_of_leftInverse {ι : σ → τ} {f : τ → σ}
    (hf : ∀ i, f (ι i) = i) (x : CircleTensor R σ) :
    fiberwiseMul (A := fun _ ↦ R[ε]) f (fiberwiseMul (A := fun _ ↦ R[ε]) ι x) = x := by
  rw [← AlgHom.comp_apply, fiberwiseMul_comp, show f ∘ ι = id from funext hf, fiberwiseMul_id]
  rfl

/-- Merging along a left inverse `f` of `ι` sends `X` on `ν` to `X` on `f ν`. -/
theorem fiberwiseMul_circleX_fiberwiseMul_of_leftInverse {ι : σ → τ} {f : τ → σ}
    (hf : ∀ i, f (ι i) = i) (ν : τ) (x : CircleTensor R σ) :
    fiberwiseMul (A := fun _ ↦ R[ε]) f (circleX R ν (fiberwiseMul (A := fun _ ↦ R[ε]) ι x)) =
      circleX R (f ν) x := by
  rw [fiberwiseMul_circleX, fiberwiseMul_fiberwiseMul_of_leftInverse hf]

/-- Splitting along a left inverse `f` of `ι` followed by `fiberwiseSplit ι` is the identity. -/
theorem fiberwiseSplit_fiberwiseSplit_of_leftInverse {ι : σ → τ} {f : τ → σ}
    (hf : ∀ i, f (ι i) = i) (x : CircleTensor R σ) :
    fiberwiseSplit (R := R) ι (fiberwiseSplit (R := R) f x) = x := by
  rw [← LinearMap.comp_apply, fiberwiseSplit_comp, show f ∘ ι = id from funext hf,
    fiberwiseSplit_id]
  rfl

/-- Splitting along a left inverse `f` of `ι`, multiplying by `X` on `ν`, and then applying
`fiberwiseSplit ι` gives multiplication by `X` on `f ν`. -/
theorem fiberwiseSplit_circleX_fiberwiseSplit_of_leftInverse {ι : σ → τ} {f : τ → σ}
    (hf : ∀ i, f (ι i) = i) (ν : τ) (x : CircleTensor R σ) :
    fiberwiseSplit (R := R) ι (circleX R ν (fiberwiseSplit (R := R) f x)) =
      circleX R (f ν) x := by
  rw [← fiberwiseSplit_circleX, fiberwiseSplit_fiberwiseSplit_of_leftInverse hf]

end Collapse

section Naturality

variable {σ' τ' : Type*} [Fintype σ'] [DecidableEq σ'] [Fintype τ'] [DecidableEq τ']

/-- `fiberwiseSplit` commutes with a merge that fixes the omitted circle. -/
theorem fiberwiseSplit_fiberwiseMul_of_singleComplement
    {ι : σ → τ} (hι : Function.Injective ι) {ν : τ} (hν : ν ∉ Set.range ι)
    (hcov : ∀ y, y = ν ∨ y ∈ Set.range ι)
    {ι' : σ' → τ'} (hι' : Function.Injective ι') {ν' : τ'} (hν' : ν' ∉ Set.range ι')
    (hcov' : ∀ y, y = ν' ∨ y ∈ Set.range ι')
    {g : σ → σ'} {g' : τ → τ'} (hιg : ∀ i, g' (ι i) = ι' (g i)) (hνg : g' ν = ν')
    (y : CircleTensor R τ) :
    fiberwiseSplit (R := R) ι' (fiberwiseMul (A := fun _ ↦ R[ε]) g' y) =
      fiberwiseMul (A := fun _ ↦ R[ε]) g (fiberwiseSplit (R := R) ι y) := by
  have hcomp : g' ∘ ι = ι' ∘ g := funext hιg
  conv_lhs => rw [← fiberwiseMul_fiberwiseSplit_circleX_add hι hν hcov y]
  rw [map_add, map_add, ← AlgHom.comp_apply, fiberwiseMul_comp, hcomp, ← fiberwiseMul_comp,
    AlgHom.comp_apply, fiberwiseSplit_fiberwiseMul_of_notMem_range hν', zero_add,
    fiberwiseMul_circleX, hνg, ← AlgHom.comp_apply, fiberwiseMul_comp, hcomp,
    ← fiberwiseMul_comp, AlgHom.comp_apply,
    fiberwiseSplit_circleX_fiberwiseMul hι' hν' hcov']

/-- `fiberwiseSplit ∘ circleX` commutes with a merge that fixes the omitted circle. -/
theorem fiberwiseSplit_circleX_fiberwiseMul_of_singleComplement
    {ι : σ → τ} (hι : Function.Injective ι) {ν : τ} (hν : ν ∉ Set.range ι)
    (hcov : ∀ y, y = ν ∨ y ∈ Set.range ι)
    {ι' : σ' → τ'} (hι' : Function.Injective ι') {ν' : τ'} (hν' : ν' ∉ Set.range ι')
    (hcov' : ∀ y, y = ν' ∨ y ∈ Set.range ι')
    {g : σ → σ'} {g' : τ → τ'} (hιg : ∀ i, g' (ι i) = ι' (g i)) (hνg : g' ν = ν')
    (y : CircleTensor R τ) :
    fiberwiseSplit (R := R) ι' (circleX R ν' (fiberwiseMul (A := fun _ ↦ R[ε]) g' y)) =
      fiberwiseMul (A := fun _ ↦ R[ε]) g (fiberwiseSplit (R := R) ι (circleX R ν y)) := by
  rw [← hνg, ← fiberwiseMul_circleX,
    fiberwiseSplit_fiberwiseMul_of_singleComplement hι hν hcov hι' hν' hcov' hιg hνg]

/-- `fiberwiseMul ι` commutes with a split that fixes the omitted circle. -/
theorem fiberwiseSplit_fiberwiseMul_comm_of_singleComplement
    {ι : σ → τ} (hι : Function.Injective ι) {ν : τ} (hν : ν ∉ Set.range ι)
    (hcov : ∀ y, y = ν ∨ y ∈ Set.range ι)
    {ι' : σ' → τ'} (hι' : Function.Injective ι') {ν' : τ'} (hν' : ν' ∉ Set.range ι')
    (hcov' : ∀ y, y = ν' ∨ y ∈ Set.range ι')
    {g : σ → σ'} {g' : τ → τ'} (hιg : ∀ i, g' (ι i) = ι' (g i)) (hνg : g' ν = ν')
    (x : CircleTensor R σ') :
    fiberwiseSplit (R := R) g' (fiberwiseMul (A := fun _ ↦ R[ε]) ι' x) =
      fiberwiseMul (A := fun _ ↦ R[ε]) ι (fiberwiseSplit (R := R) g x) := by
  have hcomp : g' ∘ ι = ι' ∘ g := funext hιg
  rw [← fiberwiseMul_fiberwiseSplit_circleX_add hι hν hcov
    (fiberwiseSplit (R := R) g' (fiberwiseMul (A := fun _ ↦ R[ε]) ι' x))]
  have h1 : fiberwiseSplit (R := R) ι (fiberwiseSplit (R := R) g'
      (fiberwiseMul (A := fun _ ↦ R[ε]) ι' x)) = 0 := by
    rw [← LinearMap.comp_apply, fiberwiseSplit_comp, hcomp, ← fiberwiseSplit_comp,
      LinearMap.comp_apply, fiberwiseSplit_fiberwiseMul_of_notMem_range hν', map_zero]
  have h2 : fiberwiseSplit (R := R) ι (circleX R ν (fiberwiseSplit (R := R) g'
      (fiberwiseMul (A := fun _ ↦ R[ε]) ι' x))) = fiberwiseSplit (R := R) g x := by
    rw [← fiberwiseSplit_circleX, hνg, ← LinearMap.comp_apply, fiberwiseSplit_comp, hcomp,
      ← fiberwiseSplit_comp, LinearMap.comp_apply,
      fiberwiseSplit_circleX_fiberwiseMul hι' hν' hcov']
  rw [h1, h2, map_zero, map_zero, add_zero]

/-- `circleX ν ∘ fiberwiseMul ι` commutes with a split that fixes the omitted circle. -/
theorem fiberwiseSplit_circleX_fiberwiseMul_comm_of_singleComplement
    {ι : σ → τ} (hι : Function.Injective ι) {ν : τ} (hν : ν ∉ Set.range ι)
    (hcov : ∀ y, y = ν ∨ y ∈ Set.range ι)
    {ι' : σ' → τ'} (hι' : Function.Injective ι') {ν' : τ'} (hν' : ν' ∉ Set.range ι')
    (hcov' : ∀ y, y = ν' ∨ y ∈ Set.range ι')
    {g : σ → σ'} {g' : τ → τ'} (hιg : ∀ i, g' (ι i) = ι' (g i)) (hνg : g' ν = ν')
    (x : CircleTensor R σ') :
    fiberwiseSplit (R := R) g' (circleX R ν' (fiberwiseMul (A := fun _ ↦ R[ε]) ι' x)) =
      circleX R ν (fiberwiseMul (A := fun _ ↦ R[ε]) ι (fiberwiseSplit (R := R) g x)) := by
  rw [← hνg, fiberwiseSplit_circleX,
    fiberwiseSplit_fiberwiseMul_comm_of_singleComplement hι hν hcov hι' hν' hcov' hιg hνg]

end Naturality

end Semiring

end TauCeti.Khovanov

/-! ### Circle splitting for `PDCode.adjoinCircle` -/

namespace TauCeti.PDCode

universe u

section Circles

variable {n : ℕ} (D : PDCode n)

/-- The crossing-bearing circles of `D.adjoinCircle` are canonically identified with those of `D`,
sending the circle of each half-edge to the circle of the same half-edge. -/
def adjoinCircleCrossingCircleEquiv (s : Fin n → Bool) :
    D.CrossingCircle s ≃ D.adjoinCircle.CrossingCircle s :=
  Quotient.congrRight fun _ _ ↦ by
    have hstep : D.adjoinCircle.CircleStep s = D.CircleStep s := by
      ext x y
      simp only [CircleStep, adjoinCircle_edgePair, smoothingTurn_adjoinCircle,
        smoothingChoice_adjoinCircle]
    rw [show D.adjoinCircle.CircleStep s = D.CircleStep s from hstep]

@[simp]
theorem adjoinCircleCrossingCircleEquiv_mk (s : Fin n → Bool) (x : Fin (4 * n)) :
    D.adjoinCircleCrossingCircleEquiv s ⟦x⟧ = ⟦x⟧ := (rfl)

@[simp]
theorem adjoinCircleCrossingCircleEquiv_symm_mk (s : Fin n → Bool) (x : Fin (4 * n)) :
    (D.adjoinCircleCrossingCircleEquiv s).symm ⟦x⟧ = ⟦x⟧ := (rfl)

/-- The inclusion of the resolved circles of `D` into those of `D.adjoinCircle`, omitting the newly
adjoined crossing-free circle. -/
def adjoinCircleIncl (s : Fin n → Bool) :
    D.ResolvedCircle s → D.adjoinCircle.ResolvedCircle s :=
  Sum.map (D.adjoinCircleCrossingCircleEquiv s)
    (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm ∘ Fin.castSucc)

/-- The newly adjoined crossing-free circle in a smoothing of `D.adjoinCircle`. -/
def adjoinCircleNew (s : Fin n → Bool) : D.adjoinCircle.ResolvedCircle s :=
  .inr (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm
    (Fin.last D.crossinglessComponentCount))

/-- Collapse the newly adjoined circle of `D.adjoinCircle` onto the resolved circle through a mark
`p` of `D`, leaving every circle of `D` fixed. -/
def adjoinCircleCollapse (p : D.Mark) (s : Fin n → Bool) :
    D.adjoinCircle.ResolvedCircle s → D.ResolvedCircle s :=
  Sum.elim (fun C ↦ .inl ((D.adjoinCircleCrossingCircleEquiv s).symm C))
    (fun i ↦ Fin.lastCases (p.resolvedCircle s) Sum.inr
      (Fin.cast (adjoinCircle_crossinglessComponentCount D) i))

@[simp]
theorem adjoinCircleIncl_inl (s : Fin n → Bool) (C : D.CrossingCircle s) :
    D.adjoinCircleIncl s (.inl C) = .inl (D.adjoinCircleCrossingCircleEquiv s C) := (rfl)

@[simp]
theorem adjoinCircleIncl_inr (s : Fin n → Bool) (i : Fin D.crossinglessComponentCount) :
    D.adjoinCircleIncl s (.inr i) =
      .inr (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm i.castSucc) := (rfl)

/-- Unfolding lemma for `adjoinCircleNew` as the last crossing-free component of
`D.adjoinCircle`. -/
theorem adjoinCircleNew_eq (s : Fin n → Bool) :
    D.adjoinCircleNew s =
      .inr (Fin.cast (adjoinCircle_crossinglessComponentCount D).symm
        (Fin.last D.crossinglessComponentCount)) := (rfl)

/-- The inclusion of resolved circles of `D` into those of `D.adjoinCircle` is injective. -/
theorem adjoinCircleIncl_injective (s : Fin n → Bool) :
    Function.Injective (D.adjoinCircleIncl s) :=
  Sum.map_injective.mpr
    ⟨(D.adjoinCircleCrossingCircleEquiv s).injective,
      (Fin.cast_injective _).comp (Fin.castSucc_injective _)⟩

/-- The newly adjoined circle is omitted from the range of `D.adjoinCircleIncl s`. -/
theorem adjoinCircleNew_notMem_range_adjoinCircleIncl (s : Fin n → Bool) :
    D.adjoinCircleNew s ∉ Set.range (D.adjoinCircleIncl s) := by
  rintro ⟨C | i, h⟩
  · exact Sum.inl_ne_inr h
  · simp only [adjoinCircleIncl_inr, adjoinCircleNew, Sum.inr.injEq] at h
    exact Fin.castSucc_ne_last i (Fin.cast_injective _ h)

/-- Every resolved circle of `D.adjoinCircle` is either the newly adjoined circle or lies in the
range of `D.adjoinCircleIncl s`. -/
theorem eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl (s : Fin n → Bool)
    (C : D.adjoinCircle.ResolvedCircle s) :
    C = D.adjoinCircleNew s ∨ C ∈ Set.range (D.adjoinCircleIncl s) := by
  rcases C with C | i
  · exact Or.inr ⟨.inl ((D.adjoinCircleCrossingCircleEquiv s).symm C), by simp⟩
  · obtain ⟨k, rfl⟩ :
        ∃ k : Fin (D.crossinglessComponentCount + 1),
          Fin.cast (adjoinCircle_crossinglessComponentCount D).symm k = i :=
      ⟨Fin.cast (adjoinCircle_crossinglessComponentCount D) i, by simp⟩
    refine Fin.lastCases (Or.inl rfl) (fun j ↦ Or.inr ⟨.inr j, rfl⟩) k

@[simp]
theorem adjoinCircleCollapse_inl (p : D.Mark) (s : Fin n → Bool)
    (C : D.adjoinCircle.CrossingCircle s) :
    D.adjoinCircleCollapse p s (.inl C) = .inl ((D.adjoinCircleCrossingCircleEquiv s).symm C) :=
  (rfl)

@[simp]
theorem adjoinCircleCollapse_adjoinCircleIncl (p : D.Mark) (s : Fin n → Bool)
    (C : D.ResolvedCircle s) :
    D.adjoinCircleCollapse p s (D.adjoinCircleIncl s C) = C := by
  rcases C with C | i <;> simp [adjoinCircleCollapse]

@[simp]
theorem adjoinCircleCollapse_adjoinCircleNew (p : D.Mark) (s : Fin n → Bool) :
    D.adjoinCircleCollapse p s (D.adjoinCircleNew s) = p.resolvedCircle s := by
  simp [adjoinCircleCollapse, adjoinCircleNew]

/-- Adjoining a crossing-free circle does not change the number of circles incident to any
crossing. -/
@[simp]
theorem card_circlesAt_adjoinCircle (s : Fin n → Bool) (c : Fin n) :
    #(D.adjoinCircle.circlesAt s c) = #(D.circlesAt s c) := by
  have himg : D.adjoinCircle.circlesAt s c =
      (D.circlesAt s c).map (D.adjoinCircleCrossingCircleEquiv s).toEmbedding := by
    ext C
    simp only [circlesAt_eq_pair, Finset.mem_insert, Finset.mem_singleton, Finset.map_insert,
      Finset.map_singleton, Equiv.coe_toEmbedding, adjoinCircleCrossingCircleEquiv_mk]
    simp only [crossing_apply, adjoinCircle_halfEdge]
  rw [himg, Finset.card_map]

/-- The saddle correspondence of `D.adjoinCircle` agrees with that of `D` on the circles of `D`. -/
theorem saddleResolvedCircleMap_adjoinCircleIncl {s t : Fin n → Bool} {c : Fin n}
    (hst : ∀ j, j ≠ c → s j = t j) (ht : #(D.circlesAt t c) = 1)
    (ht' : #(D.adjoinCircle.circlesAt t c) = 1) (C : D.ResolvedCircle s) :
    D.adjoinCircle.saddleResolvedCircleMap hst ht' (D.adjoinCircleIncl s C) =
      D.adjoinCircleIncl t (D.saddleResolvedCircleMap hst ht C) := by
  rcases C with C | i
  · induction C using Quotient.ind
    simp [adjoinCircleIncl]
  · simp [adjoinCircleIncl]

/-- The saddle correspondence of `D.adjoinCircle` fixes the newly adjoined circle. -/
@[simp]
theorem saddleResolvedCircleMap_adjoinCircleNew {s t : Fin n → Bool} {c : Fin n}
    (hst : ∀ j, j ≠ c → s j = t j) (ht' : #(D.adjoinCircle.circlesAt t c) = 1) :
    D.adjoinCircle.saddleResolvedCircleMap hst ht' (D.adjoinCircleNew s) = D.adjoinCircleNew t := by
  simp [adjoinCircleNew]

/-- Adjoining a crossing-free circle increases the number of resolved circles in every state
by `1`. -/
theorem card_resolvedCircle_adjoinCircle (s : Fin n → Bool) :
    Fintype.card (D.adjoinCircle.ResolvedCircle s) = Fintype.card (D.ResolvedCircle s) + 1 := by
  rw [card_resolvedCircle, card_resolvedCircle, stateLoopCount_adjoinCircle]

end Circles

/-! ### Cube-level splitting for `PDCode.adjoinCircle` -/

section Cube

variable {n : ℕ} (D : PDCode n) (hD : D.IsPlanar) (hD' : D.adjoinCircle.IsPlanar)
  (R : Type u) [CommRing R]

private theorem adjoinCircleBirthOne_mem_range (j : ℤ) (S : Finset (Fin n))
    (x : (D.resolutionCube hD R (j - 1)).obj S) :
    (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) (D.adjoinCircleIncl (cubeState S))).toLinearMap
        ((D.resolutionCubeι hD R (j - 1) S).hom x) ∈
      LinearMap.range (D.adjoinCircle.resolutionCubeι hD' R j S).hom := by
  have hx : (D.resolutionCubeι hD R (j - 1) S).hom x ∈
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece ((j - 1) - #S) := by
    rw [← range_resolutionCubeι]
    exact LinearMap.mem_range_self _ x
  rw [range_resolutionCubeι]
  have hdeg := (Khovanov.isHomogeneous_fiberwiseMul (R := R)
    (D.adjoinCircleIncl (cubeState S))).map_mem hx
  convert hdeg using 2
  have hc := D.card_resolvedCircle_adjoinCircle (cubeState S)
  omega

private theorem adjoinCircleBirthX_mem_range (j : ℤ) (S : Finset (Fin n))
    (x : (D.resolutionCube hD R (j + 1)).obj S) :
    Khovanov.circleX R (D.adjoinCircleNew (cubeState S))
        ((fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) (D.adjoinCircleIncl (cubeState S))).toLinearMap
          ((D.resolutionCubeι hD R (j + 1) S).hom x)) ∈
      LinearMap.range (D.adjoinCircle.resolutionCubeι hD' R j S).hom := by
  have hx : (D.resolutionCubeι hD R (j + 1) S).hom x ∈
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece ((j + 1) - #S) := by
    rw [← range_resolutionCubeι]
    exact LinearMap.mem_range_self _ x
  rw [range_resolutionCubeι]
  have h1 := (Khovanov.isHomogeneous_fiberwiseMul (R := R)
    (D.adjoinCircleIncl (cubeState S))).map_mem hx
  have h2 := (Khovanov.isHomogeneous_circleX (R := R)
    (D.adjoinCircleNew (cubeState S))).map_mem h1
  convert h2 using 2
  have hc := D.card_resolvedCircle_adjoinCircle (cubeState S)
  omega

private theorem adjoinCircleDeathOne_mem_range (j : ℤ) (S : Finset (Fin n))
    (y : (D.adjoinCircle.resolutionCube hD' R j).obj S) :
    Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl (cubeState S))
        (Khovanov.circleX R (D.adjoinCircleNew (cubeState S))
          ((D.adjoinCircle.resolutionCubeι hD' R j S).hom y)) ∈
      LinearMap.range (D.resolutionCubeι hD R (j - 1) S).hom := by
  have hy : (D.adjoinCircle.resolutionCubeι hD' R j S).hom y ∈
      (Khovanov.circleQuantumGrading R (D.adjoinCircle.ResolvedCircle (cubeState S))).piece
        (j - #S) := by
    rw [← range_resolutionCubeι]
    exact LinearMap.mem_range_self _ y
  rw [range_resolutionCubeι]
  have h1 := (Khovanov.isHomogeneous_circleX (R := R)
    (D.adjoinCircleNew (cubeState S))).map_mem hy
  have h2 := (Khovanov.isHomogeneous_fiberwiseSplit (R := R)
    (D.adjoinCircleIncl (cubeState S))).map_mem h1
  convert h2 using 2
  have hc := D.card_resolvedCircle_adjoinCircle (cubeState S)
  omega

private theorem adjoinCircleDeathX_mem_range (j : ℤ) (S : Finset (Fin n))
    (y : (D.adjoinCircle.resolutionCube hD' R j).obj S) :
    Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl (cubeState S))
        ((D.adjoinCircle.resolutionCubeι hD' R j S).hom y) ∈
      LinearMap.range (D.resolutionCubeι hD R (j + 1) S).hom := by
  have hy : (D.adjoinCircle.resolutionCubeι hD' R j S).hom y ∈
      (Khovanov.circleQuantumGrading R (D.adjoinCircle.ResolvedCircle (cubeState S))).piece
        (j - #S) := by
    rw [← range_resolutionCubeι]
    exact LinearMap.mem_range_self _ y
  rw [range_resolutionCubeι]
  have h1 := (Khovanov.isHomogeneous_fiberwiseSplit (R := R)
    (D.adjoinCircleIncl (cubeState S))).map_mem hy
  convert h1 using 2
  have hc := D.card_resolvedCircle_adjoinCircle (cubeState S)
  omega

private def adjoinCircleCubeInlApp (j : ℤ) (S : Finset (Fin n)) :
    (D.resolutionCube hD R (j - 1)).obj S ⟶ (D.adjoinCircle.resolutionCube hD' R j).obj S :=
  ModuleCat.ofHom <|
    (LinearEquiv.ofInjective _
        (D.adjoinCircle.resolutionCubeι_injective hD' R j S)).symm.toLinearMap ∘ₗ
      ((fiberwiseMul (R := R) (A := fun _ ↦ R[ε])
          (D.adjoinCircleIncl (cubeState S))).toLinearMap ∘ₗ
        (D.resolutionCubeι hD R (j - 1) S).hom).codRestrict _
        (D.adjoinCircleBirthOne_mem_range hD hD' R j S)

private def adjoinCircleCubeInrApp (j : ℤ) (S : Finset (Fin n)) :
    (D.resolutionCube hD R (j + 1)).obj S ⟶ (D.adjoinCircle.resolutionCube hD' R j).obj S :=
  ModuleCat.ofHom <|
    (LinearEquiv.ofInjective _
        (D.adjoinCircle.resolutionCubeι_injective hD' R j S)).symm.toLinearMap ∘ₗ
      ((Khovanov.circleX R (D.adjoinCircleNew (cubeState S)) ∘ₗ
          (fiberwiseMul (R := R) (A := fun _ ↦ R[ε])
            (D.adjoinCircleIncl (cubeState S))).toLinearMap) ∘ₗ
        (D.resolutionCubeι hD R (j + 1) S).hom).codRestrict _
        (D.adjoinCircleBirthX_mem_range hD hD' R j S)

private def adjoinCircleCubeFstApp (j : ℤ) (S : Finset (Fin n)) :
    (D.adjoinCircle.resolutionCube hD' R j).obj S ⟶ (D.resolutionCube hD R (j - 1)).obj S :=
  ModuleCat.ofHom <|
    (LinearEquiv.ofInjective _
        (D.resolutionCubeι_injective hD R (j - 1) S)).symm.toLinearMap ∘ₗ
      ((Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl (cubeState S)) ∘ₗ
          Khovanov.circleX R (D.adjoinCircleNew (cubeState S))) ∘ₗ
        (D.adjoinCircle.resolutionCubeι hD' R j S).hom).codRestrict _
        (D.adjoinCircleDeathOne_mem_range hD hD' R j S)

private def adjoinCircleCubeSndApp (j : ℤ) (S : Finset (Fin n)) :
    (D.adjoinCircle.resolutionCube hD' R j).obj S ⟶ (D.resolutionCube hD R (j + 1)).obj S :=
  ModuleCat.ofHom <|
    (LinearEquiv.ofInjective _
        (D.resolutionCubeι_injective hD R (j + 1) S)).symm.toLinearMap ∘ₗ
      (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl (cubeState S)) ∘ₗ
        (D.adjoinCircle.resolutionCubeι hD' R j S).hom).codRestrict _
        (D.adjoinCircleDeathX_mem_range hD hD' R j S)

@[reassoc]
private theorem adjoinCircleCubeInlApp_comp_resolutionCubeι (j : ℤ) (S : Finset (Fin n)) :
    D.adjoinCircleCubeInlApp hD hD' R j S ≫ D.adjoinCircle.resolutionCubeι hD' R j S =
      D.resolutionCubeι hD R (j - 1) S ≫
        ModuleCat.ofHom
          (fiberwiseMul (R := R) (A := fun _ ↦ R[ε])
            (D.adjoinCircleIncl (cubeState S))).toLinearMap := by
  ext x
  simp [adjoinCircleCubeInlApp]

@[reassoc]
private theorem adjoinCircleCubeInrApp_comp_resolutionCubeι (j : ℤ) (S : Finset (Fin n)) :
    D.adjoinCircleCubeInrApp hD hD' R j S ≫ D.adjoinCircle.resolutionCubeι hD' R j S =
      D.resolutionCubeι hD R (j + 1) S ≫
        ModuleCat.ofHom (Khovanov.circleX R (D.adjoinCircleNew (cubeState S)) ∘ₗ
          (fiberwiseMul (R := R) (A := fun _ ↦ R[ε])
            (D.adjoinCircleIncl (cubeState S))).toLinearMap) := by
  ext x
  simp [adjoinCircleCubeInrApp]

@[reassoc]
private theorem adjoinCircleCubeFstApp_comp_resolutionCubeι (j : ℤ) (S : Finset (Fin n)) :
    D.adjoinCircleCubeFstApp hD hD' R j S ≫ D.resolutionCubeι hD R (j - 1) S =
      D.adjoinCircle.resolutionCubeι hD' R j S ≫
        ModuleCat.ofHom (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl (cubeState S)) ∘ₗ
          Khovanov.circleX R (D.adjoinCircleNew (cubeState S))) := by
  ext x
  simp [adjoinCircleCubeFstApp]

@[reassoc]
private theorem adjoinCircleCubeSndApp_comp_resolutionCubeι (j : ℤ) (S : Finset (Fin n)) :
    D.adjoinCircleCubeSndApp hD hD' R j S ≫ D.resolutionCubeι hD R (j + 1) S =
      D.adjoinCircle.resolutionCubeι hD' R j S ≫
        ModuleCat.ofHom (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl (cubeState S))) := by
  ext x
  simp [adjoinCircleCubeSndApp]

private theorem resolutionEdgeMap_adjoinCircleIncl {s t : Fin n → Bool} {c : Fin n}
    (hst : ∀ i, i ≠ c → s i = t i) (hc : s c ≠ t c)
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
    (h' : #(D.adjoinCircle.circlesAt s c) = 2 ∨ #(D.adjoinCircle.circlesAt t c) = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.adjoinCircle.resolutionEdgeMap hst hc h' R
        (fiberwiseMul (A := fun _ ↦ R[ε]) (D.adjoinCircleIncl s) x) =
      fiberwiseMul (A := fun _ ↦ R[ε]) (D.adjoinCircleIncl t)
        (D.resolutionEdgeMap hst hc h R x) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · have hs' : #(D.adjoinCircle.circlesAt s c) = 2 := by simpa using hs
    rw [D.adjoinCircle.resolutionEdgeMap_eq_resolutionMergeMap hst hc h' R hs',
      D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, resolutionMergeMap_def, resolutionMergeMap_def,
      ← AlgHom.comp_apply, fiberwiseMul_comp, ← AlgHom.comp_apply, fiberwiseMul_comp]
    congr 2
    funext C
    exact D.saddleResolvedCircleMap_adjoinCircleIncl hst _ _ C
  · have ht := h.resolve_left hs
    have ht' : #(D.adjoinCircle.circlesAt t c) = 2 := by simpa using ht
    rw [D.adjoinCircle.resolutionEdgeMap_eq_resolutionSplitMap hst hc h' R ht',
      D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R ht,
      resolutionSplitMap_def, resolutionSplitMap_def]
    exact Khovanov.fiberwiseSplit_fiberwiseMul_comm_of_singleComplement
      (D.adjoinCircleIncl_injective t) (D.adjoinCircleNew_notMem_range_adjoinCircleIncl t)
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl t)
      (D.adjoinCircleIncl_injective s) (D.adjoinCircleNew_notMem_range_adjoinCircleIncl s)
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl s)
      (fun C ↦ D.saddleResolvedCircleMap_adjoinCircleIncl (fun i hi ↦ (hst i hi).symm) _ _ C)
      (D.saddleResolvedCircleMap_adjoinCircleNew (fun i hi ↦ (hst i hi).symm) _) x

private theorem resolutionEdgeMap_circleX_adjoinCircleIncl {s t : Fin n → Bool} {c : Fin n}
    (hst : ∀ i, i ≠ c → s i = t i) (hc : s c ≠ t c)
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
    (h' : #(D.adjoinCircle.circlesAt s c) = 2 ∨ #(D.adjoinCircle.circlesAt t c) = 2)
    (x : Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    D.adjoinCircle.resolutionEdgeMap hst hc h' R
        (Khovanov.circleX R (D.adjoinCircleNew s)
          (fiberwiseMul (A := fun _ ↦ R[ε]) (D.adjoinCircleIncl s) x)) =
      Khovanov.circleX R (D.adjoinCircleNew t)
        (fiberwiseMul (A := fun _ ↦ R[ε]) (D.adjoinCircleIncl t)
          (D.resolutionEdgeMap hst hc h R x)) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · have hs' : #(D.adjoinCircle.circlesAt s c) = 2 := by simpa using hs
    rw [D.adjoinCircle.resolutionEdgeMap_eq_resolutionMergeMap hst hc h' R hs',
      D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, resolutionMergeMap_def, resolutionMergeMap_def,
      Khovanov.fiberwiseMul_circleX, saddleResolvedCircleMap_adjoinCircleNew,
      ← AlgHom.comp_apply, fiberwiseMul_comp, ← AlgHom.comp_apply, fiberwiseMul_comp]
    congr 3
    funext C
    exact D.saddleResolvedCircleMap_adjoinCircleIncl hst _ _ C
  · have ht := h.resolve_left hs
    have ht' : #(D.adjoinCircle.circlesAt t c) = 2 := by simpa using ht
    rw [D.adjoinCircle.resolutionEdgeMap_eq_resolutionSplitMap hst hc h' R ht',
      D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R ht,
      resolutionSplitMap_def, resolutionSplitMap_def]
    exact Khovanov.fiberwiseSplit_circleX_fiberwiseMul_comm_of_singleComplement
      (D.adjoinCircleIncl_injective t) (D.adjoinCircleNew_notMem_range_adjoinCircleIncl t)
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl t)
      (D.adjoinCircleIncl_injective s) (D.adjoinCircleNew_notMem_range_adjoinCircleIncl s)
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl s)
      (fun C ↦ D.saddleResolvedCircleMap_adjoinCircleIncl (fun i hi ↦ (hst i hi).symm) _ _ C)
      (D.saddleResolvedCircleMap_adjoinCircleNew (fun i hi ↦ (hst i hi).symm) _) x

private theorem fiberwiseSplit_resolutionEdgeMap_adjoinCircle {s t : Fin n → Bool} {c : Fin n}
    (hst : ∀ i, i ≠ c → s i = t i) (hc : s c ≠ t c)
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
    (h' : #(D.adjoinCircle.circlesAt s c) = 2 ∨ #(D.adjoinCircle.circlesAt t c) = 2)
    (y : Khovanov.CircleTensor R (D.adjoinCircle.ResolvedCircle s)) :
    Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl t)
        (D.adjoinCircle.resolutionEdgeMap hst hc h' R y) =
      D.resolutionEdgeMap hst hc h R
        (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl s) y) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · have hs' : #(D.adjoinCircle.circlesAt s c) = 2 := by simpa using hs
    rw [D.adjoinCircle.resolutionEdgeMap_eq_resolutionMergeMap hst hc h' R hs',
      D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, resolutionMergeMap_def, resolutionMergeMap_def]
    exact Khovanov.fiberwiseSplit_fiberwiseMul_of_singleComplement
      (D.adjoinCircleIncl_injective s) (D.adjoinCircleNew_notMem_range_adjoinCircleIncl s)
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl s)
      (D.adjoinCircleIncl_injective t) (D.adjoinCircleNew_notMem_range_adjoinCircleIncl t)
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl t)
      (fun C ↦ D.saddleResolvedCircleMap_adjoinCircleIncl hst _ _ C)
      (D.saddleResolvedCircleMap_adjoinCircleNew hst _) y
  · have ht := h.resolve_left hs
    have ht' : #(D.adjoinCircle.circlesAt t c) = 2 := by simpa using ht
    rw [D.adjoinCircle.resolutionEdgeMap_eq_resolutionSplitMap hst hc h' R ht',
      D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R ht,
      resolutionSplitMap_def, resolutionSplitMap_def,
      ← LinearMap.comp_apply, Khovanov.fiberwiseSplit_comp,
      ← LinearMap.comp_apply, Khovanov.fiberwiseSplit_comp]
    congr 2
    funext C
    exact D.saddleResolvedCircleMap_adjoinCircleIncl (fun i hi ↦ (hst i hi).symm) _ _ C

private theorem fiberwiseSplit_circleX_resolutionEdgeMap_adjoinCircle {s t : Fin n → Bool}
    {c : Fin n} (hst : ∀ i, i ≠ c → s i = t i) (hc : s c ≠ t c)
    (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
    (h' : #(D.adjoinCircle.circlesAt s c) = 2 ∨ #(D.adjoinCircle.circlesAt t c) = 2)
    (y : Khovanov.CircleTensor R (D.adjoinCircle.ResolvedCircle s)) :
    Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl t)
        (Khovanov.circleX R (D.adjoinCircleNew t)
          (D.adjoinCircle.resolutionEdgeMap hst hc h' R y)) =
      D.resolutionEdgeMap hst hc h R
        (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl s)
          (Khovanov.circleX R (D.adjoinCircleNew s) y)) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · have hs' : #(D.adjoinCircle.circlesAt s c) = 2 := by simpa using hs
    rw [D.adjoinCircle.resolutionEdgeMap_eq_resolutionMergeMap hst hc h' R hs',
      D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, resolutionMergeMap_def, resolutionMergeMap_def]
    exact Khovanov.fiberwiseSplit_circleX_fiberwiseMul_of_singleComplement
      (D.adjoinCircleIncl_injective s) (D.adjoinCircleNew_notMem_range_adjoinCircleIncl s)
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl s)
      (D.adjoinCircleIncl_injective t) (D.adjoinCircleNew_notMem_range_adjoinCircleIncl t)
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl t)
      (fun C ↦ D.saddleResolvedCircleMap_adjoinCircleIncl hst _ _ C)
      (D.saddleResolvedCircleMap_adjoinCircleNew hst _) y
  · have ht := h.resolve_left hs
    have ht' : #(D.adjoinCircle.circlesAt t c) = 2 := by simpa using ht
    rw [D.adjoinCircle.resolutionEdgeMap_eq_resolutionSplitMap hst hc h' R ht',
      D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R ht,
      resolutionSplitMap_def, resolutionSplitMap_def,
      ← Khovanov.fiberwiseSplit_circleX,
      D.saddleResolvedCircleMap_adjoinCircleNew (fun i hi ↦ (hst i hi).symm) _]
    have hs1 : #(D.circlesAt s c) = 1 :=
      D.card_circlesAt_eq_one_of_card_circlesAt_eq_two (fun i hi ↦ (hst i hi).symm) hc.symm ht
    have hs1' : #(D.adjoinCircle.circlesAt s c) = 1 :=
      D.adjoinCircle.card_circlesAt_eq_one_of_card_circlesAt_eq_two
        (fun i hi ↦ (hst i hi).symm) hc.symm ht'
    have hcomp :
        (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl t)).comp
            (Khovanov.fiberwiseSplit (R := R)
              (D.adjoinCircle.saddleResolvedCircleMap (fun i hi ↦ (hst i hi).symm) hs1')) =
          (Khovanov.fiberwiseSplit (R := R)
            (D.saddleResolvedCircleMap (fun i hi ↦ (hst i hi).symm) hs1)).comp
              (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl s)) := by
      rw [Khovanov.fiberwiseSplit_comp, Khovanov.fiberwiseSplit_comp]
      congr 1
      funext C
      exact D.saddleResolvedCircleMap_adjoinCircleIncl (fun i hi ↦ (hst i hi).symm) hs1 hs1' C
    exact LinearMap.congr_fun hcomp (Khovanov.circleX R (D.adjoinCircleNew s) y)

/-- The first inclusion `D(j - 1) ⟶ D.adjoinCircle(j)` on cubes of resolutions, placing `1` on
the adjoined circle. -/
def adjoinCircleCubeInl (j : ℤ) :
    D.resolutionCube hD R (j - 1) ⟶ D.adjoinCircle.resolutionCube hD' R j :=
  NatTrans.ofCubeEdges (D.adjoinCircleCubeInlApp hD hD' R j) fun S T h ↦ by
    obtain ⟨a, ha, rfl⟩ := h.exists_finset_insert
    have hst := cubeState_eq_of_covBy h ha (mem_insert_self a S)
    have hc := cubeState_ne_of_notMem_of_mem ha (mem_insert_self a S)
    rw [← cancel_mono (D.adjoinCircle.resolutionCubeι hD' R j (insert a S)), Category.assoc,
      Category.assoc, adjoinCircleCubeInlApp_comp_resolutionCubeι,
      D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι_assoc hD R (j - 1) ha,
      D.adjoinCircle.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD' R j ha,
      adjoinCircleCubeInlApp_comp_resolutionCubeι_assoc]
    ext x
    exact (D.resolutionEdgeMap_adjoinCircleIncl R hst hc _ _ _).symm

/-- The second inclusion `D(j + 1) ⟶ D.adjoinCircle(j)` on cubes of resolutions, placing `X` on
the adjoined circle. -/
def adjoinCircleCubeInr (j : ℤ) :
    D.resolutionCube hD R (j + 1) ⟶ D.adjoinCircle.resolutionCube hD' R j :=
  NatTrans.ofCubeEdges (D.adjoinCircleCubeInrApp hD hD' R j) fun S T h ↦ by
    obtain ⟨a, ha, rfl⟩ := h.exists_finset_insert
    have hst := cubeState_eq_of_covBy h ha (mem_insert_self a S)
    have hc := cubeState_ne_of_notMem_of_mem ha (mem_insert_self a S)
    rw [← cancel_mono (D.adjoinCircle.resolutionCubeι hD' R j (insert a S)), Category.assoc,
      Category.assoc, adjoinCircleCubeInrApp_comp_resolutionCubeι,
      D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι_assoc hD R (j + 1) ha,
      D.adjoinCircle.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD' R j ha,
      adjoinCircleCubeInrApp_comp_resolutionCubeι_assoc]
    ext x
    exact (D.resolutionEdgeMap_circleX_adjoinCircleIncl R hst hc _ _ _).symm

/-- The first projection `D.adjoinCircle(j) ⟶ D(j - 1)` on cubes of resolutions, extracting the
`1`-component on the adjoined circle. -/
def adjoinCircleCubeFst (j : ℤ) :
    D.adjoinCircle.resolutionCube hD' R j ⟶ D.resolutionCube hD R (j - 1) :=
  NatTrans.ofCubeEdges (D.adjoinCircleCubeFstApp hD hD' R j) fun S T h ↦ by
    obtain ⟨a, ha, rfl⟩ := h.exists_finset_insert
    have hst := cubeState_eq_of_covBy h ha (mem_insert_self a S)
    have hc := cubeState_ne_of_notMem_of_mem ha (mem_insert_self a S)
    rw [← cancel_mono (D.resolutionCubeι hD R (j - 1) (insert a S)), Category.assoc,
      Category.assoc, adjoinCircleCubeFstApp_comp_resolutionCubeι,
      D.adjoinCircle.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι_assoc hD' R j ha,
      D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD R (j - 1) ha,
      adjoinCircleCubeFstApp_comp_resolutionCubeι_assoc]
    ext x
    exact D.fiberwiseSplit_circleX_resolutionEdgeMap_adjoinCircle R hst hc _ _ _

/-- The second projection `D.adjoinCircle(j) ⟶ D(j + 1)` on cubes of resolutions, extracting the
`X`-component on the adjoined circle. -/
def adjoinCircleCubeSnd (j : ℤ) :
    D.adjoinCircle.resolutionCube hD' R j ⟶ D.resolutionCube hD R (j + 1) :=
  NatTrans.ofCubeEdges (D.adjoinCircleCubeSndApp hD hD' R j) fun S T h ↦ by
    obtain ⟨a, ha, rfl⟩ := h.exists_finset_insert
    have hst := cubeState_eq_of_covBy h ha (mem_insert_self a S)
    have hc := cubeState_ne_of_notMem_of_mem ha (mem_insert_self a S)
    rw [← cancel_mono (D.resolutionCubeι hD R (j + 1) (insert a S)), Category.assoc,
      Category.assoc, adjoinCircleCubeSndApp_comp_resolutionCubeι,
      D.adjoinCircle.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι_assoc hD' R j ha,
      D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD R (j + 1) ha,
      adjoinCircleCubeSndApp_comp_resolutionCubeι_assoc]
    ext x
    exact D.fiberwiseSplit_resolutionEdgeMap_adjoinCircle R hst hc _ _ _

@[reassoc]
theorem adjoinCircleCubeInl_app_comp_resolutionCubeι (j : ℤ) (S : Finset (Fin n)) :
    (D.adjoinCircleCubeInl hD hD' R j).app S ≫ D.adjoinCircle.resolutionCubeι hD' R j S =
      D.resolutionCubeι hD R (j - 1) S ≫
        ModuleCat.ofHom
          (fiberwiseMul (R := R) (A := fun _ ↦ R[ε])
            (D.adjoinCircleIncl (cubeState S))).toLinearMap := by
  rw [adjoinCircleCubeInl, NatTrans.ofCubeEdges_app]
  exact D.adjoinCircleCubeInlApp_comp_resolutionCubeι hD hD' R j S

@[reassoc]
theorem adjoinCircleCubeInr_app_comp_resolutionCubeι (j : ℤ) (S : Finset (Fin n)) :
    (D.adjoinCircleCubeInr hD hD' R j).app S ≫ D.adjoinCircle.resolutionCubeι hD' R j S =
      D.resolutionCubeι hD R (j + 1) S ≫
        ModuleCat.ofHom (Khovanov.circleX R (D.adjoinCircleNew (cubeState S)) ∘ₗ
          (fiberwiseMul (R := R) (A := fun _ ↦ R[ε])
            (D.adjoinCircleIncl (cubeState S))).toLinearMap) := by
  rw [adjoinCircleCubeInr, NatTrans.ofCubeEdges_app]
  exact D.adjoinCircleCubeInrApp_comp_resolutionCubeι hD hD' R j S

@[reassoc]
theorem adjoinCircleCubeFst_app_comp_resolutionCubeι (j : ℤ) (S : Finset (Fin n)) :
    (D.adjoinCircleCubeFst hD hD' R j).app S ≫ D.resolutionCubeι hD R (j - 1) S =
      D.adjoinCircle.resolutionCubeι hD' R j S ≫
        ModuleCat.ofHom (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl (cubeState S)) ∘ₗ
          Khovanov.circleX R (D.adjoinCircleNew (cubeState S))) := by
  rw [adjoinCircleCubeFst, NatTrans.ofCubeEdges_app]
  exact D.adjoinCircleCubeFstApp_comp_resolutionCubeι hD hD' R j S

@[reassoc]
theorem adjoinCircleCubeSnd_app_comp_resolutionCubeι (j : ℤ) (S : Finset (Fin n)) :
    (D.adjoinCircleCubeSnd hD hD' R j).app S ≫ D.resolutionCubeι hD R (j + 1) S =
      D.adjoinCircle.resolutionCubeι hD' R j S ≫
        ModuleCat.ofHom (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleIncl (cubeState S))) := by
  rw [adjoinCircleCubeSnd, NatTrans.ofCubeEdges_app]
  exact D.adjoinCircleCubeSndApp_comp_resolutionCubeι hD hD' R j S

@[reassoc (attr := simp)]
theorem adjoinCircleCubeInl_comp_fst (j : ℤ) :
    D.adjoinCircleCubeInl hD hD' R j ≫ D.adjoinCircleCubeFst hD hD' R j = 𝟙 _ := by
  ext S : 2
  rw [NatTrans.comp_app, NatTrans.id_app, ← cancel_mono (D.resolutionCubeι hD R (j - 1) S),
    Category.assoc, adjoinCircleCubeFst_app_comp_resolutionCubeι,
    adjoinCircleCubeInl_app_comp_resolutionCubeι_assoc, Category.id_comp]
  ext x
  exact Khovanov.fiberwiseSplit_circleX_fiberwiseMul
    (D.adjoinCircleIncl_injective (cubeState S))
    (D.adjoinCircleNew_notMem_range_adjoinCircleIncl (cubeState S))
    (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl (cubeState S)) _

@[reassoc (attr := simp)]
theorem adjoinCircleCubeInl_comp_snd (j : ℤ) :
    D.adjoinCircleCubeInl hD hD' R j ≫ D.adjoinCircleCubeSnd hD hD' R j = 0 := by
  ext S : 2
  rw [NatTrans.comp_app, NatTrans.app_zero, ← cancel_mono (D.resolutionCubeι hD R (j + 1) S),
    Category.assoc, adjoinCircleCubeSnd_app_comp_resolutionCubeι,
    adjoinCircleCubeInl_app_comp_resolutionCubeι_assoc, Limits.zero_comp]
  ext x
  exact Khovanov.fiberwiseSplit_fiberwiseMul_of_notMem_range
    (D.adjoinCircleNew_notMem_range_adjoinCircleIncl (cubeState S)) _

@[reassoc (attr := simp)]
theorem adjoinCircleCubeInr_comp_fst (j : ℤ) :
    D.adjoinCircleCubeInr hD hD' R j ≫ D.adjoinCircleCubeFst hD hD' R j = 0 := by
  ext S : 2
  rw [NatTrans.comp_app, NatTrans.app_zero, ← cancel_mono (D.resolutionCubeι hD R (j - 1) S),
    Category.assoc, adjoinCircleCubeFst_app_comp_resolutionCubeι,
    adjoinCircleCubeInr_app_comp_resolutionCubeι_assoc, Limits.zero_comp]
  ext x
  simp

@[reassoc (attr := simp)]
theorem adjoinCircleCubeInr_comp_snd (j : ℤ) :
    D.adjoinCircleCubeInr hD hD' R j ≫ D.adjoinCircleCubeSnd hD hD' R j = 𝟙 _ := by
  ext S : 2
  rw [NatTrans.comp_app, NatTrans.id_app, ← cancel_mono (D.resolutionCubeι hD R (j + 1) S),
    Category.assoc, adjoinCircleCubeSnd_app_comp_resolutionCubeι,
    adjoinCircleCubeInr_app_comp_resolutionCubeι_assoc, Category.id_comp]
  ext x
  exact Khovanov.fiberwiseSplit_circleX_fiberwiseMul
    (D.adjoinCircleIncl_injective (cubeState S))
    (D.adjoinCircleNew_notMem_range_adjoinCircleIncl (cubeState S))
    (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl (cubeState S)) _

@[simp]
theorem adjoinCircleCubeFst_comp_inl_add_snd_comp_inr (j : ℤ) :
    D.adjoinCircleCubeFst hD hD' R j ≫ D.adjoinCircleCubeInl hD hD' R j +
      D.adjoinCircleCubeSnd hD hD' R j ≫ D.adjoinCircleCubeInr hD hD' R j = 𝟙 _ := by
  ext S : 2
  rw [NatTrans.app_add, NatTrans.comp_app, NatTrans.comp_app, NatTrans.id_app,
    ← cancel_mono (D.adjoinCircle.resolutionCubeι hD' R j S), Preadditive.add_comp, Category.assoc,
    Category.assoc, adjoinCircleCubeInl_app_comp_resolutionCubeι,
    adjoinCircleCubeFst_app_comp_resolutionCubeι_assoc,
    adjoinCircleCubeInr_app_comp_resolutionCubeι,
    adjoinCircleCubeSnd_app_comp_resolutionCubeι_assoc, Category.id_comp]
  ext x
  exact Khovanov.fiberwiseMul_fiberwiseSplit_circleX_add
    (D.adjoinCircleIncl_injective (cubeState S))
    (D.adjoinCircleNew_notMem_range_adjoinCircleIncl (cubeState S))
    (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl (cubeState S)) _

/-- **Adjoining a circle splits the cube of resolutions.** In quantum degree `j`, the cube of
`D.adjoinCircle` is the direct sum of the cubes of `D` in quantum degrees `j - 1` (carrying `1` on
the adjoined circle) and `j + 1` (carrying `X` on the adjoined circle). -/
def adjoinCircleResolutionCubeIso (j : ℤ) :
    D.adjoinCircle.resolutionCube hD' R j ≅
      D.resolutionCube hD R (j - 1) ⊞ D.resolutionCube hD R (j + 1) where
  hom := biprod.lift (D.adjoinCircleCubeFst hD hD' R j) (D.adjoinCircleCubeSnd hD hD' R j)
  inv := biprod.desc (D.adjoinCircleCubeInl hD hD' R j) (D.adjoinCircleCubeInr hD hD' R j)
  hom_inv_id := by
    rw [biprod.lift_desc, adjoinCircleCubeFst_comp_inl_add_snd_comp_inr]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp

@[reassoc (attr := simp)]
theorem adjoinCircleResolutionCubeIso_hom_fst (j : ℤ) :
    (D.adjoinCircleResolutionCubeIso hD hD' R j).hom ≫ biprod.fst =
      D.adjoinCircleCubeFst hD hD' R j := by
  simp [adjoinCircleResolutionCubeIso]

@[reassoc (attr := simp)]
theorem adjoinCircleResolutionCubeIso_hom_snd (j : ℤ) :
    (D.adjoinCircleResolutionCubeIso hD hD' R j).hom ≫ biprod.snd =
      D.adjoinCircleCubeSnd hD hD' R j := by
  simp [adjoinCircleResolutionCubeIso]

@[reassoc (attr := simp)]
theorem inl_adjoinCircleResolutionCubeIso_inv (j : ℤ) :
    biprod.inl ≫ (D.adjoinCircleResolutionCubeIso hD hD' R j).inv =
      D.adjoinCircleCubeInl hD hD' R j := by
  simp [adjoinCircleResolutionCubeIso]

@[reassoc (attr := simp)]
theorem inr_adjoinCircleResolutionCubeIso_inv (j : ℤ) :
    biprod.inr ≫ (D.adjoinCircleResolutionCubeIso hD hD' R j).inv =
      D.adjoinCircleCubeInr hD hD' R j := by
  simp [adjoinCircleResolutionCubeIso]

/-! ### Merging and splitting the adjoined circle at a mark -/

/-- The cube morphism merging the adjoined circle of `D.adjoinCircle` into the circle through a
mark `p` of `D`, of quantum degree `-1`. On the `1`-summand it is the identity, and on the
`X`-summand it is the marked `X`-action `TauCeti.PDCode.resolutionCubeMarkX`. -/
def adjoinCircleCollapseMerge (p : D.Mark) (j : ℤ) :
    D.adjoinCircle.resolutionCube hD' R j ⟶ D.resolutionCube hD R (j - 1) :=
  (D.adjoinCircleResolutionCubeIso hD hD' R j).hom ≫
    biprod.desc (𝟙 _) (D.resolutionCubeMarkX p hD R (j := j + 1) (j' := j - 1) (by omega))

/-- The cube morphism splitting the circle through a mark `p` of `D` into itself and the adjoined
circle of `D.adjoinCircle`, of quantum degree `-1`. Into the `1`-summand it is the marked
`X`-action `TauCeti.PDCode.resolutionCubeMarkX`, and into the `X`-summand it is the identity. -/
def adjoinCircleCollapseSplit (p : D.Mark) (j : ℤ) :
    D.resolutionCube hD R j ⟶ D.adjoinCircle.resolutionCube hD' R (j - 1) :=
  biprod.lift (D.resolutionCubeMarkX p hD R (j := j) (j' := (j - 1) - 1) (by omega))
      (eqToHom (by congr 1; omega)) ≫
    (D.adjoinCircleResolutionCubeIso hD hD' R (j - 1)).inv

@[reassoc (attr := simp)]
theorem adjoinCircleCubeInl_comp_collapseMerge (p : D.Mark) (j : ℤ) :
    D.adjoinCircleCubeInl hD hD' R j ≫ D.adjoinCircleCollapseMerge hD hD' R p j = 𝟙 _ := by
  rw [adjoinCircleCollapseMerge, ← inl_adjoinCircleResolutionCubeIso_inv_assoc,
    Iso.inv_hom_id_assoc, biprod.inl_desc]

@[reassoc (attr := simp)]
theorem adjoinCircleCubeInr_comp_collapseMerge (p : D.Mark) (j : ℤ) :
    D.adjoinCircleCubeInr hD hD' R j ≫ D.adjoinCircleCollapseMerge hD hD' R p j =
      D.resolutionCubeMarkX p hD R (j := j + 1) (j' := j - 1) (by omega) := by
  rw [adjoinCircleCollapseMerge, ← inr_adjoinCircleResolutionCubeIso_inv_assoc,
    Iso.inv_hom_id_assoc, biprod.inr_desc]

@[reassoc (attr := simp)]
theorem collapseSplit_comp_adjoinCircleCubeFst (p : D.Mark) (j : ℤ) :
    D.adjoinCircleCollapseSplit hD hD' R p j ≫ D.adjoinCircleCubeFst hD hD' R (j - 1) =
      D.resolutionCubeMarkX p hD R (j := j) (j' := (j - 1) - 1) (by omega) := by
  rw [adjoinCircleCollapseSplit, Category.assoc, ← adjoinCircleResolutionCubeIso_hom_fst,
    Iso.inv_hom_id_assoc, biprod.lift_fst]

@[reassoc (attr := simp)]
theorem collapseSplit_comp_adjoinCircleCubeSnd (p : D.Mark) (j : ℤ) :
    D.adjoinCircleCollapseSplit hD hD' R p j ≫ D.adjoinCircleCubeSnd hD hD' R (j - 1) =
      eqToHom (by congr 1; omega) := by
  rw [adjoinCircleCollapseSplit, Category.assoc, ← adjoinCircleResolutionCubeIso_hom_snd,
    Iso.inv_hom_id_assoc, biprod.lift_snd]

/-- On each vertex `S`, `adjoinCircleCollapseMerge` acts on circle tensors by `fiberwiseMul` along
`adjoinCircleCollapse`. -/
@[reassoc]
theorem adjoinCircleCollapseMerge_app_comp_resolutionCubeι (p : D.Mark) (j : ℤ)
    (S : Finset (Fin n)) :
    (D.adjoinCircleCollapseMerge hD hD' R p j).app S ≫ D.resolutionCubeι hD R (j - 1) S =
      D.adjoinCircle.resolutionCubeι hD' R j S ≫
        ModuleCat.ofHom (fiberwiseMul (R := R) (A := fun _ ↦ R[ε])
          (D.adjoinCircleCollapse p (cubeState S))).toLinearMap := by
  have hsplit := congrArg (fun f ↦ f.app S ≫ D.resolutionCubeι hD R (j - 1) S)
    (show D.adjoinCircleCollapseMerge hD hD' R p j =
        D.adjoinCircleCubeFst hD hD' R j +
          D.adjoinCircleCubeSnd hD hD' R j ≫
            D.resolutionCubeMarkX p hD R (j := j + 1) (j' := j - 1) (by omega) by
      rw [adjoinCircleCollapseMerge, adjoinCircleResolutionCubeIso, biprod.lift_desc,
        Category.comp_id])
  rw [hsplit, NatTrans.app_add, NatTrans.comp_app, Preadditive.add_comp, Category.assoc,
    adjoinCircleCubeFst_app_comp_resolutionCubeι, resolutionCubeMarkX_app_comp_resolutionCubeι,
    adjoinCircleCubeSnd_app_comp_resolutionCubeι_assoc]
  ext x
  have hx := D.adjoinCircleCollapse_adjoinCircleIncl p (cubeState S)
  have hν := D.adjoinCircleCollapse_adjoinCircleNew p (cubeState S)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.add_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  symm
  conv_lhs =>
    rw [← Khovanov.fiberwiseMul_fiberwiseSplit_circleX_add
      (D.adjoinCircleIncl_injective (cubeState S))
      (D.adjoinCircleNew_notMem_range_adjoinCircleIncl (cubeState S))
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl (cubeState S))
      ((D.adjoinCircle.resolutionCubeι hD' R j S).hom x)]
  rw [map_add, Khovanov.fiberwiseMul_fiberwiseMul_of_leftInverse hx,
    Khovanov.fiberwiseMul_circleX_fiberwiseMul_of_leftInverse hx, hν]

@[reassoc]
private theorem eqToHom_app_resolutionCubeι {j₁ j₂ : ℤ} (h : j₁ = j₂) (S : Finset (Fin n)) :
    (eqToHom (show D.resolutionCube hD R j₁ = D.resolutionCube hD R j₂ by rw [h])).app S ≫
        D.resolutionCubeι hD R j₂ S =
      D.resolutionCubeι hD R j₁ S := by
  subst h
  simp

/-- On each vertex `S`, `adjoinCircleCollapseSplit` acts on circle tensors by `fiberwiseSplit`
along `adjoinCircleCollapse`. -/
@[reassoc]
theorem adjoinCircleCollapseSplit_app_comp_resolutionCubeι (p : D.Mark) (j : ℤ)
    (S : Finset (Fin n)) :
    (D.adjoinCircleCollapseSplit hD hD' R p j).app S ≫
        D.adjoinCircle.resolutionCubeι hD' R (j - 1) S =
      D.resolutionCubeι hD R j S ≫
        ModuleCat.ofHom
          (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleCollapse p (cubeState S))) := by
  have hsplit := congrArg (fun f ↦ f.app S ≫ D.adjoinCircle.resolutionCubeι hD' R (j - 1) S)
    (show D.adjoinCircleCollapseSplit hD hD' R p j =
        D.resolutionCubeMarkX p hD R (j := j) (j' := (j - 1) - 1) (by omega) ≫
            D.adjoinCircleCubeInl hD hD' R (j - 1) +
          eqToHom (by congr 1; omega) ≫ D.adjoinCircleCubeInr hD hD' R (j - 1) by
      rw [adjoinCircleCollapseSplit, adjoinCircleResolutionCubeIso, biprod.lift_desc])
  rw [hsplit, NatTrans.app_add, NatTrans.comp_app, NatTrans.comp_app, Preadditive.add_comp,
    Category.assoc, Category.assoc, adjoinCircleCubeInl_app_comp_resolutionCubeι,
    resolutionCubeMarkX_app_comp_resolutionCubeι_assoc,
    adjoinCircleCubeInr_app_comp_resolutionCubeι,
    D.eqToHom_app_resolutionCubeι_assoc hD R (j₁ := j) (j₂ := j - 1 + 1) (by omega) S]
  ext x
  have hx := D.adjoinCircleCollapse_adjoinCircleIncl p (cubeState S)
  have hν := D.adjoinCircleCollapse_adjoinCircleNew p (cubeState S)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.add_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  symm
  conv_lhs =>
    rw [← Khovanov.fiberwiseMul_fiberwiseSplit_circleX_add
      (D.adjoinCircleIncl_injective (cubeState S))
      (D.adjoinCircleNew_notMem_range_adjoinCircleIncl (cubeState S))
      (D.eq_adjoinCircleNew_or_mem_range_adjoinCircleIncl (cubeState S))
      (Khovanov.fiberwiseSplit (R := R) (D.adjoinCircleCollapse p (cubeState S))
        ((D.resolutionCubeι hD R j S).hom x))]
  rw [Khovanov.fiberwiseSplit_circleX_fiberwiseSplit_of_leftInverse hx,
    Khovanov.fiberwiseSplit_fiberwiseSplit_of_leftInverse hx, hν]

/-- **Adjoining a circle splits the unnormalized Khovanov bracket.** In quantum degree `j`,
`⟦D.adjoinCircle⟧ʲ ≅ ⟦D⟧ʲ⁻¹ ⊞ ⟦D⟧ʲ⁺¹`. -/
def adjoinCircleKhovanovBracketIso (j : ℤ) :
    D.adjoinCircle.khovanovBracket hD' R j ≅
      D.khovanovBracket hD R (j - 1) ⊞ D.khovanovBracket hD R (j + 1) where
  hom := biprod.lift
    (eqToHom (D.adjoinCircle.khovanovBracket_apply hD' R j) ≫
      NatTrans.cubeComplexMap (D.adjoinCircleCubeFst hD hD' R j) ≫
      eqToHom (D.khovanovBracket_apply hD R (j - 1)).symm)
    (eqToHom (D.adjoinCircle.khovanovBracket_apply hD' R j) ≫
      NatTrans.cubeComplexMap (D.adjoinCircleCubeSnd hD hD' R j) ≫
      eqToHom (D.khovanovBracket_apply hD R (j + 1)).symm)
  inv := biprod.desc
    (eqToHom (D.khovanovBracket_apply hD R (j - 1)) ≫
      NatTrans.cubeComplexMap (D.adjoinCircleCubeInl hD hD' R j) ≫
      eqToHom (D.adjoinCircle.khovanovBracket_apply hD' R j).symm)
    (eqToHom (D.khovanovBracket_apply hD R (j + 1)) ≫
      NatTrans.cubeComplexMap (D.adjoinCircleCubeInr hD hD' R j) ≫
      eqToHom (D.adjoinCircle.khovanovBracket_apply hD' R j).symm)
  hom_inv_id := by
    rw [biprod.lift_desc]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Preadditive.comp_add]
    rw [← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
      ← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
      ← Preadditive.add_comp, ← NatTrans.cubeComplexMap_add,
      adjoinCircleCubeFst_comp_inl_add_snd_comp_inr, NatTrans.cubeComplexMap_id]
    simp
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp only [Category.assoc, Category.comp_id, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        biprod.lift_fst, biprod.lift_snd, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst,
        biprod.inr_snd, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    · rw [← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
        adjoinCircleCubeInl_comp_fst, NatTrans.cubeComplexMap_id]
      simp
    · rw [← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
        adjoinCircleCubeInl_comp_snd,
        show NatTrans.cubeComplexMap (0 : _ ⟶ _) = 0 from (cubeComplexFunctor _ _).map_zero _ _]
      simp
    · rw [← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
        adjoinCircleCubeInr_comp_fst,
        show NatTrans.cubeComplexMap (0 : _ ⟶ _) = 0 from (cubeComplexFunctor _ _).map_zero _ _]
      simp
    · rw [← Category.assoc (NatTrans.cubeComplexMap _), ← NatTrans.cubeComplexMap_comp,
        adjoinCircleCubeInr_comp_snd, NatTrans.cubeComplexMap_id]
      simp

@[reassoc (attr := simp)]
theorem adjoinCircleKhovanovBracketIso_hom_fst (j : ℤ) :
    (D.adjoinCircleKhovanovBracketIso hD hD' R j).hom ≫ biprod.fst =
      eqToHom (D.adjoinCircle.khovanovBracket_apply hD' R j) ≫
        NatTrans.cubeComplexMap (D.adjoinCircleCubeFst hD hD' R j) ≫
        eqToHom (D.khovanovBracket_apply hD R (j - 1)).symm := by
  simp [adjoinCircleKhovanovBracketIso]

@[reassoc (attr := simp)]
theorem adjoinCircleKhovanovBracketIso_hom_snd (j : ℤ) :
    (D.adjoinCircleKhovanovBracketIso hD hD' R j).hom ≫ biprod.snd =
      eqToHom (D.adjoinCircle.khovanovBracket_apply hD' R j) ≫
        NatTrans.cubeComplexMap (D.adjoinCircleCubeSnd hD hD' R j) ≫
        eqToHom (D.khovanovBracket_apply hD R (j + 1)).symm := by
  simp [adjoinCircleKhovanovBracketIso]

@[reassoc (attr := simp)]
theorem inl_adjoinCircleKhovanovBracketIso_inv (j : ℤ) :
    biprod.inl ≫ (D.adjoinCircleKhovanovBracketIso hD hD' R j).inv =
      eqToHom (D.khovanovBracket_apply hD R (j - 1)) ≫
        NatTrans.cubeComplexMap (D.adjoinCircleCubeInl hD hD' R j) ≫
        eqToHom (D.adjoinCircle.khovanovBracket_apply hD' R j).symm := by
  simp [adjoinCircleKhovanovBracketIso]

@[reassoc (attr := simp)]
theorem inr_adjoinCircleKhovanovBracketIso_inv (j : ℤ) :
    biprod.inr ≫ (D.adjoinCircleKhovanovBracketIso hD hD' R j).inv =
      eqToHom (D.khovanovBracket_apply hD R (j + 1)) ≫
        NatTrans.cubeComplexMap (D.adjoinCircleCubeInr hD hD' R j) ≫
        eqToHom (D.adjoinCircle.khovanovBracket_apply hD' R j).symm := by
  simp [adjoinCircleKhovanovBracketIso]

end Cube

end TauCeti.PDCode

/-! ### Normalized complex and Khovanov homology of `OrientedPDCode.adjoinCircle` -/

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (o : Bool) (hD : D.toPDCode.IsPlanar)
  (hD' : (D.adjoinCircle o).toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- **Adjoining a crossing-free circle splits the normalized Khovanov complex.** In quantum degree
`j`, `C(D ⊔ ○)ʲ ≅ C(D)ʲ⁻¹ ⊞ C(D)ʲ⁺¹`, independently of the orientation `o` of the new circle. -/
def adjoinCircleKhovanovComplexIso (j : ℤ) :
    (D.adjoinCircle o).khovanovComplex hD' R j ≅
      D.khovanovComplex hD R (j - 1) ⊞ D.khovanovComplex hD R (j + 1) :=
  let hD₀ : D.toPDCode.adjoinCircle.IsPlanar := by rwa [← toPDCode_adjoinCircle D o]
  let S := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ)
    (D.negativeCrossingCount : ℤ)
  letI := preservesBinaryBiproducts_of_preservesBiproducts S
  (D.adjoinCircle o).khovanovComplexShiftIso hD' R j ≪≫
    eqToIso (by
      rw [positiveCrossingCount_adjoinCircle, negativeCrossingCount_adjoinCircle]
      have hpair :
          (⟨(D.adjoinCircle o).toPDCode, hD'⟩ : {Q : PDCode n // Q.IsPlanar}) =
            ⟨D.toPDCode.adjoinCircle, hD₀⟩ :=
        Subtype.ext (toPDCode_adjoinCircle D o)
      exact congrArg (fun E : {Q : PDCode n // Q.IsPlanar} ↦
        (E.1.khovanovBracket E.2 R
          (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount))⟦
            (D.negativeCrossingCount : ℤ)⟧) hpair) ≪≫
    S.mapIso (D.toPDCode.adjoinCircleKhovanovBracketIso hD hD₀ R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)) ≪≫
    S.mapBiprod _ _ ≪≫
    biprod.mapIso
      (eqToIso (by congr 2; omega) ≪≫ (D.khovanovComplexShiftIso hD R (j - 1)).symm)
      (eqToIso (by congr 2; omega) ≪≫ (D.khovanovComplexShiftIso hD R (j + 1)).symm)

/-- **Adjoining a crossing-free circle splits Khovanov homology.** In bidegree `(i, j)`,
`Khⁱʲ(D ⊔ ○; R) ≅ Khⁱ,ʲ⁻¹(D; R) ⊞ Khⁱ,ʲ⁺¹(D; R)`, independently of the orientation `o`. -/
def adjoinCircleKhovanovHomologyIso (i j : ℤ) :
    (D.adjoinCircle o).khovanovHomology hD' R i j ≅
      D.khovanovHomology hD R i (j - 1) ⊞ D.khovanovHomology hD R i (j + 1) :=
  letI := preservesBinaryBiproducts_of_preservesBiproducts
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i)
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      (D.adjoinCircleKhovanovComplexIso o hD hD' R j) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapBiprod _ _

end TauCeti.OrientedPDCode
