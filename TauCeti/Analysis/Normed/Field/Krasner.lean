/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Krasner
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect

import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Finite intermediate fields via Krasner's lemma

Let `L / K` be an extension of normed fields satisfying Krasner's lemma (`IsKrasner K L`) with `L`
algebraically closed, and let `k` be a field whose image in `K` is dense. Approximating the minimal
polynomial of a separable element `x ∈ L` over `K` by a monic polynomial of the same degree over
`k` produces a root `y ∈ L` algebraic over `k` arbitrarily close to `x`. By Krasner's lemma
`x ∈ K(y)`, while comparing degrees over `K` forces `K(y) = K(x)`.

By the primitive element theorem, every finite separable intermediate field `K ⊆ E ⊆ L` is generated
over `K` by a single element algebraic over `k`. When `k` is countable, the elements of `L`
algebraic over `k` are countable (`Algebraic.countable`), so there are only countably many finite
separable intermediate fields (and, when `K` is perfect, only countably many finite intermediate
fields).

## Main results

* `IsSeparable.exists_isAlgebraic_norm_sub_lt_and_adjoin_simple_eq`: a separable element `x ∈ L`
  can be approximated arbitrarily closely by an element `y` algebraic over a dense subfield `k`
  generating the same simple extension `K⟮y⟯ = K⟮x⟯`.
* `IntermediateField.exists_isAlgebraic_adjoin_simple_eq`: every finite separable intermediate field
  is generated over `K` by an element algebraic over `k`.
* `IntermediateField.countable_finiteDimensional_isSeparable`: when `k` is countable, the finite
  separable intermediate fields of `L / K` are countable.
* `IntermediateField.countable_finiteDimensional`: when `k` is countable and `K` is perfect, the
  finite intermediate fields of `L / K` are countable.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3.
-/

public section

open Polynomial IntermediateField

section KrasnerDense

variable {k K L : Type*} [Field k] [NormedField K] [NormedField L] [NormedAlgebra K L]
  [IsKrasner K L] [Algebra k K] [Algebra k L] [IsScalarTower k K L] [IsAlgClosed L]

/-- **Krasner generation from a dense subfield.** In an algebraically closed normed extension
`L / K` satisfying Krasner's lemma, any element `x ∈ L` separable over `K` admits an arbitrarily
close element `y ∈ L` algebraic over a dense subfield `k ⊆ K` such that `K⟮y⟯ = K⟮x⟯`. -/
theorem IsSeparable.exists_isAlgebraic_norm_sub_lt_and_adjoin_simple_eq {x : L}
    (hx : IsSeparable K x) (hk : DenseRange (algebraMap k K)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : L, IsAlgebraic k y ∧ ‖x - y‖ < δ ∧ K⟮y⟯ = K⟮x⟯ := by
  classical
  have hx_int : IsIntegral K x := hx.isIntegral
  have hfm : (minpoly K x).Monic := minpoly.monic hx_int
  have hn : (minpoly K x).natDegree ≠ 0 := (minpoly.natDegree_pos hx_int).ne'
  -- Step 1: choose `0 < δ₀ ≤ δ` bounded by the distance from `x` to every distinct `K`-conjugate.
  let S : Finset L := {x' ∈ ((minpoly K x).rootSet L).toFinset | x' ≠ x}
  let δ₀ : ℝ := if hS : S.Nonempty then
    min δ (Finset.min' (S.image fun x' ↦ ‖x - x'‖) (Finset.image_nonempty.mpr hS)) else δ
  have hδ₀ : 0 < δ₀ := by
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ₀]
    · refine lt_min hδ ?_
      simp only [Finset.lt_min'_iff, Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro x' hx'
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hx').2.symm)
    · exact hδ
  have hδ₀_le : δ₀ ≤ δ := by
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ₀]
    · exact min_le_left _ _
    · exact le_rfl
  have hδ₀_conj : ∀ x' : L, IsConjRoot K x x' → x ≠ x' → δ₀ ≤ ‖x - x'‖ := by
    intro x' hconj hne
    have hx'S : x' ∈ S := Finset.mem_filter.mpr
      ⟨Set.mem_toFinset.mpr ((isConjRoot_iff_mem_minpoly_rootSet hx_int).mp hconj), hne.symm⟩
    have hS : S.Nonempty := ⟨x', hx'S⟩
    simp only [hS, ↓reduceDIte, δ₀]
    exact (min_le_right _ _).trans (Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx'S))
  -- Step 2: approximate `minpoly K x` by a monic polynomial `g ∈ k[X]` of the same degree and pick
  -- a root `y ∈ L` within distance `δ₀` of `x`.
  have hM : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  have hε : 0 < (δ₀ / max ‖x‖ 1) ^ (minpoly K x).natDegree / ((minpoly K x).natDegree + 1) := by
    positivity
  obtain ⟨g, hgm, hdeg, hcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hk hfm hε
  obtain ⟨y, hy, hxy⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε (minpoly.aeval K x) hfm
    (hgm.map _) (by rw [natDegree_map, hdeg]) hcoeff (IsAlgClosed.splits _)
  rw [mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (div_pos hδ₀ hM).le hn,
    div_mul_cancel₀ _ hM.ne'] at hxy
  have hy_root : aeval y (g.map (algebraMap k K)) = 0 := (mem_aroots.mp hy).2
  have hy_int : IsIntegral K y := ⟨g.map (algebraMap k K), hgm.map _, hy_root⟩
  have hy_alg : IsAlgebraic k y := ⟨g, hgm.ne_zero, by simpa using hy_root⟩
  -- Step 3: Krasner's lemma gives `K⟮x⟯ ≤ K⟮y⟯`, and comparing degrees over `K` forces equality.
  have hx_mem : x ∈ K⟮y⟯ := IsKrasner.krasner hx (IsAlgClosed.splits _) hy_int
    fun x' hconj hne ↦ hxy.trans_le (hδ₀_conj x' hconj hne)
  have hle : K⟮x⟯ ≤ K⟮y⟯ := adjoin_simple_le_iff.mpr hx_mem
  have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx_int
  have : FiniteDimensional K K⟮y⟯ := adjoin.finiteDimensional hy_int
  have hfin : Module.finrank K K⟮y⟯ ≤ Module.finrank K K⟮x⟯ := by
    rw [adjoin.finrank hy_int, adjoin.finrank hx_int]
    exact (natDegree_le_of_dvd (minpoly.dvd K y hy_root) (hgm.map _).ne_zero).trans_eq
      (by rw [natDegree_map, hdeg])
  have heq : K⟮x⟯.toSubmodule = K⟮y⟯.toSubmodule :=
    Submodule.eq_of_le_of_finrank_le hle hfin
  refine ⟨y, hy_alg, hxy.trans_le hδ₀_le, SetLike.ext fun z ↦ ?_⟩
  simpa using (SetLike.ext_iff.mp heq z).symm

/-- **Every finite separable intermediate field is generated over `K` by an element algebraic over
a dense subfield `k`.** -/
theorem IntermediateField.exists_isAlgebraic_adjoin_simple_eq
    (E : IntermediateField K L) [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (hk : DenseRange (algebraMap k K)) :
    ∃ y : L, IsAlgebraic k y ∧ K⟮y⟯ = E := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  have hKx : K⟮(α : L)⟯ = E := by
    have hmap := congrArg (IntermediateField.map E.val) hα
    rw [IntermediateField.adjoin_map, Set.image_singleton] at hmap
    exact hmap.trans (SetLike.ext fun z ↦ by
      simp only [IntermediateField.mem_map, IntermediateField.mem_top, true_and,
        IntermediateField.coe_val]
      exact ⟨by rintro ⟨w, rfl⟩; exact w.2, fun hz ↦ ⟨⟨z, hz⟩, rfl⟩⟩)
  have hsep : IsSeparable K (α : L) := by
    have hα_sep : IsSeparable K α := Algebra.IsSeparable.isSeparable K α
    rw [IsSeparable, ← E.coe_val, minpoly.algHom_eq E.val E.val.injective α]
    exact hα_sep
  obtain ⟨y, hy_alg, -, hy_eq⟩ :=
    hsep.exists_isAlgebraic_norm_sub_lt_and_adjoin_simple_eq hk one_pos
  exact ⟨y, hy_alg, hy_eq.trans hKx⟩

variable (k K L) in
/-- **Countably many finite separable intermediate fields.** When `k` is countable and dense in `K`,
the finite separable intermediate fields of `L / K` form a countable set. -/
theorem IntermediateField.countable_finiteDimensional_isSeparable [Countable k]
    (hk : DenseRange (algebraMap k K)) :
    Set.Countable
      {E : IntermediateField K L | FiniteDimensional K E ∧ Algebra.IsSeparable K E} := by
  refine ((Algebraic.countable k L).image (fun y : L ↦ K⟮y⟯)).mono ?_
  rintro E ⟨hfin, hsep⟩
  obtain ⟨y, hy_alg, rfl⟩ := E.exists_isAlgebraic_adjoin_simple_eq hk
  exact ⟨y, hy_alg, rfl⟩

variable (k K L) in
/-- **Countably many finite intermediate fields over a perfect base.** When `k` is countable and
dense in a perfect field `K`, the finite intermediate fields of `L / K` form a countable set. -/
theorem IntermediateField.countable_finiteDimensional [Countable k] [PerfectField K]
    (hk : DenseRange (algebraMap k K)) :
    Set.Countable {E : IntermediateField K L | FiniteDimensional K E} := by
  refine (IntermediateField.countable_finiteDimensional_isSeparable k K L hk).mono ?_
  intro E hfin
  have : FiniteDimensional K E := hfin
  have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  exact ⟨hfin, inferInstance⟩

end KrasnerDense
