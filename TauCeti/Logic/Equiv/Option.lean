/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Option
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Logic.Equiv.Set

/-!
# Extending matchings and shifting along a sequence on `Option`

A relation between two index types that holds along an equivalence of the complements of two
points, and also holds at those two points, is realised by an equivalence of the whole types
(`Equiv.exists_equiv_forall_of_equiv_subtype_ne`).

Conversely, `Equiv.optionSubtype` identifies the equivalences sending one point to another with
the equivalences of their complements, so between two types with `m + 1` elements there are `m!`
equivalences sending a given point to a given point (`Nat.card_subtype_equiv_apply_eq`).

An injective sequence `f : ℕ → α` yields a Hilbert-hotel equivalence
`Equiv.optionOfNatInjective f hf : Option α ≃ α` sending `none` to `f 0`, shifting `some (f n)` to
`f (n + 1)`, and fixing `some x` outside the range of `f`.
-/

public section

namespace Equiv

/-- A relation `R` between two types that holds along an equivalence of the complements of `i₀`
and `j₀` and also holds at `i₀, j₀` is realised by an equivalence of the whole types. -/
theorem exists_equiv_forall_of_equiv_subtype_ne {ι κ : Type*}
    {R : ι → κ → Prop} {i₀ : ι} {j₀ : κ} (e : {i // i ≠ i₀} ≃ {j // j ≠ j₀}) (h₀ : R i₀ j₀)
    (h : ∀ i : {i // i ≠ i₀}, R i (e i)) : ∃ e' : ι ≃ κ, ∀ i, R i (e' i) := by
  classical
  refine ⟨(Equiv.optionSubtypeNe i₀).symm.trans
    ((Equiv.optionCongr e).trans (Equiv.optionSubtypeNe j₀)), fun i ↦ ?_⟩
  rcases eq_or_ne i i₀ with rfl | hi
  · have hnone : ((Equiv.optionSubtypeNe i).symm.trans
        ((Equiv.optionCongr e).trans (Equiv.optionSubtypeNe j₀))) i = j₀ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self]
      rfl
    rwa [hnone]
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hi,
      Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some]
    exact h ⟨i, hi⟩

open Classical in
/-- **Hilbert's hotel along an injective sequence.** Given `f : ℕ → α` injective, `Option α ≃ α`
sends `none` to `f 0`, `some (f n)` to `f (n + 1)`, and `some x` to `x` outside the range of `f`. -/
noncomputable def optionOfNatInjective {α : Type*} (f : ℕ → α) (hf : f.Injective) :
    Option α ≃ α :=
  (optionEquivSumPUnit.{0} α).trans <|
    (((ofInjectiveSumCompl f hf).symm.sumCongr (Equiv.refl PUnit)).trans
      ((sumAssoc ℕ ↥(Set.range f)ᶜ PUnit).trans
        ((Equiv.refl ℕ |>.sumCongr (sumComm _ PUnit)).trans
          (sumAssoc ℕ PUnit ↥(Set.range f)ᶜ).symm))).trans <|
      (natSumPUnitEquivNat.sumCongr (Equiv.refl _)).trans (ofInjectiveSumCompl f hf)

section OptionOfNatInjective

variable {α : Type*} {f : ℕ → α} (hf : f.Injective)

@[simp]
theorem optionOfNatInjective_none : optionOfNatInjective f hf none = f 0 := by
  simp [optionOfNatInjective, natSumPUnitEquivNat, natEquivNatSumPUnit]

@[simp]
theorem optionOfNatInjective_some_apply (n : ℕ) :
    optionOfNatInjective f hf (some (f n)) = f (n + 1) := by
  simp [optionOfNatInjective, natSumPUnitEquivNat, natEquivNatSumPUnit]

/-- Outside the range of `f`, `optionOfNatInjective` unwraps `some`. -/
theorem optionOfNatInjective_some_of_notMem {x : α} (hx : x ∉ Set.range f) :
    optionOfNatInjective f hf (some x) = x := by
  have h := ofInjectiveSumCompl_symm_apply_compl hf ⟨x, hx⟩
  simp [optionOfNatInjective, h]

@[simp]
theorem optionOfNatInjective_symm_apply_zero :
    (optionOfNatInjective f hf).symm (f 0) = none :=
  (optionOfNatInjective f hf).symm_apply_eq.2 (optionOfNatInjective_none hf).symm

@[simp]
theorem optionOfNatInjective_symm_apply_succ (n : ℕ) :
    (optionOfNatInjective f hf).symm (f (n + 1)) = some (f n) :=
  (optionOfNatInjective f hf).symm_apply_eq.2 (optionOfNatInjective_some_apply hf n).symm

/-- Outside the range of `f`, `(optionOfNatInjective f hf).symm` wraps `x` in `some`. -/
theorem optionOfNatInjective_symm_of_notMem {x : α} (hx : x ∉ Set.range f) :
    (optionOfNatInjective f hf).symm x = some x :=
  (optionOfNatInjective f hf).symm_apply_eq.2 (optionOfNatInjective_some_of_notMem hf hx).symm

end OptionOfNatInjective

end Equiv

open Equiv in
/-- Between two finite types of the same cardinality, the equivalences sending `a` to `b` are
counted by the factorial of the number of remaining points. -/
theorem Nat.card_subtype_equiv_apply_eq {α β : Type*} [Finite α]
    (hαβ : Nat.card α = Nat.card β) (a : α) (b : β) :
    Nat.card {e : α ≃ β // e a = b} = (Nat.card α - 1).factorial := by
  classical
  have : Finite β := Nat.finite_of_card_ne_zero (by
    have := Nat.card_pos_iff.2 ⟨⟨a⟩, ‹_›⟩; omega)
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  let E : {e : α ≃ β // e a = b} ≃ ({x // x ≠ a} ≃ {y // y ≠ b}) :=
    ((equivCongr (optionSubtypeNe a) (Equiv.refl β)).symm.subtypeEquiv (fun e ↦ by simp)).trans
      (optionSubtype b)
  have hb : Fintype.card {x // x ≠ a} = Fintype.card {y // y ≠ b} := by
    simpa [Fintype.card_subtype_compl, Nat.card_eq_fintype_card] using congrArg (· - 1) hαβ
  rw [Nat.card_congr E, Nat.card_eq_fintype_card,
    Fintype.card_equiv (Fintype.equivOfCardEq hb), Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype_compl]
