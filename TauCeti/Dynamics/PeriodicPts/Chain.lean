/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Function.Iterate
import Batteries.Data.Fin.Fold

/-!
# Periodic state sequences and fixed points of finite map chains

Given subsets `U : ZMod N → Set α` and maps `Φ : ZMod N → α → α` (`N ≥ 1`), a cyclic state
sequence `z : ZMod N → α` satisfying `z i ∈ U i` and `Φ i (z i) = z (i + 1)` for every `i` is
uniquely determined by its initial state `z 0`, which is fixed by the `N`-fold composite
`Fin.foldl N (fun z j ↦ Φ (j : ZMod N) z)` and has all intermediate partial composites in `U k`
(`TauCeti.periodicChainFixedPointEquiv`). When `Φ` is constant, `Fin.foldl` reduces to iteration
`f^[k]` (`TauCeti.finFoldl_const`).

## Main declarations

* `TauCeti.finFoldl_const`: folding a step map that ignores the `Fin k` index equals `f^[k]`.
* `TauCeti.periodicChainFixedPointEquiv`: bijection between fixed initial states of a `ZMod N`
  chain with intermediate states in `U k` and cyclic state sequences `z : ZMod N → α`.
* `TauCeti.foldl_periodicChainFixedPointEquiv_symm_coe`: folding `m` steps of `Φ` from `z 0` along
  a cyclic state sequence recovers `z m`.
-/

public section

namespace TauCeti

/-- Folding a step map that ignores the `Fin k` index `k` times from `z₀` equals iterating `f`
`k` times on `z₀`. -/
theorem finFoldl_const {α : Type*} (k : ℕ) (f : α → α) (z₀ : α) :
    Fin.foldl k (fun z _ ↦ f z) z₀ = f^[k] z₀ := by
  rw [Fin.foldl_eq_foldl_finRange, List.foldl_const, List.length_finRange]

private theorem foldl_castSucc_zmod {α : Type*} {N : ℕ} (Φ : ZMod N → α → α) (k : ℕ) (z₀ : α) :
    Fin.foldl k (fun w (j : Fin k) ↦ Φ (j.castSucc : ZMod N) w) z₀ =
      Fin.foldl k (fun w (j : Fin k) ↦ Φ (j : ZMod N) w) z₀ := by
  have hfun : (fun w (j : Fin k) ↦ Φ (j.castSucc : ZMod N) w) =
      fun w (j : Fin k) ↦ Φ (j : ZMod N) w := by
    ext w j
    simp only [Fin.val_castSucc]
  rw [hfun]

private theorem foldl_apply_periodicChain {α : Type*} {N : ℕ} {U : ZMod N → Set α}
    {Φ : ZMod N → α → α}
    (z : {z : ZMod N → α // ∀ i, z i ∈ U i ∧ Φ i (z i) = z (i + 1)}) (m : ℕ) :
    Fin.foldl m (fun w j ↦ Φ (j : ZMod N) w) (z.1 0) = z.1 m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ_last, Fin.val_last, foldl_castSucc_zmod, ih, Nat.cast_add_one, (z.2 m).2]

/-- **Periodic state sequences vs. fixed initial states of a `ZMod N` chain.** Given domains
`U : ZMod N → Set α` and maps `Φ : ZMod N → α → α`, an initial state `z₀` fixed by the `N`-fold
composite `Fin.foldl N (fun z j ↦ Φ j z)` whose partial composites `Fin.foldl k ... z₀` (`k < N`)
all belong to `U k` corresponds bijectively to a cyclic sequence `z : ZMod N → α` satisfying
`z i ∈ U i` and `Φ i (z i) = z (i + 1)` for every `i`, via `z₀ ↦ fun i ↦ Fin.foldl i.val ... z₀`
and `z ↦ z 0`. -/
def periodicChainFixedPointEquiv {α : Type*} {N : ℕ} [NeZero N]
    (U : ZMod N → Set α) (Φ : ZMod N → α → α) :
    {z₀ : α //
        (∀ k < N, Fin.foldl k (fun z j ↦ Φ (j : ZMod N) z) z₀ ∈ U k) ∧
          Fin.foldl N (fun z j ↦ Φ (j : ZMod N) z) z₀ = z₀} ≃
      {z : ZMod N → α // ∀ i, z i ∈ U i ∧ Φ i (z i) = z (i + 1)} where
  toFun z₀ := ⟨fun i ↦ Fin.foldl i.val (fun z j ↦ Φ (j : ZMod N) z) z₀.1, fun i ↦ by
    refine ⟨by simpa only [ZMod.natCast_zmod_val] using z₀.2.1 i.val i.val_lt, ?_⟩
    dsimp only
    have hsucc : Φ i (Fin.foldl i.val (fun z j ↦ Φ (j : ZMod N) z) z₀.1) =
        Fin.foldl (i.val + 1) (fun z j ↦ Φ (j : ZMod N) z) z₀.1 := by
      rw [Fin.foldl_succ_last, Fin.val_last, ZMod.natCast_zmod_val, foldl_castSucc_zmod]
    rw [hsucc]
    rcases lt_or_eq_of_le (Nat.add_one_le_iff.2 i.val_lt) with hlt | heq
    · have hval : (i + 1).val = i.val + 1 := by
        have hcast : ((i.val + 1 : ℕ) : ZMod N) = i + 1 := by
          push_cast
          rw [ZMod.natCast_zmod_val]
        rw [← hcast, ZMod.val_natCast_of_lt hlt]
      rw [hval]
    · have hi1 : i + 1 = 0 := by
        calc i + 1 = (i.val : ZMod N) + 1 := by rw [ZMod.natCast_zmod_val]
          _ = ((i.val + 1 : ℕ) : ZMod N) := by push_cast; rfl
          _ = (N : ZMod N) := by rw [heq]
          _ = 0 := ZMod.natCast_self N
      rw [heq, hi1, ZMod.val_zero, Fin.foldl_zero]
      exact z₀.2.2⟩
  invFun z := ⟨z.1 0, fun k _ ↦ foldl_apply_periodicChain z k ▸ (z.2 k).1,
    by rw [foldl_apply_periodicChain z N, ZMod.natCast_self]⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv z := Subtype.ext <| funext fun i ↦
    (foldl_apply_periodicChain z i.val).trans (congrArg z.1 (ZMod.natCast_zmod_val i))

/-- `periodicChainFixedPointEquiv` sends a fixed initial state `z₀` to its partial composites along
the chain. -/
@[simp]
theorem periodicChainFixedPointEquiv_apply_coe {α : Type*} {N : ℕ} [NeZero N]
    (U : ZMod N → Set α) (Φ : ZMod N → α → α)
    (z₀ : {z₀ : α //
      (∀ k < N, Fin.foldl k (fun z j ↦ Φ (j : ZMod N) z) z₀ ∈ U k) ∧
        Fin.foldl N (fun z j ↦ Φ (j : ZMod N) z) z₀ = z₀}) (i : ZMod N) :
    (periodicChainFixedPointEquiv U Φ z₀ : ZMod N → α) i =
      Fin.foldl i.val (fun z j ↦ Φ (j : ZMod N) z) z₀.1 :=
  (rfl)

/-- `periodicChainFixedPointEquiv.symm` sends a cyclic state sequence `z` to its initial state
`z 0`. -/
@[simp]
theorem periodicChainFixedPointEquiv_symm_apply_coe {α : Type*} {N : ℕ} [NeZero N]
    (U : ZMod N → Set α) (Φ : ZMod N → α → α)
    (z : {z : ZMod N → α // ∀ i, z i ∈ U i ∧ Φ i (z i) = z (i + 1)}) :
    ((periodicChainFixedPointEquiv U Φ).symm z : α) = z.1 0 :=
  (rfl)

/-- Folding `m` steps of `Φ` from the initial state `(periodicChainFixedPointEquiv U Φ).symm z`
recovers the residue state `z (m : ZMod N)`. -/
theorem foldl_periodicChainFixedPointEquiv_symm_coe {α : Type*} {N : ℕ} [NeZero N]
    (U : ZMod N → Set α) (Φ : ZMod N → α → α)
    (z : {z : ZMod N → α // ∀ i, z i ∈ U i ∧ Φ i (z i) = z (i + 1)}) (m : ℕ) :
    Fin.foldl m (fun w j ↦ Φ (j : ZMod N) w) ((periodicChainFixedPointEquiv U Φ).symm z : α) =
      z.1 m :=
  foldl_apply_periodicChain z m

end TauCeti
