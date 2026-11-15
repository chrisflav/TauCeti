/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import TauCeti.Combinatorics.NoncrossingPartition.Rotate
public import TauCeti.Data.List.Rotate
public import TauCeti.Probability.FreeProbability.Cumulant.Basic

/-!
# Cyclic invariance of free cumulants

Free cumulants are defined from block moments by Möbius inversion on the lattice of noncrossing
partitions, so they transport along any order isomorphism `NC(s) ≃o NC(t)` that matches the block
moments of two words (`TauCeti.partitionCumulant_eq_of_orderIso` and
`TauCeti.freeCumulant_eq_of_orderIso`).

This file applies this in two dual settings:

* For a *tracial* functional `φ (x * y) = φ (y * x)` and an arbitrary word `a₁, …, aₙ`: rotating
  the letters to `a₂, …, aₙ, a₁` (precomposing `a` with `finRotate n`) changes each block moment
  `φ_π` into the block moment of the rotated partition `rotate n π`, since the letters along a
  block containing the last position are only cyclically rotated.
* For an *arbitrary* functional `φ` and a word of pairwise commuting elements (`Commute (a i) (a j)`
  for all `i, j`), such as a word in a normal element and its adjoint: the product along each block
  is unchanged by rotation directly in `A`, so free cumulants are again invariant under cyclic
  rotation without assuming `φ` is tracial. (Unlike moments, free cumulants of commuting elements
  are not invariant under arbitrary permutations because `NC(n)` is only dihedrally symmetric.)

## Main results

* `TauCeti.partitionMoment_comp_finRotate` and `TauCeti.partitionCumulant_comp_finRotate` — for a
  tracial `φ`, rotating the word rotates the partition.
* `TauCeti.freeCumulant_comp_finRotate` and `TauCeti.freeCumulant_comp_finRotate_pow` — free
  cumulants of a tracial `φ` are invariant under cyclic rotation of their arguments.
* `TauCeti.partitionMoment_comp_finRotate_of_commute`,
  `TauCeti.partitionCumulant_comp_finRotate_of_commute`,
  `TauCeti.freeCumulant_comp_finRotate_of_commute`, and
  `TauCeti.freeCumulant_comp_finRotate_pow_of_commute` — the same cyclic invariance for an
  arbitrary `φ` when the entries of the word commute pairwise.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 11.
-/

public section

open Finset

namespace TauCeti

variable {R A : Type*} [Monoid A] {n : ℕ}

section Moment

variable [CommMonoid R] {φ : A → R}

/-- For a tracial `φ`, rotating the letters of a word `a₁, …, aₙ` to `a₂, …, aₙ, a₁` changes the
block moment of a noncrossing partition `π` into the block moment of the rotated partition
`rotate n π`. -/
theorem partitionMoment_comp_finRotate (hφ : ∀ x y, φ (x * y) = φ (y * x)) (a : Fin n → A)
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    partitionMoment φ (a ∘ finRotate n) π.1 =
      partitionMoment φ a (NoncrossingPartition.rotate n π).1 := by
  rw [partitionMoment_def, partitionMoment_def, NoncrossingPartition.prod_parts_rotate]
  refine prod_congr rfl fun B _ => ?_
  -- The two words along `B` differ by a cyclic rotation, which a trace does not see.
  rw [← List.map_map]
  exact ((B.isRotated_sort_map_finRotate).map a).apply_prod_eq hφ

/-- For a word of pairwise commuting elements and an arbitrary functional `φ`, rotating the letters
of `a₁, …, aₙ` to `a₂, …, aₙ, a₁` changes the block moment of a noncrossing partition `π` into
the block moment of `rotate n π`. -/
theorem partitionMoment_comp_finRotate_of_commute (φ : A → R) {a : Fin n → A}
    (ha : ∀ i j, Commute (a i) (a j))
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    partitionMoment φ (a ∘ finRotate n) π.1 =
      partitionMoment φ a (NoncrossingPartition.rotate n π).1 := by
  rw [partitionMoment_def, partitionMoment_def, NoncrossingPartition.prod_parts_rotate]
  refine prod_congr rfl fun B _ => congrArg φ ?_
  rw [← List.map_map]
  exact ((B.isRotated_sort_map_finRotate).map a).perm.prod_eq'
    (List.pairwise_map.mpr (List.pairwise_of_forall fun i j => ha i j))

end Moment

section Cumulant

variable [CommRing R] {φ : A → R}

/-- For a tracial `φ`, rotating the letters of a word `a₁, …, aₙ` to `a₂, …, aₙ, a₁` changes the
free cumulant of a noncrossing partition `π` into that of the rotated partition `rotate n π`. -/
theorem partitionCumulant_comp_finRotate (hφ : ∀ x y, φ (x * y) = φ (y * x)) (a : Fin n → A)
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    partitionCumulant φ (a ∘ finRotate n) π =
      partitionCumulant φ a (NoncrossingPartition.rotate n π) :=
  partitionCumulant_eq_of_orderIso φ _ (partitionMoment_comp_finRotate hφ a) π

/-- **Cyclic invariance of free cumulants.** For a tracial `φ`, the free cumulants are invariant
under cyclic rotation of their arguments, `κ_n(a₂, …, aₙ, a₁) = κ_n(a₁, …, aₙ)`. -/
theorem freeCumulant_comp_finRotate (hφ : ∀ x y, φ (x * y) = φ (y * x)) (a : Fin n → A) :
    freeCumulant φ (a ∘ finRotate n) univ = freeCumulant φ a univ :=
  freeCumulant_eq_of_orderIso φ _ (partitionMoment_comp_finRotate hφ a)

/-- For a tracial `φ`, the free cumulants are invariant under every cyclic rotation of their
arguments, `κ_n(a_{k+1}, …, aₙ, a₁, …, a_k) = κ_n(a₁, …, aₙ)`. -/
theorem freeCumulant_comp_finRotate_pow (hφ : ∀ x y, φ (x * y) = φ (y * x)) (a : Fin n → A)
    (k : ℕ) : freeCumulant φ (a ∘ ⇑(finRotate n ^ k)) univ = freeCumulant φ a univ := by
  rw [Equiv.Perm.coe_pow]
  induction k with
  | zero => rw [Function.iterate_zero, Function.comp_id]
  | succ k ih =>
    rw [Function.iterate_succ, ← Function.comp_assoc, freeCumulant_comp_finRotate hφ, ih]

/-- For a word of pairwise commuting elements and an arbitrary `φ`, rotating the letters of
`a₁, …, aₙ` to `a₂, …, aₙ, a₁` changes the cumulant of `π` into that of `rotate n π`. -/
theorem partitionCumulant_comp_finRotate_of_commute (φ : A → R) {a : Fin n → A}
    (ha : ∀ i j, Commute (a i) (a j))
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    partitionCumulant φ (a ∘ finRotate n) π =
      partitionCumulant φ a (NoncrossingPartition.rotate n π) :=
  partitionCumulant_eq_of_orderIso φ _ (partitionMoment_comp_finRotate_of_commute φ ha) π

/-- For a word of pairwise commuting elements and an arbitrary `φ`, the free cumulants are
invariant under cyclic rotation of their arguments, `κ_n(a₂, …, aₙ, a₁) = κ_n(a₁, …, aₙ)`. -/
theorem freeCumulant_comp_finRotate_of_commute (φ : A → R) {a : Fin n → A}
    (ha : ∀ i j, Commute (a i) (a j)) :
    freeCumulant φ (a ∘ finRotate n) univ = freeCumulant φ a univ :=
  freeCumulant_eq_of_orderIso φ _ (partitionMoment_comp_finRotate_of_commute φ ha)

/-- For a word of pairwise commuting elements and an arbitrary `φ`, the free cumulants are
invariant under every cyclic rotation of their arguments. -/
theorem freeCumulant_comp_finRotate_pow_of_commute (φ : A → R) {a : Fin n → A}
    (ha : ∀ i j, Commute (a i) (a j)) (k : ℕ) :
    freeCumulant φ (a ∘ ⇑(finRotate n ^ k)) univ = freeCumulant φ a univ := by
  rw [Equiv.Perm.coe_pow]
  induction k with
  | zero => rw [Function.iterate_zero, Function.comp_id]
  | succ k ih =>
    rw [Function.iterate_succ, ← Function.comp_assoc,
      freeCumulant_comp_finRotate_of_commute (a := a ∘ (⇑(finRotate n))^[k]) φ
        fun i j => ha _ _, ih]

end Cumulant

end TauCeti
