/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Algebra.Homology.Interleave

/-!
# Bases of interleaved complexes of modules

Let `X₁`, `X₂`, `X₃` be three `ℤ`-indexed families of free modules over a ring `R`, with ordered
bases of ranks `m₁ q`, `m₂ q` and `m₃ q`, and maps making up an interleaved chain complex
`ChainComplex.interleave`. This file assembles bases of the terms of that complex, bases and lifts
of its boundaries from bases and lifts of the images of `δ`, `f` and `g`, and transition
determinants over a commutative ring. The rank in degree `n` is `ChainComplex.interleave.rank`,
which is `m₁ q`, `m₂ q` or `m₃ q` according as `n = 3q + 2`, `3q + 1` or `3q`, and it has finite
support if and only if the three rank functions do
(`ChainComplex.interleave.finite_setOf_rank_ne_zero_iff`).

The main application is the based long exact homology sequence, whose Reidemeister torsion is
the correction term in Milnor's multiplicativity formula
(`TauCeti.Algebra.Homology.ReidemeisterTorsion.HomologySequence`).

## Main declarations

* `ChainComplex.interleave.rank`: the rank function of the interleaved complex.
* `ChainComplex.interleave.basis`: the basis of the interleaved complex in each degree.
* `ChainComplex.interleave.XIso₁_hom_basis` and its two companions: the basis vectors are the given
  ones under the identifications of the terms.
* `ChainComplex.interleave.boundaryBasis` and `ChainComplex.interleave.boundaryLift`: bases of the
  boundaries and lifts in the interleaved complex assembled from bases and lifts of the images of
  `δ`, `f` and `g`.
* `ChainComplex.interleave.basis_det_basis_of_eq_three_mul_add_two` and its two companions:
  determinants between two interleaved bases in each residue class of degrees.
-/

public section

noncomputable section

open CategoryTheory Module

namespace ChainComplex.interleave

section Rank

variable (m₁ m₂ m₃ : ℤ → ℕ)

/-- The rank in degree `n` of an interleaved complex whose three families have ranks
`m₁`, `m₂` and `m₃`: it is `m₃ q`, `m₂ q` or `m₁ q` according as `n = 3q`, `3q + 1` or
`3q + 2`. -/
def rank (n : ℤ) : ℕ :=
  if n % 3 = 0 then m₃ (n / 3) else if n % 3 = 1 then m₂ (n / 3) else m₁ (n / 3)

variable {m₁ m₂ m₃}

theorem rank_of_eq_three_mul_add_two {n q : ℤ} (h : n = 3 * q + 2) : rank m₁ m₂ m₃ n = m₁ q := by
  have h₁ : n % 3 = 2 := by omega
  have h₂ : n / 3 = q := by omega
  simp [rank, h₁, h₂]

theorem rank_of_eq_three_mul_add_one {n q : ℤ} (h : n = 3 * q + 1) : rank m₁ m₂ m₃ n = m₂ q := by
  have h₁ : n % 3 = 1 := by omega
  have h₂ : n / 3 = q := by omega
  simp [rank, h₁, h₂]

theorem rank_of_eq_three_mul {n q : ℤ} (h : n = 3 * q) : rank m₁ m₂ m₃ n = m₃ q := by
  have h₁ : n % 3 = 0 := by omega
  have h₂ : n / 3 = q := by omega
  simp [rank, h₁, h₂]

/-- If each of the three rank functions has finite support, so does `rank`. -/
theorem finite_setOf_rank_ne_zero (h₁ : {q | m₁ q ≠ 0}.Finite) (h₂ : {q | m₂ q ≠ 0}.Finite)
    (h₃ : {q | m₃ q ≠ 0}.Finite) : {n | rank m₁ m₂ m₃ n ≠ 0}.Finite := by
  refine (((h₁.image fun q ↦ 3 * q + 2).union (h₂.image fun q ↦ 3 * q + 1)).union
    (h₃.image fun q ↦ 3 * q)).subset fun n hn ↦ ?_
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q + 2 ∨ n = 3 * q + 1 ∨ n = 3 * q :=
    ⟨n / 3, by omega⟩
  · exact .inl <| .inl ⟨q, (rank_of_eq_three_mul_add_two hq).symm.trans_ne hn, hq.symm⟩
  · exact .inl <| .inr ⟨q, (rank_of_eq_three_mul_add_one hq).symm.trans_ne hn, hq.symm⟩
  · exact .inr ⟨q, (rank_of_eq_three_mul hq).symm.trans_ne hn, hq.symm⟩

/-- `rank` has finite support if and only if each of the three rank functions does. -/
theorem finite_setOf_rank_ne_zero_iff :
    {n | rank m₁ m₂ m₃ n ≠ 0}.Finite ↔
      {q | m₁ q ≠ 0}.Finite ∧ {q | m₂ q ≠ 0}.Finite ∧ {q | m₃ q ≠ 0}.Finite := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun ⟨h₁, h₂, h₃⟩ ↦ finite_setOf_rank_ne_zero h₁ h₂ h₃⟩
  · exact (h.preimage (f := fun q ↦ 3 * q + 2) fun _ _ _ _ (hq : 3 * _ + 2 = 3 * _ + 2) ↦ by
      omega).subset fun q hq ↦ by simpa [rank_of_eq_three_mul_add_two rfl] using hq
  · exact (h.preimage (f := fun q ↦ 3 * q + 1) fun _ _ _ _ (hq : 3 * _ + 1 = 3 * _ + 1) ↦ by
      omega).subset fun q hq ↦ by simpa [rank_of_eq_three_mul_add_one rfl] using hq
  · exact (h.preimage (f := fun q ↦ 3 * q) fun _ _ _ _ (hq : 3 * _ = 3 * _) ↦ by
      omega).subset fun q hq ↦ by simpa [rank_of_eq_three_mul rfl] using hq

end Rank

section Basis

variable {R : Type*} [Ring R] {X₁ X₂ X₃ : ℤ → ModuleCat R} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0)
  (hgδ : ∀ q, g (q + 1) ≫ δ q = 0) (hδf : ∀ q, δ q ≫ f q = 0)

section TermBasis

variable {m₁ m₂ m₃ : ℤ → ℕ} (b₁ : ∀ q, Basis (Fin (m₁ q)) R (X₁ q))
  (b₂ : ∀ q, Basis (Fin (m₂ q)) R (X₂ q)) (b₃ : ∀ q, Basis (Fin (m₃ q)) R (X₃ q))

/-- The basis of the interleaved complex in degree `n`: the basis `b₃ q`, `b₂ q` or `b₁ q`
according as `n = 3q`, `3q + 1` or `3q + 2`, transported along the identification of the term. -/
def basis (n : ℤ) :
    Basis (Fin (rank m₁ m₂ m₃ n)) R ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X n) :=
  if _ : n % 3 = 0 then
    ((b₃ (n / 3)).reindex (finCongr (rank_of_eq_three_mul (by omega)).symm)).map
      (XIso₃ hfg hgδ hδf n (n / 3) (by omega)).symm.toLinearEquiv
  else if _ : n % 3 = 1 then
    ((b₂ (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_one (by omega)).symm)).map
      (XIso₂ hfg hgδ hδf n (n / 3) (by omega)).symm.toLinearEquiv
  else
    ((b₁ (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_two (by omega)).symm)).map
      (XIso₁ hfg hgδ hδf n (n / 3) (by omega)).symm.toLinearEquiv

/-- In degree `n = 3q + 2` the basis of the interleaved complex is `b₁ q`. -/
@[simp]
theorem XIso₁_hom_basis {n q : ℤ} (h : n = 3 * q + 2) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₁ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₁ q (Fin.cast (rank_of_eq_three_mul_add_two h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

/-- In degree `n = 3q + 1` the basis of the interleaved complex is `b₂ q`. -/
@[simp]
theorem XIso₂_hom_basis {n q : ℤ} (h : n = 3 * q + 1) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₂ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₂ q (Fin.cast (rank_of_eq_three_mul_add_one h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

/-- In degree `n = 3q` the basis of the interleaved complex is `b₃ q`. -/
@[simp]
theorem XIso₃_hom_basis {n q : ℤ} (h : n = 3 * q) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₃ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₃ q (Fin.cast (rank_of_eq_three_mul h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_left (by omega)]
  simp

end TermBasis

section Boundary

private theorem map_range_δ {n q : ℤ} (h : n = 3 * q + 2) :
    (LinearMap.range (δ q).hom).map
        (XIso₁ hfg hgδ hδf n q h).symm.toLinearEquiv.toLinearMap =
      LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom := by
  rw [interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf h, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_assoc, LinearMap.range_comp]
  exact congrArg (Submodule.map (XIso₁ hfg hgδ hδf n q h).inv.hom)
    (LinearMap.range_comp_of_range_eq_top (δ q).hom
      (XIso₃ hfg hgδ hδf (n + 1) (q + 1) (by omega)).toLinearEquiv.range).symm

private theorem map_range_f {n q : ℤ} (h : n = 3 * q + 1) :
    (LinearMap.range (f q).hom).map
        (XIso₂ hfg hgδ hδf n q h).symm.toLinearEquiv.toLinearMap =
      LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom := by
  rw [interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf h, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_assoc, LinearMap.range_comp]
  exact congrArg (Submodule.map (XIso₂ hfg hgδ hδf n q h).inv.hom)
    (LinearMap.range_comp_of_range_eq_top (f q).hom
      (XIso₁ hfg hgδ hδf (n + 1) q (by omega)).toLinearEquiv.range).symm

private theorem map_range_g {n q : ℤ} (h : n = 3 * q) :
    (LinearMap.range (g q).hom).map
        (XIso₃ hfg hgδ hδf n q h).symm.toLinearEquiv.toLinearMap =
      LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom := by
  rw [interleave_d_eq_of_eq_three_mul hfg hgδ hδf h, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_assoc, LinearMap.range_comp]
  exact congrArg (Submodule.map (XIso₃ hfg hgδ hδf n q h).inv.hom)
    (LinearMap.range_comp_of_range_eq_top (g q).hom
      (XIso₂ hfg hgδ hδf (n + 1) q (by omega)).toLinearEquiv.range).symm

/-- The isomorphism between `range (δ q)` and the boundaries of `ChainComplex.interleave` in degree
`n = 3q + 2`. -/
def boundaryEquiv₁ {n q : ℤ} (h : n = 3 * q + 2) :
    LinearMap.range (δ q).hom ≃ₗ[R]
      LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom :=
  ((XIso₁ hfg hgδ hδf n q h).symm.toLinearEquiv.submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (map_range_δ hfg hgδ hδf h))

/-- The isomorphism between `range (f q)` and the boundaries of `ChainComplex.interleave` in degree
`n = 3q + 1`. -/
def boundaryEquiv₂ {n q : ℤ} (h : n = 3 * q + 1) :
    LinearMap.range (f q).hom ≃ₗ[R]
      LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom :=
  ((XIso₂ hfg hgδ hδf n q h).symm.toLinearEquiv.submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (map_range_f hfg hgδ hδf h))

/-- The isomorphism between `range (g q)` and the boundaries of `ChainComplex.interleave` in degree
`n = 3q`. -/
def boundaryEquiv₃ {n q : ℤ} (h : n = 3 * q) :
    LinearMap.range (g q).hom ≃ₗ[R]
      LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom :=
  ((XIso₃ hfg hgδ hδf n q h).symm.toLinearEquiv.submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (map_range_g hfg hgδ hδf h))

/-- Coercing `boundaryEquiv₁` to the ambient term applies `(XIso₁ ...).inv`. -/
@[simp]
theorem coe_boundaryEquiv₁ {n q : ℤ} (h : n = 3 * q + 2) (x : LinearMap.range (δ q).hom) :
    (boundaryEquiv₁ hfg hgδ hδf h x : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X n) =
      (XIso₁ hfg hgδ hδf n q h).inv x :=
  (rfl)

/-- Coercing `boundaryEquiv₂` to the ambient term applies `(XIso₂ ...).inv`. -/
@[simp]
theorem coe_boundaryEquiv₂ {n q : ℤ} (h : n = 3 * q + 1) (x : LinearMap.range (f q).hom) :
    (boundaryEquiv₂ hfg hgδ hδf h x : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X n) =
      (XIso₂ hfg hgδ hδf n q h).inv x :=
  (rfl)

/-- Coercing `boundaryEquiv₃` to the ambient term applies `(XIso₃ ...).inv`. -/
@[simp]
theorem coe_boundaryEquiv₃ {n q : ℤ} (h : n = 3 * q) (x : LinearMap.range (g q).hom) :
    (boundaryEquiv₃ hfg hgδ hδf h x : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X n) =
      (XIso₃ hfg hgδ hδf n q h).inv x :=
  (rfl)

variable {r₁ r₂ r₃ : ℤ → ℕ}
  (u : ∀ q, Basis (Fin (r₁ q)) R (LinearMap.range (δ q).hom))
  (v : ∀ q, Basis (Fin (r₂ q)) R (LinearMap.range (f q).hom))
  (w : ∀ q, Basis (Fin (r₃ q)) R (LinearMap.range (g q).hom))

/-- The basis of the boundaries of `ChainComplex.interleave` in degree `n`, assembled from bases
`u q` of `range (δ q)`, `v q` of `range (f q)` and `w q` of `range (g q)`. -/
def boundaryBasis (n : ℤ) :
    Basis (Fin (rank r₁ r₂ r₃ n)) R
      (LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom) :=
  if _ : n % 3 = 0 then
    ((w (n / 3)).reindex (finCongr (rank_of_eq_three_mul (by omega)).symm)).map
      (boundaryEquiv₃ hfg hgδ hδf (by omega))
  else if _ : n % 3 = 1 then
    ((v (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_one (by omega)).symm)).map
      (boundaryEquiv₂ hfg hgδ hδf (by omega))
  else
    ((u (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_two (by omega)).symm)).map
      (boundaryEquiv₁ hfg hgδ hδf (by omega))

/-- In degree `n = 3q + 2`, `boundaryBasis` identifies with `u q` under `XIso₁`. -/
@[simp]
theorem XIso₁_hom_boundaryBasis {n q : ℤ} (h : n = 3 * q + 2) (i : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₁ hfg hgδ hδf n q h).hom (boundaryBasis hfg hgδ hδf u v w n i) =
      u q (Fin.cast (rank_of_eq_three_mul_add_two h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryBasis, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

/-- In degree `n = 3q + 1`, `boundaryBasis` identifies with `v q` under `XIso₂`. -/
@[simp]
theorem XIso₂_hom_boundaryBasis {n q : ℤ} (h : n = 3 * q + 1) (i : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₂ hfg hgδ hδf n q h).hom (boundaryBasis hfg hgδ hδf u v w n i) =
      v q (Fin.cast (rank_of_eq_three_mul_add_one h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryBasis, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

/-- In degree `n = 3q`, `boundaryBasis` identifies with `w q` under `XIso₃`. -/
@[simp]
theorem XIso₃_hom_boundaryBasis {n q : ℤ} (h : n = 3 * q) (i : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₃ hfg hgδ hδf n q h).hom (boundaryBasis hfg hgδ hδf u v w n i) =
      w q (Fin.cast (rank_of_eq_three_mul h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryBasis, dite_eq_left (by omega)]
  simp

end Boundary

section BoundaryLift

variable {r₁ r₂ r₃ : ℤ → ℕ} (sf : ∀ q, Fin (r₂ q) → X₁ q) (sg : ∀ q, Fin (r₃ q) → X₂ q)
  (sδ : ∀ q, Fin (r₁ q) → X₃ (q + 1))

/-- Lifts of `boundaryBasis` in `ChainComplex.interleave` assembled from lifts `sf`, `sg` and `sδ`
along `f`, `g` and `δ`. -/
def boundaryLift (n : ℤ) (i : Fin (rank r₁ r₂ r₃ n)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X (n + 1) :=
  if _ : n % 3 = 0 then
    (XIso₂ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv
      (sg (n / 3) (Fin.cast (rank_of_eq_three_mul (by omega)) i))
  else if _ : n % 3 = 1 then
    (XIso₁ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv
      (sf (n / 3) (Fin.cast (rank_of_eq_three_mul_add_one (by omega)) i))
  else
    (XIso₃ hfg hgδ hδf (n + 1) (n / 3 + 1) (by omega)).inv
      (sδ (n / 3) (Fin.cast (rank_of_eq_three_mul_add_two (by omega)) i))

/-- When `n + 1 = 3q + 2`, `boundaryLift` identifies with `sf q` under `XIso₁`. -/
@[simp]
theorem XIso₁_hom_boundaryLift {n q : ℤ} (h : n + 1 = 3 * q + 2) (i : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₁ hfg hgδ hδf (n + 1) q h).hom (boundaryLift hfg hgδ hδf sf sg sδ n i) =
      sf q (Fin.cast (rank_of_eq_three_mul_add_one (by omega)) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryLift, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

/-- When `n + 1 = 3q + 1`, `boundaryLift` identifies with `sg q` under `XIso₂`. -/
@[simp]
theorem XIso₂_hom_boundaryLift {n q : ℤ} (h : n + 1 = 3 * q + 1) (i : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₂ hfg hgδ hδf (n + 1) q h).hom (boundaryLift hfg hgδ hδf sf sg sδ n i) =
      sg q (Fin.cast (rank_of_eq_three_mul (by omega)) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryLift, dite_eq_left (by omega)]
  simp

/-- When `n + 1 = 3(q + 1)`, `boundaryLift` identifies with `sδ q` under `XIso₃`. -/
@[simp]
theorem XIso₃_hom_boundaryLift {n q : ℤ} (h : n + 1 = 3 * (q + 1)) (i : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₃ hfg hgδ hδf (n + 1) (q + 1) h).hom (boundaryLift hfg hgδ hδf sf sg sδ n i) =
      sδ q (Fin.cast (rank_of_eq_three_mul_add_two (by omega)) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryLift, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

/-- The differential of `ChainComplex.interleave` sends `boundaryLift` to `boundaryBasis`. -/
theorem d_boundaryLift (u : ∀ q, Basis (Fin (r₁ q)) R (LinearMap.range (δ q).hom))
    (v : ∀ q, Basis (Fin (r₂ q)) R (LinearMap.range (f q).hom))
    (w : ∀ q, Basis (Fin (r₃ q)) R (LinearMap.range (g q).hom))
    (hsf : ∀ q k, (f q).hom (sf q k) = v q k)
    (hsg : ∀ q k, (g q).hom (sg q k) = w q k) (hsδ : ∀ q k, (δ q).hom (sδ q k) = u q k)
    (n : ℤ) (i : Fin (rank r₁ r₂ r₃ n)) :
    ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom
      (boundaryLift hfg hgδ hδf sf sg sδ n i) = boundaryBasis hfg hgδ hδf u v w n i := by
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q + 2 ∨ n = 3 * q + 1 ∨ n = 3 * q :=
    ⟨n / 3, by omega⟩
  · apply (XIso₁ hfg hgδ hδf n q hq).toLinearEquiv.injective
    simp [interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf hq, hsδ]
  · apply (XIso₂ hfg hgδ hδf n q hq).toLinearEquiv.injective
    simp [interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf hq, hsf]
  · apply (XIso₃ hfg hgδ hδf n q hq).toLinearEquiv.injective
    simp [interleave_d_eq_of_eq_three_mul hfg hgδ hδf hq, hsg]

end BoundaryLift

end Basis

section CommRing

variable {R : Type*} [CommRing R] {X₁ X₂ X₃ : ℤ → ModuleCat R} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0)
  (hgδ : ∀ q, g (q + 1) ≫ δ q = 0) (hδf : ∀ q, δ q ≫ f q = 0)
  {m₁ m₂ m₃ : ℤ → ℕ} (b₁ b₁' : ∀ q, Basis (Fin (m₁ q)) R (X₁ q))
  (b₂ b₂' : ∀ q, Basis (Fin (m₂ q)) R (X₂ q)) (b₃ b₃' : ∀ q, Basis (Fin (m₃ q)) R (X₃ q))

/-- In degree `n = 3q + 2`, the determinant of one interleaved basis with respect to another is
`(b₁ q).det (b₁' q)`. -/
theorem basis_det_basis_of_eq_three_mul_add_two {n q : ℤ} (h : n = 3 * q + 2) :
    (basis hfg hgδ hδf b₁ b₂ b₃ n).det (basis hfg hgδ hδf b₁' b₂' b₃' n) =
      (b₁ q).det (b₁' q) := by
  have hb : basis hfg hgδ hδf b₁ b₂ b₃ n =
      ((b₁ q).reindex (finCongr (rank_of_eq_three_mul_add_two h).symm)).map
        (XIso₁ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    Basis.eq_of_apply_eq fun i ↦ (XIso₁ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  have hb' : basis hfg hgδ hδf b₁' b₂' b₃' n =
      ((b₁' q).reindex (finCongr (rank_of_eq_three_mul_add_two h).symm)).map
        (XIso₁ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    Basis.eq_of_apply_eq fun i ↦ (XIso₁ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  rw [hb, hb', Basis.det_map, Basis.det_reindex]
  congr 1
  ext
  simp

/-- In degree `n = 3q + 1`, the determinant of one interleaved basis with respect to another is
`(b₂ q).det (b₂' q)`. -/
theorem basis_det_basis_of_eq_three_mul_add_one {n q : ℤ} (h : n = 3 * q + 1) :
    (basis hfg hgδ hδf b₁ b₂ b₃ n).det (basis hfg hgδ hδf b₁' b₂' b₃' n) =
      (b₂ q).det (b₂' q) := by
  have hb : basis hfg hgδ hδf b₁ b₂ b₃ n =
      ((b₂ q).reindex (finCongr (rank_of_eq_three_mul_add_one h).symm)).map
        (XIso₂ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    Basis.eq_of_apply_eq fun i ↦ (XIso₂ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  have hb' : basis hfg hgδ hδf b₁' b₂' b₃' n =
      ((b₂' q).reindex (finCongr (rank_of_eq_three_mul_add_one h).symm)).map
        (XIso₂ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    Basis.eq_of_apply_eq fun i ↦ (XIso₂ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  rw [hb, hb', Basis.det_map, Basis.det_reindex]
  congr 1
  ext
  simp

/-- In degree `n = 3q`, the determinant of one interleaved basis with respect to another is
`(b₃ q).det (b₃' q)`. -/
theorem basis_det_basis_of_eq_three_mul {n q : ℤ} (h : n = 3 * q) :
    (basis hfg hgδ hδf b₁ b₂ b₃ n).det (basis hfg hgδ hδf b₁' b₂' b₃' n) =
      (b₃ q).det (b₃' q) := by
  have hb : basis hfg hgδ hδf b₁ b₂ b₃ n =
      ((b₃ q).reindex (finCongr (rank_of_eq_three_mul h).symm)).map
        (XIso₃ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    Basis.eq_of_apply_eq fun i ↦ (XIso₃ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  have hb' : basis hfg hgδ hδf b₁' b₂' b₃' n =
      ((b₃' q).reindex (finCongr (rank_of_eq_three_mul h).symm)).map
        (XIso₃ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    Basis.eq_of_apply_eq fun i ↦ (XIso₃ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  rw [hb, hb', Basis.det_map, Basis.det_reindex]
  congr 1
  ext
  simp

end CommRing

end ChainComplex.interleave
