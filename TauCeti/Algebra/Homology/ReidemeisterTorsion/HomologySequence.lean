/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Interleave
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Homology
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Alternating.Append
import TauCeti.LinearAlgebra.Exact

/-!
# The based long exact homology sequence and Milnor's multiplicativity formula

Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of
vector spaces over a field `F`. Its long exact homology sequence is the acyclic chain complex
`CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`, with `Hᵢ(S.X₁)`, `Hᵢ(S.X₂)` and
`Hᵢ(S.X₃)` in degrees `3i + 2`, `3i + 1` and `3i`. Ordered bases of the homology groups give
ordered bases of its terms (`ChainComplex.interleave.basis`), and the resulting Reidemeister
torsion is a nonzero scalar once only finitely many homology groups are nonzero
(`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`).

This scalar is the correction term in Milnor's formula for the torsion with homology bases of a
short exact sequence of complexes that need not be acyclic: with compatible chain bases and any
homology bases, `τ(S.X₂) = ε · τ(S.X₁) · τ(S.X₃) · τ(H)`, where `H` is the based long exact
homology sequence and `ε` is the Koszul sign arising from de-interleaving the boundaries, homology
representatives and lifts
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`). Specializations
handle an acyclic middle complex, split short exact sequences and biproducts.

## Main declarations

* `ChainComplex.interleave.reidemeisterTorsion_basis_eq_mul`: the basis-change formula for the
  Reidemeister torsion of an interleaved complex.
* `ChainComplex.interleave.reidemeisterTorsion_eq_one_of_append`: a bounded interleaved complex
  whose bases are assembled from bases and lifts of the images is acyclic and has torsion `1`.
* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`: the
  based long exact homology sequence has nonzero torsion.
* `CategoryTheory.ShortComplex.ShortExact.card_homology_basis_eq_of_acyclic_X₂` and
  `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_of_acyclic_X₂`
  compute the torsion of the homology sequence from the connecting isomorphisms when `S.X₂` is
  acyclic.
* `CategoryTheory.ShortComplex.Splitting.reidemeisterTorsion_homologySequenceComplex`: for a split
  short exact sequence with compatible homology bases, the homology sequence has torsion `1`.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`: Milnor's
  multiplicativity formula for a short exact sequence of based complexes with homology bases.
* `HomologicalComplex.reidemeisterTorsion_eq_mul_reidemeisterTorsionWithHomology_of_shortExact`:
  specialization when the middle complex is acyclic.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_splitting` and
  `HomologicalComplex.reidemeisterTorsionWithHomology_biprod`: specializations to split short exact
  sequences and biproducts.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorem 1.14.
-/

public section

noncomputable section

open CategoryTheory Limits Module

namespace ChainComplex.interleave

/-- Partition of `ℤ` into the three residue classes `3q + 2`, `3q + 1` and `3q`. -/
private def modThreeEquiv : (ℤ ⊕ ℤ) ⊕ ℤ ≃ ℤ where
  toFun
    | .inl (.inl q) => 3 * q + 2
    | .inl (.inr q) => 3 * q + 1
    | .inr q => 3 * q
  invFun n :=
    if n % 3 = 0 then .inr (n / 3) else if n % 3 = 1 then .inl (.inr (n / 3)) else
      .inl (.inl (n / 3))
  left_inv := by
    rintro ((q | q) | q) <;> dsimp only
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; congr 2; omega
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; congr 2; omega
    · rw [ite_eq_left (by omega)]; congr 1; omega
  right_inv n := by
    dsimp only
    split_ifs <;> dsimp only <;> omega

/-- A finitely supported product over `ℤ` splits into the products over `3q + 2`, `3q + 1` and
`3q`. -/
private theorem finprod_modThree {M : Type*} [CommMonoid M] (φ : ℤ → M)
    (hφ : Function.HasFiniteMulSupport φ) :
    ∏ᶠ n : ℤ, φ n =
      (∏ᶠ q : ℤ, φ (3 * q + 2)) * (∏ᶠ q : ℤ, φ (3 * q + 1)) * ∏ᶠ q : ℤ, φ (3 * q) := by
  have h₂ : Function.HasFiniteMulSupport fun q ↦ φ (3 * q + 2) :=
    hφ.preimage fun _ _ _ _ (h : 3 * _ + 2 = 3 * _ + 2) ↦ by omega
  have h₁ : Function.HasFiniteMulSupport fun q ↦ φ (3 * q + 1) :=
    hφ.preimage fun _ _ _ _ (h : 3 * _ + 1 = 3 * _ + 1) ↦ by omega
  have h₀ : Function.HasFiniteMulSupport fun q ↦ φ (3 * q) :=
    hφ.preimage fun _ _ _ _ (h : 3 * _ = 3 * _) ↦ by omega
  rw [← finprod_comp_equiv modThreeEquiv,
    TauCeti.finprod_sum_type _ (TauCeti.hasFiniteMulSupport_sum_type h₂ h₁) h₀,
    TauCeti.finprod_sum_type _ h₂ h₁]
  rfl

variable {F : Type*} [Field F] {X₁ X₂ X₃ : ℤ → ModuleCat F} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0)
  (hgδ : ∀ q, g (q + 1) ≫ δ q = 0) (hδf : ∀ q, δ q ≫ f q = 0)

/-- Changing the bases `(b₁, b₂, b₃)` of an interleaved complex to `(b₁', b₂', b₃')` multiplies
its Reidemeister torsion by the alternating transition determinants in each family, with exponents
`(-1) ^ q` on the first and third families and `(-1) ^ (q + 1)` on the middle one. This holds for
every interleaved complex, both sides being `0` when it is unbounded or not acyclic. -/
theorem reidemeisterTorsion_basis_eq_mul {m₁ m₂ m₃ : ℤ → ℕ}
    (b₁ b₁' : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
    (b₂ b₂' : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ b₃' : ∀ q, Basis (Fin (m₃ q)) F (X₃ q)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
        (basis hfg hgδ hδf b₁' b₂' b₃') =
      (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
          (basis hfg hgδ hδf b₁ b₂ b₃) *
        ((∏ᶠ q : ℤ, (b₁ q).det (b₁' q) ^ (q.negOnePow : ℤ)) *
          (∏ᶠ q : ℤ, (b₂ q).det (b₂' q) ^ ((q + 1).negOnePow : ℤ)) *
          ∏ᶠ q : ℤ, (b₃ q).det (b₃' q) ^ (q.negOnePow : ℤ)) := by
  by_cases hn : {n | rank m₁ m₂ m₃ n ≠ 0}.Finite
  swap
  · simp [HomologicalComplex.reidemeisterTorsion_of_not_finite _ _ hn]
  have hsupp : Function.HasFiniteMulSupport fun n : ℤ ↦
      (basis hfg hgδ hδf b₁ b₂ b₃ n).det (basis hfg hgδ hδf b₁' b₂' b₃' n) ^
        (n.negOnePow : ℤ) :=
    hn.subset <| Function.mulSupport_subset_iff'.2 fun n hn₀ ↦ by
      have : IsEmpty (Fin (rank m₁ m₂ m₃ n)) := by
        rw [show rank m₁ m₂ m₃ n = 0 by simpa using hn₀]; infer_instance
      simp
  rw [HomologicalComplex.reidemeisterTorsion_eq_mul_finprod_det _
    (basis hfg hgδ hδf b₁ b₂ b₃), finprod_modThree _ hsupp]
  congr 2
  · congr 1
    · exact finprod_congr fun q ↦ by
        rw [basis_det_basis_of_eq_three_mul_add_two hfg hgδ hδf _ _ _ _ _ _ rfl,
          (Int.negOnePow_eq_iff (3 * q + 2) q).2 ⟨q + 1, by omega⟩]
    · exact finprod_congr fun q ↦ by
        rw [basis_det_basis_of_eq_three_mul_add_one hfg hgδ hδf _ _ _ _ _ _ rfl,
          (Int.negOnePow_eq_iff (3 * q + 1) (q + 1)).2 ⟨q, by omega⟩]
  · exact finprod_congr fun q ↦ by
      rw [basis_det_basis_of_eq_three_mul hfg hgδ hδf _ _ _ _ _ _ rfl,
        (Int.negOnePow_eq_iff (3 * q) q).2 ⟨q, by omega⟩]

private theorem append_boundaryBasis_boundaryLift_eq_basis
    {m₁ m₂ m₃ r₁ r₂ r₃ : ℤ → ℕ}
    (b₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
    (b₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))
    (u : ∀ q, Basis (Fin (r₁ q)) F (LinearMap.range (δ q).hom))
    (v : ∀ q, Basis (Fin (r₂ q)) F (LinearMap.range (f q).hom))
    (w : ∀ q, Basis (Fin (r₃ q)) F (LinearMap.range (g q).hom))
    (sf : ∀ q, Fin (r₂ q) → X₁ q) (sg : ∀ q, Fin (r₃ q) → X₂ q)
    (sδ : ∀ q, Fin (r₁ q) → X₃ (q + 1))
    (hm₁ : ∀ q, m₁ q = r₁ q + r₂ q) (hm₂ : ∀ q, m₂ q = r₂ q + r₃ q)
    (hm₃ : ∀ q, m₃ (q + 1) = r₃ (q + 1) + r₁ q)
    (hb₁ : ∀ q, ⇑(b₁ q) = Fin.append (fun k ↦ (u q k : X₁ q)) (sf q) ∘ Fin.cast (hm₁ q))
    (hb₂ : ∀ q, ⇑(b₂ q) = Fin.append (fun k ↦ (v q k : X₂ q)) (sg q) ∘ Fin.cast (hm₂ q))
    (hb₃ : ∀ q, ⇑(b₃ (q + 1)) =
      Fin.append (fun k ↦ (w (q + 1) k : X₃ (q + 1))) (sδ q) ∘ Fin.cast (hm₃ q))
    (j : ℤ) (hrk : rank m₁ m₂ m₃ (j + 1) =
      rank r₁ r₂ r₃ (j + 1) + rank r₁ r₂ r₃ j) :
    Fin.append (fun l ↦ (boundaryBasis hfg hgδ hδf u v w (j + 1) l :
        (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X (j + 1)))
      (boundaryLift hfg hgδ hδf sf sg sδ j) ∘ Fin.cast hrk =
      ⇑(basis hfg hgδ hδf b₁ b₂ b₃ (j + 1)) := by
  ext l
  obtain ⟨m, rfl⟩ := (finCongr hrk.symm).surjective l
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, j + 1 = 3 * q + 2 ∨ j + 1 = 3 * q + 1 ∨ j + 1 = 3 * (q + 1) :=
    ⟨j / 3, by omega⟩
  · apply (XIso₁ hfg hgδ hδf (j + 1) q hq).toLinearEquiv.injective
    have hr₁ := rank_of_eq_three_mul_add_two (m₁ := r₁) (m₂ := r₂) (m₃ := r₃) hq
    induction m using Fin.addCases with
    | left k =>
      simp only [finCongr_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        Fin.append_left, Iso.toLinearEquiv_apply, XIso₁_hom_boundaryBasis, XIso₁_hom_basis, hb₁ q]
      rw [show (Fin.cast _ (Fin.castAdd _ k) : Fin (r₁ q + r₂ q)) =
        Fin.castAdd (r₂ q) (Fin.cast hr₁ k) from Fin.ext (by simp), Fin.append_left]
    | right k =>
      simp only [finCongr_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        Fin.append_right, Iso.toLinearEquiv_apply, XIso₁_hom_boundaryLift, XIso₁_hom_basis, hb₁ q]
      rw [show (Fin.cast _ (Fin.natAdd _ k) : Fin (r₁ q + r₂ q)) =
        Fin.natAdd (r₁ q) (Fin.cast (rank_of_eq_three_mul_add_one (by omega)) k) from
          Fin.ext (by simp [hr₁]), Fin.append_right]
  · apply (XIso₂ hfg hgδ hδf (j + 1) q hq).toLinearEquiv.injective
    have hr₂ := rank_of_eq_three_mul_add_one (m₁ := r₁) (m₂ := r₂) (m₃ := r₃) hq
    induction m using Fin.addCases with
    | left k =>
      simp only [finCongr_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        Fin.append_left, Iso.toLinearEquiv_apply, XIso₂_hom_boundaryBasis, XIso₂_hom_basis, hb₂ q]
      rw [show (Fin.cast _ (Fin.castAdd _ k) : Fin (r₂ q + r₃ q)) =
        Fin.castAdd (r₃ q) (Fin.cast hr₂ k) from Fin.ext (by simp), Fin.append_left]
    | right k =>
      simp only [finCongr_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        Fin.append_right, Iso.toLinearEquiv_apply, XIso₂_hom_boundaryLift, XIso₂_hom_basis, hb₂ q]
      rw [show (Fin.cast _ (Fin.natAdd _ k) : Fin (r₂ q + r₃ q)) =
        Fin.natAdd (r₂ q) (Fin.cast (rank_of_eq_three_mul (by omega)) k) from
          Fin.ext (by simp [hr₂]), Fin.append_right]
  · apply (XIso₃ hfg hgδ hδf (j + 1) (q + 1) hq).toLinearEquiv.injective
    have hr₃ := rank_of_eq_three_mul (m₁ := r₁) (m₂ := r₂) (m₃ := r₃) hq
    induction m using Fin.addCases with
    | left k =>
      simp only [finCongr_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        Fin.append_left, Iso.toLinearEquiv_apply, XIso₃_hom_boundaryBasis, XIso₃_hom_basis, hb₃ q]
      rw [show (Fin.cast _ (Fin.castAdd _ k) : Fin (r₃ (q + 1) + r₁ q)) =
        Fin.castAdd (r₁ q) (Fin.cast hr₃ k) from Fin.ext (by simp), Fin.append_left]
    | right k =>
      simp only [finCongr_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        Fin.append_right, Iso.toLinearEquiv_apply, XIso₃_hom_boundaryLift, XIso₃_hom_basis, hb₃ q]
      rw [show (Fin.cast _ (Fin.natAdd _ k) : Fin (r₃ (q + 1) + r₁ q)) =
        Fin.natAdd (r₃ (q + 1)) (Fin.cast (rank_of_eq_three_mul_add_two (by omega)) k) from
          Fin.ext (by simp [hr₃]), Fin.append_right]

private theorem shortComplex_exact_of_card_basis_eq {M N P : ModuleCat F} {φ : M ⟶ N} {ψ : N ⟶ P}
    (hφψ : φ ≫ ψ = 0) {m r₁ r₂ : ℕ} (b : Basis (Fin m) F N)
    (u : Basis (Fin r₁) F (LinearMap.range φ.hom)) (v : Basis (Fin r₂) F (LinearMap.range ψ.hom))
    (hm : m = r₁ + r₂) : (ShortComplex.mk φ ψ hφψ).Exact := by
  have : FiniteDimensional F N := .of_basis b
  have hle : LinearMap.range φ.hom ≤ LinearMap.ker ψ.hom := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hφψ) x
  have hdim := LinearMap.finrank_range_add_finrank_ker ψ.hom
  rw [finrank_eq_card_basis b, finrank_eq_card_basis v, Fintype.card_fin, Fintype.card_fin] at hdim
  refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    (LinearMap.exact_iff.2 (Submodule.eq_of_le_of_finrank_eq hle ?_).symm)
  rw [finrank_eq_card_basis u, Fintype.card_fin]
  omega

/-- An interleaved complex whose first and third rank functions have finite support and whose bases
in each degree list a basis of the incoming image followed by lifts of a basis of the outgoing
image is acyclic and has Reidemeister torsion `1`. -/
theorem reidemeisterTorsion_eq_one_of_append {m₁ m₂ m₃ r₁ r₂ r₃ : ℤ → ℕ}
    (b₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
    (b₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))
    (h₁ : {q | m₁ q ≠ 0}.Finite) (h₃ : {q | m₃ q ≠ 0}.Finite)
    (u : ∀ q, Basis (Fin (r₁ q)) F (LinearMap.range (δ q).hom))
    (v : ∀ q, Basis (Fin (r₂ q)) F (LinearMap.range (f q).hom))
    (w : ∀ q, Basis (Fin (r₃ q)) F (LinearMap.range (g q).hom))
    (sf : ∀ q, Fin (r₂ q) → X₁ q) (hsf : ∀ q k, (f q).hom (sf q k) = v q k)
    (sg : ∀ q, Fin (r₃ q) → X₂ q) (hsg : ∀ q k, (g q).hom (sg q k) = w q k)
    (sδ : ∀ q, Fin (r₁ q) → X₃ (q + 1)) (hsδ : ∀ q k, (δ q).hom (sδ q k) = u q k)
    (hm₁ : ∀ q, m₁ q = r₁ q + r₂ q) (hm₂ : ∀ q, m₂ q = r₂ q + r₃ q)
    (hm₃ : ∀ q, m₃ (q + 1) = r₃ (q + 1) + r₁ q)
    (hb₁ : ∀ q, ⇑(b₁ q) = Fin.append (fun k ↦ (u q k : X₁ q)) (sf q) ∘ Fin.cast (hm₁ q))
    (hb₂ : ∀ q, ⇑(b₂ q) = Fin.append (fun k ↦ (v q k : X₂ q)) (sg q) ∘ Fin.cast (hm₂ q))
    (hb₃ : ∀ q, ⇑(b₃ (q + 1)) =
      Fin.append (fun k ↦ (w (q + 1) k : X₃ (q + 1))) (sδ q) ∘ Fin.cast (hm₃ q)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
      (basis hfg hgδ hδf b₁ b₂ b₃) = 1 := by
  have hK : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic :=
    (ChainComplex.acyclic_interleave_iff _ _ _).2
      ⟨fun q ↦ shortComplex_exact_of_card_basis_eq (hδf q) (b₁ q) (u q) (v q) (hm₁ q),
        fun q ↦ shortComplex_exact_of_card_basis_eq (hfg q) (b₂ q) (v q) (w q) (hm₂ q),
        fun q ↦ shortComplex_exact_of_card_basis_eq (hgδ q) (b₃ (q + 1)) (w (q + 1)) (u q) (hm₃ q)⟩
  -- Finiteness of `m₂` follows from `m₂ q = r₂ q + r₃ q` and `r₂ q ≤ m₁ q`, `r₃ q ≤ m₃ q`.
  have h₂ : {q | m₂ q ≠ 0}.Finite := (h₁.union h₃).subset fun q hq ↦ by
    have hq' := hm₃ (q - 1)
    rw [sub_add_cancel] at hq'
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hq ⊢
    have := hm₁ q; have := hm₂ q; omega
  rw [HomologicalComplex.reidemeisterTorsion_eq_finprod (finite_setOf_rank_ne_zero h₁ h₂ h₃) hK
    (boundaryBasis hfg hgδ hδf u v w) (boundaryLift hfg hgδ hδf sf sg sδ)
    (d_boundaryLift hfg hgδ hδf sf sg sδ u v w hsf hsg hsδ)]
  refine (finprod_congr fun j ↦ ?_).trans finprod_one
  have hrk := HomologicalComplex.eq_add_of_exactAt (basis hfg hgδ hδf b₁ b₂ b₃) (j := j + 1)
    (by simp) (by simp) (hK (j + 1)) (boundaryBasis hfg hgδ hδf u v w (j + 1))
    (boundaryBasis hfg hgδ hδf u v w j)
  rw [HomologicalComplex.torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hrk,
    append_boundaryBasis_boundaryLift_eq_basis hfg hgδ hδf b₁ b₂ b₃ u v w sf sg sδ
      hm₁ hm₂ hm₃ hb₁ hb₂ hb₃ j hrk,
    Basis.det_self, one_zpow]

end ChainComplex.interleave

namespace CategoryTheory.ShortComplex.ShortExact

variable {F : Type*} [Field F] {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
  (hS : S.ShortExact) {m₁ m₂ m₃ : ℤ → ℕ} (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (b₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
  (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))

/-- The long exact homology sequence, based by ordered bases of the homology groups of which only
finitely many are nonempty, has nonzero Reidemeister torsion. -/
theorem reidemeisterTorsion_homologySequenceComplex_ne_zero (h₁ : {i | m₁ i ≠ 0}.Finite)
    (h₂ : {i | m₂ i ≠ 0}.Finite) (h₃ : {i | m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) ≠ 0 :=
  HomologicalComplex.reidemeisterTorsion_ne_zero _ _
    (ChainComplex.interleave.finite_setOf_rank_ne_zero h₁ h₂ h₃)
    hS.acyclic_homologySequenceComplex

include hS b₁ b₃ in
/-- When the middle complex `S.X₂` of a short exact sequence is acyclic, the connecting
homomorphism `H_{q+1}(S.X₃) ⟶ H_q(S.X₁)` is an isomorphism, so bases of `H_q(S.X₁)` and
`H_{q+1}(S.X₃)` have the same size. -/
theorem card_homology_basis_eq_of_acyclic_X₂ (h₂ : S.X₂.Acyclic) (q : ℤ) :
    m₁ q = m₃ (q + 1) := by
  let e := (hS.δIso (q + 1) q rfl (h₂ (q + 1)).isZero_homology
    (h₂ q).isZero_homology).toLinearEquiv
  simpa using Fintype.card_congr ((b₁ q).indexEquiv ((b₃ (q + 1)).map e))

/-- When the middle complex `S.X₂` is acyclic, its homology bases `b₂` are empty and the torsion of
the based long exact homology sequence is the alternating product of the determinants of the
connecting isomorphisms `δ : H_{q+1}(S.X₃) ⟶ H_q(S.X₁)`, with exponent `(-1) ^ (q + 1)`. -/
theorem reidemeisterTorsion_homologySequenceComplex_of_acyclic_X₂ (h₂ : S.X₂.Acyclic)
    (hm₁ : {i | m₁ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
        (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) =
      ∏ᶠ q : ℤ, ((b₁ q).det fun k ↦ (hS.δ (q + 1) q rfl).hom (b₃ (q + 1)
        (Fin.cast (hS.card_homology_basis_eq_of_acyclic_X₂ b₁ b₃ h₂ q) k))) ^
          ((q + 1).negOnePow : ℤ) := by
  have hm := hS.card_homology_basis_eq_of_acyclic_X₂ b₁ b₃ h₂
  have hm₂ (q : ℤ) : m₂ q = 0 := by
    have := ModuleCat.subsingleton_of_isZero (h₂ q).isZero_homology
    exact Nat.eq_zero_of_not_pos fun hp ↦ (b₂ q).ne_zero ⟨0, hp⟩ (Subsingleton.elim _ _)
  have hm₃ : {i | m₃ i ≠ 0}.Finite :=
    (hm₁.image fun q ↦ q + 1).subset fun i hi ↦ ⟨i - 1, by
      have := hm (i - 1); rw [sub_add_cancel] at this; simpa [this] using hi, sub_add_cancel i 1⟩
  -- Transport `b₃ (q + 1)` along `δ` to obtain a basis `b₁' q` of `H_q(S.X₁)` for which `τ(H) = 1`.
  have hsurj (q : ℤ) : Function.Surjective (hS.δ (q + 1) q rfl).hom :=
    (ModuleCat.epi_iff_surjective _).1 (hS.epi_δ (q + 1) q rfl (h₂ q).isZero_homology)
  let e (q : ℤ) := (hS.δIso (q + 1) q rfl (h₂ (q + 1)).isZero_homology
    (h₂ q).isZero_homology).toLinearEquiv
  let b₁' (q : ℤ) : Basis (Fin (m₁ q)) F (S.X₁.homology q) :=
    ((b₃ (q + 1)).map (e q)).reindex (finCongr (hm q).symm)
  let u (q : ℤ) : Basis (Fin (m₁ q)) F (LinearMap.range (hS.δ (q + 1) q rfl).hom) :=
    (b₁' q).map (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 (hsurj q))).symm
  let v (q : ℤ) : Basis (Fin 0) F (LinearMap.range (HomologicalComplex.homologyMap S.f q).hom) :=
    have := ModuleCat.subsingleton_of_isZero (h₂ q).isZero_homology
    Basis.empty _
  let w (q : ℤ) : Basis (Fin 0) F (LinearMap.range (HomologicalComplex.homologyMap S.g q).hom) :=
    have : Subsingleton (LinearMap.range (HomologicalComplex.homologyMap S.g q).hom) := by
      have := ModuleCat.subsingleton_of_isZero (h₂ q).isZero_homology
      exact ⟨fun x y ↦ Subtype.ext <| by
        obtain ⟨x', hx⟩ := x.2; obtain ⟨y', hy⟩ := y.2; rw [← hx, ← hy, Subsingleton.elim x' y']⟩
    Basis.empty _
  have hτ₀ : hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁' b₂ b₃) = 1 :=
    ChainComplex.interleave.reidemeisterTorsion_eq_one_of_append _ _ _
      b₁' b₂ b₃ hm₁ hm₃ u v w
      (fun _ ↦ Fin.elim0) (fun _ k ↦ k.elim0) (fun _ ↦ Fin.elim0) (fun _ k ↦ k.elim0)
      (fun q k ↦ b₃ (q + 1) (Fin.cast (hm q) k))
      (fun q k ↦ by simp [u, b₁', e, ShortExact.δIso])
      (fun _ ↦ (Nat.add_zero _).symm) hm₂ (fun q ↦ (hm q).symm.trans (Nat.zero_add _).symm)
      (fun q ↦ funext fun k ↦ by simp [Fin.append_right_nil _ _ rfl, u])
      (fun q ↦ funext fun k ↦ (Fin.cast (hm₂ q) k).elim0)
      (fun q ↦ funext fun k ↦ by simp [Fin.append_left_nil _ _ rfl])
  rw [ChainComplex.interleave.reidemeisterTorsion_basis_eq_mul _ _ _ b₁' b₁ b₂ b₂ b₃ b₃, hτ₀]
  simp only [Basis.det_self, one_zpow, finprod_one, one_mul, mul_one]
  refine finprod_congr fun q ↦ ?_
  have hinv : (b₁' q).det (b₁ q) = ((b₁ q).det (b₁' q))⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
  rw [hinv, inv_zpow, ← zpow_neg, ← Units.val_neg, ← Int.negOnePow_succ]
  congr 2
  ext k
  simp [b₁', e, ShortExact.δIso]

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.ShortComplex.Splitting

variable {F : Type*} [Field F] {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
  (σ : S.Splitting) {m₁ m₃ : ℤ → ℕ}
  (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
  (b₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
  (hb₁ : ∀ i k, b₂ i (Fin.castAdd (m₃ i) k) =
    (HomologicalComplex.homologyMap S.f i).hom (b₁ i k))
  (hb₃ : ∀ i k, (HomologicalComplex.homologyMap S.g i).hom (b₂ i (Fin.natAdd (m₁ i) k)) =
    b₃ i k)

include hb₁ hb₃ in
/-- For a split short exact sequence of chain complexes, the long exact homology sequence splits
into short exact sequences `0 ⟶ H_q(S.X₁) ⟶ H_q(S.X₂) ⟶ H_q(S.X₃) ⟶ 0`, so its Reidemeister
torsion with respect to compatible homology bases is `1`. -/
theorem reidemeisterTorsion_homologySequenceComplex
    (hm₁ : {i | m₁ i ≠ 0}.Finite) (hm₃ : {i | m₃ i ≠ 0}.Finite) :
    σ.shortExact.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) = 1 := by
  have hδ (q : ℤ) : σ.shortExact.δ (q + 1) q rfl = 0 := by
    rw [← Category.id_comp (σ.shortExact.δ (q + 1) q rfl), ← HomologicalComplex.homologyMap_id,
      ← σ.s_g, HomologicalComplex.homologyMap_comp, Category.assoc,
      σ.shortExact.comp_δ (q + 1) q rfl, comp_zero]
  have hfinj (q : ℤ) : Function.Injective (HomologicalComplex.homologyMap S.f q).hom :=
    Function.LeftInverse.injective (g := (HomologicalComplex.homologyMap σ.r q).hom) fun x ↦ by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, σ.f_r,
        HomologicalComplex.homologyMap_id, ModuleCat.id_apply]
  have hgsurj (q : ℤ) : Function.Surjective (HomologicalComplex.homologyMap S.g q).hom :=
    fun x ↦ ⟨(HomologicalComplex.homologyMap σ.s q).hom x, by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, σ.s_g,
        HomologicalComplex.homologyMap_id, ModuleCat.id_apply]⟩
  let u (q : ℤ) : Basis (Fin 0) F (LinearMap.range (σ.shortExact.δ (q + 1) q rfl).hom) :=
    have : Subsingleton (LinearMap.range (σ.shortExact.δ (q + 1) q rfl).hom) := by
      rw [show LinearMap.range (σ.shortExact.δ (q + 1) q rfl).hom = ⊥ by simp [hδ q]]
      infer_instance
    Basis.empty _
  let v (q : ℤ) := (b₁ q).map (LinearEquiv.ofInjective _ (hfinj q))
  let w (q : ℤ) := (b₃ q).map (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 (hgsurj q))).symm
  exact ChainComplex.interleave.reidemeisterTorsion_eq_one_of_append _ _ _
    b₁ b₂ b₃ hm₁ hm₃ u v w
    (fun q k ↦ b₁ q k) (fun q k ↦ by simp [v]) (fun q k ↦ b₂ q (Fin.natAdd (m₁ q) k))
    (fun q k ↦ hb₃ q k) (fun _ ↦ Fin.elim0) (fun _ k ↦ k.elim0)
    (fun _ ↦ (Nat.zero_add _).symm) (fun _ ↦ rfl) (fun _ ↦ (Nat.add_zero _).symm)
    (fun q ↦ funext fun k ↦ by simp [Fin.append_left_nil _ _ rfl])
    (fun q ↦ funext fun k ↦ by induction k using Fin.addCases <;> simp [hb₁ q, v])
    (fun q ↦ funext fun k ↦ by simp [Fin.append_right_nil _ _ rfl, w])

end CategoryTheory.ShortComplex.Splitting

namespace HomologicalComplex

variable {F : Type*} [Field F]

/-- Reindex a family `∀ q : ℤ, P (q + 1)` to `∀ i : ℤ, P i` along `i - 1 + 1 = i`. -/
private def extendSucc {P : ℤ → Sort*} (f : ∀ q : ℤ, P (q + 1)) (i : ℤ) : P i :=
  cast (congrArg P (sub_add_cancel i 1)) (f (i - 1))

@[simp]
private theorem extendSucc_add_one {P : ℤ → Sort*} (f : ∀ q : ℤ, P (q + 1)) (q : ℤ) :
    extendSucc f (q + 1) = f q := by
  rw [extendSucc, cast_eq_iff_heq, add_sub_cancel_right]

/-- For a bounded based complex, only finitely many homology groups have nonempty bases. -/
private theorem finite_setOf_homology_ne_zero {C : ChainComplex (ModuleCat F) ℤ} {n m : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (h : ∀ i, Basis (Fin (m i)) F (C.homology i))
    (hn : {i | n i ≠ 0}.Finite) : {i | m i ≠ 0}.Finite :=
  hn.subset fun i hi ↦ by
    have : Module.Finite F (C.X i) := .of_basis (c i)
    have hle := C.finrank_homology_le_finrank_X i
    rw [finrank_eq_card_basis (h i), finrank_eq_card_basis (c i), Fintype.card_fin,
      Fintype.card_fin] at hle
    simp only [Set.mem_ofPred_eq] at hi ⊢
    omega

/-- If the middle term of a sequence of based complexes is unbounded, then so is one of the outer
terms, so both sides of Milnor's multiplicativity formula are `0`. -/
private theorem reidemeisterTorsionWithHomology_eq_mul_of_not_finite
    {C₁ C₂ C₃ : ChainComplex (ModuleCat F) ℤ} {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (C₂.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (C₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i))
    (hn : ¬{i | n₁ i + n₃ i ≠ 0}.Finite) (ε τ : F) :
    C₂.reidemeisterTorsionWithHomology c₂ h₂ =
      ε * (C₁.reidemeisterTorsionWithHomology c₁ h₁ *
        C₃.reidemeisterTorsionWithHomology c₃ h₃) * τ := by
  rw [reidemeisterTorsionWithHomology_of_not_finite C₂ c₂ h₂ hn]
  by_cases hn₁ : {i | n₁ i ≠ 0}.Finite
  · have hn₃ : ¬{i | n₃ i ≠ 0}.Finite := fun hn₃ ↦
      hn ((hn₁.union hn₃).subset fun i hi ↦ by
        simp only [Set.mem_union, Set.mem_ofPred_eq] at hi ⊢; omega)
    simp [reidemeisterTorsionWithHomology_of_not_finite C₃ c₃ h₃ hn₃]
  · simp [reidemeisterTorsionWithHomology_of_not_finite C₁ c₁ h₁ hn₁]

section ShortExactBoundaries

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}

private theorem range_d_le_comap_range_d (q : ℤ) :
    LinearMap.range (S.X₁.d (q + 1) q).hom ≤
      (LinearMap.range (S.X₂.d (q + 1) q).hom).comap (S.f.f q).hom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(S.f.f (q + 1)).hom x, S.f.comm_apply (q + 1) q x⟩

private theorem comap_range_d_le_ker_d (hS : S.ShortExact) (q : ℤ) :
    (LinearMap.range (S.X₂.d (q + 1) q).hom).comap (S.f.f q).hom ≤
      LinearMap.ker (S.X₁.d q ((ComplexShape.down ℤ).next q)).hom := by
  rintro x₁ ⟨x₂, hx₂⟩
  exact hS.d_eq_zero_of_f_eq_d_apply (q + 1) q x₂ x₁ hx₂.symm _

/-- An element of `S.X₁.X q` whose image in `S.X₂.X q` is a boundary is a cycle whose homology
class lies in `ker (homologyMap S.f q) = range (hS.δ (q + 1) q rfl)`. -/
private def preboundaryHomologyMap (hS : S.ShortExact) (q : ℤ) :
    (LinearMap.range (S.X₂.d (q + 1) q).hom).comap (S.f.f q).hom →ₗ[F]
      LinearMap.range (hS.δ (q + 1) q rfl).hom :=
  ((S.X₁.moduleCatKerHomologyClass rfl).comp
    (Submodule.inclusion (comap_range_d_le_ker_d hS q))).codRestrict _ fun x ↦
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ (q + 1) q rfl) _).1 <| by
      change homologyMap S.f q
        (S.X₁.moduleCatKerHomologyClass rfl
          (Submodule.inclusion (comap_range_d_le_ker_d hS q) x)) = 0
      rw [homologyMap_moduleCatKerHomologyClass]
      exact (congrArg (S.X₂.moduleCatKerHomologyClass rfl) (Subtype.ext rfl)).trans
        ((S.X₂.exact_inclusion_moduleCatKerHomologyClass rfl
          ((ComplexShape.down ℤ).prev_eq'
            (rfl : (ComplexShape.down ℤ).Rel (q + 1) q))).apply_apply_eq_zero
          ⟨(S.f.f q).hom x.1, x.2⟩)

private theorem exact_preboundaryHomologyMap (hS : S.ShortExact) (q : ℤ) :
    Function.Exact (Submodule.inclusion (range_d_le_comap_range_d (S := S) q))
      (preboundaryHomologyMap hS q) := by
  intro x
  have hx : (preboundaryHomologyMap hS q x : S.X₁.homology q) =
      S.X₁.moduleCatKerHomologyClass rfl (Submodule.inclusion (comap_range_d_le_ker_d hS q) x) :=
    rfl
  rw [← Subtype.coe_inj, Submodule.coe_zero, hx,
    (S.X₁.exact_inclusion_moduleCatKerHomologyClass rfl
      ((ComplexShape.down ℤ).prev_eq' (rfl : (ComplexShape.down ℤ).Rel (q + 1) q))) _]
  exact ⟨fun ⟨b, hb⟩ ↦ ⟨b, Subtype.ext (show (b : S.X₁.X q) = x from congrArg Subtype.val hb)⟩,
    fun ⟨b, hb⟩ ↦ ⟨b, Subtype.ext (show (b : S.X₁.X q) = x from congrArg Subtype.val hb)⟩⟩

private def fPreboundary (q : ℤ) :
    (LinearMap.range (S.X₂.d (q + 1) q).hom).comap (S.f.f q).hom →ₗ[F]
      LinearMap.range (S.X₂.d (q + 1) q).hom :=
  ((S.f.f q).hom.comp (Submodule.subtype _)).codRestrict _ fun x ↦ x.2

private theorem fPreboundary_injective (hS : S.ShortExact) (q : ℤ) :
    Function.Injective (fPreboundary (S := S) q) := by
  have hf :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS q).moduleCat_injective_f
  exact fun x y h ↦ Subtype.ext (hf (congrArg Subtype.val h))

private theorem exact_fPreboundary_boundaryMap (hS : S.ShortExact) (q : ℤ) :
    Function.Exact (fPreboundary (S := S) q) (S.g.boundaryMap (q + 1) q) := by
  have hfg : Function.Exact (S.f.f q).hom (S.g.f q).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS q).exact
  intro b₂
  rw [← Subtype.coe_inj, Submodule.coe_zero, Hom.coe_boundaryMap, hfg b₂.1]
  exact ⟨fun ⟨x₁, hx₁⟩ ↦ ⟨⟨x₁, Submodule.mem_comap.2 (hx₁.symm ▸ b₂.2)⟩, Subtype.ext hx₁⟩,
    fun ⟨x₁, hx₁⟩ ↦ ⟨x₁.1, congrArg Subtype.val hx₁⟩⟩

private def shortExactPreboundaryBasis (hS : S.ShortExact) {q : ℤ} {p₁ r₁ : ℕ}
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (q + 1) q).hom))
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (y₁ : Fin r₁ → S.X₁.cycles q) (hy₁ : ∀ k, S.X₁.homologyπ q (y₁ k) = u k)
    (x₂ : Fin r₁ → S.X₂.X (q + 1))
    (hx₂ : ∀ k, (S.X₂.d (q + 1) q).hom (x₂ k) = (S.f.f q).hom (S.X₁.iCycles q (y₁ k))) :
    Basis (Fin (p₁ + r₁)) F ((LinearMap.range (S.X₂.d (q + 1) q).hom).comap (S.f.f q).hom) :=
  (Basis.ofExactLift (Submodule.inclusion_injective _) (exact_preboundaryHomologyMap hS q) b₁ u
    (fun k ↦ ⟨S.X₁.iCycles q (y₁ k), x₂ k, hx₂ k⟩) fun k ↦ Subtype.ext <| by
      change S.X₁.moduleCatKerHomologyClass rfl
        (Submodule.inclusion (comap_range_d_le_ker_d hS q)
          ⟨S.X₁.iCycles q (y₁ k), x₂ k, hx₂ k⟩) = (u k : S.X₁.homology q)
      have h : Submodule.inclusion (comap_range_d_le_ker_d hS q)
          ⟨S.X₁.iCycles q (y₁ k), x₂ k, hx₂ k⟩ = S.X₁.moduleCatCyclesToKer q _ (y₁ k) :=
        Subtype.ext (S.X₁.coe_moduleCatCyclesToKer q _ (y₁ k)).symm
      rw [h, moduleCatKerHomologyClass_moduleCatCyclesToKer, hy₁]).reindex finSumFinEquiv

private theorem coe_shortExactPreboundaryBasis (hS : S.ShortExact) {q : ℤ} {p₁ r₁ : ℕ}
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (q + 1) q).hom))
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (y₁ : Fin r₁ → S.X₁.cycles q) (hy₁ : ∀ k, S.X₁.homologyπ q (y₁ k) = u k)
    (x₂ : Fin r₁ → S.X₂.X (q + 1))
    (hx₂ : ∀ k, (S.X₂.d (q + 1) q).hom (x₂ k) = (S.f.f q).hom (S.X₁.iCycles q (y₁ k))) :
    ⇑(shortExactPreboundaryBasis hS b₁ u y₁ hy₁ x₂ hx₂) =
      Fin.append (Submodule.inclusion (range_d_le_comap_range_d q) ∘ b₁)
        fun k ↦ ⟨S.X₁.iCycles q (y₁ k), x₂ k, hx₂ k⟩ :=
  Basis.coe_reindex_ofExactLift _ _ b₁ u _ _

/-- The basis of `B_q(S.X₂)` built from a basis `b₁` of `B_q(S.X₁)`, cycles `y₁` representing a
basis `u` of `range (δ_q)` whose images in `S.X₂` bound `x₂`, and boundaries of lifts `t` of a
basis `b₃` of `B_q(S.X₃)`. -/
private def shortExactBoundaryBasisWithHomology (hS : S.ShortExact) {q : ℤ} {p₁ r₁ p₃ : ℕ}
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (q + 1) q).hom))
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (y₁ : Fin r₁ → S.X₁.cycles q) (hy₁ : ∀ k, S.X₁.homologyπ q (y₁ k) = u k)
    (x₂ : Fin r₁ → S.X₂.X (q + 1))
    (hx₂ : ∀ k, (S.X₂.d (q + 1) q).hom (x₂ k) = (S.f.f q).hom (S.X₁.iCycles q (y₁ k)))
    (b₃ : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (q + 1) q).hom))
    (t : Fin p₃ → S.X₂.X (q + 1))
    (ht : ∀ k, (S.X₃.d (q + 1) q).hom ((S.g.f (q + 1)).hom (t k)) = b₃ k) :
    Basis (Fin (p₁ + r₁ + p₃)) F (LinearMap.range (S.X₂.d (q + 1) q).hom) :=
  (Basis.ofExactLift (fPreboundary_injective hS q) (exact_fPreboundary_boundaryMap hS q)
    (shortExactPreboundaryBasis hS b₁ u y₁ hy₁ x₂ hx₂) b₃
    (fun k ↦ ⟨(S.X₂.d (q + 1) q).hom (t k), t k, rfl⟩)
    fun k ↦ Subtype.ext ((Hom.coe_boundaryMap S.g _ _ _).trans
      ((Hom.comm_apply S.g _ _ _).symm.trans (ht k)))).reindex finSumFinEquiv

private theorem coe_shortExactBoundaryBasisWithHomology_subtype (hS : S.ShortExact)
    {q : ℤ} {p₁ r₁ p₃ : ℕ}
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (q + 1) q).hom))
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (y₁ : Fin r₁ → S.X₁.cycles q) (hy₁ : ∀ k, S.X₁.homologyπ q (y₁ k) = u k)
    (x₂ : Fin r₁ → S.X₂.X (q + 1))
    (hx₂ : ∀ k, (S.X₂.d (q + 1) q).hom (x₂ k) = (S.f.f q).hom (S.X₁.iCycles q (y₁ k)))
    (b₃ : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (q + 1) q).hom))
    (t : Fin p₃ → S.X₂.X (q + 1))
    (ht : ∀ k, (S.X₃.d (q + 1) q).hom ((S.g.f (q + 1)).hom (t k)) = b₃ k) :
    ⇑(shortExactBoundaryBasisWithHomology hS b₁ u y₁ hy₁ x₂ hx₂ b₃ t ht) =
      Fin.append (fPreboundary q ∘ shortExactPreboundaryBasis hS b₁ u y₁ hy₁ x₂ hx₂)
        fun k ↦ ⟨(S.X₂.d (q + 1) q).hom (t k), t k, rfl⟩ :=
  Basis.coe_reindex_ofExactLift _ _ _ b₃ _ _

private theorem coe_shortExactBoundaryBasisWithHomology (hS : S.ShortExact) {q : ℤ} {p₁ r₁ p₃ : ℕ}
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (q + 1) q).hom))
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (y₁ : Fin r₁ → S.X₁.cycles q) (hy₁ : ∀ k, S.X₁.homologyπ q (y₁ k) = u k)
    (x₂ : Fin r₁ → S.X₂.X (q + 1))
    (hx₂ : ∀ k, (S.X₂.d (q + 1) q).hom (x₂ k) = (S.f.f q).hom (S.X₁.iCycles q (y₁ k)))
    (b₃ : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (q + 1) q).hom))
    (t : Fin p₃ → S.X₂.X (q + 1))
    (ht : ∀ k, (S.X₃.d (q + 1) q).hom ((S.g.f (q + 1)).hom (t k)) = b₃ k) :
    (fun k ↦ (shortExactBoundaryBasisWithHomology hS b₁ u y₁ hy₁ x₂ hx₂ b₃ t ht k : S.X₂.X q)) =
      Fin.append (Fin.append (fun k ↦ (S.f.f q).hom (b₁ k))
        fun k ↦ (S.f.f q).hom (S.X₁.iCycles q (y₁ k))) fun k ↦ (S.X₂.d (q + 1) q).hom (t k) := by
  ext k
  rw [congrFun (coe_shortExactBoundaryBasisWithHomology_subtype hS b₁ u y₁ hy₁ x₂ hx₂ b₃ t ht) k]
  induction k using Fin.addCases with
  | left k =>
    rw [Fin.append_left, Fin.append_left, Function.comp_apply]
    change (S.f.f q).hom (shortExactPreboundaryBasis hS b₁ u y₁ hy₁ x₂ hx₂ k : S.X₁.X q) = _
    rw [congrFun (coe_shortExactPreboundaryBasis hS b₁ u y₁ hy₁ x₂ hx₂) k]
    induction k using Fin.addCases <;> simp
  | right k => simp

end ShortExactBoundaries

section ShortExactBracket

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
  {n₁ n₃ : ℤ → ℕ} {c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)}
  {c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i)}
  {c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i)}

private theorem card_X_basis_eq_add_add {C : ChainComplex (ModuleCat F) ℤ} {n : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) {j : ℤ} {p m q : ℕ}
    (b₁ : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
    (h : Basis (Fin m) F (C.homology (j + 1)))
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom)) :
    n (j + 1) = p + m + q := by
  have : FiniteDimensional F (C.X (j + 1)) := .of_basis (c (j + 1))
  have hm : (ComplexShape.down ℤ).next (j + 1) = j :=
    (ComplexShape.down ℤ).next_eq' (rfl : (ComplexShape.down ℤ).Rel (j + 1) j)
  have hp : (ComplexShape.down ℤ).prev (j + 1) = j + 1 + 1 :=
    (ComplexShape.down ℤ).prev_eq' (rfl : (ComplexShape.down ℤ).Rel (j + 1 + 1) (j + 1))
  have hZ := (C.exact_inclusion_moduleCatKerHomologyClass hm hp).finrank_eq_add
    (Submodule.inclusion_injective _) (C.moduleCatKerHomologyClass_surjective hm)
  have hX := LinearMap.finrank_range_add_finrank_ker (C.d (j + 1) j).hom
  rw [finrank_eq_card_basis (c (j + 1)), Fintype.card_fin, finrank_eq_card_basis b₀,
    Fintype.card_fin] at hX
  rw [finrank_eq_card_basis b₁, Fintype.card_fin, finrank_eq_card_basis h,
    Fintype.card_fin] at hZ
  omega

private theorem append_four_map_eq {X Y Z : Type*} (φ : X → Y) (ι : Z → X) {p r₁ r₂ q : ℕ}
    (a : Fin p → X) (b : Fin r₁ → Z) (c : Fin r₂ → Z) (d : Fin q → X)
    (m : Fin (p + (r₁ + r₂) + q)) :
    Fin.append (Fin.append (Fin.append (fun k ↦ φ (a k)) (fun k ↦ φ (ι (b k))))
        (fun k ↦ φ (ι (c k)))) (fun k ↦ φ (d k)) (Fin.cast (by omega) m) =
      φ (Fin.append (Fin.append a fun k ↦ ι ((Fin.append b c ∘ Fin.cast rfl) k)) d m) := by
  rw [Fin.append_assoc (fun k ↦ φ (a k)), Fin.append_cast_left]
  simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
  induction m using Fin.addCases with
  | left m => induction m using Fin.addCases with
    | left k => simp
    | right m => induction m using Fin.addCases <;> simp
  | right k => simp

private theorem map_append_four_eq {X Y Z : Type*} (ψ : X → Y) (ι : Z → Y) {p r₃ r₁ q : ℕ}
    (a : Fin p → X) (b : Fin r₃ → X) (c : Fin r₁ → X) (d : Fin q → X)
    {a' : Fin p → Y} {b' : Fin r₃ → Z} {c' : Fin r₁ → Z} {d' : Fin q → Y}
    (ha : ∀ k, ψ (a k) = a' k) (hb : ∀ k, ψ (b k) = ι (b' k))
    (hc : ∀ k, ψ (c k) = ι (c' k)) (hd : ∀ k, ψ (d k) = d' k)
    (m : Fin (p + (r₃ + r₁) + q)) :
    ψ (Fin.append (Fin.append a b) (Fin.append c d) (Fin.cast (by omega) m)) =
      Fin.append (Fin.append a' fun k ↦ ι ((Fin.append b' c' ∘ Fin.cast rfl) k)) d' m := by
  have hm : Fin.cast (by omega) m =
      Fin.cast (Nat.add_assoc (p + r₃) r₁ q) (Fin.cast (by omega) m) := rfl
  rw [hm, ← Function.comp_apply (f := Fin.append (Fin.append a b) (Fin.append c d)),
    ← Fin.append_assoc, Fin.append_assoc a b c, Fin.append_cast_left]
  simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
  induction m using Fin.addCases with
  | left m => induction m using Fin.addCases with
    | left k => simp [ha]
    | right m => induction m using Fin.addCases <;> simp [hb, hc]
  | right k => simp [hd]

private theorem iCycles_append_cyclesMap (j : ℤ) {r₂ r₃ : ℕ}
    (y₁ : Fin r₂ → S.X₁.cycles j) (y₂ : Fin r₃ → S.X₂.cycles j) :
    (fun k ↦ S.X₂.iCycles j ((Fin.append (fun r ↦ (cyclesMap S.f j).hom (y₁ r)) y₂ ∘
      Fin.cast rfl) k)) =
      Fin.append (fun k ↦ (S.f.f j).hom (S.X₁.iCycles j (y₁ k)))
        fun k ↦ S.X₂.iCycles j (y₂ k) := by
  ext k
  induction k using Fin.addCases <;> simp [moduleCat_iCycles_cyclesMap_apply]

/-- In degree `j + 1`, de-interleaving the boundary basis `shortExactBoundaryBasisWithHomology`,
adapted homology representatives and lifts in `S.X₂` factors its bracket into the product of the
brackets of `S.X₁` and `S.X₃`, up to `(-1) ^ (p₃' * r₂' + (p₃' + r₃') * p₁₀)`. -/
private theorem torsionBracketWithHomology_shortExact (hS : S.ShortExact)
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    {j : ℤ} {p₁' r₁' r₂' p₃' r₃' p₁₀ r₁₀ p₃₀ m₁' m₂' m₃' : ℕ}
    (hm₁' : m₁' = r₁' + r₂') (hm₂' : m₂' = r₂' + r₃') (hm₃' : m₃' = r₃' + r₁₀)
    (b₁' : Basis (Fin p₁') F (LinearMap.range (S.X₁.d (j + 1 + 1) (j + 1)).hom))
    (u' : Basis (Fin r₁') F (LinearMap.range (hS.δ (j + 1 + 1) (j + 1) rfl).hom))
    (y₁u : Fin r₁' → S.X₁.cycles (j + 1)) (hy₁u : ∀ k, S.X₁.homologyπ (j + 1) (y₁u k) = u' k)
    (x₂' : Fin r₁' → S.X₂.X (j + 1 + 1))
    (hx₂' : ∀ k,
      (S.X₂.d (j + 1 + 1) (j + 1)).hom (x₂' k) = (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (y₁u k)))
    (b₃' : Basis (Fin p₃') F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom))
    (t' : Fin p₃' → S.X₂.X (j + 1 + 1))
    (ht' : ∀ k, (S.X₃.d (j + 1 + 1) (j + 1)).hom ((S.g.f (j + 1 + 1)).hom (t' k)) = b₃' k)
    (h₁' : Basis (Fin m₁') F (S.X₁.homology (j + 1))) (y₁v : Fin r₂' → S.X₁.cycles (j + 1))
    (y₁' : Fin m₁' → S.X₁.cycles (j + 1)) (hy₁'_eq : y₁' = Fin.append y₁u y₁v ∘ Fin.cast hm₁')
    (hy₁ : ∀ k, S.X₁.homologyπ (j + 1) (y₁' k) = h₁' k)
    (h₂' : Basis (Fin m₂') F (S.X₂.homology (j + 1))) (y₂w : Fin r₃' → S.X₂.cycles (j + 1))
    (y₂' : Fin m₂' → S.X₂.cycles (j + 1))
    (hy₂'_eq : y₂' = Fin.append (fun r ↦ (cyclesMap S.f (j + 1)).hom (y₁v r)) y₂w ∘ Fin.cast hm₂')
    (hy₂ : ∀ k, S.X₂.homologyπ (j + 1) (y₂' k) = h₂' k)
    (h₃' : Basis (Fin m₃') F (S.X₃.homology (j + 1))) (z₃ : Fin r₁₀ → S.X₃.cycles (j + 1))
    (y₃' : Fin m₃' → S.X₃.cycles (j + 1))
    (hy₃'_eq : y₃' = Fin.append (fun r ↦ (cyclesMap S.g (j + 1)).hom (y₂w r)) z₃ ∘ Fin.cast hm₃')
    (hy₃ : ∀ k, S.X₃.homologyπ (j + 1) (y₃' k) = h₃' k)
    (b₁₀ : Basis (Fin p₁₀) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (s₁ : Fin p₁₀ → S.X₁.X (j + 1)) (hs₁ : ∀ k, (S.X₁.d (j + 1) j).hom (s₁ k) = b₁₀ k)
    (u₀ : Basis (Fin r₁₀) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (y₁₀ : Fin r₁₀ → S.X₁.cycles j) (hy₁₀ : ∀ k, S.X₁.homologyπ j (y₁₀ k) = u₀ k)
    (x₂₀ : Fin r₁₀ → S.X₂.X (j + 1))
    (hx₂₀ : ∀ k, (S.X₂.d (j + 1) j).hom (x₂₀ k) = (S.f.f j).hom (S.X₁.iCycles j (y₁₀ k)))
    (hgx₂₀ : ∀ k, (S.g.f (j + 1)).hom (x₂₀ k) = S.X₃.iCycles (j + 1) (z₃ k))
    (b₃₀ : Basis (Fin p₃₀) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t₀ : Fin p₃₀ → S.X₂.X (j + 1))
    (ht₀ : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t₀ k)) = b₃₀ k)
    (hs₂ : ∀ k, (S.X₂.d (j + 1) j).hom
      (Fin.append (Fin.append (fun l ↦ (S.f.f (j + 1)).hom (s₁ l)) x₂₀) t₀ k) =
        shortExactBoundaryBasisWithHomology hS b₁₀ u₀ y₁₀ hy₁₀ x₂₀ hx₂₀ b₃₀ t₀ ht₀ k) :
    torsionBracketWithHomology c₂
        (shortExactBoundaryBasisWithHomology hS b₁' u' y₁u hy₁u x₂' hx₂' b₃' t' ht')
        h₂' y₂' hy₂
        (shortExactBoundaryBasisWithHomology hS b₁₀ u₀ y₁₀ hy₁₀ x₂₀ hx₂₀ b₃₀ t₀ ht₀)
        (Fin.append (Fin.append (fun l ↦ (S.f.f (j + 1)).hom (s₁ l)) x₂₀) t₀) hs₂ =
      (-1 : F) ^ (p₃' * r₂' + (p₃' + r₃') * p₁₀) *
        (torsionBracketWithHomology c₁ b₁' h₁' y₁' hy₁ b₁₀ s₁ hs₁ *
          torsionBracketWithHomology c₃ b₃' h₃' y₃' hy₃ b₃₀
            (fun l ↦ (S.g.f (j + 1)).hom (t₀ l)) ht₀) := by
  subst hm₁' hm₂' hm₃'; subst hy₁'_eq hy₂'_eq hy₃'_eq
  have hSj := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS (j + 1)
  have hn₁ := card_X_basis_eq_add_add c₁ b₁' h₁' b₁₀
  have hn₃ := card_X_basis_eq_add_add c₃ b₃' h₃' b₃₀
  have hN : n₁ (j + 1) + n₃ (j + 1) =
      (p₁' + r₁') + r₂' + p₁₀ + (p₃' + r₃' + (r₁₀ + p₃₀)) := by omega
  rw [torsionBracketWithHomology_eq_det_append c₂ _ _ _ hy₂ _ _ hs₂ (by omega),
    coe_shortExactBoundaryBasisWithHomology,
    torsionBracketWithHomology_eq_det_append c₁ b₁' h₁' _ hy₁ b₁₀ s₁ hs₁ hn₁,
    torsionBracketWithHomology_eq_det_append c₃ b₃' h₃' _ hy₃ b₃₀ _ ht₀ hn₃]
  have hsw := ((c₂ (j + 1)).reindex (finCongr hN)).det.map_append_append_append_comm
    (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (b₁' k))
      fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (y₁u k)))
    (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t' k))
    (fun k ↦ (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1) (y₁v k)))
    (fun k ↦ S.X₂.iCycles (j + 1) (y₂w k)) (fun l ↦ (S.f.f (j + 1)).hom (s₁ l)) (Fin.append x₂₀ t₀)
  rw [Basis.det_reindex, Basis.det_reindex] at hsw
  rw [iCycles_append_cyclesMap, Fin.append_assoc (fun l ↦ (S.f.f (j + 1)).hom (s₁ l)) x₂₀ t₀,
    Fin.append_cast_right, Function.comp_assoc,
    show Fin.cast _ ∘ Fin.cast _ =
      Fin.cast (show (p₁' + r₁') + r₂' + p₁₀ + (p₃' + r₃' + (r₁₀ + p₃₀)) = _ by omega) ∘
        finCongr hN from funext fun _ ↦ by simp,
    ← Function.comp_assoc, hsw,
    Basis.eq_reindex_ofExactLift hSj.moduleCat_injective_f
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hSj.exact)
      (c₁ (j + 1)) (c₃ (j + 1)) _ (hc₁ (j + 1)) (hc₃ (j + 1)), Basis.det_reindex]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  congr 1
  refine Basis.ofExactLift_det_eq_mul _ _ _ _ _ _ _ _ _ (fun i ↦ ?_) (fun i ↦ ?_)
  · obtain ⟨m, rfl⟩ := (finCongr hn₁.symm).surjective i
    rw [Function.comp_apply, Function.comp_apply,
      show finCongr hN (finSumFinEquiv (.inl (finCongr hn₁.symm m))) =
        Fin.castAdd (p₃' + r₃' + (r₁₀ + p₃₀)) (Fin.cast (by omega) m) from Fin.ext (by simp),
      Fin.append_left, append_four_map_eq (S.f.f (j + 1)).hom (S.X₁.iCycles (j + 1))]
    simp
  · obtain ⟨m, rfl⟩ := (finCongr hn₃.symm).surjective i
    rw [Function.comp_apply, Function.comp_apply,
      show finCongr hN (finSumFinEquiv (.inr (finCongr hn₃.symm m))) =
        Fin.natAdd ((p₁' + r₁') + r₂' + p₁₀) (Fin.cast (by omega) m) from
          Fin.ext (by simp only [finCongr_apply, finSumFinEquiv_apply_right, Fin.val_natAdd,
            Fin.val_cast]; omega),
      Fin.append_right]
    exact (map_append_four_eq (S.g.f (j + 1)).hom (S.X₃.iCycles (j + 1)) _ _ _ _
      (fun k ↦ (Hom.comm_apply S.g _ _ _).symm.trans (ht' k))
      (fun k ↦ (S.X₂.moduleCat_iCycles_cyclesMap_apply (j + 1) S.g (y₂w k)).symm) hgx₂₀
      (fun _ ↦ rfl) m).trans (by simp)

private theorem hasFiniteMulSupport_shortExactSign
    {n₁ m₁ : ℤ → ℕ} (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i)) (hn₁ : {i | n₁ i ≠ 0}.Finite) :
    Function.HasFiniteMulSupport fun j : ℤ ↦ (-1 : F) ^
      (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
          finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) :=
  ((hn₁.preimage (add_left_injective (1 : ℤ)).injOn).union hn₁).subset <|
    Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      simp only [Set.mem_union, not_or] at hj
      have hj₁ : n₁ (j + 1) = 0 := by simpa using hj.1
      have hj₀ : n₁ j = 0 := by simpa using hj.2
      have : Module.Finite F (S.X₁.X (j + 1)) := .of_basis (c₁ (j + 1))
      have : Module.Finite F (S.X₁.homology (j + 1)) := .of_basis (h₁ (j + 1))
      have hH := S.X₁.finrank_homology_le_finrank_X (j + 1)
      have hr := LinearMap.finrank_range_add_finrank_ker (homologyMap S.f (j + 1)).hom
      rw [finrank_eq_card_basis (c₁ (j + 1)), Fintype.card_fin, hj₁] at hH
      have hr₀ : finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) = 0 := by omega
      rw [hr₀, finrank_range_d_eq_zero S.X₁ c₁ hj₀, mul_zero, mul_zero, add_zero, pow_zero]

private theorem hasFiniteMulSupport_torsionBracketWithHomology
    {C : ChainComplex (ModuleCat F) ℤ} {n m r : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (h : ∀ i, Basis (Fin (m i)) F (C.homology i))
    (hn : {i | n i ≠ 0}.Finite)
    (b : ∀ j, Basis (Fin (r j)) F (LinearMap.range (C.d (j + 1) j).hom))
    (y : ∀ i, Fin (m i) → C.cycles i) (hy : ∀ i k, C.homologyπ i (y i k) = h i k)
    (s : ∀ j, Fin (r j) → C.X (j + 1)) (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k) :
    Function.HasFiniteMulSupport fun j : ℤ ↦ torsionBracketWithHomology c (b (j + 1)) (h (j + 1))
      (y (j + 1)) (hy (j + 1)) (b j) (s j) (hs j) ^ (j.negOnePow : ℤ) :=
  (hn.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
    Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      rw [torsionBracketWithHomology_eq_one c _ _ _ _ _ _ _ (by simpa using hj), one_zpow]

private theorem reidemeisterTorsionWithHomology_shortExact_of_eq_one (hS : S.ShortExact)
    {m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (h₁ h₁' : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ h₂' : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ h₃' : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) {ε : F}
    (hε : S.X₂.reidemeisterTorsionWithHomology c₂ h₂' =
      ε * (S.X₁.reidemeisterTorsionWithHomology c₁ h₁' *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃'))
    (hH : hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ h₁' h₂' h₃') = 1) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      ε * (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃) *
      hS.homologySequenceComplex.reidemeisterTorsion
        (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃) := by
  have hinv₁ : (∏ᶠ q : ℤ, (h₁' q).det (h₁ q) ^ (q.negOnePow : ℤ)) =
      (∏ᶠ q : ℤ, (h₁' q).det (h₁ q) ^ ((q + 1).negOnePow : ℤ))⁻¹ := by
    rw [← finprod_inv_distrib]
    exact finprod_congr fun q ↦ by simp [Int.negOnePow_succ, zpow_neg]
  have hinv₃ : (∏ᶠ q : ℤ, (h₃' q).det (h₃ q) ^ (q.negOnePow : ℤ)) =
      (∏ᶠ q : ℤ, (h₃' q).det (h₃ q) ^ ((q + 1).negOnePow : ℤ))⁻¹ := by
    rw [← finprod_inv_distrib]
    exact finprod_congr fun q ↦ by simp [Int.negOnePow_succ, zpow_neg]
  have hD₁ : (∏ᶠ q : ℤ, (h₁' q).det (h₁ q) ^ ((q + 1).negOnePow : ℤ)) ≠ 0 :=
    finprod_ne_zero fun q ↦ zpow_ne_zero _ (Basis.isUnit_det _ _).ne_zero
  have hD₃ : (∏ᶠ q : ℤ, (h₃' q).det (h₃ q) ^ ((q + 1).negOnePow : ℤ)) ≠ 0 :=
    finprod_ne_zero fun q ↦ zpow_ne_zero _ (Basis.isUnit_det _ _).ne_zero
  rw [reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (c := c₂) (h := h₂') h₂,
    reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (c := c₁) (h := h₁') h₁,
    reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (c := c₃) (h := h₃') h₃,
    ChainComplex.interleave.reidemeisterTorsion_basis_eq_mul _ _ _ h₁' h₁ h₂' h₂ h₃' h₃,
    hH, one_mul, hinv₁, hinv₃, hε]
  set D₁ := ∏ᶠ q : ℤ, (h₁' q).det (h₁ q) ^ ((q + 1).negOnePow : ℤ)
  set D₂ := ∏ᶠ q : ℤ, (h₂' q).det (h₂ q) ^ ((q + 1).negOnePow : ℤ)
  set D₃ := ∏ᶠ q : ℤ, (h₃' q).det (h₃ q) ^ ((q + 1).negOnePow : ℤ)
  calc ε * (S.X₁.reidemeisterTorsionWithHomology c₁ h₁' *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃') * D₂
      = ε * (S.X₁.reidemeisterTorsionWithHomology c₁ h₁' *
          S.X₃.reidemeisterTorsionWithHomology c₃ h₃') * D₂ *
          (D₁ * D₁⁻¹) * (D₃ * D₃⁻¹) := by
            rw [mul_inv_cancel₀ hD₁, mul_inv_cancel₀ hD₃, mul_one, mul_one]
    _ = ε * (S.X₁.reidemeisterTorsionWithHomology c₁ h₁' * D₁ *
          (S.X₃.reidemeisterTorsionWithHomology c₃ h₃' * D₃)) * (D₁⁻¹ * D₂ * D₃⁻¹) := by ring

private theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_append
    (hS : S.ShortExact) (hn : {i | n₁ i + n₃ i ≠ 0}.Finite)
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    {m₁ m₂ m₃ : ℤ → ℕ}
    (h₁' : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂' : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃' : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (u : ∀ q, Basis (Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom))) F
      (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (hm₁ : ∀ q, m₁ q = finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom) +
      finrank F (LinearMap.range (homologyMap S.f q).hom))
    (hm₂ : ∀ q, m₂ q = finrank F (LinearMap.range (homologyMap S.f q).hom) +
      finrank F (LinearMap.range (homologyMap S.g q).hom))
    (hm₃ : ∀ q, m₃ (q + 1) = finrank F (LinearMap.range (homologyMap S.g (q + 1)).hom) +
      finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (y₁u : ∀ q, Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom)) → S.X₁.cycles q)
    (hy₁u : ∀ q k, S.X₁.homologyπ q (y₁u q k) = u q k)
    (y₁v : ∀ q, Fin (finrank F (LinearMap.range (homologyMap S.f q).hom)) → S.X₁.cycles q)
    (y₂w : ∀ q, Fin (finrank F (LinearMap.range (homologyMap S.g q).hom)) → S.X₂.cycles q)
    (x₂ : ∀ q, Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom)) → S.X₂.X (q + 1))
    (z₃ : ∀ q, Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom)) → S.X₃.cycles (q + 1))
    (hx₂ : ∀ q k, (S.X₂.d (q + 1) q).hom (x₂ q k) = (S.f.f q).hom (S.X₁.iCycles q (y₁u q k)))
    (hgx₂ : ∀ q k, (S.g.f (q + 1)).hom (x₂ q k) = S.X₃.iCycles (q + 1) (z₃ q k))
    (y₁ : ∀ i, Fin (m₁ i) → S.X₁.cycles i)
    (hy₁_eq : ∀ q, y₁ q = Fin.append (y₁u q) (y₁v q) ∘ Fin.cast (hm₁ q))
    (hy₁ : ∀ i k, S.X₁.homologyπ i (y₁ i k) = h₁' i k)
    (y₂ : ∀ i, Fin (m₂ i) → S.X₂.cycles i)
    (hy₂_eq : ∀ q, y₂ q =
      Fin.append (fun r ↦ (cyclesMap S.f q).hom (y₁v q r)) (y₂w q) ∘ Fin.cast (hm₂ q))
    (hy₂ : ∀ i k, S.X₂.homologyπ i (y₂ i k) = h₂' i k)
    (y₃ : ∀ i, Fin (m₃ i) → S.X₃.cycles i)
    (hy₃_eq : ∀ q, y₃ (q + 1) =
      Fin.append (fun r ↦ (cyclesMap S.g (q + 1)).hom (y₂w (q + 1) r)) (z₃ q) ∘ Fin.cast (hm₃ q))
    (hy₃ : ∀ i k, S.X₃.homologyπ i (y₃ i k) = h₃' i k) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂' =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
            finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
          (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
            finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom)) *
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁' *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃') := by
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hn₃ : {i | n₃ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hg (i : ℤ) : Function.Surjective (S.g.f i).hom :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i).moduleCat_surjective_g
  let t (j : ℤ) (k : Fin (finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom))) :
      S.X₂.X (j + 1) :=
    Function.surjInv (hg (j + 1)) (chosenBoundaryLift S.X₃ c₃ (j + 1) j k)
  have ht (j : ℤ) (k) : (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t j k)) =
      chosenBoundaryBasis S.X₃ c₃ (j + 1) j k := by
    rw [Function.surjInv_eq (hg (j + 1)), chosenBoundaryLift_spec]
  let β (j : ℤ) := shortExactBoundaryBasisWithHomology hS
    (chosenBoundaryBasis S.X₁ c₁ (j + 1) j) (u j) (y₁u j) (hy₁u j) (x₂ j) (hx₂ j)
    (chosenBoundaryBasis S.X₃ c₃ (j + 1) j) (t j) (ht j)
  let s (j : ℤ) := Fin.append (Fin.append
    (fun k ↦ (S.f.f (j + 1)).hom (chosenBoundaryLift S.X₁ c₁ (j + 1) j k)) (x₂ j)) (t j)
  have hs (j : ℤ) (k) : (S.X₂.d (j + 1) j).hom (s j k) = β j k := by
    rw [congrFun (coe_shortExactBoundaryBasisWithHomology hS _ _ _ (hy₁u j) _ (hx₂ j) _ _ (ht j)) k]
    induction k using Fin.addCases with
    | left k => induction k using Fin.addCases <;>
        simp [s, Hom.comm_apply, chosenBoundaryLift_spec, hx₂]
    | right k => simp [s]
  have hτ₁ := hasFiniteMulSupport_torsionBracketWithHomology c₁ h₁' hn₁
    (fun j ↦ chosenBoundaryBasis S.X₁ c₁ (j + 1) j) y₁ hy₁
    (fun j ↦ chosenBoundaryLift S.X₁ c₁ (j + 1) j)
    (fun j ↦ chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j)
  have hτ₃ := hasFiniteMulSupport_torsionBracketWithHomology c₃ h₃' hn₃
    (fun j ↦ chosenBoundaryBasis S.X₃ c₃ (j + 1) j) y₃ hy₃
    (fun j k ↦ (S.g.f (j + 1)).hom (t j k)) ht
  have hε := hasFiniteMulSupport_shortExactSign c₁ h₁' hn₁
  rw [reidemeisterTorsionWithHomology_eq_finprod hn β y₂ hy₂ s hs,
    reidemeisterTorsionWithHomology_eq_finprod hn₁
      (fun j ↦ chosenBoundaryBasis S.X₁ c₁ (j + 1) j) y₁ hy₁
      (fun j ↦ chosenBoundaryLift S.X₁ c₁ (j + 1) j)
      (fun j ↦ chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j),
    reidemeisterTorsionWithHomology_eq_finprod hn₃
      (fun j ↦ chosenBoundaryBasis S.X₃ c₃ (j + 1) j) y₃ hy₃
      (fun j k ↦ (S.g.f (j + 1)).hom (t j k)) ht,
    ← finprod_mul_distrib hτ₁ hτ₃, ← finprod_mul_distrib hε (hτ₁.fun_mul hτ₃)]
  refine finprod_congr fun j ↦ ?_
  rw [torsionBracketWithHomology_shortExact hS hc₁ hc₃ (hm₁ (j + 1)) (hm₂ (j + 1)) (hm₃ j)
    _ _ _ (hy₁u (j + 1)) _ (hx₂ (j + 1)) _ _ (ht (j + 1)) (h₁' (j + 1)) (y₁v (j + 1))
    (y₁ (j + 1)) (hy₁_eq (j + 1)) (hy₁ (j + 1)) (h₂' (j + 1)) (y₂w (j + 1)) (y₂ (j + 1))
    (hy₂_eq (j + 1)) (hy₂ (j + 1)) (h₃' (j + 1)) (z₃ j) (y₃ (j + 1)) (hy₃_eq j) (hy₃ (j + 1))
    _ _ (chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j) _ _ (hy₁u j) _ (hx₂ j) (hgx₂ j) _ _ (ht j)
    (hs j), mul_zpow, mul_zpow]
  congr 1
  rcases Int.units_eq_one_or j.negOnePow with hj | hj <;> simp [hj, ← inv_pow]

end ShortExactBracket

section AdaptedHomologyBases

private def rangeLift {M N : Type*} [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (φ : M →ₗ[F] N) (y : LinearMap.range φ) : M :=
  Function.surjInv φ.surjective_rangeRestrict y

private theorem rangeLift_spec {M N : Type*} [AddCommGroup M] [Module F M] [AddCommGroup N]
    [Module F N] (φ : M →ₗ[F] N) (y : LinearMap.range φ) : φ (rangeLift φ y) = y :=
  congrArg Subtype.val (Function.surjInv_eq φ.surjective_rangeRestrict y)

private def cycleLift (C : ChainComplex (ModuleCat F) ℤ) (q : ℤ) (x : C.homology q) :
    C.cycles q :=
  Function.surjInv (C.moduleCat_homologyπ_surjective q) x

private theorem cycleLift_spec (C : ChainComplex (ModuleCat F) ℤ) (q : ℤ) (x : C.homology q) :
    C.homologyπ q (cycleLift C q x) = x :=
  Function.surjInv_eq (C.moduleCat_homologyπ_surjective q) x

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}

private def shortExactHomologyBasis₁ (hS : S.ShortExact) (q : ℤ) {r₁ r₂ : ℕ}
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (v : Basis (Fin r₂) F (LinearMap.range (homologyMap S.f q).hom))
    (sf : Fin r₂ → S.X₁.homology q) (hsf : ∀ k, (homologyMap S.f q).hom (sf k) = v k) :
    Basis (Fin (r₁ + r₂)) F (S.X₁.homology q) :=
  (Basis.ofExactLift (Submodule.injective_subtype _)
    (((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ (q + 1) q rfl)).range_subtype.rangeRestrict) u v sf
    fun k ↦ Subtype.ext (hsf k)).reindex finSumFinEquiv

private def shortExactHomologyBasis₂ (hS : S.ShortExact) (q : ℤ) {r₂ r₃ : ℕ}
    (v : Basis (Fin r₂) F (LinearMap.range (homologyMap S.f q).hom))
    (w : Basis (Fin r₃) F (LinearMap.range (homologyMap S.g q).hom))
    (sg : Fin r₃ → S.X₂.homology q) (hsg : ∀ k, (homologyMap S.g q).hom (sg k) = w k) :
    Basis (Fin (r₂ + r₃)) F (S.X₂.homology q) :=
  (Basis.ofExactLift (Submodule.injective_subtype _)
    (((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₂ q)).range_subtype.rangeRestrict) v w sg
    fun k ↦ Subtype.ext (hsg k)).reindex finSumFinEquiv

private def shortExactHomologyBasis₃ (hS : S.ShortExact) (q : ℤ) {r₃ r₁ : ℕ}
    (w : Basis (Fin r₃) F (LinearMap.range (homologyMap S.g (q + 1)).hom))
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (sδ : Fin r₁ → S.X₃.homology (q + 1))
    (hsδ : ∀ k, (hS.δ (q + 1) q rfl).hom (sδ k) = u k) :
    Basis (Fin (r₃ + r₁)) F (S.X₃.homology (q + 1)) :=
  (Basis.ofExactLift (Submodule.injective_subtype _)
    (((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₃ (q + 1) q rfl)).range_subtype.rangeRestrict) w u sδ
    fun k ↦ Subtype.ext (hsδ k)).reindex finSumFinEquiv

private theorem coe_shortExactHomologyBasis₁ (hS : S.ShortExact) (q : ℤ) {r₁ r₂ : ℕ}
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (v : Basis (Fin r₂) F (LinearMap.range (homologyMap S.f q).hom))
    (sf : Fin r₂ → S.X₁.homology q) (hsf : ∀ k, (homologyMap S.f q).hom (sf k) = v k) :
    ⇑(shortExactHomologyBasis₁ hS q u v sf hsf) =
      Fin.append (fun k ↦ (u k : S.X₁.homology q)) sf :=
  Basis.coe_reindex_ofExactLift _ _ u v sf _

private theorem coe_shortExactHomologyBasis₂ (hS : S.ShortExact) (q : ℤ) {r₂ r₃ : ℕ}
    (v : Basis (Fin r₂) F (LinearMap.range (homologyMap S.f q).hom))
    (w : Basis (Fin r₃) F (LinearMap.range (homologyMap S.g q).hom))
    (sg : Fin r₃ → S.X₂.homology q) (hsg : ∀ k, (homologyMap S.g q).hom (sg k) = w k) :
    ⇑(shortExactHomologyBasis₂ hS q v w sg hsg) =
      Fin.append (fun k ↦ (v k : S.X₂.homology q)) sg :=
  Basis.coe_reindex_ofExactLift _ _ v w sg _

private theorem coe_shortExactHomologyBasis₃ (hS : S.ShortExact) (q : ℤ) {r₃ r₁ : ℕ}
    (w : Basis (Fin r₃) F (LinearMap.range (homologyMap S.g (q + 1)).hom))
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (sδ : Fin r₁ → S.X₃.homology (q + 1))
    (hsδ : ∀ k, (hS.δ (q + 1) q rfl).hom (sδ k) = u k) :
    ⇑(shortExactHomologyBasis₃ hS q w u sδ hsδ) =
      Fin.append (fun k ↦ (w k : S.X₃.homology (q + 1))) sδ :=
  Basis.coe_reindex_ofExactLift _ _ w u sδ _

private theorem homologyπ_shortExactHomologyBasis₁ (hS : S.ShortExact) (q : ℤ) {m r₁ r₂ : ℕ}
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (v : Basis (Fin r₂) F (LinearMap.range (homologyMap S.f q).hom))
    (sf : Fin r₂ → S.X₁.homology q) (hsf : ∀ k, (homologyMap S.f q).hom (sf k) = v k)
    (hm : m = r₁ + r₂) (y₁u : Fin r₁ → S.X₁.cycles q) (hy₁u : ∀ k, S.X₁.homologyπ q (y₁u k) = u k)
    (y₁v : Fin r₂ → S.X₁.cycles q) (hy₁v : ∀ k, S.X₁.homologyπ q (y₁v k) = sf k) (k : Fin m) :
    S.X₁.homologyπ q ((Fin.append y₁u y₁v ∘ Fin.cast hm) k) =
      (shortExactHomologyBasis₁ hS q u v sf hsf).reindex (finCongr hm.symm) k := by
  obtain ⟨k, rfl⟩ := (finCongr hm.symm).surjective k
  induction k using Fin.addCases <;>
    simp [coe_shortExactHomologyBasis₁, hy₁u, hy₁v]

private theorem homologyπ_shortExactHomologyBasis₂ (hS : S.ShortExact) (q : ℤ) {m r₂ r₃ : ℕ}
    (v : Basis (Fin r₂) F (LinearMap.range (homologyMap S.f q).hom))
    (w : Basis (Fin r₃) F (LinearMap.range (homologyMap S.g q).hom))
    (sg : Fin r₃ → S.X₂.homology q) (hsg : ∀ k, (homologyMap S.g q).hom (sg k) = w k)
    (hm : m = r₂ + r₃) {sf : Fin r₂ → S.X₁.homology q}
    (hsf : ∀ k, (homologyMap S.f q).hom (sf k) = v k)
    (y₁v : Fin r₂ → S.X₁.cycles q) (hy₁v : ∀ k, S.X₁.homologyπ q (y₁v k) = sf k)
    (y₂w : Fin r₃ → S.X₂.cycles q) (hy₂w : ∀ k, S.X₂.homologyπ q (y₂w k) = sg k) (k : Fin m) :
    S.X₂.homologyπ q
      ((Fin.append (fun r ↦ (cyclesMap S.f q).hom (y₁v r)) y₂w ∘ Fin.cast hm) k) =
      (shortExactHomologyBasis₂ hS q v w sg hsg).reindex (finCongr hm.symm) k := by
  obtain ⟨k, rfl⟩ := (finCongr hm.symm).surjective k
  induction k using Fin.addCases <;>
    simp [coe_shortExactHomologyBasis₂, ← moduleCat_homologyMap_homologyπ, hy₁v, hy₂w, hsf]

private theorem homologyπ_shortExactHomologyBasis₃ (hS : S.ShortExact) {m r₃ r₁ : ℤ → ℕ}
    (w : ∀ q, Basis (Fin (r₃ q)) F (LinearMap.range (homologyMap S.g q).hom))
    (u : ∀ q, Basis (Fin (r₁ q)) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (sδ : ∀ q, Fin (r₁ q) → S.X₃.homology (q + 1))
    (hsδ : ∀ q k, (hS.δ (q + 1) q rfl).hom (sδ q k) = u q k)
    (hm : ∀ q, m (q + 1) = r₃ (q + 1) + r₁ q)
    {sg : ∀ q, Fin (r₃ q) → S.X₂.homology q}
    (hsg : ∀ q k, (homologyMap S.g q).hom (sg q k) = w q k)
    (y₂w : ∀ q, Fin (r₃ q) → S.X₂.cycles q)
    (hy₂w : ∀ q k, S.X₂.homologyπ q (y₂w q k) = sg q k)
    (z₃ : ∀ q, Fin (r₁ q) → S.X₃.cycles (q + 1))
    (hz₃ : ∀ q k, S.X₃.homologyπ (q + 1) (z₃ q k) = sδ q k) (i : ℤ) (k : Fin (m i)) :
    S.X₃.homologyπ i (extendSucc (P := fun i ↦ Fin (m i) → S.X₃.cycles i) (fun q ↦
      Fin.append (fun r ↦ (cyclesMap S.g (q + 1)).hom (y₂w (q + 1) r)) (z₃ q) ∘
        Fin.cast (hm q)) i k) =
      extendSucc (P := fun i ↦ Basis (Fin (m i)) F (S.X₃.homology i))
        (fun q ↦ (shortExactHomologyBasis₃ hS q (w (q + 1)) (u q) (sδ q) (hsδ q)).reindex
          (finCongr (hm q).symm)) i k := by
  obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
  simp only [extendSucc_add_one]
  obtain ⟨k, rfl⟩ := (finCongr (hm q).symm).surjective k
  induction k using Fin.addCases <;>
    simp [coe_shortExactHomologyBasis₃, ← moduleCat_homologyMap_homologyπ, hy₂w, hsg, hz₃]

private theorem reidemeisterTorsion_shortExactHomologyBasis_eq_one (hS : S.ShortExact)
    {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (hn : {i | n₁ i + n₃ i ≠ 0}.Finite)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (u : ∀ q, Basis (Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom))) F
      (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (v : ∀ q, Basis (Fin (finrank F (LinearMap.range (homologyMap S.f q).hom))) F
      (LinearMap.range (homologyMap S.f q).hom))
    (w : ∀ q, Basis (Fin (finrank F (LinearMap.range (homologyMap S.g q).hom))) F
      (LinearMap.range (homologyMap S.g q).hom))
    (sf : ∀ q, Fin (finrank F (LinearMap.range (homologyMap S.f q).hom)) → S.X₁.homology q)
    (hsf : ∀ q k, (homologyMap S.f q).hom (sf q k) = v q k)
    (sg : ∀ q, Fin (finrank F (LinearMap.range (homologyMap S.g q).hom)) → S.X₂.homology q)
    (hsg : ∀ q k, (homologyMap S.g q).hom (sg q k) = w q k)
    (sδ : ∀ q, Fin (finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom)) → S.X₃.homology (q + 1))
    (hsδ : ∀ q k, (hS.δ (q + 1) q rfl).hom (sδ q k) = u q k)
    (hm₁ : ∀ q, m₁ q = finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom) +
      finrank F (LinearMap.range (homologyMap S.f q).hom))
    (hm₂ : ∀ q, m₂ q = finrank F (LinearMap.range (homologyMap S.f q).hom) +
      finrank F (LinearMap.range (homologyMap S.g q).hom))
    (hm₃ : ∀ q, m₃ (q + 1) = finrank F (LinearMap.range (homologyMap S.g (q + 1)).hom) +
      finrank F (LinearMap.range (hS.δ (q + 1) q rfl).hom)) :
    hS.homologySequenceComplex.reidemeisterTorsion (ChainComplex.interleave.basis _ _ _
      (fun q ↦ (shortExactHomologyBasis₁ hS q (u q) (v q) (sf q) (hsf q)).reindex
        (finCongr (hm₁ q).symm))
      (fun q ↦ (shortExactHomologyBasis₂ hS q (v q) (w q) (sg q) (hsg q)).reindex
        (finCongr (hm₂ q).symm))
      (extendSucc (P := fun i ↦ Basis (Fin (m₃ i)) F (S.X₃.homology i)) fun q ↦
        (shortExactHomologyBasis₃ hS q (w (q + 1)) (u q) (sδ q) (hsδ q)).reindex
          (finCongr (hm₃ q).symm))) = 1 :=
  ChainComplex.interleave.reidemeisterTorsion_eq_one_of_append _ _ _ _ _ _
    (finite_setOf_homology_ne_zero c₁ h₁ (hn.subset fun i hi ↦ by
      simp only [Set.mem_ofPred_eq] at hi ⊢; omega))
    (finite_setOf_homology_ne_zero c₃ h₃ (hn.subset fun i hi ↦ by
      simp only [Set.mem_ofPred_eq] at hi ⊢; omega))
    u v w sf hsf sg hsg sδ hsδ hm₁ hm₂ hm₃
    (fun q ↦ by rw [Basis.coe_reindex, coe_shortExactHomologyBasis₁]; rfl)
    (fun q ↦ by rw [Basis.coe_reindex, coe_shortExactHomologyBasis₂]; rfl)
    (fun q ↦ by simp only [extendSucc_add_one]; rw [Basis.coe_reindex,
      coe_shortExactHomologyBasis₃]; rfl)

private theorem card_shortExactHomologyBasis₁ (hS : S.ShortExact) {m r₁ r₂ : ℕ} {q : ℤ}
    (h : Basis (Fin m) F (S.X₁.homology q))
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (v : Basis (Fin r₂) F (LinearMap.range (homologyMap S.f q).hom))
    (sf : Fin r₂ → S.X₁.homology q) (hsf : ∀ k, (homologyMap S.f q).hom (sf k) = v k) :
    m = r₁ + r₂ := by
  simpa using Fintype.card_congr (h.indexEquiv (shortExactHomologyBasis₁ hS q u v sf hsf))

private theorem card_shortExactHomologyBasis₂ (hS : S.ShortExact) {m r₂ r₃ : ℕ} {q : ℤ}
    (h : Basis (Fin m) F (S.X₂.homology q))
    (v : Basis (Fin r₂) F (LinearMap.range (homologyMap S.f q).hom))
    (w : Basis (Fin r₃) F (LinearMap.range (homologyMap S.g q).hom))
    (sg : Fin r₃ → S.X₂.homology q) (hsg : ∀ k, (homologyMap S.g q).hom (sg k) = w k) :
    m = r₂ + r₃ := by
  simpa using Fintype.card_congr (h.indexEquiv (shortExactHomologyBasis₂ hS q v w sg hsg))

private theorem card_shortExactHomologyBasis₃ (hS : S.ShortExact) {m r₃ r₁ : ℕ} {q : ℤ}
    (h : Basis (Fin m) F (S.X₃.homology (q + 1)))
    (w : Basis (Fin r₃) F (LinearMap.range (homologyMap S.g (q + 1)).hom))
    (u : Basis (Fin r₁) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (sδ : Fin r₁ → S.X₃.homology (q + 1)) (hsδ : ∀ k, (hS.δ (q + 1) q rfl).hom (sδ k) = u k) :
    m = r₃ + r₁ := by
  simpa using Fintype.card_congr (h.indexEquiv (shortExactHomologyBasis₃ hS q w u sδ hsδ))

end AdaptedHomologyBases

/-- **Milnor's multiplicativity formula for torsion with homology bases.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of vector
spaces over a field `F`, with compatible chain bases `(c₁, c₂, c₃)` and arbitrary homology bases
`(h₁, h₂, h₃)`. Then `τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H)`, where `H`
is the long exact homology sequence `hS.homologySequenceComplex` based by `(h₁, h₂, h₃)` and
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim im(f*,ⱼ₊₁) + (dim B₃,ⱼ₊₁ + dim im(g*,ⱼ₊₁)) · dim B₁,ⱼ)` is the
Koszul sign of de-interleaving the boundaries, homology representatives and lifts. This holds for
all complexes, both sides being `0` when `S.X₂` is unbounded. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
            finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
          (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
            finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom)) *
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃) *
      hS.homologySequenceComplex.reidemeisterTorsion
        (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap; · exact reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ h₁ h₂ h₃ hn _ _
  have (i : ℤ) : Module.Finite F (S.X₁.homology i) := .of_basis (h₁ i)
  have (i : ℤ) : Module.Finite F (S.X₂.homology i) := .of_basis (h₂ i)
  have (i : ℤ) : Module.Finite F (S.X₃.homology i) := .of_basis (h₃ i)
  let u (q : ℤ) := finBasis F (LinearMap.range (hS.δ (q + 1) q rfl).hom)
  let v (q : ℤ) := finBasis F (LinearMap.range (homologyMap S.f q).hom)
  let w (q : ℤ) := finBasis F (LinearMap.range (homologyMap S.g q).hom)
  let sf (q : ℤ) (k) := rangeLift (homologyMap S.f q).hom (v q k)
  let sg (q : ℤ) (k) := rangeLift (homologyMap S.g q).hom (w q k)
  let sδ (q : ℤ) (k) := rangeLift (hS.δ (q + 1) q rfl).hom (u q k)
  have hsf (q : ℤ) (k) := rangeLift_spec (homologyMap S.f q).hom (v q k)
  have hsg (q : ℤ) (k) := rangeLift_spec (homologyMap S.g q).hom (w q k)
  have hsδ (q : ℤ) (k) := rangeLift_spec (hS.δ (q + 1) q rfl).hom (u q k)
  have hm₁ (q : ℤ) := card_shortExactHomologyBasis₁ hS (h₁ q) (u q) (v q) (sf q) (hsf q)
  have hm₂ (q : ℤ) := card_shortExactHomologyBasis₂ hS (h₂ q) (v q) (w q) (sg q) (hsg q)
  have hm₃ (q : ℤ) := card_shortExactHomologyBasis₃ hS (h₃ (q + 1)) (w (q + 1)) (u q) (sδ q) (hsδ q)
  let hlift (q : ℤ) (k) := hS.moduleCat_exists_d_eq_of_δ_eq (q + 1) q rfl (sδ q k)
    (cycleLift S.X₁ q (u q k)) ((hsδ q k).trans (cycleLift_spec S.X₁ q (u q k)).symm)
  let h₁' (q : ℤ) := (shortExactHomologyBasis₁ hS q (u q) (v q) (sf q) (hsf q)).reindex
    (finCongr (hm₁ q).symm)
  let h₂' (q : ℤ) := (shortExactHomologyBasis₂ hS q (v q) (w q) (sg q) (hsg q)).reindex
    (finCongr (hm₂ q).symm)
  let h₃' := extendSucc (P := fun i ↦ Basis (Fin (m₃ i)) F (S.X₃.homology i)) fun q ↦
    (shortExactHomologyBasis₃ hS q (w (q + 1)) (u q) (sδ q) (hsδ q)).reindex (finCongr (hm₃ q).symm)
  exact reidemeisterTorsionWithHomology_shortExact_of_eq_one hS c₁ c₃ c₂ h₁ h₁' h₂ h₂' h₃ h₃'
    (reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_append hS hn hc₁ hc₃ h₁' h₂' h₃' u
      hm₁ hm₂ hm₃ (fun q k ↦ cycleLift S.X₁ q (u q k)) (fun q k ↦ cycleLift_spec S.X₁ q (u q k))
      (fun q k ↦ cycleLift S.X₁ q (sf q k)) (fun q k ↦ cycleLift S.X₂ q (sg q k))
      (fun q k ↦ (hlift q k).choose) (fun q k ↦ (hlift q k).choose_spec.choose)
      (fun q k ↦ (hlift q k).choose_spec.choose_spec.1)
      (fun q k ↦ (hlift q k).choose_spec.choose_spec.2.1)
      _ (fun _ ↦ rfl) (fun q ↦ homologyπ_shortExactHomologyBasis₁ hS q _ _ _ (hsf q) (hm₁ q) _
        (fun k ↦ cycleLift_spec S.X₁ q (u q k)) _ (fun k ↦ cycleLift_spec S.X₁ q (sf q k)))
      _ (fun _ ↦ rfl) (fun q ↦ homologyπ_shortExactHomologyBasis₂ hS q _ _ _ (hsg q) (hm₂ q)
        (hsf q) _ (fun k ↦ cycleLift_spec S.X₁ q (sf q k)) _
        (fun k ↦ cycleLift_spec S.X₂ q (sg q k)))
      (extendSucc (P := fun i ↦ Fin (m₃ i) → S.X₃.cycles i) fun q ↦
        Fin.append (fun r ↦ (cyclesMap S.g (q + 1)).hom (cycleLift S.X₂ (q + 1) (sg (q + 1) r)))
          (fun k ↦ (hlift q k).choose_spec.choose) ∘ Fin.cast (hm₃ q))
      (fun q ↦ extendSucc_add_one _ q)
      (homologyπ_shortExactHomologyBasis₃ hS w u sδ hsδ hm₃ hsg
        (fun q k ↦ cycleLift S.X₂ q (sg q k)) (fun q k ↦ cycleLift_spec S.X₂ q (sg q k)) _
        fun q k ↦ (hlift q k).choose_spec.choose_spec.2.2))
    (reidemeisterTorsion_shortExactHomologyBasis_eq_one hS c₁ c₃ hn h₁ h₃ u v w sf hsf sg hsg
      sδ hsδ hm₁ hm₂ hm₃)

section Specializations

/-- **Milnor's multiplicativity formula for an acyclic middle complex.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of chain complexes of vector spaces with
`S.X₂` acyclic, compatible chain bases, and homology bases `h₁`, `h₃` of `S.X₁` and `S.X₃`. Then
`τ(S.X₂) = ε · τ(S.X₁, h₁) · τ(S.X₃, h₃) · ∏ⱼ det(δⱼ₊₁) ^ ((-1) ^ (j + 1))`, where
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim B₁,ⱼ)` and `det(δⱼ₊₁)` is the determinant of the connecting
isomorphism `Hⱼ₊₁(S.X₃) ⟶ Hⱼ(S.X₁)` in the bases `h₃ (j + 1)` and `h₁ j`. -/
theorem reidemeisterTorsion_eq_mul_reidemeisterTorsionWithHomology_of_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) (h₂ : S.X₂.Acyclic)
    {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsion c₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
        finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃) *
      ∏ᶠ q : ℤ, ((h₁ q).det fun k ↦ (hS.δ (q + 1) q rfl).hom (h₃ (q + 1)
        (Fin.cast (hS.card_homology_basis_eq_of_acyclic_X₂ h₁ h₃ h₂ q) k))) ^
          ((q + 1).negOnePow : ℤ) := by
  let b₂ (i : ℤ) : Basis (Fin 0) F (S.X₂.homology i) := by
    have := ModuleCat.subsingleton_of_isZero (h₂ i).isZero_homology
    exact Basis.empty _
  rw [← reidemeisterTorsionWithHomology_eq_reidemeisterTorsion (c := c₂) (h := b₂) h₂]
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · exact reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ h₁ b₂ h₃ hn _ _
  have hm₁ : {i | m₁ i ≠ 0}.Finite := finite_setOf_homology_ne_zero c₁ h₁
    (hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega)
  rw [reidemeisterTorsionWithHomology_eq_mul_of_shortExact hS c₁ c₃ c₂ hc₁ hc₃ h₁ b₂ h₃,
    hS.reidemeisterTorsion_homologySequenceComplex_of_acyclic_X₂ h₁ b₂ h₃ h₂ hm₁]
  congr 2
  refine finprod_congr fun j ↦ ?_
  have := ModuleCat.subsingleton_of_isZero (h₂ (j + 1)).isZero_homology
  have := (homologyMap S.g (j + 1)).hom.surjective_rangeRestrict.subsingleton
  simp [finrank_zero_of_subsingleton]

/-- **Torsion with homology bases of a split short exact sequence.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a split short exact sequence of chain complexes of vector spaces,
with compatible chain bases and compatible homology bases. Then
`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃)`, with the Koszul sign
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim H₁,ⱼ₊₁ + (dim B₃,ⱼ₊₁ + dim H₃,ⱼ₊₁) · dim B₁,ⱼ)`. This holds for
all complexes, both sides being `0` when `S.X₂` is unbounded. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_splitting
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (σ : S.Splitting) {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (h₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
    (hh₁ : ∀ i k, h₂ i (Fin.castAdd (m₃ i) k) = (homologyMap S.f i).hom (h₁ i k))
    (hh₃ : ∀ i k, (homologyMap S.g i).hom (h₂ i (Fin.natAdd (m₁ i) k)) = h₃ i k) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
            finrank F (S.X₁.homology (j + 1)) +
          (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
            finrank F (S.X₃.homology (j + 1))) *
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · simpa using reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ h₁ h₂ h₃ hn _ 1
  have hm₁ : {i | m₁ i ≠ 0}.Finite := finite_setOf_homology_ne_zero c₁ h₁
    (hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega)
  have hm₃ : {i | m₃ i ≠ 0}.Finite := finite_setOf_homology_ne_zero c₃ h₃
    (hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega)
  rw [reidemeisterTorsionWithHomology_eq_mul_of_shortExact σ.shortExact c₁ c₃ c₂ hc₁ hc₃ h₁ h₂ h₃,
    σ.reidemeisterTorsion_homologySequenceComplex h₁ h₃ h₂ hh₁ hh₃ hm₁ hm₃, mul_one]
  congr 1
  refine finprod_congr fun j ↦ ?_
  have hfinj : Function.Injective (homologyMap S.f (j + 1)).hom :=
    Function.LeftInverse.injective (g := (homologyMap σ.r (j + 1)).hom) fun x ↦ by
      rw [← ModuleCat.comp_apply, ← homologyMap_comp, σ.f_r, homologyMap_id, ModuleCat.id_apply]
  have hgsurj : Function.Surjective (homologyMap S.g (j + 1)).hom :=
    fun x ↦ ⟨(homologyMap σ.s (j + 1)).hom x, by
      rw [← ModuleCat.comp_apply, ← homologyMap_comp, σ.s_g, homologyMap_id, ModuleCat.id_apply]⟩
  rw [LinearMap.finrank_range_of_inj hfinj, LinearMap.range_eq_top.2 hgsurj, finrank_top]

/-- **Torsion with homology bases of a direct sum.** The torsion of the biproduct `C₁ ⊞ C₃` of two
based complexes with based homology, based in each degree by `HomologicalComplex.biprodXBasis` and
`HomologicalComplex.biprodHomologyBasis`, is `τ(C₁ ⊞ C₃) = ε · τ(C₁) · τ(C₃)`, with the Koszul sign
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim H₁,ⱼ₊₁ + (dim B₃,ⱼ₊₁ + dim H₃,ⱼ₊₁) · dim B₁,ⱼ)`. -/
theorem reidemeisterTorsionWithHomology_biprod {C₁ C₃ : ChainComplex (ModuleCat F) ℤ}
    {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i)) :
    (C₁ ⊞ C₃).reidemeisterTorsionWithHomology
        (fun i ↦ (biprodXBasis (c₁ i) (c₃ i)).reindex finSumFinEquiv)
        (fun i ↦ (biprodHomologyBasis (h₁ i) (h₃ i)).reindex finSumFinEquiv) =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (C₃.d (j + 1 + 1) (j + 1)).hom) *
            finrank F (C₁.homology (j + 1)) +
          (finrank F (LinearMap.range (C₃.d (j + 1 + 1) (j + 1)).hom) +
            finrank F (C₃.homology (j + 1))) *
            finrank F (LinearMap.range (C₁.d (j + 1) j).hom))) *
      (C₁.reidemeisterTorsionWithHomology c₁ h₁ *
        C₃.reidemeisterTorsionWithHomology c₃ h₃) := by
  refine reidemeisterTorsionWithHomology_eq_mul_of_splitting
    (ShortComplex.Splitting.ofHasBinaryBiproduct C₁ C₃) c₁ c₃ _ (by simp)
    (by simp [← ModuleCat.comp_apply]) h₁ h₃ _ (by simp) ?_
  intro i k
  simp [← ModuleCat.comp_apply, ← homologyMap_comp]

end Specializations

end HomologicalComplex
