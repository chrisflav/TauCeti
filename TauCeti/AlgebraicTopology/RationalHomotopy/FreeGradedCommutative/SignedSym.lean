/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.Algebra.Module.GradedModule.Finsupp
public import TauCeti.AlgebraicTopology.RationalHomotopy.FreeGradedCommutative.Basic
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Grading

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.AlgebraicTopology.RationalHomotopy.FreeGradedCommutative.Tensor
import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Decomposition

/-!
# The signed symmetric algebra model of free graded-commutative algebras

This file constructs the canonical free graded-commutative algebra on a linearly ordered family of
generators of assigned natural-number degrees `deg : ι → ℕ` using
`TauCeti.SignedSym (TauCeti.InternalGrading.finsupp R fun i => (deg i : ℤ))`, and proves that
over any commutative ring in which `2` is invertible:

* `TauCeti.isFreeGradedCommutative_signedSym`: `SignedSym` on `InternalGrading.finsupp` satisfies
  `TauCeti.IsFreeGradedCommutative` on the canonical generators `freeGradedCommutativeGen R deg`.
* `TauCeti.IsFreeGradedCommutative.equivSignedSym`: every free graded-commutative algebra on
  `(x, deg)` is canonically isomorphic as an `R`-algebra to this `SignedSym` model (hence to
  `Sym(V_even) ⊗ Λ(V_odd)` via `TauCeti.SignedSym.symTensorExteriorEquiv`).

We also record basic rank and vanishing checks for the empty generator set, a single degree-`1`
generator, and a single degree-`2` generator.

## References

* Y. Félix, S. Halperin, and J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in
  Mathematics 205, Springer (2001), Section 3.
* K. Hess, *Rational homotopy theory: a brief introduction*, Contemporary Mathematics 436 (2007),
  Section 1.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

section Model

variable (R : Type u) [CommRing R] {ι : Type w} (deg : ι → ℕ)

/-- The canonical `i`-th generator of the signed symmetric algebra on the free graded module with
generator degrees `deg`. -/
noncomputable def freeGradedCommutativeGen (i : ι) :
    SignedSym (InternalGrading.finsupp R fun j : ι => (deg j : ℤ)) :=
  SignedSym.generator (InternalGrading.finsupp R fun j : ι => (deg j : ℤ)) (Finsupp.single i 1)

theorem freeGradedCommutativeGen_def (i : ι) :
    freeGradedCommutativeGen R deg i =
      SignedSym.generator (InternalGrading.finsupp R fun j : ι => (deg j : ℤ))
        (Finsupp.single i 1) := (rfl)

theorem freeGradedCommutativeGen_mem (i : ι) :
    freeGradedCommutativeGen R deg i ∈
      signedSymPiece (InternalGrading.finsupp R fun j : ι => (deg j : ℤ)) (deg i) :=
  generator_mem_signedSymPiece _ (InternalGrading.single_mem_finsupp_piece i 1)

theorem freeGradedCommutativeGen_mul_comm (i j : ι) :
    freeGradedCommutativeGen R deg i * freeGradedCommutativeGen R deg j =
      (((deg i : ℤ) * deg j).negOnePow) •
        (freeGradedCommutativeGen R deg j * freeGradedCommutativeGen R deg i) := by
  simpa [freeGradedCommutativeGen, Units.smul_def] using
    SignedSym.generator_mul_generator (InternalGrading.finsupp R fun k : ι => (deg k : ℤ))
      (InternalGrading.single_mem_finsupp_piece i 1)
      (InternalGrading.single_mem_finsupp_piece j 1)

private theorem parityGrading_finsupp_zero :
    parityGrading (InternalGrading.finsupp R fun i : ι => (deg i : ℤ)).piece 0 =
      Finsupp.supported R R {i | Even (deg i)} := by
  rw [parityGrading_zero]
  simp_rw [InternalGrading.finsupp_piece]
  rw [← Finsupp.supported_iUnion]
  congr 1
  ext i
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, even_iff_exists_two_mul]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k.toNat, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨(k : ℤ), by omega⟩

private theorem parityGrading_finsupp_one :
    parityGrading (InternalGrading.finsupp R fun i : ι => (deg i : ℤ)).piece 1 =
      Finsupp.supported R R {i | Odd (deg i)} := by
  rw [parityGrading_one]
  simp_rw [InternalGrading.finsupp_piece]
  rw [← Finsupp.supported_iUnion]
  congr 1
  ext i
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Nat.odd_iff]
  constructor
  · rintro ⟨k, hk⟩
    omega
  · intro hk
    exact ⟨(deg i / 2 : ℕ), by omega⟩

private noncomputable def evenGenBasis :
    Module.Basis {i : ι // Even (deg i)} R
      (parityGrading (InternalGrading.finsupp R fun i : ι => (deg i : ℤ)).piece 0) :=
  Module.Basis.ofRepr <|
    (LinearEquiv.ofEq _ _ (parityGrading_finsupp_zero R deg)).trans
      (Finsupp.supportedEquivFinsupp {i | Even (deg i)})

private theorem coe_evenGenBasis (i : {i : ι // Even (deg i)}) :
    (evenGenBasis R deg i : ι →₀ R) = Finsupp.single i.1 1 :=
  Finsupp.supportedEquivFinsupp_symm_single (M := R) (R := R) {i | Even (deg i)} i 1

private noncomputable def oddGenBasis :
    Module.Basis {i : ι // Odd (deg i)} R
      (parityGrading (InternalGrading.finsupp R fun i : ι => (deg i : ℤ)).piece 1) :=
  Module.Basis.ofRepr <|
    (LinearEquiv.ofEq _ _ (parityGrading_finsupp_one R deg)).trans
      (Finsupp.supportedEquivFinsupp {i | Odd (deg i)})

private theorem coe_oddGenBasis (i : {i : ι // Odd (deg i)}) :
    (oddGenBasis R deg i : ι →₀ R) = Finsupp.single i.1 1 :=
  Finsupp.supportedEquivFinsupp_symm_single (M := R) (R := R) {i | Odd (deg i)} i 1

private theorem fromSymmetricEven_symmetricAlgebra_basis [LinearOrder ι]
    (e : {i : ι // Even (deg i)} →₀ ℕ) :
    SignedSym.fromSymmetricEven (InternalGrading.finsupp R fun i : ι => (deg i : ℤ))
        ((evenGenBasis R deg).symmetricAlgebra e) =
      standardMonomial (freeGradedCommutativeGen R deg) (e.mapDomain Subtype.val) := by
  let G := InternalGrading.finsupp R fun i : ι => (deg i : ℤ)
  let φ : MvPolynomial {i : ι // Even (deg i)} R →ₐ[R] SignedSym G :=
    (SignedSym.fromSymmetricEven G).comp
      (SymmetricAlgebra.equivMvPolynomial (evenGenBasis R deg)).symm.toAlgHom
  have hmon : MvPolynomial.monomial e (1 : R) = standardMonomial MvPolynomial.X e := by
    rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod, standardMonomial_def,
      ← Multiset.prod_coe, ← Multiset.map_coe, Finset.sort_eq]
    rfl
  have hφ : ∀ i : {i : ι // Even (deg i)},
      φ (MvPolynomial.X i) = freeGradedCommutativeGen R deg i.1 := fun i => by
    simp [φ, G, freeGradedCommutativeGen, coe_evenGenBasis]
  have hval : SignedSym.fromSymmetricEven G ((evenGenBasis R deg).symmetricAlgebra e) =
      φ (MvPolynomial.monomial e 1) := by
    simp [φ, Module.Basis.symmetricAlgebra, MvPolynomial.coe_basisMonomials]
  rw [hval, hmon, map_standardMonomial,
    standardMonomial_mapDomain_strictMono (e := Subtype.val) (fun _ _ h => h)]
  congr 1
  exact funext hφ

private theorem fromExteriorOdd_exteriorAlgebra_basis [Invertible (2 : R)] [LinearOrder ι]
    (s : Finset {i : ι // Odd (deg i)}) :
    SignedSym.fromExteriorOdd (InternalGrading.finsupp R fun i : ι => (deg i : ℤ))
        ((oddGenBasis R deg).ExteriorAlgebra s) =
      standardMonomial (freeGradedCommutativeGen R deg)
        ((Finsupp.indicator s fun _ _ => (1 : ℕ)).mapDomain Subtype.val) := by
  let fs : {i : ι // Odd (deg i)} →₀ ℕ := Finsupp.indicator s fun _ _ => 1
  have hfs_supp : fs.support = s := by
    ext i
    simp [fs, Finsupp.mem_support_iff, Finsupp.indicator_apply]
  have hext : (oddGenBasis R deg).ExteriorAlgebra s =
      standardMonomial (ExteriorAlgebra.ι R ∘ oddGenBasis R deg) fs := by
    rw [ExteriorAlgebra.basis_apply_ofCard (s_card := rfl),
      ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
      Set.powersetCard.ofFinEmbEquiv_symm_apply]
    simp only [Function.comp_apply]
    rw [List.ofFn_eq_map]
    have hlist : (List.finRange s.card).map
        (fun i => ExteriorAlgebra.ι R (oddGenBasis R deg (s.orderEmbOfFin rfl i))) =
        (s.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι R (oddGenBasis R deg i) := by
      rw [← Finset.listMap_orderEmbOfFin_finRange s rfl, List.map_map]
      rfl
    rw [show (List.finRange s.card).map (fun i => ExteriorAlgebra.ι R
        (oddGenBasis R deg
          (((Set.powersetCard.ofCard (rfl : s.card = s.card)).1.orderEmbOfFin
            (Set.powersetCard.ofCard (rfl : s.card = s.card)).2) i))) =
        (s.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι R (oddGenBasis R deg i) from hlist,
      standardMonomial_def, hfs_supp]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have his : i ∈ s := (Finset.mem_sort (· ≤ ·)).1 hi
    simp [fs, Finsupp.indicator_apply, his]
  rw [hext, map_standardMonomial,
    standardMonomial_mapDomain_strictMono (e := Subtype.val) (fun _ _ h => h)]
  congr 1
  ext i
  simp [freeGradedCommutativeGen, coe_oddGenBasis]

/-- **Existence of free graded-commutative algebras**: when `2` is invertible, the signed symmetric
algebra on `InternalGrading.finsupp R (fun i => (deg i : ℤ))` is free graded-commutative on its
canonical generators `freeGradedCommutativeGen R deg`. -/
theorem isFreeGradedCommutative_signedSym [Invertible (2 : R)] [LinearOrder ι] :
    IsFreeGradedCommutative
      (signedSymPiece (InternalGrading.finsupp R fun i : ι => (deg i : ℤ)))
      (freeGradedCommutativeGen R deg) deg := by
  classical
  let G := InternalGrading.finsupp R fun i : ι => (deg i : ℤ)
  let x := freeGradedCommutativeGen R deg
  let splitEquiv :
      ExponentVector deg ≃ ({i : ι // Even (deg i)} →₀ ℕ) × Finset {i : ι // Odd (deg i)} :=
    { toFun := fun f =>
        (f.1.comapDomain Subtype.val Subtype.val_injective.injOn,
         (f.1.support.subtype fun i => Odd (deg i)))
      invFun := fun p =>
        ⟨p.1.mapDomain Subtype.val +
          (Finsupp.indicator p.2 fun _ _ => (1 : ℕ)).mapDomain Subtype.val, fun i hi => by
          have heven : p.1.mapDomain Subtype.val i = 0 :=
            Finsupp.mapDomain_of_notMem_range p.1 i (by
              rintro ⟨j, hj⟩; exact (Nat.not_even_iff_odd.2 hi) (hj ▸ j.2))
          rw [Finsupp.add_apply, heven, zero_add]
          by_cases hmem : ⟨i, hi⟩ ∈ p.2
          · rw [Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨i, hi⟩]
            simp [Finsupp.indicator_apply, hmem]
          · rw [Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨i, hi⟩]
            simp [Finsupp.indicator_apply, hmem]⟩
      left_inv := fun f => by
        ext i
        simp only [Finsupp.add_apply]
        rcases Nat.even_or_odd (deg i) with hev | hodd
        · have hodd0 : ((Finsupp.indicator (f.1.support.subtype fun j => Odd (deg j))
              fun _ _ => (1 : ℕ)).mapDomain Subtype.val) i = 0 :=
            Finsupp.mapDomain_of_notMem_range _ i (by
              rintro ⟨j, hj⟩; exact (Nat.not_even_iff_odd.2 (hj ▸ j.2)) hev)
          rw [hodd0, add_zero,
            Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨i, hev⟩,
            Finsupp.comapDomain_apply]
        · have hev0 : ((f.1.comapDomain (Subtype.val : {k : ι // Even (deg k)} → ι)
              Subtype.val_injective.injOn).mapDomain Subtype.val) i = 0 :=
            Finsupp.mapDomain_of_notMem_range
              (f.1.comapDomain (Subtype.val : {k : ι // Even (deg k)} → ι)
                Subtype.val_injective.injOn) i
              (by rintro ⟨j, hj⟩; exact (Nat.not_even_iff_odd.2 hodd) (hj ▸ j.2))
          rw [hev0, zero_add,
            Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨i, hodd⟩,
            Finsupp.indicator_apply]
          have hle : f.1 i ≤ 1 := f.2 i hodd
          split_ifs with hmem
          · have hne : f.1 i ≠ 0 := Finsupp.mem_support_iff.1 (Finset.mem_subtype.1 hmem)
            omega
          · by_contra hne
            exact hmem (Finset.mem_subtype.2 (Finsupp.mem_support_iff.2 (Ne.symm hne)))
      right_inv := fun ⟨e, s⟩ => by
        refine Prod.ext ?_ ?_
        · ext ⟨i, hi⟩
          rw [Finsupp.comapDomain_apply, Finsupp.add_apply,
            Finsupp.mapDomain_apply_of_injective Subtype.val_injective e ⟨i, hi⟩,
            Finsupp.mapDomain_of_notMem_range _ i (by
              rintro ⟨j, hj⟩; exact (Nat.not_even_iff_odd.2 (hj ▸ j.2)) hi), add_zero]
        · ext ⟨i, hi⟩
          simp only [Finset.mem_subtype, Finsupp.mem_support_iff, Finsupp.add_apply]
          rw [Finsupp.mapDomain_of_notMem_range e i (by
              rintro ⟨j, hj⟩; exact (Nat.not_even_iff_odd.2 hi) (hj ▸ j.2)), zero_add,
            Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨i, hi⟩,
            Finsupp.indicator_apply]
          by_cases his : ⟨i, hi⟩ ∈ s <;> simp [his] }
  let bSymExt : Module.Basis (ExponentVector deg) R (SignedSym G) :=
    (((evenGenBasis R deg).symmetricAlgebra.tensorProduct
      (oddGenBasis R deg).ExteriorAlgebra).map
        (SignedSym.symTensorExteriorEquiv G).symm.toLinearEquiv).reindex splitEquiv.symm
  have hb_apply : ∀ f : ExponentVector deg, bSymExt f = standardMonomial x f.1 := by
    intro f
    set p := splitEquiv f
    have hval : bSymExt f =
        SignedSym.fromSymTensorExterior G
          ((evenGenBasis R deg).symmetricAlgebra p.1 ⊗ₜ[R]
            (oddGenBasis R deg).ExteriorAlgebra p.2) := by
      simp only [bSymExt, Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.map_apply,
        Module.Basis.tensorProduct_apply', AlgEquiv.coe_toLinearEquiv,
        SignedSym.symTensorExteriorEquiv_symm_apply]
      rfl
    have hsplit : f.1 = p.1.mapDomain Subtype.val +
        (Finsupp.indicator p.2 fun _ _ => (1 : ℕ)).mapDomain Subtype.val := by
      have h := congrArg Subtype.val (splitEquiv.symm_apply_apply f)
      simpa [p, splitEquiv] using h.symm
    have hsign : monomialMulSign deg (p.1.mapDomain Subtype.val)
        ((Finsupp.indicator p.2 fun _ _ => (1 : ℕ)).mapDomain Subtype.val) = 1 :=
      monomialMulSign_eq_one_of_even_left deg (f := p.1.mapDomain Subtype.val)
        (fun i hi => by
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hi)
          exact j.2) _
    rw [hval, SignedSym.fromSymTensorExterior_tmul,
      fromSymmetricEven_symmetricAlgebra_basis R deg p.1,
      fromExteriorOdd_exteriorAlgebra_basis R deg p.2,
      standardMonomial_mul_eq_smul (freeGradedCommutativeGen_mul_comm R deg),
      hsign, one_smul, ← hsplit]
  refine ⟨freeGradedCommutativeGen_mem R deg, freeGradedCommutativeGen_mul_comm R deg, ?_, ?_⟩
  · convert bSymExt.linearIndependent using 1
    exact funext fun f => (hb_apply f).symm
  · convert bSymExt.span_eq using 2
    ext a
    simp [hb_apply, x]

end Model

namespace IsFreeGradedCommutative

/-- **Canonical identification with `SignedSym`**: when `2` is invertible, any free
graded-commutative algebra on `(x, deg)` is canonically isomorphic as an `R`-algebra to the
signed symmetric algebra model `SignedSym (InternalGrading.finsupp R fun i => (deg i : ℤ))`. -/
noncomputable def equivSignedSym {R : Type u} [CommRing R] [Invertible (2 : R)]
    {A : Type v} [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
    {ι : Type w} [LinearOrder ι] {x : ι → A} {deg : ι → ℕ}
    (hx : IsFreeGradedCommutative 𝒜 x deg) :
    A ≃ₐ[R] SignedSym (InternalGrading.finsupp R fun i : ι => (deg i : ℤ)) := by
  let G := InternalGrading.finsupp R fun i : ι => (deg i : ℤ)
  have hS := isFreeGradedCommutative_signedSym R deg
  let fwd : A →ₐ[R] SignedSym G :=
    hx.lift (freeGradedCommutativeGen R deg) (freeGradedCommutativeGen_mul_comm R deg)
  let bwd : SignedSym G →ₐ[R] A :=
    hS.lift x hx.mul_comm
  refine AlgEquiv.ofAlgHom fwd bwd ?_ ?_
  · refine hS.algHom_ext fun i => ?_
    simp [fwd, bwd]
  · refine hx.algHom_ext fun i => ?_
    simp [fwd, bwd]

@[simp]
theorem equivSignedSym_apply {R : Type u} [CommRing R] [Invertible (2 : R)]
    {A : Type v} [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
    {ι : Type w} [LinearOrder ι] {x : ι → A} {deg : ι → ℕ}
    (hx : IsFreeGradedCommutative 𝒜 x deg) (i : ι) :
    hx.equivSignedSym (x i) = freeGradedCommutativeGen R deg i := by
  simp [equivSignedSym]

@[simp]
theorem equivSignedSym_symm_gen {R : Type u} [CommRing R] [Invertible (2 : R)]
    {A : Type v} [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
    {ι : Type w} [LinearOrder ι] {x : ι → A} {deg : ι → ℕ}
    (hx : IsFreeGradedCommutative 𝒜 x deg) (i : ι) :
    hx.equivSignedSym.symm (freeGradedCommutativeGen R deg i) = x i := by
  simp [equivSignedSym]

end IsFreeGradedCommutative

/-! ### Basic rank and structure checks -/

section Checks

/-- On an empty generator set, a free graded-commutative algebra over a commutative ring satisfying
the strong rank condition has rank `1`. -/
theorem IsFreeGradedCommutative.finrank_of_isEmpty {R : Type u} [CommRing R]
    [StrongRankCondition R] {A : Type v} [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
    {ι : Type w} [LinearOrder ι] [IsEmpty ι] {x : ι → A} {deg : ι → ℕ}
    (hx : IsFreeGradedCommutative 𝒜 x deg) :
    Module.finrank R A = 1 := by
  have : Unique (ExponentVector deg) :=
    ⟨⟨0⟩, fun f => Subtype.ext (Finsupp.ext fun i => isEmptyElim i)⟩
  rw [Module.finrank_eq_card_basis hx.basis, Fintype.card_unique]

/-- On a single generator of degree `1`, a free graded-commutative algebra over a commutative ring
satisfying the strong rank condition with `2` invertible has rank `2` (`R ⊕ Re`) and `e * e = 0`.
-/
theorem IsFreeGradedCommutative.finrank_single_degree_one {R : Type u} [CommRing R]
    [StrongRankCondition R] [Invertible (2 : R)] {A : Type v} [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} {x : Unit → A}
    (hx : IsFreeGradedCommutative 𝒜 x (fun _ => 1)) :
    Module.finrank R A = 2 ∧ x () * x () = 0 := by
  refine ⟨?_, hx.sq_eq_zero_of_odd (i := ()) odd_one⟩
  let e : ExponentVector (fun _ : Unit => (1 : ℕ)) ≃ Bool :=
    { toFun := fun f => f.1 () != 0
      invFun := fun b => if b then ExponentVector.single () else 0
      left_inv := fun f => by
        have hle : f.1 () ≤ 1 := f.2 () odd_one
        ext
        by_cases h0 : f.1 () = 0
        · simp [h0]
        · have h1 : f.1 () = 1 := by omega
          simp [h1]
      right_inv := fun b => by cases b <;> simp }
  rw [Module.finrank_eq_card_basis (hx.basis.reindex e), Fintype.card_bool]

/-- On a single generator of degree `2`, all odd-degree pieces vanish and every even nonnegative
degree `2n` is spanned by `x () ^ n`. -/
theorem IsFreeGradedCommutative.single_degree_two {R : Type u} [CommRing R]
    {A : Type v} [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {x : Unit → A}
    (hx : IsFreeGradedCommutative 𝒜 x (fun _ => 2)) :
    (∀ p : ℤ, Odd p → 𝒜 p = ⊥) ∧
      ∀ n : ℕ, 𝒜 (2 * n : ℕ) = Submodule.span R {x () ^ n} := by
  constructor
  · intro p hp
    rw [hx.grade_eq_span_standardMonomial p, Submodule.span_eq_bot]
    rintro _ ⟨f, hdeg, rfl⟩
    have hf : f.1 = Finsupp.single () (f.1 ()) := Finsupp.unique_single f.1
    have hev : Even (monomialDegree (fun _ : Unit => (2 : ℕ)) f.1) := by
      rw [hf, monomialDegree_single]
      exact even_two.mul_left _
    have hp' : Even p := hdeg ▸ (Int.even_natCast _).2 hev
    exact ((Int.not_even_iff_odd.2 hp) hp').elim
  · intro n
    rw [hx.grade_eq_span_standardMonomial (2 * n : ℕ)]
    congr 1
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f, hdeg, rfl⟩
      have hf : f.1 = Finsupp.single () (f.1 ()) := Finsupp.unique_single f.1
      rw [hf, monomialDegree_single] at hdeg
      have hfn : f.1 () = n := by omega
      rw [hf, hfn, standardMonomial_single]
    · rintro rfl
      refine ⟨ExponentVector.singlePow () n (fun h => ((Nat.not_odd_iff_even.2 even_two) h).elim),
        ?_, by simp⟩
      simp; ring

/-- A degree-`1` generator of a free graded-commutative algebra over a nontrivial commutative ring
with `2` invertible cannot be sent to the polynomial indeterminate `X : Polynomial R` by any
algebra homomorphism, because `e² = 0` while `X² ≠ 0`. -/
theorem no_algHom_degree_one_to_polynomial {R : Type u} [CommRing R] [Invertible (2 : R)]
    [Nontrivial R] :
    ¬ ∃ φ : SignedSym (InternalGrading.finsupp R fun _ : Unit => (1 : ℤ)) →ₐ[R] Polynomial R,
        φ (freeGradedCommutativeGen R (fun _ : Unit => 1) ()) = Polynomial.X := by
  rintro ⟨φ, hφ⟩
  have hsq : freeGradedCommutativeGen R (fun _ : Unit => 1) () *
      freeGradedCommutativeGen R (fun _ : Unit => 1) () = 0 :=
    (isFreeGradedCommutative_signedSym R (fun _ : Unit => 1)).sq_eq_zero_of_odd (i := ()) odd_one
  have hX : (Polynomial.X : Polynomial R) ^ 2 = 0 := by
    rw [sq]
    simpa [map_mul, hφ] using congrArg φ hsq
  have hc := congrArg (fun p : Polynomial R => p.coeff 2) hX
  simp [Polynomial.coeff_X_pow] at hc

end Checks

end TauCeti
