/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import TauCeti.Algebra.HopfAlgebra.CompactType.Haar
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Conjugate
import TauCeti.Algebra.Coalgebra.Comodule.Schur
import TauCeti.Algebra.Coalgebra.Comodule.Unitarization

/-!
# Weighted Schur orthogonality relations

Let `A` be a complex star bialgebra and `h : A →ₗ[ℂ] ℂ` an invariant integral. For finite comodules
with coefficient matrices `u` and `v`, left invariance of `h` turns the averaged matrix
`h (u X vᴴ)` into an intertwiner `u T vᴴ = T`, and right invariance turns `h (uᴴ X v)` into
`uᴴ T v = T`. When there is no nonzero comodule morphism `N → M`, Schur's lemma forces the
corresponding products `u i j * star (v k l)` or `star (u i j) * v k l` to lie in `ker h`, without
any positivity assumption.

When `M` is simple with a unitary coefficient matrix `u` and `h` is normalized and two-sided
invariant, the same averaging produces matrices `C` and `D` of trace `1` satisfying
`h (u i j * star (u k l)) = δ_{ik} C j l`, `h (star (u i j) * u k l) = δ_{jl} D i k`,
`uBarᴴ C uBar = C`, and `uBar D uBarᴴ = D`, where `uBar = u.map star` is the coefficient matrix of
the conjugate comodule (`TauCeti.Comodule.conjugateComodule`). Given any positive definite
`uBar`-invariant matrix `Q` (for instance the Haar Gram matrix of the conjugate comodule when `h`
is an `AlgebraicHaar`, or `Tᴴ T` when the conjugate comodule is unitarizable), Schur's lemma on the
simple conjugate comodule shows that `C` and `D` are positive definite scalar multiples of `Q` and
`Q⁻¹`, yielding a unique positive definite weight `Ft` with `Tr Ft = Tr Ft⁻¹` such that

* `h (star (u i j) * u k l) = δ_{jl} (Ft⁻¹ i k / Tr Ft⁻¹)`,
* `h (u i j * star (u k l)) = δ_{ik} (Ft j l / Tr Ft)`.

## Main declarations

* `LinearMap.IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero` and
  `LinearMap.IsRightInvariantIntegral.apply_star_mul_coefficientMatrix_eq_zero`: vanishing of
  matrix-coefficient inner products between comodules with no nonzero morphism between them.
* `TauCeti.Comodule.existsUnique_schurWeight_of_posDef_invariant`: weighted Schur orthogonality
  from a normalized two-sided invariant integral and any positive definite `uBar`-invariant form.
* `TauCeti.AlgebraicHaar.schurWeight`: the unique normalized Schur orthogonality weight attached to
  a simple unitary comodule.
* `TauCeti.AlgebraicHaar.schur_orthogonality`: existence and uniqueness of the positive definite
  weight `Ft` satisfying both weighted Schur orthogonality relations.

## References

* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Theorem 1.4.2.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Theorem 3.2.8.
* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 11.1.3.
-/

public section

open Module Matrix
open scoped ComplexOrder

namespace TauCeti.Comodule

section Helpers

private theorem coefficientMatrix_mul_map_apply_mul_conjTranspose
    {A M N ι κ : Type*} [Semiring A] [Bialgebra ℂ A] [StarRing A]
    [StarModule ℂ A] [StarCoalgebra ℂ A]
    [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
    [AddCommMonoid N] [Module ℂ N] [Comodule ℂ A N]
    [Fintype ι] [Fintype κ]
    {h : A →ₗ[ℂ] ℂ} (hhL : h.IsLeftInvariantIntegral)
    (b : Basis ι ℂ M) (c : Basis κ ℂ N) (X : Matrix ι κ ℂ) :
    let u := coefficientMatrix (C := A) b
    let v := coefficientMatrix (C := A) c
    let T : Matrix ι κ ℂ := (u * X.map (algebraMap ℂ A) * vᴴ).map h
    u * T.map (algebraMap ℂ A) * vᴴ = T.map (algebraMap ℂ A) := by
  intro u v T
  let ru (i j : ι) : Coalgebra.Repr ℂ (u i j) ι :=
    ⟨Finset.univ, fun r ↦ u i r, fun r ↦ u r j, (comul_coefficientMatrix_eq_sum b i j).symm⟩
  let rv (k l : κ) : Coalgebra.Repr ℂ (v k l) κ :=
    ⟨Finset.univ, fun s ↦ v k s, fun s ↦ v s l, (comul_coefficientMatrix_eq_sum c k l).symm⟩
  ext i k
  calc (u * T.map (algebraMap ℂ A) * vᴴ) i k
      = ∑ r, ∑ s, T r s • (u i r * star (v k s)) := by
        simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply,
          Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
          Finset.sum_mul]
        exact Finset.sum_comm
    _ = ∑ p, ∑ q, X p q •
          (∑ r, ∑ s, h (u r p * star (v s q)) • (u i r * star (v k s))) := by
        simp only [T, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply,
          Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
          Finset.sum_mul, map_sum, map_smul, Finset.sum_smul, Finset.smul_sum, smul_smul]
        trans ∑ rs : ι × κ, ∑ pq : ι × κ,
            (X pq.1 pq.2 * h (u rs.1 pq.1 * star (v rs.2 pq.2))) • (u i rs.1 * star (v k rs.2))
        · simp only [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ Finset.sum_comm
        · rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type]
    _ = ∑ p, ∑ q, X p q • (h (u i p * star (v k q)) • (1 : A)) := by
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
        congr 1
        simpa [ru, rv] using hhL.sum_sum_mul (ru i p) (rv k q).star
    _ = T.map (algebraMap ℂ A) i k := by
        simp only [T, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply,
          Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
          Finset.sum_mul, map_sum, map_smul, smul_eq_mul, smul_smul]
        exact Finset.sum_comm

private theorem conjTranspose_coefficientMatrix_mul_map_apply_mul
    {A M N ι κ : Type*} [Semiring A] [Bialgebra ℂ A] [StarRing A]
    [StarModule ℂ A] [StarCoalgebra ℂ A]
    [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
    [AddCommMonoid N] [Module ℂ N] [Comodule ℂ A N]
    [Fintype ι] [Fintype κ]
    {h : A →ₗ[ℂ] ℂ} (hhR : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) (c : Basis κ ℂ N) (X : Matrix ι κ ℂ) :
    let u := coefficientMatrix (C := A) b
    let v := coefficientMatrix (C := A) c
    let T : Matrix ι κ ℂ := (uᴴ * X.map (algebraMap ℂ A) * v).map h
    uᴴ * T.map (algebraMap ℂ A) * v = T.map (algebraMap ℂ A) := by
  intro u v T
  let ru (i j : ι) : Coalgebra.Repr ℂ (u i j) ι :=
    ⟨Finset.univ, fun r ↦ u i r, fun r ↦ u r j, (comul_coefficientMatrix_eq_sum b i j).symm⟩
  let rv (k l : κ) : Coalgebra.Repr ℂ (v k l) κ :=
    ⟨Finset.univ, fun s ↦ v k s, fun s ↦ v s l, (comul_coefficientMatrix_eq_sum c k l).symm⟩
  ext j l
  calc (uᴴ * T.map (algebraMap ℂ A) * v) j l
      = ∑ r, ∑ s, T r s • (star (u r j) * v s l) := by
        simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply,
          Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
          Finset.sum_mul]
        exact Finset.sum_comm
    _ = ∑ p, ∑ q, X p q •
          (∑ r, ∑ s, h (star (u p r) * v q s) • (star (u r j) * v s l)) := by
        simp only [T, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply,
          Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
          Finset.sum_mul, map_sum, map_smul, Finset.sum_smul, Finset.smul_sum, smul_smul]
        trans ∑ rs : ι × κ, ∑ pq : ι × κ,
            (X pq.1 pq.2 * h (star (u pq.1 rs.1) * v pq.2 rs.2)) • (star (u rs.1 j) * v rs.2 l)
        · simp only [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ Finset.sum_comm
        · rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type]
    _ = ∑ p, ∑ q, X p q • (h (star (u p j) * v q l) • (1 : A)) := by
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
        congr 1
        simpa [ru, rv] using hhR.sum_sum_mul (ru p j).star (rv q l)
    _ = T.map (algebraMap ℂ A) j l := by
        simp only [T, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply,
          Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
          Finset.sum_mul, map_sum, map_smul, smul_eq_mul, smul_smul]
        exact Finset.sum_comm

end Helpers

end TauCeti.Comodule

namespace LinearMap

open TauCeti TauCeti.Comodule

section OrthogonalityZero

variable {A M N ι κ : Type*} [Semiring A] [Bialgebra ℂ A] [StarRing A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
  [AddCommMonoid N] [Module ℂ N] [Comodule ℂ A N]
  {h : A →ₗ[ℂ] ℂ}

/-- If `h` is a left invariant integral, `c` has unitary coefficient matrix `v`, and there is no
nonzero comodule morphism `N → M`, then `h (u i j * star (v k l)) = 0` for all entries. -/
theorem IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (hhL : h.IsLeftInvariantIntegral) (b : Basis ι ℂ M) (c : Basis κ ℂ N)
    (hv : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (hzero : ∀ f : Comodule.Hom ℂ A N M, f = 0) (i j : ι) (k l : κ) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) c k l)) = 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  let X : Matrix ι κ ℂ := Matrix.single j l 1
  let T : Matrix ι κ ℂ := (u * X.map (algebraMap ℂ A) * vᴴ).map h
  have hinv : u * T.map (algebraMap ℂ A) * vᴴ = T.map (algebraMap ℂ A) :=
    coefficientMatrix_mul_map_apply_mul_conjTranspose hhL b c X
  have hv_unit : vᴴ * v = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hv).1
  have hinter : u * T.map (algebraMap ℂ A) = T.map (algebraMap ℂ A) * v := by
    calc u * T.map (algebraMap ℂ A)
        = (u * T.map (algebraMap ℂ A)) * (vᴴ * v) := by rw [hv_unit, Matrix.mul_one]
      _ = (u * T.map (algebraMap ℂ A) * vᴴ) * v := by rw [← Matrix.mul_assoc]
      _ = T.map (algebraMap ℂ A) * v := by rw [hinv]
  have hT0 : T = 0 := eq_zero_of_coefficientMatrix_mul_eq c b hzero hinter
  have hik : T i k = 0 := congrFun (congrFun hT0 i) k
  simpa [T, X, Matrix.mul_apply, Matrix.single_apply, conjTranspose_apply, ite_and] using hik

/-- If `h` is a right invariant integral, `b` has unitary coefficient matrix `u`, and there is no
nonzero comodule morphism `N → M`, then `h (star (u i j) * v k l) = 0` for all entries. -/
theorem IsRightInvariantIntegral.apply_star_mul_coefficientMatrix_eq_zero
    [Fintype ι] [DecidableEq ι] [Finite κ]
    (hhR : h.IsRightInvariantIntegral) (b : Basis ι ℂ M) (c : Basis κ ℂ N)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (hzero : ∀ f : Comodule.Hom ℂ A N M, f = 0) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  let X : Matrix ι κ ℂ := Matrix.single i k 1
  let T : Matrix ι κ ℂ := (uᴴ * X.map (algebraMap ℂ A) * v).map h
  have hinv : uᴴ * T.map (algebraMap ℂ A) * v = T.map (algebraMap ℂ A) :=
    conjTranspose_coefficientMatrix_mul_map_apply_mul hhR b c X
  have hu_unit : u * uᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2
  have hinter : u * T.map (algebraMap ℂ A) = T.map (algebraMap ℂ A) * v := by
    calc u * T.map (algebraMap ℂ A)
        = u * (uᴴ * T.map (algebraMap ℂ A) * v) := by rw [hinv]
      _ = (u * uᴴ) * T.map (algebraMap ℂ A) * v := by simp only [Matrix.mul_assoc]
      _ = T.map (algebraMap ℂ A) * v := by rw [hu_unit, Matrix.one_mul]
  have hT0 : T = 0 := eq_zero_of_coefficientMatrix_mul_eq c b hzero hinter
  have hjl : T j l = 0 := congrFun (congrFun hT0 j) l
  simpa [T, X, Matrix.mul_apply, Matrix.single_apply, conjTranspose_apply, ite_and] using hjl

end OrthogonalityZero

end LinearMap

namespace TauCeti.Comodule

section BialgebraWeight

variable {A M ι : Type*} [Semiring A] [Bialgebra ℂ A] [StarRing A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)]
  [Fintype ι] [DecidableEq ι]

private theorem exists_rightWeight_of_simple {h : A →ₗ[ℂ] ℂ}
    (h1 : h 1 = 1) (hhL : h.IsLeftInvariantIntegral) (hhR : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ C : Matrix ι ι ℂ,
      C.trace = 1 ∧
      ((coefficientMatrix (C := A) b).map star)ᴴ * C.map (algebraMap ℂ A) *
          (coefficientMatrix (C := A) b).map star = C.map (algebraMap ℂ A) ∧
      ∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then C j l else 0 := by
  set u := coefficientMatrix (C := A) b
  have hu1 : uᴴ * u = 1 := by simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).1
  have hu2 : u * uᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2
  have hscalar (j l : ι) : ∃ c : ℂ, ∀ i k, h (u i j * star (u k l)) = if i = k then c else 0 := by
    let X : Matrix ι ι ℂ := Matrix.single j l 1
    let T : Matrix ι ι ℂ := (u * X.map (algebraMap ℂ A) * uᴴ).map h
    have hinv := coefficientMatrix_mul_map_apply_mul_conjTranspose hhL b b X
    have hcomm : u * T.map (algebraMap ℂ A) = T.map (algebraMap ℂ A) * u := by
      calc u * T.map (algebraMap ℂ A)
          = (u * T.map (algebraMap ℂ A) * uᴴ) * u := by rw [Matrix.mul_assoc, hu1, Matrix.mul_one]
        _ = T.map (algebraMap ℂ A) * u := by rw [hinv]
    obtain ⟨c, hc⟩ := exists_eq_smul_one_of_coefficientMatrix_mul_eq b hcomm
    refine ⟨c, fun i k ↦ ?_⟩
    simpa [T, X, Matrix.mul_apply, Matrix.single_apply, conjTranspose_apply, Matrix.one_apply,
      ite_and] using congrFun (congrFun hc i) k
  choose Cfn hC using hscalar
  let C : Matrix ι ι ℂ := Matrix.of Cfn
  have : Nontrivial M := nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  obtain ⟨i₀⟩ := b.index_nonempty
  have htr : C.trace = 1 := by
    have hsum : ∑ j, C j j = h (∑ j, u i₀ j * star (u i₀ j)) :=
      (map_sum h _ _).symm ▸ Finset.sum_congr rfl fun j _ ↦ by simpa [C] using (hC j j i₀ i₀).symm
    have hu_ii : (∑ j, u i₀ j * star (u i₀ j)) = 1 := by
      simpa [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] using
        congrFun (congrFun hu2 i₀) i₀
    simp only [Matrix.trace, Matrix.diag_apply, hsum, hu_ii, h1]
  have hinv : (u.map star)ᴴ * C.map (algebraMap ℂ A) * u.map star = C.map (algebraMap ℂ A) := by
    let ru (i j : ι) : Coalgebra.Repr ℂ (u i j) ι :=
      ⟨Finset.univ, fun r ↦ u i r, fun r ↦ u r j, (comul_coefficientMatrix_eq_sum b i j).symm⟩
    ext j l
    have hR := hhR.sum_sum_mul (ru i₀ j) (ru i₀ l).star
    have hCeq (r s : ι) : h (u i₀ r * star (u i₀ s)) = C r s := by simpa [C] using hC r s i₀ i₀
    simp only [ru, Coalgebra.Repr.star_index, Coalgebra.Repr.star_left,
      Coalgebra.Repr.star_right, hCeq] at hR
    calc ((u.map star)ᴴ * C.map (algebraMap ℂ A) * u.map star) j l
        = ∑ r, ∑ s, C r s • (u r j * star (u s l)) := by
          simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, star_star,
            Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
            Finset.sum_mul]
          exact Finset.sum_comm
      _ = C j l • (1 : A) := hR
      _ = C.map (algebraMap ℂ A) j l := by simp [Algebra.algebraMap_eq_smul_one]
  exact ⟨C, htr, hinv, fun i j k l ↦ hC j l i k⟩

private theorem exists_leftWeight_of_simple {h : A →ₗ[ℂ] ℂ}
    (h1 : h 1 = 1) (hhL : h.IsLeftInvariantIntegral) (hhR : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ D : Matrix ι ι ℂ,
      D.trace = 1 ∧
      (coefficientMatrix (C := A) b).map star * D.map (algebraMap ℂ A) *
          ((coefficientMatrix (C := A) b).map star)ᴴ = D.map (algebraMap ℂ A) ∧
      ∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then D i k else 0 := by
  set u := coefficientMatrix (C := A) b
  have hu1 : uᴴ * u = 1 := by simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).1
  have hu2 : u * uᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2
  have hscalar (i k : ι) : ∃ d : ℂ, ∀ j l, h (star (u i j) * u k l) = if j = l then d else 0 := by
    let X : Matrix ι ι ℂ := Matrix.single i k 1
    let T : Matrix ι ι ℂ := (uᴴ * X.map (algebraMap ℂ A) * u).map h
    have hinv : uᴴ * T.map (algebraMap ℂ A) * u = T.map (algebraMap ℂ A) :=
      conjTranspose_coefficientMatrix_mul_map_apply_mul hhR b b X
    have hcomm : u * T.map (algebraMap ℂ A) = T.map (algebraMap ℂ A) * u := by
      calc u * T.map (algebraMap ℂ A)
          = u * (uᴴ * T.map (algebraMap ℂ A) * u) := by rw [hinv]
        _ = (u * uᴴ) * T.map (algebraMap ℂ A) * u := by simp only [Matrix.mul_assoc]
        _ = T.map (algebraMap ℂ A) * u := by rw [hu2, Matrix.one_mul]
    obtain ⟨d, hd⟩ := exists_eq_smul_one_of_coefficientMatrix_mul_eq b hcomm
    refine ⟨d, fun j l ↦ ?_⟩
    simpa [T, X, Matrix.mul_apply, Matrix.single_apply, conjTranspose_apply, Matrix.one_apply,
      ite_and] using congrFun (congrFun hd j) l
  choose Dfn hD using hscalar
  let D : Matrix ι ι ℂ := Matrix.of Dfn
  have : Nontrivial M := nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  obtain ⟨j₀⟩ := b.index_nonempty
  have htr : D.trace = 1 := by
    have hsum : ∑ i, D i i = h (∑ i, star (u i j₀) * u i j₀) :=
      (map_sum h _ _).symm ▸ Finset.sum_congr rfl fun i _ ↦ by simpa [D] using (hD i i j₀ j₀).symm
    have hu_jj : (∑ i, star (u i j₀) * u i j₀) = 1 := by
      simpa [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] using
        congrFun (congrFun hu1 j₀) j₀
    simp only [Matrix.trace, Matrix.diag_apply, hsum, hu_jj, h1]
  have hinv : u.map star * D.map (algebraMap ℂ A) * (u.map star)ᴴ = D.map (algebraMap ℂ A) := by
    let ru (i j : ι) : Coalgebra.Repr ℂ (u i j) ι :=
      ⟨Finset.univ, fun r ↦ u i r, fun r ↦ u r j, (comul_coefficientMatrix_eq_sum b i j).symm⟩
    ext i k
    have hL := hhL.sum_sum_mul (ru i j₀).star (ru k j₀)
    have hDeq (r s : ι) : h (star (u r j₀) * u s j₀) = D r s := by simpa [D] using hD r s j₀ j₀
    simp only [ru, Coalgebra.Repr.star_index, Coalgebra.Repr.star_left,
      Coalgebra.Repr.star_right, hDeq] at hL
    calc (u.map star * D.map (algebraMap ℂ A) * (u.map star)ᴴ) i k
        = ∑ r, ∑ s, D r s • (star (u i r) * u k s) := by
          simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, star_star,
            Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
            Finset.sum_mul]
          exact Finset.sum_comm
      _ = D i k • (1 : A) := hL
      _ = D.map (algebraMap ℂ A) i k := by simp [Algebra.algebraMap_eq_smul_one]
  exact ⟨D, htr, hinv, fun i j k l ↦ hD i k j l⟩

private theorem exists_smul_one_of_conjugate_invariance (b : Basis ι ℂ M)
    {D P : Matrix ι ι ℂ}
    (hDinv : (coefficientMatrix (C := A) b).map star * D.map (algebraMap ℂ A) *
        ((coefficientMatrix (C := A) b).map star)ᴴ = D.map (algebraMap ℂ A))
    (hPinv : ((coefficientMatrix (C := A) b).map star)ᴴ * P.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star = P.map (algebraMap ℂ A)) :
    ∃ c : ℂ, D * P = c • (1 : Matrix ι ι ℂ) := by
  let : Comodule ℂ A (ι → ℂ) := conjugateComodule (A := A) b
  have : IsSimpleOrder (Subcomodule ℂ A (ι → ℂ)) :=
    (isSimpleOrder_conjugateComodule_iff (A := A) b).mpr inferInstance
  set uBar := (coefficientMatrix (C := A) b).map star
  have huBar : coefficientMatrix (C := A) (Pi.basisFun ℂ ι) = uBar :=
    coefficientMatrix_conjugateComodule (A := A) b
  have hcomm : uBar * (D * P).map (algebraMap ℂ A) = (D * P).map (algebraMap ℂ A) * uBar := by
    rw [Matrix.map_mul]
    calc uBar * (D.map (algebraMap ℂ A) * P.map (algebraMap ℂ A))
        = uBar * D.map (algebraMap ℂ A) * (uBarᴴ * P.map (algebraMap ℂ A) * uBar) := by
          rw [hPinv, Matrix.mul_assoc]
      _ = (uBar * D.map (algebraMap ℂ A) * uBarᴴ) * P.map (algebraMap ℂ A) * uBar := by
          simp only [Matrix.mul_assoc]
      _ = D.map (algebraMap ℂ A) * P.map (algebraMap ℂ A) * uBar := by rw [hDinv]
  exact exists_eq_smul_one_of_coefficientMatrix_mul_eq (Pi.basisFun ℂ ι) (by rwa [huBar])

private theorem posDef_weights_of_posDef_invariant (b : Basis ι ℂ M)
    {C D Q : Matrix ι ι ℂ} (hCtr : C.trace = 1) (hDtr : D.trace = 1) (hQ : Q.PosDef)
    (hCinv : ((coefficientMatrix (C := A) b).map star)ᴴ * C.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star = C.map (algebraMap ℂ A))
    (hDinv : (coefficientMatrix (C := A) b).map star * D.map (algebraMap ℂ A) *
        ((coefficientMatrix (C := A) b).map star)ᴴ = D.map (algebraMap ℂ A))
    (hQinv : ((coefficientMatrix (C := A) b).map star)ᴴ * Q.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star = Q.map (algebraMap ℂ A)) :
    C.PosDef ∧ D = (C⁻¹.trace)⁻¹ • C⁻¹ := by
  have : Nontrivial M := nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  have hinv_pos {z : ℂ} (hz : 0 < z) : 0 < z⁻¹ := by
    rw [Complex.eq_re_of_ofReal_le (r := 0) hz.le, ← Complex.ofReal_inv, Complex.zero_lt_real]
    exact inv_pos.mpr (Complex.pos_iff.mp hz).1
  let _ := hQ.isUnit.invertible
  obtain ⟨μ, hDQ⟩ := exists_smul_one_of_conjugate_invariance b hDinv hQinv
  have hD_eq : D = μ • Q⁻¹ := by
    calc D = (D * Q) * Q⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
      _ = μ • Q⁻¹ := by rw [hDQ, Matrix.smul_mul, Matrix.one_mul]
  have hμ_eq : μ = (Q⁻¹.trace)⁻¹ := eq_inv_of_mul_eq_one_left (by
    simpa [hD_eq, Matrix.trace_smul, smul_eq_mul] using hDtr)
  have hD_pos : D.PosDef := hD_eq ▸ hQ.inv.smul (hμ_eq ▸ hinv_pos hQ.inv.trace_pos)
  let _ := hD_pos.isUnit.invertible
  obtain ⟨lam, hDC⟩ := exists_smul_one_of_conjugate_invariance b hDinv hCinv
  have hC_eq : C = lam • D⁻¹ := by
    calc C = D⁻¹ * (D * C) := by
          rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]
      _ = lam • D⁻¹ := by rw [hDC, Matrix.mul_smul, Matrix.mul_one]
  have hlam_eq : lam = (D⁻¹.trace)⁻¹ := eq_inv_of_mul_eq_one_left (by
    simpa [hC_eq, Matrix.trace_smul, smul_eq_mul] using hCtr)
  have hC_pos : C.PosDef := hC_eq ▸ hD_pos.inv.smul (hlam_eq ▸ hinv_pos hD_pos.inv.trace_pos)
  let _ := hC_pos.isUnit.invertible
  have hD_from_C : D = lam • C⁻¹ := by
    calc D = (D * C) * C⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
      _ = lam • C⁻¹ := by rw [hDC, Matrix.smul_mul, Matrix.one_mul]
  have hlam_C : lam = (C⁻¹.trace)⁻¹ := eq_inv_of_mul_eq_one_left (by
    simpa [hD_from_C, Matrix.trace_smul, smul_eq_mul] using hDtr)
  exact ⟨hC_pos, hlam_C ▸ hD_from_C⟩

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
private theorem unique_schurWeight_of_orthogonality [Nonempty ι] {h : A →ₗ[ℂ] ℂ}
    {u : Matrix ι ι A} {F₁ F₂ : Matrix ι ι ℂ}
    (hF₁ : F₁.PosDef) (hF₂ : F₂.PosDef)
    (htr₁ : F₁.trace = F₁⁻¹.trace) (htr₂ : F₂.trace = F₂⁻¹.trace)
    (horth₁ : ∀ i j k l, h (u i j * star (u k l)) = if i = k then F₁ j l / F₁.trace else 0)
    (horth₂ : ∀ i j k l, h (u i j * star (u k l)) = if i = k then F₂ j l / F₂.trace else 0) :
    F₁ = F₂ := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h₁_pos : 0 < F₁.trace := hF₁.trace_pos
  have h₂_pos : 0 < F₂.trace := hF₂.trace_pos
  have h₁_ne : F₁.trace ≠ 0 := h₁_pos.ne'
  have h₂_ne : F₂.trace ≠ 0 := h₂_pos.ne'
  set c : ℂ := F₁.trace / F₂.trace with hc_def
  have hc_ne : c ≠ 0 := div_ne_zero h₁_ne h₂_ne
  let _ := invertibleOfNonzero hc_ne
  have hF_eq : F₁ = c • F₂ := by
    ext j l
    have h1 := horth₁ i₀ j i₀ l
    have h2 := horth₂ i₀ j i₀ l
    simp only [↓reduceIte] at h1 h2
    have hdiv : F₁ j l / F₁.trace = F₂ j l / F₂.trace := h1.symm.trans h2
    rw [Matrix.smul_apply, smul_eq_mul, hc_def, div_mul_eq_mul_div, mul_div_assoc, ← hdiv,
      mul_div_cancel₀ _ h₁_ne]
  have hF_inv : F₁⁻¹ = c⁻¹ • F₂⁻¹ := by
    rw [hF_eq, Matrix.inv_smul F₂ c ((Matrix.isUnit_iff_isUnit_det _).mp hF₂.isUnit), invOf_eq_inv]
  have hc_sq : c * c = 1 := by
    have ht1 : F₁.trace = c * F₂.trace := by simp [hF_eq, Matrix.trace_smul]
    have ht2 : F₁⁻¹.trace = c⁻¹ * F₂.trace := by simp [hF_inv, Matrix.trace_smul, ← htr₂]
    have hceq : c = c⁻¹ := mul_right_cancel₀ h₂_ne (ht1.symm.trans (htr₁.trans ht2))
    exact (congrArg (· * c) hceq).trans (inv_mul_cancel₀ hc_ne)
  have hc_pos : 0 < c := by
    rw [hc_def, Complex.eq_re_of_ofReal_le (r := 0) h₁_pos.le,
      Complex.eq_re_of_ofReal_le (r := 0) h₂_pos.le, ← Complex.ofReal_div, Complex.zero_lt_real]
    exact div_pos (Complex.pos_iff.mp h₁_pos).1 (Complex.pos_iff.mp h₂_pos).1
  have hc1 : c = 1 := (mul_self_eq_one_iff.mp hc_sq).resolve_right fun h ↦ by
    have hre := (Complex.pos_iff.mp (h ▸ hc_pos)).1
    norm_num at hre
  rw [hF_eq, hc1, one_smul]

/-- **Weighted Schur orthogonality from a positive definite conjugate-invariant form.**
Given a normalized two-sided invariant integral `h` on a complex star bialgebra, a simple comodule
with unitary coefficient matrix `u`, and any positive definite matrix `Q` satisfying
`(u.map star)ᴴ * Q * u.map star = Q`, there is a unique positive definite weight `Ft` with
`Tr Ft = Tr Ft⁻¹` realizing both weighted Schur orthogonality relations. -/
theorem existsUnique_schurWeight_of_posDef_invariant {h : A →ₗ[ℂ] ℂ}
    (h1 : h 1 = 1) (hhL : h.IsLeftInvariantIntegral) (hhR : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Q : Matrix ι ι ℂ} (hQ : Q.PosDef)
    (hQinv : ((coefficientMatrix (C := A) b).map star)ᴴ * Q.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star = Q.map (algebraMap ℂ A)) :
    ∃! Ft : Matrix ι ι ℂ,
      Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      ((coefficientMatrix (C := A) b).map star)ᴴ * Ft.map (algebraMap ℂ A) *
          (coefficientMatrix (C := A) b).map star = Ft.map (algebraMap ℂ A) ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  have : Nontrivial M := nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  obtain ⟨C, hCtr, hCinv, hC⟩ := exists_rightWeight_of_simple h1 hhL hhR b hu
  obtain ⟨D, hDtr, hDinv, hD⟩ := exists_leftWeight_of_simple h1 hhL hhR b hu
  obtain ⟨hC_pos, hD_eq⟩ := posDef_weights_of_posDef_invariant b hCtr hDtr hQ hCinv hDinv hQinv
  have hCinv_tr_pos : 0 < C⁻¹.trace := hC_pos.inv.trace_pos
  have hCinv_re_pos : 0 < C⁻¹.trace.re := (Complex.pos_iff.mp hCinv_tr_pos).1
  set r : ℝ := Real.sqrt C⁻¹.trace.re
  have hrC_pos : (0 : ℂ) < (r : ℂ) := Complex.zero_lt_real.mpr (Real.sqrt_pos.mpr hCinv_re_pos)
  have hr_ne : (r : ℂ) ≠ 0 := hrC_pos.ne'
  let _ := invertibleOfNonzero hr_ne
  have hr_sq : (r : ℂ) * (r : ℂ) = C⁻¹.trace := by
    rw [Complex.eq_re_of_ofReal_le (r := 0) hCinv_tr_pos.le, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hCinv_re_pos.le]
  set Ft : Matrix ι ι ℂ := (r : ℂ) • C
  have hFt_pos : Ft.PosDef := hC_pos.smul hrC_pos
  have hFt_tr : Ft.trace = (r : ℂ) := by simp [Ft, Matrix.trace_smul, hCtr]
  have hFt_inv : Ft⁻¹ = (r : ℂ)⁻¹ • C⁻¹ := by
    dsimp only [Ft]
    rw [Matrix.inv_smul C (r : ℂ) ((Matrix.isUnit_iff_isUnit_det _).mp hC_pos.isUnit),
      invOf_eq_inv]
  have hFt_inv_tr : Ft⁻¹.trace = (r : ℂ) := by
    rw [hFt_inv, Matrix.trace_smul, smul_eq_mul, ← hr_sq]; field_simp [hr_ne]
  have hFt_map : Ft.map (algebraMap ℂ A) = (r : ℂ) • C.map (algebraMap ℂ A) := by
    ext i j; simp [Ft, Algebra.algebraMap_eq_smul_one, smul_smul]
  have hFt_inv_eq : ((coefficientMatrix (C := A) b).map star)ᴴ * Ft.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = Ft.map (algebraMap ℂ A) := by
    rw [hFt_map, Matrix.mul_smul, Matrix.smul_mul]
    exact congrArg ((r : ℂ) • ·) hCinv
  have hFt_orth₂ : ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0 := fun i j k l ↦ by
    rw [hC, hFt_tr]; split_ifs <;> simp [Ft, hr_ne]
  refine ⟨Ft, ⟨hFt_pos, hFt_tr.trans hFt_inv_tr.symm, hFt_inv_eq, ?_, hFt_orth₂⟩,
    fun G ⟨hG, hGtr, _, _, hGorth⟩ ↦
      unique_schurWeight_of_orthogonality hG hFt_pos hGtr (hFt_tr.trans hFt_inv_tr.symm)
        hGorth hFt_orth₂⟩
  intro i j k l
  rw [hD, hD_eq, hFt_inv_tr, hFt_inv]
  split_ifs with hjl
  · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← hr_sq]
    field_simp [hr_ne]
  · rfl

end BialgebraWeight

end TauCeti.Comodule

namespace TauCeti.AlgebraicHaar

open TauCeti.Comodule

section Orthogonality

variable {A : Type*} [Ring A] [HopfAlgebra ℂ A] [StarRing A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]

/-- For an algebraic Haar state, matrix coefficients of comodules with no nonzero morphism
`N → M` satisfy `h (u i j * star (v k l)) = 0` whenever `v` is unitary. -/
theorem apply_coefficientMatrix_mul_star_eq_zero {M N ι κ : Type*}
    [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
    [AddCommMonoid N] [Module ℂ N] [Comodule ℂ A N]
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (h : AlgebraicHaar A) (b : Basis ι ℂ M) (c : Basis κ ℂ N)
    (hv : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (hzero : ∀ f : Comodule.Hom ℂ A N M, f = 0) (i j : ι) (k l : κ) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) c k l)) = 0 :=
  h.isLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero b c hv hzero i j k l

/-- For an algebraic Haar state, matrix coefficients of comodules with no nonzero morphism
`N → M` satisfy `h (star (u i j) * v k l) = 0` whenever `u` is unitary. -/
theorem apply_star_mul_coefficientMatrix_eq_zero {M N ι κ : Type*}
    [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
    [AddCommMonoid N] [Module ℂ N] [Comodule ℂ A N]
    [Fintype ι] [DecidableEq ι] [Finite κ]
    (h : AlgebraicHaar A) (b : Basis ι ℂ M) (c : Basis κ ℂ N)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (hzero : ∀ f : Comodule.Hom ℂ A N M, f = 0) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 :=
  h.isRightInvariantIntegral.apply_star_mul_coefficientMatrix_eq_zero b c hu hzero i j k l

section Simple

variable {M ι : Type*} [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M]
  [IsSimpleOrder (Subcomodule ℂ A M)] [Fintype ι] [DecidableEq ι]

private theorem existsUnique_schurWeight_aux (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ,
      Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      ((coefficientMatrix (C := A) b).map star)ᴴ * Ft.map (algebraMap ℂ A) *
          (coefficientMatrix (C := A) b).map star = Ft.map (algebraMap ℂ A) ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  let : Comodule ℂ A (ι → ℂ) := conjugateComodule (A := A) b
  set Q := haarGramMatrix (A := A) h.toLinearMap (Pi.basisFun ℂ ι)
  have hQ : Q.PosDef := posDef_haarGramMatrix (fun a ha ↦ h.map_star_mul_self_pos ha)
    (Pi.basisFun ℂ ι)
  have hQinv : ((coefficientMatrix (C := A) b).map star)ᴴ * Q.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = Q.map (algebraMap ℂ A) := by
    simpa [Q, coefficientMatrix_conjugateComodule] using
      conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul h.isRightInvariantIntegral
        (Pi.basisFun ℂ ι)
  exact existsUnique_schurWeight_of_posDef_invariant h.map_one
    h.isLeftInvariantIntegral h.isRightInvariantIntegral b hu hQ hQinv

/-- The unique positive definite Schur orthogonality weight `Ft` attached to an algebraic
Haar state `h` and a simple unitary comodule in a basis `b`. -/
noncomputable def schurWeight (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) : Matrix ι ι ℂ :=
  (existsUnique_schurWeight_aux h b hu).exists.choose

/-- The Schur orthogonality weight `h.schurWeight b hu` is positive definite. -/
theorem posDef_schurWeight (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (h.schurWeight b hu).PosDef :=
  (existsUnique_schurWeight_aux h b hu).exists.choose_spec.1

/-- The Schur orthogonality weight satisfies `Tr Ft = Tr Ft⁻¹`. -/
theorem trace_schurWeight_eq_trace_inv (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (h.schurWeight b hu).trace = (h.schurWeight b hu)⁻¹.trace :=
  (existsUnique_schurWeight_aux h b hu).exists.choose_spec.2.1

/-- The Schur orthogonality weight is invariant under the conjugate coefficient matrix:
`(u.map star)ᴴ * Ft * (u.map star) = Ft`. -/
theorem conjTranspose_map_star_mul_schurWeight_mul (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ((coefficientMatrix (C := A) b).map star)ᴴ * (h.schurWeight b hu).map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star =
      (h.schurWeight b hu).map (algebraMap ℂ A) :=
  (existsUnique_schurWeight_aux h b hu).exists.choose_spec.2.2.1

/-- First weighted Schur orthogonality relation:
`h (star (u i j) * u k l) = δ_{jl} (Ft⁻¹ i k / Tr Ft⁻¹)`. -/
theorem apply_star_mul_coefficientMatrix (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
      if j = l then (h.schurWeight b hu)⁻¹ i k / (h.schurWeight b hu)⁻¹.trace else 0 :=
  (existsUnique_schurWeight_aux h b hu).exists.choose_spec.2.2.2.1 i j k l

/-- Second weighted Schur orthogonality relation:
`h (u i j * star (u k l)) = δ_{ik} (Ft j l / Tr Ft)`. -/
theorem apply_coefficientMatrix_mul_star (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
      if i = k then h.schurWeight b hu j l / (h.schurWeight b hu).trace else 0 :=
  (existsUnique_schurWeight_aux h b hu).exists.choose_spec.2.2.2.2 i j k l

/-- Uniqueness of the Schur orthogonality weight from positivity, trace symmetry, and the second
orthogonality relation. -/
theorem eq_schurWeight (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {G : Matrix ι ι ℂ} (hG : G.PosDef) (htr : G.trace = G⁻¹.trace)
    (horth : ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then G j l / G.trace else 0) :
    G = h.schurWeight b hu := by
  have : Nontrivial M := nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  exact unique_schurWeight_of_orthogonality hG (h.posDef_schurWeight b hu) htr
    (h.trace_schurWeight_eq_trace_inv b hu) horth (h.apply_coefficientMatrix_mul_star b hu)

/-- **Weighted Schur orthogonality.** For a simple comodule with a finite basis `b` whose
coefficient matrix `u` is unitary, there is a unique positive definite weight `Ft` with
`Tr Ft = Tr Ft⁻¹` satisfying both weighted orthogonality relations for `h`. -/
theorem schur_orthogonality (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ,
      Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  ⟨h.schurWeight b hu,
    ⟨h.posDef_schurWeight b hu, h.trace_schurWeight_eq_trace_inv b hu,
      h.apply_star_mul_coefficientMatrix b hu, h.apply_coefficientMatrix_mul_star b hu⟩,
    fun _ ⟨hG, htr, _, horth⟩ ↦ h.eq_schurWeight b hu hG htr horth⟩

end Simple

end Orthogonality

end TauCeti.AlgebraicHaar
