/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.BetaGamma.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Grading, conformal derivation, and weight-space finiteness of the beta-gamma Fock space

The polynomial Fock space `TauCeti.BetaGamma.Fock R ι` carries a conformal `ℕ`-grading
(`TauCeti.BetaGamma.degreeSubmodule`) and, for any assignment of weights `wt : ι → W` into an
additive abelian group `W`, a `(ℕ × W)`-bigradation (`TauCeti.BetaGamma.biGradedSubmodule`) given
on creation variables by

* `deg(β_{i, -k - 1}) = k + 1` and `wt(β_{i, -k - 1}) = wt i`,
* `deg(γ_{i, -k}) = k` and `wt(γ_{i, -k}) = -wt i`.

In particular, the zero modes `γ_{i, 0}` have conformal degree `0` and root weight `-wt i`, so
the degree-zero subspace `degreeSubmodule R ι 0` is isomorphic as an `R`-algebra to the polynomial
algebra `MvPolynomial ι R` (`TauCeti.BetaGamma.degreeZeroAlgEquiv`), and is never finitely
generated when `ι` is nonempty and `R` is nontrivial
(`TauCeti.BetaGamma.not_module_finite_degreeSubmodule_zero`).

Once refined by any root-weight map admitting a positive height homomorphism `ht : W →+ ℤ` (such
as the positive roots of a reductive Lie algebra, or the canonical basis in
`TauCeti.Algebra.Vertex.BetaGamma.Character`), every bigraded weight space is finitely generated
(`TauCeti.BetaGamma.module_finite_biGradedSubmodule`) with exact rank counting the corresponding
exponent monomials (`TauCeti.BetaGamma.finrank_biGradedSubmodule`).

## Main definitions

* `TauCeti.BetaGamma.conformalWeight`, `TauCeti.BetaGamma.rootWeight`, `TauCeti.BetaGamma.biWeight`:
  the degree and root-weight assignments on creation variables.
* `TauCeti.BetaGamma.degreeSubmodule`, `TauCeti.BetaGamma.biGradedSubmodule`: the graded and
  bigraded pieces of `Fock R ι`.
* `TauCeti.BetaGamma.degreeDerivation`: the conformal degree derivation `L₀` acting by `d` on
  `degreeSubmodule R ι d`.
* `TauCeti.BetaGamma.degreeZeroSubalgebra`, `TauCeti.BetaGamma.degreeZeroAlgEquiv`: identification
  of the degree-zero subalgebra with `MvPolynomial ι R`.

## Main results

* `TauCeti.BetaGamma.degreeDerivation_of_mem_degreeSubmodule`,
  `TauCeti.BetaGamma.lie_degreeDerivation_betaMode`,
  `TauCeti.BetaGamma.lie_degreeDerivation_gammaMode`,
  `TauCeti.BetaGamma.lie_degreeDerivation_translation`: action and commutation relations of `L₀`.
* `TauCeti.BetaGamma.betaMode_mem_biGradedSubmodule`,
  `TauCeti.BetaGamma.gammaMode_mem_biGradedSubmodule`,
  `TauCeti.BetaGamma.translation_mem_biGradedSubmodule`: degree and weight shifts of modes and `T`.
* `TauCeti.BetaGamma.not_module_finite_degreeSubmodule_zero`: degree `0` is infinite-rank when
  `ι` is nonempty and `R` is nontrivial.
* `TauCeti.BetaGamma.module_finite_biGradedSubmodule`,
  `TauCeti.BetaGamma.finrank_biGradedSubmodule`: finiteness and exact rank of bigraded weight
  spaces.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §5.4.1, pp. 142–143.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §11.3.
-/

public section

noncomputable section

open Finset MvPolynomial

attribute [local instance] LieRing.ofAssociativeRing

namespace TauCeti.BetaGamma

variable {ι W : Type*}

/-! ### Conformal weights, root weights, and bigraded submodules -/

/-- Conformal degree of a creation variable: `deg(β_{i, -k - 1}) = k + 1` and
`deg(γ_{i, -k}) = k`. -/
def conformalWeight : Var ι → ℕ
  | .beta _ k => k + 1
  | .gamma _ k => k

@[simp]
theorem conformalWeight_beta (i : ι) (k : ℕ) : conformalWeight (Var.beta i k) = k + 1 := (rfl)

@[simp]
theorem conformalWeight_gamma (i : ι) (k : ℕ) : conformalWeight (Var.gamma i k) = k := (rfl)

/-- Every variable's order is bounded above by its conformal weight. -/
theorem order_le_conformalWeight (v : Var ι) : v.order ≤ conformalWeight v := by
  cases v with
  | beta _ k => simp
  | gamma _ k => simp

/-- Root-weight assignment induced by `wt : ι → W`: `β`-variables carry `+wt i` and
`γ`-variables carry `-wt i`. -/
def rootWeight [AddCommGroup W] (wt : ι → W) : Var ι → W
  | .beta i _ => wt i
  | .gamma i _ => -wt i

@[simp]
theorem rootWeight_beta [AddCommGroup W] (wt : ι → W) (i : ι) (k : ℕ) :
    rootWeight wt (Var.beta i k) = wt i := (rfl)

@[simp]
theorem rootWeight_gamma [AddCommGroup W] (wt : ι → W) (i : ι) (k : ℕ) :
    rootWeight wt (Var.gamma i k) = -wt i := (rfl)

/-- Combined `(degree, root weight)` assignment on creation variables. -/
def biWeight [AddCommGroup W] (wt : ι → W) (v : Var ι) : ℕ × W :=
  (conformalWeight v, rootWeight wt v)

@[simp]
theorem biWeight_beta [AddCommGroup W] (wt : ι → W) (i : ι) (k : ℕ) :
    biWeight wt (Var.beta i k) = (k + 1, wt i) := (rfl)

@[simp]
theorem biWeight_gamma [AddCommGroup W] (wt : ι → W) (i : ι) (k : ℕ) :
    biWeight wt (Var.gamma i k) = (k, -wt i) := (rfl)

@[simp]
theorem fst_biWeight [AddCommGroup W] (wt : ι → W) (v : Var ι) :
    (biWeight wt v).1 = conformalWeight v := (rfl)

@[simp]
theorem snd_biWeight [AddCommGroup W] (wt : ι → W) (v : Var ι) :
    (biWeight wt v).2 = rootWeight wt v := (rfl)

@[simp]
theorem fst_weight_biWeight [AddCommGroup W] (wt : ι → W) (e : Var ι →₀ ℕ) :
    (Finsupp.weight (biWeight wt) e).1 = Finsupp.weight conformalWeight e := by
  induction e using Finsupp.induction with
  | zero => simp
  | single_add v n f _ _ ih => simp [map_add, Finsupp.weight_single, ih]

@[simp]
theorem snd_weight_biWeight [AddCommGroup W] (wt : ι → W) (e : Var ι →₀ ℕ) :
    (Finsupp.weight (biWeight wt) e).2 = Finsupp.weight (rootWeight wt) e := by
  induction e using Finsupp.induction with
  | zero => simp
  | single_add v n f _ _ ih => simp [map_add, Finsupp.weight_single, ih]

section Submodules

variable (R : Type*) [CommRing R]

/-- The conformal-degree `d` submodule of `Fock R ι`. -/
abbrev degreeSubmodule (ι : Type*) : ℕ → Submodule R (Fock R ι) :=
  weightedHomogeneousSubmodule R (conformalWeight (ι := ι))

/-- The bigraded `(d, w)` weight space of `Fock R ι` for a root-weight assignment `wt : ι → W`. -/
abbrev biGradedSubmodule [AddCommGroup W] (wt : ι → W) : ℕ × W → Submodule R (Fock R ι) :=
  weightedHomogeneousSubmodule R (biWeight wt)

/-- `Fock R ι` is an `ℕ`-graded algebra by conformal weight. -/
@[instance_reducible]
def degreeGradedAlgebra (ι : Type*) : GradedAlgebra (degreeSubmodule R ι) :=
  weightedGradedAlgebra R (conformalWeight (ι := ι))

/-- `Fock R ι` is a `(ℕ × W)`-graded algebra by conformal degree and root weight. -/
@[instance_reducible]
def biGradedAlgebra [AddCommGroup W] [DecidableEq W] (wt : ι → W) :
    GradedAlgebra (biGradedSubmodule R wt) :=
  weightedGradedAlgebra R (biWeight wt)

/-- Every bigraded piece `(d, w)` lies inside the conformal-degree `d` submodule. -/
theorem biGradedSubmodule_le_degreeSubmodule [AddCommGroup W] (wt : ι → W) (d : ℕ) (w : W) :
    biGradedSubmodule R wt (d, w) ≤ degreeSubmodule R ι d := by
  intro p hp e he
  have h1 := congrArg Prod.fst (hp he)
  simpa using h1

theorem one_mem_degreeSubmodule : (1 : Fock R ι) ∈ degreeSubmodule R ι 0 :=
  isWeightedHomogeneous_one R conformalWeight

theorem X_beta_mem_degreeSubmodule (i : ι) (k : ℕ) :
    (X (Var.beta i k) : Fock R ι) ∈ degreeSubmodule R ι (k + 1) :=
  isWeightedHomogeneous_X R conformalWeight (Var.beta i k)

theorem X_gamma_mem_degreeSubmodule (i : ι) (k : ℕ) :
    (X (Var.gamma i k) : Fock R ι) ∈ degreeSubmodule R ι k :=
  isWeightedHomogeneous_X R conformalWeight (Var.gamma i k)

theorem one_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) :
    (1 : Fock R ι) ∈ biGradedSubmodule R wt (0, 0) :=
  isWeightedHomogeneous_one R (biWeight wt)

theorem X_beta_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) (i : ι) (k : ℕ) :
    (X (Var.beta i k) : Fock R ι) ∈ biGradedSubmodule R wt (k + 1, wt i) :=
  isWeightedHomogeneous_X R (biWeight wt) (Var.beta i k)

theorem X_gamma_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) (i : ι) (k : ℕ) :
    (X (Var.gamma i k) : Fock R ι) ∈ biGradedSubmodule R wt (k, -wt i) :=
  isWeightedHomogeneous_X R (biWeight wt) (Var.gamma i k)

/-- The vector `γ_{i, 0}² · 1` lies in conformal degree `0`. Together with
`TauCeti.BetaGamma.X_gamma_zero_sq_ne_zero`, this shows it is a nonzero degree-zero vector. -/
theorem X_gamma_zero_sq_mem_degreeSubmodule_zero (i : ι) :
    (X (Var.gamma i 0) : Fock R ι) ^ 2 ∈ degreeSubmodule R ι 0 := by
  simpa using (X_gamma_mem_degreeSubmodule R i 0).pow 2

/-! ### Conformal degree derivation `L₀` -/

/-- The conformal degree derivation `L₀` on `Fock R ι`, acting on creation variables by
`L₀(β_{i, -k - 1}) = (k + 1) β_{i, -k - 1}` and `L₀(γ_{i, -k}) = k γ_{i, -k}`. -/
def degreeDerivation (ι : Type*) : Derivation R (Fock R ι) (Fock R ι) :=
  mkDerivation R fun v ↦ (conformalWeight v : R) • X v

theorem degreeDerivation_one : degreeDerivation R ι 1 = 0 :=
  Derivation.map_one_eq_zero (degreeDerivation R ι)

@[simp]
theorem degreeDerivation_X (v : Var ι) :
    degreeDerivation R ι (X v) = (conformalWeight v : R) • X v :=
  mkDerivation_X R _ v

theorem degreeDerivation_X_beta (i : ι) (k : ℕ) :
    degreeDerivation R ι (X (Var.beta i k)) = ((k + 1 : ℕ) : R) • X (Var.beta i k) :=
  degreeDerivation_X R (Var.beta i k)

theorem degreeDerivation_X_gamma (i : ι) (k : ℕ) :
    degreeDerivation R ι (X (Var.gamma i k)) = (k : R) • X (Var.gamma i k) :=
  degreeDerivation_X R (Var.gamma i k)

/-- On any monomial `monomial e r`, `L₀` acts as multiplication by
`Finsupp.weight conformalWeight e`. -/
theorem degreeDerivation_monomial (e : Var ι →₀ ℕ) (r : R) :
    degreeDerivation R ι (monomial e r) =
      (Finsupp.weight conformalWeight e : R) • monomial e r := by
  rw [monomial_eq, ← MvPolynomial.algebraMap_eq, Derivation.leibniz, Derivation.map_algebraMap,
    smul_zero, add_zero, smul_eq_mul]
  have hprod : degreeDerivation R ι (e.prod fun v n ↦ (X v : Fock R ι) ^ n) =
      (Finsupp.weight conformalWeight e : R) • (e.prod fun v n ↦ (X v : Fock R ι) ^ n) := by
    induction e using Finsupp.induction with
    | zero => simp
    | single_add v n f _ hn ih =>
      rw [Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
        Finsupp.prod_single_index (h := fun v n ↦ (X v : Fock R ι) ^ n) (pow_zero _),
        Derivation.leibniz, Derivation.leibniz_pow, degreeDerivation_X, ih, map_add,
        Finsupp.weight_single, Nat.cast_add, add_smul]
      simp only [smul_eq_mul, Nat.cast_mul, mul_smul_comm, ← Nat.cast_smul_eq_nsmul R, smul_smul]
      rw [← pow_succ, show n - 1 + 1 = n by omega, mul_comm (f.prod _), add_comm]
  rw [hprod, mul_smul_comm]

/-- `L₀` acts as scalar multiplication by `d` on the conformal-degree `d` submodule. -/
theorem degreeDerivation_of_mem_degreeSubmodule {d : ℕ} {p : Fock R ι}
    (hp : p ∈ degreeSubmodule R ι d) :
    degreeDerivation R ι p = (d : R) • p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, smul_sum]
  refine sum_congr rfl fun e he ↦ ?_
  rw [degreeDerivation_monomial, hp (Finsupp.mem_support_iff.mp he)]

private theorem lie_degreeDerivation_mulLeft_X (v : Var ι) :
    ⁅(degreeDerivation R ι).toLinearMap, LinearMap.mulLeft R (X v : Fock R ι)⁆ =
      (conformalWeight v : ℤ) • LinearMap.mulLeft R (X v : Fock R ι) := by
  apply LinearMap.ext
  intro p
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, mul_apply_eq_comp,
    mul_apply_eq_comp, LinearMap.smul_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, degreeDerivation_X, smul_eq_mul, smul_eq_mul,
    mul_smul_comm, mul_comm p (X v), add_sub_cancel_left, natCast_zsmul,
    ← Nat.cast_smul_eq_nsmul R]

private theorem lie_degreeDerivation_pderiv (v : Var ι) :
    ⁅(degreeDerivation R ι).toLinearMap, (pderiv (R := R) v).toLinearMap⁆ =
      -(conformalWeight v : ℤ) • (pderiv (R := R) v).toLinearMap := by
  classical
  have hder : ⁅degreeDerivation R ι, pderiv (R := R) v⁆ =
      -((conformalWeight v : R) • pderiv (R := R) v) := by
    apply MvPolynomial.derivation_ext
    intro w
    rw [Derivation.commutator_apply, neg_apply, smul_apply, pderiv_X,
      degreeDerivation_X, (pderiv (R := R) v).map_smul, pderiv_X]
    by_cases hvw : w = v
    · subst hvw
      simp
    · simp [Pi.single_eq_of_ne hvw]
  apply LinearMap.ext
  intro p
  have := congrArg (fun D : Derivation R (Fock R ι) (Fock R ι) ↦ D p) hder
  rw [Derivation.commutator_apply, neg_apply, smul_apply] at this
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, mul_apply_eq_comp,
    mul_apply_eq_comp, Derivation.coeFn_coe, Derivation.coeFn_coe, this, LinearMap.smul_apply,
    Derivation.coeFn_coe, neg_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul R]

/-- **Degree commutation for beta modes:** `[L₀, β_{i, n}] = -n · β_{i, n}`. -/
theorem lie_degreeDerivation_betaMode (i : ι) (n : ℤ) :
    ⁅(degreeDerivation R ι).toLinearMap, betaMode R i n⁆ = (-n) • betaMode R i n := by
  rcases le_or_gt 0 n with hn | hn
  · rw [betaMode_of_nonneg R i hn, lie_degreeDerivation_pderiv, conformalWeight_gamma,
      show (n.toNat : ℤ) = n by omega, neg_smul]
  · rw [betaMode_of_neg R i hn, lie_degreeDerivation_mulLeft_X, conformalWeight_beta,
      show (((-n - 1).toNat + 1 : ℕ) : ℤ) = -n by omega]

/-- **Degree commutation for gamma modes:** `[L₀, γ_{i, n}] = -n · γ_{i, n}`. -/
theorem lie_degreeDerivation_gammaMode (i : ι) (n : ℤ) :
    ⁅(degreeDerivation R ι).toLinearMap, gammaMode R i n⁆ = (-n) • gammaMode R i n := by
  rcases le_or_gt n 0 with hn | hn
  · rw [gammaMode_of_nonpos R i hn, lie_degreeDerivation_mulLeft_X, conformalWeight_gamma,
      show ((-n).toNat : ℤ) = -n by omega]
  · rw [gammaMode_of_pos R i hn, lie_neg, lie_degreeDerivation_pderiv, conformalWeight_beta,
      show (((n - 1).toNat + 1 : ℕ) : ℤ) = n by omega, neg_smul, neg_neg, smul_neg, neg_smul,
      neg_neg]

/-- **Degree commutation for translation:** `[L₀, T] = T`. -/
theorem lie_degreeDerivation_translation :
    ⁅degreeDerivation R ι, translation R ι⁆ = translation R ι := by
  apply MvPolynomial.derivation_ext
  intro v
  rw [Derivation.commutator_apply]
  cases v with
  | beta i k =>
    rw [translation_X_beta, (degreeDerivation R ι).map_smul, degreeDerivation_X_beta,
      degreeDerivation_X_beta, (translation R ι).map_smul, translation_X_beta, smul_smul,
      smul_smul, ← sub_smul]
    congr 1
    push_cast
    ring
  | gamma i k =>
    rw [translation_X_gamma, (degreeDerivation R ι).map_smul, degreeDerivation_X_gamma,
      degreeDerivation_X_gamma, (translation R ι).map_smul, translation_X_gamma, smul_smul,
      smul_smul, ← sub_smul]
    congr 1
    push_cast
    ring

/-! ### Degree and weight shifts of modes and translation -/

private theorem pderiv_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) (v : Var ι)
    {d : ℕ} {w : W} {p : Fock R ι} (hp : p ∈ biGradedSubmodule R wt (d, w))
    (hd : conformalWeight v ≤ d) :
    pderiv v p ∈ biGradedSubmodule R wt (d - conformalWeight v, w - rootWeight wt v) := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun e he ↦ ?_
  have hwt : Finsupp.weight (biWeight wt) e = (d, w) := hp (Finsupp.mem_support_iff.mp he)
  rw [pderiv_monomial]
  by_cases hv : e v = 0
  · simp [hv]
  · refine isWeightedHomogeneous_monomial (biWeight wt) _ _ ?_
    have hle : Finsupp.single v 1 ≤ e :=
      Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hv)
    have hadd : Finsupp.weight (biWeight wt) (e - Finsupp.single v 1) +
        (conformalWeight v, rootWeight wt v) = (d, w) := by
      rw [← biWeight, ← one_smul ℕ (biWeight wt v), ← Finsupp.weight_single, ← map_add,
        tsub_add_cancel_of_le hle, hwt]
    ext
    · have h1 := congrArg Prod.fst hadd
      dsimp at h1
      omega
    · have h2 := congrArg Prod.snd hadd
      dsimp at h2
      exact eq_sub_of_add_eq h2

private theorem pderiv_eq_zero_of_lt_conformalWeight [AddCommGroup W] (wt : ι → W) (v : Var ι)
    {d : ℕ} {w : W} {p : Fock R ι} (hp : p ∈ biGradedSubmodule R wt (d, w))
    (hd : d < conformalWeight v) :
    pderiv v p = 0 := by
  rw [p.as_sum, map_sum]
  refine sum_eq_zero fun e he ↦ ?_
  have hwt : Finsupp.weight conformalWeight e = d := by
    have := congrArg Prod.fst (hp (Finsupp.mem_support_iff.mp he))
    simpa using this
  rw [pderiv_monomial]
  have hv : e v = 0 := by
    by_contra hne
    have hle : Finsupp.single v 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hne)
    have hmono : conformalWeight v ≤ Finsupp.weight conformalWeight e := by
      have hsub := congrArg (Finsupp.weight conformalWeight) (tsub_add_cancel_of_le hle)
      rw [map_add, Finsupp.weight_single, one_smul] at hsub
      omega
    omega
  simp [hv]

/-- The mode `β_{i, n}` shifts `(d, w)` to `(d - n, w + wt i)` whenever `n ≤ d`. -/
theorem betaMode_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) (i : ι) (n : ℤ)
    {d : ℕ} {w : W} {p : Fock R ι} (hp : p ∈ biGradedSubmodule R wt (d, w)) (hn : n ≤ d) :
    betaMode R i n p ∈ biGradedSubmodule R wt (((d : ℤ) - n).toNat, w + wt i) := by
  rcases le_or_gt 0 n with h0 | h0
  · rw [betaMode_of_nonneg R i h0, Derivation.coeFn_coe]
    have h := pderiv_mem_biGradedSubmodule R wt (Var.gamma i n.toNat) hp (by simp; omega)
    rw [conformalWeight_gamma, rootWeight_gamma, sub_neg_eq_add,
      show d - n.toNat = ((d : ℤ) - n).toNat by omega] at h
    exact h
  · rw [betaMode_of_neg R i h0, LinearMap.mulLeft_apply]
    have h := (X_beta_mem_biGradedSubmodule R wt i (-n - 1).toNat).mul hp
    rw [Prod.mk_add_mk, show (-n - 1).toNat + 1 + d = ((d : ℤ) - n).toNat by omega,
      add_comm (wt i) w] at h
    exact h

/-- Modes `β_{i, n}` with `n > d` annihilate the `(d, w)` weight space. -/
theorem betaMode_eq_zero_of_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) (i : ι) (n : ℤ)
    {d : ℕ} {w : W} {p : Fock R ι} (hp : p ∈ biGradedSubmodule R wt (d, w)) (hn : (d : ℤ) < n) :
    betaMode R i n p = 0 := by
  rw [betaMode_of_nonneg R i (by omega), Derivation.coeFn_coe]
  exact pderiv_eq_zero_of_lt_conformalWeight R wt (Var.gamma i n.toNat) hp (by simp; omega)

/-- The mode `γ_{i, n}` shifts `(d, w)` to `(d - n, w - wt i)` whenever `n ≤ d`. -/
theorem gammaMode_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) (i : ι) (n : ℤ)
    {d : ℕ} {w : W} {p : Fock R ι} (hp : p ∈ biGradedSubmodule R wt (d, w)) (hn : n ≤ d) :
    gammaMode R i n p ∈ biGradedSubmodule R wt (((d : ℤ) - n).toNat, w - wt i) := by
  rcases le_or_gt n 0 with h0 | h0
  · rw [gammaMode_of_nonpos R i h0, LinearMap.mulLeft_apply]
    have h := (X_gamma_mem_biGradedSubmodule R wt i (-n).toNat).mul hp
    rw [Prod.mk_add_mk, show (-n).toNat + d = ((d : ℤ) - n).toNat by omega,
      add_comm (-wt i) w, ← sub_eq_add_neg] at h
    exact h
  · rw [gammaMode_of_pos R i h0, LinearMap.neg_apply, Derivation.coeFn_coe]
    have h := (pderiv_mem_biGradedSubmodule R wt (Var.beta i (n - 1).toNat) hp (by simp; omega)).neg
    rw [conformalWeight_beta, rootWeight_beta,
      show d - ((n - 1).toNat + 1) = ((d : ℤ) - n).toNat by omega] at h
    exact h

/-- Modes `γ_{i, n}` with `n > d` annihilate the `(d, w)` weight space. -/
theorem gammaMode_eq_zero_of_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) (i : ι) (n : ℤ)
    {d : ℕ} {w : W} {p : Fock R ι} (hp : p ∈ biGradedSubmodule R wt (d, w)) (hn : (d : ℤ) < n) :
    gammaMode R i n p = 0 := by
  rw [gammaMode_of_pos R i (by omega), LinearMap.neg_apply, Derivation.coeFn_coe, neg_eq_zero]
  exact pderiv_eq_zero_of_lt_conformalWeight R wt (Var.beta i (n - 1).toNat) hp (by simp; omega)

private theorem translation_X_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) (v : Var ι) :
    translation R ι (X v) ∈
      biGradedSubmodule R wt (conformalWeight v + 1, rootWeight wt v) := by
  cases v with
  | beta i k =>
    rw [translation_X_beta]
    exact Submodule.smul_mem _ _ (X_beta_mem_biGradedSubmodule R wt i (k + 1))
  | gamma i k =>
    rw [translation_X_gamma]
    exact Submodule.smul_mem _ _ (X_gamma_mem_biGradedSubmodule R wt i (k + 1))

private theorem translation_prod_pow_mem [AddCommGroup W] (wt : ι → W) (e : Var ι →₀ ℕ) :
    translation R ι (e.prod fun v n ↦ (X v : Fock R ι) ^ n) ∈
      biGradedSubmodule R wt
        ((Finsupp.weight (biWeight wt) e).1 + 1, (Finsupp.weight (biWeight wt) e).2) := by
  induction e using Finsupp.induction with
  | zero => simp
  | single_add v n f _ hn ih =>
    rw [Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
      Finsupp.prod_single_index (h := fun v n ↦ (X v : Fock R ι) ^ n) (pow_zero _),
      Derivation.leibniz, Derivation.leibniz_pow]
    simp only [smul_eq_mul]
    have hP : (f.prod fun u m ↦ (X u : Fock R ι) ^ m) ∈
        biGradedSubmodule R wt (Finsupp.weight (biWeight wt) f) := by
      have hmon := isWeightedHomogeneous_monomial (biWeight wt) f (1 : R) rfl
      simpa [monomial_eq] using hmon
    have hXn : (X v : Fock R ι) ^ n ∈ biGradedSubmodule R wt (n • biWeight wt v) := by
      simpa using (isWeightedHomogeneous_X R (biWeight wt) v).pow n
    have hXn1 : (X v : Fock R ι) ^ (n - 1) ∈ biGradedSubmodule R wt ((n - 1) • biWeight wt v) := by
      simpa using (isWeightedHomogeneous_X R (biWeight wt) v).pow (n - 1)
    have h1 : (X v : Fock R ι) ^ n * translation R ι (f.prod fun u m ↦ (X u : Fock R ι) ^ m) ∈
        biGradedSubmodule R wt
          ((Finsupp.weight (biWeight wt) (Finsupp.single v n + f)).1 + 1,
            (Finsupp.weight (biWeight wt) (Finsupp.single v n + f)).2) := by
      have h : (X v : Fock R ι) ^ n * translation R ι (f.prod fun u m ↦ (X u : Fock R ι) ^ m) ∈
          biGradedSubmodule R wt
            (n • biWeight wt v +
              ((Finsupp.weight (biWeight wt) f).1 + 1, (Finsupp.weight (biWeight wt) f).2)) :=
        hXn.mul ih
      convert h using 2
      refine Prod.ext ?_ ?_ <;> simp [map_add, Finsupp.weight_single, Nat.add_assoc]
    have h2 : (f.prod fun u m ↦ (X u : Fock R ι) ^ m) *
        (n • ((X v : Fock R ι) ^ (n - 1) * translation R ι (X v))) ∈
        biGradedSubmodule R wt
          ((Finsupp.weight (biWeight wt) (Finsupp.single v n + f)).1 + 1,
            (Finsupp.weight (biWeight wt) (Finsupp.single v n + f)).2) := by
      have hmul : (X v : Fock R ι) ^ (n - 1) * translation R ι (X v) ∈
          biGradedSubmodule R wt
            ((n - 1) • biWeight wt v + (conformalWeight v + 1, rootWeight wt v)) :=
        hXn1.mul (translation_X_mem_biGradedSubmodule R wt v)
      have h : (f.prod fun u m ↦ (X u : Fock R ι) ^ m) *
          (n • ((X v : Fock R ι) ^ (n - 1) * translation R ι (X v))) ∈
          biGradedSubmodule R wt
            (Finsupp.weight (biWeight wt) f +
              ((n - 1) • biWeight wt v + (conformalWeight v + 1, rootWeight wt v))) :=
        hP.mul (nsmul_mem hmul n)
      convert h using 2
      have hdeg : (n - 1) * conformalWeight v + conformalWeight v = n * conformalWeight v := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
      have hwt : (n - 1) • rootWeight wt v + rootWeight wt v = n • rootWeight wt v := by
        rw [← succ_nsmul, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
      refine Prod.ext ?_ ?_
      · simp only [map_add, Finsupp.weight_single, Prod.fst_add, Prod.smul_fst, fst_biWeight,
          smul_eq_mul, fst_weight_biWeight]
        omega
      · simp [map_add, Finsupp.weight_single, hwt, add_comm]
    exact Submodule.add_mem _ h1 h2

/-- Translation `T` raises conformal degree by `1` and preserves root weight. -/
theorem translation_mem_biGradedSubmodule [AddCommGroup W] (wt : ι → W) {d : ℕ} {w : W}
    {p : Fock R ι} (hp : p ∈ biGradedSubmodule R wt (d, w)) :
    translation R ι p ∈ biGradedSubmodule R wt (d + 1, w) := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun e he ↦ ?_
  have hwt : Finsupp.weight (biWeight wt) e = (d, w) := hp (Finsupp.mem_support_iff.mp he)
  rw [monomial_eq, ← MvPolynomial.algebraMap_eq, Derivation.leibniz, Derivation.map_algebraMap,
    smul_zero, add_zero, smul_eq_mul, MvPolynomial.algebraMap_eq, C_mul']
  have h := translation_prod_pow_mem R wt e
  rw [hwt] at h
  exact Submodule.smul_mem _ (p.coeff e) h

private theorem mem_degreeSubmodule_iff_biGraded_zero {d : ℕ} {p : Fock R ι} :
    p ∈ degreeSubmodule R ι d ↔ p ∈ biGradedSubmodule R (fun _ : ι ↦ (0 : ℤ)) (d, 0) := by
  have hroot : ∀ e : Var ι →₀ ℕ, Finsupp.weight (rootWeight fun _ : ι ↦ (0 : ℤ)) e = 0 := by
    intro e
    induction e using Finsupp.induction with
    | zero => simp
    | single_add v _ _ _ _ ih => cases v <;> simp [map_add, Finsupp.weight_single, ih]
  constructor
  · intro hp e he
    ext
    · simpa using hp he
    · simpa using hroot e
  · intro hp
    exact biGradedSubmodule_le_degreeSubmodule R (fun _ : ι ↦ (0 : ℤ)) d 0 hp

/-- `β_{i, n}` maps conformal degree `d` into conformal degree `d - n` when `n ≤ d`. -/
theorem betaMode_mem_degreeSubmodule (i : ι) (n : ℤ) {d : ℕ} {p : Fock R ι}
    (hp : p ∈ degreeSubmodule R ι d) (hn : n ≤ d) :
    betaMode R i n p ∈ degreeSubmodule R ι ((d : ℤ) - n).toNat := by
  have h := betaMode_mem_biGradedSubmodule R (fun _ : ι ↦ (0 : ℤ)) i n
    ((mem_degreeSubmodule_iff_biGraded_zero R).mp hp) hn
  exact biGradedSubmodule_le_degreeSubmodule R _ _ _ h

/-- `γ_{i, n}` maps conformal degree `d` into conformal degree `d - n` when `n ≤ d`. -/
theorem gammaMode_mem_degreeSubmodule (i : ι) (n : ℤ) {d : ℕ} {p : Fock R ι}
    (hp : p ∈ degreeSubmodule R ι d) (hn : n ≤ d) :
    gammaMode R i n p ∈ degreeSubmodule R ι ((d : ℤ) - n).toNat := by
  have h := gammaMode_mem_biGradedSubmodule R (fun _ : ι ↦ (0 : ℤ)) i n
    ((mem_degreeSubmodule_iff_biGraded_zero R).mp hp) hn
  exact biGradedSubmodule_le_degreeSubmodule R _ _ _ h

/-- Translation `T` maps conformal degree `d` into conformal degree `d + 1`. -/
theorem translation_mem_degreeSubmodule {d : ℕ} {p : Fock R ι} (hp : p ∈ degreeSubmodule R ι d) :
    translation R ι p ∈ degreeSubmodule R ι (d + 1) := by
  have h := translation_mem_biGradedSubmodule R (fun _ : ι ↦ (0 : ℤ))
    ((mem_degreeSubmodule_iff_biGraded_zero R).mp hp)
  exact biGradedSubmodule_le_degreeSubmodule R _ _ _ h

/-! ### Degree-zero polynomial subalgebra -/

/-- The degree-zero subalgebra of `Fock R ι`, generated by the gamma zero modes `γ_{i, 0}`. -/
def degreeZeroSubalgebra (ι : Type*) : Subalgebra R (Fock R ι) where
  carrier := degreeSubmodule R ι 0
  mul_mem' hp hq := by simpa using hp.mul hq
  one_mem' := one_mem_degreeSubmodule R
  add_mem' hp hq := (degreeSubmodule R ι 0).add_mem hp hq
  zero_mem' := (degreeSubmodule R ι 0).zero_mem
  algebraMap_mem' r := by
    simpa [MvPolynomial.algebraMap_eq] using isWeightedHomogeneous_C (conformalWeight (ι := ι)) r

@[simp]
theorem mem_degreeZeroSubalgebra (p : Fock R ι) :
    p ∈ degreeZeroSubalgebra R ι ↔ p ∈ degreeSubmodule R ι 0 := Iff.rfl

@[simp]
theorem toSubmodule_degreeZeroSubalgebra :
    (degreeZeroSubalgebra R ι).toSubmodule = degreeSubmodule R ι 0 := (rfl)

/-- Algebra embedding `MvPolynomial ι R →ₐ[R] Fock R ι` sending `X i` to `γ_{i, 0}`. -/
def gammaZeroEmbed (ι : Type*) : MvPolynomial ι R →ₐ[R] Fock R ι :=
  rename fun i ↦ Var.gamma i 0

@[simp]
theorem gammaZeroEmbed_X (i : ι) : gammaZeroEmbed R ι (X i) = X (Var.gamma i 0) :=
  rename_X _ i

theorem gammaZeroEmbed_injective : Function.Injective (gammaZeroEmbed R ι) :=
  rename_injective _ fun _ _ h ↦ by injection h

/-- A polynomial in `Fock R ι` has conformal degree `0` if and only if it lies in the image of
`gammaZeroEmbed R ι` (i.e. is a polynomial purely in the zero modes `γ_{i, 0}`). -/
theorem mem_degreeSubmodule_zero_iff (p : Fock R ι) :
    p ∈ degreeSubmodule R ι 0 ↔ p ∈ (gammaZeroEmbed R ι).range := by
  constructor
  · intro hp
    rw [p.as_sum]
    refine Subalgebra.sum_mem _ fun e he ↦ ?_
    have hwt : Finsupp.weight conformalWeight e = 0 := hp (Finsupp.mem_support_iff.mp he)
    have hsupp : ∀ v ∈ e.support, ∃ i : ι, v = Var.gamma i 0 := by
      intro v hv
      have h0 : e v * conformalWeight v = 0 := by
        rw [Finsupp.weight_apply, Finsupp.sum] at hwt
        exact (Finset.sum_eq_zero_iff.mp hwt) v hv
      have hcw : conformalWeight v = 0 :=
        (mul_eq_zero.mp h0).resolve_left (Finsupp.mem_support_iff.mp hv)
      cases v with
      | beta _ k => simp at hcw
      | gamma i k =>
        simp only [conformalWeight_gamma] at hcw
        exact ⟨i, by rw [hcw]⟩
    have hinj : Function.Injective (fun i : ι ↦ Var.gamma i 0) := fun _ _ h ↦ by injection h
    rw [AlgHom.mem_range]
    refine ⟨monomial (e.comapDomain (fun i ↦ Var.gamma i 0) hinj.injOn) (p.coeff e), ?_⟩
    rw [gammaZeroEmbed, rename_monomial]
    refine congrArg (fun d ↦ monomial d (p.coeff e))
      (Finsupp.mapDomain_comapDomain _ hinj e fun v hv ↦ ?_)
    obtain ⟨i, rfl⟩ := hsupp v hv
    exact ⟨i, rfl⟩
  · intro hp
    obtain ⟨q, rfl⟩ := (gammaZeroEmbed R ι).mem_range.mp hp
    clear hp
    induction q using MvPolynomial.induction_on with
    | C r =>
      simpa [gammaZeroEmbed, rename_C] using
        isWeightedHomogeneous_C (conformalWeight (ι := ι)) r
    | add p₁ p₂ h₁ h₂ =>
      rw [map_add]
      exact (degreeSubmodule R ι 0).add_mem h₁ h₂
    | mul_X p₁ i hp₁ =>
      rw [map_mul, gammaZeroEmbed_X]
      simpa using hp₁.mul (X_gamma_mem_degreeSubmodule R i 0)

/-- **Degree-zero algebra isomorphism:** the conformal-degree `0` subalgebra of `Fock R ι` is
isomorphic as an `R`-algebra to `MvPolynomial ι R` via `X i ↦ γ_{i, 0}`. -/
def degreeZeroAlgEquiv (ι : Type*) : MvPolynomial ι R ≃ₐ[R] degreeZeroSubalgebra R ι :=
  (AlgEquiv.ofInjective (gammaZeroEmbed R ι) (gammaZeroEmbed_injective R)).trans
    (Subalgebra.equivOfEq _ _ (SetLike.ext fun p ↦ (mem_degreeSubmodule_zero_iff R p).symm))

@[simp]
theorem coe_degreeZeroAlgEquiv (q : MvPolynomial ι R) :
    (degreeZeroAlgEquiv R ι q : Fock R ι) = gammaZeroEmbed R ι q := (rfl)

theorem coe_degreeZeroAlgEquiv_X (i : ι) :
    (degreeZeroAlgEquiv R ι (X i) : Fock R ι) = X (Var.gamma i 0) :=
  gammaZeroEmbed_X R i

/-- The conformal-degree `0` submodule is not finitely generated whenever `R` is nontrivial and
`ι` is nonempty (because the powers of `γ_{i, 0}` are linearly independent). -/
theorem not_module_finite_degreeSubmodule_zero [Nontrivial R] [Nonempty ι] :
    ¬ Module.Finite R (degreeSubmodule R ι 0) := by
  intro hfin
  have hfin0 : Module.Finite R (degreeZeroSubalgebra R ι) := hfin
  have hfin' : Module.Finite R (MvPolynomial ι R) :=
    Module.Finite.equiv (degreeZeroAlgEquiv R ι).toLinearEquiv.symm
  have hfin_idx : Finite (ι →₀ ℕ) := Module.Finite.finite_basis (basisMonomials ι R)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have : Finite ℕ := Finite.of_injective (Finsupp.single i₀) (Finsupp.single_injective i₀)
  exact not_finite ℕ

/-! ### Bigraded finiteness and exact rank -/

/-- Exact rank of any bigraded weight space `(d, w)` as the cardinality of the exponent fiber. -/
theorem finrank_biGradedSubmodule [Nontrivial R] [AddCommGroup W] (wt : ι → W) (d : ℕ) (w : W) :
    Module.finrank R (biGradedSubmodule R wt (d, w)) =
      Nat.card {e : Var ι →₀ ℕ // Finsupp.weight (biWeight wt) e = (d, w)} := by
  let b := (basisRestrictSupport R {e : Var ι →₀ ℕ | Finsupp.weight (biWeight wt) e = (d, w)}).map
    (LinearEquiv.ofEq _ _
      (weightedHomogeneousSubmodule_eq_finsupp_supported R (biWeight wt) (d, w)).symm)
  exact Module.finrank_eq_nat_card_basis b

end Submodules

private theorem gamma_zero_exponent_le [Fintype ι] [AddCommGroup W] (wt : ι → W)
    (ht : W →+ ℤ) (hht : ∀ i : ι, 0 < ht (wt i)) {e : Var ι →₀ ℕ} {d : ℕ} {w : W}
    (he : Finsupp.weight (biWeight wt) e = (d, w)) (i : ι) :
    e (Var.gamma i 0) ≤
      (d * ((univ.sup fun j : ι ↦ (ht (wt j)).natAbs : ℕ) : ℤ) - ht w).toNat := by
  classical
  set M : ℕ := univ.sup fun j : ι ↦ (ht (wt j)).natAbs
  have hd : Finsupp.weight conformalWeight e = d := by simpa using congrArg Prod.fst he
  have hw : Finsupp.weight (rootWeight wt) e = w := by simpa using congrArg Prod.snd he
  have hht_eq : ht w = ∑ u ∈ e.support, (e u : ℤ) * ht (rootWeight wt u) := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [map_nsmul, nsmul_eq_mul]
  have hterm : ∀ u ∈ e.support, (e u : ℤ) * ht (rootWeight wt u) ≤
      (e u * conformalWeight u : ℕ) * (M : ℤ) - if u = Var.gamma i 0 then (e u : ℤ) else 0 := by
    intro u _
    cases u with
    | beta j k =>
      have hMj : ht (wt j) ≤ (M : ℤ) := by
        have hle : (ht (wt j)).natAbs ≤ M :=
          le_sup (f := fun j ↦ (ht (wt j)).natAbs) (mem_univ j)
        have hpos := hht j
        omega
      have h1 : (e (Var.beta j k) : ℤ) * ht (wt j) ≤ (e (Var.beta j k) : ℤ) * (M : ℤ) :=
        mul_le_mul_of_nonneg_left hMj (Nat.cast_nonneg _)
      have h2 : (e (Var.beta j k) : ℤ) * (M : ℤ) ≤
          ((e (Var.beta j k) * (k + 1) : ℕ) : ℤ) * (M : ℤ) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_mul_of_pos_right _ (Nat.succ_pos k)) (Nat.cast_nonneg _)
      simpa using le_trans h1 h2
    | gamma j k =>
      have hpos := hht j
      split_ifs with hEq
      · injection hEq with hji hk0
        subst hji hk0
        have : (e (Var.gamma j 0) : ℤ) * 1 ≤ (e (Var.gamma j 0) : ℤ) * ht (wt j) :=
          mul_le_mul_of_nonneg_left (by omega) (Nat.cast_nonneg _)
        simpa using (by linarith :
          (e (Var.gamma j 0) : ℤ) * (-ht (wt j)) ≤ -(e (Var.gamma j 0) : ℤ))
      · have hneg : (e (Var.gamma j k) : ℤ) * (-ht (wt j)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by omega)
        have hnonneg : (0 : ℤ) ≤ ((e (Var.gamma j k) * k : ℕ) : ℤ) * (M : ℤ) :=
          mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        simpa using le_trans hneg hnonneg
  have hsum_le : ht w ≤ (d : ℤ) * (M : ℤ) - (e (Var.gamma i 0) : ℤ) := by
    calc
      ht w = ∑ u ∈ e.support, (e u : ℤ) * ht (rootWeight wt u) := hht_eq
      _ ≤ ∑ u ∈ e.support, (((e u * conformalWeight u : ℕ) : ℤ) * (M : ℤ) -
          if u = Var.gamma i 0 then (e u : ℤ) else 0) := sum_le_sum hterm
      _ = (∑ u ∈ e.support, ((e u * conformalWeight u : ℕ) : ℤ)) * (M : ℤ) -
          ∑ u ∈ e.support, (if u = Var.gamma i 0 then (e u : ℤ) else 0) := by
            rw [sum_sub_distrib, ← sum_mul]
      _ = (d : ℤ) * (M : ℤ) - (e (Var.gamma i 0) : ℤ) := by
            have hdZ : (∑ u ∈ e.support, ((e u * conformalWeight u : ℕ) : ℤ)) = (d : ℤ) := by
              exact_mod_cast hd
            have hite : ∑ u ∈ e.support, (if u = Var.gamma i 0 then (e u : ℤ) else 0) =
                (e (Var.gamma i 0) : ℤ) := by
              by_cases hmem : Var.gamma i 0 ∈ e.support
              · simp [hmem]
              · simp [hmem, Finsupp.notMem_support_iff.mp hmem]
            rw [hdZ, hite]
  omega

/-- For finite `ι` and any root-weight map `wt : ι → W` admitting a positive height homomorphism
`ht : W →+ ℤ`, every bigraded exponent fiber `{e | biWeight e = (d, w)}` is finite. -/
theorem finite_biWeight_fiber [Finite ι] [AddCommGroup W] (wt : ι → W)
    (ht : W →+ ℤ) (hht : ∀ i : ι, 0 < ht (wt i)) (d : ℕ) (w : W) :
    {e : Var ι →₀ ℕ | Finsupp.weight (biWeight wt) e = (d, w)}.Finite := by
  classical
  cases nonempty_fintype ι
  let S : Finset (Var ι) :=
    (univ ×ˢ range (d + 1)).image (fun p : ι × ℕ ↦ Var.beta p.1 p.2) ∪
    (univ ×ˢ range (d + 1)).image (fun p : ι × ℕ ↦ Var.gamma p.1 p.2)
  let B : ℕ := max d (d * ((univ.sup fun i : ι ↦ (ht (wt i)).natAbs : ℕ) : ℤ) - ht w).toNat
  have hbound : ∀ e : Var ι →₀ ℕ, Finsupp.weight (biWeight wt) e = (d, w) →
      (∀ v, v ∉ S → e v = 0) ∧ (∀ v, e v ≤ B) := by
    intro e he
    have hd : Finsupp.weight conformalWeight e = d := by simpa using congrArg Prod.fst he
    have hdeg_le : ∀ v : Var ι, e v * conformalWeight v ≤ d := fun v ↦ by
      by_cases hv : v ∈ e.support
      · rw [← hd, Finsupp.weight_apply, Finsupp.sum]
        exact single_le_sum (f := fun u ↦ e u * conformalWeight u) (fun _ _ ↦ Nat.zero_le _) hv
      · simp [Finsupp.notMem_support_iff.mp hv]
    refine ⟨fun v hv ↦ ?_, fun v ↦ ?_⟩
    · by_contra hne
      have hcw : conformalWeight v ≤ d :=
        le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)) (hdeg_le v)
      apply hv
      cases v with
      | beta i k =>
        exact mem_union_left _ (mem_image.mpr ⟨(i, k), mem_product.mpr ⟨mem_univ _,
          mem_range.mpr (by simp at hcw; omega)⟩, rfl⟩)
      | gamma i k =>
        exact mem_union_right _ (mem_image.mpr ⟨(i, k), mem_product.mpr ⟨mem_univ _,
          mem_range.mpr (by simp at hcw; omega)⟩, rfl⟩)
    · cases v with
      | beta i k =>
        have := hdeg_le (Var.beta i k)
        simp only [conformalWeight_beta] at this
        exact le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos k))
          (le_trans this (le_max_left _ _))
      | gamma i k =>
        cases k with
        | succ k =>
          have := hdeg_le (Var.gamma i (k + 1))
          simp only [conformalWeight_gamma] at this
          exact le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos k))
            (le_trans this (le_max_left _ _))
        | zero => exact le_trans (gamma_zero_exponent_le wt ht hht he i) (le_max_right _ _)
  let φ : {e : Var ι →₀ ℕ // Finsupp.weight (biWeight wt) e = (d, w)} → (S → Fin (B + 1)) :=
    fun e v ↦ ⟨e.1 v.1, Nat.lt_succ_of_le ((hbound e.1 e.2).2 v.1)⟩
  have hφ : Function.Injective φ := fun e₁ e₂ h ↦ Subtype.ext <| Finsupp.ext fun v ↦ by
    by_cases hv : v ∈ S
    · exact congrArg Fin.val (congrFun h ⟨v, hv⟩)
    · rw [(hbound e₁.1 e₁.2).1 v hv, (hbound e₂.1 e₂.2).1 v hv]
  exact Set.finite_coe_iff.mp (Finite.of_injective φ hφ)

/-- **Finiteness of bigraded weight spaces:** for finite `ι` and any root-weight map `wt : ι → W`
admitting a positive height homomorphism `ht : W →+ ℤ`, every bigraded weight space `(d, w)` is
finitely generated over `R`. -/
theorem module_finite_biGradedSubmodule (R : Type*) [CommRing R] [Finite ι] [AddCommGroup W]
    (wt : ι → W) (ht : W →+ ℤ) (hht : ∀ i : ι, 0 < ht (wt i)) (d : ℕ) (w : W) :
    Module.Finite R (biGradedSubmodule R wt (d, w)) := by
  rw [biGradedSubmodule, weightedHomogeneousSubmodule_eq_finsupp_supported]
  have : Finite {e : Var ι →₀ ℕ // Finsupp.weight (biWeight wt) e = (d, w)} :=
    (finite_biWeight_fiber wt ht hht d w).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport R {e : Var ι →₀ ℕ | Finsupp.weight (biWeight wt) e = (d, w)})


end TauCeti.BetaGamma
