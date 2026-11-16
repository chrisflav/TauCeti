/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.BetaGamma.Basic
public import TauCeti.Algebra.Vertex.Derivative
public import TauCeti.Algebra.Vertex.NormalOrder
public import TauCeti.Algebra.Vertex.ResidueProduct

/-!
# Beta-gamma vertex fields, locality, OPEs, and normal ordering

The Weyl modes on `TauCeti.BetaGamma.Fock R ι` assemble into native `VertexOperator` fields

`β_i(z) = ∑ₙ β_{i, n} z^{-n - 1}`   and   `γ_i(z) = ∑ₙ γ_{i, n} z^{-n}`

(`TauCeti.BetaGamma.betaField`, `TauCeti.BetaGamma.gammaField`). In normalized coefficient indexing
`A(z) = ∑ₙ A[[n]] z^{-n - 1}`, the modes are

`(betaField R i)[[n]] = betaMode R i n`   and   `(gammaField R i)[[n]] = gammaMode R i (n + 1)`,

so the state-mode index of `γ_{i, n}` is `n - 1` rather than `n`. Lower truncation is uniform in
`i` (`TauCeti.BetaGamma.exists_forall_betaMode_apply_eq_zero`,
`TauCeti.BetaGamma.exists_forall_gammaMode_apply_eq_zero`), because each polynomial in `Fock R ι`
involves only finitely many creation variables.

The generating fields satisfy:

* **Vacuum creation:** nonnegative normalized modes of `betaField R i` and `gammaField R i` kill
  `1`, while their `-1`-modes create `β_{i, -1}` and `γ_{i, 0}`.
* **Mutual locality:** `β_i` with `β_j` and `γ_i` with `γ_j` are mutually local of order `0`, while
  `β_i` with `γ_j` (and `γ_i` with `β_j`) are mutually local of order `1`.
* **Ordered singular OPEs:** all nonnegative residue products of `β_i` with `β_j` and `γ_i` with
  `γ_j` vanish, while
  `nonnegResidueProduct 0 (betaField R i) (gammaField R j) = δ_{i, j} · vacuumField` and
  `nonnegResidueProduct 0 (gammaField R i) (betaField R j) = -δ_{i, j} · vacuumField`,
  with all products of order `≥ 1` vanishing. That is,
  `β_i(z) γ_j(w) ∼ δ_{i, j} / (z - w)` and `γ_i(z) β_j(w) ∼ -δ_{i, j} / (z - w)`.
* **Translation covariance:** `[T, A[[n]]] = (∂ A)[[n]]` for every generating field and every
  derivative `∂ᵏ β_i`, `∂ᵏ γ_i`.
* **Normal-ordering and derivative identities on monomials:** the iterated derivatives
  `varField R (.beta i k) = ∂ᵏ β_i` and `varField R (.gamma i k) = ∂ᵏ γ_i` have `-1`-mode
  `k! · mulLeft (X v)` and kill `1` in nonnegative modes. Their iterated normal-ordered products
  `monomialField R l` kill `1` in nonnegative modes and evaluate at mode `-1` on `1` to the
  factorial-scaled monomial `(∏ v ∈ l, v.order!) • ∏ v ∈ l, X v` (recovering exact monomials over
  any `ℚ`-algebra). In addition, `:β_i β_j: = :β_j β_i:`, `:γ_i γ_j: = :γ_j γ_i:`, and
  `:β_i γ_j: = :γ_j β_i:`.

Together with `TauCeti.BetaGamma.Basic`, these provide all field-theoretic inputs for vertex
algebra reconstruction on `Fock R ι`.

## Main definitions

* `TauCeti.BetaGamma.betaField`, `TauCeti.BetaGamma.gammaField`: the generating beta-gamma fields.
* `TauCeti.BetaGamma.vacuumField`: the identity field `|0⟩(z) = id` on `Fock R ι`.
* `TauCeti.BetaGamma.varField`: the `k`-th derivative field `∂ᵏ β_i` or `∂ᵏ γ_i` attached to a
  creation variable.
* `TauCeti.BetaGamma.monomialField`: the iterated normal-ordered product of `varField` along a
  list of creation variables.

## Main results

* `TauCeti.BetaGamma.isLocalOfOrder_betaField_betaField`,
  `TauCeti.BetaGamma.isLocalOfOrder_gammaField_gammaField`,
  `TauCeti.BetaGamma.isLocalOfOrder_betaField_gammaField`,
  `TauCeti.BetaGamma.isLocalOfOrder_gammaField_betaField`: mutual locality of generating fields.
* `TauCeti.BetaGamma.nonnegResidueProduct_betaField_betaField`,
  `TauCeti.BetaGamma.nonnegResidueProduct_gammaField_gammaField`,
  `TauCeti.BetaGamma.nonnegResidueProduct_betaField_gammaField_zero`,
  `TauCeti.BetaGamma.nonnegResidueProduct_gammaField_betaField_zero`,
  `TauCeti.BetaGamma.nonnegResidueProduct_betaField_gammaField_eq_zero`,
  `TauCeti.BetaGamma.nonnegResidueProduct_gammaField_betaField_eq_zero`: ordered singular OPEs.
* `TauCeti.BetaGamma.lie_translation_ncoeff_betaField`,
  `TauCeti.BetaGamma.lie_translation_ncoeff_gammaField`,
  `TauCeti.BetaGamma.lie_translation_ncoeff_varField`: translation covariance of fields.
* `TauCeti.BetaGamma.ncoeff_neg_one_varField`,
  `TauCeti.BetaGamma.ncoeff_neg_one_monomialField_one`,
  `TauCeti.BetaGamma.ncoeff_neg_one_monomialField_one_rat`: normal-order and derivative monomial
  identities.
* `TauCeti.BetaGamma.normalOrder_betaField_comm`,
  `TauCeti.BetaGamma.normalOrder_gammaField_comm`,
  `TauCeti.BetaGamma.normalOrder_betaField_gammaField`: symmetry of normal ordering on the
  generating fields.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §5.3.3 and §5.4.1, pp. 139–143.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §11.3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset MvPolynomial VertexOperator

attribute [local instance] LieRing.ofAssociativeRing

namespace TauCeti.BetaGamma

variable (R : Type*) [CommRing R] {ι : Type*}

/-! ### Uniform lower truncation -/

/-- **Uniform lower truncation for beta modes:** every polynomial in `Fock R ι` is killed by all
sufficiently high modes `β_{i, n}`, uniformly in `i`. -/
theorem exists_forall_betaMode_apply_eq_zero (p : Fock R ι) :
    ∃ N : ℕ, ∀ i : ι, ∀ n : ℤ, (N : ℤ) ≤ n → betaMode R i n p = 0 := by
  classical
  refine ⟨p.vars.sup (fun v ↦ v.order + 1), fun i n hn ↦ ?_⟩
  rw [betaMode_of_nonneg R i (by omega), Derivation.coeFn_coe]
  refine pderiv_eq_zero_of_notMem_vars fun hmem ↦ ?_
  have hle : n.toNat + 1 ≤ p.vars.sup (fun v ↦ v.order + 1) := by
    simpa [Var.order_gamma] using le_sup (f := fun v : Var ι ↦ v.order + 1) hmem
  omega

/-- **Uniform lower truncation for gamma modes:** every polynomial in `Fock R ι` is killed by all
sufficiently high modes `γ_{i, n}`, uniformly in `i`. -/
theorem exists_forall_gammaMode_apply_eq_zero (p : Fock R ι) :
    ∃ N : ℕ, ∀ i : ι, ∀ n : ℤ, (N : ℤ) ≤ n → gammaMode R i n p = 0 := by
  classical
  refine ⟨p.vars.sup (fun v ↦ v.order + 1) + 1, fun i n hn ↦ ?_⟩
  rw [gammaMode_of_pos R i (by omega), LinearMap.neg_apply, Derivation.coeFn_coe, neg_eq_zero]
  refine pderiv_eq_zero_of_notMem_vars fun hmem ↦ ?_
  have hle : (n - 1).toNat + 1 ≤ p.vars.sup (fun v ↦ v.order + 1) := by
    simpa [Var.order_beta] using le_sup (f := fun v : Var ι ↦ v.order + 1) hmem
  omega

/-! ### Generating fields and the vacuum field -/

private theorem bddBelow_support_betaField (i : ι) (p : Fock R ι) :
    BddBelow (Function.support fun k : ℤ ↦ betaMode R i (-k - 1) p) := by
  obtain ⟨N, hN⟩ := exists_forall_betaMode_apply_eq_zero R p
  refine ⟨-(N : ℤ) - 1, fun k hk ↦ ?_⟩
  by_contra! h
  exact hk (hN i (-k - 1) (by omega))

private theorem bddBelow_support_gammaField (i : ι) (p : Fock R ι) :
    BddBelow (Function.support fun k : ℤ ↦ gammaMode R i (-k) p) := by
  obtain ⟨N, hN⟩ := exists_forall_gammaMode_apply_eq_zero R p
  refine ⟨-(N : ℤ), fun k hk ↦ ?_⟩
  by_contra! h
  exact hk (hN i (-k) (by omega))

private theorem bddBelow_support_vacuumField (p : Fock R ι) :
    BddBelow (Function.support fun k : ℤ ↦
      (if k = 0 then (1 : Module.End R (Fock R ι)) else 0) p) :=
  ⟨0, fun k hk ↦ by
    by_contra! h
    exact hk (by simp [h.ne])⟩

/-- The beta field `β_i(z) = ∑ₙ β_{i, n} z^{-n - 1}` as a native `VertexOperator` on `Fock R ι`.
Its normalized modes are `(betaField R i)[[n]] = betaMode R i n`. -/
def betaField (i : ι) : VertexOperator R (Fock R ι) :=
  VertexOperator.of_coeff (fun k ↦ betaMode R i (-k - 1)) (bddBelow_support_betaField R i)

/-- The gamma field `γ_i(z) = ∑ₙ γ_{i, n} z^{-n}` as a native `VertexOperator` on `Fock R ι`.
Its normalized modes are `(gammaField R i)[[n]] = gammaMode R i (n + 1)`, so the state-mode index
of `γ_{i, n}` is `n - 1`. -/
def gammaField (i : ι) : VertexOperator R (Fock R ι) :=
  VertexOperator.of_coeff (fun k ↦ gammaMode R i (-k)) (bddBelow_support_gammaField R i)

/-- The identity (vacuum) field `|0⟩(z) = id` on `Fock R ι`, with `[[n]] = δ_{n, -1} · id`. -/
def vacuumField (ι : Type*) : VertexOperator R (Fock R ι) :=
  VertexOperator.of_coeff (fun k ↦ if k = 0 then (1 : Module.End R (Fock R ι)) else 0)
    (bddBelow_support_vacuumField R)

/-- The normalized modes of `β_i(z)` are `(betaField R i)[[n]] = β_{i, n}`. -/
@[simp]
theorem ncoeff_betaField (i : ι) (n : ℤ) : (betaField R i)[[n]] = betaMode R i n := by
  simp [betaField]

/-- The unnormalized Laurent coefficient of `z^k` in `β_i(z)` is `β_{i, -k - 1}`. -/
theorem coeff_betaField (i : ι) (k : ℤ) :
    HVertexOperator.coeff (betaField R i) k = betaMode R i (-k - 1) := by
  simp [betaField]

/-- The normalized modes of `γ_i(z)` are `(gammaField R i)[[n]] = γ_{i, n + 1}`. -/
@[simp]
theorem ncoeff_gammaField (i : ι) (n : ℤ) : (gammaField R i)[[n]] = gammaMode R i (n + 1) := by
  have h : -(-n - 1) = n + 1 := by omega
  simp [gammaField, h]

/-- The unnormalized Laurent coefficient of `z^k` in `γ_i(z)` is `γ_{i, -k}`. -/
theorem coeff_gammaField (i : ι) (k : ℤ) :
    HVertexOperator.coeff (gammaField R i) k = gammaMode R i (-k) := by
  simp [gammaField]

/-- The normalized modes of the vacuum field are `δ_{n, -1} · id`. -/
@[simp]
theorem ncoeff_vacuumField (n : ℤ) :
    (vacuumField R ι)[[n]] = if n = -1 then 1 else 0 := by
  have h : (-n - 1 = 0) ↔ (n = -1) := by omega
  simp [vacuumField, h]

theorem ncoeff_neg_one_vacuumField : (vacuumField R ι)[[-1]] = 1 := by
  simp

theorem ncoeff_vacuumField_of_ne {n : ℤ} (hn : n ≠ -1) : (vacuumField R ι)[[n]] = 0 := by
  simp [hn]

/-! ### Vacuum creation and generation -/

/-- Nonnegative normalized modes of `β_i(z)` kill `1`. -/
theorem ncoeff_betaField_one_of_nonneg (i : ι) {n : ℤ} (hn : 0 ≤ n) :
    ((betaField R i)[[n]]) 1 = 0 := by
  simp [betaMode_one_of_nonneg R i hn]

/-- Nonnegative normalized modes of `γ_i(z)` kill `1`. -/
theorem ncoeff_gammaField_one_of_nonneg (i : ι) {n : ℤ} (hn : 0 ≤ n) :
    ((gammaField R i)[[n]]) 1 = 0 := by
  rw [ncoeff_gammaField]
  exact gammaMode_one_of_pos R i (by omega)

/-- The `-1`-mode of `β_i(z)` creates `β_{i, -1}` from `1`. -/
theorem ncoeff_neg_one_betaField_one (i : ι) :
    ((betaField R i)[[-1]]) 1 = X (Var.beta i 0) := by
  simp

/-- The `-1`-mode of `γ_i(z)` creates `γ_{i, 0}` from `1`. -/
theorem ncoeff_neg_one_gammaField_one (i : ι) :
    ((gammaField R i)[[-1]]) 1 = X (Var.gamma i 0) := by
  simp

/-- Any `R`-submodule of `Fock R ι` containing `1` and closed under the negative normalized modes
of `betaField R i` and `gammaField R i` is all of `Fock R ι`. -/
theorem eq_top_of_one_mem_of_field_ncoeff_closed {W : Submodule R (Fock R ι)}
    (h1 : (1 : Fock R ι) ∈ W)
    (hβ : ∀ i (k : ℕ), ∀ p ∈ W, ((betaField R i)[[-(k : ℤ) - 1]]) p ∈ W)
    (hγ : ∀ i (k : ℕ), ∀ p ∈ W, ((gammaField R i)[[-(k : ℤ) - 1]]) p ∈ W) :
    W = ⊤ := by
  refine eq_top_of_one_mem_of_creation_closed R h1
    (fun i k p hp ↦ by simpa using hβ i k p hp)
    (fun i k p hp ↦ ?_)
  have hk : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by omega
  simpa [ncoeff_gammaField, hk] using hγ i k p hp

/-! ### Field commutators, mutual locality, and ordered singular OPEs -/

theorem lie_ncoeff_betaField_betaField (i j : ι) (m n : ℤ) :
    ⁅(betaField R i)[[m]], (betaField R j)[[n]]⁆ = 0 := by
  simp

theorem lie_ncoeff_gammaField_gammaField (i j : ι) (m n : ℤ) :
    ⁅(gammaField R i)[[m]], (gammaField R j)[[n]]⁆ = 0 := by
  simp

/-- Normalized mode commutator of `β_i(z)` and `γ_j(w)`:
`[(betaField R i)[[m]], (gammaField R j)[[n]]] = δ_{i, j} δ_{m + n, -1} · id`. -/
theorem lie_ncoeff_betaField_gammaField [DecidableEq ι] (i j : ι) (m n : ℤ) :
    ⁅(betaField R i)[[m]], (gammaField R j)[[n]]⁆ = if i = j ∧ m + n = -1 then 1 else 0 := by
  rw [ncoeff_betaField, ncoeff_gammaField, lie_betaMode_gammaMode]
  have h : (m + (n + 1) = 0) ↔ (m + n = -1) := by omega
  simp [h]

/-- Reversed normalized mode commutator of `γ_i(z)` and `β_j(w)`:
`[(gammaField R i)[[m]], (betaField R j)[[n]]] = -δ_{i, j} δ_{m + n, -1} · id`. -/
theorem lie_ncoeff_gammaField_betaField [DecidableEq ι] (i j : ι) (m n : ℤ) :
    ⁅(gammaField R i)[[m]], (betaField R j)[[n]]⁆ = if i = j ∧ m + n = -1 then -1 else 0 := by
  rw [ncoeff_gammaField, ncoeff_betaField, lie_gammaMode_betaMode]
  have h : (m + 1 + n = 0) ↔ (m + n = -1) := by omega
  simp [h]

/-- Beta fields commute strictly: `(betaField R i)` and `(betaField R j)` are mutually local of
order `0`. -/
theorem isLocalOfOrder_betaField_betaField (i j : ι) :
    (betaField R i).IsLocalOfOrder (betaField R j) 0 := by
  rw [isLocalOfOrder_iff]
  intro m n
  have h : betaMode R i m * betaMode R j n - betaMode R j n * betaMode R i m = 0 :=
    lie_betaMode_betaMode R i j m n
  simp [h]

/-- Gamma fields commute strictly: `(gammaField R i)` and `(gammaField R j)` are mutually local of
order `0`. -/
theorem isLocalOfOrder_gammaField_gammaField (i j : ι) :
    (gammaField R i).IsLocalOfOrder (gammaField R j) 0 := by
  rw [isLocalOfOrder_iff]
  intro m n
  have h : gammaMode R i (m + 1) * gammaMode R j (n + 1) -
      gammaMode R j (n + 1) * gammaMode R i (m + 1) = 0 :=
    lie_gammaMode_gammaMode R i j (m + 1) (n + 1)
  simp [h]

/-- **Beta-gamma locality:** `(z - w) [β_i(z), γ_j(w)] = 0`, so `betaField R i` and
`gammaField R j` are mutually local of order `1`. -/
theorem isLocalOfOrder_betaField_gammaField (i j : ι) :
    (betaField R i).IsLocalOfOrder (gammaField R j) 1 := by
  classical
  rw [isLocalOfOrder_iff]
  intro m n
  have h₁ : betaMode R i m * gammaMode R j (n + 1 + 1) -
      gammaMode R j (n + 1 + 1) * betaMode R i m =
      if i = j ∧ m + (n + 1 + 1) = 0 then 1 else 0 :=
    lie_betaMode_gammaMode R i j m (n + 1 + 1)
  have h₂ : betaMode R i (m + 1) * gammaMode R j (n + 1) -
      gammaMode R j (n + 1) * betaMode R i (m + 1) =
      if i = j ∧ (m + 1) + (n + 1) = 0 then 1 else 0 :=
    lie_betaMode_gammaMode R i j (m + 1) (n + 1)
  have hsum : m + (n + 1 + 1) = (m + 1) + (n + 1) := by omega
  simp [Nat.sum_antidiagonal_succ, h₁, h₂, hsum]
  split_ifs <;> simp

/-- **Gamma-beta locality:** `(z - w) [γ_i(z), β_j(w)] = 0`, so `gammaField R i` and
`betaField R j` are mutually local of order `1`. -/
theorem isLocalOfOrder_gammaField_betaField (i j : ι) :
    (gammaField R i).IsLocalOfOrder (betaField R j) 1 :=
  (isLocalOfOrder_betaField_gammaField R j i).symm

/-- All nonnegative residue products of two beta fields vanish (regular OPE). -/
@[simp]
theorem nonnegResidueProduct_betaField_betaField (n : ℕ) (i j : ι) :
    nonnegResidueProduct n (betaField R i) (betaField R j) = 0 :=
  (isLocalOfOrder_betaField_betaField R i j).nonnegResidueProduct_eq_zero (Nat.zero_le n)

/-- All nonnegative residue products of two gamma fields vanish (regular OPE). -/
@[simp]
theorem nonnegResidueProduct_gammaField_gammaField (n : ℕ) (i j : ι) :
    nonnegResidueProduct n (gammaField R i) (gammaField R j) = 0 :=
  (isLocalOfOrder_gammaField_gammaField R i j).nonnegResidueProduct_eq_zero (Nat.zero_le n)

/-- **Ordered beta-gamma OPE:** `β_i(z) γ_j(w) ∼ δ_{i, j} / (z - w)`, so the zeroth residue
product is `δ_{i, j} · vacuumField`. -/
theorem nonnegResidueProduct_betaField_gammaField_zero [DecidableEq ι] (i j : ι) :
    nonnegResidueProduct 0 (betaField R i) (gammaField R j) =
      if i = j then vacuumField R ι else 0 := by
  apply ext_ncoeff
  intro m
  simp only [ncoeff_nonnegResidueProduct, Nat.antidiagonal_zero, sum_singleton,
    Nat.choose_zero_right, pow_zero, one_smul, Nat.cast_zero, add_zero]
  rw [← LieRing.of_associative_ring_bracket, lie_ncoeff_betaField_gammaField]
  split_ifs with h₁ h₂ <;> simp_all

/-- Coefficient form of the ordered beta-gamma simple pole `β_i(z) γ_j(w) ∼ δ_{i, j} / (z - w)`. -/
theorem ncoeff_nonnegResidueProduct_betaField_gammaField_zero [DecidableEq ι] (i j : ι) (m : ℤ) :
    (nonnegResidueProduct 0 (betaField R i) (gammaField R j))[[m]] =
      if i = j ∧ m = -1 then 1 else 0 := by
  rw [nonnegResidueProduct_betaField_gammaField_zero]
  split_ifs with h₁ h₂ <;> simp_all

/-- Diagonal beta-gamma simple pole: `Res_z [β_i(z), γ_i(w)] = id`. -/
@[simp]
theorem nonnegResidueProduct_betaField_gammaField_zero_self (i : ι) :
    nonnegResidueProduct 0 (betaField R i) (gammaField R i) = vacuumField R ι := by
  classical
  simp [nonnegResidueProduct_betaField_gammaField_zero]

/-- **Ordered gamma-beta OPE:** `γ_i(z) β_j(w) ∼ -δ_{i, j} / (z - w)`, so the zeroth residue
product is `-δ_{i, j} · vacuumField`. -/
theorem nonnegResidueProduct_gammaField_betaField_zero [DecidableEq ι] (i j : ι) :
    nonnegResidueProduct 0 (gammaField R i) (betaField R j) =
      if i = j then -vacuumField R ι else 0 := by
  apply ext_ncoeff
  intro m
  simp only [ncoeff_nonnegResidueProduct, Nat.antidiagonal_zero, sum_singleton,
    Nat.choose_zero_right, pow_zero, one_smul, Nat.cast_zero, add_zero]
  rw [← LieRing.of_associative_ring_bracket, lie_ncoeff_gammaField_betaField]
  split_ifs with h₁ h₂ <;> simp_all

/-- Coefficient form of the ordered gamma-beta simple pole
`γ_i(z) β_j(w) ∼ -δ_{i, j} / (z - w)`. -/
theorem ncoeff_nonnegResidueProduct_gammaField_betaField_zero [DecidableEq ι] (i j : ι) (m : ℤ) :
    (nonnegResidueProduct 0 (gammaField R i) (betaField R j))[[m]] =
      if i = j ∧ m = -1 then -1 else 0 := by
  rw [nonnegResidueProduct_gammaField_betaField_zero]
  split_ifs with h₁ h₂ <;> simp_all

/-- Diagonal gamma-beta simple pole: `Res_z [γ_i(z), β_i(w)] = -id`. -/
@[simp]
theorem nonnegResidueProduct_gammaField_betaField_zero_self (i : ι) :
    nonnegResidueProduct 0 (gammaField R i) (betaField R i) = -vacuumField R ι := by
  classical
  simp [nonnegResidueProduct_gammaField_betaField_zero]

/-- All higher beta-gamma residue products (`n ≥ 1`) vanish. -/
theorem nonnegResidueProduct_betaField_gammaField_eq_zero (i j : ι) {n : ℕ} (hn : 1 ≤ n) :
    nonnegResidueProduct n (betaField R i) (gammaField R j) = 0 :=
  (isLocalOfOrder_betaField_gammaField R i j).nonnegResidueProduct_eq_zero hn

/-- All higher gamma-beta residue products (`n ≥ 1`) vanish. -/
theorem nonnegResidueProduct_gammaField_betaField_eq_zero (i j : ι) {n : ℕ} (hn : 1 ≤ n) :
    nonnegResidueProduct n (gammaField R i) (betaField R j) = 0 :=
  (isLocalOfOrder_gammaField_betaField R i j).nonnegResidueProduct_eq_zero hn

/-! ### Translation covariance of fields -/

/-- Translation covariance of `β_i(z)`: `[T, β_i[[n]]] = (∂ β_i)[[n]]`. -/
theorem lie_translation_ncoeff_betaField (i : ι) (n : ℤ) :
    ⁅(translation R ι).toLinearMap, (betaField R i)[[n]]⁆ =
      (derivative (betaField R i))[[n]] := by
  rw [ncoeff_betaField, ncoeff_derivative, ncoeff_betaField, lie_translation_betaMode]

/-- Translation covariance of `γ_i(z)`: `[T, γ_i[[n]]] = (∂ γ_i)[[n]]`. -/
theorem lie_translation_ncoeff_gammaField (i : ι) (n : ℤ) :
    ⁅(translation R ι).toLinearMap, (gammaField R i)[[n]]⁆ =
      (derivative (gammaField R i))[[n]] := by
  rw [ncoeff_gammaField, ncoeff_derivative, ncoeff_gammaField, lie_translation_gammaMode]
  have h₁ : (n + 1 : ℤ) - 1 = n := by omega
  have h₂ : (n - 1 : ℤ) + 1 = n := by omega
  rw [h₁, h₂]

/-! ### Derivative fields and normal-ordered monomial identities -/

/-- The derivative field attached to a creation variable `v : Var ι`:
`varField R (.beta i k) = ∂ᵏ β_i` and `varField R (.gamma i k) = ∂ᵏ γ_i`. -/
def varField : Var ι → VertexOperator R (Fock R ι)
  | .beta i k => (derivative (R := R) (V := Fock R ι))^[k] (betaField R i)
  | .gamma i k => (derivative (R := R) (V := Fock R ι))^[k] (gammaField R i)

@[simp]
theorem varField_beta (i : ι) (k : ℕ) :
    varField R (.beta i k) = (derivative (R := R) (V := Fock R ι))^[k] (betaField R i) := (rfl)

@[simp]
theorem varField_gamma (i : ι) (k : ℕ) :
    varField R (.gamma i k) = (derivative (R := R) (V := Fock R ι))^[k] (gammaField R i) := (rfl)

/-- Nonnegative modes of every derivative field `varField R v` kill the vacuum `1`. -/
@[simp]
theorem ncoeff_varField_one_of_nonneg (v : Var ι) {n : ℤ} (hn : 0 ≤ n) :
    ((varField R v)[[n]]) 1 = 0 := by
  have hderiv : ∀ (A : VertexOperator R (Fock R ι)),
      (∀ m : ℤ, 0 ≤ m → (A[[m]]) 1 = 0) →
      ∀ (k : ℕ) (m : ℤ), 0 ≤ m → (((derivative (R := R) (V := Fock R ι))^[k] A)[[m]]) 1 = 0 := by
    intro A hA k
    induction k with
    | zero => exact hA
    | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply', ncoeff_derivative, LinearMap.smul_apply]
      rcases hm.eq_or_lt with rfl | hpos
      · simp
      · rw [ih (m - 1) (by omega), smul_zero]
  cases v with
  | beta i k => exact hderiv _ (fun _ hm ↦ ncoeff_betaField_one_of_nonneg R i hm) k n hn
  | gamma i k => exact hderiv _ (fun _ hm ↦ ncoeff_gammaField_one_of_nonneg R i hm) k n hn

/-- The `-1`-mode of `∂ᵏ β_i` is `k! · mulLeft (β_{i, -k - 1})`, and the `-1`-mode of `∂ᵏ γ_i` is
`k! · mulLeft (γ_{i, -k})`. -/
theorem ncoeff_neg_one_varField (v : Var ι) :
    (varField R v)[[-1]] = v.order.factorial • LinearMap.mulLeft R (X v) := by
  have hneg : ∀ (A : VertexOperator R (Fock R ι)) (k m : ℕ),
      ((derivative (R := R) (V := Fock R ι))^[k] A)[[-(m : ℤ) - 1]] =
        (Nat.ascFactorial (m + 1) k) • A[[-(m : ℤ) - 1 - k]] := by
    intro A k
    induction k with
    | zero =>
      intro m
      simp
    | succ k ih =>
      intro m
      rw [Function.iterate_succ_apply', ncoeff_derivative]
      have h₁ : -(-(m : ℤ) - 1) = ((m + 1 : ℕ) : ℤ) := by omega
      have h₂ : -(m : ℤ) - 1 - 1 = -((m + 1 : ℕ) : ℤ) - 1 := by omega
      have h₃ : -((m + 1 : ℕ) : ℤ) - 1 - k = -(m : ℤ) - 1 - ((k + 1 : ℕ) : ℤ) := by omega
      rw [h₁, h₂, ih (m + 1), h₃, natCast_zsmul, smul_smul, Nat.succ_ascFactorial,
        ← Nat.ascFactorial_succ]
  have h1 (A : VertexOperator R (Fock R ι)) (k : ℕ) :
      ((derivative (R := R) (V := Fock R ι))^[k] A)[[-1]] = k.factorial • A[[-(k : ℤ) - 1]] := by
    have := hneg A k 0
    simpa [Nat.one_ascFactorial, sub_eq_add_neg, add_comm] using this
  cases v with
  | beta i k =>
    rw [varField_beta, h1, ncoeff_betaField, betaMode_neg_sub_one, Var.order_beta]
  | gamma i k =>
    have hk : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by omega
    rw [varField_gamma, h1, ncoeff_gammaField, hk, gammaMode_neg_natCast, Var.order_gamma]

/-- Evaluating the `-1`-mode of `varField R v` on `1` produces `v.order! • X v`. -/
@[simp]
theorem ncoeff_neg_one_varField_one (v : Var ι) :
    ((varField R v)[[-1]]) 1 = v.order.factorial • X v := by
  rw [ncoeff_neg_one_varField]
  simp

/-- Translation covariance holds for every derivative field `varField R v`. -/
theorem lie_translation_ncoeff_varField (v : Var ι) (n : ℤ) :
    ⁅(translation R ι).toLinearMap, (varField R v)[[n]]⁆ =
      (derivative (varField R v))[[n]] := by
  have hderiv : ∀ (A : VertexOperator R (Fock R ι)),
      (∀ m : ℤ, ⁅(translation R ι).toLinearMap, A[[m]]⁆ = (derivative A)[[m]]) →
      ∀ (k : ℕ) (m : ℤ),
        ⁅(translation R ι).toLinearMap, ((derivative (R := R) (V := Fock R ι))^[k] A)[[m]]⁆ =
          (derivative ((derivative (R := R) (V := Fock R ι))^[k] A))[[m]] := by
    intro A hA k
    induction k with
    | zero => exact hA
    | succ k ih =>
      intro m
      rw [Function.iterate_succ_apply', ncoeff_derivative, lie_smul, ih (m - 1),
        ← ncoeff_derivative]
  cases v with
  | beta i k => exact hderiv _ (lie_translation_ncoeff_betaField R i) k n
  | gamma i k => exact hderiv _ (lie_translation_ncoeff_gammaField R i) k n

/-- Any two derivative fields `varField R u` and `varField R v` are mutually local of order at most
`1 + u.order + v.order`. -/
theorem isLocalOfOrder_varField (u v : Var ι) :
    (varField R u).IsLocalOfOrder (varField R v) (1 + u.order + v.order) := by
  cases u with
  | beta i k =>
    cases v with
    | beta j l =>
      rw [varField_beta, varField_beta, Var.order_beta, Var.order_beta]
      exact ((isLocalOfOrder_betaField_betaField R i j).mono (Nat.zero_le 1)).iterate_derivative
        k l
    | gamma j l =>
      rw [varField_beta, varField_gamma, Var.order_beta, Var.order_gamma]
      exact (isLocalOfOrder_betaField_gammaField R i j).iterate_derivative k l
  | gamma i k =>
    cases v with
    | beta j l =>
      rw [varField_gamma, varField_beta, Var.order_gamma, Var.order_beta]
      exact (isLocalOfOrder_gammaField_betaField R i j).iterate_derivative k l
    | gamma j l =>
      rw [varField_gamma, varField_gamma, Var.order_gamma, Var.order_gamma]
      exact ((isLocalOfOrder_gammaField_gammaField R i j).mono (Nat.zero_le 1)).iterate_derivative
        k l

/-- The right-nested normal-ordered product of the derivative fields along a list of creation
variables: `monomialField R [v₁, …, vₘ] = :varField v₁ (:… (:varField vₘ id:)):`. -/
def monomialField : List (Var ι) → VertexOperator R (Fock R ι)
  | [] => vacuumField R ι
  | v :: l => normalOrder (varField R v) (monomialField l)

@[simp]
theorem monomialField_nil : monomialField R ([] : List (Var ι)) = vacuumField R ι := (rfl)

@[simp]
theorem monomialField_cons (v : Var ι) (l : List (Var ι)) :
    monomialField R (v :: l) = normalOrder (varField R v) (monomialField R l) := (rfl)

/-- Nonnegative normalized modes of `monomialField R l` kill the vacuum `1`. -/
@[simp]
theorem ncoeff_monomialField_one_of_nonneg (l : List (Var ι)) {n : ℤ} (hn : 0 ≤ n) :
    ((monomialField R l)[[n]]) 1 = 0 := by
  induction l generalizing n with
  | nil =>
    rw [monomialField_nil, ncoeff_vacuumField_of_ne R (by omega), LinearMap.zero_apply]
  | cons v l ih =>
    rw [monomialField_cons, ncoeff_normalOrder]
    rw [normalOrderCoeff_eq_sum _ _ n 1 (P := 0) (Q := 0)
      (fun i _ ↦ ih (by omega))
      (fun i _ ↦ ncoeff_varField_one_of_nonneg R v (Int.natCast_nonneg i))]
    simp

/-- **Normal-ordered monomial identity:** evaluating the `-1`-mode of `monomialField R l` on `1`
produces the polynomial monomial `∏ v ∈ l, X v` scaled by the product of factorials
`∏ v ∈ l, v.order!`. -/
theorem ncoeff_neg_one_monomialField_one (l : List (Var ι)) :
    ((monomialField R l)[[-1]]) 1 =
      (l.map fun v ↦ v.order.factorial).prod • (l.map (X (R := R))).prod := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [monomialField_cons, ncoeff_normalOrder]
    rw [normalOrderCoeff_eq_sum _ _ (-1) 1 (P := 1) (Q := 0)
      (fun i hi ↦ ncoeff_monomialField_one_of_nonneg R l (by omega))
      (fun i _ ↦ ncoeff_varField_one_of_nonneg R v (Int.natCast_nonneg i))]
    simp only [range_one, sum_singleton, Nat.cast_zero, neg_zero, zero_sub, add_zero, range_zero,
      sum_empty]
    rw [ih, ncoeff_neg_one_varField, LinearMap.smul_apply, LinearMap.mulLeft_apply, mul_smul_comm,
      smul_smul, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]

/-- **Normal-ordered monomial identity over a `ℚ`-algebra:** dividing by the factorials recovers
the exact polynomial monomial `∏ v ∈ l, X v` from `monomialField R l`. -/
theorem ncoeff_neg_one_monomialField_one_rat [Algebra ℚ R] (l : List (Var ι)) :
    algebraMap ℚ R (l.map fun v ↦ (v.order.factorial : ℚ)⁻¹).prod •
        ((monomialField R l)[[-1]]) 1 =
      (l.map (X (R := R))).prod := by
  rw [ncoeff_neg_one_monomialField_one, ← Nat.cast_smul_eq_nsmul R, smul_smul]
  have hrat : (l.map fun v ↦ (v.order.factorial : ℚ)⁻¹).prod *
      ((l.map fun v ↦ v.order.factorial).prod : ℕ) = 1 := by
    induction l with
    | nil => simp
    | cons v l ih =>
      simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
      have hv : (v.order.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      calc
        (v.order.factorial : ℚ)⁻¹ * (l.map fun w ↦ (w.order.factorial : ℚ)⁻¹).prod *
            ((v.order.factorial : ℚ) * ((l.map fun w ↦ w.order.factorial).prod : ℕ))
          = ((v.order.factorial : ℚ)⁻¹ * (v.order.factorial : ℚ)) *
              ((l.map fun w ↦ (w.order.factorial : ℚ)⁻¹).prod *
                ((l.map fun w ↦ w.order.factorial).prod : ℕ)) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hv, ih, one_mul]
  have hprod : algebraMap ℚ R (l.map fun v ↦ (v.order.factorial : ℚ)⁻¹).prod *
      (((l.map fun v ↦ v.order.factorial).prod : ℕ) : R) = 1 := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, hrat, map_one]
  rw [hprod, one_smul]

/-! ### Symmetry of normal ordering on the generating fields -/

/-- Normal ordering of two beta fields is symmetric: `:β_i β_j: = :β_j β_i:`. -/
theorem normalOrder_betaField_comm (i j : ι) :
    normalOrder (betaField R i) (betaField R j) =
      normalOrder (betaField R j) (betaField R i) :=
  normalOrder_comm_of_commute_ne_neg_one _ _ fun r s _ ↦
    sub_eq_zero.mp (lie_ncoeff_betaField_betaField R i j r s)

/-- Normal ordering of two gamma fields is symmetric: `:γ_i γ_j: = :γ_j γ_i:`. -/
theorem normalOrder_gammaField_comm (i j : ι) :
    normalOrder (gammaField R i) (gammaField R j) =
      normalOrder (gammaField R j) (gammaField R i) :=
  normalOrder_comm_of_commute_ne_neg_one _ _ fun r s _ ↦
    sub_eq_zero.mp (lie_ncoeff_gammaField_gammaField R i j r s)

/-- Normal ordering of a beta field and a gamma field is symmetric: `:β_i γ_j: = :γ_j β_i:`
(the simple-pole contraction is constant and hence killed by `T`). -/
theorem normalOrder_betaField_gammaField (i j : ι) :
    normalOrder (betaField R i) (gammaField R j) =
      normalOrder (gammaField R j) (betaField R i) := by
  refine normalOrder_comm_of_commute_ne_neg_one _ _ fun r s hrs ↦ ?_
  rw [ncoeff_betaField, ncoeff_gammaField]
  exact sub_eq_zero.mp (lie_betaMode_gammaMode_of_ne_or_add_ne_zero R (Or.inr (by omega)))

/-! ### Reindexing of fields -/

/-- Reindexing intertwines the normalized modes of `betaField`. -/
theorem reindex_ncoeff_betaField {κ : Type*} (e : ι ≃ κ) (i : ι) (n : ℤ) (p : Fock R ι) :
    reindex R e (((betaField R i)[[n]]) p) = ((betaField R (e i))[[n]]) (reindex R e p) := by
  simpa using reindex_betaMode R e i n p

/-- Reindexing intertwines the normalized modes of `gammaField`. -/
theorem reindex_ncoeff_gammaField {κ : Type*} (e : ι ≃ κ) (i : ι) (n : ℤ) (p : Fock R ι) :
    reindex R e (((gammaField R i)[[n]]) p) = ((gammaField R (e i))[[n]]) (reindex R e p) := by
  simpa using reindex_gammaMode R e i (n + 1) p

end TauCeti.BetaGamma
