/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Derivation.Lie
import TauCeti.RingTheory.Derivation.FirstOrder

/-!
# The beta-gamma Weyl system and its Fock module

For an arbitrary index type `ι` (in the affine Lie algebra application, the set of positive roots)
and a commutative ring `R`, the beta-gamma Fock space is the polynomial algebra

`M = R[β_{i, -k - 1}, γ_{i, -k} | i ∈ ι, k ∈ ℕ]`

(`TauCeti.BetaGamma.Fock`), with vacuum vector `1`. Its generators are indexed by
`TauCeti.BetaGamma.Var ι`, where `Var.beta i k` stands for `β_{i, -k - 1}` and `Var.gamma i k`
stands for `γ_{i, -k}`.

The Weyl modes `β_{i, n}` and `γ_{i, n}` (`TauCeti.BetaGamma.betaMode`,
`TauCeti.BetaGamma.gammaMode`) act on `Fock R ι` by creation and annihilation:

* for `n < 0`, `β_{i, n}` multiplies by `β_{i, n}`; for `n ≥ 0`, `β_{i, n} = ∂/∂γ_{i, -n}`;
* for `n ≤ 0`, `γ_{i, n}` multiplies by `γ_{i, n}`; for `n > 0`, `γ_{i, n} = -∂/∂β_{i, -n}`.

Thus `β_{i, n} 1 = 0` for `n ≥ 0` and `γ_{i, n} 1 = 0` for `n > 0`, while the creation modes
`β_{i, n}` (`n < 0`) and `γ_{i, n}` (`n ≤ 0`) generate `Fock R ι` from `1`. The modes satisfy the
Weyl commutation relations

`[β_{i, m}, γ_{j, n}] = δ_{i, j} δ_{m + n, 0}`,   `[β_{i, m}, β_{j, n}] = 0`,
`[γ_{i, m}, γ_{j, n}] = 0`.

The translation operator `T` (`TauCeti.BetaGamma.translation`) is the derivation sending
`β_{i, -k - 1} ↦ (k + 1) β_{i, -k - 2}` and `γ_{i, -k} ↦ (k + 1) γ_{i, -k - 1}`. It kills `1`
and satisfies the mode covariance identities

`[T, β_{i, n}] = -n β_{i, n - 1}`   and   `[T, γ_{i, n}] = -(n - 1) γ_{i, n - 1}`.

All constructions hold over an arbitrary commutative ring `R` and arbitrary index type `ι`, with
no characteristic-zero or finiteness assumptions.

## Main definitions

* `TauCeti.BetaGamma.Var`: the creation variable index set (`beta i k` and `gamma i k`).
* `TauCeti.BetaGamma.Fock`: the polynomial Fock carrier `MvPolynomial (Var ι) R`.
* `TauCeti.BetaGamma.betaMode`, `TauCeti.BetaGamma.gammaMode`: the Weyl mode endomorphisms.
* `TauCeti.BetaGamma.translation`: the translation derivation `T` on `Fock R ι`.
* `TauCeti.BetaGamma.reindex`: the algebra equivalence induced by a bijection of index sets.

## Main results

* `TauCeti.BetaGamma.lie_betaMode_betaMode`, `TauCeti.BetaGamma.lie_gammaMode_gammaMode`,
  `TauCeti.BetaGamma.lie_betaMode_gammaMode`, `TauCeti.BetaGamma.lie_gammaMode_betaMode`:
  the Weyl commutation relations.
* `TauCeti.BetaGamma.betaMode_one_of_nonneg`, `TauCeti.BetaGamma.gammaMode_one_of_pos`:
  the vacuum annihilation properties.
* `TauCeti.BetaGamma.eq_top_of_one_mem_of_creation_closed`: the creation modes generate `Fock R ι`
  from the vacuum `1`.
* `TauCeti.BetaGamma.lie_translation_betaMode`, `TauCeti.BetaGamma.lie_translation_gammaMode`:
  translation covariance of the Weyl modes.
* `TauCeti.BetaGamma.pow_translation_X_beta_zero`,
  `TauCeti.BetaGamma.pow_translation_X_gamma_zero`: `Tᵏ` generates the higher creation variables
  up to `k!`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §5.3.3, equations (5.3-3)–(5.3-5),
  and §5.4.1, pp. 142–143.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §11.3.
-/

public section

noncomputable section

open MvPolynomial

attribute [local instance] LieRing.ofAssociativeRing

namespace TauCeti.BetaGamma

/-! ### Creation variables and the Fock carrier -/

/-- The polynomial generators of the beta-gamma Fock space indexed by `ι`:
`beta i k` represents the creation mode `β_{i, -k - 1}` (`k : ℕ`, mode index `-k - 1 < 0`),
and `gamma i k` represents `γ_{i, -k}` (`k : ℕ`, mode index `-k ≤ 0`). -/
inductive Var (ι : Type*) where
  /-- The beta creation variable `β_{i, -k - 1}`. -/
  | beta (i : ι) (k : ℕ)
  /-- The gamma creation variable `γ_{i, -k}`. -/
  | gamma (i : ι) (k : ℕ)
  deriving DecidableEq

namespace Var

variable {ι κ : Type*}

/-- The index in `ι` attached to a creation variable. -/
def index : Var ι → ι
  | .beta i _ => i
  | .gamma i _ => i

/-- The derivative order `k : ℕ` of a creation variable (`β_{i, -k - 1}` or `γ_{i, -k}`). -/
def order : Var ι → ℕ
  | .beta _ k => k
  | .gamma _ k => k

/-- Shift the derivative order of a creation variable up by one. -/
def shift : Var ι → Var ι
  | .beta i k => .beta i (k + 1)
  | .gamma i k => .gamma i (k + 1)

/-- Map a creation variable along a function `f : ι → κ` on the index type. -/
def map (f : ι → κ) : Var ι → Var κ
  | .beta i k => .beta (f i) k
  | .gamma i k => .gamma (f i) k

@[simp]
theorem index_beta (i : ι) (k : ℕ) : (Var.beta i k).index = i := (rfl)

@[simp]
theorem index_gamma (i : ι) (k : ℕ) : (Var.gamma i k).index = i := (rfl)

@[simp]
theorem order_beta (i : ι) (k : ℕ) : (Var.beta i k).order = k := (rfl)

@[simp]
theorem order_gamma (i : ι) (k : ℕ) : (Var.gamma i k).order = k := (rfl)

@[simp]
theorem shift_beta (i : ι) (k : ℕ) : (Var.beta i k).shift = .beta i (k + 1) := (rfl)

@[simp]
theorem shift_gamma (i : ι) (k : ℕ) : (Var.gamma i k).shift = .gamma i (k + 1) := (rfl)

@[simp]
theorem map_beta (f : ι → κ) (i : ι) (k : ℕ) : map f (.beta i k) = .beta (f i) k := (rfl)

@[simp]
theorem map_gamma (f : ι → κ) (i : ι) (k : ℕ) : map f (.gamma i k) = .gamma (f i) k := (rfl)

@[simp]
theorem map_id : map (id : ι → ι) = id := by
  ext v
  cases v <;> rfl

theorem map_comp {τ : Type*} (g : κ → τ) (f : ι → κ) :
    map (g ∘ f) = map g ∘ map f := by
  ext v
  cases v <;> rfl

/-- The bijection on creation variables induced by a bijection of index types. -/
def mapEquiv (e : ι ≃ κ) : Var ι ≃ Var κ where
  toFun := map e
  invFun := map e.symm
  left_inv v := by cases v <;> simp
  right_inv v := by cases v <;> simp

@[simp]
theorem mapEquiv_beta (e : ι ≃ κ) (i : ι) (k : ℕ) :
    mapEquiv e (.beta i k) = .beta (e i) k := (rfl)

@[simp]
theorem mapEquiv_gamma (e : ι ≃ κ) (i : ι) (k : ℕ) :
    mapEquiv e (.gamma i k) = .gamma (e i) k := (rfl)

@[simp]
theorem mapEquiv_symm (e : ι ≃ κ) : (mapEquiv e).symm = mapEquiv e.symm := (rfl)

end Var

/-- The polynomial Fock module `R[β_{i, -k - 1}, γ_{i, -k} | i ∈ ι, k ∈ ℕ]` of the beta-gamma
system indexed by `ι`, with vacuum vector `1`. -/
abbrev Fock (R ι : Type*) [CommSemiring R] : Type _ :=
  MvPolynomial (Var ι) R

/-! ### Weyl modes -/

variable (R : Type*) [CommRing R] {ι : Type*}

/-- The Weyl mode `β_{i, n}` acting on `Fock R ι`:
for `n ≥ 0` it differentiates along `γ_{i, -n}` (annihilation);
for `n < 0` it multiplies by `β_{i, n}` (creation). -/
def betaMode (i : ι) (n : ℤ) : Module.End R (Fock R ι) :=
  if 0 ≤ n then
    (pderiv (Var.gamma i n.toNat)).toLinearMap
  else
    LinearMap.mulLeft R (X (Var.beta i (-n - 1).toNat))

/-- The Weyl mode `γ_{i, n}` acting on `Fock R ι`:
for `n > 0` it acts as `-∂/∂β_{i, -n}` (annihilation);
for `n ≤ 0` it multiplies by `γ_{i, n}` (creation). -/
def gammaMode (i : ι) (n : ℤ) : Module.End R (Fock R ι) :=
  if 0 < n then
    -(pderiv (Var.beta i (n - 1).toNat)).toLinearMap
  else
    LinearMap.mulLeft R (X (Var.gamma i (-n).toNat))

theorem betaMode_of_nonneg (i : ι) {n : ℤ} (hn : 0 ≤ n) :
    betaMode R i n = (pderiv (Var.gamma i n.toNat)).toLinearMap := by
  simp [betaMode, hn]

@[simp]
theorem betaMode_natCast (i : ι) (k : ℕ) :
    betaMode R i k = (pderiv (Var.gamma i k)).toLinearMap := by
  simp [betaMode]

@[simp]
theorem betaMode_zero (i : ι) :
    betaMode R i 0 = (pderiv (Var.gamma i 0)).toLinearMap := by
  simpa using betaMode_natCast R i 0

theorem betaMode_of_neg (i : ι) {n : ℤ} (hn : n < 0) :
    betaMode R i n = LinearMap.mulLeft R (X (Var.beta i (-n - 1).toNat)) := by
  simp [betaMode, hn.not_ge]

@[simp]
theorem betaMode_neg_sub_one (i : ι) (k : ℕ) :
    betaMode R i (-(k : ℤ) - 1) = LinearMap.mulLeft R (X (Var.beta i k)) := by
  rw [betaMode_of_neg R i (by omega)]
  have h : -(-(k : ℤ) - 1) - 1 = k := by omega
  rw [h, Int.toNat_natCast]

@[simp]
theorem betaMode_neg_one (i : ι) :
    betaMode R i (-1) = LinearMap.mulLeft R (X (Var.beta i 0)) := by
  simpa using betaMode_neg_sub_one R i 0

theorem gammaMode_of_pos (i : ι) {n : ℤ} (hn : 0 < n) :
    gammaMode R i n = -(pderiv (Var.beta i (n - 1).toNat)).toLinearMap := by
  simp [gammaMode, hn]

@[simp]
theorem gammaMode_natCast_add_one (i : ι) (k : ℕ) :
    gammaMode R i ((k : ℤ) + 1) = -(pderiv (Var.beta i k)).toLinearMap := by
  rw [gammaMode_of_pos R i (by omega)]
  have h : ((k : ℤ) + 1) - 1 = k := by omega
  rw [h, Int.toNat_natCast]

@[simp]
theorem gammaMode_one (i : ι) :
    gammaMode R i 1 = -(pderiv (Var.beta i 0)).toLinearMap := by
  simpa using gammaMode_natCast_add_one R i 0

theorem gammaMode_of_nonpos (i : ι) {n : ℤ} (hn : n ≤ 0) :
    gammaMode R i n = LinearMap.mulLeft R (X (Var.gamma i (-n).toNat)) := by
  simp [gammaMode, hn.not_gt]

@[simp]
theorem gammaMode_neg_natCast (i : ι) (k : ℕ) :
    gammaMode R i (-(k : ℤ)) = LinearMap.mulLeft R (X (Var.gamma i k)) := by
  rw [gammaMode_of_nonpos R i (by omega)]
  simp

@[simp]
theorem gammaMode_zero (i : ι) :
    gammaMode R i 0 = LinearMap.mulLeft R (X (Var.gamma i 0)) := by
  simpa using gammaMode_neg_natCast R i 0

/-! ### Action on the vacuum `1` -/

/-- Nonnegative beta modes kill the vacuum `1`. -/
@[simp]
theorem betaMode_one_of_nonneg (i : ι) {n : ℤ} (hn : 0 ≤ n) :
    betaMode R i n 1 = 0 := by
  simp [betaMode_of_nonneg R i hn]

/-- Positive gamma modes kill the vacuum `1`. -/
@[simp]
theorem gammaMode_one_of_pos (i : ι) {n : ℤ} (hn : 0 < n) :
    gammaMode R i n 1 = 0 := by
  simp [gammaMode_of_pos R i hn]

/-- Negative beta modes create the polynomial generators `β_{i, -k - 1}` from `1`. -/
theorem betaMode_neg_sub_one_one (i : ι) (k : ℕ) :
    betaMode R i (-(k : ℤ) - 1) 1 = X (Var.beta i k) := by
  simp

/-- Nonpositive gamma modes create the polynomial generators `γ_{i, -k}` from `1`. -/
theorem gammaMode_neg_natCast_one (i : ι) (k : ℕ) :
    gammaMode R i (-(k : ℤ)) 1 = X (Var.gamma i k) := by
  simp

/-! ### Weyl commutation relations -/

private theorem lie_pderiv_pderiv (u v : Var ι) :
    ⁅(pderiv (R := R) u).toLinearMap, (pderiv (R := R) v).toLinearMap⁆ = 0 := by
  ext p
  simp [Ring.lie_def, mul_apply_eq_comp, pderiv_comm]

private theorem lie_mulLeft_mulLeft (a b : Fock R ι) :
    ⁅LinearMap.mulLeft R a, LinearMap.mulLeft R b⁆ = 0 := by
  ext p
  simp [Ring.lie_def, mul_apply_eq_comp, mul_left_comm]

/-- All beta modes commute with one another: `[β_{i, m}, β_{j, n}] = 0`. -/
@[simp]
theorem lie_betaMode_betaMode (i j : ι) (m n : ℤ) :
    ⁅betaMode R i m, betaMode R j n⁆ = 0 := by
  rcases le_or_gt 0 m with hm | hm <;> rcases le_or_gt 0 n with hn | hn
  · rw [betaMode_of_nonneg R i hm, betaMode_of_nonneg R j hn, lie_pderiv_pderiv]
  · rw [betaMode_of_nonneg R i hm, betaMode_of_neg R j hn, Derivation.lie_mulLeft]
    simp
  · rw [← neg_eq_zero, ← lie_skew, betaMode_of_nonneg R j hn, betaMode_of_neg R i hm,
      Derivation.lie_mulLeft]
    simp
  · rw [betaMode_of_neg R i hm, betaMode_of_neg R j hn, lie_mulLeft_mulLeft]

/-- All gamma modes commute with one another: `[γ_{i, m}, γ_{j, n}] = 0`. -/
@[simp]
theorem lie_gammaMode_gammaMode (i j : ι) (m n : ℤ) :
    ⁅gammaMode R i m, gammaMode R j n⁆ = 0 := by
  rcases lt_or_ge 0 m with hm | hm <;> rcases lt_or_ge 0 n with hn | hn
  · rw [gammaMode_of_pos R i hm, gammaMode_of_pos R j hn, neg_lie, lie_neg, neg_neg,
      lie_pderiv_pderiv]
  · rw [gammaMode_of_pos R i hm, gammaMode_of_nonpos R j hn, neg_lie, Derivation.lie_mulLeft]
    simp
  · rw [← neg_eq_zero, ← lie_skew, gammaMode_of_pos R j hn, gammaMode_of_nonpos R i hm, neg_lie,
      Derivation.lie_mulLeft]
    simp
  · rw [gammaMode_of_nonpos R i hm, gammaMode_of_nonpos R j hn, lie_mulLeft_mulLeft]

/-- Opposite-index modes of the same index satisfy `[β_{i, m}, γ_{i, n}] = 1` when `m + n = 0`. -/
theorem lie_betaMode_gammaMode_of_add_eq_zero (i : ι) {m n : ℤ} (h : m + n = 0) :
    ⁅betaMode R i m, gammaMode R i n⁆ = 1 := by
  rcases le_or_gt 0 m with hm | hm
  · have hn : n ≤ 0 := by omega
    have hmn : (-n).toNat = m.toNat := by omega
    rw [betaMode_of_nonneg R i hm, gammaMode_of_nonpos R i hn, hmn, Derivation.lie_mulLeft,
      pderiv_X_self, LinearMap.mulLeft_one]
    rfl
  · have hn : 0 < n := by omega
    have hmn : (n - 1).toNat = (-m - 1).toNat := by omega
    rw [betaMode_of_neg R i hm, gammaMode_of_pos R i hn, hmn, lie_neg, ← lie_skew, neg_neg,
      Derivation.lie_mulLeft, pderiv_X_self, LinearMap.mulLeft_one]
    rfl

/-- Beta and gamma modes commute whenever their indices differ or their mode numbers do not sum
to zero. -/
theorem lie_betaMode_gammaMode_of_ne_or_add_ne_zero {i j : ι} {m n : ℤ}
    (h : i ≠ j ∨ m + n ≠ 0) :
    ⁅betaMode R i m, gammaMode R j n⁆ = 0 := by
  rcases le_or_gt 0 m with hm | hm <;> rcases lt_or_ge 0 n with hn | hn
  · rw [betaMode_of_nonneg R i hm, gammaMode_of_pos R j hn, lie_neg, lie_pderiv_pderiv, neg_zero]
  · rw [betaMode_of_nonneg R i hm, gammaMode_of_nonpos R j hn, Derivation.lie_mulLeft]
    have hne : Var.gamma j (-n).toNat ≠ Var.gamma i m.toNat := by
      intro heq
      injection heq with hij hmn
      rcases h with hne' | hadd
      · exact hne' hij.symm
      · omega
    rw [pderiv_X_of_ne hne, LinearMap.mulLeft_zero_eq_zero]
  · rw [betaMode_of_neg R i hm, gammaMode_of_pos R j hn, lie_neg, ← lie_skew, neg_neg,
      Derivation.lie_mulLeft]
    have hne : Var.beta i (-m - 1).toNat ≠ Var.beta j (n - 1).toNat := by
      intro heq
      injection heq with hij hmn
      rcases h with hne' | hadd
      · exact hne' hij
      · omega
    rw [pderiv_X_of_ne hne, LinearMap.mulLeft_zero_eq_zero]
  · rw [betaMode_of_neg R i hm, gammaMode_of_nonpos R j hn, lie_mulLeft_mulLeft]

/-- **The Weyl commutation relation `[β_{i, m}, γ_{j, n}] = δ_{i, j} δ_{m + n, 0}`.** -/
theorem lie_betaMode_gammaMode [DecidableEq ι] (i j : ι) (m n : ℤ) :
    ⁅betaMode R i m, gammaMode R j n⁆ = if i = j ∧ m + n = 0 then 1 else 0 := by
  split_ifs with h
  · rcases h with ⟨rfl, hmn⟩
    exact lie_betaMode_gammaMode_of_add_eq_zero R i hmn
  · exact lie_betaMode_gammaMode_of_ne_or_add_ne_zero R (not_and_or.mp h)

/-- **The reversed Weyl commutation relation `[γ_{i, m}, β_{j, n}] = -δ_{i, j} δ_{m + n, 0}`.** -/
theorem lie_gammaMode_betaMode [DecidableEq ι] (i j : ι) (m n : ℤ) :
    ⁅gammaMode R i m, betaMode R j n⁆ = if i = j ∧ m + n = 0 then -1 else 0 := by
  split_ifs with h
  · rcases h with ⟨rfl, hmn⟩
    rw [← lie_skew, lie_betaMode_gammaMode_of_add_eq_zero R i (by omega)]
  · rw [← lie_skew, lie_betaMode_gammaMode_of_ne_or_add_ne_zero R ?_, neg_zero]
    rcases not_and_or.mp h with hij | hmn
    · exact Or.inl (Ne.symm hij)
    · exact Or.inr (by omega)

/-! ### Basic vacuum contractions -/

/-- `β_{i, 0} γ_{i, 0} 1 = 1`: the ordered beta-gamma simple pole has coefficient `+1`. -/
theorem betaMode_zero_gammaMode_zero_one (i : ι) :
    betaMode R i 0 (gammaMode R i 0 1) = 1 := by
  simp

/-- `γ_{i, 1} β_{i, -1} 1 = -1`: the ordered gamma-beta simple pole has coefficient `-1`. -/
theorem gammaMode_one_betaMode_neg_one_one (i : ι) :
    gammaMode R i 1 (betaMode R i (-1) 1) = -1 := by
  simp

/-- `β_{i, 0} β_{i, -1} 1 = 0`: same-field beta contractions vanish. -/
theorem betaMode_zero_betaMode_neg_one_one (i : ι) :
    betaMode R i 0 (betaMode R i (-1) 1) = 0 := by
  simp

/-- `γ_{i, 1} γ_{i, 0} 1 = 0`: same-field gamma contractions vanish. -/
theorem gammaMode_one_gammaMode_zero_one (i : ι) :
    gammaMode R i 1 (gammaMode R i 0 1) = 0 := by
  simp

/-- The square `γ_{i, 0}²` is nonzero over any nontrivial coefficient ring. -/
theorem X_gamma_zero_sq_ne_zero [Nontrivial R] (i : ι) :
    (X (Var.gamma i 0) : Fock R ι) ^ 2 ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : Fock R ι ↦ p.coeff (Finsupp.single (Var.gamma i 0) 2)) h
  classical
  simp [X_pow_eq_monomial] at hcoeff

/-! ### Generation from the vacuum -/

/-- The creation modes `β_{i, -k - 1}` and `γ_{i, -k}` generate the entire Fock module `Fock R ι`
from the vacuum `1`. -/
theorem eq_top_of_one_mem_of_creation_closed {W : Submodule R (Fock R ι)}
    (h1 : (1 : Fock R ι) ∈ W)
    (hβ : ∀ i (k : ℕ), ∀ p ∈ W, betaMode R i (-(k : ℤ) - 1) p ∈ W)
    (hγ : ∀ i (k : ℕ), ∀ p ∈ W, gammaMode R i (-(k : ℤ)) p ∈ W) :
    W = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun p ↦ ?_
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.C_eq_smul_one]
    exact W.smul_mem r h1
  | add p q hp hq => exact W.add_mem hp hq
  | mul_X p v hp =>
    rw [mul_comm]
    cases v with
    | beta i k => simpa using hβ i k p hp
    | gamma i k => simpa using hγ i k p hp

/-- Any `R`-submodule of `Fock R ι` containing `1` and closed under all beta and gamma modes is
all of `Fock R ι`. -/
theorem eq_top_of_one_mem_of_mode_closed {W : Submodule R (Fock R ι)}
    (h1 : (1 : Fock R ι) ∈ W)
    (hβ : ∀ i (n : ℤ), ∀ p ∈ W, betaMode R i n p ∈ W)
    (hγ : ∀ i (n : ℤ), ∀ p ∈ W, gammaMode R i n p ∈ W) :
    W = ⊤ :=
  eq_top_of_one_mem_of_creation_closed R h1 (fun i k ↦ hβ i (-(k : ℤ) - 1))
    (fun i k ↦ hγ i (-(k : ℤ)))

/-! ### Translation operator -/

/-- The translation operator `T` on `Fock R ι`, defined as the derivation sending
`β_{i, -k - 1} ↦ (k + 1) β_{i, -k - 2}` and `γ_{i, -k} ↦ (k + 1) γ_{i, -k - 1}`. -/
def translation (ι : Type*) : Derivation R (Fock R ι) (Fock R ι) :=
  mkDerivation R fun v ↦ ((v.order + 1 : ℕ) : R) • X v.shift

@[simp]
theorem translation_X (v : Var ι) :
    translation R ι (X v) = ((v.order + 1 : ℕ) : R) • X v.shift :=
  mkDerivation_X R _ v

theorem translation_X_beta (i : ι) (k : ℕ) :
    translation R ι (X (Var.beta i k)) = ((k + 1 : ℕ) : R) • X (Var.beta i (k + 1)) :=
  mkDerivation_X R _ (Var.beta i k)

theorem translation_X_gamma (i : ι) (k : ℕ) :
    translation R ι (X (Var.gamma i k)) = ((k + 1 : ℕ) : R) • X (Var.gamma i (k + 1)) :=
  mkDerivation_X R _ (Var.gamma i k)

/-- Translation kills the vacuum `1`. -/
theorem translation_one : translation R ι 1 = 0 :=
  Derivation.map_one_eq_zero _

private theorem lie_translation_pderiv_zero {u : Var ι} (hu : u.order = 0) :
    ⁅translation R ι, pderiv (R := R) u⁆ = 0 := by
  apply derivation_ext
  intro v
  rw [Derivation.commutator_apply]
  have hfirst : translation R ι (pderiv (R := R) u (X v)) = 0 := by
    by_cases hv : v = u
    · subst hv; simp
    · simp [pderiv_X_of_ne hv]
  have hne : v.shift ≠ u := by
    intro h
    have hord := congrArg Var.order h
    cases v <;> simp at hord <;> omega
  simp [hfirst, pderiv_X_of_ne hne]

private theorem lie_translation_pderiv_shift (u : Var ι) :
    ⁅translation R ι, pderiv (R := R) u.shift⁆ =
      (-((u.order + 1 : ℕ) : ℤ)) • pderiv (R := R) u := by
  apply derivation_ext
  intro v
  rw [Derivation.commutator_apply]
  have hfirst : translation R ι (pderiv (R := R) u.shift (X v)) = 0 := by
    by_cases hv : v = u.shift
    · subst hv; simp
    · simp [pderiv_X_of_ne hv]
  rw [hfirst, zero_sub, translation_X, (pderiv (R := R) u.shift).map_smul]
  by_cases hv : v = u
  · subst hv
    rw [pderiv_X_self, smul_apply, pderiv_X_self, neg_smul, natCast_zsmul,
      Nat.cast_smul_eq_nsmul]
  · have hne : v.shift ≠ u.shift := by
      intro h
      cases u <;> cases v <;> simp_all [Var.shift]
    simp [pderiv_X_of_ne hne, pderiv_X_of_ne hv]

/-- **Translation covariance for beta modes:** `[T, β_{i, n}] = -n β_{i, n - 1}`. -/
theorem lie_translation_betaMode (i : ι) (n : ℤ) :
    ⁅(translation R ι).toLinearMap, betaMode R i n⁆ = (-n) • betaMode R i (n - 1) := by
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    cases n with
    | zero =>
      rw [betaMode_natCast, ← Derivation.commutator_coe_linear_map,
        lie_translation_pderiv_zero R (u := .gamma i 0) rfl]
      simp
    | succ k =>
      have hk : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      rw [betaMode_natCast, hk, betaMode_natCast, ← Derivation.commutator_coe_linear_map]
      have h := lie_translation_pderiv_shift R (Var.gamma i k)
      simpa using congrArg Derivation.toLinearMap h
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    have hk : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by omega
    have hneg : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by omega
    rw [betaMode_neg_sub_one, hk, betaMode_neg_sub_one, hneg, Derivation.lie_mulLeft,
      translation_X_beta]
    exact LinearMap.ext fun p ↦ by
      rw [LinearMap.mulLeft_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, smul_mul_assoc,
        natCast_zsmul, Nat.cast_smul_eq_nsmul]

/-- **Translation covariance for gamma modes:** `[T, γ_{i, n}] = -(n - 1) γ_{i, n - 1}`. -/
theorem lie_translation_gammaMode (i : ι) (n : ℤ) :
    ⁅(translation R ι).toLinearMap, gammaMode R i n⁆ =
      (-(n - 1)) • gammaMode R i (n - 1) := by
  rcases lt_or_ge 0 n with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    cases k with
    | zero =>
      rw [gammaMode_natCast_add_one, lie_neg, ← Derivation.commutator_coe_linear_map,
        lie_translation_pderiv_zero R (u := .beta i 0) rfl]
      simp
    | succ k' =>
      have hk : ((k' + 1 : ℕ) : ℤ) + 1 - 1 = (k' : ℤ) + 1 := by omega
      rw [gammaMode_natCast_add_one, hk, gammaMode_natCast_add_one, lie_neg,
        ← Derivation.commutator_coe_linear_map]
      have h := congrArg (fun D : Derivation R (Fock R ι) (Fock R ι) ↦ -D.toLinearMap)
        (lie_translation_pderiv_shift R (Var.beta i k'))
      simpa [neg_smul] using h
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    have hk : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
    have hneg : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by omega
    rw [gammaMode_neg_natCast, hneg, hk, gammaMode_neg_natCast, Derivation.lie_mulLeft,
      translation_X_gamma]
    exact LinearMap.ext fun p ↦ by
      rw [LinearMap.mulLeft_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, smul_mul_assoc,
        natCast_zsmul, Nat.cast_smul_eq_nsmul]

/-- Iterated translation produces the higher beta generators up to factorials:
`Tᵏ (β_{i, -1}) = k! • β_{i, -k - 1}`. -/
theorem pow_translation_X_beta_zero (i : ι) (k : ℕ) :
    ((translation R ι).toLinearMap ^ k) (X (Var.beta i 0)) =
      k.factorial • X (Var.beta i k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_nsmul, Derivation.coeFn_coe, translation_X_beta,
      Nat.factorial_succ, mul_nsmul, Nat.cast_smul_eq_nsmul, smul_comm]

/-- Iterated translation produces the higher gamma generators up to factorials:
`Tᵏ (γ_{i, 0}) = k! • γ_{i, -k}`. -/
theorem pow_translation_X_gamma_zero (i : ι) (k : ℕ) :
    ((translation R ι).toLinearMap ^ k) (X (Var.gamma i 0)) =
      k.factorial • X (Var.gamma i k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_nsmul, Derivation.coeFn_coe, translation_X_gamma,
      Nat.factorial_succ, mul_nsmul, Nat.cast_smul_eq_nsmul, smul_comm]

/-! ### Reindexing -/

/-- A bijection `e : ι ≃ κ` induces an `R`-algebra isomorphism of beta-gamma Fock spaces. -/
def reindex {κ : Type*} (e : ι ≃ κ) : Fock R ι ≃ₐ[R] Fock R κ :=
  renameEquiv R (Var.mapEquiv e)

@[simp]
theorem reindex_X {κ : Type*} (e : ι ≃ κ) (v : Var ι) :
    reindex R e (X v) = X (Var.mapEquiv e v) :=
  (renameEquiv_apply R (Var.mapEquiv e) (X v)).trans (rename_X _ v)

/-- Reindexing intertwines the beta modes. -/
theorem reindex_betaMode {κ : Type*} (e : ι ≃ κ) (i : ι) (n : ℤ) (p : Fock R ι) :
    reindex R e (betaMode R i n p) = betaMode R (e i) n (reindex R e p) := by
  rcases le_or_gt 0 n with hn | hn
  · rw [betaMode_of_nonneg R i hn, betaMode_of_nonneg R (e i) hn]
    simpa [reindex, Var.mapEquiv_gamma] using
      (pderiv_rename (Var.mapEquiv e).injective (Var.gamma i n.toNat) p).symm
  · rw [betaMode_of_neg R i hn, betaMode_of_neg R (e i) hn]
    simp

/-- Reindexing intertwines the gamma modes. -/
theorem reindex_gammaMode {κ : Type*} (e : ι ≃ κ) (i : ι) (n : ℤ) (p : Fock R ι) :
    reindex R e (gammaMode R i n p) = gammaMode R (e i) n (reindex R e p) := by
  rcases lt_or_ge 0 n with hn | hn
  · rw [gammaMode_of_pos R i hn, gammaMode_of_pos R (e i) hn]
    simp only [LinearMap.neg_apply, Derivation.coeFn_coe, map_neg]
    congr 1
    simpa [reindex, Var.mapEquiv_beta] using
      (pderiv_rename (Var.mapEquiv e).injective (Var.beta i (n - 1).toNat) p).symm
  · rw [gammaMode_of_nonpos R i hn, gammaMode_of_nonpos R (e i) hn]
    simp

/-- Reindexing intertwines the translation derivation. -/
theorem reindex_translation {κ : Type*} (e : ι ≃ κ) (p : Fock R ι) :
    reindex R e (translation R ι p) = translation R κ (reindex R e p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [← algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgEquiv.commutes,
      Derivation.map_algebraMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, reindex_X, translation_X,
      map_smul]
    cases v <;> simp

end TauCeti.BetaGamma
