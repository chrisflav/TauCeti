/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
import TauCeti.Algebra.Ring.Invertible

/-!
# The sign isomorphism and positivity at negative loop parameters

Over every commutative ring `R` and at every loop parameter `δ : R`, negating the Temperley–Lieb
generators defines an `R`-algebra isomorphism

`signEquiv δ n : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n`, `e δ i ↦ -e (-δ) i`.

The quadratic relation `(e i)² = δ • e i` becomes `(-e i)² = (-δ) • (-e i)`, the adjacent zigzag
relation `(e i)(e j)(e i) = e i` picks up three minus signs on the left and one on the right, and
commutation of distant generators is unchanged. By contrast, no algebra homomorphism can fix the
generator on two strands once `2 * δ ≠ 0`
(`TauCeti.TemperleyLieb.not_exists_algHom_map_e_eq`).

The sign isomorphism commutes with adding a straight strand, fixes the augmentation and the
Jones–Wenzl projections (`TauCeti.TemperleyLieb.signEquiv_jonesWenzl`), and for a self-adjoint loop
parameter preserves the analytic adjoint (`TauCeti.TemperleyLieb.signStarAlgEquiv`). On Markov
traces it introduces the parity sign `(-1) ^ n` on `n` strands:

`tr₂ n (signEquiv δ n x) = (-1) ^ n * tr₁ n x`,

so in particular `markovTrace (-q) _ (signEquiv δ n x) = (-1) ^ n * markovTrace q hq x`. The
normalised trace `δ⁻¹ ^ n * tr n _` has no sign factor, since `(-δ)⁻¹ ^ n = (-1) ^ n * δ⁻¹ ^ n`,
and the trace radicals and trace-radical quotient towers at `δ` and `-δ` correspond under
`signEquiv` (`TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`,
`TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarAlgEquiv`).

For a negative real loop parameter `δ < 0` over `ℂ`, the unnormalised Markov trace itself cannot
be positive semidefinite (already on one strand `tr 1 1 = δ < 0`), and the positive semidefinite
sesquilinear forms are the signed trace forms `(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)`. Transporting
Jones's positivity theorem along `signStarAlgEquiv` shows that these signed forms are positive
semidefinite on every number of strands if and only if `-δ` belongs to
`TauCeti.TemperleyLieb.jonesLoopParameters`
(`TauCeti.TemperleyLieb.IsMarkovTrace.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff`,
`TauCeti.TemperleyLieb.markovTrace_neg_one_pow_nonneg_iff`). Equivalently, for every nonzero real
loop parameter `δ ≠ 0`, the normalised trace forms `δ⁻¹ ^ n * tr n (x⋆ * x)` are nonnegative on
every number of strands if and only if `|δ| ∈ jonesLoopParameters`
(`TauCeti.TemperleyLieb.IsMarkovTrace.forall_inv_pow_mul_map_star_mul_self_nonneg_iff`). At `δ = 0`
both hypotheses `0 < δ` and `δ < 0` are sharp: `tr (n + 1) = 0` for all `n`, so both the unsigned
and signed forms are nonnegative at every level even though `0 ∉ jonesLoopParameters`.

## Main definitions

* `TauCeti.TemperleyLieb.signEquiv`: the `R`-algebra isomorphism
  `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n` sending `e δ i` to `-e (-δ) i`.
* `TauCeti.TemperleyLieb.signStarAlgEquiv`: for self-adjoint `δ` and `-δ`, `signEquiv` bundled as a
  `⋆`-algebra equivalence.
* `TauCeti.TemperleyLieb.signPullbackTrace`: the signed pullback `(-1) ^ n • tr n ∘ signEquiv δ n`
  of a family of functionals from `-δ` to `δ`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarAlgEquiv`: the induced algebra and
  `⋆`-algebra equivalences between the trace-radical quotients at `δ` and `-δ`.

## Main results

* `TauCeti.TemperleyLieb.signEquiv_strandIncl`, `TauCeti.TemperleyLieb.aug_signEquiv`,
  `TauCeti.TemperleyLieb.signEquiv_jonesWenzl`: compatibility of `signEquiv` with strand inclusion,
  augmentation, and Jones–Wenzl projections.
* `TauCeti.TemperleyLieb.not_exists_algHom_map_e_eq`: when `2 * δ ≠ 0`, no `R`-algebra homomorphism
  `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2` fixes the generator.
* `TauCeti.TemperleyLieb.IsMarkovTrace.signPullback`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquiv`,
  `TauCeti.TemperleyLieb.markovTrace_neg_signEquiv`: the parity relation
  `tr₂ n (signEquiv δ n x) = (-1) ^ n * tr₁ n x` between Markov traces at `δ` and `-δ`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_signEquiv`: invariance of the normalised
  Markov trace `δ⁻¹ʳ ^ n * tr n _` under `signEquiv`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.comap_traceRadical_signEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv_quotientStrandIncl`: correspondence of
  trace radicals and quotient tower inclusions at `δ` and `-δ`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_neg_one_pow_nonneg_iff`: positivity of the signed Markov trace
  forms at `δ < 0` characterizes `-δ ∈ jonesLoopParameters`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_inv_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_inv_pow_nonneg_iff`: positivity of the normalised Markov trace
  forms at `δ ≠ 0` characterizes `|δ| ∈ jonesLoopParameters`.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Facts 4.4.14 (TB6), p. 155,
  for the sign `(-1) ^ n` relating the closure traces at `δ` and `-δ`.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.

The positivity theorems build on `TauCeti.TemperleyLieb.Positivity`, the analytic adjoint and its
uniqueness come from `TauCeti.TemperleyLieb.Star`, and the quotient tower transport builds on
`TauCeti.TemperleyLieb.Trace.Radical` and `TauCeti.TemperleyLieb.Trace.Star`.
-/

public section

namespace TauCeti.TemperleyLieb

section SignEquiv

variable {R : Type*} [CommRing R]

/-- The algebra map `TemperleyLieb R δ₁ n →ₐ[R] TemperleyLieb R δ₂ n` sending `e δ₁ i` to
`-e δ₂ i` whenever `δ₁ + δ₂ = 0`. -/
private def signLift {δ₁ δ₂ : R} (h : δ₁ + δ₂ = 0) (n : ℕ) :
    TemperleyLieb R δ₁ n →ₐ[R] TemperleyLieb R δ₂ n :=
  lift (fun i ↦ -e δ₂ i)
    (fun i ↦ by
      rw [neg_mul_neg, e_mul_self, eq_neg_of_add_eq_zero_left h, neg_smul_neg])
    (fun h' ↦ by
      rw [neg_mul_neg, mul_neg, e_mul_e_mul_e h'])
    (fun h' ↦ by
      rw [neg_mul_neg, neg_mul_neg, (commute_e h').eq])

/-- **The sign isomorphism** between Temperley–Lieb algebras at opposite loop parameters, sending
every generator `e δ i` to `-e (-δ) i`. -/
def signEquiv (δ : R) (n : ℕ) : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n :=
  AlgEquiv.ofAlgHom (signLift (add_neg_cancel δ) n) (signLift (neg_add_cancel δ) n)
    (hom_ext fun i ↦ by simp [signLift])
    (hom_ext fun i ↦ by simp [signLift])

variable {n : ℕ}

/-- The sign isomorphism negates every generator. -/
@[simp]
theorem signEquiv_e (δ : R) (i : Fin (n - 1)) :
    signEquiv δ n (e δ i) = -e (-δ) i := by
  simp [signEquiv, signLift]

/-- The inverse of the sign isomorphism negates every generator. -/
@[simp]
theorem signEquiv_symm_e (δ : R) (i : Fin (n - 1)) :
    (signEquiv δ n).symm (e (-δ) i) = -e δ i := by
  simp [signEquiv, signLift]

/-- `signEquiv` commutes with `algEquivOfEq`. -/
@[simp]
theorem algEquivOfEq_signEquiv {δ₁ δ₂ : R} (h : δ₁ = δ₂) (h' : -δ₁ = -δ₂ := congrArg Neg.neg h)
    (x : TemperleyLieb R δ₁ n) :
    algEquivOfEq h' n (signEquiv δ₁ n x) = signEquiv δ₂ n (algEquivOfEq h n x) :=
  AlgHom.congr_fun
    (hom_ext (F := (algEquivOfEq h' n).toAlgHom.comp (signEquiv δ₁ n).toAlgHom)
      (G := (signEquiv δ₂ n).toAlgHom.comp (algEquivOfEq h n).toAlgHom) fun i ↦ by simp) x

/-- Composing the sign isomorphisms at `δ` and `-δ` recovers the loop-congruence equivalence for
`- -δ = δ`: `signEquiv` is involutive across the two fibers. -/
@[simp]
theorem signEquiv_trans_signEquiv (δ : R) (n : ℕ) :
    (signEquiv δ n).trans (signEquiv (-δ) n) = algEquivOfEq (neg_neg δ).symm n :=
  AlgEquiv.ext fun x ↦ AlgHom.congr_fun
    (hom_ext (F := ((signEquiv δ n).trans (signEquiv (-δ) n)).toAlgHom)
      (G := (algEquivOfEq (neg_neg δ).symm n).toAlgHom) fun i ↦ by simp) x

/-- Applying `signEquiv` twice across the fibers `δ` and `-δ` gives `algEquivOfEq (neg_neg δ).symm`.
-/
@[simp]
theorem signEquiv_signEquiv (δ : R) (x : TemperleyLieb R δ n) :
    signEquiv (-δ) n (signEquiv δ n x) = algEquivOfEq (neg_neg δ).symm n x := by
  rw [← AlgEquiv.trans_apply, signEquiv_trans_signEquiv]

/-- The inverse of `signEquiv δ n` is `signEquiv (-δ) n` followed by `algEquivOfEq (neg_neg δ) n`.
-/
theorem signEquiv_symm_eq (δ : R) (n : ℕ) :
    (signEquiv δ n).symm = (signEquiv (-δ) n).trans (algEquivOfEq (neg_neg δ) n) :=
  AlgEquiv.ext fun x ↦ AlgHom.congr_fun
    (hom_ext (F := (signEquiv δ n).symm.toAlgHom)
      (G := ((signEquiv (-δ) n).trans (algEquivOfEq (neg_neg δ) n)).toAlgHom) fun i ↦ by simp) x

/-- The sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_strandIncl (δ : R) (x : TemperleyLieb R δ (n + 1)) :
    signEquiv δ (n + 2) (strandIncl x) = strandIncl (signEquiv δ (n + 1) x) :=
  AlgHom.congr_fun
    (hom_ext (F := (signEquiv δ (n + 2)).toAlgHom.comp strandIncl)
      (G := strandIncl.comp (signEquiv δ (n + 1)).toAlgHom) fun i ↦ by simp) x

/-- The inverse of the sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_symm_strandIncl (δ : R) (x : TemperleyLieb R (-δ) (n + 1)) :
    (signEquiv δ (n + 2)).symm (strandIncl x) = strandIncl ((signEquiv δ (n + 1)).symm x) :=
  AlgHom.congr_fun
    (hom_ext (F := (signEquiv δ (n + 2)).symm.toAlgHom.comp strandIncl)
      (G := strandIncl.comp (signEquiv δ (n + 1)).symm.toAlgHom) fun i ↦ by simp) x

/-- The sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_signEquiv (δ : R) (x : TemperleyLieb R δ n) :
    aug (signEquiv δ n x) = aug x :=
  AlgHom.congr_fun
    (hom_ext (F := aug.comp (signEquiv δ n).toAlgHom) (G := aug) fun i ↦ by simp) x

/-- The inverse of the sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_signEquiv_symm (δ : R) (x : TemperleyLieb R (-δ) n) :
    aug ((signEquiv δ n).symm x) = aug x :=
  AlgHom.congr_fun
    (hom_ext (F := aug.comp (signEquiv δ n).symm.toAlgHom) (G := aug) fun i ↦ by simp) x

/-- The sign isomorphism negates the cap-cup coefficient of a Kauffman-bracket crossing. -/
theorem signEquiv_crossing (δ α β : R) (i : Fin (n - 1)) :
    signEquiv δ n (crossing δ α β i) = crossing (-δ) α (-β) i := by
  simp [crossing_def, neg_smul]

open scoped Ring in
/-- Adjacent quantum-integer ratios negate when the loop parameter is negated: one of `[m + 1]` and
`[m + 2]` is fixed and the other changes sign. -/
private theorem qInt_neg_mul_inverse_qInt_neg (δ : R) (m : ℕ) :
    qInt R (-δ) (m + 1) * (qInt R (-δ) (m + 2))⁻¹ʳ =
      -(qInt R δ (m + 1) * (qInt R δ (m + 2))⁻¹ʳ) := by
  rw [qInt_neg, qInt_neg]
  rcases m.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h₁ : (-1 : R) ^ (k + k + 1 + 1) = 1 :=
      Even.neg_one_pow ⟨k + 1, by omega⟩
    have h₂ : (-1 : R) ^ (k + k + 2 + 1) = -1 :=
      Odd.neg_one_pow ⟨k + 1, by omega⟩
    rw [h₁, h₂, one_mul, neg_one_mul, Ring.inverse_neg, mul_neg]
  · have h₁ : (-1 : R) ^ (2 * k + 1 + 1 + 1) = -1 :=
      Odd.neg_one_pow ⟨k + 1, by omega⟩
    have h₂ : (-1 : R) ^ (2 * k + 1 + 2 + 1) = 1 :=
      Even.neg_one_pow ⟨k + 2, by omega⟩
    rw [h₁, h₂, neg_one_mul, one_mul, neg_mul]

/-- The sign isomorphism carries the Jones–Wenzl projection at `δ` to the Jones–Wenzl projection at
`-δ`, with no invertibility hypothesis on the quantum integers. -/
@[simp]
theorem signEquiv_jonesWenzl (δ : R) :
    ∀ n : ℕ, signEquiv δ n (jonesWenzl δ n) = jonesWenzl (-δ) n
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    rw [jonesWenzl_add_two, jonesWenzl_add_two, map_sub, map_smul, map_mul, map_mul,
      signEquiv_strandIncl, signEquiv_e, signEquiv_jonesWenzl δ (m + 1),
      qInt_neg_mul_inverse_qInt_neg, mul_neg, neg_mul, smul_neg, neg_smul]

/-- The inverse of the sign isomorphism carries the Jones–Wenzl projection at `-δ` to the
Jones–Wenzl projection at `δ`. -/
@[simp]
theorem signEquiv_symm_jonesWenzl (δ : R) (n : ℕ) :
    (signEquiv δ n).symm (jonesWenzl (-δ) n) = jonesWenzl δ n :=
  (signEquiv δ n).injective (by simp)

/-- When `2 * δ ≠ 0`, no `R`-algebra homomorphism on two strands from loop parameter `δ` to `-δ`
can fix the generator: `(e 0)² = δ • e 0` prevents `e δ 0 ↦ e (-δ) 0` without the minus sign. -/
theorem not_exists_algHom_map_e_eq {δ : R} (hδ : 2 * δ ≠ 0) :
    ¬∃ f : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2, f (e δ 0) = e (-δ) 0 := by
  rintro ⟨f, hf⟩
  have hsq : δ • e (-δ) (0 : Fin (2 - 1)) = (-δ) • e (-δ) (0 : Fin (2 - 1)) := by
    calc
      δ • e (-δ) 0 = f (δ • e δ 0) := by rw [map_smul, hf]
      _ = f (e δ 0 * e δ 0) := by rw [e_mul_self]
      _ = e (-δ) 0 * e (-δ) 0 := by rw [map_mul, hf]
      _ = (-δ) • e (-δ) 0 := e_mul_self 0
  have heq : δ = -δ := smul_left_injective_e_two (0 : Fin (2 - 1)) hsq
  exact hδ (by linear_combination heq)

end SignEquiv

section Star

variable {R : Type*} [CommRing R] [StarRing R] {n : ℕ}

/-- For self-adjoint `δ` and `-δ`, the sign isomorphism commutes with the analytic adjoint. -/
@[simp]
theorem signEquiv_star (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (x : TemperleyLieb R δ n) :
    signEquiv δ n (star x) = star (signEquiv δ n x) :=
  (map_star_iff (F := (signEquiv δ n).toAlgHom)).mpr (fun i ↦ by simp [IsSelfAdjoint]) x

/-- For self-adjoint `δ` and `-δ`, the inverse of the sign isomorphism commutes with the analytic
adjoint. -/
@[simp]
theorem signEquiv_symm_star (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (x : TemperleyLieb R (-δ) n) :
    (signEquiv δ n).symm (star x) = star ((signEquiv δ n).symm x) :=
  (map_star_iff (F := (signEquiv δ n).symm.toAlgHom)).mpr (fun i ↦ by simp [IsSelfAdjoint]) x

/-- **The sign `⋆`-isomorphism** between Temperley–Lieb algebras at opposite self-adjoint loop
parameters. -/
def signStarAlgEquiv (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))] (n : ℕ) :
    TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n :=
  StarAlgEquiv.ofAlgEquiv (signEquiv δ n) (signEquiv_star δ)

/-- Forgetting the `⋆`-structure on `signStarAlgEquiv` recovers `signEquiv`. -/
@[simp]
theorem signStarAlgEquiv_toAlgEquiv (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (n : ℕ) : (signStarAlgEquiv δ n).toAlgEquiv = signEquiv δ n := (rfl)

/-- `signStarAlgEquiv` evaluates as `signEquiv`. -/
@[simp]
theorem signStarAlgEquiv_apply (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (x : TemperleyLieb R δ n) : signStarAlgEquiv δ n x = signEquiv δ n x := (rfl)

/-- The inverse of `signStarAlgEquiv` evaluates as `(signEquiv δ n).symm`. -/
@[simp]
theorem signStarAlgEquiv_symm_apply (δ : R) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    (x : TemperleyLieb R (-δ) n) : (signStarAlgEquiv δ n).symm x = (signEquiv δ n).symm x := (rfl)

end Star

section MarkovTrace

variable {R : Type*} [CommRing R]

/-- The signed pullback `x ↦ (-1) ^ n • tr n (signEquiv δ n x)` of a family of linear functionals
at loop parameter `-δ` to a family at loop parameter `δ`. -/
def signPullbackTrace (δ : R) (tr : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R) (n : ℕ) :
    TemperleyLieb R δ n →ₗ[R] R :=
  (-1 : R) ^ n • (tr n).comp (signEquiv δ n).toLinearMap

/-- Evaluation of `signPullbackTrace`. -/
@[simp]
theorem signPullbackTrace_apply (δ : R) (tr : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R) (n : ℕ)
    (x : TemperleyLieb R δ n) :
    signPullbackTrace δ tr n x = (-1 : R) ^ n * tr n (signEquiv δ n x) := by
  simp [signPullbackTrace, smul_eq_mul]

namespace IsMarkovTrace

variable {δ : R} {tr₁ : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr₂ : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- Pulling back a Markov trace at `-δ` along `signEquiv δ n` with the parity sign `(-1) ^ n`
produces a Markov trace at `δ`. -/
theorem signPullback (htr₂ : IsMarkovTrace R (-δ) tr₂) :
    IsMarkovTrace R δ (signPullbackTrace δ tr₂) where
  map_one n := by
    rw [signPullbackTrace_apply, _root_.map_one (signEquiv δ n), htr₂.map_one, ← mul_pow,
      neg_one_mul, neg_neg]
  map_mul_comm n x y := by
    simp only [signPullbackTrace_apply, map_mul, htr₂.map_mul_comm]
  map_strandIncl n x := by
    rw [signPullbackTrace_apply, signPullbackTrace_apply, signEquiv_strandIncl,
      htr₂.map_strandIncl, pow_succ (-1 : R) (n + 1)]
    ring
  map_strandIncl_mul_e_last n x := by
    rw [signPullbackTrace_apply, signPullbackTrace_apply, map_mul, signEquiv_strandIncl,
      signEquiv_e, mul_neg, map_neg, htr₂.map_strandIncl_mul_e_last, pow_succ (-1 : R) (n + 1)]
    ring

/-- Any Markov trace at `δ` equals the signed pullback of any Markov trace at `-δ`. -/
theorem eq_signPullbackTrace (htr₁ : IsMarkovTrace R δ tr₁) (htr₂ : IsMarkovTrace R (-δ) tr₂) :
    tr₁ = signPullbackTrace δ tr₂ :=
  htr₁.unique htr₂.signPullback

/-- A Markov trace at `δ` differs from a Markov trace at `-δ` composed with `signEquiv` by the
factor `(-1) ^ n` on `n` strands. -/
theorem apply_eq_neg_one_pow_mul_map_signEquiv (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ) (x : TemperleyLieb R δ n) :
    tr₁ n x = (-1 : R) ^ n * tr₂ n (signEquiv δ n x) := by
  simpa using LinearMap.congr_fun (congrFun (htr₁.eq_signPullbackTrace htr₂) n) x

/-- **Markov trace parity under the sign isomorphism.** On `n` strands, `signEquiv` multiplies the
Markov trace by `(-1) ^ n`. -/
theorem map_signEquiv (htr₁ : IsMarkovTrace R δ tr₁) (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ)
    (x : TemperleyLieb R δ n) :
    tr₂ n (signEquiv δ n x) = (-1 : R) ^ n * tr₁ n x := by
  rw [htr₁.apply_eq_neg_one_pow_mul_map_signEquiv htr₂ n x, ← mul_assoc, ← mul_pow,
    neg_mul_neg, one_mul, one_pow, one_mul]

/-- Evaluating a Markov trace at `δ` along `(signEquiv δ n).symm` multiplies a Markov trace at `-δ`
by `(-1) ^ n`. -/
theorem map_signEquiv_symm (htr₁ : IsMarkovTrace R δ tr₁) (htr₂ : IsMarkovTrace R (-δ) tr₂)
    (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    tr₁ n ((signEquiv δ n).symm x) = (-1 : R) ^ n * tr₂ n x := by
  simpa using htr₁.apply_eq_neg_one_pow_mul_map_signEquiv htr₂ n ((signEquiv δ n).symm x)

open scoped Ring in
/-- **Invariance of the normalised Markov trace under `signEquiv`.** Scaling by `δ⁻¹ʳ ^ n` absorbs
the parity factor `(-1) ^ n`, with no unit hypothesis on `δ`. -/
theorem inverse_pow_mul_map_signEquiv (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ) (x : TemperleyLieb R δ n) :
    ((-δ)⁻¹ʳ) ^ n * tr₂ n (signEquiv δ n x) = (δ⁻¹ʳ) ^ n * tr₁ n x := by
  rw [Ring.inverse_neg, htr₁.map_signEquiv htr₂ n x, ← mul_assoc, ← mul_pow,
    neg_mul_neg, mul_one]

open scoped Ring in
/-- At a self-adjoint loop parameter, the normalised Hermitian square `δ⁻¹ʳ ^ n * tr n (x⋆ * x)` is
invariant under `signEquiv`. -/
theorem inverse_pow_mul_map_star_mul_self_signEquiv [StarRing R] [Fact (IsSelfAdjoint δ)]
    [Fact (IsSelfAdjoint (-δ))] (htr₁ : IsMarkovTrace R δ tr₁) (htr₂ : IsMarkovTrace R (-δ) tr₂)
    (n : ℕ) (x : TemperleyLieb R δ n) :
    ((-δ)⁻¹ʳ) ^ n * tr₂ n (star (signEquiv δ n x) * signEquiv δ n x) =
      (δ⁻¹ʳ) ^ n * tr₁ n (star x * x) := by
  rw [← signEquiv_star, ← map_mul, htr₁.inverse_pow_mul_map_signEquiv htr₂]

/-- Over a field, the normalised Markov trace `δ⁻¹ ^ n * tr n _` is invariant under `signEquiv`. -/
theorem inv_pow_mul_map_signEquiv {K : Type*} [Field K] {δ : K}
    {tr₁ : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    {tr₂ : ∀ n : ℕ, TemperleyLieb K (-δ) n →ₗ[K] K}
    (htr₁ : IsMarkovTrace K δ tr₁) (htr₂ : IsMarkovTrace K (-δ) tr₂) (n : ℕ)
    (x : TemperleyLieb K δ n) :
    ((-δ)⁻¹) ^ n * tr₂ n (signEquiv δ n x) = (δ⁻¹) ^ n * tr₁ n x := by
  simpa only [Ring.inverse_eq_inv] using htr₁.inverse_pow_mul_map_signEquiv htr₂ n x

/-- Over a star field, the normalised Hermitian square `δ⁻¹ ^ n * tr n (x⋆ * x)` is invariant
under `signEquiv`. -/
theorem inv_pow_mul_map_star_mul_self_signEquiv {K : Type*} [Field K] [StarRing K] {δ : K}
    [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr₁ : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    {tr₂ : ∀ n : ℕ, TemperleyLieb K (-δ) n →ₗ[K] K}
    (htr₁ : IsMarkovTrace K δ tr₁) (htr₂ : IsMarkovTrace K (-δ) tr₂) (n : ℕ)
    (x : TemperleyLieb K δ n) :
    ((-δ)⁻¹) ^ n * tr₂ n (star (signEquiv δ n x) * signEquiv δ n x) =
      (δ⁻¹) ^ n * tr₁ n (star x * x) := by
  simpa only [Ring.inverse_eq_inv] using
    htr₁.inverse_pow_mul_map_star_mul_self_signEquiv htr₂ n x

end IsMarkovTrace

/-- If `q` is a spin parameter for the loop value `δ = -(q + q⁻¹)`, then `-q` is a spin parameter
for the opposite loop value `-δ`. -/
theorem neg_eq_neg_add_inv_neg {q : Rˣ} {δ : R} (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) :
    -δ = -(((-q : Rˣ) : R) + (((-q : Rˣ)⁻¹ : Rˣ) : R)) := by
  rw [hδ, Units.val_neg, inv_neg, Units.val_neg]
  ring

/-- **Spin-model Markov trace under the sign isomorphism.** Replacing the spin parameter `q` by `-q`
and applying `signEquiv` multiplies `markovTrace` by `(-1) ^ n` on `n` strands. -/
@[simp]
theorem markovTrace_neg_signEquiv {q : Rˣ} {δ : R} (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace (-q) (neg_eq_neg_add_inv_neg hδ) (signEquiv δ n x) =
      (-1 : R) ^ n * markovTrace q hδ x :=
  (isMarkovTrace_markovTrace q hδ).map_signEquiv
    (isMarkovTrace_markovTrace (-q) (neg_eq_neg_add_inv_neg hδ)) n x

/-- Expressing `markovTrace` at `(q, δ)` in terms of `markovTrace` at `(-q, -δ)` via `signEquiv`. -/
theorem markovTrace_eq_neg_one_pow_mul_markovTrace_neg {q : Rˣ} {δ : R}
    (hδ : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace q hδ x =
      (-1 : R) ^ n * markovTrace (-q) (neg_eq_neg_add_inv_neg hδ) (signEquiv δ n x) :=
  (isMarkovTrace_markovTrace q hδ).apply_eq_neg_one_pow_mul_map_signEquiv
    (isMarkovTrace_markovTrace (-q) (neg_eq_neg_add_inv_neg hδ)) n x

end MarkovTrace

section TraceRadical

namespace IsMarkovTrace

variable {R : Type*} [CommRing R] {δ : R}
  {tr₁ : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr₂ : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- The sign isomorphism pulls back the trace radical at `-δ` onto the trace radical at `δ`. -/
theorem comap_traceRadical_signEquiv (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ) :
    Ideal.comap (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
        ((tr₂ n).traceRadical (htr₂.map_mul_comm n)) =
      (tr₁ n).traceRadical (htr₁.map_mul_comm n) := by
  ext x
  simp only [Ideal.mem_comap, RingHom.coe_coe, LinearMap.mem_traceRadical]
  refine ⟨fun hx y ↦ ?_, fun hx y ↦ ?_⟩
  · have h := hx (signEquiv δ n y)
    rw [← map_mul, htr₁.map_signEquiv htr₂, (isUnit_one.neg.pow n).mul_right_eq_zero] at h
    exact h
  · obtain ⟨y, rfl⟩ := (signEquiv δ n).surjective y
    rw [← map_mul, htr₁.map_signEquiv htr₂, hx y, mul_zero]

/-- Membership in the trace radical is preserved and reflected by `signEquiv`. -/
theorem signEquiv_mem_traceRadical_iff (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquiv δ n x ∈ (tr₂ n).traceRadical (htr₂.map_mul_comm n) ↔
      x ∈ (tr₁ n).traceRadical (htr₁.map_mul_comm n) := by
  rw [← htr₁.comap_traceRadical_signEquiv htr₂ n]
  rfl

/-- Pushing forward the trace radical at `δ` along `signEquiv` gives the trace radical at `-δ`. -/
theorem map_traceRadical_signEquiv (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ) :
    Ideal.map (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
        ((tr₁ n).traceRadical (htr₁.map_mul_comm n)) =
      (tr₂ n).traceRadical (htr₂.map_mul_comm n) := by
  rw [← htr₁.comap_traceRadical_signEquiv htr₂ n]
  exact Ideal.map_comap_of_surjective
    (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n) (signEquiv δ n).surjective _

/-- The `R`-algebra isomorphism between the trace-radical quotients at `δ` and `-δ` induced by
`signEquiv`. -/
def quotientSignEquiv (htr₁ : IsMarkovTrace R δ tr₁) (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr₁ n).traceRadical (htr₁.map_mul_comm n)) ≃ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr₂ n).traceRadical (htr₂.map_mul_comm n)) :=
  Ideal.quotientEquivAlg ((tr₁ n).traceRadical (htr₁.map_mul_comm n))
    ((tr₂ n).traceRadical (htr₂.map_mul_comm n)) (signEquiv δ n)
    (htr₁.map_traceRadical_signEquiv htr₂ n).symm

/-- `quotientSignEquiv` acts on quotient classes via `signEquiv`. -/
@[simp]
theorem quotientSignEquiv_mk (htr₁ : IsMarkovTrace R δ tr₁) (htr₂ : IsMarkovTrace R (-δ) tr₂)
    (n : ℕ) (x : TemperleyLieb R δ n) :
    htr₁.quotientSignEquiv htr₂ n
        (Ideal.Quotient.mk ((tr₁ n).traceRadical (htr₁.map_mul_comm n)) x) =
      Ideal.Quotient.mk ((tr₂ n).traceRadical (htr₂.map_mul_comm n)) (signEquiv δ n x) :=
  (rfl)

/-- The inverse of `quotientSignEquiv` acts on quotient classes via `(signEquiv δ n).symm`. -/
@[simp]
theorem quotientSignEquiv_symm_mk (htr₁ : IsMarkovTrace R δ tr₁) (htr₂ : IsMarkovTrace R (-δ) tr₂)
    (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    (htr₁.quotientSignEquiv htr₂ n).symm
        (Ideal.Quotient.mk ((tr₂ n).traceRadical (htr₂.map_mul_comm n)) x) =
      Ideal.Quotient.mk ((tr₁ n).traceRadical (htr₁.map_mul_comm n)) ((signEquiv δ n).symm x) :=
  (rfl)

/-- `quotientSignEquiv` intertwines the quotient tower strand inclusions at `δ` and `-δ`. -/
@[simp]
theorem quotientSignEquiv_quotientStrandIncl (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ)
    (x : TemperleyLieb R δ (n + 1) ⧸ (tr₁ (n + 1)).traceRadical (htr₁.map_mul_comm (n + 1))) :
    htr₁.quotientSignEquiv htr₂ (n + 2) (htr₁.quotientStrandIncl n x) =
      htr₂.quotientStrandIncl n (htr₁.quotientSignEquiv htr₂ (n + 1) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- `quotientSignEquiv` intertwines the quotient traces up to the parity sign `(-1) ^ n`. -/
@[simp]
theorem quotientTrace_quotientSignEquiv (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ)
    (x : TemperleyLieb R δ n ⧸ (tr₁ n).traceRadical (htr₁.map_mul_comm n)) :
    (tr₂ n).quotientTrace (htr₂.map_mul_comm n) (htr₁.quotientSignEquiv htr₂ n x) =
      (-1 : R) ^ n * (tr₁ n).quotientTrace (htr₁.map_mul_comm n) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [htr₁.map_signEquiv htr₂]

section Star

variable [StarRing R] [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]

/-- For self-adjoint `δ` and `-δ`, `quotientSignEquiv` preserves the quotient star structure. -/
@[simp]
theorem quotientSignEquiv_star (htr₁ : IsMarkovTrace R δ tr₁) (htr₂ : IsMarkovTrace R (-δ) tr₂)
    (n : ℕ) [((tr₁ n).traceRadical (htr₁.map_mul_comm n)).IsStar]
    [((tr₂ n).traceRadical (htr₂.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n ⧸ (tr₁ n).traceRadical (htr₁.map_mul_comm n)) :
    htr₁.quotientSignEquiv htr₂ n (star x) = star (htr₁.quotientSignEquiv htr₂ n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- **The `⋆`-algebra isomorphism between trace-radical quotients** at opposite self-adjoint loop
parameters. -/
def quotientSignStarAlgEquiv (htr₁ : IsMarkovTrace R δ tr₁) (htr₂ : IsMarkovTrace R (-δ) tr₂)
    (n : ℕ) [((tr₁ n).traceRadical (htr₁.map_mul_comm n)).IsStar]
    [((tr₂ n).traceRadical (htr₂.map_mul_comm n)).IsStar] :
    (TemperleyLieb R δ n ⧸ (tr₁ n).traceRadical (htr₁.map_mul_comm n)) ≃⋆ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr₂ n).traceRadical (htr₂.map_mul_comm n)) :=
  StarAlgEquiv.ofAlgEquiv (htr₁.quotientSignEquiv htr₂ n) (htr₁.quotientSignEquiv_star htr₂ n)

/-- Forgetting the `⋆`-structure on `quotientSignStarAlgEquiv` recovers `quotientSignEquiv`. -/
@[simp]
theorem quotientSignStarAlgEquiv_toAlgEquiv (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ)
    [((tr₁ n).traceRadical (htr₁.map_mul_comm n)).IsStar]
    [((tr₂ n).traceRadical (htr₂.map_mul_comm n)).IsStar] :
    (htr₁.quotientSignStarAlgEquiv htr₂ n).toAlgEquiv = htr₁.quotientSignEquiv htr₂ n := (rfl)

/-- `quotientSignStarAlgEquiv` evaluates as `quotientSignEquiv`. -/
@[simp]
theorem quotientSignStarAlgEquiv_apply (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ)
    [((tr₁ n).traceRadical (htr₁.map_mul_comm n)).IsStar]
    [((tr₂ n).traceRadical (htr₂.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n ⧸ (tr₁ n).traceRadical (htr₁.map_mul_comm n)) :
    htr₁.quotientSignStarAlgEquiv htr₂ n x = htr₁.quotientSignEquiv htr₂ n x := (rfl)

/-- The inverse of `quotientSignStarAlgEquiv` evaluates as `(quotientSignEquiv _ _ _).symm`. -/
@[simp]
theorem quotientSignStarAlgEquiv_symm_apply (htr₁ : IsMarkovTrace R δ tr₁)
    (htr₂ : IsMarkovTrace R (-δ) tr₂) (n : ℕ)
    [((tr₁ n).traceRadical (htr₁.map_mul_comm n)).IsStar]
    [((tr₂ n).traceRadical (htr₂.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R (-δ) n ⧸ (tr₂ n).traceRadical (htr₂.map_mul_comm n)) :
    (htr₁.quotientSignStarAlgEquiv htr₂ n).symm x =
      (htr₁.quotientSignEquiv htr₂ n).symm x := (rfl)

end Star

end IsMarkovTrace

end TraceRadical

section Positivity

open Real
open scoped ComplexOrder

namespace IsMarkovTrace

variable {δ : ℝ} {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

/-- The `⋆`-preserving algebra equivalence between the complex Temperley–Lieb fiber at the real
parameter `-δ` and the fiber at `δ`, obtained by composing `algEquivOfEq (Complex.ofReal_neg δ)`
with `(signEquiv (δ : ℂ) n).symm`. -/
private def complexNegEquiv (δ : ℝ) (n : ℕ) :
    TemperleyLieb ℂ ((-δ : ℝ) : ℂ) n ≃ₐ[ℂ] TemperleyLieb ℂ (δ : ℂ) n :=
  (algEquivOfEq (Complex.ofReal_neg δ) n).trans (signEquiv (δ : ℂ) n).symm

/-- The Markov trace on `TemperleyLieb ℂ ((-δ : ℝ) : ℂ)` obtained from `tr` by signed pullback
along `complexNegEquiv`. -/
private def complexNegTrace (δ : ℝ) (tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ) (n : ℕ) :
    TemperleyLieb ℂ ((-δ : ℝ) : ℂ) n →ₗ[ℂ] ℂ :=
  (-1 : ℂ) ^ n • (tr n).comp (complexNegEquiv δ n).toLinearMap

private theorem isMarkovTrace_complexNegTrace (htr : IsMarkovTrace ℂ (δ : ℂ) tr) :
    IsMarkovTrace ℂ ((-δ : ℝ) : ℂ) (complexNegTrace δ tr) := by
  have h1 : IsMarkovTrace ℂ (- -(δ : ℂ))
      (fun n ↦ (tr n).comp (algEquivOfEq (neg_neg (δ : ℂ)) n).toLinearMap) :=
    htr.comp_algEquivOfEq (neg_neg (δ : ℂ))
  have h2 : IsMarkovTrace ℂ (-(δ : ℂ)) (signPullbackTrace (-(δ : ℂ))
      (fun n ↦ (tr n).comp (algEquivOfEq (neg_neg (δ : ℂ)) n).toLinearMap)) :=
    h1.signPullback
  have h3 := h2.comp_algEquivOfEq (Complex.ofReal_neg δ)
  refine IsMarkovTrace.mk (fun n ↦ ?_) (fun n x y ↦ ?_) (fun n x ↦ ?_) (fun n x ↦ ?_)
  · simpa [complexNegTrace, complexNegEquiv, signEquiv_symm_eq, smul_eq_mul] using h3.map_one n
  · simpa [complexNegTrace, complexNegEquiv, signEquiv_symm_eq, smul_eq_mul] using
      h3.map_mul_comm n x y
  · simpa [complexNegTrace, complexNegEquiv, signEquiv_symm_eq, smul_eq_mul] using
      h3.map_strandIncl n x
  · simpa [complexNegTrace, complexNegEquiv, signEquiv_symm_eq, smul_eq_mul] using
      h3.map_strandIncl_mul_e_last n x

variable [Fact (IsSelfAdjoint (δ : ℂ))]

/-- At loop parameter `δ = 0`, both the unsigned and parity-signed Hermitian forms of any Markov
trace over `ℂ` are nonnegative on every number of strands: on zero strands `TL_0(ℂ, 0) ≅ ℂ` gives
`‖aug x‖² ≥ 0`, and on a positive number of strands the Markov trace vanishes identically. This
shows that `0 < δ` in `forall_map_star_mul_self_nonneg_iff` and `δ < 0` in
`forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff` cannot be weakened to `0 ≤ δ` or `δ ≤ 0`. -/
theorem map_star_mul_self_nonneg_and_neg_one_pow_nonneg_of_loop_zero
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ = 0) (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    0 ≤ tr n (star x * x) ∧ 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x) := by
  obtain _ | n := n
  · have htr0 (z : TemperleyLieb ℂ (δ : ℂ) 0) : tr 0 z = aug z := by
      have hz : z = aug z • 1 := by
        simpa [Algebra.algebraMap_eq_smul_one] using
          ((algEquivOfLeOne (δ : ℂ) (Nat.zero_le 1)).symm_apply_apply z).symm
      conv_lhs => rw [hz]
      rw [map_smul, htr.map_one, pow_zero, smul_eq_mul, mul_one]
    rw [htr0, map_mul, aug_star, pow_zero, one_mul, and_self]
    exact star_mul_self_nonneg (aug x)
  · have h0 : (δ : ℂ) = 0 := by simp [hδ]
    have htr' : IsMarkovTrace ℂ (0 : ℂ)
        (fun m ↦ (tr m).comp (algEquivOfEq h0.symm m).toLinearMap) :=
      htr.comp_algEquivOfEq h0.symm
    have hzero : tr (n + 1) (star x * x) = 0 := by
      simpa using LinearMap.congr_fun (htr'.eq_zero_succ n) (algEquivOfEq h0 (n + 1) (star x * x))
    simp [hzero]

private theorem complexNegEquiv_star [Fact (IsSelfAdjoint ((-δ : ℝ) : ℂ))] (n : ℕ)
    (y : TemperleyLieb ℂ ((-δ : ℝ) : ℂ) n) :
    complexNegEquiv δ n (star y) = star (complexNegEquiv δ n y) := by
  have : Fact (IsSelfAdjoint (-(δ : ℂ))) := ⟨(Fact.out : IsSelfAdjoint (δ : ℂ)).neg⟩
  simp [complexNegEquiv]

private theorem complexNegTrace_star_mul_self [Fact (IsSelfAdjoint ((-δ : ℝ) : ℂ))] (n : ℕ)
    (y : TemperleyLieb ℂ ((-δ : ℝ) : ℂ) n) :
    complexNegTrace δ tr n (star y * y) =
      (-1 : ℂ) ^ n * tr n (star (complexNegEquiv δ n y) * complexNegEquiv δ n y) := by
  simp [complexNegTrace, smul_eq_mul, complexNegEquiv_star]

/-- **Failure of signed positivity from level `k` on.** Let `δ < 0` with `-δ ∉ jonesLoopParameters`
and `k = ⌊π / arccos (-δ / 2)⌋`. On every number `n ≥ k` of strands the signed Hermitian form
`(-1) ^ n * tr n (x⋆ * x)` takes a strictly negative value. -/
theorem exists_neg_one_pow_mul_map_star_mul_self_neg (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) (hδJ : -δ ∉ jonesLoopParameters) {n : ℕ} (hn : ⌊π / arccos (-δ / 2)⌋₊ ≤ n) :
    ∃ x : TemperleyLieb ℂ (δ : ℂ) n, (-1 : ℂ) ^ n * tr n (star x * x) < 0 := by
  have : Fact (IsSelfAdjoint ((-δ : ℝ) : ℂ)) := ⟨Complex.conj_ofReal (-δ)⟩
  obtain ⟨y, hy⟩ := (isMarkovTrace_complexNegTrace htr).exists_map_star_mul_self_neg
    (neg_pos.mpr hδ) hδJ hn
  exact ⟨complexNegEquiv δ n y, by rwa [← complexNegTrace_star_mul_self]⟩

/-- **Jones's restriction at negative loop parameters.** If `δ < 0` and the signed Hermitian forms
`(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` are positive semidefinite on every number of strands, then
`-δ` belongs to `jonesLoopParameters`. -/
theorem mem_jonesLoopParameters_neg_of_forall_neg_one_pow_mul_nonneg
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ < 0)
    (h : ∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) :
    -δ ∈ jonesLoopParameters := by
  by_contra hδJ
  obtain ⟨x, hx⟩ := htr.exists_neg_one_pow_mul_map_star_mul_self_neg hδ hδJ le_rfl
  exact (h _ x).not_gt hx

/-- At a negative loop parameter `δ < 0` with `-δ ∉ jonesLoopParameters`, the signed Hermitian form
on `n` strands can be positive semidefinite only below level `⌊π / arccos (-δ / 2)⌋`. -/
theorem lt_floor_of_forall_neg_one_pow_mul_nonneg (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ < 0)
    (hδJ : -δ ∉ jonesLoopParameters) {n : ℕ}
    (h : ∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) :
    n < ⌊π / arccos (-δ / 2)⌋₊ := by
  by_contra hn
  obtain ⟨x, hx⟩ := htr.exists_neg_one_pow_mul_map_star_mul_self_neg hδ hδJ (not_lt.1 hn)
  exact (h x).not_gt hx

/-- **Positivity at negative loop parameters** for an arbitrary Markov trace. For `δ < 0`, the
signed Hermitian forms `(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` are positive semidefinite on every
number of strands if and only if `-δ ∈ jonesLoopParameters`. -/
theorem forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ (-1 : ℂ) ^ n * tr n (star x * x)) ↔
      -δ ∈ jonesLoopParameters := by
  have : Fact (IsSelfAdjoint ((-δ : ℝ) : ℂ)) := ⟨Complex.conj_ofReal (-δ)⟩
  rw [← (isMarkovTrace_complexNegTrace htr).forall_map_star_mul_self_nonneg_iff (neg_pos.mpr hδ)]
  refine forall_congr' fun n ↦ ⟨fun h y ↦ ?_, fun h x ↦ ?_⟩
  · rw [complexNegTrace_star_mul_self]
    exact h (complexNegEquiv δ n y)
  · obtain ⟨y, rfl⟩ := (complexNegEquiv δ n).surjective x
    rw [← complexNegTrace_star_mul_self]
    exact h y

/-- Multiplying a complex number by a positive real scalar preserves nonnegativity in
`ComplexOrder`. -/
private theorem complex_ofReal_mul_nonneg_iff {r : ℝ} (hr : 0 < r) {z : ℂ} :
    0 ≤ (r : ℂ) * z ↔ 0 ≤ z := by
  constructor
  · intro hz
    have hrinv : (0 : ℂ) ≤ ((r⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.mpr (inv_nonneg.mpr hr.le)
    have h := mul_nonneg hrinv hz
    rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one,
      one_mul] at h
  · exact mul_nonneg (Complex.zero_le_real.mpr hr.le)

/-- **Unified positivity theorem for the normalised Markov trace.** For any nonzero real loop
parameter `δ ≠ 0`, the normalised Hermitian forms `(x, y) ↦ δ⁻¹ ^ n * tr n (x⋆ * y)` are positive
semidefinite on every number of strands if and only if `|δ| ∈ jonesLoopParameters`. -/
theorem forall_inv_pow_mul_map_star_mul_self_nonneg_iff (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ≠ 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ ((δ : ℂ)⁻¹) ^ n * tr n (star x * x)) ↔
      |δ| ∈ jonesLoopParameters := by
  rcases hδ.lt_or_gt with hneg | hpos
  · rw [abs_of_neg hneg, ← htr.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hneg]
    refine forall_congr' fun n ↦ forall_congr' fun x ↦ ?_
    have hpow : ((δ : ℂ)⁻¹) ^ n = ((((-δ)⁻¹) ^ n : ℝ) : ℂ) * (-1 : ℂ) ^ n := by
      have hd : (δ : ℂ)⁻¹ = (((-δ)⁻¹ : ℝ) : ℂ) * (-1 : ℂ) := by
        push_cast
        rw [inv_neg, mul_neg_one, neg_neg]
      rw [hd, mul_pow, ← Complex.ofReal_pow]
    rw [hpow, mul_assoc]
    exact complex_ofReal_mul_nonneg_iff (pow_pos (inv_pos.mpr (neg_pos.mpr hneg)) n)
  · rw [abs_of_pos hpos, ← htr.forall_map_star_mul_self_nonneg_iff hpos]
    refine forall_congr' fun n ↦ forall_congr' fun x ↦ ?_
    have hpow : ((δ : ℂ)⁻¹) ^ n = (((δ⁻¹) ^ n : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hpow]
    exact complex_ofReal_mul_nonneg_iff (pow_pos (inv_pos.mpr hpos) n)

end IsMarkovTrace

/-- **Positivity at negative loop parameters** for the spin-model Markov trace. Let `δ < 0` and let
`q` be a unit with `δ = -(q + q⁻¹)`. Then `(-1) ^ n * markovTrace q hq (x⋆ * x)` is real and
nonnegative for every number of strands `n` and every `x` if and only if `-δ` belongs to
`jonesLoopParameters`, that is, `-δ = 2 cos (π / m)` for some `m ≥ 3` or `-δ ≥ 2`. -/
theorem markovTrace_neg_one_pow_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ < 0)
    (q : ℂˣ) (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (-1 : ℂ) ^ n * markovTrace q hq (star x * x)) ↔
      -δ ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hδ

/-- **Positivity of the normalised spin-model Markov trace at any nonzero real loop parameter.**
For `δ ≠ 0` and `δ = -(q + q⁻¹)`, the normalised trace forms
`δ⁻¹ ^ n * markovTrace q hq (x⋆ * x)` are real and nonnegative for every `n` and `x` if and only if
`|δ| ∈ jonesLoopParameters`. -/
theorem markovTrace_inv_pow_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ ≠ 0)
    (q : ℂˣ) (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ ((δ : ℂ)⁻¹) ^ n * markovTrace q hq (star x * x)) ↔
      |δ| ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_inv_pow_mul_map_star_mul_self_nonneg_iff hδ

end Positivity

end TauCeti.TemperleyLieb
