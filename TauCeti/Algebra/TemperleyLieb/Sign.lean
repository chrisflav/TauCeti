/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star

/-!
# The sign isomorphism of the Temperley–Lieb algebra

Negating every generator of the Temperley–Lieb algebra negates the loop value: if
`e i * e i = δ e i` then `(-e i) * (-e i) = (-δ) (-e i)`, while both the cubic zig-zag relation
`(-e i) * (-e j) * (-e i) = -e i` and distant commutation `(-e i) * (-e j) = (-e j) * (-e i)` are
preserved. Over every commutative ring `R`, the universal property therefore gives a canonical
algebra isomorphism `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n` sending `e δ i` to
`-e (-δ) i`.

This sign isomorphism cannot fix the generators unless `2 * δ = 0`: any algebra map
`TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R δ' 2` sending the generator to the generator forces
`δ = δ'` (`TauCeti.TemperleyLieb.eq_of_map_e_eq`). Despite negating the generators, the sign
isomorphism fixes every Jones–Wenzl projection (`TauCeti.TemperleyLieb.signEquiv_jonesWenzl`),
because Wenzl's recursion multiplies `e (Fin.last m)` by `[m + 1] / [m + 2]`, whose sign also flips
under `δ ↦ -δ` (`TauCeti.qInt_neg_left`).

At a self-adjoint loop parameter, `-e (-δ) i` is still self-adjoint, so the sign isomorphism
commutes with the analytic adjoint and upgrades to a star-algebra equivalence
`TauCeti.TemperleyLieb.signStarAlgEquiv`.

On traces, the sign isomorphism does *not* preserve the unnormalized Markov trace directly: closing
`n` straight strands at `-δ` gives `(-δ) ^ n = (-1) ^ n * δ ^ n`, and capping the added strand with
`e (-δ) (Fin.last n) = -signEquiv δ (e δ (Fin.last n))` introduces a minus sign that matches the
passage from `(-1) ^ (n + 2)` to `(-1) ^ (n + 1)`. Thus scaling degree `n` by `(-1) ^ n` transports
an unnormalized Markov trace at `δ` to one at `-δ`
(`TauCeti.TemperleyLieb.IsMarkovTrace.signTrace`). By uniqueness of Markov traces, every Markov
trace `tr'` at `-δ` satisfies `tr' n (signEquiv δ x) = (-1) ^ n * tr n x`
(`TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquiv`),
while the normalized trace `δ⁻ⁿ • tr n` is strictly invariant on the nose
(`TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_signEquiv`). Consequently the trace
radicals correspond under `signEquiv`, and the trace-radical quotients are isomorphic as towers of
(star) algebras (`TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`,
`TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarAlgEquiv`).

## Main definitions

* `TauCeti.TemperleyLieb.signEquiv`: the algebra isomorphism
  `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n` sending `e δ i` to `-e (-δ) i`.
* `TauCeti.TemperleyLieb.signStarAlgEquiv`: the upgraded star-algebra isomorphism at a
  self-adjoint loop parameter.
* `TauCeti.TemperleyLieb.signTrace`: transport of a family of linear functionals from `δ` to `-δ`
  with sign `(-1) ^ n` on `n` strands.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarAlgEquiv`: the induced algebra and
  star-algebra isomorphisms between the trace-radical quotients at `δ` and `-δ`.

## Main results

* `TauCeti.TemperleyLieb.eq_of_map_e_eq`, `TauCeti.TemperleyLieb.two_mul_eq_zero_of_map_e_eq`:
  an algebra map on two strands fixing the generator forces equality of loop parameters, so no
  generator-fixing isomorphism between `δ` and `-δ` exists when `2 * δ ≠ 0`.
* `TauCeti.TemperleyLieb.signEquiv_strandIncl`, `TauCeti.TemperleyLieb.aug_signEquiv`,
  `TauCeti.TemperleyLieb.signEquiv_jonesWenzl`: compatibility of `signEquiv` with strand inclusion,
  augmentation, and Jones–Wenzl projections.
* `TauCeti.TemperleyLieb.IsMarkovTrace.signTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquiv`,
  `TauCeti.TemperleyLieb.markovTrace_neg_signEquiv`: Markov trace transport with factor `(-1) ^ n`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_signEquiv`: exact invariance of the
  normalized Markov trace `δ⁻ⁿ • tr n`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.comap_traceRadical_signEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv_quotientStrandIncl`: exact correspondence
  of trace radicals and compatibility of the quotient isomorphism with the tower inclusions.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Facts 4.4.14 (TB6).
-/

public section

namespace TauCeti.TemperleyLieb

section ParameterRecovery

/-- On two strands, an algebra map taking the generator to the generator forces the loop parameters
to coincide. -/
theorem eq_of_map_e_eq {R : Type*} [CommSemiring R] {δ δ' : R}
    (F : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R δ' 2) (i : Fin (2 - 1))
    (hF : F (e δ i) = e δ' i) : δ = δ' := by
  apply smul_left_injective_e_two (δ := δ') i
  calc
    δ • e δ' i = F (δ • e δ i) := by rw [map_smul, hF]
    _ = F (e δ i * e δ i) := by rw [e_mul_self]
    _ = e δ' i * e δ' i := by rw [map_mul, hF]
    _ = δ' • e δ' i := e_mul_self i

/-- An algebra map from `TemperleyLieb R δ 2` to `TemperleyLieb R (-δ) 2` cannot fix the generator
unless `2 * δ = 0`. -/
theorem two_mul_eq_zero_of_map_e_eq {R : Type*} [CommRing R] {δ : R}
    (F : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2) (i : Fin (2 - 1))
    (hF : F (e δ i) = e (-δ) i) : 2 * δ = 0 := by
  have h := eq_of_map_e_eq F i hF
  rw [two_mul]
  conv_rhs => rw [← add_neg_cancel δ]
  rw [← h]

/-- When `2 * δ ≠ 0`, no algebra map `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2` fixes the
generator. -/
theorem map_e_ne_e_neg {R : Type*} [CommRing R] {δ : R} (hδ : 2 * δ ≠ 0)
    (F : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2) (i : Fin (2 - 1)) :
    F (e δ i) ≠ e (-δ) i :=
  fun h ↦ hδ (two_mul_eq_zero_of_map_e_eq F i h)

end ParameterRecovery

variable {R : Type*} [CommRing R]

section SignEquiv

private def signTo {δ δ' : R} (h : δ' = -δ) {n : ℕ} :
    TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ' n :=
  lift (fun i ↦ -e δ' i)
    (fun i ↦ by rw [neg_mul_neg, e_mul_self, h, neg_smul, smul_neg])
    (fun hadj ↦ by rw [neg_mul_neg, mul_neg, e_mul_e_mul_e hadj])
    (fun hdist ↦ by rw [neg_mul_neg, neg_mul_neg, (commute_e hdist).eq])

private theorem signTo_e {δ δ' : R} (h : δ' = -δ) {n : ℕ} (i : Fin (n - 1)) :
    signTo h (e δ i) = -e δ' i :=
  lift_e _ _ _ _ i

private theorem signTo_comp_signTo {δ δ' : R} (h : δ' = -δ) (h' : δ = -δ') {n : ℕ} :
    (signTo h').comp (signTo h) = AlgHom.id R (TemperleyLieb R δ n) :=
  hom_ext fun i ↦ by simp [signTo_e]

/-- The **sign isomorphism** of Temperley–Lieb algebras: negating every generator gives an algebra
equivalence `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n`. -/
def signEquiv (δ : R) {n : ℕ} : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n :=
  AlgEquiv.ofAlgHom (signTo rfl) (signTo (neg_neg δ).symm)
    (signTo_comp_signTo (neg_neg δ).symm rfl)
    (signTo_comp_signTo rfl (neg_neg δ).symm)

/-- The sign isomorphism negates each generator. -/
@[simp]
theorem signEquiv_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    signEquiv δ (e δ i) = -e (-δ) i := by
  rw [signEquiv, AlgEquiv.ofAlgHom_apply, signTo_e]

/-- The inverse sign isomorphism negates each generator. -/
@[simp]
theorem signEquiv_symm_e (δ : R) {n : ℕ} (i : Fin (n - 1)) :
    (signEquiv δ).symm (e (-δ) i) = -e δ i := by
  rw [signEquiv, AlgEquiv.ofAlgHom_symm_apply, signTo_e]

/-- The sign isomorphism commutes with adding a straight strand, as an equality of algebra maps. -/
theorem signEquiv_comp_strandIncl (δ : R) (n : ℕ) :
    (signEquiv δ (n := n + 2)).toAlgHom.comp strandIncl =
      strandIncl.comp (signEquiv δ (n := n + 1)).toAlgHom :=
  hom_ext fun i ↦ by simp

/-- The sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_strandIncl (δ : R) {n : ℕ} (x : TemperleyLieb R δ (n + 1)) :
    signEquiv δ (strandIncl x) = strandIncl (signEquiv δ x) :=
  AlgHom.congr_fun (signEquiv_comp_strandIncl δ n) x

/-- The inverse sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_symm_strandIncl (δ : R) {n : ℕ} (x : TemperleyLieb R (-δ) (n + 1)) :
    (signEquiv δ).symm (strandIncl x) = strandIncl ((signEquiv δ).symm x) := by
  apply (signEquiv δ).injective
  simp

/-- The sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_signEquiv (δ : R) {n : ℕ} (x : TemperleyLieb R δ n) :
    aug (signEquiv δ x) = aug x := by
  have h : aug.comp (signEquiv δ (n := n)).toAlgHom = aug :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun h x

/-- The inverse sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_signEquiv_symm (δ : R) {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    aug ((signEquiv δ).symm x) = aug x := by
  simpa only [AlgEquiv.apply_symm_apply] using (aug_signEquiv δ ((signEquiv δ).symm x)).symm

/-- On a Kauffman crossing `α • 1 + β • e δ i`, the sign isomorphism negates the second
coefficient. -/
theorem signEquiv_crossing (δ α β : R) {n : ℕ} (i : Fin (n - 1)) :
    signEquiv δ (crossing δ α β i) = crossing (-δ) α (-β) i := by
  simp [crossing_def, neg_smul]

/-- On a Kauffman crossing `α • 1 + β • e (-δ) i`, the inverse sign isomorphism negates the second
coefficient. -/
theorem signEquiv_symm_crossing (δ α β : R) {n : ℕ} (i : Fin (n - 1)) :
    (signEquiv δ).symm (crossing (-δ) α β i) = crossing δ α (-β) i := by
  simp [crossing_def, neg_smul]

private theorem inverse_neg_one_pow_mul (k : ℕ) (x : R) :
    Ring.inverse ((-1 : R) ^ k * x) = (-1 : R) ^ k * Ring.inverse x := by
  have hu : Ring.inverse ((-1 : R) ^ k) = (-1 : R) ^ k := by
    simpa using Ring.inverse_unit ((-1 : Rˣ) ^ k)
  rw [Ring.inverse_mul (Or.inl (isUnit_neg_one.pow k)), hu, mul_comm]

private theorem inverse_neg (x : R) : Ring.inverse (-x) = -Ring.inverse x := by
  simpa using inverse_neg_one_pow_mul 1 x

/-- The sign isomorphism carries the Jones–Wenzl projection at `δ` to the Jones–Wenzl projection at
`-δ`, with no invertibility assumption on the quantum integers: the sign flip of `[m + 1] / [m + 2]`
cancels the negation of the last generator in Wenzl's recursion. -/
@[simp]
theorem signEquiv_jonesWenzl (δ : R) :
    ∀ n : ℕ, signEquiv δ (jonesWenzl δ n) = jonesWenzl (-δ) n
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have hcoeff : qInt R (-δ) (m + 1) * Ring.inverse (qInt R (-δ) (m + 2)) =
        -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by
      have hsq : (-1 : R) ^ (m + 2) * (-1 : R) ^ (m + 2) = 1 := by
        rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
      rw [qInt_neg_left δ (m + 1), qInt_neg_left δ (m + 2), inverse_neg_one_pow_mul,
        pow_succ (-1 : R) (m + 2)]
      calc
        ((-1 : R) ^ (m + 2) * qInt R δ (m + 1)) *
            (((-1 : R) ^ (m + 2) * -1) * Ring.inverse (qInt R δ (m + 2))) =
            -((-1 : R) ^ (m + 2) * (-1 : R) ^ (m + 2)) *
              (qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by ring
        _ = -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by rw [hsq, neg_one_mul]
    rw [jonesWenzl_add_two, jonesWenzl_add_two, map_sub, map_smul, map_mul, map_mul,
      signEquiv_strandIncl, signEquiv_jonesWenzl δ (m + 1), signEquiv_e, hcoeff,
      mul_neg, neg_mul, smul_neg, neg_smul, sub_neg_eq_add]

/-- The inverse sign isomorphism carries the Jones–Wenzl projection at `-δ` to the Jones–Wenzl
projection at `δ`. -/
@[simp]
theorem signEquiv_symm_jonesWenzl (δ : R) (n : ℕ) :
    (signEquiv δ).symm (jonesWenzl (-δ) n) = jonesWenzl δ n :=
  (signEquiv δ).symm_apply_eq.mpr (signEquiv_jonesWenzl δ n).symm

end SignEquiv

section Star

variable [StarRing R] {δ : R} [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]

/-- At self-adjoint loop parameters, the sign isomorphism commutes with the analytic adjoint. -/
@[simp]
theorem signEquiv_star {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquiv δ (star x) = star (signEquiv δ x) :=
  map_star_iff (F := (signEquiv δ (n := n)).toAlgHom) |>.mpr
    (fun i ↦ by simp [IsSelfAdjoint]) x

/-- At self-adjoint loop parameters, the inverse sign isomorphism commutes with the analytic
adjoint. -/
@[simp]
theorem signEquiv_symm_star {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    (signEquiv δ).symm (star x) = star ((signEquiv δ).symm x) :=
  map_star_iff (F := (signEquiv δ (n := n)).symm.toAlgHom) |>.mpr
    (fun i ↦ by simp [IsSelfAdjoint]) x

variable (δ) in
/-- At self-adjoint loop parameters, the sign isomorphism bundled as a star-algebra equivalence
`TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n`. -/
def signStarAlgEquiv {n : ℕ} : TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n :=
  StarAlgEquiv.ofAlgEquiv (signEquiv δ) (signEquiv_star (δ := δ))

/-- Coercion of `signStarAlgEquiv` to a function agrees with `signEquiv`. -/
@[simp]
theorem signStarAlgEquiv_apply {n : ℕ} (x : TemperleyLieb R δ n) :
    signStarAlgEquiv δ x = signEquiv δ x := by
  rw [signStarAlgEquiv, StarAlgEquiv.ofAlgEquiv_apply]

/-- Applying the inverse of `signStarAlgEquiv` agrees with `(signEquiv δ).symm`. -/
@[simp]
theorem signStarAlgEquiv_symm_apply {n : ℕ} (x : TemperleyLieb R (-δ) n) :
    (signStarAlgEquiv δ).symm x = (signEquiv δ).symm x := by
  apply (signEquiv δ).injective
  rw [AlgEquiv.apply_symm_apply, ← signStarAlgEquiv_apply, StarAlgEquiv.apply_symm_apply]

/-- Forgetting the star structure on `signStarAlgEquiv` recovers `signEquiv`. -/
@[simp]
theorem toAlgEquiv_signStarAlgEquiv (n : ℕ) :
    (signStarAlgEquiv δ (n := n)).toAlgEquiv = signEquiv δ := by
  rw [signStarAlgEquiv, StarAlgEquiv.toAlgEquiv_ofAlgEquiv]

end Star

section MarkovTrace

variable {δ : R}

/-- Transport a family of linear functionals on the Temperley–Lieb tower at `δ` across the sign
isomorphism to `-δ`, scaling degree `n` by `(-1) ^ n`. When `tr` is an unnormalized Markov trace at
`δ`, `signTrace tr` is the unique unnormalized Markov trace at `-δ`
(`TauCeti.TemperleyLieb.IsMarkovTrace.signTrace`). -/
def signTrace (tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) (n : ℕ) :
    TemperleyLieb R (-δ) n →ₗ[R] R :=
  ((-1 : R) ^ n) • (tr n ∘ₗ (signEquiv δ).symm.toLinearMap)

/-- Evaluation of `signTrace` at an element on `n` strands. -/
@[simp]
theorem signTrace_apply (tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) (n : ℕ)
    (x : TemperleyLieb R (-δ) n) :
    signTrace tr n x = (-1 : R) ^ n * tr n ((signEquiv δ).symm x) := by
  simp [signTrace]

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- Transporting an unnormalized Markov trace from `δ` to `-δ` with the sign `(-1) ^ n` on `n`
strands yields an unnormalized Markov trace at `-δ`. -/
theorem signTrace (htr : IsMarkovTrace R δ tr) :
    IsMarkovTrace R (-δ) (TemperleyLieb.signTrace tr) where
  map_one n := by
    rw [signTrace_apply, _root_.map_one (signEquiv δ).symm, htr.map_one, ← mul_pow, neg_one_mul]
  map_mul_comm n x y := by
    simp only [signTrace_apply, map_mul, htr.map_mul_comm]
  map_strandIncl n x := by
    rw [signTrace_apply, signEquiv_symm_strandIncl, htr.map_strandIncl, signTrace_apply,
      pow_succ (-1 : R) (n + 1)]
    ring
  map_strandIncl_mul_e_last n x := by
    rw [signTrace_apply, map_mul, signEquiv_symm_strandIncl, signEquiv_symm_e, mul_neg,
      map_neg, htr.map_strandIncl_mul_e_last, signTrace_apply, pow_succ (-1 : R) (n + 1)]
    ring

/-- Every unnormalized Markov trace at `-δ` is `TemperleyLieb.signTrace` of any unnormalized Markov
trace at `δ`. -/
theorem eq_signTrace (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') :
    tr' = TemperleyLieb.signTrace tr :=
  htr'.unique htr.signTrace

/-- On `n` strands, any unnormalized Markov trace at `-δ` evaluates on `signEquiv δ x` as `(-1) ^ n`
times any unnormalized Markov trace at `δ` evaluated on `x`. -/
theorem map_signEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R δ n) :
    tr' n (signEquiv δ x) = (-1 : R) ^ n * tr n x := by
  rw [htr.eq_signTrace htr', signTrace_apply, AlgEquiv.symm_apply_apply]

/-- On `n` strands, any unnormalized Markov trace at `δ` evaluates on `(signEquiv δ).symm y` as
`(-1) ^ n` times any unnormalized Markov trace at `-δ` evaluated on `y`. -/
theorem map_signEquiv_symm (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (y : TemperleyLieb R (-δ) n) :
    tr n ((signEquiv δ).symm y) = (-1 : R) ^ n * tr' n y := by
  have hsq : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc
    tr n ((signEquiv δ).symm y) =
        ((-1 : R) ^ n * (-1 : R) ^ n) * tr n ((signEquiv δ).symm y) := by rw [hsq, one_mul]
    _ = (-1 : R) ^ n * ((-1 : R) ^ n * tr n ((signEquiv δ).symm y)) := by ring
    _ = (-1 : R) ^ n * tr' n (signEquiv δ ((signEquiv δ).symm y)) := by
      rw [htr.map_signEquiv htr']
    _ = (-1 : R) ^ n * tr' n y := by rw [AlgEquiv.apply_symm_apply]

/-- Recovering `tr n x` from `tr' n (signEquiv δ x)` by multiplying by `(-1) ^ n`. -/
theorem eq_neg_one_pow_mul_map_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x : TemperleyLieb R δ n) :
    tr n x = (-1 : R) ^ n * tr' n (signEquiv δ x) := by
  simpa only [AlgEquiv.symm_apply_apply] using htr.map_signEquiv_symm htr' n (signEquiv δ x)

/-- **Invariance of the normalized Markov trace.** Scaling the unnormalized Markov trace on `n`
strands by `(Ring.inverse δ) ^ n` eliminates the sign `(-1) ^ n`, so the normalized trace is
strictly preserved by `signEquiv`. When `δ` is not a unit both sides vanish for `n ≥ 1` and agree at
`n = 0`. -/
theorem inverse_pow_mul_map_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x : TemperleyLieb R δ n) :
    Ring.inverse (-δ) ^ n * tr' n (signEquiv δ x) = Ring.inverse δ ^ n * tr n x := by
  have hsq : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [inverse_neg, neg_eq_neg_one_mul (Ring.inverse δ), mul_pow, htr.map_signEquiv htr']
  calc
    ((-1 : R) ^ n * Ring.inverse δ ^ n) * ((-1 : R) ^ n * tr n x) =
        ((-1 : R) ^ n * (-1 : R) ^ n) * (Ring.inverse δ ^ n * tr n x) := by ring
    _ = Ring.inverse δ ^ n * tr n x := by rw [hsq, one_mul]

section Star

variable [StarRing R] [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]

/-- The sesquilinear form of a Markov trace at `-δ` pulls back along `signEquiv` to `(-1) ^ n` times
the sesquilinear form at `δ`. -/
theorem traceSesqForm_signEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    {n : ℕ} (x y : TemperleyLieb R δ n) :
    (tr' n).traceSesqForm (signEquiv δ x) (signEquiv δ y) =
      (-1 : R) ^ n * (tr n).traceSesqForm x y := by
  rw [LinearMap.traceSesqForm_apply, LinearMap.traceSesqForm_apply, ← signEquiv_star, ← map_mul,
    htr.map_signEquiv htr']

/-- Under `signEquiv`, the quadratic trace value `tr' n (star y * y)` on `n` strands transforms by
`(-1) ^ n`. -/
theorem map_star_mul_self_signEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    {n : ℕ} (x : TemperleyLieb R δ n) :
    tr' n (star (signEquiv δ x) * signEquiv δ x) = (-1 : R) ^ n * tr n (star x * x) := by
  simpa only [LinearMap.traceSesqForm_apply] using htr.traceSesqForm_signEquiv htr' x x

/-- The normalized Hermitian trace form `(Ring.inverse δ) ^ n * tr n (star x * x)` is strictly
invariant under `signEquiv`. -/
theorem inverse_pow_mul_map_star_mul_self_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ} (x : TemperleyLieb R δ n) :
    Ring.inverse (-δ) ^ n * tr' n (star (signEquiv δ x) * signEquiv δ x) =
      Ring.inverse δ ^ n * tr n (star x * x) := by
  rw [← signEquiv_star, ← map_mul, htr.inverse_pow_mul_map_signEquiv htr']

end Star

end IsMarkovTrace

/-- If `δ = -(q + q⁻¹)` for a unit `q`, then `-δ = -((-q) + (-q)⁻¹)`. -/
theorem neg_eq_neg_add_inv (q : Rˣ) (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) :
    -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := by
  rw [hq, inv_neg, Units.val_neg, Units.val_neg]
  ring

/-- **Sign transport for the spin-model Markov trace.** Evaluating the spin-model trace at `-q`
(loop value `-δ`) on `signEquiv δ x` multiplies the spin-model trace at `q` (loop value `δ`) by
`(-1) ^ n`. -/
theorem markovTrace_neg_signEquiv (q : Rˣ) (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hnq : -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := neg_eq_neg_add_inv q hq)
    {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace (-q) hnq (signEquiv δ x) = (-1 : R) ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).map_signEquiv (isMarkovTrace_markovTrace (-q) hnq) n x

/-- Expressing the spin-model Markov trace at `q` in terms of the spin-model trace at `-q` via
`signEquiv`. -/
theorem markovTrace_eq_neg_one_pow_mul_markovTrace_neg_signEquiv (q : Rˣ)
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hnq : -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := neg_eq_neg_add_inv q hq)
    {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace q hq x = (-1 : R) ^ n * markovTrace (-q) hnq (signEquiv δ x) :=
  (isMarkovTrace_markovTrace q hq).eq_neg_one_pow_mul_map_signEquiv
    (isMarkovTrace_markovTrace (-q) hnq) n x

end MarkovTrace

section Field

variable {K : Type*} [Field K] [StarRing K] {δ : K} [Fact (IsSelfAdjoint δ)]
  [Fact (IsSelfAdjoint (-δ))] {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
  {tr' : ∀ n : ℕ, TemperleyLieb K (-δ) n →ₗ[K] K}

/-- Over a star field, the normalized quadratic trace form `(δ⁻¹) ^ n * tr n (star x * x)` is
strictly preserved by `signEquiv`. -/
theorem IsMarkovTrace.inv_pow_mul_map_star_mul_self_signEquiv (htr : IsMarkovTrace K δ tr)
    (htr' : IsMarkovTrace K (-δ) tr') {n : ℕ} (x : TemperleyLieb K δ n) :
    ((-δ)⁻¹) ^ n * tr' n (star (signEquiv δ x) * signEquiv δ x) =
      (δ⁻¹) ^ n * tr n (star x * x) := by
  simpa only [Ring.inverse_eq_inv'] using htr.inverse_pow_mul_map_star_mul_self_signEquiv htr' x

end Field

section Quotient

namespace IsMarkovTrace

variable {δ : R} {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- Because `(-1) ^ n` is a unit in every commutative ring, `signEquiv` preserves and reflects
membership in the multiplication-pairing radical of any Markov trace. -/
theorem signEquiv_mem_traceRadical_iff (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquiv δ x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) := by
  simp only [LinearMap.mem_traceRadical]
  refine ⟨fun hx y ↦ ?_, fun hx y ↦ ?_⟩
  · have h := hx (signEquiv δ y)
    rwa [← map_mul, htr.map_signEquiv htr', (isUnit_neg_one.pow n).mul_right_eq_zero] at h
  · rw [← (signEquiv δ).apply_symm_apply y, ← map_mul, htr.map_signEquiv htr',
      hx ((signEquiv δ).symm y), mul_zero]

/-- Pulling back the trace radical at `-δ` along `signEquiv` gives the trace radical at `δ`. -/
theorem comap_traceRadical_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.comap ((signEquiv δ (n := n)) : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
      ((tr' n).traceRadical (htr'.map_mul_comm n)) =
        (tr n).traceRadical (htr.map_mul_comm n) := by
  ext x
  exact htr.signEquiv_mem_traceRadical_iff htr' x

/-- Pushing forward the trace radical at `δ` along `signEquiv` gives the trace radical at `-δ`. -/
theorem map_traceRadical_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.map ((signEquiv δ (n := n)) : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n)
      ((tr n).traceRadical (htr.map_mul_comm n)) =
        (tr' n).traceRadical (htr'.map_mul_comm n) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr (htr.comap_traceRadical_signEquiv htr' n).ge)
    fun y hy ↦ ?_
  have hy' : (signEquiv δ).symm y ∈ (tr n).traceRadical (htr.map_mul_comm n) :=
    (htr.signEquiv_mem_traceRadical_iff htr' _).mp (by simpa using hy)
  have hmem := Ideal.mem_map_of_mem
    ((signEquiv δ (n := n)) : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n) hy'
  rwa [RingHom.coe_coe, AlgEquiv.apply_symm_apply] at hmem

/-- The algebra isomorphism between the trace-radical quotients at `δ` and `-δ` induced by
`signEquiv`. -/
def quotientSignEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  Ideal.quotientEquivAlg _ _ (signEquiv δ) (htr.map_traceRadical_signEquiv htr' n).symm

/-- `quotientSignEquiv` acts on quotient classes by applying `signEquiv` to representatives. -/
@[simp]
theorem quotientSignEquiv_mk (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R δ n) :
    htr.quotientSignEquiv htr' n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) (signEquiv δ x) := by
  rw [quotientSignEquiv, Ideal.quotientEquivAlg_mk]

/-- The inverse of `quotientSignEquiv` acts on quotient classes by applying `(signEquiv δ).symm` to
representatives. -/
@[simp]
theorem quotientSignEquiv_symm_mk (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    (htr.quotientSignEquiv htr' n).symm
      (Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) ((signEquiv δ).symm x) := by
  rw [quotientSignEquiv, Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]

/-- The trace-radical quotient sign equivalences intertwine the tower strand inclusions. -/
@[simp]
theorem quotientSignEquiv_quotientStrandIncl (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientSignEquiv htr' (n + 2) (htr.quotientStrandIncl n x) =
      htr'.quotientStrandIncl n (htr.quotientSignEquiv htr' (n + 1) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- Commutativity of the tower square between `quotientSignEquiv` and `quotientStrandIncl`, as an
equality of algebra homomorphisms. -/
theorem quotientSignEquiv_comp_quotientStrandIncl (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    (htr.quotientSignEquiv htr' (n + 2)).toAlgHom.comp (htr.quotientStrandIncl n) =
      (htr'.quotientStrandIncl n).comp (htr.quotientSignEquiv htr' (n + 1)).toAlgHom :=
  AlgHom.ext (htr.quotientSignEquiv_quotientStrandIncl htr' n)

/-- On the trace-radical quotients, `quotientSignEquiv` scales the induced quotient trace by
`(-1) ^ n`. -/
@[simp]
theorem quotientTrace_quotientSignEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientSignEquiv htr' n x) =
      (-1 : R) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [htr.map_signEquiv htr']

/-- On the trace-radical quotients, `quotientSignEquiv` strictly preserves the normalized quotient
trace `(Ring.inverse δ) ^ n • quotientTrace`. -/
theorem inverse_pow_mul_quotientTrace_quotientSignEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    Ring.inverse (-δ) ^ n *
        (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientSignEquiv htr' n x) =
      Ring.inverse δ ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa using htr.inverse_pow_mul_map_signEquiv htr' n x

section Star

variable [StarRing R] [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]

/-- At self-adjoint loop parameters, `quotientSignEquiv` commutes with the quotient star
involution. -/
@[simp]
theorem quotientSignEquiv_star (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientSignEquiv htr' n (star x) = star (htr.quotientSignEquiv htr' n x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- At self-adjoint loop parameters, the trace-radical quotients at `δ` and `-δ` are isomorphic as
star algebras. When working with an abstract Markov trace `htr`, supply `htr.isStar_traceRadical n`
via `have`; for `markovTrace`, `instIsStarTraceRadicalMarkovTrace` is automatic. -/
def quotientSignStarAlgEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃⋆ₐ[R]
      (TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :=
  StarAlgEquiv.ofAlgEquiv (htr.quotientSignEquiv htr' n) (htr.quotientSignEquiv_star htr' n)

/-- Coercion of `quotientSignStarAlgEquiv` to a function agrees with `quotientSignEquiv`. -/
@[simp]
theorem quotientSignStarAlgEquiv_apply (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientSignStarAlgEquiv htr' n x = htr.quotientSignEquiv htr' n x := by
  rw [quotientSignStarAlgEquiv, StarAlgEquiv.ofAlgEquiv_apply]

/-- Applying the inverse of `quotientSignStarAlgEquiv` agrees with
`(htr.quotientSignEquiv htr' n).symm`. -/
@[simp]
theorem quotientSignStarAlgEquiv_symm_apply (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :
    (htr.quotientSignStarAlgEquiv htr' n).symm x = (htr.quotientSignEquiv htr' n).symm x := by
  apply (htr.quotientSignEquiv htr' n).injective
  rw [AlgEquiv.apply_symm_apply, ← htr.quotientSignStarAlgEquiv_apply htr' n,
    StarAlgEquiv.apply_symm_apply]

/-- Forgetting the star structure on `quotientSignStarAlgEquiv` recovers `quotientSignEquiv`. -/
@[simp]
theorem toAlgEquiv_quotientSignStarAlgEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (htr.quotientSignStarAlgEquiv htr' n).toAlgEquiv = htr.quotientSignEquiv htr' n := by
  rw [quotientSignStarAlgEquiv, StarAlgEquiv.toAlgEquiv_ofAlgEquiv]

end Star

end IsMarkovTrace

end Quotient

end TauCeti.TemperleyLieb
