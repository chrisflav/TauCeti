/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Coboundary
-- Proof-only: multivariate partial derivatives, pi topology, and substitution formulas.
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Symmetric 2-cocycles from square-zero deformations and dual-number evaluation

Let `F₁` and `F₂` be commutative formal group laws over a commutative ring `S` that agree modulo
an ideal `J` with `J ^ 2 = ⊥`. Setting `Δ := F₁ - F₂`, associativity of `F₁` and `F₂` together with
invariance of the invariant differential `ω` of `F₂`
(`FormalGroup.subst_invariantDifferential_mul_pderiv` and
`FormalGroup.subst_invariantDifferential_mul_pderiv_one`) imply that
`Ψ := ω(F₂(X, Y)) · (F₁(X, Y) - F₂(X, Y))` is a symmetric additive 2-cocycle of `F₂`
(`FormalGroup.isSymmetricCocycle_invariantDifferential_mul_sub`, Lubin–Tate §1–§2).

When `F₁ = φ • F₂` for a coordinate change `φ = X + h` with `h` having zero constant term and
coefficients in `J`, the resulting cocycle is the coboundary `F₂.homDefect 𝔾ₐ (ω · h)`
(`FormalGroup.invariantDifferential_mul_smul_sub_eq_homDefect_𝔾ₐ`), and any coordinate change
congruent to `X` modulo an ideal `I` with `I * J = ⊥` acts trivially on differences `F₁ - F₂`
modulo `J` (`FormalGroup.smul_sub_smul_eq_of_mul_eq_bot`). The module also provides the dual-number
evaluation homomorphism `MvPowerSeries.evalDual` used to form derivative cocycles in
`TauCeti.RingTheory.FormalGroup.Deformation.DerivCocycle`.

## Main definitions

* `MvPowerSeries.evalDual`: evaluation at `X i ↦ ε` and `X j ↦ 0` (`j ≠ i`) into `DualNumber k`.
* `TauCeti.FormalCoordinate.ofSquareZero`: formal coordinate `X + h` modulo a square-zero ideal.

## Main results

* `MvPowerSeries.subst_add_of_mul_eq_zero`: multivariate first-order Taylor formula for
  perturbations whose pairwise products vanish.
* `FormalGroup.isSymmetricCocycle_invariantDifferential_mul_sub`: square-zero difference of
  commutative formal group laws yields a symmetric 2-cocycle after multiplying by `ω(F₂(X, Y))`.
* `FormalGroup.invariantDifferential_mul_smul_sub_eq_homDefect_𝔾ₐ`: square-zero coordinate changes
  induce coboundaries.
* `FormalGroup.smul_sub_smul_eq_of_mul_eq_bot`: coordinate changes `≡ X (mod I)` preserve
  `J`-congruent differences when `I * J = ⊥` and `J ^ 2 = ⊥`.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1–§2.
-/

public section

noncomputable section

namespace MvPowerSeries

open Finsupp

section SquareZero

open WithPiTopology

variable {σ τ R : Type*} [CommRing R]

/-- A finite family of multivariate power series whose squares vanish is substitutable. -/
theorem HasSubst.of_sq_eq_zero [Finite σ] {h : σ → MvPowerSeries τ R}
    (hh : ∀ i, h i ^ 2 = 0) : HasSubst h where
  const_coeff s := ⟨2, by rw [← map_pow, hh s, map_zero]⟩
  coeff_zero _ := Set.toFinite _

/-- The first-order Taylor formula for multivariate power series: if `h i * h j = 0` for all
`i, j`, then `f(a + h) = f(a) + ∑ i, h i * (∂ᵢ f)(a)`. -/
theorem subst_add_of_mul_eq_zero [Fintype σ] {a h : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (hh : ∀ i j, h i * h j = 0) (f : MvPowerSeries σ R) :
    f.subst (a + h) = f.subst a + ∑ i, h i * (pderiv i f).subst a := by
  classical
  have hh' : HasSubst h := HasSubst.of_sq_eq_zero fun i ↦ by rw [sq, hh i i]
  have hah : HasSubst (a + h) := ha.add hh'
  let : UniformSpace R := ⊥
  have : DiscreteUniformity R := ⟨rfl⟩
  revert f
  rw [← funext_iff]
  refine Continuous.ext_on denseRange_toMvPowerSeries
    (continuous_subst hah)
    ((continuous_subst ha).add
      (continuous_finsetSum _ fun i _ ↦
        continuous_const.mul ((continuous_subst ha).comp (continuous_pderiv i)))) ?_
  have h0 : subst a (0 : MvPowerSeries σ R) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have h1 : subst a (1 : MvPowerSeries σ R) = 1 := by rw [← coe_substAlgHom ha, map_one]
  rintro _ ⟨p, rfl⟩
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [subst_C, h0]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, map_add, subst_add hah, subst_add ha] at hp hq ⊢
    simp only [hp, hq, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X p n hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul hah, subst_X hah,
      subst_mul ha, subst_X ha, Pi.add_apply, Derivation.leibniz, smul_eq_mul,
      subst_add ha] at hp ⊢
    have hkill : (∑ i : σ, h i * (pderiv i (p : MvPowerSeries σ R)).subst a) * h n = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [mul_right_comm, hh i n, zero_mul]
    rw [hp, mul_add, add_mul, add_mul, hkill, add_zero]
    simp only [pderiv_X, Pi.single_apply]
    simp only [apply_ite (subst a), h0, h1, mul_add, mul_ite, mul_zero, mul_one]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_mul]
    simp only [Finset.mem_univ, ↓reduceIte]
    simp_rw [mul_right_comm (h _), mul_assoc]
    ring

end SquareZero

section SingleMul

variable {σ R : Type*} [CommSemiring R]

/-- The coefficient of a linear monomial `X i` in a product `f * g` is
`constantCoeff f * coeff (single i 1) g + coeff (single i 1) f * constantCoeff g`. -/
theorem coeff_single_one_mul (f g : MvPowerSeries σ R) (i : σ) :
    coeff (single i 1) (f * g) =
      constantCoeff f * coeff (single i 1) g + coeff (single i 1) f * constantCoeff g := by
  classical
  rw [coeff_mul]
  have hmem : ∀ p ∈ Finset.antidiagonal (single i 1),
      p = (0, single i 1) ∨ p = (single i 1, 0) := by
    rintro ⟨u, v⟩ huv
    rw [Finset.mem_antidiagonal] at huv
    have hi : u i + v i = 1 := by simpa using congrFun (congrArg DFunLike.coe huv) i
    have hne : ∀ j ≠ i, u j = 0 ∧ v j = 0 := fun j hj ↦ by
      have hj' : u j + v j = 0 := by
        simpa [Finsupp.single_apply, hj.symm] using congrFun (congrArg DFunLike.coe huv) j
      omega
    rcases (by omega : u i = 0 ∧ v i = 1 ∨ u i = 1 ∧ v i = 0) with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · left
      ext a
      · by_cases ha : a = i <;> simp [ha, hu, fun h' ↦ (hne a h').1]
      · by_cases ha : a = i <;> simp [ha, hv, fun h' ↦ (hne a h').2]
    · right
      ext a
      · by_cases ha : a = i <;> simp [ha, hu, fun h' ↦ (hne a h').1]
      · by_cases ha : a = i <;> simp [ha, hv, fun h' ↦ (hne a h').2]
  have hsum := Finset.sum_subset
    (s₁ := {(0, single i 1), (single i 1, 0)})
    (s₂ := Finset.antidiagonal (single i 1))
    (fun p hp ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> simp [Finset.mem_antidiagonal])
    (fun p hp hnot ↦
      absurd (hmem p hp) (by simpa [Finset.mem_insert, Finset.mem_singleton] using hnot))
    (f := fun p ↦ coeff p.1 f * coeff p.2 g)
  rw [← hsum, Finset.sum_pair (by simp [Prod.ext_iff, single_eq_zero])]
  simp [coeff_zero_eq_constantCoeff]

end SingleMul

section EvalDual

variable {σ R k : Type*} [CommRing R] [CommRing k]

/-- Evaluate a multivariate power series over `R` into `DualNumber k` along `ρ : R →+* k`
by sending `X i` to `ε` and `X j` (`j ≠ i`) to `0`. -/
@[expose]
def evalDual (ρ : R →+* k) (i : σ) : MvPowerSeries σ R →+* DualNumber k where
  toFun f := TrivSqZeroExt.inl (ρ (constantCoeff f)) +
    TrivSqZeroExt.inr (ρ (coeff (single i 1) f))
  map_one' := by
    classical
    ext <;> simp [coeff_one, single_eq_zero]
  map_mul' f g := by
    classical
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        coeff_single_one_mul, map_add, map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, smul_eq_mul,
        _root_.op_smul_eq_mul]
  map_zero' := by ext <;> simp
  map_add' f g := by ext <;> simp

/-- The scalar part of `evalDual ρ i f` is `ρ (constantCoeff f)`. -/
@[simp]
theorem fst_evalDual (ρ : R →+* k) (i : σ) (f : MvPowerSeries σ R) :
    (evalDual ρ i f).fst = ρ (constantCoeff f) := by
  simp [evalDual]

/-- The `ε`-part of `evalDual ρ i f` is `ρ (coeff (single i 1) f)`. -/
@[simp]
theorem snd_evalDual (ρ : R →+* k) (i : σ) (f : MvPowerSeries σ R) :
    (evalDual ρ i f).snd = ρ (coeff (single i 1) f) := by
  simp [evalDual]

/-- Constant power series evaluate under `evalDual ρ i` to `inl (ρ r)`. -/
@[simp]
theorem evalDual_C (ρ : R →+* k) (i : σ) (r : R) :
    evalDual ρ i (C r) = TrivSqZeroExt.inl (ρ r) := by
  classical
  ext <;> simp [coeff_C, single_eq_zero]

/-- Variable `X j` evaluates under `evalDual ρ i` to `ε` if `j = i` and `0` otherwise. -/
@[simp]
theorem evalDual_X [DecidableEq σ] (ρ : R →+* k) (i j : σ) :
    evalDual ρ i (X j) = if j = i then DualNumber.eps else 0 := by
  ext
  · split_ifs <;> simp
  · by_cases hij : j = i
    · subst hij
      simp [coeff_X]
    · simp [coeff_X, Finsupp.single_eq_single_iff, hij, Ne.symm hij]

/-- Projecting `evalDual ρ i` to the scalar component recovers `ρ ∘ constantCoeff`. -/
theorem fstHom_comp_evalDual (ρ : R →+* k) (i : σ) :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp (evalDual ρ i) = ρ.comp constantCoeff := by
  ext f
  simp

/-- Restricting `evalDual ρ i` to constants recovers `inlHom ∘ ρ`. -/
theorem evalDual_comp_C (ρ : R →+* k) (i : σ) :
    (evalDual ρ i).comp C = (TrivSqZeroExt.inlHom k k).comp ρ := by
  ext r <;> simp

end EvalDual

end MvPowerSeries

namespace TauCeti

section IdealSquareZero

variable {R : Type*} [CommRing R]

/-- If every coefficient of `f` and `g` lies in an ideal `J` with `J ^ 2 = ⊥`, then `f * g = 0`. -/
theorem mvPowerSeries_mul_eq_zero_of_coeff_mem {σ : Type*} {J : Ideal R} (hJ : J ^ 2 = ⊥)
    {f g : MvPowerSeries σ R} (hf : ∀ d, MvPowerSeries.coeff d f ∈ J)
    (hg : ∀ d, MvPowerSeries.coeff d g ∈ J) : f * g = 0 := by
  classical
  ext d
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_zero]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  rw [← Ideal.mem_bot, ← hJ, sq]
  exact Ideal.mul_mem_mul (hf p.1) (hg p.2)

/-- If coefficients of `f` lie in `I`, coefficients of `g` lie in `J`, and `I * J = ⊥`, then
`f * g = 0`. -/
theorem mvPowerSeries_mul_eq_zero_of_mul_eq_bot {σ : Type*} {I J : Ideal R} (hIJ : I * J = ⊥)
    {f g : MvPowerSeries σ R} (hf : ∀ d, MvPowerSeries.coeff d f ∈ I)
    (hg : ∀ d, MvPowerSeries.coeff d g ∈ J) : f * g = 0 := by
  classical
  ext d
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_zero]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  rw [← Ideal.mem_bot, ← hIJ]
  exact Ideal.mul_mem_mul (hf p.1) (hg p.2)

/-- Univariate version of `mvPowerSeries_mul_eq_zero_of_mul_eq_bot`. -/
theorem powerSeries_mul_eq_zero_of_mul_eq_bot {I J : Ideal R} (hIJ : I * J = ⊥)
    {f g : PowerSeries R} (hf : ∀ n, PowerSeries.coeff n f ∈ I)
    (hg : ∀ n, PowerSeries.coeff n g ∈ J) : f * g = 0 := by
  refine mvPowerSeries_mul_eq_zero_of_mul_eq_bot (σ := Unit) hIJ (fun d ↦ ?_) (fun d ↦ ?_)
  · rw [show d = Finsupp.single () (d ()) from Finsupp.ext fun _ ↦ by simp]
    exact hf (d ())
  · rw [show d = Finsupp.single () (d ()) from Finsupp.ext fun _ ↦ by simp]
    exact hg (d ())

/-- If every coefficient of `f` lies in `J`, then every coefficient of `f(a)` also lies in `J`. -/
theorem coeff_subst_mem_of_coeff_mem {σ τ : Type*} {J : Ideal R} {f : MvPowerSeries σ R}
    (hf : ∀ d, MvPowerSeries.coeff d f ∈ J) {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst a) ∈ J :=
  (Ideal.span_le.mpr (Set.range_subset_iff.mpr hf)) (MvPowerSeries.coeff_subst_mem_span ha e)

/-- Univariate version of `coeff_subst_mem_of_coeff_mem`. -/
theorem coeff_powerSeries_subst_mem_of_coeff_mem {τ : Type*} {J : Ideal R}
    {f : PowerSeries R} (hf : ∀ n, PowerSeries.coeff n f ∈ J)
    {g : MvPowerSeries τ R} (hg : PowerSeries.HasSubst g) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst g f) ∈ J := by
  change MvPowerSeries.coeff e (MvPowerSeries.subst (Function.const Unit g) f) ∈ J
  refine coeff_subst_mem_of_coeff_mem (σ := Unit) (J := J) (fun d ↦ ?_) hg.const e
  rw [show d = Finsupp.single () (d ()) from Finsupp.ext fun _ ↦ by simp]
  exact hf (d ())

end IdealSquareZero

namespace FormalCoordinate

variable {R : Type*} [CommRing R]

/-- Construct a formal coordinate `X + h` from a power series `h` with zero constant term and
coefficients in a square-zero ideal `J`. -/
@[expose]
def ofSquareZero {J : Ideal R} (hJ : J ^ 2 = ⊥) (h : PowerSeries R)
    (hh₀ : PowerSeries.constantCoeff h = 0) (hh : ∀ n, PowerSeries.coeff n h ∈ J) :
    FormalCoordinate R where
  toPowerSeries := PowerSeries.X + h
  constantCoeff_toPowerSeries := by simp [hh₀]
  isUnit_coeff_one := by
    refine .of_mul_eq_one (1 - PowerSeries.coeff 1 h) ?_
    have hsq : PowerSeries.coeff 1 h * PowerSeries.coeff 1 h = 0 := by
      rw [← Ideal.mem_bot, ← hJ, sq]
      exact Ideal.mul_mem_mul (hh 1) (hh 1)
    simp only [map_add, PowerSeries.coeff_one_X]
    linear_combination -hsq

/-- The underlying power series of `ofSquareZero hJ h hh₀ hh` is `X + h`. -/
@[simp]
theorem toPowerSeries_ofSquareZero {J : Ideal R} (hJ : J ^ 2 = ⊥) (h : PowerSeries R)
    (hh₀ : PowerSeries.constantCoeff h = 0) (hh : ∀ n, PowerSeries.coeff n h ∈ J) :
    (ofSquareZero hJ h hh₀ hh).toPowerSeries = PowerSeries.X + h :=
  rfl

/-- The inverse of `X + h` modulo a square-zero ideal is `X - h`. -/
theorem inv_ofSquareZero {J : Ideal R} (hJ : J ^ 2 = ⊥) (h : PowerSeries R)
    (hh₀ : PowerSeries.constantCoeff h = 0) (hh : ∀ n, PowerSeries.coeff n h ∈ J) :
    (ofSquareZero hJ h hh₀ hh)⁻¹ =
      ofSquareZero hJ (-h) (by simp [hh₀]) (fun n ↦ J.neg_mem (hh n)) := by
  have hsq : (-h) ^ 2 = 0 := by
    rw [neg_sq, sq]
    exact powerSeries_mul_eq_zero_of_mul_eq_bot (by rwa [← sq]) hh hh
  have hsub : (ofSquareZero hJ h hh₀ hh).toPowerSeries.subst (PowerSeries.X + -h) =
      PowerSeries.X := by
    have ha : PowerSeries.HasSubst (PowerSeries.X + -h) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hh₀])
    rw [toPowerSeries_ofSquareZero, PowerSeries.subst_add ha, PowerSeries.subst_X ha,
      PowerSeries.subst_X_add_of_sq_eq_zero hsq]
    have hkill : (-h) * PowerSeries.derivative h = 0 :=
      powerSeries_mul_eq_zero_of_mul_eq_bot (by rwa [← sq]) (fun n ↦ J.neg_mem (hh n)) fun n ↦ by
        rw [PowerSeries.coeff_derivative]
        exact J.mul_mem_right _ (hh (n + 1))
    rw [hkill, add_zero]
    ring
  ext1
  have hinj : (ofSquareZero hJ h hh₀ hh)⁻¹.toPowerSeries =
      (ofSquareZero hJ h hh₀ hh).toPowerSeries.substInvOfIsUnit
        (ofSquareZero hJ h hh₀ hh).isUnit_coeff_one := rfl
  rw [hinj, ← PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X _ (by simp [hh₀])
    (ofSquareZero hJ h hh₀ hh).isUnit_coeff_one
    (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hh₀])) hsub]
  rfl

end FormalCoordinate

end TauCeti

namespace FormalGroup

open MvPowerSeries TauCeti

section SquareZeroCocycle

variable {S : Type*} [CommRing S]

private theorem assoc_left_taylor_of_sq_eq_bot (F₁ F₂ : FormalGroup S)
    {J : Ideal S} (hJ : J ^ 2 = ⊥)
    (hΔ : ∀ d, MvPowerSeries.coeff d (F₁.toPowerSeries - F₂.toPowerSeries) ∈ J) :
    let Δ := F₁.toPowerSeries - F₂.toPowerSeries
    let F₁₂ := F₂.toPowerSeries.subst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) S)
    let Δ₁₂ := Δ.subst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) S)
    F₁.toPowerSeries.subst ![F₁.toPowerSeries.subst ![X 0, X 1], X 2] =
      F₂.toPowerSeries.subst ![F₁₂, X 2] + Δ₁₂ * (pderiv 0 F₂.toPowerSeries).subst ![F₁₂, X 2] +
        Δ.subst ![F₁₂, X 2] := by
  intro Δ F₁₂ Δ₁₂
  have hF₁ : F₁.toPowerSeries = F₂.toPowerSeries + Δ := by simp [Δ]
  have h01 : HasSubst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) S) := HasSubst.X_X
  have hF₁₂ : HasSubst (![F₁₂, X 2] : Fin 2 → MvPowerSeries (Fin 3) S) :=
    HasSubst.cons_subst_zero_left 0 1 2 F₂.zero_constantCoeff
  have hΔmem : ∀ e, coeff e Δ₁₂ ∈ J := coeff_subst_mem_of_coeff_mem hΔ h01
  have hΔkill : Δ₁₂ * Δ₁₂ = 0 := mvPowerSeries_mul_eq_zero_of_coeff_mem hJ hΔmem hΔmem
  have hΔ₁₂ : HasSubst (![Δ₁₂, 0] : Fin 2 → MvPowerSeries (Fin 3) S) :=
    HasSubst.of_sq_eq_zero fun i ↦ by fin_cases i <;> simp [sq, hΔkill]
  have harg : (![F₁.toPowerSeries.subst ![X 0, X 1], X 2] :
      Fin 2 → MvPowerSeries (Fin 3) S) = ![F₁₂, X 2] + ![Δ₁₂, 0] := by
    ext i; fin_cases i
    · simp [F₁₂, Δ₁₂, hF₁, subst_add h01]
    · simp
  have hF₂_tay := subst_add_of_mul_eq_zero hF₁₂ (h := ![Δ₁₂, 0]) (fun i j ↦ by
    fin_cases i <;> fin_cases j <;> simp [hΔkill]) F₂.toPowerSeries
  have hΔ_eq : Δ.subst (![F₁₂, X 2] + ![Δ₁₂, 0]) = Δ.subst ![F₁₂, X 2] :=
    subst_eq_subst_of_coeff_mem (hF₁₂.add hΔ₁₂) hF₁₂ (J := J)
      (fun i e ↦ by fin_cases i <;> [simpa using hΔmem e; simp])
      (fun d x hx ↦ by rw [← Ideal.mem_bot, ← hJ, sq]; exact Ideal.mul_mem_mul (hΔ d) hx)
  rw [harg]
  conv_lhs => rw [hF₁, subst_add (hF₁₂.add hΔ₁₂)]
  rw [hF₂_tay, hΔ_eq, Fin.sum_univ_two]
  simp

private theorem assoc_right_taylor_of_sq_eq_bot (F₁ F₂ : FormalGroup S)
    {J : Ideal S} (hJ : J ^ 2 = ⊥)
    (hΔ : ∀ d, MvPowerSeries.coeff d (F₁.toPowerSeries - F₂.toPowerSeries) ∈ J) :
    let Δ := F₁.toPowerSeries - F₂.toPowerSeries
    let F₂₃ := F₂.toPowerSeries.subst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) S)
    let Δ₂₃ := Δ.subst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) S)
    F₁.toPowerSeries.subst ![X 0, F₁.toPowerSeries.subst ![X 1, X 2]] =
      F₂.toPowerSeries.subst ![X 0, F₂₃] + Δ₂₃ * (pderiv 1 F₂.toPowerSeries).subst ![X 0, F₂₃] +
        Δ.subst ![X 0, F₂₃] := by
  intro Δ F₂₃ Δ₂₃
  have hF₁ : F₁.toPowerSeries = F₂.toPowerSeries + Δ := by simp [Δ]
  have h12 : HasSubst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) S) := HasSubst.X_X
  have hF₂₃ : HasSubst (![X 0, F₂₃] : Fin 2 → MvPowerSeries (Fin 3) S) :=
    HasSubst.cons_subst_zero_right 0 1 2 F₂.zero_constantCoeff
  have hΔmem : ∀ e, coeff e Δ₂₃ ∈ J := coeff_subst_mem_of_coeff_mem hΔ h12
  have hΔkill : Δ₂₃ * Δ₂₃ = 0 := mvPowerSeries_mul_eq_zero_of_coeff_mem hJ hΔmem hΔmem
  have hΔ₂₃ : HasSubst (![0, Δ₂₃] : Fin 2 → MvPowerSeries (Fin 3) S) :=
    HasSubst.of_sq_eq_zero fun i ↦ by fin_cases i <;> simp [sq, hΔkill]
  have harg : (![X 0, F₁.toPowerSeries.subst ![X 1, X 2]] :
      Fin 2 → MvPowerSeries (Fin 3) S) = ![X 0, F₂₃] + ![0, Δ₂₃] := by
    ext i; fin_cases i
    · simp
    · simp [F₂₃, Δ₂₃, hF₁, subst_add h12]
  have hF₂_tay := subst_add_of_mul_eq_zero hF₂₃ (h := ![0, Δ₂₃]) (fun i j ↦ by
    fin_cases i <;> fin_cases j <;> simp [hΔkill]) F₂.toPowerSeries
  have hΔ_eq : Δ.subst (![X 0, F₂₃] + ![0, Δ₂₃]) = Δ.subst ![X 0, F₂₃] :=
    subst_eq_subst_of_coeff_mem (hF₂₃.add hΔ₂₃) hF₂₃ (J := J)
      (fun i e ↦ by fin_cases i <;> [simp; simpa using hΔmem e])
      (fun d x hx ↦ by rw [← Ideal.mem_bot, ← hJ, sq]; exact Ideal.mul_mem_mul (hΔ d) hx)
  rw [harg]
  conv_lhs => rw [hF₁, subst_add (hF₂₃.add hΔ₂₃)]
  rw [hF₂_tay, hΔ_eq, Fin.sum_univ_two]
  simp

private theorem cocycle_mul_left_eq (F₁ F₂ : FormalGroup S) :
    let Δ := F₁.toPowerSeries - F₂.toPowerSeries
    let ω := F₂.invariantDifferential
    let Ψ := PowerSeries.subst F₂.toPowerSeries ω * Δ
    let F₁₂ := F₂.toPowerSeries.subst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) S)
    let F₂₃ := F₂.toPowerSeries.subst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) S)
    let Δ₁₂ := Δ.subst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) S)
    PowerSeries.subst (F₂.toPowerSeries.subst ![X 0, F₂₃]) ω *
        (Δ₁₂ * (pderiv 0 F₂.toPowerSeries).subst ![F₁₂, X 2] + Δ.subst ![F₁₂, X 2]) =
      Ψ.subst ![X 0, X 1] + Ψ.subst ![F₁₂, X 2] := by
  intro Δ ω Ψ F₁₂ F₂₃ Δ₁₂
  have hF₂ : PowerSeries.HasSubst F₂.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F₂.zero_constantCoeff
  have h01 : HasSubst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) S) := HasSubst.X_X
  have hF₁₂ : HasSubst (![F₁₂, X 2] : Fin 2 → MvPowerSeries (Fin 3) S) :=
    HasSubst.cons_subst_zero_left 0 1 2 F₂.zero_constantCoeff
  have hLω : PowerSeries.subst (F₂.toPowerSeries.subst ![X 0, F₂₃]) ω =
      (PowerSeries.subst F₂.toPowerSeries ω).subst ![F₁₂, X 2] := by
    rw [← F₂.assoc, subst_powerSeriesSubst hF₁₂ hF₂]
  rw [mul_add, hLω]
  congr 1
  · calc (PowerSeries.subst F₂.toPowerSeries ω).subst ![F₁₂, X 2] *
          (Δ₁₂ * (pderiv 0 F₂.toPowerSeries).subst ![F₁₂, X 2])
        = ((PowerSeries.subst F₂.toPowerSeries ω *
            pderiv 0 F₂.toPowerSeries).subst ![F₁₂, X 2]) * Δ₁₂ := by
          rw [subst_mul hF₁₂]; ring
      _ = (PowerSeries.subst (X 0) ω).subst ![F₁₂, X 2] * Δ₁₂ := by
          rw [F₂.subst_invariantDifferential_mul_pderiv]
      _ = PowerSeries.subst F₁₂ ω * Δ₁₂ := by
          rw [subst_powerSeriesSubst hF₁₂ (PowerSeries.HasSubst.X 0), subst_X hF₁₂,
            Matrix.cons_val_zero]
      _ = Ψ.subst ![X 0, X 1] := by
          rw [show Ψ = PowerSeries.subst F₂.toPowerSeries ω * Δ from rfl,
            subst_mul h01, subst_powerSeriesSubst h01 hF₂]
  · rw [show Ψ = PowerSeries.subst F₂.toPowerSeries ω * Δ from rfl, subst_mul hF₁₂]

private theorem cocycle_mul_right_eq (F₁ F₂ : FormalGroup S) [F₂.IsComm] :
    let Δ := F₁.toPowerSeries - F₂.toPowerSeries
    let ω := F₂.invariantDifferential
    let Ψ := PowerSeries.subst F₂.toPowerSeries ω * Δ
    let F₂₃ := F₂.toPowerSeries.subst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) S)
    let Δ₂₃ := Δ.subst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) S)
    PowerSeries.subst (F₂.toPowerSeries.subst ![X 0, F₂₃]) ω *
        (Δ₂₃ * (pderiv 1 F₂.toPowerSeries).subst ![X 0, F₂₃] + Δ.subst ![X 0, F₂₃]) =
      Ψ.subst ![X 0, F₂₃] + Ψ.subst ![X 1, X 2] := by
  intro Δ ω Ψ F₂₃ Δ₂₃
  have hF₂ : PowerSeries.HasSubst F₂.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F₂.zero_constantCoeff
  have h12 : HasSubst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) S) := HasSubst.X_X
  have hF₂₃ : HasSubst (![X 0, F₂₃] : Fin 2 → MvPowerSeries (Fin 3) S) :=
    HasSubst.cons_subst_zero_right 0 1 2 F₂.zero_constantCoeff
  have hRω : PowerSeries.subst (F₂.toPowerSeries.subst ![X 0, F₂₃]) ω =
      (PowerSeries.subst F₂.toPowerSeries ω).subst ![X 0, F₂₃] := by
    rw [subst_powerSeriesSubst hF₂₃ hF₂]
  rw [mul_add, hRω, add_comm (Ψ.subst ![X 0, F₂₃])]
  congr 1
  · calc (PowerSeries.subst F₂.toPowerSeries ω).subst ![X 0, F₂₃] *
          (Δ₂₃ * (pderiv 1 F₂.toPowerSeries).subst ![X 0, F₂₃])
        = ((PowerSeries.subst F₂.toPowerSeries ω *
            pderiv 1 F₂.toPowerSeries).subst ![X 0, F₂₃]) * Δ₂₃ := by
          rw [subst_mul hF₂₃]; ring
      _ = (PowerSeries.subst (X 1) ω).subst ![X 0, F₂₃] * Δ₂₃ := by
          rw [F₂.subst_invariantDifferential_mul_pderiv_one]
      _ = PowerSeries.subst F₂₃ ω * Δ₂₃ := by
          rw [subst_powerSeriesSubst hF₂₃ (PowerSeries.HasSubst.X 1), subst_X hF₂₃,
            Matrix.cons_val_one, Matrix.cons_val_fin_one]
      _ = Ψ.subst ![X 1, X 2] := by
          rw [show Ψ = PowerSeries.subst F₂.toPowerSeries ω * Δ from rfl,
            subst_mul h12, subst_powerSeriesSubst h12 hF₂]
  · rw [show Ψ = PowerSeries.subst F₂.toPowerSeries ω * Δ from rfl, subst_mul hF₂₃]

/-- **Square-zero deformation cocycle** (Lubin–Tate §1–§2): if two commutative formal group laws
`F₁` and `F₂` agree modulo a square-zero ideal `J`, then
`ω(F₂(X, Y)) · (F₁(X, Y) - F₂(X, Y))` is a symmetric 2-cocycle of `F₂`, where `ω` is the invariant
differential of `F₂`. -/
theorem isSymmetricCocycle_invariantDifferential_mul_sub (F₁ F₂ : FormalGroup S)
    [F₁.IsComm] [F₂.IsComm] {J : Ideal S} (hJ : J ^ 2 = ⊥)
    (hΔ : ∀ d, MvPowerSeries.coeff d (F₁.toPowerSeries - F₂.toPowerSeries) ∈ J) :
    F₂.IsSymmetricCocycle
      (PowerSeries.subst F₂.toPowerSeries F₂.invariantDifferential *
        (F₁.toPowerSeries - F₂.toPowerSeries)) := by
  have hF₂ : PowerSeries.HasSubst F₂.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F₂.zero_constantCoeff
  refine ⟨?_, ?_⟩
  · have hsw : HasSubst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) S) := HasSubst.X_X
    change (PowerSeries.subst F₂.toPowerSeries F₂.invariantDifferential *
        (F₁.toPowerSeries - F₂.toPowerSeries)).subst ![X 1, X 0] = _
    rw [subst_mul hsw, subst_powerSeriesSubst hsw hF₂, ← IsComm.comm (F := F₂),
      subst_sub hsw, ← IsComm.comm (F := F₁), ← IsComm.comm (F := F₂)]
  · have hassoc₁ := F₁.assoc
    rw [assoc_left_taylor_of_sq_eq_bot F₁ F₂ hJ hΔ,
      assoc_right_taylor_of_sq_eq_bot F₁ F₂ hJ hΔ, F₂.assoc, add_assoc, add_assoc] at hassoc₁
    have hdiff := congrArg
      (PowerSeries.subst (F₂.toPowerSeries.subst ![X 0, F₂.toPowerSeries.subst ![X 1, X 2]])
        F₂.invariantDifferential * ·)
      (add_left_cancel hassoc₁)
    rwa [cocycle_mul_left_eq F₁ F₂, cocycle_mul_right_eq F₁ F₂] at hdiff

private theorem powerSeries_subst_add_of_sq_eq_zero {τ S : Type*} [CommRing S]
    {a h : MvPowerSeries τ S} (ha : PowerSeries.HasSubst a) (hh : h ^ 2 = 0)
    (f : PowerSeries S) :
    PowerSeries.subst (a + h) f =
      PowerSeries.subst a f + h * PowerSeries.subst a (PowerSeries.derivative f) := by
  have hsub := subst_add_of_mul_eq_zero (σ := Unit) ha.const (h := fun _ ↦ h)
    (fun _ _ ↦ by simpa [sq] using hh) (f : MvPowerSeries Unit S)
  rw [PowerSeries.subst_def, PowerSeries.subst_def, PowerSeries.subst_def, PowerSeries.derivative]
  convert hsub using 2; simp

private theorem subst_pair_inv_ofSquareZero (F : FormalGroup S)
    {J : Ideal S} (hJ : J ^ 2 = ⊥) (h : PowerSeries S) (hh₀ : PowerSeries.constantCoeff h = 0)
    (hh : ∀ n, PowerSeries.coeff n h ∈ J) :
    let φ := FormalCoordinate.ofSquareZero hJ h hh₀ hh
    F.toPowerSeries.subst
        ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries,
          PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries] =
      F.toPowerSeries - PowerSeries.subst (X 0) h * pderiv 0 F.toPowerSeries -
        PowerSeries.subst (X 1) h * pderiv 1 F.toPowerSeries := by
  intro φ
  have hh_mem : ∀ (i : Fin 2) d,
      coeff d (PowerSeries.subst (X i : MvPowerSeries (Fin 2) S) h) ∈ J := fun i d ↦
    coeff_powerSeries_subst_mem_of_coeff_mem hh (PowerSeries.HasSubst.X i) d
  have hmul_zero : ∀ i j : Fin 2,
      ![-PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) h,
        -PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) h] i *
      ![-PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) h,
        -PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) h] j = 0 := fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      exact mvPowerSeries_mul_eq_zero_of_coeff_mem hJ
        (fun d ↦ by simpa using J.neg_mem (hh_mem _ d))
        (fun d ↦ by simpa using J.neg_mem (hh_mem _ d))
  have hφinv : φ⁻¹.toPowerSeries = PowerSeries.X - h := by
    rw [show φ⁻¹ = FormalCoordinate.ofSquareZero hJ (-h) (by simp [hh₀])
      (fun n ↦ J.neg_mem (hh n)) from FormalCoordinate.inv_ofSquareZero hJ h hh₀ hh]
    exact (sub_eq_add_neg PowerSeries.X h).symm
  have harg :
      (![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries,
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries] :
        Fin 2 → MvPowerSeries (Fin 2) S) =
        ![X 0, X 1] + ![-PowerSeries.subst (X 0) h, -PowerSeries.subst (X 1) h] := by
    funext i; fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.add_apply]
      rw [hφinv, PowerSeries.subst_sub (PowerSeries.HasSubst.X 0),
        PowerSeries.subst_X (PowerSeries.HasSubst.X 0), sub_eq_add_neg]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply]
      rw [hφinv, PowerSeries.subst_sub (PowerSeries.HasSubst.X 1),
        PowerSeries.subst_X (PowerSeries.HasSubst.X 1), sub_eq_add_neg]
  rw [harg, subst_add_of_mul_eq_zero HasSubst.X_X hmul_zero, finTwo_X_eq_X,
    subst_self, id_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, id_eq]
  ring

private theorem smul_sub_ofSquareZero (F : FormalGroup S)
    {J : Ideal S} (hJ : J ^ 2 = ⊥) (h : PowerSeries S) (hh₀ : PowerSeries.constantCoeff h = 0)
    (hh : ∀ n, PowerSeries.coeff n h ∈ J) :
    ((FormalCoordinate.ofSquareZero hJ h hh₀ hh) • F).toPowerSeries - F.toPowerSeries =
      PowerSeries.subst F.toPowerSeries h -
        PowerSeries.subst (X 0) h * pderiv 0 F.toPowerSeries -
        PowerSeries.subst (X 1) h * pderiv 1 F.toPowerSeries := by
  set φ := FormalCoordinate.ofSquareZero hJ h hh₀ hh
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hh_mem : ∀ (i : Fin 2) d,
      coeff d (PowerSeries.subst (X i : MvPowerSeries (Fin 2) S) h) ∈ J := fun i d ↦
    coeff_powerSeries_subst_mem_of_coeff_mem hh (PowerSeries.HasSubst.X i) d
  set δ := -PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) h * pderiv 0 F.toPowerSeries -
    PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) h * pderiv 1 F.toPowerSeries
  have hδmem : ∀ d, coeff d δ ∈ J := fun d ↦ by
    have hmul : ∀ i : Fin 2,
        coeff d (PowerSeries.subst (X i : MvPowerSeries (Fin 2) S) h * pderiv i F.toPowerSeries) ∈
          J := fun i ↦ by
      rw [coeff_mul]
      exact Ideal.sum_mem _ fun p _ ↦ J.mul_mem_right _ (hh_mem i p.1)
    rw [show δ = -(PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) h * pderiv 0 F.toPowerSeries) +
        -(PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) h * pderiv 1 F.toPowerSeries) by
      simp only [δ]; ring]
    rw [map_add (coeff d), map_neg (coeff d), map_neg (coeff d)]
    exact J.add_mem (J.neg_mem (hmul 0)) (J.neg_mem (hmul 1))
  have hδsq : δ ^ 2 = 0 := by rw [sq]; exact mvPowerSeries_mul_eq_zero_of_coeff_mem hJ hδmem hδmem
  have hFδ : PowerSeries.HasSubst (F.toPowerSeries + δ) := by
    refine hF.add (PowerSeries.HasSubst.of_constantCoeff_zero ?_)
    have h0 : constantCoeff (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) h) = 0 := by
      rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero (constantCoeff_X 0) h, hh₀,
        map_zero]
    have h1 : constantCoeff (PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) h) = 0 := by
      rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero (constantCoeff_X 1) h, hh₀,
        map_zero]
    simp [δ, h0, h1]
  rw [smul_toPowerSeries, subst_pair_inv_ofSquareZero F hJ h hh₀ hh, show F.toPowerSeries -
      PowerSeries.subst (X 0) h * pderiv 0 F.toPowerSeries -
      PowerSeries.subst (X 1) h * pderiv 1 F.toPowerSeries = F.toPowerSeries + δ by
    simp [δ]; ring]
  have hsub_add : PowerSeries.subst (F.toPowerSeries + δ) φ.toPowerSeries =
      F.toPowerSeries + δ + PowerSeries.subst (F.toPowerSeries + δ) h := by
    rw [FormalCoordinate.toPowerSeries_ofSquareZero, PowerSeries.subst_add hFδ,
      PowerSeries.subst_X hFδ]
  have hkill : δ * PowerSeries.subst F.toPowerSeries (PowerSeries.derivative h) = 0 :=
    mvPowerSeries_mul_eq_zero_of_coeff_mem hJ hδmem fun d ↦
      coeff_powerSeries_subst_mem_of_coeff_mem (fun n ↦ by
        rw [PowerSeries.coeff_derivative]; exact J.mul_mem_right _ (hh (n + 1))) hF d
  rw [hsub_add, powerSeries_subst_add_of_sq_eq_zero hF hδsq h, hkill, _root_.add_zero]
  simp only [δ]; ring

/-- **Square-zero coordinate changes yield coboundaries**: if `φ = X + h` is a coordinate change
whose nonlinear perturbation `h` has zero constant term and coefficients in a square-zero ideal
`J`, then `ω(F(X, Y)) · ((φ • F)(X, Y) - F(X, Y)) = F.homDefect 𝔾ₐ (ω · h)` for any commutative
formal group law `F`. -/
theorem invariantDifferential_mul_smul_sub_eq_homDefect_𝔾ₐ (F : FormalGroup S) [F.IsComm]
    {J : Ideal S} (hJ : J ^ 2 = ⊥) (h : PowerSeries S) (hh₀ : PowerSeries.constantCoeff h = 0)
    (hh : ∀ n, PowerSeries.coeff n h ∈ J) :
    PowerSeries.subst F.toPowerSeries F.invariantDifferential *
        (((FormalCoordinate.ofSquareZero hJ h hh₀ hh) • F).toPowerSeries - F.toPowerSeries) =
      F.homDefect 𝔾ₐ (F.invariantDifferential * h) := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  rw [smul_sub_ofSquareZero F hJ h hh₀ hh, mul_sub, mul_sub, ← PowerSeries.subst_mul hF,
    ← mul_assoc, ← mul_assoc, mul_right_comm (PowerSeries.subst F.toPowerSeries _),
    F.subst_invariantDifferential_mul_pderiv, mul_right_comm (PowerSeries.subst F.toPowerSeries _),
    F.subst_invariantDifferential_mul_pderiv_one,
    ← PowerSeries.subst_mul (PowerSeries.HasSubst.X 0),
    ← PowerSeries.subst_mul (PowerSeries.HasSubst.X 1), homDefect_𝔾ₐ]

private theorem coeff_inv_sub_X_mem (φ : FormalCoordinate S) {I : Ideal S}
    (hφ : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I) (n : ℕ) :
    PowerSeries.coeff n (φ⁻¹.toPowerSeries - PowerSeries.X) ∈ I := by
  have hmap : FormalCoordinate.map (Ideal.Quotient.mk I) φ = 1 := by
    ext m
    rw [FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_one,
      ← PowerSeries.map_X (Ideal.Quotient.mk I), PowerSeries.coeff_map, PowerSeries.coeff_map,
      ← sub_eq_zero, ← map_sub, ← map_sub (PowerSeries.coeff m), Ideal.Quotient.eq_zero_iff_mem]
    exact hφ m
  have hinv_map : FormalCoordinate.map (Ideal.Quotient.mk I) φ⁻¹ = 1 := by
    rw [map_inv, hmap, inv_one]
  have hm := congrArg (PowerSeries.coeff n ∘ FormalCoordinate.toPowerSeries) hinv_map
  simp only [Function.comp_apply, FormalCoordinate.toPowerSeries_map,
    FormalCoordinate.toPowerSeries_one] at hm
  rw [← PowerSeries.map_X (Ideal.Quotient.mk I), PowerSeries.coeff_map, PowerSeries.coeff_map,
    ← sub_eq_zero, ← map_sub, ← map_sub (PowerSeries.coeff n), Ideal.Quotient.eq_zero_iff_mem] at hm
  exact hm

private theorem subst_diff_eq_diff_of_mul_eq_bot (φ : FormalCoordinate S) (F₁ F₂ : FormalGroup S)
    {I J : Ideal S} (hIJ : I * J = ⊥)
    (hφ : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I)
    (hΔ : ∀ d, coeff d (F₁.toPowerSeries - F₂.toPowerSeries) ∈ J) :
    (F₁.toPowerSeries - F₂.toPowerSeries).subst
        ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries,
          PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries] =
      F₁.toPowerSeries - F₂.toPowerSeries := by
  have hφinv := coeff_inv_sub_X_mem φ hφ
  have hux : HasSubst
      (![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries,
         PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries] :
        Fin 2 → MvPowerSeries (Fin 2) S) :=
    hasSubst_of_constantCoeff_zero fun i ↦ by
      fin_cases i <;>
        exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
          φ⁻¹.constantCoeff_toPowerSeries
  have hX : (F₁.toPowerSeries - F₂.toPowerSeries).subst ![X 0, X 1] =
      F₁.toPowerSeries - F₂.toPowerSeries := by
    rw [finTwo_X_eq_X, subst_self]; rfl
  conv_rhs => rw [← hX]
  refine subst_eq_subst_of_coeff_mem hux HasSubst.X_X (J := I) (fun i e ↦ ?_) fun d x hx ↦ ?_
  · fin_cases i
    · change coeff e (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries -
          X 0) ∈ I
      rw [show PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries - X 0 =
          PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S)
            (φ⁻¹.toPowerSeries - PowerSeries.X) by
        rw [PowerSeries.subst_sub (PowerSeries.HasSubst.X 0),
          PowerSeries.subst_X (PowerSeries.HasSubst.X 0)]]
      exact coeff_powerSeries_subst_mem_of_coeff_mem hφinv (PowerSeries.HasSubst.X 0) e
    · change coeff e (PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries -
          X 1) ∈ I
      rw [show PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries - X 1 =
          PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S)
            (φ⁻¹.toPowerSeries - PowerSeries.X) by
        rw [PowerSeries.subst_sub (PowerSeries.HasSubst.X 1),
          PowerSeries.subst_X (PowerSeries.HasSubst.X 1)]]
      exact coeff_powerSeries_subst_mem_of_coeff_mem hφinv (PowerSeries.HasSubst.X 1) e
  · rw [← Ideal.mem_bot, ← hIJ, mul_comm]
    exact Ideal.mul_mem_mul (hΔ d) hx

/-- **Invariance of square-zero differences under coordinate changes `≡ X (mod I)`**:
if `φ` reduces to `X` modulo `I`, `F₁ - F₂` has coefficients in `J`, and `I * J = ⊥` and
`J ^ 2 = ⊥`, then `(φ • F₁) - (φ • F₂) = F₁ - F₂`. -/
theorem smul_sub_smul_eq_of_mul_eq_bot (φ : FormalCoordinate S) (F₁ F₂ : FormalGroup S)
    {I J : Ideal S} (hIJ : I * J = ⊥) (hJ : J ^ 2 = ⊥)
    (hφ : ∀ n, PowerSeries.coeff n (φ.toPowerSeries - PowerSeries.X) ∈ I)
    (hΔ : ∀ d, coeff d (F₁.toPowerSeries - F₂.toPowerSeries) ∈ J) :
    (φ • F₁).toPowerSeries - (φ • F₂).toPowerSeries = F₁.toPowerSeries - F₂.toPowerSeries := by
  set Δ := F₁.toPowerSeries - F₂.toPowerSeries
  set u : Fin 2 → MvPowerSeries (Fin 2) S :=
    ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) S) φ⁻¹.toPowerSeries]
  have hux : HasSubst u :=
    hasSubst_of_constantCoeff_zero fun i ↦ by
      fin_cases i <;>
        exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) _
          φ⁻¹.constantCoeff_toPowerSeries
  have hΔeq := subst_diff_eq_diff_of_mul_eq_bot φ F₁ F₂ hIJ hφ hΔ
  have hF₁_eq : F₁.toPowerSeries.subst u = F₂.toPowerSeries.subst u + Δ := by
    rw [show Δ = F₁.toPowerSeries - F₂.toPowerSeries from rfl, ← hΔeq, ← subst_add hux]
    congr 1; ring
  have hF₂u : PowerSeries.HasSubst (F₂.toPowerSeries.subst u) :=
    F₂.hasSubst_subst_pair
      (φ⁻¹.hasSubst_subst (PowerSeries.HasSubst.X 0))
      (φ⁻¹.hasSubst_subst (PowerSeries.HasSubst.X 1))
  have hΔsq : Δ ^ 2 = 0 := by rw [sq]; exact mvPowerSeries_mul_eq_zero_of_coeff_mem hJ hΔ hΔ
  have hkill : Δ * PowerSeries.subst (F₂.toPowerSeries.subst u)
      (PowerSeries.derivative (φ.toPowerSeries - PowerSeries.X)) = 0 :=
    mvPowerSeries_mul_eq_zero_of_mul_eq_bot (mul_comm I J ▸ hIJ) hΔ fun d ↦
      coeff_powerSeries_subst_mem_of_coeff_mem (fun n ↦ by
        rw [PowerSeries.coeff_derivative]; exact I.mul_mem_right _ (hφ (n + 1))) hF₂u d
  have hderiv : PowerSeries.subst (F₂.toPowerSeries.subst u)
      (PowerSeries.derivative φ.toPowerSeries) =
      1 + PowerSeries.subst (F₂.toPowerSeries.subst u)
        (PowerSeries.derivative (φ.toPowerSeries - PowerSeries.X)) := by
    rw [show PowerSeries.derivative φ.toPowerSeries =
        1 + PowerSeries.derivative (φ.toPowerSeries - PowerSeries.X) by
      rw [map_sub, PowerSeries.derivative_X]; ring, PowerSeries.subst_add hF₂u,
      PowerSeries.subst_one]
  rw [smul_toPowerSeries, smul_toPowerSeries]
  change PowerSeries.subst (F₁.toPowerSeries.subst u) φ.toPowerSeries -
      PowerSeries.subst (F₂.toPowerSeries.subst u) φ.toPowerSeries = Δ
  rw [hF₁_eq, powerSeries_subst_add_of_sq_eq_zero hF₂u hΔsq φ.toPowerSeries, hderiv, mul_add,
    mul_one, hkill, _root_.add_zero, add_sub_cancel_left]

end SquareZeroCocycle

end FormalGroup
