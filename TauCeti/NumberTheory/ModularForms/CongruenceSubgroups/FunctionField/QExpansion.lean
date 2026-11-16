/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Fricke
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.SpecialFunctions.Elliptic.TateUniformization
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import TauCeti.NumberTheory.ModularForms.QExpansion.Order
import TauCeti.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Cyclotomic `q`-expansions of Fricke functions

For a nonzero residue vector `a ∈ (ℤ/Nℤ)²`, the weight-two division value
`(2πi)⁻² N⁻² ℘((a₀ τ + a₁) / N; ℤ τ + ℤ)` is expanded in the local parameter
`q_N = exp (2πi τ / N)` via the complex Tate uniformization
(`UpperHalfPlane.tateUniformizationX_eq_weierstrassP` and
`TauCeti.tateUniformizationX_eq_tsum_nat`). Grouping the bilateral Tate series into the positive
integers congruent to `± a₀` modulo `N` and expanding each rational term
`w / (1 - w)² = ∑_{m ≥ 1} m wᵐ` yields an explicit formula for the `n`-th coefficient in `q_N`
(`TauCeti.qExpansion_weightedG2_single_div_coeff`). Every coefficient lies in the `N`-th cyclotomic
field `ℚ(ζ_N)`, and any endomorphism of `ℚ(ζ_N)` raising `ζ_N = exp (2πi / N)` to the power
`d ∈ (ℤ/Nℤ)ˣ` sends the expansion for `a` to the expansion for `a · diag(1, d)`.

Multiplying by the level-one factor `E₄ E₆ / Δ`, whose Laurent expansion in `q_N` has integer
coefficients, shows that every Fricke function `f_a` lies in the arithmetic modular function field
`F_N` (`TauCeti.frickeMeromorphicFunction_mem_modularFunctionField`) and that its Laurent
`q_N`-expansion is equivariant for the diagonal matrices `diag(1, d)`
(`TauCeti.map_laurentQExpansion_frickeMeromorphicFunction_coeff`).

## Main declarations

* `TauCeti.cexp_two_pi_I_div_mem_cyclotomic`: `exp (2πi / N) ∈ ℚ(ζ_N)`.
* `TauCeti.qExpansion_weightedG2_single_div_coeff`: explicit `q_N`-expansion coefficients of
  `(2πi)⁻² G₂^{a}` for `a ≠ 0`.
* `TauCeti.qExpansion_weightedG2_single_div_coeff_mem_cyclotomic` and
  `TauCeti.map_qExpansion_weightedG2_single_div_coeff`: cyclotomic rationality and diagonal
  equivariance of the `q_N`-expansion of `(2πi)⁻² G₂^{a}`.
* `TauCeti.laurentQExpansion_frickeMeromorphicFunction`: Laurent `q_N`-expansion of `f_a`.
* `TauCeti.frickeMeromorphicFunction_mem_modularFunctionField`: `f_a ∈ F_N`.
* `TauCeti.map_laurentQExpansion_frickeMeromorphicFunction_coeff`: cyclotomic equivariance of the
  Laurent `q_N`-expansion of `f_a` under `diag(1, d)`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1.
* Serge Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 6, §§2–3.
-/

public noncomputable section

open CongruenceSubgroup Filter PeriodPair UpperHalfPlane
open Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open scoped ArithmeticFunction.sigma Matrix MatrixGroups Real

namespace TauCeti

/-! ### Explicit `q_N`-expansion of the weight-two division values -/

/-- The primitive `N`-th root of unity `exp (2πi / N)` lies in `ℚ(ζ_N)`. -/
theorem cexp_two_pi_I_div_mem_cyclotomic (N : ℕ) :
    Complex.exp (2 * π * Complex.I / N) ∈ Subfield.closure {z : ℂ | z ^ N = 1} := by
  by_cases hN : N = 0
  · subst hN
    exact Subfield.subset_closure (pow_zero _)
  · exact Subfield.subset_closure (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

variable {N : ℕ} [NeZero N]

/-- Raising `exp (2πi / N)` to a natural power depends only on the exponent modulo `N`. -/
private theorem cexp_two_pi_I_div_pow_eq_of_modEq {m n : ℕ} (h : m ≡ n [MOD N]) :
    Complex.exp (2 * π * Complex.I / N) ^ m = Complex.exp (2 * π * Complex.I / N) ^ n := by
  have hζ : Complex.exp (2 * π * Complex.I / N) ^ N = 1 :=
    (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).pow_eq_one
  have hpow (k : ℕ) : Complex.exp (2 * π * Complex.I / N) ^ k =
      Complex.exp (2 * π * Complex.I / N) ^ (k % N) := by
    conv_lhs => rw [← Nat.div_add_mod k N, pow_add, pow_mul, hζ, one_pow, one_mul]
  rw [hpow m, hpow n, h]

/-- The inverse of `exp (2πi / N) ^ b.val` is `exp (2πi / N) ^ (-b).val`. -/
private theorem inv_cexp_two_pi_I_div_pow (b : ZMod N) :
    (Complex.exp (2 * π * Complex.I / N) ^ b.val)⁻¹ =
      Complex.exp (2 * π * Complex.I / N) ^ (-b).val := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add, ← pow_zero (Complex.exp (2 * π * Complex.I / N))]
  refine cexp_two_pi_I_div_pow_eq_of_modEq ?_
  rw [Nat.ModEq, Nat.zero_mod, ← ZMod.val_natCast]
  simp

omit [NeZero N] in
/-- The norm of `exp (2πi / N) ^ k` is `1`. -/
private theorem norm_cexp_two_pi_I_div_pow (k : ℕ) :
    ‖Complex.exp (2 * π * Complex.I / N) ^ k‖ = 1 := by
  have h : ‖Complex.exp (2 * π * Complex.I / N)‖ = 1 := by
    rw [show (2 * π * Complex.I / N : ℂ) = ((2 * π / N : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [norm_pow, h, one_pow]

omit [NeZero N] in
/-- Regrouping a residue-restricted Lambert series into a power series in `q`:
`∑_{d ≥ 1, d ≡ c (N)} q^d u / (1 - q^d u)² = ∑_{n ≥ 0} (∑_{d m = n, d ≡ c (N)} m u^m) q^n`. -/
private theorem hasSum_residueLambert {c : ZMod N} {q u : ℂ} (hq : ‖q‖ < 1) (hu : ‖u‖ = 1) :
    HasSum
      (fun n : ℕ ↦
        (∑ x ∈ n.divisorsAntidiagonal, if (x.1 : ZMod N) = c then (x.2 : ℂ) * u ^ x.2 else 0) *
          q ^ n)
      (∑' d : ℕ+, if (d : ZMod N) = c then q ^ (d : ℕ) * u / (1 - q ^ (d : ℕ) * u) ^ 2 else 0) := by
  let F : ℕ+ × ℕ+ → ℂ := fun p ↦
    if ((p.1 : ℕ) : ZMod N) = c then (p.2 : ℂ) * u ^ (p.2 : ℕ) * q ^ ((p.1 : ℕ) * p.2) else 0
  have hF_sum : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ℕ+ × ℕ+ ↦ (p.2 : ℝ) * ‖q‖ ^ ((p.1 : ℕ) * p.2))
      (by simpa using summable_prod_mul_pow 1 (r := ‖q‖) (by simpa using hq)) fun p ↦ ?_
    dsimp only [F]
    split_ifs
    · rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, hu, one_pow, mul_one]
    · rw [norm_zero]
      positivity
  have htsum : ∑' p : ℕ+ × ℕ+, F p =
      ∑' d : ℕ+, if (d : ZMod N) = c then q ^ (d : ℕ) * u / (1 - q ^ (d : ℕ) * u) ^ 2 else 0 := by
    rw [hF_sum.tsum_prod]
    refine tsum_congr fun d ↦ ?_
    dsimp only [F]
    split_ifs with hd
    · set w := q ^ (d : ℕ) * u
      have hw : ‖w‖ < 1 := by
        rw [norm_mul, norm_pow, hu, mul_one]
        exact pow_lt_one₀ (norm_nonneg q) hq d.ne_zero
      have hgeom := hasSum_coe_mul_geometric_of_norm_lt_one hw
      rw [← hasSum_nat_add_iff' 1] at hgeom
      simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, pow_zero, zero_mul,
        sub_zero] at hgeom
      rw [← hasSum_pnat_iff_hasSum_succ (f := fun m : ℕ ↦ (m : ℂ) * w ^ m)] at hgeom
      refine (hgeom.congr_fun fun m ↦ ?_).tsum_eq
      simp only [w, mul_pow, ← pow_mul]
      ring
    · simp
  have hanti := hF_sum.hasSum.sum_divisorsAntidiagonal
    (f := fun d m ↦ if (d : ZMod N) = c then (m : ℂ) * u ^ m * q ^ (d * m) else 0)
  rw [htsum] at hanti
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.divisorsAntidiagonal_zero,
    Finset.sum_empty, zero_mul, sub_zero]
  rw [← hasSum_pnat_iff_hasSum_succ
    (f := fun n : ℕ ↦ (∑ x ∈ n.divisorsAntidiagonal,
      if (x.1 : ZMod N) = c then (x.2 : ℂ) * u ^ x.2 else 0) * q ^ n)]
  refine hanti.congr_fun fun n ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  split_ifs
  · rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  · rw [zero_mul]

/-- The positive integers congruent to `c` modulo `N`, enumerated by `ℕ`. -/
private def residueEnum (c : ZMod N) (n : ℕ) : ℕ+ :=
  if hc : c = 0 then ⟨(n + 1) * N, Nat.mul_pos (Nat.succ_pos n) (NeZero.pos N)⟩
  else ⟨n * N + c.val, Nat.add_pos_right _ (Nat.pos_of_ne_zero (by simpa [ZMod.val_eq_zero]))⟩

private theorem residueEnum_injective (c : ZMod N) : Function.Injective (residueEnum c) := by
  intro m n h
  have hval := congrArg PNat.val h
  by_cases hc : c = 0
  · simp only [residueEnum, hc, ↓reduceDIte, PNat.mk_coe] at hval
    exact Nat.succ_injective (Nat.eq_of_mul_eq_mul_right (NeZero.pos N) hval)
  · simp only [residueEnum, hc, ↓reduceDIte, PNat.mk_coe] at hval
    exact Nat.eq_of_mul_eq_mul_right (NeZero.pos N) (Nat.add_right_cancel hval)

private theorem mem_range_residueEnum_iff (c : ZMod N) (d : ℕ+) :
    d ∈ Set.range (residueEnum c) ↔ ((d : ℕ) : ZMod N) = c := by
  constructor
  · rintro ⟨n, rfl⟩
    dsimp only [residueEnum]
    split_ifs with hc <;> simp [hc]
  · intro hd
    have hmod : (d : ℕ) % N = c.val := by
      rw [← ZMod.val_natCast, hd]
    have hdiv : (d : ℕ) / N * N + c.val = (d : ℕ) := by
      rw [← hmod, mul_comm, Nat.div_add_mod]
    by_cases hc : c = 0
    · have hq : 0 < (d : ℕ) / N := by
        by_contra h0
        have h0' : (d : ℕ) / N = 0 := Nat.eq_zero_of_not_pos h0
        simp [h0', hc] at hdiv
        exact d.ne_zero hdiv.symm
      refine ⟨(d : ℕ) / N - 1, PNat.eq ?_⟩
      simp only [residueEnum, hc, ↓reduceDIte, PNat.mk_coe, Nat.sub_add_cancel hq]
      simpa [hc] using hdiv
    · refine ⟨(d : ℕ) / N, PNat.eq ?_⟩
      simp only [residueEnum, hc, ↓reduceDIte, PNat.mk_coe]
      exact hdiv

/-- Reindexing a residue-class sum over `ℕ+` along `residueEnum`. -/
private theorem tsum_ite_residue_eq_tsum_nat (c : ZMod N) (g : ℕ+ → ℂ) :
    (∑' d : ℕ+, if ((d : ℕ) : ZMod N) = c then g d else 0) =
      ∑' n : ℕ, g (residueEnum c n) := by
  have h := Function.Injective.tsum_eq
    (f := fun d : ℕ+ ↦ if ((d : ℕ) : ZMod N) = c then g d else 0)
    (residueEnum_injective c) (fun d hd ↦ (mem_range_residueEnum_iff c d).mpr (by
      by_contra hne
      exact hd (by simp [hne])))
  rw [← h]
  refine tsum_congr fun n ↦ ?_
  have hr : ((residueEnum c n : ℕ) : ZMod N) = c :=
    (mem_range_residueEnum_iff c _).mp ⟨n, rfl⟩
  simp [hr]

/-- Reindexing the positive-exponent Tate sum at `q = q_N^N`, `t = q_N^{a₀} ζ^{a₁}`. -/
private theorem tateX_pos_eq_residueLambert {a : Fin 2 → ZMod N} {qN ζ : ℂ} (hqN : ‖qN‖ < 1) :
    let q := qN ^ N
    let t := qN ^ (a 0).val * ζ ^ (a 1).val
    t / (1 - t) ^ 2 + ∑' n : ℕ, q ^ (n + 1) * t / (1 - q ^ (n + 1) * t) ^ 2 =
      (if a 0 = 0 then ζ ^ (a 1).val / (1 - ζ ^ (a 1).val) ^ 2 else 0) +
        ∑' d : ℕ+, if ((d : ℕ) : ZMod N) = a 0 then
          qN ^ (d : ℕ) * ζ ^ (a 1).val / (1 - qN ^ (d : ℕ) * ζ ^ (a 1).val) ^ 2 else 0 := by
  intro q t
  rw [tsum_ite_residue_eq_tsum_nat (a 0)]
  by_cases ha0 : a 0 = 0
  · simp only [ha0, ↓reduceIte, ZMod.val_zero, pow_zero, one_mul, t, q]
    congr 1
    refine tsum_congr fun n ↦ ?_
    simp [residueEnum, ← pow_mul, mul_comm]
  · simp only [ha0, ↓reduceIte, zero_add]
    have hterm (n : ℕ) :
        qN ^ (residueEnum (a 0) n : ℕ) * ζ ^ (a 1).val = q ^ n * t := by
      simp only [residueEnum, ha0, ↓reduceDIte, PNat.mk_coe, q, t, pow_add, ← pow_mul,
        mul_comm n N, mul_assoc]
    have hq_norm : ‖q‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hqN (NeZero.ne N)
    have hsum_nat : Summable fun n : ℕ ↦ q ^ n * t / (1 - q ^ n * t) ^ 2 := by
      rw [← summable_nat_add_iff 1]
      exact summable_tateUniformizationX_nat q hq_norm t
    conv_rhs => rw [tsum_congr fun n ↦ by rw [hterm n]]
    rw [hsum_nat.tsum_eq_zero_add]
    simp

/-- Reindexing the negative-exponent Tate sum at `q = q_N^N`, `t = q_N^{a₀} ζ^{a₁}`. -/
private theorem tateX_neg_eq_residueLambert {a : Fin 2 → ZMod N} {qN : ℂ} (hqN_ne : qN ≠ 0) :
    let q := qN ^ N
    let ζ := Complex.exp (2 * π * Complex.I / N)
    let t := qN ^ (a 0).val * ζ ^ (a 1).val
    (∑' n : ℕ, q ^ (n + 1) * t⁻¹ / (1 - q ^ (n + 1) * t⁻¹) ^ 2) =
      ∑' d : ℕ+, if ((d : ℕ) : ZMod N) = -a 0 then
        qN ^ (d : ℕ) * ζ ^ (-a 1).val / (1 - qN ^ (d : ℕ) * ζ ^ (-a 1).val) ^ 2 else 0 := by
  intro q ζ t
  rw [tsum_ite_residue_eq_tsum_nat (-a 0)]
  refine tsum_congr fun n ↦ ?_
  have hpow : q ^ (n + 1) * t⁻¹ = qN ^ (residueEnum (-a 0) n : ℕ) * ζ ^ (-a 1).val := by
    have hexp : N * (n + 1) = (residueEnum (-a 0) n : ℕ) + (a 0).val := by
      dsimp only [residueEnum]
      by_cases ha0 : a 0 = 0
      · simp [ha0, mul_comm]
      · have hneg0 : -a 0 ≠ 0 := neg_ne_zero.mpr ha0
        have hlt : (a 0).val < N := ZMod.val_lt (a 0)
        have hlt' : (-a 0).val < N := ZMod.val_lt (-a 0)
        have hpos : 0 < (a 0).val := Nat.pos_of_ne_zero (by simpa [ZMod.val_eq_zero])
        have hpos' : 0 < (-a 0).val := Nat.pos_of_ne_zero (by simpa [ZMod.val_eq_zero])
        have hmod : ((a 0).val + (-a 0).val) % N = 0 := by
          rw [← ZMod.val_natCast]
          simp
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
        have hk1 : k = 1 := by
          rcases k with _ | _ | k
          · rw [mul_zero] at hk; omega
          · rfl
          · nlinarith
        have hval : (-a 0).val = N - (a 0).val := by rw [hk1, mul_one] at hk; omega
        simp only [hneg0, ↓reduceDIte, PNat.mk_coe, hval]
        rw [Nat.mul_succ, mul_comm n N]
        omega
    simp only [q, t, ← pow_mul, mul_inv]
    rw [hexp, pow_add, mul_assoc, mul_left_comm (qN ^ (a 0).val),
      inv_mul_cancel_left₀ (pow_ne_zero _ hqN_ne), inv_cexp_two_pi_I_div_pow]
  rw [hpow]

/-- Expressing `℘((a₀ τ + a₁)/N) / (2πi)²` at a nonzero `N`-torsion point via residue-restricted
Lambert sums in `q_N`. -/
private theorem weierstrassP_div_eq_residueLambert {a : Fin 2 → ZMod N} (ha : a ≠ 0) (τ : ℍ) :
    ℘[τ.periodPair] (((a 0).val * (τ : ℂ) + (a 1).val) / N) / (2 * π * Complex.I) ^ 2 =
      (1 / 12 + if a 0 = 0 then
          Complex.exp (2 * π * Complex.I / N) ^ (a 1).val /
            (1 - Complex.exp (2 * π * Complex.I / N) ^ (a 1).val) ^ 2
        else 0) +
      (∑' d : ℕ+, if ((d : ℕ) : ZMod N) = a 0 then
        Function.Periodic.qParam N (τ : ℂ) ^ (d : ℕ) *
            Complex.exp (2 * π * Complex.I / N) ^ (a 1).val /
          (1 - Function.Periodic.qParam N (τ : ℂ) ^ (d : ℕ) *
            Complex.exp (2 * π * Complex.I / N) ^ (a 1).val) ^ 2 else 0) +
      (∑' d : ℕ+, if ((d : ℕ) : ZMod N) = -a 0 then
        Function.Periodic.qParam N (τ : ℂ) ^ (d : ℕ) *
            Complex.exp (2 * π * Complex.I / N) ^ (-a 1).val /
          (1 - Function.Periodic.qParam N (τ : ℂ) ^ (d : ℕ) *
            Complex.exp (2 * π * Complex.I / N) ^ (-a 1).val) ^ 2 else 0) -
      2 * divisorSumAt 1 (Function.Periodic.qParam N (τ : ℂ) ^ N) := by
  set qN := Function.Periodic.qParam N (τ : ℂ)
  set ζ := Complex.exp (2 * π * Complex.I / N)
  set x : ℂ := ((a 0).val * (τ : ℂ) + (a 1).val) / N
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hx : x ∉ τ.periodPair.lattice := by
    intro h
    have he := intCast_comp_eq_zero_of_div_mem_lattice_periodPair
      (b := fun i ↦ ((a i).val : ℤ)) (by simpa [x] using h)
    exact ha (funext fun i ↦ by simpa using congrFun he i)
  have hqN_ne : qN ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hqN_pow : qN ^ N = Complex.exp (2 * π * Complex.I * τ) := by
    simp only [qN, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hqN_norm : ‖qN‖ < 1 := by
    rw [Function.Periodic.norm_qParam]
    exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos
      (by nlinarith [Real.pi_pos, τ.2]) (Nat.cast_pos.mpr (NeZero.pos N)))
  have hq_norm : ‖qN ^ N‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hqN_norm (NeZero.ne N)
  have ht : Complex.exp (2 * π * Complex.I * x) = qN ^ (a 0).val * ζ ^ (a 1).val := by
    simp only [qN, ζ, x, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  set qU : ℂˣ := Units.mk0 (qN ^ N) (pow_ne_zero N hqN_ne)
  set tU : ℂˣ := Units.mk0 (Complex.exp (2 * π * Complex.I * x)) (Complex.exp_ne_zero _)
  have hX := UpperHalfPlane.tateUniformizationX_eq_weierstrassP τ hx
    (q := qU) (t := tU) (by simp [qU, hqN_pow]) (by simp [tU])
  have hnat := tateUniformizationX_eq_tsum_nat qU (by simpa [qU] using hq_norm) tU
  have hpos := tateX_pos_eq_residueLambert (a := a) (ζ := ζ) hqN_norm
  have hneg := tateX_neg_eq_residueLambert (a := a) hqN_ne
  have hcomb :
      ℘[τ.periodPair] x / (2 * π * Complex.I) ^ 2 = tateUniformizationX qU tU + 1 / 12 := by
    linear_combination -hX
  rw [hcomb, hnat]
  simp only [qU, tU, Units.val_mk0, ht]
  rw [hpos, hneg]
  ring

/-- Reindexing the divisor-sum Lambert series `divisorSumAt 1 (q ^ N)` as a power series in `q`. -/
private theorem hasSum_divisorSumAt_pow {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (if N ∣ m then (σ 1 (m / N) : ℂ) else 0) * q ^ m)
      (divisorSumAt 1 (q ^ N)) := by
  have hq_norm : ‖q ^ N‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (NeZero.ne N)
  have hs := (summable_divisorSumSeries 1 hq_norm).hasSum
  rw [← divisorSumAt_def] at hs
  have hinj : Function.Injective (fun k : ℕ ↦ N * k) := mul_right_injective₀ (NeZero.ne N)
  refine (hinj.hasSum_iff fun m hm ↦ ?_).mp (hs.congr_fun fun k ↦ ?_)
  · have hndvd : ¬ N ∣ m := fun ⟨k, hk⟩ ↦ hm ⟨k, hk.symm⟩
    simp [hndvd]
  · simp [Nat.mul_div_cancel_left _ (NeZero.pos N), pow_mul]

/-- **Explicit `q_N`-expansion of the single-residue weight-two Eisenstein series.** For a nonzero
residue vector `a ∈ (ℤ/Nℤ)²`, the `n`-th coefficient of
`(2πi)⁻² G₂^{a}(τ) = (2πi)⁻² N⁻² ℘((a₀ τ + a₁) / N; ℤ τ + ℤ)` in `q_N = exp (2πi τ / N)` is given
explicitly in terms of `ζ_N = exp (2πi / N)` and the divisors of `n`. -/
theorem qExpansion_weightedG2_single_div_coeff {a : Fin 2 → ZMod N} (ha : a ≠ 0) (n : ℕ) :
    (qExpansion N (fun τ : ℍ ↦
        EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2)).coeff n =
      ((N : ℂ) ^ 2)⁻¹ *
        ((if n = 0 then (1 / 12 : ℂ) +
            if a 0 = 0 then Complex.exp (2 * π * Complex.I / N) ^ (a 1).val /
              (1 - Complex.exp (2 * π * Complex.I / N) ^ (a 1).val) ^ 2
            else 0
          else 0) +
          (∑ x ∈ n.divisorsAntidiagonal,
            if (x.1 : ZMod N) = a 0 then
              (x.2 : ℂ) * (Complex.exp (2 * π * Complex.I / N) ^ (a 1).val) ^ x.2
            else 0) +
          (∑ x ∈ n.divisorsAntidiagonal,
            if (x.1 : ZMod N) = -a 0 then
              (x.2 : ℂ) * (Complex.exp (2 * π * Complex.I / N) ^ (-a 1).val) ^ x.2
            else 0) -
          2 * if N ∣ n then (σ 1 (n / N) : ℂ) else 0) := by
  set ζ := Complex.exp (2 * π * Complex.I / N)
  set c : ℕ → ℂ := fun m ↦ ((N : ℂ) ^ 2)⁻¹ *
    ((if m = 0 then (1 / 12 : ℂ) +
        if a 0 = 0 then ζ ^ (a 1).val / (1 - ζ ^ (a 1).val) ^ 2 else 0
      else 0) +
      (∑ x ∈ m.divisorsAntidiagonal,
        if (x.1 : ZMod N) = a 0 then (x.2 : ℂ) * (ζ ^ (a 1).val) ^ x.2 else 0) +
      (∑ x ∈ m.divisorsAntidiagonal,
        if (x.1 : ZMod N) = -a 0 then (x.2 : ℂ) * (ζ ^ (-a 1).val) ^ x.2 else 0) -
      2 * if N ∣ m then (σ 1 (m / N) : ℂ) else 0)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hper : (N : ℝ) ∈ (Gamma N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hmf : (fun τ : ℍ ↦
      EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2) =
      ⇑((((2 * π * Complex.I) ^ 2)⁻¹ : ℂ) •
        EisensteinSeries.weightedG2MF (Pi.single a (1 : ℂ))) := by
    ext τ
    simp [div_eq_inv_mul, EisensteinSeries.coe_weightedG2MF]
  have han : AnalyticAt ℂ (cuspFunction N (fun τ : ℍ ↦
      EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2)) 0 := by
    rw [hmf]
    exact ModularFormClass.analyticAt_cuspFunction_zero _ hNpos hper
  refine (TauCeti.UpperHalfPlane.qExpansion_coeff_unique (c := c) hNpos han (fun τ ↦ ?_) n).symm
  set qN := Function.Periodic.qParam N (τ : ℂ)
  have hqN : ‖qN‖ < 1 := by
    rw [Function.Periodic.norm_qParam]
    exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos
      (by nlinarith [Real.pi_pos, τ.2]) hNpos)
  have h0 : HasSum (fun m : ℕ ↦ (if m = 0 then (1 / 12 : ℂ) +
      if a 0 = 0 then ζ ^ (a 1).val / (1 - ζ ^ (a 1).val) ^ 2 else 0 else 0) * qN ^ m)
      ((1 / 12 : ℂ) + if a 0 = 0 then ζ ^ (a 1).val / (1 - ζ ^ (a 1).val) ^ 2 else 0) := by
    convert hasSum_ite_eq 0 _ using 1
    ext m
    split_ifs with hm <;> simp [hm]
  have h1 := hasSum_residueLambert (c := a 0) hqN (norm_cexp_two_pi_I_div_pow (N := N) (a 1).val)
  have h2 := hasSum_residueLambert (c := -a 0) hqN (norm_cexp_two_pi_I_div_pow (N := N) (-a 1).val)
  have h3 := hasSum_divisorSumAt_pow (N := N) hqN
  have htot := (((h0.add h1).add h2).sub (h3.mul_left 2)).mul_left ((N : ℂ) ^ 2)⁻¹
  rw [EisensteinSeries.weightedG2_single_apply, mul_div_assoc,
    weierstrassP_div_eq_residueLambert ha τ]
  exact htot.congr_fun fun m ↦ by
    simp only [c, smul_eq_mul]
    ring

/-! ### Cyclotomic rationality and diagonal equivariance -/

/-- At `a = 0`, the single-residue weight-two Eisenstein function vanishes identically because
`℘[L] 0 = 0`. -/
private theorem weightedG2_single_zero_div :
    (fun τ : ℍ ↦ EisensteinSeries.weightedG2 (Pi.single (0 : Fin 2 → ZMod N) (1 : ℂ)) τ /
        (2 * π * Complex.I) ^ 2) = 0 := by
  ext τ
  simp [EisensteinSeries.weightedG2_single_apply, PeriodPair.weierstrassP_zero]

/-- Every `q_N`-expansion coefficient of `(2πi)⁻² G₂^{a}` lies in `ℚ(ζ_N)`. -/
theorem qExpansion_weightedG2_single_div_coeff_mem_cyclotomic (a : Fin 2 → ZMod N) (n : ℕ) :
    (qExpansion N (fun τ : ℍ ↦
        EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2)).coeff n ∈
      Subfield.closure {z : ℂ | z ^ N = 1} := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [weightedG2_single_zero_div, qExpansion_zero, map_zero]
    exact zero_mem _
  set K := Subfield.closure {z : ℂ | z ^ N = 1}
  have hζ : Complex.exp (2 * π * Complex.I / N) ∈ K := cexp_two_pi_I_div_mem_cyclotomic N
  rw [qExpansion_weightedG2_single_div_coeff ha]
  refine mul_mem (inv_mem (pow_mem (natCast_mem K N) 2))
    (sub_mem (add_mem (add_mem ?_ ?_) ?_) (mul_mem (ofNat_mem K 2) ?_))
  · split_ifs
    · exact add_mem (div_mem (one_mem K) (ofNat_mem K 12))
        (div_mem (pow_mem hζ _) (pow_mem (sub_mem (one_mem K) (pow_mem hζ _)) 2))
    · exact add_mem (div_mem (one_mem K) (ofNat_mem K 12)) (zero_mem K)
    · exact zero_mem K
  · refine sum_mem fun x _ ↦ ?_
    split_ifs
    · exact mul_mem (natCast_mem K _) (pow_mem (pow_mem hζ _) _)
    · exact zero_mem K
  · refine sum_mem fun x _ ↦ ?_
    split_ifs
    · exact mul_mem (natCast_mem K _) (pow_mem (pow_mem hζ _) _)
    · exact zero_mem K
  · split_ifs
    · exact natCast_mem K _
    · exact zero_mem K

/-- An endomorphism of `ℚ(ζ_N)` raising `ζ_N` to the power `d` raises `ζ_N ^ b.val` to
`ζ_N ^ (b * d).val`. -/
private theorem map_cexp_two_pi_I_div_pow (d : (ZMod N)ˣ)
    (φ : Subfield.closure {z : ℂ | z ^ N = 1} →+* Subfield.closure {z : ℂ | z ^ N = 1})
    (hφ : (φ ⟨Complex.exp (2 * π * Complex.I / N), cexp_two_pi_I_div_mem_cyclotomic N⟩ : ℂ) =
      Complex.exp (2 * π * Complex.I / N) ^ (d : ZMod N).val) (b : ZMod N) :
    (φ ⟨Complex.exp (2 * π * Complex.I / N) ^ b.val,
        pow_mem (cexp_two_pi_I_div_mem_cyclotomic N) _⟩ : ℂ) =
      Complex.exp (2 * π * Complex.I / N) ^ (b * (d : ZMod N)).val := by
  have hpow : (⟨Complex.exp (2 * π * Complex.I / N) ^ b.val,
      pow_mem (cexp_two_pi_I_div_mem_cyclotomic N) _⟩ : Subfield.closure {z : ℂ | z ^ N = 1}) =
      ⟨Complex.exp (2 * π * Complex.I / N), cexp_two_pi_I_div_mem_cyclotomic N⟩ ^ b.val :=
    Subtype.ext (by simp)
  rw [hpow, map_pow, SubmonoidClass.coe_pow, hφ, ← pow_mul]
  refine cexp_two_pi_I_div_pow_eq_of_modEq ?_
  rw [Nat.ModEq, ← ZMod.natCast_eq_natCast_iff']
  simp [mul_comm]

/-- **Cyclotomic equivariance of the `q_N`-expansion of `(2πi)⁻² G₂^{a}`.** An endomorphism of
`ℚ(ζ_N)` sending `ζ_N ↦ ζ_N ^ d` transforms the `q_N`-expansion coefficients for `a` into those for
`a · diag(1, d)`. -/
theorem map_qExpansion_weightedG2_single_div_coeff (a : Fin 2 → ZMod N)
    (d : (ZMod N)ˣ)
    (φ : Subfield.closure {z : ℂ | z ^ N = 1} →+* Subfield.closure {z : ℂ | z ^ N = 1})
    (hφ : (φ ⟨Complex.exp (2 * π * Complex.I / N), cexp_two_pi_I_div_mem_cyclotomic N⟩ : ℂ) =
      Complex.exp (2 * π * Complex.I / N) ^ (d : ZMod N).val) (n : ℕ) :
    (φ ⟨(qExpansion N (fun τ : ℍ ↦
          EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2)).coeff n,
        qExpansion_weightedG2_single_div_coeff_mem_cyclotomic a n⟩ : ℂ) =
      (qExpansion N (fun τ : ℍ ↦
        EisensteinSeries.weightedG2
          (Pi.single (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))) (1 : ℂ)) τ /
          (2 * π * Complex.I) ^ 2)).coeff n := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [Matrix.zero_vecMul, weightedG2_single_zero_div, qExpansion_zero, map_zero,
      ZeroMemClass.coe_eq_zero, map_eq_zero]
    rfl
  let K := Subfield.closure {z : ℂ | z ^ N = 1}
  let ζK : K := ⟨Complex.exp (2 * π * Complex.I / N), cexp_two_pi_I_div_mem_cyclotomic N⟩
  have hda : a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N)) ≠ 0 := fun h ↦ ha <| by
    simpa using Matrix.vecMul_injective_of_isUnit (diagGL ![1, d]).isUnit (by simpa using h)
  have h0 : (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))) 0 = a 0 := by
    simp [Matrix.vecMul, dotProduct]
  have h1 : (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))) 1 = a 1 * (d : ZMod N) := by
    simp [Matrix.vecMul, dotProduct]
  let valK (b : Fin 2 → ZMod N) : K :=
    ((N : K) ^ 2)⁻¹ *
      ((if n = 0 then (1 / 12 : K) +
          if b 0 = 0 then ζK ^ (b 1).val / (1 - ζK ^ (b 1).val) ^ 2 else 0
        else 0) +
        (∑ x ∈ n.divisorsAntidiagonal,
          if (x.1 : ZMod N) = b 0 then (x.2 : K) * (ζK ^ (b 1).val) ^ x.2 else 0) +
        (∑ x ∈ n.divisorsAntidiagonal,
          if (x.1 : ZMod N) = -b 0 then (x.2 : K) * (ζK ^ (-b 1).val) ^ x.2 else 0) -
        2 * if N ∣ n then (σ 1 (n / N) : K) else 0)
  have hcoe (b : Fin 2 → ZMod N) (hb : b ≠ 0) :
      (valK b : ℂ) = (qExpansion N (fun τ : ℍ ↦
        EisensteinSeries.weightedG2 (Pi.single b (1 : ℂ)) τ /
          (2 * π * Complex.I) ^ 2)).coeff n := by
    rw [qExpansion_weightedG2_single_div_coeff hb]
    simp only [valK, ζK]
    push_cast
    congr 2
    · congr 1
      · congr 1
        · split_ifs <;> push_cast <;> rfl
        · refine Finset.sum_congr rfl fun x _ ↦ ?_
          split_ifs <;> push_cast <;> rfl
      · refine Finset.sum_congr rfl fun x _ ↦ ?_
        split_ifs <;> push_cast <;> rfl
    · split_ifs <;> push_cast <;> rfl
  have hsub : (⟨(qExpansion N (fun τ : ℍ ↦
      EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2)).coeff n,
      qExpansion_weightedG2_single_div_coeff_mem_cyclotomic a n⟩ : K) = valK a :=
    Subtype.ext (hcoe a ha).symm
  rw [hsub, ← hcoe _ hda]
  have hmap_pow (b : ZMod N) : φ (ζK ^ b.val) = ζK ^ (b * (d : ZMod N)).val :=
    Subtype.ext (map_cexp_two_pi_I_div_pow d φ hφ b)
  congr 1
  simp only [valK, map_mul, map_inv₀, map_pow, map_natCast, map_sub, map_add, map_ofNat,
    map_sum, apply_ite φ, map_zero, map_div₀, map_one, h0, h1, neg_mul, hmap_pow]

/-! ### Cyclotomic `q_N`-expansions of the Fricke functions -/

/-- For a level-one modular form, its cusp function at width `N` is analytic at `0`. -/
private theorem analyticAt_cuspFunction_natCast_levelOne {k : ℤ} (f : _root_.ModularForm 𝒮ℒ k) :
    AnalyticAt ℂ (cuspFunction N (f : ℍ → ℂ)) 0 := by
  have h := TauCeti.analyticAt_cuspFunction_nat_mul one_ne_zero (NeZero.pos N)
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
  simpa using h

/-- The Laurent `q_N`-expansion of `f_a` at `∞` agrees with `UpperHalfPlane.laurentQExpansion N`. -/
theorem laurentQExpansion_frickeMeromorphicFunction (a : Fin 2 → ZMod N) :
    laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a) =
      TauCeti.UpperHalfPlane.laurentQExpansion N (frickeFunction a) := by
  rw [laurentQExpansion_apply, cuspDatumInftyGamma_width, cuspDatumInftyGamma_scaling, inv_one]
  simp only [one_smul, finitePart_frickeMeromorphicFunction_ofQuotient_mk]

/-- The Laurent `q_N`-expansion of `f_a` factors into the expansions of `E₄`, `E₆`, `Δ` and
`(2πi)⁻² G₂^{a}`. -/
private theorem laurentQExpansion_frickeFunction (a : Fin 2 → ZMod N) :
    TauCeti.UpperHalfPlane.laurentQExpansion N (frickeFunction a) =
      TauCeti.UpperHalfPlane.laurentQExpansion N (ModularForm.E₄ : ℍ → ℂ) *
        TauCeti.UpperHalfPlane.laurentQExpansion N (ModularForm.E₆ : ℍ → ℂ) /
        TauCeti.UpperHalfPlane.laurentQExpansion N _root_.ModularForm.discriminant *
        (qExpansion N (fun τ : ℍ ↦
          EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2) :
          LaurentSeries ℂ) := by
  have hE₄ := (analyticAt_cuspFunction_natCast_levelOne (N := N) ModularForm.E₄).meromorphicAt
  have hE₆ := (analyticAt_cuspFunction_natCast_levelOne (N := N) ModularForm.E₆).meromorphicAt
  have hΔ : _root_.MeromorphicAt (cuspFunction N _root_.ModularForm.discriminant) 0 := by
    rw [← CuspForm.coe_discriminant]
    exact (analyticAt_cuspFunction_natCast_levelOne (N := N)
      (CuspForm.toModularFormₗ CuspForm.discriminant)).meromorphicAt
  have hG_an : AnalyticAt ℂ (cuspFunction N (fun τ : ℍ ↦
      EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2)) 0 := by
    have hmf : (fun τ : ℍ ↦
        EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2) =
        ⇑((((2 * π * Complex.I) ^ 2)⁻¹ : ℂ) •
          EisensteinSeries.weightedG2MF (Pi.single a (1 : ℂ))) := by
      ext τ
      simp [div_eq_inv_mul, EisensteinSeries.coe_weightedG2MF]
    rw [hmf]
    exact ModularFormClass.analyticAt_cuspFunction_zero _
      (Nat.cast_pos.mpr (NeZero.pos N)) (by simp)
  have hfun : frickeFunction a =
      ((ModularForm.E₄ : ℍ → ℂ) * (ModularForm.E₆ : ℍ → ℂ) / _root_.ModularForm.discriminant) *
        fun τ : ℍ ↦ EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ /
          (2 * π * Complex.I) ^ 2 := by
    ext τ
    simp only [frickeFunction_def, Pi.mul_apply, Pi.div_apply]
    ring
  rw [hfun, TauCeti.UpperHalfPlane.laurentQExpansion_mul
      (TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_div
        (TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_mul hE₄ hE₆) hΔ) hG_an.meromorphicAt,
    TauCeti.UpperHalfPlane.laurentQExpansion_div
      (TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_mul hE₄ hE₆) hΔ,
    TauCeti.UpperHalfPlane.laurentQExpansion_mul hE₄ hE₆,
    TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt hG_an]

/-- A level-one function with integer `q₁`-expansion lifts to a Laurent series over any subfield `K`
of `ℂ` fixed by every endomorphism of `K`. -/
private theorem exists_laurentQExpansion_levelOne_int (K : Subfield ℂ)
    {f : ℍ → ℂ} (hper : Function.Periodic (f ∘ ofComplex) 1)
    (han : AnalyticAt ℂ (cuspFunction 1 f) 0)
    (hint : ∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 f).coeff n = m) :
    ∃ s : LaurentSeries K,
      HahnSeries.mapRingHom K.subtype s = TauCeti.UpperHalfPlane.laurentQExpansion N f ∧
      ∀ φ : K →+* K, HahnSeries.mapRingHom φ s = s := by
  let dN : ℕ+ := ⟨N, NeZero.pos N⟩
  have hexp : TauCeti.UpperHalfPlane.laurentQExpansion N f =
      LaurentSeries.expand ℂ dN (qExpansion 1 f : LaurentSeries ℂ) := by
    have h := TauCeti.UpperHalfPlane.laurentQExpansion_pnat_mul hper han.meromorphicAt dN
    rw [TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt han] at h
    simpa [dN] using h
  choose m hm using hint
  let s₁ : PowerSeries K := PowerSeries.mk fun n ↦ (m n : K)
  refine ⟨LaurentSeries.expand K dN (s₁ : LaurentSeries K), ?_, ?_⟩
  · rw [hexp]
    ext n
    simp only [HahnSeries.coeff_mapRingHom]
    by_cases hdiv : ((dN : ℕ) : ℤ) ∣ n
    · obtain ⟨k, rfl⟩ := hdiv
      simp only [LaurentSeries.coeff_expand_mul, PowerSeries.coeff_coe]
      split_ifs
      · simp
      · simp [s₁, hm]
    · simp [LaurentSeries.coeff_expand_of_not_dvd _ _ hdiv]
  · intro φ
    ext n
    simp only [HahnSeries.coeff_mapRingHom]
    by_cases hdiv : ((dN : ℕ) : ℤ) ∣ n
    · obtain ⟨k, rfl⟩ := hdiv
      simp only [LaurentSeries.coeff_expand_mul, PowerSeries.coeff_coe]
      split_ifs
      · simp
      · simp [s₁]
    · simp [LaurentSeries.coeff_expand_of_not_dvd _ _ hdiv]

/-- The level-one factor `E₄ E₆ / Δ` lifts to a Laurent series over `ℚ(ζ_N)` fixed by every
endomorphism of `ℚ(ζ_N)`. -/
private theorem exists_levelOne_factor_laurentSeries :
    ∃ s : LaurentSeries (Subfield.closure {z : ℂ | z ^ N = 1}),
      HahnSeries.mapRingHom (Subfield.closure {z : ℂ | z ^ N = 1}).subtype s =
        TauCeti.UpperHalfPlane.laurentQExpansion N (ModularForm.E₄ : ℍ → ℂ) *
          TauCeti.UpperHalfPlane.laurentQExpansion N (ModularForm.E₆ : ℍ → ℂ) /
          TauCeti.UpperHalfPlane.laurentQExpansion N _root_.ModularForm.discriminant ∧
      ∀ φ : Subfield.closure {z : ℂ | z ^ N = 1} →+* Subfield.closure {z : ℂ | z ^ N = 1},
        HahnSeries.mapRingHom φ s = s := by
  let K := Subfield.closure {z : ℂ | z ^ N = 1}
  obtain ⟨s₄, hs₄, hφ₄⟩ := exists_laurentQExpansion_levelOne_int (N := N) K
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos one_mem_strictPeriods_SL)
    ModularForm.exists_E₄_qExpansion_coeff_eq_intCast
  obtain ⟨s₆, hs₆, hφ₆⟩ := exists_laurentQExpansion_levelOne_int (N := N) K
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL)
    (ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₆ one_pos one_mem_strictPeriods_SL)
    (fun n ↦ ⟨(1 - 504 * TauCeti.divisorSumSeries (R := ℤ) 5).coeff n, by
      rw [ModularForm.qExpansion_E₆_eq, PowerSeries.coeff_map, Int.coe_castRingHom]⟩)
  obtain ⟨sΔ, hsΔ, hφΔ⟩ := exists_laurentQExpansion_levelOne_int (N := N) K
    (f := _root_.ModularForm.discriminant)
    (by
      rw [← CuspForm.coe_discriminant]
      exact SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL)
    (by
      rw [← CuspForm.coe_discriminant]
      exact ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
        one_mem_strictPeriods_SL)
    ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast
  refine ⟨s₄ * s₆ / sΔ, ?_, fun φ ↦ ?_⟩
  · rw [map_div₀, map_mul, hs₄, hs₆, hsΔ]
  · rw [map_div₀, map_mul, hφ₄, hφ₆, hφΔ]

/-- **Every Fricke function `f_a` lies in `F_N`.** Its Laurent `q_N`-expansion at `∞` has all its
coefficients in `ℚ(ζ_N)` (including `f_0 = 0`). -/
theorem frickeMeromorphicFunction_mem_modularFunctionField (a : Fin 2 → ZMod N) :
    frickeMeromorphicFunction a ∈ modularFunctionField N := by
  let K := Subfield.closure {z : ℂ | z ^ N = 1}
  rw [modularFunctionField_def, mem_coeffSubfield_iff_exists_mapRingHom_eq,
    laurentQExpansion_frickeMeromorphicFunction, laurentQExpansion_frickeFunction]
  obtain ⟨s₀, hs₀, -⟩ := exists_levelOne_factor_laurentSeries (N := N)
  let sG : PowerSeries K := PowerSeries.mk fun n ↦
    ⟨(qExpansion N (fun τ : ℍ ↦
        EisensteinSeries.weightedG2 (Pi.single a (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2)).coeff n,
      qExpansion_weightedG2_single_div_coeff_mem_cyclotomic a n⟩
  refine ⟨s₀ * (sG : LaurentSeries K), ?_⟩
  rw [map_mul, hs₀]
  congr 1
  ext n
  simp only [HahnSeries.coeff_mapRingHom, PowerSeries.coeff_coe]
  split_ifs <;> simp [sG]

/-- **Cyclotomic equivariance of the Fricke functions.** Any endomorphism of `ℚ(ζ_N)` raising
`ζ_N = exp (2πi / N)` to the power `d ∈ (ℤ/Nℤ)ˣ` acts on the Laurent `q_N`-expansion coefficients
of `f_a` by sending them to those of `f_{a · diag(1, d)}`. -/
theorem map_laurentQExpansion_frickeMeromorphicFunction_coeff (a : Fin 2 → ZMod N)
    (d : (ZMod N)ˣ)
    (φ : Subfield.closure {z : ℂ | z ^ N = 1} →+* Subfield.closure {z : ℂ | z ^ N = 1})
    (hφ : (φ ⟨Complex.exp (2 * π * Complex.I / N), cexp_two_pi_I_div_mem_cyclotomic N⟩ : ℂ) =
      Complex.exp (2 * π * Complex.I / N) ^ (d : ZMod N).val) (n : ℤ) :
    (φ ⟨(laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a)).coeff n,
        (mem_modularFunctionField.mp (frickeMeromorphicFunction_mem_modularFunctionField a)) n⟩ :
        ℂ) =
      (laurentQExpansion (cuspDatumInftyGamma N)
        (frickeMeromorphicFunction (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))))).coeff
        n := by
  let K := Subfield.closure {z : ℂ | z ^ N = 1}
  set a' := a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))
  obtain ⟨s₀, hs₀, hφ₀⟩ := exists_levelOne_factor_laurentSeries (N := N)
  let sG (b : Fin 2 → ZMod N) : LaurentSeries K :=
    (PowerSeries.mk fun m ↦ ⟨(qExpansion N (fun τ : ℍ ↦
        EisensteinSeries.weightedG2 (Pi.single b (1 : ℂ)) τ / (2 * π * Complex.I) ^ 2)).coeff m,
      qExpansion_weightedG2_single_div_coeff_mem_cyclotomic b m⟩ : PowerSeries K)
  have hlift (b : Fin 2 → ZMod N) :
      HahnSeries.mapRingHom K.subtype (s₀ * sG b) =
        laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction b) := by
    rw [laurentQExpansion_frickeMeromorphicFunction, laurentQExpansion_frickeFunction, map_mul, hs₀]
    congr 1
    ext m
    simp only [HahnSeries.coeff_mapRingHom, sG, PowerSeries.coeff_coe]
    split_ifs <;> simp
  have hmap_sG : HahnSeries.mapRingHom φ (sG a) = sG a' := by
    ext m
    simp only [HahnSeries.coeff_mapRingHom, sG, PowerSeries.coeff_coe]
    split_ifs
    · simp
    · simpa [a'] using map_qExpansion_weightedG2_single_div_coeff a d φ hφ m.natAbs
  have hmap : HahnSeries.mapRingHom φ (s₀ * sG a) = s₀ * sG a' := by
    rw [map_mul, hφ₀ φ, hmap_sG]
  have hcoeff_a : (s₀ * sG a).coeff n =
      ⟨(laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a)).coeff n,
        (mem_modularFunctionField.mp
          (frickeMeromorphicFunction_mem_modularFunctionField a)) n⟩ := by
    refine Subtype.ext ?_
    rw [← Subfield.coe_subtype, ← HahnSeries.coeff_mapRingHom, hlift a]
    rfl
  have hcoeff_a' : ((s₀ * sG a').coeff n : ℂ) =
      (laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a')).coeff n := by
    rw [← Subfield.coe_subtype, ← HahnSeries.coeff_mapRingHom, hlift a']
  rw [← hcoeff_a, ← HahnSeries.coeff_mapRingHom, hmap, hcoeff_a']

end TauCeti
