/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
public import TauCeti.RingTheory.PowerSeries.Entire.Basic
import Mathlib.Algebra.Polynomial.Inductions
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Coprime
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Intertwining
import TauCeti.Analysis.Polynomial.Coleman.Coprime
import TauCeti.RingTheory.Polynomial.Resultant.Coleman
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman decomposition on model spaces `C₀(I, R)`

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, and let `u` be a
row-compact endomorphism of a model space `C₀(I, R)` whose Fredholm series factors as
`H_u = Q S`, where `Q ∈ R[X]` satisfies `Q(0) = 1` and has invertible leading coefficient, `S` is
entire, and `Q` and `S` are coprime in the ring of entire series. Write `Q* = Q.reverse` for the
reversal of `Q`.

Putting `c = lc(Q)⁻¹` and `B = 1 - c Q*`, we have `B(0) = 0`, so `v = B(u)` is row compact, and
polynomial spectral mapping gives `H_v = D(B, Q) D(B, S) = (1 - X) ^ deg Q · D(B, S)`. Since `Q`
and `S` are coprime entire series, `D(B, S)(1)` is a unit, so `1` is a good zero of `H_v` of order
`d = deg Q`. The explicit **Riesz–Coleman projector** `ContinuousLinearMap.rieszColemanProjection`
is defined as the Riesz projector of `v` at `1` of order `d`.

Its range `range E` is finitely generated and projective of constant rank `d` on `Spec R`
(`ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`). Because `Q*(u (1 - E))` is a
unit, `Q` is coprime to `H_(u (1 - E))` in the ring of entire series, forcing `Q` to divide the
reversed characteristic polynomial `P₁ = H_(u E)` of `u` on `range E`. Comparing degrees and
constant terms gives `H_(u E) = Q` and `H_(u (1 - E)) = S`
(`ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq_coe`,
`ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq`).
Finally, Cayley–Hamilton on the finite projective module `range E` gives `f ^ k * Q*(f) = 0` for
the restriction `f` of `u`, and invertibility of `f` sharpens the nilpotence `(Q*(u)) ^ d * E = 0`
to the exact annihilation `Q*(u) * E = 0`
(`ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`). No
Noetherianity, reducedness, scalar division by a nonunit, or global basis of `range E` is used.

## Main definitions

* `ContinuousLinearMap.rieszColemanProjection`: the explicit Riesz–Coleman projector on a model
  space `C₀(I, R)`.

## Main results

* `ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`,
  `ContinuousLinearMap.IsRowCompact.exists_rieszColemanProjection`: existence of the
  Riesz–Coleman projection on `C₀(I, R)`.
* `ContinuousLinearMap.IsRieszColemanProjection.eq_rieszColemanProjection`: every Riesz–Coleman
  projection for a coprime factor equals the explicit projector.
* `ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`: every Riesz–Coleman projection of a
  row-compact operator is row compact.
* `ContinuousLinearMap.IsRieszColemanProjection.finite_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range`: the finite projective summand has
  constant rank `deg Q` (and dimension `deg Q` over a field).
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq_coe`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq`:
  the Fredholm factors on the two summands are `Q` and `S`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open scoped ZeroAtInfty Polynomial PowerSeries TauCeti.RingOpNorm

open PowerSeries (IsEntire)

namespace ContinuousLinearMap

section AlgebraHelpers

/-- Evaluating a polynomial at `u * p` for an idempotent `p` commuting with `u` acts by `P(0)` on
the complement `1 - p` and by `P(u)` on `p`. -/
private theorem aeval_mul_of_isIdempotentElem {R M : Type*} [CommRing R]
    [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [Module R M]
    [ContinuousConstSMul R M] {u p : M →L[R] M} (hp : IsIdempotentElem p)
    (hup : Commute u p) (P : R[X]) :
    Polynomial.aeval (u * p) P = P.coeff 0 • (1 - p) + Polynomial.aeval u P * p := by
  induction P using Polynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ =>
    simp only [map_add, Polynomial.coeff_add, add_smul, add_mul, h₁, h₂]
    abel
  | monomial n a =>
    cases n with
    | zero =>
      simp only [Polynomial.monomial_zero_left, Polynomial.aeval_C, Polynomial.coeff_C_zero,
        Algebra.algebraMap_eq_smul_one, smul_sub, smul_mul_assoc, one_mul, sub_add_cancel]
    | succ k =>
      have h0 : (Polynomial.monomial (k + 1) a).coeff 0 = 0 := by
        rw [Polynomial.coeff_monomial]
        exact Finsupp.single_eq_of_ne (Nat.succ_ne_zero k).symm
      simp only [Polynomial.aeval_monomial, h0, zero_smul, zero_add, hup.mul_pow,
        hp.pow_succ_eq, mul_assoc]

/-- If `Q*(u)` is inverted on `1 - p` by `w` and `lc(Q)` is a unit, then `Q*(u * (1 - p))` is
invertible on all of `M`. -/
private theorem isUnit_aeval_reverse_mul_one_sub {R M : Type*} [CommRing R]
    [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [Module R M]
    [ContinuousConstSMul R M] {u p w : M →L[R] M} {Q : R[X]}
    (hp : IsIdempotentElem p) (hup : Commute u p) (hQlc : IsUnit Q.leadingCoeff)
    (hw₁ : Polynomial.aeval u Q.reverse * w = 1 - p)
    (hw₂ : w * Polynomial.aeval u Q.reverse = 1 - p) (hpw : p * w = 0) (hwp : w * p = 0) :
    IsUnit (Polynomial.aeval (u * (1 - p)) Q.reverse) := by
  have hcomm1 : Commute u (1 - p) := (Commute.one_right u).sub_right hup
  have hQcomm : Commute (Polynomial.aeval u Q.reverse) p := by
    have hp_comp : u.toLinearMap ∘ₗ p.toLinearMap = p.toLinearMap ∘ₗ u.toLinearMap :=
      LinearMap.ext fun y ↦ congr($(hup.eq) y)
    ext x
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hp_comp Q.reverse) x
    simpa only [mul_apply_eq_comp, LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h
  have h_aeval : Polynomial.aeval (u * (1 - p)) Q.reverse =
      Q.leadingCoeff • p + Polynomial.aeval u Q.reverse * (1 - p) := by
    simpa only [Polynomial.coeff_zero_reverse, sub_sub_cancel] using
      aeval_mul_of_isIdempotentElem hp.one_sub hcomm1 Q.reverse
  obtain ⟨c, hc⟩ := hQlc.exists_left_inv
  have hc' : Q.leadingCoeff * c = 1 := mul_comm Q.leadingCoeff c ▸ hc
  have hpp : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp.eq, sub_self]
  have hpp' : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp.eq, sub_self]
  have h1p : (1 - p) * (1 - p) = 1 - p := hp.one_sub.eq
  have h1pw : (1 - p) * w = w := by rw [sub_mul, one_mul, hpw, sub_zero]
  rw [h_aeval]
  refine isUnit_iff_exists.mpr ⟨c • p + w, ?_, ?_⟩
  · calc (Q.leadingCoeff • p + Polynomial.aeval u Q.reverse * (1 - p)) * (c • p + w)
        = (c * Q.leadingCoeff) • (p * p) + Q.leadingCoeff • (p * w) +
            c • (Polynomial.aeval u Q.reverse * ((1 - p) * p)) +
            Polynomial.aeval u Q.reverse * ((1 - p) * w) := by
          simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
            mul_assoc]
          abel
      _ = p + (1 - p) := by
          rw [hc, one_smul, hp.eq, hpw, smul_zero, add_zero, hpp', mul_zero, smul_zero,
            add_zero, h1pw, hw₁]
      _ = 1 := add_sub_cancel _ _
  · calc (c • p + w) * (Q.leadingCoeff • p + Polynomial.aeval u Q.reverse * (1 - p))
        = (Q.leadingCoeff * c) • (p * p) + c • (Polynomial.aeval u Q.reverse * (p * (1 - p))) +
            Q.leadingCoeff • (w * p) + w * Polynomial.aeval u Q.reverse * (1 - p) := by
          simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
            mul_assoc]
          rw [← mul_assoc p (Polynomial.aeval u Q.reverse), ← hQcomm.eq, mul_assoc]
          abel
      _ = p + (1 - p) := by
          rw [hc', one_smul, hp.eq, hpp, mul_zero, smul_zero, add_zero, hwp, smul_zero, add_zero,
            hw₂, h1p]
      _ = 1 := add_sub_cancel _ _

/-- For any `k : ℕ`, reflecting a polynomial `Q` at `Q.natDegree + k` multiplies its reversal by
`X ^ k`. -/
private theorem reflect_natDegree_add {R : Type*} [Semiring R] (Q : R[X]) (k : ℕ) :
    Q.reflect (Q.natDegree + k) = Polynomial.X ^ k * Q.reverse := by
  have h := Polynomial.reflect_mul (1 : R[X]) Q (F := k) (G := Q.natDegree) (by simp) le_rfl
  simpa only [one_mul, add_comm k Q.natDegree, Polynomial.reflect_one, Polynomial.reverse] using h

end AlgebraHelpers

section ModelSpace

variable {R : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- The **Riesz–Coleman projector** of an endomorphism `u` of `C₀(I, R)` at a polynomial `Q : R[X]`:
the Riesz projector of `B(u)`, for `B = 1 - lc(Q)⁻¹ Q*`, at the scalar `1` of order `deg Q`. When
`u` is row compact and `H_u = Q S` with `Q(0) = 1`, `lc(Q)` a unit, `S` entire, and `Q, S` coprime
entire series, it is the unique Riesz–Coleman projection of `u` at `Q`
(`ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`). -/
noncomputable def rieszColemanProjection (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    C₀(I, R) →L[R] C₀(I, R) :=
  (Polynomial.aeval u (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection
    1 Q.natDegree

/-- Unfolding lemma for `ContinuousLinearMap.rieszColemanProjection`. -/
theorem rieszColemanProjection_def (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    u.rieszColemanProjection Q =
      (Polynomial.aeval u
        (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection
        1 Q.natDegree :=
  (rfl)

/-- For `Q = 1`, the Riesz–Coleman projector is zero. -/
@[simp]
theorem rieszColemanProjection_one (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.rieszColemanProjection 1 = 0 := by
  rw [rieszColemanProjection_def, Polynomial.natDegree_one, rieszProjection_order_zero]

section RowCompact

variable [IsUltrametricDist R]

/-- Every Riesz–Coleman projection of a row-compact operator, for a polynomial `Q` with invertible
leading coefficient, is row compact. -/
theorem IsRieszColemanProjection.isRowCompact {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQlc : IsUnit Q.leadingCoeff) :
    E.IsRowCompact := by
  rw [hE.eq_neg_smul_mul_aeval_divX_mul hQlc, mul_def, mul_def]
  exact (((hu.comp_clm _).comp_clm E).smul _).neg

variable [CompleteSpace R]

/-- For `B = 1 - lc(Q)⁻¹ Q*` and a coprime factorisation `H_u = Q S`, the Fredholm series of
`B(u)` has a good zero of order `deg Q` at `1`. -/
private theorem IsRowCompact.isGoodZero_aeval_one_sub_C_mul_reverse
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    PowerSeries.IsGoodZero (Matrix.charPowerSeries (matrixCoeff (Polynomial.aeval u
      (1 - Polynomial.C (Ring.inverse Q.leadingCoeff) * Q.reverse)))) 1 Q.natDegree := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQlc
  set B := 1 - Polynomial.C c * Q.reverse
  set d := Q.natDegree
  have hB0 : B.coeff 0 = 0 := Polynomial.coeff_zero_one_sub_C_mul_reverse hc
  have hS0 : PowerSeries.constantCoeff S = 1 := by
    have h := congrArg PowerSeries.constantCoeff hFac
    simpa [Matrix.constantCoeff_charPowerSeries, hQ0] using h.symm
  have hS0' : PowerSeries.coeff 0 S = 1 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hHv_eq : (Polynomial.aeval u B).matrixCoeff.charPowerSeries =
      (1 - PowerSeries.X) ^ d * B.colemanDSeries S := by
    rw [hu.charPowerSeries_matrixCoeff_aeval hB0, hFac, Polynomial.colemanDSeries_mul hB0,
      Polynomial.colemanDSeries_one_sub_C_mul_reverse_self hQ0 hc]
  have hDS_entire : (B.colemanDSeries S).IsEntire := by
    rw [← PowerSeries.colemanDEntire_coe hB0 hS0']
    exact PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hS
      (by rwa [Polynomial.coeff_coe]) hS0'
  have hDS_unit : IsUnit ((B.colemanDSeries S).evalAt (1 : R)) :=
    (Polynomial.isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc hS hS0).mpr hCop
  have hfac1 : (1 - PowerSeries.X : R⟦X⟧) ^ d * B.colemanDSeries S =
      (PowerSeries.X - PowerSeries.C 1) ^ d *
        (PowerSeries.C ((-1 : R) ^ d) * B.colemanDSeries S) := by
    have h1 : (1 - PowerSeries.X : R⟦X⟧) =
        PowerSeries.C (-1 : R) * (PowerSeries.X - PowerSeries.C 1) := by
      simp only [map_neg, map_one, neg_mul, one_mul, neg_sub]
    rw [h1, mul_pow, map_pow]
    ring
  rw [hHv_eq, hfac1]
  have hG : (PowerSeries.C ((-1 : R) ^ d) * B.colemanDSeries S).IsEntire :=
    (PowerSeries.isEntire_C _).mul hDS_entire
  rw [hG.isGoodZero_X_sub_C_pow_mul_iff,
    (PowerSeries.isEntire_C _).evalAt_mul hDS_entire, PowerSeries.evalAt_C,
    Algebra.algebraMap_self_apply]
  exact (isUnit_neg_one.pow d).mul hDS_unit

/-- If a polynomial `Q` with `Q(0) = 1` and unit leading coefficient divides a polynomial `P₁`
with `P₁(0) = 1` and `deg P₁ ≤ deg Q` in the ring of entire series, then `P₁ = Q`. -/
private theorem eq_of_dvd_entire_of_natDegree_le {Q P₁ : R[X]} (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) (hP₁_0 : P₁.coeff 0 = 1)
    (hP₁_deg : P₁.natDegree ≤ Q.natDegree)
    (hdvd :
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R) ∣
      ⟨P₁, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P₁)⟩) :
    P₁ = Q := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQlc
  obtain ⟨g, hg⟩ := hdvd
  have hQm : (Polynomial.C c * Q).Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one hc
  have hP₁_mod : (P₁ : R⟦X⟧).modByMonic (Polynomial.C c * Q) = 0 := by
    rw [(PowerSeries.isEntire_coe P₁).modByMonic_eq_zero_iff hQm]
    refine ⟨PowerSeries.C Q.leadingCoeff * (g : R⟦X⟧),
      (PowerSeries.isEntire_C _).mul (IsEntire.mem_subring.mp g.2), ?_⟩
    have hg' : (P₁ : R⟦X⟧) = (Q : R⟦X⟧) * (g : R⟦X⟧) := congrArg Subtype.val hg
    rw [hg', Polynomial.coe_mul, Polynomial.coe_C, mul_comm (PowerSeries.C c),
      mul_assoc (Q : R⟦X⟧), ← mul_assoc (PowerSeries.C c), ← map_mul, hc, map_one, one_mul]
  rw [PowerSeries.modByMonic_coe P₁ hQm, Polynomial.modByMonic_eq_zero_iff_dvd hQm] at hP₁_mod
  obtain ⟨G₁, hG₁⟩ := hP₁_mod
  set G₀ := Polynomial.C c * G₁
  have hP₁_eq : P₁ = Q * G₀ := by
    rw [hG₁]
    dsimp [G₀]
    ring
  have hG₀_0 : G₀.coeff 0 = 1 := by
    have h := congrArg (fun P : R[X] ↦ P.coeff 0) hP₁_eq
    simpa [Polynomial.mul_coeff_zero, hP₁_0, hQ0] using h.symm
  by_cases hG₀ : G₀ = 0
  · have : Subsingleton R := subsingleton_of_zero_eq_one (by simpa [hG₀] using hG₀_0)
    exact Subsingleton.elim P₁ Q
  have hdeg_add : (Q * G₀).natDegree = Q.natDegree + G₀.natDegree :=
    Polynomial.natDegree_mul'
      (mt hQlc.mul_right_eq_zero.mp (Polynomial.leadingCoeff_ne_zero.mpr hG₀))
  have hG₀_deg : G₀.natDegree = 0 := by
    have : Q.natDegree + G₀.natDegree ≤ Q.natDegree := by
      rw [← hdeg_add, ← hP₁_eq]
      exact hP₁_deg
    omega
  have hG₀_one : G₀ = 1 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hG₀_deg, hG₀_0, map_one]
  rw [hP₁_eq, hG₀_one, mul_one]

/-- The spectral, rank and determinant data extracted from the Riesz projector of `B(u)` at `1`
of order `deg Q`, for `B = 1 - lc(Q)⁻¹ Q*`. -/
private theorem IsRowCompact.rieszColeman_data {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} (hQ0 : Q.coeff 0 = 1) (hQlc : IsUnit Q.leadingCoeff)
    {S : R⟦X⟧} (hS : S.IsEntire) (hFac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let E := u.rieszColemanProjection Q
    IsRieszColemanProjection u Q E ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) ∧
      (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQlc
  have hc_unit : IsUnit c := IsUnit.of_mul_eq_one _ hc
  set B := 1 - Polynomial.C c * Q.reverse
  set v := Polynomial.aeval u B
  set d := Q.natDegree
  set E := u.rieszColemanProjection Q
  have hE_def : E = v.rieszProjection 1 d := rfl
  have hB0 : B.coeff 0 = 0 := Polynomial.coeff_zero_one_sub_C_mul_reverse hc
  have hv : v.IsRowCompact := hu.aeval hB0
  have hHv_good : v.matrixCoeff.charPowerSeries.IsGoodZero 1 d :=
    hu.isGoodZero_aeval_one_sub_C_mul_reverse hQ0 hQlc hS hFac hCop
  -- Step 1: Apply the Riesz projector of `v` at `1` of order `d`.
  have hEv : IsRieszProjection v 1 d E := by
    rw [hE_def]
    exact hv.isRieszProjection_rieszProjection (fun _ ↦ hHv_good.evalAt_hasseDeriv_eq_zero)
      hHv_good.isUnit_evalAt_hasseDeriv
  have hE_rc : E.IsRowCompact := hEv.isRowCompact hv
  have hE_rank (p : PrimeSpectrum R) : Module.rankAtStalk (R := R) E.range p = d :=
    hEv.rankAtStalk_range hv hHv_good p
  have huv_comm : Commute u v := by
    simpa only [Polynomial.aeval_X] using
      (Commute.all (Polynomial.X : R[X]) B).map (Polynomial.aeval u)
  have hE_comm : Commute u E := hEv.commute_of_commute huv_comm
  have hv_mem : v ∈ Algebra.adjoin R {u} := by
    rw [Algebra.adjoin_singleton_eq_range_aeval R u]
    exact ⟨B, rfl⟩
  have hsub_adjoin : (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
      (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hv_mem)
  have hE_mem : E ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) :=
    closure_mono hsub_adjoin hEv.mem_closure_adjoin
  have h1v : (1 : C₀(I, R) →L[R] C₀(I, R)) - (1 : R) • v =
      c • Polynomial.aeval u Q.reverse := by
    simp only [one_smul, v, B, map_sub, map_one, map_mul, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      sub_sub_cancel (1 : C₀(I, R) →L[R] C₀(I, R))]
  set w := c • hEv.inverse
  have hw_mem : w ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    have hinv := closure_mono hsub_adjoin hEv.inverse_mem_closure_adjoin
    have hsub : (c • ·) '' (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
        (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
      rintro _ ⟨T, hT, rfl⟩
      exact Subalgebra.smul_mem _ hT c
    exact closure_mono hsub
      (image_closure_subset_closure_image (continuous_const_smul c) ⟨hEv.inverse, hinv, rfl⟩)
  have hQw : Polynomial.aeval u Q.reverse * w = 1 - E := by
    have h := hEv.one_sub_smul_mul_inverse
    rw [h1v] at h
    simpa only [w, mul_smul_comm, smul_mul_assoc] using h
  have hwQ : w * Polynomial.aeval u Q.reverse = 1 - E := by
    have h := hEv.inverse_mul_one_sub_smul
    rw [h1v] at h
    simpa only [w, mul_smul_comm, smul_mul_assoc] using h
  have hEw : E * w = 0 := by
    ext x : 1
    have h := congr($(hEv.mul_inverse_eq_zero) x)
    simp only [w, mul_apply_eq_comp, smul_apply, map_smul, zero_apply] at h ⊢
    rw [h, smul_zero]
  have hwE : w * E = 0 := by
    ext x : 1
    have h := congr($(hEv.inverse_mul_eq_zero) x)
    simp only [w, mul_apply_eq_comp, smul_apply, zero_apply] at h ⊢
    rw [h, smul_zero]
  have hQpow : (Polynomial.aeval u Q.reverse) ^ d * E = 0 := by
    have h := hEv.pow_mul_eq_zero
    rw [h1v, smul_pow, smul_mul_assoc] at h
    exact (hc_unit.pow d).smul_eq_zero.mp h
  -- Step 2: `Q*(u (1 - E))` is invertible, so `Q` is coprime to `H_(u(1-E))`.
  have hQ_comp_unit : IsUnit (Polynomial.aeval (u * (1 - E)) Q.reverse) :=
    isUnit_aeval_reverse_mul_one_sub hEv.isIdempotentElem hE_comm hQlc hQw hwQ hEw hwE
  have hCop_comp : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u * (1 - E)).matrixCoeff.charPowerSeries,
        IsEntire.mem_subring.mpr (hu.comp_clm (1 - E)).isEntire_charPowerSeries⟩ :=
    ((hu.comp_clm (1 - E)).isUnit_aeval_reverse_iff hQlc).mp hQ_comp_unit
  -- Step 3: Identify `H_(uE)` with the reversed characteristic polynomial `P₁` on `E.range`.
  let : AddCommGroup E.range := inferInstance
  have : Module.Finite R E.range := hE_rc.finite_range_of_isIdempotentElem hEv.isIdempotentElem
  have : Module.Projective R E.range :=
    hE_rc.projective_range_of_isIdempotentElem hEv.isIdempotentElem
  have hu_maps : Set.MapsTo u E.range E.range := by
    rw [LinearMap.coe_range, coe_coe]
    exact Function.Semiconj.mapsTo_range fun x ↦ congr($(hE_comm.eq.symm) x)
  let uR : E.range →L[R] E.range := u.restrict hu_maps
  let f : Module.End R E.range := uR.toLinearMap
  have hfix (x : E.range) : E x = x :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range hEv.isIdempotentElem x
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ContinuousLinearMap.ext fun x ↦ Subtype.ext (hfix x)
  have hM : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract
      E.range.subtypeL E.rangeRestrict hri
  have huR_pr := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM hM uR
  have hext : E.range.subtypeL.comp (uR.comp E.rangeRestrict) = u * E :=
    ContinuousLinearMap.ext fun _ ↦ rfl
  have hchar : (u * E).matrixCoeff.charPowerSeries = (f.projectiveCharpolyRev : R⟦X⟧) := by
    have hc' := charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM uR
    rw [← hext, ← huR_pr.charPowerSeries_eq hri, hc']
  set P₁ := f.projectiveCharpolyRev
  -- Step 4: Divisibility `Q ∣ P₁` in `R[X]`, forcing `P₁ = Q` and `H_(u(1-E)) = S`.
  have hSplit : (Q : R⟦X⟧) * S =
      (P₁ : R⟦X⟧) * (u * (1 - E)).matrixCoeff.charPowerSeries := by
    rw [← hFac, hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hEv.isIdempotentElem hE_comm,
      hchar]
  have hQdvd_entire :
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R) ∣
      ⟨P₁, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P₁)⟩ := by
    refine hCop_comp.dvd_of_dvd_mul_right ⟨⟨S, IsEntire.mem_subring.mpr hS⟩, ?_⟩
    exact Subtype.ext hSplit.symm
  have hP₁_eq_Q : P₁ = Q :=
    eq_of_dvd_entire_of_natDegree_le hQ0 hQlc f.coeff_projectiveCharpolyRev_zero
      (f.natDegree_projectiveCharpolyRev_le fun p ↦ (hE_rank p).le) hQdvd_entire
  have hH_uE : (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) := by
    rw [hchar, hP₁_eq_Q]
  have hH_u1E : (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
    have hQ_unit_ps : IsUnit (Q : R⟦X⟧) :=
      PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hQ0])
    rw [hP₁_eq_Q] at hSplit
    exact hQ_unit_ps.mul_left_cancel hSplit.symm
  -- Step 5: `f` is invertible on `E.range` and Cayley–Hamilton gives `Q*(u)E = 0`.
  have hf_inter : u.toLinearMap ∘ₗ E.range.subtype = E.range.subtype ∘ₗ f :=
    LinearMap.ext fun _ ↦ rfl
  have hf_aeval (P : R[X]) (x : E.range) :
      ((Polynomial.aeval f P x : E.range) : C₀(I, R)) = (Polynomial.aeval u P) x := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hf_inter P) x
    simpa only [LinearMap.comp_apply, Submodule.coe_subtype, ← toLinearMap_aeval, coe_coe] using
      h.symm
  have hf_pow : Polynomial.aeval f (Q.reverse ^ d) = 0 := by
    ext x : 1
    apply Subtype.ext
    rw [hf_aeval, map_pow]
    have hx := congr($hQpow (x : C₀(I, R)))
    simpa only [mul_apply_eq_comp, hfix x, zero_apply, LinearMap.zero_apply,
      ZeroMemClass.coe_zero] using hx
  have hf_unit : IsUnit f := by
    set R₀ := Q.reverse ^ d
    have hR₀_0 : IsUnit (R₀.coeff 0) := by
      rw [← Polynomial.constantCoeff_apply, map_pow, Polynomial.constantCoeff_apply,
        Polynomial.coeff_zero_reverse]
      exact hQlc.pow d
    obtain ⟨c₀, hc₀⟩ := hR₀_0.exists_left_inv
    have hleft : f * Polynomial.aeval f R₀.divX + R₀.coeff 0 • 1 = 0 := by
      have h := congrArg (Polynomial.aeval f) (Polynomial.X_mul_divX_add R₀)
      simpa only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one, hf_pow] using h
    have hright : Polynomial.aeval f R₀.divX * f + R₀.coeff 0 • 1 = 0 := by
      have h := congrArg (Polynomial.aeval f) (Polynomial.divX_mul_X_add R₀)
      simpa only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one, hf_pow] using h
    refine isUnit_iff_exists.mpr ⟨-(c₀ • Polynomial.aeval f R₀.divX), ?_, ?_⟩
    · ext x : 1
      have hx := LinearMap.congr_fun hleft x
      simp only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smul_apply,
        one_apply_eq_self, LinearMap.zero_apply] at hx
      simp only [mul_apply_eq_comp, LinearMap.neg_apply, LinearMap.smul_apply, map_neg,
        map_smul, eq_neg_of_add_eq_zero_left hx, smul_neg, neg_neg, smul_smul, hc₀, one_smul,
        one_apply_eq_self]
    · ext x : 1
      have hx := LinearMap.congr_fun hright x
      simp only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smul_apply,
        one_apply_eq_self, LinearMap.zero_apply] at hx
      simp only [mul_apply_eq_comp, LinearMap.neg_apply, LinearMap.smul_apply,
        eq_neg_of_add_eq_zero_left hx, smul_neg, neg_neg, smul_smul, hc₀, one_smul,
        one_apply_eq_self]
  obtain ⟨n, hn, hCH⟩ := LinearMap.exists_aeval_reflect_projectiveCharpolyRev_eq_zero f
  have hn' : Q.natDegree ≤ n := hP₁_eq_Q ▸ hn
  rw [show f.projectiveCharpolyRev = Q from hP₁_eq_Q] at hCH
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn'
  rw [reflect_natDegree_add, map_mul, map_pow, Polynomial.aeval_X] at hCH
  have hf_kill : Polynomial.aeval f Q.reverse = 0 :=
    (hf_unit.pow k).mul_right_eq_zero.mp hCH
  have hQE : Polynomial.aeval u Q.reverse * E = 0 := by
    ext x : 1
    have hx := hf_aeval Q.reverse ⟨E x, ⟨x, rfl⟩⟩
    rw [hf_kill, LinearMap.zero_apply, ZeroMemClass.coe_zero] at hx
    simpa only [mul_apply_eq_comp, zero_apply] using hx.symm
  exact ⟨⟨hEv.isIdempotentElem, hE_comm, hE_mem, hQE, ⟨w, hQw, hwQ, hEw, hwE, hw_mem⟩⟩,
    hE_rank, hH_uE, hH_u1E⟩

/-- **The Riesz–Coleman projector for a coprime polynomial factor.** Let `u` be row compact on
`C₀(I, R)` with `H_u = Q S`, where `Q(0) = 1`, `lc(Q)` is a unit, `S` is entire, and `Q` and `S`
are coprime in the ring of entire series. Then `u.rieszColemanProjection Q` is a Riesz–Coleman
projection of `u` at `Q`. -/
theorem IsRowCompact.isRieszColemanProjection_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection u Q (u.rieszColemanProjection Q) :=
  (hu.rieszColeman_data hQ0 hQlc hS hFac hCop).1

/-- **Existence of the Riesz–Coleman projection on model spaces.** -/
theorem IsRowCompact.exists_rieszColemanProjection {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} (hQ0 : Q.coeff 0 = 1) (hQlc : IsUnit Q.leadingCoeff)
    {S : R⟦X⟧} (hS : S.IsEntire) (hFac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E :=
  ⟨u.rieszColemanProjection Q,
    hu.isRieszColemanProjection_rieszColemanProjection hQ0 hQlc hS hFac hCop⟩

/-- Every Riesz–Coleman projection of a row-compact operator attached to a coprime factor `Q`
equals the explicit projector `ContinuousLinearMap.rieszColemanProjection`. -/
theorem IsRieszColemanProjection.eq_rieszColemanProjection {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    E = u.rieszColemanProjection Q :=
  hE.unique (hu.isRieszColemanProjection_rieszColemanProjection hQ0 hQlc hS hFac hCop)

/-- The range of a Riesz–Coleman projection of a row-compact operator is finitely generated. -/
theorem IsRieszColemanProjection.finite_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQlc : IsUnit Q.leadingCoeff) :
    Module.Finite R E.range :=
  (hE.isRowCompact hu hQlc).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The range of a Riesz–Coleman projection of a row-compact operator is projective over `R`. -/
theorem IsRieszColemanProjection.projective_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQlc : IsUnit Q.leadingCoeff) :
    Module.Projective R E.range :=
  (hE.isRowCompact hu hQlc).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- **Constant rank of the Riesz–Coleman summand.** The finite projective summand `range E`
(`= ker Q*(u)`) has constant rank `deg Q` at every prime ideal of `R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  have hdata := hu.rieszColeman_data hQ0 hQlc hS hFac hCop
  rw [hE.unique hdata.1]
  exact hdata.2.1 p

/-- **Determinant of the finite Riesz–Coleman summand.** The Fredholm series of `u * E` is `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq_coe
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1) (hQlc : IsUnit Q.leadingCoeff)
    {S : R⟦X⟧} (hS : S.IsEntire) (hFac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) := by
  have hdata := hu.rieszColeman_data hQ0 hQlc hS hFac hCop
  rw [hE.unique hdata.1]
  exact hdata.2.2.1

/-- **Determinant of the complementary Riesz–Coleman summand.** The Fredholm series of
`u * (1 - E)` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1) (hQlc : IsUnit Q.leadingCoeff)
    {S : R⟦X⟧} (hS : S.IsEntire) (hFac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  have hdata := hu.rieszColeman_data hQ0 hQlc hS hFac hCop
  rw [hE.unique hdata.1]
  exact hdata.2.2.2

end RowCompact

end ModelSpace

section Field

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {u E : C₀(I, K) →L[K] C₀(I, K)} {Q : K[X]}

/-- Over a complete ultrametric field, the Riesz–Coleman summand `range E` has dimension
`deg Q`. -/
theorem IsRieszColemanProjection.finrank_range (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1) {S : K⟦X⟧} (hS : S.IsEntire)
    (hFac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQne : Q ≠ 0 := fun h ↦ by simp [h] at hQ0
  have hQlc : IsUnit Q.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQne)
  have hr := hE.rankAtStalk_range hu hQ0 hQlc hS hFac hCop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- Over a complete ultrametric field, `ker Q*(u)` has dimension `deg Q`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1)
    {S : K⟦X⟧} (hS : S.IsEntire) (hFac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (LinearMap.ker ((Polynomial.aeval u Q.reverse :
      C₀(I, K) →L[K] C₀(I, K)) : Module.End K C₀(I, K))) = Q.natDegree := by
  have hQne : Q ≠ 0 := fun h ↦ by simp [h] at hQ0
  have hQlc : IsUnit Q.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQne)
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hQ0 hQlc hS hFac hCop
  rw [← hE.range_eq_ker]
  exact hE.finrank_range hu hQ0 hS hFac hCop

end Field

end ContinuousLinearMap
