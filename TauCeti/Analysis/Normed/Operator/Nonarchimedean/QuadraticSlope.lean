/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Slopes
public import TauCeti.NumberTheory.Padics.Complex.Valuation
public import TauCeti.NumberTheory.Padics.LogGauge
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Companion operator of `1 - a X^2` and fractional Fredholm slopes over `ℚ_p`

Over a non-algebraically-closed ultrametric field, the Fredholm series `det (1 - T u)` of a
compact operator can have finite slopes with no corresponding eigenvalues in the base field; the
eigenvalues appear after extending scalars to a complete algebraically closed extension such as
`ℂ_[p]`.

This file records the degree-`k` pure binomial slope computation `(1 - a X^k)` and works out the
two-dimensional companion endomorphism `ContinuousLinearMap.quadraticCompanion a` on
`C₀(Fin 2, R)` with matrix `!![0, a; 1, 0]` and Fredholm series `1 - a X^2`:

* over any commutative ring `R` with an additive valuation `v`, if `v a ≠ ⊤` and `k ≠ 0`, the
  Newton slope multiset of `1 - C a * X ^ k` is `k` copies of `(v a).untop₀ / k`
  (`Polynomial.newtonSlopes_one_sub_C_mul_X_pow`);
* over a complete ultrametric Tate ring `R`, `quadraticCompanion a` is row compact with Fredholm
  series `1 - C a * X ^ 2` (`ContinuousLinearMap.charPowerSeries_quadraticCompanion`), slope
  multiplicity `2` at `(v a).untop₀ / 2`, and cutoff slope list
  `[(v a).untop₀ / 2, (v a).untop₀ / 2]`;
* over `ℚ_[p]`, `quadraticCompanion (p : ℚ_[p])` has Fredholm series `1 - p X^2` and cutoff slope
  list `[1 / 2, 1 / 2]` under `TauCeti.padicRealValuation p`, yet has **no eigenvalues** in
  `ℚ_[p]` (`ContinuousLinearMap.not_hasEigenvalue_quadraticCompanion_padic`);
* after extending scalars along `algebraMap ℚ_[p] ℂ_[p]` to `ℂ_[p]`, the extended operator is
  `quadraticCompanion (p : ℂ_[p])`, which acquires eigenvalues of valuation `1 / 2` in `ℂ_[p]`
  whose generalized eigenspaces have total dimension `2`
  (`ContinuousLinearMap.exists_hasEigenvalue_quadraticCompanion_padicComplex`,
  `ContinuousLinearMap.finsum_finrank_maxGenEigenspace_quadraticCompanion_padicComplex`).

## Main definitions

* `ContinuousLinearMap.quadraticCompanion`: the companion endomorphism on `C₀(Fin 2, R)` with
  matrix `!![0, a; 1, 0]`.

## Main results

* `Polynomial.newtonSlopes_one_sub_C_mul_X_pow`: the Newton slopes of `1 - C a * X ^ k` for
  `k ≠ 0` and `v a ≠ ⊤` are `k` copies of `(v a).untop₀ / k`.
* `ContinuousLinearMap.charPowerSeries_quadraticCompanion`: the Fredholm series of
  `quadraticCompanion a` is `1 - C a * X ^ 2`.
* `ContinuousLinearMap.hasEigenvalue_quadraticCompanion_iff`: over a field, `μ` is an eigenvalue
  of `quadraticCompanion a` if and only if `μ ^ 2 = a`.
* `ContinuousLinearMap.newtonSlopesLe_charPowerSeries_quadraticCompanion_padic`,
  `ContinuousLinearMap.not_hasEigenvalue_quadraticCompanion_padic`: `quadraticCompanion (p : ℚ_[p])`
  has slope `1 / 2` with multiplicity `2` and no eigenvalues in `ℚ_[p]`.
* `ContinuousLinearMap.exists_hasEigenvalue_quadraticCompanion_padicComplex`,
  `ContinuousLinearMap.finsum_finrank_maxGenEigenspace_quadraticCompanion_padicComplex`: over
  `ℂ_[p]`, `quadraticCompanion (p : ℂ_[p])` has eigenvalues of valuation `1 / 2` with total
  algebraic multiplicity `2`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., Graduate Texts in
  Mathematics 58, Springer, 1984, Chapter IV, §4.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap TauCeti
open scoped ZeroAtInfty NNReal Polynomial

namespace Polynomial

/-- For `k ≠ 0` and `v a ≠ ⊤`, the polynomial `1 - C a * X ^ k` has `k` finite Newton slopes, all
equal to `(v a).untop₀ / k`. -/
theorem newtonSlopes_one_sub_C_mul_X_pow {R : Type*} [CommRing R]
    (v : AddValuation R (WithTop ℝ)) {a : R} (ha : v a ≠ ⊤) {k : ℕ} (hk : k ≠ 0) :
    (1 - C a * X ^ k).newtonSlopes v = Multiset.replicate k ((v a).untop₀ / k) := by
  set f : R[X] := 1 - C a * X ^ k
  have ha0 : a ≠ 0 := fun h ↦ ha (by simp [h])
  have h10 : (1 : R) ≠ 0 := fun h ↦ WithTop.zero_ne_top (v.map_one.symm.trans (h ▸ v.map_zero))
  have : Nontrivial R := _root_.nontrivial_iff.mpr ⟨1, 0, h10⟩
  have hcoeff (n : ℕ) : f.coeff n = (if n = 0 then 1 else 0) - if n = k then a else 0 := by
    simp [f, coeff_one, coeff_C_mul, coeff_X_pow]
  have hc0 : f.coeff 0 = 1 := by simp [hcoeff, hk.symm]
  have hck : f.coeff k = -a := by simp [hcoeff, hk]
  have htrail_deg : f.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simp [hc0])
  have hdeg : f.natDegree = k := by
    refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_)
      (by simp [hck, ha0])
    simp [hcoeff, (Nat.pos_of_ne_zero hk).trans hn |>.ne', hn.ne']
  have htr : v f.trailingCoeff ≠ ⊤ := by simp [trailingCoeff, htrail_deg, hc0]
  have hld : v f.leadingCoeff ≠ ⊤ := by simp [leadingCoeff, hdeg, hck, ha]
  refine Multiset.eq_replicate.mpr ⟨?_, ?_⟩
  · rw [newtonSlopes_def, Multiset.card_map, Finset.card_val,
      ← Set.ncard_eq_toFinset_card _ (f.finite_finiteEdges_newtonPolygon v),
      finiteEdges_newtonPolygon_of_ne_top f v htr hld, htrail_deg, hdeg, Set.ncard_Ico_nat,
      Nat.sub_zero]
  · refine (forall_mem_newtonSlopes_eq_iff htr hld).mpr ⟨?_, fun n ↦ ?_⟩
    · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      simp [trailingCoeff, leadingCoeff, htrail_deg, hdeg, hc0, hck, div_mul_cancel₀ _ hkR]
    · by_cases hn0 : n = 0
      · subst hn0
        simp [trailingCoeff, htrail_deg, hc0]
      · by_cases hnk : n = k
        · rw [hnk]
          have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
          simp [trailingCoeff, htrail_deg, hc0, hck, div_mul_cancel₀ _ hkR,
            WithTop.coe_untop₀_of_ne_top ha]
        · simp [hcoeff, hn0, hnk]

end Polynomial

namespace ContinuousLinearMap

section Defs

variable {R : Type*} [SeminormedCommRing R]

/-- The companion endomorphism of `1 - a X^2` on the two-dimensional model space `C₀(Fin 2, R)`,
sending `(x₀, x₁)` to `(a * x₁, x₀)`, with matrix `!![0, a; 1, 0]`. -/
noncomputable def quadraticCompanion (a : R) : C₀(Fin 2, R) →L[R] C₀(Fin 2, R) :=
  (singleCLM R 1).comp (evalCLM R 0) + a • ((singleCLM R 0).comp (evalCLM R 1))

@[simp]
theorem quadraticCompanion_apply_zero (a : R) (x : C₀(Fin 2, R)) :
    quadraticCompanion a x 0 = a * x 1 := by
  simp [quadraticCompanion]

@[simp]
theorem quadraticCompanion_apply_one (a : R) (x : C₀(Fin 2, R)) :
    quadraticCompanion a x 1 = x 0 := by
  simp [quadraticCompanion]

/-- The matrix of `quadraticCompanion a` is `!![0, a; 1, 0]`. -/
theorem matrixCoeff_quadraticCompanion (a : R) :
    (quadraticCompanion a).matrixCoeff = !![0, a; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixCoeff_apply]

/-- On the finite model space `C₀(Fin 2, R)`, `quadraticCompanion a` is row compact. -/
theorem isRowCompact_quadraticCompanion (a : R) : (quadraticCompanion a).IsRowCompact := by
  refine isRowCompact_iff.mpr ⟨⟨max ‖a‖ (max ‖(1 : R)‖ 0), fun i j ↦ ?_⟩, by simp⟩
  rw [matrixCoeff_quadraticCompanion]
  fin_cases i <;> fin_cases j <;> simp

/-- The reversed characteristic polynomial of `!![0, a; 1, 0]` is `1 - C a * X ^ 2`. -/
private theorem charpolyRev_quadraticCompanion_matrix (a : R) :
    (!![0, a; 1, 0] : Matrix (Fin 2) (Fin 2) R).charpolyRev =
      1 - Polynomial.C a * Polynomial.X ^ 2 := by
  rw [Matrix.charpolyRev, Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.isValue, zero_ne_one, ↓reduceIte, one_ne_zero, map_zero, map_one, smul_eq_mul, mul_zero,
    mul_one, sub_zero, zero_sub]
  ring

end Defs

section Eigenvalues

variable {K : Type*} [NormedField K]

/-- Over a field, a scalar `μ` is an eigenvalue of `quadraticCompanion a` if and only if
`μ ^ 2 = a`. -/
theorem hasEigenvalue_quadraticCompanion_iff {a μ : K} :
    Module.End.HasEigenvalue (quadraticCompanion a : Module.End K C₀(Fin 2, K)) μ ↔ μ ^ 2 = a := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, hx, hx0⟩
    rw [Module.End.mem_eigenspace_iff] at hx
    have h0 : a * x 1 = μ * x 0 := by simpa using congrArg (fun f : C₀(Fin 2, K) ↦ f 0) hx
    have h1 : x 0 = μ * x 1 := by simpa using congrArg (fun f : C₀(Fin 2, K) ↦ f 1) hx
    have hx1 : x 1 ≠ 0 := by
      intro h10
      apply hx0
      ext i
      fin_cases i <;> simp [h1, h10]
    refine mul_right_cancel₀ hx1 ?_
    calc
      μ ^ 2 * x 1 = μ * (μ * x 1) := by ring
      _ = a * x 1 := by rw [← h1, h0]
  · rintro rfl
    refine ⟨ZeroAtInftyContinuousMap.single (0 : Fin 2) μ +
      ZeroAtInftyContinuousMap.single (1 : Fin 2) 1, ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      ext i
      fin_cases i <;> simp [sq]
    · intro h
      have h1 : (1 : K) = 0 := by simpa using congrArg (fun f : C₀(Fin 2, K) ↦ f 1) h
      exact one_ne_zero h1

end Eigenvalues

section TateRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]

/-- The Fredholm series of `quadraticCompanion a` is `1 - C a * X ^ 2`. -/
theorem charPowerSeries_quadraticCompanion (a : R) :
    (quadraticCompanion a).charPowerSeries = 1 - PowerSeries.C a * PowerSeries.X ^ 2 := by
  rw [(isRowCompact_quadraticCompanion a).charPowerSeries_eq_charPowerSeries_matrixCoeff,
    matrixCoeff_quadraticCompanion, Matrix.charPowerSeries_eq_charpolyRev,
    charpolyRev_quadraticCompanion_matrix]
  simp

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- Bounded coefficient extension maps `quadraticCompanion a` to `quadraticCompanion (f a)`. -/
theorem mapCoeffs_quadraticCompanion {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    [CompleteSpace S] (a : R) (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (quadraticCompanion a).mapCoeffs f hf = quadraticCompanion (f a) := by
  symm
  rw [eq_mapCoeffs_iff, matrixCoeff_quadraticCompanion, matrixCoeff_quadraticCompanion]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- For `v a ≠ ⊤`, the Fredholm series of `quadraticCompanion a` has slope `(v a).untop₀ / 2` with
multiplicity `2`. -/
theorem newtonSlopeMultiplicity_charPowerSeries_quadraticCompanion (v : AddValuation R (WithTop ℝ))
    {a : R} (ha : v a ≠ ⊤) :
    (quadraticCompanion a).charPowerSeries.newtonSlopeMultiplicity v ((v a).untop₀ / 2) = 2 := by
  have hcoe : (1 - PowerSeries.C a * PowerSeries.X ^ 2 : PowerSeries R) =
      ((1 - Polynomial.C a * Polynomial.X ^ 2 : R[X]) : PowerSeries R) := by simp
  rw [charPowerSeries_quadraticCompanion, hcoe, Polynomial.newtonSlopeMultiplicity_coe,
    Polynomial.newtonSlopes_one_sub_C_mul_X_pow v ha (by decide)]
  simp

/-- For `v a ≠ ⊤`, the cutoff slope list of `quadraticCompanion a` up to `(v a).untop₀ / 2` is
`[(v a).untop₀ / 2, (v a).untop₀ / 2]`. -/
theorem newtonSlopesLe_charPowerSeries_quadraticCompanion (v : AddValuation R (WithTop ℝ))
    {a : R} (ha : v a ≠ ⊤) :
    (quadraticCompanion a).charPowerSeries.newtonSlopesLe v ((v a).untop₀ / 2) =
      [(v a).untop₀ / 2, (v a).untop₀ / 2] := by
  set s : ℝ := (v a).untop₀ / 2
  have hcoe : (1 - PowerSeries.C a * PowerSeries.X ^ 2 : PowerSeries R) =
      ((1 - Polynomial.C a * Polynomial.X ^ 2 : R[X]) : PowerSeries R) := by simp
  have hs : (v a).untop₀ / ((2 : ℕ) : ℝ) = s := by norm_num [s]
  have hcoem : ((((1 - Polynomial.C a * Polynomial.X ^ 2 : R[X]) : PowerSeries R).newtonSlopesLe
      v s : List ℝ) : Multiset ℝ) = ([s, s] : List ℝ) := by
    rw [Polynomial.coe_newtonSlopesLe,
      Polynomial.newtonSlopes_one_sub_C_mul_X_pow v ha (by decide), hs,
      Multiset.filter_eq_self.mpr fun x hx ↦ (Multiset.eq_of_mem_replicate hx).le]
    rfl
  rw [charPowerSeries_quadraticCompanion, hcoe]
  exact List.Perm.eq_of_pairwise' (PowerSeries.sortedLE_newtonSlopesLe _ _ _).pairwise
    (by simp) (Multiset.coe_eq_coe.mp hcoem)

end TateRing

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- Over `ℚ_[p]`, `quadraticCompanion (p : ℚ_[p])` has Fredholm slope `1 / 2` with multiplicity `2`
under `TauCeti.padicRealValuation p`. -/
theorem newtonSlopeMultiplicity_charPowerSeries_quadraticCompanion_padic :
    (quadraticCompanion (p : ℚ_[p])).charPowerSeries.newtonSlopeMultiplicity
      (TauCeti.padicRealValuation p) (1 / 2) = 2 := by
  have hp : TauCeti.padicRealValuation p (p : ℚ_[p]) ≠ ⊤ := by simp
  simpa using newtonSlopeMultiplicity_charPowerSeries_quadraticCompanion
    (TauCeti.padicRealValuation p) hp

/-- Over `ℚ_[p]`, the cutoff slope list of `quadraticCompanion (p : ℚ_[p])` at `1 / 2` is
`[1 / 2, 1 / 2]`. -/
theorem newtonSlopesLe_charPowerSeries_quadraticCompanion_padic :
    (quadraticCompanion (p : ℚ_[p])).charPowerSeries.newtonSlopesLe
      (TauCeti.padicRealValuation p) (1 / 2) = [1 / 2, 1 / 2] := by
  have hp : TauCeti.padicRealValuation p (p : ℚ_[p]) ≠ ⊤ := by simp
  simpa using newtonSlopesLe_charPowerSeries_quadraticCompanion
    (TauCeti.padicRealValuation p) hp

/-- Over `ℚ_[p]`, `quadraticCompanion (p : ℚ_[p])` has **no eigenvalues** in `ℚ_[p]`, even though
its Fredholm polygon has a finite face of slope `1 / 2` and horizontal length `2`. -/
theorem not_hasEigenvalue_quadraticCompanion_padic (μ : ℚ_[p]) :
    ¬ Module.End.HasEigenvalue
      (quadraticCompanion (p : ℚ_[p]) : Module.End ℚ_[p] C₀(Fin 2, ℚ_[p])) μ := by
  rw [hasEigenvalue_quadraticCompanion_iff]
  intro hμ
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hμ0 : μ ≠ 0 := fun h ↦ hp0 (by simpa [h] using hμ.symm)
  obtain ⟨n, hn⟩ := TauCeti.exists_int_padicRealValuation hμ0
  have hv : TauCeti.padicRealValuation p (μ ^ 2) = TauCeti.padicRealValuation p (p : ℚ_[p]) :=
    congrArg _ hμ
  rw [sq, (TauCeti.padicRealValuation p).map_mul, hn, TauCeti.padicRealValuation_p,
    ← WithTop.coe_add, ← WithTop.coe_one, WithTop.coe_eq_coe] at hv
  have h2n : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 : ℝ) * n = 1)
  omega

/-- Norm recovery for `(PadicComplex.pseudoUniformizer p).addValuation` with base `p`. -/
private theorem norm_eq_rpow_neg_padicComplex_addValuation {y : ℂ_[p]} (hy : y ≠ 0) :
    ‖y‖ = (p : ℝ) ^ (-((PadicComplex.pseudoUniformizer p).addValuation y).untop₀) := by
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have htop : (PadicComplex.pseudoUniformizer p).logGauge y ≠ ⊤ :=
    TauCeti.NormedRing.PseudoUniformizer.logGauge_eq_top_iff.not.mpr hy'
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  have h := TauCeti.NormedRing.PseudoUniformizer.logGauge_eq_coe_iff.mp hr.symm
  rw [PadicComplex.coe_unit_pseudoUniformizer, PadicComplex.norm_p,
    Real.inv_rpow (Nat.cast_nonneg p), ← Real.rpow_neg (Nat.cast_nonneg p)] at h
  rw [TauCeti.NormedRing.PseudoUniformizer.addValuation_apply, ← hr, WithTop.untop₀_coe, h]

/-- `(PadicComplex.pseudoUniformizer p).addValuation` restricts along `algebraMap ℚ_[p] ℂ_[p]` to
`TauCeti.padicRealValuation p`. -/
private theorem padicComplex_addValuation_algebraMap (x : ℚ_[p]) :
    (PadicComplex.pseudoUniformizer p).addValuation (algebraMap ℚ_[p] ℂ_[p] x) =
      TauCeti.padicRealValuation p x := by
  rw [TauCeti.NormedRing.PseudoUniformizer.addValuation_apply,
    ← TauCeti.NormedRing.PseudoUniformizer.map_ratAddValuation (PadicComplex.isCommensurable p _),
    ← PadicComplex.addValuation_def, PadicComplex.addValuation_algebraMap, WithTop.map_map,
    TauCeti.padicRealValuation_eq_map]
  rfl

/-- After extending scalars to `ℂ_[p]`, `quadraticCompanion (p : ℂ_[p])` acquires an eigenvalue of
valuation `1 / 2`. -/
theorem exists_hasEigenvalue_quadraticCompanion_padicComplex :
    ∃ μ : ℂ_[p],
      (PadicComplex.pseudoUniformizer p).addValuation μ = ((1 / 2 : ℝ) : WithTop ℝ) ∧
        Module.End.HasEigenvalue
          (quadraticCompanion (p : ℂ_[p]) : Module.End ℂ_[p] C₀(Fin 2, ℂ_[p])) μ := by
  have hb : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hf : ∃ C : ℝ≥0, ∀ r : ℚ_[p], ‖algebraMap ℚ_[p] ℂ_[p] r‖ ≤ C * ‖r‖ :=
    ⟨1, fun r ↦ by simp [norm_algebraMap']⟩
  have hne : (quadraticCompanion (p : ℚ_[p])).charPowerSeries.newtonSlopeMultiplicity
      (TauCeti.padicRealValuation p) (1 / 2) ≠ 0 := by
    rw [newtonSlopeMultiplicity_charPowerSeries_quadraticCompanion_padic]
    decide
  rw [(isRowCompact_quadraticCompanion (p : ℚ_[p]))
      |>.newtonSlopeMultiplicity_charPowerSeries_ne_zero_iff_mapCoeffs
        (TauCeti.padicRealValuation p) (PadicComplex.pseudoUniformizer p).addValuation hb
        (fun _ hy ↦ norm_eq_rpow_neg_padicComplex_addValuation p hy)
        (algebraMap ℚ_[p] ℂ_[p]) hf (padicComplex_addValuation_algebraMap p),
    mapCoeffs_quadraticCompanion, map_natCast] at hne
  exact hne

/-- Over `ℂ_[p]`, the generalized eigenspaces of `quadraticCompanion (p : ℂ_[p])` at eigenvalues of
valuation `1 / 2` have total dimension `2`, matching the Fredholm slope multiplicity over
`ℚ_[p]`. -/
theorem finsum_finrank_maxGenEigenspace_quadraticCompanion_padicComplex :
    (∑ᶠ μ ∈ {μ : ℂ_[p] |
        (PadicComplex.pseudoUniformizer p).addValuation μ = ((1 / 2 : ℝ) : WithTop ℝ)},
      Module.finrank ℂ_[p]
        (Module.End.maxGenEigenspace
          (quadraticCompanion (p : ℂ_[p]) : Module.End ℂ_[p] C₀(Fin 2, ℂ_[p])) μ)) = 2 := by
  have hb : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hf : ∃ C : ℝ≥0, ∀ r : ℚ_[p], ‖algebraMap ℚ_[p] ℂ_[p] r‖ ≤ C * ‖r‖ :=
    ⟨1, fun r ↦ by simp [norm_algebraMap']⟩
  have h := (isRowCompact_quadraticCompanion (p : ℚ_[p]))
    |>.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_mapCoeffs
      (TauCeti.padicRealValuation p) (PadicComplex.pseudoUniformizer p).addValuation hb
      (fun _ hy ↦ norm_eq_rpow_neg_padicComplex_addValuation p hy)
      (algebraMap ℚ_[p] ℂ_[p]) hf (padicComplex_addValuation_algebraMap p) (1 / 2)
  rw [newtonSlopeMultiplicity_charPowerSeries_quadraticCompanion_padic,
    mapCoeffs_quadraticCompanion, map_natCast] at h
  exact h.symm

end Padic

end ContinuousLinearMap
