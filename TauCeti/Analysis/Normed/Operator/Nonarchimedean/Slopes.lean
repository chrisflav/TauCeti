/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.FiniteFactor
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.PrModule
public import TauCeti.NumberTheory.NewtonPolygon.Zeros
import TauCeti.RingTheory.PowerSeries.Weierstrass.Strassmann
import TauCeti.RingTheory.Valuation.NormNormalization

/-!
# Slopes of the Fredholm series of a compact operator

Let `K` be a complete ultrametric nontrivially normed field with a real additive valuation `v`
and a base `b > 1` such that `‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. The Fredholm series
`H_u(T) = det (1 - T u)` of a row-compact endomorphism `u` of a module with property (Pr) is
entire with constant coefficient one. Its Newton polygon therefore has a finite face of every
real slope, its finite slopes are bounded below
(`ContinuousLinearMap.bddBelow_image_unitSlope_newtonPolygon_charPowerSeries`), and they are
locally finite: only finitely many finite unit edges have slope at most any real cutoff
(`ContinuousLinearMap.IsPrCompact.finite_setOf_unitSlope_newtonPolygon_charPowerSeries_le`), so the
slopes up to a cutoff `c` form the finite nondecreasing lists `u.charPowerSeries.newtonSlopesLe v c`
and `u.charPowerSeries.newtonSlopesLt v c`, while infinitely many finite unit edges have slopes
tending to infinity
(`ContinuousLinearMap.IsPrCompact.tendsto_unitSlope_newtonPolygon_charPowerSeries`). A slope `σ`
corresponds to zeros of `H_u` of valuation `-σ`, and a zero `α` gives the eigenvalue `α⁻¹` of `u`,
so the slopes describe the valuations of the eigenvalues.

Both individual multiplicities (`PowerSeries.newtonSlopeMultiplicity`) and cutoff slope lists
(`PowerSeries.newtonSlopesLe`, `PowerSeries.newtonSlopesLt`) behave as eigenvalue valuations should:

* scaling `u` by a scalar `a` of finite valuation shifts every slope by `v a`, since
  `H_{a u}(T) = H_u(a T)`
  (`ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_smul`,
  `ContinuousLinearMap.IsPrCompact.newtonSlopesLe_charPowerSeries_smul`);
* on a block diagonal operator or bounded upper-triangular splitting, multiplicities and cutoff
  slope multisets add, since the Fredholm series multiply
  (`ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_prodMap`,
  `ContinuousLinearMap.IsPrCompact.coe_newtonSlopesLe_charPowerSeries_prodMap`);
* on a finitely generated module with property (Pr), the slopes and cutoff lists agree with those of
  the finite projective determinant `det (1 - X u)`
  (`ContinuousLinearMap.newtonSlopeMultiplicity_charPowerSeries_of_finite`,
  `ContinuousLinearMap.coe_newtonSlopesLe_charPowerSeries_of_finite`). Over a reduced coefficient
  ring, nilpotent finite operators and nilpotent finite blocks contribute no finite slopes
  (`ContinuousLinearMap.newtonSlopesLe_charPowerSeries_eq_nil_of_finite_of_isNilpotent`,
  `ContinuousLinearMap.newtonSlopesLe_charPowerSeries_eq_of_split_of_isNilpotent`).

Over an algebraically closed `K`, the slopes are the valuations of the nonzero eigenvalues counted
with algebraic multiplicity `dim (maxGenEigenspace u μ)`:

* at a single slope `σ`
  (`ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank`);
* up to a cutoff `v μ ≤ c` or strictly below `v μ < c`
  (`ContinuousLinearMap.IsPrCompact.length_newtonSlopesLe_charPowerSeries_eq_finsum_finrank`,
  `ContinuousLinearMap.IsPrCompact.length_newtonSlopesLt_charPowerSeries_eq_finsum_finrank`);
* a real number `σ` has positive slope multiplicity if and only if it is the valuation of an
  eigenvalue
  (`ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_ne_zero_iff`).

For a row-compact operator `u` on a model space `C₀(I, R)` over any complete ultrametric Tate ring
`R`, bounded coefficient extension `u.mapCoeffs f hf` into a complete algebraically closed
ultrametric field `L` with compatible valuation preserves the Fredholm polygon and therefore express
both the individual slope multiplicities and the cutoff counts as sums of algebraic multiplicities
of `u.mapCoeffs f hf` in `L`
(`ContinuousLinearMap.IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_mapCoeffs`,
`ContinuousLinearMap.IsRowCompact.length_newtonSlopesLe_charPowerSeries_eq_finsum_mapCoeffs`),
independently of the choice of complete algebraically closed extension
(`ContinuousLinearMap.IsRowCompact.finsum_finrank_maxGenEigenspace_mapCoeffs_eq`,
`ContinuousLinearMap.IsRowCompact.finsum_finrank_maxGenEigenspace_le_mapCoeffs_eq`).

## Main results

* `ContinuousLinearMap.bddBelow_image_unitSlope_newtonPolygon_charPowerSeries`: the finite slopes
  of a Fredholm polygon are bounded below.
* `ContinuousLinearMap.IsPrCompact.exists_isFiniteFace_newtonPolygon_charPowerSeries`,
  `ContinuousLinearMap.IsPrCompact.finite_setOf_unitSlope_newtonPolygon_charPowerSeries_le`,
  `ContinuousLinearMap.IsPrCompact.tendsto_unitSlope_newtonPolygon_charPowerSeries`: existence of
  finite faces and local finiteness of Fredholm slopes.
* `ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_smul`,
  `ContinuousLinearMap.IsPrCompact.newtonSlopesLe_charPowerSeries_smul`: scaling shifts slopes by
  the valuation of the scalar.
* `ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_prodMap`,
  `ContinuousLinearMap.IsPrCompact.coe_newtonSlopesLe_charPowerSeries_prodMap`: block sums add
  slope multiplicities and cutoff slope multisets.
* `ContinuousLinearMap.newtonSlopeMultiplicity_charPowerSeries_of_finite`,
  `ContinuousLinearMap.coe_newtonSlopesLe_charPowerSeries_of_finite`,
  `ContinuousLinearMap.newtonSlopesLe_charPowerSeries_eq_of_split_of_isNilpotent`: finite-module
  comparison and invisibility of nilpotent blocks.
* `ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank`,
  `ContinuousLinearMap.IsPrCompact.length_newtonSlopesLe_charPowerSeries_eq_finsum_finrank`,
  `ContinuousLinearMap.IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_ne_zero_iff`:
  slope multiplicities and cutoff counts equal algebraic multiplicities over an algebraically
  closed field.
* `ContinuousLinearMap.IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_mapCoeffs`,
  `ContinuousLinearMap.IsRowCompact.length_newtonSlopesLe_charPowerSeries_eq_finsum_mapCoeffs`,
  `ContinuousLinearMap.IsRowCompact.finsum_finrank_maxGenEigenspace_mapCoeffs_eq`: eigenvalue
  counts in complete algebraically closed extensions and independence of the extension.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter TauCeti
open scoped ZeroAtInfty NNReal

universe u u₁ u₂ w w₁ w₂

namespace ContinuousLinearMap

section SeminormedCommRing

variable {R : Type w} [SeminormedCommRing R] (v : AddValuation R (WithTop ℝ))
  {M : Type u} [SeminormedAddCommGroup M] [Module R M]

/-- The finite unit slopes of the Fredholm polygon of any continuous linear endomorphism are
bounded below, since the Fredholm series has constant coefficient `1`. -/
theorem bddBelow_image_unitSlope_newtonPolygon_charPowerSeries (u : M →L[R] M) :
    BddBelow (unitSlope (u.charPowerSeries.newtonPolygon v) ''
      finiteEdges (u.charPowerSeries.newtonPolygon v)) :=
  u.charPowerSeries.bddBelow_image_unitSlope_newtonPolygon v

end SeminormedCommRing

section Ring

variable {R : Type w} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] (v : AddValuation R (WithTop ℝ))

/-- Scaling a row-compact endomorphism by a scalar `a` of finite valuation shifts every slope of
its Fredholm polygon by `v a`, preserving multiplicities. -/
theorem IsPrCompact.newtonSlopeMultiplicity_charPowerSeries_smul {M : Type u}
    [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M] {u : M →L[R] M}
    (hu : u.IsPrCompact) {a : R} (ha : v a ≠ ⊤) (σ : ℝ) :
    (a • u).charPowerSeries.newtonSlopeMultiplicity v (σ + (v a).untop₀) =
      u.charPowerSeries.newtonSlopeMultiplicity v σ := by
  rw [hu.charPowerSeries_smul a, PowerSeries.newtonSlopeMultiplicity_rescale _ ha]

/-- Scaling a row-compact endomorphism by a scalar `a` of finite valuation shifts its cutoff slope
list `newtonSlopesLe` by `(v a).untop₀`. -/
theorem IsPrCompact.newtonSlopesLe_charPowerSeries_smul {M : Type u}
    [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M] {u : M →L[R] M}
    (hu : u.IsPrCompact) {a : R} (ha : v a ≠ ⊤) (c : ℝ) :
    (a • u).charPowerSeries.newtonSlopesLe v (c + (v a).untop₀) =
      (u.charPowerSeries.newtonSlopesLe v c).map (· + (v a).untop₀) := by
  rw [hu.charPowerSeries_smul a, PowerSeries.newtonSlopesLe_rescale _ ha]

/-- Scaling a row-compact endomorphism by a scalar `a` of finite valuation shifts its strict cutoff
slope list `newtonSlopesLt` by `(v a).untop₀`. -/
theorem IsPrCompact.newtonSlopesLt_charPowerSeries_smul {M : Type u}
    [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M] {u : M →L[R] M}
    (hu : u.IsPrCompact) {a : R} (ha : v a ≠ ⊤) (c : ℝ) :
    (a • u).charPowerSeries.newtonSlopesLt v (c + (v a).untop₀) =
      (u.charPowerSeries.newtonSlopesLt v c).map (· + (v a).untop₀) := by
  rw [hu.charPowerSeries_smul a, PowerSeries.newtonSlopesLt_rescale _ ha]

/-- On a finitely generated module with property (Pr), the multiplicity of a slope in the
Fredholm polygon is its multiplicity in the finite slope multiset of the finite projective
determinant `det (1 - X u)`. -/
theorem newtonSlopeMultiplicity_charPowerSeries_of_finite {M : Type u} [NormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] [Module.Finite R M] (hM : HasPr R M) (u : M →L[R] M)
    (σ : ℝ) :
    haveI := hM.projective
    u.charPowerSeries.newtonSlopeMultiplicity v σ =
      (((u : M →ₗ[R] M).projectiveCharpolyRev).newtonSlopes v).count σ := by
  rw [charPowerSeries_eq_projectiveCharpolyRev hM, Polynomial.newtonSlopeMultiplicity_coe]

/-- On a finitely generated module with property (Pr), the multiset underlying the cutoff slope
list `newtonSlopesLe` of the Fredholm series is the filtered finite slope multiset of
`det (1 - X u)`. -/
theorem coe_newtonSlopesLe_charPowerSeries_of_finite {M : Type u} [NormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] [Module.Finite R M] (hM : HasPr R M) (u : M →L[R] M)
    (c : ℝ) :
    haveI := hM.projective
    (((u.charPowerSeries.newtonSlopesLe v c : List ℝ) : Multiset ℝ)) =
      (((u : M →ₗ[R] M).projectiveCharpolyRev).newtonSlopes v).filter (· ≤ c) := by
  rw [charPowerSeries_eq_projectiveCharpolyRev hM, Polynomial.coe_newtonSlopesLe]

/-- On a finitely generated module with property (Pr), the multiset underlying the strict cutoff
slope list `newtonSlopesLt` of the Fredholm series is the strictly filtered finite slope multiset
of `det (1 - X u)`. -/
theorem coe_newtonSlopesLt_charPowerSeries_of_finite {M : Type u} [NormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] [Module.Finite R M] (hM : HasPr R M) (u : M →L[R] M)
    (c : ℝ) :
    haveI := hM.projective
    (((u.charPowerSeries.newtonSlopesLt v c : List ℝ) : Multiset ℝ)) =
      (((u : M →ₗ[R] M).projectiveCharpolyRev).newtonSlopes v).filter (· < c) := by
  rw [charPowerSeries_eq_projectiveCharpolyRev hM, Polynomial.coe_newtonSlopesLt]

/-- On a finitely generated module with property (Pr), `newtonSlopesLe` of the Fredholm series is
the nondecreasing sort of the filtered finite slope multiset of `det (1 - X u)`. -/
theorem newtonSlopesLe_charPowerSeries_of_finite {M : Type u} [NormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] [Module.Finite R M] (hM : HasPr R M) (u : M →L[R] M)
    (c : ℝ) :
    haveI := hM.projective
    u.charPowerSeries.newtonSlopesLe v c =
      ((((u : M →ₗ[R] M).projectiveCharpolyRev).newtonSlopes v).filter (· ≤ c)).sort := by
  rw [charPowerSeries_eq_projectiveCharpolyRev hM, Polynomial.newtonSlopesLe_coe]

/-- On a finitely generated module with property (Pr), `newtonSlopesLt` of the Fredholm series is
the nondecreasing sort of the strictly filtered finite slope multiset of `det (1 - X u)`. -/
theorem newtonSlopesLt_charPowerSeries_of_finite {M : Type u} [NormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] [Module.Finite R M] (hM : HasPr R M) (u : M →L[R] M)
    (c : ℝ) :
    haveI := hM.projective
    u.charPowerSeries.newtonSlopesLt v c =
      ((((u : M →ₗ[R] M).projectiveCharpolyRev).newtonSlopes v).filter (· < c)).sort := by
  rw [charPowerSeries_eq_projectiveCharpolyRev hM, Polynomial.newtonSlopesLt_coe]

section Nilpotent

variable [IsReduced R]

/-- Over a reduced coefficient ring, a nilpotent endomorphism of a finitely generated module with
property (Pr) has Fredholm series `1`. -/
theorem charPowerSeries_eq_one_of_finite_of_isNilpotent {M : Type u} [NormedAddCommGroup M]
    [Module R M] [IsBoundedSMul R M] [Module.Finite R M] (hM : HasPr R M) {u : M →L[R] M}
    (hnil : IsNilpotent u) :
    u.charPowerSeries = 1 := by
  have := hM.projective
  have hnil' : IsNilpotent (u : M →ₗ[R] M) := hnil.map toLinearMapRingHom
  rw [charPowerSeries_eq_projectiveCharpolyRev hM,
    LinearMap.projectiveCharpolyRev_eq_one_of_isNilpotent hnil', Polynomial.coe_one]

/-- Over a reduced coefficient ring, a nilpotent endomorphism of a finitely generated module with
property (Pr) has no finite Fredholm slopes at any valuation. -/
theorem newtonSlopeMultiplicity_charPowerSeries_eq_zero_of_finite_of_isNilpotent {M : Type u}
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [Module.Finite R M] (hM : HasPr R M)
    {u : M →L[R] M} (hnil : IsNilpotent u) (σ : ℝ) :
    u.charPowerSeries.newtonSlopeMultiplicity v σ = 0 := by
  rw [charPowerSeries_eq_one_of_finite_of_isNilpotent hM hnil,
    PowerSeries.newtonSlopeMultiplicity_one]

/-- Over a reduced coefficient ring, a nilpotent endomorphism of a finitely generated module with
property (Pr) has empty cutoff slope list `newtonSlopesLe` at every cutoff. -/
theorem newtonSlopesLe_charPowerSeries_eq_nil_of_finite_of_isNilpotent {M : Type u}
    [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [Module.Finite R M] (hM : HasPr R M)
    {u : M →L[R] M} (hnil : IsNilpotent u) (c : ℝ) :
    u.charPowerSeries.newtonSlopesLe v c = [] := by
  rw [charPowerSeries_eq_one_of_finite_of_isNilpotent hM hnil, PowerSeries.newtonSlopesLe_one]

/-- Over a reduced coefficient ring, a nilpotent finite summand in an upper-triangular bounded
splitting does not change any slope multiplicity of the Fredholm polygon. -/
theorem newtonSlopeMultiplicity_charPowerSeries_eq_of_split_of_isNilpotent
    {M N P : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [Module.Finite R M]
    [SeminormedAddCommGroup N] [Module R N] [SeminormedAddCommGroup P] [Module R P]
    {w : P →L[R] P} (hw : w.IsPrCompact) (hM : HasPr R M) (hN : HasPr R N)
    (i : M →L[R] P) (r : P →L[R] M) (j : N →L[R] P) (s : P →L[R] N)
    (hsplit : i.comp r + j.comp s = .id R P) (htri : s.comp (w.comp i) = 0)
    (hnil : IsNilpotent (r.comp (w.comp i))) (σ : ℝ) :
    w.charPowerSeries.newtonSlopeMultiplicity v σ =
      (s.comp (w.comp j)).charPowerSeries.newtonSlopeMultiplicity v σ := by
  rw [TauCeti.charPowerSeries_eq_of_split_of_isNilpotent hw hM hN i r j s hsplit htri hnil]

/-- Over a reduced coefficient ring, a nilpotent finite summand in an upper-triangular bounded
splitting does not change the cutoff slope list `newtonSlopesLe`. -/
theorem newtonSlopesLe_charPowerSeries_eq_of_split_of_isNilpotent
    {M N P : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [Module.Finite R M]
    [SeminormedAddCommGroup N] [Module R N] [SeminormedAddCommGroup P] [Module R P]
    {w : P →L[R] P} (hw : w.IsPrCompact) (hM : HasPr R M) (hN : HasPr R N)
    (i : M →L[R] P) (r : P →L[R] M) (j : N →L[R] P) (s : P →L[R] N)
    (hsplit : i.comp r + j.comp s = .id R P) (htri : s.comp (w.comp i) = 0)
    (hnil : IsNilpotent (r.comp (w.comp i))) (c : ℝ) :
    w.charPowerSeries.newtonSlopesLe v c =
      (s.comp (w.comp j)).charPowerSeries.newtonSlopesLe v c := by
  rw [TauCeti.charPowerSeries_eq_of_split_of_isNilpotent hw hM hN i r j s hsplit htri hnil]

/-- Over a reduced coefficient ring, a nilpotent finite summand in an upper-triangular bounded
splitting does not change the strict cutoff slope list `newtonSlopesLt`. -/
theorem newtonSlopesLt_charPowerSeries_eq_of_split_of_isNilpotent
    {M N P : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [Module.Finite R M]
    [SeminormedAddCommGroup N] [Module R N] [SeminormedAddCommGroup P] [Module R P]
    {w : P →L[R] P} (hw : w.IsPrCompact) (hM : HasPr R M) (hN : HasPr R N)
    (i : M →L[R] P) (r : P →L[R] M) (j : N →L[R] P) (s : P →L[R] N)
    (hsplit : i.comp r + j.comp s = .id R P) (htri : s.comp (w.comp i) = 0)
    (hnil : IsNilpotent (r.comp (w.comp i))) (c : ℝ) :
    w.charPowerSeries.newtonSlopesLt v c =
      (s.comp (w.comp j)).charPowerSeries.newtonSlopesLt v c := by
  rw [TauCeti.charPowerSeries_eq_of_split_of_isNilpotent hw hM hN i r j s hsplit htri hnil]

end Nilpotent

section BaseChangeRing

variable {I : Type u} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  {S : Type w₁} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [TauCeti.NormedRing.IsTate S] {u : C₀(I, R) →L[R] C₀(I, R)}

omit v in
/-- On model spaces, `charPowerSeries` of a row-compact endomorphism commutes with bounded
coefficient extension. -/
theorem IsRowCompact.charPowerSeries_mapCoeffs (hu : u.IsRowCompact) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).charPowerSeries = PowerSeries.map f u.charPowerSeries := by
  rw [(hu.mapCoeffs f hf).charPowerSeries_eq_charPowerSeries_matrixCoeff,
    hu.charPowerSeries_map f hf, hu.charPowerSeries_eq_charPowerSeries_matrixCoeff]

/-- Bounded coefficient extension along a valuation-preserving ring homomorphism preserves every
slope multiplicity of the Fredholm polygon. -/
theorem IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) {w : AddValuation S (WithTop ℝ)}
    (hfw : ∀ r, w (f r) = v r) (σ : ℝ) :
    (u.mapCoeffs f hf).charPowerSeries.newtonSlopeMultiplicity w σ =
      u.charPowerSeries.newtonSlopeMultiplicity v σ := by
  rw [hu.charPowerSeries_mapCoeffs f hf, u.charPowerSeries.newtonSlopeMultiplicity_map v f hfw]

/-- Bounded coefficient extension along a valuation-preserving ring homomorphism preserves the
cutoff slope list `newtonSlopesLe` of the Fredholm polygon. -/
theorem IsRowCompact.newtonSlopesLe_charPowerSeries_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) {w : AddValuation S (WithTop ℝ)}
    (hfw : ∀ r, w (f r) = v r) (c : ℝ) :
    (u.mapCoeffs f hf).charPowerSeries.newtonSlopesLe w c =
      u.charPowerSeries.newtonSlopesLe v c := by
  rw [hu.charPowerSeries_mapCoeffs f hf, u.charPowerSeries.newtonSlopesLe_map v f hfw]

/-- Bounded coefficient extension along a valuation-preserving ring homomorphism preserves the
strict cutoff slope list `newtonSlopesLt` of the Fredholm polygon. -/
theorem IsRowCompact.newtonSlopesLt_charPowerSeries_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) {w : AddValuation S (WithTop ℝ)}
    (hfw : ∀ r, w (f r) = v r) (c : ℝ) :
    (u.mapCoeffs f hf).charPowerSeries.newtonSlopesLt w c =
      u.charPowerSeries.newtonSlopesLt v c := by
  rw [hu.charPowerSeries_mapCoeffs f hf, u.charPowerSeries.newtonSlopesLt_map v f hfw]

end BaseChangeRing

end Ring

section FieldNoValuation

variable {K : Type w} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {M : Type u} [SeminormedAddCommGroup M] [Module K M] [IsBoundedSMul K M] {u : M →L[K] M}

/-- Over a complete ultrametric field, a nonzero scalar `μ` has positive algebraic multiplicity for
a row-compact endomorphism `u` of a module with property (Pr) if and only if `μ` is an eigenvalue
of `u`. -/
theorem IsPrCompact.finrank_maxGenEigenspace_ne_zero_iff_hasEigenvalue (hu : u.IsPrCompact)
    {μ : K} (hμ : μ ≠ 0) :
    Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) ≠ 0 ↔
      Module.End.HasEigenvalue (u : Module.End K M) μ := by
  obtain ⟨h, hh⟩ := hu.isEntire_charPowerSeries.exists_isGoodZero u.charPowerSeries_ne_zero μ⁻¹
  obtain ⟨E, hE⟩ := hu.exists_isRieszProjection hh
  have hfin : Module.Finite K E.range :=
    (hE.isPrCompact hu).finite_range_of_isIdempotentElem hE.isIdempotentElem
  have hrng := hE.maxGenEigenspace_eq_range (inv_mul_cancel₀ hμ)
  have : Module.Finite K (Module.End.maxGenEigenspace (u : Module.End K M) μ) := hrng ▸ hfin
  rw [ne_eq, Submodule.finrank_eq_zero, ← ne_eq]
  exact Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (k := ⊤) (by simp)

/-- Over a complete ultrametric field, the zeros of the Fredholm series of a row-compact
endomorphism of a module with property (Pr) are exactly the inverses of its nonzero eigenvalues. -/
theorem IsPrCompact.evalAt_charPowerSeries_eq_zero_iff_hasEigenvalue (hu : u.IsPrCompact)
    {a : K} :
    u.charPowerSeries.evalAt a = 0 ↔
      a ≠ 0 ∧ Module.End.HasEigenvalue (u : Module.End K M) a⁻¹ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [PowerSeries.evalAt_at_zero]
  have hord := hu.finrank_maxGenEigenspace_eq_order_taylor (inv_ne_zero ha)
  rw [inv_inv] at hord
  rw [← PowerSeries.order_taylor_ne_zero_iff, ← hord, Nat.cast_ne_zero,
    hu.finrank_maxGenEigenspace_ne_zero_iff_hasEigenvalue (inv_ne_zero ha), and_iff_right ha]

end FieldNoValuation

section Field

variable {K : Type w} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {M N : Type u} [SeminormedAddCommGroup M] [Module K M]
  [SeminormedAddCommGroup N] [Module K N] {u : M →L[K] M} {w : N →L[K] N}

namespace IsPrCompact

variable {b : ℝ} (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- The Fredholm polygon of a row-compact endomorphism has a finite face of every real slope. -/
theorem exists_isFiniteFace_newtonPolygon_charPowerSeries (hu : u.IsPrCompact) (σ : ℝ) :
    ∃ l l' : ℕ, IsFiniteFace (u.charPowerSeries.newtonPolygon v) σ l l' :=
  hu.isEntire_charPowerSeries.exists_isFiniteFace_newtonPolygon v hb hv
    u.charPowerSeries_ne_zero σ

/-- **Local finiteness of Fredholm slopes.** Only finitely many finite unit edges of the
Fredholm polygon of a row-compact endomorphism have slope at most a given real number. -/
theorem finite_setOf_unitSlope_newtonPolygon_charPowerSeries_le (hu : u.IsPrCompact) (c : ℝ) :
    {n | n ∈ finiteEdges (u.charPowerSeries.newtonPolygon v) ∧
      unitSlope (u.charPowerSeries.newtonPolygon v) n ≤ c}.Finite :=
  hu.isEntire_charPowerSeries.finite_setOf_unitSlope_newtonPolygon_le v hb hv c

/-- Only finitely many finite unit edges of the Fredholm polygon of a row-compact endomorphism
have slope strictly below a given real number. -/
theorem finite_setOf_unitSlope_newtonPolygon_charPowerSeries_lt (hu : u.IsPrCompact) (c : ℝ) :
    {n | n ∈ finiteEdges (u.charPowerSeries.newtonPolygon v) ∧
      unitSlope (u.charPowerSeries.newtonPolygon v) n < c}.Finite :=
  hu.isEntire_charPowerSeries.finite_setOf_unitSlope_newtonPolygon_lt v hb hv c

/-- If the Fredholm polygon of a row-compact endomorphism has infinitely many finite unit edges,
their slopes tend to infinity. -/
theorem tendsto_unitSlope_newtonPolygon_charPowerSeries (hu : u.IsPrCompact)
    (hinf : (finiteEdges (u.charPowerSeries.newtonPolygon v)).Infinite) :
    Tendsto (unitSlope (u.charPowerSeries.newtonPolygon v)) atTop atTop :=
  hu.isEntire_charPowerSeries.tendsto_unitSlope_newtonPolygon v hb hv hinf

/-- The multiplicity of `σ` in `u.charPowerSeries.newtonSlopesLe v c` is
`u.charPowerSeries.newtonSlopeMultiplicity v σ` for `σ ≤ c`, and `0` above `c`. -/
theorem count_newtonSlopesLe_charPowerSeries (hu : u.IsPrCompact) (c σ : ℝ) :
    (u.charPowerSeries.newtonSlopesLe v c).count σ =
      if σ ≤ c then u.charPowerSeries.newtonSlopeMultiplicity v σ else 0 :=
  hu.isEntire_charPowerSeries.count_newtonSlopesLe v hb hv c σ

/-- The multiplicity of `σ` in `u.charPowerSeries.newtonSlopesLt v c` is
`u.charPowerSeries.newtonSlopeMultiplicity v σ` for `σ < c`, and `0` from `c` on. -/
theorem count_newtonSlopesLt_charPowerSeries (hu : u.IsPrCompact) (c σ : ℝ) :
    (u.charPowerSeries.newtonSlopesLt v c).count σ =
      if σ < c then u.charPowerSeries.newtonSlopeMultiplicity v σ else 0 :=
  hu.isEntire_charPowerSeries.count_newtonSlopesLt v hb hv c σ

/-- A real number belongs to `u.charPowerSeries.newtonSlopesLe v c` iff it is at most `c` and has
nonzero Fredholm slope multiplicity. -/
theorem mem_newtonSlopesLe_charPowerSeries_iff (hu : u.IsPrCompact) {c σ : ℝ} :
    σ ∈ u.charPowerSeries.newtonSlopesLe v c ↔
      σ ≤ c ∧ u.charPowerSeries.newtonSlopeMultiplicity v σ ≠ 0 :=
  hu.isEntire_charPowerSeries.mem_newtonSlopesLe_iff v hb hv

/-- A real number belongs to `u.charPowerSeries.newtonSlopesLt v c` iff it is strictly below `c`
and has nonzero Fredholm slope multiplicity. -/
theorem mem_newtonSlopesLt_charPowerSeries_iff (hu : u.IsPrCompact) {c σ : ℝ} :
    σ ∈ u.charPowerSeries.newtonSlopesLt v c ↔
      σ < c ∧ u.charPowerSeries.newtonSlopeMultiplicity v σ ≠ 0 :=
  hu.isEntire_charPowerSeries.mem_newtonSlopesLt_iff v hb hv

/-- **Block sums add multiplicities.** The multiplicity of every slope of the Fredholm polygon of
a block diagonal operator is the sum of its multiplicities for the two blocks. -/
theorem newtonSlopeMultiplicity_charPowerSeries_prodMap (hu : u.IsPrCompact)
    (hw : w.IsPrCompact) (σ : ℝ) :
    (u.prodMap w).charPowerSeries.newtonSlopeMultiplicity v σ =
      u.charPowerSeries.newtonSlopeMultiplicity v σ +
        w.charPowerSeries.newtonSlopeMultiplicity v σ := by
  rw [charPowerSeries_prodMap hu hw]
  exact hu.isEntire_charPowerSeries.newtonSlopeMultiplicity_mul v hb hv
    hw.isEntire_charPowerSeries u.charPowerSeries_ne_zero w.charPowerSeries_ne_zero σ

/-- **Block sums add cutoff slope multisets.** For a block diagonal operator, the multiset of
Fredholm slopes at most `c` is the sum of the cutoff slope multisets of the two blocks. -/
theorem coe_newtonSlopesLe_charPowerSeries_prodMap (hu : u.IsPrCompact) (hw : w.IsPrCompact)
    (c : ℝ) :
    ((((u.prodMap w).charPowerSeries.newtonSlopesLe v c : List ℝ) : Multiset ℝ)) =
      (u.charPowerSeries.newtonSlopesLe v c : Multiset ℝ) +
        (w.charPowerSeries.newtonSlopesLe v c : Multiset ℝ) := by
  rw [charPowerSeries_prodMap hu hw]
  exact hu.isEntire_charPowerSeries.coe_newtonSlopesLe_mul v hb hv hw.isEntire_charPowerSeries
    u.charPowerSeries_ne_zero w.charPowerSeries_ne_zero c

/-- **Block sums add strict cutoff slope multisets.** For a block diagonal operator, the multiset
of Fredholm slopes strictly below `c` is the sum of the strict cutoff slope multisets of the two
blocks. -/
theorem coe_newtonSlopesLt_charPowerSeries_prodMap (hu : u.IsPrCompact) (hw : w.IsPrCompact)
    (c : ℝ) :
    ((((u.prodMap w).charPowerSeries.newtonSlopesLt v c : List ℝ) : Multiset ℝ)) =
      (u.charPowerSeries.newtonSlopesLt v c : Multiset ℝ) +
        (w.charPowerSeries.newtonSlopesLt v c : Multiset ℝ) := by
  rw [charPowerSeries_prodMap hu hw]
  exact hu.isEntire_charPowerSeries.coe_newtonSlopesLt_mul v hb hv hw.isEntire_charPowerSeries
    u.charPowerSeries_ne_zero w.charPowerSeries_ne_zero c

/-- For a block diagonal operator, the number of Fredholm slopes at most `c` is the sum of the
counts for the two blocks. -/
theorem length_newtonSlopesLe_charPowerSeries_prodMap (hu : u.IsPrCompact) (hw : w.IsPrCompact)
    (c : ℝ) :
    ((u.prodMap w).charPowerSeries.newtonSlopesLe v c).length =
      (u.charPowerSeries.newtonSlopesLe v c).length +
        (w.charPowerSeries.newtonSlopesLe v c).length := by
  rw [charPowerSeries_prodMap hu hw]
  exact hu.isEntire_charPowerSeries.length_newtonSlopesLe_mul v hb hv hw.isEntire_charPowerSeries
    u.charPowerSeries_ne_zero w.charPowerSeries_ne_zero c

/-- For a block diagonal operator, the number of Fredholm slopes strictly below `c` is the sum of
the counts for the two blocks. -/
theorem length_newtonSlopesLt_charPowerSeries_prodMap (hu : u.IsPrCompact) (hw : w.IsPrCompact)
    (c : ℝ) :
    ((u.prodMap w).charPowerSeries.newtonSlopesLt v c).length =
      (u.charPowerSeries.newtonSlopesLt v c).length +
        (w.charPowerSeries.newtonSlopesLt v c).length := by
  rw [charPowerSeries_prodMap hu hw]
  exact hu.isEntire_charPowerSeries.length_newtonSlopesLt_mul v hb hv hw.isEntire_charPowerSeries
    u.charPowerSeries_ne_zero w.charPowerSeries_ne_zero c

/-- Along an upper-triangular bounded splitting `i r + j s = id` through modules with property
(Pr), the cutoff slope multiset `newtonSlopesLe` is the sum of those of the two diagonal blocks. -/
theorem coe_newtonSlopesLe_charPowerSeries_of_split {P : Type*} [SeminormedAddCommGroup P]
    [Module K P] {t : P →L[K] P} (ht : t.IsPrCompact) (hM : HasPr K M) (hN : HasPr K N)
    (i : M →L[K] P) (r : P →L[K] M) (j : N →L[K] P) (s : P →L[K] N)
    (hsplit : i.comp r + j.comp s = .id K P) (htri : s.comp (t.comp i) = 0) (c : ℝ) :
    (((t.charPowerSeries.newtonSlopesLe v c : List ℝ) : Multiset ℝ)) =
      ((r.comp (t.comp i)).charPowerSeries.newtonSlopesLe v c : Multiset ℝ) +
        ((s.comp (t.comp j)).charPowerSeries.newtonSlopesLe v c : Multiset ℝ) := by
  rw [TauCeti.charPowerSeries_eq_mul_of_split ht hM hN i r j s hsplit htri]
  exact ((ht.comp_clm i hM).clm_comp r hM).isEntire_charPowerSeries.coe_newtonSlopesLe_mul v hb hv
    ((ht.comp_clm j hN).clm_comp s hN).isEntire_charPowerSeries
    (charPowerSeries_ne_zero _) (charPowerSeries_ne_zero _) c

/-- Every eigenvalue `μ` of valuation `σ` of a row-compact endomorphism `u` contributes positively
to the Fredholm slope multiplicity at `σ`, without assuming algebraic closedness. -/
theorem newtonSlopeMultiplicity_charPowerSeries_ne_zero_of_hasEigenvalue [IsBoundedSMul K M]
    (hu : u.IsPrCompact) {μ : K} {σ : ℝ} (hμσ : v μ = σ)
    (hμ : Module.End.HasEigenvalue (u : Module.End K M) μ) :
    u.charPowerSeries.newtonSlopeMultiplicity v σ ≠ 0 := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hμ0 : μ ≠ 0 := fun h0 ↦ by simp [h0] at hμσ
  have hxnorm : ‖μ⁻¹‖ = b ^ σ := by
    rw [norm_inv, inv_eq_iff_eq_inv, ← Real.rpow_neg hb0.le, v.norm_eq_rpow_iff hb hv, neg_neg]
    exact hμσ
  have hfx : u.charPowerSeries.evalAt μ⁻¹ = 0 :=
    hu.evalAt_charPowerSeries_eq_zero_iff_hasEigenvalue.mpr
      ⟨inv_ne_zero hμ0, (inv_inv μ).symm ▸ hμ⟩
  exact hu.isEntire_charPowerSeries.newtonSlopeMultiplicity_ne_zero_of_evalAt_eq_zero v hb hv
    u.charPowerSeries_ne_zero hxnorm hfx

omit hb hv in
/-- Bijection between eigenvalues satisfying a valuation condition bounded above by `c` and nonzero
Fredholm zeros in the corresponding punctured set, equating algebraic multiplicities with orders of
zeros. -/
private theorem finsum_finrank_maxGenEigenspace_eq_finsum_order_taylor
    [IsBoundedSMul K M] (hu : u.IsPrCompact) {c : ℝ} {p : WithTop ℝ → Prop} {q : ℝ → Prop}
    (hq : ∀ r, q r → r ≤ b ^ c)
    (hpq : ∀ μ : K, p (v μ) ↔ μ ≠ 0 ∧ q ‖μ⁻¹‖) :
    ((∑ᶠ μ ∈ {μ : K | p (v μ)},
      Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) : ℕ) : ℕ∞) =
      ∑ᶠ x ∈ {x : K | x ≠ 0 ∧ q ‖x‖},
        (PowerSeries.taylor x u.charPowerSeries).order := by
  have hH := hu.isEntire_charPowerSeries
  have hH0 := u.charPowerSeries_ne_zero
  have hbij : Set.BijOn (·⁻¹) {μ : K | p (v μ)} {x : K | x ≠ 0 ∧ q ‖x‖} := by
    refine ⟨fun μ hμ ↦ ?_, inv_injective.injOn, fun x ⟨hx0, hqx⟩ ↦ ⟨x⁻¹, ?_, inv_inv x⟩⟩
    · obtain ⟨hμ0, hqμ⟩ := (hpq μ).mp hμ
      exact ⟨inv_ne_zero hμ0, hqμ⟩
    · rw [Set.mem_ofPred_eq, hpq, inv_inv]
      exact ⟨inv_ne_zero hx0, hqx⟩
  have hord {μ : K} (hμ : p (v μ)) :
      (Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) : ℕ∞) =
        (PowerSeries.taylor μ⁻¹ u.charPowerSeries).order :=
    hu.finrank_maxGenEigenspace_eq_order_taylor ((hpq μ).mp hμ).1
  have hfin : ({μ : K | p (v μ)} ∩ Function.support fun μ ↦
      Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ)).Finite := by
    refine ((PowerSeries.IsRestricted.finite_setOf_norm_le_and_evalAt_eq_zero (L := K)
      (hH.isRestricted (b ^ c)) hH0).image (·⁻¹)).subset ?_
    rintro μ ⟨hμp, hμ⟩
    rw [Function.mem_support, ← Nat.cast_ne_zero (R := ℕ∞), hord hμp,
      PowerSeries.order_taylor_ne_zero_iff] at hμ
    exact ⟨μ⁻¹, ⟨hq _ ((hpq μ).mp hμp).2, hμ⟩, inv_inv μ⟩
  rw [← Nat.coe_castAddMonoidHom, (Nat.castAddMonoidHom ℕ∞).map_finsum_mem' hfin]
  exact finsum_mem_eq_of_bijOn _ hbij fun μ hμ ↦ hord hμ

/-- **Slopes are the valuations of the eigenvalues, with multiplicity.** Over a complete
algebraically closed ultrametric field, the multiplicity of the slope `σ` in the Fredholm polygon
of a row-compact endomorphism `u` of a module with property (Pr) is the sum of the algebraic
multiplicities `dim (maxGenEigenspace u μ)` over the eigenvalues `μ` of valuation `σ`. -/
theorem newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) (σ : ℝ) :
    u.charPowerSeries.newtonSlopeMultiplicity v σ =
      ∑ᶠ μ ∈ {μ : K | v μ = σ},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have key : (u.charPowerSeries.newtonSlopeMultiplicity v σ : ℕ∞) =
      ((∑ᶠ μ ∈ {μ : K | v μ = σ},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) : ℕ) : ℕ∞) := by
    rw [hu.isEntire_charPowerSeries.newtonSlopeMultiplicity_eq_finsum_order_taylor v hb hv
      u.charPowerSeries_ne_zero σ,
      finsum_finrank_maxGenEigenspace_eq_finsum_order_taylor (c := σ)
        (p := (· = (σ : WithTop ℝ))) (q := (· = b ^ σ)) v hu (fun _ h ↦ h.le) ?_]
    · refine finsum_congr fun x ↦ ?_
      rcases eq_or_ne x 0 with rfl | hx0
      · simp [(Real.rpow_pos_of_pos hb0 σ).ne]
      · simp [hx0]
    · intro μ
      rcases eq_or_ne μ 0 with rfl | hμ0
      · simp
      · simp only [hμ0, ne_eq, not_false_eq_true, true_and, norm_inv, inv_eq_iff_eq_inv,
          ← Real.rpow_neg hb0.le, v.norm_eq_rpow_iff hb hv, neg_neg]
  exact_mod_cast key

/-- **Cutoff slope counts equal eigenvalue counts up to the cutoff.** Over a complete algebraically
closed ultrametric field, the length of `u.charPowerSeries.newtonSlopesLe v c` is the sum of the
algebraic multiplicities `dim (maxGenEigenspace u μ)` over the eigenvalues `μ` with `v μ ≤ c`.
Note `v 0 = ⊤`, so `0` is automatically excluded. -/
theorem length_newtonSlopesLe_charPowerSeries_eq_finsum_finrank [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) (c : ℝ) :
    (u.charPowerSeries.newtonSlopesLe v c).length =
      ∑ᶠ μ ∈ {μ : K | v μ ≤ c},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have key : ((u.charPowerSeries.newtonSlopesLe v c).length : ℕ∞) =
      ((∑ᶠ μ ∈ {μ : K | v μ ≤ c},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) : ℕ) : ℕ∞) := by
    rw [hu.isEntire_charPowerSeries.length_newtonSlopesLe_eq_finsum_order_taylor v hb hv
      u.charPowerSeries_ne_zero c,
      finsum_finrank_maxGenEigenspace_eq_finsum_order_taylor (c := c)
        (p := (· ≤ (c : WithTop ℝ))) (q := (· ≤ b ^ c)) v hu (fun _ h ↦ h)]
    intro μ
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simp
    · rw [← WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.mpr hμ0), WithTop.coe_le_coe, norm_inv,
        hv μ hμ0, ← Real.rpow_neg hb0.le, neg_neg, Real.rpow_le_rpow_left_iff hb]
      simp [hμ0]
  exact_mod_cast key

/-- **Strict cutoff slope counts equal eigenvalue counts strictly below the cutoff.** Over a
complete algebraically closed ultrametric field, the length of
`u.charPowerSeries.newtonSlopesLt v c` is the sum of the algebraic multiplicities
`dim (maxGenEigenspace u μ)` over the eigenvalues `μ` with `v μ < c`. -/
theorem length_newtonSlopesLt_charPowerSeries_eq_finsum_finrank [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) (c : ℝ) :
    (u.charPowerSeries.newtonSlopesLt v c).length =
      ∑ᶠ μ ∈ {μ : K | v μ < c},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have key : ((u.charPowerSeries.newtonSlopesLt v c).length : ℕ∞) =
      ((∑ᶠ μ ∈ {μ : K | v μ < c},
        Module.finrank K (Module.End.maxGenEigenspace (u : Module.End K M) μ) : ℕ) : ℕ∞) := by
    rw [hu.isEntire_charPowerSeries.length_newtonSlopesLt_eq_finsum_order_taylor v hb hv
      u.charPowerSeries_ne_zero c,
      finsum_finrank_maxGenEigenspace_eq_finsum_order_taylor (c := c)
        (p := (· < (c : WithTop ℝ))) (q := (· < b ^ c)) v hu (fun _ h ↦ h.le)]
    intro μ
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simp
    · rw [← WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.mpr hμ0), WithTop.coe_lt_coe, norm_inv,
        hv μ hμ0, ← Real.rpow_neg hb0.le, neg_neg, Real.rpow_lt_rpow_left_iff hb]
      simp [hμ0]
  exact_mod_cast key

/-- **Eigenvalues at every slope.** Over a complete algebraically closed ultrametric field, every
finite slope `σ` of the Fredholm polygon of a row-compact endomorphism `u` of a module with
property (Pr) is the valuation of an eigenvalue of `u`. -/
theorem exists_hasEigenvalue_of_newtonSlopeMultiplicity_ne_zero [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) {σ : ℝ}
    (hσ : u.charPowerSeries.newtonSlopeMultiplicity v σ ≠ 0) :
    ∃ μ : K, v μ = σ ∧ Module.End.HasEigenvalue (u : Module.End K M) μ := by
  rw [newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank v hb hv hu] at hσ
  obtain ⟨μ, hμσ, hμ⟩ := exists_ne_zero_of_finsum_mem_ne_zero hσ
  exact ⟨μ, hμσ,
    (hu.finrank_maxGenEigenspace_ne_zero_iff_hasEigenvalue fun h0 ↦ by simp [h0] at hμσ).mp hμ⟩

/-- Over a complete algebraically closed ultrametric field, a real number `σ` has positive
Fredholm slope multiplicity if and only if it is the valuation of an eigenvalue of `u`. -/
theorem newtonSlopeMultiplicity_charPowerSeries_ne_zero_iff [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) {σ : ℝ} :
    u.charPowerSeries.newtonSlopeMultiplicity v σ ≠ 0 ↔
      ∃ μ : K, v μ = σ ∧ Module.End.HasEigenvalue (u : Module.End K M) μ :=
  ⟨hu.exists_hasEigenvalue_of_newtonSlopeMultiplicity_ne_zero v hb hv,
    fun ⟨_, hμσ, hμ⟩ ↦ hu.newtonSlopeMultiplicity_charPowerSeries_ne_zero_of_hasEigenvalue
      v hb hv hμσ hμ⟩

/-- Over a complete algebraically closed ultrametric field, a nilpotent row-compact endomorphism
of any module with property (Pr) has no finite Fredholm slopes. -/
theorem newtonSlopeMultiplicity_charPowerSeries_eq_zero_of_isNilpotent [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) (hnil : IsNilpotent u) (σ : ℝ) :
    u.charPowerSeries.newtonSlopeMultiplicity v σ = 0 := by
  by_contra hne
  obtain ⟨μ, hμσ, hμ⟩ := hu.exists_hasEigenvalue_of_newtonSlopeMultiplicity_ne_zero v hb hv hne
  have hμ0 : μ = 0 := (hμ.isNilpotent_of_isNilpotent (hnil.map toLinearMapRingHom)).eq_zero
  simp [hμ0] at hμσ

/-- Over a complete algebraically closed ultrametric field, a nilpotent row-compact endomorphism
of any module with property (Pr) has empty cutoff slope list `newtonSlopesLe` at every cutoff. -/
theorem newtonSlopesLe_charPowerSeries_eq_nil_of_isNilpotent [IsAlgClosed K]
    [IsBoundedSMul K M] (hu : u.IsPrCompact) (hnil : IsNilpotent u) (c : ℝ) :
    u.charPowerSeries.newtonSlopesLe v c = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro σ hσ
  exact ((hu.mem_newtonSlopesLe_charPowerSeries_iff v hb hv).mp hσ).2
    (hu.newtonSlopeMultiplicity_charPowerSeries_eq_zero_of_isNilpotent v hb hv hnil σ)

end IsPrCompact

end Field

section SplittingExtension

variable {I : Type u} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  {R : Type w} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] (v : AddValuation R (WithTop ℝ))
  {u : C₀(I, R) →L[R] C₀(I, R)}

section SingleExtension

variable {L : Type w₁} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L] (w : AddValuation L (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hw : ∀ y ≠ 0, ‖y‖ = b ^ (-(w y).untop₀))

include hb hw

/-- **Eigenvalue counts at a slope in a complete algebraically closed extension.** Let `u` be a
row-compact endomorphism of `C₀(I, R)` and `f : R →+* L` a bounded homomorphism into a complete
algebraically closed ultrametric field `L` with compatible valuation `w (f r) = v r`. The
multiplicity of the slope `σ` in the Fredholm polygon of `u` equals the sum of the algebraic
multiplicities of `u.mapCoeffs f hf` over the eigenvalues `μ ∈ L` with `w μ = σ`. -/
theorem IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_mapCoeffs
    (hu : u.IsRowCompact) (f : R →+* L) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hfw : ∀ r, w (f r) = v r) (σ : ℝ) :
    u.charPowerSeries.newtonSlopeMultiplicity v σ =
      ∑ᶠ μ ∈ {μ : L | w μ = σ},
        Module.finrank L
          (Module.End.maxGenEigenspace (u.mapCoeffs f hf : Module.End L C₀(I, L)) μ) := by
  rw [← hu.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs v f hf hfw σ]
  exact (isPrCompact_iff_isRowCompact.mpr (hu.mapCoeffs f hf))
    |>.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_finrank w hb hw σ

/-- **Cutoff eigenvalue counts in a complete algebraically closed extension.** For a row-compact
endomorphism `u` of `C₀(I, R)` and a bounded valuation-preserving homomorphism `f : R →+* L` into
a complete algebraically closed ultrametric field, the length of
`u.charPowerSeries.newtonSlopesLe v c` is the sum of the algebraic multiplicities of
`u.mapCoeffs f hf` over `μ ∈ L` with `w μ ≤ c`. -/
theorem IsRowCompact.length_newtonSlopesLe_charPowerSeries_eq_finsum_mapCoeffs
    (hu : u.IsRowCompact) (f : R →+* L) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hfw : ∀ r, w (f r) = v r) (c : ℝ) :
    (u.charPowerSeries.newtonSlopesLe v c).length =
      ∑ᶠ μ ∈ {μ : L | w μ ≤ c},
        Module.finrank L
          (Module.End.maxGenEigenspace (u.mapCoeffs f hf : Module.End L C₀(I, L)) μ) := by
  rw [← hu.newtonSlopesLe_charPowerSeries_mapCoeffs v f hf hfw c]
  exact (isPrCompact_iff_isRowCompact.mpr (hu.mapCoeffs f hf))
    |>.length_newtonSlopesLe_charPowerSeries_eq_finsum_finrank w hb hw c

/-- **Strict cutoff eigenvalue counts in a complete algebraically closed extension.** For a
row-compact endomorphism `u` of `C₀(I, R)` and a bounded valuation-preserving homomorphism
`f : R →+* L` into a complete algebraically closed ultrametric field, the length of
`u.charPowerSeries.newtonSlopesLt v c` is the sum of the algebraic multiplicities of
`u.mapCoeffs f hf` over `μ ∈ L` with `w μ < c`. -/
theorem IsRowCompact.length_newtonSlopesLt_charPowerSeries_eq_finsum_mapCoeffs
    (hu : u.IsRowCompact) (f : R →+* L) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hfw : ∀ r, w (f r) = v r) (c : ℝ) :
    (u.charPowerSeries.newtonSlopesLt v c).length =
      ∑ᶠ μ ∈ {μ : L | w μ < c},
        Module.finrank L
          (Module.End.maxGenEigenspace (u.mapCoeffs f hf : Module.End L C₀(I, L)) μ) := by
  rw [← hu.newtonSlopesLt_charPowerSeries_mapCoeffs v f hf hfw c]
  exact (isPrCompact_iff_isRowCompact.mpr (hu.mapCoeffs f hf))
    |>.length_newtonSlopesLt_charPowerSeries_eq_finsum_finrank w hb hw c

/-- In any complete algebraically closed ultrametric extension `L` with compatible valuation, a
real number `σ` has positive Fredholm slope multiplicity for `u` if and only if `u.mapCoeffs f hf`
has an eigenvalue in `L` of valuation `σ`. -/
theorem IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_ne_zero_iff_mapCoeffs
    (hu : u.IsRowCompact) (f : R →+* L) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hfw : ∀ r, w (f r) = v r) {σ : ℝ} :
    u.charPowerSeries.newtonSlopeMultiplicity v σ ≠ 0 ↔
      ∃ μ : L, w μ = σ ∧
        Module.End.HasEigenvalue (u.mapCoeffs f hf : Module.End L C₀(I, L)) μ := by
  rw [← hu.newtonSlopeMultiplicity_charPowerSeries_mapCoeffs v f hf hfw σ]
  exact (isPrCompact_iff_isRowCompact.mpr (hu.mapCoeffs f hf))
    |>.newtonSlopeMultiplicity_charPowerSeries_ne_zero_iff w hb hw

end SingleExtension

section ExtensionIndependence

variable {L₁ : Type w₁} [NontriviallyNormedField L₁] [IsUltrametricDist L₁] [CompleteSpace L₁]
  [IsAlgClosed L₁] (w₁ : AddValuation L₁ (WithTop ℝ)) {b₁ : ℝ} (hb₁ : 1 < b₁)
  (hw₁ : ∀ y ≠ 0, ‖y‖ = b₁ ^ (-(w₁ y).untop₀))
  {L₂ : Type w₂} [NontriviallyNormedField L₂] [IsUltrametricDist L₂] [CompleteSpace L₂]
  [IsAlgClosed L₂] (w₂ : AddValuation L₂ (WithTop ℝ)) {b₂ : ℝ} (hb₂ : 1 < b₂)
  (hw₂ : ∀ y ≠ 0, ‖y‖ = b₂ ^ (-(w₂ y).untop₀))

include hb₁ hw₁ hb₂ hw₂

/-- **Independence of the complete splitting extension at a slope.** The total algebraic
multiplicity of the eigenvalues of valuation `σ` of `u.mapCoeffs` is the same in every complete
algebraically closed ultrametric extension with compatible valuation. -/
theorem IsRowCompact.finsum_finrank_maxGenEigenspace_mapCoeffs_eq (hu : u.IsRowCompact)
    (f₁ : R →+* L₁) (hf₁ : ∃ C : ℝ≥0, ∀ r, ‖f₁ r‖ ≤ C * ‖r‖) (hfw₁ : ∀ r, w₁ (f₁ r) = v r)
    (f₂ : R →+* L₂) (hf₂ : ∃ C : ℝ≥0, ∀ r, ‖f₂ r‖ ≤ C * ‖r‖) (hfw₂ : ∀ r, w₂ (f₂ r) = v r)
    (σ : ℝ) :
    (∑ᶠ μ ∈ {μ : L₁ | w₁ μ = σ},
      Module.finrank L₁
        (Module.End.maxGenEigenspace (u.mapCoeffs f₁ hf₁ : Module.End L₁ C₀(I, L₁)) μ)) =
    ∑ᶠ μ ∈ {μ : L₂ | w₂ μ = σ},
      Module.finrank L₂
        (Module.End.maxGenEigenspace (u.mapCoeffs f₂ hf₂ : Module.End L₂ C₀(I, L₂)) μ) := by
  rw [← hu.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_mapCoeffs v w₁ hb₁ hw₁
      f₁ hf₁ hfw₁ σ,
    hu.newtonSlopeMultiplicity_charPowerSeries_eq_finsum_mapCoeffs v w₂ hb₂ hw₂
      f₂ hf₂ hfw₂ σ]

/-- **Independence of the complete splitting extension up to a cutoff.** The total algebraic
multiplicity of the eigenvalues of valuation at most `c` of `u.mapCoeffs` is the same in every
complete algebraically closed ultrametric extension with compatible valuation. -/
theorem IsRowCompact.finsum_finrank_maxGenEigenspace_le_mapCoeffs_eq (hu : u.IsRowCompact)
    (f₁ : R →+* L₁) (hf₁ : ∃ C : ℝ≥0, ∀ r, ‖f₁ r‖ ≤ C * ‖r‖) (hfw₁ : ∀ r, w₁ (f₁ r) = v r)
    (f₂ : R →+* L₂) (hf₂ : ∃ C : ℝ≥0, ∀ r, ‖f₂ r‖ ≤ C * ‖r‖) (hfw₂ : ∀ r, w₂ (f₂ r) = v r)
    (c : ℝ) :
    (∑ᶠ μ ∈ {μ : L₁ | w₁ μ ≤ c},
      Module.finrank L₁
        (Module.End.maxGenEigenspace (u.mapCoeffs f₁ hf₁ : Module.End L₁ C₀(I, L₁)) μ)) =
    ∑ᶠ μ ∈ {μ : L₂ | w₂ μ ≤ c},
      Module.finrank L₂
        (Module.End.maxGenEigenspace (u.mapCoeffs f₂ hf₂ : Module.End L₂ C₀(I, L₂)) μ) := by
  rw [← hu.length_newtonSlopesLe_charPowerSeries_eq_finsum_mapCoeffs v w₁ hb₁ hw₁
      f₁ hf₁ hfw₁ c,
    hu.length_newtonSlopesLe_charPowerSeries_eq_finsum_mapCoeffs v w₂ hb₂ hw₂
      f₂ hf₂ hfw₂ c]

/-- **Independence of the complete splitting extension strictly below a cutoff.** The total
algebraic multiplicity of the eigenvalues of valuation strictly below `c` of `u.mapCoeffs` is the
same in every complete algebraically closed ultrametric extension with compatible valuation. -/
theorem IsRowCompact.finsum_finrank_maxGenEigenspace_lt_mapCoeffs_eq (hu : u.IsRowCompact)
    (f₁ : R →+* L₁) (hf₁ : ∃ C : ℝ≥0, ∀ r, ‖f₁ r‖ ≤ C * ‖r‖) (hfw₁ : ∀ r, w₁ (f₁ r) = v r)
    (f₂ : R →+* L₂) (hf₂ : ∃ C : ℝ≥0, ∀ r, ‖f₂ r‖ ≤ C * ‖r‖) (hfw₂ : ∀ r, w₂ (f₂ r) = v r)
    (c : ℝ) :
    (∑ᶠ μ ∈ {μ : L₁ | w₁ μ < c},
      Module.finrank L₁
        (Module.End.maxGenEigenspace (u.mapCoeffs f₁ hf₁ : Module.End L₁ C₀(I, L₁)) μ)) =
    ∑ᶠ μ ∈ {μ : L₂ | w₂ μ < c},
      Module.finrank L₂
        (Module.End.maxGenEigenspace (u.mapCoeffs f₂ hf₂ : Module.End L₂ C₀(I, L₂)) μ) := by
  rw [← hu.length_newtonSlopesLt_charPowerSeries_eq_finsum_mapCoeffs v w₁ hb₁ hw₁
      f₁ hf₁ hfw₁ c,
    hu.length_newtonSlopesLt_charPowerSeries_eq_finsum_mapCoeffs v w₂ hb₂ hw₂
      f₂ hf₂ hfw₂ c]

/-- Existence of an eigenvalue of valuation `σ` of `u.mapCoeffs` is independent of the choice of
complete algebraically closed ultrametric extension with compatible valuation. -/
theorem IsRowCompact.exists_hasEigenvalue_mapCoeffs_iff (hu : u.IsRowCompact)
    (f₁ : R →+* L₁) (hf₁ : ∃ C : ℝ≥0, ∀ r, ‖f₁ r‖ ≤ C * ‖r‖) (hfw₁ : ∀ r, w₁ (f₁ r) = v r)
    (f₂ : R →+* L₂) (hf₂ : ∃ C : ℝ≥0, ∀ r, ‖f₂ r‖ ≤ C * ‖r‖) (hfw₂ : ∀ r, w₂ (f₂ r) = v r)
    {σ : ℝ} :
    (∃ μ : L₁, w₁ μ = σ ∧
      Module.End.HasEigenvalue (u.mapCoeffs f₁ hf₁ : Module.End L₁ C₀(I, L₁)) μ) ↔
    (∃ μ : L₂, w₂ μ = σ ∧
      Module.End.HasEigenvalue (u.mapCoeffs f₂ hf₂ : Module.End L₂ C₀(I, L₂)) μ) := by
  rw [← hu.newtonSlopeMultiplicity_charPowerSeries_ne_zero_iff_mapCoeffs
      v w₁ hb₁ hw₁ f₁ hf₁ hfw₁,
    hu.newtonSlopeMultiplicity_charPowerSeries_ne_zero_iff_mapCoeffs
      v w₂ hb₂ hw₂ f₂ hf₂ hfw₂]

end ExtensionIndependence

end SplittingExtension

end ContinuousLinearMap
