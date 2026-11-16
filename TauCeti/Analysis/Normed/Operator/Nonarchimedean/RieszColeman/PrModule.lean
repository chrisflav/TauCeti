/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.ModelSpace
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

/-!
# Riesz–Coleman decompositions on modules with property (Pr)

Over a complete ultrametric normed commutative ring `R` with Tate scalars, a module `M` with
property (Pr) is a continuous linear retract `r ∘ i = id` of a model space `C₀(J, R)`.
Riesz–Coleman projections compress along such retracts
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`), and when `Q` has invertible
leading coefficient re-extending recovers the ambient projector
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`). Since the Fredholm series
`H_u` of a row-compact endomorphism `u` of `M` equals that of its extension `i ∘ u ∘ r`
(`ContinuousLinearMap.IsPrCompact.charPowerSeries_eq`), every coprime polynomial factorisation
`H_u = Q S` with `Q(0) = 1`, `lc(Q)` a unit, and `S` entire produces a unique Riesz–Coleman
projection `E` of `u` at `Q` (`ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`).

Both summands `range E = ker Q*(u)` and `ker E = range Q*(u)` inherit property (Pr), and the
restrictions of `u` to them are row compact. The projection `E` is itself row compact
(`ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`), so `range E = ker Q*(u)` is finitely
generated and projective of constant rank `deg Q` on `Spec R`
(`ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`). The Fredholm
series of `u * E` and of `u|_{range E}` equal `Q`—which is also the reversed characteristic
polynomial of `u|_{range E}`—and those of `u * (1 - E)` and `u|_{ker E}` equal `S`. In particular,
when `deg Q > 0`, the projection is nonzero and `Q*(u)` is not invertible. Over a complete
ultrametric field, `ker Q*(u)` has dimension `deg Q`.

## Main results

* `ContinuousLinearMap.IsPrCompact.exists_rieszColemanProjection`: existence of the Riesz–Coleman
  projection for a coprime polynomial factor of `H_u` on a module with property (Pr).
* `ContinuousLinearMap.IsRieszColemanProjection.isPrCompact`: Riesz–Coleman projections of
  row-compact operators are row compact.
* `ContinuousLinearMap.IsRieszColemanProjection.finite_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_range_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact`:
  `range E = ker Q*(u)` is finitely generated and projective.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.rankAtStalk_ker_aeval_reverse`: constant rank `deg Q` on
  `Spec R`.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_eq_coe`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_range_eq_coe`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_restrict_ker_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_eq`:
  factorisation of the Fredholm series across the Riesz–Coleman splitting.
* `ContinuousLinearMap.IsRieszColemanProjection.ne_zero_of_natDegree_pos`,
  `ContinuousLinearMap.IsPrCompact.not_isUnit_aeval_reverse_of_natDegree_pos`: non-degeneracy for
  positive-degree factors.
* `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_of_isPrCompact`,
  `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse`: dimension `deg Q` over a field.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm Polynomial PowerSeries

open PowerSeries (IsEntire)

namespace ContinuousLinearMap

section PrModule

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] {M : Type*} [SeminormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] {u E : M →L[R] M} {Q : R[X]}

/-- **Existence of the Riesz–Coleman projection on a module with property (Pr).** Let `u` be a
row-compact endomorphism of a module with property (Pr) whose Fredholm series factors as
`H_u = Q S`, where `Q(0) = 1`, `lc(Q)` is a unit, `S` is entire, and `Q` and `S` are coprime in
the ring of entire series. Then `u` has a Riesz–Coleman projection at `Q`. -/
theorem IsPrCompact.exists_rieszColemanProjection (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at hFac
  exact ⟨_, ((hu.isRowCompact_comp i r).isRieszColemanProjection_rieszColemanProjection
    hQ0 hQlc hS hFac hCop).comp_comp_of_retract hri⟩

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- The finite summand `range E` of a Riesz–Coleman projection on a module with property (Pr)
inherits property (Pr). -/
theorem IsRieszColemanProjection.hasPr_range (hE : IsRieszColemanProjection u Q E)
    (hM : TauCeti.HasPr R M) : TauCeti.HasPr R E.range :=
  hM.of_retract E.range.subtypeL E.rangeRestrict
    (ext fun x ↦ Subtype.ext (IsIdempotentElem.apply_coe_range hE.isIdempotentElem x))

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- The complementary summand `ker E` of a Riesz–Coleman projection on a module with property (Pr)
inherits property (Pr). -/
theorem IsRieszColemanProjection.hasPr_ker (hE : IsRieszColemanProjection u Q E)
    (hM : TauCeti.HasPr R M) : TauCeti.HasPr R E.ker := by
  let rK : M →L[R] E.ker :=
    (1 - E).codRestrict E.ker fun x ↦ by
      rw [LinearMap.mem_ker, coe_coe, sub_apply, one_apply_eq_self, map_sub,
        show E (E x) = E x from congr($(hE.isIdempotentElem.eq) x), sub_self]
  exact hM.of_retract E.ker.subtypeL rK
    (ext fun x ↦ Subtype.ext <| by
      simp only [comp_apply, id_apply, ContinuousLinearMap.coe_codRestrict_apply, rK, sub_apply,
        one_apply_eq_self, Submodule.coe_subtypeL, Submodule.coe_subtype,
        show E x = 0 from x.2, sub_zero])

omit [CompleteSpace R] in
/-- A Riesz–Coleman projection of a row-compact endomorphism of a module with property (Pr) is row
compact when `Q` has invertible leading coefficient. -/
theorem IsRieszColemanProjection.isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQlc : IsUnit Q.leadingCoeff) : E.IsPrCompact := by
  rw [hE.eq_neg_smul_mul_aeval_divX_mul hQlc, mul_def, mul_def]
  exact (((hu.comp_clm _ hu.hasPr_source).comp_clm E hu.hasPr_source).smul _).neg

omit [CompleteSpace R] in
/-- The restriction of a row-compact endomorphism `u` to the finite Riesz–Coleman summand
`range E` is row compact. -/
theorem IsRieszColemanProjection.isPrCompact_restrict_range (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) :
    (u.restrict (fun _ hx ↦ hE.mapsTo_range hx)).IsPrCompact := by
  have hR : TauCeti.HasPr R E.range := hE.hasPr_range hu.hasPr_source
  have heq : u.restrict (fun _ hx ↦ hE.mapsTo_range hx) =
      E.rangeRestrict.comp (u.comp E.range.subtypeL) := by
    ext x
    have hx : E x = x := IsIdempotentElem.apply_coe_range hE.isIdempotentElem x
    have hcomm : E (u x) = u (E x) := congr($(hE.commute.eq.symm) (x : M))
    simp [hcomm, hx]
  rw [heq]
  exact (hu.comp_clm E.range.subtypeL hR).clm_comp E.rangeRestrict hR

omit [CompleteSpace R] in
/-- The restriction of a row-compact endomorphism `u` to the complementary Riesz–Coleman summand
`ker E` is row compact. -/
theorem IsRieszColemanProjection.isPrCompact_restrict_ker (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) :
    (u.restrict (fun _ hx ↦ hE.mapsTo_ker hx)).IsPrCompact := by
  have hK : TauCeti.HasPr R E.ker := hE.hasPr_ker hu.hasPr_source
  let rK : M →L[R] E.ker :=
    (1 - E).codRestrict E.ker fun x ↦ by
      rw [LinearMap.mem_ker, coe_coe, sub_apply, one_apply_eq_self, map_sub,
        show E (E x) = E x from congr($(hE.isIdempotentElem.eq) x), sub_self]
  have heq : u.restrict (fun _ hx ↦ hE.mapsTo_ker hx) =
      rK.comp (u.comp E.ker.subtypeL) := by
    ext x
    have hcomm : E (u x) = u (E x) := congr($(hE.commute.eq.symm) (x : M))
    simp [rK, hcomm, show E x = 0 from x.2]
  rw [heq]
  exact (hu.comp_clm E.ker.subtypeL hK).clm_comp rK hK

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism of a module with
property (Pr) is finitely generated. -/
theorem IsRieszColemanProjection.finite_range_of_isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQlc : IsUnit Q.leadingCoeff) : Module.Finite R E.range :=
  (hE.isPrCompact hu hQlc).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The range of a Riesz–Coleman projection of a row-compact endomorphism of a module with
property (Pr) is projective over `R`. -/
theorem IsRieszColemanProjection.projective_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQlc : IsUnit Q.leadingCoeff) :
    Module.Projective R E.range :=
  (hE.isPrCompact hu hQlc).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- The kernel `ker Q*(u)` for a Riesz–Coleman projection of a row-compact endomorphism of a
module with property (Pr) is finitely generated. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQlc : IsUnit Q.leadingCoeff) :
    Module.Finite R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range_of_isPrCompact hu hQlc

/-- The kernel `ker Q*(u)` for a Riesz–Coleman projection of a row-compact endomorphism of a
module with property (Pr) is projective over `R`. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQlc : IsUnit Q.leadingCoeff) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range_of_isPrCompact hu hQlc

/-- **Constant rank of the Riesz–Coleman summand on a (Pr) module.** The range of a
Riesz–Coleman projection attached to a coprime factor `Q` of `H_u` has constant rank `deg Q` at
every prime ideal of `R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_of_isPrCompact
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hFac
  have hF := hv.isRieszColemanProjection_rieszColemanProjection hQ0 hQlc hS hFac hCop
  have hE_eq : E = r.comp ((i.comp (u.comp r)).rieszColemanProjection Q |>.comp i) :=
    hE.unique (hF.comp_comp_of_retract hri)
  have hFE : i.comp (E.comp r) = (i.comp (u.comp r)).rieszColemanProjection Q := by
    rw [hE_eq]
    exact hF.comp_comp_eq_of_retract hri hQlc
  have heq : E.range ≃ₗ[R] ((i.comp (u.comp r)).rieszColemanProjection Q).range :=
    (rangeEquivOfRetract E hri).trans (LinearEquiv.ofEq _ _ <| by
      simpa only [toLinearMap_comp] using
        congrArg (fun T : C₀(J, R) →L[R] C₀(J, R) ↦ T.range) hFE)
  have hrank : Module.rankAtStalk (R := R) E.range =
      Module.rankAtStalk (R := R) ((i.comp (u.comp r)).rieszColemanProjection Q).range := by
    let : AddCommGroup E.range := inferInstance
    let : AddCommGroup ((i.comp (u.comp r)).rieszColemanProjection Q).range := inferInstance
    exact Module.rankAtStalk_eq_of_equiv heq
  rw [hrank]
  exact hF.rankAtStalk_range hv hQ0 hQlc hS hFac hCop p

/-- For a coprime factorisation `H_u = Q S` of the Fredholm series of a row-compact endomorphism
`u` of a module with property (Pr), `ker Q*(u)` has constant rank `deg Q` at every prime ideal
of `R`. -/
theorem IsPrCompact.rankAtStalk_ker_aeval_reverse (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) p =
      Q.natDegree := by
  obtain ⟨E, hE⟩ := hu.exists_rieszColemanProjection hQ0 hQlc hS hFac hCop
  rw [← hE.range_eq_ker]
  exact hE.rankAtStalk_range_of_isPrCompact hu hQ0 hQlc hS hFac hCop p

/-- **Determinant of `u * E` on a (Pr) module.** The Fredholm series of `u * E` is `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_eq_coe (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1) (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧}
    (hS : S.IsEntire) (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).charPowerSeries = (Q : R⟦X⟧) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hFac
  have hF := hv.isRieszColemanProjection_rieszColemanProjection hQ0 hQlc hS hFac hCop
  have hFE : i.comp (E.comp r) = (i.comp (u.comp r)).rieszColemanProjection Q := by
    rw [hE.unique (hF.comp_comp_of_retract hri)]
    exact hF.comp_comp_eq_of_retract hri hQlc
  have hext : i.comp ((u * E).comp r) =
      i.comp (u.comp r) * (i.comp (u.comp r)).rieszColemanProjection Q := by
    ext y
    have hy : ((i.comp (u.comp r)).rieszColemanProjection Q) y = i (E (r y)) :=
      congr($hFE.symm y)
    simp [hy, hri']
  rw [mul_def, (hu.comp_clm E hu.hasPr_source).charPowerSeries_eq hri, ← mul_def, hext]
  exact hF.charPowerSeries_matrixCoeff_mul_eq_coe hv hQ0 hQlc hS hFac hCop

/-- **Determinant of `u * (1 - E)` on a (Pr) module.** The Fredholm series of `u * (1 - E)` is
`S`. -/
theorem IsRieszColemanProjection.charPowerSeries_mul_one_sub_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).charPowerSeries = S := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hFac
  have hF := hv.isRieszColemanProjection_rieszColemanProjection hQ0 hQlc hS hFac hCop
  have hFE : i.comp (E.comp r) = (i.comp (u.comp r)).rieszColemanProjection Q := by
    rw [hE.unique (hF.comp_comp_of_retract hri)]
    exact hF.comp_comp_eq_of_retract hri hQlc
  have hext : i.comp ((u * (1 - E)).comp r) =
      i.comp (u.comp r) * (1 - (i.comp (u.comp r)).rieszColemanProjection Q) := by
    ext y
    have hy : ((i.comp (u.comp r)).rieszColemanProjection Q) y = i (E (r y)) :=
      congr($hFE.symm y)
    simp [hy, hri', map_sub]
  rw [mul_def, (hu.comp_clm (1 - E) hu.hasPr_source).charPowerSeries_eq hri, ← mul_def, hext]
  exact hF.charPowerSeries_matrixCoeff_mul_one_sub_eq hv hQ0 hQlc hS hFac hCop

/-- **Determinant of the restriction to `range E`.** The Fredholm series of `u` restricted to
`range E` is `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_range_eq_coe
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict (fun _ hx ↦ hE.mapsTo_range hx)).charPowerSeries = (Q : R⟦X⟧) := by
  have hR : TauCeti.HasPr R E.range := hE.hasPr_range hu.hasPr_source
  have h1 : u.restrict (fun _ hx ↦ hE.mapsTo_range hx) =
      E.rangeRestrict.comp (u.comp E.range.subtypeL) := by
    ext x
    have hx : E x = x := IsIdempotentElem.apply_coe_range hE.isIdempotentElem x
    have hcomm : E (u x) = u (E x) := congr($(hE.commute.eq.symm) (x : M))
    simp [hcomm, hx]
  have h2 : (u.comp E.range.subtypeL).comp E.rangeRestrict = u * E := ext fun _ ↦ rfl
  rw [h1, ← (hu.comp_clm E.range.subtypeL hR).charPowerSeries_comp_comm E.rangeRestrict, h2]
  exact hE.charPowerSeries_mul_eq_coe hu hQ0 hQlc hS hFac hCop

/-- **Determinant of the restriction to `ker E`.** The Fredholm series of `u` restricted to
`ker E` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_restrict_ker_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.restrict (fun _ hx ↦ hE.mapsTo_ker hx)).charPowerSeries = S := by
  have hK : TauCeti.HasPr R E.ker := hE.hasPr_ker hu.hasPr_source
  let rK : M →L[R] E.ker :=
    (1 - E).codRestrict E.ker fun x ↦ by
      rw [LinearMap.mem_ker, coe_coe, sub_apply, one_apply_eq_self, map_sub,
        show E (E x) = E x from congr($(hE.isIdempotentElem.eq) x), sub_self]
  have h1 : u.restrict (fun _ hx ↦ hE.mapsTo_ker hx) =
      rK.comp (u.comp E.ker.subtypeL) := by
    ext x
    have hcomm : E (u x) = u (E x) := congr($(hE.commute.eq.symm) (x : M))
    simp [rK, hcomm, show E x = 0 from x.2]
  have h2 : (u.comp E.ker.subtypeL).comp rK = u * (1 - E) := ext fun _ ↦ rfl
  rw [h1, ← (hu.comp_clm E.ker.subtypeL hK).charPowerSeries_comp_comm rK, h2]
  exact hE.charPowerSeries_mul_one_sub_eq hu hQ0 hQlc hS hFac hCop

/-- **Reversed characteristic polynomial on `range E`.** On the finite projective summand `range E`,
the reversed characteristic polynomial `det (1 - X u)` of the restriction of `u` equals `Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    have := hE.finite_range_of_isPrCompact hu hQlc
    have := hE.projective_range_of_isPrCompact hu hQlc
    ((u.restrict (fun _ hx ↦ hE.mapsTo_range hx)).toLinearMap).projectiveCharpolyRev = Q := by
  classical
  let : AddCommGroup E.range := inferInstance
  have : Module.Finite R E.range := hE.finite_range_of_isPrCompact hu hQlc
  have : Module.Projective R E.range := hE.projective_range_of_isPrCompact hu hQlc
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  set v := i.comp (u.comp r)
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hFac
  set F := v.rieszColemanProjection Q
  have hF := hv.isRieszColemanProjection_rieszColemanProjection hQ0 hQlc hS hFac hCop
  have hFE : i.comp (E.comp r) = F := by
    rw [hE.unique (hF.comp_comp_of_retract hri)]
    exact hF.comp_comp_eq_of_retract hri hQlc
  let : AddCommGroup F.range := inferInstance
  have : Module.Finite R F.range := hF.finite_range hv hQlc
  have : Module.Projective R F.range := hF.projective_range hv hQlc
  let e : E.range ≃ₗ[R] F.range :=
    (rangeEquivOfRetract E hri).trans (LinearEquiv.ofEq _ _ <| by
      simpa only [toLinearMap_comp] using
        congrArg (fun T : C₀(J, R) →L[R] C₀(J, R) ↦ T.range) hFE)
  have he_apply (x : E.range) : (e x : C₀(J, R)) = i x :=
    coe_rangeEquivOfRetract_apply E hri x
  let f : Module.End R E.range := (u.restrict (fun _ hx ↦ hE.mapsTo_range hx)).toLinearMap
  let g : Module.End R F.range := (v.restrict (fun _ hx ↦ hF.mapsTo_range hx)).toLinearMap
  have hfg (x : E.range) : g (e x) = e (f x) := by
    apply Subtype.ext
    simp [g, f, v, he_apply, hri']
  have hpoly : g.projectiveCharpolyRev = f.projectiveCharpolyRev := by
    simpa only [Polynomial.map_id] using
      LinearMap.projectiveCharpolyRev_eq_map_of_comp_eq (θ := RingHom.id R) e hfg
  have hF_Pr : TauCeti.HasPr R F.range :=
    hF.hasPr_range (isPrCompact_iff_isRowCompact.2 hv).hasPr_source
  have hg_coe : (g.projectiveCharpolyRev : R⟦X⟧) = (Q : R⟦X⟧) := by
    rw [← charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := F.range) hF_Pr
      (v.restrict (fun _ hx ↦ hF.mapsTo_range hx))]
    exact hF.charPowerSeries_restrict_range_eq_coe (isPrCompact_iff_isRowCompact.2 hv)
      hQ0 hQlc hS (by rwa [hv.charPowerSeries_eq_charPowerSeries_matrixCoeff]) hCop
  exact hpoly.symm.trans (Polynomial.coe_injective R hg_coe)

/-- **Non-degeneracy for positive-degree factors.** If `Q` has positive degree, the Riesz–Coleman
projection attached to a coprime factorisation `H_u = Q S` is nonzero. -/
theorem IsRieszColemanProjection.ne_zero_of_natDegree_pos (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1) (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧}
    (hS : S.IsEntire) (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (hdeg : 0 < Q.natDegree) :
    E ≠ 0 := by
  intro h0
  have h1 : (Q : R⟦X⟧) = ((1 : R[X]) : R⟦X⟧) := by
    rw [← hE.charPowerSeries_mul_eq_coe hu hQ0 hQlc hS hFac hCop, h0, mul_zero,
      charPowerSeries_zero, Polynomial.coe_one]
  have hQ1 : Q = 1 := Polynomial.coe_injective R h1
  rw [hQ1, Polynomial.natDegree_one] at hdeg
  exact lt_irrefl 0 hdeg

/-- If `Q` is a coprime polynomial factor of positive degree with `Q(0) = 1` and invertible leading
coefficient, then `Q*(u)` is not invertible. -/
theorem IsPrCompact.not_isUnit_aeval_reverse_of_natDegree_pos (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQlc : IsUnit Q.leadingCoeff) {S : R⟦X⟧} (hS : S.IsEntire)
    (hFac : u.charPowerSeries = (Q : R⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (hdeg : 0 < Q.natDegree) :
    ¬ IsUnit (Polynomial.aeval u Q.reverse) := by
  obtain ⟨E, hE⟩ := hu.exists_rieszColemanProjection hQ0 hQlc hS hFac hCop
  exact fun hunit ↦ hE.ne_zero_of_natDegree_pos hu hQ0 hQlc hS hFac hCop hdeg
    (hE.eq_zero_of_isUnit_aeval_reverse hunit)

end PrModule

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [IsBoundedSMul K M] {u E : M →L[K] M} {Q : K[X]}

/-- Over a complete ultrametric field, the Riesz–Coleman summand `range E` of a row-compact
endomorphism of a module with property (Pr) has dimension `deg Q`. -/
theorem IsRieszColemanProjection.finrank_range_of_isPrCompact (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1) {S : K⟦X⟧} (hS : S.IsEntire)
    (hFac : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQne : Q ≠ 0 := fun h ↦ by simp [h] at hQ0
  have hQlc : IsUnit Q.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQne)
  have hr :=
    hE.rankAtStalk_range_of_isPrCompact hu hQ0 hQlc hS hFac hCop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- Over a complete ultrametric field, for a coprime factorisation `H_u = Q S` of a row-compact
endomorphism of a module with property (Pr), `ker Q*(u)` has dimension `deg Q`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse (hu : u.IsPrCompact) (hQ0 : Q.coeff 0 = 1)
    {S : K⟦X⟧} (hS : S.IsEntire) (hFac : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[K] M) : M →ₗ[K] M)) =
      Q.natDegree := by
  have hQne : Q ≠ 0 := fun h ↦ by simp [h] at hQ0
  have hQlc : IsUnit Q.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQne)
  obtain ⟨E, hE⟩ := hu.exists_rieszColemanProjection hQ0 hQlc hS hFac hCop
  rw [← hE.range_eq_ker]
  exact hE.finrank_range_of_isPrCompact hu hQ0 hS hFac hCop

end Field

end ContinuousLinearMap
