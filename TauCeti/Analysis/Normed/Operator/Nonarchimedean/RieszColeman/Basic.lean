/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Banach
import TauCeti.Algebra.Ring.SpectralIdempotent
import TauCeti.LinearAlgebra.End.Aeval
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman projections on seminormed modules

Let `R` be a normed commutative ring with Tate scalars, `M` a seminormed `R`-module with bounded
scalar action, `u` a continuous `R`-linear endomorphism of `M`, and `Q ∈ R[X]` a polynomial with
reversal `Q* = Q.reverse`.

A **Riesz–Coleman projection** of `u` at `Q` (`ContinuousLinearMap.IsRieszColemanProjection`) is
an idempotent `E`, commuting with `u` and lying in the operator-norm closure of `R[u]`, such that
`Q*(u) * E = 0` and `Q*(u)` is invertible on the complementary summand `range (1 - E)`, with
complementary inverse `w` again in the closure of `R[u]`. Thus `E` gives a closed stable splitting

`M = ker Q*(u) ⊕ range Q*(u)`

(`ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
`ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`), which is unique
(`ContinuousLinearMap.IsRieszColemanProjection.unique`) and functorial for linear intertwiners
(`ContinuousLinearMap.IsRieszColemanProjection.semiconj`), so every operator commuting with `u`
commutes with `E` and `w` and preserves both summands. When `Q` has invertible leading
coefficient, `u` is invertible on `range E`
(`ContinuousLinearMap.IsRieszColemanProjection.equivRange`). For `Q = 1` the projection is zero
(`ContinuousLinearMap.IsRieszColemanProjection.eq_zero_of_eq_one`).

Riesz–Coleman projections compress along continuous linear retracts `r ∘ i = id` of `M` through a
normed module `N` (`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`), and when
`Q` has invertible leading coefficient re-extending the compression recovers the ambient projector
(`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`). Existence, rank, and
Fredholm determinant factorisations on model spaces `C₀(I, R)` and modules with property `(Pr)`
are established in `RieszColeman.ModelSpace` and `RieszColeman.PrModule`.

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: the spectral projector of `u` attached to a
  polynomial factor `Q`.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse`: the inverse of `Q*(u)` on the
  complementary summand, extended by zero.
* `ContinuousLinearMap.IsRieszColemanProjection.equivKer`: `Q*(u)` as a continuous linear
  automorphism of the complementary summand `ker E`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: `u` as a continuous linear
  automorphism of `range E` when `Q` has invertible leading coefficient.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.range_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.range_aeval_reverse_eq_ker`,
  `ContinuousLinearMap.IsRieszColemanProjection.isTopCompl_ker_range`: the closed stable splitting
  `M = ker Q*(u) ⊕ range Q*(u)`.
* `ContinuousLinearMap.IsRieszColemanProjection.unique`: uniqueness of the Riesz–Coleman
  projection.
* `ContinuousLinearMap.IsRieszColemanProjection.semiconj`,
  `ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`: functoriality under linear
  intertwiners and commuting operators.
* `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`,
  `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`: compression and
  re-extension along continuous linear retracts.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open scoped Polynomial TauCeti.RingOpNorm

namespace ContinuousLinearMap

/-- A linear intertwiner between `u` and `v` intertwines `P(u)` and `P(v)` for every polynomial
`P`. -/
private theorem semiconj_aeval {R M N : Type*} [CommSemiring R]
    [TopologicalSpace M] [AddCommGroup M] [Module R M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [TopologicalSpace N] [AddCommGroup N] [Module R N]
    [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
    {u : M →L[R] M} {v : N →L[R] N} (f : M →ₗ[R] N) (hf : Function.Semiconj f u v)
    (P : R[X]) (x : M) : f ((Polynomial.aeval u P) x) = (Polynomial.aeval v P) (f x) := by
  have hf_comp : v.toLinearMap ∘ₗ f = f ∘ₗ u.toLinearMap :=
    LinearMap.ext fun y ↦ (hf y).symm
  have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hf_comp P) x
  simpa only [LinearMap.comp_apply, ← toLinearMap_aeval, coe_coe] using h.symm

section Projection

variable {R : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]

section Module

variable {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **Riesz–Coleman projection** of an endomorphism `u` of a seminormed `R`-module `M` attached
to a polynomial `Q : R[X]`: an idempotent `E`, commuting with `u` and lying in the operator-norm
closure of the polynomials in `u`, such that `Q*(u) * E = 0` (for the reversal `Q* = Q.reverse`)
and `Q*(u)` is invertible on the complementary summand `range (1 - E)`, with inverse again in the
closure of the polynomials in `u`. For a coprime polynomial factor `Q` of the Fredholm series of a
row-compact `u`, `range E = ker Q*(u)` is the finite projective summand of determinant `Q`, and
`ker E = range Q*(u)` is its closed stable complement. -/
structure IsRieszColemanProjection (u : M →L[R] M) (Q : R[X]) (E : M →L[R] M) : Prop where
  /-- A Riesz–Coleman projection is idempotent. -/
  isIdempotentElem : IsIdempotentElem E
  /-- A Riesz–Coleman projection commutes with the operator. -/
  commute : Commute u E
  /-- A Riesz–Coleman projection is an operator-norm limit of polynomials in the operator. -/
  mem_closure_adjoin : E ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))
  /-- The reversed polynomial `Q*(u)` vanishes on the range of a Riesz–Coleman projection. -/
  aeval_reverse_mul_eq_zero : Polynomial.aeval u Q.reverse * E = 0
  /-- `Q*(u)` is invertible on the complementary summand, with inverse an operator-norm limit of
  polynomials in the operator. -/
  exists_inverse : ∃ w : M →L[R] M, Polynomial.aeval u Q.reverse * w = 1 - E ∧
    w * Polynomial.aeval u Q.reverse = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧
    w ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M))

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- A Riesz–Coleman projection commutes with every polynomial in `u`. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Commute (Polynomial.aeval u P) E :=
  ContinuousLinearMap.ext fun x ↦
    (semiconj_aeval E.toLinearMap (fun y ↦ congr($(hE.commute.eq.symm) y)) P x).symm

/-- A Riesz–Coleman projection commutes with `Q*(u)`. -/
theorem commute_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    Commute (Polynomial.aeval u Q.reverse) E :=
  hE.commute_aeval Q.reverse

/-- If `Q*(u)` is already invertible on `M`, the Riesz–Coleman projection at `Q` is zero. -/
theorem eq_zero_of_isUnit_aeval_reverse (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit (Polynomial.aeval u Q.reverse)) : E = 0 :=
  hQ.mul_right_eq_zero.mp hE.aeval_reverse_mul_eq_zero

/-- For a constant polynomial with invertible value, the Riesz–Coleman projection is zero. -/
theorem eq_zero_of_natDegree_zero (hE : IsRieszColemanProjection u Q E)
    (hdeg : Q.natDegree = 0) (hQlc : IsUnit Q.leadingCoeff) : E = 0 := by
  have hQ : Q = Polynomial.C Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hdeg]
    exact Polynomial.eq_C_of_natDegree_eq_zero hdeg
  apply hE.eq_zero_of_isUnit_aeval_reverse
  rw [hQ, Polynomial.reverse_C, Polynomial.aeval_C]
  exact hQlc.map (algebraMap R (M →L[R] M))

/-- For `Q = 1`, the Riesz–Coleman projection is zero. -/
theorem eq_zero_of_eq_one (hE : IsRieszColemanProjection u 1 E) : E = 0 :=
  hE.eq_zero_of_natDegree_zero Polynomial.natDegree_one (by simp)

/-- The operator preserves the kernel of its Riesz–Coleman projection. -/
theorem mapsTo_ker (hE : IsRieszColemanProjection u Q E) : Set.MapsTo u E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($(hE.commute.eq.symm) x)

/-- The operator preserves the range of its Riesz–Coleman projection. -/
theorem mapsTo_range (hE : IsRieszColemanProjection u Q E) : Set.MapsTo u E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($(hE.commute.eq.symm) x)

/-- Every polynomial in `u` preserves the kernel of a Riesz–Coleman projection. -/
theorem mapsTo_ker_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P) E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($((hE.commute_aeval P).eq.symm) x)

/-- Every polynomial in `u` preserves the range of a Riesz–Coleman projection. -/
theorem mapsTo_range_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P) E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($((hE.commute_aeval P).eq.symm) x)

/-- The **complementary inverse** of a Riesz–Coleman projection: the inverse of `Q*(u)` on the
complementary summand `range (1 - E)`, extended by zero on `range E`, chosen from
`IsRieszColemanProjection.exists_inverse`. -/
noncomputable def inverse (hE : IsRieszColemanProjection u Q E) : M →L[R] M :=
  hE.exists_inverse.choose

/-- The complementary inverse is a right inverse of `Q*(u)` up to `1 - E`. -/
theorem aeval_reverse_mul_inverse (hE : IsRieszColemanProjection u Q E) :
    Polynomial.aeval u Q.reverse * hE.inverse = 1 - E := by
  obtain ⟨hw, -, -, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is a left inverse of `Q*(u)` up to `1 - E`. -/
theorem inverse_mul_aeval_reverse (hE : IsRieszColemanProjection u Q E) :
    hE.inverse * Polynomial.aeval u Q.reverse = 1 - E := by
  obtain ⟨-, hw, -, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse takes values in the kernel of the Riesz–Coleman projection. -/
@[simp]
theorem mul_inverse_eq_zero (hE : IsRieszColemanProjection u Q E) : E * hE.inverse = 0 := by
  obtain ⟨-, -, hw, -, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse vanishes on the range of the Riesz–Coleman projection. -/
@[simp]
theorem inverse_mul_eq_zero (hE : IsRieszColemanProjection u Q E) : hE.inverse * E = 0 := by
  obtain ⟨-, -, -, hw, -⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is an operator-norm limit of polynomials in the operator. -/
theorem inverse_mem_closure_adjoin (hE : IsRieszColemanProjection u Q E) :
    hE.inverse ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
  obtain ⟨-, -, -, -, hw⟩ := hE.exists_inverse.choose_spec
  exact hw

/-- The complementary inverse is the unique right inverse of `Q*(u)` up to `1 - E` taking values
in the kernel of `E`. -/
theorem eq_inverse (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Polynomial.aeval u Q.reverse * w = 1 - E) (hEw : E * w = 0) : w = hE.inverse := by
  calc w = (1 - E) * w := by
        rw [sub_mul (α := M →L[R] M), one_mul, hEw, sub_zero w]
    _ = hE.inverse * (Polynomial.aeval u Q.reverse * w) := by
        rw [← mul_assoc, hE.inverse_mul_aeval_reverse]
    _ = hE.inverse := by
        rw [hw, mul_sub (α := M →L[R] M), mul_one, hE.inverse_mul_eq_zero, sub_zero hE.inverse]

/-- The complementary inverse preserves the kernel of the Riesz–Coleman projection. -/
theorem mapsTo_ker_inverse (hE : IsRieszColemanProjection u Q E) :
    Set.MapsTo hE.inverse E.ker E.ker := by
  intro x _
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, zero_apply] using
    congr($(hE.mul_inverse_eq_zero) x)

/-- On the complementary summand, the complementary inverse is a left inverse of `Q*(u)`. -/
theorem inverse_aeval_reverse_apply (hE : IsRieszColemanProjection u Q E) {x : M}
    (hx : x ∈ E.ker) : hE.inverse ((Polynomial.aeval u Q.reverse) x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.inverse_mul_aeval_reverse) x)

/-- On the complementary summand, the complementary inverse is a right inverse of `Q*(u)`. -/
theorem aeval_reverse_apply_inverse (hE : IsRieszColemanProjection u Q E) {x : M}
    (hx : x ∈ E.ker) : (Polynomial.aeval u Q.reverse) (hE.inverse x) = x := by
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, hx', sub_zero] using
    congr($(hE.aeval_reverse_mul_inverse) x)

/-- **The range of a Riesz–Coleman projection is `ker Q*(u)`.** -/
theorem range_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range (E : M →ₗ[R] M) =
      LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa only [mul_apply_eq_comp, zero_apply] using congr($(hE.aeval_reverse_mul_eq_zero) y)
  · have h := congr($(hE.inverse_mul_aeval_reverse) x)
    simp only [mul_apply_eq_comp, hx, map_zero, sub_apply, one_apply_eq_self] at h
    exact (sub_eq_zero.mp h.symm).symm

/-- **The range of `Q*(u)` is the complementary summand `ker E`.** -/
theorem range_aeval_reverse_eq_ker (hE : IsRieszColemanProjection u Q E) :
    LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) =
      LinearMap.ker (E : M →ₗ[R] M) := by
  have hzero : E * Polynomial.aeval u Q.reverse = 0 :=
    hE.commute_aeval_reverse.eq.symm.trans hE.aeval_reverse_mul_eq_zero
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  refine ⟨?_, fun hx ↦ ⟨hE.inverse x, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    simpa only [mul_apply_eq_comp, zero_apply] using congr($hzero y)
  · exact hE.aeval_reverse_apply_inverse (LinearMap.mem_ker.mpr hx)

/-- **Closed stable splitting `M = ker Q*(u) ⊕ range Q*(u)`.** The kernel and range of `Q*(u)`
are topological complements. -/
theorem isTopCompl_ker_range (hE : IsRieszColemanProjection u Q E) :
    (LinearMap.ker ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)).IsTopCompl
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← hE.range_eq_ker, hE.range_aeval_reverse_eq_ker]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hE.isIdempotentElem

/-- The complementary summand `range Q*(u)` is closed, even in infinite dimensions. -/
theorem isClosed_range_aeval_reverse [T1Space M] (hE : IsRieszColemanProjection u Q E) :
    IsClosed
      (LinearMap.range ((Polynomial.aeval u Q.reverse : M →L[R] M) : M →ₗ[R] M) : Set M) := by
  rw [hE.range_aeval_reverse_eq_ker]
  exact E.isClosed_ker

/-- `Q*(u)` as a continuous linear automorphism of the complementary summand `ker E`
(identified with `range Q*(u)` by `IsRieszColemanProjection.range_aeval_reverse_eq_ker`). Its
inverse is the restriction of `IsRieszColemanProjection.inverse`. -/
noncomputable def equivKer (hE : IsRieszColemanProjection u Q E) : E.ker ≃L[R] E.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((Polynomial.aeval u Q.reverse).restrict (fun _ hx ↦ hE.mapsTo_ker_aeval Q.reverse hx))
    (hE.inverse.restrict (fun _ hx ↦ hE.mapsTo_ker_inverse hx))
    (fun x ↦ Subtype.ext (hE.inverse_aeval_reverse_apply x.property))
    (fun x ↦ Subtype.ext (hE.aeval_reverse_apply_inverse x.property))

/-- The complementary automorphism acts by `Q*(u)`. -/
@[simp]
theorem coe_equivKer_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer x : M) = Polynomial.aeval u Q.reverse x :=
  (rfl)

/-- The inverse complementary automorphism acts by `IsRieszColemanProjection.inverse`. -/
@[simp]
theorem coe_equivKer_symm_apply (hE : IsRieszColemanProjection u Q E) (x : E.ker) :
    (hE.equivKer.symm x : M) = hE.inverse x :=
  (rfl)

/-- **Invertibility of `u` on `range E`.** When `Q` has invertible leading coefficient, `u`
restricts to a continuous linear automorphism of `range E`, with inverse the restriction of
`-lc(Q)⁻¹ • (Q*.divX)(u)`. -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E) (hQlc : IsUnit Q.leadingCoeff) :
    E.range ≃L[R] E.range := by
  let c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQlc
  let g : M →L[R] M := -(c • Polynomial.aeval u Q.reverse.divX)
  have hg_maps : Set.MapsTo g E.range E.range := fun x hx ↦
    E.range.neg_mem (E.range.smul_mem c (hE.mapsTo_range_aeval Q.reverse.divX hx))
  have hmul : u * Polynomial.aeval u Q.reverse.divX + Q.leadingCoeff • 1 =
      Polynomial.aeval u Q.reverse := by
    have h := congrArg (Polynomial.aeval u) (Polynomial.X_mul_divX_add Q.reverse)
    simpa [Polynomial.coeff_zero_reverse, Algebra.algebraMap_eq_smul_one] using h
  have hmul' : Polynomial.aeval u Q.reverse.divX * u + Q.leadingCoeff • 1 =
      Polynomial.aeval u Q.reverse := by
    have h := congrArg (Polynomial.aeval u) (Polynomial.divX_mul_X_add Q.reverse)
    simpa [Polynomial.coeff_zero_reverse, Algebra.algebraMap_eq_smul_one] using h
  have hkill (x : E.range) : (Polynomial.aeval u Q.reverse) x = 0 := by
    have hfix : E x = x :=
      ContinuousLinearMap.IsIdempotentElem.apply_coe_range hE.isIdempotentElem x
    simpa only [mul_apply_eq_comp, hfix, zero_apply] using congr($(hE.aeval_reverse_mul_eq_zero) x)
  refine ContinuousLinearEquiv.equivOfInverse
    (u.restrict fun _ hx ↦ hE.mapsTo_range hx)
    (g.restrict fun _ hx ↦ hg_maps hx) (fun x ↦ Subtype.ext ?_) (fun x ↦ Subtype.ext ?_)
  · have hx := congr($hmul' (x : M))
    simp only [add_apply, mul_apply_eq_comp, smul_apply, one_apply_eq_self, hkill x] at hx
    have hneg : (Polynomial.aeval u Q.reverse.divX) (u x) = -(Q.leadingCoeff • (x : M)) :=
      eq_neg_of_add_eq_zero_left hx
    simp only [restrict_apply, g, neg_apply, smul_apply, hneg, smul_neg, neg_neg,
      smul_smul, hc, one_smul]
  · have hx := congr($hmul (x : M))
    simp only [add_apply, mul_apply_eq_comp, smul_apply, one_apply_eq_self, hkill x] at hx
    have hneg : u ((Polynomial.aeval u Q.reverse.divX) x) = -(Q.leadingCoeff • (x : M)) :=
      eq_neg_of_add_eq_zero_left hx
    simp only [restrict_apply, g, neg_apply, smul_apply, map_neg, map_smul, hneg,
      smul_neg, neg_neg, smul_smul, hc, one_smul]

/-- On `range E`, the automorphism `equivRange` acts by `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQlc : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQlc x : M) = u x :=
  (rfl)

/-- On `range E`, the inverse automorphism acts by `-lc(Q)⁻¹ • (Q*.divX)(u)`. -/
@[simp]
theorem coe_equivRange_symm_apply (hE : IsRieszColemanProjection u Q E)
    (hQlc : IsUnit Q.leadingCoeff) (x : E.range) :
    ((hE.equivRange hQlc).symm x : M) =
      -(Ring.inverse Q.leadingCoeff • (Polynomial.aeval u Q.reverse.divX) x) :=
  (rfl)

/-- When `Q` has invertible leading coefficient, a Riesz–Coleman projection factors through `u` as
`E = -(lc(Q)⁻¹ • (u * (Q*.divX)(u) * E))`. -/
theorem eq_neg_smul_mul_aeval_divX_mul (hE : IsRieszColemanProjection u Q E)
    (hQlc : IsUnit Q.leadingCoeff) :
    E = -(Ring.inverse Q.leadingCoeff • (u * Polynomial.aeval u Q.reverse.divX * E)) := by
  have hc : Ring.inverse Q.leadingCoeff * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQlc
  have hmul : u * Polynomial.aeval u Q.reverse.divX + Q.leadingCoeff • 1 =
      Polynomial.aeval u Q.reverse := by
    have h := congrArg (Polynomial.aeval u) (Polynomial.X_mul_divX_add Q.reverse)
    simpa [Polynomial.coeff_zero_reverse, Algebra.algebraMap_eq_smul_one] using h
  ext x
  have hkill : (Polynomial.aeval u Q.reverse) (E x) = 0 :=
    congr($(hE.aeval_reverse_mul_eq_zero) x)
  have hx := congr($hmul (E x))
  simp only [add_apply, mul_apply_eq_comp, smul_apply, one_apply_eq_self, hkill] at hx
  have h2 : Q.leadingCoeff • E x = -(u ((Polynomial.aeval u Q.reverse.divX) (E x))) :=
    eq_neg_of_add_eq_zero_right hx
  calc E x = (Ring.inverse Q.leadingCoeff * Q.leadingCoeff) • E x := by rw [hc, one_smul]
    _ = Ring.inverse Q.leadingCoeff • (Q.leadingCoeff • E x) := by rw [mul_smul]
    _ = -(Ring.inverse Q.leadingCoeff • u ((Polynomial.aeval u Q.reverse.divX) (E x))) := by
        rw [h2, smul_neg]

/-- When `Q` has invertible leading coefficient, the restriction of `u` to `range E` is an
invertible continuous linear endomorphism. -/
theorem isUnit_restrict_range (hE : IsRieszColemanProjection u Q E)
    (hQlc : IsUnit Q.leadingCoeff) :
    IsUnit (u.restrict (fun _ hx ↦ hE.mapsTo_range hx)) := by
  let e := hE.equivRange hQlc
  refine ⟨⟨e.toContinuousLinearMap, e.symm.toContinuousLinearMap, ?_, ?_⟩, rfl⟩
  · ext x; exact congrArg Subtype.val (e.apply_symm_apply x)
  · ext x; exact congrArg Subtype.val (e.symm_apply_apply x)

/-- When `Q` has invertible leading coefficient, the restriction of `u` to `range E` is an
invertible linear endomorphism. -/
theorem isUnit_toLinearMap_restrict_range (hE : IsRieszColemanProjection u Q E)
    (hQlc : IsUnit Q.leadingCoeff) :
    IsUnit ((u.restrict (fun _ hx ↦ hE.mapsTo_range hx)).toLinearMap) :=
  (hE.isUnit_restrict_range hQlc).map toLinearMapRingHom

/-- **Uniqueness of the Riesz–Coleman projection.** Two Riesz–Coleman projections of `u` at the
same polynomial `Q` are equal. -/
theorem unique {E' : M →L[R] M} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection u Q E') : E = E' := by
  obtain ⟨w, hw, hw', -⟩ := hE.exists_inverse
  obtain ⟨w', hw₂, hw₂', -⟩ := hE'.exists_inverse
  exact hE.isIdempotentElem.eq_of_pow_mul_eq_zero (h := 1) hE'.isIdempotentElem
    (by simpa using hE.aeval_reverse_mul_eq_zero)
    (by simpa using hE'.aeval_reverse_mul_eq_zero) hw hw' hw₂ hw₂'

section Intertwining

variable {N : Type*} [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {v F : N →L[R] N}

/-- **Functoriality under linear intertwiners.** A linear map intertwining `u` and `v` intertwines
their Riesz–Coleman projections at the same polynomial `Q`. Continuity of `f` is not needed. -/
theorem semiconj (hE : IsRieszColemanProjection u Q E) (hF : IsRieszColemanProjection v Q F)
    (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) : Function.Semiconj f E F := by
  have hf_rev := semiconj_aeval f hf Q.reverse
  intro x
  have hfixed : F (f (E x)) = f (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hF.isIdempotentElem)).mp
    rw [hF.range_eq_ker]
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe, ← hf_rev]
    have hz := congr($(hE.aeval_reverse_mul_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  have hzero : F (f (x - E x)) = 0 := by
    have hx : x - E x ∈ E.ker := by
      apply LinearMap.mem_ker.mpr
      have hid := congr($(hE.isIdempotentElem.eq) x)
      simpa only [coe_coe, map_sub, mul_apply_eq_comp, sub_eq_zero] using hid.symm
    rw [← hE.range_aeval_reverse_eq_ker] at hx
    obtain ⟨y, hy⟩ := hx
    simp only [coe_coe] at hy
    have hy' : f (x - E x) = (Polynomial.aeval v Q.reverse) (f y) := by
      rw [← hy, hf_rev]
    apply LinearMap.mem_ker.mp
    rw [← hF.range_aeval_reverse_eq_ker]
    exact ⟨f y, hy'.symm⟩
  rw [map_sub, map_sub, hfixed, sub_eq_zero] at hzero
  exact hzero.symm

/-- An intertwiner sends the finite Riesz–Coleman summand into the corresponding summand. -/
theorem mapsTo_range_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.range F.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (hE.semiconj hF f hf x).symm⟩

/-- An intertwiner sends the complementary Riesz–Coleman summand into the corresponding
summand. -/
theorem mapsTo_ker_of_semiconj (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Set.MapsTo f E.ker F.ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  simp only [coe_coe]
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  rw [← hE.semiconj hF f hf, hx', map_zero]

/-- Intertwiners carry the complementary inverses of Riesz–Coleman projections to one another. -/
theorem semiconj_inverse (hE : IsRieszColemanProjection u Q E)
    (hF : IsRieszColemanProjection v Q F) (f : M →ₗ[R] N) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hf_rev := semiconj_aeval f hf Q.reverse
  have hEF := hE.semiconj hF f hf
  intro x
  have hker : f (hE.inverse x) ∈ F.ker := by
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hEF]
    have hz := congr($(hE.mul_inverse_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  calc f (hE.inverse x) = hF.inverse ((Polynomial.aeval v Q.reverse) (f (hE.inverse x))) :=
        (hF.inverse_aeval_reverse_apply hker).symm
    _ = hF.inverse (f ((Polynomial.aeval u Q.reverse) (hE.inverse x))) := by
        rw [hf_rev]
    _ = hF.inverse (f (x - E x)) := by
        have hz := congr($(hE.aeval_reverse_mul_inverse) x)
        exact congrArg (fun y ↦ hF.inverse (f y)) hz
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- A bounded operator commuting with `u` commutes with every Riesz–Coleman projection of `u`. -/
theorem commute_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w E :=
  ContinuousLinearMap.ext fun x ↦ hE.semiconj hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

/-- A bounded operator commuting with `u` commutes with the complementary inverse of any
Riesz–Coleman projection of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E) {w : M →L[R] M}
    (hw : Commute w u) : Commute w hE.inverse :=
  ContinuousLinearMap.ext fun x ↦
    hE.semiconj_inverse hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

end Intertwining

end IsRieszColemanProjection

end Module

section Retract

variable {M N : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] {i : M →L[R] N} {r : N →L[R] M}
  {u : M →L[R] M}

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M`
as a retract of a normed module `N`. If `E` is a Riesz–Coleman projection of the extension
`i ∘ u ∘ r` at `Q`, then `r ∘ E ∘ i` is a Riesz–Coleman projection of `u` at `Q`. -/
theorem IsRieszColemanProjection.comp_comp_of_retract (hri : r.comp i = .id R M) {Q : R[X]}
    {E : N →L[R] N} (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hrP (y : N) : r ((Polynomial.aeval (i.comp (u.comp r)) Q.reverse) y) =
      (Polynomial.aeval u Q.reverse) (r y) :=
    semiconj_aeval (u := i.comp (u.comp r)) (v := u) r.toLinearMap (fun z ↦ by simp [hri'])
      Q.reverse y
  have hiP (x : M) : i ((Polynomial.aeval u Q.reverse) x) =
      (Polynomial.aeval (i.comp (u.comp r)) Q.reverse) (i x) :=
    semiconj_aeval (u := u) (v := i.comp (u.comp r)) i.toLinearMap (fun z ↦ by simp [hri'])
      Q.reverse x
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have hE' := apply_comp_apply_of_mem_closure_adjoin hri hE.mem_closure_adjoin
  have hw' := apply_comp_apply_of_mem_closure_adjoin hri hw
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hkill (y : N) : (Polynomial.aeval (i.comp (u.comp r)) Q.reverse) (E y) = 0 :=
    congr($hE.aeval_reverse_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (w.comp i), ?_, ?_, ?_, ?_, comp_comp_mem_closure_adjoin hri hw⟩⟩
  · ext x
    simp [hE', hri', hEE]
  · ext x
    simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x
    simp [← hrP, hkill]
  · ext x
    simpa [← hrP, hri'] using congr(r $(DFunLike.congr_fun hw₁ (i x)))
  · ext x
    simpa [hiP, hri'] using congr(r $(DFunLike.congr_fun hw₂ (i x)))
  · ext x
    simpa [hw', hri'] using congr(r $(DFunLike.congr_fun hw₃ (i x)))
  · ext x
    simpa [hE', hri'] using congr(r $(DFunLike.congr_fun hw₄ (i x)))

omit [IsBoundedSMul R M] in
/-- **Extension recovers the ambient Riesz–Coleman projection.** When `Q` has invertible leading
coefficient and `E` is a Riesz–Coleman projection of `i ∘ u ∘ r`, `E` already takes values in
`range i`, so re-extending its compression `r ∘ E ∘ i` recovers `E`. -/
theorem IsRieszColemanProjection.comp_comp_eq_of_retract (hri : r.comp i = .id R M) {Q : R[X]}
    (hQlc : IsUnit Q.leadingCoeff) {E : N →L[R] N}
    (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    i.comp ((r.comp (E.comp i)).comp r) = E := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hE' := apply_comp_apply_of_mem_closure_adjoin hri hE.mem_closure_adjoin
  have hirE (y : N) : i (r (E y)) = E y := by
    have hEy := congr($(hE.eq_neg_smul_mul_aeval_divX_mul hQlc) y)
    rw [hEy]
    simp [hri']
  ext y
  simp only [comp_apply]
  rw [hE', hri', ← hE', hirE]

end Retract

end Projection

end ContinuousLinearMap
