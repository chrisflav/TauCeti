/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.ModelSpace
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Coefficientwise base change of Riesz–Coleman decompositions

Let `f : R →+* S` be a bounded unital homomorphism of normed commutative rings with Tate source
and complete ultrametric Tate target, and let `u_S = u.mapCoeffs f hf` be the coefficientwise
extension of an endomorphism `u` of a model space `C₀(I, R)`. For any polynomial `Q ∈ R[X]` with
invertible leading coefficient, the reversal of `Q.map f` is `Q.reverse.map f` and coefficientwise
extension commutes with polynomial evaluation, so Riesz–Coleman projections push forward to
Riesz–Coleman projections without any compactness assumption
(`ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`).

When `R` is also complete and ultrametric and `u` is row compact with a coprime polynomial
factorisation `H_u = Q S₀` (`Q(0) = 1`, `lc(Q)` a unit, `S₀` entire), bounded base change carries
this to a coprime factorisation `H_(u_S) = (Q.map f) (PowerSeries.map f S₀)` over `S`, so the
explicit Riesz–Coleman projector commutes with coefficient extension
(`ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs`). Over complete ultrametric
fields, the dimension of `ker Q*(u)` is invariant under bounded field extension
(`ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`).

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`: coefficientwise extension preserves
  Riesz–Coleman projections (without compactness).
* `ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs`: the explicit Riesz–Coleman
  projector commutes with bounded coefficient extension.
* `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`: bounded field extension
  preserves `dim ker Q*(u)`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm Polynomial PowerSeries

open PowerSeries (IsEntire)

namespace ContinuousLinearMap

section Helpers

/-- When `Q` has invertible leading coefficient and the target ring is nontrivial, reversal
commutes with coefficient mapping. -/
private theorem reverse_map_of_isUnit_leadingCoeff {R S : Type*} [CommRing R] [CommRing S]
    [Nontrivial S] {Q : R[X]} (hQlc : IsUnit Q.leadingCoeff) (f : R →+* S) :
    (Q.map f).reverse = Q.reverse.map f := by
  rw [Polynomial.reverse, Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (hQlc.map f).ne_zero,
    Polynomial.reflect_map, Polynomial.reverse]

/-- Bounded coefficient homomorphisms preserve coprimality in the subring of entire series. -/
private theorem isCoprime_map_entire {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    {Q : R[X]} {S₀ : R⟦X⟧} (hS₀ : S₀.IsEntire) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S₀, IsEntire.mem_subring.mpr hS₀⟩) :
    IsCoprime
      (⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :
        IsEntire.subring S)
      ⟨PowerSeries.map f S₀, IsEntire.mem_subring.mpr (by
        obtain ⟨C, hC⟩ := hf
        exact hS₀.map f hC)⟩ := by
  obtain ⟨C, hC⟩ := hf
  let φ : IsEntire.subring R →+* IsEntire.subring S :=
    { toFun g := ⟨PowerSeries.map f g.1,
        IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp g.2).map f hC)⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' g₁ g₂ := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' g₁ g₂ := Subtype.ext (map_add _ _ _) }
  have h := hCop.map φ
  have hQ : φ ⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ =
      ⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :=
    Subtype.ext Polynomial.polynomial_map_coe.symm
  rwa [hQ] at h

end Helpers

section Ring

variable {I R S : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- Coefficientwise extension commutes with polynomial evaluation. -/
private theorem mapCoeffs_aeval (u : C₀(I, R) →L[R] C₀(I, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (P : R[X]) :
    (Polynomial.aeval u P).mapCoeffs f hf = Polynomial.aeval (u.mapCoeffs f hf) (P.map f) := by
  induction P using Polynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ => simp [map_add, h₁, h₂]
  | monomial n a =>
    simp [Polynomial.map_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one]

variable [TauCeti.NormedRing.IsTate S]

/-- **Riesz–Coleman projections under bounded base change.** If `Q` has invertible leading
coefficient, the coefficientwise extension of a Riesz–Coleman projection of `u` at `Q` is a
Riesz–Coleman projection of `u.mapCoeffs f hf` at `Q.map f`. No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQlc : IsUnit Q.leadingCoeff) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  have := NormOneClass.nontrivial (G := S)
  have hrev : (Q.map f).reverse = Q.reverse.map f := reverse_map_of_isUnit_leadingCoeff hQlc f
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨?_, ?_, mapCoeffs_mem_closure_adjoin f hf hE.mem_closure_adjoin, ?_,
    ⟨w.mapCoeffs f hf, ?_, ?_, ?_, ?_, mapCoeffs_mem_closure_adjoin f hf hw⟩⟩
  · simpa [IsIdempotentElem] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.isIdempotentElem.eq
  · simpa [Commute, SemiconjBy] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.commute.eq
  · simpa [hrev, mapCoeffs_aeval] using
      congrArg (fun v ↦ v.mapCoeffs f hf) hE.aeval_reverse_mul_eq_zero
  · simpa [hrev, mapCoeffs_aeval] using congrArg (fun v ↦ v.mapCoeffs f hf) hw₁
  · simpa [hrev, mapCoeffs_aeval] using congrArg (fun v ↦ v.mapCoeffs f hf) hw₂
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₃
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₄

/-- **Bounded base change of the Riesz–Coleman projector.** For a row-compact endomorphism `u` of
`C₀(I, R)` and a coprime polynomial factorisation `H_u = Q S₀` with `Q(0) = 1`, `lc(Q)` a unit,
and `S₀` entire, the Riesz–Coleman projector of the coefficientwise extension `u.mapCoeffs f hf`
at `Q.map f` is the coefficientwise extension of the Riesz–Coleman projector of `u` at `Q`. -/
theorem IsRowCompact.rieszColemanProjection_mapCoeffs [IsUltrametricDist R] [CompleteSpace R]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) {Q : R[X]} (hQ0 : Q.coeff 0 = 1)
    (hQlc : IsUnit Q.leadingCoeff) {S₀ : R⟦X⟧} (hS₀ : S₀.IsEntire)
    (hFac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S₀)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S₀, IsEntire.mem_subring.mpr hS₀⟩) :
    (u.mapCoeffs f hf).rieszColemanProjection (Q.map f) =
      (u.rieszColemanProjection Q).mapCoeffs f hf := by
  have := NormOneClass.nontrivial (G := S)
  obtain ⟨C, hC⟩ := hf
  have hQ0' : (Q.map f).coeff 0 = 1 := by simp [hQ0]
  have hQlc' : IsUnit (Q.map f).leadingCoeff := by
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero f (hQlc.map f).ne_zero]
    exact hQlc.map f
  have hS₀' : (PowerSeries.map f S₀).IsEntire := hS₀.map f hC
  have hFac' : (u.mapCoeffs f ⟨C, hC⟩).matrixCoeff.charPowerSeries =
      ((Q.map f : S[X]) : S⟦X⟧) * PowerSeries.map f S₀ := by
    rw [hu.charPowerSeries_map f ⟨C, hC⟩, hFac, map_mul, Polynomial.polynomial_map_coe]
  have hCop' := isCoprime_map_entire hS₀ f ⟨C, hC⟩ hCop
  have h1 := (hu.mapCoeffs f ⟨C, hC⟩).isRieszColemanProjection_rieszColemanProjection
    hQ0' hQlc' hS₀' hFac' hCop'
  have h2 := (hu.isRieszColemanProjection_rieszColemanProjection
    hQ0 hQlc hS₀ hFac hCop).mapCoeffs hQlc f ⟨C, hC⟩
  exact h1.unique h2

end Ring

section Field

variable {I K L : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  {u : C₀(I, K) →L[K] C₀(I, K)}

/-- Bounded field extension preserves the dimension of `ker Q*(u)` for a coprime polynomial factor
`Q` of the Fredholm series of a row-compact operator. -/
theorem IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs (hu : u.IsRowCompact)
    (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖) {Q : K[X]} (hQ0 : Q.coeff 0 = 1)
    {S₀ : K⟦X⟧} (hS₀ : S₀.IsEntire) (hFac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S₀)
    (hCop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S₀, IsEntire.mem_subring.mpr hS₀⟩) :
    Module.finrank L (LinearMap.ker ((Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse :
      C₀(I, L) →L[L] C₀(I, L)) : Module.End L C₀(I, L))) =
    Module.finrank K (LinearMap.ker ((Polynomial.aeval u Q.reverse :
      C₀(I, K) →L[K] C₀(I, K)) : Module.End K C₀(I, K))) := by
  obtain ⟨C, hC⟩ := hf
  have hQne : Q ≠ 0 := fun h ↦ by simp [h] at hQ0
  have hQlc : IsUnit Q.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQne)
  have hQ0' : (Q.map f).coeff 0 = 1 := by simp [hQ0]
  have hS₀' : (PowerSeries.map f S₀).IsEntire := hS₀.map f hC
  have hFac' : (u.mapCoeffs f ⟨C, hC⟩).matrixCoeff.charPowerSeries =
      ((Q.map f : L[X]) : L⟦X⟧) * PowerSeries.map f S₀ := by
    rw [hu.charPowerSeries_map f ⟨C, hC⟩, hFac, map_mul, Polynomial.polynomial_map_coe]
  have hCop' := isCoprime_map_entire hS₀ f ⟨C, hC⟩ hCop
  rw [(hu.mapCoeffs f ⟨C, hC⟩).finrank_ker_aeval_reverse hQ0' hS₀' hFac' hCop',
    hu.finrank_ker_aeval_reverse hQ0 hS₀ hFac hCop,
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (hQlc.map f).ne_zero]

end Field

end ContinuousLinearMap
