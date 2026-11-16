/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.NovikovSeries.Grading
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing

/-!
# Energy-zero residue ring of the nonnegative Novikov subring

Let `H` be an additive group with a period homomorphism `N : H →+ ℝ` and `R` a ring of
coefficients. A series in `nonnegSubring R N` has only finitely many nonzero coefficients of
period `0` (since the support below cutoff `1` is finite), and when two nonnegative series are
multiplied, any pair of support exponents summing into `N.ker` must have both summands in `N.ker`.

Consequently, keeping the coefficients on `N.ker` defines a surjective ring homomorphism
`residueHom R N : nonnegSubring R N →+* AddMonoidAlgebra R N.ker` with kernel `posIdeal R N` and
right inverse `ofKerAddMonoidAlgebra R N`. Passing to the quotient identifies
`nonnegSubring R N ⧸ posIdeal R N` with the group ring `AddMonoidAlgebra R N.ker`
(`quotientPosIdealEquiv R N`), compatibly with any degree grading.

## Main definitions

* `TauCeti.NovikovSeries.residueHom`: the ring homomorphism from `nonnegSubring R N` to
  `AddMonoidAlgebra R N.ker` retaining period-zero coefficients.
* `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra`: the section embedding `AddMonoidAlgebra R N.ker`
  into `nonnegSubring R N`.
* `TauCeti.NovikovSeries.quotientPosIdealEquiv`: the ring isomorphism
  `(nonnegSubring R N ⧸ posIdeal R N) ≃+* AddMonoidAlgebra R N.ker`.

## Main results

* `TauCeti.NovikovSeries.ker_residueHom`: the kernel of `residueHom R N` is `posIdeal R N`.
* `TauCeti.NovikovSeries.residueHom_surjective`: `residueHom R N` is surjective.
* `TauCeti.NovikovSeries.residueHom_mem_gradeBy` and
  `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra_mem_gradeBy_iff`: compatibility with gradings.
-/

public section

noncomputable section

open Finset Function

namespace TauCeti

namespace NovikovSeries

section Ring

variable {R H : Type*} [Ring R] [AddGroup H] {N : H →+ ℝ}

private def residueFinsupp (a : nonnegSubring R N) : N.ker →₀ R :=
  Finsupp.onFinset
    ((a.1.finite_lt 1).toFinset.preimage N.ker.subtype N.ker.subtype_injective.injOn)
    (fun k => a.1.coeff k)
    (fun k hk => by
      rw [mem_preimage, Set.Finite.mem_toFinset]
      exact ⟨hk, by rw [AddSubgroup.subtype_apply, k.2]; exact zero_lt_one⟩)

variable (R N) in
/-- The period-zero residue homomorphism `nonnegSubring R N →+* AddMonoidAlgebra R N.ker`,
retaining the coefficients supported on `N.ker`. -/
def residueHom : nonnegSubring R N →+* AddMonoidAlgebra R N.ker where
  toFun a := AddMonoidAlgebra.ofCoeff (residueFinsupp a)
  map_zero' := AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun _ => rfl
  map_add' a b := AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun k =>
    coeff_add a.1 b.1 k
  map_one' := AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun k => by
    classical
    change (1 : NovikovSeries R H N).coeff k = (1 : AddMonoidAlgebra R N.ker).coeff k
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, coeff_one]
    by_cases hk : k = 0
    · subst hk
      simp
    · have hk' : (k : H) ≠ 0 := fun h => hk (Subtype.ext h)
      simp [hk, hk']
  map_mul' a b := AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun k => by
    classical
    change (a.1 * b.1).coeff k =
      (AddMonoidAlgebra.ofCoeff (residueFinsupp a) *
        AddMonoidAlgebra.ofCoeff (residueFinsupp b)).coeff k
    let fa := residueFinsupp a
    let fb := residueFinsupp b
    rw [coeff_mul_eq_sum_of_injOn
      (F := (fa.support ×ˢ fb.support).filter fun p : N.ker × N.ker => p.1 + p.2 = k)
      (f := fun p : N.ker × N.ker => ((p.1 : H), (p.2 : H)))
      (fun p hp => by rw [← AddSubgroup.coe_add, (mem_filter.1 hp).2])
      (fun u v huv hu hv => ?_)
      (fun p _ q _ hpq => Prod.ext (Subtype.ext (Prod.mk.inj hpq).1)
        (Subtype.ext (Prod.mk.inj hpq).2))]
    · rw [sum_filter, sum_product, AddMonoidAlgebra.coeff_mul]
      simp only [Finsupp.sum, fa, fb, residueFinsupp, Finsupp.onFinset_apply]
    · have hNu : 0 ≤ N u := not_lt.1 fun h => hu (mem_nonnegSubring.1 a.2 u h)
      have hNv : 0 ≤ N v := not_lt.1 fun h => hv (mem_nonnegSubring.1 b.2 v h)
      have hNuv : N u + N v = 0 := by rw [← map_add, huv, k.2]
      have hu0 : u ∈ N.ker := by rw [AddMonoidHom.mem_ker]; linarith
      have hv0 : v ∈ N.ker := by rw [AddMonoidHom.mem_ker]; linarith
      refine ⟨(⟨u, hu0⟩, ⟨v, hv0⟩), mem_filter.2 ⟨mem_product.2 ⟨?_, ?_⟩, Subtype.ext huv⟩, rfl⟩
      · exact Finsupp.mem_support_iff.2 hu
      · exact Finsupp.mem_support_iff.2 hv

@[simp]
theorem coeff_residueHom (a : nonnegSubring R N) (k : N.ker) :
    (residueHom R N a).coeff k = (a : NovikovSeries R H N).coeff k := by
  simp [residueHom, residueFinsupp]

/-- A nonnegative series has zero period-zero residue if and only if it belongs to `posIdeal`. -/
theorem residueHom_eq_zero_iff {a : nonnegSubring R N} :
    residueHom R N a = 0 ↔ a ∈ posIdeal R N := by
  refine ⟨fun ha => mem_posIdeal.2 fun h hh => ?_, fun ha => ?_⟩
  · rcases lt_or_eq_of_le hh with hlt | heq
    · exact mem_nonnegSubring.1 a.2 h hlt
    · have hk : h ∈ N.ker := heq
      have h0 := congrArg (fun x : AddMonoidAlgebra R N.ker => x.coeff ⟨h, hk⟩) ha
      simpa using h0
  · refine AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun k => ?_
    simp [mem_posIdeal.1 ha k (le_of_eq k.2)]

variable (R N) in
/-- The kernel of `residueHom R N` is the strictly positive ideal `posIdeal R N`. -/
theorem ker_residueHom : RingHom.ker (residueHom R N) = posIdeal R N := by
  ext a
  exact residueHom_eq_zero_iff

variable (R N) in
/-- The canonical section `AddMonoidAlgebra R N.ker →+* nonnegSubring R N` sending a group-ring
element supported on `N.ker` to the corresponding finitely supported series in `nonnegSubring`. -/
def ofKerAddMonoidAlgebra : AddMonoidAlgebra R N.ker →+* nonnegSubring R N :=
  ((ofAddMonoidAlgebra (R := R) (N := N)).comp
    (AddMonoidAlgebra.mapDomainRingHom R N.ker.subtype)).codRestrict (nonnegSubring R N) fun x => by
    refine mem_nonnegSubring.2 fun h hh => ?_
    simp only [RingHom.comp_apply, coeff_ofAddMonoidAlgebra,
      AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
    exact Finsupp.mapDomain_of_notMem_range x.coeff h fun ⟨k, hk⟩ => by
      subst hk
      exact hh.ne k.2

@[simp]
theorem coe_ofKerAddMonoidAlgebra (x : AddMonoidAlgebra R N.ker) :
    (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N) =
      ofAddMonoidAlgebra (AddMonoidAlgebra.mapDomain N.ker.subtype x) := by
  simp [ofKerAddMonoidAlgebra]

theorem coeff_ofKerAddMonoidAlgebra_coe (x : AddMonoidAlgebra R N.ker) (k : N.ker) :
    (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N).coeff k = x.coeff k := by
  rw [coe_ofKerAddMonoidAlgebra, coeff_ofAddMonoidAlgebra, AddMonoidAlgebra.coeff_mapDomain,
    ← AddSubgroup.subtype_apply k, Finsupp.mapDomain_apply_of_injective N.ker.subtype_injective]

theorem ofKerAddMonoidAlgebra_single (k : N.ker) (r : R) :
    (ofKerAddMonoidAlgebra R N (AddMonoidAlgebra.single k r) : NovikovSeries R H N) =
      single (k : H) r := by
  rw [coe_ofKerAddMonoidAlgebra, AddMonoidAlgebra.mapDomain_single, ofAddMonoidAlgebra_single]
  rfl

@[simp]
theorem residueHom_ofKerAddMonoidAlgebra (x : AddMonoidAlgebra R N.ker) :
    residueHom R N (ofKerAddMonoidAlgebra R N x) = x := by
  refine AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun k => ?_
  rw [coeff_residueHom, coeff_ofKerAddMonoidAlgebra_coe]

variable (R N) in
theorem residueHom_comp_ofKerAddMonoidAlgebra :
    (residueHom R N).comp (ofKerAddMonoidAlgebra R N) = RingHom.id _ :=
  RingHom.ext residueHom_ofKerAddMonoidAlgebra

variable (R N) in
/-- The period-zero residue map `residueHom R N` is surjective, split by `ofKerAddMonoidAlgebra`. -/
theorem residueHom_surjective : Surjective (residueHom R N) :=
  Function.RightInverse.surjective residueHom_ofKerAddMonoidAlgebra

variable (R N) in
theorem ofKerAddMonoidAlgebra_injective : Injective (ofKerAddMonoidAlgebra R N) :=
  Function.LeftInverse.injective residueHom_ofKerAddMonoidAlgebra

@[simp]
theorem residueHom_single_of_mem_ker (k : N.ker) (r : R) :
    residueHom R N ⟨single (k : H) r, single_mem_nonnegSubring (le_of_eq k.2.symm) r⟩ =
      AddMonoidAlgebra.single k r := by
  have h : (⟨single (k : H) r, single_mem_nonnegSubring (le_of_eq k.2.symm) r⟩ :
      nonnegSubring R N) = ofKerAddMonoidAlgebra R N (AddMonoidAlgebra.single k r) :=
    Subtype.ext (ofKerAddMonoidAlgebra_single k r).symm
  rw [h, residueHom_ofKerAddMonoidAlgebra]

@[simp]
theorem residueHom_single_of_pos {g : H} (hg : 0 < N g) (r : R) :
    residueHom R N ⟨single g r, single_mem_nonnegSubring hg.le r⟩ = 0 :=
  residueHom_eq_zero_iff.2 (single_mem_posIdeal hg r)

variable (R N) in
/-- **Energy-zero residue isomorphism.** The quotient of the nonnegative Novikov subring by its
strictly positive ideal is canonically isomorphic to the group ring of the period kernel. -/
def quotientPosIdealEquiv :
    (nonnegSubring R N ⧸ posIdeal R N) ≃+* AddMonoidAlgebra R N.ker :=
  (Ideal.quotEquivOfEq (ker_residueHom R N).symm).trans
    (RingHom.quotientKerEquivOfRightInverse residueHom_ofKerAddMonoidAlgebra)

@[simp]
theorem quotientPosIdealEquiv_mk (a : nonnegSubring R N) :
    quotientPosIdealEquiv R N (Ideal.Quotient.mk (posIdeal R N) a) = residueHom R N a :=
  (rfl)

@[simp]
theorem quotientPosIdealEquiv_symm_apply (x : AddMonoidAlgebra R N.ker) :
    (quotientPosIdealEquiv R N).symm x =
      Ideal.Quotient.mk (posIdeal R N) (ofKerAddMonoidAlgebra R N x) :=
  (rfl)

end Ring

section Grading

variable {R H ι : Type*} [CommRing R] [AddGroup H] {N : H →+ ℝ}

/-- The period-zero residue map preserves any degree grading on exponents. -/
theorem residueHom_mem_gradeBy (f : H → ι) {i : ι} {a : nonnegSubring R N}
    (ha : (a : NovikovSeries R H N) ∈ gradeBy R N f i) :
    residueHom R N a ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro k hk
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_residueHom] at hk
  exact mem_gradeBy_iff.1 ha (mem_support.2 hk)

/-- The section `ofKerAddMonoidAlgebra` preserves and reflects any degree grading on exponents. -/
theorem ofKerAddMonoidAlgebra_mem_gradeBy_iff (f : H → ι) {i : ι}
    {x : AddMonoidAlgebra R N.ker} :
    (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N) ∈ gradeBy R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · simpa only [residueHom_ofKerAddMonoidAlgebra] using residueHom_mem_gradeBy f hx
  · rw [AddMonoidAlgebra.mem_gradeBy_iff] at hx
    rw [mem_gradeBy_iff]
    intro h hh
    rw [mem_support, coe_ofKerAddMonoidAlgebra, coeff_ofAddMonoidAlgebra,
      AddMonoidAlgebra.coeff_mapDomain] at hh
    have hmem : h ∈ Set.range N.ker.subtype := by
      by_contra hnot
      exact hh (Finsupp.mapDomain_of_notMem_range x.coeff h hnot)
    obtain ⟨k, rfl⟩ := hmem
    rw [Finsupp.mapDomain_apply_of_injective N.ker.subtype_injective] at hh
    exact hx (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hh))

end Grading

end NovikovSeries

end TauCeti
