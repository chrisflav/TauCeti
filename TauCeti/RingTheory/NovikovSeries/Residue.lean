/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.NovikovSeries.Functoriality
public import TauCeti.RingTheory.NovikovSeries.Grading

/-!
# The energy-zero residue ring of nonnegative Novikov series

Let `N : H →+ ℝ` be a period homomorphism on an additive group `H` and `R` a ring. A series `a`
in the nonnegative subring `TauCeti.NovikovSeries.nonnegSubring R N` vanishes at every exponent of
negative period and has only finitely many nonzero coefficients of period `≤ 0`, in particular
finitely many nonzero coefficients on the period kernel `N.ker`. Retaining these period-zero
coefficients defines a ring homomorphism

`TauCeti.NovikovSeries.residueHom R N : nonnegSubring R N →+* AddMonoidAlgebra R N.ker`.

Because periods of support exponents are nonnegative, any pair `u + v = k` with `k ∈ N.ker` and
nonzero coefficients in two nonnegative series forces `N u = 0` and `N v = 0`, so convolution
restricts to the group ring of `N.ker`. The inclusion
`TauCeti.NovikovSeries.ofKerAddMonoidAlgebra R N : AddMonoidAlgebra R N.ker →+* nonnegSubring R N`
is a right inverse ring homomorphism, and the kernel of `residueHom R N` is precisely the positive
ideal `TauCeti.NovikovSeries.posIdeal R N`. Consequently the quotient
`nonnegSubring R N ⧸ posIdeal R N` is canonically isomorphic to the group ring `R[N.ker]`
(`TauCeti.NovikovSeries.quotientPosIdealRingEquiv`, and `quotientPosIdealAlgEquiv` as an algebra
isomorphism over a commutative ground ring).

The residue map and its section are compatible with any degree function `f : H → ι` on exponents
and are natural with respect to period-rescaling pushforwards `mapNonnegSubring`.

## Main definitions

* `TauCeti.NovikovSeries.residueHom`: the period-zero residue ring homomorphism from
  `nonnegSubring R N` to `AddMonoidAlgebra R N.ker`.
* `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra`: the section embedding `AddMonoidAlgebra R N.ker`
  into `nonnegSubring R N`.
* `TauCeti.NovikovSeries.quotientPosIdealRingEquiv`: the canonical ring isomorphism
  `nonnegSubring R N ⧸ posIdeal R N ≃+* AddMonoidAlgebra R N.ker`.
* `TauCeti.NovikovSeries.residueAlgHom`, `TauCeti.NovikovSeries.ofKerAddMonoidAlgebraAlgHom`, and
  `TauCeti.NovikovSeries.quotientPosIdealAlgEquiv`: the `S`-algebra versions for an `S`-algebra `R`.

## Main results

* `TauCeti.NovikovSeries.residueHom_ofKerAddMonoidAlgebra`: `ofKerAddMonoidAlgebra` is a right
  inverse to `residueHom`.
* `TauCeti.NovikovSeries.ker_residueHom`: the kernel of `residueHom` is `posIdeal R N`.
* `TauCeti.NovikovSeries.residueHom_mem_gradeBy` and
  `TauCeti.NovikovSeries.ofKerAddMonoidAlgebra_mem_gradeBy_iff`: compatibility with exponent
  gradings.
* `TauCeti.NovikovSeries.residueHom_mapNonnegSubring`: naturality of the residue homomorphism under
  period-rescaling pushforwards.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta, and K. Ono, *Lagrangian Intersection Floer Theory: Anomaly and
  Obstruction*, AMS/IP Studies in Advanced Mathematics 46 (2009), Chapter 3.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace NovikovSeries

section Ring

variable {R H : Type*} [Ring R] [AddGroup H] {N : H →+ ℝ}

/-- A nonnegative Novikov series has only finitely many nonzero coefficients on the period
kernel. -/
private theorem finite_support_ker (a : nonnegSubring R N) :
    (Function.support fun k : N.ker => (a : NovikovSeries R H N).coeff k).Finite := by
  refine ((a : NovikovSeries R H N).finite_le 0).preimage N.ker.subtype_injective.injOn |>.subset ?_
  intro k hk
  exact ⟨hk, le_of_eq (AddMonoidHom.mem_ker.1 k.2)⟩

/-- The underlying finitely supported function on `N.ker` of the energy-zero residue of a
nonnegative Novikov series. -/
private def residueFinsupp (a : nonnegSubring R N) : N.ker →₀ R :=
  Finsupp.ofSupportFinite (fun k : N.ker => (a : NovikovSeries R H N).coeff k)
    (finite_support_ker a)

@[simp]
private theorem residueFinsupp_apply (a : nonnegSubring R N) (k : N.ker) :
    residueFinsupp a k = (a : NovikovSeries R H N).coeff k :=
  rfl

variable (R N) in
/-- The energy-zero residue ring homomorphism `nonnegSubring R N →+* R[N.ker]`, keeping the
coefficients at exponents of period zero. -/
def residueHom : nonnegSubring R N →+* AddMonoidAlgebra R N.ker where
  toFun a := AddMonoidAlgebra.ofCoeff (residueFinsupp a)
  map_one' := by
    classical
    ext k
    simp [residueFinsupp, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, coeff_one,
      Finsupp.single_apply, eq_comm]
  map_mul' a b := by
    classical
    ext k
    simp only [residueFinsupp_apply, MulMemClass.coe_mul, AddMonoidAlgebra.coeff_mul]
    set s : Finset (N.ker × N.ker) :=
      ((residueFinsupp a).support ×ˢ (residueFinsupp b).support).filter
        fun p => p.1 + p.2 = k
    have hmul : ((a : NovikovSeries R H N) * (b : NovikovSeries R H N)).coeff k =
        ∑ p ∈ s, (a : NovikovSeries R H N).coeff p.1 * (b : NovikovSeries R H N).coeff p.2 := by
      refine coeff_mul_eq_sum_of_injOn (F := s)
        (f := fun p : N.ker × N.ker => ((p.1 : H), (p.2 : H)))
        (fun p hp => by
          have hp' : p.1 + p.2 = k := (Finset.mem_filter.1 hp).2
          simpa only [← AddSubgroup.coe_add] using congrArg Subtype.val hp')
        (fun u v huv hu hv => ?_)
        (fun p _ q _ hpq => by
          simp only [Prod.mk.injEq] at hpq
          exact Prod.ext (Subtype.ext hpq.1) (Subtype.ext hpq.2))
      have hu0 : 0 ≤ N u := not_lt.1 fun hlt => hu (mem_nonnegSubring.1 a.2 u hlt)
      have hv0 : 0 ≤ N v := not_lt.1 fun hlt => hv (mem_nonnegSubring.1 b.2 v hlt)
      have huv0 : N u + N v = 0 := by
        rw [← map_add, huv]
        exact AddMonoidHom.mem_ker.1 k.2
      have huK : u ∈ N.ker := AddMonoidHom.mem_ker.2 (by linarith)
      have hvK : v ∈ N.ker := AddMonoidHom.mem_ker.2 (by linarith)
      refine ⟨(⟨u, huK⟩, ⟨v, hvK⟩), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, ?_⟩,
        Subtype.ext huv⟩, rfl⟩
      · exact Finsupp.mem_support_iff.2 hu
      · exact Finsupp.mem_support_iff.2 hv
    rw [hmul, Finsupp.sum]
    simp_rw [Finsupp.sum, ← Finset.sum_product', ← Finset.sum_filter]
    rfl
  map_zero' := by
    ext
    simp [residueFinsupp]
  map_add' a b := by
    ext k
    simp [residueFinsupp]

/-- The coefficient of the energy-zero residue at `k ∈ N.ker` is the coefficient of the series
at `k`. -/
@[simp]
theorem coeff_residueHom (a : nonnegSubring R N) (k : N.ker) :
    (residueHom R N a).coeff k = (a : NovikovSeries R H N).coeff k := by
  rfl

/-- The energy-zero residue of a monomial with exponent in `N.ker` is the corresponding group-ring
monomial. -/
@[simp]
theorem residueHom_single_of_mem_ker (k : N.ker) (r : R) :
    residueHom R N ⟨single (k : H) r, single_mem_nonnegSubring (AddMonoidHom.mem_ker.1 k.2).ge r⟩ =
      AddMonoidAlgebra.single k r := by
  classical
  ext g
  by_cases hgk : g = k
  · subst hgk
    simp
  · have hval : (g : H) ≠ (k : H) := fun h => hgk (Subtype.ext h)
    simp [coeff_single_of_ne hval, AddMonoidAlgebra.coeff_single, Ne.symm hgk]

/-- Every monomial of strictly positive period has zero energy-zero residue. -/
@[simp]
theorem residueHom_single_of_pos {g : H} (hg : 0 < N g) (r : R) :
    residueHom R N ⟨single g r, single_mem_nonnegSubring hg.le r⟩ = 0 := by
  ext k
  have hkg : (k : H) ≠ g := fun h => by
    have hk0 : N k = 0 := AddMonoidHom.mem_ker.1 k.2
    rw [h] at hk0
    linarith
  simp [coeff_single_of_ne hkg]

variable (R N) in
/-- The section ring homomorphism embedding the group ring `R[N.ker]` into `nonnegSubring R N`. -/
def ofKerAddMonoidAlgebra : AddMonoidAlgebra R N.ker →+* nonnegSubring R N :=
  ((ofAddMonoidAlgebra (R := R) (N := N)).comp
    (AddMonoidAlgebra.mapDomainRingHom R N.ker.subtype)).codRestrict (nonnegSubring R N) fun x => by
    classical
    refine mem_nonnegSubring.2 fun h hh => ?_
    rw [RingHom.comp_apply, coeff_ofAddMonoidAlgebra]
    by_contra hne
    have hmem : h ∈ (AddMonoidAlgebra.mapDomain N.ker.subtype x).coeff.support :=
      Finsupp.mem_support_iff.2 hne
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hmem)
    exact hh.ne (AddMonoidHom.mem_ker.1 k.2)

/-- The coercion of `ofKerAddMonoidAlgebra R N x` to `NovikovSeries R H N` is the image of `x`
under the subgroup inclusion into `AddMonoidAlgebra R H`. -/
theorem coe_ofKerAddMonoidAlgebra (x : AddMonoidAlgebra R N.ker) :
    (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N) =
      ofAddMonoidAlgebra (AddMonoidAlgebra.mapDomainRingHom R N.ker.subtype x) := by
  rfl

/-- At an exponent in `N.ker`, `ofKerAddMonoidAlgebra` preserves coefficients. -/
@[simp]
theorem coeff_ofKerAddMonoidAlgebra_coe (x : AddMonoidAlgebra R N.ker) (k : N.ker) :
    (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N).coeff k = x.coeff k := by
  rw [coe_ofKerAddMonoidAlgebra, coeff_ofAddMonoidAlgebra]
  exact Finsupp.mapDomain_apply_of_injective N.ker.subtype_injective x.coeff k

/-- Outside `N.ker`, `ofKerAddMonoidAlgebra` has zero coefficients. -/
@[simp]
theorem coeff_ofKerAddMonoidAlgebra_of_notMem (x : AddMonoidAlgebra R N.ker) {h : H}
    (hh : h ∉ N.ker) : (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N).coeff h = 0 := by
  rw [coe_ofKerAddMonoidAlgebra, coeff_ofAddMonoidAlgebra]
  exact Finsupp.mapDomain_of_notMem_range x.coeff h (by simpa using hh)

/-- The image of a monomial `AddMonoidAlgebra.single k r` under `ofKerAddMonoidAlgebra` is
`single k r`. -/
@[simp]
theorem ofKerAddMonoidAlgebra_single (k : N.ker) (r : R) :
    (ofKerAddMonoidAlgebra R N (AddMonoidAlgebra.single k r) : NovikovSeries R H N) =
      single (k : H) r := by
  rw [coe_ofKerAddMonoidAlgebra, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, ofAddMonoidAlgebra_single]
  rfl

/-- `ofKerAddMonoidAlgebra` is a right inverse to `residueHom`. -/
@[simp]
theorem residueHom_ofKerAddMonoidAlgebra (x : AddMonoidAlgebra R N.ker) :
    residueHom R N (ofKerAddMonoidAlgebra R N x) = x := by
  ext k
  simp

/-- The composite `residueHom ∘ ofKerAddMonoidAlgebra` is the identity on `R[N.ker]`. -/
theorem residueHom_comp_ofKerAddMonoidAlgebra :
    (residueHom R N).comp (ofKerAddMonoidAlgebra R N) = RingHom.id _ :=
  RingHom.ext residueHom_ofKerAddMonoidAlgebra

/-- The energy-zero residue homomorphism is surjective. -/
theorem residueHom_surjective : Surjective (residueHom R N) :=
  Function.RightInverse.surjective residueHom_ofKerAddMonoidAlgebra

/-- The section `ofKerAddMonoidAlgebra` is injective. -/
theorem ofKerAddMonoidAlgebra_injective : Injective (ofKerAddMonoidAlgebra R N) :=
  Function.RightInverse.injective residueHom_ofKerAddMonoidAlgebra

variable (R N) in
/-- The kernel of the energy-zero residue homomorphism is the positive ideal `posIdeal R N`. -/
theorem ker_residueHom : RingHom.ker (residueHom R N) = posIdeal R N := by
  ext a
  simp only [RingHom.mem_ker, mem_posIdeal]
  constructor
  · intro ha h hh
    rcases lt_or_eq_of_le hh with hlt | heq
    · exact mem_nonnegSubring.1 a.2 h hlt
    · have hk := congrArg (fun x : AddMonoidAlgebra R N.ker => x.coeff ⟨h, heq⟩) ha
      simpa only [coeff_residueHom, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
        Pi.zero_apply] using hk
  · intro ha
    ext k
    simpa only [coeff_residueHom, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply] using ha k (le_of_eq (AddMonoidHom.mem_ker.1 k.2))

variable (R N) in
/-- The canonical ring isomorphism `nonnegSubring R N ⧸ posIdeal R N ≃+* R[N.ker]` identifying the
energy-zero residue of nonnegative Novikov series with the group ring of the period kernel. -/
def quotientPosIdealRingEquiv :
    (nonnegSubring R N ⧸ posIdeal R N) ≃+* AddMonoidAlgebra R N.ker :=
  (Ideal.quotEquivOfEq (ker_residueHom R N).symm).trans
    (RingHom.quotientKerEquivOfRightInverse
      (f := residueHom R N) (g := ofKerAddMonoidAlgebra R N)
      residueHom_ofKerAddMonoidAlgebra)

/-- On cosets, `quotientPosIdealRingEquiv` evaluates `residueHom`. -/
@[simp]
theorem quotientPosIdealRingEquiv_mk (a : nonnegSubring R N) :
    quotientPosIdealRingEquiv R N (Ideal.Quotient.mk (posIdeal R N) a) = residueHom R N a := by
  rfl

/-- The inverse of `quotientPosIdealRingEquiv` embeds `R[N.ker]` via `ofKerAddMonoidAlgebra` and
passes to the quotient modulo `posIdeal R N`. -/
@[simp]
theorem quotientPosIdealRingEquiv_symm_apply (x : AddMonoidAlgebra R N.ker) :
    (quotientPosIdealRingEquiv R N).symm x =
      Ideal.Quotient.mk (posIdeal R N) (ofKerAddMonoidAlgebra R N x) := by
  rfl

end Ring

section Algebra

variable {S R H : Type*} [CommSemiring S] [Ring R] [Algebra S R] [AddGroup H] {N : H →+ ℝ}

variable (S R N) in
/-- The energy-zero residue as an `S`-algebra homomorphism. -/
def residueAlgHom : nonnegSubring R N →ₐ[S] AddMonoidAlgebra R N.ker where
  __ := residueHom R N
  commutes' s := by
    classical
    ext k
    simp only [RingHom.toFun_eq_coe, coeff_residueHom, coe_algebraMap_nonnegSubring,
      algebraMap_apply, coeff_single, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
      AddMonoidAlgebra.coeff_single, Pi.single_apply, Finsupp.single_apply,
      ZeroMemClass.coe_eq_zero, eq_comm]

@[simp]
theorem residueAlgHom_apply (a : nonnegSubring R N) :
    residueAlgHom S R N a = residueHom R N a := by
  rfl

variable (S R N) in
/-- The section embedding `R[N.ker] → nonnegSubring R N` as an `S`-algebra homomorphism. -/
def ofKerAddMonoidAlgebraAlgHom : AddMonoidAlgebra R N.ker →ₐ[S] nonnegSubring R N where
  __ := ofKerAddMonoidAlgebra R N
  commutes' s := by
    ext h
    simp only [RingHom.toFun_eq_coe, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
      ofKerAddMonoidAlgebra_single, ZeroMemClass.coe_zero, coe_algebraMap_nonnegSubring,
      algebraMap_apply]

@[simp]
theorem ofKerAddMonoidAlgebraAlgHom_apply (x : AddMonoidAlgebra R N.ker) :
    ofKerAddMonoidAlgebraAlgHom S R N x = ofKerAddMonoidAlgebra R N x := by
  rfl

end Algebra

section CommRingAlgebra

variable {S R H : Type*} [CommSemiring S] [CommRing R] [Algebra S R] [AddGroup H] {N : H →+ ℝ}

variable (S R N) in
/-- The canonical `S`-algebra isomorphism `nonnegSubring R N ⧸ posIdeal R N ≃ₐ[S] R[N.ker]`. -/
def quotientPosIdealAlgEquiv :
    (nonnegSubring R N ⧸ posIdeal R N) ≃ₐ[S] AddMonoidAlgebra R N.ker :=
  AlgEquiv.ofRingEquiv (f := quotientPosIdealRingEquiv R N) fun s => by
    rw [← Ideal.Quotient.mk_algebraMap, quotientPosIdealRingEquiv_mk]
    exact (residueAlgHom S R N).commutes s

@[simp]
theorem quotientPosIdealAlgEquiv_mk (a : nonnegSubring R N) :
    quotientPosIdealAlgEquiv S R N (Ideal.Quotient.mk (posIdeal R N) a) = residueHom R N a := by
  rfl

@[simp]
theorem quotientPosIdealAlgEquiv_symm_apply (x : AddMonoidAlgebra R N.ker) :
    (quotientPosIdealAlgEquiv S R N).symm x =
      Ideal.Quotient.mk (posIdeal R N) (ofKerAddMonoidAlgebra R N x) := by
  rfl

end CommRingAlgebra

section Grading

variable {R H ι : Type*} [CommRing R] [AddGroup H] {N : H →+ ℝ} {f : H → ι} {i : ι}

/-- The energy-zero residue sends a homogeneous nonnegative series of degree `i` into the
homogeneous piece of degree `i` of `R[N.ker]` for the restricted degree function. -/
theorem residueHom_mem_gradeBy {a : nonnegSubring R N}
    (ha : (a : NovikovSeries R H N) ∈ gradeBy R N f i) :
    residueHom R N a ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro k hk
  exact mem_gradeBy_iff.1 ha (mem_support.2 (Finsupp.mem_support_iff.1 hk))

/-- The section `ofKerAddMonoidAlgebra` preserves and reflects homogeneity for any degree function
on exponents. -/
theorem ofKerAddMonoidAlgebra_mem_gradeBy_iff {x : AddMonoidAlgebra R N.ker} :
    (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N) ∈ gradeBy R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R (f ∘ N.ker.subtype) i := by
  rw [mem_gradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff]
  constructor
  · intro hx k hk
    have hxk : (ofKerAddMonoidAlgebra R N x : NovikovSeries R H N).coeff k ≠ 0 := by
      simpa only [coeff_ofKerAddMonoidAlgebra_coe] using Finsupp.mem_support_iff.1 hk
    exact hx (mem_support.2 hxk)
  · intro hx h hh
    by_cases hK : h ∈ N.ker
    · have hxk : x.coeff ⟨h, hK⟩ ≠ 0 := by
        rw [← coeff_ofKerAddMonoidAlgebra_coe x ⟨h, hK⟩]
        exact mem_support.1 hh
      exact hx (Finsupp.mem_support_iff.2 hxk)
    · exact absurd (coeff_ofKerAddMonoidAlgebra_of_notMem x hK) (mem_support.1 hh)

end Grading

section Pushforward

variable {R S H H' : Type*} [Ring R] [Ring S] [AddGroup H] [AddGroup H']
  {N : H →+ ℝ} {N' : H' →+ ℝ}

/-- A period-rescaling homomorphism `φ : H →+ H'` restricts to a homomorphism `N.ker →+ N'.ker`
between period kernels. -/
def periodKerMap (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) :
    N.ker →+ N'.ker :=
  (φ.comp N.ker.subtype).codRestrict N'.ker fun k => by
    obtain ⟨c, _, hcφ⟩ := hφ
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.subtype_apply, hcφ,
      AddMonoidHom.mem_ker.1 k.2, mul_zero]

@[simp]
theorem coe_periodKerMap (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (k : N.ker) :
    (periodKerMap φ hφ k : H') = φ k := by
  rfl

/-- Naturality of the energy-zero residue with respect to a period-rescaling pushforward
`mapNonnegSubring`: taking the residue commutes with pushing coefficients forward by `ρ` and
exponents along `periodKerMap φ hφ`. -/
theorem residueHom_mapNonnegSubring (ρ : R →+* S) (φ : H →+ H')
    (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (a : nonnegSubring R N) :
    residueHom S N' (mapNonnegSubring ρ φ hφ a) =
      AddMonoidAlgebra.mapDomainRingHom S (periodKerMap φ hφ)
        (AddMonoidAlgebra.mapRingHom N.ker ρ (residueHom R N a)) := by
  classical
  obtain ⟨c, hc, hcφ⟩ := hφ
  ext k'
  rw [coeff_residueHom, coe_mapNonnegSubring]
  set t : Finset N.ker :=
    (residueFinsupp a).support.filter fun k => periodKerMap φ ⟨c, hc, hcφ⟩ k = k'
  -- Every support exponent of `a` mapping into `N'.ker` already lies in `N.ker`.
  have hsub : (a : NovikovSeries R H N).support ∩ φ ⁻¹' {(k' : H')} ⊆
      (t.image N.ker.subtype : Set H) := by
    rintro h ⟨hh, hφh⟩
    have hNh : N h = 0 := by
      have h0 : c * N h = 0 := by
        rw [← hcφ, (hφh : φ h = k')]
        exact AddMonoidHom.mem_ker.1 k'.2
      exact (mul_eq_zero.1 h0).resolve_left hc.ne'
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨h, hNh⟩, Finset.mem_filter.2 ⟨?_, ?_⟩, rfl⟩)
    · exact Finsupp.mem_support_iff.2 (mem_support.1 hh)
    · exact Subtype.ext hφh
  rw [coeff_map_eq_sum (ρ : R →+ S) φ ⟨c, hc, hcφ⟩ a (t.image N.ker.subtype) hsub
      (fun h hh => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hh
        exact congrArg Subtype.val (Finset.mem_filter.1 hk).2),
    Finset.sum_image (fun _ _ _ _ h => N.ker.subtype_injective h)]
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain,
    Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  simp_rw [Finsupp.single_apply, ← Finset.sum_filter, AddMonoidAlgebra.coeff_mapRingHom,
    coeff_residueHom]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    simp only [t, Finset.mem_filter, Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_mapRingHom,
      coeff_residueHom, residueFinsupp_apply] at hk ⊢
    refine ⟨fun h0 => hk.1 ?_, hk.2⟩
    simp [h0]
  · intro k hk hnot
    simp only [t, Finset.mem_filter, Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_mapRingHom,
      coeff_residueHom, residueFinsupp_apply, not_and] at hk hnot
    by_contra h0
    exact hnot h0 hk.2

end Pushforward

end NovikovSeries

end TauCeti
