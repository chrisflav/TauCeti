/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import TauCeti.RingTheory.NovikovSeries.Field
public import TauCeti.RingTheory.NovikovSeries.HomogeneousCompletion
public import TauCeti.RingTheory.NovikovSeries.Residue
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Period-section localization, action-weighted extensions, and action-field specialization

Let `N : H →+ ℝ` be a period homomorphism on an additive monoid `H`, and suppose `s : ℝ →+ H` is
an additive section of `N` (`∀ r, N (s r) = r`). The real-period monomials
`T^r := single (s r) 1` (`TauCeti.NovikovSeries.sectionMonomial R N s r`) are units of
`NovikovSeries R H N` with inverses `T^(-r)`, whereas for `r > 0` over a nontrivial ring `T^r` is
not a unit of the nonnegative subring `nonnegSubring R N`
(`TauCeti.NovikovSeries.not_isUnit_nonnegSectionMonomial`). Because every Novikov series lies in
some period neighbourhood `U_C`, multiplying by `T^(max 0 (-C))` moves it into `nonnegSubring R N`.
Hence for commutative `R` and `H`, `NovikovSeries R H N` is the localization of `nonnegSubring R N`
at the multiplicative submonoid `S = {T^r | r ≥ 0}`
(`TauCeti.NovikovSeries.isLocalization_sectionSubmonoid`), and any ring homomorphism out of
`nonnegSubring R N` sending positive monomials `T^r` (`r > 0`) to units extends uniquely to
`NovikovSeries R H N` (`TauCeti.NovikovSeries.liftOfIsUnitSectionMonomial`).

Two instances of this general localization theorem are recorded immediately:

1. **Universal real Novikov ring `Nov(R, ℝ, id)`**: taking `H = ℝ` and `N = s = id`, localizing
   `nonnegSubring R (AddMonoidHom.id ℝ)` at `{T^r | r ≥ 0}` recovers
   `NovikovSeries R ℝ (AddMonoidHom.id ℝ)` (`TauCeti.NovikovSeries.isLocalization_real`), which
   over a field `k` is a field (`TauCeti.NovikovSeries.isField_real`) in which every nonzero series
   factors as `c T^{t₀} (1 - b)` with `b ∈ posIdeal`
   (`TauCeti.NovikovSeries.exists_single_mul_one_sub_real`).
2. **Action-weighted extension `(G × ℝ, E_R, μ_R)`**: for an additive monoid (or group) `G` with
   period `E : G →+ ℝ` and grading `μ : G →+ ι`, setting `E_R(g, r) = E g + r`
   (`TauCeti.NovikovSeries.actionPeriod E`) and `μ_R(g, r) = μ g`
   (`TauCeti.NovikovSeries.actionDegreeHom μ`) equips `G × ℝ` with the degree-zero section
   `r ↦ (0, r)` (`TauCeti.NovikovSeries.actionSection G`). Thus:
   * `Nov(R, G × ℝ, E_R)` is the localization of its nonnegative subring at `{T^r | r ≥ 0}`
     (`TauCeti.NovikovSeries.isLocalization_actionExtension`);
   * `T^r` has degree `0` and preserves every homogeneous piece;
   * `Nov(R, G, E)` embeds injectively, continuously, and with preserved grading into
     `Nov(R, G × ℝ, E_R)` (`TauCeti.NovikovSeries.actionEmbedRingHom`);
   * the kernel of `E_R` is isomorphic to `G` via `g ↦ (g, -E g)`
     (`TauCeti.NovikovSeries.actionPeriodKerEquiv`), so the energy-zero residue ring after the real
     extension is `R[G]` (`TauCeti.NovikovSeries.actionQuotientPosIdealRingEquiv`), preserving the
     `μ`-grading;
   * for any ring homomorphism `ρ : R →+* k`, pushing forward along `E_R : G × ℝ →+ ℝ` yields the
     continuous action-field map `Nov(R, G × ℝ, E_R) →+* Nov(k, ℝ, id)`
     (`TauCeti.NovikovSeries.actionFieldMap`), whose restriction to the nonnegative subring factors
     uniquely through the localization `Nov(R, G × ℝ, E_R)`
     (`TauCeti.NovikovSeries.actionFieldMap_eq_lift`);
   * whenever `μ(G)` is infinite, the algebraic graded direct sum is dense but proper in
     `nonnegSubring R (actionPeriod E)`
     (`TauCeti.NovikovSeries.not_surjective_coeAlgHom_nonnegGradeBy_actionExtension`).

## Main definitions

* `TauCeti.NovikovSeries.sectionMonomial`, `TauCeti.NovikovSeries.nonnegSectionMonomial`, and
  `TauCeti.NovikovSeries.sectionSubmonoid`: the monomials `T^r = e^(s r)` and their multiplicative
  submonoid `{T^r | r ≥ 0}` inside `nonnegSubring R N`.
* `TauCeti.NovikovSeries.liftOfIsUnitSectionMonomial`: universal factorization of ring homomorphisms
  inverting positive monomials `T^r` (`r > 0`) through `NovikovSeries R H N`.
* `TauCeti.NovikovSeries.actionPeriod`, `TauCeti.NovikovSeries.actionSection`,
  `TauCeti.NovikovSeries.actionDegree`, `TauCeti.NovikovSeries.actionDegreeHom`,
  `TauCeti.NovikovSeries.actionEmbedRingHom`, `TauCeti.NovikovSeries.actionEmbedNonneg`:
  the action-weighted extension `(G × ℝ, E_R, μ_R)`.
* `TauCeti.NovikovSeries.actionPeriodKerEquiv`,
  `TauCeti.NovikovSeries.actionQuotientPosIdealRingEquiv`,
  `TauCeti.NovikovSeries.actionQuotientPosIdealAlgEquiv`: the energy-zero residue `R[G]` after
  real extension.
* `TauCeti.NovikovSeries.actionFieldMap` and `TauCeti.NovikovSeries.actionFieldNonnegMap`: the
  action-field pushforward along `E_R`.

## Main results

* `TauCeti.NovikovSeries.isUnit_sectionMonomial` and
  `TauCeti.NovikovSeries.not_isUnit_nonnegSectionMonomial`: for `r > 0`, `T^r` is a unit of
  `NovikovSeries R H N` and a non-unit of `nonnegSubring R N`.
* `TauCeti.NovikovSeries.isLocalization_sectionSubmonoid`: `S⁻¹ Λ₀ ≅ Λ` for any additive section
  `s : ℝ →+ H` of `N`.
* `TauCeti.NovikovSeries.isLocalization_real`, `TauCeti.NovikovSeries.isField_real`, and
  `TauCeti.NovikovSeries.exists_single_mul_one_sub_real`: localization and field structure of
  `Nov(k, ℝ, id)`.
* `TauCeti.NovikovSeries.isLocalization_actionExtension` and
  `TauCeti.NovikovSeries.actionFieldMap_eq_lift`: localization of the action-weighted extension and
  factorization of the action-field map.
* `TauCeti.NovikovSeries.not_surjective_coeAlgHom_nonnegGradeBy_actionExtension`: properness of
  the graded direct sum when `μ` has infinite range.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta, and K. Ono, *Lagrangian Intersection Floer Theory: Anomaly and
  Obstruction*, AMS/IP Studies in Advanced Mathematics 46 (2009), Chapter 3.
-/

public section

noncomputable section

open Filter Function Set
open scoped DirectSum nonZeroDivisors

namespace TauCeti

namespace NovikovSeries

section SectionMonomial

variable {R H : Type*}

/-- The monomial `T^r = e^(s r)` associated to a period section `s : ℝ →+ H`. -/
def sectionMonomial (R : Type*) [Zero R] [One R] {H : Type*} [AddZeroClass H] (N : H →+ ℝ)
    (s : ℝ →+ H) (r : ℝ) : NovikovSeries R H N :=
  single (s r) (1 : R)

theorem sectionMonomial_def [Zero R] [One R] [AddZeroClass H] (N : H →+ ℝ)
    (s : ℝ →+ H) (r : ℝ) :
    sectionMonomial R N s r = single (s r) (1 : R) := by
  rfl

@[simp]
theorem sectionMonomial_zero [Zero R] [One R] [AddZeroClass H] (N : H →+ ℝ) (s : ℝ →+ H) :
    sectionMonomial R N s 0 = 1 := by
  rw [sectionMonomial_def, map_zero, single_zero_one]

@[simp]
theorem sectionMonomial_add [NonAssocSemiring R] [AddMonoid H] (N : H →+ ℝ)
    (s : ℝ →+ H) (r₁ r₂ : ℝ) :
    sectionMonomial R N s (r₁ + r₂) = sectionMonomial R N s r₁ * sectionMonomial R N s r₂ := by
  rw [sectionMonomial_def, sectionMonomial_def, sectionMonomial_def, map_add, single_mul_single,
    one_mul]

@[simp]
theorem sectionMonomial_mul_neg [NonAssocSemiring R] [AddMonoid H] (N : H →+ ℝ)
    (s : ℝ →+ H) (r : ℝ) :
    sectionMonomial R N s r * sectionMonomial R N s (-r) = 1 := by
  rw [← sectionMonomial_add, add_neg_cancel, sectionMonomial_zero]

@[simp]
theorem sectionMonomial_neg_mul [NonAssocSemiring R] [AddMonoid H] (N : H →+ ℝ)
    (s : ℝ →+ H) (r : ℝ) :
    sectionMonomial R N s (-r) * sectionMonomial R N s r = 1 := by
  rw [← sectionMonomial_add, neg_add_cancel, sectionMonomial_zero]

/-- For every `r : ℝ`, the monomial `T^r` is a unit of `NovikovSeries R H N`, with inverse
`T^(-r)`. -/
theorem isUnit_sectionMonomial [Semiring R] [AddMonoid H] (N : H →+ ℝ) (s : ℝ →+ H) (r : ℝ) :
    IsUnit (sectionMonomial R N s r) :=
  ⟨⟨sectionMonomial R N s r, sectionMonomial R N s (-r),
    sectionMonomial_mul_neg N s r, sectionMonomial_neg_mul N s r⟩, rfl⟩

theorem sectionMonomial_mem_periodFiltration [AddGroup R] [AddZeroClass H] [One R]
    {N : H →+ ℝ} {s : ℝ →+ H} (hs : ∀ r, N (s r) = r) (r : ℝ) :
    sectionMonomial R N s r ∈ periodFiltration R N r := by
  rw [sectionMonomial_def]
  simpa only [hs r] using single_mem_periodFiltration (R := R) (N := N) (s r) (1 : R)

/-- Multiplying by `T^r` shifts the period filtration by exactly `r`. -/
theorem sectionMonomial_mul_mem_periodFiltration_iff [Ring R] [AddMonoid H]
    {N : H →+ ℝ} {s : ℝ →+ H} (hs : ∀ r, N (s r) = r) (r C : ℝ) (a : NovikovSeries R H N) :
    sectionMonomial R N s r * a ∈ periodFiltration R N (r + C) ↔ a ∈ periodFiltration R N C := by
  refine ⟨fun ha => ?_, mul_mem_periodFiltration (sectionMonomial_mem_periodFiltration hs r)⟩
  have hmul := mul_mem_periodFiltration (sectionMonomial_mem_periodFiltration hs (-r)) ha
  simpa only [← mul_assoc, sectionMonomial_neg_mul, one_mul, neg_add_cancel_left] using hmul

/-- For `r ≥ 0`, `T^r` belongs to the nonnegative subring `nonnegSubring R N`. -/
theorem sectionMonomial_mem_nonnegSubring [Ring R] [AddMonoid H] {N : H →+ ℝ} {s : ℝ →+ H}
    (hs : ∀ r, N (s r) = r) {r : ℝ} (hr : 0 ≤ r) :
    sectionMonomial R N s r ∈ nonnegSubring R N :=
  single_mem_nonnegSubring (by rwa [hs]) 1

/-- The monomial `T^r` (`r ≥ 0`) as an element of `nonnegSubring R N`. -/
def nonnegSectionMonomial (R : Type*) [Ring R] {H : Type*} [AddMonoid H] {N : H →+ ℝ}
    {s : ℝ →+ H} (hs : ∀ r, N (s r) = r) {r : ℝ} (hr : 0 ≤ r) : nonnegSubring R N :=
  ⟨sectionMonomial R N s r, sectionMonomial_mem_nonnegSubring hs hr⟩

@[simp]
theorem coe_nonnegSectionMonomial [Ring R] [AddMonoid H] {N : H →+ ℝ} {s : ℝ →+ H}
    (hs : ∀ r, N (s r) = r) {r : ℝ} (hr : 0 ≤ r) :
    (nonnegSectionMonomial R hs hr : NovikovSeries R H N) = sectionMonomial R N s r := by
  rfl

@[simp]
theorem nonnegSectionMonomial_zero [Ring R] [AddMonoid H] {N : H →+ ℝ} {s : ℝ →+ H}
    (hs : ∀ r, N (s r) = r) :
    nonnegSectionMonomial R hs le_rfl = 1 :=
  Subtype.ext (sectionMonomial_zero N s)

theorem nonnegSectionMonomial_add [Ring R] [AddMonoid H] {N : H →+ ℝ} {s : ℝ →+ H}
    (hs : ∀ r, N (s r) = r) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    nonnegSectionMonomial R hs (add_nonneg hr₁ hr₂) =
      nonnegSectionMonomial R hs hr₁ * nonnegSectionMonomial R hs hr₂ :=
  Subtype.ext (sectionMonomial_add N s r₁ r₂)

/-- For `r > 0`, `T^r` lies in the positive ideal `posIdeal R N`. -/
theorem nonnegSectionMonomial_mem_posIdeal [Ring R] [AddMonoid H] {N : H →+ ℝ} {s : ℝ →+ H}
    (hs : ∀ r, N (s r) = r) {r : ℝ} (hr : 0 < r) :
    nonnegSectionMonomial R hs hr.le ∈ posIdeal R N :=
  single_mem_posIdeal (by rwa [hs]) 1

/-- Over a nontrivial coefficient ring, for `r > 0`, the monomial `T^r` is not a unit of the
nonnegative subring `nonnegSubring R N`: any inverse would have to lower periods by `r`. -/
theorem not_isUnit_nonnegSectionMonomial [Ring R] [Nontrivial R] [AddMonoid H] {N : H →+ ℝ}
    {s : ℝ →+ H} (hs : ∀ r, N (s r) = r) {r : ℝ} (hr : 0 < r) :
    ¬ IsUnit (nonnegSectionMonomial R hs hr.le) := by
  rintro ⟨u, hu⟩
  have hmul : (nonnegSectionMonomial R hs hr.le : NovikovSeries R H N) *
      ((↑u⁻¹ : nonnegSubring R N) : NovikovSeries R H N) = 1 := by
    have := congrArg Subtype.val (congrArg (· * (↑u⁻¹ : nonnegSubring R N)) hu)
    simpa [Units.mul_inv] using this.symm
  have hmem : (1 : NovikovSeries R H N) ∈ periodFiltration R N r := by
    rw [← hmul, coe_nonnegSectionMonomial]
    simpa only [add_zero] using mul_mem_periodFiltration
      (sectionMonomial_mem_periodFiltration hs r)
      (mem_periodFiltration.2 (mem_nonnegSubring.1 (↑u⁻¹ : nonnegSubring R N).2))
  have h0 : (1 : NovikovSeries R H N).coeff 0 = 0 :=
    mem_periodFiltration.1 hmem 0 (by rwa [map_zero])
  rw [← single_zero_one, coeff_single_same] at h0
  exact one_ne_zero h0

end SectionMonomial

section Localization

variable {R H : Type*} [CommRing R] [AddCommMonoid H] {N : H →+ ℝ} {s : ℝ →+ H}

/-- The multiplicative submonoid `{T^r | r ≥ 0}` of `nonnegSubring R N` generated by the
nonnegative real-period monomials along a section `s : ℝ →+ H`. -/
def sectionSubmonoid (R : Type*) [Ring R] {H : Type*} [AddMonoid H] {N : H →+ ℝ} {s : ℝ →+ H}
    (hs : ∀ r, N (s r) = r) : Submonoid (nonnegSubring R N) where
  carrier := {a | ∃ (r : ℝ) (hr : 0 ≤ r), a = nonnegSectionMonomial R hs hr}
  one_mem' := ⟨0, le_rfl, (nonnegSectionMonomial_zero hs).symm⟩
  mul_mem' := by
    rintro _ _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, rfl⟩
    exact ⟨r₁ + r₂, add_nonneg hr₁ hr₂, (nonnegSectionMonomial_add hs hr₁ hr₂).symm⟩

@[simp]
theorem mem_sectionSubmonoid_iff (hs : ∀ r, N (s r) = r) {a : nonnegSubring R N} :
    a ∈ sectionSubmonoid R hs ↔ ∃ (r : ℝ) (hr : 0 ≤ r), a = nonnegSectionMonomial R hs hr := by
  rfl

theorem nonnegSectionMonomial_mem_sectionSubmonoid (hs : ∀ r, N (s r) = r) {r : ℝ} (hr : 0 ≤ r) :
    nonnegSectionMonomial R hs hr ∈ sectionSubmonoid R hs :=
  ⟨r, hr, rfl⟩

/-- **Localization along a period section.** Given an additive section `s : ℝ →+ H` of `N`,
`NovikovSeries R H N` is the localization of `nonnegSubring R N` at the multiplicative submonoid
`S = {T^r | r ≥ 0}`. -/
theorem isLocalization_sectionSubmonoid (hs : ∀ r, N (s r) = r) :
    IsLocalization (sectionSubmonoid R hs) (NovikovSeries R H N) := by
  rw [_root_.isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    exact isUnit_sectionMonomial N s r
  · intro z
    obtain ⟨C, hC⟩ := exists_mem_periodFiltration z
    set r : ℝ := max 0 (-C)
    have hr : 0 ≤ r := le_max_left 0 (-C)
    have hmul : z * sectionMonomial R N s r ∈ nonnegSubring R N := by
      rw [mul_comm]
      have hmem := mul_mem_periodFiltration (sectionMonomial_mem_periodFiltration hs r) hC
      refine mem_nonnegSubring.2 (mem_periodFiltration.1 (antitone_periodFiltration ?_ hmem))
      have hle : -C ≤ r := le_max_right 0 (-C)
      linarith
    exact ⟨(⟨z * sectionMonomial R N s r, hmul⟩, ⟨nonnegSectionMonomial R hs hr, r, hr, rfl⟩), rfl⟩
  · intro x y hxy
    exact ⟨1, by simp [Subtype.ext hxy]⟩

/-- Every monomial in `sectionSubmonoid R hs` is a non-zero-divisor of `nonnegSubring R N`. -/
theorem sectionSubmonoid_le_nonZeroDivisors (hs : ∀ r, N (s r) = r) :
    sectionSubmonoid R hs ≤ nonZeroDivisors (nonnegSubring R N) := by
  intro a ha
  have hu : IsUnit (a : NovikovSeries R H N) := by
    obtain ⟨r, _, rfl⟩ := ha
    exact isUnit_sectionMonomial N s r
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun b hba => Subtype.ext ?_, fun b hab => Subtype.ext ?_⟩
  · exact hu.mul_right_eq_zero.1 (congrArg Subtype.val hba)
  · exact hu.mul_left_eq_zero.1 (congrArg Subtype.val hab)

/-- Any ring homomorphism out of `nonnegSubring R N` sending every positive monomial `T^r` (`r > 0`)
to a unit extends uniquely to `NovikovSeries R H N`. -/
def liftOfIsUnitSectionMonomial {A : Type*} [CommSemiring A] (hs : ∀ r, N (s r) = r)
    (f : nonnegSubring R N →+* A)
    (hf : ∀ (r : ℝ) (hr : 0 < r), IsUnit (f (nonnegSectionMonomial R hs hr.le))) :
    NovikovSeries R H N →+* A :=
  have : IsLocalization (sectionSubmonoid R hs) (NovikovSeries R H N) :=
    isLocalization_sectionSubmonoid (R := R) hs
  IsLocalization.lift (M := sectionSubmonoid R hs) (g := f) fun ⟨a, r, hr, ha⟩ => by
    dsimp only
    rw [ha]
    rcases eq_or_lt_of_le hr with rfl | hpos
    · rw [nonnegSectionMonomial_zero, _root_.map_one]
      exact isUnit_one
    · exact hf r hpos

@[simp]
theorem liftOfIsUnitSectionMonomial_coe {A : Type*} [CommSemiring A] (hs : ∀ r, N (s r) = r)
    (f : nonnegSubring R N →+* A)
    (hf : ∀ (r : ℝ) (hr : 0 < r), IsUnit (f (nonnegSectionMonomial R hs hr.le)))
    (a : nonnegSubring R N) :
    liftOfIsUnitSectionMonomial hs f hf (a : NovikovSeries R H N) = f a := by
  have : IsLocalization (sectionSubmonoid R hs) (NovikovSeries R H N) :=
    isLocalization_sectionSubmonoid (R := R) hs
  exact IsLocalization.lift_eq (M := sectionSubmonoid R hs) _ a

theorem liftOfIsUnitSectionMonomial_comp_subtype {A : Type*} [CommSemiring A]
    (hs : ∀ r, N (s r) = r) (f : nonnegSubring R N →+* A)
    (hf : ∀ (r : ℝ) (hr : 0 < r), IsUnit (f (nonnegSectionMonomial R hs hr.le))) :
    (liftOfIsUnitSectionMonomial hs f hf).comp (nonnegSubring R N).subtype = f :=
  RingHom.ext (liftOfIsUnitSectionMonomial_coe hs f hf)

theorem liftOfIsUnitSectionMonomial_unique {A : Type*} [CommSemiring A] (hs : ∀ r, N (s r) = r)
    (f : nonnegSubring R N →+* A)
    (hf : ∀ (r : ℝ) (hr : 0 < r), IsUnit (f (nonnegSectionMonomial R hs hr.le)))
    (F : NovikovSeries R H N →+* A) (hF : F.comp (nonnegSubring R N).subtype = f) :
    F = liftOfIsUnitSectionMonomial hs f hf := by
  have : IsLocalization (sectionSubmonoid R hs) (NovikovSeries R H N) :=
    isLocalization_sectionSubmonoid (R := R) hs
  exact (IsLocalization.lift_unique (M := sectionSubmonoid R hs) (S := NovikovSeries R H N)
    (g := f) _ (j := F) fun a => RingHom.congr_fun hF a).symm

end Localization

section RealSpecialization

/-- Localizing `nonnegSubring R (AddMonoidHom.id ℝ)` at the nonnegative real monomials
`{T^r | r ≥ 0}` recovers `NovikovSeries R ℝ (AddMonoidHom.id ℝ)`. -/
theorem isLocalization_real (R : Type*) [CommRing R] :
    IsLocalization
      (sectionSubmonoid R (N := AddMonoidHom.id ℝ) (s := AddMonoidHom.id ℝ) fun _ => rfl)
      (NovikovSeries R ℝ (AddMonoidHom.id ℝ)) :=
  isLocalization_sectionSubmonoid (R := R) (N := AddMonoidHom.id ℝ) (s := AddMonoidHom.id ℝ)
    fun _ => rfl

/-- Over a field `k`, the universal real Novikov ring `NovikovSeries k ℝ (AddMonoidHom.id ℝ)` is a
field. -/
theorem isField_real (k : Type*) [Field k] :
    IsField (NovikovSeries k ℝ (AddMonoidHom.id ℝ)) :=
  isField_iff.2 ⟨Field.toIsField k, Function.injective_id⟩

/-- Every nonzero series in the universal real Novikov field `Nov(k, ℝ, id)` factors as
`c T^{t₀} (1 - b)` with `c ∈ kˣ` and `b ∈ posIdeal`, and is therefore a unit. -/
theorem exists_single_mul_one_sub_real {k : Type*} [Field k]
    {a : NovikovSeries k ℝ (AddMonoidHom.id ℝ)} (ha : a ≠ 0) :
    ∃ (t₀ : ℝ) (c : kˣ) (b : nonnegSubring k (AddMonoidHom.id ℝ)),
      b ∈ posIdeal k (AddMonoidHom.id ℝ) ∧
        a = single t₀ (c : k) * (1 - (b : NovikovSeries k ℝ (AddMonoidHom.id ℝ))) :=
  exists_single_mul_one_sub_of_injective Function.injective_id ha

end RealSpecialization

section ActionExtension

variable {S R k G ι ι' : Type*}

/-- The extended period homomorphism `E_R(g, r) = E g + r` on `G × ℝ`. -/
def actionPeriod [AddZeroClass G] (E : G →+ ℝ) : G × ℝ →+ ℝ :=
  E.coprod (AddMonoidHom.id ℝ)

@[simp]
theorem actionPeriod_apply [AddZeroClass G] (E : G →+ ℝ) (p : G × ℝ) :
    actionPeriod E p = E p.1 + p.2 := by
  rfl

/-- The canonical real-action section `r ↦ (0, r)` into `G × ℝ`. -/
def actionSection (G : Type*) [AddZeroClass G] : ℝ →+ G × ℝ :=
  AddMonoidHom.inr G ℝ

@[simp]
theorem actionSection_apply [AddZeroClass G] (r : ℝ) : actionSection G r = (0, r) := by
  rfl

/-- `actionSection G` is a section of `actionPeriod E`. -/
theorem actionPeriod_actionSection [AddZeroClass G] (E : G →+ ℝ) (r : ℝ) :
    actionPeriod E (actionSection G r) = r := by
  simp [actionPeriod, actionSection]

/-- The extended degree function `μ_R(g, r) = μ g` on `G × ℝ`. -/
def actionDegree (μ : G → ι) : G × ℝ → ι :=
  μ ∘ Prod.fst

@[simp]
theorem actionDegree_apply (μ : G → ι) (p : G × ℝ) : actionDegree μ p = μ p.1 := by
  rfl

/-- The extended additive degree homomorphism `μ_R(g, r) = μ g` on `G × ℝ`. -/
def actionDegreeHom [AddZeroClass G] [AddMonoid ι] (μ : G →+ ι) : G × ℝ →+ ι :=
  μ.comp (AddMonoidHom.fst G ℝ)

@[simp]
theorem actionDegreeHom_apply [AddZeroClass G] [AddMonoid ι] (μ : G →+ ι) (p : G × ℝ) :
    actionDegreeHom μ p = μ p.1 := by
  rfl

/-- Every real-action monomial `T^r = e^(0, r)` has degree `0` for `actionDegreeHom μ`. -/
theorem sectionMonomial_actionSection_mem_gradeBy_zero [Semiring R] [AddZeroClass G]
    [AddMonoid ι] (E : G →+ ℝ) (μ : G →+ ι) (r : ℝ) :
    sectionMonomial R (actionPeriod E) (actionSection G) r ∈
      gradeBy R (actionPeriod E) (actionDegreeHom μ) 0 := by
  rw [sectionMonomial_def]
  simpa only [actionDegreeHom_apply, actionSection_apply, map_zero] using
    single_mem_gradeBy (R := R) (N := actionPeriod E) (actionDegreeHom μ) (actionSection G r) 1

/-- Every nonnegative real-action monomial `T^r` (`r ≥ 0`) lies in degree `0` of
`nonnegSubring R (actionPeriod E)`. -/
theorem nonnegSectionMonomial_actionSection_mem_nonnegGradeBy_zero [CommRing R] [AddMonoid G]
    [AddMonoid ι] (E : G →+ ℝ) (μ : G →+ ι) {r : ℝ} (hr : 0 ≤ r) :
    nonnegSectionMonomial R (actionPeriod_actionSection E) hr ∈
      nonnegGradeBy R (actionPeriod E) (actionDegreeHom μ) 0 := by
  rw [mem_nonnegGradeBy_iff, coe_nonnegSectionMonomial]
  exact sectionMonomial_actionSection_mem_gradeBy_zero E μ r

/-- Multiplication by `T^r` preserves every homogeneous piece of `NovikovSeries R (G × ℝ) E_R`. -/
theorem sectionMonomial_actionSection_mul_mem_gradeBy_iff [Semiring R] [AddMonoid G]
    [AddMonoid ι] (E : G →+ ℝ) (μ : G →+ ι) (r : ℝ) {i : ι}
    {a : NovikovSeries R (G × ℝ) (actionPeriod E)} :
    sectionMonomial R (actionPeriod E) (actionSection G) r * a ∈
      gradeBy R (actionPeriod E) (actionDegreeHom μ) i ↔
        a ∈ gradeBy R (actionPeriod E) (actionDegreeHom μ) i := by
  constructor
  · intro ha
    have hmul := SetLike.mul_mem_graded (A := gradeBy R (actionPeriod E) (actionDegreeHom μ))
      (sectionMonomial_actionSection_mem_gradeBy_zero E μ (-r)) ha
    simpa only [zero_add, ← mul_assoc, sectionMonomial_neg_mul, one_mul] using hmul
  · intro ha
    have hmul := SetLike.mul_mem_graded (A := gradeBy R (actionPeriod E) (actionDegreeHom μ))
      (sectionMonomial_actionSection_mem_gradeBy_zero E μ r) ha
    simpa only [zero_add] using hmul

/-- The action-weighted Novikov ring `Nov(R, G × ℝ, E_R)` is the localization of its nonnegative
subring at the multiplicative submonoid `{T^r | r ≥ 0}` of nonnegative real-action monomials. -/
theorem isLocalization_actionExtension [CommRing R] [AddCommMonoid G] (E : G →+ ℝ) :
    IsLocalization (sectionSubmonoid R (actionPeriod_actionSection E))
      (NovikovSeries R (G × ℝ) (actionPeriod E)) :=
  isLocalization_sectionSubmonoid (R := R) (actionPeriod_actionSection E)

/-- The canonical inclusion `g ↦ (g, 0)` preserves periods for `actionPeriod E`. -/
theorem exists_period_rescale_actionInl [AddZeroClass G] (E : G →+ ℝ) :
    ∃ c > 0, ∀ g, actionPeriod E (AddMonoidHom.inl G ℝ g) = c * E g :=
  ⟨1, one_pos, fun g => by simp⟩

/-- The canonical ring embedding `Nov(R, G, E) →+* Nov(R, G × ℝ, E_R)` induced by `g ↦ (g, 0)`. -/
def actionEmbedRingHom (R : Type*) [Semiring R] {G : Type*} [AddMonoid G] (E : G →+ ℝ) :
    NovikovSeries R G E →+* NovikovSeries R (G × ℝ) (actionPeriod E) :=
  mapRingHom (RingHom.id R) (AddMonoidHom.inl G ℝ) (exists_period_rescale_actionInl E)

@[simp]
theorem actionEmbedRingHom_single [Semiring R] [AddMonoid G] (E : G →+ ℝ) (g : G) (r : R) :
    actionEmbedRingHom R E (single g r) = single (g, (0 : ℝ)) r := by
  rw [actionEmbedRingHom, mapRingHom_apply, map_single]
  rfl

/-- The restriction of `actionEmbedRingHom` to the nonnegative subrings. -/
def actionEmbedNonneg (R : Type*) [Ring R] {G : Type*} [AddMonoid G] (E : G →+ ℝ) :
    nonnegSubring R E →+* nonnegSubring R (actionPeriod E) :=
  mapNonnegSubring (RingHom.id R) (AddMonoidHom.inl G ℝ) (exists_period_rescale_actionInl E)

@[simp]
theorem coe_actionEmbedNonneg [Ring R] [AddMonoid G] (E : G →+ ℝ) (a : nonnegSubring R E) :
    (actionEmbedNonneg R E a : NovikovSeries R (G × ℝ) (actionPeriod E)) =
      actionEmbedRingHom R E (a : NovikovSeries R G E) := by
  rw [actionEmbedNonneg, actionEmbedRingHom, coe_mapNonnegSubring, mapRingHom_apply]

theorem actionEmbedRingHom_injective [Semiring R] [AddMonoid G] (E : G →+ ℝ) :
    Injective (actionEmbedRingHom R E) := by
  intro a b hab
  exact map_injective (RingHom.id R : R →+ R) (AddMonoidHom.inl G ℝ)
    (exists_period_rescale_actionInl E) injective_id (fun _ _ h => (Prod.mk.inj h).1)
    (by simpa only [actionEmbedRingHom, mapRingHom_apply] using hab)

theorem actionEmbedNonneg_injective [Ring R] [AddMonoid G] (E : G →+ ℝ) :
    Injective (actionEmbedNonneg R E) :=
  mapNonnegSubring_injective _ _ _ injective_id fun _ _ h => (Prod.mk.inj h).1

@[fun_prop]
theorem continuous_actionEmbedRingHom [Ring R] [AddMonoid G] (E : G →+ ℝ) :
    Continuous (actionEmbedRingHom R E) :=
  continuous_mapRingHom _ _ _

@[fun_prop]
theorem continuous_actionEmbedNonneg [Ring R] [AddMonoid G] (E : G →+ ℝ) :
    Continuous (actionEmbedNonneg R E) :=
  continuous_mapNonnegSubring _ _ _

theorem actionEmbedRingHom_mem_gradeBy [Semiring R] [AddMonoid G] (E : G →+ ℝ) {μ : G → ι}
    {i : ι} {a : NovikovSeries R G E} (ha : a ∈ gradeBy R E μ i) :
    actionEmbedRingHom R E a ∈ gradeBy R (actionPeriod E) (actionDegree μ) i := by
  rw [actionEmbedRingHom, mapRingHom_apply]
  exact map_mem_gradeBy (RingHom.id R : R →+ R) (AddMonoidHom.inl G ℝ)
    (exists_period_rescale_actionInl E) (f := μ) (f' := actionDegree μ) (ψ := id)
    (fun _ => rfl) ha

theorem actionEmbedNonneg_mem_nonnegGradeBy [CommRing R] [AddMonoid G] (E : G →+ ℝ) {μ : G → ι}
    {i : ι} {a : nonnegSubring R E} (ha : a ∈ nonnegGradeBy R E μ i) :
    actionEmbedNonneg R E a ∈ nonnegGradeBy R (actionPeriod E) (actionDegree μ) i := by
  rw [actionEmbedNonneg]
  exact mapNonnegSubring_mem_nonnegGradeBy (RingHom.id R) (AddMonoidHom.inl G ℝ)
    (exists_period_rescale_actionInl E) (f := μ) (f' := actionDegree μ) (ψ := id)
    (fun _ => rfl) ha

/-- The period kernel of the action-weighted extension `E_R(g, r) = E g + r` is canonically
isomorphic to `G`, via `g ↦ (g, -E g)`. -/
def actionPeriodKerEquiv [AddGroup G] (E : G →+ ℝ) : G ≃+ (actionPeriod E).ker where
  toFun g := ⟨(g, -E g), by simp⟩
  invFun k := k.1.1
  left_inv _ := rfl
  right_inv k := by
    refine Subtype.ext (Prod.ext rfl ?_)
    have hk : E k.1.1 + k.1.2 = 0 := AddMonoidHom.mem_ker.1 k.2
    linarith
  map_add' g₁ g₂ := by
    refine Subtype.ext (Prod.ext rfl ?_)
    simp [add_comm]

@[simp]
theorem coe_actionPeriodKerEquiv [AddGroup G] (E : G →+ ℝ) (g : G) :
    (actionPeriodKerEquiv E g : G × ℝ) = (g, -E g) := by
  rfl

@[simp]
theorem actionPeriodKerEquiv_symm_apply [AddGroup G] (E : G →+ ℝ) (k : (actionPeriod E).ker) :
    (actionPeriodKerEquiv E).symm k = k.1.1 := by
  rfl

/-- The energy-zero residue ring of the action-weighted extension `nonnegSubring R E_R` is
canonically isomorphic to the full group ring `R[G]`, identifying `g ∈ G` with the period-zero
monomial `e^(g, -E g)`. -/
def actionQuotientPosIdealRingEquiv (R : Type*) [Ring R] {G : Type*} [AddGroup G] (E : G →+ ℝ) :
    (nonnegSubring R (actionPeriod E) ⧸ posIdeal R (actionPeriod E)) ≃+* AddMonoidAlgebra R G :=
  (quotientPosIdealRingEquiv R (actionPeriod E)).trans
    (AddMonoidAlgebra.mapDomainRingEquiv R (actionPeriodKerEquiv E).symm)

/-- The energy-zero residue of the action-weighted extension as an `S`-algebra isomorphism
`Λ₀ ⧸ Λ₊ ≃ₐ[S] R[G]`. -/
def actionQuotientPosIdealAlgEquiv (S R : Type*) [CommSemiring S] [CommRing R] [Algebra S R]
    {G : Type*} [AddGroup G] (E : G →+ ℝ) :
    (nonnegSubring R (actionPeriod E) ⧸ posIdeal R (actionPeriod E)) ≃ₐ[S] AddMonoidAlgebra R G :=
  (quotientPosIdealAlgEquiv S R (actionPeriod E)).trans
    (AddMonoidAlgebra.domCongr S R (actionPeriodKerEquiv E).symm)

@[simp]
theorem coeff_actionQuotientPosIdealRingEquiv_mk [Ring R] [AddGroup G] (E : G →+ ℝ)
    (a : nonnegSubring R (actionPeriod E)) (g : G) :
    (actionQuotientPosIdealRingEquiv R E
        (Ideal.Quotient.mk (posIdeal R (actionPeriod E)) a)).coeff g =
      (a : NovikovSeries R (G × ℝ) (actionPeriod E)).coeff (g, -E g) := by
  rw [actionQuotientPosIdealRingEquiv, RingEquiv.trans_apply, quotientPosIdealRingEquiv_mk,
    AddMonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
  simp

@[simp]
theorem coeff_actionQuotientPosIdealAlgEquiv_mk [CommSemiring S] [CommRing R] [Algebra S R]
    [AddGroup G] (E : G →+ ℝ) (a : nonnegSubring R (actionPeriod E)) (g : G) :
    (actionQuotientPosIdealAlgEquiv S R E
        (Ideal.Quotient.mk (posIdeal R (actionPeriod E)) a)).coeff g =
      (a : NovikovSeries R (G × ℝ) (actionPeriod E)).coeff (g, -E g) := by
  rw [actionQuotientPosIdealAlgEquiv, AlgEquiv.trans_apply, quotientPosIdealAlgEquiv_mk,
    AddMonoidAlgebra.coeff_domCongr]
  simp

/-- Under the action-extension energy-zero residue `Λ₀ → R[G]`, every homogeneous nonnegative series
of degree `i` maps into the degree-`i` piece of `R[G]` for `μ`. -/
theorem actionQuotientPosIdealRingEquiv_mk_mem_gradeBy [CommRing R] [AddGroup G] (E : G →+ ℝ)
    {μ : G → ι} {i : ι} {a : nonnegSubring R (actionPeriod E)}
    (ha : a ∈ nonnegGradeBy R (actionPeriod E) (actionDegree μ) i) :
    actionQuotientPosIdealRingEquiv R E (Ideal.Quotient.mk (posIdeal R (actionPeriod E)) a) ∈
      AddMonoidAlgebra.gradeBy R μ i := by
  rw [AddMonoidAlgebra.mem_gradeBy_iff]
  intro g hg
  have hmem : (g, -E g) ∈ (a : NovikovSeries R (G × ℝ) (actionPeriod E)).support := by
    rw [mem_support]
    simpa only [coeff_actionQuotientPosIdealRingEquiv_mk] using Finsupp.mem_support_iff.1 hg
  exact (mem_gradeBy_iff.1 (mem_nonnegGradeBy_iff.1 ha) hmem)

/-- The period map `actionPeriod E : G × ℝ →+ ℝ` rescales periods by `1` into `(ℝ, id)`. -/
theorem exists_period_rescale_actionPeriod [AddZeroClass G] (E : G →+ ℝ) :
    ∃ c > 0, ∀ p, AddMonoidHom.id ℝ (actionPeriod E p) = c * actionPeriod E p :=
  ⟨1, one_pos, fun p => by simp⟩

/-- The action-field pushforward `φ_* : Nov(R, G × ℝ, E_R) →+* Nov(k, ℝ, id)` induced by a ground
ring homomorphism `ρ : R →+* k` and `φ = E_R : G × ℝ →+ ℝ`. -/
def actionFieldMap [Semiring R] [Semiring k] [AddMonoid G] (ρ : R →+* k) (E : G →+ ℝ) :
    NovikovSeries R (G × ℝ) (actionPeriod E) →+* NovikovSeries k ℝ (AddMonoidHom.id ℝ) :=
  mapRingHom ρ (actionPeriod E) (exists_period_rescale_actionPeriod E)

/-- The restriction of the action-field pushforward to the nonnegative subring `Λ₀`. -/
def actionFieldNonnegMap [Ring R] [Ring k] [AddMonoid G] (ρ : R →+* k) (E : G →+ ℝ) :
    nonnegSubring R (actionPeriod E) →+* NovikovSeries k ℝ (AddMonoidHom.id ℝ) :=
  (actionFieldMap ρ E).comp (nonnegSubring R (actionPeriod E)).subtype

@[simp]
theorem actionFieldNonnegMap_apply [Ring R] [Ring k] [AddMonoid G] (ρ : R →+* k) (E : G →+ ℝ)
    (a : nonnegSubring R (actionPeriod E)) :
    actionFieldNonnegMap ρ E a =
      actionFieldMap ρ E (a : NovikovSeries R (G × ℝ) (actionPeriod E)) := by
  rfl

theorem coeff_actionFieldMap [Semiring R] [Semiring k] [AddMonoid G] (ρ : R →+* k) (E : G →+ ℝ)
    (a : NovikovSeries R (G × ℝ) (actionPeriod E)) (t : ℝ) :
    (actionFieldMap ρ E a).coeff t = ∑ᶠ p ∈ actionPeriod E ⁻¹' {t}, ρ (a.coeff p) := by
  rw [actionFieldMap, mapRingHom_apply, coeff_map]
  rfl

@[fun_prop]
theorem continuous_actionFieldMap [Ring R] [Ring k] [AddMonoid G] (ρ : R →+* k) (E : G →+ ℝ) :
    Continuous (actionFieldMap ρ E) :=
  continuous_mapRingHom ρ (actionPeriod E) (exists_period_rescale_actionPeriod E)

@[fun_prop]
theorem continuous_actionFieldNonnegMap [Ring R] [Ring k] [AddMonoid G] (ρ : R →+* k)
    (E : G →+ ℝ) : Continuous (actionFieldNonnegMap ρ E) :=
  (continuous_actionFieldMap ρ E).comp continuous_subtype_val

/-- The action-field pushforward preserves every period filtration neighbourhood `U_C`. -/
theorem actionFieldMap_mem_periodFiltration [Ring R] [Ring k] [AddMonoid G] (ρ : R →+* k)
    (E : G →+ ℝ) {C : ℝ} {a : NovikovSeries R (G × ℝ) (actionPeriod E)}
    (ha : a ∈ periodFiltration R (actionPeriod E) C) :
    actionFieldMap ρ E a ∈ periodFiltration k (AddMonoidHom.id ℝ) C := by
  rw [actionFieldMap, mapRingHom_apply]
  simpa only [one_mul] using map_mem_periodFiltration (ρ : R →+ k) (actionPeriod E)
    (exists_period_rescale_actionPeriod E) zero_le_one (fun p => by simp) ha

@[simp]
theorem actionFieldMap_sectionMonomial [Semiring R] [Semiring k] [AddMonoid G] (ρ : R →+* k)
    (E : G →+ ℝ) (r : ℝ) :
    actionFieldMap ρ E (sectionMonomial R (actionPeriod E) (actionSection G) r) =
      single r (1 : k) := by
  rw [actionFieldMap, mapRingHom_apply, sectionMonomial_def, map_single, actionPeriod_actionSection]
  simp

/-- The action-field map on `Λ₀` sends every nonnegative monomial `T^r` (`r ≥ 0`) to a unit of
`Nov(k, ℝ, id)`. -/
theorem isUnit_actionFieldNonnegMap_nonnegSectionMonomial [Ring R] [Ring k] [AddMonoid G]
    (ρ : R →+* k) (E : G →+ ℝ) (r : ℝ) (hr : 0 ≤ r) :
    IsUnit (actionFieldNonnegMap ρ E
      (nonnegSectionMonomial R (actionPeriod_actionSection E) hr)) := by
  rw [actionFieldNonnegMap_apply, coe_nonnegSectionMonomial, actionFieldMap_sectionMonomial]
  exact isUnit_single r isUnit_one

/-- The action-field map `actionFieldMap ρ E` on `Λ_loc` is the unique localization extension of its
restriction `actionFieldNonnegMap ρ E` on `Λ₀`. -/
theorem actionFieldMap_eq_lift [CommRing R] [CommRing k] [AddCommMonoid G] (ρ : R →+* k)
    (E : G →+ ℝ) :
    actionFieldMap ρ E =
      liftOfIsUnitSectionMonomial (actionPeriod_actionSection E) (actionFieldNonnegMap ρ E)
        (fun r hr => isUnit_actionFieldNonnegMap_nonnegSectionMonomial ρ E r hr.le) :=
  liftOfIsUnitSectionMonomial_unique _ _ _ _ rfl

/-- If a target degree function `f' : ℝ → ι'` and grading map `ψ : ι → ι'` make the degree square
`f' (E g + r) = ψ (μ g)` commute, then `actionFieldMap ρ E` sends degree-`i` series into
degree-`ψ i` series. -/
theorem actionFieldMap_mem_gradeBy [Semiring R] [Semiring k] [AddMonoid G] (ρ : R →+* k)
    (E : G →+ ℝ) {μ : G → ι} {f' : ℝ → ι'} {ψ : ι → ι'}
    (hdeg : ∀ g r, f' (E g + r) = ψ (μ g)) {i : ι}
    {a : NovikovSeries R (G × ℝ) (actionPeriod E)}
    (ha : a ∈ gradeBy R (actionPeriod E) (actionDegree μ) i) :
    actionFieldMap ρ E a ∈ gradeBy k (AddMonoidHom.id ℝ) f' (ψ i) := by
  rw [actionFieldMap, mapRingHom_apply]
  exact map_mem_gradeBy (ρ : R →+ k) (actionPeriod E) (exists_period_rescale_actionPeriod E)
    (fun p => hdeg p.1 p.2) ha

/-- Whenever `μ : G →+ ι` has infinite range over a nontrivial commutative ring `R`, the algebraic
graded subalgebra `⨁ i, nonnegGradeBy R (actionPeriod E) (actionDegreeHom μ) i` is dense but
proper in `nonnegSubring R (actionPeriod E)`. -/
theorem not_surjective_coeAlgHom_nonnegGradeBy_actionExtension [CommRing R] [Nontrivial R]
    [AddMonoid G] [AddMonoid ι] [DecidableEq ι] (E : G →+ ℝ) {μ : G →+ ι}
    (hμ : (range μ).Infinite) :
    ¬ Surjective (DirectSum.coeAlgHom (S := R)
        (nonnegGradeBy R (actionPeriod E) (actionDegreeHom μ))) := by
  let emb := hμ.natEmbedding
  choose g hg using fun n : ℕ => (emb n).2
  let u : ℕ → G × ℝ := fun n => (g n, max 0 (-E (g n)) + n)
  have hdeg : Injective (actionDegreeHom μ ∘ u) := by
    intro m n hmn
    apply emb.injective
    apply Subtype.ext
    simpa only [Function.comp_apply, actionDegreeHom_apply, u, hg] using hmn
  have hge (n : ℕ) : (n : ℝ) ≤ actionPeriod E (u n) := by
    simp only [actionPeriod_apply, u]
    have h1 : -E (g n) ≤ max 0 (-E (g n)) := le_max_right 0 (-E (g n))
    linarith
  have hN : Tendsto (fun n => actionPeriod E (u n)) atTop atTop :=
    tendsto_atTop_mono hge tendsto_natCast_atTop_atTop
  have hN0 (n : ℕ) : 0 ≤ actionPeriod E (u n) :=
    (Nat.cast_nonneg n).trans (hge n)
  exact not_surjective_coeAlgHom_nonnegGradeBy u hdeg hN hN0

end ActionExtension

end NovikovSeries

end TauCeti
