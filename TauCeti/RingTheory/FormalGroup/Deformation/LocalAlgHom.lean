/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
-- Proof-only: adic topology, multivariate power series equivalences/evaluation, and completeness.
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.MvPowerSeries.Equiv
import TauCeti.RingTheory.MvPowerSeries.Evaluation
import TauCeti.RingTheory.MvPowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.AdicComplete

/-!
# Adic completeness and local homomorphisms of multivariate power series rings

This file provides adic completeness of multivariate power series over a complete local ring and a
bijection classifying local `R`-algebra homomorphisms `R⟦σ⟧ →ₐ[R] A` by images of the variables.

## Main results

* `MvPowerSeries.isAdicComplete_maximalIdeal`: `R⟦σ⟧` is `𝔪`-adically complete when `(R, 𝔪)` is
  a complete local ring and `σ` is finite.
* `MvPowerSeries.algHom_ext_of_X_eq`: two `R`-algebra homs `R⟦σ⟧ →ₐ[R] A` sending each `X i`
  into `maximalIdeal A` agree whenever they agree on every `X i`.
* `MvPowerSeries.exists_algHom_X_eq`: evaluation at `a : σ → maximalIdeal A` defines an
  `R`-algebra hom `R⟦σ⟧ →ₐ[R] A`.
* `MvPowerSeries.algHomEquivMaximalIdeal`: bijection between such homs and `σ → maximalIdeal A`.
* `MvPowerSeries.comp_eq_comp_constantCoeff_iff` and
  `MvPowerSeries.isLocalHom_iff_comp_eq_comp_constantCoeff`: characterizations of the residue-field
  compatibility condition `π ∘ f = ρ ∘ constantCoeff`.
-/

public section

noncomputable section

open IsLocalRing

namespace MvPowerSeries

section AdicComplete

private theorem map_maximalIdeal_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    (maximalIdeal A).map e.toRingHom = maximalIdeal B := by
  ext b
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    exact fun hu ↦ ha (by simpa using hu.map e.symm.toRingHom)
  · intro hb
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    rw [mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
    exact fun hu ↦ hb (by simpa using hu.map e.toRingHom)

private theorem isAdicComplete_maximalIdeal_fin {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] :
    ∀ n : ℕ, IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R)
  | 0 => by
    let e : R ≃+* MvPowerSeries (Fin 0) R := (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
    rw [← map_maximalIdeal_ringEquiv e]
    exact (IsAdicComplete.congr_ringEquiv (maximalIdeal R) e).mpr inferInstance
  | n + 1 => by
    have : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) :=
      isAdicComplete_maximalIdeal_fin n
    let e : PowerSeries (MvPowerSeries (Fin n) R) ≃+* MvPowerSeries (Fin (n + 1)) R :=
      (finSuccEquiv R n).toRingEquiv.symm
    rw [← map_maximalIdeal_ringEquiv e]
    exact (IsAdicComplete.congr_ringEquiv _ e).mpr inferInstance

/-- **Multivariate power series over a complete local ring are complete.** If `(R, 𝔪)` is a local
ring complete for its maximal ideal and `σ` is finite, then `R⟦σ⟧` is complete for its maximal
ideal. -/
instance isAdicComplete_maximalIdeal {σ R : Type*} [Finite σ] [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal (MvPowerSeries σ R)) (MvPowerSeries σ R) := by
  cases nonempty_fintype σ
  have := isAdicComplete_maximalIdeal_fin (R := R) (Fintype.card σ)
  let e : MvPowerSeries (Fin (Fintype.card σ)) R ≃+* MvPowerSeries σ R :=
    (renameEquiv R (Fintype.equivFin σ)).toRingEquiv.symm
  rw [← map_maximalIdeal_ringEquiv e]
  exact (IsAdicComplete.congr_ringEquiv _ e).mpr inferInstance

end AdicComplete

section LocalAlgHom

variable {σ R A k : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Two `R`-algebra homomorphisms from `R⟦σ⟧` (with `σ` finite) to an `𝔪`-adically
Hausdorff local `R`-algebra `A` that agree on the variables `X i` and send them into
`maximalIdeal A` are equal, with no continuity hypothesis needed. -/
theorem algHom_ext_of_X_eq [Finite σ] [IsLocalRing A] [IsHausdorff (maximalIdeal A) A]
    {f g : MvPowerSeries σ R →ₐ[R] A} (hf : ∀ i, f (X i) ∈ maximalIdeal A)
    (hfg : ∀ i, f (X i) = g (X i)) : f = g := by
  ext s
  refine sub_eq_zero.mp (IsHausdorff.haus ‹_› (f s - g s) fun n ↦ ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  set p : MvPolynomial σ R := s.truncTotal n
  have hpoly : f (p : MvPowerSeries σ R) = g (p : MvPowerSeries σ R) := by
    induction p using MvPolynomial.induction_on with
    | C r =>
      simp only [MvPolynomial.coe_C]
      change f (algebraMap R _ r) = g (algebraMap R _ r)
      rw [AlgHom.commutes, AlgHom.commutes]
    | add p q hp hq => simp only [MvPolynomial.coe_add, map_add, hp, hq]
    | mul_X p i hp => simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, hp, hfg]
  have htail_ord : (n : ℕ∞) ≤ (s - (p : MvPowerSeries σ R)).order :=
    nat_le_order fun d hd ↦ by simp [p, coeff_truncTotal _ hd]
  have htail_mem : s - (p : MvPowerSeries σ R) ∈
      (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)) ^ n :=
    mem_pow_span_range_X_iff_le_order.mpr htail_ord
  have hf_mem : f (s - (p : MvPowerSeries σ R)) ∈ maximalIdeal A ^ n := by
    have hle : (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)).map f.toRingHom ≤
        maximalIdeal A :=
      Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr (Set.range_subset_iff.mpr hf))
    have hle_n : ((Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)) ^ n).map f.toRingHom ≤
        maximalIdeal A ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hle n
    exact hle_n (Ideal.mem_map_of_mem f.toRingHom htail_mem)
  have hg_mem : g (s - (p : MvPowerSeries σ R)) ∈ maximalIdeal A ^ n := by
    have hg : ∀ i, g (X i) ∈ maximalIdeal A := fun i ↦ hfg i ▸ hf i
    have hle : (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)).map g.toRingHom ≤
        maximalIdeal A :=
      Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr (Set.range_subset_iff.mpr hg))
    have hle_n : ((Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)) ^ n).map g.toRingHom ≤
        maximalIdeal A ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hle n
    exact hle_n (Ideal.mem_map_of_mem g.toRingHom htail_mem)
  have hsplit : f s - g s =
      f (s - (p : MvPowerSeries σ R)) - g (s - (p : MvPowerSeries σ R)) := by
    rw [map_sub, map_sub, hpoly]
    ring
  rw [hsplit]
  exact Ideal.sub_mem _ hf_mem hg_mem

/-- Given finitely many elements `a : σ → maximalIdeal A` of a complete local `R`-algebra `A`,
evaluation at `a` yields an `R`-algebra homomorphism `f : R⟦σ⟧ →ₐ[R] A` with
`f (X i) = a i`. -/
theorem exists_algHom_X_eq [Finite σ] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (a : σ → maximalIdeal A) :
    ∃ f : MvPowerSeries σ R →ₐ[R] A, ∀ i, f (X i) = a i := by
  let : WithIdeal A := ⟨maximalIdeal A⟩
  let : UniformSpace R := ⊥
  have hI : IsAdic (maximalIdeal A) := rfl
  obtain ⟨_, _⟩ := hI.isAdicComplete_iff.mp ‹_›
  have hcont : Continuous (algebraMap R A) := continuous_of_discreteTopology
  have ha : HasEval (fun i ↦ (a i : A)) := hasEval_of_mem hI fun i ↦ (a i).property
  refine ⟨⟨eval₂Hom hcont ha, fun r ↦ ?_⟩, fun i ↦ ?_⟩
  · change eval₂Hom hcont ha (C r) = algebraMap R A r
    rw [coe_eval₂Hom, eval₂_C]
  · change eval₂Hom hcont ha (X i) = a i
    rw [coe_eval₂Hom, eval₂_X]

/-- For a complete local `R`-algebra `A` and finite `σ`, `R`-algebra homomorphisms
`f : R⟦σ⟧ →ₐ[R] A` sending every `X i` into `maximalIdeal A` are in bijection with
`σ → maximalIdeal A`. -/
@[expose]
def algHomEquivMaximalIdeal [Finite σ] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] :
    {f : MvPowerSeries σ R →ₐ[R] A // ∀ i, f (X i) ∈ maximalIdeal A} ≃
      (σ → maximalIdeal A) where
  toFun f i := ⟨f.val (X i), f.property i⟩
  invFun a := ⟨(exists_algHom_X_eq a).choose,
    fun i ↦ by rw [(exists_algHom_X_eq a).choose_spec i]; exact (a i).property⟩
  left_inv f := Subtype.ext <| algHom_ext_of_X_eq
    (fun i ↦ by
      rw [(exists_algHom_X_eq
        (fun j ↦ (⟨f.val (X j), f.property j⟩ : maximalIdeal A))).choose_spec i]
      exact f.property i)
    (fun i ↦ ((exists_algHom_X_eq
      (fun j ↦ (⟨f.val (X j), f.property j⟩ : maximalIdeal A))).choose_spec i))
  right_inv a := funext fun i ↦ Subtype.ext ((exists_algHom_X_eq a).choose_spec i)

/-- The forward direction of `algHomEquivMaximalIdeal` evaluates at `X i`. -/
@[simp]
theorem algHomEquivMaximalIdeal_apply [Finite σ] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (f : {f : MvPowerSeries σ R →ₐ[R] A // ∀ i, f (X i) ∈ maximalIdeal A}) (i : σ) :
    (algHomEquivMaximalIdeal f i : A) = f.val (X i) :=
  rfl

/-- The inverse of `algHomEquivMaximalIdeal` sends `X i` to `a i`. -/
@[simp]
theorem algHomEquivMaximalIdeal_symm_X [Finite σ] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (a : σ → maximalIdeal A) (i : σ) :
    ((algHomEquivMaximalIdeal (R := R) (A := A)).symm a).val (X i) = a i :=
  (exists_algHom_X_eq a).choose_spec i

/-- For a local homomorphism `π : A →+* k` to a field `k` satisfying
`π ∘ algebraMap R A = ρ`, an `R`-algebra homomorphism `f : R⟦σ⟧ →ₐ[R] A` satisfies
`π ∘ f = ρ ∘ constantCoeff` if and only if it maps every variable `X i` into
`maximalIdeal A`. -/
theorem comp_eq_comp_constantCoeff_iff [Finite σ] [IsLocalRing A] [Field k] (π : A →+* k)
    [IsLocalHom π] (ρ : R →+* k) (hπ : π.comp (algebraMap R A) = ρ)
    (f : MvPowerSeries σ R →ₐ[R] A) :
    π.comp f.toRingHom = ρ.comp constantCoeff ↔ ∀ i, f (X i) ∈ maximalIdeal A := by
  constructor
  · intro h i
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 : π (f (X i)) = 0 := by
      have h' := RingHom.congr_fun h (X i)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h'
      rw [h', constantCoeff_X, map_zero]
    exact (hu.map π).ne_zero h0
  · intro hf
    ext s
    have hsub : s - C (constantCoeff s) ∈
        (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)) :=
      mem_span_range_X_iff.mpr (by simp)
    have hle : (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)).map f.toRingHom ≤
        maximalIdeal A :=
      Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr (Set.range_subset_iff.mpr hf))
    have hmem : f (s - C (constantCoeff s)) ∈ maximalIdeal A :=
      hle (Ideal.mem_map_of_mem f.toRingHom hsub)
    have hker : π (f (s - C (constantCoeff s))) = 0 := by
      rw [mem_maximalIdeal, mem_nonunits_iff] at hmem
      by_contra hne
      exact hmem (IsUnit.of_map π _ (isUnit_iff_ne_zero.mpr hne))
    have hC : π (f (C (constantCoeff s))) = ρ (constantCoeff s) := by
      change π (f (algebraMap R (MvPowerSeries σ R) (constantCoeff s))) = ρ (constantCoeff s)
      rw [AlgHom.commutes]
      exact RingHom.congr_fun hπ (constantCoeff s)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← sub_eq_zero, ← hC, ← map_sub π, ← map_sub f, hker]

/-- When `R` is local and `ρ : R →+* k` is a local homomorphism, an `R`-algebra homomorphism
`f : R⟦σ⟧ →ₐ[R] A` is a local homomorphism if and only if `π ∘ f = ρ ∘ constantCoeff`. -/
theorem isLocalHom_iff_comp_eq_comp_constantCoeff [Finite σ] [IsLocalRing R] [IsLocalRing A]
    [Field k] (π : A →+* k) [IsLocalHom π] (ρ : R →+* k) [IsLocalHom ρ]
    (hπ : π.comp (algebraMap R A) = ρ) (f : MvPowerSeries σ R →ₐ[R] A) :
    IsLocalHom f.toRingHom ↔ π.comp f.toRingHom = ρ.comp constantCoeff := by
  constructor
  · intro _
    rw [comp_eq_comp_constantCoeff_iff π ρ hπ f]
    intro i
    have hXi : (X i : MvPowerSeries σ R) ∈ maximalIdeal (MvPowerSeries σ R) := by
      rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_X]
      exact not_isUnit_zero
    exact map_nonunit f.toRingHom _ ((mem_maximalIdeal _).mp hXi)
  · intro hf
    refine ⟨fun s hu ↦ ?_⟩
    rw [isUnit_iff_constantCoeff]
    have hπs : IsUnit (π (f s)) := hu.map π
    have hπ' : π (f s) = ρ (constantCoeff s) := RingHom.congr_fun hf s
    rw [hπ'] at hπs
    exact IsUnit.of_map ρ _ hπs

end LocalAlgHom

end MvPowerSeries
