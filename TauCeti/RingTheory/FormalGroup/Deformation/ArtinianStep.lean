/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Deformation.QuotientStep
public import TauCeti.RingTheory.FormalGroup.Height.Basic
-- Proof-only: residue fields, Noetherian local power series, and coordinate lifts.
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Height
import TauCeti.RingTheory.MvPowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.Coordinate.Lifting

/-!
# Artinian quotient lifting steps for the Lubin–Tate universal deformation theorem

This file develops the artinian quotient rings `A ⧸ 𝔪 ^ r` and the inductive existence and
uniqueness steps across square-zero extensions `A ⧸ 𝔪 ^ (r + 1) →+* A ⧸ 𝔪 ^ r` used in
`TauCeti.RingTheory.FormalGroup.Deformation.Universal`.

## Main results

* `FormalGroup.quotient_step_exists`: lifts an `R`-algebra homomorphism and its induced deformation
  from `A ⧸ 𝔪 ^ r` to `A ⧸ 𝔪 ^ (r + 1)`.
* `FormalGroup.quotient_step_unique`: two lifts to `A ⧸ 𝔪 ^ (r + 1)` agreeing modulo `𝔪 ^ r`
  and inducing the same deformation are equal.
-/

public section

noncomputable section

open IsLocalRing MvPowerSeries TauCeti

namespace FormalGroup

section QuotientRings

/-- Quotient ring `A ⧸ (maximalIdeal A) ^ r`. -/
abbrev QuotRing (A : Type*) [CommRing A] [IsLocalRing A] (r : ℕ) : Type _ :=
  A ⧸ maximalIdeal A ^ r

/-- Canonical projection `A →+* QuotRing A r`. -/
abbrev quotProj (A : Type*) [CommRing A] [IsLocalRing A] (r : ℕ) : A →+* QuotRing A r :=
  Ideal.Quotient.mk (maximalIdeal A ^ r)

/-- Step transition projection `QuotRing A (r + 1) →+* QuotRing A r`. -/
abbrev quotStep (A : Type*) [CommRing A] [IsLocalRing A] (r : ℕ) :
    QuotRing A (r + 1) →+* QuotRing A r :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right r.le_succ)

/-- Residue homomorphism `QuotRing A r →+* k` induced by a local map `π : A →+* k` when `1 ≤ r`. -/
abbrev quotRes {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] (r : ℕ) (hr : 1 ≤ r) : QuotRing A r →+* k :=
  Ideal.Quotient.lift (maximalIdeal A ^ r) π fun _ ha ↦
    RingHom.mem_ker.mp ((ker_eq_maximalIdeal_of_field π).ge (Ideal.pow_le_self (by omega) ha))

/-- Composing `quotStep A r` with `quotProj A (r + 1)` gives `quotProj A r`. -/
theorem quotStep_comp_quotProj {A : Type*} [CommRing A] [IsLocalRing A] (r : ℕ) :
    (quotStep A r).comp (quotProj A (r + 1)) = quotProj A r := by
  ext a; rfl

/-- Composing `quotRes π r hr` with `quotProj A r` recovers `π`. -/
theorem quotRes_comp_quotProj {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] (r : ℕ) (hr : 1 ≤ r) :
    (quotRes π r hr).comp (quotProj A r) = π := by
  ext a; rfl

/-- Composing `quotRes π r hr` with `quotStep A r` equals `quotRes π (r + 1)`. -/
theorem quotRes_comp_quotStep {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] (r : ℕ) (hr : 1 ≤ r) :
    (quotRes π r hr).comp (quotStep A r) = quotRes π (r + 1) (by omega) := by
  ext a; rfl

/-- `QuotRing A r` is nontrivial whenever `1 ≤ r`. -/
theorem quotRing_nontrivial {A : Type*} [CommRing A] [IsLocalRing A] (r : ℕ) (hr : 1 ≤ r) :
    Nontrivial (QuotRing A r) :=
  Ideal.Quotient.nontrivial_iff.mpr fun htop ↦
    (maximalIdeal.isMaximal A).ne_top (eq_top_iff.mpr (htop ▸ Ideal.pow_le_self (by omega)))

/-- `quotRes π r hr` is a local homomorphism when `QuotRing A r` is nontrivial. -/
theorem quotRes_isLocalHom {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] (r : ℕ) (hr : 1 ≤ r) [Nontrivial (QuotRing A r)] :
    IsLocalHom (quotRes π r hr) := by
  refine ⟨fun b hb ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha : IsUnit (π a) := by simpa using hb
  exact (IsUnit.of_map π a ha).map (quotProj A r)

/-- The maximal ideal of `QuotRing A r` is the image of `maximalIdeal A`. -/
theorem quotRing_maximalIdeal {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] (r : ℕ) (hr : 1 ≤ r) [IsLocalRing (QuotRing A r)] :
    maximalIdeal (QuotRing A r) = (maximalIdeal A).map (quotProj A r) := by
  have : IsLocalHom (quotRes π r hr) := quotRes_isLocalHom π r hr
  ext b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← ker_eq_maximalIdeal_of_field (quotRes π r hr), RingHom.mem_ker, Ideal.Quotient.lift_mk]
  constructor
  · intro ha0
    exact Ideal.mem_map_of_mem (quotProj A r) ((ker_eq_maximalIdeal_of_field π).le ha0)
  · intro ha0
    obtain ⟨c, hc, hca⟩ :=
      (Ideal.mem_map_iff_of_surjective (quotProj A r) Ideal.Quotient.mk_surjective).mp ha0
    have hsub : a - c ∈ maximalIdeal A ^ r := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hca, sub_self]
    exact (ker_eq_maximalIdeal_of_field π).ge
      (add_sub_cancel c a ▸ (maximalIdeal A).add_mem hc (Ideal.pow_le_self (by omega) hsub))

/-- The `r`-th power of the maximal ideal of `QuotRing A r` vanishes. -/
theorem quotRing_maximalIdeal_pow {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] (r : ℕ) (hr : 1 ≤ r) [IsLocalRing (QuotRing A r)] :
    maximalIdeal (QuotRing A r) ^ r = ⊥ := by
  rw [quotRing_maximalIdeal π r hr, ← Ideal.map_pow, eq_bot_iff]
  rintro b hb
  obtain ⟨a, ha, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (quotProj A r) Ideal.Quotient.mk_surjective).mp hb
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  exact ha

/-- The kernel of `quotStep A r` is the image of `(maximalIdeal A) ^ r`. -/
theorem quotStep_ker {A : Type*} [CommRing A] [IsLocalRing A] (r : ℕ) :
    RingHom.ker (quotStep A r) = (maximalIdeal A ^ r).map (quotProj A (r + 1)) := by
  ext b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · exact fun ha0 ↦ Ideal.mem_map_of_mem (quotProj A (r + 1)) ha0
  · intro ha0
    obtain ⟨c, hc, hca⟩ :=
      (Ideal.mem_map_iff_of_surjective (quotProj A (r + 1)) Ideal.Quotient.mk_surjective).mp ha0
    have hsub : a - c ∈ maximalIdeal A ^ (r + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hca, sub_self]
    exact add_sub_cancel c a ▸ (maximalIdeal A ^ r).add_mem hc
      (Ideal.pow_le_pow_right r.le_succ hsub)

/-- `(maximalIdeal A).map (quotProj A (r + 1)) * ker (quotStep A r) = ⊥`. -/
theorem quotStep_mul_ker {A : Type*} [CommRing A] [IsLocalRing A] (r : ℕ) :
    (maximalIdeal A).map (quotProj A (r + 1)) * RingHom.ker (quotStep A r) = ⊥ := by
  rw [quotStep_ker r, ← Ideal.map_mul, ← pow_succ', eq_bot_iff]
  rintro b hb
  obtain ⟨a, ha, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (quotProj A (r + 1)) Ideal.Quotient.mk_surjective).mp hb
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  exact ha

/-- `ker (quotStep A r) ^ 2 = ⊥` when `1 ≤ r`. -/
theorem quotStep_ker_sq {A : Type*} [CommRing A] [IsLocalRing A] (r : ℕ) (hr : 1 ≤ r) :
    RingHom.ker (quotStep A r) ^ 2 = ⊥ := by
  rw [quotStep_ker r, ← Ideal.map_pow, eq_bot_iff]
  rintro b hb
  obtain ⟨a, ha, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (quotProj A (r + 1)) Ideal.Quotient.mk_surjective).mp hb
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  rw [← pow_mul] at ha
  exact Ideal.pow_le_pow_right (by omega : r + 1 ≤ r * 2) ha

end QuotientRings

section StepHelpers

private lemma homDefect_𝔾ₐ_sum {R ι : Type*} [CommRing R] (F : FormalGroup R)
    (s : Finset ι) (g : ι → PowerSeries R) :
    F.homDefect 𝔾ₐ (∑ i ∈ s, g i) = ∑ i ∈ s, F.homDefect 𝔾ₐ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FormalGroup.homDefect_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, FormalGroup.homDefect_𝔾ₐ_add, ih, Finset.sum_insert hi]

private lemma sum_mkJ_mem {σ A B B' : Type*} [Fintype σ] [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A] (q : A →+* B) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (δ : σ → RingHom.ker t) (f : σ → MvPowerSeries (Fin 2) (ResidueField A))
    (d : Fin 2 →₀ ℕ) :
    letI := jModule q t hker
    coeff d (∑ j : σ, mkJ (δ j) (f j)) ∈ RingHom.ker t := by
  let := jModule q t hker
  rw [map_sum]
  exact Ideal.sum_mem _ fun j _ ↦ coeff_mkJ_mem (δ j) (f j) d

private def quotPB (A : Type*) [CommRing A] [IsLocalRing A] (r : ℕ) :
    QuotRing A (r + 1) →+* ResidueField A :=
  Ideal.Quotient.lift (maximalIdeal A ^ (r + 1)) (residue A) fun _ ha ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_le_self r.succ_ne_zero ha)

private lemma quotPB_comp_quotProj (A : Type*) [CommRing A] [IsLocalRing A] (r : ℕ) :
    (quotPB A r).comp (quotProj A (r + 1)) = residue A := by
  ext a; rfl

private lemma lift_comp_quotPB {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] (r : ℕ) :
    (ResidueField.lift π).comp (quotPB A r) = quotRes π (r + 1) (Nat.succ_pos r) := by
  ext a
  change ResidueField.lift π (residue A a) = π a
  rw [← RingHom.comp_apply (ResidueField.lift π) (residue A), ResidueField.lift_comp_residue]

private lemma quotPB_isLocalHom (A : Type*) [CommRing A] [IsLocalRing A] (r : ℕ)
    [Nontrivial (QuotRing A (r + 1))] : IsLocalHom (quotPB A r) where
  map_nonunit b hb := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    have ha : IsUnit (residue A a) := by
      change IsUnit ((quotPB A r).comp (quotProj A (r + 1)) a) at hb
      rwa [quotPB_comp_quotProj] at hb
    exact (IsUnit.of_map (residue A) a ha).map (quotProj A (r + 1))

private lemma ker_quotPB_mul_ker_quotStep {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] (r : ℕ) [IsLocalRing (QuotRing A (r + 1))] :
    RingHom.ker (quotPB A r) * RingHom.ker (quotStep A r) = ⊥ := by
  have := quotPB_isLocalHom A r
  rw [ker_eq_maximalIdeal_of_field (quotPB A r),
    quotRing_maximalIdeal π (r + 1) (Nat.succ_pos r)]
  exact quotStep_mul_ker r

private lemma ker_quotStep_le_quotRes {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] {r : ℕ} (hr : 1 ≤ r) :
    RingHom.ker (quotStep A r) ≤ RingHom.ker (quotRes π (r + 1) (by omega)) := fun b hb ↦ by
  rw [RingHom.mem_ker, ← quotRes_comp_quotStep π r hr, RingHom.comp_apply,
    RingHom.mem_ker.mp hb, map_zero]

private lemma quotRes_comp_algebraMap {R A k : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] [Field k] (π : A →+* k) [IsLocalHom π] (ρ : R →+* k)
    (hπ : π.comp (algebraMap R A) = ρ) (r : ℕ) (hr : 1 ≤ r) :
    (quotRes π r hr).comp (algebraMap R (QuotRing A r)) = ρ := by
  ext x
  change quotRes π r hr (quotProj A r (algebraMap R A x)) = ρ x
  rw [← RingHom.comp_apply (quotRes π r hr) (quotProj A r), quotRes_comp_quotProj,
    ← RingHom.comp_apply π (algebraMap R A), hπ]

private def resBasisCocycle {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] {h : ℕ} (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R))
    (n : ℕ) : MvPowerSeries (Fin 2) (ResidueField A) :=
  let ρA : R →+* ResidueField A := (residue A).comp (algebraMap R A)
  if hn : 0 < n ∧ n < h then
    derivCocycle Γ ρA ((Γ.map constantCoeff).map ρA) ⟨n - 1, by omega⟩
  else 0

private lemma resBasisCocycle_eq {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] {h : ℕ} (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R))
    {n : ℕ} (hn₀ : 0 < n) (hnh : n < h) :
    resBasisCocycle (A := A) Γ n =
      derivCocycle Γ ((residue A).comp (algebraMap R A))
        ((Γ.map constantCoeff).map ((residue A).comp (algebraMap R A))) ⟨n - 1, by omega⟩ := by
  simp [resBasisCocycle, hn₀, hnh]

private lemma resBasisCocycle_ord {p h : ℕ} {R k A : Type*} [CommRing R] [Field k]
    [CommRing A] [Algebra R A] [IsLocalRing A] {ρ : R →+* k} {F₀ : FormalGroup k}
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R))
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ)
    (n : ℕ) (hn₀ : 0 < n) (hnh : n < h) :
    ((p ^ n : ℕ) : ℕ∞) ≤ (resBasisCocycle (A := A) Γ n).order := by
  let ι : ResidueField A →+* k := ResidueField.lift π
  let ρA : R →+* ResidueField A := (residue A).comp (algebraMap R A)
  have hιρA : ι.comp ρA = ρ := by
    dsimp only [ρA, ι]
    rw [← RingHom.comp_assoc, ResidueField.lift_comp_residue, hπ]
  have hF_res : ((Γ.map constantCoeff).map ρA).map ι = F₀ := by
    rw [FormalGroup.map_comp, hιρA, FormalGroup.map_comp, hΓ]
  rw [resBasisCocycle_eq Γ hn₀ hnh, ← order_eq_of_injective_map ι.injective,
    derivCocycle_map_residue, hF_res]
  have hord := hΓord ⟨n - 1, by omega⟩
  have hidx : (⟨n - 1, by omega⟩ : Fin (h - 1)).val + 1 = n := Nat.sub_add_cancel hn₀
  rw [hidx] at hord
  rwa [hιρA]

private lemma resBasisCocycle_comp {p h : ℕ} {R k A : Type*} [CommRing R] [Field k]
    [CommRing A] [Algebra R A] [IsLocalRing A] {ρ : R →+* k} {F₀ : FormalGroup k}
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R))
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ)
    (n : ℕ) (hn₀ : 0 < n) (hnh : n < h) :
    homogeneousComponent (p ^ n) (resBasisCocycle (A := A) Γ n) =
      ↑(TauCeti.lazardCocycle (p ^ n) (ResidueField A)) := by
  let ι : ResidueField A →+* k := ResidueField.lift π
  let ρA : R →+* ResidueField A := (residue A).comp (algebraMap R A)
  have hιρA : ι.comp ρA = ρ := by
    dsimp only [ρA, ι]
    rw [← RingHom.comp_assoc, ResidueField.lift_comp_residue, hπ]
  have hF_res : ((Γ.map constantCoeff).map ρA).map ι = F₀ := by
    rw [FormalGroup.map_comp, hιρA, FormalGroup.map_comp, hΓ]
  rw [resBasisCocycle_eq Γ hn₀ hnh]
  refine homogeneousComponent_eq_of_injective_map ι.injective (p ^ n) _ _ ?_
  rw [derivCocycle_map_residue, hF_res, hιρA, TauCeti.map_lazardCocycle]
  have hcomp := hΓcomp ⟨n - 1, by omega⟩
  have hidx : (⟨n - 1, by omega⟩ : Fin (h - 1)).val + 1 = n := Nat.sub_add_cancel hn₀
  rwa [hidx] at hcomp

private lemma sum_resBasisCocycle {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] {h : ℕ} (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R))
    (c : ℕ → ResidueField A) :
    ∑ n ∈ Finset.Ioo 0 h, c n • resBasisCocycle (A := A) Γ n =
      ∑ i : Fin (h - 1), c (i.val + 1) •
        derivCocycle Γ ((residue A).comp (algebraMap R A))
          ((Γ.map constantCoeff).map ((residue A).comp (algebraMap R A))) i := by
  symm
  refine Finset.sum_bij (fun (i : Fin (h - 1)) _ ↦ i.val + 1)
    (fun i _ ↦ Finset.mem_Ioo.mpr ⟨by omega, by omega⟩)
    (fun _ _ _ _ hi ↦ Fin.ext (by omega))
    (fun n hn ↦ ⟨⟨n - 1, by rw [Finset.mem_Ioo] at hn; omega⟩, Finset.mem_univ _, by
      dsimp only; rw [Finset.mem_Ioo] at hn; omega⟩)
    (fun i _ ↦ by rw [resBasisCocycle_eq Γ (by omega) (by omega)]; simp)

private lemma map_quotPB_eq {h : ℕ} {R k A : Type*} [CommRing R] [Field k] [CommRing A]
    [Algebra R A] [IsLocalRing A] {ρ : R →+* k}
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R))
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) (r : ℕ)
    (f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
    (hf : (quotRes π (r + 1) (Nat.succ_pos r)).comp f.toRingHom = ρ.comp constantCoeff) :
    (Γ.map f.toRingHom).map (quotPB A r) =
      (Γ.map constantCoeff).map ((residue A).comp (algebraMap R A)) := by
  let ι : ResidueField A →+* k := ResidueField.lift π
  let ρA : R →+* ResidueField A := (residue A).comp (algebraMap R A)
  have hιρA : ι.comp ρA = ρ := by
    dsimp only [ρA, ι]
    rw [← RingHom.comp_assoc, ResidueField.lift_comp_residue, hπ]
  rw [FormalGroup.map_comp]
  have hpBf : (quotPB A r).comp f.toRingHom = ρA.comp constantCoeff := by
    ext s
    apply ι.injective
    calc ι (quotPB A r (f s)) = quotRes π (r + 1) (Nat.succ_pos r) (f s) :=
          RingHom.congr_fun (lift_comp_quotPB π r) (f s)
      _ = ρ (constantCoeff s) := RingHom.congr_fun hf s
      _ = ι (ρA (constantCoeff s)) := (RingHom.congr_fun hιρA (constantCoeff s)).symm
  rw [hpBf, ← FormalGroup.map_comp]

private lemma lift_algHom_along_quotStep {h : ℕ} {R k A : Type*} [CommRing R] [Field k] [CommRing A]
    [Algebra R A] [IsLocalRing A] (ρ : R →+* k) (π : A →+* k) [IsLocalHom π]
    (hπ : π.comp (algebraMap R A) = ρ) {r : ℕ} (hr : 1 ≤ r)
    (f' : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A r)
    (hf' : (quotRes π r hr).comp f'.toRingHom = ρ.comp constantCoeff)
    (δ : Fin (h - 1) → RingHom.ker (quotStep A r))
    {x₀ : Fin (h - 1) → QuotRing A (r + 1)} (hx₀ : ∀ i, quotStep A r (x₀ i) = f' (X i)) :
    ∃ (f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1)),
      (∀ i, f (X i) = x₀ i + (δ i).val) ∧
      ((quotRes π (r + 1) (by omega)).comp f.toRingHom = ρ.comp constantCoeff) ∧
      ((quotStep A r).comp f.toRingHom = f'.toRingHom) := by
  let B := QuotRing A (r + 1)
  let B' := QuotRing A r
  let πB := quotRes π (r + 1) (by omega)
  let πB' := quotRes π r hr
  have : Nontrivial B := quotRing_nontrivial (r + 1) (by omega)
  have : Nontrivial B' := quotRing_nontrivial r hr
  have : IsLocalRing B :=
    IsLocalRing.of_surjective' (quotProj A (r + 1)) Ideal.Quotient.mk_surjective
  have : IsLocalRing B' := IsLocalRing.of_surjective' (quotProj A r) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal B) B :=
    isAdicComplete_of_pow_eq_bot (quotRing_maximalIdeal_pow π (r + 1) (by omega))
  have : IsAdicComplete (maximalIdeal B') B' :=
    isAdicComplete_of_pow_eq_bot (quotRing_maximalIdeal_pow π r hr)
  have : IsLocalHom πB := quotRes_isLocalHom π (r + 1) (by omega)
  have : IsLocalHom πB' := quotRes_isLocalHom π r hr
  have hx' : ∀ i : Fin (h - 1), f' (X i) ∈ maximalIdeal B' :=
    (comp_eq_comp_constantCoeff_iff πB' ρ (quotRes_comp_algebraMap π ρ hπ r hr) f').mp hf'
  have hx₀_mem : ∀ i, x₀ i + (δ i).val ∈ maximalIdeal B := fun i ↦ by
    rw [← ker_eq_maximalIdeal_of_field πB, RingHom.mem_ker, map_add,
      RingHom.mem_ker.mp (ker_quotStep_le_quotRes π hr (δ i).property), _root_.add_zero]
    dsimp only [πB]
    rw [← quotRes_comp_quotStep π r hr, RingHom.comp_apply, hx₀ i]
    exact (ker_eq_maximalIdeal_of_field πB').ge (hx' i)
  obtain ⟨f, hfX⟩ := exists_algHom_X_eq (R := R) (fun i ↦ ⟨x₀ i + (δ i).val, hx₀_mem i⟩)
  have hf_res : πB.comp f.toRingHom = ρ.comp constantCoeff :=
    (comp_eq_comp_constantCoeff_iff πB ρ
      (quotRes_comp_algebraMap π ρ hπ (r + 1) (by omega)) f).mpr
      fun i ↦ by rw [hfX i]; exact hx₀_mem i
  let f_B' : MvPowerSeries (Fin (h - 1)) R →ₐ[R] B' :=
    { toRingHom := (quotStep A r).comp f.toRingHom
      commutes' := fun c ↦ by
        change quotStep A r (f (algebraMap R _ c)) = algebraMap R B' c
        rw [AlgHom.commutes]
        change quotStep A r (quotProj A (r + 1) (algebraMap R A c)) =
          quotProj A r (algebraMap R A c)
        rw [← RingHom.comp_apply, quotStep_comp_quotProj] }
  have halg : f_B' = f' := algHom_ext_of_X_eq (fun i ↦ by
    change quotStep A r (f (X i)) ∈ maximalIdeal B'
    rw [hfX i, map_add, RingHom.mem_ker.mp (δ i).property, _root_.add_zero, hx₀ i]
    exact hx' i) (fun i ↦ by
    change quotStep A r (f (X i)) = f' (X i)
    rw [hfX i, map_add, RingHom.mem_ker.mp (δ i).property, _root_.add_zero, hx₀ i])
  exact ⟨f, fun i ↦ hfX i, hf_res, congrArg AlgHom.toRingHom halg⟩

end StepHelpers

section QuotientStep

private lemma quotient_step_exists_coord_solve
    {h : ℕ} {R k A : Type*} [CommRing R] [Field k] [CommRing A] [Algebra R A] [IsLocalRing A]
    (π : A →+* k) [IsLocalHom π]
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    {r : ℕ} (hr : 1 ≤ r)
    (f₀ f₁ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
    (htf_eq : (quotStep A r).comp f₀.toRingHom = (quotStep A r).comp f₁.toRingHom)
    (G₁ : FormalGroup (QuotRing A (r + 1))) (φ₀ : FormalCoordinate (QuotRing A (r + 1)))
    (hφ₀_map : FormalCoordinate.map (quotRes π (r + 1) (by omega)) φ₀ = 1)
    (g : PowerSeries (QuotRing A (r + 1))) (hg₀ : PowerSeries.constantCoeff g = 0)
    (hg_mem : ∀ n, PowerSeries.coeff n g ∈ RingHom.ker (quotStep A r))
    (hΨ_eq :
      PowerSeries.subst (Γ.map f₀.toRingHom).toPowerSeries
          (Γ.map f₀.toRingHom).invariantDifferential *
          (G₁.toPowerSeries - (Γ.map f₀.toRingHom).toPowerSeries) =
        PowerSeries.subst (Γ.map f₀.toRingHom).toPowerSeries
            (Γ.map f₀.toRingHom).invariantDifferential *
            ((Γ.map f₁.toRingHom).toPowerSeries - (Γ.map f₀.toRingHom).toPowerSeries) +
          (Γ.map f₀.toRingHom).homDefect 𝔾ₐ g) :
    ∃ ψ : FormalCoordinate (QuotRing A (r + 1)),
      FormalCoordinate.map (quotRes π (r + 1) (by omega)) (φ₀ * ψ) = 1 ∧
      (φ₀ * ψ) • (Γ.map f₁.toRingHom) = φ₀ • G₁ := by
  let B := QuotRing A (r + 1)
  let t := quotStep A r
  let πB := quotRes π (r + 1) (by omega)
  have hJ_sq : RingHom.ker t ^ 2 = ⊥ := quotStep_ker_sq r hr
  set F_B := Γ.map f₀.toRingHom
  set ω₀ := PowerSeries.subst F_B.toPowerSeries F_B.invariantDifferential
  set h_coord : PowerSeries B :=
    MvPowerSeries.subst ![0, PowerSeries.X] (pderiv 0 F_B.toPowerSeries) * g
  have hh₀ : PowerSeries.constantCoeff h_coord = 0 := by simp [h_coord, hg₀]
  have hh_mem : ∀ n, PowerSeries.coeff n h_coord ∈ RingHom.ker t := fun n ↦ by
    rw [PowerSeries.coeff_mul]
    exact Ideal.sum_mem _ fun p _ ↦ (RingHom.ker t).mul_mem_left _ (hg_mem p.2)
  set ψ := FormalCoordinate.ofSquareZero hJ_sq h_coord hh₀ hh_mem
  have hψ_map : FormalCoordinate.map πB ψ = 1 := by
    ext n
    rw [FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_one,
      FormalCoordinate.toPowerSeries_ofSquareZero, map_add, PowerSeries.map_X,
      map_add (PowerSeries.coeff n), PowerSeries.coeff_map,
      RingHom.mem_ker.mp (ker_quotStep_le_quotRes π hr (hh_mem n)), _root_.add_zero]
  have hψ_cob : ω₀ * ((ψ • F_B).toPowerSeries - F_B.toPowerSeries) = F_B.homDefect 𝔾ₐ g := by
    have hωh : F_B.invariantDifferential * h_coord = g := by
      rw [← mul_assoc, F_B.invariantDifferential_mul_subst_pderiv, one_mul]
    simpa [ω₀, ψ, hωh] using
      invariantDifferential_mul_smul_sub_eq_homDefect_𝔾ₐ F_B hJ_sq h_coord hh₀ hh_mem
  have hsmul_inv : (ψ • (Γ.map f₁.toRingHom)).toPowerSeries - (ψ • F_B).toPowerSeries =
      (Γ.map f₁.toRingHom).toPowerSeries - F_B.toPowerSeries := by
    refine smul_sub_smul_eq_of_mul_eq_bot ψ (Γ.map f₁.toRingHom) F_B
      (by rwa [← sq]) hJ_sq (fun n ↦ by simpa [ψ] using hh_mem n) fun d ↦ ?_
    rw [RingHom.mem_ker, map_sub, map_sub t, ← coeff_map, ← coeff_map, ← map_toPowerSeries,
      ← map_toPowerSeries, FormalGroup.map_comp, FormalGroup.map_comp, ← htf_eq, sub_self]
  have hω_eq : ω₀ * ((ψ • (Γ.map f₁.toRingHom)).toPowerSeries - F_B.toPowerSeries) =
      ω₀ * (G₁.toPowerSeries - F_B.toPowerSeries) := by
    have hsplit : (ψ • (Γ.map f₁.toRingHom)).toPowerSeries - F_B.toPowerSeries =
        ((Γ.map f₁.toRingHom).toPowerSeries - F_B.toPowerSeries) +
          ((ψ • F_B).toPowerSeries - F_B.toPowerSeries) := by
      rw [← hsmul_inv]; ring
    rw [hsplit, mul_add, hψ_cob, ← hΨ_eq]
  have hω_unit : IsUnit ω₀ :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by
      rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero F_B.zero_constantCoeff,
        F_B.constantCoeff_invariantDifferential, map_one]
      exact isUnit_one)
  have hG₁_eq : ψ • (Γ.map f₁.toRingHom) = G₁ := by
    ext d
    exact congrArg (coeff d) (sub_left_inj.mp (hω_unit.mul_left_cancel hω_eq))
  refine ⟨ψ, by rw [map_mul, hφ₀_map, hψ_map, mul_one], ?_⟩
  rw [mul_smul, hG₁_eq]

private lemma quotient_step_exists_projL
    {p h : ℕ} [Fact p.Prime] {R k A : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    [CommRing A] [Algebra R A] [IsLocalRing A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ)
    (r : ℕ) (f₀ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
    (hf₀ : (quotRes π (r + 1) (Nat.succ_pos r)).comp f₀.toRingHom = ρ.comp constantCoeff)
    (Ψ : MvPowerSeries (Fin 2) (QuotRing A (r + 1)))
    (hΨ_symm : (Γ.map f₀.toRingHom).IsSymmetricCocycle Ψ)
    (hΨ_mem : ∀ d, coeff d Ψ ∈ RingHom.ker (quotStep A r))
    (hΨ₀ : constantCoeff Ψ = 0) :
    let := jModule (quotProj A (r + 1)) (quotStep A r) (quotStep_mul_ker r)
    ∀ l : RingHom.ker (quotStep A r) →ₗ[ResidueField A] ResidueField A,
    ∃ (c : ℕ → ResidueField A) (g : PowerSeries (ResidueField A)),
      PowerSeries.constantCoeff g = 0 ∧
      projL l Ψ hΨ_mem =
        ∑ n ∈ Finset.Ioo 0 h, c n • resBasisCocycle (A := A) Γ n +
          ((Γ.map constantCoeff).map ((residue A).comp (algebraMap R A))).homDefect 𝔾ₐ g := by
  intro _inst l
  let ι : ResidueField A →+* k := ResidueField.lift π
  let ρA : R →+* ResidueField A := (residue A).comp (algebraMap R A)
  have hιρA : ι.comp ρA = ρ := by
    dsimp only [ρA, ι]
    rw [← RingHom.comp_assoc, ResidueField.lift_comp_residue, hπ]
  let F_res : FormalGroup (ResidueField A) := (Γ.map constantCoeff).map ρA
  have hF_res_ht : F_res.height p = h := by
    rw [← F_res.height_map ι, FormalGroup.map_comp, hιρA, FormalGroup.map_comp, hΓ, hF₀]
  have hK_char : CharP (ResidueField A) p := ι.charP ι.injective p
  have hF_ord : ((p ^ h : ℕ) : ℕ∞) ≤ (F_res.nsmulSeries p).order :=
    (F_res.height_eq_natCast_iff.mp hF_res_ht).ge
  have hF_unit : IsUnit (PowerSeries.coeff (p ^ h) (F_res.nsmulSeries p)) :=
    IsUnit.mk0 _ (F_res.coeff_nsmulSeries_ne_zero_of_height_eq hF_res_ht)
  have hpr := isSymmetricCocycle_projL (quotProj A (r + 1)) Ideal.Quotient.mk_surjective
    (quotStep A r) (quotStep_mul_ker r) (quotPB A r) (quotPB_comp_quotProj A r) l hΨ_symm hΨ_mem
  rw [map_quotPB_eq Γ π hπ r f₀ hf₀] at hpr
  have hpr0 : constantCoeff (projL l Ψ hΨ_mem) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_projL]
    have h0 : (⟨coeff 0 Ψ, hΨ_mem 0⟩ : RingHom.ker (quotStep A r)) = 0 :=
      Subtype.ext (by simpa [coeff_zero_eq_constantCoeff_apply] using hΨ₀)
    rw [h0, map_zero]
  exact IsSymmetricCocycle.exists_eq_sum_smul_add_homDefect_𝔾ₐ Fact.out
    (CharP.cast_eq_zero _ p) hF_ord hF_unit
    (fun n hn₀ hnh ↦ by
      rw [resBasisCocycle_eq Γ hn₀ hnh]
      exact isSymmetricCocycle_derivCocycle Γ ρA F_res (FormalGroup.map_comp _ _ _).symm _)
    (resBasisCocycle_ord Γ hΓ hΓord π hπ) (resBasisCocycle_comp Γ hΓ hΓcomp π hπ) hpr hpr0

private lemma quotient_step_exists_recombine
    {h : ℕ} {R k A : Type*} [CommRing R] [Field k] [CommRing A] [Algebra R A] [IsLocalRing A]
    {ρ : R →+* k} (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) (r : ℕ)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R))
    (f₀ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
    (hf₀ : (quotRes π (r + 1) (Nat.succ_pos r)).comp f₀.toRingHom = ρ.comp constantCoeff)
    (Ψ : MvPowerSeries (Fin 2) (QuotRing A (r + 1)))
    (hΨ_mem : ∀ d, coeff d Ψ ∈ RingHom.ker (quotStep A r)) :
    let := jModule (quotProj A (r + 1)) (quotStep A r) (quotStep_mul_ker r)
    ∀ {ι_idx : Type*} [Fintype ι_idx]
      (b : Module.Basis ι_idx (ResidueField A) (RingHom.ker (quotStep A r)))
      (c_mat : ι_idx → ℕ → ResidueField A) (g_vec : ι_idx → PowerSeries (ResidueField A)),
      (∀ α, PowerSeries.constantCoeff (g_vec α) = 0) →
      (∀ α, projL (b.coord α) Ψ hΨ_mem =
        ∑ n ∈ Finset.Ioo 0 h, c_mat α n • resBasisCocycle (A := A) Γ n +
          ((Γ.map constantCoeff).map ((residue A).comp (algebraMap R A))).homDefect 𝔾ₐ
            (g_vec α)) →
      let δ : Fin (h - 1) → RingHom.ker (quotStep A r) := fun i ↦ ∑ α, c_mat α (i.val + 1) • b α
      let g : PowerSeries (QuotRing A (r + 1)) := ∑ α, mkJ (τ := Unit) (b α) (g_vec α)
      PowerSeries.constantCoeff g = 0 ∧
      (∀ n, PowerSeries.coeff n g ∈ RingHom.ker (quotStep A r)) ∧
      Ψ = ∑ i : Fin (h - 1), mkJ (δ i) (derivCocycle Γ ((residue A).comp (algebraMap R A))
          ((Γ.map constantCoeff).map ((residue A).comp (algebraMap R A))) i) +
        (Γ.map f₀.toRingHom).homDefect 𝔾ₐ g := by
  intro _inst ι_idx _ b c_mat g_vec hg_vec₀ hg_vec_eq
  let q := quotProj A (r + 1)
  let t := quotStep A r
  let ρA : R →+* ResidueField A := (residue A).comp (algebraMap R A)
  let F_res : FormalGroup (ResidueField A) := (Γ.map constantCoeff).map ρA
  let g : PowerSeries (QuotRing A (r + 1)) := ∑ α, mkJ (τ := Unit) (b α) (g_vec α)
  refine ⟨?_, ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun α _ ↦ ?_
    change constantCoeff (mkJ (τ := Unit) (b α) (g_vec α)) = 0
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mkJ,
      show coeff 0 (g_vec α) = PowerSeries.constantCoeff (g_vec α) from rfl,
      hg_vec₀ α, zero_smul, ZeroMemClass.coe_zero]
  · intro n
    rw [map_sum]
    exact Ideal.sum_mem _ fun α _ ↦ coeff_mkJ_mem (b α) (g_vec α) (Finsupp.single () n)
  · have hΨ_recomb : Ψ = ∑ α, mkJ (b α) (projL (b.coord α) Ψ hΨ_mem) := by
      ext d
      have hsr := congrArg Subtype.val (b.sum_repr ⟨coeff d Ψ, hΨ_mem d⟩)
      dsimp only at hsr
      rw [← hsr, map_sum (coeff d), Submodule.coe_sum]
      refine Finset.sum_congr rfl fun α _ ↦ ?_
      rw [coeff_mkJ, coeff_projL]
      rfl
    have hdef_g : (Γ.map f₀.toRingHom).homDefect 𝔾ₐ g =
        ∑ α, mkJ (b α) (F_res.homDefect 𝔾ₐ (g_vec α)) := by
      change (Γ.map f₀.toRingHom).homDefect 𝔾ₐ (∑ α, mkJ (τ := Unit) (b α) (g_vec α)) = _
      rw [homDefect_𝔾ₐ_sum]
      refine Finset.sum_congr rfl fun α _ ↦ ?_
      dsimp only [F_res, ρA]
      rw [← map_quotPB_eq Γ π hπ r f₀ hf₀]
      exact (mkJ_homDefect_𝔾ₐ q Ideal.Quotient.mk_surjective t (quotStep_mul_ker r) (quotPB A r)
        (quotPB_comp_quotProj A r) (b α) (Γ.map f₀.toRingHom) (g_vec α)).symm
    have hterm : ∀ α, mkJ (b α) (projL (b.coord α) Ψ hΨ_mem) =
        ∑ i : Fin (h - 1), mkJ (b α) (c_mat α (i.val + 1) • derivCocycle Γ ρA F_res i) +
          mkJ (b α) (F_res.homDefect 𝔾ₐ (g_vec α)) := fun α ↦ by
      rw [hg_vec_eq α, sum_resBasisCocycle Γ (c_mat α), mkJ_add]
      congr 1
      ext d
      simp only [map_sum, coeff_mkJ]
      rw [Finset.sum_smul, Submodule.coe_sum]
    rw [hΨ_recomb, hdef_g]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ)
      (t := (Finset.univ : Finset (Fin (h - 1))))]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ext d
    simp only [map_sum, coeff_mkJ, coeff_smul, Finset.smul_sum]
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun α _ ↦ by rw [mul_comm, mul_smul]

private lemma quotient_step_exists_decomp
    {p h : ℕ} [Fact p.Prime] {R k A : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ)
    {r : ℕ} (hr : 1 ≤ r)
    (f₀ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
    (hf₀ : (quotRes π (r + 1) (by omega)).comp f₀.toRingHom = ρ.comp constantCoeff)
    (G₁ : FormalGroup (QuotRing A (r + 1))) [G₁.IsComm]
    (hG₁_t : G₁.map (quotStep A r) = (Γ.map f₀.toRingHom).map (quotStep A r)) :
    let q := quotProj A (r + 1)
    let t := quotStep A r
    let := jModule q t (quotStep_mul_ker r)
    ∃ (δ : Fin (h - 1) → RingHom.ker t) (g : PowerSeries (QuotRing A (r + 1))),
      PowerSeries.constantCoeff g = 0 ∧
      (∀ n, PowerSeries.coeff n g ∈ RingHom.ker t) ∧
      PowerSeries.subst (Γ.map f₀.toRingHom).toPowerSeries
          (Γ.map f₀.toRingHom).invariantDifferential *
          (G₁.toPowerSeries - (Γ.map f₀.toRingHom).toPowerSeries) =
        ∑ i : Fin (h - 1), mkJ (δ i) (derivCocycle Γ ((residue A).comp (algebraMap R A))
            ((Γ.map constantCoeff).map ((residue A).comp (algebraMap R A))) i) +
          (Γ.map f₀.toRingHom).homDefect 𝔾ₐ g := by
  classical
  let q := quotProj A (r + 1)
  let t := quotStep A r
  have : Nontrivial (QuotRing A (r + 1)) := quotRing_nontrivial (r + 1) (by omega)
  have : IsLocalRing (QuotRing A (r + 1)) :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let := jModule q t (quotStep_mul_ker r)
  have := jModule_finite q Ideal.Quotient.mk_surjective t (quotStep_mul_ker r)
  let b := Module.finBasis (ResidueField A) (RingHom.ker t)
  set F_B := Γ.map f₀.toRingHom
  have hΔmem : ∀ d, coeff d (G₁.toPowerSeries - F_B.toPowerSeries) ∈ RingHom.ker t := fun d ↦ by
    rw [RingHom.mem_ker, map_sub, map_sub t, ← coeff_map, ← coeff_map, ← map_toPowerSeries,
      ← map_toPowerSeries, hG₁_t, sub_self]
  set Ψ := PowerSeries.subst F_B.toPowerSeries F_B.invariantDifferential *
    (G₁.toPowerSeries - F_B.toPowerSeries)
  have hΨ_symm : F_B.IsSymmetricCocycle Ψ :=
    isSymmetricCocycle_invariantDifferential_mul_sub G₁ F_B (quotStep_ker_sq r hr) hΔmem
  have hΨ_mem : ∀ d, coeff d Ψ ∈ RingHom.ker t := fun d ↦ by
    rw [coeff_mul]
    exact Ideal.sum_mem _ fun p _ ↦ (RingHom.ker t).mul_mem_left _ (hΔmem p.2)
  have hΨ₀ : constantCoeff Ψ = 0 := by simp [Ψ, G₁.zero_constantCoeff, F_B.zero_constantCoeff]
  have hproj := fun α ↦ quotient_step_exists_projL hF₀ Γ hΓ hΓord hΓcomp π hπ r f₀ hf₀
    Ψ hΨ_symm hΨ_mem hΨ₀ (b.coord α)
  choose c_mat g_vec hg_vec₀ hg_vec_eq using hproj
  exact ⟨_, _, quotient_step_exists_recombine π hπ r Γ f₀ hf₀ Ψ hΨ_mem b c_mat g_vec
    hg_vec₀ hg_vec_eq⟩

private lemma quotient_step_exists_finish
    {h : ℕ} {R k A : Type*} [CommRing R] [Field k] [CommRing A] [Algebra R A] [IsLocalRing A]
    {ρ : R →+* k} {F₀ : FormalGroup k} (π : A →+* k) [IsLocalHom π]
    (hπ : π.comp (algebraMap R A) = ρ) (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R))
    [Γ.IsComm] (hΓ : Γ.map (ρ.comp constantCoeff) = F₀) {r : ℕ} (hr : 1 ≤ r)
    (x₀ : Fin (h - 1) → QuotRing A (r + 1)) (δ : Fin (h - 1) → RingHom.ker (quotStep A r))
    (f₀ f₁ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
    (hf₀X : ∀ i, f₀ (X i) = x₀ i + (0 : RingHom.ker (quotStep A r)).val)
    (hf₁X : ∀ i, f₁ (X i) = x₀ i + (δ i).val)
    (hf₀ : (quotRes π (r + 1) (by omega)).comp f₀.toRingHom = ρ.comp constantCoeff)
    (hf₁ : (quotRes π (r + 1) (by omega)).comp f₁.toRingHom = ρ.comp constantCoeff)
    (htf_eq : (quotStep A r).comp f₀.toRingHom = (quotStep A r).comp f₁.toRingHom)
    (G : FormalGroupLift π F₀) (φ₀ : FormalCoordinate (QuotRing A (r + 1)))
    (hφ₀_map : FormalCoordinate.map (quotRes π (r + 1) (by omega)) φ₀ = 1)
    (g : PowerSeries (QuotRing A (r + 1))) (hg₀ : PowerSeries.constantCoeff g = 0)
    (hg_mem : ∀ n, PowerSeries.coeff n g ∈ RingHom.ker (quotStep A r))
    (hΨ_decomp :
      PowerSeries.subst (Γ.map f₀.toRingHom).toPowerSeries
          (Γ.map f₀.toRingHom).invariantDifferential *
          ((φ₀⁻¹ • (G.formalGroup.map (quotProj A (r + 1)))).toPowerSeries -
            (Γ.map f₀.toRingHom).toPowerSeries) =
        let := jModule (quotProj A (r + 1)) (quotStep A r) (quotStep_mul_ker r)
        ∑ i : Fin (h - 1), mkJ (δ i) (derivCocycle Γ ((residue A).comp (algebraMap R A))
            ((Γ.map constantCoeff).map ((residue A).comp (algebraMap R A))) i) +
          (Γ.map f₀.toRingHom).homDefect 𝔾ₐ g) :
    FormalGroupDeformation.map f₁.toRingHom hf₁ ⟦⟨Γ, inferInstance, hΓ⟩⟧ =
      FormalGroupDeformation.map (quotProj A (r + 1))
        (quotRes_comp_quotProj π (r + 1) (by omega)) ⟦G⟧ := by
  let B := QuotRing A (r + 1)
  let q := quotProj A (r + 1)
  let t := quotStep A r
  let πB := quotRes π (r + 1) (by omega)
  have : Nontrivial B := quotRing_nontrivial (r + 1) (by omega)
  have : IsLocalRing B := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have : IsLocalHom πB := quotRes_isLocalHom π (r + 1) (by omega)
  have hker_pB : RingHom.ker (quotPB A r) = maximalIdeal B := by
    have := quotPB_isLocalHom A r
    exact ker_eq_maximalIdeal_of_field (quotPB A r)
  have htay := invariantDifferential_mul_map_sub_map (R := R) q Ideal.Quotient.mk_surjective t
    (quotStep_mul_ker r) (RingHom.ext fun _ ↦ rfl) (quotPB A r) (quotPB_comp_quotProj A r)
    (ker_quotPB_mul_ker_quotStep π r) Γ ((Γ.map constantCoeff).map ((residue A).comp
      (algebraMap R A))) f₀ f₁ (map_quotPB_eq Γ π hπ r f₀ hf₀) htf_eq
    (fun i ↦ hker_pB ▸ (comp_eq_comp_constantCoeff_iff πB ρ
      (quotRes_comp_algebraMap π ρ hπ (r + 1) (by omega)) f₀).mp hf₀ i)
    (fun i ↦ hker_pB ▸ (comp_eq_comp_constantCoeff_iff πB ρ
      (quotRes_comp_algebraMap π ρ hπ (r + 1) (by omega)) f₁).mp hf₁ i)
  have hδ_eq : (fun i ↦ (⟨f₁ (X i) - f₀ (X i), by
      rw [RingHom.mem_ker, map_sub]
      have h := RingHom.congr_fun htf_eq (X i)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
      exact sub_eq_zero.mpr h.symm⟩ : RingHom.ker t)) = δ := funext fun i ↦ Subtype.ext <| by
    change f₁ (X i) - f₀ (X i) = (δ i).val
    rw [hf₁X i, hf₀X i, ZeroMemClass.coe_zero, _root_.add_zero, add_sub_cancel_left]
  rw [hδ_eq] at htay
  obtain ⟨ψ, hψ_map, hψ_eq⟩ := quotient_step_exists_coord_solve π Γ hr f₀ f₁ htf_eq
    (φ₀⁻¹ • (G.formalGroup.map q)) φ₀ hφ₀_map g hg₀ hg_mem (htay ▸ hΨ_decomp)
  simp only [FormalGroupDeformation.map_mk, FormalGroupDeformation.mk_eq_mk_iff]
  refine ⟨φ₀ * ψ, hψ_map, ?_⟩
  rw [FormalGroupLift.formalGroup_map, hψ_eq, ← mul_smul, mul_inv_cancel, one_smul,
    FormalGroupLift.formalGroup_map]

/-- Existence part of the square-zero quotient lifting step from `A ⧸ 𝔪 ^ r` to
`A ⧸ 𝔪 ^ (r + 1)`. -/
theorem quotient_step_exists
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ)
    {r : ℕ} (hr : 1 ≤ r)
    (f' : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A r)
    (hf' : (quotRes π r hr).comp f'.toRingHom = ρ.comp constantCoeff)
    (G : FormalGroupLift π F₀)
    (hmatch : FormalGroupDeformation.map f'.toRingHom hf' ⟦⟨Γ, inferInstance, hΓ⟩⟧ =
      FormalGroupDeformation.map (quotProj A r) (quotRes_comp_quotProj π r hr) ⟦G⟧) :
    ∃ (f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
      (hf : (quotRes π (r + 1) (by omega)).comp f.toRingHom = ρ.comp constantCoeff),
      (quotStep A r).comp f.toRingHom = f'.toRingHom ∧
      FormalGroupDeformation.map f.toRingHom hf ⟦⟨Γ, inferInstance, hΓ⟩⟧ =
        FormalGroupDeformation.map (quotProj A (r + 1))
          (quotRes_comp_quotProj π (r + 1) (by omega)) ⟦G⟧ := by
  classical
  let B := QuotRing A (r + 1)
  let B' := QuotRing A r
  let q := quotProj A (r + 1)
  let t := quotStep A r
  let πB := quotRes π (r + 1) (by omega)
  let πB' := quotRes π r hr
  have : Nontrivial B := quotRing_nontrivial (r + 1) (by omega)
  have : Nontrivial B' := quotRing_nontrivial r hr
  have : IsLocalRing B := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have : IsLocalRing B' := IsLocalRing.of_surjective' (quotProj A r) Ideal.Quotient.mk_surjective
  have : IsLocalHom πB := quotRes_isLocalHom π (r + 1) (by omega)
  have : IsLocalHom πB' := quotRes_isLocalHom π r hr
  have : IsLocalHom t := ⟨fun b hb ↦ IsUnit.of_map πB _ <| by
    dsimp only [πB]
    rw [← quotRes_comp_quotStep π r hr]
    exact hb.map πB'⟩
  choose x₀ hx₀ using fun i : Fin (h - 1) ↦
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right r.le_succ) (f' (X i))
  obtain ⟨f₀, hf₀X, hf₀, htf₀⟩ := lift_algHom_along_quotStep ρ π hπ hr f' hf' (fun _ ↦ 0) hx₀
  simp only [FormalGroupDeformation.map_mk, FormalGroupDeformation.mk_eq_mk_iff,
    FormalGroupLift.formalGroup_map] at hmatch
  obtain ⟨φ', hφ'_map, hφ'_eq⟩ := hmatch
  obtain ⟨φ₀, hφ₀⟩ := FormalCoordinate.map_surjective_of_isLocalHom t
    (Ideal.Quotient.factor_surjective _) φ'
  have hφ₀_map : FormalCoordinate.map πB φ₀ = 1 := by
    dsimp only [πB]
    rw [← quotRes_comp_quotStep π r hr, FormalCoordinate.map_comp, hφ₀, hφ'_map]
  set G₁ := φ₀⁻¹ • (G.formalGroup.map q)
  have hG₁_t : G₁.map t = (Γ.map f₀.toRingHom).map t := by
    rw [FormalGroup.map_smul, map_inv, hφ₀, FormalGroup.map_comp, quotStep_comp_quotProj r,
      ← hφ'_eq, FormalGroup.map_comp, htf₀, inv_smul_smul]
  obtain ⟨δ, g, hg₀, hg_mem, hΨ_decomp⟩ := quotient_step_exists_decomp hF₀ Γ hΓ hΓord hΓcomp
    π hπ hr f₀ hf₀ G₁ hG₁_t
  obtain ⟨f₁, hf₁X, hf₁, htf₁⟩ := lift_algHom_along_quotStep ρ π hπ hr f' hf' δ hx₀
  exact ⟨f₁, hf₁, htf₁, quotient_step_exists_finish π hπ Γ hΓ hr x₀ δ f₀ f₁ hf₀X hf₁X hf₀ hf₁
    (htf₀.trans htf₁.symm) G φ₀ hφ₀_map g hg₀ hg_mem hΨ_decomp⟩

private lemma starIso_diff_coboundary
    {p h : ℕ} [Fact p.Prime] {R k A : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    [CommRing A] [Algebra R A] [IsLocalRing A]
    (π : A →+* k) [IsLocalHom π] {r : ℕ} (hr : 1 ≤ r)
    (f₀ f₁ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
    (hf₀ : (quotRes π (r + 1) (by omega)).comp f₀.toRingHom = ρ.comp constantCoeff)
    (hf₁ : (quotRes π (r + 1) (by omega)).comp f₁.toRingHom = ρ.comp constantCoeff)
    (htf : (quotStep A r).comp f₀.toRingHom = (quotStep A r).comp f₁.toRingHom)
    (hdef : FormalGroupDeformation.map f₀.toRingHom hf₀ ⟦⟨Γ, inferInstance, hΓ⟩⟧ =
      FormalGroupDeformation.map f₁.toRingHom hf₁ ⟦⟨Γ, inferInstance, hΓ⟩⟧) :
    ∃ g : PowerSeries (QuotRing A (r + 1)),
      (∀ n, PowerSeries.coeff n g ∈ RingHom.ker (quotStep A r)) ∧
      PowerSeries.subst (Γ.map f₀.toRingHom).toPowerSeries
          (Γ.map f₀.toRingHom).invariantDifferential *
          ((Γ.map f₁.toRingHom).toPowerSeries - (Γ.map f₀.toRingHom).toPowerSeries) =
        (Γ.map f₀.toRingHom).homDefect 𝔾ₐ g := by
  let B := QuotRing A (r + 1)
  let B' := QuotRing A r
  let t := quotStep A r
  let πB' := quotRes π r hr
  have : Nontrivial B := quotRing_nontrivial (r + 1) (by omega)
  have : Nontrivial B' := quotRing_nontrivial r hr
  have : IsLocalRing B :=
    IsLocalRing.of_surjective' (quotProj A (r + 1)) Ideal.Quotient.mk_surjective
  have : IsLocalRing B' := IsLocalRing.of_surjective' (quotProj A r) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal B') B' :=
    isAdicComplete_of_pow_eq_bot (quotRing_maximalIdeal_pow π r hr)
  have : IsLocalHom πB' := quotRes_isLocalHom π r hr
  simp only [FormalGroupDeformation.map_mk, FormalGroupDeformation.mk_eq_mk_iff,
    FormalGroupLift.formalGroup_map] at hdef
  obtain ⟨ψ, hψ_map, hψ_eq⟩ := hdef
  set F₀B := Γ.map f₀.toRingHom
  set F' := Γ.map (t.comp f₀.toRingHom)
  have hψ'_smul : (FormalCoordinate.map t ψ) • F' = F' := by
    have hF' : F' = F₀B.map t := (FormalGroup.map_comp _ _ _).symm
    rw [hF', ← FormalGroup.map_smul, hψ_eq, FormalGroup.map_comp, ← htf, ← FormalGroup.map_comp]
  let e' : FormalGroupIso F' F' :=
    (FormalGroup.smulIso (FormalCoordinate.map t ψ) F').trans (formalGroupIsoOfEq hψ'_smul)
  have he'_series : e'.toHom.toPowerSeries = (FormalCoordinate.map t ψ).toPowerSeries := by
    simp only [e', FormalGroupIso.trans_toHom, FormalGroupHom.comp_toPowerSeries,
      formalGroupIsoOfEq_toHom_toPowerSeries, FormalCoordinate.X_subst_toPowerSeries,
      FormalGroup.smulIso_toHom_toPowerSeries]
  have he'_star : e'.IsStarIso πB' := by
    rw [FormalGroupIso.isStarIso_iff, he'_series, ← FormalCoordinate.toPowerSeries_map,
      ← FormalCoordinate.map_comp, quotRes_comp_quotStep π r hr, hψ_map,
      FormalCoordinate.toPowerSeries_one]
  have hF'_ht : (F'.map πB').height p = h := by
    rw [FormalGroup.map_comp, ← RingHom.comp_assoc, quotRes_comp_quotStep π r hr,
      hf₀, hΓ, hF₀]
  have he'_refl := FormalGroupIso.eq_of_isStarIso πB' e' (FormalGroupIso.refl F') hF'_ht
  have hψ_ker : ∀ n, PowerSeries.coeff n (ψ.toPowerSeries - PowerSeries.X) ∈
      RingHom.ker t := fun n ↦ by
    have hc := congrArg (fun (e : FormalGroupIso F' F') ↦
      PowerSeries.coeff n e.toHom.toPowerSeries) he'_refl
    rw [he'_series, FormalGroupIso.refl_toHom, FormalGroupHom.id_toPowerSeries,
      FormalCoordinate.toPowerSeries_map] at hc
    rw [RingHom.mem_ker, map_sub, map_sub t, ← PowerSeries.coeff_map, hc,
      ← PowerSeries.map_X t, PowerSeries.coeff_map, sub_self]
  have hψ_sqzero : ψ = FormalCoordinate.ofSquareZero (quotStep_ker_sq r hr)
      (ψ.toPowerSeries - PowerSeries.X) (by simp) hψ_ker := by ext n; simp
  have hcob_sq := invariantDifferential_mul_smul_sub_eq_homDefect_𝔾ₐ F₀B (quotStep_ker_sq r hr)
    (ψ.toPowerSeries - PowerSeries.X) (by simp) hψ_ker
  refine ⟨F₀B.invariantDifferential * (ψ.toPowerSeries - PowerSeries.X), fun n ↦ ?_, ?_⟩
  · rw [PowerSeries.coeff_mul]
    exact Ideal.sum_mem _ fun p _ ↦ (RingHom.ker t).mul_mem_left _ (hψ_ker p.2)
  · rwa [← hψ_sqzero, hψ_eq] at hcob_sq

private lemma quotient_step_unique_coord_eq
    {p h : ℕ} [Fact p.Prime] {R k A : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    [CommRing A] [Algebra R A] [IsLocalRing A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) (r : ℕ)
    (f₀ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
    (hf₀ : (quotRes π (r + 1) (Nat.succ_pos r)).comp f₀.toRingHom = ρ.comp constantCoeff) :
    let := jModule (quotProj A (r + 1)) (quotStep A r) (quotStep_mul_ker r)
    ∀ (δ : Fin (h - 1) → RingHom.ker (quotStep A r)) (g : PowerSeries (QuotRing A (r + 1))),
      (∀ n, PowerSeries.coeff n g ∈ RingHom.ker (quotStep A r)) →
      (∑ j : Fin (h - 1), mkJ (δ j) (derivCocycle Γ ((residue A).comp (algebraMap R A))
          ((Γ.map constantCoeff).map ((residue A).comp (algebraMap R A))) j) =
        (Γ.map f₀.toRingHom).homDefect 𝔾ₐ g) →
      ∀ (l : RingHom.ker (quotStep A r) →ₗ[ResidueField A] ResidueField A) (i : Fin (h - 1)),
        l (δ i) = 0 := by
  intro _inst δ g hg_mem h_eq l i
  let q := quotProj A (r + 1)
  let t := quotStep A r
  let ι : ResidueField A →+* k := ResidueField.lift π
  let ρA : R →+* ResidueField A := (residue A).comp (algebraMap R A)
  have hιρA : ι.comp ρA = ρ := by
    dsimp only [ρA, ι]
    rw [← RingHom.comp_assoc, ResidueField.lift_comp_residue, hπ]
  let F_res : FormalGroup (ResidueField A) := (Γ.map constantCoeff).map ρA
  have hF_res_ht : F_res.height p = h := by
    rw [← F_res.height_map ι, FormalGroup.map_comp, hιρA, FormalGroup.map_comp, hΓ, hF₀]
  have hK_char : CharP (ResidueField A) p := ι.charP ι.injective p
  have hF_ord : ((p ^ h : ℕ) : ℕ∞) ≤ (F_res.nsmulSeries p).order :=
    (F_res.height_eq_natCast_iff.mp hF_res_ht).ge
  have hmem_lhs : ∀ d, coeff d (∑ j, mkJ (δ j) (derivCocycle Γ ρA F_res j)) ∈
      RingHom.ker t := fun d ↦ sum_mkJ_mem q t (quotStep_mul_ker r) δ _ d
  have hmem_rhs : ∀ d, coeff d ((Γ.map f₀.toRingHom).homDefect 𝔾ₐ g) ∈ RingHom.ker t :=
    homDefect_𝔾ₐ_coeff_mem (Γ.map f₀.toRingHom) hg_mem
  have hproj := projL_eq_of_eq l hmem_lhs hmem_rhs h_eq
  have hLHS : projL l (∑ j, mkJ (δ j) (derivCocycle Γ ρA F_res j)) hmem_lhs =
      ∑ n ∈ Finset.Ioo 0 h, (if hn : 0 < n ∧ n < h then
        l (δ ⟨n - 1, by omega⟩) else 0) • resBasisCocycle (A := A) Γ n := by
    rw [sum_resBasisCocycle Γ]
    ext d
    rw [coeff_projL]
    have hcoe : (⟨coeff d (∑ j, mkJ (δ j) (derivCocycle Γ ρA F_res j)), hmem_lhs d⟩ :
        RingHom.ker t) = ∑ j, coeff d (derivCocycle Γ ρA F_res j) • δ j :=
      Subtype.ext <| by rw [Submodule.coe_sum]; simp [coeff_mkJ]
    rw [hcoe, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : (⟨j.val + 1 - 1, by omega⟩ : Fin (h - 1)) = j := Fin.ext (Nat.add_sub_cancel j.val 1)
    dsimp only [ρA, F_res]
    rw [LinearMap.map_smul, smul_eq_mul, mul_comm, dite_eq_left ⟨Nat.succ_pos _, by omega⟩, hj,
      ← coeff_smul]
  have hRHS := projL_homDefect_𝔾ₐ q Ideal.Quotient.mk_surjective t (quotStep_mul_ker r)
    (quotPB A r) (quotPB_comp_quotProj A r) l (Γ.map f₀.toRingHom) g hg_mem
  rw [hLHS, hRHS, map_quotPB_eq Γ π hπ r f₀ hf₀] at hproj
  have hzero := eq_zero_of_sum_smul_eq_homDefect_𝔾ₐ Fact.out hF_ord
    (resBasisCocycle_ord Γ hΓ hΓord π hπ) (resBasisCocycle_comp Γ hΓ hΓcomp π hπ) hproj
    (i := i.val + 1) (by omega) (by omega)
  simpa [show 0 < i.val + 1 ∧ i.val + 1 < h from ⟨by omega, by omega⟩] using hzero

/-- Uniqueness part of the square-zero quotient lifting step from `A ⧸ 𝔪 ^ r` to
`A ⧸ 𝔪 ^ (r + 1)`. -/
theorem quotient_step_unique
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ)
    {r : ℕ} (hr : 1 ≤ r)
    (f₀ f₁ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (r + 1))
    (hf₀ : (quotRes π (r + 1) (by omega)).comp f₀.toRingHom = ρ.comp constantCoeff)
    (hf₁ : (quotRes π (r + 1) (by omega)).comp f₁.toRingHom = ρ.comp constantCoeff)
    (htf : (quotStep A r).comp f₀.toRingHom = (quotStep A r).comp f₁.toRingHom)
    (hdef : FormalGroupDeformation.map f₀.toRingHom hf₀ ⟦⟨Γ, inferInstance, hΓ⟩⟧ =
      FormalGroupDeformation.map f₁.toRingHom hf₁ ⟦⟨Γ, inferInstance, hΓ⟩⟧) :
    f₀ = f₁ := by
  classical
  let B := QuotRing A (r + 1)
  let q := quotProj A (r + 1)
  let t := quotStep A r
  let πB := quotRes π (r + 1) (by omega)
  let p_B := quotPB A r
  have : Nontrivial B := quotRing_nontrivial (r + 1) (by omega)
  have : IsLocalRing B := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal B) B :=
    isAdicComplete_of_pow_eq_bot (quotRing_maximalIdeal_pow π (r + 1) (by omega))
  have : IsLocalHom πB := quotRes_isLocalHom π (r + 1) (by omega)
  have hker_pB : RingHom.ker p_B = maximalIdeal B := by
    have := quotPB_isLocalHom A r
    exact ker_eq_maximalIdeal_of_field p_B
  let := jModule q t (quotStep_mul_ker r)
  have := jModule_finite q Ideal.Quotient.mk_surjective t (quotStep_mul_ker r)
  let b := Module.finBasis (ResidueField A) (RingHom.ker t)
  have hf₀_mem : ∀ i, f₀ (X i) ∈ maximalIdeal B :=
    (comp_eq_comp_constantCoeff_iff πB ρ
      (quotRes_comp_algebraMap π ρ hπ (r + 1) (by omega)) f₀).mp hf₀
  have hf₁_mem : ∀ i, f₁ (X i) ∈ maximalIdeal B :=
    (comp_eq_comp_constantCoeff_iff πB ρ
      (quotRes_comp_algebraMap π ρ hπ (r + 1) (by omega)) f₁).mp hf₁
  obtain ⟨g, hg_mem, hcob⟩ := starIso_diff_coboundary hF₀ Γ hΓ π hr f₀ f₁ hf₀ hf₁ htf hdef
  have htay := invariantDifferential_mul_map_sub_map (R := R) q Ideal.Quotient.mk_surjective t
    (quotStep_mul_ker r) (RingHom.ext fun _ ↦ rfl) p_B (quotPB_comp_quotProj A r)
    (ker_quotPB_mul_ker_quotStep π r) Γ
    ((Γ.map constantCoeff).map ((residue A).comp (algebraMap R A))) f₀ f₁
    (map_quotPB_eq Γ π hπ r f₀ hf₀) htf (fun i ↦ hker_pB ▸ hf₀_mem i)
    (fun i ↦ hker_pB ▸ hf₁_mem i)
  let δ : Fin (h - 1) → RingHom.ker t := fun i ↦ ⟨f₁ (X i) - f₀ (X i), by
    rw [RingHom.mem_ker, map_sub]
    have h := RingHom.congr_fun htf (X i)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    exact sub_eq_zero.mpr h.symm⟩
  exact algHom_ext_of_X_eq hf₀_mem fun i ↦ (sub_eq_zero.mp (congrArg Subtype.val
    (b.ext_elem fun α ↦ by
      have hind := quotient_step_unique_coord_eq hF₀ Γ hΓ hΓord hΓcomp π hπ r f₀ hf₀ δ g hg_mem
        (htay.symm.trans hcob) (b.coord α) i
      change b.coord α (δ i) = b.coord α 0
      rw [hind, map_zero]))).symm

end QuotientStep

end FormalGroup

