/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.RingTheory.FormalGroup.Deformation.ArtinianStep
-- Proof-only: adic topology and Noetherian local power series.
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# The Lubin–Tate universal deformation theorem

Let `k` be a field of characteristic `p > 0`, `F₀` a commutative formal group law over `k` of
finite height `h`, and `ρ : R →+* k` a ring homomorphism. A deformation `Γ` of `F₀` over
`R⟦t₁, …, t_{h-1}⟧` whose partial-derivative symmetric 2-cocycles
`FormalGroup.derivCocycle Γ ρ F₀ i` vanish below degree `p ^ (i + 1)` with degree-`p ^ (i + 1)`
component the Lazard cocycle `lazardCocycle (p ^ (i + 1)) k` is **universal**: for every complete
Noetherian local `R`-algebra `(A, π)` with `π : A →+* k` local and `π ∘ algebraMap R A = ρ`,
evaluation of `Γ` gives a bijection between `R`-algebra homomorphisms
`f : R⟦t₁, …, t_{h-1}⟧ →ₐ[R] A` satisfying `π ∘ f = ρ ∘ constantCoeff` (equivalently
`∀ i, f (X i) ∈ maximalIdeal A`, or local `R`-algebra homomorphisms when `R` is local and `ρ` is
local) and `FormalGroupDeformation π F₀` (`FormalGroup.isUniversal_of_derivCocycle`).
Specializing to `F.lubinTateLaw hp h` yields `FormalGroup.lubinTate_universal_deformation`.

The proof inductively lifts across the artinian quotients `A ⧸ 𝔪 ^ (n + 1)` via
`FormalGroup.quotient_step_exists` and `FormalGroup.quotient_step_unique`, and passes to the
inverse limit using `IsAdicComplete (maximalIdeal A) A` and rigidity
(`FormalGroupIso.eq_of_isStarIso`).

## Main results

* `FormalGroup.isUniversal_of_derivCocycle`, `FormalGroup.universalDeformationEquiv`,
  `FormalGroup.universalDeformationMaximalIdealEquiv`, and
  `FormalGroup.universalDeformationLocalEquiv`: the Lubin–Tate universal deformation criterion
  from `derivCocycle` leading terms.
* `FormalGroup.lubinTate_universal_deformation` and `FormalGroup.lubinTateUniversalEquiv`:
  `F.lubinTateLaw hp h` is a universal deformation of `F₀ = F.map ρ`.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §3 (Theorem 3.1).
-/

public section

noncomputable section

open IsLocalRing MvPowerSeries TauCeti

namespace FormalGroup

section CompatLimit

private lemma compat_factor_eq {A : Type*} [CommRing A] {I : Ideal A}
    (y : ∀ n : ℕ, A ⧸ I ^ (n + 1))
    (hy : ∀ n : ℕ,
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) (y (n + 1)) = y n)
    {m n : ℕ} (hmn : m ≤ n) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) (y n) =
      y m := by
  induction hmn with
  | refl =>
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (y m)
    rw [← hb, Ideal.Quotient.factor_mk]
  | @step k hk ih =>
    have hc : Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hk 1))
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (k + 1))) (y (k + 1))) =
        Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (Nat.add_le_add_right hk.step 1)) (y (k + 1)) := by
      rw [← RingHom.comp_apply, Ideal.Quotient.factor_comp]
    rw [← ih, ← hc, hy k]

/-- Lift a compatible sequence `(y n : A ⧸ I ^ (n + 1))` to `A` when `A` is `I`-adically
precomplete. -/
private lemma exists_limit_of_compat {A : Type*} [CommRing A] {I : Ideal A}
    [IsPrecomplete I A] (y : ∀ n : ℕ, A ⧸ I ^ (n + 1))
    (hy : ∀ n : ℕ,
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) (y (n + 1)) = y n) :
    ∃ a : A, ∀ n : ℕ, Ideal.Quotient.mk (I ^ (n + 1)) a = y n := by
  choose s hs using fun n : ℕ ↦ Ideal.Quotient.mk_surjective (y n)
  have hsmod : ∀ {m n : ℕ}, m ≤ n →
      s m ≡ s n [SMOD (I ^ m • ⊤ : Submodule A A)] := fun {m n} hmn ↦ by
    rcases Nat.eq_zero_or_pos m with rfl | _
    · rw [SModEq.sub_mem, pow_zero, Ideal.one_eq_top, smul_eq_mul, Ideal.mul_top]
      exact Submodule.mem_top
    · rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      refine Ideal.pow_le_pow_right (Nat.le_succ m) ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hs m]
      calc y m - Ideal.Quotient.mk (I ^ (m + 1)) (s n)
          = Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) (y n) -
              Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1))
                (Ideal.Quotient.mk (I ^ (n + 1)) (s n)) := by
            rw [compat_factor_eq y hy hmn, Ideal.Quotient.factor_mk]
        _ = 0 := by rw [hs n, sub_self]
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' s (fun hmn ↦ hsmod hmn)
  refine ⟨a, fun n ↦ ?_⟩
  have hna := ha (n + 1)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
    ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hna
  calc Ideal.Quotient.mk (I ^ (n + 1)) a
      = Ideal.Quotient.mk (I ^ (n + 1)) (s (n + 1)) := hna.symm
    _ = Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
          (Ideal.Quotient.mk (I ^ (n + 2)) (s (n + 1))) := (Ideal.Quotient.factor_mk _ _).symm
    _ = Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) (y (n + 1)) := by
          rw [hs (n + 1)]
    _ = y n := hy n

end CompatLimit

section UniversalProofHelpers

private lemma quotRes_zero_injective {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] : Function.Injective (quotRes π 1 le_rfl) := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro b hb
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [RingHom.mem_ker] at hb
  change quotRes π 1 le_rfl (quotProj A 1 a) = 0 at hb
  rw [← RingHom.comp_apply (quotRes π 1 le_rfl) (quotProj A 1), quotRes_comp_quotProj] at hb
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact (ker_eq_maximalIdeal_of_field π).le hb

private lemma base_hom_eq_of_quotRes {h : ℕ} {R k A : Type*} [CommRing R] [Field k]
    [CommRing A] [Algebra R A] [IsLocalRing A] {ρ : R →+* k}
    (π : A →+* k) [IsLocalHom π] (g₀ g₁ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A 1)
    (hg₀ : (quotRes π 1 le_rfl).comp g₀.toRingHom = ρ.comp constantCoeff)
    (hg₁ : (quotRes π 1 le_rfl).comp g₁.toRingHom = ρ.comp constantCoeff) : g₀ = g₁ := by
  have : Nontrivial (QuotRing A 1) := quotRing_nontrivial 1 le_rfl
  have : IsLocalRing (QuotRing A 1) :=
    IsLocalRing.of_surjective' (quotProj A 1) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal (QuotRing A 1)) (QuotRing A 1) :=
    isAdicComplete_of_pow_eq_bot (quotRing_maximalIdeal_pow π 1 le_rfl)
  have hπB_inj := quotRes_zero_injective π
  have hg₀X : ∀ i, g₀ (X i) = 0 := fun i ↦ hπB_inj (by
    calc quotRes π 1 le_rfl (g₀ (X i)) = (quotRes π 1 le_rfl).comp g₀.toRingHom (X i) := rfl
      _ = (ρ.comp constantCoeff) (X i) := RingHom.congr_fun hg₀ (X i)
      _ = quotRes π 1 le_rfl 0 := by simp)
  have hg₁X : ∀ i, g₁ (X i) = 0 := fun i ↦ hπB_inj (by
    calc quotRes π 1 le_rfl (g₁ (X i)) = (quotRes π 1 le_rfl).comp g₁.toRingHom (X i) := rfl
      _ = (ρ.comp constantCoeff) (X i) := RingHom.congr_fun hg₁ (X i)
      _ = quotRes π 1 le_rfl 0 := by simp)
  exact algHom_ext_of_X_eq (fun i ↦ by rw [hg₀X i]; exact Ideal.zero_mem _)
    (fun i ↦ (hg₀X i).trans (hg₁X i).symm)

private lemma isUniversal_injective
    {p h : ℕ} [Fact p.Prime] {R k A : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    Function.Injective
      (fun f : {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A //
          π.comp f.toRingHom = ρ.comp constantCoeff} ↦
        FormalGroupDeformation.map f.val.toRingHom f.property ⟦⟨Γ, inferInstance, hΓ⟩⟧) := by
  rintro ⟨f₀, hf₀⟩ ⟨f₁, hf₁⟩ hdef
  have hf₀_mem : ∀ i, f₀ (X i) ∈ maximalIdeal A :=
    (comp_eq_comp_constantCoeff_iff π ρ hπ f₀).mp hf₀
  have hqAlg_π : ∀ n (f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A),
      π.comp f.toRingHom = ρ.comp constantCoeff →
      (quotRes π (n + 1) (Nat.succ_pos n)).comp
        ((IsScalarTower.toAlgHom R A (QuotRing A (n + 1))).comp f).toRingHom =
        ρ.comp constantCoeff := fun n f hf ↦ by
    change (quotRes π (n + 1) (Nat.succ_pos n)).comp
      ((quotProj A (n + 1)).comp f.toRingHom) = ρ.comp constantCoeff
    rw [← RingHom.comp_assoc, quotRes_comp_quotProj, hf]
  have hcompat_q : ∀ n : ℕ,
      (quotProj A (n + 1)).comp f₀.toRingHom = (quotProj A (n + 1)).comp f₁.toRingHom := by
    intro n
    induction n with
    | zero =>
      exact congrArg AlgHom.toRingHom (base_hom_eq_of_quotRes π
        ((IsScalarTower.toAlgHom R A (QuotRing A 1)).comp f₀)
        ((IsScalarTower.toAlgHom R A (QuotRing A 1)).comp f₁)
        (hqAlg_π 0 f₀ hf₀) (hqAlg_π 0 f₁ hf₁))
    | succ n ih =>
      have htf :
          (quotStep A (n + 1)).comp
            ((IsScalarTower.toAlgHom R A (QuotRing A (n + 2))).comp f₀).toRingHom =
          (quotStep A (n + 1)).comp
            ((IsScalarTower.toAlgHom R A (QuotRing A (n + 2))).comp f₁).toRingHom := by
        change (quotStep A (n + 1)).comp ((quotProj A (n + 2)).comp f₀.toRingHom) =
          (quotStep A (n + 1)).comp ((quotProj A (n + 2)).comp f₁.toRingHom)
        rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, quotStep_comp_quotProj (n + 1)]
        exact ih
      have hmap := congrArg (FormalGroupDeformation.map (quotProj A (n + 2))
        (quotRes_comp_quotProj π (n + 2) (Nat.succ_pos (n + 1)))) hdef
      dsimp only at hmap
      rw [FormalGroupDeformation.map_comp, FormalGroupDeformation.map_comp] at hmap
      exact congrArg AlgHom.toRingHom (quotient_step_unique hF₀ Γ hΓ hΓord hΓcomp π hπ
        (r := n + 1) (Nat.succ_pos n)
        ((IsScalarTower.toAlgHom R A (QuotRing A (n + 2))).comp f₀)
        ((IsScalarTower.toAlgHom R A (QuotRing A (n + 2))).comp f₁)
        (hqAlg_π (n + 1) f₀ hf₀) (hqAlg_π (n + 1) f₁ hf₁) htf hmap)
  refine Subtype.ext (algHom_ext_of_X_eq hf₀_mem fun i ↦ ?_)
  refine eq_of_sub_eq_zero
    (IsHausdorff.haus' (I := maximalIdeal A) (f₀ (X i) - f₁ (X i)) fun n ↦ ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  rcases n with _ | n
  · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    exact sub_eq_zero.mpr (RingHom.congr_fun (hcompat_q n) (X i))

private lemma exists_base_lift_quotRing {h : ℕ} {R k A : Type*} [CommRing R] [Field k]
    [CommRing A] [Algebra R A] [IsLocalRing A] {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm]
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) (G : FormalGroupLift π F₀) :
    ∃ f₀ : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A 1,
      (quotRes π 1 le_rfl).comp f₀.toRingHom = ρ.comp constantCoeff ∧
      ∀ hf₀, FormalGroupDeformation.map f₀.toRingHom hf₀ ⟦⟨Γ, inferInstance, hΓ⟩⟧ =
        FormalGroupDeformation.map (quotProj A 1) (quotRes_comp_quotProj π 1 le_rfl) ⟦G⟧ := by
  have : Nontrivial (QuotRing A 1) := quotRing_nontrivial 1 le_rfl
  have : IsLocalRing (QuotRing A 1) :=
    IsLocalRing.of_surjective' (quotProj A 1) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal (QuotRing A 1)) (QuotRing A 1) :=
    isAdicComplete_of_pow_eq_bot (quotRing_maximalIdeal_pow π 1 le_rfl)
  have : IsLocalHom (quotRes π 1 le_rfl) := quotRes_isLocalHom π 1 le_rfl
  obtain ⟨f₀, hf₀X⟩ := exists_algHom_X_eq (R := R) (σ := Fin (h - 1))
    (fun _ ↦ (0 : maximalIdeal (QuotRing A 1)))
  have hf₀ : (quotRes π 1 le_rfl).comp f₀.toRingHom = ρ.comp constantCoeff :=
    (comp_eq_comp_constantCoeff_iff (quotRes π 1 le_rfl) ρ (by
      ext r
      change quotRes π 1 le_rfl (quotProj A 1 (algebraMap R A r)) = ρ r
      rw [← RingHom.comp_apply (quotRes π 1 le_rfl) (quotProj A 1), quotRes_comp_quotProj,
        ← RingHom.comp_apply π (algebraMap R A), hπ]) f₀).mpr
      fun i ↦ by rw [hf₀X i]; exact Ideal.zero_mem _
  refine ⟨f₀, hf₀, fun hf₀' ↦ ?_⟩
  simp only [FormalGroupDeformation.map_mk, FormalGroupDeformation.mk_eq_mk_iff,
    FormalGroupLift.formalGroup_map]
  refine ⟨1, by simp, ?_⟩
  rw [one_smul]
  refine FormalGroup.map_injective (quotRes_zero_injective π) ?_
  dsimp only
  rw [FormalGroup.map_comp, hf₀', hΓ, FormalGroup.map_comp, quotRes_comp_quotProj, G.map_eq]

private lemma quotProj_comp_eq_of_X_eq
    {h : ℕ} {R k A : Type*} [CommRing R] [Field k] [CommRing A] [Algebra R A] [IsLocalRing A]
    (π : A →+* k) [IsLocalHom π] (n : ℕ) (a_lim : Fin (h - 1) → A)
    (ha_mem : ∀ i, a_lim i ∈ maximalIdeal A)
    (f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A) (hfX : ∀ i, f (X i) = a_lim i)
    (g : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (n + 1))
    (ha_lim : ∀ i, quotProj A (n + 1) (a_lim i) = g (X i)) :
    (quotProj A (n + 1)).comp f.toRingHom = g.toRingHom := by
  have : Nontrivial (QuotRing A (n + 1)) := quotRing_nontrivial (n + 1) (Nat.succ_pos n)
  have : IsLocalRing (QuotRing A (n + 1)) :=
    IsLocalRing.of_surjective' (quotProj A (n + 1)) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal (QuotRing A (n + 1))) (QuotRing A (n + 1)) :=
    isAdicComplete_of_pow_eq_bot (quotRing_maximalIdeal_pow π (n + 1) (Nat.succ_pos n))
  have : IsLocalHom (quotRes π (n + 1) (Nat.succ_pos n)) :=
    quotRes_isLocalHom π (n + 1) (Nat.succ_pos n)
  refine congrArg AlgHom.toRingHom (algHom_ext_of_X_eq
    (f := (IsScalarTower.toAlgHom R A (QuotRing A (n + 1))).comp f) (g := g)
    (fun i ↦ ?_) (fun i ↦ ?_))
  · change quotProj A (n + 1) (f (X i)) ∈ maximalIdeal (QuotRing A (n + 1))
    rw [hfX i, ← ker_eq_maximalIdeal_of_field (quotRes π (n + 1) (Nat.succ_pos n)),
      RingHom.mem_ker]
    change (quotRes π (n + 1) (Nat.succ_pos n)).comp (quotProj A (n + 1)) (a_lim i) = 0
    rw [quotRes_comp_quotProj]
    exact (ker_eq_maximalIdeal_of_field π).ge (ha_mem i)
  · change quotProj A (n + 1) (f (X i)) = g (X i)
    rw [hfX i, ha_lim i]

private lemma exists_starIso_of_quotProj_eq
    {h : ℕ} {R k A : Type*} [CommRing R] [Field k] [CommRing A] [Algebra R A] [IsLocalRing A]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm]
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (π : A →+* k) [IsLocalHom π] (G : FormalGroupLift π F₀) (n : ℕ)
    (f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A)
    (g : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (n + 1))
    (hg : (quotRes π (n + 1) (Nat.succ_pos n)).comp g.toRingHom = ρ.comp constantCoeff)
    (hq : (quotProj A (n + 1)).comp f.toRingHom = g.toRingHom)
    (hmatch : FormalGroupDeformation.map g.toRingHom hg ⟦⟨Γ, inferInstance, hΓ⟩⟧ =
      FormalGroupDeformation.map (quotProj A (n + 1))
        (quotRes_comp_quotProj π (n + 1) (Nat.succ_pos n)) ⟦G⟧) :
    ∃ e : FormalGroupIso ((Γ.map f.toRingHom).map (quotProj A (n + 1)))
        (G.formalGroup.map (quotProj A (n + 1))),
      e.IsStarIso (quotRes π (n + 1) (Nat.succ_pos n)) := by
  simp only [FormalGroupDeformation.map_mk,
    FormalGroupDeformation.mk_eq_mk_iff_exists_isStarIso] at hmatch
  rcases hmatch with ⟨e, he⟩
  have hsrc_eq : (Γ.map f.toRingHom).map (quotProj A (n + 1)) =
      (({ formalGroup := Γ, isComm := inferInstance, map_eq := hΓ } :
        FormalGroupLift (ρ.comp constantCoeff) F₀).map g.toRingHom hg).formalGroup := by
    rw [FormalGroupLift.formalGroup_map, FormalGroup.map_comp, hq]
  have htgt_eq : (G.map (quotProj A (n + 1))
      (quotRes_comp_quotProj π (n + 1) (Nat.succ_pos n))).formalGroup =
      G.formalGroup.map (quotProj A (n + 1)) :=
    FormalGroupLift.formalGroup_map G _ _
  refine ⟨(formalGroupIsoOfEq hsrc_eq).trans (e.trans (formalGroupIsoOfEq htgt_eq)), ?_⟩
  rw [FormalGroupIso.isStarIso_iff, FormalGroupIso.trans_toHom, FormalGroupIso.trans_toHom,
    FormalGroupHom.comp_toPowerSeries, FormalGroupHom.comp_toPowerSeries,
    formalGroupIsoOfEq_toHom_toPowerSeries, formalGroupIsoOfEq_toHom_toPowerSeries,
    PowerSeries.X_subst, PowerSeries.subst_X
      (PowerSeries.HasSubst.of_constantCoeff_zero e.toHom.zero_constantCoeff)]
  exact he.map_toPowerSeries

private lemma exists_compat_lift_seq
    {p h : ℕ} [Fact p.Prime] {R k A : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) (G : FormalGroupLift π F₀) :
    ∃ (f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A)
      (_ : π.comp f.toRingHom = ρ.comp constantCoeff),
      ∀ n : ℕ, ∃ e : FormalGroupIso ((Γ.map f.toRingHom).map (quotProj A (n + 1)))
          (G.formalGroup.map (quotProj A (n + 1))),
        e.IsStarIso (quotRes π (n + 1) (Nat.succ_pos n)) := by
  classical
  let LiftCarrier (n : ℕ) := {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] QuotRing A (n + 1) //
    (quotRes π (n + 1) (Nat.succ_pos n)).comp f.toRingHom = ρ.comp constantCoeff ∧
    ∀ hf, FormalGroupDeformation.map f.toRingHom hf ⟦⟨Γ, inferInstance, hΓ⟩⟧ =
      FormalGroupDeformation.map (quotProj A (n + 1))
        (quotRes_comp_quotProj π (n + 1) (Nat.succ_pos n)) ⟦G⟧}
  have hbase_step := exists_base_lift_quotRing Γ hΓ π hπ G
  have hstep_fun : ∀ n (p : LiftCarrier n), {f : LiftCarrier (n + 1) //
      (quotStep A (n + 1)).comp f.val.toRingHom = p.val.toRingHom} := fun n p ↦ by
    have hex := quotient_step_exists hF₀ Γ hΓ hΓord hΓcomp π hπ (r := n + 1) (Nat.succ_pos n)
      p.val p.property.1 G (p.property.2 p.property.1)
    have hspec := Classical.choose_spec hex
    exact ⟨⟨Classical.choose hex, Classical.choose hspec, fun _ ↦ (Classical.choose_spec hspec).2⟩,
      (Classical.choose_spec hspec).1⟩
  let seq : ∀ n : ℕ, LiftCarrier n :=
    Nat.rec ⟨Classical.choose hbase_step, Classical.choose_spec hbase_step⟩
      fun n ih ↦ (hstep_fun n ih).val
  have hlimitX : ∀ i : Fin (h - 1), ∃ a : A, ∀ n : ℕ, quotProj A (n + 1) a = (seq n).val (X i) :=
    fun i ↦ exists_limit_of_compat (I := maximalIdeal A) (fun n ↦ (seq n).val (X i)) fun n ↦
      RingHom.congr_fun (hstep_fun n (seq n)).property (X i)
  choose a_lim ha_lim using hlimitX
  have ha_mem : ∀ i : Fin (h - 1), a_lim i ∈ maximalIdeal A := fun i ↦ by
    rw [← ker_eq_maximalIdeal_of_field π, RingHom.mem_ker]
    calc π (a_lim i) = quotRes π 1 le_rfl (quotProj A 1 (a_lim i)) := by
          rw [← RingHom.comp_apply (quotRes π 1 le_rfl) (quotProj A 1), quotRes_comp_quotProj]
      _ = (quotRes π 1 le_rfl).comp (seq 0).val.toRingHom (X i) := by rw [ha_lim i 0]; rfl
      _ = (ρ.comp constantCoeff) (X i) := RingHom.congr_fun (seq 0).property.1 (X i)
      _ = 0 := by simp
  obtain ⟨f, hfX⟩ := exists_algHom_X_eq (R := R) (fun i ↦ ⟨a_lim i, ha_mem i⟩)
  have hf : π.comp f.toRingHom = ρ.comp constantCoeff :=
    (comp_eq_comp_constantCoeff_iff π ρ hπ f).mpr fun i ↦ by rw [hfX i]; exact ha_mem i
  refine ⟨f, hf, fun n ↦ exists_starIso_of_quotProj_eq Γ hΓ π G n f (seq n).val
    (seq n).property.1
    (quotProj_comp_eq_of_X_eq π n a_lim ha_mem f hfX (seq n).val (fun i ↦ ha_lim i n))
    ((seq n).property.2 (seq n).property.1)⟩

private lemma compat_starIso_step
    {p h : ℕ} [Fact p.Prime] {R k A : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    [CommRing A] [Algebra R A] [IsLocalRing A] (π : A →+* k) [IsLocalHom π]
    (G : FormalGroupLift π F₀) (f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A)
    (hf : π.comp f.toRingHom = ρ.comp constantCoeff) (n c_idx : ℕ)
    (e₁ : FormalGroupIso ((Γ.map f.toRingHom).map (quotProj A (n + 2)))
      (G.formalGroup.map (quotProj A (n + 2))))
    (e₀ : FormalGroupIso ((Γ.map f.toRingHom).map (quotProj A (n + 1)))
      (G.formalGroup.map (quotProj A (n + 1))))
    (he₀ : e₀.IsStarIso (quotRes π (n + 1) (Nat.succ_pos n)))
    (he₁ : e₁.IsStarIso (quotRes π (n + 2) (Nat.succ_pos (n + 1)))) :
    quotStep A (n + 1) (PowerSeries.coeff c_idx e₁.toHom.toPowerSeries) =
      PowerSeries.coeff c_idx e₀.toHom.toPowerSeries := by
  let q := fun m : ℕ ↦ quotProj A (m + 1)
  let t := quotStep A (n + 1)
  let πB := quotRes π (n + 1) (Nat.succ_pos n)
  have : Nontrivial (QuotRing A (n + 1)) := quotRing_nontrivial (n + 1) (Nat.succ_pos n)
  have : IsLocalRing (QuotRing A (n + 1)) :=
    IsLocalRing.of_surjective' (q n) Ideal.Quotient.mk_surjective
  have : IsLocalHom πB := quotRes_isLocalHom π (n + 1) (Nat.succ_pos n)
  have : IsAdicComplete (maximalIdeal (QuotRing A (n + 1))) (QuotRing A (n + 1)) :=
    isAdicComplete_of_pow_eq_bot (quotRing_maximalIdeal_pow π (n + 1) (Nat.succ_pos n))
  have hsrc : ((Γ.map f.toRingHom).map (q (n + 1))).map t = (Γ.map f.toRingHom).map (q n) := by
    rw [FormalGroup.map_comp, quotStep_comp_quotProj (n + 1)]
  have htgt : (G.formalGroup.map (q (n + 1))).map t = G.formalGroup.map (q n) := by
    rw [FormalGroup.map_comp, quotStep_comp_quotProj (n + 1)]
  let e_cast : FormalGroupIso ((Γ.map f.toRingHom).map (q n)) (G.formalGroup.map (q n)) :=
    (formalGroupIsoOfEq hsrc.symm).trans ((e₁.map t).trans (formalGroupIsoOfEq htgt))
  have hsub_t : PowerSeries.HasSubst (e₁.toHom.toPowerSeries.map t) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      change constantCoeff (MvPowerSeries.map t e₁.toHom.toPowerSeries) = 0
      rw [constantCoeff_map]
      have hc0 := e₁.toHom.zero_constantCoeff
      change t (PowerSeries.constantCoeff e₁.toHom.toPowerSeries) = 0
      rw [hc0, map_zero])
  have he_cast_star : e_cast.IsStarIso πB := by
    have hstar_tn : (e₁.map t).IsStarIso πB :=
      FormalGroupIso.IsStarIso.map e₁ t (quotRes_comp_quotStep π (n + 1) (Nat.succ_pos n))
    rw [FormalGroupIso.isStarIso_iff]
    simp only [e_cast, FormalGroupIso.trans_toHom, FormalGroupHom.comp_toPowerSeries,
      formalGroupIsoOfEq_toHom_toPowerSeries, PowerSeries.X_subst, FormalGroupIso.map_toHom,
      FormalGroupHom.map_toPowerSeries]
    rw [PowerSeries.subst_X hsub_t, ← FormalGroupHom.map_toPowerSeries,
      ← FormalGroupIso.map_toHom, hstar_tn.map_toPowerSeries]
  have hht : (((Γ.map f.toRingHom).map (q n)).map πB).height p = h := by
    rw [FormalGroup.map_comp, quotRes_comp_quotProj π (n + 1) (Nat.succ_pos n),
      FormalGroup.map_comp, hf, hΓ, hF₀]
  have heq := FormalGroupIso.eq_of_isStarIso πB e_cast e₀ hht
  have hc := congrArg (fun (e : FormalGroupIso ((Γ.map f.toRingHom).map (q n))
    (G.formalGroup.map (q n))) ↦ PowerSeries.coeff c_idx e.toHom.toPowerSeries) heq
  have hcast_coeff : PowerSeries.coeff c_idx e_cast.toHom.toPowerSeries =
      t (PowerSeries.coeff c_idx e₁.toHom.toPowerSeries) := by
    simp only [e_cast, FormalGroupIso.trans_toHom, FormalGroupHom.comp_toPowerSeries,
      formalGroupIsoOfEq_toHom_toPowerSeries, PowerSeries.X_subst, FormalGroupIso.map_toHom,
      FormalGroupHom.map_toPowerSeries]
    rw [PowerSeries.subst_X hsub_t, PowerSeries.coeff_map]
  rwa [← hcast_coeff]

private lemma coord_of_compat_starIso_seq
    {h : ℕ} {R k A : Type*} [CommRing R] [Field k]
    {F₀ : FormalGroup k} [F₀.IsComm]
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    [CommRing A] [Algebra R A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (G : FormalGroupLift π F₀)
    (f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A)
    (e_seq : ∀ n : ℕ, FormalGroupIso ((Γ.map f.toRingHom).map (quotProj A (n + 1)))
      (G.formalGroup.map (quotProj A (n + 1))))
    (he_star : ∀ n : ℕ, (e_seq n).IsStarIso (quotRes π (n + 1) (Nat.succ_pos n)))
    (he_compat : ∀ n c_idx : ℕ,
      quotStep A (n + 1) (PowerSeries.coeff c_idx (e_seq (n + 1)).toHom.toPowerSeries) =
        PowerSeries.coeff c_idx (e_seq n).toHom.toPowerSeries) :
    ∃ φ : FormalCoordinate A,
      FormalCoordinate.map π φ = 1 ∧ φ • (Γ.map f.toRingHom) = G.formalGroup := by
  have hc_ex : ∀ c_idx : ℕ, ∃ a : A, ∀ n : ℕ,
      quotProj A (n + 1) a = PowerSeries.coeff c_idx (e_seq n).toHom.toPowerSeries := fun c_idx ↦
    exists_limit_of_compat (I := maximalIdeal A)
      (fun n ↦ PowerSeries.coeff c_idx (e_seq n).toHom.toPowerSeries) (fun n ↦ he_compat n c_idx)
  choose c_phi hc_phi using hc_ex
  let ψ_series : PowerSeries A := PowerSeries.mk c_phi
  have hψ_const : PowerSeries.constantCoeff ψ_series = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    refine IsHausdorff.haus' (I := maximalIdeal A) (c_phi 0) fun n ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    rcases n with _ | n
    · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    · rw [← Ideal.Quotient.eq_zero_iff_mem]
      change quotProj A (n + 1) (c_phi 0) = 0
      rw [hc_phi 0 n, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        (e_seq n).toHom.zero_constantCoeff]
  have hψ_one : IsUnit (PowerSeries.coeff 1 ψ_series) := by
    rw [PowerSeries.coeff_mk]
    refine IsUnit.of_map π _ ?_
    rw [← quotRes_comp_quotProj π 1 le_rfl, RingHom.comp_apply, hc_phi 1 0,
      ← PowerSeries.coeff_map, (he_star 0).map_toPowerSeries, PowerSeries.coeff_one_X]
    exact isUnit_one
  let φ : FormalCoordinate A := ⟨ψ_series, hψ_const, hψ_one⟩
  refine ⟨φ, ?_, ?_⟩
  · ext n
    rw [FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_one,
      ← quotRes_comp_quotProj π 1 le_rfl, PowerSeries.map_comp, RingHom.comp_apply]
    have hmap0 : PowerSeries.map (quotProj A 1) ψ_series = (e_seq 0).toHom.toPowerSeries :=
      PowerSeries.ext fun m ↦ by simp [ψ_series, hc_phi m 0]
    change PowerSeries.coeff n
      (PowerSeries.map (quotRes π 1 le_rfl) (PowerSeries.map (quotProj A 1) ψ_series)) = _
    rw [hmap0, (he_star 0).map_toPowerSeries]
  · ext d
    refine eq_of_sub_eq_zero (IsHausdorff.haus' (I := maximalIdeal A) _ fun n ↦ ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    rcases n with _ | n
    · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← coeff_map, ← coeff_map,
        ← map_toPowerSeries, ← map_toPowerSeries, FormalGroup.map_smul]
      have hφ_n : FormalCoordinate.map (quotProj A (n + 1)) φ = (e_seq n).toFormalCoordinate := by
        ext m
        rw [FormalCoordinate.toPowerSeries_map, PowerSeries.coeff_map,
          FormalGroupIso.toFormalCoordinate_toPowerSeries]
        dsimp only [φ, ψ_series]
        rw [PowerSeries.coeff_mk]
        exact hc_phi m n
      rw [hφ_n, FormalGroupIso.toFormalCoordinate_smul]

private lemma isUniversal_surjective
    {p h : ℕ} [Fact p.Prime] {R k A : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    Function.Surjective
      (fun f : {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A //
          π.comp f.toRingHom = ρ.comp constantCoeff} ↦
        FormalGroupDeformation.map f.val.toRingHom f.property ⟦⟨Γ, inferInstance, hΓ⟩⟧) := by
  intro x
  obtain ⟨G, rfl⟩ := Quotient.exists_rep x
  obtain ⟨f, hf, he_ex⟩ := exists_compat_lift_seq hF₀ Γ hΓ hΓord hΓcomp π hπ G
  choose e_seq he_star using he_ex
  have he_compat : ∀ n c_idx : ℕ,
      quotStep A (n + 1) (PowerSeries.coeff c_idx (e_seq (n + 1)).toHom.toPowerSeries) =
        PowerSeries.coeff c_idx (e_seq n).toHom.toPowerSeries := fun n c_idx ↦
    compat_starIso_step hF₀ Γ hΓ π G f hf n c_idx (e_seq (n + 1)) (e_seq n)
      (he_star n) (he_star (n + 1))
  obtain ⟨φ, hφ_map, hφ_smul⟩ :=
    coord_of_compat_starIso_seq Γ π G f e_seq he_star he_compat
  refine ⟨⟨f, hf⟩, ?_⟩
  simp only [FormalGroupDeformation.map_mk, FormalGroupDeformation.mk_eq_mk_iff,
    FormalGroupLift.formalGroup_map]
  exact ⟨φ, hφ_map, hφ_smul⟩

end UniversalProofHelpers

section MainTheorem

/-- **Lubin–Tate universal deformation criterion.** Let `F₀` be a commutative formal group law of
finite height `h` over a field `k` of characteristic `p > 0`, and let `Γ` be a lift of `F₀` over
`R⟦t₁, …, t_{h-1}⟧` along `ρ ∘ constantCoeff` whose derivative cocycles `derivCocycle Γ ρ F₀ i`
vanish below degree `p ^ (i + 1)` with degree-`p ^ (i + 1)` component
`lazardCocycle (p ^ (i + 1)) k`. Then for every complete Noetherian local `R`-algebra `(A, π)`
with `π : A →+* k` local and `π ∘ algebraMap R A = ρ`, evaluating `Γ` at `R`-algebra
homomorphisms `f : R⟦t₁, …, t_{h-1}⟧ →ₐ[R] A` satisfying `π ∘ f = ρ ∘ constantCoeff` gives a
bijection onto `FormalGroupDeformation π F₀`. -/
theorem isUniversal_of_derivCocycle
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    Function.Bijective
      (fun f : {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A //
          π.comp f.toRingHom = ρ.comp constantCoeff} ↦
        FormalGroupDeformation.map f.val.toRingHom f.property ⟦⟨Γ, inferInstance, hΓ⟩⟧) :=
  ⟨isUniversal_injective hF₀ Γ hΓ hΓord hΓcomp π hπ,
    isUniversal_surjective hF₀ Γ hΓ hΓord hΓcomp π hπ⟩

/-- The equivalence from `R`-algebra homomorphisms `R⟦t₁, …, t_{h-1}⟧ →ₐ[R] A` compatible with
reduction to `k` onto `FormalGroupDeformation π F₀`. -/
@[expose]
def universalDeformationEquiv
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A // π.comp f.toRingHom = ρ.comp constantCoeff} ≃
      FormalGroupDeformation π F₀ :=
  Equiv.ofBijective _ (isUniversal_of_derivCocycle hF₀ Γ hΓ hΓord hΓcomp π hπ)

/-- Evaluating `universalDeformationEquiv` at `f` pushes forward the universal deformation `Γ`
along `f`. -/
@[simp]
theorem universalDeformationEquiv_apply
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ)
    (f : {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A //
      π.comp f.toRingHom = ρ.comp constantCoeff}) :
    universalDeformationEquiv hF₀ Γ hΓ hΓord hΓcomp π hπ f =
      FormalGroupDeformation.map f.val.toRingHom f.property ⟦⟨Γ, inferInstance, hΓ⟩⟧ :=
  rfl

/-- Parameter-tuple form of the universal deformation theorem: deformations of `F₀` over `A`
correspond bijectively to `(h - 1)`-tuples of elements in `maximalIdeal A`. -/
@[expose]
def universalDeformationMaximalIdealEquiv
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    (Fin (h - 1) → maximalIdeal A) ≃ FormalGroupDeformation π F₀ :=
  ((MvPowerSeries.algHomEquivMaximalIdeal (R := R) (σ := Fin (h - 1)) (A := A)).symm.trans
    (Equiv.subtypeEquivRight fun f ↦
      (MvPowerSeries.comp_eq_comp_constantCoeff_iff π ρ hπ f).symm)).trans
    (universalDeformationEquiv hF₀ Γ hΓ hΓord hΓcomp π hπ)

/-- Local-homomorphism form of the universal deformation theorem when `R` is local and `ρ` is
a local homomorphism: deformations correspond bijectively to local `R`-algebra homomorphisms
`R⟦t₁, …, t_{h-1}⟧ →ₐ[R] A`. -/
@[expose]
def universalDeformationLocalEquiv
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] [CharP k p]
    {ρ : R →+* k} [IsLocalHom ρ] {F₀ : FormalGroup k} [F₀.IsComm] (hF₀ : F₀.height p = h)
    (Γ : FormalGroup (MvPowerSeries (Fin (h - 1)) R)) [Γ.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀)
    (hΓord : ∀ i : Fin (h - 1), ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤ (derivCocycle Γ ρ F₀ i).order)
    (hΓcomp : ∀ i : Fin (h - 1),
      homogeneousComponent (p ^ (i + 1 : ℕ)) (derivCocycle Γ ρ F₀ i) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k))
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A // IsLocalHom f.toRingHom} ≃
      FormalGroupDeformation π F₀ :=
  (Equiv.subtypeEquivRight (fun f ↦
      (MvPowerSeries.isLocalHom_iff_comp_eq_comp_constantCoeff π ρ hπ f))).trans
    (universalDeformationEquiv hF₀ Γ hΓ hΓord hΓcomp π hπ)

/-- **The Lubin–Tate universal deformation theorem.** Given any commutative formal group law `F`
over `R` lifting a finite-height law `F₀` over `k` along `ρ : R →+* k`, the generic Lubin–Tate
law `F.lubinTateLaw hp h` over `R⟦t₁, …, t_{h-1}⟧` is a universal deformation of `F₀`: evaluation
induces a bijection from `R`-algebra homomorphisms compatible with reduction to `k` onto
`FormalGroupDeformation π F₀`. -/
theorem lubinTate_universal_deformation
    {p h : ℕ} [hp : Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} (F : FormalGroup R) [F.IsComm] {F₀ : FormalGroup k} [F₀.IsComm]
    (hF : F.map ρ = F₀) (hF₀ : F₀.height p = h)
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    Function.Bijective
      (fun f : {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A //
          π.comp f.toRingHom = ρ.comp constantCoeff} ↦
        FormalGroupDeformation.map f.val.toRingHom f.property
          (⟦⟨F.lubinTateLaw hp.out.one_lt h, inferInstance, by
            rw [← FormalGroup.map_comp, map_constantCoeff_lubinTateLaw, hF]⟩⟧ :
            FormalGroupDeformation (ρ.comp constantCoeff) F₀)) :=
  isUniversal_of_derivCocycle hF₀ (F.lubinTateLaw hp.out.one_lt h)
    (by rw [← FormalGroup.map_comp, map_constantCoeff_lubinTateLaw, hF])
    (fun i ↦ by rw [← hF]; exact le_order_derivCocycle_lubinTateLaw F hp.out.one_lt ρ i)
    (fun i ↦ by rw [← hF]; exact homogeneousComponent_derivCocycle_lubinTateLaw F hp.out.one_lt ρ i)
    π hπ

/-- Equivalence packaging `FormalGroup.lubinTate_universal_deformation`. -/
@[expose]
def lubinTateUniversalEquiv
    {p h : ℕ} [Fact p.Prime] {R k : Type*} [CommRing R] [Field k] [CharP k p]
    {ρ : R →+* k} (F : FormalGroup R) [F.IsComm] {F₀ : FormalGroup k} [F₀.IsComm]
    (hF : F.map ρ = F₀) (hF₀ : F₀.height p = h)
    {A : Type*} [CommRing A] [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (π : A →+* k) [IsLocalHom π] (hπ : π.comp (algebraMap R A) = ρ) :
    {f : MvPowerSeries (Fin (h - 1)) R →ₐ[R] A // π.comp f.toRingHom = ρ.comp constantCoeff} ≃
      FormalGroupDeformation π F₀ :=
  Equiv.ofBijective _ (lubinTate_universal_deformation F hF hF₀ π hπ)

end MainTheorem

end FormalGroup
