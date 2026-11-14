/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.AdicCompletion
public import TauCeti.RingTheory.FormalGroup.Deformation.Marked
public import TauCeti.RingTheory.FormalGroup.Height.Basic

import TauCeti.RingTheory.AdicCompletion.Nilpotent
import TauCeti.RingTheory.FormalGroup.Deformation.Rigidity
import TauCeti.RingTheory.LocalRing.RingHom
import TauCeti.RingTheory.PowerSeries.Coordinate.AdicCompletion
import TauCeti.RingTheory.PowerSeries.Coordinate.Lifting

/-!
# Formal group deformations over adic completions and complete local rings

Let `π : R →+* k` be a ring homomorphism and `I ≤ RingHom.ker π` an ideal of `R`. For each `n : ℕ`,
`π` factors through `R ⧸ I ^ (n + 1)` via `TauCeti.FormalGroupDeformation.quotientReduction hI n`,
and through `R ⧸ I` on `AdicCompletion I R` via
`TauCeti.FormalGroupDeformation.completionReduction hI`. This file compares formal group lifts and
their coordinate-change orbit sets over `AdicCompletion I R` (and, when `R` is `I`-adically
complete, over `R` itself) with compatible systems over the Artinian quotients `R ⧸ I ^ (n + 1)`:

* **Framed lifts (`TauCeti.FormalGroupLiftAdicSystem`)**: compatible systems of lifts over
  `R ⧸ I ^ (n + 1)` are canonically equivalent to lifts over `AdicCompletion I R`
  (`TauCeti.FormalGroupLiftAdicSystem.completionEquiv`) and, when `IsAdicComplete I R`, to lifts
  over `R` (`TauCeti.FormalGroupLiftAdicSystem.completeEquiv`), with no field, height, local, or
  finite-generation hypothesis.
* **Unconditional lifting of deformation systems
  (`TauCeti.FormalGroupDeformationAdicSystem.exists_liftSystem`)**: every compatible system of
  deformation classes over `R ⧸ I ^ (n + 1)` is represented by a compatible system of framed lifts,
  and therefore comes from a deformation over `AdicCompletion I R` (`ofCompletion_surjective`) and,
  when `IsAdicComplete I R`, over `R` (`ofRing_surjective`).
* **Finite-height equivalence (`TauCeti.FormalGroupDeformationAdicSystem.completionEquiv` and
  `completeEquiv`)**: when `k` is a field of characteristic `p`, `π` is surjective with `I = ker π`,
  and `F₀` has finite height, deformations over `AdicCompletion I R` (and over `I`-adically complete
  `R`) are canonically equivalent to compatible Artinian deformation systems, naturally in
  `(R, I, π)`.
* **Complete local rings (`TauCeti.FormalGroupDeformationAdicSystem.localCompleteEquiv` and
  `TauCeti.MarkedFormalGroupDeformation.localCompleteEquiv`)**: specializing to a complete local
  ring `(R, 𝔪)` with surjective augmentation `π : R →+* k` identifies both fixed-special-fibre and
  marked deformations of `F₀` over `R` with compatible systems of deformations over
  `R ⧸ 𝔪 ^ (n + 1)`.

No `I.FG` or Noetherian assumption is needed anywhere in this file.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*,
  Bull. Soc. Math. France 94 (1966).
-/

public section

noncomputable section

namespace TauCeti

namespace FormalGroupDeformation

section Reductions

variable {R S k : Type*} [CommRing R] [CommRing S] [CommRing k]
  {π : R →+* k} {ρ : S →+* k} {I : Ideal R} {J : Ideal S}

/-- When `I ≤ RingHom.ker π`, `π` factors through `R ⧸ I ^ (n + 1)` for every `n : ℕ` because
`I ^ (n + 1) ≤ I`. -/
def quotientReduction (hI : I ≤ RingHom.ker π) (n : ℕ) : R ⧸ I ^ (n + 1) →+* k :=
  Ideal.Quotient.lift (I ^ (n + 1)) π fun _ hr ↦
    RingHom.mem_ker.mp (hI (Ideal.pow_le_self n.succ_ne_zero hr))

/-- `quotientReduction hI n` sends the class of `r : R` to `π r`. -/
@[simp]
theorem quotientReduction_mk (hI : I ≤ RingHom.ker π) (n : ℕ) (r : R) :
    quotientReduction hI n (Ideal.Quotient.mk (I ^ (n + 1)) r) = π r := (rfl)

/-- Composing `quotientReduction hI n` with the quotient projection recovers `π`. -/
@[simp]
theorem quotientReduction_comp_mk (hI : I ≤ RingHom.ker π) (n : ℕ) :
    (quotientReduction hI n).comp (Ideal.Quotient.mk (I ^ (n + 1))) = π :=
  RingHom.ext fun _ ↦ rfl

/-- The reductions `quotientReduction hI` commute with the adic transition maps
`Ideal.Quotient.factorPow`. -/
@[simp]
theorem quotientReduction_comp_factorPow (hI : I ≤ RingHom.ker π) {m n : ℕ} (h : m ≤ n) :
    (quotientReduction hI m).comp (Ideal.Quotient.factorPow I (Nat.succ_le_succ h)) =
      quotientReduction hI n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)

/-- Base change of adic quotients along a homomorphism `f : R →+* S` over `k` commutes with
`quotientReduction`. -/
theorem quotientReduction_comp_quotientMap (hI : I ≤ RingHom.ker π) (hJ : J ≤ RingHom.ker ρ)
    (f : R →+* S) (hfI : I ≤ J.comap f) (hfπ : ρ.comp f = π) (n : ℕ) :
    (quotientReduction hJ n).comp
        (Ideal.quotientMap (J ^ (n + 1)) f
          ((Ideal.pow_right_mono hfI (n + 1)).trans (Ideal.le_comap_pow _ (n + 1)))) =
      quotientReduction hI n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ DFunLike.congr_fun hfπ r)

/-- If `π` is surjective, so is `quotientReduction hI n` at every level `n`. -/
theorem surjective_quotientReduction (hI : I ≤ RingHom.ker π) (hπ : Function.Surjective π)
    (n : ℕ) : Function.Surjective (quotientReduction hI n) := fun y ↦ by
  obtain ⟨r, hr⟩ := hπ y
  exact ⟨Ideal.Quotient.mk _ r, hr⟩

/-- When `I = RingHom.ker π`, the kernel of `quotientReduction hI n` is the image of `I` in
`R ⧸ I ^ (n + 1)`. -/
theorem ker_quotientReduction_eq_map (hI : I ≤ RingHom.ker π) (hker : RingHom.ker π ≤ I)
    (n : ℕ) :
    RingHom.ker (quotientReduction hI n) = I.map (Ideal.Quotient.mk (I ^ (n + 1))) := by
  refine le_antisymm (fun x hx ↦ ?_) (Ideal.map_le_iff_le_comap.mpr fun r hr ↦ hI hr)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.mem_map_of_mem _ (hker hx)

/-- When `π` is surjective and `I = RingHom.ker π`, `quotientReduction hI n` reflects units. -/
theorem isLocalHom_quotientReduction (hI : I ≤ RingHom.ker π) (hker : RingHom.ker π ≤ I)
    (hπ : Function.Surjective π) (n : ℕ) :
    IsLocalHom (quotientReduction hI n) := by
  refine RingHom.isLocalHom_of_surjective_of_isNilpotent_ker _
    (surjective_quotientReduction hI hπ n) fun x hx ↦ ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨n + 1, by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (hker hx) (n + 1)⟩

/-- When `I = RingHom.ker π`, `R ⧸ I ^ (n + 1)` is adically Hausdorff with respect to the kernel
of `quotientReduction hI n`. -/
theorem isHausdorff_ker_quotientReduction (hI : I ≤ RingHom.ker π) (hker : RingHom.ker π ≤ I)
    (n : ℕ) :
    IsHausdorff (RingHom.ker (quotientReduction hI n)) (R ⧸ I ^ (n + 1)) := by
  have hbot : (RingHom.ker (quotientReduction hI n)) ^ (n + 1) •
      (⊤ : Submodule (R ⧸ I ^ (n + 1)) (R ⧸ I ^ (n + 1))) = ⊥ := by
    rw [ker_quotientReduction_eq_map hI hker n, ← Ideal.map_pow, Ideal.map_quotient_self]
    simp
  exact (TauCeti.isAdicComplete_of_pow_smul_eq_bot hbot).toIsHausdorff

/-- Induced augmentation `AdicCompletion I R →+* k` factoring `π` through
`AdicCompletion.evalOneₐ I` when `I ≤ RingHom.ker π`. -/
def completionReduction (hI : I ≤ RingHom.ker π) : AdicCompletion I R →+* k :=
  (Ideal.Quotient.lift I π fun _ hr ↦ RingHom.mem_ker.mp (hI hr)).comp
    (AdicCompletion.evalOneₐ I).toRingHom

/-- `completionReduction hI` agrees with `quotientReduction hI n` after projecting to
`R ⧸ I ^ (n + 1)`. -/
@[simp]
theorem quotientReduction_comp_evalₐ (hI : I ≤ RingHom.ker π) (n : ℕ) :
    (quotientReduction hI n).comp (AdicCompletion.evalₐ I (n + 1)) =
      completionReduction hI := by
  ext x
  have heq : Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero)
      (AdicCompletion.evalₐ I (n + 1) x) = AdicCompletion.evalOneₐ I x := by
    rw [← AdicCompletion.factorₐ_evalₐ_one, ← AdicCompletion.factor_evalₐ n.succ_pos x]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
    simp [← hr]
  simp only [RingHom.comp_apply, completionReduction, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    ← heq]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  simp [← hr]

/-- Restricting `completionReduction hI` along `R → AdicCompletion I R` recovers `π`. -/
@[simp]
theorem completionReduction_comp_algebraMap (hI : I ≤ RingHom.ker π) :
    (completionReduction hI).comp (algebraMap R (AdicCompletion I R)) = π := by
  rw [completionReduction, RingHom.comp_assoc, AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
  exact RingHom.ext fun _ ↦ rfl

/-- Over an `I`-adically complete ring, `completionReduction hI` composed with
`AdicCompletion.ofAlgEquiv I` is `π`. -/
theorem completionReduction_comp_ofAlgEquiv [IsAdicComplete I R] (hI : I ≤ RingHom.ker π) :
    (completionReduction hI).comp (AdicCompletion.ofAlgEquiv I).toRingHom = π :=
  RingHom.ext fun r ↦ DFunLike.congr_fun (completionReduction_comp_algebraMap hI) r

/-- Over an `I`-adically complete ring, composing `π` with `(AdicCompletion.ofAlgEquiv I).symm`
recovers `completionReduction hI`. -/
theorem comp_ofAlgEquiv_symm [IsAdicComplete I R] (hI : I ≤ RingHom.ker π) :
    π.comp (AdicCompletion.ofAlgEquiv I).symm.toRingHom = completionReduction hI := by
  ext x
  simp [completionReduction, ← AdicCompletion.mk_ofAlgEquiv_symm_eq_evalOneₐ]

/-- Functorial maps between adic completions over `k` commute with `completionReduction`. -/
theorem completionReduction_comp_mapₐ (hI : I ≤ RingHom.ker π) (hJ : J ≤ RingHom.ker ρ)
    (f : R →+* S) (hfI : I ≤ J.comap f) (hfπ : ρ.comp f = π) :
    (completionReduction hJ).comp
        (AdicCompletion.mapₐ f.toIntAlgHom
          (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hfI)).toRingHom =
      completionReduction hI := by
  rw [← quotientReduction_comp_evalₐ hJ 0, ← quotientReduction_comp_evalₐ hI 0,
    RingHom.comp_assoc]
  have heval : (AdicCompletion.evalₐ J 1 : AdicCompletion J S →+* S ⧸ J ^ 1).comp
      (AdicCompletion.mapₐ f.toIntAlgHom
        (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hfI)).toRingHom =
      (Ideal.quotientMap (J ^ 1) f
        ((Ideal.pow_right_mono hfI 1).trans (Ideal.le_comap_pow _ 1))).comp
        (AdicCompletion.evalₐ I 1) :=
    RingHom.ext fun x ↦ AdicCompletion.evalₐ_mapₐ f.toIntAlgHom
      (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hfI) 1 x
  rw [heval, ← RingHom.comp_assoc, quotientReduction_comp_quotientMap hI hJ f hfI hfπ 0]

/-- If `π` is surjective, so is `completionReduction hI`. -/
theorem surjective_completionReduction (hI : I ≤ RingHom.ker π) (hπ : Function.Surjective π) :
    Function.Surjective (completionReduction hI) := fun y ↦ by
  obtain ⟨r, hr⟩ := hπ y
  exact ⟨algebraMap R (AdicCompletion I R) r,
    (DFunLike.congr_fun (completionReduction_comp_algebraMap hI) r).trans hr⟩

/-- When `π` is surjective and `I = RingHom.ker π`, `completionReduction hI` reflects units without
any finite-generation hypothesis on `I`. -/
theorem isLocalHom_completionReduction (hI : I ≤ RingHom.ker π) (hker : RingHom.ker π ≤ I)
    (hπ : Function.Surjective π) :
    IsLocalHom (completionReduction hI) := by
  have hlift : IsLocalHom (Ideal.Quotient.lift I π fun _ hr ↦ RingHom.mem_ker.mp (hI hr)) := by
    refine RingHom.isLocalHom_of_surjective_of_isNilpotent_ker _
      (fun y ↦ let ⟨r, hr⟩ := hπ y; ⟨Ideal.Quotient.mk I r, hr⟩) fun x hx ↦ ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨1, by simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hker hx)]⟩
  exact RingHom.isLocalHom_comp
    (Ideal.Quotient.lift I π fun _ hr ↦ RingHom.mem_ker.mp (hI hr))
    (AdicCompletion.evalOneₐ I).toRingHom

/-- Over an `I`-adically complete ring `R`, `AdicCompletion.ofAlgEquiv I` identifies deformations
along `π` with deformations along `completionReduction hI`, unconditionally. -/
def completeCompletionEquiv [IsAdicComplete I R] (hI : I ≤ RingHom.ker π) (F₀ : FormalGroup k) :
    FormalGroupDeformation π F₀ ≃ FormalGroupDeformation (completionReduction hI) F₀ where
  toFun := map (AdicCompletion.ofAlgEquiv I).toRingHom (completionReduction_comp_ofAlgEquiv hI)
  invFun := map (AdicCompletion.ofAlgEquiv I).symm.toRingHom (comp_ofAlgEquiv_symm hI)
  left_inv D := by
    induction D using Quotient.inductionOn with | _ F =>
    simp only [map_mk]
    refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
    rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map, FormalGroup.map_comp,
      ← FormalGroup.map_id F.formalGroup]
    exact congrArg F.formalGroup.map
      (RingHom.ext fun r ↦ (AdicCompletion.ofAlgEquiv I).symm_apply_apply r)
  right_inv D := by
    induction D using Quotient.inductionOn with | _ F =>
    simp only [map_mk]
    refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
    rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map, FormalGroup.map_comp,
      ← FormalGroup.map_id F.formalGroup]
    exact congrArg F.formalGroup.map
      (RingHom.ext fun x ↦ (AdicCompletion.ofAlgEquiv I).apply_symm_apply x)

end Reductions

end FormalGroupDeformation

section LiftSystem

variable {R k : Type*} [CommRing R] [CommRing k] {π : R →+* k} {I : Ideal R}

/-- Commutative lifts of `F₀` over all quotients `R ⧸ I ^ (n + 1)` along
`FormalGroupDeformation.quotientReduction hI n`, compatible with the adic transition maps
`Ideal.Quotient.factorPow`. -/
structure FormalGroupLiftAdicSystem (hI : I ≤ RingHom.ker π) (F₀ : FormalGroup k) where
  /-- The lift over `R ⧸ I ^ (n + 1)`. -/
  lift (n : ℕ) : FormalGroupLift (FormalGroupDeformation.quotientReduction hI n) F₀
  /-- Reduction from `I ^ (n + 1)` to `I ^ (m + 1)` recovers the lift at `m`. -/
  map_eq {m n : ℕ} (h : m ≤ n) :
    (lift n).map (Ideal.Quotient.factorPow I (Nat.succ_le_succ h))
      (FormalGroupDeformation.quotientReduction_comp_factorPow hI h) = lift m

namespace FormalGroupLiftAdicSystem

variable {hI : I ≤ RingHom.ker π} {F₀ : FormalGroup k}

/-- Two compatible systems of lifts are equal if they agree at every quotient level. -/
@[ext]
theorem ext {F G : FormalGroupLiftAdicSystem hI F₀} (h : ∀ n, F.lift n = G.lift n) : F = G := by
  cases F
  cases G
  congr
  exact funext h

/-- Construct a `FormalGroupLiftAdicSystem` from one-step compatibility along each transition
`R ⧸ I ^ (n + 2) →+* R ⧸ I ^ (n + 1)`. -/
def ofMapSucc (L : ∀ n : ℕ, FormalGroupLift (FormalGroupDeformation.quotientReduction hI n) F₀)
    (hstep : ∀ n : ℕ,
      (L (n + 1)).map (Ideal.Quotient.factorPow I (Nat.succ_le_succ n.le_succ))
        (FormalGroupDeformation.quotientReduction_comp_factorPow hI n.le_succ) = L n) :
    FormalGroupLiftAdicSystem hI F₀ where
  lift := L
  map_eq {m n} h := by
    induction n, h using Nat.le_induction with
    | base =>
      apply FormalGroupLift.ext
      rw [FormalGroupLift.formalGroup_map, ← FormalGroup.map_id (L m).formalGroup]
      exact congrArg (L m).formalGroup.map (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl))
    | succ n _ ih =>
      rw [← ih, ← hstep n]
      apply FormalGroupLift.ext
      simp only [FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
      exact congrArg (L (n + 1)).formalGroup.map
        (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl))

/-- `ofMapSucc` has the prescribed lift at level `n`. -/
@[simp]
theorem lift_ofMapSucc
    (L : ∀ n : ℕ, FormalGroupLift (FormalGroupDeformation.quotientReduction hI n) F₀)
    (hstep : ∀ n : ℕ,
      (L (n + 1)).map (Ideal.Quotient.factorPow I (Nat.succ_le_succ n.le_succ))
        (FormalGroupDeformation.quotientReduction_comp_factorPow hI n.le_succ) = L n)
    (n : ℕ) : (ofMapSucc L hstep).lift n = L n := (rfl)

/-- Underlying compatible system of commutative formal group laws over all `R ⧸ I ^ n`, obtained by
projecting `(F.lift k).formalGroup` from `R ⧸ I ^ (k + 1)` to `R ⧸ I ^ k`. -/
def toFormalGroupAdicSystem (F : FormalGroupLiftAdicSystem hI F₀) : FormalGroupAdicSystem I where
  formalGroup k := (F.lift k).formalGroup.map (Ideal.Quotient.factorPow I k.le_succ)
  isComm _ := inferInstance
  map_eq {k l} h := by
    have hcomp : (Ideal.Quotient.factorPow I h).comp (Ideal.Quotient.factorPow I l.le_succ) =
        (Ideal.Quotient.factorPow I k.le_succ).comp
          (Ideal.Quotient.factorPow I (Nat.succ_le_succ h)) :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
    rw [FormalGroup.map_comp, hcomp, ← FormalGroup.map_comp,
      ← FormalGroupLift.formalGroup_map (F.lift l) _
        (FormalGroupDeformation.quotientReduction_comp_factorPow hI h),
      F.map_eq h]

/-- At exponent `n + 1`, `toFormalGroupAdicSystem` recovers the law of `F.lift n`. -/
@[simp]
theorem formalGroup_succ_toFormalGroupAdicSystem (F : FormalGroupLiftAdicSystem hI F₀) (n : ℕ) :
    F.toFormalGroupAdicSystem.formalGroup (n + 1) = (F.lift n).formalGroup := by
  simpa only [toFormalGroupAdicSystem, FormalGroupLift.formalGroup_map] using
    congrArg FormalGroupLift.formalGroup (F.map_eq n.le_succ)

/-- Reduce a lift over `AdicCompletion I R` to a compatible system of lifts over
`R ⧸ I ^ (n + 1)`. -/
def ofCompletion (F : FormalGroupLift (FormalGroupDeformation.completionReduction hI) F₀) :
    FormalGroupLiftAdicSystem hI F₀ where
  lift n := F.map (AdicCompletion.evalₐ I (n + 1))
    (FormalGroupDeformation.quotientReduction_comp_evalₐ hI n)
  map_eq {m n} h := by
    apply FormalGroupLift.ext
    simp only [FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
    exact congrArg F.formalGroup.map
      (RingHom.ext fun x ↦ AdicCompletion.factor_evalₐ (Nat.succ_le_succ h) x)

/-- At level `n`, `ofCompletion F` is the reduction of `F` modulo `I ^ (n + 1)`. -/
@[simp]
theorem lift_ofCompletion (F : FormalGroupLift (FormalGroupDeformation.completionReduction hI) F₀)
    (n : ℕ) :
    (ofCompletion F).lift n = F.map (AdicCompletion.evalₐ I (n + 1))
      (FormalGroupDeformation.quotientReduction_comp_evalₐ hI n) := (rfl)

/-- Assemble a compatible system of lifts over `R ⧸ I ^ (n + 1)` into a lift over
`AdicCompletion I R`. -/
def limit (F : FormalGroupLiftAdicSystem hI F₀) :
    FormalGroupLift (FormalGroupDeformation.completionReduction hI) F₀ where
  formalGroup := F.toFormalGroupAdicSystem.limit
  isComm := inferInstance
  map_eq := by
    rw [← FormalGroupDeformation.quotientReduction_comp_evalₐ hI 0, ← FormalGroup.map_comp,
      F.toFormalGroupAdicSystem.map_limit (0 + 1),
      F.formalGroup_succ_toFormalGroupAdicSystem 0, (F.lift 0).map_eq]

/-- The formal group law of `F.limit` is the inverse limit of `F.toFormalGroupAdicSystem`. -/
@[simp]
theorem formalGroup_limit (F : FormalGroupLiftAdicSystem hI F₀) :
    F.limit.formalGroup = F.toFormalGroupAdicSystem.limit := (rfl)

/-- Reducing `F.limit` modulo `I ^ (n + 1)` recovers `F.lift n`. -/
@[simp]
theorem map_limit (F : FormalGroupLiftAdicSystem hI F₀) (n : ℕ) :
    F.limit.map (AdicCompletion.evalₐ I (n + 1))
      (FormalGroupDeformation.quotientReduction_comp_evalₐ hI n) = F.lift n := by
  apply FormalGroupLift.ext
  rw [FormalGroupLift.formalGroup_map, formalGroup_limit,
    F.toFormalGroupAdicSystem.map_limit (n + 1), F.formalGroup_succ_toFormalGroupAdicSystem]

/-- Reducing the inverse-limit lift recovers the original lift system. -/
@[simp]
theorem ofCompletion_limit (F : FormalGroupLiftAdicSystem hI F₀) :
    ofCompletion F.limit = F :=
  ext F.map_limit

/-- Taking the inverse limit of the quotient reductions of a lift over `AdicCompletion I R`
recovers that lift. -/
@[simp]
theorem limit_ofCompletion
    (F : FormalGroupLift (FormalGroupDeformation.completionReduction hI) F₀) :
    (ofCompletion F).limit = F :=
  FormalGroupLift.ext <| FormalGroup.ext_adicCompletion_succ fun n ↦ by
    simpa only [FormalGroupLift.formalGroup_map, lift_ofCompletion, AlgHom.toRingHom_eq_coe] using
      congrArg FormalGroupLift.formalGroup ((ofCompletion F).map_limit n)

/-- Lifts of `F₀` over `AdicCompletion I R` are canonically equivalent to compatible systems of
lifts over `R ⧸ I ^ (n + 1)`. -/
def completionEquiv (hI : I ≤ RingHom.ker π) (F₀ : FormalGroup k) :
    FormalGroupLift (FormalGroupDeformation.completionReduction hI) F₀ ≃
      FormalGroupLiftAdicSystem hI F₀ where
  toFun := ofCompletion
  invFun := limit
  left_inv := limit_ofCompletion
  right_inv := ofCompletion_limit

/-- `completionEquiv` sends a lift over the completion to its reductions modulo `I ^ (n + 1)`. -/
@[simp]
theorem lift_completionEquiv (hI : I ≤ RingHom.ker π) (F₀ : FormalGroup k)
    (F : FormalGroupLift (FormalGroupDeformation.completionReduction hI) F₀) (n : ℕ) :
    (completionEquiv hI F₀ F).lift n = F.map (AdicCompletion.evalₐ I (n + 1))
      (FormalGroupDeformation.quotientReduction_comp_evalₐ hI n) := (rfl)

/-- The inverse of `completionEquiv` is `limit`. -/
@[simp]
theorem completionEquiv_symm_apply (F : FormalGroupLiftAdicSystem hI F₀) :
    (completionEquiv hI F₀).symm F = F.limit := (rfl)

section BaseChange

variable {S T : Type*} [CommRing S] [CommRing T] {ρ : S →+* k} {τ : T →+* k}
  {J : Ideal S} {K : Ideal T} {hJ : J ≤ RingHom.ker ρ} {hK : K ≤ RingHom.ker τ}

/-- Extend coefficients in a system of lifts along a ring homomorphism `f : R →+* S` over `k`
carrying `I` into `J`. -/
def map (F : FormalGroupLiftAdicSystem hI F₀) (f : R →+* S) (hfI : I ≤ J.comap f)
    (hfπ : ρ.comp f = π) : FormalGroupLiftAdicSystem hJ F₀ where
  lift n := (F.lift n).map
    (Ideal.quotientMap (J ^ (n + 1)) f
      ((Ideal.pow_right_mono hfI (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))))
    (FormalGroupDeformation.quotientReduction_comp_quotientMap hI hJ f hfI hfπ n)
  map_eq {m n} h := by
    apply FormalGroupLift.ext
    simp only [FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
    rw [← (F.map_eq h), FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
    exact congrArg (F.lift n).formalGroup.map
      (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by simp))

/-- Base change of a lift system acts levelwise on quotient lifts. -/
@[simp]
theorem lift_map (F : FormalGroupLiftAdicSystem hI F₀) (f : R →+* S) (hfI : I ≤ J.comap f)
    (hfπ : ρ.comp f = π) (n : ℕ) :
    (F.map (hJ := hJ) f hfI hfπ).lift n = (F.lift n).map
      (Ideal.quotientMap (J ^ (n + 1)) f
        ((Ideal.pow_right_mono hfI (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))))
      (FormalGroupDeformation.quotientReduction_comp_quotientMap hI hJ f hfI hfπ n) := (rfl)

/-- Base change along the identity ring homomorphism fixes a lift system. -/
@[simp]
theorem map_id (F : FormalGroupLiftAdicSystem hI F₀) :
    F.map (hJ := hI) (RingHom.id R) (by simp) (RingHom.comp_id π) = F := by
  refine ext fun n ↦ FormalGroupLift.ext ?_
  rw [lift_map, FormalGroupLift.formalGroup_map, ← FormalGroup.map_id (F.lift n).formalGroup]
  exact congrArg (F.lift n).formalGroup.map
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by simp))

/-- Successive base changes of lift systems agree with their composite. -/
@[simp]
theorem map_comp (F : FormalGroupLiftAdicSystem hI F₀) (f : R →+* S) (hfI : I ≤ J.comap f)
    (hfπ : ρ.comp f = π) (g : S →+* T) (hgJ : J ≤ K.comap g) (hgρ : τ.comp g = ρ) :
    (F.map (hJ := hJ) f hfI hfπ).map (hJ := hK) g hgJ hgρ =
      F.map (hJ := hK) (g.comp f) (hfI.trans (Ideal.comap_mono hgJ))
        (by rw [← RingHom.comp_assoc, hgρ, hfπ]) := by
  refine ext fun n ↦ FormalGroupLift.ext ?_
  simp only [lift_map, FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
  exact congrArg (F.lift n).formalGroup.map
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by simp))

/-- Taking inverse limits of lift systems commutes with base change to adic completions. -/
theorem limit_map (F : FormalGroupLiftAdicSystem hI F₀) (f : R →+* S) (hfI : I ≤ J.comap f)
    (hfπ : ρ.comp f = π) :
    (F.map (hJ := hJ) f hfI hfπ).limit =
      F.limit.map
        (AdicCompletion.mapₐ f.toIntAlgHom
          (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hfI)).toRingHom
        (FormalGroupDeformation.completionReduction_comp_mapₐ hI hJ f hfI hfπ) := by
  refine FormalGroupLift.ext (FormalGroup.ext_adicCompletion_succ fun n ↦ ?_)
  simp only [AlgHom.toRingHom_eq_coe]
  have h1 := congrArg FormalGroupLift.formalGroup ((F.map (hJ := hJ) f hfI hfπ).map_limit n)
  rw [FormalGroupLift.formalGroup_map] at h1
  rw [h1, lift_map, FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map,
    FormalGroup.map_comp]
  have heval : (AdicCompletion.evalₐ J (n + 1) : AdicCompletion J S →+* S ⧸ J ^ (n + 1)).comp
      (AdicCompletion.mapₐ f.toIntAlgHom
        (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hfI)).toRingHom =
      (Ideal.quotientMap (J ^ (n + 1)) f
        ((Ideal.pow_right_mono hfI (n + 1)).trans (Ideal.le_comap_pow _ (n + 1)))).comp
        (AdicCompletion.evalₐ I (n + 1)) :=
    RingHom.ext fun x ↦ AdicCompletion.evalₐ_mapₐ f.toIntAlgHom
      (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hfI) (n + 1) x
  simp only [AlgHom.toRingHom_eq_coe] at heval
  rw [heval, ← FormalGroup.map_comp, ← FormalGroupLift.formalGroup_map F.limit _
    (FormalGroupDeformation.quotientReduction_comp_evalₐ hI n), F.map_limit n]

end BaseChange

section Complete

variable [IsAdicComplete I R]

/-- Realize a compatible system of quotient lifts directly over an `I`-adically complete ring
`R`. -/
def realize (F : FormalGroupLiftAdicSystem hI F₀) : FormalGroupLift π F₀ :=
  F.limit.map (AdicCompletion.ofAlgEquiv I).symm.toRingHom
    (FormalGroupDeformation.comp_ofAlgEquiv_symm hI)

/-- Reducing `F.realize` modulo `I ^ (n + 1)` recovers `F.lift n`. -/
@[simp]
theorem map_realize (F : FormalGroupLiftAdicSystem hI F₀) (n : ℕ) :
    F.realize.map (Ideal.Quotient.mk (I ^ (n + 1)))
      (FormalGroupDeformation.quotientReduction_comp_mk hI n) = F.lift n := by
  apply FormalGroupLift.ext
  rw [realize, FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map,
    FormalGroup.map_comp]
  have hmk : (Ideal.Quotient.mk (I ^ (n + 1))).comp (AdicCompletion.ofAlgEquiv I).symm.toRingHom =
      AdicCompletion.evalₐ I (n + 1) :=
    RingHom.ext fun x ↦ AdicCompletion.mk_ofAlgEquiv_symm I (n + 1) x
  rw [hmk, ← FormalGroupLift.formalGroup_map F.limit _
    (FormalGroupDeformation.quotientReduction_comp_evalₐ hI n), F.map_limit n]

/-- Realization of lift systems over adically complete rings commutes with base change. -/
theorem realize_map {S : Type*} [CommRing S] {ρ : S →+* k} {J : Ideal S} [IsAdicComplete J S]
    {hJ : J ≤ RingHom.ker ρ} (F : FormalGroupLiftAdicSystem hI F₀) (f : R →+* S)
    (hfI : I ≤ J.comap f) (hfπ : ρ.comp f = π) :
    (F.map (hJ := hJ) f hfI hfπ).realize = F.realize.map f hfπ := by
  refine FormalGroupLift.ext (FormalGroup.ext_adic_succ (I := J) fun n ↦ ?_)
  have h1 := congrArg FormalGroupLift.formalGroup ((F.map (hJ := hJ) f hfI hfπ).map_realize n)
  rw [FormalGroupLift.formalGroup_map] at h1
  rw [h1, lift_map, FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map,
    FormalGroup.map_comp,
    ← Ideal.quotientMap_comp_mk
      ((Ideal.pow_right_mono hfI (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))),
    ← FormalGroup.map_comp,
    ← FormalGroupLift.formalGroup_map F.realize _
      (FormalGroupDeformation.quotientReduction_comp_mk hI n),
    F.map_realize n]

/-- Over an `I`-adically complete ring `R`, lifts of `F₀` along `π` are canonically equivalent to
compatible systems of quotient lifts over `R ⧸ I ^ (n + 1)`. -/
def completeEquiv (hI : I ≤ RingHom.ker π) (F₀ : FormalGroup k) :
    FormalGroupLift π F₀ ≃ FormalGroupLiftAdicSystem hI F₀ where
  toFun F := ofCompletion
    (F.map (algebraMap R (AdicCompletion I R))
      (FormalGroupDeformation.completionReduction_comp_algebraMap hI))
  invFun := realize
  left_inv F := FormalGroupLift.ext <| FormalGroup.ext_adic_succ (I := I) fun n ↦ by
    have h1 := congrArg FormalGroupLift.formalGroup
      ((ofCompletion (F.map (algebraMap R (AdicCompletion I R))
        (FormalGroupDeformation.completionReduction_comp_algebraMap hI))).map_realize n)
    rw [FormalGroupLift.formalGroup_map] at h1
    rw [h1, lift_ofCompletion, FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map,
      FormalGroup.map_comp]
    exact congrArg F.formalGroup.map (RingHom.ext fun r ↦ AdicCompletion.evalₐ_of I (n + 1) r)
  right_inv F := ext fun n ↦ FormalGroupLift.ext <| by
    rw [lift_ofCompletion, FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map,
      FormalGroup.map_comp]
    have h : (AdicCompletion.evalₐ I (n + 1) : AdicCompletion I R →+* R ⧸ I ^ (n + 1)).comp
        (algebraMap R (AdicCompletion I R)) = Ideal.Quotient.mk (I ^ (n + 1)) :=
      RingHom.ext fun r ↦ AdicCompletion.evalₐ_of I (n + 1) r
    rw [h, ← FormalGroupLift.formalGroup_map F.realize _
      (FormalGroupDeformation.quotientReduction_comp_mk hI n), F.map_realize n]

/-- `completeEquiv` sends a lift over `R` to its reductions modulo `I ^ (n + 1)`. -/
@[simp]
theorem lift_completeEquiv (hI : I ≤ RingHom.ker π) (F₀ : FormalGroup k)
    (F : FormalGroupLift π F₀) (n : ℕ) :
    (completeEquiv hI F₀ F).lift n = F.map (Ideal.Quotient.mk (I ^ (n + 1)))
      (FormalGroupDeformation.quotientReduction_comp_mk hI n) := by
  apply FormalGroupLift.ext
  simp only [completeEquiv, Equiv.coe_fn_mk, lift_ofCompletion, FormalGroupLift.formalGroup_map,
    FormalGroup.map_comp]
  exact congrArg F.formalGroup.map (RingHom.ext fun r ↦ AdicCompletion.evalₐ_of I (n + 1) r)

/-- The inverse of `completeEquiv` is `realize`. -/
@[simp]
theorem completeEquiv_symm_apply (F : FormalGroupLiftAdicSystem hI F₀) :
    (completeEquiv hI F₀).symm F = F.realize := (rfl)

end Complete

end FormalGroupLiftAdicSystem

end LiftSystem

section DeformationSystem

variable {R k : Type*} [CommRing R] [CommRing k] {π : R →+* k} {I : Ideal R}

/-- Deformation classes of `F₀` over all quotients `R ⧸ I ^ (n + 1)` along
`FormalGroupDeformation.quotientReduction hI n`, compatible with the adic transition maps
`Ideal.Quotient.factorPow`. -/
structure FormalGroupDeformationAdicSystem (hI : I ≤ RingHom.ker π) (F₀ : FormalGroup k) where
  /-- The deformation class over `R ⧸ I ^ (n + 1)`. -/
  deformation (n : ℕ) : FormalGroupDeformation (FormalGroupDeformation.quotientReduction hI n) F₀
  /-- Reduction from `I ^ (n + 1)` to `I ^ (m + 1)` recovers the deformation class at `m`. -/
  map_eq {m n : ℕ} (h : m ≤ n) :
    FormalGroupDeformation.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ h))
      (FormalGroupDeformation.quotientReduction_comp_factorPow hI h) (deformation n) =
      deformation m

namespace FormalGroupDeformationAdicSystem

variable {hI : I ≤ RingHom.ker π} {F₀ : FormalGroup k}

/-- Two compatible systems of deformations are equal if they agree at every quotient level. -/
@[ext]
theorem ext {D E : FormalGroupDeformationAdicSystem hI F₀}
    (h : ∀ n, D.deformation n = E.deformation n) : D = E := by
  cases D
  cases E
  congr
  exact funext h

/-- Construct a `FormalGroupDeformationAdicSystem` from one-step compatibility along each
transition `R ⧸ I ^ (n + 2) →+* R ⧸ I ^ (n + 1)`. -/
def ofMapSucc
    (d : ∀ n : ℕ, FormalGroupDeformation (FormalGroupDeformation.quotientReduction hI n) F₀)
    (hstep : ∀ n : ℕ,
      FormalGroupDeformation.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ n.le_succ))
        (FormalGroupDeformation.quotientReduction_comp_factorPow hI n.le_succ) (d (n + 1)) =
        d n) :
    FormalGroupDeformationAdicSystem hI F₀ where
  deformation := d
  map_eq {m n} h := by
    induction n, h using Nat.le_induction with
    | base =>
      refine Quotient.inductionOn (d m) fun F ↦ ?_
      simp only [FormalGroupDeformation.map_mk]
      refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
      rw [FormalGroupLift.formalGroup_map, ← FormalGroup.map_id F.formalGroup]
      exact congrArg F.formalGroup.map (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl))
    | succ n _ ih =>
      rw [← ih, ← hstep n, FormalGroupDeformation.map_comp]
      refine Quotient.inductionOn (d (n + 1)) fun F ↦ ?_
      simp only [FormalGroupDeformation.map_mk]
      refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
      simp only [FormalGroupLift.formalGroup_map]
      exact congrArg F.formalGroup.map
        (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl))

/-- `ofMapSucc` has the prescribed deformation class at level `n`. -/
@[simp]
theorem deformation_ofMapSucc
    (d : ∀ n : ℕ, FormalGroupDeformation (FormalGroupDeformation.quotientReduction hI n) F₀)
    (hstep : ∀ n : ℕ,
      FormalGroupDeformation.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ n.le_succ))
        (FormalGroupDeformation.quotientReduction_comp_factorPow hI n.le_succ) (d (n + 1)) =
        d n)
    (n : ℕ) : (ofMapSucc d hstep).deformation n = d n := (rfl)

/-- Project a compatible system of framed lifts to its compatible system of deformation classes. -/
def ofLiftSystem (F : FormalGroupLiftAdicSystem hI F₀) :
    FormalGroupDeformationAdicSystem hI F₀ where
  deformation n := ⟦F.lift n⟧
  map_eq h := by rw [FormalGroupDeformation.map_mk, F.map_eq h]

/-- `ofLiftSystem F` at level `n` is the deformation class of `F.lift n`. -/
@[simp]
theorem deformation_ofLiftSystem (F : FormalGroupLiftAdicSystem hI F₀) (n : ℕ) :
    (ofLiftSystem F).deformation n = ⟦F.lift n⟧ := (rfl)

/-- Reduce a deformation over `AdicCompletion I R` to a compatible system of quotient
deformations. -/
def ofCompletion (D : FormalGroupDeformation (FormalGroupDeformation.completionReduction hI) F₀) :
    FormalGroupDeformationAdicSystem hI F₀ where
  deformation n := FormalGroupDeformation.map (AdicCompletion.evalₐ I (n + 1))
    (FormalGroupDeformation.quotientReduction_comp_evalₐ hI n) D
  map_eq {m n} h := by
    induction D using Quotient.inductionOn with | _ F =>
    simp only [FormalGroupDeformation.map_mk]
    exact congrArg Quotient.mk'' ((FormalGroupLiftAdicSystem.ofCompletion F).map_eq h)

/-- At level `n`, `ofCompletion D` is the reduction of `D` modulo `I ^ (n + 1)`. -/
@[simp]
theorem deformation_ofCompletion
    (D : FormalGroupDeformation (FormalGroupDeformation.completionReduction hI) F₀) (n : ℕ) :
    (ofCompletion D).deformation n =
      FormalGroupDeformation.map (AdicCompletion.evalₐ I (n + 1))
        (FormalGroupDeformation.quotientReduction_comp_evalₐ hI n) D := (rfl)

/-- On the class of a lift `F`, `ofCompletion` agrees with `ofLiftSystem` of the reduced lift
system. -/
@[simp]
theorem ofCompletion_mk
    (F : FormalGroupLift (FormalGroupDeformation.completionReduction hI) F₀) :
    ofCompletion ⟦F⟧ = ofLiftSystem (.ofCompletion F) :=
  ext fun _ ↦ FormalGroupDeformation.map_mk _ _ F

/-- Reduce a deformation over `R` to a compatible system of quotient deformations over
`R ⧸ I ^ (n + 1)`. -/
def ofRing (hI : I ≤ RingHom.ker π) (D : FormalGroupDeformation π F₀) :
    FormalGroupDeformationAdicSystem hI F₀ where
  deformation n := FormalGroupDeformation.map (Ideal.Quotient.mk (I ^ (n + 1)))
    (FormalGroupDeformation.quotientReduction_comp_mk hI n) D
  map_eq {m n} h := by
    induction D using Quotient.inductionOn with | _ F =>
    simp only [FormalGroupDeformation.map_mk]
    exact congrArg Quotient.mk'' (FormalGroupLift.ext <| by
      rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map,
        FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
      rfl)

/-- At level `n`, `ofRing hI D` is the reduction of `D` modulo `I ^ (n + 1)`. -/
@[simp]
theorem deformation_ofRing (hI : I ≤ RingHom.ker π) (D : FormalGroupDeformation π F₀) (n : ℕ) :
    (ofRing hI D).deformation n =
      FormalGroupDeformation.map (Ideal.Quotient.mk (I ^ (n + 1)))
        (FormalGroupDeformation.quotientReduction_comp_mk hI n) D := (rfl)

/-- Over an `I`-adically complete ring, `ofCompletion` composed with `completeCompletionEquiv` is
`ofRing`. -/
theorem ofCompletion_completeCompletionEquiv [IsAdicComplete I R]
    (D : FormalGroupDeformation π F₀) :
    ofCompletion (FormalGroupDeformation.completeCompletionEquiv hI F₀ D) = ofRing hI D := by
  induction D using Quotient.inductionOn with | _ F =>
  refine ext fun n ↦ ?_
  simp only [FormalGroupDeformation.completeCompletionEquiv, Equiv.coe_fn_mk,
    deformation_ofCompletion, deformation_ofRing, FormalGroupDeformation.map_mk]
  refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
  rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_map,
    FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
  exact congrArg F.formalGroup.map (RingHom.ext fun r ↦ AdicCompletion.evalₐ_of I (n + 1) r)

/-- **Unconditional lifting of deformation systems.** Every compatible system of deformation classes
over `R ⧸ I ^ (n + 1)` is represented by a compatible system of framed lifts. -/
theorem exists_liftSystem (D : FormalGroupDeformationAdicSystem hI F₀) :
    ∃ F : FormalGroupLiftAdicSystem hI F₀, ofLiftSystem F = D := by
  classical
  choose G₀ hG₀ using fun n ↦ Quotient.exists_rep (D.deformation n)
  let q (n : ℕ) := Ideal.Quotient.factorPow I (Nat.succ_le_succ n.le_succ)
  let hq (n : ℕ) := FormalGroupDeformation.quotientReduction_comp_factorPow hI n.le_succ
  have hrel (n : ℕ) :
      ∃ δ : (FormalCoordinate.map (FormalGroupDeformation.quotientReduction hI n)).ker,
        δ • (G₀ (n + 1)).map (q n) (hq n) = G₀ n := by
    have heq : (⟦(G₀ (n + 1)).map (q n) (hq n)⟧ :
        FormalGroupDeformation (FormalGroupDeformation.quotientReduction hI n) F₀) = ⟦G₀ n⟧ := by
      rw [← FormalGroupDeformation.map_mk, hG₀ (n + 1), D.map_eq n.le_succ, hG₀ n]
    obtain ⟨φ, hφ, hFG⟩ := (FormalGroupDeformation.mk_eq_mk_iff _ _).mp heq
    exact ⟨⟨φ, MonoidHom.mem_ker.mpr hφ⟩, FormalGroupLift.ext hFG⟩
  choose δ hδ using hrel
  have hsurj (n : ℕ) : Function.Surjective (FormalCoordinate.kerMap (q n) (hq n)) := by
    have : IsLocalHom (q n) :=
      Ideal.Quotient.isLocalHom_factorPow I n.succ_ne_zero (Nat.succ_le_succ n.le_succ)
    exact FormalCoordinate.kerMap_surjective_of_isLocalHom (q n)
      (Ideal.Quotient.factor_surjective _) (hq n)
  let ψ : ∀ n : ℕ, (FormalCoordinate.map (FormalGroupDeformation.quotientReduction hI n)).ker :=
    Nat.rec 1 fun n ψₙ ↦ Classical.choose (hsurj n (ψₙ * δ n))
  have hψ (n : ℕ) : FormalCoordinate.kerMap (q n) (hq n) (ψ (n + 1)) = ψ n * δ n :=
    Classical.choose_spec (hsurj n (ψ n * δ n))
  let L (n : ℕ) := ψ n • G₀ n
  have hstep (n : ℕ) : (L (n + 1)).map (q n) (hq n) = L n := by
    apply FormalGroupLift.ext
    rw [FormalGroupLift.formalGroup_map, FormalGroupLift.formalGroup_smul, FormalGroup.map_smul,
      ← FormalCoordinate.coe_kerMap (q n) (hq n) (ψ (n + 1)), hψ n, Subgroup.coe_mul, mul_smul,
      ← FormalGroupLift.formalGroup_map (G₀ (n + 1)) (q n) (hq n),
      ← FormalGroupLift.formalGroup_smul]
    exact congrArg (fun M : FormalGroupLift _ F₀ ↦ (ψ n).val • M.formalGroup) (hδ n)
  refine ⟨FormalGroupLiftAdicSystem.ofMapSucc L hstep, ext fun n ↦ ?_⟩
  have horb : MulAction.orbitRel
      (FormalCoordinate.map (FormalGroupDeformation.quotientReduction hI n)).ker
      (FormalGroupLift (FormalGroupDeformation.quotientReduction hI n) F₀) (L n) (G₀ n) :=
    MulAction.mem_orbit_iff.mpr ⟨ψ n, rfl⟩
  exact (Quotient.sound horb).trans (hG₀ n)

/-- Every compatible system of quotient deformations lifts unconditionally to a deformation over
`AdicCompletion I R`. -/
theorem ofCompletion_surjective :
    Function.Surjective (ofCompletion (hI := hI) (F₀ := F₀)) := fun D ↦ by
  obtain ⟨F, rfl⟩ := D.exists_liftSystem
  exact ⟨⟦F.limit⟧, by rw [ofCompletion_mk, F.ofCompletion_limit]⟩

/-- Over an `I`-adically complete ring `R`, every compatible system of quotient deformations lifts
unconditionally to a deformation over `R`. -/
theorem ofRing_surjective [IsAdicComplete I R] :
    Function.Surjective (ofRing hI (F₀ := F₀)) := fun D ↦ by
  obtain ⟨E, hE⟩ := ofCompletion_surjective D
  refine ⟨(FormalGroupDeformation.completeCompletionEquiv hI F₀).symm E, ?_⟩
  rw [← ofCompletion_completeCompletionEquiv, Equiv.apply_symm_apply, hE]

section BaseChange

variable {S T : Type*} [CommRing S] [CommRing T] {ρ : S →+* k} {τ : T →+* k}
  {J : Ideal S} {K : Ideal T} {hJ : J ≤ RingHom.ker ρ} {hK : K ≤ RingHom.ker τ}

/-- Extend coefficients in a compatible system of deformations along a ring homomorphism
`f : R →+* S` over `k` carrying `I` into `J`. -/
def map (D : FormalGroupDeformationAdicSystem hI F₀) (f : R →+* S) (hfI : I ≤ J.comap f)
    (hfπ : ρ.comp f = π) : FormalGroupDeformationAdicSystem hJ F₀ where
  deformation n := FormalGroupDeformation.map
    (Ideal.quotientMap (J ^ (n + 1)) f
      ((Ideal.pow_right_mono hfI (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))))
    (FormalGroupDeformation.quotientReduction_comp_quotientMap hI hJ f hfI hfπ n)
    (D.deformation n)
  map_eq {m n} h := by
    rw [FormalGroupDeformation.map_comp, ← D.map_eq h, FormalGroupDeformation.map_comp]
    refine Quotient.inductionOn (D.deformation n) fun F ↦ ?_
    simp only [FormalGroupDeformation.map_mk]
    refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
    simp only [FormalGroupLift.formalGroup_map]
    exact congrArg F.formalGroup.map
      (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by simp))

/-- Base change of a deformation system acts levelwise on quotient deformation classes. -/
@[simp]
theorem deformation_map (D : FormalGroupDeformationAdicSystem hI F₀) (f : R →+* S)
    (hfI : I ≤ J.comap f) (hfπ : ρ.comp f = π) (n : ℕ) :
    (D.map (hJ := hJ) f hfI hfπ).deformation n = FormalGroupDeformation.map
      (Ideal.quotientMap (J ^ (n + 1)) f
        ((Ideal.pow_right_mono hfI (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))))
      (FormalGroupDeformation.quotientReduction_comp_quotientMap hI hJ f hfI hfπ n)
      (D.deformation n) := (rfl)

/-- Base change along the identity ring homomorphism fixes a deformation system. -/
@[simp]
theorem map_id (D : FormalGroupDeformationAdicSystem hI F₀) :
    D.map (hJ := hI) (RingHom.id R) (by simp) (RingHom.comp_id π) = D := by
  refine ext fun n ↦ ?_
  rw [deformation_map]
  refine Quotient.inductionOn (D.deformation n) fun F ↦ ?_
  simp only [FormalGroupDeformation.map_mk]
  refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
  rw [FormalGroupLift.formalGroup_map, ← FormalGroup.map_id F.formalGroup]
  exact congrArg F.formalGroup.map
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by simp))

/-- Successive base changes of deformation systems agree with their composite. -/
@[simp]
theorem map_comp (D : FormalGroupDeformationAdicSystem hI F₀) (f : R →+* S) (hfI : I ≤ J.comap f)
    (hfπ : ρ.comp f = π) (g : S →+* T) (hgJ : J ≤ K.comap g) (hgρ : τ.comp g = ρ) :
    (D.map (hJ := hJ) f hfI hfπ).map (hJ := hK) g hgJ hgρ =
      D.map (hJ := hK) (g.comp f) (hfI.trans (Ideal.comap_mono hgJ))
        (by rw [← RingHom.comp_assoc, hgρ, hfπ]) := by
  refine ext fun n ↦ ?_
  simp only [deformation_map]
  refine Quotient.inductionOn (D.deformation n) fun F ↦ ?_
  simp only [FormalGroupDeformation.map_mk]
  refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
  simp only [FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
  exact congrArg F.formalGroup.map
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by simp))

/-- Projecting a lift system to a deformation system commutes with base change. -/
theorem ofLiftSystem_map (F : FormalGroupLiftAdicSystem hI F₀) (f : R →+* S) (hfI : I ≤ J.comap f)
    (hfπ : ρ.comp f = π) :
    ofLiftSystem (F.map (hJ := hJ) f hfI hfπ) = (ofLiftSystem F).map f hfI hfπ :=
  ext fun _ ↦ (FormalGroupDeformation.map_mk _ _ _).symm

/-- Reducing deformations from adic completions to deformation systems is natural in `(R, I, π)`. -/
theorem ofCompletion_map
    (D : FormalGroupDeformation (FormalGroupDeformation.completionReduction hI) F₀)
    (f : R →+* S) (hfI : I ≤ J.comap f) (hfπ : ρ.comp f = π) :
    ofCompletion
        (FormalGroupDeformation.map
          (AdicCompletion.mapₐ f.toIntAlgHom
            (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hfI)).toRingHom
          (FormalGroupDeformation.completionReduction_comp_mapₐ hI hJ f hfI hfπ) D) =
      (ofCompletion D).map (hJ := hJ) f hfI hfπ := by
  induction D using Quotient.inductionOn with | _ F =>
  refine ext fun n ↦ ?_
  simp only [deformation_ofCompletion, deformation_map, FormalGroupDeformation.map_mk]
  refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
  simp only [FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
  exact congrArg F.formalGroup.map (RingHom.ext fun x ↦
    AdicCompletion.evalₐ_mapₐ f.toIntAlgHom
      (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hfI) (n + 1) x)

/-- Reducing deformations over `R` to deformation systems is natural in `(R, I, π)`. -/
theorem ofRing_map (D : FormalGroupDeformation π F₀) (f : R →+* S) (hfI : I ≤ J.comap f)
    (hfπ : ρ.comp f = π) :
    ofRing hJ (FormalGroupDeformation.map f hfπ D) =
      (ofRing hI D).map (hJ := hJ) f hfI hfπ := by
  induction D using Quotient.inductionOn with | _ F =>
  refine ext fun n ↦ ?_
  simp only [deformation_ofRing, deformation_map, FormalGroupDeformation.map_mk]
  refine congrArg Quotient.mk'' (FormalGroupLift.ext ?_)
  simp only [FormalGroupLift.formalGroup_map, FormalGroup.map_comp]
  exact congrArg F.formalGroup.map (RingHom.ext fun r ↦
    (DFunLike.congr_fun
      (Ideal.quotientMap_comp_mk
        ((Ideal.pow_right_mono hfI (n + 1)).trans (Ideal.le_comap_pow _ (n + 1)))) r).symm)

end BaseChange

section FiniteHeight

variable {R k : Type*} [CommRing R] [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {π : R →+* k} {I : Ideal R}

/-- **Finite-height injectivity on the adic completion.** When `π : R →+* k` is surjective onto a
field of characteristic `p`, `I = RingHom.ker π`, and `F₀` has finite height, two deformations over
`AdicCompletion I R` with the same Artinian reductions modulo `I ^ (n + 1)` are equal. -/
theorem ofCompletion_injective (hI : I ≤ RingHom.ker π) (hker : RingHom.ker π ≤ I)
    (hπ : Function.Surjective π) {F₀ : FormalGroup k} {h : ℕ} (hF₀ : F₀.height p = h) :
    Function.Injective (ofCompletion (hI := hI) (F₀ := F₀)) := by
  intro D₁ D₂ hD
  induction D₁ using Quotient.inductionOn with | _ F =>
  induction D₂ using Quotient.inductionOn with | _ G =>
  let πₙ (n : ℕ) := FormalGroupDeformation.quotientReduction hI n
  have hπₙ (n : ℕ) : Function.Surjective (πₙ n) :=
    FormalGroupDeformation.surjective_quotientReduction hI hπ n
  have hloc (n : ℕ) : IsLocalHom (πₙ n) :=
    FormalGroupDeformation.isLocalHom_quotientReduction hI hker hπ n
  have hhaus (n : ℕ) : IsHausdorff (RingHom.ker (πₙ n)) (R ⧸ I ^ (n + 1)) :=
    FormalGroupDeformation.isHausdorff_ker_quotientReduction hI hker n
  let Fₛ := FormalGroupLiftAdicSystem.ofCompletion F
  let Gₛ := FormalGroupLiftAdicSystem.ofCompletion G
  have hex (n : ℕ) :
      ∃! φ : (FormalCoordinate.map (πₙ n)).ker, φ • Fₛ.lift n = Gₛ.lift n := by
    have := hloc n; have := hhaus n
    have hn : (⟦Fₛ.lift n⟧ : FormalGroupDeformation (πₙ n) F₀) = ⟦Gₛ.lift n⟧ := by
      simpa only [ofCompletion_mk, deformation_ofLiftSystem] using
        congrArg (fun E ↦ E.deformation n) hD
    exact FormalGroupDeformation.existsUnique_smul_eq_of_height_eq (hπₙ n) hF₀ hn
  choose c hc_smul hc_uniq using hex
  have hc_compat {m n : ℕ} (hle : m ≤ n) :
      FormalCoordinate.kerMap (Ideal.Quotient.factorPow I (Nat.succ_le_succ hle))
        (FormalGroupDeformation.quotientReduction_comp_factorPow hI hle) (c n) = c m := by
    refine hc_uniq m _ (FormalGroupLift.ext ?_)
    rw [FormalGroupLift.formalGroup_smul, FormalCoordinate.coe_kerMap,
      ← Fₛ.map_eq hle, ← Gₛ.map_eq hle, FormalGroupLift.formalGroup_map,
      FormalGroupLift.formalGroup_map, ← FormalGroup.map_smul, ← FormalGroupLift.formalGroup_smul]
    exact congrArg (fun M : FormalGroupLift _ F₀ ↦ M.formalGroup.map _) (hc_smul n)
  let Φ := FormalCoordinateAdicSystem.ofSucc (fun n ↦ (c n).val) fun hle ↦
    (FormalCoordinate.coe_kerMap _ _ (c _)).symm.trans (congrArg Subtype.val (hc_compat hle))
  refine (FormalGroupDeformation.mk_eq_mk_iff F G).mpr ⟨Φ.limit, ?_, ?_⟩
  · rw [← FormalGroupDeformation.quotientReduction_comp_evalₐ hI 0, FormalCoordinate.map_comp,
      Φ.map_limit (0 + 1), FormalCoordinateAdicSystem.coord_succ_ofSucc]
    exact MonoidHom.mem_ker.mp (c 0).property
  · refine FormalGroup.ext_adicCompletion_succ fun n ↦ ?_
    simp only [AlgHom.toRingHom_eq_coe]
    rw [FormalGroup.map_smul, Φ.map_limit (n + 1), FormalCoordinateAdicSystem.coord_succ_ofSucc]
    simpa only [Fₛ, Gₛ, FormalGroupLift.formalGroup_smul,
      FormalGroupLiftAdicSystem.lift_ofCompletion, FormalGroupLift.formalGroup_map] using
      congrArg FormalGroupLift.formalGroup (hc_smul n)

/-- **Adic inverse-limit equivalence for finite-height formal group deformations.** When
`π : R →+* k` is surjective onto a field of characteristic `p`, `I = RingHom.ker π`, and `F₀` has
finite height, deformations of `F₀` over `AdicCompletion I R` are canonically equivalent to
compatible systems of deformations over `R ⧸ I ^ (n + 1)`. -/
def completionEquiv (hI : I ≤ RingHom.ker π) (hker : RingHom.ker π ≤ I)
    (hπ : Function.Surjective π) {F₀ : FormalGroup k} {h : ℕ} (hF₀ : F₀.height p = h) :
    FormalGroupDeformation (FormalGroupDeformation.completionReduction hI) F₀ ≃
      FormalGroupDeformationAdicSystem hI F₀ :=
  Equiv.ofBijective ofCompletion ⟨ofCompletion_injective hI hker hπ hF₀, ofCompletion_surjective⟩

/-- `completionEquiv` acts by `ofCompletion`. -/
@[simp]
theorem completionEquiv_apply (hI : I ≤ RingHom.ker π) (hker : RingHom.ker π ≤ I)
    (hπ : Function.Surjective π) {F₀ : FormalGroup k} {h : ℕ} (hF₀ : F₀.height p = h)
    (D : FormalGroupDeformation (FormalGroupDeformation.completionReduction hI) F₀) :
    completionEquiv hI hker hπ hF₀ D = ofCompletion D := (rfl)

/-- Over an `I`-adically complete ring `R` with surjective augmentation `π : R →+* k` and
`I = RingHom.ker π`, two deformations of a finite-height law `F₀` with the same Artinian reductions
modulo `I ^ (n + 1)` are equal. -/
theorem ofRing_injective [IsAdicComplete I R] (hI : I ≤ RingHom.ker π) (hker : RingHom.ker π ≤ I)
    (hπ : Function.Surjective π) {F₀ : FormalGroup k} {h : ℕ} (hF₀ : F₀.height p = h) :
    Function.Injective (ofRing hI (F₀ := F₀)) := by
  have heq : ofRing hI (F₀ := F₀) =
      ofCompletion ∘ FormalGroupDeformation.completeCompletionEquiv hI F₀ :=
    funext fun D ↦ (ofCompletion_completeCompletionEquiv D).symm
  rw [heq]
  exact (ofCompletion_injective hI hker hπ hF₀).comp
    (FormalGroupDeformation.completeCompletionEquiv hI F₀).injective

/-- **Complete-ring inverse-limit equivalence for finite-height formal group deformations.** When
`R` is `I`-adically complete, `π : R →+* k` is surjective onto a field of characteristic `p`,
`I = RingHom.ker π`, and `F₀` has finite height, deformations of `F₀` over `R` are canonically
equivalent to compatible systems of deformations over `R ⧸ I ^ (n + 1)`. -/
def completeEquiv [IsAdicComplete I R] (hI : I ≤ RingHom.ker π) (hker : RingHom.ker π ≤ I)
    (hπ : Function.Surjective π) {F₀ : FormalGroup k} {h : ℕ} (hF₀ : F₀.height p = h) :
    FormalGroupDeformation π F₀ ≃ FormalGroupDeformationAdicSystem hI F₀ :=
  Equiv.ofBijective (ofRing hI) ⟨ofRing_injective hI hker hπ hF₀, ofRing_surjective⟩

/-- `completeEquiv` acts by `ofRing hI`. -/
@[simp]
theorem completeEquiv_apply [IsAdicComplete I R] (hI : I ≤ RingHom.ker π)
    (hker : RingHom.ker π ≤ I) (hπ : Function.Surjective π) {F₀ : FormalGroup k} {h : ℕ}
    (hF₀ : F₀.height p = h) (D : FormalGroupDeformation π F₀) :
    completeEquiv hI hker hπ hF₀ D = ofRing hI D := (rfl)

/-- Naturality of the inverse-limit realization `completeEquiv.symm` under coefficient extension
between complete rings. -/
theorem completeEquiv_symm_map {S : Type*} [CommRing S] {ρ : S →+* k} {J : Ideal S}
    [IsAdicComplete I R] [IsAdicComplete J S]
    (hI : I ≤ RingHom.ker π) (hkerI : RingHom.ker π ≤ I) (hπ : Function.Surjective π)
    (hJ : J ≤ RingHom.ker ρ) (hkerJ : RingHom.ker ρ ≤ J) (hρ : Function.Surjective ρ)
    {F₀ : FormalGroup k} {h : ℕ} (hF₀ : F₀.height p = h)
    (f : R →+* S) (hfI : I ≤ J.comap f) (hfπ : ρ.comp f = π)
    (D : FormalGroupDeformationAdicSystem hI F₀) :
    (completeEquiv hJ hkerJ hρ hF₀).symm (D.map (hJ := hJ) f hfI hfπ) =
      FormalGroupDeformation.map f hfπ ((completeEquiv hI hkerI hπ hF₀).symm D) := by
  apply (completeEquiv hJ hkerJ hρ hF₀).injective
  rw [Equiv.apply_symm_apply, completeEquiv_apply hJ hkerJ hρ hF₀, ofRing_map,
    ← completeEquiv_apply hI hkerI hπ hF₀, Equiv.apply_symm_apply]

end FiniteHeight

end FormalGroupDeformationAdicSystem

section LocalRing

open _root_.IsLocalRing

variable {R k : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {π : R →+* k} {F₀ : FormalGroup k}

/-- Over a complete local ring `(R, 𝔪)` with surjective augmentation `π : R →+* k` onto a field of
characteristic `p`, fixed-special-fibre deformations of a finite-height formal group law `F₀` over
`R` are canonically equivalent to compatible systems of deformations over the Artinian quotients
`R ⧸ 𝔪 ^ (n + 1)`. -/
def FormalGroupDeformationAdicSystem.localCompleteEquiv (hπ : Function.Surjective π) {h : ℕ}
    (hF₀ : F₀.height p = h) :
    FormalGroupDeformation π F₀ ≃
      FormalGroupDeformationAdicSystem (ker_eq_maximalIdeal π hπ).ge F₀ :=
  completeEquiv (ker_eq_maximalIdeal π hπ).ge (ker_eq_maximalIdeal π hπ).le hπ hF₀

/-- `localCompleteEquiv` sends a deformation over `(R, 𝔪)` to its reductions modulo
`𝔪 ^ (n + 1)`. -/
@[simp]
theorem FormalGroupDeformationAdicSystem.deformation_localCompleteEquiv
    (hπ : Function.Surjective π) {h : ℕ} (hF₀ : F₀.height p = h)
    (D : FormalGroupDeformation π F₀) (n : ℕ) :
    (FormalGroupDeformationAdicSystem.localCompleteEquiv hπ hF₀ D).deformation n =
      FormalGroupDeformation.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
        (FormalGroupDeformation.quotientReduction_comp_mk (ker_eq_maximalIdeal π hπ).ge n) D :=
  (rfl)

/-- Over a complete local ring `(R, 𝔪)` with surjective augmentation `π : R →+* k` onto a field of
characteristic `p`, marked deformations of a finite-height formal group law `F₀` over `R` are
canonically equivalent to compatible systems of deformations over `R ⧸ 𝔪 ^ (n + 1)`. -/
def MarkedFormalGroupDeformation.localCompleteEquiv (hπ : Function.Surjective π) {h : ℕ}
    (hF₀ : F₀.height p = h) :
    MarkedFormalGroupDeformation π F₀ ≃
      FormalGroupDeformationAdicSystem (ker_eq_maximalIdeal π hπ).ge F₀ :=
  have : IsLocalHom π := .of_surjective π hπ
  (FormalGroupDeformation.markedEquiv hπ
    (surjective_units_map_of_local_ringHom π hπ inferInstance)).symm.trans
    (FormalGroupDeformationAdicSystem.localCompleteEquiv hπ hF₀)

end LocalRing

end DeformationSystem

end TauCeti
