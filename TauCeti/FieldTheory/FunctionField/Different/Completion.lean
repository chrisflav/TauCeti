/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree

import TauCeti.FieldTheory.FunctionField.Different.Complementary
import TauCeti.FieldTheory.FunctionField.Different.Localization
import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension
import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.RingTheory.DedekindDomain.Different.Discriminant
import TauCeti.RingTheory.DedekindDomain.Different.DualFamily

/-!
# Compatibility of the trace-dual different with completion

Let `F' / k'` be an extension of the field extension `F / k` in which `F' / F` is finite and
separable, and let `P'` be a place of `F' / k'` lying over the place `P` of `F / k`. This file
proves that the trace-dual different survives completion at `P'`:

* the trace dual of `𝒪̂_{P'}` over `𝒪̂_P` is the `𝒪̂_{P'}`-span of the image of the trace dual of
  the local model `𝒪'_P` over `𝒪_P`;
* the different ideal `differentIdeal 𝒪_P 𝒪'_P` generates in `𝒪̂_{P'}` the different ideal
  `differentIdeal 𝒪̂_P 𝒪̂_{P'}`;
* consequently `differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`, and the multiplicity of the
  maximal ideal `𝔪̂_{P'}` in `differentIdeal 𝒪̂_P 𝒪̂_{P'}` equals the global different exponent
  `d(P' ∣ P)` (and the multiplicity of the different of any affine model on which `P'` is finite);
* the complementary-module quotient `Ĉ / 𝒪̂_{P'}`, the different quotient
  `𝒪̂_{P'} ⧸ differentIdeal 𝒪̂_P 𝒪̂_{P'}`, and the discriminant of any `𝒪̂_P`-basis of `𝒪̂_{P'}` all
  have `𝒪̂_P`-length / order `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full residue degree,
  including any inseparable factor.

No separability hypothesis on the residue extension `F'_{P'} / F_P`, no characteristic assumption,
and no function-field hypothesis are used: the theorems apply in particular to fierce extensions
with purely inseparable residue fields.

The comparison of trace duals avoids building a tensor-product isomorphism by working directly
with the semilocal spanning and trace theorems of
`TauCeti/FieldTheory/FunctionField/Place/Completion/Semilocal.lean` and the finite trace-dual
family of `TauCeti/RingTheory/DedekindDomain/Different/DualFamily.lean`, following the same
two-inclusion architecture as `TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Basic.lean`.

## Main definitions

* `TauCeti.Place.integralClosureToCompletionIntegers`: the canonical ring homomorphism from the
  local model `𝒪'_P` to the completed valuation ring `𝒪̂_{P'}`.

## Main results

* `TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`: a finite trace-dual expansion on `F'`
  transports to the completion at `P'`.
* `TauCeti.Place.span_traceDual_one_eq_traceDual_one_completionIntegers`: the local trace dual
  of `𝒪̂_{P'}` over `𝒪̂_P` is the `𝒪̂_{P'}`-span of the image of the global trace dual of `𝒪'_P`
  over `𝒪_P`.
* `TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers`: the different ideal of
  the local model generates in `𝒪̂_{P'}` the different ideal of `𝒪̂_{P'}` over `𝒪̂_P`.
* `TauCeti.Place.differentIdeal_completionIntegers_eq_pow_maximalIdeal`:
  `differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`.
* `TauCeti.Place.multiplicity_differentIdeal_completionIntegers` and
  `TauCeti.Place.multiplicity_differentIdeal_completionIntegers_eq_multiplicity_center`: the
  multiplicity of `𝔪̂_{P'}` in `differentIdeal 𝒪̂_P 𝒪̂_{P'}` is `d(P' ∣ P)`, matching the
  coefficient of the different ideal on any affine model.
* `TauCeti.Place.mem_traceDual_completionIntegers_iff`: valuation characterization of the
  completed complementary module.
* `TauCeti.Place.length_traceDual_quotient_completionIntegers` and
  `TauCeti.Place.length_quotient_differentIdeal_completionIntegers`: the `𝒪̂_P`-length of both the
  complementary-module quotient and `𝒪̂_{P'} ⧸ differentIdeal 𝒪̂_P 𝒪̂_{P'}` is
  `d(P' ∣ P) · f(P' ∣ P)`.
* `TauCeti.Place.ord_discr_completionIntegers` and
  `TauCeti.Place.completionPlace_ord_discr_completionIntegers`: the valuation of the discriminant
  of any `𝒪̂_P`-basis of `𝒪̂_{P'}` is `d(P' ∣ P) · f(P' ∣ P)`.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter III, §§2–4 (Proposition 10).
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.4 and Section IV.2.
* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter III, Proposition 2.2.
-/

public section

open IsDedekindDomain IsLocalRing Module
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti.Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section IntegralMap

variable [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- The canonical ring homomorphism from the local model `𝒪'_P` to the completed valuation ring
`𝒪̂_{P'}` at a place `P'` lying over `P`, sending `x ∈ 𝒪'_P` to `P'.completionEmbedding x`. -/
noncomputable def integralClosureToCompletionIntegers :
    integralClosure P.integers F' →+* P'.completionPlace.integers :=
  (P'.completionEmbedding.toRingHom.comp (integralClosure P.integers F').val).codRestrict
    P'.completionPlace.integers.toSubring fun x ↦ by
      have hx : (x : F') ∈ P'.integers := P'.mem_integers_of_isIntegral (R := P.integers)
        (fun a ↦ by
          rw [IsScalarTower.algebraMap_apply P.integers F F']
          exact (mem_integers_restrict_iff k F P' (a : F)).mp (hP ▸ a.2)) x.2
      simpa [completionIntegersEmbedding_apply] using (P'.completionIntegersEmbedding ⟨x, hx⟩).2

/-- The underlying element in `F̂'_{P'}` of `integralClosureToCompletionIntegers x` is
`P'.completionEmbedding x`. -/
@[simp]
theorem coe_integralClosureToCompletionIntegers (x : integralClosure P.integers F') :
    (P.integralClosureToCompletionIntegers P' hP x : P'.Completion) =
      P'.completionEmbedding (x : F') :=
  (rfl)

/-- The map from the local model `𝒪'_P` to the completed valuation ring `𝒪̂_{P'}` is injective. -/
theorem integralClosureToCompletionIntegers_injective :
    Function.Injective (P.integralClosureToCompletionIntegers P' hP) :=
  fun _ _ h ↦ Subtype.ext (P'.completionEmbedding.injective (congrArg Subtype.val h))

/-- The map from `𝒪'_P` to `𝒪̂_{P'}` is compatible with the valuation-ring embeddings from `𝒪_P`. -/
theorem integralClosureToCompletionIntegers_algebraMap (a : P.integers) :
    P.integralClosureToCompletionIntegers P' hP
        (algebraMap P.integers (integralClosure P.integers F') a) =
      P.completionIntegersExtension P' hP (P.completionIntegersEmbedding a) := by
  apply Subtype.ext
  simp [IsScalarTower.algebraMap_apply P.integers F F']

/-- On any element of `𝒪'_P`, the map to `𝒪̂_{P'}` agrees with `P'.completionIntegersEmbedding`. -/
theorem integralClosureToCompletionIntegers_eq_completionIntegersEmbedding
    (x : integralClosure P.integers F') (hx : (x : F') ∈ P'.integers) :
    P.integralClosureToCompletionIntegers P' hP x = P'.completionIntegersEmbedding ⟨x, hx⟩ :=
  Subtype.ext (by simp [completionIntegersEmbedding_apply])

end IntegralMap

section RestrictConstants

/-- View a place of `F' / k'` as a place of `F' / k` with the same valuation. -/
private abbrev restrictConstants (P' : Place k' F') : Place k F' where
  valuation := P'.valuation
  valuation_surjective := P'.valuation_surjective
  isTrivialOn := ⟨fun c hc ↦ by
    rw [IsScalarTower.algebraMap_apply k k' F']
    exact P'.isTrivialOn.eq_one _ ((map_ne_zero (algebraMap k k')).mpr hc)⟩

variable [Algebra.IsIntegral F F']

private theorem restrict_restrictConstants (P' : Place k' F') :
    (restrictConstants (k := k) P').restrict k F = P'.restrict k F := by
  refine Place.integers_injective (SetLike.ext fun x ↦ ?_)
  rw [mem_integers_restrict_iff, mem_integers_restrict_iff, mem_integers_iff, mem_integers_iff]

private theorem completionExtension_restrictConstants (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    P.completionExtension (restrictConstants (k := k) P')
        ((restrict_restrictConstants P').trans hP) =
      P.completionExtension P' hP :=
  P.eq_completionExtension_of_continuous P' hP (P.continuous_completionExtension _ _) fun x ↦ by
    rw [completionExtension_completionEmbedding, completionEmbedding_apply,
      completionEmbedding_apply]

private theorem completionExtensionAlgebra_restrictConstants (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    P.completionExtensionAlgebra (restrictConstants (k := k) P')
        ((restrict_restrictConstants P').trans hP) =
      P.completionExtensionAlgebra P' hP := by
  refine Algebra.algebra_ext _ _ fun r ↦ ?_
  rw [P.algebraMap_completionExtensionAlgebra _ _, P.algebraMap_completionExtensionAlgebra P' hP,
    completionExtension_restrictConstants]

end RestrictConstants

section TraceDual

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- Case `k' = k` of `sum_trace_mul_smul_completionEmbedding_eq`. -/
private theorem sum_trace_mul_smul_completionEmbedding_eq_self (P : Place k F) (P' : Place k F')
    (hP : P'.restrict k F = P) {n : ℕ} (b y : Fin n → F')
    (hb : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding (b i)) •
        P'.completionEmbedding (y i) = z := by
  classical
  let ι := {Q' : Place k F' // Q'.restrict k F = P}
  let _ := fun Q' : ι ↦ P.completionExtensionAlgebra Q'.1 Q'.2
  have := Fintype.ofFinite ι
  -- Assemble the local trace pairings on `∏_{Q' ∣ P} F̂'_{Q'}` into a single `F̂_P`-linear map.
  let L : (∀ Q' : ι, Q'.1.Completion) →ₗ[P.Completion] (∀ Q' : ι, Q'.1.Completion) :=
    { toFun w Q' := ∑ i, (∑ R' : ι,
          Algebra.trace P.Completion R'.1.Completion
            (w R' * R'.1.completionEmbedding (b i))) • Q'.1.completionEmbedding (y i)
      map_add' u v := funext fun Q' ↦ by
        simp only [Pi.add_apply, add_mul, map_add, Finset.sum_add_distrib, add_smul]
      map_smul' c u := funext fun Q' ↦ by
        simp only [Pi.smul_apply, smul_mul_assoc, map_smul, ← Finset.smul_sum, smul_assoc,
          RingHom.id_apply] }
  -- `L` fixes every diagonal vector by the trace formula, hence is the identity on `∏ F̂'_{Q'}`.
  have hdiag (x : F') : L (fun Q' : ι ↦ Q'.1.completionEmbedding x) =
      fun Q' : ι ↦ Q'.1.completionEmbedding x := by
    funext Q'
    have htr (i : Fin n) :
        ∑ R' : ι, Algebra.trace P.Completion R'.1.Completion
            (R'.1.completionEmbedding x * R'.1.completionEmbedding (b i)) =
          P.completionEmbedding (Algebra.trace F F' (x * b i)) := by
      simp_rw [← map_mul, ← finsum_eq_sum_of_fintype]
      exact (completionEmbedding_trace_of_isSeparable k P (x * b i)).symm
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, htr,
      ← completionEmbedding_smul P Q'.1 Q'.2, ← map_sum, hb x]
  have hL : ∀ w, L w = w := fun w ↦ by
    refine Submodule.span_induction (p := fun w _ ↦ L w = w) ?_ (map_zero L)
      (fun u v _ _ hu hv ↦ by rw [map_add, hu, hv])
      (fun c u _ hu ↦ by rw [map_smul, hu])
      ((span_completion_pi_eq_top k F' P).symm ▸ Submodule.mem_top)
    rintro _ ⟨x, rfl⟩
    exact hdiag x
  have hsingle := congrFun (hL (Pi.single (⟨P', hP⟩ : ι) z)) ⟨P', hP⟩
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same] at hsingle
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).symm.trans hsingle
  rw [Finset.sum_eq_single (⟨P', hP⟩ : ι)
    (fun R' _ hne ↦ by simp [Pi.single_eq_of_ne hne]) (fun h ↦ absurd (Finset.mem_univ _) h),
    Pi.single_eq_same]

/-- Case `k' = k` of `completionEmbedding_mem_traceDual_completionIntegers`. -/
private theorem completionEmbedding_mem_traceDual_completionIntegers_self (P : Place k F)
    (P' : Place k F') (hP : P'.restrict k F = P) {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F
      (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    P'.completionEmbedding d ∈
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  classical
  let ι := {Q' : Place k F' // Q'.restrict k F = P}
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  let _ := fun Q' : ι ↦ P.completionExtensionAlgebra Q'.1 Q'.2
  let _ := fun Q' : ι ↦ P.completionIntegersExtensionAlgebra Q'.1 Q'.2
  have := Fintype.ofFinite ι
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  -- Sum the local trace pairings across the fibre over `P`; on `Pi.single ⟨P', hP⟩ z` this
  -- recovers the single pairing at `P'`, and on diagonal integral vectors it is a global trace.
  let T (u : ∀ Q' : ι, Q'.1.completionPlace.integers) : P.Completion :=
    ∑ Q' : ι, Algebra.trace P.Completion Q'.1.Completion
      (Q'.1.completionEmbedding d * (u Q' : Q'.1.Completion))
  have hT_single : T (Pi.single (⟨P', hP⟩ : ι) z) =
      Algebra.traceForm P.Completion P'.Completion (P'.completionEmbedding d)
        (algebraMap P'.completionPlace.integers P'.Completion z) := by
    simp only [T, Algebra.traceForm_apply]
    rw [Finset.sum_eq_single (⟨P', hP⟩ : ι)
      (fun Q' _ hne ↦ by simp [Pi.single_eq_of_ne hne]) (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp
  rw [← hT_single]
  refine Submodule.span_induction
    (p := fun u _ ↦ T u ∈ (algebraMap P.completionPlace.integers P.Completion).range)
    ?_ ?_ ?_ ?_ ((span_completionIntegers_pi_eq_top k F' P).symm ▸ Submodule.mem_top)
  · rintro _ ⟨y, rfl⟩
    have hy : IsIntegral P.integers y.1 :=
      (isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable P).mpr fun Q' hQ' ↦
        y.2 ⟨Q', hQ'⟩
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd y.1 (Submodule.mem_one.mpr ⟨⟨y.1, hy⟩, rfl⟩)
    refine ⟨P.completionIntegersEmbedding r, ?_⟩
    have htr : T (fun Q' : ι ↦ Q'.1.completionIntegersEmbedding ⟨y.1, y.2 Q'⟩) =
        P.completionEmbedding (Algebra.trace F F' (d * y.1)) := by
      simp only [T, completionIntegersEmbedding_apply, ← map_mul, ← finsum_eq_sum_of_fintype]
      exact (completionEmbedding_trace_of_isSeparable k P (d * y.1)).symm
    rw [htr, ← Algebra.traceForm_apply, ← hr]
    simp [completionIntegersEmbedding_apply]
  · exact ⟨0, by simp [T]⟩
  · intro u v _ _ hu hv
    have hadd : T (u + v) = T u + T v := by
      simp only [T, Pi.add_apply, AddMemClass.coe_add, mul_add, map_add, Finset.sum_add_distrib]
    rw [hadd]
    exact add_mem hu hv
  · rintro a u _ ⟨c, hc⟩
    have hsmul : T (a • u) = (a : P.Completion) * T u := by
      have hterm (Q' : ι) :
          Q'.1.completionEmbedding d * ((a • u) Q' : Q'.1.Completion) =
            (a : P.Completion) • (Q'.1.completionEmbedding d * (u Q' : Q'.1.Completion)) := by
        rw [Pi.smul_apply, Algebra.smul_def, MulMemClass.coe_mul,
          coe_algebraMap_completionIntegersExtensionAlgebra, Algebra.smul_def,
          algebraMap_completionExtensionAlgebra, mul_left_comm]
      simp only [T, hterm, map_smul, smul_eq_mul, ← Finset.mul_sum]
    exact ⟨a * c, by rw [hsmul, ← hc, map_mul]; rfl⟩

variable (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- **Trace-dual identities transport to completions**: if a finite family `(bᵢ, yᵢ)` in `F'`
satisfies `∑ i, Tr_{F'/F}(x * bᵢ) • yᵢ = x` for every `x ∈ F'`, then its image in `F̂'_{P'}`
satisfies the same identity with `Tr_{F̂'_{P'}/F̂_P}` for every `z ∈ F̂'_{P'}`. -/
theorem sum_trace_mul_smul_completionEmbedding_eq {n : ℕ} (b y : Fin n → F')
    (hb : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding (b i)) •
        P'.completionEmbedding (y i) = z := by
  let P'₀ := restrictConstants (k := k) P'
  have hP₀ : P'₀.restrict k F = P := (restrict_restrictConstants P').trans hP
  have hA : P.completionExtensionAlgebra P'₀ hP₀ = P.completionExtensionAlgebra P' hP :=
    completionExtensionAlgebra_restrictConstants P P' hP
  have hE : (P'₀.completionEmbedding : F' → P'.Completion) = P'.completionEmbedding :=
    funext fun _ ↦ by rw [completionEmbedding_apply, completionEmbedding_apply]
  have key : ∀ (A : Algebra P.Completion P'.Completion) (f : F' → P'.Completion),
      A = P.completionExtensionAlgebra P'₀ hP₀ → f = P'₀.completionEmbedding →
      letI := A
      ∑ i, Algebra.trace P.Completion P'.Completion (z * f (b i)) • f (y i) = z := by
    rintro _ _ rfl rfl
    exact sum_trace_mul_smul_completionEmbedding_eq_self P P'₀ hP₀ b y hb z
  exact key _ _ hA.symm hE.symm

/-- The image in `F̂'_{P'}` of an element of the trace dual of `𝒪'_P` over `𝒪_P` lies in the
trace dual of `𝒪̂_{P'}` over `𝒪̂_P`. -/
private theorem completionEmbedding_mem_traceDual_completionIntegers {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F
      (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    P'.completionEmbedding d ∈
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let P'₀ := restrictConstants (k := k) P'
  have hP₀ : P'₀.restrict k F = P := (restrict_restrictConstants P').trans hP
  have hA : P.completionExtensionAlgebra P'₀ hP₀ = P.completionExtensionAlgebra P' hP :=
    completionExtensionAlgebra_restrictConstants P P' hP
  have hE : (P'₀.completionEmbedding : F' → P'.Completion) = P'.completionEmbedding :=
    funext fun _ ↦ by rw [completionEmbedding_apply, completionEmbedding_apply]
  have h₀ := completionEmbedding_mem_traceDual_completionIntegers_self P P'₀ hP₀ hd
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  have hz₀ : (z : P'.Completion) ∈ P'₀.completionPlace.integers := by
    rw [P'₀.completionPlace.mem_integers_iff, P'₀.completionPlace_valuation]
    exact P'.completionPlace_valuation _ ▸ P'.completionPlace.mem_integers_iff.mp z.2
  have key : ∀ (A : Algebra P.Completion P'.Completion) (f : F' → P'.Completion),
      A = P.completionExtensionAlgebra P'₀ hP₀ → f = P'₀.completionEmbedding →
      letI := A
      Algebra.traceForm P.Completion P'.Completion (f d) (z : P'.Completion) ∈
        (algebraMap P.completionPlace.integers P.Completion).range := by
    rintro _ _ rfl rfl
    let _ := P.completionExtensionAlgebra P'₀ hP₀
    let _ := P.completionIntegersExtensionAlgebra P'₀ hP₀
    exact Submodule.mem_traceDual.mp h₀ (z : P'.Completion)
      (Submodule.mem_one.mpr ⟨⟨z.1, hz₀⟩, rfl⟩)
  exact key _ _ hA.symm hE.symm

/-- **The local trace dual is spanned by the global one**: the trace dual of `𝒪̂_{P'}` over `𝒪̂_P`
is the `𝒪̂_{P'}`-span of the image in `F̂'_{P'}` of the trace dual of `𝒪'_P` over `𝒪_P`. -/
theorem span_traceDual_one_eq_traceDual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) =
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz ↦ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact completionEmbedding_mem_traceDual_completionIntegers P P' hP hd
  -- `𝒪'_P` is finite and torsion-free over the DVR `𝒪_P`, hence projective, so it admits a finite
  -- trace-dual family whose expansion transports to `F̂'_{P'}`.
  have := Module.finitePresentation_of_finite P.integers (integralClosure P.integers F')
  have : Module.Projective P.integers (integralClosure P.integers F') :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨n, b, y, hy, hb⟩ :=
    exists_sum_trace_mul_smul_eq P.integers F (L := F') (B := integralClosure P.integers F')
  rw [← sum_trace_mul_smul_completionEmbedding_eq P P' hP (fun i ↦ (b i : F')) y hb z]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _ (Submodule.mem_one.mpr
    ⟨P.integralClosureToCompletionIntegers P' hP (b i),
      coe_integralClosureToCompletionIntegers P P' hP (b i)⟩)
  rw [Algebra.traceForm_apply] at hc
  rw [← hc, algebraMap_smul]
  exact Submodule.smul_of_tower_mem _ c (Submodule.subset_span ⟨y i, hy i, rfl⟩)

/-- **Trace duals commute with completion**, as fractional ideals: extending the trace dual of
`𝒪'_P` over `𝒪_P` along `𝒪'_P → 𝒪̂_{P'}` gives the trace dual of `𝒪̂_{P'}` over `𝒪̂_P`. -/
private theorem extended_dual_one_eq_dual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.finiteDimensional_completion P' hP
    haveI := P.isSeparable_completion P' hP
    haveI := P.isIntegralClosure_completionIntegers P' hP
    (FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')).extended P'.Completion
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (P.integralClosureToCompletionIntegers_injective P' hP)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal (P'.completionPlace.integers)⁰ P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isSeparable_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have hmap : IsLocalization.map (S := F') P'.Completion
      (P.integralClosureToCompletionIntegers P' hP)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (P.integralClosureToCompletionIntegers_injective P' hP)) =
      P'.completionEmbedding.toRingHom := by
    refine IsFractionRing.ringHom_ext (A := integralClosure P.integers F') fun x ↦ ?_
    rw [IsLocalization.map_eq]
    rfl
  have hdual : ((FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')) : Set F') =
      Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coeToSubmodule_dual_one]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_extended_eq_span,
    hmap, hdual, FractionalIdeal.coeToSubmodule_dual_one]
  exact span_traceDual_one_eq_traceDual_one_completionIntegers P P' hP

/-- **The different ideal commutes with completion** (Serre, *Local Fields*, Chapter III, §4,
Proposition 10): the different ideal of the local model `𝒪'_P / 𝒪_P` generates in `𝒪̂_{P'}` the
different ideal of `𝒪̂_{P'} / 𝒪̂_P`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (P.integralClosureToCompletionIntegers P' hP) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isSeparable_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  rw [← FractionalIdeal.coeIdeal_inj (K := P'.Completion),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := F') P'.Completion
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (P.integralClosureToCompletionIntegers_injective P' hP)),
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal P.integers F F' (integralClosure P.integers F'),
    coeIdeal_differentIdeal P.completionPlace.integers P.Completion P'.Completion
      P'.completionPlace.integers,
    map_inv₀, FractionalIdeal.extendedHom'_apply,
    extended_dual_one_eq_dual_one_completionIntegers P P' hP]

end TraceDual

section Invariants

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']
variable (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- **The completed different ideal is the `d(P' ∣ P)`-th power of the maximal ideal**:
`differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`. -/
theorem differentIdeal_completionIntegers_eq_pow_maximalIdeal :
    letI := P.completionIntegersExtensionAlgebra P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  rw [← map_differentIdeal_eq_differentIdeal_completionIntegers (P'.restrict k F) P' rfl]
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_) fun z hz ↦ ?_
  · rcases eq_or_ne y 0 with rfl | hy0
    · simp
    rw [Ideal.mem_comap, mem_maximalIdeal_pow_iff_coe_mem_filtration,
      coe_integralClosureToCompletionIntegers, completionEmbedding_mem_filtration_iff,
      P'.mem_filtration_iff_le_ord (by simpa using hy0)]
    exact differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0
  · obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
    set y' := (P'.restrict k F).integralClosureToCompletionIntegers P' rfl y
    have hy'0 : (y' : P'.Completion) ≠ 0 := by
      simp [y', hy0]
    have hord' : P'.completionPlace.ord (y' : P'.Completion) = differentExponent k F P' := by
      simpa [y'] using hord
    have hzfil : (z : P'.Completion) ∈ P'.completionPlace.filtration (differentExponent k F P') :=
      (P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration _ z).mp hz
    have hinv : (y' : P'.Completion)⁻¹ ∈
        P'.completionPlace.filtration (-(differentExponent k F P' : ℤ)) := by
      rw [P'.completionPlace.mem_filtration_iff_le_ord (inv_ne_zero hy'0),
        P'.completionPlace.ord_inv, hord']
    have hu : (z : P'.Completion) * (y' : P'.Completion)⁻¹ ∈ P'.completionPlace.integers := by
      have hmul := P'.completionPlace.mul_mem_filtration hzfil hinv
      rwa [add_neg_cancel, mem_filtration_zero_iff] at hmul
    have hzu : z = y' * ⟨_, hu⟩ := Subtype.ext (by
      rw [MulMemClass.coe_mul, mul_left_comm, mul_inv_cancel₀ hy'0, mul_one])
    rw [hzu]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hy)

/-- **The different exponent survives completion**: the multiplicity of the maximal ideal of
`𝒪̂_{P'}` in `differentIdeal 𝒪̂_P 𝒪̂_{P'}` equals `d(P' ∣ P)`, with no separability hypothesis on
the residue extension. -/
theorem multiplicity_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [differentIdeal_completionIntegers_eq_pow_maximalIdeal P P' hP]
  have hprime : Prime (maximalIdeal P'.completionPlace.integers) :=
    Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance
  exact multiplicity_pow_self_of_prime hprime _

/-- **Affine-model compatibility with completion**: on any affine model `B` of `F` with integral
closure `C` in `F'` on which `P'` is finite, the multiplicity of the maximal ideal of `𝒪̂_{P'}` in
the completed different ideal equals the coefficient of `differentIdeal B C` at the centre of
`P'`. -/
theorem multiplicity_differentIdeal_completionIntegers_eq_multiplicity_center
    {B C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
    [CommRing C] [IsDedekindDomain C] [Algebra C F'] [IsFractionRing C F']
    [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
    [IsIntegralClosure C B F'] [Module.IsTorsionFree B C]
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      multiplicity (P'.center hC).asIdeal (differentIdeal B C) := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [multiplicity_differentIdeal_completionIntegers P P' hP,
    differentExponent_eq_multiplicity_center (B := B) (C := C) P' hC]

/-- **Valuation characterization of the completed complementary module**: an element `z ∈ F̂'_{P'}`
belongs to the trace dual of `𝒪̂_{P'}` over `𝒪̂_P` if and only if
`v_{P'}(z) ≤ exp d(P' ∣ P)`. -/
theorem mem_traceDual_completionIntegers_iff {z : P'.Completion} :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    z ∈ Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      P'.completionPlace.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isSeparable_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  rw [mem_traceDual_one_iff_forall_mem_differentIdeal,
    differentIdeal_completionIntegers_eq_pow_maximalIdeal P P' hP]
  refine ⟨fun hz ↦ ?_, fun hz y hy ↦ ?_⟩
  · obtain ⟨t, ht⟩ := P'.completionPlace.exists_isUniformizer
    have ht0 : t ≠ 0 := ht.ne_zero
    have htord : P'.completionPlace.ord t = 1 :=
      P'.completionPlace.isUniformizer_iff_ord_eq_one.mp ht
    let t₀ : P'.completionPlace.integers :=
      ⟨t, P'.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
    have hmem : t₀ ^ differentExponent k F P' ∈
        maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
      rw [mem_maximalIdeal_pow_iff_coe_mem_filtration, Subring.coe_pow,
        P'.completionPlace.mem_filtration_iff_le_ord (pow_ne_zero _ ht0),
        P'.completionPlace.ord_pow, htord, mul_one]
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hz _ hmem)
    have hmul : (b : P'.Completion) = z * t ^ differentExponent k F P' := by
      simpa [t₀] using hb
    have hle : P'.completionPlace.valuation (z * t ^ differentExponent k F P') ≤ 1 := by
      rw [← hmul]
      exact P'.completionPlace.mem_integers_iff.mp b.2
    rw [map_mul, P'.completionPlace.valuation_eq_exp_neg_ord (pow_ne_zero _ ht0),
      P'.completionPlace.ord_pow, htord, mul_one] at hle
    calc P'.completionPlace.valuation z
        = P'.completionPlace.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ)) *
            WithZero.exp (differentExponent k F P' : ℤ) := by
          rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ ≤ 1 * WithZero.exp (differentExponent k F P' : ℤ) := by gcongr
      _ = WithZero.exp (differentExponent k F P' : ℤ) := one_mul _
  · have hyval : P'.completionPlace.valuation (y : P'.Completion) ≤
        WithZero.exp (-(differentExponent k F P' : ℤ)) :=
      P'.completionPlace.mem_filtration_iff.mp
        ((P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration _ y).mp hy)
    have hprod : P'.completionPlace.valuation (z * (y : P'.Completion)) ≤ 1 := by
      rw [map_mul]
      calc P'.completionPlace.valuation z * P'.completionPlace.valuation (y : P'.Completion)
          ≤ WithZero.exp (differentExponent k F P' : ℤ) *
              WithZero.exp (-(differentExponent k F P' : ℤ)) := by gcongr
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    exact Submodule.mem_one.mpr ⟨⟨z * (y : P'.Completion),
      P'.completionPlace.mem_integers_iff.mpr hprod⟩, rfl⟩

/-- **The length of the completed complementary-module quotient**: the `𝒪̂_P`-length of
`Ĉ / 𝒪̂_{P'}` is `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full residue degree, including
any inseparable factor. -/
theorem length_traceDual_quotient_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.length P.completionPlace.integers
        ((Submodule.traceDual P.completionPlace.integers P.Completion
            (1 : Submodule P'.completionPlace.integers P'.Completion)) ⧸
          (1 : Submodule P'.completionPlace.integers P'.Completion).comap
            (Submodule.traceDual P.completionPlace.integers P.Completion
              (1 : Submodule P'.completionPlace.integers P'.Completion)).subtype) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).finiteDimensional_completion P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  have := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have : Module.Finite (P'.restrict k F).completionPlace.ResidueField
      P'.completionPlace.ResidueField :=
    Module.finite_of_finrank_pos (by
      rw [P'.finrank_residueField_completion (k := k) (F := F)]
      exact one_le_relativeDegree k F P')
  rw [length_traceDual_quotient_eq_multiplicity_mul_finrank,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

/-- **The length of the completed different quotient**: the `𝒪̂_P`-length of
`𝒪̂_{P'} ⧸ differentIdeal 𝒪̂_P 𝒪̂_{P'}` is `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full
residue degree, including any inseparable factor. -/
theorem length_quotient_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.length P.completionPlace.integers
        (P'.completionPlace.integers ⧸
          differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isSeparable_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  rw [← length_traceDual_quotient_eq_length_quotient_differentIdeal
      (K := P.Completion) (L := P'.Completion)]
  exact length_traceDual_quotient_completionIntegers P P' hP

/-- **The discriminant of a completed integral basis**: for any `𝒪̂_P`-basis `b` of `𝒪̂_{P'}`, the
order of vanishing of `discr 𝒪̂_P b` in `𝒪̂_P` is `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the
full residue degree, including any inseparable factor. -/
theorem ord_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : letI := P.completionIntegersExtensionAlgebra P' hP
      Module.Basis ι P.completionPlace.integers P'.completionPlace.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  have := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  rw [ord_discr_eq_multiplicity_mul_finrank (P'.restrict k F).Completion P'.Completion b,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

/-- **The place order of the discriminant of a completed integral basis**: for any `𝒪̂_P`-basis
`b` of `𝒪̂_{P'}`, `ord_P (discr 𝒪̂_P b) = d(P' ∣ P) · f(P' ∣ P)` as integers. -/
theorem completionPlace_ord_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : letI := P.completionIntegersExtensionAlgebra P' hP
      Module.Basis ι P.completionPlace.integers P'.completionPlace.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    P.completionPlace.ord (Algebra.discr P.completionPlace.integers b : P.Completion) =
      (differentExponent k F P' : ℤ) * relativeDegree k F P' := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  set Δ := Algebra.discr P.completionPlace.integers b
  have hord : Ring.ord P.completionPlace.integers Δ =
      ((differentExponent k F P' * relativeDegree k F P' : ℕ) : ℕ∞) := by
    simpa [Nat.cast_mul] using ord_discr_completionIntegers P P' hP b
  have hΔ0 : Δ ≠ 0 := by
    intro h0
    rw [h0, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero] at hord
    exact ENat.top_ne_natCast _ hord
  have hval : Ring.ord P.completionPlace.integers Δ =
      ((P.completionPlace.ord (Δ : P.Completion)).toNat : ℕ∞) := by
    rw [Ring.ord_eq_addVal]
    refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
    rw [← TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal,
      P.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration,
      P.completionPlace.mem_filtration_iff_le_ord (by simpa using hΔ0), Nat.cast_le]
    have := P.completionPlace.mem_integers_iff_ord_nonneg.mp Δ.2
    omega
  have hnat : (P.completionPlace.ord (Δ : P.Completion)).toNat =
      differentExponent k F P' * relativeDegree k F P' :=
    Nat.cast_injective (hval.symm.trans hord)
  have hnonneg : 0 ≤ P.completionPlace.ord (Δ : P.Completion) :=
    P.completionPlace.mem_integers_iff_ord_nonneg.mp Δ.2
  omega

end Invariants

end TauCeti.Place
