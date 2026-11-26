/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.FormalGroup.Deformation.DerivCocycle
public import TauCeti.RingTheory.FormalGroup.Deformation.LocalAlgHom
public import TauCeti.RingTheory.FormalGroup.Deformation.StarIso
-- Proof-only: multivariate substitution and Artinian completeness helpers.
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.RingTheory.MvPowerSeries.Ideal

/-!
# Square-zero quotient-step tools for formal group deformations

This file supplies the square-zero extension and cocycle infrastructure used in the inductive proof
of the Lubin–Tate universal deformation theorem (`TauCeti.RingTheory.FormalGroup.Deformation`):

* First-order Taylor expansion in small extensions `t : B →+* B'` (`ker p_B * ker t = ⊥`) and
  the finite-dimensional `ResidueField A`-vector space structure on `RingHom.ker t`
  (`FormalGroup.jModule`, `FormalGroup.projL`, `FormalGroup.mkJ`), together with compatibility
  with multivariate substitution, additive coboundaries `homDefect 𝔾ₐ`, and symmetric
  2-cocycles.
* The Taylor difference identity relating two lifts `f₀, f₁ : R⟦σ⟧ →ₐ[R] B` to
  `FormalGroup.derivCocycle` (`FormalGroup.invariantDifferential_mul_map_sub_map`).
-/

public section

noncomputable section

open IsLocalRing MvPowerSeries TauCeti

/-! ### Square-zero quotient steps and residue-field module operations -/

namespace FormalGroup

/-- An ideal `I` with `I ^ n = ⊥` makes the ambient ring `I`-adically complete. -/
theorem isAdicComplete_of_pow_eq_bot {B : Type*} [CommRing B] {I : Ideal B} {n : ℕ}
    (hn : I ^ n = ⊥) : IsAdicComplete I B where
  haus' x hx := by
    have := hx n
    simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top, hn] using this
  prec' f hf := by
    refine ⟨f n, fun k ↦ ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    rcases le_or_gt k n with hkn | hnk
    · simpa [SModEq.sub_mem] using hf hkn
    · have hfnk : f n - f k ∈ I ^ n := by simpa [SModEq.sub_mem] using hf hnk.le
      have hzero : f k - f n = 0 := by
        rw [← Ideal.mem_bot, ← hn]
        simpa [neg_sub] using (I ^ n).neg_mem hfnk
      rw [hzero]
      exact Ideal.zero_mem _

/-- For a local homomorphism `π : A →+* k` into a field `k`, the kernel of `π` equals
`maximalIdeal A`. -/
theorem ker_eq_maximalIdeal_of_field {A k : Type*} [CommRing A] [IsLocalRing A] [Field k]
    (π : A →+* k) [IsLocalHom π] : RingHom.ker π = maximalIdeal A := by
  ext a
  rw [RingHom.mem_ker, mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h0 hu
    exact (hu.map π).ne_zero h0
  · intro hnu
    by_contra h0
    exact hnu (IsUnit.of_map π _ (isUnit_iff_ne_zero.mpr h0))

section QuotientStep

variable {B B' K : Type*} [CommRing B] [CommRing B'] [Field K]

/-- On `Ideal.span (Set.range X) ^ 2`, any two `R`-algebra homs `f₀, f₁ : R⟦σ⟧ →ₐ[R] B`
that agree modulo `t : B →+* B'` and send every `X i` into `ker p_B`, where
`ker p_B * ker t = ⊥`, take identical values. -/
theorem apply_eq_of_mem_span_range_X_sq {σ R : Type*} [CommRing R] [Algebra R B]
    {p_B : B →+* K} {t : B →+* B'} (hkt : RingHom.ker p_B * RingHom.ker t = ⊥)
    {f₀ f₁ : MvPowerSeries σ R →ₐ[R] B}
    (ht : t.comp f₁.toRingHom = t.comp f₀.toRingHom)
    (hf₀ : ∀ i, f₀ (X i) ∈ RingHom.ker p_B) (hf₁ : ∀ i, f₁ (X i) ∈ RingHom.ker p_B)
    {s : MvPowerSeries σ R}
    (hs : s ∈ (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)) ^ 2) :
    f₁ s = f₀ s := by
  have hmem₀ : ∀ u ∈ (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)),
      f₀ u ∈ RingHom.ker p_B := fun u hu ↦ by
    have hle₀ : (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)).map f₀.toRingHom ≤
        RingHom.ker p_B :=
      Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr (Set.range_subset_iff.mpr hf₀))
    exact hle₀ (Ideal.mem_map_of_mem f₀.toRingHom hu)
  have hmem₁ : ∀ u ∈ (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)),
      f₁ u ∈ RingHom.ker p_B := fun u hu ↦ by
    have hle₁ : (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)).map f₁.toRingHom ≤
        RingHom.ker p_B :=
      Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr (Set.range_subset_iff.mpr hf₁))
    exact hle₁ (Ideal.mem_map_of_mem f₁.toRingHom hu)
  have hdiff : ∀ u, f₁ u - f₀ u ∈ RingHom.ker t := fun u ↦ by
    rw [RingHom.mem_ker, map_sub]
    have h := RingHom.congr_fun ht u
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    exact sub_eq_zero.mpr h
  rw [sq] at hs
  refine sub_eq_zero.mp (Submodule.mul_induction_on hs (fun a ha b hb ↦ ?_) fun a b ha hb ↦ ?_)
  · have hsp : f₁ (a * b) - f₀ (a * b) =
        (f₁ a - f₀ a) * f₁ b + f₀ a * (f₁ b - f₀ b) := by
      rw [map_mul, map_mul]
      ring
    rw [hsp, ← Ideal.mem_bot, ← hkt]
    refine Ideal.add_mem _ ?_ ?_
    · rw [mul_comm (f₁ a - f₀ a) (f₁ b)]
      exact Ideal.mul_mem_mul (hmem₁ b hb) (hdiff a)
    · exact Ideal.mul_mem_mul (hmem₀ a ha) (hdiff b)
  · have hadd : f₁ (a + b) - f₀ (a + b) = (f₁ a - f₀ a) + (f₁ b - f₀ b) := by
      rw [map_add, map_add]
      ring
    rw [hadd, ha, hb, _root_.add_zero]

private theorem order_sub_linear_trunc {σ R : Type*} [Fintype σ] [CommRing R]
    (s : MvPowerSeries σ R) :
    ((2 : ℕ) : ℕ∞) ≤
      (s - (C (constantCoeff s) + ∑ i : σ, C (coeff (Finsupp.single i 1) s) * X i)).order := by
  classical
  set s₀ : MvPowerSeries σ R :=
    C (constantCoeff s) + ∑ i : σ, C (coeff (Finsupp.single i 1) s) * X i
  refine nat_le_order fun d hd ↦ ?_
  rw [map_sub, sub_eq_zero]
  have hd_cases : d.degree = 0 ∨ d.degree = 1 := by omega
  rcases hd_cases with h0 | h1
  · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    subst hd0
    simp [s₀, map_sum]
  · have hsum : ∑ i : σ, d i = 1 := by
      rw [← h1]
      exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ by simp_all).symm
    obtain ⟨j, hj⟩ : ∃ j : σ, d j ≠ 0 := by
      by_contra! hzero
      simp [hzero] at hsum
    have hj1 : d j = 1 := by
      have hle : d j ≤ ∑ i : σ, d i :=
        Finset.single_le_sum (fun i _ ↦ Nat.zero_le (d i)) (Finset.mem_univ j)
      omega
    have hother : ∀ i ≠ j, d i = 0 := fun i hij ↦ by
      have h2 : d i + d j ≤ ∑ x : σ, d x := by
        rw [← Finset.sum_add_sum_compl {i, j}]
        have hpair : ∑ x ∈ ({i, j} : Finset σ), d x = d i + d j := Finset.sum_pair hij
        omega
      omega
    have hd1 : d = Finsupp.single j 1 := Finsupp.ext fun i ↦ by
      by_cases hij : i = j
      · subst hij; simp [hj1]
      · simp [hother i hij, hij]
    subst hd1
    have hsingle0 : (Finsupp.single j 1 : σ →₀ ℕ) ≠ 0 := by simp
    simp only [s₀, map_add, map_sum, coeff_C, hsingle0, ↓reduceIte, _root_.zero_add]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [coeff_X, Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0), hij.symm]
    · simp

/-- Linear Taylor formula in `B`: when `t ∘ f₁ = t ∘ f₀`, `f₀ (X i), f₁ (X i) ∈ ker p_B`,
and `ker p_B * ker t = ⊥`, we have
`f₁ s - f₀ s = ∑ i, (f₁ (X i) - f₀ (X i)) * algebraMap R B (coeff (single i 1) s)`. -/
theorem sub_algHom_apply_of_mul_eq_bot {σ R : Type*} [Fintype σ] [CommRing R] [Algebra R B]
    {p_B : B →+* K} {t : B →+* B'} (hkt : RingHom.ker p_B * RingHom.ker t = ⊥)
    {f₀ f₁ : MvPowerSeries σ R →ₐ[R] B}
    (ht : t.comp f₁.toRingHom = t.comp f₀.toRingHom)
    (hf₀ : ∀ i, f₀ (X i) ∈ RingHom.ker p_B) (hf₁ : ∀ i, f₁ (X i) ∈ RingHom.ker p_B)
    (s : MvPowerSeries σ R) :
    f₁ s - f₀ s =
      ∑ i : σ, (f₁ (X i) - f₀ (X i)) * algebraMap R B (coeff (Finsupp.single i 1) s) := by
  classical
  set s₀ : MvPowerSeries σ R :=
    C (constantCoeff s) + ∑ i : σ, C (coeff (Finsupp.single i 1) s) * X i
  have hs_mem : s - s₀ ∈ (Ideal.span (Set.range X) : Ideal (MvPowerSeries σ R)) ^ 2 :=
    mem_pow_span_range_X_iff_le_order.mpr (order_sub_linear_trunc s)
  have hsq := apply_eq_of_mem_span_range_X_sq hkt ht hf₀ hf₁ hs_mem
  have hdecomp : f₁ s - f₀ s = f₁ s₀ - f₀ s₀ := by
    have hs1 : f₁ s - f₁ s₀ = f₀ s - f₀ s₀ := by simpa [map_sub] using hsq
    linear_combination hs1
  rw [hdecomp]
  have hC : ∀ r : R, (C r : MvPowerSeries σ R) = algebraMap R (MvPowerSeries σ R) r :=
    fun _ ↦ rfl
  simp only [s₀, map_add, map_sum, map_mul, hC, AlgHom.commutes]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

end QuotientStep

section ResidueModule

/-- Scalar multiplication of `ResidueField A` on `RingHom.ker t` when
`(maximalIdeal A).map q * RingHom.ker t = ⊥`. -/
@[expose, instance_reducible]
def jSMul {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    (q : A →+* B) (t : B →+* B') (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥) :
    SMul (IsLocalRing.ResidueField A) (RingHom.ker t) where
  smul c x := Quotient.liftOn' c
    (fun a ↦ (⟨q a * x.val, (RingHom.ker t).mul_mem_left _ x.property⟩ : RingHom.ker t))
    (fun a₁ a₂ hab ↦ Subtype.ext <| by
      have ha : a₁ - a₂ ∈ maximalIdeal A :=
        (Submodule.quotientRel_def (maximalIdeal A)).mp hab
      have hsub : q a₁ * x.val - q a₂ * x.val = q (a₁ - a₂) * x.val := by
        rw [map_sub]
        ring
      rw [← sub_eq_zero, hsub, ← Ideal.mem_bot, ← hker]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem q ha) x.property)

/-- `ResidueField A`-vector space structure on `RingHom.ker t` when
`(maximalIdeal A).map q * RingHom.ker t = ⊥`. -/
@[expose, instance_reducible]
def jModule {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    (q : A →+* B) (t : B →+* B') (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥) :
    @Module (IsLocalRing.ResidueField A) (RingHom.ker t) inferInstance inferInstance :=
  letI : SMul (IsLocalRing.ResidueField A) (RingHom.ker t) := jSMul q t hker
  Module.ofMinimalAxioms
    (fun c x y ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective c
      apply Subtype.ext
      change q a * (x.val + y.val) = q a * x.val + q a * y.val
      ring)
    (fun c d x ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective c
      obtain ⟨b, rfl⟩ := residue_surjective d
      apply Subtype.ext
      change q (a + b) * x.val = q a * x.val + q b * x.val
      rw [map_add, add_mul])
    (fun c d x ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective c
      obtain ⟨b, rfl⟩ := residue_surjective d
      apply Subtype.ext
      change q (a * b) * x.val = q a * (q b * x.val)
      rw [map_mul, mul_assoc])
    (fun x ↦ by
      apply Subtype.ext
      change q 1 * x.val = x.val
      rw [map_one, one_mul])

/-- Explicit formula for `jModule` scalar multiplication on residue classes `residue A a`. -/
theorem jModule_smul_coe {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A] (q : A →+* B) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥) (a : A) (x : RingHom.ker t) :
    let := jModule q t hker
    (residue A a • x).val = q a * x.val :=
  rfl

/-- If `A` is a Noetherian local ring and `q : A →+* B` is surjective, then `RingHom.ker t` is
finite-dimensional over `ResidueField A` under `jModule q t hker`. -/
theorem jModule_finite {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A] [IsNoetherianRing A]
    (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥) :
    @Module.Finite (ResidueField A) (RingHom.ker t) inferInstance inferInstance
      (jModule q t hker) := by
  classical
  let := jModule q t hker
  have : IsNoetherianRing B := isNoetherianRing_of_surjective A B q hq
  have hfg : (RingHom.ker t).FG := IsNoetherian.noetherian (RingHom.ker t)
  obtain ⟨s, hs⟩ := hfg
  let s' : Finset (RingHom.ker t) := s.attach.map
    ⟨fun b ↦ ⟨b.val, hs ▸ Ideal.subset_span b.property⟩,
      fun (_ _ : ↥s) h ↦ Subtype.ext (congrArg (Subtype.val : RingHom.ker t → B) h)⟩
  refine ⟨⟨s', ?_⟩⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ _
  have hx' : x ∈ Ideal.span (s : Set B) := hs ▸ hx
  refine Submodule.span_induction (R := B) (M := B)
    (p := fun y (hy : y ∈ Ideal.span (s : Set B)) ↦
      (⟨y, hs ▸ hy⟩ : RingHom.ker t) ∈ Submodule.span (ResidueField A) (s' : Set (RingHom.ker t)))
    ?_ ?_ ?_ ?_ hx'
  · intro y hy
    refine Submodule.subset_span ?_
    simp only [s', Finset.coe_map, Set.mem_image,
      Finset.mem_coe, Finset.mem_attach, true_and, Subtype.exists]
    exact ⟨y, hy, rfl⟩
  · exact Submodule.zero_mem _
  · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂
    exact Submodule.add_mem _ ih₁ ih₂
  · intro b y hy ih
    obtain ⟨a, rfl⟩ := hq b
    change (residue A a) • (⟨y, hs ▸ hy⟩ : RingHom.ker t) ∈ _
    exact Submodule.smul_mem _ _ ih

/-- Coefficientwise projection of a power series with coefficients in `ker t` along a
`ResidueField A`-linear functional `L : ker t →ₗ[ResidueField A] ResidueField A`. -/
@[expose]
def projL {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    {t : B →+* B'} [Module (ResidueField A) (RingHom.ker t)]
    (L : RingHom.ker t →ₗ[ResidueField A] ResidueField A)
    (f : MvPowerSeries τ B) (hf : ∀ d, coeff d f ∈ RingHom.ker t) :
    MvPowerSeries τ (ResidueField A) :=
  fun d ↦ L ⟨coeff d f, hf d⟩

/-- `projL` depends only on the underlying series, not on the proof that coefficients lie in
`RingHom.ker t`. -/
theorem projL_eq_of_eq {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A] {t : B →+* B'} [Module (ResidueField A) (RingHom.ker t)]
    (L : RingHom.ker t →ₗ[ResidueField A] ResidueField A)
    {f g : MvPowerSeries τ B} (hf : ∀ d, coeff d f ∈ RingHom.ker t)
    (hg : ∀ d, coeff d g ∈ RingHom.ker t) (hfg : f = g) :
    projL L f hf = projL L g hg := by
  subst hfg
  rfl

/-- Embed a series over `ResidueField A` into `MvPowerSeries τ B` by acting on a fixed element
`y ∈ ker t`. -/
@[expose]
def mkJ {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    {t : B →+* B'} [Module (ResidueField A) (RingHom.ker t)]
    (y : RingHom.ker t) (g : MvPowerSeries τ (ResidueField A)) : MvPowerSeries τ B :=
  fun d ↦ (coeff d g • y).val

/-- Coefficients of `projL L f hf` are `L` applied to the coefficients of `f`. -/
@[simp]
theorem coeff_projL {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    {t : B →+* B'} [Module (ResidueField A) (RingHom.ker t)]
    (L : RingHom.ker t →ₗ[ResidueField A] ResidueField A)
    (f : MvPowerSeries τ B) (hf : ∀ d, coeff d f ∈ RingHom.ker t) (d : τ →₀ ℕ) :
    coeff d (projL L f hf) = L ⟨coeff d f, hf d⟩ :=
  rfl

/-- Coefficients of `mkJ y g` are the scalar action of coefficients of `g` on `y`. -/
@[simp]
theorem coeff_mkJ {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    {t : B →+* B'} [Module (ResidueField A) (RingHom.ker t)]
    (y : RingHom.ker t) (g : MvPowerSeries τ (ResidueField A)) (d : τ →₀ ℕ) :
    coeff d (mkJ y g) = (coeff d g • y).val :=
  rfl

/-- Every coefficient of `mkJ y g` lies in `RingHom.ker t`. -/
theorem coeff_mkJ_mem {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A] {t : B →+* B'} [Module (ResidueField A) (RingHom.ker t)]
    (y : RingHom.ker t) (g : MvPowerSeries τ (ResidueField A)) (d : τ →₀ ℕ) :
    coeff d (mkJ y g) ∈ RingHom.ker t :=
  (coeff d g • y).property

/-- Additivity of `mkJ y` in the series argument. -/
theorem mkJ_add {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    {t : B →+* B'} [Module (ResidueField A) (RingHom.ker t)]
    (y : RingHom.ker t) (g₁ g₂ : MvPowerSeries τ (ResidueField A)) :
    mkJ y (g₁ + g₂) = mkJ y g₁ + mkJ y g₂ := by
  ext d
  simp [add_smul]

/-- `mkJ y` preserves subtraction in the series argument. -/
theorem mkJ_sub {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    {t : B →+* B'} [Module (ResidueField A) (RingHom.ker t)]
    (y : RingHom.ker t) (g₁ g₂ : MvPowerSeries τ (ResidueField A)) :
    mkJ y (g₁ - g₂) = mkJ y g₁ - mkJ y g₂ := by
  ext d
  simp [sub_smul]

/-- Moving a `ResidueField A`-scalar from the series in `mkJ y` onto the vector `y`. -/
theorem mkJ_smul {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    {t : B →+* B'} [Module (ResidueField A) (RingHom.ker t)]
    (y : RingHom.ker t) (c : ResidueField A) (g : MvPowerSeries τ (ResidueField A)) :
    mkJ y (c • g) = mkJ (c • y) g := by
  ext d
  simp [mul_comm c (coeff d g), mul_smul]

/-- Left multiplication by `f : MvPowerSeries τ B` on `mkJ y g` factors through `f.map p_B`. -/
theorem mul_mkJ {τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [IsLocalRing A]
    (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (y : RingHom.ker t) (f : MvPowerSeries τ B) (g : MvPowerSeries τ (ResidueField A)) :
    letI := jModule q t hker
    f * mkJ y g = mkJ y (f.map p_B * g) := by
  classical
  let := jModule q t hker
  ext d
  simp only [coeff_mul, coeff_mkJ, Finset.sum_smul, coeff_map, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  obtain ⟨a, ha⟩ := hq (coeff p.1 f)
  rw [← ha, ← RingHom.comp_apply p_B q a, hp_B, mul_smul]
  exact (jModule_smul_coe q t hker a (coeff p.2 g • y)).symm

private lemma coe_finsum_ker {α B B' : Type*} [CommRing B] [CommRing B'] (t : B →+* B')
    (f : α → RingHom.ker t) (hf : f.HasFiniteSupport) :
    (finsum f : RingHom.ker t).val = finsum (fun a ↦ (f a).val) :=
  (AddSubmonoidClass.subtype (RingHom.ker t)).map_finsum hf

private lemma ker_mul_eq_smul {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A] (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (b : B) (x : letI := jModule q t hker; RingHom.ker t) :
    letI := jModule q t hker
    (⟨x.val * b, (RingHom.ker t).mul_mem_right b x.property⟩ : RingHom.ker t) = p_B b • x := by
  let := jModule q t hker
  obtain ⟨a₀, rfl⟩ := hq b
  rw [← RingHom.comp_apply p_B q a₀, hp_B]
  apply Subtype.ext
  rw [jModule_smul_coe q t hker]
  ring

private theorem coeff_subst_ker_eq_finsum {σ τ A B B' : Type*} [CommRing A] [CommRing B]
    [CommRing B'] [IsLocalRing A] (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (f : MvPowerSeries σ B) (hf : ∀ d, coeff d f ∈ RingHom.ker t)
    {a : σ → MvPowerSeries τ B} (ha : HasSubst a) (e : τ →₀ ℕ) :
    letI := jModule q t hker
    (fun d ↦ p_B (coeff e (d.prod fun s k ↦ a s ^ k)) •
        (⟨coeff d f, hf d⟩ : RingHom.ker t)).HasFiniteSupport ∧
      (⟨coeff e (f.subst a), coeff_subst_mem_of_coeff_mem hf ha e⟩ : RingHom.ker t) =
        finsum (fun d ↦ p_B (coeff e (d.prod fun s k ↦ a s ^ k)) • ⟨coeff d f, hf d⟩) := by
  let := jModule q t hker
  have hfin : (fun d ↦ coeff d f * coeff e (d.prod fun s k ↦ a s ^ k)).HasFiniteSupport := by
    simpa [smul_eq_mul] using coeff_subst_finite ha f e
  have hfin_ker : (fun d ↦
      p_B (coeff e (d.prod fun s k ↦ a s ^ k)) •
        (⟨coeff d f, hf d⟩ : RingHom.ker t)).HasFiniteSupport :=
    hfin.subset fun d hd h0 ↦ hd <| Subtype.ext <| by
      simpa only [ZeroMemClass.coe_zero, ← h0] using
        (congrArg Subtype.val
          (ker_mul_eq_smul q hq t hker p_B hp_B _ ⟨coeff d f, hf d⟩)).symm
  refine ⟨hfin_ker, Subtype.ext ?_⟩
  dsimp only
  rw [coeff_subst ha, coe_finsum_ker t _ hfin_ker]
  trans finsum (fun d ↦ coeff d f * coeff e (d.prod fun s k ↦ a s ^ k))
  · simp [smul_eq_mul]
  · exact finsum_congr fun d ↦
      congrArg Subtype.val (ker_mul_eq_smul q hq t hker p_B hp_B _ ⟨coeff d f, hf d⟩)

/-- Projection `projL L` commutes with multivariate power series substitution. -/
theorem projL_subst {σ τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A]
    (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (L : letI := jModule q t hker; RingHom.ker t →ₗ[ResidueField A] ResidueField A)
    (f : MvPowerSeries σ B) (hf : ∀ d, coeff d f ∈ RingHom.ker t)
    {a : σ → MvPowerSeries τ B} (ha : HasSubst a) :
    let := jModule q t hker
    projL L (f.subst a) (fun e ↦ coeff_subst_mem_of_coeff_mem hf ha e) =
      (projL L f hf).subst (fun s ↦ (a s).map p_B) := by
  let := jModule q t hker
  ext e
  rw [coeff_projL, coeff_subst (ha.map p_B)]
  obtain ⟨hfin_ker, hcoe⟩ := coeff_subst_ker_eq_finsum q hq t hker p_B hp_B f hf ha e
  rw [hcoe]
  change L.toAddMonoidHom (finsum _) = _
  rw [L.toAddMonoidHom.map_finsum hfin_ker]
  refine finsum_congr fun d ↦ ?_
  change L (p_B _ • ⟨coeff d f, hf d⟩) = _
  rw [LinearMap.map_smul, smul_eq_mul, mul_comm, coeff_projL]
  congr 1
  have hmap : ((d.prod fun s k ↦ a s ^ k).map p_B) = d.prod fun s k ↦ ((a s).map p_B) ^ k := by
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [← hmap, coeff_map]

/-- Substitution into `mkJ y g` commutes with mapping the substitution tuple along `p_B`. -/
theorem mkJ_subst {σ τ A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A]
    (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (y : RingHom.ker t) (g : MvPowerSeries σ (ResidueField A))
    {a : σ → MvPowerSeries τ B} (ha : HasSubst a) :
    let := jModule q t hker
    (mkJ y g).subst a = mkJ y (g.subst fun s ↦ (a s).map p_B) := by
  let := jModule q t hker
  ext e
  rw [coeff_mkJ, coeff_subst ha, coeff_subst (ha.map p_B)]
  have hfin : (fun d ↦
      coeff d g • coeff e (d.prod fun s k ↦ (a s).map p_B ^ k)).HasFiniteSupport := by
    simpa using coeff_subst_finite (ha.map p_B) g e
  have hfin_ker : (fun d ↦
      (coeff d g • coeff e (d.prod fun s k ↦ (a s).map p_B ^ k)) • y).HasFiniteSupport :=
    hfin.subset fun d hd h0 ↦ hd (by dsimp only at h0 ⊢; rw [h0, zero_smul])
  have hsmul_mul : ∀ (c : ResidueField A) (b : B),
      (c • y).val * b = ((c * p_B b) • y).val := fun c b ↦ by
    obtain ⟨a₀, rfl⟩ := hq b
    rw [← RingHom.comp_apply p_B q a₀, hp_B, mul_comm c, mul_smul,
      mul_comm (c • y).val (q a₀)]
    exact (jModule_smul_coe q t hker a₀ (c • y)).symm
  have hsub : (finsum (fun d ↦ (coeff d g • coeff e (d.prod fun s k ↦ (a s).map p_B ^ k)) • y) :
      RingHom.ker t).val =
      finsum (fun d ↦ coeff d (mkJ y g) • coeff e (d.prod fun s k ↦ a s ^ k)) := by
    rw [coe_finsum_ker t _ hfin_ker]
    refine finsum_congr fun d ↦ ?_
    symm
    rw [smul_eq_mul, coeff_mkJ, hsmul_mul, smul_eq_mul]
    have hmap : (d.prod fun s k ↦ a s ^ k).map p_B = d.prod fun s k ↦ (a s).map p_B ^ k := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [← hmap, coeff_map]
  rw [← hsub, finsum_smul]

/-- If `g` has coefficients in `ker t`, so does `F.homDefect 𝔾ₐ g`. -/
theorem homDefect_𝔾ₐ_coeff_mem {B B' : Type*} [CommRing B] [CommRing B']
    {t : B →+* B'} (F : FormalGroup B) {g : PowerSeries B}
    (hg : ∀ n, PowerSeries.coeff n g ∈ RingHom.ker t) (d : Fin 2 →₀ ℕ) :
    coeff d (F.homDefect 𝔾ₐ g) ∈ RingHom.ker t := by
  rw [F.homDefect_𝔾ₐ, map_sub, map_sub]
  refine Ideal.sub_mem _ (Ideal.sub_mem _ ?_ ?_) ?_
  · exact coeff_powerSeries_subst_mem_of_coeff_mem hg
      (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff) d
  · exact coeff_powerSeries_subst_mem_of_coeff_mem hg (PowerSeries.HasSubst.X 0) d
  · exact coeff_powerSeries_subst_mem_of_coeff_mem hg (PowerSeries.HasSubst.X 1) d

/-- Projection `projL L` intertwines `F.homDefect 𝔾ₐ` and `(F.map p_B).homDefect 𝔾ₐ`. -/
theorem projL_homDefect_𝔾ₐ {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A]
    (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (L : letI := jModule q t hker; RingHom.ker t →ₗ[ResidueField A] ResidueField A)
    (F : FormalGroup B) (g : PowerSeries B)
    (hg : ∀ n, PowerSeries.coeff n g ∈ RingHom.ker t) :
    letI := jModule q t hker
    projL L (F.homDefect 𝔾ₐ g) (homDefect_𝔾ₐ_coeff_mem F hg) =
      (F.map p_B).homDefect 𝔾ₐ (projL (τ := Unit) L g (fun d ↦ by
        rw [show d = Finsupp.single () (d ()) from Finsupp.ext fun _ ↦ by simp]
        exact hg (d ()))) := by
  let := jModule q t hker
  set hg' : ∀ d : Unit →₀ ℕ, coeff d g ∈ RingHom.ker t := fun d ↦ by
    rw [show d = Finsupp.single () (d ()) from Finsupp.ext fun _ ↦ by simp]
    exact hg (d ())
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX0 : PowerSeries.HasSubst (X 0 : MvPowerSeries (Fin 2) B) := PowerSeries.HasSubst.X 0
  have hX1 : PowerSeries.HasSubst (X 1 : MvPowerSeries (Fin 2) B) := PowerSeries.HasSubst.X 1
  have hmap_const : ∀ a : MvPowerSeries (Fin 2) B,
      (fun _ : Unit ↦ MvPowerSeries.map p_B a) = Function.const Unit (MvPowerSeries.map p_B a) :=
    fun _ ↦ rfl
  ext d
  simp only [(F.map p_B).homDefect_𝔾ₐ]
  rw [coeff_projL]
  have heq :
      (⟨coeff d (F.homDefect 𝔾ₐ g), homDefect_𝔾ₐ_coeff_mem F hg d⟩ : RingHom.ker t) =
      ⟨coeff d (PowerSeries.subst F.toPowerSeries g),
        coeff_powerSeries_subst_mem_of_coeff_mem hg hF d⟩ -
      ⟨coeff d (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) B) g),
        coeff_powerSeries_subst_mem_of_coeff_mem hg hX0 d⟩ -
      ⟨coeff d (PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) B) g),
        coeff_powerSeries_subst_mem_of_coeff_mem hg hX1 d⟩ := by
    apply Subtype.ext
    simp [F.homDefect_𝔾ₐ, sub_sub]
  rw [heq, map_sub, map_sub]
  have hsF := congrArg (coeff d) (projL_subst (σ := Unit) q hq t hker p_B hp_B L g hg' hF.const)
  have hs0 := congrArg (coeff d) (projL_subst (σ := Unit) q hq t hker p_B hp_B L g hg' hX0.const)
  have hs1 := congrArg (coeff d) (projL_subst (σ := Unit) q hq t hker p_B hp_B L g hg' hX1.const)
  simp only [coeff_projL, PowerSeries.subst_def] at hsF hs0 hs1 ⊢
  rw [hsF, hs0, hs1]
  simp [hmap_const, map_toPowerSeries]

/-- Embedding `mkJ y` intertwines `(F.map p_B).homDefect 𝔾ₐ` and `F.homDefect 𝔾ₐ`. -/
theorem mkJ_homDefect_𝔾ₐ {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A]
    (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (y : RingHom.ker t) (F : FormalGroup B) (g : PowerSeries (ResidueField A)) :
    let := jModule q t hker
    mkJ y ((F.map p_B).homDefect 𝔾ₐ g) = F.homDefect 𝔾ₐ (mkJ (τ := Unit) y g) := by
  let := jModule q t hker
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX0 : PowerSeries.HasSubst (X 0 : MvPowerSeries (Fin 2) B) := PowerSeries.HasSubst.X 0
  have hX1 : PowerSeries.HasSubst (X 1 : MvPowerSeries (Fin 2) B) := PowerSeries.HasSubst.X 1
  have hsF := mkJ_subst (σ := Unit) q hq t hker p_B hp_B y g hF.const
  have hs0 := mkJ_subst (σ := Unit) q hq t hker p_B hp_B y g hX0.const
  have hs1 := mkJ_subst (σ := Unit) q hq t hker p_B hp_B y g hX1.const
  have hFp : (fun _ : Unit ↦ MvPowerSeries.map p_B F.toPowerSeries) =
      fun _ ↦ (F.map p_B).toPowerSeries :=
    funext fun _ ↦ (map_toPowerSeries F p_B).symm
  rw [hFp] at hsF
  simp only [MvPowerSeries.map_X] at hs0 hs1
  dsimp only
  rw [FormalGroup.homDefect_𝔾ₐ (F := F.map p_B), mkJ_sub, mkJ_sub,
    FormalGroup.homDefect_𝔾ₐ (F := F)]
  simp only [PowerSeries.subst_def] at hsF hs0 hs1 ⊢
  rw [hsF, hs0, hs1]

private theorem projL_subst_swap {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A] (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (L : letI := jModule q t hker; RingHom.ker t →ₗ[ResidueField A] ResidueField A)
    {F : FormalGroup B} {Ψ : MvPowerSeries (Fin 2) B} (hΨ : F.IsSymmetricCocycle Ψ)
    (hmem : ∀ d, coeff d Ψ ∈ RingHom.ker t) :
    let := jModule q t hker
    (projL L Ψ hmem).subst ![X 1, X 0] = projL L Ψ hmem := by
  let := jModule q t hker
  have hsw := projL_subst q hq t hker p_B hp_B L Ψ hmem
    (HasSubst.X_X (σ := Fin 2) (R := B) (i := (1 : Fin 2)) (j := (0 : Fin 2)))
  have harg : (fun s : Fin 2 ↦ ((![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) B) s).map p_B) =
      ![X 1, X 0] := by
    funext i; fin_cases i <;> simp
  rw [harg] at hsw
  rw [← hsw]
  ext d
  simp [coeff_projL, hΨ.subst_swap]

private theorem projL_subst_add_subst_eq {A B B' : Type*} [CommRing A] [CommRing B]
    [CommRing B'] [IsLocalRing A] (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (L : letI := jModule q t hker; RingHom.ker t →ₗ[ResidueField A] ResidueField A)
    {F : FormalGroup B} {Ψ : MvPowerSeries (Fin 2) B} (hΨ : F.IsSymmetricCocycle Ψ)
    (hmem : ∀ d, coeff d Ψ ∈ RingHom.ker t) :
    let := jModule q t hker
    (projL L Ψ hmem).subst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) (ResidueField A)) +
        (projL L Ψ hmem).subst ![(F.map p_B).toPowerSeries.subst ![X 0, X 1], X 2] =
      (projL L Ψ hmem).subst ![X 0, (F.map p_B).toPowerSeries.subst ![X 1, X 2]] +
        (projL L Ψ hmem).subst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) (ResidueField A)) := by
  let := jModule q t hker
  have h01 : HasSubst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) B) := HasSubst.X_X
  have h12 : HasSubst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) B) := HasSubst.X_X
  have hF₁₂ : HasSubst (![F.toPowerSeries.subst ![X 0, X 1], X 2] :
      Fin 2 → MvPowerSeries (Fin 3) B) :=
    HasSubst.cons_subst_zero_left 0 1 2 F.zero_constantCoeff
  have hF₂₃ : HasSubst (![X 0, F.toPowerSeries.subst ![X 1, X 2]] :
      Fin 2 → MvPowerSeries (Fin 3) B) :=
    HasSubst.cons_subst_zero_right 0 1 2 F.zero_constantCoeff
  have hs1 := projL_subst q hq t hker p_B hp_B L Ψ hmem h01
  have hs2 := projL_subst q hq t hker p_B hp_B L Ψ hmem hF₁₂
  have hs3 := projL_subst q hq t hker p_B hp_B L Ψ hmem hF₂₃
  have hs4 := projL_subst q hq t hker p_B hp_B L Ψ hmem h12
  have ha1 : (fun s : Fin 2 ↦ ((![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) B) s).map p_B) =
      ![X 0, X 1] := by funext i; fin_cases i <;> simp
  have ha4 : (fun s : Fin 2 ↦ ((![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) B) s).map p_B) =
      ![X 1, X 2] := by funext i; fin_cases i <;> simp
  have ha2 : (fun s : Fin 2 ↦ ((![F.toPowerSeries.subst ![X 0, X 1], X 2] :
      Fin 2 → MvPowerSeries (Fin 3) B) s).map p_B) =
      ![(F.map p_B).toPowerSeries.subst ![X 0, X 1], X 2] := by
    funext i; fin_cases i
    · change MvPowerSeries.map p_B (F.toPowerSeries.subst ![X 0, X 1]) =
        (F.map p_B).toPowerSeries.subst ![X 0, X 1]
      rw [map_toPowerSeries, map_subst h01, ha1]
    · simp
  have ha3 : (fun s : Fin 2 ↦ ((![X 0, F.toPowerSeries.subst ![X 1, X 2]] :
      Fin 2 → MvPowerSeries (Fin 3) B) s).map p_B) =
      ![X 0, (F.map p_B).toPowerSeries.subst ![X 1, X 2]] := by
    funext i; fin_cases i
    · simp
    · change MvPowerSeries.map p_B (F.toPowerSeries.subst ![X 1, X 2]) =
        (F.map p_B).toPowerSeries.subst ![X 1, X 2]
      rw [map_toPowerSeries, map_subst h12, ha4]
  rw [ha1] at hs1; rw [ha2] at hs2; rw [ha3] at hs3; rw [ha4] at hs4
  rw [← hs1, ← hs2, ← hs3, ← hs4]
  ext d
  simp only [map_add, coeff_projL]
  rw [← map_add L, ← map_add L]
  congr 1
  apply Subtype.ext
  simpa using congrArg (coeff d) hΨ.subst_add_subst_eq

/-- Projecting a symmetric 2-cocycle of `F` along `projL L` gives a symmetric 2-cocycle of
`F.map p_B`. -/
theorem isSymmetricCocycle_projL {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A]
    (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (L : letI := jModule q t hker; RingHom.ker t →ₗ[ResidueField A] ResidueField A)
    {F : FormalGroup B} {Ψ : MvPowerSeries (Fin 2) B} (hΨ : F.IsSymmetricCocycle Ψ)
    (hmem : ∀ d, coeff d Ψ ∈ RingHom.ker t) :
    let := jModule q t hker
    (F.map p_B).IsSymmetricCocycle (projL L Ψ hmem) :=
  ⟨projL_subst_swap q hq t hker p_B hp_B L hΨ hmem,
    projL_subst_add_subst_eq q hq t hker p_B hp_B L hΨ hmem⟩

/-- Transport `FormalGroup.derivCocycle` along a ring homomorphism `ι : K →+* k`. -/
theorem derivCocycle_map_residue {σ R K k : Type*} [CommRing R] [CommRing K] [CommRing k]
    {Γ : FormalGroup (MvPowerSeries σ R)} {ρA : R →+* K} {ι : K →+* k}
    {F_res : FormalGroup K} (i : σ) :
    MvPowerSeries.map ι (derivCocycle Γ ρA F_res i) =
      derivCocycle Γ (ι.comp ρA) (F_res.map ι) i := by
  have hω :
      MvPowerSeries.map ι (PowerSeries.subst F_res.toPowerSeries F_res.invariantDifferential) =
      PowerSeries.subst (F_res.map ι).toPowerSeries (F_res.map ι).invariantDifferential := by
    rw [map_toPowerSeries, ← F_res.map_invariantDifferential ι,
      PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero F_res.zero_constantCoeff)]
  have hpart : MvPowerSeries.map ι (coeffPartial ρA i Γ.toPowerSeries) =
      coeffPartial (ι.comp ρA) i Γ.toPowerSeries := by
    ext d
    simp [coeff_coeffPartial]
  rw [derivCocycle, derivCocycle, map_mul, hω, hpart]

/-- Injective base change preserves the order of a multivariate power series. -/
theorem order_eq_of_injective_map {τ K k : Type*} [CommRing K] [CommRing k]
    {ι : K →+* k} (hι : Function.Injective ι) (f : MvPowerSeries τ K) :
    (MvPowerSeries.map ι f).order = f.order := by
  apply le_antisymm
  · refine le_order_iff.mpr fun d hd ↦ ?_
    have hc := coeff_of_lt_order hd
    rwa [coeff_map, map_eq_zero_iff ι hι] at hc
  · refine le_order_iff.mpr fun d hd ↦ ?_
    rw [coeff_map, map_eq_zero_iff ι hι]
    exact coeff_of_lt_order hd

/-- Recover the homogeneous component of `f` from its image under an injective base change `ι`. -/
theorem homogeneousComponent_eq_of_injective_map {τ K k : Type*} [CommRing K] [CommRing k]
    {ι : K →+* k} (hι : Function.Injective ι) (n : ℕ) (f : MvPowerSeries τ K)
    (p : MvPolynomial τ K) (hp : homogeneousComponent n (MvPowerSeries.map ι f) =
      ↑(MvPolynomial.map ι p)) :
    homogeneousComponent n f = ↑p := by
  ext d
  have hd := congrArg (coeff d) hp
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_coe, MvPolynomial.coeff_map,
    coeff_map] at hd
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_coe]
  split_ifs with hdeg
  · simp only [hdeg, ↓reduceIte] at hd
    exact hι hd
  · simp only [hdeg, ↓reduceIte] at hd
    exact hι (by simpa using hd)

/-- Transport an equality of formal group laws `F = G` to a formal group isomorphism
`FormalGroupIso F G`. -/
@[expose]
def formalGroupIsoOfEq {R : Type*} [CommRing R] {F G : FormalGroup R} (h : F = G) :
    FormalGroupIso F G :=
  h ▸ FormalGroupIso.refl F

/-- The underlying power series of `formalGroupIsoOfEq h` is `PowerSeries.X`. -/
@[simp]
theorem formalGroupIsoOfEq_toHom_toPowerSeries {R : Type*} [CommRing R]
    {F G : FormalGroup R} (h : F = G) :
    (formalGroupIsoOfEq h).toHom.toPowerSeries = PowerSeries.X := by
  cases h
  simp [formalGroupIsoOfEq]

private theorem map_sub_map_eq_sum_mkJ_coeffPartial
    {σ A B B' R K : Type*} [Fintype σ] [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [Field K] [IsLocalRing A] [Algebra R A] [Algebra R B]
    (q : A →+* B) (t : B →+* B') (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (hAlg : algebraMap R B = q.comp (algebraMap R A))
    {p_B : B →+* K} (hker_pB : RingHom.ker p_B * RingHom.ker t = ⊥)
    (Γ : FormalGroup (MvPowerSeries σ R)) (f₀ f₁ : MvPowerSeries σ R →ₐ[R] B)
    (htf : t.comp f₀.toRingHom = t.comp f₁.toRingHom)
    (hf₀ : ∀ i, f₀ (X i) ∈ RingHom.ker p_B) (hf₁ : ∀ i, f₁ (X i) ∈ RingHom.ker p_B) :
    let := jModule q t hker
    let δ : σ → RingHom.ker t := fun i ↦ ⟨f₁ (X i) - f₀ (X i), by
      rw [RingHom.mem_ker, map_sub]
      have h := RingHom.congr_fun htf (X i)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
      exact sub_eq_zero.mpr h.symm⟩
    (Γ.map f₁.toRingHom).toPowerSeries - (Γ.map f₀.toRingHom).toPowerSeries =
      ∑ i : σ, mkJ (δ i) (coeffPartial ((residue A).comp (algebraMap R A)) i Γ.toPowerSeries) := by
  classical
  let := jModule q t hker
  set ρA := (residue A).comp (algebraMap R A)
  ext d
  rw [map_sub, map_toPowerSeries, map_toPowerSeries, coeff_map, coeff_map]
  conv_lhs =>
    rw [AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe,
      sub_algHom_apply_of_mul_eq_bot hker_pB htf.symm hf₀ hf₁]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_mkJ, coeff_coeffPartial, hAlg, RingHom.comp_apply, mul_comm]
  simpa [ρA] using (jModule_smul_coe q t hker _ ⟨f₁ (X i) - f₀ (X i), by
    rw [RingHom.mem_ker, map_sub]
    have h := RingHom.congr_fun htf (X i)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    exact sub_eq_zero.mpr h.symm⟩).symm

/-- First-order Taylor cocycle identity for two `R`-algebra homomorphisms
`f₀, f₁ : R⟦σ⟧ →ₐ[R] B` that agree modulo `t : B →+* B'`. -/
theorem invariantDifferential_mul_map_sub_map
    {σ A B B' R : Type*} [Fintype σ] [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [IsLocalRing A] [Algebra R A] [Algebra R B]
    (q : A →+* B) (hq : Function.Surjective q) (t : B →+* B')
    (hker : (maximalIdeal A).map q * RingHom.ker t = ⊥)
    (hAlg : algebraMap R B = q.comp (algebraMap R A))
    (p_B : B →+* ResidueField A) (hp_B : p_B.comp q = residue A)
    (hker_pB : RingHom.ker p_B * RingHom.ker t = ⊥)
    (Γ : FormalGroup (MvPowerSeries σ R)) (F_res : FormalGroup (ResidueField A))
    (f₀ f₁ : MvPowerSeries σ R →ₐ[R] B)
    (hF_res : (Γ.map f₀.toRingHom).map p_B = F_res)
    (htf : t.comp f₀.toRingHom = t.comp f₁.toRingHom)
    (hf₀ : ∀ i, f₀ (X i) ∈ RingHom.ker p_B)
    (hf₁ : ∀ i, f₁ (X i) ∈ RingHom.ker p_B) :
    let := jModule q t hker
    let δ : σ → RingHom.ker t := fun i ↦ ⟨f₁ (X i) - f₀ (X i), by
      rw [RingHom.mem_ker, map_sub]
      have h := RingHom.congr_fun htf (X i)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
      exact sub_eq_zero.mpr h.symm⟩
    PowerSeries.subst (Γ.map f₀.toRingHom).toPowerSeries
        (Γ.map f₀.toRingHom).invariantDifferential *
        ((Γ.map f₁.toRingHom).toPowerSeries - (Γ.map f₀.toRingHom).toPowerSeries) =
      ∑ i : σ, mkJ (δ i) (derivCocycle Γ ((residue A).comp (algebraMap R A)) F_res i) := by
  classical
  let := jModule q t hker
  set F₀B := Γ.map f₀.toRingHom
  have hdiff := map_sub_map_eq_sum_mkJ_coeffPartial q t hker hAlg hker_pB Γ f₀ f₁ htf hf₀ hf₁
  rw [hdiff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_mkJ q hq t hker p_B hp_B, derivCocycle]
  congr 2
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero F₀B.zero_constantCoeff),
    F₀B.map_invariantDifferential p_B, ← map_toPowerSeries, hF_res]

end ResidueModule

end FormalGroup
