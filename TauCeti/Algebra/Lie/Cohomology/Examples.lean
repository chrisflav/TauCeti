/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Algebra.Lie.Cohomology.Relative
public import TauCeti.Algebra.Lie.Sl2.Basic
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Explicit Chevalley–Eilenberg and relative Lie algebra cohomology computations

This file computes Chevalley–Eilenberg cohomology and relative Lie algebra cohomology in three
fundamental settings over a commutative ring `R`, without restricting to a field of characteristic
zero unless division by `2` is genuinely required:

1. **Abelian Lie algebras with trivial coefficients.** All Chevalley–Eilenberg differentials vanish
   (`d_eq_zero_of_isLieAbelian`), so `Hⁿ(L, M) ≃ₗ[R] (L [⋀^Fin n]→ₗ[R] M)`
   (`cohomologyEquivOfIsLieAbelian`). When `L` is free of rank `k`, `Hᵏ(L, M) ≃ₗ[R] M` and
   `Hⁿ(L, M) = 0` for `n > k` (the vanishing above the rank holds for arbitrary coefficients and
   arbitrary Lie algebras; see `subsingleton_cohomology_of_basis_lt`). For a rank-one abelian Lie
   algebra this gives `H⁰ ≃ M`, `H¹ ≃ M`, and `Hⁿ = 0` for `n ≥ 2`.
2. **The special linear Lie algebra `sl (Fin 2) R` with trivial coefficients `M`.** Over any
   commutative ring `R`, `d₀ = 0`, `d₂ = 0`, and `Cⁿ = 0` for `n ≥ 4`, yielding `H⁰ ≃ M`,
   `H³ ≃ M`, and `Hⁿ = 0` for `n ≥ 4`. When `2` is invertible in `R`, `d₁` is bijective
   (`bijective_d_one_slFinTwo`), so `H¹ = 0` and `H² = 0`.
3. **The relative pair `(sl (Fin 2) R, so(2), SO(2))` with trivial coefficients `W`.** We define the
   skew-symmetric subalgebra `soSubalgebra n R ≤ sl n R` and the adjoint action
   `specialOrthogonalAd n R` of `Matrix.specialOrthogonalGroup n R` on `sl n R` for any finite
   dimension `n`. Over any commutative ring `R`, relative cochains and cohomology of
   `(sl (Fin 2) R, so(2), SO(2))` vanish in all degrees `≥ 3` for arbitrary compatible coefficients.
   When `2` is invertible in `R`, the `SO(2)`-action rotates the complement of `so(2)` with weights
   `±2`, killing all degree-`1` relative cochains while fixing the volume `2`-form. Consequently all
   relative differentials vanish and `H⁰(sl₂, so(2), SO(2); W) ≃ₗ[R] W`, `H¹ = 0`, `H² ≃ₗ[R] W`,
   and `Hⁿ = 0` for `n ≥ 3`. Taking `R = ℝ` and `W = ℂ` recovers the cohomology of the compact dual
   `S²`.

## Main definitions

* `TauCeti.LieModule.Cohomology.cohomologyZeroEquivOfIsTrivial`: `H⁰(L, M) ≃ₗ[R] M` for a trivial
  `L`-module `M`.
* `TauCeti.LieModule.Cohomology.relativeGroupCohomologyZeroEquivOfIsTrivial`:
  `H⁰(L, K, G; M) ≃ₗ[R] M` when both `L` and `G` act trivially on `M`.
* `TauCeti.LieModule.Cohomology.cohomologyEquivOfIsLieAbelian`:
  `Hⁿ(L, M) ≃ₗ[R] (L [⋀^Fin n]→ₗ[R] M)` for abelian `L` and trivial `M`.
* `TauCeti.LieModule.Cohomology.cohomologyTopEquivOfIsLieAbelian`:
  `Hᵏ(L, M) ≃ₗ[R] M` for abelian `L` with a basis of cardinality `k` and trivial `M`.
* `TauCeti.LieModule.Cohomology.cohomologyThreeEquivSlFinTwo`:
  `H³(sl (Fin 2) R, M) ≃ₗ[R] M` for trivial `M` over any commutative ring `R`.
* `TauCeti.LieModule.Cohomology.soSubalgebra`: the Lie subalgebra `so(n)` inside `sl n R`.
* `TauCeti.LieModule.Cohomology.specialOrthogonalAd`: the adjoint representation of `SO(n)` on
  `sl n R`.
* `TauCeti.LieModule.Cohomology.relativeGroupCohomologyTwoEquivSlFinTwoSO2`:
  `H²(sl₂, so(2), SO(2); W) ≃ₗ[R] W` when `2` is invertible.

## Main results

* `TauCeti.LieModule.Cohomology.subsingleton_cohomology_of_basis_lt`: `Hⁿ(L, M) = 0` whenever `L`
  admits a finite basis of size strictly smaller than `n`.
* `TauCeti.LieModule.Cohomology.subsingleton_cohomologyOneSlFinTwo`,
  `TauCeti.LieModule.Cohomology.subsingleton_cohomologyTwoSlFinTwo`:
  `H¹(sl (Fin 2) R, M) = 0` and `H²(sl (Fin 2) R, M) = 0` for trivial `M` when `2` is invertible.
* `TauCeti.LieModule.Cohomology.subsingleton_relativeGroupCohomologyOneSlFinTwoSO2`:
  `H¹(sl₂, so(2), SO(2); W) = 0` when `2` is invertible.
* `TauCeti.LieModule.Cohomology.subsingleton_relativeGroupCohomologyAddThreeSlFinTwoSO2`:
  `H^{q + 3}(sl₂, so(2), SO(2); W) = 0` over any commutative ring `R`.
-/

public section

open CategoryTheory Limits AlternatingMap Matrix LieAlgebra _root_.LieModule.Cohomology

namespace TauCeti.LieModule.Cohomology

/-! ### Homological and alternating-map helpers -/

section Helpers

variable {R : Type*} [CommRing R]

private noncomputable def homologyEquivOfDiffEqZero {C : CochainComplex (ModuleCat R) ℕ}
    {n : ℕ} (hprev : ∀ m, m + 1 = n → C.d m n = 0) (hnext : C.d n (n + 1) = 0) :
    C.homology n ≃ₗ[R] C.X n :=
  match n with
  | 0 => (C.isoHomologyπ₀.symm ≪≫
      C.iCyclesIso 0 1 (ComplexShape.next_eq' _ rfl) hnext).toLinearEquiv
  | m + 1 => ((C.isoHomologyπ m (m + 1) (ComplexShape.prev_eq' _ rfl) (hprev m rfl)).symm ≪≫
      C.iCyclesIso (m + 1) (m + 2) (ComplexShape.next_eq' _ rfl) hnext).toLinearEquiv

private theorem subsingleton_homology_of_subsingleton_X {C : CochainComplex (ModuleCat R) ℕ}
    {n : ℕ} [h : Subsingleton (C.X n)] : Subsingleton (C.homology n) := by
  have hX : IsZero (C.sc n).X₂ := ModuleCat.isZero_iff_subsingleton.mpr h
  exact ModuleCat.isZero_iff_subsingleton.mp <|
    ShortComplex.isZero_homology_of_isZero_X₂ (C.sc n) hX

private theorem subsingleton_homology_of_surjective_d {C : CochainComplex (ModuleCat R) ℕ}
    {m : ℕ} (h : Function.Surjective (C.d m (m + 1))) :
    Subsingleton (C.homology (m + 1)) := by
  have hEx : (C.sc' m (m + 1) (m + 2)).Exact :=
    (C.sc' m (m + 1) (m + 2)).moduleCat_exact_iff.mpr fun x _ ↦ h x
  have hZ : IsZero (C.sc' m (m + 1) (m + 2)).homology :=
    (C.sc' m (m + 1) (m + 2)).exact_iff_isZero_homology.mp hEx
  exact ModuleCat.isZero_iff_subsingleton.mp <|
    hZ.of_iso (C.homologyIsoSc' m (m + 1) (m + 2)
      (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl))

private theorem subsingleton_homology_of_injective_d {C : CochainComplex (ModuleCat R) ℕ}
    {m : ℕ} (h : Function.Injective (C.d (m + 1) (m + 2))) :
    Subsingleton (C.homology (m + 1)) := by
  have hEx : (C.sc' m (m + 1) (m + 2)).Exact :=
    (C.sc' m (m + 1) (m + 2)).moduleCat_exact_iff.mpr fun x hx ↦
      ⟨0, by
        rw [_root_.map_zero]
        exact (h (hx.trans (_root_.map_zero _).symm)).symm⟩
  have hZ : IsZero (C.sc' m (m + 1) (m + 2)).homology :=
    (C.sc' m (m + 1) (m + 2)).exact_iff_isZero_homology.mp hEx
  exact ModuleCat.isZero_iff_subsingleton.mp <|
    hZ.of_iso (C.homologyIsoSc' m (m + 1) (m + 2)
      (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl))

private theorem eq_zero_of_basis_lt {L M ι₁ ι : Type*} [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M] [Fintype ι₁] [Fintype ι]
    (e : Module.Basis ι₁ R L) (h : Fintype.card ι₁ < Fintype.card ι)
    (ω : L [⋀^ι]→ₗ[R] M) : ω = 0 :=
  e.ext_alternating fun v hv ↦
    absurd (Fintype.card_le_of_injective v hv) (not_le.mpr h)

private noncomputable def alternatingMapBasisTopEquiv {L M ι : Type*} [AddCommGroup L]
    [Module R L] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι R L) : (L [⋀^ι]→ₗ[R] M) ≃ₗ[R] M where
  toFun ω := ω e
  invFun m := e.det.smulRight m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ω := (AlternatingMap.eq_basis_det_smulRight e ω).symm
  right_inv m := by simp [Module.Basis.det_self]

private theorem alternatingMap_pair_swap {L M : Type*} [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M] (ω : L [⋀^Fin 2]→ₗ[R] M) (x y : L) :
    ω ![y, x] = -ω ![x, y] := by
  have h := ω.map_swap ![x, y] (i := (0 : Fin 2)) (j := 1) (by decide)
  have hupd : Function.update (Function.update ![x, y] (0 : Fin 2) (![x, y] 1)) 1 (![x, y] 0) =
      ![y, x] := by ext i; fin_cases i <;> rfl
  simpa [hupd] using h

end Helpers

/-! ### General vanishing, trivial coefficients, and abelian Lie algebras -/

section Abelian

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Chevalley–Eilenberg cohomology vanishes above the rank of a free finite-rank Lie algebra,
for arbitrary coefficients `M`. -/
theorem subsingleton_cohomology_of_basis_lt {ι : Type*} [Fintype ι] {n : ℕ}
    (e : Module.Basis ι R L) (h : Fintype.card ι < n) :
    Subsingleton (cohomology R L M n) := by
  have : Subsingleton ((cochainComplex R L M).X n) :=
    ⟨fun ω₁ ω₂ ↦ by
      have hcard : Fintype.card ι < Fintype.card (Fin n) := by simpa using h
      rw [eq_zero_of_basis_lt e hcard ω₁, eq_zero_of_basis_lt e hcard ω₂]⟩
  exact subsingleton_homology_of_subsingleton_X

/-- For a trivial `L`-module `M`, the degree-zero Chevalley–Eilenberg differential vanishes. -/
theorem d_zero_eq_zero_of_isTrivial [LieModule.IsTrivial L M] : d R L M 0 = 0 := by
  ext ω v
  simp [d_zero_apply, trivial_lie_zero]

/-- For a trivial `L`-module `M`, degree-zero cohomology `H⁰(L, M)` is linearly equivalent to
`M`. -/
noncomputable def cohomologyZeroEquivOfIsTrivial [LieModule.IsTrivial L M] :
    cohomology R L M 0 ≃ₗ[R] M :=
  (cohomologyZeroEquiv R L M).trans <|
    (LinearEquiv.ofEq _ _
      (congrArg LieSubmodule.toSubmodule
        ((LieModule.isTrivial_iff_max_triv_eq_top R L M).mp ‹_›))).trans
      Submodule.topEquiv

/-- When both `L` and a group `G` act trivially on `M`, degree-zero `(K, G)`-relative cohomology
`H⁰(L, K, G; M)` is linearly equivalent to `M`. -/
noncomputable def relativeGroupCohomologyZeroEquivOfIsTrivial (K : LieSubalgebra R L)
    {G : Type*} [Group G] (Ad : Representation R G L) (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆)
    [LieModule.IsTrivial L M] [ρ.IsTrivial] :
    relativeGroupCohomology R L K M Ad ρ hAd hcompat 0 ≃ₗ[R] M := by
  have htop :
      ((LieModule.maxTrivSubmodule R L M).toSubmodule ⊓ ρ.invariants : Submodule R M) = ⊤ := by
    ext m
    simp [LieModule.mem_maxTrivSubmodule, trivial_lie_zero, Representation.mem_invariants,
      Representation.isTrivial_def]
  exact (relativeGroupCohomologyZeroEquiv R L K M Ad ρ hAd hcompat).trans
    ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv)

/-- For an abelian Lie algebra `L` acting trivially on `M`, every Chevalley–Eilenberg
differential vanishes. -/
theorem d_eq_zero_of_isLieAbelian [IsLieAbelian L] [LieModule.IsTrivial L M] (n : ℕ) :
    d R L M n = 0 := by
  cases n with
  | zero => exact d_zero_eq_zero_of_isTrivial R L M
  | succ n =>
    ext ω v
    simp only [d_succ_apply, trivial_lie_zero, smul_zero, Finset.sum_const_zero, zero_add,
      LinearMap.zero_apply, zero_apply]
    refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
    rw [ω.map_coord_zero (i := (0 : Fin (n + 1))) (by simp), smul_zero]

/-- For an abelian Lie algebra `L` acting trivially on `M`, the cohomology `Hⁿ(L, M)` is linearly
equivalent to the full space of alternating `n`-forms `L [⋀^Fin n]→ₗ[R] M`. -/
noncomputable def cohomologyEquivOfIsLieAbelian [IsLieAbelian L] [LieModule.IsTrivial L M]
    (n : ℕ) : cohomology R L M n ≃ₗ[R] (L [⋀^Fin n]→ₗ[R] M) :=
  homologyEquivOfDiffEqZero
    (fun m hm ↦ by
      subst hm
      rw [cochainComplex_d_succ, d_eq_zero_of_isLieAbelian]
      rfl)
    (by
      rw [cochainComplex_d_succ, d_eq_zero_of_isLieAbelian]
      rfl)

/-- For an abelian Lie algebra `L` with a basis of size `k` acting trivially on `M`, the top-degree
cohomology `Hᵏ(L, M)` is linearly equivalent to `M`. For `k = 1`, together with
`cohomologyZeroEquivOfIsTrivial` and `subsingleton_cohomology_of_basis_lt`, this yields
`H⁰ ≃ M`, `H¹ ≃ M`, and `Hⁿ = 0` for `n ≥ 2`. -/
noncomputable def cohomologyTopEquivOfIsLieAbelian [IsLieAbelian L] [LieModule.IsTrivial L M]
    {k : ℕ} (e : Module.Basis (Fin k) R L) : cohomology R L M k ≃ₗ[R] M :=
  (cohomologyEquivOfIsLieAbelian R L M k).trans (alternatingMapBasisTopEquiv e)

end Abelian

/-! ### Cohomology of `sl (Fin 2) R` with trivial coefficients -/

section SlFinTwo

variable (R : Type*) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable [LieRingModule (SpecialLinear.sl (Fin 2) R) M]
variable [LieModule R (SpecialLinear.sl (Fin 2) R) M]
variable [LieModule.IsTrivial (SpecialLinear.sl (Fin 2) R) M]

private theorem d_one_slFinTwo_apply (ω : SpecialLinear.sl (Fin 2) R [⋀^Fin 1]→ₗ[R] M)
    (x y : SpecialLinear.sl (Fin 2) R) :
    d R (SpecialLinear.sl (Fin 2) R) M 1 ω ![x, y] = -ω ![⁅x, y⁆] := by
  have h := congrArg (fun c : twoCochain R (SpecialLinear.sl (Fin 2) R) M ↦ c x y)
    (twoCochainEquiv_d_one ω)
  simpa [d₁₂_apply_apply, trivial_lie_zero] using h

private theorem d_one_slFinTwo_basis_zero_one
    (ω : SpecialLinear.sl (Fin 2) R [⋀^Fin 1]→ₗ[R] M) :
    d R (SpecialLinear.sl (Fin 2) R) M 1 ω ![slFinTwoBasis R 0, slFinTwoBasis R 1] =
      -ω ![slFinTwoBasis R 2] := by
  rw [d_one_slFinTwo_apply, lie_slFinTwoBasis_zero_one]

private theorem d_one_slFinTwo_basis_zero_two
    (ω : SpecialLinear.sl (Fin 2) R [⋀^Fin 1]→ₗ[R] M) :
    d R (SpecialLinear.sl (Fin 2) R) M 1 ω ![slFinTwoBasis R 0, slFinTwoBasis R 2] =
      (2 : R) • ω ![slFinTwoBasis R 0] := by
  rw [d_one_slFinTwo_apply, ← lie_skew, lie_slFinTwoBasis_two_zero, ← neg_smul]
  have hu : ![(-(2 : R)) • slFinTwoBasis R 0] =
      Function.update ![slFinTwoBasis R 0] 0 ((-(2 : R)) • ![slFinTwoBasis R 0] 0) := by
    ext i; fin_cases i; rfl
  rw [hu, ω.map_update_smul, Function.update_eq_self, neg_smul, neg_neg]

private theorem d_one_slFinTwo_basis_one_two
    (ω : SpecialLinear.sl (Fin 2) R [⋀^Fin 1]→ₗ[R] M) :
    d R (SpecialLinear.sl (Fin 2) R) M 1 ω ![slFinTwoBasis R 1, slFinTwoBasis R 2] =
      -((2 : R) • ω ![slFinTwoBasis R 1]) := by
  rw [d_one_slFinTwo_apply, ← lie_skew, lie_slFinTwoBasis_two_one, neg_neg]
  have hu : ![(2 : R) • slFinTwoBasis R 1] =
      Function.update ![slFinTwoBasis R 1] 0 ((2 : R) • ![slFinTwoBasis R 1] 0) := by
    ext i; fin_cases i; rfl
  rw [hu, ω.map_update_smul, Function.update_eq_self]

/-- For `sl (Fin 2) R` acting trivially on `M`, the degree-two Chevalley–Eilenberg differential
vanishes over every commutative ring `R`. -/
theorem d_two_slFinTwo_eq_zero : d R (SpecialLinear.sl (Fin 2) R) M 2 = 0 := by
  let b := slFinTwoBasis R
  ext ω : 1
  rw [LinearMap.zero_apply]
  have htop : d R (SpecialLinear.sl (Fin 2) R) M 2 ω ![b 0, b 1, b 2] = 0 := by
    rw [← d₂₃_twoCochainEquiv]
    have h01 : ⁅b 0, b 1⁆ = b 2 := lie_slFinTwoBasis_zero_one R
    have h02 : ⁅b 0, b 2⁆ = -((2 : R) • b 0) := by
      rw [← lie_skew, lie_slFinTwoBasis_two_zero]
    have h12 : ⁅b 1, b 2⁆ = (2 : R) • b 1 := by
      rw [← lie_skew, lie_slFinTwoBasis_two_one, neg_neg]
    have h22 : ω ![b 2, b 2] = 0 :=
      ω.map_eq_zero_of_eq ![b 2, b 2] (i := 0) (j := 1) rfl (by decide)
    have hswap : ω ![b 1, b 0] = -ω ![b 0, b 1] := alternatingMap_pair_swap ω (b 0) (b 1)
    have h1 : ω ![(-(2 : R)) • b 0, b 1] = -((2 : R) • ω ![b 0, b 1]) := by
      have hu : ![(-(2 : R)) • b 0, b 1] =
          Function.update ![b 0, b 1] 0 ((-(2 : R)) • ![b 0, b 1] 0) := by
        ext i; fin_cases i <;> rfl
      rw [hu, ω.map_update_smul, Function.update_eq_self, neg_smul]
    have h2 : ω ![(2 : R) • b 1, b 0] = (2 : R) • ω ![b 1, b 0] := by
      have hu : ![(2 : R) • b 1, b 0] =
          Function.update ![b 1, b 0] 0 ((2 : R) • ![b 1, b 0] 0) := by
        ext i; fin_cases i <;> rfl
      rw [hu, ω.map_update_smul, Function.update_eq_self]
    simp only [d₂₃_apply, trivial_lie_zero, twoCochainEquiv_apply, h01, h02, h12, h22,
      ← neg_smul, h1, h2, hswap]
    module
  have hb_eq : (⇑b : Fin 3 → SpecialLinear.sl (Fin 2) R) = ![b 0, b 1, b 2] := by
    funext i; fin_cases i <;> rfl
  rw [AlternatingMap.eq_basis_det_smulRight b (d R (SpecialLinear.sl (Fin 2) R) M 2 ω),
    hb_eq, htop]
  ext v
  simp

private theorem injective_d_one_slFinTwo [Invertible (2 : R)] :
    Function.Injective (d R (SpecialLinear.sl (Fin 2) R) M 1) := by
  let L := SpecialLinear.sl (Fin 2) R
  let b := slFinTwoBasis R
  rw [injective_iff_map_eq_zero]
  intro ω hω
  have h2 : ω ![b 2] = 0 := by
    have h := congrArg (fun f : L [⋀^Fin 2]→ₗ[R] M ↦ f ![b 0, b 1]) hω
    rw [d_one_slFinTwo_basis_zero_one, zero_apply, neg_eq_zero] at h
    exact h
  have h0 : ω ![b 0] = 0 := by
    have h := congrArg (fun f : L [⋀^Fin 2]→ₗ[R] M ↦ f ![b 0, b 2]) hω
    rw [d_one_slFinTwo_basis_zero_two, zero_apply] at h
    have h' := congrArg (fun m : M ↦ ⅟(2 : R) • m) h
    simpa only [smul_smul, invOf_mul_self, one_smul, smul_zero] using h'
  have h1 : ω ![b 1] = 0 := by
    have h := congrArg (fun f : L [⋀^Fin 2]→ₗ[R] M ↦ f ![b 1, b 2]) hω
    rw [d_one_slFinTwo_basis_one_two, zero_apply, neg_eq_zero] at h
    have h' := congrArg (fun m : M ↦ ⅟(2 : R) • m) h
    simpa only [smul_smul, invOf_mul_self, one_smul, smul_zero] using h'
  refine b.ext_alternating fun v _ ↦ ?_
  have hv : (fun i ↦ b (v i)) = ![b (v 0)] := by funext i; fin_cases i; rfl
  rw [hv, zero_apply]
  generalize v 0 = k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

private theorem surjective_d_one_slFinTwo [Invertible (2 : R)] :
    Function.Surjective (d R (SpecialLinear.sl (Fin 2) R) M 1) := by
  let L := SpecialLinear.sl (Fin 2) R
  let b := slFinTwoBasis R
  intro η
  let f : L →ₗ[R] M :=
    b.constr R ![⅟(2 : R) • η ![b 0, b 2], -(⅟(2 : R) • η ![b 1, b 2]), -η ![b 0, b 1]]
  let ω := (oneCochainEquiv R L M).symm f
  have h01 : d R L M 1 ω ![b 0, b 1] = η ![b 0, b 1] := by
    rw [d_one_slFinTwo_basis_zero_one, oneCochainEquiv_symm_apply]
    change -(f (b 2)) = η ![b 0, b 1]
    simp only [f, Module.Basis.constr_basis, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, neg_neg]
  have h02 : d R L M 1 ω ![b 0, b 2] = η ![b 0, b 2] := by
    rw [d_one_slFinTwo_basis_zero_two, oneCochainEquiv_symm_apply]
    change (2 : R) • f (b 0) = η ![b 0, b 2]
    simp only [f, Module.Basis.constr_basis, Matrix.cons_val_zero, smul_smul, mul_invOf_self,
      one_smul]
  have h12 : d R L M 1 ω ![b 1, b 2] = η ![b 1, b 2] := by
    rw [d_one_slFinTwo_basis_one_two, oneCochainEquiv_symm_apply]
    change -((2 : R) • f (b 1)) = η ![b 1, b 2]
    simp only [f, Module.Basis.constr_basis, Matrix.cons_val_one, Matrix.cons_val_zero, smul_neg,
      smul_smul, mul_invOf_self, one_smul, neg_neg]
  have swap_eq : ∀ {x y : L}, d R L M 1 ω ![x, y] = η ![x, y] → d R L M 1 ω ![y, x] = η ![y, x] :=
    fun hxy ↦ by rw [alternatingMap_pair_swap (d R L M 1 ω), alternatingMap_pair_swap η, hxy]
  refine ⟨ω, b.ext_alternating fun v hv ↦ ?_⟩
  have hv_eq : (fun i ↦ b (v i)) = ![b (v 0), b (v 1)] := by ext i; fin_cases i <;> rfl
  have hne : v 0 ≠ v 1 := fun h ↦ absurd (hv h) (by decide)
  rw [hv_eq]
  generalize v 0 = i at hne ⊢
  generalize v 1 = j at hne ⊢
  fin_cases i <;> fin_cases j
  · exact absurd rfl hne
  · exact h01
  · exact h02
  · exact swap_eq h01
  · exact absurd rfl hne
  · exact h12
  · exact swap_eq h02
  · exact swap_eq h12
  · exact absurd rfl hne

/-- When `2` is invertible in `R`, the degree-one Chevalley–Eilenberg differential for
`sl (Fin 2) R` with trivial coefficients `M` is bijective. -/
theorem bijective_d_one_slFinTwo [Invertible (2 : R)] :
    Function.Bijective (d R (SpecialLinear.sl (Fin 2) R) M 1) :=
  ⟨injective_d_one_slFinTwo R M, surjective_d_one_slFinTwo R M⟩

/-- When `2` is invertible in `R`, `H¹(sl (Fin 2) R, M) = 0` for any trivial module `M`. -/
theorem subsingleton_cohomologyOneSlFinTwo [Invertible (2 : R)] :
    Subsingleton (cohomology R (SpecialLinear.sl (Fin 2) R) M 1) :=
  subsingleton_homology_of_injective_d (m := 0) <| by
    rw [cochainComplex_d_succ]
    exact injective_d_one_slFinTwo R M

/-- When `2` is invertible in `R`, `H²(sl (Fin 2) R, M) = 0` for any trivial module `M`. -/
theorem subsingleton_cohomologyTwoSlFinTwo [Invertible (2 : R)] :
    Subsingleton (cohomology R (SpecialLinear.sl (Fin 2) R) M 2) :=
  subsingleton_homology_of_surjective_d (m := 1) <| by
    rw [cochainComplex_d_succ]
    exact surjective_d_one_slFinTwo R M

/-- Over any commutative ring `R`, `H³(sl (Fin 2) R, M) ≃ₗ[R] M` for any trivial module `M`. -/
noncomputable def cohomologyThreeEquivSlFinTwo :
    cohomology R (SpecialLinear.sl (Fin 2) R) M 3 ≃ₗ[R] M := by
  haveI : Subsingleton ((cochainComplex R (SpecialLinear.sl (Fin 2) R) M).X 4) :=
    ⟨fun ω₁ ω₂ ↦ by
      have hcard : Fintype.card (Fin 3) < Fintype.card (Fin 4) := by decide
      rw [eq_zero_of_basis_lt (slFinTwoBasis R) hcard ω₁,
        eq_zero_of_basis_lt (slFinTwoBasis R) hcard ω₂]⟩
  refine (homologyEquivOfDiffEqZero
    (fun m hm ↦ by
      have h2 : m = 2 := by omega
      subst h2
      rw [cochainComplex_d_succ, d_two_slFinTwo_eq_zero]
      rfl)
    (by
      ext ω
      exact Subsingleton.elim _ _)).trans
    (alternatingMapBasisTopEquiv (slFinTwoBasis R))

end SlFinTwo

/-! ### Relative cohomology of `(sl (Fin 2) R, so(2), SO(2))` -/

section SpecialOrthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : Type*) [Fintype n] [DecidableEq n]
variable (R : Type*) [CommRing R]

/-- The orthogonal Lie subalgebra `so(n)` viewed as a Lie subalgebra of `sl n R`, consisting of
skew-symmetric trace-zero matrices (`Aᵀ = -A`). -/
def soSubalgebra : LieSubalgebra R (SpecialLinear.sl n R) :=
  (Orthogonal.so n R).comap (SpecialLinear.sl n R).incl

/-- A trace-zero matrix lies in `soSubalgebra n R` if and only if it is skew-symmetric. -/
@[simp]
theorem mem_soSubalgebra (A : SpecialLinear.sl n R) :
    A ∈ soSubalgebra n R ↔ A.1ᵀ = -A.1 := by
  simp [soSubalgebra, Orthogonal.mem_so]

/-- The adjoint representation of `Matrix.specialOrthogonalGroup n R` on `sl n R`, given by
conjugation `g ↦ (A ↦ g A gᵀ)`. -/
def specialOrthogonalAd :
    Representation R (Matrix.specialOrthogonalGroup n R) (SpecialLinear.sl n R) where
  toFun g :=
    { toFun A := ⟨g.1 * A.1 * g.1ᵀ, by
        have hgtg : g.1ᵀ * g.1 = 1 := (Matrix.mem_orthogonalGroup_iff' n R).mp g.2.1
        change Matrix.trace (g.1 * A.1 * g.1ᵀ) = 0
        rw [Matrix.trace_mul_cycle, hgtg, one_mul]
        exact A.2⟩
      map_add' A B := Subtype.ext <| by simp [mul_add, add_mul]
      map_smul' r A := Subtype.ext <| by simp }
  map_one' := by ext A i j; simp
  map_mul' g h := by
    ext A i j
    change ((g.1 * h.1) * A.1 * (g.1 * h.1)ᵀ) i j = (g.1 * (h.1 * A.1 * h.1ᵀ) * g.1ᵀ) i j
    rw [Matrix.transpose_mul]
    simp [Matrix.mul_assoc]

/-- The underlying matrix of `specialOrthogonalAd n R g A` is `g A gᵀ`. -/
@[simp]
theorem specialOrthogonalAd_apply_val (g : Matrix.specialOrthogonalGroup n R)
    (A : SpecialLinear.sl n R) :
    (specialOrthogonalAd n R g A).1 = g.1 * A.1 * g.1ᵀ := by
  simp [specialOrthogonalAd]

/-- The adjoint action of `SO(n)` on `sl n R` acts by Lie algebra automorphisms. -/
theorem specialOrthogonalAd_lie (g : Matrix.specialOrthogonalGroup n R)
    (A B : SpecialLinear.sl n R) :
    specialOrthogonalAd n R g ⁅A, B⁆ =
      ⁅specialOrthogonalAd n R g A, specialOrthogonalAd n R g B⁆ := by
  have hgtg : g.1ᵀ * g.1 = 1 := (Matrix.mem_orthogonalGroup_iff' n R).mp g.2.1
  refine Subtype.ext ?_
  simp only [specialOrthogonalAd_apply_val, SpecialLinear.sl_bracket]
  have hAB : (g.1 * A.1 * g.1ᵀ) * (g.1 * B.1 * g.1ᵀ) = g.1 * (A.1 * B.1) * g.1ᵀ := by
    calc (g.1 * A.1 * g.1ᵀ) * (g.1 * B.1 * g.1ᵀ)
        = g.1 * A.1 * (g.1ᵀ * g.1) * B.1 * g.1ᵀ := by simp only [Matrix.mul_assoc]
      _ = g.1 * (A.1 * B.1) * g.1ᵀ := by rw [hgtg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hBA : (g.1 * B.1 * g.1ᵀ) * (g.1 * A.1 * g.1ᵀ) = g.1 * (B.1 * A.1) * g.1ᵀ := by
    calc (g.1 * B.1 * g.1ᵀ) * (g.1 * A.1 * g.1ᵀ)
        = g.1 * B.1 * (g.1ᵀ * g.1) * A.1 * g.1ᵀ := by simp only [Matrix.mul_assoc]
      _ = g.1 * (B.1 * A.1) * g.1ᵀ := by rw [hgtg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [hAB, hBA, mul_sub, sub_mul]

/-- The adjoint action of `SO(n)` preserves `so(n) ≤ sl n R`. -/
theorem specialOrthogonalAd_mem_soSubalgebra (g : Matrix.specialOrthogonalGroup n R) :
    (soSubalgebra n R).toLieSubmodule.toSubmodule ≤
      (soSubalgebra n R).toLieSubmodule.toSubmodule.comap (specialOrthogonalAd n R g) := by
  intro A hA
  rw [Submodule.mem_comap, LieSubmodule.mem_toSubmodule, LieSubalgebra.mem_toLieSubmodule,
    mem_soSubalgebra, specialOrthogonalAd_apply_val]
  have hAT : A.1ᵀ = -A.1 := (mem_soSubalgebra n R A).mp ((LieSubalgebra.mem_toLieSubmodule _).mp hA)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hAT,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

/-- The trivial representation of `SO(n)` on a trivial `sl n R`-module `W` is compatible with
`specialOrthogonalAd`. -/
theorem trivial_compat_specialOrthogonalAd {W : Type*} [AddCommGroup W] [Module R W]
    [LieRingModule (SpecialLinear.sl n R) W] [LieModule.IsTrivial (SpecialLinear.sl n R) W]
    (g : Matrix.specialOrthogonalGroup n R) (A : SpecialLinear.sl n R) (w : W) :
    Representation.trivial R (Matrix.specialOrthogonalGroup n R) W g ⁅A, w⁆ =
      ⁅specialOrthogonalAd n R g A,
        Representation.trivial R (Matrix.specialOrthogonalGroup n R) W g w⁆ := by
  simp [trivial_lie_zero]

end SpecialOrthogonal

section SlFinTwoSO2

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

private def slFinTwoH : SpecialLinear.sl (Fin 2) R :=
  ⟨!![1, 0; 0, -1], by simp⟩

private def slFinTwoS : SpecialLinear.sl (Fin 2) R :=
  ⟨!![0, 1; 1, 0], by simp⟩

private def slFinTwoJ : SpecialLinear.sl (Fin 2) R :=
  ⟨!![0, -1; 1, 0], by simp⟩

private theorem slFinTwoJ_mem_so : slFinTwoJ R ∈ soSubalgebra (Fin 2) R := by
  rw [mem_soSubalgebra]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFinTwoJ]

private def rot90 : Matrix.specialOrthogonalGroup (Fin 2) R :=
  ⟨!![0, -1; 1, 0], Matrix.of_mem_specialOrthogonalGroup_fin_two_iff.mpr ⟨rfl, rfl, by ring⟩⟩

private theorem specialOrthogonalAd_rot90_H :
    specialOrthogonalAd (Fin 2) R (rot90 R) (slFinTwoH R) = -slFinTwoH R := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [specialOrthogonalAd_apply_val, rot90, slFinTwoH, Matrix.mul_apply, Fin.sum_univ_two]

private theorem specialOrthogonalAd_rot90_S :
    specialOrthogonalAd (Fin 2) R (rot90 R) (slFinTwoS R) = -slFinTwoS R := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [specialOrthogonalAd_apply_val, rot90, slFinTwoS, Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def slFinTwoIntegralEquivFun :
    SpecialLinear.sl (Fin 2) R ≃ₗ[R] (Fin 3 → R) where
  toFun A := ![A.1 0 0, A.1 0 1 + A.1 1 0, A.1 1 0]
  map_add' A B := by ext k; fin_cases k <;> simp; ring
  map_smul' r A := by ext k; fin_cases k <;> simp; ring
  invFun v := v 0 • slFinTwoH R + v 1 • slFinTwoBasis R 0 + v 2 • slFinTwoJ R
  left_inv A := by
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [slFinTwoH, slFinTwoJ, val_one_one_eq_neg_val_zero_zero]
  right_inv v := by
    ext k
    fin_cases k <;> simp [slFinTwoH, slFinTwoJ]

private noncomputable def slFinTwoIntegralBasis :
    Module.Basis (Fin 3) R (SpecialLinear.sl (Fin 2) R) :=
  Module.Basis.ofEquivFun (slFinTwoIntegralEquivFun R)

private theorem slFinTwoIntegralBasis_two : slFinTwoIntegralBasis R 2 = slFinTwoJ R := by
  simp [slFinTwoIntegralBasis, slFinTwoIntegralEquivFun]

/-- For `(sl (Fin 2) R, so(2), SO(2))` over any commutative ring `R`, relative cochains vanish in
all degrees `≥ 3` for arbitrary `sl₂`-modules `W` and `SO(2)`-representations `ρ`. -/
theorem subsingleton_relativeGroupCochainAddThreeSlFinTwoSO2
    (W : Type*) [AddCommGroup W] [Module R W]
    [LieRingModule (SpecialLinear.sl (Fin 2) R) W]
    [LieModule R (SpecialLinear.sl (Fin 2) R) W]
    (ρ : Representation R (Matrix.specialOrthogonalGroup (Fin 2) R) W) (q : ℕ) :
    Subsingleton (relativeGroupCochain R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
      (specialOrthogonalAd (Fin 2) R) ρ (q + 3)) := by
  let L := SpecialLinear.sl (Fin 2) R
  let e := slFinTwoIntegralBasis R
  refine ⟨fun ω₁ ω₂ ↦ Subtype.ext ?_⟩
  suffices hzero : ∀ ω : relativeGroupCochain R L (soSubalgebra (Fin 2) R) W
      (specialOrthogonalAd (Fin 2) R) ρ (q + 3), ω.1 = 0 by
    rw [hzero ω₁, hzero ω₂]
  intro ω
  refine e.ext_alternating fun v hv ↦ ?_
  rw [zero_apply]
  cases q with
  | zero =>
    obtain ⟨i, hi⟩ := (Finite.injective_iff_bijective.mp hv).2 (2 : Fin 3)
    exact (mem_relativeCochain_iff.mp (mem_relativeGroupCochain_iff.mp ω.2).1).1
      (fun j ↦ e (v j)) i (by rw [hi, slFinTwoIntegralBasis_two]; exact slFinTwoJ_mem_so R)
  | succ q =>
    have hcard : Fintype.card (Fin 3) < Fintype.card (Fin (q + 1 + 3)) := by simp
    exact absurd (Fintype.card_le_of_injective v hv) (not_le.mpr hcard)

/-- Relative cohomology `H^{q + 3}(sl (Fin 2) R, so(2), SO(2); W)` vanishes in all degrees `≥ 3`
over any commutative ring `R`, for any compatible `(sl₂, SO(2))`-module `(W, ρ)`. -/
theorem subsingleton_relativeGroupCohomologyAddThreeSlFinTwoSO2
    (W : Type*) [AddCommGroup W] [Module R W]
    [LieRingModule (SpecialLinear.sl (Fin 2) R) W]
    [LieModule R (SpecialLinear.sl (Fin 2) R) W]
    (ρ : Representation R (Matrix.specialOrthogonalGroup (Fin 2) R) W)
    (hcompat : ∀ g A w, ρ g ⁅A, w⁆ = ⁅specialOrthogonalAd (Fin 2) R g A, ρ g w⁆) (q : ℕ) :
    Subsingleton (relativeGroupCohomology R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
      (specialOrthogonalAd (Fin 2) R) ρ (specialOrthogonalAd_lie (Fin 2) R) hcompat (q + 3)) := by
  have : Subsingleton
      ((relativeGroupCochainComplex R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
        (specialOrthogonalAd (Fin 2) R) ρ
        (specialOrthogonalAd_lie (Fin 2) R) hcompat).X (q + 3)) :=
    subsingleton_relativeGroupCochainAddThreeSlFinTwoSO2 R W ρ q
  exact subsingleton_homology_of_subsingleton_X

variable [Invertible (2 : R)]

private def slFinTwoCartanEquivFun : SpecialLinear.sl (Fin 2) R ≃ₗ[R] (Fin 3 → R) where
  toFun A := ![A.1 0 0, ⅟(2 : R) * (A.1 0 1 + A.1 1 0), ⅟(2 : R) * (A.1 1 0 - A.1 0 1)]
  map_add' A B := by ext k; fin_cases k <;> simp <;> ring
  map_smul' r A := by ext k; fin_cases k <;> simp <;> ring
  invFun v := v 0 • slFinTwoH R + v 1 • slFinTwoS R + v 2 • slFinTwoJ R
  left_inv A := by
    have h2inv : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [slFinTwoH, slFinTwoS, slFinTwoJ, val_one_one_eq_neg_val_zero_zero]
    · linear_combination A.1 0 1 * h2inv
    · linear_combination A.1 1 0 * h2inv
  right_inv v := by
    have h2inv : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
    ext k
    fin_cases k <;> simp [slFinTwoH, slFinTwoS, slFinTwoJ]
    · linear_combination v 1 * h2inv
    · linear_combination v 2 * h2inv

private noncomputable def slFinTwoCartanBasis :
    Module.Basis (Fin 3) R (SpecialLinear.sl (Fin 2) R) :=
  Module.Basis.ofEquivFun (slFinTwoCartanEquivFun R)

private theorem slFinTwoCartanBasis_zero : slFinTwoCartanBasis R 0 = slFinTwoH R := by
  simp [slFinTwoCartanBasis, slFinTwoCartanEquivFun]

private theorem slFinTwoCartanBasis_one : slFinTwoCartanBasis R 1 = slFinTwoS R := by
  simp [slFinTwoCartanBasis, slFinTwoCartanEquivFun]

private theorem slFinTwoCartanBasis_two : slFinTwoCartanBasis R 2 = slFinTwoJ R := by
  simp [slFinTwoCartanBasis, slFinTwoCartanEquivFun]

private theorem eq_smul_slFinTwoJ_of_mem_so {A : SpecialLinear.sl (Fin 2) R}
    (hA : A ∈ soSubalgebra (Fin 2) R) : A = A.1 1 0 • slFinTwoJ R := by
  have hT : A.1ᵀ = -A.1 := (mem_soSubalgebra (Fin 2) R A).mp hA
  have h00 : A.1 0 0 = 0 := by
    have h := congrFun (congrFun hT 0) 0
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    have h2 : (2 : R) * A.1 0 0 = 0 := by linear_combination h
    calc A.1 0 0 = ⅟(2 : R) * ((2 : R) * A.1 0 0) := by rw [← mul_assoc, invOf_mul_self, one_mul]
      _ = 0 := by rw [h2, mul_zero]
  have h01 : A.1 0 1 = -A.1 1 0 := by
    have h := congrFun (congrFun hT 1) 0
    simpa [Matrix.transpose_apply] using h
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slFinTwoJ, h00, h01, val_one_one_eq_neg_val_zero_zero]

private def slFinTwoPProj : SpecialLinear.sl (Fin 2) R →ₗ[R] (Fin 2 → R) where
  toFun A := ![A.1 0 0, ⅟(2 : R) * (A.1 0 1 + A.1 1 0)]
  map_add' A B := by ext k; fin_cases k <;> simp; ring
  map_smul' r A := by ext k; fin_cases k <;> simp; ring

private def slFinTwoVol : SpecialLinear.sl (Fin 2) R [⋀^Fin 2]→ₗ[R] R :=
  Matrix.detRowAlternating.compLinearMap (slFinTwoPProj R)

private theorem slFinTwoVol_apply (v : Fin 2 → SpecialLinear.sl (Fin 2) R) :
    slFinTwoVol R v =
      slFinTwoPProj R (v 0) 0 * slFinTwoPProj R (v 1) 1 -
        slFinTwoPProj R (v 0) 1 * slFinTwoPProj R (v 1) 0 := by
  have h : slFinTwoVol R v = Matrix.det (Matrix.of (slFinTwoPProj R ∘ v)) := rfl
  rw [h, Matrix.det_fin_two]
  rfl

private theorem slFinTwoVol_apply_HS : slFinTwoVol R ![slFinTwoH R, slFinTwoS R] = 1 := by
  rw [slFinTwoVol_apply]
  have h2inv : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  simp [slFinTwoPProj, slFinTwoH, slFinTwoS]
  linear_combination h2inv

private theorem slFinTwoVol_eq_zero_of_mem_so (v : Fin 2 → SpecialLinear.sl (Fin 2) R)
    (i : Fin 2) (hi : v i ∈ soSubalgebra (Fin 2) R) : slFinTwoVol R v = 0 := by
  have hpi : (slFinTwoPProj R ∘ v) i = 0 := by
    change slFinTwoPProj R (v i) = 0
    rw [eq_smul_slFinTwoJ_of_mem_so R hi]
    ext k
    fin_cases k <;> simp [slFinTwoPProj, slFinTwoJ]
  exact Matrix.detRowAlternating.map_coord_zero i hpi

private theorem slFinTwoVol_ad_invariant (g : Matrix.specialOrthogonalGroup (Fin 2) R)
    (v : Fin 2 → SpecialLinear.sl (Fin 2) R) :
    slFinTwoVol R (fun i ↦ specialOrthogonalAd (Fin 2) R g (v i)) = slFinTwoVol R v := by
  obtain ⟨h00, h01, hsq⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp g.2
  have h10 : g.1 1 0 = -g.1 0 1 := by linear_combination h01
  let α : R := g.1 0 0
  let β : R := g.1 0 1
  have hproj : ∀ A : SpecialLinear.sl (Fin 2) R,
      slFinTwoPProj R (specialOrthogonalAd (Fin 2) R g A) 0 =
        (α ^ 2 - β ^ 2) * slFinTwoPProj R A 0 + (2 * α * β) * slFinTwoPProj R A 1 ∧
      slFinTwoPProj R (specialOrthogonalAd (Fin 2) R g A) 1 =
        -(2 * α * β) * slFinTwoPProj R A 0 + (α ^ 2 - β ^ 2) * slFinTwoPProj R A 1 := by
    intro A
    have h2inv : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
    constructor
    · simp only [slFinTwoPProj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, specialOrthogonalAd_apply_val,
        Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
        val_one_one_eq_neg_val_zero_zero, ← h00, h10]
      change (α * A.1 0 0 + β * A.1 1 0) * α + (α * A.1 0 1 + β * -A.1 0 0) * β =
        (α ^ 2 - β ^ 2) * A.1 0 0 + 2 * α * β * (⅟(2 : R) * (A.1 0 1 + A.1 1 0))
      linear_combination -(α * β * (A.1 0 1 + A.1 1 0)) * h2inv
    · simp only [slFinTwoPProj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, specialOrthogonalAd_apply_val,
        Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
        val_one_one_eq_neg_val_zero_zero, ← h00, h10]
      change ⅟(2 : R) * (((α * A.1 0 0 + β * A.1 1 0) * -β + (α * A.1 0 1 + β * -A.1 0 0) * α) +
        ((-β * A.1 0 0 + α * A.1 1 0) * α + (-β * A.1 0 1 + α * -A.1 0 0) * β)) =
        -(2 * α * β) * A.1 0 0 + (α ^ 2 - β ^ 2) * (⅟(2 : R) * (A.1 0 1 + A.1 1 0))
      linear_combination -(2 * α * β * A.1 0 0) * h2inv
  obtain ⟨h0a, h0b⟩ := hproj (v 0)
  obtain ⟨h1a, h1b⟩ := hproj (v 1)
  rw [slFinTwoVol_apply, slFinTwoVol_apply, h0a, h0b, h1a, h1b]
  have hsq' : α ^ 2 + β ^ 2 = 1 := hsq
  linear_combination
    (slFinTwoPProj R (v 0) 0 * slFinTwoPProj R (v 1) 1 -
      slFinTwoPProj R (v 0) 1 * slFinTwoPProj R (v 1) 0) * (α ^ 2 + β ^ 2 + 1) * hsq'

private theorem slFinTwoVol_lie_J (v : Fin 2 → SpecialLinear.sl (Fin 2) R) :
    slFinTwoVol R (Function.update v 0 ⁅slFinTwoJ R, v 0⁆) +
      slFinTwoVol R (Function.update v 1 ⁅slFinTwoJ R, v 1⁆) = 0 := by
  have hJ : ∀ A : SpecialLinear.sl (Fin 2) R,
      slFinTwoPProj R ⁅slFinTwoJ R, A⁆ 0 = -2 * slFinTwoPProj R A 1 ∧
      slFinTwoPProj R ⁅slFinTwoJ R, A⁆ 1 = 2 * slFinTwoPProj R A 0 := by
    intro A
    have h2inv : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
    constructor
    · simp only [slFinTwoPProj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, SpecialLinear.sl_bracket, slFinTwoJ,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        val_one_one_eq_neg_val_zero_zero]
      linear_combination (A.1 0 1 + A.1 1 0) * h2inv
    · simp only [slFinTwoPProj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, SpecialLinear.sl_bracket, slFinTwoJ,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        val_one_one_eq_neg_val_zero_zero]
      linear_combination (2 * A.1 0 0) * h2inv
  obtain ⟨h0a, h0b⟩ := hJ (v 0)
  obtain ⟨h1a, h1b⟩ := hJ (v 1)
  rw [slFinTwoVol_apply, slFinTwoVol_apply]
  simp only [Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  rw [h0a, h0b, h1a, h1b]
  ring

variable (W : Type*) [AddCommGroup W] [Module R W]
variable [LieRingModule (SpecialLinear.sl (Fin 2) R) W]
variable [LieModule R (SpecialLinear.sl (Fin 2) R) W]

/-- For `(sl (Fin 2) R, so(2), SO(2))` with `2` invertible in `R` and the trivial `SO(2)`-action
on `W`, the space of degree-one relative cochains is trivial. -/
theorem subsingleton_relativeGroupCochainOneSlFinTwoSO2 :
    Subsingleton (relativeGroupCochain R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
      (specialOrthogonalAd (Fin 2) R)
      (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W) 1) := by
  let L := SpecialLinear.sl (Fin 2) R
  let e := slFinTwoCartanBasis R
  refine ⟨fun ω₁ ω₂ ↦ Subtype.ext ?_⟩
  suffices hzero : ∀ ω : relativeGroupCochain R L (soSubalgebra (Fin 2) R) W
      (specialOrthogonalAd (Fin 2) R)
      (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W) 1, ω.1 = 0 by
    rw [hzero ω₁, hzero ω₂]
  intro ω
  have hinv := (mem_relativeGroupCochain_iff.mp ω.2).2 (rot90 R)⁻¹
  have kill_neg : ∀ x : L, specialOrthogonalAd (Fin 2) R (rot90 R) x = -x → ω.1 ![x] = 0 := by
    intro x hx
    have h := congrArg (fun f : L [⋀^Fin 1]→ₗ[R] W ↦ f ![x]) hinv
    have hcomp : (fun i : Fin 1 ↦ specialOrthogonalAd (Fin 2) R (rot90 R)⁻¹⁻¹ (![x] i)) =
        Function.update ![x] 0 (-![x] 0) := by
      funext i
      rw [Subsingleton.elim i 0, Matrix.cons_val_zero, Function.update_self, inv_inv, hx]
    simp only [Representation.alternatingMap_apply, Representation.trivial_apply] at h
    rw [hcomp, ω.1.map_update_neg, Function.update_eq_self] at h
    have h2 : (2 : R) • ω.1 ![x] = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr h.symm
    simpa only [smul_smul, invOf_mul_self, one_smul, smul_zero] using
      congrArg (fun w : W ↦ ⅟(2 : R) • w) h2
  have hH : ω.1 ![slFinTwoH R] = 0 := kill_neg _ (specialOrthogonalAd_rot90_H R)
  have hS : ω.1 ![slFinTwoS R] = 0 := kill_neg _ (specialOrthogonalAd_rot90_S R)
  have hJ : ω.1 ![slFinTwoJ R] = 0 :=
    (mem_relativeCochain_iff.mp (mem_relativeGroupCochain_iff.mp ω.2).1).1 ![slFinTwoJ R] 0
      (slFinTwoJ_mem_so R)
  refine e.ext_alternating fun v _ ↦ ?_
  have hv : (fun i ↦ e (v i)) = ![e (v 0)] := by funext i; fin_cases i; rfl
  rw [hv, zero_apply]
  generalize v 0 = k
  fin_cases k
  · simpa [e, slFinTwoCartanBasis_zero] using hH
  · simpa [e, slFinTwoCartanBasis_one] using hS
  · simpa [e, slFinTwoCartanBasis_two] using hJ

variable [LieModule.IsTrivial (SpecialLinear.sl (Fin 2) R) W]

private theorem smulRight_slFinTwoVol_mem (w : W) :
    (slFinTwoVol R).smulRight w ∈
      relativeGroupCochain R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
        (specialOrthogonalAd (Fin 2) R)
        (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W) 2 := by
  rw [mem_relativeGroupCochain_iff, mem_relativeCochain_iff]
  refine ⟨⟨fun v i hi ↦ by
      simp [AlternatingMap.smulRight_apply, slFinTwoVol_eq_zero_of_mem_so R v i hi],
    fun k ↦ by
      ext v
      simp only [AlternatingMap.lie_apply, trivial_lie_zero, zero_sub, zero_apply, neg_eq_zero,
        AlternatingMap.smulRight_apply, Fin.sum_univ_two, ← add_smul]
      rw [eq_smul_slFinTwoJ_of_mem_so R k.2]
      have h0 : Function.update v 0 ⁅k.1.1 1 0 • slFinTwoJ R, v 0⁆ =
          Function.update v 0 (k.1.1 1 0 • ⁅slFinTwoJ R, v 0⁆) := by simp [smul_lie]
      have h1 : Function.update v 1 ⁅k.1.1 1 0 • slFinTwoJ R, v 1⁆ =
          Function.update v 1 (k.1.1 1 0 • ⁅slFinTwoJ R, v 1⁆) := by simp [smul_lie]
      rw [h0, h1, (slFinTwoVol R).map_update_smul, (slFinTwoVol R).map_update_smul,
        smul_eq_mul, smul_eq_mul, ← mul_add, slFinTwoVol_lie_J, mul_zero, zero_smul]⟩,
    fun g ↦ by
      ext v
      simp [Representation.alternatingMap_apply, AlternatingMap.smulRight_apply,
        slFinTwoVol_ad_invariant]⟩

omit [LieModule.IsTrivial (SpecialLinear.sl (Fin 2) R) W] in
private theorem eq_smulRight_slFinTwoVol
    (ω : relativeGroupCochain R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
      (specialOrthogonalAd (Fin 2) R)
      (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W) 2) :
    (slFinTwoVol R).smulRight (ω.1 ![slFinTwoH R, slFinTwoS R]) = ω.1 := by
  let e := slFinTwoCartanBasis R
  refine e.ext_alternating fun v hv ↦ ?_
  have hv_eq : (fun i ↦ e (v i)) = ![e (v 0), e (v 1)] := by funext i; fin_cases i <;> rfl
  have hne : v 0 ≠ v 1 := fun h ↦ absurd (hv h) (by decide)
  rw [hv_eq]
  have hhor := (mem_relativeCochain_iff.mp (mem_relativeGroupCochain_iff.mp ω.2).1).1
  have hHS : ((slFinTwoVol R).smulRight (ω.1 ![slFinTwoH R, slFinTwoS R]))
      ![slFinTwoH R, slFinTwoS R] = ω.1 ![slFinTwoH R, slFinTwoS R] := by
    simp [AlternatingMap.smulRight_apply, slFinTwoVol_apply_HS]
  have hSH : ((slFinTwoVol R).smulRight (ω.1 ![slFinTwoH R, slFinTwoS R]))
      ![slFinTwoS R, slFinTwoH R] = ω.1 ![slFinTwoS R, slFinTwoH R] := by
    rw [alternatingMap_pair_swap ((slFinTwoVol R).smulRight _), hHS,
      (alternatingMap_pair_swap ω.1 _ _).symm]
  have hkillR (x : SpecialLinear.sl (Fin 2) R) :
      ((slFinTwoVol R).smulRight (ω.1 ![slFinTwoH R, slFinTwoS R])) ![x, slFinTwoJ R] =
        ω.1 ![x, slFinTwoJ R] := by
    rw [AlternatingMap.smulRight_apply,
      slFinTwoVol_eq_zero_of_mem_so R _ 1 (slFinTwoJ_mem_so R), zero_smul,
      hhor _ 1 (slFinTwoJ_mem_so R)]
  have hkillL (x : SpecialLinear.sl (Fin 2) R) :
      ((slFinTwoVol R).smulRight (ω.1 ![slFinTwoH R, slFinTwoS R])) ![slFinTwoJ R, x] =
        ω.1 ![slFinTwoJ R, x] := by
    rw [AlternatingMap.smulRight_apply,
      slFinTwoVol_eq_zero_of_mem_so R _ 0 (slFinTwoJ_mem_so R), zero_smul,
      hhor _ 0 (slFinTwoJ_mem_so R)]
  have he0 : e 0 = slFinTwoH R := slFinTwoCartanBasis_zero R
  have he1 : e 1 = slFinTwoS R := slFinTwoCartanBasis_one R
  have he2 : e 2 = slFinTwoJ R := slFinTwoCartanBasis_two R
  generalize v 0 = i at hne ⊢
  generalize v 1 = j at hne ⊢
  fin_cases i <;> fin_cases j
  · exact absurd rfl hne
  · simpa [he0, he1] using hHS
  · simpa [he0, he2] using hkillR (slFinTwoH R)
  · simpa [he0, he1] using hSH
  · exact absurd rfl hne
  · simpa [he1, he2] using hkillR (slFinTwoS R)
  · simpa [he0, he2] using hkillL (slFinTwoH R)
  · simpa [he1, he2] using hkillL (slFinTwoS R)
  · exact absurd rfl hne

/-- For `(sl (Fin 2) R, so(2), SO(2))` with trivial coefficients `W` and `2` invertible in `R`,
the space of degree-two relative cochains is linearly equivalent to `W`, via evaluation on
`![H, S]`. -/
noncomputable def relativeGroupCochainTwoEquivSlFinTwoSO2 :
    relativeGroupCochain R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
      (specialOrthogonalAd (Fin 2) R)
      (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W) 2 ≃ₗ[R] W where
  toFun ω := ω.1 ![slFinTwoH R, slFinTwoS R]
  invFun w := ⟨(slFinTwoVol R).smulRight w, smulRight_slFinTwoVol_mem R W w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ω := Subtype.ext (eq_smulRight_slFinTwoVol R W ω)
  right_inv w := by
    simp [AlternatingMap.smulRight_apply, slFinTwoVol_apply_HS]

/-- Degree-one relative cohomology `H¹(sl (Fin 2) R, so(2), SO(2); W)` vanishes when `2` is
invertible in `R` and `W` is trivial. -/
theorem subsingleton_relativeGroupCohomologyOneSlFinTwoSO2 :
    Subsingleton (relativeGroupCohomology R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
      (specialOrthogonalAd (Fin 2) R)
      (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W)
      (specialOrthogonalAd_lie (Fin 2) R)
      (trivial_compat_specialOrthogonalAd (Fin 2) R) 1) := by
  have : Subsingleton
      ((relativeGroupCochainComplex R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
        (specialOrthogonalAd (Fin 2) R)
        (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W)
        (specialOrthogonalAd_lie (Fin 2) R)
        (trivial_compat_specialOrthogonalAd (Fin 2) R)).X 1) :=
    subsingleton_relativeGroupCochainOneSlFinTwoSO2 R W
  exact subsingleton_homology_of_subsingleton_X

/-- Degree-two relative cohomology `H²(sl (Fin 2) R, so(2), SO(2); W)` is linearly equivalent
to `W` when `2` is invertible in `R` and `W` is trivial. -/
noncomputable def relativeGroupCohomologyTwoEquivSlFinTwoSO2 :
    relativeGroupCohomology R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
      (specialOrthogonalAd (Fin 2) R)
      (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W)
      (specialOrthogonalAd_lie (Fin 2) R)
      (trivial_compat_specialOrthogonalAd (Fin 2) R) 2 ≃ₗ[R] W := by
  let C := relativeGroupCochainComplex R (SpecialLinear.sl (Fin 2) R) (soSubalgebra (Fin 2) R) W
    (specialOrthogonalAd (Fin 2) R)
    (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W)
    (specialOrthogonalAd_lie (Fin 2) R)
    (trivial_compat_specialOrthogonalAd (Fin 2) R)
  have h1 : Subsingleton (C.X 1) := subsingleton_relativeGroupCochainOneSlFinTwoSO2 R W
  have h3 : Subsingleton (C.X 3) :=
    subsingleton_relativeGroupCochainAddThreeSlFinTwoSO2 R W
      (Representation.trivial R (Matrix.specialOrthogonalGroup (Fin 2) R) W) 0
  refine (homologyEquivOfDiffEqZero (C := C)
    (fun m hm ↦ by
      have hm1 : m = 1 := by omega
      subst hm1
      ext ω
      have hω : ω = 0 := @Subsingleton.elim _ h1 _ _
      simp [hω])
    (by
      ext ω
      exact @Subsingleton.elim _ h3 _ _)).trans
    (relativeGroupCochainTwoEquivSlFinTwoSO2 R W)

end SlFinTwoSO2

end TauCeti.LieModule.Cohomology
