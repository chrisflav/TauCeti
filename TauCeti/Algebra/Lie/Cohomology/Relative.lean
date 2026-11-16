/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.LinearAlgebra.Alternating.Quotient
public import TauCeti.RepresentationTheory.AlternatingMap

/-!
# Relative Lie algebra cochains and cohomology

Let `L` be a Lie algebra over a commutative ring `R`, `K` a Lie subalgebra of `L`, and `M` an
`L`-module. A Chevalley–Eilenberg `n`-cochain `ω : L [⋀^Fin n]→ₗ[R] M` is **relative to `K`**
(basic, i.e. horizontal and `K`-invariant) if:

1. `ω` vanishes whenever at least one of its arguments lies in `K` (equivalently, in positive
   degree `n + 1`, all interior products `ω.curryLeft k` for `k ∈ K` vanish);
2. `⁅(k : L), ω⁆ = 0` for all `k : K`.

By Cartan's formula `ι_k (d ω) = ⁅k, ω⁆ - d (ι_k ω)` and `L`-equivariance of the differential, the
relative cochains form a subcomplex `relativeCochainComplex R L K M` of the Chevalley–Eilenberg
complex (`d_mem_relativeCochain`), whose cohomology is the relative Lie algebra cohomology
`Hⁿ(L, K; M)` (`relativeCohomology`). Descending alternating maps to `L ⧸ K` identifies
`relativeCochain R L K M n` with the `K`-invariants in `(L ⧸ K) [⋀^Fin n]→ₗ[R] M`
(`relativeCochainEquiv`).

When a group `G` acts compatibly on `L` by Lie algebra automorphisms (`Ad`) and on `M` (`ρ`), the
Chevalley–Eilenberg differential is `G`-equivariant (`alternatingMap_d`). Taking `G`-invariant
relative cochains defines the group-relative complex `relativeGroupCochainComplex` and cohomology
`Hⁿ(L, K, G; M)` (`relativeGroupCohomology`), which accounts for disconnected component groups.
When `Ad(G)` stabilizes `K` and `G`-invariance implies `K`-invariance on `(L ⧸ K) [⋀^Fin n]→ₗ[R] M`,
`relativeGroupCochainEquivIntertwiningMap` identifies the degree-`n` cochains with
`Hom_G(⋀ⁿ(L ⧸ K), M)`.

## Main definitions

* `TauCeti.LieModule.Cohomology.relativeCochain`: the `R`-module of `K`-relative `n`-cochains.
* `TauCeti.LieModule.Cohomology.relativeCochainComplex`: the relative cochain complex `C•(L, K; M)`.
* `TauCeti.LieModule.Cohomology.relativeCohomology`: relative Lie algebra cohomology `Hⁿ(L, K; M)`.
* `TauCeti.LieModule.Cohomology.relativeCochainEquiv`: identification of `Cⁿ(L, K; M)` with
  `K`-invariant alternating forms on `L ⧸ K`.
* `TauCeti.LieModule.Cohomology.relativeCohomologyZeroEquiv`: `H⁰(L, K; M) ≃ₗ[R] M^L`.
* `TauCeti.LieModule.Cohomology.relativeGroupCochain`,
  `TauCeti.LieModule.Cohomology.relativeGroupCochainComplex`,
  `TauCeti.LieModule.Cohomology.relativeGroupCohomology`: the group-relative complex
  `C•(L, K, G; M)` and its cohomology.
* `TauCeti.LieModule.Cohomology.relativeGroupCochainEquivIntertwiningMap`: identification of
  `Cⁿ(L, K, G; M)` with `Representation.IntertwiningMap ((quotientAd).exteriorPower n) ρ`.

## Main results

* `TauCeti.LieModule.Cohomology.mem_relativeCochain_succ_iff`: characterization via interior
  products and Lie derivatives.
* `TauCeti.LieModule.Cohomology.d_mem_relativeCochain`: relative cochains are closed under `d`.
* `TauCeti.LieModule.Cohomology.relativeCochainComplexBotIso`: `C•(L, ⊥; M) ≅ C•(L, M)`.
* `TauCeti.LieModule.Cohomology.alternatingMap_lie`,
  `TauCeti.LieModule.Cohomology.alternatingMap_d`: `G`-equivariance of Lie derivatives and the
  Chevalley–Eilenberg differential.
* `TauCeti.LieModule.Cohomology.relativeGroupCohomologyZeroEquiv`:
  `H⁰(L, K, G; M) ≃ₗ[R] M^L ∩ M^G`.

## References

* A. Borel and N. Wallach, *Continuous Cohomology, Discrete Subgroups, and Representations of
  Reductive Groups*, 2nd ed., AMS, 2000, Chapter I, §1.
* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
-/

public section

open CategoryTheory AlternatingMap

namespace TauCeti.LieModule.Cohomology

section Subalgebra

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L] (K : LieSubalgebra R L)
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The `R`-submodule of Chevalley–Eilenberg `n`-cochains relative to a Lie subalgebra `K`:
cochains that vanish whenever an argument lies in `K` and are annihilated by the Lie derivative
along every `k : K`. -/
def relativeCochain (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) where
  carrier :=
    {ω | (∀ (v : Fin n → L) (i : Fin n), v i ∈ K → ω v = 0) ∧ ∀ k : K, ⁅(k : L), ω⁆ = 0}
  add_mem' {ω₁ ω₂} h₁ h₂ :=
    ⟨fun v i hi ↦ by simp [h₁.1 v i hi, h₂.1 v i hi],
      fun k ↦ by rw [lie_add, h₁.2 k, h₂.2 k, add_zero]⟩
  zero_mem' := ⟨fun _ _ _ ↦ rfl, fun k ↦ lie_zero _⟩
  smul_mem' r {ω} h :=
    ⟨fun v i hi ↦ by simp [h.1 v i hi],
      fun k ↦ by rw [lie_smul, h.2 k, smul_zero]⟩

variable {R L K M}

/-- Membership in `relativeCochain R L K M n`. -/
theorem mem_relativeCochain_iff {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ relativeCochain R L K M n ↔
      (∀ (v : Fin n → L) (i : Fin n), v i ∈ K → ω v = 0) ∧ ∀ k : K, ⁅(k : L), ω⁆ = 0 :=
  Iff.rfl

/-- In positive degree, a cochain is `K`-relative if and only if every interior product `ι_k ω`
and every Lie derivative `⁅k, ω⁆` along `k : K` vanishes. -/
theorem mem_relativeCochain_succ_iff {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M} :
    ω ∈ relativeCochain R L K M (n + 1) ↔
      (∀ k : K, ω.curryLeft k = 0) ∧ ∀ k : K, ⁅(k : L), ω⁆ = 0 := by
  have h := AlternatingMap.map_eq_zero_of_mem_iff_curryLeft (P := (K : Submodule R L)) ω
  simp only [LieSubalgebra.mem_toSubmodule] at h
  rw [mem_relativeCochain_iff, h]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun k ↦ h₁ k k.2, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨fun x hx ↦ h₁ ⟨x, hx⟩, h₂⟩⟩

/-- The Chevalley–Eilenberg differential preserves `K`-relative cochains. -/
theorem d_mem_relativeCochain {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ relativeCochain R L K M n) :
    d R L M n ω ∈ relativeCochain R L K M (n + 1) := by
  rw [mem_relativeCochain_succ_iff]
  refine ⟨fun k ↦ ?_, fun k ↦ by rw [lie_d, hω.2 k, _root_.map_zero]⟩
  cases n with
  | zero =>
    rw [curryLeft_d_zero, hω.2 k]
  | succ n =>
    rw [curryLeft_d_succ, hω.2 k, (mem_relativeCochain_succ_iff.mp hω).1 k, _root_.map_zero,
      sub_self]

variable (R L K M)

/-- The differential on the `K`-relative Chevalley–Eilenberg cochains. -/
def relativeD (n : ℕ) : relativeCochain R L K M n →ₗ[R] relativeCochain R L K M (n + 1) where
  toFun ω := ⟨d R L M n ω.1, d_mem_relativeCochain ω.2⟩
  map_add' ω₁ ω₂ := Subtype.ext (map_add (d R L M n) ω₁.1 ω₂.1)
  map_smul' r ω := Subtype.ext (map_smul (d R L M n) r ω.1)

/-- The underlying alternating map of `relativeD R L K M n ω` is `d R L M n ω.1`. -/
@[simp]
theorem relativeD_coe (n : ℕ) (ω : relativeCochain R L K M n) :
    (relativeD R L K M n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω.1 :=
  (rfl)

/-- The relative differential squares to zero. -/
@[simp]
theorem relativeD_relativeD (n : ℕ) (ω : relativeCochain R L K M n) :
    relativeD R L K M (n + 1) (relativeD R L K M n ω) = 0 :=
  Subtype.ext (d_d n ω.1)

/-- The relative differential squares to zero as a composition of linear maps. -/
@[simp]
theorem relativeD_comp_relativeD (n : ℕ) :
    relativeD R L K M (n + 1) ∘ₗ relativeD R L K M n = 0 := by
  ext ω
  simp

/-- The relative Chevalley–Eilenberg cochain complex `C•(L, K; M)`. -/
@[expose] noncomputable def relativeCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (relativeCochain R L K M n))
    (fun n ↦ ModuleCat.ofHom (relativeD R L K M n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, relativeD_comp_relativeD, ModuleCat.ofHom_zero]

/-- The degree-`n` term of the relative cochain complex is `relativeCochain R L K M n`. -/
@[simp]
theorem relativeCochainComplex_X (n : ℕ) :
    (relativeCochainComplex R L K M).X n = ModuleCat.of R (relativeCochain R L K M n) :=
  (rfl)

/-- The differential of the relative cochain complex from degree `n` to degree `n + 1`. -/
@[simp]
theorem relativeCochainComplex_d_succ (n : ℕ) :
    (relativeCochainComplex R L K M).d n (n + 1) = ModuleCat.ofHom (relativeD R L K M n) := by
  simp [relativeCochainComplex]

/-- The `n`-th relative Lie algebra cohomology `Hⁿ(L, K; M)`. -/
noncomputable abbrev relativeCohomology (n : ℕ) : ModuleCat R :=
  (relativeCochainComplex R L K M).homology n

/-- The canonical inclusion `C•(L, K; M) ⟶ C•(L, M)` of the relative complex into the
Chevalley–Eilenberg complex. -/
noncomputable def relativeCochainComplexInclusion :
    relativeCochainComplex R L K M ⟶ cochainComplex R L M where
  f n := ModuleCat.ofHom (relativeCochain R L K M n).subtype
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    simp only [relativeCochainComplex_d_succ, cochainComplex_d_succ]
    refine ModuleCat.hom_ext (LinearMap.ext fun ω ↦ ?_)
    rfl

/-- In degree `n`, `relativeCochainComplexInclusion` sends a relative cochain to its underlying
alternating map. -/
@[simp]
theorem relativeCochainComplexInclusion_f_apply (n : ℕ) (ω : relativeCochain R L K M n) :
    (relativeCochainComplexInclusion R L K M).f n ω = ω.1 :=
  (rfl)

/-- Pulling back an alternating form on `L ⧸ K` along the quotient map intertwines the `K`-action
on forms on `L ⧸ K` with the `K`-action on forms on `L`. -/
theorem lie_compLinearMap_mkQ {n : ℕ} (k : K)
    (g : (L ⧸ K.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) :
    ⁅(k : L), g.compLinearMap K.toLieSubmodule.toSubmodule.mkQ⁆ =
      ⁅k, g⁆.compLinearMap K.toLieSubmodule.toSubmodule.mkQ := by
  ext v
  simp only [lie_apply, compLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  ext j
  by_cases hji : j = i
  · subst hji
    simp
    rfl
  · simp [hji]

/-- **Quotient description of relative cochains.** The `R`-module `Cⁿ(L, K; M)` of `K`-relative
cochains is linearly equivalent to the `K`-invariant alternating forms `(L ⧸ K) [⋀^Fin n]→ₗ[R] M`.
-/
noncomputable def relativeCochainEquiv (n : ℕ) :
    relativeCochain R L K M n ≃ₗ[R]
      LieModule.maxTrivSubmodule R K ((L ⧸ K.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) :=
  LinearEquiv.symm
    { toFun g :=
        ⟨g.1.compLinearMap K.toLieSubmodule.toSubmodule.mkQ,
          (AlternatingMap.exists_compLinearMap_mkQ_iff K.toLieSubmodule.toSubmodule _).1 ⟨g.1, rfl⟩,
          fun k ↦ by rw [lie_compLinearMap_mkQ, g.2 k, AlternatingMap.zero_compLinearMap]⟩
      invFun ω :=
        ⟨AlternatingMap.liftQ K.toLieSubmodule.toSubmodule ω.1
            (fun v i hi ↦ (mem_relativeCochain_iff.mp ω.2).1 v i
              ((LieSubalgebra.mem_toLieSubmodule _).mp hi)),
          fun k ↦ by
            apply AlternatingMap.compLinearMap_injective K.toLieSubmodule.toSubmodule.mkQ
              K.toLieSubmodule.toSubmodule.mkQ_surjective
            dsimp only
            rw [← lie_compLinearMap_mkQ, AlternatingMap.liftQ_comp_mkQ,
              (mem_relativeCochain_iff.mp ω.2).2 k, AlternatingMap.zero_compLinearMap]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv g := Subtype.ext <|
        (AlternatingMap.liftQ_unique K.toLieSubmodule.toSubmodule _ _ rfl).symm
      right_inv ω := Subtype.ext (AlternatingMap.liftQ_comp_mkQ _ _ _) }

/-- Evaluating the quotient form attached to a relative cochain on quotient classes. -/
@[simp]
theorem relativeCochainEquiv_apply_mk (n : ℕ) (ω : relativeCochain R L K M n) (v : Fin n → L) :
    (relativeCochainEquiv R L K M n ω).1
        (fun i ↦ (LieSubmodule.Quotient.mk (v i) : L ⧸ K.toLieSubmodule)) =
      ω.1 v :=
  AlternatingMap.liftQ_apply_mk K.toLieSubmodule.toSubmodule ω.1
    (fun v i hi ↦ (mem_relativeCochain_iff.mp ω.2).1 v i
      ((LieSubalgebra.mem_toLieSubmodule _).mp hi)) v

/-- Pulling back a `K`-invariant alternating form on `L ⧸ K` gives its underlying cochain on `L`. -/
@[simp]
theorem relativeCochainEquiv_symm_apply_coe (n : ℕ)
    (g : LieModule.maxTrivSubmodule R K ((L ⧸ K.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)) :
    ((relativeCochainEquiv R L K M n).symm g).1 =
      g.1.compLinearMap K.toSubmodule.mkQ :=
  (rfl)

/-- Degree-zero relative cohomology `H⁰(L, K; M)` is linearly equivalent to `M^L`. -/
noncomputable def relativeCohomologyZeroEquiv :
    relativeCohomology R L K M 0 ≃ₗ[R] LieModule.maxTrivSubmodule R L M := by
  let C := relativeCochainComplex R L K M
  have hg : (C.sc' 0 0 1).g = ModuleCat.ofHom (relativeD R L K M 0) :=
    relativeCochainComplex_d_succ R L K M 0
  let eKer : LinearMap.ker ((C.sc' 0 0 1).g.hom) ≃ₗ[R] LinearMap.ker (relativeD R L K M 0) :=
    LinearEquiv.ofEq _ _ (congrArg (fun f : C.X 0 ⟶ C.X 1 ↦ LinearMap.ker f.hom) hg)
  let eInv : LinearMap.ker (relativeD R L K M 0) ≃ₗ[R] LieModule.maxTrivSubmodule R L M :=
    { toFun ω := ⟨ω.1.1 ![], fun x ↦ by
        have h0 : d R L M 0 ω.1.1 ![x] = 0 :=
          congrArg (fun f : relativeCochain R L K M 1 ↦ f.1 ![x]) (LinearMap.mem_ker.mp ω.2)
        simpa [d_zero_apply] using h0⟩
      invFun m :=
        ⟨⟨constLinearEquivOfIsEmpty (R' := R) (M'' := L) (N'' := M) (ι := Fin 0) m.1,
          fun _ i _ ↦ Fin.elim0 i,
          fun k ↦ by
            ext v
            simp [lie_apply, m.2 k]⟩,
          Subtype.ext <| by
            ext v
            simp [d_zero_apply, m.2 (v 0)]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv ω := Subtype.ext <| Subtype.ext <| by
        ext v
        simp [Subsingleton.elim v ![]]
      right_inv m := Subtype.ext rfl }
  exact (C.isoHomologyπ₀.symm ≪≫ C.cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    (C.sc' 0 0 1).moduleCatCyclesIso).toLinearEquiv.trans (eKer.trans eInv)

/-- Every cochain is relative to the trivial subalgebra `⊥`. -/
@[simp]
theorem relativeCochain_bot (n : ℕ) :
    relativeCochain R L ⊥ M n = ⊤ := by
  ext ω
  simp only [Submodule.mem_top, iff_true, mem_relativeCochain_iff]
  refine ⟨fun v i hi ↦ ?_, fun k ↦ ?_⟩
  · have h0 : v i = 0 := hi
    exact ω.map_coord_zero i h0
  · have hk : (k : L) = 0 := k.2
    rw [hk, zero_lie]

/-- For the trivial subalgebra `⊥`, the inclusion `C•(L, ⊥; M) ⟶ C•(L, M)` is an isomorphism. -/
instance isIso_relativeCochainComplexInclusion_bot :
    IsIso (relativeCochainComplexInclusion R L ⊥ M) := by
  have : ∀ n, IsIso ((relativeCochainComplexInclusion R L ⊥ M).f n) := fun n ↦ by
    let e : relativeCochain R L ⊥ M n ≃ₗ[R] (L [⋀^Fin n]→ₗ[R] M) :=
      (LinearEquiv.ofEq _ _ (relativeCochain_bot R L M n)).trans Submodule.topEquiv
    have hcomp : (relativeCochainComplexInclusion R L ⊥ M).f n = e.toModuleIso.hom :=
      ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)
    rw [hcomp]
    exact e.toModuleIso.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The relative complex for the trivial subalgebra `⊥` is canonically isomorphic to the full
Chevalley–Eilenberg complex `C•(L, M)`. -/
noncomputable def relativeCochainComplexBotIso :
    relativeCochainComplex R L ⊥ M ≅ cochainComplex R L M :=
  asIso (relativeCochainComplexInclusion R L ⊥ M)

end Subalgebra

section Group

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L] {K : LieSubalgebra R L}
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable {G : Type*} [Group G]

/-- A group representation `Ad` by Lie algebra automorphisms and a compatible representation `ρ`
on `M` intertwine the contragredient action on cochains with the Lie derivative. -/
theorem alternatingMap_lie {Ad : Representation R G L} {ρ : Representation R G M}
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆)
    {n : ℕ} (g : G) (x : L) (ω : L [⋀^Fin n]→ₗ[R] M) :
    Ad.alternatingMap ρ (Fin n) g ⁅x, ω⁆ = ⁅Ad g x, Ad.alternatingMap ρ (Fin n) g ω⁆ := by
  ext v
  simp only [Representation.alternatingMap_apply, lie_apply, map_sub, map_sum, hcompat]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  ext j
  by_cases hji : j = i
  · subst hji
    have hinv : Ad g⁻¹ ⁅Ad g x, v j⁆ = ⁅x, Ad g⁻¹ (v j)⁆ := by
      have h := hAd g⁻¹ (Ad g x) (v j)
      have hg : Ad g⁻¹ (Ad g x) = x := by
        rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
        rfl
      rwa [hg] at h
    simp [hinv]
  · simp [hji]

/-- A compatible pair of group representations `(Ad, ρ)` on `(L, M)` commutes with the
Chevalley–Eilenberg differential in every degree. -/
theorem alternatingMap_d {Ad : Representation R G L} {ρ : Representation R G M}
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆)
    (n : ℕ) (g : G) (ω : L [⋀^Fin n]→ₗ[R] M) :
    d R L M n (Ad.alternatingMap ρ (Fin n) g ω) =
      Ad.alternatingMap ρ (Fin (n + 1)) g (d R L M n ω) := by
  induction n with
  | zero =>
    ext v
    have hgg : Ad g (Ad g⁻¹ (v 0)) = v 0 := by
      rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
      rfl
    simp [d_zero_apply, hcompat, hgg, Subsingleton.elim (fun i : Fin 0 ↦ Ad g⁻¹ (![] i)) ![]]
  | succ n ih =>
    refine curryLeft_injective (LinearMap.ext fun x ↦ ?_)
    have hgg : Ad g (Ad g⁻¹ x) = x := by
      rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [curryLeft_d_succ, Representation.alternatingMap_curryLeft,
      Representation.alternatingMap_curryLeft, curryLeft_d_succ, map_sub,
      alternatingMap_lie hAd hcompat, hgg, ih]

variable (R L K M)

/-- The `R`-submodule of `(K, G)`-relative cochains in degree `n`: `K`-relative cochains that are
invariant under the contragredient `G`-action. -/
noncomputable def relativeGroupCochain (Ad : Representation R G L) (ρ : Representation R G M)
    (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) :=
  relativeCochain R L K M n ⊓ (Ad.alternatingMap ρ (Fin n)).invariants

variable {R L K M}

/-- Membership in `relativeGroupCochain R L K M Ad ρ n`. -/
theorem mem_relativeGroupCochain_iff {Ad : Representation R G L} {ρ : Representation R G M}
    {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ relativeGroupCochain R L K M Ad ρ n ↔
      ω ∈ relativeCochain R L K M n ∧ ∀ g : G, Ad.alternatingMap ρ (Fin n) g ω = ω :=
  Iff.rfl

/-- The Chevalley–Eilenberg differential preserves `(K, G)`-relative cochains. -/
theorem d_mem_relativeGroupCochain {Ad : Representation R G L} {ρ : Representation R G M}
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆)
    {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ relativeGroupCochain R L K M Ad ρ n) :
    d R L M n ω ∈ relativeGroupCochain R L K M Ad ρ (n + 1) :=
  ⟨d_mem_relativeCochain hω.1, fun g ↦ by
    rw [← alternatingMap_d hAd hcompat, hω.2 g]⟩

variable (R L K M)

/-- The differential on `(K, G)`-relative cochains. -/
noncomputable def relativeGroupD (Ad : Representation R G L) (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆) (n : ℕ) :
    relativeGroupCochain R L K M Ad ρ n →ₗ[R] relativeGroupCochain R L K M Ad ρ (n + 1) where
  toFun ω := ⟨d R L M n ω.1, d_mem_relativeGroupCochain hAd hcompat ω.2⟩
  map_add' ω₁ ω₂ := Subtype.ext (map_add (d R L M n) ω₁.1 ω₂.1)
  map_smul' r ω := Subtype.ext (map_smul (d R L M n) r ω.1)

/-- The underlying alternating map of `relativeGroupD ... n ω` is `d R L M n ω.1`. -/
@[simp]
theorem relativeGroupD_coe (Ad : Representation R G L) (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆) (n : ℕ)
    (ω : relativeGroupCochain R L K M Ad ρ n) :
    (relativeGroupD R L K M Ad ρ hAd hcompat n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω.1 :=
  (rfl)

/-- The `(K, G)`-relative differential squares to zero as a composition of linear maps. -/
@[simp]
theorem relativeGroupD_comp_relativeGroupD (Ad : Representation R G L) (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆) (n : ℕ) :
    relativeGroupD R L K M Ad ρ hAd hcompat (n + 1) ∘ₗ
      relativeGroupD R L K M Ad ρ hAd hcompat n = 0 :=
  LinearMap.ext fun ω ↦ Subtype.ext (d_d n ω.1)

/-- The `(K, G)`-relative Chevalley–Eilenberg cochain complex `C•(L, K, G; M)`. -/
@[expose] noncomputable def relativeGroupCochainComplex (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (relativeGroupCochain R L K M Ad ρ n))
    (fun n ↦ ModuleCat.ofHom (relativeGroupD R L K M Ad ρ hAd hcompat n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, relativeGroupD_comp_relativeGroupD, ModuleCat.ofHom_zero]

/-- The degree-`n` term of the `(K, G)`-relative cochain complex is
`relativeGroupCochain R L K M Ad ρ n`. -/
@[simp]
theorem relativeGroupCochainComplex_X (Ad : Representation R G L) (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆) (n : ℕ) :
    (relativeGroupCochainComplex R L K M Ad ρ hAd hcompat).X n =
      ModuleCat.of R (relativeGroupCochain R L K M Ad ρ n) :=
  (rfl)

/-- The differential of the `(K, G)`-relative cochain complex from degree `n` to degree `n + 1`. -/
@[simp]
theorem relativeGroupCochainComplex_d_succ (Ad : Representation R G L) (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆) (n : ℕ) :
    (relativeGroupCochainComplex R L K M Ad ρ hAd hcompat).d n (n + 1) =
      ModuleCat.ofHom (relativeGroupD R L K M Ad ρ hAd hcompat n) := by
  simp [relativeGroupCochainComplex]

/-- The `n`-th `(K, G)`-relative Lie algebra cohomology `Hⁿ(L, K, G; M)`. -/
noncomputable abbrev relativeGroupCohomology (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆) (n : ℕ) : ModuleCat R :=
  (relativeGroupCochainComplex R L K M Ad ρ hAd hcompat).homology n

/-- The canonical inclusion `C•(L, K, G; M) ⟶ C•(L, K; M)`. -/
noncomputable def relativeGroupCochainComplexInclusion (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆) :
    relativeGroupCochainComplex R L K M Ad ρ hAd hcompat ⟶ relativeCochainComplex R L K M where
  f n := ModuleCat.ofHom (Submodule.inclusion inf_le_left)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    simp only [relativeGroupCochainComplex_d_succ, relativeCochainComplex_d_succ]
    refine ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- In degree `n`, `relativeGroupCochainComplexInclusion` preserves the underlying alternating map.
-/
@[simp]
theorem relativeGroupCochainComplexInclusion_f_apply (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆)
    (n : ℕ) (ω : relativeGroupCochain R L K M Ad ρ n) :
    ((relativeGroupCochainComplexInclusion R L K M Ad ρ hAd hcompat).f n ω).1 = ω.1 :=
  (rfl)

/-- **Quotient description of `(K, G)`-relative cochains.** When `Ad(G)` stabilizes `K`,
`Cⁿ(L, K, G; M)` is linearly equivalent to the `K`- and `G`-invariant alternating forms on `L ⧸ K`.
-/
noncomputable def relativeGroupCochainEquiv (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hK : ∀ g, K.toLieSubmodule.toSubmodule ≤ K.toLieSubmodule.toSubmodule.comap (Ad g))
    (n : ℕ) :
    relativeGroupCochain R L K M Ad ρ n ≃ₗ[R]
      ((LieModule.maxTrivSubmodule R K ((L ⧸ K.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)).toSubmodule ⊓
        ((Ad.quotient K.toLieSubmodule.toSubmodule hK).alternatingMap ρ (Fin n)).invariants :
        Submodule R ((L ⧸ K.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)) :=
  LinearEquiv.symm
    { toFun f :=
        ⟨f.1.compLinearMap K.toLieSubmodule.toSubmodule.mkQ,
          ((relativeCochainEquiv R L K M n).symm ⟨f.1, f.2.1⟩).2,
          fun g ↦ by
            rw [← Representation.alternatingMap_compLinearMap (ρ₁' := Ad)
              (ρ₁ := Ad.quotient K.toLieSubmodule.toSubmodule hK) ρ K.toLieSubmodule.toSubmodule.mkQ
              (fun _ _ ↦ rfl), f.2.2 g]⟩
      invFun ω :=
        ⟨AlternatingMap.liftQ K.toLieSubmodule.toSubmodule ω.1
            (fun v i hi ↦ (mem_relativeCochain_iff.mp ω.2.1).1 v i
              ((LieSubalgebra.mem_toLieSubmodule _).mp hi)),
          fun k ↦ by
            apply AlternatingMap.compLinearMap_injective K.toLieSubmodule.toSubmodule.mkQ
              K.toLieSubmodule.toSubmodule.mkQ_surjective
            dsimp only
            rw [← lie_compLinearMap_mkQ, AlternatingMap.liftQ_comp_mkQ,
              (mem_relativeCochain_iff.mp ω.2.1).2 k, AlternatingMap.zero_compLinearMap],
          fun g ↦ by
            apply AlternatingMap.compLinearMap_injective K.toLieSubmodule.toSubmodule.mkQ
              K.toLieSubmodule.toSubmodule.mkQ_surjective
            dsimp only
            rw [Representation.alternatingMap_compLinearMap (ρ₁' := Ad)
              (ρ₁ := Ad.quotient K.toLieSubmodule.toSubmodule hK) ρ K.toLieSubmodule.toSubmodule.mkQ
              (fun _ _ ↦ rfl), AlternatingMap.liftQ_comp_mkQ,
              (mem_relativeGroupCochain_iff.mp ω.2).2 g]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv f := Subtype.ext <|
        (AlternatingMap.liftQ_unique K.toLieSubmodule.toSubmodule _ _ rfl).symm
      right_inv ω := Subtype.ext (AlternatingMap.liftQ_comp_mkQ _ _ _) }

/-- Evaluating the quotient form attached to a `(K, G)`-relative cochain on quotient classes. -/
theorem relativeGroupCochainEquiv_apply_mk (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hK : ∀ g, K.toLieSubmodule.toSubmodule ≤ K.toLieSubmodule.toSubmodule.comap (Ad g))
    (n : ℕ) (ω : relativeGroupCochain R L K M Ad ρ n) (v : Fin n → L) :
    (relativeGroupCochainEquiv R L K M Ad ρ hK n ω).1
        (fun i ↦ (LieSubmodule.Quotient.mk (v i) : L ⧸ K.toLieSubmodule)) =
      ω.1 v :=
  AlternatingMap.liftQ_apply_mk K.toLieSubmodule.toSubmodule ω.1
    (fun w i hi ↦ (mem_relativeCochain_iff.mp ω.2.1).1 w i
      ((LieSubalgebra.mem_toLieSubmodule _).mp hi)) v

/-- Pulling back a `K`- and `G`-invariant alternating form on `L ⧸ K` gives its underlying cochain
on `L`. -/
theorem relativeGroupCochainEquiv_symm_apply_coe (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hK : ∀ g, K.toLieSubmodule.toSubmodule ≤ K.toLieSubmodule.toSubmodule.comap (Ad g))
    (n : ℕ)
    (f : ((LieModule.maxTrivSubmodule R K ((L ⧸ K.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)).toSubmodule ⊓
      ((Ad.quotient K.toLieSubmodule.toSubmodule hK).alternatingMap ρ (Fin n)).invariants :
      Submodule R ((L ⧸ K.toLieSubmodule) [⋀^Fin n]→ₗ[R] M))) :
    ((relativeGroupCochainEquiv R L K M Ad ρ hK n).symm f).1 =
      f.1.compLinearMap K.toLieSubmodule.toSubmodule.mkQ :=
  (rfl)

/-- **Exterior-power description of `(K, G)`-relative cochains.** When `Ad(G)` stabilizes `K` and
`G`-invariance implies `K`-invariance on `(L ⧸ K) [⋀^Fin n]→ₗ[R] M`, `Cⁿ(L, K, G; M)` is linearly
equivalent to `Hom_G(⋀ⁿ(L ⧸ K), M)`. -/
noncomputable def relativeGroupCochainEquivIntertwiningMap (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hK : ∀ g, K.toLieSubmodule.toSubmodule ≤ K.toLieSubmodule.toSubmodule.comap (Ad g))
    (n : ℕ)
    (hGK : ((Ad.quotient K.toLieSubmodule.toSubmodule hK).alternatingMap ρ (Fin n)).invariants ≤
      (LieModule.maxTrivSubmodule R K ((L ⧸ K.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)).toSubmodule) :
    relativeGroupCochain R L K M Ad ρ n ≃ₗ[R]
      Representation.IntertwiningMap
        ((Ad.quotient K.toLieSubmodule.toSubmodule hK).exteriorPower n) ρ :=
  (relativeGroupCochainEquiv R L K M Ad ρ hK n).trans <|
    (LinearEquiv.ofEq _ _ (inf_eq_right.mpr hGK)).trans <|
      (Ad.quotient K.toLieSubmodule.toSubmodule hK).alternatingMapInvariantsEquivIntertwiningMap ρ n

/-- Evaluating the intertwining map attached to a `(K, G)`-relative cochain on a pure wedge of
quotient classes recovers the cochain on representatives. -/
theorem relativeGroupCochainEquivIntertwiningMap_apply_ιMulti (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hK : ∀ g, K.toLieSubmodule.toSubmodule ≤ K.toLieSubmodule.toSubmodule.comap (Ad g))
    (n : ℕ)
    (hGK : ((Ad.quotient K.toLieSubmodule.toSubmodule hK).alternatingMap ρ (Fin n)).invariants ≤
      (LieModule.maxTrivSubmodule R K ((L ⧸ K.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)).toSubmodule)
    (ω : relativeGroupCochain R L K M Ad ρ n) (v : Fin n → L) :
    relativeGroupCochainEquivIntertwiningMap R L K M Ad ρ hK n hGK ω
        (exteriorPower.ιMulti R n fun i ↦
          (LieSubmodule.Quotient.mk (v i) : L ⧸ K.toLieSubmodule)) =
      ω.1 v := by
  simp only [relativeGroupCochainEquivIntertwiningMap, LinearEquiv.trans_apply,
    Representation.alternatingMapInvariantsEquivIntertwiningMap_apply_ιMulti]
  exact AlternatingMap.liftQ_apply_mk K.toLieSubmodule.toSubmodule ω.1
    (fun w i hi ↦ (mem_relativeCochain_iff.mp ω.2.1).1 w i
      ((LieSubalgebra.mem_toLieSubmodule _).mp hi)) v

/-- Degree-zero `(K, G)`-relative cohomology `H⁰(L, K, G; M)` is linearly equivalent to
`M^L ∩ M^G`. -/
noncomputable def relativeGroupCohomologyZeroEquiv (Ad : Representation R G L)
    (ρ : Representation R G M)
    (hAd : ∀ g x y, Ad g ⁅x, y⁆ = ⁅Ad g x, Ad g y⁆)
    (hcompat : ∀ g x m, ρ g ⁅x, m⁆ = ⁅Ad g x, ρ g m⁆) :
    relativeGroupCohomology R L K M Ad ρ hAd hcompat 0 ≃ₗ[R]
      ((LieModule.maxTrivSubmodule R L M).toSubmodule ⊓ ρ.invariants : Submodule R M) := by
  let C := relativeGroupCochainComplex R L K M Ad ρ hAd hcompat
  have hg : (C.sc' 0 0 1).g = ModuleCat.ofHom (relativeGroupD R L K M Ad ρ hAd hcompat 0) :=
    relativeGroupCochainComplex_d_succ R L K M Ad ρ hAd hcompat 0
  let eKer : LinearMap.ker ((C.sc' 0 0 1).g.hom) ≃ₗ[R]
      LinearMap.ker (relativeGroupD R L K M Ad ρ hAd hcompat 0) :=
    LinearEquiv.ofEq _ _ (congrArg (fun f : C.X 0 ⟶ C.X 1 ↦ LinearMap.ker f.hom) hg)
  let eInv : LinearMap.ker (relativeGroupD R L K M Ad ρ hAd hcompat 0) ≃ₗ[R]
      ((LieModule.maxTrivSubmodule R L M).toSubmodule ⊓ ρ.invariants : Submodule R M) :=
    { toFun ω :=
        ⟨ω.1.1 ![],
          fun x ↦ by
            have h0 : d R L M 0 ω.1.1 ![x] = 0 :=
              congrArg (fun f : relativeGroupCochain R L K M Ad ρ 1 ↦ f.1 ![x])
                (LinearMap.mem_ker.mp ω.2)
            simpa [d_zero_apply] using h0,
          fun g ↦ by
            have hg0 := congrArg (fun f : L [⋀^Fin 0]→ₗ[R] M ↦ f ![])
              ((mem_relativeGroupCochain_iff.mp ω.1.2).2 g)
            simpa [Subsingleton.elim (fun i : Fin 0 ↦ Ad g⁻¹ (![] i)) ![]] using hg0⟩
      invFun m :=
        ⟨⟨constLinearEquivOfIsEmpty (R' := R) (M'' := L) (N'' := M) (ι := Fin 0) m.1,
          ⟨fun _ i _ ↦ Fin.elim0 i, fun k ↦ by ext v; simp [lie_apply, m.2.1 k]⟩,
          fun g ↦ by ext v; simp [m.2.2 g]⟩,
          Subtype.ext <| by ext v; simp [d_zero_apply, m.2.1 (v 0)]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv ω := Subtype.ext <| Subtype.ext <| by ext v; simp [Subsingleton.elim v ![]]
      right_inv m := Subtype.ext rfl }
  exact (C.isoHomologyπ₀.symm ≪≫ C.cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    (C.sc' 0 0 1).moduleCatCyclesIso).toLinearEquiv.trans (eKer.trans eInv)

end Group

end TauCeti.LieModule.Cohomology
