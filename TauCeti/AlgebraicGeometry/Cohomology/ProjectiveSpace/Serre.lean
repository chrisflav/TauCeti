/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.LineBundle.Dual
import TauCeti.AlgebraicGeometry.Modules.Biprod
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Serre's finiteness and vanishing theorems on projective space

Let `R` be a Noetherian commutative ring, `M` a free `R`-module with a finite basis `b` indexed
by `κ`, so that `ℙ = Proj (Sym M)` is projective space over `R`, and `F` a coherent
(quasi-coherent, finite-type) `𝒪_ℙ`-module. This file proves Serre's two cohomology theorems on
projective space:

* **Serre's finiteness theorem** (`Module.Basis.finite_cohomology_of_isFiniteType`): for every
  `q : ℕ`, the cohomology group `Hᵠ(ℙ, F)` is a finitely generated `R`-module.
* **Serre's vanishing theorem**
  (`Module.Basis.exists_subsingleton_cohomology_tensor_twistingSheaf`): there exists `m₀ : ℤ` such
  that `Hᵠ(ℙ, F ⊗ 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`.

Both results are proved by descending induction on the cohomological degree `q`, starting above
the dimension where cohomology vanishes
(`Module.Basis.subsingleton_cohomology_proj_of_card_le`). At each step, Serre's Theorem A
(`TauCeti.SymmetricAlgebra.exists_epi_biproduct_twistingSheaf_neg`) presents `F` as a quotient of
a finite direct sum `E = ⨁_{Fin r} 𝒪(-n)` with coherent kernel `K`, and the long exact cohomology
sequence reduces `F` in degree `q` to `E` in degree `q` (known from the explicit cohomology of
twisting sheaves) and `K` in degree `q + 1` (the induction hypothesis).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2.
* [The Stacks Project, Tag 01XS](https://stacks.math.columbia.edu/tag/01XS) and
  [Tag 0200](https://stacks.math.columbia.edu/tag/0200).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory TopologicalSpace AlgebraicGeometry Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace Module.Basis

universe u

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R M

/-- Descending induction for Serre's finiteness theorem on `Proj (Sym M)` when `card κ ≥ 2`. -/
private lemma finite_cohomology_of_card_le_add [IsNoetherianRing R]
    {κ : Type*} [Fintype κ] [Nontrivial κ] (b : Module.Basis κ R M) :
    ∀ (d : ℕ) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ),
      Fintype.card κ ≤ q + d → Module.Finite R (Cohomology F q)
  | 0, F, _, _, q, hq => by
      have : Subsingleton (Cohomology F q) :=
        b.subsingleton_cohomology_proj_of_card_le F q (by omega)
      infer_instance
  | d + 1, F, _, _, q, hq => by
      have : Module.Finite R M := .of_basis b
      have : IsNoetherian (Proj 𝒜) := TauCeti.SymmetricAlgebra.instIsNoetherianProj R M
      obtain ⟨n₀, hn₀⟩ := TauCeti.SymmetricAlgebra.exists_epi_biproduct_twistingSheaf_neg R M F
      obtain ⟨r, π, hπ⟩ := hn₀ n₀ le_rfl
      have : (Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))).IsFinitePresentation :=
        TauCeti.SheafOfModules.IsInvertible.isFinitePresentation
          (M := Proj.twistingSheaf 𝒜 (-(n₀ : ℤ)))
      let E : (Proj 𝒜).Modules := ⨁ fun _ : Fin r ↦ Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))
      have hE_fp : E.IsFinitePresentation := inferInstance
      have : E.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation E
      have : E.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation E
      let K : (Proj 𝒜).Modules := kernel π
      have hK_fp : K.IsFinitePresentation := Scheme.Modules.isFinitePresentation_kernel π
      have : K.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation K
      have : K.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation K
      have hK_fin : Module.Finite R (Cohomology K (q + 1)) :=
        finite_cohomology_of_card_le_add b d K (q + 1) (by omega)
      have hTw_fin : Module.Finite R (Cohomology (Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))) q) :=
        b.finite_cohomology_twistingSheaf (-(n₀ : ℤ)) q
      have hE_fin : Module.Finite R (Cohomology E q) :=
        Module.Finite.equiv (cohomologyBiproductLinearEquiv R
          (fun _ : Fin r ↦ Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))) q).symm
      let S : ShortComplex (Proj 𝒜).Modules := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_kernel π
          mono_f := inferInstance
          epi_g := hπ }
      exact Scheme.Modules.finite_cohomology_X₃ R (Proj 𝒜) hS q

/-- **Serre's finiteness theorem on projective space.** Over a Noetherian ring `R`, the cohomology
`Hᵠ(Proj (Sym M), F)` of any coherent (quasi-coherent, finite-type) sheaf `F` on projective space
is a finitely generated `R`-module for every `q : ℕ`. -/
theorem finite_cohomology_of_isFiniteType [IsNoetherianRing R]
    {κ : Type*} [Finite κ] (b : Module.Basis κ R M)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  classical
  have := Fintype.ofFinite κ
  by_cases hκ : Nontrivial κ
  · exact finite_cohomology_of_card_le_add b (Fintype.card κ) F q (Nat.le_add_left _ _)
  · -- When `card κ ≤ 1`, embed `Proj (Sym M)` as a closed subscheme of `ℙ¹_R` and push forward.
    have hsub : Subsingleton κ := not_nontrivial_iff_subsingleton.mp hκ
    let w : Fin 2 → M := fun _ ↦ if h : Nonempty κ then b h.some else 0
    have hw : Function.Surjective (Fintype.linearCombination R w) := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
      refine top_unique ?_
      rw [← b.span_eq]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      refine ⟨0, ?_⟩
      have hne : Nonempty κ := ⟨i⟩
      simp [w, hne, Subsingleton.elim hne.some i]
    obtain ⟨j, hj, hjR⟩ := Scheme.exists_isClosedImmersion_proj_of_surjective R
      (Fintype.linearCombination R w) hw
    have : IsNoetherian (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R))) :=
      TauCeti.SymmetricAlgebra.instIsNoetherianProj R (Fin 2 → R)
    let jF := (pushforward j).obj F
    have hpf_fp : jF.IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_pushforward_of_isFinite j F
    have : jF.IsQuasicoherent :=
      SheafOfModules.instIsQuasicoherentOfIsFinitePresentation jF
    have : jF.IsFiniteType :=
      SheafOfModules.instIsFiniteTypeOfIsFinitePresentation jF
    have hfin := finite_cohomology_of_card_le_add (Pi.basisFun R (Fin 2)) 2 jF q (by simp)
    exact (j.moduleFinite_cohomology_pushforward_iff R F q).mp hfin

/-- Fixed-degree descending induction for Serre's vanishing theorem on `Proj (Sym M)`. -/
private lemma exists_subsingleton_cohomology_tensor_of_card_le_add [IsNoetherianRing R]
    {κ : Type*} [Fintype κ] [Nonempty κ] (b : Module.Basis κ R M) :
    ∀ (d : ℕ) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ),
      0 < q → Fintype.card κ ≤ q + d →
      ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q)
  | 0, F, _, _, q, _, hq =>
      ⟨0, fun m _ ↦ by
        have : Module.Finite R M := .of_basis b
        have : (Proj.twistingSheaf 𝒜 m).IsFinitePresentation :=
          TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := Proj.twistingSheaf 𝒜 m)
        have : (Proj.twistingSheaf 𝒜 m).IsQuasicoherent :=
          SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (Proj.twistingSheaf 𝒜 m)
        exact b.subsingleton_cohomology_proj_of_card_le (F ⊗ Proj.twistingSheaf 𝒜 m) q (by omega)⟩
  | d + 1, F, _, _, q, hq_pos, hq => by
      have : Module.Finite R M := .of_basis b
      have : IsNoetherian (Proj 𝒜) := TauCeti.SymmetricAlgebra.instIsNoetherianProj R M
      obtain ⟨n₀, hn₀⟩ := TauCeti.SymmetricAlgebra.exists_epi_biproduct_twistingSheaf_neg R M F
      obtain ⟨r, π, hπ⟩ := hn₀ n₀ le_rfl
      have : (Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))).IsFinitePresentation :=
        TauCeti.SheafOfModules.IsInvertible.isFinitePresentation
          (M := Proj.twistingSheaf 𝒜 (-(n₀ : ℤ)))
      let E : (Proj 𝒜).Modules := ⨁ fun _ : Fin r ↦ Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))
      have hE_fp : E.IsFinitePresentation := inferInstance
      have : E.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation E
      have : E.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation E
      let K : (Proj 𝒜).Modules := kernel π
      have hK_fp : K.IsFinitePresentation := Scheme.Modules.isFinitePresentation_kernel π
      have : K.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation K
      have : K.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation K
      obtain ⟨m₁, hm₁⟩ := exists_subsingleton_cohomology_tensor_of_card_le_add b d K (q + 1)
        (Nat.succ_pos q) (by omega)
      refine ⟨max m₁ ((n₀ : ℤ) - (Fintype.card κ : ℤ) + 1), fun m hm ↦ ?_⟩
      have hmK : Subsingleton (Cohomology (K ⊗ Proj.twistingSheaf 𝒜 m) (q + 1)) :=
        hm₁ m (le_trans (le_max_left _ _) hm)
      -- Tensor the short exact sequence `0 ⟶ K ⟶ E ⟶ F ⟶ 0` with the invertible sheaf `𝒪(m)`.
      let S : ShortComplex (Proj 𝒜).Modules := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_kernel π
          mono_f := inferInstance
          epi_g := hπ }
      let T : (Proj 𝒜).Modules ⥤ (Proj 𝒜).Modules :=
        MonoidalCategory.tensorRight (Proj.twistingSheaf 𝒜 m)
      have hTeq : T.IsEquivalence :=
        Scheme.Modules.isEquivalence_tensorRight_of_isInvertible (Proj.twistingSheaf 𝒜 m)
      have hST : (S.map T).ShortExact := hS.map_of_exact T
      -- Identify `E ⊗ 𝒪(m)` with `⨁_{Fin r} 𝒪(m - n₀)`.
      let eBip : E ⊗ Proj.twistingSheaf 𝒜 m ≅
          ⨁ fun _ : Fin r ↦ Proj.twistingSheaf 𝒜 (-(n₀ : ℤ) + m) :=
        T.mapBiproduct (fun _ : Fin r ↦ Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))) ≪≫
          biproduct.mapIso fun _ ↦
            Proj.twistingSheaf.tensorIso (_root_.SymmetricAlgebra.ι R M)
              (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule R M)
              (TauCeti.SymmetricAlgebra.iSup_basicOpen_ι_eq_top R M id (by simp)) (-(n₀ : ℤ)) m
      have hTw : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 (-(n₀ : ℤ) + m)) q) :=
        b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt
          (m := -(n₀ : ℤ) + m) (by have := le_trans (le_max_right m₁ _) hm; omega) hq_pos
      have hE : Subsingleton (Cohomology (E ⊗ Proj.twistingSheaf 𝒜 m) q) :=
        ((cohomologyBaseLinearEquivOfIso R eBip q).trans
          (cohomologyBiproductLinearEquiv R
            (fun _ : Fin r ↦ Proj.twistingSheaf 𝒜 (-(n₀ : ℤ) + m)) q)).toEquiv.subsingleton
      exact subsingleton_cohomology_X₃ hST q (q + 1) rfl hE hmK

/-- **Serre's vanishing theorem on projective space.** Over a Noetherian ring `R`, for any
coherent (quasi-coherent, finite-type) sheaf `F` on `Proj (Sym M)`, there exists `m₀ : ℤ` such
that `Hᵠ(Proj (Sym M), F ⊗ 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`. -/
theorem exists_subsingleton_cohomology_tensor_twistingSheaf [IsNoetherianRing R]
    {κ : Type*} [Finite κ] (b : Module.Basis κ R M)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  have := Fintype.ofFinite κ
  have : Module.Finite R M := .of_basis b
  by_cases hne : Nonempty κ
  · have hstep : ∀ q : Fin (Fintype.card κ),
        ∃ m₀ : ℤ, ∀ m ≥ m₀, 0 < q.1 →
          Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q.1) := by
      intro q
      by_cases hq : 0 < q.1
      · obtain ⟨m₀, hm₀⟩ := exists_subsingleton_cohomology_tensor_of_card_le_add b
          (Fintype.card κ) F q.1 hq (Nat.le_add_left _ _)
        exact ⟨m₀, fun m hm _ ↦ hm₀ m hm⟩
      · exact ⟨0, fun _ _ h ↦ (hq h).elim⟩
    choose mBound hmBound using hstep
    have hcard_pos : 0 < Fintype.card κ := Fintype.card_pos
    let m₀ : ℤ := (Finset.univ.image mBound).max'
      (Finset.image_nonempty.mpr ⟨⟨0, hcard_pos⟩, Finset.mem_univ _⟩)
    refine ⟨m₀, fun m hm q hq ↦ ?_⟩
    by_cases hlt : q < Fintype.card κ
    · have hle : mBound ⟨q, hlt⟩ ≤ m₀ :=
        Finset.le_max' _ _ (Finset.mem_image_of_mem mBound (Finset.mem_univ ⟨q, hlt⟩))
      exact hmBound ⟨q, hlt⟩ m (hle.trans hm) hq
    · have : (Proj.twistingSheaf 𝒜 m).IsFinitePresentation :=
        TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := Proj.twistingSheaf 𝒜 m)
      have : (Proj.twistingSheaf 𝒜 m).IsQuasicoherent :=
        SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (Proj.twistingSheaf 𝒜 m)
      exact b.subsingleton_cohomology_proj_of_card_le (F ⊗ Proj.twistingSheaf 𝒜 m) q (by omega)
  · have : IsEmpty κ := not_nonempty_iff.mp hne
    have htop : (⊥ : (Proj 𝒜).Opens) = ⊤ := by
      simpa using TauCeti.SymmetricAlgebra.iSup_basicOpen_ι_eq_top R M b b.span_eq
    have : IsEmpty (Proj 𝒜) :=
      ⟨fun x ↦ by simpa [← htop] using (Opens.mem_top x)⟩
    exact ⟨0, fun m _ q _ ↦
      Scheme.Modules.subsingleton_cohomology_of_isEmpty (F ⊗ Proj.twistingSheaf 𝒜 m) q⟩

end Module.Basis
