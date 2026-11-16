/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Biproducts
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Ample
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula
import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap

/-!
# Serre's finiteness and vanishing theorems on projective schemes

Let `R` be a Noetherian commutative ring. This file proves Serre's Theorem B (finiteness and
asymptotic vanishing of coherent cohomology) for projective schemes over `Spec R`:

* **Finiteness** (`AlgebraicGeometry.Scheme.IsProjectiveOver.finite_cohomology`,
  `TauCeti.SymmetricAlgebra.finite_cohomology_proj`): for every scheme `X` projective over `R`
  (in particular `Proj (Sym_R M)` for any finite `R`-module `M`, not necessarily free), every
  quasi-coherent `𝒪_X`-module `F` of finite type, and every `q : ℕ`, the cohomology group
  `Hᵠ(X, F)` is a finitely generated `R`-module.
* **Vanishing**
  (`AlgebraicGeometry.Scheme.Modules.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf`,
  `TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_twistingSheaf`): for every closed
  immersion `i : X ⟶ Proj (Sym_R M)` with `M` finite over `R` and every quasi-coherent `𝒪_X`-module
  `F` of finite type, there exists `m₀ : ℤ` such that `Hᵠ(X, F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀`
  and all `q > 0`.

The proof first uses Serre's Theorem A
(`AlgebraicGeometry.Scheme.Modules.exists_generatingSections_tensorPow_of_isAmple`) to present any
quasi-coherent sheaf `F` of finite type on a quasi-compact `Proj 𝒜` generated in degree one as a
quotient of a finite direct sum of negative twisting sheaves `⨁ 𝒪(-m)`
(`AlgebraicGeometry.Proj.exists_epi_biproduct_twistingSheaf`). On projective space
`ℙⁿ_R = Proj (Sym_R Rⁿ⁺¹)` with `n ≥ 1`, descending induction from the dimension bound
(`Module.Basis.subsingleton_cohomology_proj_of_card_le`) along the short exact sequence
`0 → K → ⨁ 𝒪(-m) → F → 0` yields both finiteness and vanishing, using the cohomology of `𝒪(m)`
(`Module.Basis.finite_cohomology_twistingSheaf`,
`Module.Basis.subsingleton_cohomology_twistingSheaf_of_neg_card_lt`) and kernel coherence
(`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_kernel`). For a general finite `R`-module
`M` and a closed subscheme `X ⟶ Proj (Sym_R M)`, choosing a surjection `R^{n+2} ↠ M` embeds
`Proj (Sym_R M)` as a closed subscheme of `ℙ^{n+1}_R` over `Spec R`, and the closed-immersion
cohomology comparison (`AlgebraicGeometry.Scheme.Hom.cohomologyPushforwardBaseLinearEquiv`) and
projection formula (`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pushforwardTensorLeftIso`)
transfer both theorems to `X`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2.
* [The Stacks Project, Tag 01XS and Section 30.14](https://stacks.math.columbia.edu/tag/01Y0).
-/

public section

open CategoryTheory Limits MonoidalCategory BraidedCategory AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

attribute [local instance] Abelian.hasFiniteBiproducts

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Cohomology squeezing and biproduct-tensor compatibility -/

/-- If `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence on a scheme over a Noetherian ring `R`,
then `Hᵠ(X, X₃)` is finitely generated over `R` whenever `Hᵠ(X, X₂)` and `H^{q+1}(X, X₁)` are. -/
private theorem finite_cohomology_X₃ (R : Type u) [CommRing R] [IsNoetherianRing R]
    [X.Over (Spec (.of R))] {S : ShortComplex X.Modules} (hS : S.ShortExact) (q : ℕ)
    [Module.Finite R (Cohomology S.X₂ q)] [Module.Finite R (Cohomology S.X₁ (q + 1))] :
    Module.Finite R (Cohomology S.X₃ q) := by
  have hex : Function.Exact (cohomologyMapBaseLinear R X S.g q)
      (cohomologyδBaseLinear R X hS q (q + 1) rfl).rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, ← LinearMap.exact_iff]
    exact exact_cohomologyMapBaseLinear_cohomologyδBaseLinear R X hS q
  have : _root_.IsNoetherian R (Cohomology S.X₁ (q + 1)) :=
    isNoetherian_of_isNoetherianRing_of_finite R _
  have : Module.Finite R (LinearMap.range (cohomologyδBaseLinear R X hS q (q + 1) rfl)) :=
    Module.Finite.iff_fg.mpr (_root_.IsNoetherian.noetherian _)
  exact Module.Finite.of_exact hex (LinearMap.surjective_rangeRestrict _)

/-- Isomorphic sheaves have isomorphic cohomology, hence vanish in the same degrees. -/
private theorem subsingleton_cohomology_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (hM : Subsingleton (Cohomology M q)) : Subsingleton (Cohomology N q) :=
  @Equiv.subsingleton _ _
    ((cohomologyFunctor X q).mapIso e).addCommGroupIsoToAddEquiv.symm.toEquiv hM

/-- Reindexing a biproduct along an equivalence of index types (possibly across universes). -/
private def biproductReindex {J K : Type*} (e : J ≃ K) (F : K → X.Modules)
    [HasBiproduct F] [HasBiproduct (F ∘ e)] : (⨁ F ∘ e) ≅ ⨁ F where
  hom := biproduct.lift fun k ↦ biproduct.π (F ∘ e) (e.symm k) ≫ eqToHom (by simp)
  inv := biproduct.lift fun j ↦ biproduct.π F (e j)
  hom_inv_id := biproduct.hom_ext _ _ fun j ↦ by simp
  inv_hom_id := biproduct.hom_ext _ _ fun k ↦ by simp

/-- Tensoring on the left distributes over biproducts in `X.Modules`, since `tensorLeft K`
is a left adjoint (`MonoidalClosed X.Modules`). -/
private def tensorLeftBiproductIso (K : X.Modules) {J : Type*} (G : J → X.Modules)
    [HasBiproduct G] [HasBiproduct fun j ↦ K ⊗ G j] :
    (⨁ fun j ↦ K ⊗ G j) ≅ K ⊗ (⨁ G) := by
  let hcolim : IsColimit ((tensorLeft K).mapCocone (biproduct.bicone G).toCocone) :=
    isColimitOfPreserves (tensorLeft K) (biproduct.isColimit G)
  let e : Discrete.functor (fun j ↦ K ⊗ G j) ≅ Discrete.functor G ⋙ tensorLeft K :=
    Discrete.natIso fun _ ↦ Iso.refl _
  exact (biproduct.isColimit fun j ↦ K ⊗ G j).coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv e _).symm hcolim)

/-- A finite constant biproduct `⨁_{Fin k} K` is isomorphic to `K ⊗ free (ULift (Fin k))`. -/
private def biproductConstIsoTensorFree (K : X.Modules) (k : ℕ) :
    (⨁ fun _ : Fin k ↦ K) ≅ K ⊗ _root_.SheafOfModules.free (ULift.{u} (Fin k)) := by
  have h1 : (⨁ fun _ : Fin k ↦ K) ≅ (⨁ fun _ : ULift.{u} (Fin k) ↦ K ⊗ 𝟙_ X.Modules) :=
    biproductReindex (Equiv.ulift.symm : Fin k ≃ ULift.{u} (Fin k)) (fun _ ↦ K) ≪≫
      biproduct.mapIso fun _ ↦ (ρ_ K).symm
  exact h1 ≪≫ tensorLeftBiproductIso K (fun _ : ULift.{u} (Fin k) ↦ 𝟙_ X.Modules) ≪≫
    whiskerLeftIso K (TauCeti.SheafOfModules.biproductIsoFree (R := X.sheaf) (ULift.{u} (Fin k)))

/-- A finite constant biproduct of a finitely presented sheaf is finitely presented. -/
private theorem isFinitePresentation_biproduct_const (K : X.Modules) [K.IsFinitePresentation]
    (k : ℕ) : (⨁ fun _ : Fin k ↦ K).IsFinitePresentation := by
  have : (_root_.SheafOfModules.free (R := X.ringCatSheaf)
      (ULift.{u} (Fin k))).IsFinitePresentation :=
    TauCeti.SheafOfModules.isFinitePresentation_free (ULift.{u} (Fin k))
  have : (K ⊗ _root_.SheafOfModules.free (ULift.{u} (Fin k))).IsFinitePresentation :=
    TauCeti.SheafOfModules.isFinitePresentation_tensorObj
  exact (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (biproductConstIsoTensorFree K k).symm this

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-! ### Finite presentations by negative twisting sheaves -/

/-- Monoidal-notation form of `Proj.twistingSheaf.tensorProductIso`: `𝒪(m) ⊗ 𝒪(n) ≅ 𝒪(m + n)`. -/
private def twistingSheafTensorIso {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] {ι : Type u} (f : ι → A)
    (hf : ∀ i, f i ∈ 𝒜 1) (hcover : ⨆ i, basicOpen 𝒜 (f i) = ⊤) (m n : ℤ) :
    twistingSheaf 𝒜 m ⊗ twistingSheaf 𝒜 n ≅ twistingSheaf 𝒜 (m + n) :=
  _root_.SheafOfModules.tensorUnderlyingIso (twistingSheaf 𝒜 m) (twistingSheaf 𝒜 n) ≪≫
    (TauCeti.SheafOfModules.tensorProductIso (Proj 𝒜).sheaf _ _).symm ≪≫
    twistingSheaf.tensorProductIso f hf hcover m n

/-- Cancelling opposite twisting sheaves in a tensor product: `𝒪(-m) ⊗ (F ⊗ 𝒪(m)) ≅ F`. -/
private def twistingSheafCancelIso {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] {ι : Type u} (f : ι → A)
    (hf : ∀ i, f i ∈ 𝒜 1) (hcover : ⨆ i, basicOpen 𝒜 (f i) = ⊤) (F : (Proj 𝒜).Modules) (m : ℤ) :
    twistingSheaf 𝒜 (-m) ⊗ (F ⊗ twistingSheaf 𝒜 m) ≅ F :=
  (α_ (twistingSheaf 𝒜 (-m)) F (twistingSheaf 𝒜 m)).symm ≪≫
    whiskerRightIso (β_ (twistingSheaf 𝒜 (-m)) F) (twistingSheaf 𝒜 m) ≪≫
    α_ F (twistingSheaf 𝒜 (-m)) (twistingSheaf 𝒜 m) ≪≫
    whiskerLeftIso F (twistingSheafTensorIso f hf hcover (-m) m ≪≫
      eqToIso (congrArg (twistingSheaf 𝒜) (neg_add_cancel m)) ≪≫
      (unitIsoTwistingSheafZero 𝒜).symm) ≪≫
    ρ_ F

/-- **Surjection from a finite direct sum of negative twists on `Proj 𝒜`.** If `Proj 𝒜` is
quasi-compact and covered by degree-one standard opens, then every quasi-coherent
`𝒪_{Proj 𝒜}`-module `F` of finite type admits an epimorphism `⨁_{Fin k} 𝒪(-m) ⟶ F` for all
sufficiently large `m`. No Noetherian hypothesis is required. -/
theorem exists_epi_biproduct_twistingSheaf {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] [CompactSpace (Proj 𝒜)]
    {ι : Type*} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1) (hcover : ⨆ i, basicOpen 𝒜 (f i) = ⊤)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ (k : ℕ)
      (π : (⨁ fun _ : Fin k ↦ twistingSheaf 𝒜 (-(m : ℤ))) ⟶ F), Epi π := by
  let f' : Set.range f → A := Subtype.val
  have hf' : ∀ x : Set.range f, f' x ∈ 𝒜 1 := fun ⟨_, i, hi⟩ ↦ hi ▸ hf i
  have hcover' : ⨆ x : Set.range f, basicOpen 𝒜 (f' x) = ⊤ := by
    simpa [f', iSup_range'] using hcover
  let L : InvertibleSheaf (Proj 𝒜) :=
    ⟨twistingSheaf 𝒜 1, isInvertible_twistingSheaf_of_iSup_eq_top f' hf' hcover' 1⟩
  have hL : (LineBundleClass.mk L).IsAmple := isAmple_twistingSheaf f' hf' hcover' one_pos
  obtain ⟨m₀, hm₀⟩ := Scheme.Modules.exists_generatingSections_tensorPow_of_isAmple F L hL
  refine ⟨m₀, fun m hm ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := hm₀ m hm
  have : Finite σ.I := hσ.finite
  cases nonempty_fintype σ.I
  let k : ℕ := Fintype.card σ.I
  have hpow : Nonempty ((L.tensorPow m).obj ≅ twistingSheaf 𝒜 (m : ℤ)) := by
    have : TauCeti.SheafOfModules.IsInvertible (R := (Proj 𝒜).ringCatSheaf)
        (twistingSheaf 𝒜 (m : ℤ)) :=
      isInvertible_twistingSheaf_of_iSup_eq_top f' hf' hcover' m
    refine (LineBundleClass.mk_eq_mk_iff (L := L.tensorPow m)
      (K := ⟨twistingSheaf 𝒜 (m : ℤ), this⟩)).mp ?_
    rw [LineBundleClass.mk_tensorPow, lineBundleClass_twistingSheaf_eq_zpow f' hf' hcover' (m : ℤ),
      zpow_natCast]
  obtain ⟨ePow⟩ := hpow
  let freeK : (Proj 𝒜).Modules :=
    _root_.SheafOfModules.free (R := (Proj 𝒜).ringCatSheaf) (ULift.{u} (Fin k))
  let freeI : (Proj 𝒜).Modules := _root_.SheafOfModules.free (R := (Proj 𝒜).ringCatSheaf) σ.I
  let eIdx : ULift.{u} (Fin k) ≃ σ.I := Equiv.ulift.trans (Fintype.equivFin σ.I).symm
  let eFree : freeK ≅ freeI :=
    (TauCeti.SheafOfModules.biproductIsoFree (R := (Proj 𝒜).sheaf) (ULift.{u} (Fin k))).symm ≪≫
      Scheme.Modules.biproductReindex eIdx (fun _ : σ.I ↦ 𝟙_ (Proj 𝒜).Modules) ≪≫
      TauCeti.SheafOfModules.biproductIsoFree (R := (Proj 𝒜).sheaf) σ.I
  let σπ : freeI ⟶ F ⊗ (L.tensorPow m).obj := σ.π
  have : Epi σπ := σ.epi
  let π₀ : freeK ⟶ F ⊗ twistingSheaf 𝒜 (m : ℤ) := eFree.hom ≫ σπ ≫ (whiskerLeftIso F ePow).hom
  have : Epi (σπ ≫ (whiskerLeftIso F ePow).hom) := epi_comp σπ (whiskerLeftIso F ePow).hom
  have : Epi π₀ := epi_comp eFree.hom _
  let K : (Proj 𝒜).Modules := twistingSheaf 𝒜 (-(m : ℤ))
  have : Epi ((tensorLeft K).map π₀) := Functor.map_epi (tensorLeft K) π₀
  let π : (⨁ fun _ : Fin k ↦ K) ⟶ F :=
    (Scheme.Modules.biproductConstIsoTensorFree K k).hom ≫ (tensorLeft K).map π₀ ≫
      (twistingSheafCancelIso f' hf' hcover' F (m : ℤ)).hom
  exact ⟨k, π, epi_comp _ _⟩

end AlgebraicGeometry.Proj

namespace TauCeti.SymmetricAlgebra

/-! ### Serre finiteness and vanishing on projective space with a finite basis -/

section Basis

variable {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => homogeneousSubmodule R M

/-- Every quasi-coherent finite-type module `G` on `Proj (Sym_R M)` (over a Noetherian ring `R`
with finite `M`) fits into a short exact sequence `0 → ker π → ⨁_{Fin k} 𝒪(-m₀) → G → 0` whose
kernel is again quasi-coherent and of finite type. -/
private theorem exists_shortExact_biproduct_twistingSheaf [Module.Finite R M]
    (G : (Proj 𝒜).Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ (m₀ k : ℕ) (π : (⨁ fun _ : Fin k ↦ Proj.twistingSheaf 𝒜 (-(m₀ : ℤ))) ⟶ G),
      (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact ∧
        (kernel π).IsQuasicoherent ∧ (kernel π).IsFiniteType := by
  obtain ⟨m₀, hm₀⟩ := Proj.exists_epi_biproduct_twistingSheaf
    (_root_.SymmetricAlgebra.ι R M) (ι_mem_homogeneousSubmodule R M)
    (iSup_basicOpen_ι_eq_top R M id (by simp)) G
  obtain ⟨k, π, hπ⟩ := hm₀ m₀ le_rfl
  let K := Proj.twistingSheaf 𝒜 (-(m₀ : ℤ))
  have : TauCeti.SheafOfModules.IsInvertible (R := (Proj 𝒜).ringCatSheaf) K := inferInstance
  have : K.IsFinitePresentation :=
    TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := K)
  have : (⨁ fun _ : Fin k ↦ K).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_biproduct_const K k
  have : (⨁ fun _ : Fin k ↦ K).IsQuasicoherent := inferInstance
  have : (⨁ fun _ : Fin k ↦ K).IsFiniteType := inferInstance
  have : (kernel π).IsFinitePresentation := Scheme.Modules.isFinitePresentation_kernel π
  exact ⟨m₀, k, π,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
      inferInstance hπ, inferInstance, inferInstance⟩

/-- On `Proj (Sym_R M)` with a finite basis of size `≥ 2` over a Noetherian ring `R`, every
quasi-coherent module of finite type has finitely generated cohomology in every degree. -/
private theorem finite_cohomology_of_basis {κ : Type*} [Finite κ] [Nontrivial κ]
    (b : Module.Basis κ R M) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (q : ℕ) : Module.Finite R (Cohomology F q) := by
  cases nonempty_fintype κ
  have : Module.Finite R M := Module.Finite.of_basis b
  have hrec : ∀ d q : ℕ, Fintype.card κ ≤ q + d →
      ∀ (G : (Proj 𝒜).Modules) [G.IsQuasicoherent] [G.IsFiniteType],
        Module.Finite R (Cohomology G q) := by
    intro d
    induction d with
    | zero =>
      intro q hq G _ _
      have := b.subsingleton_cohomology_proj_of_card_le G q (by simpa using hq)
      infer_instance
    | succ d ih =>
      intro q hq G _ _
      obtain ⟨m₀, k, π, hS, _, _⟩ := exists_shortExact_biproduct_twistingSheaf (R := R) (M := M) G
      have hmid : Module.Finite R (Cohomology (⨁ fun _ : Fin k ↦
          Proj.twistingSheaf 𝒜 (-(m₀ : ℤ))) q) := by
        have := b.finite_cohomology_twistingSheaf (-(m₀ : ℤ)) q
        exact Module.Finite.equiv
          (Scheme.Modules.cohomologyBiproductLinearEquiv R
            (fun _ : Fin k ↦ Proj.twistingSheaf 𝒜 (-(m₀ : ℤ))) q).symm
      have hker : Module.Finite R (Cohomology (kernel π) (q + 1)) :=
        ih (q + 1) (by omega) (kernel π)
      exact Scheme.Modules.finite_cohomology_X₃ R hS q
  exact hrec (Fintype.card κ) q (by omega) F

/-- Descending-induction step for Serre vanishing in a fixed positive degree `q`. -/
private theorem exists_subsingleton_cohomology_tensor_twistingSheaf_of_basis_deg {κ : Type*}
    [Fintype κ] [Nonempty κ] (b : Module.Basis κ R M) (d q : ℕ) (hqpos : 0 < q)
    (hq : Fintype.card κ ≤ q + d) (G : (Proj 𝒜).Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, Subsingleton (Cohomology (G ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  have : Module.Finite R M := Module.Finite.of_basis b
  induction d generalizing q G with
  | zero =>
    refine ⟨0, fun m _ ↦ b.subsingleton_cohomology_proj_of_card_le
      (G ⊗ Proj.twistingSheaf 𝒜 m) q (by simpa using hq)⟩
  | succ d ih =>
    obtain ⟨n₀, k, π, hS, _, _⟩ := exists_shortExact_biproduct_twistingSheaf (R := R) (M := M) G
    obtain ⟨m₁, hm₁⟩ := ih (q + 1) (Nat.succ_pos q) (by omega) (kernel π)
    refine ⟨max m₁ (n₀ : ℤ), fun m hm ↦ ?_⟩
    let K := Proj.twistingSheaf 𝒜 (-(n₀ : ℤ))
    let L := Proj.twistingSheaf 𝒜 m
    have : TauCeti.SheafOfModules.IsInvertible (R := (Proj 𝒜).ringCatSheaf) L := inferInstance
    have : L.IsLocallyFree := TauCeti.SheafOfModules.IsInvertible.isLocallyFree L
    have : L.IsFinitePresentation :=
      TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := L)
    have : L.IsFiniteType := inferInstance
    have hSm := Scheme.Modules.shortExact_map_tensorLeft L hS
    have hker : Subsingleton (Cohomology (L ⊗ kernel π) (q + 1)) :=
      Scheme.Modules.subsingleton_cohomology_of_iso (β_ (kernel π) L) (q + 1)
        (hm₁ m ((le_max_left m₁ (n₀ : ℤ)).trans hm))
    have hmid : Subsingleton (Cohomology (L ⊗ ⨁ fun _ : Fin k ↦ K) q) := by
      let eTwist : L ⊗ K ≅ Proj.twistingSheaf 𝒜 (m + -(n₀ : ℤ)) :=
        Proj.twistingSheafTensorIso (_root_.SymmetricAlgebra.ι R M)
          (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) m (-(n₀ : ℤ))
      let eSum : (⨁ fun _ : Fin k ↦ Proj.twistingSheaf 𝒜 (m + -(n₀ : ℤ))) ≅
          L ⊗ ⨁ fun _ : Fin k ↦ K :=
        biproduct.mapIso (fun _ ↦ eTwist.symm) ≪≫
          Scheme.Modules.tensorLeftBiproductIso L (fun _ : Fin k ↦ K)
      have hpos : -(Fintype.card κ : ℤ) < m + -(n₀ : ℤ) := by
        have hc : (0 : ℤ) < (Fintype.card κ : ℤ) := Nat.cast_pos.mpr Fintype.card_pos
        have hm' : (n₀ : ℤ) ≤ m := (le_max_right m₁ (n₀ : ℤ)).trans hm
        omega
      have := b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt hpos hqpos
      exact Scheme.Modules.subsingleton_cohomology_of_iso eSum q
        (Scheme.Modules.cohomologyBiproductLinearEquiv R
          (fun _ : Fin k ↦ Proj.twistingSheaf 𝒜 (m + -(n₀ : ℤ))) q).toEquiv.subsingleton
    exact Scheme.Modules.subsingleton_cohomology_of_iso (β_ L G) q
      (Scheme.Modules.subsingleton_cohomology_X₃ hSm q (q + 1) rfl hmid hker)

/-- On `Proj (Sym_R M)` with a nonempty finite basis over a Noetherian ring `R`, the cohomology
`Hᵠ(Proj (Sym_R M), F ⊗ 𝒪(m))` vanishes for all sufficiently large `m` and all `q > 0`. -/
private theorem exists_subsingleton_cohomology_tensor_twistingSheaf_of_basis {κ : Type*} [Finite κ]
    [Nonempty κ] (b : Module.Basis κ R M) (F : (Proj 𝒜).Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, 0 < q →
      Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  cases nonempty_fintype κ
  have hfin (q : Fin (Fintype.card κ)) :
      ∃ m₀ : ℤ, ∀ m ≥ m₀, 0 < q.1 →
        Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf 𝒜 m) q.1) := by
    by_cases hq : 0 < q.1
    · obtain ⟨m₀, hm₀⟩ := exists_subsingleton_cohomology_tensor_twistingSheaf_of_basis_deg
        b (Fintype.card κ) q.1 hq (by omega) F
      exact ⟨m₀, fun m hm _ ↦ hm₀ m hm⟩
    · exact ⟨0, fun _ _ hq' ↦ (hq hq').elim⟩
  choose bound hbound using hfin
  let m₀ : ℤ := Finset.univ.sup' ⟨⟨0, Fintype.card_pos⟩, Finset.mem_univ _⟩ bound
  refine ⟨m₀, fun m hm q hqpos ↦ ?_⟩
  by_cases hq : q < Fintype.card κ
  · exact hbound ⟨q, hq⟩ m
      ((Finset.le_sup' bound (Finset.mem_univ ⟨q, hq⟩)).trans hm) hqpos
  · exact b.subsingleton_cohomology_proj_of_card_le
      (F ⊗ Proj.twistingSheaf 𝒜 m) q (Nat.le_of_not_lt hq)

end Basis

/-! ### Closed embedding of `Proj (Sym_R M)` into `ℙ^{n+1}_R` -/

/-- Every finite `R`-module `M` admits a surjective `R`-linear map from a free module of finite
rank `n + 2 ≥ 2`. -/
private theorem exists_surjective_fin_add_two (R M : Type u) [CommRing R] [AddCommMonoid M]
    [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ) (φ : (ULift.{u} (Fin (n + 2)) → R) →ₗ[R] M), Function.Surjective φ := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let w : ULift.{u} (Fin (n + 2)) → M := fun i ↦
    if h : i.down.1 < n then v ⟨i.down.1, h⟩ else 0
  let φ : (ULift.{u} (Fin (n + 2)) → R) →ₗ[R] M :=
    Fintype.linearCombination R w
  refine ⟨n, φ, ?_⟩
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hv]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  refine ⟨ULift.up ⟨j.1, by omega⟩, ?_⟩
  simp [w, j.2]

/-- A surjective `R`-linear map `φ : N →ₗ[R] M` induces a surjective graded ring homomorphism
`Sym_R N →+*ᵍ Sym_R M`, hence a closed immersion `Proj (Sym_R M) ⟶ Proj (Sym_R N)` over `Spec R`. -/
private theorem exists_isClosedImmersion_proj_fin (R M : Type u) [CommRing R] [AddCommMonoid M]
    [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ) (g : homogeneousSubmodule R (ULift.{u} (Fin (n + 2)) → R) →+*ᵍ
        homogeneousSubmodule R M)
      (hg : HomogeneousIdeal.irrelevant (homogeneousSubmodule R M) ≤
        (HomogeneousIdeal.irrelevant
          (homogeneousSubmodule R (ULift.{u} (Fin (n + 2)) → R))).map g),
      IsClosedImmersion (Proj.map g hg) ∧ (Proj.map g hg).IsOver (Spec (.of R)) := by
  obtain ⟨n, φ, hφ⟩ := exists_surjective_fin_add_two R M
  let g := _root_.SymmetricAlgebra.gradedMap R φ
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := _root_.SymmetricAlgebra.map_surjective R φ hφ y
    exact ⟨x, (_root_.SymmetricAlgebra.gradedMap_apply R φ x).trans hx⟩
  have hg := HomogeneousIdeal.irrelevant_le_map_of_surjective g hsurj
  have hcl : IsClosedImmersion (Proj.map g hg) := Proj.isClosedImmersion_map g hg hsurj
  have hover : (Proj.map g hg).IsOver (Spec (.of R)) := by
    refine ⟨?_⟩
    rw [over_eq_projToSpec, over_eq_projToSpec, projToSpec_def, projToSpec_def,
      Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [g, GradedRingHom.gradedZeroRingHom_apply_coe, _root_.SymmetricAlgebra.gradedMap_apply]
  exact ⟨n, g, hg, hcl, hover⟩

/-- Transferring cohomology vanishing along a closed immersion `i : X ⟶ Y` using the projection
formula for an invertible sheaf `L` on `Y` whose pullback is isomorphic to `L'`. -/
private theorem subsingleton_cohomology_tensor_of_pushforward {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (F : X.Modules) (L : Y.Modules)
    [TauCeti.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) L] {L' : X.Modules}
    (eL : (Scheme.Modules.pullback i).obj L ≅ L') (q : ℕ)
    (h : Subsingleton (Cohomology ((Scheme.Modules.pushforward i).obj F ⊗ L) q)) :
    Subsingleton (Cohomology (F ⊗ L') q) := by
  let E : FiniteLocallyFreeSheaf Y :=
    ⟨L, ⟨TauCeti.SheafOfModules.IsInvertible.isLocallyFree L,
      TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := L)⟩⟩
  let ePull : ((FiniteLocallyFreeSheaf.pullback i).obj E).obj ≅ L' :=
    eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj i E) ≪≫ eL
  let eProj : (Scheme.Modules.pushforward i).obj F ⊗ E.obj ≅
      (Scheme.Modules.pushforward i).obj (F ⊗ L') :=
    β_ ((Scheme.Modules.pushforward i).obj F) E.obj ≪≫
      (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso i E).app F ≪≫
      (Scheme.Modules.pushforward i).mapIso (whiskerRightIso ePull F ≪≫ β_ L' F)
  exact @Equiv.subsingleton _ _
    (cohomologyPushforwardIso i (F ⊗ L') q).addCommGroupIsoToAddEquiv.symm.toEquiv
    (Scheme.Modules.subsingleton_cohomology_of_iso eProj q h)

/-! ### Serre's Theorem B for `Proj (Sym_R M)` -/

/-- **Serre's finiteness theorem on `Proj (Sym_R M)`.** Let `R` be a Noetherian ring and `M` any
finite `R`-module (not necessarily free). For every quasi-coherent `𝒪_{Proj (Sym_R M)}`-module
`F` of finite type and every `q : ℕ`, the cohomology group `Hᵠ(Proj (Sym_R M), F)` is a finitely
generated `R`-module. -/
theorem finite_cohomology_proj {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommMonoid M] [Module R M] [Module.Finite R M]
    (F : (Proj (homogeneousSubmodule R M)).Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨n, g, hg, hcl, hover⟩ := exists_isClosedImmersion_proj_fin R M
  let i := Proj.map g hg
  have : IsClosedImmersion i := hcl
  have : i.IsOver (Spec (.of R)) := hover
  let N := ULift.{u} (Fin (n + 2)) → R
  let b : Module.Basis (ULift.{u} (Fin (n + 2))) R N := Pi.basisFun R (ULift.{u} (Fin (n + 2)))
  have : ((Scheme.Modules.pushforward i).obj F).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pushforward_of_isFinite i F
  have : ((Scheme.Modules.pushforward i).obj F).IsQuasicoherent := inferInstance
  have : ((Scheme.Modules.pushforward i).obj F).IsFiniteType := inferInstance
  have := finite_cohomology_of_basis b ((Scheme.Modules.pushforward i).obj F) q
  exact (i.moduleFinite_cohomology_pushforward_iff R F q).mp this

/-- **Serre's vanishing theorem on `Proj (Sym_R M)`.** Let `R` be a Noetherian ring and `M` any
finite `R`-module (not necessarily free). For every quasi-coherent `𝒪_{Proj (Sym_R M)}`-module
`F` of finite type, there exists `m₀ : ℤ` such that `Hᵠ(Proj (Sym_R M), F ⊗ 𝒪(m)) = 0` for all
`m ≥ m₀` and all `q > 0`. -/
theorem exists_subsingleton_cohomology_tensor_twistingSheaf {R M : Type u} [CommRing R]
    [IsNoetherianRing R] [AddCommMonoid M] [Module R M] [Module.Finite R M]
    (F : (Proj (homogeneousSubmodule R M)).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, 0 < q →
      Subsingleton (Cohomology (F ⊗ Proj.twistingSheaf (homogeneousSubmodule R M) m) q) := by
  obtain ⟨n, g, hg, hcl, _⟩ := exists_isClosedImmersion_proj_fin R M
  let j := Proj.map g hg
  have : IsClosedImmersion j := hcl
  let N := ULift.{u} (Fin (n + 2)) → R
  let b : Module.Basis (ULift.{u} (Fin (n + 2))) R N := Pi.basisFun R (ULift.{u} (Fin (n + 2)))
  have : ((Scheme.Modules.pushforward j).obj F).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pushforward_of_isFinite j F
  have : ((Scheme.Modules.pushforward j).obj F).IsQuasicoherent := inferInstance
  have : ((Scheme.Modules.pushforward j).obj F).IsFiniteType := inferInstance
  obtain ⟨m₀, hm₀⟩ := exists_subsingleton_cohomology_tensor_twistingSheaf_of_basis b
    ((Scheme.Modules.pushforward j).obj F)
  exact ⟨m₀, fun m hm q hq ↦
    subsingleton_cohomology_tensor_of_pushforward j F
      (Proj.twistingSheaf (homogeneousSubmodule R N) m)
      (asIso (Proj.pullbackTwistingSheafMap g hg m)) q (hm₀ m hm q hq)⟩

end TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

/-! ### Serre's Theorem B for projective schemes over a Noetherian ring -/

/-- **Serre's finiteness theorem for projective schemes.** Let `R` be a Noetherian ring and `X` a
projective scheme over `Spec R`. For every quasi-coherent `𝒪_X`-module `F` of finite type and
every `q : ℕ`, the cohomology group `Hᵠ(X, F)` is a finitely generated `R`-module. -/
theorem IsProjectiveOver.finite_cohomology (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨M, _, _, _, i, hi, hiR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  have : ((Scheme.Modules.pushforward i).obj F).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pushforward_of_isFinite i F
  have : ((Scheme.Modules.pushforward i).obj F).IsQuasicoherent := inferInstance
  have : ((Scheme.Modules.pushforward i).obj F).IsFiniteType := inferInstance
  have := TauCeti.SymmetricAlgebra.finite_cohomology_proj ((Scheme.Modules.pushforward i).obj F) q
  exact (i.moduleFinite_cohomology_pushforward_iff R F q).mp this

/-- **Serre's vanishing theorem for closed subschemes of `Proj (Sym_R M)`.** Let `R` be a
Noetherian ring, `M` a finite `R`-module, and `i : X ⟶ Proj (Sym_R M)` a closed immersion. For
every quasi-coherent `𝒪_X`-module `F` of finite type, there exists `m₀ : ℤ` such that
`Hᵠ(X, F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀` and all `q > 0`. -/
theorem Modules.exists_subsingleton_cohomology_tensor_pullback_twistingSheaf
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] {X : Scheme.{u}}
    (i : X ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, 0 < q →
      Subsingleton (Cohomology
        (F ⊗ (Scheme.Modules.pullback i).obj
          (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m)) q) := by
  have : ((Scheme.Modules.pushforward i).obj F).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pushforward_of_isFinite i F
  have : ((Scheme.Modules.pushforward i).obj F).IsQuasicoherent := inferInstance
  have : ((Scheme.Modules.pushforward i).obj F).IsFiniteType := inferInstance
  obtain ⟨m₀, hm₀⟩ :=
    TauCeti.SymmetricAlgebra.exists_subsingleton_cohomology_tensor_twistingSheaf
      ((Scheme.Modules.pushforward i).obj F)
  exact ⟨m₀, fun m hm q hq ↦
    TauCeti.SymmetricAlgebra.subsingleton_cohomology_tensor_of_pushforward i F
      (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m)
      (Iso.refl _) q (hm₀ m hm q hq)⟩

end AlgebraicGeometry.Scheme
