/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.FormallyEtale
public import TauCeti.RingTheory.Kaehler.MapSemilinear
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Basic

/-!
# Continuous one-forms of étale extensions of Laurent series

Let `K` be a field, `F = K⸨t⸩` and `L` a formally étale `F`-algebra, for instance a finite
separable field extension of `F` (`Algebra.FormallyEtale.of_isSeparable`). The formal derivative
`D = d/dt` of `F` extends uniquely to a `K`-derivation `D_L` of `L`
(`TauCeti.LaurentSeries.Extension.derivation`), by the extension of derivations along formally
étale maps (`Derivation.extendOfFormallyEtale`).

The continuous one-forms `Ω¹_cont(L/K)` are built from `D_L` exactly as `Ω¹_cont(F/K)` is built
from `D` (`TauCeti.ContinuousKaehlerDifferential`): they are the quotient of the algebraic Kähler
differentials `Ω[L⁄K]` by the kernel of the `L`-linear map `λ_L : Ω[L⁄K] → L`, `x dy ↦ x * D_L y`,
induced by `D_L`. This file shows:

* `λ_L` induces an `L`-linear equivalence `Ω¹_cont(L/K) ≃ L` sending `dt` to `1`, so every
  continuous one-form on `L` is uniquely `x dt`, and `dy = D_L y dt`.
* The pullback `Ω¹_cont(F/K) → Ω¹_cont(L/K)`, `f dg ↦ f dg`, is induced by the map
  `Ω[F⁄K] → Ω[L⁄K]` of Kähler differentials, and it extends to an `L`-linear equivalence
  `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`, `x ⊗ ω ↦ x ω`.
* `d : L → Ω¹_cont(L/K)` is the universal derivation among `K`-derivations of `L` whose restriction
  to `F` is continuous for the valuation topology: for an `L`-module `M` with a Hausdorff topology
  for which scalar multiplication by `F` is continuous, a `K`-derivation `δ : L → M` factors as
  `ℓ ∘ d` with `ℓ` an `L`-linear map exactly when `δ` is continuous on `F`, and then `ℓ` is unique.
  This characterization does not use a topology on `L`.
* Continuous one-forms are functorial along `F`-algebra homomorphisms `φ : M →ₐ[F] L` via a
  `φ`-semilinear pullback (`Extension.ContinuousKaehlerDifferential.pullback`) compatible with `d`
  and `KaehlerDifferential.mapSemilinear`, and in towers `F → M → L` the relative pullback extends
  to `L ⊗_M Ω¹_cont(M/K) ≃ Ω¹_cont(L/K)` (`tensorEquivTower`).

## Main definitions

* `TauCeti.LaurentSeries.Extension.derivation K L`: the derivation `D_L = d/dt` of `L`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential K L`: the continuous one-forms
  `Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.D K L`: the universal derivation `d`.
* `Extension.ContinuousKaehlerDifferential.equivSelf K L`: the `L`-linear equivalence
  `Ω¹_cont(L/K) ≃ L` sending `d t` to `1`.
* `Extension.ContinuousKaehlerDifferential.map K L`: the pullback `Ω¹_cont(F/K) → Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.tensorEquiv K L`: the `L`-linear equivalence
  `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.lift`: the factorization of a derivation that is
  continuous on `F` through `d`.
* `Extension.ContinuousKaehlerDifferential.pullback` and `pullbackEquiv`: semilinear functoriality
  along `F`-algebra maps and equivalences.
* `Extension.ContinuousKaehlerDifferential.mapTower` and `tensorEquivTower`: relative pullback and
  scalar-extension equivalence in towers `F → M → L`.

## Main results

* `TauCeti.LaurentSeries.Extension.derivation_algebraMap`: `D_L` extends `D`.
* `TauCeti.LaurentSeries.Extension.eq_derivation`: `D_L` is the only derivation of `L` extending
  `D`.
* `TauCeti.LaurentSeries.Extension.derivation_algHom_apply`: `F`-algebra maps intertwine `D_M` and
  `D_L`.
* `Extension.ContinuousKaehlerDifferential.map_mk`: the pullback is induced by the map of Kähler
  differentials.
* `Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul`: the equivalence sends `x ⊗ ω` to
  `x` times the pullback of `ω`.
* `Extension.ContinuousKaehlerDifferential.existsUnique_compDer_eq`: a derivation continuous on
  `F` factors uniquely through `d`.
* `Extension.ContinuousKaehlerDifferential.exists_compDer_eq_iff`: a derivation factors through `d`
  if and only if it is continuous on `F`.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), for the continuous
  differentials of a finite separable extension of a complete discretely valued field.
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Extension

variable (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-! ### The derivation `d/dt` of an étale extension -/

/-- The derivation `D_L = d/dt` of a formally étale `K⸨X⸩`-algebra `L`: the unique extension of the
formal derivative of `K⸨X⸩` (`TauCeti.LaurentSeries.Extension.eq_derivation`). -/
noncomputable def derivation : Derivation K L L :=
  ((Algebra.linearMap K⸨X⸩ L).compDer (laurentSeriesDerivation K)).extendOfFormallyEtale L

variable {K L}

/-- The derivation `D_L` extends the formal derivative of `K⸨X⸩`. -/
@[simp]
theorem derivation_algebraMap (f : K⸨X⸩) :
    derivation K L (algebraMap K⸨X⸩ L f) =
      algebraMap K⸨X⸩ L (laurentSeriesDerivation K f) := by
  simp [derivation]

/-- `D_L t = 1`. -/
theorem derivation_algebraMap_single_one :
    derivation K L (algebraMap K⸨X⸩ L (single 1 1)) = 1 := by
  simp

/-- **Uniqueness of `d/dt`.** The derivation `D_L` is the only `K`-derivation of `L` extending the
formal derivative of `K⸨X⸩`. -/
theorem eq_derivation {δ : Derivation K L L}
    (h : ∀ f : K⸨X⸩, δ (algebraMap K⸨X⸩ L f) = algebraMap K⸨X⸩ L (laurentSeriesDerivation K f)) :
    δ = derivation K L :=
  Derivation.eq_extendOfFormallyEtale _ h

variable (K L) in
/-- The map `x dy ↦ x * D_L y` from the Kähler differentials is surjective: `x dt ↦ x`. -/
theorem derivation_liftKaehlerDifferential_surjective :
    Function.Surjective (derivation K L).liftKaehlerDifferential :=
  fun x ↦ ⟨x • KaehlerDifferential.D K L (algebraMap K⸨X⸩ L (single 1 1)), by
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, derivation_algebraMap_single_one,
      smul_eq_mul, mul_one]⟩

/-! ### Continuous one-forms -/

variable (K L) in
/-- The **continuous one-forms** `Ω¹_cont(L/K)` of a formally étale `K⸨X⸩`-algebra `L`: the
quotient of the Kähler differentials `Ω[L⁄K]` by the kernel of the `L`-linear map
`x dy ↦ x * D_L y` induced by the derivation `D_L = d/dt` of `L`. -/
def ContinuousKaehlerDifferential : Type _ :=
  Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

namespace ContinuousKaehlerDifferential

noncomputable instance : AddCommGroup (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| AddCommGroup <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

noncomputable instance (priority := 900) {R : Type*} [CommRing R] [Algebra R L] :
    Module R (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| Module R <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

instance {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] [Algebra R₁ L] [Algebra R₂ L]
    [SMul R₁ R₂] [IsScalarTower R₁ R₂ L] :
    IsScalarTower R₁ R₂ (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| IsScalarTower R₁ R₂ <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

variable (K L)

/-- The quotient map from the Kähler differentials to the continuous one-forms. -/
noncomputable def mk : Ω[L⁄K] →ₗ[L] ContinuousKaehlerDifferential K L :=
  Submodule.mkQ _

theorem mk_surjective : Function.Surjective (mk K L) :=
  Submodule.mkQ_surjective _

variable {K L} in
/-- A Kähler differential vanishes in `Ω¹_cont(L/K)` exactly when its image `Σ xᵢ * D_L yᵢ` under
the map induced by `D_L` vanishes. -/
theorem mk_eq_zero_iff {ω : Ω[L⁄K]} :
    mk K L ω = 0 ↔ (derivation K L).liftKaehlerDifferential ω = 0 :=
  Submodule.Quotient.mk_eq_zero _

/-- The universal derivation `d : L → Ω¹_cont(L/K)`. -/
noncomputable def D : Derivation K L (ContinuousKaehlerDifferential K L) :=
  (mk K L).compDer (KaehlerDifferential.D K L)

theorem D_apply (x : L) : D K L x = mk K L (KaehlerDifferential.D K L x) :=
  (rfl)

/-- **Continuous one-forms are multiples of `dt`.** The `L`-linear equivalence
`Ω¹_cont(L/K) ≃ L` induced by `D_L`, sending `x dy` to `x * D_L y` and `d t` to `1`. -/
noncomputable def equivSelf : ContinuousKaehlerDifferential K L ≃ₗ[L] L :=
  (derivation K L).liftKaehlerDifferential.quotKerEquivOfSurjective
    (derivation_liftKaehlerDifferential_surjective K L)

variable {K L}

@[simp]
theorem equivSelf_mk (ω : Ω[L⁄K]) :
    equivSelf K L (mk K L ω) = (derivation K L).liftKaehlerDifferential ω :=
  (rfl)

/-- The equivalence sends `d y` to `D_L y`. -/
@[simp]
theorem equivSelf_D (x : L) : equivSelf K L (D K L x) = derivation K L x := by
  simp [D_apply]

/-- The continuous one-form corresponding to `x` is `x dt`. -/
@[simp]
theorem equivSelf_symm_apply (x : L) :
    (equivSelf K L).symm x = x • D K L (algebraMap K⸨X⸩ L (single 1 1)) := by
  rw [LinearEquiv.symm_apply_eq, map_smul, equivSelf_D, derivation_algebraMap_single_one,
    smul_eq_mul, mul_one]

/-- Every continuous one-form is `x dt` for the unique `x = equivSelf K L ω`. -/
theorem equivSelf_smul_D_algebraMap_single_one (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K L ω • D K L (algebraMap K⸨X⸩ L (single 1 1)) = ω := by
  rw [← equivSelf_symm_apply, LinearEquiv.symm_apply_apply]

/-- **`dy = D_L y dt`.** -/
theorem derivation_smul_D_algebraMap_single_one (x : L) :
    derivation K L x • D K L (algebraMap K⸨X⸩ L (single 1 1)) = D K L x := by
  rw [← equivSelf_D, equivSelf_smul_D_algebraMap_single_one]

variable (K L) in
/-- `Ω¹_cont(L/K)` is free of rank one over `L`. -/
theorem finrank_eq_one [Nontrivial L] : Module.finrank L (ContinuousKaehlerDifferential K L) = 1 :=
  (equivSelf K L).finrank_eq.trans (Module.finrank_self L)

/-- Semilinear maps out of `Ω¹_cont(L/K)` agree as soon as they agree on `d t`. -/
@[ext]
theorem hom_ext {S N : Type*} [Semiring S] [AddCommMonoid N] [Module S N] {σ : L →+* S}
    {ℓ ℓ' : ContinuousKaehlerDifferential K L →ₛₗ[σ] N}
    (h : ℓ (D K L (algebraMap K⸨X⸩ L (single 1 1))) = ℓ' (D K L (algebraMap K⸨X⸩ L (single 1 1)))) :
    ℓ = ℓ' := by
  ext ω
  rw [← equivSelf_smul_D_algebraMap_single_one ω, map_smulₛₗ, map_smulₛₗ, h]

/-! ### Comparison with the one-forms of `K⸨X⸩` -/

variable (K L) in
/-- The **pullback of one-forms** `Ω¹_cont(K⸨X⸩/K) → Ω¹_cont(L/K)`, `f dg ↦ f dg`, read through
the rank-one normal forms: it sends `f dt` to `f dt`. It is induced by the map of Kähler
differentials (`TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.map_mk`). -/
noncomputable def map :
    TauCeti.ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K L :=
  (equivSelf K L).symm.toLinearMap.restrictScalars K⸨X⸩ ∘ₗ Algebra.linearMap K⸨X⸩ L ∘ₗ
    (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toLinearMap

/-- The pullback sends `f dt` to `f dt`. -/
@[simp]
theorem equivSelf_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivSelf K L (map K L ω) =
      algebraMap K⸨X⸩ L (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω) := by
  simp [map, -equivSelf_symm_apply]

/-- The pullback sends `d g` to `d g`. -/
@[simp]
theorem map_D (g : K⸨X⸩) :
    map K L (TauCeti.ContinuousKaehlerDifferential.D K g) = D K L (algebraMap K⸨X⸩ L g) :=
  (equivSelf K L).injective <| by
    rw [equivSelf_map, equivSelf_D, derivation_algebraMap,
      TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D, laurentSeriesDerivation_apply]

/-- The pullback of one-forms is induced by the map `Ω[K⸨X⸩⁄K] → Ω[L⁄K]` of Kähler
differentials. -/
theorem map_mk (ω : Ω[K⸨X⸩⁄K]) :
    map K L (TauCeti.ContinuousKaehlerDifferential.mk K ω) =
      mk K L (KaehlerDifferential.map K K K⸨X⸩ L ω) := by
  have h : map K L ∘ₗ TauCeti.ContinuousKaehlerDifferential.mk K =
      (mk K L).restrictScalars K⸨X⸩ ∘ₗ KaehlerDifferential.map K K K⸨X⸩ L :=
    Derivation.liftKaehlerDifferential_unique _ _ <| Derivation.ext fun g ↦ by
      simpa [← TauCeti.ContinuousKaehlerDifferential.D_apply] using D_apply K L _
  exact congr($h ω)

/-- The pullback of one-forms is injective. -/
theorem map_injective [FaithfulSMul K⸨X⸩ L] : Function.Injective (map K L) := by
  intro ω η h
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  simpa using congr(equivSelf K L $h)

variable (K L) in
/-- **`Ω¹_cont(L/K) = L ⊗_F Ω¹_cont(F/K)`.** For a formally étale `F`-algebra `L`, `F = K⸨X⸩`, the
pullback of one-forms extends to an `L`-linear equivalence
`L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`, `x ⊗ ω ↦ x ω`
(`TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul`). -/
noncomputable def tensorEquiv :
    L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K ≃ₗ[L] ContinuousKaehlerDifferential K L :=
  LinearEquiv.baseChange K⸨X⸩ L _ _
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toLinearEquiv ≪≫ₗ
    AlgebraTensorModule.rid K⸨X⸩ L L ≪≫ₗ (equivSelf K L).symm

/-- The equivalence `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` sends `x ⊗ ω` to `x` times the pullback
of `ω`. -/
@[simp]
theorem tensorEquiv_tmul (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    tensorEquiv K L (x ⊗ₜ ω) = x • map K L ω := by
  apply (equivSelf K L).injective
  simp [tensorEquiv, LinearEquiv.baseChange, Algebra.smul_def, mul_comm]

/-! ### The universal property -/

variable {M : Type*} [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
  [Module K⸨X⸩ M] [IsScalarTower K⸨X⸩ L M] [IsScalarTower K K⸨X⸩ M] [TopologicalSpace M]
  [ContinuousSMul K⸨X⸩ M]

/-- Every derivation factoring through `d` is continuous on `K⸨X⸩` when scalar multiplication by
`K⸨X⸩` on its target is continuous. -/
theorem continuous_compAlgebraMap_compDer (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M) :
    Continuous ((ℓ.compDer (D K L)).compAlgebraMap K⸨X⸩) := by
  have h : (ℓ.compDer (D K L)).compAlgebraMap K⸨X⸩ =
      (ℓ.restrictScalars K⸨X⸩ ∘ₗ map K L).compDer (TauCeti.ContinuousKaehlerDifferential.D K) :=
    Derivation.ext fun g ↦ by simp
  rw [h]
  exact TauCeti.ContinuousKaehlerDifferential.continuous_compDer _

section Hausdorff

variable [T2Space M]

/-- A `K`-derivation `δ : L → M` into a Hausdorff module that is continuous on `K⸨X⸩` satisfies
`δ y = D_L y • δ t`. -/
theorem apply_eq_derivation_smul (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩))
    (x : L) : δ x = derivation K L x • δ (algebraMap K⸨X⸩ L (single 1 1)) := by
  have h : δ = (LinearMap.toSpanSingleton L M (δ (algebraMap K⸨X⸩ L (single 1 1)))).compDer
      (derivation K L) := Derivation.eq_of_formallyUnramified (S := K⸨X⸩) fun f ↦ by
    rw [Derivation.coe_comp, LinearMap.comp_apply, Derivation.coeFn_coe, derivation_algebraMap,
      LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply, algebraMap_smul]
    exact (δ.compAlgebraMap K⸨X⸩).apply_eq_laurentSeriesDerivation_smul hδ f
  exact congr($h x)

/-- For a derivation `δ` continuous on `K⸨X⸩`, the map `Ω[L⁄K] → M` it induces is `λ_L` followed
by `x ↦ x • δ t`, where `λ_L` is the map induced by `D_L`. -/
theorem liftKaehlerDifferential_eq_toSpanSingleton_comp (δ : Derivation K L M)
    (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    δ.liftKaehlerDifferential = LinearMap.toSpanSingleton L M
      (δ (algebraMap K⸨X⸩ L (single 1 1))) ∘ₗ (derivation K L).liftKaehlerDifferential := by
  ext x
  simp [apply_eq_derivation_smul δ hδ x]

/-- **The factorization of a derivation through `d`.** A `K`-derivation `δ : L → M` that is
continuous on `K⸨X⸩` factors through `Ω¹_cont(L/K)`, by the `L`-linear map induced by its Kähler
lift. -/
noncomputable def lift (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    ContinuousKaehlerDifferential K L →ₗ[L] M :=
  Submodule.liftQ _ δ.liftKaehlerDifferential fun ω hω ↦ by
    rw [LinearMap.mem_ker, liftKaehlerDifferential_eq_toSpanSingleton_comp δ hδ,
      LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero]

@[simp]
theorem lift_mk (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) (ω : Ω[L⁄K]) :
    lift δ hδ (mk K L ω) = δ.liftKaehlerDifferential ω :=
  (rfl)

@[simp]
theorem lift_D (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) (x : L) :
    lift δ hδ (D K L x) = δ x := by
  simp [D_apply]

/-- The factorization of `δ` through `d` recovers `δ`. -/
theorem compDer_lift (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    (lift δ hδ).compDer (D K L) = δ :=
  Derivation.ext (lift_D δ hδ)

/-- The factorization of `δ` through `d` is unique. -/
theorem lift_unique (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩))
    (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M) (h : ℓ.compDer (D K L) = δ) :
    ℓ = lift δ hδ :=
  hom_ext <| by rw [lift_D, ← h]; simp

/-- **Universal property of the continuous one-forms.** Every `K`-derivation of `L` into a
Hausdorff module that is continuous on `K⸨X⸩` factors uniquely through `d` by an `L`-linear
map. -/
theorem existsUnique_compDer_eq (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    ∃! ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M, ℓ.compDer (D K L) = δ :=
  ⟨lift δ hδ, compDer_lift δ hδ, fun ℓ h ↦ lift_unique δ hδ ℓ h⟩

/-- A `K`-derivation of `L` into a Hausdorff module factors through `d` if and only if it is
continuous on `K⸨X⸩`. -/
theorem exists_compDer_eq_iff (δ : Derivation K L M) :
    (∃ ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M, ℓ.compDer (D K L) = δ) ↔
      Continuous (δ.compAlgebraMap K⸨X⸩) :=
  ⟨fun ⟨ℓ, h⟩ ↦ h ▸ continuous_compAlgebraMap_compDer ℓ, fun hδ ↦ ⟨lift δ hδ, compDer_lift δ hδ⟩⟩

end Hausdorff

end ContinuousKaehlerDifferential

/-! ### Functoriality and towers of étale extensions -/

/-- Every `K⸨X⸩`-algebra homomorphism between formally étale `K⸨X⸩`-algebras intertwines `d/dt`. -/
@[simp]
theorem derivation_algHom_apply {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] (φ : M →ₐ[K⸨X⸩] L) (x : M) :
    derivation K L (φ x) = φ (derivation K M x) :=
  Derivation.algHom_apply_eq_of_formallyUnramified (S := K⸨X⸩) (φ.restrictScalars K)
    (fun f ↦ by
      rw [AlgHom.coe_restrictScalars', φ.commutes, derivation_algebraMap, derivation_algebraMap,
        φ.commutes]) x

namespace ContinuousKaehlerDifferential

section Pullback

variable {M N : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
  [Algebra.FormallyEtale K⸨X⸩ M] [CommRing N] [Algebra K⸨X⸩ N] [Algebra K N]
  [IsScalarTower K K⸨X⸩ N] [Algebra.FormallyEtale K⸨X⸩ N]

/-- **Semilinear pullback of continuous one-forms** along a `K⸨X⸩`-algebra homomorphism
`φ : M →ₐ[K⸨X⸩] L`, sending `x dt` to `φ x dt` and `d x` to `d (φ x)`. -/
noncomputable def pullback (φ : M →ₐ[K⸨X⸩] L) :
    ContinuousKaehlerDifferential K M →ₛₗ[φ.toRingHom] ContinuousKaehlerDifferential K L where
  toFun ω := (equivSelf K L).symm (φ (equivSelf K M ω))
  map_add' ω η := by simp only [map_add]
  map_smul' x ω := by
    simp only [map_smul, smul_eq_mul, map_mul]
    rw [← smul_eq_mul, map_smul]
    rfl

@[simp]
theorem equivSelf_pullback (φ : M →ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    equivSelf K L (pullback φ ω) = φ (equivSelf K M ω) :=
  (equivSelf K L).apply_symm_apply _

@[simp]
theorem pullback_smul (φ : M →ₐ[K⸨X⸩] L) (x : M) (ω : ContinuousKaehlerDifferential K M) :
    pullback φ (x • ω) = φ x • pullback φ ω :=
  (pullback φ).map_smulₛₗ x ω

@[simp]
theorem pullback_D (φ : M →ₐ[K⸨X⸩] L) (x : M) :
    pullback φ (D K M x) = D K L (φ x) :=
  (equivSelf K L).injective <| by rw [equivSelf_pullback, equivSelf_D, equivSelf_D,
    derivation_algHom_apply]

/-- Pullback of continuous one-forms along `φ` descends from `KaehlerDifferential.mapSemilinear`
on algebraic Kähler differentials. -/
theorem pullback_mk (φ : M →ₐ[K⸨X⸩] L) (ω : Ω[M⁄K]) :
    pullback φ (mk K M ω) = mk K L (KaehlerDifferential.mapSemilinear (φ.restrictScalars K) ω) := by
  induction (KaehlerDifferential.span_range_derivation K M ▸ Submodule.mem_top :
      ω ∈ Submodule.span M (Set.range (KaehlerDifferential.D K M))) using
      Submodule.span_induction with
  | mem _ h =>
    obtain ⟨x, rfl⟩ := h
    rw [← D_apply, pullback_D, KaehlerDifferential.mapSemilinear_D, ← D_apply,
      AlgHom.coe_restrictScalars']
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, map_add, ih₁, ih₂]
  | smul x _ _ ih =>
    rw [map_smul, pullback_smul, KaehlerDifferential.mapSemilinear_smul, map_smul, ih,
      AlgHom.coe_restrictScalars']

@[simp]
theorem pullback_map (φ : M →ₐ[K⸨X⸩] L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    pullback φ (map K M ω) = map K L ω :=
  (equivSelf K L).injective <| by rw [equivSelf_pullback, equivSelf_map, equivSelf_map,
    AlgHom.commutes]

@[simp]
theorem pullback_id_apply (ω : ContinuousKaehlerDifferential K L) :
    pullback (AlgHom.id K⸨X⸩ L) ω = ω :=
  (equivSelf K L).injective <| by rw [equivSelf_pullback, AlgHom.id_apply]

theorem pullback_id :
    (pullback (AlgHom.id K⸨X⸩ L) : ContinuousKaehlerDifferential K L →ₗ[L] _) = LinearMap.id :=
  LinearMap.ext pullback_id_apply

@[simp]
theorem pullback_comp_apply (ψ : L →ₐ[K⸨X⸩] N) (φ : M →ₐ[K⸨X⸩] L)
    (ω : ContinuousKaehlerDifferential K M) :
    pullback (ψ.comp φ) ω = pullback ψ (pullback φ ω) :=
  (equivSelf K N).injective <| by rw [equivSelf_pullback, equivSelf_pullback, equivSelf_pullback,
    AlgHom.comp_apply]

theorem pullback_comp (ψ : L →ₐ[K⸨X⸩] N) (φ : M →ₐ[K⸨X⸩] L) :
    pullback (ψ.comp φ) = (pullback ψ).comp (pullback φ) :=
  LinearMap.ext (pullback_comp_apply ψ φ)

/-- **Isomorphism of continuous one-forms** induced by a `K⸨X⸩`-algebra isomorphism
`e : M ≃ₐ[K⸨X⸩] L`. It is `K⸨X⸩`-linear and `e`-semilinear (`pullbackEquiv_smul`). -/
noncomputable def pullbackEquiv (e : M ≃ₐ[K⸨X⸩] L) :
    ContinuousKaehlerDifferential K M ≃ₗ[K⸨X⸩] ContinuousKaehlerDifferential K L where
  toFun := pullback e.toAlgHom
  invFun := pullback e.symm.toAlgHom
  map_add' := map_add _
  map_smul' f ω := by
    rw [← IsScalarTower.algebraMap_smul M, pullback_smul, AlgEquiv.toAlgHom_apply,
      AlgEquiv.commutes, IsScalarTower.algebraMap_smul, RingHom.id_apply]
  left_inv ω := by rw [← pullback_comp_apply, AlgEquiv.symm_comp, pullback_id_apply]
  right_inv ω := by rw [← pullback_comp_apply, AlgEquiv.comp_symm, pullback_id_apply]

theorem pullbackEquiv_apply (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    pullbackEquiv e ω = pullback e.toAlgHom ω :=
  (rfl)

@[simp]
theorem pullbackEquiv_symm (e : M ≃ₐ[K⸨X⸩] L) :
    (pullbackEquiv e).symm = pullbackEquiv e.symm :=
  (rfl)

@[simp]
theorem pullbackEquiv_smul (e : M ≃ₐ[K⸨X⸩] L) (x : M) (ω : ContinuousKaehlerDifferential K M) :
    pullbackEquiv e (x • ω) = e x • pullbackEquiv e ω :=
  pullback_smul e.toAlgHom x ω

@[simp]
theorem pullbackEquiv_D (e : M ≃ₐ[K⸨X⸩] L) (x : M) :
    pullbackEquiv e (D K M x) = D K L (e x) :=
  pullback_D e.toAlgHom x

@[simp]
theorem pullbackEquiv_map (e : M ≃ₐ[K⸨X⸩] L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    pullbackEquiv e (map K M ω) = map K L ω :=
  pullback_map e.toAlgHom ω

end Pullback

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension

namespace TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

section Tower

variable (K M L : Type*) [Field K]
  [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
  [Algebra.FormallyEtale K⸨X⸩ M]
  [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L]
  [Algebra M L]

/-- **Relative pullback of continuous one-forms** in a tower `K⸨X⸩ → M → L` of formally étale
`K⸨X⸩`-algebras. -/
noncomputable def mapTower :
    ContinuousKaehlerDifferential K M →ₗ[M] ContinuousKaehlerDifferential K L :=
  (equivSelf K L).symm.toLinearMap.restrictScalars M ∘ₗ Algebra.linearMap M L ∘ₗ
    (equivSelf K M).toLinearMap

variable {K M L}

@[simp]
theorem equivSelf_mapTower (ω : ContinuousKaehlerDifferential K M) :
    equivSelf K L (mapTower K M L ω) = algebraMap M L (equivSelf K M ω) :=
  (equivSelf K L).apply_symm_apply _

theorem mapTower_eq_pullback_toAlgHom [IsScalarTower K⸨X⸩ M L]
    (ω : ContinuousKaehlerDifferential K M) :
    mapTower K M L ω = pullback (IsScalarTower.toAlgHom K⸨X⸩ M L) ω :=
  (equivSelf K L).injective <| by rw [equivSelf_mapTower, equivSelf_pullback,
    IsScalarTower.toAlgHom_apply]

@[simp]
theorem mapTower_D [IsScalarTower K⸨X⸩ M L] (x : M) :
    mapTower K M L (D K M x) = D K L (algebraMap M L x) := by
  rw [mapTower_eq_pullback_toAlgHom, pullback_D, IsScalarTower.toAlgHom_apply]

@[simp]
theorem mapTower_map [IsScalarTower K⸨X⸩ M L] (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapTower K M L (map K M ω) = map K L ω := by
  rw [mapTower_eq_pullback_toAlgHom, pullback_map]

variable (K M L) in
/-- **`Ω¹_cont(L/K) = L ⊗_M Ω¹_cont(M/K)` in towers.** For formally étale `K⸨X⸩`-algebras
`K⸨X⸩ → M → L`, the relative pullback extends to an `L`-linear equivalence
`L ⊗_M Ω¹_cont(M/K) ≃ Ω¹_cont(L/K)`, `x ⊗ ω ↦ x ω`. -/
noncomputable def tensorEquivTower :
    L ⊗[M] ContinuousKaehlerDifferential K M ≃ₗ[L] ContinuousKaehlerDifferential K L :=
  LinearEquiv.baseChange M L _ _ (equivSelf K M) ≪≫ₗ
    AlgebraTensorModule.rid M L L ≪≫ₗ (equivSelf K L).symm

@[simp]
theorem tensorEquivTower_tmul (x : L) (ω : ContinuousKaehlerDifferential K M) :
    tensorEquivTower K M L (x ⊗ₜ[M] ω) = x • mapTower K M L ω := by
  apply (equivSelf K L).injective
  simp [tensorEquivTower, LinearEquiv.baseChange, Algebra.smul_def, mul_comm]

end Tower

end TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential
