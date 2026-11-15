/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale
public import TauCeti.Topology.Algebra.Module.ModuleTopology
import TauCeti.RingTheory.Derivation.ModuleTopology

/-!
# The module topology on continuous one-forms of étale Laurent extensions

Let `K` be a field, `F = K⸨X⸩` with its valuation topology, and `L` a formally étale `F`-algebra.
Whenever `L` carries a topology, `Extension.ContinuousKaehlerDifferential K L` is equipped with its
`L`-module topology (`moduleTopology L _`). When `L` is a topological semiring, the rank-one
presentation `equivSelf K L : Ω¹_cont(L/K) ≃ₗ[L] L` upgrades to a continuous `L`-linear
equivalence (`continuousEquivSelf`), and every `L`-linear map out of `Ω¹_cont(L/K)` into a module
with continuous `L`-scalar multiplication is continuous (`continuous_of_linearMap`).

When `L` is finite over `F` and carries the `F`-module topology (`[IsModuleTopology K⸨X⸩ L]`):

* `Ω¹_cont(L/K)` also carries the `F`-module topology (by `IsModuleTopology.restrictScalars`), and
  both `L` and `Ω¹_cont(L/K)` are Hausdorff topological additive groups (`L` a topological ring).
* By `Derivation.continuous_iff_of_isModuleTopology`, `Extension.derivation K L` (`d/dt`) and the
  universal derivation `D K L` are continuous on `L`, `D K L` is the universal continuous
  `K`-derivation on `L`, and the scalar extension `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` upgrades to a
  continuous `F`-linear equivalence (`continuousTensorEquiv`).

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968).
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Extension

variable (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- On a finite formally étale `K⸨X⸩`-algebra carrying the `K⸨X⸩`-module topology, the extended
derivation `d/dt` is continuous. -/
theorem continuous_derivation [Module.Finite K⸨X⸩ L] [TopologicalSpace L]
    [IsModuleTopology K⸨X⸩ L] : Continuous (derivation K L) := by
  have : IsTopologicalRing L := IsModuleTopology.isTopologicalRing K⸨X⸩ L
  rw [(derivation K L).continuous_iff_of_isModuleTopology K⸨X⸩]
  have halg : Continuous (algebraMap K⸨X⸩ L) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap K⸨X⸩ L)
  exact (halg.comp (_root_.LaurentSeries.continuous_derivative (K := K))).congr fun f ↦ by
    rw [Function.comp_apply, ← laurentSeriesDerivation_apply, derivation_algebraMap]

namespace ContinuousKaehlerDifferential

section TopologicalSpace

variable [TopologicalSpace L]

/-- `Ω¹_cont(L/K)` carries the module topology over `L`. -/
noncomputable instance : TopologicalSpace (ContinuousKaehlerDifferential K L) :=
  moduleTopology L _

instance : IsModuleTopology L (ContinuousKaehlerDifferential K L) := ⟨rfl⟩

instance : IsTopologicalAddGroup (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.isTopologicalAddGroup L _

variable {K L} in
/-- Pullback of continuous one-forms along a continuous `K⸨X⸩`-algebra homomorphism is
continuous. -/
theorem continuous_pullback {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] [TopologicalSpace M]
    (φ : M →ₐ[K⸨X⸩] L) (hφ : Continuous φ) :
    Continuous (pullback φ) :=
  IsModuleTopology.continuous_of_linearMapₛₗ hφ (pullback φ)

section Semiring

variable [IsTopologicalSemiring L]

/-- When `L` is a topological semiring, the rank-one identification `Ω¹_cont(L/K) ≃ L` sending
`d t` to `1` is a continuous `L`-linear equivalence. -/
noncomputable def continuousEquivSelf :
    ContinuousKaehlerDifferential K L ≃L[L] L :=
  (equivSelf K L).toContinuousLinearEquivOfIsModuleTopology

variable {K L}

@[simp]
theorem coe_continuousEquivSelf :
    ⇑(continuousEquivSelf K L) = equivSelf K L := by
  simp [continuousEquivSelf]

@[simp]
theorem toLinearEquiv_continuousEquivSelf :
    (continuousEquivSelf K L).toLinearEquiv = equivSelf K L := by
  simp [continuousEquivSelf]

@[simp]
theorem continuousEquivSelf_symm_apply (x : L) :
    (continuousEquivSelf K L).symm x = (equivSelf K L).symm x := by
  simp [continuousEquivSelf, -equivSelf_symm_apply]

instance [T2Space L] : T2Space (ContinuousKaehlerDifferential K L) :=
  (continuousEquivSelf K L).toHomeomorph.isEmbedding.t2Space

/-- Every `L`-linear map out of `Ω¹_cont(L/K)` into a module with continuous `L`-scalar
multiplication is continuous, without assuming continuity of addition on the target. -/
@[fun_prop]
theorem continuous_of_linearMap {N : Type*} [AddCommMonoid N] [Module L N]
    [TopologicalSpace N] [ContinuousSMul L N]
    (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] N) : Continuous ℓ :=
  ((continuousEquivSelf K L).continuous.fun_smul continuous_const).congr fun ω ↦ by
    simpa only [map_smul, coe_continuousEquivSelf] using
      congrArg ℓ (equivSelf_smul_D_algebraMap_single_one ω)

end Semiring

section FiniteModuleTopology

variable [Module.Finite K⸨X⸩ L] [IsModuleTopology K⸨X⸩ L]

/-- When `L` is finite over `K⸨X⸩` and carries the `K⸨X⸩`-module topology, the `L`-module
topology on `Ω¹_cont(L/K)` is also the `K⸨X⸩`-module topology. -/
instance : IsModuleTopology K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.restrictScalars K⸨X⸩ L _

/-- Over a finite `K⸨X⸩`-algebra with the `K⸨X⸩`-module topology, `Ω¹_cont(L/K)` is Hausdorff. -/
theorem t2Space_of_isModuleTopology : T2Space (ContinuousKaehlerDifferential K L) := by
  have : IsTopologicalRing L := IsModuleTopology.isTopologicalRing K⸨X⸩ L
  have : T2Space L := TauCeti.ModuleTopology.t2Space (Module.Free.chooseBasis K⸨X⸩ L)
  infer_instance

/-- The universal derivation `d : L → Ω¹_cont(L/K)` is continuous for the `K⸨X⸩`-module
topology. -/
theorem continuous_D : Continuous (D K L) := by
  have : IsTopologicalRing L := IsModuleTopology.isTopologicalRing K⸨X⸩ L
  refine (continuousEquivSelf K L).toHomeomorph.comp_continuous_iff.mp ?_
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_def,
    coe_continuousEquivSelf, equivSelf_D] using continuous_derivation K L

/-- Pulling back continuous one-forms from `K⸨X⸩` to `L` is continuous. -/
theorem continuous_map : Continuous (map K L) :=
  TauCeti.ContinuousKaehlerDifferential.continuous_of_linearMap (map K L)

/-- The scalar-extension isomorphism `L ⊗_{K⸨X⸩} Ω¹_cont(K⸨X⸩/K) ≃ Ω¹_cont(L/K)` upgraded to a
continuous `K⸨X⸩`-linear equivalence whenever the tensor product carries the `K⸨X⸩`-module
topology (for instance via `open scoped TauCeti.ModuleTopology`). -/
noncomputable def continuousTensorEquiv
    [TopologicalSpace (L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K)]
    [IsModuleTopology K⸨X⸩ (L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K)] :
    (L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) ≃L[K⸨X⸩]
      ContinuousKaehlerDifferential K L :=
  ((tensorEquiv K L).restrictScalars K⸨X⸩).toContinuousLinearEquivOfIsModuleTopology

variable {K L}

@[simp]
theorem coe_continuousTensorEquiv
    [TopologicalSpace (L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K)]
    [IsModuleTopology K⸨X⸩ (L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K)] :
    ⇑(continuousTensorEquiv K L) = tensorEquiv K L := by
  simp [continuousTensorEquiv]
  rfl

omit [Module.Finite K⸨X⸩ L] in
/-- **Topological universal property of `Ω¹_cont(L/K)`.** On a formally étale `K⸨X⸩`-algebra `L`
carrying the `K⸨X⸩`-module topology, every continuous `K`-derivation `δ : L → N` into a Hausdorff
topological `L`-module factors uniquely through `d`, and the resulting `L`-linear map is
automatically continuous. -/
theorem existsUnique_compDer_eq_of_continuous {N : Type*} [AddCommGroup N] [Module L N]
    [Module K N] [IsScalarTower K L N] [TopologicalSpace N] [T2Space N] [ContinuousSMul L N]
    (δ : Derivation K L N) (hδ : Continuous δ) :
    ∃! ℓ : ContinuousKaehlerDifferential K L →ₗ[L] N, ℓ.compDer (D K L) = δ := by
  let _ : Module K⸨X⸩ N := Module.compHom N (algebraMap K⸨X⸩ L)
  have : IsScalarTower K⸨X⸩ L N := ⟨fun f x n ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower K K⸨X⸩ N := ⟨fun c f n ↦ by
    rw [← IsScalarTower.algebraMap_smul L (c • f), ← IsScalarTower.algebraMap_smul L f,
      ← laurentSeries_algebraMap_mul_eq_smul, map_mul, ← IsScalarTower.algebraMap_apply K K⸨X⸩ L,
      mul_smul, IsScalarTower.algebraMap_smul]⟩
  have : ContinuousAdd L := IsModuleTopology.toContinuousAdd K⸨X⸩ L
  have halg : Continuous (algebraMap K⸨X⸩ L) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap K⸨X⸩ L)
  have : ContinuousSMul K⸨X⸩ N :=
    ⟨(continuous_smul.comp ((halg.comp continuous_fst).prodMk continuous_snd)).congr
      fun p ↦ IsScalarTower.algebraMap_smul L p.1 p.2⟩
  exact existsUnique_compDer_eq δ (hδ.comp halg)

end FiniteModuleTopology

end TopologicalSpace

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension
