/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import TauCeti.RingTheory.Kaehler.Trace.FormallyEtale
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.ModuleTopology
public import TauCeti.RingTheory.LaurentSeries.Level.Adjoin
public import TauCeti.RingTheory.LaurentSeries.Level.DifferentialTransition
public import TauCeti.RingTheory.LaurentSeries.Level.ModuleTopology
public import TauCeti.RingTheory.LaurentSeries.Level.Residue
import TauCeti.RingTheory.LaurentSeries.ContinuousDual.Basic

/-!
# Differential traces, residues, and level comparisons on étale Laurent extensions

Let `K` be a field, `F = K⸨X⸩`, and `Ω = TauCeti.ContinuousKaehlerDifferential K` the module of
continuous one-forms of `F`.

1. **Base residue and scalar-extended trace.** The `K`-linear residue
   `TauCeti.ContinuousKaehlerDifferential.residue K : Ω →ₗ[K] K` extracts the coefficient of `X⁻¹`,
   vanishes on exact forms, and is continuous into discrete `K`. For any `F`-algebra `L`,
   `traceBaseChange L : L ⊗[F] Ω →ₗ[F] Ω` applies `Algebra.trace F L` on the first factor, and
   `residueBaseChange L` composes it with the base residue.

2. **Intrinsic differential trace and residue on formally étale extensions.** When `L` is formally
   étale over `F` (for instance any finite separable extension), transport along the scalar
   extension `L ⊗[F] Ω ≃ₗ[L] Ω¹_cont(L/K)` (`Extension.ContinuousKaehlerDifferential.tensorEquiv`)
   yields the intrinsic differential trace
   `Extension.ContinuousKaehlerDifferential.trace K L : Ω¹_cont(L/K) →ₗ[F] Ω` and `K`-linear
   residue `Extension.ContinuousKaehlerDifferential.residue K L : Ω¹_cont(L/K) →ₗ[K] K`:
   * On finite extensions, `trace K L` descends from Kunz's algebraic differential trace
     `Derivation.traceLin (D K) : Ω[L⁄K] →ₗ[F] Ω` (`trace_mk`), and is continuous for the
     `F`-module topology (`continuous_trace`, `continuous_residue`).
   * Unconditionally, `trace K L (d x) = d (Tr_{L/F} x)` (`trace_D`), so exact forms have residue
     zero (`residue_D`) and integration by parts holds (`residue_smul_D_eq_neg`).
   * In towers `F → M → L`, the relative trace `traceTower K M L : Ω¹_cont(L/K) →ₗ[M] Ω¹_cont(M/K)`
     is transitive (`trace_traceTower`) and preserves residues (`residue_traceTower`), proving
     Tate's identity `Res_M (Tr_{L/M} ω) = Res_L ω`.

3. **Comparison with ramified Laurent levels and level charts.** When `d` is nonzero in `K`, the
   ramified level `Level K d` (`u ^ d = X`) is separable (`Level.isSeparable_iff`) and hence
   formally étale over `F`. Its abstract module of continuous one-forms identifies with the explicit
   level one-forms via a continuous `Level K d`-linear equivalence
   `Level.ContinuousKaehlerDifferential.equivExtension K d`, sending `d g` to `d g` in the level
   parameter `u`, intertwining differential traces, and identifying the intrinsic residue with the
   coefficient of `u⁻¹` (`residue_eq_coeff_equivExtension`). Along any level chart
   `e : L ≃ₐ[F] Level K d`, `e.laurentContinuousDifferentialEquiv` transports these identifications
   to `Ω¹_cont(L/K)`.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), for the construction of
  the trace of continuous differentials via scalar extension and its compatibility with residues.
* E. Kunz, *Kähler Differentials*, Vieweg (1986), §16, for the matrix trace of differentials.
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.ContinuousKaehlerDifferential

section BaseResidue

variable (K : Type*) [Field K]

/-- **The formal residue on `Ω¹_cont(K⸨X⸩/K)`.** The `K`-linear map extracting the coefficient of
`X⁻¹` from `f dX`. -/
noncomputable def residue : ContinuousKaehlerDifferential K →ₗ[K] K where
  toFun ω := (equivLaurentSeries K ω).coeff (-1)
  map_add' ω η := by simp
  map_smul' c ω := by
    rw [← IsScalarTower.algebraMap_smul K⸨X⸩ c ω, map_smul, smul_eq_mul,
      laurentSeries_algebraMap_mul_eq_smul, coeff_smul, RingHom.id_apply]

variable {K}

theorem residue_apply (ω : ContinuousKaehlerDifferential K) :
    residue K ω = (equivLaurentSeries K ω).coeff (-1) :=
  (rfl)

/-- Exact continuous one-forms on `K⸨X⸩` have residue zero, in every characteristic. -/
@[simp]
theorem residue_D (f : K⸨X⸩) : residue K (D K f) = 0 := by
  rw [residue_apply, equivLaurentSeries_D, _root_.LaurentSeries.coeff_neg_one_derivative]

/-- The residue `Ω¹_cont(K⸨X⸩/K) → K` is continuous when `K` carries the discrete topology. -/
theorem continuous_residue [TopologicalSpace K] [DiscreteTopology K] :
    Continuous (residue K) := by
  have h := (_root_.LaurentSeries.continuous_residueForm (K := K) 1).comp
    (equivLaurentSeries K).continuous
  exact h.congr fun ω ↦ by
    simp only [Function.comp_apply, TauCeti.LaurentSeries.residueForm_apply, one_mul, residue_apply]

end BaseResidue

section BaseChange

variable {K : Type*} [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L]

/-- The differential trace on scalar-extended continuous forms: apply `Algebra.trace K⸨X⸩ L` on the
first tensor factor, so that `x ⊗ ω` maps to `Tr(x) ω`. As with `Algebra.trace`, this is zero when
`L` is not finite over `K⸨X⸩`. -/
noncomputable def traceBaseChange :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K :=
  (TensorProduct.lid K⸨X⸩ _).toLinearMap ∘ₗ (Algebra.trace K⸨X⸩ L).rTensor _

@[simp]
theorem traceBaseChange_tmul (x : L) (ω : ContinuousKaehlerDifferential K) :
    traceBaseChange L (x ⊗ₜ ω) = Algebra.trace K⸨X⸩ L x • ω := by
  simp [traceBaseChange]

/-- Tracing a pulled-back form multiplies it by the `K⸨X⸩`-rank of `L`. -/
theorem traceBaseChange_one_tmul (ω : ContinuousKaehlerDifferential K) :
    traceBaseChange L (1 ⊗ₜ ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [traceBaseChange_tmul, ← map_one (algebraMap K⸨X⸩ L), Algebra.trace_algebraMap,
    smul_assoc, one_smul]

/-- The residue on scalar-extended continuous forms, computed as the residue of their differential
trace. For every separable level chart this equals the coefficient residue in its level
parameter. -/
noncomputable def residueBaseChange :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K →+ K where
  toFun η := (equivLaurentSeries K (traceBaseChange L η)).coeff (-1)
  map_zero' := by simp
  map_add' η θ := by simp

/-- The residue is the coefficient of `X⁻¹` in the differential trace. -/
theorem residueBaseChange_apply (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    residueBaseChange L η = (equivLaurentSeries K (traceBaseChange L η)).coeff (-1) :=
  (rfl)

/-- On a pure tensor `x ⊗ f dX`, the residue is the coefficient of `X⁻¹` in `Tr(x) f`. -/
@[simp]
theorem residueBaseChange_tmul (x : L) (ω : ContinuousKaehlerDifferential K) :
    residueBaseChange L (x ⊗ₜ ω) =
      (Algebra.trace K⸨X⸩ L x * equivLaurentSeries K ω).coeff (-1) := by
  simp [residueBaseChange_apply]

/-- The residue of a form pulled back from the base is multiplied by the degree. -/
theorem residueBaseChange_one_tmul (ω : ContinuousKaehlerDifferential K) :
    residueBaseChange L (1 ⊗ₜ ω) =
      Module.finrank K⸨X⸩ L • (equivLaurentSeries K ω).coeff (-1) := by
  rw [residueBaseChange_apply, traceBaseChange_one_tmul]
  simp only [map_nsmul, HahnSeries.coeff_nsmul, Pi.smul_apply]

end BaseChange

end TauCeti.ContinuousKaehlerDifferential

namespace TauCeti.LaurentSeries.Extension

section TraceDerivation

variable {K L : Type*} [Field K] [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- **Algebraic trace commutes with `d/dt`.** On any formally étale `K⸨X⸩`-algebra `L`,
`Tr_{L/K⸨X⸩} (D_L x) = D (Tr_{L/K⸨X⸩} x)`. When `L` is not finite over `K⸨X⸩`, both sides vanish. -/
@[simp]
theorem trace_derivation (x : L) :
    Algebra.trace K⸨X⸩ L (derivation K L x) =
      laurentSeriesDerivation K (Algebra.trace K⸨X⸩ L x) := by
  by_cases h : ∃ s : Finset L, Nonempty (Module.Basis s K⸨X⸩ L)
  · obtain ⟨s, ⟨b⟩⟩ := h
    have : Module.Finite K⸨X⸩ L := Module.Finite.of_basis b
    have hμ := Derivation.map_trace_apply_eq_of_formallyUnramified
      (TauCeti.ContinuousKaehlerDifferential.D K)
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).symm.toLinearEquiv.toLinearMap
      (d₀ := laurentSeriesDerivation K)
      (fun r ↦ (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective <| by simp)
      (fun f ↦ derivation_algebraMap f) x
    simpa using congrArg (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K) hμ
  · simp [Algebra.trace_eq_zero_of_not_exists_basis K⸨X⸩ h]

end TraceDerivation

namespace ContinuousKaehlerDifferential

section IntrinsicTraceAndResidue

variable (K L : Type*) [Field K] [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- **The differential trace `Tr_{L/K⸨X⸩} : Ω¹_cont(L/K) →ₗ[K⸨X⸩] Ω¹_cont(K⸨X⸩/K)`.**
Constructed via `L ⊗_{K⸨X⸩} Ω¹_cont(K⸨X⸩/K) ≃ Ω¹_cont(L/K)` by applying `Algebra.trace K⸨X⸩ L` on
the first factor; in normal form, `x dX ↦ Tr_{L/K⸨X⸩}(x) dX`. -/
noncomputable def trace :
    ContinuousKaehlerDifferential K L →ₗ[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K :=
  TauCeti.ContinuousKaehlerDifferential.traceBaseChange L ∘ₗ
    ((tensorEquiv K L).symm.restrictScalars K⸨X⸩).toLinearMap

/-- **The formal residue `Res_L : Ω¹_cont(L/K) →ₗ[K] K`** on a formally étale `K⸨X⸩`-algebra,
defined as the base residue of the differential trace. -/
noncomputable def residue : ContinuousKaehlerDifferential K L →ₗ[K] K :=
  (TauCeti.ContinuousKaehlerDifferential.residue K).comp ((trace K L).restrictScalars K)

variable {K L}

@[simp]
theorem trace_tensorEquiv (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (tensorEquiv K L η) = TauCeti.ContinuousKaehlerDifferential.traceBaseChange L η := by
  simp [trace]

@[simp]
theorem trace_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (x • map K L ω) = Algebra.trace K⸨X⸩ L x • ω := by
  rw [← tensorEquiv_tmul, trace_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.traceBaseChange_tmul]

@[simp]
theorem trace_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (map K L ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [← one_smul L (map K L ω), ← tensorEquiv_tmul, trace_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.traceBaseChange_one_tmul]

/-- In coordinates with respect to `dX`, `trace K L` applies `Algebra.trace K⸨X⸩ L` to the
coefficient `equivSelf K L ω`. -/
@[simp]
theorem equivLaurentSeries_trace (ω : ContinuousKaehlerDifferential K L) :
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω) =
      Algebra.trace K⸨X⸩ L (equivSelf K L ω) := by
  conv_lhs => rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D, trace_smul_map]
  simp

/-- **Differential trace commutes with `d`.** On any formally étale `K⸨X⸩`-algebra `L`,
`Tr_{L/K⸨X⸩} (d x) = d (Tr_{L/K⸨X⸩} x)`. -/
@[simp]
theorem trace_D (x : L) :
    trace K L (D K L x) =
      TauCeti.ContinuousKaehlerDifferential.D K (Algebra.trace K⸨X⸩ L x) := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivSelf_D, trace_derivation, laurentSeriesDerivation_apply,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D]

/-- **Comparison with Kunz's matrix differential trace.** When `L` is finite over `K⸨X⸩`,
`trace K L` on the quotient `Ω¹_cont(L/K)` descends from Kunz's algebraic trace
`Derivation.traceLin (D K) : Ω[L⁄K] →ₗ[K⸨X⸩] Ω¹_cont(K⸨X⸩/K)`. -/
theorem trace_mk [Module.Finite K⸨X⸩ L] (ω : Ω[L⁄K]) :
    trace K L (mk K L ω) =
      Derivation.traceLin (TauCeti.ContinuousKaehlerDifferential.D K) ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivSelf_mk,
    Derivation.traceLin_apply_eq_map_trace_liftKaehlerDifferential
      (TauCeti.ContinuousKaehlerDifferential.D K)
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).symm.toLinearEquiv.toLinearMap
      (d₀ := laurentSeriesDerivation K)
      (fun r ↦ (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective <| by simp)
      (fun f ↦ derivation_algebraMap f)]
  exact ((TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).apply_symm_apply _).symm

@[simp]
theorem trace_pullbackEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    trace K L (pullbackEquiv e ω) = trace K M ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, pullbackEquiv_apply, equivSelf_pullback, AlgEquiv.toAlgHom_apply,
    Algebra.trace_eq_of_algEquiv e, equivLaurentSeries_trace]

/-- On a finite formally étale `K⸨X⸩`-algebra carrying the `K⸨X⸩`-module topology, the differential
trace is continuous. -/
theorem continuous_trace [Module.Finite K⸨X⸩ L] [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] :
    Continuous (trace K L) :=
  IsModuleTopology.continuous_of_linearMap (trace K L)

theorem residue_apply (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = TauCeti.ContinuousKaehlerDifferential.residue K (trace K L ω) :=
  (rfl)

/-- In terms of the `dX`-coordinate `equivSelf K L ω`, the residue is the coefficient of `X⁻¹` in
its algebraic trace to `K⸨X⸩`. -/
theorem residue_eq_coeff_neg_one_trace (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = (Algebra.trace K⸨X⸩ L (equivSelf K L ω)).coeff (-1) := by
  rw [residue_apply, TauCeti.ContinuousKaehlerDifferential.residue_apply, equivLaurentSeries_trace]

theorem residue_equivSelf_symm (x : L) :
    residue K L ((equivSelf K L).symm x) = (Algebra.trace K⸨X⸩ L x).coeff (-1) := by
  rw [residue_eq_coeff_neg_one_trace, LinearEquiv.apply_symm_apply]

@[simp]
theorem residue_tensorEquiv (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (tensorEquiv K L η) =
      TauCeti.ContinuousKaehlerDifferential.residueBaseChange L η := by
  rw [residue_apply, trace_tensorEquiv, TauCeti.ContinuousKaehlerDifferential.residue_apply,
    TauCeti.ContinuousKaehlerDifferential.residueBaseChange_apply]

@[simp]
theorem residue_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (map K L ω) =
      Module.finrank K⸨X⸩ L • TauCeti.ContinuousKaehlerDifferential.residue K ω := by
  rw [residue_apply, trace_map, map_nsmul]

/-- **Exact continuous one-forms have residue zero.** On any formally étale `K⸨X⸩`-algebra `L`,
`Res_L (d x) = 0` in every characteristic. -/
@[simp]
theorem residue_D (x : L) : residue K L (D K L x) = 0 := by
  rw [residue_apply, trace_D, TauCeti.ContinuousKaehlerDifferential.residue_D]

/-- **Integration by parts for residues on étale extensions:** `Res_L (x dy) = -Res_L (y dx)`. -/
theorem residue_smul_D_eq_neg (x y : L) :
    residue K L (x • D K L y) = -residue K L (y • D K L x) := by
  have h := residue_D (K := K) (L := L) (x * y)
  rw [Derivation.leibniz, map_add, add_eq_zero_iff_eq_neg] at h
  exact h

@[simp]
theorem residue_pullbackEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    residue K L (pullbackEquiv e ω) = residue K M ω := by
  rw [residue_apply, trace_pullbackEquiv, ← residue_apply]

/-- On a finite formally étale `K⸨X⸩`-algebra carrying the `K⸨X⸩`-module topology, the residue
functional `Ω¹_cont(L/K) → K` into discrete `K` is continuous. -/
theorem continuous_residue [Module.Finite K⸨X⸩ L] [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]
    [TopologicalSpace K] [DiscreteTopology K] :
    Continuous (residue K L) :=
  TauCeti.ContinuousKaehlerDifferential.continuous_residue.comp continuous_trace

end IntrinsicTraceAndResidue

section Tower

variable (K M L : Type*) [Field K]
  [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
  [Algebra.FormallyEtale K⸨X⸩ M]
  [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L]
  [Algebra M L]

/-- **Relative differential trace in a tower** `K⸨X⸩ → M → L` of formally étale `K⸨X⸩`-algebras,
acting via `Algebra.trace M L` on the first factor of `L ⊗_M Ω¹_cont(M/K) ≃ Ω¹_cont(L/K)`. -/
noncomputable def traceTower :
    ContinuousKaehlerDifferential K L →ₗ[M] ContinuousKaehlerDifferential K M :=
  (TensorProduct.lid M _).toLinearMap ∘ₗ
    (Algebra.trace M L).rTensor _ ∘ₗ
      ((tensorEquivTower K M L).symm.restrictScalars M).toLinearMap

variable {K M L}

theorem traceTower_tensorEquivTower (x : L) (ω : ContinuousKaehlerDifferential K M) :
    traceTower K M L (tensorEquivTower K M L (x ⊗ₜ[M] ω)) = Algebra.trace M L x • ω := by
  simp [traceTower, -tensorEquivTower_tmul]

@[simp]
theorem traceTower_smul_mapTower (x : L) (ω : ContinuousKaehlerDifferential K M) :
    traceTower K M L (x • mapTower K M L ω) = Algebra.trace M L x • ω := by
  rw [← tensorEquivTower_tmul, traceTower_tensorEquivTower]

@[simp]
theorem traceTower_mapTower [Nontrivial M] [Module.Free M L]
    (ω : ContinuousKaehlerDifferential K M) :
    traceTower K M L (mapTower K M L ω) = Module.finrank M L • ω := by
  rw [← one_smul L (mapTower K M L ω), traceTower_smul_mapTower, ← map_one (algebraMap M L),
    Algebra.trace_algebraMap, smul_assoc, one_smul]

@[simp]
theorem equivSelf_traceTower [IsScalarTower K⸨X⸩ M L] (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K M (traceTower K M L ω) = Algebra.trace M L (equivSelf K L ω) := by
  have ht : D K L (algebraMap K⸨X⸩ L (single 1 1)) =
      mapTower K M L (D K M (algebraMap K⸨X⸩ M (single 1 1))) := by
    rw [mapTower_D, ← IsScalarTower.algebraMap_apply K⸨X⸩ M L]
  conv_lhs => rw [← equivSelf_smul_D_algebraMap_single_one ω, ht, traceTower_smul_mapTower]
  rw [map_smul, equivSelf_D, derivation_algebraMap_single_one, smul_eq_mul, mul_one]

/-- In a finite free step `M → L` of a tower over `K⸨X⸩`, the relative differential trace commutes
with the universal derivations: `Tr_{L/M} (d x) = d (Tr_{L/M} x)`. -/
@[simp]
theorem traceTower_D [IsScalarTower K⸨X⸩ M L] [Module.Free M L] [Module.Finite M L] (x : L) :
    traceTower K M L (D K L x) = D K M (Algebra.trace M L x) := by
  have : Algebra.FormallyUnramified M L := .of_restrictScalars K⸨X⸩ M L
  have : IsScalarTower K M L := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply K K⸨X⸩ L, IsScalarTower.algebraMap_apply K⸨X⸩ M L,
      ← IsScalarTower.algebraMap_apply K K⸨X⸩ M]
  apply (equivSelf K M).injective
  rw [equivSelf_traceTower, equivSelf_D, equivSelf_D]
  exact Derivation.trace_apply_eq_of_formallyUnramified (Extension.derivation K M)
    (fun m ↦ Extension.derivation_algHom_apply (IsScalarTower.toAlgHom K⸨X⸩ M L) m) x

/-- **Transitivity of differential trace in towers:** `Tr_{M/F} (Tr_{L/M} ω) = Tr_{L/F} ω`. -/
@[simp]
theorem trace_traceTower [IsScalarTower K⸨X⸩ M L] [Module.Finite K⸨X⸩ M]
    [Module.Free M L] [Module.Finite M L] (ω : ContinuousKaehlerDifferential K L) :
    trace K M (traceTower K M L ω) = trace K L ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivSelf_traceTower, Algebra.trace_trace, equivLaurentSeries_trace]

/-- **Tate's residue-trace formula in towers:** `Res_M (Tr_{L/M} ω) = Res_L ω`. -/
@[simp]
theorem residue_traceTower [IsScalarTower K⸨X⸩ M L] [Module.Finite K⸨X⸩ M]
    [Module.Free M L] [Module.Finite M L] (ω : ContinuousKaehlerDifferential K L) :
    residue K M (traceTower K M L ω) = residue K L ω := by
  rw [residue_apply, trace_traceTower, ← residue_apply]

/-- Pulling back a form along a finite free step `M → L` multiplies its differential trace to
`K⸨X⸩` by the relative rank `finrank M L`. -/
@[simp]
theorem trace_mapTower [Nontrivial M] [IsScalarTower K⸨X⸩ M L] [Module.Finite K⸨X⸩ M]
    [Module.Free M L] [Module.Finite M L] (ω : ContinuousKaehlerDifferential K M) :
    trace K L (mapTower K M L ω) = Module.finrank M L • trace K M ω := by
  rw [← trace_traceTower (K := K) (M := M) (L := L), traceTower_mapTower, map_nsmul]

/-- Pulling back a form along a finite free step `M → L` multiplies its residue by the relative
rank `finrank M L`. -/
@[simp]
theorem residue_mapTower [Nontrivial M] [IsScalarTower K⸨X⸩ M L] [Module.Finite K⸨X⸩ M]
    [Module.Free M L] [Module.Finite M L] (ω : ContinuousKaehlerDifferential K M) :
    residue K L (mapTower K M L ω) = Module.finrank M L • residue K M ω := by
  rw [residue_apply, trace_mapTower, map_nsmul, ← residue_apply]

end Tower

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension

namespace TauCeti.LaurentSeries.Level

namespace ContinuousKaehlerDifferential

section BaseModule

variable (K : Type*) [Field K] (d : ℕ+)

/-- The constant field `K` acts on the one-forms of level `d` through `Level K d`. -/
noncomputable instance : Module K (Level.ContinuousKaehlerDifferential K d) :=
  Module.compHom _ (Algebra.algebraMap K (Level K d))

instance : IsScalarTower K (Level K d) (Level.ContinuousKaehlerDifferential K d) :=
  ⟨fun c g ω ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩

instance : IsScalarTower K K⸨X⸩ (Level.ContinuousKaehlerDifferential K d) :=
  ⟨fun c f ω ↦ by
    rw [← IsScalarTower.algebraMap_smul (Level K d) (c • f), ← laurentSeries_algebraMap_mul_eq_smul,
      map_mul, ← IsScalarTower.algebraMap_apply K K⸨X⸩ (Level K d), ← Algebra.smul_def,
      smul_assoc, IsScalarTower.algebraMap_smul]⟩

variable {K d}

@[simp]
theorem addEquivContinuousKaehlerDifferential_base_smul (c : K)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    addEquivContinuousKaehlerDifferential K d (c • ω) =
      c • addEquivContinuousKaehlerDifferential K d ω := by
  rw [← IsScalarTower.algebraMap_smul (Level K d) c, addEquivContinuousKaehlerDifferential_smul,
    ringEquivLaurentSeries_algebraMap_base, IsScalarTower.algebraMap_smul]

variable (K d) in
/-- The level's own `K`-derivation `g ↦ d(g(u))` in the level variable `u`. -/
private noncomputable def levelDerivation :
    Derivation K (Level K d) (Level.ContinuousKaehlerDifferential K d) where
  toFun g := ofForm (TauCeti.ContinuousKaehlerDifferential.D K (ringEquivLaurentSeries K d g))
  map_add' g h := by
    apply (addEquivContinuousKaehlerDifferential K d).injective
    simp
  map_smul' c g := by
    apply (addEquivContinuousKaehlerDifferential K d).injective
    rw [RingHom.id_apply, Algebra.smul_def, map_mul, ringEquivLaurentSeries_algebraMap_base,
      addEquivContinuousKaehlerDifferential_ofForm, Derivation.leibniz,
      Derivation.map_algebraMap, smul_zero, add_zero,
      addEquivContinuousKaehlerDifferential_base_smul,
      addEquivContinuousKaehlerDifferential_ofForm, IsScalarTower.algebraMap_smul]
  map_one_eq_zero' := by
    apply (addEquivContinuousKaehlerDifferential K d).injective
    simp
  leibniz' g h := by
    apply (addEquivContinuousKaehlerDifferential K d).injective
    simp [Derivation.leibniz]

@[simp]
private theorem levelDerivation_apply (g : Level K d) :
    levelDerivation K d g =
      ofForm (TauCeti.ContinuousKaehlerDifferential.D K (ringEquivLaurentSeries K d g)) :=
  (rfl)

end BaseModule

end ContinuousKaehlerDifferential

section SeparableLevel

variable (K : Type*) [Field K] (d : ℕ+) [NeZero ((d : ℕ) : K)]

/-- When `d` is nonzero in `K`, the ramified level `Level K d` is formally étale over `K⸨X⸩`. -/
instance : Algebra.FormallyEtale K⸨X⸩ (Level K d) :=
  .of_isSeparable _ _

namespace ContinuousKaehlerDifferential

/-- **Equivalence between abstract étale continuous one-forms and explicit level one-forms.**
When `d` is nonzero in `K`, `Ω¹_cont(Level K d / K)` is topologically and `Level K d`-linearly
isomorphic to `Level.ContinuousKaehlerDifferential K d`, compatible with the scalar-extension
presentations over `K⸨X⸩`. -/
noncomputable def equivExtension :
    Extension.ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
      Level.ContinuousKaehlerDifferential K d :=
  ((Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d)).symm.trans
    (Level.ContinuousKaehlerDifferential.tensorEquiv K d)).toContinuousLinearEquivOfIsModuleTopology

variable {K d}

@[simp]
theorem equivExtension_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    equivExtension K d (Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d) η) =
      Level.ContinuousKaehlerDifferential.tensorEquiv K d η := by
  simp [equivExtension]

@[simp]
theorem equivExtension_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivExtension K d (Extension.ContinuousKaehlerDifferential.map K (Level K d) ω) =
      Level.ContinuousKaehlerDifferential.map K d ω := by
  rw [← one_smul (Level K d) (Extension.ContinuousKaehlerDifferential.map K (Level K d) ω),
    ← Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul, equivExtension_tensorEquiv,
    Level.ContinuousKaehlerDifferential.tensorEquiv_tmul, one_smul]

/-- In coordinates, `equivExtension K d` multiplies the `dt`-coordinate `equivSelf` by
`d(u ^ d)/du = d u ^ (d - 1)` to produce the `du`-coordinate `equivLevel`. -/
theorem equivLevel_equivExtension
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    equivLevel K d (equivExtension K d ω) =
      Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d) ω *
        (ringEquivLaurentSeries K d).symm
          (_root_.LaurentSeries.derivative K (single (d : ℤ) 1)) := by
  conv_lhs =>
    rw [← Extension.ContinuousKaehlerDifferential.equivSelf_smul_D_algebraMap_single_one ω,
      ← Extension.ContinuousKaehlerDifferential.map_D, map_smul, equivExtension_map]
  simp

/-- `equivExtension K d` identifies the abstract universal derivation `D K (Level K d)` with the
continuous differential `d` in the level parameter `u`. -/
@[simp]
theorem equivExtension_D (g : Level K d) :
    equivExtension K d (Extension.ContinuousKaehlerDifferential.D K (Level K d) g) =
      ofForm (TauCeti.ContinuousKaehlerDifferential.D K (ringEquivLaurentSeries K d g)) := by
  have hder : (equivExtension K d).toLinearEquiv.toLinearMap.compDer
      (Extension.ContinuousKaehlerDifferential.D K (Level K d)) = levelDerivation K d := by
    refine Derivation.eq_of_formallyUnramified (S := K⸨X⸩) fun f ↦ ?_
    apply (addEquivContinuousKaehlerDifferential K d).injective
    simp [← Extension.ContinuousKaehlerDifferential.map_D]
  exact congr($hder g)

/-- `equivExtension K d` intertwines the intrinsic differential trace with the explicit level
differential trace. -/
@[simp]
theorem trace_equivExtension (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    Level.ContinuousKaehlerDifferential.trace K d (equivExtension K d ω) =
      Extension.ContinuousKaehlerDifferential.trace K (Level K d) ω := by
  obtain ⟨η, rfl⟩ :=
    (Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d)).surjective ω
  rw [equivExtension_tensorEquiv, Extension.ContinuousKaehlerDifferential.trace_tensorEquiv]
  induction η using TensorProduct.inductionOn with
  | tmul g ξ => simp
  | add η₁ η₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- **Tate's residue formula on a separable ramified level.** For every continuous one-form `ω` on
`Level K d`, its intrinsic residue `Res_{Level K d}(ω)` equals the coefficient of `u⁻¹` when `ω` is
written as `g du` in the level parameter `u`. -/
theorem residue_eq_coeff_equivExtension
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    Extension.ContinuousKaehlerDifferential.residue K (Level K d) ω =
      (ringEquivLaurentSeries K d (equivLevel K d (equivExtension K d ω))).coeff (-1) := by
  rw [Extension.ContinuousKaehlerDifferential.residue_apply, ← trace_equivExtension,
    TauCeti.ContinuousKaehlerDifferential.residue_apply, coeff_neg_one_equivLaurentSeries_trace]

/-- Under divisibility `h : d ∣ m` between separable ramified levels, `equivExtension` intertwines
étale pullback along `Level.transition K h` with the explicit substitution transition map on level
one-forms. -/
@[simp]
theorem equivExtension_pullback_transition {m : ℕ+} [NeZero ((m : ℕ) : K)] (h : d ∣ m)
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    equivExtension K m
        (Extension.ContinuousKaehlerDifferential.pullback (Level.transition K h) ω) =
      Level.ContinuousKaehlerDifferential.transition K h (equivExtension K d ω) := by
  obtain ⟨η, rfl⟩ :=
    (Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d)).surjective ω
  rw [equivExtension_tensorEquiv]
  induction η using TensorProduct.inductionOn with
  | tmul g ξ =>
    rw [Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul,
      Extension.ContinuousKaehlerDifferential.pullback_smul,
      Extension.ContinuousKaehlerDifferential.pullback_map, map_smul, equivExtension_map,
      Level.ContinuousKaehlerDifferential.tensorEquiv_tmul, map_smulₛₗ, transition_map]
    rfl
  | add η₁ η₂ ih₁ ih₂ => rw [map_add, map_add, map_add, map_add, map_add, ih₁, ih₂]

/-- **Residue scaling along level transitions:** for `d ∣ m` between separable ramified levels,
pulling back a continuous one-form from level `d` to level `m` multiplies its residue by `m / d`. -/
theorem residue_pullback_transition {m : ℕ+} [NeZero ((m : ℕ) : K)] (h : d ∣ m)
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    Extension.ContinuousKaehlerDifferential.residue K (Level K m)
        (Extension.ContinuousKaehlerDifferential.pullback (Level.transition K h) ω) =
      ((m : ℕ) / d) • Extension.ContinuousKaehlerDifferential.residue K (Level K d) ω := by
  rw [residue_eq_coeff_equivExtension, equivExtension_pullback_transition, coeff_neg_one_transition,
    ← residue_eq_coeff_equivExtension]

end ContinuousKaehlerDifferential

variable {K d}

/-- **Explicit formula for `d/dt` on a separable ramified level:** in the level variable `u` with
`t = u ^ d`, `d/dt (g) = (dg/du) / (d u ^ (d - 1))`. -/
theorem ringEquivLaurentSeries_derivation (g : Level K d) :
    ringEquivLaurentSeries K d (Extension.derivation K (Level K d) g) =
      _root_.LaurentSeries.derivative K (ringEquivLaurentSeries K d g) /
        _root_.LaurentSeries.derivative K (single (d : ℤ) 1) := by
  have hd : _root_.LaurentSeries.derivative K (single (d : ℤ) (1 : K)) ≠ 0 := by
    simp [NeZero.ne ((d : ℕ) : K)]
  have h := congrArg (fun ω ↦ ringEquivLaurentSeries K d
    (ContinuousKaehlerDifferential.equivLevel K d ω))
      (ContinuousKaehlerDifferential.equivExtension_D (K := K) (d := d) g)
  rw [ContinuousKaehlerDifferential.equivLevel_equivExtension,
    Extension.ContinuousKaehlerDifferential.equivSelf_D, map_mul, RingEquiv.apply_symm_apply,
    ContinuousKaehlerDifferential.ringEquivLaurentSeries_equivLevel,
    ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential_ofForm,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D] at h
  exact eq_div_of_mul_eq hd h

/-- Compatibility with `Level.residue`: the intrinsic residue of `x dt` on `Level K d` is
`Level.residue K d x`. -/
theorem residue_equivSelf_symm_eq_residue (x : Level K d) :
    Extension.ContinuousKaehlerDifferential.residue K (Level K d)
        ((Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d)).symm x) =
      Level.residue K d x := by
  rw [Extension.ContinuousKaehlerDifferential.residue_equivSelf_symm, coeff_neg_one_trace,
    ← residue_apply]

/-- **Comparison with the rational-exponent Puiseux residue:** on a separable ramified level
`Level K d`, `Res_F(Tr_{Level K d / F} ω) = Res_{Level K d}(ω) = d • Res_t^ℚ(ω)`, where `ω` is
embedded into the Puiseux field via its `dt`-coordinate `equivSelf`. -/
theorem residue_eq_nsmul_puiseuxField_residue
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    Extension.ContinuousKaehlerDifferential.residue K (Level K d) ω =
      (d : ℕ) • puiseuxField.residue K
        (toPuiseux K d (Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d) ω)) := by
  conv_lhs =>
    rw [← (Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d)).symm_apply_apply ω]
  rw [residue_equivSelf_symm_eq_residue, residue_eq_nsmul_residue_toPuiseux]

omit [NeZero ((d : ℕ) : K)] in
/-- Over an algebraically closed field of characteristic zero, the intrinsic residue of `x dt` on
any finite extension `L` of `K⸨X⸩` of degree `d` agrees with `Level.residueOfFinrankEq`. -/
theorem residue_equivSelf_symm_eq_residueOfFinrankEq [IsAlgClosed K] [CharZero K]
    {L : Type*} [Field L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
    [Algebra.FormallyEtale K⸨X⸩ L] (h : Module.finrank K⸨X⸩ L = d) (x : L) :
    Extension.ContinuousKaehlerDifferential.residue K L
        ((Extension.ContinuousKaehlerDifferential.equivSelf K L).symm x) =
      Level.residueOfFinrankEq h x := by
  rw [Extension.ContinuousKaehlerDifferential.residue_equivSelf_symm,
    residueOfFinrankEq_eq_coeff_neg_one_trace]

end SeparableLevel

end TauCeti.LaurentSeries.Level

namespace AlgEquiv

open TauCeti TauCeti.ContinuousKaehlerDifferential
open TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential

section ScalarExtensionChart

variable {K : Type*} [Field K] {L : Type*} [CommRing L] [Algebra K⸨X⸩ L]
  {d : ℕ+} [NeZero ((d : ℕ) : K)]

/-- A level chart identifies scalar-extended forms with the continuous forms of that
level. This is an equivalence over the base Laurent field; scalar multiplication by
`x : L` corresponds to multiplication by `e x` on the target. -/
noncomputable def laurentDifferentialTensorEquiv (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d) :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K ≃ₗ[K⸨X⸩]
      TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential K d :=
  (TensorProduct.congr e.toLinearEquiv (.refl K⸨X⸩ _)).trans
    ((TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.tensorEquiv K d).restrictScalars
      K⸨X⸩)

@[simp]
theorem laurentDifferentialTensorEquiv_tmul (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (x : L) (ω : ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv (x ⊗ₜ ω) =
      e x • TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.map K d ω := by
  simp [laurentDifferentialTensorEquiv]

/-- The inverse chart comparison sends a scalar multiple of a pulled-back form to
its corresponding pure tensor. -/
@[simp]
theorem laurentDifferentialTensorEquiv_symm_smul_map
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (x : TauCeti.LaurentSeries.Level K d) (ω : ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv.symm
        (x • TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.map K d ω) =
      e.symm x ⊗ₜ ω := by
  apply e.laurentDifferentialTensorEquiv.symm_apply_eq.mpr
  simp

/-- The chart comparison respects the extension's scalar action through the chart. -/
theorem laurentDifferentialTensorEquiv_smul
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (x : L) (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv (x • η) = e x • e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul y ω => simp [smul_tmul', smul_eq_mul, mul_smul]
  | add η θ hη hθ => simp [smul_add, hη, hθ]

/-- Differential trace commutes with every level chart. In particular the trace
transported from the explicit level is the trace on the first tensor factor. -/
@[simp]
theorem trace_laurentDifferentialTensorEquiv
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.trace K d
        (e.laurentDifferentialTensorEquiv η) = traceBaseChange L η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    simp only [laurentDifferentialTensorEquiv_tmul,
      TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.trace_smul_map,
      traceBaseChange_tmul]
    rw [Algebra.trace_eq_of_algEquiv e]
  | add η θ hη hθ => simp [hη, hθ]

/-- **Trace-residue compatibility in any level chart.** The residue of the trace
of a scalar-extended form is the coefficient residue in the level parameter. -/
theorem residueBaseChange_eq_coeff (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    residueBaseChange L η =
      (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K d
        (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K d
          (e.laurentDifferentialTensorEquiv η))).coeff (-1) := by
  rw [residueBaseChange_apply, ← trace_laurentDifferentialTensorEquiv e]
  exact coeff_neg_one_equivLaurentSeries_trace _

/-- **Independence of the level chart.** Two isomorphisms with ramified levels give
the same coefficient residue on scalar-extended forms. The levels need not be
identified in advance. -/
theorem coeff_laurentDifferentialTensorEquiv_eq {n : ℕ+} [NeZero ((n : ℕ) : K)]
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (e' : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K n)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K d
      (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K d
        (e.laurentDifferentialTensorEquiv η))).coeff (-1) =
    (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K n
      (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K n
        (e'.laurentDifferentialTensorEquiv η))).coeff (-1) := by
  rw [← residueBaseChange_eq_coeff e, ← residueBaseChange_eq_coeff e']

end ScalarExtensionChart

section IntrinsicChart

variable {K : Type*} [Field K] {L : Type*} [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]
  {d : ℕ+} [NeZero ((d : ℕ) : K)]

/-- **Intrinsic level chart on continuous one-forms.** A `K⸨X⸩`-algebra isomorphism
`e : L ≃ₐ[K⸨X⸩] Level K d` identifies `Ω¹_cont(L/K)` with the continuous one-forms of level `d`,
compatibly with `e`-scalar multiplication, universal derivations, traces, and residues. -/
noncomputable def laurentContinuousDifferentialEquiv
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d) :
    TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential K L ≃ₗ[K⸨X⸩]
      TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential K d :=
  (TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.pullbackEquiv e).trans
    ((TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivExtension K
      d).toLinearEquiv.restrictScalars K⸨X⸩)

/-- When `L` carries the `K⸨X⸩`-module topology, `e.laurentContinuousDifferentialEquiv` upgrades to
a continuous `K⸨X⸩`-linear equivalence. -/
noncomputable def laurentContinuousDifferentialContinuousEquiv
    [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d) :
    TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential K L ≃L[K⸨X⸩]
      TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential K d := by
  have : Module.Finite K⸨X⸩ L := Module.Finite.equiv e.symm.toLinearEquiv
  exact e.laurentContinuousDifferentialEquiv.toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem coe_laurentContinuousDifferentialContinuousEquiv
    [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d) :
    ⇑e.laurentContinuousDifferentialContinuousEquiv = e.laurentContinuousDifferentialEquiv := by
  have : Module.Finite K⸨X⸩ L := Module.Finite.equiv e.symm.toLinearEquiv
  simp [laurentContinuousDifferentialContinuousEquiv]

theorem laurentContinuousDifferentialEquiv_smul
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d) (x : L)
    (ω : TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential K L) :
    e.laurentContinuousDifferentialEquiv (x • ω) =
      e x • e.laurentContinuousDifferentialEquiv ω := by
  simp [laurentContinuousDifferentialEquiv]

@[simp]
theorem laurentContinuousDifferentialEquiv_D
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d) (x : L) :
    e.laurentContinuousDifferentialEquiv
        (TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.D K L x) =
      ofForm (TauCeti.ContinuousKaehlerDifferential.D K
        (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K d (e x))) := by
  simp [laurentContinuousDifferentialEquiv]

/-- `e.laurentContinuousDifferentialEquiv` agrees with `e.laurentDifferentialTensorEquiv` along the
scalar-extension presentation `L ⊗_{K⸨X⸩} Ω¹_cont(K⸨X⸩/K) ≃ Ω¹_cont(L/K)`. -/
@[simp]
theorem laurentContinuousDifferentialEquiv_tensorEquiv
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    e.laurentContinuousDifferentialEquiv
        (TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.tensorEquiv K L η) =
      e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    simp [laurentContinuousDifferentialEquiv]
  | add η₁ η₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- Every separable level chart intertwines the intrinsic differential trace with the level's
differential trace. -/
@[simp]
theorem trace_laurentContinuousDifferentialEquiv
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (ω : TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential K L) :
    TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.trace K d
        (e.laurentContinuousDifferentialEquiv ω) =
      TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.trace K L ω := by
  simp [laurentContinuousDifferentialEquiv]

/-- **Chart computation of the intrinsic residue.** In any separable level chart
`e : L ≃ₐ[K⸨X⸩] Level K d`, the intrinsic residue `Res_L(ω)` is the coefficient of `u⁻¹` when
`ω` is written in the level parameter `u`. -/
theorem residue_eq_coeff_laurentContinuousDifferentialEquiv
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (ω : TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential K L) :
    TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.residue K L ω =
      (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K d
        (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K d
          (e.laurentContinuousDifferentialEquiv ω))).coeff (-1) := by
  rw [← TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.residue_pullbackEquiv e,
    residue_eq_coeff_equivExtension]
  rfl

end IntrinsicChart

end AlgEquiv
