/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.FormallyEtale
public import TauCeti.RingTheory.Kaehler.Trace.Basic

/-!
# The trace of differentials along formally unramified and étale extensions

Let `k → R → B` be a tower of commutative rings with `B` finite free and formally unramified over
`R`, and let `D : R → R` be a `k`-derivation extending to a `k`-derivation `D' : B → B`. Both
Kunz's matrix trace derivation `a ↦ (c ↦ Tr_{B/R}(C · D(A)))` (`Derivation.traceDerivation`) and
the pairing `a ↦ (c ↦ Tr_{B/R}(c * D' a))` are `k`-derivations `B → Hom_R(B, R)` that agree on the
image of `R`. Since `B` is formally unramified over `R`, `Derivation.eq_of_formallyUnramified`
identifies them on all of `B`.

Consequently:

* `Derivation.traceDeriv_eq_trace_mul_of_formallyUnramified`: `Tr(C · D(A)) = Tr_{B/R}(c * D' a)`.
* `Derivation.trace_apply_eq_of_formallyUnramified`: `Tr_{B/R}(D' a) = D(Tr_{B/R} a)`, so
  `Algebra.trace R B` commutes with extended derivations in every characteristic.
* `Derivation.traceLin_eq_trace_comp_liftKaehlerDifferential`: Kunz's differential trace
  `Ω[B⁄k] → R` factors through `D'.liftKaehlerDifferential : Ω[B⁄k] → B` followed by
  `Algebra.trace R B`.

When `B` is formally étale over `R`, every `k`-derivation `D : R → R` extends automatically via
`Derivation.extendOfFormallyEtale`, yielding unconditional specializations.

## References

* E. Kunz, *Kähler Differentials*, Vieweg (1986), §16, for the matrix construction of the trace of
  differentials and its identification on étale extensions.
-/

public section

open Algebra TauCeti.Algebra

namespace Derivation

section Unramified

variable {k R B : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [Algebra k B] [IsScalarTower k R B] [Module.Free R B] [Module.Finite R B]

/-- Multiplication followed by `Algebra.trace R B` and an `R`-linear map `μ : R →ₗ[R] M`,
packaged as a `B`-linear map into `PrecompLinearMap R B M` (`y ↦ (c ↦ μ (Tr_{B/R}(c * y)))`). -/
private noncomputable def traceMulPrecomp {M : Type*} [AddCommGroup M] [Module R M]
    (μ : R →ₗ[R] M) : B →ₗ[B] PrecompLinearMap R B M where
  toFun y := PrecompLinearMap.ofLinearMap (μ ∘ₗ Algebra.trace R B ∘ₗ LinearMap.mulRight R y)
  map_add' x y := PrecompLinearMap.ext fun c ↦ by
    simp [PrecompLinearMap.ofLinearMap_apply, mul_add]
  map_smul' b y := PrecompLinearMap.ext fun c ↦ by
    simp [PrecompLinearMap.ofLinearMap_apply, PrecompLinearMap.smul_apply, smul_eq_mul, mul_assoc,
      mul_left_comm]

variable [Algebra.FormallyUnramified R B]

section ModuleValued

variable {M : Type*} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

private theorem traceDerivation_eq_map_of_formallyUnramified (D : Derivation k R M)
    (μ : R →ₗ[R] M) {d₀ : R → R} {D' : Derivation k B B}
    (hμ : ∀ r : R, D r = μ (d₀ r))
    (hD : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (d₀ r)) :
    traceDerivation (B := B) D = (traceMulPrecomp μ).compDer D' := by
  refine eq_of_formallyUnramified (S := R) fun r ↦ PrecompLinearMap.ext fun c ↦ ?_
  rw [traceDerivation_apply, traceDeriv_algebraMap, coe_comp, LinearMap.comp_apply, coeFn_coe,
    LinearMap.coe_restrictScalars, hμ, hD]
  simp only [traceMulPrecomp, LinearMap.coe_mk, AddHom.coe_mk, PrecompLinearMap.ofLinearMap_apply,
    LinearMap.comp_apply, LinearMap.mulRight_apply]
  rw [← μ.map_smul, smul_eq_mul, mul_comm (Algebra.trace R B c), ← smul_eq_mul,
    ← (Algebra.trace R B).map_smul, Algebra.smul_def, mul_comm (algebraMap R B (d₀ r))]

/-- **Module-valued formula for Kunz's trace derivation on a formally unramified extension.**
If `D : R → M` factors pointwise as `μ ∘ d₀` for an `R`-linear map `μ : R →ₗ[R] M` and `D' : B → B`
extends `d₀`, then `traceDeriv D a c = μ (Tr_{B/R}(c * D' a))`. -/
theorem traceDeriv_eq_map_trace_mul_of_formallyUnramified (D : Derivation k R M)
    (μ : R →ₗ[R] M) {d₀ : R → R} {D' : Derivation k B B}
    (hμ : ∀ r : R, D r = μ (d₀ r))
    (hD : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (d₀ r)) (a c : B) :
    traceDeriv D a c = μ (Algebra.trace R B (c * D' a)) := by
  have h := congrArg (fun δ : Derivation k B (PrecompLinearMap R B M) ↦ δ a c)
    (traceDerivation_eq_map_of_formallyUnramified D μ hμ hD)
  simpa [traceMulPrecomp, PrecompLinearMap.ofLinearMap_apply] using h

/-- If `D : R → M` factors pointwise as `μ ∘ d₀` and `D' : B → B` extends `d₀` on a finite free
formally unramified extension `B/R`, then `μ (Tr_{B/R}(D' a)) = D (Tr_{B/R} a)`. -/
theorem map_trace_apply_eq_of_formallyUnramified (D : Derivation k R M)
    (μ : R →ₗ[R] M) {d₀ : R → R} {D' : Derivation k B B}
    (hμ : ∀ r : R, D r = μ (d₀ r))
    (hD : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (d₀ r)) (a : B) :
    μ (Algebra.trace R B (D' a)) = D (Algebra.trace R B a) := by
  simpa only [traceDeriv_one_right, one_mul] using
    (traceDeriv_eq_map_trace_mul_of_formallyUnramified D μ hμ hD a 1).symm

/-- On a finite free formally unramified extension `B/R`, if `D : R → M` factors pointwise as
`μ ∘ d₀` and `D' : B → B` extends `d₀`, then
`traceLin D ω = μ (Tr_{B/R}(D'.liftKaehlerDifferential ω))`. -/
theorem traceLin_apply_eq_map_trace_liftKaehlerDifferential (D : Derivation k R M)
    (μ : R →ₗ[R] M) {d₀ : R → R} {D' : Derivation k B B}
    (hμ : ∀ r : R, D r = μ (d₀ r))
    (hD : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (d₀ r)) (ω : Ω[B⁄k]) :
    traceLin (B := B) D ω = μ (Algebra.trace R B (D'.liftKaehlerDifferential ω)) := by
  suffices ∀ c : B, (traceDerivation (B := B) D).liftKaehlerDifferential ω c =
      μ (Algebra.trace R B (c * D'.liftKaehlerDifferential ω)) by
    simpa only [traceLin_apply, one_mul] using this 1
  have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    intro c
    rw [liftKaehlerDifferential_comp_D, liftKaehlerDifferential_comp_D, traceDerivation_apply,
      traceDeriv_eq_map_trace_mul_of_formallyUnramified D μ hμ hD]
  | zero => simp
  | add x y _ _ hx hy =>
    intro c
    simp only [map_add, PrecompLinearMap.add_apply, mul_add, hx, hy]
  | smul b x _ hx =>
    intro c
    rw [LinearMap.map_smul, LinearMap.map_smul, PrecompLinearMap.smul_apply, smul_eq_mul,
      smul_eq_mul, hx, mul_assoc, mul_left_comm]

end ModuleValued

/-- **Formula for Kunz's trace derivation on a formally unramified extension.** If `D' : B → B`
extends `D : R → R`, then `traceDeriv D a c = Tr_{B/R}(c * D' a)`. -/
theorem traceDeriv_eq_trace_mul_of_formallyUnramified (D : Derivation k R R)
    {D' : Derivation k B B} (hD : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (D r))
    (a c : B) :
    traceDeriv D a c = Algebra.trace R B (c * D' a) :=
  traceDeriv_eq_map_trace_mul_of_formallyUnramified D LinearMap.id (fun _ ↦ rfl) hD a c

/-- **Algebraic trace commutes with extended derivations.** For a finite free formally unramified
extension `B/R` and a `k`-derivation `D' : B → B` extending `D : R → R`,
`Tr_{B/R}(D' a) = D(Tr_{B/R} a)`. -/
theorem trace_apply_eq_of_formallyUnramified (D : Derivation k R R) {D' : Derivation k B B}
    (hD : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (D r)) (a : B) :
    Algebra.trace R B (D' a) = D (Algebra.trace R B a) :=
  map_trace_apply_eq_of_formallyUnramified D LinearMap.id (fun _ ↦ rfl) hD a

/-- Pointwise form of `Derivation.traceLin_eq_trace_comp_liftKaehlerDifferential`. -/
theorem traceLin_apply_eq_trace_liftKaehlerDifferential (D : Derivation k R R)
    {D' : Derivation k B B} (hD : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (D r))
    (ω : Ω[B⁄k]) :
    traceLin (B := B) D ω = Algebra.trace R B (D'.liftKaehlerDifferential ω) :=
  traceLin_apply_eq_map_trace_liftKaehlerDifferential D LinearMap.id (fun _ ↦ rfl) hD ω

/-- On a finite free formally unramified extension `B/R`, Kunz's differential trace
`traceLin D : Ω[B⁄k] →ₗ[R] R` factors as `D'.liftKaehlerDifferential` followed by
`Algebra.trace R B`. -/
theorem traceLin_eq_trace_comp_liftKaehlerDifferential (D : Derivation k R R)
    {D' : Derivation k B B} (hD : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (D r)) :
    traceLin (B := B) D = Algebra.trace R B ∘ₗ D'.liftKaehlerDifferential.restrictScalars R :=
  LinearMap.ext (traceLin_apply_eq_trace_liftKaehlerDifferential D hD)

end Unramified

section Etale

variable {k R B : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [Algebra k B] [IsScalarTower k R B] [Module.Free R B] [Module.Finite R B]
  [Algebra.FormallyEtale R B]

/-- For a finite free formally étale `R`-algebra `B`, `Algebra.trace R B` commutes with the
canonical extension of `D : R → R` to `B`. -/
@[simp]
theorem trace_extendOfFormallyEtale (D : Derivation k R R) (a : B) :
    Algebra.trace R B (((Algebra.linearMap R B).compDer D).extendOfFormallyEtale B a) =
      D (Algebra.trace R B a) :=
  trace_apply_eq_of_formallyUnramified D
    (fun r ↦ extendOfFormallyEtale_algebraMap ((Algebra.linearMap R B).compDer D) r) a

/-- For a finite free formally étale `R`-algebra `B`, Kunz's differential trace `traceLin D` is
the algebraic trace of the Kähler lift of the extended derivation. -/
theorem traceLin_eq_trace_liftKaehlerDifferential_extendOfFormallyEtale (D : Derivation k R R)
    (ω : Ω[B⁄k]) :
    traceLin (B := B) D ω =
      Algebra.trace R B
        ((((Algebra.linearMap R B).compDer D).extendOfFormallyEtale B).liftKaehlerDifferential ω) :=
  traceLin_apply_eq_trace_liftKaehlerDifferential D
    (fun r ↦ extendOfFormallyEtale_algebraMap ((Algebra.linearMap R B).compDer D) r) ω

end Etale

end Derivation
