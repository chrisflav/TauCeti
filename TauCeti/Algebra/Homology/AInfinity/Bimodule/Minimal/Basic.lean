/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Cohomology

/-!
# Minimal A-infinity bimodules

An `(A, B)` `A∞` bimodule is **minimal** when its unary differential `m_{0,0}` vanishes
(`TauCeti.AInfinityBimodule.IsMinimal`).  Every element of a minimal bimodule is then a cycle and
no nonzero element is a boundary, so the bimodule is canonically linearly equivalent to its unary
cohomology (`TauCeti.AInfinityBimodule.IsMinimal.cohomologyEquiv`).  Between minimal bimodules, the
map induced on cohomology by a morphism of `A∞` bimodules is its linear part.  Consequently a
quasi-isomorphism between minimal bimodules is an isomorphism of `A∞` bimodules
(`TauCeti.AInfinityBimoduleHom.IsQuasiIso.isIso`, proved for vanishing unary differentials in
`TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Iso`).  Everything in this file holds over an
arbitrary commutative ring; minimal models over a field are constructed in
`TauCeti.Algebra.Homology.AInfinity.Bimodule.Minimal.Model`.

The right-module counterpart is `TauCeti.AInfinityRightModule.IsMinimal` in
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Minimal.Basic`.

## Main definitions

* `TauCeti.AInfinityBimodule.IsMinimal`: an `A∞` bimodule with zero unary differential.
* `TauCeti.AInfinityBimodule.IsMinimal.cohomologyEquiv`: the linear equivalence between a minimal
  bimodule and its unary cohomology.

## Main results

* `TauCeti.AInfinityBimodule.isMinimal_iff_ker_eq_top` and
  `TauCeti.AInfinityBimodule.isMinimal_iff_range_eq_bot`: minimality in terms of the kernel and
  range of the unary differential.
* `TauCeti.AInfinityBimoduleHom.cohomologyMap_cohomologyEquiv`: between minimal bimodules, the map
  induced on cohomology is the linear part.

## References

* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

namespace TauCeti

universe uR uA uB uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

namespace AInfinityBimodule

/-- An `(A, B)` `A∞` bimodule is **minimal** when its unary differential `m_{0,0}` vanishes. -/
def IsMinimal (MM : AInfinityBimodule AA BB M) : Prop :=
  MM.differential = 0

/-- An `A∞` bimodule is minimal exactly when its unary differential vanishes. -/
theorem isMinimal_def (MM : AInfinityBimodule AA BB M) :
    MM.IsMinimal ↔ MM.differential = 0 :=
  Iff.rfl

/-- An `A∞` bimodule is minimal exactly when every element is a cycle for the unary differential. -/
theorem isMinimal_iff_ker_eq_top (MM : AInfinityBimodule AA BB M) :
    MM.IsMinimal ↔ LinearMap.ker MM.differential = ⊤ := by
  rw [isMinimal_def, LinearMap.ker_eq_top]

/-- An `A∞` bimodule is minimal exactly when zero is its only unary boundary. -/
theorem isMinimal_iff_range_eq_bot (MM : AInfinityBimodule AA BB M) :
    MM.IsMinimal ↔ LinearMap.range MM.differential = ⊥ := by
  rw [isMinimal_def, LinearMap.range_eq_bot]

namespace IsMinimal

variable {MM : AInfinityBimodule AA BB M}

/-- Every element of a minimal bimodule lies in the kernel of its unary differential. -/
theorem mem_ker (h : MM.IsMinimal) (x : M) : x ∈ LinearMap.ker MM.differential := by
  rw [(isMinimal_iff_ker_eq_top MM).1 h]
  exact Submodule.mem_top

/-- In a minimal bimodule, the submodule of boundaries inside the cycles is trivial. -/
theorem boundariesInKer_eq_bot (h : MM.IsMinimal) : MM.differential.boundariesInKer = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_boundariesInKer, (isMinimal_iff_range_eq_bot MM).1 h, Submodule.mem_bot] at hx
  exact Subtype.ext hx

/-- A minimal bimodule is linearly equivalent to its unary cohomology: every element is a cycle,
and no nonzero element is a boundary. -/
noncomputable def cohomologyEquiv (h : MM.IsMinimal) : M ≃ₗ[R] MM.Cohomology :=
  (LinearEquiv.ofTop (LinearMap.ker MM.differential) ((isMinimal_iff_ker_eq_top MM).1 h)).symm ≪≫ₗ
    (Submodule.quotEquivOfEqBot _ h.boundariesInKer_eq_bot).symm

/-- Defining presentation of `cohomologyEquiv` as the composition of `LinearEquiv.ofTop.symm` and
`Submodule.quotEquivOfEqBot.symm`. -/
theorem cohomologyEquiv_def (h : MM.IsMinimal) :
    h.cohomologyEquiv =
      (LinearEquiv.ofTop (LinearMap.ker MM.differential)
        ((isMinimal_iff_ker_eq_top MM).1 h)).symm ≪≫ₗ
        (Submodule.quotEquivOfEqBot _ h.boundariesInKer_eq_bot).symm :=
  (rfl)

/-- The identification of a minimal bimodule with its cohomology sends an element to its class. -/
@[simp]
theorem cohomologyEquiv_apply (h : MM.IsMinimal) (x : M) :
    h.cohomologyEquiv x =
      MM.differential.homologyπ MM.differential_comp_self_eq_zero ⟨x, h.mem_ker x⟩ := by
  rw [cohomologyEquiv_def, LinearEquiv.trans_apply, LinearEquiv.ofTop_symm_apply,
    Submodule.quotEquivOfEqBot_symm_apply, LinearMap.homologyπ_apply]

/-- The inverse identification sends the quotient class of a cycle to the underlying element. -/
@[simp]
theorem cohomologyEquiv_symm_mk (h : MM.IsMinimal) (z : LinearMap.ker MM.differential) :
    h.cohomologyEquiv.symm (Submodule.Quotient.mk z) = z := by
  apply h.cohomologyEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cohomologyEquiv_apply, LinearMap.homologyπ_apply]

/-- The inverse identification sends the cohomology class of a cycle to the underlying element. -/
theorem cohomologyEquiv_symm_homologyπ (h : MM.IsMinimal) (z : LinearMap.ker MM.differential) :
    h.cohomologyEquiv.symm (MM.differential.homologyπ MM.differential_comp_self_eq_zero z) = z := by
  rw [LinearMap.homologyπ_apply, h.cohomologyEquiv_symm_mk]

end IsMinimal

end AInfinityBimodule

namespace AInfinityBimoduleHom

variable {MM : AInfinityBimodule AA BB M} {NN : AInfinityBimodule AA BB N}

/-- Between minimal bimodules, the map induced on unary cohomology is the linear part, transported
along the identifications of the bimodules with their cohomology. -/
theorem cohomologyMap_cohomologyEquiv (hM : MM.IsMinimal) (hN : NN.IsMinimal)
    (f : AInfinityBimoduleHom MM NN) (x : M) :
    f.cohomologyMap (hM.cohomologyEquiv x) = hN.cohomologyEquiv (f.linearPart x) := by
  simp only [AInfinityBimodule.IsMinimal.cohomologyEquiv_apply, LinearMap.homologyπ_apply,
    cohomologyMap_mk]

end AInfinityBimoduleHom

end TauCeti
