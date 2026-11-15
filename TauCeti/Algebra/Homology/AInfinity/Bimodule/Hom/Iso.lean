/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Inverse
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Cohomology
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.BicofreeHom

/-!
# Isomorphisms of A-infinity bimodules

A morphism of `(A, B)` `A∞` bimodules over fixed algebras is an *isomorphism* when it has a
two-sided inverse bimodule morphism.  This happens precisely when its linear part `f₀,₀` is
bijective.  Indeed the bar map of a bimodule morphism is a morphism of cofree bicomodules
`(Tᶜ(sA) ⊗ sM) ⊗ Tᶜ(sB) ⟶ (Tᶜ(sA) ⊗ sN) ⊗ Tᶜ(sB)` whose restriction to the two empty words applies
the linear part `f₀,₀` and whose remaining summands strictly shorten total word length, so it is
bijective as soon as `f₀,₀` is (`TauCeti.Comodule.Hom.bijective_of_apply_one_tmul_tmul_one`).  Its
linear inverse is again compatible with both coactions, preserves suspended degree, and intertwines
the bar differentials; this gives the inverse bimodule morphism
`TauCeti.AInfinityBimoduleHom.inverse`, whose linear part is the inverse of `f₀,₀`.

Every isomorphism is a quasi-isomorphism.  Between bimodules with vanishing unary differential, the
converse holds: every element is a cycle and only zero is a boundary, so a quasi-isomorphism has
bijective linear part and is therefore an isomorphism.

The interface follows `TauCeti.AInfinityRightModuleHom` in
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Iso`.

## Main definitions

* `TauCeti.AInfinityBimoduleHom.barEquiv`: the bar map of a bimodule morphism with bijective linear
  part, as a linear equivalence.
* `TauCeti.AInfinityBimoduleHom.inverse`: the inverse of a bimodule morphism with bijective linear
  part.
* `TauCeti.AInfinityBimoduleHom.IsIso`: a bimodule morphism admitting a two-sided inverse.

## Main results

* `TauCeti.AInfinityBimoduleHom.inverse_comp_cancel`,
  `TauCeti.AInfinityBimoduleHom.comp_inverse_cancel`, and
  `TauCeti.AInfinityBimoduleHom.linearPart_inverse`: `inverse` is a two-sided inverse whose linear
  part is the inverse linear equivalence.
* `TauCeti.AInfinityBimoduleHom.isIso_iff_linearPart_bijective`: a bimodule morphism is an
  isomorphism exactly when its linear part is bijective.
* `TauCeti.AInfinityBimoduleHom.IsIso.isQuasiIso`: every isomorphism is a quasi-isomorphism.
* `TauCeti.AInfinityBimoduleHom.isQuasiIso_iff_isIso`: between bimodules with vanishing unary
  differential, quasi-isomorphisms are exactly the isomorphisms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

namespace AInfinityBimoduleHom

variable {MM : AInfinityBimodule AA BB M} {NN : AInfinityBimodule AA BB N}
  {PP : AInfinityBimodule AA BB P}

/-! ### The inverse of a morphism with bijective linear part -/

/-- The bar map of a bimodule morphism with bijective linear part is bijective. -/
theorem barMap_bijective_of_linearPart_bijective (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) : Function.Bijective f.barMap :=
  f.barHom.bijective_of_apply_one_tmul_tmul_one f.leftCoact_comp_barMap hf
    f.barMap_one_tmul_tmul_one

/-- The bar map of a bimodule morphism with bijective linear part, as a linear equivalence of
two-sided bar constructions. -/
noncomputable def barEquiv (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) ≃ₗ[R]
      ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) :=
  LinearEquiv.ofBijective f.barMap (f.barMap_bijective_of_linearPart_bijective hf)

/-- The defining presentation of `barEquiv` as `LinearEquiv.ofBijective` of the bar map. -/
theorem barEquiv_def (f : AInfinityBimoduleHom MM NN) (hf : Function.Bijective f.linearPart) :
    f.barEquiv hf =
      LinearEquiv.ofBijective f.barMap (f.barMap_bijective_of_linearPart_bijective hf) :=
  (rfl)

/-- The linear equivalence `barEquiv f hf` applies the bar map of `f`. -/
@[simp]
theorem barEquiv_apply (f : AInfinityBimoduleHom MM NN) (hf : Function.Bijective f.linearPart)
    (z : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :
    f.barEquiv hf z = f.barHom z :=
  (rfl)

/-- The inverse of `barEquiv f hf` undoes the bar map of `f`. -/
@[simp]
theorem barEquiv_symm_barMap (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart)
    (z : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) :
    (f.barEquiv hf).symm (f.barHom z) = z := by
  rw [← barEquiv_apply f hf, LinearEquiv.symm_apply_apply]

/-- The bar map of `f` undoes the inverse of `barEquiv f hf`. -/
@[simp]
theorem barMap_barEquiv_symm (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart)
    (w : (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) :
    f.barHom ((f.barEquiv hf).symm w) = w := by
  rw [← barEquiv_apply f hf, LinearEquiv.apply_symm_apply]

/-- The inverse of a bimodule morphism with bijective linear part: its bar map is the inverse of
the bar map, which again respects both coactions, preserves suspended degree, and intertwines the
bar differentials. -/
noncomputable def inverse (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) : AInfinityBimoduleHom NN MM where
  barHom := f.barHom.inverse (f.barMap_bijective_of_linearPart_bijective hf)
  leftCoact_comp_barMap := by
    rw [Comodule.Hom.inverse_toLinearMap, ← barEquiv_def f hf]
    exact Comodule.leftCoact_comp_of_comp_eq_id f.leftCoact_comp_barMap
      (LinearMap.ext (f.barEquiv_symm_barMap hf)) (LinearMap.ext (f.barMap_barEquiv_symm hf))
  isHomogeneous_barMap := by
    rw [Comodule.Hom.inverse_toLinearMap]
    exact LinearMap.IsHomogeneous.linearEquiv_symm f.isHomogeneous_barMap
  barDifferential_comp_barMap := by
    rw [Comodule.Hom.inverse_toLinearMap, ← barEquiv_def f hf]
    refine LinearMap.ext fun w ↦ ?_
    obtain ⟨z, rfl⟩ := (f.barEquiv hf).surjective w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, barEquiv_apply, barDifferential_barMap,
      barEquiv_symm_barMap]

/-- The bar map of the inverse is the inverse of the bar map. -/
@[simp]
theorem barMap_inverse (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).barMap = (f.barEquiv hf).symm.toLinearMap :=
  Comodule.Hom.inverse_toLinearMap _ _

/-- The inverse is a left inverse. -/
@[simp]
theorem inverse_comp_cancel (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).comp f = AInfinityBimoduleHom.id MM :=
  barMap_injective <| by
    rw [barMap_comp, barMap_id, barMap_inverse]
    exact LinearMap.ext (f.barEquiv_symm_barMap hf)

/-- The inverse is a right inverse. -/
@[simp]
theorem comp_inverse_cancel (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    f.comp (f.inverse hf) = AInfinityBimoduleHom.id NN :=
  barMap_injective <| by
    rw [barMap_comp, barMap_id, barMap_inverse]
    exact LinearMap.ext (f.barMap_barEquiv_symm hf)

/-- The linear part of the inverse is the inverse of the linear part. -/
@[simp]
theorem linearPart_inverse (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) :
    (f.inverse hf).linearPart = (LinearEquiv.ofBijective f.linearPart hf).symm.toLinearMap := by
  have h := congrArg linearPart (f.inverse_comp_cancel hf)
  rw [linearPart_comp, linearPart_id] at h
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hf.2 y
  rw [LinearEquiv.coe_coe, LinearEquiv.ofBijective_symm_apply_apply, ← LinearMap.comp_apply, h,
    LinearMap.id_apply]

/-- The linear part of the inverse is bijective. -/
theorem linearPart_inverse_bijective (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) : Function.Bijective (f.inverse hf).linearPart := by
  rw [linearPart_inverse]
  exact (LinearEquiv.ofBijective f.linearPart hf).symm.bijective

/-! ### Uniqueness and normal forms of the inverse -/

/-- A left inverse of a bimodule morphism with bijective linear part is its inverse. -/
theorem eq_inverse_of_comp_eq_id_left {f : AInfinityBimoduleHom MM NN}
    {g : AInfinityBimoduleHom NN MM} (hf : Function.Bijective f.linearPart)
    (h : g.comp f = AInfinityBimoduleHom.id MM) : g = f.inverse hf := by
  rw [← comp_id g, ← comp_inverse_cancel f hf, ← comp_assoc, h, id_comp]

/-- A right inverse of a bimodule morphism with bijective linear part is its inverse. -/
theorem eq_inverse_of_comp_eq_id_right {f : AInfinityBimoduleHom MM NN}
    {g : AInfinityBimoduleHom NN MM} (hf : Function.Bijective f.linearPart)
    (h : f.comp g = AInfinityBimoduleHom.id NN) : g = f.inverse hf := by
  rw [← id_comp g, ← inverse_comp_cancel f hf, comp_assoc, h, comp_id]

/-- The inverse of the identity is the identity. -/
@[simp]
theorem inverse_id (MM : AInfinityBimodule AA BB M)
    (h : Function.Bijective (AInfinityBimoduleHom.id MM).linearPart) :
    (AInfinityBimoduleHom.id MM).inverse h = AInfinityBimoduleHom.id MM :=
  (eq_inverse_of_comp_eq_id_left h (comp_id _)).symm

/-- The inverse of the inverse is the original morphism. -/
@[simp]
theorem inverse_inverse (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) (h : Function.Bijective (f.inverse hf).linearPart) :
    (f.inverse hf).inverse h = f :=
  (eq_inverse_of_comp_eq_id_left h (comp_inverse_cancel f hf)).symm

/-- The inverse of a composite is the composite of the inverses in the reverse order. -/
@[simp]
theorem inverse_comp (g : AInfinityBimoduleHom NN PP) (f : AInfinityBimoduleHom MM NN)
    (hg : Function.Bijective g.linearPart) (hf : Function.Bijective f.linearPart)
    (h : Function.Bijective (g.comp f).linearPart) :
    (g.comp f).inverse h = (f.inverse hf).comp (g.inverse hg) :=
  (eq_inverse_of_comp_eq_id_left h (by
    rw [comp_assoc, ← comp_assoc (g.inverse hg), inverse_comp_cancel, id_comp,
      inverse_comp_cancel])).symm

/-! ### Isomorphisms -/

/-- A morphism of `(A, B)` `A∞` bimodules is an **isomorphism** when it has a two-sided inverse
bimodule morphism. -/
def IsIso (f : AInfinityBimoduleHom MM NN) : Prop :=
  ∃ g : AInfinityBimoduleHom NN MM, g.comp f = AInfinityBimoduleHom.id MM ∧
    f.comp g = AInfinityBimoduleHom.id NN

/-- A bimodule morphism is an isomorphism exactly when it has a two-sided inverse. -/
theorem isIso_def (f : AInfinityBimoduleHom MM NN) :
    f.IsIso ↔ ∃ g : AInfinityBimoduleHom NN MM, g.comp f = AInfinityBimoduleHom.id MM ∧
      f.comp g = AInfinityBimoduleHom.id NN :=
  Iff.rfl

/-- The identity bimodule morphism is an isomorphism. -/
@[simp]
theorem isIso_id (MM : AInfinityBimodule AA BB M) : (AInfinityBimoduleHom.id MM).IsIso :=
  ⟨AInfinityBimoduleHom.id MM, comp_id _, comp_id _⟩

/-- Isomorphisms of `A∞` bimodules are closed under composition. -/
theorem IsIso.comp {g : AInfinityBimoduleHom NN PP} {f : AInfinityBimoduleHom MM NN}
    (hg : g.IsIso) (hf : f.IsIso) : (g.comp f).IsIso := by
  obtain ⟨g', hg₁, hg₂⟩ := hg
  obtain ⟨f', hf₁, hf₂⟩ := hf
  refine ⟨f'.comp g', ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc g', hg₁, id_comp, hf₁]
  · rw [comp_assoc, ← comp_assoc f, hf₂, id_comp, hg₂]

/-- A bimodule morphism with bijective linear part is an isomorphism. -/
theorem isIso_of_linearPart_bijective (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) : f.IsIso :=
  ⟨f.inverse hf, f.inverse_comp_cancel hf, f.comp_inverse_cancel hf⟩

/-- The inverse of a bimodule morphism with bijective linear part is an isomorphism. -/
theorem isIso_inverse (f : AInfinityBimoduleHom MM NN)
    (hf : Function.Bijective f.linearPart) : (f.inverse hf).IsIso :=
  ⟨f, f.comp_inverse_cancel hf, f.inverse_comp_cancel hf⟩

/-- The linear part of an isomorphism is bijective. -/
theorem IsIso.linearPart_bijective {f : AInfinityBimoduleHom MM NN} (h : f.IsIso) :
    Function.Bijective f.linearPart := by
  obtain ⟨g, hg₁, hg₂⟩ := h
  refine Function.bijective_iff_has_inverse.2 ⟨g.linearPart, fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [← LinearMap.comp_apply, ← linearPart_comp, hg₁, linearPart_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← linearPart_comp, hg₂, linearPart_id, LinearMap.id_apply]

/-- A bimodule morphism is an isomorphism exactly when its linear part is bijective. -/
theorem isIso_iff_linearPart_bijective (f : AInfinityBimoduleHom MM NN) :
    f.IsIso ↔ Function.Bijective f.linearPart :=
  ⟨IsIso.linearPart_bijective, f.isIso_of_linearPart_bijective⟩

/-- An isomorphism of `A∞` bimodules is a quasi-isomorphism. -/
theorem IsIso.isQuasiIso {f : AInfinityBimoduleHom MM NN} (h : f.IsIso) : f.IsQuasiIso := by
  obtain ⟨g, hg₁, hg₂⟩ := h
  rw [isQuasiIso_def]
  refine Function.bijective_iff_has_inverse.2 ⟨g.cohomologyMap, fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hg₁, cohomologyMap_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← cohomologyMap_comp, hg₂, cohomologyMap_id, LinearMap.id_apply]

/-! ### Bimodules with vanishing unary differential -/

/-- Between `A∞` bimodules with vanishing unary differential, a bimodule morphism is a
quasi-isomorphism exactly when its linear part is bijective. -/
theorem isQuasiIso_iff_linearPart_bijective (hM : MM.differential = 0)
    (hN : NN.differential = 0) (f : AInfinityBimoduleHom MM NN) :
    f.IsQuasiIso ↔ Function.Bijective f.linearPart := by
  rw [isQuasiIso_iff, Function.Bijective, injective_iff_map_eq_zero, Function.Surjective]
  simp only [hM, hN, LinearMap.ker_zero, LinearMap.range_zero, Submodule.mem_top,
    Submodule.mem_bot, forall_true_left, true_and, sub_eq_zero]
  exact and_congr_right' (forall_congr' fun _ ↦ exists_congr fun _ ↦ eq_comm)

/-- Between `A∞` bimodules with vanishing unary differential, quasi-isomorphisms are exactly the
isomorphisms. -/
theorem isQuasiIso_iff_isIso (hM : MM.differential = 0) (hN : NN.differential = 0)
    (f : AInfinityBimoduleHom MM NN) : f.IsQuasiIso ↔ f.IsIso := by
  rw [isQuasiIso_iff_linearPart_bijective hM hN, isIso_iff_linearPart_bijective]

/-- A quasi-isomorphism between `A∞` bimodules with vanishing unary differential is an
isomorphism. -/
theorem IsQuasiIso.isIso (hM : MM.differential = 0) (hN : NN.differential = 0)
    {f : AInfinityBimoduleHom MM NN} (hf : f.IsQuasiIso) : f.IsIso :=
  (isQuasiIso_iff_isIso hM hN f).1 hf

end AInfinityBimoduleHom

end TauCeti
