/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.TwistingCochain

/-!
# The canonical augmentation of the cobar construction

For any noncounital differential graded coalgebra `(C, Δ, d)`, the zero map `C →ₗ[R] R` is a
twisting cochain into the ground ring `R` concentrated in degree zero with zero differential
(`TauCeti.isTwistingCochain_zero`).  By the cobar universal property
(`TauCeti.IsNonCounitalDGCoalgebra.cobarLift`), it extends uniquely to a DG algebra augmentation

`ε_Ω : Ω C ⟶ R`

(`TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation`) sending every desuspended generator
`ι R c` to `0` and every scalar to itself.

Moreover, the cobar universal property restricts to augmented morphisms: DG algebra maps
`φ : Ω C ⟶ A` commuting with an augmentation `eA` of `A` correspond bijectively to twisting
cochains `τ : C ⟶ A` whose values lie in the augmentation ideal `ker eA`
(`TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentedTwistingCochainEquiv`).

## Main definitions

* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation`: the canonical augmentation of `Ω C`.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentedTwistingCochainEquiv`: the augmented cobar
  universal property.

## Main results

* `TauCeti.isTwistingCochain_zero`: the zero linear map is a twisting cochain into any graded
  algebra.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation_ι`: the canonical augmentation annihilates
  every generator `ι R c`.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarAugmentation_tprod_of_pos`: the canonical augmentation
  annihilates every pure tensor of positive length.
* `TauCeti.IsNonCounitalDGCoalgebra.comp_eq_cobarAugmentation_iff`: a DG algebra map `Ω C ⟶ A`
  preserves augmentations if and only if it maps every generator into the augmentation ideal.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, for the augmentation of the cobar construction.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
-/

public section

open TensorProduct TensorAlgebra

namespace TauCeti

universe uR uC uA

variable {R : Type uR} {C : Type uC} [CommRing R] [AddCommGroup C] [Module R C]
  {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {dC : C →ₗ[R] C}

/-- The zero linear map into any graded algebra is a twisting cochain. -/
theorem isTwistingCochain_zero {A : Type uA} [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} {dA : A →ₗ[R] A} :
    IsTwistingCochain G Δ dC 𝒜 dA 0 where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ _ ↦ zero_mem _
  equation c := by
    simp [TensorProduct.map_zero_right]

namespace IsNonCounitalDGCoalgebra

variable (hC : IsNonCounitalDGCoalgebra G Δ dC)

/-- The canonical augmentation `Ω C ⟶ R` of the cobar construction, sending every generator `ι R c`
to `0`. -/
noncomputable def cobarAugmentation : DGAlgAugmentation hC.isDGAlgebra_cobarDifferential :=
  hC.cobarLift (isDGAlgebra_trivialGrading R) 0 isTwistingCochain_zero

/-- The canonical augmentation of the cobar construction annihilates every generator. -/
@[simp]
theorem cobarAugmentation_ι (c : C) : hC.cobarAugmentation (ι R c) = 0 := by
  simp [cobarAugmentation]

/-- Every generator of the cobar construction lies in its augmentation ideal. -/
theorem ι_mem_cobarAugmentationIdeal (c : C) :
    ι R c ∈ hC.cobarAugmentation.augmentationIdeal := by
  simp

/-- The canonical augmentation of the cobar construction annihilates every pure tensor of positive
length. -/
theorem cobarAugmentation_tprod_of_pos {n : ℕ} (hn : 0 < n) (x : Fin n → C) :
    hC.cobarAugmentation (tprod R C n x) = 0 := by
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ m =>
    simp [tprod_apply, List.ofFn_succ]

variable {A : Type uA} [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA}

/-- A DG algebra map `Ω C ⟶ A` preserves augmentations if and only if it maps every generator into
the augmentation ideal of `A`. -/
theorem comp_eq_cobarAugmentation_iff (eA : DGAlgAugmentation hA)
    (φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA) :
    eA.comp φ = hC.cobarAugmentation ↔ ∀ c, eA (φ (ι R c)) = 0 := by
  constructor
  · intro h c
    have hc := congrArg (fun ψ : DGAlgAugmentation hC.isDGAlgebra_cobarDifferential ↦ ψ (ι R c)) h
    simpa using hc
  · intro h
    apply hC.cobarHom_ext (isDGAlgebra_trivialGrading R)
    intro c
    simpa using h c

/-- The cobar lift of a twisting cochain `τ` preserves augmentations if and only if `τ` takes
values in the augmentation ideal of `A`. -/
theorem comp_cobarLift_eq_cobarAugmentation_iff (eA : DGAlgAugmentation hA)
    (τ : C →ₗ[R] A) (hτ : IsTwistingCochain G Δ dC 𝒜 dA τ) :
    eA.comp (hC.cobarLift hA τ hτ) = hC.cobarAugmentation ↔ ∀ c, eA (τ c) = 0 := by
  rw [hC.comp_eq_cobarAugmentation_iff eA]
  simp

/-- **The augmented cobar universal property**: augmented DG algebra maps `Ω C ⟶ A` correspond
bijectively to twisting cochains `C ⟶ A` taking values in the augmentation ideal of `A`. -/
noncomputable def cobarAugmentedTwistingCochainEquiv (eA : DGAlgAugmentation hA) :
    {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA // eA.comp φ = hC.cobarAugmentation} ≃
      {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, eA (τ c) = 0} where
  toFun φ :=
    ⟨(hC.cobarTwistingCochainEquiv hA φ.1).1,
      (hC.cobarTwistingCochainEquiv hA φ.1).2,
      fun c ↦ by
        simp only [cobarTwistingCochainEquiv_apply, map_neg, neg_eq_zero]
        exact (hC.comp_eq_cobarAugmentation_iff eA φ.1).1 φ.2 c⟩
  invFun τ :=
    ⟨hC.cobarLift hA τ.1 τ.2.1,
      (hC.comp_cobarLift_eq_cobarAugmentation_iff eA τ.1 τ.2.1).2 τ.2.2⟩
  left_inv φ := Subtype.ext <| hC.cobarHom_ext hA fun c ↦ by simp
  right_inv τ := Subtype.ext <| by
    ext c
    simp

@[simp]
theorem cobarAugmentedTwistingCochainEquiv_apply (eA : DGAlgAugmentation hA)
    (φ : {φ : DGAlgHom hC.isDGAlgebra_cobarDifferential hA // eA.comp φ = hC.cobarAugmentation})
    (c : C) :
    (hC.cobarAugmentedTwistingCochainEquiv eA φ).val c = -φ.val (ι R c) :=
  hC.cobarTwistingCochainEquiv_apply hA φ.1 c

@[simp]
theorem cobarAugmentedTwistingCochainEquiv_symm_apply_ι (eA : DGAlgAugmentation hA)
    (τ : {τ : C →ₗ[R] A // IsTwistingCochain G Δ dC 𝒜 dA τ ∧ ∀ c, eA (τ c) = 0}) (c : C) :
    ((hC.cobarAugmentedTwistingCochainEquiv eA).symm τ).val (ι R c) = -τ.val c :=
  hC.cobarLift_ι hA τ.val τ.property.1 c

end IsNonCounitalDGCoalgebra

end TauCeti
