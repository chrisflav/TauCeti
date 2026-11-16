/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.UnitaryDual
public import TauCeti.CategoryTheory.Monoidal.Pivotal.FrobeniusSchur.Simple
public import TauCeti.CategoryTheory.Preadditive.Schur
import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# Signed self-dualities, second Frobenius–Schur indicators, and braided tensor products

In a preadditive right rigid dagger monoidal category with a unitary dual functor, a *signed
self-duality* of an object `X` with sign `ε : ℤˣ` (`±1`) is a unitary morphism `r : X ⟶ Xᘁ`
satisfying `r ≫ dualConj r = (ε : ℤ) • (unitaryDualPivotalIsoApp X).hom`, where
`dualConj r = dagger (rᘁ)` is the covariant conjugate and `unitaryDualPivotalIsoApp X : X ≅ Xᘁᘁ`
is the canonical unitary pivotal isomorphism `φ_X`.

For a unitary `r : X ⟶ Xᘁ`, this condition is equivalent to:
* `r = (ε : ℤ) • ((unitaryDualPivotalIsoApp X).hom ≫ rᘁ)`, equivalently
  `r = (ε : ℤ) • ((unitaryDualPivotalIsoApp X).hom ≫ dagger (dualConj r))`;
* the Ng–Schauenburg eigenvector equation
  `(dagger r)ᘁ ≫ (unitaryDualPivotalIsoApp X).inv = (ε : ℤ) • dagger r`;
* the symmetric-evaluation equation
  `r ▷ X ≫ ε_ X Xᘁ = (ε : ℤ) • (((unitaryDualPivotalIsoApp X).hom ⊗ₘ r) ≫ ε_ Xᘁ Xᘁᘁ)`;
* the cup equation
  `η_ X Xᘁ ≫ X ◁ dagger r =
    (ε : ℤ) • (η_ Xᘁ Xᘁᘁ ≫ (dagger r ⊗ₘ (unitaryDualPivotalIsoApp X).inv))`;
* the dagger cup–cap relation
  `dagger (η_ X Xᘁ ≫ X ◁ dagger r) = (ε : ℤ) • (r ▷ X ≫ ε_ X Xᘁ)`.

Signed self-dualities transport along arbitrary unitary morphisms `u : X ⟶ Y` via
`dagger u ≫ r ≫ dualConj u`, preserving the sign `ε`. Whenever two signed self-dualities of `X`
differ by a scalar endomorphism (for instance on a simple object over an algebraically closed
field), their signs agree provided `(2 : ℤ) • 𝟙 X ≠ 0`.

In any pivotal category, Frobenius reciprocity `TauCeti.homTensorPowTwoLinearEquiv` intertwines the
second Frobenius–Schur rotation `E_X^{(2)}` with the map `g ↦ gᘁ ≫ (pivotalIsoApp X).inv` on
`Xᘁ ⟶ X` (`TauCeti.homTensorPowTwoLinearEquiv_frobeniusSchurEnd`). Consequently, over any
commutative ring `k` for which `algebraMap k (End X)` is bijective—in particular for a simple
object with finite-dimensional endomorphisms over an algebraically closed field—any signed
self-duality of `X` with sign `ε` forces `TauCeti.frobeniusSchurIndicator k X 2 = (ε : k)`,
identifying the sign with the second Frobenius–Schur indicator `ν₂(X)` independently of `r`.

Finally, in any dagger braided category with a unitary dual functor, taking
`tensorSignedSelfDuality rX rY :=
  (rX ⊗ₘ rY) ≫ (β_ Xᘁ Yᘁ).hom ≫ (rightDualTensorIso X Y).inv`
produces a signed self-duality on `X ⊗ Y` obeying the multiplicative sign law
`ε(r_X ⊗_β r_Y) = ε(r_X) * ε(r_Y)`. When `unitaryDualPivotalIsoApp X` agrees with
`TauCeti.drinfeldIso X` (trivial twist at `X`), the associated cup and cap are `ε`-symmetric under
the braiding.

## Main declarations

* `TauCeti.pivotalRotate_coevaluation_comp_whiskerLeft` and
  `TauCeti.homTensorPowTwoLinearEquiv_frobeniusSchurEnd`: the Ng–Schauenburg description of
  `E_X^{(2)}` as `g ↦ gᘁ ≫ (pivotalIsoApp X).inv` in an arbitrary pivotal category;
* `TauCeti.frobeniusSchurIndicator_two_eq_of_rightAdjointMate_comp_pivotalIsoApp_inv`:
  eigenvalue formula for `ν₂(X)` whenever `algebraMap k (End X)` is bijective;
* `TauCeti.IsSignedSelfDuality`: signed self-duality `r ≫ dualConj r = (ε : ℤ) • φ_X` for
  unitary `r : X ⟶ Xᘁ` and `ε : ℤˣ`, with its equivalent characterizations
  (`isSignedSelfDuality_iff_eq_smul_comp_rightAdjointMate`,
  `isSignedSelfDuality_iff_rightAdjointMate_dagger`, `isSignedSelfDuality_iff_evaluation`,
  `isSignedSelfDuality_iff_cup`, `isSignedSelfDuality_iff_dagger_cup`);
* `TauCeti.IsSignedSelfDuality.transport` and
  `TauCeti.IsSignedSelfDuality.sign_eq_of_comp_dagger_eq_smul`: unitary transport and sign
  independence;
* `TauCeti.frobeniusSchurIndicator_two_eq_of_isSignedSelfDuality` and
  `TauCeti.unitaryDual_frobeniusSchurIndicator_two_eq_of_isSignedSelfDuality`: identification
  `ν₂(X) = ε` on scalar-endomorphism and simple objects;
* `TauCeti.tensorSignedSelfDuality` and `TauCeti.IsSignedSelfDuality.tensor`: braided tensor
  product of signed self-dualities and the sign law `ε(r_X ⊗_β r_Y) = ε(r_X)ε(r_Y)`.

## References

* S.-H. Ng, P. Schauenburg, *Higher Frobenius–Schur indicators for pivotal categories*, in
  *Hopf algebras and generalizations*, Contemp. Math. **441** (2007), 63–90, Def. 3.1 and §4
* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  [arXiv:1808.00323](https://arxiv.org/abs/1808.00323), §2
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory ExactPairing

universe w v u

namespace TauCeti

section PivotalNgSchauenburg

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

/-- In any pivotal category, rotating the cup `η_ X Xᘁ ≫ X ◁ g` associated to `g : Xᘁ ⟶ X` yields
the cup associated to `gᘁ ≫ (pivotalIsoApp X).inv`. -/
theorem pivotalRotate_coevaluation_comp_whiskerLeft {X : C} (g : Xᘁ ⟶ X) :
    pivotalRotate (η_ X Xᘁ ≫ X ◁ g) =
      η_ X Xᘁ ≫ X ◁ (gᘁ ≫ (pivotalIsoApp X).inv) := by
  rw [pivotalRotate_comp_whiskerLeft, pivotalRotate_coevaluation, pivotalExactPairing_coevaluation,
    Category.assoc, whisker_exchange, ← coevaluation_comp_rightAdjointMate_assoc,
    MonoidalCategory.whiskerLeft_comp]

section Linear

variable (k : Type w) [Preadditive C] [MonoidalPreadditive C]

/-- Through Frobenius reciprocity `homTensorPowTwoLinearEquiv k X`, the second Frobenius–Schur
rotation `frobeniusSchurRotate X 1` acts on `g : Xᘁ ⟶ X` by
`g ↦ gᘁ ≫ (pivotalIsoApp X).inv`. -/
theorem frobeniusSchurRotate_one_homTensorPowTwoLinearEquiv_symm [Semiring k] [Linear k C]
    [MonoidalLinear k C] (X : C) (g : Xᘁ ⟶ X) :
    frobeniusSchurRotate X 1 ((homTensorPowTwoLinearEquiv k X).symm g) =
      (homTensorPowTwoLinearEquiv k X).symm (gᘁ ≫ (pivotalIsoApp X).inv) := by
  rw [homTensorPowTwoLinearEquiv_symm_apply, homTensorPowTwoLinearEquiv_symm_apply,
    frobeniusSchurRotate_def, MonoidalCategory.whiskerLeft_comp, ← Category.assoc,
    pivotalRotate_comp_whiskerLeft, pivotalRotate_coevaluation_comp_whiskerLeft,
    tensorPowSuccIso_succ_hom, tensorPowSuccIso_zero_hom]
  have hcoh :
      (ρ_ X).inv ▷ X ≫ (α_ X (𝟙_ C) X).hom ≫ X ◁ ((λ_ X).hom ≫ (ρ_ X).inv) =
        X ◁ (ρ_ X).inv := by
    monoidal
  rw [Category.assoc, Category.assoc, hcoh, ← MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- **Ng–Schauenburg formula**: conjugating `frobeniusSchurEnd k X 1` by
`homTensorPowTwoLinearEquiv k X` gives the linear map `g ↦ gᘁ ≫ (pivotalIsoApp X).inv`. -/
theorem homTensorPowTwoLinearEquiv_frobeniusSchurEnd [Semiring k] [Linear k C]
    [MonoidalLinear k C] (X : C) (g : Xᘁ ⟶ X) :
    homTensorPowTwoLinearEquiv k X
        (frobeniusSchurEnd k X 1 ((homTensorPowTwoLinearEquiv k X).symm g)) =
      gᘁ ≫ (pivotalIsoApp X).inv := by
  rw [coe_frobeniusSchurEnd, frobeniusSchurRotate_one_homTensorPowTwoLinearEquiv_symm,
    LinearEquiv.apply_symm_apply]

/-- Over any commutative ring `k` for which `algebraMap k (End X)` is bijective, if an isomorphism
`g : Xᘁ ≅ X` is an eigenvector of `h ↦ hᘁ ≫ (pivotalIsoApp X).inv` with eigenvalue `c : k`,
then the second Frobenius–Schur indicator `ν₂(X)` equals `c`. -/
theorem frobeniusSchurIndicator_two_eq_of_rightAdjointMate_comp_pivotalIsoApp_inv [CommRing k]
    [Linear k C] [MonoidalLinear k C] {X : C} (hbij : Function.Bijective (algebraMap k (End X)))
    (g : Xᘁ ≅ X) (c : k) (hg : g.homᘁ ≫ (pivotalIsoApp X).inv = c • g.hom) :
    frobeniusSchurIndicator k X 2 = c := by
  have hbij' : Function.Bijective (fun a : k => a • 𝟙 X) := by
    have hfun : (fun a : k => a • 𝟙 X) = End.asHom ∘ algebraMap k (End X) := by
      funext a
      simp [End.algebraMap_asHom]
    rw [hfun]
    exact (Equiv.bijective ⟨End.asHom, End.of, fun _ => rfl, fun _ => rfl⟩).comp hbij
  let eEnd : k ≃ₗ[k] (X ⟶ X) :=
    LinearEquiv.ofBijective
      { toFun := fun a => a • 𝟙 X
        map_add' := fun a b => add_smul a b (𝟙 X)
        map_smul' := fun a b => by simp [smul_smul] }
      hbij'
  let L : (𝟙_ C ⟶ tensorPow X 2) ≃ₗ[k] k :=
    (homTensorPowTwoLinearEquiv k X).trans
      ((Linear.homCongr k g (Iso.refl X)).trans eEnd.symm)
  have hL1 : L.conj (frobeniusSchurEnd k X 1) 1 = c := by
    have hsymm : L.symm 1 = (homTensorPowTwoLinearEquiv k X).symm g.hom := by
      have he1 : eEnd 1 = 𝟙 X := by simp [eEnd]
      simp [L, he1, Linear.homCongr_symm_apply]
    rw [LinearEquiv.conj_apply_apply, hsymm]
    simp only [L, LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_hom, Category.comp_id]
    rw [homTensorPowTwoLinearEquiv_frobeniusSchurEnd, hg, Linear.comp_smul, Iso.inv_hom_id]
    exact eEnd.symm_apply_eq.mpr (by simp [eEnd])
  have hconj : L.conj (frobeniusSchurEnd k X 1) = c • (1 : Module.End k k) := by
    ext
    simp [hL1]
  rw [frobeniusSchurIndicator_two, ← LinearMap.trace_conj' (frobeniusSchurEnd k X 1) L, hconj,
    LinearMap.trace_eq_matrix_trace k (Module.Basis.singleton Unit k)]
  simp [Matrix.trace, Matrix.diag]

end Linear

end PivotalNgSchauenburg

section SignedSelfDuality

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C] [RightRigidCategory C]

/-- The dagger of the cup `η_ X Xᘁ ≫ X ◁ dagger r` always equals
`((unitaryDualPivotalIsoApp X).hom ⊗ₘ r) ≫ ε_ Xᘁ Xᘁᘁ`. -/
theorem dagger_coevaluation_comp_whiskerLeft_dagger {X : C} (r : X ⟶ Xᘁ) :
    dagger (η_ X Xᘁ ≫ X ◁ dagger r) =
      ((unitaryDualPivotalIsoApp X).hom ⊗ₘ r) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) := by
  rw [dagger_comp, dagger_whiskerLeft, dagger_dagger,
    ← unitaryDualPivotalIsoApp_hom_whiskerRight_evaluation, ← Category.assoc,
    ← tensorHom_def']

/-- The dagger of the cap `r ▷ X ≫ ε_ X Xᘁ` always equals
`η_ Xᘁ Xᘁᘁ ≫ (dagger r ⊗ₘ (unitaryDualPivotalIsoApp X).inv)`. -/
theorem dagger_whiskerRight_comp_evaluation {X : C} (r : X ⟶ Xᘁ) :
    dagger (r ▷ X ≫ ε_ X Xᘁ) =
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫
        (dagger r ⊗ₘ (unitaryDualPivotalIsoApp X).inv) := by
  rw [dagger_comp, dagger_whiskerRight,
    ← coevaluation_comp_whiskerLeft_unitaryDualPivotalIsoApp_inv,
    Category.assoc, ← tensorHom_def']

variable [Preadditive C]

/-- A *signed self-duality* of `X` with sign `ε : ℤˣ` (`±1`) is a unitary morphism `r : X ⟶ Xᘁ`
satisfying `r ≫ dualConj r = (ε : ℤ) • (unitaryDualPivotalIsoApp X).hom`. -/
def IsSignedSelfDuality {X : C} (r : X ⟶ Xᘁ) (ε : ℤˣ) : Prop :=
  IsUnitary r ∧ r ≫ dualConj r = (ε : ℤ) • (unitaryDualPivotalIsoApp X).hom

/-- The underlying morphism of a signed self-duality is unitary. -/
theorem IsSignedSelfDuality.isUnitary {X : C} {r : X ⟶ Xᘁ} {ε : ℤˣ}
    (h : IsSignedSelfDuality r ε) : IsUnitary r :=
  h.1

/-- The defining equation `r ≫ dualConj r = (ε : ℤ) • (unitaryDualPivotalIsoApp X).hom`. -/
theorem IsSignedSelfDuality.comp_dualConj {X : C} {r : X ⟶ Xᘁ} {ε : ℤˣ}
    (h : IsSignedSelfDuality r ε) :
    r ≫ dualConj r = (ε : ℤ) • (unitaryDualPivotalIsoApp X).hom :=
  h.2

/-- A signed self-duality of sign `+1` satisfies
`r ≫ dualConj r = (unitaryDualPivotalIsoApp X).hom`. -/
theorem isSignedSelfDuality_one_iff {X : C} (r : X ⟶ Xᘁ) :
    IsSignedSelfDuality r 1 ↔
      IsUnitary r ∧ r ≫ dualConj r = (unitaryDualPivotalIsoApp X).hom := by
  simp [IsSignedSelfDuality]

/-- A signed self-duality of sign `-1` satisfies
`r ≫ dualConj r = -(unitaryDualPivotalIsoApp X).hom`. -/
theorem isSignedSelfDuality_neg_one_iff {X : C} (r : X ⟶ Xᘁ) :
    IsSignedSelfDuality r (-1) ↔
      IsUnitary r ∧ r ≫ dualConj r = -(unitaryDualPivotalIsoApp X).hom := by
  simp [IsSignedSelfDuality]

/-- The cup and cap of any signed self-duality satisfy the zig-zag identity, making `(X, X)` an
exact pairing. -/
theorem IsSignedSelfDuality.cup_cap_zigzag {X : C} {r : X ⟶ Xᘁ} {ε : ℤˣ}
    (h : IsSignedSelfDuality r ε) :
    (η_ X Xᘁ ≫ X ◁ dagger r) ▷ X ≫ (α_ X X X).hom ≫ X ◁ (r ▷ X ≫ ε_ X Xᘁ) =
      (λ_ X).hom ≫ (ρ_ X).inv := by
  calc
    (η_ X Xᘁ ≫ X ◁ dagger r) ▷ X ≫ (α_ X X X).hom ≫ X ◁ (r ▷ X ≫ ε_ X Xᘁ)
        = η_ X Xᘁ ▷ X ≫ (α_ X Xᘁ X).hom ≫ X ◁ ((dagger r ≫ r) ▷ X) ≫
            X ◁ ε_ X Xᘁ := by
      simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [associator_naturality_middle_assoc]
    _ = (λ_ X).hom ≫ (ρ_ X).inv := by
      rw [h.isUnitary.dagger_hom_id, id_whiskerRight, MonoidalCategory.whiskerLeft_id,
        Category.id_comp, ExactPairing.evaluation_coevaluation]

section UnitaryDual

variable [UnitaryDualFunctor C]

/-- For unitary `r : X ⟶ Xᘁ`, `r ≫ dualConj r = (ε : ℤ) • φ_X` is equivalent to
`r = (ε : ℤ) • (φ_X ≫ rᘁ)`. -/
theorem isSignedSelfDuality_iff_eq_smul_comp_rightAdjointMate {X : C} {r : X ⟶ Xᘁ}
    (hr : IsUnitary r) (ε : ℤˣ) :
    IsSignedSelfDuality r ε ↔
      r = (ε : ℤ) • ((unitaryDualPivotalIsoApp X).hom ≫ rᘁ) := by
  refine ⟨fun h => ?_, fun h => ⟨hr, ?_⟩⟩
  · calc
      r = r ≫ dualConj r ≫ dagger (dualConj r) := by
        rw [hr.dualConj.hom_dagger_id, Category.comp_id]
      _ = (r ≫ dualConj r) ≫ rᘁ := by rw [dagger_dualConj, Category.assoc]
      _ = (ε : ℤ) • ((unitaryDualPivotalIsoApp X).hom ≫ rᘁ) := by
        rw [h.comp_dualConj, Preadditive.zsmul_comp]
  · calc
      r ≫ dualConj r
          = ((ε : ℤ) • ((unitaryDualPivotalIsoApp X).hom ≫ rᘁ)) ≫ dualConj r :=
        congrArg (· ≫ dualConj r) h
      _ = (ε : ℤ) • ((unitaryDualPivotalIsoApp X).hom ≫ dagger (dualConj r) ≫
          dualConj r) := by
        rw [Preadditive.zsmul_comp, Category.assoc, dagger_dualConj]
      _ = (ε : ℤ) • (unitaryDualPivotalIsoApp X).hom := by
        rw [hr.dualConj.dagger_hom_id, Category.comp_id]

/-- For unitary `r : X ⟶ Xᘁ`, `r ≫ dualConj r = (ε : ℤ) • φ_X` is equivalent to
`r = (ε : ℤ) • (φ_X ≫ dagger (dualConj r))`. -/
theorem isSignedSelfDuality_iff_eq_smul_comp_dagger_dualConj {X : C} {r : X ⟶ Xᘁ}
    (hr : IsUnitary r) (ε : ℤˣ) :
    IsSignedSelfDuality r ε ↔
      r = (ε : ℤ) • ((unitaryDualPivotalIsoApp X).hom ≫ dagger (dualConj r)) := by
  simpa [dagger_dualConj] using isSignedSelfDuality_iff_eq_smul_comp_rightAdjointMate hr ε

/-- For unitary `r : X ⟶ Xᘁ`, `IsSignedSelfDuality r ε` is equivalent to the Ng–Schauenburg
eigenvector equation
`(dagger r)ᘁ ≫ (unitaryDualPivotalIsoApp X).inv = (ε : ℤ) • dagger r`. -/
theorem isSignedSelfDuality_iff_rightAdjointMate_dagger {X : C} {r : X ⟶ Xᘁ}
    (hr : IsUnitary r) (ε : ℤˣ) :
    IsSignedSelfDuality r ε ↔
      (dagger r)ᘁ ≫ (unitaryDualPivotalIsoApp X).inv = (ε : ℤ) • dagger r := by
  refine ⟨fun h => ?_, fun h => ⟨hr, ?_⟩⟩
  · calc
      (dagger r)ᘁ ≫ (unitaryDualPivotalIsoApp X).inv
          = dagger r ≫ (r ≫ dualConj r) ≫ (unitaryDualPivotalIsoApp X).inv := by
        rw [← Category.assoc, hr.dagger_hom_id_assoc, dualConj_eq_rightAdjointMate_dagger]
      _ = (ε : ℤ) • dagger r := by
        rw [h.comp_dualConj, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Iso.hom_inv_id,
          Category.comp_id]
  · calc
      r ≫ dualConj r = r ≫ ((dagger r)ᘁ ≫ (unitaryDualPivotalIsoApp X).inv) ≫
          (unitaryDualPivotalIsoApp X).hom := by
        rw [dualConj_eq_rightAdjointMate_dagger, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = (ε : ℤ) • (unitaryDualPivotalIsoApp X).hom := by
        rw [h, Preadditive.zsmul_comp, Preadditive.comp_zsmul, hr.hom_dagger_id_assoc]

section MonoidalPreadditive

variable [MonoidalPreadditive C]

/-- **Symmetric-evaluation characterization**: for unitary `r : X ⟶ Xᘁ`,
`IsSignedSelfDuality r ε` holds if and only if
`r ▷ X ≫ ε_ X Xᘁ = (ε : ℤ) • (((unitaryDualPivotalIsoApp X).hom ⊗ₘ r) ≫ ε_ Xᘁ Xᘁᘁ)`. -/
theorem isSignedSelfDuality_iff_evaluation {X : C} {r : X ⟶ Xᘁ}
    (hr : IsUnitary r) (ε : ℤˣ) :
    IsSignedSelfDuality r ε ↔
      r ▷ X ≫ ε_ X Xᘁ =
        (ε : ℤ) •
          (((unitaryDualPivotalIsoApp X).hom ⊗ₘ r) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C)) := by
  have hev : ((unitaryDualPivotalIsoApp X).hom ⊗ₘ r) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) =
      ((unitaryDualPivotalIsoApp X).hom ≫ rᘁ) ▷ X ≫ ε_ X Xᘁ := by
    rw [tensorHom_def, Category.assoc, ← rightAdjointMate_comp_evaluation, comp_whiskerRight,
      Category.assoc]
  rw [isSignedSelfDuality_iff_eq_smul_comp_rightAdjointMate hr ε, hev]
  conv_rhs => rw [← Preadditive.zsmul_comp, ← zsmul_whiskerRight]
  exact ⟨fun h => congrArg (fun f => f ▷ X ≫ ε_ X Xᘁ) h, fun h => rightHom_ext h⟩

/-- **Dagger cup–cap relation**: for unitary `r : X ⟶ Xᘁ`, `IsSignedSelfDuality r ε` holds if
and only if the cap `r ▷ X ≫ ε_ X Xᘁ` is `ε` times the dagger of the cup
`η_ X Xᘁ ≫ X ◁ dagger r`. -/
theorem isSignedSelfDuality_iff_cap_eq_smul_dagger_cup {X : C} {r : X ⟶ Xᘁ}
    (hr : IsUnitary r) (ε : ℤˣ) :
    IsSignedSelfDuality r ε ↔
      r ▷ X ≫ ε_ X Xᘁ = (ε : ℤ) • dagger (η_ X Xᘁ ≫ X ◁ dagger r) := by
  rw [isSignedSelfDuality_iff_evaluation hr ε, dagger_coevaluation_comp_whiskerLeft_dagger]

/-- **Dagger cup–cap relation** (adjoint form): for unitary `r : X ⟶ Xᘁ`,
`IsSignedSelfDuality r ε` holds if and only if
`dagger (η_ X Xᘁ ≫ X ◁ dagger r) = (ε : ℤ) • (r ▷ X ≫ ε_ X Xᘁ)`. -/
theorem isSignedSelfDuality_iff_dagger_cup {X : C} {r : X ⟶ Xᘁ}
    (hr : IsUnitary r) (ε : ℤˣ) :
    IsSignedSelfDuality r ε ↔
      dagger (η_ X Xᘁ ≫ X ◁ dagger r) = (ε : ℤ) • (r ▷ X ≫ ε_ X Xᘁ) := by
  rw [isSignedSelfDuality_iff_cap_eq_smul_dagger_cup hr ε]
  have hsq : (ε : ℤ) * (ε : ℤ) = 1 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num
  constructor <;> intro h
  · rw [h, smul_smul, hsq, one_zsmul]
  · rw [h, smul_smul, hsq, one_zsmul]

/-- **Cup characterization**: in a dagger preadditive monoidal category, for unitary
`r : X ⟶ Xᘁ`, `IsSignedSelfDuality r ε` holds if and only if
`η_ X Xᘁ ≫ X ◁ dagger r =
  (ε : ℤ) • (η_ Xᘁ Xᘁᘁ ≫ (dagger r ⊗ₘ (unitaryDualPivotalIsoApp X).inv))`. -/
theorem isSignedSelfDuality_iff_cup [DaggerPreadditive C] {X : C} {r : X ⟶ Xᘁ}
    (hr : IsUnitary r) (ε : ℤˣ) :
    IsSignedSelfDuality r ε ↔
      η_ X Xᘁ ≫ X ◁ dagger r =
        (ε : ℤ) • (η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫
          (dagger r ⊗ₘ (unitaryDualPivotalIsoApp X).inv)) := by
  rw [isSignedSelfDuality_iff_dagger_cup hr ε, ← dagger_whiskerRight_comp_evaluation]
  constructor <;> intro h
  · have hd := congrArg dagger h
    simpa [dagger_zsmul] using hd
  · have hd := congrArg dagger h
    simpa [dagger_zsmul] using hd

/-- In a dagger preadditive monoidal category, the dagger of the cap of a signed self-duality is
`ε` times its cup. -/
theorem IsSignedSelfDuality.dagger_cap [DaggerPreadditive C] {X : C} {r : X ⟶ Xᘁ} {ε : ℤˣ}
    (h : IsSignedSelfDuality r ε) :
    dagger (r ▷ X ≫ ε_ X Xᘁ) = (ε : ℤ) • (η_ X Xᘁ ≫ X ◁ dagger r) := by
  have hd := congrArg dagger ((isSignedSelfDuality_iff_cap_eq_smul_dagger_cup h.isUnitary ε).mp h)
  simpa [dagger_zsmul] using hd

end MonoidalPreadditive

/-- **Unitary transport of signed self-dualities**: conjugating `r : X ⟶ Xᘁ` along a unitary
morphism `u : X ⟶ Y` gives `dagger u ≫ r ≫ dualConj u : Y ⟶ Yᘁ` with the same sign `ε`. -/
theorem isSignedSelfDuality_transport_iff {X Y : C} {u : X ⟶ Y} (hu : IsUnitary u)
    (r : X ⟶ Xᘁ) (ε : ℤˣ) :
    IsSignedSelfDuality (dagger u ≫ r ≫ dualConj u) ε ↔ IsSignedSelfDuality r ε := by
  have hcomp :
      (dagger u ≫ r ≫ dualConj u) ≫ dualConj (dagger u ≫ r ≫ dualConj u) =
        dagger u ≫ (r ≫ dualConj r) ≫ (unitaryDualPivotalIsoApp X).inv ≫ u ≫
          (unitaryDualPivotalIsoApp Y).hom := by
    simp only [dualConj_comp, dualConj_dagger, Category.assoc]
    rw [hu.dualConj.hom_dagger_id_assoc, dualConj_dualConj_eq]
  constructor
  · rintro ⟨hU, hEq⟩
    have hrU : IsUnitary r := by
      have heq : r = u ≫ (dagger u ≫ r ≫ dualConj u) ≫ dagger (dualConj u) := by
        rw [Category.assoc, Category.assoc, hu.dualConj.hom_dagger_id, Category.comp_id,
          hu.hom_dagger_id_assoc]
      rw [heq]
      exact hu.comp (hU.comp hu.dualConj.dagger)
    refine ⟨hrU, ?_⟩
    rw [hcomp] at hEq
    calc
      r ≫ dualConj r = u ≫ (dagger u ≫ (r ≫ dualConj r) ≫
          (unitaryDualPivotalIsoApp X).inv ≫ u ≫ (unitaryDualPivotalIsoApp Y).hom) ≫
          (unitaryDualPivotalIsoApp Y).inv ≫ dagger u ≫
          (unitaryDualPivotalIsoApp X).hom := by
        simp [hu.hom_dagger_id_assoc]
      _ = (ε : ℤ) • (unitaryDualPivotalIsoApp X).hom := by
        rw [hEq, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Iso.hom_inv_id_assoc,
          hu.hom_dagger_id_assoc]
  · rintro ⟨hrU, hEq⟩
    refine ⟨hu.dagger.comp (hrU.comp hu.dualConj), ?_⟩
    rw [hcomp, hEq, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Iso.hom_inv_id_assoc,
      hu.dagger_hom_id_assoc]

/-- Transporting a signed self-duality along a unitary morphism preserves the sign. -/
theorem IsSignedSelfDuality.transport {X Y : C} {u : X ⟶ Y} (hu : IsUnitary u)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    IsSignedSelfDuality (dagger u ≫ r ≫ dualConj u) ε :=
  (isSignedSelfDuality_transport_iff hu r ε).mpr h

end UnitaryDual

/-- **Sign independence**: if two signed self-dualities `r₁, r₂ : X ⟶ Xᘁ` satisfy
`r₁ ≫ dagger r₂ = c • 𝟙 X` for a scalar `c : R`, then
`(ε₁ : ℤ) • 𝟙 X = (ε₂ : ℤ) • 𝟙 X`. -/
theorem IsSignedSelfDuality.zsmul_id_eq_of_comp_dagger_eq_smul {R : Type w} [Semiring R]
    [Star R] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C] [DaggerLinear R C]
    {X : C} {r₁ r₂ : X ⟶ Xᘁ} {ε₁ ε₂ : ℤˣ}
    (h₁ : IsSignedSelfDuality r₁ ε₁) (h₂ : IsSignedSelfDuality r₂ ε₂)
    (c : R) (hc : r₁ ≫ dagger r₂ = c • 𝟙 X) :
    (ε₁ : ℤ) • 𝟙 X = (ε₂ : ℤ) • 𝟙 X := by
  have hr₁ : r₁ = c • r₂ := by
    calc
      r₁ = (r₁ ≫ dagger r₂) ≫ r₂ := by
        rw [Category.assoc, h₂.isUnitary.dagger_hom_id, Category.comp_id]
      _ = c • r₂ := by rw [hc, Linear.smul_comp, Category.id_comp]
  have hnorm : (c * star c) • 𝟙 X = 𝟙 X := by
    have hU : IsUnitary (c • 𝟙 X) := hc ▸ h₁.isUnitary.comp h₂.isUnitary.dagger
    have hid := hU.hom_dagger_id
    rw [dagger_smul, dagger_id, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      smul_smul] at hid
    exact hid
  have hφ : (ε₁ : ℤ) • (unitaryDualPivotalIsoApp X).hom =
      (ε₂ : ℤ) • (unitaryDualPivotalIsoApp X).hom := by
    rw [← h₁.comp_dualConj, ← h₂.comp_dualConj, hr₁, dualConj_smul, Linear.smul_comp,
      Linear.comp_smul, smul_smul, ← Category.id_comp (r₂ ≫ dualConj r₂),
      ← Linear.smul_comp, hnorm, Category.id_comp]
  rw [← cancel_mono (unitaryDualPivotalIsoApp X).hom]
  simpa only [Preadditive.zsmul_comp, Category.id_comp] using hφ

/-- Under the same scalar-proportionality hypothesis, if `(2 : ℤ) • 𝟙 X ≠ 0` then
`ε₁ = ε₂`. -/
theorem IsSignedSelfDuality.sign_eq_of_comp_dagger_eq_smul {R : Type w} [Semiring R]
    [Star R] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C] [DaggerLinear R C]
    {X : C} {r₁ r₂ : X ⟶ Xᘁ} {ε₁ ε₂ : ℤˣ}
    (h₁ : IsSignedSelfDuality r₁ ε₁) (h₂ : IsSignedSelfDuality r₂ ε₂)
    (c : R) (hc : r₁ ≫ dagger r₂ = c • 𝟙 X) (h2 : (2 : ℤ) • 𝟙 X ≠ 0) :
    ε₁ = ε₂ := by
  have hid := h₁.zsmul_id_eq_of_comp_dagger_eq_smul h₂ c hc
  rcases Int.units_eq_one_or ε₁ with rfl | rfl <;>
    rcases Int.units_eq_one_or ε₂ with rfl | rfl
  · rfl
  · exfalso; apply h2
    simp only [Units.val_one, one_zsmul, Units.val_neg, neg_smul] at hid
    rw [show (2 : ℤ) • 𝟙 X = 𝟙 X + 𝟙 X from two_zsmul _]
    exact eq_neg_iff_add_eq_zero.mp hid
  · exfalso; apply h2
    simp only [Units.val_one, one_zsmul, Units.val_neg, neg_smul] at hid
    rw [show (2 : ℤ) • 𝟙 X = 𝟙 X + 𝟙 X from two_zsmul _]
    exact eq_neg_iff_add_eq_zero.mp hid.symm
  · rfl

end SignedSelfDuality

section PivotalAndFrobeniusSchur

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C] [RigidCategory C] [PivotalCategory C] [Preadditive C]

/-- The cup of any signed self-duality satisfies `cup ≫ dagger cup = rightDim X`, independently of
the sign `ε`. -/
theorem IsSignedSelfDuality.cup_comp_dagger_cup {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    (η_ X Xᘁ ≫ X ◁ dagger r) ≫ dagger (η_ X Xᘁ ≫ X ◁ dagger r) = rightDim X := by
  rw [rightDim_eq_dagger_coevaluation hφ]
  simp only [dagger_comp, dagger_whiskerLeft, dagger_dagger, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, h.isUnitary.dagger_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The cap of any signed self-duality satisfies `dagger cap ≫ cap = leftDim X`, independently of
the sign `ε`. -/
theorem IsSignedSelfDuality.dagger_cap_comp_cap {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    dagger (r ▷ X ≫ ε_ X Xᘁ) ≫ (r ▷ X ≫ ε_ X Xᘁ) = leftDim X := by
  rw [leftDim_eq_dagger_evaluation hφ]
  simp only [dagger_comp, dagger_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc, h.isUnitary.dagger_hom_id, id_whiskerRight, Category.id_comp]

variable [UnitaryDualFunctor C] [MonoidalPreadditive C]

/-- For a pivotal structure matching `unitaryDualPivotalIsoApp X`, the cup
`η_ X Xᘁ ≫ X ◁ dagger r` of a signed self-duality `r : X ⟶ Xᘁ` with sign `ε` is an eigenvector of
`pivotalRotate` with eigenvalue `ε`. -/
theorem IsSignedSelfDuality.pivotalRotate_cup {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    pivotalRotate (η_ X Xᘁ ≫ X ◁ dagger r) =
      (ε : ℤ) • (η_ X Xᘁ ≫ X ◁ dagger r) := by
  have hinv : (pivotalIsoApp X).inv = (unitaryDualPivotalIsoApp X).inv :=
    congrArg Iso.inv (Iso.ext hφ)
  rw [pivotalRotate_coevaluation_comp_whiskerLeft, hinv,
    (isSignedSelfDuality_iff_rightAdjointMate_dagger h.isUnitary ε).mp h,
    whiskerLeft_zsmul, Preadditive.comp_zsmul]

/-- Composing the cup and cap of a signed self-duality scales `rightDim X` by `ε`. -/
theorem IsSignedSelfDuality.cup_comp_cap_eq_rightDim {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    (η_ X Xᘁ ≫ X ◁ dagger r) ≫ (r ▷ X ≫ ε_ X Xᘁ) = (ε : ℤ) • rightDim X := by
  rw [(isSignedSelfDuality_iff_cap_eq_smul_dagger_cup h.isUnitary ε).mp h, Preadditive.comp_zsmul,
    h.cup_comp_dagger_cup hφ]

/-- Composing the cup and cap of a signed self-duality scales `leftDim X` by `ε`. -/
theorem IsSignedSelfDuality.cup_comp_cap_eq_leftDim [DaggerPreadditive C] {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    (η_ X Xᘁ ≫ X ◁ dagger r) ≫ (r ▷ X ≫ ε_ X Xᘁ) = (ε : ℤ) • leftDim X := by
  have hsq : (ε : ℤ) * (ε : ℤ) = 1 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num
  have hcup : η_ X Xᘁ ≫ X ◁ dagger r = (ε : ℤ) • dagger (r ▷ X ≫ ε_ X Xᘁ) := by
    rw [h.dagger_cap, smul_smul, hsq, one_zsmul]
  rw [hcup, Preadditive.zsmul_comp, h.dagger_cap_comp_cap hφ]

/-- Any signed self-dual object has equal left and right dimensions. -/
theorem IsSignedSelfDuality.leftDim_eq_rightDim [DaggerPreadditive C] {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    leftDim X = rightDim X := by
  have hsq : (ε : ℤ) * (ε : ℤ) = 1 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num
  have heq : (ε : ℤ) • leftDim X = (ε : ℤ) • rightDim X :=
    (h.cup_comp_cap_eq_leftDim hφ).symm.trans (h.cup_comp_cap_eq_rightDim hφ)
  have h2 := congrArg ((ε : ℤ) • ·) heq
  simpa [smul_smul, hsq] using h2

/-- **Identification with the second Frobenius–Schur indicator**: over any commutative ring `k`
for which `algebraMap k (End X)` is bijective, if `X` admits a signed self-duality with sign `ε`,
then `ν₂(X) = ε` for any pivotal structure matching `unitaryDualPivotalIsoApp X`. -/
theorem frobeniusSchurIndicator_two_eq_of_isSignedSelfDuality (k : Type w) [CommRing k]
    [Linear k C] [MonoidalLinear k C] {X : C}
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    (hbij : Function.Bijective (algebraMap k (End X)))
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    frobeniusSchurIndicator k X 2 = (ε : k) := by
  have hinv : (pivotalIsoApp X).inv = (unitaryDualPivotalIsoApp X).inv :=
    congrArg Iso.inv (Iso.ext hφ)
  have hg : (h.isUnitary.toIso.symm.hom)ᘁ ≫ (pivotalIsoApp X).inv =
      ((ε : ℤ) : k) • h.isUnitary.toIso.symm.hom := by
    rw [Iso.symm_hom, IsUnitary.toIso_inv, hinv,
      (isSignedSelfDuality_iff_rightAdjointMate_dagger h.isUnitary ε).mp h,
      Int.cast_smul_eq_zsmul k]
  exact frobeniusSchurIndicator_two_eq_of_rightAdjointMate_comp_pivotalIsoApp_inv k hbij
    h.isUnitary.toIso.symm ((ε : ℤ) : k) hg

/-- On a simple object with finite-dimensional endomorphisms over an algebraically closed field `k`,
the sign `ε` of any signed self-duality agrees with `frobeniusSchurIndicator k X 2`. -/
theorem frobeniusSchurIndicator_two_eq_of_isSignedSelfDuality_of_simple (k : Type w) [Field k]
    [IsAlgClosed k] [Linear k C] [MonoidalLinear k C] [Limits.HasKernels C] {X : C}
    [Simple X] [FiniteDimensional k (X ⟶ X)]
    (hφ : (pivotalIsoApp X).hom = (unitaryDualPivotalIsoApp X).hom)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    frobeniusSchurIndicator k X 2 = (ε : k) :=
  frobeniusSchurIndicator_two_eq_of_isSignedSelfDuality k hφ
    (bijective_algebraMap_end_of_simple k X) h

end PivotalAndFrobeniusSchur

section InducedFrobeniusSchur

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C] [RightRigidCategory C] [UnitaryDualFunctor C]
  [Preadditive C] [MonoidalPreadditive C]

/-- For the induced pivotal structure `unitaryDualPivotalCategory C`, any signed self-duality of
sign `ε` on an object with `algebraMap k (End X)` bijective satisfies `ν₂(X) = ε`. -/
theorem unitaryDual_frobeniusSchurIndicator_two_eq_of_isSignedSelfDuality (k : Type w) [CommRing k]
    [Linear k C] [MonoidalLinear k C] {X : C}
    (hbij : Function.Bijective (algebraMap k (End X)))
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    let _ := unitaryDualRigidCategory C
    let _ := unitaryDualPivotalCategory C
    frobeniusSchurIndicator k X 2 = (ε : k) := by
  let := unitaryDualRigidCategory C
  let := unitaryDualPivotalCategory C
  exact frobeniusSchurIndicator_two_eq_of_isSignedSelfDuality k
    (congrArg Iso.hom (pivotalIsoApp_unitaryDualPivotalCategory X)) hbij h

/-- For `unitaryDualPivotalCategory C` on a simple object with finite-dimensional endomorphisms
over an algebraically closed field `k`, any signed self-duality of sign `ε` satisfies
`ν₂(X) = ε`. -/
theorem unitaryDual_frobeniusSchurIndicator_two_eq_of_isSignedSelfDuality_of_simple (k : Type w)
    [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C] [Limits.HasKernels C] {X : C}
    [Simple X] [FiniteDimensional k (X ⟶ X)] {r : X ⟶ Xᘁ} {ε : ℤˣ}
    (h : IsSignedSelfDuality r ε) :
    let _ := unitaryDualRigidCategory C
    let _ := unitaryDualPivotalCategory C
    frobeniusSchurIndicator k X 2 = (ε : k) :=
  unitaryDual_frobeniusSchurIndicator_two_eq_of_isSignedSelfDuality k
    (bijective_algebraMap_end_of_simple k X) h

end InducedFrobeniusSchur

section BraidedMate

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]

/-- The right adjoint mate of a braiding `(β_ B A).hom : B ⊗ A ⟶ A ⊗ B` is the braiding of the
right duals, transported along `rightDualTensorIso`. -/
theorem rightAdjointMate_braiding_hom (A B : C) :
    ((β_ B A).hom)ᘁ =
      (rightDualTensorIso A B).hom ≫ (β_ Bᘁ Aᘁ).hom ≫ (rightDualTensorIso B A).inv := by
  refine rightHom_ext (X := B ⊗ A) ?_
  rw [rightAdjointMate_comp_evaluation, ← rightDualTensorIso_hom_whiskerRight_evaluation A B,
    whisker_exchange_assoc, whiskerLeft_braiding_comp_tensor_evaluation A Aᘁ B Bᘁ,
    comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    rightDualTensorIso_inv_whiskerRight_evaluation]

/-- The braided tensor product `r_X ⊗_β r_Y : X ⊗ Y ⟶ (X ⊗ Y)ᘁ` of self-duality morphisms
`r_X : X ⟶ Xᘁ` and `r_Y : Y ⟶ Yᘁ`, using `β_{Xᘁ, Yᘁ}` to reverse the dual factors. -/
noncomputable def tensorSignedSelfDuality {X Y : C} (rX : X ⟶ Xᘁ) (rY : Y ⟶ Yᘁ) :
    X ⊗ Y ⟶ (X ⊗ Y)ᘁ :=
  (rX ⊗ₘ rY) ≫ (β_ Xᘁ Yᘁ).hom ≫ (rightDualTensorIso X Y).inv

end BraidedMate

section BraidedTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]
  [BraidedCategory C] [RightRigidCategory C] [UnitaryDualFunctor C]

/-- The conjugate of a braiding `(β_ B A).hom` is the inverse braiding of the right duals,
transported along `rightDualTensorIso`. -/
theorem dualConj_braiding_hom [DaggerBraidedCategory C] (A B : C) :
    dualConj (β_ B A).hom =
      (rightDualTensorIso B A).hom ≫ (β_ Bᘁ Aᘁ).inv ≫ (rightDualTensorIso A B).inv := by
  rw [dualConj_eq_dagger_rightAdjointMate, rightAdjointMate_braiding_hom]
  simp [Category.assoc]

variable [DaggerMonoidalCategory C]

/-- When `unitaryDualPivotalIsoApp X` agrees with `drinfeldIso X` (trivial twist at `X`), the cap
of a signed self-duality is `ε`-symmetric under the braiding. -/
theorem IsSignedSelfDuality.braiding_comp_cap [Preadditive C] [MonoidalPreadditive C] {X : C}
    (hd : (unitaryDualPivotalIsoApp X).hom = (drinfeldIso X).hom)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    (β_ X X).hom ≫ r ▷ X ≫ ε_ X Xᘁ = (ε : ℤ) • (r ▷ X ≫ ε_ X Xᘁ) := by
  calc
    (β_ X X).hom ≫ r ▷ X ≫ ε_ X Xᘁ
        = X ◁ r ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by rw [braiding_naturality_right_assoc]
    _ = X ◁ r ≫ dagger (η_ X Xᘁ) := by
      rw [← (unitaryDualPivotalIsoApp_eq_drinfeldIso_iff_dagger_coevaluation X).mp hd]
    _ = dagger (η_ X Xᘁ ≫ X ◁ dagger r) := by simp
    _ = (ε : ℤ) • (r ▷ X ≫ ε_ X Xᘁ) :=
      (isSignedSelfDuality_iff_dagger_cup h.isUnitary ε).mp h

variable [DaggerBraidedCategory C]

/-- The braided tensor product of unitary morphisms is unitary. -/
theorem IsUnitary.tensorSignedSelfDuality {X Y : C} {rX : X ⟶ Xᘁ} {rY : Y ⟶ Yᘁ}
    (hX : IsUnitary rX) (hY : IsUnitary rY) :
    IsUnitary (TauCeti.tensorSignedSelfDuality rX rY) :=
  (hX.tensorHom hY).comp
    ((isUnitary_braiding Xᘁ Yᘁ).comp (isUnitary_rightDualTensorIso_inv X Y))

/-- **Braided tensor-product sign law**: in any dagger braided category with a unitary dual
functor, the braided tensor product `r_X ⊗_β r_Y` of signed self-dualities of signs `ε_X` and
`ε_Y` is a signed self-duality of sign `ε_X * ε_Y`. -/
theorem IsSignedSelfDuality.tensor [Preadditive C] [MonoidalPreadditive C] {X Y : C}
    {rX : X ⟶ Xᘁ} {rY : Y ⟶ Yᘁ} {εX εY : ℤˣ}
    (hX : IsSignedSelfDuality rX εX) (hY : IsSignedSelfDuality rY εY) :
    IsSignedSelfDuality (tensorSignedSelfDuality rX rY) (εX * εY) := by
  refine ⟨hX.isUnitary.tensorSignedSelfDuality hY.isUnitary, ?_⟩
  have hφ : (unitaryDualPivotalIsoApp (X ⊗ Y)).hom =
      ((unitaryDualPivotalIsoApp X).hom ⊗ₘ (unitaryDualPivotalIsoApp Y).hom) ≫
        (rightDualTensorIso Yᘁ Xᘁ).inv ≫ ((rightDualTensorIso X Y).hom)ᘁ := by
    have hm := NatTrans.IsMonoidal.tensor (τ := (unitaryDualPivotalNatIso C).hom) X Y
    rw [Functor.LaxMonoidal.id_μ, Category.id_comp, unitaryDualPivotalNatIso_hom_app,
      unitaryDualPivotalNatIso_hom_app, unitaryDualPivotalNatIso_hom_app,
      doubleRightDualFunctor_μ] at hm
    exact hm
  have hconj_inv : dualConj (rightDualTensorIso X Y).inv = ((rightDualTensorIso X Y).hom)ᘁ := by
    rw [dualConj_eq_rightAdjointMate_dagger, dagger_rightDualTensorIso_inv]
  have hzsmul_tensor :
      ((εX : ℤ) • (unitaryDualPivotalIsoApp X).hom) ⊗ₘ
          ((εY : ℤ) • (unitaryDualPivotalIsoApp Y).hom) =
        ((εX * εY : ℤˣ) : ℤ) •
          ((unitaryDualPivotalIsoApp X).hom ⊗ₘ (unitaryDualPivotalIsoApp Y).hom) := by
    rw [zsmul_tensorHom, tensorHom_zsmul, smul_smul, Units.val_mul]
  calc
    tensorSignedSelfDuality rX rY ≫ dualConj (tensorSignedSelfDuality rX rY)
        = (rX ⊗ₘ rY) ≫ (β_ Xᘁ Yᘁ).hom ≫
            ((rightDualTensorIso X Y).inv ≫ dualConj (rX ⊗ₘ rY)) ≫
            dualConj (β_ Xᘁ Yᘁ).hom ≫ dualConj (rightDualTensorIso X Y).inv := by
      simp only [tensorSignedSelfDuality, dualConj_comp, Category.assoc]
    _ = (rX ⊗ₘ rY) ≫ ((β_ Xᘁ Yᘁ).hom ≫ (dualConj rY ⊗ₘ dualConj rX)) ≫
          (rightDualTensorIso Xᘁ Yᘁ).inv ≫ dualConj (β_ Xᘁ Yᘁ).hom ≫
          ((rightDualTensorIso X Y).hom)ᘁ := by
      rw [rightDualTensorIso_inv_comp_dualConj_tensorHom, hconj_inv]
      simp only [Category.assoc]
    _ = ((rX ≫ dualConj rX) ⊗ₘ (rY ≫ dualConj rY)) ≫
          (β_ (Xᘁ : C)ᘁ (Yᘁ : C)ᘁ).hom ≫
          (rightDualTensorIso Xᘁ Yᘁ).inv ≫ dualConj (β_ Xᘁ Yᘁ).hom ≫
          ((rightDualTensorIso X Y).hom)ᘁ := by
      rw [← braiding_naturality]
      simp only [Category.assoc, ← tensorHom_comp_tensorHom_assoc]
    _ = ((rX ≫ dualConj rX) ⊗ₘ (rY ≫ dualConj rY)) ≫
          (rightDualTensorIso Yᘁ Xᘁ).inv ≫ ((rightDualTensorIso X Y).hom)ᘁ := by
      rw [dualConj_braiding_hom Yᘁ Xᘁ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    _ = ((εX * εY : ℤˣ) : ℤ) • (unitaryDualPivotalIsoApp (X ⊗ Y)).hom := by
      rw [hX.comp_dualConj, hY.comp_dualConj, hzsmul_tensor, Preadditive.zsmul_comp, hφ]

/-- When `unitaryDualPivotalIsoApp X` agrees with `drinfeldIso X`, the cup of a signed
self-duality is `ε`-symmetric under the braiding. -/
theorem IsSignedSelfDuality.cup_comp_braiding [Preadditive C] [MonoidalPreadditive C]
    [DaggerPreadditive C] {X : C}
    (hd : (unitaryDualPivotalIsoApp X).hom = (drinfeldIso X).hom)
    {r : X ⟶ Xᘁ} {ε : ℤˣ} (h : IsSignedSelfDuality r ε) :
    (η_ X Xᘁ ≫ X ◁ dagger r) ≫ (β_ X X).hom =
      (ε : ℤ) • (η_ X Xᘁ ≫ X ◁ dagger r) := by
  have hcap := congrArg dagger (h.braiding_comp_cap hd)
  simp only [dagger_comp, dagger_braiding_hom, dagger_zsmul, h.dagger_cap,
    Preadditive.zsmul_comp, Category.assoc] at hcap
  have hsq : (ε : ℤ) * (ε : ℤ) = 1 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num
  have hinv : (η_ X Xᘁ ≫ X ◁ dagger r) ≫ (β_ X X).inv =
      (ε : ℤ) • (η_ X Xᘁ ≫ X ◁ dagger r) := by
    have h1 := congrArg ((ε : ℤ) • ·) hcap
    simpa [smul_smul, hsq] using h1
  calc
    (η_ X Xᘁ ≫ X ◁ dagger r) ≫ (β_ X X).hom
        = ((ε : ℤ) • ((η_ X Xᘁ ≫ X ◁ dagger r) ≫ (β_ X X).inv)) ≫
            (β_ X X).hom := by
      rw [hinv, smul_smul, hsq, one_zsmul]
    _ = (ε : ℤ) • (η_ X Xᘁ ≫ X ◁ dagger r) := by
      rw [Preadditive.zsmul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end BraidedTensor

end TauCeti
