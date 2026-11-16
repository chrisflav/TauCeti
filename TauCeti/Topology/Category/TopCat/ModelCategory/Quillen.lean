/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import TauCeti.Topology.Category.TopCat.ModelCategory.TrivialFibration

/-!
# The Quillen–Serre model category structure on `TopCat`

This file constructs the Quillen–Serre (cofibrantly generated) model category structure on the
category `TopCat.{u}` of topological spaces:

* **weak equivalences**: the weak homotopy equivalences (`TauCeti.TopCat.weakEquivalences`);
* **fibrations**: the Serre fibrations (`TauCeti.TopCat.serreFibrations`), i.e. `J.rlp` where
  `J = {ι₀ : 𝔻 n ⟶ 𝔻 n ⊗ I | n : ℕ}`;
* **cofibrations**: `I.rlp.llp`, the retracts of relative `I`-cell complexes where
  `I = {∂𝔻 n ⟶ 𝔻 n | n : ℕ}`.

Following Mathlib's convention for `ModelCategory` instances on categories carrying more than one
model structure (such as `CochainComplex.Plus.modelCategoryQuillen`), the model category instances
are `scoped` inside `TauCeti.TopCat.modelCategoryQuillen`.

## Main declarations

* `TauCeti.TopCat.modelCategoryQuillen.modelCategory`: the scoped
  `HomotopicalAlgebra.ModelCategory TopCat.{u}` instance, together with the scoped
  `CategoryWithWeakEquivalences`, `CategoryWithFibrations`, `CategoryWithCofibrations`,
  `HasFunctorialFactorization`, and `IsWeakFactorizationSystem` instances.
* `TauCeti.TopCat.modelCategoryQuillen.trivialFibrations_eq` and
  `TauCeti.TopCat.modelCategoryQuillen.trivialCofibrations_eq`: identifications
  `trivialFibrations TopCat.{u} = I.rlp` and `trivialCofibrations TopCat.{u} = J.rlp.llp`.
* `TauCeti.TopCat.modelCategoryQuillen.isFibrant`: every topological space is fibrant.
* `TauCeti.TopCat.modelCategoryQuillen.isCofibrant_disk`: every Euclidean disk `𝔻 n` is cofibrant.
* `TauCeti.TopCat.modelCategoryQuillen.cofibrations_le_isClosedT1Inclusion`,
  `TauCeti.TopCat.modelCategoryQuillen.isClosedEmbedding_of_cofibration`, and
  `TauCeti.TopCat.modelCategoryQuillen.mono_of_cofibration`: every cofibration is a closed
  `T₁`-inclusion, in particular a closed embedding and a monomorphism.

## References

* D. G. Quillen, *Homotopical Algebra*, Lecture Notes in Mathematics 43, Springer (1967),
  Chapter II, Section 3.
* M. Hovey, *Model Categories*, AMS Mathematical Surveys and Monographs 63 (1999),
  Section 2.4 (Theorem 2.4.19).
-/

public section

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra MonoidalCategory
  CartesianMonoidalCategory

universe u

namespace TauCeti.TopCat.modelCategoryQuillen

/-- The weak equivalences in the Quillen–Serre model structure on `TopCat` are the weak homotopy
equivalences. -/
scoped instance categoryWithWeakEquivalences : CategoryWithWeakEquivalences TopCat.{u} where
  weakEquivalences := TauCeti.TopCat.weakEquivalences.{u}

/-- The fibrations in the Quillen–Serre model structure on `TopCat` are the Serre fibrations. -/
scoped instance categoryWithFibrations : CategoryWithFibrations TopCat.{u} where
  fibrations := TauCeti.TopCat.serreFibrations.{u}

/-- The cofibrations in the Quillen–Serre model structure on `TopCat` are the morphisms in
`I.rlp.llp` (equivalently, the retracts of relative `I`-cell complexes). -/
scoped instance categoryWithCofibrations : CategoryWithCofibrations TopCat.{u} where
  cofibrations := I.{u}.rlp.llp

/-- The weak equivalences of `TopCat` are `TauCeti.TopCat.weakEquivalences`. -/
lemma weakEquivalences_eq :
    HomotopicalAlgebra.weakEquivalences TopCat.{u} = TauCeti.TopCat.weakEquivalences.{u} :=
  rfl

/-- The fibrations of `TopCat` are `TauCeti.TopCat.serreFibrations`. -/
lemma fibrations_eq :
    HomotopicalAlgebra.fibrations TopCat.{u} = TauCeti.TopCat.serreFibrations.{u} :=
  rfl

/-- The cofibrations of `TopCat` are `I.rlp.llp`. -/
lemma cofibrations_eq :
    HomotopicalAlgebra.cofibrations TopCat.{u} = I.{u}.rlp.llp :=
  rfl

/-- A morphism in `TopCat` is a weak equivalence if and only if its underlying continuous map is a
weak homotopy equivalence. -/
lemma weakEquivalence_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ f.hom.IsWeakHomotopyEquivalence :=
  (HomotopicalAlgebra.weakEquivalence_iff f).trans (mem_weakEquivalences_iff f)

/-- A morphism in `TopCat` is a fibration if and only if it is a Serre fibration. -/
lemma fibration_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Fibration f ↔ TauCeti.TopCat.serreFibrations f :=
  HomotopicalAlgebra.fibration_iff f

/-- A morphism in `TopCat` is a cofibration if and only if it belongs to `I.rlp.llp`. -/
lemma cofibration_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Cofibration f ↔ I.{u}.rlp.llp f :=
  HomotopicalAlgebra.cofibration_iff f

/-- The trivial fibrations in the Quillen–Serre model structure on `TopCat` are precisely `I.rlp`.
-/
theorem trivialFibrations_eq :
    HomotopicalAlgebra.trivialFibrations TopCat.{u} = I.{u}.rlp :=
  rlp_I.symm

/-- A morphism in `TopCat` is a trivial fibration if and only if it belongs to `I.rlp`. -/
lemma mem_trivialFibrations_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    HomotopicalAlgebra.trivialFibrations TopCat.{u} f ↔ I.{u}.rlp f := by
  rw [trivialFibrations_eq]

scoped instance : (HomotopicalAlgebra.weakEquivalences TopCat.{u}).HasTwoOutOfThreeProperty :=
  inferInstanceAs TauCeti.TopCat.weakEquivalences.{u}.HasTwoOutOfThreeProperty

/-- The trivial cofibrations in the Quillen–Serre model structure on `TopCat` are precisely
`J.rlp.llp`. -/
theorem trivialCofibrations_eq :
    HomotopicalAlgebra.trivialCofibrations TopCat.{u} = J.{u}.rlp.llp := by
  refine le_antisymm ?_ (le_inf (antitone_llp rlp_I_le_rlp_J) llp_rlp_J_le_weakEquivalences)
  intro X Y f ⟨hfCof, hfW⟩
  let d := factorizationData J.{u}.rlp.llp J.{u}.rlp f
  have hdiW : TauCeti.TopCat.weakEquivalences d.i := llp_rlp_J_le_weakEquivalences _ d.hi
  have hdpW : TauCeti.TopCat.weakEquivalences d.p :=
    TauCeti.TopCat.weakEquivalences.of_precomp d.i d.p hdiW (d.fac.symm ▸ hfW)
  have hdp : I.{u}.rlp d.p := by
    rw [rlp_I]
    exact ⟨rlp_J ▸ d.hp, hdpW⟩
  have : HasLiftingProperty f d.p := hfCof d.p hdp
  exact of_retract (RetractArrow.ofLeftLiftingProperty d.fac) d.hi

/-- A morphism in `TopCat` is a trivial cofibration if and only if it belongs to `J.rlp.llp`. -/
lemma mem_trivialCofibrations_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    HomotopicalAlgebra.trivialCofibrations TopCat.{u} f ↔ J.{u}.rlp.llp f := by
  rw [trivialCofibrations_eq]

/-- Functorial factorization into a cofibration followed by a trivial fibration, produced by the
small object argument for `I`. -/
scoped instance hasFunctorialFactorization_cofibrations_trivialFibrations :
    (HomotopicalAlgebra.cofibrations TopCat.{u}).HasFunctorialFactorization
      (HomotopicalAlgebra.trivialFibrations TopCat.{u}) := by
  rw [cofibrations_eq, trivialFibrations_eq]
  infer_instance

/-- Functorial factorization into a trivial cofibration followed by a fibration, produced by the
small object argument for `J`. -/
scoped instance hasFunctorialFactorization_trivialCofibrations_fibrations :
    (HomotopicalAlgebra.trivialCofibrations TopCat.{u}).HasFunctorialFactorization
      (HomotopicalAlgebra.fibrations TopCat.{u}) := by
  rw [trivialCofibrations_eq, fibrations_eq, ← rlp_J]
  infer_instance

/-- Cofibrations and trivial fibrations form a weak factorization system on `TopCat`. -/
scoped instance isWeakFactorizationSystem_cofibrations_trivialFibrations :
    IsWeakFactorizationSystem (HomotopicalAlgebra.cofibrations TopCat.{u})
      (HomotopicalAlgebra.trivialFibrations TopCat.{u}) where
  rlp := by rw [cofibrations_eq, trivialFibrations_eq, rlp_llp_rlp]
  llp := by rw [cofibrations_eq, trivialFibrations_eq]

/-- Trivial cofibrations and fibrations form a weak factorization system on `TopCat`. -/
scoped instance isWeakFactorizationSystem_trivialCofibrations_fibrations :
    IsWeakFactorizationSystem (HomotopicalAlgebra.trivialCofibrations TopCat.{u})
      (HomotopicalAlgebra.fibrations TopCat.{u}) where
  rlp := by rw [trivialCofibrations_eq, fibrations_eq, ← rlp_J, rlp_llp_rlp]
  llp := by rw [trivialCofibrations_eq, fibrations_eq, ← rlp_J]

/-- **The Quillen–Serre model category structure on `TopCat.{u}`.** Weak equivalences are weak
homotopy equivalences, fibrations are Serre fibrations, and cofibrations are retracts of relative
cell complexes built from the disk boundary inclusions `∂𝔻 n ⟶ 𝔻 n`. -/
scoped instance modelCategory : ModelCategory TopCat.{u} :=
  ModelCategory.mk' TopCat.{u}

/-- Every topological space is fibrant in the Quillen–Serre model structure on `TopCat`. -/
scoped instance isFibrant (X : TopCat.{u}) : IsFibrant X := by
  rw [isFibrant_iff, fibration_iff, mem_serreFibrations_iff_hasLiftingProperty]
  intro n
  refine ⟨fun {f g} _ ↦ ⟨⟨{
    l := fst (TopCat.disk.{u} n) TopCat.I ≫ f
    fac_left := by rw [← Category.assoc, TopCat.ι₀_fst, Category.id_comp]
    fac_right := terminal.hom_ext _ _ }⟩⟩⟩

/-- Every disk boundary inclusion `∂𝔻 n ⟶ 𝔻 n` is a cofibration. -/
scoped instance cofibration_diskBoundaryInclusion (n : ℕ) :
    Cofibration (TopCat.diskBoundaryInclusion.{u} n) :=
  (cofibration_iff _).2 (le_llp_rlp I.{u} _ (diskBoundaryInclusion_mem_I n))

/-- Every cylinder bottom inclusion `ι₀ : 𝔻 n ⟶ 𝔻 n ⊗ I` is a trivial cofibration. -/
theorem mem_trivialCofibrations_ι₀_disk (n : ℕ) :
    HomotopicalAlgebra.trivialCofibrations TopCat.{u}
      (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I) :=
  (mem_trivialCofibrations_iff _).2 (le_llp_rlp J.{u} _ (ι₀_disk_mem_J n))

/-- Every cylinder bottom inclusion `ι₀ : 𝔻 n ⟶ 𝔻 n ⊗ I` is a cofibration. -/
scoped instance cofibration_ι₀_disk (n : ℕ) :
    Cofibration (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I) :=
  (HomotopicalAlgebra.mem_trivialCofibrations_iff _).1 (mem_trivialCofibrations_ι₀_disk n) |>.1

/-- Every cylinder bottom inclusion `ι₀ : 𝔻 n ⟶ 𝔻 n ⊗ I` is a weak equivalence. -/
scoped instance weakEquivalence_ι₀_disk (n : ℕ) :
    WeakEquivalence (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I) :=
  (HomotopicalAlgebra.mem_trivialCofibrations_iff _).1 (mem_trivialCofibrations_ι₀_disk n) |>.2

/-- Every Euclidean disk `𝔻 n` is cofibrant in the Quillen–Serre model structure on `TopCat`. -/
scoped instance isCofibrant_disk : ∀ n : ℕ, IsCofibrant (TopCat.disk.{u} n)
  | 0 => by
    have hEmpty : IsEmpty (TopCat.diskBoundary.{u} 0) := isEmpty_diskBoundary_zero
    have hInit : IsInitial (TopCat.diskBoundary.{u} 0) :=
      IsInitial.ofUniqueHom (fun X ↦ TopCat.ofHom ⟨hEmpty.elim, continuous_of_discreteTopology⟩)
        (fun _ _ ↦ TopCat.ext hEmpty.elim)
    exact (isCofibrant_iff_of_isInitial (TopCat.diskBoundaryInclusion.{u} 0) hInit).2 inferInstance
  | n + 1 => by
    have : IsCofibrant (TopCat.disk.{u} n) := isCofibrant_disk n
    have : IsCofibrant (TopCat.disk.{u} n ⊗ TopCat.I) :=
      isCofibrant_of_cofibration (TopCat.ι₀ : TopCat.disk.{u} n ⟶ TopCat.disk n ⊗ TopCat.I)
    let e : (TopCat.disk.{u} n ⊗ TopCat.I : TopCat.{u}) ≃ₜ TopCat.disk.{u} (n + 1) :=
      ((Homeomorph.prodCongr (diskHomeomorphCube.{u} n) TopCat.I.homeomorph).trans
        (Homeomorph.prodComm _ _)).trans
        ((cubeSplitHomeomorph n).symm.trans (diskHomeomorphCube.{u} (n + 1)).symm)
    have : Cofibration (TopCat.isoOfHomeo e).hom :=
      (cofibration_iff _).2 ((HomotopicalAlgebra.cofibrations TopCat.{u}).of_isIso _)
    exact isCofibrant_of_cofibration (TopCat.isoOfHomeo e).hom

/-- Every cofibration in the Quillen–Serre model structure on `TopCat` is a closed `T₁`-inclusion.
-/
theorem cofibrations_le_isClosedT1Inclusion :
    HomotopicalAlgebra.cofibrations TopCat.{u} ≤ isClosedT1Inclusion.{u} := by
  have := Cardinal.fact_isRegular_aleph0.{u}
  have := Cardinal.orderBotAleph0OrdToType.{u}
  rw [cofibrations_eq, SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0 I.{u},
    retracts_le_iff]
  exact le_trans (transfiniteCompositionsOfShape_monotone ℕ
    (pushouts_le_iff.2 (coproducts_le_iff.2 I_le_isClosedT1Inclusion)))
    (isClosedT1Inclusion.transfiniteCompositionsOfShape_le ℕ)

/-- Every cofibration in `TopCat` is a closed `T₁`-inclusion. -/
theorem isClosedT1Inclusion_of_cofibration {X Y : TopCat.{u}} (f : X ⟶ Y) [Cofibration f] :
    isClosedT1Inclusion f :=
  cofibrations_le_isClosedT1Inclusion f (mem_cofibrations f)

/-- Every cofibration in `TopCat` is a closed embedding. -/
theorem isClosedEmbedding_of_cofibration {X Y : TopCat.{u}} (f : X ⟶ Y) [Cofibration f] :
    Topology.IsClosedEmbedding f :=
  (isClosedEmbedding_iff f).1
    (isClosedT1Inclusion_le_isClosedEmbedding f (isClosedT1Inclusion_of_cofibration f))

/-- Every cofibration in `TopCat` is a monomorphism. -/
scoped instance mono_of_cofibration {X Y : TopCat.{u}} (f : X ⟶ Y) [Cofibration f] : Mono f :=
  (TopCat.mono_iff_injective f).2 (isClosedEmbedding_of_cofibration f).injective

end TauCeti.TopCat.modelCategoryQuillen
