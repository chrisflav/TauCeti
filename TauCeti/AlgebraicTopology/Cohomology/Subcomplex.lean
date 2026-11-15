/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex

/-!
# The small-cochain theorem on affinely stable subcomplexes

Let `S` be an affinely stable subcomplex of the singular simplicial set of a space `X`
(`SSet.Subcomplex.IsAffineStable`), such as the smooth singular simplices of a charted space, and
let `U` be an open cover of `X`. Applying the contravariant functor `Hom(-, M)` to the chain
homotopy equivalence `TauCeti.subcomplexSmallChainHomotopyEquiv` shows that restricting cochains of
`S` to the simplices of `S` subordinate to `U` is a cochain homotopy equivalence, and hence an
isomorphism on cohomology and a quasi-isomorphism of cochain complexes.

## Main declarations

* `TauCeti.subcomplexSmallCochainHomotopyEquiv`: restricting cochains of `S` to the simplices of
  `S` subordinate to an open cover is a cochain homotopy equivalence, whose homotopy inverse is a
  strict section (`TauCeti.subcomplexSmallCochainHomotopyEquiv_inv_comp_cochainComplexMap`).
* `TauCeti.subcomplexSmallCohomologyIso`: the induced isomorphism on cohomology, natural under maps
  compatible with the inclusions (`TauCeti.subcomplexSmallCohomologyIso_naturality`).
* `TauCeti.quasiIso_cochainComplexMap_homOfLE_inf_smallSingularSubcomplex`: that restriction of
  cochains is a quasi-isomorphism.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7 and
  Theorem 18.14.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology SSet.Subcomplex

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {X : TopCat.{w}} (S : (TopCat.toSSet.obj X).Subcomplex) [S.IsAffineStable]
  {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)

/-- **The small-cochain theorem on an affinely stable subcomplex.** For an open cover `U` of `X`
and an affinely stable subcomplex `S` of the singular simplicial set of `X`, restricting cochains
of `S` to the simplices of `S` subordinate to `U` is a cochain homotopy equivalence, dual to
`TauCeti.subcomplexSmallChainHomotopyEquiv`. -/
def subcomplexSmallCochainHomotopyEquiv :
    HomotopyEquiv (((S : SSet).chainComplex R).linearYonedaObj k M)
      ((((S ⊓ X.smallSingularSubcomplex U : (TopCat.toSSet.obj X).Subcomplex) : SSet).chainComplex
        R).linearYonedaObj k M) :=
  (subcomplexSmallChainHomotopyEquiv R S U hU hcov).linearYonedaFunctorMap k M

/-- The forward map of the small-cochain homotopy equivalence of an affinely stable subcomplex is
restriction along the inclusion of the simplices subordinate to the cover. -/
@[simp]
lemma subcomplexSmallCochainHomotopyEquiv_hom :
    (subcomplexSmallCochainHomotopyEquiv R k M S U hU hcov).hom =
      SSet.cochainComplexMap (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) :=
  ((subcomplexSmallChainHomotopyEquiv R S U hU hcov).linearYonedaFunctorMap_hom k M).trans
    (congrArg (fun f ↦ (ChainComplex.linearYonedaFunctor k M).map (Quiver.Hom.op f))
      (subcomplexSmallChainHomotopyEquiv_hom R S U hU hcov))

/-- The homotopy inverse of the small-cochain homotopy equivalence of an affinely stable subcomplex
is a strict section of restriction to the simplices subordinate to the cover. -/
@[reassoc (attr := simp)]
lemma subcomplexSmallCochainHomotopyEquiv_inv_comp_cochainComplexMap :
    (subcomplexSmallCochainHomotopyEquiv R k M S U hU hcov).inv ≫
      SSet.cochainComplexMap (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) =
        𝟙 _ :=
  (congrArg (· ≫ SSet.cochainComplexMap (R := R) (k := k) (M := M) _)
    ((subcomplexSmallChainHomotopyEquiv R S U hU hcov).linearYonedaFunctorMap_inv k M)).trans <| by
    have h := congrArg (fun f ↦ (ChainComplex.linearYonedaFunctor k M).map (Quiver.Hom.op f))
      (chainComplexMap_comp_subcomplexSmallChainHomotopyEquiv_inv R S U hU hcov)
    rwa [op_comp, CategoryTheory.Functor.map_comp, op_id, CategoryTheory.Functor.map_id] at h

/-- The isomorphism on cohomology induced by restricting cochains of an affinely stable subcomplex
to its simplices subordinate to an open cover, dual to `TauCeti.subcomplexSmallHomologyIso`. -/
def subcomplexSmallCohomologyIso (n : ℕ) :
    (((S : SSet).chainComplex R).linearYonedaObj k M).homology n ≅
      ((((S ⊓ X.smallSingularSubcomplex U : (TopCat.toSSet.obj X).Subcomplex) : SSet).chainComplex
        R).linearYonedaObj k M).homology n :=
  (subcomplexSmallCochainHomotopyEquiv R k M S U hU hcov).toHomologyIso n

/-- The forward map of the small-cochain cohomology isomorphism is induced by restriction to the
simplices subordinate to the cover. -/
@[simp]
lemma subcomplexSmallCohomologyIso_hom (n : ℕ) :
    (subcomplexSmallCohomologyIso R k M S U hU hcov n).hom =
      HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)))
        n := by
  simp [subcomplexSmallCohomologyIso, HomotopyEquiv.toHomologyIso]

/-- The small-cochain cohomology isomorphism of an affinely stable subcomplex is natural under maps
of simplicial sets compatible with the inclusions of the simplices subordinate to the covers. -/
@[reassoc]
lemma subcomplexSmallCohomologyIso_naturality
    {Y : TopCat.{w}} (S' : (TopCat.toSSet.obj Y).Subcomplex) [S'.IsAffineStable]
    {κ : Type*} (V : κ → Set Y) (hV : ∀ j, IsOpen (V j)) (hcovV : ⋃ j, V j = Set.univ)
    (f : ((S ⊓ X.smallSingularSubcomplex U : (TopCat.toSSet.obj X).Subcomplex) : SSet) ⟶
      ((S' ⊓ Y.smallSingularSubcomplex V : (TopCat.toSSet.obj Y).Subcomplex) : SSet))
    (g : (S : SSet) ⟶ (S' : SSet))
    (hfg : f ≫ homOfLE inf_le_left = homOfLE inf_le_left ≫ g) (n : ℕ) :
    HomologicalComplex.homologyMap (SSet.cochainComplexMap g) n ≫
        (subcomplexSmallCohomologyIso R k M S U hU hcov n).hom =
      (subcomplexSmallCohomologyIso R k M S' V hV hcovV n).hom ≫
        HomologicalComplex.homologyMap (SSet.cochainComplexMap f) n := by
  rw [subcomplexSmallCohomologyIso_hom, subcomplexSmallCohomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← SSet.cochainComplexMap_comp, ← SSet.cochainComplexMap_comp, hfg]

include hU hcov in
/-- Restricting cochains of an affinely stable subcomplex to its simplices subordinate to an open
cover is a quasi-isomorphism. -/
theorem quasiIso_cochainComplexMap_homOfLE_inf_smallSingularSubcomplex :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S))) := by
  rw [← subcomplexSmallCochainHomotopyEquiv_hom R k M S U hU hcov]
  exact (subcomplexSmallCochainHomotopyEquiv R k M S U hU hcov).quasiIso_hom

end TauCeti
