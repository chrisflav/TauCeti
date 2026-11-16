/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic

/-!
# Coefficient pairings on relative simplicial chains

Let `C` be an abelian monoidal category with `w`-small coproducts, and let `M` be an object of `C`
such that `M ⊗ -` preserves `w`-small coproducts.  A coefficient pairing `μ : M ⊗ S ⟶ N` induces
the chain map `M ⊗ C(Y; S) ⟶ C(Y; N)` of `SSet.chainComplexPairing` on the chains of a simplicial
set `Y`, which sends the summand of a simplex to the summand of the same simplex.  For a pair
`X ⟶ Y` of simplicial sets it therefore carries `M ⊗ C(X; S)` into `C(X; N)`, and descends to a
chain map `SSetPair.chainComplexPairing : M ⊗ C(Y, X; S) ⟶ C(Y, X; N)` on relative chains.

The descent uses that `M ⊗ -` preserves the cokernel `C(Y, X; S)` of `C(X; S) ⟶ C(Y; S)`.  No
hypothesis on `M` beyond the preservation of coproducts is needed for this: in each degree the
short exact sequence `0 ⟶ C(X) ⟶ C(Y) ⟶ C(Y, X) ⟶ 0` splits (`SSetPair.chainComplexXSplitting`),
since `C(X) ⟶ C(Y)` is induced by the injection of the simplices of `X` into those of `Y`, and the
additive functor `M ⊗ -` preserves split short exact sequences.

This is how the coefficients of an absolute cochain act on relative chains in the cap product
`Hᵖ(Y) ⊗ Hₙ(Y, X) ⟶ H_q(Y, X)`.

## Main definitions and results

* `SSetPair.chainComplexPairing`: the chain map `M ⊗ C(Y, X; S) ⟶ C(Y, X; N)` induced by `μ`.
* `SSetPair.chainComplexπ_chainComplexPairing`: it is the descent of
  `SSet.chainComplexPairing μ` along the quotient maps to relative chains.
* `SSetPair.chainComplexPairing_naturality`: it is natural in the pair.
* `SSetPair.isIso_chainComplexPairing`: it is an isomorphism whenever `μ` is.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace SSetPair

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {M S N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- The chain map `M ⊗ C(Y; S) ⟶ C(Y; N)` induced by a coefficient pairing, followed by the
quotient map to relative chains, vanishes on `M ⊗ C(X; S)`. -/
private lemma whiskerLeft_chainComplexMap_f_comp_chainComplexPairing_f_comp_chainComplexπ_f
    (P : SSetPair.{w}) (μ : M ⊗ S ⟶ N) (n : ℕ) :
    (M ◁ (SSet.chainComplexMap P.hom S).f n) ≫ (P.right.chainComplexPairing μ).f n ≫
      (P.chainComplexπ N).f n = 0 := by
  have h := congrArg (fun φ ↦ φ.f n) (SSet.chainComplexPairing_naturality P.hom μ)
  dsimp at h
  rw [reassoc_of% h, chainComplex_condition_f, comp_zero]

/-- The degree-`n` component of `SSetPair.chainComplexPairing`. -/
private def chainComplexPairingX (P : SSetPair.{w}) (μ : M ⊗ S ⟶ N) (n : ℕ) :
    M ⊗ (P.chainComplex S).X n ⟶ (P.chainComplex N).X n :=
  (CokernelCofork.IsColimit.desc'
    (((chainComplexXSplitting S P n).map (tensorLeft M)).gIsCokernel)
    ((P.right.chainComplexPairing μ).f n ≫ (P.chainComplexπ N).f n)
    (whiskerLeft_chainComplexMap_f_comp_chainComplexPairing_f_comp_chainComplexπ_f P μ n)).1

@[reassoc]
private lemma whiskerLeft_chainComplexπ_f_chainComplexPairingX (P : SSetPair.{w})
    (μ : M ⊗ S ⟶ N) (n : ℕ) :
    (M ◁ (P.chainComplexπ S).f n) ≫ chainComplexPairingX P μ n =
      (P.right.chainComplexPairing μ).f n ≫ (P.chainComplexπ N).f n :=
  (CokernelCofork.IsColimit.desc'
    (((chainComplexXSplitting S P n).map (tensorLeft M)).gIsCokernel) _
    (whiskerLeft_chainComplexMap_f_comp_chainComplexPairing_f_comp_chainComplexπ_f P μ n)).2

instance epi_whiskerLeft_chainComplexπ_f (P : SSetPair.{w}) (S : C) (n : ℕ) :
    Epi (M ◁ (P.chainComplexπ S).f n) :=
  ((chainComplexXSplitting S P n).map (tensorLeft M)).epi_g

/-- **The chain map induced by a coefficient pairing on relative chains**: for a pair `X ⟶ Y` of
simplicial sets and `μ : M ⊗ S ⟶ N`, the chain map `M ⊗ C(Y, X; S) ⟶ C(Y, X; N)` through which the
chain map `SSet.chainComplexPairing μ` of `Y`, followed by the quotient map to relative chains,
descends (`SSetPair.chainComplexπ_chainComplexPairing`). -/
def chainComplexPairing (P : SSetPair.{w}) (μ : M ⊗ S ⟶ N) :
    ((tensorLeft M).mapHomologicalComplex _).obj (P.chainComplex S) ⟶ P.chainComplex N where
  f n := chainComplexPairingX P μ n
  comm' i j _ := by
    have hπ : (M ◁ (P.chainComplexπ S).f i) ≫ (M ◁ (P.chainComplex S).d i j) =
        (M ◁ (P.right.chainComplex S).d i j) ≫ (M ◁ (P.chainComplexπ S).f j) := by
      simp only [← whiskerLeft_comp, HomologicalComplex.Hom.comm]
    have hμ := (P.right.chainComplexPairing μ).comm i j
    dsimp at hμ ⊢
    rw [← cancel_epi (M ◁ (P.chainComplexπ S).f i)]
    simp [whiskerLeft_chainComplexπ_f_chainComplexPairingX,
      whiskerLeft_chainComplexπ_f_chainComplexPairingX_assoc, reassoc_of% hπ, reassoc_of% hμ]

/-- The chain map induced by a coefficient pairing on relative chains is, in each degree, the
descent of the chain map `SSet.chainComplexPairing μ` of the ambient simplicial set, followed by
the quotient map to relative chains. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_chainComplexπ_f_chainComplexPairing_f (P : SSetPair.{w}) (μ : M ⊗ S ⟶ N)
    (n : ℕ) :
    (M ◁ (P.chainComplexπ S).f n) ≫ (P.chainComplexPairing μ).f n =
      (P.right.chainComplexPairing μ).f n ≫ (P.chainComplexπ N).f n :=
  whiskerLeft_chainComplexπ_f_chainComplexPairingX P μ n

/-- The chain map induced by a coefficient pairing on relative chains is the descent of the chain
map `SSet.chainComplexPairing μ` of the ambient simplicial set, followed by the quotient map to
relative chains. -/
@[reassoc]
lemma chainComplexπ_chainComplexPairing (P : SSetPair.{w}) (μ : M ⊗ S ⟶ N) :
    ((tensorLeft M).mapHomologicalComplex _).map (P.chainComplexπ S) ≫ P.chainComplexPairing μ =
      P.right.chainComplexPairing μ ≫ P.chainComplexπ N := by
  ext n : 1
  exact whiskerLeft_chainComplexπ_f_chainComplexPairing_f P μ n

/-- The chain map induced by a coefficient pairing on relative chains is natural in the pair. -/
@[reassoc]
lemma chainComplexPairing_naturality {P P' : SSetPair.{w}} (f : P ⟶ P') (μ : M ⊗ S ⟶ N) :
    ((tensorLeft M).mapHomologicalComplex _).map (SSetPair.chainComplexMap f S) ≫
        P'.chainComplexPairing μ =
      P.chainComplexPairing μ ≫ SSetPair.chainComplexMap f N := by
  ext n : 1
  have hS : (M ◁ (P.chainComplexπ S).f n) ≫ (M ◁ (SSetPair.chainComplexMap f S).f n) =
      (M ◁ (SSet.chainComplexMap f.right S).f n) ≫ (M ◁ (P'.chainComplexπ S).f n) := by
    simp only [← whiskerLeft_comp, ← HomologicalComplex.comp_f, chainComplexπ_naturality]
  have hN := congrArg (fun φ ↦ φ.f n) (chainComplexπ_naturality N f)
  have hμ := congrArg (fun φ ↦ φ.f n) (SSet.chainComplexPairing_naturality f.right μ)
  dsimp at hN hμ ⊢
  rw [← cancel_epi (M ◁ (P.chainComplexπ S).f n)]
  simp [reassoc_of% hS, reassoc_of% hμ, hN]

/-- The chain map induced by an invertible coefficient pairing on relative chains is an
isomorphism. -/
instance isIso_chainComplexPairing (P : SSetPair.{w}) (μ : M ⊗ S ⟶ N) [IsIso μ] :
    IsIso (P.chainComplexPairing μ) := by
  have : ∀ n, IsIso ((P.chainComplexPairing μ).f n) := fun n ↦ by
    have hzero : (SSet.chainComplexMap P.hom N).f n ≫ inv ((P.right.chainComplexPairing μ).f n) ≫
        (M ◁ (P.chainComplexπ S).f n) = 0 := by
      rw [← cancel_epi ((P.left.chainComplexPairing μ).f n), comp_zero]
      have hnat := congrArg (fun φ ↦ φ.f n) (SSet.chainComplexPairing_naturality P.hom μ)
      dsimp at hnat
      rw [← Category.assoc, ← Category.assoc, ← hnat, Category.assoc, Category.assoc,
        IsIso.hom_inv_id_assoc, ← whiskerLeft_comp, chainComplex_condition_f,
        MonoidalPreadditive.whiskerLeft_zero]
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' (chainComplexXSplitting N P n).gIsCokernel
      (inv ((P.right.chainComplexPairing μ).f n) ≫ (M ◁ (P.chainComplexπ S).f n)) hzero
    dsimp at hg
    refine ⟨⟨g, ?_, ?_⟩⟩
    · rw [← cancel_epi (M ◁ (P.chainComplexπ S).f n)]
      dsimp
      rw [Category.comp_id, whiskerLeft_chainComplexπ_f_chainComplexPairing_f_assoc, hg,
        IsIso.hom_inv_id_assoc]
    · rw [← cancel_epi ((P.chainComplexπ N).f n), Category.comp_id, reassoc_of% hg,
        whiskerLeft_chainComplexπ_f_chainComplexPairing_f, IsIso.inv_hom_id_assoc]
  exact HomologicalComplex.Hom.isIso_of_components _

end SSetPair
