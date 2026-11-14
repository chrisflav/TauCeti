/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.Algebra.Homology.LinearYoneda
import Mathlib.Algebra.Category.ModuleCat.Abelian
import TauCeti.Algebra.Homology.HomologySequenceLemmas
import TauCeti.Algebra.Homology.HomotopyCofiber

/-!
# Chain maps from K-projective complexes and detection of quasi-isomorphisms by `Hom(-, Y)`

A morphism in the derived category from a K-projective complex can be represented by a
chain map. This is the chain-level form of Mathlib's
`CochainComplex.IsKProjective.Qh_map_bijective`, and lets one form mapping cones of derived
morphisms using specified projective models.

A quasi-isomorphism between `ℕ`-graded chain complexes of projective objects is a chain homotopy
equivalence (Mathlib's `ChainComplex.quasiIso_iff_of_projective`). So the contravariant functor
`Hom(-, Y)` takes it to a cochain homotopy equivalence, and in particular to a quasi-isomorphism
(`ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective`,
`ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective`). This is how a map of spaces
inducing isomorphisms on homology with projective chain coefficients is seen to induce
isomorphisms on cohomology with values in every coefficient object.

Conversely, without any projectivity hypothesis, exactness of `Hom(K, Y)` in degree `i` for every
object `Y` forces `K` to be exact in degree `i`
(`ChainComplex.exactAt_of_forall_exactAt_linearYonedaObj`, testing `Y` on the cokernel of the
incoming differential of `K`), and a chain map `φ : K ⟶ L` of `ℕ`-graded chain complexes whose
pullback on `Hom(-, Y)` is a quasi-isomorphism for every `Y` is itself a quasi-isomorphism
(`ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor_map`, via the degreewise split cone
short exact sequence of `φ`). Combining the two directions characterizes quasi-isomorphisms and
chain homotopy equivalences between `ℕ`-graded chain complexes of projective objects by their
effect on `Hom(-, Y)`.

## Main results

* `CochainComplex.IsKProjective.Q_map_surjective`: every derived morphism out of a K-projective
  cochain complex is represented by a cochain map.
* `ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective`,
  `ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective`: `Hom(-, Y)` sends a
  quasi-isomorphism between `ℕ`-graded chain complexes of projectives to a cochain homotopy
  equivalence and hence a quasi-isomorphism.
* `ChainComplex.exactAt_of_forall_exactAt_linearYonedaObj`,
  `ChainComplex.acyclic_of_forall_acyclic_linearYonedaObj`: exactness (and acyclicity) of an
  `ℕ`-graded chain complex is detected by `Hom(-, Y)` across all objects `Y`.
* `ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor_map`: a chain map of `ℕ`-graded
  chain complexes inducing quasi-isomorphisms on `Hom(-, Y)` for all `Y` is a quasi-isomorphism.
* `ChainComplex.quasiIso_iff_forall_quasiIso_linearYonedaFunctor_map_of_projective`,
  `ChainComplex.homotopyEquivalences_iff_forall_quasiIso_linearYonedaFunctor_map_of_projective`:
  characterizations of quasi-isomorphisms and chain homotopy equivalences between `ℕ`-graded chain
  complexes of projective objects via `Hom(-, Y)`.

## References

* [Charles A. Weibel, *An Introduction to Homological Algebra*][weibel1994], Section 1.5.
* [The Stacks Project, Tag 0649](https://stacks.math.columbia.edu/tag/0649).
-/

public section

open CategoryTheory DerivedCategory

namespace CochainComplex.IsKProjective

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Every derived morphism from a K-projective complex is represented by a chain map. -/
theorem Q_map_surjective (K L : CochainComplex C ℤ) [K.IsKProjective] :
    Function.Surjective (Q.map : (K ⟶ L) → (Q.obj K ⟶ Q.obj L)) := by
  intro f
  obtain ⟨g, hg⟩ := (Qh_map_bijective K ((HomotopyCategory.quotient _ _).obj L)).surjective
    ((quotientCompQhIso C).hom.app K ≫ f ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((quotientCompQhIso C).hom.app K),
    ← quotientCompQhIso_hom_naturality, hg]
  simp

end CochainComplex.IsKProjective

namespace ChainComplex

open HomologicalComplex Opposite

section Converse

variable {C : Type*} [Category* C] [Abelian C]

/-- An `ℕ`-graded chain complex `K` in a `k`-linear abelian category is exact in degree `i`
whenever `Hom(K, Y)` is exact in degree `i` for every object `Y` (taking `Y` to be the cokernel
of the incoming differential of `K`). -/
theorem exactAt_of_forall_exactAt_linearYonedaObj (k : Type*) [Ring k] [Linear k C]
    (K : ChainComplex C ℕ) (i : ℕ) (h : ∀ Y : C, (K.linearYonedaObj k Y).ExactAt i) :
    K.ExactAt i := by
  cases i with
  | zero =>
    rw [exactAt_iff' _ 1 0 0 (by simp) next_nat_zero,
      ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
    have h0 : Limits.cokernel.π (K.d 1 0) = 0 :=
      (exactAt_linearYonedaObj_zero_iff k K _).1 (h _) _ (Limits.cokernel.condition _)
    simp [h0]
  | succ n =>
    rw [exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
      ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
    obtain ⟨g, hg⟩ := (exactAt_linearYonedaObj_succ_iff k K _ n).1 (h _)
      (Limits.cokernel.π (K.d (n + 2) (n + 1))) (Limits.cokernel.condition _)
    simp [← hg]

/-- An `ℕ`-graded chain complex `K` in a `k`-linear abelian category is acyclic whenever
`Hom(K, Y)` is acyclic for every object `Y`. -/
theorem acyclic_of_forall_acyclic_linearYonedaObj (k : Type*) [Ring k] [Linear k C]
    (K : ChainComplex C ℕ) (h : ∀ Y : C, (K.linearYonedaObj k Y).Acyclic) :
    K.Acyclic :=
  fun i ↦ exactAt_of_forall_exactAt_linearYonedaObj k K i fun Y ↦ h Y i

/-- **Converse detection of quasi-isomorphisms by `Hom(-, Y)`.** If a morphism `φ : K ⟶ L` of
`ℕ`-graded chain complexes in a `k`-linear abelian category induces a quasi-isomorphism
`Hom(L, Y) ⟶ Hom(K, Y)` for every object `Y`, then `φ` itself is a quasi-isomorphism. No
projectivity hypothesis on the terms of `K` or `L` is needed. -/
theorem quasiIso_of_forall_quasiIso_linearYonedaFunctor_map {K L : ChainComplex C ℕ}
    (φ : K ⟶ L) (k : Type*) [Ring k] [Linear k C]
    (h : ∀ Y : C, QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op)) :
    QuasiIso φ := by
  let hc : ∀ j : ℕ, ∃ i : ℕ, (ComplexShape.down ℕ).Rel i j := fun j ↦ ⟨j + 1, rfl⟩
  let α : Arrow.mk (𝟙 K) ⟶ Arrow.mk φ := Arrow.homMk (𝟙 K) φ
  -- The morphism of cone short exact sequences induced by `(𝟙 K, φ) : 𝟙 K ⟶ φ`.
  let μ : homotopyCofiber.coneShortComplex (𝟙 K) hc ⟶ homotopyCofiber.coneShortComplex φ hc :=
    { τ₁ := φ
      τ₂ := homotopyCofiber.mapArrowHom (𝟙 K) φ hc α
      τ₃ := 𝟙 _
      comm₁₂ := by simp [α]
      comm₂₃ := by
        rw [Category.comp_id, ← homotopyCofiber.mapArrowHom_comp]
        congr 1
        ext <;> simp [α] }
  have hS_id : (homotopyCofiber.coneShortComplex (𝟙 K) hc).ShortExact :=
    homotopyCofiber.coneShortComplex_shortExact (𝟙 K) hc
  have hS_φ : (homotopyCofiber.coneShortComplex φ hc).ShortExact :=
    homotopyCofiber.coneShortComplex_shortExact φ hc
  -- First show that the mapping cone of `φ` is acyclic by testing against every object `Y`.
  have hcone_acyclic : (homotopyCofiber φ).Acyclic := by
    refine acyclic_of_forall_acyclic_linearYonedaObj k (homotopyCofiber φ) fun Y ↦ ?_
    have : ∀ i, IsSplitMono ((homotopyCofiber.coneShortComplex (𝟙 K) hc).f.f i) :=
      fun i ↦ ⟨⟨{ retraction := homotopyCofiber.sndX (𝟙 K) i, id := by simp }⟩⟩
    have : ∀ i, IsSplitMono ((homotopyCofiber.coneShortComplex φ hc).f.f i) :=
      fun i ↦ ⟨⟨{ retraction := homotopyCofiber.sndX φ i, id := by simp }⟩⟩
    have hY_id := TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k Y hS_id
    have hY_φ := TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k Y hS_φ
    let νY : (homotopyCofiber.coneShortComplex φ hc).op.map
        (TauCeti.ChainComplex.linearYonedaFunctor k Y) ⟶
      (homotopyCofiber.coneShortComplex (𝟙 K) hc).op.map
        (TauCeti.ChainComplex.linearYonedaFunctor k Y) :=
      ((TauCeti.ChainComplex.linearYonedaFunctor k Y).mapShortComplex).map (ShortComplex.opMap μ)
    have hτ₁ : QuasiIso νY.τ₁ := by
      have h1 : νY.τ₁ = 𝟙 _ := (TauCeti.ChainComplex.linearYonedaFunctor k Y).map_id _
      have : IsIso νY.τ₁ := ⟨⟨𝟙 _, by rw [h1]; exact Category.id_comp _,
        by rw [h1]; exact Category.id_comp _⟩⟩
      exact quasiIso_of_isIso νY.τ₁
    have hτ₃ : QuasiIso νY.τ₃ := h Y
    have hτ₂ : QuasiIso νY.τ₂ := HomologySequence.quasiIso_τ₂ νY hY_φ hY_id hτ₁ hτ₃
    let C_id : ChainComplex C ℕ := homotopyCofiber (𝟙 K)
    have h_id_acyclic : ((TauCeti.ChainComplex.linearYonedaFunctor k Y).obj (op C_id)).Acyclic := by
      have hz : (TauCeti.ChainComplex.linearYonedaFunctor k Y).map (0 : C_id ⟶ C_id).op = 0 := by
        rw [Limits.op_zero, Functor.map_zero]
      exact ((Homotopy.ofEq ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map_id _).symm).trans
        (((homotopyCofiber.homotopyToZeroOfId K hc).linearYonedaFunctorMap k Y).trans
          (Homotopy.ofEq hz))).acyclic
    intro i
    have h_iso : IsIso (homologyMap νY.τ₂ i) :=
      (quasiIsoAt_iff_isIso_homologyMap νY.τ₂ i).1 (hτ₂.1 i)
    rw [exactAt_iff_isZero_homology]
    exact (h_id_acyclic i).isZero_homology.of_iso (@asIso _ _ _ _ (homologyMap νY.τ₂ i) h_iso)
  -- Both middle terms `homotopyCofiber (𝟙 K)` and `homotopyCofiber φ` in `μ` are acyclic, so `μ.τ₂`
  -- is a quasi-isomorphism; since `μ.τ₃ = 𝟙`, two-out-of-three for `τ₁` gives `QuasiIso φ`.
  have hμ₂ : QuasiIso μ.τ₂ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ((homotopyCofiber.acyclic_id K hc i).isZero_homology).isIso
      (hcone_acyclic i).isZero_homology _
  exact HomologySequence.quasiIso_τ₁ μ hS_id hS_φ hμ₂ (inferInstanceAs (QuasiIso (𝟙 _)))

end Converse

section Projective

variable {C : Type*} [Category* C] [Abelian C] {K L : ChainComplex C ℕ}
  [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]

/-- A quasi-isomorphism `φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects induces a
cochain homotopy equivalence `Hom(L, Y) ⟶ Hom(K, Y)` by precomposition, for every object `Y`. -/
theorem homotopyEquivalences_linearYonedaFunctor_map_of_projective (φ : K ⟶ L) [QuasiIso φ]
    (k : Type*) [Ring k] [Linear k C] (Y : C) :
    homotopyEquivalences _ _ ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) := by
  obtain ⟨e, he⟩ := (quasiIso_iff_of_projective φ).1 ‹_›
  exact ⟨e.linearYonedaFunctorMap k Y, by rw [HomotopyEquiv.linearYonedaFunctorMap_hom, he]⟩

/-- A quasi-isomorphism `φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects induces a
quasi-isomorphism `Hom(L, Y) ⟶ Hom(K, Y)` by precomposition, for every object `Y`. -/
theorem quasiIso_linearYonedaFunctor_map_of_projective (φ : K ⟶ L) [QuasiIso φ]
    (k : Type*) [Ring k] [Linear k C] (Y : C) :
    QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) :=
  homotopyEquivalences_le_quasiIso _ _ _
    (homotopyEquivalences_linearYonedaFunctor_map_of_projective φ k Y)

/-- A chain map `φ : K ⟶ L` between `ℕ`-graded chain complexes of projective objects in a
`k`-linear abelian category is a quasi-isomorphism if and only if `Hom(L, Y) ⟶ Hom(K, Y)` is a
quasi-isomorphism for every object `Y`. -/
theorem quasiIso_iff_forall_quasiIso_linearYonedaFunctor_map_of_projective (φ : K ⟶ L)
    (k : Type*) [Ring k] [Linear k C] :
    QuasiIso φ ↔
      ∀ Y : C, QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) :=
  ⟨fun _ Y ↦ quasiIso_linearYonedaFunctor_map_of_projective φ k Y,
    quasiIso_of_forall_quasiIso_linearYonedaFunctor_map φ k⟩

/-- A chain map `φ : K ⟶ L` between `ℕ`-graded chain complexes of projective objects in a
`k`-linear abelian category is a chain homotopy equivalence if and only if
`Hom(L, Y) ⟶ Hom(K, Y)` is a quasi-isomorphism for every object `Y`. -/
theorem homotopyEquivalences_iff_forall_quasiIso_linearYonedaFunctor_map_of_projective (φ : K ⟶ L)
    (k : Type*) [Ring k] [Linear k C] :
    homotopyEquivalences _ _ φ ↔
      ∀ Y : C, QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) :=
  (quasiIso_iff_of_projective φ).symm.trans
    (quasiIso_iff_forall_quasiIso_linearYonedaFunctor_map_of_projective φ k)

end Projective

end ChainComplex

