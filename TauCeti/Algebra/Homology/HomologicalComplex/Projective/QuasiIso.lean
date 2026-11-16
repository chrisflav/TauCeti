/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.Embedding.DownNatAdd
public import TauCeti.Algebra.Homology.Embedding.UpNatAdd
public import TauCeti.Algebra.Homology.LinearYoneda
import Mathlib.Algebra.Homology.HomologySequence
import TauCeti.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.Algebra.Homology.UniversalCoefficient.Basic

/-!
# Detecting quasi-isomorphisms of projective complexes by `Hom(-, Y)`

Let `C` be a `k`-linear abelian category and let `φ : K ⟶ L` be a morphism of `ℕ`-graded chain
complexes of projective objects of `C`. By
`ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective`, if `φ` is a quasi-isomorphism,
then precomposition `Hom(φ, Y) : Hom(L, Y) ⟶ Hom(K, Y)` is a quasi-isomorphism for every object
`Y : C`. This file proves the converse
(`ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor_map`) and combines the two into an
equivalence (`ChainComplex.quasiIso_iff_forall_quasiIso_linearYonedaFunctor_map`).

The proof forms the `ℕ`-graded mapping cone `M` of `φ`, fitting into a degreewise split short
exact sequence `0 ⟶ L ⟶ M ⟶ K[1] ⟶ 0`, where `K[1]` is `K` extended by zero along
`n ↦ n + 1` (`ComplexShape.embeddingDownNatAdd 1`). Applying `Hom(-, Y)` produces a short exact
sequence of cochain complexes whose connecting morphisms are, up to sign, the maps
`Hⁿ(Hom(φ, Y))`. Since each of these is an isomorphism, `Hom(M, Y)` is acyclic for every `Y : C`.
Since every term of `M` is a direct sum of terms of `K` and `L`, and hence projective, strong
induction on `n` using the universal coefficient isomorphism below the first non-projective
homology (`TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_lt`) with `Y = Hₙ(M)`
shows that `Hₙ(M) = 0` for all `n`. The long exact homology sequence of
`0 ⟶ L ⟶ M ⟶ K[1] ⟶ 0`, whose connecting morphisms are `±Hₙ(φ)`, then gives that `φ` is a
quasi-isomorphism.

We also record the compatibility of `ChainComplex.linearYonedaObj` with degree shifting by zero
extension (`ChainComplex.linearYonedaObjExtendIso` and
`ChainComplex.homologyLinearYonedaObjExtendIso`), which identifies `Hom(K.extend (+r), Y)` with
`Hom(K, Y).extend (+r)`.

## Main definitions and results

* `ChainComplex.linearYonedaObjExtendIso`: `Hom(K.extend (+r), Y) ≅ Hom(K, Y).extend (+r)`.
* `ChainComplex.homologyLinearYonedaObjExtendIso`: `Hᵐ(Hom(K.extend (+r), Y)) ≅ Hᵖ(Hom(K, Y))`
  for `p + r = m`.
* `ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor_map`: a morphism of `ℕ`-graded
  chain complexes of projectives inducing a quasi-isomorphism on `Hom(-, Y)` for all `Y` is a
  quasi-isomorphism.
* `ChainComplex.quasiIso_iff_forall_quasiIso_linearYonedaFunctor_map`: the characterization of
  quasi-isomorphisms between `ℕ`-graded chain complexes of projectives.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (proving a chain map of free complexes is a quasi-isomorphism from
  cohomology with arbitrary coefficients).
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 1.5 (mapping cones).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-! ### Compatibility of `linearYonedaObj` with zero-extension shifts -/

section Extend

variable (K : ChainComplex C ℕ) (k : Type*) [Ring k] [Linear k C] (Y : C)

private lemma isZero_linearYonedaObj_extend_X (r m : ℕ) (hm : m < r) :
    IsZero ((ChainComplex.linearYonedaObj
      (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).X m) := by
  have hzero : IsZero ((K.extend (ComplexShape.embeddingDownNatAdd r)).X m) :=
    K.isZero_extend_X (ComplexShape.embeddingDownNatAdd r) m fun _ hi ↦ by
      simp only [ComplexShape.embeddingDownNatAdd_f] at hi; omega
  have : Subsingleton ↑((ChainComplex.linearYonedaObj
      (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).X m) :=
    ⟨fun f g ↦ hzero.eq_of_src f g⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The degree-`m` isomorphism between `Hom((K.extend (+r))_m, Y)` and `(Hom(K, Y).extend (+r))^m`,
built from `extendXIso` when `r ≤ m` and from both terms being zero when `m < r`. -/
private def linearYonedaObjExtendIsoX (r m : ℕ) :
    (ChainComplex.linearYonedaObj (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).X m ≅
      ((K.linearYonedaObj k Y).extend (ComplexShape.embeddingUpNatAdd r)).X m := by
  by_cases hm : r ≤ m
  · let e₁ := K.extendXIso (ComplexShape.embeddingDownNatAdd r) (i := m - r) (i' := m)
      (by simp only [ComplexShape.embeddingDownNatAdd_f]; omega)
    let e₂ := (K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
      (i := m - r) (i' := m) (by simp only [ComplexShape.embeddingUpNatAdd_f]; omega)
    exact ((linearYoneda k C).obj Y).mapIso e₁.op.symm ≪≫ e₂.symm
  · exact (isZero_linearYonedaObj_extend_X K k Y r m (by omega)).iso
      ((K.linearYonedaObj k Y).isZero_extend_X (ComplexShape.embeddingUpNatAdd r) m fun _ hi ↦ by
        simp only [ComplexShape.embeddingUpNatAdd_f] at hi; omega)

private lemma linearYonedaObjExtendIsoX_hom_comp_extendXIso_hom {r p m : ℕ} (h : p + r = m)
    (f : (K.extend (ComplexShape.embeddingDownNatAdd r)).X m ⟶ Y) :
    (((K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f p = m by simp [h])).hom.hom
      ((linearYonedaObjExtendIsoX K k Y r m).hom.hom f) : K.X p ⟶ Y) =
      (K.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = m by simp [h])).inv ≫ f := by
  have hm : r ≤ m := by omega
  obtain rfl : p = m - r := by omega
  have hcomp : (linearYonedaObjExtendIsoX K k Y r m).hom ≫
      ((K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f (m - r) = m by simp [h])).hom =
      ((linearYoneda k C).obj Y).map (K.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f (m - r) = m by simp [h])).inv.op := by
    simp only [linearYonedaObjExtendIsoX, hm, ↓reduceDIte]
    let e₁ := K.extendXIso (ComplexShape.embeddingDownNatAdd r)
      (show (ComplexShape.embeddingDownNatAdd r).f (m - r) = m by simp [h])
    let e₂ := (K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
      (show (ComplexShape.embeddingUpNatAdd r).f (m - r) = m by simp [h])
    let g : (ChainComplex.linearYonedaObj
        (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).X m ⟶
        (K.linearYonedaObj k Y).X (m - r) :=
      ((linearYoneda k C).obj Y).map e₁.inv.op
    change (g ≫ e₂.inv) ≫ e₂.hom = g
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom hcomp f

private lemma extendXIso_inv_comp_linearYonedaObjExtendIsoX_inv {r p m : ℕ} (h : p + r = m)
    (f : K.X p ⟶ Y) :
    ((linearYonedaObjExtendIsoX K k Y r m).inv.hom
      (((K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f p = m by simp [h])).inv.hom f) :
        (K.extend (ComplexShape.embeddingDownNatAdd r)).X m ⟶ Y) =
      (K.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = m by simp [h])).hom ≫ f := by
  have hm : r ≤ m := by omega
  obtain rfl : p = m - r := by omega
  have hcomp : ((K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f (m - r) = m by simp [h])).inv ≫
      (linearYonedaObjExtendIsoX K k Y r m).inv =
      ((linearYoneda k C).obj Y).map (K.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f (m - r) = m by simp [h])).hom.op := by
    simp only [linearYonedaObjExtendIsoX, hm, ↓reduceDIte]
    let e₁ := K.extendXIso (ComplexShape.embeddingDownNatAdd r)
      (show (ComplexShape.embeddingDownNatAdd r).f (m - r) = m by simp [h])
    let e₂ := (K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
      (show (ComplexShape.embeddingUpNatAdd r).f (m - r) = m by simp [h])
    let g : (K.linearYonedaObj k Y).X (m - r) ⟶
        (ChainComplex.linearYonedaObj
          (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).X m :=
      ((linearYoneda k C).obj Y).map e₁.hom.op
    change e₂.inv ≫ (e₂.hom ≫ g) = g
    rw [Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom hcomp f

/-- **Zero-extension commutes with `Hom(-, Y)`**: extending a chain complex `K` upward by `r`
degrees (`ComplexShape.embeddingDownNatAdd r`) and applying `Hom(-, Y)` is naturally isomorphic
to applying `Hom(-, Y)` and extending upward by `r` degrees (`ComplexShape.embeddingUpNatAdd r`). -/
def linearYonedaObjExtendIso (r : ℕ) :
    ChainComplex.linearYonedaObj (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y ≅
      (K.linearYonedaObj k Y).extend (ComplexShape.embeddingUpNatAdd r) :=
  HomologicalComplex.Hom.isoOfComponents (linearYonedaObjExtendIsoX K k Y r) fun i j hij ↦ by
    have hij' : i + 1 = j := hij
    by_cases hi : r ≤ i
    · have hp : (i - r) + r = i := by omega
      have hq : (j - r) + r = j := by omega
      have heq := (K.linearYonedaObj k Y).extend_d_eq (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f (i - r) = i by simp [hp])
        (show (ComplexShape.embeddingUpNatAdd r).f (j - r) = j by simp [hq])
      have hKd := K.extend_d_eq (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f (j - r) = j by simp [hq])
        (show (ComplexShape.embeddingDownNatAdd r).f (i - r) = i by simp [hp])
      rw [heq, ← cancel_mono (((K.linearYonedaObj k Y).extendXIso
        (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f (j - r) = j by simp [hq])).hom)]
      simp only [Category.assoc, Iso.inv_hom_id]
      ext (f : (K.extend (ComplexShape.embeddingDownNatAdd r)).X i ⟶ Y)
      simp only [ModuleCat.hom_comp]
      symm
      refine (linearYonedaObjExtendIsoX_hom_comp_extendXIso_hom K k Y hq
        ((ChainComplex.linearYonedaObj
          (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).d i j f)).trans ?_
      change (K.extendXIso (ComplexShape.embeddingDownNatAdd r)
            (show (ComplexShape.embeddingDownNatAdd r).f (j - r) = j by simp [hq])).inv ≫
          (K.extend (ComplexShape.embeddingDownNatAdd r)).d j i ≫ f =
        K.d (j - r) (i - r) ≫
          (((K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
              (show (ComplexShape.embeddingUpNatAdd r).f (i - r) = i by simp [hp])).hom.hom
            ((linearYonedaObjExtendIsoX K k Y r i).hom.hom f) : K.X (i - r) ⟶ Y)
      rw [hKd, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
      rw [linearYonedaObjExtendIsoX_hom_comp_extendXIso_hom K k Y hp f]
    · exact (isZero_linearYonedaObj_extend_X K k Y r i (by omega)).eq_of_src _ _

/-- On a degree `m = p + r`, `linearYonedaObjExtendIso` followed by `extendXIso.hom` is
precomposition with `(K.extendXIso _ h).inv`. -/
lemma linearYonedaObjExtendIso_hom_f_comp_extendXIso_hom {r p m : ℕ} (h : p + r = m)
    (f : (K.extend (ComplexShape.embeddingDownNatAdd r)).X m ⟶ Y) :
    (((K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f p = m by simp [h])).hom.hom
      ((K.linearYonedaObjExtendIso k Y r).hom.f m f) : K.X p ⟶ Y) =
      (K.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = m by simp [h])).inv ≫ f :=
  linearYonedaObjExtendIsoX_hom_comp_extendXIso_hom K k Y h f

/-- On a degree `m = p + r`, `extendXIso.inv` followed by `(linearYonedaObjExtendIso).inv` is
precomposition with `(K.extendXIso _ h).hom`. -/
lemma extendXIso_inv_comp_linearYonedaObjExtendIso_inv_f {r p m : ℕ} (h : p + r = m)
    (f : K.X p ⟶ Y) :
    ((K.linearYonedaObjExtendIso k Y r).inv.f m
      (((K.linearYonedaObj k Y).extendXIso (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f p = m by simp [h])).inv.hom f) :
        (K.extend (ComplexShape.embeddingDownNatAdd r)).X m ⟶ Y) =
      (K.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = m by simp [h])).hom ≫ f :=
  extendXIso_inv_comp_linearYonedaObjExtendIsoX_inv K k Y h f

/-- **Cohomology of a zero-extended chain complex vanishes below the shift degree.** -/
lemma isZero_homology_linearYonedaObj_extend (r m : ℕ) (hm : m < r) :
    IsZero ((ChainComplex.linearYonedaObj
      (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).homology m) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_linearYonedaObj_extend_X K k Y r m hm)

/-- **Cohomology of a zero-extended chain complex in shifted degrees**: for `p + r = m`,
`Hᵐ(Hom(K.extend (+r), Y)) ≅ Hᵖ(Hom(K, Y))`. -/
def homologyLinearYonedaObjExtendIso {r p m : ℕ} (h : p + r = m) :
    (ChainComplex.linearYonedaObj
      (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).homology m ≅
      (K.linearYonedaObj k Y).homology p :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) m).mapIso
      (K.linearYonedaObjExtendIso k Y r) ≪≫
    (K.linearYonedaObj k Y).extendHomologyIso (ComplexShape.embeddingUpNatAdd r)
      (show (ComplexShape.embeddingUpNatAdd r).f p = m by simp [h])

/-- Evaluating `homologyLinearYonedaObjExtendIso.hom` on the class of a cocycle `φ` gives the
class of the cocycle `(K.extendXIso _ h).inv ≫ φ`. -/
lemma homologyLinearYonedaObjExtendIso_hom_homologyπ {r p m : ℕ} (h : p + r = m)
    (φ : (ChainComplex.linearYonedaObj
      (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).cycles m)
    (ψ : (K.linearYonedaObj k Y).cycles p)
    (hψ : (K.linearYonedaObj k Y).iCycles p ψ =
      (K.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = m by simp [h])).inv ≫
        (ChainComplex.linearYonedaObj
          (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).iCycles m φ) :
    (K.homologyLinearYonedaObjExtendIso k Y h).hom
        ((ChainComplex.linearYonedaObj
          (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).homologyπ m φ) =
      (K.linearYonedaObj k Y).homologyπ p ψ := by
  have he : ((K.linearYonedaObj k Y).extendCyclesIso (ComplexShape.embeddingUpNatAdd r)
      (show (ComplexShape.embeddingUpNatAdd r).f p = m by simp [h])).hom
        (cyclesMap (K.linearYonedaObjExtendIso k Y r).hom m φ) = ψ := by
    apply (ModuleCat.mono_iff_injective ((K.linearYonedaObj k Y).iCycles p)).1 inferInstance
    have h₁ := ConcreteCategory.congr_hom
      ((K.linearYonedaObj k Y).extendCyclesIso_hom_iCycles (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f p = m by simp [h]))
      (cyclesMap (K.linearYonedaObjExtendIso k Y r).hom m φ)
    have h₂ := ConcreteCategory.congr_hom
      (cyclesMap_i (K.linearYonedaObjExtendIso k Y r).hom m) φ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
    rw [h₁, h₂, hψ]
    exact linearYonedaObjExtendIso_hom_f_comp_extendXIso_hom K k Y h _
  have hπ := ConcreteCategory.congr_hom
    (homologyπ_naturality_assoc (K.linearYonedaObjExtendIso k Y r).hom m
      (((K.linearYonedaObj k Y).extendHomologyIso (ComplexShape.embeddingUpNatAdd r)
        (show (ComplexShape.embeddingUpNatAdd r).f p = m by simp [h])).hom)) φ
  rw [homologyπ_extendHomologyIso_hom] at hπ
  simp only [homologyLinearYonedaObjExtendIso, ModuleCat.hom_comp, LinearMap.comp_apply] at hπ ⊢
  rw [he] at hπ
  exact hπ

/-- Evaluating `homologyLinearYonedaObjExtendIso.inv` on the class of a cocycle `ψ` gives the
class of the cocycle `(K.extendXIso _ h).hom ≫ ψ`. -/
lemma homologyLinearYonedaObjExtendIso_inv_homologyπ {r p m : ℕ} (h : p + r = m)
    (ψ : (K.linearYonedaObj k Y).cycles p)
    (φ : (ChainComplex.linearYonedaObj
      (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).cycles m)
    (hφ : (ChainComplex.linearYonedaObj
        (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).iCycles m φ =
      (K.extendXIso (ComplexShape.embeddingDownNatAdd r)
        (show (ComplexShape.embeddingDownNatAdd r).f p = m by simp [h])).hom ≫
        (K.linearYonedaObj k Y).iCycles p ψ) :
    (K.homologyLinearYonedaObjExtendIso k Y h).inv ((K.linearYonedaObj k Y).homologyπ p ψ) =
      (ChainComplex.linearYonedaObj
        (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).homologyπ m φ := by
  let e := K.extendXIso (ComplexShape.embeddingDownNatAdd r)
    (show (ComplexShape.embeddingDownNatAdd r).f p = m by simp [h])
  have hψ : ((K.linearYonedaObj k Y).iCycles p ψ : K.X p ⟶ Y) =
      e.inv ≫ ((ChainComplex.linearYonedaObj
        (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).iCycles m φ :
          (K.extend (ComplexShape.embeddingDownNatAdd r)).X m ⟶ Y) :=
    ((Iso.inv_comp_eq e).2 hφ).symm
  have hhom := homologyLinearYonedaObjExtendIso_hom_homologyπ K k Y h φ ψ hψ
  calc (K.homologyLinearYonedaObjExtendIso k Y h).inv ((K.linearYonedaObj k Y).homologyπ p ψ)
      = (K.homologyLinearYonedaObjExtendIso k Y h).inv
          ((K.homologyLinearYonedaObjExtendIso k Y h).hom
            ((ChainComplex.linearYonedaObj
              (K.extend (ComplexShape.embeddingDownNatAdd r)) k Y).homologyπ m φ)) :=
        congrArg _ hhom.symm
    _ = _ := ConcreteCategory.congr_hom (K.homologyLinearYonedaObjExtendIso k Y h).hom_inv_id _

end Extend

/-! ### The `ℕ`-graded mapping cone and detection of quasi-isomorphisms -/

section MappingCone

variable {K L : ChainComplex C ℕ}

/-- The degree-`n` object of the `ℕ`-graded mapping cone of a chain map `K ⟶ L`: `L₀` in
degree `0` and `Lₙ₊₁ ⊞ Kₙ` in degree `n + 1`. -/
private abbrev coneX (K L : ChainComplex C ℕ) : ℕ → C
  | 0 => L.X 0
  | n + 1 => L.X (n + 1) ⊞ K.X n

/-- The `(n + 1) → n` differential of the `ℕ`-graded mapping cone of `φ : K ⟶ L`, with sign
`(-1)ⁿ` on `φₙ` so that the quotient differential on `K[1]` carries no sign. -/
private def coneDSucc (φ : K ⟶ L) : ∀ n : ℕ, coneX K L (n + 1) ⟶ coneX K L n
  | 0 => biprod.desc (L.d 1 0) (φ.f 0)
  | n + 1 =>
    biprod.desc (L.d (n + 2) (n + 1) ≫ biprod.inl)
      ((((-1 : ℤ) ^ (n + 1)) • φ.f (n + 1)) ≫ biprod.inl + K.d (n + 1) n ≫ biprod.inr)

/-- The differential of the `ℕ`-graded mapping cone of `φ : K ⟶ L`. -/
private def coneD (φ : K ⟶ L) (i j : ℕ) : coneX K L i ⟶ coneX K L j :=
  if h : j + 1 = i then eqToHom (congrArg (coneX K L) h.symm) ≫ coneDSucc φ j else 0

private lemma coneD_succ (φ : K ⟶ L) (n : ℕ) : coneD φ (n + 1) n = coneDSucc φ n := by
  simp [coneD]

private lemma coneD_eq_zero_of_ne (φ : K ⟶ L) {i j : ℕ} (h : j + 1 ≠ i) :
    coneD φ i j = 0 := by
  simp [coneD, h]

private lemma coneD_comp_coneD (φ : K ⟶ L) (i j k : ℕ) :
    coneD φ i j ≫ coneD φ j k = 0 := by
  by_cases h₁ : j + 1 = i
  · subst h₁
    by_cases h₂ : k + 1 = j
    · subst h₂
      rw [coneD_succ, coneD_succ]
      cases k with
      | zero =>
        apply biprod.hom_ext'
        · simp [coneDSucc]
        · simp [coneDSucc, Preadditive.add_comp, φ.comm 1 0]
      | succ n =>
        apply biprod.hom_ext'
        · simp [coneDSucc]
        · simp only [coneDSucc, biprod.inr_desc_assoc, Preadditive.add_comp, Category.assoc,
            biprod.inl_desc, biprod.inr_desc, Preadditive.comp_add, d_comp_d_assoc,
            zero_comp, add_zero, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
          rw [φ.comm_assoc (n + 2) (n + 1), pow_succ, mul_neg_one, neg_zsmul, neg_add_cancel,
            comp_zero]
    · rw [coneD_eq_zero_of_ne φ h₂, comp_zero]
  · rw [coneD_eq_zero_of_ne φ h₁, zero_comp]

/-- The `ℕ`-graded mapping cone of a morphism `φ : K ⟶ L` in `ChainComplex C ℕ`. -/
private def cone (φ : K ⟶ L) : ChainComplex C ℕ where
  X := coneX K L
  d := coneD φ
  shape _ _ h := coneD_eq_zero_of_ne φ h
  d_comp_d' i j k _ _ := coneD_comp_coneD φ i j k

private instance cone_projective (φ : K ⟶ L) [∀ n, Projective (K.X n)]
    [∀ n, Projective (L.X n)] (n : ℕ) : Projective ((cone φ).X n) := by
  cases n with
  | zero => exact inferInstanceAs (Projective (L.X 0))
  | succ n => exact inferInstanceAs (Projective (L.X (n + 1) ⊞ K.X n))

/-- The inclusion `L ⟶ cone φ`. -/
private def coneInl (φ : K ⟶ L) : L ⟶ cone φ where
  f
    | 0 => 𝟙 (L.X 0)
    | _ + 1 => biprod.inl
  comm' i j h := by
    have hij : j + 1 = i := h
    subst hij
    dsimp only [cone]
    rw [coneD_succ]
    cases j <;> simp [coneDSucc]

private instance isSplitMono_coneInl_f (φ : K ⟶ L) (n : ℕ) :
    IsSplitMono ((coneInl φ).f n) := by
  cases n with
  | zero => exact ⟨⟨𝟙 _, Category.id_comp _⟩⟩
  | succ n => exact ⟨⟨biprod.fst, biprod.inl_fst⟩⟩

/-- The projection `cone φ ⟶ K.extend (+1)`. -/
private def coneSnd (φ : K ⟶ L) : cone φ ⟶ K.extend (ComplexShape.embeddingDownNatAdd 1) where
  f
    | 0 => 0
    | n + 1 => biprod.snd ≫
        (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
          (ComplexShape.embeddingDownNatAdd_f 1 n)).inv
  comm' i j h := by
    have hij : j + 1 = i := h
    subst hij
    cases j with
    | zero =>
      exact (K.isZero_extend_X (ComplexShape.embeddingDownNatAdd 1) 0 fun _ hi ↦ by
        simp at hi).eq_of_tgt _ _
    | succ j =>
      dsimp only [cone]
      rw [coneD_succ, K.extend_d_eq (ComplexShape.embeddingDownNatAdd 1)
        (ComplexShape.embeddingDownNatAdd_f 1 (j + 1))
        (ComplexShape.embeddingDownNatAdd_f 1 j)]
      apply biprod.hom_ext'
      · simp [coneDSucc]
      · simp [coneDSucc, Preadditive.add_comp]

/-- The degreewise split short exact sequence `0 ⟶ L ⟶ cone φ ⟶ K.extend (+1) ⟶ 0`. -/
private def coneShortComplex (φ : K ⟶ L) : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (coneInl φ) (coneSnd φ) <| by
    ext n
    cases n with
    | zero =>
      change 𝟙 (L.X 0) ≫ (0 : L.X 0 ⟶ _) = 0
      simp
    | succ n =>
      change biprod.inl ≫ biprod.snd ≫ _ = 0
      simp

private instance isSplitMono_coneShortComplex_f (φ : K ⟶ L) (n : ℕ) :
    IsSplitMono ((coneShortComplex φ).f.f n) :=
  isSplitMono_coneInl_f φ n

private lemma coneShortComplex_shortExact (φ : K ⟶ L) : (coneShortComplex φ).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  cases n with
  | zero =>
    have hZ : IsZero ((K.extend (ComplexShape.embeddingDownNatAdd 1)).X 0) :=
      K.isZero_extend_X (ComplexShape.embeddingDownNatAdd 1) 0 fun _ hi ↦ by simp at hi
    exact (ShortComplex.Splitting.ofIsIsoOfIsZero _
      (inferInstanceAs (IsIso (𝟙 (L.X 0)))) hZ).shortExact
  | succ n =>
    have hsplit : (ShortComplex.mk (biprod.inl : L.X (n + 1) ⟶ L.X (n + 1) ⊞ K.X n)
        (biprod.snd : L.X (n + 1) ⊞ K.X n ⟶ K.X n) biprod.inl_snd).ShortExact :=
      (ShortComplex.Splitting.ofHasBinaryBiproduct (L.X (n + 1)) (K.X n)).shortExact
    refine ShortComplex.shortExact_of_iso ?_ hsplit
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
        (ComplexShape.embeddingDownNatAdd_f 1 n)).symm
      (by dsimp [coneShortComplex, coneInl, cone]; simp)
      (by dsimp [coneShortComplex, coneSnd, cone]; simp)

/-- The connecting morphism of `0 ⟶ L ⟶ cone φ ⟶ K.extend (+1) ⟶ 0` in homology is
`(-1)ⁿ • Hₙ(φ)` under `K.extendHomologyIso`. -/
private lemma coneShortComplex_δ (φ : K ⟶ L) (n : ℕ) :
    (K.extendHomologyIso (ComplexShape.embeddingDownNatAdd 1)
        (ComplexShape.embeddingDownNatAdd_f 1 n)).inv ≫
      (coneShortComplex_shortExact φ).δ (n + 1) n ((ComplexShape.down_Rel ℕ _ _).mpr rfl) =
        ((-1 : ℤ) ^ n) • homologyMap φ n := by
  apply (cancel_epi (K.homologyπ n)).1
  dsimp only [coneShortComplex]
  rw [homologyπ_extendHomologyIso_inv_assoc, Preadditive.comp_zsmul, homologyπ_naturality]
  have hx₂ : ((K.extendCyclesIso (ComplexShape.embeddingDownNatAdd 1)
        (ComplexShape.embeddingDownNatAdd_f 1 n)).inv ≫
      (K.extend (ComplexShape.embeddingDownNatAdd 1)).iCycles (n + 1)) =
        K.iCycles n ≫ (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
          (ComplexShape.embeddingDownNatAdd_f 1 n)).inv :=
    K.extendCyclesIso_inv_iCycles _ _
  have hx₃_pf : (K.iCycles n ≫ (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
      (ComplexShape.embeddingDownNatAdd_f 1 n)).inv) ≫
      (K.extend (ComplexShape.embeddingDownNatAdd 1)).d (n + 1) n = 0 := by
    cases n with
    | zero =>
      exact (K.isZero_extend_X (ComplexShape.embeddingDownNatAdd 1) 0 fun _ hi ↦ by
        simp at hi).eq_of_tgt _ _
    | succ m =>
      rw [K.extend_d_eq (ComplexShape.embeddingDownNatAdd 1)
        (ComplexShape.embeddingDownNatAdd_f 1 (m + 1))
        (ComplexShape.embeddingDownNatAdd_f 1 m), Category.assoc, Iso.inv_hom_id_assoc,
        iCycles_d_assoc, zero_comp]
  have hδ := (coneShortComplex_shortExact φ).δ_eq (n + 1) n
    ((ComplexShape.down_Rel ℕ _ _).mpr rfl)
    (A := K.cycles n)
    (x₃ := K.iCycles n ≫ (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
      (ComplexShape.embeddingDownNatAdd_f 1 n)).inv)
    (hx₃ := hx₃_pf)
    (x₂ := K.iCycles n ≫ biprod.inr)
    (hx₂ := by dsimp only [coneShortComplex, coneSnd, cone]; simp)
    (x₁ := K.iCycles n ≫ (((-1 : ℤ) ^ n) • φ.f n))
    (hx₁ := by
      dsimp only [coneShortComplex, coneInl, cone]
      rw [coneD_succ]
      cases n with
      | zero => simp [coneDSucc]
      | succ m =>
        simp [coneDSucc, Preadditive.comp_add, iCycles_d_assoc])
    ((ComplexShape.down ℕ).next n) rfl
  have hx₁_d : (K.iCycles n ≫ (((-1 : ℤ) ^ n) • φ.f n)) ≫
      L.d n ((ComplexShape.down ℕ).next n) = 0 := by
    rw [Category.assoc, Preadditive.zsmul_comp, φ.comm, Preadditive.comp_zsmul,
      iCycles_d_assoc, zero_comp, smul_zero]
  have hlhs : (K.extend (ComplexShape.embeddingDownNatAdd 1)).liftCycles
      (K.iCycles n ≫ (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
        (ComplexShape.embeddingDownNatAdd_f 1 n)).inv) n
      (ComplexShape.next_eq' _ ((ComplexShape.down_Rel ℕ _ _).mpr rfl)) hx₃_pf =
      (K.extendCyclesIso (ComplexShape.embeddingDownNatAdd 1)
        (ComplexShape.embeddingDownNatAdd_f 1 n)).inv := by
    rw [← cancel_mono ((K.extend (ComplexShape.embeddingDownNatAdd 1)).iCycles (n + 1)),
      liftCycles_i, hx₂]
  have hrhs : L.liftCycles (K.iCycles n ≫ (((-1 : ℤ) ^ n) • φ.f n)) _ rfl hx₁_d =
      ((-1 : ℤ) ^ n) • cyclesMap φ n := by
    rw [← cancel_mono (L.iCycles n), liftCycles_i, Preadditive.zsmul_comp, cyclesMap_i,
      Preadditive.comp_zsmul]
  have hδ' : (K.extend (ComplexShape.embeddingDownNatAdd 1)).liftCycles
        (K.iCycles n ≫ (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
          (ComplexShape.embeddingDownNatAdd_f 1 n)).inv) n
        (ComplexShape.next_eq' _ ((ComplexShape.down_Rel ℕ _ _).mpr rfl)) hx₃_pf ≫
      (K.extend (ComplexShape.embeddingDownNatAdd 1)).homologyπ (n + 1) ≫
      (coneShortComplex_shortExact φ).δ (n + 1) n ((ComplexShape.down_Rel ℕ _ _).mpr rfl) =
    L.liftCycles (K.iCycles n ≫ (((-1 : ℤ) ^ n) • φ.f n)) _ rfl hx₁_d ≫
      L.homologyπ n := hδ
  rw [hlhs, hrhs, Preadditive.zsmul_comp] at hδ'
  exact hδ'

/-- The connecting morphism of `0 ⟶ Hom(K.extend (+1), Y) ⟶ Hom(cone φ, Y) ⟶ Hom(L, Y) ⟶ 0`
is `(-1)ⁿ • Hⁿ(Hom(φ, Y))` under `homologyLinearYonedaObjExtendIso`. -/
private lemma coneShortComplex_linearYoneda_δ (φ : K ⟶ L) (k : Type*) [Ring k] [Linear k C]
    (Y : C) (n : ℕ) :
    (TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k Y
        (coneShortComplex_shortExact φ)).δ n (n + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl) ≫
      (K.homologyLinearYonedaObjExtendIso k Y (r := 1) (p := n) (m := n + 1) rfl).hom =
        ((-1 : ℤ) ^ n) • homologyMap (K := L.linearYonedaObj k Y) (L := K.linearYonedaObj k Y)
          ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) n := by
  let hSY := TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k Y
    (coneShortComplex_shortExact φ)
  apply (cancel_epi ((L.linearYonedaObj k Y).homologyπ n)).1
  let x₂M : (L.linearYonedaObj k Y).cycles n ⟶ ((cone φ).linearYonedaObj k Y).X n :=
    match n with
    | 0 => (L.linearYonedaObj k Y).iCycles 0
    | m + 1 => (L.linearYonedaObj k Y).iCycles (m + 1) ≫
        ModuleCat.ofHom (X := (L.linearYonedaObj k Y).X (m + 1))
          (Y := ((cone φ).linearYonedaObj k Y).X (m + 1))
          (Linear.leftComp k Y (biprod.fst : L.X (m + 1) ⊞ K.X m ⟶ L.X (m + 1)))
  let x₁M : (L.linearYonedaObj k Y).cycles n ⟶
      (ChainComplex.linearYonedaObj
        (K.extend (ComplexShape.embeddingDownNatAdd 1)) k Y).X (n + 1) :=
    (L.linearYonedaObj k Y).iCycles n ≫
      ModuleCat.ofHom (X := (L.linearYonedaObj k Y).X n)
        (Y := (ChainComplex.linearYonedaObj
          (K.extend (ComplexShape.embeddingDownNatAdd 1)) k Y).X (n + 1))
        (Linear.leftComp k Y ((K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
          (ComplexShape.embeddingDownNatAdd_f 1 n)).hom ≫ (((-1 : ℤ) ^ n) • φ.f n)))
  have hnext : (ComplexShape.up ℕ).next n = n + 1 :=
    ComplexShape.next_eq' _ ((ComplexShape.up_Rel ℕ _ _).mpr rfl)
  have hδ := hSY.δ_eq n (n + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl)
    (A := (L.linearYonedaObj k Y).cycles n)
    (x₃ := (L.linearYonedaObj k Y).iCycles n)
    (hx₃ := (L.linearYonedaObj k Y).iCycles_d n (n + 1))
    (x₂ := x₂M)
    (hx₂ := by
      ext (a : (L.linearYonedaObj k Y).cycles n)
      cases n with
      | zero =>
        change (𝟙 (L.X 0) ≫ ((L.linearYonedaObj k Y).iCycles 0 a : L.X 0 ⟶ Y)) =
          ((L.linearYonedaObj k Y).iCycles 0 a : L.X 0 ⟶ Y)
        exact Category.id_comp _
      | succ m =>
        let g : L.X (m + 1) ⟶ Y := (L.linearYonedaObj k Y).iCycles (m + 1) a
        change (biprod.inl ≫ biprod.fst ≫ g) = g
        rw [biprod.inl_fst_assoc])
    (x₁ := x₁M)
    (hx₁ := by
      ext (a : (L.linearYonedaObj k Y).cycles n)
      have hda : L.d (n + 1) n ≫ ((L.linearYonedaObj k Y).iCycles n a : L.X n ⟶ Y) = 0 :=
        TauCeti.ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) a
      cases n with
      | zero =>
        let g : L.X 0 ⟶ Y := (L.linearYonedaObj k Y).iCycles 0 a
        change (biprod.snd ≫ (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
            (ComplexShape.embeddingDownNatAdd_f 1 0)).inv) ≫
            ((K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
              (ComplexShape.embeddingDownNatAdd_f 1 0)).hom ≫
              (((-1 : ℤ) ^ 0) • φ.f 0)) ≫ g =
          coneD φ 1 0 ≫ g
        rw [coneD_succ]
        apply biprod.hom_ext'
        · simp only [coneDSucc, Category.assoc, biprod.inl_snd_assoc, zero_comp,
            biprod.inl_desc_assoc]
          exact hda.symm
        · simp [coneDSucc]
      | succ m =>
        let g : L.X (m + 1) ⟶ Y := (L.linearYonedaObj k Y).iCycles (m + 1) a
        change (biprod.snd ≫ (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
            (ComplexShape.embeddingDownNatAdd_f 1 (m + 1))).inv) ≫
            ((K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
              (ComplexShape.embeddingDownNatAdd_f 1 (m + 1))).hom ≫
              (((-1 : ℤ) ^ (m + 1)) • φ.f (m + 1))) ≫ g =
          coneD φ (m + 2) (m + 1) ≫ biprod.fst ≫ g
        rw [coneD_succ]
        apply biprod.hom_ext'
        · simp only [coneDSucc, Category.assoc, biprod.inl_snd_assoc, zero_comp,
            biprod.inl_desc_assoc, biprod.inl_fst_assoc]
          exact hda.symm
        · simp only [coneDSucc, Category.assoc, biprod.inr_snd_assoc, Iso.inv_hom_id_assoc,
            biprod.inr_desc_assoc, Preadditive.add_comp, biprod.inl_fst_assoc,
            biprod.inr_fst_assoc, zero_comp, comp_zero, add_zero])
    ((ComplexShape.up ℕ).next (n + 1)) rfl
  have hlhs : (L.linearYonedaObj k Y).liftCycles ((L.linearYonedaObj k Y).iCycles n) (n + 1)
      hnext ((L.linearYonedaObj k Y).iCycles_d n (n + 1)) = 𝟙 _ := by
    rw [← cancel_mono ((L.linearYonedaObj k Y).iCycles n), liftCycles_i, Category.id_comp]
  have hδ' : (L.linearYonedaObj k Y).liftCycles ((L.linearYonedaObj k Y).iCycles n) (n + 1)
        hnext ((L.linearYonedaObj k Y).iCycles_d n (n + 1)) ≫
      (L.linearYonedaObj k Y).homologyπ n ≫
      hSY.δ n (n + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl) =
    (ChainComplex.linearYonedaObj (K.extend (ComplexShape.embeddingDownNatAdd 1)) k Y).liftCycles
        x₁M ((ComplexShape.up ℕ).next (n + 1)) rfl _ ≫
      (ChainComplex.linearYonedaObj (K.extend (ComplexShape.embeddingDownNatAdd 1)) k Y).homologyπ
        (n + 1) := hδ
  rw [hlhs, Category.id_comp] at hδ'
  ext (ψ : (L.linearYonedaObj k Y).cycles n)
  have hδψ := ConcreteCategory.congr_hom hδ' ψ
  let Fφ : L.linearYonedaObj k Y ⟶ K.linearYonedaObj k Y :=
    (TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op
  change (K.homologyLinearYonedaObjExtendIso k Y (r := 1) (p := n) (m := n + 1) rfl).hom
      (((L.linearYonedaObj k Y).homologyπ n ≫
        hSY.δ n (n + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl)) ψ) =
    ((-1 : ℤ) ^ n) • (homologyMap Fφ n ((L.linearYonedaObj k Y).homologyπ n ψ))
  rw [hδψ]
  have hx₁M_d : x₁M ≫ (ChainComplex.linearYonedaObj
      (K.extend (ComplexShape.embeddingDownNatAdd 1)) k Y).d (n + 1)
      ((ComplexShape.up ℕ).next (n + 1)) = 0 := by
    have hnext₁ : (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
      ComplexShape.next_eq' _ ((ComplexShape.up_Rel ℕ _ _).mpr rfl)
    rw [hnext₁]
    ext (a : (L.linearYonedaObj k Y).cycles n)
    have hda : L.d (n + 1) n ≫ ((L.linearYonedaObj k Y).iCycles n a : L.X n ⟶ Y) = 0 :=
      TauCeti.ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) a
    let g : L.X n ⟶ Y := (L.linearYonedaObj k Y).iCycles n a
    change (K.extend (ComplexShape.embeddingDownNatAdd 1)).d (n + 2) (n + 1) ≫
        ((K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
          (ComplexShape.embeddingDownNatAdd_f 1 n)).hom ≫ (((-1 : ℤ) ^ n) • φ.f n)) ≫ g = 0
    rw [K.extend_d_eq (ComplexShape.embeddingDownNatAdd 1)
      (ComplexShape.embeddingDownNatAdd_f 1 (n + 1))
      (ComplexShape.embeddingDownNatAdd_f 1 n)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp]
    rw [← φ.comm_assoc (n + 1) n, hda, comp_zero, comp_zero, smul_zero]
  let c₁ := (ChainComplex.linearYonedaObj
      (K.extend (ComplexShape.embeddingDownNatAdd 1)) k Y).liftCycles x₁M
    ((ComplexShape.up ℕ).next (n + 1)) rfl hx₁M_d ψ
  let g : L.X n ⟶ Y := (L.linearYonedaObj k Y).iCycles n ψ
  have hc₁ : ((ChainComplex.linearYonedaObj
        (K.extend (ComplexShape.embeddingDownNatAdd 1)) k Y).iCycles (n + 1) c₁ :
          (K.extend (ComplexShape.embeddingDownNatAdd 1)).X (n + 1) ⟶ Y) =
      (K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
        (ComplexShape.embeddingDownNatAdd_f 1 n)).hom ≫
        (((-1 : ℤ) ^ n) • φ.f n) ≫ g := by
    have := ConcreteCategory.congr_hom
      ((ChainComplex.linearYonedaObj
        (K.extend (ComplexShape.embeddingDownNatAdd 1)) k Y).liftCycles_i x₁M
          ((ComplexShape.up ℕ).next (n + 1)) rfl hx₁M_d) ψ
    exact this.trans (by
      change ((K.extendXIso (ComplexShape.embeddingDownNatAdd 1)
          (ComplexShape.embeddingDownNatAdd_f 1 n)).hom ≫
          (((-1 : ℤ) ^ n) • φ.f n)) ≫ g = _
      rw [Category.assoc])
  have hmap : homologyMap Fφ n ((L.linearYonedaObj k Y).homologyπ n ψ) =
      (K.linearYonedaObj k Y).homologyπ n (cyclesMap Fφ n ψ) :=
    ConcreteCategory.congr_hom (homologyπ_naturality Fφ n) ψ
  rw [hmap, ← map_zsmul]
  refine homologyLinearYonedaObjExtendIso_hom_homologyπ K k Y (r := 1) (p := n) (m := n + 1) rfl
    c₁ (((-1 : ℤ) ^ n) • cyclesMap Fφ n ψ) ?_
  rw [hc₁, Iso.inv_hom_id_assoc, map_zsmul]
  change ((-1 : ℤ) ^ n) •
      ((K.linearYonedaObj k Y).iCycles n (cyclesMap Fφ n ψ) : K.X n ⟶ Y) =
    (((-1 : ℤ) ^ n) • φ.f n) ≫ g
  rw [Preadditive.zsmul_comp]
  exact congrArg (((-1 : ℤ) ^ n) • ·)
    (TauCeti.ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply φ n ψ)

/-- If the connecting morphism `δ : Hⁿ(Hom(L, Y)) ⟶ Hⁿ⁺¹(Hom(K.extend (+1), Y))` is an
isomorphism for every `n`, then `Hom(cone φ, Y)` is acyclic. -/
private lemma isZero_homology_cone_linearYonedaObj (φ : K ⟶ L) (k : Type*) [Ring k] [Linear k C]
    (Y : C) (h : QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op)) (n : ℕ) :
    IsZero (((cone φ).linearYonedaObj k Y).homology n) := by
  let SY := (coneShortComplex φ).op.map (TauCeti.ChainComplex.linearYonedaFunctor k Y)
  have hSY : SY.ShortExact := TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k Y
    (coneShortComplex_shortExact φ)
  have hδIso : ∀ m, IsIso (hSY.δ m (m + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl)) :=
    fun m ↦ by
      let f := homologyMap (K := L.linearYonedaObj k Y) (L := K.linearYonedaObj k Y)
        ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) m
      have : IsIso f :=
        (quasiIsoAt_iff_isIso_homologyMap _ m).1 ((quasiIso_iff _).1 h m)
      let sfIso : (L.linearYonedaObj k Y).homology m ≅ (K.linearYonedaObj k Y).homology m :=
        { hom := ((-1 : ℤ) ^ m) • f
          inv := ((-1 : ℤ) ^ m) • inv f
          hom_inv_id := by
            rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, smul_smul, ← mul_pow]
            simp
          inv_hom_id := by
            rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← mul_pow]
            simp }
      let e := K.homologyLinearYonedaObjExtendIso k Y (r := 1) (p := m) (m := m + 1) rfl
      have hδeq : hSY.δ m (m + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl) =
          (sfIso ≪≫ e.symm).hom :=
        (Iso.eq_comp_inv e).2 (coneShortComplex_linearYoneda_δ φ k Y m)
      rw [hδeq]
      exact (sfIso ≪≫ e.symm).isIso_hom
  have hg₀ : HomologicalComplex.homologyMap SY.g n = 0 := by
    have := hδIso n
    exact (cancel_mono (hSY.δ n (n + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl))).1
      (by rw [zero_comp]; exact hSY.comp_δ n (n + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl))
  have hf₀ : HomologicalComplex.homologyMap SY.f n = 0 := by
    cases n with
    | zero =>
      exact (isZero_homology_linearYonedaObj_extend K k Y 1 0 (by omega)).eq_of_src _ _
    | succ m =>
      have := hδIso m
      exact (cancel_epi (hSY.δ m (m + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl))).1
        (by rw [comp_zero]; exact hSY.δ_comp m (m + 1) ((ComplexShape.up_Rel ℕ _ _).mpr rfl))
  exact (hSY.homology_exact₂ n).isZero_X₂ hf₀ hg₀

/-- **Detecting quasi-isomorphisms of projective complexes by `Hom(-, Y)`.** Let `φ : K ⟶ L` be a
morphism of `ℕ`-graded chain complexes of projective objects in a `k`-linear abelian category `C`.
If `Hom(φ, Y) : Hom(L, Y) ⟶ Hom(K, Y)` is a quasi-isomorphism for every object `Y : C`, then `φ`
is a quasi-isomorphism. -/
theorem quasiIso_of_forall_quasiIso_linearYonedaFunctor_map (φ : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)] (k : Type*) [Ring k] [Linear k C]
    (h : ∀ Y : C, QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op)) :
    QuasiIso φ := by
  -- First show `Hₙ(cone φ) = 0` for all `n` by strong induction using universal coefficients.
  have hM : ∀ n, IsZero ((cone φ).homology n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      have hbij := TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_lt (k := k)
        (X := cone φ) (Y := (cone φ).homology n) n fun j hj ↦ (ih j hj).projective
      have hZ := ModuleCat.isZero_iff_subsingleton.1
        (isZero_homology_cone_linearYonedaObj φ k ((cone φ).homology n) (h _) n)
      have hsub : Subsingleton ((cone φ).homology n ⟶ (cone φ).homology n) :=
        hbij.2.subsingleton
      exact (Limits.IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _)
  -- From the long exact homology sequence of `0 ⟶ L ⟶ cone φ ⟶ K.extend (+1) ⟶ 0`, each
  -- connecting morphism `±Hₙ(φ)` is an isomorphism.
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso ((coneShortComplex_shortExact φ).δ (n + 1) n
      ((ComplexShape.down_Rel ℕ _ _).mpr rfl)) :=
    (coneShortComplex_shortExact φ).isIso_δ (n + 1) n
      ((ComplexShape.down_Rel ℕ _ _).mpr rfl) (hM (n + 1)) (hM n)
  let e := K.extendHomologyIso (ComplexShape.embeddingDownNatAdd 1)
    (ComplexShape.embeddingDownNatAdd_f 1 n)
  let δIso := asIso ((coneShortComplex_shortExact φ).δ (n + 1) n
    ((ComplexShape.down_Rel ℕ _ _).mpr rfl))
  have : IsIso (((-1 : ℤ) ^ n) • homologyMap φ n) := by
    rw [← coneShortComplex_δ φ n]
    exact (e.symm ≪≫ δIso).isIso_hom
  refine ⟨⟨((-1 : ℤ) ^ n) • inv (((-1 : ℤ) ^ n) • homologyMap φ n), ?_, ?_⟩⟩
  · calc homologyMap φ n ≫ (((-1 : ℤ) ^ n) • inv (((-1 : ℤ) ^ n) • homologyMap φ n))
        = (((-1 : ℤ) ^ n) • homologyMap φ n) ≫
            inv (((-1 : ℤ) ^ n) • homologyMap φ n) := by
          rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      _ = 𝟙 _ := IsIso.hom_inv_id _
  · calc (((-1 : ℤ) ^ n) • inv (((-1 : ℤ) ^ n) • homologyMap φ n)) ≫ homologyMap φ n
        = inv (((-1 : ℤ) ^ n) • homologyMap φ n) ≫
            (((-1 : ℤ) ^ n) • homologyMap φ n) := by
          rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
      _ = 𝟙 _ := IsIso.inv_hom_id _

/-- **Characterization of quasi-isomorphisms between projective complexes**: a morphism
`φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects in a `k`-linear abelian category
is a quasi-isomorphism if and only if `Hom(φ, Y)` is a quasi-isomorphism for every object `Y`. -/
theorem quasiIso_iff_forall_quasiIso_linearYonedaFunctor_map (φ : K ⟶ L)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)] (k : Type*) [Ring k] [Linear k C] :
    QuasiIso φ ↔
      ∀ Y : C, QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) :=
  ⟨fun _ Y ↦ quasiIso_linearYonedaFunctor_map_of_projective φ k Y,
    quasiIso_of_forall_quasiIso_linearYonedaFunctor_map φ k⟩

end MappingCone

end ChainComplex
