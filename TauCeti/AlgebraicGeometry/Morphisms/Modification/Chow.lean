/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Compactification.ProjectiveClosure
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.GraphClosure
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Segre
import TauCeti.AlgebraicGeometry.Scheme.DenseAffineCover

/-!
# Chow's lemma over a ring

Let `R` be a commutative ring and let `X` be a scheme separated and locally of finite type over
`Spec R` whose underlying topological space is Noetherian (for instance, any scheme separated and
of finite type over `Spec R` when `R` is Noetherian). Then:

1. (**General form**, `exists_isModification_and_isImmersion_isProjectiveOver_of_noetherianSpace`,
   `exists_isModification_and_isImmersion_isProjectiveOver`,
   `exists_isModification_and_isImmersion_proj`): there exist a scheme `X'` over `Spec R`, a
   modification `π : X' ⟶ X` over `Spec R`, a projective scheme `P` over `R` (or concretely
   `Proj (Sym_R M)` for a finite `R`-module `M`), and a quasi-compact immersion `i : X' ⟶ P` over
   `Spec R` whose graph `(π, i) : X' ⟶ X ×_{Spec R} P` is a closed immersion.
2. (**Proper form**, `exists_isProjectiveOver_and_isModification_of_noetherianSpace`,
   `exists_isProjectiveOver_and_isModification`): if `X` is proper over `Spec R`, then `i : X' ⟶ P`
   is proper and hence a closed immersion, so `X'` is itself projective over `R`: every proper
   scheme over `Spec R` with Noetherian underlying space (in particular, every proper scheme over a
   Noetherian ring `R`) is dominated via a modification over `Spec R` by a projective scheme over
   `R`.

The proof covers `X` by finitely many affine opens `V₁, …, Vₙ` whose total intersection
`U = V₁ ∩ ⋯ ∩ Vₙ` is dense (`AlgebraicGeometry.Scheme.exists_finite_affine_cover_dense_iInter`),
embeds each `Vₖ` openly over `Spec R` into a projective closure `P'ₖ`
(`exists_openImmersion_isProjectiveOver_of_isAffine`), forms the finite fibre product
`P = P'₁ ×_{Spec R} ⋯ ×_{Spec R} P'ₙ` (`exists_isProjectiveOver_pi`, projective by the Segre
embedding `AlgebraicGeometry.Scheme.IsProjectiveOver.pullback`), and takes `X'` to be the
scheme-theoretic graph closure of the diagonal morphism `U ⟶ P` in `X ×_{Spec R} P`
(`TauCeti.AlgebraicGeometry.graphClosure`).

## Main results

* `TauCeti.AlgebraicGeometry.exists_isProjectiveOver_pi`: finite fibre products over `Spec R` of
  projective schemes over `R` exist and are projective over `R`.
* `TauCeti.AlgebraicGeometry.exists_openImmersion_isProjectiveOver_of_isAffine`: every affine
  scheme of finite type over `Spec R` embeds openly over `Spec R` into a projective scheme over `R`.
* `exists_isModification_and_isImmersion_isProjectiveOver_of_noetherianSpace`,
  `exists_isModification_and_isImmersion_isProjectiveOver`,
  `exists_isModification_and_isImmersion_proj` (in `TauCeti.AlgebraicGeometry`): Chow's lemma for
  separated schemes of finite type.
* `exists_isProjectiveOver_and_isModification_of_noetherianSpace`,
  `exists_isProjectiveOver_and_isModification` (in `TauCeti.AlgebraicGeometry`): Chow's lemma for
  proper schemes.

## References

* [Stacks Project, Lemma 30.18.1](https://stacks.math.columbia.edu/tag/0200) and
  [Remark 30.18.2](https://stacks.math.columbia.edu/tag/0201).
* A. Grothendieck, *Éléments de géométrie algébrique. II. Étude globale élémentaire de quelques
  classes de morphismes*, Publ. Math. IHÉS 8 (1961), Theorem 5.6.1 and Corollary 5.6.2.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Exercise II.4.10.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace TauCeti.AlgebraicGeometry

universe u v

/-- **Finite fibre products of projective schemes over `R`.** For a finite family `P' : ι → Scheme`
of projective schemes over `R`, their fibre product over `Spec R` is represented by a projective
scheme `P` over `R` equipped with projections `pr k : P ⟶ P' k` over `Spec R`. -/
theorem exists_isProjectiveOver_pi {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    (P' : ι → Scheme.{u}) [∀ k, (P' k).Over (Spec (.of R))]
    [∀ k, (P' k).IsProjectiveOver R] :
    ∃ (P : Scheme.{u}) (_ : P.Over (Spec (.of R))) (_ : P.IsProjectiveOver R)
      (pr : ∀ k, P ⟶ P' k) (_ : ∀ k, (pr k).IsOver (Spec (.of R))),
      ∀ (T : Scheme.{u}) (qT : T ⟶ Spec (.of R)) (g : ∀ k, T ⟶ P' k),
        (∀ k, g k ≫ (P' k ↘ Spec (.of R)) = qT) →
          ∃ g_prod : T ⟶ P, g_prod ≫ (P ↘ Spec (.of R)) = qT ∧
            ∀ k, g_prod ≫ pr k = g k := by
  revert P'
  induction ι using Finite.induction_empty_option with
  | of_equiv e hα =>
    intro P' _ _
    obtain ⟨P, _, _, pr, _, hP⟩ := hα (fun a ↦ P' (e a))
    have h_over {i₁ i₂} (h : i₁ = i₂) :
        eqToHom (congrArg P' h) ≫ (P' i₂ ↘ Spec (.of R)) = (P' i₁ ↘ Spec (.of R)) := by
      cases h; simp
    have h_g {T : Scheme.{u}} (g : ∀ k, T ⟶ P' k) {i₁ i₂} (h : i₁ = i₂) :
        g i₁ ≫ eqToHom (congrArg P' h) = g i₂ := by
      cases h; simp
    refine ⟨P, inferInstance, inferInstance,
      fun b ↦ pr (e.symm b) ≫ eqToHom (congrArg P' (e.apply_symm_apply b)), ?_,
      fun T qT g hg ↦ ?_⟩
    · intro b
      refine ⟨?_⟩
      rw [Category.assoc, h_over (e.apply_symm_apply b), comp_over (pr (e.symm b)) (Spec (.of R))]
    · obtain ⟨g_prod, hg_over, hg_pr⟩ := hP T qT (fun a ↦ g (e a)) (fun a ↦ hg (e a))
      refine ⟨g_prod, hg_over, fun b ↦ ?_⟩
      rw [← Category.assoc, hg_pr (e.symm b), h_g g (e.apply_symm_apply b)]
  | h_empty =>
    intro P' _ _
    exact ⟨Spec (.of R), inferInstance, inferInstance, fun k ↦ k.elim, fun k ↦ k.elim,
      fun T qT _ _ ↦ ⟨qT, Category.comp_id qT, fun k ↦ k.elim⟩⟩
  | h_option hα =>
    intro P' _ _
    obtain ⟨P₀, _, _, pr₀, _, hP₀⟩ := hα (fun a ↦ P' (some a))
    let P := pullback (P₀ ↘ Spec (.of R)) (P' none ↘ Spec (.of R))
    let pr : ∀ k : Option _, P ⟶ P' k
      | none => pullback.snd _ _
      | some a => pullback.fst _ _ ≫ pr₀ a
    have hpr_over : ∀ k, (pr k).IsOver (Spec (.of R))
      | none => ⟨rfl⟩
      | some a => ⟨by
          dsimp only [pr]
          rw [Category.assoc, comp_over (pr₀ a) (Spec (.of R)), pullback.condition]
          rfl⟩
    refine ⟨P, inferInstance, inferInstance, pr, hpr_over, fun T qT g hg ↦ ?_⟩
    obtain ⟨g₀, hg₀_over, hg₀_pr⟩ := hP₀ T qT (fun a ↦ g (some a)) (fun a ↦ hg (some a))
    refine ⟨pullback.lift g₀ (g none) (hg₀_over.trans (hg none).symm), ?_, ?_⟩
    · -- `P ↘ Spec (.of R)` is definitionally `pullback.snd _ _ ≫ (P' none ↘ Spec (.of R))`.
      change pullback.lift g₀ (g none) _ ≫ pullback.snd _ _ ≫ (P' none ↘ Spec (.of R)) = qT
      rw [pullback.lift_snd_assoc, hg none]
    · rintro (_ | a)
      · exact pullback.lift_snd _ _ _
      · exact (pullback.lift_fst_assoc _ _ _ (pr₀ a)).trans (hg₀_pr a)

/-- **Projective closure of an affine scheme of finite type.** Every affine scheme `V` of finite
type over `Spec R` embeds via an open immersion over `Spec R` into a projective scheme over `R`. -/
theorem exists_openImmersion_isProjectiveOver_of_isAffine {R : Type u} [CommRing R]
    (V : Scheme.{u}) [IsAffine V] [V.Over (Spec (.of R))]
    [LocallyOfFiniteType (V ↘ Spec (.of R))] :
    ∃ (P' : Scheme.{u}) (_ : P'.Over (Spec (.of R))) (_ : P'.IsProjectiveOver R)
      (j : V ⟶ P'), IsOpenImmersion j ∧ j.IsOver (Spec (.of R)) := by
  let fV : V ⟶ Spec (.of R) := V ↘ Spec (.of R)
  let φ : CommRingCat.of R ⟶ Γ(V, ⊤) := (Scheme.ΓSpecIso (.of R)).inv ≫ fV.appTop
  have hφ_Spec : V.isoSpec.hom ≫ Spec.map φ = fV := by
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have : LocallyOfFiniteType (Spec.map φ) := by
    have hIso : Spec.map φ = V.isoSpec.inv ≫ fV := by rw [← hφ_Spec, Iso.inv_hom_id_assoc]
    rw [hIso]
    infer_instance
  let φ_ring : R →+* Γ(V, ⊤) := φ.hom
  have hφ_ft : φ_ring.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  let := φ_ring.toAlgebra
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hφ_ft
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let C := DenseCompactification.projectiveClosure (RingHom.ker π)
  let P' : Scheme.{u} := Proj ((RingHom.ker π).homogenization 0).quotientGrading
  let j : V ⟶ P' := V.isoSpec.hom ≫ Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫ C.obj.j
  have hj_over : j.IsOver (Spec (.of R)) := by
    refine ⟨?_⟩
    have hC : C.obj.j ≫ (P' ↘ Spec (.of R)) =
        Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ RingHom.ker π))) :=
      C.obj.obj.ι_π
    have he : CommRingCat.ofHom (algebraMap R _) ≫ e.toRingEquiv.toCommRingCatIso.hom = φ := by
      ext1
      exact e.toAlgHom.comp_algebraMap
    dsimp only [j]
    rw [Category.assoc, Category.assoc, hC, ← Spec.map_comp, he, hφ_Spec]
  exact ⟨P', inferInstance, inferInstance, j, inferInstance, hj_over⟩

/-- **Chow's lemma (general form, Noetherian underlying space).** Let `X` be a scheme separated and
locally of finite type over `Spec R` with Noetherian underlying topological space. Then there exist
a scheme `X'` over `Spec R`, a projective scheme `P` over `R`, a modification `π : X' ⟶ X` over
`Spec R`, and a quasi-compact immersion `i : X' ⟶ P` over `Spec R` whose graph
`(π, i) : X' ⟶ X ×_{Spec R} P` is a closed immersion. -/
@[stacks 0200]
theorem exists_isModification_and_isImmersion_isProjectiveOver_of_noetherianSpace
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))] [NoetherianSpace X]
    [IsSeparated (X ↘ Spec (.of R))] [LocallyOfFiniteType (X ↘ Spec (.of R))] :
    ∃ (X' P : Scheme.{u}) (_ : X'.Over (Spec (.of R))) (_ : P.Over (Spec (.of R)))
      (_ : P.IsProjectiveOver R) (π : X' ⟶ X) (i : X' ⟶ P)
      (emb : X' ⟶ pullback (X ↘ Spec (.of R)) (P ↘ Spec (.of R))),
      π.IsOver (Spec (.of R)) ∧ i.IsOver (Spec (.of R)) ∧ IsModification π ∧
        IsImmersion i ∧ QuasiCompact i ∧ IsClosedImmersion emb ∧
        emb ≫ pullback.fst _ _ = π ∧ emb ≫ pullback.snd _ _ = i := by
  classical
  obtain ⟨s, hs_top, hs_dense⟩ := X.exists_finite_affine_cover_dense_iInter
    NoetherianSpace.finite_irreducibleComponents
  let V : s → X.Opens := fun k ↦ k.1.1
  have hV_top : iSup V = ⊤ := by
    rw [← hs_top]
    exact le_antisymm (iSup_le fun k ↦ le_iSup₂ (f := fun U (_ : U ∈ s) ↦ U.1) k.1 k.2)
      (iSup₂_le fun W hW ↦ le_iSup V ⟨W, hW⟩)
  let U : X.Opens := ⨅ k : s, V k
  have hUV : ∀ k : s, U ≤ V k := iInf_le V
  have hU_dense : Dense (U : Set X) := by
    refine hs_dense.mono ?_
    rw [Opens.coe_iInf]
    intro x hx
    simp only [Set.mem_iInter] at hx ⊢
    exact fun k ↦ hx k.1 k.2
  have : NoetherianSpace U.toScheme := U.ι.isEmbedding.isInducing.noetherianSpace
  have hV_aff : ∀ k : s, IsAffine (V k).toScheme := fun k ↦ k.1.2
  have hV_ft : ∀ k : s, LocallyOfFiniteType ((V k).toScheme ↘ Spec (.of R)) := fun k ↦ by
    rw [← (V k).ι_comp_over (Spec (.of R))]
    infer_instance
  choose P' _ _ j _ _ using fun k : s ↦
    exists_openImmersion_isProjectiveOver_of_isAffine (R := R) (V k).toScheme
  obtain ⟨P, _, _, pr, _, hP_univ⟩ := exists_isProjectiveOver_pi (R := R) P'
  obtain ⟨g, hg, hg_pr⟩ := hP_univ U.toScheme (U.ι ≫ (X ↘ Spec (.of R)))
    (fun k ↦ X.homOfLE (hUV k) ≫ j k) fun k ↦ by
      rw [Category.assoc, comp_over (j k) (Spec (.of R)), ← (V k).ι_comp_over (Spec (.of R)),
        Scheme.homOfLE_ι_assoc]
  let f := X ↘ Spec (.of R)
  let q := P ↘ Spec (.of R)
  let X' := graphClosure f q U g hg
  let π : X' ⟶ X := graphClosureFst f q U g hg
  let i : X' ⟶ P := graphClosureSnd f q U g hg
  let : X'.Over (Spec (.of R)) := ⟨π ≫ f⟩
  have hπ_mod : IsModification π := isModification_graphClosureFst hU_dense
  have hi_imm : IsImmersion i := isImmersion_graphClosureSnd hV_top hUV
    (fun k ↦ comp_over (pr k) (Spec (.of R)))
    (fun k ↦ (comp_over (j k) (Spec (.of R))).trans ((V k).ι_comp_over (Spec (.of R))).symm) hg_pr
  refine ⟨X', P, inferInstance, inferInstance, inferInstance, π, i,
    (opensGraph f q U g hg).imageι, ⟨rfl⟩, ⟨(graphClosureFst_comp f q U g hg).symm⟩,
    hπ_mod, hi_imm, inferInstance, inferInstance,
    (graphClosureFst_def f q U g hg).symm, (graphClosureSnd_def f q U g hg).symm⟩

/-- **Chow's lemma (general form over a Noetherian ring).** Every scheme `X` separated and of
finite type over a Noetherian ring `R` admits a modification `π : X' ⟶ X` over `Spec R` such that
`X'` embeds via a quasi-compact immersion `i : X' ⟶ P` over `Spec R` into a projective scheme `P`
over `R`, with `(π, i) : X' ⟶ X ×_{Spec R} P` a closed immersion. -/
@[stacks 0200]
theorem exists_isModification_and_isImmersion_isProjectiveOver
    {R : Type u} [CommRing R] [IsNoetherianRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [IsSeparated (X ↘ Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [LocallyOfFiniteType (X ↘ Spec (.of R))] :
    ∃ (X' P : Scheme.{u}) (_ : X'.Over (Spec (.of R))) (_ : P.Over (Spec (.of R)))
      (_ : P.IsProjectiveOver R) (π : X' ⟶ X) (i : X' ⟶ P)
      (emb : X' ⟶ pullback (X ↘ Spec (.of R)) (P ↘ Spec (.of R))),
      π.IsOver (Spec (.of R)) ∧ i.IsOver (Spec (.of R)) ∧ IsModification π ∧
        IsImmersion i ∧ QuasiCompact i ∧ IsClosedImmersion emb ∧
        emb ≫ pullback.fst _ _ = π ∧ emb ≫ pullback.snd _ _ = i := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of R))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of R))
  have : IsNoetherian X := {}
  exact exists_isModification_and_isImmersion_isProjectiveOver_of_noetherianSpace X

/-- **Chow's lemma with ambient `Proj (Sym_R M)`.** Every scheme `X` separated and of finite type
over a Noetherian ring `R` admits a modification `π : X' ⟶ X` over `Spec R`, a finite `R`-module
`M`, and a quasi-compact immersion `i : X' ⟶ Proj (Sym_R M)` over `Spec R` whose graph
`(π, i) : X' ⟶ X ×_{Spec R} Proj (Sym_R M)` is a closed immersion. -/
@[stacks 0201]
theorem exists_isModification_and_isImmersion_proj
    {R : Type u} [CommRing R] [IsNoetherianRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [IsSeparated (X ↘ Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    [LocallyOfFiniteType (X ↘ Spec (.of R))] :
    ∃ (X' : Scheme.{u}) (_ : X'.Over (Spec (.of R))) (M : Type u) (_ : AddCommMonoid M)
      (_ : Module R M) (_ : Module.Finite R M) (π : X' ⟶ X)
      (i : X' ⟶ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M))
      (emb : X' ⟶ pullback (X ↘ Spec (.of R))
        (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) ↘ Spec (.of R))),
      π.IsOver (Spec (.of R)) ∧ i.IsOver (Spec (.of R)) ∧ IsModification π ∧
        IsImmersion i ∧ QuasiCompact i ∧ IsClosedImmersion emb ∧
        emb ≫ pullback.fst _ _ = π ∧ emb ≫ pullback.snd _ _ = i := by
  obtain ⟨X', P, _, _, _, π, i, emb, _, _, _, _, _, _, hemb_fst, hemb_snd⟩ :=
    exists_isModification_and_isImmersion_isProjectiveOver (R := R) X
  obtain ⟨M, _, _, _, fP, _, _⟩ :=
    Scheme.IsProjectiveOver.exists_isClosedImmersion (R := R) (X := P)
  let ℙM := Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M)
  have heX : (X ↘ Spec (.of R)) ≫ 𝟙 _ = 𝟙 X ≫ (X ↘ Spec (.of R)) := by simp
  have heP : (P ↘ Spec (.of R)) ≫ 𝟙 _ = fP ≫ (ℙM ↘ Spec (.of R)) := by
    rw [Category.comp_id, comp_over fP (Spec (.of R))]
  let pMap := pullback.map (X ↘ Spec (.of R)) (P ↘ Spec (.of R)) (X ↘ Spec (.of R))
    (ℙM ↘ Spec (.of R)) (𝟙 X) fP (𝟙 _) heX heP
  have hpMap : IsClosedImmersion pMap := by
    dsimp only [pMap]
    rw [pullback_map_eq_pullbackFstFstIso_inv]
    infer_instance
  refine ⟨X', inferInstance, M, inferInstance, inferInstance, inferInstance, π, i ≫ fP,
    emb ≫ pMap, inferInstance, inferInstance, ‹_›, inferInstance, inferInstance, inferInstance,
    ?_, ?_⟩
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, hemb_fst]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hemb_snd]

/-- **Chow's lemma for proper schemes (Noetherian underlying space).** Every proper scheme `X` over
`Spec R` with Noetherian underlying topological space admits a modification `π : X' ⟶ X` over
`Spec R` with `X'` projective over `R`. -/
@[stacks 0200]
theorem exists_isProjectiveOver_and_isModification_of_noetherianSpace
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))] [NoetherianSpace X]
    [IsProper (X ↘ Spec (.of R))] :
    ∃ (X' : Scheme.{u}) (_ : X'.Over (Spec (.of R))) (_ : X'.IsProjectiveOver R) (π : X' ⟶ X),
      π.IsOver (Spec (.of R)) ∧ IsModification π := by
  obtain ⟨X', P, _, _, _, π, i, _, _, _, _, _, _, _, _, _⟩ :=
    exists_isModification_and_isImmersion_isProjectiveOver_of_noetherianSpace (R := R) X
  have hi_comp : i ≫ (P ↘ Spec (.of R)) = π ≫ (X ↘ Spec (.of R)) :=
    (comp_over i (Spec (.of R))).trans (comp_over π (Spec (.of R))).symm
  have : IsProper (i ≫ (P ↘ Spec (.of R))) := by
    rw [hi_comp]
    infer_instance
  have : IsProper i := IsProper.of_comp (f := i) (g := P ↘ Spec (.of R))
  have : IsClosedImmersion i := .of_isPreimmersion i i.isClosedMap.isClosed_range
  have : X'.IsProjectiveOver R := .of_isClosedImmersion R i
  exact ⟨X', inferInstance, inferInstance, π, inferInstance, ‹_›⟩

/-- **Chow's lemma for proper schemes over a Noetherian ring.** Every proper scheme `X` over a
Noetherian ring `R` admits a modification `π : X' ⟶ X` over `Spec R` with `X'` projective over
`R`. -/
@[stacks 0200]
theorem exists_isProjectiveOver_and_isModification
    {R : Type u} [CommRing R] [IsNoetherianRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [IsProper (X ↘ Spec (.of R))] :
    ∃ (X' : Scheme.{u}) (_ : X'.Over (Spec (.of R))) (_ : X'.IsProjectiveOver R) (π : X' ⟶ X),
      π.IsOver (Spec (.of R)) ∧ IsModification π := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of R))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of R))
  have : IsNoetherian X := {}
  exact exists_isProjectiveOver_and_isModification_of_noetherianSpace X

end TauCeti.AlgebraicGeometry
