/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.LinearAlgebra.Alternating.BaseChange
import Mathlib.CategoryTheory.Abelian.Exact
import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Base change of the Chevalley–Eilenberg complex and cohomology

Let `L` be a Lie algebra over a commutative ring `R`, `M` an `L`-module, and `S` a commutative
`R`-algebra. Extending scalars on alternating maps commutes with the Lie derivative
(`TauCeti.LieModule.Cohomology.lie_baseChange`) and with the Chevalley–Eilenberg differential in
every degree (`TauCeti.LieModule.Cohomology.d_baseChange`). These assemble into a canonical
comparison morphism of cochain complexes
`TauCeti.LieModule.Cohomology.baseChangeCochainComplexHom` from `S ⊗[R] C•(L, M)` to
`C•(S ⊗[R] L, S ⊗[R] M)`.

When `L` is finitely generated and projective as an `R`-module, the comparison morphism is an
isomorphism of cochain complexes (`TauCeti.LieModule.Cohomology.baseChangeCochainComplexIso`),
via `AlternatingMap.isBaseChange_baseChangeHom`. When `S` is additionally flat over `R`, extension
of scalars preserves homology and hence yields a canonical isomorphism
`S ⊗[R] Hⁿ(L, M) ≅ Hⁿ(S ⊗[R] L, S ⊗[R] M)` in every degree
(`TauCeti.LieModule.Cohomology.baseChangeCohomologyIso`,
`TauCeti.LieModule.Cohomology.baseChangeCohomologyLinearEquiv`). In particular, for a
finite-dimensional Lie algebra over a field `E` and any field extension `E'/E`, all hypotheses are
inferred automatically.

## Main definitions

* `TauCeti.LieModule.Cohomology.baseChangeCochainComplexHom`: the canonical morphism
  `S ⊗[R] C•(L, M) ⟶ C•(S ⊗[R] L, S ⊗[R] M)`.
* `TauCeti.LieModule.Cohomology.baseChangeCochainComplexIso`: the isomorphism of cochain complexes
  for finite projective `L`.
* `TauCeti.LieModule.Cohomology.baseChangeCohomologyIso`: the isomorphism on cohomology in every
  degree for finite projective `L` and flat `S`.
* `TauCeti.LieModule.Cohomology.baseChangeCohomologyLinearEquiv`: the `S`-linear equivalence
  `S ⊗[R] Hⁿ(L, M) ≃ₗ[S] Hⁿ(S ⊗[R] L, S ⊗[R] M)`.

## Main results

* `TauCeti.LieModule.Cohomology.lie_baseChange`: scalar extension intertwines the Lie derivative.
* `TauCeti.LieModule.Cohomology.d_baseChange`: scalar extension commutes with the
  Chevalley–Eilenberg differential.
* `TauCeti.LieModule.Cohomology.isIso_baseChangeCochainComplexHom`: the comparison morphism is an
  isomorphism for finite projective `L`.
-/

public section

open CategoryTheory AlternatingMap
open scoped TensorProduct ChangeOfRings

namespace TauCeti.LieModule.Cohomology

universe uR uS uL uM

section

variable {R : Type uR} (S : Type uS) [CommRing R] [CommRing S] [Algebra R S]

private theorem preservesHomology_extendScalars.{uW} [Module.Flat R S] :
    (ModuleCat.extendScalars.{uR, uS, uW} (algebraMap R S)).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun C hC ↦ by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC
    let S' : ShortComplex (ModuleCat.{max uS uW} S) :=
      ShortComplex.mk
        (ModuleCat.ofHom (LinearMap.baseChange S C.f.hom))
        (ModuleCat.ofHom (LinearMap.baseChange S C.g.hom))
        (by
          rw [← ModuleCat.ofHom_comp, ← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, C.zero]
          simp)
    have hS' : S'.Exact := by
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      exact Module.Flat.lTensor_exact S hC
    have hcomm (X Y : ModuleCat.{uW} R) (f : X ⟶ Y) :
        (ModuleCat.extendScalarsAlgebraMapIso X).inv ≫
          (ModuleCat.extendScalars (algebraMap R S)).map f ≫
          (ModuleCat.extendScalarsAlgebraMapIso Y).hom =
        ModuleCat.ofHom (LinearMap.baseChange S f.hom) := by
      refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
      induction z using TensorProduct.inductionOn with
      | tmul s x =>
        simp only [CategoryTheory.comp_apply, ModuleCat.hom_ofHom, LinearMap.baseChange_tmul]
        rw [ModuleCat.extendScalarsAlgebraMapIso_inv_tmul]
        exact (congrArg (ModuleCat.extendScalarsAlgebraMapIso Y).hom
          (ModuleCat.ExtendScalars.map_tmul (algebraMap R S) f s x)).trans
          (ModuleCat.extendScalarsAlgebraMapIso_hom_tmul Y s (f x))
      | add x y hx hy => simp only [map_add, hx, hy]
    have hcomm' (X Y : ModuleCat.{uW} R) (f : X ⟶ Y) :
        (ModuleCat.extendScalarsAlgebraMapIso X).inv ≫
          (ModuleCat.extendScalars (algebraMap R S)).map f =
        ModuleCat.ofHom (LinearMap.baseChange S f.hom) ≫
          (ModuleCat.extendScalarsAlgebraMapIso Y).inv := by
      rw [← hcomm X Y f]
      simp
    exact ShortComplex.exact_of_iso
      (ShortComplex.isoMk
        (ModuleCat.extendScalarsAlgebraMapIso C.X₁).symm
        (ModuleCat.extendScalarsAlgebraMapIso C.X₂).symm
        (ModuleCat.extendScalarsAlgebraMapIso C.X₃).symm
        (hcomm' C.X₁ C.X₂ C.f) (hcomm' C.X₂ C.X₃ C.g)) hS'

end

variable {R : Type uR} (S : Type uS) {L : Type uL} {M : Type uM}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Scalar extension of cochains intertwines the Lie derivative on pure tensors. -/
theorem lie_baseChange {n : ℕ} (s : S) (x : L) (ω : L [⋀^Fin n]→ₗ[R] M) :
    ⁅s ⊗ₜ[R] x, ω.baseChange S⁆ = s • ⁅x, ω⁆.baseChange S := by
  refine AlternatingMap.ext_tmul fun m ↦ ?_
  rw [lie_apply, smul_apply, baseChange_apply_one_tmul, baseChange_apply_one_tmul, lie_apply,
    LieAlgebra.ExtendScalars.bracket_tmul, mul_one, TensorProduct.tmul_sub, smul_sub,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_sum, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hupd : Function.update (fun j : Fin n ↦ (1 : S) ⊗ₜ[R] m j) i
      ⁅s ⊗ₜ[R] x, (1 : S) ⊗ₜ[R] m i⁆ =
      fun j : Fin n ↦ Function.update (fun _ : Fin n ↦ (1 : S)) i s j ⊗ₜ[R]
        Function.update m i ⁅x, m i⁆ j := by
    ext j
    by_cases hij : j = i
    · subst hij
      simp [LieAlgebra.ExtendScalars.bracket_tmul]
    · simp [hij]
  rw [hupd, baseChange_apply_tmul, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [TensorProduct.smul_tmul']

/-- Scalar extension of cochains commutes with the Chevalley–Eilenberg differential in every
degree. -/
theorem d_baseChange (n : ℕ) (ω : L [⋀^Fin n]→ₗ[R] M) :
    d S (S ⊗[R] L) (S ⊗[R] M) n (ω.baseChange S) = (d R L M n ω).baseChange S := by
  induction n with
  | zero =>
    refine AlternatingMap.ext_tmul fun m ↦ ?_
    have h0 : (ω.baseChange S) ![] = (1 : S) ⊗ₜ[R] ω ![] := by
      simpa [Subsingleton.elim (Fin.elim0 : Fin 0 → L) ![],
        Subsingleton.elim (fun i : Fin 0 ↦ (1 : S) ⊗ₜ[R] ![] i) ![]] using
        baseChange_apply_one_tmul S ω ![]
    rw [d_zero_apply, h0, LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
      baseChange_apply_one_tmul, d_zero_apply]
  | succ n ih =>
    refine curryLeft_injective (LinearMap.ext fun z ↦ ?_)
    induction z using TensorProduct.inductionOn with
    | tmul s x =>
      rw [curryLeft_d_succ, lie_baseChange, baseChange_curryLeft, map_smul, ih,
        baseChange_curryLeft, curryLeft_d_succ, baseChange_sub]
      ext v
      simp [smul_sub]
    | add z₁ z₂ h₁ h₂ => simp [map_add, h₁, h₂]

variable (R L M)

omit [LieRingModule L M] [LieModule R L M] in
private noncomputable def baseChangeDegreeHom (n : ℕ) :
    (ModuleCat.extendScalars.{uR, uS, max uL uM} (algebraMap R S)).obj
        (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M)) ⟶
      ModuleCat.of S ((S ⊗[R] L) [⋀^Fin n]→ₗ[S] (S ⊗[R] M)) :=
  (ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M))).hom ≫
    ModuleCat.ofHom (R := S) (X := S ⊗[R] (L [⋀^Fin n]→ₗ[R] M))
      (LinearMap.liftBaseChange S (AlternatingMap.baseChangeHom R S L M n))

omit [LieRingModule L M] [LieModule R L M] in
private theorem baseChangeDegreeHom_tmul (n : ℕ) (s : S) (ω : L [⋀^Fin n]→ₗ[R] M) :
    baseChangeDegreeHom R S L M n (s ⊗ₜ[R, algebraMap R S] ω) = s • ω.baseChange S := by
  let M₀ := ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M)
  let f := (ModuleCat.extendScalarsAlgebraMapIso (S := S) M₀).hom
  let g : ModuleCat.of S (S ⊗[R] M₀) ⟶
      ModuleCat.of S ((S ⊗[R] L) [⋀^Fin n]→ₗ[S] (S ⊗[R] M)) :=
    ModuleCat.ofHom (LinearMap.liftBaseChange S (AlternatingMap.baseChangeHom R S L M n))
  refine ((CategoryTheory.comp_apply f g (s ⊗ₜ[R, algebraMap R S] ω)).trans
    (congrArg g (ModuleCat.extendScalarsAlgebraMapIso_hom_tmul M₀ s ω))).trans ?_
  simp only [g, ModuleCat.hom_ofHom, LinearMap.liftBaseChange_tmul]
  rw [baseChangeHom_apply]

private theorem baseChangeDegreeHom_comm (i : ℕ) :
    baseChangeDegreeHom R S L M i ≫ ModuleCat.ofHom (d S (S ⊗[R] L) (S ⊗[R] M) i) =
      (ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom (d R L M i)) ≫
        baseChangeDegreeHom R S L M (i + 1) := by
  rw [← cancel_epi
    (ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin i]→ₗ[R] M))).inv]
  refine ConcreteCategory.hom_ext _ _ fun w ↦ ?_
  induction w using TensorProduct.inductionOn with
  | tmul s ω =>
    simp only [CategoryTheory.comp_apply, ModuleCat.hom_ofHom]
    rw [ModuleCat.extendScalarsAlgebraMapIso_inv_tmul]
    calc
      d S (S ⊗[R] L) (S ⊗[R] M) i
          (baseChangeDegreeHom R S L M i (s ⊗ₜ[R, algebraMap R S] ω))
        = d S (S ⊗[R] L) (S ⊗[R] M) i (s • ω.baseChange S) :=
          congrArg (d S (S ⊗[R] L) (S ⊗[R] M) i) (baseChangeDegreeHom_tmul R S L M i s ω)
      _ = s • (d R L M i ω).baseChange S := by rw [map_smul, d_baseChange]
      _ = baseChangeDegreeHom R S L M (i + 1) (s ⊗ₜ[R, algebraMap R S] d R L M i ω) :=
          (baseChangeDegreeHom_tmul R S L M (i + 1) s (d R L M i ω)).symm
      _ = baseChangeDegreeHom R S L M (i + 1)
            (((ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom (d R L M i)))
              (s ⊗ₜ[R, algebraMap R S] ω)) :=
          congrArg (baseChangeDegreeHom R S L M (i + 1))
            (ModuleCat.ExtendScalars.map_tmul (algebraMap R S)
              (ModuleCat.ofHom (d R L M i)) s ω).symm
  | add x y hx hy =>
    simp only [map_add] at hx hy ⊢
    rw [hx, hy]

/-- The canonical comparison morphism of cochain complexes from `S ⊗[R] C•(L, M)` to
`C•(S ⊗[R] L, S ⊗[R] M)`, sending `s ⊗ₜ ω` to `s • ω.baseChange S` in every degree. -/
noncomputable def baseChangeCochainComplexHom :
    ((ModuleCat.extendScalars.{uR, uS, max uL uM} (algebraMap R S)).mapHomologicalComplex
        (.up ℕ)).obj (cochainComplex R L M) ⟶
      cochainComplex S (S ⊗[R] L) (S ⊗[R] M) where
  f n := baseChangeDegreeHom R S L M n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [Functor.mapHomologicalComplex_obj_d, cochainComplex_d_succ, cochainComplex_d_succ]
    exact baseChangeDegreeHom_comm R S L M i

/-- On a pure tensor `s ⊗ₜ ω` in degree `n`, `baseChangeCochainComplexHom` evaluates to
`s • ω.baseChange S`. -/
theorem baseChangeCochainComplexHom_f_tmul (n : ℕ) (s : S) (ω : L [⋀^Fin n]→ₗ[R] M) :
    (baseChangeCochainComplexHom R S L M).f n (s ⊗ₜ[R, algebraMap R S] ω) =
      s • ω.baseChange S :=
  baseChangeDegreeHom_tmul R S L M n s ω

/-- When `L` is finitely generated and projective over `R`, the base-change comparison morphism of
Chevalley–Eilenberg complexes is an isomorphism. -/
instance isIso_baseChangeCochainComplexHom [Module.Finite R L] [Module.Projective R L] :
    IsIso (baseChangeCochainComplexHom R S L M) := by
  have : ∀ n, IsIso ((baseChangeCochainComplexHom R S L M).f n) := fun n ↦ by
    have hlift : LinearMap.liftBaseChange S (AlternatingMap.baseChangeHom R S L M n) =
        (AlternatingMap.baseChangeEquiv R S L M n).toLinearMap := by
      apply LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.inductionOn with
      | tmul s ω => simp
      | add x y hx hy => simp [hx, hy]
    let e : (ModuleCat.extendScalars.{uR, uS, max uL uM} (algebraMap R S)).obj
        (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M)) ≅
        ModuleCat.of S ((S ⊗[R] L) [⋀^Fin n]→ₗ[S] (S ⊗[R] M)) :=
      ModuleCat.extendScalarsAlgebraMapIso (ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M)) ≪≫
        (AlternatingMap.baseChangeEquiv R S L M n).toModuleIso
    have hcomp : (baseChangeCochainComplexHom R S L M).f n = e.hom := by
      dsimp only [baseChangeCochainComplexHom, baseChangeDegreeHom, e, Iso.trans_hom,
        LinearEquiv.toModuleIso_hom]
      rw [hlift]
      rfl
    rw [hcomp]
    exact e.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Base change of the Chevalley–Eilenberg cochain complex.** For a finitely generated projective
Lie algebra `L` over `R` and any commutative `R`-algebra `S`,
`S ⊗[R] C•(L, M) ≅ C•(S ⊗[R] L, S ⊗[R] M)`. -/
noncomputable def baseChangeCochainComplexIso [Module.Finite R L] [Module.Projective R L] :
    ((ModuleCat.extendScalars.{uR, uS, max uL uM} (algebraMap R S)).mapHomologicalComplex
        (.up ℕ)).obj (cochainComplex R L M) ≅
      cochainComplex S (S ⊗[R] L) (S ⊗[R] M) :=
  asIso (baseChangeCochainComplexHom R S L M)

/-- The forward morphism of `baseChangeCochainComplexIso` is `baseChangeCochainComplexHom`. -/
@[simp]
theorem baseChangeCochainComplexIso_hom [Module.Finite R L] [Module.Projective R L] :
    (baseChangeCochainComplexIso R S L M).hom = baseChangeCochainComplexHom R S L M :=
  (rfl)

/-- **Base change of Lie algebra cohomology.** For a finitely generated projective Lie algebra `L`
over `R` and a flat commutative `R`-algebra `S`, extension of scalars commutes with
Chevalley–Eilenberg cohomology in every degree:
`S ⊗[R] Hⁿ(L, M) ≅ Hⁿ(S ⊗[R] L, S ⊗[R] M)`. -/
noncomputable def baseChangeCohomologyIso [Module.Finite R L] [Module.Projective R L]
    [Module.Flat R S] (n : ℕ) :
    (ModuleCat.extendScalars.{uR, uS, max uL uM} (algebraMap R S)).obj (cohomology R L M n) ≅
      cohomology S (S ⊗[R] L) (S ⊗[R] M) n := by
  have := preservesHomology_extendScalars.{uR, uS, max uL uM} (R := R) S
  exact ((ModuleCat.extendScalars.{uR, uS, max uL uM}
        (algebraMap R S)).mapHomologicalComplexCompHomologyFunctorIso (.up ℕ) n).symm.app
      (cochainComplex R L M) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℕ) n).mapIso
      (baseChangeCochainComplexIso R S L M)

/-- The `S`-linear equivalence `S ⊗[R] Hⁿ(L, M) ≃ₗ[S] Hⁿ(S ⊗[R] L, S ⊗[R] M)` for a finitely
generated projective Lie algebra `L` and a flat commutative `R`-algebra `S`. -/
noncomputable def baseChangeCohomologyLinearEquiv [Module.Finite R L] [Module.Projective R L]
    [Module.Flat R S] (n : ℕ) :
    S ⊗[R] cohomology R L M n ≃ₗ[S] cohomology S (S ⊗[R] L) (S ⊗[R] M) n :=
  ((ModuleCat.extendScalarsAlgebraMapIso (cohomology R L M n)).symm ≪≫
    baseChangeCohomologyIso R S L M n).toLinearEquiv

end TauCeti.LieModule.Cohomology
