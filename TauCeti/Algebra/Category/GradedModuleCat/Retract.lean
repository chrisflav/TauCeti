/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.Module.GradedModule.Free

/-!
# Graded free isomorphisms and retracts in `GradedModuleCat`

A family of homogeneous elements of `M` forming an `A`-basis induces a graded isomorphism
`free 𝒜 d ≅ M` via `freeLift`. Combining this with the graded Nakayama lifting theorem shows that
any bounded-below projective object `P` whose homogeneous elements `v i` form an `𝒜 0`-basis modulo
`A₊ P` is isomorphic to `free 𝒜 d`.

For finite index types, `free 𝒜 s` is canonically isomorphic both to the shifted function space
`piShiftObj 𝒜 s` (with carrier `J → A`) and to the categorical biproduct
`⨁ j : J, (regular (𝒜 := 𝒜)).shiftObj (s j)`. Over a nonnegatively `ℤ`-graded `k`-algebra connected
over a principal ideal domain `k`, every finitely generated projective object — and hence every
retract of `free 𝒜 s` and the splitting object of every idempotent endomorphism of a finite
biproduct of shifted regular modules — is isomorphic to a finite graded free module `free 𝒜 d`
(equivalently `⨁ i : Fin n, A{d i}`).

## Main definitions

* `TauCeti.GradedModuleCat.freeIsoOfBasis`: the graded isomorphism `free 𝒜 d ≅ M` associated to a
  homogeneous `A`-basis of `M`.
* `TauCeti.GradedModuleCat.freeIsoOfHeadBasis`: the graded isomorphism `free 𝒜 d ≅ P` lifted from a
  homogeneous `𝒜 0`-basis of `P ⧸ A₊ P`.
* `TauCeti.GradedModuleCat.piShiftObj` and `TauCeti.GradedModuleCat.freeIsoPiShift`: the graded
  module `J → A` with shifts `s : J → ℤ` and its graded isomorphism with `free 𝒜 s`.
* `TauCeti.GradedModuleCat.freeIsoBiproduct`: the canonical isomorphism between `free 𝒜 s` and the
  finite categorical biproduct `⨁ j : J, (regular (𝒜 := 𝒜)).shiftObj (s j)`.

## Main results

* `TauCeti.GradedModuleCat.moduleProjective_of_projective` and
  `TauCeti.GradedModuleCat.projective_iff_moduleProjective`: categorical projectivity in
  `GradedModuleCat 𝒜` agrees with projectivity of the underlying `A`-module.
* `TauCeti.GradedModuleCat.exists_iso_free_of_projective`,
  `TauCeti.GradedModuleCat.exists_iso_free_of_retract`, and
  `TauCeti.GradedModuleCat.exists_iso_biproduct_shift_of_retract`: over a connected nonnegatively
  graded algebra over a PID, any finitely generated projective object or retract of a finite shifted
  free module or biproduct of shifted regular modules is isomorphic to one.
* `TauCeti.GradedModuleCat.exists_split_free_of_idempotent` and
  `TauCeti.GradedModuleCat.exists_split_biproduct_shift_of_idempotent`: every degree-zero idempotent
  endomorphism of a finite shifted free module or biproduct of shifted regular modules splits
  through a finite shifted free module or biproduct.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.GradedModuleCat

universe uk uA v uI uJ

section General

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Every categorically projective object of `GradedModuleCat 𝒜` has a projective underlying
`A`-module, being a retract of its canonical graded free presentation. -/
theorem moduleProjective_of_projective (P : GradedModuleCat.{max uA v} 𝒜) [Projective P] :
    Module.Projective A P := by
  let I := Σ p : ℤ, P.grading.piece p
  let f : free 𝒜 (Sigma.fst : I → ℤ) ⟶ P := freeLift Sigma.snd
  have hrange : (Set.range fun i : I ↦ (i.2 : P)) = {y : P | ∃ p, y ∈ P.grading.piece p} := by
    ext y
    simp [I]
  have hf : Function.Surjective f.hom := (freeLift_surjective_iff _).mpr <| by
    rw [hrange, P.grading.span_setOf_exists_mem_piece_eq_top A]
  have : Epi f := (epi_iff_surjective f).mpr hf
  have : Module.Projective A (free 𝒜 (Sigma.fst : I → ℤ)) :=
    inferInstanceAs (Module.Projective A (DirectSum I fun _ ↦ A))
  exact Module.Projective.of_split (Projective.factorThru (𝟙 P) f).hom f.hom <| by
    simpa only [hom_comp, hom_id] using congrArg Hom.hom (Projective.factorThru_comp (𝟙 P) f)

/-- An object of `GradedModuleCat 𝒜` is categorically projective if and only if its underlying
`A`-module is projective. -/
theorem projective_iff_moduleProjective (P : GradedModuleCat.{max uA v} 𝒜) :
    Projective P ↔ Module.Projective A P :=
  ⟨fun _ ↦ moduleProjective_of_projective P, fun _ ↦ inferInstance⟩

/-- A homogeneous `A`-basis of `M` makes `freeLift` an isomorphism `free 𝒜 d ⟶ M`. -/
theorem isIso_freeLift_of_basis {I : Type uI} {d : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (b : Module.Basis I A M) (hb : ∀ i, b i ∈ M.grading.piece (d i)) :
    IsIso (freeLift fun i ↦ (⟨b i, hb i⟩ : M.grading.piece (d i))) := by
  classical
  let v : ∀ i, M.grading.piece (d i) := fun i ↦ ⟨b i, hb i⟩
  have hcomp : (freeLift v).hom.comp (finsuppLequivDFinsupp A).toLinearMap = b.repr.symm := by
    apply Finsupp.lhom_ext
    intro i a
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, finsuppLequivDFinsupp_apply_apply,
      Function.comp_apply, Finsupp.toDFinsupp_single, DirectSum.single_eq_lof A,
      Module.Basis.repr_symm_apply]
    rw [Finsupp.linearCombination_single]
    exact freeLift_lof v i a
  rw [isIso_iff_bijective]
  have hbij : Function.Bijective ((freeLift v).hom ∘ finsuppLequivDFinsupp A) :=
    LinearMap.coe_comp (freeLift v).hom (finsuppLequivDFinsupp A).toLinearMap ▸
      hcomp ▸ b.repr.symm.bijective
  exact (Function.Bijective.of_comp_iff (freeLift v).hom (finsuppLequivDFinsupp A).bijective).mp
    hbij

/-- The graded isomorphism `free 𝒜 d ≅ M` induced by a homogeneous `A`-basis of `M`. -/
def freeIsoOfBasis {I : Type uI} {d : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (b : Module.Basis I A M) (hb : ∀ i, b i ∈ M.grading.piece (d i)) :
    free 𝒜 d ≅ M :=
  have := isIso_freeLift_of_basis b hb
  asIso (freeLift fun i ↦ ⟨b i, hb i⟩)

/-- The forward morphism of `freeIsoOfBasis` is `freeLift` on the basis vectors. -/
@[simp]
theorem freeIsoOfBasis_hom {I : Type uI} {d : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (b : Module.Basis I A M) (hb : ∀ i, b i ∈ M.grading.piece (d i)) :
    (freeIsoOfBasis b hb).hom = freeLift fun i ↦ ⟨b i, hb i⟩ :=
  (rfl)

/-- For a bounded-below projective graded module `P` over a nonnegatively graded algebra, a
homogeneous family forming an `𝒜 0`-basis modulo `A₊ P` induces a graded isomorphism
`freeLift v : free 𝒜 d ⟶ P`. -/
theorem isIso_freeLift_of_head_basis {I : Type uI} {d : I → ℤ}
    {P : GradedModuleCat.{max uA uI} 𝒜} [Projective P]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (b_low : ℤ) (hlow : ∀ p < b_low, P.grading.piece p = ⊥)
    (v : ∀ i, P.grading.piece (d i))
    (hli : LinearIndependent (SetLike.GradeZero.subalgebra 𝒜)
      fun i ↦ (InternalGrading.positiveSubmodule 𝒜 P hneg).mkQ (v i))
    (hspan : ⊤ ≤ Submodule.span (SetLike.GradeZero.subalgebra 𝒜)
      (Set.range fun i ↦ (InternalGrading.positiveSubmodule 𝒜 P hneg).mkQ (v i))) :
    IsIso (freeLift v) := by
  have : Module.Projective A P := moduleProjective_of_projective P
  let B := P.grading.basisOfHead 𝒜 hneg b_low hlow (fun i ↦ (v i).2) hli hspan
  have hB : ∀ i, B i ∈ P.grading.piece (d i) := fun i ↦ by simp [B]
  have hv : (fun i ↦ (⟨B i, hB i⟩ : P.grading.piece (d i))) = v :=
    funext fun i ↦
      Subtype.ext (congrFun (P.grading.coe_basisOfHead 𝒜 hneg b_low hlow _ hli hspan) i)
  exact hv ▸ isIso_freeLift_of_basis B hB

/-- The graded isomorphism `free 𝒜 d ≅ P` lifted from a homogeneous `𝒜 0`-basis of `P ⧸ A₊ P`. -/
def freeIsoOfHeadBasis {I : Type uI} {d : I → ℤ}
    {P : GradedModuleCat.{max uA uI} 𝒜} [Projective P]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (b_low : ℤ) (hlow : ∀ p < b_low, P.grading.piece p = ⊥)
    (v : ∀ i, P.grading.piece (d i))
    (hli : LinearIndependent (SetLike.GradeZero.subalgebra 𝒜)
      fun i ↦ (InternalGrading.positiveSubmodule 𝒜 P hneg).mkQ (v i))
    (hspan : ⊤ ≤ Submodule.span (SetLike.GradeZero.subalgebra 𝒜)
      (Set.range fun i ↦ (InternalGrading.positiveSubmodule 𝒜 P hneg).mkQ (v i))) :
    free 𝒜 d ≅ P :=
  have := isIso_freeLift_of_head_basis hneg b_low hlow v hli hspan
  asIso (freeLift v)

/-- The forward morphism of `freeIsoOfHeadBasis` is `freeLift v`. -/
@[simp]
theorem freeIsoOfHeadBasis_hom {I : Type uI} {d : I → ℤ}
    {P : GradedModuleCat.{max uA uI} 𝒜} [Projective P]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (b_low : ℤ) (hlow : ∀ p < b_low, P.grading.piece p = ⊥)
    (v : ∀ i, P.grading.piece (d i))
    (hli : LinearIndependent (SetLike.GradeZero.subalgebra 𝒜)
      fun i ↦ (InternalGrading.positiveSubmodule 𝒜 P hneg).mkQ (v i))
    (hspan : ⊤ ≤ Submodule.span (SetLike.GradeZero.subalgebra 𝒜)
      (Set.range fun i ↦ (InternalGrading.positiveSubmodule 𝒜 P hneg).mkQ (v i))) :
    (freeIsoOfHeadBasis hneg b_low hlow v hli hspan).hom = freeLift v :=
  (rfl)

variable (𝒜) in
/-- The finite shifted product `J → A` bundled as an object of `GradedModuleCat 𝒜`, with `j`-th
coordinate shifted by `s j`. -/
abbrev piShiftObj {J : Type uJ} [Finite J] (s : J → ℤ) : GradedModuleCat.{max uA uJ} 𝒜 where
  carrier := J → A
  grading := InternalGrading.piShiftGrading 𝒜 s
  gradedSMul := InternalGrading.instGradedSMulPiShiftGrading 𝒜 s

/-- Membership in the degree-`p` piece of `piShiftObj 𝒜 s` is checked coordinatewise. This is not
a simp lemma because `InternalGrading.mem_piShiftGrading_piece_iff` already simplifies the unfolded
piece. -/
theorem mem_piShiftObj_piece_iff {J : Type uJ} [Finite J] (s : J → ℤ) (p : ℤ)
    (x : piShiftObj 𝒜 s) :
    dsimp% only (x ∈ (piShiftObj 𝒜 s).grading.piece p) ↔ ∀ j, x j ∈ 𝒜 (p - s j) :=
  InternalGrading.mem_piShiftGrading_piece_iff 𝒜 s p x

variable (𝒜) in
/-- For a finite index type `J`, the graded free module `free 𝒜 s` is canonically isomorphic to the
shifted function space `piShiftObj 𝒜 s`. -/
def freeIsoPiShift {J : Type uJ} [Finite J] (s : J → ℤ) :
    free 𝒜 s ≅ piShiftObj 𝒜 s :=
  letI := Fintype.ofFinite J
  isoMk (DirectSum.linearEquivFunOnFintype A J fun _ ↦ A) fun p x ↦ by
    rw [mem_free_piece_iff, mem_piShiftObj_piece_iff]
    exact forall_congr' fun _ ↦ Iff.rfl

/-- Evaluating the forward map of `freeIsoPiShift` at coordinate `j` reads the `j`-th summand. -/
@[simp]
theorem hom_freeIsoPiShift_apply {J : Type uJ} [Finite J] (s : J → ℤ) (x : free 𝒜 s) (j : J) :
    (freeIsoPiShift 𝒜 s).hom.hom x j = x j :=
  letI := Fintype.ofFinite J
  (rfl)

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable (𝒜) in
/-- For a finite index type `J : Type`, the graded free module `free 𝒜 s` is canonically isomorphic
to the categorical biproduct `⨁ fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)`. -/
def freeIsoBiproduct {J : Type} [Finite J] (s : J → ℤ) :
    free 𝒜 s ≅ ⨁ fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j) :=
  (productFanIsLimit fun j ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)).conePointUniqueUpToIso
    (biproduct.isLimit _)

/-- Postcomposing `(freeIsoBiproduct 𝒜 s).hom` with the `j`-th biproduct projection recovers the
`j`-th product fan projection. -/
@[simp]
theorem freeIsoBiproduct_hom_π {J : Type} [Finite J] (s : J → ℤ) (j : J) :
    (freeIsoBiproduct 𝒜 s).hom ≫ biproduct.π (fun j ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)) j =
      (productFan fun j ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)).proj j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk j)

/-- Postcomposing `(freeIsoBiproduct 𝒜 s).inv` with the `j`-th product fan projection recovers the
`j`-th biproduct projection. -/
@[simp]
theorem freeIsoBiproduct_inv_proj {J : Type} [Finite J] (s : J → ℤ) (j : J) :
    (freeIsoBiproduct 𝒜 s).inv ≫
        (productFan fun j ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)).proj j =
      biproduct.π (fun j ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)) j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

end General

section ConnectedPID

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {k : Type uk} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
  {A : Type uA} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- **Categorical graded freeness of finitely generated projective objects over a connected graded
algebra over a PID.** Every finitely generated projective object `P` of `GradedModuleCat 𝒜` is
isomorphic to `free 𝒜 d` for some finite basis degrees `d : Fin n → ℤ`. -/
theorem exists_iso_free_of_projective
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    (P : GradedModuleCat.{uA} 𝒜) [Module.Finite A P] [Projective P] :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (P ≅ free 𝒜 d) := by
  have : Module.Projective A P := moduleProjective_of_projective P
  obtain ⟨n, b, d, hb⟩ := P.grading.exists_homogeneous_basis_of_projective 𝒜 hneg hzero hinj
  exact ⟨n, d, ⟨(freeIsoOfBasis b hb).symm⟩⟩

/-- **Categorical graded freeness of retracts over a connected graded algebra over a PID.** Every
retract of a finite graded free module `free 𝒜 s` in `GradedModuleCat 𝒜` is isomorphic to
`free 𝒜 d` for some finite basis degrees `d : Fin n → ℤ`. -/
theorem exists_iso_free_of_retract {J : Type} [Finite J] (s : J → ℤ)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    {P : GradedModuleCat.{uA} 𝒜} (h : CategoryTheory.Retract P (free 𝒜 s)) :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (P ≅ free 𝒜 d) := by
  let h' : CategoryTheory.Retract P (piShiftObj 𝒜 s) := h.trans (freeIsoPiShift 𝒜 s).retract
  have hsplit : h'.r.hom ∘ₗ h'.i.hom = LinearMap.id := by
    simpa only [hom_comp, hom_id] using congrArg Hom.hom h'.retract
  obtain ⟨n, b, d, hb⟩ := P.grading.exists_homogeneous_basis_of_retract_pi 𝒜 hneg hzero hinj
    h'.i.hom h'.r.hom hsplit
  exact ⟨n, d, ⟨(freeIsoOfBasis b hb).symm⟩⟩

/-- Every retract of a finite biproduct `⨁ fun j : J ↦ A{s j}` of shifted regular modules over a
nonnegatively graded algebra connected over a PID is again isomorphic to a finite biproduct
`⨁ fun i : Fin n ↦ A{d i}`. -/
theorem exists_iso_biproduct_shift_of_retract {J : Type} [Finite J] (s : J → ℤ)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    {P : GradedModuleCat.{uA} 𝒜}
    (h : CategoryTheory.Retract P (⨁ fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j))) :
    ∃ (n : ℕ) (d : Fin n → ℤ),
      Nonempty (P ≅ ⨁ fun i : Fin n ↦ (regular (𝒜 := 𝒜)).shiftObj (d i)) := by
  obtain ⟨n, d, ⟨e⟩⟩ := exists_iso_free_of_retract 𝒜 s hneg hzero hinj
    (h.trans (freeIsoBiproduct 𝒜 s).symm.retract)
  exact ⟨n, d, ⟨e ≪≫ freeIsoBiproduct 𝒜 d⟩⟩

/-- Every idempotent endomorphism `e` of `free 𝒜 s` over a nonnegatively graded algebra connected
over a PID splits through a finite graded free module `free 𝒜 d`. -/
theorem exists_split_free_of_idempotent {J : Type} [Finite J] (s : J → ℤ)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    (e : free 𝒜 s ⟶ free 𝒜 s) (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (ι : free 𝒜 d ⟶ free 𝒜 s) (π : free 𝒜 s ⟶ free 𝒜 d),
      ι ≫ π = 𝟙 (free 𝒜 d) ∧ π ≫ ι = e := by
  obtain ⟨P, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split (free 𝒜 s) e he
  obtain ⟨n, d, ⟨φ⟩⟩ := exists_iso_free_of_retract 𝒜 s hneg hzero hinj ⟨i, r, hir⟩
  refine ⟨n, d, φ.inv ≫ i, r ≫ φ.hom, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc i, hir, Category.id_comp, φ.inv_hom_id]
  · rw [Category.assoc, ← Category.assoc φ.hom, φ.hom_inv_id, Category.id_comp, hri]

/-- Every idempotent endomorphism `e` of a finite biproduct `⨁ fun j : J ↦ A{s j}` of shifted
regular modules over a nonnegatively graded algebra connected over a PID splits through a finite
biproduct `⨁ fun i : Fin n ↦ A{d i}`. -/
theorem exists_split_biproduct_shift_of_idempotent {J : Type} [Finite J] (s : J → ℤ)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    (e : (⨁ fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)) ⟶
      ⨁ fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j))
    (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (⨁ fun i : Fin n ↦ (regular (𝒜 := 𝒜)).shiftObj (d i)) ⟶
        ⨁ fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j))
      (π : (⨁ fun j : J ↦ (regular (𝒜 := 𝒜)).shiftObj (s j)) ⟶
        ⨁ fun i : Fin n ↦ (regular (𝒜 := 𝒜)).shiftObj (d i)),
      ι ≫ π = 𝟙 _ ∧ π ≫ ι = e := by
  obtain ⟨P, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split _ e he
  obtain ⟨n, d, ⟨φ⟩⟩ := exists_iso_biproduct_shift_of_retract 𝒜 s hneg hzero hinj ⟨i, r, hir⟩
  refine ⟨n, d, φ.inv ≫ i, r ≫ φ.hom, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc i, hir, Category.id_comp, φ.inv_hom_id]
  · rw [Category.assoc, ← Category.assoc φ.hom, φ.hom_inv_id, Category.id_comp, hri]

end ConnectedPID

end TauCeti.GradedModuleCat
