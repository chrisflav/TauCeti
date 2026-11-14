/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.StdBasis
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Free
import Mathlib.CategoryTheory.Idempotents.Basic
import TauCeti.Algebra.Module.GradedModule.Nakayama
import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Graded freeness of retracts of finite graded free modules

Let `A` be a `ℤ`-graded `k`-algebra concentrated in nonnegative degrees whose degree-zero piece
consists of `k`-scalars, where `k` is a principal ideal domain acting faithfully on `A`. Every
graded retract of a finite graded free `A`-module `free 𝒜 s` is again isomorphic to a finite
graded free `A`-module `free 𝒜 d`.

The algebra `A` need not be commutative or of low global dimension, and `k` need not be a field:
unlike `TauCeti.Algebra.Category.GradedModuleCat.Idempotent.MinimalResolution`, the degree-zero
subalgebra `𝒜 0 ≅ k` need not be semisimple (for instance, `A` may be a positively weighted
polynomial ring over `ℤ` in arbitrarily many variables), so arbitrary bounded-below graded modules
do not admit projective covers. For a graded retract of `free 𝒜 s`, however, the degree-`p` head
modulo the positive-degree action `A₊` embeds into the finite free `k`-module indexed by the
summands with `s j = p`. Because `k` is a principal ideal domain, that degree-`p` head has a
finite `k`-basis. Lifting those `k`-bases homogeneously gives a graded map from a finite graded
free module `E`:

* bounded-below graded Nakayama makes the map surjective because its image spans the retract modulo
  `A₊`;
* categorical projectivity of the retract splits the surjection homogeneously, making its kernel a
  bounded-below graded retract of `E`;
* linear independence of the chosen `k`-bases forces the kernel into `A₊ E` and hence `A₊ K`, so a
  second application of bounded-below graded Nakayama proves injectivity.

In coordinate form on `(J → A)`, any degree-zero idempotent endomorphism factors through
`(Fin n → A)` via homogeneous `A`-linear inclusion and projection maps, and its image
`LinearMap.range p` admits a finite `A`-basis of homogeneous vectors.

## Main results

* `TauCeti.GradedModuleCat.exists_free_retract_of_idempotent`: any graded idempotent on a finite
  graded free module splits through a `Fin n`-indexed graded free module.
* `TauCeti.GradedModuleCat.exists_fin_free_retract_of_idempotent`: the `ULift`-free specialization
  when the source index type lives in `Type`.
* `TauCeti.GradedModuleCat.exists_iso_fin_free_of_retract`: any graded retract of a finite graded
  free module is graded-isomorphic to `free 𝒜 d` and to a finite biproduct of shifts of `regular`.
* `TauCeti.GradedModuleCat.exists_homogeneous_pi_retract_of_idempotent`: coordinate splitting of a
  degree-zero idempotent on `(J → A)` into homogeneous `A`-linear maps through `(Fin n → A)`.
* `TauCeti.GradedModuleCat.exists_homogeneous_basis_range_idempotent`: the image of a degree-zero
  idempotent on `(J → A)` has a finite `A`-basis with homogeneous coordinates.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projectives and bounded-below graded Nakayama arguments.
* L.-H. Robert and E. Wagner, *A closed formula for the evaluation of sl(N)-foams*, Quantum
  Topol. 11 (2020), no. 3, 411–487 (arXiv:1702.04140v3), Theorem 3.30, for the integral graded
  retract splitting over symmetric polynomials.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v uJ

section RetractPositive

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- Along a graded retraction `i ≫ r = 𝟙 M`, an element of `M` whose image in `P` lies in `A₊ P`
already lies in `A₊ M`. -/
theorem mem_positive_smul_top_of_retract {M P : GradedModuleCat.{v} 𝒜}
    (i : M ⟶ P) (r : P ⟶ M) (hir : i ≫ r = 𝟙 M) {z : M}
    (hz : i.hom z ∈ (⨆ (d : ℤ) (_ : 0 < d), 𝒜 d) • (⊤ : Submodule k P)) :
    z ∈ (⨆ (d : ℤ) (_ : 0 < d), 𝒜 d) • (⊤ : Submodule k M) := by
  have hmap : ∀ y ∈ (⨆ (d : ℤ) (_ : 0 < d), 𝒜 d) • (⊤ : Submodule k P),
      r.hom y ∈ (⨆ (d : ℤ) (_ : 0 < d), 𝒜 d) • (⊤ : Submodule k M) := fun _ hy ↦
    Submodule.smul_induction_on hy
      (fun a ha y _ ↦ by
        rw [r.hom.map_smul]
        exact Submodule.smul_mem_smul ha Submodule.mem_top)
      (fun _ _ hx hy ↦ by
        rw [map_add]
        exact add_mem hx hy)
  have hri : r.hom (i.hom z) = z := by
    simpa using LinearMap.congr_fun (congr_arg Hom.hom hir) z
  exact hri ▸ hmap _ hz

end RetractPositive

section FreeHead

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

section ScalarGradeZero

variable [FaithfulSMul k A] {𝒜}

omit [GradedAlgebra 𝒜] [FaithfulSMul k A] in
private theorem map_u_mem {I : Type*} {d : I → ℤ} {M N : GradedModuleCat.{v} 𝒜}
    (u : ∀ i, M.grading.piece (d i)) (g : M ⟶ N) {p : ℤ} {i : I} (hi : d i = p) :
    g.hom (u i) ∈ N.grading.piece p := by
  rw [← hi]
  exact map_mem g (u i).2

/-- Projection from the degree-`p` piece of `free 𝒜 s` onto the `k`-coordinates of the summands
of shift `p`. -/
private def freeHeadProj (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} (s : J → ℤ) (p : ℤ) :
    (free 𝒜 s).grading.piece p →ₗ[k] ({j : J // s j = p} → k) :=
  LinearMap.pi fun j : {j : J // s j = p} ↦
    (GradedAlgebra.gradeZeroEquiv 𝒜 h₀).symm.toLinearMap ∘ₗ
      ((DirectSum.component k J (fun _ ↦ A) j.1).comp
        ((free 𝒜 s).grading.piece p).subtype).codRestrict (𝒜 0) fun x ↦ by
        rw [LinearMap.comp_apply, Submodule.subtype_apply, ← DirectSum.apply_eq_component]
        have hxj := (mem_free_piece_iff 𝒜 s p x.1).mp x.2 j.1
        rwa [j.2, sub_self] at hxj

private theorem algebraMap_freeHeadProj_apply (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} (s : J → ℤ) (p : ℤ)
    (x : (free 𝒜 s).grading.piece p) (j : {j : J // s j = p}) :
    algebraMap k A (freeHeadProj h₀ s p x j) = x.1 j.1 := by
  simp only [freeHeadProj, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    GradedAlgebra.algebraMap_gradeZeroEquiv_symm, LinearMap.codRestrict_apply,
    Submodule.subtype_apply, ← DirectSum.apply_eq_component]

/-- The kernel of `freeHeadProj` is precisely `A₊ (free 𝒜 s)` intersected with the degree-`p`
piece. -/
private theorem freeHeadProj_eq_zero_iff (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} (s : J → ℤ) (p : ℤ) (x : (free 𝒜 s).grading.piece p) :
    freeHeadProj h₀ s p x = 0 ↔
      (x : free 𝒜 s) ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 s)) := by
  rw [free_mem_positive_smul_top_iff 𝒜 s hneg x.2, funext_iff]
  refine ⟨fun h j hsj ↦ ?_, fun h ⟨j, hsj⟩ ↦ ?_⟩
  · rw [← algebraMap_freeHeadProj_apply h₀ s p x ⟨j, hsj⟩, h ⟨j, hsj⟩, Pi.zero_apply, map_zero]
  · apply FaithfulSMul.algebraMap_injective k A
    rw [algebraMap_freeHeadProj_apply, h j hsj, Pi.zero_apply, map_zero]

/-- On a finite graded free source `free 𝒜 d`, `freeHeadProj` converts `freeLift u ≫ g` in
degree `p` into a `k`-linear combination over the basis indices with `d i = p`. -/
private theorem freeHeadProj_freeLift_comp (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {I : Type uJ} [Finite I] {d : I → ℤ} {J : Type uJ} {s : J → ℤ}
    {M : GradedModuleCat.{max uA uJ} 𝒜} (u : ∀ i, M.grading.piece (d i))
    (g : M ⟶ free 𝒜 s) (p : ℤ) (z : (free 𝒜 d).grading.piece p) :
    freeHeadProj h₀ s p ⟨(freeLift u ≫ g).hom z.1, map_mem (freeLift u ≫ g) z.2⟩ =
      ∑ i ∈ (Fintype.ofFinite {i : I // d i = p}).elems,
        freeHeadProj h₀ d p z i • freeHeadProj h₀ s p ⟨g.hom (u i.1), map_u_mem u g i.2⟩ := by
  classical
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite {i : I // d i = p}
  let _ := (free 𝒜 s).gradedSMul
  have hterm_mem (i : I) : (z.1 i) • g.hom (u i) ∈ (free 𝒜 s).grading.piece p := by
    have hzi : z.1 i ∈ 𝒜 (p - d i) := (mem_free_piece_iff 𝒜 d p z.1).mp z.2 i
    simpa [sub_add_cancel] using
      SetLike.GradedSMul.smul_mem (B := (free 𝒜 s).grading.piece) hzi (map_mem g (u i).2)
  have hmap_sum : (⟨(freeLift u ≫ g).hom z.1, map_mem (freeLift u ≫ g) z.2⟩ :
      (free 𝒜 s).grading.piece p) = ∑ i : I, ⟨(z.1 i) • g.hom (u i), hterm_mem i⟩ :=
    Subtype.ext <| by
      rw [Subtype.coe_mk, Submodule.coe_sum]
      conv_lhs => rw [← DirectSum.sum_univ_of z.1]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [← DirectSum.lof_eq_of A, hom_comp, LinearMap.comp_apply, freeLift_lof, map_smul]
  have helem : (Fintype.ofFinite {i : I // d i = p}).elems = Finset.univ := rfl
  rw [helem, hmap_sum, map_sum]
  have hfilter :
      ∑ i : I, freeHeadProj h₀ s p ⟨(z.1 i) • g.hom (u i), hterm_mem i⟩ =
        ∑ i ∈ Finset.univ.filter (fun i : I ↦ d i = p),
          freeHeadProj h₀ s p ⟨(z.1 i) • g.hom (u i), hterm_mem i⟩ := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi ↦ ?_
    have hzi : z.1 i ∈ 𝒜 (p - d i) := (mem_free_piece_iff 𝒜 d p z.1).mp z.2 i
    rcases lt_or_gt_of_ne (by simpa using hi : d i ≠ p) with hlt | hgt
    · exact (freeHeadProj_eq_zero_iff hneg h₀ s p _).mpr <| Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem (p - d i) (Submodule.mem_iSup_of_mem (by omega) hzi))
        Submodule.mem_top
    · have hz0 : z.1 i = 0 := by rwa [hneg _ (by omega), Submodule.mem_bot] at hzi
      have hsub : (⟨(z.1 i) • g.hom (u i), hterm_mem i⟩ : (free 𝒜 s).grading.piece p) = 0 :=
        Subtype.ext (by simp [hz0])
      rw [hsub, map_zero]
  rw [hfilter, Finset.sum_subtype (p := fun i ↦ d i = p) _ (fun _ ↦ by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsmul : (⟨(z.1 i.1) • g.hom (u i.1), hterm_mem i.1⟩ : (free 𝒜 s).grading.piece p) =
      freeHeadProj h₀ d p z i • ⟨g.hom (u i.1), map_u_mem u g i.2⟩ :=
    Subtype.ext (by rw [Subtype.coe_mk, ← algebraMap_freeHeadProj_apply h₀ d p z i,
      algebraMap_smul, SetLike.val_smul])
  rw [hsmul, map_smul]

/-- If the homogeneous lifts `u` span the degree-`p` head of a bounded-below retract `M` of
`free 𝒜 s` in every degree `p`, then `freeLift u : free 𝒜 d ⟶ M` is surjective. -/
private theorem freeLift_surjective_of_head_span (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {I : Type uJ} {d : I → ℤ} {J : Type uJ} [Finite J] {s : J → ℤ}
    {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s) (rM : free 𝒜 s ⟶ M)
    (hir : iM ≫ rM = 𝟙 M) (u : ∀ i, M.grading.piece (d i))
    (hspan : ∀ (p : ℤ) (x : M.grading.piece p),
      ∃ y ∈ LinearMap.range (freeLift u).hom, ∃ hy : y ∈ M.grading.piece p,
        freeHeadProj h₀ s p ⟨iM.hom y, map_mem iM hy⟩ =
          freeHeadProj h₀ s p ⟨iM.hom x.1, map_mem iM x.2⟩) :
    Function.Surjective (freeLift u).hom := by
  rw [← LinearMap.range_eq_top]
  obtain ⟨b, hb⟩ := exists_free_piece_eq_bot_of_lt 𝒜 s hneg
  have hiM : Function.Injective iM.hom := Function.LeftInverse.injective fun x ↦ by
    simpa using LinearMap.congr_fun (congr_arg Hom.hom hir) x
  have hbelow : ∀ p < b, M.grading.piece p = ⊥ :=
    fun p hp ↦ piece_eq_bot_of_injective iM hiM (hb p hp)
  refine InternalGrading.eq_top_of_piece_le_sup_positive_smul_top 𝒜
    (LinearMap.range (freeLift u).hom) (freeLift u).isHomogeneous.isHomogeneous_range b hbelow
    fun p x hx ↦ ?_
  obtain ⟨y, hyR, hyP, hhead⟩ := hspan p ⟨x, hx⟩
  have hdecomp : x = y + (x - y) := by abel
  rw [hdecomp]
  refine Submodule.add_mem_sup hyR (mem_positive_smul_top_of_retract iM rM hir ?_)
  have hxy : iM.hom (x - y) ∈ (free 𝒜 s).grading.piece p :=
    map_mem iM ((M.grading.piece p).sub_mem hx hyP)
  refine (freeHeadProj_eq_zero_iff hneg h₀ s p ⟨iM.hom (x - y), hxy⟩).mp ?_
  have hsub : (⟨iM.hom (x - y), hxy⟩ : (free 𝒜 s).grading.piece p) =
      ⟨iM.hom x, map_mem iM hx⟩ - ⟨iM.hom y, map_mem iM hyP⟩ :=
    Subtype.ext (map_sub iM.hom x y)
  rw [hsub, map_sub, hhead, sub_self]

/-- If `freeLift u : free 𝒜 d ⟶ M` onto a projective graded module `M` is surjective and the
head images of `u` in each degree `p` are `k`-linearly independent, then `(freeLift u).hom` is
injective. -/
private theorem freeLift_injective_of_head_linearIndependent (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (h₀ : 𝒜 0 ≤ 1) {I : Type uJ} [Finite I] {d : I → ℤ} {J : Type uJ} {s : J → ℤ}
    {M : GradedModuleCat.{max uA uJ} 𝒜} [Projective M] (iM : M ⟶ free 𝒜 s)
    (u : ∀ i, M.grading.piece (d i)) (hsurj : Function.Surjective (freeLift u).hom)
    (hli : ∀ p : ℤ, LinearIndependent k fun i : {i : I // d i = p} ↦
      freeHeadProj h₀ s p ⟨iM.hom (u i.1), map_u_mem u iM i.2⟩) :
    Function.Injective (freeLift u).hom := by
  let φ : free 𝒜 d ⟶ M := freeLift u
  let _ := (kernelObj φ).gradedSMul
  have : Epi φ := (epi_iff_surjective φ).mpr hsurj
  have : IsSplitEpi φ :=
    .mk' ⟨Projective.factorThru (𝟙 M) φ, Projective.factorThru_comp (𝟙 M) φ⟩
  let bicone := binaryBiconeOfIsSplitEpiOfKernel (kernelIsLimit φ)
  obtain ⟨b, hb⟩ := exists_free_piece_eq_bot_of_lt 𝒜 d hneg
  have hK_below : ∀ p < b, (kernelObj φ).grading.piece p = ⊥ :=
    fun p hp ↦ kernelObj_piece_eq_bot_of_piece_eq_bot φ (hb p hp)
  have hK_pos : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (kernelObj φ)) = ⊤ := by
    refine top_unique fun z _ ↦ ?_
    classical
    rw [← DirectSum.sum_support_decompose (kernelObj φ).grading.piece z]
    refine Submodule.sum_mem _ fun p _ ↦ ?_
    set zp := DirectSum.decompose (kernelObj φ).grading.piece z p
    refine mem_positive_smul_top_of_retract bicone.inl bicone.fst bicone.inl_fst ?_
    have hbicone : bicone.inl.hom zp.1 = zp.1.1 := by
      simp [bicone]; rfl
    rw [hbicone]
    have hzpE : zp.1.1 ∈ (free 𝒜 d).grading.piece p :=
      (InternalGrading.mem_ker_piece _ _).mp zp.2
    refine (freeHeadProj_eq_zero_iff hneg h₀ d p ⟨zp.1.1, hzpE⟩).mp ?_
    have hzero_img : (freeLift u ≫ iM).hom zp.1.1 = 0 := by
      rw [hom_comp, LinearMap.comp_apply, LinearMap.mem_ker.mp zp.1.2, map_zero]
    have hsub0 : (⟨(freeLift u ≫ iM).hom zp.1.1, map_mem (freeLift u ≫ iM) hzpE⟩ :
        (free 𝒜 s).grading.piece p) = 0 := Subtype.ext hzero_img
    have hsum0 := (freeHeadProj_freeLift_comp hneg h₀ u iM p ⟨zp.1.1, hzpE⟩).symm.trans
      (by rw [hsub0, map_zero])
    exact funext fun i ↦
      linearIndependent_iff'.mp (hli p) (Fintype.ofFinite _).elems _ hsum0 i
        ((Fintype.ofFinite _).complete i)
  have : Subsingleton (kernelObj φ) :=
    InternalGrading.subsingleton_of_positive_smul_top_eq_top
      (G := (kernelObj φ).grading) 𝒜 b hK_below hK_pos
  exact LinearMap.ker_eq_bot.mp <| (Submodule.eq_bot_iff _).mpr fun x hx ↦
    congr_arg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : kernelObj φ) 0)

end ScalarGradeZero

/-! ### Splitting graded idempotents on finite graded free modules -/

section RetractSplitting

variable [IsDomain k] [IsPrincipalIdealRing k] [FaithfulSMul k A]

omit [CommRing k] [Ring A] [Algebra k A] [GradedAlgebra 𝒜] [IsDomain k]
  [IsPrincipalIdealRing k] [FaithfulSMul k A] in
/-- For a reindexing `eIdx : Fin n ≃ Σ p : S, Fin (r p)` and `d' i = (eIdx i.down).1.1`, the fiber
`{i : ULift (Fin n) // d' i = p}` at `p ∈ S` is equivalent to `Fin (r p)`. -/
private def fiberEquivFin {S : Finset ℤ} {r : ℤ → ℕ} {n : ℕ}
    (eIdx : Fin n ≃ Σ p : S, Fin (r p.1)) {p : ℤ} (hp : p ∈ S) :
    {i : ULift.{uJ} (Fin n) // (eIdx i.down).1.1 = p} ≃ Fin (r p) where
  toFun i := Fin.cast (congr_arg r i.2) (eIdx i.1.down).2
  invFun t := ⟨ULift.up (eIdx.symm ⟨⟨p, hp⟩, t⟩), by simp⟩
  left_inv := fun ⟨⟨i⟩, hi⟩ ↦ Subtype.ext <| congr_arg ULift.up <| eIdx.injective <| by
    rw [Equiv.apply_symm_apply]
    rcases h : eIdx i with ⟨⟨q, hq⟩, t⟩
    have hqp : q = p := by simpa [h] using hi
    subst hqp
    have hhq : hq = hp := Subsingleton.elim _ _
    subst hhq
    ext
    · rfl
    · refine heq_of_eq (Fin.ext ?_)
      rw [Fin.val_cast]
      exact congr_arg (fun z : Σ p : S, Fin (r p.1) ↦ (z.2 : ℕ)) h
  right_inv t := by
    ext
    rw [Fin.val_cast, Equiv.apply_symm_apply]

omit [IsDomain k] [IsPrincipalIdealRing k] in
/-- The `k`-linear map sending a degree-`p` element of `M` to the shift-`p` head coordinates of its
image under `iM : M ⟶ free 𝒜 s`. -/
private def retractHeadProj (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} (s : J → ℤ)
    {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s) (p : ℤ) :
    M.grading.piece p →ₗ[k] ({j : J // s j = p} → k) :=
  (freeHeadProj h₀ s p).comp <|
    ((iM.hom.restrictScalars k).domRestrict (M.grading.piece p)).codRestrict
      ((free 𝒜 s).grading.piece p) fun x ↦ map_mem iM x.2

omit [IsDomain k] [IsPrincipalIdealRing k] in
@[simp]
private theorem retractHeadProj_apply (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} (s : J → ℤ)
    {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s) (p : ℤ)
    (x : M.grading.piece p) :
    retractHeadProj 𝒜 h₀ s iM p x = freeHeadProj h₀ s p ⟨iM.hom x.1, map_mem iM x.2⟩ :=
  rfl

omit [IsDomain k] [IsPrincipalIdealRing k] in
private theorem head_span_of_sigma_basis (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} [Fintype J] (s : J → ℤ)
    {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s)
    (bPid : ∀ p : ℤ,
      Σ r : ℕ, Module.Basis (Fin r) k (LinearMap.range (retractHeadProj 𝒜 h₀ s iM p)))
    {n : ℕ} (eIdx : Fin n ≃ Σ p : Finset.univ.image s, Fin (bPid p.1).1)
    (u₀ : ∀ idx : (Σ p : Finset.univ.image s, Fin (bPid p.1).1), M.grading.piece idx.1.1)
    (hu₀ : ∀ idx, retractHeadProj 𝒜 h₀ s iM idx.1.1 (u₀ idx) = ((bPid idx.1.1).2 idx.2).1)
    (p : ℤ) (x : M.grading.piece p) :
    let u : ∀ i : ULift.{uJ} (Fin n), M.grading.piece (((fun i ↦ (eIdx i).1.1) ∘ ULift.down) i) :=
      fun i ↦ u₀ (eIdx i.down)
    ∃ y ∈ LinearMap.range (freeLift u).hom, ∃ hy : y ∈ M.grading.piece p,
      freeHeadProj h₀ s p ⟨iM.hom y, map_mem iM hy⟩ =
        freeHeadProj h₀ s p ⟨iM.hom x.1, map_mem iM x.2⟩ := by
  classical
  intro u
  by_cases hp : p ∈ Finset.univ.image s
  · let c := (bPid p).2.repr ⟨retractHeadProj 𝒜 h₀ s iM p x, ⟨x, rfl⟩⟩
    let y : M := ∑ t : Fin (bPid p).1, c t • (u₀ ⟨⟨p, hp⟩, t⟩ : M)
    have hyP : y ∈ M.grading.piece p :=
      (M.grading.piece p).sum_mem fun t _ ↦ (M.grading.piece p).smul_mem (c t) (u₀ ⟨⟨p, hp⟩, t⟩).2
    have hyR : y ∈ LinearMap.range (freeLift u).hom := Submodule.sum_mem _ fun t _ ↦ by
      rw [← algebraMap_smul A]
      exact Submodule.smul_mem _ _ ⟨freeGenerator (ULift.up (eIdx.symm ⟨⟨p, hp⟩, t⟩)), by
        rw [freeLift_generator]
        exact congr_arg (fun z ↦ (u₀ z : M)) (eIdx.apply_symm_apply ⟨⟨p, hp⟩, t⟩)⟩
    have hy_sub : (⟨y, hyP⟩ : M.grading.piece p) =
        ∑ t : Fin (bPid p).1, c t • u₀ ⟨⟨p, hp⟩, t⟩ :=
      Subtype.ext (by simp [y])
    have hval :=
      congr_arg Subtype.val ((bPid p).2.sum_repr ⟨retractHeadProj 𝒜 h₀ s iM p x, ⟨x, rfl⟩⟩)
    refine ⟨y, hyR, hyP, ?_⟩
    rw [← retractHeadProj_apply 𝒜 h₀ s iM p ⟨y, hyP⟩, ← retractHeadProj_apply 𝒜 h₀ s iM p x,
      hy_sub, map_sum]
    refine (Finset.sum_congr rfl fun t _ ↦ ?_).trans
      (by simpa only [Submodule.coe_sum, SetLike.val_smul] using hval)
    rw [map_smul, hu₀ ⟨⟨p, hp⟩, t⟩]
  · refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
    ext ⟨j, rfl⟩
    exact False.elim (hp (Finset.mem_image_of_mem s (Finset.mem_univ j)))

omit [IsDomain k] [IsPrincipalIdealRing k] in
private theorem head_linearIndependent_of_sigma_basis (h₀ : 𝒜 0 ≤ 1) {J : Type uJ} [Fintype J]
    (s : J → ℤ) {M : GradedModuleCat.{max uA uJ} 𝒜} (iM : M ⟶ free 𝒜 s)
    (bPid : ∀ p : ℤ,
      Σ r : ℕ, Module.Basis (Fin r) k (LinearMap.range (retractHeadProj 𝒜 h₀ s iM p)))
    {n : ℕ} (eIdx : Fin n ≃ Σ p : Finset.univ.image s, Fin (bPid p.1).1)
    (u₀ : ∀ idx : (Σ p : Finset.univ.image s, Fin (bPid p.1).1), M.grading.piece idx.1.1)
    (hu₀ : ∀ idx, retractHeadProj 𝒜 h₀ s iM idx.1.1 (u₀ idx) = ((bPid idx.1.1).2 idx.2).1)
    (p : ℤ) :
    let d : Fin n → ℤ := fun i ↦ (eIdx i).1.1
    let u : ∀ i : ULift.{uJ} (Fin n), M.grading.piece ((d ∘ ULift.down) i) :=
      fun i ↦ u₀ (eIdx i.down)
    LinearIndependent k fun i : {i : ULift.{uJ} (Fin n) // (d ∘ ULift.down) i = p} ↦
      freeHeadProj h₀ s p ⟨iM.hom (u i.1), map_u_mem u iM i.2⟩ := by
  classical
  intro d u
  by_cases hp : p ∈ Finset.univ.image s
  · let eqv := fiberEquivFin.{uJ} (r := fun q ↦ (bPid q).1) eIdx hp
    have hidx : ∀ (idx : Σ p : Finset.univ.image s, Fin (bPid p.1).1) (h : idx.1.1 = p),
        freeHeadProj h₀ s p ⟨iM.hom (u₀ idx).1,
            map_u_mem (d := fun z : Σ p : Finset.univ.image s, Fin (bPid p.1).1 ↦ z.1.1)
              u₀ iM h⟩ =
          ((bPid p).2 (Fin.cast (congr_arg (fun q ↦ (bPid q).1) h) idx.2)).1 := by
      rintro ⟨⟨q, hq⟩, t⟩ rfl
      exact hu₀ ⟨⟨q, hq⟩, t⟩
    have hcomp : (fun i : {i : ULift.{uJ} (Fin n) // (d ∘ ULift.down) i = p} ↦
        freeHeadProj h₀ s p ⟨iM.hom (u i.1), map_u_mem u iM i.2⟩) =
        (fun t : Fin (bPid p).1 ↦ ((bPid p).2 t : {j : J // s j = p} → k)) ∘ eqv := by
      ext ⟨⟨i⟩, hi⟩
      exact congr_fun (hidx (eIdx i) hi) _
    rw [hcomp]
    exact (((bPid p).2.linearIndependent).map' (Submodule.subtype _)
      (Submodule.ker_subtype _)).comp eqv eqv.injective
  · have : IsEmpty {i : ULift.{uJ} (Fin n) // (d ∘ ULift.down) i = p} :=
      ⟨fun ⟨i, hi⟩ ↦ hp (hi ▸ (eIdx i.down).1.2)⟩
    exact linearIndependent_empty_type

/-- Given a graded retract `M` of a finite graded free module `free 𝒜 s`, lifting degreewise
`k`-bases of its head images produces a bijective graded map `free 𝒜 d' ⟶ M`. -/
private theorem exists_bijective_freeLift_of_retract (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} [Finite J] (s : J → ℤ) {M : GradedModuleCat.{max uA uJ} 𝒜}
    (iM : M ⟶ free 𝒜 s) (rM : free 𝒜 s ⟶ M) (hirM : iM ≫ rM = 𝟙 M) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (φ : free 𝒜 (d ∘ ULift.down) ⟶ M),
      Function.Bijective φ.hom := by
  classical
  have : Projective (free 𝒜 s) := projective_of_module_projective (free 𝒜 s)
  have : Projective M := (Retract.mk iM rM hirM).projective
  cases nonempty_fintype J
  let bPid (p : ℤ) :
      Σ r : ℕ, Module.Basis (Fin r) k (LinearMap.range (retractHeadProj 𝒜 h₀ s iM p)) :=
    Submodule.basisOfPid (Pi.basisFun k {j : J // s j = p})
      (LinearMap.range (retractHeadProj 𝒜 h₀ s iM p))
  let Idx : Type := Σ p : Finset.univ.image s, Fin (bPid p.1).1
  let eIdx : Fin (Fintype.card Idx) ≃ Idx := (Fintype.equivFin Idx).symm
  choose u₀ hu₀ using fun idx : Idx ↦ ((bPid idx.1.1).2 idx.2).2
  let d : Fin (Fintype.card Idx) → ℤ := fun i ↦ (eIdx i).1.1
  let u : ∀ i : ULift.{uJ} (Fin (Fintype.card Idx)), M.grading.piece ((d ∘ ULift.down) i) :=
    fun i ↦ u₀ (eIdx i.down)
  have hsurj : Function.Surjective (freeLift u).hom :=
    freeLift_surjective_of_head_span hneg h₀ iM rM hirM u
      (head_span_of_sigma_basis 𝒜 h₀ s iM bPid eIdx u₀ hu₀)
  have hinj : Function.Injective (freeLift u).hom :=
    freeLift_injective_of_head_linearIndependent hneg h₀ iM u hsurj
      (head_linearIndependent_of_sigma_basis 𝒜 h₀ s iM bPid eIdx u₀ hu₀)
  exact ⟨Fintype.card Idx, d, freeLift u, hinj, hsurj⟩

/-- **Graded retract freeness.** Over a nonnegatively `ℤ`-graded `k`-algebra `A` whose degree-zero
piece consists of scalars from a principal ideal domain `k` acting faithfully on `A`, every graded
idempotent `e` on a finite graded free module `free 𝒜 s` splits through a `Fin n`-indexed graded
free module `free 𝒜 (d ∘ ULift.down)`. -/
theorem exists_free_retract_of_idempotent (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} [Finite J] (s : J → ℤ) (e : free 𝒜 s ⟶ free 𝒜 s) (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : free 𝒜 (d ∘ ULift.down) ⟶ free 𝒜 s)
      (π : free 𝒜 s ⟶ free 𝒜 (d ∘ ULift.down)),
      π ≫ ι = e ∧ ι ≫ π = 𝟙 (free 𝒜 (d ∘ ULift.down)) := by
  obtain ⟨M, iM, rM, hirM, hrMiM⟩ := IsIdempotentComplete.idempotents_split (free 𝒜 s) e he
  obtain ⟨n, d, φ, hφ⟩ := exists_bijective_freeLift_of_retract 𝒜 hneg h₀ s iM rM hirM
  have : IsIso φ := (isIso_iff_bijective φ).mpr hφ
  refine ⟨n, d, (asIso φ).hom ≫ iM, rM ≫ (asIso φ).inv, ?_, ?_⟩
  · simp [Category.assoc, hrMiM]
  · simp [Category.assoc, reassoc_of% hirM]

/-- The `ULift`-free form of `exists_free_retract_of_idempotent` when the source index type `J`
lives in `Type`. -/
theorem exists_fin_free_retract_of_idempotent (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type} [Finite J] (s : J → ℤ) (e : free 𝒜 s ⟶ free 𝒜 s) (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (ι : free 𝒜 d ⟶ free 𝒜 s) (π : free 𝒜 s ⟶ free 𝒜 d),
      π ≫ ι = e ∧ ι ≫ π = 𝟙 (free 𝒜 d) := by
  obtain ⟨n, d, ι, π, hπι, hιπ⟩ := exists_free_retract_of_idempotent 𝒜 hneg h₀ s e he
  let isoU : free 𝒜 (d ∘ ULift.down) ≅ free 𝒜 d := freeCongr 𝒜 Equiv.ulift.{0} d
  refine ⟨n, d, isoU.inv ≫ ι, π ≫ isoU.hom, ?_, ?_⟩
  · rw [Category.assoc, Iso.hom_inv_id_assoc, hπι]
  · rw [Category.assoc, reassoc_of% hιπ, Iso.inv_hom_id]

/-- Any graded retract `W` of a `Type`-indexed finite graded free module `free 𝒜 s` is
isomorphic to `free 𝒜 d` for a `Fin n`-tuple of shifts `d`, and therefore splits into `n` shifted
copies of the regular module with explicit summand inclusions and projections satisfying both
biproduct identities. -/
theorem exists_iso_fin_free_of_retract (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type} [Finite J] (s : J → ℤ) {W : GradedModuleCat.{uA} 𝒜}
    (u : W ⟶ free 𝒜 s) (v : free 𝒜 s ⟶ W) (huv : u ≫ v = 𝟙 W) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : ∀ i : Fin n, (regular (𝒜 := 𝒜)).shiftObj (d i) ⟶ W)
      (π : ∀ i : Fin n, W ⟶ (regular (𝒜 := 𝒜)).shiftObj (d i)),
      Nonempty (W ≅ free 𝒜 d) ∧
      (∀ i, ι i ≫ π i = 𝟙 _) ∧
      (∀ i j, i ≠ j → ι i ≫ π j = 0) ∧
      ∑ i : Fin n, π i ≫ ι i = 𝟙 W := by
  obtain ⟨n, d, φ, hφ⟩ := exists_bijective_freeLift_of_retract 𝒜 hneg h₀ s u v huv
  have : IsIso φ := (isIso_iff_bijective φ).mpr hφ
  let isoFree : W ≅ free 𝒜 d := (asIso φ).symm ≪≫ freeCongr 𝒜 Equiv.ulift.{0} d
  let F : Fin n → GradedModuleCat.{uA} 𝒜 := fun i ↦ (regular (𝒜 := 𝒜)).shiftObj (d i)
  let _ := HasBiproduct.of_hasCoproduct F
  let isoBiprod : W ≅ ⨁ F := isoFree ≪≫ directSumObjIsoBiproduct F
  refine ⟨n, d, fun i ↦ biproduct.ι F i ≫ isoBiprod.inv,
    fun i ↦ isoBiprod.hom ≫ biproduct.π F i, ⟨isoFree⟩, fun i ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · simp [F, Category.assoc, Iso.inv_hom_id_assoc]
  · simp [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_ne _ hij]
  · simp_rw [Category.assoc, ← Category.assoc (biproduct.π F _), ← Preadditive.comp_sum,
      ← Preadditive.sum_comp, biproduct.total, Category.id_comp, Iso.hom_inv_id]

/-! ### Coordinate splittings and homogeneous bases -/

omit [CommRing k] [Algebra k A] [GradedAlgebra 𝒜] [IsDomain k] [IsPrincipalIdealRing k]
  [FaithfulSMul k A] in
private theorem linearEquivFunOnFintype_symm_apply {I : Type*} [Fintype I]
    (v : I → A) (i : I) :
    (DirectSum.linearEquivFunOnFintype A I (fun _ ↦ A)).symm v i = v i := by
  rw [← DirectSum.linearEquivFunOnFintype_apply A, LinearEquiv.apply_symm_apply]

/-- **Homogeneous Pi-module splitting of a degree-zero idempotent.** On a finite product `(J → A)`
equipped with summand shifts `s : J → ℤ`, every degree-zero `A`-linear idempotent `p` factors as
`ι ∘ₗ π = p` with `π ∘ₗ ι = id` through `(Fin n → A)` for homogeneous `A`-linear maps `ι` and `π`
respecting shifts `d : Fin n → ℤ`. -/
theorem exists_homogeneous_pi_retract_of_idempotent (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} [Finite J] (s : J → ℤ) (p : (J → A) →ₗ[A] (J → A)) (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ j, p v j ∈ 𝒜 (q - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → A) →ₗ[A] (J → A)) (π : (J → A) →ₗ[A] (Fin n → A)),
      ι.comp π = p ∧ π.comp ι = LinearMap.id ∧
      (∀ (q : ℤ) (w : Fin n → A), (∀ i, w i ∈ 𝒜 (q - d i)) → ∀ j, ι w j ∈ 𝒜 (q - s j)) ∧
      (∀ (q : ℤ) (v : J → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ i, π v i ∈ 𝒜 (q - d i)) := by
  classical
  cases nonempty_fintype J
  let eqJ : free 𝒜 s ≃ₗ[A] (J → A) := DirectSum.linearEquivFunOnFintype A J (fun _ ↦ A)
  let eHom : free 𝒜 s →ₗ[A] free 𝒜 s := eqJ.symm.toLinearMap ∘ₗ p ∘ₗ eqJ.toLinearMap
  have heHom :
      LinearMap.IsHomogeneous eHom (free 𝒜 s).grading.piece (free 𝒜 s).grading.piece 0 := by
    refine LinearMap.isHomogeneous_def.mpr fun q x hx ↦ ?_
    rw [add_zero]
    refine (mem_free_piece_iff 𝒜 s q _).mpr fun j ↦ ?_
    simp only [eHom, eqJ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      linearEquivFunOnFintype_symm_apply]
    exact hhom q _ (fun j' ↦ by
      rw [DirectSum.linearEquivFunOnFintype_apply]
      exact (mem_free_piece_iff 𝒜 s q x).mp hx j') j
  let e : free 𝒜 s ⟶ free 𝒜 s := ofHom eHom heHom
  have he : e ≫ e = e := by
    refine hom_ext (LinearMap.ext fun x ↦ ?_)
    have hpp := LinearMap.congr_fun hp (eqJ x)
    simpa [e, eHom] using congr_arg eqJ.symm hpp
  obtain ⟨n, d, ι₀, π₀, hπι₀, hιπ₀⟩ := exists_free_retract_of_idempotent 𝒜 hneg h₀ s e he
  let eqFin : free 𝒜 (d ∘ ULift.down) ≃ₗ[A] (Fin n → A) :=
    (DirectSum.linearEquivFunOnFintype A (ULift.{uJ} (Fin n)) (fun _ ↦ A)).trans
      (LinearEquiv.funCongrLeft A A Equiv.ulift.{uJ}.symm)
  let ι : (Fin n → A) →ₗ[A] (J → A) := eqJ.toLinearMap ∘ₗ ι₀.hom ∘ₗ eqFin.symm.toLinearMap
  let π : (J → A) →ₗ[A] (Fin n → A) := eqFin.toLinearMap ∘ₗ π₀.hom ∘ₗ eqJ.symm.toLinearMap
  refine ⟨n, d, ι, π, LinearMap.ext fun v ↦ ?_, LinearMap.ext fun w ↦ ?_,
    fun q w hw j ↦ ?_, fun q v hv i ↦ ?_⟩
  · have h1 := LinearMap.congr_fun (congr_arg Hom.hom hπι₀) (eqJ.symm v)
    simpa [ι, π, e, eHom] using congr_arg eqJ h1
  · have h2 := LinearMap.congr_fun (congr_arg Hom.hom hιπ₀) (eqFin.symm w)
    simpa [ι, π] using congr_arg eqFin h2
  · have hmem : eqFin.symm w ∈ (free 𝒜 (d ∘ ULift.down)).grading.piece q :=
      (mem_free_piece_iff 𝒜 (d ∘ ULift.down) q _).mpr fun ⟨i⟩ ↦ by
        simp only [eqFin, LinearEquiv.symm_trans_apply, LinearEquiv.funCongrLeft_symm,
          LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
          linearEquivFunOnFintype_symm_apply, Function.comp_apply]
        exact hw i
    simpa only [ι, eqJ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      DirectSum.linearEquivFunOnFintype_apply] using
      (mem_free_piece_iff 𝒜 s q _).mp (map_mem ι₀ hmem) j
  · have hmem : eqJ.symm v ∈ (free 𝒜 s).grading.piece q :=
      (mem_free_piece_iff 𝒜 s q _).mpr fun j ↦ by
        simpa only [eqJ, linearEquivFunOnFintype_symm_apply] using hv j
    simpa only [π, eqFin, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.ulift_symm_apply,
      DirectSum.linearEquivFunOnFintype_apply, Function.comp_apply] using
      (mem_free_piece_iff 𝒜 (d ∘ ULift.down) q _).mp (map_mem π₀ hmem) ⟨i⟩

/-- **Homogeneous basis of a graded idempotent image.** Over a nonnegatively `ℤ`-graded `k`-algebra
`A` whose degree-zero piece consists of scalars from a principal ideal domain `k` acting faithfully
on `A`, the image `LinearMap.range p` of any degree-zero `A`-linear idempotent `p` on `(J → A)` has
a finite `A`-basis whose `i`-th vector has `j`-th coordinate in `𝒜 (d i - s j)`. -/
theorem exists_homogeneous_basis_range_idempotent (hneg : ∀ i < 0, 𝒜 i = ⊥) (h₀ : 𝒜 0 ≤ 1)
    {J : Type uJ} [Finite J] (s : J → ℤ) (p : (J → A) →ₗ[A] (J → A)) (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ j, p v j ∈ 𝒜 (q - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A (LinearMap.range p)) (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ 𝒜 (d i - s j) := by
  classical
  obtain ⟨n, d, ι, π, hιπ, hπι, hι_hom, -⟩ :=
    exists_homogeneous_pi_retract_of_idempotent 𝒜 hneg h₀ s p hp hhom
  have hleft : Function.LeftInverse π ι := LinearMap.congr_fun hπι
  let eqRange : (Fin n → A) ≃ₗ[A] LinearMap.range p :=
    (LinearEquiv.ofLeftInverse hleft).trans <|
      LinearEquiv.ofEq _ _ <|
        hιπ ▸ (LinearMap.range_comp_of_range_eq_top ι
          (LinearMap.range_eq_top_of_surjective π hleft.surjective)).symm
  refine ⟨n, (Pi.basisFun A (Fin n)).map eqRange, d, fun i j ↦ ?_⟩
  have hcoe : (((Pi.basisFun A (Fin n)).map eqRange) i : J → A) = ι (Pi.single i 1) := by
    simp [eqRange]
  rw [hcoe]
  refine hι_hom (d i) (Pi.single i 1) (fun i' ↦ ?_) j
  by_cases hi : i' = i
  · subst hi
    simpa using SetLike.one_mem_graded 𝒜
  · simp [Pi.single_eq_of_ne hi]

end RetractSplitting

end FreeHead

end TauCeti.GradedModuleCat
