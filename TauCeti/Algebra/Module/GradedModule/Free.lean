/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.DirectSum
public import TauCeti.Algebra.Module.GradedModule.HomogeneousPart
public import TauCeti.Algebra.Module.GradedModule.Nakayama
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.Algebra.Module.GradedModule.Shift

/-!
# Homogeneous bases of bounded-below projective graded modules

First, degreewise bases on the active homogeneous pieces of an internally graded module assemble
into a basis of the total module (`TauCeti.InternalGrading.basisOfPieceBases`).

Second, let `A` be a nonnegatively `ℤ`-graded `k`-algebra and `P` a bounded-below projective graded
`A`-module. Write `A₊` for the positive-degree part of `A` and `P₊ = A₊ P` for the `A`-submodule
`TauCeti.InternalGrading.positiveSubmodule 𝒜 P hneg`. Any homogeneous family `v : I → P` whose
classes in `P ⧸ P₊` form a basis over the degree-zero subalgebra `𝒜 0` lifts to a homogeneous
`A`-basis of `P` (`TauCeti.InternalGrading.basisOfHead`). Surjectivity of the free extension from
`v` follows from bounded-below graded Nakayama. Projectivity of `P` supplies an ungraded section,
whose degree-zero part is a homogeneous section; the induced projection onto the kernel maps `F₊`
into `K₊`, while `𝒜 0`-linear independence modulo `P₊` places the kernel inside `F₊`, so graded
Nakayama kills the kernel. Neither commutativity of `A` nor finite generation is needed for this
lifting step.

Third, when `A` is connected over a principal ideal domain `k` (`𝒜 0` is the isomorphic image of
`k`), every finitely generated projective graded `A`-module has a finite homogeneous `A`-basis
(`TauCeti.InternalGrading.exists_homogeneous_basis_of_projective`), and hence so does every graded
module that is an `A`-linear retract of `J → A` for finite `J`
(`TauCeti.InternalGrading.exists_homogeneous_basis_of_retract_pi`). In particular, the image of any
degree-zero idempotent endomorphism `p` of `J → A` has a finite homogeneous `A`-basis
(`TauCeti.InternalGrading.exists_homogeneous_basis_range_idempotent`) and splits homogeneously
through a finite shifted product (`TauCeti.InternalGrading.exists_homogeneous_split_idempotent`).

## Main definitions

* `TauCeti.InternalGrading.basisOfPieceBases`: a `k`-basis of an internally graded module assembled
  from bases of its active homogeneous pieces.
* `TauCeti.InternalGrading.basisOfHead`: an `A`-basis of a bounded-below projective graded module
  lifted from a homogeneous basis of `P ⧸ A₊ P` over `𝒜 0`.
* `TauCeti.InternalGrading.piShiftGrading`: the internal grading on a finite product `J → A` with
  summand shifts `s : J → ℤ`, placing `v` in degree `p` when `∀ j, v j ∈ 𝒜 (p - s j)`.

## Main results

* `TauCeti.InternalGrading.coe_basisOfPieceBases`: `basisOfPieceBases` has the given homogeneous
  piece-basis vectors.
* `TauCeti.InternalGrading.coe_basisOfHead`: `basisOfHead` has the given homogeneous vectors.
* `TauCeti.InternalGrading.exists_homogeneous_basis_of_projective` and
  `TauCeti.InternalGrading.exists_homogeneous_basis_of_retract_pi`: over a nonnegatively graded
  algebra connected over a PID, every finitely generated projective graded module (and every graded
  module that is a retract of `J → A` for finite `J`) has a finite homogeneous basis.
* `TauCeti.InternalGrading.exists_homogeneous_basis_range_idempotent`: the image of a degree-zero
  idempotent on a finite shifted product has a finite homogeneous basis.
* `TauCeti.InternalGrading.exists_homogeneous_split_idempotent`: explicit degree-zero inclusion and
  projection maps factoring a degree-zero idempotent through a finite shifted product.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded projective
  modules and graded Nakayama.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Chapter II, §4, for freeness of projective
  graded modules over connected graded rings via reduction modulo `A₊`.

See `TauCeti.Algebra.Module.GradedModule.HomogeneousBasis` for the complementary grid-homology
freeness theorem for finitely generated torsion-free modules over `k[X]` with `k` a field.
-/

public section

noncomputable section

open _root_.DirectSum

namespace TauCeti.InternalGrading

universe uk uA uM uI uJ

section PieceBases

variable {k : Type uk} [Semiring k] {Q : Type uM} [AddCommMonoid Q] [Module k Q]
  {ι : Type*} [DecidableEq ι] (QG : InternalGrading k Q ι) {S : Set ι}

/-- Assemble `k`-bases on the active homogeneous pieces of an internally graded module into a
`k`-basis of the whole module, extending by `Module.Basis.empty` outside `S` and collecting via
`DirectSum.IsInternal.collectedBasis`. -/
def basisOfPieceBases (hvanish : ∀ p, p ∉ S → QG.piece p = ⊥) {I : S → Type uI}
    (bp : ∀ p : S, Module.Basis (I p) k (QG.piece p.1)) :
    Module.Basis (Σ p : S, I p) k Q := by
  classical
  let α : ι → Type uI := fun p ↦ Σ h : PLift (p ∈ S), I ⟨p, h.down⟩
  let bp' : ∀ p : ι, Module.Basis (α p) k (QG.piece p) := fun p ↦
    if hp : p ∈ S then
      (bp ⟨p, hp⟩).reindex
        { toFun := fun j ↦ ⟨⟨hp⟩, j⟩
          invFun := fun x ↦ x.2
          left_inv := fun _ ↦ rfl
          right_inv := fun ⟨⟨_⟩, _⟩ ↦ rfl }
    else by
      have : Subsingleton (QG.piece p) := hvanish p hp ▸ inferInstance
      have : IsEmpty (α p) := ⟨fun ⟨⟨h⟩, _⟩ ↦ hp h⟩
      exact Module.Basis.empty (QG.piece p)
  exact (QG.isInternal.collectedBasis bp').reindex
    { toFun := fun ⟨p, ⟨h⟩, j⟩ ↦ ⟨⟨p, h⟩, j⟩
      invFun := fun ⟨⟨p, h⟩, j⟩ ↦ ⟨p, ⟨h⟩, j⟩
      left_inv := fun ⟨_, ⟨_⟩, _⟩ ↦ rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl }

/-- Evaluating `basisOfPieceBases` at `⟨p, j⟩` returns the `j`-th basis vector of piece `p`. -/
@[simp]
theorem coe_basisOfPieceBases (hvanish : ∀ p, p ∉ S → QG.piece p = ⊥) {I : S → Type uI}
    (bp : ∀ p : S, Module.Basis (I p) k (QG.piece p.1)) :
    ⇑(QG.basisOfPieceBases hvanish bp) = fun idx : (Σ p : S, I p) ↦ (bp idx.1 idx.2 : Q) := by
  ext ⟨⟨p, hp⟩, j⟩
  simp [basisOfPieceBases, hp]

end PieceBases

section HeadBasis

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- The internal grading on a direct sum `⨁ _ : I, A` with generator `i` placed in degree `d i`. -/
private def shiftedFreeGrading {I : Type uI} (d : I → ℤ) :
    InternalGrading k (⨁ _ : I, A) ℤ :=
  InternalGrading.directSum fun i ↦ (InternalGrading.ofDecomposition 𝒜).shift (-d i)

private theorem mem_shiftedFreeGrading_piece_iff {I : Type uI} (d : I → ℤ) (p : ℤ)
    (x : ⨁ _ : I, A) :
    x ∈ (shiftedFreeGrading 𝒜 d).piece p ↔ ∀ i, x i ∈ 𝒜 (p - d i) := by
  simp [shiftedFreeGrading, sub_eq_add_neg]

private instance instGradedSMulShiftedFreeGrading {I : Type uI} (d : I → ℤ) :
    SetLike.GradedSMul 𝒜 (shiftedFreeGrading 𝒜 d).piece where
  smul_mem {_ _} a x ha hx := by
    rw [mem_shiftedFreeGrading_piece_iff] at hx ⊢
    intro i
    have hmul : (a • x) i = a * x i := DFinsupp.smul_apply a x i
    rw [hmul, vadd_eq_add, add_sub_assoc]
    exact SetLike.GradedMonoid.toGradedMul.mul_mem ha (hx i)

private theorem shiftedFreeGrading_piece_eq_bot {I : Type uI} {d : I → ℤ}
    (hneg : ∀ i < 0, 𝒜 i = ⊥) {b : ℤ} (hbd : ∀ i, b ≤ d i) {p : ℤ} (hp : p < b) :
    (shiftedFreeGrading 𝒜 d).piece p = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [mem_shiftedFreeGrading_piece_iff] at hx
  ext i
  have hlt : p - d i < 0 := by
    have := hbd i
    omega
  simpa only [DirectSum.zero_apply, hneg _ hlt, Submodule.mem_bot] using hx i

/-- The `A`-linear extension `(⨁ _ : I, A) →ₗ[A] P` sending generator `i` to `v i`. -/
private def shiftedFreeLift {P : Type uM} [AddCommGroup P] [Module A P] {I : Type uI}
    [DecidableEq I] (v : I → P) : (⨁ _ : I, A) →ₗ[A] P :=
  DirectSum.toModule A I P fun i ↦ LinearMap.toSpanSingleton A P (v i)

private theorem isHomogeneous_shiftedFreeLift {P : Type uM} [AddCommGroup P] [Module k P]
    [Module A P] (G : InternalGrading k P ℤ) [SetLike.GradedSMul 𝒜 G.piece]
    {I : Type uI} [DecidableEq I] {v : I → P} {d : I → ℤ} (hv : ∀ i, v i ∈ G.piece (d i)) :
    TauCeti.LinearMap.IsHomogeneous (shiftedFreeLift v)
      (shiftedFreeGrading 𝒜 d).piece G.piece 0 := by
  refine TauCeti.LinearMap.isHomogeneous_def.mpr fun p y hy ↦ ?_
  refine InternalGrading.toModule_mem_of_mem_directSumPiece _ G.piece _
    (fun i z hz ↦ ?_) (by simpa only [shiftedFreeGrading, directSum_piece] using hy)
  have hz' : z ∈ 𝒜 (p - d i) := by simpa [sub_eq_add_neg] using hz
  rw [LinearMap.toSpanSingleton_apply]
  simpa using SetLike.GradedSMul.smul_mem hz' (hv i)

private theorem shiftedFreeLift_surjective {P : Type uM} [AddCommGroup P] [Module k P]
    [Module A P] [IsScalarTower k A P] (G : InternalGrading k P ℤ) [SetLike.GradedSMul 𝒜 G.piece]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (b : ℤ) (hbelow : ∀ p < b, G.piece p = ⊥)
    {I : Type uI} [DecidableEq I] {v : I → P} {d : I → ℤ} (hv : ∀ i, v i ∈ G.piece (d i))
    (hspan : ⊤ ≤ Submodule.span (SetLike.GradeZero.subalgebra 𝒜)
      (Set.range fun i ↦ (positiveSubmodule 𝒜 P hneg).mkQ (v i))) :
    Function.Surjective (shiftedFreeLift (A := A) v) := by
  rw [← LinearMap.range_eq_top]
  refine G.eq_top_of_piece_le_sup_positive_smul_top 𝒜 (LinearMap.range (shiftedFreeLift v))
    (isHomogeneous_shiftedFreeLift 𝒜 G hv).isHomogeneous_range b hbelow fun p x _ ↦ ?_
  let U := positiveSubmodule 𝒜 P hneg
  obtain ⟨c, hc⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan (Submodule.mem_top (x := U.mkQ x)))
  let y : ⨁ _ : I, A := ∑ i ∈ c.support, DirectSum.lof A I (fun _ ↦ A) i (c i : A)
  have hy : shiftedFreeLift v y = ∑ i ∈ c.support, (c i : A) • v i := by
    simp only [y, map_sum, shiftedFreeLift, DirectSum.toModule_lof,
      LinearMap.toSpanSingleton_apply]
  have hmk : U.mkQ (x - shiftedFreeLift v y) = 0 := by
    rw [map_sub, sub_eq_zero, hy, map_sum, ← hc, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [LinearMap.map_smul, Subalgebra.smul_def]
  have hpos : x - shiftedFreeLift v y ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P) :=
    (mem_positiveSubmodule_iff 𝒜 hneg).mp ((Submodule.Quotient.mk_eq_zero U).mp hmk)
  rw [← add_sub_cancel (shiftedFreeLift v y) x]
  exact Submodule.add_mem_sup ⟨y, rfl⟩ hpos

private theorem ker_shiftedFreeLift_le_positive {P : Type uM} [AddCommGroup P] [Module k P]
    [Module A P] [IsScalarTower k A P] (hneg : ∀ i < 0, 𝒜 i = ⊥) {I : Type uI} [DecidableEq I]
    {v : I → P}
    (hli : LinearIndependent (SetLike.GradeZero.subalgebra 𝒜)
      fun i ↦ (positiveSubmodule 𝒜 P hneg).mkQ (v i))
    {z : ⨁ _ : I, A} (hz : z ∈ LinearMap.ker (shiftedFreeLift (A := A) v)) :
    z ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (⨁ _ : I, A)) := by
  classical
  let g : I → SetLike.GradeZero.subalgebra 𝒜 := fun i ↦
    ⟨(decompose 𝒜 (z i) 0 : A), (decompose 𝒜 (z i) 0).2⟩
  have hsum_z : z = ∑ i ∈ z.support, (z i) • DirectSum.lof A I (fun _ ↦ A) i 1 := by
    conv_lhs => rw [← DFinsupp.sum_single (f := z)]
    rw [DFinsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [DirectSum.single_eq_lof A, ← LinearMap.map_smul, smul_eq_mul, mul_one]
  let z₀ : ⨁ _ : I, A := ∑ i ∈ z.support, (g i : A) • DirectSum.lof A I (fun _ ↦ A) i 1
  have hdiff : z - z₀ ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (⨁ _ : I, A)) := by
    rw [hsum_z, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hsub : z i • DirectSum.lof A I (fun _ ↦ A) i 1 -
        (g i : A) • DirectSum.lof A I (fun _ ↦ A) i 1 =
        (z i - (g i : A)) • DirectSum.lof A I (fun _ ↦ A) i 1 :=
      (sub_smul (z i) (g i : A) _).symm
    rw [hsub]
    exact Submodule.smul_mem_smul (sub_decompose_zero_mem_positive 𝒜 hneg (z i)) Submodule.mem_top
  have hmk : ∑ i ∈ z.support, g i • (positiveSubmodule 𝒜 P hneg).mkQ (v i) = 0 := by
    have hmap := map_mem_positive_smul_top 𝒜 (shiftedFreeLift v) hdiff
    rw [map_sub, LinearMap.mem_ker.mp hz, zero_sub, neg_mem_iff] at hmap
    have hz₀ : shiftedFreeLift v z₀ = ∑ i ∈ z.support, (g i : A) • v i := by
      simp [z₀, shiftedFreeLift, DirectSum.toModule_lof]
    rw [hz₀, ← mem_positiveSubmodule_iff 𝒜 hneg, ← Submodule.Quotient.mk_eq_zero,
      ← Submodule.mkQ_apply, map_sum] at hmap
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans hmap
    rw [Subalgebra.smul_def, LinearMap.map_smul]
  have hg0 : ∀ i ∈ z.support, g i = 0 := linearIndependent_iff'.mp hli z.support g hmk
  have hz₀_eq : z₀ = 0 := Finset.sum_eq_zero fun i hi ↦ by simp [hg0 i hi]
  simpa [hz₀_eq] using hdiff

private theorem shiftedFreeLift_injective {P : Type uM} [AddCommGroup P] [Module k P]
    [Module A P] [IsScalarTower k A P] [Module.Projective A P] (G : InternalGrading k P ℤ)
    [SetLike.GradedSMul 𝒜 G.piece] (hneg : ∀ i < 0, 𝒜 i = ⊥) {b : ℤ} {I : Type uI}
    [DecidableEq I] {v : I → P} {d : I → ℤ} (hv : ∀ i, v i ∈ G.piece (d i))
    (hbd : ∀ i, b ≤ d i) (hsurj : Function.Surjective (shiftedFreeLift (A := A) v))
    (hli : LinearIndependent (SetLike.GradeZero.subalgebra 𝒜)
      fun i ↦ (positiveSubmodule 𝒜 P hneg).mkQ (v i)) :
    Function.Injective (shiftedFreeLift (A := A) v) := by
  let FG := shiftedFreeGrading 𝒜 d
  let φ := shiftedFreeLift (A := A) v
  have hφ : TauCeti.LinearMap.IsHomogeneous φ FG.piece G.piece 0 :=
    isHomogeneous_shiftedFreeLift 𝒜 G hv
  obtain ⟨s₀, hs₀⟩ := Module.projective_lifting_property φ LinearMap.id hsurj
  let σ := G.homogeneousPartOfGradedSMul FG 𝒜 s₀ 0
  have hid_hom : TauCeti.LinearMap.IsHomogeneous (LinearMap.id : P →ₗ[A] P) G.piece G.piece 0 :=
    TauCeti.LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by simpa using hx
  have hφσ : φ ∘ₗ σ = LinearMap.id := by
    calc φ ∘ₗ σ = G.homogeneousPartOfGradedSMul G 𝒜 (φ ∘ₗ s₀) (0 + 0) :=
          G.comp_homogeneousPartOfGradedSMul FG 𝒜 G s₀ 0 hφ
      _ = G.homogeneousPartOfGradedSMul G 𝒜 LinearMap.id 0 := by rw [hs₀, add_zero]
      _ = LinearMap.id := G.homogeneousPartOfGradedSMul_eq_self G 𝒜 LinearMap.id 0 hid_hom
  let K := LinearMap.ker φ
  let KG : InternalGrading k K ℤ := FG.ker hφ
  have : SetLike.GradedSMul 𝒜 KG.piece :=
    ⟨fun {_ _} _ _ ha hx ↦ by
      rw [mem_ker_piece] at hx ⊢
      exact SetLike.GradedSMul.smul_mem (B := FG.piece) ha hx⟩
  let ρ : (⨁ _ : I, A) →ₗ[A] K := (LinearMap.id - σ ∘ₗ φ).codRestrict K fun x ↦ by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
      ← LinearMap.comp_apply, ← LinearMap.comp_assoc, hφσ, LinearMap.id_comp, sub_self]
  have hKtop : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k K) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨z, hz⟩ -
    have hρz : ρ z = ⟨z, hz⟩ := Subtype.ext (by simp [ρ, LinearMap.mem_ker.mp hz])
    exact hρz ▸ map_mem_positive_smul_top 𝒜 ρ (ker_shiftedFreeLift_le_positive 𝒜 hneg hli hz)
  have hKbelow : ∀ p < b, KG.piece p = ⊥ := fun p hp ↦ by
    rw [Submodule.eq_bot_iff]
    intro z hz
    apply Subtype.ext
    have hz' : (z : ⨁ _ : I, A) ∈ (shiftedFreeGrading 𝒜 d).piece p := (FG.mem_ker_piece hφ).mp hz
    rw [shiftedFreeGrading_piece_eq_bot 𝒜 hneg hbd hp, Submodule.mem_bot] at hz'
    exact hz'
  have : Subsingleton K := KG.subsingleton_of_positive_smul_top_eq_top 𝒜 b hKbelow hKtop
  exact LinearMap.ker_eq_bot.mp
    ((Submodule.eq_bot_iff K).mpr fun z hz ↦
      congrArg Subtype.val (Subsingleton.elim (⟨z, hz⟩ : K) 0))

/-- **Homogeneous basis from the graded head.** Let `A` be a nonnegatively graded `k`-algebra and
`P` a bounded-below projective graded `A`-module. Any family `v : I → P` of homogeneous elements
whose images in `P ⧸ A₊ P` form a basis over the degree-zero subalgebra `𝒜 0` is an `A`-basis of
`P`. -/
def basisOfHead {P : Type uM} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [Module.Projective A P] (G : InternalGrading k P ℤ) [SetLike.GradedSMul 𝒜 G.piece]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (b : ℤ) (hbelow : ∀ p < b, G.piece p = ⊥)
    {I : Type uI} {v : I → P} {d : I → ℤ} (hv : ∀ i, v i ∈ G.piece (d i))
    (hli : LinearIndependent (SetLike.GradeZero.subalgebra 𝒜)
      fun i ↦ (positiveSubmodule 𝒜 P hneg).mkQ (v i))
    (hspan : ⊤ ≤ Submodule.span (SetLike.GradeZero.subalgebra 𝒜)
      (Set.range fun i ↦ (positiveSubmodule 𝒜 P hneg).mkQ (v i))) :
    Module.Basis I A P := by
  classical
  by_cases hA : Subsingleton A
  · have : Subsingleton P := Module.subsingleton A P
    have : Subsingleton (I →₀ A) := Module.subsingleton A (I →₀ A)
    exact Module.Basis.ofRepr 0
  · rw [not_subsingleton_iff_nontrivial] at hA
    have : Nontrivial (SetLike.GradeZero.subalgebra 𝒜) :=
      ⟨⟨0, 1, fun h ↦ one_ne_zero (congrArg Subtype.val h).symm⟩⟩
    have hbd : ∀ i, b ≤ d i := fun i ↦ by
      by_contra! hlt
      have hvi0 : v i = 0 := by
        simpa only [hbelow (d i) hlt, Submodule.mem_bot] using hv i
      exact hli.ne_zero i (by simp [hvi0])
    have hsurj := shiftedFreeLift_surjective 𝒜 G hneg b hbelow hv hspan
    have hinj := shiftedFreeLift_injective 𝒜 G hneg hv hbd hsurj hli
    let e : (⨁ _ : I, A) ≃ₗ[A] P := LinearEquiv.ofBijective (shiftedFreeLift v) ⟨hinj, hsurj⟩
    exact Module.Basis.ofRepr (e.symm.trans (finsuppLequivDFinsupp A).symm)

/-- The basis constructed by `basisOfHead` has the prescribed homogeneous vectors `v`. -/
@[simp]
theorem coe_basisOfHead {P : Type uM} [AddCommGroup P] [Module k P] [Module A P]
    [IsScalarTower k A P] [Module.Projective A P] (G : InternalGrading k P ℤ)
    [SetLike.GradedSMul 𝒜 G.piece] (hneg : ∀ i < 0, 𝒜 i = ⊥) (b : ℤ)
    (hbelow : ∀ p < b, G.piece p = ⊥) {I : Type uI} {v : I → P} {d : I → ℤ}
    (hv : ∀ i, v i ∈ G.piece (d i))
    (hli : LinearIndependent (SetLike.GradeZero.subalgebra 𝒜)
      fun i ↦ (positiveSubmodule 𝒜 P hneg).mkQ (v i))
    (hspan : ⊤ ≤ Submodule.span (SetLike.GradeZero.subalgebra 𝒜)
      (Set.range fun i ↦ (positiveSubmodule 𝒜 P hneg).mkQ (v i))) :
    ⇑(G.basisOfHead 𝒜 hneg b hbelow hv hli hspan) = v := by
  classical
  ext i
  rw [basisOfHead]
  split_ifs with hA
  · have : Subsingleton P := Module.subsingleton A P
    exact Subsingleton.elim _ _
  · simp only [Module.Basis.coe_ofRepr, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply, shiftedFreeLift]
    have hsingle : (finsuppLequivDFinsupp A) (Finsupp.single i (1 : A)) =
        DirectSum.lof A I (fun _ ↦ A) i 1 := by
      ext j
      simp [DirectSum.lof_eq_of, DirectSum.of_apply]
    rw [hsingle, DirectSum.toModule_lof, LinearMap.toSpanSingleton_apply, one_smul]

end HeadBasis

section PiShift

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

private theorem isInternal_piShiftPiece {J : Type uJ} [Finite J] (s : J → ℤ) :
    DirectSum.IsInternal (fun p : ℤ ↦ Submodule.pi Set.univ fun j : J ↦ 𝒜 (p - s j)) := by
  cases nonempty_fintype J
  classical
  let FG : InternalGrading k (⨁ _ : J, A) ℤ :=
    InternalGrading.directSum fun j ↦ (InternalGrading.ofDecomposition 𝒜).shift (-s j)
  let e := DirectSum.linearEquivFunOnFintype k J fun _ ↦ A
  have hmap : ∀ p, ((FG.map e).piece p : Submodule k (J → A)) =
      Submodule.pi Set.univ fun j ↦ 𝒜 (p - s j) := fun p ↦ by
    ext x
    simp only [map_piece, Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, forall_true_left]
    refine ⟨fun ⟨y, hy, hyx⟩ j ↦ ?_, fun hx ↦ ⟨e.symm x, ?_, e.apply_symm_apply x⟩⟩
    · rw [← hyx]
      have hy' : ∀ j, y j ∈ 𝒜 (p - s j) := by
        simpa [FG, sub_eq_add_neg] using hy
      exact hy' j
    · simp only [FG, directSum_piece, mem_directSumPiece_iff, shift_piece, ofDecomposition_piece]
      intro j
      have hxj : (e.symm x) j = x j := congrFun (e.apply_symm_apply x) j
      simpa [hxj, sub_eq_add_neg] using hx j
  convert (FG.map e).isInternal using 1
  ext p x
  exact (SetLike.ext_iff.mp (hmap p) x).symm

/-- The internal grading on a finite product `J → A` with shifts `s : J → ℤ`, placing `x` in
degree `p` when `x j ∈ 𝒜 (p - s j)` for every `j`. -/
def piShiftGrading {J : Type uJ} [Finite J] (s : J → ℤ) :
    InternalGrading k (J → A) ℤ where
  piece p := Submodule.pi Set.univ fun j ↦ 𝒜 (p - s j)
  isInternal := isInternal_piShiftPiece 𝒜 s

/-- Membership in the degree-`p` piece of `piShiftGrading` is checked coordinatewise. -/
@[simp]
theorem mem_piShiftGrading_piece_iff {J : Type uJ} [Finite J] (s : J → ℤ) (p : ℤ) (x : J → A) :
    x ∈ (piShiftGrading 𝒜 s).piece p ↔ ∀ j, x j ∈ 𝒜 (p - s j) := by
  simp [piShiftGrading]

/-- Scalar multiplication on `J → A` respects `piShiftGrading`. -/
instance instGradedSMulPiShiftGrading {J : Type uJ} [Finite J] (s : J → ℤ) :
    SetLike.GradedSMul 𝒜 (piShiftGrading 𝒜 s).piece where
  smul_mem {_ _} _ _ ha hx := by
    rw [mem_piShiftGrading_piece_iff] at hx ⊢
    intro j
    rw [Pi.smul_apply, smul_eq_mul, vadd_eq_add, add_sub_assoc]
    exact SetLike.GradedMonoid.toGradedMul.mul_mem ha (hx j)

/-- A finite shifted product over a nonnegatively graded algebra is bounded below. -/
theorem exists_piece_piShiftGrading_eq_bot {J : Type uJ} [Finite J] (s : J → ℤ)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) :
    ∃ b : ℤ, ∀ p < b, (piShiftGrading 𝒜 s).piece p = ⊥ := by
  cases nonempty_fintype J
  by_cases hJ : Nonempty J
  · refine ⟨(Finset.univ.image s).min' (Finset.image_nonempty.mpr Finset.univ_nonempty),
      fun p hp ↦ ?_⟩
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [mem_piShiftGrading_piece_iff] at hx
    ext j
    have hle : (Finset.univ.image s).min' _ ≤ s j :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem s (Finset.mem_univ j))
    simpa only [Pi.zero_apply, hneg (p - s j) (by omega), Submodule.mem_bot] using hx j
  · rw [not_nonempty_iff] at hJ
    exact ⟨0, fun _ _ ↦ (Submodule.eq_bot_iff _).mpr fun x _ ↦ Subsingleton.elim x 0⟩

end PiShift

section ConnectedPID

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- In `(J → A) ⧸ A₊(J → A)` for finite `J`, the classes of the standard unit vectors span over `k`
when `𝒜 0` lies in the image of `k`. -/
private theorem top_le_span_piQuotient {J : Type uJ} [Finite J] [DecidableEq J]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A)) :
    let U := positiveSubmodule 𝒜 (J → A) hneg
    ⊤ ≤ Submodule.span k (Set.range fun j : J ↦ U.mkQ (Pi.single j 1)) := by
  cases nonempty_fintype J
  intro U y _
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective U y
  have hxsum : x = ∑ j : J, Pi.single j (x j) := by
    ext j
    simp
  rw [← Submodule.mkQ_apply, hxsum, map_sum]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  obtain ⟨r, hr⟩ := hzero (decompose 𝒜 (x j) 0).2
  have hdecomp : Pi.single j (x j) =
      r • (Pi.single j (1 : A) : J → A) +
        (x j - (decompose 𝒜 (x j) 0 : A)) • (Pi.single j (1 : A) : J → A) := by
    ext j'
    by_cases hjj : j' = j
    · subst hjj
      simp [← hr, Algebra.algebraMap_eq_smul_one]
    · simp [Pi.single_eq_of_ne hjj]
  have hpos : U.mkQ ((x j - (decompose 𝒜 (x j) 0 : A)) • (Pi.single j (1 : A) : J → A)) = 0 :=
    (Submodule.Quotient.mk_eq_zero U).mpr <| (mem_positiveSubmodule_iff 𝒜 hneg).mpr <|
      Submodule.smul_mem_smul (sub_decompose_zero_mem_positive 𝒜 hneg (x j)) Submodule.mem_top
  rw [hdecomp, map_add, LinearMap.map_smul_of_tower, hpos, add_zero]
  exact Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl⟩)

/-- In `(J → A) ⧸ A₊(J → A)`, the classes of the standard unit vectors are `k`-linearly
independent when `algebraMap k A` is injective. -/
private theorem linearIndependent_piQuotient {J : Type uJ} [DecidableEq J]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hinj : Function.Injective (algebraMap k A)) :
    LinearIndependent k
      (fun j : J ↦ (positiveSubmodule 𝒜 (J → A) hneg).mkQ (Pi.single j 1)) := by
  classical
  let U := positiveSubmodule 𝒜 (J → A) hneg
  rw [linearIndependent_iff']
  intro t c hsum j₀ hj₀
  have hval : U.mkQ (∑ j ∈ t, c j • (Pi.single j (1 : A) : J → A)) = 0 := by
    rw [map_sum]
    refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans hsum
    exact LinearMap.map_smul_of_tower U.mkQ (c j) _
  have hmem : (∑ j ∈ t, c j • (Pi.single j (1 : A) : J → A)) ∈ U := by
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hval
  have hproj := map_mem_positive_smul_top 𝒜 (LinearMap.proj j₀ : (J → A) →ₗ[A] A)
    ((mem_positiveSubmodule_iff 𝒜 hneg).mp hmem)
  have heval : (LinearMap.proj j₀ : (J → A) →ₗ[A] A)
      (∑ j ∈ t, c j • (Pi.single j (1 : A) : J → A)) = algebraMap k A (c j₀) := by
    rw [LinearMap.proj_apply, Finset.sum_apply, Finset.sum_eq_single j₀]
    · simp [Algebra.algebraMap_eq_smul_one]
    · intro j _ hne
      simp [Pi.single_eq_of_ne (Ne.symm hne)]
    · intro habs
      exact False.elim (habs hj₀)
  rw [heval] at hproj
  have hc0 : (decompose 𝒜 (algebraMap k A (c j₀)) 0 : A) = 0 :=
    decompose_zero_eq_zero_of_mem_positive 𝒜 hneg hproj
  have hmem0 : algebraMap k A (c j₀) ∈ 𝒜 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (𝒜 0).smul_mem _ SetLike.GradedMonoid.toGradedOne.one_mem
  rw [decompose_of_mem_same 𝒜 hmem0] at hc0
  exact hinj (hc0.trans (map_zero (algebraMap k A)).symm)

/-- Any `A`-linear map descends to `A₊`-quotients over a nonnegatively graded algebra. -/
private def mapQPositive {M : Type uM} {N : Type*} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (f : M →ₗ[A] N) :
    (M ⧸ positiveSubmodule 𝒜 M hneg) →ₗ[A] (N ⧸ positiveSubmodule 𝒜 N hneg) :=
  Submodule.mapQ _ _ f fun _ hx ↦ Submodule.mem_comap.mpr
    ((mem_positiveSubmodule_iff 𝒜 hneg).mpr
      (map_mem_positive_smul_top 𝒜 f ((mem_positiveSubmodule_iff 𝒜 hneg).mp hx)))

private theorem mapQPositive_injective_of_comp_eq_id {M : Type uM} {N : Type*} [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] [AddCommGroup N] [Module k N] [Module A N]
    [IsScalarTower k A N] (hneg : ∀ i < 0, 𝒜 i = ⊥) {ι₀ : M →ₗ[A] N} {π₀ : N →ₗ[A] M}
    (hsplit : π₀ ∘ₗ ι₀ = LinearMap.id) :
    Function.Injective (mapQPositive 𝒜 hneg ι₀) :=
  Function.LeftInverse.injective (g := mapQPositive 𝒜 hneg π₀) fun q ↦ by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [mapQPositive, mapQPositive, Submodule.mapQ_apply, Submodule.mapQ_apply]
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun hsplit x)

variable [IsDomain k] [IsPrincipalIdealRing k]

/-- The graded head `P ⧸ A₊ P` of a finitely generated projective graded `A`-module has a finite
`k`-basis of homogeneous vectors. -/
private theorem exists_head_basis_of_projective
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    {P : Type uM} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [Module.Finite A P] [Module.Projective A P]
    (G : InternalGrading k P ℤ) [SetLike.GradedSMul 𝒜 G.piece] :
    ∃ (n : ℕ) (bQ : Module.Basis (Fin n) k (P ⧸ positiveSubmodule 𝒜 P hneg)) (d : Fin n → ℤ),
      ∀ i, bQ i ∈
        (G.quotient (positiveSubmodule 𝒜 P hneg) (G.isHomogeneous_positiveSubmodule 𝒜 hneg)).piece
          (d i) := by
  classical
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := P)
  let π₀ : (Fin m → A) →ₗ[A] P := Fintype.linearCombination A g
  have hπ₀ : Function.Surjective π₀ :=
    LinearMap.range_eq_top.mp ((Fintype.range_linearCombination A g).trans hg)
  obtain ⟨ι₀, hsplit⟩ := Module.projective_lifting_property π₀ LinearMap.id hπ₀
  let UP := positiveSubmodule 𝒜 P hneg
  let UF := positiveSubmodule 𝒜 (Fin m → A) hneg
  let QP_G := G.quotient UP (G.isHomogeneous_positiveSubmodule 𝒜 hneg)
  let bF : Module.Basis (Fin m) k ((Fin m → A) ⧸ UF) :=
    Module.Basis.mk (linearIndependent_piQuotient 𝒜 hneg hinj)
      (top_le_span_piQuotient 𝒜 hneg hzero)
  let ιbar : (P ⧸ UP) →ₗ[k] ((Fin m → A) ⧸ UF) := (mapQPositive 𝒜 hneg ι₀).restrictScalars k
  have hbar_inj : Function.Injective ιbar := mapQPositive_injective_of_comp_eq_id 𝒜 hneg hsplit
  obtain ⟨_, bTot⟩ := Submodule.basisOfPid bF (LinearMap.range ιbar)
  have : Module.Finite k (P ⧸ UP) :=
    Module.Finite.equiv
      (bTot.map (LinearEquiv.ofInjective ιbar hbar_inj).symm).equivFun.symm
  let S : Set ℤ := {p | QP_G.piece p ≠ ⊥}
  have : Fintype S := QP_G.finite_piece_ne_bot.fintype
  have hvanish : ∀ p, p ∉ S → QP_G.piece p = ⊥ := fun _ hp ↦ Classical.not_not.mp hp
  let bpiece (p : S) : Σ n : ℕ, Module.Basis (Fin n) k (QP_G.piece p.1) := by
    let ιp : QP_G.piece p.1 →ₗ[k] ((Fin m → A) ⧸ UF) := ιbar.comp (QP_G.piece p.1).subtype
    have hιp_inj : Function.Injective ιp := hbar_inj.comp Subtype.val_injective
    obtain ⟨np, bR⟩ := Submodule.basisOfPid bF (LinearMap.range ιp)
    exact ⟨np, bR.map (LinearEquiv.ofInjective ιp hιp_inj).symm⟩
  let bQ := QP_G.basisOfPieceBases hvanish fun p ↦ (bpiece p).2
  let eFin := (Fintype.equivFin (Σ p : S, Fin (bpiece p).1)).symm
  refine ⟨_, bQ.reindex eFin.symm, fun i ↦ (eFin i).1.1, fun i ↦ ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm_apply]
  dsimp only [bQ]
  rw [coe_basisOfPieceBases]
  exact ((bpiece (eFin i).1).2 (eFin i).2).2

/-- **Graded freeness of finitely generated projective modules over a connected graded algebra over
a PID.** Let `A` be a nonnegatively `ℤ`-graded `k`-algebra over a principal ideal domain `k` whose
degree-zero piece is the isomorphic image of `k`. Every finitely generated projective graded
`A`-module `P` has a finite homogeneous `A`-basis. -/
theorem exists_homogeneous_basis_of_projective
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    {P : Type uM} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [Module.Finite A P] [Module.Projective A P]
    (G : InternalGrading k P ℤ) [SetLike.GradedSMul 𝒜 G.piece] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A P) (d : Fin n → ℤ),
      ∀ i, b i ∈ G.piece (d i) := by
  classical
  obtain ⟨b_low, hP_low⟩ := G.exists_piece_eq_bot_of_finite 𝒜 hneg
  let UP := positiveSubmodule 𝒜 P hneg
  obtain ⟨n, bQ, d, hbQ⟩ := exists_head_basis_of_projective 𝒜 hneg hzero hinj G
  choose v hv_mem hv_mk using fun i ↦ (G.mem_quotient_piece_iff UP _).mp (hbQ i)
  have hmk_eq : (fun i ↦ UP.mkQ (v i)) = ⇑bQ := funext hv_mk
  have hsurj_k : Function.Surjective (algebraMap k (SetLike.GradeZero.subalgebra 𝒜)) :=
    fun a ↦ by
      obtain ⟨r, hr⟩ := hzero a.2
      exact ⟨r, Subtype.ext hr⟩
  have hliA₀ : LinearIndependent (SetLike.GradeZero.subalgebra 𝒜) fun i ↦ UP.mkQ (v i) :=
    hmk_eq ▸ bQ.linearIndependent.map_of_surjective_injectiveₛ
      (algebraMap k (SetLike.GradeZero.subalgebra 𝒜)) (AddMonoidHom.id (P ⧸ UP))
      hsurj_k Function.injective_id fun r m ↦ (algebraMap_smul _ r m).symm
  have hspanA₀ : ⊤ ≤ Submodule.span (SetLike.GradeZero.subalgebra 𝒜)
      (Set.range fun i ↦ UP.mkQ (v i)) :=
    hmk_eq ▸ (Submodule.span_eq_top_of_span_eq_top k (SetLike.GradeZero.subalgebra 𝒜) _
      bQ.span_eq).ge
  exact ⟨n, G.basisOfHead 𝒜 hneg b_low hP_low hv_mem hliA₀ hspanA₀, d, fun i ↦ by
    simpa using hv_mem i⟩

/-- **Graded freeness of retracts over a connected graded algebra over a PID.** Let `A` be a
nonnegatively `ℤ`-graded `k`-algebra over a principal ideal domain `k` whose degree-zero piece is
the isomorphic image of `k`. Every graded module `P` that is an `A`-linear retract of `J → A` for a
finite index type `J` (`π₀ ∘ₗ ι₀ = id`) has a finite homogeneous `A`-basis. -/
theorem exists_homogeneous_basis_of_retract_pi {J : Type uJ} [Finite J]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    {P : Type uM} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    (G : InternalGrading k P ℤ) [SetLike.GradedSMul 𝒜 G.piece]
    (ι₀ : P →ₗ[A] (J → A)) (π₀ : (J → A) →ₗ[A] P) (hsplit : π₀ ∘ₗ ι₀ = LinearMap.id) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A P) (d : Fin n → ℤ),
      ∀ i, b i ∈ G.piece (d i) := by
  cases nonempty_fintype J
  have : Module.Finite A P :=
    Module.Finite.of_surjective π₀ (Function.LeftInverse.surjective (LinearMap.congr_fun hsplit))
  have : Module.Projective A (J → A) := Module.Projective.of_basis (Pi.basisFun A J)
  have : Module.Projective A P := Module.Projective.of_split ι₀ π₀ hsplit
  exact G.exists_homogeneous_basis_of_projective 𝒜 hneg hzero hinj

/-- **Homogeneous basis for the image of a degree-zero idempotent.** Over a nonnegatively graded
`k`-algebra `A` connected over a principal ideal domain `k`, the image of any degree-zero
idempotent endomorphism `p` of a finite shifted product `J → A` (with shifts `s : J → ℤ`) admits a
finite `A`-basis `b : Module.Basis (Fin n) A (LinearMap.range p)` of homogeneous vectors of degrees
`d : Fin n → ℤ`, meaning `(b i).val j ∈ 𝒜 (d i - s j)` for all `i` and `j`. -/
theorem exists_homogeneous_basis_range_idempotent {J : Type uJ} [Finite J] (s : J → ℤ)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    (p : (J → A) →ₗ[A] (J → A)) (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ j, p v j ∈ 𝒜 (q - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A (LinearMap.range p)) (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ 𝒜 (d i - s j) := by
  let FG := piShiftGrading 𝒜 s
  have hp_hom : TauCeti.LinearMap.IsHomogeneous p FG.piece FG.piece 0 :=
    TauCeti.LinearMap.isHomogeneous_def.mpr fun q v hv ↦ by
      rw [add_zero]
      rw [mem_piShiftGrading_piece_iff] at hv ⊢
      exact hhom q v hv
  let RG := FG.submodule (LinearMap.range p) hp_hom.isHomogeneous_range
  have : SetLike.GradedSMul 𝒜 RG.piece :=
    ⟨fun {_ _} _ _ ha hx ↦ by
      rw [mem_submodule_piece] at hx ⊢
      exact SetLike.GradedSMul.smul_mem (B := FG.piece) ha hx⟩
  have hsplit : p.rangeRestrict ∘ₗ (LinearMap.range p).subtype = LinearMap.id :=
    LinearMap.ext fun ⟨_, y, rfl⟩ ↦ Subtype.ext (LinearMap.congr_fun hp y)
  obtain ⟨n, b, d, hb⟩ := RG.exists_homogeneous_basis_of_retract_pi 𝒜 hneg hzero hinj
    (LinearMap.range p).subtype p.rangeRestrict hsplit
  refine ⟨n, b, d, fun i j ↦ ?_⟩
  exact (mem_piShiftGrading_piece_iff 𝒜 s (d i) (b i).val).mp
    ((FG.mem_submodule_piece _ _).mp (hb i)) j

/-- **Explicit homogeneous splitting of a degree-zero idempotent.** Under the hypotheses of
`exists_homogeneous_basis_range_idempotent`, `p` factors as `ι ∘ₗ π = p` with `π ∘ₗ ι = id`
through a finite shifted product `Fin n → A` of degrees `d : Fin n → ℤ`, where both `ι` and `π`
preserve degrees. -/
theorem exists_homogeneous_split_idempotent {J : Type uJ} [Finite J] (s : J → ℤ)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : 𝒜 0 ≤ LinearMap.range (Algebra.linearMap k A))
    (hinj : Function.Injective (algebraMap k A))
    (p : (J → A) →ₗ[A] (J → A)) (hp : p.comp p = p)
    (hhom : ∀ (q : ℤ) (v : J → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ j, p v j ∈ 𝒜 (q - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (ι : (Fin n → A) →ₗ[A] (J → A))
      (π : (J → A) →ₗ[A] (Fin n → A)),
      π.comp ι = LinearMap.id ∧ ι.comp π = p ∧
      (∀ (q : ℤ) (u : Fin n → A), (∀ i, u i ∈ 𝒜 (q - d i)) → ∀ j, ι u j ∈ 𝒜 (q - s j)) ∧
      (∀ (q : ℤ) (v : J → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ i, π v i ∈ 𝒜 (q - d i)) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent 𝒜 s hneg hzero hinj p hp hhom
  let e : (Fin n → A) ≃ₗ[A] LinearMap.range p := b.equivFun.symm
  let ι : (Fin n → A) →ₗ[A] (J → A) := (LinearMap.range p).subtype.comp e.toLinearMap
  let π : (J → A) →ₗ[A] (Fin n → A) := e.symm.toLinearMap.comp p.rangeRestrict
  have hp_hom : TauCeti.LinearMap.IsHomogeneous p (piShiftGrading 𝒜 s).piece
      (piShiftGrading 𝒜 s).piece 0 :=
    TauCeti.LinearMap.isHomogeneous_def.mpr fun q v hv ↦ by
      rw [add_zero]
      rw [mem_piShiftGrading_piece_iff] at hv ⊢
      exact hhom q v hv
  let RG := (piShiftGrading 𝒜 s).submodule (LinearMap.range p) hp_hom.isHomogeneous_range
  have he_hom : TauCeti.LinearMap.IsHomogeneous e.toLinearMap
      (piShiftGrading 𝒜 d).piece RG.piece 0 := by
    refine TauCeti.LinearMap.isHomogeneous_def.mpr fun q u hu ↦ ?_
    rw [add_zero]
    rw [mem_piShiftGrading_piece_iff] at hu
    rw [mem_submodule_piece, mem_piShiftGrading_piece_iff]
    intro j
    rw [LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Finset.sum_apply]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    have hdeg : (q - d i) + (d i - s j) = q - s j := by omega
    exact hdeg ▸ SetLike.GradedMonoid.toGradedMul.mul_mem (hu i) (hb i j)
  have he_symm_hom := TauCeti.LinearMap.IsHomogeneous.linearEquiv_symm he_hom
  refine ⟨n, d, ι, π, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun u ↦ ?_
    have hp_fix : p.rangeRestrict (ι u) = e u := by
      apply Subtype.ext
      obtain ⟨y, hy⟩ := (e u).2
      rw [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearEquiv.coe_coe, ← hy]
      exact LinearMap.congr_fun hp y
    simp [π, hp_fix]
  · refine LinearMap.ext fun v ↦ ?_
    simp [ι, π]
  · intro q u hu j
    have hmem : e u ∈ RG.piece q := by
      simpa using he_hom.map_mem ((mem_piShiftGrading_piece_iff 𝒜 d q u).mpr hu)
    exact (mem_piShiftGrading_piece_iff 𝒜 s q (ι u)).mp
      (((piShiftGrading 𝒜 s).mem_submodule_piece _ _).mp hmem) j
  · intro q v hv i
    have hrv : p.rangeRestrict v ∈ RG.piece q := by
      rw [← add_zero q]
      exact ((piShiftGrading 𝒜 s).isHomogeneous_rangeRestrict hp_hom).map_mem
        ((mem_piShiftGrading_piece_iff 𝒜 s q v).mpr hv)
    have hmem : e.symm (p.rangeRestrict v) ∈ (piShiftGrading 𝒜 d).piece q := by
      simpa using he_symm_hom.map_mem hrv
    exact (mem_piShiftGrading_piece_iff 𝒜 d q (π v)).mp hmem i

end ConnectedPID

end TauCeti.InternalGrading
