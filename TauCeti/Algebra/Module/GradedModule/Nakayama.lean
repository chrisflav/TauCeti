/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Generated

/-!
# Graded Nakayama and detection of generating degrees

For a bounded-below internally graded module, the positive-degree part of the algebra cannot
surject onto the whole module unless the module is zero. More generally, homogeneous generators
modulo the positive-degree action generate the module itself. In particular, over a nonnegatively
graded algebra, a bounded-below module is generated in degree `d` exactly when every homogeneous
piece outside degree `d` lies in `A₊ M`.

The last criterion expresses concentration of `M / A₊ M` in degree `d` without choosing a
presentation of that quotient. It detects the generating degrees of terms of minimal graded
projective resolutions: maps to modules annihilated by `A₊` see precisely this quotient.
Neither projectivity nor semisimplicity is needed for the generation criterion. Boundedness below
is essential; no finite-generation hypothesis is required when a lower bound is supplied.

The positive-degree action `A₊ M` is itself a homogeneous submodule, stable under degree-zero
scalars: its degree-`p` components are sums of products `a • y` with `a` of positive degree `i`
and `y` of degree `p - i`. Over a nonnegatively graded ring, `A₊ M` is stable under all of `A`
(`TauCeti.InternalGrading.positiveSubmodule`).

## Main definitions

* `TauCeti.InternalGrading.positiveSubmodule`: the positive-degree action `A₊ N` on a module `N`
  over a nonnegatively graded algebra `A`, bundled as an `A`-submodule.

## Main results

* `TauCeti.InternalGrading.eq_top_of_piece_le_sup_positive_smul_top`: homogeneous generation modulo
  `A₊` implies generation of a bounded-below graded module.
* `TauCeti.InternalGrading.subsingleton_of_positive_smul_top_eq_top`: a bounded-below graded module
  with `A₊ M = M` is zero.
* `TauCeti.InternalGrading.isGeneratedInDegree_iff_piece_le_positive_smul_top`: characterization of
  generation in degree `d` via containment of all other pieces in `A₊ M`.
* `TauCeti.InternalGrading.exists_piece_eq_bot_of_finite` and
  `TauCeti.InternalGrading.bddBelow_setOf_piece_ne_bot`: every finitely generated graded `A`-module
  over a nonnegatively graded algebra is bounded below.
* `TauCeti.InternalGrading.map_mem_positive_smul_top` and
  `TauCeti.InternalGrading.decompose_zero_eq_zero_of_mem_positive`: functoriality of `A₊ M` under
  `A`-linear maps and vanishing of the degree-zero component on `A₊ A`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of graded rings*, Section 2.3, for graded modules.
* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for detection of linearity via the generating degrees of minimal resolutions.
-/

public section

namespace TauCeti.InternalGrading

open _root_.DirectSum

universe uk uA uM uN

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]
  {M : Type uM} [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝒜 : ℤ → Submodule k A) {G : InternalGrading k M ℤ} [SetLike.GradedSMul 𝒜 G.piece]

/-- The degree-`p` component of an element of `A₊ M` is a sum of products `a • y` with `a` of
some positive degree `i` and `y` of degree `p - i`. -/
theorem decompose_mem_span_of_mem_positive_smul_top {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) (p : ℤ) :
    (decompose G.piece x p : M) ∈ Submodule.span k
      {z | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, ∃ y ∈ G.piece (p - i), a • y = z} := by
  classical
  set S := Submodule.span k {z | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, ∃ y ∈ G.piece (p - i), a • y = z}
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
  · refine Submodule.iSup_induction _ (motive := fun a =>
      (decompose G.piece (a • y) p : M) ∈ S) ha (fun i a ha => ?_) ?_ ?_
    · refine Submodule.iSup_induction _ (motive := fun a =>
        (decompose G.piece (a • y) p : M) ∈ S) ha (fun hi a ha => ?_) ?_ ?_
      · let f : M →ₗ[k] M := Algebra.lsmul k k M a
        have hf : TauCeti.LinearMap.IsHomogeneous f G.piece G.piece i :=
          TauCeti.LinearMap.isHomogeneous_def.mpr fun q z hz => by
            simpa [f, add_comm] using SetLike.GradedSMul.smul_mem ha hz
        have h := hf.map_decompose (p - i) y
        rw [sub_add_cancel] at h
        simpa only [f, Algebra.lsmul_apply] using h ▸ Submodule.subset_span
          ⟨i, hi, a, ha, _, (decompose G.piece y (p - i)).property, rfl⟩
      · simp
      · intro a b ha hb
        simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
          S.add_mem ha hb
    · simp
    · intro a b ha hb
      simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
        S.add_mem ha hb
  · simpa only [decompose_add, DirectSum.add_apply, Submodule.coe_add] using S.add_mem hx hy

/-- A component of `A₊ M` lies in an `A`-submodule if all lower-degree pieces do. The positive
scalar lowers the degree of the module component needed to compute that component. -/
theorem decompose_mem_of_mem_positive_smul_top (U : Submodule A M) {p : ℤ}
    (hU : ∀ q < p, ∀ x ∈ G.piece q, x ∈ U) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    (decompose G.piece x p : M) ∈ U := by
  refine (Submodule.span_le (p := U.restrictScalars k)).mpr ?_
    (decompose_mem_span_of_mem_positive_smul_top 𝒜 hx p)
  rintro _ ⟨i, hi, a, -, y, hy, rfl⟩
  exact U.smul_mem a (hU (p - i) (by omega) y hy)

/-- **Graded Nakayama for homogeneous generators.** In a bounded-below graded module, if each
homogeneous piece lies in the sum of a homogeneous `A`-submodule and the positive-degree action
on the module, then that submodule is the whole module. This is generation modulo `A₊`. -/
theorem eq_top_of_piece_le_sup_positive_smul_top (U : Submodule A M)
    (hhom : SetLike.IsHomogeneous G.piece U) (b : ℤ)
    (hbelow : ∀ p < b, G.piece p = ⊥)
    (hU : ∀ p, G.piece p ≤ U.restrictScalars k ⊔
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) : U = ⊤ := by
  have pieces : ∀ n : ℕ, ∀ x ∈ G.piece (b + n), x ∈ U := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hU _ hx)
      have lower : ∀ q < b + n, ∀ x ∈ G.piece q, x ∈ U := by
        intro q hq x hx
        by_cases hqb : q < b
        · rw [hbelow q hqb] at hx
          have hz : x = 0 := by simpa using hx
          rw [hz]
          exact U.zero_mem
        · have heq : b + (q - b).toNat = q := by omega
          exact ih (q - b).toNat (by omega) x (heq.symm ▸ hx)
      rw [← decompose_of_mem_same G.piece hx, decompose_add,
        DirectSum.add_apply, Submodule.coe_add]
      exact U.add_mem (hhom _ hy)
        (decompose_mem_of_mem_positive_smul_top 𝒜 U lower hz)
  apply top_unique
  intro x _
  classical
  rw [← sum_support_decompose G.piece x]
  refine U.sum_mem fun p _ => ?_
  by_cases hp : p < b
  · have hz := (Submodule.eq_bot_iff _).mp (hbelow p hp) _ (decompose G.piece x p).property
    rw [hz]
    exact U.zero_mem
  · have heq : b + (p - b).toNat = p := by omega
    exact pieces (p - b).toNat _ (heq.symm ▸ (decompose G.piece x p).property)

/-- **Graded Nakayama.** A bounded-below graded module satisfying `A₊ M = M` is zero. -/
theorem subsingleton_of_positive_smul_top_eq_top (b : ℤ)
    (hbelow : ∀ p < b, G.piece p = ⊥)
    (h : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) = ⊤) :
    Subsingleton M := by
  have hbot : (⊥ : Submodule A M) = ⊤ :=
    eq_top_of_piece_le_sup_positive_smul_top 𝒜 ⊥ (by
      intro p x hx
      have hx : x = 0 := by simpa using hx
      simp [hx]) b hbelow (by simp [h])
  exact subsingleton_of_forall_eq 0 fun x => by
    have hx : x ∈ (⊥ : Submodule A M) := hbot.symm ▸ Submodule.mem_top
    simpa using hx

/-- **Graded Nakayama below a degree.** In a bounded-below graded module, if every homogeneous
piece below degree `e` lies in `A₊ M`, then all those pieces vanish. -/
theorem piece_eq_bot_of_piece_le_positive_smul_top (b : ℤ) (hbelow : ∀ p < b, G.piece p = ⊥)
    {e : ℤ} (h : ∀ p < e, G.piece p ≤ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M))
    {p : ℤ} (hp : p < e) : G.piece p = ⊥ := by
  induction hn : (p - b).toNat using Nat.strong_induction_on generalizing p with
  | ind n ih =>
    by_cases hpb : p < b
    · exact hbelow p hpb
    refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
    have hU := decompose_mem_of_mem_positive_smul_top 𝒜 (⊥ : Submodule A M) (p := p)
      (fun q hq y hy ↦ by
        have hq' : G.piece q = ⊥ := if hqb : q < b then hbelow q hqb else
          ih (q - b).toNat (by omega) (hq.trans hp) rfl
        rw [hq'] at hy
        simpa using hy) (h p hp hx)
    rwa [decompose_of_mem_same G.piece hx, Submodule.mem_bot] at hU

/-- The positive-degree action `A₊ M` is a homogeneous submodule. -/
theorem isHomogeneous_positive_smul_top :
    SetLike.IsHomogeneous G.piece ((⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) := by
  intro p x hx
  refine Submodule.span_le.mpr ?_ (decompose_mem_span_of_mem_positive_smul_top 𝒜 hx p)
  rintro _ ⟨i, hi, a, ha, y, -, rfl⟩
  exact Submodule.smul_mem_smul (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ha))
    Submodule.mem_top

variable {𝒜} in
/-- Degree-zero scalars preserve the positive-degree action `A₊ M`. -/
theorem smul_mem_positive_smul_top [SetLike.GradedMul 𝒜] {a : A} (ha : a ∈ 𝒜 0) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    a • x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  have hmul : ∀ b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i, a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
    intro b hb
    refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i)
      hb (fun i b hb => ?_) (by simp) (fun b c hb hc => by simpa [mul_add] using add_mem hb hc)
    refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i)
      hb (fun hi b hb => ?_) (by simp) (fun b c hb hc => by simpa [mul_add] using add_mem hb hc)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi
      (by simpa using SetLike.GradedMul.mul_mem ha hb))
  refine Submodule.smul_induction_on hx (fun b hb y _ => ?_) (fun x y hx hy => ?_)
  · rw [← mul_smul]
    exact Submodule.smul_mem_smul (hmul b hb) Submodule.mem_top
  · simpa only [smul_add] using Submodule.add_mem _ hx hy

variable [GradedAlgebra 𝒜]

/-- A bounded-below module over a nonnegatively graded algebra is generated in degree `d`
exactly when its homogeneous pieces outside degree `d` lie in `A₊ M`. Equivalently, its quotient
by the positive-degree action is concentrated in degree `d`. -/
theorem isGeneratedInDegree_iff_piece_le_positive_smul_top (h𝒜 : ∀ i < 0, 𝒜 i = ⊥)
    (b : ℤ) (hbelow : ∀ p < b, G.piece p = ⊥) (d : ℤ) :
    G.IsGeneratedInDegree A d ↔
      ∀ p, p ≠ d → G.piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  constructor
  · intro hG p hp
    rcases lt_or_gt_of_ne hp with hlt | hgt
    · simp [hG.piece_eq_bot_of_lt 𝒜 h𝒜 hlt]
    · exact hG.piece_le_smul_top 𝒜 hgt
  · intro hG
    have hspan := eq_top_of_piece_le_sup_positive_smul_top 𝒜
      (Submodule.span A (G.piece d : Set M)) (isHomogeneous_span_piece 𝒜 d) b hbelow
      fun p => by
        by_cases hp : p = d
        · subst p
          exact le_sup_of_le_left fun x hx => Submodule.subset_span hx
        · exact le_sup_of_le_right (hG p hp)
    exact (G.isGeneratedInDegree_iff d).mpr fun x => hspan.symm ▸ Submodule.mem_top

/-- The generating-degree criterion for a module finite over the grading's scalar semiring.
Its internal grading has finite support, which supplies the lower bound automatically. -/
theorem isGeneratedInDegree_iff_piece_le_positive_smul_top_of_finite [Module.Finite k M]
    (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) (d : ℤ) :
    G.IsGeneratedInDegree A d ↔
      ∀ p, p ≠ d → G.piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  obtain ⟨b, hb⟩ := G.finite_piece_ne_bot.bddBelow
  apply isGeneratedInDegree_iff_piece_le_positive_smul_top 𝒜 h𝒜 b _ d
  intro p hp
  by_contra hne
  have := hb hne
  omega

omit [IsScalarTower k A M] in
/-- Every finitely generated graded module over a nonnegatively graded algebra is bounded below:
the homogeneous components of a finite `A`-generating set have a minimum degree, and nonnegative
scalars never lower degree. -/
theorem exists_piece_eq_bot_of_finite [Module.Finite A M] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    ∃ b : ℤ, ∀ p < b, G.piece p = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  obtain ⟨b, hb⟩ : BddBelow (⋃ g ∈ s, ((decompose G.piece g).support : Set ℤ)) :=
    (s.finite_toSet.biUnion fun _ _ ↦ Finset.finite_toSet _).bddBelow
  refine ⟨b, fun p hp ↦ (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_⟩
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp (hs ▸ Submodule.mem_top : x ∈ _)
  rw [← decompose_of_mem_same G.piece hx, decompose_sum, DFinsupp.finsetSum_apply,
    AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_eq_zero fun r _ ↦ ?_
  rw [← sum_support_decompose G.piece (g r).1, Finset.smul_sum, decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_eq_zero fun q hq ↦ ?_
  have hbq : b ≤ q := hb (Set.mem_biUnion (g r).2 hq)
  have h := coe_decompose_smul_add_of_right_mem 𝒜 G.piece
    (decompose G.piece (g r).1 q).property (a := c r) (i := p - q)
  rw [sub_add_cancel] at h
  have hc0 : (decompose 𝒜 (c r) (p - q) : A) = 0 := by
    simpa only [h𝒜 (p - q) (by omega), Submodule.mem_bot] using
      (decompose 𝒜 (c r) (p - q)).property
  rw [h, hc0, zero_smul]

omit [IsScalarTower k A M] in
/-- The set of nonzero homogeneous pieces of a finitely generated graded module over a
nonnegatively graded algebra is bounded below. -/
theorem bddBelow_setOf_piece_ne_bot [Module.Finite A M] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    BddBelow {p | G.piece p ≠ ⊥} := by
  obtain ⟨b, hb⟩ := G.exists_piece_eq_bot_of_finite 𝒜 h𝒜
  exact ⟨b, fun p hp ↦ not_lt.mp fun hlt ↦ hp (hb p hlt)⟩

omit [GradedAlgebra 𝒜] in
/-- Every `A`-linear map carries `A₊ M` into `A₊ N`. -/
theorem map_mem_positive_smul_top {N : Type uN} [AddCommMonoid N] [Module k N]
    [Module A N] [IsScalarTower k A N] (f : M →ₗ[A] N) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    f x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
  · rw [f.map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- On a nonnegatively graded algebra itself, no nonzero degree-zero component arises from
`A₊ A`. -/
theorem decompose_zero_eq_zero_of_mem_positive (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) {a : A}
    (ha : a ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k A)) :
    (decompose 𝒜 a 0 : A) = 0 := by
  refine Submodule.smul_induction_on ha (fun x hx y _ => ?_) (fun x y hx hy => ?_)
  · refine Submodule.iSup_induction _ (motive := fun x => (decompose 𝒜 (x • y) 0 : A) = 0)
      hx (fun i x hx => ?_) (by simp) (fun b c hb hc => by
        rw [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add, hb, hc, add_zero])
    refine Submodule.iSup_induction _ (motive := fun x => (decompose 𝒜 (x • y) 0 : A) = 0)
      hx (fun hi x hx => ?_) (by simp) (fun b c hb hc => by
        rw [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add, hb, hc, add_zero])
    rw [smul_eq_mul]
    have hmul := coe_decompose_mul_add_of_left_mem 𝒜 (j := -i) (b := y) hx
    rw [add_neg_cancel] at hmul
    have hy0 : (decompose 𝒜 y (-i) : A) = 0 := by
      simpa only [h𝒜 (-i) (by omega), Submodule.mem_bot] using (decompose 𝒜 y (-i)).property
    rw [hmul, hy0, mul_zero]
  · rw [decompose_add, DirectSum.add_apply, Submodule.coe_add, hx, hy, add_zero]

/-- Over a nonnegatively graded algebra, the positive-degree action `A₊ N` is stable under all
scalars in `A`. -/
theorem smul_mem_positive_smul_top_of_nonneg {N : Type uN} [AddCommMonoid N] [Module k N]
    [Module A N] [IsScalarTower k A N] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) (a : A) {x : N}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N)) :
    a • x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) := by
  classical
  rw [← sum_support_decompose 𝒜 a, Finset.sum_smul]
  refine Submodule.sum_mem _ fun q _ => ?_
  rcases lt_trichotomy q 0 with hlt | rfl | hgt
  · have hz : (decompose 𝒜 a q : A) = 0 := by
      simpa only [h𝒜 q hlt, Submodule.mem_bot] using (decompose 𝒜 a q).property
    simp [hz]
  · exact smul_mem_positive_smul_top (decompose 𝒜 a 0).property hx
  · exact Submodule.smul_mem_smul
      (Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem hgt (decompose 𝒜 a q).property))
      Submodule.mem_top

/-- The positive-degree action `A₊ N` on a module `N` over a nonnegatively graded algebra, bundled
as an `A`-submodule. -/
def positiveSubmodule (N : Type uN) [AddCommMonoid N] [Module k N] [Module A N]
    [IsScalarTower k A N] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) : Submodule A N :=
  { (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) with
    smul_mem' := fun a _ hx => smul_mem_positive_smul_top_of_nonneg 𝒜 h𝒜 a hx }

/-- Membership in `positiveSubmodule` is membership in `A₊ N`. -/
@[simp]
theorem mem_positiveSubmodule_iff {N : Type uN} [AddCommMonoid N] [Module k N] [Module A N]
    [IsScalarTower k A N] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) {x : N} :
    x ∈ positiveSubmodule 𝒜 N h𝒜 ↔
      x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) :=
  (Iff.rfl)

/-- Restricting scalars of `positiveSubmodule` to `k` recovers `A₊ N`. -/
@[simp]
theorem restrictScalars_positiveSubmodule {N : Type uN} [AddCommMonoid N] [Module k N]
    [Module A N] [IsScalarTower k A N] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    (positiveSubmodule 𝒜 N h𝒜).restrictScalars k =
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) :=
  Submodule.ext fun _ => Iff.rfl

/-- The `A`-submodule `positiveSubmodule` of an internally graded module is homogeneous. -/
theorem isHomogeneous_positiveSubmodule {N : Type uN} [AddCommMonoid N] [Module k N]
    [Module A N] [IsScalarTower k A N] (H : InternalGrading k N ℤ) [SetLike.GradedSMul 𝒜 H.piece]
    (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    SetLike.IsHomogeneous H.piece (positiveSubmodule 𝒜 N h𝒜) :=
  H.isHomogeneous_positive_smul_top 𝒜

section Ring

variable {R : Type uk} [CommSemiring R] {B : Type uA} [Ring B] [Algebra R B]
  (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ]

/-- Over a nonnegatively graded algebra, subtracting the degree-zero component leaves a sum of
positive-degree components. -/
theorem sub_decompose_zero_mem_positive (hℬ : ∀ i < 0, ℬ i = ⊥) (b : B) :
    b - (decompose ℬ b 0 : B) ∈ ⨆ (i : ℤ) (_ : 0 < i), ℬ i := by
  classical
  let s := (decompose ℬ b).support
  have hsum : ∑ q ∈ s, (decompose ℬ b q : B) = b := sum_support_decompose ℬ b
  have herase : b - (decompose ℬ b 0 : B) = ∑ q ∈ s.erase 0, (decompose ℬ b q : B) := by
    by_cases h0 : (0 : ℤ) ∈ s
    · rw [← Finset.add_sum_erase s (fun q => (decompose ℬ b q : B)) h0] at hsum
      nth_rw 1 [← hsum]
      exact add_sub_cancel_left _ _
    · have hz : (decompose ℬ b 0 : B) = 0 := by simp [DFinsupp.notMem_support_iff.mp h0]
      nth_rw 1 [← hsum]
      rw [hz, sub_zero, Finset.erase_eq_of_notMem h0]
  rw [herase]
  refine Submodule.sum_mem _ fun q hq => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hq) with hlt | hgt
  · have hz : (decompose ℬ b q : B) = 0 := by
      simpa only [hℬ q hlt, Submodule.mem_bot] using (decompose ℬ b q).property
    simp [hz]
  · exact Submodule.mem_iSup_of_mem q
      (Submodule.mem_iSup_of_mem hgt (decompose ℬ b q).property)

end Ring

end TauCeti.InternalGrading
