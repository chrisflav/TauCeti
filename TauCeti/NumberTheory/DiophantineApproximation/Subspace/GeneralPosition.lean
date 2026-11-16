/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.LinearAlgebra.Dual.GeneralPosition
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.ApproxProd

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import TauCeti.Analysis.AbsoluteValue.Dual
import TauCeti.Data.Finset.Max
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.NumberTheory.Height.Northcott
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# The approximation product for linear forms in general position

Let `K` be a number field, `F` a field extension of `K`, `Sinf` and `Sfin` finite sets of infinite
and finite places of `K`, and at each place `v` let `w v` be an absolute value of `F` lying over
`v` and `L v : κ → Module.Dual F (ι → F)` a family of linear forms whose restriction to a finite
subset `B v : Finset κ` is in general position (`Module.Dual.IsGeneralPosition`). The general
approximation product `NumberField.generalProd` multiplies the normalized values
`w v (L v k x) / ⨆ j, v (x j)` over all `k ∈ B v` at each place `v ∈ Sinf ∪ Sfin`, raised to
`v.mult` at infinite places. When `B v = Finset.univ` on `ι`, this agrees with
`NumberField.approxProd` (`NumberField.generalProd_univ_eq_approxProd`).

Following Vojta (1987) and Bombieri–Gubler (Theorem 7.2.9), this file reduces `generalProd` to
finitely many linearly independent systems of `card ι` forms:

1. At a place where `card ι ≤ (B v).card`, keeping the `card ι` smallest values `w v (L v k x)`
   (`Finset.exists_subset_card_eq_forall_le`) selects a basis of `Module.Dual F (ι → F)`. That
   basis bounds the local sup norm by a constant times its largest value
   (`AbsoluteValue.exists_pos_forall_iSup_le_mul_iSup_apply`), so every discarded normalized factor
   is bounded below by a positive constant independent of `x`.
2. At a place where `(B v).card ≤ card ι`, the forms on `B v` are linearly independent and extend
   to a basis by adding coordinate projections `LinearMap.proj`
   (`Module.Dual.exists_index_extendProj`) at no cost, since each coordinate projection has
   normalized value at most `1`.

Assembling the local choices across `Sinf` and `Sfin` yields finitely many systems `M` of linearly
independent forms and a constant `C > 0` such that every nonzero `x : ι → K` satisfies
`approxProd Sinf Sfin w M x ≤ C * generalProd Sinf Sfin w B L x` for some `M`
(`NumberField.exists_finset_pos_forall_approxProd_le_mul_generalProd`). Combining this with the
Northcott property (`Height.exists_finset_submodule_of_mulHeight_le`) absorbs `C` into a halving
of the exponent `ε`, reducing the general-position inequality
`generalProd Sinf Sfin w B L x ≤ mulHeight x ^ (-card ι - ε)` directly to the linearly independent
inequality at `ε / 2` (`NumberField.exists_finset_submodule_or_approxProd_le_of_generalProd_le`).

## Main results

* `NumberField.generalProd`: the approximation product over arbitrary finite sets `B v` of forms at
  each place, together with its invariance and monotonicity API (`generalProd_smul`,
  `generalProd_congr`, `generalProd_union`, `generalProd_univ_eq_approxProd`,
  `generalProd_le_generalProd_of_subset`, `generalProd_le_generalProd_of_subset_forms`).
* `NumberField.exists_finset_pos_forall_prod_div_iSup_le`: local reduction at one place for any
  finite family of forms in general position.
* `NumberField.exists_finset_pos_forall_approxProd_le_mul_generalProd`: global reduction of
  `generalProd` to finitely many linearly independent `approxProd` systems.
* `NumberField.exists_finset_submodule_or_approxProd_le_of_generalProd_le`: reduction of the
  general-position Subspace Theorem inequality with exponent `-card ι - ε` to finitely many proper
  subspaces (from Northcott) and finitely many linearly independent systems at exponent
  `-card ι - ε / 2`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Definition 7.2.8 and Theorem 7.2.9.
* P. Vojta, *Diophantine Approximations and Value Distribution Theory*, Lecture Notes in Mathematics
  1239, Springer (1987).
-/

public section

open AbsoluteValue Height Module

namespace NumberField

section Local

variable {K F ι κ : Type*} [Field K] [Field F] [Algebra K F]

/-- A local factor of `generalProd` is nonnegative. -/
theorem prod_mem_div_iSup_nonneg (v : AbsoluteValue K ℝ) (w : AbsoluteValue F ℝ)
    (B : Finset κ) (L : κ → Dual F (ι → F)) (x : ι → K) :
    0 ≤ ∏ k ∈ B, w (L k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) :=
  Finset.prod_nonneg fun _ _ ↦
    div_nonneg (apply_nonneg _ _) (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)

/-- Enlarging a finite set of forms by coordinate projections at a place where `w` lies over `v`
can only decrease the local product. -/
theorem prod_mem_div_iSup_le_of_subset [Finite ι] {v : AbsoluteValue K ℝ} {w : AbsoluteValue F ℝ}
    [w.LiesOver v] {B B' : Finset κ} (hBB' : B ⊆ B') {L : κ → Dual F (ι → F)}
    (hproj : ∀ k ∈ B', k ∉ B → ∃ i : ι, L k = LinearMap.proj i) (x : ι → K) :
    ∏ k ∈ B', w (L k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) ≤
      ∏ k ∈ B, w (L k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  classical
  rw [← Finset.prod_sdiff hBB']
  refine mul_le_of_le_one_left (prod_mem_div_iSup_nonneg v w B L x) ?_
  refine Finset.prod_le_one₀ (fun _ _ ↦ ?_) fun k hk ↦ ?_
  · exact div_nonneg (apply_nonneg _ _) (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
  · obtain ⟨i, hi⟩ := hproj k (Finset.mem_sdiff.mp hk).1 (Finset.mem_sdiff.mp hk).2
    rw [hi, LinearMap.proj_apply, LiesOver.apply_algebraMap v]
    exact div_le_one_of_le₀ (le_ciSup (f := fun j ↦ v (x j)) (Finite.bddAbove_range _) i)
      (Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)

/-- **Local reduction when `B` has at most `card ι` forms**: a general-position family of at most
`card ι` linear forms on `ι → F` is linearly independent and extends to a basis `l` by coordinate
projections, whose local approximation factor is at most that of `B` at every point `x`. -/
theorem exists_linearIndependent_forall_prod_div_iSup_le [Fintype ι]
    {v : AbsoluteValue K ℝ} {w : AbsoluteValue F ℝ} [w.LiesOver v]
    (B : Finset κ) (L : κ → Dual F (ι → F)) (hcard : B.card ≤ Fintype.card ι)
    (hL : Dual.IsGeneralPosition fun k : B ↦ L k) :
    ∃ l : ι → Dual F (ι → F), LinearIndependent F l ∧
      ∀ x : ι → K,
        (∏ i : ι, w (l i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ≤
          ∏ k ∈ B, w (L k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  classical
  have hliB : LinearIndependent F fun k : B ↦ L k :=
    (Dual.isGeneralPosition_iff_linearIndependent_of_card_le
      (by simpa [Module.finrank_fintype_fun_eq_card] using hcard)).mp hL
  obtain ⟨e, l, hl, he, hproj⟩ := Dual.exists_index_extendProj hliB
  refine ⟨l, hl, fun x ↦ ?_⟩
  let s : Finset ι := Finset.univ.image e
  have hsub := prod_mem_div_iSup_le_of_subset (v := v) (w := w) (L := l) (Finset.subset_univ s)
    (fun i _ hi ↦ hproj i fun ⟨k, hk⟩ ↦ hi (hk ▸ Finset.mem_image_of_mem e (Finset.mem_univ k))) x
  refine hsub.trans_eq ?_
  rw [Finset.prod_image fun _ _ _ _ h ↦ e.injective h]
  simp_rw [he]
  exact Finset.prod_coe_sort B fun k ↦ w (L k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)

/-- Given a `card ι`-element subset `t ⊆ B` on which `w (L k xF)` takes its smallest values and a
sup-norm bound `M ≤ C₀ * ⨆ i, w (L (eqv i) xF)`, every discarded factor `k ∈ B \ t` is at least
`C₀⁻¹`, so the product over `t` is bounded by `C₀ ^ (B.card - card ι)` times the product over
`B`. -/
private theorem prod_div_iSup_le_of_subset_min [Fintype ι]
    {v : AbsoluteValue K ℝ} {w : AbsoluteValue F ℝ} [w.LiesOver v]
    {B t : Finset κ} (htB : t ⊆ B) (htcard : t.card = Fintype.card ι) (eqv : ι ≃ t)
    {L : κ → Dual F (ι → F)} {C₀ : ℝ} (hC₀ : 0 < C₀) {x : ι → K} (hx : x ≠ 0)
    (hsup : ⨆ j, w (algebraMap K F (x j)) ≤
      C₀ * ⨆ i, w (L (eqv i).1 fun j ↦ algebraMap K F (x j)))
    (hmin : ∀ a ∈ t, ∀ b ∈ B, b ∉ t →
      w (L a fun j ↦ algebraMap K F (x j)) ≤ w (L b fun j ↦ algebraMap K F (x j))) :
    (∏ i : ι, w (L (eqv i).1 fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ≤
      C₀ ^ (B.card - Fintype.card ι) *
        ∏ k ∈ B, w (L k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  classical
  obtain ⟨j₀, hj₀⟩ : ∃ j : ι, x j ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨j₀⟩
  let xF : ι → F := fun j ↦ algebraMap K F (x j)
  set M : ℝ := ⨆ j, v (x j)
  have hM_pos : 0 < M :=
    lt_of_lt_of_le (v.pos hj₀) (le_ciSup (f := fun j ↦ v (x j)) (Finite.bddAbove_range _) j₀)
  have hxF_sup : (⨆ j, w (xF j)) = M := by simp only [M, xF, LiesOver.apply_algebraMap v]
  have hdisc : ∀ b ∈ B \ t, C₀⁻¹ ≤ w (L b xF) / M := fun b hb ↦ by
    rw [Finset.mem_sdiff] at hb
    have hsup_le : (⨆ i, w (L (eqv i).1 xF)) ≤ w (L b xF) :=
      ciSup_le fun i ↦ hmin (eqv i).1 (eqv i).2 b hb.1 hb.2
    have hMb : M ≤ C₀ * w (L b xF) := by
      calc M = ⨆ j, w (xF j) := hxF_sup.symm
        _ ≤ C₀ * ⨆ i, w (L (eqv i).1 xF) := hsup
        _ ≤ C₀ * w (L b xF) := mul_le_mul_of_nonneg_left hsup_le hC₀.le
    rw [le_div_iff₀ hM_pos]
    calc C₀⁻¹ * M ≤ C₀⁻¹ * (C₀ * w (L b xF)) := mul_le_mul_of_nonneg_left hMb (by positivity)
      _ = w (L b xF) := inv_mul_cancel_left₀ hC₀.ne' _
  have hprod_disc : (C₀ ^ (B.card - Fintype.card ι))⁻¹ ≤ ∏ b ∈ B \ t, w (L b xF) / M := by
    have hcard_sdiff : (B \ t).card = B.card - Fintype.card ι := by
      rw [Finset.card_sdiff_of_subset htB, htcard]
    calc (C₀ ^ (B.card - Fintype.card ι))⁻¹
        = ∏ _b ∈ B \ t, C₀⁻¹ := by rw [Finset.prod_const, hcard_sdiff, inv_pow]
      _ ≤ ∏ b ∈ B \ t, w (L b xF) / M := Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) hdisc
  have hform_eq : (∏ i : ι, w (L (eqv i).1 xF) / M) = ∏ k ∈ t, w (L k xF) / M :=
    (Fintype.prod_equiv eqv _ (fun k : t ↦ w (L k.1 xF) / M) fun _ ↦ rfl).trans
      (Finset.prod_coe_sort t fun k ↦ w (L k xF) / M)
  have h1 : 1 ≤ C₀ ^ (B.card - Fintype.card ι) * ∏ b ∈ B \ t, w (L b xF) / M := by
    calc (1 : ℝ)
        = C₀ ^ (B.card - Fintype.card ι) * (C₀ ^ (B.card - Fintype.card ι))⁻¹ :=
          (mul_inv_cancel₀ (by positivity)).symm
      _ ≤ C₀ ^ (B.card - Fintype.card ι) * ∏ b ∈ B \ t, w (L b xF) / M :=
          mul_le_mul_of_nonneg_left hprod_disc (by positivity)
  rw [hform_eq, ← Finset.prod_sdiff htB]
  have ht_nonneg : 0 ≤ ∏ k ∈ t, w (L k xF) / M := prod_mem_div_iSup_nonneg v w t L x
  calc (∏ k ∈ t, w (L k xF) / M)
      = (∏ k ∈ t, w (L k xF) / M) * 1 := (mul_one _).symm
    _ ≤ (∏ k ∈ t, w (L k xF) / M) *
          (C₀ ^ (B.card - Fintype.card ι) * ∏ b ∈ B \ t, w (L b xF) / M) :=
        mul_le_mul_of_nonneg_left h1 ht_nonneg
    _ = C₀ ^ (B.card - Fintype.card ι) *
          ((∏ b ∈ B \ t, w (L b xF) / M) * ∏ k ∈ t, w (L k xF) / M) := by ring

/-- **Local reduction when `B` has at least `card ι` forms**: selecting the `card ι` smallest
values `w (L k x)` yields a basis of `Dual F (ι → F)` whose sup-norm comparison bounds every
discarded normalized factor from below by a positive constant independent of `x`. -/
theorem exists_finset_pos_forall_prod_div_iSup_le_of_card_le [Fintype ι]
    {v : AbsoluteValue K ℝ} {w : AbsoluteValue F ℝ} [w.LiesOver v]
    (B : Finset κ) (L : κ → Dual F (ι → F)) (hcard : Fintype.card ι ≤ B.card)
    (hL : Dual.IsGeneralPosition fun k : B ↦ L k) :
    ∃ (S : Finset (ι → Dual F (ι → F))) (C : ℝ), 0 < C ∧
      (∀ l ∈ S, LinearIndependent F l) ∧
      ∀ x : ι → K, x ≠ 0 → ∃ l ∈ S,
        (∏ i : ι, w (l i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ≤
          C * ∏ k ∈ B, w (L k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Finset (Finset κ), ∀ s, s ∈ P ↔ s ⊆ B ∧ s.card = Fintype.card ι :=
    ⟨B.powersetCard (Fintype.card ι), fun _ ↦ Finset.mem_powersetCard⟩
  obtain ⟨eqv⟩ : Nonempty ((s : P) → ι ≃ s.1) :=
    ⟨fun s ↦ Fintype.equivOfCardEq (by rw [Fintype.card_coe, ((hP s.1).mp s.2).2])⟩
  let form : P → ι → Dual F (ι → F) := fun s i ↦ L (eqv s i).1
  have hli : ∀ s : P, LinearIndependent F (form s) := fun s ↦ by
    have hsub := ((hP s.1).mp s.2).1
    let emb : ι → B := fun i ↦ ⟨(eqv s i).1, hsub (eqv s i).2⟩
    have hemb : Function.Injective emb := fun _ _ h ↦
      (eqv s).injective (Subtype.ext (Subtype.mk.inj h))
    have h := hL.linearIndependent_comp hemb (by simp [Module.finrank_fintype_fun_eq_card])
    exact h
  choose c hc_pos hc_le using fun s : P ↦ w.exists_pos_forall_iSup_le_mul_iSup_apply (hli s)
  let C₀ : ℝ := 1 + ∑ s : P, c s
  have hC₀_pos : 0 < C₀ := by
    have hsum : 0 ≤ ∑ s : P, c s := Finset.sum_nonneg fun s _ ↦ (hc_pos s).le
    linarith
  have hc_le_C₀ : ∀ s : P, c s ≤ C₀ := fun s ↦ by
    have h1 : c s ≤ ∑ s' : P, c s' :=
      Finset.single_le_sum (fun s' _ ↦ (hc_pos s').le) (Finset.mem_univ s)
    linarith
  refine ⟨Finset.univ.image form, C₀ ^ (B.card - Fintype.card ι), by positivity, ?_, fun x hx ↦ ?_⟩
  · rintro _ hmem
    rcases Finset.mem_image.mp hmem with ⟨s, _, rfl⟩
    exact hli s
  · obtain ⟨t, htB, htcard, hmin⟩ :=
      Finset.exists_subset_card_eq_forall_le B (fun k ↦ w (L k fun j ↦ algebraMap K F (x j))) hcard
    let s : P := ⟨t, (hP t).mpr ⟨htB, htcard⟩⟩
    refine ⟨form s, Finset.mem_image_of_mem form (Finset.mem_univ s), ?_⟩
    have hsup : (⨆ j, w (algebraMap K F (x j))) ≤
        C₀ * ⨆ i, w (L (eqv s i).1 fun j ↦ algebraMap K F (x j)) :=
      (hc_le s fun j ↦ algebraMap K F (x j)).trans
        (mul_le_mul_of_nonneg_right (hc_le_C₀ s) (Real.iSup_nonneg fun _ ↦ w.nonneg _))
    exact prod_div_iSup_le_of_subset_min htB htcard (eqv s) hC₀_pos hx hsup hmin

/-- **Unified local reduction at a single place**: for any finite family `B` of linear forms in
general position on `ι → F` measured by an absolute value `w` lying over `v`, there exist finitely
many bases `l` of `Dual F (ι → F)` and a constant `C > 0` such that every nonzero `x : ι → K`
satisfies the local approximation-product inequality for one of these bases. -/
theorem exists_finset_pos_forall_prod_div_iSup_le [Fintype ι]
    {v : AbsoluteValue K ℝ} {w : AbsoluteValue F ℝ} [w.LiesOver v]
    (B : Finset κ) (L : κ → Dual F (ι → F))
    (hL : Dual.IsGeneralPosition fun k : B ↦ L k) :
    ∃ (S : Finset (ι → Dual F (ι → F))) (C : ℝ), 0 < C ∧
      (∀ l ∈ S, LinearIndependent F l) ∧
      ∀ x : ι → K, x ≠ 0 → ∃ l ∈ S,
        (∏ i : ι, w (l i fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ≤
          C * ∏ k ∈ B, w (L k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  rcases le_total (Fintype.card ι) B.card with hcard | hcard
  · exact exists_finset_pos_forall_prod_div_iSup_le_of_card_le (v := v) (w := w) B L hcard hL
  · obtain ⟨l, hl, hle⟩ :=
      exists_linearIndependent_forall_prod_div_iSup_le (v := v) (w := w) B L hcard hL
    exact ⟨{l}, 1, one_pos, by simpa using hl, fun x _ ↦
      ⟨l, Finset.mem_singleton_self l, by simpa using hle x⟩⟩

end Local

section Global

variable {K F ι κ : Type*} [Field K] [Field F] [Algebra K F] [NumberField K]

/-- The approximation product of a point `x : ι → K` with respect to finite families `B v` of
linear forms `L v k` with coefficients in `F` at the places of `K` in `Sinf` and `Sfin`, each
measured by an absolute value `w v` of `F`: the product over `v ∈ Sinf` of
`(∏ k ∈ B v.1, w v.1 (L v.1 k x) / ⨆ j, v (x j)) ^ v.mult`, times the product over `v ∈ Sfin` of
`∏ k ∈ B v.1, w v.1 (L v.1 k x) / ⨆ j, v (x j)`, where `x` is mapped into `F`.

Using one index type `κ` with a finite subset `B v : Finset κ` per place lets every place carry a
different number of forms while keeping all systems in a single type. When `κ = ι` and
`B _ = Finset.univ`, this coincides with `NumberField.approxProd`. -/
noncomputable def generalProd (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F)) (x : ι → K) : ℝ :=
  (∏ v ∈ Sinf,
      (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
    ∏ v ∈ Sfin, ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)

/-- Unfolding lemma for `generalProd`. -/
theorem generalProd_def (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F)) (x : ι → K) :
    generalProd Sinf Sfin w B L x =
      (∏ v ∈ Sinf,
          (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j)) ^ v.mult) *
        ∏ v ∈ Sfin, ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v (x j) := by
  rw [generalProd]

variable {Sinf Sinf' : Finset (InfinitePlace K)} {Sfin Sfin' : Finset (FinitePlace K)}
  {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ} {B : AbsoluteValue K ℝ → Finset κ}
  {L : AbsoluteValue K ℝ → κ → Dual F (ι → F)}

/-- When `κ = ι` and every place takes all forms `Finset.univ`, `generalProd` coincides with
`approxProd`. -/
theorem generalProd_univ_eq_approxProd [Fintype ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → ι → Dual F (ι → F))
    (x : ι → K) :
    generalProd Sinf Sfin w (fun _ ↦ Finset.univ) L x = approxProd Sinf Sfin w L x := by
  rw [generalProd_def, approxProd_def]

/-- The general approximation product is invariant under scaling the point by a nonzero scalar,
provided that each absolute value `w v` lies over `v`. -/
theorem generalProd_smul (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1) {c : K} (hc : c ≠ 0) (x : ι → K) :
    generalProd Sinf Sfin w B L (c • x) = generalProd Sinf Sfin w B L x := by
  simp only [generalProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  congr 1
  · refine Finset.prod_congr rfl fun v hv ↦ ?_
    have := hwInf v hv
    simp only [apply_div_iSup_smul _ hc]
  · refine Finset.prod_congr rfl fun v hv ↦ ?_
    have := hwFin v hv
    simp only [apply_div_iSup_smul _ hc]

/-- The general approximation product depends on `B` and `L` only at the places of `Sinf` and
`Sfin` (and on `L v` only at indices in `B v`). -/
theorem generalProd_congr {B' : AbsoluteValue K ℝ → Finset κ}
    {L' : AbsoluteValue K ℝ → κ → Dual F (ι → F)}
    (hBInf : ∀ v ∈ Sinf, B v.1 = B' v.1) (hBFin : ∀ v ∈ Sfin, B v.1 = B' v.1)
    (hLInf : ∀ v ∈ Sinf, ∀ k ∈ B v.1, L v.1 k = L' v.1 k)
    (hLFin : ∀ v ∈ Sfin, ∀ k ∈ B v.1, L v.1 k = L' v.1 k) (x : ι → K) :
    generalProd Sinf Sfin w B L x = generalProd Sinf Sfin w B' L' x := by
  simp only [generalProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  congr 1
  · refine Finset.prod_congr rfl fun v hv ↦ congrArg (· ^ v.mult) ?_
    rw [← hBInf v hv]
    exact Finset.prod_congr rfl fun k hk ↦ by rw [hLInf v hv k hk]
  · refine Finset.prod_congr rfl fun v hv ↦ ?_
    rw [← hBFin v hv]
    exact Finset.prod_congr rfl fun k hk ↦ by rw [hLFin v hv k hk]

/-- The general approximation product is nonnegative. -/
theorem generalProd_nonneg (x : ι → K) : 0 ≤ generalProd Sinf Sfin w B L x := by
  simp only [generalProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  exact mul_nonneg
    (Finset.prod_nonneg fun v _ ↦ pow_nonneg (prod_mem_div_iSup_nonneg _ _ _ _ x) _)
    (Finset.prod_nonneg fun v _ ↦ prod_mem_div_iSup_nonneg _ _ _ _ x)

/-- The general approximation product over no places is `1`. -/
@[simp]
theorem generalProd_empty (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (B : AbsoluteValue K ℝ → Finset κ) (L : AbsoluteValue K ℝ → κ → Dual F (ι → F)) (x : ι → K) :
    generalProd ∅ ∅ w B L x = 1 := by
  simp [generalProd_def]

/-- The general approximation product with empty form sets at every place is `1`. -/
@[simp]
theorem generalProd_empty_forms (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (x : ι → K) :
    generalProd Sinf Sfin w (fun _ ↦ (∅ : Finset κ)) L x = 1 := by
  simp [generalProd_def]

/-- The general approximation product is multiplicative in disjoint sets of places. -/
theorem generalProd_union [DecidableEq (InfinitePlace K)] [DecidableEq (FinitePlace K)]
    (hinf : Disjoint Sinf Sinf') (hfin : Disjoint Sfin Sfin') (x : ι → K) :
    generalProd (Sinf ∪ Sinf') (Sfin ∪ Sfin') w B L x =
      generalProd Sinf Sfin w B L x * generalProd Sinf' Sfin' w B L x := by
  simp only [generalProd_def, Finset.prod_union hinf, Finset.prod_union hfin]
  ring

/-- Adding coordinate projections to the form sets `B v` at places of `Sinf` and `Sfin` can only
decrease `generalProd`. -/
theorem generalProd_le_generalProd_of_subset_forms [Finite ι] {B' : AbsoluteValue K ℝ → Finset κ}
    (hBInf : ∀ v ∈ Sinf, B v.1 ⊆ B' v.1) (hBFin : ∀ v ∈ Sfin, B v.1 ⊆ B' v.1)
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (hLInf : ∀ v ∈ Sinf, ∀ k ∈ B' v.1, k ∉ B v.1 → ∃ i : ι, L v.1 k = LinearMap.proj i)
    (hLFin : ∀ v ∈ Sfin, ∀ k ∈ B' v.1, k ∉ B v.1 → ∃ i : ι, L v.1 k = LinearMap.proj i)
    (x : ι → K) :
    generalProd Sinf Sfin w B' L x ≤ generalProd Sinf Sfin w B L x := by
  simp only [generalProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  refine mul_le_mul
    (Finset.prod_le_prod₀ (fun _ _ ↦ pow_nonneg (prod_mem_div_iSup_nonneg _ _ _ _ x) _)
      fun v hv ↦ pow_le_pow_left₀ (prod_mem_div_iSup_nonneg _ _ _ _ x) ?_ _)
    (Finset.prod_le_prod₀ (fun _ _ ↦ prod_mem_div_iSup_nonneg _ _ _ _ x) fun v hv ↦ ?_)
    (Finset.prod_nonneg fun _ _ ↦ prod_mem_div_iSup_nonneg _ _ _ _ x)
    (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (prod_mem_div_iSup_nonneg _ _ _ _ x) _)
  · have := hwInf v hv
    exact prod_mem_div_iSup_le_of_subset (hBInf v hv) (hLInf v hv) x
  · have := hwFin v hv
    exact prod_mem_div_iSup_le_of_subset (hBFin v hv) (hLFin v hv) x

/-- The general approximation product is at most `1` when every form at every place of `Sinf` and
`Sfin` is a coordinate projection, measured by an absolute value lying over that place. -/
theorem generalProd_le_one [Finite ι] (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (hLInf : ∀ v ∈ Sinf, ∀ k ∈ B v.1, ∃ i : ι, L v.1 k = LinearMap.proj i)
    (hLFin : ∀ v ∈ Sfin, ∀ k ∈ B v.1, ∃ i : ι, L v.1 k = LinearMap.proj i) (x : ι → K) :
    generalProd Sinf Sfin w B L x ≤ 1 := by
  simpa using generalProd_le_generalProd_of_subset_forms (B := fun _ ↦ (∅ : Finset κ)) (B' := B)
    (fun _ _ ↦ Finset.empty_subset _) (fun _ _ ↦ Finset.empty_subset _) hwInf hwFin
    (fun v hv k hk _ ↦ hLInf v hv k hk) (fun v hv k hk _ ↦ hLFin v hv k hk) x

/-- Enlarging the sets of places by places carrying only coordinate projections can only decrease
`generalProd`. -/
theorem generalProd_le_generalProd_of_subset [Finite ι] (hinf : Sinf ⊆ Sinf') (hfin : Sfin ⊆ Sfin')
    (hwInf : ∀ v ∈ Sinf', v ∉ Sinf → (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ Sfin', v ∉ Sfin → (w v.1).LiesOver v.1)
    (hLInf : ∀ v ∈ Sinf', v ∉ Sinf → ∀ k ∈ B v.1, ∃ i : ι, L v.1 k = LinearMap.proj i)
    (hLFin : ∀ v ∈ Sfin', v ∉ Sfin → ∀ k ∈ B v.1, ∃ i : ι, L v.1 k = LinearMap.proj i)
    (x : ι → K) :
    generalProd Sinf' Sfin' w B L x ≤ generalProd Sinf Sfin w B L x := by
  classical
  rw [← Finset.union_sdiff_of_subset hinf, ← Finset.union_sdiff_of_subset hfin,
    generalProd_union Finset.disjoint_sdiff Finset.disjoint_sdiff]
  refine mul_le_of_le_one_right (generalProd_nonneg x) (generalProd_le_one ?_ ?_ ?_ ?_ x) <;>
    simp only [Finset.mem_sdiff] <;> grind

/-- The underlying absolute values of distinct infinite and finite places are distinct. -/
private theorem placeAbv_injective (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) :
    Function.Injective (Sum.elim (fun v : Sinf ↦ v.1.1) (fun u : Sfin ↦ u.1.1)) := by
  rintro (⟨v₁, _⟩ | ⟨u₁, _⟩) (⟨v₂, _⟩ | ⟨u₂, _⟩) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Subtype.ext (Subtype.ext h))
  · exact (v₁.not_isNonarchimedean (h ▸ fun a b ↦ u₂.add_le a b)).elim
  · exact (v₂.not_isNonarchimedean (h.symm ▸ fun a b ↦ u₁.add_le a b)).elim
  · exact congrArg Sum.inr (Subtype.ext (Subtype.ext h))

/-- Multiplying placewise bounds at `Sinf` (raised to `v.mult`) and `Sfin` bounds `approxProd` by
a constant multiple of `generalProd`. -/
private theorem approxProd_le_mul_generalProd_of_forall [Fintype ι]
    {M : AbsoluteValue K ℝ → ι → Dual F (ι → F)} {cInf : InfinitePlace K → ℝ}
    {cFin : FinitePlace K → ℝ} (hcInf : ∀ v ∈ Sinf, 0 ≤ cInf v)
    {x : ι → K}
    (hInf : ∀ v ∈ Sinf,
      (∏ i, w v.1 (M v.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, v.1 (x j)) ≤
        cInf v * ∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, v.1 (x j))
    (hFin : ∀ u ∈ Sfin,
      (∏ i, w u.1 (M u.1 i fun j ↦ algebraMap K F (x j)) / ⨆ j, u.1 (x j)) ≤
        cFin u * ∏ k ∈ B u.1, w u.1 (L u.1 k fun j ↦ algebraMap K F (x j)) / ⨆ j, u.1 (x j)) :
    approxProd Sinf Sfin w M x ≤
      ((∏ v ∈ Sinf, cInf v ^ v.mult) * ∏ u ∈ Sfin, cFin u) * generalProd Sinf Sfin w B L x := by
  simp only [approxProd_def, generalProd_def, InfinitePlace.coe_apply, FinitePlace.coe_apply]
  have h1 : (∏ v ∈ Sinf, (∏ i, w v.1 (M v.1 i fun j ↦ algebraMap K F (x j)) /
        ⨆ j, v.1 (x j)) ^ v.mult) ≤
      (∏ v ∈ Sinf, cInf v ^ v.mult) *
        ∏ v ∈ Sinf, (∏ k ∈ B v.1, w v.1 (L v.1 k fun j ↦ algebraMap K F (x j)) /
          ⨆ j, v.1 (x j)) ^ v.mult := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀
      (fun _ _ ↦ pow_nonneg (prod_div_iSup_nonneg _ _ _ x) _) fun v hv ↦ ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (prod_div_iSup_nonneg _ _ _ x) (hInf v hv) _
  have h2 : (∏ u ∈ Sfin, ∏ i, w u.1 (M u.1 i fun j ↦ algebraMap K F (x j)) /
        ⨆ j, u.1 (x j)) ≤
      (∏ u ∈ Sfin, cFin u) *
        ∏ u ∈ Sfin, ∏ k ∈ B u.1, w u.1 (L u.1 k fun j ↦ algebraMap K F (x j)) /
          ⨆ j, u.1 (x j) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ prod_div_iSup_nonneg _ _ _ x) hFin
  have hmul := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ ↦ prod_div_iSup_nonneg _ _ _ x)
    (mul_nonneg (Finset.prod_nonneg fun v hv ↦ pow_nonneg (hcInf v hv) _)
      (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (prod_mem_div_iSup_nonneg _ _ _ _ x) _))
  exact hmul.trans_eq (by ring)

/-- **Global reduction from general position to linearly independent systems** (Vojta 1987;
Bombieri–Gubler, Theorem 7.2.9). Given finite sets `Sinf` and `Sfin` of places of `K`, extensions
`w v` lying over `v`, and finite families `B v` of forms `L v` in general position at every place
of `Sinf` and `Sfin`, there exist finitely many systems `M` of linearly independent forms at those
places and a constant `C > 0` such that every nonzero `x : ι → K` satisfies
`approxProd Sinf Sfin w M x ≤ C * generalProd Sinf Sfin w B L x` for at least one `M`. -/
theorem exists_finset_pos_forall_approxProd_le_mul_generalProd [Fintype ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (hLInf : ∀ v ∈ Sinf, Dual.IsGeneralPosition fun k : B v.1 ↦ L v.1 k)
    (hLFin : ∀ v ∈ Sfin, Dual.IsGeneralPosition fun k : B v.1 ↦ L v.1 k) :
    ∃ (T : Finset (AbsoluteValue K ℝ → ι → Dual F (ι → F))) (C : ℝ), 0 < C ∧
      (∀ M ∈ T, (∀ v ∈ Sinf, LinearIndependent F (M v.1)) ∧
        ∀ v ∈ Sfin, LinearIndependent F (M v.1)) ∧
      ∀ x : ι → K, x ≠ 0 → ∃ M ∈ T,
        approxProd Sinf Sfin w M x ≤ C * generalProd Sinf Sfin w B L x := by
  classical
  let P := {v : InfinitePlace K // v ∈ Sinf} ⊕ {u : FinitePlace K // u ∈ Sfin}
  let abv : P → AbsoluteValue K ℝ := Sum.elim (fun v ↦ v.1.1) (fun u ↦ u.1.1)
  have habv : Function.Injective abv := placeAbv_injective Sinf Sfin
  have hloc : ∀ p : P, ∃ (S : Finset (ι → Dual F (ι → F))) (c : ℝ), 0 < c ∧
      (∀ l ∈ S, LinearIndependent F l) ∧ ∀ x : ι → K, x ≠ 0 → ∃ l ∈ S,
        (∏ i : ι, w (abv p) (l i fun j ↦ algebraMap K F (x j)) / ⨆ j, abv p (x j)) ≤
          c * ∏ k ∈ B (abv p), w (abv p) (L (abv p) k fun j ↦ algebraMap K F (x j)) /
            ⨆ j, abv p (x j) := by
    rintro (⟨v, hv⟩ | ⟨u, hu⟩) <;> simp only [abv, Sum.elim_inl, Sum.elim_inr]
    · have := hwInf v hv
      exact exists_finset_pos_forall_prod_div_iSup_le (B v.1) (L v.1) (hLInf v hv)
    · have := hwFin u hu
      exact exists_finset_pos_forall_prod_div_iSup_le (B u.1) (L u.1) (hLFin u hu)
  choose S c hc_pos hS_li hS_le using hloc
  let assemble : ((p : P) → ι → Dual F (ι → F)) → AbsoluteValue K ℝ → ι → Dual F (ι → F) :=
    fun f v ↦ if h : ∃ p : P, abv p = v then f h.choose else fun i ↦ LinearMap.proj i
  have hassemble : ∀ f (p : P), assemble f (abv p) = f p := fun f p ↦ by
    have h : ∃ q : P, abv q = abv p := ⟨p, rfl⟩
    simp only [assemble, dite_eq_left h]
    exact congrArg f (habv h.choose_spec)
  let cInf : InfinitePlace K → ℝ := fun v ↦ if hv : v ∈ Sinf then c (.inl ⟨v, hv⟩) else 1
  let cFin : FinitePlace K → ℝ := fun u ↦ if hu : u ∈ Sfin then c (.inr ⟨u, hu⟩) else 1
  have hcInf_pos : ∀ v ∈ Sinf, 0 < cInf v := fun v hv ↦ by
    simp only [cInf, dite_eq_left hv]; exact hc_pos _
  have hcFin_pos : ∀ u ∈ Sfin, 0 < cFin u := fun u hu ↦ by
    simp only [cFin, dite_eq_left hu]; exact hc_pos _
  let C : ℝ := (∏ v ∈ Sinf, cInf v ^ v.mult) * ∏ u ∈ Sfin, cFin u
  have hC_pos : 0 < C :=
    mul_pos (Finset.prod_pos fun v hv ↦ pow_pos (hcInf_pos v hv) _) (Finset.prod_pos hcFin_pos)
  refine ⟨(Fintype.piFinset S).image assemble, C, hC_pos, ?_, fun x hx ↦ ?_⟩
  · rintro _ hM
    rcases Finset.mem_image.mp hM with ⟨f, hf, rfl⟩
    rw [Fintype.mem_piFinset] at hf
    exact ⟨fun v hv ↦ hassemble f (.inl ⟨v, hv⟩) ▸ hS_li _ _ (hf _),
      fun u hu ↦ hassemble f (.inr ⟨u, hu⟩) ▸ hS_li _ _ (hf _)⟩
  · choose f hf_mem hf_le using fun p : P ↦ hS_le p x hx
    refine ⟨assemble f, Finset.mem_image_of_mem assemble (Fintype.mem_piFinset.mpr hf_mem),
      approxProd_le_mul_generalProd_of_forall (fun v hv ↦ (hcInf_pos v hv).le) ?_ ?_⟩
    · intro v hv
      have h : assemble f v.1 = f (.inl ⟨v, hv⟩) := hassemble f (.inl ⟨v, hv⟩)
      rw [h]
      simp only [cInf, dite_eq_left hv]
      exact hf_le (.inl ⟨v, hv⟩)
    · intro u hu
      have h : assemble f u.1 = f (.inr ⟨u, hu⟩) := hassemble f (.inr ⟨u, hu⟩)
      rw [h]
      simp only [cFin, dite_eq_left hu]
      exact hf_le (.inr ⟨u, hu⟩)

/-- **Reduction of the general-position Subspace Theorem inequality to linearly independent
systems** (Vojta 1987; Bombieri–Gubler, Theorem 7.2.9). In dimension at least `2`, given `ε > 0`
and finite families of linear forms in general position at the places of `Sinf` and `Sfin`, there
exist finitely many proper subspaces `U` of `ι → K` and finitely many systems `M` of linearly
independent forms at those places such that every nonzero solution of
`generalProd Sinf Sfin w B L x ≤ mulHeight x ^ (-card ι - ε)` either lies in some `W ∈ U` or
satisfies `approxProd Sinf Sfin w M x ≤ mulHeight x ^ (-card ι - ε / 2)` for some `M ∈ T`. -/
theorem exists_finset_submodule_or_approxProd_le_of_generalProd_le [Fintype ι] [Nontrivial ι]
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (B : AbsoluteValue K ℝ → Finset κ)
    (L : AbsoluteValue K ℝ → κ → Dual F (ι → F))
    (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (hLInf : ∀ v ∈ Sinf, Dual.IsGeneralPosition fun k : B v.1 ↦ L v.1 k)
    (hLFin : ∀ v ∈ Sfin, Dual.IsGeneralPosition fun k : B v.1 ↦ L v.1 k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (U : Finset (Submodule K (ι → K))) (T : Finset (AbsoluteValue K ℝ → ι → Dual F (ι → F))),
      (∀ W ∈ U, W ≠ ⊤) ∧
      (∀ M ∈ T, (∀ v ∈ Sinf, LinearIndependent F (M v.1)) ∧
        ∀ v ∈ Sfin, LinearIndependent F (M v.1)) ∧
      ∀ x : ι → K, x ≠ 0 →
        generalProd Sinf Sfin w B L x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) →
        (∃ W ∈ U, x ∈ W) ∨
          ∃ M ∈ T, approxProd Sinf Sfin w M x ≤ mulHeight x ^ (-(Fintype.card ι : ℝ) - ε / 2) := by
  obtain ⟨T, C, hC_pos, hT_li, hT_le⟩ :=
    exists_finset_pos_forall_approxProd_le_mul_generalProd Sinf Sfin w B L hwInf hwFin hLInf hLFin
  let R : ℝ := (max C 1) ^ (2 / ε)
  obtain ⟨U, hU_prop, hU_cov⟩ := Height.exists_finset_submodule_of_mulHeight_le (K := K) (ι := ι) R
  refine ⟨U, T, hU_prop, hT_li, fun x hx hgen ↦ ?_⟩
  by_cases hR : mulHeight x ≤ R
  · exact Or.inl (hU_cov x hx hR)
  · push Not at hR
    obtain ⟨M, hMT, hM⟩ := hT_le x hx
    refine Or.inr ⟨M, hMT, ?_⟩
    have hH_pos : 0 < mulHeight x := Height.mulHeight_pos x
    have hC1_nonneg : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right C 1)
    have hCR : C ≤ R ^ (ε / 2) := by
      have hpow : R ^ (ε / 2) = max C 1 := by
        rw [← Real.rpow_mul hC1_nonneg]
        have hmul : (2 / ε) * (ε / 2) = 1 := by field_simp
        rw [hmul, Real.rpow_one]
      rw [hpow]
      exact le_max_left C 1
    have hC_le : C ≤ mulHeight x ^ (ε / 2) :=
      hCR.trans (Real.rpow_le_rpow (by positivity) hR.le (by positivity))
    calc approxProd Sinf Sfin w M x
        ≤ C * generalProd Sinf Sfin w B L x := hM
      _ ≤ C * mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) :=
          mul_le_mul_of_nonneg_left hgen hC_pos.le
      _ ≤ mulHeight x ^ (ε / 2) * mulHeight x ^ (-(Fintype.card ι : ℝ) - ε) :=
          mul_le_mul_of_nonneg_right hC_le (by positivity)
      _ = mulHeight x ^ (ε / 2 + (-(Fintype.card ι : ℝ) - ε)) :=
          (Real.rpow_add hH_pos _ _).symm
      _ = mulHeight x ^ (-(Fintype.card ι : ℝ) - ε / 2) := by ring_nf

end Global

/-! ### Examples -/

/-- Over `ℚ` at the archimedean place, the general approximation product of the three binary forms
`X₀`, `X₁`, and `X₀ + X₁` evaluated at `(2, -1)` is `1 / 4`. -/
example :
    generalProd {Rat.infinitePlace} ∅ id (fun _ ↦ Finset.univ)
      (fun _ (o : Option (Fin 2)) ↦
        o.elim (LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 0 + LinearMap.proj 1)
          LinearMap.proj)
      ![(2 : ℚ), -1] = 1 / 4 := by
  have hsup : (⨆ j : Fin 2, Rat.infinitePlace (![(2 : ℚ), -1] j)) = 2 := by
    refine le_antisymm (ciSup_le fun j ↦ ?_) ?_
    · fin_cases j <;> norm_num [Rat.infinitePlace_apply]
    · have h0 := le_ciSup (f := fun j : Fin 2 ↦ Rat.infinitePlace (![(2 : ℚ), -1] j))
        (Finite.bddAbove_range _) 0
      simpa [Rat.infinitePlace_apply] using h0
  rw [generalProd_def]
  simp only [Finset.prod_singleton, Finset.prod_empty, mul_one, id_eq,
    Rat.isReal_infinitePlace.mult_eq_one, pow_one, Algebra.algebraMap_self, RingHom.id_apply, hsup]
  rw [Fintype.prod_option, Fin.prod_univ_two]
  simp only [Option.elim_none, Option.elim_some, LinearMap.add_apply, LinearMap.proj_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ← InfinitePlace.coe_apply,
    Rat.infinitePlace_apply]
  norm_num

/-- A single nonzero binary linear form over `ℚ` satisfies an eventual lower bound of order `n⁻¹`
(or `1`, when its second coefficient is nonzero) along `(1, n)`. -/
private theorem exists_nat_pos_le_rat_infinitePlace_linearForm {f : Dual ℚ (Fin 2 → ℚ)}
    (hf : f ≠ 0) :
    ∃ (N : ℕ) (c : ℝ), 0 < c ∧
      (f ![0, 1] = 0 → ∀ n : ℕ, 1 ≤ n →
        c / (n : ℝ) ≤ Rat.infinitePlace (f ![1, (n : ℚ)]) / (n : ℝ)) ∧
      (f ![0, 1] ≠ 0 → ∀ n : ℕ, N ≤ n →
        c ≤ Rat.infinitePlace (f ![1, (n : ℚ)]) / (n : ℝ)) := by
  have heval : ∀ n : ℕ, f ![1, (n : ℚ)] = f ![1, 0] + (n : ℚ) * f ![0, 1] := fun n ↦ by
    have hvec : ![(1 : ℚ), (n : ℚ)] = ![1, 0] + (n : ℚ) • ![0, 1] := by
      ext j; fin_cases j <;> simp
    rw [hvec, map_add, map_smul, smul_eq_mul]
  by_cases hb : f ![0, 1] = 0
  · have ha : f ![1, 0] ≠ 0 := by
      intro ha
      apply hf
      apply LinearMap.ext
      intro y
      have hy : y = y 0 • ![1, 0] + y 1 • ![0, 1] := by ext j; fin_cases j <;> simp
      rw [hy, map_add, map_smul, map_smul, ha, hb]; simp
    refine ⟨1, |(f ![1, 0] : ℝ)|, by exact_mod_cast abs_pos.mpr ha, fun _ n _ ↦ ?_,
      fun h ↦ (h hb).elim⟩
    rw [heval, hb, mul_zero, add_zero, Rat.infinitePlace_apply, Rat.cast_abs]
  · obtain ⟨N, hN⟩ := exists_nat_gt (2 * |(f ![1, 0] : ℝ)| / |(f ![0, 1] : ℝ)|)
    have hb_pos : (0 : ℝ) < |(f ![0, 1] : ℝ)| := by exact_mod_cast abs_pos.mpr hb
    refine ⟨max N 1, |(f ![0, 1] : ℝ)| / 2, by positivity, fun h ↦ (hb h).elim, fun _ n hn ↦ ?_⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right N 1) hn
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left N 1) hn
    have hgt : 2 * |(f ![1, 0] : ℝ)| < (n : ℝ) * |(f ![0, 1] : ℝ)| := by
      have := (div_lt_iff₀ hb_pos).mp (lt_of_lt_of_le hN hnN)
      linarith
    rw [heval, Rat.infinitePlace_apply, le_div_iff₀ (by positivity)]
    push_cast
    have htri : |(f ![0, 1] : ℝ)| * (n : ℝ) - |(f ![1, 0] : ℝ)| ≤
        |(f ![1, 0] : ℝ) + (n : ℝ) * (f ![0, 1] : ℝ)| := by
      have := abs_sub_abs_le_abs_add ((n : ℝ) * (f ![0, 1] : ℝ)) (f ![1, 0] : ℝ)
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n), add_comm, mul_comm] at this
      exact this
    linarith

/-- Any linearly independent pair of binary forms over `ℚ` has normalized archimedean product
bounded below by `δ / n` for all sufficiently large `n` along `(1, n)`. -/
private theorem exists_nat_pos_le_prod_rat_infinitePlace {l : Fin 2 → Dual ℚ (Fin 2 → ℚ)}
    (hl : LinearIndependent ℚ l) :
    ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧ ∀ n : ℕ, N ≤ n →
      δ / (n : ℝ) ≤
        (Rat.infinitePlace (l 0 ![1, (n : ℚ)]) / (n : ℝ)) *
          (Rat.infinitePlace (l 1 ![1, (n : ℚ)]) / (n : ℝ)) := by
  choose N c hc_pos hzero hnz using fun i : Fin 2 ↦
    exists_nat_pos_le_rat_infinitePlace_linearForm (hl.ne_zero i)
  have hnotboth : l 0 ![0, 1] ≠ 0 ∨ l 1 ![0, 1] ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : LinearMap.pi l ![(0 : ℚ), 1] = LinearMap.pi l 0 := by
      ext i; fin_cases i <;> simp [h]
    have := congrFun (hl.pi_bijective.1 h0) 1
    norm_num at this
  refine ⟨max (max (N 0) (N 1)) 1, c 0 * c 1, mul_pos (hc_pos 0) (hc_pos 1), fun n hn ↦ ?_⟩
  have hn0 : N 0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : N 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn_ge1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn_pos : (0 : ℝ) < n := by positivity
  have h1_le_n : (1 : ℝ) ≤ n := by exact_mod_cast hn_ge1
  have h0_bound : ∀ i : Fin 2, N i ≤ n →
      c i / (n : ℝ) ≤ Rat.infinitePlace (l i ![1, (n : ℚ)]) / (n : ℝ) := fun i hni ↦ by
    by_cases hb : l i ![0, 1] = 0
    · exact hzero i hb n hn_ge1
    · exact (div_le_self (hc_pos i).le h1_le_n).trans (hnz i hb n hni)
  have hnonneg : ∀ i : Fin 2, 0 ≤ Rat.infinitePlace (l i ![1, (n : ℚ)]) / (n : ℝ) := fun i ↦
    div_nonneg (AbsoluteValue.nonneg _ _) hn_pos.le
  rcases hnotboth with hb0 | hb1
  · calc c 0 * c 1 / (n : ℝ)
        = c 0 * (c 1 / (n : ℝ)) := by ring
      _ ≤ (Rat.infinitePlace (l 0 ![1, (n : ℚ)]) / (n : ℝ)) *
            (Rat.infinitePlace (l 1 ![1, (n : ℚ)]) / (n : ℝ)) :=
          mul_le_mul (hnz 0 hb0 n hn0) (h0_bound 1 hn1)
            (div_nonneg (hc_pos 1).le hn_pos.le) (hnonneg 0)
  · calc c 0 * c 1 / (n : ℝ)
        = (c 0 / (n : ℝ)) * c 1 := by ring
      _ ≤ (Rat.infinitePlace (l 0 ![1, (n : ℚ)]) / (n : ℝ)) *
            (Rat.infinitePlace (l 1 ![1, (n : ℚ)]) / (n : ℝ)) :=
          mul_le_mul (h0_bound 0 hn0) (hnz 1 hb1 n hn1) (hc_pos 1).le (hnonneg 0)

/-- General position cannot be dropped from
`exists_finset_pos_forall_approxProd_le_mul_generalProd`: for the dependent pair `![X₀, X₀]` on
`ℚ²` at the archimedean place, `generalProd` decays like `n⁻²` along `(1, n)`, whereas every
linearly independent pair of forms has `approxProd` bounded below by a positive multiple of
`n⁻¹`. -/
example :
    ¬ ∃ (T : Finset (AbsoluteValue ℚ ℝ → Fin 2 → Dual ℚ (Fin 2 → ℚ))) (C : ℝ),
      0 < C ∧
      (∀ M ∈ T, LinearIndependent ℚ (M Rat.infinitePlace.1)) ∧
      ∀ x : Fin 2 → ℚ, x ≠ 0 → ∃ M ∈ T,
        approxProd {Rat.infinitePlace} ∅ id M x ≤
          C * generalProd {Rat.infinitePlace} ∅ id (fun _ ↦ Finset.univ)
            (fun _ ↦ ![LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 0, LinearMap.proj 0])
            x := by
  rintro ⟨T, C, _, hT_li, hT_le⟩
  choose N δ hδ_pos hδ_le using fun M : T ↦
    exists_nat_pos_le_prod_rat_infinitePlace (hT_li M.1 M.2)
  let δ₀ : ℝ := (1 + ∑ M : T, (δ M)⁻¹)⁻¹
  have hsum : 0 ≤ ∑ M : T, (δ M)⁻¹ := Finset.sum_nonneg fun M _ ↦ inv_nonneg.mpr (hδ_pos M).le
  have hδ₀_pos : 0 < δ₀ := inv_pos.mpr (by linarith)
  obtain ⟨m, hm⟩ := exists_nat_gt (C / δ₀)
  let n : ℕ := max (max (Finset.univ.sup N) m) 1
  have hn_pos : (0 : ℝ) < n := by have : 1 ≤ n := le_max_right _ _; positivity
  have hsup : (⨆ j : Fin 2, Rat.infinitePlace (![(1 : ℚ), (n : ℚ)] j)) = (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_max_right (max (Finset.univ.sup N) m) 1
    refine le_antisymm (ciSup_le fun j ↦ by fin_cases j <;> simp [Rat.infinitePlace_apply, hn1]) ?_
    simpa [Rat.infinitePlace_apply] using le_ciSup
      (f := fun j : Fin 2 ↦ Rat.infinitePlace (![(1 : ℚ), (n : ℚ)] j)) (Finite.bddAbove_range _) 1
  obtain ⟨M, hMT, hM⟩ := hT_le ![(1 : ℚ), (n : ℚ)] fun h ↦ by
    have := congrFun h 0; norm_num at this
  have hδ₀_le : δ₀ ≤ δ ⟨M, hMT⟩ := by
    have h1 : (δ ⟨M, hMT⟩)⁻¹ ≤ ∑ M' : T, (δ M')⁻¹ :=
      Finset.single_le_sum (fun M' _ ↦ inv_nonneg.mpr (hδ_pos M').le) (Finset.mem_univ _)
    have hle : (δ ⟨M, hMT⟩)⁻¹ ≤ 1 + ∑ M' : T, (δ M')⁻¹ := by linarith
    simpa [δ₀] using inv_anti₀ (inv_pos.mpr (hδ_pos ⟨M, hMT⟩)) hle
  have hN_le : N ⟨M, hMT⟩ ≤ n :=
    le_trans (le_trans (Finset.le_sup (Finset.mem_univ _)) (le_max_left _ _)) (le_max_left _ _)
  have hlow : δ₀ / (n : ℝ) ≤ approxProd {Rat.infinitePlace} ∅ id M ![(1 : ℚ), (n : ℚ)] := by
    simp only [approxProd_def, Finset.prod_singleton, Finset.prod_empty, mul_one, id_eq,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one, Algebra.algebraMap_self, RingHom.id_apply,
      hsup, Fin.prod_univ_two]
    exact (div_le_div_of_nonneg_right hδ₀_le hn_pos.le).trans (hδ_le ⟨M, hMT⟩ n hN_le)
  have hgen : generalProd {Rat.infinitePlace} ∅ id (fun _ ↦ Finset.univ)
      (fun _ ↦ ![LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 0, LinearMap.proj 0])
      ![(1 : ℚ), (n : ℚ)] = (1 / (n : ℝ)) * (1 / (n : ℝ)) := by
    simp only [generalProd_def, Finset.prod_singleton, Finset.prod_empty, mul_one, id_eq,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one, Algebra.algebraMap_self, RingHom.id_apply,
      hsup, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      LinearMap.proj_apply, ← InfinitePlace.coe_apply, Rat.infinitePlace_apply]
    norm_num
  have hcontra : δ₀ / (n : ℝ) ≤ C * ((1 / (n : ℝ)) * (1 / (n : ℝ))) := hlow.trans (hgen ▸ hM)
  have hmn : (m : ℝ) ≤ n := by
    exact_mod_cast le_trans (le_max_right (Finset.univ.sup N) m) (le_max_left _ _)
  have hC_lt : C < δ₀ * (n : ℝ) := by
    have := (div_lt_iff₀ hδ₀_pos).mp (lt_of_lt_of_le hm hmn); linarith
  have h1 := mul_le_mul_of_nonneg_right hcontra (sq_nonneg (n : ℝ))
  field_simp at h1; linarith

end NumberField
