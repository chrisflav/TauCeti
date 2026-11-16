/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.BetaGamma.Grading
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Order.WellQuasiOrder

/-!
# Bigraded character and Euler product identity of the beta-gamma Fock space

For a finite index set `ι` and nontrivial commutative ring `R`, the canonical root-weight
assignment `i ↦ Pi.single i 1 : ι → ℤ` (`TauCeti.BetaGamma.canonicalWeight`) refines the conformal
grading on `TauCeti.BetaGamma.Fock R ι` into finite-rank bigraded weight spaces
`biGradedSubmodule R canonicalWeight (d, w)`.

We package their ranks into the formal bigraded character
`TauCeti.BetaGamma.character R ι S : PowerSeries (HahnSeries (ι → ℤ) S)`, where `PowerSeries.X`
tracks the conformal degree `q` and `HahnSeries.single (Pi.single i 1) 1` tracks `e^{-α_i}` (so
`HahnSeries.single (-Pi.single i 1) 1` tracks `e^{α_i}`, and the support at each fixed degree `d`
is bounded below by `-d` in every coordinate, hence partially well-ordered). We prove the exact
product identity modulo every `q^{N + 1}`
(`TauCeti.BetaGamma.coeff_character_mul_characterEulerFactor`):

`ch(M) · ∏_{i ∈ ι} ((1 - e^{-α_i}) ∏_{n=1}^N (1 - e^{α_i} q^n)(1 - e^{-α_i} q^n))`
is congruent to `1` modulo `q^{N + 1}`.

We also record explicit low-degree rank-one dimension checks
(`finrank_biGradedSubmodule_unit_zero`, `_unit_one_pos`, `_unit_one_zero`, `_unit_one_neg_one`).

## Main definitions

* `TauCeti.BetaGamma.canonicalWeight`: the canonical free-lattice weight assignment
  `i ↦ Pi.single i 1 : ι → ℤ`.
* `TauCeti.BetaGamma.characterCoeff`, `TauCeti.BetaGamma.character`: the formal bigraded character
  in `PowerSeries (HahnSeries (ι → ℤ) S)`.
* `TauCeti.BetaGamma.characterEulerFactor`: the truncated Euler product up to conformal degree `N`.

## Main results

* `TauCeti.BetaGamma.coeff_character_mul_characterEulerFactor`: exact bigraded character product
  identity modulo `q^{N + 1}`.
* `TauCeti.BetaGamma.finrank_biGradedSubmodule_unit_zero`,
  `TauCeti.BetaGamma.finrank_biGradedSubmodule_unit_one_pos`,
  `TauCeti.BetaGamma.finrank_biGradedSubmodule_unit_one_zero`,
  `TauCeti.BetaGamma.finrank_biGradedSubmodule_unit_one_neg_one`: explicit rank-one weight-space
  dimensions.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §5.4.1, pp. 142–143.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §11.3.
-/

public section

noncomputable section

open Finset

namespace TauCeti.BetaGamma

variable {ι : Type*}

/-! ### Canonical root-weight assignment and bigraded character -/

/-- Canonical free-lattice root-weight assignment `i ↦ Pi.single i 1 : ι → ℤ`. -/
def canonicalWeight [DecidableEq ι] (i : ι) : ι → ℤ :=
  Pi.single i 1

@[simp]
theorem canonicalWeight_apply [DecidableEq ι] (i j : ι) :
    canonicalWeight i j = if j = i then 1 else 0 := by
  simp [canonicalWeight, Pi.single_apply]

private theorem canonicalWeight_height [Finite ι] [DecidableEq ι] :
    ∃ ht : (ι → ℤ) →+ ℤ, ∀ i : ι, 0 < ht (canonicalWeight i) := by
  cases nonempty_fintype ι
  refine ⟨AddMonoidHom.mk' (fun f : ι → ℤ ↦ ∑ j : ι, f j) (fun f g ↦ sum_add_distrib), fun i ↦ ?_⟩
  simp [canonicalWeight]

private theorem biWeight_canonical_lower_bound [DecidableEq ι] {e : Var ι →₀ ℕ} {d : ℕ}
    {ν : ι → ℤ} (he : Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)) :
    ∀ i : ι, -(d : ℤ) ≤ ν i := by
  have hd : Finsupp.weight conformalWeight e = d := by simpa using congrArg Prod.fst he
  have hν : Finsupp.weight (rootWeight (canonicalWeight (ι := ι))) e = -ν := by
    simpa using congrArg Prod.snd he
  intro i
  have hle : Finsupp.weight (rootWeight (canonicalWeight (ι := ι))) e i ≤ (d : ℤ) := by
    have hsum : Finsupp.weight (rootWeight (canonicalWeight (ι := ι))) e i =
        ∑ u ∈ e.support, (e u : ℤ) * rootWeight canonicalWeight u i := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine sum_congr rfl fun u _ ↦ ?_
      simp
    rw [hsum]
    calc
      ∑ u ∈ e.support, (e u : ℤ) * rootWeight canonicalWeight u i
        ≤ ∑ u ∈ e.support, ((e u * conformalWeight u : ℕ) : ℤ) := by
          refine sum_le_sum fun u _ ↦ ?_
          cases u with
          | beta j k =>
            by_cases hij : i = j
            · subst hij
              simpa [canonicalWeight] using
                (show (e (Var.beta i k) : ℤ) ≤ ((e (Var.beta i k) * (k + 1) : ℕ) : ℤ) by
                  exact_mod_cast Nat.le_mul_of_pos_right _ (Nat.succ_pos k))
            · simp [canonicalWeight, Pi.single_eq_of_ne hij]
          | gamma j k =>
            have h1 : (e (Var.gamma j k) : ℤ) * (-canonicalWeight j i) ≤ 0 := by
              by_cases hij : i = j
              · subst hij; simp [canonicalWeight]
              · simp [canonicalWeight, Pi.single_eq_of_ne hij]
            have h2 : (0 : ℤ) ≤ ((e (Var.gamma j k) * k : ℕ) : ℤ) := Nat.cast_nonneg _
            simpa using le_trans h1 h2
      _ = (d : ℤ) := by exact_mod_cast hd
  have hneg : -ν i ≤ (d : ℤ) := by simpa [hν] using hle
  omega

private theorem isPWO_of_bddBelow_const [Finite ι] (d : ℕ) {s : Set (ι → ℤ)}
    (hs : ∀ ν ∈ s, ∀ i : ι, -(d : ℤ) ≤ ν i) : s.IsPWO := by
  let f : (ι → ℕ) → (ι → ℤ) := fun g i ↦ (g i : ℤ) - d
  have hf : Monotone f := fun g₁ g₂ h i ↦ by
    have : (g₁ i : ℤ) ≤ (g₂ i : ℤ) := Nat.cast_le.mpr (h i)
    dsimp [f]
    omega
  have hpwo : (f '' Set.univ).IsPWO :=
    (Set.isPWO_of_wellQuasiOrderedLE (Set.univ : Set (ι → ℕ))).image_of_monotone hf
  refine hpwo.mono fun ν hν ↦ ?_
  refine ⟨fun i ↦ (ν i + d).toNat, Set.mem_univ _, funext fun i ↦ ?_⟩
  have hi := hs ν hν i
  dsimp [f]
  omega

/-- The `d`-th degree slice of the bigraded character as a Hahn series in `ι → ℤ`, where
`HahnSeries.single (Pi.single i 1) 1` represents `e^{-α_i}`. -/
def characterCoeff (R : Type*) [CommRing R] [Nontrivial R] (ι : Type*) [Finite ι]
    [DecidableEq ι] (S : Type*) [Semiring S] (d : ℕ) : HahnSeries (ι → ℤ) S where
  coeff ν := (Module.finrank R (biGradedSubmodule R (canonicalWeight (ι := ι)) (d, -ν)) : S)
  isPWO_support' := by
    refine isPWO_of_bddBelow_const d fun ν hν ↦ ?_
    have hne : Module.finrank R (biGradedSubmodule R (canonicalWeight (ι := ι)) (d, -ν)) ≠ 0 :=
      fun h0 ↦ hν (by simp [h0])
    rw [finrank_biGradedSubmodule] at hne
    obtain ⟨⟨e, he⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
    exact biWeight_canonical_lower_bound he

@[simp]
theorem coeff_characterCoeff (R : Type*) [CommRing R] [Nontrivial R] (ι : Type*) [Finite ι]
    [DecidableEq ι] (S : Type*) [Semiring S] (d : ℕ) (ν : ι → ℤ) :
    (characterCoeff R ι S d).coeff ν =
      (Module.finrank R (biGradedSubmodule R (canonicalWeight (ι := ι)) (d, -ν)) : S) := (rfl)

/-- **The formal bigraded character** of `Fock R ι` in `PowerSeries (HahnSeries (ι → ℤ) S)`.
The `q^d` coefficient is `characterCoeff R ι S d`, whose coefficient at `ν` is the rank of the
bigraded weight space `(d, -ν)` (so `single (Pi.single i 1) 1` tracks `e^{-α_i}`). -/
def character (R : Type*) [CommRing R] [Nontrivial R] (ι : Type*) [Finite ι] [DecidableEq ι]
    (S : Type*) [Semiring S] : PowerSeries (HahnSeries (ι → ℤ) S) :=
  PowerSeries.mk (characterCoeff R ι S)

@[simp]
theorem coeff_character (R : Type*) [CommRing R] [Nontrivial R] (ι : Type*) [Finite ι]
    [DecidableEq ι] (S : Type*) [Semiring S] (d : ℕ) :
    PowerSeries.coeff d (character R ι S) = characterCoeff R ι S d :=
  PowerSeries.coeff_mk d _

/-- The truncated Euler denominator up to conformal degree `N`:
`∏_{i ∈ ι} ((1 - e^{-α_i}) ∏_{n = 1}^N (1 - e^{α_i} q^n)(1 - e^{-α_i} q^n))`. -/
def characterEulerFactor (ι : Type*) [Fintype ι] [DecidableEq ι] (S : Type*) [CommRing S]
    (N : ℕ) : PowerSeries (HahnSeries (ι → ℤ) S) :=
  ∏ i : ι, ((1 - PowerSeries.C (HahnSeries.single (Pi.single i 1) (1 : S))) *
    ∏ n ∈ Finset.Icc 1 N,
      ((1 - PowerSeries.C (HahnSeries.single (-Pi.single i 1) (1 : S)) * PowerSeries.X ^ n) *
       (1 - PowerSeries.C (HahnSeries.single (Pi.single i 1) (1 : S)) * PowerSeries.X ^ n)))

/-! ### Exact Euler product identity -/

section CharacterProof

variable [DecidableEq ι] (S : Type*) [CommRing S]

private def varFactor (v : Var ι) : PowerSeries (HahnSeries (ι → ℤ) S) :=
  1 - PowerSeries.C (HahnSeries.single (-rootWeight canonicalWeight v) (1 : S)) *
    PowerSeries.X ^ conformalWeight v

private def seriesOnCoeff [Finite ι] (T : Finset (Var ι)) (d : ℕ) : HahnSeries (ι → ℤ) S where
  coeff ν :=
    (Nat.card {e : Var ι →₀ ℕ //
      e.support ⊆ T ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)} : S)
  isPWO_support' := by
    refine isPWO_of_bddBelow_const d fun ν hν ↦ ?_
    have hne : Nat.card {e : Var ι →₀ ℕ //
        e.support ⊆ T ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)} ≠ 0 :=
      fun h0 ↦ hν (by simp [h0])
    obtain ⟨⟨e, _, he⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
    exact biWeight_canonical_lower_bound he

private theorem coeff_seriesOnCoeff [Finite ι] (T : Finset (Var ι)) (d : ℕ) (ν : ι → ℤ) :
    (seriesOnCoeff S T d).coeff ν =
      (Nat.card {e : Var ι →₀ ℕ //
        e.support ⊆ T ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)} : S) :=
  rfl

private def seriesOn [Finite ι] (T : Finset (Var ι)) : PowerSeries (HahnSeries (ι → ℤ) S) :=
  PowerSeries.mk (seriesOnCoeff S T)

private theorem finite_fiber_subset [Finite ι] (T : Finset (Var ι)) (d : ℕ) (ν : ι → ℤ) :
    Finite {e : Var ι →₀ ℕ //
      e.support ⊆ T ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)} := by
  obtain ⟨ht, hht⟩ := canonicalWeight_height (ι := ι)
  have hfin := (finite_biWeight_fiber canonicalWeight ht hht d (-ν)).to_subtype
  exact Finite.of_injective (fun x ↦ (⟨x.1, x.2.2⟩ :
      {e : Var ι →₀ ℕ // Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)}))
    fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)

private def insertFiberEquiv (T : Finset (Var ι)) {v : Var ι} (hv : v ∉ T) {d : ℕ}
    (hle : conformalWeight v ≤ d) (ν : ι → ℤ) :
    {e : Var ι →₀ ℕ //
      e.support ⊆ insert v T ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)} ≃
    {e : Var ι →₀ ℕ //
      e.support ⊆ T ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)} ⊕
    {e : Var ι →₀ ℕ // e.support ⊆ insert v T ∧
      Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e =
        (d - conformalWeight v, -(ν - -rootWeight canonicalWeight v))} where
  toFun := fun ⟨e, hsupp, hwt⟩ ↦
    if hev : e v = 0 then
      Sum.inl ⟨e, fun u hu ↦ by
        rcases mem_insert.mp (hsupp hu) with rfl | huT
        · exact absurd hev (Finsupp.mem_support_iff.mp hu)
        · exact huT, hwt⟩
    else
      Sum.inr ⟨e - Finsupp.single v 1, fun u hu ↦
        hsupp (Finsupp.mem_support_iff.mpr fun h0 ↦
          Finsupp.mem_support_iff.mp hu (by simp [h0])), by
        have hle1 : Finsupp.single v 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hev)
        have hadd : Finsupp.weight (biWeight (canonicalWeight (ι := ι)))
            (e - Finsupp.single v 1) + biWeight canonicalWeight v = (d, -ν) := by
          rw [← one_smul ℕ (biWeight canonicalWeight v), ← Finsupp.weight_single, ← map_add,
            tsub_add_cancel_of_le hle1, hwt]
        ext
        · have h1 := congrArg Prod.fst hadd
          simp only [Prod.fst_add, fst_biWeight] at h1
          omega
        · have h2 := congrArg Prod.snd hadd
          simp only [Prod.snd_add, snd_biWeight] at h2
          simp [neg_add_rev, eq_sub_of_add_eq h2, sub_eq_add_neg, add_comm]⟩
  invFun := Sum.elim
    (fun ⟨e, hsupp, hwt⟩ ↦ ⟨e, subset_trans hsupp (subset_insert v T), hwt⟩)
    (fun ⟨e, hsupp, hwt⟩ ↦ ⟨e + Finsupp.single v 1, fun u hu ↦ by
      by_cases huv : u = v
      · subst huv; exact mem_insert_self _ _
      · exact hsupp (Finsupp.mem_support_iff.mpr fun h0 ↦
          Finsupp.mem_support_iff.mp hu (by simp [h0, Ne.symm huv])), by
      rw [map_add, hwt, Finsupp.weight_single, one_smul]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, fst_biWeight]
        omega
      · simp only [Prod.snd_add, snd_biWeight, sub_neg_eq_add, neg_add_rev]
        abel⟩)
  left_inv := fun ⟨e, hsupp, hwt⟩ ↦ by
    by_cases hev : e v = 0
    · simp [hev]
    · simp only [hev, ↓reduceDIte, Sum.elim_inr]
      exact Subtype.ext (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hev)))
  right_inv := fun x ↦ by
    rcases x with ⟨e, hsupp, hwt⟩ | ⟨e, hsupp, hwt⟩
    · have hev : e v = 0 := Finsupp.notMem_support_iff.mp fun hmem ↦ hv (hsupp hmem)
      simp [hev]
    · have hev : (e + Finsupp.single v 1 : Var ι →₀ ℕ) v ≠ 0 := by simp
      simp only [Sum.elim_inr, hev, ↓reduceDIte, Sum.inr.injEq]
      refine Subtype.ext (Finsupp.ext fun u ↦ ?_)
      by_cases huv : u = v <;> simp [huv]

private def insertFiberEquivOfLt (T : Finset (Var ι)) {v : Var ι} {d : ℕ}
    (hlt : d < conformalWeight v) (ν : ι → ℤ) :
    {e : Var ι →₀ ℕ //
      e.support ⊆ insert v T ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)} ≃
    {e : Var ι →₀ ℕ //
      e.support ⊆ T ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)} where
  toFun := fun ⟨e, hsupp, hwt⟩ ↦ ⟨e, fun u hu ↦ by
    rcases mem_insert.mp (hsupp hu) with rfl | huT
    · exfalso
      have hdeg : Finsupp.weight conformalWeight e = d := by simpa using congrArg Prod.fst hwt
      have hle1 : conformalWeight u ≤ Finsupp.weight conformalWeight e := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        exact le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.mp hu)))
          (single_le_sum (f := fun w ↦ e w * conformalWeight w) (fun _ _ ↦ Nat.zero_le _) hu)
      omega
    · exact huT, hwt⟩
  invFun := fun ⟨e, hsupp, hwt⟩ ↦ ⟨e, subset_trans hsupp (subset_insert v T), hwt⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

private theorem seriesOn_empty [Finite ι] : seriesOn S (∅ : Finset (Var ι)) = 1 := by
  refine PowerSeries.ext fun d ↦ HahnSeries.ext (funext fun ν ↦ ?_)
  simp only [seriesOn, PowerSeries.coeff_mk, PowerSeries.coeff_one, coeff_seriesOnCoeff]
  by_cases h : d = 0 ∧ ν = 0
  · obtain ⟨rfl, rfl⟩ := h
    have : Unique {e : Var ι →₀ ℕ //
        e.support ⊆ ∅ ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (0, -0)} :=
      ⟨⟨⟨0, by simp, by ext <;> simp⟩⟩, fun ⟨e, he, _⟩ ↦ Subtype.ext (Finsupp.support_eq_empty.mp
        (Finset.subset_empty.mp he))⟩
    rw [Nat.card_unique]
    simp
  · have : IsEmpty {e : Var ι →₀ ℕ //
        e.support ⊆ ∅ ∧ Finsupp.weight (biWeight (canonicalWeight (ι := ι))) e = (d, -ν)} :=
      ⟨fun ⟨e, he, hwt⟩ ↦ by
        have he0 : e = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp he)
        subst he0
        rw [map_zero] at hwt
        have h1 : (0 : ℕ) = d := congrArg Prod.fst hwt
        have h2 : (0 : ι → ℤ) = -ν := congrArg Prod.snd hwt
        exact h ⟨h1.symm, neg_eq_zero.mp h2.symm⟩⟩
    rw [Nat.card_eq_zero.mpr (Or.inl ‹IsEmpty _›), Nat.cast_zero]
    split_ifs with hd
    · subst hd
      have hν : ν ≠ 0 := fun h0 ↦ h ⟨rfl, h0⟩
      simp [HahnSeries.coeff_one, hν]
    · simp

private theorem seriesOn_insert_mul [Finite ι] (T : Finset (Var ι)) {v : Var ι} (hv : v ∉ T) :
    seriesOn S (insert v T) * varFactor S v = seriesOn S T := by
  refine PowerSeries.ext fun d ↦ HahnSeries.ext (funext fun ν ↦ ?_)
  simp only [varFactor, mul_sub, mul_one, map_sub, ← mul_assoc, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mul_C, seriesOn, PowerSeries.coeff_mk]
  have := finite_fiber_subset (ι := ι) (insert v T) d ν
  have := finite_fiber_subset (ι := ι) T d ν
  by_cases hle : conformalWeight v ≤ d
  · simp only [hle, ↓reduceIte, HahnSeries.coeff_sub, HahnSeries.coeff_mul_single, mul_one,
      coeff_seriesOnCoeff]
    have := finite_fiber_subset (ι := ι) (insert v T) (d - conformalWeight v)
      (ν - -rootWeight canonicalWeight v)
    have hcard := (Nat.card_congr (insertFiberEquiv T hv hle ν)).trans Nat.card_sum
    rw [hcard, Nat.cast_add, add_sub_cancel_right]
  · simp only [hle, ↓reduceIte, sub_zero, coeff_seriesOnCoeff]
    have hcard := Nat.card_congr (insertFiberEquivOfLt T (Nat.lt_of_not_ge hle) ν)
    rw [hcard]

private theorem seriesOn_mul_prod_varFactor [Finite ι] (T : Finset (Var ι)) :
    seriesOn S T * ∏ v ∈ T, varFactor S v = 1 := by
  induction T using Finset.induction with
  | empty => simp [seriesOn_empty]
  | insert v T hv ih =>
    rw [prod_insert hv, ← mul_assoc, seriesOn_insert_mul S T hv, ih]

private def varsUpTo (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℕ) : Finset (Var ι) :=
  univ.biUnion fun i : ι ↦
    insert (Var.gamma i 0)
      ((Finset.Icc 1 N).biUnion fun n ↦ {Var.beta i (n - 1), Var.gamma i n})

private theorem mem_varsUpTo_iff [Fintype ι] {N : ℕ} {v : Var ι} :
    v ∈ varsUpTo ι N ↔ conformalWeight v ≤ N := by
  simp only [varsUpTo, mem_biUnion, mem_univ, true_and, mem_insert, mem_Icc, mem_singleton]
  constructor
  · rintro ⟨i, rfl | ⟨n, ⟨hn1, hnN⟩, rfl | rfl⟩⟩
    · simp
    · simp; omega
    · simp; omega
  · intro hv
    cases v with
    | beta i k =>
      refine ⟨i, Or.inr ⟨k + 1, ⟨by omega, by simpa using hv⟩, Or.inl (by simp)⟩⟩
    | gamma i k =>
      cases k with
      | zero => exact ⟨i, Or.inl rfl⟩
      | succ k => exact ⟨i, Or.inr ⟨k + 1, ⟨by omega, by simpa using hv⟩, Or.inr rfl⟩⟩

private theorem prod_varFactor_varsUpTo [Fintype ι] (N : ℕ) :
    ∏ v ∈ varsUpTo ι N, varFactor S v = characterEulerFactor ι S N := by
  rw [varsUpTo, prod_biUnion]
  · refine prod_congr rfl fun i _ ↦ ?_
    rw [prod_insert]
    · congr 1
      · simp [varFactor, canonicalWeight]
      · rw [prod_biUnion]
        · refine prod_congr rfl fun n hn ↦ ?_
          have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
          rw [prod_pair (by intro h; injection h)]
          simp [varFactor, canonicalWeight, show n - 1 + 1 = n by omega]
        · intro m hm n hn hmn
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro v hv₁ hv₂
          simp only [mem_insert, mem_singleton] at hv₁ hv₂
          rcases hv₁ with rfl | rfl <;> rcases hv₂ with h | h
          · injection h with _ hk
            have := (mem_Icc.mp hm).1; have := (mem_Icc.mp hn).1; omega
          · cases h
          · cases h
          · injection h with _ hk
            exact hmn hk
    · simp only [mem_biUnion, mem_Icc, mem_insert, mem_singleton, not_exists, not_and]
      intro n hn
      rintro (h | h)
      · injection h
      · injection h with _ hk
        have := hn.1; omega
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have hi : v.index = i := by
      simp only [mem_insert, mem_biUnion, mem_Icc, mem_singleton] at hv₁
      rcases hv₁ with rfl | ⟨_, _, rfl | rfl⟩ <;> simp
    have hj : v.index = j := by
      simp only [mem_insert, mem_biUnion, mem_Icc, mem_singleton] at hv₂
      rcases hv₂ with rfl | ⟨_, _, rfl | rfl⟩ <;> simp
    exact hij (hi.symm.trans hj)

end CharacterProof

/-- **Exact bigraded character product formula (Frenkel §5.4.1, p. 143):** for every cutoff `N`
and every conformal degree `d ≤ N`, multiplying `character R ι S` by the truncated Euler product
`characterEulerFactor ι S N` yields `1` in degree `0` and `0` in degrees `1, …, N`. -/
theorem coeff_character_mul_characterEulerFactor (R : Type*) [CommRing R] [Nontrivial R]
    (ι : Type*) [Fintype ι] [DecidableEq ι] (S : Type*) [CommRing S] (N : ℕ) {d : ℕ}
    (hd : d ≤ N) :
    PowerSeries.coeff d (character R ι S * characterEulerFactor ι S N) =
      if d = 0 then 1 else 0 := by
  have hagree : ∀ k ≤ N, PowerSeries.coeff k (character R ι S) =
      PowerSeries.coeff k (seriesOn S (varsUpTo ι N)) := by
    intro k hk
    simp only [coeff_character, seriesOn, PowerSeries.coeff_mk]
    refine HahnSeries.ext (funext fun ν ↦ ?_)
    rw [coeff_characterCoeff, coeff_seriesOnCoeff, finrank_biGradedSubmodule]
    congr 1
    refine Nat.card_congr
      { toFun := fun ⟨e, hwt⟩ ↦ ⟨e, fun v hv ↦ by
          rw [mem_varsUpTo_iff]
          have hdeg : Finsupp.weight conformalWeight e = k := by
            simpa using congrArg Prod.fst hwt
          have hle : conformalWeight v ≤ Finsupp.weight conformalWeight e := by
            rw [Finsupp.weight_apply, Finsupp.sum]
            exact le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero
              (Finsupp.mem_support_iff.mp hv)))
              (single_le_sum (f := fun u ↦ e u * conformalWeight u) (fun _ _ ↦ Nat.zero_le _) hv)
          omega, hwt⟩
        invFun := fun ⟨e, _, hwt⟩ ↦ ⟨e, hwt⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  have hmul : PowerSeries.coeff d (character R ι S * characterEulerFactor ι S N) =
      PowerSeries.coeff d (seriesOn S (varsUpTo ι N) * characterEulerFactor ι S N) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [hagree p.1 (le_trans (le_of_add_le_left (mem_antidiagonal.mp hp).le) hd)]
  rw [hmul, ← prod_varFactor_varsUpTo S N, seriesOn_mul_prod_varFactor S (varsUpTo ι N),
    PowerSeries.coeff_one]

/-! ### Rank-one dimension checks -/

section RankOne

variable (R : Type*) [CommRing R] [Nontrivial R]

private theorem rootWeight_unit_beta (k m : ℕ) :
    Finsupp.weight (rootWeight (canonicalWeight (ι := Unit)))
      (Finsupp.single (Var.beta () k) m) () = (m : ℤ) := by
  simp [Finsupp.weight_single, canonicalWeight]

private theorem rootWeight_unit_gamma (k m : ℕ) :
    Finsupp.weight (rootWeight (canonicalWeight (ι := Unit)))
      (Finsupp.single (Var.gamma () k) m) () = -(m : ℤ) := by
  simp [Finsupp.weight_single, canonicalWeight]

/-- Rank-one degree-zero check: each nonpositive weight `-m` has a one-dimensional weight space
(spanned by `γ_0^m`). -/
theorem finrank_biGradedSubmodule_unit_zero (m : ℕ) :
    Module.finrank R (biGradedSubmodule R (canonicalWeight (ι := Unit)) (0, fun _ ↦ -(m : ℤ))) =
      1 := by
  rw [finrank_biGradedSubmodule]
  have huniq : Unique {e : Var Unit →₀ ℕ //
      Finsupp.weight (biWeight (canonicalWeight (ι := Unit))) e = (0, fun _ ↦ -(m : ℤ))} := by
    refine ⟨⟨⟨Finsupp.single (Var.gamma () 0) m, ?_⟩⟩, fun ⟨e, he⟩ ↦ Subtype.ext ?_⟩
    · ext
      · simp [Finsupp.weight_single]
      · simp [Finsupp.weight_single, canonicalWeight]
    · have hd : Finsupp.weight conformalWeight e = 0 := by simpa using congrArg Prod.fst he
      have hw : Finsupp.weight (rootWeight (canonicalWeight (ι := Unit))) e () = -(m : ℤ) := by
        simpa using congrFun (congrArg Prod.snd he) ()
      have hzero : ∀ v : Var Unit, v ≠ Var.gamma () 0 → e v = 0 := by
        intro v hv
        by_contra hne
        have hpos : 0 < conformalWeight v := by
          cases v with
          | beta _ _ => simp
          | gamma u k => cases u; cases k with | zero => exact absurd rfl hv | succ _ => simp
        have hle : e v * conformalWeight v ≤ Finsupp.weight conformalWeight e := by
          rw [Finsupp.weight_apply, Finsupp.sum]
          exact single_le_sum (f := fun u ↦ e u * conformalWeight u) (fun _ _ ↦ Nat.zero_le _)
            (Finsupp.mem_support_iff.mpr hne)
        have hmul : 0 < e v * conformalWeight v := Nat.mul_pos (Nat.pos_of_ne_zero hne) hpos
        omega
      have he_eq : e = Finsupp.single (Var.gamma () 0) (e (Var.gamma () 0)) := by
        ext v
        by_cases hv : v = Var.gamma () 0
        · subst hv; simp
        · rw [hzero v hv, Finsupp.single_eq_of_ne hv]
      rw [he_eq, rootWeight_unit_gamma] at hw
      have hm : e (Var.gamma () 0) = m := by omega
      rwa [hm] at he_eq
  exact Nat.card_unique

private theorem unit_degree_one_other_eq_zero {e : Var Unit →₀ ℕ}
    (hd : Finsupp.weight conformalWeight e = 1) {v : Var Unit}
    (h1 : v ≠ Var.beta () 0) (h2 : v ≠ Var.gamma () 1) (h3 : v ≠ Var.gamma () 0) :
    e v = 0 := by
  have hge : 2 ≤ conformalWeight v := by
    cases v with
    | beta u k => cases u; cases k with | zero => exact absurd rfl h1 | succ _ => simp
    | gamma u k =>
      cases u; cases k with
      | zero => exact absurd rfl h3
      | succ k => cases k with | zero => exact absurd rfl h2 | succ _ => simp
  by_contra hne
  have hle : e v * conformalWeight v ≤ 1 := by
    rw [← hd, Finsupp.weight_apply, Finsupp.sum]
    exact single_le_sum (f := fun u ↦ e u * conformalWeight u) (fun _ _ ↦ Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr hne)
  have : 2 ≤ e v * conformalWeight v :=
    le_trans hge (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne))
  omega

private theorem unit_degree_one_cases {e : Var Unit →₀ ℕ}
    (hd : Finsupp.weight conformalWeight e = 1) :
    e = Finsupp.single (Var.beta () 0) 1 +
        Finsupp.single (Var.gamma () 0) (e (Var.gamma () 0)) ∨
    e = Finsupp.single (Var.gamma () 1) 1 +
        Finsupp.single (Var.gamma () 0) (e (Var.gamma () 0)) := by
  have hother : ∀ v : Var Unit, v ≠ Var.beta () 0 → v ≠ Var.gamma () 1 → v ≠ Var.gamma () 0 →
      e v = 0 := fun _ h1 h2 h3 ↦ unit_degree_one_other_eq_zero hd h1 h2 h3
  have h12 : Var.beta () 0 ≠ Var.gamma () 1 := by intro h; injection h
  have h13 : Var.beta () 0 ≠ Var.gamma () 0 := by intro h; injection h
  have h23 : Var.gamma () 1 ≠ Var.gamma () 0 := by intro h; injection h with _ h'; omega
  have hsum : e (Var.beta () 0) + e (Var.gamma () 1) = 1 := by
    have hsupp : e.support ⊆ {Var.beta () 0, Var.gamma () 1, Var.gamma () 0} := by
      intro v hv
      simp only [mem_insert, mem_singleton]
      by_contra h
      push Not at h
      exact Finsupp.mem_support_iff.mp hv (hother v h.1 h.2.1 h.2.2)
    have hwt : Finsupp.weight conformalWeight e = e (Var.beta () 0) + e (Var.gamma () 1) := by
      rw [Finsupp.weight_apply, Finsupp.sum,
        sum_subset hsupp fun v _ hv ↦ by simp [Finsupp.notMem_support_iff.mp hv]]
      simp [sum_insert, h12, h13, h23]
    omega
  have hmk : ∀ (u w : Var Unit), u ≠ w → u ≠ Var.gamma () 0 → w ≠ Var.gamma () 0 →
      e u = 1 → e w = 0 →
      (∀ v, v ≠ u → v ≠ w → v ≠ Var.gamma () 0 → e v = 0) →
      e = Finsupp.single u 1 + Finsupp.single (Var.gamma () 0) (e (Var.gamma () 0)) := by
    intro u w huw hu0 hw0 heu hew ho
    ext v
    rw [Finsupp.add_apply]
    by_cases hv1 : v = u
    · subst hv1; rw [heu, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hu0, add_zero]
    · by_cases hv2 : v = Var.gamma () 0
      · subst hv2; rw [Finsupp.single_eq_of_ne hu0.symm, Finsupp.single_eq_same, zero_add]
      · by_cases hv3 : v = w
        · subst hv3
          rw [hew, Finsupp.single_eq_of_ne huw.symm, Finsupp.single_eq_of_ne hw0, add_zero]
        · rw [ho v hv1 hv3 hv2, Finsupp.single_eq_of_ne hv1,
            Finsupp.single_eq_of_ne hv2, add_zero]
  rcases (by omega : (e (Var.beta () 0) = 1 ∧ e (Var.gamma () 1) = 0) ∨
      (e (Var.beta () 0) = 0 ∧ e (Var.gamma () 1) = 1)) with ⟨hb, hg⟩ | ⟨hb, hg⟩
  · exact Or.inl (hmk _ _ h12 h13 h23 hb hg hother)
  · exact Or.inr (hmk _ _ h12.symm h23 h13 hg hb fun v h1 h2 h3 ↦ hother v h2 h1 h3)

/-- Rank-one degree-one check: `(1, +1)` has dimension `1` (spanned by `β_{-1}`). -/
theorem finrank_biGradedSubmodule_unit_one_pos :
    Module.finrank R (biGradedSubmodule R (canonicalWeight (ι := Unit)) (1, fun _ ↦ 1)) = 1 := by
  rw [finrank_biGradedSubmodule]
  have huniq : Unique {e : Var Unit →₀ ℕ //
      Finsupp.weight (biWeight (canonicalWeight (ι := Unit))) e = (1, fun _ ↦ 1)} := by
    refine ⟨⟨⟨Finsupp.single (Var.beta () 0) 1, ?_⟩⟩, fun ⟨e, he⟩ ↦ Subtype.ext ?_⟩
    · ext <;> simp [Finsupp.weight_single, canonicalWeight]
    · have hd : Finsupp.weight conformalWeight e = 1 := by simpa using congrArg Prod.fst he
      have hw : Finsupp.weight (rootWeight (canonicalWeight (ι := Unit))) e () = 1 := by
        simpa using congrFun (congrArg Prod.snd he) ()
      rcases unit_degree_one_cases hd with h | h
      · rw [h, map_add, Pi.add_apply, rootWeight_unit_beta, rootWeight_unit_gamma] at hw
        have h0 : e (Var.gamma () 0) = 0 := by omega
        simpa [h0] using h
      · rw [h, map_add, Pi.add_apply, rootWeight_unit_gamma, rootWeight_unit_gamma] at hw
        omega
  exact Nat.card_unique

/-- Rank-one degree-one check: `(1, 0)` has dimension `1` (spanned by `β_{-1} γ_0`). -/
theorem finrank_biGradedSubmodule_unit_one_zero :
    Module.finrank R (biGradedSubmodule R (canonicalWeight (ι := Unit)) (1, fun _ ↦ 0)) = 1 := by
  rw [finrank_biGradedSubmodule]
  have huniq : Unique {e : Var Unit →₀ ℕ //
      Finsupp.weight (biWeight (canonicalWeight (ι := Unit))) e = (1, fun _ ↦ 0)} := by
    refine ⟨⟨⟨Finsupp.single (Var.beta () 0) 1 + Finsupp.single (Var.gamma () 0) 1, ?_⟩⟩,
      fun ⟨e, he⟩ ↦ Subtype.ext ?_⟩
    · ext <;> simp [map_add, Finsupp.weight_single, canonicalWeight]
    · have hd : Finsupp.weight conformalWeight e = 1 := by simpa using congrArg Prod.fst he
      have hw : Finsupp.weight (rootWeight (canonicalWeight (ι := Unit))) e () = 0 := by
        simpa using congrFun (congrArg Prod.snd he) ()
      rcases unit_degree_one_cases hd with h | h
      · rw [h, map_add, Pi.add_apply, rootWeight_unit_beta, rootWeight_unit_gamma] at hw
        have h1 : e (Var.gamma () 0) = 1 := by omega
        simpa [h1] using h
      · rw [h, map_add, Pi.add_apply, rootWeight_unit_gamma, rootWeight_unit_gamma] at hw
        omega
  exact Nat.card_unique

/-- Rank-one degree-one check: `(1, -1)` has dimension `2` (spanned by `γ_{-1}` and
`β_{-1} γ_0²`). -/
theorem finrank_biGradedSubmodule_unit_one_neg_one :
    Module.finrank R (biGradedSubmodule R (canonicalWeight (ι := Unit)) (1, fun _ ↦ -1)) = 2 := by
  rw [finrank_biGradedSubmodule]
  let e₁ : Var Unit →₀ ℕ := Finsupp.single (Var.beta () 0) 1 + Finsupp.single (Var.gamma () 0) 2
  let e₂ : Var Unit →₀ ℕ := Finsupp.single (Var.gamma () 1) 1
  have he₁ : Finsupp.weight (biWeight (canonicalWeight (ι := Unit))) e₁ = (1, fun _ ↦ -1) := by
    ext <;> simp [e₁, map_add, Finsupp.weight_single, canonicalWeight]
  have he₂ : Finsupp.weight (biWeight (canonicalWeight (ι := Unit))) e₂ = (1, fun _ ↦ -1) := by
    ext <;> simp [e₂, Finsupp.weight_single, canonicalWeight]
  have hne : e₁ ≠ e₂ := fun h ↦ by
    have := congrArg (fun f : Var Unit →₀ ℕ ↦ f (Var.beta () 0)) h
    simp [e₁, e₂] at this
  have hequiv : {e : Var Unit →₀ ℕ //
      Finsupp.weight (biWeight (canonicalWeight (ι := Unit))) e = (1, fun _ ↦ -1)} ≃ Bool :=
    { toFun := fun ⟨e, _⟩ ↦ decide (e = e₁)
      invFun := fun b ↦ if b then ⟨e₁, he₁⟩ else ⟨e₂, he₂⟩
      left_inv := fun ⟨e, he⟩ ↦ by
        have hd : Finsupp.weight conformalWeight e = 1 := by simpa using congrArg Prod.fst he
        have hw : Finsupp.weight (rootWeight (canonicalWeight (ι := Unit))) e () = -1 := by
          simpa using congrFun (congrArg Prod.snd he) ()
        rcases unit_degree_one_cases hd with h | h
        · rw [h, map_add, Pi.add_apply, rootWeight_unit_beta, rootWeight_unit_gamma] at hw
          have h2 : e (Var.gamma () 0) = 2 := by omega
          have heq : e = e₁ := by simpa [e₁, h2] using h
          simp [heq]
        · rw [h, map_add, Pi.add_apply, rootWeight_unit_gamma, rootWeight_unit_gamma] at hw
          have h0 : e (Var.gamma () 0) = 0 := by omega
          have heq : e = e₂ := by simpa [e₂, h0] using h
          simp [heq, hne.symm]
      right_inv := fun b ↦ by cases b <;> simp [hne.symm] }
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_bool]

end RankOne

end TauCeti.BetaGamma
