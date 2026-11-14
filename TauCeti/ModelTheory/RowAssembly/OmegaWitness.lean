/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RowAssembly.BackAndForth
public import TauCeti.ModelTheory.Scott.Height
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.ModelTheory.BackAndForth.PureSet
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.Logic.Equiv.Option

/-!
# A countable structure of internal Scott rank `ω` with a large level-`ω` class

We construct a countably infinite relational structure `BaseAssembly` over the countable relational
vocabulary `omegaLang = RowAssembly.lang (Label ℕ) Language.empty` together with a Cantor-indexed
family of countably infinite companions `CompanionAssembly z` (`z : ℕ → Bool`) such that:

* `internalScottRank (L := omegaLang) BaseAssembly = ω` (`internalScottRank_baseAssembly`);
* for every `z : ℕ → Bool`, the empty tuples of `CompanionAssembly z` and `BaseAssembly` are
  back-and-forth equivalent at level `ω` (`bfEquiv_omega0_companionAssembly`);
* no `CompanionAssembly z` is isomorphic to `BaseAssembly`
  (`isEmpty_equiv_companionAssembly_baseAssembly`), and `CompanionAssembly z` and
  `CompanionAssembly z'` are non-isomorphic whenever `z ≠ z'` (`isEmpty_equiv_companionAssembly`);
* `ω < scottHeight (L := omegaLang) BaseAssembly ≤ ω + ω`
  (`omega0_lt_scottHeight_baseAssembly`, `scottHeight_baseAssembly_le_omega0_add_omega0`).

The rows of `BaseAssembly` are the nondecreasing finite words `p` over `ℕ` satisfying `p[i] ≤ i`
(`AllowedWord`). At row `p` and nonempty word label `τ : Label ℕ`, the fiber `BaseFiber p τ` is the
pure set `Fin (τ.lastVal + 1)` when `τ` is a prefix of `p`, and `ℕ` otherwise. Each companion
`CompanionAssembly z` adjoins a single limit row `none` along the path
`pathVal z (2n) = n`, `pathVal z (2n + 1) = n + (z n).toNat`; at finite depth `m`, a Hilbert-hotel
row bijection (`Equiv.optionOfNatInjective`) shifts the path prefixes from length `2m + 1` onward
to establish `BFEquiv m`.

## References

* Adapted from `InfinitaryLogic/ModelTheory/ScottRankOmegaExample.lean` and
  `InfinitaryLogic/ModelTheory/TreeLimitWitness.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0).
-/

public section

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language
open scoped Ordinal

/-! ### Nonempty word labels and allowed words -/

/-- Nonempty finite words over `U`, used as fiber labels. -/
abbrev Label (U : Type*) : Type _ := {τ : List U // τ ≠ []}

/-- The last entry of a nonempty word over `ℕ`. -/
def Label.lastVal (τ : Label ℕ) : ℕ := τ.1.getLast τ.2

/-- Nondecreasing finite words `p` over `ℕ` satisfying `p[i] ≤ i` at every index `i`. -/
@[ext]
structure AllowedWord : Type where
  /-- The underlying list of natural numbers. -/
  toList : List ℕ
  /-- Entries are nondecreasing. -/
  pairwise_le : toList.Pairwise (· ≤ ·)
  /-- Each entry is bounded by its index. -/
  getElem_le : ∀ (i : ℕ) (hi : i < toList.length), toList[i] ≤ i

instance : Countable AllowedWord :=
  Function.Injective.countable (f := AllowedWord.toList) fun _ _ => AllowedWord.ext

/-- The allowed word `[0, 1, …, k]` of length `k + 1`. -/
def rangeWord (k : ℕ) : AllowedWord where
  toList := List.range (k + 1)
  pairwise_le := List.pairwise_lt_range.imp le_of_lt
  getElem_le i hi := by simp

/-- The allowed word `[0, 1, …, k, k]` of length `k + 2`, duplicating `k` at the end. -/
def rangeDupWord (k : ℕ) : AllowedWord where
  toList := List.range (k + 1) ++ [k]
  pairwise_le := by
    rw [List.pairwise_append]
    refine ⟨List.pairwise_lt_range.imp le_of_lt, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_range] at ha
    rw [List.mem_singleton] at hb
    omega
  getElem_le i hi := by
    rcases lt_or_ge i (k + 1) with hlt | hge
    · rw [List.getElem_append_left (by simpa using hlt)]
      simp
    · rw [List.getElem_append_right (by simpa using hge)]
      simp at hi ⊢
      omega

instance : Infinite AllowedWord :=
  Infinite.of_injective rangeWord fun j k h => by
    have hlen := congrArg (fun w => w.toList.length) h
    simpa [rangeWord] using hlen

/-- Every nonempty prefix `τ` of an allowed word `p` satisfies `τ.lastVal + 1 ≤ p.toList.length`. -/
theorem lastVal_add_one_le_length {p : AllowedWord} {τ : Label ℕ} (hτ : τ.1 <+: p.toList) :
    τ.lastVal + 1 ≤ p.toList.length := by
  have hpos : 0 < τ.1.length := List.length_pos_iff.mpr τ.2
  have hlen : τ.1.length ≤ p.toList.length := hτ.length_le
  obtain ⟨t, ht⟩ := hτ
  have hm : τ.1.length - 1 < p.toList.length := by omega
  have happ : (τ.1 ++ t)[τ.1.length - 1]'(by rw [ht]; exact hm) =
      τ.1[τ.1.length - 1]'(by omega) :=
    List.getElem_append_left (by omega)
  simp only [ht] at happ
  have hlast : τ.lastVal = p.toList[τ.1.length - 1] := by
    rw [Label.lastVal, List.getLast_eq_getElem, happ]
  have hbound := p.getElem_le (τ.1.length - 1) hm
  omega

/-! ### The base row assembly -/

/-- The countable relational vocabulary of the rank-`ω` row assembly. -/
abbrev omegaLang : Language.{0, 0} := lang (Label ℕ) Language.empty

open Classical in
/-- The component pure set of `BaseAssembly` at row `p` and label `τ`: finite of size
`τ.lastVal + 1` when `τ` is a prefix of `p`, and `ℕ` otherwise. -/
def BaseFiber (p : AllowedWord) (τ : Label ℕ) : Type :=
  if τ.1 <+: p.toList then Fin (τ.lastVal + 1) else ℕ

instance (p : AllowedWord) (τ : Label ℕ) : Language.empty.Structure (BaseFiber p τ) :=
  Language.emptyStructure

instance (p : AllowedWord) (τ : Label ℕ) : Countable (BaseFiber p τ) := by
  classical
  unfold BaseFiber
  split_ifs <;> infer_instance

/-- The countable base row assembly of internal Scott rank `ω`. -/
abbrev BaseAssembly : Type := Carrier AllowedWord BaseFiber

/-- When `τ` is a prefix of `p`, the fiber `BaseFiber p τ` has cardinality `τ.lastVal + 1`. -/
theorem baseFiber_of_isPrefix {p : AllowedWord} {τ : Label ℕ} (h : τ.1 <+: p.toList) :
    ENat.card (BaseFiber p τ) = (τ.lastVal + 1 : ℕ) := by
  classical
  simp [BaseFiber, h]

/-- When `τ` is not a prefix of `p`, the fiber `BaseFiber p τ` is countably infinite. -/
theorem baseFiber_of_not_isPrefix {p : AllowedWord} {τ : Label ℕ} (h : ¬ τ.1 <+: p.toList) :
    ENat.card (BaseFiber p τ) = ⊤ := by
  classical
  simp [BaseFiber, h]

/-- A fiber `BaseFiber p τ` is finite if and only if `τ` is a prefix of `p`. -/
theorem finite_baseFiber_iff (p : AllowedWord) (τ : Label ℕ) :
    Finite (BaseFiber p τ) ↔ τ.1 <+: p.toList := by
  classical
  unfold BaseFiber
  split_ifs with h
  · exact iff_of_true inferInstance h
  · exact iff_of_false Infinite.not_finite h

/-! ### Row rigidity and the upper bound `internalScottRank BaseAssembly ≤ ω` -/

private theorem isPrefix_of_forall_bfEquiv_baseFiber {p q : AllowedWord}
    (h : ∀ τ : Label ℕ, BFEquiv (L := Language.empty)
      ((p.toList.length + 2 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → BaseFiber p τ) (Fin.elim0 : Fin 0 → BaseFiber q τ)) :
    p.toList <+: q.toList := by
  set k : ℕ := p.toList.length + 2
  by_cases hp : p.toList = []
  · simp [hp]
  · let τp : Label ℕ := ⟨p.toList, hp⟩
    have hcard := (bfEquiv_empty_elim0_natCast_iff k).mp (h τp)
    rw [baseFiber_of_isPrefix List.prefix_rfl] at hcard
    have hlt : τp.lastVal + 1 < k := by
      have := lastVal_add_one_le_length (p := p) (τ := τp) List.prefix_rfl
      omega
    by_contra hnot
    rw [baseFiber_of_not_isPrefix hnot, min_top_left] at hcard
    have hmin : min ((τp.lastVal + 1 : ℕ) : ℕ∞) (k : ℕ∞) = (τp.lastVal + 1 : ℕ) :=
      min_eq_left (by exact_mod_cast hlt.le)
    rw [hmin] at hcard
    exact hlt.ne (by exact_mod_cast hcard)

private theorem length_le_of_forall_bfEquiv_baseFiber {p q : AllowedWord}
    (h : ∀ τ : Label ℕ, BFEquiv (L := Language.empty)
      ((p.toList.length + 2 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → BaseFiber p τ) (Fin.elim0 : Fin 0 → BaseFiber q τ)) :
    q.toList.length ≤ p.toList.length := by
  set k : ℕ := p.toList.length + 2
  by_contra! hlt
  let l : ℕ := p.toList.length + 1
  have hl_ne : q.toList.take l ≠ [] := by
    simp only [ne_eq, List.take_eq_nil_iff, not_or]
    exact ⟨by omega, List.ne_nil_of_length_pos (by omega)⟩
  let τq : Label ℕ := ⟨q.toList.take l, hl_ne⟩
  have hτq_len : τq.1.length = l := List.length_take_of_le (by omega)
  have hnot_p : ¬ τq.1 <+: p.toList := fun hpre => by
    have := hpre.length_le
    omega
  have hpre_q : τq.1 <+: q.toList := List.take_prefix l q.toList
  have hlast_le : τq.lastVal ≤ p.toList.length := by
    have hlast_eq : τq.lastVal = q.toList[p.toList.length] := by
      rw [Label.lastVal, List.getLast_eq_getElem]
      have hidx : τq.1.length - 1 = p.toList.length := by omega
      simp only [hidx, τq, List.getElem_take]
    exact hlast_eq.trans_le (q.getElem_le p.toList.length hlt)
  have hcard := (bfEquiv_empty_elim0_natCast_iff k).mp (h τq)
  rw [baseFiber_of_not_isPrefix hnot_p, baseFiber_of_isPrefix hpre_q, min_top_left] at hcard
  have hlt_k : τq.lastVal + 1 < k := by omega
  have hmin : min ((τq.lastVal + 1 : ℕ) : ℕ∞) (k : ℕ∞) = (τq.lastVal + 1 : ℕ) :=
    min_eq_left (by exact_mod_cast hlt_k.le)
  rw [hmin] at hcard
  exact hlt_k.ne (by exact_mod_cast hcard.symm)

/-- Each allowed word `p` is uniquely determined among all allowed words `q` by the level-`(|p|+2)`
empty-tuple back-and-forth types of its fibers. -/
theorem eq_of_forall_bfEquiv_baseFiber {p q : AllowedWord}
    (h : ∀ τ : Label ℕ, BFEquiv (L := Language.empty)
      ((p.toList.length + 2 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → BaseFiber p τ) (Fin.elim0 : Fin 0 → BaseFiber q τ)) :
    p = q := by
  obtain ⟨t, ht⟩ := isPrefix_of_forall_bfEquiv_baseFiber h
  have hle := length_le_of_forall_bfEquiv_baseFiber h
  have ht_len : t.length = 0 := by
    have := congrArg List.length ht
    simp at this
    omega
  ext1
  simpa [List.eq_nil_of_length_eq_zero ht_len] using ht

private theorem exists_aut_comp_eq_of_row_eq {n : ℕ} {a b : Fin n → BaseAssembly}
    (h0 : SameAtomicType (L := omegaLang) a b)
    (hrow : ∀ k, ownerRow (a k) = ownerRow (b k)) :
    ∃ Φ : BaseAssembly ≃[omegaLang] BaseAssembly, Φ ∘ a = b := by
  classical
  have hsort (k : Fin n) : sort (a k) = sort (b k) := sort_eq_of_sameAtomicType h0 k
  have hfib (p : AllowedWord) (τ : Label ℕ) :
      ∃ σ : BaseFiber p τ ≃[Language.empty] BaseFiber p τ,
        ∀ (k : Fin n) (u : BaseFiber p τ) (v : BaseFiber p τ),
          a k = .pt p τ u → b k = .pt p τ v → σ u = v := by
    let Idx := {k : Fin n // ownerRow (a k) = p ∧ sort (a k) = some τ}
    have hx (idx : Idx) : ∃ u : BaseFiber p τ, a idx.1 = .pt p τ u :=
      exists_pt_of_sort_eq_some idx.2.1 idx.2.2
    have hy (idx : Idx) : ∃ v : BaseFiber p τ, b idx.1 = .pt p τ v :=
      exists_pt_of_sort_eq_some ((hrow idx.1).symm.trans idx.2.1)
        ((hsort idx.1).symm.trans idx.2.2)
    choose x hx_eq using hx
    choose y hy_eq using hy
    have hxy (i₁ i₂ : Idx) : x i₁ = x i₂ ↔ y i₁ = y i₂ := by
      have heq := h0.eq_iff i₁.1 i₂.1
      rwa [hx_eq i₁, hx_eq i₂, pt_inj_right, hy_eq i₁, hy_eq i₂, pt_inj_right] at heq
    obtain ⟨π, -, hπ⟩ := exists_perm_apply_eq_of_eq_iff (fun _ : BaseFiber p τ => ()) hxy
      (fun _ => rfl)
    refine ⟨StrongHomClass.toEquiv π, fun k u v hau hbv => ?_⟩
    let idx : Idx := ⟨k, by simp [hau], by simp [hau]⟩
    have hu : x idx = u := pt_inj_right.mp ((hx_eq idx).symm.trans hau)
    have hv : y idx = v := pt_inj_right.mp ((hy_eq idx).symm.trans hbv)
    simpa [hu, hv] using hπ idx
  choose eC heC using hfib
  let eC' : ∀ p τ, BaseFiber p τ ≃[Language.empty] BaseFiber (Equiv.refl AllowedWord p) τ := eC
  refine ⟨equivOfFiberEquiv (Equiv.refl AllowedWord) eC', funext fun k => ?_⟩
  cases hak : a k with
  | row p =>
    have hsb : sort (b k) = none := by simpa [hak] using (hsort k).symm
    have hrb : ownerRow (b k) = p := by simpa [hak] using (hrow k).symm
    rw [Function.comp_apply, hak, equivOfFiberEquiv_row, Equiv.refl_apply, ← hrb]
    exact (eq_row_of_sort_eq_none hsb).symm
  | pt p τ u =>
    have hsb : sort (b k) = some τ := by simpa [hak] using (hsort k).symm
    have hrb : ownerRow (b k) = p := by simpa [hak] using (hrow k).symm
    obtain ⟨v, hbv⟩ := exists_pt_of_sort_eq_some hrb hsb
    rw [Function.comp_apply, hak, hbv, equivOfFiberEquiv_pt]
    exact congrArg (Carrier.pt p τ) (heC p τ k u v hak hbv)

/-- Every finite tuple in `BaseAssembly` has finite orbit rank. -/
theorem orbitRank_lt_omega0_baseAssembly {n : ℕ} (a : Fin n → BaseAssembly) :
    orbitRank (L := omegaLang) a < ω := by
  let r : ℕ := Finset.univ.sup fun k : Fin n => (ownerRow (a k)).toList.length
  let N : ℕ := r + 2 + n
  refine (orbitRank_le a ?_).trans_lt (Ordinal.natCast_lt_omega0 N)
  rw [mem_orbitStable_iff_of_countable]
  intro b hab
  have hab_cast : BFEquiv (L := omegaLang) (((r + 2 : ℕ) : Ordinal.{0}) + n) n a b := by
    simpa [N, Nat.cast_add] using hab
  have hab' := bfEquiv_append_ownerRow hab_cast
  refine exists_aut_comp_eq_of_row_eq hab.sameAtomicType fun k => ?_
  apply eq_of_forall_bfEquiv_baseFiber
  intro τ
  have hfib := bfEquiv_elim0_fiber_of_row_eq hab' (p := Fin.natAdd n k)
    (Fin.append_right _ _ k) (Fin.append_right _ _ k) τ
  have hle : (ownerRow (a k)).toList.length + 2 ≤ r + 2 :=
    Nat.add_le_add_right (Finset.le_sup (f := fun j : Fin n => (ownerRow (a j)).toList.length)
      (Finset.mem_univ k)) 2
  exact hfib.mono (Nat.cast_le.mpr hle)

/-- The internal Scott rank of `BaseAssembly` is at most `ω`. -/
theorem internalScottRank_baseAssembly_le_omega0 :
    internalScottRank (L := omegaLang) BaseAssembly ≤ ω :=
  (internalScottRank_le_iff BaseAssembly ω).mpr fun _ a => orbitRank_lt_omega0_baseAssembly a

/-! ### Two-row lower bound and `internalScottRank BaseAssembly = ω` -/

private theorem eq_rangeDupWord_of_prefix {k : ℕ} {τ : Label ℕ}
    (hpre : τ.1 <+: (rangeDupWord k).toList) (hnpre : ¬ τ.1 <+: (rangeWord k).toList) :
    τ.1 = (rangeDupWord k).toList := by
  obtain ⟨t, ht⟩ := hpre
  cases t with
  | nil =>
    simpa using ht
  | cons c ts =>
    exfalso
    apply hnpre
    refine ⟨(c :: ts).dropLast, ?_⟩
    have hdrop := congrArg List.dropLast ht
    rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil c ts)] at hdrop
    simpa [rangeDupWord, rangeWord] using hdrop

private theorem bfEquiv_baseFiber_rangeWord_rangeDupWord (k : ℕ) (τ : Label ℕ) :
    BFEquiv (L := Language.empty) ((k + 1 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → BaseFiber (rangeWord k) τ)
      (Fin.elim0 : Fin 0 → BaseFiber (rangeDupWord k) τ) := by
  by_cases hp : τ.1 <+: (rangeWord k).toList
  · have hq : τ.1 <+: (rangeDupWord k).toList := hp.trans ⟨[k], rfl⟩
    rw [bfEquiv_empty_elim0_natCast_iff, baseFiber_of_isPrefix hp, baseFiber_of_isPrefix hq]
  · by_cases hq : τ.1 <+: (rangeDupWord k).toList
    · have hτ : τ.1 = (rangeDupWord k).toList := eq_rangeDupWord_of_prefix hq hp
      have hlast : τ.lastVal = k := by simp [Label.lastVal, hτ, rangeDupWord]
      have : Infinite (BaseFiber (rangeWord k) τ) := by
        classical
        simp only [BaseFiber, hp, ↓reduceIte]
        infer_instance
      rw [bfEquiv_empty_elim0_natCast_iff_le_card, baseFiber_of_isPrefix hq, hlast]
    · rw [bfEquiv_empty_elim0_natCast_iff, baseFiber_of_not_isPrefix hp,
        baseFiber_of_not_isPrefix hq]

/-- At depth `k + 1`, the singleton row tuples `![.row (rangeWord k)]` and
`![.row (rangeDupWord k)]` are back-and-forth equivalent, yet no automorphism carries one to the
other; hence the orbit rank of `![.row (rangeWord k)]` exceeds `k`. -/
theorem natCast_lt_orbitRank_row_rangeWord (k : ℕ) :
    (k : Ordinal.{0}) <
      orbitRank (L := omegaLang) ![(Carrier.row (rangeWord k) : BaseAssembly)] := by
  classical
  by_contra! hle
  have hstab : (k : Ordinal.{0}) ∈
      orbitStable (L := omegaLang) ![(Carrier.row (rangeWord k) : BaseAssembly)] :=
    (orbitRank_le_iff _ _).mp hle
  let eR : AllowedWord ≃ AllowedWord := Equiv.swap (rangeWord k) (rangeDupWord k)
  have hbf_succ : BFEquiv (L := omegaLang) ((k + 1 : ℕ) : Ordinal.{0}) 1
      ![(Carrier.row (rangeWord k) : BaseAssembly)]
      ![(Carrier.row (eR (rangeWord k)) : BaseAssembly)] := by
    refine bfEquiv_singleton_row_of_fiber_bfEquiv eR (rangeWord k) fun r τ => ?_
    by_cases hr₁ : r = rangeWord k
    · subst hr₁
      dsimp only [eR]
      rw [Equiv.swap_apply_left]
      exact bfEquiv_baseFiber_rangeWord_rangeDupWord k τ
    · by_cases hr₂ : r = rangeDupWord k
      · subst hr₂
        dsimp only [eR]
        rw [Equiv.swap_apply_right]
        exact (bfEquiv_baseFiber_rangeWord_rangeDupWord k τ).symm
      · dsimp only [eR]
        rw [Equiv.swap_apply_of_ne_of_ne hr₁ hr₂]
  have hbf : BFEquiv (L := omegaLang) (k : Ordinal.{0}) 1
      ![(Carrier.row (rangeWord k) : BaseAssembly)]
      ![(Carrier.row (rangeDupWord k) : BaseAssembly)] := by
    rw [Equiv.swap_apply_left] at hbf_succ
    exact hbf_succ.mono (Nat.cast_le.mpr (Nat.le_succ k))
  obtain ⟨Φ, hΦ⟩ := (bfEquiv_iff_exists_equiv_comp_eq_of_mem_orbitStable hstab).mp hbf
  have hrow : rowEquivOfEquiv Φ (rangeWord k) = rangeDupWord k := by
    have h0 := congrFun hΦ 0
    simpa using congrArg ownerRow h0
  let τk : Label ℕ := ⟨(rangeDupWord k).toList, by simp [rangeDupWord]⟩
  have hnpre : ¬ τk.1 <+: (rangeWord k).toList := fun hpre => by
    have := hpre.length_le
    simp [τk, rangeDupWord, rangeWord] at this
  have hfin_q : Finite (BaseFiber (rowEquivOfEquiv Φ (rangeWord k)) τk) := by
    rw [hrow, finite_baseFiber_iff]
  have hfin_p : Finite (BaseFiber (rangeWord k) τk) :=
    Finite.of_equiv _ (fiberEquivOfEquiv Φ (rangeWord k) τk).toEquiv.symm
  exact hnpre ((finite_baseFiber_iff _ _).mp hfin_p)

/-- The internal Scott rank of `BaseAssembly` is at least `ω`. -/
theorem omega0_le_internalScottRank_baseAssembly :
    ω ≤ internalScottRank (L := omegaLang) BaseAssembly :=
  Ordinal.omega0_le.mpr fun k =>
    ((natCast_lt_orbitRank_row_rangeWord k).trans (orbitRank_lt_internalScottRank _)).le

/-- The internal Scott rank of `BaseAssembly` is `ω`. -/
theorem internalScottRank_baseAssembly :
    internalScottRank (L := omegaLang) BaseAssembly = ω :=
  le_antisymm internalScottRank_baseAssembly_le_omega0 omega0_le_internalScottRank_baseAssembly

/-! ### Cantor-tree companions `CompanionAssembly z` -/

/-- The `i`-th entry of the path encoding `z : ℕ → Bool`: `pathVal z (2n) = n` and
`pathVal z (2n + 1) = n + (z n).toNat`. -/
def pathVal (z : ℕ → Bool) (i : ℕ) : ℕ :=
  i / 2 + if i % 2 = 1 then (z (i / 2)).toNat else 0

/-- The sequence `pathVal z` is nondecreasing. -/
theorem monotone_pathVal (z : ℕ → Bool) : Monotone (pathVal z) := by
  refine monotone_nat_of_le_succ fun i => ?_
  have hb : (z (i / 2)).toNat ≤ 1 := Bool.toNat_le _
  simp only [pathVal]
  split_ifs <;> omega

/-- Every entry `pathVal z i` is bounded by its index `i`. -/
theorem pathVal_le_self (z : ℕ → Bool) (i : ℕ) : pathVal z i ≤ i := by
  have hb : (z (i / 2)).toNat ≤ 1 := Bool.toNat_le _
  simp only [pathVal]
  split_ifs <;> omega

/-- Every entry `pathVal z i` is at least `i / 2`, regardless of `z`. -/
theorem half_le_pathVal (z : ℕ → Bool) (i : ℕ) : i / 2 ≤ pathVal z i :=
  Nat.le_add_right _ _

/-- The encoding `z ↦ pathVal z` is injective. -/
theorem eq_of_forall_pathVal_eq {z z' : ℕ → Bool} (h : ∀ i, pathVal z i = pathVal z' i) :
    z = z' := by
  funext n
  have hn := h (2 * n + 1)
  have hd : (2 * n + 1) / 2 = n := by omega
  have hm : (2 * n + 1) % 2 = 1 := by omega
  simp only [pathVal, hd, hm, ↓reduceIte, Nat.add_left_cancel_iff] at hn
  cases hzn : z n <;> cases hzn' : z' n <;> simp_all

/-- The `n`-th finite prefix of `pathVal z` as an allowed word of length `n + 1`. -/
def pathRow (z : ℕ → Bool) (n : ℕ) : AllowedWord where
  toList := (List.range (n + 1)).map (pathVal z)
  pairwise_le := List.pairwise_map.mpr (List.pairwise_lt_range.imp fun h =>
    monotone_pathVal z (Nat.le_of_lt h))
  getElem_le i hi := by
    simp only [List.length_map, List.length_range] at hi
    simp [pathVal_le_self]

@[simp]
theorem toList_pathRow (z : ℕ → Bool) (n : ℕ) :
    (pathRow z n).toList = (List.range (n + 1)).map (pathVal z) := by
  rfl

/-- Distinct prefix lengths give distinct rows along `pathRow z`. -/
theorem pathRow_injective (z : ℕ → Bool) : Function.Injective (pathRow z) :=
  fun m n h => by
    have hlen := congrArg (fun w => w.toList.length) h
    simpa using hlen

/-- The `n`-th nonempty prefix of `pathVal z` as a fiber label. -/
def pathLabel (z : ℕ → Bool) (n : ℕ) : Label ℕ :=
  ⟨(pathRow z n).toList, by simp⟩

@[simp]
theorem val_pathLabel (z : ℕ → Bool) (n : ℕ) :
    (pathLabel z n).1 = (List.range (n + 1)).map (pathVal z) := by
  rfl

@[simp]
theorem lastVal_pathLabel (z : ℕ → Bool) (n : ℕ) :
    (pathLabel z n).lastVal = pathVal z n := by
  rw [Label.lastVal, List.getLast_eq_getElem]
  simp

/-- A label is a prefix of `pathRow z n` exactly when it is `pathLabel z k` for some `k ≤ n`. -/
theorem isPrefix_pathRow_iff (z : ℕ → Bool) (n : ℕ) (τ : Label ℕ) :
    τ.1 <+: (pathRow z n).toList ↔ ∃ k ≤ n, τ = pathLabel z k := by
  constructor
  · intro hpre
    have hpos : 0 < τ.1.length := List.length_pos_iff.mpr τ.2
    have hle : τ.1.length ≤ n + 1 := by simpa using hpre.length_le
    let k : ℕ := τ.1.length - 1
    have hk : k + 1 = τ.1.length := by omega
    refine ⟨k, by omega, Subtype.ext ?_⟩
    obtain ⟨t, ht⟩ := hpre
    have htake : ((pathRow z n).toList).take τ.1.length = τ.1 := by
      rw [← ht, List.take_left]
    rw [← htake, toList_pathRow, val_pathLabel, ← List.map_take, List.take_range, min_eq_left hle,
      hk]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨((List.range (n + 1)).drop (k + 1)).map (pathVal z), ?_⟩
    rw [val_pathLabel, toList_pathRow, ← List.map_append]
    have htake : (List.range (n + 1)).take (k + 1) = List.range (k + 1) := by
      rw [List.take_range]
      congr 1
      omega
    rw [← htake, List.take_append_drop]

/-- Predicate cutting out the labels along the infinite branch `pathVal z`. -/
def IsPathLabel (z : ℕ → Bool) (τ : Label ℕ) : Prop :=
  ∃ k, τ = pathLabel z k

/-- A label satisfies `IsPathLabel z` iff it equals `pathLabel z k` for some `k`. -/
theorem isPathLabel_iff (z : ℕ → Bool) (τ : Label ℕ) :
    IsPathLabel z τ ↔ ∃ k, τ = pathLabel z k := by
  rfl

open Classical in
/-- The labelled fibers of `CompanionAssembly z`: every `some p` copies `BaseFiber p`, while the
adjoined row `none` follows the infinite branch `IsPathLabel z`. -/
def CompanionFiber (z : ℕ → Bool) : Option AllowedWord → Label ℕ → Type
  | some p, τ => BaseFiber p τ
  | none, τ => if IsPathLabel z τ then Fin (τ.lastVal + 1) else ℕ

instance (z : ℕ → Bool) (r : Option AllowedWord) (τ : Label ℕ) :
    Language.empty.Structure (CompanionFiber z r τ) :=
  Language.emptyStructure

instance (z : ℕ → Bool) (r : Option AllowedWord) (τ : Label ℕ) :
    Countable (CompanionFiber z r τ) := by
  classical
  cases r with
  | some p => exact inferInstanceAs (Countable (BaseFiber p τ))
  | none =>
    dsimp only [CompanionFiber]
    split_ifs <;> infer_instance

/-- The companion row assembly indexed by a Cantor branch `z : ℕ → Bool`. -/
abbrev CompanionAssembly (z : ℕ → Bool) : Type := Carrier (Option AllowedWord) (CompanionFiber z)

/-- At the limit row `none`, `CompanionFiber z none τ` is finite iff `τ` lies on the branch `z`. -/
theorem finite_companionFiber_none_iff (z : ℕ → Bool) (τ : Label ℕ) :
    Finite (CompanionFiber z none τ) ↔ IsPathLabel z τ := by
  classical
  dsimp only [CompanionFiber]
  split_ifs with h
  · exact iff_of_true inferInstance h
  · exact iff_of_false Infinite.not_finite h

/-! ### Finite-level Hilbert-hotel equivalences and `BFEquiv ω` -/

private theorem bfEquiv_companionFiber_none_pathRow (z : ℕ → Bool) (m : ℕ) (τ : Label ℕ) :
    BFEquiv (L := Language.empty) (m : Ordinal.{o}) 0
      (Fin.elim0 : Fin 0 → CompanionFiber z none τ)
      (Fin.elim0 : Fin 0 → BaseFiber (pathRow z (2 * m)) τ) := by
  classical
  by_cases hpre : τ.1 <+: (pathRow z (2 * m)).toList
  · obtain ⟨k, _, rfl⟩ := (isPrefix_pathRow_iff z (2 * m) τ).mp hpre
    have hpath : IsPathLabel z (pathLabel z k) := ⟨k, rfl⟩
    rw [bfEquiv_empty_elim0_natCast_iff, baseFiber_of_isPrefix hpre]
    simp [CompanionFiber, hpath]
  · by_cases hpath : IsPathLabel z τ
    · obtain ⟨k, rfl⟩ := hpath
      have hk_gt : 2 * m < k := by
        by_contra! hle
        exact hpre ((isPrefix_pathRow_iff z (2 * m) _).mpr ⟨k, hle, rfl⟩)
      have hcard_p : ENat.card (CompanionFiber z none (pathLabel z k)) =
          (pathVal z k + 1 : ℕ) := by
        have hp : IsPathLabel z (pathLabel z k) := ⟨k, rfl⟩
        simp [CompanionFiber, hp]
      have : Infinite (BaseFiber (pathRow z (2 * m)) (pathLabel z k)) := by
        simp only [BaseFiber, hpre, ↓reduceIte]
        infer_instance
      symm
      rw [bfEquiv_empty_elim0_natCast_iff_le_card, hcard_p]
      have hm_le : m ≤ pathVal z k := by
        have := half_le_pathVal z k
        omega
      exact_mod_cast (by omega : m ≤ pathVal z k + 1)
    · rw [bfEquiv_empty_elim0_natCast_iff, baseFiber_of_not_isPrefix hpre]
      simp [CompanionFiber, hpath]

private theorem bfEquiv_baseFiber_pathRow_succ (z : ℕ → Bool) (m n : ℕ) (τ : Label ℕ) :
    BFEquiv (L := Language.empty) (m : Ordinal.{o}) 0
      (Fin.elim0 : Fin 0 → BaseFiber (pathRow z (2 * m + n)) τ)
      (Fin.elim0 : Fin 0 → BaseFiber (pathRow z (2 * m + (n + 1))) τ) := by
  classical
  by_cases hp : τ.1 <+: (pathRow z (2 * m + n)).toList
  · obtain ⟨k, hk, rfl⟩ := (isPrefix_pathRow_iff z (2 * m + n) τ).mp hp
    have hq : (pathLabel z k).1 <+: (pathRow z (2 * m + (n + 1))).toList :=
      (isPrefix_pathRow_iff z (2 * m + (n + 1)) _).mpr ⟨k, by omega, rfl⟩
    rw [bfEquiv_empty_elim0_natCast_iff, baseFiber_of_isPrefix hp, baseFiber_of_isPrefix hq]
  · by_cases hq : τ.1 <+: (pathRow z (2 * m + (n + 1))).toList
    · obtain ⟨k, hk, rfl⟩ := (isPrefix_pathRow_iff z (2 * m + (n + 1)) τ).mp hq
      have hk_eq : k = 2 * m + (n + 1) := by
        by_contra hne
        exact hp ((isPrefix_pathRow_iff z (2 * m + n) _).mpr ⟨k, by omega, rfl⟩)
      have : Infinite (BaseFiber (pathRow z (2 * m + n)) (pathLabel z k)) := by
        simp only [BaseFiber, hp, ↓reduceIte]
        infer_instance
      rw [bfEquiv_empty_elim0_natCast_iff_le_card, baseFiber_of_isPrefix hq, lastVal_pathLabel]
      have hm_le : m ≤ pathVal z k := by
        have := half_le_pathVal z k
        omega
      exact_mod_cast (by omega : m ≤ pathVal z k + 1)
    · rw [bfEquiv_empty_elim0_natCast_iff, baseFiber_of_not_isPrefix hp,
        baseFiber_of_not_isPrefix hq]

/-- At every finite depth `m`, the empty tuples of `CompanionAssembly z` and `BaseAssembly` are
back-and-forth equivalent via a Hilbert-hotel shift along the tail of `pathRow z`. -/
theorem bfEquiv_natCast_companionAssembly (z : ℕ → Bool) (m : ℕ) :
    BFEquiv (L := omegaLang) (m : Ordinal.{o}) 0
      (Fin.elim0 : Fin 0 → CompanionAssembly z) (Fin.elim0 : Fin 0 → BaseAssembly) := by
  classical
  let f : ℕ → AllowedWord := fun n => pathRow z (2 * m + n)
  have hf : f.Injective := fun n₁ n₂ h => by
    have := pathRow_injective z h
    omega
  refine bfEquiv_elim0_of_fiber_bfEquiv (Equiv.optionOfNatInjective f hf) fun r τ => ?_
  cases r with
  | none =>
    rw [Equiv.optionOfNatInjective_none]
    exact bfEquiv_companionFiber_none_pathRow z m τ
  | some p =>
    by_cases hp : p ∈ Set.range f
    · obtain ⟨n, rfl⟩ := hp
      rw [Equiv.optionOfNatInjective_some_apply]
      exact bfEquiv_baseFiber_pathRow_succ z m n τ
    · rw [Equiv.optionOfNatInjective_some_of_notMem hf hp]
      exact BFEquiv.refl _ _

/-- For every `z : ℕ → Bool`, the empty tuples of `CompanionAssembly z` and `BaseAssembly` are
back-and-forth equivalent at level `ω`. -/
theorem bfEquiv_omega0_companionAssembly (z : ℕ → Bool) :
    BFEquiv (L := omegaLang) (ω : Ordinal.{o}) 0
      (Fin.elim0 : Fin 0 → CompanionAssembly z) (Fin.elim0 : Fin 0 → BaseAssembly) := by
  rw [BFEquiv.limit Ordinal.isSuccLimit_omega0]
  intro β hβ
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hβ
  exact bfEquiv_natCast_companionAssembly z m

/-! ### Pairwise non-isomorphism and Scott height consequences -/

/-- No `CompanionAssembly z` is isomorphic to `BaseAssembly`. -/
theorem isEmpty_equiv_companionAssembly_baseAssembly (z : ℕ → Bool) :
    IsEmpty (CompanionAssembly z ≃[omegaLang] BaseAssembly) := by
  refine ⟨fun Φ => ?_⟩
  let p : AllowedWord := rowEquivOfEquiv Φ none
  let τ : Label ℕ := pathLabel z p.toList.length
  have hfin_z : Finite (CompanionFiber z none τ) :=
    (finite_companionFiber_none_iff z τ).mpr ⟨p.toList.length, rfl⟩
  have hfin_p : Finite (BaseFiber p τ) :=
    Finite.of_equiv _ (fiberEquivOfEquiv Φ none τ).toEquiv
  have hpre : τ.1 <+: p.toList := (finite_baseFiber_iff p τ).mp hfin_p
  have hlen := hpre.length_le
  simp [τ, pathLabel, pathRow] at hlen

/-- Distinct Cantor branches `z ≠ z'` yield non-isomorphic companions. -/
theorem isEmpty_equiv_companionAssembly {z z' : ℕ → Bool} (hzz' : z ≠ z') :
    IsEmpty (CompanionAssembly z ≃[omegaLang] CompanionAssembly z') := by
  refine ⟨fun Φ => ?_⟩
  have hnone : rowEquivOfEquiv Φ none = none := by
    cases hr : rowEquivOfEquiv Φ none with
    | none => rfl
    | some p =>
      exfalso
      let τ : Label ℕ := pathLabel z p.toList.length
      have hfin_z : Finite (CompanionFiber z none τ) :=
        (finite_companionFiber_none_iff z τ).mpr ⟨p.toList.length, rfl⟩
      have hfin_p : Finite (CompanionFiber z' (rowEquivOfEquiv Φ none) τ) :=
        Finite.of_equiv _ (fiberEquivOfEquiv Φ none τ).toEquiv
      rw [hr] at hfin_p
      have hpre : τ.1 <+: p.toList := (finite_baseFiber_iff p τ).mp hfin_p
      have hlen := hpre.length_le
      simp [τ, pathLabel, pathRow] at hlen
  apply hzz'
  refine eq_of_forall_pathVal_eq fun k => ?_
  have hfin_z : Finite (CompanionFiber z none (pathLabel z k)) :=
    (finite_companionFiber_none_iff z _).mpr ⟨k, rfl⟩
  have hfin_z' : Finite (CompanionFiber z' (rowEquivOfEquiv Φ none) (pathLabel z k)) :=
    Finite.of_equiv _ (fiberEquivOfEquiv Φ none (pathLabel z k)).toEquiv
  rw [hnone] at hfin_z'
  obtain ⟨k', hk'⟩ := (finite_companionFiber_none_iff z' _).mp hfin_z'
  have hlast := congrArg Label.lastVal hk'
  have hlen : k = k' := by
    simpa [pathLabel, pathRow] using congrArg (fun τ : Label ℕ => τ.1.length) hk'
  subst hlen
  simpa using hlast

/-- The external Scott height of `BaseAssembly` strictly exceeds its internal Scott rank `ω`. -/
theorem omega0_lt_scottHeight_baseAssembly :
    ω < scottHeight (L := omegaLang) BaseAssembly := by
  by_contra! hle
  obtain ⟨Φ⟩ := nonempty_equiv_of_bfEquiv_of_scottHeight_le hle
    (bfEquiv_omega0_companionAssembly (fun _ => false)).symm
  exact (isEmpty_equiv_companionAssembly_baseAssembly (fun _ => false)).false Φ.symm

/-- The Scott height of `BaseAssembly` is bounded above by `ω + ω`. -/
theorem scottHeight_baseAssembly_le_omega0_add_omega0 :
    scottHeight (L := omegaLang) BaseAssembly ≤ ω + ω := by
  simpa [internalScottRank_baseAssembly] using
    scottHeight_le_internalScottRank_add_omega0 (L := omegaLang) BaseAssembly

/-- **Rank-`ω` witness with continuum-many `BFEquiv ω` companions.** There exist a countable
structure `M` over `omegaLang` of internal Scott rank `ω` and Scott height strictly above `ω`, and
a Cantor-indexed family `N` of pairwise non-isomorphic countable structures, none isomorphic to `M`,
all back-and-forth equivalent to `M` at level `ω`. -/
theorem exists_internalScottRank_omega_with_large_bfClass :
    ∃ (M : Type) (_ : omegaLang.Structure M) (_ : Countable M) (_ : Infinite M)
      (N : (ℕ → Bool) → Type) (_ : ∀ z, omegaLang.Structure (N z))
      (_ : ∀ z, Countable (N z)) (_ : ∀ z, Infinite (N z)),
      internalScottRank (L := omegaLang) M = ω ∧
      ω < scottHeight (L := omegaLang) M ∧
      (∀ z, BFEquiv (L := omegaLang) (ω : Ordinal.{0}) 0
        (Fin.elim0 : Fin 0 → N z) (Fin.elim0 : Fin 0 → M)) ∧
      (∀ z, IsEmpty (N z ≃[omegaLang] M)) ∧
      (∀ z z', z ≠ z' → IsEmpty (N z ≃[omegaLang] N z')) :=
  ⟨BaseAssembly, inferInstance, inferInstance, inferInstance,
    CompanionAssembly, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    internalScottRank_baseAssembly, omega0_lt_scottHeight_baseAssembly,
    bfEquiv_omega0_companionAssembly, isEmpty_equiv_companionAssembly_baseAssembly,
    fun _ _ h => isEmpty_equiv_companionAssembly h⟩

end TauCeti.RowAssembly
