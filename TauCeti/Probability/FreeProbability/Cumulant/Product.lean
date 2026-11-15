/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Comap
public import TauCeti.Probability.FreeProbability.Cumulant.Basic

/-!
# Free cumulants with products as arguments

Let `φ : A → R` be a function on a monoid, `a : α → A` a word indexed by a finite set `s` of
positions in a linear order, and `f : α → β` a map to a linear order that is monotone on `s`. The
fibres of `f` cut `s` into consecutive intervals; multiplying the letters of `a` along each fibre,
in increasing order, gives the grouped word `fiberProd a s f`, indexed by the image `f '' s`. Let
`σ_f ∈ NC(s)` be the partition of `s` into the fibres of `f`.

The free cumulants of the grouped word are sums of free cumulants of the original word: for every
noncrossing partition `ρ` of `f '' s`,
`κ_ρ(fiberProd a s f) = ∑_{π ∈ NC(s), π ⊔ σ_f = ρ̂} κ_π(a)`, where `ρ̂` is the pullback of `ρ`
along `f` and the join is taken in `NC(s)`. For `ρ` the partition into one part this is the
formula `κ_m(A₁, …, A_m) = ∑_{π ∈ NC(n), π ⊔ σ = 1_n} κ_π(a₁, …, aₙ)` for cumulants whose
arguments `A_j` are products of consecutive letters, the key step towards the characterisation of
freeness by the vanishing of mixed cumulants.

The proof identifies the block moments of `ρ̂` with those of `ρ`, so that both sides satisfy the
moment–cumulant formula on `NC(f '' s)`, and then uses that pulling back is an order isomorphism
of `NC(f '' s)` onto the upper interval `[σ_f, 1_s]` of `NC(s)`. Specializing to the collapse of
positions `0` and `1` in `Fin (n + 3)` when `a 0 * a 1 = 1` and decomposing the proper partitions
joining `{0, 1}` to `⊤` into two-part interval splits (as in `NoncrossingPartition.mu_bot_top`)
gives `TauCeti.freeCumulant_eq_neg_sum_of_mul_eq_one`.

## Main definitions

* `TauCeti.fiberProd a s f` — the word indexed by `f '' s` whose letter at `y` is the product, in
  increasing order, of the letters of `a` at the positions of `s` over `y`.

## Main results

* `TauCeti.partitionMoment_comap` — the block moment of the pullback of a partition `P` of
  `f '' s` is the block moment of `P` for the grouped word.
* `TauCeti.partitionCumulant_fiberProd` — `κ_ρ(fiberProd a s f) = ∑_{π ⊔ σ_f = ρ̂} κ_π(a)`.
* `TauCeti.freeCumulant_fiberProd` and `TauCeti.freeCumulant_fiberProd_eq_sum_prod` — the free
  cumulant of the grouped word is `∑_{π ⊔ σ_f = 1_s} κ_π(a)`, and in multiplicative form
  `∑_{π ⊔ σ_f = 1_s} ∏_{B ∈ π} κ_B(a)`.
* `TauCeti.freeCumulant_comp_of_strictMonoOn` — for injective `f` no letters are grouped, so free
  cumulants are invariant under increasing relabelling of the positions; in particular
  `TauCeti.freeCumulant_eq_freeCumulant_comp_orderEmbOfFin` — every free cumulant is a cumulant
  `κ_n` of a word indexed by `Fin n`.
* `TauCeti.freeCumulant_eq_neg_sum_of_mul_eq_one` — when `φ 1 = 1` and `a 0 * a 1 = 1` in a word of
  length `n + 3`, `κ(a) = -∑ r : Fin (n + 2), κ_{[1, r + 1]}(a) * κ_{univ \ [1, r + 1]}(a)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Theorem 11.12.
* M. Krawczyk, R. Speicher, *Combinatorics of free cumulants*, J. Combin. Theory Ser. A 90
  (2000), 267–292.
-/

public section

open Finset

namespace TauCeti

variable {R A α β : Type*} [LinearOrder α] {s : Finset α} {f : α → β}

section FiberProd

variable [Monoid A] [DecidableEq β]

/-- The word obtained from `a` by grouping along the fibres of `f`: its letter at `y` is the
product `a_{x₁} * ⋯ * a_{xₖ}` over the positions `x₁ < ⋯ < xₖ` of `s` with `f xᵢ = y`. When `β` is
linearly ordered and `f` is monotone on `s` these positions are consecutive in `s`. -/
def fiberProd (a : α → A) (s : Finset α) (f : α → β) (y : β) : A :=
  ({x ∈ s | f x = y}.sort.map a).prod

/-- Unfolding of the word grouped along the fibres of `f`. -/
theorem fiberProd_def (a : α → A) (s : Finset α) (f : α → β) (y : β) :
    fiberProd a s f y = ({x ∈ s | f x = y}.sort.map a).prod := by
  rw [fiberProd]

end FiberProd

variable [LinearOrder β]

section Moment

variable [Monoid A]

/-- For `f` monotone on `s`, the product of a word along the positions of `s` over a set `C` is
the product of the word grouped along the fibres of `f` over the values of `f` at those
positions. -/
private theorem prod_map_sort_filter_eq (hf : MonotoneOn f s) (a : α → A) (C : Finset β) :
    ({x ∈ s | f x ∈ C}.sort.map a).prod =
      (({x ∈ s | f x ∈ C}.image f).sort.map (fiberProd a s f)).prod := by
  rw [prod_map_sort_eq_prod_map_sort_image (hf.mono (coe_subset.2 (filter_subset _ s)))]
  refine congrArg List.prod (List.map_congr_left fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := mem_image.1 ((mem_sort _).1 hy)
  rw [fiberProd_def, filter_filter,
    filter_congr (s := s) (q := fun z => f z = f x) fun z _ =>
      ⟨And.right, fun h => ⟨h ▸ (mem_filter.1 hx).2, h⟩⟩]

variable [CommMonoid R]

/-- The block moment of the pullback along `f` of a partition `P` of `f '' s` is the block
moment of `P` for the word grouped along the fibres of `f`. -/
theorem partitionMoment_comap (φ : A → R) (a : α → A) (hf : MonotoneOn f s)
    (P : Finpartition (s.image f)) :
    partitionMoment φ a (P.comap f) = partitionMoment φ (fiberProd a s f) P := by
  rw [partitionMoment_def, partitionMoment_def, Finpartition.prod_parts_comap]
  refine prod_congr rfl fun C hC => ?_
  rw [prod_map_sort_filter_eq hf, Finpartition.image_filter_mem_of_mem_parts hC]

end Moment

section Cumulant

variable [CommRing R] [Monoid A] (φ : A → R) (a : α → A)

/-- *Free cumulants with products as arguments*: the free cumulant of a noncrossing partition `ρ`
of `f '' s` for the word grouped along the fibres of `f` is the sum of the free cumulants of the
noncrossing partitions `π` of `s` whose join with the partition `σ_f` of `s` into the fibres of `f`
is the pullback of `ρ`. -/
theorem partitionCumulant_fiberProd (hf : MonotoneOn f s)
    (ρ : NoncrossingPartition (s.image f)) :
    partitionCumulant φ (fiberProd a s f) ρ =
      ∑ π : NoncrossingPartition s with π ⊔ NoncrossingPartition.comap hf ⊥ =
        NoncrossingPartition.comap hf ρ, partitionCumulant φ a π := by
  set e := NoncrossingPartition.comap hf
  -- Both sides satisfy the moment–cumulant formula on `NC(f '' s)`.
  refine (congrFun (eq_partitionCumulant_of_forall_sum_Iic φ (fiberProd a s f)
    (fun ρ => ∑ π : NoncrossingPartition s with π ⊔ e ⊥ = e ρ, partitionCumulant φ a π)
    fun ρ => ?_) ρ).symm
  -- A partition `π` of `s` contributes to the term of `ρ' ≤ ρ` with `π ⊔ σ_f = ρ̂'` exactly when
  -- `π ≤ ρ̂`, and then `ρ'` is unique.
  rw [sum_comm' (t' := Iic (e ρ))
      (s' := fun π => {ρ' ∈ Iic ρ | π ⊔ e ⊥ = e ρ'}) fun ρ' π => by
    simp only [mem_filter, mem_univ, true_and, mem_Iic]
    exact ⟨fun ⟨h, hπ⟩ => ⟨⟨h, hπ⟩, le_sup_left.trans (hπ.trans_le (e.monotone h))⟩,
      fun ⟨h, _⟩ => h⟩]
  rw [← partitionMoment_comap φ a hf, ← NoncrossingPartition.coe_comap hf,
    ← sum_Iic_partitionCumulant]
  refine sum_congr rfl fun π hπ => ?_
  obtain ⟨ρ₀, hρ₀⟩ :=
    (NoncrossingPartition.exists_comap_eq_iff (hf := hf)).2 (le_sup_right (a := π))
  have hρ₀ρ : ρ₀ ≤ ρ :=
    e.le_iff_le.1 (hρ₀.trans_le (sup_le (mem_Iic.1 hπ) (e.monotone bot_le)))
  rw [show {ρ' ∈ Iic ρ | π ⊔ e ⊥ = e ρ'} = {ρ₀} by
      ext ρ'
      rw [mem_filter, mem_Iic, mem_singleton, ← hρ₀, e.injective.eq_iff]
      exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨h ▸ hρ₀ρ, h.symm⟩⟩,
    sum_singleton]

/-- *Free cumulants with products as arguments*: the free cumulant of the word grouped along the
fibres of `f` is the sum of the free cumulants of the noncrossing partitions `π` of `s` whose join
with the partition `σ_f` of `s` into the fibres of `f` is the partition into one part,
`κ(fiberProd a s f) = ∑_{π ⊔ σ_f = 1_s} κ_π(a)`. -/
theorem freeCumulant_fiberProd (hf : MonotoneOn f s) :
    freeCumulant φ (fiberProd a s f) (s.image f) =
      ∑ π : NoncrossingPartition s with π ⊔ NoncrossingPartition.comap hf ⊥ = ⊤,
        partitionCumulant φ a π := by
  rw [freeCumulant_def, partitionCumulant_fiberProd φ a hf, NoncrossingPartition.comap_top]

/-- *Free cumulants with products as arguments*, in multiplicative form:
`κ(fiberProd a s f) = ∑_{π ⊔ σ_f = 1_s} ∏_{B ∈ π} κ_B(a)`, where `σ_f` is the partition of `s`
into the fibres of `f`. -/
theorem freeCumulant_fiberProd_eq_sum_prod (hf : MonotoneOn f s) :
    freeCumulant φ (fiberProd a s f) (s.image f) =
      ∑ π : NoncrossingPartition s with π ⊔ NoncrossingPartition.comap hf ⊥ = ⊤,
        ∏ B ∈ π.1.parts, freeCumulant φ a B := by
  simp_rw [freeCumulant_fiberProd φ a hf, partitionCumulant_eq_prod_freeCumulant]

/-- *Increasing relabelling*: for a map `e` that is strictly monotone on `s`, the free cumulant of
the word `b ∘ e` along `s` is the free cumulant of `b` along the image `e '' s`. -/
theorem freeCumulant_comp_of_strictMonoOn {e : α → β} (he : StrictMonoOn e s) (b : β → A) :
    freeCumulant φ (b ∘ e) s = freeCumulant φ b (s.image e) := by
  -- The fibres of `e` in `s` are singletons, so grouping along them changes nothing.
  have hfib : ∀ x ∈ s, {y ∈ s | e y = e x} = {x} := fun x hx =>
    eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨hx, rfl⟩,
      fun y hy => he.injOn (mem_filter.1 hy).1 hx (mem_filter.1 hy).2⟩
  have hσ : NoncrossingPartition.comap he.monotoneOn ⊥ = ⊥ := by
    refine Subtype.ext <| Finpartition.ext_of_part fun x hx => ?_
    simp only [NoncrossingPartition.coe_comap, NoncrossingPartition.coe_bot,
      Finpartition.part_comap_bot hx, hfib x hx]
    -- The part of `⊥` through `x` is the singleton `{x}`.
    exact (Finpartition.part_eq_of_mem _ (Finpartition.mem_bot_iff.2 ⟨x, hx, rfl⟩)
      (mem_singleton_self x)).symm
  have hb : Set.EqOn b (fiberProd (b ∘ e) s e) (s.image e) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    simp [fiberProd_def, hfib x hx]
  rw [freeCumulant_congr φ hb, freeCumulant_fiberProd φ (b ∘ e) he.monotoneOn, hσ]
  simp only [sup_bot_eq, filter_eq', mem_univ, ite_true, sum_singleton, freeCumulant_def]

/-- Relabelling the positions of `s` increasingly by `Fin #s`: the free cumulant of `b` along `s`
is the cumulant `κ_n` of the word `b ∘ s.orderEmbOfFin`, which lists the letters of `b` at the
positions of `s` in increasing order. -/
theorem freeCumulant_eq_freeCumulant_comp_orderEmbOfFin (b : α → A) (s : Finset α) :
    freeCumulant φ b s = freeCumulant φ (b ∘ s.orderEmbOfFin rfl) univ := by
  rw [freeCumulant_comp_of_strictMonoOn φ ((s.orderEmbOfFin rfl).strictMono.strictMonoOn _),
    image_orderEmbOfFin_univ]

end Cumulant

section CollapseZeroOne

private theorem icc_convex_fin {n : ℕ} (r : Fin (n + 2)) :
    ∀ a ∈ Icc (1 : Fin (n + 3)) r.succ, ∀ c ∈ Icc 1 r.succ,
      ∀ b ∈ (univ : Finset (Fin (n + 3))), a < b → b < c → b ∈ Icc 1 r.succ :=
  fun _ ha _ hc _ _ hab hbc =>
    mem_Icc.2 ⟨(mem_Icc.1 ha).1.trans hab.le, hbc.le.trans (mem_Icc.1 hc).2⟩

/-- The two-part noncrossing partition of `Fin (n + 3)` splitting off the interval
`[1, r + 1]`. -/
private noncomputable def splitIccZeroOne {n : ℕ} (r : Fin (n + 2)) :
    NoncrossingPartition (univ : Finset (Fin (n + 3))) :=
  ⟨Finpartition.splitPartition univ (Icc 1 r.succ)
      (nonempty_Icc.2 (Fin.one_le_of_ne_zero r.succ_ne_zero)) (subset_univ _),
    Finpartition.isNoncrossing_splitPartition (icc_convex_fin r)⟩

private theorem splitIccZeroOne_injective {n : ℕ} :
    Function.Injective (splitIccZeroOne (n := n)) := by
  intro r₁ r₂ h
  have h1 : ∀ r : Fin (n + 2), (1 : Fin (n + 3)) ∈ Icc 1 r.succ :=
    fun r => mem_Icc.2 ⟨le_rfl, Fin.one_le_of_ne_zero r.succ_ne_zero⟩
  have hp := congrArg (fun π : NoncrossingPartition _ => π.1.part 1) h
  rw [splitIccZeroOne, splitIccZeroOne, Finpartition.part_splitPartition_of_mem (h1 r₁),
    Finpartition.part_splitPartition_of_mem (h1 r₂)] at hp
  have hm₁ : r₁.succ ≤ r₂.succ :=
    (mem_Icc.1 (hp ▸ mem_Icc.2 ⟨Fin.one_le_of_ne_zero r₁.succ_ne_zero, le_rfl⟩)).2
  have hm₂ : r₂.succ ≤ r₁.succ :=
    (mem_Icc.1 (hp.symm ▸ mem_Icc.2 ⟨Fin.one_le_of_ne_zero r₂.succ_ne_zero, le_rfl⟩)).2
  exact Fin.succ_injective _ (le_antisymm hm₁ hm₂)

/-- Every proper noncrossing partition of `Fin (n + 3)` whose join with the pair `{0, 1}` is `⊤`
has the form `splitIccZeroOne r` for a unique `r : Fin (n + 2)`. -/
private theorem image_splitIccZeroOne_eq {n : ℕ} :
    univ.image (splitIccZeroOne (n := n)) =
      ({π : NoncrossingPartition (univ : Finset (Fin (n + 3))) |
        π ⊔ ⟨Finpartition.pairPartition univ 0 1 (subset_univ _),
          Finpartition.isNoncrossing_pairPartition (subset_univ _)⟩ = ⊤} : Finset _).erase ⊤ := by
  ext π
  simp only [mem_image, mem_univ, true_and]
  refine ⟨?_, fun hπ => ?_⟩
  · rintro ⟨r, rfl⟩
    exact NoncrossingPartition.splitPartition_mem_erase_top_sup_pairPartition (subset_univ _)
      (nonempty_Icc.2 (Fin.one_le_of_ne_zero r.succ_ne_zero)) (subset_univ _) (icc_convex_fin r)
      (mem_Icc.2 ⟨le_rfl, Fin.one_le_of_ne_zero r.succ_ne_zero⟩) (by simp)
  · obtain ⟨hπtop, -, hsup⟩ := (mem_erase.1 hπ).imp_right mem_filter.1
    have hadj : ∀ z ∈ (univ : Finset (Fin (n + 3))), z ≤ 0 ∨ 1 ≤ z := fun z _ =>
      (eq_or_ne z 0).imp Eq.le Fin.one_le_of_ne_zero
    obtain ⟨hunion, hne⟩ := NoncrossingPartition.part_union_eq_of_sup_pairPartition_eq_top
      (subset_univ _) (by simp) hadj hπtop hsup
    have h1T : (1 : Fin (n + 3)) ∈ π.1.part 1 := π.1.mem_part_self.2 (mem_univ 1)
    have h0T : (0 : Fin (n + 3)) ∉ π.1.part 1 := fun h0 =>
      hne ((π.1.mem_part_iff_part_eq_part (mem_univ 0) (mem_univ 1)).1 h0)
    obtain ⟨r, hr⟩ := Fin.eq_succ_of_ne_zero
      (ne_of_mem_of_not_mem (max'_mem (π.1.part 1) ⟨1, h1T⟩) h0T)
    have hTIcc : π.1.part 1 = Icc 1 r.succ := by
      ext x
      simp only [mem_Icc, ← hr]
      refine ⟨fun hx => ⟨Fin.one_le_of_ne_zero (ne_of_mem_of_not_mem hx h0T),
        le_max' _ x hx⟩, fun ⟨h1x, hxm⟩ => by_contra fun hxT => ?_⟩
      have hx0 : x ∈ π.1.part 0 :=
        (mem_union.1 (hunion.symm ▸ mem_univ x)).resolve_right hxT
      exact hne (Finpartition.isNoncrossing_iff_part.1 π.2 0 (mem_univ 0) 1 (mem_univ 1)
        x hx0 _ (max'_mem _ _) (by simp)
        (h1x.lt_of_ne fun h => hxT (h ▸ h1T)) (hxm.lt_of_ne fun h => hxT (h ▸ max'_mem _ _)))
    refine ⟨r, Subtype.ext (Finpartition.ext_of_part fun x _ => ?_)⟩
    rw [splitIccZeroOne]
    by_cases hx : x ∈ Icc 1 r.succ
    · rw [Finpartition.part_splitPartition_of_mem hx, ← hTIcc]
      exact ((π.1.mem_part_iff_part_eq_part (mem_univ x) (mem_univ 1)).1 (hTIcc.symm ▸ hx)).symm
    · rw [Finpartition.part_splitPartition_of_notMem (mem_univ x) hx, ← hTIcc]
      have hx1 : x ∉ π.1.part 1 := hTIcc.symm ▸ hx
      have hx0 : x ∈ π.1.part 0 := (mem_union.1 (hunion.symm ▸ mem_univ x)).resolve_right hx1
      rw [(π.1.mem_part_iff_part_eq_part (mem_univ x) (mem_univ 0)).1 hx0]
      ext y
      simp only [mem_sdiff, mem_univ, true_and]
      exact ⟨fun hyT => (mem_union.1 (hunion.symm ▸ mem_univ y)).resolve_right hyT,
        fun hy0 hyT => hne ((π.1.mem_part_iff_part_eq_part (mem_univ y) (mem_univ 0)).1 hy0 ▸
          (π.1.mem_part_iff_part_eq_part (mem_univ y) (mem_univ 1)).1 hyT)⟩

private theorem comap_collapse_zero_one_bot {n : ℕ}
    (hf : MonotoneOn (fun z : Fin (n + 3) => if z = 1 then 0 else z)
      (univ : Finset (Fin (n + 3)))) :
    NoncrossingPartition.comap hf ⊥ =
      ⟨Finpartition.pairPartition univ 0 1 (subset_univ _),
        Finpartition.isNoncrossing_pairPartition (subset_univ _)⟩ := by
  refine Subtype.ext (Finpartition.ext_of_part fun x hx => ?_)
  simp only [NoncrossingPartition.coe_comap, NoncrossingPartition.coe_bot,
    Finpartition.part_comap_bot hx]
  by_cases hx01 : x = 0 ∨ x = 1
  · have hpair0 : (Finpartition.pairPartition univ 0 1 (subset_univ _)).part x = {0, 1} :=
      Finpartition.part_eq_of_mem _
        (Finpartition.mem_parts_pairPartition.2 (Or.inl rfl)) (by simp [hx01])
    rw [hpair0]
    ext z
    rcases hx01 with rfl | rfl <;>
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton] <;>
      by_cases hz : z = 1 <;> simp [hz]
  · have hx0 : x ≠ 0 := fun h => hx01 (Or.inl h)
    have hx1 : x ≠ 1 := fun h => hx01 (Or.inr h)
    have hsing : {x} ∈ (Finpartition.pairPartition univ 0 1 (subset_univ _)).parts :=
      Finpartition.mem_parts_pairPartition.2 (Or.inr ⟨x, by simp [hx0, hx1], rfl⟩)
    rw [Finpartition.part_eq_of_mem _ hsing (mem_singleton_self x)]
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_singleton, ite_eq_right hx1]
    by_cases hz : z = 1 <;> simp [hz, hx0.symm, hx1.symm]

variable [CommRing R] [Monoid A] in
/-- **Cancelling an adjacent inverse pair at the start of a free cumulant.** If `φ 1 = 1` and the
first two entries of a word `a : Fin (n + 3) → A` satisfy `a 0 * a 1 = 1`, then `freeCumulant φ a`
on `univ` equals minus the sum over `r : Fin (n + 2)` of the products of the cumulants of `a` on
`[1, r + 1]` and on its complement `univ \ [1, r + 1]`. -/
theorem freeCumulant_eq_neg_sum_of_mul_eq_one (φ : A → R) (h1 : φ 1 = 1) {n : ℕ}
    {a : Fin (n + 3) → A} (ha : a 0 * a 1 = 1) :
    freeCumulant φ a univ =
      -∑ r : Fin (n + 2),
        freeCumulant φ a (Icc 1 r.succ) * freeCumulant φ a (univ \ Icc 1 r.succ) := by
  have hadj : ∀ z ∈ (univ : Finset (Fin (n + 3))), z ≤ 0 ∨ 1 ≤ z := fun z _ =>
    (eq_or_ne z 0).imp Eq.le Fin.one_le_of_ne_zero
  obtain ⟨hf, -, -⟩ := Finset.collapse_adjacent_spec (mem_univ (0 : Fin (n + 3)))
    (mem_univ 1) (by simp) hadj
  set f : Fin (n + 3) → Fin (n + 3) := fun z => if z = 1 then 0 else z
  have hfib0 : fiberProd a univ f 0 = 1 := by
    have hset : {x ∈ (univ : Finset (Fin (n + 3))) | f x = 0} = {0, 1} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, f]
      by_cases hx : x = 1 <;> simp [hx]
    rw [fiberProd_def, hset, sort_pair _ (by simp) (by simp)]
    simpa using ha
  let two : Fin (n + 3) := ⟨2, by omega⟩
  have hcard : 1 < #(univ.image f) :=
    one_lt_card.2 ⟨0, mem_image_of_mem f (mem_univ 0),
      two, mem_image.2 ⟨two, mem_univ two, by simp [f, two, Fin.ext_iff]⟩,
      by simp [two, Fin.ext_iff]⟩
  have hlhs : freeCumulant φ (fiberProd a univ f) (univ.image f) = 0 :=
    freeCumulant_eq_zero_of_apply_eq_one φ _ h1 hfib0 (mem_image_of_mem f (mem_univ 0)) hcard
  have hrhs := (freeCumulant_fiberProd_eq_sum_prod φ a hf).symm.trans hlhs
  rw [comap_collapse_zero_one_bot hf,
    ← sum_erase_add _ _ (by simp : (⊤ : NoncrossingPartition _) ∈ _),
    ← partitionCumulant_eq_prod_freeCumulant, ← freeCumulant_def, ← image_splitIccZeroOne_eq,
    sum_image fun _ _ _ _ h => splitIccZeroOne_injective h] at hrhs
  have hparts (r : Fin (n + 2)) :
      ∏ B ∈ (splitIccZeroOne r).1.parts, freeCumulant φ a B =
        freeCumulant φ a (Icc 1 r.succ) * freeCumulant φ a (univ \ Icc 1 r.succ) := by
    have hsC : ((univ : Finset (Fin (n + 3))) \ Icc 1 r.succ).Nonempty :=
      ⟨0, mem_sdiff.2 ⟨mem_univ 0, by simp⟩⟩
    have hne : Icc (1 : Fin (n + 3)) r.succ ≠ univ \ Icc 1 r.succ := fun heq =>
      (mem_sdiff.1 (heq ▸ mem_Icc.2 ⟨le_rfl, Fin.one_le_of_ne_zero r.succ_ne_zero⟩)).2
        (mem_Icc.2 ⟨le_rfl, Fin.one_le_of_ne_zero r.succ_ne_zero⟩)
    rw [splitIccZeroOne, Finpartition.parts_splitPartition hsC, prod_pair hne]
  simp_rw [hparts] at hrhs
  exact eq_neg_of_add_eq_zero_right hrhs

end CollapseZeroOne

end TauCeti
