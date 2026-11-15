/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Finset.Sort

/-!
# Finite cutoff lists of slopes of Newton polygons

The Newton polygon of a power series can have infinitely many finite unit edges, so its finite
slopes do not form a multiset. Whenever only finitely many finite unit edges have slope at most a
real cutoff `c`, as holds for every entire series, those slopes form a finite nondecreasing list
`PowerSeries.newtonSlopesLe f v c`, with strict variant `PowerSeries.newtonSlopesLt f v c` below
`c`. When infinitely many finite unit edges lie below the cutoff, both definitions fall back to the
empty list `[]`.

Because a Newton polygon is convex, listing the finite unit edges below `c` in increasing index
order already produces a nondecreasing list of real slopes (`PowerSeries.sortedLE_newtonSlopesLe`
and `PowerSeries.sortedLE_newtonSlopesLt`). Under finiteness of the cutoff edge set:

* the multiplicity of `σ` in `f.newtonSlopesLe v c` is `f.newtonSlopeMultiplicity v σ` for `σ ≤ c`,
  and `0` above `c` (`PowerSeries.count_newtonSlopesLe`);
* `f.newtonSlopesLe v c` splits as `f.newtonSlopesLt v c` followed by
  `f.newtonSlopeMultiplicity v c` copies of `c`
  (`PowerSeries.newtonSlopesLe_eq_append_replicate`), and for `c₁ ≤ c₂` the list below `c₁` is a
  prefix and a filter of the list below `c₂` (`PowerSeries.isPrefix_newtonSlopesLe_of_le`,
  `PowerSeries.newtonSlopesLe_eq_filter_of_le`);
* the length of `f.newtonSlopesLe v c` is the sum of `f.newtonSlopeMultiplicity v σ` over `σ ≤ c`
  (`PowerSeries.length_newtonSlopesLe_eq_finsum_newtonSlopeMultiplicity`).

For a polynomial `p`, the cutoff list is the nondecreasing sort of the filtered finite slope
multiset `(p.newtonSlopes v).filter (· ≤ c)` (`Polynomial.newtonSlopesLe_coe` and
`Polynomial.coe_newtonSlopesLe`). For nonzero entire series over a normed division ring, cutoff
slope multisets add under multiplication (`PowerSeries.IsEntire.coe_newtonSlopesLe_mul`).

## Main definitions

* `PowerSeries.newtonSlopesLe f v c`: the nondecreasing list of finite unit slopes `≤ c` of the
  Newton polygon of `f`, or `[]` if infinitely many finite unit edges have slope `≤ c`.
* `PowerSeries.newtonSlopesLt f v c`: the strict cutoff list of finite unit slopes `< c`.

## Main results

* `PowerSeries.sortedLE_newtonSlopesLe`, `PowerSeries.sortedLE_newtonSlopesLt`: the cutoff lists
  are ordered nondecreasingly.
* `PowerSeries.count_newtonSlopesLe`, `PowerSeries.count_newtonSlopesLt`: multiplicities in the
  cutoff lists agree with `PowerSeries.newtonSlopeMultiplicity` up to the cutoff.
* `PowerSeries.newtonSlopesLe_eq_append_replicate`, `PowerSeries.newtonSlopesLe_eq_filter_of_le`,
  `PowerSeries.isPrefix_newtonSlopesLe_of_le`: compatibility across cutoffs.
* `PowerSeries.length_newtonSlopesLe_eq_finsum_newtonSlopeMultiplicity`: the cutoff length is the
  sum of the slope multiplicities up to the cutoff.
* `PowerSeries.newtonSlopesLe_rescale`, `PowerSeries.newtonSlopesLe_X_pow_mul`,
  `PowerSeries.newtonSlopesLe_map`: elementary operations on cutoff lists.
* `Polynomial.coe_newtonSlopesLe`, `Polynomial.newtonSlopesLe_coe`: comparison with
  `Polynomial.newtonSlopes`.
* `PowerSeries.IsEntire.coe_newtonSlopesLe_mul`: cutoff slope multisets add on products of nonzero
  entire series.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open TauCeti

namespace PowerSeries

section SortedSlopes

/-- The unit slopes of `h` satisfying `p`, listed in increasing edge-index order when finitely many
finite unit edges satisfy `p`, and `[]` otherwise. -/
private noncomputable def sortedSlopes (h : ℕ → WithTop ℝ) (p : ℝ → Prop) : List ℝ :=
  open Classical in
  if hs : {n | n ∈ finiteEdges h ∧ p (unitSlope h n)}.Finite then
    hs.toFinset.sort.map (unitSlope h)
  else []

private theorem sortedSlopes_of_finite {h : ℕ → WithTop ℝ} {p : ℝ → Prop}
    (hs : {n | n ∈ finiteEdges h ∧ p (unitSlope h n)}.Finite) :
    sortedSlopes h p = hs.toFinset.sort.map (unitSlope h) := by
  simp only [sortedSlopes, hs, ↓reduceDIte]

private theorem sortedLE_sortedSlopes {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) (p : ℝ → Prop) :
    (sortedSlopes h p).SortedLE := by
  classical
  rw [sortedSlopes]
  split_ifs with hs
  · rw [List.sortedLE_iff_pairwise, List.pairwise_map]
    refine (hs.toFinset.pairwise_sort (· ≤ ·)).imp_of_mem fun {i j} hi hj hij => ?_
    rw [Finset.mem_sort, Set.Finite.mem_toFinset] at hi hj
    exact hh.monotoneOn hi.1 hj.1 hij
  · exact List.sortedLE_nil

private theorem forall_mem_sortedSlopes {h : ℕ → WithTop ℝ} {p : ℝ → Prop} {σ : ℝ}
    (hσ : σ ∈ sortedSlopes h p) : p σ := by
  classical
  rw [sortedSlopes] at hσ
  split_ifs at hσ with hs
  · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hσ
    rw [Finset.mem_sort, Set.Finite.mem_toFinset] at hn
    exact hn.2
  · cases hσ

private theorem count_sortedSlopes {h : ℕ → WithTop ℝ} {p : ℝ → Prop} [DecidablePred p]
    (hs : {n | n ∈ finiteEdges h ∧ p (unitSlope h n)}.Finite) (σ : ℝ) :
    (sortedSlopes h p).count σ =
      if p σ then {n | n ∈ finiteEdges h ∧ unitSlope h n = σ}.ncard else 0 := by
  rw [sortedSlopes_of_finite hs, ← Multiset.coe_count, ← Multiset.map_coe, Finset.sort_eq,
    Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  split_ifs with hpσ
  · have hsub : {n | n ∈ finiteEdges h ∧ unitSlope h n = σ}.Finite :=
      hs.subset fun n hn => ⟨hn.1, hn.2.symm ▸ hpσ⟩
    rw [Set.ncard_eq_toFinset_card _ hsub]
    congr 1
    ext n
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2 ▸ hpσ⟩, h2.symm⟩⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn hseq
    rw [Set.Finite.mem_toFinset] at hn
    exact hpσ (hseq ▸ hn.2)

private theorem length_sortedSlopes {h : ℕ → WithTop ℝ} {p : ℝ → Prop}
    (hs : {n | n ∈ finiteEdges h ∧ p (unitSlope h n)}.Finite) :
    (sortedSlopes h p).length = {n | n ∈ finiteEdges h ∧ p (unitSlope h n)}.ncard := by
  rw [sortedSlopes_of_finite hs, List.length_map, Finset.length_sort,
    ← Set.ncard_eq_toFinset_card _ hs]

private theorem sortedSlopes_eq_map {h g : ℕ → WithTop ℝ} {p q : ℝ → Prop}
    (φ : ℕ ↪ ℕ) (hφ : StrictMonoOn φ (finiteEdges h)) (t : ℝ → ℝ)
    (hedges : finiteEdges g = φ '' finiteEdges h)
    (hslope : ∀ n ∈ finiteEdges h, unitSlope g (φ n) = t (unitSlope h n))
    (hpq : ∀ n ∈ finiteEdges h, q (unitSlope g (φ n)) ↔ p (unitSlope h n)) :
    sortedSlopes g q = (sortedSlopes h p).map t := by
  classical
  have hset : {m | m ∈ finiteEdges g ∧ q (unitSlope g m)} =
      φ '' {n | n ∈ finiteEdges h ∧ p (unitSlope h n)} := by
    ext m
    simp only [Set.mem_ofPred_eq, hedges, Set.mem_image]
    constructor
    · rintro ⟨⟨n, hn, rfl⟩, hq⟩
      exact ⟨n, ⟨hn, (hpq n hn).mp hq⟩, rfl⟩
    · rintro ⟨n, ⟨hn, hp⟩, rfl⟩
      exact ⟨⟨n, hn, rfl⟩, (hpq n hn).mpr hp⟩
  by_cases hs : {n | n ∈ finiteEdges h ∧ p (unitSlope h n)}.Finite
  · have hsg : {m | m ∈ finiteEdges g ∧ q (unitSlope g m)}.Finite := hset ▸ hs.image φ
    have hfin : hsg.toFinset = hs.toFinset.map φ := by
      ext m
      simp only [Set.Finite.mem_toFinset, Finset.mem_map, hset, Set.mem_image]
    have hmono : StrictMonoOn φ hs.toFinset := hφ.mono fun n hn => (hs.mem_toFinset.mp hn).1
    rw [sortedSlopes_of_finite hsg, sortedSlopes_of_finite hs, hfin, ← hmono.map_finsetSort,
      List.map_map, List.map_map]
    refine List.map_congr_left fun n hn => ?_
    rw [Finset.mem_sort, Set.Finite.mem_toFinset] at hn
    exact hslope n hn.1
  · have hsg : ¬ {m | m ∈ finiteEdges g ∧ q (unitSlope g m)}.Finite := by
      rw [hset, Set.finite_image_iff φ.injective.injOn]
      exact hs
    simp only [sortedSlopes, hsg, hs, ↓reduceDIte, List.map_nil]

private theorem eq_of_sortedLE_of_count_eq {l₁ l₂ : List ℝ} (h₁ : l₁.SortedLE) (h₂ : l₂.SortedLE)
    (hc : ∀ σ : ℝ, l₁.count σ = l₂.count σ) : l₁ = l₂ := by
  have hm : (l₁ : Multiset ℝ) = (l₂ : Multiset ℝ) :=
    Multiset.ext.mpr fun σ => by simpa only [Multiset.coe_count] using hc σ
  exact (Multiset.coe_eq_coe.mp hm).eq_of_pairwise' h₁.pairwise h₂.pairwise

end SortedSlopes

section Ring

variable {R S : Type*} [Ring R] [Ring S] (f : R⟦X⟧) (v : AddValuation R (WithTop ℝ))

/-- The nondecreasing list of finite unit slopes at most `c` of the Newton polygon of `f`. When
infinitely many finite unit edges have slope at most `c`, this is the empty list `[]`. -/
noncomputable def newtonSlopesLe (c : ℝ) : List ℝ :=
  open Classical in
  if hs : {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.Finite
  then hs.toFinset.sort.map (unitSlope (f.newtonPolygon v))
  else []

/-- The nondecreasing list of finite unit slopes strictly below `c` of the Newton polygon of `f`.
When infinitely many finite unit edges have slope strictly below `c`, this is the empty list
`[]`. -/
noncomputable def newtonSlopesLt (c : ℝ) : List ℝ :=
  open Classical in
  if hs : {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c}.Finite
  then hs.toFinset.sort.map (unitSlope (f.newtonPolygon v))
  else []

/-- `newtonSlopesLe` sorts the finite unit edges of slope at most `c` by edge index and maps them
by `unitSlope`. -/
theorem newtonSlopesLe_def (c : ℝ) :
    f.newtonSlopesLe v c =
      open Classical in
      if hs : {n | n ∈ finiteEdges (f.newtonPolygon v) ∧
          unitSlope (f.newtonPolygon v) n ≤ c}.Finite
      then hs.toFinset.sort.map (unitSlope (f.newtonPolygon v))
      else [] :=
  (rfl)

/-- `newtonSlopesLt` sorts the finite unit edges of slope strictly below `c` by edge index and maps
them by `unitSlope`. -/
theorem newtonSlopesLt_def (c : ℝ) :
    f.newtonSlopesLt v c =
      open Classical in
      if hs : {n | n ∈ finiteEdges (f.newtonPolygon v) ∧
          unitSlope (f.newtonPolygon v) n < c}.Finite
      then hs.toFinset.sort.map (unitSlope (f.newtonPolygon v))
      else [] :=
  (rfl)

private theorem newtonSlopesLe_eq_sortedSlopes (c : ℝ) :
    f.newtonSlopesLe v c = sortedSlopes (f.newtonPolygon v) (· ≤ c) :=
  (rfl)

private theorem newtonSlopesLt_eq_sortedSlopes (c : ℝ) :
    f.newtonSlopesLt v c = sortedSlopes (f.newtonPolygon v) (· < c) :=
  (rfl)

/-- The cutoff list `f.newtonSlopesLe v c` is ordered nondecreasingly. -/
theorem sortedLE_newtonSlopesLe (c : ℝ) : (f.newtonSlopesLe v c).SortedLE :=
  sortedLE_sortedSlopes (f.isConvexSeq_newtonPolygon v) (· ≤ c)

/-- The strict cutoff list `f.newtonSlopesLt v c` is ordered nondecreasingly. -/
theorem sortedLE_newtonSlopesLt (c : ℝ) : (f.newtonSlopesLt v c).SortedLE :=
  sortedLE_sortedSlopes (f.isConvexSeq_newtonPolygon v) (· < c)

/-- Every entry of `f.newtonSlopesLe v c` is at most `c`. -/
theorem le_of_mem_newtonSlopesLe {c σ : ℝ} (hσ : σ ∈ f.newtonSlopesLe v c) : σ ≤ c := by
  rw [newtonSlopesLe_eq_sortedSlopes] at hσ
  exact forall_mem_sortedSlopes (p := (· ≤ c)) hσ

/-- Every entry of `f.newtonSlopesLt v c` is strictly less than `c`. -/
theorem lt_of_mem_newtonSlopesLt {c σ : ℝ} (hσ : σ ∈ f.newtonSlopesLt v c) : σ < c := by
  rw [newtonSlopesLt_eq_sortedSlopes] at hσ
  exact forall_mem_sortedSlopes (p := (· < c)) hσ

/-- The zero power series has no finite slopes at or below any cutoff. -/
@[simp]
theorem newtonSlopesLe_zero (c : ℝ) : (0 : R⟦X⟧).newtonSlopesLe v c = [] := by
  simp [newtonSlopesLe_def]

/-- The zero power series has no finite slopes strictly below any cutoff. -/
@[simp]
theorem newtonSlopesLt_zero (c : ℝ) : (0 : R⟦X⟧).newtonSlopesLt v c = [] := by
  simp [newtonSlopesLt_def]

variable {f v}

/-- The cutoff list `newtonSlopesLe` depends only on the Newton polygon. -/
theorem newtonSlopesLe_congr {g : S⟦X⟧} {w : AddValuation S (WithTop ℝ)}
    (h : f.newtonPolygon v = g.newtonPolygon w) (c : ℝ) :
    f.newtonSlopesLe v c = g.newtonSlopesLe w c := by
  rw [newtonSlopesLe_eq_sortedSlopes, newtonSlopesLe_eq_sortedSlopes, h]

/-- The strict cutoff list `newtonSlopesLt` depends only on the Newton polygon. -/
theorem newtonSlopesLt_congr {g : S⟦X⟧} {w : AddValuation S (WithTop ℝ)}
    (h : f.newtonPolygon v = g.newtonPolygon w) (c : ℝ) :
    f.newtonSlopesLt v c = g.newtonSlopesLt w c := by
  rw [newtonSlopesLt_eq_sortedSlopes, newtonSlopesLt_eq_sortedSlopes, h]

variable (f v)

/-- Negation preserves the cutoff list `newtonSlopesLe`. -/
@[simp]
theorem newtonSlopesLe_neg (c : ℝ) : (-f).newtonSlopesLe v c = f.newtonSlopesLe v c :=
  newtonSlopesLe_congr (f.newtonPolygon_neg v) c

/-- Negation preserves the strict cutoff list `newtonSlopesLt`. -/
@[simp]
theorem newtonSlopesLt_neg (c : ℝ) : (-f).newtonSlopesLt v c = f.newtonSlopesLt v c :=
  newtonSlopesLt_congr (f.newtonPolygon_neg v) c

/-- Multiplying by a constant of finite valuation preserves `newtonSlopesLe`. -/
theorem newtonSlopesLe_C_mul {a : R} (ha : v a ≠ ⊤) (c : ℝ) :
    (C a * f).newtonSlopesLe v c = f.newtonSlopesLe v c := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ha
  have hpoly : (C a * f).newtonPolygon v =
      fun n => f.newtonPolygon v n + ((r + 0 * n : ℝ) : WithTop ℝ) := by
    simp [newtonPolygon_C_mul, ← hr, add_comm]
  simpa only [newtonSlopesLe_eq_sortedSlopes, List.map_id] using
    sortedSlopes_eq_map (Function.Embedding.refl ℕ) (fun _ _ _ _ hab => hab) id
      (by rw [hpoly, finiteEdges_add_affine, Function.Embedding.coe_refl, Set.image_id])
      (fun n hn => by
        dsimp only [Function.Embedding.coe_refl, id]
        rw [hpoly, unitSlope_add_affine hn, add_zero])
      (fun n hn => by
        dsimp only [Function.Embedding.coe_refl, id]
        rw [hpoly, unitSlope_add_affine hn, add_zero])

/-- Multiplying by a constant of finite valuation preserves `newtonSlopesLt`. -/
theorem newtonSlopesLt_C_mul {a : R} (ha : v a ≠ ⊤) (c : ℝ) :
    (C a * f).newtonSlopesLt v c = f.newtonSlopesLt v c := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ha
  have hpoly : (C a * f).newtonPolygon v =
      fun n => f.newtonPolygon v n + ((r + 0 * n : ℝ) : WithTop ℝ) := by
    simp [newtonPolygon_C_mul, ← hr, add_comm]
  simpa only [newtonSlopesLt_eq_sortedSlopes, List.map_id] using
    sortedSlopes_eq_map (Function.Embedding.refl ℕ) (fun _ _ _ _ hab => hab) id
      (by rw [hpoly, finiteEdges_add_affine, Function.Embedding.coe_refl, Set.image_id])
      (fun n hn => by
        dsimp only [Function.Embedding.coe_refl, id]
        rw [hpoly, unitSlope_add_affine hn, add_zero])
      (fun n hn => by
        dsimp only [Function.Embedding.coe_refl, id]
        rw [hpoly, unitSlope_add_affine hn, add_zero])

/-- Multiplying by a scalar of finite valuation preserves `newtonSlopesLe`. -/
theorem newtonSlopesLe_smul {a : R} (ha : v a ≠ ⊤) (c : ℝ) :
    (a • f).newtonSlopesLe v c = f.newtonSlopesLe v c := by
  rw [smul_eq_C_mul, newtonSlopesLe_C_mul f v ha]

/-- Multiplying by a scalar of finite valuation preserves `newtonSlopesLt`. -/
theorem newtonSlopesLt_smul {a : R} (ha : v a ≠ ⊤) (c : ℝ) :
    (a • f).newtonSlopesLt v c = f.newtonSlopesLt v c := by
  rw [smul_eq_C_mul, newtonSlopesLt_C_mul f v ha]

/-- Multiplying by `X ^ k` preserves `newtonSlopesLe`: zero roots contribute no finite slopes. -/
@[simp]
theorem newtonSlopesLe_X_pow_mul (k : ℕ) (c : ℝ) :
    (X ^ k * f).newtonSlopesLe v c = f.newtonSlopesLe v c := by
  simpa only [newtonSlopesLe_eq_sortedSlopes, List.map_id] using
    sortedSlopes_eq_map (addRightEmbedding k) (fun _ _ _ _ h => Nat.add_lt_add_right h k) id
      (by rw [newtonPolygon_X_pow_mul, finiteEdges_shift]; rfl)
      (fun n _ => by rw [newtonPolygon_X_pow_mul, addRightEmbedding_apply, unitSlope_shift, id])
      (fun n _ => by rw [newtonPolygon_X_pow_mul, addRightEmbedding_apply, unitSlope_shift])

/-- Multiplying by `X ^ k` preserves `newtonSlopesLt`: zero roots contribute no finite slopes. -/
@[simp]
theorem newtonSlopesLt_X_pow_mul (k : ℕ) (c : ℝ) :
    (X ^ k * f).newtonSlopesLt v c = f.newtonSlopesLt v c := by
  simpa only [newtonSlopesLt_eq_sortedSlopes, List.map_id] using
    sortedSlopes_eq_map (addRightEmbedding k) (fun _ _ _ _ h => Nat.add_lt_add_right h k) id
      (by rw [newtonPolygon_X_pow_mul, finiteEdges_shift]; rfl)
      (fun n _ => by rw [newtonPolygon_X_pow_mul, addRightEmbedding_apply, unitSlope_shift, id])
      (fun n _ => by rw [newtonPolygon_X_pow_mul, addRightEmbedding_apply, unitSlope_shift])

/-- Mapping the coefficients along a ring homomorphism compatible with the valuations preserves
`newtonSlopesLe`. -/
theorem newtonSlopesLe_map (φ : R →+* S) {w : AddValuation S (WithTop ℝ)}
    (hφ : ∀ x, w (φ x) = v x) (c : ℝ) :
    (map φ f).newtonSlopesLe w c = f.newtonSlopesLe v c :=
  newtonSlopesLe_congr (f.newtonPolygon_map v φ hφ) c

/-- Mapping the coefficients along a ring homomorphism compatible with the valuations preserves
`newtonSlopesLt`. -/
theorem newtonSlopesLt_map (φ : R →+* S) {w : AddValuation S (WithTop ℝ)}
    (hφ : ∀ x, w (φ x) = v x) (c : ℝ) :
    (map φ f).newtonSlopesLt w c = f.newtonSlopesLt v c :=
  newtonSlopesLt_congr (f.newtonPolygon_map v φ hφ) c

/-- Mapping the coefficients along a ring homomorphism that multiplies the valuations by a positive
real factor `a` multiplies the cutoff slopes by `a`. -/
theorem newtonSlopesLe_map_eq_map_mul (φ : R →+* S) {w : AddValuation S (WithTop ℝ)}
    {a : ℝ} (ha : 0 < a) (hφ : ∀ x, w (φ x) = (v x).map (a * ·)) (c : ℝ) :
    (map φ f).newtonSlopesLe w (a * c) = (f.newtonSlopesLe v c).map (a * ·) := by
  have hpoly := f.newtonPolygon_map_eq_map_mul v φ ha hφ
  have hslope (n : ℕ) :
      unitSlope ((map φ f).newtonPolygon w) n = a * unitSlope (f.newtonPolygon v) n := by
    rw [hpoly]
    simpa using unitSlope_map (h := f.newtonPolygon v) (AddMonoidHom.mulLeft a) n
  rw [newtonSlopesLe_eq_sortedSlopes, newtonSlopesLe_eq_sortedSlopes]
  exact sortedSlopes_eq_map (Function.Embedding.refl ℕ) (fun _ _ _ _ hab => hab) (a * ·)
    (by rw [hpoly, finiteEdges_map (f := (a * ·)), Function.Embedding.coe_refl, Set.image_id])
    (fun n _ => by dsimp only [Function.Embedding.coe_refl, id]; rw [hslope n])
    (fun n _ => by
      dsimp only [Function.Embedding.coe_refl, id]
      rw [hslope n, mul_le_mul_iff_right₀ ha])

/-- Mapping the coefficients along a ring homomorphism that multiplies the valuations by a positive
real factor `a` multiplies the strict cutoff slopes by `a`. -/
theorem newtonSlopesLt_map_eq_map_mul (φ : R →+* S) {w : AddValuation S (WithTop ℝ)}
    {a : ℝ} (ha : 0 < a) (hφ : ∀ x, w (φ x) = (v x).map (a * ·)) (c : ℝ) :
    (map φ f).newtonSlopesLt w (a * c) = (f.newtonSlopesLt v c).map (a * ·) := by
  have hpoly := f.newtonPolygon_map_eq_map_mul v φ ha hφ
  have hslope (n : ℕ) :
      unitSlope ((map φ f).newtonPolygon w) n = a * unitSlope (f.newtonPolygon v) n := by
    rw [hpoly]
    simpa using unitSlope_map (h := f.newtonPolygon v) (AddMonoidHom.mulLeft a) n
  rw [newtonSlopesLt_eq_sortedSlopes, newtonSlopesLt_eq_sortedSlopes]
  exact sortedSlopes_eq_map (Function.Embedding.refl ℕ) (fun _ _ _ _ hab => hab) (a * ·)
    (by rw [hpoly, finiteEdges_map (f := (a * ·)), Function.Embedding.coe_refl, Set.image_id])
    (fun n _ => by dsimp only [Function.Embedding.coe_refl, id]; rw [hslope n])
    (fun n _ => by
      dsimp only [Function.Embedding.coe_refl, id]
      rw [hslope n, mul_lt_mul_iff_right₀ ha])

variable {f v}

/-- When only finitely many finite unit edges have slope at most `c`, the multiplicity of `σ` in
`f.newtonSlopesLe v c` is `f.newtonSlopeMultiplicity v σ` for `σ ≤ c`, and `0` otherwise. -/
theorem count_newtonSlopesLe {c : ℝ}
    (hfin : {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.Finite)
    (σ : ℝ) :
    (f.newtonSlopesLe v c).count σ = if σ ≤ c then f.newtonSlopeMultiplicity v σ else 0 := by
  rw [newtonSlopesLe_eq_sortedSlopes, newtonSlopeMultiplicity_def]
  exact count_sortedSlopes (p := (· ≤ c)) hfin σ

/-- When only finitely many finite unit edges have slope strictly below `c`, the multiplicity of
`σ` in `f.newtonSlopesLt v c` is `f.newtonSlopeMultiplicity v σ` for `σ < c`, and `0` otherwise. -/
theorem count_newtonSlopesLt {c : ℝ}
    (hfin : {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c}.Finite)
    (σ : ℝ) :
    (f.newtonSlopesLt v c).count σ = if σ < c then f.newtonSlopeMultiplicity v σ else 0 := by
  rw [newtonSlopesLt_eq_sortedSlopes, newtonSlopeMultiplicity_def]
  exact count_sortedSlopes (p := (· < c)) hfin σ

/-- When only finitely many finite unit edges have slope at most `c`, a real number belongs to
`f.newtonSlopesLe v c` if and only if it is at most `c` and has nonzero slope multiplicity. -/
theorem mem_newtonSlopesLe_iff {c σ : ℝ}
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.Finite) :
    σ ∈ f.newtonSlopesLe v c ↔ σ ≤ c ∧ f.newtonSlopeMultiplicity v σ ≠ 0 := by
  rw [← List.count_pos_iff, count_newtonSlopesLe hfin, Nat.pos_iff_ne_zero]
  split_ifs with hσ <;> simp [hσ]

/-- When only finitely many finite unit edges have slope strictly below `c`, a real number belongs
to `f.newtonSlopesLt v c` if and only if it is strictly below `c` and has nonzero slope
multiplicity. -/
theorem mem_newtonSlopesLt_iff {c σ : ℝ}
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c}.Finite) :
    σ ∈ f.newtonSlopesLt v c ↔ σ < c ∧ f.newtonSlopeMultiplicity v σ ≠ 0 := by
  rw [← List.count_pos_iff, count_newtonSlopesLt hfin, Nat.pos_iff_ne_zero]
  split_ifs with hσ <;> simp [hσ]

/-- When only finitely many finite unit edges have slope at most `c`, the length of
`f.newtonSlopesLe v c` is the number of finite unit edges of slope at most `c`. -/
theorem length_newtonSlopesLe {c : ℝ}
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.Finite) :
    (f.newtonSlopesLe v c).length =
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.ncard := by
  rw [newtonSlopesLe_eq_sortedSlopes]
  exact length_sortedSlopes (p := (· ≤ c)) hfin

/-- When only finitely many finite unit edges have slope strictly below `c`, the length of
`f.newtonSlopesLt v c` is the number of finite unit edges of slope strictly below `c`. -/
theorem length_newtonSlopesLt {c : ℝ}
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c}.Finite) :
    (f.newtonSlopesLt v c).length =
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c}.ncard := by
  rw [newtonSlopesLt_eq_sortedSlopes]
  exact length_sortedSlopes (p := (· < c)) hfin

/-- On a Newton polygon with first finite index `a` and a finite face `[l, u]` of slope `c`, the
length of `f.newtonSlopesLe v c` is `u - a`. -/
theorem length_newtonSlopesLe_of_isFiniteFace {c : ℝ} {l u a : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) c l u) (ha : f.newtonPolygon v a ≠ ⊤)
    (hfirst : ∀ n, f.newtonPolygon v n ≠ ⊤ → a ≤ n) :
    (f.newtonSlopesLe v c).length = u - a := by
  have hconv := f.isConvexSeq_newtonPolygon v
  rw [length_newtonSlopesLe (hface.finite_setOf_unitSlope_le hconv)]
  have hu := hface.right_eq_start_add_ncard_unitSlope_le hconv ha hfirst
  omega

/-- On a Newton polygon with first finite index `a` and a finite face `[l, u]` of slope `c`, the
length of `f.newtonSlopesLt v c` is `l - a`. -/
theorem length_newtonSlopesLt_of_isFiniteFace {c : ℝ} {l u a : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) c l u) (ha : f.newtonPolygon v a ≠ ⊤)
    (hfirst : ∀ n, f.newtonPolygon v n ≠ ⊤ → a ≤ n) :
    (f.newtonSlopesLt v c).length = l - a := by
  have hconv := f.isConvexSeq_newtonPolygon v
  have hlt :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c}.Finite :=
    (hface.finite_setOf_unitSlope_le hconv).subset fun _ h => ⟨h.1, h.2.le⟩
  rw [length_newtonSlopesLt hlt]
  have hl := hface.left_eq_start_add_ncard_unitSlope_lt hconv ha hfirst
  omega

/-- When only finitely many finite unit edges have slope at most `c`, `f.newtonSlopesLe v c` is
`f.newtonSlopesLt v c` followed by `f.newtonSlopeMultiplicity v c` copies of `c`. -/
theorem newtonSlopesLe_eq_append_replicate {c : ℝ}
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.Finite) :
    f.newtonSlopesLe v c =
      f.newtonSlopesLt v c ++ List.replicate (f.newtonSlopeMultiplicity v c) c := by
  have hlt :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c}.Finite :=
    hfin.subset fun _ h => ⟨h.1, h.2.le⟩
  refine eq_of_sortedLE_of_count_eq (f.sortedLE_newtonSlopesLe v c) ?_ fun σ => ?_
  · rw [List.sortedLE_iff_pairwise, List.pairwise_append]
    refine ⟨(f.sortedLE_newtonSlopesLt v c).pairwise, List.pairwise_replicate.mpr (.inr le_rfl),
      fun x hx y hy => ?_⟩
    rw [List.eq_of_mem_replicate hy]
    exact (lt_of_mem_newtonSlopesLt f v hx).le
  · rw [count_newtonSlopesLe hfin, List.count_append, count_newtonSlopesLt hlt,
      List.count_replicate]
    rcases lt_trichotomy σ c with h | rfl | h
    · simp [h, h.le, h.ne']
    · simp
    · simp [not_le.mpr h, not_lt.mpr h.le, h.ne]

/-- When only finitely many finite unit edges have slope at most `c`, `f.newtonSlopesLt v c` is a
prefix of `f.newtonSlopesLe v c`. -/
theorem isPrefix_newtonSlopesLt_newtonSlopesLe {c : ℝ}
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.Finite) :
    f.newtonSlopesLt v c <+: f.newtonSlopesLe v c :=
  ⟨_, (newtonSlopesLe_eq_append_replicate hfin).symm⟩

/-- For `c₁ ≤ c₂`, when only finitely many finite unit edges have slope at most `c₂`, filtering
`f.newtonSlopesLe v c₂` by `(· ≤ c₁)` recovers `f.newtonSlopesLe v c₁`. -/
theorem newtonSlopesLe_eq_filter_of_le {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c₂}.Finite) :
    f.newtonSlopesLe v c₁ = (f.newtonSlopesLe v c₂).filter (· ≤ c₁) := by
  have hfin₁ :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c₁}.Finite :=
    hfin.subset fun _ h => ⟨h.1, h.2.trans hc⟩
  refine eq_of_sortedLE_of_count_eq (f.sortedLE_newtonSlopesLe v c₁)
    (List.sortedLE_iff_pairwise.mpr ((f.sortedLE_newtonSlopesLe v c₂).pairwise.filter _))
    fun σ => ?_
  rw [count_newtonSlopesLe hfin₁, ← Multiset.coe_count, ← Multiset.filter_coe,
    Multiset.count_filter, Multiset.coe_count, count_newtonSlopesLe hfin]
  by_cases hσ : σ ≤ c₁
  · simp [hσ, hσ.trans hc]
  · simp [hσ]

/-- For `c₁ ≤ c₂`, when only finitely many finite unit edges have slope at most `c₂`, filtering
`f.newtonSlopesLe v c₂` by `(· < c₁)` recovers `f.newtonSlopesLt v c₁`. -/
theorem newtonSlopesLt_eq_filter_newtonSlopesLe_of_le {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c₂}.Finite) :
    f.newtonSlopesLt v c₁ = (f.newtonSlopesLe v c₂).filter (· < c₁) := by
  have hfin₁ :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c₁}.Finite :=
    hfin.subset fun _ h => ⟨h.1, h.2.le.trans hc⟩
  refine eq_of_sortedLE_of_count_eq (f.sortedLE_newtonSlopesLt v c₁)
    (List.sortedLE_iff_pairwise.mpr ((f.sortedLE_newtonSlopesLe v c₂).pairwise.filter _))
    fun σ => ?_
  rw [count_newtonSlopesLt hfin₁, ← Multiset.coe_count, ← Multiset.filter_coe,
    Multiset.count_filter, Multiset.coe_count, count_newtonSlopesLe hfin]
  by_cases hσ : σ < c₁
  · simp [hσ, hσ.le.trans hc]
  · simp [hσ]

/-- For `c₁ ≤ c₂`, when only finitely many finite unit edges have slope at most `c₂`,
`f.newtonSlopesLe v c₁` is a prefix of `f.newtonSlopesLe v c₂`. -/
theorem isPrefix_newtonSlopesLe_of_le {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c₂}.Finite) :
    f.newtonSlopesLe v c₁ <+: f.newtonSlopesLe v c₂ := by
  have hfin₁ :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c₁}.Finite :=
    hfin.subset fun _ h => ⟨h.1, h.2.trans hc⟩
  have hmid : {n | n ∈ finiteEdges (f.newtonPolygon v) ∧
      (c₁ < unitSlope (f.newtonPolygon v) n ∧ unitSlope (f.newtonPolygon v) n ≤ c₂)}.Finite :=
    hfin.subset fun _ h => ⟨h.1, h.2.2⟩
  refine ⟨sortedSlopes (f.newtonPolygon v) (fun s => c₁ < s ∧ s ≤ c₂), ?_⟩
  refine eq_of_sortedLE_of_count_eq ?_ (f.sortedLE_newtonSlopesLe v c₂) fun σ => ?_
  · rw [List.sortedLE_iff_pairwise, List.pairwise_append]
    refine ⟨(f.sortedLE_newtonSlopesLe v c₁).pairwise,
      (sortedLE_sortedSlopes (f.isConvexSeq_newtonPolygon v) _).pairwise, fun x hx y hy => ?_⟩
    exact (le_of_mem_newtonSlopesLe f v hx).trans (forall_mem_sortedSlopes hy).1.le
  · rw [List.count_append, count_newtonSlopesLe hfin₁,
      count_sortedSlopes (p := fun s => c₁ < s ∧ s ≤ c₂) hmid,
      ← newtonSlopeMultiplicity_def, count_newtonSlopesLe hfin]
    by_cases h₁ : σ ≤ c₁
    · simp only [h₁, ↓reduceIte, h₁.trans hc, not_lt.mpr h₁, false_and, add_zero]
    · simp only [h₁, ↓reduceIte, lt_of_not_ge h₁, true_and, zero_add]

/-- When only finitely many finite unit edges have slope at most `c`, the length of
`f.newtonSlopesLe v c` is the sum of the slope multiplicities over `σ ≤ c`. -/
theorem length_newtonSlopesLe_eq_finsum_newtonSlopeMultiplicity {c : ℝ}
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.Finite) :
    (f.newtonSlopesLe v c).length = ∑ᶠ σ ∈ Set.Iic c, f.newtonSlopeMultiplicity v σ := by
  classical
  set l := f.newtonSlopesLe v c
  have hlen : l.length = ∑ σ ∈ l.toFinset, f.newtonSlopeMultiplicity v σ := by
    rw [← Multiset.coe_card, ← Multiset.toFinset_sum_count_eq (l : Multiset ℝ)]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have hσc := le_of_mem_newtonSlopesLe f v (List.mem_toFinset.mp hσ)
    simp [l, count_newtonSlopesLe hfin, hσc]
  rw [hlen, eq_comm, finsum_mem_eq_sum_of_inter_support_eq]
  ext σ
  simp [l, mem_newtonSlopesLe_iff hfin]

/-- When only finitely many finite unit edges have slope strictly below `c`, the length of
`f.newtonSlopesLt v c` is the sum of the slope multiplicities over `σ < c`. -/
theorem length_newtonSlopesLt_eq_finsum_newtonSlopeMultiplicity {c : ℝ}
    (hfin :
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c}.Finite) :
    (f.newtonSlopesLt v c).length = ∑ᶠ σ ∈ Set.Iio c, f.newtonSlopeMultiplicity v σ := by
  classical
  set l := f.newtonSlopesLt v c
  have hlen : l.length = ∑ σ ∈ l.toFinset, f.newtonSlopeMultiplicity v σ := by
    rw [← Multiset.coe_card, ← Multiset.toFinset_sum_count_eq (l : Multiset ℝ)]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have hσc := lt_of_mem_newtonSlopesLt f v (List.mem_toFinset.mp hσ)
    simp [l, count_newtonSlopesLt hfin, hσc]
  rw [hlen, eq_comm, finsum_mem_eq_sum_of_inter_support_eq]
  ext σ
  simp [l, mem_newtonSlopesLt_iff hfin]

end Ring

section CommRing

variable {R : Type*} [CommRing R] {v : AddValuation R (WithTop ℝ)}

/-- Substituting `a X` for `X` adds the valuation of `a` to every slope and shifts the cutoff by
`(v a).untop₀`. -/
theorem newtonSlopesLe_rescale (f : R⟦X⟧) {a : R} (ha : v a ≠ ⊤) (c : ℝ) :
    (rescale a f).newtonSlopesLe v (c + (v a).untop₀) =
      (f.newtonSlopesLe v c).map (· + (v a).untop₀) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ha
  have hpoly : (rescale a f).newtonPolygon v =
      fun n => f.newtonPolygon v n + ((0 + r * n : ℝ) : WithTop ℝ) := by
    simp only [f.newtonPolygon_rescale v ha, ← hr, ← WithTop.coe_nsmul, nsmul_eq_mul, zero_add,
      mul_comm]
  rw [newtonSlopesLe_eq_sortedSlopes, newtonSlopesLe_eq_sortedSlopes]
  exact sortedSlopes_eq_map (Function.Embedding.refl ℕ) (fun _ _ _ _ hab => hab)
    (· + (v a).untop₀)
    (by rw [hpoly, finiteEdges_add_affine, Function.Embedding.coe_refl, Set.image_id])
    (fun n hn => by
      dsimp only [Function.Embedding.coe_refl, id]
      rw [hpoly, unitSlope_add_affine hn, ← hr, WithTop.untop₀_coe])
    (fun n hn => by
      dsimp only [Function.Embedding.coe_refl, id]
      rw [hpoly, unitSlope_add_affine hn, ← hr, WithTop.untop₀_coe, add_le_add_iff_right])

/-- Substituting `a X` for `X` adds the valuation of `a` to every slope and shifts the strict
cutoff by `(v a).untop₀`. -/
theorem newtonSlopesLt_rescale (f : R⟦X⟧) {a : R} (ha : v a ≠ ⊤) (c : ℝ) :
    (rescale a f).newtonSlopesLt v (c + (v a).untop₀) =
      (f.newtonSlopesLt v c).map (· + (v a).untop₀) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ha
  have hpoly : (rescale a f).newtonPolygon v =
      fun n => f.newtonPolygon v n + ((0 + r * n : ℝ) : WithTop ℝ) := by
    simp only [f.newtonPolygon_rescale v ha, ← hr, ← WithTop.coe_nsmul, nsmul_eq_mul, zero_add,
      mul_comm]
  rw [newtonSlopesLt_eq_sortedSlopes, newtonSlopesLt_eq_sortedSlopes]
  exact sortedSlopes_eq_map (Function.Embedding.refl ℕ) (fun _ _ _ _ hab => hab)
    (· + (v a).untop₀)
    (by rw [hpoly, finiteEdges_add_affine, Function.Embedding.coe_refl, Set.image_id])
    (fun n hn => by
      dsimp only [Function.Embedding.coe_refl, id]
      rw [hpoly, unitSlope_add_affine hn, ← hr, WithTop.untop₀_coe])
    (fun n hn => by
      dsimp only [Function.Embedding.coe_refl, id]
      rw [hpoly, unitSlope_add_affine hn, ← hr, WithTop.untop₀_coe, add_lt_add_iff_right])

end CommRing

end PowerSeries

namespace Polynomial

variable {R : Type*} [Ring R] (p : R[X]) (v : AddValuation R (WithTop ℝ))

/-- For a polynomial viewed as a power series, the multiset underlying `newtonSlopesLe` is the
filtered finite slope multiset `(p.newtonSlopes v).filter (· ≤ c)`. -/
@[simp]
theorem coe_newtonSlopesLe (c : ℝ) :
    (((p : PowerSeries R).newtonSlopesLe v c : List ℝ) : Multiset ℝ) =
      (p.newtonSlopes v).filter (· ≤ c) := by
  have hfin : {n | n ∈ finiteEdges ((p : PowerSeries R).newtonPolygon v) ∧
      unitSlope ((p : PowerSeries R).newtonPolygon v) n ≤ c}.Finite :=
    (p.newtonPolygon_coe v ▸ p.finite_finiteEdges_newtonPolygon v).subset fun _ h => h.1
  ext σ
  rw [Multiset.coe_count, PowerSeries.count_newtonSlopesLe hfin, Multiset.count_filter,
    newtonSlopeMultiplicity_coe]

/-- For a polynomial viewed as a power series, the multiset underlying `newtonSlopesLt` is the
filtered finite slope multiset `(p.newtonSlopes v).filter (· < c)`. -/
@[simp]
theorem coe_newtonSlopesLt (c : ℝ) :
    (((p : PowerSeries R).newtonSlopesLt v c : List ℝ) : Multiset ℝ) =
      (p.newtonSlopes v).filter (· < c) := by
  have hfin : {n | n ∈ finiteEdges ((p : PowerSeries R).newtonPolygon v) ∧
      unitSlope ((p : PowerSeries R).newtonPolygon v) n < c}.Finite :=
    (p.newtonPolygon_coe v ▸ p.finite_finiteEdges_newtonPolygon v).subset fun _ h => h.1
  ext σ
  rw [Multiset.coe_count, PowerSeries.count_newtonSlopesLt hfin, Multiset.count_filter,
    newtonSlopeMultiplicity_coe]

/-- For a polynomial viewed as a power series, `newtonSlopesLe` is the nondecreasing sort of
`(p.newtonSlopes v).filter (· ≤ c)`. -/
theorem newtonSlopesLe_coe (c : ℝ) :
    (p : PowerSeries R).newtonSlopesLe v c = ((p.newtonSlopes v).filter (· ≤ c)).sort := by
  have hm : (((p : PowerSeries R).newtonSlopesLe v c : List ℝ) : Multiset ℝ) =
      (((p.newtonSlopes v).filter (· ≤ c)).sort : Multiset ℝ) := by
    rw [coe_newtonSlopesLe, Multiset.sort_eq]
  exact (Multiset.coe_eq_coe.mp hm).eq_of_pairwise'
    ((p : PowerSeries R).sortedLE_newtonSlopesLe v c).pairwise (Multiset.pairwise_sort _ _)

/-- For a polynomial viewed as a power series, `newtonSlopesLt` is the nondecreasing sort of
`(p.newtonSlopes v).filter (· < c)`. -/
theorem newtonSlopesLt_coe (c : ℝ) :
    (p : PowerSeries R).newtonSlopesLt v c = ((p.newtonSlopes v).filter (· < c)).sort := by
  have hm : (((p : PowerSeries R).newtonSlopesLt v c : List ℝ) : Multiset ℝ) =
      (((p.newtonSlopes v).filter (· < c)).sort : Multiset ℝ) := by
    rw [coe_newtonSlopesLt, Multiset.sort_eq]
  exact (Multiset.coe_eq_coe.mp hm).eq_of_pairwise'
    ((p : PowerSeries R).sortedLE_newtonSlopesLt v c).pairwise (Multiset.pairwise_sort _ _)

end Polynomial

namespace PowerSeries

section One

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ))

/-- The constant series `1` has no finite slopes at or below any cutoff. -/
@[simp]
theorem newtonSlopesLe_one (c : ℝ) : (1 : R⟦X⟧).newtonSlopesLe v c = [] := by
  rw [← Polynomial.coe_one, Polynomial.newtonSlopesLe_coe, ← Polynomial.C_1,
    Polynomial.newtonSlopes_C, Multiset.filter_zero, Multiset.sort_zero]

/-- The constant series `1` has no finite slopes strictly below any cutoff. -/
@[simp]
theorem newtonSlopesLt_one (c : ℝ) : (1 : R⟦X⟧).newtonSlopesLt v c = [] := by
  rw [← Polynomial.coe_one, Polynomial.newtonSlopesLt_coe, ← Polynomial.C_1,
    Polynomial.newtonSlopes_C, Multiset.filter_zero, Multiset.sort_zero]

end One

section Entire

variable {K : Type*} [NormedDivisionRing K] (v : AddValuation K (WithTop ℝ)) {b : ℝ}
  (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f g : K⟦X⟧}

include hb hv

/-- Only finitely many finite unit edges of an entire series have slope strictly below `c`. -/
theorem IsEntire.finite_setOf_unitSlope_newtonPolygon_lt (hf : f.IsEntire) (c : ℝ) :
    {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n < c}.Finite :=
  (hf.finite_setOf_unitSlope_newtonPolygon_le v hb hv c).subset fun _ h => ⟨h.1, h.2.le⟩

/-- For an entire series, the multiplicity of `σ` in `f.newtonSlopesLe v c` is
`f.newtonSlopeMultiplicity v σ` for `σ ≤ c`, and `0` above `c`. -/
theorem IsEntire.count_newtonSlopesLe (hf : f.IsEntire) (c σ : ℝ) :
    (f.newtonSlopesLe v c).count σ = if σ ≤ c then f.newtonSlopeMultiplicity v σ else 0 :=
  PowerSeries.count_newtonSlopesLe (hf.finite_setOf_unitSlope_newtonPolygon_le v hb hv c) σ

/-- For an entire series, the multiplicity of `σ` in `f.newtonSlopesLt v c` is
`f.newtonSlopeMultiplicity v σ` for `σ < c`, and `0` from `c` on. -/
theorem IsEntire.count_newtonSlopesLt (hf : f.IsEntire) (c σ : ℝ) :
    (f.newtonSlopesLt v c).count σ = if σ < c then f.newtonSlopeMultiplicity v σ else 0 :=
  PowerSeries.count_newtonSlopesLt (hf.finite_setOf_unitSlope_newtonPolygon_lt v hb hv c) σ

/-- For an entire series, `σ ∈ f.newtonSlopesLe v c` iff `σ ≤ c` and `σ` has nonzero slope
multiplicity. -/
theorem IsEntire.mem_newtonSlopesLe_iff (hf : f.IsEntire) {c σ : ℝ} :
    σ ∈ f.newtonSlopesLe v c ↔ σ ≤ c ∧ f.newtonSlopeMultiplicity v σ ≠ 0 :=
  PowerSeries.mem_newtonSlopesLe_iff (hf.finite_setOf_unitSlope_newtonPolygon_le v hb hv c)

/-- For an entire series, `σ ∈ f.newtonSlopesLt v c` iff `σ < c` and `σ` has nonzero slope
multiplicity. -/
theorem IsEntire.mem_newtonSlopesLt_iff (hf : f.IsEntire) {c σ : ℝ} :
    σ ∈ f.newtonSlopesLt v c ↔ σ < c ∧ f.newtonSlopeMultiplicity v σ ≠ 0 :=
  PowerSeries.mem_newtonSlopesLt_iff (hf.finite_setOf_unitSlope_newtonPolygon_lt v hb hv c)

/-- For an entire series, the length of `f.newtonSlopesLe v c` is the sum of its slope
multiplicities up to `c`. -/
theorem IsEntire.length_newtonSlopesLe_eq_finsum_newtonSlopeMultiplicity (hf : f.IsEntire)
    (c : ℝ) :
    (f.newtonSlopesLe v c).length = ∑ᶠ σ ∈ Set.Iic c, f.newtonSlopeMultiplicity v σ :=
  PowerSeries.length_newtonSlopesLe_eq_finsum_newtonSlopeMultiplicity
    (hf.finite_setOf_unitSlope_newtonPolygon_le v hb hv c)

/-- For an entire series, the length of `f.newtonSlopesLt v c` is the sum of its slope
multiplicities strictly below `c`. -/
theorem IsEntire.length_newtonSlopesLt_eq_finsum_newtonSlopeMultiplicity (hf : f.IsEntire)
    (c : ℝ) :
    (f.newtonSlopesLt v c).length = ∑ᶠ σ ∈ Set.Iio c, f.newtonSlopeMultiplicity v σ :=
  PowerSeries.length_newtonSlopesLt_eq_finsum_newtonSlopeMultiplicity
    (hf.finite_setOf_unitSlope_newtonPolygon_lt v hb hv c)

/-- **Cutoff slope multisets add under products.** For nonzero entire series, the multiset of
finite slopes at most `c` of `f * g` is the sum of those of `f` and `g`. -/
theorem IsEntire.coe_newtonSlopesLe_mul (hf : f.IsEntire) (hg : g.IsEntire) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) (c : ℝ) :
    (((f * g).newtonSlopesLe v c : List ℝ) : Multiset ℝ) =
      (f.newtonSlopesLe v c : Multiset ℝ) + (g.newtonSlopesLe v c : Multiset ℝ) := by
  ext σ
  rw [Multiset.count_add, Multiset.coe_count, Multiset.coe_count, Multiset.coe_count,
    (hf.mul hg).count_newtonSlopesLe v hb hv, hf.count_newtonSlopesLe v hb hv,
    hg.count_newtonSlopesLe v hb hv]
  split_ifs with hσ
  · exact hf.newtonSlopeMultiplicity_mul v hb hv hg hf0 hg0 σ
  · rfl

/-- **Strict cutoff slope multisets add under products.** For nonzero entire series, the multiset
of finite slopes strictly below `c` of `f * g` is the sum of those of `f` and `g`. -/
theorem IsEntire.coe_newtonSlopesLt_mul (hf : f.IsEntire) (hg : g.IsEntire) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) (c : ℝ) :
    (((f * g).newtonSlopesLt v c : List ℝ) : Multiset ℝ) =
      (f.newtonSlopesLt v c : Multiset ℝ) + (g.newtonSlopesLt v c : Multiset ℝ) := by
  ext σ
  rw [Multiset.count_add, Multiset.coe_count, Multiset.coe_count, Multiset.coe_count,
    (hf.mul hg).count_newtonSlopesLt v hb hv, hf.count_newtonSlopesLt v hb hv,
    hg.count_newtonSlopesLt v hb hv]
  split_ifs with hσ
  · exact hf.newtonSlopeMultiplicity_mul v hb hv hg hf0 hg0 σ
  · rfl

/-- For nonzero entire series, the number of finite slopes at most `c` adds under products. -/
theorem IsEntire.length_newtonSlopesLe_mul (hf : f.IsEntire) (hg : g.IsEntire) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) (c : ℝ) :
    ((f * g).newtonSlopesLe v c).length =
      (f.newtonSlopesLe v c).length + (g.newtonSlopesLe v c).length := by
  simpa only [Multiset.coe_card, Multiset.card_add] using
    congrArg Multiset.card (hf.coe_newtonSlopesLe_mul v hb hv hg hf0 hg0 c)

/-- For nonzero entire series, the number of finite slopes strictly below `c` adds under
products. -/
theorem IsEntire.length_newtonSlopesLt_mul (hf : f.IsEntire) (hg : g.IsEntire) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) (c : ℝ) :
    ((f * g).newtonSlopesLt v c).length =
      (f.newtonSlopesLt v c).length + (g.newtonSlopesLt v c).length := by
  simpa only [Multiset.coe_card, Multiset.card_add] using
    congrArg Multiset.card (hf.coe_newtonSlopesLt_mul v hb hv hg hf0 hg0 c)

end Entire

end PowerSeries
