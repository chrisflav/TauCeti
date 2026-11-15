/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Basic.Finite.Sum

/-!
# Compact supports in relative CW complexes

A compact subset of a relative CW complex meets only finitely many open cells outside the
base. Closing those cells downward along the finitely many lower-dimensional cells meeting each
boundary places every finite set of cells, and hence every compact subset of the complex, inside a
finite subcomplex (`TauCeti.exists_subcomplex_finite_of_finite_cells`,
`TauCeti.exists_subcomplex_finite_of_isCompact`). Consequently every compact subset lies in a
skeleton of finite dimension, even when the complex is infinite-dimensional. The base itself need
not be compact or finite-dimensional. So the preimages of the skeleta under a continuous map into
the complex absorb every compact set (`TauCeti.exists_subset_preimageSkeleton_of_isCompact`).

These are the compact-support statements used to pass from skeletal homology to homology
of the whole pair. They do not require local finiteness of the CW structure. The key weak-topology
criterion is that a subset meeting each open cell in a finite set is closed (respectively
discrete) as soon as its intersection with the base is.

## References

* A. Hatcher, *Algebraic Topology*, Appendix, Proposition A.1.
-/

public section

open Set Topology Topology.RelCWComplex

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D S : Set X}
  [RelCWComplex C D]

/-- A subset of a relative CW complex is closed if it meets each open cell in a finite set and
meets the base in a closed set. -/
lemma isClosed_of_finite_inter_openCell (hSC : S ⊆ C) (hSD : IsClosed (S ∩ D))
    (hS : ∀ n (i : cell C n), (S ∩ openCell n i).Finite) : IsClosed S :=
  isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hSC hSD
    fun n _ i ↦ Or.inl (hS n i).isClosed

/-- A subset of a relative CW complex is discrete if it meets each open cell in a finite set and
meets the base in a discrete set. -/
lemma isDiscrete_of_finite_inter_openCell (hSC : S ⊆ C) (hSD : IsDiscrete (S ∩ D))
    (hS : ∀ n (i : cell C n), (S ∩ openCell n i).Finite) : IsDiscrete S := by
  refine isDiscrete_iff_forall_mem_exists_isClosed.2 fun T hTS ↦ ?_
  obtain ⟨U, hU, hUT⟩ :=
    isDiscrete_iff_forall_mem_exists_isClosed.1 hSD (T ∩ D) (inter_subset_inter_left _ hTS)
  -- The part of `T` off the base is closed by the previous lemma; on the base, `U` cuts out `T`.
  have hTD : IsClosed (T \ D) :=
    isClosed_of_finite_inter_openCell (sdiff_subset.trans (hTS.trans hSC))
      (by simpa only [sdiff_inter_self] using isClosed_empty)
      fun n i ↦ (hS n i).subset (inter_subset_inter_left _ (sdiff_subset.trans hTS))
  refine ⟨U ∩ D ∪ T \ D, (hU.inter (isClosedBase C)).union hTD, ?_⟩
  ext x
  have hx := Set.ext_iff.1 hUT x
  have := @hTS x
  simp only [mem_union, mem_inter_iff, mem_sdiff] at hx ⊢
  tauto

/-- A compact subset of the ambient space meets only finitely many relative open cells.
There is no local-finiteness or dimension assumption, and the base is excluded from the cell
indexing. -/
theorem finite_setOf_nonempty_inter_openCell_of_isCompact {K : Set X} (hK : IsCompact K) :
    {a : Σ n, cell C n | (K ∩ openCell a.1 a.2).Nonempty}.Finite := by
  let A := {a : Σ n, cell C n | (K ∩ openCell a.1 a.2).Nonempty}
  -- Pick a point `x a` of `K` in each open cell `a` that `K` meets.
  choose x hxK hxO using fun a : A ↦ a.2
  have hx {a : A} {m : ℕ} {j : cell C m} (h : x a ∈ openCell m j) : a.1 = ⟨m, j⟩ :=
    eq_of_not_disjoint_openCell (not_disjoint_iff.2 ⟨x a, hxO a, h⟩)
  have hxinj : Function.Injective x := fun a b hab ↦ Subtype.ext (hx (hab ▸ hxO b))
  have hSC : range x ⊆ C := range_subset_iff.2 fun a ↦ openCell_subset_complex _ _ (hxO a)
  have hSD : (range x ∩ D).Finite := finite_empty.subset <| by
    rintro _ ⟨⟨a, rfl⟩, hD⟩
    exact disjoint_left.1 (disjointBase _ _) (hxO a) hD
  have hS (n : ℕ) (i : cell C n) : (range x ∩ openCell n i).Finite := by
    refine Set.Subsingleton.finite ?_
    rintro _ ⟨⟨a, rfl⟩, ha⟩ _ ⟨⟨b, rfl⟩, hb⟩
    exact congrArg x (Subtype.ext ((hx ha).trans (hx hb).symm))
  -- So the chosen points form a closed discrete subset of the compact set `K`.
  have hcompact : IsCompact (range x) :=
    hK.of_isClosed_subset (isClosed_of_finite_inter_openCell hSC hSD.isClosed hS)
      (range_subset_iff.2 hxK)
  have : Finite A := (finite_range_iff hxinj).1
    (hcompact.finite (isDiscrete_of_finite_inter_openCell hSC hSD.isDiscrete hS))
  exact Set.toFinite A

/-- Every compact subset of a relative CW complex is contained in a skeleton of finite
relative dimension. The skeleton contains the entire base, so no restriction on the base is
needed. -/
theorem exists_subset_skeletonLT_of_isCompact {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ n : ℕ, K ⊆ (skeletonLT C (n : ℕ∞) : Set X) := by
  obtain ⟨N, hN⟩ :=
    ((finite_setOf_nonempty_inter_openCell_of_isCompact (C := C) hK).image Sigma.fst).bddAbove
  refine ⟨N + 1, fun x hx ↦ ?_⟩
  have hxC := hKC hx
  rw [← union_iUnion_openCell_eq_complex (C := C)] at hxC
  rcases hxC with hxD | hxC
  · exact (skeletonLT C _).base_subset hxD
  · obtain ⟨m, i, hxi⟩ := by simpa only [mem_iUnion] using hxC
    refine mem_skeletonLT_iff.2 (Or.inr ⟨m, ?_, i, hxi⟩)
    exact_mod_cast Nat.lt_succ_of_le (hN ⟨⟨m, i⟩, ⟨x, hx, hxi⟩, rfl⟩)

/-- **The skeletal filtration absorbs compact sets.** If `f` is continuous with values in the
complex `C`, every compact subset of `E` lies in the preimage of some skeleton, since its image is
compact and so lies in a finite skeleton. -/
lemma exists_subset_preimageSkeleton_of_isCompact {E : Type*} [TopologicalSpace E] {f : E → X}
    (hf : Continuous f) (hfC : Set.range f ⊆ C) {K : Set E} (hK : IsCompact K) :
    ∃ q, K ⊆ preimageSkeleton C f q := by
  obtain ⟨n, hn⟩ := exists_subset_skeletonLT_of_isCompact (hK.image hf)
    ((Set.image_subset_range f K).trans hfC)
  refine ⟨n, fun x hx ↦ ?_⟩
  rw [preimageSkeleton_natCast]
  exact skeletonLT_mono le_self_add (hn (mem_image_of_mem f hx))

/-- Adjoining a single `n`-cell `i` whose boundary already lies in a subcomplex `E₀` produces a
subcomplex `E₀ ∪ openCell n i`, finite when `E₀` is. -/
private lemma exists_subcomplex_adjoin_cell (E₀ : Subcomplex C) [RelCWComplex.Finite (E₀ : Set X)]
    {n : ℕ} (i : cell C n) (hfront : cellFrontier n i ⊆ E₀) :
    ∃ E : Subcomplex C, RelCWComplex.Finite (E : Set X) ∧ i ∈ E.I n := by
  let I' (m : ℕ) : Set (cell C m) := E₀.I m ∪ {j | (⟨m, j⟩ : Σ k, cell C k) = ⟨n, i⟩}
  let E : Subcomplex C := Subcomplex.mk' C ((E₀ : Set X) ∪ openCell n i) I'
    (fun m ⟨j, hj⟩ ↦ by
      rcases hj with hj | hj
      · exact (E₀.closedCell_subset_of_mem hj).trans subset_union_left
      · obtain ⟨rfl, hj'⟩ := Sigma.mk.inj_iff.1 hj
        cases eq_of_heq hj'
        exact cellFrontier_union_openCell_eq_closedCell m j ▸ union_subset_union_left _ hfront)
    (by
      refine Subset.antisymm (union_subset (E₀.base_subset.trans subset_union_left)
        (iUnion₂_subset fun m ⟨j, hj⟩ ↦ ?_)) (union_subset ?_ ?_)
      · rcases hj with hj | hj
        · exact (E₀.openCell_subset_of_mem hj).trans subset_union_left
        · obtain ⟨rfl, hj'⟩ := Sigma.mk.inj_iff.1 hj
          cases eq_of_heq hj'
          exact subset_union_right
      · rw [← E₀.union]
        exact union_subset subset_union_left (iUnion₂_subset fun m ⟨j, hj⟩ ↦
          subset_union_of_subset_right
            (subset_iUnion₂ (s := fun k (l : I' k) ↦ openCell k (l : cell C k)) m ⟨j, .inl hj⟩) _)
      · exact subset_union_of_subset_right
          (subset_iUnion₂ (s := fun k (l : I' k) ↦ openCell k (l : cell C k)) n ⟨i, .inr rfl⟩) _)
  have : _root_.Finite (Σ m, cell (E₀ : Set X) m) :=
    RelCWComplex.finite_cells_of_finite (C := (E₀ : Set X))
  refine ⟨E, RelCWComplex.finite_of_finite_cells <| Finite.of_surjective
    (f := Sum.elim (fun p : Σ m, cell (E₀ : Set X) m ↦ ⟨p.1, p.2.1, .inl p.2.2⟩)
      (fun _ : Unit ↦ ⟨n, i, .inr rfl⟩)) ?_, .inr rfl⟩
  rintro ⟨m, j, hj | hj⟩
  · exact ⟨.inl ⟨m, j, hj⟩, rfl⟩
  · obtain ⟨rfl, hj'⟩ := Sigma.mk.inj_iff.1 hj
    cases eq_of_heq hj'
    exact ⟨.inr (), rfl⟩

/-- Every single cell of a relative CW complex lies in a finite subcomplex: by strong induction on
its dimension, its boundary lies in the base together with finitely many lower-dimensional closed
cells, which lie in a finite union of finite subcomplexes. -/
private lemma exists_subcomplex_finite_cell (n : ℕ) (i : cell C n) :
    ∃ E : Subcomplex C, RelCWComplex.Finite (E : Set X) ∧ i ∈ E.I n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell (C := C) n i
    let idx := (Finset.range n).sigma J
    choose F hFfin hFmem using fun p : idx ↦
      ih p.1.1 (Finset.mem_range.1 (Finset.mem_sigma.1 p.2).1) p.1.2
    let E₀ : Subcomplex C := Finset.univ.sup F
    have : RelCWComplex.Finite (E₀ : Set X) := Subcomplex.finite_finsetSup _ _ fun p _ ↦ hFfin p
    refine exists_subcomplex_adjoin_cell E₀ i fun x hx ↦ ?_
    rcases hJ hx with hxD | hxJ
    · exact E₀.base_subset hxD
    · obtain ⟨m, hmn, j, hj, hxj⟩ := by simpa only [mem_iUnion, exists_prop] using hxJ
      let p : idx := ⟨⟨m, j⟩, Finset.mem_sigma.2 ⟨Finset.mem_range.2 hmn, hj⟩⟩
      exact E₀.closedCell_subset_of_mem
        (Subcomplex.le_iff_I_subset.1 (Finset.le_sup (f := F) (Finset.mem_univ p)) m (hFmem p)) hxj

/-- **Every finite set of cells of a relative CW complex lies in a finite subcomplex**
(Hatcher, Proposition A.1). -/
theorem exists_subcomplex_finite_of_finite_cells {A : Set (Σ n, cell C n)} (hA : A.Finite) :
    ∃ E : Subcomplex C, RelCWComplex.Finite (E : Set X) ∧ ∀ c ∈ A, c.2 ∈ E.I c.1 := by
  choose F hFfin hFmem using fun c : A ↦ exists_subcomplex_finite_cell (C := C) c.1.1 c.1.2
  refine ⟨hA.toFinset.attach.sup fun c ↦ F ⟨c.1, hA.mem_toFinset.1 c.2⟩,
    Subcomplex.finite_finsetSup _ _ fun c _ ↦ hFfin _, fun c hc ↦ ?_⟩
  have hc' : c ∈ hA.toFinset := hA.mem_toFinset.2 hc
  exact Subcomplex.le_iff_I_subset.1
    (Finset.le_sup (f := fun x : {x // x ∈ hA.toFinset} ↦ F ⟨x.1, hA.mem_toFinset.1 x.2⟩)
      (Finset.mem_attach _ ⟨c, hc'⟩))
    c.1 (hFmem ⟨c, hc⟩)

/-- **Every compact subset of a relative CW complex lies in a finite subcomplex**
(Hatcher, Proposition A.1). The subcomplex contains the entire base `D`, so no compactness or
finiteness hypothesis on `D` is needed. -/
theorem exists_subcomplex_finite_of_isCompact {K : Set X} (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ E : Subcomplex C, RelCWComplex.Finite (E : Set X) ∧ K ⊆ (E : Set X) := by
  obtain ⟨E, hEfin, hE⟩ := exists_subcomplex_finite_of_finite_cells
    (finite_setOf_nonempty_inter_openCell_of_isCompact (C := C) hK)
  refine ⟨E, hEfin, fun x hx ↦ ?_⟩
  have hxC := hKC hx
  rw [← union_iUnion_openCell_eq_complex (C := C)] at hxC
  rcases hxC with hxD | hxC
  · exact E.base_subset hxD
  · obtain ⟨m, i, hxi⟩ := by simpa only [mem_iUnion] using hxC
    exact E.openCell_subset_of_mem (hE ⟨m, i⟩ ⟨x, hx, hxi⟩) hxi

end TauCeti
