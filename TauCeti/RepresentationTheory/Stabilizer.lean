/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.RepresentationTheory.Quotient
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Pointwise stabilizers of subsets and generic vectors in spans

Let `ρ` be a linear representation of a group `G` on a module `V`. For a subset `s ⊆ V`, the
pointwise stabilizer `⨅ u ∈ s, ρ.stabilizer u` coincides with the pointwise stabilizer of the
linear span `Submodule.span R s`.

When `V` is a vector space over a field `K` and the effective quotient `G ⧸ ρ.ker` is finite of
order at most `ENat.card K` (in particular whenever `K` is infinite and `G ⧸ ρ.ker` is finite),
this pointwise stabilizer is already the stabilizer of a *single* vector `v ∈ Submodule.span K s`.
Indeed, the identity coset lies in the image of `⨅ u ∈ s, ρ.stabilizer u` in `G ⧸ ρ.ker`, so there
are strictly fewer than `Nat.card (G ⧸ ρ.ker)` cosets outside that image, and each such coset cuts
out a proper subspace of `Submodule.span K s`; the union-of-subspaces lemma
`Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt` then produces a vector in the span avoiding
all of them.

In invariant theory this reduces Steinberg's theorem for the pointwise stabilizer of an arbitrary
subset or subspace to the stabilizer of a single vector.

## Main results

* `Representation.ker_le_stabilizer`: the kernel of `ρ` fixes every vector.
* `Representation.biInf_stabilizer_span`: the pointwise stabilizer of `Submodule.span R s` equals
  the pointwise stabilizer of `s`.
* `Representation.exists_mem_span_stabilizer_eq_biInf`: if `Nat.card (G ⧸ ρ.ker) ≤ ENat.card K`,
  some vector in `Submodule.span K s` has stabilizer `⨅ u ∈ s, ρ.stabilizer u`.
* `Representation.exists_mem_span_stabilizer_eq_biInf_of_infinite`: the same conclusion over any
  infinite field when `G ⧸ ρ.ker` is finite.
* `Representation.exists_mem_stabilizer_eq_biInf` and
  `Representation.exists_mem_stabilizer_eq_biInf_of_infinite`: specialization to submodules of `V`.

## References

* R. Steinberg, *Differential equations invariant under finite reflection groups*,
  Trans. Amer. Math. Soc. **112** (1964), 392–400, Corollary 1.6.
* G. I. Lehrer and D. E. Taylor, *Unitary Reflection Groups*, Cambridge University Press (2009),
  Theorem 9.44.
-/

public section

namespace Representation

section Semiring

variable {R G V : Type*} [Semiring R] [Group G] [AddCommMonoid V] [Module R V]
  (ρ : Representation R G V)

/-- Every element in the kernel of a representation fixes every vector. -/
theorem ker_le_stabilizer (v : V) : ρ.ker ≤ ρ.stabilizer v := fun _ hg ↦ by
  rw [mem_stabilizer, MonoidHom.mem_ker.mp hg, one_apply_eq_self]

/-- The pointwise stabilizer of the linear span of `s` equals the pointwise stabilizer of `s`. -/
@[simp]
theorem biInf_stabilizer_span (s : Set V) :
    (⨅ v ∈ Submodule.span R s, ρ.stabilizer v) = ⨅ u ∈ s, ρ.stabilizer u := by
  refine le_antisymm (le_iInf₂ fun u hu ↦ iInf₂_le u (Submodule.subset_span hu)) ?_
  refine le_iInf₂ fun v hv ↦ ?_
  induction hv using Submodule.span_induction with
  | mem u hu => exact iInf₂_le u hu
  | zero => simp [stabilizer_zero]
  | add x y _ _ hx hy => exact (le_inf hx hy).trans (ρ.le_stabilizer_add x y)
  | smul r x _ hx => exact hx.trans (ρ.le_stabilizer_smul r x)

end Semiring

section Field

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V)

/-- **Generic vector for a pointwise stabilizer.** Let `ρ` be a linear representation of `G` on a
`K`-vector space `V` whose effective quotient `G ⧸ ρ.ker` is finite of cardinality at most
`ENat.card K`. Then for every subset `s ⊆ V`, there is a vector `v ∈ Submodule.span K s` whose
stabilizer equals the pointwise stabilizer `⨅ u ∈ s, ρ.stabilizer u`. -/
theorem exists_mem_span_stabilizer_eq_biInf [Finite (G ⧸ ρ.ker)]
    (hcard : (Nat.card (G ⧸ ρ.ker) : ENat) ≤ ENat.card K) (s : Set V) :
    ∃ v ∈ Submodule.span K s, ρ.stabilizer v = ⨅ u ∈ s, ρ.stabilizer u := by
  classical
  let := Fintype.ofFinite (G ⧸ ρ.ker)
  set H : Subgroup G := ⨅ u ∈ s, ρ.stabilizer u
  set W : Submodule K V := Submodule.span K s
  have hker : ρ.ker ≤ H := le_iInf₂ fun u _ ↦ ρ.ker_le_stabilizer u
  -- Cosets outside the image of `H` in `G ⧸ ρ.ker`; the identity coset is excluded.
  let T : Finset (G ⧸ ρ.ker) :=
    Finset.univ.filter fun q ↦ q ∉ H.map (QuotientGroup.mk' ρ.ker)
  have h1_notMem : (1 : G ⧸ ρ.ker) ∉ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    exact ⟨1, H.one_mem, map_one _⟩
  have hT_lt : (T.card : ENat) < ENat.card K := by
    refine lt_of_lt_of_le ?_ hcard
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Nat.cast_lt.mpr (Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ T,
        fun h ↦ h1_notMem (h.symm ▸ Finset.mem_univ 1)⟩))
  let p (q : {q : G ⧸ ρ.ker // q ∈ T}) : Submodule K W :=
    ((ρ.ofQuotient ρ.ker q.1).fixedSubmodule).comap W.subtype
  have hp_ne_top (q : {q : G ⧸ ρ.ker // q ∈ T}) : p q ≠ ⊤ := by
    obtain ⟨g, hg_eq⟩ := QuotientGroup.mk'_surjective ρ.ker q.1
    have hg_notMem : g ∉ H := fun hgH ↦
      (Finset.mem_filter.mp q.2).2 ⟨g, hgH, hg_eq⟩
    simp only [H, Subgroup.mem_iInf, mem_stabilizer, not_forall] at hg_notMem
    obtain ⟨u, hu, hgu⟩ := hg_notMem
    intro htop
    have hu_mem : (⟨u, Submodule.subset_span hu⟩ : W) ∈ p q := htop ▸ Submodule.mem_top
    dsimp only [p] at hu_mem
    rw [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_fixedSubmodule_iff,
      ← hg_eq] at hu_mem
    exact hgu ((ρ.ofQuotient_coe_apply ρ.ker g u).symm.trans hu_mem)
  have hcard_attach : ((Finset.univ : Finset {q // q ∈ T}).card : ENat) < ENat.card K := by
    rwa [Finset.card_univ, Fintype.card_coe]
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p hp_ne_top
    hcard_attach
  obtain ⟨v, hv⟩ := Set.exists_of_ssubset hss
  refine ⟨v.1, v.2, le_antisymm (fun g hg ↦ ?_) ?_⟩
  · by_contra hgH
    have hqT : QuotientGroup.mk' ρ.ker g ∈ T := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rintro ⟨h, hhH, hmk⟩
      have hdiff : h⁻¹ * g ∈ ρ.ker := by
        rw [← QuotientGroup.ker_mk' ρ.ker, MonoidHom.mem_ker, map_mul, map_inv, hmk,
          inv_mul_cancel]
      exact hgH (by simpa [mul_assoc] using H.mul_mem hhH (hker hdiff))
    have hv_mem : v ∈ p ⟨QuotientGroup.mk' ρ.ker g, hqT⟩ := by
      dsimp only [p]
      rw [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_fixedSubmodule_iff]
      exact (ρ.ofQuotient_coe_apply ρ.ker g v.1).trans hg
    exact hv.2 (Set.mem_iUnion₂.mpr ⟨⟨_, hqT⟩, Finset.mem_univ _, hv_mem⟩)
  · dsimp only [H]
    rw [← ρ.biInf_stabilizer_span s]
    exact iInf₂_le v.1 v.2

/-- Over an infinite field, if the effective quotient `G ⧸ ρ.ker` is finite, every subset `s ⊆ V`
admits a vector in `Submodule.span K s` whose stabilizer equals `⨅ u ∈ s, ρ.stabilizer u`. -/
theorem exists_mem_span_stabilizer_eq_biInf_of_infinite [Infinite K] [Finite (G ⧸ ρ.ker)]
    (s : Set V) :
    ∃ v ∈ Submodule.span K s, ρ.stabilizer v = ⨅ u ∈ s, ρ.stabilizer u :=
  ρ.exists_mem_span_stabilizer_eq_biInf (by simp) s

/-- For a submodule `U` of `V`, if `Nat.card (G ⧸ ρ.ker) ≤ ENat.card K`, there is a vector `v ∈ U`
whose stabilizer equals the pointwise stabilizer `⨅ u ∈ U, ρ.stabilizer u`. -/
theorem exists_mem_stabilizer_eq_biInf [Finite (G ⧸ ρ.ker)]
    (hcard : (Nat.card (G ⧸ ρ.ker) : ENat) ≤ ENat.card K) (U : Submodule K V) :
    ∃ v ∈ U, ρ.stabilizer v = ⨅ u ∈ U, ρ.stabilizer u := by
  simpa [Submodule.span_eq] using ρ.exists_mem_span_stabilizer_eq_biInf hcard (U : Set V)

/-- Over an infinite field, if `G ⧸ ρ.ker` is finite, every submodule `U` of `V` contains a vector
whose stabilizer equals the pointwise stabilizer of `U`. -/
theorem exists_mem_stabilizer_eq_biInf_of_infinite [Infinite K] [Finite (G ⧸ ρ.ker)]
    (U : Submodule K V) :
    ∃ v ∈ U, ρ.stabilizer v = ⨅ u ∈ U, ρ.stabilizer u :=
  ρ.exists_mem_stabilizer_eq_biInf (by simp) U

end Field

end Representation
