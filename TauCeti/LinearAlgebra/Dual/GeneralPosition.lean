/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.LinearAlgebra.LinearIndependent.GeneralPosition

import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear forms in general position

A family `L : κ → Module.Dual K V` of linear forms on a finite-dimensional `K`-vector space `V`
is in **general position** (`Module.Dual.IsGeneralPosition`) if every subfamily of cardinality at
most `finrank K V` is linearly independent. Requiring independence for all subfamilies of size at
most `finrank K V`, rather than only those of size equal to `finrank K V`, ensures that families
with fewer than `finrank K V` forms must themselves be linearly independent instead of satisfying
the condition vacuously. When `κ` has at least `n` elements, general position on `Fin n → K` agrees
with `TauCeti.InGeneralPosition` on the coefficient vectors
(`Module.Dual.isGeneralPosition_iff_inGeneralPosition`).

In the Subspace Theorem for forms in general position (Vojta 1987; Bombieri–Gubler, Definition
7.2.8 and Theorem 7.2.9), places carrying fewer than `card ι` forms must be completed to a basis of
the dual of `ι → K` by adding coordinate projections `LinearMap.proj` without changing the existing
forms. `Module.Dual.exists_index_extendProj` provides this completion from `Module.Basis.extendLe`.

## Main results

* `Module.Dual.IsGeneralPosition`: every subfamily of at most `finrank K V` forms is linearly
  independent.
* `Module.Dual.isGeneralPosition_iff_linearIndependent_of_card_le` and
  `Module.Dual.isGeneralPosition_iff_linearIndependent`: for at most `finrank K V` forms, general
  position is linear independence.
* `Module.Dual.isGeneralPosition_iff_forall_card_eq`: when `finrank K V ≤ ENat.card κ`, checking
  subfamilies of exact size `finrank K V` suffices.
* `Module.Dual.isGeneralPosition_iff_inGeneralPosition`: equivalence with
  `TauCeti.InGeneralPosition` of the coefficient vectors on `Fin n → K` whenever
  `n ≤ ENat.card κ`; an example at the end shows why the cardinality hypothesis is necessary.
* `Module.Dual.IsGeneralPosition.comp_injective`, `Module.Dual.IsGeneralPosition.smul`, and
  `Module.Dual.IsGeneralPosition.comp_linearEquiv`: invariance under restriction, nonzero
  rescaling, and linear equivalences.
* `Module.Dual.exists_index_extendProj`: any linearly independent family of forms on `ι → K`
  extends to a basis of `Module.Dual K (ι → K)` by adding coordinate projections.
* `Module.Dual.isGeneralPosition_option_sum_proj`: the coordinate projections on `ι → K` together
  with their sum are in general position.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Definition 7.2.8 and Theorem 7.2.9.
* P. Vojta, *Diophantine Approximations and Value Distribution Theory*, Lecture Notes in Mathematics
  1239, Springer (1987).
-/

public section

open Function Module

namespace Module.Dual

section Basic

variable {K V κ : Type*} [Field K] [AddCommMonoid V] [Module K V]

/-- A family `L : κ → Module.Dual K V` of linear forms on a vector space `V` is in **general
position** if every finite subfamily of cardinality at most `finrank K V` is linearly independent.
On an infinite-dimensional space `finrank K V = 0`, so the predicate is vacuous, matching Mathlib's
convention for `Module.finrank`. -/
def IsGeneralPosition (L : κ → Dual K V) : Prop :=
  ∀ s : Finset κ, s.card ≤ finrank K V → LinearIndependent K fun i : s ↦ L i

variable {L : κ → Dual K V}

/-- Characterization of general position by linear independence of all finite subfamilies of size
at most `finrank K V`. -/
theorem isGeneralPosition_iff :
    IsGeneralPosition L ↔
      ∀ s : Finset κ, s.card ≤ finrank K V → LinearIndependent K fun i : s ↦ L i :=
  (Iff.rfl)

/-- Every finite subfamily of cardinality at most `finrank K V` of a family in general position is
linearly independent. -/
theorem IsGeneralPosition.linearIndependent (hL : IsGeneralPosition L) {s : Finset κ}
    (hs : s.card ≤ finrank K V) : LinearIndependent K fun i : s ↦ L i :=
  hL s hs

/-- Precomposing a general-position family with an injection from a finite type of cardinality at
most `finrank K V` gives a linearly independent family. -/
theorem IsGeneralPosition.linearIndependent_comp {ι : Type*} [Fintype ι]
    (hL : IsGeneralPosition L) {e : ι → κ} (he : Injective e)
    (hcard : Fintype.card ι ≤ finrank K V) : LinearIndependent K (L ∘ e) := by
  classical
  have hle : (Finset.univ.image e).card ≤ finrank K V :=
    (Finset.card_image_le).trans (by simpa using hcard)
  let f : ι → Finset.univ.image e := fun i ↦ ⟨e i, Finset.mem_image_of_mem e (Finset.mem_univ i)⟩
  have hf : Injective f := fun _ _ h ↦ he (congrArg Subtype.val h)
  exact (hL.linearIndependent hle).comp f hf

/-- Any linearly independent family of linear forms is in general position. -/
theorem isGeneralPosition_of_linearIndependent (hL : LinearIndependent K L) :
    IsGeneralPosition L :=
  fun _ _ ↦ hL.comp Subtype.val Subtype.val_injective

/-- For a finite family of at most `finrank K V` linear forms, general position is equivalent to
linear independence. -/
theorem isGeneralPosition_iff_linearIndependent_of_card_le [Fintype κ]
    (hcard : Fintype.card κ ≤ finrank K V) :
    IsGeneralPosition L ↔ LinearIndependent K L := by
  refine ⟨fun hL ↦ ?_, isGeneralPosition_of_linearIndependent⟩
  exact hL.linearIndependent_comp injective_id hcard

/-- For a family of `finrank K V` linear forms, general position is linear independence. -/
theorem isGeneralPosition_iff_linearIndependent [Fintype κ]
    (hcard : Fintype.card κ = finrank K V) :
    IsGeneralPosition L ↔ LinearIndependent K L :=
  isGeneralPosition_iff_linearIndependent_of_card_le hcard.le

/-- When `κ` has at least `finrank K V` elements, a family `L : κ → Dual K V` is in general
position if and only if every subfamily of exact cardinality `finrank K V` is linearly
independent. -/
theorem isGeneralPosition_iff_forall_card_eq (hcard : (finrank K V : ℕ∞) ≤ ENat.card κ) :
    IsGeneralPosition L ↔
      ∀ s : Finset κ, s.card = finrank K V → LinearIndependent K fun i : s ↦ L i := by
  refine ⟨fun hL s hs ↦ hL s hs.le, fun hL s hs ↦ ?_⟩
  have hex : ∃ t : Finset κ, s ⊆ t ∧ t.card = finrank K V := by
    rcases finite_or_infinite κ with _ | _
    · have : Fintype κ := Fintype.ofFinite κ
      have hn : finrank K V ≤ Fintype.card κ := by
        simpa [ENat.card_eq_coe_fintype_card] using hcard
      exact Finset.exists_superset_card_eq hs hn
    · exact Infinite.exists_superset_card_eq s (finrank K V) hs
  obtain ⟨t, hst, ht⟩ := hex
  let g : s → t := fun i ↦ ⟨i.1, hst i.2⟩
  have hg : Injective g := fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)
  exact (hL t ht).comp g hg

/-- Restricting a general-position family along an injection preserves general position. -/
theorem IsGeneralPosition.comp_injective {κ' : Type*} (hL : IsGeneralPosition L) {f : κ' → κ}
    (hf : Injective f) : IsGeneralPosition (L ∘ f) := by
  classical
  intro s hs
  have himg : (s.image f).card ≤ finrank K V := Finset.card_image_le.trans hs
  let g : s → s.image f := fun i ↦ ⟨f i.1, Finset.mem_image_of_mem f i.2⟩
  have hg : Injective g := fun _ _ h ↦ Subtype.ext (hf (congrArg Subtype.val h))
  exact (hL.linearIndependent himg).comp g hg

/-- Rescaling every form in a general-position family by a nonzero scalar preserves general
position. -/
theorem IsGeneralPosition.smul (hL : IsGeneralPosition L) {c : κ → K} (hc : ∀ i, c i ≠ 0) :
    IsGeneralPosition fun i ↦ c i • L i := by
  intro s hs
  let u : s → Kˣ := fun i ↦ Units.mk0 (c i.1) (hc i.1)
  have hu := (hL.linearIndependent hs).units_smul u
  convert hu using 1
  ext i x
  simp [u]

/-- Precomposing a general-position family with a linear equivalence preserves general position. -/
theorem IsGeneralPosition.comp_linearEquiv {W : Type*} [AddCommMonoid W] [Module K W]
    (hL : IsGeneralPosition L) (e : W ≃ₗ[K] V) :
    IsGeneralPosition fun i ↦ (L i).comp e.toLinearMap := by
  intro s hs
  have hs' : s.card ≤ finrank K V := by rwa [← e.finrank_eq]
  have hli : LinearIndependent K (e.dualMap ∘ fun i : s ↦ L i) :=
    (hL.linearIndependent hs').map' e.dualMap.toLinearMap e.dualMap.ker
  convert hli using 1
  ext i x
  simp [LinearEquiv.dualMap_apply]

/-- A general-position family on a space of dimension at least `2` is injective: no two distinct
indices carry the same linear form. -/
theorem IsGeneralPosition.injective (hdim : 2 ≤ finrank K V) (hL : IsGeneralPosition L) :
    Injective L := by
  classical
  intro i j hij
  by_contra hne
  have hli := hL.linearIndependent (s := {i, j}) (by rw [Finset.card_pair hne]; exact hdim)
  exact hne (congrArg Subtype.val
    (hli.injective (a₁ := ⟨i, Finset.mem_insert_self i _⟩)
      (a₂ := ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j)⟩) hij))

end Basic

/-- Every form in a general-position family on a nontrivial finite-dimensional space is nonzero. -/
theorem IsGeneralPosition.ne_zero {K V κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {L : κ → Dual K V} (hL : IsGeneralPosition L)
    (i : κ) : L i ≠ 0 := by
  have hpos : 1 ≤ finrank K V := finrank_pos
  have hli := hL.linearIndependent (s := {i}) (by simpa using hpos)
  exact hli.ne_zero ⟨i, Finset.mem_singleton_self i⟩

/-- The coordinate projections `LinearMap.proj i` span the dual module `Dual R (ι → R)`. -/
theorem span_range_proj {R ι : Type*} [CommSemiring R] [Finite ι] :
    Submodule.span R (Set.range (LinearMap.proj (R := R) (φ := fun _ : ι ↦ R))) = ⊤ := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  refine top_unique fun f _ ↦ ?_
  have hf : f = ∑ i, f (Pi.basisFun R ι i) • LinearMap.proj (R := R) i := by
    apply LinearMap.ext
    intro x
    conv_lhs => rw [← (Pi.basisFun R ι).sum_repr x]
    simp [map_sum, map_smul, Pi.basisFun_repr, mul_comm]
  rw [hf]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

section CoordinateSpace

variable {K ι κ : Type*} [Field K]

/-- On `ι → K`, general position says that every finite subfamily of cardinality at most `card ι`
is linearly independent. -/
theorem isGeneralPosition_pi_iff [Fintype ι] {L : κ → Dual K (ι → K)} :
    IsGeneralPosition L ↔
      ∀ s : Finset κ, s.card ≤ Fintype.card ι → LinearIndependent K fun i : s ↦ L i := by
  simp [IsGeneralPosition, finrank_fintype_fun_eq_card]

/-- Evaluating forms on `ι → K` at the standard basis is a linear equivalence from the dual space
to `ι → K`, so linear independence of forms is equivalent to linear independence of their
coefficient vectors. -/
theorem linearIndependent_iff_eval_basisFun [Finite ι] {ι' : Type*}
    (L : ι' → Dual K (ι → K)) :
    LinearIndependent K L ↔ LinearIndependent K fun j i ↦ L j (Pi.basisFun K ι i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let e : Dual K (ι → K) ≃ₗ[K] (ι → K) :=
    (Pi.basisFun K ι).dualBasis.equivFun
  have he : ∀ f : Dual K (ι → K), e f = fun i ↦ f (Pi.basisFun K ι i) := fun f ↦ by
    ext i
    simp [e, Basis.equivFun_apply, Basis.dualBasis_repr]
  simpa [Function.comp_def, he] using (e.toLinearMap.linearIndependent_iff e.ker).symm

/-- A family of linear forms on `Fin n → K` in general position has coefficient vectors in general
position in the sense of `TauCeti.InGeneralPosition`. -/
theorem IsGeneralPosition.inGeneralPosition {n : ℕ} {L : κ → Dual K (Fin n → K)}
    (hL : IsGeneralPosition L) :
    TauCeti.InGeneralPosition fun j i ↦ L j (Pi.basisFun K (Fin n) i) := by
  rw [TauCeti.inGeneralPosition_iff_det_ne_zero]
  intro e he
  have hli : LinearIndependent K (L ∘ e) :=
    hL.linearIndependent_comp he (by simp [finrank_fintype_fun_eq_card])
  rw [linearIndependent_iff_eval_basisFun] at hli
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.linearIndependent_row_iff.mp hli)

/-- For a family of at least `n` linear forms on `Fin n → K`, `Module.Dual.IsGeneralPosition` is
equivalent to `TauCeti.InGeneralPosition` of the coefficient vectors. -/
theorem isGeneralPosition_iff_inGeneralPosition {n : ℕ} {L : κ → Dual K (Fin n → K)}
    (hcard : (n : ℕ∞) ≤ ENat.card κ) :
    IsGeneralPosition L ↔
      TauCeti.InGeneralPosition fun j i ↦ L j (Pi.basisFun K (Fin n) i) := by
  refine ⟨IsGeneralPosition.inGeneralPosition, fun hL ↦ ?_⟩
  have hfin : (finrank K (Fin n → K) : ℕ∞) ≤ ENat.card κ := by
    simpa [finrank_fintype_fun_eq_card] using hcard
  rw [isGeneralPosition_iff_forall_card_eq hfin]
  intro s hs
  rw [finrank_fintype_fun_eq_card, Fintype.card_fin] at hs
  exact (linearIndependent_iff_eval_basisFun (fun i : s ↦ L i)).mpr (hL.linearIndependent s hs)

/-- **Completing a linearly independent family of forms by coordinate projections**: any linearly
independent family `L : κ → Dual K (ι → K)` extends to a linearly independent family
`l : ι → Dual K (ι → K)` along an embedding `e : κ ↪ ι`, with every added form equal to a
coordinate projection `LinearMap.proj j`. -/
theorem exists_index_extendProj [Finite ι] {L : κ → Dual K (ι → K)} (hL : LinearIndependent K L) :
    ∃ (e : κ ↪ ι) (l : ι → Dual K (ι → K)),
      LinearIndependent K l ∧ (∀ k : κ, l (e k) = L k) ∧
        ∀ i : ι, i ∉ Set.range e → ∃ j : ι, l i = LinearMap.proj j := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let s : Set (Dual K (ι → K)) := Set.range L
  let t : Set (Dual K (ι → K)) := s ∪ Set.range (LinearMap.proj (R := K) (φ := fun _ : ι ↦ K))
  have hs : LinearIndepOn K id s := hL.linearIndepOn_id
  have hst : s ⊆ t := Set.subset_union_left
  have ht : ⊤ ≤ Submodule.span K t := by
    rw [← span_range_proj (R := K) (ι := ι)]
    exact Submodule.span_mono Set.subset_union_right
  let b := Basis.extendLe hs hst ht
  have : Finite (hs.extend hst) := Module.Finite.finite_basis b
  have : Fintype (hs.extend hst) := Fintype.ofFinite _
  have hcard : Fintype.card (hs.extend hst) = Fintype.card ι := by
    rw [← finrank_eq_card_basis b, Subspace.dual_finrank_eq, finrank_fintype_fun_eq_card]
  let φ : hs.extend hst ≃ ι := Fintype.equivOfCardEq hcard
  let e : κ ↪ ι :=
    ⟨fun k ↦ φ ⟨L k, hs.subset_extend hst ⟨k, rfl⟩⟩, fun k₁ k₂ h ↦
      hL.injective (congrArg Subtype.val (φ.injective h))⟩
  refine ⟨e, b ∘ φ.symm, b.linearIndependent.comp φ.symm φ.symm.injective,
    fun k ↦ ?_, fun i hi ↦ ?_⟩
  · have hek : e k = φ ⟨L k, hs.subset_extend hst ⟨k, rfl⟩⟩ := rfl
    rw [Function.comp_apply, hek, φ.symm_apply_apply]
    exact Basis.extendLe_apply_self hs hst ht _
  · have hmem : (φ.symm i).1 ∈ t := hs.extend_subset hst (φ.symm i).2
    rcases hmem with ⟨k, hk⟩ | ⟨j, hj⟩
    · exfalso
      apply hi
      refine ⟨k, ?_⟩
      have hsub : (⟨L k, hs.subset_extend hst ⟨k, rfl⟩⟩ : hs.extend hst) = φ.symm i :=
        Subtype.ext hk
      have hek : e k = φ ⟨L k, hs.subset_extend hst ⟨k, rfl⟩⟩ := rfl
      rw [hek, hsub, φ.apply_symm_apply]
    · exact ⟨j, by simpa [b] using hj.symm⟩

/-- The coordinate projections on `ι → K` together with their sum form a family of `card ι + 1`
linear forms in general position. The index `none` labels the sum `∑ i, LinearMap.proj i` and
`some i` labels `LinearMap.proj i`. -/
theorem isGeneralPosition_option_sum_proj [Fintype ι] :
    IsGeneralPosition fun o : Option ι ↦
      o.elim (∑ i : ι, LinearMap.proj (R := K) (φ := fun _ : ι ↦ K) i) LinearMap.proj := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Lfin : Option (Fin (Fintype.card ι)) → Dual K (Fin (Fintype.card ι) → K) :=
    fun o ↦ o.elim (∑ i, LinearMap.proj i) LinearMap.proj
  have hfin : IsGeneralPosition Lfin := by
    rw [isGeneralPosition_iff_inGeneralPosition (by simp [ENat.card_eq_coe_fintype_card])]
    convert TauCeti.inGeneralPosition_coords_add_sum (K := K) (n := Fintype.card ι) using 1
    ext o j
    cases o with
    | none => simp [Lfin]
    | some i => simp [Lfin, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have hcomp := (hfin.comp_linearEquiv (LinearEquiv.piCongrLeft' K (fun _ ↦ K) e)).comp_injective
    (Option.map_injective e.injective)
  convert hcomp using 1
  funext o
  apply LinearMap.ext
  intro x
  cases o with
  | none =>
    simp only [Function.comp_apply, Option.map_none, Option.elim_none, LinearMap.coe_comp,
      LinearEquiv.coe_coe, LinearMap.sum_apply, LinearMap.proj_apply,
      LinearEquiv.piCongrLeft'_apply, Lfin]
    exact (Equiv.sum_comp e.symm x).symm
  | some i =>
    simp [Lfin]

end CoordinateSpace

/-! ### Examples -/

/-- Over any field, the three binary linear forms `X₀`, `X₁`, and `X₀ + X₁` are in general
position. -/
example {K : Type*} [Field K] :
    IsGeneralPosition fun o : Option (Fin 2) ↦
      o.elim (LinearMap.proj (R := K) (φ := fun _ : Fin 2 ↦ K) 0 + LinearMap.proj 1)
        LinearMap.proj := by
  simpa [Fin.sum_univ_two] using isGeneralPosition_option_sum_proj (K := K) (ι := Fin 2)

/-- The cardinality hypothesis `n ≤ ENat.card κ` in
`Module.Dual.isGeneralPosition_iff_inGeneralPosition` cannot be dropped: a single zero form on
`Fin 2 → ℚ` satisfies `TauCeti.InGeneralPosition` vacuously (there is no injection
`Fin 2 → Fin 1`), yet fails `Module.Dual.IsGeneralPosition`. -/
example :
    TauCeti.InGeneralPosition (fun (_ : Fin 1) (i : Fin 2) ↦ (0 : Dual ℚ (Fin 2 → ℚ))
        (Pi.basisFun ℚ (Fin 2) i)) ∧
      ¬ IsGeneralPosition (fun _ : Fin 1 ↦ (0 : Dual ℚ (Fin 2 → ℚ))) := by
  refine ⟨?_, fun hL ↦ hL.ne_zero (0 : Fin 1) rfl⟩
  rw [TauCeti.inGeneralPosition_iff_det_ne_zero]
  intro e he
  have hcard := Fintype.card_le_of_injective e he
  simp at hcard

end Module.Dual
