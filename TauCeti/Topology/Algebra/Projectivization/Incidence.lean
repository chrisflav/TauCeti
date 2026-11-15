/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Opens
public import TauCeti.Topology.Algebra.Projectivization.ZeroLocus

/-!
# Base change, fibers, and the open full-rank locus of projective incidence families

A map into the coefficient space of homogeneous equations determines a family of projective
zero loci, with the subspace topology from the product of the parameter space and projective
space. For a continuous coefficient map its projection is proper. In particular, a coefficient
path gives a compact family over the closed interval, even when some fibers are singular or
empty.

`ComplexProjectiveFamily.pullbackHomeomorph` identifies reparametrization with the topological
fiber product, retaining both projections. `ComplexProjectiveFamily.fiberHomeomorph` identifies
each actual fiber of the projection with the existing projective zero locus. These comparisons
do not require smoothness or a choice of projective representatives.

Complementing the closed bad-rank locus `TauCeti.complexProjectiveBadRankLocus`, the open subset
`TauCeti.complexProjectiveFullRankParams N d` (bundled as `TopologicalSpace.Opens` in
`TauCeti.complexProjectiveFullRankParamsOpens N d`) consists of the coefficient families whose cone
Jacobian is surjective at every point of their projective zero locus. Coordinate linear subspaces
of any codimension at most `N` and Fermat hypersurfaces of any positive degree provide explicit
full-rank families.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Lecture 14 (incidence correspondences).
-/

public section

open MvPolynomial Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

variable {N : ℕ} {ι A B D : Type*} {d : ι → ℕ}

/-- In `ℂ⁰` there are no lines, so the universal incidence variety is empty. -/
@[simp]
theorem complexProjectiveIncidence_of_fin_zero (d : ι → ℕ) :
    complexProjectiveIncidence 0 d = ∅ :=
  Set.eq_empty_of_isEmpty _

/-- The family of projective zero loci associated to a coefficient map `c`, with the subspace
topology from the product of its parameter space and the native projective space. -/
def complexProjectiveFamily (c : B → ∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) :
    Set (B × ℙ ℂ (Fin N → ℂ)) :=
  Prod.map c id ⁻¹' complexProjectiveIncidence N d

/-- Membership in a projective family is membership in the zero locus at that parameter. -/
@[simp]
theorem mem_complexProjectiveFamily
    {c : B → ∀ i, homogeneousSubmodule (Fin N) ℂ (d i)} {x : B × ℙ ℂ (Fin N → ℂ)} :
    x ∈ complexProjectiveFamily c ↔
      x.2 ∈ complexProjectiveZeroLocus fun i ↦ (c x.1 i : MvPolynomial (Fin N) ℂ) := by
  rw [complexProjectiveFamily, Set.mem_preimage, mem_complexProjectiveIncidence]
  rfl

/-- In `ℂ⁰` there are no lines, so every projective family is empty. -/
@[simp]
theorem complexProjectiveFamily_of_fin_zero
    (c : B → ∀ i, homogeneousSubmodule (Fin 0) ℂ (d i)) :
    complexProjectiveFamily c = ∅ :=
  Set.eq_empty_of_isEmpty _

/-- The family over the coefficient space itself is the original incidence variety. -/
@[simp]
theorem complexProjectiveFamily_id :
    complexProjectiveFamily (id : (∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) → _) =
      complexProjectiveIncidence N d := by
  ext x
  simp only [mem_complexProjectiveFamily, mem_complexProjectiveIncidence, id_eq]

/-! ### The open full-rank parameter locus -/

section FullRank

variable (N) in
/-- The **full-rank parameter locus** in the space of homogeneous polynomial families of degrees `d`
in `N` variables: the families `c` whose cone Jacobian is surjective at every nonzero common zero
(equivalently, at every point of `TauCeti.complexProjectiveZeroLocus`). -/
def complexProjectiveFullRankParams (d : ι → ℕ) :
    Set (∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) :=
  {c | ∀ v : Fin N → ℂ, v ≠ 0 → (∀ i, eval v (c i : MvPolynomial (Fin N) ℂ) = 0) →
    (jacobiMatrixAt (fun i ↦ (c i : MvPolynomial (Fin N) ℂ)) v).mulVec.Surjective}

@[simp]
theorem mem_complexProjectiveFullRankParams
    {c : ∀ i, homogeneousSubmodule (Fin N) ℂ (d i)} :
    c ∈ complexProjectiveFullRankParams N d ↔
      ∀ v : Fin N → ℂ, v ≠ 0 → (∀ i, eval v (c i : MvPolynomial (Fin N) ℂ) = 0) →
        (jacobiMatrixAt (fun i ↦ (c i : MvPolynomial (Fin N) ℂ)) v).mulVec.Surjective :=
  Iff.rfl

/-- A coefficient family lies in `TauCeti.complexProjectiveFullRankParams` if and only if its cone
Jacobian is surjective at a representative of every point of its projective zero locus. -/
theorem mem_complexProjectiveFullRankParams_iff_forall_zeroLocus
    {c : ∀ i, homogeneousSubmodule (Fin N) ℂ (d i)} :
    c ∈ complexProjectiveFullRankParams N d ↔
      ∀ L ∈ complexProjectiveZeroLocus (fun i ↦ (c i : MvPolynomial (Fin N) ℂ)),
        (jacobiMatrixAt (fun i ↦ (c i : MvPolynomial (Fin N) ℂ)) L.rep).mulVec.Surjective := by
  have hc : ∀ i, (c i : MvPolynomial (Fin N) ℂ).IsHomogeneous (d i) :=
    fun i ↦ (mem_homogeneousSubmodule _ _).mp (c i).2
  refine ⟨fun h L hL ↦ h L.rep L.rep_ne_zero
    ((mem_complexProjectiveZeroLocus_iff_eval_rep hc L).mp hL), fun h v hv hz ↦ ?_⟩
  let L := Projectivization.mk ℂ v hv
  have hL : L ∈ complexProjectiveZeroLocus fun i ↦ (c i : MvPolynomial (Fin N) ℂ) :=
    (complexProjectiveZeroLocus_mk_iff hc v hv).mpr hz
  exact (mulVec_surjective_jacobiMatrixAt_iff_of_mk_eq_mk hc L.rep_ne_zero hv L.mk_rep).mp (h L hL)

/-- The full-rank parameter locus is the complement of the projection of the bad-rank locus. -/
theorem complexProjectiveFullRankParams_eq_compl_image_fst_badRankLocus (d : ι → ℕ) :
    complexProjectiveFullRankParams N d =
      (Prod.fst '' complexProjectiveBadRankLocus N d)ᶜ := by
  ext c
  rw [mem_complexProjectiveFullRankParams_iff_forall_zeroLocus, Set.mem_compl_iff, Set.mem_image]
  constructor
  · rintro h ⟨⟨c', L⟩, hbad, rfl⟩
    obtain ⟨hL, hrank⟩ := mem_complexProjectiveBadRankLocus.mp hbad
    exact hrank (h L (mem_complexProjectiveIncidence.mp hL))
  · intro h L hL
    by_contra hrank
    exact h ⟨(c, L), mem_complexProjectiveBadRankLocus.mpr
      ⟨mem_complexProjectiveIncidence.mpr hL, hrank⟩, rfl⟩

/-- The full-rank parameter locus is open in the coefficient space. -/
theorem isOpen_complexProjectiveFullRankParams (d : ι → ℕ) :
    IsOpen (complexProjectiveFullRankParams N d) :=
  isOpen_setOfPred_forall_mulVec_surjective_jacobiMatrixAt d

variable (N) in
/-- The full-rank parameter locus bundled as a `TopologicalSpace.Opens` of the coefficient space. -/
def complexProjectiveFullRankParamsOpens (d : ι → ℕ) :
    TopologicalSpace.Opens (∀ i, homogeneousSubmodule (Fin N) ℂ (d i)) :=
  ⟨complexProjectiveFullRankParams N d, isOpen_complexProjectiveFullRankParams d⟩

@[simp]
theorem coe_complexProjectiveFullRankParamsOpens (d : ι → ℕ) :
    (complexProjectiveFullRankParamsOpens N d : Set (∀ i, homogeneousSubmodule (Fin N) ℂ (d i))) =
      complexProjectiveFullRankParams N d :=
  (rfl)

@[simp]
theorem mem_complexProjectiveFullRankParamsOpens
    {c : ∀ i, homogeneousSubmodule (Fin N) ℂ (d i)} :
    c ∈ complexProjectiveFullRankParamsOpens N d ↔ c ∈ complexProjectiveFullRankParams N d :=
  Iff.rfl

/-- In `0` variables there are no nonzero vectors, so every coefficient family vacuously has full
Jacobian rank. -/
@[simp]
theorem complexProjectiveFullRankParams_of_fin_zero (d : ι → ℕ) :
    complexProjectiveFullRankParams 0 d = Set.univ :=
  Set.eq_univ_of_forall fun _ v hv ↦ (hv (Subsingleton.elim v 0)).elim

/-- With no equations (`[IsEmpty ι]`), every coefficient family has surjective cone Jacobian. -/
@[simp]
theorem complexProjectiveFullRankParams_of_isEmpty [IsEmpty ι] (d : ι → ℕ) :
    complexProjectiveFullRankParams N d = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ y ↦ ⟨0, Subsingleton.elim _ y⟩

/-- **Coordinate complete intersections have full Jacobian rank.** Any family of distinct coordinate
linear forms `X (e k)` along an injection `e : ι ↪ Fin N` lies in
`TauCeti.complexProjectiveFullRankParams N (fun _ ↦ 1)`. -/
theorem coordinateSubspace_mem_complexProjectiveFullRankParams (e : ι ↪ Fin N) :
    (fun k ↦ ⟨X (e k), isHomogeneous_X ℂ (e k)⟩ :
      ∀ _ : ι, homogeneousSubmodule (Fin N) ℂ 1) ∈
        complexProjectiveFullRankParams N (fun _ ↦ 1) := by
  classical
  intro v _ _ y
  refine ⟨Function.extend e y 0, funext fun k ↦ ?_⟩
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (e k)]
  · simp [jacobiMatrixAt_apply, pderiv_X, e.injective.extend_apply]
  · intro j _ hj
    simp [jacobiMatrixAt_apply, pderiv_X, hj.symm]
  · simp

/-- **Fermat hypersurfaces have full Jacobian rank.** For a single equation of positive degree `m`,
the Fermat polynomial `∑ j, X j ^ m` has surjective cone Jacobian at every nonzero vector, hence
lies in `TauCeti.complexProjectiveFullRankParams`. -/
theorem sum_X_pow_mem_complexProjectiveFullRankParams [Unique ι] {d : ι → ℕ}
    (hd : d default ≠ 0) :
    (fun k ↦ ⟨∑ j : Fin N, (X j : MvPolynomial (Fin N) ℂ) ^ d k,
      Submodule.sum_mem _ fun j _ ↦ by
        rw [mem_homogeneousSubmodule]
        simpa using (isHomogeneous_X ℂ j).pow (d k)⟩) ∈
        complexProjectiveFullRankParams N d := by
  intro v hv _
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  rw [mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero]
  refine ⟨j, ?_⟩
  rw [map_sum, map_sum, Finset.sum_eq_single j]
  · rw [pderiv_pow, pderiv_X_self, mul_one, map_mul, map_natCast, map_pow, eval_X]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hd) (pow_ne_zero _ hj)
  · intro l _ hlj
    rw [pderiv_pow, pderiv_X_of_ne hlj, mul_zero, map_zero]
  · simp

end FullRank

namespace ComplexProjectiveFamily

variable (c : B → ∀ i, homogeneousSubmodule (Fin N) ℂ (d i))

/-- Reparametrization of a projective family, preserving its projective coordinate. -/
def baseChange (f : A → B) : complexProjectiveFamily (c ∘ f) → complexProjectiveFamily c :=
  fun x ↦ ⟨(f x.1.1, x.1.2), x.2⟩

/-- Reparametrization applies the parameter map and leaves the projective coordinate fixed. -/
@[simp]
theorem coe_baseChange (f : A → B) (x : complexProjectiveFamily (c ∘ f)) :
    (baseChange c f x : B × ℙ ℂ (Fin N → ℂ)) = (f x.1.1, x.1.2) :=
  (rfl)

/-- Reparametrization by the identity is the identity on the total space. -/
@[simp]
theorem baseChange_id (x : complexProjectiveFamily c) : baseChange c id x = x := by
  apply Subtype.ext
  rfl

/-- Successive reparametrizations agree with reparametrization by the composite map. -/
@[simp]
theorem baseChange_comp (f : A → B) (g : D → A)
    (x : complexProjectiveFamily (c ∘ f ∘ g)) :
    baseChange c f (baseChange (c ∘ f) g x) = baseChange c (f ∘ g) x :=
  (rfl)

variable [TopologicalSpace A] [TopologicalSpace B]

/-- The total space of a continuous projective family is closed in the product. -/
theorem isClosed (hc : Continuous c) : IsClosed (complexProjectiveFamily c) :=
  (isClosed_complexProjectiveIncidence d).preimage (hc.prodMap continuous_id)

/-- Projection of a continuous projective family to its parameter space is proper. -/
theorem isProperMap_fst (hc : Continuous c) :
    IsProperMap fun x : complexProjectiveFamily c ↦ x.1.1 :=
  isProperMap_fst_of_compactSpace.restrict (isClosed c hc)

/-- A continuous projective family over a compact parameter space has compact total space. -/
theorem isCompact_univ [CompactSpace B] (hc : Continuous c) :
    IsCompact (Set.univ : Set (complexProjectiveFamily c)) := by
  simpa using (isProperMap_fst c hc).isCompact_preimage
    (K := Set.univ) _root_.isCompact_univ

/-- A continuous change of parameter induces a continuous map of total spaces; continuity of
the coefficient map itself is unnecessary here. -/
theorem continuous_baseChange {f : A → B} (hf : Continuous f) : Continuous (baseChange c f) :=
  ((hf.comp continuous_subtype_val.fst).prodMk continuous_subtype_val.snd).subtype_mk _

/-- Reparametrization is the topological fiber product of the original family projection and
the parameter map. The comparison retains the parameter and the projective point. -/
def pullbackHomeomorph (f : A → B) (hf : Continuous f) :
    complexProjectiveFamily (c ∘ f) ≃ₜ
      {z : A × complexProjectiveFamily c // f z.1 = z.2.1.1} := by
  refine
    { toFun := fun x ↦ ⟨(x.1.1, baseChange c f x), rfl⟩
      invFun := fun z ↦ ⟨(z.1.1, z.1.2.1.2), ?_⟩
      left_inv := fun _ ↦ rfl
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rw [mem_complexProjectiveFamily]
    simpa only [Function.comp_apply, z.2] using mem_complexProjectiveFamily.mp z.1.2.2
  · intro z
    rcases z with ⟨⟨a, ⟨⟨b, L⟩, hL⟩⟩, h⟩
    dsimp only at h
    cases h
    rfl
  · exact (continuous_subtype_val.fst.prodMk (continuous_baseChange c hf)).subtype_mk _
  · exact (continuous_subtype_val.fst.prodMk
      (continuous_subtype_val.comp continuous_subtype_val.snd).snd).subtype_mk _

/-- The first projection of the pullback comparison is the unchanged parameter. -/
@[simp]
theorem pullbackHomeomorph_apply_fst (f : A → B) (hf : Continuous f)
    (x : complexProjectiveFamily (c ∘ f)) : (pullbackHomeomorph c f hf x).1.1 = x.1.1 :=
  (rfl)

/-- The second projection of the pullback comparison is the reparametrization map. -/
@[simp]
theorem pullbackHomeomorph_apply_snd (f : A → B) (hf : Continuous f)
    (x : complexProjectiveFamily (c ∘ f)) :
    (pullbackHomeomorph c f hf x).1.2 = baseChange c f x :=
  (rfl)

/-- The inverse pullback comparison retains the new parameter and the projective coordinate. -/
@[simp]
theorem coe_pullbackHomeomorph_symm_apply (f : A → B) (hf : Continuous f)
    (z : {z : A × complexProjectiveFamily c // f z.1 = z.2.1.1}) :
    ((pullbackHomeomorph c f hf).symm z : A × ℙ ℂ (Fin N → ℂ)) = (z.1.1, z.1.2.1.2) :=
  (rfl)

/-- The projective zero locus at `b` is homeomorphic to the actual fiber of the family
projection over `b`, with its subspace topology. -/
def fiberHomeomorph (b : B) :
    (complexProjectiveZeroLocus fun i ↦ (c b i : MvPolynomial (Fin N) ℂ)) ≃ₜ
      {x : complexProjectiveFamily c // x.1.1 = b} := by
  refine
    { toFun := fun L ↦ ⟨⟨(b, L.1), mem_complexProjectiveFamily.mpr L.2⟩, rfl⟩
      invFun := fun x ↦ ⟨x.1.1.2, ?_⟩
      left_inv := fun _ ↦ rfl
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · simpa only [x.2] using mem_complexProjectiveFamily.mp x.1.2
  · intro x
    rcases x with ⟨⟨⟨b', L⟩, hL⟩, h⟩
    dsimp only at h
    cases h
    rfl
  · exact ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _
  · exact ((continuous_subtype_val.comp continuous_subtype_val).snd).subtype_mk _

/-- The fiber comparison inserts the specified parameter and the original projective point. -/
@[simp]
theorem coe_fiberHomeomorph_apply (b : B)
    (L : complexProjectiveZeroLocus fun i ↦ (c b i : MvPolynomial (Fin N) ℂ)) :
    ((fiberHomeomorph c b L).1 : B × ℙ ℂ (Fin N → ℂ)) = (b, L.1) :=
  (rfl)

/-- The inverse fiber comparison forgets the parameter and retains the projective point. -/
@[simp]
theorem coe_fiberHomeomorph_symm_apply (b : B)
    (x : {x : complexProjectiveFamily c // x.1.1 = b}) :
    ((fiberHomeomorph c b).symm x : ℙ ℂ (Fin N → ℂ)) = x.1.1.2 :=
  (rfl)

/-- Reparametrization commutes with the identifications of both fibers with their common
projective zero locus. -/
theorem baseChange_fiberHomeomorph (f : A → B) (a : A)
    (L : complexProjectiveZeroLocus fun i ↦ (c (f a) i : MvPolynomial (Fin N) ℂ)) :
    baseChange c f (fiberHomeomorph (c ∘ f) a L).1 = (fiberHomeomorph c (f a) L).1 :=
  (rfl)

end ComplexProjectiveFamily

end TauCeti
