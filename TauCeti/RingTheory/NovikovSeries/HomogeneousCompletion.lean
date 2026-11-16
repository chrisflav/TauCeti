/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.RingTheory.NovikovSeries.Functoriality
public import TauCeti.RingTheory.NovikovSeries.Grading
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing

/-!
# Closed homogeneous pieces and graded completion of Novikov series

Let `N : H →+ ℝ` be a period homomorphism and `f : H → ι` a degree function on exponents. Each
support-restricted submodule `TauCeti.NovikovSeries.supported R N s` is closed in the period
topology, being an intersection of zero fibres of the locally constant coefficient maps
(`TauCeti.NovikovSeries.isClosed_supported`). In particular, every homogeneous piece
`TauCeti.NovikovSeries.gradeBy R N f i`, and likewise every nonnegative homogeneous piece
`TauCeti.NovikovSeries.nonnegGradeBy R N f i` inside `nonnegSubring R N`, is closed and therefore
complete.

For an additive degree function `f : H →+ ι` over a commutative ring `R`, the nonnegative
homogeneous pieces form a graded monoid (`TauCeti.NovikovSeries.nonnegGradeBy.gradedMonoid`),
yielding bilinear convolution maps
`nonnegGradeBy R N f i ⊗[R] nonnegGradeBy R N f j →ₗ[R] nonnegGradeBy R N f (i + j)`
(`TauCeti.NovikovSeries.nonnegGradeByMul`) and an injective `R`-algebra homomorphism
`DirectSum.coeAlgHom (nonnegGradeBy R N f) : (⨁ i, nonnegGradeBy R N f i) →ₐ[R] nonnegSubring R N`
with dense range (`TauCeti.NovikovSeries.coeAlgHom_nonnegGradeBy_injective`,
`TauCeti.NovikovSeries.denseRange_coeAlgHom_nonnegGradeBy`). Thus `nonnegSubring R N` is the
period-filtration completion of the algebraic graded subalgebra `⨁ i, nonnegGradeBy R N f i`
(`TauCeti.NovikovSeries.nonnegGradedCompletionPkg`), and analogously `NovikovSeries R H N` is the
completion of `⨁ i, gradeBy R N f i` (`TauCeti.NovikovSeries.gradedCompletionPkg`). The family of
homogeneous pieces is packaged as a Mathlib `CategoryTheory.GradedObject` in `ModuleCat R`
(`TauCeti.NovikovSeries.gradedObject` and `TauCeti.NovikovSeries.nonnegGradedObject`).

Period-rescaling pushforwards `map` and `mapNonnegSubring` send homogeneous pieces to homogeneous
pieces whenever a degree map commutes with the exponent homomorphism
(`TauCeti.NovikovSeries.map_mem_gradeBy` and
`TauCeti.NovikovSeries.mapNonnegSubring_mem_nonnegGradeBy`).

Finally, any element of the algebraic span `⨆ i, gradeBy R N f i` has support meeting only finitely
many degrees (`TauCeti.NovikovSeries.finite_image_support_of_mem_iSup_gradeBy`). Consequently,
whenever there exists a sequence of nonnegative-period exponents with pairwise distinct degrees and
periods tending to `+∞`, the resulting series lies in `nonnegSubring R N` but outside the algebraic
direct sum, so `⨁ i, nonnegGradeBy R N f i` is dense but proper in `nonnegSubring R N`
(`TauCeti.NovikovSeries.not_surjective_coeAlgHom_nonnegGradeBy`).

## Main definitions

* `TauCeti.NovikovSeries.nonnegGradeBy`: homogeneous nonnegative Novikov series of degree `i`.
* `TauCeti.NovikovSeries.gradeByMul` and `TauCeti.NovikovSeries.nonnegGradeByMul`: convolution maps
  on tensor products of homogeneous pieces.
* `TauCeti.NovikovSeries.gradedCompletionPkg` and
  `TauCeti.NovikovSeries.nonnegGradedCompletionPkg`: `AbstractCompletion` packages presenting
  `NovikovSeries R H N` and `nonnegSubring R N` as period completions of their algebraic graded
  subalgebras.
* `TauCeti.NovikovSeries.gradedObject` and `TauCeti.NovikovSeries.nonnegGradedObject`: the
  homogeneous pieces as `CategoryTheory.GradedObject ι (ModuleCat R)`.
* `TauCeti.NovikovSeries.seqSeries`: the characteristic series of a sequence of exponents whose
  periods tend to `+∞`.

## Main results

* `TauCeti.NovikovSeries.isClosed_supported`, `TauCeti.NovikovSeries.isClosed_gradeBy`, and
  `TauCeti.NovikovSeries.isClosed_nonnegGradeBy`: closedness of homogeneous pieces.
* `TauCeti.NovikovSeries.coeAlgHom_gradeBy_injective`,
  `TauCeti.NovikovSeries.coeAlgHom_nonnegGradeBy_injective`,
  `TauCeti.NovikovSeries.denseRange_coeAlgHom_gradeBy`, and
  `TauCeti.NovikovSeries.denseRange_coeAlgHom_nonnegGradeBy`: injectivity and density of the
  graded subalgebra inclusions.
* `TauCeti.NovikovSeries.map_mem_gradeBy` and
  `TauCeti.NovikovSeries.mapNonnegSubring_mem_nonnegGradeBy`: pushforward preserves homogeneity
  along a commuting degree square.
* `TauCeti.NovikovSeries.finite_image_support_of_mem_iSup_gradeBy` and
  `TauCeti.NovikovSeries.not_surjective_coeAlgHom_nonnegGradeBy`: properness of the algebraic
  direct sum when degrees diverge along a sequence of diverging nonnegative periods.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta, and K. Ono, *Lagrangian Intersection Floer Theory: Anomaly and
  Obstruction*, AMS/IP Studies in Advanced Mathematics 46 (2009), Chapter 3.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

open CategoryTheory Filter Function Set Topology
open scoped DirectSum TensorProduct

namespace TauCeti

namespace NovikovSeries

section Closed

variable {R H ι : Type*} [Ring R] [AddZeroClass H] {N : H →+ ℝ}

/-- The submodule of Novikov series supported in `s` is closed in the period topology, being an
intersection of zero fibres of the locally constant coefficient functions. -/
theorem isClosed_supported (s : Set H) :
    IsClosed (supported R N s : Set (NovikovSeries R H N)) := by
  have heq : (supported R N s : Set (NovikovSeries R H N)) =
      ⋂ h ∈ sᶜ, {a : NovikovSeries R H N | a.coeff h = 0} := by
    ext a
    simp only [SetLike.mem_coe, mem_supported, mem_iInter, mem_compl_iff, mem_ofPred_eq,
      subset_def, mem_support]
    constructor
    · intro ha h hs
      by_contra hne
      exact hs (ha h hne)
    · intro ha h hh
      by_contra hs
      exact hh (ha h hs)
  rw [heq]
  exact isClosed_biInter fun h _ => (isLocallyConstant_coeff h).isClosed_fiber 0

/-- Every homogeneous piece `gradeBy R N f i` is closed in the period topology. -/
theorem isClosed_gradeBy (f : H → ι) (i : ι) :
    IsClosed (gradeBy R N f i : Set (NovikovSeries R H N)) := by
  have heq : (gradeBy R N f i : Set (NovikovSeries R H N)) =
      (supported R N (f ⁻¹' {i}) : Set (NovikovSeries R H N)) := by
    ext a
    simp only [SetLike.mem_coe, mem_gradeBy_iff, mem_supported]
  rw [heq]
  exact isClosed_supported (f ⁻¹' {i})

/-- Every homogeneous piece `gradeBy R N f i` is complete for the induced period uniformity. -/
instance instCompleteSpaceGradeBy (f : H → ι) (i : ι) : CompleteSpace (gradeBy R N f i) :=
  (isClosed_gradeBy f i).completeSpace_coe

end Closed

section FiniteDegrees

variable {R H ι : Type*} [Semiring R] [AddZeroClass H] {N : H →+ ℝ}

/-- Every series in the algebraic span of the homogeneous pieces meets only finitely many
degrees. -/
theorem finite_image_support_of_mem_iSup_gradeBy {f : H → ι} {a : NovikovSeries R H N}
    (ha : a ∈ ⨆ i, gradeBy R N f i) : (f '' a.support).Finite := by
  refine Submodule.iSup_induction (motive := fun b => (f '' b.support).Finite) _ ha
    (fun i _ hb => (finite_singleton i).subset ?_)
    (by simp)
    (fun _ _ hb hc => (hb.union hc).subset ?_)
  · rintro _ ⟨h, hh, rfl⟩
    exact mem_gradeBy_iff.1 hb hh
  · rw [← image_union]
    exact image_mono (support_add_subset _ _)

end FiniteDegrees

section NonnegGradeBy

variable {R H ι : Type*} [CommRing R] [AddMonoid H] {N : H →+ ℝ}

variable (R N) in
/-- The `R`-submodule of nonnegative Novikov series homogeneous of degree `i` for `f : H → ι`. -/
def nonnegGradeBy (f : H → ι) (i : ι) : Submodule R (nonnegSubring R N) where
  carrier := {a | (a : NovikovSeries R H N) ∈ gradeBy R N f i}
  zero_mem' := zero_mem _
  add_mem' ha hb := add_mem ha hb
  smul_mem' r _ ha := Submodule.smul_mem (gradeBy R N f i) r ha

/-- A nonnegative Novikov series has degree `i` exactly when its coercion to `NovikovSeries`
does. -/
@[simp]
theorem mem_nonnegGradeBy_iff {f : H → ι} {i : ι} {a : nonnegSubring R N} :
    a ∈ nonnegGradeBy R N f i ↔ (a : NovikovSeries R H N) ∈ gradeBy R N f i := by
  rfl

/-- Every homogeneous piece of `nonnegSubring R N` is closed in the period topology. -/
theorem isClosed_nonnegGradeBy (f : H → ι) (i : ι) :
    IsClosed (nonnegGradeBy R N f i : Set (nonnegSubring R N)) :=
  (isClosed_gradeBy f i).preimage continuous_subtype_val

/-- Every homogeneous piece of `nonnegSubring R N` is complete for the induced period
uniformity. -/
instance instCompleteSpaceNonnegGradeBy (f : H → ι) (i : ι) :
    CompleteSpace (nonnegGradeBy R N f i) :=
  (isClosed_nonnegGradeBy f i).completeSpace_coe

/-- A monomial `r e^h` of nonnegative period lies in `nonnegGradeBy R N f (f h)`. -/
theorem single_mem_nonnegGradeBy (f : H → ι) {h : H} (hh : 0 ≤ N h) (r : R) :
    (⟨single h r, single_mem_nonnegSubring hh r⟩ : nonnegSubring R N) ∈
      nonnegGradeBy R N f (f h) :=
  single_mem_gradeBy f h r

/-- Homogeneous pieces of `nonnegSubring R N` of distinct degrees are independent. -/
theorem iSupIndep_nonnegGradeBy (f : H → ι) : iSupIndep (nonnegGradeBy R N f) := by
  intro i
  rw [Submodule.disjoint_def]
  intro a hai ha
  let emb : nonnegSubring R N →ₗ[R] NovikovSeries R H N :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : (⨆ (j) (_ : j ≠ i), nonnegGradeBy R N f j) ≤
      (⨆ (j) (_ : j ≠ i), gradeBy R N f j).comap emb :=
    iSup₂_le fun j hj _ hx => Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj hx)
  exact Subtype.ext <|
    (Submodule.disjoint_def.1 (iSupIndep_gradeBy (R := R) (N := N) f i)) (a : NovikovSeries R H N)
      hai (hle ha)

/-- For an additive degree function, the homogeneous pieces of `nonnegSubring R N` form a graded
monoid. -/
instance nonnegGradeBy.gradedMonoid [AddMonoid ι] (f : H →+ ι) :
    SetLike.GradedMonoid (nonnegGradeBy R N f) where
  one_mem := SetLike.one_mem_graded (A := gradeBy R N f)
  mul_mem _ _ _ _ ha hb := SetLike.mul_mem_graded (A := gradeBy R N f) ha hb

/-- An element of the algebraic span of the nonnegative homogeneous pieces lies in the algebraic
span of the homogeneous pieces of `NovikovSeries R H N`. -/
theorem coe_mem_iSup_gradeBy_of_mem_iSup_nonnegGradeBy {f : H → ι} {a : nonnegSubring R N}
    (ha : a ∈ ⨆ i, nonnegGradeBy R N f i) :
    (a : NovikovSeries R H N) ∈ ⨆ i, gradeBy R N f i :=
  Submodule.iSup_induction
    (motive := fun x : nonnegSubring R N => (x : NovikovSeries R H N) ∈ ⨆ i, gradeBy R N f i)
    _ ha (fun i _ hx => Submodule.mem_iSup_of_mem i hx) (zero_mem _)
    fun _ _ hx hy => add_mem hx hy

/-- Every element of the algebraic span of the homogeneous pieces of `nonnegSubring R N` has
support meeting only finitely many degrees. -/
theorem finite_image_support_of_mem_iSup_nonnegGradeBy {f : H → ι} {a : nonnegSubring R N}
    (ha : a ∈ ⨆ i, nonnegGradeBy R N f i) : (f '' (a : NovikovSeries R H N).support).Finite :=
  finite_image_support_of_mem_iSup_gradeBy (coe_mem_iSup_gradeBy_of_mem_iSup_nonnegGradeBy ha)

end NonnegGradeBy

section ConvolutionAndCompletion

variable {R H ι : Type*} [CommRing R] [AddMonoid H] {N : H →+ ℝ}

variable (R N) in
/-- The convolution map `gradeBy R N f i ⊗[R] gradeBy R N f j →ₗ[R] gradeBy R N f (i + j)`. -/
def gradeByMul [AddMonoid ι] (f : H →+ ι) (i j : ι) :
    gradeBy R N f i ⊗[R] gradeBy R N f j →ₗ[R] gradeBy R N f (i + j) :=
  TensorProduct.lift (DirectSum.gMulLHom (R := R) (A := fun k => gradeBy R N f k))

@[simp]
theorem coe_gradeByMul_tmul [AddMonoid ι] (f : H →+ ι) {i j : ι}
    (x : gradeBy R N f i) (y : gradeBy R N f j) :
    (gradeByMul R N f i j (x ⊗ₜ[R] y) : NovikovSeries R H N) = x * y := by
  rfl

variable (R N) in
/-- The convolution map
`nonnegGradeBy R N f i ⊗[R] nonnegGradeBy R N f j →ₗ[R] nonnegGradeBy R N f (i + j)`. -/
def nonnegGradeByMul [AddMonoid ι] (f : H →+ ι) (i j : ι) :
    nonnegGradeBy R N f i ⊗[R] nonnegGradeBy R N f j →ₗ[R] nonnegGradeBy R N f (i + j) :=
  TensorProduct.lift (DirectSum.gMulLHom (R := R) (A := fun k => nonnegGradeBy R N f k))

@[simp]
theorem coe_nonnegGradeByMul_tmul [AddMonoid ι] (f : H →+ ι) {i j : ι}
    (x : nonnegGradeBy R N f i) (y : nonnegGradeBy R N f j) :
    (nonnegGradeByMul R N f i j (x ⊗ₜ[R] y) : nonnegSubring R N) = x * y := by
  rfl

/-- The graded subalgebra inclusion `(⨁ i, gradeBy R N f i) →ₐ[R] NovikovSeries R H N` is
injective. -/
theorem coeAlgHom_gradeBy_injective [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    Injective (DirectSum.coeAlgHom (S := R) (gradeBy R N f)) :=
  (iSupIndep_gradeBy (R := R) (N := N) f).dfinsupp_lsum_injective

/-- The graded subalgebra inclusion `(⨁ i, nonnegGradeBy R N f i) →ₐ[R] nonnegSubring R N` is
injective. -/
theorem coeAlgHom_nonnegGradeBy_injective [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    Injective (DirectSum.coeAlgHom (S := R) (nonnegGradeBy R N f)) :=
  (iSupIndep_nonnegGradeBy (R := R) (N := N) f).dfinsupp_lsum_injective

/-- Every finitely supported nonnegative Novikov series lies in the span of the homogeneous pieces
of `nonnegSubring R N`. -/
theorem ofFinsupp_mem_iSup_nonnegGradeBy (f : H → ι) {x : H →₀ R}
    (hx : ofFinsupp x ∈ nonnegSubring R N) :
    (⟨ofFinsupp x, hx⟩ : nonnegSubring R N) ∈ ⨆ i, nonnegGradeBy R N f i := by
  have hx_nonneg : ∀ h ∈ x.support, 0 ≤ N h := fun h hh =>
    not_lt.1 fun hlt => (Finsupp.mem_support_iff.1 hh) (by
      simpa only [coeff_ofFinsupp] using mem_nonnegSubring.1 hx h hlt)
  have hsum : (⟨ofFinsupp x, hx⟩ : nonnegSubring R N) =
      ∑ h ∈ x.support.attach,
        (⟨single h.1 (x h.1), single_mem_nonnegSubring (hx_nonneg h.1 h.2) (x h.1)⟩ :
          nonnegSubring R N) := by
    ext h
    have hcoe : ((∑ g ∈ x.support.attach,
        (⟨single g.1 (x g.1), single_mem_nonnegSubring (hx_nonneg g.1 g.2) (x g.1)⟩ :
          nonnegSubring R N) : nonnegSubring R N) : NovikovSeries R H N) =
        ∑ g ∈ x.support.attach, single g.1 (x g.1) :=
      map_sum (nonnegSubring R N).subtype _ _
    rw [hcoe]
    simp only [coeff_ofFinsupp, coeff_sum]
    by_cases hh : h ∈ x.support
    · rw [Finset.sum_eq_single ⟨h, hh⟩
        (fun g _ hgh => coeff_single_of_ne (fun h' => hgh (Subtype.ext h'.symm)) _)
        (fun hnh => absurd (Finset.mem_attach _ _) hnh), coeff_single_same]
    · rw [Finsupp.notMem_support_iff.1 hh, Finset.sum_eq_zero]
      intro g _
      exact coeff_single_of_ne (by rintro rfl; exact hh g.2) _
  rw [hsum]
  exact Submodule.sum_mem _ fun h _ =>
    Submodule.mem_iSup_of_mem (f h.1) (single_mem_nonnegGradeBy f (hx_nonneg h.1 h.2) (x h.1))

/-- The graded subalgebra `⨁ i, gradeBy R N f i` is dense in `NovikovSeries R H N`. -/
theorem denseRange_coeAlgHom_gradeBy [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    DenseRange (DirectSum.coeAlgHom (S := R) (gradeBy R N f)) := by
  intro a
  refine mem_closure_of_tendsto (tendsto_ofFinsupp_trunc a) (Eventually.of_forall fun C => ?_)
  have hmem : ofFinsupp (trunc C a) ∈ ⨆ i, gradeBy R N f i :=
    ofFinsupp_mem_iSup_gradeBy f (trunc C a)
  rw [Submodule.iSup_eq_toSubmodule_range] at hmem
  exact hmem

/-- The graded subalgebra `⨁ i, nonnegGradeBy R N f i` is dense in `nonnegSubring R N`. -/
theorem denseRange_coeAlgHom_nonnegGradeBy [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    DenseRange (DirectSum.coeAlgHom (S := R) (nonnegGradeBy R N f)) := by
  intro a
  have htrunc (C : ℝ) : ofFinsupp (trunc C (a : NovikovSeries R H N)) ∈ nonnegSubring R N :=
    mem_nonnegSubring.2 <| mem_periodFiltration.1 <|
      ofFinsupp_trunc_mem_periodFiltration C (mem_periodFiltration.2 (mem_nonnegSubring.1 a.2))
  have htend : Tendsto
      (fun C => (⟨ofFinsupp (trunc C (a : NovikovSeries R H N)), htrunc C⟩ : nonnegSubring R N))
      atTop (𝓝 a) := by
    rw [tendsto_subtype_rng]
    exact tendsto_ofFinsupp_trunc (a : NovikovSeries R H N)
  refine mem_closure_of_tendsto htend (Eventually.of_forall fun C => ?_)
  have hmem : (⟨ofFinsupp (trunc C (a : NovikovSeries R H N)), htrunc C⟩ : nonnegSubring R N) ∈
      ⨆ i, nonnegGradeBy R N f i :=
    ofFinsupp_mem_iSup_nonnegGradeBy f (htrunc C)
  rw [Submodule.iSup_eq_toSubmodule_range] at hmem
  exact hmem

variable (R N) in
/-- The uniform structure on `⨁ i, gradeBy R N f i` induced by its inclusion into
`NovikovSeries R H N`. -/
@[instance_reducible]
def directSumGradeByUniformSpace [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    UniformSpace (⨁ i, gradeBy R N f i) :=
  UniformSpace.comap (DirectSum.coeAlgHom (S := R) (gradeBy R N f)) inferInstance

theorem isUniformInducing_coeAlgHom_gradeBy [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    @IsUniformInducing _ _ (directSumGradeByUniformSpace R N f) _
      (DirectSum.coeAlgHom (S := R) (gradeBy R N f)) := by
  exact @IsUniformInducing.mk _ _ (directSumGradeByUniformSpace R N f) _ _ rfl

variable (R N) in
/-- `NovikovSeries R H N` as the period completion of the graded subalgebra
`⨁ i, gradeBy R N f i`. -/
@[expose]
def gradedCompletionPkg [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    @AbstractCompletion (⨁ i, gradeBy R N f i) (directSumGradeByUniformSpace R N f) :=
  @AbstractCompletion.mk _ (directSumGradeByUniformSpace R N f) (NovikovSeries R H N)
    (DirectSum.coeAlgHom (S := R) (gradeBy R N f)) inferInstance inferInstance inferInstance
    (isUniformInducing_coeAlgHom_gradeBy f) (denseRange_coeAlgHom_gradeBy f)

theorem gradedCompletionPkg_coe [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    @AbstractCompletion.coe _ (directSumGradeByUniformSpace R N f)
        (gradedCompletionPkg R N f) =
      DirectSum.coeAlgHom (S := R) (gradeBy R N f) := by
  rfl

variable (R N) in
/-- The uniform structure on `⨁ i, nonnegGradeBy R N f i` induced by its inclusion into
`nonnegSubring R N`. -/
@[instance_reducible]
def directSumNonnegGradeByUniformSpace [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    UniformSpace (⨁ i, nonnegGradeBy R N f i) :=
  UniformSpace.comap (DirectSum.coeAlgHom (S := R) (nonnegGradeBy R N f)) inferInstance

theorem isUniformInducing_coeAlgHom_nonnegGradeBy [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    @IsUniformInducing _ _ (directSumNonnegGradeByUniformSpace R N f) _
      (DirectSum.coeAlgHom (S := R) (nonnegGradeBy R N f)) := by
  exact @IsUniformInducing.mk _ _ (directSumNonnegGradeByUniformSpace R N f) _ _ rfl

variable (R N) in
/-- `nonnegSubring R N` as the period completion of the graded subalgebra
`⨁ i, nonnegGradeBy R N f i`. -/
@[expose]
def nonnegGradedCompletionPkg [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    @AbstractCompletion (⨁ i, nonnegGradeBy R N f i) (directSumNonnegGradeByUniformSpace R N f) :=
  @AbstractCompletion.mk _ (directSumNonnegGradeByUniformSpace R N f) (nonnegSubring R N)
    (DirectSum.coeAlgHom (S := R) (nonnegGradeBy R N f)) inferInstance inferInstance inferInstance
    (isUniformInducing_coeAlgHom_nonnegGradeBy f) (denseRange_coeAlgHom_nonnegGradeBy f)

theorem nonnegGradedCompletionPkg_coe [AddMonoid ι] [DecidableEq ι] (f : H →+ ι) :
    @AbstractCompletion.coe _ (directSumNonnegGradeByUniformSpace R N f)
        (nonnegGradedCompletionPkg R N f) =
      DirectSum.coeAlgHom (S := R) (nonnegGradeBy R N f) := by
  rfl

end ConvolutionAndCompletion

section GradedObject

universe u v w

/-- The homogeneous pieces `gradeBy R N f i` packaged as a Mathlib
`CategoryTheory.GradedObject ι (ModuleCat R)`. -/
def gradedObject (R : Type u) [CommRing R] {H : Type v} [AddZeroClass H] (N : H →+ ℝ)
    {ι : Type w} (f : H → ι) : CategoryTheory.GradedObject ι (ModuleCat.{max u v} R) :=
  fun i => ModuleCat.of R (gradeBy R N f i)

@[simp]
theorem gradedObject_apply (R : Type u) [CommRing R] {H : Type v} [AddZeroClass H] (N : H →+ ℝ)
    {ι : Type w} (f : H → ι) (i : ι) :
    gradedObject R N f i = ModuleCat.of R (gradeBy R N f i) := by
  rfl

/-- The nonnegative homogeneous pieces `nonnegGradeBy R N f i` packaged as a Mathlib
`CategoryTheory.GradedObject ι (ModuleCat R)`. -/
def nonnegGradedObject (R : Type u) [CommRing R] {H : Type v} [AddMonoid H] (N : H →+ ℝ)
    {ι : Type w} (f : H → ι) : CategoryTheory.GradedObject ι (ModuleCat.{max u v} R) :=
  fun i => ModuleCat.of R (nonnegGradeBy R N f i)

@[simp]
theorem nonnegGradedObject_apply (R : Type u) [CommRing R] {H : Type v} [AddMonoid H] (N : H →+ ℝ)
    {ι : Type w} (f : H → ι) (i : ι) :
    nonnegGradedObject R N f i = ModuleCat.of R (nonnegGradeBy R N f i) := by
  rfl

end GradedObject

section GradedPushforward

variable {R S H H' ι ι' : Type*}

/-- A period-rescaling pushforward maps homogeneous series of degree `i` into homogeneous series of
degree `ψ i` whenever the degree functions commute with the exponent homomorphism:
`∀ h, f' (φ h) = ψ (f h)`. -/
theorem map_mem_gradeBy [Semiring R] [Semiring S] [AddZeroClass H] [AddZeroClass H']
    {N : H →+ ℝ} {N' : H' →+ ℝ} (ρ : R →+ S) (φ : H →+ H')
    (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) {f : H → ι} {f' : H' → ι'} {ψ : ι → ι'}
    (hdeg : ∀ h, f' (φ h) = ψ (f h)) {i : ι} {a : NovikovSeries R H N}
    (ha : a ∈ gradeBy R N f i) :
    map ρ φ hφ a ∈ gradeBy S N' f' (ψ i) := by
  rw [mem_gradeBy_iff]
  intro h' hh'
  obtain ⟨h, hh, rfl⟩ := support_map_subset ρ φ hφ a hh'
  rw [mem_preimage, mem_singleton_iff, hdeg, (mem_gradeBy_iff.1 ha hh : f h = i)]

/-- On nonnegative subrings, a period-rescaling pushforward maps homogeneous series of degree `i`
into homogeneous series of degree `ψ i` whenever `∀ h, f' (φ h) = ψ (f h)`. -/
theorem mapNonnegSubring_mem_nonnegGradeBy [CommRing R] [CommRing S] [AddMonoid H] [AddMonoid H']
    {N : H →+ ℝ} {N' : H' →+ ℝ} (ρ : R →+* S) (φ : H →+ H')
    (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) {f : H → ι} {f' : H' → ι'} {ψ : ι → ι'}
    (hdeg : ∀ h, f' (φ h) = ψ (f h)) {i : ι} {a : nonnegSubring R N}
    (ha : a ∈ nonnegGradeBy R N f i) :
    mapNonnegSubring ρ φ hφ a ∈ nonnegGradeBy S N' f' (ψ i) := by
  rw [mem_nonnegGradeBy_iff, coe_mapNonnegSubring]
  exact map_mem_gradeBy (ρ : R →+ S) φ hφ hdeg (mem_nonnegGradeBy_iff.1 ha)

end GradedPushforward

section Properness

variable {R H ι : Type*}

/-- The Novikov series with coefficient `1` along a sequence of exponents `u : ℕ → H` whose
periods tend to `+∞`, and `0` elsewhere. -/
def seqSeries (R : Type*) [Semiring R] {H : Type*} [AddZeroClass H] {N : H →+ ℝ}
    (u : ℕ → H) (hN : Tendsto (fun n => N (u n)) atTop atTop) : NovikovSeries R H N where
  coeff h := by
    classical
    exact if h ∈ range u then 1 else 0
  finite_lt C := by
    classical
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hN.eventually_ge_atTop C)
    refine ((Finset.range M).image u).finite_toSet.subset ?_
    rintro h ⟨hh, hlt⟩
    have hmem : h ∈ range u := by
      by_contra hnot
      exact hh (by simp [hnot])
    obtain ⟨n, rfl⟩ := hmem
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 ?_, rfl⟩)
    by_contra hge
    exact (hM n (not_lt.1 hge)).not_gt hlt

@[simp]
theorem coeff_seqSeries_apply [Semiring R] [AddZeroClass H] {N : H →+ ℝ}
    (u : ℕ → H) (hN : Tendsto (fun n => N (u n)) atTop atTop) (n : ℕ) :
    (seqSeries R u hN).coeff (u n) = 1 := by
  simp [seqSeries]

theorem coeff_seqSeries_of_notMem_range [Semiring R] [AddZeroClass H] {N : H →+ ℝ}
    (u : ℕ → H) (hN : Tendsto (fun n => N (u n)) atTop atTop) {h : H} (hh : h ∉ range u) :
    (seqSeries R u hN).coeff h = 0 := by
  simp [seqSeries, hh]

/-- If every term `u n` has nonnegative period, then `seqSeries R u hN` lies in
`nonnegSubring R N`. -/
theorem seqSeries_mem_nonnegSubring [Ring R] [AddMonoid H] {N : H →+ ℝ}
    (u : ℕ → H) (hN : Tendsto (fun n => N (u n)) atTop atTop) (hN0 : ∀ n, 0 ≤ N (u n)) :
    seqSeries R u hN ∈ nonnegSubring R N := by
  refine mem_nonnegSubring.2 fun h hh => ?_
  refine coeff_seqSeries_of_notMem_range u hN ?_
  rintro ⟨n, rfl⟩
  exact (hN0 n).not_gt hh

/-- Over a nontrivial coefficient ring, if `f ∘ u : ℕ → ι` is injective and `N (u n) → +∞`, then
`seqSeries R u hN` meets infinitely many degrees and therefore does not lie in the algebraic span
`⨆ i, gradeBy R N f i`. -/
theorem seqSeries_notMem_iSup_gradeBy [Semiring R] [Nontrivial R] [AddZeroClass H] {N : H →+ ℝ}
    {f : H → ι} (u : ℕ → H) (hdeg : Injective (f ∘ u))
    (hN : Tendsto (fun n => N (u n)) atTop atTop) :
    seqSeries R u hN ∉ ⨆ i, gradeBy R N f i := by
  intro hmem
  have hfin : (f '' (seqSeries R u hN).support).Finite :=
    finite_image_support_of_mem_iSup_gradeBy hmem
  have hsub : range (f ∘ u) ⊆ f '' (seqSeries R u hN).support := by
    rintro _ ⟨n, rfl⟩
    refine ⟨u n, mem_support.2 ?_, rfl⟩
    rw [coeff_seqSeries_apply]
    exact one_ne_zero
  exact (infinite_range_of_injective hdeg) (hfin.subset hsub)

/-- Whenever there exists a sequence of nonnegative-period exponents with pairwise distinct degrees
and periods tending to `+∞`, the algebraic graded subalgebra `⨁ i, nonnegGradeBy R N f i` is a
proper dense subalgebra of `nonnegSubring R N`. -/
theorem not_surjective_coeAlgHom_nonnegGradeBy [CommRing R] [Nontrivial R] [AddMonoid H]
    {N : H →+ ℝ} [AddMonoid ι] [DecidableEq ι] {f : H →+ ι} (u : ℕ → H)
    (hdeg : Injective (f ∘ u)) (hN : Tendsto (fun n => N (u n)) atTop atTop)
    (hN0 : ∀ n, 0 ≤ N (u n)) :
    ¬ Surjective (DirectSum.coeAlgHom (S := R) (nonnegGradeBy R N f)) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj ⟨seqSeries R u hN, seqSeries_mem_nonnegSubring u hN hN0⟩
  have hmem : (⟨seqSeries R u hN, seqSeries_mem_nonnegSubring u hN hN0⟩ : nonnegSubring R N) ∈
      ⨆ i, nonnegGradeBy R N f i := by
    rw [Submodule.iSup_eq_toSubmodule_range]
    exact ⟨x, hx⟩
  exact seqSeries_notMem_iSup_gradeBy u hdeg hN
    (coe_mem_iSup_gradeBy_of_mem_iSup_nonnegGradeBy hmem)

end Properness

end NovikovSeries

end TauCeti
