/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.SetTheory.Cardinal.Basic
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Reindex
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Basic
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Hilbert dimension and unitary classification of Hilbert spaces

This file establishes the cardinality invariance of Hilbert bases, defines the Hilbert dimension
of a complete inner-product space over `ℝ` or `ℂ`, and classifies Hilbert spaces up to linear
isometric (and continuous linear) equivalence by their Hilbert dimension.

## Main definitions and results

* `HilbertBasis.prod`: the Hilbert basis of `WithLp 2 (E × F)` formed from Hilbert bases of `E`
  and `F`.
* `HilbertBasis.finite_iff_finiteDimensional`, `HilbertBasis.separableSpace_iff_countable`:
  finiteness and countability of a Hilbert basis index type characterize finite-dimensionality and
  separability of the ambient space.
* `HilbertBasis.lift_mk_le_of_denseRange`: a continuous linear map with dense range cannot
  increase the cardinality of a Hilbert basis; in particular any two Hilbert bases of the same
  space have equipotent index types (`HilbertBasis.lift_mk_eq`, `HilbertBasis.mk_eq`), and
  continuous linear equivalences preserve Hilbert-basis cardinality
  (`ContinuousLinearEquiv.hilbertBasis_lift_mk_eq`).
* `TauCeti.hilbertDim`: the Hilbert dimension of a complete inner-product space, defined as the
  cardinality of a Hilbert basis and shown independent of the choice
  (`HilbertBasis.lift_mk_eq_hilbertDim`, `HilbertBasis.mk_eq_hilbertDim`). Its `Cardinal.toNat`
  always agrees with `Module.finrank` (`TauCeti.toNat_hilbertDim`, `TauCeti.hilbertDim_eq_finrank`),
  it is bounded above by the algebraic Hamel rank (`TauCeti.hilbertDim_le_rank`), equals `#S` on
  `ℓ²(S, 𝕜)` (`TauCeti.hilbertDim_lp`), is additive under `L²` products and orthogonal
  decompositions (`TauCeti.hilbertDim_prodLp`, `Submodule.hilbertDim_add_hilbertDim_orthogonal`),
  and characterizes separability (`TauCeti.separableSpace_iff_hilbertDim_le_aleph0`,
  `TauCeti.hilbertDim_eq_aleph0_iff`).
* `TauCeti.exists_hilbertBasis_nat`, `TauCeti.nonempty_linearIsometryEquiv_lp_nat`: every
  separable infinite-dimensional Hilbert space admits a `ℕ`-indexed Hilbert basis and is linearly
  isometrically equivalent to `ℓ²(ℕ, 𝕜)`.
* `HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`,
  `TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`,
  `TauCeti.nonempty_linearIsometryEquiv_iff_nonempty_continuousLinearEquiv`: two Hilbert spaces
  over the same scalar field are linearly isometrically equivalent if and only if they are
  continuously linearly equivalent, if and only if they have the same Hilbert dimension.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §I.5.
-/

public section

open scoped InnerProductSpace lp

universe u v

section HilbertBasisProd

variable {ι κ 𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace HilbertBasis

/-- The Hilbert basis of the `L²` product `WithLp 2 (E × F)` obtained by combining Hilbert bases of
`E` and `F`. -/
protected noncomputable def prod (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    HilbertBasis (ι ⊕ κ) 𝕜 (WithLp 2 (E × F)) :=
  haveI : CompleteSpace E := b.completeSpace
  haveI : CompleteSpace F := c.completeSpace
  HilbertBasis.mkOfOrthogonalEqBot
    (v := Sum.elim (fun i ↦ WithLp.toLp 2 (b i, (0 : F)))
      (fun j ↦ WithLp.toLp 2 ((0 : E), c j)))
    (by
      refine ⟨?_, ?_⟩
      · rintro (i | j)
        · simp [WithLp.norm_toLp_fst, b.orthonormal.1 i]
        · simp [WithLp.norm_toLp_snd, c.orthonormal.1 j]
      · rintro (i₁ | j₁) (i₂ | j₂) h
        · simp [b.orthonormal.2 (fun heq ↦ h (congrArg Sum.inl heq))]
        · simp
        · simp
        · simp [c.orthonormal.2 (fun heq ↦ h (congrArg Sum.inr heq))])
    (by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_orthogonal] at hx
      have hfst : x.fst = 0 := by
        apply b.repr.injective
        ext i
        rw [map_zero, lp.coeFn_zero, Pi.zero_apply, HilbertBasis.repr_apply_apply]
        have h := hx (WithLp.toLp 2 (b i, (0 : F)))
          (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
        simpa [WithLp.prod_inner_apply] using h
      have hsnd : x.snd = 0 := by
        apply c.repr.injective
        ext j
        rw [map_zero, lp.coeFn_zero, Pi.zero_apply, HilbertBasis.repr_apply_apply]
        have h := hx (WithLp.toLp 2 ((0 : E), c j))
          (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
        simpa [WithLp.prod_inner_apply] using h
      exact WithLp.ofLp_injective 2 (Prod.ext hfst hsnd))

/-- The underlying family of `b.prod c` is the disjoint union of `(b i, 0)` and `(0, c j)`. -/
theorem coe_prod (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    ⇑(b.prod c) = Sum.elim (fun i ↦ WithLp.toLp 2 (b i, (0 : F)))
      (fun j ↦ WithLp.toLp 2 ((0 : E), c j)) := by
  have : CompleteSpace E := b.completeSpace
  have : CompleteSpace F := c.completeSpace
  exact HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The left basis vectors of `b.prod c` are `(b i, 0)`. -/
@[simp]
theorem prod_inl (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (i : ι) :
    b.prod c (.inl i) = WithLp.toLp 2 (b i, (0 : F)) := by
  simp [coe_prod]

/-- The right basis vectors of `b.prod c` are `(0, c j)`. -/
@[simp]
theorem prod_inr (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (j : κ) :
    b.prod c (.inr j) = WithLp.toLp 2 ((0 : E), c j) := by
  simp [coe_prod]

/-- The left coordinates of `x` in `b.prod c` are the coordinates of `x.fst` in `b`. -/
@[simp]
theorem repr_prod_inl (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (x : WithLp 2 (E × F)) (i : ι) :
    (b.prod c).repr x (.inl i) = b.repr x.fst i := by
  simp [HilbertBasis.repr_apply_apply]

/-- The right coordinates of `x` in `b.prod c` are the coordinates of `x.snd` in `c`. -/
@[simp]
theorem repr_prod_inr (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (x : WithLp 2 (E × F)) (j : κ) :
    (b.prod c).repr x (.inr j) = c.repr x.snd j := by
  simp [HilbertBasis.repr_apply_apply]

end HilbertBasis

end HilbertBasisProd

section HilbertBasisProperties

variable {ι κ 𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace HilbertBasis

/-- A Hilbert space is a subsingleton if and only if the index type of a Hilbert basis is empty. -/
theorem isEmpty_iff_subsingleton (b : HilbertBasis ι 𝕜 E) : IsEmpty ι ↔ Subsingleton E := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun i ↦ ?_⟩⟩
  · refine ⟨fun x y ↦ b.repr.injective ?_⟩
    ext i
    exact h.elim i
  · have h0 : b i = 0 := Subsingleton.elim _ _
    have h1 := b.orthonormal.1 i
    simp [h0] at h1

/-- A Hilbert space is nontrivial if and only if the index type of a Hilbert basis is nonempty. -/
theorem nonempty_iff_nontrivial (b : HilbertBasis ι 𝕜 E) : Nonempty ι ↔ Nontrivial E := by
  rw [← not_isEmpty_iff, ← not_subsingleton_iff_nontrivial, b.isEmpty_iff_subsingleton]

/-- A Hilbert space is finite-dimensional if and only if the index type of a Hilbert basis is
finite. -/
theorem finite_iff_finiteDimensional (b : HilbertBasis ι 𝕜 E) :
    Finite ι ↔ FiniteDimensional 𝕜 E := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : Fintype ι := Fintype.ofFinite ι
    exact Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  · exact Cardinal.lt_aleph0_iff_finite.1 <|
      (Cardinal.lift_lt_aleph0.1 <|
        (b.orthonormal.linearIndependent.cardinal_lift_le_rank).trans_lt
          (Cardinal.lift_lt_aleph0.2 (Module.rank_lt_aleph0 𝕜 E)))

/-- A Hilbert space is infinite-dimensional if and only if the index type of a Hilbert basis is
infinite. -/
theorem infinite_iff_not_finiteDimensional (b : HilbertBasis ι 𝕜 E) :
    Infinite ι ↔ ¬ FiniteDimensional 𝕜 E := by
  rw [← not_finite_iff_infinite, b.finite_iff_finiteDimensional]

/-- The cardinality of a finite Hilbert basis equals `Module.finrank 𝕜 E`. -/
theorem card_eq_finrank [Fintype ι] (b : HilbertBasis ι 𝕜 E) :
    Fintype.card ι = Module.finrank 𝕜 E :=
  (Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis).symm

/-- In a finite-dimensional Hilbert space, the cardinal of any Hilbert basis index type equals
`Module.finrank 𝕜 E`. -/
theorem mk_eq_finrank [FiniteDimensional 𝕜 E] (b : HilbertBasis ι 𝕜 E) :
    Cardinal.mk ι = Module.finrank 𝕜 E := by
  have : Finite ι := b.finite_iff_finiteDimensional.2 inferInstance
  have : Fintype ι := Fintype.ofFinite ι
  rw [Cardinal.mk_fintype, b.card_eq_finrank]

/-- A Hilbert space is separable if and only if the index type of a Hilbert basis is countable. -/
theorem separableSpace_iff_countable (b : HilbertBasis ι 𝕜 E) :
    TopologicalSpace.SeparableSpace E ↔ Countable ι := by
  refine ⟨fun _ ↦ b.orthonormal.countable_of_separableSpace, fun _ ↦ ?_⟩
  have : TopologicalSpace.SeparableSpace ℓ²(ι, 𝕜) := lp.separableSpace (by norm_num)
  exact b.repr.symm.surjective.denseRange.separableSpace b.repr.symm.continuous

end HilbertBasis

end HilbertBasisProperties

section CardinalityInvariance

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace HilbertBasis

private theorem eq_zero_of_forall_inner_apply_eq_zero {κ : Type*} (c : HilbertBasis κ 𝕜 F)
    {f : F →L[𝕜] E} (hf : DenseRange f) {x : E} (hx : ∀ j, ⟪x, f (c j)⟫_𝕜 = 0) : x = 0 := by
  have hzero_F (y : F) : ⟪x, f y⟫_𝕜 = 0 := by
    have hsum := ((innerSL 𝕜 x).comp f).hasSum (c.hasSum_repr y)
    have h0 : HasSum (fun _ : κ ↦ (0 : 𝕜)) ⟪x, f y⟫_𝕜 := by
      simpa [ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul, hx] using hsum
    exact h0.unique hasSum_zero
  have heq : (innerSL 𝕜 x : E → 𝕜) = fun _ ↦ (0 : 𝕜) :=
    hf.equalizer (innerSL 𝕜 x).continuous continuous_const (funext hzero_F)
  exact inner_self_eq_zero.1 (congrFun heq x)

/-- **Dense-range monotonicity of Hilbert-basis cardinality.** If `f : F →L[𝕜] E` has dense range,
then the index cardinality of any Hilbert basis of `E` is at most that of any Hilbert basis of `F`.
-/
theorem lift_mk_le_of_denseRange {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) {f : F →L[𝕜] E} (hf : DenseRange f) :
    Cardinal.lift.{v} (Cardinal.mk ι) ≤ Cardinal.lift.{u} (Cardinal.mk κ) := by
  by_cases hκ : Finite κ
  · -- Finite-dimensional case: the range of `f` is finite-dimensional, hence closed, hence all of
    -- `E`.
    have : FiniteDimensional 𝕜 F := c.finite_iff_finiteDimensional.1 hκ
    have hrange_fin : FiniteDimensional 𝕜 (LinearMap.range (f : F →ₗ[𝕜] E)) :=
      Module.Finite.range (f : F →ₗ[𝕜] E)
    have hclosed : IsClosed (Set.range f) := by
      simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
        Submodule.isClosed_of_finiteDimensional (LinearMap.range (f : F →ₗ[𝕜] E))
    have hsurj : Function.Surjective f := by
      rw [← Set.range_eq_univ, ← hclosed.closure_eq]
      exact hf.closure_eq
    have : FiniteDimensional 𝕜 E := Module.Finite.of_surjective (f : F →ₗ[𝕜] E) hsurj
    have hle : Module.finrank 𝕜 E ≤ Module.finrank 𝕜 F := by
      have htop : LinearMap.range (f : F →ₗ[𝕜] E) = ⊤ :=
        LinearMap.range_eq_top.2 hsurj
      rw [← finrank_top 𝕜 E, ← htop]
      exact LinearMap.finrank_range_le (f : F →ₗ[𝕜] E)
    rw [b.mk_eq_finrank, c.mk_eq_finrank, Cardinal.lift_natCast, Cardinal.lift_natCast]
    exact Nat.cast_le.2 hle
  · -- Infinite-dimensional case: the countable supports of `b.repr (f (c j))` cover `ι`.
    have : Infinite κ := not_finite_iff_infinite.1 hκ
    let s : κ → Set ι := fun j ↦ Function.support (b.repr (f (c j)) : ι → 𝕜)
    have hs_count (j : κ) : (s j).Countable :=
      lp.countable_support (b.repr (f (c j))) (by norm_num)
    have hcover : ∀ i : ι, ∃ j : κ, i ∈ s j := by
      intro i
      by_contra h
      push Not at h
      have hbi : b i = 0 := eq_zero_of_forall_inner_apply_eq_zero c hf fun j ↦ by
        simpa [s, Function.mem_support, HilbertBasis.repr_apply_apply] using h j
      have hnorm := b.orthonormal.1 i
      simp [hbi] at hnorm
    -- Map `(j, x)` with `x ∈ s j` surjectively onto `ι` after lifting to `max u v`.
    let g : (j : ULift.{u} κ) × ULift.{v} (s j.down) → ULift.{v} ι :=
      fun p ↦ ULift.up p.2.down.val
    have hg : Function.Surjective g := by
      rintro ⟨i⟩
      obtain ⟨j, hj⟩ := hcover i
      exact ⟨⟨ULift.up j, ULift.up ⟨i, hj⟩⟩, rfl⟩
    have hinf : Cardinal.aleph0.{max u v} ≤ Cardinal.mk (ULift.{u} κ) :=
      Cardinal.aleph0_le_mk_iff.2 inferInstance
    rw [← Cardinal.mk_uLift.{v}, ← Cardinal.mk_uLift.{u}]
    calc Cardinal.mk (ULift.{v} ι)
        ≤ Cardinal.mk ((j : ULift.{u} κ) × ULift.{v} (s j.down)) :=
          Cardinal.mk_le_of_surjective hg
      _ = Cardinal.sum (fun j : ULift.{u} κ ↦ Cardinal.mk (ULift.{v} (s j.down))) :=
          Cardinal.mk_sigma _
      _ ≤ Cardinal.sum (fun _ : ULift.{u} κ ↦ Cardinal.aleph0.{max u v}) := by
          refine Cardinal.sum_le_sum _ _ fun j ↦ ?_
          have : Countable (s j.down) := (hs_count j.down).to_subtype
          exact Cardinal.mk_le_aleph0
      _ = Cardinal.mk (ULift.{u} κ) * Cardinal.aleph0.{max u v} := by
          rw [Cardinal.sum_const, Cardinal.lift_id, Cardinal.lift_id, mul_comm]
      _ = Cardinal.mk (ULift.{u} κ) :=
          Cardinal.mul_eq_left hinf hinf Cardinal.aleph0_ne_zero

/-- **Basis-cardinality invariance.** Any two Hilbert bases of the same inner-product space have
index types of the same cardinality. -/
theorem lift_mk_eq {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    Cardinal.lift.{v} (Cardinal.mk ι) = Cardinal.lift.{u} (Cardinal.mk κ) :=
  le_antisymm
    (b.lift_mk_le_of_denseRange c (f := ContinuousLinearMap.id 𝕜 E) denseRange_id)
    (c.lift_mk_le_of_denseRange b (f := ContinuousLinearMap.id 𝕜 E) denseRange_id)

/-- Same-universe form of `HilbertBasis.lift_mk_eq`. -/
theorem mk_eq {ι κ : Type u} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 E) :
    Cardinal.mk ι = Cardinal.mk κ := by
  simpa using b.lift_mk_eq c

end HilbertBasis

/-- A continuous linear equivalence preserves the index cardinality of Hilbert bases. -/
theorem ContinuousLinearEquiv.hilbertBasis_lift_mk_eq {ι : Type u} {κ : Type v}
    (e : E ≃L[𝕜] F) (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    Cardinal.lift.{v} (Cardinal.mk ι) = Cardinal.lift.{u} (Cardinal.mk κ) :=
  le_antisymm
    (b.lift_mk_le_of_denseRange c (f := e.symm.toContinuousLinearMap) e.symm.surjective.denseRange)
    (c.lift_mk_le_of_denseRange b (f := e.toContinuousLinearMap) e.surjective.denseRange)

namespace HilbertBasis

/-- **Unitary classification via Hilbert bases.** Two Hilbert spaces equipped with Hilbert bases
are linearly isometrically equivalent if and only if their basis index types have the same
cardinality. -/
theorem nonempty_linearIsometryEquiv_iff_lift_mk_eq {ι : Type u} {κ : Type v}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔
      Cardinal.lift.{v} (Cardinal.mk ι) = Cardinal.lift.{u} (Cardinal.mk κ) := by
  refine ⟨fun ⟨U⟩ ↦ (b.mapₗᵢ U).lift_mk_eq c, fun h ↦ ?_⟩
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 h
  exact ⟨b.equivₗᵢ c e⟩

/-- Same-universe form of `HilbertBasis.nonempty_linearIsometryEquiv_iff_lift_mk_eq`. -/
theorem nonempty_linearIsometryEquiv_iff_mk_eq {ι κ : Type u}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    Nonempty (E ≃ₗᵢ[𝕜] F) ↔ Cardinal.mk ι = Cardinal.mk κ := by
  simpa using b.nonempty_linearIsometryEquiv_iff_lift_mk_eq c

end HilbertBasis

end CardinalityInvariance

section HilbertDim

namespace TauCeti

/-- **Hilbert dimension** of a complete inner-product space over `ℝ` or `ℂ`: the cardinality of
any Hilbert basis of `H`. -/
noncomputable def hilbertDim (𝕜 : Type*) (H : Type u) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] : Cardinal.{u} :=
  Cardinal.mk (exists_hilbertBasis 𝕜 H).choose

end TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The lifted index cardinality of any Hilbert basis of `H` equals the lifted Hilbert dimension of
`H`. -/
theorem HilbertBasis.lift_mk_eq_hilbertDim {ι : Type v} {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (b : HilbertBasis ι 𝕜 H) :
    Cardinal.lift.{u} (Cardinal.mk ι) = Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 H) := by
  obtain ⟨c, -⟩ := (exists_hilbertBasis 𝕜 H).choose_spec
  exact b.lift_mk_eq c

/-- Same-universe form of `HilbertBasis.lift_mk_eq_hilbertDim`. -/
theorem HilbertBasis.mk_eq_hilbertDim {ι H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (b : HilbertBasis ι 𝕜 H) :
    Cardinal.mk ι = TauCeti.hilbertDim 𝕜 H := by
  simpa using b.lift_mk_eq_hilbertDim

namespace TauCeti

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- In finite dimension, the Hilbert dimension agrees with `Module.finrank`. -/
theorem hilbertDim_eq_finrank [FiniteDimensional 𝕜 H] :
    hilbertDim 𝕜 H = Module.finrank 𝕜 H := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 H
  rw [← b.mk_eq_hilbertDim, b.mk_eq_finrank]

/-- The Hilbert dimension is at most the algebraic Hamel dimension `Module.rank`. -/
theorem hilbertDim_le_rank : hilbertDim 𝕜 H ≤ Module.rank 𝕜 H := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 H
  rw [← b.mk_eq_hilbertDim]
  simpa using b.orthonormal.linearIndependent.cardinal_lift_le_rank

/-- A Hilbert space is finite-dimensional if and only if its Hilbert dimension is strictly less
than `ℵ₀`. -/
theorem finiteDimensional_iff_hilbertDim_lt_aleph0 :
    FiniteDimensional 𝕜 H ↔ hilbertDim 𝕜 H < Cardinal.aleph0 := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 H
  rw [← b.mk_eq_hilbertDim, Cardinal.lt_aleph0_iff_finite, b.finite_iff_finiteDimensional]

/-- The `Cardinal.toNat` of the Hilbert dimension always equals `Module.finrank` (both being `0` in
infinite dimension). -/
theorem toNat_hilbertDim : (hilbertDim 𝕜 H).toNat = Module.finrank 𝕜 H := by
  by_cases h : FiniteDimensional 𝕜 H
  · rw [hilbertDim_eq_finrank, Cardinal.toNat_natCast]
  · have hle : Cardinal.aleph0 ≤ hilbertDim 𝕜 H :=
      not_lt.1 ((finiteDimensional_iff_hilbertDim_lt_aleph0 (𝕜 := 𝕜)).not.1 h)
    rw [Cardinal.toNat_apply_of_aleph0_le hle,
      Module.finrank, Cardinal.toNat_apply_of_aleph0_le (hle.trans hilbertDim_le_rank)]

/-- A Hilbert space has Hilbert dimension `0` if and only if it is a subsingleton. -/
theorem hilbertDim_eq_zero_iff : hilbertDim 𝕜 H = 0 ↔ Subsingleton H := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 H
  rw [← b.mk_eq_hilbertDim, Cardinal.mk_eq_zero_iff, b.isEmpty_iff_subsingleton]

/-- A subsingleton Hilbert space has Hilbert dimension `0`. -/
@[simp]
theorem hilbertDim_subsingleton [Subsingleton H] : hilbertDim 𝕜 H = 0 :=
  hilbertDim_eq_zero_iff.2 ‹_›

/-- A Hilbert space has positive Hilbert dimension if and only if it is nontrivial. -/
theorem hilbertDim_pos_iff : 0 < hilbertDim 𝕜 H ↔ Nontrivial H := by
  rw [pos_iff_ne_zero, ne_eq, hilbertDim_eq_zero_iff, not_subsingleton_iff_nontrivial]

/-- The Hilbert dimension of `ℓ²(S, 𝕜)` is the cardinality of `S`. -/
@[simp]
theorem hilbertDim_lp (𝕜 : Type v) (S : Type u) [RCLike 𝕜] :
    hilbertDim 𝕜 ℓ²(S, 𝕜) = Cardinal.lift.{v} (Cardinal.mk S) := by
  have h := (default : HilbertBasis S 𝕜 ℓ²(S, 𝕜)).lift_mk_eq_hilbertDim
  rw [Cardinal.lift_id'.{u, max u v}, Cardinal.lift_umax.{u, v}] at h
  exact h.symm

/-- The scalar field has Hilbert dimension `1` over itself. -/
@[simp]
theorem hilbertDim_self (𝕜 : Type u) [RCLike 𝕜] : hilbertDim 𝕜 𝕜 = 1 := by
  rw [hilbertDim_eq_finrank, Module.finrank_self, Nat.cast_one]

/-- Finite-dimensional `EuclideanSpace 𝕜 ι` has Hilbert dimension `Fintype.card ι`. -/
@[simp]
theorem hilbertDim_euclideanSpace (𝕜 : Type u) (ι : Type v) [RCLike 𝕜] [Fintype ι] :
    hilbertDim 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
  rw [hilbertDim_eq_finrank, finrank_euclideanSpace]

/-- A Hilbert space is separable if and only if its Hilbert dimension is at most `ℵ₀`. -/
theorem separableSpace_iff_hilbertDim_le_aleph0 :
    TopologicalSpace.SeparableSpace H ↔ hilbertDim 𝕜 H ≤ Cardinal.aleph0 := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 H
  rw [← b.mk_eq_hilbertDim, Cardinal.le_aleph0_iff_set_countable,
    b.separableSpace_iff_countable, Set.countable_coe_iff]

/-- A Hilbert space has Hilbert dimension `ℵ₀` if and only if it is separable and
infinite-dimensional. -/
theorem hilbertDim_eq_aleph0_iff :
    hilbertDim 𝕜 H = Cardinal.aleph0 ↔
      TopologicalSpace.SeparableSpace H ∧ ¬ FiniteDimensional 𝕜 H := by
  rw [separableSpace_iff_hilbertDim_le_aleph0 (𝕜 := 𝕜),
    finiteDimensional_iff_hilbertDim_lt_aleph0 (𝕜 := 𝕜), not_lt, le_antisymm_iff]

/-- Every separable infinite-dimensional Hilbert space admits a Hilbert basis indexed by `ℕ`. -/
theorem exists_hilbertBasis_nat [TopologicalSpace.SeparableSpace H]
    (hinf : ¬ FiniteDimensional 𝕜 H) : Nonempty (HilbertBasis ℕ 𝕜 H) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 H
  have : Countable w := b.separableSpace_iff_countable.1 inferInstance
  have : Infinite w := b.infinite_iff_not_finiteDimensional.2 hinf
  have heq : Cardinal.lift.{0} (Cardinal.mk w) = Cardinal.lift.{u} (Cardinal.mk ℕ) := by simp
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 heq
  exact ⟨b.reindex e⟩

/-- Every separable infinite-dimensional Hilbert space is linearly isometrically equivalent to
`ℓ²(ℕ, 𝕜)`. -/
theorem nonempty_linearIsometryEquiv_lp_nat [TopologicalSpace.SeparableSpace H]
    (hinf : ¬ FiniteDimensional 𝕜 H) : Nonempty (H ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜)) := by
  obtain ⟨b⟩ := exists_hilbertBasis_nat (𝕜 := 𝕜) (H := H) hinf
  exact ⟨b.repr⟩

/-- **Additivity of Hilbert dimension under `L²` products.** -/
theorem hilbertDim_prodLp :
    hilbertDim 𝕜 (WithLp 2 (H × K)) =
      Cardinal.lift.{v} (hilbertDim 𝕜 H) + Cardinal.lift.{u} (hilbertDim 𝕜 K) := by
  obtain ⟨wH, bH, -⟩ := exists_hilbertBasis 𝕜 H
  obtain ⟨wK, bK, -⟩ := exists_hilbertBasis 𝕜 K
  rw [← (bH.prod bK).mk_eq_hilbertDim, ← bH.mk_eq_hilbertDim, ← bK.mk_eq_hilbertDim,
    Cardinal.mk_sum]

end TauCeti

/-- A continuous linear map with dense range cannot increase the Hilbert dimension. -/
theorem ContinuousLinearMap.lift_hilbertDim_le_of_denseRange {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (f : K →L[𝕜] H) (hf : DenseRange f) :
    Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 H) ≤ Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 K) := by
  obtain ⟨_, bH, -⟩ := exists_hilbertBasis 𝕜 H
  obtain ⟨_, bK, -⟩ := exists_hilbertBasis 𝕜 K
  rw [← bH.mk_eq_hilbertDim, ← bK.mk_eq_hilbertDim]
  exact bH.lift_mk_le_of_denseRange bK hf

/-- Same-universe form of `ContinuousLinearMap.lift_hilbertDim_le_of_denseRange`. -/
theorem ContinuousLinearMap.hilbertDim_le_of_denseRange {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (f : K →L[𝕜] H) (hf : DenseRange f) :
    TauCeti.hilbertDim 𝕜 H ≤ TauCeti.hilbertDim 𝕜 K := by
  simpa using f.lift_hilbertDim_le_of_denseRange hf

/-- A continuous linear equivalence preserves Hilbert dimension. -/
theorem ContinuousLinearEquiv.lift_hilbertDim_eq {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (e : H ≃L[𝕜] K) :
    Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 H) = Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 K) :=
  le_antisymm
    (e.symm.toContinuousLinearMap.lift_hilbertDim_le_of_denseRange e.symm.surjective.denseRange)
    (e.toContinuousLinearMap.lift_hilbertDim_le_of_denseRange e.surjective.denseRange)

/-- Same-universe form of `ContinuousLinearEquiv.lift_hilbertDim_eq`. -/
theorem ContinuousLinearEquiv.hilbertDim_eq {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (e : H ≃L[𝕜] K) :
    TauCeti.hilbertDim 𝕜 H = TauCeti.hilbertDim 𝕜 K := by
  simpa using e.lift_hilbertDim_eq

/-- A linear isometric equivalence preserves Hilbert dimension. -/
theorem LinearIsometryEquiv.lift_hilbertDim_eq {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (e : H ≃ₗᵢ[𝕜] K) :
    Cardinal.lift.{v} (TauCeti.hilbertDim 𝕜 H) = Cardinal.lift.{u} (TauCeti.hilbertDim 𝕜 K) :=
  e.toContinuousLinearEquiv.lift_hilbertDim_eq

/-- Same-universe form of `LinearIsometryEquiv.lift_hilbertDim_eq`. -/
theorem LinearIsometryEquiv.hilbertDim_eq {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (e : H ≃ₗᵢ[𝕜] K) :
    TauCeti.hilbertDim 𝕜 H = TauCeti.hilbertDim 𝕜 K := by
  simpa using e.lift_hilbertDim_eq

/-- **Orthogonal additivity of Hilbert dimension.** For every complete subspace `U` of a Hilbert
space `H`, `hilbertDim 𝕜 U + hilbertDim 𝕜 Uᗮ = hilbertDim 𝕜 H`. -/
theorem Submodule.hilbertDim_add_hilbertDim_orthogonal {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (U : Submodule 𝕜 H) [CompleteSpace U] :
    TauCeti.hilbertDim 𝕜 U + TauCeti.hilbertDim 𝕜 Uᗮ = TauCeti.hilbertDim 𝕜 H := by
  have h := U.orthogonalDecomposition.hilbertDim_eq
  simpa [TauCeti.hilbertDim_prodLp] using h.symm

/-- A complete subspace of a Hilbert space has Hilbert dimension at most that of the ambient space.
-/
theorem Submodule.hilbertDim_le {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (U : Submodule 𝕜 H) [CompleteSpace U] :
    TauCeti.hilbertDim 𝕜 U ≤ TauCeti.hilbertDim 𝕜 H := by
  rw [← U.hilbertDim_add_hilbertDim_orthogonal]
  exact le_self_add

namespace TauCeti

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- **Unitary classification of Hilbert spaces.** Two complete inner-product spaces over the same
scalar field are linearly isometrically equivalent if and only if their Hilbert dimensions agree. -/
theorem nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq :
    Nonempty (H ≃ₗᵢ[𝕜] K) ↔
      Cardinal.lift.{v} (hilbertDim 𝕜 H) = Cardinal.lift.{u} (hilbertDim 𝕜 K) := by
  obtain ⟨_, bH, -⟩ := exists_hilbertBasis 𝕜 H
  obtain ⟨_, bK, -⟩ := exists_hilbertBasis 𝕜 K
  rw [← bH.mk_eq_hilbertDim, ← bK.mk_eq_hilbertDim]
  exact bH.nonempty_linearIsometryEquiv_iff_lift_mk_eq bK

/-- Same-universe form of `TauCeti.nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq`. -/
theorem nonempty_linearIsometryEquiv_iff_hilbertDim_eq {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K] :
    Nonempty (H ≃ₗᵢ[𝕜] K) ↔ hilbertDim 𝕜 H = hilbertDim 𝕜 K := by
  simpa using nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq (𝕜 := 𝕜) (H := H) (K := K)

/-- Two complete inner-product spaces over the same scalar field are continuously linearly
equivalent if and only if their Hilbert dimensions agree. -/
theorem nonempty_continuousLinearEquiv_iff_lift_hilbertDim_eq :
    Nonempty (H ≃L[𝕜] K) ↔
      Cardinal.lift.{v} (hilbertDim 𝕜 H) = Cardinal.lift.{u} (hilbertDim 𝕜 K) := by
  refine ⟨fun ⟨e⟩ ↦ e.lift_hilbertDim_eq, fun h ↦ ?_⟩
  obtain ⟨U⟩ := (nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq (𝕜 := 𝕜)).2 h
  exact ⟨U.toContinuousLinearEquiv⟩

/-- Same-universe form of `TauCeti.nonempty_continuousLinearEquiv_iff_lift_hilbertDim_eq`. -/
theorem nonempty_continuousLinearEquiv_iff_hilbertDim_eq {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K] :
    Nonempty (H ≃L[𝕜] K) ↔ hilbertDim 𝕜 H = hilbertDim 𝕜 K := by
  simpa using nonempty_continuousLinearEquiv_iff_lift_hilbertDim_eq (𝕜 := 𝕜) (H := H) (K := K)

/-- Two complete inner-product spaces over the same scalar field are linearly isometrically
equivalent if and only if they are continuously linearly equivalent. -/
theorem nonempty_linearIsometryEquiv_iff_nonempty_continuousLinearEquiv :
    Nonempty (H ≃ₗᵢ[𝕜] K) ↔ Nonempty (H ≃L[𝕜] K) := by
  rw [nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq (𝕜 := 𝕜),
    nonempty_continuousLinearEquiv_iff_lift_hilbertDim_eq (𝕜 := 𝕜)]

end TauCeti

end HilbertDim
