/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Hom
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical

/-!
# The Jones quotient at `δ = √3` as the inversion-fixed cubic quantum torus

Building on the surjective star-compatible comparison homomorphism
`F_m = cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` from
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Hom`, this file equips the cubic quantum torus tower
`CubicTorus N` and its inversion-fixed subalgebra tower `cubicFixed N` with coordinate inclusions
and trace-preserving conditional expectations, identifies the Markov trace at `δ = √3` with
`(√3) ^ m` times `TwistedMonoidAlgebra.scalarTrace`, establishes positivity of the Markov Hermitian
form at `δ = √3`, and identifies the `m`-strand Temperley–Lieb trace-radical quotient (the Jones
quotient at index `δ² = 3`) with `cubicFixed (m - 1)`.

* **Coordinate inclusions and conditional expectation**: extending `Fin N → ZMod 3` by `0` in the
  last coordinate preserves `chainForm` and `cubicFactor`, inducing injective algebra maps
  `cubicIncl N` and `cubicFixedIncl N` that intertwine `strandIncl`, `cubicInversion`, and
  `TwistedMonoidAlgebra.adjoint`, and preserve `TwistedMonoidAlgebra.scalarTrace`. The linear map
  `cubicCondExp N : CubicTorus (N + 1) →ₗ[ℂ] CubicTorus N` deleting Weyl basis elements with
  nonzero last coordinate is a trace-preserving `cubicIncl N`-bimodule retraction commuting with
  inversion and adjoint, restricting to
  `cubicFixedCondExp N : cubicFixed (N + 1) →ₗ[ℂ] cubicFixed N`.
* **Markov trace identity**: multiplying `cubicIncl N a` on the right by the last projection
  `cubicProjection (N + 1) (Fin.last N)` scales the scalar trace by `3⁻¹`, because the two
  off-identity terms `U_N` and `U_N ^ 2` lie outside the range of `cubicExtendHom N` and vanish
  under `TwistedMonoidAlgebra.scalarTrace_map_mul_of_eq_zero`. Hence
  `cubicFixedTrace m x = (√3) ^ m * scalarTrace (F_m x)` satisfies `IsMarkovTrace`, and Markov
  uniqueness identifies every Markov trace at `√3` with it.
* **Positivity and the trace radical**: Parseval positivity and faithfulness of
  `scalarTrace (adjoint a * a)` show that at `δ = √3` the Markov Hermitian form
  `tr m (star x * x)` is positive semidefinite (the `m = 6` discrete-series point `2 cos (π / 6)`
  of Jones's positivity theorem), and identify both its null space and `(tr m).traceRadical` with
  `RingHom.ker (cubicFixedHom m)`.
* **Jones quotient equivalence and five-strand Jones–Wenzl vanishing**: passing to the quotient
  yields `IsMarkovTrace.quotientCubicFixedEquiv` of complex dimension `(3 ^ (m - 1) + 1) / 2`
  intertwining `quotientStrandIncl` and `quotientTrace`. In particular, at five strands
  (`dim TL_5 = 42`, `dim cubicFixed 4 = 41`), `cubicFixedHom 5` annihilates the negligible
  Jones–Wenzl projection `jonesWenzl (√3 : ℂ) 5`.

## Main definitions

* `TauCeti.TemperleyLieb.cubicExtendHom`, `TauCeti.TemperleyLieb.cubicIncl`, and
  `TauCeti.TemperleyLieb.cubicFixedIncl`: the coordinate inclusions extending `Fin N → ZMod 3` by
  zero.
* `TauCeti.TemperleyLieb.cubicCondExp` and `TauCeti.TemperleyLieb.cubicFixedCondExp`: the
  trace-preserving conditional expectations deleting Weyl basis vectors with nonzero last
  coordinate.
* `TauCeti.TemperleyLieb.cubicFixedTrace`: the unnormalized Markov trace at `√3` induced by
  `TwistedMonoidAlgebra.scalarTrace`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv`: the algebra isomorphism between
  the `m`-strand Temperley–Lieb trace quotient at `√3` and `cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.cubicIncl_injective`, `TauCeti.TemperleyLieb.cubicFixedIncl_injective`,
  and `TauCeti.TemperleyLieb.cubicFixedHom_strandIncl`: injectivity and tower compatibility of the
  coordinate inclusions.
* `TauCeti.TemperleyLieb.isMarkovTrace_cubicFixedTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.apply_eq_mul_scalarTrace_cubicFixedHom`, and
  `TauCeti.TemperleyLieb.markovTrace_eq_mul_scalarTrace_cubicFixedHom`: the Markov-trace formula
  `tr m x = (√3) ^ m * scalarTrace (cubicFixedHom m x)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_sqrt_three` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicFixedHom`: positivity of the
  Markov Hermitian form at `δ = √3` and identification of the trace radical with
  `RingHom.ker (cubicFixedHom m)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_eq_mul_scalarTrace_quotientCubicFixedEquiv`,
  and `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_three`: tower, trace,
  and dimension (`(3 ^ (m - 1) + 1) / 2`) properties of the Jones quotient equivalence.
* `TauCeti.TemperleyLieb.exists_cubicFixedModel` and
  `TauCeti.TemperleyLieb.cubicFixedHom_jonesWenzl_five`: packaged existence theorem for the
  inversion-fixed cubic quantum torus model at `δ = √3` and vanishing of the five-strand
  Jones–Wenzl projection.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*, J. Math.
  Phys. 55 (2014), 061702.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topol. 8
  (2017), 433–458.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Coordinate inclusions on `CubicTorus` and `cubicFixed` -/

/-- Extending a coordinate vector `a : Fin N → ZMod 3` by `0` in the last coordinate gives a group
homomorphism `Multiplicative (Fin N → ZMod 3) →* Multiplicative (Fin (N + 1) → ZMod 3)`. -/
def cubicExtendHom (N : ℕ) :
    Multiplicative (Fin N → ZMod 3) →* Multiplicative (Fin (N + 1) → ZMod 3) where
  toFun a := Multiplicative.ofAdd (Fin.snoc a.toAdd 0)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k <;> simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k <;> simp

/-- Evaluation of `cubicExtendHom` via `Fin.snoc · 0`. -/
@[simp]
theorem cubicExtendHom_apply (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicExtendHom N a = Multiplicative.ofAdd (Fin.snoc a.toAdd 0) :=
  (rfl)

/-- `cubicExtendHom N` is injective. -/
theorem cubicExtendHom_injective (N : ℕ) : Function.Injective (cubicExtendHom N) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  ext k
  have hk := congrFun (congrArg Multiplicative.toAdd hab) k.castSucc
  simpa using hk

/-- Extending by `0` in the last coordinate preserves `chainForm`. -/
theorem chainForm_snoc_zero (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm (N + 1) (Fin.snoc a 0) (Fin.snoc b 0) = chainForm N a b := by
  cases N with
  | zero =>
    simp [chainForm_apply]
  | succ M =>
    rw [chainForm_apply, chainForm_apply]
    have hsplit := Fin.sum_univ_castSucc (n := M) fun j : Fin (M + 1) ↦
      Fin.snoc (α := fun _ ↦ ZMod 3) a 0 ⟨j.1, by omega⟩ *
          Fin.snoc (α := fun _ ↦ ZMod 3) b 0 ⟨j.1 + 1, by omega⟩ -
        Fin.snoc (α := fun _ ↦ ZMod 3) b 0 ⟨j.1, by omega⟩ *
          Fin.snoc (α := fun _ ↦ ZMod 3) a 0 ⟨j.1 + 1, by omega⟩
    refine hsplit.trans ?_
    have hlast : (⟨(Fin.last M).1 + 1, by omega⟩ : Fin (M + 2)) = Fin.last (M + 1) :=
      Fin.ext (by simp)
    rw [hlast, Fin.snoc_last, Fin.snoc_last, mul_zero, mul_zero, sub_self, add_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h0 : (⟨j.castSucc.1, by omega⟩ : Fin (M + 2)) =
        (⟨j.1, by omega⟩ : Fin (M + 1)).castSucc := Fin.ext rfl
    have h1 : (⟨j.castSucc.1 + 1, by omega⟩ : Fin (M + 2)) =
        (⟨j.1 + 1, by omega⟩ : Fin (M + 1)).castSucc := Fin.ext rfl
    rw [h0, h1, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- `cubicExtendHom N` pulls `cubicFactor (N + 1)` back to `cubicFactor N`. -/
theorem cubicFactor_cubicExtendHom (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b = cubicFactor (N + 1) (cubicExtendHom N a) (cubicExtendHom N b) := by
  rw [cubicFactor_apply, cubicFactor_apply, cubicExtendHom_apply, cubicExtendHom_apply,
    toAdd_ofAdd, toAdd_ofAdd, chainForm_snoc_zero]

/-- The coordinate inclusion `CubicTorus N →ₐ[ℂ] CubicTorus (N + 1)` induced by extending
`Fin N → ZMod 3` by zero. -/
noncomputable def cubicIncl (N : ℕ) : CubicTorus N →ₐ[ℂ] CubicTorus (N + 1) :=
  TwistedMonoidAlgebra.map (cubicExtendHom N) (cubicFactor_cubicExtendHom N)

/-- Unfolding `cubicIncl` as `TwistedMonoidAlgebra.map`. -/
theorem cubicIncl_def (N : ℕ) :
    cubicIncl N = TwistedMonoidAlgebra.map (cubicExtendHom N) (cubicFactor_cubicExtendHom N) :=
  (rfl)

/-- Action of `cubicIncl N` on Weyl basis elements. -/
@[simp]
theorem cubicIncl_of (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicIncl N (TwistedMonoidAlgebra.of a) = TwistedMonoidAlgebra.of (cubicExtendHom N a) :=
  TwistedMonoidAlgebra.map_of ..

/-- `cubicIncl N` is injective. -/
theorem cubicIncl_injective (N : ℕ) : Function.Injective (cubicIncl N) :=
  TwistedMonoidAlgebra.map_injective (cubicExtendHom N) (cubicFactor_cubicExtendHom N)
    (cubicExtendHom_injective N)

/-- `cubicIncl N` sends the `j`-th site unitary to the `j.castSucc`-th site unitary. -/
@[simp]
theorem cubicIncl_cubicSite (N : ℕ) (j : Fin N) :
    cubicIncl N (cubicSite N j) = cubicSite (N + 1) j.castSucc := by
  have hsnoc : Fin.snoc (α := fun _ ↦ ZMod 3) (Pi.single j 1) 0 =
      Pi.single j.castSucc 1 := by
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp [(Fin.castSucc_lt_last j).ne']
    · simp [Pi.single_apply]
  rw [cubicSite_def, cubicSite_def, cubicIncl_of, cubicExtendHom_apply, toAdd_ofAdd, hsnoc]

/-- `cubicIncl N` sends the `j`-th cubic projection to the `j.castSucc`-th cubic projection. -/
@[simp]
theorem cubicIncl_cubicProjection (N : ℕ) (j : Fin N) :
    cubicIncl N (cubicProjection N j) = cubicProjection (N + 1) j.castSucc := by
  simp [cubicProjection_def]

/-- `cubicIncl N` commutes with `cubicInversion`. -/
@[simp]
theorem cubicIncl_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicIncl N (cubicInversion N x) = cubicInversion (N + 1) (cubicIncl N x) := by
  have hhom : (cubicIncl N).comp (cubicInversion N) =
      (cubicInversion (N + 1)).comp (cubicIncl N) := by
    ext a
    simp only [AlgHom.comp_apply, cubicInversion_of, cubicIncl_of, map_inv]
  exact AlgHom.congr_fun hhom x

/-- `cubicIncl N` intertwines `TwistedMonoidAlgebra.adjoint`. -/
@[simp]
theorem cubicIncl_adjoint (N : ℕ) (x : CubicTorus N) :
    cubicIncl N (TwistedMonoidAlgebra.adjoint x) =
      TwistedMonoidAlgebra.adjoint (cubicIncl N x) := by
  rw [cubicIncl_def]
  exact (TwistedMonoidAlgebra.adjoint_map (α := cubicFactor N) (β := cubicFactor (N + 1))
    (cubicExtendHom N) (cubicFactor_cubicExtendHom N) x).symm

/-- `cubicIncl N` preserves `TwistedMonoidAlgebra.scalarTrace`. -/
@[simp]
theorem scalarTrace_cubicIncl (N : ℕ) (x : CubicTorus N) :
    TwistedMonoidAlgebra.scalarTrace (cubicIncl N x) = TwistedMonoidAlgebra.scalarTrace x := by
  rw [cubicIncl_def]
  exact TwistedMonoidAlgebra.scalarTrace_map (cubicExtendHom N) (cubicFactor_cubicExtendHom N)
    (fun g hg ↦ cubicExtendHom_injective N (by rw [hg, map_one])) x

/-- `cubicIncl N` maps `cubicFixed N` into `cubicFixed (N + 1)`. -/
theorem cubicIncl_mem_cubicFixed (N : ℕ) {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicIncl N x ∈ cubicFixed (N + 1) := by
  rw [mem_cubicFixed_iff] at hx ⊢
  rw [← cubicIncl_cubicInversion, hx]

/-- `cubicIncl N x` lies in `cubicFixed (N + 1)` if and only if `x` lies in `cubicFixed N`. -/
@[simp]
theorem cubicIncl_mem_cubicFixed_iff (N : ℕ) {x : CubicTorus N} :
    cubicIncl N x ∈ cubicFixed (N + 1) ↔ x ∈ cubicFixed N := by
  refine ⟨fun h ↦ ?_, cubicIncl_mem_cubicFixed N⟩
  rw [mem_cubicFixed_iff] at h ⊢
  rw [← cubicIncl_cubicInversion] at h
  exact cubicIncl_injective N h

/-- The restricted coordinate inclusion `cubicFixed N →ₐ[ℂ] cubicFixed (N + 1)`. -/
noncomputable def cubicFixedIncl (N : ℕ) : cubicFixed N →ₐ[ℂ] cubicFixed (N + 1) :=
  ((cubicIncl N).comp (cubicFixed N).val).codRestrict (cubicFixed (N + 1)) fun x ↦
    cubicIncl_mem_cubicFixed N x.2

/-- Coercing `cubicFixedIncl` to the ambient cubic torus recovers `cubicIncl`. -/
@[simp]
theorem coe_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    (cubicFixedIncl N x : CubicTorus (N + 1)) = cubicIncl N x :=
  (rfl)

/-- `cubicFixedIncl N` is injective. -/
theorem cubicFixedIncl_injective (N : ℕ) : Function.Injective (cubicFixedIncl N) := by
  intro x y hxy
  exact Subtype.ext (cubicIncl_injective N (congrArg Subtype.val hxy))

/-- `cubicFixedIncl N` intertwines `cubicFixedAdjoint`. -/
@[simp]
theorem cubicFixedIncl_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    cubicFixedIncl N (cubicFixedAdjoint N x) =
      cubicFixedAdjoint (N + 1) (cubicFixedIncl N x) := by
  apply Subtype.ext
  simp [cubicIncl_adjoint]

/-! ### Trace-preserving conditional expectations on `CubicTorus` and `cubicFixed` -/

/-- The trace-preserving conditional expectation `CubicTorus (N + 1) →ₗ[ℂ] CubicTorus N`, deleting
Weyl basis elements with nonzero last coordinate and dropping the trailing zero otherwise. -/
noncomputable def cubicCondExp (N : ℕ) : CubicTorus (N + 1) →ₗ[ℂ] CubicTorus N :=
  (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin (N + 1) → ZMod 3))
      (cubicFactor (N + 1))).constr ℂ
    fun a ↦
      if a.toAdd (Fin.last N) = 0 then
        TwistedMonoidAlgebra.of (Multiplicative.ofAdd (Fin.init a.toAdd))
      else 0

/-- Action of `cubicCondExp N` on Weyl basis elements. -/
@[simp]
theorem cubicCondExp_of (N : ℕ) (a : Multiplicative (Fin (N + 1) → ZMod 3)) :
    cubicCondExp N (TwistedMonoidAlgebra.of a) =
      if a.toAdd (Fin.last N) = 0 then
        TwistedMonoidAlgebra.of (Multiplicative.ofAdd (Fin.init a.toAdd))
      else 0 :=
  TwistedMonoidAlgebra.constr_of ..

/-- `cubicCondExp N` is a left inverse to `cubicIncl N`. -/
@[simp]
theorem cubicCondExp_cubicIncl (N : ℕ) (x : CubicTorus N) :
    cubicCondExp N (cubicIncl N x) = x := by
  have hlin : (cubicCondExp N).comp (cubicIncl N).toLinearMap = LinearMap.id := by
    refine (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
      (cubicFactor N)).ext fun a ↦ ?_
    simp [Fin.init_snoc]
  exact LinearMap.congr_fun hlin x

/-- `cubicCondExp N` preserves `TwistedMonoidAlgebra.scalarTrace`. -/
@[simp]
theorem scalarTrace_cubicCondExp (N : ℕ) (x : CubicTorus (N + 1)) :
    TwistedMonoidAlgebra.scalarTrace (cubicCondExp N x) = TwistedMonoidAlgebra.scalarTrace x := by
  have hlin : TwistedMonoidAlgebra.scalarTrace.comp (cubicCondExp N) =
      TwistedMonoidAlgebra.scalarTrace := by
    refine (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin (N + 1) → ZMod 3))
      (cubicFactor (N + 1))).ext fun a ↦ ?_
    simp only [LinearMap.comp_apply, TwistedMonoidAlgebra.basis_apply, cubicCondExp_of]
    by_cases hlast : a.toAdd (Fin.last N) = 0
    · rw [ite_eq_left_iff.mpr fun h ↦ absurd hlast h]
      by_cases ha : a = 1
      · subst ha
        have hinit : Fin.init (0 : Fin (N + 1) → ZMod 3) = 0 := rfl
        simp [hinit]
      · have hinit : Multiplicative.ofAdd (Fin.init a.toAdd) ≠ 1 := by
          intro h
          apply ha
          apply Multiplicative.toAdd.injective
          ext k
          refine Fin.lastCases hlast (fun k ↦ ?_) k
          simpa [Fin.init] using congrFun (congrArg Multiplicative.toAdd h) k
        rw [TwistedMonoidAlgebra.scalarTrace_of_ne_one hinit,
          TwistedMonoidAlgebra.scalarTrace_of_ne_one ha]
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hlast, map_zero]
      have ha : a ≠ 1 := fun h ↦ hlast (by simp [h])
      rw [TwistedMonoidAlgebra.scalarTrace_of_ne_one ha]
  exact LinearMap.congr_fun hlin x

/-- `cubicCondExp N` commutes with `cubicInversion`. -/
@[simp]
theorem cubicCondExp_cubicInversion (N : ℕ) (x : CubicTorus (N + 1)) :
    cubicCondExp N (cubicInversion (N + 1) x) = cubicInversion N (cubicCondExp N x) := by
  have hlin : (cubicCondExp N).comp (cubicInversion (N + 1)).toLinearMap =
      (cubicInversion N).toLinearMap.comp (cubicCondExp N) := by
    refine (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin (N + 1) → ZMod 3))
      (cubicFactor (N + 1))).ext fun a ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, TwistedMonoidAlgebra.basis_apply,
      cubicInversion_of, cubicCondExp_of, toAdd_inv, Pi.neg_apply, neg_eq_zero]
    split_ifs with h
    · have hinit : Fin.init (-a.toAdd) = -(Fin.init a.toAdd) := rfl
      rw [hinit, ofAdd_neg, cubicInversion_of]
    · simp
  exact LinearMap.congr_fun hlin x

/-- `cubicCondExp N` intertwines `TwistedMonoidAlgebra.adjoint`. -/
@[simp]
theorem cubicCondExp_adjoint (N : ℕ) (x : CubicTorus (N + 1)) :
    cubicCondExp N (TwistedMonoidAlgebra.adjoint x) =
      TwistedMonoidAlgebra.adjoint (cubicCondExp N x) := by
  have hlin : (cubicCondExp N).comp (TwistedMonoidAlgebra.adjoint
        (k := ℂ) (G := Multiplicative (Fin (N + 1) → ZMod 3)) (α := cubicFactor (N + 1))) =
      (TwistedMonoidAlgebra.adjoint
        (k := ℂ) (G := Multiplicative (Fin N → ZMod 3)) (α := cubicFactor N)).comp
          (cubicCondExp N) := by
    refine (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin (N + 1) → ZMod 3))
      (cubicFactor (N + 1))).ext fun a ↦ ?_
    simp only [LinearMap.comp_apply, TwistedMonoidAlgebra.basis_apply,
      TwistedMonoidAlgebra.adjoint_of, cubicCondExp_of, toAdd_inv, Pi.neg_apply, neg_eq_zero]
    split_ifs with h
    · have hinit : Fin.init (-a.toAdd) = -(Fin.init a.toAdd) := rfl
      rw [hinit, ofAdd_neg, TwistedMonoidAlgebra.adjoint_of]
    · simp
  exact LinearMap.congr_fun hlin x

/-- Left `cubicIncl N`-module property of `cubicCondExp N`. -/
theorem cubicCondExp_mul_cubicIncl_left (N : ℕ) (x : CubicTorus N) (y : CubicTorus (N + 1)) :
    cubicCondExp N (cubicIncl N x * y) = x * cubicCondExp N y := by
  have hright (a : Multiplicative (Fin N → ZMod 3)) :
      (cubicCondExp N).comp (LinearMap.mulLeft ℂ (cubicIncl N (TwistedMonoidAlgebra.of a))) =
        (LinearMap.mulLeft ℂ (TwistedMonoidAlgebra.of a)).comp (cubicCondExp N) := by
    refine (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin (N + 1) → ZMod 3))
      (cubicFactor (N + 1))).ext fun b ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, TwistedMonoidAlgebra.basis_apply,
      cubicIncl_of, TwistedMonoidAlgebra.of_mul_of, map_smul, cubicCondExp_of, toAdd_mul,
      cubicExtendHom_apply, toAdd_ofAdd, Pi.add_apply, Fin.snoc_last, zero_add]
    split_ifs with hlast
    · have hbe : b = cubicExtendHom N (Multiplicative.ofAdd (Fin.init b.toAdd)) := by
        apply Multiplicative.toAdd.injective
        ext k
        refine Fin.lastCases ?_ (fun k ↦ ?_) k
        · simp [hlast]
        · simp [Fin.init]
      have hfac :
          cubicFactor (N + 1) (Multiplicative.ofAdd (Fin.snoc a.toAdd 0)) b =
            cubicFactor N a (Multiplicative.ofAdd (Fin.init b.toAdd)) := by
        conv_lhs => rw [← cubicExtendHom_apply, hbe]
        exact (cubicFactor_cubicExtendHom N a _).symm
      have hinit : Fin.init (Fin.snoc a.toAdd 0 + b.toAdd) = a.toAdd + Fin.init b.toAdd := by
        ext k; simp [Fin.init]
      rw [hfac, hinit, ofAdd_add, ofAdd_toAdd, TwistedMonoidAlgebra.of_mul_of]
    · simp
  have hleft :
      ((cubicCondExp N).comp (LinearMap.mulRight ℂ y)).comp (cubicIncl N).toLinearMap =
        LinearMap.mulRight ℂ (cubicCondExp N y) := by
    refine (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
      (cubicFactor N)).ext fun a ↦ ?_
    simpa [LinearMap.mulLeft_apply] using LinearMap.congr_fun (hright a) y
  exact LinearMap.congr_fun hleft x

/-- Right `cubicIncl N`-module property of `cubicCondExp N`. -/
theorem cubicCondExp_mul_cubicIncl_right (N : ℕ) (y : CubicTorus (N + 1)) (x : CubicTorus N) :
    cubicCondExp N (y * cubicIncl N x) = cubicCondExp N y * x := by
  have h := congrArg TwistedMonoidAlgebra.adjoint
    (cubicCondExp_mul_cubicIncl_left N (TwistedMonoidAlgebra.adjoint x)
      (TwistedMonoidAlgebra.adjoint y))
  simp only [cubicIncl_adjoint, ← adjoint_mul_cubicTorus, cubicCondExp_adjoint,
    TwistedMonoidAlgebra.adjoint_adjoint] at h
  exact h

/-- `cubicCondExp N` maps `cubicFixed (N + 1)` into `cubicFixed N`. -/
theorem cubicCondExp_mem_cubicFixed (N : ℕ) {x : CubicTorus (N + 1)}
    (hx : x ∈ cubicFixed (N + 1)) : cubicCondExp N x ∈ cubicFixed N := by
  rw [mem_cubicFixed_iff] at hx ⊢
  rw [← cubicCondExp_cubicInversion, hx]

/-- The trace-preserving conditional expectation `cubicFixed (N + 1) →ₗ[ℂ] cubicFixed N`
obtained by restricting `cubicCondExp N` to inversion-fixed elements. -/
noncomputable def cubicFixedCondExp (N : ℕ) : cubicFixed (N + 1) →ₗ[ℂ] cubicFixed N :=
  ((cubicCondExp N).comp (cubicFixed (N + 1)).toSubmodule.subtype).codRestrict
    (cubicFixed N).toSubmodule fun x ↦ cubicCondExp_mem_cubicFixed N x.2

/-- Coercing `cubicFixedCondExp` to the ambient cubic torus recovers `cubicCondExp`. -/
@[simp]
theorem coe_cubicFixedCondExp (N : ℕ) (x : cubicFixed (N + 1)) :
    (cubicFixedCondExp N x : CubicTorus N) = cubicCondExp N x :=
  (rfl)

/-- `cubicFixedCondExp N` is a left inverse to `cubicFixedIncl N`. -/
@[simp]
theorem cubicFixedCondExp_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    cubicFixedCondExp N (cubicFixedIncl N x) = x :=
  Subtype.ext (cubicCondExp_cubicIncl N (x : CubicTorus N))

/-- `cubicFixedCondExp N` preserves `TwistedMonoidAlgebra.scalarTrace`. -/
theorem scalarTrace_cubicFixedCondExp (N : ℕ) (x : cubicFixed (N + 1)) :
    TwistedMonoidAlgebra.scalarTrace (cubicFixedCondExp N x : CubicTorus N) =
      TwistedMonoidAlgebra.scalarTrace (x : CubicTorus (N + 1)) :=
  scalarTrace_cubicCondExp N (x : CubicTorus (N + 1))

/-- `cubicFixedCondExp N` intertwines `cubicFixedAdjoint`. -/
@[simp]
theorem cubicFixedCondExp_cubicFixedAdjoint (N : ℕ) (x : cubicFixed (N + 1)) :
    cubicFixedCondExp N (cubicFixedAdjoint (N + 1) x) =
      cubicFixedAdjoint N (cubicFixedCondExp N x) := by
  apply Subtype.ext
  simp [cubicCondExp_adjoint]

/-- Left `cubicFixedIncl N`-module property of `cubicFixedCondExp N`. -/
theorem cubicFixedCondExp_mul_cubicFixedIncl_left (N : ℕ) (x : cubicFixed N)
    (y : cubicFixed (N + 1)) :
    cubicFixedCondExp N (cubicFixedIncl N x * y) = x * cubicFixedCondExp N y :=
  Subtype.ext (cubicCondExp_mul_cubicIncl_left N (x : CubicTorus N) (y : CubicTorus (N + 1)))

/-- Right `cubicFixedIncl N`-module property of `cubicFixedCondExp N`. -/
theorem cubicFixedCondExp_mul_cubicFixedIncl_right (N : ℕ) (y : cubicFixed (N + 1))
    (x : cubicFixed N) :
    cubicFixedCondExp N (y * cubicFixedIncl N x) = cubicFixedCondExp N y * x :=
  Subtype.ext (cubicCondExp_mul_cubicIncl_right N (y : CubicTorus (N + 1)) (x : CubicTorus N))

/-! ### Tower compatibility and the Markov trace identity at `δ = √3` -/

/-- `cubicFixedHom` intertwines Temperley–Lieb `strandIncl` with `cubicFixedIncl`. -/
theorem cubicFixedHom_strandIncl (n : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1)) :
    cubicFixedHom (n + 2) (strandIncl x) =
      cubicFixedIncl n (cubicFixedHom (n + 1) x) := by
  have hhom : (cubicFixedHom (n + 2)).comp strandIncl =
      (cubicFixedIncl n).comp (cubicFixedHom (n + 1)) := by
    apply TemperleyLieb.hom_ext
    intro i
    apply Subtype.ext
    simp only [AlgHom.comp_apply, strandIncl_e, coe_cubicFixedHom_e, coe_cubicFixedIncl]
    rw [coe_cubicFixedHom_e (n + 1) i, map_smul]
    exact congrArg ((Real.sqrt 3 : ℂ) • ·) (cubicIncl_cubicProjection n i).symm
  exact AlgHom.congr_fun hhom x

/-- Multiplying an included element `cubicIncl N a` on the right by the last cubic projection
`cubicProjection (N + 1) (Fin.last N)` scales its scalar trace by `3⁻¹`. -/
theorem scalarTrace_cubicIncl_mul_cubicProjection_last (N : ℕ) (a : CubicTorus N) :
    TwistedMonoidAlgebra.scalarTrace
        (cubicIncl N a * cubicProjection (N + 1) (Fin.last N)) =
      (3 : ℂ)⁻¹ * TwistedMonoidAlgebra.scalarTrace a := by
  have hnot1 : Multiplicative.ofAdd (Pi.single (Fin.last N) (1 : ZMod 3)) ∉
      Set.range (cubicExtendHom N) := by
    rintro ⟨b, hb⟩
    have h0 := congrFun (congrArg Multiplicative.toAdd hb) (Fin.last N)
    simp at h0
  have hnot2 : Multiplicative.ofAdd (-(Pi.single (Fin.last N) (1 : ZMod 3))) ∉
      Set.range (cubicExtendHom N) := by
    rintro ⟨b, hb⟩
    have h0 := congrFun (congrArg Multiplicative.toAdd hb) (Fin.last N)
    simp at h0
  have hterm1 : TwistedMonoidAlgebra.scalarTrace
      (cubicIncl N a * cubicSite (N + 1) (Fin.last N)) = 0 := by
    rw [cubicIncl_def, cubicSite_def]
    exact TwistedMonoidAlgebra.scalarTrace_map_mul_of_eq_zero (cubicExtendHom N)
      (cubicFactor_cubicExtendHom N) hnot1 a
  have hterm2 : TwistedMonoidAlgebra.scalarTrace
      (cubicIncl N a * cubicSite (N + 1) (Fin.last N) ^ 2) = 0 := by
    rw [cubicIncl_def, cubicSite_sq_eq_of_neg]
    exact TwistedMonoidAlgebra.scalarTrace_map_mul_of_eq_zero (cubicExtendHom N)
      (cubicFactor_cubicExtendHom N) hnot2 a
  rw [cubicProjection_def, mul_smul_comm, map_smul, mul_add, mul_add, mul_one, map_add, map_add,
    hterm1, hterm2, add_zero, add_zero, scalarTrace_cubicIncl, smul_eq_mul]

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√3 : ℂ) m` obtained by pulling back
`(√3) ^ m` times `TwistedMonoidAlgebra.scalarTrace` along `cubicFixedHom m`. -/
noncomputable def cubicFixedTrace (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 3 : ℂ) ^ m) •
    (TwistedMonoidAlgebra.scalarTrace ∘ₗ
      (cubicFixed (m - 1)).val.toLinearMap ∘ₗ (cubicFixedHom m).toLinearMap)

/-- Evaluation formula for `cubicFixedTrace`. -/
theorem cubicFixedTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedTrace m x =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.scalarTrace (cubicFixedHom m x : CubicTorus (m - 1)) := by
  simp [cubicFixedTrace]

/-- **The cubic quantum torus scalar trace defines a Markov trace at `δ = √3`.** -/
theorem isMarkovTrace_cubicFixedTrace :
    IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) cubicFixedTrace where
  map_one m := by
    rw [cubicFixedTrace_apply, map_one, Subalgebra.coe_one,
      TwistedMonoidAlgebra.scalarTrace_one, mul_one]
  map_mul_comm m x y := by
    rw [cubicFixedTrace_apply, cubicFixedTrace_apply, map_mul, map_mul,
      Subalgebra.coe_mul, Subalgebra.coe_mul, TwistedMonoidAlgebra.scalarTrace_mul_comm]
  map_strandIncl n x := by
    simp only [cubicFixedTrace_apply, cubicFixedHom_strandIncl, coe_cubicFixedIncl,
      scalarTrace_cubicIncl, pow_succ']
    ring
  map_strandIncl_mul_e_last n x := by
    have he : ((cubicFixedHom (n + 2) (e (Real.sqrt 3 : ℂ) (Fin.last n)) :
        cubicFixed (n + 2 - 1)) : CubicTorus (n + 2 - 1)) =
        (Real.sqrt 3 : ℂ) • cubicProjection (n + 1) (Fin.last n) :=
      coe_cubicFixedHom_e (n + 2) (Fin.last n)
    have hsq : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    rw [cubicFixedTrace_apply, cubicFixedTrace_apply, map_mul, Subalgebra.coe_mul,
      cubicFixedHom_strandIncl, coe_cubicFixedIncl, he, mul_smul_comm, map_smul,
      scalarTrace_cubicIncl_mul_cubicProjection_last, smul_eq_mul, pow_succ, mul_assoc,
      ← mul_assoc (Real.sqrt 3 : ℂ), ← mul_assoc ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)),
      hsq, mul_inv_cancel₀ (by norm_num), one_mul]

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- Every Markov trace on `TemperleyLieb ℂ (√3 : ℂ)` coincides with `cubicFixedTrace`. -/
theorem eq_cubicFixedTrace (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) :
    tr = cubicFixedTrace :=
  htr.unique isMarkovTrace_cubicFixedTrace

/-- **The Markov trace at `δ = √3` as the cubic quantum torus scalar trace**: for every Markov
trace `tr`, `tr m x = (√3 : ℂ) ^ m * scalarTrace (cubicFixedHom m x)`. -/
theorem apply_eq_mul_scalarTrace_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    tr m x =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.scalarTrace (cubicFixedHom m x : CubicTorus (m - 1)) := by
  rw [htr.eq_cubicFixedTrace, cubicFixedTrace_apply]

/-- **Positivity of the Markov trace at `δ = √3`** (the `m = 6` discrete-series point
`2 cos (π / 6)` of Jones's positivity theorem): `0 ≤ tr m (star x * x)` on every number of
strands. -/
theorem map_star_mul_self_nonneg_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  have hz := scalarTrace_adjoint_mul_self_cubicTorus_nonneg
    (cubicFixedHom m x : CubicTorus (m - 1))
  have hz0 : ((0 : ℝ) : ℂ) ≤
      TwistedMonoidAlgebra.scalarTrace
        (TwistedMonoidAlgebra.adjoint (cubicFixedHom m x : CubicTorus (m - 1)) *
          (cubicFixedHom m x : CubicTorus (m - 1))) := by
    simpa using hz
  rw [htr.apply_eq_mul_scalarTrace_cubicFixedHom, map_mul, Subalgebra.coe_mul,
    coe_cubicFixedHom_star, Complex.eq_re_of_ofReal_le hz0, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.zero_le_real]
  exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp hz).1

/-- At `δ = √3`, `tr m (star x * x) = 0` if and only if `cubicFixedHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ cubicFixedHom m x = 0 := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  rw [htr.apply_eq_mul_scalarTrace_cubicFixedHom, map_mul, Subalgebra.coe_mul,
    coe_cubicFixedHom_star, mul_eq_zero, or_iff_right (pow_ne_zero m hne),
    scalarTrace_adjoint_mul_self_cubicTorus_eq_zero_iff, ZeroMemClass.coe_eq_zero]

/-! ### Kernel = trace radical and the Jones quotient equivalence -/

/-- **The trace radical at `δ = √3` is the kernel of `cubicFixedHom`.** -/
theorem traceRadical_eq_ker_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicFixedHom m) := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  ext x
  rw [LinearMap.mem_traceRadical, RingHom.mem_ker]
  constructor
  · intro hx
    have hstar := hx (star x)
    rw [htr.apply_eq_mul_scalarTrace_cubicFixedHom, map_mul, Subalgebra.coe_mul,
      coe_cubicFixedHom_star, TwistedMonoidAlgebra.scalarTrace_mul_comm, mul_eq_zero,
      or_iff_right (pow_ne_zero m hne), scalarTrace_adjoint_mul_self_cubicTorus_eq_zero_iff]
      at hstar
    exact Subtype.ext hstar
  · intro hx y
    rw [htr.apply_eq_mul_scalarTrace_cubicFixedHom, map_mul, hx, zero_mul,
      Subalgebra.coe_zero, map_zero, mul_zero]

/-- At `δ = √3`, the null vectors of `x ↦ tr m (star x * x)` are precisely the trace radical. -/
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ x ∈ (tr m).traceRadical (htr.map_mul_comm m) := by
  rw [htr.map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero,
    htr.traceRadical_eq_ker_cubicFixedHom, RingHom.mem_ker]

/-- **The Jones quotient at `δ = √3` is isomorphic to the inversion-fixed cubic quantum torus**
`cubicFixed (m - 1)`. -/
noncomputable def quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) ≃ₐ[ℂ]
      cubicFixed (m - 1) :=
  (Ideal.quotientEquivAlgOfEq ℂ (htr.traceRadical_eq_ker_cubicFixedHom m)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (cubicFixedHom_surjective m))

/-- `quotientCubicFixedEquiv` evaluates on a quotient representative via `cubicFixedHom`. -/
@[simp]
theorem quotientCubicFixedEquiv_mk
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    htr.quotientCubicFixedEquiv m
        (Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x) =
      cubicFixedHom m x := by
  simp [quotientCubicFixedEquiv, Ideal.quotientEquivAlgOfEq_mk]

/-- `quotientCubicFixedEquiv` intertwines the Temperley–Lieb quotient strand map
`quotientStrandIncl` with `cubicFixedIncl`. -/
theorem quotientCubicFixedEquiv_quotientStrandIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientCubicFixedEquiv (n + 2) (htr.quotientStrandIncl n q) =
      cubicFixedIncl n (htr.quotientCubicFixedEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [htr.quotientStrandIncl_mk, htr.quotientCubicFixedEquiv_mk,
    htr.quotientCubicFixedEquiv_mk, cubicFixedHom_strandIncl]

/-- `(quotientCubicFixedEquiv m).symm` maps `cubicFixedHom m x` back to the quotient class
of `x`. -/
@[simp]
theorem quotientCubicFixedEquiv_symm_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (htr.quotientCubicFixedEquiv m).symm (cubicFixedHom m x) =
      Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x :=
  (htr.quotientCubicFixedEquiv m).injective (by simp)

/-- `(quotientCubicFixedEquiv _).symm` intertwines `cubicFixedIncl` with `quotientStrandIncl`. -/
theorem quotientCubicFixedEquiv_symm_cubicFixedIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (y : cubicFixed n) :
    (htr.quotientCubicFixedEquiv (n + 2)).symm (cubicFixedIncl n y) =
      htr.quotientStrandIncl n ((htr.quotientCubicFixedEquiv (n + 1)).symm y) :=
  (htr.quotientCubicFixedEquiv (n + 2)).injective (by
    rw [AlgEquiv.apply_symm_apply, htr.quotientCubicFixedEquiv_quotientStrandIncl,
      AlgEquiv.apply_symm_apply])

/-- The induced trace on the `m`-strand Temperley–Lieb quotient at `δ = √3` is `(√3 : ℂ) ^ m` times
`TwistedMonoidAlgebra.scalarTrace` under `quotientCubicFixedEquiv`. -/
theorem quotientTrace_eq_mul_scalarTrace_quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.scalarTrace
          (htr.quotientCubicFixedEquiv m q : CubicTorus (m - 1)) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_scalarTrace_cubicFixedHom]

/-- Transporting `quotientTrace` across `(quotientCubicFixedEquiv m).symm` gives `(√3 : ℂ) ^ m`
times `TwistedMonoidAlgebra.scalarTrace`. -/
@[simp]
theorem quotientTrace_quotientCubicFixedEquiv_symm
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) (x : cubicFixed (m - 1)) :
    (tr m).quotientTrace (htr.map_mul_comm m) ((htr.quotientCubicFixedEquiv m).symm x) =
      (Real.sqrt 3 : ℂ) ^ m * TwistedMonoidAlgebra.scalarTrace (x : CubicTorus (m - 1)) := by
  simp [htr.quotientTrace_eq_mul_scalarTrace_quotientCubicFixedEquiv]

/-- The `m`-strand Temperley–Lieb trace quotient at `δ = √3` has complex dimension
`(3 ^ (m - 1) + 1) / 2`. -/
@[simp]
theorem finrank_quotient_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    Module.finrank ℂ
        (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) =
      (3 ^ (m - 1) + 1) / 2 := by
  rw [(htr.quotientCubicFixedEquiv m).toLinearEquiv.finrank_eq, finrank_cubicFixed]

end IsMarkovTrace

/-- Specialization of `IsMarkovTrace.apply_eq_mul_scalarTrace_cubicFixedHom` to the spin-model
`markovTrace` at any unit `q : ℂˣ` satisfying `(√3 : ℂ) = -(q + q⁻¹)`. -/
theorem markovTrace_eq_mul_scalarTrace_cubicFixedHom (q : ℂˣ)
    (hq : (Real.sqrt 3 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    markovTrace q hq x =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.scalarTrace (cubicFixedHom m x : CubicTorus (m - 1)) :=
  (isMarkovTrace_markovTrace q hq).apply_eq_mul_scalarTrace_cubicFixedHom m x

/-! ### Packaged cubic quantum torus model and five-strand Jones–Wenzl vanishing -/

/-- **The inversion-fixed cubic quantum torus model of `TemperleyLieb ℂ (√3 : ℂ) m`.** For every
Markov trace `tr` at loop value `√3` and every `m : ℕ`, there is a surjective `ℂ`-algebra
homomorphism `F : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` sending each generator
`e j` to `(√3 : ℂ) • cubicProjection (m - 1) j`, intertwining `star` with
`TwistedMonoidAlgebra.adjoint`, expressing `tr m` as `(√3 : ℂ) ^ m` times
`TwistedMonoidAlgebra.scalarTrace`, and having kernel equal to the trace radical
`(tr m).traceRadical`. -/
theorem exists_cubicFixedModel
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1),
      Function.Surjective F ∧
      (∀ j : Fin (m - 1),
        (F (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
          (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        (F (star x) : CubicTorus (m - 1)) =
          TwistedMonoidAlgebra.adjoint (F x)) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        tr m x =
          (Real.sqrt 3 : ℂ) ^ m *
            TwistedMonoidAlgebra.scalarTrace (F x : CubicTorus (m - 1))) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨cubicFixedHom m,
    cubicFixedHom_surjective m,
    coe_cubicFixedHom_e m,
    coe_cubicFixedHom_star,
    htr.apply_eq_mul_scalarTrace_cubicFixedHom m,
    (htr.traceRadical_eq_ker_cubicFixedHom m).symm⟩

/-- At `δ = √3`, `cubicFixedHom 5` maps the five-strand Jones–Wenzl projection
`jonesWenzl (√3 : ℂ) 5` to `0`. -/
@[simp]
theorem cubicFixedHom_jonesWenzl_five :
    cubicFixedHom 5 (jonesWenzl (Real.sqrt 3 : ℂ) 5) = 0 := by
  have hsq : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hq3 : qInt ℂ (Real.sqrt 3 : ℂ) 3 = 2 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 1, qInt_two, qInt_one, hsq]
    norm_num
  have hq4 : qInt ℂ (Real.sqrt 3 : ℂ) 4 = (Real.sqrt 3 : ℂ) := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 2, hq3, qInt_two]
    ring
  have hq5 : qInt ℂ (Real.sqrt 3 : ℂ) 5 = 1 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 3, hq4, hq3, hsq]
    norm_num
  have hq6 : qInt ℂ (Real.sqrt 3 : ℂ) 6 = 0 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 4, hq5, hq4]
    ring
  have hunits : ∀ k ∈ Finset.Icc 1 5, IsUnit (qInt ℂ (Real.sqrt 3 : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · simp
    · simp [qInt_two]
    · simp [hq3]
    · simp [hq4]
    · simp [hq5]
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicFixedTrace.traceRadical_eq_ker_cubicFixedHom 5,
    isMarkovTrace_cubicFixedTrace.jonesWenzl_mem_traceRadical_iff hunits]
  exact hq6

end TauCeti.TemperleyLieb
