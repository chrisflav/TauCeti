/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Invariant forms on simply laced root systems

In a simply laced irreducible root system all roots have the same length for every invariant form.
Consequently two roots whose sum is again a root have Cartan integer `-1`.

When the roots and coroots span, there is a unique invariant form `RootPairing.Base.simplyLacedForm`
giving every root squared length `2`: on the simple-root basis it evaluates against the simple
coroots, `⟨αᵢ, x⟩ = ⟨x, αᵢ^∨⟩`, and Cartan-matrix symmetry makes this bilinear form symmetric and
reflection-invariant. Because the squared root lengths determine the form on every simple root, it
is independent of the simply laced base and invariant under the full automorphism group `P.Aut`.
Over a linearly ordered field it is positive definite, as its restriction to each component is a
positive multiple of the canonical root form.

## Main definitions

* `RootPairing.Base.simplyLacedForm`: the unique invariant form on a simply laced root system
  giving every root squared length `2`.

## Main results

* `RootPairing.InvariantForm.apply_root_root_eq_of_isSimplyLaced`: in a simply laced irreducible
  root system all roots have the same length.
* `RootPairing.Base.pairingIn_eq_neg_one_of_isSimplyLaced`: two roots whose sum is a root have
  Cartan integer `-1`.
* `RootPairing.Base.simplyLacedForm_apply_root_self`,
  `RootPairing.Base.simplyLacedForm_apply_root_right`, and
  `RootPairing.Base.simplyLacedForm_apply_root_left`: `simplyLacedForm` gives every root squared
  length `2` and identifies pairing with `αᵢ` with evaluation of `αᵢ^∨`.
* `RootPairing.Base.eq_simplyLacedForm_of_apply_root_self` and
  `RootPairing.Base.simplyLacedForm_weightMap`: uniqueness and `P.Aut`-invariance of
  `simplyLacedForm`.
* `RootPairing.Base.posDef_simplyLacedForm`: over a linearly ordered field, `simplyLacedForm` is
  positive definite.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1, no. 4.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, page 1.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- **In a simply laced irreducible root system all roots have the same length** for every invariant
form. Irreducibility is needed: a system of type `A₁ × A₁` has invariant forms giving its two
components different lengths. -/
theorem InvariantForm.apply_root_root_eq_of_isSimplyLaced [CharZero R] [IsDomain R] [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (B : P.InvariantForm) (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) (i j : ι) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  have hsimple (l m : b.support) : B.form (P.root l) (P.root l) = B.form (P.root m) (P.root m) := by
    refine b.induction_on_cartanMatrix
      (fun k : b.support ↦ B.form (P.root l) (P.root l) = B.form (P.root k) (P.root k)) rfl ?_
    intro u v (huv : B.form (P.root l) (P.root l) = _) hne
    rcases eq_or_ne u v with rfl | hne'
    · exact huv
    have hvu : b.cartanMatrix v u = -1 := (hsl hne'.symm).resolve_left hne
    have huv' : b.cartanMatrix u v = -1 :=
      (hsl hne').resolve_left (b.cartanMatrix_apply_eq_zero_iff_symm.not.mp hne)
    have hp (x y : b.support) (hxy : b.cartanMatrix x y = -1) : P.pairing x y = -1 := by
      have : P.pairingIn ℤ x y = -1 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using hxy
      rw [← P.algebraMap_pairingIn ℤ, this]
      simp
    have := B.pairing_mul_eq_pairing_mul_swap (u : ι) v
    rw [hp v u hvu, hp u v huv'] at this
    rw [huv]
    linear_combination -this
  have : Nonempty ι := ⟨i⟩
  obtain ⟨l⟩ : Nonempty b.support := b.support_nonempty.to_subtype
  have hall (x : ι) : B.form (P.root x) (P.root x) = B.form (P.root l) (P.root l) := by
    refine b.induction_simple_reflect x
      (p := fun x ↦ B.form (P.root x) (P.root x) = B.form (P.root l) (P.root l))
      (fun k hk ↦ hsimple ⟨k, hk⟩ l) fun k r hk _ ↦ ?_
    rw [← hk, root_reflectionPerm, B.apply_reflection_reflection]
  rw [hall i, hall j]

namespace Base

section Irreducible

variable [CharZero R] (b : P.Base) [P.IsCrystallographic] [Finite ι] [IsDomain R] [P.IsReduced]
  [P.IsIrreducible]

/-- **In a simply laced irreducible root system, two roots whose sum is a root have Cartan integer
`-1`.** -/
theorem pairingIn_eq_neg_one_of_isSimplyLaced (hsl : b.cartanMatrix.IsSimplyLaced) {i k m : ι}
    (hm : P.root m = P.root i + P.root k) : P.pairingIn ℤ i k = -1 := by
  have := Fintype.ofFinite ι
  let B := P.toInvariantForm
  have hlen (x y : ι) := B.apply_root_root_eq_of_isSimplyLaced b hsl x y
  have hexp := B.form_root_add_root_self k i
  rw [add_comm (P.root k), ← hm, hlen m k, hlen i k] at hexp
  have hz : (P.pairing i k + 1) * B.form (P.root k) (P.root k) = 0 := by
    linear_combination -hexp
  have hp : P.pairing i k = -1 := by
    have := (mul_eq_zero.mp hz).resolve_right (B.ne_zero k)
    linear_combination this
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [algebraMap_pairingIn, hp, map_neg, map_one]

end Irreducible

section CanonicalForm

/-- The Cartan matrix of a simply laced base is symmetric: off-diagonal entries are `0` or `-1`,
and zero entries occur symmetrically. -/
theorem cartanMatrix_isSymm_of_isSimplyLaced [CharZero R] [IsDomain R] [P.IsCrystallographic]
    (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced) :
    b.cartanMatrix.IsSymm := by
  ext i j
  rw [Matrix.transpose_apply]
  rcases eq_or_ne i j with rfl | hne
  · rfl
  by_cases h0 : b.cartanMatrix i j = 0
  · rw [h0, b.cartanMatrix_apply_eq_zero_iff_symm.mp h0]
  · have hij : b.cartanMatrix i j = -1 := (hsl hne).resolve_left h0
    have hji : b.cartanMatrix j i = -1 :=
      (hsl hne.symm).resolve_left (b.cartanMatrix_apply_eq_zero_iff_symm.not.mp h0)
    rw [hji, hij]

/-- Auxiliary bilinear form sending the `i`-th simple root to the `i`-th simple coroot
functional. -/
private noncomputable def simplyLacedBilin [P.IsRootSystem] (b : P.Base) :
    LinearMap.BilinForm R M :=
  b.toWeightBasis.constr ℤ fun i : b.support ↦ P.coroot' i

private theorem simplyLacedBilin_apply_simple [P.IsRootSystem] (b : P.Base) (i : b.support)
    (y : M) : b.simplyLacedBilin (P.root i) y = P.coroot' i y := by
  simpa [simplyLacedBilin, b.toWeightBasis_apply] using
    congrArg (fun f : M →ₗ[R] R ↦ f y)
      (b.toWeightBasis.constr_basis ℤ (fun j : b.support ↦ P.coroot' j) i)

variable [CharZero R] [IsDomain R] [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)

private theorem simplyLacedBilin_isSymm (hsl : b.cartanMatrix.IsSimplyLaced) :
    LinearMap.IsSymm b.simplyLacedBilin := by
  have heq : b.simplyLacedBilin = b.simplyLacedBilin.flip := by
    refine b.toWeightBasis.ext fun i ↦ b.toWeightBasis.ext fun j ↦ ?_
    change b.simplyLacedBilin (b.toWeightBasis i) (b.toWeightBasis j) =
      b.simplyLacedBilin (b.toWeightBasis j) (b.toWeightBasis i)
    rw [b.toWeightBasis_apply, b.toWeightBasis_apply,
      simplyLacedBilin_apply_simple, simplyLacedBilin_apply_simple,
      root_coroot'_eq_pairing, root_coroot'_eq_pairing]
    have hsym := congrFun (congrFun (b.cartanMatrix_isSymm_of_isSimplyLaced hsl) i) j
    rw [Matrix.transpose_apply] at hsym
    simp only [cartanMatrix, cartanMatrixIn_def] at hsym
    rw [← P.algebraMap_pairingIn ℤ j i, ← P.algebraMap_pairingIn ℤ i j, hsym]
  exact ⟨fun x y ↦ LinearMap.congr_fun₂ heq x y⟩

private theorem simplyLacedBilin_reflection_simple (hsl : b.cartanMatrix.IsSimplyLaced)
    {i : ι} (hi : i ∈ b.support) (x y : M) :
    b.simplyLacedBilin (P.reflection i x) (P.reflection i y) = b.simplyLacedBilin x y := by
  have hsym := b.simplyLacedBilin_isSymm hsl
  have hleft (z : M) : b.simplyLacedBilin (P.root i) z = P.coroot' i z :=
    b.simplyLacedBilin_apply_simple ⟨i, hi⟩ z
  have hright (z : M) : b.simplyLacedBilin z (P.root i) = P.coroot' i z :=
    (hsym.eq z (P.root i)).trans (hleft z)
  have htwo : P.coroot' i (P.root i) = 2 := by
    rw [root_coroot'_eq_pairing, pairing_same]
  simp only [reflection_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    hleft, hright, htwo, smul_eq_mul]
  ring

variable [Finite ι] [P.IsReduced]

private theorem simplyLacedBilin_reflection (hsl : b.cartanMatrix.IsSimplyLaced)
    (k : ι) (x y : M) :
    b.simplyLacedBilin (P.reflection k x) (P.reflection k y) = b.simplyLacedBilin x y := by
  refine b.induction_simple_reflect k
    (p := fun k ↦ ∀ x y, b.simplyLacedBilin (P.reflection k x) (P.reflection k y) =
      b.simplyLacedBilin x y)
    (fun i hi x y ↦ b.simplyLacedBilin_reflection_simple hsl hi x y)
    (fun i j ih hj x y ↦ ?_) x y
  have hperm := LinearEquiv.congr_fun (P.reflection_reflectionPerm (i := i) (j := j))
  rw [hperm x, hperm y]
  simp only [mul_apply_eq_comp]
  rw [b.simplyLacedBilin_reflection_simple hsl hj, ih,
    b.simplyLacedBilin_reflection_simple hsl hj]

private theorem simplyLacedBilin_apply_root_self (hsl : b.cartanMatrix.IsSimplyLaced) (k : ι) :
    b.simplyLacedBilin (P.root k) (P.root k) = 2 := by
  refine b.induction_simple_reflect k
    (p := fun k ↦ b.simplyLacedBilin (P.root k) (P.root k) = 2)
    (fun i hi ↦ by
      rw [b.simplyLacedBilin_apply_simple ⟨i, hi⟩, root_coroot'_eq_pairing, pairing_same])
    fun i j ih _ ↦ ?_
  rw [root_reflectionPerm, b.simplyLacedBilin_reflection hsl j, ih]

/-- **The canonical norm-two invariant form on a simply laced root system.** It is the unique
invariant form giving every root squared length `2`; for every root `αᵢ` and weight `x` it
satisfies `⟨x, αᵢ⟩ = ⟨x, αᵢ^∨⟩`. -/
noncomputable def simplyLacedForm (hsl : b.cartanMatrix.IsSimplyLaced) : P.InvariantForm where
  form := b.simplyLacedBilin
  symm := b.simplyLacedBilin_isSymm hsl
  ne_zero i := by
    rw [b.simplyLacedBilin_apply_root_self hsl i]
    exact two_ne_zero
  isOrthogonal_reflection i x y := b.simplyLacedBilin_reflection hsl i x y

theorem simplyLacedForm_apply_root_self (hsl : b.cartanMatrix.IsSimplyLaced) (i : ι) :
    (b.simplyLacedForm hsl).form (P.root i) (P.root i) = 2 :=
  b.simplyLacedBilin_apply_root_self hsl i

@[simp]
theorem simplyLacedForm_apply_root_right (hsl : b.cartanMatrix.IsSimplyLaced) (x : M) (i : ι) :
    (b.simplyLacedForm hsl).form x (P.root i) = P.coroot' i x := by
  have h := (b.simplyLacedForm hsl).two_mul_apply_root x i
  rw [b.simplyLacedForm_apply_root_self hsl i, mul_comm (P.coroot' i x) 2] at h
  exact mul_left_cancel₀ (two_ne_zero (α := R)) h

@[simp]
theorem simplyLacedForm_apply_root_left (hsl : b.cartanMatrix.IsSimplyLaced) (i : ι) (x : M) :
    (b.simplyLacedForm hsl).form (P.root i) x = P.coroot' i x :=
  ((b.simplyLacedForm hsl).symm.eq (P.root i) x).trans (b.simplyLacedForm_apply_root_right hsl x i)

/-- **Uniqueness of the norm-two invariant form**: any invariant form giving every simple root
squared length `2` coincides with `b.simplyLacedForm hsl`. -/
theorem eq_simplyLacedForm_of_apply_root_self (hsl : b.cartanMatrix.IsSimplyLaced)
    (B : P.InvariantForm) (hB : ∀ i ∈ b.support, B.form (P.root i) (P.root i) = 2) :
    B = b.simplyLacedForm hsl := by
  have heq : B.form = (b.simplyLacedForm hsl).form := by
    refine b.toWeightBasis.ext fun i ↦ LinearMap.ext fun z ↦ ?_
    have hsym : B.form (P.root i) z = B.form z (P.root i) := B.symm.eq (P.root i) z
    rw [b.toWeightBasis_apply, hsym, b.simplyLacedForm_apply_root_left hsl i z]
    have h := B.two_mul_apply_root z i
    rw [hB i i.2, mul_comm (P.coroot' i z) 2] at h
    exact mul_left_cancel₀ (two_ne_zero (α := R)) h
  ext x y
  exact LinearMap.congr_fun₂ heq x y

/-- **Base-independence of `simplyLacedForm`**: any two simply laced bases determine the same
norm-two invariant form. -/
theorem simplyLacedForm_eq {b' : P.Base} (hsl : b.cartanMatrix.IsSimplyLaced)
    (hsl' : b'.cartanMatrix.IsSimplyLaced) :
    b.simplyLacedForm hsl = b'.simplyLacedForm hsl' :=
  b'.eq_simplyLacedForm_of_apply_root_self hsl' (b.simplyLacedForm hsl) fun i _ ↦
    b.simplyLacedForm_apply_root_self hsl i

/-- **Automorphism invariance of `simplyLacedForm`**: every automorphism of `P` (not necessarily
preserving `b`) preserves the norm-two invariant form. -/
@[simp]
theorem simplyLacedForm_weightMap (hsl : b.cartanMatrix.IsSimplyLaced) (σ : P.Aut) (x y : M) :
    (b.simplyLacedForm hsl).form (σ.weightMap x) (σ.weightMap y) =
      (b.simplyLacedForm hsl).form x y := by
  let B' : P.InvariantForm :=
    { form := (b.simplyLacedForm hsl).form.compl₁₂ σ.weightMap σ.weightMap
      symm := ⟨fun u v ↦ (b.simplyLacedForm hsl).symm.eq (σ.weightMap u) (σ.weightMap v)⟩
      ne_zero i := by
        simp only [LinearMap.compl₁₂_apply, Hom.root_weightMap_apply,
          b.simplyLacedForm_apply_root_self hsl]
        exact two_ne_zero
      isOrthogonal_reflection i u v := by
        simp only [LinearMap.compl₁₂_apply]
        have hw : ∀ z, σ.weightMap (P.reflection i z) =
            P.reflection (σ.indexEquiv i) (σ.weightMap z) :=
          σ.weightEquiv_reflection i
        rw [hw u, hw v, (b.simplyLacedForm hsl).apply_reflection_reflection] }
  have hEq : B' = b.simplyLacedForm hsl :=
    b.eq_simplyLacedForm_of_apply_root_self hsl B' fun i _ ↦ by
      change (b.simplyLacedForm hsl).form (σ.weightMap (P.root i)) (σ.weightMap (P.root i)) = 2
      rw [Hom.root_weightMap_apply, b.simplyLacedForm_apply_root_self hsl]
  exact congrArg (fun B : P.InvariantForm ↦ B.form x y) hEq

end CanonicalForm

section PosDef

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Module K M] [Module K N] {Q : RootPairing ι K M N}
  [Finite ι] [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]

/-- Over a linearly ordered field, the canonical norm-two invariant form on a finite reduced
crystallographic simply laced root system is positive definite. -/
theorem posDef_simplyLacedForm (b : Q.Base) (hsl : b.cartanMatrix.IsSimplyLaced) :
    (b.simplyLacedForm hsl).form.toQuadraticMap.PosDef := by
  have := Fintype.ofFinite ι
  let B₀ := Q.toInvariantForm
  set B := b.simplyLacedForm hsl
  rw [← InvariantForm.ofComponent_restrictComponent B, InvariantForm.posDef_ofComponent_iff]
  intro C x hx
  set i := C.nonempty_supp.some
  have hi : Q.componentOf i = C := (C.mem_supp_iff i).mp C.nonempty_supp.some_mem
  have hc : 0 < InvariantForm.componentScale B₀ B C := by
    rw [← hi, InvariantForm.componentScale_eq_div, b.simplyLacedForm_apply_root_self hsl i]
    exact div_pos two_pos (Q.rootForm_posDef (Q.root i) (Q.ne_zero i))
  rw [LinearMap.BilinMap.toQuadraticMap_apply, InvariantForm.restrictComponent_form_apply,
    InvariantForm.form_apply_eq_componentScale_mul B₀ B x.2 x.2]
  exact mul_pos hc (Q.rootForm_posDef (x : M) fun h ↦ hx (Subtype.ext h))

end PosDef

end Base

end RootPairing
