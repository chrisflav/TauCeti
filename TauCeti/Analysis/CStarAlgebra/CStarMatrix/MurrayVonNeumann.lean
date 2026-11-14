/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Unitization
import TauCeti.Data.Matrix.Block

/-!
# Murray–von Neumann equivalence and stabilized unitary rotation of C⋆-matrix projections

Two projections `p ∈ Mₘ(A)` and `q ∈ Mₙ(A)` over a (not necessarily unital) C⋆-algebra `A` are
*Murray–von Neumann equivalent* when `vᴴ * v = p` and `v * vᴴ = q` for a rectangular matrix
`v ∈ M_{n × m}(A)`. Across variable finite index types, this relation defines the semigroup `V(A)`
and hence `K₀(A)`.

This file develops the rectangular partial-isometry and equivalence calculus on `CStarMatrix`, and
proves stabilized unitary conjugacy and path homotopy in both the unital and non-unital settings:

* **Rectangular partial-isometry calculus:** over a non-unital C⋆-algebra `A`, idempotence of
  `v.conjTranspose * v` forces the partial-isometry law `v * v.conjTranspose * v = v`
  (`CStarMatrix.mul_conjTranspose_mul_self_of_isIdempotentElem`), so `v.conjTranspose * v` is a
  star projection if and only if `v * v.conjTranspose` is
  (`CStarMatrix.isStarProjection_conjTranspose_mul_self_iff`), and on square matrices this
  characterizes `TauCeti.IsPartialIsometry`
  (`CStarMatrix.isPartialIsometry_iff_isStarProjection_star_mul_self`).
* **Rectangular Murray–von Neumann equivalence (`CStarMatrix.MurrayVonNeumannEquiv`):**
  reflexivity on star projections, symmetry, transitivity across matrix sizes, compatibility with
  block-diagonal direct sums (`fromBlocks_zero₁₂_zero₂₁`), internal orthogonal addition
  (`add_of_mul_eq_zero`), zero-corner stabilization (`murrayVonNeumannEquiv_fromBlocks_zero_right`,
  `murrayVonNeumannEquiv_fromBlocks_zero_left`), finite reindexing (`reindexₐ`), entrywise
  `⋆`-homomorphisms (`map`, `mapStarAlgHom`), and unitary conjugacy.
* **Stabilized unitary conjugacy and explicit rotation paths:** over unital `A`, the self-adjoint
  unitary `CStarMatrix.stabilizedSwapUnitary` (`fromBlocks (1 - p) vᴴ v (1 - q)`) conjugates
  `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` and is joined to `1` by
  `Unitary.selfAdjointRotationPath`; composing with `permUnitary A (Equiv.sumComm n n)` yields
  `CStarMatrix.stabilizedConjUnitary` and `CStarMatrix.stabilizedConjUnitaryPath`, conjugating
  `fromBlocks p 0 0 0` to `fromBlocks q 0 0 0` along an explicit rotation path. Passing through
  `Unitization ℂ A` and taking `A`-components produces explicit continuous paths of
  stabilized projections (`CStarMatrix.stabilizedSwapProjectionPath`,
  `CStarMatrix.stabilizedProjectionPath`, `MurrayVonNeumannEquiv.joined_fromBlocks_zero_swap`,
  `MurrayVonNeumannEquiv.joined_fromBlocks_zero`) for arbitrary non-unital C⋆-algebras `A`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Propositions 4.2.2, 4.3.2,
  and 4.6.2.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C*-Algebras*,
  Propositions 2.2.4–2.2.8.
* N. E. Wegge-Olsen, *K-Theory and C*-Algebras: A Friendly Approach*, Chapter 3.
-/

public section

open scoped ComplexOrder unitInterval

namespace CStarMatrix

section PartialIsometry

variable {m n A : Type*}

theorem isSelfAdjoint_conjTranspose_mul_self [Fintype n] [NonUnitalNonAssocSemiring A] [StarRing A]
    (v : CStarMatrix n m A) :
    IsSelfAdjoint (v.conjTranspose * v) := by
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

theorem isSelfAdjoint_mul_conjTranspose_self [Fintype m] [NonUnitalNonAssocSemiring A] [StarRing A]
    (v : CStarMatrix n m A) :
    IsSelfAdjoint (v * v.conjTranspose) := by
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

section CStar

variable [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `vᴴ * v` is idempotent for a rectangular matrix `v` over a C⋆-algebra, then
`v * vᴴ * v = v`. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem {v : CStarMatrix n m A}
    (hv : IsIdempotentElem (v.conjTranspose * v)) :
    v * v.conjTranspose * v = v := by
  set p : CStarMatrix m m A := v.conjTranspose * v
  set d : CStarMatrix n m A := v * v.conjTranspose * v - v
  suffices hd0 : d.conjTranspose * d = 0 from
    sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp hd0)
  have hvp : v * v.conjTranspose * v = v * p := CStarMatrix.mul_assoc v v.conjTranspose v
  have hd : d.conjTranspose = p * v.conjTranspose - v.conjTranspose := by
    simp only [d, p, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
      CStarMatrix.mul_assoc]
  calc
    d.conjTranspose * d
      = (p * v.conjTranspose - v.conjTranspose) * (v * p - v) := by rw [hd, ← hvp]
    _ = 0 := by
        simp only [CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.mul_assoc]
        simp only [← CStarMatrix.mul_assoc v.conjTranspose v p, p, hv.eq, sub_self]

/-- Dual rectangular partial-isometry identity: if `v * vᴴ` is idempotent, then
`vᴴ * v * vᴴ = vᴴ`. -/
theorem conjTranspose_mul_self_mul_conjTranspose_of_isIdempotentElem {v : CStarMatrix n m A}
    (hv : IsIdempotentElem (v * v.conjTranspose)) :
    v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
  simpa only [conjTranspose_conjTranspose] using
    mul_conjTranspose_mul_self_of_isIdempotentElem (v := v.conjTranspose)
      (by simpa only [conjTranspose_conjTranspose] using hv)

/-- For a rectangular `CStarMatrix`, `vᴴ * v` is idempotent if and only if `v * vᴴ` is. -/
theorem isIdempotentElem_conjTranspose_mul_self_iff {v : CStarMatrix n m A} :
    IsIdempotentElem (v.conjTranspose * v) ↔ IsIdempotentElem (v * v.conjTranspose) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [IsIdempotentElem, ← CStarMatrix.mul_assoc (v * v.conjTranspose) v v.conjTranspose,
      mul_conjTranspose_mul_self_of_isIdempotentElem h]
  · rw [IsIdempotentElem, ← CStarMatrix.mul_assoc (v.conjTranspose * v) v.conjTranspose v,
      conjTranspose_mul_self_mul_conjTranspose_of_isIdempotentElem h]

/-- For a rectangular `CStarMatrix`, `vᴴ * v` is a star projection if and only if `v * vᴴ` is. -/
theorem isStarProjection_conjTranspose_mul_self_iff {v : CStarMatrix n m A} :
    IsStarProjection (v.conjTranspose * v) ↔ IsStarProjection (v * v.conjTranspose) := by
  simp only [isStarProjection_iff, isIdempotentElem_conjTranspose_mul_self_iff,
    isSelfAdjoint_conjTranspose_mul_self, isSelfAdjoint_mul_conjTranspose_self]

/-- On square `CStarMatrix` algebras, `v` is a partial isometry if and only if `star v * v` is a
star projection. -/
theorem isPartialIsometry_iff_isStarProjection_star_mul_self {v : CStarMatrix n n A} :
    TauCeti.IsPartialIsometry v ↔ IsStarProjection (star v * v) :=
  ⟨TauCeti.IsPartialIsometry.isStarProjection_star_mul_self, fun h =>
    TauCeti.isPartialIsometry_iff.mpr
      (mul_conjTranspose_mul_self_of_isIdempotentElem h.isIdempotentElem)⟩

end CStar

end PartialIsometry

section MurrayVonNeumannEquiv

variable {l m m' n n' R A B : Type*}

/-- Rectangular Murray–von Neumann equivalence between `p : CStarMatrix m m A` and
`q : CStarMatrix n n A`: there exists `v : CStarMatrix n m A` with `vᴴ * v = p` and
`v * vᴴ = q`. -/
def MurrayVonNeumannEquiv [Fintype m] [Fintype n] [AddCommMonoid A] [Mul A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

theorem murrayVonNeumannEquiv_iff [Fintype m] [Fintype n] [AddCommMonoid A] [Mul A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    MurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  Iff.rfl

/-- Every star projection in `CStarMatrix m m A` is Murray–von Neumann equivalent to itself. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_refl [Fintype m] [AddCommMonoid A] [Mul A]
    [Star A] {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p p :=
  ⟨p, by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

@[symm]
theorem MurrayVonNeumannEquiv.symm [Fintype m] [Fintype n] [AddCommMonoid A] [Mul A]
    [InvolutiveStar A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    MurrayVonNeumannEquiv q p := by
  rcases h with ⟨v, hvp, hvq⟩
  exact ⟨v.conjTranspose, by simpa using hvq, by simpa using hvp⟩

theorem murrayVonNeumannEquiv_comm [Fintype m] [Fintype n] [AddCommMonoid A] [Mul A]
    [InvolutiveStar A] {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    MurrayVonNeumannEquiv p q ↔ MurrayVonNeumannEquiv q p :=
  ⟨MurrayVonNeumannEquiv.symm, MurrayVonNeumannEquiv.symm⟩

theorem MurrayVonNeumannEquiv.isSelfAdjoint_left [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    IsSelfAdjoint p := by
  rcases h with ⟨v, rfl, -⟩
  exact isSelfAdjoint_conjTranspose_mul_self v

theorem MurrayVonNeumannEquiv.isSelfAdjoint_right [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    IsSelfAdjoint q := by
  rcases h with ⟨v, -, rfl⟩
  exact isSelfAdjoint_mul_conjTranspose_self v

/-- Purely algebraic transitivity of `MurrayVonNeumannEquiv` for idempotent matrices. -/
theorem MurrayVonNeumannEquiv.trans_of_isIdempotentElem [Fintype l] [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix l l A} {q : CStarMatrix m m A}
    {r : CStarMatrix n n A} (hp : IsIdempotentElem p) (hr : IsIdempotentElem r)
    (h₁ : MurrayVonNeumannEquiv p q) (h₂ : MurrayVonNeumannEquiv q r) :
    MurrayVonNeumannEquiv p r := by
  rcases h₁ with ⟨v₁, hv₁p, hv₁q⟩
  rcases h₂ with ⟨v₂, hv₂q, hv₂r⟩
  refine ⟨v₂ * v₁, ?_, ?_⟩
  · calc
      (v₂ * v₁).conjTranspose * (v₂ * v₁)
        = (v₁.conjTranspose * v₂.conjTranspose) * (v₂ * v₁) := by rw [conjTranspose_mul]
      _ = v₁.conjTranspose * ((v₂.conjTranspose * v₂) * v₁) := by
          simp only [CStarMatrix.mul_assoc]
      _ = v₁.conjTranspose * ((v₁ * v₁.conjTranspose) * v₁) := by rw [hv₂q, ← hv₁q]
      _ = (v₁.conjTranspose * v₁) * (v₁.conjTranspose * v₁) := by
          simp only [CStarMatrix.mul_assoc]
      _ = p := by rw [hv₁p, hp.eq]
  · calc
      (v₂ * v₁) * (v₂ * v₁).conjTranspose
        = (v₂ * v₁) * (v₁.conjTranspose * v₂.conjTranspose) := by rw [conjTranspose_mul]
      _ = v₂ * ((v₁ * v₁.conjTranspose) * v₂.conjTranspose) := by
          simp only [CStarMatrix.mul_assoc]
      _ = v₂ * ((v₂.conjTranspose * v₂) * v₂.conjTranspose) := by rw [hv₁q, ← hv₂q]
      _ = (v₂ * v₂.conjTranspose) * (v₂ * v₂.conjTranspose) := by
          simp only [CStarMatrix.mul_assoc]
      _ = r := by rw [hv₂r, hr.eq]

/-- Over a C⋆-algebra, `MurrayVonNeumannEquiv` preserves `IsIdempotentElem`. -/
theorem MurrayVonNeumannEquiv.isIdempotentElem_iff [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : MurrayVonNeumannEquiv p q) :
    IsIdempotentElem p ↔ IsIdempotentElem q := by
  rcases h with ⟨v, rfl, rfl⟩
  exact isIdempotentElem_conjTranspose_mul_self_iff

/-- Over a C⋆-algebra, `MurrayVonNeumannEquiv` preserves `IsStarProjection`. -/
theorem MurrayVonNeumannEquiv.isStarProjection_iff [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : MurrayVonNeumannEquiv p q) :
    IsStarProjection p ↔ IsStarProjection q := by
  rcases h with ⟨v, rfl, rfl⟩
  exact isStarProjection_conjTranspose_mul_self_iff

/-- Transitivity of `MurrayVonNeumannEquiv` across matrix sizes over a C⋆-algebra. -/
theorem MurrayVonNeumannEquiv.trans [Fintype l] [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (hp : IsIdempotentElem p) (h₁ : MurrayVonNeumannEquiv p q)
    (h₂ : MurrayVonNeumannEquiv q r) :
    MurrayVonNeumannEquiv p r :=
  h₁.trans_of_isIdempotentElem hp (h₂.isIdempotentElem_iff.mp (h₁.isIdempotentElem_iff.mp hp)) h₂

/-- On square `CStarMatrix` algebras, Murray–von Neumann equivalence of a star projection `p` with
`q` is witnessed by a partial isometry `v` with initial projection `p` and final projection `q`. -/
theorem murrayVonNeumannEquiv_iff_exists_isPartialIsometry [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix n n A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  refine ⟨fun ⟨v, hvp, hvq⟩ => ⟨v, ?_, hvp, hvq⟩, fun ⟨v, _, hvp, hvq⟩ => ⟨v, hvp, hvq⟩⟩
  rw [isPartialIsometry_iff_isStarProjection_star_mul_self, star_eq_conjTranspose, hvp]
  exact hp

@[simp]
theorem murrayVonNeumannEquiv_zero_iff [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} :
    MurrayVonNeumannEquiv p (0 : CStarMatrix n n A) ↔ p = 0 := by
  refine ⟨fun ⟨v, hvp, hvq⟩ => ?_, fun hp => ?_⟩
  · rw [mul_conjTranspose_self_eq_zero.mp hvq, conjTranspose_zero, CStarMatrix.zero_mul] at hvp
    exact hvp.symm
  · subst hp
    exact ⟨0, by simp, by simp⟩

@[simp]
theorem zero_murrayVonNeumannEquiv_iff [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {q : CStarMatrix n n A} :
    MurrayVonNeumannEquiv (0 : CStarMatrix m m A) q ↔ q = 0 := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_zero_iff]

theorem murrayVonNeumannEquiv_of_isEmpty_right [Fintype m] [Fintype n] [IsEmpty n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    MurrayVonNeumannEquiv p q ↔ p = 0 := by
  have hq : q = 0 := by ext i; exact isEmptyElim i
  rw [hq, murrayVonNeumannEquiv_zero_iff]

/-- Block-diagonal direct sums respect `MurrayVonNeumannEquiv`. -/
theorem MurrayVonNeumannEquiv.fromBlocks_zero₁₂_zero₂₁ [Fintype m] [Fintype m'] [Fintype n]
    [Fintype n'] [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p₁ : CStarMatrix m m A} {p₂ : CStarMatrix m' m' A}
    {q₁ : CStarMatrix n n A} {q₂ : CStarMatrix n' n' A}
    (h₁ : MurrayVonNeumannEquiv p₁ q₁) (h₂ : MurrayVonNeumannEquiv p₂ q₂) :
    MurrayVonNeumannEquiv (fromBlocks p₁ 0 0 p₂) (fromBlocks q₁ 0 0 q₂) := by
  rcases h₁ with ⟨v₁, hv₁p, hv₁q⟩
  rcases h₂ with ⟨v₂, hv₂p, hv₂q⟩
  refine ⟨fromBlocks v₁ 0 0 v₂, ?_, ?_⟩ <;>
    simp [hv₁p, hv₁q, hv₂p, hv₂q]

/-- Orthogonal sums of equivalent star projections are Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.add_of_mul_eq_zero [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0)
    (h₁ : MurrayVonNeumannEquiv p₁ q₁) (h₂ : MurrayVonNeumannEquiv p₂ q₂) :
    MurrayVonNeumannEquiv (p₁ + p₂) (q₁ + q₂) := by
  rcases h₁ with ⟨v₁, hv₁p, hv₁q⟩
  rcases h₂ with ⟨v₂, hv₂p, hv₂q⟩
  have hId₁ : IsIdempotentElem (v₁.conjTranspose * v₁) := hv₁p.symm ▸ hp₁.isIdempotentElem
  have hId₂ : IsIdempotentElem (v₂.conjTranspose * v₂) := hv₂p.symm ▸ hp₂.isIdempotentElem
  have hv₁_p₁ : v₁ * p₁ = v₁ := by
    rw [← hv₁p, ← CStarMatrix.mul_assoc]
    exact mul_conjTranspose_mul_self_of_isIdempotentElem hId₁
  have hv₂_p₂ : v₂ * p₂ = v₂ := by
    rw [← hv₂p, ← CStarMatrix.mul_assoc]
    exact mul_conjTranspose_mul_self_of_isIdempotentElem hId₂
  have hp₂_v₂ : p₂ * v₂.conjTranspose = v₂.conjTranspose := by
    simpa only [conjTranspose_mul, ← star_eq_conjTranspose, hp₂.isSelfAdjoint.star_eq] using
      congrArg conjTranspose hv₂_p₂
  have hv₁_q₁ : v₁.conjTranspose * q₁ = v₁.conjTranspose := by
    rw [← hv₁q, ← CStarMatrix.mul_assoc]
    exact conjTranspose_mul_self_mul_conjTranspose_of_isIdempotentElem
      (isIdempotentElem_conjTranspose_mul_self_iff.mp hId₁)
  have hq₂_v₂ : q₂ * v₂ = v₂ := by
    rw [← hv₂q]
    exact mul_conjTranspose_mul_self_of_isIdempotentElem hId₂
  have hcross₁ : v₁.conjTranspose * v₂ = 0 := by
    rw [← hv₁_q₁, ← hq₂_v₂, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc q₁ q₂ v₂, hq,
      CStarMatrix.zero_mul, CStarMatrix.mul_zero]
  have hcross₂ : v₂.conjTranspose * v₁ = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose hcross₁
  have hcross₃ : v₁ * v₂.conjTranspose = 0 := by
    rw [← hv₁_p₁, ← hp₂_v₂, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc p₁ p₂ v₂.conjTranspose,
      hp, CStarMatrix.zero_mul, CStarMatrix.mul_zero]
  have hcross₄ : v₂ * v₁.conjTranspose = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose hcross₃
  refine ⟨v₁ + v₂, ?_, ?_⟩
  · simp only [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add,
      hv₁p, hv₂p, hcross₁, hcross₂, add_zero, zero_add]
  · simp only [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add,
      hv₁q, hv₂q, hcross₃, hcross₄, add_zero, zero_add]

/-- Reindexing both sides preserves `MurrayVonNeumannEquiv` without assuming unitality of `A`. -/
theorem MurrayVonNeumannEquiv.reindexₐ [Fintype m] [Fintype m'] [Fintype n] [Fintype n']
    [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) (eₘ : m ≃ m') (eₙ : n ≃ n') :
    MurrayVonNeumannEquiv (reindexₐ R A eₘ p) (reindexₐ R A eₙ q) := by
  rcases h with ⟨v, hvp, hvq⟩
  refine ⟨reindexₗ R A eₙ eₘ v, ?_, ?_⟩
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hvp, reindexₐ_eq_reindexₗ]
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hvq, reindexₐ_eq_reindexₗ]

/-- Every star projection `p` is Murray–von Neumann equivalent to any reindexing `reindexₐ R A e p`
without requiring `A` to be unital. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_reindexₐ [Fintype m] [Fintype n]
    [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) (e : m ≃ n) :
    MurrayVonNeumannEquiv p (reindexₐ R A e p) := by
  simpa using hp.murrayVonNeumannEquiv_refl.reindexₐ (R := R) (Equiv.refl m) e

/-- Padding a star projection `p` with a lower-right zero block yields a Murray–von Neumann
equivalent projection without requiring `A` to be unital. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_fromBlocks_zero_right [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p (fromBlocks p 0 0 (0 : CStarMatrix n n A)) := by
  let v : CStarMatrix (m ⊕ n) m A := ofMatrix (Sum.elim (ofMatrix.symm p) 0)
  have hv_inr (x : n) (j : m) : v (Sum.inr x) j = 0 := rfl
  have hpp : p.conjTranspose * p = p := by
    rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  have hpp' : p * p.conjTranspose = p := by
    rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  refine ⟨v, ?_, ?_⟩
  · ext j₁ j₂
    rw [mul_apply, Fintype.sum_sum_type]
    have h₁ : (∑ x : m, (v.conjTranspose) j₁ (Sum.inl x) * v (Sum.inl x) j₂) =
        (p.conjTranspose * p) j₁ j₂ := rfl
    have h₂ : (∑ x : n, (v.conjTranspose) j₁ (Sum.inr x) * v (Sum.inr x) j₂) = 0 := by
      simp [hv_inr]
    rw [h₁, h₂, add_zero, hpp]
  · ext (i₁ | i₁) (i₂ | i₂)
    · rw [fromBlocks_apply₁₁]
      exact congrArg (fun M => M i₁ i₂) hpp'
    · simp [mul_apply, hv_inr]
    · simp [mul_apply, hv_inr]
    · simp [mul_apply, hv_inr]

/-- Padding a star projection `p` with an upper-left zero block yields a Murray–von Neumann
equivalent projection without requiring `A` to be unital. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_fromBlocks_zero_left [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p (fromBlocks (0 : CStarMatrix m m A) 0 0 p) := by
  have h₁ := hp.murrayVonNeumannEquiv_fromBlocks_zero_right (n := m)
  rcases h₁ with ⟨v, hvp, hvq⟩
  refine ⟨reindexₗ ℕ A (Equiv.sumComm n m) (Equiv.refl n) v, ?_, ?_⟩
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hvp]
    rfl
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hvq, ← reindexₐ_eq_reindexₗ,
      reindexₐ_sumComm_fromBlocks]

/-- Entrywise application of any `⋆`-ring homomorphism preserves `MurrayVonNeumannEquiv`. -/
theorem MurrayVonNeumannEquiv.map {F : Type*} [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] [StarHomClass F A B]
    (f : F) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    MurrayVonNeumannEquiv (p.map f) (q.map f) := by
  rcases h with ⟨v, rfl, rfl⟩
  exact ⟨v.map f, by rw [map_conjTranspose, CStarMatrix.map_mul],
    by rw [map_conjTranspose, CStarMatrix.map_mul]⟩

theorem MurrayVonNeumannEquiv.mapStarAlgHom [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [StarRing A] [Algebra R A]
    [Semiring B] [StarRing B] [Algebra R B]
    (f : A →⋆ₐ[R] B) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    MurrayVonNeumannEquiv (mapStarAlgHom f p) (mapStarAlgHom f q) := by
  rw [mapStarAlgHom_apply, mapStarAlgHom_apply]
  exact h.map f

/-- Unitary conjugates of a star projection in `CStarMatrix n n A` are Murray–von Neumann
equivalent. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_unitary_conj [Fintype n] [DecidableEq n]
    [Ring A] [StarRing A] {p : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A)) :
    MurrayVonNeumannEquiv p
      ((u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A)) := by
  refine ⟨(u : CStarMatrix n n A) * p, ?_, ?_⟩
  · calc
      ((u : CStarMatrix n n A) * p).conjTranspose * ((u : CStarMatrix n n A) * p)
        = star p * (star (u : CStarMatrix n n A) * (u : CStarMatrix n n A)) * p := by
          simp only [← star_eq_conjTranspose, star_mul, mul_assoc]
      _ = p := by
          rw [Unitary.star_mul_self_of_mem u.prop, mul_one, hp.isSelfAdjoint.star_eq,
            hp.isIdempotentElem.eq]
  · calc
      ((u : CStarMatrix n n A) * p) * ((u : CStarMatrix n n A) * p).conjTranspose
        = (u : CStarMatrix n n A) * (p * star p) * star (u : CStarMatrix n n A) := by
          simp only [← star_eq_conjTranspose, star_mul, mul_assoc]
      _ = (u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A) := by
          rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

end MurrayVonNeumannEquiv

section StabilizedRotation

variable {m n A : Type*}

section Unital

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The self-adjoint unitary `fromBlocks (1 - p) vᴴ v (1 - q)` in
`CStarMatrix (m ⊕ n) (m ⊕ n) A` swapping `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` for a
rectangular partial-isometry equivalence `vᴴ * v = p`, `v * vᴴ = q`. -/
noncomputable def stabilizedSwapUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hq : IsStarProjection q :=
    hvq ▸ isStarProjection_conjTranspose_mul_self_iff.mp (hvp.symm ▸ hp)
  have hvp_abs : v * p = v := by
    rw [← hvp, ← CStarMatrix.mul_assoc]
    exact mul_conjTranspose_mul_self_of_isIdempotentElem (hvp.symm ▸ hp.isIdempotentElem)
  have hpv_abs : p * v.conjTranspose = v.conjTranspose := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, ← star_eq_conjTranspose,
      hp.isSelfAdjoint.star_eq] using congrArg conjTranspose hvp_abs
  have hsa : IsSelfAdjoint (fromBlocks (1 - p) v.conjTranspose v (1 - q)) :=
    isSelfAdjoint_fromBlocks.mpr
      ⟨(IsSelfAdjoint.one _).sub hp.isSelfAdjoint, conjTranspose_conjTranspose v,
        (IsSelfAdjoint.one _).sub hq.isSelfAdjoint⟩
  have hmul (X Y : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
      ofMatrix.symm (X * Y) = ofMatrix.symm X * ofMatrix.symm Y := rfl
  have hsq :
      fromBlocks (1 - p) v.conjTranspose v (1 - q) *
        fromBlocks (1 - p) v.conjTranspose v (1 - q) = 1 := by
    apply ofMatrix.symm.injective
    rw [hmul, ofMatrix_symm_fromBlocks]
    exact Matrix.fromBlocks_one_sub_mul_self_of_mul_eq
      (congrArg ofMatrix.symm hvp) (congrArg ofMatrix.symm hvq)
      (congrArg ofMatrix.symm hpv_abs) (congrArg ofMatrix.symm hvp_abs)
  exact ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    rw [Unitary.mem_iff, hsa.star_eq]
    exact ⟨hsq, hsq⟩⟩

@[simp]
theorem coe_stabilizedSwapUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    (stabilizedSwapUnitary hp hvp hvq : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 - p) v.conjTranspose v (1 - q) :=
  (rfl)

theorem isSelfAdjoint_stabilizedSwapUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    IsSelfAdjoint (stabilizedSwapUnitary hp hvp hvq : CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hq : IsStarProjection q :=
    hvq ▸ isStarProjection_conjTranspose_mul_self_iff.mp (hvp.symm ▸ hp)
  exact isSelfAdjoint_fromBlocks.mpr
    ⟨(IsSelfAdjoint.one _).sub hp.isSelfAdjoint, conjTranspose_conjTranspose v,
      (IsSelfAdjoint.one _).sub hq.isSelfAdjoint⟩

/-- Conjugating `fromBlocks p 0 0 0` by `stabilizedSwapUnitary` yields `fromBlocks 0 0 0 q`. -/
theorem stabilizedSwapUnitary_conj [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    (stabilizedSwapUnitary hp hvp hvq : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        fromBlocks p 0 0 (0 : CStarMatrix n n A) *
        star (stabilizedSwapUnitary hp hvp hvq : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (0 : CStarMatrix m m A) 0 0 q := by
  have hvp_abs : v * p = v := by
    rw [← hvp, ← CStarMatrix.mul_assoc]
    exact mul_conjTranspose_mul_self_of_isIdempotentElem (hvp.symm ▸ hp.isIdempotentElem)
  have hmul (X Y : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
      ofMatrix.symm (X * Y) = ofMatrix.symm X * ofMatrix.symm Y := rfl
  rw [(isSelfAdjoint_stabilizedSwapUnitary hp hvp hvq).star_eq, coe_stabilizedSwapUnitary]
  apply ofMatrix.symm.injective
  rw [hmul, hmul, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks]
  exact Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
    (congrArg ofMatrix.symm hvp) (congrArg ofMatrix.symm hvq) (congrArg ofMatrix.symm hvp_abs)

/-- Explicit exponential rotation path from `1` to `stabilizedSwapUnitary hp hvp hvq` in
`unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`. -/
noncomputable def stabilizedSwapUnitaryPath [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    Path (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) (stabilizedSwapUnitary hp hvp hvq) :=
  Unitary.selfAdjointRotationPath (isSelfAdjoint_stabilizedSwapUnitary hp hvp hvq)

theorem stabilizedSwapUnitaryPath_eq [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    stabilizedSwapUnitaryPath hp hvp hvq =
      Unitary.selfAdjointRotationPath (isSelfAdjoint_stabilizedSwapUnitary hp hvp hvq) :=
  (rfl)

/-- The stabilized unitary in `CStarMatrix (n ⊕ n) (n ⊕ n) A` conjugating `fromBlocks p 0 0 0` to
`fromBlocks q 0 0 0`, obtained by composing `stabilizedSwapUnitary` with the block-swap permutation
unitary `permUnitary A (Equiv.sumComm n n)`. -/
noncomputable def stabilizedConjUnitary [Fintype n] [DecidableEq n]
    {p q v : CStarMatrix n n A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A) :=
  permUnitary A (Equiv.sumComm n n) * stabilizedSwapUnitary hp hvp hvq

theorem stabilizedConjUnitary_eq [Fintype n] [DecidableEq n]
    {p q v : CStarMatrix n n A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    stabilizedConjUnitary hp hvp hvq =
      permUnitary A (Equiv.sumComm n n) * stabilizedSwapUnitary hp hvp hvq :=
  (rfl)

/-- Conjugating `fromBlocks p 0 0 0` by `stabilizedConjUnitary` yields `fromBlocks q 0 0 0`. -/
theorem stabilizedConjUnitary_conj [Fintype n] [DecidableEq n]
    {p q v : CStarMatrix n n A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    (stabilizedConjUnitary hp hvp hvq : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
        fromBlocks p 0 0 (0 : CStarMatrix n n A) *
        star (stabilizedConjUnitary hp hvp hvq : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks q 0 0 (0 : CStarMatrix n n A) := by
  let s := permUnitary A (Equiv.sumComm n n)
  let w := stabilizedSwapUnitary hp hvp hvq
  calc
    ((s * w : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
        fromBlocks p 0 0 0 *
        star ((s * w : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) : CStarMatrix (n ⊕ n) (n ⊕ n) A)
      = (s : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
          ((w : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks p 0 0 0 *
            star (w : CStarMatrix (n ⊕ n) (n ⊕ n) A)) *
          star (s : CStarMatrix (n ⊕ n) (n ⊕ n) A) := by
        simp only [Submonoid.coe_mul, star_mul, mul_assoc]
    _ = (s : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks 0 0 0 q *
          star (s : CStarMatrix (n ⊕ n) (n ⊕ n) A) := by
        rw [stabilizedSwapUnitary_conj hp hvp hvq]
    _ = fromBlocks q 0 0 0 := by
        rw [permUnitary_conj_eq_reindexₐ (R := ℂ) (Equiv.sumComm n n),
          reindexₐ_sumComm_fromBlocks]

/-- Explicit rotation path from `1` to `stabilizedConjUnitary hp hvp hvq` in
`unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`, formed by multiplying the exponential rotation paths of
its two self-adjoint unitary factors. -/
noncomputable def stabilizedConjUnitaryPath [Fintype n] [DecidableEq n]
    {p q v : CStarMatrix n n A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    Path (1 : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) (stabilizedConjUnitary hp hvp hvq) := by
  let hs : IsSelfAdjoint
      (permUnitary A (Equiv.sumComm n n) : CStarMatrix (n ⊕ n) (n ⊕ n) A) :=
    isSelfAdjoint_permUnitary_of_involutive fun x => by cases x <;> rfl
  let γ₁ := Unitary.selfAdjointRotationPath hs
  let γ₂ := stabilizedSwapUnitaryPath hp hvp hvq
  exact
    { toFun := fun t => γ₁ t * γ₂ t
      continuous_toFun := γ₁.continuous.mul γ₂.continuous
      source' := by simp [γ₁, γ₂]
      target' := by simp [γ₁, γ₂, stabilizedConjUnitary] }

theorem stabilizedConjUnitaryPath_apply [Fintype n] [DecidableEq n]
    {p q v : CStarMatrix n n A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (t : I) :
    stabilizedConjUnitaryPath hp hvp hvq t =
      Unitary.selfAdjointRotationPath
          (isSelfAdjoint_permUnitary_of_involutive (A := A) (e := Equiv.sumComm n n)
            fun x => by cases x <;> rfl) t *
        stabilizedSwapUnitaryPath hp hvp hvq t :=
  (rfl)

/-- Over a unital C⋆-algebra, Murray–von Neumann equivalent projections `p ∈ Mₘ(A)` and `q ∈ Mₙ(A)`
become conjugate in `M_{m ⊕ n}(A)` by a unitary in the identity path component. -/
theorem MurrayVonNeumannEquiv.exists_unitary_conj_fromBlocks_zero_swap
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (h : MurrayVonNeumannEquiv p q) :
    ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      Joined 1 u ∧
      (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromBlocks p 0 0 (0 : CStarMatrix n n A) *
        star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
        fromBlocks (0 : CStarMatrix m m A) 0 0 q := by
  rcases h with ⟨v, hvp, hvq⟩
  exact ⟨stabilizedSwapUnitary hp hvp hvq, ⟨stabilizedSwapUnitaryPath hp hvp hvq⟩,
    stabilizedSwapUnitary_conj hp hvp hvq⟩

/-- Over a unital C⋆-algebra, Murray–von Neumann equivalent projections `p, q ∈ Mₙ(A)` become
conjugate as `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0` in `M_{n ⊕ n}(A)` by a unitary in the
identity path component. -/
theorem MurrayVonNeumannEquiv.exists_unitary_conj_fromBlocks_zero [Fintype n] [DecidableEq n]
    {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (h : MurrayVonNeumannEquiv p q) :
    ∃ u : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A),
      Joined 1 u ∧
      (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks p 0 0 (0 : CStarMatrix n n A) *
        star (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
        fromBlocks q 0 0 (0 : CStarMatrix n n A) := by
  rcases h with ⟨v, hvp, hvq⟩
  exact ⟨stabilizedConjUnitary hp hvp hvq, ⟨stabilizedConjUnitaryPath hp hvp hvq⟩,
    stabilizedConjUnitary_conj hp hvp hvq⟩

end Unital

section NonUnital

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Descend a unitary path in `CStarMatrix k k (Unitization ℂ A)` conjugating `mapₙₐ inr P₀` to
`mapₙₐ inr P₁` to a continuous path in `{P : CStarMatrix k k A // IsStarProjection P}`. -/
private noncomputable def unitizationConjProjectionPath {k : Type*} [Fintype k] [DecidableEq k]
    {P₀ P₁ : CStarMatrix k k A} (hP₀ : IsStarProjection P₀) (hP₁ : IsStarProjection P₁)
    (u : unitary (CStarMatrix k k (Unitization ℂ A)))
    (γ : @Path (unitary (CStarMatrix k k (Unitization ℂ A)))
      (by
        letI : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder (Unitization ℂ A)
        letI : StarOrderedRing (Unitization ℂ A) :=
          CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
        infer_instance)
      1 u)
    (hu : (u : CStarMatrix k k (Unitization ℂ A)) *
        mapₙₐ (Unitization.inrNonUnitalStarAlgHom ℂ A) P₀ *
        star (u : CStarMatrix k k (Unitization ℂ A)) =
      mapₙₐ (Unitization.inrNonUnitalStarAlgHom ℂ A) P₁) :
    Path (⟨P₀, hP₀⟩ : {P : CStarMatrix k k A // IsStarProjection P}) ⟨P₁, hP₁⟩ := by
  letI : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder (Unitization ℂ A)
  letI : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  let inr : A →⋆ₙₐ[ℂ] Unitization ℂ A := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hinj : Function.Injective (mapₙₐ (n := k) inr) :=
    map_injective (Unitization.inr_injective (R := ℂ))
  let Q' : I → CStarMatrix k k (Unitization ℂ A) := fun t =>
    (γ t : CStarMatrix k k (Unitization ℂ A)) * mapₙₐ inr P₀ *
      star (γ t : CStarMatrix k k (Unitization ℂ A))
  let Q : I → CStarMatrix k k A := fun t => (Q' t).map (fun x => x.snd)
  have hP₀_fst : (mapₙₐ inr P₀).map (Unitization.fstHom (R := ℂ) (A := A)) = 0 :=
    CStarMatrix.ext fun i j => Unitization.fst_inr ℂ (P₀ i j)
  have hQ'_lift (t : I) : mapₙₐ inr (Q t) = Q' t := by
    have hfst : (Q' t).map (Unitization.fstHom (R := ℂ) (A := A)) = 0 := by
      simp only [Q', CStarMatrix.map_mul, hP₀_fst, CStarMatrix.mul_zero, CStarMatrix.zero_mul]
    refine CStarMatrix.ext fun i j => ?_
    have hij : (Q' t i j).fst = 0 := congrArg (fun M => M i j) hfst
    exact Unitization.ext (by simp [inr, Q, hij]) (by simp [inr, Q])
  have hQ_proj (t : I) : IsStarProjection (Q t) := by
    have hQ'_proj : IsStarProjection (Q' t) :=
      (hP₀.map (mapₙₐ inr)).map (Unitary.conjStarAlgAut ℕ (CStarMatrix k k (Unitization ℂ A)) (γ t))
    refine ⟨show Q t * Q t = Q t from hinj ?_, isSelfAdjoint_iff.mpr (hinj ?_)⟩
    · rw [map_mul, hQ'_lift, hQ'_proj.isIdempotentElem.eq]
    · rw [map_star, hQ'_lift, hQ'_proj.isSelfAdjoint.star_eq]
  have hcontU : Continuous fun t : I => (γ t : CStarMatrix k k (Unitization ℂ A)) :=
    continuous_subtype_val.comp γ.continuous
  have hcontQ' : Continuous Q' :=
    (hcontU.mul continuous_const).mul (continuous_star.comp hcontU)
  have hcontQ : Continuous Q :=
    continuous_map Unitization.continuous_snd hcontQ'
  refine
    { toFun := fun t => ⟨Q t, hQ_proj t⟩
      continuous_toFun := hcontQ.subtype_mk hQ_proj
      source' := Subtype.ext <| hinj <| by
        rw [hQ'_lift]
        simp [Q']
      target' := Subtype.ext <| hinj <| by
        rw [hQ'_lift]
        simpa [Q'] using hu }

/-- Explicit continuous path in `{P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P}` from
`fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` for any non-unital C⋆-algebra `A` and rectangular
partial-isometry witness `vᴴ * v = p`, `v * vᴴ = q`. -/
noncomputable def stabilizedSwapProjectionPath [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    Path
      (⟨fromBlocks p 0 0 (0 : CStarMatrix n n A),
        isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, .zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨fromBlocks (0 : CStarMatrix m m A) 0 0 q,
        isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr
          ⟨.zero _, hvq ▸ isStarProjection_conjTranspose_mul_self_iff.mp (hvp.symm ▸ hp)⟩⟩ := by
  classical
  letI : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder (Unitization ℂ A)
  letI : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  let inr : A →⋆ₙₐ[ℂ] Unitization ℂ A := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hp' : IsStarProjection (mapₙₐ inr p) := hp.map (mapₙₐ inr)
  have hv'p : (v.map inr).conjTranspose * v.map inr = mapₙₐ inr p := by
    rw [map_conjTranspose, ← CStarMatrix.map_mul, hvp, mapₙₐ_apply, mapₗ_apply]
    rfl
  have hv'q : v.map inr * (v.map inr).conjTranspose = mapₙₐ inr q := by
    rw [map_conjTranspose, ← CStarMatrix.map_mul, hvq, mapₙₐ_apply, mapₗ_apply]
    rfl
  refine unitizationConjProjectionPath
    (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, .zero _⟩)
    (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr
      ⟨.zero _, hvq ▸ isStarProjection_conjTranspose_mul_self_iff.mp (hvp.symm ▸ hp)⟩)
    (stabilizedSwapUnitary hp' hv'p hv'q)
    (stabilizedSwapUnitaryPath hp' hv'p hv'q) ?_
  simpa only [mapₙₐ_apply, mapₗ_apply, fromBlocks_map, CStarMatrix.map_zero] using
    stabilizedSwapUnitary_conj hp' hv'p hv'q

/-- Explicit continuous path in `{P : CStarMatrix (n ⊕ n) (n ⊕ n) A // IsStarProjection P}` from
`fromBlocks p 0 0 0` to `fromBlocks q 0 0 0` for any non-unital C⋆-algebra `A` and equivalence
witness `vᴴ * v = p`, `v * vᴴ = q`. -/
noncomputable def stabilizedProjectionPath [Fintype n]
    {p q v : CStarMatrix n n A}
    (hp : IsStarProjection p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    Path
      (⟨fromBlocks p 0 0 (0 : CStarMatrix n n A),
        isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, .zero _⟩⟩ :
        {P : CStarMatrix (n ⊕ n) (n ⊕ n) A // IsStarProjection P})
      ⟨fromBlocks q 0 0 (0 : CStarMatrix n n A),
        isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr
          ⟨hvq ▸ isStarProjection_conjTranspose_mul_self_iff.mp (hvp.symm ▸ hp), .zero _⟩⟩ := by
  classical
  letI : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder (Unitization ℂ A)
  letI : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  let inr : A →⋆ₙₐ[ℂ] Unitization ℂ A := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hp' : IsStarProjection (mapₙₐ inr p) := hp.map (mapₙₐ inr)
  have hv'p : (v.map inr).conjTranspose * v.map inr = mapₙₐ inr p := by
    rw [map_conjTranspose, ← CStarMatrix.map_mul, hvp, mapₙₐ_apply, mapₗ_apply]
    rfl
  have hv'q : v.map inr * (v.map inr).conjTranspose = mapₙₐ inr q := by
    rw [map_conjTranspose, ← CStarMatrix.map_mul, hvq, mapₙₐ_apply, mapₗ_apply]
    rfl
  refine unitizationConjProjectionPath
    (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, .zero _⟩)
    (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr
      ⟨hvq ▸ isStarProjection_conjTranspose_mul_self_iff.mp (hvp.symm ▸ hp), .zero _⟩)
    (stabilizedConjUnitary hp' hv'p hv'q)
    (stabilizedConjUnitaryPath hp' hv'p hv'q) ?_
  simpa only [mapₙₐ_apply, mapₗ_apply, fromBlocks_map, CStarMatrix.map_zero] using
    stabilizedConjUnitary_conj hp' hv'p hv'q

/-- Over any (not necessarily unital) C⋆-algebra `A`, Murray–von Neumann equivalent projections
`p ∈ Mₘ(A)` and `q ∈ Mₙ(A)` become path-connected as `fromBlocks p 0 0 0` and
`fromBlocks 0 0 0 q` inside `{P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P}`. -/
theorem MurrayVonNeumannEquiv.joined_fromBlocks_zero_swap [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (h : MurrayVonNeumannEquiv p q) :
    Joined
      (⟨fromBlocks p 0 0 (0 : CStarMatrix n n A),
        isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, .zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨fromBlocks (0 : CStarMatrix m m A) 0 0 q,
        isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr
          ⟨.zero _, h.isStarProjection_iff.mp hp⟩⟩ := by
  rcases h with ⟨v, hvp, hvq⟩
  exact ⟨stabilizedSwapProjectionPath hp hvp hvq⟩

/-- Over any (not necessarily unital) C⋆-algebra `A`, Murray–von Neumann equivalent projections
`p, q ∈ Mₙ(A)` become path-connected as `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0` inside
`{P : CStarMatrix (n ⊕ n) (n ⊕ n) A // IsStarProjection P}`. -/
theorem MurrayVonNeumannEquiv.joined_fromBlocks_zero [Fintype n]
    {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (h : MurrayVonNeumannEquiv p q) :
    Joined
      (⟨fromBlocks p 0 0 (0 : CStarMatrix n n A),
        isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, .zero _⟩⟩ :
        {P : CStarMatrix (n ⊕ n) (n ⊕ n) A // IsStarProjection P})
      ⟨fromBlocks q 0 0 (0 : CStarMatrix n n A),
        isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr
          ⟨h.isStarProjection_iff.mp hp, .zero _⟩⟩ := by
  rcases h with ⟨v, hvp, hvq⟩
  exact ⟨stabilizedProjectionPath hp hvp hvq⟩

end NonUnital

end StabilizedRotation

end CStarMatrix

end
