/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.Algebra.CharP.Invertible
import TauCeti.Algebra.DirectSum.Component
import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
import TauCeti.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Parity decomposition of the signed symmetric algebra

For an internally `ZMod 2`-graded `R`-module `V` with grading `G`, splitting `V` into `G.piece 0`
and `G.piece 1` compares `TauCeti.ParitySignedSym G` with
`SymmetricAlgebra R (G.piece 0) ⊗[R] ExteriorAlgebra R (G.piece 1)`. Since the symmetric factor is
purely even, the Koszul sign between the factors is `+1`, so their super tensor product is
Mathlib's ordinary `Algebra.TensorProduct`.

We prove this algebra-level comparison first for `TauCeti.ParitySignedSym` without an integer lift,
then specialize to `G : InternalGrading R V ℤ` via `TauCeti.SignedSym.parityEquiv G` along with
naturality for `TauCeti.SignedSym.map`. Over any commutative ring `R`, `fromSymmetricEven` is
central and injective and `toSymTensorExterior` is surjective; when `Invertible (2 : R)` holds,
`symTensorExteriorEquiv` is an `R`-algebra equivalence and yields `instModuleFree`.

For word-length and parity-grading compatibility on `SignedSym`, see
`TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Decomposition.Grading`; for the purely even
and purely odd cases, see `TauCeti.LinearAlgebra.SignedSymmetricAlgebra.SymmetricExterior`. This
realizes J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1).

## Main definitions and results

* `TauCeti.ParitySignedSym.fromSymmetricEven`, `toSymmetricEven`, `toExteriorOdd`,
  `fromExteriorOdd`, `toSymTensorExterior`, `fromSymTensorExterior`, `symTensorExteriorEquiv`,
  `instModuleFree`: algebra-level parity decomposition and module freeness for `ParitySignedSym`.
* `TauCeti.SignedSym.fromSymmetricEven`, `toSymmetricEven`, `toExteriorOdd`, `fromExteriorOdd`,
  `toSymTensorExterior`, `fromSymTensorExterior`, `symTensorExteriorEquiv`, `instModuleFree`,
  `toSymTensorExterior_comp_map`, `map_comp_fromSymTensorExterior`: specialization to `SignedSym`
  via `SignedSym.parityEquiv G` and functoriality along degree-preserving maps.
-/

public section

open DirectSum
open scoped TensorProduct

namespace TauCeti

universe u v w

/-! ### Parity-graded decomposition (`ParitySignedSym`) -/

namespace ParitySignedSym

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V (ZMod 2))

private theorem commute_generator_of_mem_piece_zero {x : V} (hx : x ∈ G.piece 0) (y : V) :
    Commute (generator G x) (generator G y) := by
  have hmul (j : ZMod 2) {z : V} (hz : z ∈ G.piece j) :
      generator G x * generator G z = generator G z * generator G x := by
    simpa using generator_mul_generator G hx hz
  rw [← coe_decompose_zero_add_coe_decompose_one G.piece y, map_add, Commute, SemiconjBy,
    mul_add, add_mul, hmul 0 (DirectSum.decompose G.piece y 0).2,
    hmul 1 (DirectSum.decompose G.piece y 1).2]

private theorem generator_mem_center_of_mem_piece_zero {x : V} (hx : x ∈ G.piece 0) :
    generator G x ∈ Subalgebra.center R (ParitySignedSym G) := by
  refine Subalgebra.mem_center_iff.2 fun a => ?_
  induction a using ParitySignedSym.induction with
  | algebraMap r => exact Algebra.commutes r _
  | generator y => exact (commute_generator_of_mem_piece_zero G hx y).symm
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

/-! #### Even and odd factor inclusions and projections -/

/-- Canonical algebra map `Sym(V_even) → ParitySignedSym G` over any commutative ring. -/
noncomputable def fromSymmetricEven : SymmetricAlgebra R (G.piece 0) →ₐ[R] ParitySignedSym G :=
  SymmetricAlgebra.liftOfCommute ⟨(generator G).comp (G.piece 0).subtype, fun x y =>
    commute_generator_of_mem_piece_zero G x.2 y.1⟩

@[simp]
theorem fromSymmetricEven_ι (x : G.piece 0) :
    fromSymmetricEven G (SymmetricAlgebra.ι R (G.piece 0) x) = generator G x :=
  SymmetricAlgebra.liftOfCommute_ι_apply _ _ x

/-- Every element in the image of `fromSymmetricEven` lies in the center of `ParitySignedSym G`. -/
theorem fromSymmetricEven_mem_center (s : SymmetricAlgebra R (G.piece 0)) :
    fromSymmetricEven G s ∈ Subalgebra.center R (ParitySignedSym G) := by
  induction s using SymmetricAlgebra.induction with
  | algebraMap r => simpa only [AlgHom.commutes] using Subalgebra.algebraMap_mem _ r
  | ι x => simpa only [fromSymmetricEven_ι] using generator_mem_center_of_mem_piece_zero G x.2
  | mul a b ha hb => rw [map_mul]; exact mul_mem ha hb
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- Every element in the image of `fromSymmetricEven` commutes with all of `ParitySignedSym G`. -/
theorem commute_fromSymmetricEven (s : SymmetricAlgebra R (G.piece 0)) (a : ParitySignedSym G) :
    Commute (fromSymmetricEven G s) a :=
  (Subalgebra.mem_center_iff.1 (fromSymmetricEven_mem_center G s) a).symm

/-- Algebra projection `ParitySignedSym G → Sym(V_even)` sending odd generators to zero. -/
noncomputable def toSymmetricEven : ParitySignedSym G →ₐ[R] SymmetricAlgebra R (G.piece 0) :=
  lift G ((SymmetricAlgebra.ι R (G.piece 0)).comp (homogeneousProj G.piece 0)) <| by
    intro i j x y hx _
    simp only [LinearMap.comp_apply, homogeneousProj_apply]
    by_cases hi : i = 0
    · simp [hi, mul_comm]
    · simp [decompose_apply_of_mem_ne G.piece hx hi]

@[simp]
theorem toSymmetricEven_generator (x : V) :
    toSymmetricEven G (generator G x) =
      SymmetricAlgebra.ι R (G.piece 0) (DirectSum.decompose G.piece x 0) := by
  simp [toSymmetricEven]

/-- On an even-parity generator, `toSymmetricEven` is the canonical symmetric generator. -/
theorem toSymmetricEven_generator_of_mem_piece_zero {x : V} (hx : x ∈ G.piece 0) :
    toSymmetricEven G (generator G x) = SymmetricAlgebra.ι R (G.piece 0) ⟨x, hx⟩ := by
  rw [toSymmetricEven_generator, decompose_apply_of_mem_same G.piece hx]

/-- `toSymmetricEven` annihilates odd-parity generators. -/
theorem toSymmetricEven_generator_of_mem_piece_one {x : V} (hx : x ∈ G.piece 1) :
    toSymmetricEven G (generator G x) = 0 := by
  rw [toSymmetricEven_generator, decompose_apply_of_mem_ne G.piece hx (by decide), map_zero]

@[simp]
theorem toSymmetricEven_comp_fromSymmetricEven :
    (toSymmetricEven G).comp (fromSymmetricEven G) =
      AlgHom.id R (SymmetricAlgebra R (G.piece 0)) := by
  ext x; simp [toSymmetricEven_generator_of_mem_piece_zero G x.2]

@[simp]
theorem toSymmetricEven_fromSymmetricEven (s : SymmetricAlgebra R (G.piece 0)) :
    toSymmetricEven G (fromSymmetricEven G s) = s :=
  AlgHom.congr_fun (toSymmetricEven_comp_fromSymmetricEven G) s

/-- Over any commutative ring, `fromSymmetricEven G` is injective. -/
theorem fromSymmetricEven_injective : Function.Injective (fromSymmetricEven G) :=
  Function.LeftInverse.injective (toSymmetricEven_fromSymmetricEven G)

/-- Over any commutative ring, `toSymmetricEven G` is surjective. -/
theorem toSymmetricEven_surjective : Function.Surjective (toSymmetricEven G) :=
  Function.RightInverse.surjective (toSymmetricEven_fromSymmetricEven G)

/-- Algebra projection `ParitySignedSym G → Λ(V_odd)` sending even generators to zero. -/
noncomputable def toExteriorOdd : ParitySignedSym G →ₐ[R] ExteriorAlgebra R (G.piece 1) :=
  lift G ((ExteriorAlgebra.ι R (M := G.piece 1)).comp (homogeneousProj G.piece 1)) <| by
    intro i j x y hx hy
    simp only [LinearMap.comp_apply, homogeneousProj_apply]
    by_cases hi : i = 1
    · by_cases hj : j = 1
      · simp only [hi, hj, mul_one, uzpow_one, Units.neg_smul, one_smul]
        exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
      · simp [decompose_apply_of_mem_ne G.piece hy hj]
    · simp [decompose_apply_of_mem_ne G.piece hx hi]

@[simp]
theorem toExteriorOdd_generator (x : V) :
    toExteriorOdd G (generator G x) = ExteriorAlgebra.ι R (DirectSum.decompose G.piece x 1) := by
  simp [toExteriorOdd]

/-- `toExteriorOdd` annihilates even-parity generators. -/
theorem toExteriorOdd_generator_of_mem_piece_zero {x : V} (hx : x ∈ G.piece 0) :
    toExteriorOdd G (generator G x) = 0 := by
  rw [toExteriorOdd_generator, decompose_apply_of_mem_ne G.piece hx (by decide), map_zero]

/-- On an odd-parity generator, `toExteriorOdd` is the canonical exterior generator. -/
theorem toExteriorOdd_generator_of_mem_piece_one {x : V} (hx : x ∈ G.piece 1) :
    toExteriorOdd G (generator G x) = ExteriorAlgebra.ι R ⟨x, hx⟩ := by
  rw [toExteriorOdd_generator, decompose_apply_of_mem_same G.piece hx]

@[simp]
theorem toExteriorOdd_comp_fromSymmetricEven :
    (toExteriorOdd G).comp (fromSymmetricEven G) =
      (Algebra.ofId R (ExteriorAlgebra R (G.piece 1))).comp SymmetricAlgebra.algebraMapInv := by
  ext x; simp [toExteriorOdd_generator_of_mem_piece_zero G x.2, SymmetricAlgebra.algebraMapInv_ι]

@[simp]
theorem toExteriorOdd_fromSymmetricEven (s : SymmetricAlgebra R (G.piece 0)) :
    toExteriorOdd G (fromSymmetricEven G s) =
      algebraMap R (ExteriorAlgebra R (G.piece 1)) (SymmetricAlgebra.algebraMapInv s) :=
  AlgHom.congr_fun (toExteriorOdd_comp_fromSymmetricEven G) s

/-- Over any commutative ring, `toExteriorOdd G` is surjective. -/
theorem toExteriorOdd_surjective : Function.Surjective (toExteriorOdd G) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← CliffordAlgebra.adjoin_range_ι, Algebra.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  exact ⟨generator G x.1, toExteriorOdd_generator_of_mem_piece_one G x.2⟩

/-- When `2` is invertible, canonical algebra map `Λ(V_odd) → ParitySignedSym G`. -/
def fromExteriorOdd [Invertible (2 : R)] : ExteriorAlgebra R (G.piece 1) →ₐ[R] ParitySignedSym G :=
  ExteriorAlgebra.lift R ⟨(generator G).comp (G.piece 1).subtype, fun x =>
    eq_zero_of_eq_neg_of_invertible_two (R := R) (by simpa using generator_mul_generator G x.2 x.2)⟩

@[simp]
theorem fromExteriorOdd_ι [Invertible (2 : R)] (x : G.piece 1) :
    fromExteriorOdd G (ExteriorAlgebra.ι R x) = generator G x :=
  ExteriorAlgebra.lift_ι_apply _ _ _ x

@[simp]
theorem toExteriorOdd_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toExteriorOdd G).comp (fromExteriorOdd G) = AlgHom.id R (ExteriorAlgebra R (G.piece 1)) := by
  ext x; simp [toExteriorOdd_generator_of_mem_piece_one G x.2]

@[simp]
theorem toExteriorOdd_fromExteriorOdd [Invertible (2 : R)] (e : ExteriorAlgebra R (G.piece 1)) :
    toExteriorOdd G (fromExteriorOdd G e) = e :=
  AlgHom.congr_fun (toExteriorOdd_comp_fromExteriorOdd G) e

@[simp]
theorem toSymmetricEven_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toSymmetricEven G).comp (fromExteriorOdd G) =
      (Algebra.ofId R (SymmetricAlgebra R (G.piece 0))).comp ExteriorAlgebra.algebraMapInv := by
  ext x; simp [toSymmetricEven_generator_of_mem_piece_one G x.2, ExteriorAlgebra.algebraMapInv]

@[simp]
theorem toSymmetricEven_fromExteriorOdd [Invertible (2 : R)] (e : ExteriorAlgebra R (G.piece 1)) :
    toSymmetricEven G (fromExteriorOdd G e) =
      algebraMap R (SymmetricAlgebra R (G.piece 0)) (ExteriorAlgebra.algebraMapInv e) :=
  AlgHom.congr_fun (toSymmetricEven_comp_fromExteriorOdd G) e

/-- When `2` is invertible, `fromExteriorOdd G` is injective. -/
theorem fromExteriorOdd_injective [Invertible (2 : R)] : Function.Injective (fromExteriorOdd G) :=
  Function.LeftInverse.injective (toExteriorOdd_fromExteriorOdd G)

/-! #### Tensor product comparison and algebra equivalence -/

private noncomputable def symTensorExteriorGenerator :
    V →ₗ[R] SymmetricAlgebra R (G.piece 0) ⊗[R] ExteriorAlgebra R (G.piece 1) :=
  Algebra.TensorProduct.includeLeft.toLinearMap.comp
      ((SymmetricAlgebra.ι R (G.piece 0)).comp (homogeneousProj G.piece 0)) +
    Algebra.TensorProduct.includeRight.toLinearMap.comp
      ((ExteriorAlgebra.ι R (M := G.piece 1)).comp (homogeneousProj G.piece 1))

private theorem symTensorExteriorGenerator_of_mem_piece_zero {x : V} (hx : x ∈ G.piece 0) :
    symTensorExteriorGenerator G x = SymmetricAlgebra.ι R (G.piece 0) ⟨x, hx⟩ ⊗ₜ[R] 1 := by
  simp [symTensorExteriorGenerator, decompose_apply_of_mem_same G.piece hx,
    decompose_apply_of_mem_ne (j := 1) G.piece hx (by decide)]

private theorem symTensorExteriorGenerator_of_mem_piece_one {x : V} (hx : x ∈ G.piece 1) :
    symTensorExteriorGenerator G x = 1 ⊗ₜ[R] ExteriorAlgebra.ι R ⟨x, hx⟩ := by
  simp [symTensorExteriorGenerator, decompose_apply_of_mem_same G.piece hx,
    decompose_apply_of_mem_ne (j := 0) G.piece hx (by decide)]

/-- Comparison homomorphism `ParitySignedSym G → Sym(V_even) ⊗ Λ(V_odd)` over any commutative ring,
sending `x = x₀ + x₁` to `ι x₀ ⊗ₜ 1 + 1 ⊗ₜ ι x₁`. -/
noncomputable def toSymTensorExterior :
    ParitySignedSym G →ₐ[R] SymmetricAlgebra R (G.piece 0) ⊗[R] ExteriorAlgebra R (G.piece 1) :=
  lift G (symTensorExteriorGenerator G) <| by
    intro i j x y hx hy
    rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) i with rfl | rfl <;>
      rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) j with rfl | rfl
    · simp [symTensorExteriorGenerator_of_mem_piece_zero G hx,
        symTensorExteriorGenerator_of_mem_piece_zero G hy, mul_comm]
    · simp [symTensorExteriorGenerator_of_mem_piece_zero G hx,
        symTensorExteriorGenerator_of_mem_piece_one G hy]
    · simp [symTensorExteriorGenerator_of_mem_piece_one G hx,
        symTensorExteriorGenerator_of_mem_piece_zero G hy]
    · rw [symTensorExteriorGenerator_of_mem_piece_one G hx,
        symTensorExteriorGenerator_of_mem_piece_one G hy, Algebra.TensorProduct.tmul_mul_tmul,
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), TensorProduct.tmul_neg]
      simp

@[simp]
theorem toSymTensorExterior_generator (x : V) :
    toSymTensorExterior G (generator G x) =
      SymmetricAlgebra.ι R (G.piece 0) (DirectSum.decompose G.piece x 0) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] ExteriorAlgebra.ι R (DirectSum.decompose G.piece x 1) := by
  simp [toSymTensorExterior, symTensorExteriorGenerator]

/-- On an even-parity generator, `toSymTensorExterior` lands in the left tensor factor. -/
theorem toSymTensorExterior_generator_of_mem_piece_zero {x : V} (hx : x ∈ G.piece 0) :
    toSymTensorExterior G (generator G x) = SymmetricAlgebra.ι R (G.piece 0) ⟨x, hx⟩ ⊗ₜ[R] 1 :=
  (lift_generator G _ _ x).trans (symTensorExteriorGenerator_of_mem_piece_zero G hx)

/-- On an odd-parity generator, `toSymTensorExterior` lands in the right tensor factor. -/
theorem toSymTensorExterior_generator_of_mem_piece_one {x : V} (hx : x ∈ G.piece 1) :
    toSymTensorExterior G (generator G x) = 1 ⊗ₜ[R] ExteriorAlgebra.ι R ⟨x, hx⟩ :=
  (lift_generator G _ _ x).trans (symTensorExteriorGenerator_of_mem_piece_one G hx)

@[simp]
theorem toSymTensorExterior_comp_fromSymmetricEven :
    (toSymTensorExterior G).comp (fromSymmetricEven G) = Algebra.TensorProduct.includeLeft := by
  ext x; simp [toSymTensorExterior_generator_of_mem_piece_zero G x.2]

@[simp]
theorem toSymTensorExterior_fromSymmetricEven (s : SymmetricAlgebra R (G.piece 0)) :
    toSymTensorExterior G (fromSymmetricEven G s) = s ⊗ₜ[R] 1 :=
  AlgHom.congr_fun (toSymTensorExterior_comp_fromSymmetricEven G) s

/-- Over any commutative ring, `toSymTensorExterior G` is surjective. -/
theorem toSymTensorExterior_surjective : Function.Surjective (toSymTensorExterior G) := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  have htop : (⊤ : Subalgebra R
      (SymmetricAlgebra R (G.piece 0) ⊗[R] ExteriorAlgebra R (G.piece 1))) =
      Algebra.TensorProduct.includeLeft.range ⊔ Algebra.TensorProduct.includeRight.range := by
    simpa [Algebra.TensorProduct.map_id] using Algebra.TensorProduct.map_range
      (AlgHom.id R (SymmetricAlgebra R (G.piece 0))) (AlgHom.id R (ExteriorAlgebra R (G.piece 1)))
  rw [htop]
  refine sup_le ?_ ?_
  · rw [← toSymTensorExterior_comp_fromSymmetricEven G]; exact AlgHom.range_comp_le_range _ _
  · rw [← Algebra.map_top, ← CliffordAlgebra.adjoin_range_ι, AlgHom.map_adjoin,
      Algebra.adjoin_le_iff]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨generator G x.1, toSymTensorExterior_generator_of_mem_piece_one G x.2⟩

@[simp]
theorem toSymTensorExterior_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toSymTensorExterior G).comp (fromExteriorOdd G) = Algebra.TensorProduct.includeRight := by
  ext x; simp [toSymTensorExterior_generator_of_mem_piece_one G x.2]

@[simp]
theorem toSymTensorExterior_fromExteriorOdd [Invertible (2 : R)]
    (e : ExteriorAlgebra R (G.piece 1)) :
    toSymTensorExterior G (fromExteriorOdd G e) = 1 ⊗ₜ[R] e :=
  AlgHom.congr_fun (toSymTensorExterior_comp_fromExteriorOdd G) e

/-- When `2` is invertible, multiplication gives `Sym(V_even) ⊗ Λ(V_odd) → ParitySignedSym G`. -/
noncomputable def fromSymTensorExterior [Invertible (2 : R)] :
    SymmetricAlgebra R (G.piece 0) ⊗[R] ExteriorAlgebra R (G.piece 1) →ₐ[R] ParitySignedSym G :=
  Algebra.TensorProduct.lift (fromSymmetricEven G) (fromExteriorOdd G) fun s e =>
    commute_fromSymmetricEven G s (fromExteriorOdd G e)

@[simp]
theorem fromSymTensorExterior_tmul [Invertible (2 : R)]
    (s : SymmetricAlgebra R (G.piece 0)) (e : ExteriorAlgebra R (G.piece 1)) :
    fromSymTensorExterior G (s ⊗ₜ[R] e) = fromSymmetricEven G s * fromExteriorOdd G e :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

@[simp]
theorem fromSymTensorExterior_comp_includeLeft [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp Algebra.TensorProduct.includeLeft = fromSymmetricEven G :=
  AlgHom.ext fun _ => by simp

@[simp]
theorem fromSymTensorExterior_comp_includeRight [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp Algebra.TensorProduct.includeRight = fromExteriorOdd G :=
  AlgHom.ext fun _ => by simp

@[simp]
theorem fromSymTensorExterior_comp_toSymTensorExterior [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp (toSymTensorExterior G) = AlgHom.id R (ParitySignedSym G) := by
  ext x
  calc
    fromSymTensorExterior G (toSymTensorExterior G (generator G x)) =
        generator G (DirectSum.decompose G.piece x 0 : V) +
          generator G (DirectSum.decompose G.piece x 1 : V) := by simp
    _ = generator G x := by rw [← map_add, coe_decompose_zero_add_coe_decompose_one]

@[simp]
theorem fromSymTensorExterior_toSymTensorExterior [Invertible (2 : R)] (a : ParitySignedSym G) :
    fromSymTensorExterior G (toSymTensorExterior G a) = a :=
  AlgHom.congr_fun (fromSymTensorExterior_comp_toSymTensorExterior G) a

@[simp]
theorem toSymTensorExterior_comp_fromSymTensorExterior [Invertible (2 : R)] :
    (toSymTensorExterior G).comp (fromSymTensorExterior G) =
      AlgHom.id R (SymmetricAlgebra R (G.piece 0) ⊗[R] ExteriorAlgebra R (G.piece 1)) :=
  Algebra.TensorProduct.ext (by ext x; simp [toSymTensorExterior_generator_of_mem_piece_zero G x.2])
    (by ext x; simp [toSymTensorExterior_generator_of_mem_piece_one G x.2])

@[simp]
theorem toSymTensorExterior_fromSymTensorExterior [Invertible (2 : R)]
    (z : SymmetricAlgebra R (G.piece 0) ⊗[R] ExteriorAlgebra R (G.piece 1)) :
    toSymTensorExterior G (fromSymTensorExterior G z) = z :=
  AlgHom.congr_fun (toSymTensorExterior_comp_fromSymTensorExterior G) z

/-- **Comparison with symmetric and exterior algebras.** When `2` is invertible in `R`,
`ParitySignedSym G` is canonically isomorphic as an `R`-algebra to `Sym(V_even) ⊗ Λ(V_odd)`. -/
noncomputable def symTensorExteriorEquiv [Invertible (2 : R)] :
    ParitySignedSym G ≃ₐ[R] SymmetricAlgebra R (G.piece 0) ⊗[R] ExteriorAlgebra R (G.piece 1) :=
  AlgEquiv.ofAlgHom (toSymTensorExterior G) (fromSymTensorExterior G)
    (toSymTensorExterior_comp_fromSymTensorExterior G)
    (fromSymTensorExterior_comp_toSymTensorExterior G)

@[simp]
theorem symTensorExteriorEquiv_apply [Invertible (2 : R)] (a : ParitySignedSym G) :
    symTensorExteriorEquiv G a = toSymTensorExterior G a := by simp [symTensorExteriorEquiv]

@[simp]
theorem symTensorExteriorEquiv_toAlgHom [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).toAlgHom = toSymTensorExterior G :=
  AlgEquiv.toAlgHom_ofAlgHom _ _ _ _

@[simp]
theorem symTensorExteriorEquiv_toLinearMap [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).toLinearMap = (toSymTensorExterior G).toLinearMap :=
  AlgEquiv.toLinearMap_ofAlgHom _ _ _ _

@[simp]
theorem symTensorExteriorEquiv_symm_apply [Invertible (2 : R)]
    (z : SymmetricAlgebra R (G.piece 0) ⊗[R] ExteriorAlgebra R (G.piece 1)) :
    (symTensorExteriorEquiv G).symm z = fromSymTensorExterior G z := by
  simp [symTensorExteriorEquiv]

@[simp]
theorem symTensorExteriorEquiv_symm_toAlgHom [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).symm.toAlgHom = fromSymTensorExterior G :=
  AlgHom.ext (symTensorExteriorEquiv_symm_apply G)

@[simp]
theorem symTensorExteriorEquiv_toLinearEquiv_symm_toLinearMap [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).toLinearEquiv.symm.toLinearMap =
      (fromSymTensorExterior G).toLinearMap :=
  LinearMap.ext (symTensorExteriorEquiv_symm_apply G)

/-- When `2` is invertible and both parity summands are free, `ParitySignedSym G` is free. -/
instance instModuleFree [Invertible (2 : R)]
    [Module.Free R (G.piece 0)] [Module.Free R (G.piece 1)] :
    Module.Free R (ParitySignedSym G) :=
  Module.Free.of_equiv (symTensorExteriorEquiv G).symm.toLinearEquiv

end ParitySignedSym

/-! ### Integer-graded specialization (`SignedSym`) -/

namespace SignedSym

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V ℤ)

private noncomputable def symEvenParityEquiv :
    SymmetricAlgebra R (G.parity.piece 0) ≃ₐ[R] SymmetricAlgebra R (parityGrading G.piece 0) :=
  SymmetricAlgebra.mapEquiv R (LinearEquiv.ofEq _ _ (congrFun G.parity_piece 0))

private noncomputable def extOddParityEquiv :
    ExteriorAlgebra R (G.parity.piece 1) ≃ₐ[R] ExteriorAlgebra R (parityGrading G.piece 1) :=
  let e := LinearEquiv.ofEq _ _ (congrFun G.parity_piece 1)
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap) (ExteriorAlgebra.map e.symm.toLinearMap)
    (by rw [ExteriorAlgebra.map_comp_map, e.comp_symm, ExteriorAlgebra.map_id])
    (by rw [ExteriorAlgebra.map_comp_map, e.symm_comp, ExteriorAlgebra.map_id])

private theorem ofEq_decompose_parity (x : V) (k : ZMod 2) :
    LinearEquiv.ofEq _ _ (congrFun G.parity_piece k) (DirectSum.decompose G.parity.piece x k) =
      DirectSum.decompose (parityGrading G.piece) x k := by
  apply Subtype.ext
  have hx := coe_decompose_zero_add_coe_decompose_one G.parity.piece x
  have hm (j : ZMod 2) : (DirectSum.decompose G.parity.piece x j : V) ∈ parityGrading G.piece j :=
    G.parity_piece ▸ (DirectSum.decompose G.parity.piece x j).2
  rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) k with rfl | rfl <;>
    conv_rhs => rw [← hx, DirectSum.decompose_add, DirectSum.add_apply]
  · rw [decompose_apply_of_mem_same (parityGrading G.piece) (hm 0),
      decompose_apply_of_mem_ne (parityGrading G.piece) (hm 1) (by decide), add_zero]; rfl
  · rw [decompose_apply_of_mem_ne (parityGrading G.piece) (hm 0) (by decide),
      decompose_apply_of_mem_same (parityGrading G.piece) (hm 1), zero_add]; rfl

/-! #### Even and odd factor inclusions and projections -/

/-- Canonical algebra map `Sym(V_even) → SignedSym G` over any commutative ring. -/
noncomputable def fromSymmetricEven :
    SymmetricAlgebra R (parityGrading G.piece 0) →ₐ[R] SignedSym G :=
  (parityEquiv G).symm.toAlgHom.comp
    ((ParitySignedSym.fromSymmetricEven G.parity).comp (symEvenParityEquiv G).symm.toAlgHom)

@[simp]
theorem fromSymmetricEven_ι (x : parityGrading G.piece 0) :
    fromSymmetricEven G (SymmetricAlgebra.ι R (parityGrading G.piece 0) x) = generator G x := by
  simp [fromSymmetricEven, symEvenParityEquiv]

/-- Every element in the image of `fromSymmetricEven` commutes with all of `SignedSym G`. -/
theorem commute_fromSymmetricEven (s : SymmetricAlgebra R (parityGrading G.piece 0))
    (a : SignedSym G) : Commute (fromSymmetricEven G s) a := by
  simpa [fromSymmetricEven] using
    (ParitySignedSym.commute_fromSymmetricEven G.parity
      ((symEvenParityEquiv G).symm s) (parityEquiv G a)).map (parityEquiv G).symm.toAlgHom

/-- Every element in the image of `fromSymmetricEven` lies in the center of `SignedSym G`. -/
theorem fromSymmetricEven_mem_center (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    fromSymmetricEven G s ∈ Subalgebra.center R (SignedSym G) :=
  Subalgebra.mem_center_iff.mpr fun a => (commute_fromSymmetricEven G s a).symm

/-- Algebra projection `SignedSym G → Sym(V_even)` sending odd generators to zero. -/
noncomputable def toSymmetricEven :
    SignedSym G →ₐ[R] SymmetricAlgebra R (parityGrading G.piece 0) :=
  (symEvenParityEquiv G).toAlgHom.comp
    ((ParitySignedSym.toSymmetricEven G.parity).comp (parityEquiv G).toAlgHom)

@[simp]
theorem toSymmetricEven_generator (x : V) :
    toSymmetricEven G (generator G x) = SymmetricAlgebra.ι R (parityGrading G.piece 0)
      (DirectSum.decompose (parityGrading G.piece) x 0) := by
  simp [toSymmetricEven, symEvenParityEquiv, ofEq_decompose_parity]

/-- On an even-parity generator, `toSymmetricEven` is the canonical symmetric generator. -/
theorem toSymmetricEven_generator_of_mem_parityGrading_zero {x : V}
    (hx : x ∈ parityGrading G.piece 0) :
    toSymmetricEven G (generator G x) = SymmetricAlgebra.ι R (parityGrading G.piece 0) ⟨x, hx⟩ := by
  rw [toSymmetricEven_generator, decompose_apply_of_mem_same (parityGrading G.piece) hx]

/-- `toSymmetricEven` annihilates odd-parity generators. -/
theorem toSymmetricEven_generator_of_mem_parityGrading_one {x : V}
    (hx : x ∈ parityGrading G.piece 1) : toSymmetricEven G (generator G x) = 0 := by
  rw [toSymmetricEven_generator,
    decompose_apply_of_mem_ne (parityGrading G.piece) hx (by decide), map_zero]

@[simp]
theorem toSymmetricEven_comp_fromSymmetricEven :
    (toSymmetricEven G).comp (fromSymmetricEven G) =
      AlgHom.id R (SymmetricAlgebra R (parityGrading G.piece 0)) := by
  ext x; simp [toSymmetricEven_generator_of_mem_parityGrading_zero G x.2]

@[simp]
theorem toSymmetricEven_fromSymmetricEven (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    toSymmetricEven G (fromSymmetricEven G s) = s :=
  AlgHom.congr_fun (toSymmetricEven_comp_fromSymmetricEven G) s

/-- Over any commutative ring, `fromSymmetricEven G` is injective. -/
theorem fromSymmetricEven_injective : Function.Injective (fromSymmetricEven G) :=
  Function.LeftInverse.injective (toSymmetricEven_fromSymmetricEven G)

/-- Over any commutative ring, `toSymmetricEven G` is surjective. -/
theorem toSymmetricEven_surjective : Function.Surjective (toSymmetricEven G) :=
  Function.RightInverse.surjective (toSymmetricEven_fromSymmetricEven G)

/-- Algebra projection `SignedSym G → Λ(V_odd)` sending even generators to zero. -/
noncomputable def toExteriorOdd :
    SignedSym G →ₐ[R] ExteriorAlgebra R (parityGrading G.piece 1) :=
  (extOddParityEquiv G).toAlgHom.comp
    ((ParitySignedSym.toExteriorOdd G.parity).comp (parityEquiv G).toAlgHom)

@[simp]
theorem toExteriorOdd_generator (x : V) :
    toExteriorOdd G (generator G x) =
      ExteriorAlgebra.ι R (DirectSum.decompose (parityGrading G.piece) x 1) := by
  simp [toExteriorOdd, extOddParityEquiv, ExteriorAlgebra.map_apply_ι, ofEq_decompose_parity]

/-- `toExteriorOdd` annihilates even-parity generators. -/
theorem toExteriorOdd_generator_of_mem_parityGrading_zero {x : V}
    (hx : x ∈ parityGrading G.piece 0) : toExteriorOdd G (generator G x) = 0 := by
  rw [toExteriorOdd_generator,
    decompose_apply_of_mem_ne (parityGrading G.piece) hx (by decide), map_zero]

/-- On an odd-parity generator, `toExteriorOdd` is the canonical exterior generator. -/
theorem toExteriorOdd_generator_of_mem_parityGrading_one {x : V}
    (hx : x ∈ parityGrading G.piece 1) :
    toExteriorOdd G (generator G x) = ExteriorAlgebra.ι R ⟨x, hx⟩ := by
  rw [toExteriorOdd_generator, decompose_apply_of_mem_same (parityGrading G.piece) hx]

@[simp]
theorem toExteriorOdd_comp_fromSymmetricEven :
    (toExteriorOdd G).comp (fromSymmetricEven G) =
      (Algebra.ofId R (ExteriorAlgebra R (parityGrading G.piece 1))).comp
        SymmetricAlgebra.algebraMapInv := by
  ext x; simp [toExteriorOdd_generator_of_mem_parityGrading_zero G x.2,
    SymmetricAlgebra.algebraMapInv_ι]

@[simp]
theorem toExteriorOdd_fromSymmetricEven (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    toExteriorOdd G (fromSymmetricEven G s) =
      algebraMap R (ExteriorAlgebra R (parityGrading G.piece 1))
        (SymmetricAlgebra.algebraMapInv s) :=
  AlgHom.congr_fun (toExteriorOdd_comp_fromSymmetricEven G) s

/-- Over any commutative ring, `toExteriorOdd G` is surjective. -/
theorem toExteriorOdd_surjective : Function.Surjective (toExteriorOdd G) :=
  (extOddParityEquiv G).surjective.comp
    ((ParitySignedSym.toExteriorOdd_surjective G.parity).comp (parityEquiv G).surjective)

/-- When `2` is invertible, canonical algebra map `Λ(V_odd) → SignedSym G`. -/
noncomputable def fromExteriorOdd [Invertible (2 : R)] :
    ExteriorAlgebra R (parityGrading G.piece 1) →ₐ[R] SignedSym G :=
  (parityEquiv G).symm.toAlgHom.comp
    ((ParitySignedSym.fromExteriorOdd G.parity).comp (extOddParityEquiv G).symm.toAlgHom)

@[simp]
theorem fromExteriorOdd_ι [Invertible (2 : R)] (x : parityGrading G.piece 1) :
    fromExteriorOdd G (ExteriorAlgebra.ι R x) = generator G x := by
  simp [fromExteriorOdd, extOddParityEquiv, ExteriorAlgebra.map_apply_ι]

@[simp]
theorem toExteriorOdd_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toExteriorOdd G).comp (fromExteriorOdd G) =
      AlgHom.id R (ExteriorAlgebra R (parityGrading G.piece 1)) := by
  ext x; simp [toExteriorOdd_generator_of_mem_parityGrading_one G x.2]

@[simp]
theorem toExteriorOdd_fromExteriorOdd [Invertible (2 : R)]
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    toExteriorOdd G (fromExteriorOdd G e) = e :=
  AlgHom.congr_fun (toExteriorOdd_comp_fromExteriorOdd G) e

@[simp]
theorem toSymmetricEven_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toSymmetricEven G).comp (fromExteriorOdd G) =
      (Algebra.ofId R (SymmetricAlgebra R (parityGrading G.piece 0))).comp
        ExteriorAlgebra.algebraMapInv := by
  ext x; simp [toSymmetricEven_generator_of_mem_parityGrading_one G x.2,
    ExteriorAlgebra.algebraMapInv]

@[simp]
theorem toSymmetricEven_fromExteriorOdd [Invertible (2 : R)]
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    toSymmetricEven G (fromExteriorOdd G e) =
      algebraMap R (SymmetricAlgebra R (parityGrading G.piece 0))
        (ExteriorAlgebra.algebraMapInv e) :=
  AlgHom.congr_fun (toSymmetricEven_comp_fromExteriorOdd G) e

/-- When `2` is invertible, `fromExteriorOdd G` is injective. -/
theorem fromExteriorOdd_injective [Invertible (2 : R)] : Function.Injective (fromExteriorOdd G) :=
  Function.LeftInverse.injective (toExteriorOdd_fromExteriorOdd G)

/-! #### Tensor product comparison, algebra equivalence, and module freeness -/

/-- Comparison homomorphism `SignedSym G → Sym(V_even) ⊗ Λ(V_odd)` over any commutative ring. -/
noncomputable def toSymTensorExterior :
    SignedSym G →ₐ[R] SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1) :=
  (Algebra.TensorProduct.congr (symEvenParityEquiv G) (extOddParityEquiv G)).toAlgHom.comp
    ((ParitySignedSym.toSymTensorExterior G.parity).comp (parityEquiv G).toAlgHom)

@[simp]
theorem toSymTensorExterior_generator (x : V) :
    toSymTensorExterior G (generator G x) =
      SymmetricAlgebra.ι R (parityGrading G.piece 0)
          (DirectSum.decompose (parityGrading G.piece) x 0) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] ExteriorAlgebra.ι R (DirectSum.decompose (parityGrading G.piece) x 1) := by
  simp [toSymTensorExterior, symEvenParityEquiv, extOddParityEquiv, ExteriorAlgebra.map_apply_ι,
    ofEq_decompose_parity]

/-- On an even-parity generator, `toSymTensorExterior` lands in the left tensor factor. -/
theorem toSymTensorExterior_generator_of_mem_parityGrading_zero {x : V}
    (hx : x ∈ parityGrading G.piece 0) : toSymTensorExterior G (generator G x) =
      SymmetricAlgebra.ι R (parityGrading G.piece 0) ⟨x, hx⟩ ⊗ₜ[R] 1 := by
  simp [decompose_apply_of_mem_same (parityGrading G.piece) hx,
    decompose_apply_of_mem_ne (j := 1) (parityGrading G.piece) hx (by decide)]

/-- On an odd-parity generator, `toSymTensorExterior` lands in the right tensor factor. -/
theorem toSymTensorExterior_generator_of_mem_parityGrading_one {x : V}
    (hx : x ∈ parityGrading G.piece 1) :
    toSymTensorExterior G (generator G x) = 1 ⊗ₜ[R] ExteriorAlgebra.ι R ⟨x, hx⟩ := by
  simp [decompose_apply_of_mem_same (parityGrading G.piece) hx,
    decompose_apply_of_mem_ne (j := 0) (parityGrading G.piece) hx (by decide)]

@[simp]
theorem toSymTensorExterior_comp_fromSymmetricEven :
    (toSymTensorExterior G).comp (fromSymmetricEven G) = Algebra.TensorProduct.includeLeft := by
  ext x; simp [toSymTensorExterior_generator_of_mem_parityGrading_zero G x.2]

@[simp]
theorem toSymTensorExterior_fromSymmetricEven
    (s : SymmetricAlgebra R (parityGrading G.piece 0)) :
    toSymTensorExterior G (fromSymmetricEven G s) = s ⊗ₜ[R] 1 :=
  AlgHom.congr_fun (toSymTensorExterior_comp_fromSymmetricEven G) s

/-- Over any commutative ring, `toSymTensorExterior G` is surjective. -/
theorem toSymTensorExterior_surjective : Function.Surjective (toSymTensorExterior G) :=
  (Algebra.TensorProduct.congr (symEvenParityEquiv G) (extOddParityEquiv G)).surjective.comp
    ((ParitySignedSym.toSymTensorExterior_surjective G.parity).comp (parityEquiv G).surjective)

@[simp]
theorem toSymTensorExterior_comp_fromExteriorOdd [Invertible (2 : R)] :
    (toSymTensorExterior G).comp (fromExteriorOdd G) = Algebra.TensorProduct.includeRight := by
  ext x; simp [toSymTensorExterior_generator_of_mem_parityGrading_one G x.2]

@[simp]
theorem toSymTensorExterior_fromExteriorOdd [Invertible (2 : R)]
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    toSymTensorExterior G (fromExteriorOdd G e) = 1 ⊗ₜ[R] e :=
  AlgHom.congr_fun (toSymTensorExterior_comp_fromExteriorOdd G) e

/-- When `2` is invertible, multiplication gives `Sym(V_even) ⊗ Λ(V_odd) → SignedSym G`. -/
noncomputable def fromSymTensorExterior [Invertible (2 : R)] :
    SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1) →ₐ[R] SignedSym G :=
  (parityEquiv G).symm.toAlgHom.comp
    ((ParitySignedSym.fromSymTensorExterior G.parity).comp
      (Algebra.TensorProduct.congr (symEvenParityEquiv G) (extOddParityEquiv G)).symm.toAlgHom)

@[simp]
theorem fromSymTensorExterior_tmul [Invertible (2 : R)]
    (s : SymmetricAlgebra R (parityGrading G.piece 0))
    (e : ExteriorAlgebra R (parityGrading G.piece 1)) :
    fromSymTensorExterior G (s ⊗ₜ[R] e) = fromSymmetricEven G s * fromExteriorOdd G e := by
  simp [fromSymTensorExterior, fromSymmetricEven, fromExteriorOdd]

@[simp]
theorem fromSymTensorExterior_comp_includeLeft [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp Algebra.TensorProduct.includeLeft = fromSymmetricEven G :=
  AlgHom.ext fun _ => by simp

@[simp]
theorem fromSymTensorExterior_comp_includeRight [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp Algebra.TensorProduct.includeRight = fromExteriorOdd G :=
  AlgHom.ext fun _ => by simp

/-- **Comparison with symmetric and exterior algebras.** When `2` is invertible in `R`,
`SignedSym G` is canonically isomorphic as an `R`-algebra to `Sym(V_even) ⊗ Λ(V_odd)`. -/
noncomputable def symTensorExteriorEquiv [Invertible (2 : R)] :
    SignedSym G ≃ₐ[R] SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1) :=
  (parityEquiv G).trans
    ((ParitySignedSym.symTensorExteriorEquiv G.parity).trans
      (Algebra.TensorProduct.congr (symEvenParityEquiv G) (extOddParityEquiv G)))

@[simp]
theorem symTensorExteriorEquiv_apply [Invertible (2 : R)] (a : SignedSym G) :
    symTensorExteriorEquiv G a = toSymTensorExterior G a := by
  simp [symTensorExteriorEquiv, toSymTensorExterior]

@[simp]
theorem symTensorExteriorEquiv_toAlgHom [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).toAlgHom = toSymTensorExterior G :=
  AlgHom.ext (symTensorExteriorEquiv_apply G)

@[simp]
theorem symTensorExteriorEquiv_toLinearMap [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).toLinearMap = (toSymTensorExterior G).toLinearMap :=
  LinearMap.ext (symTensorExteriorEquiv_apply G)

@[simp]
theorem symTensorExteriorEquiv_symm_apply [Invertible (2 : R)]
    (z : SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1)) :
    (symTensorExteriorEquiv G).symm z = fromSymTensorExterior G z := by
  simp [symTensorExteriorEquiv, fromSymTensorExterior]

@[simp]
theorem symTensorExteriorEquiv_symm_toAlgHom [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).symm.toAlgHom = fromSymTensorExterior G :=
  AlgHom.ext (symTensorExteriorEquiv_symm_apply G)

@[simp]
theorem symTensorExteriorEquiv_toLinearEquiv_symm_toLinearMap [Invertible (2 : R)] :
    (symTensorExteriorEquiv G).toLinearEquiv.symm.toLinearMap =
      (fromSymTensorExterior G).toLinearMap :=
  LinearMap.ext (symTensorExteriorEquiv_symm_apply G)

@[simp]
theorem fromSymTensorExterior_toSymTensorExterior [Invertible (2 : R)] (a : SignedSym G) :
    fromSymTensorExterior G (toSymTensorExterior G a) = a := by
  simpa using (symTensorExteriorEquiv G).symm_apply_apply a

@[simp]
theorem fromSymTensorExterior_comp_toSymTensorExterior [Invertible (2 : R)] :
    (fromSymTensorExterior G).comp (toSymTensorExterior G) = AlgHom.id R (SignedSym G) :=
  AlgHom.ext (fromSymTensorExterior_toSymTensorExterior G)

@[simp]
theorem toSymTensorExterior_fromSymTensorExterior [Invertible (2 : R)]
    (z : SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
      ExteriorAlgebra R (parityGrading G.piece 1)) :
    toSymTensorExterior G (fromSymTensorExterior G z) = z := by
  simpa using (symTensorExteriorEquiv G).apply_symm_apply z

@[simp]
theorem toSymTensorExterior_comp_fromSymTensorExterior [Invertible (2 : R)] :
    (toSymTensorExterior G).comp (fromSymTensorExterior G) =
      AlgHom.id R (SymmetricAlgebra R (parityGrading G.piece 0) ⊗[R]
        ExteriorAlgebra R (parityGrading G.piece 1)) :=
  AlgHom.ext (toSymTensorExterior_fromSymTensorExterior G)

/-- When `2` is invertible and both parity summands are free, `SignedSym G` is a free `R`-module
(supplied automatically from `[∀ p, Module.Free R (G.piece p)]` via
`TauCeti.instModuleFreeCoarsenGrading`). -/
instance instModuleFree [Invertible (2 : R)]
    [Module.Free R (parityGrading G.piece 0)] [Module.Free R (parityGrading G.piece 1)] :
    Module.Free R (SignedSym G) :=
  Module.Free.of_equiv (symTensorExteriorEquiv G).symm.toLinearEquiv

/-! #### Functoriality along degree-preserving maps -/

section Functoriality

variable {W : Type w} [AddCommGroup W] [Module R W] (H : InternalGrading R W ℤ)
variable (f : V →ₗ[R] W) (hf : LinearMap.IsHomogeneous f G.piece H.piece 0)

/-- `fromSymmetricEven` is natural with respect to degree-preserving linear maps. -/
theorem map_comp_fromSymmetricEven :
    (map G H f hf).comp (fromSymmetricEven G) =
      (fromSymmetricEven H).comp (SymmetricAlgebra.map R (hf.parityGrading_zero.restrict 0)) := by
  ext x; simp

/-- `fromExteriorOdd` is natural with respect to degree-preserving linear maps. -/
theorem map_comp_fromExteriorOdd [Invertible (2 : R)] :
    (map G H f hf).comp (fromExteriorOdd G) =
      (fromExteriorOdd H).comp (ExteriorAlgebra.map (hf.parityGrading_zero.restrict 1)) := by
  ext x; simp

/-- `toSymmetricEven` is natural with respect to degree-preserving linear maps. -/
theorem toSymmetricEven_comp_map :
    (toSymmetricEven H).comp (map G H f hf) =
      (SymmetricAlgebra.map R (hf.parityGrading_zero.restrict 0)).comp (toSymmetricEven G) := by
  ext x; simp

/-- `toExteriorOdd` is natural with respect to degree-preserving linear maps. -/
theorem toExteriorOdd_comp_map :
    (toExteriorOdd H).comp (map G H f hf) =
      (ExteriorAlgebra.map (hf.parityGrading_zero.restrict 1)).comp (toExteriorOdd G) := by
  ext x; simp

/-- `toSymTensorExterior` is natural with respect to degree-preserving linear maps. -/
theorem toSymTensorExterior_comp_map :
    (toSymTensorExterior H).comp (map G H f hf) =
      (Algebra.TensorProduct.map (SymmetricAlgebra.map R (hf.parityGrading_zero.restrict 0))
        (ExteriorAlgebra.map (hf.parityGrading_zero.restrict 1))).comp (toSymTensorExterior G) := by
  ext x; simp

/-- `fromSymTensorExterior` is natural with respect to degree-preserving linear maps. -/
theorem map_comp_fromSymTensorExterior [Invertible (2 : R)] :
    (map G H f hf).comp (fromSymTensorExterior G) =
      (fromSymTensorExterior H).comp
        (Algebra.TensorProduct.map (SymmetricAlgebra.map R (hf.parityGrading_zero.restrict 0))
          (ExteriorAlgebra.map (hf.parityGrading_zero.restrict 1))) :=
  Algebra.TensorProduct.ext (by ext x; simp) (by ext x; simp)

end Functoriality

end SignedSym

end TauCeti
