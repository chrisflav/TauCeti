/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Rectangular C⋆-matrix calculus, amplification, and block matrices

Mathlib equips `CStarMatrix m n A` with the Hilbert C⋆-module operator norm and shows that square
matrices `CStarMatrix n n A` form a (non-unital or unital) C⋆-algebra. Operator `K`-theory works
across all matrix sizes simultaneously: rectangular partial isometries witness equivalences between
projections of different matrix sizes, `⋆`-homomorphisms amplify entrywise to every matrix size,
nested matrix algebras flatten isometrically, finite reindexings act by permutation unitaries, and
direct sums are formed by block-diagonal matrices `fromBlocks p 0 0 q`.

This file develops that rectangular and block calculus on `CStarMatrix`:

* **Rectangular operator-norm calculus and C⋆-identities:**
  `toCLM (M * N) = (toCLM N).comp (toCLM M)` (`CStarMatrix.toCLM_mul`), submultiplicativity
  `‖M * N‖ ≤ ‖M‖ * ‖N‖` (`CStarMatrix.norm_mul_le`), and the rectangular C⋆-identities
  `‖M.conjTranspose‖ = ‖M‖` (`CStarMatrix.norm_conjTranspose`),
  `‖M * M.conjTranspose‖ = ‖M‖ ^ 2` (`CStarMatrix.norm_mul_conjTranspose_self`), and
  `‖M.conjTranspose * M‖ = ‖M‖ ^ 2` (`CStarMatrix.norm_conjTranspose_mul_self`), together with the
  vanishing characterizations `M.conjTranspose * M = 0 ↔ M = 0` and
  `M * M.conjTranspose = 0 ↔ M = 0`.
* **Entrywise amplification and nested flattening:** `CStarMatrix.mapStarAlgHom` amplifies unital
  `⋆`-algebra homomorphisms, `CStarMatrix.norm_map_le` and `CStarMatrix.norm_map_of_injective`
  establish rectangular operator-norm contractivity and isometry of `⋆`-homomorphisms, and
  `CStarMatrix.compStarAlgEquiv` identifies `CStarMatrix m m (CStarMatrix n n A)` with
  `CStarMatrix (m × n) (m × n) A` as a `⋆`-algebra equivalence (isometric over C⋆-algebras by
  `StarAlgEquiv.norm_map`).
* **Single-entry corners, reindexing, and permutation unitaries:** `CStarMatrix.single` and the
  isometric corner `⋆`-embedding `CStarMatrix.singleNonUnitalStarAlgHom`, the rectangular linear
  isometry equivalence `CStarMatrix.reindexₗᵢ`, rectangular `PEquiv.toMatrix` conjugation
  `CStarMatrix.toMatrix_toPEquiv_conj_eq_reindexₐ`, and the group homomorphism
  `CStarMatrix.permUnitary : Equiv.Perm n →* unitary (CStarMatrix n n A)` implementing
  `CStarMatrix.reindexₐ` by conjugation.
* **Block matrices:** `CStarMatrix.fromBlocks`, its algebraic and `⋆`-algebraic laws, the bundled
  block-diagonal and corner `⋆`-homomorphisms (`CStarMatrix.blockDiagNonUnitalStarAlgHom`,
  `CStarMatrix.inlNonUnitalStarAlgHom`, `CStarMatrix.inrNonUnitalStarAlgHom`), the rectangular
  block-diagonal norm formula `‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖`
  (`CStarMatrix.norm_fromBlocks_zero₁₂_zero₂₁`), and compatibility with `Equiv.sumComm` and
  `Equiv.sumAssoc`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Sections 3.1 and 4.1.
* N. E. Wegge-Olsen, *K-Theory and C*-Algebras: A Friendly Approach*, Chapters 1–3.
-/

public section

open scoped ComplexOrder InnerProductSpace WithCStarModule

namespace CStarMatrix

section RectangularAlgebra

variable {k l m n o p R A B : Type*}

/-- Pulling `ofMatrix` out of rectangular matrix multiplication. -/
@[simp]
theorem of_mul_of [Fintype m] [Mul A] [AddCommMonoid A] (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix M * ofMatrix N = ofMatrix (M * N) :=
  (rfl)

/-- Reading a rectangular `CStarMatrix` product as an ordinary `Matrix` product. -/
theorem ofMatrix_symm_hMul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N :=
  (rfl)

/-- Pulling `ofMatrix` out of `conjTranspose`. -/
@[simp]
theorem conjTranspose_of [Star A] (M : Matrix m n A) :
    (ofMatrix M).conjTranspose = ofMatrix (Matrix.conjTranspose M) :=
  (rfl)

/-- Reading `conjTranspose` on `CStarMatrix` as `Matrix.conjTranspose`. -/
@[simp]
theorem ofMatrix_symm_conjTranspose [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = Matrix.conjTranspose (ofMatrix.symm M) :=
  (rfl)

/-- Rectangular matrix multiplication on `CStarMatrix` is associative. -/
protected theorem mul_assoc [Fintype l] [Fintype m] [NonUnitalSemiring A]
    (L : CStarMatrix k l A) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    L * M * N = L * (M * N) :=
  Matrix.mul_assoc (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

protected theorem mul_sub [Fintype m] [NonUnitalNonAssocRing A]
    (L : CStarMatrix l m A) (M N : CStarMatrix m n A) :
    L * (M - N) = L * M - L * N :=
  Matrix.mul_sub (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L - M) * N = L * N - M * N :=
  Matrix.sub_mul (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N)

@[simp]
protected theorem neg_mul [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (-M) * N = -(M * N) :=
  Matrix.neg_mul (ofMatrix.symm M) (ofMatrix.symm N)

@[simp]
protected theorem mul_neg [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    M * (-N) = -(M * N) :=
  Matrix.mul_neg (ofMatrix.symm M) (ofMatrix.symm N)

@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M :=
  Matrix.one_mul (ofMatrix.symm M)

@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M :=
  Matrix.mul_one (ofMatrix.symm M)

@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M := by
  ext i j
  simp

@[simp]
theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose := by
  ext i j
  simp

@[simp]
theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose := by
  ext i j
  simp

@[simp]
theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose := by
  ext i j
  simp

@[simp]
theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (c : R) (M : CStarMatrix m n A) :
    (c • M).conjTranspose = star c • M.conjTranspose := by
  ext i j
  simp

@[simp]
theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 :=
  Matrix.conjTranspose_one

@[simp]
theorem conjTranspose_mul [Fintype m] [NonUnitalNonAssocSemiring A] [StarRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose :=
  Matrix.conjTranspose_mul (ofMatrix.symm M) (ofMatrix.symm N)

@[simp]
theorem conjTranspose_eq_zero [AddMonoid A] [StarAddMonoid A]
    {M : CStarMatrix m n A} : M.conjTranspose = 0 ↔ M = 0 :=
  ⟨fun h => by
    simpa only [conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg (conjTranspose (m := n) (n := m) (A := A)) h,
    fun h => by rw [h, conjTranspose_zero]⟩

@[simp]
theorem sum_apply {ι : Type*} [AddCommMonoid A] (s : Finset ι) (f : ι → CStarMatrix m n A)
    (i : m) (j : n) :
    (∑ x ∈ s, f x) i j = ∑ x ∈ s, f x i j := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert _ _ hxs ih => simp [Finset.sum_insert hxs, ih]

end RectangularAlgebra

section RectangularNorm

variable {l m n A : Type*} [NonUnitalCStarAlgebra A]

/-- Rectangular matrix multiplication reverses composition under `toCLM` (since `toCLM` acts on rows
by `Matrix.vecMul`). -/
theorem toCLM_mul [Fintype l] [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  ext v j
  exact congrFun (Matrix.vecMul_vecMul v (ofMatrix.symm M) (ofMatrix.symm N)).symm j

variable [PartialOrder A] [StarOrderedRing A]

/-- Submultiplicativity of the operator norm for rectangular `CStarMatrix` multiplication. -/
protected theorem norm_mul_le [Fintype l] [Fintype m] [Fintype n]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]
  exact ContinuousLinearMap.opNorm_comp_le (toCLM N) (toCLM M)

open ContinuousLinearMap CStarModule in
private theorem norm_sq_le_norm_mul_conjTranspose_self [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖M‖ ^ 2 ≤ ‖M * M.conjTranspose‖ := by
  have hmain : ‖M‖ ≤ √‖M * M.conjTranspose‖ := by
    rw [norm_def, opNorm_le_iff (by positivity)]
    intro v
    rw [norm_eq_sqrt_norm_inner_self (A := A), ← inner_toCLM_conjTranspose_right]
    have h₁ : ‖⟪v, toCLM (ofMatrix.symm M).conjTranspose (toCLM M v)⟫_A‖ ≤
        ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 :=
      calc
        _ ≤ ‖v‖ * ‖toCLM M.conjTranspose (toCLM M v)‖ := norm_inner_le (C⋆ᵐᵒᵈ(A, m → A))
        _ ≤ ‖v‖ * (‖(toCLM M.conjTranspose).comp (toCLM M)‖ * ‖v‖) := by
          gcongr
          exact le_opNorm ((toCLM M.conjTranspose).comp (toCLM M)) v
        _ = ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by
          rw [← toCLM_mul, ← norm_def]
          ring
    have h₂ : ‖v‖ = √(‖v‖ ^ 2) := by simp
    rw [h₂, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt h₁
  rw [← Real.sqrt_le_sqrt_iff (by positivity)]
  simpa [Real.sqrt_sq (norm_nonneg M)] using hmain

private theorem norm_conjTranspose_le [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ ≤ ‖M‖ := by
  obtain h0 | hpos := (norm_nonneg M.conjTranspose).eq_or_lt
  · rw [← h0]
    exact norm_nonneg M
  · refine le_of_mul_le_mul_left ?_ hpos
    calc
      ‖M.conjTranspose‖ * ‖M.conjTranspose‖ = ‖M.conjTranspose‖ ^ 2 := (sq _).symm
      _ ≤ ‖M.conjTranspose * M.conjTranspose.conjTranspose‖ :=
        norm_sq_le_norm_mul_conjTranspose_self M.conjTranspose
      _ = ‖M.conjTranspose * M‖ := by rw [conjTranspose_conjTranspose]
      _ ≤ ‖M.conjTranspose‖ * ‖M‖ := CStarMatrix.norm_mul_le M.conjTranspose M

/-- Taking the conjugate transpose of a rectangular `CStarMatrix` preserves the operator norm. -/
@[simp]
theorem norm_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ = ‖M‖ :=
  le_antisymm (norm_conjTranspose_le M)
    (by simpa only [conjTranspose_conjTranspose] using norm_conjTranspose_le M.conjTranspose)

/-- Rectangular C⋆-identity `‖M * M.conjTranspose‖ = ‖M‖ ^ 2`. -/
@[simp]
theorem norm_mul_conjTranspose_self [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 :=
  le_antisymm
    (by simpa only [norm_conjTranspose, sq] using CStarMatrix.norm_mul_le M M.conjTranspose)
    (norm_sq_le_norm_mul_conjTranspose_self M)

/-- Rectangular C⋆-identity `‖M.conjTranspose * M‖ = ‖M‖ ^ 2`. -/
@[simp]
theorem norm_conjTranspose_mul_self [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose * M‖ = ‖M‖ ^ 2 := by
  simpa only [conjTranspose_conjTranspose, norm_conjTranspose] using
    norm_mul_conjTranspose_self M.conjTranspose

/-- For a rectangular matrix over a C⋆-algebra, `M.conjTranspose * M = 0` iff `M = 0`. -/
@[simp]
theorem conjTranspose_mul_self_eq_zero [Fintype m] [Finite n] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 := by
  cases nonempty_fintype n
  rw [← norm_eq_zero, norm_conjTranspose_mul_self, sq_eq_zero_iff, norm_eq_zero]

/-- For a rectangular matrix over a C⋆-algebra, `M * M.conjTranspose = 0` iff `M = 0`. -/
@[simp]
theorem mul_conjTranspose_self_eq_zero [Finite m] [Fintype n] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 := by
  cases nonempty_fintype m
  rw [← norm_eq_zero, norm_mul_conjTranspose_self, sq_eq_zero_iff, norm_eq_zero]

end RectangularNorm

section MapAndComp

variable {l m n R A B C : Type*}

@[simp]
protected theorem map_zero {F : Type*} [Zero A] [Zero B] [FunLike F A B] [ZeroHomClass F A B]
    (f : F) : (0 : CStarMatrix m n A).map f = 0 := by
  ext i j
  simp

protected theorem map_add {F : Type*} [Add A] [Add B] [FunLike F A B] [AddHomClass F A B]
    (f : F) (M N : CStarMatrix m n A) : (M + N).map f = M.map f + N.map f := by
  ext i j
  simp

theorem map_conjTranspose {F : Type*} [Star A] [Star B] [FunLike F A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    (M.map f).conjTranspose = M.conjTranspose.map f := by
  ext i j
  simp [map_star]

protected theorem map_mul {F : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
    [NonUnitalNonAssocSemiring B] [FunLike F A B] [NonUnitalRingHomClass F A B] (f : F)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f := by
  ext i j
  simp [mul_apply]

@[simp]
protected theorem map_one {F : Type*} [DecidableEq n] [NonAssocSemiring A] [NonAssocSemiring B]
    [FunLike F A B] [RingHomClass F A B] (f : F) :
    (1 : CStarMatrix n n A).map f = 1 := by
  ext i j
  simp [one_apply]

@[simp]
theorem mapₙₐ_id [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A] :
    mapₙₐ (NonUnitalStarAlgHom.id R A) = NonUnitalStarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  rfl

theorem mapₙₐ_comp [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] [NonUnitalNonAssocSemiring C] [Module R C]
    [Star C] (g : B →⋆ₙₐ[R] C) (f : A →⋆ₙₐ[R] B) :
    mapₙₐ (n := n) (g.comp f) = (mapₙₐ g).comp (mapₙₐ f) := by
  ext M i j
  rfl

/-- Applying a unital `⋆`-algebra homomorphism entrywise gives a unital `⋆`-algebra homomorphism
on square `CStarMatrix` algebras. -/
def mapStarAlgHom [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [StarRing A]
    [Algebra R A] [Semiring B] [StarRing B] [Algebra R B] (f : A →⋆ₐ[R] B) :
    CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B where
  toFun M := M.map f
  map_one' := CStarMatrix.map_one f
  map_mul' := CStarMatrix.map_mul f
  map_zero' := CStarMatrix.map_zero f
  map_add' := CStarMatrix.map_add f
  commutes' r := by
    ext i j
    simp only [algebraMap_apply, map_apply]
    split_ifs
    · exact AlgHomClass.commutes f r
    · exact map_zero f
  map_star' M := (map_conjTranspose f M).symm

@[simp]
theorem mapStarAlgHom_apply [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [StarRing A]
    [Algebra R A] [Semiring B] [StarRing B] [Algebra R B] (f : A →⋆ₐ[R] B)
    (M : CStarMatrix n n A) :
    mapStarAlgHom f M = M.map f :=
  (rfl)

@[simp]
theorem mapStarAlgHom_toNonUnitalStarAlgHom [Fintype n] [DecidableEq n] [CommSemiring R]
    [Semiring A] [StarRing A] [Algebra R A] [Semiring B] [StarRing B] [Algebra R B]
    (f : A →⋆ₐ[R] B) :
    (mapStarAlgHom (n := n) f).toNonUnitalStarAlgHom = mapₙₐ f.toNonUnitalStarAlgHom := by
  ext M i j
  rfl

@[simp]
theorem mapStarAlgHom_id [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [StarRing A]
    [Algebra R A] :
    mapStarAlgHom (StarAlgHom.id R A) = StarAlgHom.id R (CStarMatrix n n A) := by
  ext M i j
  rfl

theorem mapStarAlgHom_comp [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [StarRing A]
    [Algebra R A] [Semiring B] [StarRing B] [Algebra R B] [Semiring C] [StarRing C] [Algebra R C]
    (g : B →⋆ₐ[R] C) (f : A →⋆ₐ[R] B) :
    mapStarAlgHom (n := n) (g.comp f) = (mapStarAlgHom g).comp (mapStarAlgHom f) := by
  ext M i j
  rfl

/-- Entrywise application of any `⋆`-algebra homomorphism between C⋆-algebras is norm-contractive
on rectangular `CStarMatrix` spaces. -/
theorem norm_map_le {F : Type*} [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    ‖M.map f‖ ≤ ‖M‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    ← norm_conjTranspose_mul_self M, map_conjTranspose, ← CStarMatrix.map_mul]
  exact NonUnitalStarAlgHom.norm_apply_le
    (mapₙₐ (NonUnitalStarAlgHom.ofClass f : A →⋆ₙₐ[ℂ] B)) (M.conjTranspose * M)

/-- Entrywise application of an injective `⋆`-algebra homomorphism between C⋆-algebras is isometric
on rectangular `CStarMatrix` spaces. -/
theorem norm_map_of_injective {F : Type*} [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (hf : Function.Injective f) (M : CStarMatrix m n A) :
    ‖M.map f‖ = ‖M‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    ← norm_conjTranspose_mul_self M, map_conjTranspose, ← CStarMatrix.map_mul]
  exact NonUnitalStarAlgHom.norm_map
    (mapₙₐ (NonUnitalStarAlgHom.ofClass f : A →⋆ₙₐ[ℂ] B)) (map_injective hf)
    (M.conjTranspose * M)

/-- Entrywise application of a continuous map between C⋆-algebras is continuous on `CStarMatrix`. -/
theorem continuous_map {X : Type*} [TopologicalSpace X]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {g : A → B} (hg : Continuous g) {f : X → CStarMatrix m n A} (hf : Continuous f) :
    Continuous fun x => (f x).map g :=
  continuous_pi fun i => continuous_pi fun j =>
    hg.comp ((continuous_apply j).comp ((continuous_apply i).comp hf))

variable (m n R A) in
/-- Flattening nested square `CStarMatrix` algebras `Mₘ(Mₙ(A)) ≃⋆ₐ[R] M_{m × n}(A)` (isometric over
C⋆-algebras by `StarAlgEquiv.norm_map`). -/
def compStarAlgEquiv [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] :
    CStarMatrix m m (CStarMatrix n n A) ≃⋆ₐ[R] CStarMatrix (m × n) (m × n) A where
  toFun M := ofMatrix (fun ik jl => M ik.1 jl.1 ik.2 jl.2)
  invFun N := ofMatrix (fun i j => ofMatrix (fun k l => N (i, k) (j, l)))
  left_inv M := by
    ext i j k l
    rfl
  right_inv N := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rfl
  map_mul' M N := by
    ext ⟨i, k⟩ ⟨j, l⟩
    -- Unfold entrywise evaluation on both sides to sums over `m`, `n`, and `m × n`.
    change (∑ x : m, M i x * N x j) k l = ∑ xy : m × n, M i xy.1 k xy.2 * N xy.1 j xy.2 l
    rw [sum_apply]
    simp only [mul_apply]
    exact (Fintype.sum_prod_type fun xy : m × n => M i xy.1 k xy.2 * N xy.1 j xy.2 l).symm
  map_add' M N := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rfl
  map_smul' r M := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rfl
  map_star' M := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rfl

@[simp]
theorem compStarAlgEquiv_apply [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (M : CStarMatrix m m (CStarMatrix n n A)) (ik jl : m × n) :
    compStarAlgEquiv m n R A M ik jl = M ik.1 jl.1 ik.2 jl.2 :=
  (rfl)

@[simp]
theorem compStarAlgEquiv_symm_apply [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (N : CStarMatrix (m × n) (m × n) A) (i j : m) (k l : n) :
    (compStarAlgEquiv m n R A).symm N i j k l = N (i, k) (j, l) :=
  (rfl)

end MapAndComp

section SingleAndReindex

variable {k l m n o p R A B : Type*}

/-- The `m × n` matrix with `a` at `(i, j)` and `0` elsewhere. -/
def single [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) (a : A) : CStarMatrix m n A :=
  ofMatrix (Matrix.single i j a)

@[simp]
theorem of_single [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) (a : A) :
    ofMatrix (Matrix.single i j a) = single i j a :=
  (rfl)

@[simp]
theorem ofMatrix_symm_single [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) (a : A) :
    ofMatrix.symm (single i j a : CStarMatrix m n A) = Matrix.single i j a :=
  (rfl)

theorem single_apply [DecidableEq m] [DecidableEq n] [Zero A] (i i' : m) (j j' : n) (a : A) :
    single i j a i' j' = if i = i' ∧ j = j' then a else 0 :=
  Matrix.single_apply i j a i' j'

@[simp]
theorem single_apply_same [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) (a : A) :
    single i j a i j = a :=
  Matrix.single_apply_same i j a

@[simp]
theorem single_zero [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) :
    (single i j 0 : CStarMatrix m n A) = 0 :=
  Matrix.single_zero i j

theorem single_add [DecidableEq m] [DecidableEq n] [AddZeroClass A] (i : m) (j : n) (a b : A) :
    (single i j (a + b) : CStarMatrix m n A) = single i j a + single i j b :=
  Matrix.single_add i j a b

theorem smul_single [DecidableEq m] [DecidableEq n] [Monoid R] [AddMonoid A]
    [DistribMulAction R A] (r : R) (i : m) (j : n) (a : A) :
    r • (single i j a : CStarMatrix m n A) = single i j (r • a) :=
  Matrix.smul_single r i j a

@[simp]
theorem conjTranspose_single [DecidableEq m] [DecidableEq n] [AddMonoid A] [StarAddMonoid A]
    (i : m) (j : n) (a : A) :
    (single i j a : CStarMatrix m n A).conjTranspose = single j i (star a) :=
  Matrix.conjTranspose_single i j a

@[simp]
theorem star_single [DecidableEq n] [AddMonoid A] [StarAddMonoid A] (i j : n) (a : A) :
    star (single i j a : CStarMatrix n n A) = single j i (star a) :=
  Matrix.conjTranspose_single i j a

@[simp]
theorem single_mul_single_same [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [NonUnitalNonAssocSemiring A] (i : l) (j : m) (k : n) (a b : A) :
    (single i j a : CStarMatrix l m A) * (single j k b : CStarMatrix m n A) =
      single i k (a * b) := by
  rw [← of_single, ← of_single, of_mul_of, Matrix.single_mul_single_same, of_single]

theorem single_mul_single_of_ne [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [NonUnitalNonAssocSemiring A] (i : l) {j j' : m} (k : n) (h : j ≠ j') (a b : A) :
    (single i j a : CStarMatrix l m A) * (single j' k b : CStarMatrix m n A) = 0 := by
  ext i' k'
  simp only [mul_apply, single_apply, zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs with h1 h2
  · exact absurd (h1.2.trans h2.1.symm) h
  all_goals simp

@[simp]
theorem map_single {F : Type*} [DecidableEq m] [DecidableEq n] [Zero A] [Zero B]
    [FunLike F A B] [ZeroHomClass F A B] (f : F) (i : m) (j : n) (a : A) :
    (single i j a : CStarMatrix m n A).map f = single i j (f a) := by
  ext i' j'
  simp [single_apply, apply_ite f]

variable (R) in
/-- The diagonal corner inclusion `a ↦ single i i a` as a non-unital `⋆`-algebra homomorphism. -/
def singleNonUnitalStarAlgHom [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) :
    A →⋆ₙₐ[R] CStarMatrix n n A where
  toFun a := single i i a
  map_smul' r a := (smul_single r i i a).symm
  map_zero' := single_zero i i
  map_add' a b := single_add i i a b
  map_mul' a b := (single_mul_single_same i i i a b).symm
  map_star' a := (star_single i i a).symm

variable (R) in
@[simp]
theorem singleNonUnitalStarAlgHom_apply [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) (a : A) :
    singleNonUnitalStarAlgHom R i a = single i i a :=
  (rfl)

theorem singleNonUnitalStarAlgHom_injective [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) :
    Function.Injective (singleNonUnitalStarAlgHom R (A := A) i) := by
  intro a b h
  simpa using congrArg (fun M : CStarMatrix n n A => M i i) h

/-- A single-entry `CStarMatrix` has the same norm as its entry. -/
@[simp]
theorem norm_single [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (i : m) (j : n) (a : A) :
    ‖(single i j a : CStarMatrix m n A)‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    conjTranspose_single, single_mul_single_same, ← singleNonUnitalStarAlgHom_apply ℂ j,
    NonUnitalStarAlgHom.norm_map (singleNonUnitalStarAlgHom ℂ (A := A) j)
      (singleNonUnitalStarAlgHom_injective (R := ℂ) j),
    CStarRing.norm_star_mul_self, sq]

@[simp]
theorem isStarProjection_single_same [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {i : n} {a : A} :
    IsStarProjection (single i i a : CStarMatrix n n A) ↔ IsStarProjection a := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · have h1 := congrArg (fun M : CStarMatrix n n A => M i i) h.isIdempotentElem.eq
    simpa [IsIdempotentElem, single_mul_single_same] using h1
  · have h2 := congrArg (fun M : CStarMatrix n n A => M i i) h.isSelfAdjoint.star_eq
    simpa [IsSelfAdjoint] using h2
  · exact h.map (singleNonUnitalStarAlgHom ℕ i)

@[simp]
theorem reindexₗ_refl [Semiring R] [AddCommMonoid A] [Module R A] :
    reindexₗ R A (Equiv.refl m) (Equiv.refl n) = LinearEquiv.refl R (CStarMatrix m n A) := by
  ext M i j
  rfl

@[simp]
theorem reindexₐ_refl [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A] :
    reindexₐ R A (Equiv.refl n) = StarAlgEquiv.refl R (CStarMatrix n n A) := by
  ext M i j
  rfl

@[simp]
theorem reindexₗ_conjTranspose [Semiring R] [AddCommMonoid A] [Module R A] [Star A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A eₘ eₙ M).conjTranspose = reindexₗ R A eₙ eₘ M.conjTranspose := by
  ext i j
  rfl

theorem reindexₗ_mul [Fintype m] [Fintype o] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    (eₗ : l ≃ n) (eₘ : m ≃ o) (eₙ : k ≃ p) (M : CStarMatrix l m A) (N : CStarMatrix m k A) :
    reindexₗ R A eₗ eₘ M * reindexₗ R A eₘ eₙ N = reindexₗ R A eₗ eₙ (M * N) := by
  ext i j
  simp only [mul_apply, reindexₗ_apply]
  exact Fintype.sum_equiv eₘ.symm _ _ fun _ => rfl

theorem reindexₐ_eq_reindexₗ [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexₐ R A e M = reindexₗ R A e e M :=
  (rfl)

/-- Reindexing rows and columns of a rectangular `CStarMatrix` preserves the operator norm. -/
@[simp]
theorem norm_reindexₗ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    ‖reindexₗ ℂ A eₘ eₙ M‖ = ‖M‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    ← norm_conjTranspose_mul_self M, reindexₗ_conjTranspose, reindexₗ_mul, ← reindexₐ_eq_reindexₗ,
    StarAlgEquiv.norm_map]

/-- Rectangular row-and-column reindexing bundled as a linear isometry equivalence. -/
noncomputable def reindexₗᵢ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    CStarMatrix m n A ≃ₗᵢ[ℂ] CStarMatrix l o A :=
  { reindexₗ ℂ A eₘ eₙ with
    norm_map' := norm_reindexₗ eₘ eₙ }

@[simp]
theorem coe_reindexₗᵢ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (reindexₗᵢ (A := A) eₘ eₙ : CStarMatrix m n A → CStarMatrix l o A) = reindexₗ ℂ A eₘ eₙ :=
  (rfl)

theorem conjTranspose_toMatrix_toPEquiv [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    (ofMatrix (e.toPEquiv.toMatrix : Matrix m n A)).conjTranspose =
      ofMatrix e.symm.toPEquiv.toMatrix := by
  ext i j
  simp only [conjTranspose_apply, ofMatrix_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, apply_ite star, star_one, star_zero]
  exact if_congr (eq_comm.trans e.symm_apply_eq.symm) rfl rfl

theorem toMatrix_toPEquiv_mul_conjTranspose [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    ofMatrix (e.toPEquiv.toMatrix : Matrix m n A) *
        (ofMatrix (e.toPEquiv.toMatrix : Matrix m n A)).conjTranspose = 1 := by
  rw [conjTranspose_toMatrix_toPEquiv, of_mul_of, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
    Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  rfl

theorem conjTranspose_mul_toMatrix_toPEquiv [Fintype m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    (ofMatrix (e.toPEquiv.toMatrix : Matrix m n A)).conjTranspose *
        ofMatrix (e.toPEquiv.toMatrix : Matrix m n A) = 1 := by
  classical
  simpa only [conjTranspose_toMatrix_toPEquiv, Equiv.symm_symm] using
    toMatrix_toPEquiv_mul_conjTranspose (A := A) e.symm

/-- Conjugating `M : CStarMatrix m m A` by the rectangular `n × m` permutation matrix
`ofMatrix e.symm.toPEquiv.toMatrix` implements `reindexₐ R A e`. -/
theorem toMatrix_toPEquiv_conj_eq_reindexₐ [Fintype m] [Fintype n] [DecidableEq m]
    [Semiring R] [NonAssocSemiring A] [StarRing A] [Module R A]
    (e : m ≃ n) (M : CStarMatrix m m A) :
    ofMatrix (e.symm.toPEquiv.toMatrix : Matrix n m A) * M *
        (ofMatrix (e.symm.toPEquiv.toMatrix : Matrix n m A)).conjTranspose =
      reindexₐ R A e M := by
  classical
  rw [conjTranspose_toMatrix_toPEquiv, Equiv.symm_symm]
  ext i j
  have h1 : (e.symm.toPEquiv.toMatrix : Matrix n m A) * ofMatrix.symm M =
      (ofMatrix.symm M).submatrix e.symm id :=
    PEquiv.toMatrix_toPEquiv_mul e.symm (ofMatrix.symm M)
  have h2 : (ofMatrix.symm M).submatrix e.symm id * (e.toPEquiv.toMatrix : Matrix m n A) =
      ((ofMatrix.symm M).submatrix e.symm id).submatrix id e.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ e
  change (((e.symm.toPEquiv.toMatrix : Matrix n m A) * ofMatrix.symm M) *
      (e.toPEquiv.toMatrix : Matrix m n A)) i j = Matrix.reindex e e (ofMatrix.symm M) i j
  rw [h1, h2]
  rfl

variable (A) in
/-- Group homomorphism sending a permutation `e : Equiv.Perm n` to its unitary matrix
`ofMatrix (e⁻¹.permMatrix A)` in `unitary (CStarMatrix n n A)`. -/
def permUnitary [Fintype n] [DecidableEq n] [Ring A] [StarRing A] :
    Equiv.Perm n →* unitary (CStarMatrix n n A) where
  toFun e :=
    ⟨ofMatrix (e⁻¹.permMatrix A), by
      rw [Unitary.mem_iff, star_eq_conjTranspose]
      exact ⟨conjTranspose_mul_toMatrix_toPEquiv e⁻¹, toMatrix_toPEquiv_mul_conjTranspose e⁻¹⟩⟩
  map_one' := Subtype.ext <| by
    change ofMatrix ((1 : Equiv.Perm n)⁻¹.permMatrix A) = ofMatrix 1
    rw [inv_one, Matrix.permMatrix_one]
  map_mul' e₁ e₂ := Subtype.ext <| by
    simp only [Submonoid.coe_mul]
    rw [_root_.mul_inv_rev, Matrix.permMatrix_mul, ← of_mul_of]

@[simp]
theorem coe_permUnitary [Fintype n] [DecidableEq n] [Ring A] [StarRing A] (e : Equiv.Perm n) :
    (permUnitary A e : CStarMatrix n n A) = ofMatrix (e⁻¹.permMatrix A) :=
  (rfl)

/-- Conjugating by `permUnitary A e` implements `reindexₐ R A e`. -/
theorem permUnitary_conj_eq_reindexₐ [Fintype n] [DecidableEq n] [Semiring R] [Ring A] [StarRing A]
    [Module R A] (e : Equiv.Perm n) (M : CStarMatrix n n A) :
    (permUnitary A e : CStarMatrix n n A) * M * star (permUnitary A e : CStarMatrix n n A) =
      reindexₐ R A e M :=
  toMatrix_toPEquiv_conj_eq_reindexₐ e M

/-- An involutive permutation defines a self-adjoint unitary in `CStarMatrix n n A`. -/
theorem isSelfAdjoint_permUnitary_of_involutive [Fintype n] [DecidableEq n] [Ring A] [StarRing A]
    {e : Equiv.Perm n} (he : Function.Involutive e) :
    IsSelfAdjoint (permUnitary A e : CStarMatrix n n A) := by
  have he_inv : e⁻¹ = e := by
    ext x
    exact e.injective (by rw [Equiv.Perm.inv_def, e.apply_symm_apply]; exact (he x).symm)
  have hu : star (permUnitary A e) = permUnitary A e := by
    rw [Unitary.star_eq_inv, ← map_inv, he_inv]
  exact congrArg Subtype.val hu

end SingleAndReindex

section Block

variable {l m n o p q R A B : Type*}

/-- Construct a `(m ⊕ n) × (o ⊕ p)` `CStarMatrix` from four blocks. -/
def fromBlocks (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) :
    CStarMatrix (m ⊕ n) (o ⊕ p) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))

@[simp]
theorem of_fromBlocks (M₁₁ : Matrix m o A) (M₁₂ : Matrix m p A)
    (M₂₁ : Matrix n o A) (M₂₂ : Matrix n p A) :
    ofMatrix (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (ofMatrix M₁₁) (ofMatrix M₁₂) (ofMatrix M₂₁) (ofMatrix M₂₂) :=
  (rfl)

@[simp]
theorem ofMatrix_symm_fromBlocks (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) :
    ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
        (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) :=
  (rfl)

@[simp]
theorem fromBlocks_apply₁₁ (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) (i : m) (j : o) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inl j) = M₁₁ i j :=
  (rfl)

@[simp]
theorem fromBlocks_apply₁₂ (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) (i : m) (j : p) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inr j) = M₁₂ i j :=
  (rfl)

@[simp]
theorem fromBlocks_apply₂₁ (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) (i : n) (j : o) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inl j) = M₂₁ i j :=
  (rfl)

@[simp]
theorem fromBlocks_apply₂₂ (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) (i : n) (j : p) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inr j) = M₂₂ i j :=
  (rfl)

theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix m o A} {M₁₂ N₁₂ : CStarMatrix m p A}
    {M₂₁ N₂₁ : CStarMatrix n o A} {M₂₂ N₂₂ : CStarMatrix n p A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ :=
  Matrix.fromBlocks_inj

@[simp]
theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m o A) (0 : CStarMatrix m p A)
      (0 : CStarMatrix n o A) (0 : CStarMatrix n p A) = 0 :=
  Matrix.fromBlocks_zero

@[simp]
theorem fromBlocks_one [DecidableEq m] [DecidableEq n] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix m m A) 0 0 (1 : CStarMatrix n n A) = 1 :=
  Matrix.fromBlocks_one

theorem fromBlocks_add [Add A]
    (M₁₁ N₁₁ : CStarMatrix m o A) (M₁₂ N₁₂ : CStarMatrix m p A)
    (M₂₁ N₂₁ : CStarMatrix n o A) (M₂₂ N₂₂ : CStarMatrix n p A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) :=
  Matrix.fromBlocks_add _ _ _ _ _ _ _ _

@[simp]
theorem fromBlocks_neg [Neg A]
    (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) :
    -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) :=
  Matrix.fromBlocks_neg _ _ _ _

theorem fromBlocks_sub [Sub A]
    (M₁₁ N₁₁ : CStarMatrix m o A) (M₁₂ N₁₂ : CStarMatrix m p A)
    (M₂₁ N₂₁ : CStarMatrix n o A) (M₂₂ N₂₂ : CStarMatrix n p A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by
  ext (i | i) (j | j) <;> rfl

@[simp]
theorem fromBlocks_smul [SMul R A] (c : R)
    (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) :
    c • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ =
      fromBlocks (c • M₁₁) (c • M₁₂) (c • M₂₁) (c • M₂₂) :=
  Matrix.fromBlocks_smul _ _ _ _ _

theorem fromBlocks_multiply [Fintype o] [Fintype p] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix l o A) (M₁₂ : CStarMatrix l p A)
    (M₂₁ : CStarMatrix m o A) (M₂₂ : CStarMatrix m p A)
    (N₁₁ : CStarMatrix o n A) (N₁₂ : CStarMatrix o q A)
    (N₂₁ : CStarMatrix p n A) (N₂₂ : CStarMatrix p q A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) :=
  Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _

@[simp]
theorem fromBlocks_zero₁₂_zero₂₁_mul [Fintype o] [Fintype p] [NonUnitalNonAssocSemiring A]
    (M₁ : CStarMatrix l o A) (M₂ : CStarMatrix m p A)
    (N₁ : CStarMatrix o n A) (N₂ : CStarMatrix p q A) :
    fromBlocks M₁ 0 0 M₂ * fromBlocks N₁ 0 0 N₂ = fromBlocks (M₁ * N₁) 0 0 (M₂ * N₂) := by
  simp [fromBlocks_multiply]

@[simp]
theorem fromBlocks_conjTranspose [Star A]
    (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
      fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose M₁₂.conjTranspose M₂₂.conjTranspose :=
  Matrix.fromBlocks_conjTranspose _ _ _ _

@[simp]
theorem star_fromBlocks [Star A]
    (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    star (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (star M₁₁) M₂₁.conjTranspose M₁₂.conjTranspose (star M₂₂) :=
  Matrix.fromBlocks_conjTranspose _ _ _ _

@[simp]
theorem fromBlocks_map (M₁₁ : CStarMatrix m o A) (M₁₂ : CStarMatrix m p A)
    (M₂₁ : CStarMatrix n o A) (M₂₂ : CStarMatrix n p A) (f : A → B) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).map f =
      fromBlocks (M₁₁.map f) (M₁₂.map f) (M₂₁.map f) (M₂₂.map f) := by
  ext (i | i) (j | j) <;> rfl

variable (R) in
/-- Block-diagonal direct sum `(M, N) ↦ fromBlocks M 0 0 N` as a non-unital `⋆`-algebra
homomorphism. -/
def blockDiagNonUnitalStarAlgHom [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun MN := fromBlocks MN.1 0 0 MN.2
  map_smul' c MN := by simp
  map_zero' := fromBlocks_zero
  map_add' MN₁ MN₂ := by simp [fromBlocks_add]
  map_mul' MN₁ MN₂ := (fromBlocks_zero₁₂_zero₂₁_mul MN₁.1 MN₁.2 MN₂.1 MN₂.2).symm
  map_star' MN := by simp

variable (R) in
@[simp]
theorem blockDiagNonUnitalStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (MN : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagNonUnitalStarAlgHom R MN = fromBlocks MN.1 0 0 MN.2 :=
  (rfl)

theorem blockDiagNonUnitalStarAlgHom_injective [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (blockDiagNonUnitalStarAlgHom R (m := m) (n := n) (A := A)) := by
  rintro ⟨M₁, N₁⟩ ⟨M₂, N₂⟩ h
  obtain ⟨rfl, -, -, rfl⟩ := fromBlocks_inj.mp h
  rfl

variable (m n R A) in
/-- Upper-left corner inclusion `M ↦ fromBlocks M 0 0 0` as a non-unital `⋆`-algebra
homomorphism. -/
def inlNonUnitalStarAlgHom [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockDiagNonUnitalStarAlgHom R).comp (NonUnitalStarAlgHom.inl R _ _)

@[simp]
theorem inlNonUnitalStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (M : CStarMatrix m m A) :
    inlNonUnitalStarAlgHom m n R A M = fromBlocks M 0 0 0 :=
  (rfl)

theorem inlNonUnitalStarAlgHom_injective [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (inlNonUnitalStarAlgHom m n R A) := fun _ _ h => (fromBlocks_inj.mp h).1

variable (m n R A) in
/-- Lower-right corner inclusion `N ↦ fromBlocks 0 0 0 N` as a non-unital `⋆`-algebra
homomorphism. -/
def inrNonUnitalStarAlgHom [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockDiagNonUnitalStarAlgHom R).comp (NonUnitalStarAlgHom.inr R _ _)

@[simp]
theorem inrNonUnitalStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (N : CStarMatrix n n A) :
    inrNonUnitalStarAlgHom m n R A N = fromBlocks 0 0 0 N :=
  (rfl)

theorem inrNonUnitalStarAlgHom_injective [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (inrNonUnitalStarAlgHom m n R A) :=
  fun _ _ h => (fromBlocks_inj.mp h).2.2.2

/-- The operator norm of a rectangular block-diagonal `CStarMatrix` is the maximum of the norms of
its diagonal blocks. -/
@[simp]
theorem norm_fromBlocks_zero₁₂_zero₂₁ [Fintype m] [Fintype n] [Fintype o] [Fintype p]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (M : CStarMatrix m o A) (N : CStarMatrix n p A) :
    ‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖ := by
  have hsq (X : CStarMatrix o o A) (Y : CStarMatrix p p A) :
      ‖fromBlocks X 0 0 Y‖ = max ‖X‖ ‖Y‖ := by
    rw [← blockDiagNonUnitalStarAlgHom_apply ℂ (X, Y),
      NonUnitalStarAlgHom.norm_map
        (blockDiagNonUnitalStarAlgHom ℂ (m := o) (n := p) (A := A))
        (blockDiagNonUnitalStarAlgHom_injective (R := ℂ)),
      Prod.norm_def]
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), ← norm_conjTranspose_mul_self,
    fromBlocks_conjTranspose, conjTranspose_zero, conjTranspose_zero,
    fromBlocks_zero₁₂_zero₂₁_mul, hsq, norm_conjTranspose_mul_self, norm_conjTranspose_mul_self]
  rcases le_total ‖M‖ ‖N‖ with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (norm_nonneg M) h 2)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (norm_nonneg N) h 2)]

@[simp]
theorem isIdempotentElem_fromBlocks_zero₁₂_zero₂₁ [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    IsIdempotentElem (fromBlocks p 0 0 q) ↔ IsIdempotentElem p ∧ IsIdempotentElem q := by
  simp [IsIdempotentElem, fromBlocks_inj, eq_comm]

theorem isSelfAdjoint_fromBlocks [AddMonoid A] [StarAddMonoid A]
    {M₁₁ : CStarMatrix m m A} {M₁₂ : CStarMatrix m n A}
    {M₂₁ : CStarMatrix n m A} {M₂₂ : CStarMatrix n n A} :
    IsSelfAdjoint (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) ↔
      IsSelfAdjoint M₁₁ ∧ M₁₂.conjTranspose = M₂₁ ∧ IsSelfAdjoint M₂₂ := by
  rw [IsSelfAdjoint, star_fromBlocks, fromBlocks_inj]
  refine ⟨fun ⟨h1, _, h3, h4⟩ => ⟨h1, h3, h4⟩, fun ⟨h1, h3, h4⟩ => ⟨h1, ?_, h3, h4⟩⟩
  simpa using congrArg conjTranspose h3.symm

@[simp]
theorem isSelfAdjoint_fromBlocks_zero₁₂_zero₂₁ [AddMonoid A] [StarAddMonoid A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    IsSelfAdjoint (fromBlocks p 0 0 q) ↔ IsSelfAdjoint p ∧ IsSelfAdjoint q := by
  simp [isSelfAdjoint_fromBlocks]

@[simp]
theorem isStarProjection_fromBlocks_zero₁₂_zero₂₁ [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    IsStarProjection (fromBlocks p 0 0 q) ↔ IsStarProjection p ∧ IsStarProjection q := by
  simp [isStarProjection_iff, and_left_comm, and_assoc]

@[simp]
theorem fromBlocks_zero₁₂_zero₂₁_mem_unitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {u : CStarMatrix m m A} {v : CStarMatrix n n A} :
    fromBlocks u 0 0 v ∈ unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) ↔
      u ∈ unitary (CStarMatrix m m A) ∧ v ∈ unitary (CStarMatrix n n A) := by
  simp [Unitary.mem_iff, ← fromBlocks_one, fromBlocks_inj, and_left_comm, and_assoc]

/-- Reindexing by `Equiv.sumComm m n` swaps the blocks of `fromBlocks`. -/
@[simp]
theorem reindexₐ_sumComm_fromBlocks [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumComm m n) (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks M₂₂ M₂₁ M₁₂ M₁₁ := by
  ext (i | i) (j | j) <;> rfl

/-- Reindexing by `Equiv.sumAssoc l m n` reassociates iterated block-diagonal sums. -/
@[simp]
theorem reindexₐ_sumAssoc_fromBlocks_zero₁₂_zero₂₁ [Fintype l] [Fintype m] [Fintype n]
    [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (M₁ : CStarMatrix l l A) (M₂ : CStarMatrix m m A) (M₃ : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumAssoc l m n) (fromBlocks (fromBlocks M₁ 0 0 M₂) 0 0 M₃) =
      fromBlocks M₁ 0 0 (fromBlocks M₂ 0 0 M₃) := by
  ext (i | (i | i)) (j | (j | j)) <;> rfl

end Block

end CStarMatrix

end
