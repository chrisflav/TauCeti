/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.CoaugmentedBar
public import TauCeti.Algebra.Homology.AInfinity.Curved.Algebra
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Coderivation

/-!
# The bar coderivation of a curved A-infinity algebra

An uncurved `A∞` algebra has its bar differential on the reduced tensor coalgebra
`TauCeti.ReducedTensorWords R A`, extended by zero to `TauCeti.TensorWords R A`. For a curved
`A∞` algebra `𝒜`, the nullary curvature operation `m₀ = 𝒜.curvature ∈ A²` means that
the bar coderivation `b` no longer annihilates the empty word: `b 1 = ofLetter m₀`, and on
positive-length words `b` adds the nullary insertion coderivation
`TauCeti.TensorWords.insertGradedCoderiv` of `m₀` to the zero-extended reduced bar coderivation.

This file develops the curved suspension Taylor correspondence on `TauCeti.TensorWords R A` and
constructs `TauCeti.CurvedAInfinityAlgebra.barDifferential`. A general degree-one Taylor map
`F : TensorWords R A →ₗ[R] A` determines a degree-one graded coderivation
`b = TensorWords.gradedCoderiv (G.shift 1) F 1`, and when `F` is a curved suspension of operations
`mₙ` of degree `2 - n`, the composition `(F ∘ₗ b)` on `1` and on homogeneous pure tensor words
evaluates to the suspended curved Stasheff sums `TauCeti.AInfinity.curvedSuspendedStasheffSum`.
Consequently `b ∘ₗ b = 0` holds if and only if all curved Stasheff identities hold on
homogeneous inputs in every arity `n ≥ 0`. Conversely, any square-zero degree-one coderivation on
`TensorWords R A` builds a curved `A∞` algebra via `TauCeti.CurvedAInfinityAlgebra.ofTaylor`, and
for uncurved `A∞` algebras this construction agrees with
`TauCeti.AInfinityAlgebra.coaugmentedBarDifferential`.

## Main definitions

* `TauCeti.AInfinity.IsCurvedSuspension`: compatibility between a coaugmented Taylor map
  `F : TensorWords R A →ₗ[R] A` and unsuspended operations `mₙ` for all `n ≥ 0`.
* `TauCeti.AInfinity.curvedSuspensionTaylor`: the coaugmented Taylor map suspending `mₙ`.
* `TauCeti.AInfinity.curvedDesuspension`: the unsuspended operations extracted from a coaugmented
  Taylor map.
* `TauCeti.CurvedAInfinityAlgebra.taylor`: the coaugmented Taylor map of a curved `A∞` algebra.
* `TauCeti.CurvedAInfinityAlgebra.barDifferential`: the square-zero degree-one bar coderivation on
  `TensorWords R A`.
* `TauCeti.CurvedAInfinityAlgebra.ofTaylor`: construct a curved `A∞` algebra from a degree-one
  coaugmented Taylor map whose graded coderivation squares to zero.

## Main results

* `TauCeti.AInfinity.IsCurvedSuspension.comp_self_eq_zero_iff_forall_curvedStasheffSum_eq_zero`:
  the curved bar coderivation squares to zero if and only if all curved Stasheff identities hold
  on homogeneous inputs in every arity `n ≥ 0`.
* `TauCeti.CurvedAInfinityAlgebra.barDifferential_sq`:
  `𝒜.barDifferential ∘ₗ 𝒜.barDifferential = 0`.
* `TauCeti.CurvedAInfinityAlgebra.ofTaylor_self`: every curved `A∞` algebra is reconstructed from
  its Taylor map.
* `TauCeti.AInfinityAlgebra.barDifferential_toCurvedAInfinityAlgebra` and
  `TauCeti.CurvedAInfinityAlgebra.barDifferential_eq_coaugmentedBarDifferential`: when the
  curvature vanishes, the curved bar coderivation agrees with
  `TauCeti.AInfinityAlgebra.coaugmentedBarDifferential`.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Section 3.2.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct
open _root_.MultilinearMap

universe uR uA

namespace TauCeti

namespace AInfinity

variable {R : Type uR} {A : Type uA}

section SuspendedCurvedStasheff

variable [CommRing R] [AddCommMonoid A] [Module R A]
variable (m : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin k ↦ A) A)
variable (d : ℕ → ℤ) (x : ℕ → A)

/-- The suspended curved Stasheff sum splits into the uncurved suspended Stasheff sum plus the
curvature insertion terms with inner arity zero. -/
theorem curvedSuspendedStasheffSum_eq_suspendedStasheffSum_add (n : ℕ) :
    curvedSuspendedStasheffSum m d x n =
      suspendedStasheffSum m d x n +
        ∑ p ∈ Finset.range (n + 1), suspendedStasheffTerm m d x p 0 (n - p) := by
  rw [curvedSuspendedStasheffSum_def, suspendedStasheffSum_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le _),
    Finset.sum_insert (by simp), add_comm, Nat.sub_zero, zero_add]

/-- In arity zero, the suspended curved Stasheff sum is `m 1 ![m 0 ![]]`. -/
theorem curvedSuspendedStasheffSum_zero :
    curvedSuspendedStasheffSum m d x 0 = m 1 ![m 0 ![]] := by
  rw [curvedSuspendedStasheffSum_eq_smul, curvedStasheffSum_zero, suspExp_zero,
    negOnePowCast_zero, one_smul]

end SuspendedCurvedStasheff

section CurvedSuspension

variable [CommRing R] [AddCommGroup A] [Module R A]

/-- A coaugmented Taylor map `F : TensorWords R A →ₗ[R] A` is the curved suspension of
operations `mₙ` (`n ≥ 0`) when `F 1 = m 0 ![]` and its restriction along
`TensorWords.reducedInclusion` is the suspension of `m` in positive arities. -/
def IsCurvedSuspension (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A) : Prop :=
  F 1 = m 0 ![] ∧ IsSuspension G (F ∘ₗ TensorWords.reducedInclusion R A) m

/-- Expose the defining conditions of `IsCurvedSuspension` across module boundaries. -/
theorem isCurvedSuspension_def (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A) :
    IsCurvedSuspension G F m ↔
      F 1 = m 0 ![] ∧ IsSuspension G (F ∘ₗ TensorWords.reducedInclusion R A) m :=
  Iff.rfl

/-- Unpack the nullary value of a curved suspension Taylor map. -/
theorem IsCurvedSuspension.apply_one {G : InternalGrading R A ℤ} {F : TensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A}
    (hFm : IsCurvedSuspension G F m) : F 1 = m 0 ![] :=
  ((isCurvedSuspension_def G F m).mp hFm).1

/-- Unpack the positive-arity suspension condition of a curved suspension Taylor map. -/
theorem IsCurvedSuspension.isSuspension {G : InternalGrading R A ℤ}
    {F : TensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A}
    (hFm : IsCurvedSuspension G F m) :
    IsSuspension G (F ∘ₗ TensorWords.reducedInclusion R A) m :=
  ((isCurvedSuspension_def G F m).mp hFm).2

/-- Two coaugmented Taylor maps suspending the same family of operations are equal. -/
theorem IsCurvedSuspension.taylor_eq {G : InternalGrading R A ℤ}
    {F F' : TensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A}
    (hF : IsCurvedSuspension G F m) (hF' : IsCurvedSuspension G F' m) : F = F' := by
  have hred : F ∘ₗ TensorWords.reducedInclusion R A =
      F' ∘ₗ TensorWords.reducedInclusion R A :=
    hF.isSuspension.taylor_eq hF'.isSuspension
  refine LinearMap.ext fun w ↦ ?_
  calc
    F w = F (TensorWords.reducedInclusion R A (TensorWords.reducedProjection R A w) +
        algebraMap R (TensorWords R A) (TensorWords.counit R A w)) := by
      rw [TensorWords.reducedInclusion_reducedProjection_add_algebraMap_counit]
    _ = (F ∘ₗ TensorWords.reducedInclusion R A) (TensorWords.reducedProjection R A w) +
        TensorWords.counit R A w • F 1 := by
      rw [map_add, LinearMap.comp_apply, Algebra.algebraMap_eq_smul_one, map_smul]
    _ = (F' ∘ₗ TensorWords.reducedInclusion R A) (TensorWords.reducedProjection R A w) +
        TensorWords.counit R A w • F' 1 := by
      rw [hred, hF.apply_one, hF'.apply_one]
    _ = F' (TensorWords.reducedInclusion R A (TensorWords.reducedProjection R A w) +
        algebraMap R (TensorWords R A) (TensorWords.counit R A w)) := by
      rw [map_add, LinearMap.comp_apply, Algebra.algebraMap_eq_smul_one, map_smul]
    _ = F' w := by
      rw [TensorWords.reducedInclusion_reducedProjection_add_algebraMap_counit]

/-- A coaugmented Taylor map suspending operations of degree `2 - n` (`n ≥ 0`) has degree one for
the suspended grading on `TensorWords R A`. -/
theorem IsCurvedSuspension.isHomogeneous {G : InternalGrading R A ℤ}
    {F : TensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A}
    (hFm : IsCurvedSuspension G F m)
    (hm : ∀ n, MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n)) :
    LinearMap.IsHomogeneous F (TensorWords.gradedPiece (G.shift 1)) (G.shift 1).piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro D w hw
  have hred : F (TensorWords.reducedInclusion R A (TensorWords.reducedProjection R A w)) ∈
      (G.shift 1).piece (D + 1) := by
    have hproj := (TensorWords.isHomogeneous_reducedProjection (G.shift 1)).map_mem hw
    rw [add_zero] at hproj
    exact (hFm.isSuspension.isHomogeneous fun n _ ↦ hm n).map_mem hproj
  have hcounit : F (algebraMap R (TensorWords R A) (TensorWords.counit R A w)) ∈
      (G.shift 1).piece (D + 1) := by
    by_cases hD : D = 0
    · subst D
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hFm.apply_one]
      refine Submodule.smul_mem _ _ ?_
      rw [InternalGrading.shift_piece, zero_add]
      have hm₀ : m 0 ![] ∈ G.piece (∑ i : Fin 0, (i.elim0 : ℤ) + (2 - (0 : ℕ))) :=
        (hm 0).map_mem (fun i ↦ i.elim0) ![] (fun i ↦ i.elim0)
      simpa using hm₀
    · rw [TensorWords.counit_eq_zero_of_mem_gradedPiece (G.shift 1) hw hD, _root_.map_zero,
        _root_.map_zero]
      exact zero_mem _
  have hsum : F w =
      F (TensorWords.reducedInclusion R A (TensorWords.reducedProjection R A w)) +
        F (algebraMap R (TensorWords R A) (TensorWords.counit R A w)) := by
    rw [← map_add, TensorWords.reducedInclusion_reducedProjection_add_algebraMap_counit]
  rw [hsum]
  exact add_mem hred hcounit

/-- The coaugmented Taylor map suspending a family of operations `mₙ` (`n ≥ 0`). On the empty
word it returns the curvature `m 0 ![]`, and on positive-length words it restricts to
`suspensionTaylor G m`. -/
noncomputable def curvedSuspensionTaylor (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A) :
    TensorWords R A →ₗ[R] A :=
  suspensionTaylor G m ∘ₗ TensorWords.reducedProjection R A +
    (TensorWords.counit R A).smulRight (m 0 ![])

/-- The defining formula of `curvedSuspensionTaylor`. -/
theorem curvedSuspensionTaylor_def (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A) :
    curvedSuspensionTaylor G m =
      suspensionTaylor G m ∘ₗ TensorWords.reducedProjection R A +
        (TensorWords.counit R A).smulRight (m 0 ![]) := (rfl)

/-- On the empty word, `curvedSuspensionTaylor` returns the nullary operation `m 0 ![]`. -/
@[simp]
theorem curvedSuspensionTaylor_one (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A) :
    curvedSuspensionTaylor G m (1 : TensorWords R A) = m 0 ![] := by
  simp [curvedSuspensionTaylor_def]

/-- On a length-zero tensor power, `curvedSuspensionTaylor` scales `m 0 ![]` by the counit. -/
@[simp]
theorem curvedSuspensionTaylor_of_zero (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A)
    (z : TensorPower R 0 A) :
    curvedSuspensionTaylor G m (TensorWords.of R A 0 z) =
      (TensorPower.algebraMap₀ (R := R) (M := A)).symm z • m 0 ![] := by
  simp [curvedSuspensionTaylor_def]

/-- Restricting `curvedSuspensionTaylor` to positive-length words recovers `suspensionTaylor`. -/
@[simp]
theorem curvedSuspensionTaylor_comp_reducedInclusion (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A) :
    curvedSuspensionTaylor G m ∘ₗ TensorWords.reducedInclusion R A = suspensionTaylor G m := by
  ext w
  simp [curvedSuspensionTaylor_def]

/-- Applying `curvedSuspensionTaylor` to an included positive-length word evaluates
`suspensionTaylor`. -/
@[simp]
theorem curvedSuspensionTaylor_reducedInclusion (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A)
    (w : ReducedTensorWords R A) :
    curvedSuspensionTaylor G m (TensorWords.reducedInclusion R A w) = suspensionTaylor G m w := by
  rw [← LinearMap.comp_apply, curvedSuspensionTaylor_comp_reducedInclusion]

/-- On a pure tensor word of positive length, `curvedSuspensionTaylor` evaluates `m n` after
twisting the `i`-th letter by `G.koszulTwist ((n : ℤ) - 1 - i)`. -/
@[simp]
theorem curvedSuspensionTaylor_of_tprod_of_pos (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A)
    {n : ℕ} (hn : 0 < n) (x : Fin n → A) :
    curvedSuspensionTaylor G m (TensorWords.of R A n (PiTensorProduct.tprod R x)) =
      m n fun i ↦ G.koszulTwist ((n : ℤ) - 1 - i) (x i) := by
  rw [← TensorWords.reducedInclusion_of R A ⟨n, hn⟩, curvedSuspensionTaylor_reducedInclusion,
    suspensionTaylor_of_tprod]

/-- On a single letter, `curvedSuspensionTaylor` evaluates the unary operation `m 1`. -/
@[simp]
theorem curvedSuspensionTaylor_ofLetter (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A) (a : A) :
    curvedSuspensionTaylor G m (TensorWords.ofLetter R A a) = m 1 ![a] := by
  rw [TensorWords.ofLetter_eq_of_tprod, curvedSuspensionTaylor_of_tprod_of_pos G m Nat.one_pos]
  congr 1
  funext i
  fin_cases i
  simp

/-- `curvedSuspensionTaylor G m` satisfies `IsCurvedSuspension G _ m`. -/
theorem isCurvedSuspension_curvedSuspensionTaylor (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A) :
    IsCurvedSuspension G (curvedSuspensionTaylor G m) m :=
  (isCurvedSuspension_def G _ m).mpr
    ⟨curvedSuspensionTaylor_one G m, by
      rw [curvedSuspensionTaylor_comp_reducedInclusion]
      exact isSuspension_suspensionTaylor G m⟩

/-- The **curved desuspension** of a coaugmented Taylor map `F : TensorWords R A →ₗ[R] A`: the
unsuspended operations whose curved suspension it is. In arity zero it is the constant map with
value `F 1`, and in positive arity it agrees with `desuspension` on
`F ∘ₗ TensorWords.reducedInclusion R A`. -/
noncomputable def curvedDesuspension (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    (n : ℕ) : MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A :=
  match n with
  | 0 => MultilinearMap.constOfIsEmpty (RingHom.id R) (fun _ : Fin 0 ↦ A) (F 1)
  | n + 1 => desuspension G (F ∘ₗ TensorWords.reducedInclusion R A) (n + 1)

/-- In arity zero, `curvedDesuspension` is the constant multilinear map with value `F 1`. -/
@[simp]
theorem curvedDesuspension_zero (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A) :
    curvedDesuspension G F 0 =
      MultilinearMap.constOfIsEmpty (RingHom.id R) (fun _ : Fin 0 ↦ A) (F 1) := (rfl)

/-- Evaluating `curvedDesuspension` at arity zero returns `F 1`. -/
theorem curvedDesuspension_zero_apply (G : InternalGrading R A ℤ)
    (F : TensorWords R A →ₗ[R] A) (x : Fin 0 → A) : curvedDesuspension G F 0 x = F 1 := (rfl)

/-- In positive arity, `curvedDesuspension` agrees with `desuspension` on the reduced restriction
of `F`. -/
theorem curvedDesuspension_of_pos (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    {n : ℕ} (hn : 0 < n) :
    curvedDesuspension G F n = desuspension G (F ∘ₗ TensorWords.reducedInclusion R A) n := by
  cases n with
  | zero => omega
  | succ k => rfl

/-- In positive arity, `curvedDesuspension` evaluates `F` on the tensor word of Koszul-twisted
letters. -/
theorem curvedDesuspension_apply (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    {n : ℕ} (hn : 0 < n) (x : Fin n → A) :
    curvedDesuspension G F n x =
      F (TensorWords.of R A n
        (PiTensorProduct.tprod R fun i ↦ G.koszulTwist ((n : ℤ) - 1 - i) (x i))) := by
  rw [curvedDesuspension_of_pos G F hn, desuspension_apply G _ hn, LinearMap.comp_apply,
    TensorWords.reducedInclusion_of]

/-- Suspending the curved desuspension of a coaugmented Taylor map recovers `F`. -/
@[simp]
theorem curvedSuspensionTaylor_curvedDesuspension (G : InternalGrading R A ℤ)
    (F : TensorWords R A →ₗ[R] A) :
    curvedSuspensionTaylor G (curvedDesuspension G F) = F := by
  have hred : suspensionTaylor G (curvedDesuspension G F) =
      F ∘ₗ TensorWords.reducedInclusion R A := by
    refine ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_
    rw [suspensionTaylor_of_tprod, LinearMap.comp_apply, TensorWords.reducedInclusion_of,
      curvedDesuspension_apply G F n.property]
    congr 3
    funext i
    rw [← LinearMap.comp_apply (G.koszulTwist _), InternalGrading.koszulTwist_comp_self,
      LinearMap.id_apply]
  refine LinearMap.ext fun w ↦ ?_
  rw [curvedSuspensionTaylor_def, LinearMap.add_apply, LinearMap.comp_apply, hred,
    LinearMap.smulRight_apply, curvedDesuspension_zero_apply, LinearMap.comp_apply]
  calc
    F (TensorWords.reducedInclusion R A (TensorWords.reducedProjection R A w)) +
        TensorWords.counit R A w • F 1
      = F (TensorWords.reducedInclusion R A (TensorWords.reducedProjection R A w) +
          algebraMap R (TensorWords R A) (TensorWords.counit R A w)) := by
        rw [map_add, Algebra.algebraMap_eq_smul_one, map_smul]
    _ = F w := by
        rw [TensorWords.reducedInclusion_reducedProjection_add_algebraMap_counit]

/-- Every coaugmented Taylor map is the curved suspension of its curved desuspension. -/
theorem isCurvedSuspension_curvedDesuspension (G : InternalGrading R A ℤ)
    (F : TensorWords R A →ₗ[R] A) :
    IsCurvedSuspension G F (curvedDesuspension G F) := by
  simpa only [curvedSuspensionTaylor_curvedDesuspension] using
    isCurvedSuspension_curvedSuspensionTaylor G (curvedDesuspension G F)

/-- Any family of operations `m` (`n ≥ 0`) suspended by `F` equals `curvedDesuspension G F`. -/
theorem IsCurvedSuspension.eq_curvedDesuspension {G : InternalGrading R A ℤ}
    {F : TensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A}
    (hFm : IsCurvedSuspension G F m) : m = curvedDesuspension G F := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext x
    rw [curvedDesuspension_zero_apply, Subsingleton.elim x ![], ← hFm.apply_one]
  · ext x
    rw [curvedDesuspension_apply G F hn, ← TensorWords.reducedInclusion_of R A ⟨n, hn⟩,
      ← LinearMap.comp_apply, hFm.isSuspension.taylor_eq (isSuspension_suspensionTaylor G m),
      suspensionTaylor_of_tprod]
    congr 1
    funext i
    rw [← LinearMap.comp_apply (G.koszulTwist _), InternalGrading.koszulTwist_comp_self,
      LinearMap.id_apply]

/-- The curved desuspension of a degree-one coaugmented Taylor map has cohomological degree `2 - n`
in every arity `n ≥ 0`. -/
theorem isHomogeneous_curvedDesuspension {G : InternalGrading R A ℤ}
    {F : TensorWords R A →ₗ[R] A}
    (hF : LinearMap.IsHomogeneous F (TensorWords.gradedPiece (G.shift 1)) (G.shift 1).piece 1)
    {n : ℕ} :
    MultilinearMap.IsHomogeneous (curvedDesuspension G F n)
      (fun _ ↦ G.piece) G.piece (2 - n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [MultilinearMap.isHomogeneous_def]
    intro d x _
    rw [curvedDesuspension_zero_apply, Nat.cast_zero, sub_zero, Finset.univ_eq_empty,
      Finset.sum_empty, zero_add]
    have h1 := hF.map_mem (TensorWords.one_mem_gradedPiece (G.shift 1))
    rw [InternalGrading.shift_piece, zero_add] at h1
    simpa only [show (1 : ℤ) + 1 = 2 by ring] using h1
  · rw [curvedDesuspension_of_pos G F hn]
    have hFred : LinearMap.IsHomogeneous (F ∘ₗ TensorWords.reducedInclusion R A)
        (ReducedTensorWords.gradedPiece (G.shift 1)) (G.shift 1).piece 1 := by
      rw [LinearMap.isHomogeneous_def]
      intro D w hw
      exact hF.map_mem (TensorWords.mem_gradedPiece_of_reducedInclusion hw)
    exact isHomogeneous_desuspension hFred

end CurvedSuspension

section CurvedSquare

variable [CommRing R] [AddCommGroup A] [Module R A]

/-- Evaluating `F ∘ₗ b` on the empty word yields `m 1 ![m 0 ![]]`, the arity-zero curved
Stasheff sum. -/
theorem IsCurvedSuspension.comp_self_of_one {G : InternalGrading R A ℤ}
    {F : TensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A}
    (hFm : IsCurvedSuspension G F m)
    (hm₀ : m 0 ![] ∈ G.piece 2) :
    (F ∘ₗ TensorWords.gradedCoderiv (G.shift 1) F 1) (1 : TensorWords R A) =
      m 1 ![m 0 ![]] := by
  rw [LinearMap.comp_apply, TensorWords.gradedCoderiv_one, hFm.apply_one,
    ← TensorWords.reducedInclusion_ofLetter, ← LinearMap.comp_apply F,
    ReducedTensorWords.ofLetter_eq_of_tprod]
  have h1 := (isSuspension_def G (F ∘ₗ TensorWords.reducedInclusion R A) m).1 hFm.isSuspension
    1 Nat.one_pos (fun _ ↦ 2) (fun _ ↦ m 0 ![]) fun _ _ ↦ hm₀
  refine h1.trans ?_
  rw [evalNat_suspend, suspExp_one, negOnePowCast_zero, one_smul, evalNat_def]
  congr 1
  funext i
  fin_cases i
  rfl

/-- Evaluating `F ∘ₗ b` on a homogeneous pure tensor word of positive length yields the
suspended curved Stasheff sum `curvedSuspendedStasheffSum m d x n`. -/
theorem IsCurvedSuspension.comp_self_of_tprod {G : InternalGrading R A ℤ}
    {F : TensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A}
    (hFm : IsCurvedSuspension G F m)
    {n : ℕ}
    (hm : ∀ s, s ≤ n + 1 →
      MultilinearMap.IsHomogeneous (m s) (fun _ ↦ G.piece) G.piece (2 - s))
    (hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → A)
    (hx : ∀ i < n, x i ∈ G.piece (d i)) :
    (F ∘ₗ TensorWords.gradedCoderiv (G.shift 1) F 1)
        (TensorWords.of R A n (PiTensorProduct.tprod R fun i : Fin n ↦ x i)) =
      curvedSuspendedStasheffSum m d x n := by
  rw [LinearMap.comp_apply, TensorWords.gradedCoderiv_of_pos _ _ _ hn, map_add]
  have hfirst : F (TensorWords.reducedInclusion R A
      (ReducedTensorWords.gradedCoderiv (G.shift 1)
        (F ∘ₗ TensorWords.reducedInclusion R A) 1
        (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R fun i : Fin n ↦ x i)))) =
      suspendedStasheffSum m d x n := by
    let bred := ReducedTensorWords.gradedCoderiv (G.shift 1)
      (F ∘ₗ TensorWords.reducedInclusion R A) 1
    calc
      F (TensorWords.reducedInclusion R A
          (bred (ReducedTensorWords.of R A ⟨n, hn⟩
            (PiTensorProduct.tprod R fun i : Fin n ↦ x i))))
        = (ReducedTensorWords.letter R A ∘ₗ bred)
            (bred (ReducedTensorWords.of R A ⟨n, hn⟩
              (PiTensorProduct.tprod R fun i : Fin n ↦ x i))) := by
          rw [← LinearMap.comp_apply F, ReducedTensorWords.letter_comp_gradedCoderiv]
      _ = (bred ∘ₗ bred).taylorComponent ⟨n, hn⟩
            (PiTensorProduct.tprod R fun i : Fin n ↦ x i) := by
          rw [LinearMap.taylorComponent_apply, LinearMap.comp_apply, LinearMap.comp_apply]
      _ = suspendedStasheffSum m d x n :=
          hFm.isSuspension.taylorComponent_comp_self_apply
            (fun s _ hs ↦ hm s (by omega)) hn d x hx
  have hm₀ : m 0 ![] ∈ G.piece (blockDeg d 0 0) := by
    have hmem := (hm 0 (Nat.zero_le _)).map_mem (fun i ↦ i.elim0) ![] fun i ↦ i.elim0
    simpa [blockDeg_def] using hmem
  have hsecond : F (TensorWords.insertGradedCoderiv (G.shift 1) 1 (F 1)
      (TensorWords.of R A n (PiTensorProduct.tprod R fun i : Fin n ↦ x i))) =
      ∑ p ∈ Finset.range (n + 1), suspendedStasheffTerm m d x p 0 (n - p) := by
    have hx' : ∀ i < n, x i ∈ (G.shift 1).piece (d i - 1) := by
      intro i hi
      rw [InternalGrading.shift_piece, sub_add_cancel]
      exact hx i hi
    rw [hFm.apply_one,
      TensorWords.insertGradedCoderiv_of_tprod_of_homogeneous_nat (G.shift 1) 1 (m 0 ![])
        (fun i ↦ d i - 1) x hx',
      _root_.map_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    rw [map_smul, ← TensorWords.reducedInclusion_of R A ⟨p + 1 + (n - p), by omega⟩,
      ← LinearMap.comp_apply F]
    have hm₀p : m 0 ![] ∈ G.piece (blockDeg d p 0) := by
      simpa [blockDeg_def] using hm₀
    have hreplace : ∀ i < p + 1 + (n - p - 0),
        replaceBlock x p 0 (m 0 ![]) i ∈ G.piece (replaceDeg d p 0 i) := fun _ hi ↦
      replaceBlock_mem_replaceDeg_of_mem_blockDeg G.piece hx hm₀p (by omega) hi
    have houter := (isSuspension_def G (F ∘ₗ TensorWords.reducedInclusion R A) m).1
      hFm.isSuspension (p + 1 + (n - p)) (by omega) (replaceDeg d p 0)
      (replaceBlock x p 0 (m 0 ![])) (fun i hi ↦ hreplace i (by simpa using hi))
    rw [houter, suspendedStasheffTerm_def, one_mul]
    have hinner0 :
        evalNat (suspend (fun j ↦ d (p + j)) (m 0)) (fun j ↦ x (p + j)) = m 0 ![] := by
      rw [evalNat_suspend, suspExp_zero, negOnePowCast_zero, one_smul, evalNat_def]
      exact congrArg (m 0) (funext fun i ↦ i.elim0)
    rw [hinner0]
  rw [hfirst, hsecond, ← curvedSuspendedStasheffSum_eq_suspendedStasheffSum_add]

/-- On homogeneous inputs of length `n > 0`, `(F ∘ₗ b)` evaluates to the curved Stasheff sum
scaled by `negOnePowCast R (suspExp n d)`. -/
theorem IsCurvedSuspension.comp_self_eq_smul_curvedStasheffSum {G : InternalGrading R A ℤ}
    {F : TensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A}
    (hFm : IsCurvedSuspension G F m)
    {n : ℕ}
    (hm : ∀ s, s ≤ n + 1 →
      MultilinearMap.IsHomogeneous (m s) (fun _ ↦ G.piece) G.piece (2 - s))
    (hn : 0 < n) (d : ℕ → ℤ) (x : ℕ → A)
    (hx : ∀ i < n, x i ∈ G.piece (d i)) :
    (F ∘ₗ TensorWords.gradedCoderiv (G.shift 1) F 1)
        (TensorWords.of R A n (PiTensorProduct.tprod R fun i : Fin n ↦ x i)) =
      negOnePowCast R (suspExp n d) • curvedStasheffSum m d x n := by
  rw [hFm.comp_self_of_tprod hm hn d x hx, curvedSuspendedStasheffSum_eq_smul]

/-- **Main theorem of the curved bar construction.** A degree-one curved bar coderivation
`b = TensorWords.gradedCoderiv (G.shift 1) F 1` squares to zero if and only if the unsuspended
operations `mₙ` satisfy every curved Stasheff identity on homogeneous inputs in every arity
`n ≥ 0`. -/
theorem IsCurvedSuspension.comp_self_eq_zero_iff_forall_curvedStasheffSum_eq_zero
    {G : InternalGrading R A ℤ} {F : TensorWords R A →ₗ[R] A}
    {m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A}
    (hFm : IsCurvedSuspension G F m)
    (hm : ∀ n, MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n)) :
    TensorWords.gradedCoderiv (G.shift 1) F 1 ∘ₗ
        TensorWords.gradedCoderiv (G.shift 1) F 1 = 0 ↔
      ∀ (n : ℕ) (d : ℕ → ℤ) (x : ℕ → A),
        (∀ i < n, x i ∈ G.piece (d i)) → curvedStasheffSum m d x n = 0 := by
  have hFhom : LinearMap.IsHomogeneous F (TensorWords.gradedPiece (G.shift 1))
      (G.shift 1).piece 1 := hFm.isHomogeneous hm
  rw [TensorWords.gradedCoderiv_comp_self_eq_zero_iff hFhom]
  have hm₀ : m 0 ![] ∈ G.piece 2 := by
    simpa using (hm 0).map_mem (fun i ↦ i.elim0) ![] (fun i ↦ i.elim0)
  constructor
  · intro hFb n d x hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 := LinearMap.congr_fun hFb (1 : TensorWords R A)
      rw [hFm.comp_self_of_one hm₀, LinearMap.zero_apply] at h1
      simpa only [curvedStasheffSum_zero] using h1
    · have ht := LinearMap.congr_fun hFb
        (TensorWords.of R A n (PiTensorProduct.tprod R fun i : Fin n ↦ x i))
      rw [hFm.comp_self_of_tprod (fun s _ ↦ hm s) hn d x hx, LinearMap.zero_apply] at ht
      exact (curvedSuspendedStasheffSum_eq_zero_iff m d x n).mp ht
  · intro hstasheff
    refine TensorWords.linearMap_ext R A fun n z ↦ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0word : TensorWords.of R A 0 (PiTensorProduct.tprod R z) = (1 : TensorWords R A) := by
        rw [TensorWords.one_eq_of_zero]
        exact TensorWords.of_tprod_congr R A fun i ↦ i.elim0
      rw [h0word, hFm.comp_self_of_one hm₀, LinearMap.zero_apply]
      have h0 := hstasheff 0 0 0 fun _ h ↦ absurd h (Nat.not_lt_zero _)
      simpa only [curvedStasheffSum_zero] using h0
    · suffices hcomp :
          (F ∘ₗ TensorWords.gradedCoderiv (G.shift 1) F 1) ∘ₗ TensorWords.of R A n = 0 by
        exact LinearMap.congr_fun hcomp (PiTensorProduct.tprod R z)
      apply InternalGrading.piTensorProduct_ext (fun _ ↦ G)
      intro q
      let d : ℕ → ℤ := fun i ↦ if h : i < n then (q ⟨i, h⟩).1 else 0
      let x : ℕ → A := fun i ↦ if h : i < n then (q ⟨i, h⟩).2 else 0
      have hx : ∀ i < n, x i ∈ G.piece (d i) := by
        intro i hi
        simp only [x, d, hi, dite_true]
        exact (q ⟨i, hi⟩).2.property
      have ht := hFm.comp_self_of_tprod (fun s _ ↦ hm s) hn d x hx
      have hs : curvedSuspendedStasheffSum m d x n = 0 :=
        (curvedSuspendedStasheffSum_eq_zero_iff m d x n).mpr (hstasheff n d x hx)
      rw [hs] at ht
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply, x, Fin.isLt, dite_true] using ht

end CurvedSquare

end AInfinity

namespace CurvedAInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

section Bar

variable (𝒜 : CurvedAInfinityAlgebra R A)

/-- The coaugmented Taylor map of a curved `A∞` algebra: the curved suspension of its operations
`𝒜.m`. -/
noncomputable def taylor : TensorWords R A →ₗ[R] A :=
  AInfinity.curvedSuspensionTaylor 𝒜.grading 𝒜.m

/-- The defining formula of `CurvedAInfinityAlgebra.taylor`. -/
theorem taylor_def : 𝒜.taylor = AInfinity.curvedSuspensionTaylor 𝒜.grading 𝒜.m := (rfl)

/-- On the empty word, the Taylor map returns the curvature `𝒜.curvature`. -/
@[simp]
theorem taylor_one : 𝒜.taylor (1 : TensorWords R A) = 𝒜.curvature := by
  rw [taylor_def, AInfinity.curvedSuspensionTaylor_one, m_zero_apply]

/-- Restricting the Taylor map to positive-length words recovers `AInfinity.suspensionTaylor`. -/
@[simp]
theorem taylor_comp_reducedInclusion :
    𝒜.taylor ∘ₗ TensorWords.reducedInclusion R A =
      AInfinity.suspensionTaylor 𝒜.grading 𝒜.m := by
  rw [taylor_def, AInfinity.curvedSuspensionTaylor_comp_reducedInclusion]

/-- The Taylor map of a curved `A∞` algebra is a curved suspension of its operations `𝒜.m`. -/
theorem taylor_isCurvedSuspension :
    AInfinity.IsCurvedSuspension 𝒜.grading 𝒜.taylor 𝒜.m :=
  AInfinity.isCurvedSuspension_curvedSuspensionTaylor 𝒜.grading 𝒜.m

/-- The Taylor map has degree one for the suspended grading on `TensorWords R A`. -/
theorem isHomogeneous_taylor :
    LinearMap.IsHomogeneous 𝒜.taylor (TensorWords.gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece 1 :=
  𝒜.taylor_isCurvedSuspension.isHomogeneous 𝒜.m_degree

/-- On a single letter, the Taylor map evaluates the unary operation `𝒜.m 1`. -/
@[simp]
theorem taylor_ofLetter (a : A) :
    𝒜.taylor (TensorWords.ofLetter R A a) = 𝒜.m 1 ![a] := by
  rw [taylor_def, AInfinity.curvedSuspensionTaylor_ofLetter]

/-- On a two-letter word, the Taylor map evaluates `𝒜.m 2` with the degree-one Koszul twist on
the first letter. -/
theorem taylor_of_two (a b : A) :
    𝒜.taylor (TensorWords.of R A 2 (PiTensorProduct.tprod R ![a, b])) =
      𝒜.m 2 ![𝒜.grading.koszulTwist 1 a, b] := by
  rw [taylor_def, AInfinity.curvedSuspensionTaylor_of_tprod_of_pos _ _ (by decide)]
  congr 1
  funext i
  fin_cases i <;> simp [InternalGrading.koszulTwist_zero]

/-- The bar differential of a curved `A∞` algebra: the degree-one graded coderivation on
`TensorWords R A` generated by `𝒜.taylor`. -/
noncomputable def barDifferential : TensorWords R A →ₗ[R] TensorWords R A :=
  TensorWords.gradedCoderiv (𝒜.grading.shift 1) 𝒜.taylor 1

/-- The defining formula of `CurvedAInfinityAlgebra.barDifferential`. -/
theorem barDifferential_def :
    𝒜.barDifferential = TensorWords.gradedCoderiv (𝒜.grading.shift 1) 𝒜.taylor 1 := (rfl)

/-- The bar differential is a graded coderivation of twist parameter one on `TensorWords R A`. -/
theorem isGradedCoderivation_barDifferential :
    TensorWords.IsGradedCoderivation (𝒜.grading.shift 1) 1 𝒜.barDifferential :=
  TensorWords.isGradedCoderivation_gradedCoderiv (𝒜.grading.shift 1) 𝒜.taylor 1

/-- The bar differential raises total letter degree by one. -/
theorem isHomogeneous_barDifferential :
    LinearMap.IsHomogeneous 𝒜.barDifferential
      (TensorWords.gradedPiece (𝒜.grading.shift 1))
      (TensorWords.gradedPiece (𝒜.grading.shift 1)) 1 :=
  TensorWords.isHomogeneous_gradedCoderiv 1 1 𝒜.isHomogeneous_taylor

/-- The letterwise Koszul twist of the suspended words anticommutes with the bar differential. -/
theorem map_koszulTwist_barDifferential (w : TensorWords R A) :
    TensorWords.map ((𝒜.grading.shift 1).koszulTwist 1) (𝒜.barDifferential w) =
      -𝒜.barDifferential (TensorWords.map ((𝒜.grading.shift 1).koszulTwist 1) w) := by
  have hhom : LinearMap.IsHomogeneous 𝒜.barDifferential
      (TensorWords.grading (𝒜.grading.shift 1)).piece
      (TensorWords.grading (𝒜.grading.shift 1)).piece 1 := by
    rw [TensorWords.grading_piece]
    exact 𝒜.isHomogeneous_barDifferential
  rw [← TensorWords.koszulTwist_grading]
  simpa using hhom.koszulTwist_apply 1 w

/-- The letter component of the bar differential is the Taylor map `𝒜.taylor`. -/
@[simp]
theorem letter_comp_barDifferential :
    TensorWords.letter R A ∘ₗ 𝒜.barDifferential = 𝒜.taylor :=
  TensorWords.letter_comp_gradedCoderiv (𝒜.grading.shift 1) 𝒜.taylor 1

/-- The bar differential maps the empty word to the single letter given by the curvature. -/
@[simp]
theorem barDifferential_one :
    𝒜.barDifferential (1 : TensorWords R A) = TensorWords.ofLetter R A 𝒜.curvature := by
  rw [barDifferential_def, TensorWords.gradedCoderiv_one, taylor_one]

/-- The bar differential of a curved `A∞` algebra squares to zero. -/
@[simp]
theorem barDifferential_sq : 𝒜.barDifferential ∘ₗ 𝒜.barDifferential = 0 := by
  rw [barDifferential_def]
  exact (𝒜.taylor_isCurvedSuspension.comp_self_eq_zero_iff_forall_curvedStasheffSum_eq_zero
    𝒜.m_degree).mpr 𝒜.stasheff

end Bar

/-- The bar differential of operations satisfying `m_degree` squares to zero if and only if all
curved Stasheff identities hold on homogeneous inputs. -/
theorem barDifferential_sq_iff_stasheff (G : InternalGrading R A ℤ)
    (m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A)
    (hm : ∀ n, MultilinearMap.IsHomogeneous (m n) (fun _ ↦ G.piece) G.piece (2 - n)) :
    TensorWords.gradedCoderiv (G.shift 1) (AInfinity.curvedSuspensionTaylor G m) 1 ∘ₗ
        TensorWords.gradedCoderiv (G.shift 1) (AInfinity.curvedSuspensionTaylor G m) 1 = 0 ↔
      ∀ (n : ℕ) (d : ℕ → ℤ) (x : ℕ → A),
        (∀ i < n, x i ∈ G.piece (d i)) → AInfinity.curvedStasheffSum m d x n = 0 :=
  (AInfinity.isCurvedSuspension_curvedSuspensionTaylor G m)
    |>.comp_self_eq_zero_iff_forall_curvedStasheffSum_eq_zero hm

section OfTaylor

/-- Construct a curved `A∞` algebra from a degree-one coaugmented Taylor map
`F : TensorWords R A →ₗ[R] A` whose graded coderivation
`TensorWords.gradedCoderiv (G.shift 1) F 1` squares to zero. Its operations are
`AInfinity.curvedDesuspension G F`. -/
noncomputable def ofTaylor (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    (hF : LinearMap.IsHomogeneous F (TensorWords.gradedPiece (G.shift 1)) (G.shift 1).piece 1)
    (hsq : TensorWords.gradedCoderiv (G.shift 1) F 1 ∘ₗ
        TensorWords.gradedCoderiv (G.shift 1) F 1 = 0) :
    CurvedAInfinityAlgebra R A where
  grading := G
  m := AInfinity.curvedDesuspension G F
  m_degree _ := AInfinity.isHomogeneous_curvedDesuspension hF
  stasheff := by
    have hm : ∀ n, MultilinearMap.IsHomogeneous (AInfinity.curvedDesuspension G F n)
        (fun _ ↦ G.piece) G.piece (2 - n) := fun _ ↦
      AInfinity.isHomogeneous_curvedDesuspension hF
    exact ((AInfinity.isCurvedSuspension_curvedDesuspension G F)
      |>.comp_self_eq_zero_iff_forall_curvedStasheffSum_eq_zero hm).mp hsq

/-- The grading of `ofTaylor G F hF hsq` is `G`. -/
@[simp]
theorem ofTaylor_grading (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    (hF hsq) : (ofTaylor G F hF hsq).grading = G := (rfl)

/-- The operations of `ofTaylor G F hF hsq` are `AInfinity.curvedDesuspension G F`. -/
@[simp]
theorem ofTaylor_m (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A) (hF hsq) :
    (ofTaylor G F hF hsq).m = AInfinity.curvedDesuspension G F := (rfl)

/-- The curvature of `ofTaylor G F hF hsq` is `F 1`. -/
@[simp]
theorem ofTaylor_curvature (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    (hF hsq) : (ofTaylor G F hF hsq).curvature = F 1 := by
  rw [← (ofTaylor G F hF hsq).m_zero_apply ![], ofTaylor_m,
    AInfinity.curvedDesuspension_zero_apply]

/-- The Taylor map of `ofTaylor G F hF hsq` recovers `F`. -/
@[simp]
theorem ofTaylor_taylor (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    (hF hsq) : (ofTaylor G F hF hsq).taylor = F := by
  rw [taylor_def, ofTaylor_grading, ofTaylor_m,
    AInfinity.curvedSuspensionTaylor_curvedDesuspension]

/-- The bar differential of `ofTaylor G F hF hsq` is the coderivation generated by `F`. -/
@[simp]
theorem barDifferential_ofTaylor (G : InternalGrading R A ℤ) (F : TensorWords R A →ₗ[R] A)
    (hF hsq) :
    (ofTaylor G F hF hsq).barDifferential = TensorWords.gradedCoderiv (G.shift 1) F 1 := by
  rw [barDifferential_def, ofTaylor_grading, ofTaylor_taylor]

/-- The operations of a curved `A∞` algebra are the curved desuspension of its Taylor map. -/
theorem m_eq_curvedDesuspension (𝒜 : CurvedAInfinityAlgebra R A) :
    𝒜.m = AInfinity.curvedDesuspension 𝒜.grading 𝒜.taylor :=
  𝒜.taylor_isCurvedSuspension.eq_curvedDesuspension

/-- Every curved `A∞` algebra is reconstructed from its own Taylor map via `ofTaylor`. -/
@[simp]
theorem ofTaylor_self (𝒜 : CurvedAInfinityAlgebra R A) :
    ofTaylor 𝒜.grading 𝒜.taylor 𝒜.isHomogeneous_taylor
      (by simpa only [barDifferential_def] using 𝒜.barDifferential_sq) = 𝒜 :=
  ext (ofTaylor_grading _ _ _ _) (by rw [ofTaylor_m, 𝒜.m_eq_curvedDesuspension])

end OfTaylor

end CurvedAInfinityAlgebra

/-! ### Comparison with uncurved bar differentials -/

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-- On positive-length words, the Taylor map of `𝒜.toCurvedAInfinityAlgebra` agrees with
`𝒜.taylor`. -/
theorem taylor_comp_reducedInclusion_toCurvedAInfinityAlgebra :
    𝒜.toCurvedAInfinityAlgebra.taylor ∘ₗ TensorWords.reducedInclusion R A = 𝒜.taylor := by
  rw [CurvedAInfinityAlgebra.taylor_comp_reducedInclusion, toCurvedAInfinityAlgebra_grading,
    toCurvedAInfinityAlgebra_m]
  exact (𝒜.taylor_isSuspension.taylor_eq (AInfinity.isSuspension_suspensionTaylor _ _)).symm

/-- The Taylor map of `𝒜.toCurvedAInfinityAlgebra` factors through
`TensorWords.reducedProjection` and `𝒜.taylor`. -/
theorem taylor_toCurvedAInfinityAlgebra :
    𝒜.toCurvedAInfinityAlgebra.taylor =
      𝒜.taylor ∘ₗ TensorWords.reducedProjection R A := by
  rw [CurvedAInfinityAlgebra.taylor_def, toCurvedAInfinityAlgebra_grading,
    toCurvedAInfinityAlgebra_m, AInfinity.curvedSuspensionTaylor_def, 𝒜.m_zero,
    _root_.zero_apply, LinearMap.smulRight_zero, add_zero,
    𝒜.taylor_isSuspension.taylor_eq (AInfinity.isSuspension_suspensionTaylor _ _)]

/-- Viewing an uncurved `A∞` algebra as a curved one gives the same bar coderivation as
`𝒜.coaugmentedBarDifferential`. -/
@[simp]
theorem barDifferential_toCurvedAInfinityAlgebra :
    𝒜.toCurvedAInfinityAlgebra.barDifferential = 𝒜.coaugmentedBarDifferential := by
  rw [CurvedAInfinityAlgebra.barDifferential_def, toCurvedAInfinityAlgebra_grading,
    TensorWords.gradedCoderiv_of_apply_one_eq_zero _ _
      (by rw [CurvedAInfinityAlgebra.taylor_one, curvature_toCurvedAInfinityAlgebra]),
    taylor_comp_reducedInclusion_toCurvedAInfinityAlgebra,
    AInfinityAlgebra.coaugmentedBarDifferential_def, AInfinityAlgebra.barDifferential_def]

end AInfinityAlgebra

namespace CurvedAInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- A curved `A∞` algebra of curvature zero has the same bar coderivation on `TensorWords R A` as
its associated uncurved `A∞` algebra. -/
theorem barDifferential_eq_coaugmentedBarDifferential (𝒜 : CurvedAInfinityAlgebra R A)
    (h : 𝒜.curvature = 0) :
    𝒜.barDifferential = (𝒜.toAInfinityAlgebra h).coaugmentedBarDifferential := by
  have hbar := (𝒜.toAInfinityAlgebra h).barDifferential_toCurvedAInfinityAlgebra
  rwa [𝒜.toCurvedAInfinityAlgebra_toAInfinityAlgebra h] at hbar

end CurvedAInfinityAlgebra

end TauCeti
