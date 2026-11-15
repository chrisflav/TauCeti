/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# The Segre product of two graded algebras

Let `A = ⨁ᵢ 𝒜 i` and `B = ⨁ᵢ ℬ i` be `ι`-graded `R`-algebras. Their *Segre product* (or *Segre
subalgebra*, EGA II §3.1.4) is

`A ♯ B = ⨆ᵢ im(𝒜 i ⊗[R] ℬ i → A ⊗[R] B)`,

the `R`-subalgebra of `A ⊗[R] B` spanned by pure tensors `a ⊗ₜ b` of homogeneous elements of the
same degree `i`. When `𝒜` and `ℬ` internally decompose `A` and `B`, this sum is direct:
`A ♯ B = ⨁ᵢ (𝒜 i ⊗[R] ℬ i)` is again an `ι`-graded `R`-algebra whose degree-`i` component is
canonically isomorphic to `𝒜 i ⊗[R] ℬ i`.

For `ℕ`-graded commutative `R`-algebras, `Proj (A ♯ B)` is the fibre product `Proj A ×_{Spec R}
Proj B` (EGA II Proposition 3.1.8; Hartshorne Exercise II.5.11). Moreover, if `A` and `B` are
generated in positive degrees over `R` by the images of linear maps `f : M →ₗ[R] 𝒜 1` and
`g : N →ₗ[R] ℬ 1`, then `A ♯ B` is generated in positive degrees over `R` by the image of
`M ⊗[R] N →ₗ[R] (A ♯ B)₁`, giving the Segre closed immersion
`Proj A ×_{Spec R} Proj B ↪ Proj (Sym_R (M ⊗[R] N))` (Stacks, Lemma 27.11.3 (01N0)).

## Implementation notes

In addition to `segreSubalgebra 𝒜 ℬ : Subalgebra R (A ⊗[R] B)`, we bundle its carrier as a
dedicated type `Segre 𝒜 ℬ` whose `CommSemiring`, `Ring`, and `CommRing` instances extend
`Segre.instSemiring` directly (`toSemiring := instSemiring`). On the bare subtype
`↥(segreSubalgebra 𝒜 ℬ)`, `Subalgebra.algebra` uses `Subalgebra.toSemiring`
(`TensorProduct.addCommMonoid`) whereas `Subalgebra.toCommRing` uses `Subalgebra.toSubring`
(`TensorProduct.addCommGroup`), which causes expensive quotient reductions when `GradedAlgebra` and
`CommRing` interact in `HomogeneousLocalization` and `Proj`. On `Segre 𝒜 ℬ`, all ring hierarchies
share the exact same `Semiring` projection at `reducible` transparency.

## Main definitions

* `TauCeti.GradedAlgebra.segreSubalgebra 𝒜 ℬ`: the Segre subalgebra
  `⨆ᵢ map₂ mk (𝒜 i) (ℬ i)` of `A ⊗[R] B`.
* `TauCeti.GradedAlgebra.Segre 𝒜 ℬ`: the carrier type of the Segre product, equipped with
  `Segre.toTensorProduct : Segre 𝒜 ℬ →ₐ[R] A ⊗[R] B` and
  `Segre.equivSubalgebra : Segre 𝒜 ℬ ≃ₐ[R] segreSubalgebra 𝒜 ℬ`.
* `TauCeti.GradedAlgebra.Segre.tmul ha hb`: the pure tensor `a ⊗ₜ b` in `Segre 𝒜 ℬ` for `a ∈ 𝒜 i`
  and `b ∈ ℬ i`.
* `TauCeti.GradedAlgebra.Segre.grading 𝒜 ℬ`: the `ι`-grading on `Segre 𝒜 ℬ`.
* `TauCeti.GradedAlgebra.Segre.gradingEquiv 𝒜 ℬ i`: the `R`-linear equivalence
  `𝒜 i ⊗[R] ℬ i ≃ₗ[R] Segre.grading 𝒜 ℬ i`.
* `TauCeti.GradedAlgebra.Segre.instGradedAlgebra`: the `GradedAlgebra` instance on
  `Segre.grading 𝒜 ℬ`.
* `TauCeti.GradedAlgebra.Segre.map f g`: functoriality of the Segre graded algebra along graded
  `R`-algebra homomorphisms `f : 𝒜 →ₐᵍ[R] 𝒜'` and `g : ℬ →ₐᵍ[R] ℬ'`.
* `TauCeti.GradedAlgebra.Segre.linearMap f g`: the `R`-linear map
  `M ⊗[R] N →ₗ[R] Segre.grading 𝒜 ℬ 1` induced by `f : M →ₗ[R] 𝒜 1` and `g : N →ₗ[R] ℬ 1`.

## Main results

* `TauCeti.GradedAlgebra.Segre.isInternal_grading`: `Segre.grading 𝒜 ℬ` is an internal direct-sum
  decomposition of `Segre 𝒜 ℬ`.
* `TauCeti.GradedAlgebra.Segre.grading_subset_adjoin_range_linearMap`: if `f : M →ₗ[R] 𝒜 1` and
  `g : N →ₗ[R] ℬ 1` generate `𝒜` and `ℬ` in positive degrees over `R`, then `Segre.linearMap f g`
  generates `Segre.grading 𝒜 ℬ` in positive degrees over `R`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique. II. Étude globale élémentaire de quelques
  classes de morphismes*, Publ. Math. IHÉS 8 (1961), §3.1.4 and Proposition 3.1.8.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Exercises I.2.14 and II.5.11.
* [The Stacks Project, Lemma 27.11.3 (01N0)](https://stacks.math.columbia.edu/tag/01N0)
-/

public section

open DirectSum
open scoped TensorProduct

namespace TauCeti.GradedAlgebra

section Subalgebra

variable {ι R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B) [AddMonoid ι]
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ]

/-- The product of the degree-`i` and degree-`j` diagonal tensor pieces in `A ⊗[R] B` lies in the
degree-`(i + j)` diagonal tensor piece. -/
theorem map₂_mk_mul_le (i j : ι) :
    Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i) *
      Submodule.map₂ (TensorProduct.mk R A B) (𝒜 j) (ℬ j) ≤
    Submodule.map₂ (TensorProduct.mk R A B) (𝒜 (i + j)) (ℬ (i + j)) := by
  rw [Submodule.mul_le]
  intro x hx y hy
  have h : Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i) ≤
      (Submodule.map₂ (TensorProduct.mk R A B) (𝒜 (i + j)) (ℬ (i + j))).comap
        (LinearMap.mulRight R y) :=
    Submodule.map₂_le.2 fun a₁ ha₁ b₁ hb₁ ↦ by
      have h' : Submodule.map₂ (TensorProduct.mk R A B) (𝒜 j) (ℬ j) ≤
           (Submodule.map₂ (TensorProduct.mk R A B) (𝒜 (i + j)) (ℬ (i + j))).comap
            (LinearMap.mulLeft R (a₁ ⊗ₜ[R] b₁)) :=
        Submodule.map₂_le.2 fun a₂ ha₂ b₂ hb₂ ↦ by
          simpa using Submodule.apply_mem_map₂ (TensorProduct.mk R A B)
            (SetLike.mul_mem_graded ha₁ ha₂) (SetLike.mul_mem_graded hb₁ hb₂)
      exact h' hy
  exact h hx

/-- The *Segre subalgebra* `⨆ᵢ map₂ mk (𝒜 i) (ℬ i)` of `A ⊗[R] B`: the `R`-subalgebra spanned by
pure tensors `a ⊗ₜ b` of homogeneous elements of the same degree. -/
def segreSubalgebra : Subalgebra R (A ⊗[R] B) :=
  Submodule.toSubalgebra (⨆ i : ι, Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i))
    (Submodule.mem_iSup_of_mem 0 <| by
      simpa [Algebra.TensorProduct.one_def] using Submodule.apply_mem_map₂
        (TensorProduct.mk R A B) (SetLike.GradedOne.one_mem (A := 𝒜))
        (SetLike.GradedOne.one_mem (A := ℬ)))
    fun {x y} hx hy ↦ by
      induction hx using Submodule.iSup_induction' with
      | mem i x hx =>
        induction hy using Submodule.iSup_induction' with
        | mem j y hy =>
          exact Submodule.mem_iSup_of_mem (i + j)
            (map₂_mk_mul_le 𝒜 ℬ i j (Submodule.mul_mem_mul hx hy))
        | zero => simp
        | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | zero => simp
      | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz

variable {𝒜 ℬ} in
/-- Membership in `segreSubalgebra 𝒜 ℬ` is membership in `⨆ i, map₂ mk (𝒜 i) (ℬ i)`. -/
theorem mem_segreSubalgebra {x : A ⊗[R] B} :
    x ∈ segreSubalgebra 𝒜 ℬ ↔
      x ∈ ⨆ i : ι, Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i) :=
  -- `(Iff.rfl)`, not `Iff.rfl`: `segreSubalgebra` is not `@[expose]`d.
  (Iff.rfl)

variable {𝒜 ℬ} in
/-- Every element of `map₂ mk (𝒜 i) (ℬ i)` lies in `segreSubalgebra 𝒜 ℬ`. -/
theorem mem_segreSubalgebra_of_mem {i : ι} {x : A ⊗[R] B}
    (hx : x ∈ Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i)) :
    x ∈ segreSubalgebra 𝒜 ℬ :=
  Submodule.mem_iSup_of_mem i hx

variable {𝒜 ℬ} in
/-- A pure tensor of homogeneous elements of the same degree lies in `segreSubalgebra 𝒜 ℬ`. -/
theorem tmul_mem_segreSubalgebra {i : ι} {a : A} {b : B} (ha : a ∈ 𝒜 i) (hb : b ∈ ℬ i) :
    a ⊗ₜ[R] b ∈ segreSubalgebra 𝒜 ℬ :=
  mem_segreSubalgebra_of_mem (Submodule.apply_mem_map₂ (TensorProduct.mk R A B) ha hb)

variable {𝒜 ℬ} in
/-- `segreSubalgebra 𝒜 ℬ` is the smallest `R`-subalgebra containing `a ⊗ₜ b` for all `a ∈ 𝒜 i` and
`b ∈ ℬ i`. -/
theorem segreSubalgebra_le_iff {S : Subalgebra R (A ⊗[R] B)} :
    segreSubalgebra 𝒜 ℬ ≤ S ↔
      ∀ i (a : A), a ∈ 𝒜 i → ∀ (b : B), b ∈ ℬ i → a ⊗ₜ[R] b ∈ S := by
  refine (iSup_le_iff (a := Subalgebra.toSubmodule S)).trans ?_
  simp_rw [Submodule.map₂_le, TensorProduct.mk_apply]
  rfl

/-- The *Segre product* `A ♯ B` of two `ι`-graded `R`-algebras `𝒜` and `ℬ`, bundled as a dedicated
type over `segreSubalgebra 𝒜 ℬ` so that its `Semiring`, `CommSemiring`, `Ring`, and `CommRing`
structures share a single defeq `Semiring` projection. -/
@[ext]
structure Segre : Type (max u_3 u_4) where
  /-- Construct an element of `Segre 𝒜 ℬ` from an element of `segreSubalgebra 𝒜 ℬ`. -/
  ofSubalgebra ::
  /-- The underlying element of `segreSubalgebra 𝒜 ℬ`. -/
  toSubalgebra : segreSubalgebra 𝒜 ℬ

end Subalgebra

namespace Segre

section Semiring

variable {ι R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B} [AddMonoid ι]
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ]

/-- `Segre.toSubalgebra` is injective. -/
theorem toSubalgebra_injective :
    Function.Injective (Segre.toSubalgebra (𝒜 := 𝒜) (ℬ := ℬ)) :=
  fun _ _ ↦ Segre.ext

instance instZero : Zero (Segre 𝒜 ℬ) := ⟨⟨0⟩⟩
instance instOne : One (Segre 𝒜 ℬ) := ⟨⟨1⟩⟩
instance instAdd : Add (Segre 𝒜 ℬ) := ⟨fun x y ↦ ⟨x.1 + y.1⟩⟩
instance instMul : Mul (Segre 𝒜 ℬ) := ⟨fun x y ↦ ⟨x.1 * y.1⟩⟩
instance instPow : Pow (Segre 𝒜 ℬ) ℕ := ⟨fun x n ↦ ⟨x.1 ^ n⟩⟩
instance instNatCast : NatCast (Segre 𝒜 ℬ) := ⟨fun n ↦ ⟨n⟩⟩

instance instSMul {S : Type*} [SMul S (segreSubalgebra 𝒜 ℬ)] : SMul S (Segre 𝒜 ℬ) :=
  ⟨fun s x ↦ ⟨s • x.1⟩⟩

instance instSemiring : Semiring (Segre 𝒜 ℬ) :=
  toSubalgebra_injective.semiring _ rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)

instance instAlgebra : Algebra R (Segre 𝒜 ℬ) where
  algebraMap :=
    { toFun r := ⟨algebraMap R (segreSubalgebra 𝒜 ℬ) r⟩
      map_one' := Segre.ext (map_one _)
      map_mul' x y := Segre.ext (map_mul _ x y)
      map_zero' := Segre.ext (map_zero _)
      map_add' x y := Segre.ext (map_add _ x y) }
  commutes' r x := toSubalgebra_injective (Algebra.commutes r x.1)
  smul_def' r x := toSubalgebra_injective (Algebra.smul_def r x.1)

/-- The canonical `R`-algebra isomorphism `Segre 𝒜 ℬ ≃ₐ[R] segreSubalgebra 𝒜 ℬ`. -/
def equivSubalgebra : Segre 𝒜 ℬ ≃ₐ[R] segreSubalgebra 𝒜 ℬ where
  toFun := Segre.toSubalgebra
  invFun := Segre.ofSubalgebra
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The injective `R`-algebra inclusion `Segre 𝒜 ℬ →ₐ[R] A ⊗[R] B`. -/
def toTensorProduct : Segre 𝒜 ℬ →ₐ[R] A ⊗[R] B :=
  (segreSubalgebra 𝒜 ℬ).val.comp (equivSubalgebra (𝒜 := 𝒜) (ℬ := ℬ)).toAlgHom

/-- `Segre.toTensorProduct` is injective. -/
theorem toTensorProduct_injective :
    Function.Injective (toTensorProduct (𝒜 := 𝒜) (ℬ := ℬ)) :=
  Subtype.val_injective.comp toSubalgebra_injective

/-- Two elements of `Segre 𝒜 ℬ` are equal if their images in `A ⊗[R] B` are equal. -/
@[ext]
theorem ext_toTensorProduct {x y : Segre 𝒜 ℬ} (h : toTensorProduct x = toTensorProduct y) :
    x = y :=
  toTensorProduct_injective h

@[simp]
theorem toTensorProduct_ofSubalgebra (x : segreSubalgebra 𝒜 ℬ) :
    toTensorProduct (ofSubalgebra x) = (x : A ⊗[R] B) :=
  -- `(rfl)`, not `rfl`: `toTensorProduct` is not `@[expose]`d.
  (rfl)

/-- The pure tensor `a ⊗ₜ b` in `Segre 𝒜 ℬ`, for `a ∈ 𝒜 i` and `b ∈ ℬ i`. -/
def tmul {i : ι} {a : A} {b : B} (ha : a ∈ 𝒜 i) (hb : b ∈ ℬ i) : Segre 𝒜 ℬ :=
  ⟨⟨a ⊗ₜ[R] b, tmul_mem_segreSubalgebra ha hb⟩⟩

@[simp]
theorem toTensorProduct_tmul {i : ι} {a : A} {b : B} (ha : a ∈ 𝒜 i) (hb : b ∈ ℬ i) :
    toTensorProduct (tmul ha hb) = a ⊗ₜ[R] b :=
  -- `(rfl)`, not `rfl`: `tmul` and `toTensorProduct` are not `@[expose]`d.
  (rfl)

@[simp]
theorem tmul_mul_tmul {i j : ι} {a₁ a₂ : A} {b₁ b₂ : B}
    (ha₁ : a₁ ∈ 𝒜 i) (hb₁ : b₁ ∈ ℬ i) (ha₂ : a₂ ∈ 𝒜 j) (hb₂ : b₂ ∈ ℬ j) :
    tmul ha₁ hb₁ * tmul ha₂ hb₂ =
      tmul (SetLike.mul_mem_graded ha₁ ha₂) (SetLike.mul_mem_graded hb₁ hb₂) := by
  apply ext_toTensorProduct
  simp

@[simp]
theorem tmul_pow {i : ι} {a : A} {b : B} (ha : a ∈ 𝒜 i) (hb : b ∈ ℬ i) (n : ℕ) :
    tmul ha hb ^ n =
      tmul (SetLike.pow_mem_graded n ha) (SetLike.pow_mem_graded n hb) := by
  apply ext_toTensorProduct
  simp [Algebra.TensorProduct.tmul_pow]

variable (𝒜 ℬ) in
/-- The grading on `Segre 𝒜 ℬ`: its degree-`i` piece is the preimage of
`map₂ mk (𝒜 i) (ℬ i)` along `toTensorProduct`. -/
def grading (i : ι) : Submodule R (Segre 𝒜 ℬ) :=
  (Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i)).comap toTensorProduct.toLinearMap

@[simp]
theorem mem_grading {i : ι} {x : Segre 𝒜 ℬ} :
    x ∈ grading 𝒜 ℬ i ↔
      toTensorProduct x ∈ Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i) :=
  -- `(Iff.rfl)`, not `Iff.rfl`: `grading` is not `@[expose]`d.
  (Iff.rfl)

/-- For `a ∈ 𝒜 i` and `b ∈ ℬ i`, `Segre.tmul ha hb` has degree `i`. -/
theorem tmul_mem_grading {i : ι} {a : A} {b : B} (ha : a ∈ 𝒜 i) (hb : b ∈ ℬ i) :
    tmul ha hb ∈ grading 𝒜 ℬ i :=
  Submodule.apply_mem_map₂ (TensorProduct.mk R A B) ha hb

variable (𝒜 ℬ) in
/-- The degree-`i` piece of `Segre 𝒜 ℬ`, mapped into `A ⊗[R] B`, is `map₂ mk (𝒜 i) (ℬ i)`. -/
theorem map_grading (i : ι) :
    (grading 𝒜 ℬ i).map toTensorProduct.toLinearMap =
      Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i) := by
  refine le_antisymm (Submodule.map_comap_le _ _) fun x hx ↦ ?_
  exact ⟨⟨⟨x, mem_segreSubalgebra_of_mem hx⟩⟩, hx, rfl⟩

/-- The components of `Segre.grading 𝒜 ℬ` multiply like a grading. -/
instance : SetLike.GradedMonoid (grading 𝒜 ℬ) where
  one_mem := by
    rw [mem_grading, map_one, Algebra.TensorProduct.one_def]
    exact Submodule.apply_mem_map₂ (TensorProduct.mk R A B)
      (SetLike.GradedOne.one_mem (A := 𝒜)) (SetLike.GradedOne.one_mem (A := ℬ))
  mul_mem i j x y hx hy := by
    rw [mem_grading, map_mul]
    exact map₂_mk_mul_le 𝒜 ℬ i j (Submodule.mul_mem_mul hx hy)

variable (𝒜 ℬ) in
/-- `Segre 𝒜 ℬ` is spanned by its graded pieces `Segre.grading 𝒜 ℬ i`. -/
theorem iSup_grading_eq_top : ⨆ i, grading 𝒜 ℬ i = ⊤ := by
  apply Submodule.map_injective_of_injective (f := toTensorProduct.toLinearMap)
    toTensorProduct_injective
  simp only [Submodule.map_iSup, map_grading, Submodule.map_top]
  ext x
  refine ⟨fun hx ↦ ⟨⟨⟨x, hx⟩⟩, rfl⟩, ?_⟩
  rintro ⟨⟨⟨y, hy⟩⟩, rfl⟩
  exact hy

end Semiring

section CommSemiring

variable {ι R A B : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [CommSemiring B] [Algebra R B] {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B}
  [AddMonoid ι] [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ]

instance instCommSemiring : CommSemiring (Segre 𝒜 ℬ) :=
  { instSemiring with
    mul_comm := fun x y ↦ toSubalgebra_injective (mul_comm x.1 y.1) }

end CommSemiring

section Ring

variable {ι R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B} [AddMonoid ι]
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ]

instance instNeg : Neg (Segre 𝒜 ℬ) := ⟨fun x ↦ ⟨-x.1⟩⟩
instance instSub : Sub (Segre 𝒜 ℬ) := ⟨fun x y ↦ ⟨x.1 - y.1⟩⟩
instance instIntCast : IntCast (Segre 𝒜 ℬ) := ⟨fun n ↦ ⟨n⟩⟩

instance instRing : Ring (Segre 𝒜 ℬ) :=
  { instSemiring with
    neg := Neg.neg
    sub := Sub.sub
    zsmul := fun n x ↦ n • x
    intCast := Int.cast
    sub_eq_add_neg := fun x y ↦ toSubalgebra_injective (sub_eq_add_neg x.1 y.1)
    zsmul_zero' := fun x ↦ toSubalgebra_injective <| Subtype.ext (zero_smul ℤ x.1.1)
    zsmul_succ' := fun n x ↦
      toSubalgebra_injective <| Subtype.ext (SubNegMonoid.zsmul_succ' n x.1.1)
    zsmul_neg' := fun n x ↦
      toSubalgebra_injective <| Subtype.ext (SubNegMonoid.zsmul_neg' n x.1.1)
    neg_add_cancel := fun x ↦ toSubalgebra_injective (neg_add_cancel x.1)
    intCast_ofNat := fun n ↦ toSubalgebra_injective (Int.cast_natCast n)
    intCast_negSucc := fun n ↦ toSubalgebra_injective (Ring.intCast_negSucc n) }

end Ring

section CommRing

variable {ι R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B} [AddMonoid ι]
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ]

instance instCommRing : CommRing (Segre 𝒜 ℬ) :=
  { instRing with
    mul_comm := fun x y ↦ toSubalgebra_injective (mul_comm x.1 y.1) }

-- Verify there is no diamond between the semiring and commutative-ring hierarchies.
example : (instCommRing : CommRing (Segre 𝒜 ℬ)).toSemiring = instSemiring := by
  with_reducible_and_instances rfl

example : (instCommRing : CommRing (Segre 𝒜 ℬ)).toCommSemiring = instCommSemiring := by
  with_reducible_and_instances rfl

end CommRing

section GradedAlgebra

variable {ι R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
  [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The inclusion `𝒜 i ⊗[R] ℬ i →ₗ[R] A ⊗[R] B` is split-injective when `𝒜` and `ℬ` decompose
`A` and `B`. -/
theorem mapIncl_grade_injective (i : ι) :
    Function.Injective (TensorProduct.mapIncl (𝒜 i) (ℬ i)) :=
  LinearMap.injective_of_comp_eq_id _
    (TensorProduct.map (component R ι (fun i ↦ 𝒜 i) i ∘ₗ decomposeLinearEquiv 𝒜)
      (component R ι (fun j ↦ ℬ j) i ∘ₗ decomposeLinearEquiv ℬ)) (by ext; simp)

/-- Auxiliary `R`-linear map `𝒜 i ⊗[R] ℬ i →ₗ[R] Segre.grading 𝒜 ℬ i`. -/
private def gradingLinearMap (i : ι) : 𝒜 i ⊗[R] ℬ i →ₗ[R] grading 𝒜 ℬ i :=
  ((equivSubalgebra (𝒜 := 𝒜) (ℬ := ℬ)).symm.toLinearMap ∘ₗ
    (TensorProduct.mapIncl (𝒜 i) (ℬ i)).codRestrict
      ((segreSubalgebra 𝒜 ℬ).toSubmodule.comap LinearMap.id)
      (fun z ↦ by
        induction z using TensorProduct.inductionOn with
        | tmul a b => exact tmul_mem_segreSubalgebra a.2 b.2
        | add x y hx hy => rw [map_add]; exact add_mem hx hy)).codRestrict
    (grading 𝒜 ℬ i) fun z ↦ by
      induction z using TensorProduct.inductionOn with
      | tmul a b => exact tmul_mem_grading a.2 b.2
      | add x y hx hy => rw [map_add]; exact add_mem hx hy

private theorem toTensorProduct_gradingLinearMap (i : ι) (z : 𝒜 i ⊗[R] ℬ i) :
    toTensorProduct (gradingLinearMap 𝒜 ℬ i z : Segre 𝒜 ℬ) =
      TensorProduct.mapIncl (𝒜 i) (ℬ i) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp [map_add, hx, hy]

/-- The canonical `R`-linear equivalence `𝒜 i ⊗[R] ℬ i ≃ₗ[R] Segre.grading 𝒜 ℬ i`. -/
noncomputable def gradingEquiv (i : ι) : 𝒜 i ⊗[R] ℬ i ≃ₗ[R] grading 𝒜 ℬ i :=
  LinearEquiv.ofBijective (gradingLinearMap 𝒜 ℬ i)
    ⟨fun z₁ z₂ h ↦ mapIncl_grade_injective 𝒜 ℬ i <|
        (toTensorProduct_gradingLinearMap 𝒜 ℬ i z₁).symm.trans
          ((congrArg (fun w : grading 𝒜 ℬ i ↦ toTensorProduct (w : Segre 𝒜 ℬ)) h).trans
            (toTensorProduct_gradingLinearMap 𝒜 ℬ i z₂)),
      fun ⟨x, hx⟩ ↦ by
        obtain ⟨z, hz⟩ :
            toTensorProduct x ∈ LinearMap.range (TensorProduct.mapIncl (𝒜 i) (ℬ i)) := by
          rwa [TensorProduct.range_mapIncl]
        exact ⟨z, Subtype.ext <| ext_toTensorProduct <|
          (toTensorProduct_gradingLinearMap 𝒜 ℬ i z).trans hz⟩⟩

@[simp]
theorem toTensorProduct_gradingEquiv_apply (i : ι) (z : 𝒜 i ⊗[R] ℬ i) :
    toTensorProduct (gradingEquiv 𝒜 ℬ i z : Segre 𝒜 ℬ) =
      TensorProduct.mapIncl (𝒜 i) (ℬ i) z :=
  toTensorProduct_gradingLinearMap 𝒜 ℬ i z

@[simp]
theorem coe_gradingEquiv_tmul (i : ι) (a : 𝒜 i) (b : ℬ i) :
    (gradingEquiv 𝒜 ℬ i (a ⊗ₜ[R] b) : Segre 𝒜 ℬ) = tmul a.2 b.2 :=
  -- `(rfl)`, not `rfl`: `gradingEquiv` is not `@[expose]`d.
  (rfl)

/-- Each graded piece `Segre.grading 𝒜 ℬ i` is finite over `R` when `𝒜 i` and `ℬ i` are. -/
instance {i : ι} [Module.Finite R (𝒜 i)] [Module.Finite R (ℬ i)] :
    Module.Finite R (grading 𝒜 ℬ i) :=
  Module.Finite.equiv (gradingEquiv 𝒜 ℬ i)

/-- **The Segre product is internally graded**: `Segre 𝒜 ℬ` is the internal direct sum of the
pieces `Segre.grading 𝒜 ℬ i`. -/
theorem isInternal_grading : IsInternal (grading 𝒜 ℬ) := by
  let C : ι × ι → Submodule R (A ⊗[R] B) :=
    fun p ↦ Submodule.map₂ (TensorProduct.mk R A B) (𝒜 p.1) (ℬ p.2)
  have hC : IsInternal C :=
    DirectSum.IsInternal.tensorProduct 𝒜 ℬ (Decomposition.isInternal 𝒜)
      (Decomposition.isInternal ℬ)
  let toC (i : ι) : grading 𝒜 ℬ i →+ C (i, i) :=
    { toFun := fun x ↦ ⟨toTensorProduct (x : Segre 𝒜 ℬ), x.2⟩
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp }
  let emb : (⨁ i, grading 𝒜 ℬ i) →+ ⨁ p, C p :=
    DirectSum.toAddMonoid fun i ↦ (DirectSum.of (fun p ↦ C p) (i, i)).comp (toC i)
  have hcoe (y : ⨁ i, grading 𝒜 ℬ i) :
      DirectSum.coeAddMonoidHom C (emb y) =
        toTensorProduct (DirectSum.coeAddMonoidHom (grading 𝒜 ℬ) y) := by
    induction y using DirectSum.induction_on with
    | zero => simp [emb]
    | of i x => simp [emb, toC]
    | add y z hy hz => simp [map_add, hy, hz]
  refine ⟨fun y z h ↦ DirectSum.ext fun i ↦ Subtype.ext <| ext_toTensorProduct ?_, fun x ↦ ?_⟩
  · have hemb : emb y = emb z :=
      hC.1 ((hcoe y).trans ((congrArg toTensorProduct h).trans (hcoe z).symm))
    have hi (w : ⨁ k, grading 𝒜 ℬ k) :
        ((emb w (i, i) : C (i, i)) : A ⊗[R] B) = toTensorProduct (w i : Segre 𝒜 ℬ) := by
      induction w using DirectSum.induction_on with
      | zero => simp [emb]
      | of j x =>
        simp only [emb, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
        obtain rfl | hji := eq_or_ne j i
        · simp [toC]
        · have hne : (j, j) ≠ (i, i) := fun hp ↦ hji (Prod.mk.inj hp).1
          rw [DirectSum.of_eq_of_ne _ _ _ hne.symm, DirectSum.of_eq_of_ne _ _ _ hji.symm]
          simp
      | add u v hu hv => simp [map_add, hu, hv]
    rw [← hi y, ← hi z, hemb]
  · obtain ⟨y, hy⟩ := LinearMap.range_eq_top.1
      (range_coeLinearMap.trans (iSup_grading_eq_top 𝒜 ℬ)) x
    exact ⟨y, hy⟩

/-- The graded pieces `Segre.grading 𝒜 ℬ i` are independent in `Segre 𝒜 ℬ`. -/
theorem iSupIndep_grading : iSupIndep (grading 𝒜 ℬ) :=
  (isInternal_grading 𝒜 ℬ).submodule_iSupIndep

/-- `Segre 𝒜 ℬ` is an `ι`-graded `R`-algebra with grading `Segre.grading 𝒜 ℬ`. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (grading 𝒜 ℬ) :=
  (isInternal_grading 𝒜 ℬ).gradedAlgebra

section Map

variable {A' B' : Type*} [Semiring A'] [Algebra R A'] [Semiring B'] [Algebra R B']
  {𝒜' : ι → Submodule R A'} {ℬ' : ι → Submodule R B'}
  [GradedAlgebra 𝒜'] [GradedAlgebra ℬ'] {𝒜 ℬ}

/-- Graded `R`-algebra homomorphisms `f : 𝒜 →ₐᵍ[R] 𝒜'` and `g : ℬ →ₐᵍ[R] ℬ'` induce a graded
`R`-algebra homomorphism `Segre.grading 𝒜 ℬ →ₐᵍ[R] Segre.grading 𝒜' ℬ'`. -/
noncomputable def map (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') :
    grading 𝒜 ℬ →ₐᵍ[R] grading 𝒜' ℬ' where
  toAlgHom := (equivSubalgebra (𝒜 := 𝒜') (ℬ := ℬ')).symm.toAlgHom.comp <|
    ((Algebra.TensorProduct.map f.toAlgHom g.toAlgHom).comp toTensorProduct).codRestrict
      (segreSubalgebra 𝒜' ℬ') fun ⟨⟨x, hx⟩⟩ ↦ by
        induction hx using Submodule.iSup_induction' with
        | mem i x hx =>
          have h : Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i) ≤
              (Submodule.map₂ (TensorProduct.mk R A' B') (𝒜' i) (ℬ' i)).comap
                (Algebra.TensorProduct.map f.toAlgHom g.toAlgHom).toLinearMap :=
            Submodule.map₂_le.2 fun a ha b hb ↦ by
              simpa using Submodule.apply_mem_map₂ (TensorProduct.mk R A' B')
                (f.map_mem ha) (g.map_mem hb)
          exact mem_segreSubalgebra_of_mem (h hx)
        | zero => simp
        | add x y _ _ hx hy => simpa using add_mem hx hy
  map_mem {i x} hx := by
    have h : Submodule.map₂ (TensorProduct.mk R A B) (𝒜 i) (ℬ i) ≤
        (Submodule.map₂ (TensorProduct.mk R A' B') (𝒜' i) (ℬ' i)).comap
          (Algebra.TensorProduct.map f.toAlgHom g.toAlgHom).toLinearMap :=
      Submodule.map₂_le.2 fun a ha b hb ↦ by
        simpa using Submodule.apply_mem_map₂ (TensorProduct.mk R A' B')
          (f.map_mem ha) (g.map_mem hb)
    exact h hx

@[simp]
theorem toTensorProduct_map_apply (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ') (x : Segre 𝒜 ℬ) :
    toTensorProduct (map f g x) =
      Algebra.TensorProduct.map f.toAlgHom g.toAlgHom (toTensorProduct x) :=
  -- `(rfl)`, not `rfl`: `map` is not `@[expose]`d.
  (rfl)

@[simp]
theorem map_tmul (f : 𝒜 →ₐᵍ[R] 𝒜') (g : ℬ →ₐᵍ[R] ℬ')
    {i : ι} {a : A} {b : B} (ha : a ∈ 𝒜 i) (hb : b ∈ ℬ i) :
    map f g (tmul ha hb) = tmul (f.map_mem ha) (g.map_mem hb) := by
  apply ext_toTensorProduct
  simp

end Map

end GradedAlgebra

end Segre

/-! ### Generation in degree one -/

section DegreeOne

variable {R A B M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [CommSemiring B] [Algebra R B] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The diagonal tensor product of `n`-th powers of two submodules is contained in the `n`-th power
of their diagonal tensor product. -/
theorem map₂_mk_pow_le (P : Submodule R A) (Q : Submodule R B) (n : ℕ) :
    Submodule.map₂ (TensorProduct.mk R A B) (P ^ n) (Q ^ n) ≤
      Submodule.map₂ (TensorProduct.mk R A B) P Q ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero, Submodule.map₂_le]
    intro a ha b hb
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨s, rfl⟩ := Submodule.mem_one.mp hb
    refine Submodule.mem_one.mpr ⟨r * s, ?_⟩
    simp only [TensorProduct.mk_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.TensorProduct.one_def, mul_smul, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    rw [smul_comm]
  | succ n ih =>
    rw [pow_succ, pow_succ, pow_succ, Submodule.map₂_le]
    intro a ha b hb
    refine Submodule.mul_induction_on ha (fun a₁ ha₁ a₂ ha₂ ↦ ?_) fun x₁ x₂ hx₁ hx₂ ↦ by
      simpa only [TensorProduct.mk_apply, TensorProduct.add_tmul] using add_mem hx₁ hx₂
    refine Submodule.mul_induction_on hb (fun b₁ hb₁ b₂ hb₂ ↦ ?_) fun y₁ y₂ hy₁ hy₂ ↦ by
      simpa only [TensorProduct.mk_apply, TensorProduct.tmul_add] using add_mem hy₁ hy₂
    rw [TensorProduct.mk_apply, ← Algebra.TensorProduct.tmul_mul_tmul]
    exact Submodule.mul_mem_mul (ih (Submodule.apply_mem_map₂ _ ha₁ hb₁))
      (Submodule.apply_mem_map₂ _ ha₂ hb₂)

/-- If an `ℕ`-graded `R`-algebra `𝒜` is generated in degree `n` by a submodule `P ≤ 𝒜 1` over `R`
(meaning `𝒜 n ⊆ R[P]`), then in fact `𝒜 n ≤ P ^ n` (even when `𝒜 0` is larger than `R`). -/
theorem grade_le_pow_of_subset_adjoin {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]
    {P : Submodule R A} (hP : P ≤ 𝒜 1) {n : ℕ}
    (hn : (𝒜 n : Set A) ⊆ Algebra.adjoin R (P : Set A)) :
    𝒜 n ≤ P ^ n := by
  have hPpow (m : ℕ) : P ^ m ≤ 𝒜 m := by
    induction m with
    | zero =>
      rw [pow_zero, Submodule.one_le]
      exact SetLike.GradedOne.one_mem
    | succ m ih =>
      rw [pow_succ, Submodule.mul_le]
      intro x hx y hy
      exact SetLike.mul_mem_graded (ih hx) (hP hy)
  let S : Subalgebra R A := Submodule.toSubalgebra (⨆ m : ℕ, P ^ m)
    (Submodule.mem_iSup_of_mem 0 (pow_zero P ▸ Submodule.one_le.mp le_rfl))
    fun {x y} hx hy ↦ by
      induction hx using Submodule.iSup_induction' with
      | mem i x hx =>
        induction hy using Submodule.iSup_induction' with
        | mem j y hy =>
          exact Submodule.mem_iSup_of_mem (i + j) (pow_add P i j ▸ Submodule.mul_mem_mul hx hy)
        | zero => simp
        | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | zero => simp
      | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  have hadj : Algebra.adjoin R (P : Set A) ≤ S :=
    Algebra.adjoin_le fun x hx ↦ Submodule.mem_iSup_of_mem 1 ((pow_one P).symm ▸ hx)
  intro x hx
  have hxS : x ∈ ⨆ m : ℕ, P ^ m := hadj (hn hx)
  have hproj : ∀ y ∈ ⨆ m : ℕ, P ^ m, (decompose 𝒜 y n : A) ∈ P ^ n := fun y hy ↦ by
    induction hy using Submodule.iSup_induction' with
    | mem m y hy =>
      obtain rfl | hmn := eq_or_ne m n
      · rwa [decompose_of_mem_same 𝒜 (hPpow m hy)]
      · rw [decompose_of_mem_ne 𝒜 (hPpow m hy) hmn]
        exact zero_mem _
    | zero => simp
    | add y z _ _ hy hz =>
      rw [decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem hy hz
  simpa only [decompose_of_mem_same 𝒜 hx] using hproj x hxS

namespace Segre

variable {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B}

/-- The `R`-linear map `M ⊗[R] N →ₗ[R] Segre.grading 𝒜 ℬ 1` induced by linear maps `f : M →ₗ[R] 𝒜 1`
and `g : N →ₗ[R] ℬ 1`, sending `m ⊗ₜ n` to `(f m) ⊗ₜ (g n)`. -/
def linearMap [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ]
    (f : M →ₗ[R] 𝒜 1) (g : N →ₗ[R] ℬ 1) : M ⊗[R] N →ₗ[R] grading 𝒜 ℬ 1 :=
  ((equivSubalgebra (𝒜 := 𝒜) (ℬ := ℬ)).symm.toLinearMap ∘ₗ
    (TensorProduct.map ((𝒜 1).subtype ∘ₗ f) ((ℬ 1).subtype ∘ₗ g)).codRestrict
      ((segreSubalgebra 𝒜 ℬ).toSubmodule.comap LinearMap.id)
      (fun z ↦ by
        induction z using TensorProduct.inductionOn with
        | tmul m n => exact tmul_mem_segreSubalgebra (f m).2 (g n).2
        | add x y hx hy => rw [map_add]; exact add_mem hx hy)).codRestrict
    (grading 𝒜 ℬ 1) fun z ↦ by
      induction z using TensorProduct.inductionOn with
      | tmul m n => exact tmul_mem_grading (f m).2 (g n).2
      | add x y hx hy => rw [map_add]; exact add_mem hx hy

@[simp]
theorem coe_linearMap_tmul [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ]
    (f : M →ₗ[R] 𝒜 1) (g : N →ₗ[R] ℬ 1) (m : M) (n : N) :
    (linearMap f g (m ⊗ₜ[R] n) : Segre 𝒜 ℬ) = tmul (f m).2 (g n).2 :=
  -- `(rfl)`, not `rfl`: `linearMap` is not `@[expose]`d.
  (rfl)

private theorem pow_subset_adjoin {C : Type*} [CommSemiring C] [Algebra R C]
    (W : Submodule R C) (k : ℕ) :
    ((W ^ k : Submodule R C) : Set C) ⊆ Algebra.adjoin R (W : Set C) := by
  induction k with
  | zero =>
    rintro y hy
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (pow_zero W ▸ hy)
    exact hr ▸ Subalgebra.algebraMap_mem _ r
  | succ k ih =>
    rw [pow_succ]
    intro y hy
    refine Submodule.mul_induction_on hy (fun u hu v hv ↦ ?_) (fun _ _ hu hv ↦ add_mem hu hv)
    exact mul_mem (ih hu) (Algebra.subset_adjoin hv)

/-- **Generation of the Segre product in degree one**: if `f : M →ₗ[R] 𝒜 1` and
`g : N →ₗ[R] ℬ 1` generate `𝒜` and `ℬ` in positive degrees over `R`, then `Segre.linearMap f g`
generates `Segre.grading 𝒜 ℬ` in positive degrees over `R`. -/
theorem grading_subset_adjoin_range_linearMap [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    {f : M →ₗ[R] 𝒜 1} {g : N →ₗ[R] ℬ 1}
    (hf : ∀ i, 0 < i → (𝒜 i : Set A) ⊆ Algebra.adjoin R (Set.range fun m ↦ (f m : A)))
    (hg : ∀ i, 0 < i → (ℬ i : Set B) ⊆ Algebra.adjoin R (Set.range fun n ↦ (g n : B))) :
    ∀ i, 0 < i → (grading 𝒜 ℬ i : Set (Segre 𝒜 ℬ)) ⊆
      Algebra.adjoin R (Set.range fun z ↦ (linearMap f g z : Segre 𝒜 ℬ)) := by
  let P : Submodule R A := LinearMap.range ((𝒜 1).subtype ∘ₗ f)
  let Q : Submodule R B := LinearMap.range ((ℬ 1).subtype ∘ₗ g)
  let W : Submodule R (Segre 𝒜 ℬ) :=
    LinearMap.range ((grading 𝒜 ℬ 1).subtype ∘ₗ linearMap f g)
  have hPrange : (P : Set A) = Set.range fun m ↦ (f m : A) := by ext x; simp [P]
  have hQrange : (Q : Set B) = Set.range fun n ↦ (g n : B) := by ext x; simp [Q]
  have hWrange : (W : Set (Segre 𝒜 ℬ)) =
      Set.range fun z ↦ (linearMap f g z : Segre 𝒜 ℬ) := by ext x; simp [W]
  have hP1 : P ≤ 𝒜 1 := by rintro _ ⟨m, rfl⟩; exact (f m).2
  have hQ1 : Q ≤ ℬ 1 := by rintro _ ⟨n, rfl⟩; exact (g n).2
  have hPQW : Submodule.map₂ (TensorProduct.mk R A B) P Q ≤
      W.map (toTensorProduct (𝒜 := 𝒜) (ℬ := ℬ)).toLinearMap := by
    rw [Submodule.map₂_le]
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨linearMap f g (m ⊗ₜ[R] n), ⟨m ⊗ₜ[R] n, rfl⟩, rfl⟩
  intro i hi x hx
  have hPi : 𝒜 i ≤ P ^ i := grade_le_pow_of_subset_adjoin hP1 (hPrange ▸ hf i hi)
  have hQi : ℬ i ≤ Q ^ i := grade_le_pow_of_subset_adjoin hQ1 (hQrange ▸ hg i hi)
  have hmap : toTensorProduct x ∈
      (W ^ i).map (toTensorProduct (𝒜 := 𝒜) (ℬ := ℬ)).toLinearMap := by
    have hval : (W ^ i).map (toTensorProduct (𝒜 := 𝒜) (ℬ := ℬ)).toLinearMap =
        (W.map (toTensorProduct (𝒜 := 𝒜) (ℬ := ℬ)).toLinearMap) ^ i :=
      Submodule.map_pow (f := toTensorProduct (𝒜 := 𝒜) (ℬ := ℬ)) W i
    exact hval ▸ pow_le_pow_left' hPQW i (map₂_mk_pow_le P Q i (Submodule.map₂_le_map₂ hPi hQi hx))
  obtain ⟨y, hy, hyx⟩ := hmap
  exact hWrange ▸ pow_subset_adjoin W i (ext_toTensorProduct hyx ▸ hy)

end Segre

end DegreeOne

end TauCeti.GradedAlgebra
