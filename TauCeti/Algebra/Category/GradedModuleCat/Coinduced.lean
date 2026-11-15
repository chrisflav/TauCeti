/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian

/-!
# Coinduced graded modules and injective presentations

Let `𝒜 : ℤ → Submodule k A` be an internally graded `k`-algebra. For any `A`-module `M`, the
**coinduced graded module** `coinduced 𝒜 M` has underlying `k`-module `⨁ p : ℤ, M`, with degree-`p`
piece the `p`-th summand `M` and `A`-action sending `a ∈ 𝒜 q` and `m` in degree `p` to `a • m` in
degree `q + p`. Because `A` is internally graded, every element of `A` has finitely many nonzero
homogeneous components, so this action lands inside the direct sum rather than the direct product.
In Năstăsescu–Van Oystaeyen's terminology this is the graded part of `Hom_A(A, M) ≅ ∏_{p : ℤ} M`.

Summing the homogeneous coordinates defines an `A`-linear counit `coinduced 𝒜 M →ₗ[A] M`, and any
`A`-linear map `f : E →ₗ[A] M` from a graded module `E` lifts uniquely to a degree-zero map
`E ⟶ coinduced 𝒜 M` sending `e ∈ Eₚ` to `f e` in degree `p`. This exhibits `coinducedFunctor 𝒜`
as right adjoint to the faithful exact forgetful functor `toModuleCat`. Consequently coinduced
graded modules on injective `A`-modules are injective in `GradedModuleCat 𝒜`, and
`GradedModuleCat 𝒜` has enough injectives via `EnoughInjectives.of_adjunction`.

## Main definitions

* `TauCeti.GradedModuleCat.coinduced`: the coinduced graded `𝒜`-module on an `A`-module `M`.
* `TauCeti.GradedModuleCat.coinducedSingle`: the degree-`p` coordinate inclusion
  `M →+ coinduced 𝒜 M`.
* `TauCeti.GradedModuleCat.coinducedCounit`: the `A`-linear counit summing all coordinates.
* `TauCeti.GradedModuleCat.coinducedLift`: the graded lift of an `A`-linear map `E →ₗ[A] M`.
* `TauCeti.GradedModuleCat.coinducedHomEquiv`: the adjunction equivalence on morphisms.
* `TauCeti.GradedModuleCat.coinducedFunctor` and `TauCeti.GradedModuleCat.coinducedAdjunction`:
  the right adjoint to `toModuleCat`.

## Main results

* `TauCeti.GradedModuleCat.injective_coinducedFunctor_obj`: coinducing an injective `A`-module
  gives an injective graded `𝒜`-module.
* `TauCeti.GradedModuleCat.enoughInjectives`: `GradedModuleCat.{max uA v} 𝒜` has enough injectives.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  **1836**, Springer (2004), Sections 2.2 and 2.3.
-/

public section

noncomputable section

open CategoryTheory
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe v uk uA

section Carrier

/-- Copy of an `A`-module `M` carrying only the restricted `k`-module structure along
`algebraMap k A`, with a single `AddCommGroup` instance so `⨁ _ : ℤ, CoinducedPiece k A M`
synthesizes `AddCommGroup` and `Module k` without an `AddCommMonoid`/`AddCommGroup` diamond. -/
@[ext]
private structure CoinducedPiece (k : Type uk) (A : Type uA) (M : Type v) where
  /-- Underlying element of `M`. -/
  val : M

section Piece

variable {k : Type uk} {A : Type uA} {M : Type v}

private theorem CoinducedPiece.val_injective :
    Function.Injective (CoinducedPiece.val (k := k) (A := A) (M := M)) :=
  fun _ _ ↦ CoinducedPiece.ext

section Group

variable [AddCommGroup M]

private instance : Zero (CoinducedPiece k A M) := ⟨⟨0⟩⟩
private instance : Add (CoinducedPiece k A M) := ⟨fun x y ↦ ⟨x.val + y.val⟩⟩
private instance : Neg (CoinducedPiece k A M) := ⟨fun x ↦ ⟨-x.val⟩⟩
private instance : Sub (CoinducedPiece k A M) := ⟨fun x y ↦ ⟨x.val - y.val⟩⟩
private instance : SMul ℕ (CoinducedPiece k A M) := ⟨fun n x ↦ ⟨n • x.val⟩⟩
private instance : SMul ℤ (CoinducedPiece k A M) := ⟨fun n x ↦ ⟨n • x.val⟩⟩

@[simp] private theorem CoinducedPiece.val_zero : (0 : CoinducedPiece k A M).val = 0 := rfl
@[simp] private theorem CoinducedPiece.val_add (x y : CoinducedPiece k A M) :
    (x + y).val = x.val + y.val := rfl

private instance : AddCommGroup (CoinducedPiece k A M) :=
  CoinducedPiece.val_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Group

section Module

variable [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M] [Module A M]

private instance : SMul k (CoinducedPiece k A M) := ⟨fun r x ↦ ⟨algebraMap k A r • x.val⟩⟩

@[simp] private theorem CoinducedPiece.val_smul (r : k) (x : CoinducedPiece k A M) :
    (r • x).val = algebraMap k A r • x.val := rfl

private instance : Module k (CoinducedPiece k A M) where
  one_smul x := CoinducedPiece.ext <| by simp
  mul_smul r s x := CoinducedPiece.ext <| by simp [mul_smul]
  smul_zero r := CoinducedPiece.ext <| by simp
  smul_add r x y := CoinducedPiece.ext <| by simp [smul_add]
  add_smul r s x := CoinducedPiece.ext <| by simp [add_smul]
  zero_smul x := CoinducedPiece.ext <| by simp

private def CoinducedPiece.lsmul (a : A) : CoinducedPiece k A M →ₗ[k] CoinducedPiece k A M where
  toFun x := ⟨a • x.val⟩
  map_add' x y := CoinducedPiece.ext <| by simp [smul_add]
  map_smul' r x := CoinducedPiece.ext <| by
    simp only [CoinducedPiece.val_smul, RingHom.id_apply]
    rw [← mul_smul, ← Algebra.commutes, mul_smul]

@[simp] private theorem CoinducedPiece.val_lsmul (a : A) (x : CoinducedPiece k A M) :
    (CoinducedPiece.lsmul a x).val = a • x.val := rfl

private def CoinducedPiece.lsmulK :
    A →ₗ[k] CoinducedPiece k A M →ₗ[k] CoinducedPiece k A M where
  toFun := CoinducedPiece.lsmul
  map_add' a b := LinearMap.ext fun m ↦ CoinducedPiece.ext (add_smul a b m.val)
  map_smul' r a := LinearMap.ext fun m ↦ CoinducedPiece.ext <| by
    rw [RingHom.id_apply, LinearMap.smul_apply, CoinducedPiece.val_smul, CoinducedPiece.val_lsmul,
      CoinducedPiece.val_lsmul, Algebra.smul_def, mul_smul]

end Module

end Piece

/-- Carrier of the coinduced graded module on `M`. Wrapping the external direct sum of copies of
`CoinducedPiece k A M` avoids an action diamond with the coordinatewise `A`-module structure on a
direct sum. -/
@[ext]
private structure CoinducedCarrier (k : Type uk) (A : Type uA) (M : Type v) [AddCommGroup M] where
  /-- The finitely supported family of homogeneous coordinates in `M`. -/
  coords : ⨁ _ : ℤ, CoinducedPiece k A M

private theorem CoinducedCarrier.coords_injective {k : Type uk} {A : Type uA} {M : Type v}
    [AddCommGroup M] :
    Function.Injective (CoinducedCarrier.coords (k := k) (A := A) (M := M)) :=
  fun _ _ ↦ CoinducedCarrier.ext

section CarrierGroup

variable {k : Type uk} {A : Type uA} {M : Type v} [AddCommGroup M]

private instance : Zero (CoinducedCarrier k A M) := ⟨⟨0⟩⟩
private instance : Add (CoinducedCarrier k A M) := ⟨fun x y ↦ ⟨x.coords + y.coords⟩⟩
private instance : Neg (CoinducedCarrier k A M) := ⟨fun x ↦ ⟨-x.coords⟩⟩
private instance : Sub (CoinducedCarrier k A M) := ⟨fun x y ↦ ⟨x.coords - y.coords⟩⟩
private instance : SMul ℕ (CoinducedCarrier k A M) := ⟨fun n x ↦ ⟨n • x.coords⟩⟩
private instance : SMul ℤ (CoinducedCarrier k A M) := ⟨fun n x ↦ ⟨n • x.coords⟩⟩

@[simp] private theorem CoinducedCarrier.coords_zero : (0 : CoinducedCarrier k A M).coords = 0 :=
  rfl
@[simp] private theorem CoinducedCarrier.coords_add (x y : CoinducedCarrier k A M) :
    (x + y).coords = x.coords + y.coords := rfl

private instance : AddCommGroup (CoinducedCarrier k A M) :=
  CoinducedCarrier.coords_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end CarrierGroup

section CarrierModule

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {M : Type v} [AddCommGroup M] [Module A M]

private instance : SMul k (CoinducedCarrier k A M) := ⟨fun r x ↦ ⟨r • x.coords⟩⟩

@[simp] private theorem CoinducedCarrier.coords_smulK (r : k) (x : CoinducedCarrier k A M) :
    (r • x).coords = r • x.coords := rfl

private instance : Module k (CoinducedCarrier k A M) :=
  CoinducedCarrier.coords_injective.module k ⟨⟨CoinducedCarrier.coords, rfl⟩, fun _ _ ↦ rfl⟩
    fun _ _ ↦ rfl

private def CoinducedCarrier.coordsLinearEquiv :
    CoinducedCarrier k A M ≃ₗ[k] ⨁ _ : ℤ, CoinducedPiece k A M where
  toFun := CoinducedCarrier.coords
  invFun := CoinducedCarrier.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem CoinducedCarrier.coordsLinearEquiv_apply (x : CoinducedCarrier k A M) :
    CoinducedCarrier.coordsLinearEquiv x = x.coords :=
  rfl

end CarrierModule

end Carrier

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [DirectSum.Decomposition 𝒜] [SetLike.GradedMonoid 𝒜]

section Action

variable {M : Type v} [AddCommGroup M] [Module A M]

private def homogPieceSmul (q p : ℤ) :
    𝒜 q →ₗ[k] CoinducedPiece k A M →ₗ[k] ⨁ _ : ℤ, CoinducedPiece k A M :=
  LinearMap.mk₂ k
    (fun a m ↦ DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducedPiece k A M) (q + p)
      (CoinducedPiece.lsmul (a : A) m))
    (fun a₁ a₂ m ↦ by
      rw [Submodule.coe_add, ← map_add]
      exact congrArg _ (CoinducedPiece.ext (add_smul _ _ m.val)))
    (fun r a m ↦ by
      rw [Submodule.coe_smul, ← map_smul]
      refine congrArg _ (CoinducedPiece.ext ?_)
      simp only [CoinducedPiece.val_lsmul, CoinducedPiece.val_smul]
      rw [Algebra.smul_def, mul_smul])
    (fun _ _ _ ↦ by simp [map_add])
    (fun _ _ _ ↦ by simp [map_smul])

private def homogSmul (q : ℤ) :
    𝒜 q →ₗ[k] (⨁ _ : ℤ, CoinducedPiece k A M) →ₗ[k] ⨁ _ : ℤ, CoinducedPiece k A M :=
  (DirectSum.toModule k ℤ (𝒜 q →ₗ[k] ⨁ _ : ℤ, CoinducedPiece k A M)
    fun p ↦ (homogPieceSmul 𝒜 q p).flip).flip

private def smulBilinear :
    A →ₗ[k] (⨁ _ : ℤ, CoinducedPiece k A M) →ₗ[k] ⨁ _ : ℤ, CoinducedPiece k A M :=
  DirectSum.toModule k ℤ _ (homogSmul 𝒜) ∘ₗ (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

omit [SetLike.GradedMonoid 𝒜] in
private theorem smulBilinear_lof_of_mem {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) (p : ℤ)
    (m : CoinducedPiece k A M) :
    smulBilinear 𝒜 a (DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducedPiece k A M) p m) =
      DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducedPiece k A M) (q + p)
        (CoinducedPiece.lsmul a m) := by
  simp only [smulBilinear, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [DirectSum.decomposeLinearEquiv_apply_coe 𝒜 q ⟨a, ha⟩, DirectSum.toModule_lof]
  simp [homogSmul, homogPieceSmul]

private theorem smulBilinear_one :
    smulBilinear 𝒜 (M := M) (1 : A) = LinearMap.id := by
  apply DirectSum.linearMap_ext k
  intro p
  refine LinearMap.ext fun m ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [smulBilinear_lof_of_mem 𝒜 (SetLike.one_mem_graded 𝒜) p m, zero_add]
  exact congrArg (DirectSum.lof k ℤ _ p) (CoinducedPiece.ext (one_smul A m.val))

private theorem smulBilinear_mul (a b : A) :
    smulBilinear 𝒜 (M := M) (a * b) = (smulBilinear 𝒜 a).comp (smulBilinear 𝒜 b) := by
  have hExt : (LinearMap.mk₂ k (fun x y : A ↦ smulBilinear 𝒜 (M := M) (x * y))
      (fun _ _ _ ↦ by simp [add_mul]) (fun _ _ _ ↦ by simp)
      (fun _ _ _ ↦ by simp [mul_add]) (fun _ _ _ ↦ by simp)) =
    LinearMap.mk₂ k (fun x y : A ↦ (smulBilinear 𝒜 (M := M) x).comp (smulBilinear 𝒜 y))
      (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
      (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp) := by
    apply (InternalGrading.ofDecomposition 𝒜).linearMap_ext
    intro r a' ha'
    apply (InternalGrading.ofDecomposition 𝒜).linearMap_ext
    intro q b' hb'
    apply DirectSum.linearMap_ext k
    intro p
    refine LinearMap.ext fun m ↦ ?_
    rw [InternalGrading.ofDecomposition_piece] at ha' hb'
    simp only [LinearMap.mk₂_apply, LinearMap.comp_apply]
    rw [smulBilinear_lof_of_mem 𝒜 (SetLike.mul_mem_graded ha' hb') p m,
      smulBilinear_lof_of_mem 𝒜 hb' p m, smulBilinear_lof_of_mem 𝒜 ha' (q + p), add_assoc]
    exact congrArg (DirectSum.lof k ℤ _ (r + (q + p)))
      (CoinducedPiece.ext (mul_smul a' b' m.val))
  exact LinearMap.congr_fun (LinearMap.congr_fun hExt a) b

private def counitLinear :
    (⨁ _ : ℤ, CoinducedPiece k A M) →ₗ[k] CoinducedPiece k A M :=
  DirectSum.toModule k ℤ (CoinducedPiece k A M) fun _ ↦ LinearMap.id

omit [SetLike.GradedMonoid 𝒜] in
private theorem counitLinear_smulBilinear (a : A) (x : ⨁ _ : ℤ, CoinducedPiece k A M) :
    counitLinear (smulBilinear 𝒜 a x) = CoinducedPiece.lsmul a (counitLinear x) := by
  have hExt : ({ toFun := fun b : A ↦ counitLinear (M := M) ∘ₗ smulBilinear 𝒜 b
                 map_add' := fun _ _ ↦ by ext; simp
                 map_smul' := fun _ _ ↦ by ext; simp } :
        A →ₗ[k] (⨁ _ : ℤ, CoinducedPiece k A M) →ₗ[k] CoinducedPiece k A M) =
      { toFun := fun b : A ↦ CoinducedPiece.lsmulK b ∘ₗ counitLinear (M := M)
        map_add' := fun _ _ ↦ by ext; simp [map_add]
        map_smul' := fun _ _ ↦ by ext; simp [map_smul] } := by
    apply (InternalGrading.ofDecomposition 𝒜).linearMap_ext
    intro q b hb
    apply DirectSum.linearMap_ext k
    intro p
    refine LinearMap.ext fun m ↦ ?_
    rw [InternalGrading.ofDecomposition_piece] at hb
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rw [smulBilinear_lof_of_mem 𝒜 hb p m]
    simp [counitLinear, CoinducedPiece.lsmulK]
  exact LinearMap.congr_fun (LinearMap.congr_fun hExt a) x

end Action

@[instance_reducible]
private def coinducedModule (M : Type v) [AddCommGroup M] [Module A M] :
    Module A (CoinducedCarrier k A M) where
  smul a x := ⟨smulBilinear 𝒜 a x.coords⟩
  one_smul x := CoinducedCarrier.ext <| LinearMap.congr_fun (smulBilinear_one 𝒜) x.coords
  mul_smul a b x := CoinducedCarrier.ext <| LinearMap.congr_fun (smulBilinear_mul 𝒜 a b) x.coords
  smul_zero a := CoinducedCarrier.ext <| (smulBilinear 𝒜 a).map_zero
  smul_add a x y := CoinducedCarrier.ext <| (smulBilinear 𝒜 a).map_add x.coords y.coords
  add_smul a b x := CoinducedCarrier.ext <|
    (LinearMap.congr_fun ((smulBilinear 𝒜).map_add a b) x.coords).trans
      (LinearMap.add_apply _ _ _)
  zero_smul x := CoinducedCarrier.ext <|
    LinearMap.congr_fun (smulBilinear 𝒜).map_zero x.coords

private abbrev coinducedGrading (M : Type v) [AddCommGroup M] [Module A M] :
    InternalGrading k (CoinducedCarrier k A M) ℤ :=
  (InternalGrading.ofDecomposition
    (DirectSum.summand k fun _ : ℤ ↦ CoinducedPiece k A M)).map
    (CoinducedCarrier.coordsLinearEquiv (k := k) (A := A) (M := M)).symm

/-- The **coinduced graded `𝒜`-module** on an `A`-module `M`, with degree-`p` piece a copy of `M`
and homogeneous `A`-action shifting degrees. -/
def coinduced (M : Type v) [AddCommGroup M] [Module A M] : GradedModuleCat.{v} 𝒜 where
  carrier := CoinducedCarrier k A M
  isModule := coinducedModule 𝒜 M
  isScalarTower := by
    let := coinducedModule 𝒜 M
    exact ⟨fun r a x ↦ CoinducedCarrier.ext <|
      (LinearMap.congr_fun ((smulBilinear 𝒜).map_smul r a) x.coords).trans
        (LinearMap.smul_apply _ _ _)⟩
  grading := coinducedGrading (k := k) (A := A) M
  gradedSMul := by
    let := coinducedModule 𝒜 M
    refine ⟨fun ⦃q p⦄ a x ha hx ↦ ?_⟩
    rw [InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
      InternalGrading.ofDecomposition_piece, DirectSum.mem_summand] at hx ⊢
    obtain ⟨m, hm⟩ := hx
    rw [CoinducedCarrier.coordsLinearEquiv_apply] at hm
    refine ⟨CoinducedPiece.lsmul a m, ?_⟩
    rw [CoinducedCarrier.coordsLinearEquiv_apply, vadd_eq_add]
    dsimp only [HSMul.hSMul, SMul.smul, coinducedModule]
    rw [← hm, ← DirectSum.lof_eq_of (R := k), ← DirectSum.lof_eq_of (R := k),
      smulBilinear_lof_of_mem 𝒜 ha p m]

section CoinducedAPI

attribute [local implicit_reducible] coinduced

variable {𝒜} {M : Type v} [AddCommGroup M] [Module A M]

/-- Place an element of `M` into degree `p` of `coinduced 𝒜 M`. -/
def coinducedSingle (p : ℤ) : M →+ coinduced 𝒜 M where
  toFun m := ⟨DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducedPiece k A M) p ⟨m⟩⟩
  map_zero' := CoinducedCarrier.ext <|
    (DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducedPiece k A M) p).map_zero
  map_add' x y := CoinducedCarrier.ext <|
    (DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducedPiece k A M) p).map_add ⟨x⟩ ⟨y⟩

/-- `coinducedSingle p m` is homogeneous of degree `p`. -/
theorem coinducedSingle_mem_piece (p : ℤ) (m : M) :
    coinducedSingle p m ∈ (coinduced 𝒜 M).grading.piece p := by
  dsimp only [coinduced]
  rw [InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
    InternalGrading.ofDecomposition_piece]
  exact DirectSum.lof_mem_summand (R := k) (M := fun _ : ℤ ↦ CoinducedPiece k A M) p ⟨m⟩

/-- The degree-`p` piece of `coinduced 𝒜 M` consists of the elements `coinducedSingle p m`. -/
theorem mem_coinduced_piece_iff (p : ℤ) (x : coinduced 𝒜 M) :
    x ∈ (coinduced 𝒜 M).grading.piece p ↔ ∃ m : M, coinducedSingle (𝒜 := 𝒜) p m = x := by
  dsimp only [coinduced]
  rw [InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
    InternalGrading.ofDecomposition_piece, DirectSum.mem_summand]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m.val, CoinducedCarrier.ext ?_⟩
    simpa [coinducedSingle, DirectSum.lof_eq_of] using
      hm.trans (CoinducedCarrier.coordsLinearEquiv_apply x)
  · rintro ⟨m, rfl⟩
    exact ⟨⟨m⟩, by simp [coinducedSingle, DirectSum.lof_eq_of]⟩

/-- A homogeneous scalar `a ∈ 𝒜 q` shifts `coinducedSingle p m` to
`coinducedSingle (q + p) (a • m)`. -/
theorem smul_coinducedSingle {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) (p : ℤ) (m : M) :
    a • coinducedSingle (𝒜 := 𝒜) p m = coinducedSingle (q + p) (a • m) :=
  CoinducedCarrier.ext (smulBilinear_lof_of_mem 𝒜 ha p ⟨m⟩)

variable (𝒜 M) in
/-- The `A`-linear counit `coinduced 𝒜 M →ₗ[A] M` summing all homogeneous coordinates. -/
def coinducedCounit : coinduced 𝒜 M →ₗ[A] M where
  toFun x := (counitLinear (CoinducedCarrier.coords x)).val
  map_add' x y := by
    dsimp only [coinduced] at x y
    rw [CoinducedCarrier.coords_add, map_add]
    rfl
  map_smul' a x := by
    dsimp only [coinduced] at x
    exact congrArg CoinducedPiece.val (counitLinear_smulBilinear 𝒜 a x.coords)

/-- Evaluating `coinducedCounit` on a single homogeneous coordinate recovers the element. -/
@[simp]
theorem coinducedCounit_single (p : ℤ) (m : M) :
    coinducedCounit 𝒜 M (coinducedSingle p m) = m := by
  simp [coinducedCounit, coinducedSingle, counitLinear]

private def coinducedLiftLinear {E : GradedModuleCat.{v} 𝒜} (f : E →ₗ[A] M) :
    E →ₗ[k] CoinducedCarrier k A M :=
  (CoinducedCarrier.coordsLinearEquiv (k := k) (A := A) (M := M)).symm.toLinearMap ∘ₗ
    DirectSum.toModule k ℤ (⨁ _ : ℤ, CoinducedPiece k A M)
      (fun p ↦ DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducedPiece k A M) p ∘ₗ
        { toFun := fun e ↦ ⟨f e.1⟩
          map_add' := fun x y ↦ CoinducedPiece.ext (by simp)
          map_smul' := fun r x ↦ CoinducedPiece.ext (by
            dsimp only [CoinducedPiece.val_smul, RingHom.id_apply]
            rw [Submodule.coe_smul, ← algebraMap_smul A r x.1, f.map_smul]) }) ∘ₗ
    (DirectSum.decomposeLinearEquiv E.grading.piece).toLinearMap

omit [DirectSum.Decomposition 𝒜] [SetLike.GradedMonoid 𝒜] in
private theorem coinducedLiftLinear_apply_of_mem {E : GradedModuleCat.{v} 𝒜} (f : E →ₗ[A] M)
    {p : ℤ} {e : E} (he : e ∈ E.grading.piece p) :
    coinducedLiftLinear f e = ⟨DirectSum.lof k ℤ (fun _ : ℤ ↦ CoinducedPiece k A M) p ⟨f e⟩⟩ := by
  unfold coinducedLiftLinear
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [DirectSum.decomposeLinearEquiv_apply_coe E.grading.piece p ⟨e, he⟩, DirectSum.toModule_lof]
  rfl

private def coinducedLiftLinearK {E : GradedModuleCat.{v} 𝒜} (f : E →ₗ[A] M) :
    E →ₗ[k] coinduced 𝒜 M where
  toFun e := coinducedLiftLinear f e
  map_add' x y := (coinducedLiftLinear f).map_add x y
  map_smul' c x := (coinducedLiftLinear f).map_smul c x

private theorem coinducedLiftLinearK_apply_of_mem {E : GradedModuleCat.{v} 𝒜} (f : E →ₗ[A] M)
    {p : ℤ} {e : E} (he : e ∈ E.grading.piece p) :
    coinducedLiftLinearK (𝒜 := 𝒜) f e = coinducedSingle (𝒜 := 𝒜) p (f e) :=
  coinducedLiftLinear_apply_of_mem f he

/-- Lift an `A`-linear map `f : E →ₗ[A] M` out of a graded module `E` to a graded morphism
`E ⟶ coinduced 𝒜 M` sending `e ∈ Eₚ` to `coinducedSingle p (f e)`. -/
def coinducedLift {E : GradedModuleCat.{v} 𝒜} (f : E →ₗ[A] M) : E ⟶ coinduced 𝒜 M := by
  refine ofHom
    { toFun := coinducedLiftLinearK (𝒜 := 𝒜) f
      map_add' := (coinducedLiftLinearK (𝒜 := 𝒜) f).map_add
      map_smul' := fun a e ↦ ?_ }
    (LinearMap.isHomogeneous_def.mpr fun p e he ↦ by
      simpa [coinducedLiftLinearK_apply_of_mem f he] using
        coinducedSingle_mem_piece (𝒜 := 𝒜) p (f e))
  have hbil : LinearMap.mk₂ k (fun x : A ↦ fun y : E ↦ coinducedLiftLinearK (𝒜 := 𝒜) f (x • y))
      (fun _ _ _ ↦ by simp [add_smul]) (fun _ _ _ ↦ by simp [smul_assoc])
      (fun _ _ _ ↦ by simp [smul_add])
      (fun c x y ↦ by rw [smul_comm x c y, LinearMap.map_smul]) =
    LinearMap.mk₂ k (fun x : A ↦ fun y : E ↦ x • coinducedLiftLinearK (𝒜 := 𝒜) f y)
      (fun _ _ _ ↦ by simp [add_smul]) (fun _ _ _ ↦ by simp [smul_assoc])
      (fun _ _ _ ↦ by simp [smul_add])
      (fun c x y ↦ by rw [LinearMap.map_smul, smul_comm c x]) := by
    apply (InternalGrading.ofDecomposition 𝒜).linearMap_ext
    intro q a' ha'
    apply E.grading.linearMap_ext
    intro p e' he'
    rw [InternalGrading.ofDecomposition_piece] at ha'
    simp only [LinearMap.mk₂_apply]
    have hae : a' • e' ∈ E.grading.piece (q + p) := by
      simpa only [vadd_eq_add] using SetLike.GradedSMul.smul_mem ha' he'
    rw [coinducedLiftLinearK_apply_of_mem f hae, coinducedLiftLinearK_apply_of_mem f he',
      f.map_smul, smul_coinducedSingle ha' p (f e')]
  exact LinearMap.congr_fun (LinearMap.congr_fun hbil a) e

/-- On a homogeneous element of degree `p`, `coinducedLift f` acts by `coinducedSingle p ∘ f`. -/
theorem coinducedLift_apply_of_mem {E : GradedModuleCat.{v} 𝒜} (f : E →ₗ[A] M)
    {p : ℤ} {e : E} (he : e ∈ E.grading.piece p) :
    (coinducedLift f).hom e = coinducedSingle p (f e) :=
  coinducedLiftLinearK_apply_of_mem f he

/-- Composing `coinducedLift f` with `coinducedCounit` recovers `f`. -/
@[simp]
theorem coinducedCounit_comp_coinducedLift {E : GradedModuleCat.{v} 𝒜} (f : E →ₗ[A] M) :
    coinducedCounit 𝒜 M ∘ₗ (coinducedLift f).hom = f := by
  apply E.grading.linearMap_ext
  intro p e he
  simp [coinducedLift_apply_of_mem f he]

/-- Pointwise form of `coinducedCounit_comp_coinducedLift`. -/
@[simp]
theorem coinducedCounit_coinducedLift_apply {E : GradedModuleCat.{v} 𝒜} (f : E →ₗ[A] M) (e : E) :
    coinducedCounit 𝒜 M ((coinducedLift f).hom e) = f e :=
  LinearMap.congr_fun (coinducedCounit_comp_coinducedLift f) e

/-- Any graded morphism into `coinduced 𝒜 M` is recovered by lifting its composite with
`coinducedCounit`. -/
@[simp]
theorem coinducedLift_coinducedCounit_comp {E : GradedModuleCat.{v} 𝒜}
    (g : E ⟶ coinduced 𝒜 M) :
    coinducedLift (coinducedCounit 𝒜 M ∘ₗ g.hom) = g := by
  apply hom_ext
  apply E.grading.linearMap_ext
  intro p e he
  rw [coinducedLift_apply_of_mem _ he, LinearMap.comp_apply]
  obtain ⟨m, hm⟩ := (mem_coinduced_piece_iff p (g.hom e)).mp (map_mem g he)
  rw [← hm, coinducedCounit_single]

/-- Morphisms in `GradedModuleCat 𝒜` into `coinduced 𝒜 M` correspond additively to `A`-linear
maps into `M`. -/
def coinducedHomEquiv (E : GradedModuleCat.{v} 𝒜) (M : Type v) [AddCommGroup M] [Module A M] :
    (E ⟶ coinduced 𝒜 M) ≃+ (E →ₗ[A] M) where
  toFun g := coinducedCounit 𝒜 M ∘ₗ g.hom
  invFun := coinducedLift
  left_inv := coinducedLift_coinducedCounit_comp
  right_inv := coinducedCounit_comp_coinducedLift
  map_add' f g := by ext; simp

/-- Forward direction of `coinducedHomEquiv`: postcomposition with `coinducedCounit`. -/
@[simp]
theorem coinducedHomEquiv_apply {E : GradedModuleCat.{v} 𝒜} (g : E ⟶ coinduced 𝒜 M) :
    coinducedHomEquiv E M g = coinducedCounit 𝒜 M ∘ₗ g.hom :=
  (rfl)

/-- Inverse of `coinducedHomEquiv`: `coinducedLift`. -/
@[simp]
theorem coinducedHomEquiv_symm_apply {E : GradedModuleCat.{v} 𝒜} (f : E →ₗ[A] M) :
    (coinducedHomEquiv E M).symm f = coinducedLift f :=
  (rfl)

end CoinducedAPI

/-! ### The right adjoint functor and enough injectives -/

attribute [local implicit_reducible] toModuleCat

/-- The coinduced graded module functor `ModuleCat A ⥤ GradedModuleCat 𝒜`. -/
@[expose, implicit_reducible]
def coinducedFunctor : ModuleCat.{v} A ⥤ GradedModuleCat.{v} 𝒜 where
  obj M := coinduced 𝒜 M
  map {M N} φ := coinducedLift (φ.hom ∘ₗ coinducedCounit 𝒜 M)
  map_id M := by
    simpa only [ModuleCat.hom_id, LinearMap.id_comp, hom_id, LinearMap.comp_id] using
      coinducedLift_coinducedCounit_comp (𝟙 (coinduced 𝒜 M))
  map_comp {L M N} φ ψ := by
    apply (coinducedHomEquiv (coinduced 𝒜 L) N).injective
    ext x
    simp

/-- `coinducedFunctor 𝒜` sends an `A`-module `M` to `coinduced 𝒜 M`. -/
@[simp]
theorem coinducedFunctor_obj (M : ModuleCat.{v} A) :
    (coinducedFunctor 𝒜).obj M = coinduced 𝒜 M :=
  (rfl)

/-- Naturality of `coinducedCounit` with respect to `coinducedFunctor 𝒜`. -/
@[simp]
theorem coinducedCounit_comp_coinducedFunctor_map {M N : ModuleCat.{v} A} (φ : M ⟶ N) :
    coinducedCounit 𝒜 N ∘ₗ ((coinducedFunctor 𝒜).map φ).hom = φ.hom ∘ₗ coinducedCounit 𝒜 M :=
  coinducedCounit_comp_coinducedLift _

/-- **Coinduction is right adjoint to forgetting the grading.** -/
def coinducedAdjunction : toModuleCat.{v} (𝒜 := 𝒜) ⊣ coinducedFunctor.{v} 𝒜 :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun E M ↦
        Equiv.mk (fun f ↦ coinducedLift f.hom)
          (fun g ↦ ModuleCat.ofHom (coinducedCounit 𝒜 M ∘ₗ g.hom))
          (fun f ↦ ModuleCat.hom_ext (coinducedCounit_comp_coinducedLift f.hom))
          (fun g ↦ coinducedLift_coinducedCounit_comp g)
      homEquiv_naturality_left_symm := fun {E' E M} u g ↦ by
        apply ModuleCat.hom_ext
        ext x
        simp
      homEquiv_naturality_right := fun {E M N} f φ ↦ by
        apply (coinducedHomEquiv E N).injective
        ext x
        simp [coinducedFunctor] }

/-- The counit of `coinducedAdjunction` is `coinducedCounit`. -/
@[simp]
theorem hom_coinducedAdjunction_counit_app (M : ModuleCat.{v} A) :
    ((coinducedAdjunction 𝒜).counit.app M).hom = coinducedCounit 𝒜 M := by
  simp [coinducedAdjunction]

/-- Coinducing an injective `A`-module produces an injective graded `𝒜`-module. -/
instance injective_coinducedFunctor_obj (I : ModuleCat.{v} A) [Injective I] :
    Injective ((coinducedFunctor 𝒜).obj I) :=
  Injective.injective_of_adjoint (coinducedAdjunction 𝒜) I

/-- Every category of graded modules over an internally graded algebra has enough injectives,
obtained by coinducing injective `A`-modules along `coinducedAdjunction`. -/
instance enoughInjectives : EnoughInjectives (GradedModuleCat.{max uA v} 𝒜) :=
  EnoughInjectives.of_adjunction (coinducedAdjunction.{max uA v, uk, uA} 𝒜)

end TauCeti.GradedModuleCat
