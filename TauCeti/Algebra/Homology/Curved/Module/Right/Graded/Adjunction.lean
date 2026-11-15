/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.Algebra.Category.GradedModuleCat.Coinduced
public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.Homology.Curved.Module.Right.Abelian
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective
public import TauCeti.Algebra.Module.GradedModule.Prod

/-!
# Left and right adjoints to forgetting the differential of curved right modules

For a curved differential graded algebra `(𝒜, d, w)` over `R`, the faithful exact functor
`forgetDifferential` from the abelian category of closed curved right modules to the category of
graded right `A`-modules admits both a left adjoint `inducedFunctor` (`G⁺`) and a right adjoint
`coinducedFunctor` (`G⁻`), following Positselski.

For a graded right `A`-module `E`, the curved right module `inducedObj h E` (`G⁺(E)`) has:
* homogeneous degree-`p` piece `Eₚ ⊕ E_{p - 1}`,
* twisted right `A`-action
  `(x, y) · a = (x · a - (-1)^|y| y · d a, y · a)` for homogeneous `y`,
* curved differential `d(x, y) = (y · w, x)`.

Its curved differential squares to right multiplication by `w` because `d w = 0`, and obeys the
right graded Leibniz rule because `d (d a) = a * w - w * a`. Its cohomological shift by `1` is the
coinduced curved right module `coinducedObj h E := (inducedObj h E).shift 1` (`G⁻(E)`).

Both `inducedObj h E` and `coinducedObj h E` are contractible via `(x, y) ↦ (y, 0)` and
`(x, y) ↦ (-y, 0)`, hence zero in the curved homotopy category. Moreover, the underlying graded
right module of `inducedObj h E` sits in the natural graded short exact sequence
`0 ⟶ E ⟶ forgetDifferential(G⁺(E)) ⟶ E{1} ⟶ 0`, so `G⁺` preserves underlying graded projectivity
and graded injectivity, and `G⁻` preserves underlying graded injectivity. Combined with
`EnoughProjectives` and `EnoughInjectives` on graded right modules, every curved right module
admits a closed epimorphism from a contractible graded-projective curved module and a closed
monomorphism into a contractible graded-injective curved module.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.inducedObj` and `TauCeti.CurvedDGRightModuleCat.inducedFunctor`:
  the left adjoint `G⁺` to `forgetDifferential`.
* `TauCeti.CurvedDGRightModuleCat.coinducedObj` and
  `TauCeti.CurvedDGRightModuleCat.coinducedFunctor`: the right adjoint `G⁻` to
  `forgetDifferential`.
* `TauCeti.CurvedDGRightModuleCat.inducedAdjunction` and
  `TauCeti.CurvedDGRightModuleCat.coinducedAdjunction`: the adjunctions
  `inducedFunctor h ⊣ forgetDifferential` and `forgetDifferential ⊣ coinducedFunctor h`.
* `TauCeti.CurvedDGRightModuleCat.inducedShortComplex`: the underlying graded short exact sequence
  `0 ⟶ E ⟶ toGradedModuleCat (inducedObj h E) ⟶ E.shiftObj 1 ⟶ 0`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_inducedObj` and
  `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_coinducedObj`: `G⁺(E)` and `G⁻(E)` vanish in the
  curved homotopy category.
* `TauCeti.CurvedDGRightModuleCat.projective_toGradedModuleCat_inducedObj` and
  `TauCeti.CurvedDGRightModuleCat.injective_toGradedModuleCat_coinducedObj`: `G⁺` preserves
  projectivity and `G⁻` preserves injectivity of underlying graded modules.
* `TauCeti.CurvedDGRightModuleCat.exists_epi_from_inducedObj` and
  `TauCeti.CurvedDGRightModuleCat.exists_mono_to_coinducedObj`: canonical contractible
  graded-projective and graded-injective curved presentations.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6, Lemma.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6.
-/

public section

open CategoryTheory CategoryTheory.Limits MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe u

attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

/-! ### Private carrier of the induced curved right module -/

section Carrier

@[ext]
private structure InducedCarrier (E : Type u) where
  fst : E
  snd : E

private def InducedCarrier.toProd {E : Type u} (z : InducedCarrier E) : E × E :=
  (z.fst, z.snd)

private theorem InducedCarrier.toProd_injective (E : Type u) :
    Function.Injective (InducedCarrier.toProd (E := E)) :=
  fun _ _ h ↦ InducedCarrier.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

section CarrierGroup

variable {E : Type u} [AddCommGroup E]

private instance : Zero (InducedCarrier E) := ⟨⟨0, 0⟩⟩
private instance : Add (InducedCarrier E) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
private instance : Neg (InducedCarrier E) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
private instance : Sub (InducedCarrier E) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
private instance : SMul ℕ (InducedCarrier E) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
private instance : SMul ℤ (InducedCarrier E) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩

@[simp] private theorem InducedCarrier.fst_zero : (0 : InducedCarrier E).fst = 0 := rfl
@[simp] private theorem InducedCarrier.snd_zero : (0 : InducedCarrier E).snd = 0 := rfl
@[simp] private theorem InducedCarrier.fst_add (x y : InducedCarrier E) :
    (x + y).fst = x.fst + y.fst := rfl
@[simp] private theorem InducedCarrier.snd_add (x y : InducedCarrier E) :
    (x + y).snd = x.snd + y.snd := rfl
@[simp] private theorem InducedCarrier.fst_neg (x : InducedCarrier E) : (-x).fst = -x.fst := rfl
@[simp] private theorem InducedCarrier.snd_neg (x : InducedCarrier E) : (-x).snd = -x.snd := rfl
@[simp] private theorem InducedCarrier.fst_sub (x y : InducedCarrier E) :
    (x - y).fst = x.fst - y.fst := rfl
@[simp] private theorem InducedCarrier.snd_sub (x y : InducedCarrier E) :
    (x - y).snd = x.snd - y.snd := rfl
@[simp] private theorem InducedCarrier.fst_zsmul (n : ℤ) (x : InducedCarrier E) :
    (n • x).fst = n • x.fst := rfl
@[simp] private theorem InducedCarrier.snd_zsmul (n : ℤ) (x : InducedCarrier E) :
    (n • x).snd = n • x.snd := rfl

private instance : AddCommGroup (InducedCarrier E) :=
  (InducedCarrier.toProd_injective E).addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end CarrierGroup

section CarrierModule

variable {R : Type u} [CommRing R] {E : Type u} [AddCommGroup E] [Module R E]

private instance : SMul R (InducedCarrier E) := ⟨fun r x ↦ ⟨r • x.fst, r • x.snd⟩⟩

@[simp] private theorem InducedCarrier.fst_smul (r : R) (x : InducedCarrier E) :
    (r • x).fst = r • x.fst := rfl
@[simp] private theorem InducedCarrier.snd_smul (r : R) (x : InducedCarrier E) :
    (r • x).snd = r • x.snd := rfl

private instance : Module R (InducedCarrier E) :=
  (InducedCarrier.toProd_injective E).module R ⟨⟨InducedCarrier.toProd, rfl⟩, fun _ _ ↦ rfl⟩
    fun _ _ ↦ rfl

variable (R E) in
private def InducedCarrier.equivProd : InducedCarrier E ≃ₗ[R] E × E where
  toFun := InducedCarrier.toProd
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem InducedCarrier.equivProd_apply (z : InducedCarrier E) :
    InducedCarrier.equivProd R E z = (z.fst, z.snd) :=
  rfl

end CarrierModule

end Carrier

/-! ### Construction of `inducedObj` (`G⁺`) -/

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  (h : IsCurvedDGAlgebra 𝒜 d w)

section InducedHelpers

private theorem op_mem_opposite_of_mem {r : ℤ} {a : A} (ha : a ∈ 𝒜 r) :
    op a ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece r := by
  rwa [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece]

private theorem koszulTwist_one_of_mem
    {E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {q : ℤ} {y : E} (hy : y ∈ E.grading.piece q) :
    E.grading.koszulTwist 1 y = q.negOnePow • y := by
  rw [E.grading.koszulTwist_apply_of_mem hy 1, one_mul, Int.cast_smul_eq_zsmul, Units.smul_def]

private theorem koszulTwist_one_op_smul
    {E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {r : ℤ} {a : A} (ha : a ∈ 𝒜 r) (y : E) :
    E.grading.koszulTwist 1 (op a • y) =
      r.negOnePow • (op a • E.grading.koszulTwist 1 y) := by
  induction y using DirectSum.Decomposition.inductionOn E.grading.piece with
  | zero => simp
  | @homogeneous q y =>
    have hay : op a • (y : E) ∈ E.grading.piece (r + q) := by
      simpa only [vadd_eq_add] using SetLike.GradedSMul.smul_mem (op_mem_opposite_of_mem ha) y.2
    rw [koszulTwist_one_of_mem hay, koszulTwist_one_of_mem y.2, Int.negOnePow_add,
      Units.smul_def, Units.val_mul, mul_smul, ← Units.smul_def, ← Units.smul_def,
      smul_comm (op a) q.negOnePow]
  | add y₁ y₂ hy₁ hy₂ => simp [smul_add, map_add, hy₁, hy₂]

private noncomputable def inducedSMul (d : A →ₗ[R] A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (u : Aᵐᵒᵖ) (z : InducedCarrier E) : InducedCarrier E :=
  ⟨u • z.fst - op (d u.unop) • E.grading.koszulTwist 1 z.snd, u • z.snd⟩

@[simp]
private theorem inducedSMul_fst (d : A →ₗ[R] A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (u : Aᵐᵒᵖ) (z : InducedCarrier E) :
    (inducedSMul d E u z).fst = u • z.fst - op (d u.unop) • E.grading.koszulTwist 1 z.snd :=
  rfl

@[simp]
private theorem inducedSMul_snd (d : A →ₗ[R] A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (u : Aᵐᵒᵖ) (z : InducedCarrier E) :
    (inducedSMul d E u z).snd = u • z.snd :=
  rfl

private theorem inducedSMul_zero (d : A →ₗ[R] A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (u : Aᵐᵒᵖ) :
    inducedSMul d E u 0 = 0 :=
  InducedCarrier.ext (by simp) (smul_zero u)

private theorem inducedSMul_add (d : A →ₗ[R] A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (u : Aᵐᵒᵖ) (z₁ z₂ : InducedCarrier E) :
    inducedSMul d E u (z₁ + z₂) = inducedSMul d E u z₁ + inducedSMul d E u z₂ :=
  InducedCarrier.ext
    (by simp only [inducedSMul_fst, InducedCarrier.fst_add, InducedCarrier.snd_add, smul_add,
      map_add]; abel)
    (smul_add u z₁.snd z₂.snd)

private theorem add_inducedSMul (d : A →ₗ[R] A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (u₁ u₂ : Aᵐᵒᵖ) (z : InducedCarrier E) :
    inducedSMul d E (u₁ + u₂) z = inducedSMul d E u₁ z + inducedSMul d E u₂ z :=
  InducedCarrier.ext
    (by simp only [inducedSMul_fst, InducedCarrier.fst_add, add_smul, MulOpposite.unop_add,
      map_add, MulOpposite.op_add]; abel)
    (add_smul u₁ u₂ z.snd)

private theorem zero_inducedSMul (d : A →ₗ[R] A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : InducedCarrier E) :
    inducedSMul d E 0 z = 0 :=
  InducedCarrier.ext (by simp) (zero_smul Aᵐᵒᵖ z.snd)

private theorem smul_inducedSMul (d : A →ₗ[R] A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (r : R) (u : Aᵐᵒᵖ) (z : InducedCarrier E) :
    inducedSMul d E (r • u) z = r • inducedSMul d E u z :=
  InducedCarrier.ext
    (by simp only [inducedSMul_fst, InducedCarrier.fst_smul, MulOpposite.unop_smul, d.map_smul,
      MulOpposite.op_smul, smul_assoc, smul_sub])
    (smul_assoc r u z.snd)

private noncomputable abbrev inducedGrading
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    InternalGrading R (InducedCarrier E) ℤ :=
  (E.grading.prod (E.shiftObj 1).grading).map (InducedCarrier.equivProd R E).symm

private theorem mem_inducedGrading_iff
    {E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (p : ℤ) (z : InducedCarrier E) :
    z ∈ (inducedGrading E).piece p ↔
      z.fst ∈ E.grading.piece p ∧ z.snd ∈ E.grading.piece (p - 1) := by
  rw [InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm, InternalGrading.prod_piece,
    Submodule.mem_prod, GradedModuleCat.mem_shiftObj_piece_iff]
  rfl

private def inducedDifferential (w : A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    InducedCarrier E →ₗ[R] InducedCarrier E where
  toFun z := ⟨op w • z.snd, z.fst⟩
  map_add' x y := by ext <;> simp [smul_add]
  map_smul' r x := by ext <;> simp [smul_comm r (op w)]

@[simp]
private theorem inducedDifferential_fst (w : A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : InducedCarrier E) :
    (inducedDifferential w E z).fst = op w • z.snd :=
  rfl

@[simp]
private theorem inducedDifferential_snd (w : A)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (z : InducedCarrier E) :
    (inducedDifferential w E z).snd = z.fst :=
  rfl

end InducedHelpers

section InducedAction

include h

private theorem inducedSmul_mul
    {E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (b a : A) (z : InducedCarrier E) :
    op (a * b) • z.fst - op (d (a * b)) • E.grading.koszulTwist 1 z.snd =
      op b • (op a • z.fst - op (d a) • E.grading.koszulTwist 1 z.snd) -
        op (d b) • E.grading.koszulTwist 1 (op a • z.snd) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous r a =>
    rw [koszulTwist_one_op_smul a.2, h.leibniz a.2 b]
    simp only [MulOpposite.op_add, MulOpposite.op_mul, Units.smul_def, MulOpposite.op_smul,
      add_smul, mul_smul, smul_assoc, smul_sub, smul_comm (op (d b)) (r.negOnePow : ℤ), sub_sub]
  | add a₁ a₂ ha₁ ha₂ =>
    calc op ((a₁ + a₂) * b) • z.fst - op (d ((a₁ + a₂) * b)) • E.grading.koszulTwist 1 z.snd
      _ = (op (a₁ * b) • z.fst - op (d (a₁ * b)) • E.grading.koszulTwist 1 z.snd) +
            (op (a₂ * b) • z.fst - op (d (a₂ * b)) • E.grading.koszulTwist 1 z.snd) := by
          rw [add_mul, map_add, MulOpposite.op_add, MulOpposite.op_add, add_smul, add_smul]
          abel
      _ = op b • (op (a₁ + a₂) • z.fst - op (d (a₁ + a₂)) • E.grading.koszulTwist 1 z.snd) -
            op (d b) • E.grading.koszulTwist 1 (op (a₁ + a₂) • z.snd) := by
          rw [ha₁, ha₂]
          simp only [MulOpposite.op_add, add_smul, map_add, smul_add, smul_sub]
          abel

private theorem inducedSMul_one
    {E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (z : InducedCarrier E) :
    inducedSMul d E 1 z = z :=
  InducedCarrier.ext (by simp [h.map_one_eq_zero]) (one_smul Aᵐᵒᵖ z.snd)

private theorem inducedSMul_mul_apply
    {E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (v u : Aᵐᵒᵖ) (z : InducedCarrier E) :
    inducedSMul d E (v * u) z = inducedSMul d E v (inducedSMul d E u z) :=
  InducedCarrier.ext
    (by simpa only [inducedSMul_fst, inducedSMul_snd, MulOpposite.op_mul, MulOpposite.unop_mul,
      MulOpposite.op_unop] using inducedSmul_mul h v.unop u.unop z)
    (mul_smul v u z.snd)

@[instance_reducible]
private noncomputable def inducedModuleOp (h : IsCurvedDGAlgebra 𝒜 d w)
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    Module Aᵐᵒᵖ (InducedCarrier E) where
  smul := inducedSMul d E
  one_smul := inducedSMul_one h
  mul_smul := inducedSMul_mul_apply h
  smul_zero := inducedSMul_zero d E
  smul_add := inducedSMul_add d E
  add_smul := add_inducedSMul d E
  zero_smul := zero_inducedSMul d E

private theorem inducedIsScalarTower
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    let _ := inducedModuleOp h E
    IsScalarTower R Aᵐᵒᵖ (InducedCarrier E) :=
  let _ := inducedModuleOp h E
  ⟨smul_inducedSMul d E⟩

private theorem inducedSMul_mem_piece
    {E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {r p : ℤ} {u : Aᵐᵒᵖ} {z : InducedCarrier E}
    (hu : u ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece r)
    (hz : z ∈ (inducedGrading E).piece p) :
    inducedSMul d E u z ∈ (inducedGrading E).piece (r + p) := by
  rw [mem_inducedGrading_iff] at hz ⊢
  rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at hu
  have hu' : u ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece r := by
    simpa only [MulOpposite.op_unop] using op_mem_opposite_of_mem hu
  have hdu : op (d u.unop) ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece (r + 1) :=
    op_mem_opposite_of_mem (h.map_mem hu)
  have hτ : E.grading.koszulTwist 1 z.snd ∈ E.grading.piece (p - 1) :=
    E.grading.koszulTwist_mem_piece hz.2 1
  refine ⟨Submodule.sub_mem _ ?_ ?_, ?_⟩
  · simpa only [inducedSMul_fst, vadd_eq_add] using SetLike.GradedSMul.smul_mem hu' hz.1
  · have hmem := SetLike.GradedSMul.smul_mem hdu hτ
    simpa only [vadd_eq_add, (by omega : r + 1 + (p - 1) = r + p)] using hmem
  · have hmem := SetLike.GradedSMul.smul_mem hu' hz.2
    simpa only [inducedSMul_snd, vadd_eq_add, (by omega : r + (p - 1) = r + p - 1)] using hmem

private theorem inducedGradedSMul
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    let _ := inducedModuleOp h E
    SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
      (inducedGrading E).piece :=
  let _ := inducedModuleOp h E
  ⟨fun ⦃_ _⦄ _ _ hu hz ↦ inducedSMul_mem_piece h hu hz⟩

private theorem inducedLeibniz
    {E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {p : ℤ} {z : InducedCarrier E} (hz : z ∈ (inducedGrading E).piece p) (a : A) :
    inducedDifferential w E (inducedSMul d E (op a) z) =
      inducedSMul d E (op a) (inducedDifferential w E z) +
        p.negOnePow • inducedSMul d E (op (d a)) z := by
  obtain ⟨hz₁, hz₂⟩ := (mem_inducedGrading_iff p z).mp hz
  have hτ₁ : E.grading.koszulTwist 1 z.fst = p.negOnePow • z.fst :=
    koszulTwist_one_of_mem hz₁
  have hτ₂ : E.grading.koszulTwist 1 z.snd = -(p.negOnePow • z.snd) := by
    rw [koszulTwist_one_of_mem hz₂, Int.negOnePow_sub, Int.negOnePow_one,
      mul_neg, mul_one, Units.neg_smul]
  refine InducedCarrier.ext ?_ ?_
  · simp only [inducedDifferential_fst, inducedDifferential_snd, inducedSMul_fst,
      inducedSMul_snd, InducedCarrier.fst_add, Units.smul_def, InducedCarrier.fst_zsmul,
      MulOpposite.unop_op]
    rw [hτ₁, hτ₂, h.sq_eq a]
    simp only [Units.smul_def, smul_neg, sub_neg_eq_add, smul_add]
    rw [smul_comm (op (a * w - w * a)) (p.negOnePow : ℤ),
      ← mul_smul (p.negOnePow : ℤ) (p.negOnePow : ℤ), ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_smul, smul_comm (op (d a)) (p.negOnePow : ℤ),
      ← mul_smul (op w) (op a), ← mul_smul (op a) (op w),
      ← MulOpposite.op_mul, ← MulOpposite.op_mul]
    have hw : op (a * w) • z.snd = op (w * a) • z.snd + op (a * w - w * a) • z.snd := by
      rw [← add_smul, ← MulOpposite.op_add, add_sub_cancel]
    rw [hw]
    abel
  · simp only [inducedDifferential_snd, inducedSMul_fst, inducedSMul_snd,
      InducedCarrier.snd_add, Units.smul_def, InducedCarrier.snd_zsmul, MulOpposite.unop_op]
    rw [hτ₂, Units.smul_def, smul_neg, sub_neg_eq_add, smul_comm (op (d a)) (p.negOnePow : ℤ)]

private theorem inducedDifferential_sq
    {E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (z : InducedCarrier E) :
    inducedDifferential w E (inducedDifferential w E z) = inducedSMul d E (op w) z :=
  InducedCarrier.ext (by simp [h.map_curvature]) rfl

end InducedAction

/-- The **induced curved right module** `G⁺(E)` on a graded right `A`-module `E`, left adjoint on
objects to `forgetDifferential`. -/
noncomputable def inducedObj
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{u, u, u} h := by
  letI : Module Aᵐᵒᵖ (InducedCarrier E) := inducedModuleOp h E
  letI : IsScalarTower R Aᵐᵒᵖ (InducedCarrier E) := inducedIsScalarTower h E
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
      (inducedGrading E).piece := inducedGradedSMul h E
  refine
    { carrier := InducedCarrier E
      grading := (inducedGrading E).piece
      differential := inducedDifferential w E
      isCurvedDGRightModule := ⟨?_, fun hz a ↦ inducedLeibniz h hz a, inducedDifferential_sq h⟩ }
  refine LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_
  obtain ⟨hz₁, hz₂⟩ := (mem_inducedGrading_iff p z).mp hz
  rw [mem_inducedGrading_iff]
  refine ⟨?_, by simpa only [inducedDifferential_snd, add_sub_cancel_right] using hz₁⟩
  have hw := SetLike.GradedSMul.smul_mem (op_mem_opposite_of_mem h.curvature_mem) hz₂
  simpa only [inducedDifferential_fst, vadd_eq_add, (by omega : 2 + (p - 1) = p + 1)] using hw

/-- The **coinduced curved right module** `G⁻(E) := G⁺(E)[1]` on a graded right `A`-module `E`,
right adjoint on objects to `forgetDifferential`. -/
noncomputable def coinducedObj
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{u, u, u} h :=
  (inducedObj h E).shift 1

/-- `coinducedObj h E` is the shift by `1` of `inducedObj h E`. -/
theorem coinducedObj_eq_shift
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    coinducedObj h E = (inducedObj h E).shift 1 :=
  (rfl)

attribute [local implicit_reducible] inducedObj coinducedObj

/-! ### Left and right adjunctions with `forgetDifferential` -/

section Adjunctions

variable {E F : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
  {M N : CurvedDGRightModuleCat.{u, u, u} h}

private noncomputable def mkInducedObj (e₁ e₂ : E) : inducedObj h E := ⟨e₁, e₂⟩

@[simp]
private theorem mkInducedObj_fst (e₁ e₂ : E) : (mkInducedObj h e₁ e₂).fst = e₁ := rfl

@[simp]
private theorem mkInducedObj_snd (e₁ e₂ : E) : (mkInducedObj h e₁ e₂).snd = e₂ := rfl

@[simp]
private theorem inducedObj_zero_fst : (0 : inducedObj h E).fst = 0 := rfl

@[simp]
private theorem inducedObj_zero_snd : (0 : inducedObj h E).snd = 0 := rfl

@[simp]
private theorem inducedObj_add_fst (x y : inducedObj h E) :
    (x + y).fst = x.fst + y.fst := rfl

@[simp]
private theorem inducedObj_add_snd (x y : inducedObj h E) :
    (x + y).snd = x.snd + y.snd := rfl

@[simp]
private theorem inducedObj_neg_fst (x : inducedObj h E) :
    (-x).fst = -x.fst := rfl

@[simp]
private theorem inducedObj_neg_snd (x : inducedObj h E) :
    (-x).snd = -x.snd := rfl

@[simp]
private theorem inducedObj_smul_fst (u : Aᵐᵒᵖ) (z : inducedObj h E) :
    (u • z).fst = u • z.fst - op (d u.unop) • E.grading.koszulTwist 1 z.snd :=
  rfl

@[simp]
private theorem inducedObj_smul_snd (u : Aᵐᵒᵖ) (z : inducedObj h E) :
    (u • z).snd = u • z.snd :=
  rfl

@[simp]
private theorem inducedObj_differential_fst (z : inducedObj h E) :
    ((inducedObj h E).differential z).fst = op w • z.snd :=
  rfl

@[simp]
private theorem inducedObj_differential_snd (z : inducedObj h E) :
    ((inducedObj h E).differential z).snd = z.fst :=
  rfl

private noncomputable def mkCoinducedObj (e₁ e₂ : E) : coinducedObj h E := ⟨e₁, e₂⟩

@[simp]
private theorem mkCoinducedObj_fst (e₁ e₂ : E) : (mkCoinducedObj h e₁ e₂).fst = e₁ := rfl

@[simp]
private theorem mkCoinducedObj_snd (e₁ e₂ : E) : (mkCoinducedObj h e₁ e₂).snd = e₂ := rfl

@[simp]
private theorem coinducedObj_add_fst (x y : coinducedObj h E) :
    (x + y).fst = x.fst + y.fst := rfl

@[simp]
private theorem coinducedObj_add_snd (x y : coinducedObj h E) :
    (x + y).snd = x.snd + y.snd := rfl

@[simp]
private theorem coinducedObj_neg_fst (x : coinducedObj h E) :
    (-x).fst = -x.fst := rfl

@[simp]
private theorem coinducedObj_neg_snd (x : coinducedObj h E) :
    (-x).snd = -x.snd := rfl

@[simp]
private theorem coinducedObj_smul_fst (u : Aᵐᵒᵖ) (z : coinducedObj h E) :
    (u • z).fst = u • z.fst - op (d u.unop) • E.grading.koszulTwist 1 z.snd :=
  rfl

@[simp]
private theorem coinducedObj_smul_snd (u : Aᵐᵒᵖ) (z : coinducedObj h E) :
    (u • z).snd = u • z.snd :=
  rfl

private noncomputable def inducedUnitLinear
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    E →ₗ[Aᵐᵒᵖ] inducedObj h E where
  toFun e := mkInducedObj h e 0
  map_add' _ _ := InducedCarrier.ext rfl (add_zero 0).symm
  map_smul' _ _ := InducedCarrier.ext (by simp) (by simp)

@[simp]
private theorem inducedUnitLinear_apply (e : E) :
    inducedUnitLinear h E e = mkInducedObj h e 0 :=
  rfl

/-- The unit morphism `E ⟶ toGradedModuleCat (inducedObj h E)` sending `e ↦ (e, 0)`. -/
noncomputable def inducedUnit
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    E ⟶ toGradedModuleCat (inducedObj h E) :=
  GradedModuleCat.ofHom (M := E) (N := toGradedModuleCat (inducedObj h E)) (inducedUnitLinear h E)
    (LinearMap.isHomogeneous_def.mpr fun p e he ↦ by
      rw [toGradedModuleCat_piece, add_zero, inducedUnitLinear_apply]
      exact (mem_inducedGrading_iff p (mkInducedObj h e 0)).mpr ⟨he, Submodule.zero_mem _⟩)

@[simp]
private theorem inducedUnit_hom_apply (e : E) :
    (inducedUnit h E).hom e = mkInducedObj h e 0 :=
  rfl

private noncomputable def homToCarrier (f : E ⟶ toGradedModuleCat M) : E →ₗ[Aᵐᵒᵖ] M :=
  f.hom

private noncomputable def homFromCarrier (f : toGradedModuleCat M ⟶ E) : M →ₗ[Aᵐᵒᵖ] E :=
  f.hom

private theorem differential_smul_hom_apply (f : E ⟶ toGradedModuleCat M) (u : Aᵐᵒᵖ) (y : E) :
    M.differential (u • homToCarrier h f y) =
      u • M.differential (homToCarrier h f y) +
        op (d u.unop) • homToCarrier h f (E.grading.koszulTwist 1 y) := by
  induction y using DirectSum.Decomposition.inductionOn E.grading.piece with
  | zero => simp
  | @homogeneous q y =>
    have hfy : homToCarrier h f y ∈ M.grading q := by
      simpa only [homToCarrier, toGradedModuleCat_piece] using GradedModuleCat.map_mem f y.2
    have hleib := M.isCurvedDGRightModule.leibniz hfy u.unop
    rw [MulOpposite.op_unop] at hleib
    rw [hleib, koszulTwist_one_of_mem y.2]
    simp only [Units.smul_def, map_zsmul, smul_comm (op (d u.unop)) (q.negOnePow : ℤ)]
  | add y₁ y₂ hy₁ hy₂ =>
    simp only [map_add, smul_add, hy₁, hy₂]
    abel

/-- Lift a graded morphism `f : E ⟶ toGradedModuleCat M` to a closed morphism
`inducedObj h E ⟶ M` sending `(x, y) ↦ f x + d_M (f y)`. -/
noncomputable def inducedLift (f : E ⟶ toGradedModuleCat M) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h E) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M := by
  refine closedHomOf
    { toFun := fun z ↦ homToCarrier h f z.fst + M.differential (homToCarrier h f z.snd)
      map_add' := fun z₁ z₂ ↦ by
        simp only [inducedObj_add_fst, inducedObj_add_snd, map_add]
        abel
      map_smul' := fun u z ↦ by
        simp only [inducedObj_smul_fst, inducedObj_smul_snd, map_sub, map_smul,
          differential_smul_hom_apply h f u z.snd, RingHom.id_apply, smul_add]
        abel }
    (fun p z hz ↦ ?_)
    (fun z ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [map_add, M.isCurvedDGRightModule.sq_eq, inducedObj_differential_fst,
        inducedObj_differential_snd, map_smul, add_comm])
  obtain ⟨hz₁, hz₂⟩ := (mem_inducedGrading_iff p z).mp hz
  have hfx : homToCarrier h f z.fst ∈ M.grading p := by
    simpa only [homToCarrier, toGradedModuleCat_piece] using GradedModuleCat.map_mem f hz₁
  have hfy : homToCarrier h f z.snd ∈ M.grading (p - 1) := by
    simpa only [homToCarrier, toGradedModuleCat_piece] using GradedModuleCat.map_mem f hz₂
  have hdfy : M.differential (homToCarrier h f z.snd) ∈ M.grading p := by
    simpa only [sub_add_cancel] using M.isCurvedDGRightModule.isHomogeneous.map_mem hfy
  exact Submodule.add_mem _ hfx hdfy

@[simp]
private theorem closedHom_inducedLift_apply (f : E ⟶ toGradedModuleCat M) (z : inducedObj h E) :
    closedHom (inducedLift h f) z =
      homToCarrier h f z.fst + M.differential (homToCarrier h f z.snd) := by
  simp [inducedLift]

/-- Precomposing the underlying graded morphism of `inducedLift h f` with `inducedUnit h E`
recovers `f`. -/
@[simp]
theorem inducedUnit_comp_forgetDifferential_inducedLift (f : E ⟶ toGradedModuleCat M) :
    inducedUnit h E ≫ (forgetDifferential (h := h)).map (inducedLift h f) = f := by
  apply GradedModuleCat.hom_ext
  ext e
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply, forgetDifferential_map_hom,
    inducedUnit_hom_apply]
  rw [closedHom_inducedLift_apply]
  simp [homToCarrier]

/-- Any closed morphism out of `inducedObj h E` is uniquely determined by precomposing its
underlying graded morphism with `inducedUnit h E`. -/
@[simp]
theorem inducedLift_inducedUnit_comp
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h E) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) :
    inducedLift h (inducedUnit h E ≫ (forgetDifferential (h := h)).map g) = g := by
  apply closedHom_ext
  intro z
  have hz : z = mkInducedObj h z.fst 0 +
      (inducedObj h E).differential (mkInducedObj h z.snd 0) :=
    InducedCarrier.ext (by simp) (by simp)
  conv_rhs => rw [hz, map_add, ← differential_closedHom]
  rw [closedHom_inducedLift_apply]
  rfl

/-- The left adjoint functor `G⁺` from graded right `A`-modules to closed curved right modules. -/
noncomputable def inducedFunctor :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj E := ForgetEnrichment.of _ (inducedObj h E)
  map {E F} φ := inducedLift h (φ ≫ inducedUnit h F)
  map_id E := by
    rw [Category.id_comp]
    have hid : inducedUnit h E =
        inducedUnit h E ≫ (forgetDifferential (h := h)).map
          (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h E))) := by
      apply GradedModuleCat.hom_ext
      ext e
      simp
    rw [hid]
    exact inducedLift_inducedUnit_comp h (M := inducedObj h E) _
  map_comp {E F G} φ ψ := by
    have hcomp : inducedUnit h E ≫
        (forgetDifferential (h := h)).map
          (inducedLift h (φ ≫ inducedUnit h F) ≫ inducedLift h (ψ ≫ inducedUnit h G)) =
        (φ ≫ ψ) ≫ inducedUnit h G := by
      rw [Functor.map_comp, ← Category.assoc, inducedUnit_comp_forgetDifferential_inducedLift,
        Category.assoc, inducedUnit_comp_forgetDifferential_inducedLift, Category.assoc]
    exact (congrArg (inducedLift h) hcomp).symm.trans
      (inducedLift_inducedUnit_comp h (M := inducedObj h G)
        (inducedLift h (φ ≫ inducedUnit h F) ≫ inducedLift h (ψ ≫ inducedUnit h G)))

attribute [local implicit_reducible] inducedFunctor

/-- `inducedFunctor h` sends a graded right module `E` to `inducedObj h E` in the closed
category. -/
@[simp]
theorem inducedFunctor_obj
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (inducedFunctor (R := R) h).obj E =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h E) :=
  (rfl)

/-- **Positselski's left adjunction `G⁺ ⊣ forgetDifferential`.** -/
noncomputable def inducedAdjunction :
    inducedFunctor (R := R) h ⊣ forgetDifferential (h := h) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun E M ↦
        { toFun := fun g ↦ inducedUnit h E ≫ (forgetDifferential (h := h)).map g
          invFun := fun f ↦ inducedLift h (M := ForgetEnrichment.to _ M) f
          left_inv := fun g ↦ inducedLift_inducedUnit_comp h (M := ForgetEnrichment.to _ M) g
          right_inv := fun f ↦
            inducedUnit_comp_forgetDifferential_inducedLift h (M := ForgetEnrichment.to _ M) f }
      homEquiv_naturality_left_symm := fun {E' E M} u f ↦ by
        dsimp only [Equiv.coe_fn_symm_mk]
        have hnat : inducedUnit h E' ≫
            (forgetDifferential (h := h)).map
              ((inducedFunctor (R := R) h).map u ≫
                inducedLift h (M := ForgetEnrichment.to _ M) f) = u ≫ f := by
          rw [Functor.map_comp, ← Category.assoc]
          exact ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (inducedUnit_comp_forgetDifferential_inducedLift h
              (u ≫ inducedUnit h E)))).trans
            ((Category.assoc _ _ _).trans
              (congrArg (u ≫ ·) (inducedUnit_comp_forgetDifferential_inducedLift h
                (M := ForgetEnrichment.to _ M) f)))
        exact (congrArg (inducedLift h (M := ForgetEnrichment.to _ M)) hnat).symm.trans
          (inducedLift_inducedUnit_comp h (M := ForgetEnrichment.to _ M) _)
      homEquiv_naturality_right := fun {E M N} g v ↦ by
        dsimp only [Equiv.coe_fn_mk]
        rw [Functor.map_comp, Category.assoc] }

/-- `inducedLift h f` is an epimorphism whenever `f` is a graded epimorphism. -/
instance epi_inducedLift (f : E ⟶ toGradedModuleCat M) [Epi f] :
    Epi (inducedLift h f) := by
  have hepi : Epi (inducedUnit h E ≫ (forgetDifferential (h := h)).map (inducedLift h f)) := by
    rw [inducedUnit_comp_forgetDifferential_inducedLift]
    infer_instance
  have : Epi ((forgetDifferential (h := h)).map (inducedLift h f)) :=
    epi_of_epi (inducedUnit h E) _
  exact (forgetDifferential (h := h)).epi_of_epi_map ‹_›

private noncomputable def coinducedCounitLinear
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinducedObj h E) →ₗ[Aᵐᵒᵖ] E where
  toFun z := z.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem coinducedCounitLinear_apply (z : toGradedModuleCat (coinducedObj h E)) :
    coinducedCounitLinear h E z = z.snd :=
  rfl

/-- The counit morphism `toGradedModuleCat (coinducedObj h E) ⟶ E` sending `(x, y) ↦ y`. -/
noncomputable def coinducedCounit
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinducedObj h E) ⟶ E :=
  GradedModuleCat.ofHom (coinducedCounitLinear h E)
    (LinearMap.isHomogeneous_def.mpr fun p z hz ↦ by
      rw [toGradedModuleCat_piece] at hz
      dsimp only [coinducedObj] at hz
      rw [shift_grading] at hz
      obtain ⟨_, hz₂⟩ := (mem_inducedGrading_iff (p + 1) z).mp hz
      simpa only [coinducedCounitLinear_apply, add_zero, add_sub_cancel_right] using hz₂)

private theorem neg_hom_differential_smul (f : toGradedModuleCat M ⟶ E) (u : Aᵐᵒᵖ) (m : M) :
    -homFromCarrier h f (M.differential (u • m)) =
      u • (-homFromCarrier h f (M.differential m)) -
        op (d u.unop) • E.grading.koszulTwist 1 (homFromCarrier h f m) := by
  induction m using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | @homogeneous q m =>
    have hfm : homFromCarrier h f (m : M) ∈ E.grading.piece q :=
      GradedModuleCat.map_mem f (by simpa only [toGradedModuleCat_piece] using m.2)
    have hleib := M.isCurvedDGRightModule.leibniz m.2 u.unop
    rw [MulOpposite.op_unop] at hleib
    rw [hleib]
    simp only [map_add, map_smul, Units.smul_def, map_zsmul, neg_add, smul_neg]
    rw [koszulTwist_one_of_mem hfm]
    simp only [Units.smul_def, smul_comm (op (d u.unop)) (q.negOnePow : ℤ), sub_eq_add_neg]
  | add m₁ m₂ hm₁ hm₂ =>
    simp only [smul_add, map_add, neg_add, hm₁, hm₂]
    abel

/-- Lift a graded morphism `f : toGradedModuleCat M ⟶ E` to a closed morphism
`M ⟶ coinducedObj h E` sending `m ↦ (-f (d_M m), f m)`. -/
noncomputable def coinducedLift (f : toGradedModuleCat M ⟶ E) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h E) := by
  refine closedHomOf
    { toFun := fun m ↦
        mkCoinducedObj h (-homFromCarrier h f (M.differential m)) (homFromCarrier h f m)
      map_add' := fun m₁ m₂ ↦ InducedCarrier.ext
        (by simp only [map_add, neg_add, coinducedObj_add_fst, mkCoinducedObj_fst])
        (map_add (homFromCarrier h f) m₁ m₂)
      map_smul' := fun u m ↦ InducedCarrier.ext
        (by
          simpa only [mkCoinducedObj_fst, coinducedObj_smul_fst, mkCoinducedObj_snd,
            RingHom.id_apply] using neg_hom_differential_smul h f u m)
        ((homFromCarrier h f).map_smul u m) }
    (fun p m hm ↦ ?_) (fun m ↦ ?_)
  · dsimp only [coinducedObj, LinearMap.coe_mk, AddHom.coe_mk]
    rw [shift_grading]
    refine (mem_inducedGrading_iff (p + 1) _).mpr ?_
    have hdm : M.differential m ∈ M.grading (p + 1) :=
      M.isCurvedDGRightModule.isHomogeneous.map_mem hm
    refine ⟨by simpa only [mkCoinducedObj_fst, homFromCarrier] using
      Submodule.neg_mem _ (GradedModuleCat.map_mem f
        (by simpa only [toGradedModuleCat_piece] using hdm)), ?_⟩
    simpa only [mkCoinducedObj_snd, homFromCarrier, add_sub_cancel_right] using
      GradedModuleCat.map_mem f (by simpa only [toGradedModuleCat_piece] using hm)
  · dsimp only [coinducedObj]
    rw [shift_one_differential_apply]
    exact InducedCarrier.ext
      (by simp only [LinearMap.coe_mk, AddHom.coe_mk, inducedObj_neg_fst,
        inducedObj_differential_fst, mkCoinducedObj_snd, M.isCurvedDGRightModule.sq_eq, map_smul,
        mkCoinducedObj_fst])
      (by simp only [LinearMap.coe_mk, AddHom.coe_mk, inducedObj_neg_snd,
        inducedObj_differential_snd, mkCoinducedObj_fst, neg_neg, mkCoinducedObj_snd])

@[simp]
private theorem closedHom_coinducedLift_apply (f : toGradedModuleCat M ⟶ E) (m : M) :
    closedHom (coinducedLift h f) m =
      mkCoinducedObj h (-homFromCarrier h f (M.differential m)) (homFromCarrier h f m) := by
  simp [coinducedLift]

/-- Postcomposing the underlying graded morphism of `coinducedLift h f` with `coinducedCounit h E`
recovers `f`. -/
@[simp]
theorem forgetDifferential_coinducedLift_comp_coinducedCounit (f : toGradedModuleCat M ⟶ E) :
    (forgetDifferential (h := h)).map (coinducedLift h f) ≫ coinducedCounit h E = f := by
  apply GradedModuleCat.hom_ext
  ext m
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply, forgetDifferential_map_hom]
  rw [closedHom_coinducedLift_apply]
  rfl

/-- Any closed morphism into `coinducedObj h E` is uniquely determined by postcomposing its
underlying graded morphism with `coinducedCounit h E`. -/
@[simp]
theorem coinducedLift_comp_coinducedCounit
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h E)) :
    coinducedLift h ((forgetDifferential (h := h)).map g ≫ coinducedCounit h E) = g := by
  apply closedHom_ext
  intro m
  have hd := congrArg InducedCarrier.snd (differential_closedHom g m)
  dsimp only [coinducedObj] at hd
  rw [shift_one_differential_apply] at hd
  have hfst : (closedHom g m).fst = -(closedHom g (M.differential m)).snd :=
    neg_eq_iff_eq_neg.mp hd
  rw [closedHom_coinducedLift_apply]
  exact InducedCarrier.ext hfst.symm rfl

/-- The right adjoint functor `G⁻` from graded right `A`-modules to closed curved right modules. -/
noncomputable def coinducedFunctor :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj E := ForgetEnrichment.of _ (coinducedObj h E)
  map {E F} φ := coinducedLift h (coinducedCounit h E ≫ φ)
  map_id E := by
    rw [Category.comp_id]
    have hid : coinducedCounit h E =
        (forgetDifferential (h := h)).map
          (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h E))) ≫
            coinducedCounit h E := by
      apply GradedModuleCat.hom_ext
      ext z
      simp
    rw [hid]
    exact coinducedLift_comp_coinducedCounit h (M := coinducedObj h E) _
  map_comp {E F G} φ ψ := by
    have hcomp : (forgetDifferential (h := h)).map
          (coinducedLift h (coinducedCounit h E ≫ φ) ≫
            coinducedLift h (coinducedCounit h F ≫ ψ)) ≫ coinducedCounit h G =
        coinducedCounit h E ≫ (φ ≫ ψ) := by
      rw [Functor.map_comp, Category.assoc, forgetDifferential_coinducedLift_comp_coinducedCounit,
        ← Category.assoc, forgetDifferential_coinducedLift_comp_coinducedCounit, Category.assoc]
    exact (congrArg (coinducedLift h) hcomp).symm.trans
      (coinducedLift_comp_coinducedCounit h (M := coinducedObj h E)
        (coinducedLift h (coinducedCounit h E ≫ φ) ≫
          coinducedLift h (coinducedCounit h F ≫ ψ)))

attribute [local implicit_reducible] coinducedFunctor

/-- `coinducedFunctor h` sends a graded right module `E` to `coinducedObj h E` in the closed
category. -/
@[simp]
theorem coinducedFunctor_obj
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinducedFunctor (R := R) h).obj E =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h E) :=
  (rfl)

/-- **Positselski's right adjunction `forgetDifferential ⊣ G⁻`.** -/
noncomputable def coinducedAdjunction :
    forgetDifferential (h := h) ⊣ coinducedFunctor (R := R) h :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M E ↦
        { toFun := fun f ↦ coinducedLift h (M := ForgetEnrichment.to _ M) f
          invFun := fun g ↦ (forgetDifferential (h := h)).map g ≫ coinducedCounit h E
          left_inv := fun f ↦
            forgetDifferential_coinducedLift_comp_coinducedCounit h (M := ForgetEnrichment.to _ M) f
          right_inv := fun g ↦
            coinducedLift_comp_coinducedCounit h (M := ForgetEnrichment.to _ M) g }
      homEquiv_naturality_left_symm := fun {M' M E} u g ↦ by
        dsimp only [Equiv.coe_fn_symm_mk]
        rw [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := fun {M E F} f v ↦ by
        dsimp only [Equiv.coe_fn_mk]
        have hnat : (forgetDifferential (h := h)).map
            (coinducedLift h (M := ForgetEnrichment.to _ M) f ≫
              (coinducedFunctor (R := R) h).map v) ≫ coinducedCounit h F = f ≫ v := by
          rw [Functor.map_comp, Category.assoc]
          exact (congrArg (_ ≫ ·) (forgetDifferential_coinducedLift_comp_coinducedCounit h
            (coinducedCounit h E ≫ v))).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ v) (forgetDifferential_coinducedLift_comp_coinducedCounit h
                (M := ForgetEnrichment.to _ M) f)))
        exact (congrArg (coinducedLift h (M := ForgetEnrichment.to _ M)) hnat).symm.trans
          (coinducedLift_comp_coinducedCounit h (M := ForgetEnrichment.to _ M) _) }

/-- `coinducedLift h f` is a monomorphism whenever `f` is a graded monomorphism. -/
instance mono_coinducedLift (f : toGradedModuleCat M ⟶ E) [Mono f] :
    Mono (coinducedLift h f) := by
  have hmono : Mono ((forgetDifferential (h := h)).map (coinducedLift h f) ≫
      coinducedCounit h E) := by
    rw [forgetDifferential_coinducedLift_comp_coinducedCounit]
    infer_instance
  have : Mono ((forgetDifferential (h := h)).map (coinducedLift h f)) :=
    mono_of_mono _ (coinducedCounit h E)
  exact (forgetDifferential (h := h)).mono_of_mono_map ‹_›

/-! ### Contractibility and underlying graded exact sequence -/

/-- `inducedObj h E` (`G⁺(E)`) is contractible, hence zero in the curved homotopy category. -/
theorem isZero_homotopy_inducedObj
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (inducedObj h E)) := by
  rw [isZero_homotopy_iff_exists_contraction]
  refine ⟨⟨{ toFun := fun z ↦ mkInducedObj h z.snd 0
             map_add' := fun _ _ ↦ InducedCarrier.ext rfl (add_zero 0).symm
             map_smul' := fun u z ↦ InducedCarrier.ext (by simp) (by simp) }, ?_⟩, fun z ↦ ?_⟩
  · refine dgRightModuleCochains.mem_iff.mpr (LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_)
    dsimp only [LinearMap.restrictScalars_apply, LinearMap.coe_mk, AddHom.coe_mk]
    obtain ⟨_, hz₂⟩ := (mem_inducedGrading_iff p z).mp hz
    exact (mem_inducedGrading_iff (p + -1) _).mpr
      ⟨by simpa only [mkInducedObj_fst, (by omega : p + -1 = p - 1)] using hz₂,
        Submodule.zero_mem _⟩
  · exact InducedCarrier.ext (by simp) (by simp)

/-- `coinducedObj h E` (`G⁻(E)`) is contractible, hence zero in the curved homotopy category. -/
theorem isZero_homotopy_coinducedObj
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (coinducedObj h E)) :=
  (homotopyShiftFunctor (h := h) 1).map_isZero (isZero_homotopy_inducedObj h E)

private noncomputable def inducedProjLinear
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (inducedObj h E) →ₗ[Aᵐᵒᵖ] E.shiftObj 1 where
  toFun z := z.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem inducedProjLinear_apply (z : toGradedModuleCat (inducedObj h E)) :
    inducedProjLinear h E z = z.snd :=
  rfl

/-- The projection `toGradedModuleCat (inducedObj h E) ⟶ E.shiftObj 1` onto the second
coordinate. -/
noncomputable def inducedProj
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (inducedObj h E) ⟶ E.shiftObj 1 :=
  GradedModuleCat.ofHom (inducedProjLinear h E)
    (LinearMap.isHomogeneous_def.mpr fun p z hz ↦ by
      rw [toGradedModuleCat_piece] at hz
      obtain ⟨_, hz₂⟩ := (mem_inducedGrading_iff p z).mp hz
      rw [add_zero, GradedModuleCat.mem_shiftObj_piece_iff, inducedProjLinear_apply]
      exact hz₂)

/-- The composite `E ⟶ toGradedModuleCat (inducedObj h E) ⟶ E.shiftObj 1` is zero. -/
@[simp]
theorem inducedUnit_comp_inducedProj
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedUnit h E ≫ inducedProj h E = 0 :=
  GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- The underlying graded short complex
`0 ⟶ E ⟶ toGradedModuleCat (inducedObj h E) ⟶ E.shiftObj 1 ⟶ 0`. -/
noncomputable abbrev inducedShortComplex
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    ShortComplex (GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :=
  ShortComplex.mk (inducedUnit h E) (inducedProj h E) (inducedUnit_comp_inducedProj h E)

/-- The underlying graded short complex of `inducedObj h E` is short exact. -/
theorem inducedShortComplex_shortExact
    (E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (inducedShortComplex h E).ShortExact where
  mono_f := (GradedModuleCat.mono_iff_injective _).mpr fun e₁ e₂ h₁₂ ↦
    congrArg InducedCarrier.fst h₁₂
  epi_g := (GradedModuleCat.epi_iff_surjective _).mpr fun y ↦ ⟨⟨0, y⟩, rfl⟩
  exact := GradedModuleCat.exact_iff.mpr fun z ↦
    ⟨fun hz ↦ ⟨z.fst, InducedCarrier.ext rfl hz.symm⟩,
     by rintro ⟨e, rfl⟩; rfl⟩

/-- `G⁺(P)` is graded-projective whenever `P` is a projective graded right `A`-module. -/
instance projective_toGradedModuleCat_inducedObj
    (P : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective P] :
    Projective (toGradedModuleCat (inducedObj h P)) := by
  have : Projective (P.shiftObj 1) := GradedModuleCat.projective_shiftObj P 1
  exact projective_iff_hasProjectiveDimensionLT_one.mpr
    ((inducedShortComplex_shortExact h P).hasProjectiveDimensionLT_X₂ 1
      inferInstance inferInstance)

/-- `G⁺(P)` lies in `gradedProjective R h` whenever `P` is projective. -/
theorem gradedProjective_inducedObj
    (P : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective P] :
    gradedProjective R h (DGHomotopyCategory.of R (inducedObj h P)) :=
  (gradedProjective_iff _).mpr (projective_toGradedModuleCat_inducedObj h P)

/-- `G⁺(I)` is graded-injective whenever `I` is an injective graded right `A`-module. -/
instance injective_toGradedModuleCat_inducedObj
    (I : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective I] :
    Injective (toGradedModuleCat (inducedObj h I)) := by
  have : Injective (I.shiftObj 1) := GradedModuleCat.injective_shiftObj I 1
  exact injective_iff_hasInjectiveDimensionLT_one.mpr
    ((inducedShortComplex_shortExact h I).hasInjectiveDimensionLT_X₂ 1
      inferInstance inferInstance)

/-- `G⁻(I)` is graded-injective whenever `I` is an injective graded right `A`-module. -/
instance injective_toGradedModuleCat_coinducedObj
    (I : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective I] :
    Injective (toGradedModuleCat (coinducedObj h I)) :=
  Injective.of_iso
    ((closedShiftFunctorCompForgetDifferentialIso (h := h) 1).app
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h I))).symm
    (GradedModuleCat.injective_shiftObj (toGradedModuleCat (inducedObj h I)) (-1))

/-- `G⁻(I)` lies in `gradedInjective R h` whenever `I` is injective. -/
theorem gradedInjective_coinducedObj
    (I : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective I] :
    gradedInjective R h (DGHomotopyCategory.of R (coinducedObj h I)) :=
  (gradedInjective_iff _).mpr (injective_toGradedModuleCat_coinducedObj h I)

/-! ### Contractible graded-projective and graded-injective presentations -/

/-- Every curved right module admits a closed epimorphism from `inducedObj h P` for a projective
graded right `A`-module `P`. -/
theorem exists_epi_from_inducedObj (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ∃ (P : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
      (_ : Projective P)
      (π : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h P) ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M),
      Epi π := by
  have : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece :=
    (InternalGrading.ofDecomposition_piece 𝒜).symm ▸ inferInstance
  exact ⟨Projective.over (toGradedModuleCat M), inferInstance,
    inducedLift h (Projective.π (toGradedModuleCat M)), inferInstance⟩

/-- Every curved right module admits a closed monomorphism into `coinducedObj h I` for an injective
graded right `A`-module `I`. -/
theorem exists_mono_to_coinducedObj (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ∃ (I : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
      (_ : Injective I)
      (ι : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h I)),
      Mono ι := by
  have : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece :=
    (InternalGrading.ofDecomposition_piece 𝒜).symm ▸ inferInstance
  exact ⟨Injective.under (toGradedModuleCat M), inferInstance,
    coinducedLift h (Injective.ι (toGradedModuleCat M)), inferInstance⟩

end Adjunctions

end TauCeti.CurvedDGRightModuleCat
