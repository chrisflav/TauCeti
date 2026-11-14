/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Injective
public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.Algebra.Homology.Curved.Module.Right.Abelian
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Basic
public import TauCeti.Algebra.Homology.Curved.Module.Right.Homotopy
public import TauCeti.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.CategoryTheory.Functor.EpiMono
import TauCeti.Algebra.Homology.Ext.Equivalence

/-!
# Induced and coinduced curved differential graded right modules

For a curved differential graded algebra `(A, d, w)`, the functor `forgetDifferential` forgetting
the differential of a curved right `A`-module and sending closed morphisms to homogeneous
degree-zero maps of graded right `A`-modules admits both a left adjoint `G⁺` (`inducedFunctor`) and
a right adjoint `G⁻` (`coinducedFunctor`), following Positselski.

Given a graded right `A`-module `U` (represented as an object of
`GradedModuleCat (InternalGrading.ofDecomposition 𝒜).opposite.piece`), the **induced curved module**
`inducedObj h U` (`G⁺(U)`) has underlying `R`-module `U × U` with degree-`p` piece
`U_p × U_{p - 1}`, right `A`-action

`(u₀, u₁) · a = (u₀ · a - (-1)^{|u₁|} u₁ · d a, u₁ · a)`

expressed globally without degree case splits via the Koszul twist `U.grading.koszulTwist 1`, and
curved differential `d⁺(u₀, u₁) = (u₁ · w, u₀)`. Its underlying graded right `A`-module fits into a
canonical short exact sequence

`0 ⟶ U ⟶ toGradedModuleCat (inducedObj h U) ⟶ U{1} ⟶ 0`

whose outer terms are `U` and its grading shift `U{1}`, so `inducedObj h U` inherits every
projective or injective dimension bound of `U` (in particular, it is graded-projective when `U` is
projective, and graded-injective when `U` is injective). At the same time, the odd right `A`-linear
endomorphism `(u₀, u₁) ↦ (u₁, 0)` is a contracting homotopy of `inducedObj h U`, so `inducedObj h U`
is zero in the curved homotopy category.

The **coinduced curved module** `coinducedObj h U` (`G⁻(U)`) is `inducedObj h (U{-1})`, which
carries a natural counit `toGradedModuleCat (coinducedObj h U) ⟶ U` sending `(v₀, v₁) ↦ v₁` and
universal lift `m ↦ (g (d_M m), g m)` for any graded morphism `g : toGradedModuleCat M ⟶ U`.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.inducedObj` and `TauCeti.CurvedDGRightModuleCat.coinducedObj`:
  the induced (`G⁺`) and coinduced (`G⁻`) curved right modules of a graded right module.
* `TauCeti.CurvedDGRightModuleCat.inducedShortComplex`: the short exact sequence
  `0 ⟶ U ⟶ toGradedModuleCat (inducedObj h U) ⟶ U{1} ⟶ 0` of graded right modules.
* `TauCeti.CurvedDGRightModuleCat.inducedFunctor` and
  `TauCeti.CurvedDGRightModuleCat.coinducedFunctor`: the left and right adjoint functors to
  `forgetDifferential`, with adjunctions `inducedAdjunction` and `coinducedAdjunction`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.inducedShortComplex_shortExact`: exactness of the underlying
  graded extension of `inducedObj h U`.
* `TauCeti.CurvedDGRightModuleCat.hasProjectiveDimensionLT_toGradedModuleCat_inducedObj` and
  `TauCeti.CurvedDGRightModuleCat.hasInjectiveDimensionLT_toGradedModuleCat_coinducedObj`:
  preservation of graded projective and injective dimension bounds under `G⁺` and `G⁻`.
* `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_inducedObj` and
  `TauCeti.CurvedDGRightModuleCat.isZero_homotopy_coinducedObj`: contractibility of induced and
  coinduced curved right modules in the curved homotopy category.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.2 (proof of Lemma 3.2)
  and Section 3.6 (proof of Theorem 3.6(a)).
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6.
-/

public section

open CategoryTheory CategoryTheory.Limits MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe uR uA uM u

section Objects

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- Global Koszul-twisted form of the right Leibniz rule on a curved right module: for every
(not necessarily homogeneous) element `m : M` and `a : A`,
`d_M (m · a) = d_M m · a + (τ m) · d a`. -/
theorem differential_op_smul {h : IsCurvedDGAlgebra 𝒜 d w}
    (M : CurvedDGRightModuleCat.{uR, uA, uM} h) (a : A) (m : M) :
    M.differential (op a • m) =
      op a • M.differential m +
        op (d a) • (InternalGrading.ofDecomposition M.grading).koszulTwist 1 m := by
  induction m using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x y hx hy =>
    simp only [smul_add, map_add, hx, hy]
    abel
  | @homogeneous q x =>
    have hx' : (x : M) ∈ (InternalGrading.ofDecomposition M.grading).piece q := by
      simpa only [InternalGrading.ofDecomposition_piece] using x.2
    rw [M.isCurvedDGRightModule.leibniz x.2 a,
      (InternalGrading.ofDecomposition M.grading).koszulTwist_one_apply_of_mem hx',
      Int.cast_smul_eq_zsmul R (q.negOnePow : ℤ), ← Units.smul_def,
      smul_comm (op (d a)) q.negOnePow (x : M)]

/-- Private carrier of `inducedObj h U`, wrapping `U × U` with explicit algebra parameters so its
twisted right `A`-module instance has no undetermined typeclass metavariables. -/
@[ext]
private structure InducedCarrier (R : Type uR) (A : Type uA) [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A) (w : A)
    (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) : Type uM where
  fst : U
  snd : U

section InducedCarrierInstances

variable (h : IsCurvedDGAlgebra 𝒜 d w)
  (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)

private instance : AddCommGroup (InducedCarrier R A 𝒜 d w h U) where
  zero := ⟨0, 0⟩
  add x y := ⟨x.fst + y.fst, x.snd + y.snd⟩
  neg x := ⟨-x.fst, -x.snd⟩
  sub x y := ⟨x.fst - y.fst, x.snd - y.snd⟩
  nsmul n x := ⟨n • x.fst, n • x.snd⟩
  zsmul n x := ⟨n • x.fst, n • x.snd⟩
  add_assoc _ _ _ := InducedCarrier.ext (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add _ := InducedCarrier.ext (zero_add _) (zero_add _)
  add_zero _ := InducedCarrier.ext (add_zero _) (add_zero _)
  nsmul_zero _ := InducedCarrier.ext (zero_smul _ _) (zero_smul _ _)
  nsmul_succ _ _ := InducedCarrier.ext (succ_nsmul _ _) (succ_nsmul _ _)
  sub_eq_add_neg _ _ := InducedCarrier.ext (sub_eq_add_neg _ _) (sub_eq_add_neg _ _)
  zsmul_zero' _ := InducedCarrier.ext (zero_smul _ _) (zero_smul _ _)
  zsmul_succ' _ _ := InducedCarrier.ext (SubNegMonoid.zsmul_succ' _ _)
    (SubNegMonoid.zsmul_succ' _ _)
  zsmul_neg' _ _ := InducedCarrier.ext (SubNegMonoid.zsmul_neg' _ _)
    (SubNegMonoid.zsmul_neg' _ _)
  neg_add_cancel _ := InducedCarrier.ext (neg_add_cancel _) (neg_add_cancel _)
  add_comm _ _ := InducedCarrier.ext (add_comm _ _) (add_comm _ _)

@[simp]
private theorem inducedCarrier_zero_fst : (0 : InducedCarrier R A 𝒜 d w h U).fst = 0 := rfl

@[simp]
private theorem inducedCarrier_zero_snd : (0 : InducedCarrier R A 𝒜 d w h U).snd = 0 := rfl

@[simp]
private theorem inducedCarrier_add_fst (x y : InducedCarrier R A 𝒜 d w h U) :
    (x + y).fst = x.fst + y.fst := rfl

@[simp]
private theorem inducedCarrier_add_snd (x y : InducedCarrier R A 𝒜 d w h U) :
    (x + y).snd = x.snd + y.snd := rfl

private instance : Module R (InducedCarrier R A 𝒜 d w h U) where
  smul r x := ⟨r • x.fst, r • x.snd⟩
  one_smul _ := InducedCarrier.ext (one_smul _ _) (one_smul _ _)
  mul_smul _ _ _ := InducedCarrier.ext (mul_smul _ _ _) (mul_smul _ _ _)
  smul_zero _ := InducedCarrier.ext (smul_zero _) (smul_zero _)
  smul_add _ _ _ := InducedCarrier.ext (smul_add _ _ _) (smul_add _ _ _)
  add_smul _ _ _ := InducedCarrier.ext (add_smul _ _ _) (add_smul _ _ _)
  zero_smul _ := InducedCarrier.ext (zero_smul _ _) (zero_smul _ _)

@[simp]
private theorem inducedCarrier_smul_base_fst (r : R) (x : InducedCarrier R A 𝒜 d w h U) :
    (r • x).fst = r • x.fst := rfl

@[simp]
private theorem inducedCarrier_smul_base_snd (r : R) (x : InducedCarrier R A 𝒜 d w h U) :
    (r • x).snd = r • x.snd := rfl

@[simp]
private theorem inducedCarrier_units_smul_fst (u : ℤˣ) (x : InducedCarrier R A 𝒜 d w h U) :
    (u • x).fst = u • x.fst := rfl

@[simp]
private theorem inducedCarrier_units_smul_snd (u : ℤˣ) (x : InducedCarrier R A 𝒜 d w h U) :
    (u • x).snd = u • x.snd := rfl

private theorem koszulTwist_op_smul_of_mem {r : ℤ} {b : A} (hb : b ∈ 𝒜 r) (u : U) :
    U.grading.koszulTwist 1 (op b • u) =
      r.negOnePow • (op b • U.grading.koszulTwist 1 u) := by
  let smulLinear : U →ₗ[R] U :=
    { toFun := fun v ↦ op b • v
      map_add' := smul_add (op b)
      map_smul' := fun c v ↦ smul_comm (op b) c v }
  have hsmul : LinearMap.IsHomogeneous smulLinear U.grading.piece U.grading.piece r :=
    LinearMap.isHomogeneous_def.mpr fun q x hx ↦
      op_smul_mem_of_mem_graded (ℳ := U.grading.piece) hb hx
  simpa only [smulLinear, LinearMap.coe_mk, AddHom.coe_mk, one_mul,
    Int.cast_smul_eq_zsmul R (r.negOnePow : ℤ), ← Units.smul_def] using
    hsmul.koszulTwist_apply 1 u

private noncomputable instance : SMul Aᵐᵒᵖ (InducedCarrier R A 𝒜 d w h U) where
  smul a x := ⟨a • x.fst - op (d a.unop) • U.grading.koszulTwist 1 x.snd, a • x.snd⟩

@[simp]
private theorem inducedCarrier_smul_op_fst (a : Aᵐᵒᵖ) (x : InducedCarrier R A 𝒜 d w h U) :
    (a • x).fst = a • x.fst - op (d a.unop) • U.grading.koszulTwist 1 x.snd := rfl

@[simp]
private theorem inducedCarrier_smul_op_snd (a : Aᵐᵒᵖ) (x : InducedCarrier R A 𝒜 d w h U) :
    (a • x).snd = a • x.snd := rfl

private noncomputable instance : Module Aᵐᵒᵖ (InducedCarrier R A 𝒜 d w h U) where
  one_smul x := InducedCarrier.ext
    (by simp [h.map_one_eq_zero])
    (one_smul _ _)
  mul_smul a b x := by
    refine InducedCarrier.ext ?_ (mul_smul a b x.snd)
    induction a using MulOpposite.rec' with | h a => ?_
    induction b using MulOpposite.rec' with | h b => ?_
    rw [← op_mul, inducedCarrier_smul_op_fst, inducedCarrier_smul_op_fst,
      inducedCarrier_smul_op_fst, inducedCarrier_smul_op_snd, unop_op, unop_op, unop_op]
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add b₁ b₂ hb₁ hb₂ =>
      simp only [add_mul, MulOpposite.op_add, add_smul, map_add, smul_add] at hb₁ hb₂ ⊢
      calc
        op (b₁ * a) • x.fst + op (b₂ * a) • x.fst -
            (op (d (b₁ * a)) • U.grading.koszulTwist 1 x.snd +
              op (d (b₂ * a)) • U.grading.koszulTwist 1 x.snd)
          = (op (b₁ * a) • x.fst - op (d (b₁ * a)) • U.grading.koszulTwist 1 x.snd) +
              (op (b₂ * a) • x.fst - op (d (b₂ * a)) • U.grading.koszulTwist 1 x.snd) := by abel
        _ = (op a • (op b₁ • x.fst - op (d b₁) • U.grading.koszulTwist 1 x.snd) -
              op (d a) • U.grading.koszulTwist 1 (op b₁ • x.snd)) +
            (op a • (op b₂ • x.fst - op (d b₂) • U.grading.koszulTwist 1 x.snd) -
              op (d a) • U.grading.koszulTwist 1 (op b₂ • x.snd)) := by rw [hb₁, hb₂]
        _ = op a • (op b₁ • x.fst + op b₂ • x.fst -
              (op (d b₁) • U.grading.koszulTwist 1 x.snd +
                op (d b₂) • U.grading.koszulTwist 1 x.snd)) -
            (op (d a) • U.grading.koszulTwist 1 (op b₁ • x.snd) +
              op (d a) • U.grading.koszulTwist 1 (op b₂ • x.snd)) := by
          simp only [smul_sub, smul_add]
          abel
    | @homogeneous r b =>
      rw [h.leibniz b.2 a, koszulTwist_op_smul_of_mem U b.2 x.snd]
      rcases Int.units_eq_one_or r.negOnePow with hr | hr
      · simp only [hr, one_smul, MulOpposite.op_add, add_smul, op_mul, mul_smul, smul_sub]
        abel
      · simp [hr, MulOpposite.op_add, add_smul, op_mul, mul_smul, smul_sub]
        abel
  smul_zero a := InducedCarrier.ext (by simp) (smul_zero _)
  smul_add a x y := InducedCarrier.ext
    (by
      simp only [inducedCarrier_smul_op_fst, inducedCarrier_add_fst, inducedCarrier_add_snd,
        smul_add, map_add]
      abel)
    (smul_add _ _ _)
  add_smul a b x := InducedCarrier.ext
    (by
      simp only [inducedCarrier_smul_op_fst, inducedCarrier_add_fst, add_smul,
        MulOpposite.unop_add, map_add, MulOpposite.op_add]
      abel)
    (add_smul _ _ _)
  zero_smul x := InducedCarrier.ext (by simp) (zero_smul _ _)

private instance : IsScalarTower R Aᵐᵒᵖ (InducedCarrier R A 𝒜 d w h U) where
  smul_assoc r a x := InducedCarrier.ext
    (by
      simp only [inducedCarrier_smul_op_fst, inducedCarrier_smul_base_fst, unop_smul, map_smul,
        op_smul, smul_assoc, smul_comm r, smul_sub])
    (smul_assoc r a x.snd)

private def inducedProdEquiv : InducedCarrier R A 𝒜 d w h U ≃ₗ[R] U × U where
  toFun x := (x.fst, x.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def inducedInternalGrading :
    InternalGrading R (InducedCarrier R A 𝒜 d w h U) ℤ :=
  (U.grading.prod (U.grading.shift (-1))).map (inducedProdEquiv h U).symm

private theorem mem_inducedInternalGrading_piece_iff (p : ℤ)
    (x : InducedCarrier R A 𝒜 d w h U) :
    x ∈ (inducedInternalGrading h U).piece p ↔
      x.fst ∈ U.grading.piece p ∧ x.snd ∈ U.grading.piece (p - 1) := by
  simp only [inducedInternalGrading, InternalGrading.map_piece, Submodule.mem_map,
    InternalGrading.prod_piece, Submodule.mem_prod, InternalGrading.shift_piece,
    LinearEquiv.coe_toLinearMap, ← sub_eq_add_neg]
  exact ⟨by rintro ⟨⟨a, b⟩, hab, rfl⟩; exact hab, fun hx ↦ ⟨(x.fst, x.snd), hx, rfl⟩⟩

private noncomputable instance :
    SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
      (inducedInternalGrading h U).piece where
  smul_mem {i j a x} ha hx := by
    rw [mem_inducedInternalGrading_piece_iff] at hx ⊢
    rw [vadd_eq_add, inducedCarrier_smul_op_fst, inducedCarrier_smul_op_snd]
    have ha' : a.unop ∈ 𝒜 i := by
      simpa only [InternalGrading.mem_opposite_piece_iff,
        InternalGrading.ofDecomposition_piece] using ha
    have hda : op (d a.unop) • U.grading.koszulTwist 1 x.snd ∈ U.grading.piece (i + j) := by
      simpa only [show j - 1 + (i + 1) = i + j by omega] using
        op_smul_mem_of_mem_graded (ℳ := U.grading.piece) (h.map_mem ha')
          (U.grading.koszulTwist_mem_piece hx.2 1)
    refine ⟨Submodule.sub_mem _ (SetLike.GradedSMul.smul_mem ha hx.1) hda, ?_⟩
    simpa only [vadd_eq_add, show i + (j - 1) = i + j - 1 by omega] using
      SetLike.GradedSMul.smul_mem ha hx.2

private def inducedDifferential :
    InducedCarrier R A 𝒜 d w h U →ₗ[R] InducedCarrier R A 𝒜 d w h U where
  toFun x := ⟨op w • x.snd, x.fst⟩
  map_add' _ _ := InducedCarrier.ext (smul_add _ _ _) rfl
  map_smul' r x := InducedCarrier.ext (smul_comm (op w) r x.snd) rfl

@[simp]
private theorem inducedDifferential_fst (x : InducedCarrier R A 𝒜 d w h U) :
    (inducedDifferential h U x).fst = op w • x.snd := rfl

@[simp]
private theorem inducedDifferential_snd (x : InducedCarrier R A 𝒜 d w h U) :
    (inducedDifferential h U x).snd = x.fst := rfl

private theorem isCurvedDGRightModule_inducedCarrier :
    IsCurvedDGRightModule h (inducedInternalGrading h U).piece (inducedDifferential h U) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
    rw [mem_inducedInternalGrading_piece_iff] at hx ⊢
    refine ⟨?_, ?_⟩
    · simpa only [inducedDifferential_fst, show p - 1 + 2 = p + 1 by omega] using
        op_smul_mem_of_mem_graded (ℳ := U.grading.piece) h.curvature_mem hx.2
    · simpa only [inducedDifferential_snd, add_sub_cancel_right] using hx.1
  leibniz {p x} hx a := by
    rw [mem_inducedInternalGrading_piece_iff] at hx
    have hτ₁ : U.grading.koszulTwist 1 x.fst = p.negOnePow • x.fst := by
      rw [U.grading.koszulTwist_one_apply_of_mem hx.1, Int.cast_smul_eq_zsmul R,
        ← Units.smul_def]
    have hsign : (p - 1).negOnePow = -p.negOnePow := by
      rw [sub_eq_add_neg, Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one, mul_neg,
        mul_one]
    have hτ₂ : U.grading.koszulTwist 1 x.snd = -(p.negOnePow • x.snd) := by
      rw [U.grading.koszulTwist_one_apply_of_mem hx.2, hsign, Units.val_neg, Int.cast_neg,
        neg_smul, Int.cast_smul_eq_zsmul R, ← Units.smul_def]
    refine InducedCarrier.ext ?_ ?_
    · simp only [inducedDifferential_fst, inducedDifferential_snd, inducedCarrier_smul_op_fst,
        inducedCarrier_smul_op_snd, inducedCarrier_add_fst, inducedCarrier_units_smul_fst,
        unop_op]
      rw [hτ₁, hτ₂, h.sq_eq a, smul_neg, sub_neg_eq_add, smul_comm (op (d a)) p.negOnePow,
        ← mul_smul, ← mul_smul, ← op_mul, ← op_mul, MulOpposite.op_sub, sub_smul]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp
      · simp only [hp, one_smul]
        abel
      · simp [hp]
    · simp only [inducedDifferential_snd, inducedCarrier_smul_op_fst, inducedCarrier_smul_op_snd,
        inducedCarrier_add_snd, inducedCarrier_units_smul_snd, unop_op]
      rw [hτ₂, smul_neg, sub_neg_eq_add, smul_comm (op (d a)) p.negOnePow]
  sq_eq x := InducedCarrier.ext
    (by simp [h.map_curvature])
    rfl

end InducedCarrierInstances

/-- **The induced curved differential graded right module** `G⁺(U)` attached to a graded right
`A`-module `U`. Its underlying graded `R`-module is `U ⊕ U{1}` with Koszul-twisted right
`A`-action and curved differential `(u₀, u₁) ↦ (u₁ · w, u₀)`. -/
noncomputable def inducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{uR, uA, uM} h where
  carrier := InducedCarrier R A 𝒜 d w h U
  grading := (inducedInternalGrading h U).piece
  differential := inducedDifferential h U
  isCurvedDGRightModule := isCurvedDGRightModule_inducedCarrier h U

/-- Private projection to the first component of `inducedObj h U`. -/
private noncomputable def inducedFstFn (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (x : inducedObj h U) : U :=
  InducedCarrier.fst x

/-- Private projection to the second component of `inducedObj h U`. -/
private noncomputable def inducedSndFn (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (x : inducedObj h U) : U :=
  InducedCarrier.snd x

/-- Private constructor for elements of `inducedObj h U`. -/
private noncomputable def inducedMk (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (u₀ u₁ : U) : inducedObj h U :=
  InducedCarrier.mk u₀ u₁

private theorem inducedObj_ext {h : IsCurvedDGAlgebra 𝒜 d w}
    {U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {x y : inducedObj h U}
    (h₁ : inducedFstFn h U x = inducedFstFn h U y)
    (h₂ : inducedSndFn h U x = inducedSndFn h U y) : x = y :=
  InducedCarrier.ext h₁ h₂

private theorem mem_inducedObj_grading_iff (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (p : ℤ) (x : inducedObj h U) :
    x ∈ (inducedObj h U).grading p ↔
      inducedFstFn h U x ∈ U.grading.piece p ∧
        inducedSndFn h U x ∈ U.grading.piece (p - 1) :=
  mem_inducedInternalGrading_piece_iff h U p x

@[simp]
private theorem inducedFstFn_mk (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (u₀ u₁ : U) : inducedFstFn h U (inducedMk h U u₀ u₁) = u₀ := rfl

@[simp]
private theorem inducedSndFn_mk (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (u₀ u₁ : U) : inducedSndFn h U (inducedMk h U u₀ u₁) = u₁ := rfl

@[simp]
private theorem inducedFstFn_zero (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedFstFn h U 0 = 0 := rfl

@[simp]
private theorem inducedSndFn_zero (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedSndFn h U 0 = 0 := rfl

@[simp]
private theorem inducedFstFn_add (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (x y : inducedObj h U) :
    inducedFstFn h U (x + y) = inducedFstFn h U x + inducedFstFn h U y := rfl

@[simp]
private theorem inducedSndFn_add (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (x y : inducedObj h U) :
    inducedSndFn h U (x + y) = inducedSndFn h U x + inducedSndFn h U y := rfl

@[simp]
private theorem inducedFstFn_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : Aᵐᵒᵖ) (x : inducedObj h U) :
    inducedFstFn h U (a • x) =
      a • inducedFstFn h U x - op (d a.unop) • U.grading.koszulTwist 1 (inducedSndFn h U x) :=
  rfl

@[simp]
private theorem inducedSndFn_smul (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (a : Aᵐᵒᵖ) (x : inducedObj h U) :
    inducedSndFn h U (a • x) = a • inducedSndFn h U x := rfl

@[simp]
private theorem inducedFstFn_differential (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (x : inducedObj h U) :
    inducedFstFn h U ((inducedObj h U).differential x) = op w • inducedSndFn h U x := rfl

@[simp]
private theorem inducedSndFn_differential (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (x : inducedObj h U) :
    inducedSndFn h U ((inducedObj h U).differential x) = inducedFstFn h U x := rfl

private noncomputable def inducedInlLinear (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    U →ₗ[Aᵐᵒᵖ] inducedObj h U where
  toFun u := inducedMk h U u 0
  map_add' u v := inducedObj_ext (by simp) (by simp)
  map_smul' a u := inducedObj_ext (by simp) (by simp)

private noncomputable def inducedSndLinear (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedObj h U →ₗ[Aᵐᵒᵖ] U where
  toFun := inducedSndFn h U
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The homogeneous degree-zero right `A`-linear inclusion `u ↦ (u, 0)` of `U` into the underlying
graded module of `inducedObj h U`; this is the unit of `inducedFunctor h ⊣ forgetDifferential`. -/
noncomputable def inducedInl (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    U ⟶ toGradedModuleCat (inducedObj h U) :=
  GradedModuleCat.ofHom
    { toFun := fun u ↦ inducedMk h U u 0
      map_add' := (inducedInlLinear h U).map_add'
      map_smul' := (inducedInlLinear h U).map_smul' }
    (LinearMap.isHomogeneous_def.mpr fun p u hu ↦ by
      rw [toGradedModuleCat_piece, add_zero]
      exact (mem_inducedObj_grading_iff h U p _).mpr ⟨hu, Submodule.zero_mem _⟩)

@[simp]
private theorem inducedInl_hom_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (u : U) :
    (inducedInl h U).hom u = inducedMk h U u 0 := rfl

/-- The homogeneous degree-zero right `A`-linear projection `(u₀, u₁) ↦ u₁` from the underlying
graded module of `inducedObj h U` onto `U{1}`. -/
noncomputable def inducedSnd (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (inducedObj h U) ⟶ U.shiftObj 1 :=
  GradedModuleCat.ofHom
    { toFun := inducedSndFn h U
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      rw [toGradedModuleCat_piece] at hx
      rw [add_zero, GradedModuleCat.mem_shiftObj_piece_iff]
      exact ((mem_inducedObj_grading_iff h U p x).mp hx).2)

@[simp]
private theorem inducedSnd_hom_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (x : toGradedModuleCat (inducedObj h U)) :
    (inducedSnd h U).hom x = inducedSndFn h U x := rfl

/-- The composite `inducedInl h U ≫ inducedSnd h U` is zero. -/
@[simp]
theorem inducedInl_comp_inducedSnd (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    inducedInl h U ≫ inducedSnd h U = 0 :=
  GradedModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl

/-- The canonical short complex `0 ⟶ U ⟶ toGradedModuleCat (inducedObj h U) ⟶ U{1} ⟶ 0` of graded
right `A`-modules. -/
noncomputable abbrev inducedShortComplex (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    ShortComplex (GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :=
  ShortComplex.mk (inducedInl h U) (inducedSnd h U) (inducedInl_comp_inducedSnd h U)

/-- **Exactness of the induced graded extension.** Forgetting the differential fits `inducedObj h U`
into a short exact sequence `0 ⟶ U ⟶ toGradedModuleCat (inducedObj h U) ⟶ U{1} ⟶ 0`. -/
theorem inducedShortComplex_shortExact (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (inducedShortComplex h U).ShortExact where
  mono_f := (GradedModuleCat.mono_iff_injective _).mpr fun u v huv ↦ by
    have h' := congrArg (inducedFstFn h U) huv
    simpa only [inducedInl_hom_apply, inducedFstFn_mk] using h'
  epi_g := (GradedModuleCat.epi_iff_surjective _).mpr fun u₁ ↦
    ⟨inducedMk h U 0 (u₁ : U), inducedSndFn_mk h U 0 (u₁ : U)⟩
  exact := GradedModuleCat.exact_iff.mpr fun x ↦ by
    refine ⟨fun hx ↦ ⟨inducedFstFn h U x, ?_⟩, ?_⟩
    · have hx' : inducedSndFn h U x = 0 := hx
      exact inducedObj_ext
        (by simp)
        (by simp [hx'])
    · rintro ⟨_, rfl⟩
      rfl

/-- `inducedObj h U` preserves every projective-dimension bound `< n` of `U`. -/
theorem hasProjectiveDimensionLT_toGradedModuleCat_inducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (n : ℕ)
    [HasProjectiveDimensionLT U n] :
    HasProjectiveDimensionLT (toGradedModuleCat (inducedObj h U)) n := by
  have hshift : HasProjectiveDimensionLT (U.shiftObj 1) n := by
    have : HasProjectiveDimensionLT (((GradedModuleCat.shift _) ^ (1 : ℤ)).functor.obj U) n :=
      (((GradedModuleCat.shift _) ^ (1 : ℤ)).hasProjectiveDimensionLT_functor_obj_iff U n).mpr ‹_›
    exact hasProjectiveDimensionLT_of_iso ((GradedModuleCat.shiftPowIso _ 1).app U) n
  exact (inducedShortComplex_shortExact h U).hasProjectiveDimensionLT_X₂ n ‹_› hshift

/-- `inducedObj h U` preserves every injective-dimension bound `< n` of `U`. -/
theorem hasInjectiveDimensionLT_toGradedModuleCat_inducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (n : ℕ)
    [HasInjectiveDimensionLT U n] :
    HasInjectiveDimensionLT (toGradedModuleCat (inducedObj h U)) n := by
  have hshift : HasInjectiveDimensionLT (U.shiftObj 1) n := by
    have : HasInjectiveDimensionLT (((GradedModuleCat.shift _) ^ (1 : ℤ)).functor.obj U) n :=
      (((GradedModuleCat.shift _) ^ (1 : ℤ)).hasInjectiveDimensionLT_functor_obj_iff U n).mpr ‹_›
    exact hasInjectiveDimensionLT_of_iso ((GradedModuleCat.shiftPowIso _ 1).app U) n
  exact (inducedShortComplex_shortExact h U).hasInjectiveDimensionLT_X₂ n ‹_› hshift

/-- When `U` is projective in `GradedModuleCat`, `inducedObj h U` is graded-projective. -/
instance projective_toGradedModuleCat_inducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective U] :
    Projective (toGradedModuleCat (inducedObj h U)) := by
  have : HasProjectiveDimensionLT U 1 := projective_iff_hasProjectiveDimensionLT_one.mp ‹_›
  have := hasProjectiveDimensionLT_toGradedModuleCat_inducedObj h U 1
  exact projective_iff_hasProjectiveDimensionLT_one.mpr this

/-- When `U` is injective in `GradedModuleCat`, `inducedObj h U` is graded-injective. -/
instance injective_toGradedModuleCat_inducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective U] :
    Injective (toGradedModuleCat (inducedObj h U)) := by
  have : HasInjectiveDimensionLT U 1 := injective_iff_hasInjectiveDimensionLT_one.mp ‹_›
  have := hasInjectiveDimensionLT_toGradedModuleCat_inducedObj h U 1
  exact injective_iff_hasInjectiveDimensionLT_one.mpr this

/-- **The coinduced curved differential graded right module** `G⁻(U)` attached to a graded right
`A`-module `U`, realized as `inducedObj h (U{-1})` so its degree-`p` piece is `U_{p + 1} × U_p`. -/
noncomputable abbrev coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    CurvedDGRightModuleCat.{uR, uA, uM} h :=
  inducedObj h (U.shiftObj (-1))

/-- The homogeneous degree-zero right `A`-linear counit `(v₀, v₁) ↦ v₁` from the underlying graded
module of `coinducedObj h U` to `U`; this is the counit of
`forgetDifferential ⊣ coinducedFunctor`. -/
noncomputable def coinducedCounit (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    toGradedModuleCat (coinducedObj h U) ⟶ U :=
  GradedModuleCat.ofHom
    { toFun := inducedSndFn h (U.shiftObj (-1))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      rw [toGradedModuleCat_piece] at hx
      have hx₂ := ((mem_inducedObj_grading_iff h (U.shiftObj (-1)) p x).mp hx).2
      rw [GradedModuleCat.mem_shiftObj_piece_iff, show p - 1 - -1 = p + 0 by omega] at hx₂
      exact hx₂)

@[simp]
private theorem coinducedCounit_hom_apply (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
    (x : toGradedModuleCat (coinducedObj h U)) :
    (coinducedCounit h U).hom x = inducedSndFn h (U.shiftObj (-1)) x := rfl

/-- `coinducedObj h U` preserves every projective-dimension bound `< n` of `U`. -/
theorem hasProjectiveDimensionLT_toGradedModuleCat_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (n : ℕ)
    [HasProjectiveDimensionLT U n] :
    HasProjectiveDimensionLT (toGradedModuleCat (coinducedObj h U)) n := by
  have : HasProjectiveDimensionLT (U.shiftObj (-1)) n := by
    have : HasProjectiveDimensionLT (((GradedModuleCat.shift _) ^ (-1 : ℤ)).functor.obj U) n :=
      (((GradedModuleCat.shift _) ^ (-1 : ℤ)).hasProjectiveDimensionLT_functor_obj_iff U n).mpr ‹_›
    exact hasProjectiveDimensionLT_of_iso ((GradedModuleCat.shiftPowIso _ (-1)).app U) n
  exact hasProjectiveDimensionLT_toGradedModuleCat_inducedObj h (U.shiftObj (-1)) n

/-- `coinducedObj h U` preserves every injective-dimension bound `< n` of `U`. -/
theorem hasInjectiveDimensionLT_toGradedModuleCat_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) (n : ℕ)
    [HasInjectiveDimensionLT U n] :
    HasInjectiveDimensionLT (toGradedModuleCat (coinducedObj h U)) n := by
  have : HasInjectiveDimensionLT (U.shiftObj (-1)) n := by
    have : HasInjectiveDimensionLT (((GradedModuleCat.shift _) ^ (-1 : ℤ)).functor.obj U) n :=
      (((GradedModuleCat.shift _) ^ (-1 : ℤ)).hasInjectiveDimensionLT_functor_obj_iff U n).mpr ‹_›
    exact hasInjectiveDimensionLT_of_iso ((GradedModuleCat.shiftPowIso _ (-1)).app U) n
  exact hasInjectiveDimensionLT_toGradedModuleCat_inducedObj h (U.shiftObj (-1)) n

/-- When `U` is projective in `GradedModuleCat`, `coinducedObj h U` is graded-projective. -/
instance projective_toGradedModuleCat_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Projective U] :
    Projective (toGradedModuleCat (coinducedObj h U)) :=
  projective_toGradedModuleCat_inducedObj h (U.shiftObj (-1))

/-- When `U` is injective in `GradedModuleCat`, `coinducedObj h U` is graded-injective. -/
instance injective_toGradedModuleCat_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece) [Injective U] :
    Injective (toGradedModuleCat (coinducedObj h U)) :=
  injective_toGradedModuleCat_inducedObj h (U.shiftObj (-1))

end Objects

/-! ### Contractibility and universal properties in the closed and homotopy categories -/

section Categorical

attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- **Every induced curved module is contractible.** The odd right `A`-linear map
`(u₀, u₁) ↦ (u₁, 0)` satisfies `d⁺ k + k d⁺ = id`, so `inducedObj h U` is zero in the curved
homotopy category. -/
theorem isZero_homotopy_inducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (inducedObj h U)) := by
  rw [isZero_homotopy_iff_exists_contraction]
  let k : inducedObj h U →ₗ[Aᵐᵒᵖ] inducedObj h U :=
    (inducedInlLinear h U).comp (inducedSndLinear h U)
  have hk (x : inducedObj h U) : k x = inducedMk h U (inducedSndFn h U x) 0 := rfl
  refine ⟨⟨k, ?_⟩, fun x ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p x hx
    rw [LinearMap.restrictScalars_apply, hk]
    have hx₂ : inducedSndFn h U x ∈ U.grading.piece (p + -1) := by
      simpa only [sub_eq_add_neg] using ((mem_inducedObj_grading_iff h U p x).mp hx).2
    exact (mem_inducedObj_grading_iff h U (p + -1) _).mpr ⟨hx₂, Submodule.zero_mem _⟩
  · exact inducedObj_ext (by simp [hk]) (by simp [hk])

/-- **Every coinduced curved module is contractible** in the curved homotopy category. -/
theorem isZero_homotopy_coinducedObj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    IsZero (DGHomotopyCategory.of R (coinducedObj h U)) :=
  isZero_homotopy_inducedObj h (U.shiftObj (-1))

section InducedAdjunction

variable {h : IsCurvedDGAlgebra 𝒜 d w}

private noncomputable abbrev gradedHomLinear
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (f : U ⟶ toGradedModuleCat M) : U →ₗ[R] M :=
  f.hom.restrictScalars R

private noncomputable def inducedDescLinear
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (f : U ⟶ toGradedModuleCat M) : inducedObj h U →ₗ[Aᵐᵒᵖ] M := by
  let fR : U →ₗ[R] M := gradedHomLinear f
  have hfR : LinearMap.IsHomogeneous fR U.grading.piece
      (InternalGrading.ofDecomposition M.grading).piece 0 :=
    LinearMap.isHomogeneous_def.mpr fun p u hu ↦ by
      have hu' := f.isHomogeneous.map_mem hu
      rw [toGradedModuleCat_piece] at hu'
      rw [InternalGrading.ofDecomposition_piece]
      exact hu'
  have hτ (u : U) :
      (InternalGrading.ofDecomposition M.grading).koszulTwist 1 (fR u) =
        fR (U.grading.koszulTwist 1 u) := by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul] using
      hfR.koszulTwist_apply 1 u
  refine
    { toFun := fun x ↦ fR (inducedFstFn h U x) + M.differential (fR (inducedSndFn h U x))
      map_add' := fun x y ↦ by
        simp only [inducedFstFn_add, inducedSndFn_add, map_add]
        abel
      map_smul' := fun a x ↦ ?_ }
  induction a using MulOpposite.rec' with | h a => ?_
  have hfR_smul (b : A) (u : U) : fR (op b • u) = op b • fR u :=
    f.hom.map_smul (op b) u
  simp only [RingHom.id_apply, inducedFstFn_smul, inducedSndFn_smul, unop_op, map_sub,
    hfR_smul, differential_op_smul M a, hτ, smul_add]
  abel

@[simp]
private theorem inducedDescLinear_apply
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (f : U ⟶ toGradedModuleCat M) (x : inducedObj h U) :
    inducedDescLinear f x =
      gradedHomLinear f (inducedFstFn h U x) +
        M.differential (gradedHomLinear f (inducedSndFn h U x)) :=
  rfl

/-- Universal closed morphism `(u₀, u₁) ↦ f u₀ + d_M (f u₁)` out of `inducedObj h U` associated to
a graded morphism `f : U ⟶ toGradedModuleCat M`. -/
noncomputable def inducedDesc
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (f : U ⟶ toGradedModuleCat M) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h U) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  closedHomOf (M := inducedObj h U) (N := M) (inducedDescLinear f)
    (fun p x hx ↦ by
      obtain ⟨hx₁, hx₂⟩ := (mem_inducedObj_grading_iff h U p x).mp hx
      have hf₁ : gradedHomLinear f (inducedFstFn h U x) ∈ M.grading p := by
        have h₁ := f.isHomogeneous.map_mem hx₁
        rwa [toGradedModuleCat_piece, add_zero] at h₁
      have hf₂ : gradedHomLinear f (inducedSndFn h U x) ∈ M.grading (p - 1) := by
        have h₂ := f.isHomogeneous.map_mem hx₂
        rwa [toGradedModuleCat_piece, add_zero] at h₂
      have hdf₂ : M.differential (gradedHomLinear f (inducedSndFn h U x)) ∈ M.grading p := by
        simpa only [sub_add_cancel] using M.isCurvedDGRightModule.isHomogeneous.map_mem hf₂
      rw [inducedDescLinear_apply]
      exact Submodule.add_mem _ hf₁ hdf₂)
    (fun x ↦ by
      rw [inducedDescLinear_apply, inducedDescLinear_apply, map_add,
        M.isCurvedDGRightModule.sq_eq, inducedFstFn_differential, inducedSndFn_differential]
      have hfw :
          gradedHomLinear f (op w • inducedSndFn h U x) =
            op w • gradedHomLinear f (inducedSndFn h U x) :=
        f.hom.map_smul (op w) _
      rw [hfw, add_comm])

/-- Precomposing `inducedDesc f` with the unit `inducedInl h U` recovers `f`. -/
@[simp]
theorem inducedInl_comp_forgetDifferential_inducedDesc
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (f : U ⟶ toGradedModuleCat M) :
    inducedInl h U ≫ (forgetDifferential (h := h)).map (inducedDesc f) = f := by
  apply GradedModuleCat.hom_ext
  ext u
  rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, forgetDifferential_map_hom, inducedDesc,
    closedHom_closedHomOf, inducedInl_hom_apply, inducedDescLinear_apply]
  simp

/-- Closed morphisms out of `inducedObj h U` are determined by their restriction along
`inducedInl h U`. -/
theorem induced_hom_ext
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {φ ψ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h U) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M}
    (hφψ : inducedInl h U ≫ (forgetDifferential (h := h)).map φ =
      inducedInl h U ≫ (forgetDifferential (h := h)).map ψ) :
    φ = ψ := by
  have hinl (u : U) : closedHom φ (inducedMk h U u 0) = closedHom ψ (inducedMk h U u 0) :=
    congrArg (fun g : U ⟶ toGradedModuleCat M ↦ (g.hom u : M)) hφψ
  apply closedHom_ext
  intro x
  have hx : x = inducedMk h U (inducedFstFn h U x) 0 +
      (inducedObj h U).differential (inducedMk h U (inducedSndFn h U x) 0) :=
    inducedObj_ext (by simp) (by simp)
  rw [hx, map_add, map_add, ← differential_closedHom, ← differential_closedHom, hinl, hinl]

/-- If `f : U ⟶ toGradedModuleCat M` is an epimorphism in `GradedModuleCat`, then `inducedDesc f`
is an epimorphism in the closed category of curved right modules. -/
instance epi_inducedDesc
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (f : U ⟶ toGradedModuleCat M) [Epi f] :
    Epi (inducedDesc f) := by
  let φ : toGradedModuleCat (inducedObj h U) ⟶ toGradedModuleCat M :=
    (forgetDifferential (h := h)).map (inducedDesc f)
  have : Epi (inducedInl h U ≫ φ) :=
    (inducedInl_comp_forgetDifferential_inducedDesc f).symm ▸ inferInstance
  have hφ : Epi φ := epi_of_epi (inducedInl h U) φ
  exact (forgetDifferential (h := h)).epi_of_epi_map hφ

variable (h) in
/-- **The induced curved module functor** `G⁺`, left adjoint to `forgetDifferential`. -/
@[expose]
noncomputable def inducedFunctor :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj U := ForgetEnrichment.of _ (inducedObj h U)
  map g := inducedDesc (g ≫ inducedInl h _)
  map_id U := induced_hom_ext <|
    (inducedInl_comp_forgetDifferential_inducedDesc (𝟙 U ≫ inducedInl h U)).trans <|
      (Category.id_comp _).trans <|
        (Category.comp_id _).symm.trans <|
          congrArg (inducedInl h U ≫ ·)
            ((forgetDifferential (h := h)).map_id
              (ForgetEnrichment.of _ (inducedObj h U))).symm
  map_comp {U V W} f g := induced_hom_ext <|
    let φ := inducedDesc (f ≫ inducedInl h V)
    let ψ := inducedDesc (g ≫ inducedInl h W)
    (inducedInl_comp_forgetDifferential_inducedDesc ((f ≫ g) ≫ inducedInl h W)).trans <|
      (Category.assoc f g (inducedInl h W)).trans <|
        (congrArg (f ≫ ·)
          (inducedInl_comp_forgetDifferential_inducedDesc (g ≫ inducedInl h W)).symm).trans <|
          (Category.assoc f (inducedInl h V) ((forgetDifferential (h := h)).map ψ)).symm.trans <|
            (congrArg (· ≫ (forgetDifferential (h := h)).map ψ)
              (inducedInl_comp_forgetDifferential_inducedDesc
                (f ≫ inducedInl h V)).symm).trans <|
              (Category.assoc (inducedInl h U) ((forgetDifferential (h := h)).map φ)
                ((forgetDifferential (h := h)).map ψ)).trans <|
                congrArg (inducedInl h U ≫ ·) ((forgetDifferential (h := h)).map_comp φ ψ).symm

/-- On objects, `inducedFunctor h` sends `U` to `inducedObj h U`. -/
@[simp]
theorem inducedFunctor_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (CurvedDGRightModuleCat.inducedFunctor h).obj U =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (inducedObj h U) :=
  rfl

variable (h) in
/-- **Left adjunction `G⁺ ⊣ forgetDifferential`.** Closed morphisms out of `inducedObj h U`
correspond naturally to graded morphisms out of `U`. -/
noncomputable def inducedAdjunction :
    CurvedDGRightModuleCat.inducedFunctor h ⊣ forgetDifferential (h := h) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun U M ↦
        { toFun := fun φ ↦ inducedInl h U ≫ (forgetDifferential (h := h)).map φ
          invFun := fun f ↦ inducedDesc (M := ForgetEnrichment.to _ M) f
          left_inv := fun _ ↦ induced_hom_ext (inducedInl_comp_forgetDifferential_inducedDesc _)
          right_inv := fun f ↦ inducedInl_comp_forgetDifferential_inducedDesc f }
      homEquiv_naturality_left_symm := fun {U V M} g f ↦ induced_hom_ext <|
        let φ := inducedDesc (g ≫ inducedInl h V)
        let ψ := inducedDesc (M := ForgetEnrichment.to _ M) f
        (inducedInl_comp_forgetDifferential_inducedDesc (g ≫ f)).trans <|
          (congrArg (g ≫ ·) (inducedInl_comp_forgetDifferential_inducedDesc f).symm).trans <|
            (Category.assoc g (inducedInl h V) ((forgetDifferential (h := h)).map ψ)).symm.trans <|
              (congrArg (· ≫ (forgetDifferential (h := h)).map ψ)
                (inducedInl_comp_forgetDifferential_inducedDesc
                  (g ≫ inducedInl h V)).symm).trans <|
                (Category.assoc (inducedInl h U) ((forgetDifferential (h := h)).map φ)
                  ((forgetDifferential (h := h)).map ψ)).trans <|
                  congrArg (inducedInl h U ≫ ·)
                    ((forgetDifferential (h := h)).map_comp φ ψ).symm
      homEquiv_naturality_right := fun {U _ _} φ ψ ↦
        (congrArg (inducedInl h U ≫ ·)
          ((forgetDifferential (h := h)).map_comp φ ψ)).trans (Category.assoc _ _ _).symm }

end InducedAdjunction

section CoinducedAdjunction

variable {h : IsCurvedDGAlgebra 𝒜 d w}

private noncomputable def coinducedLiftLinear
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ U) : M →ₗ[Aᵐᵒᵖ] coinducedObj h U := by
  let gR : M →ₗ[R] U := g.hom.restrictScalars R
  have hg_shift : LinearMap.IsHomogeneous gR
      (InternalGrading.ofDecomposition M.grading).piece (U.shiftObj (-1)).grading.piece (-1) :=
    LinearMap.isHomogeneous_def.mpr fun p m hm ↦ by
      rw [InternalGrading.ofDecomposition_piece, ← toGradedModuleCat_piece] at hm
      rw [GradedModuleCat.mem_shiftObj_piece_iff, show p + -1 - -1 = p + 0 by omega]
      exact g.isHomogeneous.map_mem hm
  have hτ (m : M) :
      (U.shiftObj (-1)).grading.koszulTwist 1 (gR m) =
        -gR ((InternalGrading.ofDecomposition M.grading).koszulTwist 1 m) := by
    simpa only [mul_neg, mul_one, Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg,
      Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul] using
      hg_shift.koszulTwist_apply 1 m
  refine
    { toFun := fun m ↦ inducedMk h (U.shiftObj (-1)) (gR (M.differential m)) (gR m)
      map_add' := fun x y ↦ inducedObj_ext (by simp) (map_add gR x y)
      map_smul' := fun a m ↦ ?_ }
  induction a using MulOpposite.rec' with | h a => ?_
  have hgR_smul (b : A) (x : M) : gR (op b • x) = op b • gR x :=
    g.hom.map_smul (op b) x
  refine inducedObj_ext ?_ (hgR_smul a m)
  simp only [RingHom.id_apply, inducedFstFn_mk, inducedFstFn_smul, inducedSndFn_mk, unop_op,
    differential_op_smul M a m, map_add, hgR_smul, hτ, smul_neg, sub_neg_eq_add]

@[simp]
private theorem inducedFstFn_coinducedLiftLinear
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ U) (m : M) :
    inducedFstFn h (U.shiftObj (-1)) (coinducedLiftLinear g m) = g.hom (M.differential m) :=
  rfl

@[simp]
private theorem inducedSndFn_coinducedLiftLinear
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ U) (m : M) :
    inducedSndFn h (U.shiftObj (-1)) (coinducedLiftLinear g m) = g.hom m :=
  rfl

/-- Universal closed morphism `m ↦ (g (d_M m), g m)` into `coinducedObj h U` associated to a graded
morphism `g : toGradedModuleCat M ⟶ U`. -/
noncomputable def coinducedLift
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ U) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h U) :=
  closedHomOf (M := M) (N := coinducedObj h U) (coinducedLiftLinear g)
    (fun p m hm ↦ by
      refine (mem_inducedObj_grading_iff h (U.shiftObj (-1)) p _).mpr ⟨?_, ?_⟩
      · rw [inducedFstFn_coinducedLiftLinear, GradedModuleCat.mem_shiftObj_piece_iff,
          sub_neg_eq_add]
        have hdm : M.differential m ∈ (toGradedModuleCat M).grading.piece (p + 1) := by
          rw [toGradedModuleCat_piece]
          exact M.isCurvedDGRightModule.isHomogeneous.map_mem hm
        simpa only [add_zero] using g.isHomogeneous.map_mem hdm
      · rw [inducedSndFn_coinducedLiftLinear, GradedModuleCat.mem_shiftObj_piece_iff,
          show p - 1 - -1 = p + 0 by omega]
        have hm' : m ∈ (toGradedModuleCat M).grading.piece p := by
          rwa [toGradedModuleCat_piece]
        exact g.isHomogeneous.map_mem hm')
    (fun m ↦ inducedObj_ext
      (by
        simp only [inducedFstFn_differential, inducedSndFn_coinducedLiftLinear,
          inducedFstFn_coinducedLiftLinear, M.isCurvedDGRightModule.sq_eq]
        exact (g.hom.map_smul (op w) m).symm)
      rfl)

/-- Composing `coinducedLift g` with the counit `coinducedCounit h U` recovers `g`. -/
@[simp]
theorem forgetDifferential_coinducedLift_comp_coinducedCounit
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ U) :
    (forgetDifferential (h := h)).map (coinducedLift g) ≫ coinducedCounit h U = g := by
  apply GradedModuleCat.hom_ext
  ext m
  rw [GradedModuleCat.hom_comp, LinearMap.comp_apply, forgetDifferential_map_hom, coinducedLift,
    closedHom_closedHomOf, coinducedCounit_hom_apply]
  exact inducedSndFn_coinducedLiftLinear g m

/-- Closed morphisms into `coinducedObj h U` are determined by postcomposition with
`coinducedCounit h U`. -/
theorem coinduced_hom_ext
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    {φ ψ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h U)}
    (hφψ : (forgetDifferential (h := h)).map φ ≫ coinducedCounit h U =
      (forgetDifferential (h := h)).map ψ ≫ coinducedCounit h U) :
    φ = ψ := by
  have hsnd (m : M) : inducedSndFn h (U.shiftObj (-1)) (closedHom φ m) =
      inducedSndFn h (U.shiftObj (-1)) (closedHom ψ m) :=
    congrArg (fun g : toGradedModuleCat M ⟶ U ↦ g.hom m) hφψ
  apply closedHom_ext
  intro m
  refine inducedObj_ext ?_ (hsnd m)
  have hdφ := congrArg (inducedSndFn h (U.shiftObj (-1))) (differential_closedHom φ m)
  have hdψ := congrArg (inducedSndFn h (U.shiftObj (-1))) (differential_closedHom ψ m)
  simp only [inducedSndFn_differential] at hdφ hdψ
  exact hdφ.trans ((hsnd (M.differential m)).trans hdψ.symm)

/-- If `g : toGradedModuleCat M ⟶ U` is a monomorphism in `GradedModuleCat`, then `coinducedLift g`
is a monomorphism in the closed category of curved right modules. -/
instance mono_coinducedLift
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    {U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece}
    (g : toGradedModuleCat M ⟶ U) [Mono g] :
    Mono (coinducedLift g) := by
  let φ : toGradedModuleCat M ⟶ toGradedModuleCat (coinducedObj h U) :=
    (forgetDifferential (h := h)).map (coinducedLift g)
  have : Mono (φ ≫ coinducedCounit h U) :=
    (forgetDifferential_coinducedLift_comp_coinducedCounit g).symm ▸ inferInstance
  have hφ : Mono φ := mono_of_mono φ (coinducedCounit h U)
  exact (forgetDifferential (h := h)).mono_of_mono_map hφ

variable (h) in
/-- **The coinduced curved module functor** `G⁻`, right adjoint to `forgetDifferential`. -/
@[expose]
noncomputable def coinducedFunctor :
    GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) where
  obj U := ForgetEnrichment.of _ (coinducedObj h U)
  map g := coinducedLift (coinducedCounit h _ ≫ g)
  map_id U := coinduced_hom_ext <|
    (forgetDifferential_coinducedLift_comp_coinducedCounit (coinducedCounit h U ≫ 𝟙 U)).trans <|
      (Category.comp_id _).trans <|
        (Category.id_comp _).symm.trans <|
          congrArg (· ≫ coinducedCounit h U)
            ((forgetDifferential (h := h)).map_id
              (ForgetEnrichment.of _ (coinducedObj h U))).symm
  map_comp {U V W} f g := coinduced_hom_ext <|
    let φ := coinducedLift (coinducedCounit h U ≫ f)
    let ψ := coinducedLift (coinducedCounit h V ≫ g)
    (forgetDifferential_coinducedLift_comp_coinducedCounit
      (coinducedCounit h U ≫ (f ≫ g))).trans <|
      (Category.assoc (coinducedCounit h U) f g).symm.trans <|
        (congrArg (· ≫ g)
          (forgetDifferential_coinducedLift_comp_coinducedCounit
            (coinducedCounit h U ≫ f)).symm).trans <|
          (Category.assoc ((forgetDifferential (h := h)).map φ) (coinducedCounit h V) g).trans <|
            (congrArg ((forgetDifferential (h := h)).map φ ≫ ·)
              (forgetDifferential_coinducedLift_comp_coinducedCounit
                (coinducedCounit h V ≫ g)).symm).trans <|
              (Category.assoc ((forgetDifferential (h := h)).map φ)
                ((forgetDifferential (h := h)).map ψ) (coinducedCounit h W)).symm.trans <|
                congrArg (· ≫ coinducedCounit h W)
                  ((forgetDifferential (h := h)).map_comp φ ψ).symm

/-- On objects, `coinducedFunctor h` sends `U` to `coinducedObj h U`. -/
@[simp]
theorem coinducedFunctor_obj (h : IsCurvedDGAlgebra 𝒜 d w)
    (U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :
    (coinducedFunctor h).obj U =
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinducedObj h U) :=
  rfl

variable (h) in
/-- **Right adjunction `forgetDifferential ⊣ G⁻`.** Closed morphisms into `coinducedObj h U`
correspond naturally to graded morphisms into `U`. -/
noncomputable def coinducedAdjunction :
    forgetDifferential (h := h) ⊣ coinducedFunctor h :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M U ↦
        { toFun := fun g ↦ coinducedLift (M := ForgetEnrichment.to _ M) g
          invFun := fun φ ↦ (forgetDifferential (h := h)).map φ ≫ coinducedCounit h U
          left_inv := fun g ↦ forgetDifferential_coinducedLift_comp_coinducedCounit g
          right_inv := fun _ ↦ coinduced_hom_ext
            (forgetDifferential_coinducedLift_comp_coinducedCounit _) }
      homEquiv_naturality_left_symm := fun {_ _ U} φ ψ ↦
        (congrArg (· ≫ coinducedCounit h U)
          ((forgetDifferential (h := h)).map_comp φ ψ)).trans (Category.assoc _ _ _)
      homEquiv_naturality_right := fun {M U V} g f ↦ coinduced_hom_ext <|
        let φ := coinducedLift (M := ForgetEnrichment.to _ M) g
        let ψ := coinducedLift (coinducedCounit h U ≫ f)
        (forgetDifferential_coinducedLift_comp_coinducedCounit (g ≫ f)).trans <|
          (congrArg (· ≫ f)
            (forgetDifferential_coinducedLift_comp_coinducedCounit g).symm).trans <|
            (Category.assoc ((forgetDifferential (h := h)).map φ) (coinducedCounit h U) f).trans <|
              (congrArg ((forgetDifferential (h := h)).map φ ≫ ·)
                (forgetDifferential_coinducedLift_comp_coinducedCounit
                  (coinducedCounit h U ≫ f)).symm).trans <|
                (Category.assoc ((forgetDifferential (h := h)).map φ)
                  ((forgetDifferential (h := h)).map ψ) (coinducedCounit h V)).symm.trans <|
                  congrArg (· ≫ coinducedCounit h V)
                    ((forgetDifferential (h := h)).map_comp φ ψ).symm }

end CoinducedAdjunction

end Categorical

end TauCeti.CurvedDGRightModuleCat
