/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Reduced
public import TauCeti.RepresentationTheory.Crystal.Highest
public import TauCeti.RepresentationTheory.LSPath.Crystal.Operations
public import TauCeti.RepresentationTheory.LSPath.Highest
public import TauCeti.RepresentationTheory.LSPath.Reverse
public import TauCeti.RepresentationTheory.LSPath.Weight
public import TauCeti.RepresentationTheory.LSPath.Word

import Mathlib.LinearAlgebra.TensorProduct.Tower
import TauCeti.RepresentationTheory.LSPath.LinearMap
import TauCeti.RepresentationTheory.LSPath.Realization

/-!
# The highest-weight normal crystal `B(λ)` of Lakshmibai–Seshadri paths

For a dominant weight `λ` of a finite reduced root datum `(P, b)`, the Lakshmibai–Seshadri paths
`LSPath P b λ` carry a canonical normal crystal structure `TauCeti.LSPath.normalCrystal hlam`,
defined intrinsically without choosing an ambient vector-space realization or requiring the coweight
lattice to be finite free.

In every realization `(𝕜, V, f, F)` over a linearly ordered field `𝕜` whose simple-coroot height
forms satisfy `F i (f x) = ⟨x, αᵢ^∨⟩`, the realized LS paths form a crystal-admissible set of
integral paths (`TauCeti.LSPath.isCrystalSet_range_toPLPath`,
`TauCeti.LSPath.isIntegralPath_toPLPath`). The canonical rational realization `X → ℚ ⊗[ℤ] X` embeds
semilinearly into `(𝕜, V, f, F)` along `Rat.castHom 𝕜`, transferring all weights, string lengths,
and root operators verbatim.

This yields Littelmann's structural theorems for `B(λ)`:

* **Uniqueness of the highest path and generation**: `LSPath.straight λ` is the unique highest
  element (`TauCeti.LSPath.forall_normalCrystal_e_eq_none_iff`); since `LSPath P b λ` is finite,
  every LS path is obtained from `LSPath.straight λ` by a word of lowering operators
  (`TauCeti.LSPath.exists_normalCrystal_fWord_straight`), and the crystal graph of `B(λ)` is
  connected (`TauCeti.LSPath.connected_normalCrystal_graph`).
* **Equivalence with the operator-generated component**: the realized LS paths are precisely the
  paths obtained from `PLPath.straight 𝕜 (f λ)` by words of lowering operators
  (`TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord_straight`, without injectivity on `f`);
  when `f` is injective, `toPLPath 𝕜 f` induces a strict crystal isomorphism from
  `LSPath.normalCrystal hlam` onto the connected component `PLPath.normalCrystalComponent` of
  `PLPath.straight 𝕜 (f λ)` (`TauCeti.LSPath.toPLPathComponentIso`), proving finiteness of that
  component (`TauCeti.PLPath.finite_supp_connectedComponentMk_straight`) and specializing to
  `PLPath.baseChangeNormalCrystal` (`TauCeti.LSPath.toPLPathBaseChangeComponentIso`).
* **Crystal duality**: path reversal `LSPath.reverse` is a strict crystal isomorphism
  `B(λ)^∨ ≃ B(-w₀ λ)` (`TauCeti.LSPath.reverseCrystalIso`).
* **Central weights, zero weight, and empty root systems**: whenever `λ` annihilates all simple
  coroots (including `λ = 0` and empty root systems), every LS path is straight and `B(λ)` is
  strictly isomorphic to `NormalCrystal.central λ` (`TauCeti.LSPath.centralIso`,
  `TauCeti.LSPath.zeroIso`).

## Main definitions

* `TauCeti.LSPath.normalCrystal`: the canonical normal crystal `B(λ)` on `LSPath P b λ`.
* `TauCeti.LSPath.toPLPathRangeIso`, `TauCeti.LSPath.toPLPathComponentIso`,
  `TauCeti.LSPath.toPLPathBaseChangeComponentIso`: strict crystal isomorphisms identifying
  `LSPath.normalCrystal hlam` with the realized LS crystal and with the operator-generated
  component of the straight path `PLPath.straight 𝕜 (f λ)`.
* `TauCeti.LSPath.reverseCrystalIso`: crystal duality `B(λ)^∨ ≃ B(-w₀ λ)`.
* `TauCeti.LSPath.centralIso`, `TauCeti.LSPath.zeroIso`: strict crystal isomorphisms for central
  weights and `λ = 0`.

## Main results

* `TauCeti.LSPath.isCrystalSet_range_toPLPath`, `TauCeti.LSPath.isIntegralPath_toPLPath`,
  `TauCeti.PLPath.isIntegralPath_straight_of_mem_dominantChamber`: LS paths and dominant straight
  paths are crystal-admissible integral paths.
* `TauCeti.LSPath.forall_normalCrystal_e_eq_none_iff`,
  `TauCeti.LSPath.exists_normalCrystal_fWord_straight`,
  `TauCeti.LSPath.connected_normalCrystal_graph`: uniqueness of the highest element, lowering-word
  generation, and connectedness of `B(λ)`.
* `TauCeti.LSPath.mem_range_toPLPath_iff_exists_lowerWord_straight`,
  `TauCeti.LSPath.mem_supp_connectedComponentMk_straight_iff`,
  `TauCeti.PLPath.finite_supp_connectedComponentMk_straight`: equivalence between LS paths and the
  operator-generated straight-path component, and finiteness of the component.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329–346, §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499–525, §§2, 4.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

public section

namespace TauCeti

open Module RootPairing Set
open scoped TensorProduct

/-! ### Crystal-admissibility, integrality, and faithful realization of LS paths -/

namespace LSPath

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced]

section Realization

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- **The realized Lakshmibai–Seshadri paths of a dominant shape form a crystal-admissible set.**
No injectivity of `f` and no spanning or regularity assumption on `λ` are needed. -/
theorem isCrystalSet_range_toPLPath {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsCrystalSet b f F (range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) where
  endpoint_mem_range := by
    rintro _ ⟨π, rfl⟩
    obtain ⟨m, -, hm⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := 𝕜) hlam f
    exact ⟨(π.dir (Fin.last _)).1 • lam + m, hm.symm⟩
  exists_minHeight_eq_intCast := by
    rintro _ ⟨π, rfl⟩ i
    exact π.exists_minHeight_eq_intCast hlam f i (F i) (hF i)
  mem_of_raise_eq_some := by
    rintro i _ q hr ⟨π, rfl⟩
    exact π.exists_toPLPath_eq_of_raise_eq_some hlam f i (F i) (hF i) hr
  mem_of_lower_eq_some := by
    rintro i _ q hl ⟨π, rfl⟩
    exact π.exists_toPLPath_eq_of_lower_eq_some hlam f i (F i) (hF i) hl

/-- Every realized Lakshmibai–Seshadri path of dominant shape is an integral path. -/
theorem isIntegralPath_toPLPath {lam : X} (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    PLPath.IsIntegralPath b f F (π.toPLPath 𝕜 f) :=
  (isCrystalSet_range_toPLPath hlam hF).subset_isIntegralPath ⟨π, rfl⟩

/-- When the simple-coroot height forms agree with the simple coroots on `f(X)`, the realized Weyl
orbit automatically has no distinct elements on the same ray, so injectivity of `f` on `W λ` alone
makes `toPLPath 𝕜 f` injective on `LSPath P b λ`. -/
theorem toPLPath_injective_of_coroot' {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hf : InjOn f (range fun w : P.weylGroup ↦ w • lam))
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    Function.Injective fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f :=
  toPLPath_injective hlam hf (P.pairwise_not_sameRay_range_smul b hF lam)

end Realization

end LSPath

namespace PLPath

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- **Every dominant straight path is an integral path**, in any realization whose height forms
agree with the simple coroots on `f(X)`. -/
theorem isIntegralPath_straight_of_mem_dominantChamber {lam : X}
    (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    IsIntegralPath b f F (straight 𝕜 (f lam)) := by
  simpa using (LSPath.straight (P := P) (b := b) lam).isIntegralPath_toPLPath hlam hF

end PLPath

/-! ### Canonical rational realization and `LSPath.normalCrystal` -/

namespace LSPath

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}

section RationalHelpers

private noncomputable abbrev ratMap (X : Type*) [AddCommGroup X] : X →+ ℚ ⊗[ℤ] X :=
  (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom

private theorem ratMap_apply (x : X) : ratMap X x = (1 : ℚ) ⊗ₜ[ℤ] x :=
  (rfl)

private noncomputable def ratCorootForm (P : RootDatum ι X Y) (i : ι) : Dual ℚ (ℚ ⊗[ℤ] X) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id (R := ℚ)).smulRight ((Int.castAddHom ℚ).toIntLinearMap.comp (P.coroot' i)))

private theorem ratCorootForm_tmul (P : RootDatum ι X Y) (i : ι) (q : ℚ) (x : X) :
    ratCorootForm P i (q ⊗ₜ[ℤ] x) = q * (P.coroot' i x : ℚ) := by
  simp [ratCorootForm]

private theorem ratCorootForm_ratMap (P : RootDatum ι X Y) (i : ι) (x : X) :
    ratCorootForm P i (ratMap X x) = (P.coroot' i x : ℚ) := by
  simp [ratMap_apply, ratCorootForm_tmul]

section SemilinearComparison

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

private noncomputable def ratLiftAux (f : X →+ V) : (ℚ ⊗[ℤ] X) →ₗ[ℤ] V :=
  TensorProduct.lift
    { toFun := fun q ↦
        { toFun := fun x ↦ (q : 𝕜) • f x
          map_add' := fun x y ↦ by rw [map_add, smul_add]
          map_smul' := fun n x ↦ by
            simp only [map_zsmul, RingHom.id_apply, smul_comm (q : 𝕜) n] }
      map_add' := fun q₁ q₂ ↦ by
        ext x
        simp [Rat.cast_add, add_smul]
      map_smul' := fun n q ↦ by
        ext x
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
          zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast, mul_smul, Int.cast_smul_eq_zsmul] }

private theorem ratLiftAux_tmul (f : X →+ V) (q : ℚ) (x : X) :
    ratLiftAux 𝕜 f (q ⊗ₜ[ℤ] x) = (q : 𝕜) • f x :=
  TensorProduct.lift.tmul q x

private noncomputable def ratLift (f : X →+ V) : (ℚ ⊗[ℤ] X) →ₛₗ[Rat.castHom 𝕜] V where
  toFun := ratLiftAux 𝕜 f
  map_add' := (ratLiftAux 𝕜 f).map_add
  map_smul' r w := by
    induction w using TensorProduct.inductionOn with
    | tmul q x =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, ratLiftAux_tmul, ratLiftAux_tmul,
        Rat.coe_castHom, Rat.cast_mul, mul_smul]
    | add w₁ w₂ ih₁ ih₂ => simp [map_add, smul_add, ih₁, ih₂]

private theorem ratLift_tmul (f : X →+ V) (q : ℚ) (x : X) :
    ratLift 𝕜 f (q ⊗ₜ[ℤ] x) = (q : 𝕜) • f x :=
  ratLiftAux_tmul 𝕜 f q x

private theorem ratLift_ratMap (f : X →+ V) (x : X) :
    ratLift 𝕜 f (ratMap X x) = f x := by
  simp [ratMap_apply, ratLift_tmul]

private theorem apply_ratLift {f : X →+ V} {i : ι} {F : Dual 𝕜 V}
    (hF : ∀ x, F (f x) = (P.coroot' i x : 𝕜)) (w : ℚ ⊗[ℤ] X) :
    F (ratLift 𝕜 f w) = (Rat.castHom 𝕜) (ratCorootForm P i w) := by
  induction w using TensorProduct.inductionOn with
  | tmul q x =>
    rw [ratLift_tmul, map_smul, hF, ratCorootForm_tmul, Rat.coe_castHom, Rat.cast_mul,
      Rat.cast_intCast, smul_eq_mul]
  | add w₁ w₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]

private theorem mapSemilinear_toPLPath_ratLift [Finite ι] [P.IsReduced] {lam : X} (f : X →+ V)
    (π : LSPath P b lam) :
    (π.toPLPath ℚ (ratMap X)).mapSemilinear (ratLift 𝕜 f) = π.toPLPath 𝕜 f := by
  rw [toPLPath_def, PLPath.mapSemilinear_ofSegments Rat.cast_strictMono, toPLPath_def]
  congr 1
  simp only [timed_def, List.map_ofFn, Function.comp_def, map_smulₛₗ, Rat.coe_castHom,
    Rat.cast_id, ratLift_ratMap]

end SemilinearComparison

end RationalHelpers

variable [Finite ι] [P.IsReduced]

section CanonicalCrystal

private noncomputable def ratEquiv {lam : X} (hlam : lam ∈ dominantChamber P b) :
    LSPath P b lam ≃ range fun π : LSPath P b lam ↦ π.toPLPath ℚ (ratMap X) :=
  Equiv.ofInjective (fun π : LSPath P b lam ↦ π.toPLPath ℚ (ratMap X))
    (toPLPath_injective_of_coroot' hlam (P.tensorProduct_mk_injective ℚ).injOn
      fun i x ↦ ratCorootForm_ratMap P i x)

private theorem ratEquiv_apply {lam : X} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (ratEquiv hlam π).1 = π.toPLPath ℚ (ratMap X) :=
  (rfl)

/-- **Littelmann's normal crystal `B(λ)` on Lakshmibai–Seshadri paths.** For any dominant weight
`λ` of a finite reduced root datum `(P, b)`, `LSPath P b λ` carries a canonical normal crystal
structure, independent of any auxiliary vector-space realization. In every realization `(f, F)`
with `F i (f x) = ⟨x, αᵢ^∨⟩`, its weight is the endpoint, its string lengths are `-min H_i` and
`H_i(1) - min H_i`, and its raising and lowering operators are Littelmann's path operators `e_i`
and `f_i`. -/
noncomputable def normalCrystal {lam : X} (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal P b (LSPath P b lam) :=
  (PLPath.normalCrystalOn (P.tensorProduct_mk_injective ℚ)
    (fun i x ↦ ratCorootForm_ratMap P i x)
    (isCrystalSet_range_toPLPath hlam fun i x ↦ ratCorootForm_ratMap P i x)).transport
    (ratEquiv hlam).symm

private theorem ratMap_normalCrystal_wt {lam : X} (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    ratMap X ((normalCrystal hlam).wt π) = (π.toPLPath ℚ (ratMap X)).endpoint := by
  simpa [normalCrystal, ratEquiv_apply] using
    PLPath.apply_normalCrystalOn_wt
      (hf := P.tensorProduct_mk_injective ℚ)
      (hF := fun i x ↦ ratCorootForm_ratMap P i x)
      (hS := isCrystalSet_range_toPLPath hlam fun i x ↦ ratCorootForm_ratMap P i x)
      (ratEquiv hlam π)

private theorem cast_normalCrystal_ε_rat {lam : X} (hlam : lam ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).ε i π : ℚ) =
      -(π.toPLPath ℚ (ratMap X)).minHeight (ratCorootForm P i) := by
  simpa [normalCrystal, ratEquiv_apply] using
    PLPath.cast_normalCrystalOn_ε
      (hf := P.tensorProduct_mk_injective ℚ)
      (hF := fun i x ↦ ratCorootForm_ratMap P i x)
      (hS := isCrystalSet_range_toPLPath hlam fun i x ↦ ratCorootForm_ratMap P i x)
      i (ratEquiv hlam π)

private theorem cast_normalCrystal_φ_rat {lam : X} (hlam : lam ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).φ i π : ℚ) =
      ratCorootForm P i (π.toPLPath ℚ (ratMap X)).endpoint -
        (π.toPLPath ℚ (ratMap X)).minHeight (ratCorootForm P i) := by
  simpa [normalCrystal, ratEquiv_apply] using
    PLPath.cast_normalCrystalOn_φ
      (hf := P.tensorProduct_mk_injective ℚ)
      (hF := fun i x ↦ ratCorootForm_ratMap P i x)
      (hS := isCrystalSet_range_toPLPath hlam fun i x ↦ ratCorootForm_ratMap P i x)
      i (ratEquiv hlam π)

private theorem normalCrystal_e_eq_some_iff_rat {lam : X} (hlam : lam ∈ dominantChamber P b)
    {i : b.support} {π π' : LSPath P b lam} :
    (normalCrystal hlam).e i π = some π' ↔
      PLPath.raise (ratCorootForm P i) (ratMap X (P.root i)) (π.toPLPath ℚ (ratMap X)) =
        some (π'.toPLPath ℚ (ratMap X)) := by
  simp only [normalCrystal, NormalCrystal.transport_e, Equiv.symm_symm, Option.map_eq_some_iff,
    Equiv.symm_apply_eq, exists_eq_right]
  exact PLPath.normalCrystalOn_e_eq_some_iff

private theorem normalCrystal_f_eq_some_iff_rat {lam : X} (hlam : lam ∈ dominantChamber P b)
    {i : b.support} {π π' : LSPath P b lam} :
    (normalCrystal hlam).f i π = some π' ↔
      PLPath.lower (ratCorootForm P i) (ratMap X (P.root i)) (π.toPLPath ℚ (ratMap X)) =
        some (π'.toPLPath ℚ (ratMap X)) := by
  simp only [normalCrystal, NormalCrystal.transport_f, Equiv.symm_symm, Option.map_eq_some_iff,
    Equiv.symm_apply_eq, exists_eq_right]
  exact PLPath.normalCrystalOn_f_eq_some_iff

private theorem normalCrystal_e_eq_none_iff_rat {lam : X} (hlam : lam ∈ dominantChamber P b)
    {i : b.support} {π : LSPath P b lam} :
    (normalCrystal hlam).e i π = none ↔
      PLPath.raise (ratCorootForm P i) (ratMap X (P.root i)) (π.toPLPath ℚ (ratMap X)) = none := by
  simp only [normalCrystal, NormalCrystal.transport_e, Equiv.symm_symm, Option.map_eq_none_iff]
  exact PLPath.normalCrystalOn_e_eq_none_iff

private theorem normalCrystal_f_eq_none_iff_rat {lam : X} (hlam : lam ∈ dominantChamber P b)
    {i : b.support} {π : LSPath P b lam} :
    (normalCrystal hlam).f i π = none ↔
      PLPath.lower (ratCorootForm P i) (ratMap X (P.root i)) (π.toPLPath ℚ (ratMap X)) = none := by
  simp only [normalCrystal, NormalCrystal.transport_f, Equiv.symm_symm, Option.map_eq_none_iff]
  exact PLPath.normalCrystalOn_f_eq_none_iff

section CrystalAPI

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- In any realization `(𝕜, V, f)`, the realized weight of an LS path in `LSPath.normalCrystal` is
its path endpoint. -/
theorem apply_normalCrystal_wt {lam : X} (hlam : lam ∈ dominantChamber P b) (f : X →+ V)
    (π : LSPath P b lam) :
    f ((normalCrystal hlam).wt π) = (π.toPLPath 𝕜 f).endpoint := by
  rw [← mapSemilinear_toPLPath_ratLift 𝕜 f π, PLPath.endpoint_mapSemilinear,
    ← ratMap_normalCrystal_wt hlam π, ratLift_ratMap]

/-- For an injective realization, the crystal weight of an LS path is characterized by its endpoint.
-/
theorem normalCrystal_wt_eq_iff {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hf : Function.Injective f) {π : LSPath P b lam} {μ : X} :
    (normalCrystal hlam).wt π = μ ↔ (π.toPLPath 𝕜 f).endpoint = f μ := by
  rw [← hf.eq_iff, apply_normalCrystal_wt (𝕜 := 𝕜) hlam f π, eq_comm]

/-- The weight of the straight LS path of dominant shape `λ` is `λ`. -/
@[simp]
theorem normalCrystal_wt_straight {lam : X} (hlam : lam ∈ dominantChamber P b) :
    (normalCrystal hlam).wt (straight lam) = lam := by
  apply P.tensorProduct_mk_injective ℚ
  simpa [ratMap_apply] using ratMap_normalCrystal_wt hlam (straight lam)

/-- **Raising string length on `B(λ)`**: in any realization whose height forms agree with the simple
coroots, `ε_i(π) = -min H_i(π)`. -/
theorem cast_normalCrystal_ε {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).ε i π : 𝕜) = -(π.toPLPath 𝕜 f).minHeight (F i) := by
  have h := congrArg (Rat.castHom 𝕜) (cast_normalCrystal_ε_rat hlam i π)
  rw [← mapSemilinear_toPLPath_ratLift 𝕜 f π,
    PLPath.minHeight_mapSemilinear Rat.cast_strictMono _ (apply_ratLift 𝕜 (hF i))]
  simpa [Rat.coe_castHom] using h

/-- **Lowering string length on `B(λ)`**: in any realization whose height forms agree with the
simple coroots, `φ_i(π) = H_i(π)(1) - min H_i(π)`. -/
theorem cast_normalCrystal_φ {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    ((normalCrystal hlam).φ i π : 𝕜) =
      F i (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight (F i) := by
  have h := congrArg (Rat.castHom 𝕜) (cast_normalCrystal_φ_rat hlam i π)
  rw [← mapSemilinear_toPLPath_ratLift 𝕜 f π, PLPath.endpoint_mapSemilinear,
    PLPath.minHeight_mapSemilinear Rat.cast_strictMono _ (apply_ratLift 𝕜 (hF i)),
    apply_ratLift 𝕜 (hF i)]
  simpa [Rat.coe_castHom] using h

/-- Raising in `LSPath.normalCrystal` realizes `PLPath.raise` in every compatible realization, with
no injectivity hypothesis on `f`. -/
theorem toPLPath_of_normalCrystal_e_eq_some {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π π' : LSPath P b lam} (h : (normalCrystal hlam).e i π = some π') :
    PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  have hr := (normalCrystal_e_eq_some_iff_rat hlam).mp h
  rw [← mapSemilinear_toPLPath_ratLift 𝕜 f π, ← mapSemilinear_toPLPath_ratLift 𝕜 f π',
    ← ratLift_ratMap 𝕜 f (P.root i),
    PLPath.raise_mapSemilinear Rat.cast_strictMono _ (apply_ratLift 𝕜 (hF i)), hr,
    Option.map_some]

/-- Lowering in `LSPath.normalCrystal` realizes `PLPath.lower` in every compatible realization, with
no injectivity hypothesis on `f`. -/
theorem toPLPath_of_normalCrystal_f_eq_some {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π π' : LSPath P b lam} (h : (normalCrystal hlam).f i π = some π') :
    PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  have hl := (normalCrystal_f_eq_some_iff_rat hlam).mp h
  rw [← mapSemilinear_toPLPath_ratLift 𝕜 f π, ← mapSemilinear_toPLPath_ratLift 𝕜 f π',
    ← ratLift_ratMap 𝕜 f (P.root i),
    PLPath.lower_mapSemilinear Rat.cast_strictMono _ (apply_ratLift 𝕜 (hF i)), hl,
    Option.map_some]

/-- Annihilation by `e_i` in `LSPath.normalCrystal` agrees with annihilation by `PLPath.raise` in
every compatible realization. -/
theorem normalCrystal_e_eq_none_iff {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π : LSPath P b lam} :
    (normalCrystal hlam).e i π = none ↔
      PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = none := by
  rw [normalCrystal_e_eq_none_iff_rat hlam, ← mapSemilinear_toPLPath_ratLift 𝕜 f π,
    ← ratLift_ratMap 𝕜 f (P.root i),
    PLPath.raise_mapSemilinear Rat.cast_strictMono _ (apply_ratLift 𝕜 (hF i)),
    Option.map_eq_none_iff]

/-- Annihilation by `f_i` in `LSPath.normalCrystal` agrees with annihilation by `PLPath.lower` in
every compatible realization. -/
theorem normalCrystal_f_eq_none_iff {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π : LSPath P b lam} :
    (normalCrystal hlam).f i π = none ↔
      PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = none := by
  rw [normalCrystal_f_eq_none_iff_rat hlam, ← mapSemilinear_toPLPath_ratLift 𝕜 f π,
    ← ratLift_ratMap 𝕜 f (P.root i),
    PLPath.lower_mapSemilinear Rat.cast_strictMono _ (apply_ratLift 𝕜 (hF i)),
    Option.map_eq_none_iff]

/-- Whenever `f` separates the Weyl orbit `W λ`, `e_i` in `LSPath.normalCrystal` is characterized by
`PLPath.raise` on realized paths. -/
theorem normalCrystal_e_eq_some_iff {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hf : InjOn f (range fun w : P.weylGroup ↦ w • lam))
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π π' : LSPath P b lam} :
    (normalCrystal hlam).e i π = some π' ↔
      PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  refine ⟨toPLPath_of_normalCrystal_e_eq_some hlam hF, fun hr ↦ ?_⟩
  cases he : (normalCrystal hlam).e i π with
  | none =>
    rw [(normalCrystal_e_eq_none_iff hlam hF).mp he] at hr
    cases hr
  | some π'' =>
    have hEq := Option.some.inj ((toPLPath_of_normalCrystal_e_eq_some hlam hF he).symm.trans hr)
    exact congrArg some (toPLPath_injective_of_coroot' hlam hf hF hEq)

/-- Whenever `f` separates the Weyl orbit `W λ`, `f_i` in `LSPath.normalCrystal` is characterized by
`PLPath.lower` on realized paths. -/
theorem normalCrystal_f_eq_some_iff {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hf : InjOn f (range fun w : P.weylGroup ↦ w • lam))
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {i : b.support} {π π' : LSPath P b lam} :
    (normalCrystal hlam).f i π = some π' ↔
      PLPath.lower (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  refine ⟨toPLPath_of_normalCrystal_f_eq_some hlam hF, fun hl ↦ ?_⟩
  cases hf' : (normalCrystal hlam).f i π with
  | none =>
    rw [(normalCrystal_f_eq_none_iff hlam hF).mp hf'] at hl
    cases hl
  | some π'' =>
    have hEq := Option.some.inj ((toPLPath_of_normalCrystal_f_eq_some hlam hF hf').symm.trans hl)
    exact congrArg some (toPLPath_injective_of_coroot' hlam hf hF hEq)

/-- Words of lowering operators in `LSPath.normalCrystal` realize `PLPath.lowerWord` in every
compatible realization. -/
theorem toPLPath_of_normalCrystal_fWord_eq_some {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {w : List b.support} {π π' : LSPath P b lam}
    (h : (normalCrystal hlam).fWord w π = some π') :
    PLPath.lowerWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil =>
    rw [NormalCrystal.fWord_nil] at h
    obtain rfl := Option.some.inj h
    exact PLPath.lowerWord_nil _
  | cons i w ih =>
    obtain ⟨σ, hσ, hw⟩ := Option.bind_eq_some_iff.mp ((normalCrystal hlam).fWord_cons i w π ▸ h)
    rw [PLPath.lowerWord_cons, toPLPath_of_normalCrystal_f_eq_some hlam hF hσ, Option.bind_some,
      ih hw]

/-- Words of raising operators in `LSPath.normalCrystal` realize `PLPath.raiseWord` in every
compatible realization. -/
theorem toPLPath_of_normalCrystal_eWord_eq_some {lam : X} (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {w : List b.support} {π π' : LSPath P b lam}
    (h : (normalCrystal hlam).eWord w π = some π') :
    PLPath.raiseWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  induction w generalizing π with
  | nil =>
    rw [NormalCrystal.eWord_nil] at h
    obtain rfl := Option.some.inj h
    exact PLPath.raiseWord_nil _
  | cons i w ih =>
    obtain ⟨σ, hσ, hw⟩ := Option.bind_eq_some_iff.mp ((normalCrystal hlam).eWord_cons i w π ▸ h)
    rw [PLPath.raiseWord_cons, toPLPath_of_normalCrystal_e_eq_some hlam hF hσ, Option.bind_some,
      ih hw]

end CrystalAPI

/-! ### Unique highest element, generation by lowering words, and connectedness -/

/-- **Uniqueness of the highest element of `B(λ)`.** The straight path `straight λ` is the unique
element of `LSPath.normalCrystal hlam` annihilated by every raising operator. -/
theorem forall_normalCrystal_e_eq_none_iff {lam : X} (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    (∀ i, (normalCrystal hlam).e i π = none) ↔ π = straight lam := by
  have := P.flip_isReduced
  simp only [normalCrystal_e_eq_none_iff_rat hlam]
  exact π.forall_raise_eq_none_iff hlam (ratMap X) (fun i ↦ ratCorootForm P i)
    (fun i x ↦ ratCorootForm_ratMap P i x)

/-- Every raising operator vanishes on the straight path `straight λ`. -/
@[simp]
theorem normalCrystal_e_straight {lam : X} (hlam : lam ∈ dominantChamber P b) (i : b.support) :
    (normalCrystal hlam).e i (straight lam) = none :=
  (forall_normalCrystal_e_eq_none_iff hlam (straight lam)).mpr rfl i

/-- **Generation of `B(λ)` from the straight path**: every Lakshmibai–Seshadri path of dominant
shape `λ` is obtained from `straight λ` by a finite word of lowering operators. -/
theorem exists_normalCrystal_fWord_straight {lam : X} (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    ∃ w : List b.support, (normalCrystal hlam).fWord w (straight lam) = some π := by
  have := LSPath.finite hlam
  exact (normalCrystal hlam).exists_fWord_eq_some_of_unique_highest
    (fun ρ hρ ↦ (forall_normalCrystal_e_eq_none_iff hlam ρ).mp hρ) π

omit [Finite ι] [P.IsReduced] in
private theorem reachable_of_fWord_eq_some {B : Type*} {c : NormalCrystal P b B}
    {w : List b.support} {x y : B} (h : c.fWord w x = some y) : c.graph.Reachable x y := by
  induction w generalizing x with
  | nil =>
    rw [NormalCrystal.fWord_nil] at h
    exact Option.some.inj h ▸ .refl x
  | cons i w ih =>
    obtain ⟨z, hz, hw⟩ := Option.bind_eq_some_iff.mp (c.fWord_cons i w x ▸ h)
    exact (c.graph_adj_of_f_eq_some hz).reachable.trans (ih hw)

/-- **The crystal graph of `B(λ)` is connected.** -/
theorem connected_normalCrystal_graph {lam : X} (hlam : lam ∈ dominantChamber P b) :
    (normalCrystal hlam).graph.Connected := by
  have : Nonempty (LSPath P b lam) := ⟨straight lam⟩
  refine ⟨fun π₁ π₂ ↦ ?_⟩
  obtain ⟨w₁, hw₁⟩ := exists_normalCrystal_fWord_straight hlam π₁
  obtain ⟨w₂, hw₂⟩ := exists_normalCrystal_fWord_straight hlam π₂
  exact (reachable_of_fWord_eq_some hw₁).symm.trans (reachable_of_fWord_eq_some hw₂)

end CanonicalCrystal

/-! ### Equivalence with realized path crystals and the operator-generated component -/

section ComponentComparison

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : X →+ V} {F : b.support → Dual 𝕜 V}

omit [Finite ι] [P.IsReduced] in
private theorem reflTransGen_rootStep_of_lowerWord_eq_some
    {w : List b.support} {π ρ : PLPath 𝕜 V}
    (h : PLPath.lowerWord F (fun i ↦ f (P.root i)) w π = some ρ) :
    Relation.ReflTransGen (PLPath.RootStep b f F) π ρ := by
  induction w generalizing π with
  | nil =>
    rw [PLPath.lowerWord_nil] at h
    exact Option.some.inj h ▸ .refl
  | cons i w ih =>
    obtain ⟨σ, hσ, hw⟩ := Option.bind_eq_some_iff.mp (PLPath.lowerWord_cons i w π ▸ h)
    exact .head (.of_lower_eq_some hσ) (ih hw)

/-- **Equivalence between Lakshmibai–Seshadri paths and lowering words from the straight path.**
In every realization `(𝕜, V, f, F)` whose height forms agree with the simple coroots (with no
injectivity assumption on `f`), the realized LS paths of dominant shape `λ` are precisely the paths
obtained from `PLPath.straight 𝕜 (f λ)` by finite words of lowering operators. -/
theorem mem_range_toPLPath_iff_exists_lowerWord_straight {lam : X}
    (hlam : lam ∈ dominantChamber P b)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (q : PLPath 𝕜 V) :
    q ∈ range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      ∃ w : List b.support,
        PLPath.lowerWord F (fun i ↦ f (P.root i)) w (PLPath.straight 𝕜 (f lam)) = some q := by
  constructor
  · rintro ⟨π, rfl⟩
    obtain ⟨w, hw⟩ := exists_normalCrystal_fWord_straight hlam π
    refine ⟨w, ?_⟩
    simpa only [toPLPath_straight] using toPLPath_of_normalCrystal_fWord_eq_some hlam hF hw
  · rintro ⟨w, hw⟩
    have hS := isCrystalSet_range_toPLPath (𝕜 := 𝕜) (f := f) (F := F) hlam hF
    have hstart : PLPath.straight 𝕜 (f lam) ∈ range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f :=
      ⟨straight lam, toPLPath_straight 𝕜 f⟩
    exact hS.mem_of_reflTransGen_rootStep (reflTransGen_rootStep_of_lowerWord_eq_some hw) hstart

/-- In any injective compatible realization, the connected component of `PLPath.straight 𝕜 (f λ)` in
Littelmann's ambient integral-path crystal consists precisely of the realized LS paths of shape `λ`.
-/
theorem mem_supp_connectedComponentMk_straight_iff {lam : X}
    (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hlam : lam ∈ dominantChamber P b)
    (x : {π : PLPath 𝕜 V | PLPath.IsIntegralPath b f F π}) :
    x ∈ ((PLPath.normalCrystal hf hF).graph.connectedComponentMk
        ⟨PLPath.straight 𝕜 (f lam),
          PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩).supp ↔
      x.1 ∈ range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f := by
  rw [PLPath.mem_supp_connectedComponentMk_normalCrystalOn_iff]
  constructor
  · intro hwalk
    have hS := isCrystalSet_range_toPLPath (𝕜 := 𝕜) (f := f) (F := F) hlam hF
    exact hS.mem_of_reflTransGen_rootStep hwalk ⟨straight lam, toPLPath_straight 𝕜 f⟩
  · intro hx
    obtain ⟨w, hw⟩ := (mem_range_toPLPath_iff_exists_lowerWord_straight hlam hF x.1).mp hx
    exact reflTransGen_rootStep_of_lowerWord_eq_some hw

/-- In any injective compatible realization, `toPLPath 𝕜 f` induces a strict crystal isomorphism
from `LSPath.normalCrystal hlam` onto the realized path crystal `PLPath.normalCrystalOn`. -/
noncomputable def toPLPathRangeIso {lam : X} (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalOn hf hF (isCrystalSet_range_toPLPath hlam hF)) where
  toEquiv := Equiv.ofInjective (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f)
    (toPLPath_injective_of_coroot' hlam hf.injOn hF)
  wt_toFun π := hf ((PLPath.apply_normalCrystalOn_wt _).trans
    (apply_normalCrystal_wt hlam f π).symm)
  e_toFun i π := by
    rw [PLPath.normalCrystalOn_e_eq_map_iff]
    cases he : (normalCrystal hlam).e i π with
    | none => simpa using (normalCrystal_e_eq_none_iff hlam hF).mp he
    | some π' => simpa using toPLPath_of_normalCrystal_e_eq_some hlam hF he

@[simp]
theorem toPLPathRangeIso_apply {lam : X} (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (toPLPathRangeIso hf hF hlam π).1 = π.toPLPath 𝕜 f :=
  (rfl)

/-- **Identification of `B(λ)` with the operator-generated component of the straight path.**
In any injective compatible realization `(𝕜, V, f, F)`, `π ↦ π.toPLPath 𝕜 f` is a strict crystal
isomorphism from `LSPath.normalCrystal hlam` onto `PLPath.normalCrystalComponent` of
`PLPath.straight 𝕜 (f λ)`. -/
noncomputable def toPLPathComponentIso {lam : X} (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal.StrictIso (normalCrystal hlam)
      (PLPath.normalCrystalComponent hf hF
        ⟨PLPath.straight 𝕜 (f lam),
          PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) where
  toEquiv :=
    { toFun := fun π ↦
        ⟨⟨π.toPLPath 𝕜 f, π.isIntegralPath_toPLPath hlam hF⟩,
          (mem_supp_connectedComponentMk_straight_iff hf hF hlam _).mpr (mem_range_self π)⟩
      invFun := fun x ↦
        Classical.choose ((mem_supp_connectedComponentMk_straight_iff hf hF hlam x.1).mp x.2)
      left_inv := fun π ↦
        toPLPath_injective_of_coroot' hlam hf.injOn hF
          (Classical.choose_spec
            ((mem_supp_connectedComponentMk_straight_iff hf hF hlam
              ⟨π.toPLPath 𝕜 f, π.isIntegralPath_toPLPath hlam hF⟩).mp
              ((mem_supp_connectedComponentMk_straight_iff hf hF hlam _).mpr (mem_range_self π))))
      right_inv := fun x ↦ Subtype.ext (Subtype.ext
        (Classical.choose_spec
          ((mem_supp_connectedComponentMk_straight_iff hf hF hlam x.1).mp x.2))) }
  wt_toFun π := hf (by
    dsimp only [PLPath.normalCrystalComponent]
    rw [NormalCrystal.component_eq_restrict, NormalCrystal.restrict_wt,
      PLPath.apply_normalCrystalOn_wt]
    exact (apply_normalCrystal_wt hlam f π).symm)
  e_toFun i π := by
    dsimp only [PLPath.normalCrystalComponent]
    rw [NormalCrystal.component_eq_restrict]
    cases he : (normalCrystal hlam).e i π with
    | none =>
      simp only [Option.map_none]
      cases h' : ((PLPath.normalCrystal hf hF).restrict _ _).e i _ with
      | none => rfl
      | some y =>
        rw [NormalCrystal.restrict_e_eq_some_iff, PLPath.normalCrystalOn_e_eq_some_iff,
          (normalCrystal_e_eq_none_iff hlam hF).mp he] at h'
        cases h'
    | some π' =>
      rw [Option.map_some, NormalCrystal.restrict_e_eq_some_iff,
        PLPath.normalCrystalOn_e_eq_some_iff]
      exact toPLPath_of_normalCrystal_e_eq_some hlam hF he

@[simp]
theorem toPLPathComponentIso_apply {lam : X} (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (toPLPathComponentIso hf hF hlam π).1.1 = π.toPLPath 𝕜 f :=
  (rfl)

/-- Specialization of `LSPath.toPLPathComponentIso` to the canonical scalar-extension crystal
`PLPath.baseChangeNormalCrystal b 𝕜` on `𝕜 ⊗[ℤ] X`. -/
noncomputable def toPLPathBaseChangeComponentIso [Module.Free ℤ Y] [Module.Finite ℤ Y]
    {lam : X} (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal.StrictIso (normalCrystal hlam)
      ((PLPath.baseChangeNormalCrystal b 𝕜).component
        ((PLPath.baseChangeNormalCrystal b 𝕜).graph.connectedComponentMk
          ⟨PLPath.straight 𝕜 ((1 : 𝕜) ⊗ₜ[ℤ] lam),
            PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam
              (f := (TensorProduct.mk ℤ 𝕜 X 1).toAddMonoidHom)
              (F := fun i ↦ (P.baseChange 𝕜).coroot' i.1) (fun i x ↦ by simp)⟩)) :=
  toPLPathComponentIso (P.tensorProduct_mk_injective 𝕜)
    (F := fun i ↦ (P.baseChange 𝕜).coroot' i.1) (fun i x ↦ by simp) hlam

@[simp]
theorem toPLPathBaseChangeComponentIso_apply [Module.Free ℤ Y] [Module.Finite ℤ Y]
    {lam : X} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (toPLPathBaseChangeComponentIso (𝕜 := 𝕜) hlam π).1.1 =
      π.toPLPath 𝕜 (TensorProduct.mk ℤ 𝕜 X 1).toAddMonoidHom :=
  (rfl)

end ComponentComparison

/-! ### Crystal duality via path reversal -/

section Duality

/-- **Crystal duality for `B(λ)`**: path reversal `LSPath.reverse` is a strict crystal isomorphism
from `(LSPath.normalCrystal hlam).dual` to `LSPath.normalCrystal` of the dual dominant weight
`-w₀ λ`. -/
noncomputable def reverseCrystalIso {lam : X} (hlam : lam ∈ dominantChamber P b) :
    NormalCrystal.StrictIso (normalCrystal hlam).dual
      (normalCrystal (have := P.flip_isReduced; neg_smul_mem_dominantChamber_longestElement hlam))
    where
  toEquiv := reverse hlam
  wt_toFun π := by
    have := P.flip_isReduced
    rw [NormalCrystal.dual_wt]
    have h : ratMap X ((normalCrystal (neg_smul_mem_dominantChamber_longestElement hlam)).wt
        (reverse hlam π)) = ratMap X (-(normalCrystal hlam).wt π) := by
      rw [ratMap_normalCrystal_wt, toPLPath_reverse, PLPath.endpoint_reverse, map_neg,
        ratMap_normalCrystal_wt]
    exact P.tensorProduct_mk_injective ℚ
      (by simpa only [ratMap, LinearMap.toAddMonoidHom_coe, Equiv.toFun_as_coe] using h)
  e_toFun i π := by
    have := P.flip_isReduced
    set hlam' := neg_smul_mem_dominantChamber_longestElement hlam
    cases hf' : (normalCrystal hlam).f i π with
    | none =>
      simp only [NormalCrystal.dual_e, Equiv.toFun_as_coe, hf', Option.map_none]
      rw [normalCrystal_e_eq_none_iff_rat hlam', toPLPath_reverse, PLPath.raise_reverse,
        (normalCrystal_f_eq_none_iff_rat hlam).mp hf', Option.map_none]
    | some π' =>
      simp only [NormalCrystal.dual_e, Equiv.toFun_as_coe, hf', Option.map_some]
      rw [normalCrystal_e_eq_some_iff_rat hlam', toPLPath_reverse, toPLPath_reverse,
        PLPath.raise_reverse, (normalCrystal_f_eq_some_iff_rat hlam).mp hf', Option.map_some]

@[simp]
theorem coe_reverseCrystalIso {lam : X} (hlam : lam ∈ dominantChamber P b) :
    ⇑(reverseCrystalIso hlam) = reverse hlam :=
  (rfl)

@[simp]
theorem coe_reverseCrystalIso_symm {lam : X} (hlam : lam ∈ dominantChamber P b) :
    ⇑(reverseCrystalIso hlam).symm = (reverse hlam).symm :=
  (NormalCrystal.StrictIso.coe_toEquiv_symm (reverseCrystalIso hlam)).symm

end Duality

/-! ### Central weights, `λ = 0`, and empty root systems -/

section Central

/-- If `λ` annihilates every simple coroot (covering `λ = 0`, pure central characters, and empty
root systems), then every Lakshmibai–Seshadri path of shape `λ` is the straight path. -/
theorem eq_straight_of_forall_coroot'_eq_zero {lam : X}
    (hlam : ∀ i ∈ b.support, P.coroot' i lam = 0) (π : LSPath P b lam) :
    π = straight lam := by
  have := P.flip_isReduced
  have hdom : lam ∈ dominantChamber P b :=
    (mem_dominantChamber P b lam).mpr fun i hi ↦ (hlam i hi).ge
  apply π.eq_straight_iff_dir_zero_eq_one.mpr
  refine eq_of_isMinimalCosetRep_of_smul_eq hdom (π.dir 0).2
    ((weylCoxeterSystem P b).isMinimalCosetRep_one _) ?_
  rw [smul_eq_self_of_forall_coroot'_eq_zero b hlam, one_smul]

/-- **Central weights give one-element crystals.** Whenever `λ` annihilates all simple coroots
(including `λ = 0` and empty root systems), `LSPath.normalCrystal` is strictly isomorphic to
`NormalCrystal.central λ`. -/
noncomputable def centralIso (lam : X)
    (hlam : ∀ i : b.support, P.toLinearMap lam (P.coroot i) = 0) :
    NormalCrystal.StrictIso
      (normalCrystal ((mem_dominantChamber P b lam).mpr fun i hi ↦ (hlam ⟨i, hi⟩).ge))
      (NormalCrystal.central lam hlam) where
  toEquiv :=
    { toFun := fun _ ↦ PUnit.unit
      invFun := fun _ ↦ straight lam
      left_inv := fun π ↦
        (eq_straight_of_forall_coroot'_eq_zero (fun i hi ↦ hlam ⟨i, hi⟩) π).symm
      right_inv := fun _ ↦ rfl }
  wt_toFun π := by
    rw [eq_straight_of_forall_coroot'_eq_zero (fun i hi ↦ hlam ⟨i, hi⟩) π,
      normalCrystal_wt_straight, NormalCrystal.central_wt]
  e_toFun i π := by
    rw [eq_straight_of_forall_coroot'_eq_zero (fun i hi ↦ hlam ⟨i, hi⟩) π,
      normalCrystal_e_straight, NormalCrystal.central_e, Option.map_none]

@[simp]
theorem centralIso_symm_apply (lam : X)
    (hlam : ∀ i : b.support, P.toLinearMap lam (P.coroot i) = 0) (u : PUnit) :
    (centralIso lam hlam).symm u = straight lam :=
  eq_straight_of_forall_coroot'_eq_zero (fun i hi ↦ hlam ⟨i, hi⟩) _

/-- The crystal `B(0)` is strictly isomorphic to the trivial zero-weight crystal
`NormalCrystal.central 0`. -/
noncomputable def zeroIso :
    NormalCrystal.StrictIso (normalCrystal (zero_mem_dominantChamber P b))
      (NormalCrystal.central (P := P) (b := b) 0 (by simp)) :=
  centralIso 0 (by simp)

end Central

end LSPath

/-! ### Finiteness of the operator-generated straight-path component -/

namespace PLPath

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- **Finiteness of the straight-path component `B(λ)`.** For dominant `λ` in any injective
compatible realization, the connected component of `straight 𝕜 (f λ)` in Littelmann's integral-path
crystal is finite. -/
theorem finite_supp_connectedComponentMk_straight (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam : X} (hlam : lam ∈ dominantChamber P b) :
    Finite ((normalCrystal hf hF).graph.connectedComponentMk
      ⟨straight 𝕜 (f lam), isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) := by
  have := LSPath.finite hlam
  exact Finite.of_equiv _ (LSPath.toPLPathComponentIso hf hF hlam).toEquiv

end PLPath

end TauCeti
