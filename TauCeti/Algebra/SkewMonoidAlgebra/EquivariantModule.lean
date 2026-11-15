/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.SkewMonoidAlgebra.Lift
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Algebra.Algebra.SMulDistribClass
public import TauCeti.Algebra.Group.Action.MulDistribMulAction

/-!
# Skew monoid algebra modules and equivariant modules

Let a monoid `G` act on a semiring `A` by semiring endomorphisms (`MulSemiringAction G A`). A
*semilinear* (or *equivariant*) `G`-action on a left `A`-module `M` is a distributive action of `G`
satisfying

  `g • (a • m) = (g • a) • (g • m)`

for all `g : G`, `a : A`, and `m : M` — Mathlib's `SMulDistribClass G A M`. Because `single g a` in
`SkewMonoidAlgebra A G` decomposes as `single 1 a * single g 1` with the commutation law
`single g 1 * single 1 a = single 1 (g • a) * single g 1`, semilinear `G`-actions on `A`-modules
are in bijection with left module structures over `SkewMonoidAlgebra A G`:

* Given `[Module A M] [DistribMulAction G M] [SMulDistribClass G A M]`, the universal property
  `SkewMonoidAlgebra.liftNCRingHom` combines `Module.toAddMonoidEnd A M` and
  `DistribMulAction.toAddMonoidEnd G M` into a ring homomorphism
  `TauCeti.skewMonoidAlgebraToAddMonoidEnd A G M : SkewMonoidAlgebra A G →+* AddMonoid.End M`
  sending `single g a` to `m ↦ a • (g • m)`. The wrapper `TauCeti.EquivariantAsModule A G M`
  carries the resulting `SkewMonoidAlgebra A G`-module structure.
* Conversely, given `[Module (SkewMonoidAlgebra A G) N]`, restricting along
  `SkewMonoidAlgebra.singleOneRingHom : A →+* SkewMonoidAlgebra A G` and
  `SkewMonoidAlgebra.of A G : G →* SkewMonoidAlgebra A G` equips the wrapper
  `TauCeti.EquivariantOfModule A G N` with `[Module A]`, `[DistribMulAction G]`, and
  `[SMulDistribClass G A]`.
* Morphisms between equivariant `A`-modules are bundled in `TauCeti.EquivariantLinearMap A G M M'`
  (and equivalences in `TauCeti.EquivariantLinearEquiv A G M M'`), which correspond bijectively to
  `SkewMonoidAlgebra A G`-linear maps `EquivariantAsModule A G M →ₗ EquivariantAsModule A G M'`
  (`TauCeti.EquivariantLinearMap.equivLinearMapAsModule`).

All constructions in this file hold at full semiring/monoid generality (`[Semiring A] [Monoid G]`),
requiring neither additive inverses on `A` or `M`, nor inverses in `G`, nor an auxiliary commutative
base ring. When `A` is an algebra over a commutative semiring `k` with `k`-linear `G`-action,
`TauCeti.skewMonoidAlgebraToModuleEnd` upgrades the action homomorphism to a `k`-algebra map into
`Module.End k M`, and restricting scalars of `EquivariantAsModule A G M` to `k` recovers `M`
`k`-linearly (preserving `Module.finrank`).

## Main definitions

* `TauCeti.skewMonoidAlgebraToAddMonoidEnd`: the action homomorphism
  `SkewMonoidAlgebra A G →+* AddMonoid.End M`.
* `TauCeti.skewMonoidAlgebraToModuleEnd`: its `k`-algebra upgrade
  `SkewMonoidAlgebra A G →ₐ[k] Module.End k M`.
* `TauCeti.EquivariantAsModule`: wrapper equipping an equivariant `(A, G)`-module with its left
  `SkewMonoidAlgebra A G`-module structure.
* `TauCeti.EquivariantOfModule`: wrapper equipping a left `SkewMonoidAlgebra A G`-module with its
  underlying `A`-module and semilinear `G`-action.
* `TauCeti.EquivariantLinearMap`, `TauCeti.EquivariantLinearEquiv`: `A`-linear, `G`-equivariant
  maps and equivalences, together with `TauCeti.EquivariantLinearMap.equivLinearMapAsModule`,
  `TauCeti.EquivariantLinearMap.equivLinearMapOfModule`, and the roundtrip equivalences
  `TauCeti.equivariantAsOfModuleLinearEquiv` and `TauCeti.equivariantOfAsModuleEquiv`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics **82** (1993), §1.5.
-/

public noncomputable section

namespace TauCeti

/-! ### Action homomorphisms from `SkewMonoidAlgebra A G` -/

section ActionHom

variable (A G M : Type*) [Semiring A] [Monoid G] [MulSemiringAction G A]
  [AddCommMonoid M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]

/-- **Action ring homomorphism of an equivariant module.** Given an `A`-module `M` with a
semilinear `G`-action (`SMulDistribClass G A M`), the `A`-action and the `G`-action combine into a
ring homomorphism `SkewMonoidAlgebra A G →+* AddMonoid.End M` sending `single g a` to
`m ↦ a • (g • m)`. -/
def skewMonoidAlgebraToAddMonoidEnd : SkewMonoidAlgebra A G →+* AddMonoid.End M :=
  SkewMonoidAlgebra.liftNCRingHom (Module.toAddMonoidEnd A M)
    (DistribMulAction.toAddMonoidEnd G M) fun {a g} ↦ by
      ext m
      exact (smul_distrib_smul g a m).symm

variable {A G M}

@[simp]
theorem skewMonoidAlgebraToAddMonoidEnd_single (g : G) (a : A) (m : M) :
    skewMonoidAlgebraToAddMonoidEnd A G M (SkewMonoidAlgebra.single g a) m = a • (g • m) := by
  -- `liftNCRingHom` evaluates via `liftNC`, which sends `single g a` to `f a * γ g`.
  change (SkewMonoidAlgebra.liftNC (Module.toAddMonoidEnd A M).toAddMonoidHom
    (DistribMulAction.toAddMonoidEnd G M) (SkewMonoidAlgebra.single g a)) m = a • (g • m)
  rw [SkewMonoidAlgebra.liftNC_single]
  rfl

@[simp]
theorem skewMonoidAlgebraToAddMonoidEnd_singleOneRingHom (a : A) (m : M) :
    skewMonoidAlgebraToAddMonoidEnd A G M
      (SkewMonoidAlgebra.singleOneRingHom (G := G) a) m = a • m := by
  simp [SkewMonoidAlgebra.singleOneRingHom]

theorem skewMonoidAlgebraToAddMonoidEnd_of (g : G) (m : M) :
    skewMonoidAlgebraToAddMonoidEnd A G M (SkewMonoidAlgebra.of A G g) m = g • m := by
  simp

end ActionHom

section AlgebraActionHom

variable (k A G M : Type*) [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G]
  [MulSemiringAction G A] [SMulCommClass G k A] [AddCommMonoid M] [Module k M] [Module A M]
  [IsScalarTower k A M] [DistribMulAction G M] [SMulDistribClass G A M]

/-- **`k`-algebra action homomorphism of an equivariant module.** When `G` acts `k`-linearly on a
`k`-algebra `A` and `M` is a compatible `(k, A)`-module with semilinear `G`-action,
`skewMonoidAlgebraToAddMonoidEnd` upgrades to a `k`-algebra homomorphism
`SkewMonoidAlgebra A G →ₐ[k] Module.End k M` sending `single g a` to `m ↦ a • (g • m)`. -/
def skewMonoidAlgebraToModuleEnd : SkewMonoidAlgebra A G →ₐ[k] Module.End k M :=
  letI : SMulCommClass G k M := MulSemiringAction.smulCommClass_of_smulDistribClass k A G M
  SkewMonoidAlgebra.liftNCAlgHom (Algebra.lsmul k k M)
    (DistribMulAction.toModuleEnd k M) fun {a g} ↦ by
      ext m
      exact (smul_distrib_smul g a m).symm

variable {k A G M}

@[simp]
theorem skewMonoidAlgebraToModuleEnd_single (g : G) (a : A) (m : M) :
    skewMonoidAlgebraToModuleEnd k A G M (SkewMonoidAlgebra.single g a) m = a • (g • m) := by
  have : SMulCommClass G k M := MulSemiringAction.smulCommClass_of_smulDistribClass k A G M
  -- `liftNCAlgHom` shares its underlying function with `liftNC` on `single g a`.
  change (SkewMonoidAlgebra.liftNC
    (Algebra.lsmul k k M : A →ₐ[k] Module.End k M).toLinearMap.toAddMonoidHom
    (DistribMulAction.toModuleEnd k M) (SkewMonoidAlgebra.single g a)) m = a • (g • m)
  simp

@[simp]
theorem skewMonoidAlgebraToModuleEnd_singleOneRingHom (a : A) (m : M) :
    skewMonoidAlgebraToModuleEnd k A G M
      (SkewMonoidAlgebra.singleOneRingHom (G := G) a) m = a • m := by
  simp [SkewMonoidAlgebra.singleOneRingHom]

theorem skewMonoidAlgebraToModuleEnd_of (g : G) (m : M) :
    skewMonoidAlgebraToModuleEnd k A G M (SkewMonoidAlgebra.of A G g) m = g • m := by
  simp

/-- `skewMonoidAlgebraToModuleEnd` agrees pointwise with `skewMonoidAlgebraToAddMonoidEnd`. -/
theorem skewMonoidAlgebraToModuleEnd_apply (x : SkewMonoidAlgebra A G) (m : M) :
    skewMonoidAlgebraToModuleEnd k A G M x m = skewMonoidAlgebraToAddMonoidEnd A G M x m := by
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, hp, hq]
    rfl
  | single g a => simp

end AlgebraActionHom

/-! ### `EquivariantAsModule`: from equivariant modules to `SkewMonoidAlgebra A G`-modules -/

/-- Wrapper equipping an `A`-module `M` carrying a semilinear `G`-action (`SMulDistribClass G A M`)
with its induced left `SkewMonoidAlgebra A G`-module structure, where `single g a` acts by
`m ↦ a • (g • m)`. -/
@[ext]
structure EquivariantAsModule (A G M : Type*) where
  /-- Wrap an element of `M` in `EquivariantAsModule A G M`. -/
  of ::
  /-- The underlying element of `M`. -/
  val : M

namespace EquivariantAsModule

section Additive

variable {A G M : Type*}

@[simp]
theorem of_val (x : EquivariantAsModule A G M) : of x.val = x :=
  (rfl)

instance [Zero M] : Zero (EquivariantAsModule A G M) := ⟨of 0⟩
instance [Add M] : Add (EquivariantAsModule A G M) := ⟨fun x y ↦ of (x.val + y.val)⟩
instance [Neg M] : Neg (EquivariantAsModule A G M) := ⟨fun x ↦ of (-x.val)⟩
instance [Sub M] : Sub (EquivariantAsModule A G M) := ⟨fun x y ↦ of (x.val - y.val)⟩

@[simp] theorem val_zero [Zero M] : (0 : EquivariantAsModule A G M).val = 0 := (rfl)
@[simp] theorem of_zero [Zero M] : of (A := A) (G := G) (0 : M) = 0 := (rfl)

@[simp]
theorem val_add [Add M] (x y : EquivariantAsModule A G M) :
    (x + y).val = x.val + y.val :=
  (rfl)

@[simp]
theorem of_add [Add M] (m n : M) :
    of (A := A) (G := G) (m + n) = of m + of n :=
  (rfl)

@[simp]
theorem val_neg [Neg M] (x : EquivariantAsModule A G M) : (-x).val = -x.val :=
  (rfl)

@[simp]
theorem of_neg [Neg M] (m : M) : of (A := A) (G := G) (-m) = -of m :=
  (rfl)

@[simp]
theorem val_sub [Sub M] (x y : EquivariantAsModule A G M) :
    (x - y).val = x.val - y.val :=
  (rfl)

@[simp]
theorem of_sub [Sub M] (m n : M) :
    of (A := A) (G := G) (m - n) = of m - of n :=
  (rfl)

instance [AddCommMonoid M] : SMul ℕ (EquivariantAsModule A G M) := ⟨fun n x ↦ of (n • x.val)⟩
instance [AddCommGroup M] : SMul ℤ (EquivariantAsModule A G M) := ⟨fun z x ↦ of (z • x.val)⟩

instance [AddCommMonoid M] : AddCommMonoid (EquivariantAsModule A G M) where
  nsmul n x := n • x
  add_assoc _ _ _ := EquivariantAsModule.ext (add_assoc _ _ _)
  zero_add _ := EquivariantAsModule.ext (zero_add _)
  add_zero _ := EquivariantAsModule.ext (add_zero _)
  nsmul_zero _ := EquivariantAsModule.ext (zero_smul ℕ _)
  nsmul_succ _ _ := EquivariantAsModule.ext (succ_nsmul _ _)
  add_comm _ _ := EquivariantAsModule.ext (add_comm _ _)

instance [AddCommGroup M] : AddCommGroup (EquivariantAsModule A G M) where
  zsmul z x := z • x
  sub_eq_add_neg _ _ := EquivariantAsModule.ext (sub_eq_add_neg _ _)
  zsmul_zero' _ := EquivariantAsModule.ext (zero_smul ℤ _)
  zsmul_succ' _ _ := EquivariantAsModule.ext (SubNegMonoid.zsmul_succ' _ _)
  zsmul_neg' _ _ := EquivariantAsModule.ext (SubNegMonoid.zsmul_neg' _ _)
  neg_add_cancel _ := EquivariantAsModule.ext (neg_add_cancel _)

variable (A G M) in
/-- Additive equivalence identifying `EquivariantAsModule A G M` with `M`. -/
def addEquiv [AddCommMonoid M] : EquivariantAsModule A G M ≃+ M where
  toFun := val
  invFun := of
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem addEquiv_apply [AddCommMonoid M] (x : EquivariantAsModule A G M) :
    addEquiv A G M x = x.val :=
  (rfl)

@[simp]
theorem addEquiv_symm_apply [AddCommMonoid M] (m : M) :
    (addEquiv A G M).symm m = of m :=
  (rfl)

end Additive

section Module

variable {A G M : Type*} [Semiring A] [Monoid G] [MulSemiringAction G A]
  [AddCommMonoid M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]

instance : SMul (SkewMonoidAlgebra A G) (EquivariantAsModule A G M) where
  smul r x := of (skewMonoidAlgebraToAddMonoidEnd A G M r x.val)

/-- An arbitrary element of `SkewMonoidAlgebra A G` acts on `EquivariantAsModule A G M` via
`skewMonoidAlgebraToAddMonoidEnd`. -/
theorem val_smul (r : SkewMonoidAlgebra A G) (x : EquivariantAsModule A G M) :
    (r • x).val = skewMonoidAlgebraToAddMonoidEnd A G M r x.val :=
  (rfl)

instance : Module (SkewMonoidAlgebra A G) (EquivariantAsModule A G M) where
  one_smul x := EquivariantAsModule.ext <| by rw [val_smul, map_one]; rfl
  mul_smul r s x := EquivariantAsModule.ext <| by rw [val_smul, val_smul, val_smul, map_mul]; rfl
  smul_zero r := EquivariantAsModule.ext <| by rw [val_smul, val_zero, map_zero]
  smul_add r x y := EquivariantAsModule.ext <| by
    rw [val_smul, val_add, val_add, val_smul, val_smul, map_add]
  add_smul r s x := EquivariantAsModule.ext <| by
    rw [val_smul, val_add, val_smul, val_smul, map_add]; rfl
  zero_smul x := EquivariantAsModule.ext <| by rw [val_smul, map_zero]; rfl

@[simp]
theorem single_smul_of (g : G) (a : A) (m : M) :
    SkewMonoidAlgebra.single g a • of (A := A) (G := G) m = of (a • (g • m)) := by
  ext
  simp [val_smul]

@[simp]
theorem val_single_smul (g : G) (a : A) (x : EquivariantAsModule A G M) :
    (SkewMonoidAlgebra.single g a • x).val = a • (g • x.val) := by
  simp [val_smul]

@[simp]
theorem singleOneRingHom_smul_of (a : A) (m : M) :
    SkewMonoidAlgebra.singleOneRingHom (G := G) a • of (A := A) (G := G) m = of (a • m) := by
  ext
  simp [val_smul]

@[simp]
theorem val_singleOneRingHom_smul (a : A) (x : EquivariantAsModule A G M) :
    (SkewMonoidAlgebra.singleOneRingHom (G := G) a • x).val = a • x.val := by
  simp [val_smul]

theorem of_smul_of (g : G) (m : M) :
    SkewMonoidAlgebra.of A G g • of (A := A) (G := G) m = of (g • m) := by
  simp

theorem val_of_smul (g : G) (x : EquivariantAsModule A G M) :
    (SkewMonoidAlgebra.of A G g • x).val = g • x.val := by
  simp

/-- On the canonical equivariant module `A` itself (via `TauCeti.smulDistribClass_self`),
`single g a` acts by `b ↦ a * g • b`. -/
theorem single_smul_self_of (g : G) (a b : A) :
    SkewMonoidAlgebra.single g a • of (A := A) (G := G) b = of (a * g • b) := by
  simp

/-- On the canonical equivariant module `A` itself, applying `of A G g` after `single 1 a` to `1`
recovers `g • a`. -/
theorem of_smul_singleOneRingHom_smul_one (g : G) (a : A) :
    SkewMonoidAlgebra.of A G g •
      (SkewMonoidAlgebra.singleOneRingHom (G := G) a • of (A := A) (G := G) (1 : A)) =
      of (g • a) := by
  simp

end Module

section RestrictScalars

variable (k A G M : Type*) [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G]
  [MulSemiringAction G A] [SMulCommClass G k A] [AddCommMonoid M] [Module k M] [Module A M]
  [IsScalarTower k A M] [DistribMulAction G M] [SMulDistribClass G A M]

/-- Restricting the `SkewMonoidAlgebra A G`-module `EquivariantAsModule A G M` to `k` along
`algebraMap k (SkewMonoidAlgebra A G)` recovers `M` `k`-linearly. -/
def restrictScalarsLinearEquiv :
    RestrictScalars k (SkewMonoidAlgebra A G) (EquivariantAsModule A G M) ≃ₗ[k] M where
  toFun x := (RestrictScalars.addEquiv k (SkewMonoidAlgebra A G) _ x).val
  invFun m := (RestrictScalars.addEquiv k (SkewMonoidAlgebra A G) _).symm (of m)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    rw [RingHom.id_apply, RestrictScalars.addEquiv_map_smul]
    -- `algebraMap k (SkewMonoidAlgebra A G) r` is `single 1 (algebraMap k A r)`.
    change (SkewMonoidAlgebra.single (1 : G) (algebraMap k A r) •
      RestrictScalars.addEquiv k (SkewMonoidAlgebra A G) (EquivariantAsModule A G M) x).val = _
    rw [val_single_smul, one_smul, algebraMap_smul]

theorem algebraMap_smul_of (r : k) (m : M) :
    algebraMap k (SkewMonoidAlgebra A G) r • of (A := A) (G := G) m = of (r • m) := by
  rw [SkewMonoidAlgebra.coe_algebraMap, Function.comp_apply, single_smul_of, one_smul,
    algebraMap_smul]

theorem val_algebraMap_smul (r : k) (x : EquivariantAsModule A G M) :
    (algebraMap k (SkewMonoidAlgebra A G) r • x).val = r • x.val := by
  rw [SkewMonoidAlgebra.coe_algebraMap, Function.comp_apply, val_single_smul, one_smul,
    algebraMap_smul]

@[simp]
theorem restrictScalarsLinearEquiv_apply
    (x : RestrictScalars k (SkewMonoidAlgebra A G) (EquivariantAsModule A G M)) :
    restrictScalarsLinearEquiv k A G M x =
      (RestrictScalars.addEquiv k (SkewMonoidAlgebra A G) _ x).val :=
  (rfl)

@[simp]
theorem restrictScalarsLinearEquiv_symm_apply (m : M) :
    (restrictScalarsLinearEquiv k A G M).symm m =
      (RestrictScalars.addEquiv k (SkewMonoidAlgebra A G) _).symm (of m) :=
  (rfl)

/-- Restricting `EquivariantAsModule A G M` to `k` preserves `Module.finrank`. -/
@[simp]
theorem finrank_restrictScalars :
    Module.finrank k (RestrictScalars k (SkewMonoidAlgebra A G) (EquivariantAsModule A G M)) =
      Module.finrank k M :=
  (restrictScalarsLinearEquiv k A G M).finrank_eq

end RestrictScalars

end EquivariantAsModule

/-! ### `EquivariantOfModule`: from `SkewMonoidAlgebra A G`-modules to equivariant modules -/

/-- Wrapper equipping a left `SkewMonoidAlgebra A G`-module `N` with its underlying `A`-module
structure (via `singleOneRingHom`) and semilinear `G`-action (via `SkewMonoidAlgebra.of A G`). -/
@[ext]
structure EquivariantOfModule (A G N : Type*) where
  /-- Wrap an element of `N` in `EquivariantOfModule A G N`. -/
  of ::
  /-- The underlying element of `N`. -/
  val : N

namespace EquivariantOfModule

section Additive

variable {A G N : Type*}

@[simp]
theorem of_val (x : EquivariantOfModule A G N) : of x.val = x :=
  (rfl)

instance [Zero N] : Zero (EquivariantOfModule A G N) := ⟨of 0⟩
instance [Add N] : Add (EquivariantOfModule A G N) := ⟨fun x y ↦ of (x.val + y.val)⟩
instance [Neg N] : Neg (EquivariantOfModule A G N) := ⟨fun x ↦ of (-x.val)⟩
instance [Sub N] : Sub (EquivariantOfModule A G N) := ⟨fun x y ↦ of (x.val - y.val)⟩

@[simp] theorem val_zero [Zero N] : (0 : EquivariantOfModule A G N).val = 0 := (rfl)
@[simp] theorem of_zero [Zero N] : of (A := A) (G := G) (0 : N) = 0 := (rfl)

@[simp]
theorem val_add [Add N] (x y : EquivariantOfModule A G N) :
    (x + y).val = x.val + y.val :=
  (rfl)

@[simp]
theorem of_add [Add N] (m n : N) :
    of (A := A) (G := G) (m + n) = of m + of n :=
  (rfl)

@[simp]
theorem val_neg [Neg N] (x : EquivariantOfModule A G N) : (-x).val = -x.val :=
  (rfl)

@[simp]
theorem of_neg [Neg N] (n : N) : of (A := A) (G := G) (-n) = -of n :=
  (rfl)

@[simp]
theorem val_sub [Sub N] (x y : EquivariantOfModule A G N) :
    (x - y).val = x.val - y.val :=
  (rfl)

@[simp]
theorem of_sub [Sub N] (m n : N) :
    of (A := A) (G := G) (m - n) = of m - of n :=
  (rfl)

instance [AddCommMonoid N] : SMul ℕ (EquivariantOfModule A G N) := ⟨fun n x ↦ of (n • x.val)⟩
instance [AddCommGroup N] : SMul ℤ (EquivariantOfModule A G N) := ⟨fun z x ↦ of (z • x.val)⟩

instance [AddCommMonoid N] : AddCommMonoid (EquivariantOfModule A G N) where
  nsmul n x := n • x
  add_assoc _ _ _ := EquivariantOfModule.ext (add_assoc _ _ _)
  zero_add _ := EquivariantOfModule.ext (zero_add _)
  add_zero _ := EquivariantOfModule.ext (add_zero _)
  nsmul_zero _ := EquivariantOfModule.ext (zero_smul ℕ _)
  nsmul_succ _ _ := EquivariantOfModule.ext (succ_nsmul _ _)
  add_comm _ _ := EquivariantOfModule.ext (add_comm _ _)

instance [AddCommGroup N] : AddCommGroup (EquivariantOfModule A G N) where
  zsmul z x := z • x
  sub_eq_add_neg _ _ := EquivariantOfModule.ext (sub_eq_add_neg _ _)
  zsmul_zero' _ := EquivariantOfModule.ext (zero_smul ℤ _)
  zsmul_succ' _ _ := EquivariantOfModule.ext (SubNegMonoid.zsmul_succ' _ _)
  zsmul_neg' _ _ := EquivariantOfModule.ext (SubNegMonoid.zsmul_neg' _ _)
  neg_add_cancel _ := EquivariantOfModule.ext (neg_add_cancel _)

variable (A G N) in
/-- Additive equivalence identifying `EquivariantOfModule A G N` with `N`. -/
def addEquiv [AddCommMonoid N] : EquivariantOfModule A G N ≃+ N where
  toFun := val
  invFun := of
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem addEquiv_apply [AddCommMonoid N] (x : EquivariantOfModule A G N) :
    addEquiv A G N x = x.val :=
  (rfl)

@[simp]
theorem addEquiv_symm_apply [AddCommMonoid N] (n : N) :
    (addEquiv A G N).symm n = of n :=
  (rfl)

end Additive

section Equivariant

variable {A G N : Type*} [Semiring A] [Monoid G] [MulSemiringAction G A]
  [AddCommMonoid N] [Module (SkewMonoidAlgebra A G) N]

instance : SMul A (EquivariantOfModule A G N) where
  smul a x := of (SkewMonoidAlgebra.singleOneRingHom (G := G) a • x.val)

@[simp]
theorem smul_coeff_of (a : A) (n : N) :
    a • of (A := A) (G := G) n = of (SkewMonoidAlgebra.singleOneRingHom (G := G) a • n) :=
  (rfl)

@[simp]
theorem val_smul_coeff (a : A) (x : EquivariantOfModule A G N) :
    (a • x).val = SkewMonoidAlgebra.singleOneRingHom (G := G) a • x.val :=
  (rfl)

instance : Module A (EquivariantOfModule A G N) where
  one_smul x := EquivariantOfModule.ext <| by rw [val_smul_coeff, map_one, one_smul]
  mul_smul a b x := EquivariantOfModule.ext <| by
    rw [val_smul_coeff, val_smul_coeff, val_smul_coeff, map_mul, mul_smul]
  smul_zero a := EquivariantOfModule.ext <| by rw [val_smul_coeff, val_zero, smul_zero]
  smul_add a x y := EquivariantOfModule.ext <| by
    rw [val_smul_coeff, val_add, val_add, val_smul_coeff, val_smul_coeff, smul_add]
  add_smul a b x := EquivariantOfModule.ext <| by
    rw [val_smul_coeff, val_add, val_smul_coeff, val_smul_coeff, map_add, add_smul]
  zero_smul x := EquivariantOfModule.ext <| by rw [val_smul_coeff, map_zero, zero_smul, val_zero]

instance : SMul G (EquivariantOfModule A G N) where
  smul g x := of (SkewMonoidAlgebra.of A G g • x.val)

theorem val_smul_group_eq_of_smul (g : G) (x : EquivariantOfModule A G N) :
    (g • x).val = SkewMonoidAlgebra.of A G g • x.val :=
  (rfl)

@[simp]
theorem smul_group_of (g : G) (n : N) :
    g • of (A := A) (G := G) n = of (SkewMonoidAlgebra.single g (1 : A) • n) :=
  EquivariantOfModule.ext (congrArg (· • n) (SkewMonoidAlgebra.of_apply A G g))

@[simp]
theorem val_smul_group (g : G) (x : EquivariantOfModule A G N) :
    (g • x).val = SkewMonoidAlgebra.single g (1 : A) • x.val :=
  congrArg (· • x.val) (SkewMonoidAlgebra.of_apply A G g)

instance : DistribMulAction G (EquivariantOfModule A G N) where
  one_smul x := EquivariantOfModule.ext <| by
    rw [val_smul_group_eq_of_smul, map_one, one_smul]
  mul_smul g h x := EquivariantOfModule.ext <| by
    rw [val_smul_group_eq_of_smul, val_smul_group_eq_of_smul, val_smul_group_eq_of_smul,
      map_mul, mul_smul]
  smul_zero g := EquivariantOfModule.ext <| by
    rw [val_smul_group_eq_of_smul, val_zero, smul_zero]
  smul_add g x y := EquivariantOfModule.ext <| by
    rw [val_smul_group_eq_of_smul, val_add, val_add, val_smul_group_eq_of_smul,
      val_smul_group_eq_of_smul, smul_add]

instance : SMulDistribClass G A (EquivariantOfModule A G N) where
  smul_distrib_smul g a x := by
    ext
    simp only [val_smul_group, val_smul_coeff, ← mul_smul]
    simp [SkewMonoidAlgebra.singleOneRingHom]

end Equivariant

end EquivariantOfModule

/-! ### `EquivariantLinearMap`, `EquivariantLinearEquiv`, and roundtrip equivalences -/

/-- An `A`-linear, `G`-equivariant map between `A`-modules carrying distributive `G`-actions. -/
structure EquivariantLinearMap (A G M M' : Type*) [Semiring A] [Monoid G]
    [AddCommMonoid M] [Module A M] [DistribMulAction G M]
    [AddCommMonoid M'] [Module A M'] [DistribMulAction G M'] extends M →ₗ[A] M' where
  /-- The map commutes with the `G`-action. -/
  map_smul_group' : ∀ (g : G) (m : M), toLinearMap (g • m) = g • toLinearMap m

namespace EquivariantLinearMap

section Basic

variable {A G M M' M'' : Type*} [Semiring A] [Monoid G]
  [AddCommMonoid M] [Module A M] [DistribMulAction G M]
  [AddCommMonoid M'] [Module A M'] [DistribMulAction G M']
  [AddCommMonoid M''] [Module A M''] [DistribMulAction G M'']

theorem toLinearMap_injective :
    Function.Injective (toLinearMap : EquivariantLinearMap A G M M' → (M →ₗ[A] M'))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance : FunLike (EquivariantLinearMap A G M M') M M' where
  coe f := f.toLinearMap
  coe_injective _ _ h := toLinearMap_injective (DFunLike.coe_injective h)

instance : LinearMapClass (EquivariantLinearMap A G M M') A M M' where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'

@[ext]
theorem ext {f g : EquivariantLinearMap A G M M'} (h : ∀ m, f m = g m) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem coe_toLinearMap (f : EquivariantLinearMap A G M M') : ⇑f.toLinearMap = f :=
  (rfl)

theorem toLinearMap_apply (f : EquivariantLinearMap A G M M') (m : M) : f.toLinearMap m = f m :=
  (rfl)

@[simp]
theorem coe_mk (f : M →ₗ[A] M') (hf) : ⇑(⟨f, hf⟩ : EquivariantLinearMap A G M M') = f :=
  (rfl)

@[simp]
theorem map_smul_group (f : EquivariantLinearMap A G M M') (g : G) (m : M) :
    f (g • m) = g • f m :=
  f.map_smul_group' g m

/-- The identity `A`-linear `G`-equivariant map on `M`. -/
def id : EquivariantLinearMap A G M M where
  toLinearMap := LinearMap.id
  map_smul_group' _ _ := rfl

@[simp]
theorem toLinearMap_id : (id : EquivariantLinearMap A G M M).toLinearMap = LinearMap.id :=
  (rfl)

@[simp]
theorem id_apply (m : M) : (id : EquivariantLinearMap A G M M) m = m :=
  (rfl)

/-- Composition of `A`-linear `G`-equivariant maps. -/
def comp (g : EquivariantLinearMap A G M' M'') (f : EquivariantLinearMap A G M M') :
    EquivariantLinearMap A G M M'' where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_smul_group' x m := by simp

@[simp]
theorem toLinearMap_comp (g : EquivariantLinearMap A G M' M'')
    (f : EquivariantLinearMap A G M M') :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  (rfl)

@[simp]
theorem comp_apply (g : EquivariantLinearMap A G M' M'')
    (f : EquivariantLinearMap A G M M') (m : M) :
    g.comp f m = g (f m) :=
  (rfl)

instance : Zero (EquivariantLinearMap A G M M') := ⟨⟨0, fun _ _ ↦ by simp⟩⟩

instance : Add (EquivariantLinearMap A G M M') :=
  ⟨fun f g ↦ ⟨f.toLinearMap + g.toLinearMap, fun _ _ ↦ by simp [smul_add]⟩⟩

@[simp] theorem zero_apply (m : M) : (0 : EquivariantLinearMap A G M M') m = 0 := (rfl)
@[simp] theorem toLinearMap_zero : (0 : EquivariantLinearMap A G M M').toLinearMap = 0 := (rfl)

@[simp]
theorem add_apply (f g : EquivariantLinearMap A G M M') (m : M) : (f + g) m = f m + g m :=
  (rfl)

@[simp]
theorem toLinearMap_add (f g : EquivariantLinearMap A G M M') :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap :=
  (rfl)

instance {R : Type*} [Semiring R] [Module R M'] [SMulCommClass A R M'] [SMulCommClass G R M'] :
    SMul R (EquivariantLinearMap A G M M') :=
  ⟨fun r f ↦ ⟨r • f.toLinearMap, fun _ _ ↦ by simp [smul_comm]⟩⟩

@[simp]
theorem smul_apply {R : Type*} [Semiring R] [Module R M'] [SMulCommClass A R M']
    [SMulCommClass G R M'] (r : R) (f : EquivariantLinearMap A G M M') (m : M) :
    (r • f) m = r • f m :=
  (rfl)

@[simp]
theorem toLinearMap_smul {R : Type*} [Semiring R] [Module R M'] [SMulCommClass A R M']
    [SMulCommClass G R M'] (r : R) (f : EquivariantLinearMap A G M M') :
    (r • f).toLinearMap = r • f.toLinearMap :=
  (rfl)

instance : AddCommMonoid (EquivariantLinearMap A G M M') where
  nsmul n f := n • f
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _
  nsmul_zero _ := ext fun _ ↦ zero_smul ℕ _
  nsmul_succ _ _ := ext fun _ ↦ succ_nsmul _ _
  add_comm _ _ := ext fun _ ↦ add_comm _ _

section Group

variable {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N]

instance : Neg (EquivariantLinearMap A G M N) :=
  ⟨fun f ↦ ⟨-f.toLinearMap, fun _ _ ↦ by simp⟩⟩

instance : Sub (EquivariantLinearMap A G M N) :=
  ⟨fun f g ↦ ⟨f.toLinearMap - g.toLinearMap, fun _ _ ↦ by simp [smul_sub]⟩⟩

@[simp]
theorem neg_apply (f : EquivariantLinearMap A G M N) (m : M) : (-f) m = -f m :=
  (rfl)

@[simp]
theorem toLinearMap_neg (f : EquivariantLinearMap A G M N) : (-f).toLinearMap = -f.toLinearMap :=
  (rfl)

@[simp]
theorem sub_apply (f g : EquivariantLinearMap A G M N) (m : M) : (f - g) m = f m - g m :=
  (rfl)

@[simp]
theorem toLinearMap_sub (f g : EquivariantLinearMap A G M N) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap :=
  (rfl)

instance : AddCommGroup (EquivariantLinearMap A G M N) where
  zsmul z f := z • f
  sub_eq_add_neg _ _ := ext fun _ ↦ sub_eq_add_neg _ _
  zsmul_zero' _ := ext fun _ ↦ zero_smul ℤ _
  zsmul_succ' _ _ := ext fun _ ↦ SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' _ _ := ext fun _ ↦ SubNegMonoid.zsmul_neg' _ _
  neg_add_cancel _ := ext fun _ ↦ neg_add_cancel _

end Group

instance {R : Type*} [Semiring R] [Module R M'] [SMulCommClass A R M'] [SMulCommClass G R M'] :
    Module R (EquivariantLinearMap A G M M') where
  one_smul _ := ext fun _ ↦ one_smul R _
  mul_smul _ _ _ := ext fun _ ↦ mul_smul _ _ _
  smul_zero _ := ext fun _ ↦ smul_zero _
  smul_add _ _ _ := ext fun _ ↦ smul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _
  zero_smul _ := ext fun _ ↦ zero_smul R _

end Basic

section AsModule

variable (A G M M' : Type*) [Semiring A] [Monoid G] [MulSemiringAction G A]
  [AddCommMonoid M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [AddCommMonoid M'] [Module A M'] [DistribMulAction G M'] [SMulDistribClass G A M']

/-- **Hom-space bijection between equivariant maps and `SkewMonoidAlgebra A G`-linear maps.**
An `A`-linear, `G`-equivariant map `M → M'` is the same data as a `SkewMonoidAlgebra A G`-linear
map `EquivariantAsModule A G M →ₗ[SkewMonoidAlgebra A G] EquivariantAsModule A G M'`. -/
def equivLinearMapAsModule :
    EquivariantLinearMap A G M M' ≃+
      (EquivariantAsModule A G M →ₗ[SkewMonoidAlgebra A G] EquivariantAsModule A G M') where
  toFun f :=
    { toFun x := .of (f x.val)
      map_add' _ _ := by ext; simp
      map_smul' r x := by
        induction r using SkewMonoidAlgebra.induction_on with
        | zero => simp
        | add p q hp hq => simp [add_smul, hp, hq]
        | single g a =>
          ext
          simp }
  invFun F :=
    { toFun m := (F (.of m)).val
      map_add' m n := by
        -- `of (m + n)` is `of m + of n`, and `F` is additive.
        change (F (.of m + .of n)).val = _
        rw [map_add]
        rfl
      map_smul' a m := by
        rw [RingHom.id_apply, ← EquivariantAsModule.singleOneRingHom_smul_of (G := G),
          F.map_smul, EquivariantAsModule.val_singleOneRingHom_smul]
      map_smul_group' g m := by
        rw [LinearMap.coe_mk, AddHom.coe_mk,
          ← EquivariantAsModule.of_smul_of (A := A) (G := G),
          F.map_smul, EquivariantAsModule.val_of_smul] }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := by ext; rfl

variable {A G M M'}

@[simp]
theorem equivLinearMapAsModule_apply (f : EquivariantLinearMap A G M M')
    (x : EquivariantAsModule A G M) :
    equivLinearMapAsModule A G M M' f x = .of (f x.val) :=
  (rfl)

theorem val_equivLinearMapAsModule_apply (f : EquivariantLinearMap A G M M')
    (x : EquivariantAsModule A G M) :
    (equivLinearMapAsModule A G M M' f x).val = f x.val :=
  (rfl)

theorem equivLinearMapAsModule_apply_of (f : EquivariantLinearMap A G M M') (m : M) :
    equivLinearMapAsModule A G M M' f (.of m) = .of (f m) :=
  (rfl)

@[simp]
theorem equivLinearMapAsModule_symm_apply
    (F : EquivariantAsModule A G M →ₗ[SkewMonoidAlgebra A G] EquivariantAsModule A G M') (m : M) :
    (equivLinearMapAsModule A G M M').symm F m = (F (.of m)).val :=
  (rfl)

@[simp]
theorem equivLinearMapAsModule_id :
    equivLinearMapAsModule A G M M .id = LinearMap.id := by
  ext x
  simp

@[simp]
theorem equivLinearMapAsModule_comp {M'' : Type*} [AddCommMonoid M''] [Module A M'']
    [DistribMulAction G M''] [SMulDistribClass G A M'']
    (g : EquivariantLinearMap A G M' M'') (f : EquivariantLinearMap A G M M') :
    equivLinearMapAsModule A G M M'' (g.comp f) =
      (equivLinearMapAsModule A G M' M'' g).comp (equivLinearMapAsModule A G M M' f) := by
  ext x
  simp

end AsModule

section OfModule

variable (A G N N' : Type*) [Semiring A] [Monoid G] [MulSemiringAction G A]
  [AddCommMonoid N] [Module (SkewMonoidAlgebra A G) N]
  [AddCommMonoid N'] [Module (SkewMonoidAlgebra A G) N']

/-- **Hom-space bijection on `EquivariantOfModule`.** A `SkewMonoidAlgebra A G`-linear map
`N →ₗ[SkewMonoidAlgebra A G] N'` is the same data as an `A`-linear, `G`-equivariant map between
`EquivariantOfModule A G N` and `EquivariantOfModule A G N'`. -/
def equivLinearMapOfModule :
    (N →ₗ[SkewMonoidAlgebra A G] N') ≃+
      EquivariantLinearMap A G (EquivariantOfModule A G N) (EquivariantOfModule A G N') where
  toFun F :=
    { toFun x := .of (F x.val)
      map_add' x y := EquivariantOfModule.ext (F.map_add x.val y.val)
      map_smul' a x := EquivariantOfModule.ext
        (F.map_smul (SkewMonoidAlgebra.singleOneRingHom (G := G) a) x.val)
      map_smul_group' g x := EquivariantOfModule.ext
        (F.map_smul (SkewMonoidAlgebra.of A G g) x.val) }
  invFun f :=
    { toFun n := (f (.of n)).val
      map_add' m n := by
        -- `of (m + n)` is `of m + of n`, and `f` is additive.
        change (f (.of m + .of n)).val = _
        rw [map_add]
        rfl
      map_smul' r n := by
        rw [RingHom.id_apply]
        induction r using SkewMonoidAlgebra.induction_on with
        | zero => simp
        | add p q hp hq =>
          rw [add_smul, EquivariantOfModule.of_add, map_add, EquivariantOfModule.val_add, hp, hq,
            add_smul]
        | single g a =>
          have hga : SkewMonoidAlgebra.single g a =
              SkewMonoidAlgebra.singleOneRingHom (G := G) a * SkewMonoidAlgebra.of A G g := by
            simp [SkewMonoidAlgebra.singleOneRingHom]
          rw [hga, mul_smul, mul_smul, ← EquivariantOfModule.smul_coeff_of (G := G),
            map_smul f, EquivariantOfModule.val_smul_coeff]
          exact congrArg (SkewMonoidAlgebra.singleOneRingHom (G := G) a • ·) <| by
            rw [SkewMonoidAlgebra.of_apply, ← EquivariantOfModule.smul_group_of (A := A),
              f.map_smul_group, EquivariantOfModule.val_smul_group] }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := by ext; rfl

variable {A G N N'}

@[simp]
theorem equivLinearMapOfModule_apply (F : N →ₗ[SkewMonoidAlgebra A G] N')
    (x : EquivariantOfModule A G N) :
    equivLinearMapOfModule A G N N' F x = .of (F x.val) :=
  (rfl)

@[simp]
theorem equivLinearMapOfModule_symm_apply
    (f : EquivariantLinearMap A G (EquivariantOfModule A G N) (EquivariantOfModule A G N'))
    (n : N) :
    (equivLinearMapOfModule A G N N').symm f n = (f (.of n)).val :=
  (rfl)

@[simp]
theorem equivLinearMapOfModule_id :
    equivLinearMapOfModule A G N N LinearMap.id = .id := by
  ext x
  simp

@[simp]
theorem equivLinearMapOfModule_comp {N'' : Type*} [AddCommMonoid N'']
    [Module (SkewMonoidAlgebra A G) N'']
    (G' : N' →ₗ[SkewMonoidAlgebra A G] N'') (F : N →ₗ[SkewMonoidAlgebra A G] N') :
    equivLinearMapOfModule A G N N'' (G'.comp F) =
      (equivLinearMapOfModule A G N' N'' G').comp (equivLinearMapOfModule A G N N' F) := by
  ext x
  simp

end OfModule

end EquivariantLinearMap

/-- An `A`-linear, `G`-equivariant equivalence between `A`-modules carrying distributive
`G`-actions. -/
structure EquivariantLinearEquiv (A G M M' : Type*) [Semiring A] [Monoid G]
    [AddCommMonoid M] [Module A M] [DistribMulAction G M]
    [AddCommMonoid M'] [Module A M'] [DistribMulAction G M'] extends M ≃ₗ[A] M' where
  /-- The equivalence commutes with the `G`-action. -/
  map_smul_group' : ∀ (g : G) (m : M), toLinearEquiv (g • m) = g • toLinearEquiv m

namespace EquivariantLinearEquiv

variable {A G M M' M'' : Type*} [Semiring A] [Monoid G]
  [AddCommMonoid M] [Module A M] [DistribMulAction G M]
  [AddCommMonoid M'] [Module A M'] [DistribMulAction G M']
  [AddCommMonoid M''] [Module A M''] [DistribMulAction G M'']

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : EquivariantLinearEquiv A G M M' → (M ≃ₗ[A] M'))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance : EquivLike (EquivariantLinearEquiv A G M M') M M' where
  coe e := e.toLinearEquiv
  inv e := e.toLinearEquiv.symm
  left_inv e := e.toLinearEquiv.left_inv
  right_inv e := e.toLinearEquiv.right_inv
  coe_injective' _ _ h _ := toLinearEquiv_injective (DFunLike.coe_injective h)

instance : LinearEquivClass (EquivariantLinearEquiv A G M M') A M M' where
  map_add e := e.map_add'
  map_smulₛₗ e := e.map_smul'

@[ext]
theorem ext {e₁ e₂ : EquivariantLinearEquiv A G M M'} (h : ∀ m, e₁ m = e₂ m) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ h

@[simp]
theorem coe_toLinearEquiv (e : EquivariantLinearEquiv A G M M') : ⇑e.toLinearEquiv = e :=
  (rfl)

@[simp]
theorem coe_mk (e : M ≃ₗ[A] M') (he) : ⇑(⟨e, he⟩ : EquivariantLinearEquiv A G M M') = e :=
  (rfl)

/-- Forget the inverse of an `EquivariantLinearEquiv` to obtain an `EquivariantLinearMap`. -/
def toEquivariantLinearMap (e : EquivariantLinearEquiv A G M M') :
    EquivariantLinearMap A G M M' where
  toLinearMap := e.toLinearEquiv.toLinearMap
  map_smul_group' := e.map_smul_group'

@[simp]
theorem coe_toEquivariantLinearMap (e : EquivariantLinearEquiv A G M M') :
    ⇑e.toEquivariantLinearMap = e :=
  (rfl)

theorem toEquivariantLinearMap_apply (e : EquivariantLinearEquiv A G M M') (m : M) :
    e.toEquivariantLinearMap m = e m :=
  (rfl)

@[simp]
theorem toLinearMap_toEquivariantLinearMap (e : EquivariantLinearEquiv A G M M') :
    e.toEquivariantLinearMap.toLinearMap = e.toLinearEquiv.toLinearMap :=
  (rfl)

@[simp]
theorem map_smul_group (e : EquivariantLinearEquiv A G M M') (g : G) (m : M) :
    e (g • m) = g • e m :=
  e.map_smul_group' g m

/-- The identity `A`-linear `G`-equivariant equivalence on `M`. -/
def refl : EquivariantLinearEquiv A G M M where
  toLinearEquiv := LinearEquiv.refl A M
  map_smul_group' _ _ := rfl

@[simp] theorem refl_apply (m : M) : (refl : EquivariantLinearEquiv A G M M) m = m := (rfl)

/-- Inverse of an `A`-linear `G`-equivariant equivalence. -/
def symm (e : EquivariantLinearEquiv A G M M') : EquivariantLinearEquiv A G M' M where
  toLinearEquiv := e.toLinearEquiv.symm
  map_smul_group' g m' := by
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.apply_symm_apply, coe_toLinearEquiv, map_smul_group]
    exact congrArg (g • ·) (e.toLinearEquiv.apply_symm_apply m').symm

@[simp]
theorem symm_apply_apply (e : EquivariantLinearEquiv A G M M') (m : M) : e.symm (e m) = m :=
  e.toLinearEquiv.symm_apply_apply m

@[simp]
theorem apply_symm_apply (e : EquivariantLinearEquiv A G M M') (m' : M') : e (e.symm m') = m' :=
  e.toLinearEquiv.apply_symm_apply m'

/-- Transitivity of `A`-linear `G`-equivariant equivalences. -/
def trans (e₁ : EquivariantLinearEquiv A G M M') (e₂ : EquivariantLinearEquiv A G M' M'') :
    EquivariantLinearEquiv A G M M'' where
  toLinearEquiv := e₁.toLinearEquiv.trans e₂.toLinearEquiv
  map_smul_group' g m := by simp

@[simp]
theorem trans_apply (e₁ : EquivariantLinearEquiv A G M M')
    (e₂ : EquivariantLinearEquiv A G M' M'') (m : M) :
    e₁.trans e₂ m = e₂ (e₁ m) :=
  (rfl)

/-- Convert an `EquivariantLinearEquiv` into a `SkewMonoidAlgebra A G`-linear equivalence between
the attached `EquivariantAsModule`s. -/
def toAsModuleLinearEquiv [MulSemiringAction G A] [SMulDistribClass G A M]
    [SMulDistribClass G A M'] (e : EquivariantLinearEquiv A G M M') :
    EquivariantAsModule A G M ≃ₗ[SkewMonoidAlgebra A G] EquivariantAsModule A G M' :=
  LinearEquiv.ofLinearMap
    (EquivariantLinearMap.equivLinearMapAsModule A G M M' e.toEquivariantLinearMap)
    (EquivariantLinearMap.equivLinearMapAsModule A G M' M e.symm.toEquivariantLinearMap)
    (by ext m'; simp)
    (by ext m; simp)

@[simp]
theorem toAsModuleLinearEquiv_of [MulSemiringAction G A] [SMulDistribClass G A M]
    [SMulDistribClass G A M'] (e : EquivariantLinearEquiv A G M M') (m : M) :
    e.toAsModuleLinearEquiv (.of m) = .of (e m) :=
  (rfl)

@[simp]
theorem toAsModuleLinearEquiv_symm_of [MulSemiringAction G A] [SMulDistribClass G A M]
    [SMulDistribClass G A M'] (e : EquivariantLinearEquiv A G M M') (m' : M') :
    e.toAsModuleLinearEquiv.symm (.of m') = .of (e.symm m') :=
  (rfl)

/-- Convert a `SkewMonoidAlgebra A G`-linear equivalence between `EquivariantAsModule`s back into
an `EquivariantLinearEquiv`. -/
def ofAsModuleLinearEquiv [MulSemiringAction G A] [SMulDistribClass G A M]
    [SMulDistribClass G A M']
    (E : EquivariantAsModule A G M ≃ₗ[SkewMonoidAlgebra A G] EquivariantAsModule A G M') :
    EquivariantLinearEquiv A G M M' :=
  let f := (EquivariantLinearMap.equivLinearMapAsModule A G M M').symm E.toLinearMap
  let g := (EquivariantLinearMap.equivLinearMapAsModule A G M' M).symm E.symm.toLinearMap
  { toLinearEquiv := LinearEquiv.ofLinearMap f.toLinearMap g.toLinearMap
      (by
        ext m'
        simp [f, g])
      (by
        ext m
        simp [f, g])
    map_smul_group' := f.map_smul_group }

@[simp]
theorem ofAsModuleLinearEquiv_apply [MulSemiringAction G A] [SMulDistribClass G A M]
    [SMulDistribClass G A M']
    (E : EquivariantAsModule A G M ≃ₗ[SkewMonoidAlgebra A G] EquivariantAsModule A G M') (m : M) :
    ofAsModuleLinearEquiv E m = (E (.of m)).val :=
  (rfl)

@[simp]
theorem ofAsModuleLinearEquiv_symm_apply [MulSemiringAction G A] [SMulDistribClass G A M]
    [SMulDistribClass G A M']
    (E : EquivariantAsModule A G M ≃ₗ[SkewMonoidAlgebra A G] EquivariantAsModule A G M')
    (m' : M') :
    (ofAsModuleLinearEquiv E).symm m' = (E.symm (.of m')).val :=
  (rfl)

end EquivariantLinearEquiv

section Roundtrip

variable (A G : Type*) [Semiring A] [Monoid G] [MulSemiringAction G A]

/-- **Module roundtrip:** viewing a left `SkewMonoidAlgebra A G`-module `N` as an equivariant
`(A, G)`-module and converting back recovers `N` as a `SkewMonoidAlgebra A G`-module. -/
def equivariantAsOfModuleLinearEquiv (N : Type*) [AddCommMonoid N]
    [Module (SkewMonoidAlgebra A G) N] :
    EquivariantAsModule A G (EquivariantOfModule A G N) ≃ₗ[SkewMonoidAlgebra A G] N where
  toFun x := x.val.val
  invFun n := .of (.of n)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    rw [RingHom.id_apply]
    induction r using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | add p q hp hq =>
      simp only [add_smul, EquivariantAsModule.val_add, EquivariantOfModule.val_add]
      rw [hp, hq]
    | single g a =>
      simp only [EquivariantAsModule.val_single_smul, EquivariantOfModule.val_smul_coeff,
        EquivariantOfModule.val_smul_group, ← mul_smul]
      exact congrArg (· • x.val.val) (by simp [SkewMonoidAlgebra.singleOneRingHom])

@[simp]
theorem equivariantAsOfModuleLinearEquiv_apply {N : Type*} [AddCommMonoid N]
    [Module (SkewMonoidAlgebra A G) N]
    (x : EquivariantAsModule A G (EquivariantOfModule A G N)) :
    equivariantAsOfModuleLinearEquiv A G N x = x.val.val :=
  (rfl)

@[simp]
theorem equivariantAsOfModuleLinearEquiv_symm_apply {N : Type*} [AddCommMonoid N]
    [Module (SkewMonoidAlgebra A G) N] (n : N) :
    (equivariantAsOfModuleLinearEquiv A G N).symm n = .of (.of n) :=
  (rfl)

/-- **Equivariant roundtrip:** converting an equivariant `(A, G)`-module `M` to a left
`SkewMonoidAlgebra A G`-module and reading off its underlying equivariant structure recovers `M` up
to `EquivariantLinearEquiv`. -/
def equivariantOfAsModuleEquiv (M : Type*) [AddCommMonoid M] [Module A M] [DistribMulAction G M]
    [SMulDistribClass G A M] :
    EquivariantLinearEquiv A G M (EquivariantOfModule A G (EquivariantAsModule A G M)) where
  toFun m := .of (.of m)
  invFun x := x.val.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a m := by
    ext
    simp
  map_smul_group' g m := by
    ext
    simp

@[simp]
theorem equivariantOfAsModuleEquiv_apply {M : Type*} [AddCommMonoid M] [Module A M]
    [DistribMulAction G M] [SMulDistribClass G A M] (m : M) :
    equivariantOfAsModuleEquiv A G M m = .of (.of m) :=
  (rfl)

@[simp]
theorem equivariantOfAsModuleEquiv_symm_apply {M : Type*} [AddCommMonoid M] [Module A M]
    [DistribMulAction G M] [SMulDistribClass G A M]
    (x : EquivariantOfModule A G (EquivariantAsModule A G M)) :
    (equivariantOfAsModuleEquiv A G M).symm x = x.val.val :=
  (rfl)

end Roundtrip

end TauCeti
