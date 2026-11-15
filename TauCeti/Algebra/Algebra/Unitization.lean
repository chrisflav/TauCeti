/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization

/-!
# Functoriality and one-sided ideal actions of the forced unitization

A homomorphism of nonunital algebras `f : A →ₙₐ[R] B` induces a unital algebra homomorphism
`Unitization R A →ₐ[R] Unitization R B`, sending `(r, a)` to `(r, f a)`. This is the non-star
counterpart of Mathlib's `Unitization.starMap`, and it is functorial.

Furthermore, the embedded copy `Unitization.inr '' Set.univ` is a two-sided ideal of
`Unitization R A`: multiplying `u : Unitization R A` on the right by `b : A` gives
`(0, u.fst • b + u.snd * b)`, and multiplying `b : A` on the right by `u` gives
`(0, u.fst • b + b * u.snd)`. Consequently, every `R`-submodule `L : Submodule R A` closed under
ambient left multiplication (`∀ a : A, ∀ x ∈ L, a * x ∈ L`) absorbs
`(u * (b : Unitization R A)).snd` for `b ∈ L` and carries a canonical unital `R`-algebra action
`L.unitizationLeftAction hL : Unitization R A →ₐ[R] Module.End R L`, with right-ideal dual
`M.unitizationRightAction hM : Unitization R A →ₐ[R] (Module.End R M)ᵐᵒᵖ`.

## Main declarations

* `Unitization.map`: the unital algebra homomorphism induced on forced unitizations.
* `Unitization.map_id`, `Unitization.map_comp`: functoriality.
* `Unitization.fstHom_comp_map`: the induced map preserves the augmentation.
* `Unitization.map_surjective`: the induced map of a surjective homomorphism is surjective.
* `Unitization.fst_mul_inr`, `Unitization.snd_mul_inr`, `Unitization.inr_snd_mul_inr` and their
  right-multiplication duals `Unitization.fst_inr_mul`, `Unitization.snd_inr_mul`,
  `Unitization.inr_snd_inr_mul`: coordinate formulas for products of `Unitization R A` with `A`.
* `Submodule.snd_mul_inr_mem` and `Submodule.snd_inr_mul_mem`: algebraic absorption of
  `Unitization R A` multiples in one-sided `R`-ideals.
* `Submodule.leftIdealLmul`, `Submodule.unitizationLeftAction`, `Submodule.unitizationLeftModule`,
  `Submodule.rightIdealRmul`, and `Submodule.unitizationRightAction`: canonical actions of `A` and
  `Unitization R A` on left and right `R`-ideals.
-/

public section

namespace Unitization

section Map

variable {R A B C : Type*} [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

/-- The unital algebra homomorphism between forced unitizations induced by a homomorphism of
nonunital algebras. -/
def map (f : A →ₙₐ[R] B) : Unitization R A →ₐ[R] Unitization R B :=
  lift ((inrNonUnitalAlgHom R B).comp f)

/-- The induced map of unitizations restricts to the original nonunital algebra homomorphism. -/
@[simp]
theorem map_inr (f : A →ₙₐ[R] B) (a : A) : map f (inr a) = inr (f a) := by simp [map]

/-- The induced map of unitizations is the identity on scalars. -/
@[simp]
theorem map_inl (f : A →ₙₐ[R] B) (r : R) :
    map f (inl r : Unitization R A) = algebraMap R (Unitization R B) r := by simp [map]

/-- The scalar component of the induced map of unitizations is unchanged. -/
@[simp]
theorem fst_map (f : A →ₙₐ[R] B) (x : Unitization R A) : (map f x).fst = x.fst := by
  simp [map, algebraMap_eq_inl]

/-- The nonunital-algebra component of the induced map of unitizations is obtained by applying the
original homomorphism. -/
@[simp]
theorem snd_map (f : A →ₙₐ[R] B) (x : Unitization R A) : (map f x).snd = f x.snd := by
  simp [map, algebraMap_eq_inl]

/-- The induced map of forced unitizations preserves the augmentation `(r, a) ↦ r`. -/
@[simp]
theorem fstHom_comp_map (f : A →ₙₐ[R] B) : (fstHom R B).comp (map f) = fstHom R A :=
  AlgHom.ext fun x ↦ by simp

/-- A surjective homomorphism of nonunital algebras induces a surjective homomorphism of forced
unitizations: `(r, b)` is the image of `(r, a)` for any preimage `a` of `b`. -/
theorem map_surjective {f : A →ₙₐ[R] B} (hf : Function.Surjective f) :
    Function.Surjective (map f) := fun y ↦ by
  obtain ⟨a, ha⟩ := hf y.snd
  exact ⟨inl y.fst + inr a,
    Unitization.ext (by rw [fst_map]; simp) (by rw [snd_map]; simp [ha])⟩

/-- The identity homomorphism induces the identity homomorphism of forced unitizations. -/
@[simp]
theorem map_id : map (NonUnitalAlgHom.id R A) = AlgHom.id R (Unitization R A) :=
  algHom_ext'' fun _ ↦ by simp

/-- Unitization preserves composition of nonunital algebra homomorphisms. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) : map (g.comp f) = (map g).comp (map f) :=
  algHom_ext'' fun _ ↦ by simp

end Map

section MulInr

variable {R A : Type*} [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A]

/-- Multiplying an element of `Unitization R A` on the right by an element of `A` has zero scalar
part. -/
theorem fst_mul_inr (u : Unitization R A) (b : A) :
    (u * (b : Unitization R A)).fst = 0 :=
  mul_zero u.fst

/-- Multiplying an element of `Unitization R A` on the right by `b : A` acts on the `A`-coordinate
by `u.fst • b + u.snd * b`. -/
theorem snd_mul_inr (u : Unitization R A) (b : A) :
    (u * (b : Unitization R A)).snd = u.fst • b + u.snd * b := by
  simp [snd_mul]

/-- The product `u * (b : Unitization R A)` lies in the image of `Unitization.inr`. -/
theorem inr_snd_mul_inr (u : Unitization R A) (b : A) :
    (((u * (b : Unitization R A)).snd : A) : Unitization R A) = u * (b : Unitization R A) :=
  Unitization.ext (fst_mul_inr u b).symm rfl

/-- Multiplying `b : A` on the right by an element of `Unitization R A` has zero scalar part. -/
theorem fst_inr_mul (b : A) (u : Unitization R A) :
    ((b : Unitization R A) * u).fst = 0 :=
  zero_mul u.fst

/-- Multiplying `b : A` on the right by `u : Unitization R A` acts on the `A`-coordinate by
`u.fst • b + b * u.snd`. -/
theorem snd_inr_mul (b : A) (u : Unitization R A) :
    ((b : Unitization R A) * u).snd = u.fst • b + b * u.snd := by
  simp [snd_mul]

/-- The product `(b : Unitization R A) * u` lies in the image of `Unitization.inr`. -/
theorem inr_snd_inr_mul (b : A) (u : Unitization R A) :
    ((((b : Unitization R A) * u).snd : A) : Unitization R A) = (b : Unitization R A) * u :=
  Unitization.ext (fst_inr_mul b u).symm rfl

end MulInr

end Unitization

namespace Submodule

section Absorption

variable {R A : Type*} [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]

/-- If `L : Submodule R A` absorbs ambient left multiples and `b ∈ L`, then for every
`u : Unitization R A` the `A`-coordinate of `u * (b : Unitization R A)` belongs to `L`. -/
theorem snd_mul_inr_mem (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (u : Unitization R A) {b : A} (hb : b ∈ L) :
    (u * (b : Unitization R A)).snd ∈ L := by
  rw [Unitization.snd_mul_inr]
  exact L.add_mem (L.smul_mem u.fst hb) (hL u.snd b hb)

/-- If `M : Submodule R A` absorbs ambient right multiples and `b ∈ M`, then for every
`u : Unitization R A` the `A`-coordinate of `(b : Unitization R A) * u` belongs to `M`. -/
theorem snd_inr_mul_mem (M : Submodule R A) (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M)
    {b : A} (hb : b ∈ M) (u : Unitization R A) :
    ((b : Unitization R A) * u).snd ∈ M := by
  rw [Unitization.snd_inr_mul]
  exact M.add_mem (M.smul_mem u.fst hb) (hM u.snd b hb)

end Absorption

section IdealActions

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Left multiplication of `A` on an `R`-submodule `L` that absorbs ambient left multiples,
bundled as a nonunital `R`-algebra homomorphism into `Module.End R L`. -/
def leftIdealLmul (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    A →ₙₐ[R] Module.End R L where
  toFun a :=
    { toFun := fun x => ⟨a * x, hL a x x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add a x y)
      map_smul' := fun r x => Subtype.ext (mul_smul_comm r a x) }
  map_smul' r a := LinearMap.ext fun x => Subtype.ext (smul_mul_assoc r a x)
  map_zero' := LinearMap.ext fun x => Subtype.ext (zero_mul (x : A))
  map_add' a b := LinearMap.ext fun x => Subtype.ext (add_mul a b x)
  map_mul' a b := LinearMap.ext fun x => Subtype.ext (mul_assoc a b x)

/-- Coercing `L.leftIdealLmul hL a x` to `A` gives `a * x`. -/
@[simp]
theorem coe_leftIdealLmul_apply (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (a : A) (x : L) :
    ((L.leftIdealLmul hL a x : L) : A) = a * x :=
  (rfl)

/-- The canonical unital `R`-algebra homomorphism from `Unitization R A` into the `R`-linear
endomorphisms of a left `R`-ideal `L`, sending `(r, a)` to `x ↦ r • x + a * x`. -/
def unitizationLeftAction (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    Unitization R A →ₐ[R] Module.End R L :=
  Unitization.lift (L.leftIdealLmul hL)

/-- On an element `a : A`, `L.unitizationLeftAction hL` restricts to `L.leftIdealLmul hL a`. -/
@[simp]
theorem unitizationLeftAction_inr (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) (a : A) :
    L.unitizationLeftAction hL (a : Unitization R A) = L.leftIdealLmul hL a := by
  simp [unitizationLeftAction]

/-- On scalars `r : R`, `L.unitizationLeftAction hL` acts as `algebraMap R (Module.End R L) r`. -/
@[simp]
theorem unitizationLeftAction_inl (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) (r : R) :
    L.unitizationLeftAction hL (Unitization.inl r) = algebraMap R (Module.End R L) r := by
  simp [unitizationLeftAction]

/-- Coercing `L.unitizationLeftAction hL u x` to `A` gives `u.fst • x + u.snd * x`. -/
@[simp]
theorem coe_unitizationLeftAction_apply (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L)
    (u : Unitization R A) (x : L) :
    ((L.unitizationLeftAction hL u x : L) : A) = u.fst • (x : A) + u.snd * (x : A) :=
  (rfl)

/-- The action of `u : Unitization R A` on `x : L` agrees in `A` with the `A`-coordinate of the
product `u * (x : Unitization R A)`. -/
theorem coe_unitizationLeftAction_eq_snd_mul (L : Submodule R A)
    (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) (u : Unitization R A) (x : L) :
    ((L.unitizationLeftAction hL u x : L) : A) = (u * ((x : A) : Unitization R A)).snd := by
  rw [Unitization.snd_mul_inr, coe_unitizationLeftAction_apply]

/-- The `Unitization R A`-module structure on a left `R`-ideal `L` induced by
`L.unitizationLeftAction hL`. Provided as an explicit definition rather than a global instance
because it depends on the left-ideal hypothesis `hL`. -/
@[instance_reducible]
def unitizationLeftModule (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    Module (Unitization R A) L :=
  Module.compHom L (L.unitizationLeftAction hL).toRingHom

/-- Right multiplication of `A` on an `R`-submodule `M` that absorbs ambient right multiples,
bundled as a nonunital `R`-algebra homomorphism into `(Module.End R M)ᵐᵒᵖ`. -/
def rightIdealRmul (M : Submodule R A) (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M) :
    A →ₙₐ[R] (Module.End R M)ᵐᵒᵖ where
  toFun a := MulOpposite.op
    { toFun := fun x => ⟨x * a, hM a x x.2⟩
      map_add' := fun x y => Subtype.ext (add_mul (x : A) y a)
      map_smul' := fun r x => Subtype.ext (smul_mul_assoc r (x : A) a) }
  map_smul' r a := MulOpposite.unop_injective <| LinearMap.ext fun x =>
    Subtype.ext (mul_smul_comm r (x : A) a)
  map_zero' := MulOpposite.unop_injective <| LinearMap.ext fun x => Subtype.ext (mul_zero (x : A))
  map_add' a b := MulOpposite.unop_injective <| LinearMap.ext fun x =>
    Subtype.ext (mul_add (x : A) a b)
  map_mul' a b := MulOpposite.unop_injective <| LinearMap.ext fun x =>
    Subtype.ext (mul_assoc (x : A) a b).symm

/-- Coercing `(M.rightIdealRmul hM a).unop x` to `A` gives `x * a`. -/
@[simp]
theorem coe_unop_rightIdealRmul_apply (M : Submodule R A) (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M)
    (a : A) (x : M) :
    (((M.rightIdealRmul hM a).unop x : M) : A) = x * a :=
  (rfl)

/-- The canonical unital `R`-algebra homomorphism from `Unitization R A` into
`(Module.End R M)ᵐᵒᵖ` for a right `R`-ideal `M`, sending `(r, a)` to `x ↦ r • x + x * a`. -/
def unitizationRightAction (M : Submodule R A) (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M) :
    Unitization R A →ₐ[R] (Module.End R M)ᵐᵒᵖ :=
  Unitization.lift (M.rightIdealRmul hM)

/-- On an element `a : A`, `M.unitizationRightAction hM` restricts to `M.rightIdealRmul hM a`. -/
@[simp]
theorem unitizationRightAction_inr (M : Submodule R A) (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M)
    (a : A) :
    M.unitizationRightAction hM (a : Unitization R A) = M.rightIdealRmul hM a := by
  simp [unitizationRightAction]

/-- On scalars `r : R`, `M.unitizationRightAction hM` acts as
`algebraMap R (Module.End R M)ᵐᵒᵖ r`. -/
@[simp]
theorem unitizationRightAction_inl (M : Submodule R A) (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M)
    (r : R) :
    M.unitizationRightAction hM (Unitization.inl r) = algebraMap R (Module.End R M)ᵐᵒᵖ r := by
  simp [unitizationRightAction]

/-- Coercing `(M.unitizationRightAction hM u).unop x` to `A` gives `u.fst • x + x * u.snd`. -/
@[simp]
theorem coe_unop_unitizationRightAction_apply (M : Submodule R A)
    (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M) (u : Unitization R A) (x : M) :
    (((M.unitizationRightAction hM u).unop x : M) : A) = u.fst • (x : A) + (x : A) * u.snd := by
  simp [unitizationRightAction, rightIdealRmul, Algebra.algebraMap_eq_smul_one]

/-- The action of `u : Unitization R A` on `x : M` agrees in `A` with the `A`-coordinate of the
product `(x : Unitization R A) * u`. -/
theorem coe_unop_unitizationRightAction_eq_snd_mul (M : Submodule R A)
    (hM : ∀ a : A, ∀ x ∈ M, x * a ∈ M) (u : Unitization R A) (x : M) :
    (((M.unitizationRightAction hM u).unop x : M) : A) = (((x : A) : Unitization R A) * u).snd := by
  rw [Unitization.snd_inr_mul, coe_unop_unitizationRightAction_apply]

end IdealActions

end Submodule
