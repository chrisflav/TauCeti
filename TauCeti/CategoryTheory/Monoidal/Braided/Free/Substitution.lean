/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.Free.Basic
public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Substitution

/-!
# Braided substitution of tensor expressions for coupons

A `TensorSignature.BraidedSubstitution S T` replaces each generating object of `S` by a formal
tensor expression in `T.FreeBraided` (including the unit or a multi-letter word) and each coupon
of `S` by a raw braided morphism expression in `T` between the resulting substituted boundaries.

`FreeBraided.Hom.subst` performs this replacement on raw braided terms before quotienting by the
braided-monoidal axioms, and `FreeBraided.HomEquiv.subst` proves that it preserves those axioms
(including naturality of the braiding, inverse laws and both hexagons). The strong braided functor
`BraidedSubstitution.toFunctor` is the universal lift `FreeBraided.lift`, and
`BraidedSubstitution.toFunctor_map_homMk` identifies its action with raw braided substitution.

When a substitution replaces every object generator by a word of constant port length `k` (cabling
each strand into `k` parallel strands) and every coupon by a crossing-free expression, each single
crossing becomes a `k`-by-`k` cable crossing, scaling the integer crossing-exponent sum by `k * k`
(`FreeBraided.Hom.crossingExp_subst`, `BraidedSubstitution.crossingExp_toFunctor_map`).

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §§1, 3.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature

/-- A typed braided substitution between tensor signatures. Object generators of `S` are replaced
by formal tensor expressions in `T.FreeBraided`, and coupons of `S` by raw braided morphism
expressions in `T` between the substituted source and target words. The object and coupon types of
the two signatures need not share universes. -/
@[ext]
structure BraidedSubstitution (S : TensorSignature.{u, v}) (T : TensorSignature.{u', v'}) where
  /-- The formal tensor expression in `T.FreeBraided` replacing each object generator of `S`. -/
  obj : S.Obj → T.FreeBraided
  /-- The raw braided morphism expression replacing each coupon of `S`. -/
  coupon : ∀ g : S.Coupon, FreeBraided.Hom
    (projectObj obj (S.src g)).as (projectObj obj (S.tgt g)).as

variable {S : TensorSignature.{u, v}} {T : TensorSignature.{u', v'}}

namespace FreeBraided

/-- Substitute formal tensor expressions for object generators and raw braided expressions for
coupons, transporting structural associators, unitors and braidings along `projectObj`. -/
def Hom.subst (σ : BraidedSubstitution S T) : ∀ {X Y}, Hom X Y →
    Hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .id X => .id (projectObj σ.obj X).as
  | _, _, .α_hom X Y Z => .α_hom (projectObj σ.obj X).as
      (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .α_inv X Y Z => .α_inv (projectObj σ.obj X).as
      (projectObj σ.obj Y).as (projectObj σ.obj Z).as
  | _, _, .l_hom X => .l_hom (projectObj σ.obj X).as
  | _, _, .l_inv X => .l_inv (projectObj σ.obj X).as
  | _, _, .ρ_hom X => .ρ_hom (projectObj σ.obj X).as
  | _, _, .ρ_inv X => .ρ_inv (projectObj σ.obj X).as
  | _, _, .β_hom X Y => .β_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .β_inv X Y => .β_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as
  | _, _, .coupon g => σ.coupon g
  | _, _, .comp f g => (f.subst σ).comp (g.subst σ)
  | _, _, .whiskerLeft X f => (f.subst σ).whiskerLeft (projectObj σ.obj X).as
  | _, _, .whiskerRight f X => (f.subst σ).whiskerRight (projectObj σ.obj X).as
  | _, _, .tensor f g => (f.subst σ).tensor (g.subst σ)

@[simp]
theorem Hom.subst_id (σ : BraidedSubstitution S T) (X) :
    (Hom.id X).subst σ = .id (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_coupon (σ : BraidedSubstitution S T) (g : S.Coupon) :
    (Hom.coupon g).subst σ = σ.coupon g := by rfl

@[simp]
theorem Hom.subst_comp (σ : BraidedSubstitution S T) {X Y Z} (f : Hom X Y) (g : Hom Y Z) :
    (f.comp g).subst σ = (f.subst σ).comp (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_tensor (σ : BraidedSubstitution S T) {W X Y Z} (f : Hom W X) (g : Hom Y Z) :
    (f.tensor g).subst σ = (f.subst σ).tensor (g.subst σ) := by rfl

@[simp]
theorem Hom.subst_whiskerLeft (σ : BraidedSubstitution S T) (X) {Y Z} (f : Hom Y Z) :
    (f.whiskerLeft X).subst σ = (f.subst σ).whiskerLeft (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_whiskerRight (σ : BraidedSubstitution S T) {Y Z} (f : Hom Y Z) (X) :
    (f.whiskerRight X).subst σ = (f.subst σ).whiskerRight (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_α_hom (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_hom X Y Z).subst σ =
      .α_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_α_inv (σ : BraidedSubstitution S T) (X Y Z) :
    (Hom.α_inv X Y Z).subst σ =
      .α_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as (projectObj σ.obj Z).as := by rfl

@[simp]
theorem Hom.subst_l_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.l_hom X).subst σ = .l_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_l_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.l_inv X).subst σ = .l_inv (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_hom (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_hom X).subst σ = .ρ_hom (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_ρ_inv (σ : BraidedSubstitution S T) (X) :
    (Hom.ρ_inv X).subst σ = .ρ_inv (projectObj σ.obj X).as := by rfl

@[simp]
theorem Hom.subst_β_hom (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_hom X Y).subst σ = .β_hom (projectObj σ.obj X).as (projectObj σ.obj Y).as := by rfl

@[simp]
theorem Hom.subst_β_inv (σ : BraidedSubstitution S T) (X Y) :
    (Hom.β_inv X Y).subst σ = .β_inv (projectObj σ.obj X).as (projectObj σ.obj Y).as := by rfl

/-- Replacing every object generator by a formal tensor word of constant length `k` and every
coupon by a raw braided expression of crossing-exponent sum `0` scales the crossing-exponent sum of
every raw braided morphism by `k * k`. -/
theorem Hom.crossingExp_subst (σ : BraidedSubstitution S T) {k : ℕ}
    (hobj : ∀ a : S.Obj, (σ.obj a).as.length = k)
    (hc : ∀ g : S.Coupon, (σ.coupon g).crossingExp = 0)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    (f.subst σ).crossingExp = (k : ℤ) * (k : ℤ) * f.crossingExp := by
  have hlen_proj : ∀ W : FreeMonoidalCategory S.Obj,
      (projectObj σ.obj W).as.length = k * W.length := fun W ↦ by
    rw [as_projectObj σ.obj W, length_projectObj_const hobj W, Nat.mul_comm]
  induction f with
  | id => dsimp only [Hom.subst, Hom.crossingExp]; omega
  | α_hom => dsimp only [Hom.subst, Hom.crossingExp]; omega
  | α_inv => dsimp only [Hom.subst, Hom.crossingExp]; omega
  | l_hom => dsimp only [Hom.subst, Hom.crossingExp]; omega
  | l_inv => dsimp only [Hom.subst, Hom.crossingExp]; omega
  | ρ_hom => dsimp only [Hom.subst, Hom.crossingExp]; omega
  | ρ_inv => dsimp only [Hom.subst, Hom.crossingExp]; omega
  | coupon g => dsimp only [Hom.subst, Hom.crossingExp]; rw [hc g]; omega
  | comp _ _ hf hg => dsimp only [Hom.subst, Hom.crossingExp]; rw [hf, hg, Int.mul_add]
  | whiskerLeft _ _ hf => dsimp only [Hom.subst, Hom.crossingExp]; exact hf
  | whiskerRight _ _ hf => dsimp only [Hom.subst, Hom.crossingExp]; exact hf
  | tensor _ _ hf hg => dsimp only [Hom.subst, Hom.crossingExp]; rw [hf, hg, Int.mul_add]
  | β_hom X Y =>
    dsimp only [Hom.subst, Hom.crossingExp]
    rw [hlen_proj X, hlen_proj Y, Int.natCast_mul, Int.natCast_mul,
      Int.mul_assoc (k : ℤ) (X.length : ℤ), Int.mul_left_comm (X.length : ℤ) (k : ℤ),
      ← Int.mul_assoc]
  | β_inv X Y =>
    dsimp only [Hom.subst, Hom.crossingExp]
    rw [hlen_proj X, hlen_proj Y, Int.natCast_mul, Int.natCast_mul, Int.mul_neg]
    congr 1
    rw [Int.mul_assoc (k : ℤ) (X.length : ℤ), Int.mul_left_comm (X.length : ℤ) (k : ℤ),
      ← Int.mul_assoc]

end FreeBraided

namespace BraidedSubstitution

open FreeBraided

variable (σ : BraidedSubstitution S T)

/-- The strong braided functor induced by a raw braided substitution: the universal lift of the
specified object expressions and the equivalence classes of the replacing coupons. -/
@[expose] def toFunctor : S.FreeBraided ⥤ T.FreeBraided :=
  FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))

instance : σ.toFunctor.Monoidal := inferInstanceAs
  (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Monoidal

instance : σ.toFunctor.Braided := inferInstanceAs
  (FreeBraided.lift σ.obj (fun g ↦ FreeBraided.homMk (σ.coupon g))).Braided

@[simp]
theorem toFunctor_ε : Functor.LaxMonoidal.ε σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_ε _ _

@[simp]
theorem toFunctor_η : Functor.OplaxMonoidal.η σ.toFunctor = 𝟙 _ :=
  FreeBraided.lift_η _ _

@[simp]
theorem toFunctor_μ (X Y : S.FreeBraided) :
    Functor.LaxMonoidal.μ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_μ _ _ X Y

@[simp]
theorem toFunctor_δ (X Y : S.FreeBraided) :
    Functor.OplaxMonoidal.δ σ.toFunctor X Y = 𝟙 _ :=
  FreeBraided.lift_δ _ _ X Y

@[simp]
theorem toFunctor_obj (X : S.FreeBraided) :
    σ.toFunctor.obj X = projectObj σ.obj X.as := by rfl

@[simp]
theorem toFunctor_map_coupon (g : S.Coupon) :
    σ.toFunctor.map (FreeBraided.coupon g) = FreeBraided.homMk (σ.coupon g) :=
  FreeBraided.lift_map_coupon _ _ g

/-- Interpreting a raw braided expression by the induced braided functor yields the equivalence
class of its raw substitution. -/
@[simp]
theorem toFunctor_map_homMk {X Y : FreeMonoidalCategory S.Obj} (f : FreeBraided.Hom X Y) :
    σ.toFunctor.map (FreeBraided.homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f) =
      FreeBraided.homMk (f.subst σ) := by
  induction f with
  | id X => exact liftMap_id _ _ ⟨X⟩
  | α_hom X Y Z => exact lift_map_associator_hom _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | α_inv X Y Z => exact lift_map_associator_inv _ _ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | l_hom X => exact lift_map_leftUnitor_hom _ _ ⟨X⟩
  | l_inv X => exact lift_map_leftUnitor_inv _ _ ⟨X⟩
  | ρ_hom X => exact lift_map_rightUnitor_hom _ _ ⟨X⟩
  | ρ_inv X => exact lift_map_rightUnitor_inv _ _ ⟨X⟩
  | β_hom X Y => exact lift_map_braiding_hom _ _ ⟨X⟩ ⟨Y⟩
  | β_inv X Y => exact lift_map_braiding_inv _ _ ⟨X⟩ ⟨Y⟩
  | coupon g => exact lift_map_coupon _ _ g
  | comp f g hf hg =>
    exact (liftMap_comp _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ≫ ·) hf hg)
  | whiskerLeft X f hf =>
    exact (lift_map_whiskerLeft _ _ ⟨X⟩ (homMk f)).trans
      (congrArg (projectObj σ.obj X ◁ ·) hf)
  | whiskerRight f X hf =>
    exact (lift_map_whiskerRight _ _ (homMk f) ⟨X⟩).trans
      (congrArg (· ▷ projectObj σ.obj X) hf)
  | tensor f g hf hg =>
    exact (lift_map_tensorHom _ _ (homMk f) (homMk g)).trans (congrArg₂ (· ⊗ₘ ·) hf hg)

/-- Under a braided substitution that replaces every object generator by a formal tensor word of
constant length `k` and every coupon by a crossing-free expression, the induced braided functor
scales crossing-exponent sums by `k * k`. -/
theorem crossingExp_toFunctor_map {k : ℕ}
    (hlenS : ∀ g : S.Coupon, (S.src g).length = (S.tgt g).length)
    (hlenT : ∀ g : T.Coupon, (T.src g).length = (T.tgt g).length)
    (hobj : ∀ a : S.Obj, (σ.obj a).as.length = k)
    (hc : ∀ g : S.Coupon, (σ.coupon g).crossingExp = 0)
    {X Y : S.FreeBraided} (f : X ⟶ Y) :
    crossingExp hlenT (σ.toFunctor.map f) = (k : ℤ) * (k : ℤ) * crossingExp hlenS f := by
  induction f using Quotient.inductionOn with | _ f
  exact (congrArg (crossingExp hlenT) (σ.toFunctor_map_homMk f)).trans
    ((crossingExp_homMk hlenT (f.subst σ)).trans
      ((f.crossingExp_subst σ hobj hc).trans
        (congrArg ((k : ℤ) * (k : ℤ) * ·) (crossingExp_homMk hlenS f).symm)))

end BraidedSubstitution

namespace FreeBraided

/-- Raw braided substitution preserves the congruence generated by the braided-monoidal axioms,
with no assumption on the replacing coupons. -/
theorem HomEquiv.subst (σ : BraidedSubstitution S T) {X Y} {f g : Hom X Y} (h : HomEquiv f g) :
    HomEquiv (f.subst σ) (g.subst σ) := by
  apply Quotient.exact (s := setoidHom _ _)
  exact (σ.toFunctor_map_homMk f).symm.trans
    ((congrArg (σ.toFunctor.map (X := ⟨X⟩) (Y := ⟨Y⟩)) (Quotient.sound h)).trans
      (σ.toFunctor_map_homMk g))

end FreeBraided

end TauCeti.TensorSignature
