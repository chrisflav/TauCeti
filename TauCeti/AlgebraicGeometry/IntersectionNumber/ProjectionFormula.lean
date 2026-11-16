/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Degree.Pullback
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
import TauCeti.AlgebraicGeometry.Curves.Degree.Normalization

/-!
# The projection formula for intersection numbers

Let `k` be a field, `C` an integral proper curve over `k`, possibly singular, and `g : C' ⟶ C` a
finite morphism over `k`. When `g` is flat of constant rank `n` and `H⁰(C', 𝒪_{C'})`,
`H¹(C', 𝒪_{C'})` are finite-dimensional, pulling back along `g` multiplies degrees by `n`
(`LineBundleClass.eulerDegree_pullback_of_finrank_eq`). When `C'` is integral and `g` is finite
dominant, pulling back along `g` multiplies degrees by `[K(C') : K(C)]` without regularity or
cohomology-finiteness hypotheses (`LineBundleClass.eulerDegree_pullback_of_isFinite_isDominant`).

For intersection numbers this is the **projection formula**. Let `ι : C ⟶ X` be a curve on a
scheme `X`, for instance a component of the special fibre of a regular model, and let
`ι' : C' ⟶ X'` be a curve on a scheme `X'` with a morphism `f : X' ⟶ X` carrying `C'` onto `C`
by `g`, that is `ι' ≫ f = g ≫ ι`. Then for every line-bundle class `a` on `X`,

`(f^* a · C') = n · (a · C)`,

the intersection number of `a` with the cycle `f_* C' = n C`
(`LineBundleClass.intersectionNumber_pullback_of_finrank_eq` and
`LineBundleClass.intersectionNumber_pullback_of_isDominant`). Curves contracted by `f` are
treated by `LineBundleClass.intersectionNumber_eq_zero_of_eq_comp`.

## Main results

* `LineBundleClass.intersectionNumber_comp_of_finrank_eq` and
  `LineBundleClass.intersectionNumber_comp_of_isDominant`: `(a · (g ≫ ι)) = n · (a · ι)`.
* `LineBundleClass.intersectionNumber_pullback_of_finrank_eq` and
  `LineBundleClass.intersectionNumber_pullback_of_isDominant`: the projection formula
  `(f^* a · C') = n · (a · C)`, including the unconditional finite dominant case on possibly
  singular integral curves.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.2 (the projection formula on
  arithmetic surfaces).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace LineBundleClass

variable (k : Type u) [Field k] {C C' : Scheme.{u}} [C.Over (Spec (.of k))]
  [C'.Over (Spec (.of k))] (g : C' ⟶ C) [g.IsOver (Spec (.of k))] [IsFinite g]
  [IsIntegral C] [IsProper (C ↘ Spec (.of k))] [RelativeDimensionLE 1 (C ↘ Spec (.of k))]

variable {X X' : Scheme.{u}} (ι : C ⟶ X)

section FiniteFlat

variable [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C').obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial C').obj 1)]

/-- **Intersection numbers with a finite flat cover of a curve.** If `g : C' ⟶ C` is finite flat
of constant rank `n` onto an integral proper curve `ι : C ⟶ X` over `k` and `H⁰(C', 𝒪_{C'})`,
`H¹(C', 𝒪_{C'})` are finite-dimensional, then the intersection number of a class `a` on `X` with
`C'`, mapping to `X` by `g ≫ ι`, is `n` times its intersection number with `C`. -/
theorem intersectionNumber_comp_of_finrank_eq [Flat g] {n : ℕ} (hg : ∀ x, g.finrank x = n)
    (a : LineBundleClass X) :
    intersectionNumber k (g ≫ ι) a = n * intersectionNumber k ι a := by
  have := (InvertibleSheaf.trivial C).finiteDimensional_cohomology_of_isProper k (i := 0) (by omega)
  have := (InvertibleSheaf.trivial C).finiteDimensional_cohomology_of_isProper k (i := 1) (by omega)
  rw [intersectionNumber_def, intersectionNumber_def, ← pullback_comp,
    eulerDegree_pullback_of_finrank_eq k g hg]

/-- **The projection formula.** Let `ι : C ⟶ X` and `ι' : C' ⟶ X'` be curves, `f : X' ⟶ X` a
morphism and `g : C' ⟶ C` a finite flat morphism of constant rank `n` with `ι' ≫ f = g ≫ ι`, where
`C` is an integral proper curve over `k` and `H⁰(C', 𝒪_{C'})`, `H¹(C', 𝒪_{C'})` are
finite-dimensional. Then `(f^* a · C') = n · (a · C)` for every line-bundle class `a` on `X`: the
pullback of `a` meets `C'` as `a` meets the pushforward `f_* C' = n C`. -/
theorem intersectionNumber_pullback_of_finrank_eq [Flat g] {n : ℕ} (hg : ∀ x, g.finrank x = n)
    (f : X' ⟶ X) {ι' : C' ⟶ X'} (w : ι' ≫ f = g ≫ ι) (a : LineBundleClass X) :
    intersectionNumber k ι' (pullback f a) = n * intersectionNumber k ι a := by
  rw [intersectionNumber_pullback, w, intersectionNumber_comp_of_finrank_eq k g ι hg]

end FiniteFlat

section FiniteDominant

/-- **Intersection numbers with a finite dominant cover of a curve.** If `g : C' ⟶ C` is a finite
dominant `k`-morphism between integral schemes and `C` is proper over `k` with fibres of dimension
at most one (possibly singular), then `(a · (g ≫ ι)) = [K(C') : K(C)] · (a · ι)` for every
line-bundle class `a` on `X`. -/
theorem intersectionNumber_comp_of_isDominant [IsIntegral C'] [IsDominant g]
    (a : LineBundleClass X) :
    intersectionNumber k (g ≫ ι) a =
      Module.finrank g.functionFieldMap.hom.fieldRange C'.functionField *
        intersectionNumber k ι a := by
  rw [intersectionNumber_def, intersectionNumber_def, ← pullback_comp,
    eulerDegree_pullback_of_isFinite_isDominant k g]

/-- **The projection formula for a finite dominant morphism.** Let `ι : C ⟶ X` and `ι' : C' ⟶ X'`
be curves, `f : X' ⟶ X` a morphism and `g : C' ⟶ C` a finite dominant `k`-morphism between integral
schemes with `ι' ≫ f = g ≫ ι`, where `C` is proper over `k` with fibres of dimension at most one
(neither `C` nor `C'` need be regular). Then `(f^* a · C') = [K(C') : K(C)] · (a · C)` for every
line-bundle class `a` on `X`. -/
theorem intersectionNumber_pullback_of_isDominant [IsIntegral C'] [IsDominant g]
    (f : X' ⟶ X) {ι' : C' ⟶ X'} (w : ι' ≫ f = g ≫ ι) (a : LineBundleClass X) :
    intersectionNumber k ι' (pullback f a) =
      Module.finrank g.functionFieldMap.hom.fieldRange C'.functionField *
        intersectionNumber k ι a := by
  rw [intersectionNumber_pullback, w, intersectionNumber_comp_of_isDominant k g ι]

end FiniteDominant

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
