/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Volume
public import TauCeti.RepresentationTheory.SU2.SymmetricPower

/-!
# The defining two-dimensional representation of `SU(2)` and its invariant volume form

`SU(2)` sits inside `GL₂(ℂ)` via `TauCeti.SU2.toGL` and inside `SL₂(ℂ)` via
`Matrix.specialUnitaryGroup.toSL`. Restricting the standard column-vector representation of
`GL₂(ℂ)` along `TauCeti.SU2.toGL` gives the **defining two-dimensional complex representation**
`TauCeti.SU2.stdRep` of `SU(2)` on `Fin 2 → ℂ`.

Because `TauCeti.SU2.toGL` factors through `SL₂(ℂ)`, the defining representation of `SU(2)` is
also the restriction of `TauCeti.stdSLRep ℂ 2` along `Matrix.specialUnitaryGroup.toSL`. It is
therefore faithful (`TauCeti.SU2.stdRep_injective`), has character equal to the matrix trace
(`TauCeti.SU2.char_stdRep`), preserves the standard-basis determinant alternating form
`Matrix.detRowAlternating` (`TauCeti.SU2.detRowAlternating_stdRep`), and has trivial second
exterior power (`TauCeti.SU2.topExtPowerEquivTrivial`). Restricting further along `H.subtype`
equips every subgroup `H ≤ SU(2)` with a faithful two-dimensional complex representation preserving
a nondegenerate alternating form (`TauCeti.SU2.stdRep_comp_subtype_injective`,
`TauCeti.SU2.detRowAlternating_stdRep_subtype`), the input to the McKay quiver of finite subgroups
of `SU(2)`.

## Main definitions

* `TauCeti.SU2.stdRep`: the defining representation of `SU(2)` on `Fin 2 → ℂ`.
* `TauCeti.SU2.stdFDRep`: its finite-dimensional bundled form in `FDRep ℂ SU2`.
* `TauCeti.SU2.topExtPowerEquivTrivial`: the isomorphism `⋀[ℂ]^2 (Fin 2 → ℂ) ≅ ℂ` of `SU(2)`
  representations.

## Main results

* `TauCeti.SU2.stdSLRep_comp_toSL`: restricting `stdSLRep ℂ 2` along `toSL` recovers `stdRep`.
* `TauCeti.SU2.stdRep_injective` and `TauCeti.SU2.stdRep_comp_subtype_injective`: faithfulness on
  `SU(2)` and on every subgroup `H ≤ SU(2)`.
* `TauCeti.SU2.char_stdRep` and `TauCeti.SU2.char_stdFDRep`: the character is the matrix trace.
* `TauCeti.SU2.detRowAlternating_stdRep` and `TauCeti.SU2.detRowAlternating_stdRep_subtype`:
  invariance of the standard-basis determinant alternating form.
* `TauCeti.SU2.stdRep_exteriorPower_two_apply`: `SU(2)` acts trivially on `⋀[ℂ]^2 (Fin 2 → ℂ)`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, Springer, 1991,
  Lecture 10.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti.SU2

/-- **The defining two-dimensional complex representation of `SU(2)`** on column vectors
`Fin 2 → ℂ`, obtained by restricting `TauCeti.stdRep ℂ 2` along `TauCeti.SU2.toGL`. -/
def stdRep : Representation ℂ SU2 (Fin 2 → ℂ) :=
  (_root_.TauCeti.stdRep ℂ 2).comp toGL

theorem stdRep_def : stdRep = (_root_.TauCeti.stdRep ℂ 2).comp toGL := (rfl)

/-- The defining representation of `SU(2)` acts by multiplication by the underlying matrix. -/
@[simp]
theorem stdRep_apply (g : SU2) :
    stdRep g = Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa only [stdRep, MonoidHom.comp_apply, coe_toGL] using
    _root_.TauCeti.stdRep_apply ℂ 2 (toGL g)

/-- Evaluation of the defining `SU(2)` action is matrix-vector multiplication. -/
theorem stdRep_apply_apply (g : SU2) (v : Fin 2 → ℂ) :
    stdRep g v = (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [stdRep_apply, Matrix.mulVecLin_apply]

/-- Restricting the standard representation of `SL₂(ℂ)` along `Matrix.specialUnitaryGroup.toSL`
recovers the defining representation of `SU(2)`. -/
@[simp]
theorem stdSLRep_comp_toSL :
    (stdSLRep ℂ 2).comp Matrix.specialUnitaryGroup.toSL = stdRep :=
  MonoidHom.ext fun g => LinearMap.ext fun v => by simp

/-- **The defining representation of `SU(2)` is faithful.** -/
theorem stdRep_injective : Function.Injective stdRep :=
  fun _ _ h => toGL_injective (_root_.TauCeti.stdRep_injective ℂ 2 h)

/-- The defining representation of `SU(2)`, bundled as an object of `FDRep ℂ SU2`. -/
noncomputable abbrev stdFDRep : FDRep ℂ SU2 :=
  FDRep.of stdRep

/-- **The character of the defining representation of `SU(2)` is the matrix trace.** -/
@[simp]
theorem char_stdRep (g : SU2) :
    stdRep.character g = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa only [stdRep, Representation.character, MonoidHom.comp_apply, coe_toGL] using
    _root_.TauCeti.char_stdRep ℂ 2 (toGL g)

/-- The character of the bundled defining representation of `SU(2)` is the matrix trace. -/
@[simp]
theorem char_stdFDRep (g : SU2) :
    stdFDRep.character g = Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using char_stdRep g

/-- **The defining `SU(2)` action preserves the standard-basis determinant alternating form.**

As with `TauCeti.detRowAlternating_stdSLRep`, this is deliberately not a `simp` lemma because
`stdRep_apply` already rewrites `stdRep g` to `Matrix.mulVecLin ↑g`. -/
theorem detRowAlternating_stdRep (g : SU2) (v : Fin 2 → Fin 2 → ℂ) :
    Matrix.detRowAlternating (fun i => stdRep g (v i)) = Matrix.detRowAlternating v := by
  have h := detRowAlternating_stdSLRep ℂ 2 (Matrix.specialUnitaryGroup.toSL g) v
  simpa only [stdSLRep_apply_apply, Matrix.specialUnitaryGroup.coe_toSL, stdRep_apply_apply]
    using h

/-- `SU(2)` acts trivially on the top exterior power `⋀[ℂ]^2 (Fin 2 → ℂ)` of its defining
representation. -/
theorem stdRep_exteriorPower_two_apply (g : SU2) :
    stdRep.exteriorPower 2 g = LinearMap.id := by
  have h := stdSLRep_exteriorPower_self_apply ℂ 2 (Matrix.specialUnitaryGroup.toSL g)
  simpa only [Representation.exteriorPower_apply, stdSLRep_apply,
    Matrix.specialUnitaryGroup.coe_toSL, stdRep_apply] using h

/-- **The second exterior power of the defining representation of `SU(2)` is trivial.** -/
noncomputable def topExtPowerEquivTrivial :
    (stdRep.exteriorPower 2).Equiv (Representation.trivial ℂ SU2 ℂ) :=
  .mk ((Pi.basisFun ℂ (Fin 2)).exteriorPowerTopEquiv) fun g => by
    rw [stdRep_exteriorPower_two_apply]
    ext x
    simp [Representation.isTrivial_def]

@[simp]
theorem topExtPowerEquivTrivial_toLinearEquiv :
    topExtPowerEquivTrivial.toLinearEquiv = (Pi.basisFun ℂ (Fin 2)).exteriorPowerTopEquiv :=
  (rfl)

@[simp]
theorem topExtPowerEquivTrivial_apply_ιMulti (v : Fin 2 → (Fin 2 → ℂ)) :
    topExtPowerEquivTrivial (exteriorPower.ιMulti ℂ 2 v) = (Matrix.of v).det := by
  rw [← Representation.Equiv.coe_toIntertwiningMap,
    ← Representation.Equiv.toLinearEquiv_apply, topExtPowerEquivTrivial_toLinearEquiv,
    Module.Basis.exteriorPowerTopEquiv_apply_ιMulti, Pi.basisFun_det_apply]

/-- **The defining representation of `SU(2)` restricts to a faithful representation of every
subgroup `H ≤ SU(2)`.** -/
theorem stdRep_comp_subtype_injective (H : Subgroup SU2) :
    Function.Injective (stdRep.comp H.subtype) :=
  stdRep_injective.comp Subtype.val_injective

/-- Every subgroup `H ≤ SU(2)` preserves `Matrix.detRowAlternating` in its restricted defining
representation. -/
theorem detRowAlternating_stdRep_subtype (H : Subgroup SU2) (g : H) (v : Fin 2 → Fin 2 → ℂ) :
    Matrix.detRowAlternating (fun i => (stdRep.comp H.subtype) g (v i)) =
      Matrix.detRowAlternating v :=
  detRowAlternating_stdRep (g : SU2) v

end TauCeti.SU2
