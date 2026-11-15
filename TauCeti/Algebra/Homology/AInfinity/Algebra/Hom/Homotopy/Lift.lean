/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Transformation

/-!
# Graded chain-homotopy inverses and relative lifting of transformations

Let `f : A ⟶ B` be a morphism of `A∞` algebras over a commutative ring `R`.  A *graded
chain-homotopy inverse* of `f.linearPart` (`TauCeti.AInfinityHom.LinearHomotopyInverse`) consists
of a degree-zero chain map `inv : B →ₗ[R] A` together with degree-`(-1)` chain homotopies
`leftHomotopy` on `A` and `rightHomotopy` on `B` witnessing `inv ∘ f₁ ∼ id_A` and
`f₁ ∘ inv ∼ id_B`.

Any such chain-homotopy inverse solves coupled relative cocycle equations simultaneously
(`TauCeti.AInfinityHom.LinearHomotopyInverse.exists_relative_coboundary`): given homogeneous linear
maps `Φ : M →ₗ[R] A` and `Ψ : M →ₗ[R] B` from a graded differential module `(M, d_M)` with
`m₁ ∘ Φ + ε • (Φ ∘ d_M) = 0` and `m₁ ∘ Ψ - ε • (Ψ ∘ d_M) = f₁ ∘ Φ`, correcting the trial
preimage `inv ∘ Ψ - h_L ∘ Φ` by `inv` applied to the cycle defect `Ψ - f₁ ∘ (inv ∘ Ψ - h_L ∘ Φ)`
produces simultaneous coboundary witnesses `(ξ, η)` vanishing wherever `Φ` and `Ψ` vanish.

Inducting along the conilpotence filtration of the reduced bar coalgebra yields relative cocycle
lifting for postcomposition with `f` on the complex of reduced transformations
(`TauCeti.AInfinityHom.LinearHomotopyInverse.exists_reducedTransformationCochains_compRight`): for
any `A∞` morphisms `u v : C ⟶ A`, every closed reduced transformation `D` from `u` to `v` whose
postcomposition `compRight f D` is a coboundary `δ K` is itself a coboundary `δ L` with
`compRight f L` homologous to `K`.  At degree `-1`, this lifts any homotopy from `f ∘ u` to
`f ∘ v` across `f` to a homotopy from `u` to `v`
(`TauCeti.AInfinityHom.LinearHomotopyInverse.liftHomotopy`).

## Main definitions

* `TauCeti.AInfinityHom.Homotopy.cast`: transport a homotopy along equalities of source and target
  morphisms.
* `TauCeti.AInfinityHom.LinearHomotopyInverse`: a graded two-sided chain-homotopy inverse of
  `f.linearPart`.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.liftHomotopy`: lift a homotopy from `f ∘ u` to
  `f ∘ v` across `f` to a homotopy from `u` to `v`.

## Main results

* `TauCeti.AInfinityHom.LinearHomotopyInverse.exists_relative_coboundary`: simultaneous solution of
  coupled unary cocycle equations.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.exists_reducedTransformationCochains_compRight`:
  relative cocycle lifting for postcomposition with `f` on reduced transformations.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.nonempty_homotopy_comp_left_iff`: `f ∘ u` and
  `f ∘ v` are homotopic if and only if `u` and `v` are homotopic.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1, Section 1.3.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), Sections 1--2.
-/

public section

namespace TauCeti

universe uR uA uB uC

namespace AInfinityHom

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-! ### Transport of homotopies -/

/-- Transport a homotopy along equalities of its source and target morphisms. -/
def Homotopy.cast {f f' g g' : AInfinityHom AA BB} (hf : f = f') (hg : g = g')
    (h : Homotopy f g) : Homotopy f' g' :=
  hf ▸ hg ▸ h

/-- Transporting a homotopy leaves its underlying bar coderivation unchanged. -/
@[simp]
theorem Homotopy.barHomotopy_cast {f f' g g' : AInfinityHom AA BB} (hf : f = f') (hg : g = g')
    (h : Homotopy f g) : (Homotopy.cast hf hg h).barHomotopy = h.barHomotopy := by
  subst hf; subst hg; rfl

/-- Transporting a homotopy leaves its Taylor components unchanged. -/
@[simp]
theorem Homotopy.taylor_cast {f f' g g' : AInfinityHom AA BB} (hf : f = f') (hg : g = g')
    (h : Homotopy f g) : (Homotopy.cast hf hg h).taylor = h.taylor := by
  subst hf; subst hg; rfl

private theorem map_units_smul {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (u : X →ₗ[R] Y) (ε : ℤˣ) (x : X) :
    u (ε • x) = ε • u x := by
  rw [Units.smul_def, map_zsmul, ← Units.smul_def]

/-! ### Graded chain-homotopy inverses of the linear part -/

/-- A graded two-sided chain-homotopy inverse of the linear part `f.linearPart` of an `A∞`
morphism `f`: a degree-zero chain map `inv : B →ₗ[R] A` together with degree-`(-1)` chain
homotopies `leftHomotopy` on `A` and `rightHomotopy` on `B`. -/
@[ext]
structure LinearHomotopyInverse (f : AInfinityHom AA BB) where
  /-- The chain-homotopy inverse of `f.linearPart`. -/
  inv : B →ₗ[R] A
  /-- The inverse preserves the internal grading. -/
  isHomogeneous_inv : LinearMap.IsHomogeneous inv BB.grading.piece AA.grading.piece 0
  /-- The inverse intertwines the unary differentials. -/
  differential_comp_inv : AA.differential ∘ₗ inv = inv ∘ₗ BB.differential
  /-- The left chain homotopy between `inv ∘ₗ f.linearPart` and `id_A`. -/
  leftHomotopy : Module.End R A
  /-- The left chain homotopy has internal degree `-1`. -/
  isHomogeneous_leftHomotopy :
    LinearMap.IsHomogeneous leftHomotopy AA.grading.piece AA.grading.piece (-1)
  /-- The left chain-homotopy equation `inv ∘ f₁ - id = m₁ ∘ h_L + h_L ∘ m₁`. -/
  inv_comp_linearPart_sub_id :
    inv ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ leftHomotopy + leftHomotopy ∘ₗ AA.differential
  /-- The right chain homotopy between `f.linearPart ∘ₗ inv` and `id_B`. -/
  rightHomotopy : Module.End R B
  /-- The right chain homotopy has internal degree `-1`. -/
  isHomogeneous_rightHomotopy :
    LinearMap.IsHomogeneous rightHomotopy BB.grading.piece BB.grading.piece (-1)
  /-- The right chain-homotopy equation `f₁ ∘ inv - id = m₁ ∘ h_R + h_R ∘ m₁`. -/
  linearPart_comp_inv_sub_id :
    f.linearPart ∘ₗ inv - LinearMap.id =
      BB.differential ∘ₗ rightHomotopy + rightHomotopy ∘ₗ BB.differential

namespace LinearHomotopyInverse

/-- The identity chain-homotopy inverse of the identity `A∞` morphism. -/
protected def id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).LinearHomotopyInverse where
  inv := LinearMap.id
  isHomogeneous_inv := LinearMap.isHomogeneous_id _
  differential_comp_inv := by rw [LinearMap.comp_id, LinearMap.id_comp]
  leftHomotopy := 0
  isHomogeneous_leftHomotopy := LinearMap.isHomogeneous_zero _ _ _
  inv_comp_linearPart_sub_id := by
    rw [linearPart_id, LinearMap.comp_id, sub_self, LinearMap.comp_zero, LinearMap.zero_comp,
      add_zero]
  rightHomotopy := 0
  isHomogeneous_rightHomotopy := LinearMap.isHomogeneous_zero _ _ _
  linearPart_comp_inv_sub_id := by
    rw [linearPart_id, LinearMap.comp_id, sub_self, LinearMap.comp_zero, LinearMap.zero_comp,
      add_zero]

/-- An `A∞` morphism with bijective linear part has a strict chain-homotopy inverse with zero
homotopies. -/
noncomputable def ofBijective {f : AInfinityHom AA BB} (hf : Function.Bijective f.linearPart) :
    f.LinearHomotopyInverse where
  inv := (f.inverse hf).linearPart
  isHomogeneous_inv := (f.inverse hf).isHomogeneous_linearPart
  differential_comp_inv := (f.inverse hf).differential_comp_linearPart
  leftHomotopy := 0
  isHomogeneous_leftHomotopy := LinearMap.isHomogeneous_zero _ _ _
  inv_comp_linearPart_sub_id := by
    rw [← linearPart_comp, f.inverse_comp_cancel hf, linearPart_id, sub_self,
      LinearMap.comp_zero, LinearMap.zero_comp, add_zero]
  rightHomotopy := 0
  isHomogeneous_rightHomotopy := LinearMap.isHomogeneous_zero _ _ _
  linearPart_comp_inv_sub_id := by
    rw [← linearPart_comp, f.comp_inverse_cancel hf, linearPart_id, sub_self,
      LinearMap.comp_zero, LinearMap.zero_comp, add_zero]

/-- Read off a graded chain-homotopy inverse of `f.linearPart` from an `A∞` homotopy inverse `g`
and homotopies `g ∘ f ∼ id_A` and `f ∘ g ∼ id_B`. -/
noncomputable def ofHomotopy {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (h₁ : Homotopy (g.comp f) (AInfinityHom.id AA))
    (h₂ : Homotopy (f.comp g) (AInfinityHom.id BB)) : f.LinearHomotopyInverse where
  inv := g.linearPart
  isHomogeneous_inv := g.isHomogeneous_linearPart
  differential_comp_inv := g.differential_comp_linearPart
  leftHomotopy := h₁.linearHomotopy
  isHomogeneous_leftHomotopy := LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
    simpa only [sub_eq_add_neg] using h₁.linearHomotopy_mem ha
  inv_comp_linearPart_sub_id := LinearMap.ext fun a ↦ by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, linearPart_comp, linearPart_id, AInfinityAlgebra.differential_apply]
      using h₁.linearPart_sub_linearPart a
  rightHomotopy := h₂.linearHomotopy
  isHomogeneous_rightHomotopy := LinearMap.isHomogeneous_def.2 fun _ _ hb ↦ by
    simpa only [sub_eq_add_neg] using h₂.linearHomotopy_mem hb
  linearPart_comp_inv_sub_id := LinearMap.ext fun b ↦ by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, linearPart_comp, linearPart_id, AInfinityAlgebra.differential_apply]
      using h₂.linearPart_sub_linearPart b

private theorem comp_chain_homotopy {X Y Z : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    {dX : Module.End R X} {dY : Module.End R Y}
    {p : X →ₗ[R] Y} {q : Y →ₗ[R] Z} {q' : Z →ₗ[R] Y} {p' : Y →ₗ[R] X}
    {h₁ : Module.End R X} {h₂ : Module.End R Y}
    (hp : dY ∘ₗ p = p ∘ₗ dX) (hp' : dX ∘ₗ p' = p' ∘ₗ dY)
    (hh₁ : p' ∘ₗ p - LinearMap.id = dX ∘ₗ h₁ + h₁ ∘ₗ dX)
    (hh₂ : q' ∘ₗ q - LinearMap.id = dY ∘ₗ h₂ + h₂ ∘ₗ dY) :
    (p' ∘ₗ q') ∘ₗ (q ∘ₗ p) - LinearMap.id =
      dX ∘ₗ (h₁ + p' ∘ₗ h₂ ∘ₗ p) + (h₁ + p' ∘ₗ h₂ ∘ₗ p) ∘ₗ dX := by
  refine LinearMap.ext fun x ↦ ?_
  have e₁ : p' (p x) - x = dX (h₁ x) + h₁ (dX x) := by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply] using LinearMap.congr_fun hh₁ x
  have e₂ : p' (q' (q (p x))) - p' (p x) = p' (dY (h₂ (p x))) + p' (h₂ (dY (p x))) := by
    simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, map_sub, map_add] using congrArg p' (LinearMap.congr_fun hh₂ (p x))
  have ep : dY (p x) = p (dX x) := LinearMap.congr_fun hp x
  have ep' : dX (p' (h₂ (p x))) = p' (dY (h₂ (p x))) := LinearMap.congr_fun hp' (h₂ (p x))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_add]
  rw [ep', ← ep]
  calc p' (q' (q (p x))) - x
      = (p' (q' (q (p x))) - p' (p x)) + (p' (p x) - x) := by abel
    _ = p' (dY (h₂ (p x))) + p' (h₂ (dY (p x))) + (dX (h₁ x) + h₁ (dX x)) := by rw [e₂, e₁]
    _ = dX (h₁ x) + p' (dY (h₂ (p x))) + (h₁ (dX x) + p' (h₂ (dY (p x)))) := by abel

/-- Graded chain-homotopy inverses compose in reverse order. -/
noncomputable def comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (cg : g.LinearHomotopyInverse) (cf : f.LinearHomotopyInverse) :
    (g.comp f).LinearHomotopyInverse where
  inv := cf.inv ∘ₗ cg.inv
  isHomogeneous_inv := by
    simpa only [add_zero] using cf.isHomogeneous_inv.comp cg.isHomogeneous_inv
  differential_comp_inv := by
    rw [← LinearMap.comp_assoc, cf.differential_comp_inv, LinearMap.comp_assoc,
      cg.differential_comp_inv, LinearMap.comp_assoc]
  leftHomotopy := cf.leftHomotopy + cf.inv ∘ₗ cg.leftHomotopy ∘ₗ f.linearPart
  isHomogeneous_leftHomotopy := cf.isHomogeneous_leftHomotopy.add
    (by simpa only [zero_add, add_zero] using
      cf.isHomogeneous_inv.comp (cg.isHomogeneous_leftHomotopy.comp f.isHomogeneous_linearPart))
  inv_comp_linearPart_sub_id := by
    rw [linearPart_comp]
    exact comp_chain_homotopy f.differential_comp_linearPart cf.differential_comp_inv
      cf.inv_comp_linearPart_sub_id cg.inv_comp_linearPart_sub_id
  rightHomotopy := cg.rightHomotopy + g.linearPart ∘ₗ cf.rightHomotopy ∘ₗ cg.inv
  isHomogeneous_rightHomotopy := cg.isHomogeneous_rightHomotopy.add
    (by simpa only [zero_add, add_zero] using
      g.isHomogeneous_linearPart.comp (cf.isHomogeneous_rightHomotopy.comp cg.isHomogeneous_inv))
  linearPart_comp_inv_sub_id := by
    rw [linearPart_comp]
    exact comp_chain_homotopy cg.differential_comp_inv g.differential_comp_linearPart
      cg.linearPart_comp_inv_sub_id cf.linearPart_comp_inv_sub_id

/-! ### Coupled linear obstruction solver -/

section ObstructionSolver

variable {f : AInfinityHom AA BB} {M : Type*} [AddCommMonoid M] [Module R M]

private noncomputable def obstructionTrial (c : f.LinearHomotopyInverse)
    (Φ : M →ₗ[R] A) (Ψ : M →ₗ[R] B) : M →ₗ[R] A :=
  c.inv ∘ₗ Ψ - c.leftHomotopy ∘ₗ Φ

private noncomputable def obstructionResidual (c : f.LinearHomotopyInverse)
    (Φ : M →ₗ[R] A) (Ψ : M →ₗ[R] B) : M →ₗ[R] B :=
  Ψ - f.linearPart ∘ₗ c.obstructionTrial Φ Ψ

private noncomputable def solveLeft (c : f.LinearHomotopyInverse)
    (Φ : M →ₗ[R] A) (Ψ : M →ₗ[R] B) : M →ₗ[R] A :=
  c.obstructionTrial Φ Ψ + c.inv ∘ₗ c.obstructionResidual Φ Ψ

private noncomputable def solveRight (c : f.LinearHomotopyInverse)
    (Φ : M →ₗ[R] A) (Ψ : M →ₗ[R] B) : M →ₗ[R] B :=
  -(c.rightHomotopy ∘ₗ c.obstructionResidual Φ Ψ)

private theorem differential_comp_obstructionTrial (c : f.LinearHomotopyInverse)
    (dM : Module.End R M) (ε : ℤˣ) {Φ : M →ₗ[R] A} {Ψ : M →ₗ[R] B}
    (hΦ : AA.differential ∘ₗ Φ + ε • (Φ ∘ₗ dM) = 0)
    (hΨ : BB.differential ∘ₗ Ψ - ε • (Ψ ∘ₗ dM) = f.linearPart ∘ₗ Φ) :
    AA.differential ∘ₗ c.obstructionTrial Φ Ψ - ε • (c.obstructionTrial Φ Ψ ∘ₗ dM) = Φ :=
  LinearMap.ext fun m ↦ by
    have einv : AA.differential (c.inv (Ψ m)) = c.inv (BB.differential (Ψ m)) :=
      LinearMap.congr_fun c.differential_comp_inv (Ψ m)
    have eΨ : BB.differential (Ψ m) = f.linearPart (Φ m) + ε • Ψ (dM m) :=
      sub_eq_iff_eq_add.1 <| by
        simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
          using LinearMap.congr_fun hΨ m
    have el : c.inv (f.linearPart (Φ m)) =
        AA.differential (c.leftHomotopy (Φ m)) + c.leftHomotopy (AA.differential (Φ m)) + Φ m :=
      sub_eq_iff_eq_add.1 <| by
        simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.id_apply] using LinearMap.congr_fun c.inv_comp_linearPart_sub_id (Φ m)
    have eΦ : AA.differential (Φ m) = -(ε • Φ (dM m)) :=
      eq_neg_of_add_eq_zero_left <| by
        simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.zero_apply] using LinearMap.congr_fun hΦ m
    simp only [obstructionTrial, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      map_sub]
    rw [einv, eΨ, map_add, map_units_smul, el, eΦ, map_neg, map_units_smul, smul_sub]
    abel

private theorem differential_comp_obstructionResidual (c : f.LinearHomotopyInverse)
    (dM : Module.End R M) (ε : ℤˣ) {Φ : M →ₗ[R] A} {Ψ : M →ₗ[R] B}
    (hΦ : AA.differential ∘ₗ Φ + ε • (Φ ∘ₗ dM) = 0)
    (hΨ : BB.differential ∘ₗ Ψ - ε • (Ψ ∘ₗ dM) = f.linearPart ∘ₗ Φ) :
    BB.differential ∘ₗ c.obstructionResidual Φ Ψ = ε • (c.obstructionResidual Φ Ψ ∘ₗ dM) :=
  LinearMap.ext fun m ↦ by
    have et : AA.differential (c.obstructionTrial Φ Ψ m) =
        Φ m + ε • c.obstructionTrial Φ Ψ (dM m) :=
      sub_eq_iff_eq_add.1 <| by
        simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
          using LinearMap.congr_fun (c.differential_comp_obstructionTrial dM ε hΦ hΨ) m
    have eΨ : BB.differential (Ψ m) = f.linearPart (Φ m) + ε • Ψ (dM m) :=
      sub_eq_iff_eq_add.1 <| by
        simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
          using LinearMap.congr_fun hΨ m
    have ef : BB.differential (f.linearPart (c.obstructionTrial Φ Ψ m)) =
        f.linearPart (AA.differential (c.obstructionTrial Φ Ψ m)) :=
      LinearMap.congr_fun f.differential_comp_linearPart (c.obstructionTrial Φ Ψ m)
    simp only [obstructionResidual, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      map_sub]
    rw [ef, et, eΨ, map_add, map_units_smul, smul_sub]
    abel

private theorem solveLeft_spec (c : f.LinearHomotopyInverse) (dM : Module.End R M) (ε : ℤˣ)
    {Φ : M →ₗ[R] A} {Ψ : M →ₗ[R] B}
    (hΦ : AA.differential ∘ₗ Φ + ε • (Φ ∘ₗ dM) = 0)
    (hΨ : BB.differential ∘ₗ Ψ - ε • (Ψ ∘ₗ dM) = f.linearPart ∘ₗ Φ) :
    AA.differential ∘ₗ c.solveLeft Φ Ψ - ε • (c.solveLeft Φ Ψ ∘ₗ dM) = Φ :=
  LinearMap.ext fun m ↦ by
    have et : AA.differential (c.obstructionTrial Φ Ψ m) - ε • c.obstructionTrial Φ Ψ (dM m) =
        Φ m := by
      simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
        using LinearMap.congr_fun (c.differential_comp_obstructionTrial dM ε hΦ hΨ) m
    have eres : BB.differential (c.obstructionResidual Φ Ψ m) =
        ε • c.obstructionResidual Φ Ψ (dM m) := by
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply]
        using LinearMap.congr_fun (c.differential_comp_obstructionResidual dM ε hΦ hΨ) m
    have einv : AA.differential (c.inv (c.obstructionResidual Φ Ψ m)) =
        c.inv (BB.differential (c.obstructionResidual Φ Ψ m)) :=
      LinearMap.congr_fun c.differential_comp_inv (c.obstructionResidual Φ Ψ m)
    simp only [solveLeft, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, map_add, smul_add]
    rw [einv, eres, map_units_smul, ← et]
    abel

private theorem solveRight_spec (c : f.LinearHomotopyInverse) (dM : Module.End R M) (ε : ℤˣ)
    {Φ : M →ₗ[R] A} {Ψ : M →ₗ[R] B}
    (hΦ : AA.differential ∘ₗ Φ + ε • (Φ ∘ₗ dM) = 0)
    (hΨ : BB.differential ∘ₗ Ψ - ε • (Ψ ∘ₗ dM) = f.linearPart ∘ₗ Φ) :
    f.linearPart ∘ₗ c.solveLeft Φ Ψ +
      (BB.differential ∘ₗ c.solveRight Φ Ψ + ε • (c.solveRight Φ Ψ ∘ₗ dM)) = Ψ :=
  LinearMap.ext fun m ↦ by
    let r := c.obstructionResidual Φ Ψ
    have eres : BB.differential (r m) = ε • r (dM m) := by
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply]
        using LinearMap.congr_fun (c.differential_comp_obstructionResidual dM ε hΦ hΨ) m
    have er : BB.differential (c.rightHomotopy (r m)) + c.rightHomotopy (BB.differential (r m)) =
        f.linearPart (c.inv (r m)) - r m := by
      simpa only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.id_apply]
        using (LinearMap.congr_fun c.linearPart_comp_inv_sub_id (r m)).symm
    have e₁ : (f.linearPart ∘ₗ c.solveLeft Φ Ψ) m =
        f.linearPart (c.obstructionTrial Φ Ψ m) + f.linearPart (c.inv (r m)) := by
      simp only [solveLeft, LinearMap.comp_apply, LinearMap.add_apply, map_add, r]
    have e₂ : (BB.differential ∘ₗ c.solveRight Φ Ψ + ε • (c.solveRight Φ Ψ ∘ₗ dM)) m =
        -(BB.differential (c.rightHomotopy (r m)) + c.rightHomotopy (BB.differential (r m))) := by
      simp only [solveRight, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.neg_apply, map_neg, smul_neg, r]
      rw [← map_units_smul c.rightHomotopy, ← eres, neg_add]
    rw [LinearMap.add_apply, e₁, e₂, er]
    simp only [r, obstructionResidual, LinearMap.sub_apply, LinearMap.comp_apply]
    abel

private theorem isHomogeneous_solveLeft (c : f.LinearHomotopyInverse)
    {GM : ℤ → Submodule R M} {p : ℤ} {Φ : M →ₗ[R] A} {Ψ : M →ₗ[R] B}
    (hΦ : LinearMap.IsHomogeneous Φ GM (AA.grading.shift 1).piece (p + 1))
    (hΨ : LinearMap.IsHomogeneous Ψ GM (BB.grading.shift 1).piece p) :
    LinearMap.IsHomogeneous (c.solveLeft Φ Ψ) GM (AA.grading.shift 1).piece p ∧
      LinearMap.IsHomogeneous (c.obstructionResidual Φ Ψ) GM (BB.grading.shift 1).piece p := by
  have hinv := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 c.isHomogeneous_inv
  have hlH := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 c.isHomogeneous_leftHomotopy
  have hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  have ht₁ : LinearMap.IsHomogeneous (c.inv ∘ₗ Ψ) GM (AA.grading.shift 1).piece p := by
    simpa only [add_zero] using hinv.comp hΨ
  have ht₂ : LinearMap.IsHomogeneous (c.leftHomotopy ∘ₗ Φ) GM (AA.grading.shift 1).piece p := by
    simpa only [add_neg_cancel_right] using hlH.comp hΦ
  have htrial : LinearMap.IsHomogeneous (c.obstructionTrial Φ Ψ) GM (AA.grading.shift 1).piece p :=
    ht₁.sub ht₂
  have hf₁t : LinearMap.IsHomogeneous (f.linearPart ∘ₗ c.obstructionTrial Φ Ψ)
      GM (BB.grading.shift 1).piece p := by
    simpa only [add_zero] using hf₁.comp htrial
  have hres : LinearMap.IsHomogeneous (c.obstructionResidual Φ Ψ) GM (BB.grading.shift 1).piece p :=
    hΨ.sub hf₁t
  have hinv_res : LinearMap.IsHomogeneous (c.inv ∘ₗ c.obstructionResidual Φ Ψ)
      GM (AA.grading.shift 1).piece p := by
    simpa only [add_zero] using hinv.comp hres
  exact ⟨htrial.add hinv_res, hres⟩

private theorem isHomogeneous_solveRight (c : f.LinearHomotopyInverse)
    {GM : ℤ → Submodule R M} {q : ℤ} {Φ : M →ₗ[R] A} {Ψ : M →ₗ[R] B}
    (hΦ : LinearMap.IsHomogeneous Φ GM (AA.grading.shift 1).piece ((q + 1) + 1))
    (hΨ : LinearMap.IsHomogeneous Ψ GM (BB.grading.shift 1).piece (q + 1)) :
    LinearMap.IsHomogeneous (c.solveRight Φ Ψ) GM (BB.grading.shift 1).piece q := by
  have hrH := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 c.isHomogeneous_rightHomotopy
  have hcomp : LinearMap.IsHomogeneous (c.rightHomotopy ∘ₗ c.obstructionResidual Φ Ψ)
      GM (BB.grading.shift 1).piece q := by
    simpa only [add_neg_cancel_right] using hrH.comp (c.isHomogeneous_solveLeft hΦ hΨ).2
  exact hcomp.neg

/-- **Coupled linear obstruction solver.**  Given a graded chain-homotopy inverse `c` of
`f.linearPart`, a module `M` with grading `GM`, an endomorphism `dM`, a sign `ε : ℤˣ`, and
homogeneous linear maps `Φ : M →ₗ[R] A` and `Ψ : M →ₗ[R] B` satisfying `m₁ ∘ Φ + ε • (Φ ∘ dM) = 0`
and `m₁ ∘ Ψ - ε • (Ψ ∘ dM) = f₁ ∘ Φ`, there exist homogeneous linear maps `ξ : M →ₗ[R] A` and
`η : M →ₗ[R] B` vanishing wherever both `Φ` and `Ψ` vanish and solving
`m₁ ∘ ξ - ε • (ξ ∘ dM) = Φ` and `f₁ ∘ ξ + (m₁ ∘ η + ε • (η ∘ dM)) = Ψ`. -/
theorem exists_relative_coboundary (c : f.LinearHomotopyInverse)
    {GM : ℤ → Submodule R M} (dM : Module.End R M) (ε : ℤˣ) {q : ℤ}
    {Φ : M →ₗ[R] A} {Ψ : M →ₗ[R] B}
    (hΦ_hom : LinearMap.IsHomogeneous Φ GM (AA.grading.shift 1).piece ((q + 1) + 1))
    (hΨ_hom : LinearMap.IsHomogeneous Ψ GM (BB.grading.shift 1).piece (q + 1))
    (hΦ : AA.differential ∘ₗ Φ + ε • (Φ ∘ₗ dM) = 0)
    (hΨ : BB.differential ∘ₗ Ψ - ε • (Ψ ∘ₗ dM) = f.linearPart ∘ₗ Φ) :
    ∃ (ξ : M →ₗ[R] A) (η : M →ₗ[R] B),
      LinearMap.IsHomogeneous ξ GM (AA.grading.shift 1).piece (q + 1) ∧
      LinearMap.IsHomogeneous η GM (BB.grading.shift 1).piece q ∧
      (∀ m, Φ m = 0 → Ψ m = 0 → ξ m = 0 ∧ η m = 0) ∧
      AA.differential ∘ₗ ξ - ε • (ξ ∘ₗ dM) = Φ ∧
      f.linearPart ∘ₗ ξ + (BB.differential ∘ₗ η + ε • (η ∘ₗ dM)) = Ψ :=
  ⟨c.solveLeft Φ Ψ, c.solveRight Φ Ψ,
    (c.isHomogeneous_solveLeft hΦ_hom hΨ_hom).1,
    c.isHomogeneous_solveRight hΦ_hom hΨ_hom,
    fun m hmΦ hmΨ ↦ by
      have ht : c.obstructionTrial Φ Ψ m = 0 := by
        simp only [obstructionTrial, LinearMap.sub_apply, LinearMap.comp_apply, hmΦ, hmΨ,
          map_zero, sub_self]
      have hr : c.obstructionResidual Φ Ψ m = 0 := by
        simp only [obstructionResidual, LinearMap.sub_apply, LinearMap.comp_apply, hmΨ, ht,
          map_zero, sub_self]
      exact ⟨by simp only [solveLeft, LinearMap.add_apply, LinearMap.comp_apply, ht, hr,
          map_zero, add_zero],
        by simp only [solveRight, LinearMap.neg_apply, LinearMap.comp_apply, hr, map_zero,
          neg_zero]⟩,
    c.solveLeft_spec dM ε hΦ hΨ,
    c.solveRight_spec dM ε hΦ hΨ⟩

end ObstructionSolver

/-! ### Relative cocycle lifting on reduced transformations -/

section TransformationLifting

variable {f : AInfinityHom AA BB} {u v : AInfinityHom CC AA}

private theorem liftStep_closed_top {q : ℤ} {n : ℕ}
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    (hD_closed : reducedTransformationDifferential u v ((q + 1) + 1) D = 0)
    (hD_van : ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor D z = 0) :
    AA.differential ∘ₗ
        (reducedTransformationCochains.taylor D ∘ₗ
          ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩) +
      (q + 1).negOnePow •
        ((reducedTransformationCochains.taylor D ∘ₗ
            ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩) ∘ₗ
          CC.unaryBarDifferential) = 0 := by
  have h0 := congrArg reducedTransformationCochains.taylor hD_closed
  rw [reducedTransformationCochains.taylor_reducedTransformationDifferential,
    reducedTransformationCochains.taylor_zero, Int.negOnePow_succ, Units.neg_smul,
    sub_neg_eq_add] at h0
  refine LinearMap.ext fun z ↦ ?_
  have hz := ReducedTensorWords.lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ z
  have hPz := LinearMap.congr_fun h0 (ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩ z)
  rw [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.comp_apply,
    reducedTransformationCochains.apply_eq_ofLetter_of_mem_filtration_succ hD_van hz,
    AA.taylor_ofLetter, ← AA.differential_apply,
    CC.apply_barDifferential_lengthProj hD_van z] at hPz
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.zero_apply] using hPz

private theorem liftStep_rel_top {q : ℤ} {n : ℕ}
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    {K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)}
    (hK_rel : reducedTransformationDifferential (f.comp u) (f.comp v) (q + 1) K =
      reducedTransformationCochains.compRight f ((q + 1) + 1) D)
    (hD_van : ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor D z = 0)
    (hK_van : ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor K z = 0) :
    BB.differential ∘ₗ
        (reducedTransformationCochains.taylor K ∘ₗ
          ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩) -
      (q + 1).negOnePow •
        ((reducedTransformationCochains.taylor K ∘ₗ
            ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩) ∘ₗ
          CC.unaryBarDifferential) =
      f.linearPart ∘ₗ
        (reducedTransformationCochains.taylor D ∘ₗ
          ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩) := by
  have h0 := congrArg reducedTransformationCochains.taylor hK_rel
  rw [reducedTransformationCochains.taylor_reducedTransformationDifferential,
    reducedTransformationCochains.taylor_compRight] at h0
  refine LinearMap.ext fun z ↦ ?_
  have hz := ReducedTensorWords.lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ z
  have hPz := LinearMap.congr_fun h0 (ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩ z)
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.comp_apply,
    reducedTransformationCochains.apply_eq_ofLetter_of_mem_filtration_succ hK_van hz,
    reducedTransformationCochains.apply_eq_ofLetter_of_mem_filtration_succ hD_van hz,
    BB.taylor_ofLetter, ← BB.differential_apply, ← linearPart_apply,
    CC.apply_barDifferential_lengthProj hK_van z] at hPz
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] using hPz

private structure LiftStage (f : AInfinityHom AA BB) (q : ℤ)
    (D : reducedTransformationCochains u v ((q + 1) + 1))
    (K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)) (n : ℕ) where
  L : reducedTransformationCochains u v (q + 1)
  M : reducedTransformationCochains (f.comp u) (f.comp v) q
  diff_eq : ∀ z ∈ ReducedTensorWords.filtration R C n,
    reducedTransformationCochains.taylor (reducedTransformationDifferential u v (q + 1) L) z =
      reducedTransformationCochains.taylor D z
  rel_eq : ∀ z ∈ ReducedTensorWords.filtration R C n,
    reducedTransformationCochains.taylor
        (reducedTransformationCochains.compRight f (q + 1) L +
          reducedTransformationDifferential (f.comp u) (f.comp v) q M) z =
      reducedTransformationCochains.taylor K z

private noncomputable def liftStageZero (f : AInfinityHom AA BB) (q : ℤ)
    (D : reducedTransformationCochains u v ((q + 1) + 1))
    (K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)) :
    LiftStage f q D K 0 where
  L := 0
  M := 0
  diff_eq z hz := by
    rw [ReducedTensorWords.filtration_zero, Submodule.mem_bot] at hz
    rw [hz, map_zero, map_zero]
  rel_eq z hz := by
    rw [ReducedTensorWords.filtration_zero, Submodule.mem_bot] at hz
    rw [hz, map_zero, map_zero]

private noncomputable def LiftStage.resD {q : ℤ} {n : ℕ}
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    {K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)}
    (s : LiftStage f q D K n) : reducedTransformationCochains u v ((q + 1) + 1) :=
  D - reducedTransformationDifferential u v (q + 1) s.L

private noncomputable def LiftStage.resK {q : ℤ} {n : ℕ}
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    {K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)}
    (s : LiftStage f q D K n) : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1) :=
  K - (reducedTransformationCochains.compRight f (q + 1) s.L +
    reducedTransformationDifferential (f.comp u) (f.comp v) q s.M)

private theorem LiftStage.res_closed_and_rel {q : ℤ} {n : ℕ}
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    {K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)}
    (hD : reducedTransformationDifferential u v ((q + 1) + 1) D = 0)
    (hK : reducedTransformationDifferential (f.comp u) (f.comp v) (q + 1) K =
      reducedTransformationCochains.compRight f ((q + 1) + 1) D)
    (s : LiftStage f q D K n) :
    reducedTransformationDifferential u v ((q + 1) + 1) s.resD = 0 ∧
      reducedTransformationDifferential (f.comp u) (f.comp v) (q + 1) s.resK =
        reducedTransformationCochains.compRight f ((q + 1) + 1) s.resD :=
  ⟨by rw [resD, map_sub, hD, reducedTransformationDifferential_reducedTransformationDifferential,
        sub_zero],
    by rw [resK, resD, map_sub, map_add, hK, reducedTransformationDifferential_compRight,
         reducedTransformationDifferential_reducedTransformationDifferential, add_zero, map_sub]⟩

private theorem LiftStage.res_vanish {q : ℤ} {n : ℕ}
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    {K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)}
    (s : LiftStage f q D K n) :
    (∀ w ∈ ReducedTensorWords.filtration R C n, reducedTransformationCochains.taylor s.resD w = 0) ∧
      (∀ w ∈ ReducedTensorWords.filtration R C n,
        reducedTransformationCochains.taylor s.resK w = 0) :=
  ⟨fun w hw ↦ by
      rw [resD, reducedTransformationCochains.taylor_sub, LinearMap.sub_apply, s.diff_eq w hw,
        sub_self],
    fun w hw ↦ by
      rw [resK, reducedTransformationCochains.taylor_sub, LinearMap.sub_apply, s.rel_eq w hw,
        sub_self]⟩

private theorem taylor_reducedTransformationDifferential_apply_of_mem_filtration_succ
    {X : Type*} [AddCommGroup X] [Module R X] {XX : AInfinityAlgebra R X}
    {g₁ g₂ : AInfinityHom CC XX} {p : ℤ} {n : ℕ}
    {W : reducedTransformationCochains g₁ g₂ p}
    (hW : ∀ w ∈ ReducedTensorWords.filtration R C n, reducedTransformationCochains.taylor W w = 0)
    {z : ReducedTensorWords R C} (hz : z ∈ ReducedTensorWords.filtration R C (n + 1)) :
    reducedTransformationCochains.taylor (reducedTransformationDifferential g₁ g₂ p W) z =
      XX.differential (reducedTransformationCochains.taylor W z) -
        p.negOnePow • reducedTransformationCochains.taylor W (CC.unaryBarDifferential z) := by
  rw [reducedTransformationCochains.taylor_reducedTransformationDifferential, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    reducedTransformationCochains.apply_eq_ofLetter_of_mem_filtration_succ hW hz,
    XX.taylor_ofLetter, ← XX.differential_apply,
    CC.apply_barDifferential_of_mem_filtration_succ hW hz]

private theorem exists_liftStepDelta (c : f.LinearHomotopyInverse) {q : ℤ} {n : ℕ}
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    {K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)}
    (hD : reducedTransformationDifferential u v ((q + 1) + 1) D = 0)
    (hK : reducedTransformationDifferential (f.comp u) (f.comp v) (q + 1) K =
      reducedTransformationCochains.compRight f ((q + 1) + 1) D)
    (s : LiftStage f q D K n) :
    ∃ (ΔL : reducedTransformationCochains u v (q + 1))
      (ΔM : reducedTransformationCochains (f.comp u) (f.comp v) q),
      (∀ w ∈ ReducedTensorWords.filtration R C n,
        reducedTransformationCochains.taylor ΔL w = 0 ∧
          reducedTransformationCochains.taylor ΔM w = 0) ∧
      (∀ z ∈ ReducedTensorWords.filtration R C (n + 1),
        reducedTransformationCochains.taylor
            (reducedTransformationDifferential u v (q + 1) ΔL) z =
          reducedTransformationCochains.taylor s.resD z) ∧
      (∀ z ∈ ReducedTensorWords.filtration R C (n + 1),
        reducedTransformationCochains.taylor
            (reducedTransformationCochains.compRight f (q + 1) ΔL +
              reducedTransformationDifferential (f.comp u) (f.comp v) q ΔM) z =
          reducedTransformationCochains.taylor s.resK z) := by
  have hP := ReducedTensorWords.isHomogeneous_lengthProj (CC.grading.shift 1) ⟨n + 1, n.succ_pos⟩
  have hΦ_hom := LinearMap.IsHomogeneous.comp
    (reducedTransformationCochains.isHomogeneous_taylor s.resD) hP
  have hΨ_hom := LinearMap.IsHomogeneous.comp
    (reducedTransformationCochains.isHomogeneous_taylor s.resK) hP
  rw [zero_add] at hΦ_hom hΨ_hom
  obtain ⟨ξ, η, hξ_hom, hη_hom, hvan, hξ_eq, hη_eq⟩ :=
    c.exists_relative_coboundary CC.unaryBarDifferential (q + 1).negOnePow hΦ_hom hΨ_hom
      (liftStep_closed_top (s.res_closed_and_rel hD hK).1 s.res_vanish.1)
      (liftStep_rel_top (s.res_closed_and_rel hD hK).2 s.res_vanish.1 s.res_vanish.2)
  let ΔL := reducedTransformationCochains.ofTaylor u v hξ_hom
  let ΔM := reducedTransformationCochains.ofTaylor (f.comp u) (f.comp v) hη_hom
  have hvan_fil : ∀ w ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor ΔL w = 0 ∧
        reducedTransformationCochains.taylor ΔM w = 0 := fun w hw ↦ by
    have hPw := ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R C
      (n := ⟨n + 1, n.succ_pos⟩) n.lt_succ_self hw
    rw [reducedTransformationCochains.taylor_ofTaylor,
      reducedTransformationCochains.taylor_ofTaylor]
    exact hvan w (by rw [LinearMap.comp_apply, hPw, map_zero])
      (by rw [LinearMap.comp_apply, hPw, map_zero])
  refine ⟨ΔL, ΔM, hvan_fil, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [taylor_reducedTransformationDifferential_apply_of_mem_filtration_succ
      (fun w hw ↦ (hvan_fil w hw).1) hz, reducedTransformationCochains.taylor_ofTaylor]
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      ReducedTensorWords.apply_lengthProj_of_mem_filtration R C s.res_vanish.1 hz]
      using LinearMap.congr_fun hξ_eq z
  · have hsign : q.negOnePow = -(q + 1).negOnePow := by rw [Int.negOnePow_succ, neg_neg]
    rw [reducedTransformationCochains.taylor_add, LinearMap.add_apply,
      reducedTransformationCochains.taylor_compRight, LinearMap.comp_apply,
      reducedTransformationCochains.apply_eq_ofLetter_of_mem_filtration_succ
        (fun w hw ↦ (hvan_fil w hw).1) hz, ← linearPart_apply,
      taylor_reducedTransformationDifferential_apply_of_mem_filtration_succ
        (fun w hw ↦ (hvan_fil w hw).2) hz,
      hsign, Units.neg_smul, sub_neg_eq_add,
      reducedTransformationCochains.taylor_ofTaylor,
      reducedTransformationCochains.taylor_ofTaylor]
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      ReducedTensorWords.apply_lengthProj_of_mem_filtration R C s.res_vanish.2 hz]
      using LinearMap.congr_fun hη_eq z

private noncomputable def liftStageSucc (c : f.LinearHomotopyInverse) {q : ℤ} {n : ℕ}
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    {K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)}
    (hD : reducedTransformationDifferential u v ((q + 1) + 1) D = 0)
    (hK : reducedTransformationDifferential (f.comp u) (f.comp v) (q + 1) K =
      reducedTransformationCochains.compRight f ((q + 1) + 1) D)
    (s : LiftStage f q D K n) :
    { s' : LiftStage f q D K (n + 1) //
      ∀ w ∈ ReducedTensorWords.filtration R C n,
        reducedTransformationCochains.taylor s'.L w =
          reducedTransformationCochains.taylor s.L w ∧
        reducedTransformationCochains.taylor s'.M w =
          reducedTransformationCochains.taylor s.M w } := by
  let hex := c.exists_liftStepDelta hD hK s
  let ΔL := hex.choose
  let ΔM := hex.choose_spec.choose
  have hΔ := hex.choose_spec.choose_spec
  refine ⟨⟨s.L + ΔL, s.M + ΔM, fun z hz ↦ ?_, fun z hz ↦ ?_⟩, fun w hw ↦ ?_⟩
  · rw [map_add, reducedTransformationCochains.taylor_add, LinearMap.add_apply, hΔ.2.1 z hz,
      LiftStage.resD, reducedTransformationCochains.taylor_sub, LinearMap.sub_apply,
      add_sub_cancel]
  · have hlin : reducedTransformationCochains.compRight f (q + 1) (s.L + ΔL) +
        reducedTransformationDifferential (f.comp u) (f.comp v) q (s.M + ΔM) =
      (reducedTransformationCochains.compRight f (q + 1) s.L +
          reducedTransformationDifferential (f.comp u) (f.comp v) q s.M) +
        (reducedTransformationCochains.compRight f (q + 1) ΔL +
          reducedTransformationDifferential (f.comp u) (f.comp v) q ΔM) := by
      rw [map_add, map_add]
      abel
    rw [hlin, reducedTransformationCochains.taylor_add, LinearMap.add_apply, hΔ.2.2 z hz,
      LiftStage.resK, reducedTransformationCochains.taylor_sub, LinearMap.sub_apply,
      add_sub_cancel]
  · exact ⟨by rw [reducedTransformationCochains.taylor_add, LinearMap.add_apply,
        (hΔ.1 w hw).1, add_zero],
      by rw [reducedTransformationCochains.taylor_add, LinearMap.add_apply,
        (hΔ.1 w hw).2, add_zero]⟩

private noncomputable def liftStageSeq (c : f.LinearHomotopyInverse) {q : ℤ}
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    {K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)}
    (hD : reducedTransformationDifferential u v ((q + 1) + 1) D = 0)
    (hK : reducedTransformationDifferential (f.comp u) (f.comp v) (q + 1) K =
      reducedTransformationCochains.compRight f ((q + 1) + 1) D) :
    ∀ n : ℕ, LiftStage f q D K n
  | 0 => liftStageZero f q D K
  | n + 1 => (c.liftStageSucc hD hK (c.liftStageSeq hD hK n)).1

/-- **Relative cocycle lifting on reduced transformations.**  If `f.linearPart` admits a graded
chain-homotopy inverse `c`, then for any morphisms `u v : C ⟶ A`, any closed transformation `D` of
degree `(q + 1) + 1` from `u` to `v`, and any transformation `K` of degree `q + 1` from `f ∘ u` to
`f ∘ v` bounding `compRight f D`, there exist transformations `L` of degree `q + 1` from `u` to `v`
and `M` of degree `q` from `f ∘ u` to `f ∘ v` with `δ L = D` and `compRight f L + δ M = K`. -/
theorem exists_reducedTransformationCochains_compRight (c : f.LinearHomotopyInverse) (q : ℤ)
    {D : reducedTransformationCochains u v ((q + 1) + 1)}
    {K : reducedTransformationCochains (f.comp u) (f.comp v) (q + 1)}
    (hD : reducedTransformationDifferential u v ((q + 1) + 1) D = 0)
    (hK : reducedTransformationDifferential (f.comp u) (f.comp v) (q + 1) K =
      reducedTransformationCochains.compRight f ((q + 1) + 1) D) :
    ∃ (L : reducedTransformationCochains u v (q + 1))
      (M : reducedTransformationCochains (f.comp u) (f.comp v) q),
      reducedTransformationDifferential u v (q + 1) L = D ∧
        reducedTransformationCochains.compRight f (q + 1) L +
          reducedTransformationDifferential (f.comp u) (f.comp v) q M = K := by
  let S := c.liftStageSeq hD hK
  let SL : ℕ → reducedTransformationCochains u v (q + 1) := fun n ↦ (S n).L
  let SM : ℕ → reducedTransformationCochains (f.comp u) (f.comp v) q := fun n ↦ (S n).M
  have hSL : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor (SL (n + 1)) z =
        reducedTransformationCochains.taylor (SL n) z :=
    fun n z hz ↦ ((c.liftStageSucc hD hK (S n)).2 z hz).1
  have hSM : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor (SM (n + 1)) z =
        reducedTransformationCochains.taylor (SM n) z :=
    fun n z hz ↦ ((c.liftStageSucc hD hK (S n)).2 z hz).2
  refine ⟨reducedTransformationCochains.filtrationLimit hSL,
    reducedTransformationCochains.filtrationLimit hSM,
    reducedTransformationCochains.ext ?_, reducedTransformationCochains.ext ?_⟩
  · refine LinearMap.ext fun z ↦ ?_
    obtain ⟨k, hz⟩ := ReducedTensorWords.exists_mem_filtration R C z
    rw [← (S k).diff_eq _ hz,
      reducedTransformationCochains.taylor_reducedTransformationDifferential,
      reducedTransformationCochains.taylor_reducedTransformationDifferential,
      LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      reducedTransformationCochains.coe_filtrationLimit_apply_of_mem_filtration hSL hz,
      reducedTransformationCochains.taylor_filtrationLimit_apply_of_mem_filtration hSL
        (CC.barDifferential_mem_filtration hz)]
  · refine LinearMap.ext fun z ↦ ?_
    obtain ⟨k, hz⟩ := ReducedTensorWords.exists_mem_filtration R C z
    rw [← (S k).rel_eq _ hz,
      reducedTransformationCochains.taylor_add, reducedTransformationCochains.taylor_add,
      LinearMap.add_apply, LinearMap.add_apply,
      reducedTransformationCochains.taylor_compRight,
      reducedTransformationCochains.taylor_compRight,
      reducedTransformationCochains.taylor_reducedTransformationDifferential,
      reducedTransformationCochains.taylor_reducedTransformationDifferential,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.comp_apply,
      reducedTransformationCochains.coe_filtrationLimit_apply_of_mem_filtration hSL hz,
      reducedTransformationCochains.coe_filtrationLimit_apply_of_mem_filtration hSM hz,
      reducedTransformationCochains.taylor_filtrationLimit_apply_of_mem_filtration hSM
        (CC.barDifferential_mem_filtration hz)]

/-- Lift a homotopy `h : Homotopy (f.comp u) (f.comp v)` across `f` to a homotopy from `u` to
`v`. -/
noncomputable def liftHomotopy (c : f.LinearHomotopyInverse)
    (h : Homotopy (f.comp u) (f.comp v)) : Homotopy u v :=
  let hD : reducedTransformationDifferential u v ((-2 + 1) + 1)
      ⟨u.barMap - v.barMap, barMap_sub_barMap_mem_reducedTransformationCochains u v⟩ = 0 :=
    reducedTransformationDifferential_barMap_sub_barMap u v
  let hK : reducedTransformationDifferential (f.comp u) (f.comp v) (-2 + 1)
      (Homotopy.equivCochains h).1 =
      reducedTransformationCochains.compRight f ((-2 + 1) + 1)
        ⟨u.barMap - v.barMap, barMap_sub_barMap_mem_reducedTransformationCochains u v⟩ := by
    apply Subtype.ext
    change (((f.comp u).reducedTransformationDifferential (f.comp v) (-1)
      (Homotopy.equivCochains h).1 :
        ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B)) = _
    rw [(Homotopy.equivCochains h).2, reducedTransformationCochains.coe_compRight, Submodule.coe_mk,
      LinearMap.comp_sub, barMap_comp, barMap_comp]
  let hex := c.exists_reducedTransformationCochains_compRight (-2) hD hK
  Homotopy.equivCochains.symm ⟨hex.choose, congrArg Subtype.val hex.choose_spec.choose_spec.1⟩

/-- Postcomposing with `f` reflects and preserves the existence of a homotopy between morphisms
into `AA`. -/
theorem nonempty_homotopy_comp_left_iff (c : f.LinearHomotopyInverse) (u v : AInfinityHom CC AA) :
    Nonempty (Homotopy (f.comp u) (f.comp v)) ↔ Nonempty (Homotopy u v) :=
  ⟨fun ⟨h⟩ ↦ ⟨c.liftHomotopy h⟩, fun ⟨h⟩ ↦ ⟨h.compRight f⟩⟩

end TransformationLifting

end LinearHomotopyInverse

end AInfinityHom

end TauCeti
