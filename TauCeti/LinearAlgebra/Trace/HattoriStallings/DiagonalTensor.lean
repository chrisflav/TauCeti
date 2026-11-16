/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import TauCeti.LinearAlgebra.Trace.HattoriStallings.MonoidExtension

/-!
# Diagonal Tensor Products for Group-Ring Hattori–Stallings Traces

This module develops the diagonal tensor product `M ⊗[A] P` of a `Λ[Γ]`-module `M` and an
`A[Γ]`-module `P` over a commutative ring `A` with an `A`-algebra `Λ` (possibly noncommutative),
and proves the multiplicativity identities for centralizer traces and coinvariant traces
(Stacks §64.15, Lemmas 64.15.7–64.15.8).

## Main definitions

* `MonoidAlgebra.DiagonalTensor A Λ P M`: wrapper around `M ⊗[A] P` carrying the left `Λ`-module
  structure (acting on `M`, definitionally compatible with `Module ℤ`) and the diagonal
  `MonoidAlgebra Λ Γ`-module structure
  `single γ a • (m ⊗ₜ p) = (single γ a • m) ⊗ₜ (single γ 1 • p)`.
* `TauCeti.MonoidExtension.hattoriStallingsTraceClass` and
  `TauCeti.MonoidExtension.projectiveTraceClass`: the `G`-conjugacy-class-invariant trace of a
  degree-`n` element acting on a finite projective `Λ`-module `M`.

## Main theorems

* `MonoidAlgebra.DiagonalTensor.finite_projective`: if `P` is finite projective over `A[G]` and
  `M` is finite projective over `Λ` (without assuming `M` is projective over `A` or `G` is finite),
  then `DiagonalTensor A Λ P M` is finite projective over `Λ[G]`.
* `LinearMap.centralizerTrace_diagonalTensor` (Stacks Lemma 64.15.7):
  `centralizerTrace Λ ι γ (DiagonalTensor A Λ P M) hDG =
    cyclicQuotientSMul A Λ (centralizerScalarTrace A ι γ P hPG)
      (hattoriStallingsTrace Λ M (singleSMulEnd Λ γ M))`.
* `TauCeti.MonoidExtension.hattoriStallingsTrace_coinvariantsAction_diagonalTensor`
  (Stacks Lemma 64.15.8):
  `hattoriStallingsTrace Λ (Coinvariants Λ G (DiagonalTensor A Λ P M)) (E.coinvariantsAction ...) =
    ∑ᶠ c : E.ConjClasses n,
      cyclicQuotientSMul A Λ (E.centralizerScalarTraceClass A n P hPG c)
        (E.hattoriStallingsTraceClass Λ n M c)`.

## References

* [Stacks Project, Tag 03UB (Lemma 64.15.7)](https://stacks.math.columbia.edu/tag/03UB)
* [Stacks Project, Tag 03UC (Lemma 64.15.8)](https://stacks.math.columbia.edu/tag/03UC)
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace MonoidAlgebra

/-! ### Section 1: Diagonal tensor products over group and monoid algebras -/

/-- Wrapper around `M ⊗[A] P` carrying the left `Λ`-module structure (on `M`) and the diagonal
`MonoidAlgebra Λ Γ`-action `single γ a • (m ⊗ₜ p) = (single γ a • m) ⊗ₜ (single γ 1 • p)`.
Parameterizing by `Λ` ensures the left `Λ`-module instance never clashes with the diagonal
`MonoidAlgebra Λ Γ`-module instance. -/
structure DiagonalTensor (A Λ : Type*) [CommRing A] [Ring Λ] [Algebra A Λ]
    (P M : Type*) [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M] where
  /-- The underlying tensor product element in `M ⊗[A] P`. -/
  val : M ⊗[A] P

namespace DiagonalTensor

variable {A Λ : Type*} [CommRing A] [Ring Λ] [Algebra A Λ]
variable {P M : Type*} [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M]

@[ext]
theorem ext {x y : DiagonalTensor A Λ P M} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  congr

/-- Pure tensor constructor `m ⊗ₜ p` in `DiagonalTensor A Λ P M`. -/
def tmul (m : M) (p : P) : DiagonalTensor A Λ P M :=
  ⟨m ⊗ₜ[A] p⟩

@[simp]
theorem val_tmul (m : M) (p : P) : (tmul (A := A) (Λ := Λ) m p).val = m ⊗ₜ[A] p :=
  (rfl)

instance instAddCommGroup : AddCommGroup (DiagonalTensor A Λ P M) where
  add x y := ⟨x.val + y.val⟩
  zero := ⟨0⟩
  neg x := ⟨-x.val⟩
  sub x y := ⟨x.val - y.val⟩
  nsmul n x := ⟨n • x.val⟩
  zsmul n x := ⟨n • x.val⟩
  add_assoc x y z := ext (add_assoc x.val y.val z.val)
  zero_add x := ext (zero_add x.val)
  add_zero x := ext (add_zero x.val)
  add_comm x y := ext (add_comm x.val y.val)
  neg_add_cancel x := ext (neg_add_cancel x.val)
  sub_eq_add_neg x y := ext (sub_eq_add_neg x.val y.val)
  nsmul_zero x := ext (AddMonoid.nsmul_zero x.val)
  nsmul_succ n x := ext (AddMonoid.nsmul_succ n x.val)
  zsmul_zero' x := ext (SubNegMonoid.zsmul_zero' x.val)
  zsmul_succ' n x := ext (SubNegMonoid.zsmul_succ' n x.val)
  zsmul_neg' n x := ext (SubNegMonoid.zsmul_neg' n x.val)

@[simp]
theorem val_zero : (0 : DiagonalTensor A Λ P M).val = 0 :=
  (rfl)

@[simp]
theorem val_add (x y : DiagonalTensor A Λ P M) : (x + y).val = x.val + y.val :=
  (rfl)

@[simp]
theorem val_neg (x : DiagonalTensor A Λ P M) : (-x).val = -x.val :=
  (rfl)

@[simp]
theorem val_sub (x y : DiagonalTensor A Λ P M) : (x - y).val = x.val - y.val :=
  (rfl)

@[simp]
theorem val_sum {ι : Type*} (s : Finset ι) (f : ι → DiagonalTensor A Λ P M) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

@[simp]
theorem zero_tmul (p : P) : tmul (A := A) (Λ := Λ) (0 : M) p = 0 :=
  ext (TensorProduct.zero_tmul (R := A) M p)

@[simp]
theorem tmul_zero (m : M) : tmul (A := A) (Λ := Λ) m (0 : P) = 0 :=
  ext (TensorProduct.tmul_zero (R := A) P m)

theorem add_tmul (m₁ m₂ : M) (p : P) :
    tmul (A := A) (Λ := Λ) (m₁ + m₂) p = tmul m₁ p + tmul m₂ p :=
  ext (TensorProduct.add_tmul m₁ m₂ p)

theorem tmul_add (m : M) (p₁ p₂ : P) :
    tmul (A := A) (Λ := Λ) m (p₁ + p₂) = tmul m p₁ + tmul m p₂ :=
  ext (TensorProduct.tmul_add m p₁ p₂)

theorem smul_tmul (c : A) (m : M) (p : P) :
    tmul (A := A) (Λ := Λ) (c • m) p = tmul m (c • p) :=
  ext (TensorProduct.smul_tmul c m p)

/-- Induction principle for `DiagonalTensor A Λ P M` inherited from `TensorProduct.inductionOn`. -/
@[elab_as_elim]
theorem inductionOn {C : DiagonalTensor A Λ P M → Prop} (x : DiagonalTensor A Λ P M)
    (tmul : ∀ m p, C (tmul m p))
    (add : ∀ x y, C x → C y → C (x + y)) : C x := by
  rcases x with ⟨t⟩
  exact TensorProduct.inductionOn t tmul (fun u v hu hv ↦ add ⟨u⟩ ⟨v⟩ hu hv)

section LeftModule

variable [Module Λ M] [IsScalarTower A Λ M]

/-- Left `Λ`-module structure on `DiagonalTensor A Λ P M` acting on the left factor `M`.
When `Λ = ℤ`, this agrees definitionally with `AddCommGroup.toIntModule` because `zsmul` on
`M ⊗[A] P` is `TensorProduct.leftSMul`. -/
instance instModuleCoeff : Module Λ (DiagonalTensor A Λ P M) where
  smul r x := ⟨r • x.val⟩
  one_smul x := ext (one_smul Λ x.val)
  mul_smul r s x := ext (mul_smul r s x.val)
  smul_zero r := ext (smul_zero r)
  smul_add r x y := ext (smul_add r x.val y.val)
  add_smul r s x := ext (add_smul r s x.val)
  zero_smul x := ext (zero_smul Λ x.val)

@[simp]
theorem val_smul (r : Λ) (x : DiagonalTensor A Λ P M) : (r • x).val = r • x.val :=
  (rfl)

@[simp]
theorem smul_tmul' (r : Λ) (m : M) (p : P) :
    r • tmul (A := A) (Λ := Λ) m p = tmul (r • m) p :=
  (rfl)

end LeftModule

section DiagonalAction

variable {Γ : Type*} [Monoid Γ]
variable [Module (MonoidAlgebra A Γ) P] [IsScalarTower A (MonoidAlgebra A Γ) P]
variable [Module Λ M] [IsScalarTower A Λ M]
variable [Module (MonoidAlgebra Λ Γ) M] [IsScalarTower Λ (MonoidAlgebra Λ Γ) M]

/-- Left `Λ`-scalar multiplication packaged as a ring homomorphism into `Module.End ℤ`. -/
def coeffActionHom : Λ →+* Module.End ℤ (DiagonalTensor A Λ P M) where
  toFun r :=
    { toFun := fun x ↦ r • x
      map_add' := smul_add r
      map_smul' := fun n x ↦ by
        simp only [RingHom.id_apply, smul_comm n r x] }
  map_one' := by
    ext x
    simp
  map_mul' r s := by
    ext x
    simp [mul_smul]
  map_zero' := by
    ext x
    simp
  map_add' r s := by
    ext x
    simp [add_smul]

/-- Diagonal action of a monoid element `γ : Γ` packaged as a monoid homomorphism into
`Module.End ℤ`. -/
def monoidActionHom : Γ →* Module.End ℤ (DiagonalTensor A Λ P M) where
  toFun γ :=
    let fM : Module.End A M := (singleSMulEnd Λ γ M).restrictScalars A
    let fP : Module.End A P := singleSMulEnd A γ P
    let fT : Module.End A (M ⊗[A] P) := TensorProduct.map fM fP
    { toFun := fun x ↦ ⟨fT x.val⟩
      map_add' := fun x y ↦ ext (fT.map_add x.val y.val)
      map_smul' := fun n x ↦ ext (map_zsmul fT n x.val) }
  map_one' := by
    ext x
    refine inductionOn x ?_ ?_
    · intro m p
      simp [singleSMulEnd_one]
    · intro x y hx hy
      simp only [LinearMap.coe_mk, AddHom.coe_mk, val_add, map_add] at hx hy ⊢
      exact congrArg₂ (· + ·) hx hy
  map_mul' γ₁ γ₂ := by
    ext x
    refine inductionOn x ?_ ?_
    · intro m p
      simp [singleSMulEnd_mul]
    · intro x y hx hy
      simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_apply_eq_comp, val_add, map_add] at hx hy ⊢
      exact congrArg₂ (· + ·) hx hy

/-- Ring homomorphism `MonoidAlgebra Λ Γ →+* Module.End ℤ (DiagonalTensor A Λ P M)` defining the
diagonal `Λ[Γ]`-module structure. -/
def diagonalActionHom : MonoidAlgebra Λ Γ →+* Module.End ℤ (DiagonalTensor A Λ P M) :=
  liftNCRingHom (coeffActionHom (A := A) (Λ := Λ) (P := P) (M := M))
    (monoidActionHom (A := A) (Λ := Λ) (P := P) (M := M) (Γ := Γ)) fun r γ ↦ by
      ext x
      refine inductionOn x ?_ ?_
      · intro m p
        simp only [mul_apply_eq_comp, coeffActionHom, monoidActionHom, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, val_smul, val_tmul,
          TensorProduct.smul_tmul', TensorProduct.map_tmul, LinearMap.coe_restrictScalars,
          singleSMulEnd_apply]
        have hcomm : (single γ (1 : Λ) : MonoidAlgebra Λ Γ) • (r • m) =
            r • ((single γ (1 : Λ) : MonoidAlgebra Λ Γ) • m) := by
          simpa only [singleSMulEnd_apply] using (singleSMulEnd Λ γ M).map_smul r m
        rw [hcomm]
      · intro x y hx hy
        simp only [mul_apply_eq_comp, map_add, val_add] at hx hy ⊢
        exact congrArg₂ (· + ·) hx hy

/-- Diagonal `MonoidAlgebra Λ Γ`-module structure on `DiagonalTensor A Λ P M`. -/
instance instModuleMonoidAlgebra : Module (MonoidAlgebra Λ Γ) (DiagonalTensor A Λ P M) :=
  Module.compHom (DiagonalTensor A Λ P M)
    (diagonalActionHom (A := A) (Λ := Λ) (P := P) (M := M) (Γ := Γ))

@[simp]
theorem single_smul_tmul (γ : Γ) (a : Λ) (m : M) (p : P) :
    (single γ a : MonoidAlgebra Λ Γ) • tmul (A := A) (Λ := Λ) m p =
      tmul ((single γ a : MonoidAlgebra Λ Γ) • m)
        ((single γ (1 : A) : MonoidAlgebra A Γ) • p) := by
  change (diagonalActionHom (A := A) (Λ := Λ) (P := P) (M := M) (Γ := Γ) (single γ a))
      (tmul m p) = _
  rw [diagonalActionHom, liftNCRingHom_single]
  apply ext
  simp only [mul_apply_eq_comp, coeffActionHom, monoidActionHom, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, val_smul, val_tmul,
    TensorProduct.map_tmul, LinearMap.coe_restrictScalars, singleSMulEnd_apply]
  rw [TensorProduct.smul_tmul']
  congr 1
  have h1 : (single γ a : MonoidAlgebra Λ Γ) = a • single γ (1 : Λ) := by
    rw [smul_single, smul_eq_mul, mul_one]
  rw [h1, smul_assoc]

/-- Compatibility of left `Λ`-multiplication with the diagonal `Λ[Γ]`-action. -/
instance instIsScalarTower : IsScalarTower Λ (MonoidAlgebra Λ Γ) (DiagonalTensor A Λ P M) where
  smul_assoc r x t := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => simp [smul_add, add_smul, h₁, h₂]
    | single γ a =>
      refine inductionOn t ?_ ?_
      · intro m p
        rw [smul_single, single_smul_tmul, single_smul_tmul, smul_tmul', ← smul_single, smul_assoc]
      · intro u v hu hv
        simp only [smul_add, hu, hv]

end DiagonalAction

section MapDomainCompatibility

variable {G Γ : Type*} [Monoid G] [Monoid Γ]
variable [Module (MonoidAlgebra A Γ) P] [IsScalarTower A (MonoidAlgebra A Γ) P]
variable [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
variable [Module Λ M] [IsScalarTower A Λ M]
variable [Module (MonoidAlgebra Λ Γ) M] [IsScalarTower Λ (MonoidAlgebra Λ Γ) M]
variable [Module (MonoidAlgebra Λ G) M] [IsScalarTower Λ (MonoidAlgebra Λ G) M]

/-- Compatibility of the restricted `Λ[G]`-action and the ambient `Λ[Γ]`-action on
`DiagonalTensor A Λ P M` along any monoid homomorphism `ι : G →* Γ`. -/
theorem smul_eq_mapDomain (ι : G →* Γ)
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P), r • p = mapDomain ι r • p)
    (hMG : ∀ (r : MonoidAlgebra Λ G) (m : M), r • m = mapDomain ι r • m)
    (r : MonoidAlgebra Λ G) (x : DiagonalTensor A Λ P M) :
    r • x = mapDomain ι r • x := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r₁ r₂ h₁ h₂ => simp [add_smul, mapDomain_add, h₁, h₂]
  | single g a =>
    refine inductionOn x ?_ ?_
    · intro m p
      rw [mapDomain_single, single_smul_tmul, single_smul_tmul, hMG, hPG, mapDomain_single,
        mapDomain_single]
    · intro u v hu hv
      simp only [smul_add, hu, hv]

end MapDomainCompatibility

section FiniteProjective

variable {G : Type*} [Group G]
variable [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A G) P]
variable [Module Λ M] [IsScalarTower A Λ M]
variable [Module (MonoidAlgebra Λ G) M] [IsScalarTower Λ (MonoidAlgebra Λ G) M]

/-- Explicit `MonoidAlgebra Λ G`-linear inclusion
`DiagonalTensor A Λ P M →ₗ[Λ[G]] (Fin m × Fin k → Λ[G])` constructed from an `A[G]`-retract `iP`
of `P` and a `Λ`-retract `iM` of `M`, using the Frobenius untwisting formula
`(m ⊗ₜ p) ↦ ∑ g, single g (iM (single g⁻¹ 1 • (c_g • m)) l)`. -/
def retractIncl {m k : ℕ}
    (iP : P →ₗ[MonoidAlgebra A G] (Fin m → MonoidAlgebra A G))
    (iM : M →ₗ[Λ] (Fin k → Λ)) :
    DiagonalTensor A Λ P M →ₗ[MonoidAlgebra Λ G] (Fin m × Fin k → MonoidAlgebra Λ G) :=
  let bilin : M →ₗ[A] P →ₗ[A] (Fin m × Fin k → MonoidAlgebra Λ G) :=
    { toFun := fun x ↦
        { toFun := fun p jl ↦
            (iP p jl.1).coeff.sum fun g c ↦
              single g (iM ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • (c • x)) jl.2)
          map_add' := fun p₁ p₂ ↦ funext fun jl ↦ by
            rw [map_add, Pi.add_apply, coeff_add]
            exact Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g c₁ c₂ ↦ by
              simp only [add_smul, smul_add, map_add, Pi.add_apply, single_add])
          map_smul' := fun a p ↦ funext fun jl ↦ by
            rw [RingHom.id_apply, Pi.smul_apply]
            have hsmul : iP (a • p) jl.1 = a • iP p jl.1 := by
              rw [← algebraMap_smul (MonoidAlgebra A G) a p, iP.map_smul, Pi.smul_apply,
                algebraMap_smul]
            rw [hsmul]
            generalize iP p jl.1 = u
            induction u using MonoidAlgebra.induction_linear with
            | zero => simp
            | add u₁ u₂ hu₁ hu₂ =>
              rw [smul_add, coeff_add, coeff_add,
                Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g c₁ c₂ ↦ by
                  simp only [add_smul, smul_add, map_add, Pi.add_apply, single_add]),
                Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g c₁ c₂ ↦ by
                  simp only [add_smul, smul_add, map_add, Pi.add_apply, single_add]),
                smul_add, hu₁, hu₂]
            | single g c =>
              rw [smul_single, coeff_single, coeff_single,
                Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
              have hcm : (single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • ((a • c) • x) =
                  algebraMap A Λ a •
                    ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • (c • x)) := by
                rw [smul_eq_mul, mul_smul, ← algebraMap_smul Λ a (c • x)]
                simpa only [singleSMulEnd_apply] using
                  (singleSMulEnd Λ g⁻¹ M).map_smul (algebraMap A Λ a) (c • x)
              rw [hcm, iM.map_smul, Pi.smul_apply, smul_eq_mul,
                ← Algebra.smul_def, smul_single] }
      map_add' := fun x₁ x₂ ↦ LinearMap.ext fun p ↦ funext fun jl ↦ by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply]
        rw [← Finsupp.sum_add]
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        simp only [smul_add, map_add, Pi.add_apply, single_add]
      map_smul' := fun a x ↦ LinearMap.ext fun p ↦ funext fun jl ↦ by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
          RingHom.id_apply, Finsupp.sum]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        have hcm : (single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • ((iP p jl.1).coeff g • (a • x)) =
            algebraMap A Λ a •
              ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • ((iP p jl.1).coeff g • x)) := by
          rw [smul_comm ((iP p jl.1).coeff g) a x, ← algebraMap_smul Λ a ((iP p jl.1).coeff g • x)]
          simpa only [singleSMulEnd_apply] using
            (singleSMulEnd Λ g⁻¹ M).map_smul (algebraMap A Λ a) ((iP p jl.1).coeff g • x)
        rw [hcm, iM.map_smul, Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def, smul_single] }
  let liftA : M ⊗[A] P →ₗ[A] (Fin m × Fin k → MonoidAlgebra Λ G) := TensorProduct.lift bilin
  { toFun := fun x ↦ liftA x.val
    map_add' := fun x y ↦ liftA.map_add x.val y.val
    map_smul' := fun r x ↦ by
      rw [RingHom.id_apply]
      induction r using MonoidAlgebra.induction_linear with
      | zero => simp
      | add r₁ r₂ h₁ h₂ => simp [add_smul, h₁, h₂]
      | single h b =>
        refine inductionOn x ?_ ?_
        · intro m p
          funext jl
          rw [single_smul_tmul, Pi.smul_apply, smul_eq_mul]
          change ((iP ((single h (1 : A) : MonoidAlgebra A G) • p) jl.1).coeff.sum fun g c ↦
              single g (iM ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
                (c • ((single h b : MonoidAlgebra Λ G) • m))) jl.2)) =
            single h b * ((iP p jl.1).coeff.sum fun g c ↦
              single g (iM ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • (c • m)) jl.2))
          rw [iP.map_smul, Pi.smul_apply, smul_eq_mul]
          generalize iP p jl.1 = u
          induction u using MonoidAlgebra.induction_linear with
          | zero => simp
          | add u₁ u₂ hu₁ hu₂ =>
            rw [mul_add, coeff_add, coeff_add,
              Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g c₁ c₂ ↦ by
                simp only [add_smul, smul_add, map_add, Pi.add_apply, single_add]),
              Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g c₁ c₂ ↦ by
                simp only [add_smul, smul_add, map_add, Pi.add_apply, single_add]),
              mul_add, hu₁, hu₂]
          | single g c =>
            rw [single_mul_single, one_mul, coeff_single, coeff_single,
              Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
              single_mul_single]
            congr 1
            have hinner :
                (single (h * g)⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
                  (c • ((single h b : MonoidAlgebra Λ G) • m)) =
                b • ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • (c • m)) := by
              rw [← algebraMap_smul Λ c ((single h b : MonoidAlgebra Λ G) • m),
                ← algebraMap_smul Λ c m]
              have hc1 : (single h b : MonoidAlgebra Λ G) • (algebraMap A Λ c • m) =
                  algebraMap A Λ c • ((single h b : MonoidAlgebra Λ G) • m) := by
                have h1 : (single h b : MonoidAlgebra Λ G) = b • single h (1 : Λ) := by
                  rw [smul_single, smul_eq_mul, mul_one]
                have hcomm : (single h (1 : Λ) : MonoidAlgebra Λ G) • (algebraMap A Λ c • m) =
                    algebraMap A Λ c • ((single h (1 : Λ) : MonoidAlgebra Λ G) • m) := by
                  simpa only [singleSMulEnd_apply] using
                    (singleSMulEnd Λ h M).map_smul (algebraMap A Λ c) m
                rw [h1, smul_assoc, hcomm, smul_assoc, ← mul_smul, ← mul_smul,
                  Algebra.commutes c b]
              rw [← hc1, ← mul_smul, single_mul_single, mul_inv_rev, inv_mul_cancel_right, one_mul]
              have hb : (single g⁻¹ b : MonoidAlgebra Λ G) = b • single g⁻¹ (1 : Λ) := by
                rw [smul_single, smul_eq_mul, mul_one]
              rw [hb, smul_assoc]
            rw [hinner, iM.map_smul, Pi.smul_apply, smul_eq_mul]
        · intro u v hu hv
          simp only [smul_add, liftA.map_add, val_add, hu, hv] }

@[simp]
theorem retractIncl_tmul {m k : ℕ}
    (iP : P →ₗ[MonoidAlgebra A G] (Fin m → MonoidAlgebra A G))
    (iM : M →ₗ[Λ] (Fin k → Λ)) (x : M) (p : P) (jl : Fin m × Fin k) :
    retractIncl iP iM (tmul x p) jl =
      (iP p jl.1).coeff.sum fun g c ↦
        single g (iM ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • (c • x)) jl.2) :=
  (rfl)

/-- Explicit `MonoidAlgebra Λ G`-linear retraction
`(Fin m × Fin k → Λ[G]) →ₗ[Λ[G]] DiagonalTensor A Λ P M` left-inverse to `retractIncl`. -/
def retractProj {m k : ℕ}
    (rP : (Fin m → MonoidAlgebra A G) →ₗ[MonoidAlgebra A G] P)
    (rM : (Fin k → Λ) →ₗ[Λ] M) :
    (Fin m × Fin k → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] DiagonalTensor A Λ P M where
  toFun v := ∑ jl : Fin m × Fin k, (v jl).coeff.sum fun g a ↦
    tmul ((single g a : MonoidAlgebra Λ G) • rM (Pi.single jl.2 1))
      (rP (Pi.single jl.1 (single g (1 : A))))
  map_add' v w := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun jl _ ↦ ?_
    rw [Pi.add_apply, coeff_add]
    exact Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g a₁ a₂ ↦ by
      rw [single_add, add_smul, add_tmul])
  map_smul' r v := by
    rw [RingHom.id_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r₁ r₂ h₁ h₂ =>
      have hadd : ∀ w₁ w₂ : Fin m × Fin k → MonoidAlgebra Λ G,
          (∑ jl : Fin m × Fin k, ((w₁ + w₂) jl).coeff.sum fun g a ↦
            tmul (A := A) (Λ := Λ) ((single g a : MonoidAlgebra Λ G) • rM (Pi.single jl.2 1))
              (rP (Pi.single jl.1 (single g (1 : A))))) =
          (∑ jl : Fin m × Fin k, (w₁ jl).coeff.sum fun g a ↦
            tmul (A := A) (Λ := Λ) ((single g a : MonoidAlgebra Λ G) • rM (Pi.single jl.2 1))
              (rP (Pi.single jl.1 (single g (1 : A))))) +
          (∑ jl : Fin m × Fin k, (w₂ jl).coeff.sum fun g a ↦
            tmul (A := A) (Λ := Λ) ((single g a : MonoidAlgebra Λ G) • rM (Pi.single jl.2 1))
              (rP (Pi.single jl.1 (single g (1 : A))))) := fun w₁ w₂ ↦ by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun jl _ ↦ ?_
        rw [Pi.add_apply, coeff_add]
        exact Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g a₁ a₂ ↦ by
          rw [single_add, add_smul, add_tmul])
      rw [add_smul, add_smul, hadd, h₁, h₂]
    | single h b =>
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun jl _ ↦ ?_
      rw [Pi.smul_apply, smul_eq_mul]
      generalize v jl = u
      induction u using MonoidAlgebra.induction_linear with
      | zero => simp
      | add u₁ u₂ hu₁ hu₂ =>
        rw [mul_add, coeff_add, coeff_add,
          Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g a₁ a₂ ↦ by
            rw [single_add, add_smul, add_tmul]),
          Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g a₁ a₂ ↦ by
            rw [single_add, add_smul, add_tmul]),
          smul_add, hu₁, hu₂]
      | single g a =>
        rw [single_mul_single, coeff_single, coeff_single,
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
          single_smul_tmul]
        congr 1
        · rw [← mul_smul, single_mul_single]
        · have hpi : (Pi.single jl.1 (single (h * g) (1 : A)) : Fin m → MonoidAlgebra A G) =
              (single h (1 : A) : MonoidAlgebra A G) •
                Pi.single jl.1 (single g (1 : A)) := by
            ext j
            by_cases hj : j = jl.1 <;> simp [hj, single_mul_single]
          rw [hpi, rP.map_smul]

@[simp]
theorem retractProj_single_single {m k : ℕ}
    (rP : (Fin m → MonoidAlgebra A G) →ₗ[MonoidAlgebra A G] P)
    (rM : (Fin k → Λ) →ₗ[Λ] M) (jl : Fin m × Fin k) (g : G) (a : Λ) :
    retractProj rP rM (Pi.single jl (single g a)) =
      tmul ((single g a : MonoidAlgebra Λ G) • rM (Pi.single jl.2 1))
        (rP (Pi.single jl.1 (single g (1 : A)))) := by
  change ∑ p : Fin m × Fin k,
      ((Pi.single jl (single g a) : Fin m × Fin k → MonoidAlgebra Λ G) p).coeff.sum
        (fun g' a' ↦
          tmul (A := A) (Λ := Λ) ((single g' a' : MonoidAlgebra Λ G) • rM (Pi.single p.2 1))
            (rP (Pi.single p.1 (single g' (1 : A))))) = _
  rw [Finset.sum_eq_single jl]
  · rw [Pi.single_eq_same, coeff_single, Finsupp.sum_single_index (by simp)]
  · intro p _ hp
    rw [Pi.single_eq_of_ne hp]
    simp
  · intro hmem
    exact absurd (Finset.mem_univ jl) hmem

/-- `retractProj rP rM` is a left inverse to `retractIncl iP iM`. -/
theorem retractProj_comp_retractIncl {m k : ℕ}
    (iP : P →ₗ[MonoidAlgebra A G] (Fin m → MonoidAlgebra A G))
    (rP : (Fin m → MonoidAlgebra A G) →ₗ[MonoidAlgebra A G] P)
    (hrP : rP ∘ₗ iP = .id)
    (iM : M →ₗ[Λ] (Fin k → Λ)) (rM : (Fin k → Λ) →ₗ[Λ] M) (hrM : rM ∘ₗ iM = .id) :
    retractProj (A := A) (Λ := Λ) (P := P) (M := M) (G := G) rP rM ∘ₗ
      retractIncl iP iM = .id := by
  apply LinearMap.ext
  intro x
  refine inductionOn x ?_ ?_
  · intro m₀ p₀
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    change ∑ jl : Fin m × Fin k, (retractIncl iP iM (tmul m₀ p₀) jl).coeff.sum (fun g a ↦
        tmul (A := A) (Λ := Λ) ((single g a : MonoidAlgebra Λ G) • rM (Pi.single jl.2 1))
          (rP (Pi.single jl.1 (single g (1 : A))))) = tmul m₀ p₀
    rw [Fintype.sum_prod_type]
    have hstep : ∀ (j : Fin m) (l : Fin k),
        (retractIncl iP iM (tmul m₀ p₀) (j, l)).coeff.sum (fun g a ↦
          tmul (A := A) (Λ := Λ) ((single g a : MonoidAlgebra Λ G) • rM (Pi.single l 1))
            (rP (Pi.single j (single g (1 : A))))) =
        (iP p₀ j).coeff.sum fun g c ↦
          tmul (A := A) (Λ := Λ)
            ((single g (iM ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • (c • m₀)) l) :
              MonoidAlgebra Λ G) • rM (Pi.single l 1))
            (rP (Pi.single j (single g (1 : A)))) := by
      intro j l
      rw [retractIncl_tmul]
      let φ : MonoidAlgebra Λ G →+ DiagonalTensor A Λ P M :=
        { toFun := fun u ↦ u.coeff.sum fun g a ↦
            tmul ((single g a : MonoidAlgebra Λ G) • rM (Pi.single l 1))
              (rP (Pi.single j (single g (1 : A))))
          map_zero' := by simp
          map_add' := fun u₁ u₂ ↦ by
            rw [coeff_add]
            exact Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g a₁ a₂ ↦ by
              rw [single_add, add_smul, add_tmul]) }
      have hφ : ∀ (g : G) (a : Λ), φ (single g a) =
          tmul (A := A) (Λ := Λ) ((single g a : MonoidAlgebra Λ G) • rM (Pi.single l 1))
            (rP (Pi.single j (single g (1 : A)))) := fun g a ↦ by
        change (single g a : MonoidAlgebra Λ G).coeff.sum (fun g' a' ↦
          tmul (A := A) (Λ := Λ) ((single g' a' : MonoidAlgebra Λ G) • rM (Pi.single l 1))
            (rP (Pi.single j (single g' (1 : A))))) = _
        rw [coeff_single, Finsupp.sum_single_index (by simp)]
      change φ ((iP p₀ j).coeff.sum fun g c ↦
          single g (iM ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • (c • m₀)) l)) = _
      rw [Finsupp.sum, map_sum]
      exact Finset.sum_congr rfl fun g _ ↦ hφ g _
    simp_rw [hstep]
    have hinner : ∀ j : Fin m,
        ∑ l : Fin k, (iP p₀ j).coeff.sum (fun g c ↦
          tmul (A := A) (Λ := Λ)
            ((single g (iM ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • (c • m₀)) l) :
              MonoidAlgebra Λ G) • rM (Pi.single l 1))
            (rP (Pi.single j (single g (1 : A))))) =
        tmul (A := A) (Λ := Λ) m₀ (rP (Pi.single j (iP p₀ j))) := by
      intro j
      simp_rw [Finsupp.sum]
      rw [Finset.sum_comm]
      have hterm : ∀ g ∈ (iP p₀ j).coeff.support,
          ∑ l : Fin k,
            tmul (A := A) (Λ := Λ) ((single g (iM ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) •
                ((iP p₀ j).coeff g • m₀)) l) : MonoidAlgebra Λ G) • rM (Pi.single l 1))
              (rP (Pi.single j (single g (1 : A)))) =
          tmul (A := A) (Λ := Λ) m₀ (rP (Pi.single j (single g ((iP p₀ j).coeff g)))) := by
        intro g _
        have hsum_tmul : ∀ s : Finset (Fin k), ∀ f : Fin k → M, ∀ p : P,
            ∑ l ∈ s, tmul (A := A) (Λ := Λ) (f l) p = tmul (∑ l ∈ s, f l) p := by
          intro s f p
          classical
          induction s using Finset.induction_on with
          | empty => simp
          | insert l s hl ih => rw [Finset.sum_insert hl, Finset.sum_insert hl, ih, add_tmul]
        rw [hsum_tmul]
        let y : M := (single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • ((iP p₀ j).coeff g • m₀)
        have hM : ∑ l : Fin k,
            (single g (iM y l) : MonoidAlgebra Λ G) • rM (Pi.single l 1) =
            (iP p₀ j).coeff g • m₀ := by
          have hl : ∀ l : Fin k,
              (single g (iM y l) : MonoidAlgebra Λ G) • rM (Pi.single l 1) =
              (single g (1 : Λ) : MonoidAlgebra Λ G) • rM (Pi.single l (iM y l)) := by
            intro l
            have h1 : (single g (iM y l) : MonoidAlgebra Λ G) =
                single g (1 : Λ) * single 1 (iM y l) := by
              rw [single_mul_single, mul_one, one_mul]
            have h2 : (single (1 : G) (iM y l) : MonoidAlgebra Λ G) =
                (iM y l) • (1 : MonoidAlgebra Λ G) := by
              rw [one_def, smul_single, smul_eq_mul, mul_one]
            rw [h1, mul_smul, h2, smul_assoc, one_smul, ← rM.map_smul]
            congr 2
            funext l'
            by_cases hll' : l' = l <;> simp [hll']
          simp_rw [hl, ← Finset.smul_sum, ← map_sum]
          have hpi : (∑ l : Fin k, Pi.single l (iM y l)) = iM y := by
            funext l'
            simp [Finset.sum_apply, Pi.single_apply]
          rw [hpi]
          have hrm : rM (iM y) = y := congrArg (fun f : Module.End Λ M ↦ f y) hrM
          rw [hrm]
          change (single g (1 : Λ) : MonoidAlgebra Λ G) •
              ((single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • ((iP p₀ j).coeff g • m₀)) = _
          rw [← mul_smul, single_mul_single, mul_inv_cancel, mul_one, ← one_def, one_smul]
        rw [hM, smul_tmul, ← algebraMap_smul (MonoidAlgebra A G), ← rP.map_smul]
        congr 2
        funext j'
        rw [Pi.smul_apply, algebraMap_smul]
        by_cases hj' : j' = j
        · subst hj'
          simp [smul_single]
        · simp [hj']
      rw [Finset.sum_congr rfl hterm]
      have hsum_tmul' : ∀ s : Finset G, ∀ f : G → P,
          ∑ g ∈ s, tmul (A := A) (Λ := Λ) m₀ (f g) = tmul m₀ (∑ g ∈ s, f g) := by
        intro s f
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert g s hg ih => rw [Finset.sum_insert hg, Finset.sum_insert hg, ih, tmul_add]
      rw [hsum_tmul', ← map_sum]
      congr 2
      funext j'
      rw [Finset.sum_apply]
      by_cases hj' : j' = j
      · subst hj'
        simp only [Pi.single_eq_same]
        exact sum_coeff_single (iP p₀ j')
      · simp [Pi.single_eq_of_ne hj']
    simp_rw [hinner]
    have hsum_j : ∀ s : Finset (Fin m), ∀ f : Fin m → P,
        ∑ j ∈ s, tmul (A := A) (Λ := Λ) m₀ (f j) = tmul m₀ (∑ j ∈ s, f j) := by
      intro s f
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ih, tmul_add]
    rw [hsum_j, ← map_sum]
    have hpiP : (∑ j : Fin m, Pi.single j (iP p₀ j)) = iP p₀ := by
      funext j'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hpiP]
    have hrp : rP (iP p₀) = p₀ := congrArg (fun f : Module.End (MonoidAlgebra A G) P ↦ f p₀) hrP
    rw [hrp]
  · intro u v hu hv
    simp only [map_add, LinearMap.id_apply] at hu hv ⊢
    exact congrArg₂ (· + ·) hu hv

/-- If `P` is finitely generated and projective over `A[G]` and `M` is finitely generated and
projective over `Λ`, then `DiagonalTensor A Λ P M` is finitely generated and projective over
`Λ[G]`. Neither finiteness of `G` nor `A`-projectivity of `M` is required. -/
theorem finite_projective [Module.Finite (MonoidAlgebra A G) P]
    [Module.Projective (MonoidAlgebra A G) P] [Module.Finite Λ M] [Module.Projective Λ M] :
    Module.Finite (MonoidAlgebra Λ G) (DiagonalTensor A Λ P M) ∧
      Module.Projective (MonoidAlgebra Λ G) (DiagonalTensor A Λ P M) := by
  obtain ⟨m, rP, iP, -, -, hrP⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra A G) P
  obtain ⟨k, rM, iM, -, -, hrM⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ M
  let iD := retractIncl (A := A) (Λ := Λ) (P := P) (M := M) (G := G) iP iM
  let rD := retractProj (A := A) (Λ := Λ) (P := P) (M := M) (G := G) rP rM
  have hrD : rD ∘ₗ iD = .id := retractProj_comp_retractIncl iP rP hrP iM rM hrM
  have hsurj : Function.Surjective rD := Function.RightInverse.surjective
    (fun x ↦ congrArg (fun f : Module.End (MonoidAlgebra Λ G) _ ↦ f x) hrD)
  exact ⟨Module.Finite.of_surjective rD hsurj, Module.Projective.of_split iD rD hrD⟩

end FiniteProjective

end DiagonalTensor

end MonoidAlgebra

/-! ### Section 2: Centralizer trace of a diagonal tensor product (Stacks 64.15.7) -/

namespace LinearMap

section CentralizerTraceDiagonalTensor

open MonoidAlgebra MonoidAlgebra.DiagonalTensor

variable {A Λ : Type*} [CommRing A] [Ring Λ] [Algebra A Λ]
variable {G Γ : Type*} [Group G] [Monoid Γ]

/-- Conjugating `singleSMulEnd Λ γ M` by an element `ι g` in the image of a group `G` leaves its
Hattori–Stallings trace over `Λ` unchanged. -/
theorem hattoriStallingsTrace_singleSMulEnd_conj (ι : G →* Γ) (g : G) (γ : Γ)
    (M : Type*) [AddCommGroup M] [Module Λ M] [Module (MonoidAlgebra Λ Γ) M]
    [IsScalarTower Λ (MonoidAlgebra Λ Γ) M] [Module.Finite Λ M] [Module.Projective Λ M] :
    hattoriStallingsTrace Λ M (singleSMulEnd Λ (ι g * γ * ι g⁻¹) M) =
      hattoriStallingsTrace Λ M (singleSMulEnd Λ γ M) := by
  let e : M ≃ₗ[Λ] M := LinearEquiv.ofLinearMap
    (singleSMulEnd Λ (ι g) M) (singleSMulEnd Λ (ι g⁻¹) M)
    (by
      rw [← singleSMulEnd_mul, ← map_mul ι g g⁻¹, mul_inv_cancel, map_one, singleSMulEnd_one])
    (by
      rw [← singleSMulEnd_mul, ← map_mul ι g⁻¹ g, inv_mul_cancel, map_one, singleSMulEnd_one])
  have hconj : singleSMulEnd Λ (ι g * γ * ι g⁻¹) M =
      e.conjRingEquiv (singleSMulEnd Λ γ M) := by
    ext x
    simp [e, singleSMulEnd_apply, ← mul_smul, single_mul_single, mul_assoc]
  rw [hconj]
  exact hattoriStallingsTrace_conj (singleSMulEnd Λ γ M) e

/-- **Stacks Lemma 64.15.7.** For any monoid homomorphism `ι : G →* Γ` from a group `G` such that
the centralizer `Z_γ = ι.centralizerSubgroup γ` has finite index in `G`, any finite projective
`A[G]`-module `P` with compatible `A[Γ]`-action, and any finite projective `Λ`-module `M` with
compatible `Λ[Γ]`-action, the centralizer trace on the diagonal tensor product `M ⊗[A] P` factors
as the scalar action of `centralizerScalarTrace A ι γ P` on `hattoriStallingsTrace Λ M γ`. -/
theorem centralizerTrace_diagonalTensor (ι : G →* Γ) (γ : Γ)
    [(ι.centralizerSubgroup γ).FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A Γ) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A Γ) P]
    [IsScalarTower A (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P), r • p = mapDomain ι r • p)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (M : Type*) [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [Module (MonoidAlgebra Λ Γ) M] [IsScalarTower Λ (MonoidAlgebra Λ Γ) M]
    [Module (MonoidAlgebra Λ G) M] [IsScalarTower Λ (MonoidAlgebra Λ G) M]
    (hMG : ∀ (r : MonoidAlgebra Λ G) (m : M), r • m = mapDomain ι r • m)
    [Module.Finite Λ M] [Module.Projective Λ M] :
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).2
    centralizerTrace Λ ι γ (DiagonalTensor A Λ P M)
        (DiagonalTensor.smul_eq_mapDomain ι hPG hMG) =
      TauCeti.cyclicQuotientSMul A Λ (centralizerScalarTrace A ι γ P hPG)
        (hattoriStallingsTrace Λ M (singleSMulEnd Λ γ M)) := by
  classical
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).2
  let Z := ι.centralizerSubgroup γ
  have : Fintype (G ⧸ Z.subtype.range) := by
    have : Finite (G ⧸ Z.subtype.range) := by rw [Subgroup.range_subtype]; infer_instance
    exact Fintype.ofFinite _
  obtain ⟨m, rP, iP, -, -, hrP⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra A G) P
  obtain ⟨k, rM, iM, -, -, hrM⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ M
  let iD0 := retractIncl (A := A) (Λ := Λ) (P := P) (M := M) (G := G) iP iM
  let rD0 := retractProj (A := A) (Λ := Λ) (P := P) (M := M) (G := G) rP rM
  have hrD0 : rD0 ∘ₗ iD0 = .id := retractProj_comp_retractIncl iP rP hrP iM rM hrM
  let eIdx : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv
  let ePi : (Fin m × Fin k → MonoidAlgebra Λ G) ≃ₗ[MonoidAlgebra Λ G]
      (Fin (m * k) → MonoidAlgebra Λ G) :=
    LinearEquiv.piCongrLeft' (MonoidAlgebra Λ G) (fun _ ↦ MonoidAlgebra Λ G) eIdx
  let iD : DiagonalTensor A Λ P M →ₗ[MonoidAlgebra Λ G] (Fin (m * k) → MonoidAlgebra Λ G) :=
    ePi.toLinearMap ∘ₗ iD0
  let rD : (Fin (m * k) → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] DiagonalTensor A Λ P M :=
    rD0 ∘ₗ ePi.symm.toLinearMap
  have hrD : rD ∘ₗ iD = .id := by
    apply LinearMap.ext
    intro x
    change rD0 (ePi.symm (ePi (iD0 x))) = x
    rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hrD0 x
  rw [centralizerTrace_eq_of_retract ι γ (DiagonalTensor A Λ P M)
      (DiagonalTensor.smul_eq_mapDomain ι hPG hMG) iD rD hrD,
    centralizerScalarTrace_eq_of_retract ι γ P hPG iP rP hrP]
  have hsum_idx :
      (∑ idx : Fin (m * k), ∑ q : G ⧸ Z.subtype.range,
        (iD ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) •
          rD (Pi.single idx (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) idx).coeff q.out⁻¹) =
      ∑ j : Fin m, ∑ q : G ⧸ Z.subtype.range, ∑ l : Fin k,
        (iD0 ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) •
          rD0 (Pi.single (j, l) (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) (j, l)).coeff q.out⁻¹ := by
    rw [← Fintype.sum_equiv eIdx
      (fun p : Fin m × Fin k ↦ ∑ q : G ⧸ Z.subtype.range,
        (iD0 ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) •
          rD0 (Pi.single p (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) p).coeff q.out⁻¹)
      (fun idx : Fin (m * k) ↦ ∑ q : G ⧸ Z.subtype.range,
        (iD ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) •
          rD (Pi.single idx (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) idx).coeff q.out⁻¹)
      (fun p ↦ Finset.sum_congr rfl fun q _ ↦ by
        have hsymm : ePi.symm (Pi.single (eIdx p) (MonoidAlgebra.single q.out⁻¹ (1 : Λ))) =
            Pi.single p (MonoidAlgebra.single q.out⁻¹ (1 : Λ)) := by
          apply ePi.injective
          rw [LinearEquiv.apply_symm_apply]
          funext idx
          change (Pi.single (eIdx p) (MonoidAlgebra.single q.out⁻¹ (1 : Λ)) :
              Fin (m * k) → MonoidAlgebra Λ G) idx =
            (Pi.single p (MonoidAlgebra.single q.out⁻¹ (1 : Λ)) :
              Fin m × Fin k → MonoidAlgebra Λ G) (eIdx.symm idx)
          by_cases h : idx = eIdx p
          · subst h
            simp
          · have h' : eIdx.symm idx ≠ p := fun hEq ↦ h (by rw [← hEq, Equiv.apply_symm_apply])
            simp [h, h']
        have heval : ∀ v : Fin m × Fin k → MonoidAlgebra Λ G, ePi v (eIdx p) = v p := fun v ↦ by
          change v (eIdx.symm (eIdx p)) = v p
          rw [Equiv.symm_apply_apply]
        simp only [iD, rD, LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, heval])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
  rw [hsum_idx]
  have hentry : ∀ (j : Fin m) (q : G ⧸ Z.subtype.range) (l : Fin k),
      (iD0 ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) •
        rD0 (Pi.single (j, l) (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) (j, l)).coeff q.out⁻¹ =
      algebraMap A Λ
        ((iP ((MonoidAlgebra.single γ (1 : A) : MonoidAlgebra A Γ) •
          rP (Pi.single j (MonoidAlgebra.single q.out⁻¹ (1 : A)))) j).coeff q.out⁻¹) *
        iM (singleSMulEnd Λ (ι q.out * γ * ι q.out⁻¹) M (rM (Pi.single l 1))) l := by
    intro j q l
    dsimp only [iD0, rD0]
    rw [retractProj_single_single, single_smul_tmul, retractIncl_tmul]
    set p' : P := (MonoidAlgebra.single γ (1 : A) : MonoidAlgebra A Γ) •
      rP (Pi.single j (MonoidAlgebra.single q.out⁻¹ (1 : A)))
    set m' : M := (MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ Γ) •
      ((MonoidAlgebra.single q.out⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • rM (Pi.single l 1))
    have hcoeff_sum : ∀ u : MonoidAlgebra A G,
        (u.coeff.sum fun g c ↦
          MonoidAlgebra.single g
            (iM ((MonoidAlgebra.single g⁻¹ (1 : Λ) : MonoidAlgebra Λ G) • (c • m')) l)).coeff
          q.out⁻¹ =
        iM ((MonoidAlgebra.single q.out (1 : Λ) : MonoidAlgebra Λ G) •
          (u.coeff q.out⁻¹ • m')) l := by
      intro u
      induction u using MonoidAlgebra.induction_linear with
      | zero => simp
      | add u₁ u₂ h₁ h₂ =>
        rw [coeff_add,
          Finsupp.sum_add_index' (fun _ ↦ by simp) (fun g c₁ c₂ ↦ by
            simp only [add_smul, smul_add, map_add, Pi.add_apply, single_add]),
          coeff_add, Finsupp.add_apply, h₁, h₂, Finsupp.add_apply,
          add_smul, smul_add, map_add, Pi.add_apply]
      | single g c =>
        rw [coeff_single, Finsupp.sum_single_index (by simp), coeff_single]
        by_cases hg : g = q.out⁻¹
        · subst hg
          simp
        · simp [Finsupp.single_eq_of_ne (Ne.symm hg)]
    rw [hcoeff_sum (iP p' j)]
    have hm' :
        (MonoidAlgebra.single q.out (1 : Λ) : MonoidAlgebra Λ G) •
          ((iP p' j).coeff q.out⁻¹ • m') =
        algebraMap A Λ ((iP p' j).coeff q.out⁻¹) •
          singleSMulEnd Λ (ι q.out * γ * ι q.out⁻¹) M (rM (Pi.single l 1)) := by
      rw [← algebraMap_smul Λ ((iP p' j).coeff q.out⁻¹) m']
      have hcomm :
          (MonoidAlgebra.single q.out (1 : Λ) : MonoidAlgebra Λ G) •
            (algebraMap A Λ ((iP p' j).coeff q.out⁻¹) • m') =
          algebraMap A Λ ((iP p' j).coeff q.out⁻¹) •
            ((MonoidAlgebra.single q.out (1 : Λ) : MonoidAlgebra Λ G) • m') := by
        simpa only [singleSMulEnd_apply] using
          (singleSMulEnd Λ q.out M).map_smul (algebraMap A Λ ((iP p' j).coeff q.out⁻¹)) m'
      rw [hcomm]
      congr 1
      dsimp only [m']
      rw [hMG, hMG, mapDomain_single, mapDomain_single, singleSMulEnd_apply,
        ← mul_smul, ← mul_smul, single_mul_single, single_mul_single, mul_one, mul_one, mul_assoc]
    rw [hm', iM.map_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [hentry, ← Finset.mul_sum, map_sum, TauCeti.cyclicQuotientSMul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← TauCeti.cyclicQuotientSMul_mkQ A Λ]
  congr 1
  have htr :
      (TauCeti.commutatorSubmodule ℤ Λ).mkQ
          (∑ l : Fin k, iM (singleSMulEnd Λ (ι q.out * γ * ι q.out⁻¹) M (rM (Pi.single l 1))) l) =
        hattoriStallingsTrace Λ M (singleSMulEnd Λ (ι q.out * γ * ι q.out⁻¹) M) := by
    rw [hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin k)) iM rM hrM,
      Module.Basis.hattoriStallingsTrace_apply]
    congr 1
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp [Pi.basisFun_apply, Pi.basisFun_repr]
  rw [htr, hattoriStallingsTrace_singleSMulEnd_conj ι q.out γ M]

/-- Commutative specialization of Stacks Lemma 64.15.7. -/
theorem centralizerScalarTrace_diagonalTensor {Λ : Type*} [CommRing Λ] [Algebra A Λ]
    (ι : G →* Γ) (γ : Γ) [(ι.centralizerSubgroup γ).FiniteIndex]
    (P : Type*) [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A Γ) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A Γ) P]
    [IsScalarTower A (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P), r • p = mapDomain ι r • p)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (M : Type*) [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [Module (MonoidAlgebra Λ Γ) M] [IsScalarTower Λ (MonoidAlgebra Λ Γ) M]
    [Module (MonoidAlgebra Λ G) M] [IsScalarTower Λ (MonoidAlgebra Λ G) M]
    (hMG : ∀ (r : MonoidAlgebra Λ G) (m : M), r • m = mapDomain ι r • m)
    [Module.Finite Λ M] [Module.Projective Λ M] :
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).2
    centralizerScalarTrace Λ ι γ (DiagonalTensor A Λ P M)
        (DiagonalTensor.smul_eq_mapDomain ι hPG hMG) =
      algebraMap A Λ (centralizerScalarTrace A ι γ P hPG) *
        projectiveTrace Λ M (singleSMulEnd Λ γ M) := by
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).2
  rw [centralizerScalarTrace_apply, centralizerTrace_diagonalTensor ι γ P hPG M hMG,
    TauCeti.cyclicQuotientEquivSelf_cyclicQuotientSMul,
    cyclicQuotientEquivSelf_hattoriStallingsTrace]

end CentralizerTraceDiagonalTensor

end LinearMap

/-! ### Section 3: Coinvariant trace of a diagonal tensor product (Stacks 64.15.8) -/

namespace TauCeti

namespace MonoidExtension

open _root_.MonoidAlgebra _root_.MonoidAlgebra.DiagonalTensor

variable {G Γ : Type*} [Group G] [Group Γ] (E : MonoidExtension G Γ)

/-- The Hattori–Stallings trace of a `G`-conjugacy class `c : E.ConjClasses n` acting on a finite
projective `Λ`-module `M` equipped with a `Λ[E.monoid]`-action. -/
def hattoriStallingsTraceClass (Λ : Type*) [Ring Λ] (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module Λ M] [Module (MonoidAlgebra Λ E.monoid) M]
    [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) M]
    [Module.Finite Λ M] [Module.Projective Λ M] :
    E.ConjClasses n → cyclicQuotient ℤ Λ :=
  Quotient.lift (fun γ : E.fiber n ↦
      LinearMap.hattoriStallingsTrace Λ M (singleSMulEnd Λ γ.1 M)) fun γ₁ γ₂ h ↦ by
    obtain ⟨g, rfl⟩ := E.conjSetoid_iff.mp h
    rw [E.coe_conjFiber, E.conj_eq_monoidIncl_mul]
    exact (LinearMap.hattoriStallingsTrace_singleSMulEnd_conj E.monoidIncl g γ₁.1 M).symm

@[simp]
theorem hattoriStallingsTraceClass_mk (Λ : Type*) [Ring Λ] {n : ℕ} (M : Type*) [AddCommGroup M]
    [Module Λ M] [Module (MonoidAlgebra Λ E.monoid) M]
    [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) M]
    [Module.Finite Λ M] [Module.Projective Λ M] (γ : E.fiber n) :
    E.hattoriStallingsTraceClass Λ n M ⟦γ⟧ =
      LinearMap.hattoriStallingsTrace Λ M (singleSMulEnd Λ γ.1 M) :=
  (rfl)

/-- Commutative scalar version of `hattoriStallingsTraceClass`. -/
def projectiveTraceClass (Λ : Type*) [CommRing Λ] (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module Λ M] [Module (MonoidAlgebra Λ E.monoid) M]
    [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) M]
    [Module.Finite Λ M] [Module.Projective Λ M] (c : E.ConjClasses n) : Λ :=
  cyclicQuotientEquivSelf Λ (E.hattoriStallingsTraceClass Λ n M c)

@[simp]
theorem projectiveTraceClass_mk (Λ : Type*) [CommRing Λ] {n : ℕ} (M : Type*) [AddCommGroup M]
    [Module Λ M] [Module (MonoidAlgebra Λ E.monoid) M]
    [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) M]
    [Module.Finite Λ M] [Module.Projective Λ M] (γ : E.fiber n) :
    E.projectiveTraceClass Λ n M ⟦γ⟧ =
      LinearMap.projectiveTrace Λ M (singleSMulEnd Λ γ.1 M) := by
  rw [projectiveTraceClass, hattoriStallingsTraceClass_mk,
    LinearMap.cyclicQuotientEquivSelf_hattoriStallingsTrace]

/-- **Stacks Lemma 64.15.8.** For a finite group `G`, a commutative ring `A`, an `A`-algebra `Λ`
(possibly noncommutative), a finite projective `A[G]`-module `P` with `E.monoid`-action, and a
finite projective `Λ`-module `M` with `E.monoid`-action, the Hattori–Stallings trace of the
degree-`n` action on the diagonal coinvariants `(M ⊗[A] P)_G` decomposes over `G`-conjugacy classes
in `E.fiber n` as the sum of `centralizerScalarTraceClass` acting on
`hattoriStallingsTraceClass`. -/
theorem hattoriStallingsTrace_coinvariantsAction_diagonalTensor {A Λ : Type*} [CommRing A]
    [Ring Λ] [Algebra A Λ] [Finite G] (n : ℕ)
    (P : Type*) [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A E.monoid) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A E.monoid) P]
    [IsScalarTower A (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P), r • p = mapDomain E.monoidIncl r • p)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (M : Type*) [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [Module (MonoidAlgebra Λ E.monoid) M] [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) M]
    [Module (MonoidAlgebra Λ G) M] [IsScalarTower Λ (MonoidAlgebra Λ G) M]
    (hMG : ∀ (r : MonoidAlgebra Λ G) (m : M), r • m = mapDomain E.monoidIncl r • m)
    [Module.Finite Λ M] [Module.Projective Λ M] :
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).2
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := DiagonalTensor A Λ P M)).1
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := DiagonalTensor A Λ P M)).2
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G (DiagonalTensor A Λ P M))
        (E.coinvariantsAction Λ n (DiagonalTensor A Λ P M)
          (DiagonalTensor.smul_eq_mapDomain E.monoidIncl hPG hMG)) =
      ∑ᶠ c : E.ConjClasses n,
        cyclicQuotientSMul A Λ (E.centralizerScalarTraceClass A n P hPG c)
          (E.hattoriStallingsTraceClass Λ n M c) := by
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).2
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G)
    (P := DiagonalTensor A Λ P M)).1
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G)
    (P := DiagonalTensor A Λ P M)).2
  rw [E.hattoriStallingsTrace_coinvariantsAction n (DiagonalTensor A Λ P M)
      (DiagonalTensor.smul_eq_mapDomain E.monoidIncl hPG hMG)]
  refine finsum_congr fun c ↦ ?_
  obtain ⟨γ, rfl⟩ := Quotient.exists_rep c
  rw [E.centralizerTraceClass_mk, E.centralizerScalarTraceClass_mk,
    E.hattoriStallingsTraceClass_mk]
  exact LinearMap.centralizerTrace_diagonalTensor E.monoidIncl γ.1 P hPG M hMG

/-- Commutative specialization of Stacks Lemma 64.15.8. -/
theorem projectiveTrace_coinvariantsAction_diagonalTensor {A Λ : Type*} [CommRing A]
    [CommRing Λ] [Algebra A Λ] [Finite G] (n : ℕ)
    (P : Type*) [AddCommGroup P] [Module A P] [Module (MonoidAlgebra A E.monoid) P]
    [Module (MonoidAlgebra A G) P] [IsScalarTower A (MonoidAlgebra A E.monoid) P]
    [IsScalarTower A (MonoidAlgebra A G) P]
    (hPG : ∀ (r : MonoidAlgebra A G) (p : P), r • p = mapDomain E.monoidIncl r • p)
    [Module.Finite (MonoidAlgebra A G) P] [Module.Projective (MonoidAlgebra A G) P]
    (M : Type*) [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    [Module (MonoidAlgebra Λ E.monoid) M] [IsScalarTower Λ (MonoidAlgebra Λ E.monoid) M]
    [Module (MonoidAlgebra Λ G) M] [IsScalarTower Λ (MonoidAlgebra Λ G) M]
    (hMG : ∀ (r : MonoidAlgebra Λ G) (m : M), r • m = mapDomain E.monoidIncl r • m)
    [Module.Finite Λ M] [Module.Projective Λ M] :
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).1
    haveI := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).2
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := DiagonalTensor A Λ P M)).1
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := DiagonalTensor A Λ P M)).2
    LinearMap.projectiveTrace Λ (Coinvariants Λ G (DiagonalTensor A Λ P M))
        (E.coinvariantsAction Λ n (DiagonalTensor A Λ P M)
          (DiagonalTensor.smul_eq_mapDomain E.monoidIncl hPG hMG)) =
      ∑ᶠ c : E.ConjClasses n,
        algebraMap A Λ (E.centralizerScalarTraceClass A n P hPG c) *
          E.projectiveTraceClass Λ n M c := by
  classical
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).1
  have := (DiagonalTensor.finite_projective (A := A) (Λ := Λ) (P := P) (M := M) (G := G)).2
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G)
    (P := DiagonalTensor A Λ P M)).1
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G)
    (P := DiagonalTensor A Λ P M)).2
  have : Fintype (E.ConjClasses n) := Fintype.ofFinite _
  rw [← LinearMap.cyclicQuotientEquivSelf_hattoriStallingsTrace,
    E.hattoriStallingsTrace_coinvariantsAction_diagonalTensor n P hPG M hMG,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [cyclicQuotientEquivSelf_cyclicQuotientSMul, projectiveTraceClass]

end MonoidExtension

end TauCeti
