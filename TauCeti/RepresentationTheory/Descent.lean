/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import TauCeti.LinearAlgebra.LinearMap.BaseChange
public import TauCeti.RepresentationTheory.BaseChange
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coefficient-field descent of representation morphisms and equivalences

This file develops the algebraic descent properties for base change of representations, showing
that morphisms and equivalences over an algebraic field extension `Ω / E` behave as a filtered
colimit over the finite intermediate fields `E' ⊆ Ω`.

Specifically, we prove:

* **Transitivity of base change** (`Representation.baseChangeTransEquiv`): for a tower `R → A → B`,
  base-changing a representation in two steps `B ⊗[A] (A ⊗[R] V)` is equivariantly equivalent to
  `B ⊗[R] V` via `TensorProduct.AlgebraTensorModule.cancelBaseChange`.
* **Faithfulness of faithfully flat base change**
  (`Representation.IntertwiningMap.baseChange_injective` and
  `Representation.Equiv.baseChange_injective`): two intertwining maps or equivalences that agree
  after faithfully flat extension of scalars are already equal. In particular, morphisms defined
  over two extensions `A₁, A₂` that induce the same map over a larger faithfully flat extension
  `B` already agree over any common enlargement `A₃ ⊆ B`
  (`Representation.IntertwiningMap.baseChangeTrans_eq_of_baseChangeTrans_eq`).
* **Descent of intertwining maps and equivalences**
  (`Representation.IntertwiningMap.exists_descent`,
  `Representation.IntertwiningMap.exists_descent_family`, `Representation.Equiv.exists_descent`):
  for finite-dimensional representations `ρ, σ` over `E` and an algebraic extension `Ω / E`, any
  intertwining map (or finite family of intertwining maps, or equivalence) between `ρ.baseChange Ω`
  and `σ.baseChange Ω` descends to a finite intermediate field `E' : IntermediateField E Ω`,
  obtained by adjoining the entries of its matrix in base-changed `E`-bases.

## Main declarations

* `Representation.baseChangeTransEquiv`: equivariant equivalence
  `B ⊗[A] (A ⊗[R] V) ≃ B ⊗[R] V` for a tower of scalars `R → A → B`.
* `Representation.IntertwiningMap.baseChange_injective`: faithfully flat base change is injective
  on intertwining maps.
* `Representation.Equiv.baseChange_injective`: faithfully flat base change is injective on
  equivalences of representations.
* `Representation.IntertwiningMap.baseChangeTrans_eq_of_baseChangeTrans_eq`: two intertwining maps
  over `A₁` and `A₂` that agree after base change to `B` already agree after base change to any
  common enlargement `A₃` over which `B` is faithfully flat.
* `Representation.IntertwiningMap.exists_descent`: an intertwining map over an algebraic extension
  `Ω / E` between base-changed finite-dimensional `E`-representations descends to a finite
  intermediate field.
* `Representation.IntertwiningMap.exists_descent_family`: simultaneous descent of a finite family
  of intertwining maps to a single finite intermediate field.
* `Representation.Equiv.exists_descent`: an equivalence over an algebraic extension `Ω / E` between
  base-changed finite-dimensional `E`-representations descends to a finite intermediate field.

## References

* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *G-local systems on smooth projective curves
  are potentially automorphic*, Acta Math. 223 (2019), §4.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace Representation

@[simp]
theorem IntertwiningMap.baseChange_id {R A G V : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Monoid G] [AddCommMonoid V] [Module R V] (ρ : Representation R G V) :
    (IntertwiningMap.id ρ).baseChange A = IntertwiningMap.id (ρ.baseChange A) :=
  IntertwiningMap.ext <| by
    rw [IntertwiningMap.toLinearMap_baseChange]
    exact LinearMap.baseChange_id

section BaseChangeTrans

variable {R G M : Type*} [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]
variable (A B : Type*) [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B]

/-- **Extension of scalars in stages**: for a tower `R → A → B`, extending a representation to `A`
and then to `B` is equivariantly equivalent to extending directly to `B`, via
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
noncomputable def baseChangeTransEquiv (ρ : Representation R G M) :
    (baseChange B (baseChange A ρ)).Equiv (baseChange B ρ) :=
  .mk (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M) fun g ↦ by
    ext
    simp

@[simp]
theorem baseChangeTransEquiv_tmul (ρ : Representation R G M) (b : B) (a : A) (x : M) :
    ρ.baseChangeTransEquiv A B (b ⊗ₜ (a ⊗ₜ x)) = (a • b) ⊗ₜ x :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R A B b x a

@[simp]
theorem baseChangeTransEquiv_symm_tmul (ρ : Representation R G M) (b : B) (x : M) :
    (ρ.baseChangeTransEquiv A B).symm (b ⊗ₜ x) = b ⊗ₜ (1 ⊗ₜ x) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R A B b x

end BaseChangeTrans

section Faithfulness

variable {R A G V W : Type*} [CommRing R] [Ring A] [Algebra R A] [Module.FaithfullyFlat R A]
  [Monoid G] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- **Faithfully flat base change is injective on intertwining maps**: two intertwining maps whose
extensions of scalars to a faithfully flat algebra agree are already equal. -/
theorem IntertwiningMap.baseChange_injective :
    Function.Injective (fun f : IntertwiningMap ρ σ ↦ f.baseChange A) := fun _ _ h ↦ by
  have h' := congrArg IntertwiningMap.toLinearMap h
  simp only [IntertwiningMap.toLinearMap_baseChange] at h'
  exact IntertwiningMap.ext (LinearMap.baseChange_injective h')

/-- **Faithfully flat base change is injective on equivalences of representations.** -/
theorem Equiv.baseChange_injective :
    Function.Injective (fun e : ρ.Equiv σ ↦ e.baseChange A) := fun e₁ e₂ h ↦ by
  apply Equiv.ext
  funext v
  have hmap : e₁.toIntertwiningMap.baseChange A = e₂.toIntertwiningMap.baseChange A := by
    refine DFunLike.ext _ _ fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a w =>
      simpa [IntertwiningMap.baseChange_tmul, Equiv.baseChange_tmul] using
        DFunLike.congr_fun h (a ⊗ₜ w)
  exact DFunLike.congr_fun (IntertwiningMap.baseChange_injective hmap) v

end Faithfulness

section Agreement

variable {R A₁ A₂ A₃ B G V W : Type*}
  [CommRing R] [CommRing A₁] [CommRing A₂] [CommRing A₃] [Ring B]
  [Algebra R A₁] [Algebra R A₂] [Algebra R A₃] [Algebra R B]
  [Algebra A₁ A₃] [Algebra A₂ A₃] [Algebra A₁ B] [Algebra A₂ B] [Algebra A₃ B]
  [IsScalarTower R A₁ A₃] [IsScalarTower R A₂ A₃] [IsScalarTower R A₁ B] [IsScalarTower R A₂ B]
  [IsScalarTower R A₃ B] [IsScalarTower A₁ A₃ B] [IsScalarTower A₂ A₃ B]
  [Module.FaithfullyFlat A₃ B]
  [Monoid G] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

omit [Module.FaithfullyFlat A₃ B] in
/-- Transferring an intertwining map from `A₁` to `A₃` and then to `B` agrees with transferring it
directly from `A₁` to `B`. -/
private theorem IntertwiningMap.baseChangeTrans_trans
    (f : IntertwiningMap (ρ.baseChange A₁) (σ.baseChange A₁)) :
    ((σ.baseChangeTransEquiv A₃ B).toIntertwiningMap.comp
      ((((σ.baseChangeTransEquiv A₁ A₃).toIntertwiningMap.comp (f.baseChange A₃)).comp
        (ρ.baseChangeTransEquiv A₁ A₃).symm.toIntertwiningMap).baseChange B)).comp
      (ρ.baseChangeTransEquiv A₃ B).symm.toIntertwiningMap =
    ((σ.baseChangeTransEquiv A₁ B).toIntertwiningMap.comp (f.baseChange B)).comp
      (ρ.baseChangeTransEquiv A₁ B).symm.toIntertwiningMap := by
  refine DFunLike.ext _ _ fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b v =>
    simp only [IntertwiningMap.comp_apply, Equiv.coe_toIntertwiningMap,
      baseChangeTransEquiv_symm_tmul, IntertwiningMap.baseChange_tmul]
    induction f (1 ⊗ₜ v) using TensorProduct.inductionOn with
    | add y z hy hz => simp [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul a₁ w => simp [smul_assoc]

/-- **Agreement of descended intertwining maps over a common enlargement.** If `f₁` over `A₁` and
`f₂` over `A₂` induce the same intertwining map over a larger algebra `B`, then they already induce
the same intertwining map over any common enlargement `A₃` such that `B` is faithfully flat over
`A₃`. -/
theorem IntertwiningMap.baseChangeTrans_eq_of_baseChangeTrans_eq
    (f₁ : IntertwiningMap (ρ.baseChange A₁) (σ.baseChange A₁))
    (f₂ : IntertwiningMap (ρ.baseChange A₂) (σ.baseChange A₂))
    (h : ((σ.baseChangeTransEquiv A₁ B).toIntertwiningMap.comp (f₁.baseChange B)).comp
          (ρ.baseChangeTransEquiv A₁ B).symm.toIntertwiningMap =
        ((σ.baseChangeTransEquiv A₂ B).toIntertwiningMap.comp (f₂.baseChange B)).comp
          (ρ.baseChangeTransEquiv A₂ B).symm.toIntertwiningMap) :
    ((σ.baseChangeTransEquiv A₁ A₃).toIntertwiningMap.comp (f₁.baseChange A₃)).comp
        (ρ.baseChangeTransEquiv A₁ A₃).symm.toIntertwiningMap =
      ((σ.baseChangeTransEquiv A₂ A₃).toIntertwiningMap.comp (f₂.baseChange A₃)).comp
        (ρ.baseChangeTransEquiv A₂ A₃).symm.toIntertwiningMap := by
  let g₁ := ((σ.baseChangeTransEquiv A₁ A₃).toIntertwiningMap.comp (f₁.baseChange A₃)).comp
    (ρ.baseChangeTransEquiv A₁ A₃).symm.toIntertwiningMap
  let g₂ := ((σ.baseChangeTransEquiv A₂ A₃).toIntertwiningMap.comp (f₂.baseChange A₃)).comp
    (ρ.baseChangeTransEquiv A₂ A₃).symm.toIntertwiningMap
  have hB : ((σ.baseChangeTransEquiv A₃ B).toIntertwiningMap.comp (g₁.baseChange B)).comp
        (ρ.baseChangeTransEquiv A₃ B).symm.toIntertwiningMap =
      ((σ.baseChangeTransEquiv A₃ B).toIntertwiningMap.comp (g₂.baseChange B)).comp
        (ρ.baseChangeTransEquiv A₃ B).symm.toIntertwiningMap := by
    rw [IntertwiningMap.baseChangeTrans_trans, IntertwiningMap.baseChangeTrans_trans, h]
  apply IntertwiningMap.baseChange_injective (A := B)
  refine DFunLike.ext _ _ fun x ↦ ?_
  have hx := DFunLike.congr_fun hB (ρ.baseChangeTransEquiv A₃ B x)
  simp only [IntertwiningMap.comp_apply, Equiv.coe_toIntertwiningMap, Equiv.symm_apply_apply] at hx
  exact (σ.baseChangeTransEquiv A₃ B).injective hx

end Agreement

section Descent

variable {E Ω G : Type*} [Field E] [Field Ω] [Algebra E Ω] [Monoid G]

/-- If the matrix of an intertwining map `f : Ω ⊗[E] V → Ω ⊗[E] W` in base-changed `E`-bases has
all entries in an intermediate field `E'`, then `f` descends to an intertwining map over `E'`. -/
private theorem IntertwiningMap.exists_descent_of_toMatrix_mem
    {V W : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {ρ : Representation E G V} {σ : Representation E G W}
    (f : IntertwiningMap (ρ.baseChange Ω) (σ.baseChange Ω))
    (E' : IntermediateField E Ω)
    (hmem : ∀ i j,
      LinearMap.toMatrix ((Module.finBasis E V).baseChange Ω)
        ((Module.finBasis E W).baseChange Ω) f.toLinearMap i j ∈ E') :
    ∃ f' : IntertwiningMap (ρ.baseChange E') (σ.baseChange E'),
      (σ.baseChangeTransEquiv E' Ω).toIntertwiningMap.comp (f'.baseChange Ω) =
        f.comp (ρ.baseChangeTransEquiv E' Ω).toIntertwiningMap := by
  let bV := Module.finBasis E V
  let bW := Module.finBasis E W
  let M' : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E V)) E' :=
    fun i j ↦ ⟨LinearMap.toMatrix (bV.baseChange Ω) (bW.baseChange Ω) f.toLinearMap i j, hmem i j⟩
  let f₀ : E' ⊗[E] V →ₗ[E'] E' ⊗[E] W :=
    (LinearMap.toMatrix (bV.baseChange E') (bW.baseChange E')).symm M'
  let cV := ρ.baseChangeTransEquiv E' Ω
  let cW := σ.baseChangeTransEquiv E' Ω
  have hf₀_baseChange : cW.toLinearMap ∘ₗ f₀.baseChange Ω = f.toLinearMap ∘ₗ cV.toLinearMap := by
    apply ((bV.baseChange E').baseChange Ω).ext
    intro j
    have hM' : f₀ ((bV.baseChange E') j) = ∑ i, M' i j • (bW.baseChange E') i := by
      have h := LinearMap.toMatrix_apply (bV.baseChange E') (bW.baseChange E') f₀
      rw [LinearEquiv.apply_symm_apply] at h
      rw [← (bW.baseChange E').sum_repr (f₀ ((bV.baseChange E') j))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← h i j]
    have hM : f.toLinearMap ((bV.baseChange Ω) j) =
        ∑ i, (M' i j : Ω) • (bW.baseChange Ω) i := by
      rw [← (bW.baseChange Ω).sum_repr (f.toLinearMap ((bV.baseChange Ω) j))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← LinearMap.toMatrix_apply (bV.baseChange Ω) (bW.baseChange Ω) f.toLinearMap i j]
    simp only [LinearMap.comp_apply, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
      Equiv.coe_toLinearMap]
    rw [baseChangeTransEquiv_tmul, one_smul, ← Module.Basis.baseChange_apply Ω bV j, hM,
      ← Module.Basis.baseChange_apply E' bV j, hM', TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      baseChangeTransEquiv_tmul, Module.Basis.baseChange_apply, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    rfl
  have hint : ∀ g : G, f₀ ∘ₗ (ρ.baseChange E') g = (σ.baseChange E') g ∘ₗ f₀ := fun g ↦ by
    apply LinearMap.baseChange_injective (A := Ω)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    apply LinearMap.ext
    intro x
    apply EquivLike.injective cW
    have h1 := LinearMap.congr_fun hf₀_baseChange ((ρ.baseChange E' g).baseChange Ω x)
    have h2 := LinearMap.congr_fun hf₀_baseChange x
    have hcV : cV ((ρ.baseChange E' g).baseChange Ω x) = (ρ.baseChange Ω) g (cV x) := by
      simpa [cV, baseChange_apply] using LinearMap.congr_fun (cV.isIntertwining' g) x
    have hcW : cW ((σ.baseChange E' g).baseChange Ω (f₀.baseChange Ω x)) =
        (σ.baseChange Ω) g (cW (f₀.baseChange Ω x)) := by
      simpa [cW, baseChange_apply] using
        LinearMap.congr_fun (cW.isIntertwining' g) (f₀.baseChange Ω x)
    have hf := LinearMap.congr_fun (f.isIntertwining' g) (cV x)
    simp only [LinearMap.comp_apply, IntertwiningMap.coe_toLinearMap,
      Equiv.coe_toIntertwiningMap] at h1 h2 hf ⊢
    rw [hcW, h1, h2, hcV, hf]
  refine ⟨⟨f₀, hint⟩, IntertwiningMap.ext ?_⟩
  rw [IntertwiningMap.comp_toLinearMap, IntertwiningMap.toLinearMap_baseChange,
    IntertwiningMap.comp_toLinearMap]
  exact hf₀_baseChange

/-- **Descent of an intertwining map to a finite intermediate field.** If `Ω / E` is an algebraic
field extension and `ρ, σ` are finite-dimensional `E`-representations, then every intertwining map
`Ω ⊗[E] V → Ω ⊗[E] W` descends to `E' ⊗[E] V → E' ⊗[E] W` for some finite intermediate field
`E' : IntermediateField E Ω`. -/
theorem IntertwiningMap.exists_descent [Algebra.IsAlgebraic E Ω]
    {V W : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {ρ : Representation E G V} {σ : Representation E G W}
    (f : IntertwiningMap (ρ.baseChange Ω) (σ.baseChange Ω)) :
    ∃ (E' : IntermediateField E Ω) (_ : FiniteDimensional E E')
      (f' : IntertwiningMap (ρ.baseChange E') (σ.baseChange E')),
      (σ.baseChangeTransEquiv E' Ω).toIntertwiningMap.comp (f'.baseChange Ω) =
        f.comp (ρ.baseChangeTransEquiv E' Ω).toIntertwiningMap := by
  let M := LinearMap.toMatrix ((Module.finBasis E V).baseChange Ω)
    ((Module.finBasis E W).baseChange Ω) f.toLinearMap
  let S : Set Ω := Set.range fun p : Fin (Module.finrank E W) × Fin (Module.finrank E V) ↦
    M p.1 p.2
  let E' : IntermediateField E Ω := IntermediateField.adjoin E S
  have hE'_fin : FiniteDimensional E E' := IntermediateField.finiteDimensional_adjoin fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨f', hf'⟩ := IntertwiningMap.exists_descent_of_toMatrix_mem f E' fun i j ↦
    IntermediateField.subset_adjoin E S ⟨(i, j), rfl⟩
  exact ⟨E', hE'_fin, f', hf'⟩

/-- **Simultaneous descent of finitely many intertwining maps.** Over an algebraic extension
`Ω / E`, any finite family of intertwining maps between base-changed finite-dimensional
`E`-representations descends simultaneously to a single finite intermediate field `E' ⊆ Ω`. -/
theorem IntertwiningMap.exists_descent_family [Algebra.IsAlgebraic E Ω]
    {α : Type*} [Finite α]
    {V W : α → Type*} [∀ a, AddCommGroup (V a)] [∀ a, Module E (V a)]
    [∀ a, FiniteDimensional E (V a)]
    [∀ a, AddCommGroup (W a)] [∀ a, Module E (W a)] [∀ a, FiniteDimensional E (W a)]
    {ρ : ∀ a, Representation E G (V a)} {σ : ∀ a, Representation E G (W a)}
    (f : ∀ a, IntertwiningMap ((ρ a).baseChange Ω) ((σ a).baseChange Ω)) :
    ∃ (E' : IntermediateField E Ω) (_ : FiniteDimensional E E')
      (f' : ∀ a, IntertwiningMap ((ρ a).baseChange E') ((σ a).baseChange E')),
      ∀ a, ((σ a).baseChangeTransEquiv E' Ω).toIntertwiningMap.comp ((f' a).baseChange Ω) =
        (f a).comp ((ρ a).baseChangeTransEquiv E' Ω).toIntertwiningMap := by
  let S : Set Ω := ⋃ a : α, Set.range fun
      p : Fin (Module.finrank E (W a)) × Fin (Module.finrank E (V a)) ↦
    LinearMap.toMatrix ((Module.finBasis E (V a)).baseChange Ω)
      ((Module.finBasis E (W a)).baseChange Ω) (f a).toLinearMap p.1 p.2
  let E' : IntermediateField E Ω := IntermediateField.adjoin E S
  have hE'_fin : FiniteDimensional E E' := IntermediateField.finiteDimensional_adjoin fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hdesc : ∀ a, ∃ f' : IntertwiningMap ((ρ a).baseChange E') ((σ a).baseChange E'),
      ((σ a).baseChangeTransEquiv E' Ω).toIntertwiningMap.comp (f'.baseChange Ω) =
        (f a).comp ((ρ a).baseChangeTransEquiv E' Ω).toIntertwiningMap := fun a ↦
    IntertwiningMap.exists_descent_of_toMatrix_mem (f a) E' fun i j ↦
      IntermediateField.subset_adjoin E S (Set.mem_iUnion.mpr ⟨a, ⟨(i, j), rfl⟩⟩)
  choose f' hf' using hdesc
  exact ⟨E', hE'_fin, f', hf'⟩

/-- **Descent of an equivalence of representations to a finite intermediate field.** Over an
algebraic extension `Ω / E`, an equivalence `(ρ.baseChange Ω).Equiv (σ.baseChange Ω)` between
base-changed finite-dimensional `E`-representations descends to an equivalence over a finite
intermediate field `E' : IntermediateField E Ω`. -/
theorem Equiv.exists_descent [Algebra.IsAlgebraic E Ω]
    {V W : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {ρ : Representation E G V} {σ : Representation E G W}
    (e : (ρ.baseChange Ω).Equiv (σ.baseChange Ω)) :
    ∃ (E' : IntermediateField E Ω) (_ : FiniteDimensional E E')
      (e' : (ρ.baseChange E').Equiv (σ.baseChange E')),
      (e'.baseChange Ω).trans (σ.baseChangeTransEquiv E' Ω) =
        (ρ.baseChangeTransEquiv E' Ω).trans e := by
  let S₁ : Set Ω := Set.range fun p : Fin (Module.finrank E W) × Fin (Module.finrank E V) ↦
    LinearMap.toMatrix ((Module.finBasis E V).baseChange Ω)
      ((Module.finBasis E W).baseChange Ω) e.toLinearMap p.1 p.2
  let S₂ : Set Ω := Set.range fun p : Fin (Module.finrank E V) × Fin (Module.finrank E W) ↦
    LinearMap.toMatrix ((Module.finBasis E W).baseChange Ω)
      ((Module.finBasis E V).baseChange Ω) e.symm.toLinearMap p.1 p.2
  let E' : IntermediateField E Ω := IntermediateField.adjoin E (S₁ ∪ S₂)
  have hE'_fin : FiniteDimensional E E' := IntermediateField.finiteDimensional_adjoin fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨f', hf'⟩ := IntertwiningMap.exists_descent_of_toMatrix_mem e.toIntertwiningMap E'
    fun i j ↦ IntermediateField.subset_adjoin E (S₁ ∪ S₂) (Or.inl ⟨(i, j), rfl⟩)
  obtain ⟨g', hg'⟩ := IntertwiningMap.exists_descent_of_toMatrix_mem e.symm.toIntertwiningMap E'
    fun i j ↦ IntermediateField.subset_adjoin E (S₁ ∪ S₂) (Or.inr ⟨(i, j), rfl⟩)
  have hgf : g'.comp f' = IntertwiningMap.id _ := by
    apply IntertwiningMap.baseChange_injective (A := Ω)
    dsimp only
    rw [IntertwiningMap.baseChange_comp, IntertwiningMap.baseChange_id]
    refine DFunLike.ext _ _ fun x ↦ ?_
    apply EquivLike.injective (ρ.baseChangeTransEquiv E' Ω)
    have h1 := DFunLike.congr_fun hg' (f'.baseChange Ω x)
    have h2 := DFunLike.congr_fun hf' x
    simp only [IntertwiningMap.comp_apply, Equiv.coe_toIntertwiningMap,
      IntertwiningMap.id_apply] at h1 h2 ⊢
    rw [h1, h2, Equiv.symm_apply_apply]
  have hfg : f'.comp g' = IntertwiningMap.id _ := by
    apply IntertwiningMap.baseChange_injective (A := Ω)
    dsimp only
    rw [IntertwiningMap.baseChange_comp, IntertwiningMap.baseChange_id]
    refine DFunLike.ext _ _ fun x ↦ ?_
    apply EquivLike.injective (σ.baseChangeTransEquiv E' Ω)
    have h1 := DFunLike.congr_fun hf' (g'.baseChange Ω x)
    have h2 := DFunLike.congr_fun hg' x
    simp only [IntertwiningMap.comp_apply, Equiv.coe_toIntertwiningMap,
      IntertwiningMap.id_apply] at h1 h2 ⊢
    rw [h1, h2, Equiv.apply_symm_apply]
  let e' : (ρ.baseChange E').Equiv (σ.baseChange E') :=
    Equiv.mk (LinearEquiv.ofLinearMap f'.toLinearMap g'.toLinearMap
      (congrArg IntertwiningMap.toLinearMap hfg)
      (congrArg IntertwiningMap.toLinearMap hgf)) f'.isIntertwining'
  refine ⟨E', hE'_fin, e', Equiv.ext (funext fun x ↦ ?_)⟩
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [Equiv.trans_apply, map_add, hx, hy]
  | tmul ω y =>
    have hx := DFunLike.congr_fun hf' (ω ⊗ₜ y)
    have he' : e' y = f' y := rfl
    simpa [Equiv.trans_apply, Equiv.baseChange_tmul, he', IntertwiningMap.comp_apply,
      IntertwiningMap.baseChange_tmul] using hx

end Descent

end Representation
