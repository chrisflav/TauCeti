/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.Algebra.Module.Lattice

/-!
# Lattices in the linear dual

The integral dual of an `R`-submodule of a `K`-module consists of the `K`-linear
functionals taking values in `R` on that submodule. This construction requires no
bilinear form on the ambient module. For the span of a finite basis it is the span
of the dual basis; in particular the dual of a free full lattice is a full lattice.

Precomposition carries integral duals contravariantly along lattice-preserving
linear maps. This is the linear-algebra input to contragredient actions on
admissible integral lattices.

Evaluation restricts to an `R`-valued pairing between the integral dual and the
submodule. Over a ring with fraction field `K`, this pairing is perfect for a free
full lattice: its integral dual is its `R`-linear dual, and in particular is again free.
The integral dual sends `c • N` to `c⁻¹ • N^∨`, turns sums into intersections and (for
free lattices) intersections into sums, reverses inclusions strictly on free full lattices,
and satisfies biduality: the canonical evaluation map `V ≃ₗ[K] V^∨∨` carries a free full
lattice `N` onto `(N^∨)^∨`.
-/

public section

namespace Submodule

variable {R K V W : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V]
  [AddCommGroup W] [Module K W] [Module R W]

variable (K) in
/-- The linear functionals taking values in the image of `R` on `N`.
No bilinear form or full-lattice hypothesis is required. -/
def dualLattice (N : Submodule R V) : Submodule R (Module.Dual K V) :=
  ⨅ x : N, (1 : Submodule R K).comap
    ((LinearMap.applyₗ (R := K) (M₂ := K) (x : V)).restrictScalars R)

/-- Membership in the integral dual is integrality of every evaluation on the original
submodule. -/
@[simp]
theorem mem_dualLattice (N : Submodule R V) (φ : Module.Dual K V) :
    φ ∈ N.dualLattice K ↔ ∀ x ∈ N, φ x ∈ (1 : Submodule R K) := by
  simp [dualLattice]

/-- A functional is integral on a span exactly when it is integral on the spanning set. -/
theorem mem_dualLattice_span_iff [IsScalarTower R K V] (s : Set V) (φ : Module.Dual K V) :
    φ ∈ (span R s).dualLattice K ↔ ∀ x ∈ s, φ x ∈ (1 : Submodule R K) := by
  refine ⟨fun hφ x hx ↦ (mem_dualLattice _ φ).mp hφ x (subset_span hx), fun h ↦ ?_⟩
  have : span R s ≤ (1 : Submodule R K).comap (φ.restrictScalars R) := span_le.mpr h
  exact (mem_dualLattice _ φ).mpr fun x hx ↦ this hx

variable (K) in
/-- Taking the integral dual reverses inclusions. -/
theorem dualLattice_antitone : Antitone (dualLattice (R := R) (V := V) K) := by
  intro M N h φ hφ
  exact (mem_dualLattice M φ).mpr fun x hx => (mem_dualLattice N φ).mp hφ x (h hx)

/-- Precomposition with a lattice-preserving map preserves the corresponding integral duals. -/
theorem dualMap_mem_dualLattice (M : Submodule R V) (N : Submodule R W)
    (f : V →ₗ[K] W) (hf : ∀ x ∈ M, f x ∈ N)
    {φ : Module.Dual K W} (hφ : φ ∈ N.dualLattice K) :
    f.dualMap φ ∈ M.dualLattice K := by
  exact (mem_dualLattice M _).mpr fun x hx => (mem_dualLattice N φ).mp hφ _ (hf x hx)

/-- The integral dual of the zero submodule is the entire dual space. -/
@[simp]
theorem dualLattice_bot : (⊥ : Submodule R V).dualLattice K = ⊤ := by
  ext φ
  simp only [mem_dualLattice, mem_bot, mem_one, forall_eq, map_zero, mem_top, iff_true]
  exact ⟨0, map_zero _⟩

/-- The integral dual of a sum of submodules is the intersection of their integral duals. -/
@[simp]
theorem dualLattice_sup (M N : Submodule R V) :
    (M ⊔ N).dualLattice K = M.dualLattice K ⊓ N.dualLattice K := by
  ext φ
  simp only [mem_dualLattice, mem_inf]
  refine ⟨fun h ↦ ⟨fun x hx ↦ h x (mem_sup_left hx), fun y hy ↦ h y (mem_sup_right hy)⟩,
    fun ⟨hM, hN⟩ z hz ↦ ?_⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup.mp hz
  rw [map_add]
  exact add_mem (hM x hx) (hN y hy)

open scoped Pointwise in
/-- **Homothety scaling of the integral dual**: scaling a submodule by a unit `c : Kˣ` scales its
integral dual by `c⁻¹`. -/
@[simp]
theorem dualLattice_smul [IsScalarTower R K V] (c : Kˣ) (N : Submodule R V) :
    (c • N).dualLattice K = c⁻¹ • N.dualLattice K := by
  ext φ
  simp only [mem_dualLattice, Units.smul_def, mem_smul_pointwise_iff_exists]
  constructor
  · intro hφ
    refine ⟨(c : K) • φ, fun x hx ↦ ?_, by rw [smul_smul, Units.inv_mul, one_smul]⟩
    have hcx : φ ((c : K) • x) ∈ (1 : Submodule R K) := hφ _ ⟨x, hx, rfl⟩
    simpa [map_smul] using hcx
  · rintro ⟨ψ, hψ, rfl⟩ _ ⟨x, hx, rfl⟩
    have h := hψ x hx
    simpa [map_smul, ← mul_assoc] using h

/-- Under evaluation at `1`, the integral dual of `1 : Submodule R K` is `1 : Submodule R K`. -/
@[simp]
theorem map_eval_one_dualLattice_one :
    ((1 : Submodule R K).dualLattice K).map ((Module.Dual.eval K K 1).restrictScalars R) =
      (1 : Submodule R K) := by
  apply le_antisymm
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (mem_dualLattice _ φ).mp hφ 1 (mem_one.mpr ⟨1, map_one _⟩)
  · intro x hx
    refine ⟨x • LinearMap.id, (mem_dualLattice _ _).mpr fun y hy ↦ ?_, by simp⟩
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    obtain ⟨s, rfl⟩ := mem_one.mp hy
    exact mem_one.mpr ⟨r * s, by simp [Algebra.smul_def]⟩

end Submodule

namespace Module.Basis

variable {R K V ι : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [Finite ι] [DecidableEq ι]

/-- The integral dual of a basis lattice is the lattice spanned by the dual basis. -/
@[simp]
theorem dualLattice_span (b : Basis ι K V) :
    (Submodule.span R (Set.range b)).dualLattice K =
      Submodule.span R (Set.range b.dualBasis) := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · intro φ hφ
    rw [← b.dualBasis.sum_repr φ]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [dualBasis_repr]
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp
      ((Submodule.mem_dualLattice _ _).mp hφ _ (Submodule.subset_span ⟨i, rfl⟩))
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine (Submodule.mem_dualLattice _ _).mpr ?_
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      simp only [dualBasis_apply_self]
      split
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => simp
    | add x y _ _ hx hy => simpa using (1 : Submodule R K).add_mem hx hy
    | smul r x _ hx => simpa using (1 : Submodule R K).smul_mem r hx

end Module.Basis

namespace Submodule

variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- The integral dual of a free full lattice is again a full lattice. -/
instance isLattice_dualLattice (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    (N.dualLattice K).IsLattice K := by
  classical
  let b := Module.Free.chooseBasis R N
  rw [← b.span_range_extendOfIsLattice (K := K), (b.extendOfIsLattice K).dualLattice_span]
  exact isLattice_span (Set.finite_range _) (b.extendOfIsLattice K).dualBasis.span_eq

section Pairing

variable {R K V : Type*} [CommRing R] [CommRing K] [Algebra R K] [FaithfulSMul R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

variable (K) in
/-- The `R`-valued evaluation pairing between the integral dual of `N` and `N`. -/
noncomputable def dualLatticePairing (N : Submodule R V) :
    N.dualLattice K →ₗ[R] N →ₗ[R] R :=
  LinearMap.restrictScalarsRange₂ (N.dualLattice K).subtype N.subtype (Algebra.linearMap R K)
    (FaithfulSMul.algebraMap_injective R K) LinearMap.id fun φ x ↦
      Submodule.mem_one.mp ((mem_dualLattice N _).mp φ.2 x x.2)

/-- The integral pairing is evaluation, read back in `K`. -/
@[simp]
theorem algebraMap_dualLatticePairing (N : Submodule R V) (φ : N.dualLattice K) (x : N) :
    algebraMap R K (N.dualLatticePairing K φ x) = (φ : Module.Dual K V) x :=
  LinearMap.restrictScalarsRange₂_apply (N.dualLattice K).subtype N.subtype (Algebra.linearMap R K)
    (FaithfulSMul.algebraMap_injective R K) LinearMap.id _ φ x

end Pairing

section PerfectPairing

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- **The integral dual of a free full lattice is its `R`-linear dual.** Evaluation pairs the
integral dual of `N` perfectly with `N`: every `R`-linear functional on `N` extends uniquely to a
`K`-linear functional on the ambient space. -/
instance isPerfPair_dualLatticePairing (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    (N.dualLatticePairing K).IsPerfPair := by
  refine .of_bijective _ ⟨fun φ ψ h ↦ ?_, fun g ↦ ?_⟩
  · refine Subtype.ext <| LinearMap.ext_on (IsLattice.span_eq_top (A := K) (M := N))
      fun x hx ↦ ?_
    simpa using congr(algebraMap R K ($h ⟨x, hx⟩))
  · -- Extend `g` along the `K`-basis of `V` given by an `R`-basis of `N`.
    let b := Module.Free.chooseBasis R N
    let φ : Module.Dual K V := (b.extendOfIsLattice K).constr K fun i ↦ algebraMap R K (g (b i))
    have hφ (x : N) : φ x = algebraMap R K (g x) := by
      have : (φ.restrictScalars R).comp N.subtype = (Algebra.linearMap R K).comp g :=
        b.ext fun i ↦ by
          rw [LinearMap.comp_apply, Submodule.subtype_apply,
            ← Module.Basis.extendOfIsLattice_apply K b, LinearMap.restrictScalars_apply,
            Module.Basis.constr_basis, LinearMap.comp_apply, Algebra.linearMap_apply]
      exact congr($this x)
    refine ⟨⟨φ, (mem_dualLattice N φ).mpr fun x hx ↦
      Submodule.mem_one.mpr ⟨g ⟨x, hx⟩, (hφ ⟨x, hx⟩).symm⟩⟩, LinearMap.ext fun x ↦ ?_⟩
    apply FaithfulSMul.algebraMap_injective R K
    simp [hφ]

/-- **The integral dual of a free full lattice is free.** It is isomorphic to the `R`-linear dual
of `N` via the perfect pairing `dualLatticePairing`. -/
instance free_dualLattice (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    Module.Free R (N.dualLattice K) := by
  classical
  have := IsDomain.of_faithfulSMul R K
  have : Finite (Module.Free.ChooseBasisIndex R N) :=
    Module.Finite.finite_basis (Module.Free.chooseBasis R N)
  exact Module.Free.of_basis
    ((Module.Free.chooseBasis R N).dualBasis.map (N.dualLatticePairing K).toPerfPair.symm)

/-- **Biduality for free full lattices.** The canonical evaluation equivalence `V ≃ₗ[K] V^∨∨`
carries a free full lattice `N` onto its double integral dual `(N^∨)^∨`. -/
theorem map_evalEquiv_eq_dualLattice_dualLattice [Module.IsReflexive K V]
    (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    N.map ((Module.evalEquiv K V).toLinearMap.restrictScalars R) =
      (N.dualLattice K).dualLattice K := by
  classical
  have := IsDomain.of_faithfulSMul R K
  let b := Module.Free.chooseBasis R N
  let e := b.extendOfIsLattice K
  have : Finite (Module.Free.ChooseBasisIndex R N) := Module.Finite.finite_basis b
  have heval : ((Module.evalEquiv K V).toLinearMap.restrictScalars R ∘ e) = e.dualBasis.dualBasis :=
    funext fun i ↦ e.dualBasis.ext fun j ↦ by simp
  rw [← b.span_range_extendOfIsLattice (K := K), e.dualLattice_span, e.dualBasis.dualLattice_span,
    map_span, ← Set.range_comp, heval]

/-- **Taking the integral dual strictly reverses inclusion on free full lattices.** -/
theorem dualLattice_le_dualLattice_iff (M N : Submodule R V)
    [M.IsLattice K] [Module.Free R M] [N.IsLattice K] [Module.Free R N] :
    N.dualLattice K ≤ M.dualLattice K ↔ M ≤ N := by
  refine ⟨fun h ↦ ?_, fun h ↦ dualLattice_antitone K h⟩
  have := Module.Finite.of_isLattice (A := K) M
  have h2 := dualLattice_antitone K h
  rw [← map_evalEquiv_eq_dualLattice_dualLattice M,
    ← map_evalEquiv_eq_dualLattice_dualLattice N] at h2
  intro x hx
  have hx' : Module.evalEquiv K V x ∈
      N.map ((Module.evalEquiv K V).toLinearMap.restrictScalars R) :=
    h2 (mem_map_of_mem hx)
  obtain ⟨y, hy, hyx⟩ := hx'
  exact (Module.evalEquiv K V).injective hyx ▸ hy

/-- **The integral dual determines a free full lattice uniquely.** -/
theorem dualLattice_eq_dualLattice_iff (M N : Submodule R V)
    [M.IsLattice K] [Module.Free R M] [N.IsLattice K] [Module.Free R N] :
    M.dualLattice K = N.dualLattice K ↔ M = N := by
  simp only [le_antisymm_iff, dualLattice_le_dualLattice_iff, and_comm]

/-- **The integral dual turns intersections into sums** for free full lattices whose intersection
and dual sum are free full lattices (in particular for any two lattices over a principal ideal
domain). -/
theorem dualLattice_inf (M N : Submodule R V)
    [M.IsLattice K] [Module.Free R M] [N.IsLattice K] [Module.Free R N]
    [(M ⊓ N).IsLattice K] [Module.Free R (M ⊓ N : Submodule R V)]
    [Module.Free R (M.dualLattice K ⊔ N.dualLattice K : Submodule R (Module.Dual K V))] :
    (M ⊓ N).dualLattice K = M.dualLattice K ⊔ N.dualLattice K := by
  have := IsDomain.of_faithfulSMul R K
  have := Module.Finite.of_isLattice (A := K) M
  rw [← dualLattice_eq_dualLattice_iff (K := K), dualLattice_sup,
    ← map_evalEquiv_eq_dualLattice_dualLattice (M ⊓ N),
    ← map_evalEquiv_eq_dualLattice_dualLattice M,
    ← map_evalEquiv_eq_dualLattice_dualLattice N]
  exact map_inf _ (Module.evalEquiv K V).injective

end PerfectPairing

end Submodule
