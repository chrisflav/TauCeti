/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Module
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Lattice stabilizers and integral general linear groups

Let `R` be a commutative ring with fraction field `K`, and let `V` be a `K`-vector space. If `L`
is an `R`-submodule spanning `V` over `K` (in particular any full `R`-lattice), then every
`K`-linear automorphism of `V` stabilizing `L` restricts to an `R`-linear automorphism of `L`, and
conversely every `R`-linear automorphism of `L` extends uniquely to a `K`-linear automorphism of
`V` via localization (`Submodule.stabilizerMulEquivAut`).

When `L` is a full lattice equipped with a finite `R`-basis `b : Module.Basis ι R L`, composing
with `Module.Basis.toGL` identifies the stabilizer of `L` in `V ≃ₗ[K] V` with `GL ι R`
(`Module.Basis.stabilizerMulEquivGL`). In the extended `K`-basis `b.extendOfIsLattice K` of `V`,
this identification is compatible with `Matrix.GeneralLinearGroup.map (algebraMap R K)`
(`Module.Basis.map_stabilizerMulEquivGL`), so the image of the stabilizer in `GL ι K` is precisely
the range of `GL ι R → GL ι K` (`Module.Basis.map_toGL_stabilizer_eq_range_map`).

## Main definitions

* `Submodule.stabilizerMulEquivAut`: group isomorphism between the stabilizer of a spanning
  submodule `L` in `V ≃ₗ[K] V` and the `R`-linear automorphism group `L ≃ₗ[R] L`.
* `Module.Basis.stabilizerMulEquivGL`: group isomorphism between the stabilizer of a full lattice
  `L` in `V ≃ₗ[K] V` and `GL ι R` induced by an `R`-basis of `L`.

## Main statements

* `Module.Basis.map_stabilizerMulEquivGL`: mapping the `GL ι R`-matrix of a stabilizer element
  into `GL ι K` gives its matrix in the extended `K`-basis.
* `Module.Basis.mem_stabilizer_iff_toGL_extendOfIsLattice_mem_range_map`: an automorphism of `V`
  stabilizes `L` if and only if its matrix in `b.extendOfIsLattice K` lies in the image of
  `GL ι R`.
* `Module.Basis.map_toGL_stabilizer_eq_range_map`: the image of the stabilizer of `L` under
  `(b.extendOfIsLattice K).toGL` is the range of `Matrix.GeneralLinearGroup.map (algebraMap R K)`.
-/

public section

open scoped MatrixGroups Pointwise

namespace Submodule

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

variable (K) in
/-- **Restriction to a spanning submodule.** For an `R`-submodule `L` spanning `V` over the
fraction field `K` (in particular any full lattice), the stabilizer of `L` in `V ≃ₗ[K] V` is
isomorphic as a group to the `R`-linear automorphism group `L ≃ₗ[R] L`. -/
noncomputable def stabilizerMulEquivAut (L : Submodule R V)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃* (L ≃ₗ[R] L) :=
  have := IsDomain.of_faithfulSMul R K
  have := IsLattice.isLocalizedModule_subtype K L hL
  { toFun g :=
      have hg := TauCeti.mem_stabilizer_set_iff_mapsTo.mp g.2
      { toFun x := ⟨(g : V ≃ₗ[K] V) x, hg.1 x.2⟩
        invFun x := ⟨((g : V ≃ₗ[K] V)⁻¹ : V ≃ₗ[K] V) x, hg.2 x.2⟩
        left_inv x := Subtype.ext ((g : V ≃ₗ[K] V).symm_apply_apply x)
        right_inv x := Subtype.ext ((g : V ≃ₗ[K] V).apply_symm_apply x)
        map_add' x y := Subtype.ext (map_add (g : V ≃ₗ[K] V) (x : V) y)
        map_smul' r x := Subtype.ext (((g : V ≃ₗ[K] V).toLinearMap).map_smul_of_tower r (x : V)) }
    invFun e :=
      let f : V ≃ₗ[K] V := IsLocalizedModule.mapEquiv (nonZeroDivisors R) L.subtype L.subtype K e
      have hf (x : L) : f (x : V) = (e x : V) := by
        simpa [f] using IsLocalizedModule.map_apply (nonZeroDivisors R) L.subtype L.subtype
          e.toLinearMap x
      have hfinv (x : L) : (f⁻¹ : V ≃ₗ[K] V) (x : V) = (e.symm x : V) := by
        simpa [f] using IsLocalizedModule.map_apply (nonZeroDivisors R) L.subtype L.subtype
          e.symm.toLinearMap x
      ⟨f, TauCeti.mem_stabilizer_set_iff_mapsTo.mpr
        ⟨fun x hx ↦ by simp [LinearEquiv.smul_def, hf ⟨x, hx⟩],
         fun x hx ↦ by simp [LinearEquiv.smul_def, hfinv ⟨x, hx⟩]⟩⟩
    left_inv g := by
      apply Subtype.ext
      apply LinearEquiv.toLinearMap_injective
      refine LinearMap.ext_on hL fun x hx ↦ ?_
      change (IsLocalizedModule.mapEquiv (nonZeroDivisors R) L.subtype L.subtype K _ : V →ₗ[K] V)
        (L.subtype ⟨x, hx⟩) = (g : V ≃ₗ[K] V) x
      exact (IsLocalizedModule.map_apply (nonZeroDivisors R) L.subtype L.subtype _ ⟨x, hx⟩)
    right_inv e := by
      refine LinearEquiv.ext fun x ↦ Subtype.ext ?_
      simpa using IsLocalizedModule.map_apply (nonZeroDivisors R) L.subtype L.subtype
        e.toLinearMap x
    map_mul' g₁ g₂ := LinearEquiv.ext fun _ ↦ Subtype.ext rfl }

@[simp]
theorem coe_stabilizerMulEquivAut_apply (L : Submodule R V)
    (hL : Submodule.span K (L : Set V) = ⊤)
    (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) (x : L) :
    ((L.stabilizerMulEquivAut K hL g x : L) : V) = (g : V ≃ₗ[K] V) x :=
  (rfl)

@[simp]
theorem coe_stabilizerMulEquivAut_symm_apply (L : Submodule R V)
    (hL : Submodule.span K (L : Set V) = ⊤) (e : L ≃ₗ[R] L) (x : L) :
    ((L.stabilizerMulEquivAut K hL).symm e : V ≃ₗ[K] V) x = (e x : V) := by
  have := IsDomain.of_faithfulSMul R K
  have := IsLattice.isLocalizedModule_subtype K L hL
  simpa [stabilizerMulEquivAut] using
    IsLocalizedModule.map_apply (nonZeroDivisors R) L.subtype L.subtype e.toLinearMap x

end Submodule

namespace Module.Basis

variable {R K V ι : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [Fintype ι] [DecidableEq ι]

variable (K) in
/-- **Matrix form of the lattice stabilizer.** In an `R`-basis `b` of a full lattice `L ⊆ V`,
the stabilizer of `L` in `V ≃ₗ[K] V` is isomorphic as a group to `GL ι R`. -/
noncomputable def stabilizerMulEquivGL {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) :
    MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ≃* GL ι R :=
  (L.stabilizerMulEquivAut K (Submodule.IsLattice.span_eq_top (A := K) (M := L))).trans b.toGL

/-- Mapping the `GL ι R`-matrix of a stabilizer element into `GL ι K` gives its matrix in the
extended `K`-basis `b.extendOfIsLattice K`. -/
@[simp]
theorem map_stabilizerMulEquivGL {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (b.stabilizerMulEquivGL K g) =
      (b.extendOfIsLattice K).toGL (g : V ≃ₗ[K] V) := by
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, RingHom.mapMatrix_apply, Matrix.map_apply, stabilizerMulEquivGL,
    MulEquiv.trans_apply, coe_toGL, LinearMap.toMatrix_apply, LinearEquiv.coe_coe,
    extendOfIsLattice_apply]
  rw [← Submodule.coe_stabilizerMulEquivAut_apply L _ g (b j), extendOfIsLattice_repr_coe]

/-- The matrix in `b.extendOfIsLattice K` of an element of `GL ι R` acting through
`stabilizerMulEquivGL.symm` is the image of that matrix in `GL ι K`. -/
@[simp]
theorem toGL_extendOfIsLattice_stabilizerMulEquivGL_symm {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) (A : GL ι R) :
    (b.extendOfIsLattice K).toGL ((b.stabilizerMulEquivGL K).symm A : V ≃ₗ[K] V) =
      Matrix.GeneralLinearGroup.map (algebraMap R K) A := by
  simpa using (b.map_stabilizerMulEquivGL ((b.stabilizerMulEquivGL K).symm A)).symm

/-- The matrix in the extended `K`-basis of a stabilizer element is the entrywise `algebraMap`
image of its `GL ι R`-matrix. -/
theorem toMatrix_extendOfIsLattice_eq_map_stabilizerMulEquivGL {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) (g : MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)) :
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (g : V ≃ₗ[K] V) =
      ((b.stabilizerMulEquivGL K g : Matrix ι ι R)).map (algebraMap R K) := by
  simpa [Matrix.GeneralLinearGroup.map] using
    (congrArg Units.val (b.map_stabilizerMulEquivGL g)).symm

/-- An automorphism of `V` stabilizes a full lattice `L` if and only if its matrix in an extended
lattice basis lies in the image of `GL ι R → GL ι K`. -/
theorem mem_stabilizer_iff_toGL_extendOfIsLattice_mem_range_map {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) (g : V ≃ₗ[K] V) :
    g ∈ MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V) ↔
      (b.extendOfIsLattice K).toGL g ∈
        (Matrix.GeneralLinearGroup.map (n := ι) (algebraMap R K)).range := by
  constructor
  · intro hg
    exact ⟨b.stabilizerMulEquivGL K ⟨g, hg⟩, b.map_stabilizerMulEquivGL ⟨g, hg⟩⟩
  · rintro ⟨A, hA⟩
    have hEq : g = ((b.stabilizerMulEquivGL K).symm A : V ≃ₗ[K] V) :=
      (b.extendOfIsLattice K).toGL.injective (by simp [hA])
    exact hEq ▸ ((b.stabilizerMulEquivGL K).symm A).2

/-- The image of the stabilizer of a full lattice under `(b.extendOfIsLattice K).toGL` is the
range of `GL ι R → GL ι K`. -/
theorem map_toGL_stabilizer_eq_range_map {L : Submodule R V} [L.IsLattice K]
    (b : Module.Basis ι R L) :
    (MulAction.stabilizer (V ≃ₗ[K] V) (L : Set V)).map
        (b.extendOfIsLattice K).toGL.toMonoidHom =
      (Matrix.GeneralLinearGroup.map (n := ι) (algebraMap R K)).range := by
  ext M
  obtain ⟨g, rfl⟩ := (b.extendOfIsLattice K).toGL.surjective M
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, EmbeddingLike.apply_eq_iff_eq,
    exists_eq_right]
  exact b.mem_stabilizer_iff_toGL_extendOfIsLattice_mem_range_map g

end Module.Basis
