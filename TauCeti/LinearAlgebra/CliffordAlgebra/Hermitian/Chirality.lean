/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Geometric
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
-- Private: orthonormal-basis orthogonality for `-‖v‖²` is used only inside frame proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Intrinsic chirality on real Clifford actions on complex modules

Let `V` be an oriented real inner product space of dimension `n`, `Q` a quadratic form on `V`, and
`ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S` a real Clifford action on a complex module `S`. Via
the complex-linear scalar extension `ρ.cliffordBaseChange ℂ` on
`CliffordAlgebra (Q.baseChange ℂ)`, the normalized complex volume element
`CliffordAlgebra.complexVolume Q o` acts on `S` by

  `ρ.cliffordBaseChange ℂ (complexVolume Q o) = i ^ ⌊(n + 1) / 2⌋ • ρ (volumeElement Q o)`.

In even dimension `n = 2ℓ` with `Q v = -‖v‖ ^ 2`, this operator equals
`i ^ ℓ • c(e₁) ⋯ c(e₂ₗ)` for every positively oriented orthonormal basis `e`, squares to `1`,
anticommutes with every real generator `c(v) = ρ (ι Q v)`, and decomposes `S = S⁺ ⊕ S⁻` into its
`+1`- and `-1`-eigenspaces. In rank zero (`n = 0`) for `positiveOrientation` it is `1` (so `S⁺ = ⊤`
and `S⁻ = ⊥`), and in dimension `4` it agrees with `ρ (CliffordAlgebra.chirality Q o)`, identifying
`S⁺` with `CliffordAlgebra.positiveHalfSpinors o ρ`.

When real vectors act skew-Hermitianly on `S`, `ρ.cliffordBaseChange ℂ (complexVolume Q o)` is
symmetric (and self-adjoint when `S` is finite-dimensional), so distinct eigenspaces are mutually
orthogonal. Under the full geometric convention `AlgHom.IsGeometricClifford`, the half-spinor
subspaces are exact orthogonal complements of one another (`(S⁺)ᗮ = S⁻` and `(S⁻)ᗮ = S⁺`) without
assuming finite-dimensionality or completeness of `S`, and in even dimension Clifford multiplication
by any unit vector restricts to a complex-linear isometric equivalence `S^μ ≃ₗᵢ[ℂ] S^{-μ}`.

## Main definitions

* `AlgHom.IsGeometricClifford.halfSpinIsometryEquiv`: in even dimension, Clifford multiplication by
  a unit vector as a complex-linear isometric equivalence between the `μ`- and `-μ`-eigenspaces of
  `ρ.cliffordBaseChange ℂ (complexVolume Q o)`.

## Main results

* `AlgHom.cliffordBaseChange_complexVolume`, `AlgHom.cliffordBaseChange_complexVolume_of_even`:
  `ρ_ℂ (complexVolume Q o) = i ^ ⌊(n + 1) / 2⌋ • ρ (volumeElement Q o)`.
* `AlgHom.cliffordBaseChange_complexVolume_eq_of_even`,
  `AlgHom.cliffordBaseChange_complexVolume_eq_prod_pairs`: positively oriented orthonormal frame
  formulas in dimension `2ℓ` under `Q v = -‖v‖ ^ 2`.
* `AlgHom.cliffordBaseChange_complexVolume_eq_chirality`,
  `AlgHom.eigenspace_cliffordBaseChange_complexVolume_eq_positiveHalfSpinors`: agreement with
  four-dimensional `CliffordAlgebra.chirality` and `CliffordAlgebra.positiveHalfSpinors`.
* `AlgHom.isCompl_eigenspace_cliffordBaseChange_complexVolume`,
  `AlgHom.map_ι_mem_eigenspace_cliffordBaseChange_complexVolume_neg`,
  `AlgHom.finrank_eigenspace_cliffordBaseChange_complexVolume_neg`: chirality direct-sum splitting,
  vector exchange of eigenspaces, and equal half-spin dimensions.
* `AlgHom.isSymmetric_cliffordBaseChange_complexVolume`,
  `AlgHom.isSelfAdjoint_cliffordBaseChange_complexVolume`: symmetry and self-adjointness of the
  chirality operator when real vectors act skew-Hermitianly.
* `AlgHom.IsGeometricClifford.orthogonal_eigenspace_cliffordBaseChange_complexVolume_one`,
  `AlgHom.IsGeometricClifford.orthogonal_eigenspace_cliffordBaseChange_complexVolume_neg_one`:
  `(S⁺)ᗮ = S⁻` and `(S⁻)ᗮ = S⁺` on any geometric Clifford module.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §12.1.2.
-/

public section

noncomputable section

open CliffordAlgebra Module
open scoped InnerProductSpace TensorProduct

namespace AlgHom

/-! ### Action of `complexVolume` through `cliffordBaseChange ℂ` -/

section Action

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} [AddCommGroup S] [Module ℂ S] [Module ℝ S] [IsScalarTower ℝ ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

section GeneralDim

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- The complexified action of `CliffordAlgebra.complexVolume Q o` is `i ^ ⌊(n + 1) / 2⌋` times the
real action of `CliffordAlgebra.volumeElement Q o`. -/
theorem cliffordBaseChange_complexVolume :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) • ρ (volumeElement Q o) := by
  rw [complexVolume_def, map_smul, cliffordBaseChange_ofBaseChangeAux]

/-- Reversing the orientation negates the operator `ρ.cliffordBaseChange ℂ (complexVolume Q o)`. -/
theorem cliffordBaseChange_complexVolume_neg_orientation :
    ρ.cliffordBaseChange ℂ (complexVolume Q (-o)) =
      -ρ.cliffordBaseChange ℂ (complexVolume Q o) := by
  rw [complexVolume_neg_orientation, map_neg]

/-- **Frame formula for `ρ.cliffordBaseChange ℂ (complexVolume Q o)`**: for any positively oriented
orthonormal basis `b` orthogonal for `Q`, the operator equals `i ^ ⌊(n + 1) / 2⌋ • c(b₁) ⋯ c(bₙ)`.
-/
theorem cliffordBaseChange_complexVolume_eq (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) •
        (((List.finRange n).map b).map fun v ↦ ρ (ι Q v)).prod := by
  rw [complexVolume_eq o b hb hQb, map_smul, map_list_prod, List.map_map]
  simp [Function.comp_def]

/-- For `Q v = -‖v‖ ^ 2`, `ρ.cliffordBaseChange ℂ (complexVolume Q o)` squares to `1`. -/
@[simp]
theorem cliffordBaseChange_complexVolume_mul_self (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) *
        ρ.cliffordBaseChange ℂ (complexVolume Q o) = 1 := by
  rw [← map_mul, complexVolume_mul_self o hQ, map_one]

/-- For `Q v = -‖v‖ ^ 2`, `ρ.cliffordBaseChange ℂ (complexVolume Q o)` is an involution on `S`. -/
theorem cliffordBaseChange_complexVolume_involutive (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    Function.Involutive (ρ.cliffordBaseChange ℂ (complexVolume Q o)) := fun ψ ↦ by
  have h := congr($(ρ.cliffordBaseChange_complexVolume_mul_self o hQ) ψ)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

/-- **In even dimension the chirality operator anticommutes with every real generator**:
`Γ * c(v) = -(c(v) * Γ)`. -/
theorem cliffordBaseChange_complexVolume_mul_map_ι_of_even (hn : Even n) (v : V) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) * ρ (ι Q v) =
      -(ρ (ι Q v) * ρ.cliffordBaseChange ℂ (complexVolume Q o)) := by
  rw [← ρ.cliffordBaseChange_ι_one_tmul ℂ v, ← map_mul, ← map_mul, ← map_neg,
    complexVolume_mul_ι_of_even o hn]

end GeneralDim

section EvenDim

variable {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ)] (o : Orientation ℝ V (Fin (2 * ℓ)))

/-- In dimension `2ℓ`, `ρ.cliffordBaseChange ℂ (complexVolume Q o) = i ^ ℓ • ρ (volumeElement Q o)`.
-/
theorem cliffordBaseChange_complexVolume_of_even :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) = Complex.I ^ ℓ • ρ (volumeElement Q o) := by
  rw [ρ.cliffordBaseChange_complexVolume o, show (2 * ℓ + 1) / 2 = ℓ by omega]

/-- **Frame formula in even dimension `2ℓ`**: when `Q v = -‖v‖ ^ 2`, for every positively oriented
orthonormal basis `b`,
`ρ.cliffordBaseChange ℂ (complexVolume Q o) = i ^ ℓ • c(b₀) ⋯ c(b_{2ℓ-1})`. -/
theorem cliffordBaseChange_complexVolume_eq_of_even (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V) (hb : b.toBasis.orientation = o) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) =
      Complex.I ^ ℓ • (((List.finRange (2 * ℓ)).map b).map fun v ↦ ρ (ι Q v)).prod := by
  rw [ρ.cliffordBaseChange_complexVolume_eq o b hb (b.isOrthoᵢ_associated hQ),
    show (2 * ℓ + 1) / 2 = ℓ by omega]

/-- **Adjacent-pair frame formula in even dimension `2ℓ`**: when `Q v = -‖v‖ ^ 2`, the chirality
operator factors as `i ^ ℓ` times the product of adjacent bivectors `c(b_{2k}) c(b_{2k+1})`. -/
theorem cliffordBaseChange_complexVolume_eq_prod_pairs (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V) (hb : b.toBasis.orientation = o) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) =
      Complex.I ^ ℓ • (List.ofFn fun k : Fin ℓ ↦
        ρ (ι Q (b ⟨2 * k, by omega⟩)) * ρ (ι Q (b ⟨2 * k + 1, by omega⟩))).prod := by
  rw [complexVolume_eq_prod_pairs b hb (b.isOrthoᵢ_associated hQ), map_smul, map_list_prod,
    List.map_ofFn]
  simp [Function.comp_def]

end EvenDim

section RankZero

variable [Fact (finrank ℝ V = 0)]

/-- **Rank zero**: for the positive orientation on a zero-dimensional space,
`ρ.cliffordBaseChange ℂ (complexVolume Q positiveOrientation) = 1`. -/
theorem cliffordBaseChange_complexVolume_positiveOrientation :
    ρ.cliffordBaseChange ℂ (complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0))) =
      1 := by
  rw [complexVolume_positiveOrientation, map_one]

/-- In rank zero for `positiveOrientation`, the `+1`-eigenspace of the chirality operator is `⊤`. -/
theorem eigenspace_cliffordBaseChange_complexVolume_positiveOrientation_one :
    (ρ.cliffordBaseChange ℂ
      (complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0)))).eigenspace 1 = ⊤ := by
  rw [ρ.cliffordBaseChange_complexVolume_positiveOrientation]
  ext ψ
  simp

/-- In rank zero for `positiveOrientation`, the `-1`-eigenspace of the chirality operator is `⊥`. -/
theorem eigenspace_cliffordBaseChange_complexVolume_positiveOrientation_neg_one :
    (ρ.cliffordBaseChange ℂ
      (complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0)))).eigenspace (-1) = ⊥ := by
  rw [ρ.cliffordBaseChange_complexVolume_positiveOrientation]
  ext ψ
  simp only [Module.End.mem_eigenspace_iff, one_apply_eq_self, neg_one_smul, Submodule.mem_bot]
  exact ⟨fun h ↦ (two_ne_zero : (2 : ℂ) ≠ 0).isUnit.smul_left_cancel.1
    (by rw [two_smul ℂ, smul_zero, ← add_eq_zero_iff_eq_neg.2 h]), fun h ↦ by simp [h]⟩

end RankZero

end Action

/-! ### Comparison with four-dimensional `CliffordAlgebra.chirality` -/

section FourDim

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} [AddCommGroup S] [Module ℂ S] [Module ℝ S] [IsScalarTower ℝ ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- **Four-dimensional comparison**: `ρ.cliffordBaseChange ℂ (complexVolume Q o)` agrees with the
real four-dimensional chirality action `ρ (chirality Q o)`. -/
theorem cliffordBaseChange_complexVolume_eq_chirality (o : Orientation ℝ V (Fin 4)) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) = ρ (chirality Q o) := by
  rw [← ofBaseChangeAux_chirality, cliffordBaseChange_ofBaseChangeAux]

/-- **Four-dimensional half-spinors**: the `+1`-eigenspace of
`ρ.cliffordBaseChange ℂ (complexVolume Q o)` coincides with
`CliffordAlgebra.positiveHalfSpinors o ρ`. -/
theorem eigenspace_cliffordBaseChange_complexVolume_eq_positiveHalfSpinors
    (o : Orientation ℝ V (Fin 4)) :
    (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace 1 = positiveHalfSpinors o ρ := by
  ext ψ
  simp [ρ.cliffordBaseChange_complexVolume_eq_chirality]

end FourDim

/-! ### Chirality eigenspaces `S^±` -/

section Eigenspaces

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))

section CompatibleModule

variable [AddCommGroup S] [Module ℂ S] [Module ℝ S] [IsScalarTower ℝ ℂ S]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- When a `CliffordAlgebra (Q.baseChange ℂ)`-module structure on `S` agrees with
`ρ.cliffordBaseChange ℂ`, `Algebra.lsmul ℂ ℂ S (complexVolume Q o)` equals
`ρ.cliffordBaseChange ℂ (complexVolume Q o)`. -/
theorem lsmul_complexVolume_eq_cliffordBaseChange
    (hsmul : ∀ (a : CliffordAlgebra (Q.baseChange ℂ)) (ψ : S),
      a • ψ = ρ.cliffordBaseChange ℂ a ψ) :
    Algebra.lsmul ℂ ℂ S (complexVolume Q o) = ρ.cliffordBaseChange ℂ (complexVolume Q o) :=
  LinearMap.ext fun ψ ↦ hsmul (complexVolume Q o) ψ

/-- Agreement of the `μ`-eigenspaces of `Algebra.lsmul ℂ ℂ S (complexVolume Q o)` and
`ρ.cliffordBaseChange ℂ (complexVolume Q o)` when the module action is induced by `ρ`. -/
theorem eigenspace_lsmul_complexVolume_eq
    (hsmul : ∀ (a : CliffordAlgebra (Q.baseChange ℂ)) (ψ : S),
      a • ψ = ρ.cliffordBaseChange ℂ a ψ) (μ : ℂ) :
    (Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace μ =
      (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace μ := by
  rw [ρ.lsmul_complexVolume_eq_cliffordBaseChange o hsmul]

end CompatibleModule

section AlgHomEigenspaces

variable [AddCommGroup S] [Module ℂ S] [Module ℝ S] [IsScalarTower ℝ ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- Reversing the orientation exchanges the `μ`- and `-μ`-eigenspaces of the chirality operator. -/
theorem eigenspace_cliffordBaseChange_complexVolume_neg_orientation (μ : ℂ) :
    (ρ.cliffordBaseChange ℂ (complexVolume Q (-o))).eigenspace μ =
      (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace (-μ) := by
  ext ψ
  simp only [cliffordBaseChange_complexVolume_neg_orientation, Module.End.mem_eigenspace_iff,
    LinearMap.neg_apply, neg_smul, neg_eq_iff_eq_neg]

/-- **Chirality direct-sum decomposition**: when `Q v = -‖v‖ ^ 2`, `S` is the internal direct sum of
the `+1`- and `-1`-eigenspaces of `ρ.cliffordBaseChange ℂ (complexVolume Q o)`. -/
theorem isCompl_eigenspace_cliffordBaseChange_complexVolume (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    IsCompl ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace 1)
      ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace (-1)) := by
  let : Module (CliffordAlgebra (Q.baseChange ℂ)) S :=
    Module.compHom S (ρ.cliffordBaseChange ℂ).toRingHom
  have hact (a : CliffordAlgebra (Q.baseChange ℂ)) (s : S) :
      a • s = ρ.cliffordBaseChange ℂ a s := rfl
  let : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S :=
    ⟨fun c a s ↦ by simp only [hact, map_smul, LinearMap.smul_apply]⟩
  rw [← ρ.eigenspace_lsmul_complexVolume_eq o hact 1,
    ← ρ.eigenspace_lsmul_complexVolume_eq o hact (-1)]
  exact isCompl_eigenspace_complexVolume o hQ

/-- **Real vectors exchange chirality eigenspaces in even dimension**: if `Γ ψ = μ • ψ`, then
`Γ (c(v) ψ) = (-μ) • c(v) ψ`. -/
theorem map_ι_mem_eigenspace_cliffordBaseChange_complexVolume_neg (hn : Even n) (v : V) {μ : ℂ}
    {ψ : S} (hψ : ψ ∈ (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace μ) :
    ρ (ι Q v) ψ ∈ (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace (-μ) := by
  let : Module (CliffordAlgebra (Q.baseChange ℂ)) S :=
    Module.compHom S (ρ.cliffordBaseChange ℂ).toRingHom
  have hact (a : CliffordAlgebra (Q.baseChange ℂ)) (s : S) :
      a • s = ρ.cliffordBaseChange ℂ a s := rfl
  let : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S :=
    ⟨fun c a s ↦ by simp only [hact, map_smul, LinearMap.smul_apply]⟩
  rw [← ρ.cliffordBaseChange_ι_one_tmul ℂ v, ← hact,
    ← ρ.eigenspace_lsmul_complexVolume_eq o hact]
  exact ι_smul_mem_eigenspace_complexVolume_neg o hn (1 ⊗ₜ v)
    ((ρ.eigenspace_lsmul_complexVolume_eq o hact μ).symm ▸ hψ)

/-- **Equal dimensions of opposite chirality eigenspaces**: in positive even dimension, for any
quadratic form `Q` and any `μ : ℂ`, the `-μ`- and `μ`-eigenspaces of
`ρ.cliffordBaseChange ℂ (complexVolume Q o)` have equal complex `finrank`. -/
theorem finrank_eigenspace_cliffordBaseChange_complexVolume_neg (hn : Even n) (hn0 : n ≠ 0)
    (μ : ℂ) :
    finrank ℂ ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace (-μ)) =
      finrank ℂ ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace μ) := by
  let : Module (CliffordAlgebra (Q.baseChange ℂ)) S :=
    Module.compHom S (ρ.cliffordBaseChange ℂ).toRingHom
  have hact (a : CliffordAlgebra (Q.baseChange ℂ)) (s : S) :
      a • s = ρ.cliffordBaseChange ℂ a s := rfl
  let : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S :=
    ⟨fun c a s ↦ by simp only [hact, map_smul, LinearMap.smul_apply]⟩
  rw [← ρ.eigenspace_lsmul_complexVolume_eq o hact (-μ),
    ← ρ.eigenspace_lsmul_complexVolume_eq o hact μ]
  exact finrank_eigenspace_complexVolume_neg o hn hn0 μ

/-- **Half-spinor dimension for a spinor module**: when `Q v = -‖v‖ ^ 2`, `n ≠ 0`, and
`ρ.cliffordBaseChange ℂ` is bijective, both half-spinor eigenspaces (`μ = ±1`) have dimension
`2 ^ (n / 2 - 1)`. -/
theorem finrank_eigenspace_cliffordBaseChange_complexVolume_of_bijective
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hbij : Function.Bijective (ρ.cliffordBaseChange ℂ)) (hn0 : n ≠ 0)
    {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace μ) = 2 ^ (n / 2 - 1) := by
  let : Module (CliffordAlgebra (Q.baseChange ℂ)) S :=
    Module.compHom S (ρ.cliffordBaseChange ℂ).toRingHom
  have hact (a : CliffordAlgebra (Q.baseChange ℂ)) (s : S) :
      a • s = ρ.cliffordBaseChange ℂ a s := rfl
  let : IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S :=
    ⟨fun c a s ↦ by simp only [hact, map_smul, LinearMap.smul_apply]⟩
  have hlsmul : Algebra.lsmul ℂ ℂ S = ρ.cliffordBaseChange ℂ :=
    AlgHom.ext fun a ↦ LinearMap.ext fun s ↦ rfl
  rw [← ρ.eigenspace_lsmul_complexVolume_eq o hact μ]
  exact finrank_eigenspace_complexVolume_of_bijective_lsmul o hQ (hlsmul ▸ hbij) hn0 hμ

end AlgHomEigenspaces

end Eigenspaces

/-! ### Self-adjointness and orthogonal chirality decomposition on Hermitian modules -/

section Hermitian

private theorem orthogonal_eigenspace_one_of_involutive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {T : Module.End ℂ E} (hT : T.IsSymmetric)
    (hinv : Function.Involutive T) :
    (T.eigenspace 1)ᗮ = T.eigenspace (-1) := by
  ext y
  rw [Submodule.mem_orthogonal, Module.End.mem_eigenspace_iff, neg_one_smul]
  refine ⟨fun hy ↦ ?_, fun hy x hx ↦ ?_⟩
  · have hx : y + T y ∈ T.eigenspace 1 := by
      rw [Module.End.mem_eigenspace_iff, one_smul, map_add, hinv y, add_comm]
    have h0 : ⟪y + T y, y⟫_ℂ = 0 := hy _ hx
    have h1 : ⟪y + T y, T y⟫_ℂ = 0 := by
      rw [← hT (y + T y) y, Module.End.mem_eigenspace_iff.1 hx, one_smul, h0]
    have hself : ⟪y + T y, y + T y⟫_ℂ = 0 := by rw [inner_add_right, h0, h1, add_zero]
    exact eq_neg_iff_add_eq_zero.2 (by rwa [add_comm, ← inner_self_eq_zero (𝕜 := ℂ)])
  · exact hT.orthogonalFamily_eigenspaces (by norm_num : (1 : ℂ) ≠ -1) ⟨x, hx⟩ ⟨y, by
      rwa [Module.End.mem_eigenspace_iff, neg_one_smul]⟩

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))

section Seminormed

variable [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- **Symmetry of `complexVolume`**: if real vectors act skew-Hermitianly under `ρ`, then
`ρ.cliffordBaseChange ℂ (complexVolume Q o)` is symmetric with respect to the complex inner product
(for any quadratic form `Q` and without assuming `S` is finite-dimensional). -/
theorem inner_cliffordBaseChange_complexVolume
    (hρ : ∀ (v : V) (x y : S), ⟪ρ (ι Q v) x, y⟫_ℂ = -⟪x, ρ (ι Q v) y⟫_ℂ) (x y : S) :
    ⟪ρ.cliffordBaseChange ℂ (complexVolume Q o) x, y⟫_ℂ =
      ⟪x, ρ.cliffordBaseChange ℂ (complexVolume Q o) y⟫_ℂ := by
  simpa only [conjStar_complexVolume] using
    ρ.inner_cliffordBaseChange_eq_conjStar hρ (complexVolume Q o) x y

/-- `LinearMap.IsSymmetric` form of `AlgHom.inner_cliffordBaseChange_complexVolume`. -/
theorem isSymmetric_cliffordBaseChange_complexVolume
    (hρ : ∀ (v : V) (x y : S), ⟪ρ (ι Q v) x, y⟫_ℂ = -⟪x, ρ (ι Q v) y⟫_ℂ) :
    (ρ.cliffordBaseChange ℂ (complexVolume Q o)).IsSymmetric :=
  ρ.inner_cliffordBaseChange_complexVolume o hρ

namespace IsGeometricClifford

variable {ρ} (hρ : ρ.IsGeometricClifford)
include hρ

/-- Under `AlgHom.IsGeometricClifford`, the chirality operator is symmetric. -/
theorem isSymmetric_cliffordBaseChange_complexVolume :
    (ρ.cliffordBaseChange ℂ (complexVolume Q o)).IsSymmetric :=
  ρ.isSymmetric_cliffordBaseChange_complexVolume o hρ.inner_map_ι_left

/-- **Clifford multiplication by a unit vector as an isometric equivalence of chirality
eigenspaces** in even dimension, with inverse `-c(u)`. -/
def halfSpinIsometryEquiv (hn : Even n) {u : V} (hu : ‖u‖ = 1) (μ : ℂ) :
    ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace μ) ≃ₗᵢ[ℂ]
      ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace (-μ)) where
  toFun ψ := ⟨ρ (ι Q u) ψ, ρ.map_ι_mem_eigenspace_cliffordBaseChange_complexVolume_neg o hn u ψ.2⟩
  invFun ψ := ⟨-ρ (ι Q u) ψ, neg_mem (by
    simpa only [neg_neg] using
      ρ.map_ι_mem_eigenspace_cliffordBaseChange_complexVolume_neg o hn u ψ.2)⟩
  map_add' x y := Subtype.ext (map_add (ρ (ι Q u)) (x : S) (y : S))
  map_smul' c x := Subtype.ext (map_smul (ρ (ι Q u)) c (x : S))
  left_inv x := Subtype.ext <| by
    simp [map_ι_apply_map_ι_apply, hρ.quadratic_eq_neg_norm_sq, hu]
  right_inv x := Subtype.ext <| by
    simp [map_ι_apply_map_ι_apply, hρ.quadratic_eq_neg_norm_sq, hu]
  norm_map' x := by
    simp [hρ.norm_map_ι_apply, hu]

/-- Coercion to `S` of `AlgHom.IsGeometricClifford.halfSpinIsometryEquiv`. -/
@[simp]
theorem coe_halfSpinIsometryEquiv_apply (hn : Even n) {u : V} (hu : ‖u‖ = 1) (μ : ℂ)
    (ψ : (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace μ) :
    (hρ.halfSpinIsometryEquiv o hn hu μ ψ : S) = ρ (ι Q u) ψ :=
  (rfl)

/-- Coercion to `S` of `(AlgHom.IsGeometricClifford.halfSpinIsometryEquiv).symm`. -/
@[simp]
theorem coe_halfSpinIsometryEquiv_symm_apply (hn : Even n) {u : V} (hu : ‖u‖ = 1) (μ : ℂ)
    (ψ : (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace (-μ)) :
    ((hρ.halfSpinIsometryEquiv o hn hu μ).symm ψ : S) = -ρ (ι Q u) ψ :=
  (rfl)

end IsGeometricClifford

end Seminormed

section Normed

variable [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- When real vectors act skew-Hermitianly under `ρ`, distinct eigenspaces of
`ρ.cliffordBaseChange ℂ (complexVolume Q o)` are mutually orthogonal. -/
theorem orthogonalFamily_eigenspaces_cliffordBaseChange_complexVolume
    (hρ : ∀ (v : V) (x y : S), ⟪ρ (ι Q v) x, y⟫_ℂ = -⟪x, ρ (ι Q v) y⟫_ℂ) :
    OrthogonalFamily ℂ
      (fun μ ↦ (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace μ)
      (fun μ ↦ ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace μ).subtypeₗᵢ) :=
  (ρ.isSymmetric_cliffordBaseChange_complexVolume o hρ).orthogonalFamily_eigenspaces

/-- Pointwise orthogonality of vectors in distinct chirality eigenspaces. -/
theorem inner_eq_zero_of_mem_eigenspace_cliffordBaseChange_complexVolume
    (hρ : ∀ (v : V) (x y : S), ⟪ρ (ι Q v) x, y⟫_ℂ = -⟪x, ρ (ι Q v) y⟫_ℂ)
    {μ ν : ℂ} (hμν : μ ≠ ν)
    {x : S} (hx : x ∈ (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace μ)
    {y : S} (hy : y ∈ (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace ν) :
    ⟪x, y⟫_ℂ = 0 :=
  ρ.orthogonalFamily_eigenspaces_cliffordBaseChange_complexVolume o hρ hμν ⟨x, hx⟩ ⟨y, hy⟩

section FiniteDimensional

variable [FiniteDimensional ℂ S]

/-- On a finite-dimensional complex inner product space, if real vectors act skew-adjointly under
`ρ`, then `ρ.cliffordBaseChange ℂ (complexVolume Q o)` equals its adjoint. -/
theorem adjoint_cliffordBaseChange_complexVolume
    (hρ : ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v)) :
    (ρ.cliffordBaseChange ℂ (complexVolume Q o)).adjoint =
      ρ.cliffordBaseChange ℂ (complexVolume Q o) := by
  simpa only [conjStar_complexVolume] using
    (ρ.adjoint_cliffordBaseChange_eq_conjStar_iff.mpr hρ) (complexVolume Q o)

/-- `IsSelfAdjoint` form of `AlgHom.adjoint_cliffordBaseChange_complexVolume`. -/
theorem isSelfAdjoint_cliffordBaseChange_complexVolume
    (hρ : ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v)) :
    IsSelfAdjoint (ρ.cliffordBaseChange ℂ (complexVolume Q o)) :=
  ρ.adjoint_cliffordBaseChange_complexVolume o hρ

end FiniteDimensional

namespace IsGeometricClifford

variable {ρ} (hρ : ρ.IsGeometricClifford)
include hρ

/-- Under `AlgHom.IsGeometricClifford` on a finite-dimensional module, the chirality operator is
self-adjoint. -/
theorem isSelfAdjoint_cliffordBaseChange_complexVolume [FiniteDimensional ℂ S] :
    IsSelfAdjoint (ρ.cliffordBaseChange ℂ (complexVolume Q o)) :=
  ρ.isSelfAdjoint_cliffordBaseChange_complexVolume o hρ.adjoint_map_ι

/-- **Exact orthogonal complement `(S⁺)ᗮ = S⁻`**: on any geometric Clifford module (without
assuming finite-dimensionality or completeness of `S`), the orthogonal complement of the
`+1`-eigenspace of `ρ.cliffordBaseChange ℂ (complexVolume Q o)` is the `-1`-eigenspace. -/
theorem orthogonal_eigenspace_cliffordBaseChange_complexVolume_one :
    ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace 1)ᗮ =
      (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace (-1) :=
  orthogonal_eigenspace_one_of_involutive
    (hρ.isSymmetric_cliffordBaseChange_complexVolume o)
    (ρ.cliffordBaseChange_complexVolume_involutive o hρ.quadratic_eq_neg_norm_sq)

/-- **Exact orthogonal complement `(S⁻)ᗮ = S⁺`**: on any geometric Clifford module, the orthogonal
complement of the `-1`-eigenspace of `ρ.cliffordBaseChange ℂ (complexVolume Q o)` is the
`+1`-eigenspace. -/
theorem orthogonal_eigenspace_cliffordBaseChange_complexVolume_neg_one :
    ((ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace (-1))ᗮ =
      (ρ.cliffordBaseChange ℂ (complexVolume Q o)).eigenspace 1 := by
  rw [← ρ.eigenspace_cliffordBaseChange_complexVolume_neg_orientation o 1,
    hρ.orthogonal_eigenspace_cliffordBaseChange_complexVolume_one (-o),
    ρ.eigenspace_cliffordBaseChange_complexVolume_neg_orientation, neg_neg]

end IsGeometricClifford

end Normed

end Hermitian

end AlgHom

end
