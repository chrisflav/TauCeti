/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.LinearAlgebra.CliffordAlgebra.Classification
import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Metric
import TauCeti.LinearAlgebra.Matrix.TensorProduct
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Hurwitz–Radon systems and representations of `Cliff(0, r)`

A **Hurwitz–Radon system** of rank `r` on a real inner product space `E` is an `r`-tuple of
skew-adjoint linear isometry equivalences `J_0, …, J_{r-1} : E ≃ₗᵢ[ℝ] E` whose distinct pairs
anticommute:

* `⟪J_i x, y⟫ = -⟪x, J_i y⟫` for every `i` and `x, y ∈ E`;
* `J_i (J_j x) + J_j (J_i x) = 0` whenever `i ≠ j`.

Because each `J_i` is both isometric and skew-adjoint, `J_i² = -1`
(`HurwitzRadonSystem.op_op_self`), `J_i x` is orthogonal to `x`
(`HurwitzRadonSystem.inner_self_op`), and at every unit vector `x ∈ S(E)` the vectors
`J_0 x, …, J_{r-1} x` are pairwise orthonormal (`HurwitzRadonSystem.orthonormal_op_sphere`).

The universal property of `CliffordAlgebra (realCliffordForm 0 r)` identifies Hurwitz–Radon systems
on a finite-dimensional real inner product space `E` with algebraic `Cliff(0, r)`-module structures
of the same dimension:

* every `S : HurwitzRadonSystem E r` induces an `ℝ`-algebra homomorphism
  `S.cliffordAlgHom : CliffordAlgebra (realCliffordForm 0 r) →ₐ[ℝ] Module.End ℝ E`;
* conversely, any `Cliff(0, r)`-module `W` with `finrank ℝ W = finrank ℝ E` carries a
  monomial-group-invariant positive-definite symmetric bilinear form making Clifford generators
  skew-adjoint (`AlgHom.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι`), and transporting
  those generators along an orthonormal basis isomorphism `W ≃ₗᵢ[ℝ] E` produces a
  `HurwitzRadonSystem E r` (`TauCeti.nonempty_hurwitzRadonSystem_of_cliffordModule`).

Consequently, a finite-dimensional real inner product space `E` admits a rank-`r` Hurwitz–Radon
system if and only if it admits an algebraic `Cliff(0, r)`-representation
(`TauCeti.nonempty_hurwitzRadonSystem_iff_nonempty_algHom`). Combined with the classification of
`Cliff(0, 1) ≅ ℂ`, `Cliff(0, 3) ≅ ℍ × ℍ`, and `Cliff(0, 7) ≅ M₈(ℝ) × M₈(ℝ)`, every real inner
product space `E` of dimension `n + 1` with `n ∈ {0, 1, 3, 7}` admits a Hurwitz–Radon system of
rank `n` (`TauCeti.nonempty_hurwitzRadonSystem_of_eq`).

## Main definitions

* `TauCeti.HurwitzRadonSystem`: a rank-`r` system of skew-adjoint anticommuting linear isometries of
  a real inner product space `E`.
* `TauCeti.HurwitzRadonSystem.cliffordAlgHom`: the `Cliff(0, r)`-representation on `E` induced by a
  Hurwitz–Radon system.
* `TauCeti.HurwitzRadonSystem.zero`: the empty rank-`0` Hurwitz–Radon system on any `E`.

## Main results

* `TauCeti.HurwitzRadonSystem.orthonormal_op_sphere`: for `x ∈ sphere (0 : E) 1`, the vectors
  `i ↦ S.op i x` are orthonormal in `E` and orthogonal to `x`.
* `TauCeti.nonempty_hurwitzRadonSystem_of_cliffordModule`: a `Cliff(0, r)`-module of dimension
  `finrank ℝ E` yields a `HurwitzRadonSystem E r`.
* `TauCeti.nonempty_hurwitzRadonSystem_iff_nonempty_algHom`: `HurwitzRadonSystem E r` is nonempty
  if and only if `CliffordAlgebra (realCliffordForm 0 r) →ₐ[ℝ] Module.End ℝ E` is nonempty.
* `TauCeti.nonempty_hurwitzRadonSystem_of_eq`: `Nonempty (HurwitzRadonSystem E n)` when
  `finrank ℝ E = n + 1` and `n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7`.

## References

* A. Hurwitz, *Über die Komposition der quadratischen Formen*, Math. Ann. **88** (1922), 1–25.
* J. Radon, *Lineare Scharen orthogonaler Matrizen*, Abh. Math. Sem. Univ. Hamburg **1** (1922),
  1–14.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989), Chapter I,
  §§4–5 and §7.
-/

public section

open CliffordAlgebra InnerProductSpace Metric Module
open scoped Quaternion

noncomputable section

namespace TauCeti

/-- A **Hurwitz–Radon system** of rank `r` on a real inner product space `E`: an `r`-tuple of
skew-adjoint linear isometry equivalences whose distinct pairs anticommute. -/
structure HurwitzRadonSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℕ) where
  /-- The `r` orthogonal operators on `E`. -/
  op : Fin r → (E ≃ₗᵢ[ℝ] E)
  /-- Each operator is skew-adjoint for the inner product of `E`. -/
  inner_op_left (i : Fin r) (x y : E) : inner ℝ (op i x) y = -inner ℝ x (op i y)
  /-- Distinct operators anticommute. -/
  op_op_add_swap {i j : Fin r} (hij : i ≠ j) (x : E) : op i (op j x) + op j (op i x) = 0

namespace HurwitzRadonSystem

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℕ}

/-- Two Hurwitz–Radon systems on `E` of rank `r` are equal if their operators agree pointwise. -/
@[ext]
theorem ext {S T : HurwitzRadonSystem E r} (h : ∀ i x, S.op i x = T.op i x) : S = T := by
  cases S; cases T
  congr
  funext i
  exact LinearIsometryEquiv.ext (h i)

/-- Every operator in a Hurwitz–Radon system squares to `-1`. -/
@[simp]
theorem op_op_self (S : HurwitzRadonSystem E r) (i : Fin r) (x : E) :
    S.op i (S.op i x) = -x := by
  refine ext_inner_right ℝ fun y ↦ ?_
  rw [S.inner_op_left, (S.op i).inner_map_map, inner_neg_left]

/-- Every operator in a Hurwitz–Radon system sends each vector `x` into `(ℝ ∙ x)ᗮ`. -/
@[simp]
theorem inner_self_op (S : HurwitzRadonSystem E r) (i : Fin r) (x : E) :
    inner ℝ x (S.op i x) = 0 := by
  have h := S.inner_op_left i x x
  rw [real_inner_comm] at h
  linarith

/-- Distinct operators in a Hurwitz–Radon system map any vector `x` to orthogonal vectors. -/
theorem inner_op_ne (S : HurwitzRadonSystem E r) {i j : Fin r} (hij : i ≠ j) (x : E) :
    inner ℝ (S.op i x) (S.op j x) = 0 := by
  have h1 := S.inner_op_left i x (S.op j x)
  have h2 := S.inner_op_left j x (S.op i x)
  have hsum : inner ℝ x (S.op i (S.op j x)) + inner ℝ x (S.op j (S.op i x)) = 0 := by
    rw [← inner_add_right, S.op_op_add_swap hij x, inner_zero_right]
  rw [real_inner_comm (S.op i x) (S.op j x)] at h2
  linarith

/-- Evaluating a Hurwitz–Radon system at a point of the unit sphere produces an orthonormal
`r`-tuple in `E`. -/
theorem orthonormal_op_sphere (S : HurwitzRadonSystem E r) (x : sphere (0 : E) 1) :
    Orthonormal ℝ (fun i ↦ S.op i (x : E)) := by
  refine ⟨fun i ↦ ?_, fun {i j} hij ↦ S.inner_op_ne hij x⟩
  rw [(S.op i).norm_map, Subtype.coe_prop x |> mem_sphere_zero_iff_norm.mp]

/-- The unique rank-`0` Hurwitz–Radon system on `E`. -/
def zero : HurwitzRadonSystem E 0 where
  op := Fin.elim0
  inner_op_left i := i.elim0
  op_op_add_swap {i} := i.elim0

instance : Unique (HurwitzRadonSystem E 0) where
  default := zero
  uniq _ := ext fun i ↦ i.elim0

private def cliffordLiftLinear (S : HurwitzRadonSystem E r) :
    (Fin (0 + r) → ℝ) →ₗ[ℝ] Module.End ℝ E :=
  ∑ i : Fin r,
    (LinearMap.proj (Fin.cast (zero_add r).symm i)).smulRight (S.op i).toLinearEquiv.toLinearMap

private theorem cliffordLiftLinear_sq (S : HurwitzRadonSystem E r) (v : Fin (0 + r) → ℝ) :
    S.cliffordLiftLinear v * S.cliffordLiftLinear v =
      algebraMap ℝ (Module.End ℝ E) (realCliffordForm 0 r v) := by
  ext x
  let c : Fin r → ℝ := fun i ↦ v (Fin.cast (zero_add r).symm i)
  have hLx (y : E) : S.cliffordLiftLinear v y = ∑ i : Fin r, c i • S.op i y := by
    simp [cliffordLiftLinear, c, LinearMap.sum_apply]
  have hexp : (S.cliffordLiftLinear v * S.cliffordLiftLinear v) x =
      ∑ i : Fin r, ∑ j : Fin r, (c i * c j) • S.op i (S.op j x) := by
    rw [mul_apply_eq_comp, hLx ((S.cliffordLiftLinear v) x)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hLx x, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, smul_smul]
  have hdouble : (S.cliffordLiftLinear v * S.cliffordLiftLinear v) x +
        (S.cliffordLiftLinear v * S.cliffordLiftLinear v) x =
      (realCliffordForm 0 r v • (1 : Module.End ℝ E)) x +
        (realCliffordForm 0 r v • (1 : Module.End ℝ E)) x := by
    rw [hexp]
    conv_lhs => rhs; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    have hdiag : (∑ i : Fin r, ((∑ j : Fin r, (c i * c j) • S.op i (S.op j x)) +
        ∑ j : Fin r, (c j * c i) • S.op j (S.op i x))) =
        ∑ i : Fin r, (-(c i * c i)) • (x + x) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_add_distrib, Finset.sum_eq_single i]
      · have hneg : -x + -x = -(x + x) := by abel
        rw [S.op_op_self, ← smul_add, hneg, smul_neg, neg_smul]
      · intro j _ hji
        rw [mul_comm (c j) (c i), ← smul_add, S.op_op_add_swap hji.symm x, smul_zero]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have hform : realCliffordForm 0 r v = ∑ i : Fin r, -(c i * c i) := by
      rw [realCliffordForm_apply]
      refine Fintype.sum_equiv (finCongr (zero_add r)) _ _ fun k ↦ ?_
      rw [realCliffordWeight_of_le (Nat.zero_le _), neg_one_mul]
      rfl
    rw [hdiag, ← Finset.sum_smul, ← hform, LinearMap.smul_apply, one_apply_eq_self, smul_add]
  calc (S.cliffordLiftLinear v * S.cliffordLiftLinear v) x
      = (2 : ℝ)⁻¹ • ((S.cliffordLiftLinear v * S.cliffordLiftLinear v) x +
          (S.cliffordLiftLinear v * S.cliffordLiftLinear v) x) := by
          rw [← two_smul ℝ, inv_smul_smul₀ two_ne_zero]
    _ = (2 : ℝ)⁻¹ • ((realCliffordForm 0 r v • (1 : Module.End ℝ E)) x +
          (realCliffordForm 0 r v • (1 : Module.End ℝ E)) x) := by rw [hdouble]
    _ = algebraMap ℝ (Module.End ℝ E) (realCliffordForm 0 r v) x := by
          rw [← two_smul ℝ, inv_smul_smul₀ two_ne_zero, Algebra.algebraMap_eq_smul_one]

/-- The `ℝ`-algebra homomorphism `Cliff(0, r) →ₐ[ℝ] End_ℝ(E)` sending the `i`-th negative coordinate
generator to `S.op i`. -/
def cliffordAlgHom (S : HurwitzRadonSystem E r) :
    CliffordAlgebra (realCliffordForm 0 r) →ₐ[ℝ] Module.End ℝ E :=
  CliffordAlgebra.lift (realCliffordForm 0 r) ⟨S.cliffordLiftLinear, S.cliffordLiftLinear_sq⟩

/-- On a generator `ι v`, `S.cliffordAlgHom` acts as the corresponding linear combination of the
operators `S.op i`. -/
theorem cliffordAlgHom_ι (S : HurwitzRadonSystem E r) (v : Fin (0 + r) → ℝ) (x : E) :
    S.cliffordAlgHom (ι (realCliffordForm 0 r) v) x =
      ∑ i : Fin r, v (Fin.cast (zero_add r).symm i) • S.op i x := by
  simp [cliffordAlgHom, cliffordLiftLinear, LinearMap.sum_apply]

/-- On the `i`-th standard basis generator, `S.cliffordAlgHom` evaluates to `S.op i`. -/
@[simp]
theorem cliffordAlgHom_ι_single (S : HurwitzRadonSystem E r) (i : Fin r) (x : E) :
    S.cliffordAlgHom (ι (realCliffordForm 0 r) (Pi.single (Fin.cast (zero_add r).symm i) 1)) x =
      S.op i x := by
  rw [cliffordAlgHom_ι, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : Fin.cast (zero_add r).symm j ≠ Fin.cast (zero_add r).symm i :=
      fun h ↦ hji ((Fin.cast_injective _) h)
    simp [Pi.single_eq_of_ne hne]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end Basic

end HurwitzRadonSystem

section CliffordModule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem nonempty_hurwitzRadonSystem_of_posDef_isSkewAdjoint [FiniteDimensional ℝ E] {r : ℕ}
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (hW : finrank ℝ W = finrank ℝ E)
    (ρ : CliffordAlgebra (realCliffordForm 0 r) →ₐ[ℝ] Module.End ℝ W)
    (B : LinearMap.BilinForm ℝ W) (hBpos : B.toQuadraticMap.PosDef) (hBsymm : B.IsSymm)
    (hBskew : ∀ v, B.IsSkewAdjoint (ρ (ι (realCliffordForm 0 r) v))) :
    Nonempty (HurwitzRadonSystem E r) := by
  let core : InnerProductSpace.Core ℝ W :=
    { inner x y := B x y
      conj_inner_symm x y := by simpa using hBsymm.eq y x
      re_inner_nonneg x := by simpa using hBpos.nonneg x
      add_left x y z := B.add_left x y z
      smul_left x y c := by simp
      definite x hx := hBpos.anisotropic x hx }
  let := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ W := InnerProductSpace.ofCore core.toCore
  have hinner (x y : W) : inner ℝ x y = B x y := (rfl)
  let eWE : W ≃ₗᵢ[ℝ] E :=
    ((stdOrthonormalBasis ℝ W).reindex (finCongr hW)).repr.trans (stdOrthonormalBasis ℝ E).repr.symm
  let u : Fin r → (Fin (0 + r) → ℝ) := fun i ↦ Pi.single (Fin.cast (zero_add r).symm i) 1
  have hQu (i : Fin r) : realCliffordForm 0 r (u i) = -1 :=
    realCliffordForm_single_one_of_le (Nat.zero_le _)
  let f : Fin r → (W →ₗ[ℝ] W) := fun i ↦ ρ (ι (realCliffordForm 0 r) (u i))
  have hf_sq (i : Fin r) (w : W) : f i (f i w) = -w := by
    dsimp only [f]
    rw [← mul_apply_eq_comp, comp_ι_sq_scalar, hQu i, map_neg, map_one,
      LinearMap.neg_apply, one_apply_eq_self]
  let JW : Fin r → (W ≃ₗᵢ[ℝ] W) := fun i ↦
    { toLinearEquiv := LinearEquiv.ofLinearMap (f i) (-f i)
        (LinearMap.ext fun w ↦ by simp [hf_sq]) (LinearMap.ext fun w ↦ by simp [hf_sq])
      norm_map' := fun w ↦ by
        rw [LinearEquiv.coe_ofLinearMap, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
          ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner, hinner]
        simpa [f, hQu i] using
          ρ.bilinForm_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply B (u i)
            (hBskew (u i)) w w }
  have hJW (i : Fin r) (w : W) : JW i w = f i w := (rfl)
  refine ⟨{
    op := fun i ↦ eWE.symm.trans ((JW i).trans eWE)
    inner_op_left := fun i x y ↦ by
      simp only [LinearIsometryEquiv.trans_apply]
      rw [← eWE.symm.inner_map_map, eWE.symm_apply_apply, hinner, hJW]
      have hsk := hBskew (u i) (eWE.symm x) (eWE.symm y)
      have hr : inner ℝ x (eWE (JW i (eWE.symm y))) = B (eWE.symm x) (f i (eWE.symm y)) := by
        rw [← eWE.symm.inner_map_map, eWE.symm_apply_apply, hinner, hJW]
      rw [hr]
      simpa only [f, Pi.neg_apply, map_neg] using hsk
    op_op_add_swap := fun {i j} hij x ↦ by
      simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
      rw [← map_add]
      have hortho : (realCliffordForm 0 r).IsOrtho (u i) (u j) :=
        isOrtho_realCliffordForm_single (fun h ↦ hij ((Fin.cast_injective _) h)) 1 1
      have hanti : JW i (JW j (eWE.symm x)) + JW j (JW i (eWE.symm x)) = 0 := by
        rw [hJW, hJW, hJW, hJW]
        simpa only [f, map_add, map_mul, map_zero, LinearMap.add_apply, LinearMap.zero_apply,
          mul_apply_eq_comp] using
          congrArg (fun a ↦ ρ a (eWE.symm x)) (ι_mul_ι_add_swap_of_isOrtho hortho)
      rw [hanti, map_zero] }⟩

/-- **Hurwitz–Radon system from a `Cliff(0, r)`-module.** Any `Cliff(0, r)`-module `W` of the same
finite dimension as `E` induces a rank-`r` Hurwitz–Radon system on `E`. -/
theorem nonempty_hurwitzRadonSystem_of_cliffordModule [FiniteDimensional ℝ E] {r : ℕ}
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (hW : finrank ℝ W = finrank ℝ E)
    (ρ : CliffordAlgebra (realCliffordForm 0 r) →ₐ[ℝ] Module.End ℝ W) :
    Nonempty (HurwitzRadonSystem E r) := by
  let bW : Module.Basis (Fin (finrank ℝ E)) ℝ W := Module.finBasisOfFinrankEq ℝ W hW
  let Q₀ : QuadraticForm ℝ W := (realCliffordForm (finrank ℝ E) 0).comp bW.equivFun.toLinearMap
  have hQ₀ : Q₀.PosDef := (posDef_realCliffordForm_zero (finrank ℝ E)).comp _ bW.equivFun.injective
  let bR : Module.Basis (Fin (0 + r)) ℝ (Fin (0 + r) → ℝ) := Pi.basisFun ℝ (Fin (0 + r))
  obtain ⟨B, hBpos, hBsymm, hBskew⟩ := ρ.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι bR
    (fun i j hij ↦ by simpa only [bR, Pi.basisFun_apply] using
      isOrtho_realCliffordForm_single hij 1 1)
    (fun i ↦ by simpa only [bR, Pi.basisFun_apply] using
      realCliffordForm_single_one_of_le (Nat.zero_le _))
    hQ₀
  exact nonempty_hurwitzRadonSystem_of_posDef_isSkewAdjoint hW ρ B hBpos hBsymm hBskew

/-- **Algebraic characterization of Hurwitz–Radon systems.** A finite-dimensional real inner product
space `E` admits a rank-`r` Hurwitz–Radon system if and only if `E` admits an `ℝ`-algebra
homomorphism from `Cliff(0, r)` to `End_ℝ(E)`. -/
theorem nonempty_hurwitzRadonSystem_iff_nonempty_algHom [FiniteDimensional ℝ E] (r : ℕ) :
    Nonempty (HurwitzRadonSystem E r) ↔
      Nonempty (CliffordAlgebra (realCliffordForm 0 r) →ₐ[ℝ] Module.End ℝ E) :=
  ⟨fun ⟨S⟩ ↦ ⟨S.cliffordAlgHom⟩,
    fun ⟨ρ⟩ ↦ nonempty_hurwitzRadonSystem_of_cliffordModule rfl ρ⟩

/-- **Existence of rank-`n` Hurwitz–Radon systems in dimensions `n + 1 ∈ {1, 2, 4, 8}`.** Every real
inner product space `E` of dimension `n + 1` with `n = 0, 1, 3, 7` admits `n` skew-adjoint
anticommuting linear isometries, induced respectively by the trivial system (`n = 0`), `ℂ`
(`Cliff(0, 1) ≅ ℂ`), `ℍ` (`Cliff(0, 3) ≅ ℍ × ℍ`), and `ℝ⁸` (`Cliff(0, 7) ≅ M₈(ℝ) × M₈(ℝ)`). -/
theorem nonempty_hurwitzRadonSystem_of_eq {n : ℕ} [FiniteDimensional ℝ E]
    (hE : finrank ℝ E = n + 1) (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (HurwitzRadonSystem E n) := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨HurwitzRadonSystem.zero⟩
  · exact nonempty_hurwitzRadonSystem_of_cliffordModule (W := ℂ)
      (Complex.finrank_real_complex.trans hE.symm)
      ((Algebra.lmul ℝ ℂ).comp realCliffordZeroOneEquivComplex.toAlgHom)
  · obtain ⟨e⟩ := realClifford_classification_of_residue_eq_three 0 3
      (by rw [realCliffordResidue_def])
    exact nonempty_hurwitzRadonSystem_of_cliffordModule (W := ℍ[ℝ])
      (Quaternion.finrank_eq_four.trans hE.symm)
      ((Algebra.lmul ℝ ℍ[ℝ]).comp
        ((Matrix.finOneAlgEquiv ℝ ℍ[ℝ]).symm.toAlgHom.comp ((AlgHom.fst ℝ _ _).comp e.toAlgHom)))
  · obtain ⟨e⟩ := realClifford_classification_of_residue_eq_seven 0 7
      (by rw [realCliffordResidue_def])
    have hfin8 : finrank ℝ (Fin 8 → ℝ) = finrank ℝ E := by
      rw [Module.finrank_fin_fun, hE]
    exact nonempty_hurwitzRadonSystem_of_cliffordModule (W := Fin 8 → ℝ) hfin8
      (Matrix.toLinAlgEquiv'.toAlgHom.comp ((AlgHom.fst ℝ _ _).comp e.toAlgHom))

end CliffordModule

end TauCeti
