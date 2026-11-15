/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.TangentBundle
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame.Orthonormal
public import TauCeti.LinearAlgebra.CliffordAlgebra.Module.HurwitzRadon

/-!
# Clifford tangent frames, parallelizability of `S⁰, S¹, S³, S⁷`, and sphere H-space multiplications

Evaluating a rank-`r` Hurwitz–Radon system `S : HurwitzRadonSystem E r` along the unit sphere
`Sⁿ = sphere (0 : E) 1` of an `(n + 1)`-dimensional real inner product space `E` and lifting via
`TauCeti.sphereTangentialLift` produces `r` analytic (`C^ω`, hence `C^m` for every `m : ℕ∞ω`) vector
fields `S.tangentField n : Fin r → (x : Sⁿ) → TangentSpace (𝓡 n) x` that are orthonormal with
respect to `TauCeti.sphereRoundMetric` at every point
(`HurwitzRadonSystem.orthonormal_tangentField`). In particular `r ≤ n`
(`HurwitzRadonSystem.rank_le`).

When `r = n`, `S.tangentField n` is a global `C^m` orthonormal frame of `TangentSpace (𝓡 n)` over
`univ` (`HurwitzRadonSystem.isLocalFrameOn_tangentField`). Via
`IsLocalFrameOn.trivialization`, it induces a global linear trivialization
`S.tangentTrivialization m` of `TangentBundle (𝓡 n) Sⁿ` belonging to the `C^m` maximal vector-bundle
atlas (`HurwitzRadonSystem.tangentTrivialization_mem_maximalAtlas`), with inner-product fibre
coordinates `w ↦ (⟪S.tangentField n i x, w⟫)ᵢ`. Plugging `S.tangentField n` into
`TauCeti.sphereFrameMul` yields a `C^m` strict-unit H-space multiplication on `Sⁿ` given explicitly
by the bilinear Clifford/Cayley–Dickson formula
`μ(x, y) = ⟪e₀, y⟫ x + ∑ᵢ ⟪Jᵢ e₀, y⟫ Jᵢ x` (`HurwitzRadonSystem.coe_sphereFrameMul_tangentField`).

Combining this with `TauCeti.nonempty_hurwitzRadonSystem_of_eq` (from `Cliff(0, 1) ≅ ℂ`,
`Cliff(0, 3) ≅ ℍ × ℍ`, and `Cliff(0, 7) ≅ M₈(ℝ) × M₈(ℝ)`) proves that for `n ∈ {0, 1, 3, 7}`:

* `Sⁿ` admits a global `C^m` orthonormal tangent frame and a global compatible trivialization of
  `TangentBundle (𝓡 n) Sⁿ` (`TauCeti.exists_orthonormal_isLocalFrameOn_tangentSpace_sphere_of_eq`);
* `Sⁿ` admits a `C^m` multiplication `Sⁿ × Sⁿ → Sⁿ` with any chosen basepoint `e₀` as strict
  two-sided identity and bijective left translations (`TauCeti.exists_contMDiff_sphereMul_of_eq`);
* the Euclidean sphere `sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` is parallelizable
  (`TauCeti.exists_contMDiff_linearIndependent_tangentSpace_sphere_of_eq`).

## Main definitions

* `TauCeti.HurwitzRadonSystem.tangentField`: the `r` analytic orthonormal vector fields on `Sⁿ`
  associated to a rank-`r` Hurwitz–Radon system on `E`.
* `TauCeti.HurwitzRadonSystem.tangentTrivialization`: the global compatible trivialization of
  `TangentBundle (𝓡 n) Sⁿ` associated to a rank-`n` Hurwitz–Radon system.

## Main results

* `TauCeti.HurwitzRadonSystem.isLocalFrameOn_tangentField` and
  `TauCeti.HurwitzRadonSystem.tangentTrivialization_mem_maximalAtlas`: global `C^m` frame and
  compatible bundle trivialization from a rank-`n` Hurwitz–Radon system.
* `TauCeti.HurwitzRadonSystem.coe_sphereFrameMul_tangentField`: explicit bilinear formula for the
  induced strict-unit multiplication on `Sⁿ`.
* `TauCeti.exists_orthonormal_isLocalFrameOn_tangentSpace_sphere_of_eq`,
  `TauCeti.exists_contMDiff_sphereMul_of_eq`, and
  `TauCeti.exists_contMDiff_linearIndependent_tangentSpace_sphere_of_eq`: parallelizability and
  strict-unit H-space multiplications on `S⁰, S¹, S³, S⁷`.

## References

* J. F. Adams, *Vector fields on spheres*, Ann. of Math. (2) **75** (1962), 603–632.
* A. Hatcher, *Vector Bundles and K-Theory*, §§1.1 and 2.3.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989), Chapter I,
  §7 (vector fields on spheres from Clifford modules).
-/

public section

open Bundle InnerProductSpace Metric Module Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

namespace HurwitzRadonSystem

section VectorFields

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℕ}

/-- The `i`-th tangent vector field on `Sⁿ` induced by a Hurwitz–Radon system `S` on `E`, obtained
by tangentially lifting `x ↦ S.op i x`. -/
def tangentField (S : HurwitzRadonSystem E r) (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (i : Fin r) (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x :=
  sphereTangentialLift x (S.op i (x : E))

/-- `S.tangentField n i x` is defined by applying `TauCeti.sphereTangentialLift x` to `S.op i x`. -/
theorem tangentField_apply (S : HurwitzRadonSystem E r) (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (i : Fin r) (x : sphere (0 : E) 1) :
    S.tangentField n i x = sphereTangentialLift x (S.op i (x : E)) :=
  (rfl)

/-- Read back in the ambient space `E`, `S.tangentField n i x` is `S.op i x`. -/
theorem coe_sphereTangentEquiv_tangentField (S : HurwitzRadonSystem E r) (n : ℕ)
    [Fact (finrank ℝ E = n + 1)] (i : Fin r) (x : sphere (0 : E) 1) :
    (sphereTangentEquiv x (S.tangentField n i x) : E) = S.op i (x : E) :=
  coe_sphereTangentEquiv_sphereTangentialLift_of_inner_eq_zero (S.inner_self_op i x)

/-- Each vector field `S.tangentField n i` is `C^m` for every smoothness exponent `m` (including
`m = ω`). -/
theorem contMDiff_tangentField (S : HurwitzRadonSystem E r) (n : ℕ)
    [Fact (finrank ℝ E = n + 1)] (m : ℕ∞ω) (i : Fin r) :
    ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x ↦ (⟨x, S.tangentField n i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
  simp only [tangentField_apply]
  exact contMDiff_sphereTangentialLift (b := id) (u := fun x ↦ S.op i (x : E)) contMDiff_id
    ((S.op i).toLinearIsometry.toContinuousLinearMap.contDiff.comp_contMDiff contMDiff_coe_sphere)

/-- At every point `x ∈ Sⁿ`, the tangent vectors `i ↦ S.tangentField n i x` are orthonormal with
respect to `TauCeti.sphereRoundMetric`. -/
theorem orthonormal_tangentField (S : HurwitzRadonSystem E r) (n : ℕ)
    [Fact (finrank ℝ E = n + 1)] (x : sphere (0 : E) 1) :
    Orthonormal ℝ (fun i ↦ S.tangentField n i x) := by
  refine ⟨fun i ↦ ?_, fun {i j} hij ↦ ?_⟩
  · rw [← (sphereTangentEquiv x).norm_map, ← Submodule.norm_coe,
      coe_sphereTangentEquiv_tangentField]
    exact (S.orthonormal_op_sphere x).1 i
  · dsimp only
    rw [← (sphereTangentEquiv x).inner_map_map, Submodule.coe_inner,
      coe_sphereTangentEquiv_tangentField, coe_sphereTangentEquiv_tangentField]
    exact (S.orthonormal_op_sphere x).2 hij

/-- At every point `x ∈ Sⁿ`, the tangent vectors `i ↦ S.tangentField n i x` are linearly
independent. -/
theorem linearIndependent_tangentField (S : HurwitzRadonSystem E r) (n : ℕ)
    [Fact (finrank ℝ E = n + 1)] (x : sphere (0 : E) 1) :
    LinearIndependent ℝ (fun i ↦ S.tangentField n i x) :=
  (S.orthonormal_tangentField n x).linearIndependent

private theorem finrank_tangentSpace_sphere (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (x : sphere (0 : E) 1) : finrank ℝ (TangentSpace (𝓡 n) x) = n :=
  (sphereTangentEquiv (n := n) x).toLinearEquiv.finrank_eq.trans
    (Submodule.finrank_orthogonal_span_singleton (n := n) (ne_zero_of_mem_unit_sphere x))

/-- The rank `r` of a Hurwitz–Radon system on an `(n + 1)`-dimensional real inner product space is
at most `n`. -/
theorem rank_le (S : HurwitzRadonSystem E r) (n : ℕ) [Fact (finrank ℝ E = n + 1)] : r ≤ n := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  let bE := stdOrthonormalBasis ℝ E
  let x₀ : sphere (0 : E) 1 := ⟨bE ⟨0, by
    rw [Fact.out (p := finrank ℝ E = n + 1)]
    exact Nat.succ_pos n⟩, by rw [mem_sphere_zero_iff_norm, bE.orthonormal.1]⟩
  simpa [finrank_tangentSpace_sphere] using
    (S.linearIndependent_tangentField n x₀).fintype_card_le_finrank

end VectorFields

section GlobalFrame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A rank-`n` Hurwitz–Radon system on `E` defines a global `C^m` frame of `TangentSpace (𝓡 n)`
over `univ ⊆ Sⁿ`. -/
theorem isLocalFrameOn_tangentField (S : HurwitzRadonSystem E n) (m : ℕ∞ω) :
    IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) m (S.tangentField n) univ where
  linearIndependent _ := S.linearIndependent_tangentField n _
  generating {x} _ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · let eT := (trivializationAt (EuclideanSpace ℝ (Fin 0)) (TangentSpace (𝓡 0)) x).linearEquivAt
        ℝ x (FiberBundle.mem_baseSet_trivializationAt' x)
      intro v _
      have hv : v = 0 := eT.injective (by ext i; exact i.elim0)
      rw [hv]
      exact Submodule.zero_mem _
    · let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact le_of_eq
        ((S.linearIndependent_tangentField n x).span_eq_top_of_card_eq_finrank
          ((Fintype.card_fin n).trans (finrank_tangentSpace_sphere n x).symm)).symm
  contMDiffOn i := (S.contMDiff_tangentField n m i).contMDiffOn

/-- The global linear trivialization of `TangentBundle (𝓡 n) Sⁿ` induced by a rank-`n`
Hurwitz–Radon system `S` and the standard orthonormal basis of `EuclideanSpace ℝ (Fin n)`. -/
def tangentTrivialization (S : HurwitzRadonSystem E n) (m : ℕ∞ω) :
    Trivialization (EuclideanSpace ℝ (Fin n))
      (π (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)) :=
  (S.isLocalFrameOn_tangentField m).trivialization isOpen_univ
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- `S.tangentTrivialization m` is globally defined on `univ`. -/
@[simp]
theorem baseSet_tangentTrivialization (S : HurwitzRadonSystem E n) (m : ℕ∞ω) :
    (S.tangentTrivialization m).baseSet = univ :=
  (S.isLocalFrameOn_tangentField m).baseSet_trivialization isOpen_univ _

/-- `S.tangentTrivialization m` is fibrewise `ℝ`-linear. -/
instance isLinear_tangentTrivialization (S : HurwitzRadonSystem E n) (m : ℕ∞ω) :
    (S.tangentTrivialization m).IsLinear ℝ := by
  rw [tangentTrivialization]
  infer_instance

/-- `S.tangentTrivialization m` belongs to the `C^m` maximal vector-bundle atlas of
`TangentBundle (𝓡 n) Sⁿ`. -/
theorem tangentTrivialization_mem_maximalAtlas (S : HurwitzRadonSystem E n) (m : ℕ∞ω) :
    letI : IsManifold (𝓡 n) (m + 1) (sphere (0 : E) 1) := IsManifold.of_le (n := ω) le_top
    (S.tangentTrivialization m).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) (𝓡 n) m).maximalAtlas
        (TangentBundle (𝓡 n) (sphere (0 : E) 1)) := by
  let _ : IsManifold (𝓡 n) (m + 1) (sphere (0 : E) 1) := IsManifold.of_le (n := ω) le_top
  exact (S.isLocalFrameOn_tangentField m).trivialization_mem_maximalAtlas isOpen_univ _

/-- The `i`-th coordinate of a tangent vector `w` in `S.tangentTrivialization m` is the round inner
product `⟪S.tangentField n i x, w⟫`. -/
@[simp]
theorem tangentTrivialization_apply_ofLp (S : HurwitzRadonSystem E n) (m : ℕ∞ω)
    (x : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) x) (i : Fin n) :
    ((S.tangentTrivialization m ⟨x, w⟩).2).ofLp i = inner ℝ (S.tangentField n i x) w := by
  let hs := S.isLocalFrameOn_tangentField m
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have htriv : (S.tangentTrivialization m ⟨x, w⟩).2 =
      (hs.toBasisAt (mem_univ x)).equiv b (Equiv.refl (Fin n)) w :=
    congrArg Prod.snd (hs.trivialization_apply isOpen_univ b (mem_univ x) w)
  have hb (z : EuclideanSpace ℝ (Fin n)) : z.ofLp i = b.repr z i := by
    simp [b]
  have hrepr : b.repr ((hs.toBasisAt (mem_univ x)).equiv b (Equiv.refl (Fin n)) w) i =
      hs.coeff i x w := by
    conv_lhs => rw [← (hs.toBasisAt (mem_univ x)).sum_repr w]
    simp only [map_sum, map_smul, Module.Basis.equiv_apply, Equiv.refl_apply,
      Module.Basis.repr_self]
    simp [IsLocalFrameOn.coeff]
  rw [htriv, hb, hrepr]
  exact hs.coeff_eq_inner (mem_univ x) (S.orthonormal_tangentField n x) i w

/-- The inverse of `S.tangentTrivialization m` at `x` expands `y : EuclideanSpace ℝ (Fin n)` in the
orthonormal frame `S.tangentField n · x`. -/
@[simp]
theorem tangentTrivialization_symm_apply (S : HurwitzRadonSystem E n) (m : ℕ∞ω)
    (x : sphere (0 : E) 1) (y : EuclideanSpace ℝ (Fin n)) :
    (S.tangentTrivialization m).symm x y = ∑ i : Fin n, y.ofLp i • S.tangentField n i x := by
  rw [tangentTrivialization,
    (S.isLocalFrameOn_tangentField m).trivialization_symm_apply isOpen_univ _ (mem_univ x) y]
  simp

/-- Because `S.tangentField n` is already orthonormal, Gram–Schmidt leaves it unchanged, so the
`(i + 1)`-th vector of `TauCeti.sphereFrameOrthonormalBasis` is simply `S.op i x`. -/
theorem sphereFrameOrthonormalBasis_tangentField_succ (S : HurwitzRadonSystem E n)
    (x : sphere (0 : E) 1) (i : Fin n) :
    sphereFrameOrthonormalBasis (S.tangentField n) (S.linearIndependent_tangentField n) x i.succ =
      S.op i (x : E) := by
  have hgs : gramSchmidtNormed ℝ (fun j ↦ S.tangentField n j x) i = S.tangentField n i x := by
    rw [gramSchmidtNormed, gramSchmidt_of_orthogonal ℝ (S.orthonormal_tangentField n x).2,
      (S.orthonormal_tangentField n x).1 i]
    simp
  rw [sphereFrameOrthonormalBasis_succ, hgs, coe_sphereTangentEquiv_tangentField]

/-- **Explicit bilinear formula for the Clifford H-space multiplication on `Sⁿ`.** Evaluated on the
orthonormal tangent frame of `S`, `TauCeti.sphereFrameMul` multiplies `x, y ∈ Sⁿ` via
`⟪e₀, y⟫ x + ∑ᵢ ⟪S.op i e₀, y⟫ S.op i x`. -/
theorem coe_sphereFrameMul_tangentField (S : HurwitzRadonSystem E n)
    (e₀ x y : sphere (0 : E) 1) :
    ((sphereFrameMul e₀ (S.tangentField n) (S.linearIndependent_tangentField n) x y :
      sphere (0 : E) 1) : E) =
      inner ℝ (e₀ : E) (y : E) • (x : E) +
        ∑ i : Fin n, inner ℝ (S.op i (e₀ : E)) (y : E) • S.op i (x : E) := by
  rw [coe_sphereFrameMul, sphereFrameIsometry_apply, Fin.sum_univ_succ,
    sphereFrameOrthonormalBasis_zero, sphereFrameOrthonormalBasis_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sphereFrameOrthonormalBasis_tangentField_succ, sphereFrameOrthonormalBasis_tangentField_succ]

end GlobalFrame

end HurwitzRadonSystem

section DivisionAlgebraSpheres

/-- **Global orthonormal tangent frames and trivializations on `S⁰, S¹, S³, S⁷`.** For any
`(n + 1)`-dimensional real inner product space `E` with `n ∈ {0, 1, 3, 7}` and any `m : ℕ∞ω`, the
unit sphere `Sⁿ` admits a global `C^m` orthonormal tangent frame and a global trivialization in the
`C^m` maximal vector-bundle atlas of `TangentBundle (𝓡 n) Sⁿ`. -/
theorem exists_orthonormal_isLocalFrameOn_tangentSpace_sphere_of_eq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) (m : ℕ∞ω) :
    letI : IsManifold (𝓡 n) (m + 1) (sphere (0 : E) 1) := IsManifold.of_le (n := ω) le_top
    ∃ (v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
      (e : Trivialization (EuclideanSpace ℝ (Fin n))
        (π (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _))),
      IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) m v univ ∧
      (∀ x, Orthonormal ℝ (fun i ↦ v i x)) ∧
      e.baseSet = univ ∧
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) (𝓡 n)
          m).maximalAtlas (TangentBundle (𝓡 n) (sphere (0 : E) 1)) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  obtain ⟨S⟩ := nonempty_hurwitzRadonSystem_of_eq (E := E) Fact.out hn
  exact ⟨S.tangentField n, S.tangentTrivialization m, S.isLocalFrameOn_tangentField m,
    S.orthonormal_tangentField n, S.baseSet_tangentTrivialization m,
    S.tangentTrivialization_mem_maximalAtlas m⟩

/-- **Smooth strict-unit H-space multiplications on `S⁰, S¹, S³, S⁷`.** For `n ∈ {0, 1, 3, 7}`, any
`(n + 1)`-dimensional real inner product space `E`, any basepoint `e₀ ∈ Sⁿ`, and any `m : ℕ∞ω`,
there exists a `C^m` multiplication `μ : Sⁿ → Sⁿ → Sⁿ` with `e₀` as strict two-sided identity and
bijective left translations. -/
theorem exists_contMDiff_sphereMul_of_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) (e₀ : sphere (0 : E) 1) (m : ℕ∞ω) :
    ∃ μ : sphere (0 : E) 1 → sphere (0 : E) 1 → sphere (0 : E) 1,
      ContMDiff ((𝓡 n).prod (𝓡 n)) (𝓡 n) m (Function.uncurry μ) ∧
      (∀ x, μ e₀ x = x) ∧
      (∀ x, μ x e₀ = x) ∧
      ∀ x, Function.Bijective (μ x) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  obtain ⟨S⟩ := nonempty_hurwitzRadonSystem_of_eq (E := E) Fact.out hn
  exact ⟨sphereFrameMul e₀ (S.tangentField n) (S.linearIndependent_tangentField n),
    contMDiff_uncurry_sphereFrameMul e₀ (S.contMDiff_tangentField n m)
      (S.linearIndependent_tangentField n),
    sphereFrameMul_left_id e₀ (S.tangentField n) (S.linearIndependent_tangentField n),
    sphereFrameMul_right_id e₀ (S.tangentField n) (S.linearIndependent_tangentField n),
    bijective_sphereFrameMul_left e₀ (S.tangentField n) (S.linearIndependent_tangentField n)⟩

/-- **Parallelizability of the Euclidean spheres `S⁰, S¹, S³, S⁷`.** Whenever
`n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7`, the unit `n`-sphere in `ℝⁿ⁺¹` admits `n` smooth pointwise linearly
independent tangent vector fields. -/
theorem exists_contMDiff_linearIndependent_tangentSpace_sphere_of_eq {n : ℕ}
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    letI := finrank_euclideanSpace_fin_succ_fact n
    ∃ v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun x ↦ (⟨x, v i x⟩ :
          TangentBundle (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))) ∧
      ∀ x, LinearIndependent ℝ (fun i ↦ v i x) := by
  let _ := finrank_euclideanSpace_fin_succ_fact n
  have : FiniteDimensional ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
    FiniteDimensional.of_fact_finrank_eq_succ n
  obtain ⟨S⟩ := nonempty_hurwitzRadonSystem_of_eq
    (E := EuclideanSpace ℝ (Fin (n + 1))) Fact.out hn
  exact ⟨S.tangentField n, S.contMDiff_tangentField n ∞, S.linearIndependent_tangentField n⟩

end DivisionAlgebraSpheres

end TauCeti
