/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.Star

/-!
# The Temperley–Lieb comparison homomorphism at `δ = √3`

Building on the cubic quantum torus `CubicTorus N`, its inversion-fixed subalgebra
`cubicFixed N`, and its cubic projections `cubicProjection N j` from
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic`, this file constructs the surjective
star-compatible comparison homomorphism
`cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`.

* **Comparison homomorphism and star compatibility**: rescaling the cubic projections
  `p_j = cubicProjection (m - 1) j` by `√3` satisfies the Temperley–Lieb relations at loop value
  `δ = √3` and lands in `cubicFixed (m - 1)`, yielding `cubicFixedHom m` via
  `TemperleyLieb.lift`. On generators, `star (e j) = e j` maps to the self-adjoint element
  `(√3 : ℂ) • p_j`, so `cubicFixedHom m` intertwines the Temperley–Lieb analytic adjoint with
  `TwistedMonoidAlgebra.adjoint` (`coe_cubicFixedHom_star`, `cubicFixedHom_star`).
* **Surjectivity**: every inversion-fixed element is a linear combination of the symmetric Weyl
  elements `c(a) = of a + of (-a)` (`a : Fin (m - 1) → ZMod 3`), which obey the product identity
  `c(a) c(b) = α(a, b) c(a + b) + α(a, b)⁻¹ c(a - b)`. Starting from the site generators
  `c(e_j) = (√3 : ℂ) • F_m (e j) - 1`, induction on the highest nonzero coordinate of `a` shows
  that every `c(a)` lies in the range of `cubicFixedHom m` (`cubicFixedHom_surjective`).

Coordinate inclusions, conditional expectations, the Markov trace identity, positivity of the
Markov Hermitian form at `δ = √3`, and the identification of the trace-radical Jones quotient
with `cubicFixed (m - 1)` are established in
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Quotient`.

## Main definitions

* `TauCeti.TemperleyLieb.cubicFixedHom`: the `ℂ`-algebra homomorphism
  `TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` sending `e (√3 : ℂ) j` to
  `(√3 : ℂ) • cubicProjection (m - 1) j`.

## Main results

* `TauCeti.TemperleyLieb.coe_cubicFixedHom_e`: evaluation of `cubicFixedHom m` on generators.
* `TauCeti.TemperleyLieb.coe_cubicFixedHom_star` and `TauCeti.TemperleyLieb.cubicFixedHom_star`:
  compatibility of `cubicFixedHom` with the Temperley–Lieb analytic adjoint and
  `TwistedMonoidAlgebra.adjoint` / `cubicFixedAdjoint`.
* `TauCeti.TemperleyLieb.cubicFixedHom_surjective`: surjectivity of `cubicFixedHom m` for every
  `m : ℕ`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*, J. Math.
  Phys. 55 (2014), 061702.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topol. 8
  (2017), 433–458.
-/

public section

open scoped ComplexConjugate

namespace TauCeti.TemperleyLieb

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact` so that
`TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m` carries the analytic adjoint instances
`TemperleyLieb.instStarRing` and `TemperleyLieb.instStarModule`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

private theorem sqrt_three_coe_mul_self :
    (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

/-- For every nonzero `t : ZMod 3`, `ω ^ (2t) - ω ^ (-2t) ≠ 0`. -/
private theorem coe_cubeRootPow_sq_sub_inv_sq_ne_zero {t : ZMod 3} (ht : t ≠ 0) :
    (cubeRootPow (2 * t) : ℂ) - (cubeRootPow (-(2 * t)) : ℂ) ≠ 0 := by
  have h12 : (cubeRootOfUnity : ℂ) ^ 2 ≠ (cubeRootOfUnity : ℂ) := by
    intro h
    have hmul : (cubeRootOfUnity : ℂ) * ((cubeRootOfUnity : ℂ) - 1) = 0 := by
      linear_combination h
    exact coe_cubeRootOfUnity_ne_one (sub_eq_zero.mp
      ((mul_eq_zero.mp hmul).resolve_left cubeRootOfUnity.ne_zero))
  have h2 : (cubeRootPow 2 : ℂ) = (cubeRootOfUnity : ℂ) ^ 2 := by
    have h11 : (2 : ZMod 3) = 1 + 1 := by decide
    rw [h11, cubeRootPow_add, cubeRootPow_one, Units.val_mul, sq]
  rcases (by decide : ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2) t with rfl | rfl | rfl
  · exact absurd rfl ht
  · have hneg : -(2 * (1 : ZMod 3)) = 1 := by decide
    have hpos : 2 * (1 : ZMod 3) = 2 := by decide
    rw [hneg, hpos, h2, cubeRootPow_one]
    exact sub_ne_zero.mpr h12
  · have hneg : -(2 * (2 : ZMod 3)) = 2 := by decide
    have hpos : 2 * (2 : ZMod 3) = 1 := by decide
    rw [hneg, hpos, h2, cubeRootPow_one]
    exact sub_ne_zero.mpr h12.symm

/-! ### Comparison homomorphism and star compatibility -/

/-- The `j`-th Temperley–Lieb generator `(√3 : ℂ) • cubicProjection (m - 1) j`, bundled as an
element of `cubicFixed (m - 1)`. -/
private noncomputable def cubicFixedGenerator (m : ℕ) (j : Fin (m - 1)) : cubicFixed (m - 1) :=
  ⟨(Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j,
    Subalgebra.smul_mem _ (cubicProjection_mem_cubicFixed (m - 1) j) _⟩

/-- The **cubic quantum torus comparison homomorphism**
`TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`, sending `e (√3 : ℂ) j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`. -/
noncomputable def cubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1) :=
  lift (cubicFixedGenerator m)
    (fun i ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, SetLike.val_smul, cubicFixedGenerator, smul_mul_smul_comm,
        cubicProjection_mul_self, smul_smul])
    (fun {i j} h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, cubicFixedGenerator, smul_mul_assoc, mul_smul_comm,
        cubicProjection_mul_cubicProjection_mul_cubicProjection h, smul_smul]
      rw [sqrt_three_coe_mul_self]
      norm_num)
    (fun {i j} h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, cubicFixedGenerator]
      exact ((commute_cubicProjection h).smul_left _ |>.smul_right _).eq)

/-- Action of `cubicFixedHom` on the `j`-th Temperley–Lieb generator, coerced to the ambient
`CubicTorus (m - 1)`. -/
@[simp]
theorem coe_cubicFixedHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicFixedHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := by
  simp [cubicFixedHom, cubicFixedGenerator]

/-- `cubicFixedHom` intertwines the Temperley–Lieb analytic adjoint with
`TwistedMonoidAlgebra.adjoint`. -/
theorem coe_cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (cubicFixedHom m (star x) : CubicTorus (m - 1)) =
      TwistedMonoidAlgebra.adjoint (cubicFixedHom m x) := by
  have hadd (a b : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
      (cubicFixedHom m (a + b) : CubicTorus (m - 1)) =
        (cubicFixedHom m a : CubicTorus (m - 1)) + (cubicFixedHom m b : CubicTorus (m - 1)) :=
    congrArg Subtype.val ((cubicFixedHom m).map_add' a b)
  have hmul (a b : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
      (cubicFixedHom m (a * b) : CubicTorus (m - 1)) =
        (cubicFixedHom m a : CubicTorus (m - 1)) * (cubicFixedHom m b : CubicTorus (m - 1)) :=
    congrArg Subtype.val ((cubicFixedHom m).map_mul' a b)
  induction x using TemperleyLieb.induction with
  | e j =>
    rw [star_e, coe_cubicFixedHom_e, map_smulₛₗ, starRingEnd_apply, adjoint_cubicProjection]
    simp [Complex.conj_ofReal]
  | algebraMap z =>
    have hstar : star (algebraMap ℂ (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) z) =
        algebraMap ℂ (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) (conj z) := by
      rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, Algebra.algebraMap_eq_smul_one]
      rfl
    rw [hstar, (cubicFixedHom m).commutes, (cubicFixedHom m).commutes,
      Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
      TwistedMonoidAlgebra.adjoint_algebraMap]
    rfl
  | add x y hx hy =>
    rw [star_add, hadd, hadd, map_add, hx, hy]
  | mul x y hx hy =>
    rw [star_mul, hmul, hmul, adjoint_mul_cubicTorus, hx, hy]

/-- `cubicFixedHom` intertwines the Temperley–Lieb analytic adjoint with `cubicFixedAdjoint`. -/
@[simp]
theorem cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedHom m (star x) = cubicFixedAdjoint (m - 1) (cubicFixedHom m x) := by
  apply Subtype.ext
  rw [coe_cubicFixedHom_star, coe_cubicFixedAdjoint]

/-! ### Surjectivity of `cubicFixedHom` -/

/-- Ambient `ℂ`-algebra homomorphism into `CubicTorus (m - 1)` used to establish surjectivity of
`cubicFixedHom m`. -/
private noncomputable def ambientCubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] CubicTorus (m - 1) :=
  (cubicFixed (m - 1)).val.comp (cubicFixedHom m)

/-- The symmetric Weyl element `c(a) = of a + of (-a)` in `CubicTorus N`. -/
private noncomputable def symWeyl (N : ℕ) (a : Fin N → ZMod 3) : CubicTorus N :=
  TwistedMonoidAlgebra.of (Multiplicative.ofAdd a) +
    TwistedMonoidAlgebra.of (Multiplicative.ofAdd (-a))

private theorem symWeyl_neg (N : ℕ) (a : Fin N → ZMod 3) :
    symWeyl N (-a) = symWeyl N a := by
  simp [symWeyl, add_comm]

private theorem symWeyl_zero (N : ℕ) : symWeyl N 0 = (2 : ℂ) • 1 := by
  simp [symWeyl, two_smul]

private theorem symWeyl_mul (N : ℕ) (a b : Fin N → ZMod 3) :
    symWeyl N a * symWeyl N b =
      (cubeRootPow (2 * chainForm N a b) : ℂ) • symWeyl N (a + b) +
        (cubeRootPow (-(2 * chainForm N a b)) : ℂ) • symWeyl N (a - b) := by
  have h1 : cubicFactor N (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) =
      cubeRootPow (2 * chainForm N a b) := by
    rw [cubicFactor_apply, toAdd_ofAdd, toAdd_ofAdd]
  have h2 : cubicFactor N (Multiplicative.ofAdd (-a)) (Multiplicative.ofAdd (-b)) =
      cubeRootPow (2 * chainForm N a b) := by
    simp [cubicFactor_apply]
  have h3 : cubicFactor N (Multiplicative.ofAdd a) (Multiplicative.ofAdd (-b)) =
      cubeRootPow (-(2 * chainForm N a b)) := by
    simp [cubicFactor_apply]
  have h4 : cubicFactor N (Multiplicative.ofAdd (-a)) (Multiplicative.ofAdd b) =
      cubeRootPow (-(2 * chainForm N a b)) := by
    simp [cubicFactor_apply]
  simp only [symWeyl, add_mul, mul_add, TwistedMonoidAlgebra.of_mul_of, h1, h2, h3, h4,
    ← ofAdd_add, smul_add]
  have hn1 : -a + -b = -(a + b) := by abel
  have hn2 : a + -b = a - b := (sub_eq_add_neg a b).symm
  have hn3 : -a + b = -(a - b) := by abel
  rw [hn1, hn2, hn3]
  abel

private theorem symWeyl_single_mem_range (m : ℕ) (j : Fin (m - 1)) :
    symWeyl (m - 1) (Pi.single j 1) ∈ (ambientCubicFixedHom m).range := by
  rw [AlgHom.mem_range]
  refine ⟨(Real.sqrt 3 : ℂ) • e (Real.sqrt 3 : ℂ) j - 1, ?_⟩
  have he : ambientCubicFixedHom m (e (Real.sqrt 3 : ℂ) j) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j :=
    coe_cubicFixedHom_e m j
  have h3 : ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (3 : ℂ)⁻¹ = 1 := by
    rw [sqrt_three_coe_mul_self]
    norm_num
  rw [map_sub, map_smul, map_one, he, cubicProjection_def, smul_smul, smul_smul, h3, one_smul,
    symWeyl, ← cubicSite_def, ← cubicSite_sq_eq_of_neg]
  abel

private theorem symWeyl_add_mem_of_chainForm_ne_zero {m : ℕ} {a b : Fin (m - 1) → ZMod 3}
    (ha : symWeyl (m - 1) a ∈ (ambientCubicFixedHom m).range)
    (hb : symWeyl (m - 1) b ∈ (ambientCubicFixedHom m).range)
    (hB : chainForm (m - 1) a b ≠ 0) :
    symWeyl (m - 1) (a + b) ∈ (ambientCubicFixedHom m).range := by
  set t := 2 * chainForm (m - 1) a b
  have ht : t ≠ 0 := (by decide : ∀ x : ZMod 3, x ≠ 0 → 2 * x ≠ 0) _ hB
  have hdiff : (cubeRootPow (2 * t) : ℂ) - (cubeRootPow (-(2 * t)) : ℂ) ≠ 0 :=
    coe_cubeRootPow_sq_sub_inv_sq_ne_zero ht
  have hab := symWeyl_mul (m - 1) a b
  have hba : symWeyl (m - 1) b * symWeyl (m - 1) a =
      (cubeRootPow (-t) : ℂ) • symWeyl (m - 1) (a + b) +
        (cubeRootPow t : ℂ) • symWeyl (m - 1) (a - b) := by
    have h := symWeyl_mul (m - 1) b a
    rw [chainForm_swap, mul_neg, neg_neg, add_comm b a, ← symWeyl_neg _ (b - a), neg_sub] at h
    exact h
  have hlin : (cubeRootPow t : ℂ) • (symWeyl (m - 1) a * symWeyl (m - 1) b) -
      (cubeRootPow (-t) : ℂ) • (symWeyl (m - 1) b * symWeyl (m - 1) a) =
      ((cubeRootPow (2 * t) : ℂ) - (cubeRootPow (-(2 * t)) : ℂ)) • symWeyl (m - 1) (a + b) := by
    rw [hab, hba, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul,
      ← cubeRootPow_add, ← cubeRootPow_add, ← cubeRootPow_add, ← cubeRootPow_add,
      add_neg_cancel, neg_add_cancel, cubeRootPow_zero, Units.val_one, one_smul,
      ← two_mul, ← neg_add, ← two_mul, sub_smul]
    abel
  have hmem := sub_mem (Subalgebra.smul_mem _ (mul_mem ha hb) (cubeRootPow t : ℂ))
    (Subalgebra.smul_mem _ (mul_mem hb ha) (cubeRootPow (-t) : ℂ))
  rw [hlin] at hmem
  have hres := Subalgebra.smul_mem _ hmem
    ((cubeRootPow (2 * t) : ℂ) - (cubeRootPow (-(2 * t)) : ℂ))⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hdiff, one_smul] at hres

private theorem symWeyl_add_mem_of_chainForm_eq_zero {m : ℕ} {a b : Fin (m - 1) → ZMod 3}
    (ha : symWeyl (m - 1) a ∈ (ambientCubicFixedHom m).range)
    (hb : symWeyl (m - 1) b ∈ (ambientCubicFixedHom m).range)
    (hsub : symWeyl (m - 1) (a - b) ∈ (ambientCubicFixedHom m).range)
    (hB : chainForm (m - 1) a b = 0) :
    symWeyl (m - 1) (a + b) ∈ (ambientCubicFixedHom m).range := by
  have hmul := symWeyl_mul (m - 1) a b
  simp only [hB, mul_zero, neg_zero, cubeRootPow_zero, Units.val_one, one_smul] at hmul
  have heq : symWeyl (m - 1) (a + b) =
      symWeyl (m - 1) a * symWeyl (m - 1) b - symWeyl (m - 1) (a - b) := by
    rw [hmul]; abel
  rw [heq]
  exact sub_mem (mul_mem ha hb) hsub

private theorem update_zero_of_ge {N k : ℕ} (hk : k < N) {a : Fin N → ZMod 3}
    (hhi : ∀ j : Fin N, k + 1 ≤ j.1 → a j = 0) :
    ∀ j : Fin N, k ≤ j.1 → Function.update a ⟨k, hk⟩ 0 j = 0 := by
  intro j hj
  by_cases hji : j = ⟨k, hk⟩
  · simp [hji]
  · simp [hji, hhi j (by have : j.1 ≠ k := fun h ↦ hji (Fin.ext h); omega)]

private theorem eq_update_add_single_one {N : ℕ} {a : Fin N → ZMod 3} {i : Fin N}
    (hai : a i = 1) :
    a = Function.update a i 0 + Pi.single i 1 := by
  ext j
  by_cases hji : j = i
  · subst hji; simp [hai]
  · simp [hji]

private theorem chainForm_single_right_of_zero_above {N : ℕ} {a : Fin N → ZMod 3}
    {i : Fin N} (hpos : 0 < i.1) (hhi : ∀ j : Fin N, i.1 < j.1 → a j = 0) :
    chainForm N a (Pi.single i 1) = a ⟨i.1 - 1, by omega⟩ := by
  rw [chainForm_single_right, dite_eq_left hpos]
  have h2 : (if h : (i : ℕ) + 1 < N then a ⟨i.1 + 1, h⟩ else 0) = 0 := by
    split_ifs with hlt
    · exact hhi ⟨i.1 + 1, hlt⟩ (Nat.lt_succ_self i.1)
    · rfl
  rw [h2, sub_zero]

/-- Inductive step when the coordinate immediately below the leading index `k₁ + 1` is nonzero. -/
private theorem symWeyl_mem_range_of_adj_ne_zero {m k₁ : ℕ} (hk : k₁ + 1 < m - 1)
    (ih : ∀ v : Fin (m - 1) → ZMod 3, (∀ j : Fin (m - 1), k₁ + 1 ≤ j.1 → v j = 0) →
      symWeyl (m - 1) v ∈ (ambientCubicFixedHom m).range)
    {v : Fin (m - 1) → ZMod 3} (hvhi : ∀ j : Fin (m - 1), k₁ + 2 ≤ j.1 → v j = 0)
    (hvi : v ⟨k₁ + 1, hk⟩ = 1) (hvi₁ : v ⟨k₁, by omega⟩ ≠ 0) :
    symWeyl (m - 1) v ∈ (ambientCubicFixedHom m).range := by
  let i : Fin (m - 1) := ⟨k₁ + 1, hk⟩
  let i₁ : Fin (m - 1) := ⟨k₁, by omega⟩
  let v' : Fin (m - 1) → ZMod 3 := Function.update v i 0
  have hv'0 : ∀ j : Fin (m - 1), k₁ + 1 ≤ j.1 → v' j = 0 := update_zero_of_ge hk hvhi
  have hB : chainForm (m - 1) v' (Pi.single i 1) = v i₁ := by
    rw [chainForm_single_right_of_zero_above (by dsimp [i]; omega)
      (fun j hj ↦ hv'0 j (by dsimp [i] at hj; omega))]
    have hidx : (⟨i.1 - 1, by omega⟩ : Fin (m - 1)) = i₁ := Fin.ext rfl
    have hne1 : i₁ ≠ i := ne_of_apply_ne Fin.val (by dsimp [i, i₁]; omega)
    rw [hidx]; simp [v', hne1]
  rw [eq_update_add_single_one hvi]
  exact symWeyl_add_mem_of_chainForm_ne_zero (ih v' hv'0) (symWeyl_single_mem_range m i)
    (by rw [hB]; exact hvi₁)

/-- Inductive step when `v (k₂ + 2) = 1`, `v (k₂ + 1) = 0`, and `v k₂ ≠ 1`. -/
private theorem symWeyl_mem_range_of_prev_ne_one {m k₂ : ℕ} (hk : k₂ + 2 < m - 1)
    (ih : ∀ v : Fin (m - 1) → ZMod 3, (∀ j : Fin (m - 1), k₂ + 2 ≤ j.1 → v j = 0) →
      symWeyl (m - 1) v ∈ (ambientCubicFixedHom m).range)
    {v : Fin (m - 1) → ZMod 3} (hvhi : ∀ j : Fin (m - 1), k₂ + 3 ≤ j.1 → v j = 0)
    (hvi : v ⟨k₂ + 2, hk⟩ = 1) (hvi₁ : v ⟨k₂ + 1, by omega⟩ = 0)
    (hvi₂ : v ⟨k₂, by omega⟩ ≠ 1) :
    symWeyl (m - 1) v ∈ (ambientCubicFixedHom m).range := by
  let i : Fin (m - 1) := ⟨k₂ + 2, hk⟩
  let i₁ : Fin (m - 1) := ⟨k₂ + 1, by omega⟩
  let i₂ : Fin (m - 1) := ⟨k₂, by omega⟩
  let u := v + Pi.single i₁ 1
  have hne_i : i ≠ i₁ := ne_of_apply_ne Fin.val (by dsimp [i, i₁]; omega)
  have hne_i₂ : i₂ ≠ i₁ := ne_of_apply_ne Fin.val (by dsimp [i₁, i₂]; omega)
  have hu_mem : symWeyl (m - 1) u ∈ (ambientCubicFixedHom m).range := by
    refine symWeyl_mem_range_of_adj_ne_zero hk ih (fun j hj ↦ ?_)
      (by simp [u, i, Pi.single_eq_of_ne hne_i, hvi]) (by simp [u, i₁, hvi₁])
    have hji₁ : j ≠ i₁ := ne_of_apply_ne Fin.val (by dsimp [i₁]; omega)
    simp [u, hvhi j hj, Pi.single_eq_of_ne hji₁]
  have hBu : chainForm (m - 1) u (Pi.single i₁ 1) = v i₂ - 1 := by
    rw [chainForm_single_right]
    have hpos : 0 < (i₁ : ℕ) := by dsimp [i₁]; omega
    have hlt : (i₁ : ℕ) + 1 < m - 1 := by dsimp [i₁]; omega
    have hidx1 : (⟨i₁.1 - 1, by omega⟩ : Fin (m - 1)) = i₂ := Fin.ext rfl
    have hidx2 : (⟨i₁.1 + 1, hlt⟩ : Fin (m - 1)) = i := Fin.ext rfl
    rw [dite_eq_left hpos, dite_eq_left hlt, hidx1, hidx2]
    simp [u, Pi.single_eq_of_ne hne_i₂, Pi.single_eq_of_ne hne_i, i, hvi]
  have hsub_eq : v = u + (-Pi.single i₁ 1) := by simp [u]
  rw [hsub_eq]
  refine symWeyl_add_mem_of_chainForm_ne_zero hu_mem ?_ ?_
  · rw [symWeyl_neg]; exact symWeyl_single_mem_range m i₁
  · rw [map_neg, hBu]; exact neg_ne_zero.mpr (sub_ne_zero.mpr hvi₂)

/-- Inductive step when `a (k₂ + 2) = 1`, `a (k₂ + 1) = 0`, and `a k₂ = 1`. -/
private theorem symWeyl_mem_range_of_prev_eq_one {m k₂ : ℕ} (hk : k₂ + 2 < m - 1)
    (ih : ∀ a : Fin (m - 1) → ZMod 3, (∀ j : Fin (m - 1), k₂ + 2 ≤ j.1 → a j = 0) →
      symWeyl (m - 1) a ∈ (ambientCubicFixedHom m).range)
    {a : Fin (m - 1) → ZMod 3} (hhi : ∀ j : Fin (m - 1), k₂ + 3 ≤ j.1 → a j = 0)
    (hak : a ⟨k₂ + 2, hk⟩ = 1) (hai₁ : a ⟨k₂ + 1, by omega⟩ = 0)
    (hai₂ : a ⟨k₂, by omega⟩ = 1) :
    symWeyl (m - 1) a ∈ (ambientCubicFixedHom m).range := by
  let i : Fin (m - 1) := ⟨k₂ + 2, hk⟩
  let i₁ : Fin (m - 1) := ⟨k₂ + 1, by omega⟩
  let i₂ : Fin (m - 1) := ⟨k₂, by omega⟩
  let a' : Fin (m - 1) → ZMod 3 := Function.update a i 0
  have ha'_zero : ∀ j : Fin (m - 1), k₂ + 2 ≤ j.1 → a' j = 0 := update_zero_of_ge hk hhi
  let b := -a' + Pi.single i 1
  have hne_i₁ : i₁ ≠ i := ne_of_apply_ne Fin.val (by dsimp [i, i₁]; omega)
  have hne_i₂ : i₂ ≠ i := ne_of_apply_ne Fin.val (by dsimp [i, i₂]; omega)
  have hb_mem : symWeyl (m - 1) b ∈ (ambientCubicFixedHom m).range := by
    refine symWeyl_mem_range_of_prev_ne_one hk ih (fun j hj ↦ ?_)
      (by simp [b, a', i]) (by simp [b, a', i₁, hne_i₁, hai₁]) ?_
    · have hji : j ≠ i := ne_of_apply_ne Fin.val (by dsimp [i]; omega)
      simp [b, ha'_zero j (by omega), Pi.single_eq_of_ne hji]
    · simp only [b, Pi.add_apply, Pi.neg_apply, Pi.single_eq_of_ne hne_i₂, add_zero, a',
        Function.update_of_ne hne_i₂, i₂, hai₂]
      decide
  have hBa' : chainForm (m - 1) a' (Pi.single i 1) = 0 := by
    rw [chainForm_single_right_of_zero_above (by dsimp [i]; omega)
      (fun j hj ↦ ha'_zero j (by dsimp [i] at hj; omega))]
    have hidx1 : (⟨i.1 - 1, by omega⟩ : Fin (m - 1)) = i₁ := Fin.ext rfl
    rw [hidx1]; simp [a', hne_i₁, i₁, hai₁]
  have hsub_mem : symWeyl (m - 1) (a' - Pi.single i 1) ∈ (ambientCubicFixedHom m).range := by
    have heq : a' - Pi.single i 1 = -b := by simp [b]; abel
    rw [heq, symWeyl_neg]
    exact hb_mem
  rw [eq_update_add_single_one hak]
  exact symWeyl_add_mem_of_chainForm_eq_zero (ih a' ha'_zero)
    (symWeyl_single_mem_range m i) hsub_mem hBa'

private theorem symWeyl_mem_range_step {m k : ℕ} (hk : k < m - 1)
    (ih : ∀ a : Fin (m - 1) → ZMod 3, (∀ j : Fin (m - 1), k ≤ j.1 → a j = 0) →
      symWeyl (m - 1) a ∈ (ambientCubicFixedHom m).range)
    {a : Fin (m - 1) → ZMod 3} (hhi : ∀ j : Fin (m - 1), k + 1 ≤ j.1 → a j = 0)
    (hak : a ⟨k, hk⟩ = 1) :
    symWeyl (m - 1) a ∈ (ambientCubicFixedHom m).range := by
  cases k with
  | zero =>
    have ha'0 : Function.update a ⟨0, hk⟩ 0 = 0 :=
      funext fun j ↦ update_zero_of_ge hk hhi j (Nat.zero_le _)
    rw [eq_update_add_single_one hak, ha'0, zero_add]
    exact symWeyl_single_mem_range m ⟨0, hk⟩
  | succ k₁ =>
    let i₁ : Fin (m - 1) := ⟨k₁, by omega⟩
    by_cases hai₁ : a i₁ = 0
    · cases k₁ with
      | zero =>
        have ha'0 : Function.update a ⟨0 + 1, hk⟩ 0 = 0 := funext fun j ↦ by
          by_cases hj0 : j.1 = 0
          · have hjeq : j = i₁ := Fin.ext hj0
            have hne1 : i₁ ≠ ⟨0 + 1, hk⟩ := ne_of_apply_ne Fin.val (by dsimp [i₁]; omega)
            rw [hjeq]; simp [hne1, hai₁]
          · exact update_zero_of_ge hk hhi j (by omega)
        rw [eq_update_add_single_one hak, ha'0, zero_add]
        exact symWeyl_single_mem_range m ⟨0 + 1, hk⟩
      | succ k₂ =>
        by_cases hai₂ : a ⟨k₂, by omega⟩ = 1
        · exact symWeyl_mem_range_of_prev_eq_one hk ih hhi hak hai₁ hai₂
        · exact symWeyl_mem_range_of_prev_ne_one hk ih hhi hak hai₁ hai₂
    · exact symWeyl_mem_range_of_adj_ne_zero hk ih hhi hak hai₁

private theorem symWeyl_mem_range (m : ℕ) (a : Fin (m - 1) → ZMod 3) :
    symWeyl (m - 1) a ∈ (ambientCubicFixedHom m).range := by
  have hind : ∀ k : ℕ, k ≤ m - 1 → ∀ v : Fin (m - 1) → ZMod 3,
      (∀ j : Fin (m - 1), k ≤ j.1 → v j = 0) →
      symWeyl (m - 1) v ∈ (ambientCubicFixedHom m).range := by
    intro k
    induction k with
    | zero =>
      intro _ v hv
      have hv0 : v = 0 := funext fun j ↦ hv j (Nat.zero_le _)
      rw [hv0, symWeyl_zero]
      exact Subalgebra.smul_mem _ (one_mem _) _
    | succ k ih =>
      intro hk v hv
      have ih' := ih (Nat.le_of_succ_le hk)
      let i : Fin (m - 1) := ⟨k, hk⟩
      rcases (by decide : ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2) (v i) with h0 | h1 | h2
      · refine ih' v fun j hj ↦ ?_
        by_cases hjk : j.1 = k
        · have hji : j = i := Fin.ext hjk
          rw [hji]; exact h0
        · exact hv j (by omega)
      · exact symWeyl_mem_range_step hk ih' hv h1
      · rw [← symWeyl_neg]
        refine symWeyl_mem_range_step hk ih' (fun j hj ↦ by simp [hv j hj]) ?_
        rw [Pi.neg_apply]
        have : v ⟨k, hk⟩ = 2 := h2
        rw [this]; decide
  exact hind (m - 1) le_rfl a fun j hj ↦ absurd hj (not_le_of_gt j.isLt)

/-- **Surjectivity of `cubicFixedHom`**: for every `m : ℕ`, the Temperley–Lieb algebra at `δ = √3`
surjects onto the inversion-fixed subalgebra `cubicFixed (m - 1)`. -/
theorem cubicFixedHom_surjective (m : ℕ) : Function.Surjective (cubicFixedHom m) := by
  intro x
  have hmem : (x : CubicTorus (m - 1)) ∈ (ambientCubicFixedHom m).range := by
    have hfix : cubicInversion (m - 1) (x : CubicTorus (m - 1)) = x := mem_cubicFixed_iff.mp x.2
    set b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin (m - 1) → ZMod 3))
      (cubicFactor (m - 1))
    have hb : ∀ g, b g = TwistedMonoidAlgebra.of g :=
      TwistedMonoidAlgebra.basis_apply ℂ (Multiplicative (Fin (m - 1) → ZMod 3))
        (cubicFactor (m - 1))
    have h1 : (b.repr (x : CubicTorus (m - 1))).sum (fun g c ↦ c • TwistedMonoidAlgebra.of g) =
        (x : CubicTorus (m - 1)) := by
      simpa only [Finsupp.linearCombination_apply, hb] using
        b.linearCombination_repr (x : CubicTorus (m - 1))
    have h2 : (b.repr (x : CubicTorus (m - 1))).sum (fun g c ↦ c • TwistedMonoidAlgebra.of g⁻¹) =
        (x : CubicTorus (m - 1)) := by
      calc
        (b.repr (x : CubicTorus (m - 1))).sum (fun g c ↦ c • TwistedMonoidAlgebra.of g⁻¹)
            = cubicInversion (m - 1)
                ((b.repr (x : CubicTorus (m - 1))).sum
                  (fun g c ↦ c • TwistedMonoidAlgebra.of g)) := by
              rw [Finsupp.sum, Finsupp.sum, map_sum]
              refine Finset.sum_congr rfl fun g _ ↦ by simp
        _ = (x : CubicTorus (m - 1)) := by rw [h1, hfix]
    have hexpand : (x : CubicTorus (m - 1)) =
        (2 : ℂ)⁻¹ • ((b.repr (x : CubicTorus (m - 1))).sum fun g c ↦
          c • symWeyl (m - 1) g.toAdd) := by
      have hsum : (b.repr (x : CubicTorus (m - 1))).sum (fun g c ↦ c • symWeyl (m - 1) g.toAdd) =
          (x : CubicTorus (m - 1)) + (x : CubicTorus (m - 1)) := by
        rw [Finsupp.sum] at h1 h2 ⊢
        simp only [symWeyl, ofAdd_toAdd, ofAdd_neg, smul_add, Finset.sum_add_distrib]
        rw [h1, h2]
      rw [hsum, ← two_smul ℂ, smul_smul]
      norm_num
    rw [hexpand]
    refine Subalgebra.smul_mem _ ?_ _
    rw [Finsupp.sum]
    exact sum_mem fun g _ ↦ Subalgebra.smul_mem _ (symWeyl_mem_range m g.toAdd) _
  rw [AlgHom.mem_range] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, Subtype.ext hy⟩

end TauCeti.TemperleyLieb
