/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.LinearAlgebra.Alternating.Curry
public import TauCeti.LinearAlgebra.Alternating.Derivation

/-!
# Descent of alternating maps to quotients

Let `P` be a submodule of an `R`-module `M`, and let `ι` be a finite index type. An alternating
map `f : M [⋀^ι]→ₗ[R] N` descends to `(M ⧸ P) [⋀^ι]→ₗ[R] N` along `P.mkQ` if and only if `f`
vanishes whenever one of its arguments lies in `P` (`AlternatingMap.exists_compLinearMap_mkQ_iff`).
In positive finite degree `Fin (n + 1)`, this horizontality condition is equivalent to the vanishing
of the interior products `f.curryLeft x` for all `x ∈ P`
(`AlternatingMap.map_eq_zero_of_mem_iff_curryLeft`).

The descended map `AlternatingMap.liftQ` is unique (`AlternatingMap.liftQ_unique`), because
precomposition with the surjection `P.mkQ` is injective (`AlternatingMap.compLinearMap_injective`),
and it is natural with respect to linear maps on the target and linear maps on the source
stabilizing `P`, as well as the derivations they induce
(`AlternatingMap.alternatingDerivation_compLinearMap_mkQ`).

## Main definitions

* `AlternatingMap.liftQ`: the unique alternating map on `M ⧸ P` descending an alternating map on
  `M` that vanishes whenever an argument lies in `P`.

## Main results

* `AlternatingMap.map_eq_of_sub_mem`: an alternating map vanishing on `P` depends only on the
  classes of its arguments modulo `P`.
* `AlternatingMap.liftQ_comp_mkQ`, `AlternatingMap.liftQ_unique`: characterizing properties of
  `AlternatingMap.liftQ`.
* `AlternatingMap.exists_compLinearMap_mkQ_iff`: factorization criterion through `M ⧸ P`.
* `AlternatingMap.map_eq_zero_of_mem_iff_curryLeft`: equivalence of horizontality and vanishing of
  interior products along `P`.
* `AlternatingMap.alternatingDerivation_compLinearMap_mkQ`: compatibility of `compLinearMap P.mkQ`
  with induced derivations.
-/

public section

namespace AlternatingMap

section Ring

variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- An alternating map on finitely many arguments that vanishes whenever an argument lies in `P`
takes the same value on tuples whose entries agree modulo `P`. -/
theorem map_eq_of_sub_mem [Finite ι] {P : Submodule R M} {f : M [⋀^ι]→ₗ[R] N}
    (hf : ∀ (v : ι → M) (i : ι), v i ∈ P → f v = 0) {v w : ι → M}
    (hvw : ∀ i, v i - w i ∈ P) : f v = f w := by
  classical
  have := Fintype.ofFinite ι
  -- Replace the coordinates of `w` by those of `v` one index at a time.
  suffices ∀ s : Finset ι, f (s.piecewise v w) = f w by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.piecewise_insert]
    have hvj : v j = w j + (v j - w j) := (add_sub_cancel _ _).symm
    have h0 : f (Function.update (s.piecewise v w) j (v j - w j)) = 0 :=
      hf _ j (by simp [hvw j])
    have hwj : s.piecewise v w j = w j := Finset.piecewise_eq_of_notMem _ _ _ hj
    rw [hvj, map_update_add, h0, add_zero, ← hwj, Function.update_eq_self, ih]

private theorem map_eq_of_mkQ_eq [Finite ι] {P : Submodule R M} {f : M [⋀^ι]→ₗ[R] N}
    (hf : ∀ (v : ι → M) (i : ι), v i ∈ P → f v = 0) {v w : ι → M}
    (hvw : ∀ i, P.mkQ (v i) = P.mkQ (w i)) : f v = f w :=
  map_eq_of_sub_mem hf fun i ↦ by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hvw i

/-- Descend an alternating map `f : M [⋀^ι]→ₗ[R] N` that vanishes whenever an argument lies in `P`
to an alternating map `(M ⧸ P) [⋀^ι]→ₗ[R] N`. -/
noncomputable def liftQ [Finite ι] (P : Submodule R M) (f : M [⋀^ι]→ₗ[R] N)
    (hf : ∀ (v : ι → M) (i : ι), v i ∈ P → f v = 0) : (M ⧸ P) [⋀^ι]→ₗ[R] N where
  toFun q := f fun i ↦ Quotient.out (q i)
  map_update_add' q i x y := by
    rw [map_eq_of_mkQ_eq (P := P) hf (w := Function.update (fun k ↦ Quotient.out (q k)) i
        (Quotient.out x + Quotient.out y)) fun j ↦ by
      by_cases hji : j = i
      · subst hji; simp [Submodule.Quotient.mk_add]
      · simp [hji]]
    rw [map_update_add]
    congr 1
    · exact map_eq_of_mkQ_eq (P := P) hf fun j ↦ by by_cases hji : j = i <;> simp [hji]
    · exact map_eq_of_mkQ_eq (P := P) hf fun j ↦ by by_cases hji : j = i <;> simp [hji]
  map_update_smul' q i r x := by
    rw [map_eq_of_mkQ_eq (P := P) hf (w := Function.update (fun k ↦ Quotient.out (q k)) i
        (r • Quotient.out x)) fun j ↦ by
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]]
    rw [map_update_smul]
    congr 1
    exact map_eq_of_mkQ_eq (P := P) hf fun j ↦ by by_cases hji : j = i <;> simp [hji]
  map_eq_zero_of_eq' q i j hq hij :=
    f.map_eq_zero_of_eq _ (congrArg Quotient.out hq) hij

/-- Evaluating `liftQ P f hf` on quotient classes evaluates `f` on their representatives. -/
@[simp]
theorem liftQ_apply_mk [Finite ι] (P : Submodule R M) (f : M [⋀^ι]→ₗ[R] N)
    (hf : ∀ (v : ι → M) (i : ι), v i ∈ P → f v = 0) (v : ι → M) :
    liftQ P f hf (fun i ↦ Submodule.Quotient.mk (v i)) = f v :=
  map_eq_of_mkQ_eq (P := P) hf fun i ↦ Quotient.out_eq (P.mkQ (v i))

/-- Evaluating `liftQ P f hf` on `P.mkQ ∘ v` evaluates `f` on `v`. -/
theorem liftQ_apply_mkQ [Finite ι] (P : Submodule R M) (f : M [⋀^ι]→ₗ[R] N)
    (hf : ∀ (v : ι → M) (i : ι), v i ∈ P → f v = 0) (v : ι → M) :
    liftQ P f hf (fun i ↦ P.mkQ (v i)) = f v :=
  liftQ_apply_mk P f hf v

/-- Precomposing `liftQ P f hf` with `P.mkQ` recovers `f`. -/
@[simp]
theorem liftQ_comp_mkQ [Finite ι] (P : Submodule R M) (f : M [⋀^ι]→ₗ[R] N)
    (hf : ∀ (v : ι → M) (i : ι), v i ∈ P → f v = 0) :
    (liftQ P f hf).compLinearMap P.mkQ = f := by
  ext v
  exact liftQ_apply_mkQ P f hf v

/-- An alternating map on `M ⧸ P` whose pullback along `P.mkQ` is `f` equals `liftQ P f hf`. -/
theorem liftQ_unique [Finite ι] (P : Submodule R M) (f : M [⋀^ι]→ₗ[R] N)
    (hf : ∀ (v : ι → M) (i : ι), v i ∈ P → f v = 0) {g : (M ⧸ P) [⋀^ι]→ₗ[R] N}
    (hg : g.compLinearMap P.mkQ = f) : g = liftQ P f hf :=
  compLinearMap_injective P.mkQ P.mkQ_surjective (hg.trans (liftQ_comp_mkQ P f hf).symm)

/-- An alternating map `f : M [⋀^ι]→ₗ[R] N` on finitely many arguments factors through `P.mkQ` if
and only if it vanishes whenever one of its arguments lies in `P`. -/
theorem exists_compLinearMap_mkQ_iff [Finite ι] (P : Submodule R M) (f : M [⋀^ι]→ₗ[R] N) :
    (∃ g : (M ⧸ P) [⋀^ι]→ₗ[R] N, g.compLinearMap P.mkQ = f) ↔
      ∀ (v : ι → M) (i : ι), v i ∈ P → f v = 0 := by
  refine ⟨?_, fun hf ↦ ⟨liftQ P f hf, liftQ_comp_mkQ P f hf⟩⟩
  rintro ⟨g, rfl⟩ v i hi
  exact g.map_coord_zero i ((Submodule.Quotient.mk_eq_zero P).2 hi)

end Ring

section CommSemiring

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- In positive degree `Fin (n + 1)`, vanishing whenever an argument lies in `P` is equivalent to
vanishing of all interior products `f.curryLeft x` for `x ∈ P`. -/
theorem map_eq_zero_of_mem_iff_curryLeft {n : ℕ} (P : Submodule R M)
    (f : M [⋀^Fin (n + 1)]→ₗ[R] N) :
    (∀ (v : Fin (n + 1) → M) (i : Fin (n + 1)), v i ∈ P → f v = 0) ↔
      ∀ x ∈ P, f.curryLeft x = 0 := by
  refine ⟨fun hf x hx ↦ ?_, fun hf v i hi ↦ map_eq_zero_of_curryLeft_eq_zero (hf (v i) hi) rfl⟩
  ext w
  exact hf (Matrix.vecCons x w) 0 (by simpa using hx)

end CommSemiring

section CommRing

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Pulling back an alternating map along `P.mkQ` intertwines the derivation induced by a linear
endomorphism stabilizing `P` with the derivation induced on `M ⧸ P`. -/
theorem alternatingDerivation_compLinearMap_mkQ [Fintype ι] [DecidableEq ι] (P : Submodule R M)
    (φ : M →ₗ[R] M) (hφ : P ≤ P.comap φ) (g : (M ⧸ P) [⋀^ι]→ₗ[R] N) :
    ((P.mapQ P φ hφ).alternatingDerivation g).compLinearMap P.mkQ =
      φ.alternatingDerivation (g.compLinearMap P.mkQ) := by
  ext v
  simp only [compLinearMap_apply, LinearMap.alternatingDerivation_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  ext j
  by_cases hji : j = i
  · subst hji; simp
  · simp [hji]

end CommRing

end AlternatingMap
