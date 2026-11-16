/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Multilinear maps on localized modules

Let `R` be a commutative semiring, `S : Submonoid R` a submonoid, and `Rₛ` a localization of `R`
at `S`. Given a finite family of localization maps `g i : M i →ₗ[R] Mₛ i` at `S` into
`Rₛ`-modules and an `Rₛ`-module `N`, every `R`-multilinear map `f : (∀ i, M i) →ₘₗ[R] N` extends
uniquely to an `Rₛ`-multilinear map `extendMultilinear S Rₛ g f : (∀ i, Mₛ i) →ₘₗ[Rₛ] N`
satisfying `F (fun i => g i (m i)) = f m` for all `m`.

Since the index type is finite, each tuple `v : ∀ i, Mₛ i` admits denominators `s : ι → S` and
numerators `m : ∀ i, M i` with `s i • v i = g i (m i)`, and `Rₛ`-multilinearity forces
`F v = IsLocalization.mk' Rₛ 1 (∏ i, s i) • f m`. This works over any commutative semiring and
without requiring any `g i` to be injective, including in arity zero (`IsEmpty ι`).

## Main definitions

* `IsLocalizedModule.extendMultilinear`: the unique `Rₛ`-multilinear extension of an
  `R`-multilinear map along a finite family of module localizations at `S`.

## Main results

* `IsLocalizedModule.extendMultilinear_apply_of_smul_eq`: explicit formula for the extension on a
  tuple cleared by denominators `s : ι → S`.
* `IsLocalizedModule.extendMultilinear_apply_comp`: the extension restricts to `f` along `g`.
* `IsLocalizedModule.extendMultilinear_apply_mk'`: evaluation on a tuple of fractions
  `IsLocalizedModule.mk' (g i) (m i) (s i)`.
* `IsLocalizedModule.multilinearMap_ext`: two `Rₛ`-multilinear maps agreeing along `g` are equal.
* `IsLocalizedModule.extendMultilinear_unique` and
  `IsLocalizedModule.existsUnique_extendMultilinear`: uniqueness of the `Rₛ`-multilinear
  extension.
-/

public section

noncomputable section

open Function

namespace IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable (Rₛ : Type*) [CommSemiring Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
variable {ι : Type*}
variable {M Mₛ : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (Mₛ i)]
variable [∀ i, Module R (M i)] [∀ i, Module R (Mₛ i)] [∀ i, Module Rₛ (Mₛ i)]
variable [∀ i, IsScalarTower R Rₛ (Mₛ i)]
variable (g : ∀ i, M i →ₗ[R] Mₛ i) [∀ i, IsLocalizedModule S (g i)]
variable {N : Type*} [AddCommMonoid N] [Module Rₛ N]

private theorem mk'_one_smul_algebraMap_smul (a : S) (x : N) :
    IsLocalization.mk' Rₛ 1 a • (algebraMap R Rₛ a • x) = x := by
  rw [smul_smul, IsLocalization.mk'_spec, map_one, one_smul]

private theorem mk'_one_mul_smul_algebraMap_smul (a b : S) (x : N) :
    IsLocalization.mk' Rₛ 1 (a * b) • (algebraMap R Rₛ a • x) =
      IsLocalization.mk' Rₛ 1 b • x := by
  have hmul : IsLocalization.mk' Rₛ 1 (a * b) =
      IsLocalization.mk' Rₛ 1 b * IsLocalization.mk' Rₛ 1 a := by
    rw [← IsLocalization.mk'_mul, one_mul, mul_comm]
  rw [hmul, mul_smul, mk'_one_smul_algebraMap_smul]

variable [Module R N] [IsScalarTower R Rₛ N]

section FintypeAux

variable [Fintype ι]

omit [∀ i, Module Rₛ (Mₛ i)] [∀ i, IsScalarTower R Rₛ (Mₛ i)] in
private theorem inv_prod_smul_eq (f : (∀ i, M i) →ₘₗ[R] N) {v : ∀ i, Mₛ i}
    {m n : ∀ i, M i} {s t : ι → S}
    (hm : ∀ i, s i • v i = g i (m i)) (hn : ∀ i, t i • v i = g i (n i)) :
    IsLocalization.mk' Rₛ 1 (∏ i, s i) • f m =
      IsLocalization.mk' Rₛ 1 (∏ i, t i) • f n := by
  have hgm (i : ι) : g i (t i • m i) = g i (s i • n i) := by
    rw [Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul, ← Submonoid.smul_def,
      ← Submonoid.smul_def, ← hm i, ← hn i, smul_comm]
  choose c hc using fun i => IsLocalizedModule.exists_of_eq (S := S) (f := g i) (hgm i)
  have heq : (fun i => ((c i * t i : S) : R) • m i) =
      fun i => ((c i * s i : S) : R) • n i := funext fun i => by
    simpa only [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def] using hc i
  have hf := congrArg f heq
  simp only [f.map_smul_univ, RingHom.id_apply, Submonoid.coe_mul, Finset.prod_mul_distrib] at hf
  have hf' : algebraMap R Rₛ (∏ i, c i : S) • (algebraMap R Rₛ (∏ i, t i : S) • f m) =
      algebraMap R Rₛ (∏ i, c i : S) • (algebraMap R Rₛ (∏ i, s i : S) • f n) := by
    simpa only [Submonoid.coe_finsetProd, algebraMap_smul, smul_smul] using hf
  have hf'' : algebraMap R Rₛ (∏ i, t i : S) • f m =
      algebraMap R Rₛ (∏ i, s i : S) • f n := by
    have h := congrArg (IsLocalization.mk' Rₛ 1 (∏ i, c i) • ·) hf'
    simpa only [mk'_one_smul_algebraMap_smul] using h
  calc IsLocalization.mk' Rₛ 1 (∏ i, s i) • f m
      = IsLocalization.mk' Rₛ 1 (∏ i, s i) •
          (IsLocalization.mk' Rₛ 1 (∏ i, t i) • (algebraMap R Rₛ (∏ i, t i : S) • f m)) := by
        rw [mk'_one_smul_algebraMap_smul]
    _ = IsLocalization.mk' Rₛ 1 (∏ i, s i) •
          (IsLocalization.mk' Rₛ 1 (∏ i, t i) • (algebraMap R Rₛ (∏ i, s i : S) • f n)) := by
        rw [hf'']
    _ = IsLocalization.mk' Rₛ 1 (∏ i, t i) •
          (IsLocalization.mk' Rₛ 1 (∏ i, s i) • (algebraMap R Rₛ (∏ i, s i : S) • f n)) := by
        rw [smul_comm]
    _ = IsLocalization.mk' Rₛ 1 (∏ i, t i) • f n := by
        rw [mk'_one_smul_algebraMap_smul]

private def extendMultilinearAuxFun (f : (∀ i, M i) →ₘₗ[R] N) (v : ∀ i, Mₛ i) : N :=
  let rep := fun i => Classical.choose (IsLocalizedModule.surj S (g i) (v i))
  IsLocalization.mk' Rₛ 1 (∏ i, (rep i).2) • f (fun i => (rep i).1)

omit [∀ i, Module Rₛ (Mₛ i)] [∀ i, IsScalarTower R Rₛ (Mₛ i)] in
private theorem extendMultilinearAuxFun_eq (f : (∀ i, M i) →ₘₗ[R] N) {v : ∀ i, Mₛ i}
    {m : ∀ i, M i} {s : ι → S} (h : ∀ i, s i • v i = g i (m i)) :
    extendMultilinearAuxFun S Rₛ g f v = IsLocalization.mk' Rₛ 1 (∏ i, s i) • f m :=
  inv_prod_smul_eq S Rₛ g f (fun i => Classical.choose_spec (IsLocalizedModule.surj S (g i) (v i)))
    h

omit [∀ i, Module Rₛ (Mₛ i)] [∀ i, IsScalarTower R Rₛ (Mₛ i)] in
private theorem extendMultilinearAuxFun_update_add [DecidableEq ι] (f : (∀ i, M i) →ₘₗ[R] N)
    (v : ∀ i, Mₛ i) (i : ι) (x y : Mₛ i) :
    extendMultilinearAuxFun S Rₛ g f (update v i (x + y)) =
      extendMultilinearAuxFun S Rₛ g f (update v i x) +
        extendMultilinearAuxFun S Rₛ g f (update v i y) := by
  choose rep hv using fun j => IsLocalizedModule.surj S (g j) (v j)
  obtain ⟨⟨mx, sx⟩, hx⟩ := IsLocalizedModule.surj S (g i) x
  obtain ⟨⟨my, sy⟩, hy⟩ := IsLocalizedModule.surj S (g i) y
  dsimp only at hx hy
  let m : ∀ j, M j := fun j => (rep j).1
  let s : ι → S := fun j => (rep j).2
  have hxy : ∀ j, update s i (sx * sy) j • update v i (x + y) j =
      g j (update m i (sy • mx + sx • my) j) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp only [update_self, map_add, smul_add, mul_smul]
      rw [hy, smul_comm sx sy x, hx]
      simp only [Submonoid.smul_def, map_smul]
    · simp only [update_of_ne hji]
      exact hv j
  have hx' : ∀ j, update s i sx j • update v i x j = g j (update m i mx j) := by
    intro j
    by_cases hji : j = i
    · subst hji; simpa using hx
    · simpa [update_of_ne hji] using hv j
  have hy' : ∀ j, update s i sy j • update v i y j = g j (update m i my j) := by
    intro j
    by_cases hji : j = i
    · subst hji; simpa using hy
    · simpa [update_of_ne hji] using hv j
  rw [extendMultilinearAuxFun_eq S Rₛ g f hxy, extendMultilinearAuxFun_eq S Rₛ g f hx',
    extendMultilinearAuxFun_eq S Rₛ g f hy']
  let p : S := ∏ j ∈ Finset.univ.erase i, s j
  have hprod (t : S) : ∏ j, update s i t j = t * p := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => update_of_ne (Finset.ne_of_mem_erase hj) t s
  rw [hprod (sx * sy), hprod sx, hprod sy, f.map_update_add, Submonoid.smul_def, Submonoid.smul_def,
    f.map_update_smul, f.map_update_smul, RingHom.id_apply, RingHom.id_apply, smul_add]
  congr 1
  · rw [← algebraMap_smul Rₛ (sy : R), mul_comm sx sy, mul_assoc,
      mk'_one_mul_smul_algebraMap_smul]
  · rw [← algebraMap_smul Rₛ (sx : R), mul_assoc,
      mk'_one_mul_smul_algebraMap_smul]

private theorem extendMultilinearAuxFun_update_smul [DecidableEq ι] (f : (∀ i, M i) →ₘₗ[R] N)
    (v : ∀ i, Mₛ i) (i : ι) (a : Rₛ) (x : Mₛ i) :
    extendMultilinearAuxFun S Rₛ g f (update v i (a • x)) =
      a • extendMultilinearAuxFun S Rₛ g f (update v i x) := by
  choose rep hv using fun j => IsLocalizedModule.surj S (g j) (v j)
  obtain ⟨⟨mx, sx⟩, hx⟩ := IsLocalizedModule.surj S (g i) x
  obtain ⟨⟨r, t⟩, ha⟩ := IsLocalization.surj S a
  dsimp only at hx ha
  let m : ∀ j, M j := fun j => (rep j).1
  let s : ι → S := fun j => (rep j).2
  have hax : ∀ j, update s i (t * sx) j • update v i (a • x) j =
      g j (update m i (r • mx) j) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp only [update_self, map_smul, Submonoid.smul_def, Submonoid.coe_mul]
      rw [mul_comm (t : R) (sx : R), ← algebraMap_smul Rₛ ((sx : R) * (t : R)), map_mul, mul_smul,
        ← mul_smul (algebraMap R Rₛ (t : R)) a x, mul_comm (algebraMap R Rₛ (t : R)) a, ha,
        algebraMap_smul, algebraMap_smul, smul_comm (sx : R) r x, ← Submonoid.smul_def, hx]
    · simp only [update_of_ne hji]
      exact hv j
  have hx' : ∀ j, update s i sx j • update v i x j = g j (update m i mx j) := by
    intro j
    by_cases hji : j = i
    · subst hji; simpa using hx
    · simpa [update_of_ne hji] using hv j
  rw [extendMultilinearAuxFun_eq S Rₛ g f hax, extendMultilinearAuxFun_eq S Rₛ g f hx']
  let p : S := ∏ j ∈ Finset.univ.erase i, s j
  have hprod (u : S) : ∏ j, update s i u j = u * p := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => update_of_ne (Finset.ne_of_mem_erase hj) u s
  rw [hprod (t * sx), hprod sx, f.map_update_smul, RingHom.id_apply, ← algebraMap_smul Rₛ r, ← ha,
    mul_smul, mul_assoc, smul_comm (IsLocalization.mk' Rₛ 1 (t * (sx * p))) a,
    mk'_one_mul_smul_algebraMap_smul]

end FintypeAux

variable [Finite ι]

/-- The unique `Rₛ`-multilinear extension of an `R`-multilinear map `f : (∀ i, M i) →ₘₗ[R] N`
along a finite family of module localizations `g i : M i →ₗ[R] Mₛ i` at `S`. -/
def extendMultilinear (f : (∀ i, M i) →ₘₗ[R] N) : (∀ i, Mₛ i) →ₘₗ[Rₛ] N :=
  letI : Fintype ι := Fintype.ofFinite ι
  { toFun := extendMultilinearAuxFun S Rₛ g f
    map_update_add' := fun _ _ _ _ => extendMultilinearAuxFun_update_add S Rₛ g f _ _ _ _
    map_update_smul' := fun _ _ _ _ => extendMultilinearAuxFun_update_smul S Rₛ g f _ _ _ _ }

/-- If denominators `s : ι → S` clear `v` into the images `g i (m i)`, then `extendMultilinear`
evaluates `f m` divided by `∏ i, s i`. -/
theorem extendMultilinear_apply_of_smul_eq [inst : Fintype ι] (f : (∀ i, M i) →ₘₗ[R] N)
    {v : ∀ i, Mₛ i} {m : ∀ i, M i} {s : ι → S} (h : ∀ i, s i • v i = g i (m i)) :
    extendMultilinear S Rₛ g f v = IsLocalization.mk' Rₛ 1 (∏ i, s i) • f m := by
  obtain rfl : inst = Fintype.ofFinite ι := Subsingleton.elim _ _
  let : Fintype ι := Fintype.ofFinite ι
  exact extendMultilinearAuxFun_eq S Rₛ g f h

/-- The extended multilinear map agrees with `f` on tuples coming from `g`. -/
@[simp]
theorem extendMultilinear_apply_comp (f : (∀ i, M i) →ₘₗ[R] N) (m : ∀ i, M i) :
    extendMultilinear S Rₛ g f (fun i => g i (m i)) = f m := by
  cases nonempty_fintype ι
  have h := extendMultilinear_apply_of_smul_eq S Rₛ g f (s := fun _ => 1) (m := m)
    (fun i => one_smul S (g i (m i)))
  simpa [IsLocalization.mk'_one] using h

/-- Evaluation of `extendMultilinear` on a tuple of fractions `mk' (g i) (m i) (s i)`. -/
@[simp]
theorem extendMultilinear_apply_mk' [Fintype ι] (f : (∀ i, M i) →ₘₗ[R] N)
    (m : ∀ i, M i) (s : ι → S) :
    extendMultilinear S Rₛ g f (fun i => IsLocalizedModule.mk' (g i) (m i) (s i)) =
      IsLocalization.mk' Rₛ 1 (∏ i, s i) • f m :=
  extendMultilinear_apply_of_smul_eq S Rₛ g f fun i =>
    IsLocalizedModule.mk'_cancel' (g i) (m i) (s i)

omit [Module R N] [IsScalarTower R Rₛ N] in
include S in
/-- Two `Rₛ`-multilinear maps from localized modules are equal if they agree on all tuples in the
images of the localization maps `g i`. -/
theorem multilinearMap_ext {F G : (∀ i, Mₛ i) →ₘₗ[Rₛ] N}
    (h : ∀ m : ∀ i, M i, F (fun i => g i (m i)) = G (fun i => g i (m i))) : F = G := by
  cases nonempty_fintype ι
  ext v
  choose rep hv using fun i => IsLocalizedModule.surj S (g i) (v i)
  have hF : algebraMap R Rₛ (∏ i, (rep i).2 : S) • F v = F (fun i => g i (rep i).1) := by
    simpa only [Submonoid.coe_finsetProd, map_prod, RingHom.id_apply, algebraMap_smul,
      ← Submonoid.smul_def, hv] using (F.map_smul_univ (fun i => algebraMap R Rₛ (rep i).2) v).symm
  have hG : algebraMap R Rₛ (∏ i, (rep i).2 : S) • G v = G (fun i => g i (rep i).1) := by
    simpa only [Submonoid.coe_finsetProd, map_prod, RingHom.id_apply, algebraMap_smul,
      ← Submonoid.smul_def, hv] using (G.map_smul_univ (fun i => algebraMap R Rₛ (rep i).2) v).symm
  calc F v = IsLocalization.mk' Rₛ 1 (∏ i, (rep i).2) •
          (algebraMap R Rₛ (∏ i, (rep i).2 : S) • F v) :=
        (mk'_one_smul_algebraMap_smul S Rₛ _ _).symm
    _ = IsLocalization.mk' Rₛ 1 (∏ i, (rep i).2) • F (fun i => g i (rep i).1) := by rw [hF]
    _ = IsLocalization.mk' Rₛ 1 (∏ i, (rep i).2) • G (fun i => g i (rep i).1) := by rw [h]
    _ = IsLocalization.mk' Rₛ 1 (∏ i, (rep i).2) •
          (algebraMap R Rₛ (∏ i, (rep i).2 : S) • G v) := by rw [hG]
    _ = G v := mk'_one_smul_algebraMap_smul S Rₛ _ _

/-- Any `Rₛ`-multilinear map extending `f` along `g` is equal to `extendMultilinear S Rₛ g f`. -/
theorem extendMultilinear_unique (f : (∀ i, M i) →ₘₗ[R] N) {F : (∀ i, Mₛ i) →ₘₗ[Rₛ] N}
    (h : ∀ m : ∀ i, M i, F (fun i => g i (m i)) = f m) :
    F = extendMultilinear S Rₛ g f :=
  multilinearMap_ext S Rₛ g fun m => by rw [h, extendMultilinear_apply_comp]

include S in
/-- Every `R`-multilinear map on a finite family of modules extends uniquely to an
`Rₛ`-multilinear map on their localizations at `S`. -/
theorem existsUnique_extendMultilinear (f : (∀ i, M i) →ₘₗ[R] N) :
    ∃! F : (∀ i, Mₛ i) →ₘₗ[Rₛ] N, ∀ m : ∀ i, M i, F (fun i => g i (m i)) = f m :=
  ⟨extendMultilinear S Rₛ g f, extendMultilinear_apply_comp S Rₛ g f,
    fun _ h => extendMultilinear_unique S Rₛ g f h⟩

@[simp]
theorem extendMultilinear_zero :
    extendMultilinear S Rₛ g (0 : (∀ i, M i) →ₘₗ[R] N) = 0 :=
  (extendMultilinear_unique S Rₛ g 0 fun _ => rfl).symm

@[simp]
theorem extendMultilinear_add (f₁ f₂ : (∀ i, M i) →ₘₗ[R] N) :
    extendMultilinear S Rₛ g (f₁ + f₂) =
      extendMultilinear S Rₛ g f₁ + extendMultilinear S Rₛ g f₂ :=
  (extendMultilinear_unique S Rₛ g (f₁ + f₂) fun m => by simp).symm

@[simp]
theorem extendMultilinear_smul (a : Rₛ) (f : (∀ i, M i) →ₘₗ[R] N) :
    extendMultilinear S Rₛ g (a • f) = a • extendMultilinear S Rₛ g f :=
  (extendMultilinear_unique S Rₛ g (a • f) fun m => by simp).symm

end IsLocalizedModule
