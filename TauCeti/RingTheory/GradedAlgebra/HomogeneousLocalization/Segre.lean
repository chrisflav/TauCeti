/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
public import TauCeti.RingTheory.GradedAlgebra.Segre

/-!
# Homogeneous localizations of a Segre product

Let `A = ⨁ᵢ 𝒜 i` and `B = ⨁ᵢ ℬ i` be `ι`-graded commutative `R`-algebras, and let `a ∈ 𝒜 d` and
`b ∈ ℬ d` be homogeneous elements of the same degree `d`. On the Segre product
`A ♯ B = Segre 𝒜 ℬ`, the pure tensor `a ⊗ₜ b` has degree `d`, and the standard affine chart
`(A ♯ B)_{(a ⊗ₜ b)}` is canonically isomorphic as an `R`-algebra to `A_{(a)} ⊗[R] B_{(b)}`:

`Away 𝒜 a ⊗[R] Away ℬ b ≃ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)`.

These chart isomorphisms, together with the compatibility of the factor inclusions
`Away 𝒜 a →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)` (`x / aⁿ ↦ (x ⊗ₜ bⁿ) / (a ⊗ₜ b)ⁿ`) and
`Away ℬ b →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)` (`y / bⁿ ↦ (aⁿ ⊗ₜ y) / (a ⊗ₜ b)ⁿ`) with
the transition maps `awayMap`, provide the affine inputs to the Segre fibre-product isomorphism
`Proj (Segre.grading 𝒜 ℬ) ≅ Proj 𝒜 ×_{Spec R} Proj ℬ`.

## Main definitions

* `HomogeneousLocalization.Away.segreFst`: the canonical `R`-algebra map
  `Away 𝒜 a →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)`.
* `HomogeneousLocalization.Away.segreSnd`: the canonical `R`-algebra map
  `Away ℬ b →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)`.
* `HomogeneousLocalization.Away.segreHom`: the `R`-algebra map
  `Away 𝒜 a ⊗[R] Away ℬ b →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)`.
* `HomogeneousLocalization.Away.segreEquiv`: the `R`-algebra isomorphism
  `Away 𝒜 a ⊗[R] Away ℬ b ≃ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)`.

## Main results

* `HomogeneousLocalization.Away.segreFst_awayMap` and
  `HomogeneousLocalization.Away.segreSnd_awayMap`: compatibility of `segreFst` and `segreSnd` with
  chart transition maps `awayMap`.
* `HomogeneousLocalization.Away.segreFst_isLocalizationElem_mul_segreSnd_isLocalizationElem`: for
  `ℕ`-gradings, the product of the images of `Away.isLocalizationElem` from the two factors is
  `Away.isLocalizationElem` on the Segre chart.

## References

* A. Grothendieck, *Éléments de géométrie algébrique. II. Étude globale élémentaire de quelques
  classes de morphismes*, Publ. Math. IHÉS 8 (1961), §3.1.4 and Proposition 3.1.8.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Exercise II.5.11.
-/

public section

open TauCeti.GradedAlgebra
open scoped TensorProduct

namespace HomogeneousLocalization.Away

section General

variable {ι R A B : Type*} [AddCommMonoid ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

section Embedding

private def segreToLoc (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ] (a : A) (b : B) :
    Segre 𝒜 ℬ →+* Localization.Away (a ⊗ₜ[R] b) :=
  (algebraMap (A ⊗[R] B) (Localization.Away (a ⊗ₜ[R] b))).comp
    (Segre.toTensorProduct (𝒜 := 𝒜) (ℬ := ℬ)).toRingHom

variable {d : ι} {a : A} {b : B} (ha : a ∈ 𝒜 d) (hb : b ∈ ℬ d)

private theorem isUnit_segreToLoc :
    IsUnit (segreToLoc 𝒜 ℬ a b (Segre.tmul ha hb)) := by
  rw [segreToLoc, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Segre.toTensorProduct_tmul]
  exact IsLocalization.Away.algebraMap_isUnit (a ⊗ₜ[R] b)

/-- The injective `R`-algebra embedding of `Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)` into the
ordinary localization `Localization.Away (a ⊗ₜ[R] b)`. -/
private noncomputable def segreValAlgHom :
    Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb) →ₐ[R] Localization.Away (a ⊗ₜ[R] b) where
  toRingHom := Away.lift (Segre.grading 𝒜 ℬ) (segreToLoc 𝒜 ℬ a b) (isUnit_segreToLoc ha hb)
  commutes' r := by
    -- `algebraMap R` factors through `Segre.grading 𝒜 ℬ 0` via `fromZeroRingHom`.
    change Away.lift (Segre.grading 𝒜 ℬ) _ _
      (algebraMap (Segre.grading 𝒜 ℬ 0) (Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb))
        (algebraMap R (Segre.grading 𝒜 ℬ 0) r)) = _
    rw [Away.lift_algebraMap, segreToLoc, RingHom.comp_apply, SetLike.GradeZero.coe_algebraMap,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

private theorem segreValAlgHom_mk (hs : Segre.tmul ha hb ∈ Segre.grading 𝒜 ℬ d)
    (n : ℕ) (x : Segre 𝒜 ℬ) (hx : x ∈ Segre.grading 𝒜 ℬ (n • d)) :
    segreValAlgHom ha hb (Away.mk (Segre.grading 𝒜 ℬ) hs n x hx) =
      Localization.mk (Segre.toTensorProduct x)
        (⟨(a ⊗ₜ[R] b) ^ n, pow_mem (Submonoid.mem_powers (a ⊗ₜ[R] b)) n⟩ :
          Submonoid.powers (a ⊗ₜ[R] b)) := by
  let u := isUnit_segreToLoc ha hb
  have hu : ((u.unit ^ n : (Localization.Away (a ⊗ₜ[R] b))ˣ) : Localization.Away (a ⊗ₜ[R] b)) =
      algebraMap (A ⊗[R] B) (Localization.Away (a ⊗ₜ[R] b)) ((a ⊗ₜ[R] b) ^ n) := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, segreToLoc, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Segre.toTensorProduct_tmul, map_pow]
  -- Unfold `segreValAlgHom` to `Away.lift` so `Away.lift_mk` applies.
  change Away.lift (Segre.grading 𝒜 ℬ) _ u (Away.mk (Segre.grading 𝒜 ℬ) hs n x hx) = _
  rw [Away.lift_mk, Units.mul_inv_eq_iff_eq_mul, hu, segreToLoc, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← Localization.mk_one_eq_algebraMap,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp [mul_comm]

private theorem segreValAlgHom_injective : Function.Injective (segreValAlgHom ha hb) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, s, hs, rfl⟩ :=
    Away.mk_surjective (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha hb) z
  rw [segreValAlgHom_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hz
  obtain ⟨⟨_, k, rfl⟩, hc⟩ := hz
  apply val_injective
  rw [Away.val_mk, val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨Segre.tmul ha hb ^ k, k, rfl⟩, Segre.ext_toTensorProduct ?_⟩
  simpa using hc

end Embedding

section FactorMaps

private def includeLeftComp (a : A) (b : B) : A →+* Localization.Away (a ⊗ₜ[R] b) :=
  (algebraMap (A ⊗[R] B) (Localization.Away (a ⊗ₜ[R] b))).comp
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom

private def includeRightComp (a : A) (b : B) : B →+* Localization.Away (a ⊗ₜ[R] b) :=
  (algebraMap (A ⊗[R] B) (Localization.Away (a ⊗ₜ[R] b))).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom

private theorem isUnit_includeLeftComp (a : A) (b : B) :
    IsUnit (includeLeftComp (R := R) a b a) := by
  rw [includeLeftComp, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeft_apply]
  exact isUnit_of_dvd_unit
    (map_dvd (algebraMap (A ⊗[R] B) (Localization.Away (a ⊗ₜ[R] b)))
      ⟨1 ⊗ₜ[R] b, by simp⟩)
    (IsLocalization.Away.algebraMap_isUnit (a ⊗ₜ[R] b))

private theorem isUnit_includeRightComp (a : A) (b : B) :
    IsUnit (includeRightComp (R := R) a b b) := by
  rw [includeRightComp, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]
  exact isUnit_of_dvd_unit
    (map_dvd (algebraMap (A ⊗[R] B) (Localization.Away (a ⊗ₜ[R] b)))
      ⟨a ⊗ₜ[R] 1, by simp⟩)
    (IsLocalization.Away.algebraMap_isUnit (a ⊗ₜ[R] b))

/-- Auxiliary lift of the first factor into `Localization.Away (a ⊗ₜ[R] b)`. -/
private noncomputable def segreFstAux (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (a : A) (b : B) : Away 𝒜 a →ₐ[R] Localization.Away (a ⊗ₜ[R] b) where
  toRingHom := Away.lift 𝒜 (includeLeftComp (R := R) a b) (isUnit_includeLeftComp (R := R) a b)
  commutes' r := by
    -- `algebraMap R` factors through `𝒜 0` via `fromZeroRingHom`.
    change Away.lift 𝒜 _ _ (algebraMap (𝒜 0) (Away 𝒜 a) (algebraMap R (𝒜 0) r)) = _
    rw [Away.lift_algebraMap, includeLeftComp, RingHom.comp_apply,
      SetLike.GradeZero.coe_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/-- Auxiliary lift of the second factor into `Localization.Away (a ⊗ₜ[R] b)`. -/
private noncomputable def segreSndAux (ℬ : ι → Submodule R B) [GradedAlgebra ℬ]
    (a : A) (b : B) : Away ℬ b →ₐ[R] Localization.Away (a ⊗ₜ[R] b) where
  toRingHom := Away.lift ℬ (includeRightComp (R := R) a b) (isUnit_includeRightComp (R := R) a b)
  commutes' r := by
    -- `algebraMap R` factors through `ℬ 0` via `fromZeroRingHom`.
    change Away.lift ℬ _ _ (algebraMap (ℬ 0) (Away ℬ b) (algebraMap R (ℬ 0) r)) = _
    rw [Away.lift_algebraMap, includeRightComp, RingHom.comp_apply,
      SetLike.GradeZero.coe_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

variable {d : ι} {a : A} {b : B} (ha : a ∈ 𝒜 d) (hb : b ∈ ℬ d)

private theorem segreFstAux_mk (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) :
    segreFstAux 𝒜 a b (Away.mk 𝒜 ha n x hx) =
      segreValAlgHom ha hb
        (Away.mk (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha hb) n
          (Segre.tmul hx (SetLike.pow_mem_graded n hb))
          (Segre.tmul_mem_grading hx (SetLike.pow_mem_graded n hb))) := by
  let u := isUnit_includeLeftComp (R := R) a b
  have hu : ((u.unit ^ n : (Localization.Away (a ⊗ₜ[R] b))ˣ) : Localization.Away (a ⊗ₜ[R] b)) =
      algebraMap (A ⊗[R] B) (Localization.Away (a ⊗ₜ[R] b)) ((a ^ n) ⊗ₜ[R] 1) := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, includeLeftComp, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
      ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  -- Unfold `segreFstAux` to `Away.lift` so `Away.lift_mk` applies.
  change Away.lift 𝒜 _ u (Away.mk 𝒜 ha n x hx) = _
  rw [Away.lift_mk, segreValAlgHom_mk, Units.mul_inv_eq_iff_eq_mul, hu, includeLeftComp,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeft_apply, ← Localization.mk_one_eq_algebraMap,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp [Algebra.TensorProduct.tmul_pow, mul_comm]

private theorem segreSndAux_mk (n : ℕ) (y : B) (hy : y ∈ ℬ (n • d)) :
    segreSndAux ℬ a b (Away.mk ℬ hb n y hy) =
      segreValAlgHom ha hb
        (Away.mk (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha hb) n
          (Segre.tmul (SetLike.pow_mem_graded n ha) hy)
          (Segre.tmul_mem_grading (SetLike.pow_mem_graded n ha) hy)) := by
  let u := isUnit_includeRightComp (R := R) a b
  have hu : ((u.unit ^ n : (Localization.Away (a ⊗ₜ[R] b))ˣ) : Localization.Away (a ⊗ₜ[R] b)) =
      algebraMap (A ⊗[R] B) (Localization.Away (a ⊗ₜ[R] b)) (1 ⊗ₜ[R] (b ^ n)) := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, includeRightComp, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  -- Unfold `segreSndAux` to `Away.lift` so `Away.lift_mk` applies.
  change Away.lift ℬ _ u (Away.mk ℬ hb n y hy) = _
  rw [Away.lift_mk, segreValAlgHom_mk, Units.mul_inv_eq_iff_eq_mul, hu, includeRightComp,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, ← Localization.mk_one_eq_algebraMap,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp [Algebra.TensorProduct.tmul_pow, mul_comm]

/-- The canonical `R`-algebra homomorphism
`Away 𝒜 a →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)` sending `x / aⁿ` to
`(x ⊗ₜ bⁿ) / (a ⊗ₜ b)ⁿ`. -/
noncomputable def segreFst :
    Away 𝒜 a →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb) :=
  (AlgEquiv.ofInjective (segreValAlgHom ha hb) (segreValAlgHom_injective ha hb)).symm.toAlgHom.comp
    ((segreFstAux 𝒜 a b).codRestrict (segreValAlgHom ha hb).range fun z ↦ by
      obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 ha z
      exact ⟨_, (segreFstAux_mk ha hb n x hx).symm⟩)

/-- The canonical `R`-algebra homomorphism
`Away ℬ b →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)` sending `y / bⁿ` to
`(aⁿ ⊗ₜ y) / (a ⊗ₜ b)ⁿ`. -/
noncomputable def segreSnd :
    Away ℬ b →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb) :=
  (AlgEquiv.ofInjective (segreValAlgHom ha hb) (segreValAlgHom_injective ha hb)).symm.toAlgHom.comp
    ((segreSndAux ℬ a b).codRestrict (segreValAlgHom ha hb).range fun z ↦ by
      obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective ℬ hb z
      exact ⟨_, (segreSndAux_mk ha hb n y hy).symm⟩)

private theorem segreValAlgHom_segreFst (z : Away 𝒜 a) :
    segreValAlgHom ha hb (segreFst ha hb z) = segreFstAux 𝒜 a b z := by
  have h := (AlgEquiv.ofInjective (segreValAlgHom ha hb)
    (segreValAlgHom_injective ha hb)).apply_symm_apply
    ⟨segreFstAux 𝒜 a b z, by
      obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 ha z
      exact ⟨_, (segreFstAux_mk ha hb n x hx).symm⟩⟩
  exact congrArg Subtype.val h

private theorem segreValAlgHom_segreSnd (z : Away ℬ b) :
    segreValAlgHom ha hb (segreSnd ha hb z) = segreSndAux ℬ a b z := by
  have h := (AlgEquiv.ofInjective (segreValAlgHom ha hb)
    (segreValAlgHom_injective ha hb)).apply_symm_apply
    ⟨segreSndAux ℬ a b z, by
      obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective ℬ hb z
      exact ⟨_, (segreSndAux_mk ha hb n y hy).symm⟩⟩
  exact congrArg Subtype.val h

/-- `segreFst` sends `x / aⁿ` to `(x ⊗ₜ bⁿ) / (a ⊗ₜ b)ⁿ`. -/
@[simp]
theorem segreFst_mk (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) :
    segreFst ha hb (Away.mk 𝒜 ha n x hx) =
      Away.mk (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha hb) n
        (Segre.tmul hx (SetLike.pow_mem_graded n hb))
        (Segre.tmul_mem_grading hx (SetLike.pow_mem_graded n hb)) :=
  segreValAlgHom_injective ha hb <|
    (segreValAlgHom_segreFst ha hb _).trans (segreFstAux_mk ha hb n x hx)

/-- `segreSnd` sends `y / bⁿ` to `(aⁿ ⊗ₜ y) / (a ⊗ₜ b)ⁿ`. -/
@[simp]
theorem segreSnd_mk (n : ℕ) (y : B) (hy : y ∈ ℬ (n • d)) :
    segreSnd ha hb (Away.mk ℬ hb n y hy) =
      Away.mk (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha hb) n
        (Segre.tmul (SetLike.pow_mem_graded n ha) hy)
        (Segre.tmul_mem_grading (SetLike.pow_mem_graded n ha) hy) :=
  segreValAlgHom_injective ha hb <|
    (segreValAlgHom_segreSnd ha hb _).trans (segreSndAux_mk ha hb n y hy)

/-- `segreFst` commutes with the chart transition maps `awayMap`. -/
theorem segreFst_awayMap {e : ι} {a' x : A} {b' y : B}
    (ha' : a' ∈ 𝒜 e) (hb' : b' ∈ ℬ e) (hx : x = a * a') (hy : y = b * b')
    (hx_mem : x ∈ 𝒜 (d + e)) (hy_mem : y ∈ ℬ (d + e))
    (hw : Segre.tmul hx_mem hy_mem = Segre.tmul ha hb * Segre.tmul ha' hb') (z : Away 𝒜 a) :
    awayMap (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha' hb') hw (segreFst ha hb z) =
      segreFst hx_mem hy_mem (awayMap 𝒜 ha' hx z) := by
  subst hx hy
  obtain ⟨n, u, hu, rfl⟩ := Away.mk_surjective 𝒜 ha z
  apply segreValAlgHom_injective hx_mem hy_mem
  rw [segreFst_mk, awayMap_mk, awayMap_mk, segreFst_mk, segreValAlgHom_mk, segreValAlgHom_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, map_mul, map_pow, Segre.toTensorProduct_tmul,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_pow]

/-- `segreSnd` commutes with the chart transition maps `awayMap`. -/
theorem segreSnd_awayMap {e : ι} {a' x : A} {b' y : B}
    (ha' : a' ∈ 𝒜 e) (hb' : b' ∈ ℬ e) (hx : x = a * a') (hy : y = b * b')
    (hx_mem : x ∈ 𝒜 (d + e)) (hy_mem : y ∈ ℬ (d + e))
    (hw : Segre.tmul hx_mem hy_mem = Segre.tmul ha hb * Segre.tmul ha' hb') (z : Away ℬ b) :
    awayMap (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha' hb') hw (segreSnd ha hb z) =
      segreSnd hx_mem hy_mem (awayMap ℬ hb' hy z) := by
  subst hx hy
  obtain ⟨n, v, hv, rfl⟩ := Away.mk_surjective ℬ hb z
  apply segreValAlgHom_injective hx_mem hy_mem
  rw [segreSnd_mk, awayMap_mk, awayMap_mk, segreSnd_mk, segreValAlgHom_mk, segreValAlgHom_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, map_mul, map_pow, Segre.toTensorProduct_tmul,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_pow]

end FactorMaps

section TensorEquiv

variable {d : ι} {a : A} {b : B} (ha : a ∈ 𝒜 d) (hb : b ∈ ℬ d)

/-- The canonical `R`-algebra homomorphism
`Away 𝒜 a ⊗[R] Away ℬ b →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb)` combining `segreFst` and
`segreSnd`. -/
noncomputable def segreHom :
    Away 𝒜 a ⊗[R] Away ℬ b →ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb) :=
  Algebra.TensorProduct.lift (segreFst ha hb) (segreSnd ha hb)
    fun x y ↦ Commute.all (segreFst ha hb x) (segreSnd ha hb y)

@[simp]
theorem segreHom_tmul (x : Away 𝒜 a) (y : Away ℬ b) :
    segreHom ha hb (x ⊗ₜ[R] y) = segreFst ha hb x * segreSnd ha hb y :=
  Algebra.TensorProduct.lift_tmul _ _ _ x y

/-- On fractions over the same power `n`, `segreHom` sends `(x / aⁿ) ⊗ₜ (y / bⁿ)` to
`(x ⊗ₜ y) / (a ⊗ₜ b)ⁿ`. -/
theorem segreHom_tmul_mk_same (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) (y : B) (hy : y ∈ ℬ (n • d)) :
    segreHom ha hb (Away.mk 𝒜 ha n x hx ⊗ₜ[R] Away.mk ℬ hb n y hy) =
      Away.mk (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha hb) n
        (Segre.tmul hx hy) (Segre.tmul_mem_grading hx hy) := by
  apply segreValAlgHom_injective ha hb
  rw [segreHom_tmul, map_mul, segreFst_mk, segreSnd_mk, segreValAlgHom_mk, segreValAlgHom_mk,
    segreValAlgHom_mk, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, Segre.toTensorProduct_tmul,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
  congr 1 <;> ring

private theorem segreHom_map_mkLinearMap (n : ℕ) (u : 𝒜 (n • d) ⊗[R] ℬ (n • d)) :
    segreHom ha hb (TensorProduct.map (Away.mkLinearMap ha n) (Away.mkLinearMap hb n) u) =
      Away.mkLinearMap (Segre.tmul_mem_grading ha hb) n (Segre.gradingEquiv 𝒜 ℬ (n • d) u) := by
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, Away.mkLinearMap_apply, segreHom_tmul_mk_same,
      Segre.coe_gradingEquiv_tmul]
  | add u₁ u₂ hu₁ hu₂ => simp only [map_add, hu₁, hu₂]

private theorem map_mkLinearMap_promoteNumerator (n N : ℕ) (hnN : n ≤ N)
    (u : 𝒜 (n • d) ⊗[R] ℬ (n • d)) :
    TensorProduct.map (Away.mkLinearMap ha N) (Away.mkLinearMap hb N)
        (TensorProduct.map (Away.promoteNumerator ha n N hnN)
          (Away.promoteNumerator hb n N hnN) u) =
      TensorProduct.map (Away.mkLinearMap ha n) (Away.mkLinearMap hb n) u := by
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, Away.mkLinearMap_promoteNumerator]
  | add u₁ u₂ hu₁ hu₂ => simp only [map_add, hu₁, hu₂]

/-- Every element of `Away 𝒜 a ⊗[R] Away ℬ b` can be written over a single exponent `n`. -/
private theorem exists_eq_map_mkLinearMap (z : Away 𝒜 a ⊗[R] Away ℬ b) :
    ∃ (n : ℕ) (u : 𝒜 (n • d) ⊗[R] ℬ (n • d)),
      TensorProduct.map (Away.mkLinearMap ha n) (Away.mkLinearMap hb n) u = z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨n₁, x₀, hx₀, rfl⟩ := Away.mk_surjective 𝒜 ha x
    obtain ⟨n₂, y₀, hy₀, rfl⟩ := Away.mk_surjective ℬ hb y
    refine ⟨n₁ + n₂,
      Away.promoteNumerator ha n₁ (n₁ + n₂) (Nat.le_add_right n₁ n₂) ⟨x₀, hx₀⟩ ⊗ₜ[R]
        Away.promoteNumerator hb n₂ (n₁ + n₂) (Nat.le_add_left n₂ n₁) ⟨y₀, hy₀⟩, ?_⟩
    rw [TensorProduct.map_tmul, Away.mkLinearMap_promoteNumerator,
      Away.mkLinearMap_promoteNumerator, Away.mkLinearMap_apply, Away.mkLinearMap_apply]
  | add z₁ z₂ hz₁ hz₂ =>
    obtain ⟨n₁, u₁, rfl⟩ := hz₁
    obtain ⟨n₂, u₂, rfl⟩ := hz₂
    refine ⟨n₁ + n₂,
      TensorProduct.map (Away.promoteNumerator ha n₁ (n₁ + n₂) (Nat.le_add_right n₁ n₂))
        (Away.promoteNumerator hb n₁ (n₁ + n₂) (Nat.le_add_right n₁ n₂)) u₁ +
      TensorProduct.map (Away.promoteNumerator ha n₂ (n₁ + n₂) (Nat.le_add_left n₂ n₁))
        (Away.promoteNumerator hb n₂ (n₁ + n₂) (Nat.le_add_left n₂ n₁)) u₂, ?_⟩
    simp only [map_add, map_mkLinearMap_promoteNumerator]

/-- `segreHom` is surjective. -/
theorem segreHom_surjective : Function.Surjective (segreHom ha hb) := by
  intro w
  obtain ⟨n, s, hs, rfl⟩ :=
    Away.mk_surjective (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha hb) w
  refine ⟨TensorProduct.map (Away.mkLinearMap ha n) (Away.mkLinearMap hb n)
    ((Segre.gradingEquiv 𝒜 ℬ (n • d)).symm ⟨s, hs⟩), ?_⟩
  rw [segreHom_map_mkLinearMap, LinearEquiv.apply_symm_apply, Away.mkLinearMap_apply]

private theorem mapIncl_promoteNumerator (n N : ℕ) (hnN : n ≤ N)
    (u : 𝒜 (n • d) ⊗[R] ℬ (n • d)) :
    TensorProduct.mapIncl (𝒜 (N • d)) (ℬ (N • d))
        (TensorProduct.map (Away.promoteNumerator ha n N hnN)
          (Away.promoteNumerator hb n N hnN) u) =
      TensorProduct.mapIncl (𝒜 (n • d)) (ℬ (n • d)) u * (a ⊗ₜ[R] b) ^ (N - n) := by
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, TensorProduct.mapIncl, Submodule.subtype_apply,
      Away.coe_promoteNumerator, Algebra.TensorProduct.tmul_pow,
      Algebra.TensorProduct.tmul_mul_tmul]
  | add u₁ u₂ hu₁ hu₂ => simp only [map_add, add_mul, hu₁, hu₂]

/-- `segreHom` is injective. -/
theorem segreHom_injective : Function.Injective (segreHom ha hb) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, u, rfl⟩ := exists_eq_map_mkLinearMap ha hb z
  rw [segreHom_map_mkLinearMap] at hz
  have hval := congrArg HomogeneousLocalization.val hz
  simp only [Away.mkLinearMap_apply, Away.val_mk, val_zero, Localization.mk_eq_mk'] at hval
  obtain ⟨⟨_, k, rfl⟩, hc⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hval
  let N := n + k
  let u' := TensorProduct.map
    (Away.promoteNumerator ha n N (Nat.le_add_right n k))
    (Away.promoteNumerator hb n N (Nat.le_add_right n k)) u
  have hu' : u' = 0 := by
    apply Segre.mapIncl_grade_injective 𝒜 ℬ (N • d)
    rw [map_zero]
    dsimp only [u']
    rw [mapIncl_promoteNumerator, Nat.add_sub_cancel_left,
      ← Segre.toTensorProduct_gradingEquiv_apply]
    have hc' := congrArg (Segre.toTensorProduct (𝒜 := 𝒜) (ℬ := ℬ)) hc
    simpa only [map_mul, map_pow, Segre.toTensorProduct_tmul, map_zero,
      mul_comm ((a ⊗ₜ[R] b) ^ k)] using hc'
  calc
    TensorProduct.map (Away.mkLinearMap ha n) (Away.mkLinearMap hb n) u
      = TensorProduct.map (Away.mkLinearMap ha N) (Away.mkLinearMap hb N) u' :=
        (map_mkLinearMap_promoteNumerator ha hb n N (Nat.le_add_right n k) u).symm
    _ = 0 := by rw [hu', map_zero]

/-- **Standard affine charts of the Segre product**: for `a ∈ 𝒜 d` and `b ∈ ℬ d`, the
homogeneous localization of `Segre 𝒜 ℬ` away from `a ⊗ₜ b` is canonically isomorphic as an
`R`-algebra to `Away 𝒜 a ⊗[R] Away ℬ b`. -/
noncomputable def segreEquiv :
    Away 𝒜 a ⊗[R] Away ℬ b ≃ₐ[R] Away (Segre.grading 𝒜 ℬ) (Segre.tmul ha hb) :=
  AlgEquiv.ofBijective (segreHom ha hb)
    ⟨segreHom_injective ha hb, segreHom_surjective ha hb⟩

@[simp]
theorem segreEquiv_apply (z : Away 𝒜 a ⊗[R] Away ℬ b) :
    segreEquiv ha hb z = segreHom ha hb z :=
  -- `(rfl)`, not `rfl`: `segreEquiv` is not `@[expose]`d.
  (rfl)

/-- `segreEquiv` sends a pure tensor `x ⊗ₜ y` to `segreFst x * segreSnd y`. -/
theorem segreEquiv_tmul (x : Away 𝒜 a) (y : Away ℬ b) :
    segreEquiv ha hb (x ⊗ₜ[R] y) = segreFst ha hb x * segreSnd ha hb y :=
  segreHom_tmul ha hb x y

@[simp]
theorem segreEquiv_symm_mk (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) (y : B) (hy : y ∈ ℬ (n • d)) :
    (segreEquiv ha hb).symm
      (Away.mk (Segre.grading 𝒜 ℬ) (Segre.tmul_mem_grading ha hb) n
        (Segre.tmul hx hy) (Segre.tmul_mem_grading hx hy)) =
      Away.mk 𝒜 ha n x hx ⊗ₜ[R] Away.mk ℬ hb n y hy := by
  apply (segreEquiv ha hb).injective
  rw [AlgEquiv.apply_symm_apply, segreEquiv_apply, segreHom_tmul_mk_same]

end TensorEquiv

end General

/-! ### Compatibility with `Away.isLocalizationElem` for `ℕ`-gradings -/

section NatGrading

variable {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- On an `ℕ`-graded Segre chart `D₊(a ⊗ₜ b)` (`a ∈ 𝒜 d`, `b ∈ ℬ d`), the product of the images of
`Away.isLocalizationElem` for `a' ∈ 𝒜 e` and `b' ∈ ℬ e` is `Away.isLocalizationElem` for
`a' ⊗ₜ b'`. -/
theorem segreFst_isLocalizationElem_mul_segreSnd_isLocalizationElem
    {d e : ℕ} {a a' : A} {b b' : B}
    (ha : a ∈ 𝒜 d) (hb : b ∈ ℬ d) (ha' : a' ∈ 𝒜 e) (hb' : b' ∈ ℬ e) :
    segreFst ha hb (isLocalizationElem ha ha') *
      segreSnd ha hb (isLocalizationElem hb hb') =
    isLocalizationElem (Segre.tmul_mem_grading ha hb)
      (Segre.tmul_mem_grading ha' hb') := by
  apply segreValAlgHom_injective ha hb
  rw [map_mul, isLocalizationElem, isLocalizationElem, isLocalizationElem,
    segreFst_mk, segreSnd_mk, segreValAlgHom_mk, segreValAlgHom_mk,
    segreValAlgHom_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, map_pow,
    Segre.toTensorProduct_tmul, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul]
  congr 1 <;> ring

end NatGrading

end HomogeneousLocalization.Away
