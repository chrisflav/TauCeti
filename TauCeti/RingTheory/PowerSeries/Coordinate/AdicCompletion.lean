/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Units
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic

/-!
# Formal coordinates over adic inverse limits

Let `I` be an ideal of a commutative ring `R`. A compatible system of formal coordinates over the
quotients `R ⧸ I ^ n` determines a unique formal coordinate over `AdicCompletion I R`, and if `R`
is `I`-adically complete, a unique formal coordinate over `R` itself. Because base change of formal
coordinates commutes with power series substitution, the compatible systems form a group under
levelwise composition and these comparisons are group isomorphisms
(`TauCeti.FormalCoordinateAdicSystem.completionEquiv` and
`TauCeti.FormalCoordinateAdicSystem.completeEquiv`).

Unlike formal group laws, formal coordinates are assembled directly coefficientwise via
`AdicCompletion.liftElem`, using `AdicCompletion.isUnit_iff_forall_evalₐ` to invert the linear
coefficient in the completion. No finite-generation, Noetherian, or local-ring assumption on
`(R, I)` is required.

Together with rigidity of homomorphisms of finite-height formal group laws, this coordinate
inverse-limit isomorphism passes from compatible Artinian-level coordinates to a single coordinate
change over the completion when comparing orbit sets of formal group deformations.

## Main definitions and results

* `TauCeti.FormalCoordinate.ext_adicCompletion` and `TauCeti.FormalCoordinate.ext_adic`: formal
  coordinates over an adic completion or an adically Hausdorff ring are determined by their
  quotient reductions.
* `TauCeti.FormalCoordinateAdicSystem I`: the group of compatible families of formal coordinates
  over `R ⧸ I ^ n`, with `TauCeti.FormalCoordinateAdicSystem.ofSucc` for families indexed by
  `R ⧸ I ^ (n + 1)`.
* `TauCeti.FormalCoordinateAdicSystem.completionEquiv`: the group isomorphism
  `FormalCoordinate (AdicCompletion I R) ≃* FormalCoordinateAdicSystem I`.
* `TauCeti.FormalCoordinateAdicSystem.map` and `TauCeti.FormalCoordinateAdicSystem.limit_map`:
  functorial base change of coordinate systems and compatibility with inverse limits.
* `TauCeti.FormalCoordinateAdicSystem.completeEquiv`: for `I`-adically complete `R`, the group
  isomorphism `FormalCoordinate R ≃* FormalCoordinateAdicSystem I`.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*,
  Bull. Soc. Math. France 94 (1966).
-/

public section

noncomputable section

namespace TauCeti

namespace FormalCoordinate

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- Equality of formal coordinates over an adic completion can be tested on all coefficient
reductions. -/
theorem ext_adicCompletion {φ ψ : FormalCoordinate (AdicCompletion I R)}
    (h : ∀ n, map (AdicCompletion.evalₐ I n).toRingHom φ =
      map (AdicCompletion.evalₐ I n).toRingHom ψ) : φ = ψ := by
  apply FormalCoordinate.ext
  apply PowerSeries.ext
  intro k
  apply AdicCompletion.ext_evalₐ
  intro n
  have hk := congrArg (fun χ : FormalCoordinate (R ⧸ I ^ n) ↦
    PowerSeries.coeff k χ.toPowerSeries) (h n)
  simpa only [toPowerSeries_map, PowerSeries.coeff_map, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] using hk

/-- Formal coordinates over an adically Hausdorff ring are determined by all their reductions. -/
theorem ext_adic [IsHausdorff I R] {φ ψ : FormalCoordinate R}
    (h : ∀ n, map (Ideal.Quotient.mk (I ^ n)) φ = map (Ideal.Quotient.mk (I ^ n)) ψ) : φ = ψ := by
  apply FormalCoordinate.ext
  apply PowerSeries.ext
  intro k
  exact congrFun (IsHausdorff.funext' I
    (f := fun d ↦ PowerSeries.coeff d φ.toPowerSeries)
    (g := fun d ↦ PowerSeries.coeff d ψ.toPowerSeries) fun n d ↦ by
      simpa only [toPowerSeries_map, PowerSeries.coeff_map] using
        congrArg (fun χ : FormalCoordinate (R ⧸ I ^ n) ↦
          PowerSeries.coeff d χ.toPowerSeries) (h n)) k

end FormalCoordinate

section System

variable {R : Type*} [CommRing R]

/-- Formal coordinates over all the quotients `R ⧸ I ^ n`, compatible with coefficient
reduction. -/
structure FormalCoordinateAdicSystem (I : Ideal R) where
  /-- The formal coordinate at the indicated power of the ideal. -/
  coord (n : ℕ) : FormalCoordinate (R ⧸ I ^ n)
  /-- Reduction from a higher power gives the coordinate at a lower power. -/
  map_eq {m n : ℕ} (h : m ≤ n) :
    FormalCoordinate.map (Ideal.Quotient.factorPow I h) (coord n) = coord m

namespace FormalCoordinateAdicSystem

variable {I : Ideal R}

/-- A compatible system of formal coordinates is determined by its levelwise coordinates. -/
@[ext]
theorem ext {φ ψ : FormalCoordinateAdicSystem I} (h : ∀ n, φ.coord n = ψ.coord n) : φ = ψ := by
  cases φ
  cases ψ
  congr
  exact funext h

instance : One (FormalCoordinateAdicSystem I) where
  one :=
    { coord _ := 1
      map_eq _ := map_one _ }

instance : Mul (FormalCoordinateAdicSystem I) where
  mul φ ψ :=
    { coord n := φ.coord n * ψ.coord n
      map_eq h := by rw [map_mul, φ.map_eq h, ψ.map_eq h] }

instance : Inv (FormalCoordinateAdicSystem I) where
  inv φ :=
    { coord n := (φ.coord n)⁻¹
      map_eq h := by rw [map_inv, φ.map_eq h] }

/-- The identity coordinate system has coordinate `1` at every quotient level. -/
@[simp]
theorem coord_one (n : ℕ) : (1 : FormalCoordinateAdicSystem I).coord n = 1 := (rfl)

/-- Multiplication in `FormalCoordinateAdicSystem` acts levelwise on coordinates. -/
@[simp]
theorem coord_mul (φ ψ : FormalCoordinateAdicSystem I) (n : ℕ) :
    (φ * ψ).coord n = φ.coord n * ψ.coord n := (rfl)

/-- Inversion in `FormalCoordinateAdicSystem` acts levelwise on coordinates. -/
@[simp]
theorem coord_inv (φ : FormalCoordinateAdicSystem I) (n : ℕ) :
    φ⁻¹.coord n = (φ.coord n)⁻¹ := (rfl)

/-- Compatible systems of formal coordinates form a group under levelwise composition. -/
instance : Group (FormalCoordinateAdicSystem I) where
  mul_assoc φ ψ χ := ext fun n ↦ mul_assoc (φ.coord n) (ψ.coord n) (χ.coord n)
  one_mul φ := ext fun n ↦ one_mul (φ.coord n)
  mul_one φ := ext fun n ↦ mul_one (φ.coord n)
  inv_mul_cancel φ := ext fun n ↦ inv_mul_cancel (φ.coord n)

/-- Projection to the `n`-th quotient level as a group homomorphism. -/
def coordHom (I : Ideal R) (n : ℕ) :
    FormalCoordinateAdicSystem I →* FormalCoordinate (R ⧸ I ^ n) where
  toFun φ := φ.coord n
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `coordHom` evaluates a coordinate system at level `n`. -/
@[simp]
theorem coordHom_apply (I : Ideal R) (n : ℕ) (φ : FormalCoordinateAdicSystem I) :
    coordHom I n φ = φ.coord n := (rfl)

/-- Build a compatible system indexed by all `n : ℕ` from a compatible family indexed by positive
exponents `n + 1`, projecting `R ⧸ I ^ (n + 1)` to `R ⧸ I ^ n` at index `n`. -/
def ofSucc (c : ∀ n : ℕ, FormalCoordinate (R ⧸ I ^ (n + 1)))
    (hc : ∀ {m n : ℕ} (h : m ≤ n),
      FormalCoordinate.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ h)) (c n) = c m) :
    FormalCoordinateAdicSystem I where
  coord k := FormalCoordinate.map (Ideal.Quotient.factorPow I k.le_succ) (c k)
  map_eq {k l} h := by
    have hcomp : (Ideal.Quotient.factorPow I h).comp (Ideal.Quotient.factorPow I l.le_succ) =
        (Ideal.Quotient.factorPow I k.le_succ).comp
          (Ideal.Quotient.factorPow I (Nat.succ_le_succ h)) := by
      apply Ideal.Quotient.ringHom_ext
      ext x
      rfl
    rw [← FormalCoordinate.map_comp, hcomp, FormalCoordinate.map_comp, hc h]

/-- Evaluating `ofSucc` at `n + 1` recovers the input coordinate at index `n`. -/
@[simp]
theorem coord_succ_ofSucc (c : ∀ n : ℕ, FormalCoordinate (R ⧸ I ^ (n + 1)))
    (hc : ∀ {m n : ℕ} (h : m ≤ n),
      FormalCoordinate.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ h)) (c n) = c m)
    (n : ℕ) :
    (ofSucc c hc).coord (n + 1) = c n :=
  hc n.le_succ

/-- Reduce a formal coordinate over the adic completion at every power of the ideal, as a group
homomorphism. -/
def ofCompletion (I : Ideal R) :
    FormalCoordinate (AdicCompletion I R) →* FormalCoordinateAdicSystem I where
  toFun φ :=
    { coord n := FormalCoordinate.map (AdicCompletion.evalₐ I n).toRingHom φ
      map_eq h := by
        rw [← FormalCoordinate.map_comp]
        exact congrArg (fun g ↦ FormalCoordinate.map g φ)
          (RingHom.ext fun x ↦ AdicCompletion.factor_evalₐ h x) }
  map_one' := ext fun _ ↦ map_one _
  map_mul' _ _ := ext fun _ ↦ map_mul _ _ _

/-- The coordinate at level `n` is coefficient reduction from the completion. -/
@[simp]
theorem coord_ofCompletion (I : Ideal R) (φ : FormalCoordinate (AdicCompletion I R)) (n : ℕ) :
    (ofCompletion I φ).coord n = FormalCoordinate.map (AdicCompletion.evalₐ I n).toRingHom φ :=
  (rfl)

private theorem coeff_compatible (φ : FormalCoordinateAdicSystem I) (k : ℕ) {m n : ℕ}
    (h : m ≤ n) :
    Ideal.Quotient.factorPow I h (PowerSeries.coeff k (φ.coord n).toPowerSeries) =
      PowerSeries.coeff k (φ.coord m).toPowerSeries := by
  simpa only [FormalCoordinate.toPowerSeries_map, PowerSeries.coeff_map] using
    congrArg (fun ψ ↦ PowerSeries.coeff k ψ.toPowerSeries) (φ.map_eq h)

/-- The formal coordinate over the adic completion realizing a compatible system. -/
def limit (φ : FormalCoordinateAdicSystem I) : FormalCoordinate (AdicCompletion I R) where
  toPowerSeries := PowerSeries.mk fun k ↦
    AdicCompletion.liftElem I (fun n ↦ PowerSeries.coeff k (φ.coord n).toPowerSeries)
      (φ.coeff_compatible k)
  constantCoeff_toPowerSeries := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    refine AdicCompletion.ext_evalₐ fun n ↦ ?_
    rw [AdicCompletion.evalₐ_liftElem, map_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      (φ.coord n).constantCoeff_toPowerSeries]
  isUnit_coeff_one := by
    rw [PowerSeries.coeff_mk, AdicCompletion.isUnit_iff_forall_evalₐ]
    intro n
    rw [AdicCompletion.evalₐ_liftElem]
    exact (φ.coord n).isUnit_coeff_one

/-- The inverse-limit coordinate has the prescribed reduction at every power of `I`. -/
@[simp]
theorem map_limit (φ : FormalCoordinateAdicSystem I) (n : ℕ) :
    FormalCoordinate.map (AdicCompletion.evalₐ I n) φ.limit = φ.coord n := by
  apply FormalCoordinate.ext
  apply PowerSeries.ext
  intro k
  simp [limit]

/-- Reducing the inverse-limit coordinate recovers the original system. -/
@[simp]
theorem ofCompletion_limit (φ : FormalCoordinateAdicSystem I) :
    ofCompletion I φ.limit = φ :=
  ext fun n ↦ by simpa only [coord_ofCompletion, AlgHom.toRingHom_eq_coe] using φ.map_limit n

/-- Taking the inverse limit of the reductions of a coordinate over the completion recovers it. -/
@[simp]
theorem limit_ofCompletion (φ : FormalCoordinate (AdicCompletion I R)) :
    (ofCompletion I φ).limit = φ :=
  FormalCoordinate.ext_adicCompletion fun n ↦ by
    simpa only [coord_ofCompletion, AlgHom.toRingHom_eq_coe] using (ofCompletion I φ).map_limit n

/-- Formal coordinates over the adic completion are isomorphic as a group to compatible systems
of formal coordinates over the quotient rings. -/
def completionEquiv (I : Ideal R) :
    FormalCoordinate (AdicCompletion I R) ≃* FormalCoordinateAdicSystem I where
  toFun := ofCompletion I
  invFun := limit
  left_inv := limit_ofCompletion
  right_inv := ofCompletion_limit
  map_mul' := (ofCompletion I).map_mul'

/-- The group isomorphism to systems reduces coefficients at each power. -/
@[simp]
theorem coord_completionEquiv (I : Ideal R) (φ : FormalCoordinate (AdicCompletion I R)) (n : ℕ) :
    (completionEquiv I φ).coord n =
      FormalCoordinate.map (AdicCompletion.evalₐ I n).toRingHom φ := (rfl)

/-- The inverse of `completionEquiv` is `limit`. -/
@[simp]
theorem completionEquiv_symm_apply (φ : FormalCoordinateAdicSystem I) :
    (completionEquiv I).symm φ = φ.limit := (rfl)

section BaseChange

variable {S T : Type*} [CommRing S] [CommRing T] {J : Ideal S} {K : Ideal T}

/-- Extend coefficients in a system of formal coordinates along a ring homomorphism carrying `I`
into `J`. -/
def map (f : R →+* S) (hf : I ≤ J.comap f) :
    FormalCoordinateAdicSystem I →* FormalCoordinateAdicSystem J where
  toFun φ :=
    { coord n := FormalCoordinate.map
        (Ideal.quotientMap (J ^ n) f ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n)))
        (φ.coord n)
      map_eq h := by
        rw [← FormalCoordinate.map_comp, ← φ.map_eq h, ← FormalCoordinate.map_comp]
        exact congrArg (fun g ↦ FormalCoordinate.map g _)
          (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by simp)) }
  map_one' := ext fun _ ↦ map_one _
  map_mul' _ _ := ext fun _ ↦ map_mul _ _ _

/-- Base change of a coordinate system acts levelwise on coefficients. -/
@[simp]
theorem coord_map (f : R →+* S) (hf : I ≤ J.comap f) (φ : FormalCoordinateAdicSystem I) (n : ℕ) :
    (map f hf φ).coord n = FormalCoordinate.map
      (Ideal.quotientMap (J ^ n) f ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n)))
      (φ.coord n) := (rfl)

/-- Extending coefficients by the identity does not change a coordinate system. -/
@[simp]
theorem map_id (φ : FormalCoordinateAdicSystem I) :
    map (RingHom.id R) (J := I) (by simp) φ = φ := by
  apply ext
  intro n
  rw [coord_map]
  have h : Ideal.quotientMap (I ^ n) (RingHom.id R) (by simp) = RingHom.id (R ⧸ I ^ n) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by simp)
  rw [h, FormalCoordinate.map_id, MonoidHom.id_apply]

/-- Successive coefficient extensions of coordinate systems agree with their composite. -/
@[simp]
theorem map_comp (f : R →+* S) (hf : I ≤ J.comap f) (g : S →+* T) (hg : J ≤ K.comap g)
    (φ : FormalCoordinateAdicSystem I) :
    map g hg (map f hf φ) = map (g.comp f) (hf.trans (Ideal.comap_mono hg)) φ := by
  apply ext
  intro n
  simp only [coord_map, ← FormalCoordinate.map_comp]
  exact congrArg (fun q ↦ FormalCoordinate.map q (φ.coord n))
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ by simp))

/-- Taking inverse limits of formal coordinates commutes with coefficient extension to adic
completions. -/
theorem limit_map (f : R →+* S) (hf : I ≤ J.comap f) (φ : FormalCoordinateAdicSystem I) :
    (map f hf φ).limit = FormalCoordinate.map
      (AdicCompletion.mapₐ f.toIntAlgHom
        (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hf)).toRingHom φ.limit := by
  apply FormalCoordinate.ext_adicCompletion
  intro n
  simp only [AlgHom.toRingHom_eq_coe]
  rw [map_limit, coord_map, ← FormalCoordinate.map_comp]
  have h : (AdicCompletion.evalₐ J n).toRingHom.comp
      (AdicCompletion.mapₐ f.toIntAlgHom
        (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hf)).toRingHom =
      (Ideal.quotientMap (J ^ n) f
        ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n))).comp
        (AdicCompletion.evalₐ I n).toRingHom := by
    ext x
    exact AdicCompletion.evalₐ_mapₐ f.toIntAlgHom
      (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hf) n x
  simp only [AlgHom.toRingHom_eq_coe] at h
  rw [h, FormalCoordinate.map_comp, map_limit]

end BaseChange

section Complete

variable [IsAdicComplete I R]

/-- Realize a compatible system of formal coordinates over an adically complete ring itself. -/
def realize (φ : FormalCoordinateAdicSystem I) : FormalCoordinate R :=
  FormalCoordinate.map (AdicCompletion.ofAlgEquiv I).symm.toRingHom φ.limit

/-- Reduction of the realized coordinate gives the specified quotient coordinate. -/
@[simp]
theorem map_realize (φ : FormalCoordinateAdicSystem I) (n : ℕ) :
    FormalCoordinate.map (Ideal.Quotient.mk (I ^ n)) φ.realize = φ.coord n := by
  rw [realize, ← FormalCoordinate.map_comp]
  have h : (Ideal.Quotient.mk (I ^ n)).comp (AdicCompletion.ofAlgEquiv I).symm.toRingHom =
      AdicCompletion.evalₐ I n :=
    RingHom.ext fun x ↦ AdicCompletion.mk_ofAlgEquiv_symm I n x
  rw [h, φ.map_limit]

/-- Realization of coordinate systems over complete rings commutes with coefficient extension. -/
theorem realize_map {S : Type*} [CommRing S] {J : Ideal S} [IsAdicComplete J S]
    (f : R →+* S) (hf : I ≤ J.comap f) (φ : FormalCoordinateAdicSystem I) :
    (map f hf φ).realize = FormalCoordinate.map f φ.realize := by
  apply FormalCoordinate.ext_adic (I := J)
  intro n
  rw [map_realize, coord_map, ← FormalCoordinate.map_comp,
    ← Ideal.quotientMap_comp_mk ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n)),
    FormalCoordinate.map_comp, map_realize]

/-- Over an adically complete ring, compatible quotient coordinates have a unique realization. -/
theorem existsUnique_realization (φ : FormalCoordinateAdicSystem I) :
    ∃! ψ : FormalCoordinate R,
      ∀ n, FormalCoordinate.map (Ideal.Quotient.mk (I ^ n)) ψ = φ.coord n := by
  refine ⟨φ.realize, φ.map_realize, fun ψ hψ ↦ FormalCoordinate.ext_adic (I := I) fun n ↦ ?_⟩
  rw [hψ n, φ.map_realize]

/-- Over an adically complete ring, formal coordinates are isomorphic as a group to compatible
systems of quotient formal coordinates. -/
def completeEquiv (I : Ideal R) [IsAdicComplete I R] :
    FormalCoordinate R ≃* FormalCoordinateAdicSystem I where
  toFun := (ofCompletion I).comp (FormalCoordinate.map (algebraMap R (AdicCompletion I R)))
  invFun := realize
  left_inv φ := FormalCoordinate.ext_adic (I := I) fun n ↦ by
    rw [map_realize, MonoidHom.comp_apply, coord_ofCompletion, ← FormalCoordinate.map_comp]
    exact congrArg (fun g ↦ FormalCoordinate.map g φ)
      (RingHom.ext fun x ↦ AdicCompletion.evalₐ_of I n x)
  right_inv φ := ext fun n ↦ by
    rw [MonoidHom.comp_apply, coord_ofCompletion, ← FormalCoordinate.map_comp]
    have h : (AdicCompletion.evalₐ I n).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
        Ideal.Quotient.mk (I ^ n) := RingHom.ext fun x ↦ AdicCompletion.evalₐ_of I n x
    rw [h, map_realize]
  map_mul' :=
    ((ofCompletion I).comp (FormalCoordinate.map (algebraMap R (AdicCompletion I R)))).map_mul'

/-- The complete-ring isomorphism sends a coordinate to its coefficient reductions. -/
@[simp]
theorem coord_completeEquiv (I : Ideal R) [IsAdicComplete I R] (φ : FormalCoordinate R) (n : ℕ) :
    (completeEquiv I φ).coord n = FormalCoordinate.map (Ideal.Quotient.mk (I ^ n)) φ := by
  simp only [completeEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, MonoidHom.comp_apply,
    coord_ofCompletion, ← FormalCoordinate.map_comp]
  exact congrArg (fun g ↦ FormalCoordinate.map g φ)
    (RingHom.ext fun x ↦ AdicCompletion.evalₐ_of I n x)

/-- The inverse complete-ring isomorphism realizes the compatible system. -/
@[simp]
theorem completeEquiv_symm_apply (φ : FormalCoordinateAdicSystem I) :
    (completeEquiv I).symm φ = φ.realize := (rfl)

end Complete

end FormalCoordinateAdicSystem

end System

end TauCeti
