/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.ReesAlgebra.Extended.Basic
public import TauCeti.RingTheory.ReesAlgebra.Grading

/-!
# The `ℤ`-grading of the extended Rees algebra

For an ideal `I` of a commutative semiring `R`, the extended Rees algebra
`Ideal.extendedReesAlgebra I = R[It, t⁻¹]` inside `R[T;T⁻¹]` is graded over `ℤ` by the exponent
of `T`: its degree-`d` submodule `Ideal.extendedReesAlgebra.grade I d` consists of the Laurent
monomials `C r * T d` with `r ∈ I.zFiltration (-d)`. In particular:

* for `n : ℕ`, `grade I n` is isomorphic to `I ^ n` via `r ↦ C r * T n`;
* for `d ≤ 0`, `grade I d` is isomorphic to `R` via `r ↦ C r * T d`;
* `invT I = T (-1)` is homogeneous of degree `-1`, and `monomialDegreeOne ha = C a * T 1` is
  homogeneous of degree `1`.

Over a commutative ring `R`, the inclusion `reesAlgebra.toExtended I` identifies
`reesAlgebra.grade I n` with `Ideal.extendedReesAlgebra.grade I (n : ℤ)` for every `n : ℕ`, and the
nonnegative graded part `⨆ n : ℕ, grade I (n : ℤ)` equals the image of Mathlib's `reesAlgebra I`.

## Main definitions

* `Ideal.extendedReesAlgebra.grade I d`: the degree-`d` `R`-submodule of `I.extendedReesAlgebra`.
* `Ideal.extendedReesAlgebra.gradedAlgebra`: the `GradedAlgebra (grade I)` instance.
* `Ideal.extendedReesAlgebra.gradeEquiv I d`: the `R`-linear equivalence
  `↥(I.zFiltration (-d)) ≃ₗ[R] grade I d`.
* `Ideal.extendedReesAlgebra.gradeZeroEquiv I`: the ring isomorphism `R ≃+* grade I 0`.
* `Ideal.extendedReesAlgebra.mapGradedRingHom f h`: functoriality as a `ℤ`-graded ring homomorphism.
* `reesAlgebra.toExtendedGradeEquiv I n`: the `R`-linear equivalence
  `reesAlgebra.grade I n ≃ₗ[R] Ideal.extendedReesAlgebra.grade I (n : ℤ)`.

## Main results

* `Ideal.extendedReesAlgebra.isInternal_grade`: `I.extendedReesAlgebra` is the internal direct sum
  of `grade I`.
* `Ideal.extendedReesAlgebra.coe_decompose_apply`: the degree-`d` component of `f` is
  `C (f.coeff d) * T d`.
* `reesAlgebra.toExtended_mem_grade`: `reesAlgebra.toExtended I` preserves and reflects nonnegative
  degrees.
* `reesAlgebra.range_toExtended_toSubmodule_eq_iSup_grade`: the nonnegative graded part
  `⨆ n : ℕ, grade I (n : ℤ)` equals the image of `reesAlgebra I`.
-/

public section

open DirectSum LaurentPolynomial

namespace Ideal.extendedReesAlgebra

section Semiring

variable {R : Type*} [CommSemiring R] (I : Ideal R)

/-- The degree-`d` homogeneous piece of `I.extendedReesAlgebra`: the Laurent monomials `C r * T d`
with `r ∈ I.zFiltration (-d)`. -/
noncomputable def grade (d : ℤ) : Submodule R I.extendedReesAlgebra :=
  Submodule.comap I.extendedReesAlgebra.val.toLinearMap
    (Submodule.map (AddMonoidAlgebra.lsingle d) (I.zFiltration (-d)))

variable {I}

/-- An element of `I.extendedReesAlgebra` lies in `grade I d` iff it is a Laurent monomial
`C r * T d` with `r ∈ I.zFiltration (-d)`. -/
theorem mem_grade_iff {d : ℤ} {f : I.extendedReesAlgebra} :
    f ∈ grade I d ↔ ∃ r ∈ I.zFiltration (-d), C r * T d = (f : R[T;T⁻¹]) := by
  simp only [grade, Submodule.mem_comap, AlgHom.toLinearMap_apply, Subalgebra.coe_val,
    Submodule.mem_map, AddMonoidAlgebra.lsingle_apply, single_eq_C_mul_T]

/-- An element of `I.extendedReesAlgebra` has degree `d` iff it equals the single Laurent monomial
formed from its `d`-th coefficient. -/
theorem mem_grade_iff_C_mul_T_coeff {d : ℤ} {f : I.extendedReesAlgebra} :
    f ∈ grade I d ↔ C ((f : R[T;T⁻¹]).coeff d) * T d = (f : R[T;T⁻¹]) := by
  refine ⟨fun hf ↦ ?_, fun h ↦
    mem_grade_iff.mpr ⟨_, Ideal.mem_extendedReesAlgebra_iff_zFiltration.mp f.2 d, h⟩⟩
  obtain ⟨r, -, hr⟩ := mem_grade_iff.mp hf
  have hc : (f : R[T;T⁻¹]).coeff d = r := by
    rw [← hr, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  rwa [hc]

/-- The Laurent monomial `monomial I d r hr` is homogeneous of degree `d`. -/
theorem monomial_mem_grade (d : ℤ) (r : R) (hr : r ∈ I.zFiltration (-d)) :
    monomial I d r hr ∈ grade I d :=
  mem_grade_iff.mpr ⟨r, hr, (coe_monomial I d r hr).symm⟩

variable (I) in
/-- The inverse parameter `invT I = T (-1)` is homogeneous of degree `-1`. -/
theorem invT_mem_grade : invT I ∈ grade I (-1) :=
  mem_grade_iff.mpr ⟨1, by simp, by simp [coe_invT]⟩

/-- The degree-one generator `monomialDegreeOne ha = C a * T 1` is homogeneous of degree `1`. -/
theorem monomialDegreeOne_mem_grade {a : R} (ha : a ∈ I) : monomialDegreeOne ha ∈ grade I 1 :=
  mem_grade_iff.mpr ⟨a, by simpa using ha, (coe_monomialDegreeOne ha).symm⟩

/-- Coefficients of a degree-`d` element vanish outside degree `d`. -/
theorem coeff_eq_zero_of_mem_grade {m d : ℤ} {f : I.extendedReesAlgebra} (hf : f ∈ grade I d)
    (hmd : m ≠ d) : (f : R[T;T⁻¹]).coeff m = 0 := by
  rw [← mem_grade_iff_C_mul_T_coeff.mp hf, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  split_ifs with h
  · exact absurd h.symm hmd
  · rfl

/-- A degree-`d` element vanishes iff its `d`-th coefficient vanishes. -/
theorem coeff_eq_zero_iff_of_mem_grade {d : ℤ} {f : I.extendedReesAlgebra} (hf : f ∈ grade I d) :
    (f : R[T;T⁻¹]).coeff d = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ Subtype.ext ?_, fun h ↦ by simp [h]⟩
  rw [← mem_grade_iff_C_mul_T_coeff.mp hf, h, map_zero, zero_mul, ZeroMemClass.coe_zero]

/-- Multiplication in `I.extendedReesAlgebra` respects the `ℤ`-grading `grade I`. -/
instance gradedMonoid : SetLike.GradedMonoid (grade I) where
  one_mem := mem_grade_iff.mpr ⟨1, by simp, by simp⟩
  mul_mem d₁ d₂ f g hf hg := by
    obtain ⟨r, hr, hrf⟩ := mem_grade_iff.mp hf
    obtain ⟨s, hs, hsg⟩ := mem_grade_iff.mp hg
    refine mem_grade_iff.mpr ⟨r * s, ?_, ?_⟩
    · rw [neg_add]
      exact SetLike.mul_mem_graded hr hs
    · rw [Subalgebra.coe_mul, ← hrf, ← hsg, T_add, map_mul]
      ring

private noncomputable def component (d : ℤ) (f : I.extendedReesAlgebra) : grade I d :=
  ⟨monomial I d ((f : R[T;T⁻¹]).coeff d)
    (Ideal.mem_extendedReesAlgebra_iff_zFiltration.mp f.2 d),
    monomial_mem_grade d _ _⟩

private theorem coe_component (d : ℤ) (f : I.extendedReesAlgebra) :
    ((component d f : I.extendedReesAlgebra) : R[T;T⁻¹]) = C ((f : R[T;T⁻¹]).coeff d) * T d :=
  coe_monomial I d _ _

private theorem component_add (d : ℤ) (f g : I.extendedReesAlgebra) :
    component d (f + g) = component d f + component d g := by
  ext1; ext1
  simp [coe_component, add_mul]

private theorem component_of_mem {m d : ℤ} {f : I.extendedReesAlgebra} (hf : f ∈ grade I m) :
    component d f = if h : m = d then h ▸ ⟨f, hf⟩ else 0 := by
  split_ifs with h
  · subst h
    exact Subtype.ext (Subtype.ext ((coe_component m f).trans (mem_grade_iff_C_mul_T_coeff.mp hf)))
  · ext1; ext1
    simp [coe_component, coeff_eq_zero_of_mem_grade hf (Ne.symm h)]

private noncomputable def decomposeAux (f : I.extendedReesAlgebra) : ⨁ d : ℤ, grade I d :=
  ∑ d ∈ (f : R[T;T⁻¹]).coeff.support, of (fun d ↦ grade I d) d (component d f)

private theorem decomposeAux_apply (f : I.extendedReesAlgebra) (d : ℤ) :
    decomposeAux f d = component d f := by
  rw [decomposeAux, DFinsupp.finsetSum_apply]
  simp_rw [of_apply]
  rw [Finset.sum_dite_eq']
  split_ifs with h
  · rfl
  · ext1; ext1
    simp [coe_component, Finsupp.notMem_support_iff.mp h]

private theorem coe_decomposeAux (f : I.extendedReesAlgebra) :
    DirectSum.coeAddMonoidHom (fun d ↦ grade I d) (decomposeAux f) = f := by
  rw [decomposeAux, map_sum]
  simp_rw [coeAddMonoidHom_of]
  exact (as_sum_support f).symm

private theorem decomposeAux_coe (x : ⨁ d : ℤ, grade I d) :
    decomposeAux (DirectSum.coeAddMonoidHom (fun d ↦ grade I d) x) = x := by
  ext d : 1
  rw [decomposeAux_apply]
  induction x using DirectSum.induction_on with
  | zero => ext1; ext1; simp [coe_component]
  | of m y => rw [coeAddMonoidHom_of, component_of_mem y.2, of_apply]
  | add x y hx hy => rw [map_add, component_add, hx, hy, DirectSum.add_apply]

variable (I) in
/-- `I.extendedReesAlgebra` is the internal direct sum of its `ℤ`-graded pieces. -/
theorem isInternal_grade : IsInternal (grade I) :=
  Function.bijective_iff_has_inverse.mpr ⟨decomposeAux, decomposeAux_coe, coe_decomposeAux⟩

/-- The `ℤ`-grading of `I.extendedReesAlgebra` by the Laurent exponent. -/
noncomputable instance gradedAlgebra : GradedAlgebra (grade I) :=
  (isInternal_grade I).gradedAlgebra

/-- The degree-`d` homogeneous component of `f ∈ I.extendedReesAlgebra` is `C (f.coeff d) * T d`. -/
@[simp]
theorem coe_decompose_apply (f : I.extendedReesAlgebra) (d : ℤ) :
    ((decompose (grade I) f d : I.extendedReesAlgebra) : R[T;T⁻¹]) =
      C ((f : R[T;T⁻¹]).coeff d) * T d := by
  have h : decompose (grade I) f = decomposeAux f :=
    (isInternal_grade I).1 <| by
      rw [coe_decomposeAux]
      exact (decompose (grade I)).symm_apply_apply f
  rw [h, decomposeAux_apply, coe_component]

variable (I)

/-- The `R`-linear isomorphism `r ↦ C r * T d` between `I.zFiltration (-d)` and `grade I d`. -/
noncomputable def gradeEquiv (d : ℤ) : ↥(I.zFiltration (-d)) ≃ₗ[R] grade I d where
  toFun r := ⟨monomial I d r.1 r.2, monomial_mem_grade d r.1 r.2⟩
  invFun f := ⟨((f : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff d,
    Ideal.mem_extendedReesAlgebra_iff_zFiltration.mp (f : I.extendedReesAlgebra).2 d⟩
  map_add' r s := by ext1; ext1; simp [coe_monomial, add_mul]
  map_smul' c r := by ext1; ext1; simp [coe_monomial, smul_eq_mul, ← smul_eq_C_mul]
  left_inv r := by
    ext1
    simp only [coe_monomial, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same]
  right_inv f := by
    ext1; ext1
    exact (coe_monomial I d _ _).trans (mem_grade_iff_C_mul_T_coeff.mp f.2)

@[simp]
theorem coe_gradeEquiv_apply (d : ℤ) (r : ↥(I.zFiltration (-d))) :
    ((gradeEquiv I d r : I.extendedReesAlgebra) : R[T;T⁻¹]) = C (r : R) * T d :=
  coe_monomial I d r.1 r.2

@[simp]
theorem coe_gradeEquiv_symm_apply (d : ℤ) (f : grade I d) :
    ((gradeEquiv I d).symm f : R) = ((f : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff d :=
  (rfl)

/-- The degree-zero piece of `I.extendedReesAlgebra` is isomorphic to the base semiring `R`. -/
noncomputable def gradeZeroEquiv : R ≃+* grade I 0 :=
  RingEquiv.ofBijective (algebraMap R (grade I 0)) <| by
    refine ⟨fun r s h ↦ ?_, fun f ↦ ?_⟩
    · have hc := congr_arg
        (fun x : grade I 0 ↦ ((x : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff 0) h
      simpa only [SetLike.GradeZero.coe_algebraMap, Subalgebra.coe_algebraMap,
        LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        ← single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using hc
    · obtain ⟨r, -, hr⟩ := mem_grade_iff.mp f.2
      refine ⟨r, Subtype.ext (Subtype.ext ?_)⟩
      rw [← hr, T_zero, mul_one, SetLike.GradeZero.coe_algebraMap, Subalgebra.coe_algebraMap,
        LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem gradeZeroEquiv_apply (r : R) : gradeZeroEquiv I r = algebraMap R (grade I 0) r :=
  RingEquiv.ofBijective_apply _ _ r

@[simp]
theorem coe_gradeZeroEquiv (r : R) :
    ((gradeZeroEquiv I r : I.extendedReesAlgebra) : R[T;T⁻¹]) = C r := by
  rw [gradeZeroEquiv_apply, SetLike.GradeZero.coe_algebraMap, Subalgebra.coe_algebraMap,
    LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

@[simp]
theorem gradeZeroEquiv_symm_apply (f : grade I 0) :
    (gradeZeroEquiv I).symm f = ((f : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff 0 := by
  rw [RingEquiv.symm_apply_eq]
  obtain ⟨r, -, hr⟩ := mem_grade_iff.mp f.2
  ext1; ext1
  have hc : ((f : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff 0 = r := by
    rw [← hr, T_zero, mul_one, ← single_eq_C, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same]
  rw [coe_gradeZeroEquiv, hc, ← hr, T_zero, mul_one]

variable {I} in
/-- Functoriality `map f h` preserves the `ℤ`-grading of the extended Rees algebra. -/
theorem map_mem_grade {S : Type*} [CommSemiring S] {J : Ideal S} (f : R →+* S)
    (h : I ≤ J.comap f) {d : ℤ} {x : I.extendedReesAlgebra} (hx : x ∈ grade I d) :
    map f h x ∈ grade J d := by
  obtain ⟨r, hr, hrx⟩ := mem_grade_iff.mp hx
  have hx' : x = monomial I d r hr := Subtype.ext (hrx.symm.trans (coe_monomial I d r hr).symm)
  rw [hx', map_monomial]
  exact monomial_mem_grade d _ _

variable {I} in
/-- `Ideal.extendedReesAlgebra.map` packaged as a `ℤ`-graded ring homomorphism. -/
noncomputable def mapGradedRingHom {S : Type*} [CommSemiring S] {J : Ideal S} (f : R →+* S)
    (h : I ≤ J.comap f) : grade I →+*ᵍ grade J where
  __ := map f h
  map_mem := map_mem_grade f h

variable {I} in
@[simp]
theorem mapGradedRingHom_apply {S : Type*} [CommSemiring S] {J : Ideal S} (f : R →+* S)
    (h : I ≤ J.comap f) (x : I.extendedReesAlgebra) :
    mapGradedRingHom f h x = map f h x :=
  (rfl)

variable {I} in
/-- An element of `I.extendedReesAlgebra` lies in the nonnegative graded part
`⨆ n : ℕ, grade I (n : ℤ)` precisely when all of its strictly negative Laurent coefficients
vanish. -/
theorem mem_iSup_grade_natCast_iff {f : I.extendedReesAlgebra} :
    f ∈ (⨆ n : ℕ, grade I (n : ℤ)) ↔ ∀ d < 0, (f : R[T;T⁻¹]).coeff d = 0 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · refine Submodule.iSup_induction (fun n : ℕ ↦ grade I (n : ℤ))
      (motive := fun g ↦ ∀ d < 0, (g : R[T;T⁻¹]).coeff d = 0) hf (fun n g hg d hd ↦ ?_)
      (by simp) (fun g₁ g₂ hg₁ hg₂ d hd ↦ by simp [hg₁ d hd, hg₂ d hd])
    exact coeff_eq_zero_of_mem_grade hg (by omega)
  · rw [as_sum_support f]
    refine Submodule.sum_mem _ fun d hd ↦ ?_
    have hnn : 0 ≤ d := not_lt.mp fun hlt ↦ Finsupp.mem_support_iff.mp hd (hf d hlt)
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = d := ⟨d.toNat, Int.toNat_of_nonneg hnn⟩
    exact Submodule.mem_iSup_of_mem n (monomial_mem_grade _ _ _)

end Semiring

end Ideal.extendedReesAlgebra

/-! ### Comparison with `reesAlgebra.grade` and the nonnegative graded part -/

section CommRing

variable {R : Type*} [CommRing R] (I : Ideal R)

variable {I} in
@[simp]
theorem reesAlgebra.toExtended_monomialDegreeOne {a : R} (ha : a ∈ I) :
    reesAlgebra.toExtended I (reesAlgebra.monomialDegreeOne ha) =
      Ideal.extendedReesAlgebra.monomialDegreeOne ha := by
  apply Subtype.ext
  rw [reesAlgebra.coe_toExtended, reesAlgebra.coe_monomialDegreeOne,
    Polynomial.toLaurent_C_mul_T, Nat.cast_one, Ideal.extendedReesAlgebra.coe_monomialDegreeOne]

variable {I} in
/-- `reesAlgebra.toExtended` preserves and reflects membership in nonnegative degrees. -/
@[simp]
theorem reesAlgebra.toExtended_mem_grade {n : ℕ} {f : reesAlgebra I} :
    reesAlgebra.toExtended I f ∈ Ideal.extendedReesAlgebra.grade I (n : ℤ) ↔
      f ∈ reesAlgebra.grade I n := by
  rw [Ideal.extendedReesAlgebra.mem_grade_iff, reesAlgebra.mem_grade_iff]
  simp only [Ideal.zFiltration_neg_natCast, reesAlgebra.coe_toExtended,
    ← Polynomial.toLaurent_C_mul_T, Polynomial.toLaurent_inj]

/-- The degree-`n` graded piece of Mathlib's `reesAlgebra I` is `R`-linearly isomorphic to the
degree-`(n : ℤ)` piece of `I.extendedReesAlgebra`. -/
noncomputable def reesAlgebra.toExtendedGradeEquiv (n : ℕ) :
    reesAlgebra.grade I n ≃ₗ[R] Ideal.extendedReesAlgebra.grade I (n : ℤ) :=
  LinearEquiv.ofBijective
    (((reesAlgebra.toExtended I).toLinearMap.domRestrict (reesAlgebra.grade I n)).codRestrict
      (Ideal.extendedReesAlgebra.grade I (n : ℤ)) fun x ↦
        reesAlgebra.toExtended_mem_grade.mpr x.2)
    ⟨fun _ _ hxy ↦ Subtype.ext <| reesAlgebra.toExtended_injective I (congr_arg Subtype.val hxy),
      fun y ↦ by
        obtain ⟨r, hr, hry⟩ := Ideal.extendedReesAlgebra.mem_grade_iff.mp y.2
        have hrn : r ∈ I ^ n := by simpa using hr
        exact ⟨⟨⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hrn⟩,
          reesAlgebra.monomial_mem_grade hrn⟩,
          Subtype.ext (Subtype.ext
            ((reesAlgebra.coe_toExtended _).trans ((Polynomial.toLaurent_C_mul_T n r).trans hry)))⟩⟩

variable {I} in
@[simp]
theorem reesAlgebra.coe_toExtendedGradeEquiv_apply (n : ℕ) (x : reesAlgebra.grade I n) :
    (reesAlgebra.toExtendedGradeEquiv I n x : I.extendedReesAlgebra) =
      reesAlgebra.toExtended I x :=
  (rfl)

/-- **Nonnegative graded part equals `reesAlgebra I`.** Inside `I.extendedReesAlgebra`, the
nonnegative graded part `⨆ n : ℕ, grade I (n : ℤ)` equals the image of Mathlib's `reesAlgebra I`
under `reesAlgebra.toExtended I`. -/
theorem reesAlgebra.range_toExtended_toSubmodule_eq_iSup_grade :
    (reesAlgebra.toExtended I).range.toSubmodule =
      ⨆ n : ℕ, Ideal.extendedReesAlgebra.grade I (n : ℤ) := by
  ext f
  rw [Subalgebra.mem_toSubmodule, Ideal.extendedReesAlgebra.mem_range_toExtended_iff,
    Ideal.extendedReesAlgebra.mem_iSup_grade_natCast_iff]

end CommRing
