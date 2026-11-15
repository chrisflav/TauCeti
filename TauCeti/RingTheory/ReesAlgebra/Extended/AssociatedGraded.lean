/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.ReesAlgebra.Extended.Grading

/-!
# Special fibre of the extended Rees algebra and comparison with `gr_I R`

For an ideal `I` of a commutative ring `R`, setting the inverse parameter `invT I = T (-1)` of the
extended Rees algebra `Ideal.extendedReesAlgebra I = R[It, t⁻¹]` to zero kills all strictly negative
degrees and mods out each nonnegative degree `I ^ n · T n` by `I ^ (n + 1) · T n`. This file
identifies the `t⁻¹ = 0` fibre with `Ideal.AssociatedGraded I = ⨁ n : ℕ, I ^ n ⧸ I ^ (n + 1)`, and
restricts the comparison along `reesAlgebra.toExtended I` to recover the standard quotient
presentation `(reesAlgebra I ⧸ I · reesAlgebra I) ≃ₐ[R] I.AssociatedGraded`.

## Main definitions

* `Ideal.extendedReesAlgebra.toAssociatedGraded I`: the surjective `R`-algebra homomorphism
  `I.extendedReesAlgebra →ₐ[R] I.AssociatedGraded` sending `C r * T n` (`r ∈ I ^ n`) to `[r]_n` and
  `invT I` to `0`.
* `Ideal.extendedReesAlgebra.quotientInvTEquiv I`: the `R`-algebra isomorphism
  `(I.extendedReesAlgebra ⧸ Ideal.span {invT I}) ≃ₐ[R] I.AssociatedGraded`.
* `reesAlgebra.toAssociatedGraded I` and `reesAlgebra.quotientMapAlgebraMapEquiv I`: restriction to
  Mathlib's `reesAlgebra I` and the isomorphism
  `(reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) ≃ₐ[R] I.AssociatedGraded`.

## Main results

* `Ideal.extendedReesAlgebra.ker_toAssociatedGraded`: the kernel of `toAssociatedGraded I` is
  `Ideal.span {invT I}`.
* `Ideal.extendedReesAlgebra.map_toAssociatedGraded`: naturality with `Ideal.AssociatedGraded.map`.
* `reesAlgebra.ker_toAssociatedGraded`: the kernel on `reesAlgebra I` is
  `I.map (algebraMap R (reesAlgebra I))`.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, GTM 150, §6.5.
* H. Matsumura, *Commutative Ring Theory*, Cambridge Studies in Advanced Mathematics 8, §15.
-/

public section

open DirectSum LaurentPolynomial

namespace Ideal.extendedReesAlgebra

variable {R : Type*} [CommRing R] (I : Ideal R)

private theorem coeff_mem_pow_toNat {d : ℤ} (f : I.extendedReesAlgebra) :
    (f : R[T;T⁻¹]).coeff d ∈ I ^ d.toNat := by
  have hf := Ideal.mem_extendedReesAlgebra_iff_zFiltration.mp f.2 d
  rwa [Ideal.zFiltration_def, neg_neg] at hf

private noncomputable def gradeToAssociatedGraded (d : ℤ) :
    grade I d →ₗ[R] I.AssociatedGraded :=
  if _ : 0 ≤ d then
    { toFun f := Ideal.AssociatedGraded.mk I d.toNat
        ⟨((f : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff d, coeff_mem_pow_toNat I f.1⟩
      map_add' f g := by
        rw [← map_add]
        exact congr_arg (Ideal.AssociatedGraded.mk I d.toNat) (Subtype.ext (by simp))
      map_smul' r f := by
        rw [RingHom.id_apply, ← map_smul]
        exact congr_arg (Ideal.AssociatedGraded.mk I d.toNat) (Subtype.ext (by simp)) }
  else
    0

private theorem gradeToAssociatedGraded_of_neg {d : ℤ} (hd : d < 0) (f : grade I d) :
    gradeToAssociatedGraded I d f = 0 := by
  rw [gradeToAssociatedGraded]
  split_ifs with h
  · omega
  · rfl

private theorem gradeToAssociatedGraded_of_nonneg {d : ℤ} (hd : 0 ≤ d) (f : grade I d) :
    gradeToAssociatedGraded I d f =
      Ideal.AssociatedGraded.mk I d.toNat
        ⟨((f : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff d, coeff_mem_pow_toNat I f.1⟩ := by
  rw [gradeToAssociatedGraded]
  split_ifs
  rfl

private theorem coeff_mul_of_mem_grade {d₁ d₂ : ℤ} {x y : I.extendedReesAlgebra}
    (hx : x ∈ grade I d₁) (hy : y ∈ grade I d₂) :
    ((x * y : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff (d₁ + d₂) =
      (x : R[T;T⁻¹]).coeff d₁ * (y : R[T;T⁻¹]).coeff d₂ := by
  obtain ⟨r, -, hr⟩ := mem_grade_iff.mp hx
  obtain ⟨s, -, hs⟩ := mem_grade_iff.mp hy
  have hmul : ((x * y : I.extendedReesAlgebra) : R[T;T⁻¹]) = C (r * s) * T (d₁ + d₂) := by
    rw [Subalgebra.coe_mul, ← hr, ← hs, T_add, map_mul]
    ring
  rw [hmul, ← hr, ← hs]
  simp only [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

private theorem gradeToAssociatedGraded_one :
    gradeToAssociatedGraded I 0 (1 : grade I 0) = 1 := by
  rw [gradeToAssociatedGraded_of_nonneg I le_rfl, ← Ideal.AssociatedGraded.mk_zero_one]
  refine congr_arg (Ideal.AssociatedGraded.mk I 0) (Subtype.ext ?_)
  simp

private theorem gradeToAssociatedGraded_mul {d₁ d₂ : ℤ} (x : grade I d₁) (y : grade I d₂) :
    gradeToAssociatedGraded I (d₁ + d₂) ⟨(x : I.extendedReesAlgebra) * y,
      SetLike.mul_mem_graded x.2 y.2⟩ =
      gradeToAssociatedGraded I d₁ x * gradeToAssociatedGraded I d₂ y := by
  rcases lt_or_ge (d₁ + d₂) 0 with hsum | hsum
  · rw [gradeToAssociatedGraded_of_neg I hsum]
    rcases lt_or_ge d₁ 0 with hd₁ | _
    · simp [gradeToAssociatedGraded_of_neg I hd₁]
    · simp [gradeToAssociatedGraded_of_neg I (by omega : d₂ < 0)]
  · rw [gradeToAssociatedGraded_of_nonneg I hsum]
    rcases lt_or_ge d₁ 0 with hd₁ | hd₁
    · rw [gradeToAssociatedGraded_of_neg I hd₁, zero_mul, Ideal.AssociatedGraded.mk_eq_zero_iff]
      -- Unfold the subtype projection before rewriting the homogeneous product coefficient.
      change (((x : I.extendedReesAlgebra) * y : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff
        (d₁ + d₂) ∈ I ^ ((d₁ + d₂).toNat + 1)
      rw [coeff_mul_of_mem_grade I x.2 y.2]
      exact Ideal.mul_mem_left _ _
        (Ideal.pow_le_pow_right (by omega : (d₁ + d₂).toNat + 1 ≤ d₂.toNat)
          (coeff_mem_pow_toNat I y.1))
    · rcases lt_or_ge d₂ 0 with hd₂ | hd₂
      · rw [gradeToAssociatedGraded_of_neg I hd₂, mul_zero, Ideal.AssociatedGraded.mk_eq_zero_iff]
        -- Unfold the subtype projection before rewriting the homogeneous product coefficient.
        change (((x : I.extendedReesAlgebra) * y : I.extendedReesAlgebra) : R[T;T⁻¹]).coeff
          (d₁ + d₂) ∈ I ^ ((d₁ + d₂).toNat + 1)
        rw [coeff_mul_of_mem_grade I x.2 y.2]
        exact Ideal.mul_mem_right _ _
          (Ideal.pow_le_pow_right (by omega : (d₁ + d₂).toNat + 1 ≤ d₁.toNat)
            (coeff_mem_pow_toNat I x.1))
      · rw [gradeToAssociatedGraded_of_nonneg I hd₁, gradeToAssociatedGraded_of_nonneg I hd₂,
          Ideal.AssociatedGraded.mk_mul_mk,
          Ideal.AssociatedGraded.mk_congr (by omega : (d₁ + d₂).toNat = d₁.toNat + d₂.toNat)]
        exact congr_arg (Ideal.AssociatedGraded.mk I (d₁.toNat + d₂.toNat))
          (Subtype.ext (coeff_mul_of_mem_grade I x.2 y.2))

/-- The canonical `R`-algebra homomorphism `I.extendedReesAlgebra →ₐ[R] I.AssociatedGraded`
evaluating the inverse parameter `invT I` at `0`: it sends `C r * T n` (`r ∈ I ^ n`) to the class
`[r]_n` in `I ^ n ⧸ I ^ (n + 1)` and kills all strictly negative Laurent degrees. -/
noncomputable def toAssociatedGraded : I.extendedReesAlgebra →ₐ[R] I.AssociatedGraded :=
  (DirectSum.toAlgebra R _ (gradeToAssociatedGraded I)
    (gradeToAssociatedGraded_one I) fun x y ↦ gradeToAssociatedGraded_mul I x y).comp
      (DirectSum.decomposeAlgEquiv (grade I)).toAlgHom

private theorem toAssociatedGraded_of_mem_grade {d : ℤ} {f : I.extendedReesAlgebra}
    (hf : f ∈ grade I d) :
    toAssociatedGraded I f = gradeToAssociatedGraded I d ⟨f, hf⟩ := by
  rw [toAssociatedGraded, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    DirectSum.decomposeAlgEquiv_apply, DirectSum.decompose_of_mem (grade I) hf]
  exact (DirectSum.toAlgebra_apply R _ (gradeToAssociatedGraded I) (gradeToAssociatedGraded_one I)
    (fun x y ↦ gradeToAssociatedGraded_mul I x y) _).trans (DirectSum.toSemiring_of _ _ _ _ _)

variable {I}

@[simp]
theorem toAssociatedGraded_monomial_natCast (n : ℕ) (r : R) (hr : r ∈ I.zFiltration (-(n : ℤ))) :
    toAssociatedGraded I (monomial I (n : ℤ) r hr) =
      Ideal.AssociatedGraded.mk I n ⟨r, by simpa using hr⟩ := by
  rw [toAssociatedGraded_of_mem_grade I (monomial_mem_grade (n : ℤ) r hr),
    gradeToAssociatedGraded_of_nonneg I (Nat.cast_nonneg n),
    Ideal.AssociatedGraded.mk_congr (Int.toNat_natCast n)]
  refine congr_arg (Ideal.AssociatedGraded.mk I n) (Subtype.ext ?_)
  simp only [coe_monomial, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same]

@[simp]
theorem toAssociatedGraded_monomial_of_neg {d : ℤ} (hd : d < 0) (r : R)
    (hr : r ∈ I.zFiltration (-d)) :
    toAssociatedGraded I (monomial I d r hr) = 0 := by
  rw [toAssociatedGraded_of_mem_grade I (monomial_mem_grade d r hr),
    gradeToAssociatedGraded_of_neg I hd]

@[simp]
theorem toAssociatedGraded_invT : toAssociatedGraded I (invT I) = 0 := by
  rw [toAssociatedGraded_of_mem_grade I (invT_mem_grade I),
    gradeToAssociatedGraded_of_neg I (by omega)]

@[simp]
theorem toAssociatedGraded_monomialDegreeOne {a : R} (ha : a ∈ I) :
    toAssociatedGraded I (monomialDegreeOne ha) =
      Ideal.AssociatedGraded.mk I 1 ⟨a, by rw [pow_one]; exact ha⟩ := by
  have h1 : monomialDegreeOne ha = monomial I ((1 : ℕ) : ℤ) a (by simpa using ha) := by
    apply Subtype.ext
    simp [coe_monomialDegreeOne, coe_monomial]
  rw [h1, toAssociatedGraded_monomial_natCast]

/-- The degree-`n` component of `toAssociatedGraded I f` in `I.AssociatedGraded` is the residue
class of `(f : R[T;T⁻¹]).coeff n` in `I ^ n ⧸ I ^ (n + 1)`. -/
@[simp]
theorem toAssociatedGraded_apply (f : I.extendedReesAlgebra) (n : ℕ) :
    toAssociatedGraded I f n =
      Submodule.Quotient.mk
        ⟨(f : R[T;T⁻¹]).coeff (n : ℤ), Ideal.mem_extendedReesAlgebra_iff.mp f.2 n⟩ := by
  conv_lhs => rw [as_sum_support f]
  rw [map_sum, DFinsupp.finsetSum_apply]
  by_cases hn : (n : ℤ) ∈ (f : R[T;T⁻¹]).coeff.support
  · rw [Finset.sum_eq_single (n : ℤ)]
    · rw [toAssociatedGraded_monomial_natCast, Ideal.AssociatedGraded.mk_apply,
        DirectSum.of_eq_same]
    · intro d _ hdn
      rcases lt_or_ge d 0 with hd | hd
      · simp [toAssociatedGraded_monomial_of_neg hd]
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = d := ⟨d.toNat, Int.toNat_of_nonneg hd⟩
        have hmn : m ≠ n := fun h ↦ hdn (congr_arg Nat.cast h)
        rw [toAssociatedGraded_monomial_natCast, Ideal.AssociatedGraded.mk_apply,
          DirectSum.of_eq_of_ne _ _ _ hmn.symm]
    · exact fun h ↦ absurd hn h
  · have hc0 : (f : R[T;T⁻¹]).coeff (n : ℤ) = 0 := Finsupp.notMem_support_iff.mp hn
    have hsum0 : (∑ d ∈ (f : R[T;T⁻¹]).coeff.support,
        toAssociatedGraded I
          (monomial I d ((f : R[T;T⁻¹]).coeff d)
            (Ideal.mem_extendedReesAlgebra_iff_zFiltration.mp f.2 d)) n) = 0 := by
      refine Finset.sum_eq_zero fun d hd ↦ ?_
      have hdn : d ≠ (n : ℤ) := fun h ↦ hn (h ▸ hd)
      rcases lt_or_ge d 0 with hd0 | hd0
      · simp [toAssociatedGraded_monomial_of_neg hd0]
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = d := ⟨d.toNat, Int.toNat_of_nonneg hd0⟩
        have hmn : m ≠ n := fun h ↦ hdn (congr_arg Nat.cast h)
        rw [toAssociatedGraded_monomial_natCast, Ideal.AssociatedGraded.mk_apply,
          DirectSum.of_eq_of_ne _ _ _ hmn.symm]
    rw [hsum0, eq_comm, Ideal.gradedPiece_mk_eq_zero_iff]
    simp [hc0]

variable (I)

/-- `toAssociatedGraded I` is surjective onto `I.AssociatedGraded`. -/
theorem toAssociatedGraded_surjective : Function.Surjective (toAssociatedGraded I) := by
  intro g
  induction g using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n q =>
    obtain ⟨⟨r, hr⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨monomial I (n : ℤ) r (by simpa using hr),
      (toAssociatedGraded_monomial_natCast n r _).trans (Ideal.AssociatedGraded.mk_apply n _)⟩
  | add x y hx hy =>
    obtain ⟨fx, rfl⟩ := hx
    obtain ⟨fy, rfl⟩ := hy
    exact ⟨fx + fy, map_add _ _ _⟩

/-- **Kernel at `t⁻¹ = 0`.** The kernel of `toAssociatedGraded I` on `I.extendedReesAlgebra` is the
principal ideal generated by `invT I`. -/
theorem ker_toAssociatedGraded :
    RingHom.ker (toAssociatedGraded I : I.extendedReesAlgebra →+* I.AssociatedGraded) =
      Ideal.span {invT I} := by
  ext f
  rw [RingHom.mem_ker, AlgHom.coe_toRingHom, DFinsupp.ext_iff, mem_span_invT_iff]
  refine forall_congr' fun n ↦ ?_
  rw [toAssociatedGraded_apply, DFinsupp.zero_apply, Ideal.gradedPiece_mk_eq_zero_iff]

/-- **Special fibre at `t⁻¹ = 0`.** Quotienting the extended Rees algebra `R[It, t⁻¹]` by `invT I`
canonically recovers the associated graded ring `gr_I R`. -/
noncomputable def quotientInvTEquiv :
    (I.extendedReesAlgebra ⧸ Ideal.span {invT I}) ≃ₐ[R] I.AssociatedGraded :=
  (Ideal.quotientEquivAlgOfEq R (ker_toAssociatedGraded I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (toAssociatedGraded_surjective I))

@[simp]
theorem quotientInvTEquiv_mk (f : I.extendedReesAlgebra) :
    quotientInvTEquiv I (Ideal.Quotient.mk _ f) = toAssociatedGraded I f :=
  (rfl)

@[simp]
theorem quotientInvTEquiv_symm_mk (n : ℕ) (x : ↥(I ^ n)) :
    (quotientInvTEquiv I).symm (Ideal.AssociatedGraded.mk I n x) =
      Ideal.Quotient.mk _ (monomial I (n : ℤ) x.1 (by simp)) := by
  apply (quotientInvTEquiv I).symm_apply_eq.mpr
  simp

variable {I} in
/-- `toAssociatedGraded` is natural with respect to ring homomorphisms `f : R →+* S` satisfying
`I ≤ J.comap f`. -/
theorem map_toAssociatedGraded {S : Type*} [CommRing S] {J : Ideal S} (f : R →+* S)
    (h : I ≤ J.comap f) (x : I.extendedReesAlgebra) :
    Ideal.AssociatedGraded.map f h (toAssociatedGraded I x) =
      toAssociatedGraded J (map f h x) := by
  conv_lhs => rw [as_sum_support x]
  conv_rhs => rw [as_sum_support x]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rcases lt_or_ge d 0 with hd | hd
  · simp [toAssociatedGraded_monomial_of_neg hd]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = d := ⟨d.toNat, Int.toNat_of_nonneg hd⟩
    simp [toAssociatedGraded_monomial_natCast]

end Ideal.extendedReesAlgebra

/-! ### Induced quotient presentation of `reesAlgebra I` -/

namespace reesAlgebra

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The canonical surjective `R`-algebra homomorphism `reesAlgebra I →ₐ[R] I.AssociatedGraded`,
obtained by restricting `Ideal.extendedReesAlgebra.toAssociatedGraded I` along
`reesAlgebra.toExtended I`. -/
noncomputable def toAssociatedGraded : reesAlgebra I →ₐ[R] I.AssociatedGraded :=
  (Ideal.extendedReesAlgebra.toAssociatedGraded I).comp (reesAlgebra.toExtended I)

@[simp]
theorem toAssociatedGraded_apply_toExtended (f : reesAlgebra I) :
    Ideal.extendedReesAlgebra.toAssociatedGraded I (reesAlgebra.toExtended I f) =
      toAssociatedGraded I f :=
  (rfl)

@[simp]
theorem toAssociatedGraded_apply (f : reesAlgebra I) (n : ℕ) :
    toAssociatedGraded I f n =
      Submodule.Quotient.mk ⟨(f : Polynomial R).coeff n, (mem_reesAlgebra_iff I _).mp f.2 n⟩ := by
  rw [toAssociatedGraded, AlgHom.comp_apply, Ideal.extendedReesAlgebra.toAssociatedGraded_apply]
  refine congr_arg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [reesAlgebra.coe_toExtended, ← coeff_trunc, Polynomial.trunc_toLaurent]

@[simp]
theorem toAssociatedGraded_monomialDegreeOne {I : Ideal R} {a : R} (ha : a ∈ I) :
    toAssociatedGraded I (monomialDegreeOne ha) =
      Ideal.AssociatedGraded.mk I 1 ⟨a, by rw [pow_one]; exact ha⟩ := by
  rw [toAssociatedGraded, AlgHom.comp_apply, toExtended_monomialDegreeOne,
    Ideal.extendedReesAlgebra.toAssociatedGraded_monomialDegreeOne]

private theorem toExtended_monomial (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    reesAlgebra.toExtended I ⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ =
      Ideal.extendedReesAlgebra.monomial I (n : ℤ) r (by simpa using hr) := by
  apply Subtype.ext
  rw [reesAlgebra.coe_toExtended, Polynomial.toLaurent_C_mul_T,
    Ideal.extendedReesAlgebra.coe_monomial]

/-- `reesAlgebra.toAssociatedGraded I` is surjective onto `I.AssociatedGraded`. -/
theorem toAssociatedGraded_surjective : Function.Surjective (toAssociatedGraded I) := by
  intro g
  induction g using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n q =>
    obtain ⟨⟨r, hr⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩, ?_⟩
    rw [toAssociatedGraded, AlgHom.comp_apply, toExtended_monomial I n r hr,
      Ideal.extendedReesAlgebra.toAssociatedGraded_monomial_natCast,
      Ideal.AssociatedGraded.mk_apply]
  | add x y hx hy =>
    obtain ⟨fx, rfl⟩ := hx
    obtain ⟨fy, rfl⟩ := hy
    exact ⟨fx + fy, map_add _ _ _⟩

/-- The kernel of `reesAlgebra.toAssociatedGraded I` is the extended ideal
`I.map (algebraMap R (reesAlgebra I))`. -/
theorem ker_toAssociatedGraded :
    RingHom.ker (toAssociatedGraded I : reesAlgebra I →+* I.AssociatedGraded) =
      I.map (algebraMap R (reesAlgebra I)) := by
  ext f
  rw [RingHom.mem_ker, AlgHom.coe_toRingHom, DFinsupp.ext_iff, mem_map_algebraMap_reesAlgebra_iff]
  refine forall_congr' fun n ↦ ?_
  rw [toAssociatedGraded_apply, DFinsupp.zero_apply, Ideal.gradedPiece_mk_eq_zero_iff]

/-- **Quotient of `reesAlgebra I` by `I · reesAlgebra I`.** Restricting the extended-Rees quotient
along `reesAlgebra.toExtended I` yields `(reesAlgebra I ⧸ I · reesAlgebra I) ≃ₐ[R] gr_I R`. -/
noncomputable def quotientMapAlgebraMapEquiv :
    (reesAlgebra I ⧸ I.map (algebraMap R (reesAlgebra I))) ≃ₐ[R] I.AssociatedGraded :=
  (Ideal.quotientEquivAlgOfEq R (ker_toAssociatedGraded I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (toAssociatedGraded_surjective I))

@[simp]
theorem quotientMapAlgebraMapEquiv_mk (f : reesAlgebra I) :
    quotientMapAlgebraMapEquiv I (Ideal.Quotient.mk _ f) = toAssociatedGraded I f :=
  (rfl)

@[simp]
theorem quotientMapAlgebraMapEquiv_symm_mk (n : ℕ) (x : ↥(I ^ n)) :
    (quotientMapAlgebraMapEquiv I).symm (Ideal.AssociatedGraded.mk I n x) =
      Ideal.Quotient.mk _ ⟨Polynomial.monomial n x.1, reesAlgebra.monomial_mem.mpr x.2⟩ := by
  apply (quotientMapAlgebraMapEquiv I).symm_apply_eq.mpr
  rw [quotientMapAlgebraMapEquiv_mk, toAssociatedGraded, AlgHom.comp_apply,
    toExtended_monomial I n x.1 x.2, Ideal.extendedReesAlgebra.toAssociatedGraded_monomial_natCast]

end reesAlgebra
