/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import TauCeti.RingTheory.AdicCompletion.AlgHom
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.AdicCompletion.CofinalLimit

/-!
# Cofinal ideal invariance and Chinese remainder decomposition of adic completions

The `I`-adic completion of a commutative `A`-algebra `R` depends only on the equivalence class of
the `I`-adic filtration: if `I ≤ J` and `J ^ k ≤ I` for some `k`, the map of completions
`AdicCompletion I R →ₐ[A] AdicCompletion J R` induced by the identity of `R` is an isomorphism.
Neither finite generation of the ideals nor Noetherianity of `R` is required.

For a finite family `I : ι → Ideal R` of pairwise coprime ideals, `(⨅ i, I i) ^ n = ⨅ i, I i ^ n`
for every `n`, and the Chinese remainder theorem `Ideal.quotientInfRingEquivPiQuotient` splits
each quotient `R ⧸ (⨅ i, I i) ^ n` as `∀ i, R ⧸ I i ^ n`. Passing to projective limits gives the
canonical `A`-algebra isomorphism

`AdicCompletion (⨅ i, I i) R ≃ₐ[A] ∀ i, AdicCompletion (I i) R`

whose `i`-th coordinate is induced by the inclusion `⨅ j, I j ≤ I i`. Combining this with cofinal
ideal invariance decomposes `AdicCompletion J R` whenever `J` lies in each `I i` and contains a
power of `⨅ i, I i` — in particular, over a Noetherian ring, whenever `J.radical = ⨅ i, I i` for
finitely many pairwise coprime ideals `I i` (for instance the maximal ideals above a maximal ideal
of a base ring in a finite algebra).

## Main definitions and results

* `AdicCompletion.mapₐ_id_bijective_of_pow_le` and `AdicCompletion.equivOfLEOfPowLE`: for `I ≤ J`
  with `∃ k, J ^ k ≤ I`, the identity map induces an `A`-algebra isomorphism
  `AdicCompletion I R ≃ₐ[A] AdicCompletion J R`.
* `AdicCompletion.equivOfPowLEOfPowLE`: symmetric form for any two ideals each containing a power
  of the other.
* `Ideal.iInf_pow_eq_of_pairwise_isCoprime`: for a finite pairwise coprime family `I`,
  `(⨅ i, I i) ^ n = ⨅ i, I i ^ n`.
* `AdicCompletion.pi_mapₐ_iInf_bijective` and `AdicCompletion.coprimeEquiv`: the Chinese remainder
  isomorphism `AdicCompletion (⨅ i, I i) R ≃ₐ[A] ∀ i, AdicCompletion (I i) R`.
* `AdicCompletion.equivPiOfPowIInfLE` and `AdicCompletion.equivPiOfRadicalEqIInf`: the product
  decomposition of `AdicCompletion J R` when `(⨅ i, I i) ^ k ≤ J ≤ ⨅ i, I i`, and in particular
  when `R` is Noetherian and `J.radical = ⨅ i, I i`.

## References

* N. Bourbaki, *Commutative Algebra*, Ch. III, §2, no. 13, Proposition 18.
* M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
* [Stacks Project, Section 10.97](https://stacks.math.columbia.edu/tag/07N9).
-/

public section

open Function

namespace Ideal

/-- For a finite family of pairwise coprime ideals, powering commutes with intersection. -/
theorem iInf_pow_eq_of_pairwise_isCoprime {R ι : Type*} [CommRing R] [Finite ι]
    (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) (n : ℕ) :
    (⨅ i, I i) ^ n = ⨅ i, I i ^ n := by
  cases nonempty_fintype ι
  have h1 : ∏ i : ι, I i = ⨅ i, I i := by
    simpa using prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) fun i _ j _ hij ↦ hI hij
  have h2 : ∏ i : ι, I i ^ n = ⨅ i, I i ^ n := by
    simpa using prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      fun i _ j _ hij ↦ (hI hij).pow
  rw [← h1, ← Finset.prod_pow, h2]

end Ideal

namespace AdicCompletion

section Cofinal

variable (A : Type*) [CommRing A] {R : Type*} [CommRing R] [Algebra A R]

variable {A} in
/-- **Cofinal ideals have the same adic completion.** If `I ≤ J` and `J ^ k ≤ I` for some `k`, the
homomorphism `AdicCompletion I R →ₐ[A] AdicCompletion J R` induced by the identity of `R` is
bijective. -/
theorem mapₐ_id_bijective_of_pow_le {I J : Ideal R} (hIJ : I ≤ J) (hJI : ∃ k : ℕ, J ^ k ≤ I) :
    Bijective (mapₐ (AlgHom.id A R) hIJ) := by
  obtain ⟨k, hk⟩ := hJI
  have hkn (n : ℕ) : J ^ ((k + 1) * n) ≤ I ^ n :=
    (pow_mul J (k + 1) n).le.trans
      (Ideal.pow_right_mono ((Ideal.pow_le_pow_right k.le_succ).trans hk) n)
  have hopen (n : ℕ) : ∃ m : ℕ, J ^ m ≤ I ^ n := ⟨(k + 1) * n, hkn n⟩
  -- `toQuotient J (hopen n)` recovers `evalₐ I n` on the image of `mapₐ (AlgHom.id A R) hIJ`.
  have hleft (x : AdicCompletion I R) (n : ℕ) :
      toQuotient J (hopen n) (mapₐ (AlgHom.id A R) hIJ x) = evalₐ I n x := by
    rw [toQuotient_eq J (hopen n) (hkn n), RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, evalₐ_mapₐ (AlgHom.id A R) hIJ ((k + 1) * n) x]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I ((k + 1) * n) x)
    rw [← factor_evalₐ (Nat.le_mul_of_pos_left n k.succ_pos) x, ← hr]
    rfl
  refine ⟨fun x y hxy ↦ ext_evalₐ fun n ↦ ?_, fun y ↦ ?_⟩
  · rw [← hleft x n, ← hleft y n, hxy]
  · let g (n : ℕ) : AdicCompletion J R →+* R ⧸ I ^ n := toQuotient J (hopen n)
    have hg {m n : ℕ} (hmn : m ≤ n) : (Ideal.Quotient.factorPow I hmn).comp (g n) = g m := by
      ext z
      exact factor_toQuotient J (hopen n) (hopen m) (Ideal.pow_le_pow_right hmn) z
    refine ⟨liftRingHom I g hg y, ext_evalₐ fun n ↦ ?_⟩
    rw [evalₐ_mapₐ (AlgHom.id A R) hIJ n _, evalₐ_liftRingHom]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (g n y)
    have hfac := factor_toQuotient J (hopen n) ⟨n, le_rfl⟩ (Ideal.pow_right_mono hIJ n) y
    rw [toQuotient_pow] at hfac
    rw [← hr, Ideal.quotientMap_mk]
    exact (show Ideal.Quotient.mk (J ^ n) r =
      Ideal.Quotient.factor (Ideal.pow_right_mono hIJ n) (g n y) by rw [← hr]; rfl).trans hfac

/-- If `I ≤ J` and `J ^ k ≤ I` for some `k`, the identity of `R` induces an `A`-algebra
isomorphism `AdicCompletion I R ≃ₐ[A] AdicCompletion J R`. -/
noncomputable def equivOfLEOfPowLE {I J : Ideal R} (hIJ : I ≤ J) (hJI : ∃ k : ℕ, J ^ k ≤ I) :
    AdicCompletion I R ≃ₐ[A] AdicCompletion J R :=
  AlgEquiv.ofBijective (mapₐ (AlgHom.id A R) hIJ) (mapₐ_id_bijective_of_pow_le hIJ hJI)

/-- As an algebra homomorphism, `equivOfLEOfPowLE` is `mapₐ (AlgHom.id A R) hIJ`. -/
@[simp]
theorem toAlgHom_equivOfLEOfPowLE {I J : Ideal R} (hIJ : I ≤ J) (hJI : ∃ k : ℕ, J ^ k ≤ I) :
    (equivOfLEOfPowLE A hIJ hJI : AdicCompletion I R →ₐ[A] AdicCompletion J R) =
      mapₐ (AlgHom.id A R) hIJ :=
  AlgHom.ext fun _ ↦ rfl

/-- `equivOfLEOfPowLE` commutes with the canonical maps from `R` into its completions. -/
@[simp]
theorem equivOfLEOfPowLE_of {I J : Ideal R} (hIJ : I ≤ J) (hJI : ∃ k : ℕ, J ^ k ≤ I) (r : R) :
    equivOfLEOfPowLE A hIJ hJI (of I R r) = of J R r :=
  mapₐ_of (AlgHom.id A R) hIJ r

/-- On images of elements of `R`, the inverse of `equivOfLEOfPowLE` also acts as the identity. -/
@[simp]
theorem equivOfLEOfPowLE_symm_of {I J : Ideal R} (hIJ : I ≤ J) (hJI : ∃ k : ℕ, J ^ k ≤ I)
    (r : R) :
    (equivOfLEOfPowLE A hIJ hJI).symm (of J R r) = of I R r := by
  rw [← equivOfLEOfPowLE_of A hIJ hJI r, AlgEquiv.symm_apply_apply]

/-- **Cofinal ideal invariance of adic completions (symmetric form).** If `I ^ l ≤ J` and
`J ^ k ≤ I` for some `l` and `k`, there is a canonical `A`-algebra isomorphism
`AdicCompletion I R ≃ₐ[A] AdicCompletion J R` compatible with the canonical maps from `R`,
obtained by comparing both ideals with `I ⊓ J`. -/
noncomputable def equivOfPowLEOfPowLE {I J : Ideal R} (hIJ : ∃ l : ℕ, I ^ l ≤ J)
    (hJI : ∃ k : ℕ, J ^ k ≤ I) :
    AdicCompletion I R ≃ₐ[A] AdicCompletion J R :=
  have hI : ∃ m : ℕ, I ^ m ≤ I ⊓ J := by
    obtain ⟨l, hl⟩ := hIJ
    exact ⟨l + 1, le_inf (Ideal.pow_le_self l.succ_ne_zero)
      ((Ideal.pow_le_pow_right l.le_succ).trans hl)⟩
  have hJ : ∃ m : ℕ, J ^ m ≤ I ⊓ J := by
    obtain ⟨k, hk⟩ := hJI
    exact ⟨k + 1, le_inf ((Ideal.pow_le_pow_right k.le_succ).trans hk)
      (Ideal.pow_le_self k.succ_ne_zero)⟩
  (equivOfLEOfPowLE A inf_le_left hI).symm.trans (equivOfLEOfPowLE A inf_le_right hJ)

/-- `equivOfPowLEOfPowLE` commutes with the canonical maps from `R` into its completions. -/
@[simp]
theorem equivOfPowLEOfPowLE_of {I J : Ideal R} (hIJ : ∃ l : ℕ, I ^ l ≤ J)
    (hJI : ∃ k : ℕ, J ^ k ≤ I) (r : R) :
    equivOfPowLEOfPowLE A hIJ hJI (of I R r) = of J R r := by
  simp [equivOfPowLEOfPowLE]

end Cofinal

section ChineseRemainder

variable (A : Type*) [CommRing A] {R : Type*} [CommRing R] [Algebra A R]
variable {ι : Type*} [Finite ι]

variable {A} in
/-- **Chinese remainder theorem for adic completions (bijectivity).** For a finite family
`I : ι → Ideal R` of pairwise coprime ideals, the product of the canonical maps
`AdicCompletion (⨅ i, I i) R →ₐ[A] AdicCompletion (I i) R` is bijective. -/
theorem pi_mapₐ_iInf_bijective (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) :
    Bijective (AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (iInf_le I i)) := by
  let e (n : ℕ) : (R ⧸ (⨅ i, I i) ^ n) ≃+* ∀ i, R ⧸ I i ^ n :=
    (Ideal.quotEquivOfEq (Ideal.iInf_pow_eq_of_pairwise_isCoprime I hI n)).trans
      (Ideal.quotientInfRingEquivPiQuotient (fun i ↦ I i ^ n) fun _ _ hij ↦ (hI hij).pow)
  have he_mk (n : ℕ) (r : R) (i : ι) :
      e n (Ideal.Quotient.mk ((⨅ j, I j) ^ n) r) i = Ideal.Quotient.mk (I i ^ n) r := rfl
  have he (n : ℕ) (x : AdicCompletion (⨅ i, I i) R) (i : ι) :
      e n (evalₐ (⨅ j, I j) n x) i = evalₐ (I i) n (mapₐ (AlgHom.id A R) (iInf_le I i) x) := by
    rw [evalₐ_mapₐ (AlgHom.id A R) (iInf_le I i) n x]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ (⨅ j, I j) n x)
    simp [← hr, he_mk]
  refine ⟨fun x y hxy ↦ ext_evalₐ fun n ↦ (e n).injective (funext fun i ↦ ?_), fun z ↦ ?_⟩
  · rw [he, he]
    exact congrArg (evalₐ (I i) n) (congrFun hxy i)
  · let g (n : ℕ) : (∀ i, AdicCompletion (I i) R) →+* R ⧸ (⨅ i, I i) ^ n :=
      (e n).symm.toRingHom.comp
        (RingHom.pi fun i ↦ (evalₐ (I i) n).toRingHom.comp (Pi.evalRingHom _ i))
    have hg {m n : ℕ} (hmn : m ≤ n) :
        (Ideal.Quotient.factorPow (⨅ i, I i) hmn).comp (g n) = g m := by
      ext w
      apply (e m).injective
      ext i
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (g n w)
      have hri : Ideal.Quotient.mk (I i ^ n) r = evalₐ (I i) n (w i) := by
        have h1 : e n (g n w) i = evalₐ (I i) n (w i) := by simp [g]
        rwa [← hr, he_mk] at h1
      have hgm : e m (g m w) i = evalₐ (I i) m (w i) := by simp [g]
      rw [RingHom.comp_apply, hgm, ← factor_evalₐ hmn (w i), ← hri, ← hr]
      exact he_mk m r i
    refine ⟨liftRingHom (⨅ i, I i) g hg z, funext fun i ↦ ext_evalₐ fun n ↦ ?_⟩
    rw [AlgHom.pi_apply, ← he n _ i, evalₐ_liftRingHom]
    simp [g]

/-- **Chinese remainder isomorphism for adic completions.** For a finite family of pairwise
coprime ideals `I i` of an `A`-algebra `R`, the completion along `⨅ i, I i` is canonically
isomorphic as an `A`-algebra to `∀ i, AdicCompletion (I i) R`. -/
noncomputable def coprimeEquiv (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) :
    AdicCompletion (⨅ i, I i) R ≃ₐ[A] ∀ i, AdicCompletion (I i) R :=
  AlgEquiv.ofBijective (AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (iInf_le I i))
    (pi_mapₐ_iInf_bijective I hI)

/-- Each coordinate of `coprimeEquiv` is the map of completions induced by the inclusion
`⨅ j, I j ≤ I i`. -/
@[simp]
theorem coprimeEquiv_apply (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))
    (x : AdicCompletion (⨅ i, I i) R) (i : ι) :
    coprimeEquiv A I hI x i = mapₐ (AlgHom.id A R) (iInf_le I i) x := by
  simp [coprimeEquiv]

/-- On canonical images of elements of `R`, `coprimeEquiv` acts coordinatewise by `of (I i) R`. -/
theorem coprimeEquiv_of (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I)) (r : R) (i : ι) :
    coprimeEquiv A I hI (of (⨅ j, I j) R r) i = of (I i) R r := by
  rw [coprimeEquiv_apply]
  exact mapₐ_of (AlgHom.id A R) (iInf_le I i) r

variable {A} in
/-- If `J` lies in every ideal of a finite pairwise coprime family `I` and contains a power of
`⨅ i, I i`, the product of the maps `AdicCompletion J R →ₐ[A] AdicCompletion (I i) R` is
bijective. -/
theorem pi_mapₐ_bijective_of_pow_iInf_le {J : Ideal R} (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) (hJI : ∀ i, J ≤ I i) (hpow : ∃ k : ℕ, (⨅ i, I i) ^ k ≤ J) :
    Bijective (AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (hJI i)) := by
  have hcomp : (AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (hJI i)) =
      (AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (iInf_le I i)).comp
        (mapₐ (AlgHom.id A R) (le_iInf hJI)) :=
    AlgHom.ext fun x ↦ funext fun i ↦
      (mapₐ_mapₐ (AlgHom.id A R) (iInf_le I i) (AlgHom.id A R) (le_iInf hJI) x).symm
  rw [hcomp, AlgHom.coe_comp]
  exact (pi_mapₐ_iInf_bijective I hI).comp (mapₐ_id_bijective_of_pow_le (le_iInf hJI) hpow)

/-- **Product decomposition of a semilocal adic completion.** If `J` lies in each ideal of a
finite pairwise coprime family `I` and contains a power of `⨅ i, I i`, the completion
`AdicCompletion J R` splits canonically as `∀ i, AdicCompletion (I i) R`. -/
noncomputable def equivPiOfPowIInfLE {J : Ideal R} (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) (hJI : ∀ i, J ≤ I i) (hpow : ∃ k : ℕ, (⨅ i, I i) ^ k ≤ J) :
    AdicCompletion J R ≃ₐ[A] ∀ i, AdicCompletion (I i) R :=
  AlgEquiv.ofBijective (AlgHom.pi fun i ↦ mapₐ (AlgHom.id A R) (hJI i))
    (pi_mapₐ_bijective_of_pow_iInf_le I hI hJI hpow)

/-- Each coordinate of `equivPiOfPowIInfLE` is `mapₐ (AlgHom.id A R) (hJI i)`. -/
@[simp]
theorem equivPiOfPowIInfLE_apply {J : Ideal R} (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) (hJI : ∀ i, J ≤ I i) (hpow : ∃ k : ℕ, (⨅ i, I i) ^ k ≤ J)
    (x : AdicCompletion J R) (i : ι) :
    equivPiOfPowIInfLE A I hI hJI hpow x i = mapₐ (AlgHom.id A R) (hJI i) x := by
  simp [equivPiOfPowIInfLE]

/-- On canonical images of elements of `R`, `equivPiOfPowIInfLE` acts coordinatewise by
`of (I i) R`. -/
theorem equivPiOfPowIInfLE_of {J : Ideal R} (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) (hJI : ∀ i, J ≤ I i) (hpow : ∃ k : ℕ, (⨅ i, I i) ^ k ≤ J)
    (r : R) (i : ι) :
    equivPiOfPowIInfLE A I hI hJI hpow (of J R r) i = of (I i) R r := by
  rw [equivPiOfPowIInfLE_apply]
  exact mapₐ_of (AlgHom.id A R) (hJI i) r

/-- Over a Noetherian ring `R`, if the radical of `J` is the intersection of a finite pairwise
coprime family `I i`, then `AdicCompletion J R` splits canonically as
`∀ i, AdicCompletion (I i) R`. -/
noncomputable def equivPiOfRadicalEqIInf [IsNoetherianRing R] {J : Ideal R} (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) (hrad : J.radical = ⨅ i, I i) :
    AdicCompletion J R ≃ₐ[A] ∀ i, AdicCompletion (I i) R :=
  equivPiOfPowIInfLE A I hI (fun i ↦ J.le_radical.trans (hrad.le.trans (iInf_le I i)))
    (Ideal.exists_pow_le_of_le_radical_of_fg hrad.ge (IsNoetherian.noetherian _))

/-- Each coordinate of `equivPiOfRadicalEqIInf` is induced by `J ≤ I i`. -/
@[simp]
theorem equivPiOfRadicalEqIInf_apply [IsNoetherianRing R] {J : Ideal R} (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) (hrad : J.radical = ⨅ i, I i)
    (x : AdicCompletion J R) (i : ι) :
    equivPiOfRadicalEqIInf A I hI hrad x i =
      mapₐ (AlgHom.id A R) (J.le_radical.trans (hrad.le.trans (iInf_le I i))) x := by
  simp [equivPiOfRadicalEqIInf]

end ChineseRemainder

end AdicCompletion
