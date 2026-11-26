/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Saturated
public import TauCeti.Algebra.Module.ZLattice.RationalSubspace
public import TauCeti.LinearAlgebra.Dimension.Submodule
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.BoundedEvaluation
public import TauCeti.NumberTheory.NumberField.Discriminant.RelationLattice
public import TauCeti.RingTheory.MvPolynomial.Jacobian.Basic
import TauCeti.Algebra.Order.BigOperators.Fin
import TauCeti.Geometry.Euclidean.Volume.UnitBall
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond
import TauCeti.NumberTheory.NumberField.Discriminant.Basic

/-!
# Small polynomial relations with a nonvanishing Jacobian

Let `K` be a number field of degree `n = [K : ℚ]` and `κ : σ → 𝓞 K` a finite tuple of
algebraic integers of size `r = #σ`. Evaluating the `M = (d + r choose r)` monomials `κ ^ α` of
degree at most `d` gives a `ℚ`-subspace of `ℚ`-relations among the monomials, whose integral
points form a saturated lattice `L` in its `ℓ`-dimensional real span (`relationSubspace`). When
degree-`d` rational evaluation at `κ` covers `K`, we have `ℓ = M - n`, and the kernel of
`firstJetValueMap` at the conjugate points `(τ (κ j))_j` of `κ` has `ℂ`-dimension `ℓ`.

When every `κ j` has house at most `C₀ ≥ 1`, every conjugate of every bounded-degree monomial
has modulus at most `C₀ ^ d`, so
`TauCeti.NumberField.covolume_intLattice_ker_linearCombination_le_of_norm_le` bounds the covolume
of `L` by `√(M ^ n * C₀ ^ (2 * n * d)) / √|disc K| ≤ √(M ^ n) * C₀ ^ (n * d)`.
Applying Minkowski's second theorem on the unit Euclidean ball in the intrinsic `ℓ`-dimensional
real span of `L` (using `TauCeti.two_div_sqrt_pow_le_volumeReal_closedBall`) produces `ℓ`
linearly independent integral relation polynomials of degree at most `d` with nondecreasing
coefficient Euclidean norms at least `1` and product at most
`ℓ ^ (ℓ / 2) * √(M ^ n) * C₀ ^ (n * d)`. Discarding the longest `n - 1` of them leaves
`k = ℓ + 1 - n` independent relations whose coefficient norms and individual coefficients are at
most `ℓ ^ (ℓ / (2 * n)) * √M * C₀ ^ d`.

If the conjugate points of `κ` are well poised in degree `d`, the derivative map
`TauCeti.firstJetDerivMap` is surjective on `ker (firstJetValueMap ... d)`, so by codimension
counting (`LinearMap.exists_surjective_proj_comp_domRestrict`) the retained `k` relations still
surject onto at least one conjugate gradient block `ℂ^σ`. Picking a nonzero `r × r` minor from
that block yields `r` integer polynomials `E : σ → MvPolynomial σ ℤ` of total degree at most
`d`, all vanishing at `κ`, with coefficients bounded by `ℓ ^ (ℓ / (2 * n)) * √M * C₀ ^ d`
and with `TauCeti.jacobian E` nonvanishing at `κ`.

## Main definitions

* `TauCeti.NumberField.monomialTuple`: the monomials `κ ^ α` of total degree at most `d` as a
  family in `𝓞 K`.
* `TauCeti.NumberField.relationSubspace`: the `ℚ`-subspace of rational linear relations among
  `monomialTuple κ d`.

## Main results

* `TauCeti.NumberField.finrank_relationSubspace_of_map_eq_top`: when rational bounded evaluation
  covers `K`, the relation subspace has dimension `(d + #σ).choose (#σ) - [K : ℚ]`.
* `TauCeti.NumberField.covolume_relationSubspace_le`: the covolume bound with `√|disc K|` in the
  denominator.
* `TauCeti.NumberField.exists_linearIndependent_short_relations`: Minkowski's second theorem
  producing `ℓ` independent short integral relation polynomials.
* `TauCeti.NumberField.exists_truncated_short_relations`: dropping `n - 1` relations leaves
  `ℓ + 1 - n` relations with explicit coefficient bounds.
* `TauCeti.NumberField.exists_jacobian_ne_zero_equations_of_wellPoised`: extracting `r` bounded
  integer equations vanishing at `κ` with `jacobian E` nonzero at `κ`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §3,
  pp. 493–495.
-/

public section

open MeasureTheory Module MvPolynomial NumberField
open scoped Matrix

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

section MonomialRelations

variable {σ : Type*} (κ : σ → 𝓞 K) (d : ℕ)

/-- The monomials of total degree at most `d` evaluated at an integral tuple `κ : σ → 𝓞 K`,
regarded as a finite family in `𝓞 K`. -/
noncomputable def monomialTuple : {s : σ →₀ ℕ // s.degree ≤ d} → 𝓞 K :=
  fun s ↦ aeval κ (monomial s.val (1 : ℤ))

/-- Coercing `monomialTuple κ d s` to `K` evaluates the rational monomial `s` at `κ`. -/
@[simp]
theorem coe_monomialTuple (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    (monomialTuple κ d s : K) = aeval (fun j ↦ (κ j : K)) (monomial s.val (1 : ℚ)) := by
  rw [monomialTuple, aeval_monomial, aeval_monomial, map_one, map_one, one_mul, one_mul,
    Finsupp.prod, Finsupp.prod]
  push_cast
  rfl

variable [Fintype σ] [DecidableEq σ]

/-- The `ℚ`-subspace of rational linear relations among the degree-`≤ d` monomial values at
`κ`. -/
noncomputable def relationSubspace :
    Submodule ℚ ({s : σ →₀ ℕ // s.degree ≤ d} → ℚ) :=
  LinearMap.ker (Fintype.linearCombination ℚ fun s ↦ (monomialTuple κ d s : K))

/-- A tuple of integers lies in the integer points of `relationSubspace κ d` exactly when the
corresponding integer polynomial of total degree at most `d` vanishes at `κ`. -/
theorem mem_relationSubspace_intPoints_iff (z : {s : σ →₀ ℕ // s.degree ≤ d} → ℤ) :
    z ∈ (relationSubspace κ d).intPoints ↔
      aeval (fun j ↦ (κ j : K))
        (((basisRestrictTotalDegree σ ℤ d).equivFun.symm z : restrictTotalDegree σ ℤ d) :
          MvPolynomial σ ℤ) = 0 := by
  rw [Submodule.mem_intPoints, relationSubspace, LinearMap.mem_ker,
    Fintype.linearCombination_apply, (basisRestrictTotalDegree σ ℤ d).equivFun_symm_apply]
  simp only [Submodule.coe_sum, SetLike.val_smul, coe_basisRestrictTotalDegree, map_sum,
    zsmul_eq_mul, coe_monomialTuple, aeval_monomial, map_one, one_mul, Rat.cast_intCast,
    Rat.smul_def, map_mul, map_intCast]

/-- The range of rational linear combinations of `monomialTuple κ d` is the image of
`restrictTotalDegree σ ℚ d` under evaluation at `κ`. -/
theorem range_linearCombination_monomialTuple :
    LinearMap.range (Fintype.linearCombination ℚ fun s ↦ (monomialTuple κ d s : K)) =
      (restrictTotalDegree σ ℚ d).map (aeval (fun j ↦ (κ j : K))).toLinearMap := by
  rw [Fintype.range_linearCombination, restrictTotalDegree_eq_span, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, Subtype.exists, coe_monomialTuple, Set.mem_ofPred_eq,
    AlgHom.toLinearMap_apply]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨monomial s 1, ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩

/-- When degree-`d` rational evaluation at `κ` is onto `K`, the relation subspace has dimension
`(d + #σ).choose (#σ) - [K : ℚ]`. -/
theorem finrank_relationSubspace_of_map_eq_top
    (hκ : (restrictTotalDegree σ ℚ d).map (aeval (fun j ↦ (κ j : K))).toLinearMap = ⊤) :
    finrank ℚ (relationSubspace κ d) =
      (d + Fintype.card σ).choose (Fintype.card σ) - finrank ℚ K := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (Fintype.linearCombination ℚ fun s ↦ (monomialTuple κ d s : K))
  have hkerQ :
      (Fintype.linearCombination ℚ fun s ↦ (monomialTuple κ d s : K)).ker =
        relationSubspace κ d := rfl
  rw [hkerQ, range_linearCombination_monomialTuple, hκ, finrank_top,
    Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    Finsupp.card_degree_le_eq_choose] at h
  omega

/-- The kernel of `firstJetValueMap` at the conjugate points of `κ` has `ℂ`-dimension equal to
`finrank ℚ (relationSubspace κ d)`. -/
theorem finrank_ker_firstJetValueMap_conjugate :
    finrank ℂ (LinearMap.ker (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d)) =
      finrank ℚ (relationSubspace κ d) := by
  have hrkC := LinearMap.finrank_range_add_finrank_ker
    (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d)
  have hrkQ := LinearMap.finrank_range_add_finrank_ker
    (Fintype.linearCombination ℚ fun s ↦ (monomialTuple κ d s : K))
  have hkerQ :
      (Fintype.linearCombination ℚ fun s ↦ (monomialTuple κ d s : K)).ker =
        relationSubspace κ d := rfl
  have hcard : finrank ℂ (restrictTotalDegree σ ℂ d) =
      finrank ℚ ({s : σ →₀ ℕ // s.degree ≤ d} → ℚ) := by
    rw [Module.finrank_eq_card_basis (basisRestrictTotalDegree σ ℂ d),
      Module.finrank_fintype_fun_eq_card]
  have him : finrank ℂ
      (LinearMap.range (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d)) =
      finrank ℚ (LinearMap.range
        (Fintype.linearCombination ℚ fun s ↦ (monomialTuple κ d s : K))) := by
    rw [range_firstJetValueMap_conjugate, range_linearCombination_monomialTuple,
      finrank_span_canonicalEmbedding_image]
  rw [hkerQ] at hrkQ
  omega

end MonomialRelations

section HeightsAndCovolume

variable {σ : Type*} {κ : σ → 𝓞 K} {d : ℕ}

/-- When `1 ≤ C₀` and every `κ j` has house at most `C₀`, every conjugate of every
degree-`≤ d` monomial in `κ` has modulus at most `C₀ ^ d`. -/
theorem norm_embedding_monomialTuple_le {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (hκ : ∀ j, house (κ j : K) ≤ C₀) (τ : K →+* ℂ)
    (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    ‖τ (monomialTuple κ d s : K)‖ ≤ C₀ ^ d := by
  simp only [coe_monomialTuple, aeval_monomial, map_one, one_mul, Finsupp.prod, map_prod,
    map_pow, norm_prod, norm_pow]
  calc ∏ j ∈ s.val.support, ‖τ (κ j : K)‖ ^ s.val j
      ≤ ∏ j ∈ s.val.support, C₀ ^ s.val j := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ ?_
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_embedding_le_house _ τ).trans (hκ j)) _
    _ = C₀ ^ (∑ j ∈ s.val.support, s.val j) := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ C₀ ^ d := pow_le_pow_right₀ hC₀ s.property

variable [Fintype σ] [DecidableEq σ]

/-- Covolume bound for `relationSubspace κ d` retaining `√|discr K|` in the denominator. -/
theorem covolume_relationSubspace_le
    (hspan : (restrictTotalDegree σ ℚ d).map (aeval (fun j ↦ (κ j : K))).toLinearMap = ⊤)
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (hκ : ∀ j, house (κ j : K) ≤ C₀) :
    ZLattice.covolume (relationSubspace κ d).intLattice ≤
      √(((d + Fintype.card σ).choose (Fintype.card σ) * (C₀ ^ d) ^ 2) ^ finrank ℚ K) /
        √|(discr K : ℝ)| := by
  have hspan' : Submodule.span ℚ (Set.range fun s ↦ (monomialTuple κ d s : K)) = ⊤ := by
    rw [← Fintype.range_linearCombination, range_linearCombination_monomialTuple, hspan]
  have h := covolume_intLattice_ker_linearCombination_le_of_norm_le hspan'
    (fun (τ : K →ₐ[ℚ] ℂ) s ↦ norm_embedding_monomialTuple_le hC₀ hκ τ.toRingHom s)
  rwa [← Nat.card_eq_fintype_card, Finsupp.card_degree_le_eq_choose] at h

/-- Discriminant-free covolume bound `covol L ≤ √(M ^ n) * C₀ ^ (n * d)` for
`relationSubspace κ d`. -/
theorem covolume_relationSubspace_le_mul_pow
    (hspan : (restrictTotalDegree σ ℚ d).map (aeval (fun j ↦ (κ j : K))).toLinearMap = ⊤)
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (hκ : ∀ j, house (κ j : K) ≤ C₀) :
    ZLattice.covolume (relationSubspace κ d).intLattice ≤
      √(((d + Fintype.card σ).choose (Fintype.card σ) : ℝ) ^ finrank ℚ K) *
        C₀ ^ (finrank ℚ K * d) := by
  have hdiscr : (1 : ℝ) ≤ √|(discr K : ℝ)| := by
    rw [Real.one_le_sqrt]
    exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  refine (covolume_relationSubspace_le hspan hC₀ hκ).trans ?_
  refine (div_le_self (Real.sqrt_nonneg _) hdiscr).trans_eq ?_
  rw [mul_pow, ← pow_mul, ← pow_mul,
    show d * (2 * finrank ℚ K) = finrank ℚ K * d * 2 by ring,
    pow_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end HeightsAndCovolume

section ShortRelations

/-- A nonzero point in `(V.intLattice : Set V.realSpan)` has Euclidean norm at least `1`. -/
private theorem one_le_norm_of_mem_intLattice_ne_zero {ι : Type*} [Fintype ι]
    {V : Submodule ℚ (ι → ℚ)} {x : V.realSpan} (hxL : x ∈ V.intLattice) (hx0 : x ≠ 0) :
    1 ≤ ‖x‖ := by
  have hx0' : (x : EuclideanSpace ℝ ι) ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
  obtain ⟨i, hi⟩ : ∃ i : ι, (x : EuclideanSpace ℝ ι) i ≠ 0 := by
    by_contra! h
    exact hx0' (PiLp.ext h)
  obtain ⟨z, hz⟩ := Submodule.mem_intLattice.1 hxL i
  have hz0 : z ≠ 0 := fun h ↦ hi (by simp [hz, h])
  have hz1 : (1 : ℝ) ≤ |(x : EuclideanSpace ℝ ι) i| := by
    rw [hz, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs hz0
  exact hz1.trans (by
    simpa [Submodule.norm_coe] using PiLp.norm_apply_le (x : EuclideanSpace ℝ ι) i)

/-- Mapping coefficients preserves bounded total degree. -/
private theorem map_mem_restrictTotalDegree {σ R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {d : ℕ} (p : restrictTotalDegree σ R d) :
    (p : MvPolynomial σ R).map f ∈ restrictTotalDegree σ S d := by
  rw [mem_restrictTotalDegree, totalDegree_eq]
  exact (Finset.sup_mono (support_map_subset f _)).trans
    ((totalDegree_eq _).symm.trans_le ((mem_restrictTotalDegree σ d _).1 p.property))

/-- Real linear independence of coefficient vectors in `EuclideanSpace ℝ` implies complex linear
independence of the corresponding polynomials in `MvPolynomial σ ℂ`. -/
private theorem linearIndependent_complex_poly_of_real {σ ι : Type*}
    {d : ℕ} (E : ι → restrictTotalDegree σ ℤ d)
    {v : ι → EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d}}
    (hv : LinearIndependent ℝ v)
    (hcoeff : ∀ i s, v i s = (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ)) :
    LinearIndependent ℂ (fun i ↦ (E i : MvPolynomial σ ℤ).map (Int.castRingHom ℂ)) := by
  rw [linearIndependent_iff]
  intro g hg
  have hval (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
      ∑ j ∈ g.support, g j * (v j s : ℂ) = 0 := by
    have h0 := congrArg (lcoeff ℂ s.val) hg
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_zero] at h0
    simpa [lcoeff_apply, coeff_map, ← Complex.ofReal_intCast, ← hcoeff] using h0
  have hre : (g.mapRange Complex.re Complex.zero_re).sum (fun j c ↦ c • v j) = 0 := by
    rw [Finsupp.sum_mapRange_index (fun j ↦ zero_smul ℝ (v j))]
    ext s
    have h0 := congrArg Complex.re (hval s)
    rw [Finsupp.sum, WithLp.ofLp_sum]
    simpa [Complex.mul_re] using h0
  have him : (g.mapRange Complex.im Complex.zero_im).sum (fun j c ↦ c • v j) = 0 := by
    rw [Finsupp.sum_mapRange_index (fun j ↦ zero_smul ℝ (v j))]
    ext s
    have h0 := congrArg Complex.im (hval s)
    rw [Finsupp.sum, WithLp.ofLp_sum]
    simpa [Complex.mul_im] using h0
  have gre := Finsupp.ext_iff.1 (linearIndependent_iff.1 hv _ hre)
  have gim := Finsupp.ext_iff.1 (linearIndependent_iff.1 hv _ him)
  ext i
  exact Complex.ext (by simpa using gre i) (by simpa using gim i)

/-- Real linear independence of coefficient vectors in `EuclideanSpace ℝ` implies real linear
independence of the polynomials in `restrictTotalDegree σ ℝ d`. -/
private theorem linearIndependent_real_poly_of_real {σ ι : Type*} [Finite σ]
    {d : ℕ} (E : ι → restrictTotalDegree σ ℤ d)
    {v : ι → EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d}}
    (hv : LinearIndependent ℝ v)
    (hcoeff : ∀ i s, (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ) = v i s) :
    LinearIndependent ℝ (fun i ↦ ((basisRestrictTotalDegree σ ℝ d).equivFun.symm
      (fun s ↦ (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ)) :
        restrictTotalDegree σ ℝ d)) := by
  let e : EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d} ≃ₗ[ℝ]
      restrictTotalDegree σ ℝ d :=
    (WithLp.linearEquiv 2 ℝ _).trans (basisRestrictTotalDegree σ ℝ d).equivFun.symm
  have heq := hv.map' e.toLinearMap e.ker
  have hfun :
      (fun i ↦ ((basisRestrictTotalDegree σ ℝ d).equivFun.symm
        (fun s ↦ (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ)) :
          restrictTotalDegree σ ℝ d)) =
        e.toLinearMap ∘ v := by
    funext i
    exact congrArg (basisRestrictTotalDegree σ ℝ d).equivFun.symm (funext fun s ↦ hcoeff i s)
  exact hfun ▸ heq

private theorem product_norm_minkowski_bound {ι : Type*} [Fintype ι]
    (V : Submodule ℚ (ι → ℚ)) (a : Fin (finrank ℝ V.realSpan) → V.realSpan)
    (ha_norm : ∀ j, ‖a j‖ =
      ZLattice.successiveMin V.intLattice (ConvexBody.closedBall 0 1 zero_le_one) j) :
    ∏ j, ‖a j‖ ≤
      (finrank ℝ V.realSpan : ℝ) ^ ((finrank ℝ V.realSpan : ℝ) / 2) *
        ZLattice.covolume V.intLattice := by
  set ℓ := finrank ℝ V.realSpan
  simp_rw [ha_norm]
  have hmink := ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume V.intLattice
    volume (K := ConvexBody.closedBall 0 1 zero_le_one)
    (fun _ hx ↦ by simpa [ConvexBody.coe_closedBall, Metric.mem_closedBall, norm_neg] using hx)
  have hball := two_div_sqrt_pow_le_volumeReal_closedBall (0 : V.realSpan) zero_le_one
  rw [mul_one] at hball
  have hpow_le :
      (∏ j, ZLattice.successiveMin V.intLattice (ConvexBody.closedBall 0 1 zero_le_one) j) *
          (2 / √(ℓ : ℝ)) ^ ℓ ≤
        2 ^ ℓ * ZLattice.covolume V.intLattice := by
    have hnn : 0 ≤
        ∏ j, ZLattice.successiveMin V.intLattice (ConvexBody.closedBall 0 1 zero_le_one) j :=
      Finset.prod_nonneg fun j _ ↦ ZLattice.successiveMin_nonneg _ _ j
    exact (mul_le_mul_of_nonneg_left hball hnn).trans (by simpa [ℓ] using hmink)
  rw [div_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((ℓ : ℝ) ^ (1 / 2 : ℝ)) ℓ,
    ← Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_eq_div] at hpow_le
  have hl : (0 : ℝ) < (ℓ : ℝ) ^ ((ℓ : ℝ) / 2) := by
    rcases eq_or_ne ℓ 0 with h0 | hpos
    · simp [h0]
    · exact Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hpos)) _
  have h2 : (0 : ℝ) < 2 ^ ℓ := pow_pos two_pos ℓ
  rw [mul_div_assoc', div_le_iff₀ hl, mul_right_comm] at hpow_le
  exact (mul_le_mul_iff_left₀ h2).1 (by linarith)

/-- Short linearly independent integral vectors of `V` realizing Minkowski's second theorem. -/
private theorem exists_lattice_short_vectors {ι : Type*} [Fintype ι]
    (V : Submodule ℚ (ι → ℚ)) :
    let ℓ := finrank ℝ V.realSpan
    ∃ z : Fin ℓ → V.intPoints,
      LinearIndependent ℝ (fun i ↦ (WithLp.toLp 2 (fun s ↦ ((z i).val s : ℝ)) :
        EuclideanSpace ℝ ι)) ∧
      (∀ i, 1 ≤ ‖(WithLp.toLp 2 (fun s ↦ ((z i).val s : ℝ)) :
        EuclideanSpace ℝ ι)‖) ∧
      Monotone (fun i ↦ ‖(WithLp.toLp 2 (fun s ↦ ((z i).val s : ℝ)) :
        EuclideanSpace ℝ ι)‖) ∧
      ∏ i, ‖(WithLp.toLp 2 (fun s ↦ ((z i).val s : ℝ)) : EuclideanSpace ℝ ι)‖ ≤
        (ℓ : ℝ) ^ ((ℓ : ℝ) / 2) * ZLattice.covolume V.intLattice := by
  set ℓ := finrank ℝ V.realSpan
  let U : ConvexBody V.realSpan := ConvexBody.closedBall 0 1 zero_le_one
  have hU0 : (0 : V.realSpan) ∈ interior (U : Set V.realSpan) :=
    ConvexBody.mem_interior_closedBall_self 0 zero_lt_one
  obtain ⟨a, ha, haL⟩ :=
    ZLattice.exists_linearIndependent_gauge_eq_successiveMin V.intLattice hU0
  have ha_norm (j : Fin ℓ) : ‖a j‖ = ZLattice.successiveMin V.intLattice U j := by
    rw [← (haL j).2, ConvexBody.coe_closedBall, gauge_closedBall zero_le_one, div_one]
  let z : Fin ℓ → V.intPoints := fun i ↦ V.intPointsEquivIntLattice.symm ⟨a i, (haL i).1⟩
  have hLp (i : Fin ℓ) :
      (WithLp.toLp 2 (fun s ↦ ((z i).val s : ℝ)) : EuclideanSpace ℝ ι) =
        (a i : EuclideanSpace ℝ ι) := by
    ext s
    exact Submodule.intCast_intPointsEquivIntLattice_symm_apply V ⟨a i, (haL i).1⟩ s
  have hnorm (i : Fin ℓ) :
      ‖(WithLp.toLp 2 (fun s ↦ ((z i).val s : ℝ)) :
        EuclideanSpace ℝ ι)‖ = ‖a i‖ := by
    rw [hLp i, Submodule.norm_coe]
  refine ⟨z, ?_, fun i ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · have ha' := ha.map' V.realSpan.subtype (Submodule.ker_subtype _)
    convert ha' using 1
    exact funext hLp
  · rw [hnorm]
    exact one_le_norm_of_mem_intLattice_ne_zero (haL i).1 (ha.ne_zero i)
  · simp only [hnorm, ha_norm]
    exact ZLattice.monotone_successiveMin V.intLattice hU0 hij
  · simp_rw [hnorm]
    exact product_norm_minkowski_bound V a ha_norm

/-- **Minkowski's second theorem for polynomial relations.** Given an integral tuple
`κ : σ → 𝓞 K` whose degree-`≤ d` rational values cover `K`, there exist
`ℓ = M - [K : ℚ]` linearly independent integer polynomials `E 0, …, E (ℓ - 1)` of total
degree at most `d`, vanishing at `κ`, with nondecreasing coefficient Euclidean norms `≥ 1` whose
product is at most `ℓ ^ (ℓ / 2) * √(M ^ n) * C₀ ^ (n * d)`, and whose complexifications are
`ℂ`-linearly independent. -/
theorem exists_linearIndependent_short_relations {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → 𝓞 K) (d : ℕ)
    (hspan : (restrictTotalDegree σ ℚ d).map (aeval (fun j ↦ (κ j : K))).toLinearMap = ⊤)
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (hκ : ∀ j, house (κ j : K) ≤ C₀) :
    let M := (d + Fintype.card σ).choose (Fintype.card σ)
    let n := finrank ℚ K
    let ℓ := M - n
    ∃ E : Fin ℓ → restrictTotalDegree σ ℤ d,
      LinearIndependent ℝ (fun i ↦ ((basisRestrictTotalDegree σ ℝ d).equivFun.symm
        (fun s ↦ (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ)) :
          restrictTotalDegree σ ℝ d)) ∧
      (∀ i, aeval (fun j ↦ (κ j : K)) (E i : MvPolynomial σ ℤ) = 0) ∧
      (∀ i, 1 ≤ ‖(WithLp.toLp 2 (fun s : {s : σ →₀ ℕ // s.degree ≤ d} ↦
        (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ)) :
          EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d})‖) ∧
      Monotone (fun i ↦ ‖(WithLp.toLp 2 (fun s : {s : σ →₀ ℕ // s.degree ≤ d} ↦
        (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ)) :
          EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d})‖) ∧
      ∏ i, ‖(WithLp.toLp 2 (fun s : {s : σ →₀ ℕ // s.degree ≤ d} ↦
        (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ)) :
          EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d})‖ ≤
          (ℓ : ℝ) ^ ((ℓ : ℝ) / 2) * √(M ^ n : ℝ) * C₀ ^ (n * d) ∧
      LinearIndependent ℂ (fun i ↦ (E i : MvPolynomial σ ℤ).map (Int.castRingHom ℂ)) := by
  set V := relationSubspace κ d
  set M := (d + Fintype.card σ).choose (Fintype.card σ)
  set n := finrank ℚ K
  set ℓ := M - n
  have hfin : finrank ℝ V.realSpan = ℓ := by
    rw [Submodule.finrank_realSpan, finrank_relationSubspace_of_map_eq_top κ d hspan]
  let e : Fin ℓ ≃ Fin (finrank ℝ V.realSpan) := finCongr hfin.symm
  obtain ⟨z, hz_li, hz1, hzmono, hzprod⟩ := exists_lattice_short_vectors V
  let E : Fin ℓ → restrictTotalDegree σ ℤ d :=
    fun i ↦ (basisRestrictTotalDegree σ ℤ d).equivFun.symm (z (e i)).val
  have hcoeff (i : Fin ℓ) (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
      (E i : MvPolynomial σ ℤ).coeff s.val = (z (e i)).val s := by
    rw [← basisRestrictTotalDegree_repr_apply, ← Basis.equivFun_apply]
    exact congrFun ((basisRestrictTotalDegree σ ℤ d).equivFun.apply_symm_apply (z (e i)).val) s
  have hLp (i : Fin ℓ) :
      (WithLp.toLp 2 (fun s : {s : σ →₀ ℕ // s.degree ≤ d} ↦
          (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ)) :
          EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d}) =
        (WithLp.toLp 2 (fun s ↦ ((z (e i)).val s : ℝ)) :
          EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d}) := by
    ext s
    exact congrArg Int.cast (hcoeff i s)
  have hcoeff' (i : Fin ℓ) (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
      (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ) =
        (WithLp.toLp 2 (fun t ↦ ((z (e i)).val t : ℝ)) :
          EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d}) s :=
    congrArg Int.cast (hcoeff i s)
  have hz_li' : LinearIndependent ℝ (fun i ↦
      (WithLp.toLp 2 (fun s ↦ ((z (e i)).val s : ℝ)) :
        EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d})) := hz_li.comp e e.injective
  have hcov := covolume_relationSubspace_le_mul_pow hspan hC₀ hκ
  refine ⟨E, linearIndependent_real_poly_of_real E hz_li' hcoeff',
    fun i ↦ (mem_relationSubspace_intPoints_iff κ d _).1 (z (e i)).property,
    fun i ↦ by rw [hLp]; exact hz1 _,
    fun i j hij ↦ by simp only [hLp]; exact hzmono (show (e i : ℕ) ≤ (e j : ℕ) from hij),
    ?_, linearIndependent_complex_poly_of_real E hz_li' (fun i s ↦ (hcoeff' i s).symm)⟩
  simp_rw [hLp]
  rw [e.prod_comp (fun j ↦ ‖(WithLp.toLp 2 (fun s ↦ ((z j).val s : ℝ)) :
    EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d})‖)]
  refine hzprod.trans ?_
  rw [hfin, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcov (by positivity)

/-- For `ℓ` nondecreasing reals `≥ 1` whose product is at most
`ℓ ^ (ℓ / 2) * √(M ^ n) * C₀ ^ (n * d)`, the first `ℓ + 1 - n` terms are at most
`ℓ ^ (ℓ / (2 * n)) * √M * C₀ ^ d`. -/
private theorem ordered_term_le_of_prod_le {n ℓ M d : ℕ} {C₀ : ℝ} (hn : 0 < n)
    (hC₀ : 0 ≤ C₀) {ν : Fin ℓ → ℝ} (h1 : ∀ i, 1 ≤ ν i) (hmono : Monotone ν)
    (hprod : ∏ i, ν i ≤ (ℓ : ℝ) ^ ((ℓ : ℝ) / 2) * √(M ^ n : ℝ) * C₀ ^ (n * d))
    {i : Fin ℓ} (hi : (i : ℕ) < ℓ + 1 - n) :
    ν i ≤ (ℓ : ℝ) ^ ((ℓ : ℝ) / (2 * (n : ℝ))) * √(M : ℝ) * C₀ ^ d := by
  set B := (ℓ : ℝ) ^ ((ℓ : ℝ) / (2 * (n : ℝ))) * √(M : ℝ) * C₀ ^ d
  have hi_le : n ≤ ℓ - (i : ℕ) := by omega
  have hpow : ν i ^ n ≤ B ^ n := by
    calc ν i ^ n
        ≤ ν i ^ (ℓ - (i : ℕ)) := pow_le_pow_right₀ (h1 i) hi_le
      _ ≤ ∏ j, ν j := Fin.pow_sub_le_prod_of_monotone h1 hmono i
      _ ≤ (ℓ : ℝ) ^ ((ℓ : ℝ) / 2) * √(M ^ n : ℝ) * C₀ ^ (n * d) := hprod
      _ = B ^ n := by
          have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
          have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
          have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
          have hdiv : (ℓ : ℝ) / (2 * (n : ℝ)) * (n : ℝ) = (ℓ : ℝ) / 2 := by field_simp
          have hsqrt : √((M : ℝ) ^ n) = (√(M : ℝ)) ^ n := by
            rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((M : ℝ) ^ _),
              ← Real.rpow_natCast (M : ℝ), ← Real.rpow_mul hM0, ← Real.rpow_mul hM0,
              mul_comm (n : ℝ)]
          rw [show B ^ n = ((ℓ : ℝ) ^ ((ℓ : ℝ) / (2 * (n : ℝ)))) ^ n *
              (√(M : ℝ)) ^ n * (C₀ ^ d) ^ n by simp only [B, mul_pow]]
          rw [← Real.rpow_natCast ((ℓ : ℝ) ^ _), ← Real.rpow_mul hℓ0, hdiv, hsqrt,
            ← pow_mul, mul_comm d n]
  exact le_of_pow_le_pow_left₀ hn.ne' (by positivity) hpow

/-- Keeping the shortest `k = ℓ + 1 - n` independent relation polynomials bounds each
Euclidean coefficient norm and each individual coefficient modulus by
`ℓ ^ (ℓ / (2 * n)) * √M * C₀ ^ d`. -/
theorem exists_truncated_short_relations {σ : Type*} [Fintype σ]
    (κ : σ → 𝓞 K) (d : ℕ)
    (hspan : (restrictTotalDegree σ ℚ d).map (aeval (fun j ↦ (κ j : K))).toLinearMap = ⊤)
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (hκ : ∀ j, house (κ j : K) ≤ C₀) :
    let M := (d + Fintype.card σ).choose (Fintype.card σ)
    let n := finrank ℚ K
    let ℓ := M - n
    let k := ℓ + 1 - n
    let B := (ℓ : ℝ) ^ ((ℓ : ℝ) / (2 * (n : ℝ))) * √(M : ℝ) * C₀ ^ d
    ∃ E : Fin k → restrictTotalDegree σ ℤ d,
      (∀ i, aeval (fun j ↦ (κ j : K)) (E i : MvPolynomial σ ℤ) = 0) ∧
      (∀ i s, |((E i : MvPolynomial σ ℤ).coeff s : ℝ)| ≤ B) ∧
      LinearIndependent ℂ (fun i ↦ (E i : MvPolynomial σ ℤ).map (Int.castRingHom ℂ)) := by
  classical
  set M := (d + Fintype.card σ).choose (Fintype.card σ)
  set n := finrank ℚ K
  set ℓ := M - n
  set k := ℓ + 1 - n
  have hn : 0 < n := finrank_pos
  have hkℓ : k ≤ ℓ := by omega
  obtain ⟨E, -, hE0, hE1, hEmono, hEprod, hEli⟩ :=
    exists_linearIndependent_short_relations κ d hspan hC₀ hκ
  let ν : Fin ℓ → ℝ := fun i ↦
    ‖(WithLp.toLp 2 (fun s : {s : σ →₀ ℕ // s.degree ≤ d} ↦
      (((E i : MvPolynomial σ ℤ).coeff s.val : ℤ) : ℝ)) :
        EuclideanSpace ℝ {s : σ →₀ ℕ // s.degree ≤ d})‖
  have hB (i : Fin k) :
      ν (Fin.castLE hkℓ i) ≤
        (ℓ : ℝ) ^ ((ℓ : ℝ) / (2 * (n : ℝ))) * √(M : ℝ) * C₀ ^ d :=
    ordered_term_le_of_prod_le hn (zero_le_one.trans hC₀) hE1 hEmono hEprod i.isLt
  refine ⟨fun i ↦ E (Fin.castLE hkℓ i), fun i ↦ hE0 _, fun i s ↦ ?_,
    hEli.comp _ (Fin.castLE_injective hkℓ)⟩
  by_cases hs : s.degree ≤ d
  · have h1 : |(((E (Fin.castLE hkℓ i) : MvPolynomial σ ℤ).coeff s : ℤ) : ℝ)| ≤
        ν (Fin.castLE hkℓ i) := by
      simpa [ν, Real.norm_eq_abs] using
        PiLp.norm_apply_le (WithLp.toLp 2 (fun t : {t : σ →₀ ℕ // t.degree ≤ d} ↦
          (((E (Fin.castLE hkℓ i) : MvPolynomial σ ℤ).coeff t.val : ℤ) : ℝ)) :
          EuclideanSpace ℝ {t : σ →₀ ℕ // t.degree ≤ d}) ⟨s, hs⟩
    exact h1.trans (hB i)
  · have hz := coeff_eq_zero_of_mem_restrictTotalDegree
      (E (Fin.castLE hkℓ i)).property (not_le.1 hs)
    simp only [hz, Int.cast_zero, abs_zero]
    positivity

end ShortRelations

section JacobianExtraction

private theorem ringHom_aeval_int {σ K R : Type*} [CommRing K] [CommRing R] (τ : K →+* R)
    (κ : σ → K) (p : MvPolynomial σ ℤ) :
    τ (aeval κ p) = eval (fun j ↦ τ (κ j)) (p.map (Int.castRingHom R)) := by
  rw [aeval_def, algebraMap_int_eq, hom_eval₂, eval_map,
    Subsingleton.elim (τ.comp (Int.castRingHom K)) (Int.castRingHom R)]

/-- When the conjugate points of `κ` are well poised in degree `d`, the derivative map
`TauCeti.firstJetDerivMap` restricts to a surjection onto at least one conjugate gradient block
`ℂ^σ` from the complex span of the retained `k = ℓ + 1 - n` relations. -/
private theorem firstJetDerivMap_conjugate_proj_surjective_of_wellPoised
    {σ : Type*} [Fintype σ] {κ : σ → 𝓞 K} {d : ℕ}
    (hWP : WellPoised (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d)
    {v : Fin
        ((d + Fintype.card σ).choose (Fintype.card σ) - finrank ℚ K + 1 - finrank ℚ K) →
      LinearMap.ker (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d)}
    (hv : LinearIndependent ℂ (fun i ↦ (v i : restrictTotalDegree σ ℂ d))) :
    ∃ τ₀ : K →+* ℂ, Function.Surjective
      ((LinearMap.proj τ₀ ∘ₗ
        firstJetDerivMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d).domRestrict
          (Submodule.span ℂ (Set.range v))) := by
  have hderiv : Function.Surjective
      (firstJetDerivMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d) :=
    (firstJetMap_surjective_iff.1 (wellPoised_iff.1 hWP)).2
  have hspan :
      (restrictTotalDegree σ ℚ d).map (aeval (fun j ↦ (κ j : K))).toLinearMap = ⊤ :=
    map_aeval_restrictTotalDegree_eq_top_of_wellPoised hWP
  set W : Submodule ℂ
      (LinearMap.ker (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d)) :=
    Submodule.span ℂ (Set.range v)
  have hv' : LinearIndependent ℂ v := LinearIndependent.of_comp (LinearMap.ker _).subtype hv
  have hW : finrank ℂ W =
      (d + Fintype.card σ).choose (Fintype.card σ) - finrank ℚ K + 1 - finrank ℚ K := by
    rw [finrank_span_eq_card hv', Fintype.card_fin]
  have hker : finrank ℂ
      (LinearMap.ker (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d)) =
      (d + Fintype.card σ).choose (Fintype.card σ) - finrank ℚ K := by
    classical
    rw [finrank_ker_firstJetValueMap_conjugate, finrank_relationSubspace_of_map_eq_top κ d hspan]
  refine LinearMap.exists_surjective_proj_comp_domRestrict (𝕜 := ℂ)
    (E := LinearMap.ker (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d))
    hderiv W ?_
  rw [hW, hker, NumberField.Embeddings.card K ℂ]
  omega

omit [NumberField K] in
/-- If `proj τ₀ ∘ₗ firstJetDerivMap` restricts to a surjection on the span of `v`, then the
transpose of the conjugate derivative matrix of `v` has surjective `mulVec`. -/
private theorem derivMatrix_transpose_mulVec_surjective
    {σ : Type*} {κ : σ → 𝓞 K} {d k : ℕ}
    (E : Fin k → restrictTotalDegree σ ℤ d) (τ₀ : K →+* ℂ)
    (v : Fin k → LinearMap.ker (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d))
    (hv : ∀ i, ((v i : restrictTotalDegree σ ℂ d) : MvPolynomial σ ℂ) =
      (E i : MvPolynomial σ ℤ).map (Int.castRingHom ℂ))
    (hτ₀ : Function.Surjective
      ((LinearMap.proj τ₀ ∘ₗ
        firstJetDerivMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d).domRestrict
          (Submodule.span ℂ (Set.range v)))) :
    ((Matrix.of fun i j ↦ aeval (fun j ↦ (κ j : K))
      (pderiv j (E i : MvPolynomial σ ℤ))).map τ₀)ᵀ.mulVec.Surjective := fun y ↦ by
  have hAC (i : Fin k) (j : σ) :
      ((Matrix.of fun i j ↦ aeval (fun j ↦ (κ j : K))
        (pderiv j (E i : MvPolynomial σ ℤ))).map τ₀) i j =
        (LinearMap.proj τ₀ ∘ₗ
          firstJetDerivMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d) (v i) j := by
    rw [Matrix.map_apply, Matrix.of_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      firstJetDerivMap_apply, hv i, pderiv_map]
    exact ringHom_aeval_int τ₀ (fun j ↦ (κ j : K)) (pderiv j (E i : MvPolynomial σ ℤ))
  obtain ⟨w, hw⟩ := hτ₀ y
  have hex : ∃ x, ((Matrix.of fun i j ↦ aeval (fun j ↦ (κ j : K))
        (pderiv j (E i : MvPolynomial σ ℤ))).map τ₀)ᵀ *ᵥ x =
      (LinearMap.proj τ₀ ∘ₗ
        firstJetDerivMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d) w.val := by
    refine Submodule.span_induction (p := fun u _ ↦ ∃ x,
        ((Matrix.of fun i j ↦ aeval (fun j ↦ (κ j : K))
          (pderiv j (E i : MvPolynomial σ ℤ))).map τ₀)ᵀ *ᵥ x =
        (LinearMap.proj τ₀ ∘ₗ firstJetDerivMap _ d) u) ?_ ⟨0, by simp⟩ ?_ ?_ w.property
    · rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, funext fun j ↦ ?_⟩
      simp [← hAC]
    · rintro u₁ u₂ - - ⟨x, hx⟩ ⟨z, hz⟩
      exact ⟨x + z, by rw [Matrix.mulVec_add, hx, hz, map_add]⟩
    · rintro c u - ⟨x, hx⟩
      exact ⟨c • x, by rw [Matrix.mulVec_smul, hx, map_smul]⟩
  obtain ⟨x, hx⟩ := hex
  exact ⟨x, hx.trans (by simpa [LinearMap.domRestrict_apply] using hw)⟩

/-- **Extracting a bounded system with nonzero Jacobian at `κ`.** If the conjugate points of
`κ : σ → 𝓞 K` are well poised in degree `d` and every `κ j` has house at most `C₀ ≥ 1`,
then there exist `#σ` integer polynomials `E : σ → MvPolynomial σ ℤ` of total degree at most
`d`, all vanishing at `κ`, with every coefficient bounded by
`ℓ ^ (ℓ / (2 * n)) * √M * C₀ ^ d` and such that `TauCeti.jacobian E` does not vanish at
`κ`. -/
theorem exists_jacobian_ne_zero_equations_of_wellPoised {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → 𝓞 K) (d : ℕ)
    (hWP : WellPoised (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d)
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (hκ : ∀ j, house (κ j : K) ≤ C₀) :
    let M := (d + Fintype.card σ).choose (Fintype.card σ)
    let n := finrank ℚ K
    let ℓ := M - n
    let B := (ℓ : ℝ) ^ ((ℓ : ℝ) / (2 * (n : ℝ))) * √(M : ℝ) * C₀ ^ d
    ∃ E : σ → MvPolynomial σ ℤ,
      (∀ i, (E i).totalDegree ≤ d) ∧
      (∀ i s, |((E i).coeff s : ℝ)| ≤ B) ∧
      (∀ i, aeval (fun j ↦ (κ j : K)) (E i) = 0) ∧
      aeval (fun j ↦ (κ j : K)) (TauCeti.jacobian E) ≠ 0 := by
  have hspan :
      (restrictTotalDegree σ ℚ d).map (aeval (fun j ↦ (κ j : K))).toLinearMap = ⊤ :=
    map_aeval_restrictTotalDegree_eq_top_of_wellPoised hWP
  obtain ⟨E, hE0, hEcoeff, hEli⟩ := exists_truncated_short_relations κ d hspan hC₀ hκ
  let v : Fin
      ((d + Fintype.card σ).choose (Fintype.card σ) - finrank ℚ K + 1 - finrank ℚ K) →
      LinearMap.ker (firstJetValueMap (fun (τ : K →+* ℂ) j ↦ τ (κ j : K)) d) :=
    fun i ↦ ⟨⟨(E i : MvPolynomial σ ℤ).map (Int.castRingHom ℂ),
        map_mem_restrictTotalDegree _ (E i)⟩,
      (mem_ker_firstJetValueMap _ _).2 fun τ ↦ by
        rw [← ringHom_aeval_int, hE0 i, map_zero]⟩
  have hli : LinearIndependent ℂ fun i ↦ (v i : restrictTotalDegree σ ℂ d) :=
    LinearIndependent.of_comp (restrictTotalDegree σ ℂ d).subtype hEli
  obtain ⟨τ₀, hτ₀⟩ := firstJetDerivMap_conjugate_proj_surjective_of_wellPoised hWP hli
  let A_K : Matrix _ σ K :=
    Matrix.of fun i j ↦ aeval (fun j ↦ (κ j : K)) (pderiv j (E i : MvPolynomial σ ℤ))
  have hsurj := derivMatrix_transpose_mulVec_surjective E τ₀ v (fun _ ↦ rfl) hτ₀
  have hrank : Fintype.card σ ≤ A_K.rank := by
    rw [← Matrix.rank_map A_K τ₀, ← Matrix.rank_transpose,
      Matrix.mulVec_surjective_iff_rank_eq_card.1 hsurj]
  obtain ⟨rowEmb, colEmb, hdet⟩ := Matrix.le_rank_iff_exists_det_submatrix_ne_zero.1 hrank
  let e : Fin (Fintype.card σ) ≃ σ :=
    Equiv.ofBijective colEmb ((Fintype.bijective_iff_injective_and_card colEmb).2
      ⟨colEmb.injective, Fintype.card_fin _⟩)
  refine ⟨fun s ↦ (E (rowEmb (e.symm s)) : MvPolynomial σ ℤ),
    fun s ↦ (mem_restrictTotalDegree σ d _).1 (E _).property,
    fun s t ↦ hEcoeff _ t, fun s ↦ hE0 _, ?_⟩
  rw [aeval_jacobian]
  have hmat : (Matrix.of fun s s' ↦ aeval (fun j ↦ (κ j : K))
      (pderiv s' (E (rowEmb (e.symm s)) : MvPolynomial σ ℤ))) =
      (A_K.submatrix rowEmb colEmb).reindex e e := by
    ext s s'
    have hcol : colEmb (e.symm s') = s' := e.apply_symm_apply s'
    simp [A_K, hcol]
  rw [hmat, Matrix.det_reindex_self]
  exact hdet

end JacobianExtraction

end TauCeti.NumberField
