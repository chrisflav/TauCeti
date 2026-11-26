/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Deformation.Cocycle
public import TauCeti.RingTheory.FormalGroup.Deformation.LubinTate
-- Proof-only: multivariate and univariate substitution lemmas.
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Partial-derivative symmetric 2-cocycles of formal group deformations

Given a commutative formal group law `Γ` over `R⟦t₁, …, t_{h-1}⟧` reducing to `F₀` over `k`
along `ρ.comp constantCoeff`, evaluating along the dual-number map `MvPowerSeries.evalDual ρ i`
produces the partial-derivative symmetric 2-cocycle `FormalGroup.derivCocycle Γ ρ F₀ i` over `k`.
For the generic Lubin–Tate law `F.lubinTateLaw hp h`, `FormalGroup.derivCocycle` vanishes below
degree `p ^ (i + 1)` and has degree-`p ^ (i + 1)` homogeneous component
`lazardCocycle (p ^ (i + 1)) k`.

## Main definitions

* `FormalGroup.coeffPartial`: extracts the linear `X i`-coefficient along `ρ : R →+* k`.
* `FormalGroup.derivCocycle`: the partial-derivative cocycle of a deformation along parameter `i`.

## Main results

* `FormalGroup.isSymmetricCocycle_derivCocycle`: `derivCocycle` is a symmetric 2-cocycle of `F₀`.
* `FormalGroup.le_order_derivCocycle_lubinTateLaw`: `derivCocycle (F.lubinTateLaw hp h)` has order
  at least `p ^ (i + 1)`.
* `FormalGroup.homogeneousComponent_derivCocycle_lubinTateLaw`: its degree-`p ^ (i + 1)`
  homogeneous component is `lazardCocycle (p ^ (i + 1)) k`.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1–§2.
-/

public section

noncomputable section

namespace FormalGroup

open MvPowerSeries TauCeti

section DerivCocycle

variable {σ R k : Type*} [CommRing R] [CommRing k]

/-- Extract the coefficient of `X i` from every `(Fin 2)`-monomial coefficient of a two-variable
series over `R⟦σ⟧`, reducing along `ρ : R →+* k`. -/
@[expose]
noncomputable def coeffPartial (ρ : R →+* k) (i : σ)
    (f : MvPowerSeries (Fin 2) (MvPowerSeries σ R)) : MvPowerSeries (Fin 2) k :=
  fun d ↦ ρ (MvPowerSeries.coeff (Finsupp.single i 1) (coeff d f))

/-- Coefficients of `coeffPartial ρ i f` are `ρ` applied to the `X i`-coefficient of `coeff d f`. -/
@[simp]
theorem coeff_coeffPartial (ρ : R →+* k) (i : σ)
    (f : MvPowerSeries (Fin 2) (MvPowerSeries σ R)) (d : Fin 2 →₀ ℕ) :
    coeff d (coeffPartial ρ i f) = ρ (MvPowerSeries.coeff (Finsupp.single i 1) (coeff d f)) :=
  rfl

/-- **The partial-derivative cocycle** of a deformation `Γ` over `R⟦t₁, …, t_{h-1}⟧` reducing to
`F₀` along `ρ.comp constantCoeff`, in the direction of the parameter `i : σ`. -/
@[expose]
noncomputable def derivCocycle (Γ : FormalGroup (MvPowerSeries σ R)) (ρ : R →+* k)
    (F₀ : FormalGroup k) (i : σ) : MvPowerSeries (Fin 2) k :=
  PowerSeries.subst F₀.toPowerSeries F₀.invariantDifferential *
    coeffPartial ρ i Γ.toPowerSeries

/-- The partial-derivative cocycle has zero constant term. -/
@[simp]
theorem constantCoeff_derivCocycle (Γ : FormalGroup (MvPowerSeries σ R)) (ρ : R →+* k)
    (F₀ : FormalGroup k) (i : σ) :
    constantCoeff (derivCocycle Γ ρ F₀ i) = 0 := by
  rw [derivCocycle, map_mul, ← coeff_zero_eq_constantCoeff_apply (coeffPartial ρ i Γ.toPowerSeries),
    coeff_coeffPartial, coeff_zero_eq_constantCoeff_apply, Γ.zero_constantCoeff]
  simp

private theorem isSymmetricCocycle_eps_smul_derivCocycle (Γ : FormalGroup (MvPowerSeries σ R))
    [Γ.IsComm] (ρ : R →+* k) (F₀ : FormalGroup k) [F₀.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀) (i : σ) :
    (F₀.map (TrivSqZeroExt.inlHom k k)).IsSymmetricCocycle
      ((DualNumber.eps : DualNumber k) •
        MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (derivCocycle Γ ρ F₀ i)) := by
  classical
  let ι : k →+* DualNumber k := TrivSqZeroExt.inlHom k k
  let π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  have hker : RingHom.ker π ^ 2 = ⊥ := by
    rw [← le_bot_iff, sq, Ideal.mul_le]
    intro x hx y hy
    have hxf : x.fst = 0 := by simpa [π] using hx
    have hyf : y.fst = 0 := by simpa [π] using hy
    rw [Ideal.mem_bot]
    ext <;> simp [hxf, hyf]
  have hcomp : (Γ.map (evalDual ρ i)).map π = F₀ := by
    rw [map_comp, fstHom_comp_evalDual, hΓ]
  have hF₀ : (F₀.map ι).map π = F₀ := by
    rw [map_comp]
    convert F₀.map_id
    ext x
    simp [ι, π]
  have hΔmem : ∀ d, coeff d ((Γ.map (evalDual ρ i)).toPowerSeries - (F₀.map ι).toPowerSeries) ∈
      RingHom.ker π := fun d ↦ by
    rw [RingHom.mem_ker, map_sub (coeff d), map_sub π, ← coeff_map, ← coeff_map,
      ← map_toPowerSeries, ← map_toPowerSeries, hcomp, hF₀, sub_self]
  have hsymm := isSymmetricCocycle_invariantDifferential_mul_sub
    (Γ.map (evalDual ρ i)) (F₀.map ι) hker hΔmem
  have hΔeq : (Γ.map (evalDual ρ i)).toPowerSeries - (F₀.map ι).toPowerSeries =
      C (DualNumber.eps : DualNumber k) *
        MvPowerSeries.map ι (coeffPartial ρ i Γ.toPowerSeries) := by
    ext d
    · have hfst : ρ (constantCoeff (coeff d Γ.toPowerSeries)) = coeff d F₀.toPowerSeries := by
        simp [← hΓ, map_toPowerSeries, coeff_map]
      simp [ι, map_toPowerSeries, coeff_map, hfst]
    · simp [ι, map_toPowerSeries, coeff_map]
  have hωeq : PowerSeries.subst (F₀.map ι).toPowerSeries (F₀.map ι).invariantDifferential =
      MvPowerSeries.map ι (PowerSeries.subst F₀.toPowerSeries F₀.invariantDifferential) := by
    rw [map_toPowerSeries, ← F₀.map_invariantDifferential ι,
      PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero F₀.zero_constantCoeff)]
  have hΨeq :
      PowerSeries.subst (F₀.map ι).toPowerSeries (F₀.map ι).invariantDifferential *
          ((Γ.map (evalDual ρ i)).toPowerSeries - (F₀.map ι).toPowerSeries) =
        (DualNumber.eps : DualNumber k) • MvPowerSeries.map ι (derivCocycle Γ ρ F₀ i) := by
    rw [hωeq, hΔeq, ← mul_assoc, mul_comm _ (C (DualNumber.eps : DualNumber k)), mul_assoc,
      ← map_mul (MvPowerSeries.map ι), ← smul_eq_C_mul]
    rfl
  rwa [hΨeq] at hsymm

private theorem derivCocycle_swap_eq (Φ : MvPowerSeries (Fin 2) k)
    (hsw : ((DualNumber.eps : DualNumber k) •
      MvPowerSeries.map (TrivSqZeroExt.inlHom k k) Φ).subst ![X 1, X 0] =
        (DualNumber.eps : DualNumber k) • MvPowerSeries.map (TrivSqZeroExt.inlHom k k) Φ) :
    Φ.subst ![X 1, X 0] = Φ := by
  classical
  let ι : k →+* DualNumber k := TrivSqZeroExt.inlHom k k
  have harg : (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) (DualNumber k)) =
      fun j ↦ MvPowerSeries.map ι ((![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) k) j) := by
    funext j; fin_cases j <;> simp
  rw [harg, subst_smul ((HasSubst.X_X :
      HasSubst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) k)).map ι)] at hsw
  dsimp only [ι] at hsw
  rw [← MvPowerSeries.map_subst (a := (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) k))
    HasSubst.X_X] at hsw
  ext d
  have hcoeff := congrArg (fun f ↦ TrivSqZeroExt.snd (coeff d f)) hsw
  simpa [ι] using hcoeff

private theorem derivCocycle_cocycle_eq (F₀ : FormalGroup k) (Φ : MvPowerSeries (Fin 2) k)
    (hcoc :
      ((DualNumber.eps : DualNumber k) •
          MvPowerSeries.map (TrivSqZeroExt.inlHom k k) Φ).subst
          (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) (DualNumber k)) +
        ((DualNumber.eps : DualNumber k) •
            MvPowerSeries.map (TrivSqZeroExt.inlHom k k) Φ).subst
          ![(F₀.map (TrivSqZeroExt.inlHom k k)).toPowerSeries.subst ![X 0, X 1], X 2] =
      ((DualNumber.eps : DualNumber k) •
          MvPowerSeries.map (TrivSqZeroExt.inlHom k k) Φ).subst
          ![X 0, (F₀.map (TrivSqZeroExt.inlHom k k)).toPowerSeries.subst ![X 1, X 2]] +
        ((DualNumber.eps : DualNumber k) •
          MvPowerSeries.map (TrivSqZeroExt.inlHom k k) Φ).subst
          (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) (DualNumber k))) :
    Φ.subst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) k) +
        Φ.subst ![F₀.toPowerSeries.subst ![X 0, X 1], X 2] =
      Φ.subst ![X 0, F₀.toPowerSeries.subst ![X 1, X 2]] +
        Φ.subst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) k) := by
  classical
  let ι : k →+* DualNumber k := TrivSqZeroExt.inlHom k k
  have hsubst_pull : ∀ (a : Fin 2 → MvPowerSeries (Fin 3) k), HasSubst a →
      ((DualNumber.eps : DualNumber k) • MvPowerSeries.map ι Φ).subst
          (fun j ↦ MvPowerSeries.map ι (a j)) =
        (DualNumber.eps : DualNumber k) • MvPowerSeries.map ι (Φ.subst a) := fun a ha ↦ by
    rw [subst_smul (ha.map ι), ← MvPowerSeries.map_subst ha]
  have h01 : (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) (DualNumber k)) =
      fun j ↦ MvPowerSeries.map ι ((![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) k) j) := by
    funext j; fin_cases j <;> simp
  have h12 : (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) (DualNumber k)) =
      fun j ↦ MvPowerSeries.map ι ((![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) k) j) := by
    funext j; fin_cases j <;> simp
  have hF₁₂ : HasSubst (![F₀.toPowerSeries.subst ![X 0, X 1], X 2] :
      Fin 2 → MvPowerSeries (Fin 3) k) :=
    HasSubst.cons_subst_zero_left 0 1 2 F₀.zero_constantCoeff
  have hF₂₃ : HasSubst (![X 0, F₀.toPowerSeries.subst ![X 1, X 2]] :
      Fin 2 → MvPowerSeries (Fin 3) k) :=
    HasSubst.cons_subst_zero_right 0 1 2 F₀.zero_constantCoeff
  have hargL : (![(F₀.map ι).toPowerSeries.subst ![X 0, X 1], X 2] :
      Fin 2 → MvPowerSeries (Fin 3) (DualNumber k)) =
      fun j ↦ MvPowerSeries.map ι
        ((![F₀.toPowerSeries.subst ![X 0, X 1], X 2] : Fin 2 → MvPowerSeries (Fin 3) k) j) := by
    funext j; fin_cases j
    · change (F₀.map ι).toPowerSeries.subst ![X 0, X 1] =
          MvPowerSeries.map ι (F₀.toPowerSeries.subst ![X 0, X 1])
      rw [map_toPowerSeries, h01, ← MvPowerSeries.map_subst (HasSubst.X_X :
        HasSubst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) k))]
    · simp
  have hargR : (![X 0, (F₀.map ι).toPowerSeries.subst ![X 1, X 2]] :
      Fin 2 → MvPowerSeries (Fin 3) (DualNumber k)) =
      fun j ↦ MvPowerSeries.map ι
        ((![X 0, F₀.toPowerSeries.subst ![X 1, X 2]] : Fin 2 → MvPowerSeries (Fin 3) k) j) := by
    funext j; fin_cases j
    · simp
    · change (F₀.map ι).toPowerSeries.subst ![X 1, X 2] =
          MvPowerSeries.map ι (F₀.toPowerSeries.subst ![X 1, X 2])
      rw [map_toPowerSeries, h12, ← MvPowerSeries.map_subst (HasSubst.X_X :
        HasSubst (![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) k))]
  dsimp only [ι] at h01 h12 hargL hargR hsubst_pull
  rw [hargL, hargR, h01, h12, hsubst_pull _ HasSubst.X_X, hsubst_pull _ hF₁₂,
    hsubst_pull _ hF₂₃, hsubst_pull _ HasSubst.X_X] at hcoc
  ext d
  have hcoeff := congrArg (fun f ↦ TrivSqZeroExt.snd (coeff d f)) hcoc
  simpa [ι, map_add] using hcoeff

/-- **The partial-derivative cocycle is a symmetric 2-cocycle of `F₀`** whenever `Γ` is a
commutative lift of `F₀` along `ρ.comp constantCoeff`. -/
theorem isSymmetricCocycle_derivCocycle (Γ : FormalGroup (MvPowerSeries σ R)) [Γ.IsComm]
    (ρ : R →+* k) (F₀ : FormalGroup k) [F₀.IsComm]
    (hΓ : Γ.map (ρ.comp constantCoeff) = F₀) (i : σ) :
    F₀.IsSymmetricCocycle (derivCocycle Γ ρ F₀ i) :=
  let hsymm := isSymmetricCocycle_eps_smul_derivCocycle Γ ρ F₀ hΓ i
  ⟨derivCocycle_swap_eq _ hsymm.subst_swap,
    derivCocycle_cocycle_eq F₀ _ hsymm.subst_add_subst_eq⟩

private theorem coeffPartial_lubinTateLaw_order {p h : ℕ} (F : FormalGroup R) [F.IsComm]
    (hp : 1 < p) (ρ : R →+* k) (i : Fin (h - 1)) :
    ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤
      (coeffPartial ρ i (F.lubinTateLaw hp h).toPowerSeries).order := by
  have hC : (evalDual ρ i).comp C =
      ((TrivSqZeroExt.inlHom k k).comp
        (ρ.comp (constantCoeff (σ := Fin (h - 1))))).comp C := by
    ext r <;> simp
  have hX : ∀ j < i, evalDual ρ i (X j) =
      ((TrivSqZeroExt.inlHom k k).comp (ρ.comp constantCoeff)) (X j) := fun j hj ↦ by
    simp [hj.ne]
  have hord := le_order_map_lubinTateLaw_sub_map (F := F) (hp := hp) (h := h) hC hX
  refine nat_le_order fun d hd ↦ ?_
  have hcoeff := coeff_of_lt_order ((Nat.cast_lt.mpr hd).trans_le hord)
  have hzero := congrArg TrivSqZeroExt.snd hcoeff
  simpa [coeff_coeffPartial] using hzero

/-- The `p ^ (i + 1)`-order bound for the partial-derivative cocycle of the generic Lubin–Tate
law: `derivCocycle (F.lubinTateLaw hp h) ρ (F.map ρ) i` vanishes below degree `p ^ (i + 1)`. -/
theorem le_order_derivCocycle_lubinTateLaw {p h : ℕ} (F : FormalGroup R) [F.IsComm]
    (hp : 1 < p) (ρ : R →+* k) (i : Fin (h - 1)) :
    ((p ^ (i + 1 : ℕ) : ℕ) : ℕ∞) ≤
      (derivCocycle (F.lubinTateLaw hp h) ρ (F.map ρ) i).order :=
  (coeffPartial_lubinTateLaw_order F hp ρ i).trans (le_add_self.trans le_order_mul)

/-- Multiplying a series `g` of order at least `n` on the left by a series with constant
coefficient `1` does not change its degree-`n` homogeneous component. -/
private theorem homogeneousComponent_mul_of_constantCoeff_eq_one {τ : Type*}
    {f g : MvPowerSeries τ k} (hf : constantCoeff f = 1) {n : ℕ} (hg : (n : ℕ∞) ≤ g.order) :
    homogeneousComponent n (f * g) = homogeneousComponent n g := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
  split_ifs with hdeg
  · rw [coeff_mul, Finset.sum_eq_single (0, d)]
    · simp [hf]
    · rintro ⟨u, v⟩ huv hne
      rw [Finset.mem_antidiagonal] at huv
      have hv_ne : v ≠ d := fun h ↦ hne (Prod.ext (by
        subst h
        exact add_eq_right.mp huv) h)
      have hv_lt : v.degree < n := by
        have hsum : u.degree + v.degree = d.degree := by
          rw [← huv, map_add]
        have hu_pos : 0 < u.degree := by
          rcases Nat.eq_zero_or_pos u.degree with h0 | hpos
          · have hu0 : u = 0 := by
              ext j
              exact Nat.eq_zero_of_le_zero ((Finsupp.le_degree j u).trans h0.le)
            rw [hu0, _root_.zero_add] at huv
            exact absurd huv hv_ne
          · exact hpos
        omega
      rw [coeff_of_lt_order ((Nat.cast_lt.mpr hv_lt).trans_le hg), mul_zero]
    · intro hnot
      exact absurd (Finset.mem_antidiagonal.mpr (_root_.zero_add d)) hnot
  · rfl

/-- The degree-`p ^ (i + 1)` homogeneous component of
`derivCocycle (F.lubinTateLaw hp h) ρ (F.map ρ) i` is the Lazard cocycle
`lazardCocycle (p ^ (i + 1)) k`. -/
theorem homogeneousComponent_derivCocycle_lubinTateLaw {p h : ℕ} (F : FormalGroup R) [F.IsComm]
    (hp : 1 < p) (ρ : R →+* k) (i : Fin (h - 1)) :
    homogeneousComponent (p ^ (i + 1 : ℕ))
        (derivCocycle (F.lubinTateLaw hp h) ρ (F.map ρ) i) =
      ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k) := by
  have hC : (evalDual ρ i).comp C =
      ((TrivSqZeroExt.inlHom k k).comp
        (ρ.comp (constantCoeff (σ := Fin (h - 1))))).comp C := by
    ext r <;> simp
  have hX : ∀ j < i, evalDual ρ i (X j) =
      ((TrivSqZeroExt.inlHom k k).comp (ρ.comp constantCoeff)) (X j) := fun j hj ↦ by
    simp [hj.ne]
  have hcomp := homogeneousComponent_map_lubinTateLaw_sub_map_eq_smul_lazardCocycle
    (F := F) (hp := hp) (h := h) hC hX
  have hpart_comp :
      homogeneousComponent (p ^ (i + 1 : ℕ))
          (coeffPartial ρ i (F.lubinTateLaw hp h).toPowerSeries) =
        ↑(TauCeti.lazardCocycle (p ^ (i + 1 : ℕ)) k) := by
    ext d
    have hc := congrArg (fun f ↦ (coeff d f).snd) hcomp
    rw [coeff_homogeneousComponent]
    split_ifs with hdeg
    · rw [coeff_homogeneousComponent, ite_eq_left hdeg] at hc
      have hsub :
          (coeff d (((F.lubinTateLaw hp h).map (evalDual ρ i)).toPowerSeries -
            ((F.lubinTateLaw hp h).map ((TrivSqZeroExt.inlHom k k).comp
              (ρ.comp constantCoeff))).toPowerSeries)).snd =
            coeff d (coeffPartial ρ i (F.lubinTateLaw hp h).toPowerSeries) := by
        rw [map_sub (coeff d), map_toPowerSeries, map_toPowerSeries, coeff_map, coeff_map]
        simp [TrivSqZeroExt.inlHom_apply]
      rw [← hsub, hc, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe,
        AddMonoidAlgebra.coeff_smul_apply,
        ← TauCeti.map_lazardCocycle (TrivSqZeroExt.inlHom k k), MvPolynomial.coeff_map]
      simp [TrivSqZeroExt.inlHom_apply]
    · simp [MvPolynomial.coeff_coe,
        (TauCeti.isHomogeneous_lazardCocycle (p ^ (i + 1 : ℕ))).coeff_eq_zero (R := k) hdeg]
  have hω_const : constantCoeff
      (PowerSeries.subst (F.map ρ).toPowerSeries (F.map ρ).invariantDifferential) = 1 := by
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero (F.map ρ).zero_constantCoeff,
      (F.map ρ).constantCoeff_invariantDifferential, map_one]
  rw [derivCocycle, homogeneousComponent_mul_of_constantCoeff_eq_one hω_const
    (coeffPartial_lubinTateLaw_order F hp ρ i), hpart_comp]

end DerivCocycle

end FormalGroup
