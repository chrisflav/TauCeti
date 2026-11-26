/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The volume `ω_k` of the unit ball of `ℝ ^ k`

This file defines `ω_k = TauCeti.unitBallVolume k`, the volume of the unit ball of
`EuclideanSpace ℝ (Fin k)`, and expresses the volume of every ball of radius `r` in a
`k`-dimensional real inner product space as `ω_k r ^ k`
(`TauCeti.volume_ball_eq_unitBallVolume_mul`, `TauCeti.volume_closedBall_eq_unitBallVolume_mul`).
Inscribing a cube of side `2 / √k` gives `(2 / √k) ^ k ≤ ω_k`
(`TauCeti.two_div_sqrt_pow_le_unitBallVolume`, and
`TauCeti.two_div_sqrt_pow_le_volumeReal_closedBall` for general radii). It records `ω_1 = 2` and
`ω_2 = π` (`TauCeti.unitBallVolume_one`, `TauCeti.unitBallVolume_two`).
The constant `ω_k` normalizes the `k`-dimensional densities of a measure.
-/

public section

noncomputable section

open Metric MeasureTheory Module
open scoped ENNReal

namespace TauCeti

/-- `ω_k`, the volume of the unit ball of `ℝ ^ k` (that is, of `EuclideanSpace ℝ (Fin k)`). The
volume of a ball of radius `r > 0` in a `k`-dimensional real inner product space is `ω_k r ^ k`
(`TauCeti.volume_ball_eq_unitBallVolume_mul`). -/
def unitBallVolume (k : ℕ) : ℝ≥0∞ :=
  volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)

theorem unitBallVolume_def (k : ℕ) :
    unitBallVolume k = volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) :=
  (rfl)

theorem unitBallVolume_pos (k : ℕ) : 0 < unitBallVolume k :=
  measure_ball_pos _ _ one_pos

theorem unitBallVolume_ne_zero (k : ℕ) : unitBallVolume k ≠ 0 :=
  (unitBallVolume_pos k).ne'

theorem unitBallVolume_ne_top (k : ℕ) : unitBallVolume k ≠ ∞ :=
  measure_ball_lt_top.ne

/-- The volume `ω_k ρ ^ k` of a ball of radius `ρ > 0` in `ℝ ^ k` is nonzero. -/
theorem unitBallVolume_mul_ofReal_pow_ne_zero (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    unitBallVolume k * ENNReal.ofReal ρ ^ k ≠ 0 :=
  mul_ne_zero (unitBallVolume_ne_zero k) (pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ).ne')

/-- The volume `ω_k ρ ^ k` of a ball of radius `ρ` in `ℝ ^ k` is finite. -/
theorem unitBallVolume_mul_ofReal_pow_ne_top (k : ℕ) (ρ : ℝ) :
    unitBallVolume k * ENNReal.ofReal ρ ^ k ≠ ∞ :=
  ENNReal.mul_ne_top (unitBallVolume_ne_top k) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The unit ball of a real inner product space of dimension `k` has volume `ω_k`. -/
theorem volume_ball_zero_one_eq_unitBallVolume :
    volume (ball (0 : E) 1) = unitBallVolume (finrank ℝ E) :=
  volume_ball_eq_of_finrank_eq (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm 0 0 1

/-- A closed ball of radius `r ≥ 0` in a real inner product space of dimension `k` has volume
`ω_k r ^ k`. -/
theorem volume_closedBall_eq_unitBallVolume_mul (x : E) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = unitBallVolume (finrank ℝ E) * ENNReal.ofReal r ^ finrank ℝ E := by
  rw [Measure.addHaar_closedBall _ x hr, volume_ball_zero_one_eq_unitBallVolume,
    ENNReal.ofReal_pow hr, mul_comm]

/-- An open ball of radius `r > 0` in a real inner product space of dimension `k` has volume
`ω_k r ^ k`. -/
theorem volume_ball_eq_unitBallVolume_mul (x : E) {r : ℝ} (hr : 0 < r) :
    volume (ball x r) = unitBallVolume (finrank ℝ E) * ENNReal.ofReal r ^ finrank ℝ E := by
  rw [Measure.addHaar_ball_of_pos _ x hr, volume_ball_zero_one_eq_unitBallVolume,
    ENNReal.ofReal_pow hr.le, mul_comm]

end InnerProductSpace

/-- `ω_1 = 2`: the unit ball of `ℝ` is an interval of length `2`. -/
@[simp]
theorem unitBallVolume_one : unitBallVolume 1 = 2 := by
  have h := volume_ball_eq_unitBallVolume_mul (0 : ℝ) one_pos
  simp only [Real.volume_ball, Module.finrank_self, ENNReal.ofReal_one, one_pow, mul_one] at h
  rw [← h, ENNReal.ofReal_ofNat]

/-- `ω_2 = π`: the unit disc has area `π`. -/
@[simp]
theorem unitBallVolume_two : unitBallVolume 2 = ENNReal.ofReal Real.pi := by
  rw [unitBallVolume_def, EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_one, one_pow,
    one_mul]

/-- Inscribing a cube of side `2 / √k` inside the closed unit ball of `ℝ ^ k` shows that
`(2 / √k) ^ k ≤ ω_k`. -/
theorem two_div_sqrt_pow_le_unitBallVolume (k : ℕ) :
    ENNReal.ofReal (2 / √(k : ℝ)) ^ k ≤ unitBallVolume k := by
  set s : ℝ := 1 / √(k : ℝ)
  set Q : Set (Fin k → ℝ) := Set.Icc (fun _ ↦ -s) (fun _ ↦ s)
  have hsub : WithLp.ofLp ⁻¹' Q ⊆ closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg x),
      EuclideanSpace.real_norm_sq_eq]
    have hsq : ∀ i : Fin k, x i ^ 2 ≤ s ^ 2 := fun i ↦ by
      have hi : x i ∈ Set.Icc (-s) s := ⟨hx.1 i, hx.2 i⟩
      exact sq_le_sq.2 <| by simpa [abs_of_nonneg (show 0 ≤ s by positivity)] using abs_le.2 hi
    calc ∑ i : Fin k, x i ^ 2 ≤ ∑ _i : Fin k, s ^ 2 := Finset.sum_le_sum fun i _ ↦ hsq i
      _ = (k : ℝ) * (1 / (k : ℝ)) := by
          simp [s, Real.sq_sqrt (Nat.cast_nonneg k)]
      _ ≤ 1 := by
          rcases eq_or_ne k 0 with rfl | hk
          · simp
          · rw [mul_one_div_cancel (Nat.cast_ne_zero.2 hk)]
  have hvolQ : volume (WithLp.ofLp ⁻¹' Q : Set (EuclideanSpace ℝ (Fin k))) =
      ENNReal.ofReal (2 / √(k : ℝ)) ^ k := by
    rw [(PiLp.volume_preserving_ofLp (Fin k)).measure_preimage
      measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    simp [s, sub_neg_eq_add,
      show (√(k : ℝ))⁻¹ + (√(k : ℝ))⁻¹ = 2 / √(k : ℝ) by ring]
  have hball : volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) = unitBallVolume k := by
    rw [volume_closedBall_eq_unitBallVolume_mul 0 zero_le_one, finrank_euclideanSpace_fin,
      ENNReal.ofReal_one, one_pow, mul_one]
  exact hvolQ ▸ hball ▸ measure_mono hsub

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A closed ball of radius `r ≥ 0` in a `k`-dimensional real inner product space has volume at
least `(2 * r / √k) ^ k`, by inscribing a hypercube of side `2 * r / √k`. -/
theorem two_div_sqrt_pow_le_volume_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (2 * r / √(finrank ℝ E : ℝ)) ^ finrank ℝ E ≤
      volume (closedBall x r) := by
  rw [volume_closedBall_eq_unitBallVolume_mul x hr,
    show 2 * r / √(finrank ℝ E : ℝ) = 2 / √(finrank ℝ E : ℝ) * r by ring,
    ENNReal.ofReal_mul (by positivity), mul_pow]
  exact mul_le_mul_left (two_div_sqrt_pow_le_unitBallVolume (finrank ℝ E)) _

/-- Real-valued form of `TauCeti.two_div_sqrt_pow_le_volume_closedBall`: a closed ball of radius
`r ≥ 0` in a `k`-dimensional real inner product space has real volume at least
`(2 * r / √k) ^ k`. -/
theorem two_div_sqrt_pow_le_volumeReal_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) :
    (2 * r / √(finrank ℝ E : ℝ)) ^ finrank ℝ E ≤ volume.real (closedBall x r) := by
  have h := ENNReal.toReal_mono measure_closedBall_lt_top.ne
    (two_div_sqrt_pow_le_volume_closedBall x hr)
  rwa [← measureReal_def, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h

end InnerProductSpace

end TauCeti
