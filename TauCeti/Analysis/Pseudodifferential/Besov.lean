/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.FourierMultiplier
public import TauCeti.Analysis.Holder.Zygmund
import TauCeti.Analysis.Pseudodifferential.Symbol.Dyadic
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Pseudodifferential operators on Besov and Hölder–Zygmund spaces

Let `a ∈ S^m_{1,0}(ℝⁿ; V, W)` be a uniform symbol of order `m ∈ ℝ` between finite-dimensional
complex normed spaces. Its left quantization `Op(a)` extends to tempered distributions via
`TauCeti.Symbol.quantizeTemperedCLM`. This file proves that `Op(a)` maps the inhomogeneous Besov
space `B^s_{p,q}(ℝⁿ; V)` boundedly into `B^{s-m}_{p,q}(ℝⁿ; W)` for every `s ∈ ℝ` and every
`1 ≤ p, q ≤ ∞`, including the endpoints `p = 1` and `p = ∞` where `Op(a)` fails to preserve `Lᵖ`
(Taylor, Lecture I, (3.32)–(3.34)).

At `p = q = ∞`, `B^s_{∞,∞}` is the Hölder–Zygmund scale `𝒞^s`. Composing with the inclusions
`TauCeti.BesovSpace.toHolderSpace` and `TauCeti.BesovSpace.toCkHolderSpace` yields bounded
real-linear operators into the classical bounded Hölder spaces `C_b^{0,α}` and `C_b^{k,α}` whenever
`0 < α < 1` and `k + α ≤ s - m`, and in particular at `s - m = k + α`.

## Proof architecture

1. **Uniform `Lᵖ` bound on dyadic symbol pieces.** For a uniform symbol `b` of order `0`, the
   `r`-th Littlewood–Paley piece `b_r(x, ξ) = ψ_r(ξ) b(x, ξ)` has bounded frequency support and
   satisfies the scale-invariant integral bounds `∫ ‖b_r(x, ξ)‖ dξ ≤ A` and
   `∫ ‖∂_{ξ_j}^{n+1} b_r(x, ξ)‖ dξ ≤ A R^{n+1}` with `A = C 2^{rn}` and `R = 2^{-r}`
   (`TauCeti.Symbol.IsUniform.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le`). Hence
   `TauCeti.Symbol.norm_quantizeLp_le` bounds `‖Op(b_r)‖_{Lᵖ → Lᵖ} ≤ C` uniformly in `r` and
   `1 ≤ p ≤ ∞`.
2. **Band-limited and annular `Lᵖ` bound.** Any `f ∈ Lᵖ` whose Fourier transform vanishes on the
   excluded frequency set of the `k`-th Littlewood–Paley block is reproduced by the sum of at most
   `2L + 1` rescaled pieces `ψ_r(2π ·)` around `k`. By exact right composition with Fourier
   multipliers (`TauCeti.Symbol.quantizeTemperedCLM_fourierMultiplierCLM_of_coefficient_eq`),
   `Op(b) f = ∑_r Op(b_r) f` lies in `Lᵖ` with norm `O(‖f‖_p)` uniformly in `k` and `p`.
3. **Off-diagonal decay between Littlewood–Paley blocks.**
   * When `j > k`, iterating the spatial-derivative commutator
     `∂_i (Op(b) f) = Op(b) (∂_i f) + Op(∂_{x_i} b) f`
     (`TauCeti.Symbol.lineDerivOp_quantizeTemperedCLM`)
     with Bernstein's inequality bounds the `M`-th derivatives of `Op(b) Δ_k u` by `O(2^{kM})`,
     and the reverse Bernstein inequality on the `j`-th annulus gains `2^{-jM}`.
   * When `j < k`, the annular reproducing formula writes `Δ_k u = ∑_i ∂_i h_i` with
     `‖h_i‖_p = O(2^{-k} ‖Δ_k u‖_p)` and the same annular spectrum, while
     `Op(b) (∂_i h_i) = ∂_i (Op(b) h_i) - Op(∂_{x_i} b) h_i` transfers the derivative to `Δ_j`,
     where Bernstein's inequality costs `2^j`; iterating `M` times gains `(2^j / 2^k)^M`.
4. **Summing the blocks and lifting the order.** Taking `M = ⌊|s|⌋₊ + 1 > |s|` gives geometric
   decay away from the diagonal on `ℓ^q(ℕ, Lᵖ)`, establishing `Op(b) : B^s_{p,q} →L[ℂ] B^s_{p,q}`
   for symbols of order `0`. Writing `Op(a) u = Op(a ∘ ⟨ξ / 2π⟩^{-m}) (J^m u)` via
   `TauCeti.Symbol.quantizeTemperedCLM_besselPotential` reduces general order `m ∈ ℝ` to order `0`
   via the Bessel-potential lifting isomorphism `TauCeti.BesovSpace.besselPotentialEquiv`.

## Main declarations

* `TemperedDistribution.MemBesov.quantizeTemperedCLM`: if `u ∈ B^s_{p,q}` and `a` is uniform of
  order `m`, then `Op(a) u ∈ B^{s-m}_{p,q}`.
* `TauCeti.Symbol.quantizeBesov`: the bounded operator
  `Op(a) : B^s_{p,q}(ℝⁿ; V) →L[ℂ] B^{s-m}_{p,q}(ℝⁿ; W)`, characterized by
  `TauCeti.Symbol.toDistr_quantizeBesov`.
* `TauCeti.Symbol.quantizeZygmundToHolder` and `TauCeti.Symbol.quantizeZygmundToCkHolder`:
  the Hölder–Zygmund order shifts `𝒞^s →L[ℝ] C_b^{0,α}` and `𝒞^s →L[ℝ] C_b^{k,α}` for `0 < α < 1`
  and `k + α ≤ s - m`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3,
  (3.32)–(3.34).
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Princeton University Press, 1993, Chapter VI, §5.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory Metric Distribution Filter Real ContinuousLinearMap TemperedDistribution
open BoundedContinuousFunction
open scoped ENNReal NNReal SchwartzMap ContDiff FourierTransform LineDeriv Topology

namespace TauCeti

namespace Symbol

section OrderZero

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [CompleteSpace W]

/-! ### Uniform `Lᵖ` bound on dyadic pieces of an order-zero symbol -/

/-- The `r`-th Littlewood–Paley piece of a symbol `b` of order `0`, viewed at the integrable order
`-n - 1` via its bounded frequency support. -/
private def boundedPiece (φ : ContDiffBump (0 : CoordinateSpace n)) (b : Symbol n V W 0)
    (r : ℕ) : Symbol n V W (-(n : ℝ) - 1) :=
  ofBoundedFrequencySupport (b.littlewoodPaleyPiece φ r).coefficient
    (b.littlewoodPaleyPiece φ r).contDiff_coefficient (2 ^ r * φ.rOut)
    fun x _ hξ ↦ b.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm φ x hξ

omit [FiniteDimensional ℂ V] [CompleteSpace V] [FiniteDimensional ℂ W] [CompleteSpace W] in
private theorem isUniform_boundedPiece (φ : ContDiffBump (0 : CoordinateSpace n))
    {b : Symbol n V W 0} (hb : b.IsUniform) (r : ℕ) :
    (boundedPiece φ b r).IsUniform := by
  refine isUniform_iff.2 fun α β ↦ ?_
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_mixedDeriv_littlewoodPaleyPiece_le_two_pow φ α β
  set e : ℝ := (-(n : ℝ) - 1 - β.length) / 2
  set R : ℝ := 2 ^ r * φ.rOut
  have he : e ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) β.length]) zero_le_two
  refine ⟨C * ((2 : ℝ) ^ r) ^ ((0 : ℝ) - β.length) * (1 + R ^ 2) ^ (-e), by positivity,
    fun x ξ ↦ ?_⟩
  by_cases hξ : ξ ∈ tsupport (φ.inhomogeneousLittlewoodPaley r)
  · have hξR : ‖ξ‖ ≤ R :=
      mem_closedBall_zero_iff.1 (φ.tsupport_inhomogeneousLittlewoodPaley_subset_closedBall r hξ)
    have hsq : 1 + ‖ξ‖ ^ 2 ≤ 1 + R ^ 2 := by gcongr
    have hrpow : 1 ≤ (1 + R ^ 2) ^ (-e) * (1 + ‖ξ‖ ^ 2) ^ e :=
      calc (1 : ℝ) = (1 + R ^ 2) ^ (-e) * (1 + R ^ 2) ^ e := by
            rw [← Real.rpow_add (by positivity), neg_add_cancel, Real.rpow_zero]
        _ ≤ (1 + R ^ 2) ^ (-e) * (1 + ‖ξ‖ ^ 2) ^ e :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hsq he)
              (by positivity)
    calc ‖mixedDeriv α β (boundedPiece φ b r).coefficient x ξ‖
        ≤ C * ((2 : ℝ) ^ r) ^ ((0 : ℝ) - β.length) * 1 := by
          rw [mul_one, boundedPiece, coefficient_ofBoundedFrequencySupport]
          exact hC r x ξ
      _ ≤ C * ((2 : ℝ) ^ r) ^ ((0 : ℝ) - β.length) *
            ((1 + R ^ 2) ^ (-e) * (1 + ‖ξ‖ ^ 2) ^ e) := by gcongr
      _ = C * ((2 : ℝ) ^ r) ^ ((0 : ℝ) - β.length) * (1 + R ^ 2) ^ (-e) *
            (1 + ‖ξ‖ ^ 2) ^ e := by ring
  · rw [boundedPiece, coefficient_ofBoundedFrequencySupport,
      b.mixedDeriv_littlewoodPaleyPiece_eq_zero_of_notMem_tsupport φ α β x hξ, norm_zero]
    positivity

/-- For a uniform symbol `b` of order `0`, the quantizations of its Littlewood–Paley pieces map
`Lᵖ` to `Lᵖ` with norm bounded uniformly in the dyadic index `r` and the exponent `1 ≤ p ≤ ∞`. -/
private theorem exists_quantizeTemperedCLM_littlewoodPaleyPiece_eq_and_norm_le
    (φ : ContDiffBump (0 : CoordinateSpace n)) {b : Symbol n V W 0} (hb : b.IsUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (r : ℕ)
      (f : Lp V p (volume : Measure (CoordinateSpace n))),
      ∃ g : Lp W p (volume : Measure (CoordinateSpace n)),
        (b.littlewoodPaleyPiece φ r).quantizeTemperedCLM (hb.littlewoodPaleyPiece φ r)
          (f : 𝓢'(CoordinateSpace n, V)) = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := hb.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le φ [] []
  choose C₁ hC₁0 hC₁ using fun j : Fin n ↦
    hb.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le φ [] (List.replicate (n + 1) j)
  set M : ℝ := C₀ + ∑ j : Fin n, C₁ j
  set I : ℝ := ∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹
  have : 0 ≤ I := integral_nonneg fun _ ↦ by positivity
  have hM0 : 0 ≤ M := add_nonneg hC₀0 (Finset.sum_nonneg fun j _ ↦ hC₁0 j)
  refine ⟨2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * M * I, by positivity,
    fun {p} _ r f ↦ ?_⟩
  have hm : -(n : ℝ) - 1 < -n := by linarith
  have hc := isUniform_boundedPiece φ hb r
  set A : ℝ := M * ((2 : ℝ) ^ r) ^ n
  set R : ℝ := ((2 : ℝ) ^ r)⁻¹
  have h₀ (x : CoordinateSpace n) : ∫ ξ, ‖(boundedPiece φ b r).coefficient (x, ξ)‖ ≤ A := by
    have h₀' : ∫ ξ, ‖(boundedPiece φ b r).coefficient (x, ξ)‖ ≤ C₀ * ((2 : ℝ) ^ r) ^ n := by
      simpa [boundedPiece, Real.rpow_natCast] using hC₀ r x
    exact h₀'.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ hC₁0 j)) (by positivity))
  have h₁ (x : CoordinateSpace n) (j : Fin n) :
      ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) j) (boundedPiece φ b r).coefficient x ξ‖ ≤
        A * R ^ (n + 1) := by
    have hj := hC₁ j r x
    rw [List.length_replicate, Nat.cast_add, Nat.cast_one,
      show (0 : ℝ) - (n + 1) + n = -1 by ring, Real.rpow_neg_one] at hj
    have hAR : A * R ^ (n + 1) = M * ((2 : ℝ) ^ r)⁻¹ := by
      simp only [A, R, pow_succ, inv_pow]
      field_simp
    rw [boundedPiece, coefficient_ofBoundedFrequencySupport, hAR]
    exact hj.trans (mul_le_mul_of_nonneg_right
      ((Finset.single_le_sum (fun i _ ↦ hC₁0 i) (Finset.mem_univ j)).trans
        (le_add_of_nonneg_left hC₀0)) (by positivity))
  have hop := (boundedPiece φ b r).norm_quantizeLp_le (p := p) (hm := hm) (ha := hc)
    (by positivity : 0 < R) h₀ h₁
  have hcancel : 2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * A * I * R ^ n =
      2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ * M * I := by
    simp only [A, R, inv_pow]
    field_simp
  refine ⟨(boundedPiece φ b r).quantizeLp p hm hc f, ?_, ?_⟩
  · rw [quantizeTemperedCLM_congr (hb.littlewoodPaleyPiece φ r) hc
      (coefficient_ofBoundedFrequencySupport _ _ _ _).symm,
      quantizeTemperedCLM_lp _ hm hc f]
  · exact ((boundedPiece φ b r).quantizeLp p hm hc).le_opNorm f |>.trans
      (mul_le_mul_of_nonneg_right (hop.trans_eq hcancel) (norm_nonneg f))

/-! ### Reproducing frequency-localized `Lᵖ` functions by boundedly many pieces -/

/-- The excluded frequency set of the `k`-th Littlewood–Paley block: outside the closed ball of
radius `φ.rOut` when `k = 0`, and outside the `k`-th dyadic annulus when `k ≥ 1`. -/
private def specSet (φ : ContDiffBump (0 : CoordinateSpace n)) : ℕ → Set (CoordinateSpace n)
  | 0 => (closedBall 0 φ.rOut)ᶜ
  | k + 1 => ball 0 (2 ^ k * φ.rIn) ∪ (closedBall 0 (2 ^ (k + 1) * φ.rOut))ᶜ

private theorem compl_closedBall_subset_specSet (φ : ContDiffBump (0 : CoordinateSpace n))
    (k : ℕ) : (closedBall (0 : CoordinateSpace n) (2 ^ k * φ.rOut))ᶜ ⊆ specSet φ k := by
  rcases k with _ | k
  · simp [specSet]
  · exact Set.subset_union_right

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
private theorem isVanishingOn_specSet_littlewoodPaleyBlock
    (φ : ContDiffBump (0 : CoordinateSpace n)) (k : ℕ) (u : 𝓢'(CoordinateSpace n, V)) :
    IsVanishingOn (𝓕 (littlewoodPaleyBlock V φ k u) : 𝓢'(CoordinateSpace n, V)) (specSet φ k) := by
  rcases k with _ | k
  · simpa [specSet] using isVanishingOn_fourier_littlewoodPaleyBlock φ 0 u
  · simpa only [specSet, Set.compl_sdiff, Set.union_comm] using
      isVanishingOn_fourier_littlewoodPaleyBlock_succ φ k u

private theorem two_mul_rOut_div_rIn_mul (φ : ContDiffBump (0 : CoordinateSpace n)) (k : ℕ) :
    2 * φ.rOut / φ.rIn * (2 ^ k * φ.rIn) = 2 ^ (k + 1) * φ.rOut := by
  have := φ.rIn_pos.ne'
  rw [pow_succ]
  field_simp

private theorem sum_inhomogeneousLittlewoodPaley_two_pi_eq_one
    (φ : ContDiffBump (0 : CoordinateSpace n)) {T : Finset ℕ} {ζ : CoordinateSpace n}
    (hzero : ∀ r ∉ T, φ.inhomogeneousLittlewoodPaley r ((2 * π) • ζ) = 0) :
    (∑ r ∈ T,
      fun w : CoordinateSpace n ↦ (φ.inhomogeneousLittlewoodPaley r ((2 * π) • w) : ℂ)) ζ = 1 := by
  have hval : (∑ r ∈ T,
      (fun w : CoordinateSpace n ↦ (φ.inhomogeneousLittlewoodPaley r ((2 * π) • w) : ℂ))) ζ =
      ((∑ r ∈ T, φ.inhomogeneousLittlewoodPaley r ((2 * π) • ζ) : ℝ) : ℂ) := by simp
  rw [hval, (hasSum_sum_of_ne_finset_zero hzero).unique
    (φ.hasSum_inhomogeneousLittlewoodPaley ((2 * π) • ζ)), Complex.ofReal_one]

private theorem tsupport_sum_inhomogeneousLittlewoodPaley_two_pi_sub_one_subset_succ
    (φ : ContDiffBump (0 : CoordinateSpace n)) {L : ℕ}
    (h₁ : 4 * π * φ.rOut < 2 ^ L * φ.rIn) (h₂ : φ.rOut < 2 ^ L * (π * φ.rIn)) (k : ℕ) :
    tsupport ((∑ r ∈ Finset.Ico (k + 1 - L) (k + 1 + L + 1),
      fun ζ : CoordinateSpace n ↦ (φ.inhomogeneousLittlewoodPaley r ((2 * π) • ζ) : ℂ)) - 1) ⊆
      specSet φ (k + 1) := by
  have hrIn := φ.rIn_pos
  have hrOut := φ.rOut_pos
  set S : Set (CoordinateSpace n) :=
    {ζ | ‖ζ‖ ≤ 2 ^ k * (φ.rIn / 2)} ∪ {ζ | 2 ^ (k + 1) * (2 * φ.rOut) ≤ ‖ζ‖}
  have hSclosed : IsClosed S :=
    (isClosed_le continuous_norm continuous_const).union
      (isClosed_le continuous_const continuous_norm)
  have hSsub : S ⊆ specSet φ (k + 1) := by
    rintro ζ (hζ | hζ)
    · rw [Set.mem_ofPred] at hζ
      have : (0 : ℝ) < 2 ^ k * φ.rIn := by positivity
      exact Or.inl (mem_ball_zero_iff.2 (by linarith))
    · rw [Set.mem_ofPred] at hζ
      exact Or.inr fun hcb ↦ by
        have := mem_closedBall_zero_iff.1 hcb
        have : (0 : ℝ) < 2 ^ (k + 1) * φ.rOut := by positivity
        linarith
  refine (closure_minimal (fun ζ hζ ↦ ?_) hSclosed).trans hSsub
  by_contra hnotS
  simp only [S, Set.mem_union, Set.mem_ofPred, not_or, not_le] at hnotS
  refine hζ ?_
  rw [Pi.sub_apply, Pi.one_apply, sub_eq_zero]
  refine sum_inhomogeneousLittlewoodPaley_two_pi_eq_one φ fun r hr ↦ ?_
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hr
  rcases hr with hr | hr
  · refine φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hrk : r + L ≤ k := by omega
    calc 2 ^ r * φ.rOut ≤ 2 ^ r * (2 ^ L * (π * φ.rIn)) := by gcongr
      _ = 2 ^ (r + L) * (π * φ.rIn) := by rw [pow_add]; ring
      _ ≤ 2 ^ k * (π * φ.rIn) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hrk) (by positivity)
      _ ≤ 2 * π * ‖ζ‖ := by nlinarith [Real.pi_pos, hnotS.1]
  · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    refine φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hrk : k + 1 + L ≤ r' := by omega
    calc 2 * π * ‖ζ‖ ≤ 2 ^ (k + 1) * (4 * π * φ.rOut) := by nlinarith [Real.pi_pos, hnotS.2]
      _ ≤ 2 ^ (k + 1) * (2 ^ L * φ.rIn) := by gcongr
      _ = 2 ^ (k + 1 + L) * φ.rIn := by rw [pow_add]; ring
      _ ≤ 2 ^ r' * φ.rIn :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hrk) hrIn.le

/-- A finite window of `2π`-rescaled Littlewood–Paley cutoffs around `k` equals `1` near the
spectrum of the `k`-th Littlewood–Paley block. -/
private theorem exists_tsupport_sum_inhomogeneousLittlewoodPaley_two_pi_sub_one_subset
    (φ : ContDiffBump (0 : CoordinateSpace n)) :
    ∃ L : ℕ, ∀ k : ℕ,
      tsupport ((∑ r ∈ Finset.Ico (k - L) (k + L + 1),
        fun ζ : CoordinateSpace n ↦ (φ.inhomogeneousLittlewoodPaley r ((2 * π) • ζ) : ℂ)) - 1) ⊆
        specSet φ k := by
  have hrIn := φ.rIn_pos
  have hrOut := φ.rOut_pos
  obtain ⟨L₁, hL₁⟩ := pow_unbounded_of_one_lt (4 * π * φ.rOut / φ.rIn) one_lt_two
  obtain ⟨L₂, hL₂⟩ := pow_unbounded_of_one_lt (φ.rOut / (π * φ.rIn)) one_lt_two
  rw [div_lt_iff₀ hrIn] at hL₁
  rw [div_lt_iff₀ (by positivity)] at hL₂
  set L := max L₁ L₂
  have h₁ : 4 * π * φ.rOut < 2 ^ L * φ.rIn :=
    hL₁.trans_le (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (le_max_left _ _))
      hrIn.le)
  have h₂ : φ.rOut < 2 ^ L * (π * φ.rIn) :=
    hL₂.trans_le (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (le_max_right _ _))
      (by positivity))
  refine ⟨L, fun k ↦ ?_⟩
  rcases k with _ | k
  · dsimp only [specSet]
    refine Set.Subset.trans ?_
      (Set.compl_subset_compl.2 (closedBall_subset_ball (ε₂ := 2 * φ.rOut) (by linarith)))
    refine closure_minimal (fun ζ hζ hball ↦ hζ ?_) isOpen_ball.isClosed_compl
    rw [Pi.sub_apply, Pi.one_apply, sub_eq_zero]
    refine sum_inhomogeneousLittlewoodPaley_two_pi_eq_one φ fun r hr ↦ ?_
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by simp at hr; omega⟩
    have hrL : L ≤ r' := by simp at hr; omega
    refine φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hζn : ‖ζ‖ < 2 * φ.rOut := mem_ball_zero_iff.1 hball
    calc 2 * π * ‖ζ‖ ≤ 4 * π * φ.rOut := by nlinarith [Real.pi_pos]
      _ ≤ 2 ^ L * φ.rIn := h₁.le
      _ ≤ 2 ^ r' * φ.rIn :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hrL) hrIn.le
  · exact tsupport_sum_inhomogeneousLittlewoodPaley_two_pi_sub_one_subset_succ φ h₁ h₂ k

/-- **Uniform `Lᵖ` bound on frequency-localized inputs.** For a uniform symbol `b` of order `0`, if
`f ∈ Lᵖ` has Fourier transform vanishing on `specSet φ k`, then `Op(b) f` is an `Lᵖ` function of
norm at most `C ‖f‖_p`, with `C` independent of `k` and `1 ≤ p ≤ ∞`. -/
private theorem exists_quantizeTemperedCLM_eq_and_norm_le_of_specSet
    (φ : ContDiffBump (0 : CoordinateSpace n)) {b : Symbol n V W 0} (hb : b.IsUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (k : ℕ)
      (f : Lp V p (volume : Measure (CoordinateSpace n))),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V)) (specSet φ k) →
      ∃ g : Lp W p (volume : Measure (CoordinateSpace n)),
        b.quantizeTemperedCLM hb (f : 𝓢'(CoordinateSpace n, V)) = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  obtain ⟨Cp, hCp0, hpiece⟩ := exists_quantizeTemperedCLM_littlewoodPaleyPiece_eq_and_norm_le φ hb
  obtain ⟨L, hL⟩ := exists_tsupport_sum_inhomogeneousLittlewoodPaley_two_pi_sub_one_subset φ
  refine ⟨(2 * L + 1) * Cp, by positivity, fun {p} _ k f hf ↦ ?_⟩
  set S := Finset.Ico (k - L) (k + L + 1)
  set g : ℕ → CoordinateSpace n → ℂ :=
    fun r ζ ↦ (φ.inhomogeneousLittlewoodPaley r ((2 * π) • ζ) : ℂ)
  have hg (r : ℕ) : (g r).HasTemperateGrowth := by fun_prop
  have hsum_fn : (fun ζ ↦ ∑ r ∈ S, g r ζ) = ∑ r ∈ S, g r :=
    (funext fun ζ ↦ Finset.sum_apply ζ S g).symm
  have hG : (∑ r ∈ S, g r).HasTemperateGrowth := by
    rw [← hsum_fn]
    exact Function.HasTemperateGrowth.sum fun r _ ↦ hg r
  choose v hv hvn using fun r ↦ hpiece r f
  have hfrepr : (f : 𝓢'(CoordinateSpace n, V)) =
      ∑ r ∈ S,
        TemperedDistribution.fourierMultiplierCLM V (g r) (f : 𝓢'(CoordinateSpace n, V)) := by
    rw [← sum_apply, ← TemperedDistribution.fourierMultiplierCLM_sum V fun r _ ↦ hg r, hsum_fn,
      fourierMultiplierCLM_eq_self_of_isVanishingOn hf hG (hL k)]
  have hterm (r : ℕ) :
      b.quantizeTemperedCLM hb
        (TemperedDistribution.fourierMultiplierCLM V (g r) (f : 𝓢'(CoordinateSpace n, V))) =
        (v r : 𝓢'(CoordinateSpace n, W)) := by
    rw [quantizeTemperedCLM_fourierMultiplierCLM_of_coefficient_eq hb
      (hb.littlewoodPaleyPiece φ r) (hg r) (fun q ↦ ?_), hv r]
    have hζ : (2 * π) • ((2 * π)⁻¹ • q.2) = q.2 :=
      smul_inv_smul₀ (by positivity : (2 * π : ℝ) ≠ 0) q.2
    dsimp only [g]
    rw [hζ]
    simp
  refine ⟨∑ r ∈ S, v r, ?_, ?_⟩
  · rw [hfrepr, map_sum, Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun r _ ↦ hterm r
  · have hcard : (S.card : ℝ) ≤ 2 * L + 1 := by
      have : S.card ≤ 2 * L + 1 := by simp only [S, Nat.card_Ico]; omega
      exact_mod_cast this
    calc ‖∑ r ∈ S, v r‖ ≤ ∑ r ∈ S, ‖v r‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ S, Cp * ‖f‖ := Finset.sum_le_sum fun r _ ↦ hvn r
      _ = S.card * (Cp * ‖f‖) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * L + 1) * (Cp * ‖f‖) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hCp0 (norm_nonneg f))
      _ = (2 * L + 1) * Cp * ‖f‖ := by ring

/-! ### Off-diagonal decay between Littlewood–Paley blocks -/

/-- **Iterated spatial derivatives of `Op(b) f`.** For a uniform symbol `b` of order `0` and any
`M`, if `f ∈ Lᵖ` has Fourier transform vanishing on `specSet φ k`, then every `M`-fold coordinate
derivative of `Op(b) f` is an `Lᵖ` function of norm `O(2^{kM} ‖f‖_p)`. -/
private theorem exists_iteratedLineDerivOp_quantizeTemperedCLM_eq_and_norm_le
    (φ : ContDiffBump (0 : CoordinateSpace n)) (M : ℕ) {b : Symbol n V W 0} (hb : b.IsUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (k : ℕ)
      (f : Lp V p (volume : Measure (CoordinateSpace n))),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V)) (specSet φ k) →
      ∀ i : Fin M → Fin n, ∃ g : Lp W p (volume : Measure (CoordinateSpace n)),
        ∂^{⇑(EuclideanSpace.basisFun (Fin n) ℝ) ∘ i}
          (b.quantizeTemperedCLM hb (f : 𝓢'(CoordinateSpace n, V))) = g ∧
        ‖g‖ ≤ C * ((2 : ℝ) ^ k) ^ M * ‖f‖ := by
  set eb := EuclideanSpace.basisFun (Fin n) ℝ
  obtain ⟨CB, hCB, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := CoordinateSpace n) (F := V)
  induction M generalizing b with
  | zero =>
    obtain ⟨C₀, hC₀, h₀⟩ := exists_quantizeTemperedCLM_eq_and_norm_le_of_specSet φ hb
    refine ⟨C₀, hC₀, fun {p} _ k f hf i ↦ ?_⟩
    obtain ⟨g, hg, hgn⟩ := h₀ k f hf
    exact ⟨g, by simpa [LineDeriv.iteratedLineDerivOp_zero] using hg, by simpa using hgn⟩
  | succ M ih =>
    obtain ⟨C₁, hC₁, h₁⟩ := ih hb
    choose C₂ hC₂ h₂ using fun j : Fin n ↦ ih (hb.spatialDeriv j)
    set CS : ℝ := ∑ j : Fin n, C₂ j
    have hCS : 0 ≤ CS := Finset.sum_nonneg fun j _ ↦ hC₂ j
    refine ⟨C₁ * CB * φ.rOut + CS, by have := φ.rOut_pos; positivity,
      fun {p} _ k f hf i ↦ ?_⟩
    set j := i (Fin.last M)
    have hR : (0 : ℝ) < 2 ^ k * φ.rOut := by have := φ.rOut_pos; positivity
    obtain ⟨f', hf', hf'n⟩ := hB hR f (hf.mono (compl_closedBall_subset_specSet φ k)) (eb j)
    have hf'v : IsVanishingOn (𝓕 (f' : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V))
        (specSet φ k) := by
      rw [← hf']
      exact isVanishingOn_fourier_lineDerivOp hf (eb j)
    obtain ⟨g₁, hg₁, hg₁n⟩ := h₁ k f' hf'v (Fin.init i)
    obtain ⟨g₂, hg₂, hg₂n⟩ := h₂ j k f hf (Fin.init i)
    refine ⟨g₁ + g₂, ?_, ?_⟩
    · have heb : (⇑eb ∘ i) (Fin.last M) = EuclideanSpace.single j (1 : ℝ) := by
        simp [eb, j, EuclideanSpace.basisFun_apply]
      have hinit : Fin.init (⇑eb ∘ i) = ⇑eb ∘ Fin.init i := rfl
      rw [LineDeriv.iteratedLineDerivOp_succ_right, heb, lineDerivOp_quantizeTemperedCLM,
        ← EuclideanSpace.basisFun_apply, hf', LineDeriv.iteratedLineDerivOp_add, hinit, hg₁, hg₂,
        Lp.toTemperedDistribution_add]
    · rw [eb.orthonormal.1 j, mul_one] at hf'n
      have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
      have hjCS : C₂ j ≤ CS := Finset.single_le_sum (fun l _ ↦ hC₂ l) (Finset.mem_univ j)
      calc ‖g₁ + g₂‖ ≤ ‖g₁‖ + ‖g₂‖ := norm_add_le _ _
        _ ≤ C₁ * ((2 : ℝ) ^ k) ^ M * (CB * (2 ^ k * φ.rOut) * ‖f‖) +
              CS * ((2 : ℝ) ^ k) ^ M * ‖f‖ :=
            add_le_add (hg₁n.trans (by gcongr)) (hg₂n.trans (by gcongr))
        _ = (C₁ * CB * φ.rOut * 2 ^ k + CS) * ((2 : ℝ) ^ k) ^ M * ‖f‖ := by ring
        _ ≤ ((C₁ * CB * φ.rOut + CS) * 2 ^ k) * ((2 : ℝ) ^ k) ^ M * ‖f‖ := by
            gcongr
            have := φ.rOut_pos
            nlinarith
        _ = (C₁ * CB * φ.rOut + CS) * ((2 : ℝ) ^ k) ^ (M + 1) * ‖f‖ := by rw [pow_succ]; ring

/-- **High output frequency, low input frequency (`j > k`).** On the `j`-th dyadic annulus the
reverse Bernstein inequality gains `2^{-jM}`, while `M`-th derivatives of `Op(b) f` grow at most
like `2^{kM}`. -/
private theorem exists_littlewoodPaleyBlock_quantizeTemperedCLM_eq_and_norm_le_of_lt
    (φ : ContDiffBump (0 : CoordinateSpace n)) (M : ℕ) {b : Symbol n V W 0} (hb : b.IsUniform) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {j k : ℕ}, k < j →
      ∀ f : Lp V p (volume : Measure (CoordinateSpace n)),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V)) (specSet φ k) →
      ∃ v : Lp W p (volume : Measure (CoordinateSpace n)),
        littlewoodPaleyBlock W φ j (b.quantizeTemperedCLM hb (f : 𝓢'(CoordinateSpace n, V))) = v ∧
        ‖v‖ ≤ K * ((2 : ℝ) ^ k / 2 ^ j) ^ M * ‖f‖ := by
  set eb := EuclideanSpace.basisFun (Fin n) ℝ
  obtain ⟨Cr, hCr, hrev⟩ :=
    eb.exists_norm_le_div_pow_mul_sum_norm_of_iteratedLineDerivOp_eq (F := W)
      (2 * φ.rOut / φ.rIn)
  obtain ⟨CD, hCD, hderB⟩ :=
    exists_iteratedLineDerivOp_quantizeTemperedCLM_eq_and_norm_le φ M hb
  obtain ⟨_, -, h₀⟩ := exists_quantizeTemperedCLM_eq_and_norm_le_of_specSet φ hb
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := W) φ
  set A : ℝ := 2 * Cr * n / φ.rIn
  have hA : 0 ≤ A := by have := φ.rIn_pos; positivity
  refine ⟨A ^ M * max CΔ 0 * CD, by positivity, fun {p} _ {j k} hkj f hf ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨bf, hbf, -⟩ := h₀ k f hf
  obtain ⟨w, hw, -⟩ := hΔ (j + 1) bf
  refine ⟨w, by rwa [hbf], ?_⟩
  have hR : (0 : ℝ) < 2 ^ j * φ.rIn := by have := φ.rIn_pos; positivity
  have hwv : IsVanishingOn (𝓕 (w : 𝓢'(CoordinateSpace n, W)) : 𝓢'(CoordinateSpace n, W))
      (ball 0 (2 ^ j * φ.rIn) ∪ (closedBall 0 (2 * φ.rOut / φ.rIn * (2 ^ j * φ.rIn)))ᶜ) := by
    rw [two_mul_rOut_div_rIn_mul, ← hw]
    simpa only [Set.compl_sdiff, Set.union_comm] using
      isVanishingOn_fourier_littlewoodPaleyBlock_succ φ j _
  choose y hy hyn using fun i : Fin M → Fin n ↦ hderB k f hf i
  choose z hz hzn using fun i : Fin M → Fin n ↦ hΔ (j + 1) (y i)
  have hder (i : Fin M → Fin n) : ∂^{⇑eb ∘ i} (w : 𝓢'(CoordinateSpace n, W)) = z i := by
    rw [← hw, ← hbf, ← littlewoodPaleyBlock_iteratedLineDerivOp, hy i, hz i]
  have hz' (i : Fin M → Fin n) :
      ‖z i‖ ≤ max CΔ 0 * (CD * ((2 : ℝ) ^ k) ^ M * ‖f‖) :=
    (hzn i).trans (mul_le_mul (le_max_left _ _) (hyn i) (norm_nonneg _) (le_max_right _ _))
  calc ‖w‖ ≤ (Cr / (2 ^ j * φ.rIn)) ^ M * ∑ i, ‖z i‖ := hrev M hR w z hwv hder
    _ ≤ (Cr / (2 ^ j * φ.rIn)) ^ M *
          ∑ _i : Fin M → Fin n, max CΔ 0 * (CD * ((2 : ℝ) ^ k) ^ M * ‖f‖) := by
        gcongr with i
        exact hz' i
    _ = A ^ M * max CΔ 0 * CD * ((2 : ℝ) ^ k / 2 ^ (j + 1)) ^ M * ‖f‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, A, div_pow, mul_pow, pow_succ]
        have := φ.rIn_pos
        push_cast
        field_simp

private theorem exists_littlewoodPaleyBlock_quantizeTemperedCLM_eq_and_norm_le_of_annulus_succ
    (φ : ContDiffBump (0 : CoordinateSpace n)) (M : ℕ) {b : Symbol n V W 0} (hb : b.IsUniform)
    {K : ℝ} (hK : 0 ≤ K)
    (h₁ : ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j k : ℕ) (f : Lp V p (volume : Measure (CoordinateSpace n))),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V))
        (specSet φ (k + 1)) →
      ∃ v : Lp W p (volume : Measure (CoordinateSpace n)),
        littlewoodPaleyBlock W φ j (b.quantizeTemperedCLM hb (f : 𝓢'(CoordinateSpace n, V))) = v ∧
        ‖v‖ ≤ K * ((2 : ℝ) ^ j / (2 ^ k * φ.rIn)) ^ M * ‖f‖)
    (h₂ : ∀ (i : Fin n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (j k : ℕ)
      (f : Lp V p (volume : Measure (CoordinateSpace n))),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V))
        (specSet φ (k + 1)) →
      ∃ v : Lp W p (volume : Measure (CoordinateSpace n)),
        littlewoodPaleyBlock W φ j
          ((spatialDeriv i b).quantizeTemperedCLM (hb.spatialDeriv i)
            (f : 𝓢'(CoordinateSpace n, V))) = v ∧
        ‖v‖ ≤ K * ((2 : ℝ) ^ j / (2 ^ k * φ.rIn)) ^ M * ‖f‖) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j k : ℕ)
      (f : Lp V p (volume : Measure (CoordinateSpace n))),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V))
        (specSet φ (k + 1)) →
      ∃ v : Lp W p (volume : Measure (CoordinateSpace n)),
        littlewoodPaleyBlock W φ j (b.quantizeTemperedCLM hb (f : 𝓢'(CoordinateSpace n, V))) = v ∧
        ‖v‖ ≤ K' * ((2 : ℝ) ^ j / (2 ^ k * φ.rIn)) ^ (M + 1) * ‖f‖ := by
  set eb := EuclideanSpace.basisFun (Fin n) ℝ
  obtain ⟨Crep, hCrep, hrep⟩ :=
    eb.exists_eq_sum_lineDerivOp_and_norm_le (F := V) (2 * φ.rOut / φ.rIn)
  obtain ⟨CB, hCB, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := CoordinateSpace n) (F := W)
  refine ⟨n * Crep * (CB * φ.rOut + 1) * K, by have := φ.rOut_pos; positivity,
    fun {p} _ j k f hf ↦ ?_⟩
  set R : ℝ := 2 ^ k * φ.rIn
  have hR : 0 < R := by have := φ.rIn_pos; positivity
  have hf' : IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V))
      (ball 0 R ∪ (closedBall 0 (2 * φ.rOut / φ.rIn * R))ᶜ) := by
    simpa only [R, two_mul_rOut_div_rIn_mul, specSet] using hf
  obtain ⟨h, hfh, hh⟩ := hrep hR f hf'
  have hhspec (i : Fin n) :
      IsVanishingOn (𝓕 (h i : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V))
        (specSet φ (k + 1)) := by
    simpa only [R, two_mul_rOut_div_rIn_mul, specSet] using (hh i).1
  choose y hy hyn using fun i : Fin n ↦ h₁ j k (h i) (hhspec i)
  have hR' : (0 : ℝ) < 2 ^ j * φ.rOut := by have := φ.rOut_pos; positivity
  choose y' hy' hy'n using fun i : Fin n ↦ hB hR' (y i)
    (by rw [← hy i]; exact isVanishingOn_fourier_littlewoodPaleyBlock φ j _) (eb i)
  choose z hz hzn using fun i : Fin n ↦ h₂ i j k (h i) (hhspec i)
  refine ⟨∑ i, (y' i - z i), ?_, ?_⟩
  · have hcomm (i : Fin n) :
        b.quantizeTemperedCLM hb (∂_{eb i} (h i : 𝓢'(CoordinateSpace n, V))) =
          ∂_{eb i} (b.quantizeTemperedCLM hb (h i : 𝓢'(CoordinateSpace n, V))) -
            (spatialDeriv i b).quantizeTemperedCLM (hb.spatialDeriv i)
              (h i : 𝓢'(CoordinateSpace n, V)) := by
      rw [EuclideanSpace.basisFun_apply, lineDerivOp_quantizeTemperedCLM]
      abel
    rw [hfh, map_sum, map_sum]
    simp_rw [hcomm, map_sub, littlewoodPaleyBlock_lineDerivOp, hy, hy', hz,
      Lp.toTemperedDistribution_sum, Lp.toTemperedDistribution_sub]
  · have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
    have hterm (i : Fin n) : ‖y' i - z i‖ ≤
        Crep * (CB * φ.rOut + 1) * K * ((2 : ℝ) ^ j / R) ^ (M + 1) * ‖f‖ := by
      have hy'i := hy'n i
      rw [eb.orthonormal.1 i, mul_one] at hy'i
      calc ‖y' i - z i‖ ≤ ‖y' i‖ + ‖z i‖ := norm_sub_le _ _
        _ ≤ CB * (2 ^ j * φ.rOut) * (K * ((2 : ℝ) ^ j / R) ^ M * ‖h i‖) +
              K * ((2 : ℝ) ^ j / R) ^ M * ‖h i‖ :=
            add_le_add (hy'i.trans (mul_le_mul_of_nonneg_left (hyn i) (by positivity))) (hzn i)
        _ = (CB * φ.rOut * 2 ^ j + 1) * (K * ((2 : ℝ) ^ j / R) ^ M) * ‖h i‖ := by ring
        _ ≤ (CB * φ.rOut + 1) * 2 ^ j * (K * ((2 : ℝ) ^ j / R) ^ M) * (Crep / R * ‖f‖) := by
            have hle : CB * φ.rOut * 2 ^ j + 1 ≤ (CB * φ.rOut + 1) * 2 ^ j := by linarith
            exact mul_le_mul (mul_le_mul_of_nonneg_right hle (by positivity)) (hh i).2
              (norm_nonneg _) (by have := φ.rOut_pos; positivity)
        _ = _ := by rw [pow_succ]; field_simp
    calc ‖∑ i, (y' i - z i)‖ ≤ ∑ i, ‖y' i - z i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, Crep * (CB * φ.rOut + 1) * K * ((2 : ℝ) ^ j / R) ^ (M + 1) * ‖f‖ :=
          Finset.sum_le_sum fun i _ ↦ hterm i
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/-- **Low output frequency, high input frequency (`j < k + 1`).** On the `(k + 1)`-st dyadic
annulus, writing `f = ∑_i ∂_i h_i` with `‖h_i‖_p = O(2^{-k} ‖f‖_p)` and commuting `∂_i` past
`Op(b)` gains `2^j / 2^k` at each step. -/
private theorem exists_littlewoodPaleyBlock_quantizeTemperedCLM_eq_and_norm_le_of_annulus
    (φ : ContDiffBump (0 : CoordinateSpace n)) (M : ℕ) {b : Symbol n V W 0} (hb : b.IsUniform) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j k : ℕ)
      (f : Lp V p (volume : Measure (CoordinateSpace n))),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V))
        (specSet φ (k + 1)) →
      ∃ v : Lp W p (volume : Measure (CoordinateSpace n)),
        littlewoodPaleyBlock W φ j (b.quantizeTemperedCLM hb (f : 𝓢'(CoordinateSpace n, V))) = v ∧
        ‖v‖ ≤ K * ((2 : ℝ) ^ j / (2 ^ k * φ.rIn)) ^ M * ‖f‖ := by
  induction M generalizing b with
  | zero =>
    obtain ⟨C₀, hC₀, h₀⟩ := exists_quantizeTemperedCLM_eq_and_norm_le_of_specSet φ hb
    obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := W) φ
    refine ⟨max CΔ 0 * C₀, by positivity, fun {p} _ j k f hf ↦ ?_⟩
    obtain ⟨bf, hbf, hbfn⟩ := h₀ (k + 1) f hf
    obtain ⟨w, hw, hwn⟩ := hΔ j bf
    refine ⟨w, by rwa [hbf], ?_⟩
    calc ‖w‖ ≤ max CΔ 0 * (C₀ * ‖f‖) :=
          hwn.trans (mul_le_mul (le_max_left _ _) hbfn (norm_nonneg _) (le_max_right _ _))
      _ = max CΔ 0 * C₀ * ((2 : ℝ) ^ j / (2 ^ k * φ.rIn)) ^ 0 * ‖f‖ := by ring
  | succ M ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := ih hb
    choose K₂ hK₂ h₂ using fun i : Fin n ↦ ih (hb.spatialDeriv i)
    set K : ℝ := K₁ + ∑ i : Fin n, K₂ i
    have hK₁le : K₁ ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hK₂ i)
    have hK₂le (i : Fin n) : K₂ i ≤ K :=
      (Finset.single_le_sum (fun l _ ↦ hK₂ l) (Finset.mem_univ i)).trans (le_add_of_nonneg_left hK₁)
    have hrIn := φ.rIn_pos
    exact exists_littlewoodPaleyBlock_quantizeTemperedCLM_eq_and_norm_le_of_annulus_succ φ M hb
      (add_nonneg hK₁ (Finset.sum_nonneg fun i _ ↦ hK₂ i))
      (fun j k f hf ↦ by
        obtain ⟨v, hv, hvn⟩ := h₁ j k f hf
        exact ⟨v, hv, hvn.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK₁le (by positivity)) (norm_nonneg f))⟩)
      (fun i _ _ j k f hf ↦ by
        obtain ⟨v, hv, hvn⟩ := h₂ i j k f hf
        exact ⟨v, hv, hvn.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hK₂le i) (by positivity)) (norm_nonneg f))⟩)

/-- **Off-diagonal decay of an order-zero operator between Littlewood–Paley blocks.** For any
`M : ℕ` and uniform symbol `b` of order `0`, there is `K ≥ 0`, independent of `1 ≤ p ≤ ∞`, `j`,
`k`, and `u`, such that whenever `Δ_k u = f ∈ Lᵖ`, the block `Δ_j (Op(b) f)` lies in `Lᵖ` with
`‖Δ_j (Op(b) f)‖_p ≤ K 2^{-M |j - k|} ‖f‖_p`. -/
private theorem exists_littlewoodPaleyBlock_quantizeTemperedCLM_eq_and_norm_le
    (φ : ContDiffBump (0 : CoordinateSpace n)) (M : ℕ) {b : Symbol n V W 0} (hb : b.IsUniform) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j k : ℕ) (u : 𝓢'(CoordinateSpace n, V))
      (f : Lp V p (volume : Measure (CoordinateSpace n))),
      littlewoodPaleyBlock V φ k u = f →
      ∃ v : Lp W p (volume : Measure (CoordinateSpace n)),
        littlewoodPaleyBlock W φ j (b.quantizeTemperedCLM hb (f : 𝓢'(CoordinateSpace n, V))) = v ∧
        ‖v‖ ≤ K * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
  obtain ⟨K₁, hK₁, h₁⟩ :=
    exists_littlewoodPaleyBlock_quantizeTemperedCLM_eq_and_norm_le_of_lt φ M hb
  obtain ⟨K₂, hK₂, h₂⟩ :=
    exists_littlewoodPaleyBlock_quantizeTemperedCLM_eq_and_norm_le_of_annulus φ M hb
  obtain ⟨C₀, hC₀, h₀⟩ := exists_quantizeTemperedCLM_eq_and_norm_le_of_specSet φ hb
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := W) φ
  set K₀ : ℝ := max CΔ 0 * C₀
  have hrIn := φ.rIn_pos
  refine ⟨K₁ + K₂ * (2 / φ.rIn) ^ M + K₀, by positivity, fun {p} _ j k u f hf ↦ ?_⟩
  have hspec : IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, V)) : 𝓢'(CoordinateSpace n, V))
      (specSet φ k) := hf ▸ isVanishingOn_specSet_littlewoodPaleyBlock φ k u
  have hK (K : ℝ) (hKK : K ≤ K₁ + K₂ * (2 / φ.rIn) ^ M + K₀) :
      K * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ ≤
        (K₁ + K₂ * (2 / φ.rIn) ^ M + K₀) * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
    gcongr
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · obtain ⟨v, hv, hvn⟩ := h₁ hkj f hspec
    refine ⟨v, hv, (hvn.trans_eq ?_).trans
      (hK K₁ (by linarith [show 0 ≤ K₂ * (2 / φ.rIn) ^ M + K₀ by positivity]))⟩
    rw [Real.pow_div_pow_pow_eq_rpow_of_le two_pos hkj.le]
  · obtain ⟨bf, hbf, hbfn⟩ := h₀ k f hspec
    obtain ⟨v, hv, hvn⟩ := hΔ k bf
    refine ⟨v, by rwa [hbf], ?_⟩
    have hv₀ : ‖v‖ ≤ K₀ * (2 : ℝ) ^ (-(M * |(k : ℝ) - k|)) * ‖f‖ := by
      simpa [K₀, mul_assoc] using
        hvn.trans (mul_le_mul (le_max_left _ _) hbfn (norm_nonneg _) (le_max_right _ _))
    exact hv₀.trans (hK K₀ (by linarith [show 0 ≤ K₂ * (2 / φ.rIn) ^ M by positivity]))
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨v, hv, hvn⟩ := h₂ j k f hspec
    refine ⟨v, hv, (hvn.trans_eq ?_).trans
      (hK (K₂ * (2 / φ.rIn) ^ M) (by linarith [show 0 ≤ K₀ by positivity]))⟩
    rw [abs_sub_comm, ← Real.pow_div_pow_pow_eq_rpow_of_le two_pos hjk.le, div_pow, div_pow,
      div_pow, mul_pow, pow_succ]
    field_simp
    ring

/-! ### Boundedness on Besov spaces at order zero -/

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] [FiniteDimensional ℂ W] in
private theorem lp_exists_hasSum_and_norm_le_of_summable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (x : lp (fun _ : ℕ ↦ Lp V p (volume : Measure (CoordinateSpace n))) q) {a : ℤ → ℝ}
    (ha0 : ∀ d, 0 ≤ a d) (ha : Summable a) {c : ℝ} (hc : 0 ≤ c)
    (w : ℕ → ℕ → Lp W p (volume : Measure (CoordinateSpace n)))
    (hw : ∀ j k, ‖w j k‖ ≤ c * a ((k : ℤ) - j) * ‖x k‖) :
    ∃ y : lp (fun _ : ℕ ↦ Lp W p (volume : Measure (CoordinateSpace n))) q,
      (∀ j, HasSum (w j) (y j)) ∧ ‖y‖ ≤ c * (∑' d, a d) * ‖x‖ := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hca : 0 ≤ c * ∑' d, a d := mul_nonneg hc (tsum_nonneg ha0)
  by_cases hnt : Nontrivial (Lp W p (volume : Measure (CoordinateSpace n)))
  · obtain ⟨g₀, hg₀⟩ := @exists_ne _ hnt 0
    set u₀ : Lp W p (volume : Measure (CoordinateSpace n)) := ‖g₀‖⁻¹ • g₀
    have hu₀ : ‖u₀‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (norm_ne_zero_iff.2 hg₀)]
    have hmemW : Memℓp (fun k ↦ ‖x k‖ • u₀) q :=
      ((lp.memℓp x).norm).mono fun k ↦ by simp [norm_smul, hu₀]
    set xW : lp (fun _ : ℕ ↦ Lp W p (volume : Measure (CoordinateSpace n))) q := ⟨_, hmemW⟩
    have hxWk (k : ℕ) : ‖xW k‖ = ‖x k‖ := by simp [xW, norm_smul, hu₀]
    have hxW : ‖xW‖ ≤ ‖x‖ := lp.norm_mono hq0 fun k ↦ (hxWk k).le
    obtain ⟨y, hyj, hyn⟩ := lp.exists_hasSum_and_norm_le_of_summable xW ha0 ha hc w fun j k ↦ by
      rw [hxWk]; exact hw j k
    exact ⟨y, hyj, hyn.trans (mul_le_mul_of_nonneg_left hxW hca)⟩
  · rw [not_nontrivial_iff_subsingleton] at hnt
    refine ⟨0, fun j ↦ ?_, by rw [norm_zero]; positivity⟩
    have h0 : w j = 0 := funext fun _ ↦ Subsingleton.elim _ _
    rw [lp.coeFn_zero, Pi.zero_apply, h0]
    exact hasSum_zero

/-- **Order-zero uniform symbols are bounded on all Besov spaces, uniformly in `p` and `q`.** For
every bump function `φ`, real `s`, and uniform symbol `b` of order `0`, there is `C ≥ 0` such that
for all `1 ≤ p, q ≤ ∞` and `u ∈ B^s_{p,q}(ℝⁿ; V)`, `Op(b) u` lies in `B^s_{p,q}(ℝⁿ; W)` with
`‖Op(b) u‖ ≤ C ‖u‖`. -/
private theorem exists_toDistr_eq_quantizeTemperedCLM_and_norm_le
    (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) {b : Symbol n V W 0} (hb : b.IsUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace V φ s p q),
      ∃ v : BesovSpace W φ s p q,
        v.toDistr = b.quantizeTemperedCLM hb u.toDistr ∧ ‖v‖ ≤ C * ‖u‖ := by
  set N : ℕ := ⌊|s|⌋₊ + 1
  have hN : |s| < N := by push_cast [N]; exact Nat.lt_floor_add_one _
  set r : ℝ := 2 ^ (|s| - N)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  obtain ⟨K, hK, hblock⟩ := exists_littlewoodPaleyBlock_quantizeTemperedCLM_eq_and_norm_le φ N hb
  refine ⟨K * ∑' d : ℤ, r ^ d.natAbs, by positivity, fun {p q} _ _ u ↦ ?_⟩
  set c : ℕ → ℂ := fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)
  choose v hv hvn using fun j k ↦
    hblock j k u.toDistr (u.block k) (u.coe_block k).symm
  have hentry (j k : ℕ) :
      ‖c j • v j k‖ ≤ K * r ^ ((k : ℤ) - j).natAbs * ‖u.weightedBlocks k‖ := by
    have hexp : s * j + -(N * |(j : ℝ) - k|) ≤ (|s| - N) * |(j : ℝ) - k| + s * k := by
      have := (le_abs_self (s * (j - k))).trans_eq (abs_mul s ((j : ℝ) - k))
      nlinarith
    have hr : r ^ ((k : ℤ) - j).natAbs = (2 : ℝ) ^ ((|s| - N) * |(j : ℝ) - k|) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, Nat.cast_natAbs, Int.cast_abs,
        abs_sub_comm, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    rw [norm_smul, Complex.norm_of_nonneg (by positivity), u.norm_weightedBlocks_apply k, hr]
    calc (2 : ℝ) ^ (s * j) * ‖v j k‖
        ≤ (2 : ℝ) ^ (s * j) * (K * (2 : ℝ) ^ (-(N * |(j : ℝ) - k|)) * ‖u.block k‖) := by
          gcongr
          exact hvn j k
      _ = K * (2 : ℝ) ^ (s * j + -(N * |(j : ℝ) - k|)) * ‖u.block k‖ := by
          rw [Real.rpow_add two_pos]; ring
      _ ≤ K * (2 : ℝ) ^ ((|s| - N) * |(j : ℝ) - k| + s * k) * ‖u.block k‖ := by
          gcongr; exact one_le_two
      _ = _ := by rw [Real.rpow_add two_pos]; ring
  have hsum : Summable fun d : ℤ ↦ r ^ d.natAbs :=
    summable_int_iff_summable_nat_and_neg.2
      ⟨by simpa using summable_geometric_of_lt_one hr0 hr1,
        by simpa using summable_geometric_of_lt_one hr0 hr1⟩
  obtain ⟨B, hBj, hBn⟩ := lp_exists_hasSum_and_norm_le_of_summable u.weightedBlocks
    (fun d ↦ by positivity) hsum hK (fun j k ↦ c j • v j k) hentry
  -- The tempered distribution of `B j` is `2^{js} Δ_j (Op(b) u)`, the limit of
  -- `2^{js} Δ_j (Op(b) ∑_{k < M} Δ_k u)`.
  have hB (j : ℕ) : (B j : 𝓢'(CoordinateSpace n, W)) =
      c j • littlewoodPaleyBlock W φ j (b.quantizeTemperedCLM hb u.toDistr) := by
    have h₁ := ((Lp.toTemperedDistributionCLM W volume p).continuous.tendsto _).comp
      (hBj j).tendsto_sum_nat
    have h₂ :=
      ((c j • (littlewoodPaleyBlock W φ j ∘L b.quantizeTemperedCLM hb)).continuous.tendsto _).comp
        (tendsto_sum_littlewoodPaleyBlock φ u.toDistr)
    refine tendsto_nhds_unique h₁ (h₂.congr fun M ↦ ?_)
    simp only [Function.comp_apply, map_sum, map_smul, smul_apply,
      ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply]
    simp_rw [← u.coe_block, hv]
  refine ⟨⟨b.quantizeTemperedCLM hb u.toDistr, B, hB⟩, rfl, ?_⟩
  rw [← BesovSpace.norm_weightedBlocks, ← u.norm_weightedBlocks]
  exact hBn

private def quantizeBesovOrderZero (φ : ContDiffBump (0 : CoordinateSpace n))
    {b : Symbol n V W 0} (hb : b.IsUniform) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    BesovSpace V φ s p q →L[ℂ] BesovSpace W φ s p q :=
  have hC := (exists_toDistr_eq_quantizeTemperedCLM_and_norm_le φ s hb).choose_spec
  LinearMap.mkContinuous
    { toFun u := (hC.2 u).choose
      map_add' u v := BesovSpace.ext <| by
        rw [(hC.2 (u + v)).choose_spec.1, BesovSpace.toDistr_add, BesovSpace.toDistr_add, map_add,
          (hC.2 u).choose_spec.1, (hC.2 v).choose_spec.1]
      map_smul' c u := BesovSpace.ext <| by
        rw [(hC.2 (c • u)).choose_spec.1, BesovSpace.toDistr_smul, RingHom.id_apply,
          BesovSpace.toDistr_smul, map_smul, (hC.2 u).choose_spec.1] }
    _ fun u ↦ (hC.2 u).choose_spec.2

private theorem toDistr_quantizeBesovOrderZero (φ : ContDiffBump (0 : CoordinateSpace n))
    {b : Symbol n V W 0} (hb : b.IsUniform) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (u : BesovSpace V φ s p q) :
    (quantizeBesovOrderZero φ hb s p q u).toDistr = b.quantizeTemperedCLM hb u.toDistr :=
  ((exists_toDistr_eq_quantizeTemperedCLM_and_norm_le φ s hb).choose_spec.2 u).choose_spec.1

end OrderZero

/-! ### Boundedness on Besov spaces for arbitrary order `m ∈ ℝ` -/

section GeneralOrder

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [CompleteSpace W] {m m' : ℝ}

/-- **Besov mapping of uniform pseudodifferential operators.** The quantization `Op(a)` of a
uniform symbol `a` of order `m ∈ ℝ` maps the inhomogeneous Besov space `B^s_{p,q}(ℝⁿ; V)` boundedly
into `B^{s-m}_{p,q}(ℝⁿ; W)` for every real `s` and every `1 ≤ p, q ≤ ∞`.

As a tempered distribution, `Op(a) u` agrees with `TauCeti.Symbol.quantizeTemperedCLM`
(`TauCeti.Symbol.toDistr_quantizeBesov`). -/
def quantizeBesov (a : Symbol n V W m) (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    BesovSpace V φ s p q →L[ℂ] BesovSpace W φ (s - m) p q :=
  quantizeBesovOrderZero φ
      (b := Symbol.inclusion (by linarith : m + -m ≤ 0) (a.comp (besselPotential (-m))))
      ((ha.comp (isUniform_besselPotential (-m))).inclusion (by linarith)) (s - m) p q ∘L
    (BesovSpace.besselPotentialEquiv V φ p q m rfl).toContinuousLinearMap

/-- The Besov operator `TauCeti.Symbol.quantizeBesov` agrees with
`TauCeti.Symbol.quantizeTemperedCLM` on the underlying tempered distributions. -/
@[simp]
theorem toDistr_quantizeBesov (a : Symbol n V W m) (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (u : BesovSpace V φ s p q) :
    (a.quantizeBesov φ ha s p q u).toDistr = a.quantizeTemperedCLM ha u.toDistr := by
  rw [quantizeBesov, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    toDistr_quantizeBesovOrderZero, BesovSpace.toDistr_besselPotentialEquiv,
    quantizeTemperedCLM_inclusion (ha.comp (isUniform_besselPotential (-m))),
    ← quantizeTemperedCLM_besselPotential a ha (-m),
    besselPotential_besselPotential_apply, add_neg_cancel, besselPotential_zero,
    ContinuousLinearMap.id_apply]

/-- At order `0`, `TauCeti.Symbol.quantizeBesov` is bounded uniformly in `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_quantizeBesov_orderZero_le (b : Symbol n V W 0)
    (φ : ContDiffBump (0 : CoordinateSpace n)) (hb : b.IsUniform) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
      ‖b.quantizeBesov φ hb s p q‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_toDistr_eq_quantizeTemperedCLM_and_norm_le φ s hb
  refine ⟨C, hC0, fun p q _ _ ↦ ContinuousLinearMap.opNorm_le_bound _ hC0 fun u ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := hC u
  have heq : b.quantizeBesov φ hb s p q u = BesovSpace.inclusion W φ p (by linarith) le_rfl v :=
    BesovSpace.ext <| by rw [toDistr_quantizeBesov, BesovSpace.toDistr_inclusion, hv]
  rw [heq]
  exact (BesovSpace.norm_inclusion_le _ _ v).trans hvn

/-- Two uniform symbols with equal coefficients induce the same operator on Besov spaces. -/
theorem quantizeBesov_congr {a b : Symbol n V W m} (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) (hb : b.IsUniform) (h : a.coefficient = b.coefficient) (s : ℝ)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    a.quantizeBesov φ ha s p q = b.quantizeBesov φ hb s p q := by
  ext1 u
  exact BesovSpace.ext (by simp [quantizeTemperedCLM_congr ha hb h])

/-- `TauCeti.Symbol.quantizeBesov` is additive in the symbol. -/
theorem quantizeBesov_add {a b : Symbol n V W m} (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    (a + b).quantizeBesov φ (ha.add hb) s p q =
      a.quantizeBesov φ ha s p q + b.quantizeBesov φ hb s p q := by
  ext1 u
  exact BesovSpace.ext (by simp [quantizeTemperedCLM_add ha hb])

/-- `TauCeti.Symbol.quantizeBesov` is homogeneous in the symbol. -/
theorem quantizeBesov_smul {a : Symbol n V W m} (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) (c : ℂ) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    (c • a).quantizeBesov φ (ha.smul c) s p q = c • a.quantizeBesov φ ha s p q := by
  ext1 u
  exact BesovSpace.ext (by simp [quantizeTemperedCLM_smul ha c])

/-- The zero symbol quantizes to `0` on Besov spaces. -/
@[simp]
theorem quantizeBesov_zero (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    (0 : Symbol n V W m).quantizeBesov φ isUniform_zero s p q = 0 := by
  ext1 u
  exact BesovSpace.ext (by simp)

/-- `TauCeti.Symbol.quantizeBesov` commutes with negation of the symbol. -/
theorem quantizeBesov_neg {a : Symbol n V W m} (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    (-a).quantizeBesov φ ha.neg s p q = -a.quantizeBesov φ ha s p q := by
  ext1 u
  exact BesovSpace.ext (by simp [quantizeTemperedCLM_neg ha])

/-- `TauCeti.Symbol.quantizeBesov` commutes with subtraction of uniform symbols. -/
theorem quantizeBesov_sub {a b : Symbol n V W m} (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    (a - b).quantizeBesov φ (ha.sub hb) s p q =
      a.quantizeBesov φ ha s p q - b.quantizeBesov φ hb s p q := by
  ext1 u
  exact BesovSpace.ext (by simp [quantizeTemperedCLM_sub ha hb])

/-- `TauCeti.Symbol.quantizeBesov` commutes with finite sums of uniform symbols. -/
theorem quantizeBesov_sum {ι : Type*} (S : Finset ι) (a : ι → Symbol n V W m)
    (φ : ContDiffBump (0 : CoordinateSpace n)) (ha : ∀ i, (a i).IsUniform) (s : ℝ)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    (∑ i ∈ S, a i).quantizeBesov φ (IsUniform.sum fun i _ ↦ ha i) s p q =
      ∑ i ∈ S, (a i).quantizeBesov φ (ha i) s p q := by
  ext1 u
  refine BesovSpace.ext ?_
  rw [toDistr_quantizeBesov, quantizeTemperedCLM_sum S a ha, sum_apply, sum_apply]
  have hdist (T : Finset ι) (f : ι → BesovSpace W φ (s - m) p q) :
      (∑ i ∈ T, f i).toDistr = ∑ i ∈ T, (f i).toDistr := by
    have h := map_sum (BesovSpace.toDistrCLM W φ (s - m) p q) f T
    simp only [BesovSpace.toDistrCLM_apply] at h
    exact h
  rw [hdist]
  exact Finset.sum_congr rfl fun i _ ↦ (toDistr_quantizeBesov (a i) φ (ha i) s p q u).symm

/-- Increasing the nominal symbol order `m ≤ m'` composes `quantizeBesov` with the Besov inclusion
`B^{s-m}_{p,q} ⊆ B^{s-m'}_{p,q}`. -/
theorem quantizeBesov_symbolInclusion (a : Symbol n V W m) (hm : m ≤ m')
    (φ : ContDiffBump (0 : CoordinateSpace n)) (ha : a.IsUniform) (s : ℝ) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace V φ s p q) :
    (Symbol.inclusion hm a).quantizeBesov φ (ha.inclusion hm) s p q u =
      BesovSpace.inclusion W φ p (by linarith) le_rfl (a.quantizeBesov φ ha s p q u) :=
  BesovSpace.ext (by simp [quantizeTemperedCLM_inclusion ha hm])

/-- `quantizeBesov` commutes with the Besov scale inclusions `B^s_{p,q} ⊆ B^{s'}_{p,q'}` for
`s' ≤ s` and `q ≤ q'`. -/
theorem quantizeBesov_inclusion (a : Symbol n V W m) (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) {s s' : ℝ} {p q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ q')]
    (hs : s' ≤ s) (hq : q ≤ q') (u : BesovSpace V φ s p q) :
    a.quantizeBesov φ ha s' p q' (BesovSpace.inclusion V φ p hs hq u) =
      BesovSpace.inclusion W φ p (by linarith) hq (a.quantizeBesov φ ha s p q u) :=
  BesovSpace.ext (by simp)

/-- `quantizeBesov` commutes with changing the Littlewood–Paley bump function via
`TauCeti.BesovSpace.bumpEquiv`. -/
theorem bumpEquiv_quantizeBesov (a : Symbol n V W m)
    (φ φ' : ContDiffBump (0 : CoordinateSpace n)) (ha : a.IsUniform) (s : ℝ) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace V φ s p q) :
    BesovSpace.bumpEquiv W φ φ' (s - m) p q (a.quantizeBesov φ ha s p q u) =
      a.quantizeBesov φ' ha s p q (BesovSpace.bumpEquiv V φ φ' s p q u) :=
  BesovSpace.ext (by simp)

/-! ### Hölder–Zygmund order shift (`p = q = ∞`) -/

/-- **Hölder–Zygmund mapping into `C_b^{0,α}`.** A uniform symbol `a` of order `m` defines a
bounded real-linear operator from the Zygmund space `𝒞^s = B^s_{∞,∞}` into the bounded `α`-Hölder
space `HolderSpace α (CoordinateSpace n) W` whenever `0 < α < 1` and `(α : ℝ) ≤ s - m` (in
particular when `s - m = α`, i.e., `s = m + α`). -/
def quantizeZygmundToHolder (a : Symbol n V W m) (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) {s : ℝ} {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) (hs : (α : ℝ) ≤ s - m) :
    BesovSpace V φ s ∞ ∞ →L[ℝ] HolderSpace α (CoordinateSpace n) W :=
  (BesovSpace.toHolderSpace W φ hα0 hα1).comp
    ((BesovSpace.inclusion W φ ∞ hs le_rfl ∘L a.quantizeBesov φ ha s ∞ ∞).restrictScalars ℝ)

/-- The bounded `α`-Hölder function `a.quantizeZygmundToHolder φ ha hα0 hα1 hs u` represents the
tempered distribution `Op(a) u`. -/
@[simp]
theorem toLpTop_quantizeZygmundToHolder (a : Symbol n V W m)
    (φ : ContDiffBump (0 : CoordinateSpace n)) (ha : a.IsUniform) {s : ℝ} {α : ℝ≥0} (hα0 : 0 < α)
    (hα1 : α < 1) (hs : (α : ℝ) ≤ s - m) (u : BesovSpace V φ s ∞ ∞) :
    (toLpTop volume ℂ
        (a.quantizeZygmundToHolder φ ha hα0 hα1 hs u).toBoundedContinuousFunction :
        𝓢'(CoordinateSpace n, W)) =
      a.quantizeTemperedCLM ha u.toDistr := by
  simp [quantizeZygmundToHolder]

/-- **Hölder–Zygmund mapping into `C_b^{k,α}`** (Taylor, Lecture I, (3.34)). A uniform symbol `a`
of order `m` defines a bounded real-linear operator from the Zygmund space `𝒞^s = B^s_{∞,∞}` into
`CkHolderSpace k α (CoordinateSpace n) W` whenever `0 < α < 1` and `(k : ℝ) + α ≤ s - m` (in
particular when `s - m = k + α` is any positive non-integer). -/
def quantizeZygmundToCkHolder (a : Symbol n V W m) (φ : ContDiffBump (0 : CoordinateSpace n))
    (ha : a.IsUniform) (k : ℕ) {s : ℝ} {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (hs : (k : ℝ) + α ≤ s - m) :
    BesovSpace V φ s ∞ ∞ →L[ℝ] CkHolderSpace k α (CoordinateSpace n) W :=
  (BesovSpace.toCkHolderSpace W φ k hα0 hα1).comp
    ((BesovSpace.inclusion W φ ∞ hs le_rfl ∘L a.quantizeBesov φ ha s ∞ ∞).restrictScalars ℝ)

/-- The bounded `C^{k,α}` function `a.quantizeZygmundToCkHolder φ ha k hα0 hα1 hs u` represents
the tempered distribution `Op(a) u`. -/
@[simp]
theorem toLpTop_quantizeZygmundToCkHolder (a : Symbol n V W m)
    (φ : ContDiffBump (0 : CoordinateSpace n)) (ha : a.IsUniform) (k : ℕ) {s : ℝ} {α : ℝ≥0}
    (hα0 : 0 < α) (hα1 : α < 1) (hs : (k : ℝ) + α ≤ s - m) (u : BesovSpace V φ s ∞ ∞) :
    (toLpTop volume ℂ
        (a.quantizeZygmundToCkHolder φ ha k hα0 hα1 hs u).toBoundedContinuousFunction :
        𝓢'(CoordinateSpace n, W)) =
      a.quantizeTemperedCLM ha u.toDistr := by
  simp [quantizeZygmundToCkHolder]

end GeneralOrder

end Symbol

end TauCeti

namespace TemperedDistribution

open TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [CompleteSpace W] {φ : ContDiffBump (0 : CoordinateSpace n)} {m s : ℝ} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Uniform pseudodifferential operators preserve the Besov scale with shift `-m`.** If
`u ∈ B^s_{p,q}(ℝⁿ; V)` (`1 ≤ p, q ≤ ∞`) and `a` is a uniform symbol of order `m`, then
`Op(a) u ∈ B^{s-m}_{p,q}(ℝⁿ; W)`. -/
theorem MemBesov.quantizeTemperedCLM {u : 𝓢'(CoordinateSpace n, V)} (hu : u.MemBesov φ s p q)
    {a : Symbol n V W m} (ha : a.IsUniform) :
    (a.quantizeTemperedCLM ha u).MemBesov φ (s - m) p q := by
  have h := (a.quantizeBesov φ ha s p q hu.toBesovSpace).memBesov_toDistr
  rwa [Symbol.toDistr_quantizeBesov, hu.toDistr_toBesovSpace] at h

end TemperedDistribution
