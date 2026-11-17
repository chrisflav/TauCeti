/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Topology.Baire.CompleteMetrizable
public import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Strong operator topology: composition, local bounds, and joint continuity

Composition preserves pointwise convergence when the outer operators are uniformly bounded
in operator norm. Only that family needs a bound, and neither space needs completeness.
For sequences on a barrelled seminormed space (in particular, any Banach space) the bound
follows automatically from Banach–Steinhaus (`ContinuousLinearMap.exists_norm_le_of_bddAbove`).

For a family `T : X → E →SL[σ] F` of continuous semilinear maps on a topological space `X`:

* Joint continuity of `(x, v) ↦ T x v` is equivalent to strong continuity together with local
  uniform operator-norm boundedness (`ContinuousLinearMap.continuous_uncurry_iff`, and its
  pointwise form `ContinuousLinearMap.continuousAt_uncurry_iff`), requiring no completeness or
  barrelledness on `E`.
* If `x ↦ ‖T x v‖` is lower semicontinuous for every `v` (in particular, when `T` is strongly
  continuous), then `x ↦ ‖T x‖` is lower semicontinuous
  (`ContinuousLinearMap.lowerSemicontinuous_opNorm`), so on a nonempty Baire space `T` is
  uniformly operator-norm bounded on some nonempty open set
  (`ContinuousLinearMap.exists_nonempty_open_norm_le`), with no completeness or barrelledness
  on `E`.
* When `E` is barrelled (automatically satisfied when `E` is complete), Banach–Steinhaus supplies
  operator-norm bounds along any countably generated filter
  (`ContinuousLinearMap.exists_eventually_norm_le_of_isCountablyGenerated`), on every compact
  subset of `X` under upper semicontinuity or strong continuity
  (`ContinuousLinearMap.exists_norm_le_of_isCompact_upperSemicontinuousOn`,
  `ContinuousLinearMap.exists_norm_le_of_isCompact_continuousOn`), on compact neighborhoods when
  `X` is weakly locally compact and `x ↦ ‖T x v‖` is upper semicontinuous
  (`ContinuousLinearMap.exists_compact_nhds_norm_le`), and on neighborhoods at any point whose
  neighborhood filter is countably generated under upper semicontinuity at that point
  (`ContinuousLinearMap.exists_nhds_norm_le_of_isCountablyGenerated`). In both regimes strong
  continuity upgrades automatically to joint continuity (including the pointwise equivalence
  `ContinuousLinearMap.continuousAt_uncurry_iff_of_isCountablyGenerated`).

On a complete real or complex Hilbert space, orthogonal projections form a strongly closed
set. Their uniform norm bound lets idempotence pass to the strong limit; self-adjointness
passes through inner products. The closedness statement uses Mathlib's
`PointwiseConvergenceCLM` copy, leaving the norm topology on continuous linear maps unchanged.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), Lemma 2.3 and Remark 2.4.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*, §2.4.
-/

public section

open Filter Topology

namespace ContinuousLinearMap

section Semilinear

variable {𝕜 𝕜₂ E F X : Type*} [NontriviallyNormedField 𝕜]
  [NontriviallyNormedField 𝕜₂] {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- **Banach–Steinhaus theorem for barrelled seminormed spaces.** A pointwise bounded family of
continuous semilinear maps from a barrelled seminormed space (in particular, from any Banach space)
is uniformly bounded in operator norm by a nonnegative constant. -/
theorem exists_norm_le_of_bddAbove [BarrelledSpace 𝕜 E] {ι : Type*} {T : ι → E →SL[σ] F}
    (hT : ∀ x : E, BddAbove (Set.range fun i ↦ ‖T i x‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖T i‖ ≤ C :=
  ((NormedSpace.equicontinuous_tfae T).out 7 3).mpr <|
    (norm_withSeminorms 𝕜₂ F).banach_steinhaus fun _ x ↦ hT x

/-- **Banach–Steinhaus along a countably generated filter.** For any countably generated filter
`l` (for example `atTop` on `ℕ`, or `𝓝 x₀` at a point with a countable neighborhood basis), a
family of continuous semilinear maps from a barrelled seminormed space that is pointwise eventually
bounded along `l` is eventually uniformly bounded in operator norm along `l`. -/
theorem exists_eventually_norm_le_of_isCountablyGenerated [BarrelledSpace 𝕜 E]
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {T : ι → E →SL[σ] F}
    (hT : ∀ v : E, ∃ M : ℝ, ∀ᶠ i in l, ‖T i v‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in l, ‖T i‖ ≤ C := by
  obtain ⟨u, hu⟩ := l.exists_antitone_basis
  by_contra! h
  have hstep : ∀ n : ℕ, ∃ i ∈ u n, (n : ℝ) < ‖T i‖ := fun n ↦ by
    by_contra! hle
    exact h n (Nat.cast_nonneg n) (eventually_of_mem (hu.mem n) fun i hi ↦ not_lt.mpr (hle i hi))
  choose x hxu hxn using hstep
  have hx : Tendsto x atTop l := hu.tendsto_right_iff.mpr fun n _ ↦
    eventually_atTop.mpr ⟨n, fun k hk ↦ hu.antitone hk (hxu k)⟩
  obtain ⟨C, -, hC⟩ := exists_norm_le_of_bddAbove (T := fun k ↦ T (x k)) fun v ↦ by
    obtain ⟨M, hM⟩ := hT v
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hx.eventually hM)
    refine ⟨max M (((Finset.range N).sup fun k ↦ ‖T (x k) v‖₊ : NNReal) : ℝ),
      Set.forall_mem_range.mpr fun k ↦ ?_⟩
    by_cases hk : k < N
    · have hle : ‖T (x k) v‖₊ ≤ (Finset.range N).sup fun j ↦ ‖T (x j) v‖₊ :=
        Finset.le_sup (f := fun j ↦ ‖T (x j) v‖₊) (Finset.mem_range.mpr hk)
      exact le_trans (by exact_mod_cast hle) (le_max_right _ _)
    · exact (hN k (not_lt.mp hk)).trans (le_max_left _ _)
  obtain ⟨n, hn⟩ := exists_nat_gt C
  exact hn.not_ge ((hxn n).le.trans (hC n))

/-- A pointwise convergent sequence of continuous semilinear maps on a barrelled seminormed space
(in particular, any Banach space) is uniformly norm bounded. -/
theorem exists_norm_le_of_tendsto_pointwise [BarrelledSpace 𝕜 E]
    {T : ℕ → E →SL[σ] F} {f : E → F}
    (hT : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (f x))) :
    ∃ C : ℝ, ∀ n, ‖T n‖ ≤ C := by
  obtain ⟨C, -, hC⟩ := exists_norm_le_of_bddAbove (T := T) fun x ↦ by
    obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ (hT x)).exists_norm_le
    exact ⟨M, Set.forall_mem_range.mpr fun n ↦ hM _ (Set.mem_range_self n)⟩
  exact ⟨C, hC⟩

variable [TopologicalSpace X]

/-- If `x ↦ ‖T x v‖` is lower semicontinuous for every `v` (for instance, when `T` is strongly
continuous), then the operator norm `x ↦ ‖T x‖` is lower semicontinuous. -/
theorem lowerSemicontinuous_opNorm {T : X → E →SL[σ] F}
    (hT : ∀ v : E, LowerSemicontinuous fun x ↦ ‖T x v‖) :
    LowerSemicontinuous fun x ↦ ‖T x‖ := by
  refine lowerSemicontinuous_iff_isClosed_preimage.mpr fun C ↦ ?_
  by_cases hC : 0 ≤ C
  · have hEq : (fun x ↦ ‖T x‖) ⁻¹' Set.Iic C =
        ⋂ v : E, (fun x ↦ ‖T x v‖) ⁻¹' Set.Iic (C * ‖v‖) := by
      ext x
      simp [opNorm_le_iff hC]
    rw [hEq]
    exact isClosed_iInter fun v ↦ (hT v).isClosed_preimage _
  · have hEq : (fun x ↦ ‖T x‖) ⁻¹' Set.Iic C = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx ↦ hC ((norm_nonneg _).trans hx)
    rw [hEq]
    exact isClosed_empty

/-- On a nonempty Baire space, a family of continuous semilinear maps with lower semicontinuous
pointwise norms `x ↦ ‖T x v‖` (in particular, any strongly continuous family) is uniformly
operator-norm bounded on some nonempty open set, with no completeness or barrelledness on `E`. -/
theorem exists_nonempty_open_norm_le [BaireSpace X] [Nonempty X] {T : X → E →SL[σ] F}
    (hT : ∀ v : E, LowerSemicontinuous fun x ↦ ‖T x v‖) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ‖T x‖ ≤ C := by
  have hlsc := lowerSemicontinuous_opNorm hT
  have huniv : ⋃ n : ℕ, (fun x ↦ ‖T x‖) ⁻¹' Set.Iic (n : ℝ) = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr (exists_nat_ge ‖T x‖)
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed
    (fun n : ℕ ↦ hlsc.isClosed_preimage n) huniv
  refine ⟨interior ((fun x ↦ ‖T x‖) ⁻¹' Set.Iic (n : ℝ)), isOpen_interior, hn,
    n, Nat.cast_nonneg n, fun x hx ↦ interior_subset hx⟩

/-- **Uniform boundedness on compact sets (upper semicontinuous form).** A family of continuous
semilinear maps from a barrelled seminormed space (in particular, any Banach space) whose pointwise
norms `x ↦ ‖T x v‖` are upper semicontinuous on a compact set `K` has a uniform nonnegative
operator-norm bound on `K`. -/
theorem exists_norm_le_of_isCompact_upperSemicontinuousOn [BarrelledSpace 𝕜 E]
    {T : X → E →SL[σ] F} {K : Set X} (hK : IsCompact K)
    (hT : ∀ v : E, UpperSemicontinuousOn (fun x ↦ ‖T x v‖) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖T x‖ ≤ C := by
  obtain ⟨C, hC₀, hC⟩ := exists_norm_le_of_bddAbove (T := fun x : K ↦ T x) fun v ↦ by
    obtain ⟨M, hM⟩ := (hT v).bddAbove_of_isCompact hK
    exact ⟨M, Set.forall_mem_range.mpr fun x ↦ hM ⟨x.1, x.2, rfl⟩⟩
  exact ⟨C, hC₀, fun x hx ↦ hC ⟨x, hx⟩⟩

/-- **Uniform boundedness on compact sets.** A family of continuous semilinear maps from a barrelled
seminormed space (in particular, any Banach space) that is strongly continuous on a compact set `K`
has a uniform nonnegative operator-norm bound on `K`. -/
theorem exists_norm_le_of_isCompact_continuousOn [BarrelledSpace 𝕜 E]
    {T : X → E →SL[σ] F} {K : Set X} (hK : IsCompact K)
    (hT : ∀ v : E, ContinuousOn (fun x ↦ T x v) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖T x‖ ≤ C :=
  exists_norm_le_of_isCompact_upperSemicontinuousOn hK fun v ↦ (hT v).norm.upperSemicontinuousOn

/-- A family of continuous semilinear maps from a barrelled seminormed space (in particular, any
Banach space), indexed by a weakly locally compact space, whose pointwise norms `x ↦ ‖T x v‖` are
upper semicontinuous admits a compact neighborhood of every point with a uniform operator-norm
bound. -/
theorem exists_compact_nhds_norm_le [BarrelledSpace 𝕜 E] [WeaklyLocallyCompactSpace X]
    {T : X → E →SL[σ] F} (hT : ∀ v : E, UpperSemicontinuous fun x ↦ ‖T x v‖) (x₀ : X) :
    ∃ K ∈ 𝓝 x₀, IsCompact K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖T x‖ ≤ C := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds x₀
  exact ⟨K, hK, hKc, exists_norm_le_of_isCompact_upperSemicontinuousOn hKc
    fun v ↦ (hT v).upperSemicontinuousOn K⟩

/-- A family of continuous semilinear maps from a barrelled seminormed space (in particular, any
Banach space) whose pointwise norms `x ↦ ‖T x v‖` are upper semicontinuous at a point `x₀` whose
neighborhood filter is countably generated (for instance, in any first-countable space) is
uniformly norm bounded on some neighborhood of `x₀`. -/
theorem exists_nhds_norm_le_of_isCountablyGenerated [BarrelledSpace 𝕜 E]
    {T : X → E →SL[σ] F} {x₀ : X} [(𝓝 x₀).IsCountablyGenerated]
    (hT : ∀ v : E, UpperSemicontinuousAt (fun x ↦ ‖T x v‖) x₀) :
    ∃ U ∈ 𝓝 x₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ‖T x‖ ≤ C := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_eventually_norm_le_of_isCountablyGenerated (l := 𝓝 x₀) (T := T)
      fun v ↦ ⟨‖T x₀ v‖ + 1, (hT v (‖T x₀ v‖ + 1) (lt_add_one _)).mono fun _ hx ↦ hx.le⟩
  exact ⟨{x | ‖T x‖ ≤ C}, hC, C, hC₀, fun _ hx ↦ hx⟩

/-- Joint continuity of `(x, v) ↦ T x v` at `(x₀, 0)` implies a uniform operator-norm bound on
some neighborhood of `x₀`. Completeness or barrelledness of `E` is not needed. -/
theorem exists_nhds_norm_le_of_continuousAt_zero {T : X → E →SL[σ] F} {x₀ : X}
    (h : ContinuousAt (fun p : X × E ↦ T p.1 p.2) (x₀, 0)) :
    ∃ U ∈ 𝓝 x₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ‖T x‖ ≤ C := by
  have hmem : (fun p : X × E ↦ T p.1 p.2) ⁻¹' Metric.ball 0 1 ∈ 𝓝 (x₀, (0 : E)) :=
    h (by simpa [map_zero] using Metric.ball_mem_nhds (0 : F) zero_lt_one)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hmem
  obtain ⟨U, hU, V, hV, hUV⟩ := hmem
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hC : 0 ≤ ‖c‖ / δ := div_nonneg (norm_nonneg c) hδ.le
  refine ⟨U, hU, ‖c‖ / δ, hC, fun x hx ↦
    opNorm_le_of_shell hδ hC hc fun v hv₁ hv₂ ↦ ?_⟩
  have hball : ‖T x v‖ < 1 := by
    have hxv : (x, v) ∈ U ×ˢ V := ⟨hx, hδV (mem_ball_zero_iff.mpr hv₂)⟩
    exact mem_ball_zero_iff.mp (hUV hxv)
  have hc_pos : 0 < ‖c‖ := zero_lt_one.trans hc
  calc ‖T x v‖ ≤ 1 := hball.le
    _ = ‖c‖ / δ * (δ / ‖c‖) := by field_simp [hc_pos.ne', hδ.ne']
    _ ≤ ‖c‖ / δ * ‖v‖ := mul_le_mul_of_nonneg_left hv₁ hC

/-- Local uniform operator-norm boundedness near `x₀` upgrades continuity of `x ↦ T x v₀` at
`x₀` to joint continuity of `(x, v) ↦ T x v` at `(x₀, v₀)`. -/
theorem continuousAt_uncurry_of_eventually_norm_le {T : X → E →SL[σ] F} {x₀ : X} {v₀ : E}
    {C : ℝ} (hC : ∀ᶠ x in 𝓝 x₀, ‖T x‖ ≤ C)
    (hT : ContinuousAt (fun x ↦ T x v₀) x₀) :
    ContinuousAt (fun p : X × E ↦ T p.1 p.2) (x₀, v₀) :=
  AddMonoidHomClass.tendsto_apply_of_eventually_bound
    ((continuous_fst.continuousAt.eventually hC).mono fun p hp v ↦ (T p.1).le_of_opNorm_le hp v)
    (hT.tendsto.comp continuous_fst.continuousAt)
    continuous_snd.continuousAt

/-- **Pointwise joint continuity criterion.** The action `(x, v) ↦ T x v` is jointly continuous
at `(x₀, v)` for every `v` if and only if every slice `x ↦ T x v` is continuous at `x₀` and
`T` is uniformly operator-norm bounded on some neighborhood of `x₀`. -/
theorem continuousAt_uncurry_iff {T : X → E →SL[σ] F} {x₀ : X} :
    (∀ v : E, ContinuousAt (fun p : X × E ↦ T p.1 p.2) (x₀, v)) ↔
      (∀ v : E, ContinuousAt (fun x ↦ T x v) x₀) ∧
        ∃ U ∈ 𝓝 x₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ‖T x‖ ≤ C := by
  refine ⟨fun h ↦ ⟨fun v ↦ ?_, exists_nhds_norm_le_of_continuousAt_zero (h 0)⟩, ?_⟩
  · exact (h v).comp_of_eq (continuousAt_id.prodMk continuousAt_const) rfl
  · rintro ⟨hT, U, hU, C, -, hC⟩ v
    exact continuousAt_uncurry_of_eventually_norm_le (eventually_of_mem hU hC) (hT v)

/-- **Joint continuity criterion.** The action `(x, v) ↦ T x v` is jointly continuous on `X × E`
if and only if every slice `x ↦ T x v` is continuous and `T` is locally uniformly operator-norm
bounded around every point of `X`. Completeness or barrelledness of `E` is not needed. -/
theorem continuous_uncurry_iff {T : X → E →SL[σ] F} :
    Continuous (fun p : X × E ↦ T p.1 p.2) ↔
      (∀ v : E, Continuous fun x ↦ T x v) ∧
        ∀ x₀ : X, ∃ U ∈ 𝓝 x₀,
          ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ‖T x‖ ≤ C := by
  simp_rw [continuous_iff_continuousAt, Prod.forall, continuousAt_uncurry_iff, forall_and]
  exact and_congr_left' forall_comm

/-- A family of continuous semilinear maps from a barrelled seminormed space (in particular, any
Banach space) that is strongly continuous on a compact set `K` is jointly continuous on
`K ×ˢ Set.univ`. -/
theorem continuousOn_uncurry_of_isCompact [BarrelledSpace 𝕜 E] {T : X → E →SL[σ] F}
    {K : Set X} (hK : IsCompact K) (hT : ∀ v : E, ContinuousOn (fun x ↦ T x v) K) :
    ContinuousOn (fun p : X × E ↦ T p.1 p.2) (K ×ˢ Set.univ) := by
  obtain ⟨C, -, hC⟩ := exists_norm_le_of_isCompact_continuousOn hK hT
  refine AddMonoidHomClass.continuousOn_apply_of_bound (T := fun p : X × E ↦ T p.1)
    (f := Prod.snd) (C := C)
    (fun v ↦ (hT v).comp continuous_fst.continuousOn (fun p hp ↦ hp.1))
    (fun p hp v ↦ (T p.1).le_of_opNorm_le (hC p.1 hp.1) v) continuous_snd.continuousOn

/-- On a weakly locally compact parameter space, a strongly continuous family of continuous
semilinear maps from a barrelled seminormed space (in particular, any Banach space) is jointly
continuous. -/
theorem continuous_uncurry_of_weaklyLocallyCompact [BarrelledSpace 𝕜 E]
    [WeaklyLocallyCompactSpace X] {T : X → E →SL[σ] F}
    (hT : ∀ v : E, Continuous fun x ↦ T x v) :
    Continuous fun p : X × E ↦ T p.1 p.2 :=
  continuous_uncurry_iff.mpr ⟨hT, fun x₀ ↦ by
    obtain ⟨K, hK, -, C, hC₀, hC⟩ :=
      exists_compact_nhds_norm_le (fun v ↦ (hT v).norm.upperSemicontinuous) x₀
    exact ⟨K, hK, C, hC₀, hC⟩⟩

/-- At a point `x₀` whose neighborhood filter is countably generated (for instance, in any
first-countable space), joint continuity at `(x₀, v)` for every `v` of a family of continuous
semilinear maps from a barrelled seminormed space (in particular, any Banach space) is equivalent
to strong continuity at `x₀`. -/
theorem continuousAt_uncurry_iff_of_isCountablyGenerated [BarrelledSpace 𝕜 E]
    {T : X → E →SL[σ] F} {x₀ : X} [(𝓝 x₀).IsCountablyGenerated] :
    (∀ v : E, ContinuousAt (fun p : X × E ↦ T p.1 p.2) (x₀, v)) ↔
      ∀ v : E, ContinuousAt (fun x ↦ T x v) x₀ :=
  ⟨fun h v ↦ (h v).comp_of_eq (continuousAt_id.prodMk continuousAt_const) rfl, fun hT v ↦ by
    obtain ⟨U, hU, C, -, hC⟩ := exists_nhds_norm_le_of_isCountablyGenerated
      fun w ↦ (hT w).norm.upperSemicontinuousAt
    exact continuousAt_uncurry_of_eventually_norm_le (eventually_of_mem hU hC) (hT v)⟩

/-- On a first-countable parameter space, a strongly continuous family of continuous semilinear
maps from a barrelled seminormed space (in particular, any Banach space) is jointly continuous. -/
theorem continuous_uncurry_of_firstCountable [BarrelledSpace 𝕜 E] [FirstCountableTopology X]
    {T : X → E →SL[σ] F} (hT : ∀ v : E, Continuous fun x ↦ T x v) :
    Continuous fun p : X × E ↦ T p.1 p.2 :=
  continuous_iff_continuousAt.mpr fun p ↦
    (continuousAt_uncurry_iff_of_isCountablyGenerated.mpr fun v ↦
      (hT v).continuousAt) p.2

end Semilinear

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Strong convergence is preserved by composition when the outer operators are eventually
uniformly norm bounded. The inner operators need no norm bound. -/
theorem tendsto_comp_apply_of_eventually_norm_le {l : Filter ι}
    {S : ι → F →L[𝕜] G} {T : ι → E →L[𝕜] F}
    {S₀ : F →L[𝕜] G} {T₀ : E →L[𝕜] F} {C : ℝ}
    (hS : ∀ y, Tendsto (fun i => S i y) l (𝓝 (S₀ y)))
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 (T₀ x)))
    (hC : ∀ᶠ i in l, ‖S i‖ ≤ C) (x : E) :
    Tendsto (fun i => (S i).comp (T i) x) l (𝓝 (S₀.comp T₀ x)) :=
  tendsto_apply_of_eventually_norm_le (T := S) (g := fun i => T i x)
    hC (hS (T₀ x)) (hT x)

/-- Composition of strongly continuous operator families is strongly continuous on any set
where the outer family has a common operator-norm bound. Taking the parameter space to be a
product of strong operator spaces gives joint continuity on norm-bounded sets. -/
theorem continuousOn_pointwise_comp_of_norm_le {X : Type*} [TopologicalSpace X]
    {S : X → F →L[𝕜] G} {T : X → E →L[𝕜] F} {s : Set X} {C : ℝ}
    (hS : ContinuousOn (fun x => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) F G (S x)) s)
    (hT : ContinuousOn (fun x => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F (T x)) s)
    (hC : ∀ x ∈ s, ‖S x‖ ≤ C) :
    ContinuousOn (fun x =>
      toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E G ((S x).comp (T x))) s := by
  intro x hx
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  -- Evaluation of `toPointwiseConvergenceCLM … f` is definitionally evaluation of `f`,
  -- in both the hypotheses and the composition goal.
  exact tendsto_comp_apply_of_eventually_norm_le
    (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp (hS x hx))
    (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp (hT x hx))
    (eventually_mem_nhdsWithin.mono fun y hy => hC y hy)

/-- On a barrelled intermediate space (in particular, any Banach space), composition preserves
strong convergence of sequences without an explicit uniform bound. This does not assert joint
continuity on the whole space. -/
theorem tendsto_comp_apply_of_tendsto_pointwise [BarrelledSpace 𝕜 F]
    {S : ℕ → F →L[𝕜] G} {T : ℕ → E →L[𝕜] F}
    {S₀ : F →L[𝕜] G} {T₀ : E →L[𝕜] F}
    (hS : ∀ y, Tendsto (fun n => S n y) atTop (𝓝 (S₀ y)))
    (hT : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x))) (x : E) :
    Tendsto (fun n => (S n).comp (T n) x) atTop (𝓝 (S₀.comp T₀ x)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_pointwise hS
  exact tendsto_comp_apply_of_eventually_norm_le hS hT (Eventually.of_forall hC) x

end ContinuousLinearMap

namespace IsStarProjection

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A strong limit of orthogonal projections is an orthogonal projection, for arbitrary nets
and with no separability or dimension restriction. -/
theorem of_tendsto_pointwise {l : Filter ι} [l.NeBot]
    {P : ι → H →L[𝕜] H} {P₀ : H →L[𝕜] H}
    (hP : ∀ᶠ i in l, IsStarProjection (P i))
    (hlim : ∀ x, Tendsto (fun i => P i x) l (𝓝 (P₀ x))) : IsStarProjection P₀ := by
  have hsq := ContinuousLinearMap.tendsto_comp_apply_of_eventually_norm_le hlim hlim
    (hP.mono fun i hi => hi.norm_le _)
  have hidem : IsIdempotentElem P₀ := by
    apply ContinuousLinearMap.ext
    intro x
    exact tendsto_nhds_unique (hsq x)
      ((hlim x).congr' (hP.mono fun i hi => congrArg (fun T : H →L[𝕜] H => T x)
        hi.isIdempotentElem.eq.symm))
  refine ⟨hidem, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_⟩
  exact tendsto_nhds_unique
    (((hlim x).inner tendsto_const_nhds).congr' (hP.mono fun i hi =>
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hi.isSelfAdjoint x y)))
    (tendsto_const_nhds.inner (hlim y))

end IsStarProjection

namespace PointwiseConvergenceCLM

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Orthogonal projections are closed in the strong operator topology. -/
theorem isClosed_image_toPointwiseConvergenceCLM_setOf_isStarProjection :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      {P : H →L[𝕜] H | IsStarProjection P}) := by
  refine isClosed_iff_forall_filter.mpr fun P l hl hmem hlim => ?_
  have : l.NeBot := hl -- Supplies the instance for `IsStarProjection.of_tendsto_pointwise`.
  -- `ofFun.symm` and `toPointwiseConvergenceCLM` preserve the underlying operator
  -- definitionally, so their evaluations agree and rewrapping the limit gives `P`.
  refine ⟨(UniformConvergenceCLM.ofFun (RingHom.id 𝕜) H _).symm P,
    IsStarProjection.of_tendsto_pointwise ?_ (tendsto_iff_forall_tendsto.mp hlim), rfl⟩
  apply Filter.Eventually.mono (le_principal_iff.mp hmem)
  rintro i ⟨Q, hQ, hQi⟩
  subst i
  exact hQ

end PointwiseConvergenceCLM
