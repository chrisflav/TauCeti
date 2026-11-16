/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.UrysohnsLemma
import TauCeti.MeasureTheory.Group.ModularCharacter
import TauCeti.Topology.Compactness.LocallyCompact

/-!
# Weil's quotient measure on right-coset spaces

Let `G` be a locally compact Hausdorff topological group and `H ≤ G` a closed subgroup, so that
the right-coset space `H \ G` (realized as `MulAction.orbitRel.Quotient H G`) is a locally compact
Hausdorff space carrying a continuous right action of `G`.

For a right Haar measure `μH` on `H`, integrating along `H`-orbits sends every compactly supported
continuous function `f : C_c(G, ℝ)` to its fibre average
`q ↦ ∫ h : H, f ((h : G) * q.out) ∂μH` in `C_c(H \ G, ℝ)`. This linear operator
`TauCeti.quotientFibreAverage` is surjective onto `C_c(H \ G, ℝ)` and admits nonnegative lifts for
nonnegative functions.

When `G` is second countable, `μG` and `μH` are right Haar measures, and the modular characters of
`G` and `H` agree on `H`, integration against `μG` vanishes on the kernel of the fibre average.
It therefore descends to a right-`G`-invariant positive linear functional on `C_c(H \ G, ℝ)`,
whose Riesz–Markov–Kakutani representing measure is Weil's quotient measure
`TauCeti.quotientMeasure`.

## Main definitions

* `TauCeti.orbitRelQuotientMulRight`: right multiplication by `g : G` on `H \ G` as a
  homeomorphism.
* `TauCeti.quotientFibreAverage`: the fibre-average linear map
  `C_c(G, ℝ) →ₗ[ℝ] C_c(H \ G, ℝ)`.
* `TauCeti.quotientMeasure`: Weil's right-`G`-invariant Radon quotient measure on `H \ G`.

## Main results

* `TauCeti.exists_quotientFibreAverage_eq`: surjectivity of the fibre average with nonnegative
  lifts.
* `TauCeti.exists_unique_quotientMeasure`: existence and uniqueness of the right-`G`-invariant
  Radon quotient measure on `H \ G`.
* `TauCeti.quotientMeasure_smul_subgroup` and `TauCeti.quotientMeasure_smul_group`: scaling laws
  under rescaling `μH` and `μG`.

## References

* Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, §2.6.
* André Weil, *L'intégration dans les groupes topologiques et ses applications*, §9.
-/

public section

open MeasureTheory Set Filter Topology CompactlySupportedContinuousMap
open scoped NNReal ENNReal Pointwise CompactlySupported

namespace TauCeti

section OrbitQuotientTopology

variable {G : Type*} [Group G]

/-- Two elements of `G` represent the same right coset in `H \ G` iff `x * y⁻¹ ∈ H`. -/
theorem orbitRelQuotient_eq_iff (H : Subgroup G) {x y : G} :
    (Quotient.mk'' x : MulAction.orbitRel.Quotient H G) = Quotient.mk'' y ↔ x * y⁻¹ ∈ H := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  simp only [Subgroup.smul_def, smul_eq_mul]
  constructor
  · rintro ⟨h, rfl⟩
    simp [mul_assoc]
  · intro hxy
    exact ⟨⟨x * y⁻¹, hxy⟩, by simp⟩

/-- Multiplying on the left by an element of `H` does not change the right coset in `H \ G`. -/
@[simp]
theorem orbitRelQuotient_mk_mul_left (H : Subgroup G) (h : H) (g : G) :
    (Quotient.mk'' ((h : G) * g) : MulAction.orbitRel.Quotient H G) = Quotient.mk'' g :=
  (orbitRelQuotient_eq_iff H).mpr (by simp [mul_assoc])

/-- The canonical representative `q.out` of a coset `Quotient.mk'' g` differs from `g` by left
multiplication by an element of `H`. -/
theorem orbitRelQuotient_out_mul_inv_mem (H : Subgroup G) (g : G) :
    (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out * g⁻¹ ∈ H :=
  (orbitRelQuotient_eq_iff H).mp
    (Quotient.out_eq' (Quotient.mk'' g : MulAction.orbitRel.Quotient H G))

variable [TopologicalSpace G]

/-- The right-coset space `H \ G` of a topological group by a closed subgroup is Hausdorff. -/
theorem t2Space_orbitRelQuotient [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) : T2Space (MulAction.orbitRel.Quotient H G) := by
  rw [t2Space_iff_of_isOpenQuotientMap (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G))]
  have heq : {p : G × G |
      (Quotient.mk (MulAction.orbitRel H G) p.1) = Quotient.mk (MulAction.orbitRel H G) p.2} =
      (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' (H : Set G) := by
    ext ⟨x, y⟩
    exact orbitRelQuotient_eq_iff H
  rw [heq]
  exact hH.preimage (continuous_fst.mul continuous_snd.inv)

/-- Right translation by `g : G` on the right-coset space `H \ G`, as a homeomorphism. -/
def orbitRelQuotientMulRight [ContinuousMul G] (H : Subgroup G) (g : G) :
    MulAction.orbitRel.Quotient H G ≃ₜ MulAction.orbitRel.Quotient H G where
  toFun := Quotient.lift (fun x : G => (Quotient.mk'' (x * g) : MulAction.orbitRel.Quotient H G))
    fun _ y ⟨h, hh⟩ => by
      simp [← hh, Subgroup.smul_def, mul_assoc]
  invFun := Quotient.lift
    (fun x : G => (Quotient.mk'' (x * g⁻¹) : MulAction.orbitRel.Quotient H G))
    fun _ y ⟨h, hh⟩ => by
      simp [← hh, Subgroup.smul_def, mul_assoc]
  left_inv q := by
    induction q using Quotient.inductionOn' with | h x =>
    simp [Quotient.lift_mk]
  right_inv q := by
    induction q using Quotient.inductionOn' with | h x =>
    simp [Quotient.lift_mk]
  continuous_toFun := by
    rw [(MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).isQuotientMap.continuous_iff]
    exact continuous_quotient_mk'.comp (continuous_mul_const g)
  continuous_invFun := by
    rw [(MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).isQuotientMap.continuous_iff]
    exact continuous_quotient_mk'.comp (continuous_mul_const g⁻¹)

@[simp]
theorem orbitRelQuotientMulRight_mk [ContinuousMul G] (H : Subgroup G) (g x : G) :
    orbitRelQuotientMulRight H g (Quotient.mk'' x) = Quotient.mk'' (x * g) :=
  (rfl)

theorem orbitRelQuotientMulRight_apply [ContinuousMul G] (H : Subgroup G) (g : G)
    (q : MulAction.orbitRel.Quotient H G) :
    orbitRelQuotientMulRight H g q = Quotient.mk'' (q.out * g) := by
  conv_lhs => rw [← Quotient.out_eq' q]
  rfl

@[simp]
theorem orbitRelQuotientMulRight_symm [ContinuousMul G] (H : Subgroup G) (g : G) :
    (orbitRelQuotientMulRight H g).symm = orbitRelQuotientMulRight H g⁻¹ := by
  ext q
  induction q using Quotient.inductionOn' with | h x =>
  rfl

@[simp]
theorem orbitRelQuotientMulRight_one [ContinuousMul G] (H : Subgroup G) :
    orbitRelQuotientMulRight H 1 = Homeomorph.refl _ := by
  ext q
  induction q using Quotient.inductionOn' with | h x =>
  simp

theorem orbitRelQuotientMulRight_mul [ContinuousMul G] (H : Subgroup G) (g₁ g₂ : G)
    (q : MulAction.orbitRel.Quotient H G) :
    orbitRelQuotientMulRight H (g₁ * g₂) q =
      orbitRelQuotientMulRight H g₂ (orbitRelQuotientMulRight H g₁ q) := by
  induction q using Quotient.inductionOn' with | h x =>
  simp [mul_assoc]

end OrbitQuotientTopology

section FibreAverage

variable {G : Type*} [Group G]

/-- The fibre integral `g ↦ ∫ h : H, f ((h : G) * g) ∂μH` is invariant under left
multiplication by elements of `H`. -/
private theorem integral_mul_left_eq_self_fibre {H : Subgroup G}
    [MeasurableSpace H] [MeasurableMul H] (μH : Measure H) [μH.IsMulRightInvariant]
    (f : G → ℝ) (h₀ : H) (g : G) :
    ∫ h : H, f ((h : G) * ((h₀ : G) * g)) ∂μH = ∫ h : H, f ((h : G) * g) ∂μH := by
  simpa only [Subgroup.coe_mul, mul_assoc] using
    integral_mul_right_eq_self (μ := μH) (fun h : H => f ((h : G) * g)) h₀

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restricting a compactly supported continuous function on `G` to a right coset `H * g` gives a
compactly supported continuous function on `H`. -/
private theorem hasCompactSupport_mul_right_subtype {H : Subgroup G} (hH : IsClosed (H : Set G))
    {f : G → ℝ} (hfc : HasCompactSupport f) (g : G) :
    HasCompactSupport (fun h : H => f ((h : G) * g)) := by
  have hemb : Topology.IsClosedEmbedding (fun h : H => (h : G) * g) :=
    (Homeomorph.mulRight g).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal
  exact hfc.comp_isClosedEmbedding hemb

/-- Restricting a compactly supported continuous function on `G` to a right coset `H * g` gives an
integrable function on `H` against any locally finite measure. -/
private theorem integrable_mul_right_subtype {H : Subgroup G} (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [IsFiniteMeasureOnCompacts μH]
    {f : G → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (g : G) :
    Integrable (fun h : H => f ((h : G) * g)) μH :=
  (hf.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
    (hasCompactSupport_mul_right_subtype hH hfc g)

variable [LocallyCompactSpace G]

/-- The fibre integral `g ↦ ∫ h : H, f ((h : G) * g) ∂μH` is continuous in `g` when `f` is
continuous and compactly supported. -/
private theorem continuous_integral_fibre {H : Subgroup G} (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [IsFiniteMeasureOnCompacts μH]
    (f : C_c(G, ℝ)) :
    Continuous (fun g : G => ∫ h : H, f ((h : G) * g) ∂μH) := by
  let _ := IsTopologicalGroup.leftUniformSpace G
  rw [Metric.continuous_iff']
  intro g₀ ε hε
  -- Step 1: Confine the fibre support for `g` in a compact neighbourhood `V` of `g₀` to a fixed
  -- compact set `S ⊆ H`.
  obtain ⟨V, hVc, hVmem⟩ := exists_compact_mem_nhds g₀
  obtain ⟨K, hKc, hfK⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
  let S : Set H := ((↑) : H → G) ⁻¹' (K * V⁻¹)
  have hSc : IsCompact S := hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hKc.mul hVc.inv)
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ENNReal.ofReal δ * μH S < ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hSc.measure_ne_top, ← measureReal_def]
    by_cases hS' : μH.real S = 0
    · exact ⟨1, one_pos, by simp [hS', hε]⟩
    · refine ⟨ε / 2 / μH.real S, by positivity, ?_⟩
      rwa [← ENNReal.ofReal_mul' measureReal_nonneg, ENNReal.ofReal_lt_ofReal_iff hε,
        div_mul_cancel₀ _ hS', half_lt_self_iff]
  have hS {g : G} (hg : g ∈ V) {h : H} (hh : h ∉ S) : f ((h : G) * g) = 0 := by
    contrapose! hh
    exact Set.mem_mul.mpr ⟨(h : G) * g, not_imp_comm.mp (hfK _) hh, g⁻¹,
      Set.inv_mem_inv.mpr hg, mul_inv_cancel_right (h : G) g⟩
  -- Step 2: Use left uniform continuity of `f` to get a neighbourhood of `g₀` with uniform
  -- pointwise oscillation `≤ δ` along `S`.
  have huc : UniformContinuous f := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  rw [uniformContinuous_iff_eventually] at huc
  obtain ⟨U, hU, hfU⟩ := Filter.mem_comap.mp (huc _ (Metric.dist_mem_uniformity hδ0))
  have hgU : {g : G | g⁻¹ * g₀ ∈ U} ∈ 𝓝 g₀ := by
    have hcont : Continuous (fun g : G => g⁻¹ * g₀) := continuous_inv.mul continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hU)
  -- Step 3: Integrate the uniform bound over `S`.
  refine Filter.mem_of_superset (Filter.inter_mem hgU hVmem) fun g ⟨hgU', hgV⟩ => ?_
  have hdist (h : H) (_ : h ∈ S) :
      edist (f ((h : G) * g)) (f ((h : G) * g₀)) ≤ ENNReal.ofReal δ := by
    rw [edist_dist]
    have hmem : ((h : G) * g, (h : G) * g₀) ∈ (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' U := by
      simpa [mul_assoc] using hgU'
    exact ENNReal.ofReal_le_ofReal (hfU hmem).le
  have hint_g := integrable_mul_right_subtype hH μH f.continuous f.hasCompactSupport g
  have hint_g₀ := integrable_mul_right_subtype hH μH f.continuous f.hasCompactSupport g₀
  calc dist (∫ h : H, f ((h : G) * g) ∂μH) (∫ h : H, f ((h : G) * g₀) ∂μH)
      ≤ (∫⁻ h : H, edist (f ((h : G) * g)) (f ((h : G) * g₀)) ∂μH).toReal :=
        dist_integral_le_lintegral_edist hint_g hint_g₀
    _ = (∫⁻ h in S, edist (f ((h : G) * g)) (f ((h : G) * g₀)) ∂μH).toReal := by
        rw [setLIntegral_eq_of_support_subset]
        intro h hh
        contrapose hh
        rw [Function.notMem_support, hS hgV hh, hS (mem_of_mem_nhds hVmem) hh, edist_self]
    _ < ε := by
        refine ENNReal.toReal_lt_of_lt_ofReal
          ((setLIntegral_mono measurable_const hdist).trans_lt ?_)
        rwa [lintegral_const, Measure.restrict_apply_univ]

/-- **The fibre average** sending `f : C_c(G, ℝ)` to the compactly supported continuous function
`H g ↦ ∫ h : H, f ((h : G) * g) ∂μH` on `H \ G`. -/
noncomputable def quotientFibreAverage (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH] :
    C_c(G, ℝ) →ₗ[ℝ] C_c(MulAction.orbitRel.Quotient H G, ℝ) where
  toFun f :=
    { toFun := fun q => ∫ h : H, f ((h : G) * q.out) ∂μH
      continuous_toFun := by
        have hq := (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).isQuotientMap
        rw [hq.continuous_iff]
        have heq : (fun g : G => ∫ h : H, f ((h : G) *
            (Quotient.mk (MulAction.orbitRel H G) g).out) ∂μH) =
            fun g : G => ∫ h : H, f ((h : G) * g) ∂μH := by
          ext g
          let h₀ : H := ⟨_, orbitRelQuotient_out_mul_inv_mem H g⟩
          have hrep : (Quotient.mk (MulAction.orbitRel H G) g).out = (h₀ : G) * g := by
            simp [h₀]
          rw [hrep]
          exact integral_mul_left_eq_self_fibre μH f h₀ g
        rw [Function.comp_def, heq]
        exact continuous_integral_fibre hH μH f
      hasCompactSupport' := by
        have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_orbitRelQuotient H hH
        refine HasCompactSupport.of_support_subset_isCompact
          (f.hasCompactSupport.image (continuous_quotient_mk' (s := MulAction.orbitRel H G))) ?_
        intro q hq
        rw [Function.mem_support] at hq
        by_contra hnot
        apply hq
        have hzero : ∀ h : H, f ((h : G) * q.out) = 0 := by
          intro h
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          apply hnot
          refine ⟨(h : G) * q.out, hmem,
            (orbitRelQuotient_mk_mul_left H h q.out).trans (Quotient.out_eq' q)⟩
        simp [hzero] }
  map_add' f₁ f₂ := by
    ext q
    exact integral_add
      (integrable_mul_right_subtype hH μH f₁.continuous f₁.hasCompactSupport q.out)
      (integrable_mul_right_subtype hH μH f₂.continuous f₂.hasCompactSupport q.out)
  map_smul' c f := by
    ext q
    exact integral_smul c (fun h : H => f ((h : G) * q.out))

theorem quotientFibreAverage_apply (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH] (f : C_c(G, ℝ)) (q : MulAction.orbitRel.Quotient H G) :
    quotientFibreAverage H hH μH f q = ∫ h : H, f ((h : G) * q.out) ∂μH :=
  (rfl)

@[simp]
theorem quotientFibreAverage_mk (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH] (f : C_c(G, ℝ)) (g : G) :
    quotientFibreAverage H hH μH f (Quotient.mk'' g) = ∫ h : H, f ((h : G) * g) ∂μH := by
  rw [quotientFibreAverage_apply]
  let h₀ : H := ⟨_, orbitRelQuotient_out_mul_inv_mem H g⟩
  have hrep : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = (h₀ : G) * g := by
    simp [h₀]
  rw [hrep]
  exact integral_mul_left_eq_self_fibre μH f h₀ g

theorem quotientFibreAverage_mono (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH] {f₁ f₂ : C_c(G, ℝ)} (h : f₁ ≤ f₂) :
    quotientFibreAverage H hH μH f₁ ≤ quotientFibreAverage H hH μH f₂ :=
  fun q => integral_mono
    (integrable_mul_right_subtype hH μH f₁.continuous f₁.hasCompactSupport q.out)
    (integrable_mul_right_subtype hH μH f₂.continuous f₂.hasCompactSupport q.out)
    fun _ => h _

/-- The fibre average intertwines right translation on `G` with right translation on `H \ G`. -/
theorem quotientFibreAverage_comp_mulRight (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH] (f : C_c(G, ℝ)) (g : G) :
    quotientFibreAverage H hH μH (f.comp (Homeomorph.mulRight g).toCocompactMap) =
      (quotientFibreAverage H hH μH f).comp (orbitRelQuotientMulRight H g).toCocompactMap := by
  ext q
  induction q using Quotient.inductionOn' with | h x =>
  simp [mul_assoc]

/-- **Surjectivity of the fibre average with nonnegative lifts.** Every `F : C_c(H \ G, ℝ)` is the
fibre average of some `f : C_c(G, ℝ)`, which can be chosen nonnegative whenever `F` is. -/
theorem exists_quotientFibreAverage_eq (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (F : C_c(MulAction.orbitRel.Quotient H G, ℝ)) :
    ∃ f : C_c(G, ℝ), quotientFibreAverage H hH μH f = F ∧ (0 ≤ F → 0 ≤ f) := by
  -- Lift the compact support of `F` to a compact set `K ⊆ G`.
  have hπ : IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel H G)) :=
    MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)
  obtain ⟨K, hKc, hKsub⟩ := hπ.isOpenMap.exists_isCompact_subset_image F.hasCompactSupport
    (by rw [hπ.surjective.range_eq]; exact subset_univ _)
  -- Pick `η ∈ C_c(G, [0, 1])` equal to `1` on `K`.
  obtain ⟨η₀, hη1, hηc, -, hη01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hKc isOpen_univ (subset_univ K)
  let η : C_c(G, ℝ) := ⟨η₀, hηc⟩
  -- The fibre average `P η` is strictly positive on `tsupport F`.
  have hPη_nonneg (q : MulAction.orbitRel.Quotient H G) :
      0 ≤ quotientFibreAverage H hH μH η q :=
    integral_nonneg fun h => (hη01 _).1
  have hPη_pos {q : MulAction.orbitRel.Quotient H G} (hq : q ∈ tsupport F) :
      0 < quotientFibreAverage H hH μH η q := by
    obtain ⟨k, hkK, rfl⟩ := hKsub hq
    have hmk : Quotient.mk (MulAction.orbitRel H G) k = Quotient.mk'' k := rfl
    rw [hmk, quotientFibreAverage_mk]
    have hne : η (((1 : H) : G) * k) ≠ 0 := by
      simpa [η] using (hη1 hkK).symm ▸ one_ne_zero
    exact (η.continuous.comp (continuous_subtype_val.mul continuous_const))
      |>.integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (hasCompactSupport_mul_right_subtype hH η.hasCompactSupport k)
      (fun h => (hη01 _).1) hne
  -- Define `ψ q := F q / P η q` (which is `0` when `P η q = 0`); `ψ` is continuous everywhere.
  let ψ : MulAction.orbitRel.Quotient H G → ℝ := fun q =>
    F q / quotientFibreAverage H hH μH η q
  have hψ_cont : Continuous ψ := by
    rw [continuous_iff_continuousAt]
    intro q
    by_cases hq : quotientFibreAverage H hH μH η q = 0
    · have hnot : q ∉ tsupport F := fun hmem => (hPη_pos hmem).ne' hq
      have hopen : IsOpen (tsupport F)ᶜ := isClosed_tsupport F |>.isOpen_compl
      have hconst : ψ =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
        filter_upwards [hopen.mem_nhds hnot] with q' hq'
        simp [ψ, image_eq_zero_of_notMem_tsupport hq']
      exact continuousAt_const.congr hconst.symm
    · exact F.continuous.continuousAt.div
        (quotientFibreAverage H hH μH η).continuous.continuousAt hq
  -- Multiply `(ψ ∘ π)` by `η` to get the lift `f`.
  let f : C_c(G, ℝ) :=
    { toFun := fun g => ψ (Quotient.mk'' g) * η g
      continuous_toFun := (hψ_cont.comp continuous_quotient_mk').mul η.continuous
      hasCompactSupport' := η.hasCompactSupport.mul_left }
  refine ⟨f, ?_, ?_⟩
  · ext q
    induction q using Quotient.inductionOn' with | h g =>
    rw [quotientFibreAverage_mk]
    have hconst : (fun h : H => f ((h : G) * g)) =
        fun h : H => ψ (Quotient.mk'' g) * η ((h : G) * g) := by
      ext h
      simp [f]
    rw [hconst, integral_const_mul, ← quotientFibreAverage_mk H hH μH η g]
    by_cases hq : quotientFibreAverage H hH μH η (Quotient.mk'' g) = 0
    · have hnot : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G) ∉ tsupport F :=
        fun hmem => (hPη_pos hmem).ne' hq
      simp [ψ, hq, image_eq_zero_of_notMem_tsupport hnot]
    · exact div_mul_cancel₀ _ hq
  · intro hF g
    exact mul_nonneg (div_nonneg (hF _) (hPη_nonneg _)) (hη01 g).1

end FibreAverage

section QuotientMeasureConstruction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Auxiliary regularity of locally finite Borel measures on `H \ G`. -/
theorem regular_of_isFiniteMeasureOnCompacts_orbitRelQuotient (H : Subgroup G)
    (hH : IsClosed (H : Set G)) [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (ν : Measure (MulAction.orbitRel.Quotient H G)) [IsFiniteMeasureOnCompacts ν] :
    ν.Regular := by
  have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_orbitRelQuotient H hH
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace
  have : SecondCountableTopology (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).secondCountableTopology
  exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν

variable [MeasurableSpace G] [BorelSpace G]

/-- **Adjointness of the fibre average under matching modular characters.**
When the modular characters of `G` and `H` agree on `H`,
`∫ g, (P φ)(H g) * f g ∂μG = ∫ g, φ g * (P f)(H g) ∂μG` for all `φ, f : C_c(G, ℝ)`.
-/
theorem integral_quotientFibreAverage_mul_eq (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    (φ f : C_c(G, ℝ)) :
    ∫ g, quotientFibreAverage H hH μH φ (Quotient.mk'' g) * f g ∂μG =
      ∫ g, φ g * quotientFibreAverage H hH μH f (Quotient.mk'' g) ∂μG := by
  have : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite μG := inferInstance
  have : SigmaFinite μH := inferInstance
  let K_H : Set H := ((↑) : H → G) ⁻¹' (tsupport φ * (tsupport f)⁻¹)
  have hKH : IsCompact K_H :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      (φ.hasCompactSupport.mul f.hasCompactSupport.inv)
  -- Step 1: Compact support of `(g, h) ↦ φ (h * g) * f g` on `G × H` for Fubini.
  have hcont1 : Continuous (fun p : G × H => φ ((p.2 : G) * p.1) * f p.1) :=
    (φ.continuous.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)).mul
      (f.continuous.comp continuous_fst)
  have hsupp1 : HasCompactSupport (fun p : G × H => φ ((p.2 : G) * p.1) * f p.1) := by
    refine HasCompactSupport.of_support_subset_isCompact (f.hasCompactSupport.prod hKH) ?_
    rintro ⟨g, h⟩ hp
    rw [Function.mem_support] at hp
    have hg : g ∈ tsupport f := subset_tsupport _ (right_ne_zero_of_mul hp)
    have hhg : (h : G) * g ∈ tsupport φ := subset_tsupport _ (left_ne_zero_of_mul hp)
    refine ⟨hg, Set.mem_mul.mpr ⟨(h : G) * g, hhg, g⁻¹, Set.inv_mem_inv.mpr hg,
      mul_inv_cancel_right (h : G) g⟩⟩
  have hint1 : Integrable (Function.uncurry fun g (h : H) => φ ((h : G) * g) * f g)
      (μG.prod μH) :=
    hcont1.integrable_of_hasCompactSupport hsupp1
  -- Step 2: Compact support of `(h, g) ↦ φ g * ((c_H h)⁻¹ * f (h⁻¹ * g))` on `H × G`.
  have hcH_cont : Continuous (fun h : H => (Measure.modularCharacter (G := H) h : ℝ)⁻¹) :=
    (NNReal.continuous_coe.comp continuous_modularCharacter).inv₀ fun h =>
      NNReal.coe_ne_zero.mpr (Measure.modularCharacterFun_pos h).ne'
  have hcont2 : Continuous (fun p : H × G =>
      φ p.2 * ((Measure.modularCharacter (G := H) p.1 : ℝ)⁻¹ * f ((p.1 : G)⁻¹ * p.2))) :=
    (φ.continuous.comp continuous_snd).mul
      ((hcH_cont.comp continuous_fst).mul
        (f.continuous.comp ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd)))
  have hsupp2 : HasCompactSupport (fun p : H × G =>
      φ p.2 *
        ((Measure.modularCharacter (G := H) p.1 : ℝ)⁻¹ * f ((p.1 : G)⁻¹ * p.2))) := by
    refine HasCompactSupport.of_support_subset_isCompact (hKH.prod φ.hasCompactSupport) ?_
    rintro ⟨h, g⟩ hp
    rw [Function.mem_support] at hp
    have hg : g ∈ tsupport φ := subset_tsupport _ (left_ne_zero_of_mul hp)
    have hhg : (h : G)⁻¹ * g ∈ tsupport f :=
      subset_tsupport _ (right_ne_zero_of_mul (right_ne_zero_of_mul hp))
    refine ⟨Set.mem_mul.mpr ⟨g, hg, ((h : G)⁻¹ * g)⁻¹,
      Set.inv_mem_inv.mpr hhg, by simp⟩, hg⟩
  have hint2 : Integrable (Function.uncurry fun (h : H) g =>
      φ g * ((Measure.modularCharacter (G := H) h : ℝ)⁻¹ * f ((h : G)⁻¹ * g)))
      (μH.prod μG) :=
    hcont2.integrable_of_hasCompactSupport hsupp2
  -- Step 3: Chain Fubini, left-translation on `G`, modular match, Fubini, and inversion on `H`.
  calc ∫ g, quotientFibreAverage H hH μH φ (Quotient.mk'' g) * f g ∂μG
      = ∫ g, ∫ h : H, φ ((h : G) * g) * f g ∂μH ∂μG := by
          congr 1 with g
          rw [quotientFibreAverage_mk, integral_mul_const]
    _ = ∫ h : H, ∫ g, φ ((h : G) * g) * f g ∂μG ∂μH :=
          integral_integral_swap hint1
    _ = ∫ h : H, ∫ g, φ g * ((Measure.modularCharacter (G := H) h : ℝ)⁻¹ *
          f ((h : G)⁻¹ * g)) ∂μG ∂μH := by
          congr 1 with h
          have hshift := integral_mul_left_eq_modularCharacter_inv_smul (μ := μG)
            (f := fun g => φ g * f ((h : G)⁻¹ * g))
            (φ.continuous.mul (f.continuous.comp (continuous_const.mul continuous_id)))
            φ.hasCompactSupport.mul_right (h : G)
          simp only [inv_mul_cancel_left, smul_eq_mul] at hshift
          rw [hshift, hmod h, ← integral_const_mul]
          congr 1 with g
          ring
    _ = ∫ g, ∫ h : H, φ g * ((Measure.modularCharacter (G := H) h : ℝ)⁻¹ *
          f ((h : G)⁻¹ * g)) ∂μH ∂μG :=
          integral_integral_swap hint2
    _ = ∫ g, φ g * quotientFibreAverage H hH μH f (Quotient.mk'' g) ∂μG := by
          congr 1 with g
          rw [integral_const_mul, quotientFibreAverage_mk]
          congr 1
          simpa only [Subgroup.coe_inv, smul_eq_mul] using
            integral_modularCharacter_inv_smul_inv_eq_self (μ := μH)
              (f := fun h : H => f ((h : G) * g))
              (f.continuous.comp (continuous_subtype_val.mul continuous_const))
              (hasCompactSupport_mul_right_subtype hH f.hasCompactSupport g)

/-- **Vanishing on the kernel of the fibre average.** If `quotientFibreAverage H hH μH f = 0`,
then `∫ g, f g ∂μG = 0`. -/
theorem integral_eq_zero_of_quotientFibreAverage_eq_zero (H : Subgroup G)
    (hH : IsClosed (H : Set G)) [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    {f : C_c(G, ℝ)} (hf : quotientFibreAverage H hH μH f = 0) :
    ∫ g, f g ∂μG = 0 := by
  have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_orbitRelQuotient H hH
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace
  let K : Set (MulAction.orbitRel.Quotient H G) :=
    Quotient.mk (MulAction.orbitRel H G) '' tsupport f
  have hKc : IsCompact K := f.hasCompactSupport.image continuous_quotient_mk'
  obtain ⟨Φ₀, hΦ1, hΦc, -, -⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hKc isOpen_univ (subset_univ K)
  let Φ : C_c(MulAction.orbitRel.Quotient H G, ℝ) := ⟨Φ₀, hasCompactSupport_def.mpr hΦc⟩
  obtain ⟨φ, hφ, -⟩ := exists_quotientFibreAverage_eq H hH μH Φ
  have hmul : (fun g : G => quotientFibreAverage H hH μH φ (Quotient.mk'' g) * f g) = f := by
    ext g
    rw [hφ]
    by_cases hg : g ∈ tsupport f
    · have hmem : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G) ∈ K := ⟨g, hg, rfl⟩
      simp [Φ, hΦ1 hmem]
    · simp [image_eq_zero_of_notMem_tsupport hg]
  calc ∫ g, f g ∂μG
      = ∫ g, quotientFibreAverage H hH μH φ (Quotient.mk'' g) * f g ∂μG := by rw [hmul]
    _ = ∫ g, φ g * quotientFibreAverage H hH μH f (Quotient.mk'' g) ∂μG :=
          integral_quotientFibreAverage_mul_eq H hH μG μH hmod φ f
    _ = 0 := by simp [hf]

/-- The descended positive linear functional on `C_c(H \ G, ℝ)` induced by `μG` and `μH`. -/
private noncomputable def quotientFunctional (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    C_c(MulAction.orbitRel.Quotient H G, ℝ) →ₚ[ℝ] ℝ := by
  let lift (F : C_c(MulAction.orbitRel.Quotient H G, ℝ)) : C_c(G, ℝ) :=
    (exists_quotientFibreAverage_eq H hH μH F).choose
  have hlift_eq (F : C_c(MulAction.orbitRel.Quotient H G, ℝ)) :
      quotientFibreAverage H hH μH (lift F) = F :=
    (exists_quotientFibreAverage_eq H hH μH F).choose_spec.1
  have hlift_nonneg (F : C_c(MulAction.orbitRel.Quotient H G, ℝ)) (hF : 0 ≤ F) :
      0 ≤ lift F :=
    (exists_quotientFibreAverage_eq H hH μH F).choose_spec.2 hF
  have hwell {f₁ f₂ : C_c(G, ℝ)}
      (h : quotientFibreAverage H hH μH f₁ = quotientFibreAverage H hH μH f₂) :
      ∫ g, f₁ g ∂μG = ∫ g, f₂ g ∂μG := by
    have h0 : ∫ g, (f₁ - f₂) g ∂μG = 0 :=
      integral_eq_zero_of_quotientFibreAverage_eq_zero H hH μG μH hmod
        (by rw [map_sub, h, sub_self])
    have hsub : ∫ g, (f₁ - f₂) g ∂μG = ∫ g, f₁ g ∂μG - ∫ g, f₂ g ∂μG :=
      integral_sub f₁.integrable f₂.integrable
    linarith
  exact
    { toFun := fun F => ∫ g, lift F g ∂μG
      map_add' := fun F₁ F₂ => by
        rw [hwell (f₁ := lift (F₁ + F₂)) (f₂ := lift F₁ + lift F₂)
          (by rw [map_add, hlift_eq, hlift_eq, hlift_eq])]
        exact integral_add (lift F₁).integrable (lift F₂).integrable
      map_smul' := fun c F => by
        rw [hwell (f₁ := lift (c • F)) (f₂ := c • lift F)
          (by rw [map_smul, hlift_eq, hlift_eq])]
        exact integral_smul c (lift F)
      monotone' := fun F₁ F₂ hF => by
        have hdiff : 0 ≤ F₂ - F₁ := sub_nonneg.mpr hF
        have hpos : 0 ≤ ∫ g, lift (F₂ - F₁) g ∂μG :=
          integral_nonneg fun g => hlift_nonneg (F₂ - F₁) hdiff g
        have heq : ∫ g, lift (F₂ - F₁) g ∂μG =
            ∫ g, lift F₂ g ∂μG - ∫ g, lift F₁ g ∂μG := by
          rw [hwell (f₁ := lift (F₂ - F₁)) (f₂ := lift F₂ - lift F₁)
            (by rw [map_sub, hlift_eq, hlift_eq, hlift_eq])]
          exact integral_sub (lift F₂).integrable (lift F₁).integrable
        linarith }

private theorem quotientFunctional_apply_fibreAverage (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h)
    (f : C_c(G, ℝ)) :
    quotientFunctional H hH μG μH hmod (quotientFibreAverage H hH μH f) = ∫ g, f g ∂μG := by
  let F := quotientFibreAverage H hH μH f
  let liftF := (exists_quotientFibreAverage_eq H hH μH F).choose
  have hlift : quotientFibreAverage H hH μH liftF = F :=
    (exists_quotientFibreAverage_eq H hH μH F).choose_spec.1
  have h0 : ∫ g, (liftF - f) g ∂μG = 0 :=
    integral_eq_zero_of_quotientFibreAverage_eq_zero H hH μG μH hmod
      (by rw [map_sub, hlift, sub_self])
  have hsub : ∫ g, (liftF - f) g ∂μG = ∫ g, liftF g ∂μG - ∫ g, f g ∂μG :=
    integral_sub liftF.integrable f.integrable
  have hval : quotientFunctional H hH μG μH hmod (quotientFibreAverage H hH μH f) =
      ∫ g, liftF g ∂μG := rfl
  linarith

/-- **Weil's quotient measure** on the right-coset space `H \ G`, defined via the
Riesz–Markov–Kakutani representation theorem for the descended positive linear functional on
`C_c(H \ G, ℝ)`. -/
noncomputable def quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    Measure (MulAction.orbitRel.Quotient H G) :=
  letI : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_orbitRelQuotient H hH
  letI : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace
  RealRMK.rieszMeasure (quotientFunctional H hH μG μH hmod)

variable (H : Subgroup G) (hH : IsClosed (H : Set G))
  [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
  [BorelSpace (MulAction.orbitRel.Quotient H G)]
  (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
  [μG.IsOpenPosMeasure]
  (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
  [μH.IsOpenPosMeasure]
  (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
    Measure.modularCharacter (G := H) h)

/-- Weil's quotient measure is regular. -/
theorem regular_quotientMeasure :
    (quotientMeasure H hH μG μH hmod).Regular := by
  have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_orbitRelQuotient H hH
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace
  exact RealRMK.regular_rieszMeasure _

/-- Weil's quotient measure is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_quotientMeasure :
    IsFiniteMeasureOnCompacts (quotientMeasure H hH μG μH hmod) := by
  have := regular_quotientMeasure H hH μG μH hmod
  infer_instance

/-- Weil's quotient measure is σ-finite. -/
theorem sigmaFinite_quotientMeasure :
    SigmaFinite (quotientMeasure H hH μG μH hmod) := by
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace
  have : SecondCountableTopology (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).secondCountableTopology
  have := isFiniteMeasureOnCompacts_quotientMeasure H hH μG μH hmod
  infer_instance

/-- **Weil's quotient integral formula** for a bundled compactly supported continuous function. -/
theorem integral_quotientFibreAverage_quotientMeasure (f : C_c(G, ℝ)) :
    ∫ q, quotientFibreAverage H hH μH f q ∂quotientMeasure H hH μG μH hmod =
      ∫ g, f g ∂μG := by
  have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_orbitRelQuotient H hH
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace
  rw [quotientMeasure, RealRMK.integral_rieszMeasure,
    quotientFunctional_apply_fibreAverage H hH μG μH hmod f]

/-- **Weil's quotient integral formula** for compactly supported continuous functions
`f : G → ℝ`. -/
theorem integral_quotientMeasure_of_continuous_hasCompactSupport {f : G → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ g, f g ∂μG =
      ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂quotientMeasure H hH μG μH hmod :=
  (integral_quotientFibreAverage_quotientMeasure H hH μG μH hmod ⟨⟨f, hf⟩, hfc⟩).symm

/-- Weil's quotient measure is positive on every nonempty open set. -/
theorem isOpenPosMeasure_quotientMeasure :
    (quotientMeasure H hH μG μH hmod).IsOpenPosMeasure := by
  have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_orbitRelQuotient H hH
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace
  refine ⟨fun U hU ⟨q₀, hq₀⟩ => ?_⟩
  obtain ⟨K, hKc, hq₀K, hKU⟩ := exists_compact_subset hU hq₀
  obtain ⟨F₀, hF1, hFc, hFsupp, hF01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hKc hU hKU
  let F : C_c(MulAction.orbitRel.Quotient H G, ℝ) := ⟨F₀, hasCompactSupport_def.mpr hFc⟩
  obtain ⟨f, hfF, hf0⟩ := exists_quotientFibreAverage_eq H hH μH F
  have hf_nonneg : 0 ≤ f := hf0 fun q => (hF01 q).1
  have hpos : 0 < quotientFunctional H hH μG μH hmod F := by
    rw [← hfF, quotientFunctional_apply_fibreAverage]
    have hne : ∃ g : G, f g ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : F q₀ = 0 := by
        rw [← hfF, quotientFibreAverage_apply]
        simp [hall]
      have h1 : F q₀ = 1 := hF1 (interior_subset hq₀K)
      linarith
    obtain ⟨g, hg⟩ := hne
    exact f.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero f.hasCompactSupport
      hf_nonneg hg
  have hle := RealRMK.le_rieszMeasure_tsupport_subset (quotientFunctional H hH μG μH hmod)
    (f := F) hF01 hFsupp
  exact (ENNReal.ofReal_pos.mpr hpos |>.trans_le hle).ne'

/-- **Right-`G`-invariance of Weil's quotient measure.** -/
theorem map_mulRight_quotientMeasure (g : G) :
    Measure.map (orbitRelQuotientMulRight H g) (quotientMeasure H hH μG μH hmod) =
      quotientMeasure H hH μG μH hmod := by
  have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_orbitRelQuotient H hH
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace
  have := regular_quotientMeasure H hH μG μH hmod
  have : (Measure.map (orbitRelQuotientMulRight H g)
      (quotientMeasure H hH μG μH hmod)).Regular :=
    Measure.Regular.map (orbitRelQuotientMulRight H g)
  refine Measure.ext_of_integral_eq_on_compactlySupported fun F => ?_
  obtain ⟨f, hfF, -⟩ := exists_quotientFibreAverage_eq H hH μH F
  rw [integral_map (orbitRelQuotientMulRight H g).continuous.aemeasurable
    (map_continuous F).aestronglyMeasurable]
  have hcomp : (fun q => F (orbitRelQuotientMulRight H g q)) =
      (F.comp (orbitRelQuotientMulRight H g).toCocompactMap : _ → ℝ) := rfl
  rw [hcomp, ← hfF, ← quotientFibreAverage_comp_mulRight,
    integral_quotientFibreAverage_quotientMeasure,
    integral_quotientFibreAverage_quotientMeasure]
  exact integral_mul_right_eq_self (μ := μG) f g

/-- **Uniqueness of Weil's quotient measure:** any Borel measure on `H \ G` finite on compacts
satisfying Weil's integral formula on compactly supported continuous functions coincides with
`quotientMeasure`. -/
theorem quotientMeasure_unique (ν : Measure (MulAction.orbitRel.Quotient H G))
    [IsFiniteMeasureOnCompacts ν]
    (hν : ∀ f : G → ℝ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μG = ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂ν) :
    ν = quotientMeasure H hH μG μH hmod := by
  have : T2Space (MulAction.orbitRel.Quotient H G) := t2Space_orbitRelQuotient H hH
  have : LocallyCompactSpace (MulAction.orbitRel.Quotient H G) :=
    (MulAction.isOpenQuotientMap_quotientMk (Γ := H) (T := G)).locallyCompactSpace
  have : ν.Regular := regular_of_isFiniteMeasureOnCompacts_orbitRelQuotient H hH ν
  have := regular_quotientMeasure H hH μG μH hmod
  refine Measure.ext_of_integral_eq_on_compactlySupported fun F => ?_
  obtain ⟨f, hfF, -⟩ := exists_quotientFibreAverage_eq H hH μH F
  rw [← hfF, integral_quotientFibreAverage_quotientMeasure]
  exact (hν f f.continuous f.hasCompactSupport).symm

/-- **Subgroup scaling law:** replacing `μH` by `c • μH` multiplies the quotient measure by
`c⁻¹`. -/
theorem quotientMeasure_smul_subgroup (c : ℝ≥0) [(c • μH).IsOpenPosMeasure] :
    quotientMeasure H hH μG (c • μH) hmod = c⁻¹ • quotientMeasure H hH μG μH hmod := by
  have hc : c ≠ 0 := fun h0 =>
    isOpen_univ.measure_ne_zero (c • μH) Set.univ_nonempty (by simp [h0])
  have := isFiniteMeasureOnCompacts_quotientMeasure H hH μG μH hmod
  symm
  refine quotientMeasure_unique H hH μG (c • μH) hmod
    (c⁻¹ • quotientMeasure H hH μG μH hmod) fun f hf hfc => ?_
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, NNReal.coe_inv]
  rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (NNReal.coe_ne_zero.mpr hc), one_mul]
  exact integral_quotientMeasure_of_continuous_hasCompactSupport H hH μG μH hmod hf hfc

/-- **Group scaling law:** replacing `μG` by `c • μG` multiplies the quotient measure by `c`. -/
theorem quotientMeasure_smul_group (c : ℝ≥0) [(c • μG).IsOpenPosMeasure] :
    quotientMeasure H hH (c • μG) μH hmod = c • quotientMeasure H hH μG μH hmod := by
  have := isFiniteMeasureOnCompacts_quotientMeasure H hH μG μH hmod
  symm
  refine quotientMeasure_unique H hH (c • μG) μH hmod
    (c • quotientMeasure H hH μG μH hmod) fun f hf hfc => ?_
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  rw [integral_quotientMeasure_of_continuous_hasCompactSupport H hH μG μH hmod hf hfc]

end QuotientMeasureConstruction

section ExistsUnique

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Weil's quotient measure:** for right Haar measures on `G` and on a closed subgroup `H`
with matching modular characters, there is exactly one right-`G`-invariant Radon measure on
`H \ G` with `∫_G f = ∫_{H \ G} ∫_H f(h g) dh d(H g)` for compactly supported continuous `f`. -/
theorem exists_unique_quotientMeasure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (MulAction.orbitRel.Quotient H G)]
    [BorelSpace (MulAction.orbitRel.Quotient H G)]
    (μG : Measure G) [μG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μG]
    [μG.IsOpenPosMeasure]
    (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
    [μH.IsOpenPosMeasure]
    (hmod : ∀ h : H, Measure.modularCharacter (G := G) h =
      Measure.modularCharacter (G := H) h) :
    ∃! ν : Measure (MulAction.orbitRel.Quotient H G), IsFiniteMeasureOnCompacts ν ∧
      (∀ g : G, Measure.map (fun q : MulAction.orbitRel.Quotient H G =>
        (Quotient.mk'' (q.out * g) : MulAction.orbitRel.Quotient H G)) ν = ν) ∧
      ∀ f : G → ℝ, Continuous f → HasCompactSupport f →
        ∫ g, f g ∂μG = ∫ q, (∫ h : H, f ((h : G) * q.out) ∂μH) ∂ν := by
  refine ⟨quotientMeasure H hH μG μH hmod,
    ⟨isFiniteMeasureOnCompacts_quotientMeasure H hH μG μH hmod, fun g => ?_,
      fun f hf hfc => integral_quotientMeasure_of_continuous_hasCompactSupport
        H hH μG μH hmod hf hfc⟩,
    fun ν ⟨hfin, _, hint⟩ => quotientMeasure_unique H hH μG μH hmod ν hint⟩
  have hfun : (fun q : MulAction.orbitRel.Quotient H G =>
      (Quotient.mk'' (q.out * g) : MulAction.orbitRel.Quotient H G)) =
      orbitRelQuotientMulRight H g :=
    funext fun q => (orbitRelQuotientMulRight_apply H g q).symm
  rw [hfun]
  exact map_mulRight_quotientMeasure H hH μG μH hmod g

end ExistsUnique

end TauCeti
