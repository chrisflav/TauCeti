/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Exponential
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Topology
public import TauCeti.Analysis.Sobolev.BesselPotential.Conj
public import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
public import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# The Banach Lie group structure on the Sobolev framed gauge group

For `s > 1`, `TauCeti.Vortex.SobolevTopologicalGaugeGroup hs` is the framed gauge group
`G_s = {1 + h : h ∈ H^s(ℂ), |1 + h| = 1}` equipped with its Sobolev topology
(`TauCeti.Analysis.PDE.Vortex.FramedGauge.Topology`). This file constructs its real-analytic Banach
manifold charts modelled on the real Banach space `BesselPotentialSpace.RealSubspace ℂ s 2` of
real-valued `H^s` functions, proves that `G_s` is a commutative Banach Lie group, and shows that
the coordinate map `u ↦ u - 1` embeds `G_s` as a closed smooth submanifold of `H^s(ℂ)`.

The global exponential homomorphism `exp hs : RealSubspace ℂ s 2 → G_s`, `f ↦ exp(i f)`, has
`H^s(ℂ)` coordinate `expSubOne (i f)` (`subOne_exp`), is injective (`exp_injective`), and is an
open embedding (`isOpenEmbedding_exp`) by the local surjectivity and argument Lipschitz estimates
of `TauCeti.Analysis.PDE.Vortex.FramedGauge.Exponential`. Left-translating `exp hs` by each element
`u ∈ G_s` produces an open cover `chartPiece hs u : f ↦ u * exp hs f` whose overlap transitions are
translations `z ↦ z + (y - x)` on `RealSubspace ℂ s 2`, hence real-analytic (`C^ω`, and therefore
`C^n` for every `n : ℕ∞ω`).

## Main definitions

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.exp`: the exponential map
  `f ↦ exp(i f)` from `RealSubspace ℂ s 2` to `G_s`, bundled as `expHom`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.chartPiece`: the exponential chart
  `f ↦ u * exp hs f` centred at `u ∈ G_s`.
* `ChartedSpace`, `IsManifold`, and `LieGroup` instances on `SobolevTopologicalGaugeGroup hs`
  modelled on `𝓘(ℝ, RealSubspace ℂ s 2)` for every regularity `n : ℕ∞ω`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.mulGaugeCLE`: pointwise multiplication by `u ∈ G_s`
  as a continuous `ℂ`-linear equivalence `H^s(ℂ) ≃L[ℂ] H^s(ℂ)`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.inclusionHom`: the smooth group homomorphism
  `G_{s₂} →* G_{s₁}` for `1 < s₁ ≤ s₂`.

## Main results

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.isClosedEmbedding_subOne`: `u ↦ u - 1` is a closed
  topological embedding of `G_s` into `H^s(ℂ)` with image `{h | ∀ z, ‖1 + h(z)‖ = 1}`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.isOpenEmbedding_exp`: `exp hs` is an open embedding.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.isSmoothEmbedding_subOne`: for `1 ≤ n`, `u ↦ u - 1`
  is a `C^n` smooth embedding into `H^s(ℂ)`, so a map into `G_s` is `C^n` iff its `H^s(ℂ)`
  coordinate `u - 1` is `C^n` (`contMDiff_iff_subOne`).
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_mulGauge`: the linear gauge action
  `(u, h) ↦ mulGaugeCLE u h` on `H^s(ℂ)` is `C^n`.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_inclusionHom`: `G_{s₂} →* G_{s₁}` is `C^n`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, §3.
-/

public section

noncomputable section

namespace TauCeti.Vortex.SobolevTopologicalGaugeGroup

open Filter MeasureTheory Module TemperedDistribution BesselPotentialSpace Topology
open scoped SchwartzMap BesselPotentialSpace ZeroAtInfty Manifold ContDiff

variable {s : ℝ} {hs : 1 < s}

-- Stated as a theorem rather than a `CommGroup` instance so the opaque `Group` instance from
-- `Topology.lean` remains unique across `module` boundaries.
/-- Multiplication in `G_s` is commutative. -/
protected theorem mul_comm (u v : SobolevTopologicalGaugeGroup hs) : u * v = v * u :=
  (toSubgroup hs).injective (by rw [map_mul, map_mul, _root_.mul_comm])

protected theorem mul_inv (u v : SobolevTopologicalGaugeGroup hs) : (u * v)⁻¹ = u⁻¹ * v⁻¹ := by
  rw [mul_inv_rev, SobolevTopologicalGaugeGroup.mul_comm]

/-! ### Closed embedding into `H^s(ℂ)` -/

/-- Under the Sobolev embedding `toZeroAtInfty`, `subOne u` evaluates everywhere to `u(z) - 1`. -/
@[simp]
theorem toZeroAtInfty_subOne_apply (u : SobolevTopologicalGaugeGroup hs) (z : ℂ) :
    toZeroAtInfty (finrank_real_complex_lt_two_mul hs) (subOne u) z =
      ((toSubgroup hs u : ℂ → Circle) z : ℂ) - 1 := by
  have hcont : Continuous fun w ↦ ((toSubgroup hs u : ℂ → Circle) w : ℂ) - 1 :=
    (continuous_subtype_val.comp ((mem_sobolevGaugeGroup hs _).1 (toSubgroup hs u).2).1).sub
      continuous_const
  exact congrFun (coe_toZeroAtInfty_eq_of_ae_eq (finrank_real_complex_lt_two_mul hs) hcont
    (coeFn_toLp_inclusion_subOne (zero_le_one.trans hs.le) u)) z

/-- Inversion in `G_s` acts on `u - 1 ∈ H^s(ℂ)` by the isometric `ℝ`-linear conjugation
`conjLIE`. -/
@[simp]
theorem subOne_inv (u : SobolevTopologicalGaugeGroup hs) :
    subOne u⁻¹ = conjLIE ℂ s 2 (subOne u) := by
  apply toZeroAtInfty_injective (finrank_real_complex_lt_two_mul hs)
  ext z
  rw [toZeroAtInfty_subOne_apply, toZeroAtInfty_conjLIE, ZeroAtInftyContinuousMap.star_apply,
    toZeroAtInfty_subOne_apply, map_inv]
  simp only [InvMemClass.coe_inv, Pi.inv_apply, Circle.coe_inv, star_sub, RCLike.star_def,
    star_one, sub_left_inj]
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]

/-- The single coordinate `u ↦ subOne u` embeds `G_s` topologically into `H^s(ℂ)`. -/
theorem isEmbedding_subOne :
    IsEmbedding (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  have hcomp : (fun h : H^{s}(ℂ) ↦ (h, conjLIE ℂ s 2 h)) ∘
      (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) =
      fun u ↦ (subOne u, subOne u⁻¹) :=
    funext fun u ↦ by simp
  exact .of_comp continuous_subOne (continuous_id.prodMk (conjLIE ℂ s 2).continuous)
    (hcomp ▸ isEmbedding_subOne_prod)

/-- Continuity into `G_s` is equivalent to continuity of `x ↦ subOne (f x)` in `H^s(ℂ)`. -/
theorem continuous_iff_subOne {X : Type*} [TopologicalSpace X]
    {f : X → SobolevTopologicalGaugeGroup hs} :
    Continuous f ↔ Continuous fun x ↦ subOne (f x) :=
  isEmbedding_subOne.continuous_iff

/-- The image of `subOne : G_s → H^s(ℂ)` consists of the elements `h ∈ H^s(ℂ)` whose continuous
representative `g = toZeroAtInfty h` satisfies `‖1 + g(z)‖ = 1` at every point `z ∈ ℂ`. -/
theorem range_subOne :
    Set.range (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) =
      {h | ∀ z : ℂ, ‖1 + toZeroAtInfty (finrank_real_complex_lt_two_mul hs) h z‖ = 1} := by
  have hs' := finrank_real_complex_lt_two_mul hs
  ext h
  constructor
  · rintro ⟨u, rfl⟩ z
    rw [toZeroAtInfty_subOne_apply, add_sub_cancel]
    exact Circle.norm_coe _
  · intro hh
    set g := toZeroAtInfty hs' h
    let v : ℂ → Circle := fun z ↦ ⟨1 + g z, mem_sphere_zero_iff_norm.2 (hh z)⟩
    have hv : v ∈ sobolevGaugeGroup hs := by
      refine (mem_sobolevGaugeGroup hs v).2
        ⟨continuous_induced_rng.2 (continuous_const.add (map_continuous g)), ?_, ?_⟩
      · convert re_toZeroAtInfty_mem_realSobolevFunctions hs' (reCLM_mem_realSubmodule h) using 1
        ext z
        simp [v, g]
      · convert re_toZeroAtInfty_mem_realSobolevFunctions hs' (imCLM_mem_realSubmodule h) using 1
        ext z
        simp [v, g]
    refine ⟨(toSubgroup hs).symm ⟨v, hv⟩, toZeroAtInfty_injective hs' ?_⟩
    ext z
    simp [v, g]

/-- The image of `subOne : G_s → H^s(ℂ)` is closed in `H^s(ℂ)`. -/
theorem isClosed_range_subOne :
    IsClosed (Set.range (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ))) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  rw [range_subOne, Set.ofPred_forall]
  refine isClosed_iInter fun z ↦ isClosed_eq ?_ continuous_const
  have heval : Continuous fun h : H^{s}(ℂ) ↦ toZeroAtInfty hs' h z :=
    (BoundedContinuousFunction.evalCLM ℂ z).continuous.comp
      (ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp (toZeroAtInfty hs').continuous)
  exact (continuous_const.add heval).norm

/-- `subOne` is a closed embedding of `G_s` into the Hilbert space `H^s(ℂ)`. -/
theorem isClosedEmbedding_subOne :
    IsClosedEmbedding (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) :=
  ⟨isEmbedding_subOne, isClosed_range_subOne⟩

/-! ### The exponential homomorphism and open embedding -/

variable (hs) in
/-- **The exponential map `f ↦ exp(i f)`** from the real Sobolev space `RealSubspace ℂ s 2` into
the Sobolev framed gauge group `G_s`. -/
def exp (f : RealSubspace ℂ s 2) : SobolevTopologicalGaugeGroup hs :=
  (toSubgroup hs).symm ⟨fun z ↦ Circle.exp
      (toZeroAtInfty (finrank_real_complex_lt_two_mul hs) (RealSubspace.valLI f) z).re,
    exp_mem_sobolevGaugeGroup hs (Complex.continuous_re.comp (map_continuous _))
      (re_toZeroAtInfty_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs)
        f.valLI_mem)⟩

@[simp]
theorem toSubgroup_exp_apply (f : RealSubspace ℂ s 2) (z : ℂ) :
    (toSubgroup hs (exp hs f) : ℂ → Circle) z =
      Circle.exp
        (toZeroAtInfty (finrank_real_complex_lt_two_mul hs) (RealSubspace.valLI f) z).re := by
  simp [exp]

/-- In `H^s(ℂ)` coordinates, `exp hs f` is given by the entire power series `expSubOne (i • f)`. -/
@[simp]
theorem subOne_exp (f : RealSubspace ℂ s 2) :
    subOne (exp hs f) =
      expSubOne (finrank_real_complex_lt_two_mul hs) (Complex.I • RealSubspace.valLI f) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  apply toZeroAtInfty_injective hs'
  ext z
  rw [toZeroAtInfty_subOne_apply, toSubgroup_exp_apply, Circle.coe_exp,
    toZeroAtInfty_expSubOne_apply, map_smul, _root_.smul_apply, smul_eq_mul,
    mul_comm Complex.I, ← toZeroAtInfty_apply_eq_re_of_mem_realSubmodule hs' f.valLI_mem z]

@[simp]
theorem exp_zero : exp hs 0 = 1 :=
  subOne_injective (by simp)

theorem exp_add (f g : RealSubspace ℂ s 2) : exp hs (f + g) = exp hs f * exp hs g :=
  subOne_injective (by simp [subOne_mul, smul_add, expSubOne_add])

theorem exp_neg (f : RealSubspace ℂ s 2) : exp hs (-f) = (exp hs f)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← exp_add, neg_add_cancel, exp_zero])

theorem exp_sub (f g : RealSubspace ℂ s 2) : exp hs (f - g) = exp hs f * (exp hs g)⁻¹ := by
  rw [sub_eq_add_neg, exp_add, exp_neg]

variable (hs) in
/-- `exp hs` bundled as a group homomorphism `Multiplicative (RealSubspace ℂ s 2) →* G_s`. -/
def expHom : Multiplicative (RealSubspace ℂ s 2) →* SobolevTopologicalGaugeGroup hs where
  toFun f := exp hs (Multiplicative.toAdd f)
  map_one' := exp_zero
  map_mul' _ _ := exp_add _ _

/-- `exp hs` is globally injective: two real `H^s` phases with the same exponential vanish at
infinity on the connected plane, so they coincide everywhere. -/
theorem exp_injective : Function.Injective (exp hs) := by
  intro f g hfg
  have hs' := finrank_real_complex_lt_two_mul hs
  let F : ℂ → ℝ := fun z ↦ (toZeroAtInfty hs' (RealSubspace.valLI f) z).re
  let G : ℂ → ℝ := fun z ↦ (toZeroAtInfty hs' (RealSubspace.valLI g) z).re
  have hF : Continuous F ∧ F ∈ realSobolevFunctions ℂ s 2 :=
    ⟨Complex.continuous_re.comp (map_continuous _),
      re_toZeroAtInfty_mem_realSobolevFunctions hs' f.valLI_mem⟩
  have hG : Continuous G ∧ G ∈ realSobolevFunctions ℂ s 2 :=
    ⟨Complex.continuous_re.comp (map_continuous _),
      re_toZeroAtInfty_mem_realSobolevFunctions hs' g.valLI_mem⟩
  have hexp : (fun z ↦ Circle.exp (F z)) = fun z ↦ Circle.exp (G z) :=
    funext fun z ↦ by
      simpa [F, G] using congrFun (congrArg Subtype.val (congrArg (toSubgroup hs) hfg)) z
  have hFG := injOn_exp hs hF hG hexp
  refine RealSubspace.ext (toZeroAtInfty_injective hs' ?_)
  ext z
  rw [toZeroAtInfty_apply_eq_re_of_mem_realSubmodule hs' f.valLI_mem z,
    toZeroAtInfty_apply_eq_re_of_mem_realSubmodule hs' g.valLI_mem z]
  exact congrArg Complex.ofReal (congrFun hFG z)

@[fun_prop, continuity]
theorem continuous_exp : Continuous (exp hs) :=
  continuous_iff_subOne.2 <| by
    simp only [subOne_exp]
    exact (contDiff_real_expSubOne (n := 0) _).continuous.comp
      (RealSubspace.valLI.continuous.const_smul Complex.I)

/-- Every gauge sufficiently close to `1` in `H^s` norm lies in the image of `exp hs`. -/
private theorem exists_mem_range_exp_of_norm_subOne_lt :
    ∃ δ > 0, ∀ u : SobolevTopologicalGaugeGroup hs, ‖subOne u‖ < δ →
      u ∈ Set.range (exp hs) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  have h0 : 0 ≤ s := zero_le_one.trans hs.le
  obtain ⟨δ, hδ, hexp⟩ := exists_continuous_mem_realSobolevFunctions_eq_exp hs
  refine ⟨δ, hδ, fun u hu ↦ ?_⟩
  have hh := memSobolev_toLp_inclusion h0 (subOne u)
  have hhh : hh.toBesselPotentialSpace = subOne u :=
    toBesselPotentialSpace_memSobolev_toLp_inclusion h0 (subOne u)
  obtain ⟨k, hk_cont, hk_sob, hku⟩ := hexp (toSubgroup hs u) (toSubgroup hs u).2
    (coeFn_toLp_inclusion_subOne h0 u) hh (by rwa [hhh])
  obtain ⟨f, hf_mem, hfk⟩ := exists_mem_realSubmodule_toZeroAtInfty_eq_ofReal hs' hk_cont hk_sob
  refine ⟨RealSubspace.mk f hf_mem, (toSubgroup hs).injective (Subtype.ext ?_)⟩
  funext z
  rw [toSubgroup_exp_apply, RealSubspace.valLI_mk, hku, hfk z, Complex.ofReal_re]

private theorem toBesselPotentialSpace_eq_of_ae_eq_toZeroAtInfty (hs : 1 < s)
    {F : Lp ℂ 2 (volume : Measure ℂ)} (hFs : MemSobolev s 2 (Lp.toTemperedDistribution F))
    {g : H^{s}(ℂ)}
    (hae : (F : ℂ → ℂ) =ᵐ[volume] toZeroAtInfty (finrank_real_complex_lt_two_mul hs) g) :
    hFs.toBesselPotentialSpace = g := by
  have h0 : 0 ≤ s := zero_le_one.trans hs.le
  have hF_lp : F = (inclusion h0 g).toLp := Lp.ext <| hae.trans
    (coeFn_toLp_inclusion_ae_eq_toZeroAtInfty (finrank_real_complex_lt_two_mul hs) h0 g).symm
  apply BesselPotentialSpace.ext
  rw [hFs.toBesselPotentialSpace_toDistr, hF_lp,
    ← (memSobolev_toLp_inclusion h0 g).toBesselPotentialSpace_toDistr,
    toBesselPotentialSpace_memSobolev_toLp_inclusion]

private theorem continuous_arg_of_norm_subOne_lt (u : SobolevTopologicalGaugeGroup hs)
    (hnorm : ∀ z : ℂ, ‖((toSubgroup hs u : ℂ → Circle) z : ℂ) - 1‖ < 1) :
    Continuous fun z ↦ Complex.arg ((toSubgroup hs u : ℂ → Circle) z : ℂ) := by
  have hu_cont : Continuous fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ) :=
    continuous_subtype_val.comp ((mem_sobolevGaugeGroup hs _).1 (toSubgroup hs u).2).1
  refine continuous_iff_continuousAt.2 fun z ↦
    (Complex.continuousAt_arg ?_).comp_of_eq hu_cont.continuousAt rfl
  simpa using Complex.mem_slitPlane_of_norm_lt_one (hnorm z)

/-- Near `1 ∈ G_s`, the phase `f` is controlled linearly by `‖subOne (exp hs f)‖`. -/
private theorem exists_norm_le_mul_norm_subOne_exp :
    ∃ δ > 0, ∃ K : ℝ, 0 < K ∧ ∀ f : RealSubspace ℂ s 2,
      ‖subOne (exp hs f)‖ < δ → ‖f‖ ≤ K * ‖subOne (exp hs f)‖ := by
  have hs' := finrank_real_complex_lt_two_mul hs
  have h0 : 0 ≤ s := zero_le_one.trans hs.le
  obtain ⟨C, hC, harg⟩ := exists_memSobolev_ae_eq_arg_and_norm_sub_le hs
  set M := (eLpNorm (fun ξ : ℂ ↦ (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 volume).toReal
  set δ : ℝ := min ((M + 1)⁻¹) ((2 * C + 2)⁻¹)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, (1 - C * δ)⁻¹, ?_, fun f hf ↦ ?_⟩
  · have hCδ : C * δ ≤ 2⁻¹ := by
      calc C * δ ≤ C * (2 * C + 2)⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
        _ ≤ 2⁻¹ := by rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
    exact inv_pos.2 (by linarith)
  · have hCδ : C * δ < 1 :=
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hC).trans_lt
        ((mul_inv_lt_iff₀ (by positivity)).2 (by linarith))
    set u := exp hs f
    have hnorm (z : ℂ) : ‖((toSubgroup hs u : ℂ → Circle) z : ℂ) - 1‖ < 1 := calc
      ‖((toSubgroup hs u : ℂ → Circle) z : ℂ) - 1‖
        = ‖toZeroAtInfty hs' (subOne u) z‖ := by rw [toZeroAtInfty_subOne_apply]
      _ ≤ M * ‖subOne u‖ := norm_toZeroAtInfty_apply_le hs' (subOne u) z
      _ ≤ M * δ := mul_le_mul_of_nonneg_left hf.le ENNReal.toReal_nonneg
      _ < (M + 1) * (M + 1)⁻¹ :=
          (by nlinarith : M * δ < (M + 1) * δ).trans_le
            (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity))
      _ = 1 := mul_inv_cancel₀ (by positivity)
    -- Apply the Lipschitz `arg` bound to `u = exp hs f` and `1`, then identify `F = f`, `F' = 0`.
    have hh := memSobolev_toLp_inclusion h0 (subOne u)
    have hhh : hh.toBesselPotentialSpace = subOne u :=
      toBesselPotentialSpace_memSobolev_toLp_inclusion h0 (subOne u)
    have hh1 := memSobolev_toLp_inclusion h0 (subOne (1 : SobolevTopologicalGaugeGroup hs))
    have hhh1 : hh1.toBesselPotentialSpace = 0 := by
      rw [toBesselPotentialSpace_memSobolev_toLp_inclusion, subOne_one]
    obtain ⟨F, F', hF_ae, hF'_ae, hFs, hF's, hbound⟩ := harg
      (coeFn_toLp_inclusion_subOne h0 u)
      (coeFn_toLp_inclusion_subOne h0 (1 : SobolevTopologicalGaugeGroup hs))
      hh hh1 (R := δ) (by rw [hhh]; exact hf.le) (by rw [hhh1, norm_zero]; exact hδ.le) hCδ
    have hk_eq : (fun z ↦ Complex.arg ((toSubgroup hs u : ℂ → Circle) z : ℂ)) =
        fun z ↦ (toZeroAtInfty hs' (RealSubspace.valLI f) z).re :=
      injOn_exp hs ⟨continuous_arg_of_norm_subOne_lt u hnorm,
          mem_realSobolevFunctions_of_ae_eq_ofReal hFs hF_ae⟩
        ⟨Complex.continuous_re.comp (map_continuous _),
          re_toZeroAtInfty_mem_realSobolevFunctions hs' f.valLI_mem⟩
        (funext fun z ↦ by dsimp only; rw [Circle.exp_arg, toSubgroup_exp_apply])
    have hF_eq : hFs.toBesselPotentialSpace = RealSubspace.valLI f :=
      toBesselPotentialSpace_eq_of_ae_eq_toZeroAtInfty hs hFs (by
        filter_upwards [hF_ae] with z hz
        rw [hz, toZeroAtInfty_apply_eq_re_of_mem_realSubmodule hs' f.valLI_mem z]
        exact congrArg Complex.ofReal (congrFun hk_eq z))
    have hF'_eq : hF's.toBesselPotentialSpace = 0 :=
      toBesselPotentialSpace_eq_of_ae_eq_toZeroAtInfty hs hF's (by
        filter_upwards [hF'_ae] with z hz; rw [hz, map_one]; simp)
    rw [← RealSubspace.valLI.norm_map]
    rwa [hF_eq, hF'_eq, sub_zero, hhh, hhh1, sub_zero] at hbound

/-- **The exponential map `exp hs : RealSubspace ℂ s 2 → G_s` is an open embedding.** -/
theorem isOpenEmbedding_exp : IsOpenEmbedding (exp hs) := by
  obtain ⟨δ₁, hδ₁, hrange⟩ := exists_mem_range_exp_of_norm_subOne_lt (hs := hs)
  obtain ⟨δ₂, hδ₂, K, hK, hlip⟩ := exists_norm_le_mul_norm_subOne_exp (hs := hs)
  have hind : IsInducing (exp hs) := by
    rw [isInducing_iff_nhds]
    intro f₀
    refine le_antisymm (tendsto_iff_comap.1 continuous_exp.continuousAt.tendsto) ?_
    rw [Metric.nhds_basis_ball.ge_iff]
    intro ε hε
    set r := min δ₂ (ε / (K + 1))
    have hr : 0 < r := lt_min hδ₂ (by positivity)
    let V : Set (SobolevTopologicalGaugeGroup hs) :=
      (fun u ↦ subOne (u * (exp hs f₀)⁻¹)) ⁻¹' Metric.ball 0 r
    have hV : V ∈ 𝓝 (exp hs f₀) := by
      refine (continuous_subOne.comp
        (continuous_id.mul continuous_const)).continuousAt.preimage_mem_nhds ?_
      simpa using Metric.ball_mem_nhds 0 hr
    refine ⟨V, hV, fun f hf ↦ ?_⟩
    have hsub : exp hs f * (exp hs f₀)⁻¹ = exp hs (f - f₀) := (exp_sub f f₀).symm
    have hnorm : ‖subOne (exp hs (f - f₀))‖ < r := by
      simpa [V, hsub] using hf
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖f - f₀‖ ≤ K * ‖subOne (exp hs (f - f₀))‖ :=
          hlip (f - f₀) (hnorm.trans_le (min_le_left _ _))
      _ ≤ K * r := mul_le_mul_of_nonneg_left hnorm.le hK.le
      _ < (K + 1) * (ε / (K + 1)) := by
          calc K * r < (K + 1) * r := by nlinarith
            _ ≤ (K + 1) * (ε / (K + 1)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = ε := mul_div_cancel₀ ε (by positivity)
  have hopen : IsOpen (Set.range (exp hs)) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨f₀, rfl⟩
    let W : Set (SobolevTopologicalGaugeGroup hs) :=
      (fun u ↦ subOne (u * (exp hs f₀)⁻¹)) ⁻¹' Metric.ball 0 δ₁
    have hW : W ∈ 𝓝 (exp hs f₀) := by
      refine (continuous_subOne.comp
        (continuous_id.mul continuous_const)).continuousAt.preimage_mem_nhds ?_
      simpa using Metric.ball_mem_nhds 0 hδ₁
    refine Filter.mem_of_superset hW fun u hu ↦ ?_
    obtain ⟨g, hg⟩ := hrange (u * (exp hs f₀)⁻¹) (by simpa [W] using hu)
    exact ⟨g + f₀, by rw [exp_add, hg, mul_assoc, inv_mul_cancel, mul_one]⟩
  exact ⟨⟨hind, exp_injective⟩, hopen⟩

/-! ### Banach manifold and Lie group structure -/

variable (hs) in
/-- **The exponential chart `f ↦ u * exp hs f` centred at `u ∈ G_s`.** -/
def chartPiece (u : SobolevTopologicalGaugeGroup hs) (f : RealSubspace ℂ s 2) :
    SobolevTopologicalGaugeGroup hs :=
  u * exp hs f

@[simp]
theorem chartPiece_apply (u : SobolevTopologicalGaugeGroup hs) (f : RealSubspace ℂ s 2) :
    chartPiece hs u f = u * exp hs f := by rfl

theorem chartPiece_zero (u : SobolevTopologicalGaugeGroup hs) : chartPiece hs u 0 = u := by
  simp

/-- Every translated exponential chart `chartPiece hs u` is an open embedding into `G_s`. -/
theorem isOpenEmbedding_chartPiece (u : SobolevTopologicalGaugeGroup hs) :
    IsOpenEmbedding (chartPiece hs u) :=
  (Homeomorph.mulLeft u).isOpenEmbedding.comp isOpenEmbedding_exp

theorem chartPiece_surjective (x : SobolevTopologicalGaugeGroup hs) :
    ∃ u f, chartPiece hs u f = x :=
  ⟨x, 0, chartPiece_zero x⟩

/-- Overlap transitions between two exponential charts are affine translations `z ↦ z + (y - x)`,
hence `C^n` for every `n : ℕ∞ω` (including `ω`). -/
private theorem chartPiece_deck {n : ℕ∞ω} (u v : SobolevTopologicalGaugeGroup hs)
    (x y : RealSubspace ℂ s 2) (hxy : chartPiece hs u x = chartPiece hs v y) :
    ∃ T : RealSubspace ℂ s 2 → RealSubspace ℂ s 2,
      ContMDiffAt 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, RealSubspace ℂ s 2) n T x ∧
        chartPiece hs v ∘ T =ᶠ[𝓝 x] chartPiece hs u := by
  refine ⟨fun z ↦ z + (y - x), (contMDiff_id.add contMDiff_const).contMDiffAt,
    Eventually.of_forall fun z ↦ ?_⟩
  have hadd : z + (y - x) = y - x + z := by abel
  have hxy' : v * exp hs y = u * exp hs x := by simpa only [chartPiece_apply] using hxy.symm
  rw [Function.comp_apply, chartPiece_apply, chartPiece_apply, hadd, exp_add, exp_sub,
    ← mul_assoc, ← mul_assoc, hxy', mul_inv_cancel_right]

/-- Banach chart atlas on `G_s` modelled on `RealSubspace ℂ s 2` via translated exponential maps. -/
instance : ChartedSpace (RealSubspace ℂ s 2) (SobolevTopologicalGaugeGroup hs) :=
  TauCeti.chartedSpaceOfIsOpenEmbedding (H := RealSubspace ℂ s 2)
    (isOpenEmbedding_chartPiece (hs := hs)) chartPiece_surjective

/-- `G_s` is a `C^n` Banach manifold (including `C^ω`) modelled on `RealSubspace ℂ s 2`. -/
instance {n : ℕ∞ω} : IsManifold 𝓘(ℝ, RealSubspace ℂ s 2) n (SobolevTopologicalGaugeGroup hs) :=
  TauCeti.isManifold_chartedSpaceOfIsOpenEmbedding (I := 𝓘(ℝ, RealSubspace ℂ s 2)) (n := n)
    (isOpenEmbedding_chartPiece (hs := hs)) chartPiece_surjective chartPiece_deck

theorem contMDiff_chartPiece {n : ℕ∞ω} (u : SobolevTopologicalGaugeGroup hs) :
    ContMDiff 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, RealSubspace ℂ s 2) n (chartPiece hs u) :=
  TauCeti.contMDiff_chartedSpaceOfIsOpenEmbedding (I := 𝓘(ℝ, RealSubspace ℂ s 2)) (n := n)
    (isOpenEmbedding_chartPiece (hs := hs)) chartPiece_surjective chartPiece_deck u

theorem isLocalDiffeomorph_chartPiece {n : ℕ∞ω} (u : SobolevTopologicalGaugeGroup hs) :
    IsLocalDiffeomorph 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, RealSubspace ℂ s 2) n (chartPiece hs u) :=
  TauCeti.isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding (I := 𝓘(ℝ, RealSubspace ℂ s 2))
    (n := n) (isOpenEmbedding_chartPiece (hs := hs)) chartPiece_surjective chartPiece_deck u

/-- Smoothness out of `G_s` is tested by precomposing with every exponential chart `chartPiece`. -/
theorem contMDiff_iff_comp_chartPiece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] {n : ℕ∞ω}
    {g : SobolevTopologicalGaugeGroup hs → N} :
    ContMDiff 𝓘(ℝ, RealSubspace ℂ s 2) I n g ↔
      ∀ u, ContMDiff 𝓘(ℝ, RealSubspace ℂ s 2) I n (g ∘ chartPiece hs u) :=
  TauCeti.contMDiff_iff_chartedSpaceOfIsOpenEmbedding (I := 𝓘(ℝ, RealSubspace ℂ s 2)) (n := n)
    (isOpenEmbedding_chartPiece (hs := hs)) chartPiece_surjective chartPiece_deck

theorem contMDiff_exp {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, RealSubspace ℂ s 2) n (exp hs) := by
  have heq : exp hs = chartPiece hs 1 := funext fun f ↦ by simp
  rw [heq]
  exact contMDiff_chartPiece 1

theorem isLocalDiffeomorph_exp {n : ℕ∞ω} :
    IsLocalDiffeomorph 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, RealSubspace ℂ s 2) n (exp hs) := by
  have heq : exp hs = chartPiece hs 1 := funext fun f ↦ by simp
  rw [heq]
  exact isLocalDiffeomorph_chartPiece 1

/-- The exponential map `exp hs : RealSubspace ℂ s 2 → G_s` is a `C^n` smooth open embedding. -/
theorem isSmoothEmbedding_exp {n : ℕ∞ω} :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, RealSubspace ℂ s 2) n (exp hs) :=
  ⟨TauCeti.isImmersion_comp_isLocalDiffeomorph (f := id) isLocalDiffeomorph_exp
      (Manifold.IsImmersion.id (I := 𝓘(ℝ, RealSubspace ℂ s 2)) (n := n)
        (M := SobolevTopologicalGaugeGroup hs)),
    isOpenEmbedding_exp.isEmbedding⟩

/-- **`G_s` is a real-analytic (hence `C^n` for every `n : ℕ∞ω`) Banach Lie group** modelled on
`RealSubspace ℂ s 2`. -/
instance {n : ℕ∞ω} : LieGroup 𝓘(ℝ, RealSubspace ℂ s 2) n (SobolevTopologicalGaugeGroup hs) where
  contMDiff_mul := fun ⟨u, v⟩ ↦ by
    have hp := (isLocalDiffeomorph_chartPiece (hs := hs) (n := n) u 0).prodMap
      (isLocalDiffeomorph_chartPiece (hs := hs) (n := n) v 0)
    have hp0 : Prod.map (chartPiece hs u) (chartPiece hs v) (0, 0) = (u, v) := by simp
    rw [← hp0, ← hp.contMDiffAt_comp_iff le_rfl]
    have hmul : (fun q : SobolevTopologicalGaugeGroup hs × SobolevTopologicalGaugeGroup hs ↦
        q.1 * q.2) ∘ Prod.map (chartPiece hs u) (chartPiece hs v) =
        fun q : RealSubspace ℂ s 2 × RealSubspace ℂ s 2 ↦ chartPiece hs (u * v) (q.1 + q.2) := by
      ext ⟨f, g⟩
      dsimp only [Function.comp_apply, Prod.map_apply]
      calc chartPiece hs u f * chartPiece hs v g
        _ = u * (exp hs f * v) * exp hs g := by simp [chartPiece_apply, mul_assoc]
        _ = u * (v * exp hs f) * exp hs g := by
            rw [SobolevTopologicalGaugeGroup.mul_comm (exp hs f) v]
        _ = u * v * (exp hs f * exp hs g) := by simp [mul_assoc]
        _ = chartPiece hs (u * v) (f + g) := by rw [← exp_add, chartPiece_apply]
    rw [hmul]
    exact ((contMDiff_chartPiece (u * v)).comp (contMDiff_fst.add contMDiff_snd)).contMDiffAt
  contMDiff_inv := contMDiff_iff_comp_chartPiece.2 fun u ↦ by
    have hinv : (fun a : SobolevTopologicalGaugeGroup hs ↦ a⁻¹) ∘ chartPiece hs u =
        chartPiece hs u⁻¹ ∘ fun x : RealSubspace ℂ s 2 ↦ -x := by
      ext f
      rw [Function.comp_apply, Function.comp_apply, chartPiece_apply,
        SobolevTopologicalGaugeGroup.mul_inv, ← exp_neg, chartPiece_apply]
    rw [hinv]
    exact (contMDiff_chartPiece u⁻¹).comp (contMDiff_neg 𝓘(ℝ, RealSubspace ℂ s 2) n)

/-! ### Linear gauge multiplication, smooth submanifold embedding, and order inclusions -/

/-- Pointwise multiplication by `u ∈ G_s` on `H^s(ℂ)`, as a continuous `ℂ`-linear map
`h ↦ h + (u - 1) h`. -/
def mulGaugeCLM (u : SobolevTopologicalGaugeGroup hs) : H^{s}(ℂ) →L[ℂ] H^{s}(ℂ) :=
  .id ℂ H^{s}(ℂ) + mulCLM (finrank_real_complex_lt_two_mul hs) (subOne u)

theorem mulGaugeCLM_apply (u : SobolevTopologicalGaugeGroup hs) (h : H^{s}(ℂ)) :
    mulGaugeCLM u h = h + mulCLM (finrank_real_complex_lt_two_mul hs) (subOne u) h := by rfl

@[simp]
theorem toZeroAtInfty_mulGaugeCLM_apply (u : SobolevTopologicalGaugeGroup hs) (h : H^{s}(ℂ))
    (z : ℂ) :
    toZeroAtInfty (finrank_real_complex_lt_two_mul hs) (mulGaugeCLM u h) z =
      ((toSubgroup hs u : ℂ → Circle) z : ℂ) *
        toZeroAtInfty (finrank_real_complex_lt_two_mul hs) h z := by
  simp [mulGaugeCLM_apply]
  ring

@[simp]
theorem mulGaugeCLM_one : mulGaugeCLM (1 : SobolevTopologicalGaugeGroup hs) = .id ℂ H^{s}(ℂ) := by
  ext1 h
  apply toZeroAtInfty_injective (finrank_real_complex_lt_two_mul hs)
  ext z
  rw [toZeroAtInfty_mulGaugeCLM_apply, map_one]
  simp

@[simp]
theorem mulGaugeCLM_mul (u v : SobolevTopologicalGaugeGroup hs) :
    mulGaugeCLM (u * v) = (mulGaugeCLM u).comp (mulGaugeCLM v) := by
  ext1 h
  apply toZeroAtInfty_injective (finrank_real_complex_lt_two_mul hs)
  ext z
  rw [toZeroAtInfty_mulGaugeCLM_apply, ContinuousLinearMap.comp_apply,
    toZeroAtInfty_mulGaugeCLM_apply, toZeroAtInfty_mulGaugeCLM_apply, map_mul]
  simp [mul_assoc]

/-- **Pointwise multiplication by `u ∈ G_s` as a continuous `ℂ`-linear equivalence** of `H^s(ℂ)`,
with inverse `mulGaugeCLE u⁻¹`. -/
def mulGaugeCLE (u : SobolevTopologicalGaugeGroup hs) : H^{s}(ℂ) ≃L[ℂ] H^{s}(ℂ) :=
  ContinuousLinearEquiv.equivOfInverse (mulGaugeCLM u) (mulGaugeCLM u⁻¹)
    (fun h ↦ by
      have h1 := congrArg (· h) (mulGaugeCLM_mul u⁻¹ u)
      rw [inv_mul_cancel, mulGaugeCLM_one, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] at h1
      exact h1.symm)
    (fun h ↦ by
      have h1 := congrArg (· h) (mulGaugeCLM_mul u u⁻¹)
      rw [mul_inv_cancel, mulGaugeCLM_one, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] at h1
      exact h1.symm)

@[simp]
theorem coe_mulGaugeCLE (u : SobolevTopologicalGaugeGroup hs) :
    (mulGaugeCLE u : H^{s}(ℂ) →L[ℂ] H^{s}(ℂ)) = mulGaugeCLM u := by rfl

theorem mulGaugeCLE_apply (u : SobolevTopologicalGaugeGroup hs) (h : H^{s}(ℂ)) :
    mulGaugeCLE u h = h + mulCLM (finrank_real_complex_lt_two_mul hs) (subOne u) h := by rfl

@[simp]
theorem mulGaugeCLE_symm (u : SobolevTopologicalGaugeGroup hs) :
    (mulGaugeCLE u).symm = mulGaugeCLE u⁻¹ := by
  ext h
  rfl

@[simp]
theorem toZeroAtInfty_mulGaugeCLE_apply (u : SobolevTopologicalGaugeGroup hs) (h : H^{s}(ℂ))
    (z : ℂ) :
    toZeroAtInfty (finrank_real_complex_lt_two_mul hs) (mulGaugeCLE u h) z =
      ((toSubgroup hs u : ℂ → Circle) z : ℂ) *
        toZeroAtInfty (finrank_real_complex_lt_two_mul hs) h z :=
  toZeroAtInfty_mulGaugeCLM_apply u h z

theorem subOne_mul_eq_mulGaugeCLE_add (u v : SobolevTopologicalGaugeGroup hs) :
    subOne (u * v) = mulGaugeCLE u (subOne v) + subOne u := by
  rw [subOne_mul, mulGaugeCLE_apply]
  abel

/-- The Lie-algebra inclusion `f ↦ i • f` from `RealSubspace ℂ s 2` into `H^s(ℂ)`. -/
private def lieAlgebraInclCLM (s : ℝ) : RealSubspace ℂ s 2 →L[ℝ] H^{s}(ℂ) :=
  ((Complex.I • ContinuousLinearMap.id ℂ H^{s}(ℂ)).restrictScalars ℝ).comp RealSubspace.valCLM

private theorem hasLeftInverse_lieAlgebraInclCLM (hs : 1 < s) :
    (lieAlgebraInclCLM s).HasLeftInverse :=
  ⟨RealSubspace.imCLM (E := ℂ) (s := s) (p := 2), fun f ↦ RealSubspace.ext <| by
    have hs' := finrank_real_complex_lt_two_mul hs
    apply toZeroAtInfty_injective hs'
    ext z
    have hι : RealSubspace.valLI (RealSubspace.imCLM (lieAlgebraInclCLM s f)) =
        imCLM ℂ s 2 (Complex.I • RealSubspace.valLI f) := by
      simp [lieAlgebraInclCLM]
    rw [hι, toZeroAtInfty_imCLM_apply, map_smul, _root_.smul_apply, smul_eq_mul,
      toZeroAtInfty_apply_eq_re_of_mem_realSubmodule hs' f.valLI_mem z]
    simp⟩

/-- The coordinate map `subOne : G_s → H^s(ℂ)` is `C^n` for every `n : ℕ∞ω` (including `ω`). -/
theorem contMDiff_subOne {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, H^{s}(ℂ)) n
      (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  refine contMDiff_iff_comp_chartPiece.2 fun u ↦ ?_
  let A : H^{s}(ℂ) →L[ℝ] H^{s}(ℂ) := (mulGaugeCLE u).toContinuousLinearMap.restrictScalars ℝ
  have hformula : subOne ∘ chartPiece hs u =
      fun f : RealSubspace ℂ s 2 ↦ A (expSubOne hs' (lieAlgebraInclCLM s f)) + subOne u := by
    ext1 f
    simp [chartPiece, subOne_mul_eq_mulGaugeCLE_add, lieAlgebraInclCLM, A, mulGaugeCLE_apply,
      mulGaugeCLM_apply]
  rw [hformula]
  have hι : ContMDiff 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, H^{s}(ℂ)) n (lieAlgebraInclCLM s) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (lieAlgebraInclCLM s)).contMDiff
  have hexp : ContMDiff 𝓘(ℝ, H^{s}(ℂ)) 𝓘(ℝ, H^{s}(ℂ)) n (expSubOne hs') :=
    (contDiff_real_expSubOne (n := n) hs').contMDiff
  have hA : ContMDiff 𝓘(ℝ, H^{s}(ℂ)) 𝓘(ℝ, H^{s}(ℂ)) n A :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) A).contMDiff
  exact (hA.comp (hexp.comp hι)).add contMDiff_const

/-- The operator-valued representation `u ↦ mulGaugeCLM u` into `H^s(ℂ) →L[ℂ] H^s(ℂ)` is `C^n`. -/
theorem contMDiff_mulGaugeCLM {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, H^{s}(ℂ) →L[ℂ] H^{s}(ℂ)) n
      (mulGaugeCLM (hs := hs)) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  let M : H^{s}(ℂ) →L[ℝ] H^{s}(ℂ) →L[ℂ] H^{s}(ℂ) := (mulCLM (E := ℂ) hs').restrictScalars ℝ
  have hM : ContMDiff 𝓘(ℝ, H^{s}(ℂ)) 𝓘(ℝ, H^{s}(ℂ) →L[ℂ] H^{s}(ℂ)) n M :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) M).contMDiff
  exact contMDiff_const.add (hM.comp contMDiff_subOne)

/-- The linear gauge action `(u, h) ↦ mulGaugeCLE u h` of `G_s` on `H^s(ℂ)` is `C^n`. -/
theorem contMDiff_mulGauge {n : ℕ∞ω} :
    ContMDiff (𝓘(ℝ, RealSubspace ℂ s 2).prod 𝓘(ℝ, H^{s}(ℂ))) 𝓘(ℝ, H^{s}(ℂ)) n
      (fun p : SobolevTopologicalGaugeGroup hs × H^{s}(ℂ) ↦ mulGaugeCLE p.1 p.2) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  have hbC := (mulCLM (E := ℂ) hs').isBoundedBilinearMap
  have hbR : IsBoundedBilinearMap ℝ (fun q : H^{s}(ℂ) × H^{s}(ℂ) ↦ mulCLM hs' q.1 q.2) :=
    { add_left := hbC.add_left
      smul_left := fun r x y ↦ by
        dsimp only
        rw [(mulCLM hs').map_smul_of_tower, _root_.smul_apply]
      add_right := hbC.add_right
      smul_right := fun r x y ↦ by
        dsimp only
        rw [(mulCLM hs' x).map_smul_of_tower]
      bound := hbC.bound }
  exact contMDiff_snd.add
    ((hbR.contDiff (n := n)).contMDiff.comp
      ((contMDiff_subOne.comp contMDiff_fst).prodMk_space contMDiff_snd))

/-- For `1 ≤ n`, `subOne : G_s → H^s(ℂ)` is a `C^n` immersion with fixed complement. -/
theorem isImmersion_subOne {n : ℕ∞ω} (hn : 1 ≤ n) :
    Manifold.IsImmersion 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, H^{s}(ℂ)) n
      (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  have himm₀ : Manifold.IsImmersion 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, H^{s}(ℂ)) n
      (lieAlgebraInclCLM s) :=
    (hasLeftInverse_lieAlgebraInclCLM hs).isImmersion
  -- `expSubOne` has derivative `id` at `0`, so `subOne ∘ exp hs = expSubOne ∘ (i • ·)` immerses.
  have hexp_ld : IsLocalDiffeomorphAt 𝓘(ℝ, H^{s}(ℂ)) 𝓘(ℝ, H^{s}(ℂ)) n (expSubOne hs') 0 :=
    TauCeti.isLocalDiffeomorphAt_of_fderiv_eq (contDiff_real_expSubOne (n := n) hs').contDiffOn
      isOpen_univ (Set.mem_univ 0) hn (e := ContinuousLinearEquiv.refl ℝ H^{s}(ℂ))
      ((hasStrictFDerivAt_expSubOne_zero hs').restrictScalars ℝ).hasFDerivAt.fderiv.symm
  have h₁ : Manifold.IsImmersionAtOfComplement himm₀.complement
      𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, H^{s}(ℂ)) n (subOne ∘ exp hs) 0 := by
    have hcomp : expSubOne hs' ∘ lieAlgebraInclCLM s = subOne ∘ exp hs :=
      funext fun f ↦ by simp [lieAlgebraInclCLM]
    rw [← hcomp]
    have hι0 : lieAlgebraInclCLM s 0 = 0 := map_zero (lieAlgebraInclCLM s)
    exact TauCeti.isImmersionAtOfComplement_isLocalDiffeomorphAt_comp
      (hι0.symm ▸ hexp_ld) (himm₀.isImmersionOfComplement_complement 0)
  -- Postcompose with the affine diffeomorphism `h ↦ mulGaugeCLE u h + subOne u` at each `u`.
  refine Manifold.IsImmersionOfComplement.isImmersion (F := himm₀.complement) fun u ↦ ?_
  let aff : H^{s}(ℂ) → H^{s}(ℂ) := fun h ↦ mulGaugeCLE u h + subOne u
  let L : H^{s}(ℂ) ≃L[ℝ] H^{s}(ℂ) := (mulGaugeCLE u).restrictScalars ℝ
  have haff_ld : IsLocalDiffeomorphAt 𝓘(ℝ, H^{s}(ℂ)) 𝓘(ℝ, H^{s}(ℂ)) n aff 0 :=
    TauCeti.isLocalDiffeomorphAt_of_fderiv_eq
      ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) L.toContinuousLinearMap).add
        contDiff_const).contDiffOn isOpen_univ (Set.mem_univ 0) hn (e := L)
      ((L.toContinuousLinearMap.hasFDerivAt).add_const (subOne u)).fderiv.symm
  have h₂ : Manifold.IsImmersionAtOfComplement himm₀.complement
      𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, H^{s}(ℂ)) n (subOne ∘ chartPiece hs u) 0 := by
    have hcomp : aff ∘ (subOne ∘ exp hs) = subOne ∘ chartPiece hs u :=
      funext fun f ↦ (subOne_mul_eq_mulGaugeCLE_add u (exp hs f)).symm
    rw [← hcomp]
    have hexp0 : (subOne ∘ exp hs) 0 = 0 := by simp
    exact TauCeti.isImmersionAtOfComplement_isLocalDiffeomorphAt_comp (hexp0.symm ▸ haff_ld) h₁
  have hcp0 := (TauCeti.isImmersionAtOfComplement_comp_isLocalDiffeomorphAt_iff
    (isLocalDiffeomorph_chartPiece u 0)).1 h₂
  rwa [chartPiece_zero] at hcp0

/-- **`subOne : G_s → H^s(ℂ)` is a `C^n` smooth closed embedding** for every `1 ≤ n`. -/
theorem isSmoothEmbedding_subOne {n : ℕ∞ω} (hn : 1 ≤ n) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, RealSubspace ℂ s 2) 𝓘(ℝ, H^{s}(ℂ)) n
      (subOne : SobolevTopologicalGaugeGroup hs → H^{s}(ℂ)) :=
  ⟨isImmersion_subOne hn, isEmbedding_subOne⟩

/-- For `1 ≤ n`, a map `g : M → G_s` is `C^n` if and only if `subOne ∘ g : M → H^s(ℂ)` is `C^n`. -/
theorem contMDiff_iff_subOne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} (hn : 1 ≤ n)
    {g : M → SobolevTopologicalGaugeGroup hs} :
    ContMDiff I 𝓘(ℝ, RealSubspace ℂ s 2) n g ↔ ContMDiff I 𝓘(ℝ, H^{s}(ℂ)) n (subOne ∘ g) := by
  rw [ContMDiff.iff_comp_isImmersion (isImmersion_subOne hn)]
  exact ⟨And.right, fun h ↦ ⟨continuous_iff_subOne.2 h.continuous, h⟩⟩

/-- **Monotonicity of the Sobolev gauge groups**, bundled as a group homomorphism `G_{s₂} →* G_{s₁}`
for `1 < s₁ ≤ s₂`. -/
def inclusionHom {s₁ s₂ : ℝ} (hs₁ : 1 < s₁) (h : s₁ ≤ s₂) :
    SobolevTopologicalGaugeGroup (hs₁.trans_le h) →* SobolevTopologicalGaugeGroup hs₁ :=
  (toSubgroup hs₁).symm.toMonoidHom.comp
    ((Subgroup.inclusion (sobolevGaugeGroup_mono hs₁ h)).comp
      (toSubgroup (hs₁.trans_le h)).toMonoidHom)

@[simp]
theorem toSubgroup_inclusionHom_apply {s₁ s₂ : ℝ} (hs₁ : 1 < s₁) (h : s₁ ≤ s₂)
    (u : SobolevTopologicalGaugeGroup (hs₁.trans_le h)) (z : ℂ) :
    (toSubgroup hs₁ (inclusionHom hs₁ h u) : ℂ → Circle) z =
      (toSubgroup (hs₁.trans_le h) u : ℂ → Circle) z := by
  simp [inclusionHom]

@[simp]
theorem subOne_inclusionHom {s₁ s₂ : ℝ} (hs₁ : 1 < s₁) (h : s₁ ≤ s₂)
    (u : SobolevTopologicalGaugeGroup (hs₁.trans_le h)) :
    subOne (inclusionHom hs₁ h u) = inclusion h (subOne u) := by
  apply toZeroAtInfty_injective (finrank_real_complex_lt_two_mul hs₁)
  ext z
  simp

@[simp]
theorem inclusionHom_exp {s₁ s₂ : ℝ} (hs₁ : 1 < s₁) (h : s₁ ≤ s₂)
    (f : RealSubspace ℂ s₂ 2) :
    inclusionHom hs₁ h (exp (hs₁.trans_le h) f) = exp hs₁ (RealSubspace.inclusion h f) := by
  apply subOne_injective
  rw [subOne_inclusionHom, subOne_exp, subOne_exp,
    inclusion_expSubOne (finrank_real_complex_lt_two_mul hs₁)
      (finrank_real_complex_lt_two_mul (hs₁.trans_le h)) h,
    map_smul, RealSubspace.valLI_inclusion_apply]

/-- The Sobolev order inclusion `G_{s₂} →* G_{s₁}` (`1 < s₁ ≤ s₂`) is `C^n` for every `n : ℕ∞ω`. -/
theorem contMDiff_inclusionHom {s₁ s₂ : ℝ} (hs₁ : 1 < s₁) (h : s₁ ≤ s₂) {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, RealSubspace ℂ s₂ 2) 𝓘(ℝ, RealSubspace ℂ s₁ 2) n (inclusionHom hs₁ h) := by
  refine contMDiff_iff_comp_chartPiece.2 fun u ↦ ?_
  have hcomp : inclusionHom hs₁ h ∘ chartPiece (hs₁.trans_le h) u =
      chartPiece hs₁ (inclusionHom hs₁ h u) ∘ RealSubspace.inclusion h := by
    ext1 f
    simp [chartPiece]
  rw [hcomp]
  exact (contMDiff_chartPiece _).comp
    ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (RealSubspace.inclusion h)).contMDiff)

end TauCeti.Vortex.SobolevTopologicalGaugeGroup
