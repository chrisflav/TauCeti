/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
import TauCeti.Analysis.Fredholm.CompactPerturbation
import TauCeti.LinearAlgebra.Ray
import TauCeti.Topology.MetricSpace.Lebesgue

/-!
# Homotopy and compact-perturbation invariance of determinant-line orientation transport

Orientation transport along a continuous path of Fredholm operators
(`TauCeti.detLineOrientationTransport`) is invariant under endpoint-fixing homotopies through
Fredholm operators. Because the determinant line bundle over the space of Fredholm operators is a
genuine locally trivial real line bundle (`TauCeti.Analysis.Fredholm.DeterminantLine.Bundle`), its
associated orientation double cover has locally constant transition signs; parallel transport in a
cover with locally constant transitions depends only on the endpoint-relative homotopy class of a
path. Rather than passing through the covering-space formalism, this file proves homotopy invariance
directly from coherent families (`TauCeti.IsDetLineCoherentOn`), matching the chart-level
construction of `TauCeti.Analysis.Fredholm.DeterminantLine.Transport`.

The argument has three stages:

1. **Gluing coherent families on closed sets.** Coherence at a point `x₀` only tests the ray of the
   chart reading near `x₀`, not the norm of the representative. Two coherent families `v₁` on `s₁`
   and `v₂` on `s₂` over closed sets that lie on the same ray along `s₁ ∩ s₂` therefore glue
   directly via `fun x ↦ if x ∈ s₁ then v₁ x else v₂ x`, with no continuous rescaling
   (`TauCeti.IsDetLineCoherentOn.ite`). When `s₁ ∩ s₂` is preconnected, any coherent family on `s₂`
   can be rescaled by a single nonzero constant when `s₁ ∩ s₂` is nonempty (or glued directly when
   `s₁ ∩ s₂` is empty) so that uniqueness (`TauCeti.IsDetLineCoherentOn.sameRay`) aligns its rays
   across all of `s₁ ∩ s₂` (`TauCeti.exists_isDetLineCoherentOn_union`).
2. **Coherent families on rectangles.** Over a compact rectangle `R = [p, q] × [c, d]`, a Lebesgue
   number `δ > 0` (`TauCeti.lebesgue_number_lemma_of_metric_of_mem_nhds`) puts every `δ`-ball of
   `R` inside a single kernel chart, where a constant chart reading defines a coherent family
   (`TauCeti.exists_isDetLineCoherentOn_of_isInvertible`). Connectedness induction along `[c, d]`
   glues `δ`-squares into thin vertical strips `[m, M] × [c, d]` of width `M - m < δ`, and a second
   connectedness induction along `[p, q]` glues those strips across `R`
   (`TauCeti.exists_isDetLineCoherentOn_Icc_prod_Icc`).
3. **Boundary transport and homotopy invariance.** Restricting a coherent family on
   `[[s₀, s₁]] × [[a, b]]` to the four edges identifies the two composites around the boundary of
   the rectangle (`TauCeti.detLineOrientationTransport_prod`). When the top and bottom edges are
   constant in `s`, their transports reduce to `LinearMap.detLineCongrOfEq`, giving
   endpoint-relative homotopy invariance (`TauCeti.detLineOrientationTransport_homotopy`,
   `TauCeti.detLineOrientationTransport_of_homotopy`), trivial holonomy of null-homotopic Fredholm
   loops (`TauCeti.detLineOrientationTransport_loop_of_homotopy`), and invariance under families of
   compact perturbations fixing the endpoints
   (`TauCeti.detLineOrientationTransport_of_isCompactOperator_sub`).

## Main results

* `TauCeti.isDetLineCoherentOn_of_detLineChartEquiv_eq`,
  `TauCeti.exists_isDetLineCoherentOn_of_isInvertible`: a single kernel chart valid on `s` carries
  a coherent family with constant chart reading.
* `TauCeti.IsDetLineCoherentOn.ite`, `TauCeti.exists_isDetLineCoherentOn_union`: gluing of coherent
  families on closed sets, and continuation across a preconnected closed overlap.
* `TauCeti.exists_isDetLineCoherentOn_Icc_prod_Icc`: existence of coherent families on compact
  rectangles `[p, q] × [c, d]` with a prescribed nonzero value at a basepoint.
* `TauCeti.detLineOrientationTransport_prod`: transporting around the bottom and right edges of a
  Fredholm rectangle agrees with transporting around the left and top edges.
* `TauCeti.detLineOrientationTransport_homotopy`,
  `TauCeti.detLineOrientationTransport_of_homotopy`: endpoint-relative homotopy invariance of
  determinant-line orientation transport.
* `TauCeti.detLineOrientationTransport_loop_of_homotopy`: a Fredholm loop homotopic rel endpoints
  to the constant loop acts trivially on orientations.
* `TauCeti.detLineOrientationTransport_of_isCompactOperator_sub`: two continuous Fredholm paths with
  the same endpoints whose difference is compact at every parameter induce the same orientation
  transport.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix A.2 (determinant line bundles and orientations).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
* F. Bourgeois, A. Mohnke, *Coherent orientations in symplectic field theory*, Math. Z. 248 (2004),
  123–146 (orientation transport and homotopy invariance for Fredholm families).
-/

public section

open Filter Set Topology ContinuousLinearMap TensorProduct Module

namespace TauCeti

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

section Gluing

/-- **Coherence in a single kernel chart.** On any set `s` where a kernel chart `(S, G, q)` is
valid, a family read by the chart as a fixed nonzero vector `w₀` at every point of `s` is coherent
on `s`. -/
theorem isDetLineCoherentOn_of_detLineChartEquiv_eq {T : X → E →L[ℝ] F}
    {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s : Set X}
    {S : Submodule ℝ F} [FiniteDimensional ℝ S] {G : Submodule ℝ (E × S)}
    [FiniteDimensional ℝ G] {q : E × S →L[ℝ] G}
    (hq : ∀ x ∈ s, (((T x).coprod S.subtypeL).prod q).IsInvertible)
    {w₀ : TauCeti.detLine ℝ G ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ S)} (hw₀ : w₀ ≠ 0)
    (hv : ∀ x (hx : x ∈ s), detLineChartEquiv (T x) S.subtypeL q (hq x hx) (v x) = w₀) :
    IsDetLineCoherentOn T v s := by
  rw [isDetLineCoherentOn_iff]
  intro x₀ hx₀
  rw [isDetLineCoherentWithinAt_iff]
  refine ⟨fun h0 ↦ hw₀ (by rw [← hv x₀ hx₀, h0, LinearEquiv.map_zero]), S, inferInstance, G,
    inferInstance, q, hq x₀ hx₀, eventually_of_mem self_mem_nhdsWithin fun x hx ↦ ⟨hq x hx, ?_⟩⟩
  rw [hv x hx, hv x₀ hx₀]

/-- On any set `s` where a single kernel chart `(S, G, q)` is valid, there exists a coherent family
on `s`. -/
theorem exists_isDetLineCoherentOn_of_isInvertible {T : X → E →L[ℝ] F} {s : Set X}
    {S : Submodule ℝ F} [FiniteDimensional ℝ S] {G : Submodule ℝ (E × S)}
    [FiniteDimensional ℝ G] {q : E × S →L[ℝ] G}
    (hq : ∀ x ∈ s, (((T x).coprod S.subtypeL).prod q).IsInvertible) :
    ∃ v : ∀ x, (T x : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn T v s := by
  classical
  have hfin : finrank ℝ (TauCeti.detLine ℝ G ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ S)) = 1 := by
    rw [finrank_tensorProduct, Subspace.dual_finrank_eq, TauCeti.finrank_detLine,
      TauCeti.finrank_detLine]
  have : Nontrivial (TauCeti.detLine ℝ G ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ S)) :=
    Module.nontrivial_of_finrank_eq_succ hfin
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : TauCeti.detLine ℝ G ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ S))
  refine ⟨fun x ↦ if h : (((T x).coprod S.subtypeL).prod q).IsInvertible then
      (detLineChartEquiv (T x) S.subtypeL q h).symm w₀ else 0,
    isDetLineCoherentOn_of_detLineChartEquiv_eq hq hw₀ fun x hx ↦ ?_⟩
  rw [dite_eq_left (hq x hx), LinearEquiv.apply_symm_apply]

variable [CompleteSpace E]

/-- **Gluing coherent families on closed sets.** If `v₁` is coherent on the closed set `s₁`, `v₂`
is coherent on the closed set `s₂`, `T` is continuous on `s₂`, and `v₁` and `v₂` lie on the same
ray on `s₁ ∩ s₂`, then the family equal to `v₁` on `s₁` and `v₂` outside `s₁` is coherent on
`s₁ ∪ s₂`. No continuous rescaling of `v₂` is needed on `s₁ ∩ s₂`. -/
theorem IsDetLineCoherentOn.ite {T : X → E →L[ℝ] F} {v₁ v₂ : ∀ x, (T x : E →ₗ[ℝ] F).detLine}
    {s₁ s₂ : Set X} [DecidablePred (· ∈ s₁)] (hs₁ : IsClosed s₁) (hs₂ : IsClosed s₂)
    (hT₂ : ContinuousOn T s₂) (hv₁ : IsDetLineCoherentOn T v₁ s₁)
    (hv₂ : IsDetLineCoherentOn T v₂ s₂) (hsr : ∀ x ∈ s₁ ∩ s₂, SameRay ℝ (v₁ x) (v₂ x)) :
    IsDetLineCoherentOn T (fun x ↦ if x ∈ s₁ then v₁ x else v₂ x) (s₁ ∪ s₂) := by
  rw [isDetLineCoherentOn_iff]
  intro x₀ hx₀
  by_cases hx₀₁ : x₀ ∈ s₁
  · by_cases hx₀₂ : x₀ ∈ s₂
    · -- On `s₁ ∩ s₂`, split `𝓝[s₁ ∪ s₂] x₀ = 𝓝[s₁] x₀ ⊔ 𝓝[s₂ \ s₁] x₀`.
      obtain ⟨hv₁₀, S, hS, G, hG, q, h₀, hev₁⟩ :=
        isDetLineCoherentWithinAt_iff.1 (isDetLineCoherentOn_iff.1 hv₁ x₀ hx₀₁)
      have hev₂ := (isDetLineCoherentOn_iff.1 hv₂ x₀ hx₀₂).eventually_sameRay (hT₂ x₀ hx₀₂) h₀
      have hchart₂₀ : detLineChartEquiv (T x₀) S.subtypeL q h₀ (v₂ x₀) ≠ 0 :=
        (LinearEquiv.map_ne_zero_iff _).2 (hv₂.ne_zero hx₀₂)
      have hsr₀ : SameRay ℝ (detLineChartEquiv (T x₀) S.subtypeL q h₀ (v₂ x₀))
          (detLineChartEquiv (T x₀) S.subtypeL q h₀ (v₁ x₀)) :=
        (hsr x₀ ⟨hx₀₁, hx₀₂⟩).symm.map (detLineChartEquiv (T x₀) S.subtypeL q h₀).toLinearMap
      rw [isDetLineCoherentWithinAt_iff]
      refine ⟨by simpa only [ite_eq_left hx₀₁] using hv₁₀, S, hS, G, hG, q, h₀, ?_⟩
      rw [← union_sdiff_self (s := s₁) (t := s₂), nhdsWithin_union, eventually_sup]
      refine ⟨?_, ?_⟩
      · filter_upwards [hev₁, self_mem_nhdsWithin] with x ⟨h, hx⟩ hxs₁
        exact ⟨h, by simpa only [ite_eq_left hxs₁, ite_eq_left hx₀₁] using hx⟩
      · filter_upwards [nhdsWithin_mono x₀ sdiff_subset hev₂, self_mem_nhdsWithin]
          with x ⟨h, hx⟩ hxdiff
        exact ⟨h, by simpa only [ite_eq_right hxdiff.2, ite_eq_left hx₀₁] using
          hx.trans_of_ne_zero hsr₀ hchart₂₀⟩
    · -- On `s₁ \ s₂`, `s₂ᶜ` is a neighbourhood of `x₀`, so `s₁ ∪ s₂` agrees with `s₁` near `x₀`.
      have hmem : s₁ ∈ 𝓝[s₁ ∪ s₂] x₀ := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hs₂.isOpen_compl.mem_nhds hx₀₂)]
          with x hx hx₂ using hx.resolve_right hx₂
      exact ((isDetLineCoherentOn_iff.1 hv₁ x₀ hx₀₁).mono_of_mem_nhdsWithin hmem).congr
        (eventually_of_mem hmem fun x hx ↦ (ite_eq_left hx).symm) (ite_eq_left hx₀₁).symm
  · -- On `s₂ \ s₁`, `s₁ᶜ` is a neighbourhood of `x₀`, so `s₁ ∪ s₂` agrees with `s₂` near `x₀`.
    have hx₀₂ : x₀ ∈ s₂ := hx₀.resolve_left hx₀₁
    have hmem₁ : s₁ᶜ ∈ 𝓝[s₁ ∪ s₂] x₀ := nhdsWithin_le_nhds (hs₁.isOpen_compl.mem_nhds hx₀₁)
    have hmem₂ : s₂ ∈ 𝓝[s₁ ∪ s₂] x₀ := by
      filter_upwards [self_mem_nhdsWithin, hmem₁] with x hx hx₁ using hx.resolve_left hx₁
    exact ((isDetLineCoherentOn_iff.1 hv₂ x₀ hx₀₂).mono_of_mem_nhdsWithin hmem₂).congr
      (eventually_of_mem hmem₁ fun x hx ↦ (ite_eq_right hx).symm) (ite_eq_right hx₀₁).symm

/-- **Continuation of a coherent family across a closed preconnected overlap.** If `v₁` is coherent
on the closed set `s₁`, `s₂` is closed and carries some coherent family, `T` is continuous on `s₂`,
and `s₁ ∩ s₂` is preconnected, then `v₁` extends to a coherent family on `s₁ ∪ s₂`. -/
theorem exists_isDetLineCoherentOn_union {T : X → E →L[ℝ] F}
    {v₁ v₂ : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s₁ s₂ : Set X}
    (hs₁ : IsClosed s₁) (hs₂ : IsClosed s₂) (hT₂ : ContinuousOn T s₂)
    (hconn : IsPreconnected (s₁ ∩ s₂))
    (hv₁ : IsDetLineCoherentOn T v₁ s₁) (hv₂ : IsDetLineCoherentOn T v₂ s₂) :
    ∃ w : ∀ x, (T x : E →ₗ[ℝ] F).detLine,
      (∀ x ∈ s₁, w x = v₁ x) ∧ IsDetLineCoherentOn T w (s₁ ∪ s₂) := by
  classical
  rcases (s₁ ∩ s₂).eq_empty_or_nonempty with hemp | ⟨x₀, hx₀⟩
  · exact ⟨fun x ↦ if x ∈ s₁ then v₁ x else v₂ x, fun x hx ↦ ite_eq_left hx,
      hv₁.ite hs₁ hs₂ hT₂ hv₂ fun x hx ↦ False.elim (hemp.subset hx)⟩
  obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_ne_zero' (v₂ x₀) (hv₂.ne_zero hx₀.2)).1
    (LinearMap.finrank_detLine _) (v₁ x₀)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hv₁.ne_zero hx₀.1 (by rw [← hr, zero_smul])
  have hv₂' : IsDetLineCoherentOn T (fun x ↦ r • v₂ x) s₂ := hv₂.smul hr0
  refine ⟨fun x ↦ if x ∈ s₁ then v₁ x else r • v₂ x, fun x hx ↦ ite_eq_left hx,
    hv₁.ite hs₁ hs₂ hT₂ hv₂' fun x hx ↦ ?_⟩
  exact (hv₁.mono inter_subset_left).sameRay (hT₂.mono inter_subset_right) hconn
    (hv₂'.mono inter_subset_right) hx₀ hx (by rw [hr])

end Gluing

section Rectangle

variable [CompleteSpace E] {H : ℝ × ℝ → E →L[ℝ] F}

/-- On a vertical strip `[m, M] × [c, d]` narrower than `δ` in which every `δ`-ball carries a
coherent family, connectedness induction in the second coordinate constructs a coherent family on
the whole strip. -/
private theorem exists_isDetLineCoherentOn_strip {m M c d δ : ℝ} (hmM : m ≤ M) (hcd : c ≤ d)
    (hδ : 0 < δ) (hmδ : M - m < δ) (hH : ContinuousOn H (Icc m M ×ˢ Icc c d))
    (hball : ∀ x ∈ Icc m M, ∀ y ∈ Icc c d, ∃ v : ∀ z, (H z : E →ₗ[ℝ] F).detLine,
      IsDetLineCoherentOn H v ((Icc m M ×ˢ Icc c d) ∩ Metric.ball (x, y) δ)) :
    ∃ v : ∀ z, (H z : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn H v (Icc m M ×ˢ Icc c d) := by
  have hsmall {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc c d) (ht₂ : t₂ ∈ Icc c d) (htδ : t₂ - t₁ < δ) :
      ∃ v : ∀ z, (H z : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn H v (Icc m M ×ˢ Icc t₁ t₂) := by
    obtain ⟨v, hv⟩ := hball m (left_mem_Icc.2 hmM) t₁ ht₁
    refine ⟨v, hv.mono fun z hz ↦ ⟨⟨hz.1, Icc_subset_Icc ht₁.1 ht₂.2 hz.2⟩, ?_⟩⟩
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.2 hz.1.1), abs_of_nonneg (sub_nonneg.2 hz.2.1)]
    exact ⟨(sub_le_sub_right hz.1.2 m).trans_lt hmδ, (sub_le_sub_right hz.2.2 t₁).trans_lt htδ⟩
  let Q : ℝ → Prop := fun t ↦
    ∃ v : ∀ z, (H z : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn H v (Icc m M ×ˢ Icc c t)
  have hstep {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc c d) (ht₂ : t₂ ∈ Icc c d) (ht : t₁ ≤ t₂)
      (htδ : t₂ - t₁ < δ) : Q t₁ ↔ Q t₂ := by
    refine ⟨fun ⟨v₁, hv₁⟩ ↦ ?_,
      fun ⟨v, hv⟩ ↦ ⟨v, hv.mono (prod_mono_right (Icc_subset_Icc_right ht))⟩⟩
    obtain ⟨v₂, hv₂⟩ := hsmall ht₁ ht₂ htδ
    have hunion : (Icc m M ×ˢ Icc c t₁) ∪ (Icc m M ×ˢ Icc t₁ t₂) = Icc m M ×ˢ Icc c t₂ := by
      rw [← prod_union, Icc_union_Icc_eq_Icc ht₁.1 ht]
    have hinter : (Icc m M ×ˢ Icc c t₁) ∩ (Icc m M ×ˢ Icc t₁ t₂) = Icc m M ×ˢ {t₁} := by
      rw [prod_inter_prod, inter_self, Icc_inter_Icc_eq_singleton ht₁.1 ht]
    obtain ⟨w, -, hw⟩ := exists_isDetLineCoherentOn_union (isClosed_Icc.prod isClosed_Icc)
      (isClosed_Icc.prod isClosed_Icc) (hH.mono (prod_mono_right (Icc_subset_Icc ht₁.1 ht₂.2)))
      (hinter ▸ isPreconnected_Icc.prod isPreconnected_singleton) hv₁ hv₂
    exact ⟨w, hunion ▸ hw⟩
  have hQ (t : ℝ) (ht : t ∈ Icc c d) : ∀ᶠ y in 𝓝[Icc c d] t, (Q t ↔ Q y) ∧ (Q y ↔ Q t) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)]
      with y hy hyx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyx
    rcases le_total t y with hty | hyt
    · have := hstep ht hy hty hyx.2
      exact ⟨this, this.symm⟩
    · have := hstep hy ht hyt (by linarith [hyx.1])
      exact ⟨this.symm, this⟩
  have hQc : Q c := hsmall (left_mem_Icc.2 hcd) (left_mem_Icc.2 hcd) (by simpa using hδ)
  exact (isPreconnected_Icc.induction₂' (fun x y ↦ Q x ↔ Q y) hQ
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd)).1 hQc

variable [CompleteSpace F]

/-- Existence of an unnormalized coherent family on a nonempty compact rectangle `[p, q] × [c, d]`,
obtained by gluing thin vertical strips across `[p, q]`. -/
private theorem exists_isDetLineCoherentOn_rect {p q c d : ℝ} (hpq : p ≤ q) (hcd : c ≤ d)
    (hH : ContinuousOn H (Icc p q ×ˢ Icc c d))
    (hF : ∀ z ∈ Icc p q ×ˢ Icc c d, IsFredholm (H z)) :
    ∃ v : ∀ z, (H z : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn H v (Icc p q ×ˢ Icc c d) := by
  set R := Icc p q ×ˢ Icc c d
  have hcov (z : R) : ∃ V ∈ 𝓝 (z : ℝ × ℝ),
      ∃ v : ∀ w, (H w : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn H v (V ∩ R) := by
    obtain ⟨S, hS, G, hG, q', U, hU, hzU, hinv⟩ := (hF z z.2).exists_isOpen_kernelChart
    obtain ⟨V, hV, hVR⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1
      ((hH z z.2).preimage_mem_nhdsWithin (hU.mem_nhds hzU))
    exact ⟨V, hV, exists_isDetLineCoherentOn_of_isInvertible fun w hw ↦ hinv _ (hVR hw)⟩
  choose V hV vloc hvloc using hcov
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric_of_mem_nhds
    (isCompact_Icc.prod isCompact_Icc) (c := V) fun z hz ↦ ⟨⟨z, hz⟩, hV ⟨z, hz⟩⟩
  have hstrip {m M : ℝ} (hm : m ∈ Icc p q) (hM : M ∈ Icc p q) (hmM : m ≤ M) (hmδ : M - m < δ) :
      ∃ v : ∀ z, (H z : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn H v (Icc m M ×ˢ Icc c d) := by
    refine exists_isDetLineCoherentOn_strip hmM hcd hδ hmδ
      (hH.mono (prod_mono_left (Icc_subset_Icc hm.1 hM.2))) fun x hx y hy ↦ ?_
    obtain ⟨i, hi⟩ := hleb (x, y) ⟨Icc_subset_Icc hm.1 hM.2 hx, hy⟩
    exact ⟨vloc i, (hvloc i).mono fun z hz ↦
      ⟨hi hz.2, Icc_subset_Icc hm.1 hM.2 hz.1.1, hz.1.2⟩⟩
  let P : ℝ → Prop := fun s ↦
    ∃ v : ∀ z, (H z : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn H v (Icc p s ×ˢ Icc c d)
  have hstep {m M : ℝ} (hm : m ∈ Icc p q) (hM : M ∈ Icc p q) (hmM : m ≤ M) (hmδ : M - m < δ) :
      P m ↔ P M := by
    refine ⟨fun ⟨v₁, hv₁⟩ ↦ ?_,
      fun ⟨v, hv⟩ ↦ ⟨v, hv.mono (prod_mono_left (Icc_subset_Icc_right hmM))⟩⟩
    obtain ⟨v₂, hv₂⟩ := hstrip hm hM hmM hmδ
    have hunion : (Icc p m ×ˢ Icc c d) ∪ (Icc m M ×ˢ Icc c d) = Icc p M ×ˢ Icc c d := by
      rw [← union_prod, Icc_union_Icc_eq_Icc hm.1 hmM]
    have hinter : (Icc p m ×ˢ Icc c d) ∩ (Icc m M ×ˢ Icc c d) = {m} ×ˢ Icc c d := by
      rw [prod_inter_prod, inter_self, Icc_inter_Icc_eq_singleton hm.1 hmM]
    obtain ⟨w, -, hw⟩ := exists_isDetLineCoherentOn_union (isClosed_Icc.prod isClosed_Icc)
      (isClosed_Icc.prod isClosed_Icc) (hH.mono (prod_mono_left (Icc_subset_Icc hm.1 hM.2)))
      (hinter ▸ isPreconnected_singleton.prod isPreconnected_Icc) hv₁ hv₂
    exact ⟨w, hunion ▸ hw⟩
  have hP (s : ℝ) (hs : s ∈ Icc p q) : ∀ᶠ y in 𝓝[Icc p q] s, (P s ↔ P y) ∧ (P y ↔ P s) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds s hδ)]
      with y hy hyx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyx
    rcases le_total s y with hsy | hys
    · have := hstep hs hy hsy hyx.2
      exact ⟨this, this.symm⟩
    · have := hstep hy hs hys (by linarith [hyx.1])
      exact ⟨this.symm, this⟩
  have hPp : P p := hstrip (left_mem_Icc.2 hpq) (left_mem_Icc.2 hpq) le_rfl (by simpa using hδ)
  exact (isPreconnected_Icc.induction₂' (fun x y ↦ P x ↔ P y) hP
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) (left_mem_Icc.2 hpq) (right_mem_Icc.2 hpq)).1 hPp

/-- **Existence of coherent families on a rectangle.** For a family `H : ℝ × ℝ → E →L[ℝ] F` of
operators continuous and Fredholm on `[p, q] × [c, d]`, every nonzero element of the determinant
line at any point `z₀` extends to a family coherent on `[p, q] × [c, d]`. -/
theorem exists_isDetLineCoherentOn_Icc_prod_Icc {p q c d : ℝ}
    (hH : ContinuousOn H (Icc p q ×ˢ Icc c d))
    (hF : ∀ z ∈ Icc p q ×ˢ Icc c d, IsFredholm (H z)) {z₀ : ℝ × ℝ}
    {v₀ : (H z₀ : E →ₗ[ℝ] F).detLine} (hv₀ : v₀ ≠ 0) :
    ∃ v : ∀ z, (H z : E →ₗ[ℝ] F).detLine,
      v z₀ = v₀ ∧ IsDetLineCoherentOn H v (Icc p q ×ˢ Icc c d) := by
  classical
  set R := Icc p q ×ˢ Icc c d
  by_cases hR : p ≤ q ∧ c ≤ d
  · obtain ⟨w, hw⟩ := exists_isDetLineCoherentOn_rect hR.1 hR.2 hH hF
    by_cases hz₀ : z₀ ∈ R
    · obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_ne_zero' (w z₀) (hw.ne_zero hz₀)).1
        (LinearMap.finrank_detLine _) v₀
      have hr0 : r ≠ 0 := by rintro rfl; exact hv₀ (by rw [← hr, zero_smul])
      exact ⟨fun z ↦ r • w z, hr, hw.smul hr0⟩
    · refine ⟨fun z ↦ if h : z = z₀ then
          LinearMap.detLineCongrOfEq (congrArg (fun x ↦ (H x : E →ₗ[ℝ] F)) h.symm) v₀ else w z,
        by simp, hw.congr fun z hz ↦ by simp [show z ≠ z₀ by rintro rfl; exact hz₀ hz]⟩
  · refine ⟨fun z ↦ if h : z = z₀ then
        LinearMap.detLineCongrOfEq (congrArg (fun x ↦ (H x : E →ₗ[ℝ] F)) h.symm) v₀ else 0,
      by simp, by rw [isDetLineCoherentOn_iff]; exact fun z hz ↦
        False.elim (hR ⟨hz.1.1.trans hz.1.2, hz.2.1.trans hz.2.2⟩)⟩

end Rectangle

section Homotopy

variable [CompleteSpace E] [CompleteSpace F]

/-- **Rectangle boundary transport.** For a family `H : ℝ × ℝ → E →L[ℝ] F` continuous and Fredholm
on `[[s₀, s₁]] × [[a, b]]`, transporting an orientation along `s ↦ H (s, a)` from `s₀` to `s₁` and
then along `t ↦ H (s₁, t)` from `a` to `b` agrees with transporting it along `t ↦ H (s₀, t)` from
`a` to `b` and then along `s ↦ H (s, b)` from `s₀` to `s₁`. -/
theorem detLineOrientationTransport_prod {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ z ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H z))
    (hHa : ContinuousOn (fun s ↦ H (s, a)) (uIcc s₀ s₁))
    (hFa : ∀ s ∈ uIcc s₀ s₁, IsFredholm (H (s, a)))
    (hHb : ContinuousOn (fun s ↦ H (s, b)) (uIcc s₀ s₁))
    (hFb : ∀ s ∈ uIcc s₀ s₁, IsFredholm (H (s, b)))
    (hHs₀ : ContinuousOn (fun t ↦ H (s₀, t)) (uIcc a b))
    (hFs₀ : ∀ t ∈ uIcc a b, IsFredholm (H (s₀, t)))
    (hHs₁ : ContinuousOn (fun t ↦ H (s₁, t)) (uIcc a b))
    (hFs₁ : ∀ t ∈ uIcc a b, IsFredholm (H (s₁, t)))
    (o : Module.Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b hHs₁ hFs₁
        (detLineOrientationTransport (T := fun s ↦ H (s, a)) s₀ s₁ hHa hFa o) =
      detLineOrientationTransport (T := fun s ↦ H (s, b)) s₀ s₁ hHb hFb
        (detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b hHs₀ hFs₀ o) := by
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc_prod_Icc hH hF hv₀
  have hv_bot : IsDetLineCoherentOn (fun s ↦ H (s, a)) (fun s ↦ v (s, a)) (uIcc s₀ s₁) :=
    hv.comp (f := fun s ↦ (s, a)) (by fun_prop) fun s hs ↦ ⟨hs, left_mem_uIcc⟩
  have hv_top : IsDetLineCoherentOn (fun s ↦ H (s, b)) (fun s ↦ v (s, b)) (uIcc s₀ s₁) :=
    hv.comp (f := fun s ↦ (s, b)) (by fun_prop) fun s hs ↦ ⟨hs, right_mem_uIcc⟩
  have hv_left : IsDetLineCoherentOn (fun t ↦ H (s₀, t)) (fun t ↦ v (s₀, t)) (uIcc a b) :=
    hv.comp (f := fun t ↦ (s₀, t)) (by fun_prop) fun t ht ↦ ⟨left_mem_uIcc, ht⟩
  have hv_right : IsDetLineCoherentOn (fun t ↦ H (s₁, t)) (fun t ↦ v (s₁, t)) (uIcc a b) :=
    hv.comp (f := fun t ↦ (s₁, t)) (by fun_prop) fun t ht ↦ ⟨right_mem_uIcc, ht⟩
  rw [detLineOrientationTransport_rayOfNeZero hHa hFa hv_bot,
    detLineOrientationTransport_rayOfNeZero hHs₁ hFs₁ hv_right,
    detLineOrientationTransport_rayOfNeZero hHs₀ hFs₀ hv_left,
    detLineOrientationTransport_rayOfNeZero hHb hFb hv_top]

/-- **Endpoint-relative homotopy invariance of orientation transport.** Let `H : ℝ × ℝ → E →L[ℝ] F`
be continuous and Fredholm on `[[s₀, s₁]] × [[a, b]]`, with `H (s, a) = H (s₀, a)` and
`H (s, b) = H (s₀, b)` for every `s ∈ [[s₀, s₁]]`. Then the paths `t ↦ H (s₀, t)` and
`t ↦ H (s₁, t)` induce the same orientation transport, intertwined at the endpoints by
`LinearMap.detLineCongrOfEq`. -/
theorem detLineOrientationTransport_homotopy {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ z ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H z))
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = H (s₀, a))
    (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = H (s₀, b))
    (hHs₀ : ContinuousOn (fun t ↦ H (s₀, t)) (uIcc a b))
    (hFs₀ : ∀ t ∈ uIcc a b, IsFredholm (H (s₀, t)))
    (hHs₁ : ContinuousOn (fun t ↦ H (s₁, t)) (uIcc a b))
    (hFs₁ : ∀ t ∈ uIcc a b, IsFredholm (H (s₁, t)))
    (o : Module.Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b hHs₁ hFs₁
        (Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg ContinuousLinearMap.toLinearMap (ha s₁ right_mem_uIcc).symm)) o) =
      Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg ContinuousLinearMap.toLinearMap (hb s₁ right_mem_uIcc).symm))
        (detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b hHs₀ hFs₀ o) := by
  have hHa : ContinuousOn (fun s ↦ H (s, a)) (uIcc s₀ s₁) :=
    hH.comp (continuous_id.prodMk continuous_const).continuousOn fun s hs ↦ ⟨hs, left_mem_uIcc⟩
  have hFa (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : IsFredholm (H (s, a)) := hF (s, a) ⟨hs, left_mem_uIcc⟩
  have hHb : ContinuousOn (fun s ↦ H (s, b)) (uIcc s₀ s₁) :=
    hH.comp (continuous_id.prodMk continuous_const).continuousOn fun s hs ↦ ⟨hs, right_mem_uIcc⟩
  have hFb (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : IsFredholm (H (s, b)) := hF (s, b) ⟨hs, right_mem_uIcc⟩
  have hbot : detLineOrientationTransport (T := fun s ↦ H (s, a)) s₀ s₁ hHa hFa o =
      Module.Ray.map (LinearMap.detLineCongrOfEq
        (congrArg ContinuousLinearMap.toLinearMap (ha s₁ right_mem_uIcc).symm)) o := by
    have := detLineOrientationTransport_congr (T := fun _ ↦ H (s₀, a)) (T' := fun s ↦ H (s, a))
      (fun s hs ↦ (ha s hs).symm) continuousOn_const (fun _ _ ↦ hFa s₀ left_mem_uIcc) hHa hFa o
    simpa [Subsingleton.elim (congrArg ContinuousLinearMap.toLinearMap (ha s₀ left_mem_uIcc).symm)
      rfl] using this
  have htop (o' : Module.Ray ℝ (H (s₀, b) : E →ₗ[ℝ] F).detLine) :
      detLineOrientationTransport (T := fun s ↦ H (s, b)) s₀ s₁ hHb hFb o' =
        Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg ContinuousLinearMap.toLinearMap (hb s₁ right_mem_uIcc).symm)) o' := by
    have := detLineOrientationTransport_congr (T := fun _ ↦ H (s₀, b)) (T' := fun s ↦ H (s, b))
      (fun s hs ↦ (hb s hs).symm) continuousOn_const (fun _ _ ↦ hFb s₀ left_mem_uIcc) hHb hFb o'
    simpa [Subsingleton.elim (congrArg ContinuousLinearMap.toLinearMap (hb s₀ left_mem_uIcc).symm)
      rfl] using this
  rw [← hbot, detLineOrientationTransport_prod hH hF hHa hFa hHb hFb hHs₀ hFs₀ hHs₁ hFs₁, htop]

/-- **Homotopy invariance for two Fredholm paths.** If `T₀` and `T₁` are joined on `[[a, b]]` by a
continuous Fredholm homotopy `H` on `[[s₀, s₁]] × [[a, b]]` that is constant at `t = a` and `t = b`,
then `T₀` and `T₁` induce the same orientation transport. -/
theorem detLineOrientationTransport_of_homotopy {T₀ T₁ : ℝ → E →L[ℝ] F}
    {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hT₀ : ContinuousOn T₀ (uIcc a b)) (hF₀ : ∀ t ∈ uIcc a b, IsFredholm (T₀ t))
    (hT₁ : ContinuousOn T₁ (uIcc a b)) (hF₁ : ∀ t ∈ uIcc a b, IsFredholm (T₁ t))
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hFH : ∀ z ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H z))
    (hH₀ : ∀ t ∈ uIcc a b, H (s₀, t) = T₀ t) (hH₁ : ∀ t ∈ uIcc a b, H (s₁, t) = T₁ t)
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = T₀ a) (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = T₀ b)
    (o : Module.Ray ℝ (T₀ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := T₁) a b hT₁ hF₁
        (Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg ContinuousLinearMap.toLinearMap
          ((ha s₁ right_mem_uIcc).symm.trans (hH₁ a left_mem_uIcc)))) o) =
      Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg ContinuousLinearMap.toLinearMap
          ((hb s₁ right_mem_uIcc).symm.trans (hH₁ b right_mem_uIcc))))
        (detLineOrientationTransport (T := T₀) a b hT₀ hF₀ o) := by
  have hHs₀ : ContinuousOn (fun t ↦ H (s₀, t)) (uIcc a b) :=
    hH.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht ↦ ⟨left_mem_uIcc, ht⟩
  have hFs₀ (t : ℝ) (ht : t ∈ uIcc a b) : IsFredholm (H (s₀, t)) := hFH (s₀, t) ⟨left_mem_uIcc, ht⟩
  have hHs₁ : ContinuousOn (fun t ↦ H (s₁, t)) (uIcc a b) :=
    hH.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht ↦ ⟨right_mem_uIcc, ht⟩
  have hFs₁ (t : ℝ) (ht : t ∈ uIcc a b) : IsFredholm (H (s₁, t)) := hFH (s₁, t) ⟨right_mem_uIcc, ht⟩
  have ha' (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : H (s, a) = H (s₀, a) :=
    (ha s hs).trans (hH₀ a left_mem_uIcc).symm
  have hb' (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : H (s, b) = H (s₀, b) :=
    (hb s hs).trans (hH₀ b right_mem_uIcc).symm
  let ea₀ := LinearMap.detLineCongrOfEq
    (congrArg ContinuousLinearMap.toLinearMap (hH₀ a left_mem_uIcc).symm)
  have hc₀ := detLineOrientationTransport_congr (T := T₀) (T' := fun t ↦ H (s₀, t))
    (fun t ht ↦ (hH₀ t ht).symm) hT₀ hF₀ hHs₀ hFs₀ o
  have hc₁ := detLineOrientationTransport_congr (T := fun t ↦ H (s₁, t)) (T' := T₁)
    hH₁ hHs₁ hFs₁ hT₁ hF₁
    (Module.Ray.map (LinearMap.detLineCongrOfEq
      (congrArg ContinuousLinearMap.toLinearMap (ha' s₁ right_mem_uIcc).symm))
      (Module.Ray.map ea₀ o))
  have hhom := detLineOrientationTransport_homotopy hH hFH ha' hb' hHs₀ hFs₀ hHs₁ hFs₁
    (Module.Ray.map ea₀ o)
  rw [hhom, hc₀] at hc₁
  simpa only [← Equiv.trans_apply, ← Module.Ray.map_trans, ← LinearMap.detLineCongrOfEq_trans,
    ea₀] using hc₁

/-- **Trivial holonomy of null-homotopic Fredholm loops.** If a continuous Fredholm loop `T` on
`[[a, b]]` (`T a = T b`) is homotopic through Fredholm loops to the constant loop at `T a`, then
orientation transport along `T` from `a` to `b` is induced by `T a = T b`. -/
theorem detLineOrientationTransport_loop_of_homotopy {T : ℝ → E →L[ℝ] F}
    {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hFH : ∀ z ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H z))
    (hH₀ : ∀ t ∈ uIcc a b, H (s₀, t) = T a) (hH₁ : ∀ t ∈ uIcc a b, H (s₁, t) = T t)
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = T a) (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = T a)
    (o : Module.Ray ℝ (T a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := T) a b hT hF o =
      Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg ContinuousLinearMap.toLinearMap
          ((hb s₁ right_mem_uIcc).symm.trans (hH₁ b right_mem_uIcc)))) o := by
  have h := detLineOrientationTransport_of_homotopy (T₀ := fun _ ↦ T a) (T₁ := T)
    continuousOn_const (fun _ _ ↦ hF a left_mem_uIcc) hT hF hH hFH hH₀ hH₁ ha hb o
  have ha_eq : congrArg ContinuousLinearMap.toLinearMap
      ((ha s₁ right_mem_uIcc).symm.trans (hH₁ a left_mem_uIcc)) = rfl :=
    Subsingleton.elim _ _
  simpa [ha_eq] using h

/-- **Compact-perturbation invariance of orientation transport.** Two continuous Fredholm paths on
`[[a, b]]` with the same endpoints whose difference is compact at every parameter induce the same
orientation transport: straight-line interpolation stays in the Fredholm locus by stability of
Fredholm operators under compact perturbations
(`ContinuousLinearMap.IsFredholm.add_of_isCompactOperator`). -/
theorem detLineOrientationTransport_of_isCompactOperator_sub {T₀ T₁ : ℝ → E →L[ℝ] F} {a b : ℝ}
    (hT₀ : ContinuousOn T₀ (uIcc a b)) (hF₀ : ∀ t ∈ uIcc a b, IsFredholm (T₀ t))
    (hT₁ : ContinuousOn T₁ (uIcc a b)) (hF₁ : ∀ t ∈ uIcc a b, IsFredholm (T₁ t))
    (hK : ∀ t ∈ uIcc a b, IsCompactOperator (T₁ t - T₀ t))
    (ha : T₀ a = T₁ a) (hb : T₀ b = T₁ b)
    (o : Module.Ray ℝ (T₀ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := T₁) a b hT₁ hF₁
        (Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg ContinuousLinearMap.toLinearMap ha)) o) =
      Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg ContinuousLinearMap.toLinearMap hb))
        (detLineOrientationTransport (T := T₀) a b hT₀ hF₀ o) := by
  let H : ℝ × ℝ → E →L[ℝ] F := fun p ↦ T₀ p.2 + p.1 • (T₁ p.2 - T₀ p.2)
  have hsnd : MapsTo Prod.snd (uIcc (0 : ℝ) 1 ×ˢ uIcc a b) (uIcc a b) := fun _ hp ↦ hp.2
  have hH : ContinuousOn H (uIcc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    (hT₀.comp continuousOn_snd hsnd).add
      (continuousOn_fst.smul ((hT₁.sub hT₀).comp continuousOn_snd hsnd))
  have hFH (p : ℝ × ℝ) (hp : p ∈ uIcc (0 : ℝ) 1 ×ˢ uIcc a b) : IsFredholm (H p) :=
    (hF₀ p.2 hp.2).add_of_isCompactOperator (by simpa using (hK p.2 hp.2).smul p.1)
  simpa using detLineOrientationTransport_of_homotopy (s₀ := 0) (s₁ := 1) hT₀ hF₀ hT₁ hF₁ hH hFH
    (fun t _ ↦ by simp [H]) (fun t _ ↦ by simp [H])
    (fun s _ ↦ by simp [H, ha]) (fun s _ ↦ by simp [H, hb]) o

end Homotopy

end TauCeti
