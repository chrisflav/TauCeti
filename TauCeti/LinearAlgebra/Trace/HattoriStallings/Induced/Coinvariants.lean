/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module

public import TauCeti.LinearAlgebra.Trace.HattoriStallings.Induced.Basic

/-!
# Coinvariant Traces of Induced Modules for Monoid Extensions

This file constructs the `Λ`-linear isomorphism
`Coinvariants Λ G (InducedModule Λ S Q) ≃ₗ[Λ] (Fin S.index → Coinvariants Λ S.kernel Q)` and proves
Stacks Project Lemma 64.15.6 (Tag 03UA) for the degree-`n` action on `G`-coinvariants.

## Main definitions

* `TauCeti.MonoidExtension.InducedModule.coinvariantsEquiv`: the `Λ`-linear isomorphism
  `Coinvariants Λ G (InducedModule Λ S Q) ≃ₗ[Λ] (Fin S.index → Coinvariants Λ S.kernel Q)`.

## Main results

* `TauCeti.MonoidExtension.InducedModule.coinvariantsEquiv_coinvariantsAction_single`:
  under `coinvariantsEquiv`, the degree-`n` coinvariant action shifts coordinate `r` to
  `(r + n) % S.index` via the degree-`(r + n) / S.index` coinvariant action of `S.toExtension`.
* `TauCeti.MonoidExtension.hattoriStallingsTrace_coinvariantsAction_inducedModule_of_not_dvd` and
  `TauCeti.MonoidExtension.hattoriStallingsTrace_coinvariantsAction_inducedModule_mul`:
  **Stacks Lemma 64.15.6** — the Hattori–Stallings trace on `(InducedModule Λ S Q)_G` vanishes when
  `S.index ∤ n` and equals `S.index • Tr(k, Q_{S.kernel})` when `n = k * S.index`.

## References

* [Stacks Project, Lemma 64.15.6 (Tag 03UA)](https://stacks.math.columbia.edu/tag/03UA)
-/

@[expose] public section

noncomputable section

namespace TauCeti

namespace MonoidExtension

open _root_.MonoidAlgebra

variable {G Γ : Type*} [Group G] [Group Γ]

/-! ### Section 4: Coinvariants of `InducedModule Λ S Q` and Stacks Lemma 64.15.6 -/

namespace InducedModule

variable {Λ : Type*} [Ring Λ] {E : MonoidExtension G Γ} {S : E.Subextension}
variable {Q : Type*} [AddCommGroup Q] [Module Λ Q]
variable [Module (MonoidAlgebra Λ S.toExtension.monoid) Q]
variable [IsScalarTower Λ (MonoidAlgebra Λ S.toExtension.monoid) Q]

/-- Pointwise delta section `Q →ₗ[Λ] InducedModule Λ S Q` supported on the single `S.kernel`-orbit
of `baseStrip γ₁ r`. -/
def deltaSection (γ₁ : E.fiber 1) (r : Fin S.index) : Q →ₗ[Λ] InducedModule Λ S Q := by
  classical
  refine
    { toFun := fun q₀ ↦
        { toFun := fun x ↦
            if stripDeg x = r then
              if hmem : stripGroupCoord γ₁ x ∈ conjKernel (S := S) γ₁ r then
                (MonoidAlgebra.single
                    (S.toExtension.monoidIncl ((conjKernelEquiv (S := S) γ₁ r).symm ⟨_, hmem⟩)⁻¹)
                    (1 : Λ) :
                  MonoidAlgebra Λ S.toExtension.monoid) • q₀
              else 0
            else 0
          equivariant := fun x k' ↦ by
            obtain ⟨hdeg, hcoord⟩ := stripGroupCoord_stripMulKernel γ₁ x k'
            by_cases hr : stripDeg x = r
            · subst hr
              have hdeg' : stripDeg (S.stripMulKernel x k') = stripDeg x := hdeg
              simp only [hdeg', ↓reduceIte]
              have hmem_iff : stripGroupCoord γ₁ (S.stripMulKernel x k') ∈
                    conjKernel (S := S) γ₁ (stripDeg x) ↔
                  stripGroupCoord γ₁ x ∈ conjKernel (S := S) γ₁ (stripDeg x) := by
                rw [hcoord]
                exact Subgroup.mul_mem_cancel_right _ (conjKernelEquiv γ₁ (stripDeg x) k').2
              by_cases hmem : stripGroupCoord γ₁ x ∈ conjKernel (S := S) γ₁ (stripDeg x)
              · have hmem' := hmem_iff.mpr hmem
                simp only [hmem, hmem', ↓reduceDIte]
                rw [← mul_smul, single_mul_single, one_mul, ← map_mul]
                congr 3
                rw [← mul_inv_rev]
                congr 1
                apply (conjKernelEquiv (S := S) γ₁ (stripDeg x)).injective
                apply Subtype.ext
                simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
                exact hcoord
              · have hmem' : stripGroupCoord γ₁ (S.stripMulKernel x k') ∉
                    conjKernel (S := S) γ₁ (stripDeg x) := fun hc ↦ hmem (hmem_iff.mp hc)
                simp [hmem, hmem']
            · have hr' : stripDeg (S.stripMulKernel x k') ≠ r := by rwa [hdeg]
              simp [hr, hr'] }
      map_add' := fun q₁ q₂ ↦ ext fun x ↦ by
        rw [add_apply]
        dsimp only
        split_ifs <;> simp [smul_add]
      map_smul' := fun a q₀ ↦ ext fun x ↦ by
        rw [RingHom.id_apply, smul_apply]
        dsimp only
        split_ifs
        · simpa only [singleSMulEnd_apply] using
            (singleSMulEnd Λ (Γ := S.toExtension.monoid) _ Q).map_smul a q₀
        · simp
        · simp }

open Classical in
theorem deltaSection_apply_groupMulStrip_baseStrip (γ₁ : E.fiber 1) (r r' : Fin S.index)
    (g : G) (q₀ : Q) :
    deltaSection (Λ := Λ) (S := S) γ₁ r q₀ (S.groupMulStrip g (baseStrip γ₁ r')) =
      if r' = r then
        if hmem : g ∈ conjKernel (S := S) γ₁ r then
          (MonoidAlgebra.single
              (S.toExtension.monoidIncl ((conjKernelEquiv (S := S) γ₁ r).symm ⟨_, hmem⟩)⁻¹)
              (1 : Λ) :
            MonoidAlgebra Λ S.toExtension.monoid) • q₀
        else 0
      else 0 := by
  dsimp only [deltaSection, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [stripDeg_groupMulStrip_baseStrip, stripGroupCoord_groupMulStrip_baseStrip]

theorem deltaSection_smul_kernel (γ₁ : E.fiber 1) (r : Fin S.index) (k' : S.kernel) (q₀ : Q) :
    deltaSection (Λ := Λ) (S := S) γ₁ r
        ((MonoidAlgebra.single (S.toExtension.monoidIncl k') (1 : Λ) :
          MonoidAlgebra Λ S.toExtension.monoid) • q₀) =
      (MonoidAlgebra.single (conjKernelEquiv (S := S) γ₁ r k').1 (1 : Λ) : MonoidAlgebra Λ G) •
        deltaSection (Λ := Λ) (S := S) γ₁ r q₀ := by
  classical
  ext x
  set r' := stripDeg x
  set g := stripGroupCoord γ₁ x
  have hx : x = S.groupMulStrip g (baseStrip γ₁ r') := (groupMulStrip_stripGroupCoord γ₁ x).symm
  rw [hx, single_group_smul_apply, one_smul, ← Subextension.groupMulStrip_mul,
    deltaSection_apply_groupMulStrip_baseStrip, deltaSection_apply_groupMulStrip_baseStrip]
  by_cases hr : r' = r
  · subst hr
    simp only [↓reduceIte]
    have hmem_iff : g ∈ conjKernel (S := S) γ₁ r' ↔
        ((conjKernelEquiv (S := S) γ₁ r' k').1)⁻¹ * g ∈ conjKernel (S := S) γ₁ r' :=
      (Subgroup.mul_mem_cancel_left _ (inv_mem (conjKernelEquiv γ₁ r' k').2)).symm
    by_cases hmem : g ∈ conjKernel (S := S) γ₁ r'
    · have hmem' := hmem_iff.mp hmem
      simp only [hmem, hmem', ↓reduceDIte]
      rw [← mul_smul, single_mul_single, mul_one, ← map_mul]
      congr 3
      apply (conjKernelEquiv (S := S) γ₁ r').injective
      apply Subtype.ext
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    · have hmem' : ((conjKernelEquiv (S := S) γ₁ r' k').1)⁻¹ * g ∉ conjKernel (S := S) γ₁ r' :=
        fun hc ↦ hmem (hmem_iff.mpr hc)
      simp [hmem, hmem']
  · simp [hr]

/-- Every element of `InducedModule Λ S Q` decomposes as a finite sum of `G`-translates of
`deltaSection`s over `Fin S.index` and cosets `G ⧸ conjKernel γ₁ r`. -/
theorem eq_sum_single_deltaSection (γ₁ : E.fiber 1)
    [∀ r : Fin S.index, Fintype (G ⧸ conjKernel (S := S) γ₁ r)] (f : InducedModule Λ S Q) :
    f = ∑ r : Fin S.index, ∑ q : G ⧸ conjKernel (S := S) γ₁ r,
      (MonoidAlgebra.single q.out (1 : Λ) : MonoidAlgebra Λ G) •
        deltaSection (Λ := Λ) (S := S) γ₁ r (f (S.groupMulStrip q.out (baseStrip γ₁ r))) := by
  classical
  ext x
  set r₀ := stripDeg x
  set g₀ := stripGroupCoord γ₁ x
  have hx : x = S.groupMulStrip g₀ (baseStrip γ₁ r₀) := (groupMulStrip_stripGroupCoord γ₁ x).symm
  rw [sum_apply, Finset.sum_eq_single r₀]
  · rw [sum_apply]
    let q₀ : G ⧸ conjKernel (S := S) γ₁ r₀ := QuotientGroup.mk g₀
    rw [Finset.sum_eq_single q₀]
    · rw [hx, single_group_smul_apply, one_smul, ← Subextension.groupMulStrip_mul,
        deltaSection_apply_groupMulStrip_baseStrip]
      have hmem : q₀.out⁻¹ * g₀ ∈ conjKernel (S := S) γ₁ r₀ :=
        QuotientGroup.eq.mp (QuotientGroup.out_eq' q₀)
      simp only [↓reduceIte, hmem, ↓reduceDIte]
      let k₀ := (conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩
      have hg₀ : g₀ = q₀.out * (conjKernelEquiv (S := S) γ₁ r₀ k₀).1 := by
        have h1 : (conjKernelEquiv (S := S) γ₁ r₀ k₀).1 = q₀.out⁻¹ * g₀ := by
          change ((conjKernelEquiv (S := S) γ₁ r₀)
            ((conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩)).1 = _
          rw [MulEquiv.apply_symm_apply]
        rw [h1, mul_inv_cancel_left]
      conv_lhs => rw [hg₀, groupMulStrip_baseStrip_mul_conjKernel, f.equivariant]
    · intro q _ hq
      rw [hx, single_group_smul_apply, one_smul, ← Subextension.groupMulStrip_mul,
        deltaSection_apply_groupMulStrip_baseStrip]
      have hnmem : q.out⁻¹ * g₀ ∉ conjKernel (S := S) γ₁ r₀ := by
        intro hmem
        have hqeq : q = q₀ := by
          rw [← QuotientGroup.out_eq' q]
          exact QuotientGroup.eq.mpr hmem
        exact hq hqeq
      simp [hnmem]
    · intro hmem
      exact absurd (Finset.mem_univ q₀) hmem
  · intro r _ hr
    rw [sum_apply]
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    rw [hx, single_group_smul_apply, one_smul, ← Subextension.groupMulStrip_mul,
      deltaSection_apply_groupMulStrip_baseStrip]
    simp [Ne.symm hr]
  · intro hmem
    exact absurd (Finset.mem_univ r₀) hmem

/-- Canonical `Λ`-linear isomorphism
`Coinvariants Λ G (InducedModule Λ S Q) ≃ₗ[Λ] (Fin S.index → Coinvariants Λ S.kernel Q)`. -/
def coinvariantsEquiv [Finite G] (γ₁ : E.fiber 1)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q) :
    Coinvariants Λ G (InducedModule Λ S Q) ≃ₗ[Λ]
      (Fin S.index → Coinvariants Λ S.kernel Q) := by
  classical
  have : ∀ r : Fin S.index, Fintype (G ⧸ conjKernel (S := S) γ₁ r) := fun _ ↦ Fintype.ofFinite _
  let fwdRaw : InducedModule Λ S Q →ₗ[Λ] (Fin S.index → Coinvariants Λ S.kernel Q) :=
    { toFun := fun f r ↦ ∑ q : G ⧸ conjKernel (S := S) γ₁ r,
        Coinvariants.mk (Λ := Λ) (G := S.kernel) (f (S.groupMulStrip q.out (baseStrip γ₁ r)))
      map_add' := fun f g ↦ by
        funext r
        simp [map_add, Finset.sum_add_distrib]
      map_smul' := fun a f ↦ by
        funext r
        simp [Finset.smul_sum] }
  have hfwd_inv : ∀ (g : G) (f : InducedModule Λ S Q),
      fwdRaw ((MonoidAlgebra.single g (1 : Λ) : MonoidAlgebra Λ G) • f) = fwdRaw f := by
    intro g f
    funext r
    change ∑ q : G ⧸ conjKernel (S := S) γ₁ r,
        Coinvariants.mk (Λ := Λ) (G := S.kernel)
          (((MonoidAlgebra.single g (1 : Λ) : MonoidAlgebra Λ G) • f)
            (S.groupMulStrip q.out (baseStrip γ₁ r))) =
      ∑ q : G ⧸ conjKernel (S := S) γ₁ r,
        Coinvariants.mk (Λ := Λ) (G := S.kernel) (f (S.groupMulStrip q.out (baseStrip γ₁ r)))
    let eQ : (G ⧸ conjKernel (S := S) γ₁ r) ≃ (G ⧸ conjKernel (S := S) γ₁ r) :=
      MulAction.toPerm g⁻¹
    rw [Fintype.sum_equiv eQ _ _ (fun q ↦ ?_)]
    have hrel : (eQ q).out⁻¹ * (g⁻¹ * q.out) ∈ conjKernel (S := S) γ₁ r :=
      QuotientGroup.eq.mp (by
        rw [QuotientGroup.out_eq']
        exact congrArg (g⁻¹ • ·) (QuotientGroup.out_eq' q).symm)
    let k' := (conjKernelEquiv (S := S) γ₁ r).symm ⟨_, hrel⟩
    have hq : g⁻¹ * q.out = (eQ q).out * (conjKernelEquiv (S := S) γ₁ r k').1 := by
      have h1 : (conjKernelEquiv (S := S) γ₁ r k').1 = (eQ q).out⁻¹ * (g⁻¹ * q.out) := by
        change ((conjKernelEquiv (S := S) γ₁ r)
          ((conjKernelEquiv (S := S) γ₁ r).symm ⟨_, hrel⟩)).1 = _
        rw [MulEquiv.apply_symm_apply]
      rw [h1, mul_inv_cancel_left]
    rw [single_group_smul_apply, one_smul, ← Subextension.groupMulStrip_mul, hq,
      groupMulStrip_baseStrip_mul_conjKernel, f.equivariant]
    have h1 : (MonoidAlgebra.single (S.toExtension.monoidIncl k'⁻¹) (1 : Λ) :
          MonoidAlgebra Λ S.toExtension.monoid) •
          f (S.groupMulStrip (eQ q).out (baseStrip γ₁ r)) =
        (MonoidAlgebra.single k'⁻¹ (1 : Λ) : MonoidAlgebra Λ S.kernel) •
          f (S.groupMulStrip (eQ q).out (baseStrip γ₁ r)) := by
      rw [hQG', mapDomain_single]
    rw [h1, Coinvariants.mk_single_smul]
  let fwd : Coinvariants Λ G (InducedModule Λ S Q) →ₗ[Λ]
      (Fin S.index → Coinvariants Λ S.kernel Q) :=
    Coinvariants.lift (Λ := Λ) (G := G) fwdRaw hfwd_inv
  let invComp : Fin S.index →
      Coinvariants Λ S.kernel Q →ₗ[Λ] Coinvariants Λ G (InducedModule Λ S Q) := fun r ↦
    Coinvariants.lift (Λ := Λ) (G := S.kernel)
      ((Coinvariants.mk (Λ := Λ) (G := G)).comp (deltaSection γ₁ r)) fun k' q₀ ↦ by
        simp only [LinearMap.comp_apply]
        rw [hQG', mapDomain_single, deltaSection_smul_kernel, Coinvariants.mk_single_smul]
  let inv : (Fin S.index → Coinvariants Λ S.kernel Q) →ₗ[Λ]
      Coinvariants Λ G (InducedModule Λ S Q) :=
    { toFun := fun v ↦ ∑ r : Fin S.index, invComp r (v r)
      map_add' := fun v w ↦ by simp [map_add, Finset.sum_add_distrib]
      map_smul' := fun a v ↦ by simp [Finset.smul_sum] }
  refine
    { toLinearMap := fwd
      invFun := inv
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    obtain ⟨f, rfl⟩ := Coinvariants.mk_surjective (Λ := Λ) (G := G) c
    change inv (fwd (Coinvariants.mk (Λ := Λ) (G := G) f)) = Coinvariants.mk (Λ := Λ) (G := G) f
    dsimp only [fwd, inv]
    rw [Coinvariants.lift_mk]
    change ∑ r : Fin S.index, invComp r (fwdRaw f r) =
      Coinvariants.mk (Λ := Λ) (G := G) f
    conv_rhs => rw [eq_sum_single_deltaSection γ₁ f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    change invComp r (∑ q : G ⧸ conjKernel (S := S) γ₁ r,
        Coinvariants.mk (Λ := Λ) (G := S.kernel) (f (S.groupMulStrip q.out (baseStrip γ₁ r)))) = _
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    dsimp only [invComp]
    rw [Coinvariants.lift_mk, LinearMap.comp_apply, Coinvariants.mk_single_smul]
  · intro v
    funext r₀
    change fwd (∑ r : Fin S.index, invComp r (v r)) r₀ = v r₀
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single r₀]
    · obtain ⟨q₀, hq₀⟩ := Coinvariants.mk_surjective (Λ := Λ) (G := S.kernel) (v r₀)
      rw [← hq₀]
      dsimp only [fwd, invComp]
      rw [Coinvariants.lift_mk, LinearMap.comp_apply, Coinvariants.lift_mk]
      change ∑ q : G ⧸ conjKernel (S := S) γ₁ r₀,
          Coinvariants.mk (Λ := Λ) (G := S.kernel)
            (deltaSection γ₁ r₀ q₀ (S.groupMulStrip q.out (baseStrip γ₁ r₀))) = _
      let q1 : G ⧸ conjKernel (S := S) γ₁ r₀ := QuotientGroup.mk 1
      rw [Finset.sum_eq_single q1]
      · rw [deltaSection_apply_groupMulStrip_baseStrip]
        have hmem : q1.out ∈ conjKernel (S := S) γ₁ r₀ := by
          have h1 : q1.out⁻¹ * 1 ∈ conjKernel (S := S) γ₁ r₀ :=
            QuotientGroup.eq.mp (QuotientGroup.out_eq' q1)
          rw [mul_one] at h1
          simpa using inv_mem h1
        simp only [↓reduceIte, hmem, ↓reduceDIte]
        let k' := ((conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩)⁻¹
        have h1 : (MonoidAlgebra.single (S.toExtension.monoidIncl k') (1 : Λ) :
              MonoidAlgebra Λ S.toExtension.monoid) • q₀ =
            (MonoidAlgebra.single k' (1 : Λ) : MonoidAlgebra Λ S.kernel) • q₀ := by
          rw [hQG', mapDomain_single]
        rw [h1, Coinvariants.mk_single_smul]
      · intro q _ hq
        rw [deltaSection_apply_groupMulStrip_baseStrip]
        have hnmem : q.out ∉ conjKernel (S := S) γ₁ r₀ := by
          intro hmem
          have hmem' : (1 : G)⁻¹ * q.out ∈ conjKernel (S := S) γ₁ r₀ := by simpa using hmem
          have h1 : q1 = QuotientGroup.mk q.out := QuotientGroup.eq.mpr hmem'
          rw [QuotientGroup.out_eq'] at h1
          exact hq h1.symm
        simp [hnmem]
      · intro hmem
        exact absurd (Finset.mem_univ q1) hmem
    · intro r _ hr
      obtain ⟨q₀, hq₀⟩ := Coinvariants.mk_surjective (Λ := Λ) (G := S.kernel) (v r)
      rw [← hq₀]
      dsimp only [fwd, invComp]
      rw [Coinvariants.lift_mk, LinearMap.comp_apply, Coinvariants.lift_mk]
      change ∑ q : G ⧸ conjKernel (S := S) γ₁ r₀,
          Coinvariants.mk (Λ := Λ) (G := S.kernel)
            (deltaSection γ₁ r q₀ (S.groupMulStrip q.out (baseStrip γ₁ r₀))) = 0
      refine Finset.sum_eq_zero fun q _ ↦ ?_
      rw [deltaSection_apply_groupMulStrip_baseStrip]
      simp [Ne.symm hr]
    · intro hmem
      exact absurd (Finset.mem_univ r₀) hmem

theorem coinvariantsEquiv_mk [Finite G] (γ₁ : E.fiber 1)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    (f : InducedModule Λ S Q) (r : Fin S.index)
    [Fintype (G ⧸ conjKernel (S := S) γ₁ r)] :
    coinvariantsEquiv (Λ := Λ) (S := S) (Q := Q) γ₁ hQG'
        (Coinvariants.mk (Λ := Λ) (G := G) f) r =
      ∑ q : G ⧸ conjKernel (S := S) γ₁ r,
        Coinvariants.mk (Λ := Λ) (G := S.kernel) (f (S.groupMulStrip q.out (baseStrip γ₁ r))) := by
  dsimp only [coinvariantsEquiv, LinearEquiv.coe_mk]
  rw [Coinvariants.lift_mk]
  change ∑ q ∈ @Finset.univ (G ⧸ conjKernel (S := S) γ₁ r) (Fintype.ofFinite _),
      Coinvariants.mk (Λ := Λ) (G := S.kernel) (f (S.groupMulStrip q.out (baseStrip γ₁ r))) =
    ∑ q : G ⧸ conjKernel (S := S) γ₁ r,
      Coinvariants.mk (Λ := Λ) (G := S.kernel) (f (S.groupMulStrip q.out (baseStrip γ₁ r)))
  exact Finset.sum_congr (Finset.ext fun _ ↦ by simp) fun _ _ ↦ rfl

theorem coinvariantsEquiv_symm_single [Finite G] (γ₁ : E.fiber 1)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    (r : Fin S.index) (q₀ : Q) :
    (coinvariantsEquiv (Λ := Λ) (S := S) (Q := Q) γ₁ hQG').symm
        (Pi.single r (Coinvariants.mk (Λ := Λ) (G := S.kernel) q₀)) =
      Coinvariants.mk (Λ := Λ) (G := G) (deltaSection γ₁ r q₀) := by
  classical
  dsimp only [coinvariantsEquiv, LinearEquiv.symm_mk, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [Finset.sum_eq_single r]
  · simp
  · intro r' _ hr'
    simp [Pi.single_eq_of_ne hr']
  · intro hmem
    exact absurd (Finset.mem_univ r) hmem

/-- Formula for the degree-`n` coinvariant action conjugated by `coinvariantsEquiv`: it shifts
coordinate `r : Fin S.index` to `(r + n) % S.index` and acts by the degree-`(r + n) / S.index`
coinvariant action of `S.toExtension` on `Coinvariants Λ S.kernel Q`. -/
theorem coinvariantsEquiv_coinvariantsAction_single [Finite G] (γ₁ : E.fiber 1) (n : ℕ)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    (r : Fin S.index) (c : Coinvariants Λ S.kernel Q) :
    (coinvariantsEquiv (Λ := Λ) (S := S) (Q := Q) γ₁ hQG').conjRingEquiv
        (E.coinvariantsAction Λ n (InducedModule Λ S Q)
          (smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q))) (Pi.single r c) =
      Pi.single ⟨(r.1 + n) % S.index, Nat.mod_lt _ S.index_pos⟩
        (S.toExtension.coinvariantsAction Λ ((r.1 + n) / S.index) Q hQG' c) := by
  classical
  have : ∀ r' : Fin S.index, Fintype (G ⧸ conjKernel (S := S) γ₁ r') := fun _ ↦ Fintype.ofFinite _
  obtain ⟨q₀, rfl⟩ := Coinvariants.mk_surjective (Λ := Λ) (G := S.kernel) c
  let r' : Fin S.index := ⟨(r.1 + n) % S.index, Nat.mod_lt _ S.index_pos⟩
  let k : ℕ := (r.1 + n) / S.index
  have hrn : r'.1 + S.index * k = r.1 + n := by
    dsimp only [r', k]
    linarith [Nat.div_add_mod (r.1 + n) S.index]
  let γn : E.fiber n := ⟨γ₁.1 ^ n, by
    rw [SubmonoidClass.coe_pow, E.degree_pow, γ₁.2, Nat.cast_one, mul_one]⟩
  obtain ⟨γ'k⟩ := S.toExtension.fiber_nonempty k
  have hdeg_eq : E.degree (γ₁.1.1 ^ (S.index * k)) = E.degree γ'k.1.1.1 := by
    rw [E.degree_pow, γ₁.2, Nat.cast_one, mul_one, S.degree_eq_index_mul_toExtension_degree, γ'k.2]
    push_cast
    ring
  obtain ⟨g₀, hg₀⟩ := E.exists_incl_mul_of_degree_eq hdeg_eq
  let g₁ : G := E.conjAut (γ₁.1.1 ^ r'.1) g₀
  have hmul_base : γn.1.1 * γ₁.1.1 ^ r.1 = (E.incl g₁ * γ₁.1.1 ^ r'.1) * γ'k.1.1.1 := by
    have hpow : γn.1.1 * γ₁.1.1 ^ r.1 = γ₁.1.1 ^ r'.1 * γ₁.1.1 ^ (S.index * k) := by
      dsimp only [γn]
      rw [SubmonoidClass.coe_pow, ← pow_add, ← pow_add, add_comm n r.1, hrn]
    rw [hpow, hg₀, ← mul_assoc]
    congr 1
    dsimp only [g₁]
    rw [E.incl_conjAut]
    group
  have hconj :
      (coinvariantsEquiv (Λ := Λ) (S := S) (Q := Q) γ₁ hQG').conjRingEquiv
          (E.coinvariantsAction Λ n (InducedModule Λ S Q)
            (smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q)))
          (Pi.single r (Coinvariants.mk (Λ := Λ) (G := S.kernel) q₀)) =
        coinvariantsEquiv (Λ := Λ) (S := S) (Q := Q) γ₁ hQG'
          (E.coinvariantsAction Λ n (InducedModule Λ S Q)
            (smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q))
            ((coinvariantsEquiv (Λ := Λ) (S := S) (Q := Q) γ₁ hQG').symm
              (Pi.single r (Coinvariants.mk (Λ := Λ) (G := S.kernel) q₀)))) := by
    simp
  rw [hconj, coinvariantsEquiv_symm_single,
    E.coinvariantsAction_mk Λ γn (InducedModule Λ S Q)
      (smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q))]
  funext r''
  rw [coinvariantsEquiv_mk]
  by_cases hrr : r'' = r'
  · subst hrr
    rw [Pi.single_eq_same, S.toExtension.coinvariantsAction_mk Λ γ'k Q hQG']
    let q₁ : G ⧸ conjKernel (S := S) γ₁ r' := QuotientGroup.mk g₁
    have hconj_mem : ∀ h : G,
        (E.conjAut γn.1.1).symm (h * g₁⁻¹) ∈ conjKernel (S := S) γ₁ r ↔
          g₁⁻¹ * h ∈ conjKernel (S := S) γ₁ r' := by
      intro h
      rw [mem_conjKernel_iff, mem_conjKernel_iff, Subextension.mem_kernel, Subextension.mem_kernel]
      have h_id : E.incl ((E.conjAut (γ₁.1.1 ^ r.1)).symm ((E.conjAut γn.1.1).symm (h * g₁⁻¹))) =
          (γ'k.1.1.1)⁻¹ *
            E.incl ((E.conjAut (γ₁.1.1 ^ r'.1)).symm (g₁⁻¹ * h)) * γ'k.1.1.1 := by
        have hsymm : ∀ (z : Γ) (u : G), E.incl ((E.conjAut z).symm u) = z⁻¹ * E.incl u * z := by
          intro z u
          have h1 := E.incl_conjAut z ((E.conjAut z).symm u)
          rw [(E.conjAut z).apply_symm_apply] at h1
          calc E.incl ((E.conjAut z).symm u)
              = z⁻¹ * (z * E.incl ((E.conjAut z).symm u) * z⁻¹) * z := by group
            _ = z⁻¹ * E.incl u * z := by rw [← h1]
        rw [hsymm, hsymm, hsymm]
        have hinv_base : (γ₁.1.1 ^ r.1)⁻¹ * (γn.1.1)⁻¹ =
            (γ'k.1.1.1)⁻¹ * (γ₁.1.1 ^ r'.1)⁻¹ * (E.incl g₁)⁻¹ := by
          calc (γ₁.1.1 ^ r.1)⁻¹ * (γn.1.1)⁻¹ = (γn.1.1 * γ₁.1.1 ^ r.1)⁻¹ := by group
            _ = ((E.incl g₁ * γ₁.1.1 ^ r'.1) * γ'k.1.1.1)⁻¹ := by rw [hmul_base]
            _ = (γ'k.1.1.1)⁻¹ * (γ₁.1.1 ^ r'.1)⁻¹ * (E.incl g₁)⁻¹ := by group
        have hstep : (γ₁.1.1 ^ r.1)⁻¹ * (γn.1.1⁻¹ * E.incl (h * g₁⁻¹) * γn.1.1) *
            γ₁.1.1 ^ r.1 =
            ((γ₁.1.1 ^ r.1)⁻¹ * γn.1.1⁻¹) * E.incl (h * g₁⁻¹) * (γn.1.1 * γ₁.1.1 ^ r.1) := by
          group
        rw [hstep, hinv_base, hmul_base]
        have h_conj : (γ'k.1.1.1)⁻¹ * (γ₁.1.1 ^ r'.1)⁻¹ * (E.incl g₁)⁻¹ * E.incl (h * g₁⁻¹) *
            (E.incl g₁ * γ₁.1.1 ^ r'.1 * γ'k.1.1.1) =
            (γ'k.1.1.1)⁻¹ * ((γ₁.1.1 ^ r'.1)⁻¹ *
              ((E.incl g₁)⁻¹ * E.incl (h * g₁⁻¹) * E.incl g₁) * γ₁.1.1 ^ r'.1) * γ'k.1.1.1 := by
          group
        rw [h_conj]
        have hg₁_comm : (E.incl g₁)⁻¹ * E.incl (h * g₁⁻¹) * E.incl g₁ = E.incl (g₁⁻¹ * h) := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          group
        rw [hg₁_comm]
      rw [h_id]
      constructor
      · intro hsub
        have h1 := mul_mem (mul_mem γ'k.1.1.2 hsub) (inv_mem γ'k.1.1.2)
        simpa [mul_assoc] using h1
      · intro hsub
        exact mul_mem (mul_mem (inv_mem γ'k.1.1.2) hsub) γ'k.1.1.2
    rw [Finset.sum_eq_single q₁]
    · let y₀ := S.groupMulStrip ((E.conjAut γn.1.1).symm (q₁.out * g₁⁻¹)) (baseStrip γ₁ r)
      have heq_q₁ : γn.1.1 * y₀.1 =
          (S.groupMulStrip q₁.out (baseStrip γ₁ r')).1 * γ'k.1.1.1 := by
        rw [Subextension.coe_groupMulStrip, Subextension.coe_groupMulStrip, coe_baseStrip,
          coe_baseStrip]
        have h1 := E.incl_conjAut γn.1.1 ((E.conjAut γn.1.1).symm (q₁.out * g₁⁻¹))
        rw [(E.conjAut γn.1.1).apply_symm_apply] at h1
        have h2 : γn.1.1 * E.incl ((E.conjAut γn.1.1).symm (q₁.out * g₁⁻¹)) =
            E.incl (q₁.out * g₁⁻¹) * γn.1.1 := by
          calc γn.1.1 * E.incl ((E.conjAut γn.1.1).symm (q₁.out * g₁⁻¹))
              = (γn.1.1 * E.incl ((E.conjAut γn.1.1).symm (q₁.out * g₁⁻¹)) * γn.1.1⁻¹) *
                  γn.1.1 := by group
            _ = E.incl (q₁.out * g₁⁻¹) * γn.1.1 := by rw [← h1]
        rw [← mul_assoc, h2, mul_assoc, hmul_base, ← mul_assoc, ← mul_assoc, ← map_mul,
          inv_mul_cancel_right]
      rw [single_smul_apply_of_eq γn.1 1 _ _ y₀ γ'k.1 heq_q₁,
        deltaSection_apply_groupMulStrip_baseStrip]
      have hmem_q₁ : g₁⁻¹ * q₁.out ∈ conjKernel (S := S) γ₁ r' :=
        QuotientGroup.eq.mp (QuotientGroup.out_eq' q₁).symm
      have hmem_y : (E.conjAut γn.1.1).symm (q₁.out * g₁⁻¹) ∈ conjKernel (S := S) γ₁ r :=
        (hconj_mem q₁.out).mpr hmem_q₁
      simp only [↓reduceIte, hmem_y, ↓reduceDIte]
      rw [← mul_smul, single_mul_single, mul_one]
      let k'' := ((conjKernelEquiv (S := S) γ₁ r).symm ⟨_, hmem_y⟩)⁻¹
      have h_eq_fib : S.toExtension.degree (γ'k.1 * S.toExtension.monoidIncl k'').1 = k := by
        rw [Submonoid.coe_mul, S.toExtension.degree_mul, S.toExtension.coe_monoidIncl,
          S.toExtension.degree_incl, add_zero, γ'k.2]
      let γ'k₂ : S.toExtension.fiber k := ⟨γ'k.1 * S.toExtension.monoidIncl k'', h_eq_fib⟩
      change Coinvariants.mk (Λ := Λ) (G := S.kernel)
          ((MonoidAlgebra.single γ'k₂.1 (1 : Λ) : MonoidAlgebra Λ S.toExtension.monoid) • q₀) = _
      rw [← S.toExtension.coinvariantsAction_mk Λ γ'k₂ Q hQG',
        S.toExtension.coinvariantsAction_mk Λ γ'k Q hQG']
    · intro q _ hq
      let y₀ := S.groupMulStrip ((E.conjAut γn.1.1).symm (q.out * g₁⁻¹)) (baseStrip γ₁ r)
      have heq_q : γn.1.1 * y₀.1 =
          (S.groupMulStrip q.out (baseStrip γ₁ r')).1 * γ'k.1.1.1 := by
        rw [Subextension.coe_groupMulStrip, Subextension.coe_groupMulStrip, coe_baseStrip,
          coe_baseStrip]
        have h1 := E.incl_conjAut γn.1.1 ((E.conjAut γn.1.1).symm (q.out * g₁⁻¹))
        rw [(E.conjAut γn.1.1).apply_symm_apply] at h1
        have h2 : γn.1.1 * E.incl ((E.conjAut γn.1.1).symm (q.out * g₁⁻¹)) =
            E.incl (q.out * g₁⁻¹) * γn.1.1 := by
          calc γn.1.1 * E.incl ((E.conjAut γn.1.1).symm (q.out * g₁⁻¹))
              = (γn.1.1 * E.incl ((E.conjAut γn.1.1).symm (q.out * g₁⁻¹)) * γn.1.1⁻¹) *
                  γn.1.1 := by group
            _ = E.incl (q.out * g₁⁻¹) * γn.1.1 := by rw [← h1]
        rw [← mul_assoc, h2, mul_assoc, hmul_base, ← mul_assoc, ← mul_assoc, ← map_mul,
          inv_mul_cancel_right]
      rw [single_smul_apply_of_eq γn.1 1 _ _ y₀ γ'k.1 heq_q,
        deltaSection_apply_groupMulStrip_baseStrip]
      have hnmem : (E.conjAut γn.1.1).symm (q.out * g₁⁻¹) ∉ conjKernel (S := S) γ₁ r := by
        intro hmem
        have hmem' : g₁⁻¹ * q.out ∈ conjKernel (S := S) γ₁ r' := (hconj_mem q.out).mp hmem
        have hqeq : q = q₁ := (QuotientGroup.out_eq' q).symm.trans (QuotientGroup.eq.mpr hmem').symm
        exact hq hqeq
      simp only [↓reduceIte, hnmem, ↓reduceDIte, smul_zero, map_zero]
    · intro hmem
      exact absurd (Finset.mem_univ q₁) hmem
  · rw [Pi.single_eq_of_ne hrr]
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    let x := S.groupMulStrip q.out (baseStrip γ₁ r'')
    obtain ⟨y, γ', heq⟩ := S.exists_strip_mul_eq γn.1 x
    rw [single_smul_apply_of_eq γn.1 1 _ x y γ' heq]
    have hne : stripDeg y ≠ r := by
      intro hdeg
      have h1 := congrArg E.degree heq
      rw [E.degree_mul, E.degree_mul] at h1
      have hy_deg : E.degree y.1 = (r : ℕ) := by rw [← stripDeg_coe y, hdeg]
      have hx_deg : E.degree x.1 = (r'' : ℕ) := by
        rw [Subextension.coe_groupMulStrip, coe_baseStrip, E.degree_mul, E.degree_incl, zero_add,
          E.degree_pow, γ₁.2, Nat.cast_one, mul_one]
      have hγn_deg : E.degree γn.1.1 = (n : ℕ) := γn.2
      obtain ⟨t, ht⟩ := S.dvd_degree γ'.1.1 γ'.1.2
      have hmod : ((r''.1 : ℤ) % (S.index : ℤ)) = ((r.1 + n : ℤ) % (S.index : ℤ)) := by
        have hsub : (r.1 + n : ℤ) = r''.1 + (S.index : ℤ) * t := by linarith
        rw [hsub, Int.add_mul_emod_self_left]
      have hmod_nat : r''.1 % S.index = (r.1 + n) % S.index := by
        have h2 : ((r''.1 % S.index : ℕ) : ℤ) = (((r.1 + n) % S.index : ℕ) : ℤ) := by
          simpa using hmod
        exact Int.ofNat.inj h2
      rw [Nat.mod_eq_of_lt r''.2] at hmod_nat
      exact hrr (Fin.ext hmod_nat)
    have hzero : deltaSection (Λ := Λ) γ₁ r q₀ y = 0 := by
      dsimp only [deltaSection, LinearMap.coe_mk, AddHom.coe_mk]
      simp [hne]
    rw [hzero, smul_zero, map_zero]

end InducedModule

section Stacks64_15_6

private theorem hattoriStallingsTrace_pi_of_single {Λ : Type*} [Ring Λ] {d : ℕ}
    {C : Type*} [AddCommGroup C] [Module Λ C] [Module.Finite Λ C] [Module.Projective Λ C]
    [Module.Projective Λ (Fin d → C)]
    (F : Module.End Λ (Fin d → C)) (σ : Fin d → Fin d) (T : Fin d → Module.End Λ C)
    (hF : ∀ (r : Fin d) (c : C), F (Pi.single r c) = Pi.single (σ r) (T r c)) :
    LinearMap.hattoriStallingsTrace Λ (Fin d → C) F =
      ∑ r : Fin d, if σ r = r then LinearMap.hattoriStallingsTrace Λ C (T r) else 0 := by
  classical
  obtain ⟨t, rC, iC, -, -, hrC⟩ := Module.Finite.exists_comp_eq_id_of_projective Λ C
  let iD : (Fin d → C) →ₗ[Λ] (Fin d × Fin t → Λ) :=
    { toFun := fun v rj ↦ iC (v rj.1) rj.2
      map_add' := fun v w ↦ by funext rj; simp
      map_smul' := fun a v ↦ by funext rj; simp }
  let rD : (Fin d × Fin t → Λ) →ₗ[Λ] (Fin d → C) :=
    { toFun := fun w r ↦ rC (fun j ↦ w (r, j))
      map_add' := fun v w ↦ by
        funext r
        exact rC.map_add (fun j ↦ v (r, j)) (fun j ↦ w (r, j))
      map_smul' := fun a v ↦ by
        funext r
        exact rC.map_smul a (fun j ↦ v (r, j)) }
  have hrD : rD ∘ₗ iD = .id := by
    apply LinearMap.ext
    intro v
    funext r
    change rC (iC (v r)) = v r
    exact LinearMap.congr_fun hrC (v r)
  rw [LinearMap.hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin d × Fin t)) iD rD hrD,
    Module.Basis.hattoriStallingsTrace_apply, Fintype.sum_prod_type, map_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hrD_single : ∀ j : Fin t,
      rD (Pi.basisFun Λ (Fin d × Fin t) (r, j)) = Pi.single r (rC (Pi.single j 1)) := by
    intro j
    funext r'
    rw [Pi.basisFun_apply]
    change rC (fun j' ↦ (Pi.single (M := fun _ ↦ Λ) (r, j) (1 : Λ)) (r', j')) =
      (Pi.single (M := fun _ ↦ C) r (rC (Pi.single j 1))) r'
    by_cases hrr' : r' = r
    · subst hrr'
      rw [Pi.single_eq_same]
      congr 1
      funext j'
      by_cases hjj' : j' = j <;> simp [hjj']
    · rw [Pi.single_eq_of_ne hrr']
      have hzero : (fun j' : Fin t ↦ (Pi.single (r, j) (1 : Λ) : Fin d × Fin t → Λ) (r', j')) =
          0 := by
        funext j'
        have hne : (r', j') ≠ (r, j) := fun h ↦ hrr' (congrArg Prod.fst h)
        simp [Pi.single_eq_of_ne hne]
      rw [hzero, map_zero]
  by_cases hfix : σ r = r
  · simp only [hfix, ↓reduceIte]
    rw [LinearMap.hattoriStallingsTrace_eq_of_retract (Pi.basisFun Λ (Fin t)) iC rC hrC,
      Module.Basis.hattoriStallingsTrace_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [LinearMap.comp_apply, Pi.basisFun_repr, hrD_single, hF, hfix]
    change iC ((Pi.single (M := fun _ ↦ C) r (T r (rC (Pi.single j 1)))) r) j =
      iC (T r (rC (Pi.basisFun Λ (Fin t) j))) j
    simp [Pi.basisFun_apply]
  · simp only [hfix, ↓reduceIte]
    rw [Finset.sum_eq_zero fun j _ ↦ ?_, map_zero]
    simp only [LinearMap.comp_apply, Pi.basisFun_repr, hrD_single, hF]
    change iC ((Pi.single (M := fun _ ↦ C) (σ r) (T r (rC (Pi.single j 1)))) r) j = 0
    rw [Pi.single_eq_of_ne (Ne.symm hfix), map_zero, Pi.zero_apply]

/-- **Stacks Lemma 64.15.6 (non-divisible degree case).** For a subextension `S : E.Subextension`
of index `d = S.index` with finite kernel `G` and a finite projective `Λ[S.kernel]`-module `Q`
with `S.toExtension.monoid`-action, if `S.index ∤ n`, then the Hattori–Stallings trace of the
degree-`n` action on `(InducedModule Λ S Q)_G` vanishes in `Λ / [Λ, Λ]`. -/
theorem hattoriStallingsTrace_coinvariantsAction_inducedModule_of_not_dvd {Λ : Type*} [Ring Λ]
    {E : MonoidExtension G Γ} [Finite G] (S : E.Subextension) {n : ℕ} (hnd : ¬ S.index ∣ n)
    (Q : Type*) [AddCommGroup Q] [Module Λ Q]
    [Module (MonoidAlgebra Λ S.toExtension.monoid) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ S.toExtension.monoid) Q]
    [Module (MonoidAlgebra Λ S.kernel) Q] [IsScalarTower Λ (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    [Module.Finite (MonoidAlgebra Λ S.kernel) Q]
    [Module.Projective (MonoidAlgebra Λ S.kernel) Q] :
    haveI := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').1
    haveI := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').2
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := InducedModule Λ S Q)).1
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := InducedModule Λ S Q)).2
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G (InducedModule Λ S Q))
        (E.coinvariantsAction Λ n (InducedModule Λ S Q)
          (InducedModule.smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q))) = 0 := by
  have := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').1
  have := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').2
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := InducedModule Λ S Q)).1
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := InducedModule Λ S Q)).2
  have := (Coinvariants.finite_projective (Λ := Λ) (G := S.kernel) (P := Q)).1
  have := (Coinvariants.finite_projective (Λ := Λ) (G := S.kernel) (P := Q)).2
  obtain ⟨γ₁⟩ := E.fiber_nonempty 1
  let e := InducedModule.coinvariantsEquiv (Λ := Λ) (S := S) (Q := Q) γ₁ hQG'
  have : Module.Projective Λ (Fin S.index → Coinvariants Λ S.kernel Q) :=
    Module.Projective.of_split e.symm.toLinearMap e.toLinearMap (by ext v; simp)
  rw [← LinearMap.hattoriStallingsTrace_conj _ e,
    hattoriStallingsTrace_pi_of_single
      (e.conjRingEquiv (E.coinvariantsAction Λ n (InducedModule Λ S Q)
        (InducedModule.smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q))))
      (fun r : Fin S.index ↦ ⟨(r.1 + n) % S.index, Nat.mod_lt _ S.index_pos⟩)
      (fun r : Fin S.index ↦ S.toExtension.coinvariantsAction Λ ((r.1 + n) / S.index) Q hQG')
      (InducedModule.coinvariantsEquiv_coinvariantsAction_single γ₁ n hQG')]
  refine Finset.sum_eq_zero fun r _ ↦ ?_
  have hne : (⟨(r.1 + n) % S.index, Nat.mod_lt _ S.index_pos⟩ : Fin S.index) ≠ r := by
    intro hEq
    have hmod : (r.1 + n) % S.index = r.1 := congrArg Fin.val hEq
    have hdiv := Nat.div_add_mod (r.1 + n) S.index
    exact hnd ⟨(r.1 + n) / S.index, by omega⟩
  simp [hne]

/-- **Stacks Lemma 64.15.6 (divisible degree case).** For a subextension `S : E.Subextension`
of index `d = S.index` with finite `G` and a finite projective `Λ[S.kernel]`-module `Q` with
`S.toExtension.monoid`-action, the Hattori–Stallings trace of the degree-`(k * S.index)` action on
`(InducedModule Λ S Q)_G` equals `S.index` times the Hattori–Stallings trace of the degree-`k`
action on `Q_{S.kernel}`, over an arbitrary (possibly noncommutative) ring `Λ`. -/
theorem hattoriStallingsTrace_coinvariantsAction_inducedModule_mul {Λ : Type*} [Ring Λ]
    {E : MonoidExtension G Γ} [Finite G] (S : E.Subextension) (k : ℕ)
    (Q : Type*) [AddCommGroup Q] [Module Λ Q]
    [Module (MonoidAlgebra Λ S.toExtension.monoid) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ S.toExtension.monoid) Q]
    [Module (MonoidAlgebra Λ S.kernel) Q] [IsScalarTower Λ (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    [Module.Finite (MonoidAlgebra Λ S.kernel) Q]
    [Module.Projective (MonoidAlgebra Λ S.kernel) Q] :
    haveI := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').1
    haveI := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').2
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := InducedModule Λ S Q)).1
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := G)
      (P := InducedModule Λ S Q)).2
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := S.kernel) (P := Q)).1
    haveI := (Coinvariants.finite_projective (Λ := Λ) (G := S.kernel) (P := Q)).2
    LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ G (InducedModule Λ S Q))
        (E.coinvariantsAction Λ (k * S.index) (InducedModule Λ S Q)
          (InducedModule.smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q))) =
      S.index • LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ S.kernel Q)
        (S.toExtension.coinvariantsAction Λ k Q hQG') := by
  have := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').1
  have := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').2
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := InducedModule Λ S Q)).1
  have := (Coinvariants.finite_projective (Λ := Λ) (G := G) (P := InducedModule Λ S Q)).2
  have := (Coinvariants.finite_projective (Λ := Λ) (G := S.kernel) (P := Q)).1
  have := (Coinvariants.finite_projective (Λ := Λ) (G := S.kernel) (P := Q)).2
  obtain ⟨γ₁⟩ := E.fiber_nonempty 1
  let e := InducedModule.coinvariantsEquiv (Λ := Λ) (S := S) (Q := Q) γ₁ hQG'
  have : Module.Projective Λ (Fin S.index → Coinvariants Λ S.kernel Q) :=
    Module.Projective.of_split e.symm.toLinearMap e.toLinearMap (by ext v; simp)
  rw [← LinearMap.hattoriStallingsTrace_conj _ e,
    hattoriStallingsTrace_pi_of_single
      (e.conjRingEquiv (E.coinvariantsAction Λ (k * S.index) (InducedModule Λ S Q)
        (InducedModule.smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q))))
      (fun r : Fin S.index ↦ ⟨(r.1 + k * S.index) % S.index, Nat.mod_lt _ S.index_pos⟩)
      (fun r : Fin S.index ↦
        S.toExtension.coinvariantsAction Λ ((r.1 + k * S.index) / S.index) Q hQG')
      (InducedModule.coinvariantsEquiv_coinvariantsAction_single γ₁ (k * S.index) hQG')]
  have hterm : ∀ r : Fin S.index,
      (if (⟨(r.1 + k * S.index) % S.index, Nat.mod_lt _ S.index_pos⟩ : Fin S.index) = r then
        LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ S.kernel Q)
          (S.toExtension.coinvariantsAction Λ ((r.1 + k * S.index) / S.index) Q hQG')
      else 0) =
      LinearMap.hattoriStallingsTrace Λ (Coinvariants Λ S.kernel Q)
        (S.toExtension.coinvariantsAction Λ k Q hQG') := by
    intro r
    have hmod : (⟨(r.1 + k * S.index) % S.index, Nat.mod_lt _ S.index_pos⟩ : Fin S.index) = r := by
      apply Fin.ext
      change (r.1 + k * S.index) % S.index = r.1
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.2]
    have hdiv : (r.1 + k * S.index) / S.index = k := by
      rw [Nat.add_mul_div_right _ _ S.index_pos, Nat.div_eq_of_lt r.2, zero_add]
    rw [hmod, hdiv]
    simp
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Commutative specialization of Stacks Lemma 64.15.6 (non-divisible degree case). -/
theorem projectiveTrace_coinvariantsAction_inducedModule_of_not_dvd {A : Type*} [CommRing A]
    {E : MonoidExtension G Γ} [Finite G] (S : E.Subextension) {n : ℕ} (hnd : ¬ S.index ∣ n)
    (Q : Type*) [AddCommGroup Q] [Module A Q]
    [Module (MonoidAlgebra A S.toExtension.monoid) Q]
    [IsScalarTower A (MonoidAlgebra A S.toExtension.monoid) Q]
    [Module (MonoidAlgebra A S.kernel) Q] [IsScalarTower A (MonoidAlgebra A S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra A S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    [Module.Finite (MonoidAlgebra A S.kernel) Q]
    [Module.Projective (MonoidAlgebra A S.kernel) Q] :
    haveI := (InducedModule.finite_projective (Λ := A) (S := S) (Q := Q) hQG').1
    haveI := (InducedModule.finite_projective (Λ := A) (S := S) (Q := Q) hQG').2
    haveI := (Coinvariants.finite_projective (Λ := A) (G := G)
      (P := InducedModule A S Q)).1
    haveI := (Coinvariants.finite_projective (Λ := A) (G := G)
      (P := InducedModule A S Q)).2
    LinearMap.projectiveTrace A (Coinvariants A G (InducedModule A S Q))
        (E.coinvariantsAction A n (InducedModule A S Q)
          (InducedModule.smul_eq_mapDomain (Λ := A) (S := S) (Q := Q))) = 0 := by
  have := (InducedModule.finite_projective (Λ := A) (S := S) (Q := Q) hQG').1
  have := (InducedModule.finite_projective (Λ := A) (S := S) (Q := Q) hQG').2
  have := (Coinvariants.finite_projective (Λ := A) (G := G) (P := InducedModule A S Q)).1
  have := (Coinvariants.finite_projective (Λ := A) (G := G) (P := InducedModule A S Q)).2
  rw [← LinearMap.cyclicQuotientEquivSelf_hattoriStallingsTrace,
    hattoriStallingsTrace_coinvariantsAction_inducedModule_of_not_dvd S hnd Q hQG', map_zero]

/-- Commutative specialization of Stacks Lemma 64.15.6 (divisible degree case). -/
theorem projectiveTrace_coinvariantsAction_inducedModule_mul {A : Type*} [CommRing A]
    {E : MonoidExtension G Γ} [Finite G] (S : E.Subextension) (k : ℕ)
    (Q : Type*) [AddCommGroup Q] [Module A Q]
    [Module (MonoidAlgebra A S.toExtension.monoid) Q]
    [IsScalarTower A (MonoidAlgebra A S.toExtension.monoid) Q]
    [Module (MonoidAlgebra A S.kernel) Q] [IsScalarTower A (MonoidAlgebra A S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra A S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    [Module.Finite (MonoidAlgebra A S.kernel) Q]
    [Module.Projective (MonoidAlgebra A S.kernel) Q] :
    haveI := (InducedModule.finite_projective (Λ := A) (S := S) (Q := Q) hQG').1
    haveI := (InducedModule.finite_projective (Λ := A) (S := S) (Q := Q) hQG').2
    haveI := (Coinvariants.finite_projective (Λ := A) (G := G)
      (P := InducedModule A S Q)).1
    haveI := (Coinvariants.finite_projective (Λ := A) (G := G)
      (P := InducedModule A S Q)).2
    haveI := (Coinvariants.finite_projective (Λ := A) (G := S.kernel) (P := Q)).1
    haveI := (Coinvariants.finite_projective (Λ := A) (G := S.kernel) (P := Q)).2
    LinearMap.projectiveTrace A (Coinvariants A G (InducedModule A S Q))
        (E.coinvariantsAction A (k * S.index) (InducedModule A S Q)
          (InducedModule.smul_eq_mapDomain (Λ := A) (S := S) (Q := Q))) =
      (S.index : A) * LinearMap.projectiveTrace A (Coinvariants A S.kernel Q)
        (S.toExtension.coinvariantsAction A k Q hQG') := by
  have := (InducedModule.finite_projective (Λ := A) (S := S) (Q := Q) hQG').1
  have := (InducedModule.finite_projective (Λ := A) (S := S) (Q := Q) hQG').2
  have := (Coinvariants.finite_projective (Λ := A) (G := G) (P := InducedModule A S Q)).1
  have := (Coinvariants.finite_projective (Λ := A) (G := G) (P := InducedModule A S Q)).2
  have := (Coinvariants.finite_projective (Λ := A) (G := S.kernel) (P := Q)).1
  have := (Coinvariants.finite_projective (Λ := A) (G := S.kernel) (P := Q)).2
  rw [← LinearMap.cyclicQuotientEquivSelf_hattoriStallingsTrace,
    hattoriStallingsTrace_coinvariantsAction_inducedModule_mul S k Q hQG', map_nsmul,
    nsmul_eq_mul, LinearMap.cyclicQuotientEquivSelf_hattoriStallingsTrace]

/-- `InducedModule ℤ S Q` has no `Module ℤ` diamond with `AddCommGroup.toIntModule`. -/
example {E : MonoidExtension G Γ} (S : E.Subextension) (Q : Type*) [AddCommGroup Q]
    [Module (MonoidAlgebra ℤ S.toExtension.monoid) Q] :
    (inferInstance : Module ℤ (InducedModule ℤ S Q)) =
      AddCommGroup.toIntModule (InducedModule ℤ S Q) :=
  rfl

end Stacks64_15_6

end MonoidExtension

end TauCeti

