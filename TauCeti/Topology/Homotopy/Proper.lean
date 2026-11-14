/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Topology.Maps.Proper.Basic

/-!
# Proper homotopy equivalences

A continuous map `f : X → Y` is a *proper homotopy equivalence*
(`ContinuousMap.HasProperHomotopyInverse`) if it is proper and has a proper homotopy inverse
`g : Y → X` for which both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` are proper as maps
`I × X → X` and `I × Y → Y`. These are the equivalences of the proper homotopy category, in which
invariants at infinity such as simple connectivity at infinity and the set of ends live.

Joint properness on the cylinder is preserved by constant homotopies, reversal, concatenation, and
horizontal composition (`ContinuousMap.Homotopy.isProperMap_refl`,
`ContinuousMap.Homotopy.isProperMap_symm`, `ContinuousMap.Homotopy.isProperMap_trans`,
`ContinuousMap.Homotopy.isProperMap_comp`), and forces every time slice — in particular both
endpoints — to be proper (`ContinuousMap.Homotopy.isProperMap_eval`). Consequently proper homotopy
equivalences contain all homeomorphisms (`Homeomorph.hasProperHomotopyInverse`), are closed under
composition (`ContinuousMap.HasProperHomotopyInverse.comp`), and are invariant under jointly proper
homotopy (`ContinuousMap.HasProperHomotopyInverse.iff_of_homotopy`), while the inclusion of a
point into a noncompact space is never a proper homotopy equivalence even when the space is
contractible (`TauCeti.not_hasProperHomotopyInverse_subtypeVal_singleton`).

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23.
-/

public section

open Set
open scoped unitInterval

namespace ContinuousMap

section Homotopy

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Homotopy

/-- Every time slice `x ↦ H (t, x)` of a jointly proper homotopy is proper. -/
theorem isProperMap_eval {f₀ f₁ : C(X, Y)} {H : Homotopy f₀ f₁} (hH : IsProperMap H) (t : I) :
    IsProperMap (fun x ↦ H (t, x)) :=
  hH.comp (isProperMap_prodMk_left t)

/-- The initial map of a jointly proper homotopy is proper. -/
theorem isProperMap_left {f₀ f₁ : C(X, Y)} {H : Homotopy f₀ f₁} (hH : IsProperMap H) :
    IsProperMap f₀ := by
  simpa only [Function.comp_def, H.apply_zero] using isProperMap_eval hH 0

/-- The terminal map of a jointly proper homotopy is proper. -/
theorem isProperMap_right {f₀ f₁ : C(X, Y)} {H : Homotopy f₀ f₁} (hH : IsProperMap H) :
    IsProperMap f₁ := by
  simpa only [Function.comp_def, H.apply_one] using isProperMap_eval hH 1

/-- The constant homotopy of a proper map is jointly proper, because `I` is compact. -/
theorem isProperMap_refl {f : C(X, Y)} (hf : IsProperMap f) : IsProperMap (Homotopy.refl f) :=
  hf.comp isProperMap_snd_of_compactSpace

@[simp]
theorem isProperMap_refl_iff {f : C(X, Y)} : IsProperMap (Homotopy.refl f) ↔ IsProperMap f :=
  ⟨isProperMap_left, isProperMap_refl⟩

/-- Reversing a jointly proper homotopy preserves properness. -/
theorem isProperMap_symm {f₀ f₁ : C(X, Y)} {H : Homotopy f₀ f₁} (hH : IsProperMap H) :
    IsProperMap H.symm :=
  hH.comp (unitInterval.continuous_symm.isProperMap.prodMap isProperMap_id)

@[simp]
theorem isProperMap_symm_iff {f₀ f₁ : C(X, Y)} {H : Homotopy f₀ f₁} :
    IsProperMap H.symm ↔ IsProperMap H :=
  ⟨fun h ↦ by simpa only [symm_symm] using isProperMap_symm h, isProperMap_symm⟩

@[simp]
theorem isProperMap_cast_iff {f₀ f₁ g₀ g₁ : C(X, Y)} (H : Homotopy f₀ f₁)
    (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) : IsProperMap (H.cast h₀ h₁) ↔ IsProperMap H :=
  (Iff.rfl)

/-- Concatenating two jointly proper homotopies gives a jointly proper homotopy: the two halves of
the cylinder form a binary closed cover, and on each half the time coordinate is rescaled by a
proper map between compact Hausdorff intervals. -/
theorem isProperMap_trans {f₀ f₁ f₂ : C(X, Y)} {F : Homotopy f₀ f₁} {G : Homotopy f₁ f₂}
    (hF : IsProperMap F) (hG : IsProperMap G) : IsProperMap (F.trans G) := by
  let I₀ : Set I := {t | (t : ℝ) ≤ 1 / 2}
  let I₁ : Set I := {t | 1 / 2 ≤ (t : ℝ)}
  have hI₀ : IsClosed I₀ := isClosed_le continuous_subtype_val continuous_const
  have hI₁ : IsClosed I₁ := isClosed_le continuous_const continuous_subtype_val
  have : CompactSpace I₀ := isCompact_iff_compactSpace.1 hI₀.isCompact
  have : CompactSpace I₁ := isCompact_iff_compactSpace.1 hI₁.isCompact
  let S : Set (I × X) := Prod.fst ⁻¹' I₀
  let T : Set (I × X) := Prod.fst ⁻¹' I₁
  have hST : S ∪ T = univ := by
    ext p
    simpa only [S, T, I₀, I₁, mem_union, mem_preimage, mem_ofPred_eq, mem_univ, iff_true] using
      le_total (p.1 : ℝ) (1 / 2)
  refine IsProperMap.of_domRestrict_of_isClosed_union (hI₀.preimage continuous_fst)
    (hI₁.preimage continuous_fst) hST ?_ ?_
  · let α₀ : I₀ → I := fun t ↦ ⟨2 * (t : ℝ),
      (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.1.2.1, t.2⟩⟩
    have hα₀ : IsProperMap α₀ := (Continuous.subtype_mk (by fun_prop) _).isProperMap
    let e₀ : S ≃ₜ I₀ × X :=
      { toFun := fun p ↦ (⟨p.1.1, p.2⟩, p.1.2)
        invFun := fun q ↦ ⟨(q.1.1, q.2), q.1.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have heq : S.domRestrict (F.trans G) = F ∘ Prod.map α₀ id ∘ e₀ := by
      ext p
      have hp : (p.1.1 : ℝ) ≤ 1 / 2 := p.2
      simp only [domRestrict_apply, Function.comp_apply, trans_apply, hp, ↓reduceDIte]
      rfl
    rw [heq]
    exact hF.comp ((hα₀.prodMap isProperMap_id).comp e₀.isProperMap)
  · let α₁ : I₁ → I := fun t ↦ ⟨2 * (t : ℝ) - 1,
      unitInterval.two_mul_sub_one_mem_iff.2 ⟨t.2, t.1.2.2⟩⟩
    have hα₁ : IsProperMap α₁ := (Continuous.subtype_mk (by fun_prop) _).isProperMap
    let e₁ : T ≃ₜ I₁ × X :=
      { toFun := fun p ↦ (⟨p.1.1, p.2⟩, p.1.2)
        invFun := fun q ↦ ⟨(q.1.1, q.2), q.1.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have heq : T.domRestrict (F.trans G) = G ∘ Prod.map α₁ id ∘ e₁ := by
      ext p
      have hp : 1 / 2 ≤ (p.1.1 : ℝ) := p.2
      simp only [domRestrict_apply, Function.comp_apply, trans_apply]
      split_ifs with hle
      · have hhalf : (p.1.1 : ℝ) = 1 / 2 := le_antisymm hle hp
        have h1 : (⟨2 * (p.1.1 : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨p.1.1.2.1, hle⟩⟩ : I) = 1 := by ext; norm_num [hhalf]
        have h0 : α₁ ⟨p.1.1, hp⟩ = 0 := by ext; norm_num [α₁, hhalf]
        exact (congrArg (fun t ↦ F (t, p.1.2)) h1).trans
          ((F.apply_one p.1.2).trans ((G.apply_zero p.1.2).symm.trans
            (congrArg (fun t ↦ G (t, p.1.2)) h0.symm)))
      · rfl
    rw [heq]
    exact hG.comp ((hα₁.prodMap isProperMap_id).comp e₁.isProperMap)

/-- A concatenation of homotopies is jointly proper if and only if both factors are jointly
proper. -/
@[simp]
theorem isProperMap_trans_iff {f₀ f₁ f₂ : C(X, Y)} {F : Homotopy f₀ f₁} {G : Homotopy f₁ f₂} :
    IsProperMap (F.trans G) ↔ IsProperMap F ∧ IsProperMap G := by
  refine ⟨fun hFG ↦ ⟨?_, ?_⟩, fun ⟨hF, hG⟩ ↦ isProperMap_trans hF hG⟩
  · let β₀ : I → I := fun t ↦ ⟨(t : ℝ) / 2, by linarith [t.2.1], by linarith [t.2.2]⟩
    have hβ₀ : IsProperMap β₀ := (Continuous.subtype_mk (by fun_prop) _).isProperMap
    have heq : (F : I × X → Y) = (F.trans G) ∘ Prod.map β₀ id := funext fun ⟨t, x⟩ ↦ by
      have ht : ((β₀ t : I) : ℝ) ≤ 1 / 2 := by dsimp [β₀]; linarith [t.2.2]
      simp only [Function.comp_apply, Prod.map_apply, id_eq, trans_apply, ht, ↓reduceDIte]
      congr 2
      ext
      dsimp [β₀]
      ring
    rw [heq]
    exact hFG.comp (hβ₀.prodMap isProperMap_id)
  · let β₁ : I → I := fun t ↦ ⟨((t : ℝ) + 1) / 2, by linarith [t.2.1], by linarith [t.2.2]⟩
    have hβ₁ : IsProperMap β₁ := (Continuous.subtype_mk (by fun_prop) _).isProperMap
    have heq : (G : I × X → Y) = (F.trans G) ∘ Prod.map β₁ id := funext fun ⟨t, x⟩ ↦ by
      simp only [Function.comp_apply, Prod.map_apply, id_eq, trans_apply]
      split_ifs with ht
      · have ht' : ((t : ℝ) + 1) / 2 ≤ 1 / 2 := ht
        have ht0 : (t : ℝ) = 0 := by linarith [t.2.1]
        have ht0' : t = 0 := Subtype.ext ht0
        have h1 : (⟨2 * (β₁ t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨(β₁ t).2.1, ht⟩⟩ : I) = 1 := by ext; simp [β₁, ht0]
        rw [h1, ht0', G.apply_zero, F.apply_one]
      · congr 2
        ext
        dsimp [β₁]
        ring
    rw [heq]
    exact hFG.comp (hβ₁.prodMap isProperMap_id)

/-- Horizontal composition `(t, x) ↦ G (t, F (t, x))` of jointly proper homotopies is jointly
proper: the diagonal of the compact Hausdorff interval `I` is proper, so the track
`(t, x) ↦ (t, F (t, x))` is proper. -/
theorem isProperMap_comp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} {G : Homotopy g₀ g₁}
    {F : Homotopy f₀ f₁} (hG : IsProperMap G) (hF : IsProperMap F) :
    IsProperMap (G.comp F) := by
  have hdiag : IsProperMap (fun t : I ↦ (t, t)) := (continuous_id.prodMk continuous_id).isProperMap
  have htrack : IsProperMap (fun p : I × X ↦ (p.1, F p)) :=
    (isProperMap_id.prodMap hF).comp
      ((Homeomorph.prodAssoc I I X).isProperMap.comp (hdiag.prodMap isProperMap_id))
  exact hG.comp htrack

/-- Precomposing a jointly proper homotopy with a proper map preserves properness. -/
theorem isProperMap_compContinuousMap {g₀ g₁ : C(Y, Z)} {G : Homotopy g₀ g₁} (hG : IsProperMap G)
    {f : C(X, Y)} (hf : IsProperMap f) : IsProperMap (G.compContinuousMap f) :=
  isProperMap_comp hG (isProperMap_refl hf)

end Homotopy

namespace HomotopyRel

@[simp]
theorem isProperMap_symm_iff {f₀ f₁ : C(X, Y)} {S : Set X} {H : HomotopyRel f₀ f₁ S} :
    IsProperMap H.symm ↔ IsProperMap H :=
  Homotopy.isProperMap_symm_iff (H := H.toHomotopy)

theorem isProperMap_trans {f₀ f₁ f₂ : C(X, Y)} {S : Set X} {F : HomotopyRel f₀ f₁ S}
    {G : HomotopyRel f₁ f₂ S} (hF : IsProperMap F) (hG : IsProperMap G) :
    IsProperMap (F.trans G) :=
  Homotopy.isProperMap_trans (F := F.toHomotopy) (G := G.toHomotopy) hF hG

@[simp]
theorem isProperMap_trans_iff {f₀ f₁ f₂ : C(X, Y)} {S : Set X} {F : HomotopyRel f₀ f₁ S}
    {G : HomotopyRel f₁ f₂ S} :
    IsProperMap (F.trans G) ↔ IsProperMap F ∧ IsProperMap G :=
  Homotopy.isProperMap_trans_iff (F := F.toHomotopy) (G := G.toHomotopy)

end HomotopyRel

end Homotopy

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A continuous map `f : X → Y` is a **proper homotopy equivalence** if it is proper and has a
proper homotopy inverse `g`, with both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` proper as maps
`I × X → X` and `I × Y → Y`. -/
def HasProperHomotopyInverse (f : C(X, Y)) : Prop :=
  IsProperMap f ∧ ∃ g : C(Y, X), IsProperMap g ∧
    ∃ H : Homotopy (g.comp f) (ContinuousMap.id X), ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y),
      IsProperMap H ∧ IsProperMap H'

namespace HasProperHomotopyInverse

/-- A proper map with a proper inverse `g` up to proper homotopies `g ∘ f ≃ id` and
`f ∘ g ≃ id` is a proper homotopy equivalence. -/
theorem intro {f : C(X, Y)} (hf : IsProperMap f) (g : C(Y, X)) (hg : IsProperMap g)
    (H : Homotopy (g.comp f) (ContinuousMap.id X)) (H' : Homotopy (f.comp g) (ContinuousMap.id Y))
    (hH : IsProperMap H) (hH' : IsProperMap H') : f.HasProperHomotopyInverse :=
  ⟨hf, g, hg, H, H', hH, hH'⟩

/-- A proper homotopy equivalence is a proper map. -/
theorem isProperMap {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) : IsProperMap f :=
  hf.1

/-- A proper homotopy equivalence has a proper homotopy inverse `g`, with proper homotopies
`g ∘ f ≃ id` and `f ∘ g ≃ id`. -/
theorem exists_inverse {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ g : C(Y, X), IsProperMap g ∧
      ∃ H : Homotopy (g.comp f) (ContinuousMap.id X),
        ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y), IsProperMap H ∧ IsProperMap H' :=
  hf.2

/-- A proper homotopy equivalence `f` is a homotopy equivalence: forgetting properness gives a
homotopy equivalence whose forward map is `f`. -/
theorem exists_homotopyEquiv {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ e : X ≃ₕ Y, (e : X → Y) = f := by
  obtain ⟨g, -, H, H', -, -⟩ := hf.exists_inverse
  exact ⟨⟨f, g, ⟨H⟩, ⟨H'⟩⟩, rfl⟩

/-- Any proper homotopy inverse witnessing `ContinuousMap.HasProperHomotopyInverse` is itself a
proper homotopy equivalence. -/
theorem of_inverse {f : C(X, Y)} {g : C(Y, X)} (hf : IsProperMap f) (hg : IsProperMap g)
    (H : Homotopy (g.comp f) (ContinuousMap.id X)) (H' : Homotopy (f.comp g) (ContinuousMap.id Y))
    (hH : IsProperMap H) (hH' : IsProperMap H') : g.HasProperHomotopyInverse :=
  .intro hg f hf H' H hH' hH

/-- The identity map of a topological space is a proper homotopy equivalence. -/
protected theorem id : (ContinuousMap.id X).HasProperHomotopyInverse :=
  .intro isProperMap_id (ContinuousMap.id X) isProperMap_id
    (Homotopy.refl _) (Homotopy.refl _)
    (Homotopy.isProperMap_refl isProperMap_id) (Homotopy.isProperMap_refl isProperMap_id)

/-- Proper homotopy equivalences are closed under composition. -/
theorem comp {g : C(Y, Z)} {f : C(X, Y)} (hg : g.HasProperHomotopyInverse)
    (hf : f.HasProperHomotopyInverse) : (g.comp f).HasProperHomotopyInverse := by
  obtain ⟨f', hf', Hf, Hf', hHf, hHf'⟩ := hf.exists_inverse
  obtain ⟨g', hg', Hg, Hg', hHg, hHg'⟩ := hg.exists_inverse
  let L₁ : Homotopy ((f'.comp g').comp (g.comp f)) (f'.comp f) :=
    ((Homotopy.refl f').comp (Hg.compContinuousMap f)).cast
      (ContinuousMap.ext fun _ ↦ rfl) (ContinuousMap.ext fun _ ↦ rfl)
  let R₁ : Homotopy ((g.comp f).comp (f'.comp g')) (g.comp g') :=
    ((Homotopy.refl g).comp (Hf'.compContinuousMap g')).cast
      (ContinuousMap.ext fun _ ↦ rfl) (ContinuousMap.ext fun _ ↦ rfl)
  have hL₁ : IsProperMap L₁ :=
    Homotopy.isProperMap_comp (Homotopy.isProperMap_refl hf')
      (Homotopy.isProperMap_compContinuousMap hHg hf.1)
  have hR₁ : IsProperMap R₁ :=
    Homotopy.isProperMap_comp (Homotopy.isProperMap_refl hg.1)
      (Homotopy.isProperMap_compContinuousMap hHf' hg')
  exact .intro (hg.1.comp hf.1) (f'.comp g') (hf'.comp hg')
    (L₁.trans Hf) (R₁.trans Hg')
    (Homotopy.isProperMap_trans hL₁ hHf) (Homotopy.isProperMap_trans hR₁ hHg')

/-- **Proper homotopy transport.** A map linked by a jointly proper homotopy to a proper homotopy
equivalence is itself a proper homotopy equivalence, with the same proper inverse. -/
theorem of_homotopy {f₀ f₁ : C(X, Y)} (hf₀ : f₀.HasProperHomotopyInverse)
    (H : Homotopy f₀ f₁) (hH : IsProperMap H) : f₁.HasProperHomotopyInverse := by
  obtain ⟨g, hg, K, K', hK, hK'⟩ := hf₀.exists_inverse
  exact .intro (Homotopy.isProperMap_right hH) g hg
    (((Homotopy.refl g).comp H.symm).trans K)
    ((H.symm.compContinuousMap g).trans K')
    (Homotopy.isProperMap_trans (Homotopy.isProperMap_comp (Homotopy.isProperMap_refl hg)
      (Homotopy.isProperMap_symm hH)) hK)
    (Homotopy.isProperMap_trans (Homotopy.isProperMap_compContinuousMap
      (Homotopy.isProperMap_symm hH) hg) hK')

/-- Two maps linked by a jointly proper homotopy are proper homotopy equivalences simultaneously. -/
theorem iff_of_homotopy {f₀ f₁ : C(X, Y)} (H : Homotopy f₀ f₁) (hH : IsProperMap H) :
    f₀.HasProperHomotopyInverse ↔ f₁.HasProperHomotopyInverse :=
  ⟨fun h ↦ h.of_homotopy H hH, fun h ↦ h.of_homotopy H.symm (Homotopy.isProperMap_symm hH)⟩

end HasProperHomotopyInverse

end ContinuousMap

/-- A homeomorphism is a proper homotopy equivalence, with constant homotopies: these are the
projections `I × X → X` and `I × Y → Y`, which are proper as `I` is compact. -/
theorem Homeomorph.hasProperHomotopyInverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : (e : C(X, Y)).HasProperHomotopyInverse := by
  refine .intro e.isProperMap e.symm e.symm.isProperMap
    ((ContinuousMap.Homotopy.refl _).cast rfl e.symm_comp_toContinuousMap)
    ((ContinuousMap.Homotopy.refl _).cast rfl e.toContinuousMap_comp_symm) ?_ ?_ <;>
  · convert isProperMap_snd_of_compactSpace (X := I) using 1
    ext x
    simp

namespace TauCeti

/-- The inclusion of a point into a noncompact space (such as `ℝ`) is never a proper homotopy
equivalence, even when the ambient space is contractible: any proper map from `X` into a singleton
would pull back that compact singleton to `X` itself. -/
theorem not_hasProperHomotopyInverse_subtypeVal_singleton {X : Type*} [TopologicalSpace X]
    [NoncompactSpace X] (x₀ : X) :
    ¬ (ContinuousMap.subtypeVal ({x₀} : Set X)).HasProperHomotopyInverse := by
  intro h
  obtain ⟨g, hg, -⟩ := h.exists_inverse
  exact not_compactSpace_iff.2 ‹NoncompactSpace X› hg.compactSpace

end TauCeti
