/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Root operators under linear maps

The linear-image construction `TauCeti.PLPath.map` is defined in
`TauCeti.RepresentationTheory.LSPath.PLPath`, including for noninjective maps and collapsed
segments. This file proves naturality of root operators.

The operators `lower` and `raise` commute with a linear map `g` when the target coroot form
pulls back to the source form and the target root is the image of the source root. The equality
of forms preserves all running heights, so the record cuts, not just the endpoints, agree.
The same naturality holds for a semilinear map `g : V →ₛₗ[σ] W` over any strictly monotone field
homomorphism `σ : 𝕜₁ →+* 𝕜₂` (`TauCeti.PLPath.mapSemilinear`), permitting base change of the
ordered ground field (such as embedding a canonical rational realization into an arbitrary ordered
field).

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1 (paths, reparametrizations and root operators).
-/

public section

namespace TauCeti.PLPath

open Module

/-! ### Semilinear images along order-preserving field homomorphisms -/

section Semilinear

variable {𝕜₁ 𝕜₂ V W : Type*} [Field 𝕜₁] [LinearOrder 𝕜₁] [IsStrictOrderedRing 𝕜₁]
  [Field 𝕜₂] [LinearOrder 𝕜₂] [IsStrictOrderedRing 𝕜₂]
  [AddCommGroup V] [Module 𝕜₁ V] [AddCommGroup W] [Module 𝕜₂ W] {σ : 𝕜₁ →+* 𝕜₂}

/-- Taking a semilinear image over a strictly monotone field homomorphism preserves elementary
path moves, including when segments collapse. -/
theorem Move.mapSemilinear (hσ : StrictMono σ) (g : V →ₛₗ[σ] W) {l m : List V}
    (h : Move 𝕜₁ l m) : Move 𝕜₂ (l.map g) (m.map g) := by
  cases h with
  | @merge l m v w hvw =>
    have hsame : SameRay 𝕜₂ (g v) (g w) := by
      rcases hvw with rfl | rfl | ⟨r₁, r₂, hr₁, hr₂, hr⟩
      · exact (map_zero g).symm ▸ SameRay.zero_left _
      · exact (map_zero g).symm ▸ SameRay.zero_right _
      · refine Or.inr (Or.inr ⟨σ r₁, σ r₂, ?_, ?_, ?_⟩)
        · simpa only [map_zero] using hσ hr₁
        · simpa only [map_zero] using hσ hr₂
        · simpa only [map_smulₛₗ] using congrArg g hr
    simpa using Move.merge (l.map g) (m.map g) hsame
  | erase_zero l m => simpa using Move.erase_zero (l.map g) (m.map g)

/-- Normalizing a segment presentation before taking its semilinear image over a strictly monotone
field homomorphism does not change the target path. -/
theorem ofSegments_map_normalize_semilinear (hσ : StrictMono σ) (g : V →ₛₗ[σ] W) (l : List V) :
    ofSegments 𝕜₂ ((normalize 𝕜₁ l).map g) = ofSegments 𝕜₂ (l.map g) := by
  apply ofSegments_eq_ofSegments_iff.mpr
  exact (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    ((reflTransGen_move_normalize l).lift _ fun _ _ h ↦ h.mapSemilinear hσ g)).symm _ _

/-- The semilinear image of a piecewise-linear path along a semilinear map `g : V →ₛₗ[σ] W`.
When `σ` is strictly monotone, this is independent of the segment presentation
(`TauCeti.PLPath.mapSemilinear_ofSegments`). -/
noncomputable def mapSemilinear (p : PLPath 𝕜₁ V) (g : V →ₛₗ[σ] W) : PLPath 𝕜₂ W :=
  ofSegments 𝕜₂ (p.segments.map g)

theorem mapSemilinear_def (p : PLPath 𝕜₁ V) (g : V →ₛₗ[σ] W) :
    p.mapSemilinear g = ofSegments 𝕜₂ (p.segments.map g) :=
  (rfl)

/-- A semilinear image over a strictly monotone field homomorphism can be computed on any segment
presentation. -/
@[simp]
theorem mapSemilinear_ofSegments (hσ : StrictMono σ) (l : List V) (g : V →ₛₗ[σ] W) :
    (ofSegments 𝕜₁ l).mapSemilinear g = ofSegments 𝕜₂ (l.map g) := by
  simp only [mapSemilinear, segments_ofSegments, ofSegments_map_normalize_semilinear hσ]

@[simp]
theorem mapSemilinear_one (g : V →ₛₗ[σ] W) : (1 : PLPath 𝕜₁ V).mapSemilinear g = 1 := by
  simp [mapSemilinear]

@[simp]
theorem mapSemilinear_mul (hσ : StrictMono σ) (p q : PLPath 𝕜₁ V) (g : V →ₛₗ[σ] W) :
    (p * q).mapSemilinear g = p.mapSemilinear g * q.mapSemilinear g := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  obtain ⟨m, rfl⟩ := ofSegments_surjective q
  rw [← ofSegments_append, mapSemilinear_ofSegments hσ, mapSemilinear_ofSegments hσ,
    mapSemilinear_ofSegments hσ, List.map_append, ofSegments_append]

@[simp]
theorem mapSemilinear_straight (hσ : StrictMono σ) (v : V) (g : V →ₛₗ[σ] W) :
    (straight 𝕜₁ v).mapSemilinear g = straight 𝕜₂ (g v) := by
  simp [straight_def, mapSemilinear_ofSegments hσ]

@[simp]
theorem endpoint_mapSemilinear (p : PLPath 𝕜₁ V) (g : V →ₛₗ[σ] W) :
    (p.mapSemilinear g).endpoint = g p.endpoint := by
  simp [mapSemilinear, endpoint_def, map_list_sum]

/-- Semilinear images over a strictly monotone field homomorphism commute with path reversal. -/
@[simp]
theorem mapSemilinear_reverse (hσ : StrictMono σ) (p : PLPath 𝕜₁ V) (g : V →ₛₗ[σ] W) :
    p.reverse.mapSemilinear g = (p.mapSemilinear g).reverse := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp [mapSemilinear_ofSegments hσ, List.map_reverse, List.map_map, Function.comp_def]

omit [IsStrictOrderedRing 𝕜₁] [IsStrictOrderedRing 𝕜₂] in
/-- Minimum height on segment lists is natural under semilinear maps intertwining the height forms
along a strictly monotone field homomorphism. -/
theorem listMinHeight_mapSemilinear (hσ : StrictMono σ) {g : V →ₛₗ[σ] W}
    {f : Dual 𝕜₁ V} {f' : Dual 𝕜₂ W} (hf : ∀ v, f' (g v) = σ (f v)) (l : List V) :
    listMinHeight f' (l.map g) = σ (listMinHeight f l) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, listMinHeight_cons, listMinHeight_cons, ih, hf, ← map_add, ← σ.map_zero,
      ← hσ.monotone.map_min]

/-- Minimum height is natural under semilinear maps intertwining the height forms along a strictly
monotone field homomorphism. -/
theorem minHeight_mapSemilinear (hσ : StrictMono σ) (p : PLPath 𝕜₁ V) {g : V →ₛₗ[σ] W}
    {f : Dual 𝕜₁ V} {f' : Dual 𝕜₂ W} (hf : ∀ v, f' (g v) = σ (f v)) :
    (p.mapSemilinear g).minHeight f' = σ (p.minHeight f) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  rw [mapSemilinear_ofSegments hσ, minHeight_ofSegments, minHeight_ofSegments,
    listMinHeight_mapSemilinear hσ hf]

omit [IsStrictOrderedRing 𝕜₁] [IsStrictOrderedRing 𝕜₂] in
/-- Capped record reflection commutes with semilinear maps intertwining the height forms along a
strictly monotone field homomorphism. -/
theorem reflectRecords_mapSemilinear (hσ : StrictMono σ) {g : V →ₛₗ[σ] W}
    {f : Dual 𝕜₁ V} {f' : Dual 𝕜₂ W} (hf : ∀ v, f' (g v) = σ (f v))
    (x : V) (c : 𝕜₁) (l : List V) :
    reflectRecords f' (g x) (σ c) (l.map g) = (reflectRecords f x c l).map g := by
  induction l generalizing c with
  | nil => simp
  | cons v l ih =>
    have hm : listMinHeight f' (l.map g) = σ (listMinHeight f l) :=
      listMinHeight_mapSemilinear hσ hf l
    have hmin : min (f' (g v) + listMinHeight f' (l.map g)) (σ c) =
        σ (min (f v + listMinHeight f l) c) := by
      rw [hf, hm, ← map_add, ← hσ.monotone.map_min]
    by_cases h : 0 < min (f v + listMinHeight f l) c
    · have h' : 0 < min (f' (g v) + listMinHeight f' (l.map g)) (σ c) := by
        rw [hmin]
        simpa only [map_zero] using hσ h
      rw [List.map_cons, reflectRecords_cons_of_pos h', reflectRecords_cons_of_pos h,
        List.map_cons, List.map_cons, hmin, hf, ← map_sub σ, ih]
      simp only [preReflection_apply, hf, map_smulₛₗ, map_sub, map_div₀, σ.map_one,
        RingHom.id_apply]
    · have h' : min (f' (g v) + listMinHeight f' (l.map g)) (σ c) ≤ 0 := by
        rw [hmin]
        simpa only [map_zero] using hσ.monotone (le_of_not_gt h)
      rw [List.map_cons, reflectRecords_cons_of_nonpos h',
        reflectRecords_cons_of_nonpos (le_of_not_gt h)]
      simp only [List.map_cons, hf, ← map_sub, ih]

omit [IsStrictOrderedRing 𝕜₁] [IsStrictOrderedRing 𝕜₂] in
/-- Lowering on segment lists is natural under semilinear maps intertwining the root and height
form along a strictly monotone field homomorphism. -/
theorem listLower_mapSemilinear (hσ : StrictMono σ) {g : V →ₛₗ[σ] W}
    {f : Dual 𝕜₁ V} {f' : Dual 𝕜₂ W} (hf : ∀ v, f' (g v) = σ (f v)) (x : V) (l : List V) :
    listLower f' (g x) (l.map g) = (listLower f x l).map (List.map g) := by
  have he : f' (l.map g).sum = σ (f l.sum) := by
    rw [← map_list_sum, hf]
  have hcond : 1 ≤ f' (l.map g).sum - listMinHeight f' (l.map g) ↔
      1 ≤ f l.sum - listMinHeight f l := by
    rw [he, listMinHeight_mapSemilinear hσ hf, ← map_sub, ← σ.map_one, hσ.le_iff_le]
  simp only [listLower_def, hcond]
  split_ifs
  · simp only [Option.map_some, Option.some.injEq]
    simpa only [map_add, σ.map_one, listMinHeight_mapSemilinear hσ hf] using
      reflectRecords_mapSemilinear hσ hf x (listMinHeight f l + 1) l
  · rfl

/-- Lowering commutes with a semilinear map intertwining the root and height form along a strictly
monotone field homomorphism. -/
theorem lower_mapSemilinear (hσ : StrictMono σ) (p : PLPath 𝕜₁ V) {g : V →ₛₗ[σ] W}
    {f : Dual 𝕜₁ V} {f' : Dual 𝕜₂ W} (hf : ∀ v, f' (g v) = σ (f v)) (x : V) :
    lower f' (g x) (p.mapSemilinear g) = (lower f x p).map (fun q ↦ q.mapSemilinear g) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  simp only [mapSemilinear_ofSegments hσ, lower_ofSegments, listLower_mapSemilinear hσ hf,
    Option.map_map]
  congr 1
  funext l
  exact (mapSemilinear_ofSegments hσ l g).symm

/-- Raising commutes with a semilinear map intertwining the root and height form along a strictly
monotone field homomorphism. -/
theorem raise_mapSemilinear (hσ : StrictMono σ) (p : PLPath 𝕜₁ V) {g : V →ₛₗ[σ] W}
    {f : Dual 𝕜₁ V} {f' : Dual 𝕜₂ W} (hf : ∀ v, f' (g v) = σ (f v)) (x : V) :
    raise f' (g x) (p.mapSemilinear g) = (raise f x p).map (fun q ↦ q.mapSemilinear g) := by
  simp only [raise_def, ← mapSemilinear_reverse hσ, lower_mapSemilinear hσ _ hf, Option.map_map]
  congr 1
  funext q
  exact (mapSemilinear_reverse hσ q g).symm

end Semilinear

/-! ### Linear images over the same field -/

variable {𝕜 V W : Type*} [Field 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

section Heights

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {g : V →ₗ[𝕜] W} {f : Dual 𝕜 V} {f' : Dual 𝕜 W}

/-- For a linear map over the same field, `mapSemilinear` agrees with `PLPath.map`. -/
theorem mapSemilinear_eq_map (p : PLPath 𝕜 V) (g : V →ₗ[𝕜] W) :
    p.mapSemilinear g = p.map g := by
  rw [mapSemilinear_def, map_def]

omit [IsStrictOrderedRing 𝕜] in
/-- Capped record reflection commutes with a linear map preserving the height form.
No normalization or injectivity assumption is needed. -/
theorem reflectRecords_map (hf : f'.comp g = f) (x : V) (c : 𝕜) (l : List V) :
    reflectRecords f' (g x) c (l.map g) = (reflectRecords f x c l).map g :=
  reflectRecords_mapSemilinear (σ := RingHom.id 𝕜) strictMono_id (LinearMap.congr_fun hf) x c l

omit [IsStrictOrderedRing 𝕜] in
/-- Lowering on lists is natural for maps preserving the root and coroot form. -/
theorem listLower_map (hf : f'.comp g = f) (x : V) (l : List V) :
    listLower f' (g x) (l.map g) = (listLower f x l).map (List.map g) :=
  listLower_mapSemilinear (σ := RingHom.id 𝕜) strictMono_id (LinearMap.congr_fun hf) x l

/-- Lowering commutes with a linear image preserving the root and the coroot form. -/
theorem lower_map (p : PLPath 𝕜 V) (hf : f'.comp g = f) (x : V) :
    lower f' (g x) (p.map g) = (lower f x p).map (fun q ↦ q.map g) := by
  simpa only [mapSemilinear_eq_map] using
    lower_mapSemilinear (σ := RingHom.id 𝕜) strictMono_id p (LinearMap.congr_fun hf) x

/-- Raising commutes with a linear image preserving the root and the coroot form. -/
theorem raise_map (p : PLPath 𝕜 V) (hf : f'.comp g = f) (x : V) :
    raise f' (g x) (p.map g) = (raise f x p).map (fun q ↦ q.map g) := by
  simpa only [mapSemilinear_eq_map] using
    raise_mapSemilinear (σ := RingHom.id 𝕜) strictMono_id p (LinearMap.congr_fun hf) x

end Heights

end TauCeti.PLPath
