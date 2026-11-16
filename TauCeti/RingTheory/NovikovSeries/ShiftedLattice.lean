/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.RingTheory.NovikovSeries.ActionExtension
public import TauCeti.Topology.Algebra.Module.LocalizedModule

/-!
# Weighted filtrations, shifted lattices, and multilinear extension over Novikov rings

Let `H` be an additive monoid with period homomorphism `N : H →+ ℝ`, and let `w : ι → ℝ` assign a
real action weight to each generator of a free Novikov module `ι → NovikovSeries R H N`. The
*weighted filtration* at cutoff `C : ℝ` is the `nonnegSubring R N`-submodule
`weightedFiltration R N w C` of tuples `x` satisfying `x i ∈ periodFiltration R N (C - w i)` for
every `i` (corresponding to weighted valuation `val(x i) + w i ≥ C`).

Its zero-level `positiveLattice R N w := weightedFiltration R N w 0` is the positive weighted
lattice, and its shifted lattices `shiftedLattice R N w r := weightedFiltration R N w (-r)` form a
monotone family of open and closed `nonnegSubring R N`-submodules (when `ι` is finite) exhausting
`ι → NovikovSeries R H N` as `r` ranges over `[0, ∞)`.

When `R` is commutative and `H` is an additive commutative group:
* Multiplying by any monomial `e^g` of period `N g = r` gives a topological `nonnegSubring R N`-
  linear isomorphism `shiftedLattice R N w r ≃L[nonnegSubring R N] positiveLattice R N w`
  (`shiftedLatticeEquivPositiveOfPeriod`); in the action-extended ring this holds for every `r : ℝ`
  via `T^r` (`shiftedLatticeEquivPositiveAction`), and coordinatewise rescaling identifies
  `positiveLattice R (actionPeriod E) w` with the standard free module
  `ι → nonnegSubring R (actionPeriod E)` (`positiveLatticeEquivPiAction`).
* Whenever `N` is unbounded above on `M ≤ H` and `ι` is finite, `ι → NovikovSeries R H N` is the
  localization of every `weightedFiltration R N w C` at `monomialSubmonoid R N M`
  (`isLocalizedModule_weightedFiltration`).
* Consequently, every continuous `nonnegSubring R N`-multilinear map from a finite family of
  positive weighted lattices into a topological `NovikovSeries R H N`-module extends uniquely to a
  continuous `NovikovSeries R H N`-multilinear map on the full free Novikov modules
  (`extendContinuousMultilinearPositive`), preserving finite valuation loss bounds
  (`multilinearMap_mem_weightedFiltration_of_positiveLattice`) and weighted homogeneous degree
  shifts (`multilinearMap_mem_weightedGradeBy_of_positiveLattice`).

Finally, we record the two-term torsion-versus-localization model for any positive-period monomial
`t = e^g` (`N g > 0`, in particular `T^A` for `A > 0`): the quotient `nonnegSubring R N ⧸ (t)` is
nontrivial and `t` admits no `nonnegSubring R N`-linear contracting homotopy, whereas on any
weighted lattice `(shiftedLatticeEquivPositiveOfPeriod R w rfl).symm` (multiplication by `e^(-g)`,
or `T^(-A)` in the action-extended ring) contracts `t` from `positiveLattice` into `shiftedLattice`
with exact filtration loss `N g` (or `A`).

## Main definitions

* `TauCeti.NovikovSeries.weightedFiltration`, `TauCeti.NovikovSeries.positiveLattice`, and
  `TauCeti.NovikovSeries.shiftedLattice`: weighted filtration submodules and shifted lattices.
* `TauCeti.NovikovSeries.shiftedLatticeInclusion`: continuous inclusions between shifted lattices.
* `TauCeti.NovikovSeries.shiftedLatticeEquivPositiveOfPeriod`,
  `TauCeti.NovikovSeries.shiftedLatticeEquivPositiveAction`,
  `TauCeti.NovikovSeries.positiveLatticeEquivPi`, and
  `TauCeti.NovikovSeries.positiveLatticeEquivPiAction`: topological module equivalences for shifted
  and positive weighted lattices.
* `TauCeti.NovikovSeries.weightedGradeBy`: weighted homogeneous submodules on free Novikov modules.
* `TauCeti.NovikovSeries.extendContinuousMultilinearPositive`: unique continuous multilinear
  extension from positive weighted lattices to full free Novikov modules.

## Main results

* `TauCeti.NovikovSeries.isLocalizedModule_weightedFiltration`: weighted filtrations localize to
  the full free Novikov module.
* `TauCeti.NovikovSeries.existsUnique_extendContinuousMultilinearPositive`,
  `TauCeti.NovikovSeries.multilinearMap_mem_weightedFiltration_of_positiveLattice`, and
  `TauCeti.NovikovSeries.multilinearMap_mem_weightedGradeBy_of_positiveLattice`: unique continuous
  multilinear extension with loss-bound and degree-shift preservation.
* `TauCeti.NovikovSeries.nontrivial_quotient_span_single_of_pos`,
  `TauCeti.NovikovSeries.not_exists_linearMap_single_mul_eq_id`, and
  `TauCeti.NovikovSeries.single_smul_symm_shiftedLatticeEquivPositiveOfPeriod`: torsion over
  `nonnegSubring` versus loss-`N g` contraction into `shiftedLattice`.
-/

public section

noncomputable section

open Function Topology

namespace TauCeti

namespace NovikovSeries

section WeightedFiltration

variable {R H ι : Type*} [Ring R] [AddMonoid H] {N : H →+ ℝ}

variable (R N) in
/-- The weighted filtration submodule at cutoff `C` on `ι → NovikovSeries R H N`: tuples `x` whose
`i`-th coordinate lies in `periodFiltration R N (C - w i)`. -/
def weightedFiltration (w : ι → ℝ) (C : ℝ) :
    Submodule (nonnegSubring R N) (ι → NovikovSeries R H N) where
  carrier := {x | ∀ i, x i ∈ periodFiltration R N (C - w i)}
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  smul_mem' c x hx i := by
    simpa only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, zero_add] using
      mul_mem_periodFiltration (mem_periodFiltration.2 (mem_nonnegSubring.1 c.2)) (hx i)

@[simp]
theorem mem_weightedFiltration {w : ι → ℝ} {C : ℝ} {x : ι → NovikovSeries R H N} :
    x ∈ weightedFiltration R N w C ↔ ∀ i, x i ∈ periodFiltration R N (C - w i) :=
  Iff.rfl

/-- Higher cutoff gives a smaller weighted filtration submodule. -/
theorem antitone_weightedFiltration {w : ι → ℝ} {C D : ℝ} (h : C ≤ D) :
    weightedFiltration R N w D ≤ weightedFiltration R N w C := fun _ hx i =>
  antitone_periodFiltration (sub_le_sub_right h (w i)) (hx i)

/-- Every weighted filtration submodule is closed in the product period topology. -/
theorem isClosed_weightedFiltration (w : ι → ℝ) (C : ℝ) :
    IsClosed (weightedFiltration R N w C : Set (ι → NovikovSeries R H N)) := by
  have h : (weightedFiltration R N w C : Set (ι → NovikovSeries R H N)) =
      Set.univ.pi fun i => (periodFiltration R N (C - w i) : Set (NovikovSeries R H N)) := by
    ext x
    simp [Set.mem_pi]
  rw [h]
  exact isClosed_set_pi fun i _ => isClosed_periodFiltration (C - w i)

/-- On a finite generator set, every weighted filtration submodule is open in the product period
topology. -/
theorem isOpen_weightedFiltration [Finite ι] (w : ι → ℝ) (C : ℝ) :
    IsOpen (weightedFiltration R N w C : Set (ι → NovikovSeries R H N)) := by
  have h : (weightedFiltration R N w C : Set (ι → NovikovSeries R H N)) =
      Set.univ.pi fun i => (periodFiltration R N (C - w i) : Set (NovikovSeries R H N)) := by
    ext x
    simp [Set.mem_pi]
  rw [h]
  exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_periodFiltration (C - w i)

/-- Multiplying by a monomial `r e^g` shifts the weighted filtration cutoff by `N g`. -/
theorem single_smul_mem_weightedFiltration {w : ι → ℝ} {C : ℝ} (g : H) (r : R)
    {x : ι → NovikovSeries R H N} (hx : x ∈ weightedFiltration R N w C) :
    (single g r : NovikovSeries R H N) • x ∈ weightedFiltration R N w (N g + C) := fun i => by
  simpa only [Pi.smul_apply, smul_eq_mul, add_sub_assoc] using
    mul_mem_periodFiltration (single_mem_periodFiltration g r) (hx i)

/-- Under left cancellation on exponents, multiplying by `u e^g` with unit coefficient `u` shifts
the weighted filtration by exactly `N g`. -/
theorem single_smul_mem_weightedFiltration_iff [IsLeftCancelAdd H] {w : ι → ℝ} {C : ℝ} (g : H)
    (u : Rˣ) {x : ι → NovikovSeries R H N} :
    (single g (u : R) : NovikovSeries R H N) • x ∈ weightedFiltration R N w (N g + C) ↔
      x ∈ weightedFiltration R N w C := by
  refine forall_congr' fun i => ?_
  simpa only [Pi.smul_apply, smul_eq_mul, add_sub_assoc] using
    single_mul_mem_periodFiltration_iff (R := R) (N := N) g u (C := C - w i) (a := x i)

/-- On a finite generator set, every element of `ι → NovikovSeries R H N` lies in some weighted
filtration level. -/
theorem exists_mem_weightedFiltration [Finite ι] (w : ι → ℝ) (x : ι → NovikovSeries R H N) :
    ∃ C : ℝ, x ∈ weightedFiltration R N w C := by
  cases nonempty_fintype ι
  choose D hD using fun i => exists_mem_periodFiltration (x i)
  let s : Finset ℝ := insert 0 (Finset.univ.image fun i => D i + w i)
  have hs : s.Nonempty := ⟨0, Finset.mem_insert_self 0 _⟩
  refine ⟨s.min' hs, fun i => ?_⟩
  have hle : s.min' hs ≤ D i + w i :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  exact antitone_periodFiltration (by linarith) (hD i)

variable (R N) in
/-- The positive weighted lattice `weightedFiltration R N w 0`. -/
def positiveLattice (w : ι → ℝ) : Submodule (nonnegSubring R N) (ι → NovikovSeries R H N) :=
  weightedFiltration R N w 0

variable (R N) in
/-- The shifted weighted lattice `weightedFiltration R N w (-r)` of allowance `r : ℝ`. -/
def shiftedLattice (w : ι → ℝ) (r : ℝ) : Submodule (nonnegSubring R N) (ι → NovikovSeries R H N) :=
  weightedFiltration R N w (-r)

@[simp]
theorem mem_positiveLattice {w : ι → ℝ} {x : ι → NovikovSeries R H N} :
    x ∈ positiveLattice R N w ↔ ∀ i, x i ∈ periodFiltration R N (-w i) := by
  simp [positiveLattice]

@[simp]
theorem mem_shiftedLattice {w : ι → ℝ} {r : ℝ} {x : ι → NovikovSeries R H N} :
    x ∈ shiftedLattice R N w r ↔ ∀ i, x i ∈ periodFiltration R N (-r - w i) :=
  Iff.rfl

variable (R N) in
theorem positiveLattice_eq_shiftedLattice_zero (w : ι → ℝ) :
    positiveLattice R N w = shiftedLattice R N w 0 := by
  simp [positiveLattice, shiftedLattice]

/-- Shifted lattices are monotone in the shift parameter `r`. -/
theorem monotone_shiftedLattice {w : ι → ℝ} {r s : ℝ} (h : r ≤ s) :
    shiftedLattice R N w r ≤ shiftedLattice R N w s :=
  antitone_weightedFiltration (neg_le_neg h)

/-- On a finite generator set, the nonnegative shifted lattices exhaust
`ι → NovikovSeries R H N`. -/
theorem iUnion_shiftedLattice [Finite ι] (w : ι → ℝ) :
    (⋃ r ≥ (0 : ℝ), (shiftedLattice R N w r : Set (ι → NovikovSeries R H N))) = Set.univ := by
  refine Set.eq_univ_iff_forall.2 fun x => ?_
  obtain ⟨C, hx⟩ := exists_mem_weightedFiltration w x
  refine Set.mem_iUnion₂.2 ⟨max (-C) 0, le_max_right _ _, ?_⟩
  exact antitone_weightedFiltration (by linarith [le_max_left (-C) (0 : ℝ)]) hx

variable (R N) in
/-- The continuous `nonnegSubring R N`-linear inclusion between nested shifted lattices. -/
def shiftedLatticeInclusion (w : ι → ℝ) {r s : ℝ} (h : r ≤ s) :
    shiftedLattice R N w r →L[nonnegSubring R N] shiftedLattice R N w s where
  toLinearMap := Submodule.inclusion (monotone_shiftedLattice h)
  cont := continuous_induced_rng.2 continuous_subtype_val

@[simp]
theorem coe_shiftedLatticeInclusion {w : ι → ℝ} {r s : ℝ} (h : r ≤ s)
    (x : shiftedLattice R N w r) :
    ((shiftedLatticeInclusion R N w h x : shiftedLattice R N w s) : ι → NovikovSeries R H N) =
      x :=
  (rfl)

theorem shiftedLatticeInclusion_injective {w : ι → ℝ} {r s : ℝ} (h : r ≤ s) :
    Injective (shiftedLatticeInclusion R N w h) := fun _ _ hxy =>
  Subtype.ext <| by
    simpa only [coe_shiftedLatticeInclusion] using congrArg Subtype.val hxy

@[simp]
theorem shiftedLatticeInclusion_refl (w : ι → ℝ) (r : ℝ) :
    shiftedLatticeInclusion R N w (le_refl r) = ContinuousLinearMap.id _ _ := by
  ext x i
  rfl

theorem shiftedLatticeInclusion_comp (w : ι → ℝ) {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    (shiftedLatticeInclusion R N w hst).comp (shiftedLatticeInclusion R N w hrs) =
      shiftedLatticeInclusion R N w (hrs.trans hst) := by
  ext x i
  rfl

end WeightedFiltration

section LatticeEquivalences

variable {R H G ι : Type*} [CommRing R] [AddCommGroup H] {N : H →+ ℝ}

/-- Multiplying by a monomial `e^g` of period `N g = r` identifies membership in
`shiftedLattice R N w r` with membership in `positiveLattice R N w`. -/
theorem mem_shiftedLattice_iff_single_smul {w : ι → ℝ} {r : ℝ} {g : H} (hg : N g = r)
    {x : ι → NovikovSeries R H N} :
    x ∈ shiftedLattice R N w r ↔
      (single g (1 : R) : NovikovSeries R H N) • x ∈ positiveLattice R N w := by
  have h := single_smul_mem_weightedFiltration_iff (R := R) (N := N) (w := w) (C := -r) g (1 : Rˣ)
    (x := x)
  rw [hg, add_neg_cancel] at h
  exact h.symm

variable (R) in
/-- Multiplying by a monomial `e^g` of period `N g = r` gives a topological
`nonnegSubring R N`-linear equivalence between `shiftedLattice R N w r` and
`positiveLattice R N w`. -/
def shiftedLatticeEquivPositiveOfPeriod (w : ι → ℝ) {r : ℝ} {g : H} (hg : N g = r) :
    shiftedLattice R N w r ≃L[nonnegSubring R N] positiveLattice R N w where
  toFun x := ⟨(single g 1 : NovikovSeries R H N) • x.1,
    (mem_shiftedLattice_iff_single_smul hg).1 x.2⟩
  invFun y := ⟨(single (-g) 1 : NovikovSeries R H N) • y.1, by
    rw [mem_shiftedLattice_iff_single_smul hg, smul_smul, single_mul_single, add_neg_cancel,
      mul_one, single_zero_one, one_smul]
    exact y.2⟩
  left_inv x := Subtype.ext <| by
    dsimp only
    rw [smul_smul, single_mul_single, neg_add_cancel, mul_one, single_zero_one, one_smul]
  right_inv y := Subtype.ext <| by
    dsimp only
    rw [smul_smul, single_mul_single, add_neg_cancel, mul_one, single_zero_one, one_smul]
  map_add' _ _ := Subtype.ext (smul_add _ _ _)
  map_smul' c x := Subtype.ext <| funext fun i => by
    simp [Pi.smul_apply, Subring.smul_def, mul_left_comm]
  continuous_toFun :=
    continuous_induced_rng.2 ((continuous_const_smul _).comp continuous_subtype_val)
  continuous_invFun :=
    continuous_induced_rng.2 ((continuous_const_smul _).comp continuous_subtype_val)

@[simp]
theorem coe_shiftedLatticeEquivPositiveOfPeriod {w : ι → ℝ} {r : ℝ} {g : H} (hg : N g = r)
    (x : shiftedLattice R N w r) :
    (shiftedLatticeEquivPositiveOfPeriod R w hg x : ι → NovikovSeries R H N) =
      (single g 1 : NovikovSeries R H N) • x.1 :=
  (rfl)

@[simp]
theorem coe_shiftedLatticeEquivPositiveOfPeriod_symm {w : ι → ℝ} {r : ℝ} {g : H} (hg : N g = r)
    (y : positiveLattice R N w) :
    ((shiftedLatticeEquivPositiveOfPeriod R w hg).symm y : ι → NovikovSeries R H N) =
      (single (-g) 1 : NovikovSeries R H N) • y.1 :=
  (rfl)

variable (R) in
/-- In the action-extended Novikov ring, multiplication by `T^r` identifies every shifted lattice
`shiftedLattice R (actionPeriod E) w r` with `positiveLattice R (actionPeriod E) w`. -/
def shiftedLatticeEquivPositiveAction [AddCommGroup G] (E : G →+ ℝ) (w : ι → ℝ) (r : ℝ) :
    shiftedLattice R (actionPeriod E) w r ≃L[nonnegSubring R (actionPeriod E)]
      positiveLattice R (actionPeriod E) w :=
  shiftedLatticeEquivPositiveOfPeriod R (N := actionPeriod E) w (g := (0, r)) (by simp)

@[simp]
theorem coe_shiftedLatticeEquivPositiveAction [AddCommGroup G] (E : G →+ ℝ) (w : ι → ℝ) (r : ℝ)
    (x : shiftedLattice R (actionPeriod E) w r) :
    (shiftedLatticeEquivPositiveAction R E w r x : ι → NovikovSeries R (G × ℝ) (actionPeriod E)) =
      actionMonomial R E r • x.1 := by
  simp [shiftedLatticeEquivPositiveAction, actionMonomial_eq_single]

@[simp]
theorem coe_shiftedLatticeEquivPositiveAction_symm [AddCommGroup G] (E : G →+ ℝ) (w : ι → ℝ)
    (r : ℝ) (y : positiveLattice R (actionPeriod E) w) :
    ((shiftedLatticeEquivPositiveAction R E w r).symm y :
        ι → NovikovSeries R (G × ℝ) (actionPeriod E)) =
      actionMonomial R E (-r) • y.1 := by
  simp [shiftedLatticeEquivPositiveAction, actionMonomial_eq_single]

variable (R) in
/-- Given a section `τ : ℝ → H` of `N`, coordinatewise rescaling by `e^(τ (w i))` identifies the
positive weighted lattice `positiveLattice R N w` with the standard free module
`ι → nonnegSubring R N`. -/
def positiveLatticeEquivPi (τ : ℝ → H) (hτ : ∀ t, N (τ t) = t) (w : ι → ℝ) :
    positiveLattice R N w ≃L[nonnegSubring R N] (ι → nonnegSubring R N) where
  toFun x i := ⟨single (τ (w i)) 1 * x.1 i, by
    have h := mul_mem_periodFiltration (single_mem_periodFiltration (τ (w i)) (1 : R))
      (mem_positiveLattice.1 x.2 i)
    rw [hτ (w i), add_neg_cancel] at h
    exact mem_nonnegSubring.2 (mem_periodFiltration.1 h)⟩
  invFun y := ⟨fun i => single (-τ (w i)) 1 * (y i : NovikovSeries R H N), by
    refine mem_positiveLattice.2 fun i => ?_
    have h := mul_mem_periodFiltration (single_mem_periodFiltration (-τ (w i)) (1 : R))
      (mem_periodFiltration.2 (mem_nonnegSubring.1 (y i).2))
    simpa [map_neg, hτ (w i)] using h⟩
  left_inv x := Subtype.ext <| funext fun i => by
    simp [← mul_assoc, single_mul_single]
  right_inv y := funext fun i => Subtype.ext <| by
    simp [← mul_assoc, single_mul_single]
  map_add' _ _ := funext fun _ => Subtype.ext (mul_add _ _ _)
  map_smul' c x := funext fun i => Subtype.ext <| by
    simp [Subring.smul_def, mul_left_comm]
  continuous_toFun := continuous_pi fun i => continuous_induced_rng.2 <|
    (continuous_const_mul _).comp ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.2 <| continuous_pi fun i =>
    (continuous_const_mul _).comp (continuous_subtype_val.comp (continuous_apply i))

@[simp]
theorem coe_positiveLatticeEquivPi (τ : ℝ → H) (hτ : ∀ t, N (τ t) = t) (w : ι → ℝ)
    (x : positiveLattice R N w) (i : ι) :
    (positiveLatticeEquivPi R τ hτ w x i : NovikovSeries R H N) = single (τ (w i)) 1 * x.1 i :=
  (rfl)

@[simp]
theorem coe_positiveLatticeEquivPi_symm (τ : ℝ → H) (hτ : ∀ t, N (τ t) = t) (w : ι → ℝ)
    (y : ι → nonnegSubring R N) (i : ι) :
    ((positiveLatticeEquivPi R τ hτ w).symm y : ι → NovikovSeries R H N) i =
      single (-τ (w i)) 1 * (y i : NovikovSeries R H N) :=
  (rfl)

variable (R) in
/-- In the action-extended Novikov ring, coordinatewise rescaling by `T^(w i)` identifies any
positive weighted lattice with the standard free `nonnegSubring`-module. -/
def positiveLatticeEquivPiAction [AddCommGroup G] (E : G →+ ℝ) (w : ι → ℝ) :
    positiveLattice R (actionPeriod E) w ≃L[nonnegSubring R (actionPeriod E)]
      (ι → nonnegSubring R (actionPeriod E)) :=
  positiveLatticeEquivPi R (N := actionPeriod E) (fun t => (0, t)) (fun t => by simp) w

@[simp]
theorem coe_positiveLatticeEquivPiAction [AddCommGroup G] (E : G →+ ℝ) (w : ι → ℝ)
    (x : positiveLattice R (actionPeriod E) w) (i : ι) :
    (positiveLatticeEquivPiAction R E w x i : NovikovSeries R (G × ℝ) (actionPeriod E)) =
      actionMonomial R E (w i) * x.1 i := by
  simp [positiveLatticeEquivPiAction, actionMonomial_eq_single]

@[simp]
theorem coe_positiveLatticeEquivPiAction_symm [AddCommGroup G] (E : G →+ ℝ) (w : ι → ℝ)
    (y : ι → nonnegSubring R (actionPeriod E)) (i : ι) :
    ((positiveLatticeEquivPiAction R E w).symm y :
        ι → NovikovSeries R (G × ℝ) (actionPeriod E)) i =
      actionMonomial R E (-w i) * (y i : NovikovSeries R (G × ℝ) (actionPeriod E)) := by
  simp [positiveLatticeEquivPiAction, actionMonomial_eq_single]

end LatticeEquivalences

section ModuleLocalization

variable {R H G ι : Type*} [CommRing R] [AddCommGroup H] {N : H →+ ℝ}

/-- **Localization of weighted filtrations.** When `ι` is finite and `N` is unbounded above on
`M ≤ H`, the inclusion of `weightedFiltration R N w C` into `ι → NovikovSeries R H N` is a module
localization at `monomialSubmonoid R N M`. -/
theorem isLocalizedModule_weightedFiltration [Finite ι] {M : AddSubmonoid H}
    (hM_unbdd : ∀ C : ℝ, ∃ g ∈ M, C ≤ N g) (w : ι → ℝ) (C : ℝ) :
    IsLocalizedModule (monomialSubmonoid R N M) (weightedFiltration R N w C).subtype where
  map_units s := by
    obtain ⟨u, hu⟩ := isUnit_coe_of_mem_monomialSubmonoid s.2
    refine (Module.End.isUnit_iff _).2 ⟨fun x y hxy => ?_, fun y => ?_⟩
    · funext i
      have hi : (u : NovikovSeries R H N) * x i = (u : NovikovSeries R H N) * y i := by
        simpa [Algebra.lsmul_coe, Subring.smul_def, hu] using congrFun hxy i
      exact u.isUnit.mul_left_cancel hi
    · refine ⟨(↑u⁻¹ : NovikovSeries R H N) • y, ?_⟩
      funext i
      simp [Subring.smul_def, ← hu, ← mul_assoc]
  surj x := by
    obtain ⟨D, hx⟩ := exists_mem_weightedFiltration w x
    obtain ⟨g, hgM, hg⟩ := hM_unbdd (max (C - D) 0)
    have hg0 : 0 ≤ N g := le_trans (le_max_right _ _) hg
    have hCD : C ≤ N g + D := by linarith [le_max_left (C - D) (0 : ℝ)]
    let s : monomialSubmonoid R N M :=
      ⟨⟨single g 1, single_mem_nonnegSubring hg0 1⟩, single_one_mem_monomialSubmonoid hgM hg0⟩
    have hmem : (s : nonnegSubring R N) • x ∈ weightedFiltration R N w C :=
      antitone_weightedFiltration hCD (single_smul_mem_weightedFiltration g 1 hx)
    exact ⟨(⟨(s : nonnegSubring R N) • x, hmem⟩, s), rfl⟩
  exists_of_eq hxy := ⟨1, by rw [Subtype.ext hxy]⟩

theorem isLocalizedModule_positiveLattice [Finite ι] {M : AddSubmonoid H}
    (hM_unbdd : ∀ C : ℝ, ∃ g ∈ M, C ≤ N g) (w : ι → ℝ) :
    IsLocalizedModule (monomialSubmonoid R N M) (positiveLattice R N w).subtype :=
  isLocalizedModule_weightedFiltration hM_unbdd w 0

theorem isLocalizedModule_shiftedLattice [Finite ι] {M : AddSubmonoid H}
    (hM_unbdd : ∀ C : ℝ, ∃ g ∈ M, C ≤ N g) (w : ι → ℝ) (r : ℝ) :
    IsLocalizedModule (monomialSubmonoid R N M) (shiftedLattice R N w r).subtype :=
  isLocalizedModule_weightedFiltration hM_unbdd w (-r)

theorem isLocalizedModule_weightedFiltration_action [Finite ι] [AddCommGroup G] (E : G →+ ℝ)
    (w : ι → ℝ) (C : ℝ) :
    IsLocalizedModule (actionMonomialSubmonoid R E)
      (weightedFiltration R (actionPeriod E) w C).subtype := by
  rw [actionMonomialSubmonoid_eq]
  exact isLocalizedModule_weightedFiltration (R := R) (H := G × ℝ) (N := actionPeriod E)
    (M := (AddSubmonoid.nonneg ℝ).map (AddMonoidHom.inr G ℝ))
    (fun D => ⟨(0, max D 0), ⟨max D 0, le_max_right _ _, rfl⟩, by simp⟩) w C

theorem isLocalizedModule_positiveLattice_action [Finite ι] [AddCommGroup G] (E : G →+ ℝ)
    (w : ι → ℝ) :
    IsLocalizedModule (actionMonomialSubmonoid R E)
      (positiveLattice R (actionPeriod E) w).subtype :=
  isLocalizedModule_weightedFiltration_action E w 0

end ModuleLocalization

section WeightedGrading

variable {R H ι B : Type*}

variable (R N) in
/-- The weighted homogeneous submodule of degree `b` on `ι → NovikovSeries R H N`: tuples `x` whose
`i`-th coordinate lies in `gradeBy R N μ (b - deg i)`. -/
def weightedGradeBy [Semiring R] [AddZeroClass H] (N : H →+ ℝ) [AddGroup B]
    (μ : H → B) (deg : ι → B) (b : B) : Submodule R (ι → NovikovSeries R H N) where
  carrier := {x | ∀ i, x i ∈ gradeBy R N μ (b - deg i)}
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  smul_mem' r _ hx i := Submodule.smul_mem _ r (hx i)

@[simp]
theorem mem_weightedGradeBy [Semiring R] [AddZeroClass H] {N : H →+ ℝ} [AddGroup B]
    {μ : H → B} {deg : ι → B} {b : B} {x : ι → NovikovSeries R H N} :
    x ∈ weightedGradeBy R N μ deg b ↔ ∀ i, x i ∈ gradeBy R N μ (b - deg i) :=
  Iff.rfl

/-- Every weighted homogeneous submodule is closed in the product period topology. -/
theorem isClosed_weightedGradeBy [Ring R] [AddZeroClass H] {N : H →+ ℝ} [AddGroup B]
    (μ : H → B) (deg : ι → B) (b : B) :
    IsClosed (weightedGradeBy R N μ deg b : Set (ι → NovikovSeries R H N)) := by
  have h : (weightedGradeBy R N μ deg b : Set (ι → NovikovSeries R H N)) =
      Set.univ.pi fun i => (gradeBy R N μ (b - deg i) : Set (NovikovSeries R H N)) := by
    ext x
    simp [Set.mem_pi]
  rw [h]
  exact isClosed_set_pi fun i _ => isClosed_gradeBy μ (b - deg i)

/-- Multiplying by a degree-zero monomial preserves every weighted homogeneous piece. -/
theorem single_smul_mem_weightedGradeBy_of_map_eq_zero [Semiring R] [AddMonoid H] {N : H →+ ℝ}
    [AddGroup B] {μ : H →+ B} {deg : ι → B} {g : H} (hg : μ g = 0) (r : R) {b : B}
    {x : ι → NovikovSeries R H N} (hx : x ∈ weightedGradeBy R N μ deg b) :
    (single g r : NovikovSeries R H N) • x ∈ weightedGradeBy R N μ deg b := fun i =>
  single_mul_mem_gradeBy_of_map_eq_zero hg r (hx i)

/-- Over an additive group of exponents, multiplying by a degree-zero monomial with unit
coefficient preserves and reflects every weighted homogeneous piece. -/
theorem single_smul_mem_weightedGradeBy_iff [Semiring R] [AddGroup H] {N : H →+ ℝ} [AddGroup B]
    {μ : H →+ B} {deg : ι → B} {g : H} (hg : μ g = 0) (u : Rˣ) {b : B}
    {x : ι → NovikovSeries R H N} :
    (single g (u : R) : NovikovSeries R H N) • x ∈ weightedGradeBy R N μ deg b ↔
      x ∈ weightedGradeBy R N μ deg b :=
  forall_congr' fun _ => single_mul_mem_gradeBy_iff hg u

end WeightedGrading

section MultilinearExtension

variable {R H G κ ι' B : Type*}

/-- Product of monomials `single (g k) 1` over a finite set equals `single (∑ k, g k) 1`. -/
private theorem prod_single_one [CommSemiring R] [AddCommMonoid H] {N : H →+ ℝ} (s : Finset κ)
    (g : κ → H) :
    ∏ k ∈ s, (single (g k) (1 : R) : NovikovSeries R H N) = single (∑ k ∈ s, g k) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, ih, single_mul_single, mul_one]

section Extend

variable [CommRing R] [AddCommGroup H] {N : H →+ ℝ} [Finite κ] {ι : κ → Type*} [∀ k, Finite (ι k)]
variable {M' : Type*} [AddCommMonoid M']
variable [Module (nonnegSubring R N) M'] [Module (NovikovSeries R H N) M']
variable [IsScalarTower (nonnegSubring R N) (NovikovSeries R H N) M']
variable [TopologicalSpace M'] [ContinuousConstSMul (NovikovSeries R H N) M']

/-- Unique continuous `NovikovSeries R H N`-multilinear extension of a continuous
`nonnegSubring R N`-multilinear map defined on positive weighted lattices. -/
def extendContinuousMultilinearPositive (hN_unbdd : ∀ C : ℝ, ∃ g : H, C ≤ N g)
    (w : ∀ k, ι k → ℝ)
    (f : ContinuousMultilinearMap (nonnegSubring R N)
      (fun k => positiveLattice R N (w k)) M') :
    ContinuousMultilinearMap (NovikovSeries R H N)
      (fun k => ι k → NovikovSeries R H N) M' :=
  letI := isLocalization_monomialSubmonoid (R := R) (N := N) (M := ⊤)
    fun C => let ⟨g, hg⟩ := hN_unbdd C; ⟨g, trivial, hg⟩
  letI : ∀ k, IsLocalizedModule (monomialSubmonoid R N ⊤) (positiveLattice R N (w k)).subtype :=
    fun k => isLocalizedModule_positiveLattice (M := ⊤)
      (fun C => let ⟨g, hg⟩ := hN_unbdd C; ⟨g, trivial, hg⟩) (w k)
  IsLocalizedModule.extendContinuousMultilinear (monomialSubmonoid R N ⊤) (NovikovSeries R H N)
    (fun k => (positiveLattice R N (w k)).subtype)
    (fun _ => IsInducing.subtypeVal)
    (fun k => by
      rw [Submodule.coe_subtype, Subtype.range_coe]
      exact isOpen_weightedFiltration (R := R) (N := N) (w k) 0)
    f

@[simp]
theorem extendContinuousMultilinearPositive_apply_coe (hN_unbdd : ∀ C : ℝ, ∃ g : H, C ≤ N g)
    (w : ∀ k, ι k → ℝ)
    (f : ContinuousMultilinearMap (nonnegSubring R N)
      (fun k => positiveLattice R N (w k)) M')
    (m : ∀ k, positiveLattice R N (w k)) :
    extendContinuousMultilinearPositive hN_unbdd w f (fun k => (m k : ι k → NovikovSeries R H N)) =
      f m := by
  let _ := isLocalization_monomialSubmonoid (R := R) (N := N) (M := ⊤)
    fun C => let ⟨g, hg⟩ := hN_unbdd C; ⟨g, trivial, hg⟩
  let _ : ∀ k, IsLocalizedModule (monomialSubmonoid R N ⊤) (positiveLattice R N (w k)).subtype :=
    fun k => isLocalizedModule_positiveLattice (M := ⊤)
      (fun C => let ⟨g, hg⟩ := hN_unbdd C; ⟨g, trivial, hg⟩) (w k)
  exact IsLocalizedModule.extendContinuousMultilinear_apply_comp (monomialSubmonoid R N ⊤)
    (NovikovSeries R H N) (fun k => (positiveLattice R N (w k)).subtype) _ _ f m

/-- Any continuous `NovikovSeries R H N`-multilinear map restricting to `f` on positive weighted
lattices equals `extendContinuousMultilinearPositive hN_unbdd w f`. -/
theorem extendContinuousMultilinearPositive_unique (hN_unbdd : ∀ C : ℝ, ∃ g : H, C ≤ N g)
    (w : ∀ k, ι k → ℝ)
    (f : ContinuousMultilinearMap (nonnegSubring R N)
      (fun k => positiveLattice R N (w k)) M')
    {F : ContinuousMultilinearMap (NovikovSeries R H N) (fun k => ι k → NovikovSeries R H N) M'}
    (h : ∀ m : ∀ k, positiveLattice R N (w k),
      F (fun k => (m k : ι k → NovikovSeries R H N)) = f m) :
    F = extendContinuousMultilinearPositive hN_unbdd w f := by
  let _ := isLocalization_monomialSubmonoid (R := R) (N := N) (M := ⊤)
    fun C => let ⟨g, hg⟩ := hN_unbdd C; ⟨g, trivial, hg⟩
  let _ : ∀ k, IsLocalizedModule (monomialSubmonoid R N ⊤) (positiveLattice R N (w k)).subtype :=
    fun k => isLocalizedModule_positiveLattice (M := ⊤)
      (fun C => let ⟨g, hg⟩ := hN_unbdd C; ⟨g, trivial, hg⟩) (w k)
  exact IsLocalizedModule.extendContinuousMultilinear_unique (monomialSubmonoid R N ⊤)
    (NovikovSeries R H N) (fun k => (positiveLattice R N (w k)).subtype) _ _ f h

/-- Existence and uniqueness of the continuous `NovikovSeries R H N`-multilinear extension from
positive weighted lattices. -/
theorem existsUnique_extendContinuousMultilinearPositive (hN_unbdd : ∀ C : ℝ, ∃ g : H, C ≤ N g)
    (w : ∀ k, ι k → ℝ)
    (f : ContinuousMultilinearMap (nonnegSubring R N)
      (fun k => positiveLattice R N (w k)) M') :
    ∃! F : ContinuousMultilinearMap (NovikovSeries R H N)
      (fun k => ι k → NovikovSeries R H N) M',
      ∀ m : ∀ k, positiveLattice R N (w k), F (fun k => (m k : ι k → NovikovSeries R H N)) = f m :=
  ⟨extendContinuousMultilinearPositive hN_unbdd w f,
    extendContinuousMultilinearPositive_apply_coe hN_unbdd w f,
    fun _ h => extendContinuousMultilinearPositive_unique hN_unbdd w f h⟩

end Extend

section FiltrationAndGrading

variable [CommRing R] [AddCommGroup H] {N : H →+ ℝ} [Fintype κ] {ι : κ → Type*}

/-- **Loss-bound preservation.** If a multilinear map `F` over `NovikovSeries R H N` sends positive
weighted lattices into `shiftedLattice R N w' D` (valuation loss `≤ D`), then for any cutoffs
`C k = N (g k)`, `F` sends `∏ k, weightedFiltration (w k) (C k)` into
`weightedFiltration w' (∑ k, C k - D)`. -/
theorem multilinearMap_mem_weightedFiltration_of_positiveLattice
    {w : ∀ k, ι k → ℝ} {w' : ι' → ℝ} {D : ℝ}
    (F : (∀ k, ι k → NovikovSeries R H N) →ₘₗ[NovikovSeries R H N] (ι' → NovikovSeries R H N))
    (hloss : ∀ m : ∀ k, positiveLattice R N (w k),
      F (fun k => (m k : ι k → NovikovSeries R H N)) ∈ shiftedLattice R N w' D)
    {C : κ → ℝ} {g : κ → H} (hg : ∀ k, N (g k) = C k)
    {v : ∀ k, ι k → NovikovSeries R H N}
    (hv : ∀ k, v k ∈ weightedFiltration R N (w k) (C k)) :
    F v ∈ weightedFiltration R N w' ((∑ k, C k) - D) := by
  let m : ∀ k, positiveLattice R N (w k) := fun k =>
    ⟨(single (-g k) 1 : NovikovSeries R H N) • v k, by
      have h := single_smul_mem_weightedFiltration (-g k) 1 (hv k)
      simpa [positiveLattice, map_neg, hg k] using h⟩
  have hv_eq : v = fun k => (single (g k) (1 : R) : NovikovSeries R H N) •
      (m k : ι k → NovikovSeries R H N) := by
    funext k
    simp only [m, smul_smul, single_mul_single, add_neg_cancel, mul_one, single_zero_one, one_smul]
  rw [hv_eq, F.map_smul_univ]
  simp only [RingHom.id_apply]
  rw [prod_single_one]
  have hmem := single_smul_mem_weightedFiltration (∑ k, g k) (1 : R) (hloss m)
  have hsum : N (∑ k, g k) = ∑ k, C k := by simp [map_sum, hg]
  simpa only [hsum, ← sub_eq_add_neg] using hmem

/-- **Degree-shift preservation.** Suppose `N` is unbounded above on `μ.ker`. If a multilinear map
`F` over `NovikovSeries R H N` sends tuples of positive weighted lattice elements of degrees `b k`
into degree `∑ k, b k + d`, then `F` has the same degree shift on all homogeneous tuples. -/
theorem multilinearMap_mem_weightedGradeBy_of_positiveLattice [∀ k, Finite (ι k)] [AddCommGroup B]
    {μ : H →+ B} (hker_unbdd : ∀ C : ℝ, ∃ g : H, μ g = 0 ∧ C ≤ N g)
    {w : ∀ k, ι k → ℝ} {deg : ∀ k, ι k → B} {deg' : ι' → B} {d : B}
    (F : (∀ k, ι k → NovikovSeries R H N) →ₘₗ[NovikovSeries R H N] (ι' → NovikovSeries R H N))
    (hdeg : ∀ (m : ∀ k, positiveLattice R N (w k)) (b : κ → B),
      (∀ k, (m k : ι k → NovikovSeries R H N) ∈ weightedGradeBy R N μ (deg k) (b k)) →
      F (fun k => (m k : ι k → NovikovSeries R H N)) ∈ weightedGradeBy R N μ deg' ((∑ k, b k) + d))
    {b : κ → B} {v : ∀ k, ι k → NovikovSeries R H N}
    (hv : ∀ k, v k ∈ weightedGradeBy R N μ (deg k) (b k)) :
    F v ∈ weightedGradeBy R N μ deg' ((∑ k, b k) + d) := by
  choose D hD using fun k => exists_mem_weightedFiltration (w k) (v k)
  choose g hgμ hgN using fun k => hker_unbdd (-D k)
  let m : ∀ k, positiveLattice R N (w k) := fun k =>
    ⟨(single (g k) 1 : NovikovSeries R H N) • v k,
      antitone_weightedFiltration (by linarith [hgN k])
        (single_smul_mem_weightedFiltration (g k) 1 (hD k))⟩
  have hm_deg : ∀ k, (m k : ι k → NovikovSeries R H N) ∈ weightedGradeBy R N μ (deg k) (b k) :=
    fun k => single_smul_mem_weightedGradeBy_of_map_eq_zero (hgμ k) 1 (hv k)
  have hv_eq : v = fun k => (single (-g k) (1 : R) : NovikovSeries R H N) •
      (m k : ι k → NovikovSeries R H N) := by
    funext k
    simp only [m, smul_smul, single_mul_single, neg_add_cancel, mul_one, single_zero_one, one_smul]
  rw [hv_eq, F.map_smul_univ]
  simp only [RingHom.id_apply]
  rw [prod_single_one]
  refine single_smul_mem_weightedGradeBy_of_map_eq_zero ?_ 1 (hdeg m b hm_deg)
  simp [map_sum, map_neg, hgμ]

/-- Action-extension specialization of `multilinearMap_mem_weightedFiltration_of_positiveLattice`:
loss-bound preservation holds at every real cutoff tuple `C : κ → ℝ`. -/
theorem multilinearMap_mem_weightedFiltration_action [AddCommGroup G] (E : G →+ ℝ)
    {w : ∀ k, ι k → ℝ} {w' : ι' → ℝ} {D : ℝ}
    (F : (∀ k, ι k → NovikovSeries R (G × ℝ) (actionPeriod E))
      →ₘₗ[NovikovSeries R (G × ℝ) (actionPeriod E)]
      (ι' → NovikovSeries R (G × ℝ) (actionPeriod E)))
    (hloss : ∀ m : ∀ k, positiveLattice R (actionPeriod E) (w k),
      F (fun k => (m k : ι k → NovikovSeries R (G × ℝ) (actionPeriod E))) ∈
        shiftedLattice R (actionPeriod E) w' D)
    {C : κ → ℝ} {v : ∀ k, ι k → NovikovSeries R (G × ℝ) (actionPeriod E)}
    (hv : ∀ k, v k ∈ weightedFiltration R (actionPeriod E) (w k) (C k)) :
    F v ∈ weightedFiltration R (actionPeriod E) w' ((∑ k, C k) - D) :=
  multilinearMap_mem_weightedFiltration_of_positiveLattice F hloss
    (g := fun k => (0, C k)) (fun k => by simp) hv

/-- Action-extension specialization of `multilinearMap_mem_weightedGradeBy_of_positiveLattice`:
degree-shift preservation holds automatically for `actionDegree μ`. -/
theorem multilinearMap_mem_weightedGradeBy_action [∀ k, Finite (ι k)] [AddCommGroup G]
    [AddCommGroup B] (E : G →+ ℝ) (μ : G →+ B) {w : ∀ k, ι k → ℝ} {deg : ∀ k, ι k → B}
    {deg' : ι' → B} {d : B}
    (F : (∀ k, ι k → NovikovSeries R (G × ℝ) (actionPeriod E))
      →ₘₗ[NovikovSeries R (G × ℝ) (actionPeriod E)]
      (ι' → NovikovSeries R (G × ℝ) (actionPeriod E)))
    (hdeg : ∀ (m : ∀ k, positiveLattice R (actionPeriod E) (w k)) (b : κ → B),
      (∀ k, (m k : ι k → NovikovSeries R (G × ℝ) (actionPeriod E)) ∈
        weightedGradeBy R (actionPeriod E) (actionDegree μ) (deg k) (b k)) →
      F (fun k => (m k : ι k → NovikovSeries R (G × ℝ) (actionPeriod E))) ∈
        weightedGradeBy R (actionPeriod E) (actionDegree μ) deg' ((∑ k, b k) + d))
    {b : κ → B} {v : ∀ k, ι k → NovikovSeries R (G × ℝ) (actionPeriod E)}
    (hv : ∀ k, v k ∈ weightedGradeBy R (actionPeriod E) (actionDegree μ) (deg k) (b k)) :
    F v ∈ weightedGradeBy R (actionPeriod E) (actionDegree μ) deg' ((∑ k, b k) + d) :=
  multilinearMap_mem_weightedGradeBy_of_positiveLattice
    (fun C => ⟨(0, C), by simp, by simp⟩) F hdeg hv

end FiltrationAndGrading

end MultilinearExtension

section TwoTermComplex

variable {R H G : Type*}

/-- Over a nontrivial coefficient ring, no positive-period monomial `t = e^g` (`N g > 0`) admits a
right-inverse `nonnegSubring R N`-linear endomorphism of `nonnegSubring R N`: the two-term complex
`nonnegSubring → nonnegSubring` with differential `t · -` is not contractible over
`nonnegSubring`. -/
theorem not_exists_linearMap_single_mul_eq_id [Ring R] [Nontrivial R] [AddMonoid H] {N : H →+ ℝ}
    {g : H} (hg : 0 < N g) :
    ¬ ∃ h : nonnegSubring R N →ₗ[nonnegSubring R N] nonnegSubring R N,
      ∀ x, (⟨single g 1, single_mem_nonnegSubring hg.le 1⟩ : nonnegSubring R N) * h x = x := by
  rintro ⟨h, hh⟩
  have h1 : (1 : nonnegSubring R N) ∈ posIdeal R N := by
    rw [← hh 1]
    exact Ideal.IsTwoSided.mul_mem_of_left (h 1) (single_mem_posIdeal hg 1)
  exact not_isUnit_of_mem_posIdeal h1 isUnit_one

/-- Over a nontrivial commutative coefficient ring, the homology `nonnegSubring R N ⧸ (e^g)` of the
two-term complex with differential `e^g` (`N g > 0`) is nontrivial. -/
theorem nontrivial_quotient_span_single_of_pos [CommRing R] [Nontrivial R] [AddCommGroup H]
    {N : H →+ ℝ} {g : H} (hg : 0 < N g) :
    Nontrivial (nonnegSubring R N ⧸
      Ideal.span ({⟨single g 1, single_mem_nonnegSubring hg.le 1⟩} : Set (nonnegSubring R N))) := by
  rw [Ideal.Quotient.nontrivial_iff]
  intro htop
  have hle : Ideal.span ({⟨single g 1, single_mem_nonnegSubring hg.le 1⟩} :
      Set (nonnegSubring R N)) ≤ posIdeal R N :=
    Ideal.span_le.2 (Set.singleton_subset_iff.2 (single_mem_posIdeal hg 1))
  exact posIdeal_ne_top R N (top_unique (htop ▸ hle))

/-- On any weighted lattice, composing `(shiftedLatticeEquivPositiveOfPeriod R w rfl).symm`
(multiplication by `e^(-g)`, filtration loss `N g`) with multiplication by `e^g` recovers the
inclusion `positiveLattice R N w → shiftedLattice R N w (N g)`. -/
theorem single_smul_symm_shiftedLatticeEquivPositiveOfPeriod [CommRing R] [AddCommGroup H]
    {N : H →+ ℝ} {ι : Type*} (w : ι → ℝ) {g : H} (hg : 0 ≤ N g)
    (x : positiveLattice R N w) :
    (((⟨single g 1, single_mem_nonnegSubring hg 1⟩ : nonnegSubring R N) •
        (shiftedLatticeEquivPositiveOfPeriod R w (r := N g) rfl).symm x :
          shiftedLattice R N w (N g)) : ι → NovikovSeries R H N) = x := by
  simp only [SetLike.val_smul, coe_shiftedLatticeEquivPositiveOfPeriod_symm, Subring.smul_def,
    smul_smul, single_mul_single, add_neg_cancel, mul_one, single_zero_one, one_smul]

/-- On any weighted lattice, applying `(shiftedLatticeEquivPositiveOfPeriod R w rfl).symm` after
multiplication by `e^g` recovers the inclusion `positiveLattice R N w → shiftedLattice R N w (N g)`.
-/
theorem symm_shiftedLatticeEquivPositiveOfPeriod_single_smul [CommRing R] [AddCommGroup H]
    {N : H →+ ℝ} {ι : Type*} (w : ι → ℝ) {g : H} (hg : 0 ≤ N g)
    (x : positiveLattice R N w) :
    ((shiftedLatticeEquivPositiveOfPeriod R w (r := N g) rfl).symm
        ((⟨single g 1, single_mem_nonnegSubring hg 1⟩ : nonnegSubring R N) • x) :
      ι → NovikovSeries R H N) = x := by
  simp only [coe_shiftedLatticeEquivPositiveOfPeriod_symm, SetLike.val_smul, Subring.smul_def,
    smul_smul, single_mul_single, neg_add_cancel, mul_one, single_zero_one, one_smul]

/-- Action-extension specialization: for any `A > 0`, `nonnegSubring R (actionPeriod E) ⧸ (T^A)` is
nontrivial, witnessing non-acyclicity of the two-term complex with differential `T^A` over
`nonnegSubring`. -/
theorem nontrivial_quotient_span_nonnegActionMonomial_of_pos [CommRing R] [Nontrivial R]
    [AddCommGroup G] (E : G →+ ℝ) {A : ℝ} (hA : 0 < A) :
    Nontrivial (nonnegSubring R (actionPeriod E) ⧸
      Ideal.span ({nonnegActionMonomial R E hA.le} : Set (nonnegSubring R (actionPeriod E)))) := by
  have hpos : 0 < actionPeriod E (0, A) := by simpa using hA
  have heq : nonnegActionMonomial R E hA.le =
      ⟨single (0, A) 1, single_mem_nonnegSubring hpos.le 1⟩ :=
    Subtype.ext ((coe_nonnegActionMonomial E hA.le).trans (actionMonomial_eq_single E A))
  rw [heq]
  exact nontrivial_quotient_span_single_of_pos hpos

/-- Action-extension specialization: for any `A > 0`, `T^A` admits no `nonnegSubring`-linear
contracting homotopy on `nonnegSubring R (actionPeriod E)`. -/
theorem not_exists_linearMap_nonnegActionMonomial_mul_eq_id [Ring R] [Nontrivial R] [AddMonoid G]
    (E : G →+ ℝ) {A : ℝ} (hA : 0 < A) :
    ¬ ∃ h : nonnegSubring R (actionPeriod E) →ₗ[nonnegSubring R (actionPeriod E)]
        nonnegSubring R (actionPeriod E),
      ∀ x, nonnegActionMonomial R E hA.le * h x = x := by
  have hpos : 0 < actionPeriod E (0, A) := by simpa using hA
  have heq : nonnegActionMonomial R E hA.le =
      ⟨single (0, A) 1, single_mem_nonnegSubring hpos.le 1⟩ :=
    Subtype.ext ((coe_nonnegActionMonomial E hA.le).trans (actionMonomial_eq_single E A))
  simp_rw [heq]
  exact not_exists_linearMap_single_mul_eq_id hpos

/-- Action-extension specialization: on any weighted lattice, composing
`(shiftedLatticeEquivPositiveAction R E w A).symm` (multiplication by `T^(-A)`, exact filtration
loss `A`) with multiplication by `T^A` recovers the inclusion into `shiftedLattice ... A`. -/
theorem nonnegActionMonomial_smul_symm_shiftedLatticeEquivPositiveAction [CommRing R]
    [AddCommGroup G] {ι : Type*} (E : G →+ ℝ) (w : ι → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (x : positiveLattice R (actionPeriod E) w) :
    ((nonnegActionMonomial R E hA • (shiftedLatticeEquivPositiveAction R E w A).symm x :
        shiftedLattice R (actionPeriod E) w A) :
      ι → NovikovSeries R (G × ℝ) (actionPeriod E)) = x := by
  simp only [SetLike.val_smul, coe_shiftedLatticeEquivPositiveAction_symm, Subring.smul_def,
    coe_nonnegActionMonomial, smul_smul, ← actionMonomial_add, add_neg_cancel, actionMonomial_zero,
    one_smul]

/-- Action-extension specialization: on any weighted lattice, applying
`(shiftedLatticeEquivPositiveAction R E w A).symm` after multiplication by `T^A` recovers the
inclusion into `shiftedLattice ... A`. -/
theorem symm_shiftedLatticeEquivPositiveAction_nonnegActionMonomial_smul [CommRing R]
    [AddCommGroup G] {ι : Type*} (E : G →+ ℝ) (w : ι → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (x : positiveLattice R (actionPeriod E) w) :
    ((shiftedLatticeEquivPositiveAction R E w A).symm (nonnegActionMonomial R E hA • x) :
      ι → NovikovSeries R (G × ℝ) (actionPeriod E)) = x := by
  simp only [coe_shiftedLatticeEquivPositiveAction_symm, SetLike.val_smul, Subring.smul_def,
    coe_nonnegActionMonomial, smul_smul, ← actionMonomial_add, neg_add_cancel, actionMonomial_zero,
    one_smul]

end TwoTermComplex

end NovikovSeries

end TauCeti
