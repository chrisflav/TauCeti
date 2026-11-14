/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Countable.Basic

/-!
# Row assemblies of labelled structures

Given a label type `I` and a relational component language `Lc`, a **row assembly** packages a
row-indexed matrix of `Lc`-structures `C : R → I → Type*` into a single relational structure over
`RowAssembly.lang I Lc`. Its carrier `RowAssembly.Carrier R C` is the disjoint union of one element
`Carrier.row r` for each row `r : R` and the elements `Carrier.pt r i x` of each labelled fiber
`C r i`.

The assembled language `RowAssembly.lang I Lc` has unary `Sym.row`, binary `Sym.own` relating each
fiber point to its owner row, unary `Sym.lab i` cutting out the points of label `i`, `Sym.lift S`
lifting each positive-arity relation `S` of `Lc` to tuples lying in a single fiber, and
`Sym.lift0 S i` reading each nullary relation `S` of `Lc` at the owner row so that empty fibers
retain their nullary atomic diagram.

Because `Sym.row`, `Sym.own`, and `Sym.lab` recover the sort and owner row of every element, an
isomorphism between two row assemblies decomposes uniquely into a bijection of rows `eR : R₁ ≃ R₂`
together with fiberwise `Lc`-isomorphisms `C₁ r i ≃[Lc] C₂ (eR r) i`.

## Main definitions

* `TauCeti.RowAssembly.Sym`, `TauCeti.RowAssembly.lang`: the relational vocabulary of a row
  assembly over labels `I` and component language `Lc`.
* `TauCeti.RowAssembly.Carrier`, `ownerRow`, `sort`: the assembled carrier, its owner-row map, and
  its label sort.
* `TauCeti.RowAssembly.equivOfFiberEquiv`: assemble an isomorphism from a row bijection and
  fiberwise component isomorphisms.
* `TauCeti.RowAssembly.rowEquivOfEquiv`, `TauCeti.RowAssembly.fiberEquivOfEquiv`: restrict an
  isomorphism of row assemblies to its induced row bijection and fiberwise component isomorphisms.

## Main results

* `TauCeti.RowAssembly.nonempty_equiv_iff`: two row assemblies over a relational component language
  are isomorphic if and only if some row bijection makes all corresponding labelled fibers
  isomorphic.

## References

* Adapted from `InfinitaryLogic/ModelTheory/FiberAssembly.lean` and
  `InfinitaryLogic/ModelTheory/FiberIsoAssembly.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0), generalized from nonempty-word labels in universe zero to an arbitrary label type
  and universe-polymorphic component language.
-/

public section

universe u v w uR uR' uC uC'

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language

/-! ### The assembled language -/

/-- The relation symbols of a row assembly over labels `I` and component language `Lc`:
rows (`row`), ownership of a fiber point by a row (`own`), fiber labels (`lab`), lifted positive
component relations (`lift`), and lifted nullary component relations (`lift0`) evaluated at the
owner row. -/
inductive Sym (I : Type w) (Lc : Language.{u, v}) : ℕ → Type (max v w)
  | row : Sym I Lc 1
  | own : Sym I Lc 2
  | lab (i : I) : Sym I Lc 1
  | lift {l : ℕ} (R : Lc.Relations (l + 1)) : Sym I Lc (l + 1)
  | lift0 (R : Lc.Relations 0) (i : I) : Sym I Lc 1

/-- The relational language of a row assembly over labels `I` and component language `Lc`.
It is an abbreviation so that relation symbols match directly by cases on `Sym I Lc`. -/
abbrev lang (I : Type w) (Lc : Language.{u, v}) : Language.{0, max v w} where
  Functions _ := PEmpty
  Relations := Sym I Lc

instance instIsRelational (I : Type w) (Lc : Language.{u, v}) : (lang I Lc).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty PEmpty)

/-- Countably many labels and countably many component relations at each arity yield countably many
assembled relations at each arity. -/
instance instCountableRelations (I : Type w) (Lc : Language.{u, v}) [Countable I]
    [∀ l, Countable (Lc.Relations l)] (n : ℕ) : Countable ((lang I Lc).Relations n) := by
  let enc : (k : ℕ) → Sym I Lc k →
      (Unit ⊕ Unit ⊕ I ⊕ (Lc.Relations 0 × I)) ⊕ Lc.Relations k
    | _, .row => .inl (.inl ())
    | _, .own => .inl (.inr (.inl ()))
    | _, .lab i => .inl (.inr (.inr (.inl i)))
    | _, .lift R => .inr R
    | _, .lift0 R i => .inl (.inr (.inr (.inr (R, i))))
  refine Function.Injective.countable (f := enc n) fun a b hab => ?_
  cases a <;> cases b <;> simp_all [enc]

/-! ### The assembled carrier and its structure -/

/-- The carrier of a row assembly: one row element `row r` for each `r : R`, together with the
labelled fiber points `pt r i x` for `x : C r i`. -/
inductive Carrier (R : Type uR) {I : Type w} (C : R → I → Type uC) : Type (max uR w uC)
  | row (r : R)
  | pt (r : R) (i : I) (x : C r i)

section CarrierAPI

variable {I : Type w} {R : Type uR} {C : R → I → Type uC}

/-- The owner row of an assembled element: `r` itself on `row r`, and the fiber's row on
`pt r i x`. -/
def ownerRow : Carrier R C → R
  | .row r => r
  | .pt r _ _ => r

@[simp]
theorem ownerRow_row (r : R) : ownerRow (Carrier.row r : Carrier R C) = r :=
  (rfl)

@[simp]
theorem ownerRow_pt (r : R) (i : I) (x : C r i) : ownerRow (Carrier.pt r i x) = r :=
  (rfl)

/-- The label sort of an assembled element: `none` on rows and `some i` on points of label `i`. -/
def sort : Carrier R C → Option I
  | .row _ => none
  | .pt _ i _ => some i

@[simp]
theorem sort_row (r : R) : sort (Carrier.row r : Carrier R C) = none :=
  (rfl)

@[simp]
theorem sort_pt (r : R) (i : I) (x : C r i) : sort (Carrier.pt r i x) = some i :=
  (rfl)

/-- Equality of row elements reduces to equality of rows. -/
theorem row_inj {r₁ r₂ : R} :
    (Carrier.row r₁ : Carrier R C) = .row r₂ ↔ r₁ = r₂ :=
  ⟨Carrier.row.inj, congrArg _⟩

/-- Within a fixed row and label fiber, `Carrier.pt r i` is injective as an iff. -/
theorem pt_inj_right {r : R} {i : I} {x y : C r i} :
    (Carrier.pt r i x : Carrier R C) = .pt r i y ↔ x = y :=
  ⟨fun h => eq_of_heq (Carrier.pt.inj h).2.2, congrArg _⟩

@[simp]
theorem row_ne_pt {r₁ r₂ : R} {i : I} {x : C r₂ i} :
    (Carrier.row r₁ : Carrier R C) ≠ .pt r₂ i x := by
  rintro ⟨⟩

@[simp]
theorem pt_ne_row {r₁ r₂ : R} {i : I} {x : C r₁ i} :
    (Carrier.pt r₁ i x : Carrier R C) ≠ .row r₂ := by
  rintro ⟨⟩

/-- An element of sort `none` is its own owner row. -/
theorem eq_row_of_sort_eq_none {z : Carrier R C} (h : sort z = none) :
    z = .row (ownerRow z) := by
  cases z with
  | row _ => rfl
  | pt _ _ _ => cases h

/-- An element with owner row `r` and sort `some i` comes from a point of the fiber `C r i`. -/
theorem exists_pt_of_sort_eq_some {z : Carrier R C} {r : R} {i : I}
    (hr : ownerRow z = r) (hs : sort z = some i) :
    ∃ x : C r i, z = .pt r i x := by
  cases z with
  | row _ => cases hs
  | pt r' i' x =>
    cases hr
    cases Option.some.inj hs
    exact ⟨x, rfl⟩

/-- Equivalence of `Carrier R C` with the disjoint union of `R` and the sigma type of all fibers. -/
def equivSumSigma : Carrier R C ≃ R ⊕ Σ (r : R) (i : I), C r i where
  toFun
    | .row r => .inl r
    | .pt r i x => .inr ⟨r, i, x⟩
  invFun
    | .inl r => .row r
    | .inr ⟨r, i, x⟩ => .pt r i x
  left_inv z := by cases z <;> rfl
  right_inv s := by rcases s with r | ⟨r, i, x⟩ <;> rfl

instance instCountableCarrier [Countable R] [Countable I] [∀ r i, Countable (C r i)] :
    Countable (Carrier R C) :=
  Countable.of_equiv _ equivSumSigma.symm

instance instInfiniteCarrier [Infinite R] : Infinite (Carrier R C) :=
  Infinite.of_injective (Carrier.row (C := C)) fun _ _ => Carrier.row.inj

end CarrierAPI

section Structure

variable {I : Type w} {Lc : Language.{u, v}} {R : Type uR} {C : R → I → Type uC}
  [∀ r i, Lc.Structure (C r i)]

/-- The canonical `(lang I Lc)`-structure on `Carrier R C`. -/
instance instStructure : (lang I Lc).Structure (Carrier R C) where
  funMap f _ := isEmptyElim f
  RelMap
    | .row, v => sort (v 0) = none
    | .own, v => (sort (v 0)).isSome ∧ sort (v 1) = none ∧ ownerRow (v 0) = ownerRow (v 1)
    | .lab i, v => sort (v 0) = some i
    | .lift S, v =>
        ∃ (r : R) (i : I) (w : Fin _ → C r i),
          (∀ k, v k = .pt r i (w k)) ∧ Structure.RelMap S w
    | .lift0 S i, v =>
        ∃ r : R, v 0 = .row r ∧ @Structure.RelMap Lc (C r i) _ 0 S Fin.elim0

@[simp]
theorem relMap_row_iff (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang I Lc) Sym.row v ↔ sort (v 0) = none := by
  rfl

/-- `Sym.row` holds on a singleton tuple iff its entry is a row element. -/
theorem relMap_row_iff_exists_row (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang I Lc) Sym.row v ↔ ∃ r : R, v 0 = .row r := by
  rw [relMap_row_iff]
  refine ⟨fun h => ⟨ownerRow (v 0), eq_row_of_sort_eq_none h⟩, ?_⟩
  rintro ⟨r, hr⟩
  simp [hr]

@[simp]
theorem relMap_own_iff (v : Fin 2 → Carrier R C) :
    Structure.RelMap (L := lang I Lc) Sym.own v ↔
      (sort (v 0)).isSome ∧ sort (v 1) = none ∧ ownerRow (v 0) = ownerRow (v 1) := by
  rfl

/-- `Sym.own` holds on a pair iff its first entry is a fiber point and its second entry is that
point's owner row. -/
theorem relMap_own_iff_exists_pt (v : Fin 2 → Carrier R C) :
    Structure.RelMap (L := lang I Lc) Sym.own v ↔
      ∃ (r : R) (i : I) (x : C r i), v 0 = .pt r i x ∧ v 1 = .row r := by
  rw [relMap_own_iff]
  constructor
  · rintro ⟨hs0, hs1, hown⟩
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs0
    obtain ⟨x, hx⟩ := exists_pt_of_sort_eq_some hown hi
    exact ⟨ownerRow (v 1), i, x, hx, eq_row_of_sort_eq_none hs1⟩
  · rintro ⟨r, i, x, hv0, hv1⟩
    simp [hv0, hv1]

@[simp]
theorem relMap_lab_iff (i : I) (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang I Lc) (Sym.lab i) v ↔ sort (v 0) = some i := by
  rfl

/-- `Sym.lab i` holds on a singleton tuple iff its entry is a point of some `i`-labelled fiber. -/
theorem relMap_lab_iff_exists_pt (i : I) (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang I Lc) (Sym.lab i) v ↔ ∃ (r : R) (x : C r i), v 0 = .pt r i x := by
  rw [relMap_lab_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := exists_pt_of_sort_eq_some rfl h
    exact ⟨ownerRow (v 0), x, hx⟩
  · rintro ⟨r, x, hv⟩
    simp [hv]

/-- `Sym.lift S` holds on a tuple iff all entries come from a single labelled fiber where `S`
holds. -/
theorem relMap_lift_iff {l : ℕ} (S : Lc.Relations (l + 1)) (v : Fin (l + 1) → Carrier R C) :
    Structure.RelMap (L := lang I Lc) (Sym.lift S) v ↔
      ∃ (r : R) (i : I) (w : Fin (l + 1) → C r i),
        (∀ k, v k = .pt r i (w k)) ∧ Structure.RelMap S w := by
  rfl

/-- `Sym.lift0 S i` holds on a singleton tuple iff its entry is a row element whose `i`-labelled
fiber satisfies the nullary relation `S`. -/
theorem relMap_lift0_iff (S : Lc.Relations 0) (i : I) (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang I Lc) (Sym.lift0 S i) v ↔
      ∃ r : R, v 0 = .row r ∧ @Structure.RelMap Lc (C r i) _ 0 S Fin.elim0 := by
  rfl

@[simp]
theorem relMap_lift_pt {l : ℕ} (S : Lc.Relations (l + 1)) (r : R) (i : I)
    (w : Fin (l + 1) → C r i) :
    Structure.RelMap (L := lang I Lc) (Sym.lift S) (fun k => Carrier.pt (C := C) r i (w k)) ↔
      Structure.RelMap S w := by
  rw [relMap_lift_iff]
  refine ⟨?_, fun hS => ⟨r, i, w, fun _ => rfl, hS⟩⟩
  rintro ⟨r', i', w', hw', hS⟩
  have hr : r = r' := by simpa using congrArg ownerRow (hw' 0)
  subst hr
  have hi : i = i' := Option.some.inj (by simpa using congrArg sort (hw' 0))
  subst hi
  have hw : w = w' := funext fun k => pt_inj_right.mp (hw' k)
  exact hw ▸ hS

/-- At a row singleton `![.row r]`, `Sym.lift0 S i` evaluates the nullary relation `S` in the fiber
`C r i`. -/
theorem relMap_lift0_of_eq_row (S : Lc.Relations 0) (i : I) {v : Fin 1 → Carrier R C} {r : R}
    (hv : v 0 = .row r) :
    Structure.RelMap (L := lang I Lc) (Sym.lift0 S i) v ↔
      @Structure.RelMap Lc (C r i) _ 0 S Fin.elim0 := by
  simp [relMap_lift0_iff, hv]

end Structure

/-! ### Isomorphism assembly and restriction -/

section Isomorphism

variable {I : Type w} {Lc : Language.{u, v}}
  {R₁ : Type uR} {R₂ : Type uR'}
  {C₁ : R₁ → I → Type uC} {C₂ : R₂ → I → Type uC'}
  [∀ r i, Lc.Structure (C₁ r i)] [∀ r i, Lc.Structure (C₂ r i)]

/-- Assemble a carrier bijection from a bijection of rows `eR : R₁ ≃ R₂` and fiberwise bijections
`eC r i : C₁ r i ≃ C₂ (eR r) i`. -/
def carrierEquivOfFiberEquiv (eR : R₁ ≃ R₂) (eC : ∀ r i, C₁ r i ≃ C₂ (eR r) i) :
    Carrier R₁ C₁ ≃ Carrier R₂ C₂ :=
  equivSumSigma.trans <|
    (eR.sumCongr (Equiv.sigmaCongr eR fun r =>
      Equiv.sigmaCongrRight fun i => eC r i)).trans equivSumSigma.symm

@[simp]
theorem carrierEquivOfFiberEquiv_row (eR : R₁ ≃ R₂) (eC : ∀ r i, C₁ r i ≃ C₂ (eR r) i)
    (r : R₁) :
    carrierEquivOfFiberEquiv eR eC (.row r) = .row (eR r) := by
  rfl

@[simp]
theorem carrierEquivOfFiberEquiv_pt (eR : R₁ ≃ R₂) (eC : ∀ r i, C₁ r i ≃ C₂ (eR r) i)
    (r : R₁) (i : I) (x : C₁ r i) :
    carrierEquivOfFiberEquiv eR eC (.pt r i x) = .pt (eR r) i (eC r i x) := by
  rfl

@[simp]
theorem sort_carrierEquivOfFiberEquiv (eR : R₁ ≃ R₂) (eC : ∀ r i, C₁ r i ≃ C₂ (eR r) i)
    (z : Carrier R₁ C₁) :
    sort (carrierEquivOfFiberEquiv eR eC z) = sort z := by
  cases z <;> rfl

@[simp]
theorem ownerRow_carrierEquivOfFiberEquiv (eR : R₁ ≃ R₂) (eC : ∀ r i, C₁ r i ≃ C₂ (eR r) i)
    (z : Carrier R₁ C₁) :
    ownerRow (carrierEquivOfFiberEquiv eR eC z) = eR (ownerRow z) := by
  cases z <;> rfl

private theorem map_rel_lift_carrierEquivOfFiberEquiv {l : ℕ} (eR : R₁ ≃ R₂)
    (eC : ∀ r i, C₁ r i ≃[Lc] C₂ (eR r) i) (S : Lc.Relations (l + 1))
    (v : Fin (l + 1) → Carrier R₁ C₁) :
    Structure.RelMap (L := lang I Lc) (Sym.lift S)
        (carrierEquivOfFiberEquiv eR (fun r i => (eC r i).toEquiv) ∘ v) ↔
      Structure.RelMap (L := lang I Lc) (Sym.lift S) v := by
  simp only [relMap_lift_iff, Function.comp_apply]
  constructor
  · rintro ⟨r₂, i, w₂, hw, hS⟩
    obtain ⟨r, rfl⟩ := eR.surjective r₂
    have hk (k : Fin _) : ∃ x : C₁ r i, v k = .pt r i x ∧ eC r i x = w₂ k := by
      have hk0 := hw k
      cases hv : v k with
      | row r' => simp [hv] at hk0
      | pt r' i' x =>
        rw [hv, carrierEquivOfFiberEquiv_pt] at hk0
        have hown_k : eR r' = eR r := by simpa using congrArg ownerRow hk0
        cases eR.injective hown_k
        have hsort_k : some i' = some i := by simpa using congrArg sort hk0
        cases Option.some.inj hsort_k
        exact ⟨x, rfl, pt_inj_right.mp hk0⟩
    choose w₁ hw₁ hw₂ using hk
    have hw_eq : eC r i ∘ w₁ = w₂ := funext hw₂
    exact ⟨r, i, w₁, hw₁, (eC r i).map_rel S w₁ |>.mp (hw_eq ▸ hS)⟩
  · rintro ⟨r, i, w₁, hw, hS⟩
    refine ⟨eR r, i, eC r i ∘ w₁, fun k => ?_, (eC r i).map_rel S w₁ |>.mpr hS⟩
    simp only [hw k, carrierEquivOfFiberEquiv_pt]
    rfl

/-- Assemble an isomorphism of row assemblies from a bijection of rows `eR : R₁ ≃ R₂` and
fiberwise `Lc`-isomorphisms `eC r i : C₁ r i ≃[Lc] C₂ (eR r) i`. -/
def equivOfFiberEquiv (eR : R₁ ≃ R₂) (eC : ∀ r i, C₁ r i ≃[Lc] C₂ (eR r) i) :
    Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂ where
  toEquiv := carrierEquivOfFiberEquiv eR fun r i => (eC r i).toEquiv
  map_fun' {n} f := isEmptyElim f
  map_rel' {n} R v := by
    simp only [Equiv.toFun_as_coe]
    cases R with
    | row => simp
    | own => simp [eR.injective.eq_iff]
    | lab i => simp
    | lift S => exact map_rel_lift_carrierEquivOfFiberEquiv eR eC S v
    | lift0 S i =>
      simp only [relMap_lift0_iff, Function.comp_apply]
      constructor
      · rintro ⟨r₂, hr, hS⟩
        obtain ⟨r, rfl⟩ := eR.surjective r₂
        cases hv : v 0 with
        | row r' =>
          rw [hv, carrierEquivOfFiberEquiv_row, row_inj] at hr
          cases eR.injective hr
          have h0 : eC r i ∘ (Fin.elim0 : Fin 0 → C₁ r i) = Fin.elim0 := Subsingleton.elim _ _
          exact ⟨r, rfl, ((eC r i).map_rel S Fin.elim0).mp (h0 ▸ hS)⟩
        | pt _ _ _ => simp [hv] at hr
      · rintro ⟨r, hr, hS⟩
        have h0 : eC r i ∘ (Fin.elim0 : Fin 0 → C₁ r i) = Fin.elim0 := Subsingleton.elim _ _
        exact ⟨eR r, by simp [hr], h0 ▸ ((eC r i).map_rel S Fin.elim0).mpr hS⟩

@[simp]
theorem equivOfFiberEquiv_row (eR : R₁ ≃ R₂) (eC : ∀ r i, C₁ r i ≃[Lc] C₂ (eR r) i) (r : R₁) :
    equivOfFiberEquiv eR eC (.row r) = .row (eR r) := by
  rfl

@[simp]
theorem equivOfFiberEquiv_pt (eR : R₁ ≃ R₂) (eC : ∀ r i, C₁ r i ≃[Lc] C₂ (eR r) i)
    (r : R₁) (i : I) (x : C₁ r i) :
    equivOfFiberEquiv eR eC (.pt r i x) = .pt (eR r) i (eC r i x) := by
  rfl

/-- Every isomorphism of row assemblies preserves the label sort. -/
@[simp]
theorem sort_equiv (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) (z : Carrier R₁ C₁) :
    sort (Φ z) = sort z := by
  cases z with
  | row r =>
    exact (Φ.map_rel Sym.row ![Carrier.row r]).mpr rfl
  | pt r i x =>
    exact (Φ.map_rel (Sym.lab i) ![Carrier.pt r i x]).mpr rfl

/-- The bijection of rows `R₁ ≃ R₂` induced by an isomorphism of row assemblies. -/
def rowEquivOfEquiv (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) : R₁ ≃ R₂ where
  toFun r := ownerRow (Φ (.row r))
  invFun r' := ownerRow (Φ.symm (.row r'))
  left_inv r := by
    have h : Φ (.row r) = .row (ownerRow (Φ (.row r))) :=
      eq_row_of_sort_eq_none (by simp)
    have h' := congrArg (ownerRow ∘ Φ.symm) h
    simpa using h'.symm
  right_inv r' := by
    have h : Φ.symm (.row r') = .row (ownerRow (Φ.symm (.row r'))) :=
      eq_row_of_sort_eq_none (by simp)
    have h' := congrArg (ownerRow ∘ Φ) h
    simpa using h'.symm

/-- An isomorphism of row assemblies maps `.row r` to `.row (rowEquivOfEquiv Φ r)`. -/
theorem apply_row_eq_rowEquivOfEquiv (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) (r : R₁) :
    Φ (.row r) = .row (rowEquivOfEquiv Φ r) :=
  eq_row_of_sort_eq_none (by simp)

@[simp]
theorem rowEquivOfEquiv_symm (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) :
    (rowEquivOfEquiv Φ).symm = rowEquivOfEquiv Φ.symm := by
  ext r
  rfl

@[simp]
theorem rowEquivOfEquiv_equivOfFiberEquiv (eR : R₁ ≃ R₂) (eC : ∀ r i, C₁ r i ≃[Lc] C₂ (eR r) i) :
    rowEquivOfEquiv (equivOfFiberEquiv eR eC) = eR := by
  ext r
  rfl

/-- An isomorphism of row assemblies intertwines `ownerRow` with `rowEquivOfEquiv Φ`. -/
@[simp]
theorem ownerRow_equiv (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) (z : Carrier R₁ C₁) :
    ownerRow (Φ z) = rowEquivOfEquiv Φ (ownerRow z) := by
  cases z with
  | row r => rfl
  | pt r i x =>
    have hown : Structure.RelMap (L := lang I Lc) Sym.own ![Φ (.pt r i x), Φ (.row r)] :=
      (Φ.map_rel Sym.own ![Carrier.pt r i x, Carrier.row r]).mpr ⟨rfl, rfl, rfl⟩
    exact hown.2.2

private noncomputable def fiberFun
    (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) (r : R₁) (i : I) (x : C₁ r i) :
    C₂ (rowEquivOfEquiv Φ r) i :=
  (exists_pt_of_sort_eq_some (z := Φ (.pt r i x)) (by simp) (by simp)).choose

private theorem apply_pt_eq_fiberFun
    (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) (r : R₁) (i : I) (x : C₁ r i) :
    Φ (.pt r i x) = .pt (rowEquivOfEquiv Φ r) i (fiberFun Φ r i x) :=
  (exists_pt_of_sort_eq_some (z := Φ (.pt r i x)) (by simp) (by simp)).choose_spec

private theorem bijective_fiberFun
    (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) (r : R₁) (i : I) :
    Function.Bijective (fiberFun Φ r i) := by
  refine ⟨fun x₁ x₂ h => ?_, fun y => ?_⟩
  · have hΦ : Φ (.pt r i x₁) = Φ (.pt r i x₂) := by
      rw [apply_pt_eq_fiberFun, apply_pt_eq_fiberFun, h]
    exact pt_inj_right.mp (Φ.injective hΦ)
  · let z := Φ.symm (.pt (rowEquivOfEquiv Φ r) i y)
    have hz_apply : Φ z = .pt (rowEquivOfEquiv Φ r) i y := Φ.apply_symm_apply _
    have hz_own : ownerRow z = r :=
      (rowEquivOfEquiv Φ).injective (by simpa [hz_apply] using (ownerRow_equiv Φ z).symm)
    have hz_sort : sort z = some i := by simpa [hz_apply] using (sort_equiv Φ z).symm
    obtain ⟨x, hx⟩ := exists_pt_of_sort_eq_some hz_own hz_sort
    refine ⟨x, pt_inj_right.mp ?_⟩
    rw [← apply_pt_eq_fiberFun, ← hx, hz_apply]

/-- The fiberwise `Lc`-isomorphism `C₁ r i ≃[Lc] C₂ (rowEquivOfEquiv Φ r) i` induced by an
isomorphism `Φ` of row assemblies, when `Lc` is relational. -/
noncomputable def fiberEquivOfEquiv [Lc.IsRelational]
    (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) (r : R₁) (i : I) :
    C₁ r i ≃[Lc] C₂ (rowEquivOfEquiv Φ r) i where
  toEquiv := Equiv.ofBijective (fiberFun Φ r i) (bijective_fiberFun Φ r i)
  map_fun' {n} fn := isEmptyElim fn
  map_rel' {k} S w := by
    simp only [Equiv.toFun_as_coe, Equiv.coe_ofBijective]
    cases k with
    | zero =>
      have h0 := Φ.map_rel (Sym.lift0 S i) ![Carrier.row r]
      rw [relMap_lift0_of_eq_row S i (r := rowEquivOfEquiv Φ r) (apply_row_eq_rowEquivOfEquiv Φ r),
        relMap_lift0_of_eq_row S i (r := r) rfl] at h0
      rwa [Subsingleton.elim (fiberFun Φ r i ∘ w) Fin.elim0, Subsingleton.elim w Fin.elim0]
    | succ l =>
      have hl := Φ.map_rel (Sym.lift S) (fun m => .pt r i (w m))
      have hcomp : Φ ∘ (fun m => Carrier.pt r i (w m)) =
          fun m => .pt (rowEquivOfEquiv Φ r) i ((fiberFun Φ r i ∘ w) m) :=
        funext fun m => apply_pt_eq_fiberFun Φ r i (w m)
      rwa [hcomp, relMap_lift_pt, relMap_lift_pt] at hl

/-- An isomorphism of row assemblies over a relational component language maps `.pt r i x` to
`.pt (rowEquivOfEquiv Φ r) i (fiberEquivOfEquiv Φ r i x)`. -/
theorem apply_pt_eq_fiberEquivOfEquiv [Lc.IsRelational]
    (Φ : Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) (r : R₁) (i : I) (x : C₁ r i) :
    Φ (.pt r i x) = .pt (rowEquivOfEquiv Φ r) i (fiberEquivOfEquiv Φ r i x) :=
  apply_pt_eq_fiberFun Φ r i x

/-- Two row assemblies over a relational component language are isomorphic if and only if some
bijection of rows makes all corresponding labelled fibers isomorphic. -/
theorem nonempty_equiv_iff [Lc.IsRelational] :
    Nonempty (Carrier R₁ C₁ ≃[lang I Lc] Carrier R₂ C₂) ↔
      ∃ eR : R₁ ≃ R₂, ∀ r i, Nonempty (C₁ r i ≃[Lc] C₂ (eR r) i) :=
  ⟨fun ⟨Φ⟩ => ⟨rowEquivOfEquiv Φ, fun r i => ⟨fiberEquivOfEquiv Φ r i⟩⟩,
    fun ⟨eR, hC⟩ => ⟨equivOfFiberEquiv eR fun r i => (hC r i).some⟩⟩

end Isomorphism

end TauCeti.RowAssembly
