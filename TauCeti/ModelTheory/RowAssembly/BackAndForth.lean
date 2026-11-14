/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RowAssembly.Basic
public import TauCeti.ModelTheory.BackAndForth.Equivalence

/-!
# Back-and-forth equivalence in row assemblies

Back-and-forth equivalence in a row assembly interacts cleanly with its labelled fibers:

1. **Owner-row extension** (`bfEquiv_append_ownerRow`): from `BFEquiv (α + n) n a b` in the
   assembled structure, `n` forth steps append the owner rows `.row (ownerRow (a k))` on the left,
   and `Sym.row` together with `Sym.own` forces their partners on the right to be the corresponding
   owner rows `.row (ownerRow (b k))` at depth `α`.
2. **Pointed fiber restriction** (`bfEquiv_fiber_of_row_eq`, `bfEquiv_elim0_fiber_of_row_eq`):
   once a tuple index holds matching rows `.row r₁` and `.row r₂`, `BFEquiv` at depth `α` in the
   assembly restricts to `BFEquiv` at depth `α` between every pair of corresponding labelled fibers
   `C₁ r₁ i` and `C₂ r₂ i`, including on empty tuples.
3. **Back-and-forth assembly** (`bfEquiv_of_fiber_bfEquiv`, `bfEquiv_elim0_of_fiber_bfEquiv`,
   `bfEquiv_singleton_row_of_fiber_bfEquiv`): a bijection of rows `eR : R₁ ≃ R₂` whose paired
   fibers agree at back-and-forth depth `α` lifts to `BFEquiv` at depth `α` in the assembled
   structures.

## References

* Adapted from `InfinitaryLogic/ModelTheory/FiberAssembly.lean` and
  `InfinitaryLogic/ModelTheory/FiberIsoAssembly.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0), generalized to arbitrary ordinal universes, arbitrary label types, and relational
  component languages without `Fintype` or `DecidableEq` hypotheses.
-/

public section

universe u v w uR uR' uC uC' o

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language

variable {I : Type w} {Lc : Language.{u, v}}
  {R₁ : Type uR} {R₂ : Type uR'}
  {C₁ : R₁ → I → Type uC} {C₂ : R₂ → I → Type uC'}
  [∀ r i, Lc.Structure (C₁ r i)] [∀ r i, Lc.Structure (C₂ r i)]

/-! ### Atomic-type preservation of sorts and owner rows -/

/-- Atomic-type agreement in a row assembly preserves the label sort of every entry. -/
theorem sort_eq_of_sameAtomicType {n : ℕ} {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : SameAtomicType (L := lang I Lc) a b) (k : Fin n) :
    sort (a k) = sort (b k) := by
  cases hs : sort (a k) with
  | none =>
    exact ((h.rel_iff Sym.row ![k]).mp hs).symm
  | some i =>
    exact ((h.rel_iff (Sym.lab i) ![k]).mp hs).symm

/-- When position `p` holds `.row r₁` in `a` and `.row r₂` in `b`, atomic-type agreement identifies
the entries of `a` owned by `r₁` with the entries of `b` owned by `r₂`. -/
theorem ownerRow_eq_iff_of_sameAtomicType {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : SameAtomicType (L := lang I Lc) a b) {p : Fin n} {r₁ : R₁} {r₂ : R₂}
    (ha : a p = .row r₁) (hb : b p = .row r₂) (k : Fin n) :
    ownerRow (a k) = r₁ ↔ ownerRow (b k) = r₂ := by
  cases hak : a k with
  | row r' =>
    have hsb : sort (b k) = none := by
      simpa [hak] using (sort_eq_of_sameAtomicType h k).symm
    have hbk : b k = .row (ownerRow (b k)) := eq_row_of_sort_eq_none hsb
    have heq := h.eq_iff k p
    rw [hak, ha, row_inj, hbk, hb, row_inj] at heq
    simpa [hak] using heq
  | pt r' i x =>
    have hsb : (sort (b k)).isSome := by
      rw [← sort_eq_of_sameAtomicType h k, hak, sort_pt]
      rfl
    have hown := h.rel_iff Sym.own ![k, p]
    simpa [hak, ha, hb, hsb] using hown

/-! ### Owner-row extension and pointed fiber restriction -/

/-- Appending the owner rows of an `n`-tuple on the left and taking `n` forth steps matches them
with the owner rows of the partner tuple on the right. -/
theorem bfEquiv_append_ownerRow {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : BFEquiv (L := lang I Lc) (α + n) n a b) :
    BFEquiv (L := lang I Lc) α (n + n)
      (Fin.append a fun k => .row (ownerRow (a k)))
      (Fin.append b fun k => .row (ownerRow (b k))) := by
  obtain ⟨y, hy⟩ := BFEquiv.exists_bfEquiv_append n h (fun k => .row (ownerRow (a k)))
  have h0 := hy.sameAtomicType
  suffices hy_eq : y = fun k => .row (ownerRow (b k)) by rwa [← hy_eq]
  funext k
  have hpa : Fin.append a (fun j => Carrier.row (ownerRow (a j))) (Fin.natAdd n k) =
      .row (ownerRow (a k)) := Fin.append_right _ _ k
  have hpb : Fin.append b y (Fin.natAdd n k) = y k := Fin.append_right _ _ k
  have hsort : sort (y k) = none := by
    have hs := (sort_eq_of_sameAtomicType h0 (Fin.natAdd n k)).symm
    rwa [hpa, hpb, sort_row] at hs
  have hyk : y k = .row (ownerRow (y k)) := eq_row_of_sort_eq_none hsort
  have hown := ownerRow_eq_iff_of_sameAtomicType h0 (p := Fin.natAdd n k)
    (r₁ := ownerRow (a k)) (r₂ := ownerRow (y k)) hpa (hpb.trans hyk) (Fin.castAdd n k)
  simp only [Fin.append_left, true_iff] at hown
  exact hyk.trans (congrArg Carrier.row hown.symm)

private theorem forth_fiber_of_row_eq {n m : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    {P : (k : ℕ) → (Fin k → Carrier R₁ C₁) → (Fin k → Carrier R₂ C₂) → Prop}
    (hP0 : ∀ {k} {u : Fin k → Carrier R₁ C₁} {v : Fin k → Carrier R₂ C₂},
      P k u v → SameAtomicType (L := lang I Lc) u v)
    (hforth : ∀ z : Carrier R₁ C₁, ∃ w : Carrier R₂ C₂, P (n + 1) (Fin.snoc a z) (Fin.snoc b w))
    {p : Fin n} {r₁ : R₁} {r₂ : R₂} (ha : a p = .row r₁) (hb : b p = .row r₂)
    (i : I) {g : Fin m → Fin n} {x : Fin m → C₁ r₁ i} {y : Fin m → C₂ r₂ i}
    (hx : ∀ k, a (g k) = .pt r₁ i (x k)) (hy : ∀ k, b (g k) = .pt r₂ i (y k))
    (u : C₁ r₁ i) :
    ∃ (v : C₂ r₂ i) (g' : Fin (m + 1) → Fin (n + 1)),
      P (n + 1) (Fin.snoc a (.pt r₁ i u)) (Fin.snoc b (.pt r₂ i v)) ∧
      (Fin.snoc a (.pt r₁ i u) : Fin (n + 1) → Carrier R₁ C₁) p.castSucc = .row r₁ ∧
      (Fin.snoc b (.pt r₂ i v) : Fin (n + 1) → Carrier R₂ C₂) p.castSucc = .row r₂ ∧
      (∀ k, (Fin.snoc a (.pt r₁ i u) : Fin (n + 1) → Carrier R₁ C₁) (g' k) =
        .pt r₁ i ((Fin.snoc x u : Fin (m + 1) → C₁ r₁ i) k)) ∧
      (∀ k, (Fin.snoc b (.pt r₂ i v) : Fin (n + 1) → Carrier R₂ C₂) (g' k) =
        .pt r₂ i ((Fin.snoc y v : Fin (m + 1) → C₂ r₂ i) k)) := by
  obtain ⟨w, hw⟩ := hforth (.pt r₁ i u)
  have h0 := hP0 hw
  have hsort : sort w = some i := by
    have := sort_eq_of_sameAtomicType h0 (Fin.last n)
    simpa using this.symm
  have hown : ownerRow w = r₂ := by
    have := ownerRow_eq_iff_of_sameAtomicType h0 (p := p.castSucc)
      (r₁ := r₁) (r₂ := r₂) (by simp [ha]) (by simp [hb]) (Fin.last n)
    simpa using this
  obtain ⟨v, rfl⟩ := exists_pt_of_sort_eq_some hown hsort
  refine ⟨v, Fin.snoc (Fin.castSucc ∘ g) (Fin.last n), hw, by simp [ha], by simp [hb], ?_, ?_⟩
  · exact fun k => Fin.lastCases (by simp) (fun j => by simp [hx j]) k
  · exact fun k => Fin.lastCases (by simp) (fun j => by simp [hy j]) k

/-- **Pointed fiber restriction.** When index `p` holds `.row r₁` in `a` and `.row r₂` in `b`,
back-and-forth equivalence of `a` and `b` at depth `α` in the row assembly restricts to
back-and-forth equivalence at depth `α` of any subtuples `x` in `C₁ r₁ i` and `y` in `C₂ r₂ i`
sitting at matching indices `g k`. -/
theorem bfEquiv_fiber_of_row_eq [Lc.IsRelational] {α : Ordinal.{o}} {n m : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : BFEquiv (L := lang I Lc) α n a b)
    {p : Fin n} {r₁ : R₁} {r₂ : R₂} (ha : a p = .row r₁) (hb : b p = .row r₂)
    (i : I) {g : Fin m → Fin n} {x : Fin m → C₁ r₁ i} {y : Fin m → C₂ r₂ i}
    (hx : ∀ k, a (g k) = .pt r₁ i (x k)) (hy : ∀ k, b (g k) = .pt r₂ i (y k)) :
    BFEquiv (L := Lc) α m x y := by
  induction α using Ordinal.limitRecOn generalizing n m with
  | zero =>
    have h0 := BFEquiv.zero.mp h
    refine BFEquiv.zero.mpr ((sameAtomicType_iff x y).mpr ⟨fun k₁ k₂ => ?_, fun {l} S f => ?_⟩)
    · have heq := h0.eq_iff (g k₁) (g k₂)
      rwa [hx k₁, hx k₂, pt_inj_right, hy k₁, hy k₂, pt_inj_right] at heq
    · cases l with
      | zero =>
        have hrel := h0.rel_iff (Sym.lift0 S i) (fun _ => p)
        rw [relMap_lift0_of_eq_row S i ha, relMap_lift0_of_eq_row S i hb] at hrel
        rwa [Subsingleton.elim (x ∘ f) Fin.elim0, Subsingleton.elim (y ∘ f) Fin.elim0]
      | succ l =>
        have hrel := h0.rel_iff (Sym.lift S) (g ∘ f)
        have hax : a ∘ (g ∘ f) = fun q => .pt r₁ i ((x ∘ f) q) := funext fun q => hx (f q)
        have hby : b ∘ (g ∘ f) = fun q => .pt r₂ i ((y ∘ f) q) := funext fun q => hy (f q)
        rwa [hax, hby, relMap_lift_pt, relMap_lift_pt] at hrel
  | add_one α ih =>
    obtain ⟨hα, hforth, hback⟩ := (BFEquiv.add_one α a b).mp h
    refine (BFEquiv.add_one α x y).mpr ⟨ih hα ha hb hx hy, fun u => ?_, fun v => ?_⟩
    · obtain ⟨v, g', hw, ha', hb', hx', hy'⟩ :=
        forth_fiber_of_row_eq BFEquiv.sameAtomicType hforth ha hb i hx hy u
      exact ⟨v, ih hw ha' hb' hx' hy'⟩
    · have hback' : ∀ w : Carrier R₂ C₂, ∃ z : Carrier R₁ C₁,
          BFEquiv (L := lang I Lc) α (n + 1) (Fin.snoc b w) (Fin.snoc a z) := fun w => by
        obtain ⟨z, hz⟩ := hback w
        exact ⟨z, hz.symm⟩
      obtain ⟨u, g', hw, hb', ha', hy', hx'⟩ :=
        forth_fiber_of_row_eq BFEquiv.sameAtomicType hback' hb ha i hy hx v
      exact ⟨u, ih hw.symm ha' hb' hx' hy'⟩
  | limit α hlim ih =>
    exact (BFEquiv.limit hlim x y).mpr fun β hβ =>
      ih β hβ ((BFEquiv.limit hlim a b).mp h β hβ) ha hb hx hy

/-- When index `p` holds `.row r₁` in `a` and `.row r₂` in `b`, back-and-forth equivalence of `a`
and `b` at depth `α` in the row assembly implies empty-tuple back-and-forth equivalence at depth
`α` between `C₁ r₁ i` and `C₂ r₂ i` for every label `i`. -/
theorem bfEquiv_elim0_fiber_of_row_eq [Lc.IsRelational] {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : BFEquiv (L := lang I Lc) α n a b)
    {p : Fin n} {r₁ : R₁} {r₂ : R₂} (ha : a p = .row r₁) (hb : b p = .row r₂) (i : I) :
    BFEquiv (L := Lc) α 0 (Fin.elim0 : Fin 0 → C₁ r₁ i) (Fin.elim0 : Fin 0 → C₂ r₂ i) :=
  bfEquiv_fiber_of_row_eq h ha hb i (g := Fin.elim0) (fun k => k.elim0) (fun k => k.elim0)

/-! ### Assembling back-and-forth equivalence from fiberwise equivalence -/

/-- Fiberwise witness that `a` and `b` match at depth `α` along a row bijection `eR : R₁ ≃ R₂`:
sorts agree, owner rows correspond under `eR`, and for every paired fiber `(r₁, r₂)` with
`eR r₁ = r₂` and label `i`, some `α`-equivalent component tuples `x` and `y` cover all entries of
`a` and `b` lying in that fiber. -/
structure FiberTupleMatch [Lc.IsRelational] (eR : R₁ ≃ R₂) (α : Ordinal.{o}) {n : ℕ}
    (a : Fin n → Carrier R₁ C₁) (b : Fin n → Carrier R₂ C₂) : Prop where
  /-- Corresponding entries have equal label sorts. -/
  sort_eq : ∀ k, sort (a k) = sort (b k)
  /-- Owner rows of corresponding entries match along `eR`. -/
  ownerRow_eq : ∀ k, eR (ownerRow (a k)) = ownerRow (b k)
  /-- Every paired fiber has `α`-equivalent component tuples covering the entries in that fiber. -/
  exists_fiber_bfEquiv : ∀ (r₁ : R₁) (r₂ : R₂), eR r₁ = r₂ → ∀ i : I,
    ∃ (d : ℕ) (x : Fin d → C₁ r₁ i) (y : Fin d → C₂ r₂ i),
      BFEquiv (L := Lc) α d x y ∧
      ∀ k, ownerRow (a k) = r₁ → sort (a k) = some i →
        ∃ m : Fin d, a k = .pt r₁ i (x m) ∧ b k = .pt r₂ i (y m)

/-- Symmetry of `FiberTupleMatch` along `eR.symm`. -/
theorem FiberTupleMatch.symm [Lc.IsRelational] {eR : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : FiberTupleMatch (Lc := Lc) eR α a b) :
    FiberTupleMatch (Lc := Lc) eR.symm α b a := by
  obtain ⟨hsort, hown, hfib⟩ := h
  refine ⟨fun k => (hsort k).symm, fun k => eR.symm_apply_eq.mpr (hown k).symm, ?_⟩
  intro r₂ r₁ hr i
  obtain ⟨d, x, y, hxy, hmem⟩ := hfib r₁ r₂ (eR.symm_apply_eq.mp hr).symm i
  refine ⟨d, y, x, hxy.symm, fun k hbk hsb => ?_⟩
  have hak : ownerRow (a k) = r₁ :=
    eR.injective ((hown k).trans (hbk.trans (eR.symm_apply_eq.mp hr)))
  have hsa : sort (a k) = some i := (hsort k).trans hsb
  obtain ⟨m, ha, hb⟩ := hmem k hak hsa
  exact ⟨m, hb, ha⟩

/-- Monotonicity of `FiberTupleMatch` in the ordinal depth. -/
theorem FiberTupleMatch.mono [Lc.IsRelational] {eR : R₁ ≃ R₂} {α β : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : FiberTupleMatch (Lc := Lc) eR β a b) (hαβ : α ≤ β) :
    FiberTupleMatch (Lc := Lc) eR α a b := by
  obtain ⟨hsort, hown, hfib⟩ := h
  refine ⟨hsort, hown, fun r₁ r₂ hr i => ?_⟩
  obtain ⟨d, x, y, hxy, hmem⟩ := hfib r₁ r₂ hr i
  exact ⟨d, x, y, hxy.mono hαβ, hmem⟩

private theorem eq_imp_of_fiberTupleMatch_zero [Lc.IsRelational] {eR : R₁ ≃ R₂} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : FiberTupleMatch (Lc := Lc) eR (0 : Ordinal.{o}) a b) {k₁ k₂ : Fin n}
    (hk : a k₁ = a k₂) : b k₁ = b k₂ := by
  obtain ⟨hsort, hown, hfib⟩ := h
  have hr₁ : ownerRow (a k₁) = ownerRow (a k₂) := congrArg ownerRow hk
  have hr₂ : ownerRow (b k₁) = ownerRow (b k₂) :=
    (hown k₁).symm.trans ((congrArg eR hr₁).trans (hown k₂))
  cases hs : sort (a k₁) with
  | none =>
    have hs₁ : sort (b k₁) = none := (hsort k₁).symm.trans hs
    have hs₂ : sort (b k₂) = none := (hsort k₂).symm.trans (hk ▸ hs)
    rw [eq_row_of_sort_eq_none hs₁, eq_row_of_sort_eq_none hs₂, hr₂]
  | some i =>
    obtain ⟨d, x, y, hxy, hmem⟩ := hfib (ownerRow (a k₁)) (ownerRow (b k₁)) (hown k₁) i
    obtain ⟨m₁, ha₁, hb₁⟩ := hmem k₁ rfl hs
    obtain ⟨m₂, ha₂, hb₂⟩ := hmem k₂ hr₁.symm (hk ▸ hs)
    have hxm : x m₁ = x m₂ := pt_inj_right.mp (ha₁.symm.trans (hk.trans ha₂))
    have hym : y m₁ = y m₂ := (hxy.sameAtomicType.eq_iff m₁ m₂).mp hxm
    rw [hb₁, hb₂, hym]

private theorem relMap_imp_of_fiberTupleMatch_zero [Lc.IsRelational] {eR : R₁ ≃ R₂} {n l : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : FiberTupleMatch (Lc := Lc) eR (0 : Ordinal.{o}) a b)
    (R : (lang I Lc).Relations l) (f : Fin l → Fin n)
    (hR : Structure.RelMap (L := lang I Lc) R (a ∘ f)) :
    Structure.RelMap (L := lang I Lc) R (b ∘ f) := by
  obtain ⟨hsort, hown, hfib⟩ := h
  cases R with
  | row =>
    simpa [← hsort (f 0)] using hR
  | lab i =>
    simpa [← hsort (f 0)] using hR
  | own =>
    simpa [← hsort (f 0), ← hsort (f 1), ← hown (f 0), ← hown (f 1), eR.injective.eq_iff] using hR
  | lift0 S i =>
    obtain ⟨r₁, hr₁, hS⟩ := hR
    obtain ⟨d, x, y, hxy, _⟩ := hfib r₁ (eR r₁) rfl i
    have hsb : sort (b (f 0)) = none := by
      have : sort (a (f 0)) = none := by simp [Function.comp_apply] at hr₁; simp [hr₁]
      exact (hsort (f 0)).symm.trans this
    have hrb : ownerRow (b (f 0)) = eR r₁ := by
      have : ownerRow (a (f 0)) = r₁ := by simp [Function.comp_apply] at hr₁; simp [hr₁]
      exact (hown (f 0)).symm.trans (congrArg eR this)
    have h0 := hxy.sameAtomicType.rel_iff S Fin.elim0
    rw [Subsingleton.elim (x ∘ Fin.elim0) Fin.elim0,
      Subsingleton.elim (y ∘ Fin.elim0) Fin.elim0] at h0
    exact ⟨eR r₁, (eq_row_of_sort_eq_none hsb).trans (congrArg Carrier.row hrb), h0.mp hS⟩
  | lift S =>
    obtain ⟨r₁, i, w₁, hw₁, hS⟩ := hR
    obtain ⟨d, x, y, hxy, hmem⟩ := hfib r₁ (eR r₁) rfl i
    have hq (q : Fin _) : ∃ m : Fin d, x m = w₁ q ∧ b (f q) = .pt (eR r₁) i (y m) := by
      have hfq : a (f q) = .pt r₁ i (w₁ q) := hw₁ q
      obtain ⟨m, ha, hb⟩ := hmem (f q) (by simp [hfq]) (by simp [hfq])
      exact ⟨m, pt_inj_right.mp (ha.symm.trans hfq), hb⟩
    choose g hgx hgb using hq
    have hw_eq : x ∘ g = w₁ := funext hgx
    exact ⟨eR r₁, i, y ∘ g, hgb, (hxy.sameAtomicType.rel_iff S g).mp (hw_eq ▸ hS)⟩

private theorem forth_of_fiberTupleMatch_add_one [Lc.IsRelational] {eR : R₁ ≃ R₂} {α : Ordinal.{o}}
    {n : ℕ} {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : FiberTupleMatch (Lc := Lc) eR (α + 1) a b) (u : Carrier R₁ C₁) :
    ∃ v : Carrier R₂ C₂,
      FiberTupleMatch (Lc := Lc) eR α (Fin.snoc a u) (Fin.snoc b v) := by
  obtain ⟨hsort, hown, hfib⟩ := h
  cases u with
  | row r₀ =>
    refine ⟨.row (eR r₀), ?_, ?_, fun r₁ r₂ hr i => ?_⟩
    · exact fun k => Fin.lastCases (by simp) (fun j => by simpa using hsort j) k
    · exact fun k => Fin.lastCases (by simp) (fun j => by simpa using hown j) k
    · obtain ⟨d, x, y, hxy, hmem⟩ := hfib r₁ r₂ hr i
      refine ⟨d, x, y, hxy.mono (Order.le_succ α), fun k hkr hks => ?_⟩
      refine Fin.lastCases (fun _ hs => by simp at hs) (fun j hjr hjs => ?_) k hkr hks
      simpa using hmem j (by simpa using hjr) (by simpa using hjs)
  | pt r₀ i₀ p₀ =>
    obtain ⟨d₀, x₀, y₀, hxy₀, hmem₀⟩ := hfib r₀ (eR r₀) rfl i₀
    obtain ⟨q₀, hq₀⟩ := ((BFEquiv.add_one α x₀ y₀).mp hxy₀).2.1 p₀
    refine ⟨.pt (eR r₀) i₀ q₀, ?_, ?_, fun r₁ r₂ hr i => ?_⟩
    · exact fun k => Fin.lastCases (by simp) (fun j => by simpa using hsort j) k
    · exact fun k => Fin.lastCases (by simp) (fun j => by simpa using hown j) k
    · by_cases hri : r₀ = r₁ ∧ i₀ = i
      · rcases hri with ⟨rfl, rfl⟩
        subst hr
        refine ⟨d₀ + 1, Fin.snoc x₀ p₀, Fin.snoc y₀ q₀, hq₀, fun k hkr hks => ?_⟩
        refine Fin.lastCases (fun _ _ => ⟨Fin.last d₀, by simp, by simp⟩)
          (fun j hjr hjs => ?_) k hkr hks
        obtain ⟨m, ha, hb⟩ := hmem₀ j (by simpa using hjr) (by simpa using hjs)
        exact ⟨m.castSucc, by simpa using ha, by simpa using hb⟩
      · obtain ⟨d, x, y, hxy, hmem⟩ := hfib r₁ r₂ hr i
        refine ⟨d, x, y, hxy.mono (Order.le_succ α), fun k hkr hks => ?_⟩
        refine Fin.lastCases (fun hr' hs' => ?_) (fun j hjr hjs => ?_) k hkr hks
        · exact False.elim (hri ⟨by simpa using hr', Option.some.inj (by simpa using hs')⟩)
        · simpa using hmem j (by simpa using hjr) (by simpa using hjs)

/-- **Back-and-forth assembly.** If `a` and `b` satisfy `FiberTupleMatch eR α a b` along a row
bijection `eR : R₁ ≃ R₂`, then `a` and `b` are back-and-forth equivalent at depth `α` in the
assembled language. -/
theorem bfEquiv_of_fiber_bfEquiv [Lc.IsRelational] {eR : R₁ ≃ R₂} {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → Carrier R₁ C₁} {b : Fin n → Carrier R₂ C₂}
    (h : FiberTupleMatch (Lc := Lc) eR α a b) :
    BFEquiv (L := lang I Lc) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    refine BFEquiv.zero.mpr ((sameAtomicType_iff a b).mpr ⟨fun k₁ k₂ => ?_, fun R f => ?_⟩)
    · exact ⟨eq_imp_of_fiberTupleMatch_zero h, eq_imp_of_fiberTupleMatch_zero h.symm⟩
    · exact ⟨relMap_imp_of_fiberTupleMatch_zero h R f,
        relMap_imp_of_fiberTupleMatch_zero h.symm R f⟩
  | add_one α ih =>
    refine (BFEquiv.add_one α a b).mpr ⟨ih (h.mono (Order.le_succ α)), fun u => ?_, fun v => ?_⟩
    · obtain ⟨v, hv⟩ := forth_of_fiberTupleMatch_add_one h u
      exact ⟨v, ih hv⟩
    · obtain ⟨u, hu⟩ := forth_of_fiberTupleMatch_add_one h.symm v
      exact ⟨u, ih hu.symm⟩
  | limit α hlim ih =>
    exact (BFEquiv.limit hlim a b).mpr fun β hβ => ih β hβ (h.mono hβ.le)

/-- If a bijection of rows `eR : R₁ ≃ R₂` makes every paired fiber `(C₁ r i, C₂ (eR r) i)`
empty-tuple equivalent at depth `α`, then the empty tuples of the assembled structures are
equivalent at depth `α`. -/
theorem bfEquiv_elim0_of_fiber_bfEquiv [Lc.IsRelational] {α : Ordinal.{o}} (eR : R₁ ≃ R₂)
    (hC : ∀ r i, BFEquiv (L := Lc) α 0
      (Fin.elim0 : Fin 0 → C₁ r i) (Fin.elim0 : Fin 0 → C₂ (eR r) i)) :
    BFEquiv (L := lang I Lc) α 0
      (Fin.elim0 : Fin 0 → Carrier R₁ C₁) (Fin.elim0 : Fin 0 → Carrier R₂ C₂) := by
  refine bfEquiv_of_fiber_bfEquiv (eR := eR) ⟨fun k => k.elim0, fun k => k.elim0, ?_⟩
  rintro r₁ _ rfl i
  exact ⟨0, Fin.elim0, Fin.elim0, hC r₁ i, fun k => k.elim0⟩

/-- If a bijection of rows `eR : R₁ ≃ R₂` makes every paired fiber `(C₁ r' i, C₂ (eR r') i)`
empty-tuple equivalent at depth `α`, then the singleton row tuples `![.row r]` and `![.row (eR r)]`
are equivalent at depth `α`. -/
theorem bfEquiv_singleton_row_of_fiber_bfEquiv [Lc.IsRelational] {α : Ordinal.{o}} (eR : R₁ ≃ R₂)
    (r : R₁)
    (hC : ∀ r' i, BFEquiv (L := Lc) α 0
      (Fin.elim0 : Fin 0 → C₁ r' i) (Fin.elim0 : Fin 0 → C₂ (eR r') i)) :
    BFEquiv (L := lang I Lc) α 1
      ![(Carrier.row r : Carrier R₁ C₁)] ![(Carrier.row (eR r) : Carrier R₂ C₂)] := by
  refine bfEquiv_of_fiber_bfEquiv (eR := eR) ⟨?_, ?_, ?_⟩
  · exact Fin.forall_fin_one.mpr (by simp)
  · exact Fin.forall_fin_one.mpr (by simp)
  · rintro r₁ _ rfl i
    refine ⟨0, Fin.elim0, Fin.elim0, hC r₁ i, ?_⟩
    exact Fin.forall_fin_one.mpr fun _ hs => by simp at hs

end TauCeti.RowAssembly
