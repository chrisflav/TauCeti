/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space, `F` a finite-dimensional real normed space of dimension `r`,
`k` a commutative ring, and `M` a `k`-module. For the Thom pair
`(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) with projection `π : B × F ⟶ B`
(`TauCeti.prodThomPairProj`), this file proves the **product case of the Thom isomorphism** in
singular cohomology for every rank `r ≥ 0` and every class `u ∈ Hʳ(B × F, B × (F ∖ {0}); k)`
whose restriction to every fibre pair `(F, F ∖ {0})` generates `Hʳ(F, F ∖ {0}; k)`:

`a ↦ π^* a ⌣ u : Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`

is bijective in every degree `p` (`TauCeti.bijective_pullbackCup_prodThomPair`).

The proof constructs a single class `u₀ ∈ Hʳ(B × F, B × (F ∖ {0}); k)` whose pullback-cup map is
bijective for every coefficient module `M` and every degree `p`, splitting into three cases on the
rank `r = finrank ℝ F`:

* **Rank `0`**: `F` is a point, so `B × (F ∖ {0})` is empty, the relative cohomology maps
  isomorphically to the absolute cohomology of `B × F ≅ B`, and `u₀` is the preimage of `1`.
* **Rank `1`**: choosing `F ≃L[ℝ] ℝ`, the punctured space `B × (F ∖ {0})` is homotopy equivalent
  to the disjoint union of two copies of `B`. A degree-zero class `σ₁` equal to `1` on the positive
  component and `0` on the negative component splits `Hᵖ(B × (F ∖ {0}); M)` as
  `(b, c) ↦ π₀^* b + π₀^* c ⌣ σ₁`, and the long exact sequence of the pair identifies
  `Hᵖ(B; M)` with `Hᵖ⁺¹(B × F, B × (F ∖ {0}); M)` via `c ↦ δ (π₀^* c ⌣ σ₁) = (-1)ᵖ π^* c ⌣ δ σ₁`.
* **Rank `r = d + 2 ≥ 2`**: choosing `F ≃L[ℝ] ℝᵈ⁺²`,
  `TauCeti.prodThomPairSingularCohomologySphereEquiv` shows that `c ↦ δ (σ ⌣ π₀^* c)` is bijective,
  and graded commutativity with the connecting-morphism Leibniz rule rewrites this as
  `(-1)^(p(d+2)) π^* c ⌣ δ σ`.

For any other fibrewise-generating class `u`, surjectivity of the map for `u₀` in degree `0` writes
`u = π^* f ⌣ u₀` with `f ∈ H⁰(B; k)`. Restricting to each fibre shows that `f(b)` is a unit in `k`
for every `b : B`, so `f` is a unit in `H⁰(B; k)` (`TauCeti.exists_singularCup_eq_one`), and
associativity of the cup product identifies `a ↦ π^* a ⌣ u` with the composite of right cupping by
`f` and the bijective map for `u₀`.

## Main results

* `TauCeti.bijective_pullbackCup_prodThomPair`: for any finite-dimensional real normed space `F`
  and any class `u ∈ Hʳ(B × F, B × (F ∖ {0}); k)` generating every fibre `Hʳ(F, F ∖ {0}; k)`,
  `a ↦ π^* a ⌣ u` is bijective `Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)` for every `k`-module
  `M` and every `p`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D, Theorem 4D.10.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module

universe w

namespace TauCeti

section Helpers

variable {k : Type w} [CommRing k]

/-- Scaling a `k`-module by `(-1 : ℤ) ^ n` is an involution, hence bijective. -/
private theorem bijective_neg_one_pow_zsmul {V : Type*} [AddCommGroup V] (n : ℕ) :
    Function.Bijective (fun v : V ↦ ((-1 : ℤ) ^ n) • v) := by
  have hinv : Function.LeftInverse (fun v : V ↦ ((-1 : ℤ) ^ n) • v)
      (fun v : V ↦ ((-1 : ℤ) ^ n) • v) := fun v ↦ by
    dsimp only
    rw [← mul_zsmul, ← mul_pow]
    simp
  exact ⟨hinv.injective, hinv.surjective⟩

/-- Every class of `Hᵐ(B × F; M)` is pulled back from `B`, since `F` is contractible. -/
private theorem exists_singularCohomologyMap_prodThomPairProj_eq (M : ModuleCat.{w} k)
    {B F : Type w} [TopologicalSpace B] [TopologicalSpace F] [Zero F] [ContractibleSpace F]
    (m : ℕ) (y : (prodThomPair B F).fst.singularCohomology (ModuleCat.of k k) k M m) :
    ∃ b, TopCat.singularCohomologyMap (prodThomPairProj B F) m b = y := by
  have h1 := (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap
    (ModuleCat.of k k) k M m
  rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at h1
  have hproj : TopCat.ofHom ContinuousMap.fst = prodThomPairProj B F :=
    TopCat.ext fun p ↦ (prodThomPairProj_apply F p).symm
  have : IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k) (M := M)
    (prodThomPairProj B F) m) := hproj ▸ h1
  refine ⟨inv (TopCat.singularCohomologyMap (prodThomPairProj B F) m) y, ?_⟩
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

/-- If there exists some class `u₀` whose pullback-cup map is bijective for every coefficient
module and degree, then the pullback-cup map of any fibrewise-generating class `u` is bijective. -/
private theorem bijective_pullbackCup_prodThomPair_of_exists (M : ModuleCat.{w} k)
    {B : Type w} [TopologicalSpace B]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (h₀ : ∃ u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k)
      (finrank ℝ F), ∀ (N : ModuleCat.{w} k) (p m : ℕ) (h : p + finrank ℝ F = m),
      Function.Bijective ((prodThomPair B F).pullbackCup N (prodThomPairProj B F)
        (finrank ℝ F) p m h u₀))
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k)
      (finrank ℝ F)}
    (hu : ∀ b : B,
      Submodule.span k {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} =
        ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F)
      (finrank ℝ F) p m h u) := by
  obtain ⟨u₀, hbij₀⟩ := h₀
  obtain ⟨f, hf⟩ := (hbij₀ (ModuleCat.of k k) 0 (finrank ℝ F) (zero_add _)).2 u
  -- Restricting `u = π^* f ⌣ u₀` to the fibre over `b` scales `u₀|_b` by `f(b)`.
  have hf_unit : ∀ b : B, IsUnit (singularCohomologyZeroEval b f) := by
    intro b
    have hproj : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
        TopCat.const (X := (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).fst) b :=
      TopCat.ext fun x ↦
        (prodThomPairProj_apply F (TopPair.Hom.fst (prodThomPairFiberMap F b) x)).trans
          (congrArg Prod.fst (prodThomPairFiberMap_fst_apply F b x))
    have hfib : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u =
        singularCohomologyZeroEval b f •
          TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u₀ := by
      rw [← hf, TopPair.pullbackCup_apply, ← TopPair.singularCup_naturality,
        ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hproj,
        singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, map_smul,
        LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def]
      congr 1
      exact (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCup_constSingularCocycle_left k
        (η := 𝟙 _) (by monoidal) (by monoidal) (zero_add _) _
    let e := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of k k)
      (OpenPartialHomeomorph.refl F) (Set.mem_univ (0 : F))
    have hmem : e.symm 1 ∈ Submodule.span k
        {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} := by
      rw [hu b]; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    rw [hfib] at ha
    have h1 := congrArg e ha
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul] at h1
    exact isUnit_iff_exists_inv.2
      ⟨a * e (TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u₀),
        by linear_combination h1⟩
  obtain ⟨g, hfg, hgf⟩ := exists_singularCup_eq_one f hf_unit
  -- Right cupping with `f` on `Hᵖ(B; M)` is bijective with inverse right cupping with `g`.
  let R (w : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0) :
      (TopCat.of B).singularCohomology (ModuleCat.of k k) k M p →
        (TopCat.of B).singularCohomology (ModuleCat.of k k) k M p :=
    fun a ↦ (TopCat.of B).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (ρ_ M).hom p 0 p rfl a w
  have hR_comp : ∀ w₁ w₂ a, R w₂ (R w₁ a) =
      R ((TopCat.of B).singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl w₁ w₂) a := fun w₁ w₂ a ↦
    (TopCat.of B).singularCup_assoc k (by monoidal) (by monoidal) rfl rfl rfl rfl a w₁ w₂
  have hR_one : ∀ a, R (TopCat.of B).singularCohomologyZeroOne a = a := fun a ↦ by
    dsimp only [R]
    rw [TopCat.singularCohomologyZeroOne_def]
    exact (TopCat.of B).singularCup_constSingularCocycle_right k (η := 𝟙 _)
      (by monoidal) (by monoidal) rfl a
  have hRf_bij : Function.Bijective (R f) := by
    refine Function.bijective_iff_has_inverse.2 ⟨R g, fun a ↦ ?_, fun a ↦ ?_⟩
    · rw [hR_comp, hfg, hR_one]
    · rw [hR_comp, hgf, hR_one]
  -- By associativity of the cup product, `pullbackCup u = pullbackCup u₀ ∘ R f`.
  have hcomp : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u₀) ∘ R f := by
    funext a
    simp only [Function.comp_apply, TopPair.pullbackCup_apply, R, ← hf]
    rw [← TopCat.singularCup_naturality]
    exact ((prodThomPair B F).singularCup_assoc k (by monoidal) (by monoidal)
      rfl h (zero_add _) h _ _ _).symm
  rw [hcomp]
  exact (hbij₀ M p m h).comp hRf_bij

end Helpers

section RankZero

variable {k : Type w} [CommRing k]

/-- Existence of a class with bijective pullback-cup map when `finrank ℝ F = 0`. -/
private theorem exists_bijective_pullbackCup_rankZero {B : Type w} [TopologicalSpace B]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hr : finrank ℝ F = 0) :
    ∃ u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) 0,
      ∀ (M : ModuleCat.{w} k) (p m : ℕ) (h : p + 0 = m),
        Function.Bijective
          ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h u₀) := by
  have : Subsingleton F := finrank_zero_iff.mp hr
  have : Unique F := uniqueOfSubsingleton 0
  have : IsEmpty (prodThomPair B F).snd := ⟨fun p ↦ p.2 (Subsingleton.elim p.1.2 0)⟩
  let u₀ : (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0 :=
    inv ((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0) (prodThomPair B F).fst.singularCohomologyZeroOne
  have hπu₀ : (prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0 u₀ = (prodThomPair B F).fst.singularCohomologyZeroOne := by
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  have hproj : prodThomPairProj B F = (TopCat.isoOfHomeo (Homeomorph.prodUnique B F)).hom :=
    TopCat.ext fun p ↦ prodThomPairProj_apply F p
  have : IsIso (prodThomPairProj B F) := hproj ▸ inferInstance
  refine ⟨u₀, fun M p m h ↦ ?_⟩
  subst h
  have hπ_bij : Function.Bijective ((prodThomPair B F).singularCohomologyπ
      (ModuleCat.of k k) k M p) :=
    (asIso ((prodThomPair B F).singularCohomologyπ
      (ModuleCat.of k k) k M p)).toLinearEquiv.bijective
  have hproj_bij : Function.Bijective (TopCat.singularCohomologyMap (R := ModuleCat.of k k)
      (k := k) (M := M) (prodThomPairProj B F) p) :=
    ((singularCohomologyFunctor (ModuleCat.of k k) k M p).mapIso
      (asIso (prodThomPairProj B F)).op).toLinearEquiv.bijective
  have hcomp : ⇑((prodThomPair B F).singularCohomologyπ (ModuleCat.of k k) k M p) ∘
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p p rfl u₀) =
      ⇑(TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k) (M := M)
        (prodThomPairProj B F) p) := by
    funext a
    simp only [Function.comp_apply, TopPair.pullbackCup_apply]
    rw [TopPair.singularCohomologyπ_singularCup, hπu₀, TopCat.singularCohomologyZeroOne_def]
    exact (prodThomPair B F).fst.singularCup_constSingularCocycle_right k (η := 𝟙 _)
      (by monoidal) (by monoidal) rfl _
  exact (Function.Bijective.of_comp_iff' hπ_bij _).1 (hcomp ▸ hproj_bij)

end RankZero

section RankOne

variable {k : Type w} [CommRing k]

/-- A constant-fibre section `b ↦ (b, e⁻¹ c)` of `B × (F ∖ {0}) → B` for `e : F ≃L[ℝ] ℝ` and
`c ≠ 0`. -/
private def rankOneSection {B F : Type w} [TopologicalSpace B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : F ≃L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) :
    TopCat.of B ⟶ (prodThomPair B F).snd :=
  TopCat.ofHom
    ⟨fun b ↦ ⟨(b, e.symm c), fun h0 ↦ hc (by simpa using congrArg e h0)⟩, by fun_prop⟩

private lemma rankOneSection_comp_proj {B F : Type w} [TopologicalSpace B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : F ≃L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) :
    rankOneSection (B := B) e c hc ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
  TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (rankOneSection e c hc b)

private lemma rankOnePos_clopen {B F : Type w} [TopologicalSpace B] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : F ≃L[ℝ] ℝ) :
    IsClopen {p : (prodThomPair B F).snd | (0 : ℝ) < e p.1.2} := by
  have hpos_open : IsOpen {p : (prodThomPair B F).snd | (0 : ℝ) < e p.1.2} :=
    isOpen_lt continuous_const (e.continuous.comp (continuous_snd.comp continuous_subtype_val))
  have hneg_open : IsOpen {p : (prodThomPair B F).snd | e p.1.2 < (0 : ℝ)} :=
    isOpen_lt (e.continuous.comp (continuous_snd.comp continuous_subtype_val)) continuous_const
  have hcompl : {p : (prodThomPair B F).snd | (0 : ℝ) < e p.1.2}ᶜ =
      {p : (prodThomPair B F).snd | e p.1.2 < (0 : ℝ)} := by
    ext p
    have hne : e p.1.2 ≠ 0 := fun h0 ↦ p.2 (e.injective (h0.trans (map_zero e).symm))
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    exact ⟨fun h ↦ lt_of_le_of_ne h hne, le_of_lt⟩
  exact ⟨isOpen_compl_iff.1 (hcompl ▸ hneg_open), hpos_open⟩

/-- Homotopy equivalence `Σ (_ : ULift Bool), B ≃ₕ B × (F ∖ {0})` for `e : F ≃L[ℝ] ℝ`. -/
private def rankOnePuncturedHomotopyEquiv (B : Type w) [TopologicalSpace B] {F : Type w}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : F ≃L[ℝ] ℝ) :
    ContinuousMap.HomotopyEquiv (Σ _ : ULift.{w} Bool, TopCat.of B) (prodThomPair B F).snd := by
  have hclopen := rankOnePos_clopen (B := B) e
  have hpos_open := hclopen.isOpen
  have hneg_open : IsOpen {p : (prodThomPair B F).snd | e p.1.2 < (0 : ℝ)} :=
    isOpen_lt (e.continuous.comp (continuous_snd.comp continuous_subtype_val)) continuous_const
  let sPos := rankOneSection (B := B) e 1 one_ne_zero
  let sNeg := rankOneSection (B := B) e (-1) (neg_ne_zero.mpr one_ne_zero)
  let gFun : C(Σ _ : ULift.{w} Bool, TopCat.of B, (prodThomPair B F).snd) :=
    ⟨fun x ↦ if x.1.down then sPos x.2 else sNeg x.2, continuous_sigma fun i ↦ by
      cases i with
      | up b => cases b <;> [exact sNeg.hom.continuous; exact sPos.hom.continuous]⟩
  have hf_cont : Continuous (fun p : (prodThomPair B F).snd ↦
      (⟨ULift.up (decide ((0 : ℝ) < e p.1.2)), p.1.1⟩ : Σ _ : ULift.{w} Bool, TopCat.of B)) := by
    rw [continuous_def]
    intro U hU
    have hU' : ∀ i : ULift.{w} Bool,
        IsOpen {b : B | (⟨i, b⟩ : Σ _ : ULift.{w} Bool, TopCat.of B) ∈ U} :=
      fun i ↦ hU.preimage continuous_sigmaMk
    have hpre : (fun p : (prodThomPair B F).snd ↦
        (⟨ULift.up (decide ((0 : ℝ) < e p.1.2)), p.1.1⟩ :
          Σ _ : ULift.{w} Bool, TopCat.of B)) ⁻¹' U =
        ({p | (0 : ℝ) < e p.1.2} ∩
          (fun p : (prodThomPair B F).snd ↦ p.1.1) ⁻¹' {b | ⟨ULift.up true, b⟩ ∈ U}) ∪
        ({p | e p.1.2 < (0 : ℝ)} ∩
          (fun p : (prodThomPair B F).snd ↦ p.1.1) ⁻¹' {b | ⟨ULift.up false, b⟩ ∈ U}) := by
      ext p
      have hne : e p.1.2 ≠ 0 := fun h0 ↦ p.2 (e.injective (h0.trans (map_zero e).symm))
      by_cases hp : (0 : ℝ) < e p.1.2
      · have hnot : ¬ e p.1.2 < 0 := not_lt.mpr hp.le
        simp [hp, hnot]
      · have hlt : e p.1.2 < 0 := lt_of_le_of_ne (not_lt.1 hp) hne
        simp [hp, hlt]
    rw [hpre]
    exact (hpos_open.inter ((hU' (ULift.up true)).preimage
        (continuous_fst.comp continuous_subtype_val))).union
      (hneg_open.inter ((hU' (ULift.up false)).preimage
        (continuous_fst.comp continuous_subtype_val)))
  let fFun : C((prodThomPair B F).snd, Σ _ : ULift.{w} Bool, TopCat.of B) := ⟨_, hf_cont⟩
  have hleft : fFun.comp gFun = ContinuousMap.id _ := by
    ext ⟨⟨b⟩, x⟩
    · cases b
      · have hval : e (sNeg x).1.2 = -1 := e.apply_symm_apply (-1)
        simp [fFun, gFun, hval]
      · have hval : e (sPos x).1.2 = 1 := e.apply_symm_apply 1
        simp [fFun, gFun, hval]
    · cases b
      · exact heq_of_eq (show (sNeg x).1.1 = x from rfl)
      · exact heq_of_eq (show (sPos x).1.1 = x from rfl)
  let signVec : (prodThomPair B F).snd → F :=
    fun p ↦ if (0 : ℝ) < e p.1.2 then e.symm 1 else e.symm (-1)
  have hsignVec_cont : Continuous signVec :=
    continuous_if (fun p hp ↦ absurd hp (by rw [hclopen.frontier_eq]; exact Set.notMem_empty _))
      continuous_const.continuousOn continuous_const.continuousOn
  have hne_homotopy : ∀ (t : unitInterval) (p : (prodThomPair B F).snd),
      (1 - (t : ℝ)) • signVec p + (t : ℝ) • p.1.2 ≠ 0 := by
    intro t p h0
    have he0 : (1 - (t : ℝ)) * e (signVec p) + (t : ℝ) * e p.1.2 = 0 := by
      simpa [map_add, map_smul, smul_eq_mul] using congrArg e h0
    have hne : e p.1.2 ≠ 0 := fun h1 ↦ p.2 (e.injective (h1.trans (map_zero e).symm))
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    by_cases hp : (0 : ℝ) < e p.1.2
    · have hsign : e (signVec p) = 1 := by simp [signVec, hp]
      rw [hsign, mul_one] at he0
      rcases eq_or_lt_of_le ht0 with ht | ht
      · rw [← ht] at he0; norm_num at he0
      · nlinarith
    · have hlt : e p.1.2 < 0 := lt_of_le_of_ne (not_lt.1 hp) hne
      have hsign : e (signVec p) = -1 := by simp [signVec, hp]
      rw [hsign] at he0
      rcases eq_or_lt_of_le ht0 with ht | ht
      · rw [← ht] at he0; norm_num at he0
      · nlinarith
  exact
    { toFun := gFun
      invFun := fFun
      left_inv := hleft ▸ ContinuousMap.Homotopic.refl _
      right_inv :=
        ⟨{ toFun := fun tp ↦
            ⟨(tp.2.1.1, (1 - (tp.1 : ℝ)) • signVec tp.2 + (tp.1 : ℝ) • tp.2.1.2),
              hne_homotopy tp.1 tp.2⟩
           continuous_toFun := by
             refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
             · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
             · refine Continuous.add ?_ ?_
               · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
                   (hsignVec_cont.comp continuous_snd)
               · exact (continuous_subtype_val.comp continuous_fst).smul
                   (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
           map_zero_left := fun p ↦ by
             apply Subtype.ext
             by_cases hp : (0 : ℝ) < e p.1.2
             · apply Prod.ext <;> (simp [gFun, fFun, sPos, rankOneSection, signVec, hp]; rfl)
             · apply Prod.ext <;> (simp [gFun, fFun, sNeg, rankOneSection, signVec, hp]; rfl)
           map_one_left := fun p ↦ by
             apply Subtype.ext
             apply Prod.ext <;> simp }⟩ }

/-- Pulling back along the positive and negative sections identifies `H^q(B × (F ∖ {0}); M)`
with `H^q(B; M) × H^q(B; M)` when `e : F ≃L[ℝ] ℝ`. -/
private theorem bijective_rankOnePuncturedSplit (M : ModuleCat.{w} k) {B F : Type w}
    [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : F ≃L[ℝ] ℝ) (q : ℕ) :
    Function.Bijective (fun x : (prodThomPair B F).snd.singularCohomology
      (ModuleCat.of k k) k M q ↦
        (TopCat.singularCohomologyMap (rankOneSection (B := B) e 1 one_ne_zero) q x,
          TopCat.singularCohomologyMap (rankOneSection (B := B) e (-1)
            (neg_ne_zero.mpr one_ne_zero)) q x)) := by
  let X₂ : ULift.{w} Bool → TopCat.{w} := fun _ ↦ TopCat.of B
  let heq := rankOnePuncturedHomotopyEquiv B e
  have : IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k) (M := M)
    (TopCat.ofHom heq.toFun) q) := heq.isIso_singularCohomologyMap (ModuleCat.of k k) k M q
  have hlim := isLimitFanSingularCohomology X₂ (ModuleCat.{w} k) (ModuleCat.of k k) k M q
  have hg_bij : Function.Bijective (TopCat.singularCohomologyMap (R := ModuleCat.of k k)
      (k := k) (M := M) (TopCat.ofHom heq.toFun) q) :=
    (asIso (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k) (M := M)
      (TopCat.ofHom heq.toFun) q)).toLinearEquiv.bijective
  have hsPos_eq : TopCat.sigmaι X₂ (ULift.up true) ≫ TopCat.ofHom heq.toFun =
      rankOneSection e 1 one_ne_zero :=
    TopCat.ext fun _ ↦ rfl
  have hsNeg_eq : TopCat.sigmaι X₂ (ULift.up false) ≫ TopCat.ofHom heq.toFun =
      rankOneSection e (-1) (neg_ne_zero.mpr one_ne_zero) :=
    TopCat.ext fun _ ↦ rfl
  have hfan_bij : Function.Bijective
      (fun y : (TopCat.of (Σ i : ULift.{w} Bool, X₂ i)).singularCohomology
        (ModuleCat.of k k) k M q ↦
          (TopCat.singularCohomologyMap (TopCat.sigmaι X₂ (ULift.up true)) q y,
            TopCat.singularCohomologyMap (TopCat.sigmaι X₂ (ULift.up false)) q y)) := by
    constructor
    · intro y₁ y₂ hy
      have hhom : ModuleCat.ofHom (LinearMap.toSpanSingleton k _ y₁) =
          ModuleCat.ofHom (LinearMap.toSpanSingleton k _ y₂) := by
        refine Fan.IsLimit.hom_ext hlim _ _ fun i ↦ ?_
        ext
        cases i with
        | up b =>
          cases b
          · simpa [Fan.proj] using congrArg Prod.snd hy
          · simpa [Fan.proj] using congrArg Prod.fst hy
      simpa using congrArg (fun φ ↦ φ.hom (1 : k)) hhom
    · rintro ⟨a, b⟩
      let cone : Fan fun i : ULift.{w} Bool ↦
          (X₂ i).singularCohomology (ModuleCat.of k k) k M q :=
        Fan.mk (ModuleCat.of k k) fun i ↦
          ModuleCat.ofHom (LinearMap.toSpanSingleton k _ (if i.down then a else b))
      refine ⟨(hlim.lift cone).hom (1 : k), Prod.ext ?_ ?_⟩
      · have h1 : hlim.lift cone ≫
            TopCat.singularCohomologyMap (TopCat.sigmaι X₂ (ULift.up true)) q =
            ModuleCat.ofHom (LinearMap.toSpanSingleton k _ a) :=
          hlim.fac cone ⟨ULift.up true⟩
        have h1' := congrArg (fun φ ↦ φ.hom (1 : k)) h1
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h1'
        exact h1'.trans (one_smul k a)
      · have h2 : hlim.lift cone ≫
            TopCat.singularCohomologyMap (TopCat.sigmaι X₂ (ULift.up false)) q =
            ModuleCat.ofHom (LinearMap.toSpanSingleton k _ b) :=
          hlim.fac cone ⟨ULift.up false⟩
        have h2' := congrArg (fun φ ↦ φ.hom (1 : k)) h2
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h2'
        exact h2'.trans (one_smul k b)
  have hcomp : (fun x : (prodThomPair B F).snd.singularCohomology (ModuleCat.of k k) k M q ↦
      (TopCat.singularCohomologyMap (rankOneSection (B := B) e 1 one_ne_zero) q x,
        TopCat.singularCohomologyMap (rankOneSection (B := B) e (-1)
          (neg_ne_zero.mpr one_ne_zero)) q x)) =
      (fun y : (TopCat.of (Σ i : ULift.{w} Bool, X₂ i)).singularCohomology
          (ModuleCat.of k k) k M q ↦
        (TopCat.singularCohomologyMap (TopCat.sigmaι X₂ (ULift.up true)) q y,
          TopCat.singularCohomologyMap (TopCat.sigmaι X₂ (ULift.up false)) q y)) ∘
      TopCat.singularCohomologyMap (TopCat.ofHom heq.toFun) q := by
    funext x
    simp only [Function.comp_apply, ← hsPos_eq, ← hsNeg_eq, TopCat.singularCohomologyMap_comp,
      ConcreteCategory.comp_apply]
  rw [hcomp]
  exact hfan_bij.comp hg_bij

/-- Existence of a class with bijective pullback-cup map when `finrank ℝ F = 1`. -/
private theorem exists_bijective_pullbackCup_rankOne {B : Type w} [TopologicalSpace B]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hr : finrank ℝ F = 1) :
    ∃ u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) 1,
      ∀ (M : ModuleCat.{w} k) (p m : ℕ) (h : p + 1 = m),
        Function.Bijective
          ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h u₀) := by
  let e : F ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (hr.trans (Module.finrank_self ℝ).symm)
  let sPos := rankOneSection (B := B) e 1 one_ne_zero
  let sNeg := rankOneSection (B := B) e (-1) (neg_ne_zero.mpr one_ne_zero)
  have hsPos_proj : sPos ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
    rankOneSection_comp_proj e 1 one_ne_zero
  have hsNeg_proj : sNeg ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
    rankOneSection_comp_proj e (-1) (neg_ne_zero.mpr one_ne_zero)
  -- Degree-zero class `σ₁` equal to `1` on the positive sheet and `0` on the negative sheet.
  obtain ⟨σ₁, hσ₁⟩ := exists_singularCohomologyZeroEval_eq
    (X := (prodThomPair B F).snd)
    (fun p ↦ if (0 : ℝ) < e p.1.2 then (1 : k) else 0) fun p q hpq ↦ by
      obtain ⟨γ⟩ := hpq
      have hcl : IsClopen (γ ⁻¹' {r : (prodThomPair B F).snd | (0 : ℝ) < e r.1.2}) :=
        (rankOnePos_clopen e).preimage γ.continuous
      rcases isClopen_iff.1 hcl with h0 | h1
      · have hp' : ¬ (0 : ℝ) < e p.1.2 := fun h ↦
          Set.notMem_empty (0 : unitInterval) (h0 ▸ by simpa using h)
        have hq' : ¬ (0 : ℝ) < e q.1.2 := fun h ↦
          Set.notMem_empty (1 : unitInterval) (h0 ▸ by simpa using h)
        simp [hp', hq']
      · have hp' : (0 : ℝ) < e p.1.2 := by
          have : (0 : unitInterval) ∈ γ ⁻¹' {r | (0 : ℝ) < e r.1.2} := h1 ▸ Set.mem_univ _
          simpa using this
        have hq' : (0 : ℝ) < e q.1.2 := by
          have : (1 : unitInterval) ∈ γ ⁻¹' {r | (0 : ℝ) < e r.1.2} := h1 ▸ Set.mem_univ _
          simpa using this
        simp [hp', hq']
  have hsPos_σ₁ :
      TopCat.singularCohomologyMap sPos 0 σ₁ = (TopCat.of B).singularCohomologyZeroOne :=
    singularCohomologyZero_ext fun b ↦ by
      rw [singularCohomologyZeroEval_naturality, hσ₁,
        singularCohomologyZeroEval_singularCohomologyZeroOne]
      have hval : e (sPos b).1.2 = 1 := e.apply_symm_apply 1
      simp [hval]
  have hsNeg_σ₁ : TopCat.singularCohomologyMap sNeg 0 σ₁ = 0 :=
    singularCohomologyZero_ext fun b ↦ by
      rw [singularCohomologyZeroEval_naturality, hσ₁, map_zero]
      have hval : e (sNeg b).1.2 = -1 := e.apply_symm_apply (-1)
      simp [hval]
  -- `u₀ := δ σ₁` has bijective pullback-cup map in every degree and for every module `M`.
  let u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) 1 :=
    (prodThomPair B F).singularCohomologyδ (ModuleCat.of k k) k (ModuleCat.of k k) 0 1 rfl σ₁
  refine ⟨u₀, fun M p m h ↦ ?_⟩
  subst h
  let D : (TopCat.of B).singularCohomology (ModuleCat.of k k) k M p ×
      (TopCat.of B).singularCohomology (ModuleCat.of k k) k M p →
      (prodThomPair B F).snd.singularCohomology (ModuleCat.of k k) k M p :=
    fun bc ↦ TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p bc.1 +
      (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (ρ_ M).hom p 0 p rfl
        (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p bc.2) σ₁
  have hD_bij : Function.Bijective D := by
    have hcomp : (fun x ↦ (TopCat.singularCohomologyMap sPos p x,
          TopCat.singularCohomologyMap sNeg p x)) ∘ D =
        fun bc ↦ (bc.1 + bc.2, bc.1) := by
      funext ⟨b, c⟩
      simp only [Function.comp_apply, D, map_add, ← TopCat.singularCup_naturality,
        ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hsPos_proj, hsNeg_proj,
        TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply, hsPos_σ₁, hsNeg_σ₁,
        TopCat.singularCohomologyZeroOne_def, map_zero, add_zero]
      congr 1
      congr 1
      exact (TopCat.of B).singularCup_constSingularCocycle_right k (η := 𝟙 _)
        (by monoidal) (by monoidal) rfl c
    have hshear : Function.Bijective (fun bc :
        (TopCat.of B).singularCohomology (ModuleCat.of k k) k M p ×
        (TopCat.of B).singularCohomology (ModuleCat.of k k) k M p ↦ (bc.1 + bc.2, bc.1)) :=
      Function.bijective_iff_has_inverse.2 ⟨fun xy ↦ (xy.2, xy.1 - xy.2),
        fun ⟨b, c⟩ ↦ by simp, fun ⟨x, y⟩ ↦ by simp⟩
    exact (Function.Bijective.of_comp_iff' (bijective_rankOnePuncturedSplit M e p) D).1
      (hcomp ▸ hshear)
  have hD_zero : ∀ b, D (b, 0) = TopCat.singularCohomologyMap (prodThomPair B F).map p
      (TopCat.singularCohomologyMap (prodThomPairProj B F) p b) := fun b ↦ by
    simp only [D, map_zero, LinearMap.zero_apply, add_zero, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj]
  have hproj_inj : ∀ q, Function.Injective (TopCat.singularCohomologyMap (R := ModuleCat.of k k)
      (k := k) (M := M) (prodThomPairPuncturedProj B F) q) := fun q ↦
    Function.LeftInverse.injective (g := TopCat.singularCohomologyMap sPos q) fun b ↦ by
      rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hsPos_proj,
        TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
  -- Exactness of the pair LES shows `c ↦ δ (D (0, c))` is bijective.
  have hδD_bij : Function.Bijective (fun c : (TopCat.of B).singularCohomology
      (ModuleCat.of k k) k M p ↦
        (prodThomPair B F).singularCohomologyδ (ModuleCat.of k k) k M p (p + 1) rfl
          (D (0, c))) := by
    have hadd : ∀ b c, D (b, c) = D (b, 0) + D (0, c) := fun b c ↦ by
      simp only [D, map_zero, LinearMap.zero_apply, add_zero, zero_add]
    constructor
    · intro c₁ c₂ hc
      have hdiff : (prodThomPair B F).singularCohomologyδ (ModuleCat.of k k) k M p (p + 1) rfl
          (D (0, c₁ - c₂)) = 0 := by
        have hsub : D (0, c₁ - c₂) = D (0, c₁) - D (0, c₂) := by
          simp only [D, map_zero, zero_add, map_sub, LinearMap.sub_apply]
        dsimp only at hc
        rw [hsub, map_sub, hc, sub_self]
      obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
        ((prodThomPair B F).singularCohomology_exact_subspace (ModuleCat.of k k) k M p (p + 1)) _
        hdiff
      obtain ⟨b, rfl⟩ := exists_singularCohomologyMap_prodThomPairProj_eq M p y
      rw [← hD_zero b] at hy
      have := congrArg Prod.snd (hD_bij.1 hy)
      exact sub_eq_zero.1 this.symm
    · intro z
      obtain ⟨b, hb⟩ := exists_singularCohomologyMap_prodThomPairProj_eq M (p + 1)
        ((prodThomPair B F).singularCohomologyπ (ModuleCat.of k k) k M (p + 1) z)
      have hπ : (prodThomPair B F).singularCohomologyπ (ModuleCat.of k k) k M (p + 1) z = 0 := by
        have h0 := ConcreteCategory.congr_hom
          ((prodThomPair B F).singularCohomologyπ_comp_singularCohomologyMap
            (ModuleCat.of k k) k M (p + 1)) z
        rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
          ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj] at h0
        rw [← hb, hproj_inj (p + 1) (h0.trans (map_zero _).symm), map_zero]
      obtain ⟨x, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
        ((prodThomPair B F).singularCohomology_exact_relative (ModuleCat.of k k) k M p (p + 1)) z
        hπ
      obtain ⟨⟨b', c⟩, rfl⟩ := hD_bij.2 x
      refine ⟨c, ?_⟩
      have hδ0 : (prodThomPair B F).singularCohomologyδ (ModuleCat.of k k) k M p (p + 1) rfl
          (D (b', 0)) = 0 := by
        rw [hD_zero b', ← ConcreteCategory.comp_apply,
          (prodThomPair B F).singularCohomologyMap_comp_singularCohomologyδ
            (ModuleCat.of k k) k M p (p + 1)]
        simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [hadd b' c, map_add, hδ0, zero_add]
  -- Compare `δ (D (0, c))` with `(-1)ᵖ • pullbackCup u₀ c` via `singularCohomologyδ_singularCup`.
  have hrel : (fun c ↦ (prodThomPair B F).singularCohomologyδ (ModuleCat.of k k) k M p (p + 1) rfl
        (D (0, c))) =
      (fun v ↦ ((-1 : ℤ) ^ p) • v) ∘
        ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p (p + 1) rfl u₀) := by
    funext c
    simp only [Function.comp_apply, D, map_zero, zero_add, TopPair.pullbackCup_apply,
      ← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
    exact (prodThomPair B F).singularCohomologyδ_singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
      (ρ_ M).hom rfl rfl rfl rfl _ σ₁
  exact (Function.Bijective.of_comp_iff' (bijective_neg_one_pow_zsmul p) _).1 (hrel ▸ hδD_bij)

end RankOne

section RankAtLeastTwo

variable {k : Type w} [CommRing k]

/-- Existence of a class with bijective pullback-cup map when `finrank ℝ F = d + 2`. -/
private theorem exists_bijective_pullbackCup_rankSuccSucc {B : Type w} [TopologicalSpace B]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {d : ℕ}
    (hr : finrank ℝ F = d + 2) :
    ∃ u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) (d + 2),
      ∀ (M : ModuleCat.{w} k) (p m : ℕ) (h : p + (d + 2) = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F)
          (d + 2) p m h u₀) := by
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    ContinuousLinearEquiv.ofFinrankEq (hr.trans (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm)
  let u₀ : (prodThomPair B F).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) (d + 2) :=
    (prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
      (d + 1) (d + 2) rfl (prodThomPairPuncturedClass k B e)
  refine ⟨u₀, fun M p m h ↦ ?_⟩
  have hrel : ⇑(prodThomPairSingularCohomologySphereEquiv M B e p m h) =
      (fun v ↦ ((-1 : ℤ) ^ (p * (d + 1))) • v) ∘ (fun v ↦ ((-1 : ℤ) ^ p) • v) ∘
        ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h u₀) := by
    funext c
    simp only [Function.comp_apply, prodThomPairSingularCohomologySphereEquiv_apply,
      TopPair.pullbackCup_apply]
    have hcomm := (prodThomPair B F).snd.singularCup_gradedComm k
      (u := (λ_ (𝟙_ (ModuleCat.{w} k))).inv) (u' := (λ_ (𝟙_ (ModuleCat.{w} k))).inv)
      (μ := (ρ_ M).hom) (μ' := (λ_ M).hom)
      (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])
      (by exact braiding_leftUnitor M)
      (add_comm p (d + 1))
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p c)
      (prodThomPairPuncturedClass k B e)
    rw [hcomm, map_zsmul, ← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp,
      ConcreteCategory.comp_apply]
    congr 1
    exact (prodThomPair B F).singularCohomologyδ_singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
      (ρ_ M).hom (add_comm p (d + 1)) rfl (by omega) h
      (TopCat.singularCohomologyMap (prodThomPairProj B F) p c)
      (prodThomPairPuncturedClass k B e)
  have hbij : Function.Bijective (prodThomPairSingularCohomologySphereEquiv M B e p m h) :=
    (prodThomPairSingularCohomologySphereEquiv M B e p m h).bijective
  rw [hrel] at hbij
  exact (Function.Bijective.of_comp_iff'
    ((bijective_neg_one_pow_zsmul (p * (d + 1))).comp (bijective_neg_one_pow_zsmul p)) _).1 hbij

end RankAtLeastTwo

/-- **The Thom isomorphism for a product bundle.** Let `F` be a finite-dimensional real normed
space of dimension `r`, `k` a commutative ring, and `M` a `k`-module. For any class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); k)` whose restriction to every fibre pair `(F, F ∖ {0})` generates
`Hʳ(F, F ∖ {0}; k)`, the map `a ↦ π^* a ⌣ u` is bijective
`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)` in every degree `p`. -/
theorem bijective_pullbackCup_prodThomPair {k : Type w} [CommRing k] (M : ModuleCat.{w} k)
    {B : Type w} [TopologicalSpace B]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k)
      (finrank ℝ F)}
    (hu : ∀ b : B,
      Submodule.span k {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} =
        ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F)
      (finrank ℝ F) p m h u) := by
  refine bijective_pullbackCup_prodThomPair_of_exists M ?_ hu h
  rcases hdim : finrank ℝ F with _ | _ | d
  · exact exists_bijective_pullbackCup_rankZero hdim
  · exact exists_bijective_pullbackCup_rankOne hdim
  · exact exists_bijective_pullbackCup_rankSuccSucc hdim

end TauCeti
