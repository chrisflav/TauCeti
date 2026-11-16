/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Region
public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Ore
public import TauCeti.NumberTheory.LocalField.MassFormula.RootCount
import TauCeti.NumberTheory.LocalField.MassFormula.Countable
import TauCeti.NumberTheory.LocalField.MassFormula.Integral
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The discriminant box in Eisenstein coefficient space

Let `K` be a nonarchimedean local field with residue cardinality `q = Nat.card 𝓀[K]`, ring of
integers `𝒪[K]`, and maximal ideal `𝓂[K]`. For a positive degree `n` and a wild exponent `j`, the
**discriminant box** `TauCeti.eisensteinBox K n j` is the subset of the Eisenstein region
`TauCeti.eisensteinSet K n` consisting of those coefficient vectors `a : Fin n → K` whose degree-`h`
coefficient (`1 ≤ h < n`) lies in `𝓂[K] ^ oreCoefficientDepth K n j h` and, when `j % n > 0`,
whose coefficient at index `j % n` does not lie in the next power of `𝓂[K]`; when
`¬ IsOreAdmissible K n j`, the box is empty.

By `TauCeti.iInf_eisenstein_derivative_eq_iff`, a vector `a ∈ eisensteinSet K n` lies in
`eisensteinBox K n j` if and only if its integral Eisenstein lift has derivative infimum equal to
`n - 1 + j`. Consequently:

* the boxes `eisensteinBox K n j` (`j : ℕ`) are pairwise disjoint and partition the separable locus
  of `eisensteinSet K n`;
* `eisensteinBox K n j` is nonempty if and only if `IsOreAdmissible K n j` holds;
* every root of `monicOfCoeff a` for `a ∈ eisensteinBox K n j` generates a member of `σ_K(n)` with
  wild exponent `j`, and conversely every Eisenstein polynomial having a root in `L ∈ σ_K(n)` lies
  in `eisensteinBox K n L.wildExponent`;
* each box is measurable and, for a left-invariant measure `μ` normalized on `integerBox K (Fin n)`,
  has volume `q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) (1 - q⁻¹)` when `n ∣ j` and
  `q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) (1 - q⁻¹)²` when `n ∤ j`;
* integrating `L.rootCount` over `eisensteinBox K n j` yields `q ^ (-(n + j)) (1 - q⁻¹)` if
  `L.wildExponent = j` and `0` otherwise, while summing over `L ∈ σ_K(n)` gives
  `n * μ (eisensteinBox K n j)`.

## Main definitions

* `TauCeti.eisensteinBox K n j`: the discriminant box of degree `n` and wild exponent `j` in
  `Fin n → K`.

## Main results

* `TauCeti.mem_eisensteinBox_iff_iInf_eq`: characterization of box membership via the Eisenstein
  derivative infimum.
* `TauCeti.pairwise_disjoint_eisensteinBox` and `TauCeti.iUnion_eisensteinBox_eq`: the boxes
  partition the separable Eisenstein polynomials of degree `n`.
* `TauCeti.measure_eisensteinBox`: the exact Haar volume of the discriminant box.
* `IntermediateField.lintegral_rootCount_eisensteinBox_of_wildExponent_eq` and
  `TauCeti.tsum_lintegral_rootCount_eisensteinBox_eq`: the local and summed root-count integrals
  over the discriminant box.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `𝔭`-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, Colloq. Internat. CNRS **143** (1966), 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §§2–3.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing MeasureTheory TauCeti.Polynomial
open scoped IntermediateField ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

section DiscreteValuation

variable [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- The **discriminant box** in `Fin n → K`: when `IsOreAdmissible K n j`, the set of Eisenstein
coefficient vectors `a ∈ eisensteinSet K n` whose degree-`h` entry (`1 ≤ h < n`) lies in
`𝓂[K] ^ oreCoefficientDepth K n j h` and, for `h = j % n` (when `0 < j % n`), does not lie in
`𝓂[K] ^ (oreCoefficientDepth K n j h + 1)`. When `¬ IsOreAdmissible K n j`, the box is empty. -/
def eisensteinBox (n j : ℕ) : Set (Fin n → K) :=
  {a | IsOreAdmissible K n j ∧ a ∈ eisensteinSet K n ∧
    ∀ i : Fin n, 0 < i.1 →
      a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i.1) ∧
        (i.1 = j % n →
          a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i.1 + 1)))}

/-- Unfolding membership in `TauCeti.eisensteinBox`. -/
theorem mem_eisensteinBox_iff {n j : ℕ} {a : Fin n → K} :
    a ∈ eisensteinBox K n j ↔
      IsOreAdmissible K n j ∧ a ∈ eisensteinSet K n ∧
        ∀ i : Fin n, 0 < i.1 →
          a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ oreCoefficientDepth K n j i.1) ∧
            (i.1 = j % n →
              a i ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (oreCoefficientDepth K n j i.1 + 1))) := by
  rw [eisensteinBox]; rfl

/-- Every discriminant box lies inside the Eisenstein region. -/
theorem eisensteinBox_subset_eisensteinSet (n j : ℕ) :
    eisensteinBox K n j ⊆ eisensteinSet K n :=
  fun _ ha ↦ ha.2.1

/-- Non-admissible pairs `(n, j)` have empty discriminant box. -/
theorem eisensteinBox_eq_empty_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    eisensteinBox K n j = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ ha ↦ h ha.1

/-- At degree `0`, every discriminant box is empty. -/
@[simp]
theorem eisensteinBox_zero_left (j : ℕ) : eisensteinBox K 0 j = ∅ :=
  eisensteinBox_eq_empty_of_not_isOreAdmissible (isOreAdmissible_zero_left j)

private theorem enat_le_and_not_succ_le_iff {d : ℕ} {v : ℕ∞} :
    (d : ℕ∞) ≤ v ∧ ¬ ((d + 1 : ℕ) : ℕ∞) ≤ v ↔ v = (d : ℕ∞) := by
  cases v with
  | top => simp
  | coe m => norm_cast; omega

private theorem mem_image_maximalIdeal_pow_iff_le_addVal {c : 𝒪[K]} {d : ℕ} :
    (c : K) ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d) ↔ (d : ℕ∞) ≤ addVal 𝒪[K] c := by
  rw [Subtype.val_injective.mem_set_image, SetLike.mem_coe,
    TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]

/-- For a monic Eisenstein polynomial `f` of positive degree `n` over `𝒪[K]` with image
`monicOfCoeff a`, `a` lies in `eisensteinBox K n j` if and only if the Eisenstein derivative
infimum of `f` equals `n - 1 + j`. -/
theorem mem_eisensteinBox_iff_iInf_eq {n j : ℕ} (hn : 0 < n) {a : Fin n → K} {f : 𝒪[K][X]}
    (hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a) (he : f.IsEisensteinAt 𝓂[K]) :
    a ∈ eisensteinBox K n j ↔
      (⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)) =
        ((n - 1 + j : ℕ) : ℕ∞) := by
  have hmonic : f.Monic := (FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr
    (hf ▸ monic_monicOfCoeff a)
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
      natDegree_monicOfCoeff]
  have hcoeff (i : Fin n) : a i = (f.coeff i.1 : K) := by
    rw [← coeff_monicOfCoeff a i, ← hf, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]
  have ha_eis : a ∈ eisensteinSet K n :=
    mem_eisensteinSet_iff_exists_isEisensteinAt.mpr ⟨f, hf, he⟩
  rw [iInf_eisenstein_derivative_eq_iff hn hmonic he hdeg, mem_eisensteinBox_iff]
  simp only [ha_eis, true_and]
  refine and_congr_right fun _ ↦ forall₂_congr fun i _ ↦ ?_
  rw [hcoeff i, mem_image_maximalIdeal_pow_iff_le_addVal,
    mem_image_maximalIdeal_pow_iff_le_addVal]
  split_ifs with him
  · simp only [him, true_imp_iff]
    exact enat_le_and_not_succ_le_iff
  · simp [him]

/-- A discriminant box `eisensteinBox K n j` is nonempty if and only if `IsOreAdmissible K n j`. -/
theorem nonempty_eisensteinBox_iff {n j : ℕ} :
    (eisensteinBox K n j).Nonempty ↔ IsOreAdmissible K n j := by
  refine ⟨fun ⟨_, ha⟩ ↦ ha.1, fun hadm ↦ ?_⟩
  obtain ⟨f, hmonic, he, hdeg, hinf⟩ := exists_eisenstein_iInf_derivative_eq (K := K) hadm
  let a : Fin n → K := fun i ↦ (f.coeff i.1 : K)
  have hf : f.map (algebraMap 𝒪[K] K) = monicOfCoeff a := by
    have hfdeg : (f.map (algebraMap 𝒪[K] K)).natDegree = n := by
      rwa [natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K)]
    rw [← monicOfCoeff_coeff (hmonic.map _) hfdeg]
    exact congrArg monicOfCoeff (funext fun i ↦ by
      simp [a, coeff_map, Algebra.algebraMap_ofSubsemiring_apply])
  exact ⟨a, (mem_eisensteinBox_iff_iInf_eq hadm.pos hf he).mpr hinf⟩

/-- Every polynomial in a discriminant box is separable. -/
theorem separable_monicOfCoeff_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) : (monicOfCoeff a).Separable := by
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha.2.1
  have hmonic : f.Monic := (FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr
    (hf ▸ monic_monicOfCoeff a)
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
      natDegree_monicOfCoeff]
  have hinf := (mem_eisensteinBox_iff_iInf_eq ha.1.pos hf he).mp ha
  rw [← hf]
  exact (separable_map_iff_iInf_eisenstein_derivative_ne_top ha.1.pos hmonic he hdeg).mpr
    (hinf ▸ ENat.natCast_ne_top _)

variable (K) in
/-- The discriminant boxes `eisensteinBox K n j` (`j : ℕ`) are pairwise disjoint. -/
theorem pairwise_disjoint_eisensteinBox (n : ℕ) :
    (Set.univ : Set ℕ).PairwiseDisjoint (eisensteinBox K n) := by
  intro j₁ _ j₂ _ hne
  refine Set.disjoint_left.mpr fun a ha₁ ha₂ ↦ hne ?_
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha₁.2.1
  have h₁ := (mem_eisensteinBox_iff_iInf_eq ha₁.1.pos hf he).mp ha₁
  have h₂ := (mem_eisensteinBox_iff_iInf_eq ha₂.1.pos hf he).mp ha₂
  have heq : n - 1 + j₁ = n - 1 + j₂ := by exact_mod_cast h₁.symm.trans h₂
  omega

/-- For `0 < n`, the discriminant boxes `eisensteinBox K n j` (`j : ℕ`) partition the separable
Eisenstein polynomials of degree `n`. -/
theorem iUnion_eisensteinBox_eq {n : ℕ} (hn : 0 < n) :
    ⋃ j : ℕ, eisensteinBox K n j = {a ∈ eisensteinSet K n | (monicOfCoeff a).Separable} := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, ha⟩
    exact ⟨ha.2.1, separable_monicOfCoeff_of_mem_eisensteinBox ha⟩
  · rintro ⟨ha, hsep⟩
    obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
    have hmonic : f.Monic := (FaithfulSMul.algebraMap_injective 𝒪[K] K).monic_map_iff.mpr
      (hf ▸ monic_monicOfCoeff a)
    have hdeg : f.natDegree = n := by
      rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
        natDegree_monicOfCoeff]
    have hfin : (⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)) ≠ ⊤ :=
      (separable_map_iff_iInf_eisenstein_derivative_ne_top hn hmonic he hdeg).mp (hf ▸ hsep)
    cases hval : (⨅ i : Fin n, n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ)) with
    | top => exact absurd hval hfin
    | coe d =>
      have hge : ((n - 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
        rw [← hval]
        refine le_iInf fun i ↦ ?_
        rcases (Nat.succ_le_of_lt i.isLt).lt_or_eq with hlt | heq
        · have hmem : f.coeff (i + 1) ∈ 𝓂[K] ^ 1 := by simpa using he.mem (hdeg ▸ hlt)
          have h1 : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff (i + 1)) := by
            exact_mod_cast (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal).mp
              hmem
          have h1' : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) := by
            rw [addVal_mul]
            exact le_trans h1 le_self_add
          have hmul : (n : ℕ∞) ≤ n • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) := by
            rw [nsmul_eq_mul]
            simpa only [mul_one] using mul_le_mul_right h1' (n : ℕ∞)
          exact le_trans (by norm_cast; omega) (le_trans hmul le_self_add)
        · have hi : i.1 = n - 1 := by omega
          rw [hi]
          exact le_add_self
      have hge' : n - 1 ≤ d := by exact_mod_cast hge
      refine ⟨d - (n - 1), (mem_eisensteinBox_iff_iInf_eq hn hf he).mpr ?_⟩
      rw [hval, Nat.add_sub_of_le hge']

/-! ### Difference-of-boxes representation for volume computations -/

private abbrev idealBox (K : Type*) [Field K] [ValuativeRel K] {n : ℕ} (d : Fin n → ℕ) :
    Set (Fin n → K) :=
  Set.univ.pi fun i ↦ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i)

private theorem mem_idealBox_sdiff_update_iff {n : ℕ} {d : Fin n → ℕ} {k : Fin n}
    {a : Fin n → K} :
    a ∈ idealBox K d \ idealBox K (Function.update d k (d k + 1)) ↔
      (∀ i, a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ d i)) ∧
        a k ∉ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ (d k + 1)) := by
  simp only [Set.mem_sdiff, idealBox, Set.mem_univ_pi]
  refine and_congr_right fun ha ↦ not_congr ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · simpa only [Function.update_self] using h k
  · rcases eq_or_ne i k with rfl | hik
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hik]
      exact ha i

private theorem mem_idealBox_sdiff_zero_iff {n : ℕ} (hn : 0 < n) {e : Fin n → ℕ}
    (he₀ : e ⟨0, hn⟩ = 1) (he_ge : ∀ i, 1 ≤ e i) {a : Fin n → K} :
    a ∈ idealBox K e \ idealBox K (Function.update e ⟨0, hn⟩ (e ⟨0, hn⟩ + 1)) ↔
      a ∈ eisensteinSet K n ∧
        ∀ i : Fin n, 0 < i.1 → a i ∈ ((↑) : 𝒪[K] → K) '' ↑(𝓂[K] ^ e i) := by
  set i₀ : Fin n := ⟨0, hn⟩
  rw [mem_idealBox_sdiff_update_iff, he₀, eisensteinSet_eq_sdiff hn]
  simp only [Set.mem_sdiff, Set.mem_univ_pi]
  constructor
  · rintro ⟨ha, hnot0⟩
    have ha1 (i : Fin n) : a i ∈ ((↑) : 𝒪[K] → K) '' ↑𝓂[K] := by
      rcases ha i with ⟨c, hc, hca⟩
      exact ⟨c, Ideal.pow_le_self (by have := he_ge i; omega) hc, hca⟩
    exact ⟨⟨ha1, fun h2 ↦ hnot0 (by simpa [i₀] using h2 i₀)⟩, fun i _ ↦ ha i⟩
  · rintro ⟨⟨ha₁, ha₂⟩, hbox⟩
    refine ⟨fun i ↦ ?_, fun h0 ↦ ha₂ fun i ↦ ?_⟩
    · rcases Nat.eq_zero_or_pos i.1 with hi0 | hi0
      · have hi : i = i₀ := Fin.ext hi0
        simpa [hi, he₀] using ha₁ i₀
      · exact hbox i hi0
    · rcases eq_or_ne i i₀ with rfl | hi
      · simpa [i₀] using h0
      · rw [Function.update_of_ne hi, pow_one]
        exact ha₁ i

private theorem eisensteinBox_eq_sdiff_of_mod_eq_zero {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : j % n = 0) :
    let e : Fin n → ℕ := fun i ↦ if i.1 = 0 then 1 else oreCoefficientDepth K n j i.1
    eisensteinBox K n j =
      idealBox K e \ idealBox K (Function.update e ⟨0, hadm.pos⟩ (e ⟨0, hadm.pos⟩ + 1)) := by
  intro e
  have he₀ : e ⟨0, hadm.pos⟩ = 1 := by simp [e]
  have he_ge (i : Fin n) : 1 ≤ e i := by
    dsimp only [e]; split_ifs
    · exact le_rfl
    · exact one_le_oreCoefficientDepth n j i.1
  ext a
  rw [mem_eisensteinBox_iff, mem_idealBox_sdiff_zero_iff hadm.pos he₀ he_ge]
  simp only [hadm, true_and, hb]
  refine and_congr_right fun _ ↦ forall₂_congr fun i hi0 ↦ ?_
  simp [e, hi0.ne']

private theorem eisensteinBox_eq_sdiff_of_mod_pos {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : 0 < j % n) :
    let i₀ : Fin n := ⟨0, hadm.pos⟩
    let i₁ : Fin n := ⟨j % n, Nat.mod_lt j hadm.pos⟩
    let e : Fin n → ℕ := fun i ↦ if i.1 = 0 then 1 else oreCoefficientDepth K n j i.1
    let e₂ : Fin n → ℕ := Function.update e i₁ (e i₁ + 1)
    let S (d : Fin n → ℕ) := idealBox K d \ idealBox K (Function.update d i₀ (d i₀ + 1))
    S e₂ ⊆ S e ∧ eisensteinBox K n j = S e \ S e₂ := by
  intro i₀ i₁ e e₂ S
  have hne : i₁ ≠ i₀ := fun h ↦ hb.ne' (congrArg Fin.val h)
  have he₀ : e i₀ = 1 := by simp [e, i₀]
  have he₂₀ : e₂ i₀ = 1 := by simp [e₂, hne.symm, he₀]
  have he_ge (i : Fin n) : 1 ≤ e i := by
    dsimp only [e]; split_ifs
    · exact le_rfl
    · exact one_le_oreCoefficientDepth n j i.1
  have hle : e ≤ e₂ := le_update_iff.mpr ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩
  have he₂_ge (i : Fin n) : 1 ≤ e₂ i := le_trans (he_ge i) (hle i)
  have hsub : S e₂ ⊆ S e := fun a ha ↦ by
    rw [mem_idealBox_sdiff_update_iff, he₂₀] at ha
    rw [mem_idealBox_sdiff_update_iff, he₀]
    exact ⟨Set.mem_univ_pi.mp (univ_pi_image_maximalIdeal_pow_subset (K := K) hle
      (Set.mem_univ_pi.mpr ha.1)), ha.2⟩
  refine ⟨hsub, ?_⟩
  ext a
  rw [mem_eisensteinBox_iff, Set.mem_sdiff, mem_idealBox_sdiff_zero_iff hadm.pos he₀ he_ge,
    mem_idealBox_sdiff_zero_iff hadm.pos he₂₀ he₂_ge]
  simp only [hadm, true_and]
  constructor
  · rintro ⟨ha, hbox⟩
    refine ⟨⟨ha, fun i hi0 ↦ by simpa [e, hi0.ne'] using (hbox i hi0).1⟩, fun ⟨_, h2⟩ ↦ ?_⟩
    exact (hbox i₁ hb).2 rfl (by simpa [e₂, e, i₁, hb.ne'] using h2 i₁ hb)
  · rintro ⟨⟨ha, hbox⟩, hnot2⟩
    refine ⟨ha, fun i hi0 ↦ ⟨by simpa [e, hi0.ne'] using hbox i hi0, fun him hmem ↦ ?_⟩⟩
    apply hnot2
    refine ⟨ha, fun k hk0 ↦ ?_⟩
    rcases eq_or_ne k i₁ with rfl | hk
    · have hik : i = i₁ := Fin.ext him
      subst hik
      simpa [e₂, e, hi0.ne'] using hmem
    · dsimp only [e₂]; rw [Function.update_of_ne hk]; exact hbox k hk0

end DiscreteValuation

section LocalField

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-! ### Wild-exponent constancy on the discriminant box -/

/-- Every root `x ∈ SeparableClosure K` of a polynomial in `eisensteinBox K n j` generates a
totally ramified degree-`n` extension with wild exponent `j`. -/
theorem wildExponent_adjoin_eq_of_mem_eisensteinBox {n j : ℕ} {a : Fin n → K}
    (ha : a ∈ eisensteinBox K n j) {x : SeparableClosure K}
    (hx : aeval x (monicOfCoeff a) = 0) :
    K⟮x⟯ ∈ totallyRamifiedOfDegree K n ∧ (K⟮x⟯).wildExponent = j := by
  have hn : 0 < n := ha.1.pos
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha.2.1
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
      natDegree_monicOfCoeff]
  have hroot : aeval x (f.map (algebraMap 𝒪[K] K)) = 0 := hf ▸ hx
  have hmem : K⟮x⟯ ∈ totallyRamifiedOfDegree K n :=
    adjoin_mem_totallyRamifiedOfDegree_of_eisenstein he hdeg hroot
  refine ⟨hmem, ?_⟩
  have hinf := (mem_eisensteinBox_iff_iInf_eq hn hf he).mp ha
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein he hroot
  rw [hdeg, hinf] at hd
  have hd_eq : (K⟮x⟯).discriminantExponent = n - 1 + j := by exact_mod_cast hd
  have hwd := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
  omega

/-- If `L ∈ σ_K(n)` contains a root of `monicOfCoeff a` with `a ∈ eisensteinBox K n j`, then
`L.wildExponent = j`. -/
theorem wildExponent_eq_of_mem_eisensteinBox_of_rootCount_ne_zero {n j : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinBox K n j) (hrc : L.rootCount a ≠ 0) :
    L.wildExponent = j := by
  classical
  have hL' := mem_totallyRamifiedOfDegree_iff.mp hL
  have hirr := irreducible_monicOfCoeff_of_mem_eisensteinSet ha.1.pos ha.2.1
  rw [L.rootCount_eq_card_filter_adjoin_eq hirr hL'.1] at hrc
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero hrc)
  rw [Multiset.mem_filter] at hx
  have hroot : aeval x (monicOfCoeff a) = 0 := (mem_aroots.mp hx.1).2
  rw [← hx.2]
  exact (wildExponent_adjoin_eq_of_mem_eisensteinBox ha hroot).2

/-- Conversely, if `L ∈ σ_K(n)` contains a root of an Eisenstein polynomial `monicOfCoeff a`, then
`a` lies in the discriminant box for `L.wildExponent`. -/
theorem mem_eisensteinBox_of_mem_eisensteinSet_of_rootCount_ne_zero {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    {a : Fin n → K} (ha : a ∈ eisensteinSet K n) (hrc : L.rootCount a ≠ 0) :
    a ∈ eisensteinBox K n L.wildExponent := by
  classical
  have hL' := mem_totallyRamifiedOfDegree_iff.mp hL
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hL
  have hirr := irreducible_monicOfCoeff_of_mem_eisensteinSet hn ha
  rw [L.rootCount_eq_card_filter_adjoin_eq hirr hL'.1] at hrc
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero hrc)
  rw [Multiset.mem_filter] at hx
  obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
  have hdeg : f.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K), hf,
      natDegree_monicOfCoeff]
  have hroot : aeval x (f.map (algebraMap 𝒪[K] K)) = 0 := hf ▸ (mem_aroots.mp hx.1).2
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein he hroot
  rw [hx.2, hdeg] at hd
  have hwd : L.discriminantExponent = n - 1 + L.wildExponent := by
    have := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL
    omega
  rw [hwd] at hd
  exact (mem_eisensteinBox_iff_iInf_eq hn hf he).mpr hd.symm

/-- On a discriminant box for a wild exponent `j ≠ L.wildExponent`, the root count of `L` vanishes
identically. -/
theorem rootCount_eq_zero_of_mem_eisensteinBox_of_wildExponent_ne {n j : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (hne : L.wildExponent ≠ j) {a : Fin n → K} (ha : a ∈ eisensteinBox K n j) :
    L.rootCount a = 0 :=
  by_contra fun hrc ↦ hne (wildExponent_eq_of_mem_eisensteinBox_of_rootCount_ne_zero hL ha hrc)

/-! ### Measurability and exact Haar measure of the discriminant box -/

/-- Every discriminant box is measurable. -/
theorem measurableSet_eisensteinBox {n j : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] : MeasurableSet (eisensteinBox K n j) := by
  by_cases hadm : IsOreAdmissible K n j
  · rcases (j % n).eq_zero_or_pos with hb0 | hbpos
    · rw [eisensteinBox_eq_sdiff_of_mod_eq_zero hadm hb0]
      exact (measurableSet_univ_pi_image_maximalIdeal_pow (K := K) _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow (K := K) _)
    · rw [(eisensteinBox_eq_sdiff_of_mod_pos hadm hbpos).2]
      exact ((measurableSet_univ_pi_image_maximalIdeal_pow (K := K) _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow (K := K) _)).diff
        ((measurableSet_univ_pi_image_maximalIdeal_pow (K := K) _).diff
          (measurableSet_univ_pi_image_maximalIdeal_pow (K := K) _))
  · rw [eisensteinBox_eq_empty_of_not_isOreAdmissible hadm]
    exact MeasurableSet.empty

private theorem one_div_pow_sub_one_div_pow_succ {Q : ℝ≥0∞} (hQ0 : Q ≠ 0) (hQt : Q ≠ ∞) (s : ℕ) :
    1 / Q ^ s - 1 / Q ^ (s + 1) = 1 / Q ^ s * (1 - 1 / Q) := by
  simp only [one_div]
  rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.inv_ne_top.mpr (pow_ne_zero _ hQ0), mul_one, pow_succ,
    ENNReal.mul_inv (.inl (pow_ne_zero _ hQ0)) (.inl (ENNReal.pow_ne_top hQt))]

private theorem measure_idealBox_sdiff_update {n : ℕ} [MeasurableSpace (Fin n → K)]
    [BorelSpace (Fin n → K)] (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    (hμ : μ (integerBox K (Fin n)) = 1) (d : Fin n → ℕ) (k : Fin n) :
    μ (idealBox K d \ idealBox K (Function.update d k (d k + 1))) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (∑ i, d i) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  set d' := Function.update d k (d k + 1)
  have hsub : idealBox K d' ⊆ idealBox K d :=
    univ_pi_image_maximalIdeal_pow_subset (K := K)
      (le_update_iff.mpr ⟨Nat.le_succ _, fun _ _ ↦ le_rfl⟩)
  have hsum : ∑ i, d' i = (∑ i, d i) + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase,
      add_assoc, add_comm 1, ← add_assoc, Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have h₁ := Measure.measure_univ_pi_image_maximalIdeal_pow μ d
  have h₂ := Measure.measure_univ_pi_image_maximalIdeal_pow μ d'
  rw [hμ, mul_one] at h₁ h₂
  rw [hsum] at h₂
  have hq : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  rw [measure_sdiff hsub
    (measurableSet_univ_pi_image_maximalIdeal_pow (K := K) d').nullMeasurableSet
    (h₂ ▸ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq)), h₁, h₂,
    one_div_pow_sub_one_div_pow_succ hq (ENNReal.natCast_ne_top _)]

private theorem sum_eisensteinBox_depths {n j : ℕ} (hn : 0 < n) :
    (∑ i : Fin n, if i.1 = 0 then 1 else oreCoefficientDepth K n j i.1) =
      1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h := by
  rw [Fin.sum_univ_eq_sum_range (fun h ↦ if h = 0 then 1 else oreCoefficientDepth K n j h) n]
  have hrange : Finset.range n = insert 0 (Finset.Ico 1 n) := by
    ext h; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  have hnotmem : (0 : ℕ) ∉ Finset.Ico 1 n := by simp
  rw [hrange, Finset.sum_insert hnotmem, ite_eq_left rfl]
  congr 1
  refine Finset.sum_congr rfl fun h hh ↦ ?_
  have h0 : h ≠ 0 := by have := (Finset.mem_Ico.mp hh).1; omega
  rw [ite_eq_right h0]

/-- **The exact Haar measure of the discriminant box**: for an Ore-admissible pair `(n, j)` and a
left-invariant measure `μ` on `Fin n → K` normalized on `integerBox K (Fin n)`, the volume of
`eisensteinBox K n j` is `q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) · (1 - q⁻¹)` if `n ∣ j`, and
`q ^ (-(1 + ∑_{h=1}^{n-1} ν_h)) · (1 - q⁻¹)²` if `n ∤ j`. -/
theorem measure_eisensteinBox {n j : ℕ} (hadm : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    μ (eisensteinBox K n j) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^
          (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) *
        if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) := by
  let e : Fin n → ℕ := fun i ↦ if i.1 = 0 then 1 else oreCoefficientDepth K n j i.1
  have hsum : ∑ i, e i = 1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h :=
    sum_eisensteinBox_depths hadm.pos
  rcases (j % n).eq_zero_or_pos with hb0 | hbpos
  · rw [ite_eq_left hb0, mul_one, eisensteinBox_eq_sdiff_of_mod_eq_zero hadm hb0,
      measure_idealBox_sdiff_update μ hμ e ⟨0, hadm.pos⟩, hsum]
  · rw [ite_eq_right hbpos.ne']
    obtain ⟨hsub, heq⟩ := eisensteinBox_eq_sdiff_of_mod_pos hadm hbpos
    set i₀ : Fin n := ⟨0, hadm.pos⟩
    set i₁ : Fin n := ⟨j % n, Nat.mod_lt j hadm.pos⟩
    set e₂ : Fin n → ℕ := Function.update e i₁ (e i₁ + 1)
    have hsum₂ : ∑ i, e₂ i = (∑ i, e i) + 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i₁), Finset.sdiff_singleton_eq_erase,
        add_assoc, add_comm 1, ← add_assoc, Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
    have hmeas₂ : MeasurableSet (idealBox K e₂ \ idealBox K (Function.update e₂ i₀ (e₂ i₀ + 1))) :=
      (measurableSet_univ_pi_image_maximalIdeal_pow (K := K) _).diff
        (measurableSet_univ_pi_image_maximalIdeal_pow (K := K) _)
    have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
    have hvol₁ := measure_idealBox_sdiff_update μ hμ e i₀
    have hvol₂ := measure_idealBox_sdiff_update μ hμ e₂ i₀
    have hfin₂ : μ (idealBox K e₂ \ idealBox K (Function.update e₂ i₀ (e₂ i₀ + 1))) ≠ ∞ := by
      rw [hvol₂]
      exact ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq0))
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    rw [heq, measure_sdiff hsub hmeas₂.nullMeasurableSet hfin₂, hvol₁, hvol₂, hsum₂, hsum,
      ← ENNReal.sub_mul (fun _ _ ↦ ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self),
      one_div_pow_sub_one_div_pow_succ hq0 (ENNReal.natCast_ne_top _)]

/-! ### Root-count integrals over the discriminant box -/

/-- **Sum of root-count integrals over a discriminant box**: for every measure `μ` on
`Fin n → K`, the root-count integrals over `σ_K(n)` on `eisensteinBox K n j` sum to
`n * μ (eisensteinBox K n j)`. Because every polynomial in the box is separable, no null-set
excision or Haar assumption is needed. -/
theorem tsum_lintegral_rootCount_eisensteinBox_eq {n j : ℕ}
    [MeasurableSpace (Fin n → K)] [OpensMeasurableSpace (Fin n → K)] (μ : Measure (Fin n → K)) :
    ∑' L : totallyRamifiedOfDegree K n,
      ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ =
        n * μ (eisensteinBox K n j) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have := (countable_totallyRamifiedOfDegree hn (K := K)).to_subtype
  have hae (L : totallyRamifiedOfDegree K n) :
      AEMeasurable (fun a ↦ (L.1.rootCount a : ℝ≥0∞)) (μ.restrict (eisensteinBox K n j)) :=
    (aemeasurable_rootCount_restrict_eisensteinSet μ L.2).mono_measure
      (Measure.restrict_mono (eisensteinBox_subset_eisensteinSet n j) le_rfl)
  rw [← lintegral_tsum hae]
  have hsum : ∀ a ∈ eisensteinBox K n j,
      (∑' L : totallyRamifiedOfDegree K n, (L.1.rootCount a : ℝ≥0∞)) = n := fun a ha ↦ by
    obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha.2.1
    exact tsum_rootCount_eq_of_separable he hf (separable_monicOfCoeff_of_mem_eisensteinBox ha)
  rw [setLIntegral_congr_fun measurableSet_eisensteinBox hsum, setLIntegral_const]

end LocalField

end TauCeti

namespace IntermediateField

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For `L ∈ σ_K(n)` with `L.wildExponent = j`, integrating `L.rootCount` over `eisensteinBox K n j`
agrees with integrating over all of `eisensteinSet K n`, because every Eisenstein polynomial having
a root in `L` lies in `eisensteinBox K n j`. -/
theorem lintegral_rootCount_eisensteinBox_eq_lintegral_eisensteinSet
    {n j : ℕ} {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (hj : L.wildExponent = j) [MeasurableSpace (Fin n → K)] [OpensMeasurableSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) :
    ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
      ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ := by
  rw [← lintegral_indicator measurableSet_eisensteinBox,
    ← lintegral_indicator measurableSet_eisensteinSet]
  refine lintegral_congr fun a ↦ ?_
  by_cases hbox : a ∈ eisensteinBox K n j
  · simp [Set.indicator_of_mem hbox,
      Set.indicator_of_mem (eisensteinBox_subset_eisensteinSet n j hbox)]
  · rw [Set.indicator_of_notMem hbox]
    by_cases heis : a ∈ eisensteinSet K n
    · rw [Set.indicator_of_mem heis]
      have h0 : L.rootCount a = 0 := by_contra fun hne ↦
        hbox (hj ▸ mem_eisensteinBox_of_mem_eisensteinSet_of_rootCount_ne_zero hL heis hne)
      simp [h0]
    · rw [Set.indicator_of_notMem heis]

/-- For `L ∈ σ_K(n)` with `L.wildExponent = j` and a left-invariant measure `μ` normalized on
`integerBox K (Fin n)`, the root count of `L` integrates over `eisensteinBox K n j` to
`q ^ (-(n + j)) (1 - q⁻¹)`. -/
theorem lintegral_rootCount_eisensteinBox_of_wildExponent_eq
    {n j : ℕ} {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (hj : L.wildExponent = j) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hd : L.discriminantExponent + 1 = n + j := by
    have := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL
    omega
  rw [L.lintegral_rootCount_eisensteinBox_eq_lintegral_eisensteinSet hL hj μ,
    L.lintegral_rootCount hL μ hμ, hd]

/-- For `L ∈ σ_K(n)` with `L.wildExponent ≠ j`, the root count of `L` integrates to `0` over
`eisensteinBox K n j`. -/
theorem lintegral_rootCount_eisensteinBox_of_wildExponent_ne
    {n j : ℕ} {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (hne : L.wildExponent ≠ j) [MeasurableSpace (Fin n → K)] [OpensMeasurableSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) :
    ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ = 0 := by
  have h0 : ∀ a ∈ eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) = 0 := fun a ha ↦ by
    simp [rootCount_eq_zero_of_mem_eisensteinBox_of_wildExponent_ne hL hne ha]
  rw [setLIntegral_congr_fun measurableSet_eisensteinBox h0, lintegral_zero]

end IntermediateField
