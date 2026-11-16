/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.Contraction.Unperturbed
import TauCeti.Algebra.Homology.Contraction.Perturbation
import TauCeti.LinearAlgebra.TensorAlgebra.Projection
import Mathlib.Tactic.Abel

/-!
# Contraction of the cobar--bar construction onto the `A∞` algebra

Let `𝒜` be an `A∞` algebra on a graded module `A` over any commutative ring `R`, and let
`Ω Tᶜ(sA)` be the cobar construction of its reduced bar coalgebra `Tᶜ(sA)` with differential
`d_Ω` (`TauCeti.cobarDifferential`).  This file constructs an explicit special contraction

`TauCeti.AInfinityAlgebra.cobarBarContraction 𝒜`

of `(Ω Tᶜ(sA), d_Ω)` onto `(R × A, (0, 𝒜.differential))`, whose inclusion is

`(r, a) ↦ algebraMap R _ r + 𝒜.toCobarBar.linearPart a`,

whose first projection coordinate is the canonical augmentation
`𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation`, and whose contracting homotopy maps into
the augmentation ideal of `Ω Tᶜ(sA)`.  No field, flatness, or boundedness hypothesis is required.

Starting from the unperturbed contraction `TauCeti.AInfinityAlgebra.cobarUnaryContraction 𝒜` for
the unary cobar differential `d₀`, the perturbation `δ = d_Ω - d₀` is the odd derivation sending
`s⁻¹ v` to `-s⁻¹ (b_{≥ 2} v)`.  With respect to the exhaustive total-letter-count filtration on
`Ω Tᶜ(sA)`, the unperturbed homotopy `h` preserves the filtration while `δ` strictly lowers it,
so `δ h` is locally nilpotent and `1 + δ h` is invertible
(`Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero`).  Applying the basic perturbation
lemma (`TauCeti.LinearSpecialContraction.perturb`) yields `cobarBarContraction 𝒜`, and because
`δ ∘ incl = 0`, both the inclusion and the retract differential are unchanged.

## Main definitions

* `TauCeti.AInfinityAlgebra.cobarBarContraction`: the special contraction of `Ω Tᶜ(sA)` onto
  `R × A`.

## Main results

* `TauCeti.AInfinityAlgebra.cobarBarContraction_incl`: the inclusion of `cobarBarContraction` is
  `(r, a) ↦ algebraMap R _ r + 𝒜.toCobarBar.linearPart a`.
* `TauCeti.AInfinityAlgebra.fst_cobarBarContraction_proj`: the scalar coordinate of the projection
  is the canonical cobar augmentation.
* `TauCeti.AInfinityAlgebra.cobarAugmentation_cobarBarContraction_homotopy`: the contracting
  homotopy lands in the augmentation ideal of `Ω Tᶜ(sA)`.

## References

* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4, for the bar--cobar resolution `Ω B A` of an augmented `A∞` algebra.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, for the contracting homotopy of `Ω B A`.
* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* M. Crainic, *On the perturbation lemma, and deformations*, Section 2.
-/

public section

open scoped BigOperators TensorProduct
open TensorAlgebra TauCeti.InternalGrading

namespace TauCeti.AInfinityAlgebra

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### Perturbation by the higher bar differential -/

section Perturbation

variable (𝒜 : AInfinityAlgebra R A)

/-- The perturbation `δ = d_Ω - d₀` of the cobar differential. -/
private noncomputable def cobarPerturbation :
    Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
  cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential -
    cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
      (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential

private theorem cobarPerturbation_eq_derivation :
    cobarPerturbation 𝒜 =
      tensorAlgebraDerivation ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1))
        (-(ι R ∘ₗ 𝒜.higherBarDifferential)) := by
  refine tensorAlgebraDerivation_unique _ _ (cobarPerturbation 𝒜) (fun x y ↦ ?_) (fun v ↦ ?_)
  · simp only [cobarPerturbation, LinearMap.sub_apply, cobarDifferential_mul_eq]
    rw [sub_mul, mul_sub]
    abel
  · simp only [cobarPerturbation, LinearMap.sub_apply, cobarDifferential_ι, LinearMap.neg_apply,
      LinearMap.comp_apply, 𝒜.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add]
    abel

private theorem cobarPerturbation_comp_incl :
    cobarPerturbation 𝒜 ∘ₗ 𝒜.cobarUnaryContraction.incl = 0 := by
  apply LinearMap.ext
  rintro ⟨r, a⟩
  rw [LinearMap.comp_apply, LinearMap.zero_apply, cobarPerturbation_eq_derivation,
    cobarUnaryContraction_incl, AInfinityHom.linearPart_apply, taylor_toCobarBar]
  simp [tensorAlgebraDerivation_algebraMap, tensorAlgebraDerivation_ι,
    ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_ofLetter]

private theorem cobarAugmentation_cobarPerturbation
    (x : TensorAlgebra R (ReducedTensorWords R A)) :
    𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation (cobarPerturbation 𝒜 x) = 0 := by
  simp only [cobarPerturbation, LinearMap.sub_apply, map_sub]
  rw [𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.map_d x,
    ← cobarAugmentation_unaryBar_eq 𝒜,
    𝒜.isNonCounitalDGCoalgebra_unaryBar.cobarAugmentation.map_d x, sub_self]

/-- The total-letter-count filtration on `Ω Tᶜ(sA)`: the `N`-th step is spanned by pure tensors
`s⁻¹ v₁ * ⋯ * s⁻¹ v_k` whose factors lie in `filtration (n i)` with `∑ i, n i ≤ N`. -/
private noncomputable def cobarWordFiltration (N : ℕ) :
    Submodule R (TensorAlgebra R (ReducedTensorWords R A)) :=
  Submodule.span R {z | ∃ (k : ℕ) (v : Fin k → ReducedTensorWords R A) (n : Fin k → ℕ),
    (∀ i, v i ∈ ReducedTensorWords.filtration R A (n i)) ∧ ∑ i, n i ≤ N ∧
      z = TensorAlgebra.tprod R _ k v}

private theorem cobarWordFiltration_monotone {M N : ℕ} (hMN : M ≤ N) :
    cobarWordFiltration (R := R) (A := A) M ≤ cobarWordFiltration (R := R) (A := A) N :=
  Submodule.span_mono fun _ ⟨k, v, n, hv, hn, hz⟩ ↦ ⟨k, v, n, hv, hn.trans hMN, hz⟩

private theorem tprod_mem_cobarWordFiltration {k : ℕ} (v : Fin k → ReducedTensorWords R A)
    (n : Fin k → ℕ) (hv : ∀ i, v i ∈ ReducedTensorWords.filtration R A (n i))
    {N : ℕ} (hn : ∑ i, n i ≤ N) :
    TensorAlgebra.tprod R _ k v ∈ cobarWordFiltration (R := R) (A := A) N :=
  Submodule.subset_span ⟨k, v, n, hv, hn, rfl⟩

private theorem one_mem_cobarWordFiltration :
    (1 : TensorAlgebra R (ReducedTensorWords R A)) ∈ cobarWordFiltration (R := R) (A := A) 0 := by
  have h1 : (1 : TensorAlgebra R (ReducedTensorWords R A)) =
      TensorAlgebra.tprod R _ 0 Fin.elim0 := by
    simp [TensorAlgebra.tprod_apply]
  rw [h1]
  exact tprod_mem_cobarWordFiltration Fin.elim0 Fin.elim0 (fun i ↦ Fin.elim0 i) (by simp)

private theorem ι_mem_cobarWordFiltration {v : ReducedTensorWords R A} {n : ℕ}
    (hv : v ∈ ReducedTensorWords.filtration R A n) :
    ι R v ∈ cobarWordFiltration (R := R) (A := A) n := by
  have h1 : ι R v = TensorAlgebra.tprod R _ 1 (fun _ ↦ v) := by
    simp [TensorAlgebra.tprod_apply]
  rw [h1]
  exact tprod_mem_cobarWordFiltration (fun _ ↦ v) (fun _ ↦ n) (fun _ ↦ hv) (by simp)

private theorem mul_mem_cobarWordFiltration {M N : ℕ}
    {x y : TensorAlgebra R (ReducedTensorWords R A)}
    (hx : x ∈ cobarWordFiltration (R := R) (A := A) M)
    (hy : y ∈ cobarWordFiltration (R := R) (A := A) N) :
    x * y ∈ cobarWordFiltration (R := R) (A := A) (M + N) := by
  refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb ↦ by
    rw [add_mul]; exact add_mem ha hb) (fun r _ _ ha ↦ by
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha) hx
  rintro _ ⟨k₁, v₁, n₁, hv₁, hn₁, rfl⟩
  refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb ↦ by
    rw [mul_add]; exact add_mem ha hb) (fun r _ _ ha ↦ by
    rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha) hy
  rintro _ ⟨k₂, v₂, n₂, hv₂, hn₂, rfl⟩
  rw [TensorAlgebra.tprod_mul_tprod]
  refine tprod_mem_cobarWordFiltration (Fin.append v₁ v₂) (Fin.append n₁ n₂) (fun i ↦ ?_) ?_
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa using hv₁ j
    · simpa using hv₂ j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact Nat.add_le_add hn₁ hn₂

private theorem exists_mem_cobarWordFiltration (x : TensorAlgebra R (ReducedTensorWords R A)) :
    ∃ N : ℕ, x ∈ cobarWordFiltration (R := R) (A := A) N := by
  induction x using TensorAlgebra.induction with
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r one_mem_cobarWordFiltration
  | ι v =>
    obtain ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R A v
    exact ⟨n, ι_mem_cobarWordFiltration hn⟩
  | mul x y hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    exact ⟨M + N, mul_mem_cobarWordFiltration hM hN⟩
  | add x y hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    exact ⟨max M N, add_mem (cobarWordFiltration_monotone (le_max_left M N) hM)
      (cobarWordFiltration_monotone (le_max_right M N) hN)⟩

private theorem tprod_eq_zero_of_filtration_zero {k : ℕ} (v : Fin k → ReducedTensorWords R A)
    (n : Fin k → ℕ) (hv : ∀ i, v i ∈ ReducedTensorWords.filtration R A (n i))
    {i : Fin k} (hi : n i = 0) :
    TensorAlgebra.tprod R _ k v = 0 := by
  have hvi : v i = 0 := by
    have := hv i
    rw [hi, ReducedTensorWords.filtration_zero, Submodule.mem_bot] at this
    exact this
  exact (TensorAlgebra.tprod R (ReducedTensorWords R A) k).map_coord_zero i hvi

private theorem cobarHomotopy_eq_zero_of_mem_filtration_zero
    {x : TensorAlgebra R (ReducedTensorWords R A)}
    (hx : x ∈ cobarWordFiltration (R := R) (A := A) 0) :
    𝒜.cobarUnaryContraction.homotopy x = 0 := by
  refine Submodule.span_induction ?_ (map_zero _) (fun _ _ _ _ ha hb ↦ by rw [map_add, ha, hb,
    add_zero]) (fun r _ _ ha ↦ by rw [map_smul, ha, smul_zero]) hx
  rintro _ ⟨k, v, n, hv, hn, rfl⟩
  cases k with
  | zero =>
    have h1 : TensorAlgebra.tprod R _ 0 v = 1 := by simp [TensorAlgebra.tprod_apply]
    rw [h1, cobarUnaryContraction_homotopy_one]
  | succ m =>
    have hn0 : n 0 = 0 := by
      have hle : n 0 ≤ ∑ i : Fin (m + 1), n i :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ 0)
      omega
    rw [tprod_eq_zero_of_filtration_zero v n hv hn0, map_zero]

private theorem cobarPerturbation_eq_zero_of_mem_filtration_zero
    {x : TensorAlgebra R (ReducedTensorWords R A)}
    (hx : x ∈ cobarWordFiltration (R := R) (A := A) 0) : cobarPerturbation 𝒜 x = 0 := by
  refine Submodule.span_induction ?_ (map_zero _) (fun _ _ _ _ ha hb ↦ by rw [map_add, ha, hb,
    add_zero]) (fun r _ _ ha ↦ by rw [map_smul, ha, smul_zero]) hx
  rintro _ ⟨k, v, n, hv, hn, rfl⟩
  cases k with
  | zero =>
    have h1 : TensorAlgebra.tprod R _ 0 v = 1 := by simp [TensorAlgebra.tprod_apply]
    rw [h1, cobarPerturbation_eq_derivation, tensorAlgebraDerivation_one]
  | succ m =>
    have hn0 : n 0 = 0 := by
      have hle : n 0 ≤ ∑ i : Fin (m + 1), n i :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ 0)
      omega
    rw [tprod_eq_zero_of_filtration_zero v n hv hn0, map_zero]

/-- The contracting homotopy `h` preserves the total-letter-count filtration. -/
private theorem cobarHomotopy_mem_cobarWordFiltration {N : ℕ}
    {x : TensorAlgebra R (ReducedTensorWords R A)}
    (hx : x ∈ cobarWordFiltration (R := R) (A := A) N) :
    𝒜.cobarUnaryContraction.homotopy x ∈ cobarWordFiltration (R := R) (A := A) N := by
  refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb ↦ by
    rw [map_add]; exact add_mem ha hb) (fun r _ _ ha ↦ by
    rw [map_smul]; exact Submodule.smul_mem _ r ha) hx
  rintro _ ⟨k, v, n, hv, hn, rfl⟩
  match k with
  | 0 =>
    have h1 : TensorAlgebra.tprod R _ 0 v = 1 := by simp [TensorAlgebra.tprod_apply]
    rw [h1, cobarUnaryContraction_homotopy_one]
    exact zero_mem _
  | 1 =>
    have h1 : TensorAlgebra.tprod R _ 1 v = ι R (v 0) := by simp [TensorAlgebra.tprod_apply]
    rw [h1, cobarUnaryContraction_homotopy_ι]
    exact zero_mem _
  | m + 2 =>
    rcases Nat.eq_zero_or_pos (n 0) with hn0 | hn0
    · rw [tprod_eq_zero_of_filtration_zero v n hv hn0, map_zero]
      exact zero_mem _
    · rw [cobarUnaryContraction_homotopy_tprod_add_two]
      have hprep : ι R (ReducedTensorWords.prepend R A
          ((𝒜.grading.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A (v 0))) (v 1)) ∈
          cobarWordFiltration (R := R) (A := A) (n 1 + 1) :=
        ι_mem_cobarWordFiltration (ReducedTensorWords.prepend_mem_filtration R A _ (hv 1))
      have htail : TensorAlgebra.tprod R _ m (fun i : Fin m ↦ v i.succ.succ) ∈
          cobarWordFiltration (R := R) (A := A) (∑ i : Fin m, n i.succ.succ) :=
        tprod_mem_cobarWordFiltration _ (fun i ↦ n i.succ.succ) (fun i ↦ hv i.succ.succ) le_rfl
      have hsum : n 1 + 1 + ∑ i : Fin m, n i.succ.succ ≤ N := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one] at hn
        omega
      exact cobarWordFiltration_monotone hsum (mul_mem_cobarWordFiltration hprep htail)

private theorem map_mem_filtration (f : A →ₗ[R] A) {n : ℕ} {v : ReducedTensorWords R A}
    (hv : v ∈ ReducedTensorWords.filtration R A n) :
    ReducedTensorWords.map (R := R) f v ∈ ReducedTensorWords.filtration R A n := by
  rw [ReducedTensorWords.mem_filtration_iff] at hv ⊢
  intro k hk
  rw [ReducedTensorWords.component_map, hv k hk, map_zero]

/-- The perturbation `δ` strictly lowers the total-letter-count filtration. -/
private theorem cobarPerturbation_tprod_mem_cobarWordFiltration :
    ∀ (k : ℕ) (v : Fin k → ReducedTensorWords R A) (n : Fin k → ℕ),
      (∀ i, v i ∈ ReducedTensorWords.filtration R A (n i)) →
      cobarPerturbation 𝒜 (TensorAlgebra.tprod R _ k v) ∈
        cobarWordFiltration (R := R) (A := A) (∑ i, n i - 1)
  | 0, v, _, _ => by
    have h1 : TensorAlgebra.tprod R (ReducedTensorWords R A) 0 v = 1 := by
      simp [TensorAlgebra.tprod_apply]
    rw [h1, cobarPerturbation_eq_derivation, tensorAlgebraDerivation_one]
    exact zero_mem _
  | m + 1, v, n, hv => by
    rcases Nat.eq_zero_or_pos (n 0) with hn0 | hn0
    · rw [tprod_eq_zero_of_filtration_zero v n hv hn0, map_zero]
      exact zero_mem _
    obtain ⟨r, hr⟩ : ∃ r, n 0 = r + 1 := ⟨n 0 - 1, by omega⟩
    have hsplit : TensorAlgebra.tprod R _ (m + 1) v =
        ι R (v 0) * TensorAlgebra.tprod R _ m (fun i ↦ v i.succ) := by
      simp [TensorAlgebra.tprod_apply, List.ofFn_succ]
    have htw : koszulTwistAlgEquiv
          (tensorAlgebraPiece ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1))) 1
          (ι R (v 0)) =
        -ι R ((ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (v 0)) := by
      rw [koszulTwistAlgEquiv_apply, koszulTwist_tensorAlgebraPiece_ι,
        InternalGrading.koszulTwist_shift]
      simp
    rw [hsplit, cobarPerturbation_eq_derivation, tensorAlgebraDerivation_mul,
      tensorAlgebraDerivation_ι, LinearMap.neg_apply, LinearMap.comp_apply,
      htw, ← cobarPerturbation_eq_derivation]
    have hsum_eq : ∑ i : Fin (m + 1), n i = r + 1 + ∑ i : Fin m, n i.succ := by
      rw [Fin.sum_univ_succ, hr]
    refine add_mem ?_ ?_
    · rw [neg_mul]
      refine neg_mem <| cobarWordFiltration_monotone (by omega) <| mul_mem_cobarWordFiltration
        (ι_mem_cobarWordFiltration (𝒜.higherBarDifferential_filtration r ⟨v 0, hr ▸ hv 0, rfl⟩))
        (tprod_mem_cobarWordFiltration _ (fun i ↦ n i.succ) (fun i ↦ hv i.succ) le_rfl)
    · rcases Nat.eq_zero_or_pos (∑ i : Fin m, n i.succ) with htail0 | htail_pos
      · have hmem0 : TensorAlgebra.tprod R _ m (fun i ↦ v i.succ) ∈
            cobarWordFiltration (R := R) (A := A) 0 :=
          tprod_mem_cobarWordFiltration _ (fun i ↦ n i.succ) (fun i ↦ hv i.succ) (by omega)
        rw [cobarPerturbation_eq_zero_of_mem_filtration_zero 𝒜 hmem0, mul_zero]
        exact zero_mem _
      · rw [neg_mul]
        have hv0 : (ReducedTensorWords.grading (𝒜.grading.shift 1)).koszulTwist 1 (v 0) ∈
            ReducedTensorWords.filtration R A (r + 1) := by
          rw [ReducedTensorWords.koszulTwist_grading]
          exact map_mem_filtration _ (hr ▸ hv 0)
        exact neg_mem <| cobarWordFiltration_monotone (by omega) <| mul_mem_cobarWordFiltration
          (ι_mem_cobarWordFiltration hv0)
          (cobarPerturbation_tprod_mem_cobarWordFiltration m (fun i ↦ v i.succ)
            (fun i ↦ n i.succ) (fun i ↦ hv i.succ))

private theorem cobarPerturbation_mem_cobarWordFiltration {N : ℕ}
    {x : TensorAlgebra R (ReducedTensorWords R A)}
    (hx : x ∈ cobarWordFiltration (R := R) (A := A) (N + 1)) :
    cobarPerturbation 𝒜 x ∈ cobarWordFiltration (R := R) (A := A) N := by
  refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb ↦ by
    rw [map_add]; exact add_mem ha hb) (fun r _ _ ha ↦ by
    rw [map_smul]; exact Submodule.smul_mem _ r ha) hx
  rintro _ ⟨k, v, n, hv, hn, rfl⟩
  exact cobarWordFiltration_monotone (by omega)
    (cobarPerturbation_tprod_mem_cobarWordFiltration 𝒜 k v n hv)

private theorem pow_perturbation_mul_homotopy_apply_eq_zero :
    ∀ (N : ℕ) {x : TensorAlgebra R (ReducedTensorWords R A)},
      x ∈ cobarWordFiltration (R := R) (A := A) N →
      ((cobarPerturbation 𝒜 * 𝒜.cobarUnaryContraction.homotopy) ^ (N + 1)) x = 0 := by
  intro N
  induction N with
  | zero =>
    intro x hx
    simp [Module.End.mul_eq_comp, cobarHomotopy_eq_zero_of_mem_filtration_zero 𝒜 hx]
  | succ N ih =>
    intro x hx
    rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply]
    have hstep : (cobarPerturbation 𝒜 * 𝒜.cobarUnaryContraction.homotopy) x ∈
        cobarWordFiltration (R := R) (A := A) N :=
      cobarPerturbation_mem_cobarWordFiltration 𝒜 (cobarHomotopy_mem_cobarWordFiltration 𝒜 hx)
    exact ih hstep

private theorem isUnit_one_add_cobarPerturbation_mul_homotopy :
    IsUnit (1 + cobarPerturbation 𝒜 * 𝒜.cobarUnaryContraction.homotopy) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _ fun x ↦ by
    obtain ⟨N, hN⟩ := exists_mem_cobarWordFiltration (R := R) (A := A) x
    exact ⟨N + 1, pow_perturbation_mul_homotopy_apply_eq_zero 𝒜 N hN⟩

private theorem cobarPerturbation_sq_eq :
    (cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential +
      cobarPerturbation 𝒜) ∘ₗ
    (cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential +
      cobarPerturbation 𝒜) =
    cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential ∘ₗ
    cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential := by
  rw [cobarPerturbation, add_sub_cancel]
  ext x
  simp [𝒜.isNonCounitalDGCoalgebra_bar.cobarDifferential_cobarDifferential,
    𝒜.isNonCounitalDGCoalgebra_unaryBar.cobarDifferential_cobarDifferential]

private theorem cobarPerturbationSeries_comp_incl :
    𝒜.cobarUnaryContraction.perturbationSeries (cobarPerturbation 𝒜) ∘ₗ
      𝒜.cobarUnaryContraction.incl = 0 := by
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_eq_comp,
    LinearMap.comp_assoc, cobarPerturbation_comp_incl, LinearMap.comp_zero]

private theorem cobarPerturbedDifferential_eq :
    𝒜.cobarUnaryContraction.perturbedDifferential (cobarPerturbation 𝒜) =
      LinearMap.prodMap (0 : Module.End R R) 𝒜.differential := by
  rw [LinearSpecialContraction.perturbedDifferential_def, cobarPerturbationSeries_comp_incl,
    LinearMap.comp_zero, add_zero]

private theorem cobarUnary_add_perturbation :
    cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.unaryBarDifferential +
      cobarPerturbation 𝒜 =
    cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential :=
  add_sub_cancel _ _

end Perturbation

/-! ### The cobar--bar special contraction -/

private def castContraction {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {dM dM' : Module.End R M} {dN dN' : Module.End R N}
    (hdM : dM = dM') (hdN : dN = dN') (c : LinearSpecialContraction dM dN) :
    LinearSpecialContraction dM' dN' :=
  hdM ▸ hdN ▸ c

private theorem castContraction_incl {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {dM dM' : Module.End R M} {dN dN' : Module.End R N}
    (hdM : dM = dM') (hdN : dN = dN') (c : LinearSpecialContraction dM dN) :
    (castContraction hdM hdN c).incl = c.incl := by
  subst hdM; subst hdN; rfl

private theorem castContraction_proj {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {dM dM' : Module.End R M} {dN dN' : Module.End R N}
    (hdM : dM = dM') (hdN : dN = dN') (c : LinearSpecialContraction dM dN) :
    (castContraction hdM hdN c).proj = c.proj := by
  subst hdM; subst hdN; rfl

private theorem castContraction_homotopy {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {dM dM' : Module.End R M} {dN dN' : Module.End R N}
    (hdM : dM = dM') (hdN : dN = dN') (c : LinearSpecialContraction dM dN) :
    (castContraction hdM hdN c).homotopy = c.homotopy := by
  subst hdM; subst hdN; rfl

/-- **The cobar--bar contraction**: a special contraction of the cobar construction
`(Ω Tᶜ(sA), d_Ω)` onto `(R × A, (0, 𝒜.differential))`, built over any commutative ring by
perturbing the unary cobar contraction with the higher bar differential. -/
noncomputable def cobarBarContraction (𝒜 : AInfinityAlgebra R A) :
    LinearSpecialContraction
      (cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential)
      (LinearMap.prodMap (0 : Module.End R R) 𝒜.differential) :=
  castContraction (cobarUnary_add_perturbation 𝒜) (cobarPerturbedDifferential_eq 𝒜)
    (𝒜.cobarUnaryContraction.perturb (cobarPerturbation 𝒜)
      (cobarPerturbation_sq_eq 𝒜) (isUnit_one_add_cobarPerturbation_mul_homotopy 𝒜))

/-- The inclusion of the cobar--bar contraction sends `(r, a)` to
`algebraMap R _ r + 𝒜.toCobarBar.linearPart a`. -/
@[simp]
theorem cobarBarContraction_incl (𝒜 : AInfinityAlgebra R A) (r : R) (a : A) :
    𝒜.cobarBarContraction.incl (r, a) = algebraMap R _ r + 𝒜.toCobarBar.linearPart a := by
  have hi : 𝒜.cobarBarContraction.incl = 𝒜.cobarUnaryContraction.incl := by
    rw [cobarBarContraction, castContraction_incl, LinearSpecialContraction.perturb_incl,
      cobarPerturbationSeries_comp_incl, LinearMap.comp_zero, sub_zero]
  rw [hi, cobarUnaryContraction_incl]

/-- On `0 × A`, the inclusion of the cobar--bar contraction is the linear part of
`𝒜.toCobarBar`. -/
theorem cobarBarContraction_incl_zero_left (𝒜 : AInfinityAlgebra R A) (a : A) :
    𝒜.cobarBarContraction.incl (0, a) = 𝒜.toCobarBar.linearPart a := by
  simp

/-- On `R × 0`, the inclusion of the cobar--bar contraction is the scalar inclusion. -/
theorem cobarBarContraction_incl_zero_right (𝒜 : AInfinityAlgebra R A) (r : R) :
    𝒜.cobarBarContraction.incl (r, 0) = algebraMap R _ r := by
  simp

/-- The scalar coordinate of the cobar--bar projection is the canonical cobar augmentation. -/
@[simp]
theorem fst_cobarBarContraction_proj (𝒜 : AInfinityAlgebra R A)
    (x : TensorAlgebra R (ReducedTensorWords R A)) :
    (𝒜.cobarBarContraction.proj x).1 =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation x := by
  let εlin : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] R :=
    𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.toGradedAlgHom.toAlgHom.toLinearMap
  have hεδ : εlin ∘ₗ cobarPerturbation 𝒜 = 0 :=
    LinearMap.ext (cobarAugmentation_cobarPerturbation 𝒜)
  have hεX : εlin ∘ₗ 𝒜.cobarUnaryContraction.perturbationSeries (cobarPerturbation 𝒜) = 0 := by
    have h1 : εlin ∘ₗ (1 + cobarPerturbation 𝒜 * 𝒜.cobarUnaryContraction.homotopy) = εlin := by
      rw [LinearMap.comp_add, Module.End.one_eq_id, LinearMap.comp_id, Module.End.mul_eq_comp,
        ← LinearMap.comp_assoc, hεδ, LinearMap.zero_comp, add_zero]
    calc εlin ∘ₗ 𝒜.cobarUnaryContraction.perturbationSeries (cobarPerturbation 𝒜)
        = (εlin ∘ₗ (1 + cobarPerturbation 𝒜 * 𝒜.cobarUnaryContraction.homotopy)) ∘ₗ
            𝒜.cobarUnaryContraction.perturbationSeries (cobarPerturbation 𝒜) := by rw [h1]
      _ = εlin ∘ₗ ((1 + cobarPerturbation 𝒜 * 𝒜.cobarUnaryContraction.homotopy) *
            𝒜.cobarUnaryContraction.perturbationSeries (cobarPerturbation 𝒜)) := by
          rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp]
      _ = εlin ∘ₗ cobarPerturbation 𝒜 := by
          rw [𝒜.cobarUnaryContraction.one_add_mul_perturbationSeries _
            (isUnit_one_add_cobarPerturbation_mul_homotopy 𝒜)]
      _ = 0 := hεδ
  have hp : LinearMap.fst R R A ∘ₗ 𝒜.cobarBarContraction.proj = εlin := by
    rw [cobarBarContraction, castContraction_proj, LinearSpecialContraction.perturb_proj,
      LinearMap.comp_sub, ← LinearMap.comp_assoc]
    have hfst : LinearMap.fst R R A ∘ₗ 𝒜.cobarUnaryContraction.proj = εlin :=
      LinearMap.ext fun y ↦ 𝒜.fst_cobarUnaryContraction_proj y
    rw [hfst, ← LinearMap.comp_assoc, hεX, LinearMap.zero_comp, sub_zero]
  exact LinearMap.congr_fun hp x

/-- The contracting homotopy of the cobar--bar contraction maps into the augmentation ideal. -/
@[simp]
theorem cobarAugmentation_cobarBarContraction_homotopy (𝒜 : AInfinityAlgebra R A)
    (x : TensorAlgebra R (ReducedTensorWords R A)) :
    𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation (𝒜.cobarBarContraction.homotopy x) = 0 := by
  let εlin : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] R :=
    𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.toGradedAlgHom.toAlgHom.toLinearMap
  have hεh : εlin ∘ₗ 𝒜.cobarUnaryContraction.homotopy = 0 :=
    LinearMap.ext (cobarAugmentation_cobarUnaryContraction_homotopy 𝒜)
  have hh : εlin ∘ₗ 𝒜.cobarBarContraction.homotopy = 0 := by
    rw [cobarBarContraction, castContraction_homotopy, LinearSpecialContraction.perturb_homotopy,
      LinearMap.comp_sub, ← LinearMap.comp_assoc, hεh, LinearMap.zero_comp, sub_zero]
  exact LinearMap.congr_fun hh x

end TauCeti.AInfinityAlgebra
