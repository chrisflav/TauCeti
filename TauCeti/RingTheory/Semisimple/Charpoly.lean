/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.RingTheory.CompositionSeries.Multiplicity
-- Non-public: `Polynomial.rootMultiplicity_mul` and `rootMultiplicity_X_sub_C_pow` extract
-- multiplicities from characteristic polynomials of Jacobson-density idempotent actions.
import Mathlib.Algebra.Polynomial.RingDivision
-- Non-public: `isArtinian_of_tower` upgrades `FiniteDimensional k M` to `IsArtinian A M`.
import Mathlib.RingTheory.Artinian.Module
-- Non-public: `isNoetherian_of_tower` upgrades `FiniteDimensional k M` to `IsNoetherian A M`.
import Mathlib.RingTheory.Noetherian.Basic
-- Non-public: `Fintype.sum_ite_eq_card_nsmul` evaluates constant-dimension sums over matching
-- composition factors.
import TauCeti.Data.Fintype.BigOperators
-- Non-public: `LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ` splits characteristic
-- polynomials across invariant submodules and quotients.
import TauCeti.LinearAlgebra.Charpoly.Quotient
-- Non-public: `LinearMap.trace_eq_add_of_exact` splits traces across short exact sequences.
import TauCeti.LinearAlgebra.Trace.Exact
-- Non-public: `LinearMap.trace_pi` splits traces across finite products.
import TauCeti.LinearAlgebra.Trace.Pi
-- Non-public: `Algebra.pi_lsmul_surjective_of_forall_end_eq_smul` gives multi-factor density.
import TauCeti.RingTheory.Semisimple.DoubleCentralizer
-- Non-public: `jordanHolderMultiplicity_pi_eq_natCard` and
-- `IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq` classify semisimple
-- modules by their Jordan–Hölder multiplicities.
import TauCeti.RingTheory.Semisimple.Multiplicity
-- Non-public: `TauCeti.endAlgEquivSelfOfIsSimpleModule` supplies scalar commutants over an
-- algebraically closed field.
import TauCeti.RingTheory.Semisimple.Schur
-- Non-public: `IsSimpleModule.congr` and `isSimpleModule_iff_quot_maximal` transport simplicity
-- and present simple factors as quotients of `A`.
import TauCeti.RingTheory.SimpleModule.Basic
-- Non-public: `IsSemisimpleModule.exists_forall_smul_eq_ite` isolates a single simple isomorphism
-- class in a finite semisimple module.
import TauCeti.RingTheory.SimpleModule.Isotypic

/-!
# Characteristic polynomials, traces, and composition factors of modules

Let `A` be an algebra over a field `k` and let `M` be a finite-dimensional `A`-module. Along a
composition series of `M`, the characteristic polynomial of the action of any `a : A` multiplies
over the composition factors (`TauCeti.charpoly_lsmul_eq_prod_compositionSeries`), and its trace
adds (`TauCeti.trace_lsmul_eq_sum_compositionSeries`). Consequently both invariants depend only on
the Jordan–Hölder multiplicities of `M`, and coincide with those of the finite product of its
composition factors.

This file proves the converse in **arbitrary characteristic**: two finite-dimensional `A`-modules
`M` and `N` have the same Jordan–Hölder multiplicities if and only if every `a : A` acts on them
with the same characteristic polynomial
(`TauCeti.jordanHolderMultiplicity_eq_iff_charpoly_lsmul_eq`).
For semisimple modules this yields the module-level Brauer–Nesbitt theorem: finite-dimensional
semisimple `A`-modules with equal characteristic polynomials on `A` are isomorphic
(`IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_lsmul_eq`). No finiteness of `A` and no
characteristic assumption on `k` are needed.

The proof isolates one simple isomorphism class `S` at a time via Jacobson density
(`IsSemisimpleModule.exists_forall_smul_eq_ite`) applied to the product of the semisimplifications
of `M` and `N`. The resulting element `a : A` acts as the identity on factors isomorphic to `S` and
as zero on all others, so its characteristic polynomial is `(X - 1) ^ (m * dim S) * X ^ r`, where
`m = [M : S]`. Taking `Polynomial.rootMultiplicity 1` recovers `m * dim S` in `ℕ` rather than in
`k`, avoiding division by the characteristic of `k`.

Over an algebraically closed field `k`, combining multi-factor Jacobson density
(`Algebra.pi_lsmul_surjective_of_forall_end_eq_smul`) with Schur's lemma gives Burnside–Wedderburn
surjectivity `A → ∏ i, End_k (T i)` (`Algebra.pi_lsmul_surjective_of_isAlgClosed`). Applying
this to a rank-one projection of trace `1` on a single simple factor shows that equal trace
functions on `A` force equal Jordan–Hölder multiplicities modulo the characteristic of `k`
(`TauCeti.natCast_jordanHolderMultiplicity_eq_of_trace_lsmul_eq`).

## Main results

* `TauCeti.charpoly_lsmul_eq_prod_compositionSeries`: the characteristic polynomial of `a : A` on
  `M` is the product of its characteristic polynomials on the composition factors.
* `TauCeti.trace_lsmul_eq_sum_compositionSeries`: the trace of `a : A` on `M` is the sum of its
  traces on the composition factors.
* `TauCeti.jordanHolderMultiplicity_le_finrank`: every Jordan–Hölder multiplicity of `M` is at
  most `Module.finrank k M`.
* `TauCeti.jordanHolderMultiplicity_eq_of_charpoly_lsmul_eq` and
  `TauCeti.jordanHolderMultiplicity_eq_iff_charpoly_lsmul_eq`: finite-dimensional `A`-modules over
  any field have the same Jordan–Hölder multiplicities if and only if every `a : A` acts on them
  with the same characteristic polynomial.
* `IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_lsmul_eq` and
  `IsSemisimpleModule.nonempty_linearEquiv_iff_charpoly_lsmul_eq`: finite-dimensional semisimple
  `A`-modules over any field are isomorphic if and only if every `a : A` acts on them with the same
  characteristic polynomial.
* `Algebra.pi_lsmul_surjective_of_isAlgClosed`: over an algebraically closed field, the diagonal
  action of `A` on finitely many pairwise non-isomorphic finite-dimensional simple modules is
  surjective onto the product of their `k`-endomorphism algebras.
* `TauCeti.natCast_jordanHolderMultiplicity_eq_of_trace_lsmul_eq`: over an algebraically closed
  field, finite-dimensional `A`-modules with equal trace functions on `A` have the same
  Jordan–Hölder multiplicities in `k` (i.e. modulo `char k`).

## References

* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §30, Theorem 30.16 (Brauer–Nesbitt theorem).
* S. Lang, *Algebra*, revised third edition, Chapter XVII, §3.
-/

public section

open Module Polynomial

namespace TauCeti

/-! ### Characteristic polynomials and traces on quotients, products, and composition series -/

section CompositionSeries

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {M N : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

private theorem finite_submodule [FiniteDimensional k M] (p : Submodule A M) :
    FiniteDimensional k p :=
  .of_injective (p.subtype.restrictScalars k) Subtype.val_injective

private theorem finite_quotient [FiniteDimensional k M] (p : Submodule A M) :
    FiniteDimensional k (M ⧸ p) :=
  .of_surjective (p.mkQ.restrictScalars k) p.mkQ_surjective

private theorem finite_subquotient [FiniteDimensional k M]
    (s : CompositionSeries (Submodule A M)) (i : Fin s.length) :
    FiniteDimensional k
      (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) :=
  have := finite_submodule (k := k) (s i.succ)
  finite_quotient (k := k) (Submodule.comap (s i.succ).subtype (s i.castSucc))

private theorem charpoly_lsmul_eq_of_linearEquiv [FiniteDimensional k M] [FiniteDimensional k N]
    (e : M ≃ₗ[A] N) (a : A) :
    (Algebra.lsmul k k M a).charpoly = (Algebra.lsmul k k N a).charpoly := by
  have hconj : (e.restrictScalars k).conj (Algebra.lsmul k k M a) = Algebra.lsmul k k N a := by
    ext y
    simp
  rw [← hconj, LinearEquiv.charpoly_conj]

private theorem trace_lsmul_eq_of_linearEquiv (e : M ≃ₗ[A] N) (a : A) :
    LinearMap.trace k M (Algebra.lsmul k k M a) = LinearMap.trace k N (Algebra.lsmul k k N a) := by
  have hconj : (e.restrictScalars k).conj (Algebra.lsmul k k M a) = Algebra.lsmul k k N a := by
    ext y
    simp
  rw [← hconj, LinearMap.trace_conj']

private theorem charpoly_lsmul_eq_mul_quotient [FiniteDimensional k M] (p : Submodule A M)
    [FiniteDimensional k p] [FiniteDimensional k (M ⧸ p)] (a : A) :
    (Algebra.lsmul k k M a).charpoly =
      (Algebra.lsmul k k p a).charpoly * (Algebra.lsmul k k (M ⧸ p) a).charpoly := by
  let W : Submodule k M := p.restrictScalars k
  have hW : W ≤ W.comap (Algebra.lsmul k k M a) := fun x hx ↦ p.smul_mem a hx
  have hchar := LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W
    (Algebra.lsmul k k M a) hW
  let e₁ : W ≃ₗ[k] p :=
    { toFun := id
      invFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e₂ : (M ⧸ W) ≃ₗ[k] (M ⧸ p) := Submodule.Quotient.restrictScalarsEquiv k p
  have h₁ : e₁.conj ((Algebra.lsmul k k M a).restrict hW) = Algebra.lsmul k k p a := by
    ext x
    rfl
  have h₂ : e₂.conj (W.mapQ W (Algebra.lsmul k k M a) hW) = Algebra.lsmul k k (M ⧸ p) a := by
    refine LinearMap.ext fun q ↦ Submodule.Quotient.induction_on p q fun x ↦ ?_
    rfl
  rw [hchar, ← h₁, ← h₂, e₁.charpoly_conj, e₂.charpoly_conj]

private theorem trace_lsmul_eq_add_quotient [FiniteDimensional k M] (p : Submodule A M) (a : A) :
    LinearMap.trace k M (Algebra.lsmul k k M a) =
      LinearMap.trace k p (Algebra.lsmul k k p a) +
        LinearMap.trace k (M ⧸ p) (Algebra.lsmul k k (M ⧸ p) a) := by
  have hex : Function.Exact (p.subtype.restrictScalars k) (p.mkQ.restrictScalars k) := by
    rw [LinearMap.exact_iff]
    ext x
    simp
  exact LinearMap.trace_eq_add_of_exact Subtype.val_injective p.mkQ_surjective hex
    (by ext x; rfl) (by ext x; rfl)

private theorem charpoly_lsmul_pi :
    ∀ {ι : Type*} [Fintype ι] (P : ι → Type*)
      [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)] [∀ i, Module A (P i)]
      [∀ i, IsScalarTower k A (P i)] [∀ i, FiniteDimensional k (P i)] (a : A),
      (Algebra.lsmul k k (∀ i, P i) a).charpoly =
        ∏ i, (Algebra.lsmul k k (P i) a).charpoly := by
  apply Fintype.induction_empty_option
  · intro α β _ e IH P _ _ _ _ _ a
    let _ : Fintype α := .ofEquiv β e.symm
    rw [← charpoly_lsmul_eq_of_linearEquiv (LinearEquiv.piCongrLeft A P e) a, IH,
      e.prod_comp (fun j ↦ (Algebra.lsmul k k (P j) a).charpoly)]
  · intro P _ _ _ _ _ a
    have hzero : Algebra.lsmul k k (∀ i : PEmpty, P i) a = 0 := Subsingleton.elim _ _
    rw [hzero, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero,
      Fintype.prod_empty]
  · intro ι _ IH P _ _ _ _ _ a
    have hconj : (LinearEquiv.piOptionEquivProd k (M := P)).conj
        (Algebra.lsmul k k (∀ i, P i) a) =
        (Algebra.lsmul k k (P none) a).prodMap (Algebra.lsmul k k (∀ i, P (some i)) a) :=
      LinearMap.ext fun _ ↦ Prod.ext rfl rfl
    rw [← (LinearEquiv.piOptionEquivProd k (M := P)).charpoly_conj, hconj,
      LinearMap.charpoly_prodMap, IH, Fintype.prod_option]

private theorem trace_lsmul_pi {ι : Type*} [Fintype ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)] [∀ i, Module A (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, FiniteDimensional k (P i)] (a : A) :
    LinearMap.trace k (∀ i, P i) (Algebra.lsmul k k (∀ i, P i) a) =
      ∑ i, LinearMap.trace k (P i) (Algebra.lsmul k k (P i) a) := by
  classical
  rw [LinearMap.trace_pi]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (LinearMap.trace k (P i)) ?_
  ext x
  simp

/-- Equal pairs of submodules yield isomorphic subquotients. -/
private def subquotientCongr {p₁ p₂ q₁ q₂ : Submodule A M} (hp : p₁ = p₂)
    (hq : q₁ = q₂) :
    (↥p₁ ⧸ Submodule.comap p₁.subtype q₁) ≃ₗ[A]
      (↥p₂ ⧸ Submodule.comap p₂.subtype q₂) := by
  subst hp hq
  exact LinearEquiv.refl A _

private theorem prod_fin_snoc {β : Type*} [CommMonoid β]
    (s : CompositionSeries (Submodule A M)) (x : Submodule A M)
    (hx : JordanHolderLattice.IsMaximal s.last x) (f : Fin (s.snoc x hx).length → β) :
    ∏ i, f i =
      (∏ i : Fin s.length, f (i.castSucc.cast (RelSeries.snoc_length s x hx).symm)) *
        f ((Fin.last s.length).cast (RelSeries.snoc_length s x hx).symm) := by
  rw [← (finCongr (RelSeries.snoc_length s x hx)).symm.prod_comp, Fin.prod_univ_castSucc]
  rfl

private theorem sum_fin_snoc {β : Type*} [AddCommMonoid β]
    (s : CompositionSeries (Submodule A M)) (x : Submodule A M)
    (hx : JordanHolderLattice.IsMaximal s.last x) (f : Fin (s.snoc x hx).length → β) :
    ∑ i, f i =
      (∑ i : Fin s.length, f (i.castSucc.cast (RelSeries.snoc_length s x hx).symm)) +
        f ((Fin.last s.length).cast (RelSeries.snoc_length s x hx).symm) := by
  rw [← (finCongr (RelSeries.snoc_length s x hx)).symm.sum_comp, Fin.sum_univ_castSucc]
  rfl

private theorem snoc_castSucc_succ (s : CompositionSeries (Submodule A M)) (x : Submodule A M)
    (hx : JordanHolderLattice.IsMaximal s.last x) (i : Fin s.length) :
    (s.snoc x hx) ((i.castSucc.cast (RelSeries.snoc_length s x hx).symm).succ) = s i.succ := by
  have heq : (i.castSucc.cast (RelSeries.snoc_length s x hx).symm).succ =
      Fin.cast (by simp) i.succ.castSucc := Fin.ext (by simp)
  rw [heq]
  exact RelSeries.snoc_cast_castSucc s x hx i.succ

private theorem snoc_castSucc_castSucc (s : CompositionSeries (Submodule A M)) (x : Submodule A M)
    (hx : JordanHolderLattice.IsMaximal s.last x) (i : Fin s.length) :
    (s.snoc x hx) ((i.castSucc.cast (RelSeries.snoc_length s x hx).symm).castSucc) =
      s i.castSucc := by
  have heq : (i.castSucc.cast (RelSeries.snoc_length s x hx).symm).castSucc =
      Fin.cast (by simp) i.castSucc.castSucc := Fin.ext (by simp)
  rw [heq]
  exact RelSeries.snoc_cast_castSucc s x hx i.castSucc

private theorem snoc_last_succ (s : CompositionSeries (Submodule A M)) (x : Submodule A M)
    (hx : JordanHolderLattice.IsMaximal s.last x) :
    (s.snoc x hx) (((Fin.last s.length).cast (RelSeries.snoc_length s x hx).symm).succ) = x := by
  have heq : ((Fin.last s.length).cast (RelSeries.snoc_length s x hx).symm).succ =
      Fin.last (s.snoc x hx).length := Fin.ext (by simp [RelSeries.snoc_length])
  rw [heq]
  exact RelSeries.last_snoc s x hx

private theorem snoc_last_castSucc (s : CompositionSeries (Submodule A M)) (x : Submodule A M)
    (hx : JordanHolderLattice.IsMaximal s.last x) :
    (s.snoc x hx) (((Fin.last s.length).cast (RelSeries.snoc_length s x hx).symm).castSucc) =
      s.last := by
  have heq : ((Fin.last s.length).cast (RelSeries.snoc_length s x hx).symm).castSucc =
      Fin.cast (by simp) (Fin.last s.length).castSucc := Fin.ext (by simp)
  rw [heq]
  exact RelSeries.snoc_cast_castSucc s x hx (Fin.last s.length)

private theorem charpoly_lsmul_last_eq_prod [FiniteDimensional k M]
    (s : CompositionSeries (Submodule A M)) (a : A) :
    ∀ (_ : s.head = ⊥) [FiniteDimensional k s.last]
      [∀ i : Fin s.length,
        FiniteDimensional k (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc))],
      (Algebra.lsmul k k s.last a).charpoly =
        ∏ i : Fin s.length,
          (Algebra.lsmul k k
            (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) a).charpoly := by
  induction s using RelSeries.inductionOn' with
  | singleton x =>
    intro hbot _ _
    have hx : x = ⊥ := hbot
    subst hx
    have : Subsingleton (RelSeries.singleton
        {(u, v) | JordanHolderLattice.IsMaximal u v} (⊥ : Submodule A M)).last := by
      rw [RelSeries.last_singleton]; infer_instance
    have hzero : Algebra.lsmul k k
        (RelSeries.singleton {(u, v) | JordanHolderLattice.IsMaximal u v}
          (⊥ : Submodule A M)).last a = 0 := Subsingleton.elim _ _
    rw [hzero, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero]
    simp
  | snoc s x hx ih =>
    intro hbot _ _
    have hsbot : s.head = ⊥ := by simpa using hbot
    have := finite_submodule (k := k) x
    have := finite_submodule (k := k) s.last
    have := finite_submodule (k := k) (Submodule.comap x.subtype s.last)
    have := finite_quotient (k := k) (Submodule.comap x.subtype s.last)
    have : ∀ i : Fin s.length,
        FiniteDimensional k (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) :=
      fun i ↦ finite_subquotient (k := k) s i
    rw [prod_fin_snoc]
    have hfac (i : Fin s.length) := charpoly_lsmul_eq_of_linearEquiv (k := k)
      (subquotientCongr (snoc_castSucc_succ s x hx i) (snoc_castSucc_castSucc s x hx i)) a
    have hlast := charpoly_lsmul_eq_of_linearEquiv (k := k)
      (subquotientCongr (snoc_last_succ s x hx) (snoc_last_castSucc s x hx)) a
    rw [Finset.prod_congr rfl fun i _ ↦ hfac i, hlast, ← ih hsbot,
      charpoly_lsmul_eq_of_linearEquiv
        (LinearEquiv.ofEq (s.snoc x hx).last x (RelSeries.last_snoc s x hx)) a,
      charpoly_lsmul_eq_mul_quotient (Submodule.comap x.subtype s.last) a,
      charpoly_lsmul_eq_of_linearEquiv (Submodule.comapSubtypeEquivOfLe hx.le) a]

/-- **Characteristic polynomials multiply along a composition series.** For any composition series
of a finite-dimensional `A`-module `M`, the characteristic polynomial of `a : A` on `M` is the
product of its characteristic polynomials on the composition factors.

The `FiniteDimensional k` hypothesis on the subquotients follows automatically from
`FiniteDimensional k M`, and is a binder here only because `LinearMap.charpoly` carries it in its
signature. -/
theorem charpoly_lsmul_eq_prod_compositionSeries [FiniteDimensional k M]
    (s : CompositionSeries (Submodule A M)) (hbot : s.head = ⊥) (htop : s.last = ⊤)
    [∀ i : Fin s.length,
      FiniteDimensional k (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc))]
    (a : A) :
    (Algebra.lsmul k k M a).charpoly =
      ∏ i : Fin s.length,
        (Algebra.lsmul k k
          (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) a).charpoly := by
  have := finite_submodule (k := k) s.last
  rw [← charpoly_lsmul_last_eq_prod s a hbot]
  exact charpoly_lsmul_eq_of_linearEquiv
    ((LinearEquiv.ofEq s.last ⊤ htop).trans Submodule.topEquiv).symm a

private theorem trace_lsmul_last_eq_sum [FiniteDimensional k M]
    (s : CompositionSeries (Submodule A M)) (hbot : s.head = ⊥) (a : A) :
    LinearMap.trace k s.last (Algebra.lsmul k k s.last a) =
      ∑ i : Fin s.length,
        LinearMap.trace k
          (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc))
          (Algebra.lsmul k k
            (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) a) := by
  induction s using RelSeries.inductionOn' with
  | singleton x =>
    have hx : x = ⊥ := hbot
    subst hx
    have : Subsingleton (RelSeries.singleton
        {(u, v) | JordanHolderLattice.IsMaximal u v} (⊥ : Submodule A M)).last := by
      rw [RelSeries.last_singleton]; infer_instance
    have hzero : Algebra.lsmul k k
        (RelSeries.singleton {(u, v) | JordanHolderLattice.IsMaximal u v}
          (⊥ : Submodule A M)).last a = 0 := Subsingleton.elim _ _
    simp [hzero]
  | snoc s x hx ih =>
    have hsbot : s.head = ⊥ := by simpa using hbot
    have := finite_submodule (k := k) x
    rw [sum_fin_snoc]
    have hfac (i : Fin s.length) := trace_lsmul_eq_of_linearEquiv (k := k)
      (subquotientCongr (snoc_castSucc_succ s x hx i) (snoc_castSucc_castSucc s x hx i)) a
    have hlast := trace_lsmul_eq_of_linearEquiv (k := k)
      (subquotientCongr (snoc_last_succ s x hx) (snoc_last_castSucc s x hx)) a
    rw [Finset.sum_congr rfl fun i _ ↦ hfac i, hlast, ← ih hsbot,
      trace_lsmul_eq_of_linearEquiv
        (LinearEquiv.ofEq (s.snoc x hx).last x (RelSeries.last_snoc s x hx)) a,
      trace_lsmul_eq_add_quotient (Submodule.comap x.subtype s.last) a,
      trace_lsmul_eq_of_linearEquiv (Submodule.comapSubtypeEquivOfLe hx.le) a]

/-- **Traces add along a composition series.** For any composition series of a finite-dimensional
`A`-module `M`, the trace of `a : A` on `M` is the sum of its traces on the composition factors. -/
theorem trace_lsmul_eq_sum_compositionSeries [FiniteDimensional k M]
    (s : CompositionSeries (Submodule A M)) (hbot : s.head = ⊥) (htop : s.last = ⊤) (a : A) :
    LinearMap.trace k M (Algebra.lsmul k k M a) =
      ∑ i : Fin s.length,
        LinearMap.trace k
          (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc))
          (Algebra.lsmul k k
            (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) a) := by
  rw [← trace_lsmul_last_eq_sum s hbot a]
  exact trace_lsmul_eq_of_linearEquiv
    ((LinearEquiv.ofEq s.last ⊤ htop).trans Submodule.topEquiv).symm a

private theorem finrank_last_eq_sum [FiniteDimensional k M]
    (s : CompositionSeries (Submodule A M)) (hbot : s.head = ⊥) :
    Module.finrank k s.last =
      ∑ i : Fin s.length,
        Module.finrank k (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) := by
  induction s using RelSeries.inductionOn' with
  | singleton x =>
    have hx : x = ⊥ := hbot
    subst hx
    rw [RelSeries.last_singleton]
    exact Module.finrank_zero_of_subsingleton
  | snoc s x hx ih =>
    have hsbot : s.head = ⊥ := by simpa using hbot
    have := finite_submodule (k := k) x
    rw [sum_fin_snoc]
    have hfac (i : Fin s.length) :=
      ((subquotientCongr (snoc_castSucc_succ s x hx i)
        (snoc_castSucc_castSucc s x hx i)).restrictScalars k).finrank_eq
    have hlast :=
      ((subquotientCongr (snoc_last_succ s x hx)
        (snoc_last_castSucc s x hx)).restrictScalars k).finrank_eq
    rw [Finset.sum_congr rfl fun i _ ↦ hfac i, hlast, ← ih hsbot, RelSeries.last_snoc]
    let p : Submodule A x := Submodule.comap x.subtype s.last
    have hdim := Submodule.finrank_quotient_add_finrank (p.restrictScalars k)
    have hq : Module.finrank k (x ⧸ p.restrictScalars k) = Module.finrank k (x ⧸ p) :=
      (Submodule.Quotient.restrictScalarsEquiv k p).finrank_eq
    have hp : Module.finrank k (p.restrictScalars k) = Module.finrank k s.last :=
      ((Submodule.comapSubtypeEquivOfLe hx.le).restrictScalars k).finrank_eq
    rw [hq, hp, add_comm] at hdim
    exact hdim.symm

/-- **Jordan–Hölder multiplicities are bounded by the dimension.** Every composition factor of a
finite-dimensional `A`-module is nontrivial and hence contributes at least `1` to `finrank k M`,
so the composition length — and in particular every Jordan–Hölder multiplicity — is at most
`Module.finrank k M`. -/
theorem jordanHolderMultiplicity_le_finrank [FiniteDimensional k M]
    [IsNoetherian A M] [IsArtinian A M]
    (S : Type*) [AddCommGroup S] [Module A S] :
    jordanHolderMultiplicity A M S ≤ Module.finrank k M := by
  obtain ⟨s, hbot, htop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian A M
  rw [← compositionMultiplicity_eq_jordanHolderMultiplicity s hbot htop S]
  refine (compositionMultiplicity_le_length s S).trans ?_
  have hM : Module.finrank k M =
      ∑ i : Fin s.length,
        Module.finrank k (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) := by
    rw [← finrank_last_eq_sum s hbot]
    exact (((LinearEquiv.ofEq s.last ⊤ htop).trans
      Submodule.topEquiv).restrictScalars k).finrank_eq.symm
  rw [hM]
  calc s.length = ∑ _i : Fin s.length, 1 := by simp
    _ ≤ ∑ i : Fin s.length,
          Module.finrank k
            (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have := finite_subquotient (k := k) s i
        have : IsSimpleModule A
            (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) :=
          isSimpleModule_subquotient s i
        have : Nontrivial (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) :=
          IsSimpleModule.nontrivial A _
        exact Module.finrank_pos

end CompositionSeries

/-! ### Characteristic polynomials determine Jordan–Hölder multiplicities -/

section CharpolyDetermination

universe u v w

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]
variable {M : Type v} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable {N : Type w} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

private theorem rootMultiplicity_finset_prod {ι : Type*} (s : Finset ι) (p : ι → k[X])
    (hp : ∀ i ∈ s, p i ≠ 0) (r : k) :
    Polynomial.rootMultiplicity r (∏ i ∈ s, p i) =
      ∑ i ∈ s, Polynomial.rootMultiplicity r (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hpi : p i ≠ 0 := hp i (Finset.mem_insert_self i s)
    have hps : ∏ j ∈ s, p j ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj ↦ hp j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hpi hps),
      ih fun j hj ↦ hp j (Finset.mem_insert_of_mem hj)]

open scoped Classical in
private theorem smul_eq_ite_of_injective {X : Type*} [AddCommGroup X] [Module A X]
    {S : Type*} [AddCommGroup S] [Module A S] {a : A}
    (ha : ∀ T : Submodule A X, IsSimpleModule A T → ∀ x ∈ T,
      a • x = if Nonempty (T ≃ₗ[A] S) then x else 0)
    {Y : Type*} [AddCommGroup Y] [Module A Y] [IsSimpleModule A Y]
    (f : Y →ₗ[A] X) (hf : Function.Injective f) (y : Y) :
    a • y = if Nonempty (S ≃ₗ[A] Y) then y else 0 := by
  let e := LinearEquiv.ofInjective f hf
  have hT : IsSimpleModule A (LinearMap.range f) := IsSimpleModule.congr e.symm
  have hiff : Nonempty (LinearMap.range f ≃ₗ[A] S) ↔ Nonempty (S ≃ₗ[A] Y) :=
    ⟨fun ⟨e'⟩ ↦ ⟨e'.symm.trans e.symm⟩, fun ⟨e'⟩ ↦ ⟨(e'.trans e).symm⟩⟩
  have hy := ha _ hT (f y) (LinearMap.mem_range_self f y)
  rw [← map_smul, hiff] at hy
  apply hf
  split_ifs at hy ⊢ <;> simpa using hy

open scoped Classical in
private theorem rootMultiplicity_one_charpoly_lsmul_pi {X : Type*} [AddCommGroup X] [Module A X]
    {S : Type*} [AddCommGroup S] [Module A S] {a : A}
    (ha : ∀ T : Submodule A X, IsSimpleModule A T → ∀ x ∈ T,
      a • x = if Nonempty (T ≃ₗ[A] S) then x else 0)
    {ι : Type*} [Fintype ι] (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)] [∀ i, Module A (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, FiniteDimensional k (P i)]
    [∀ i, IsSimpleModule A (P i)]
    (j : (∀ i, P i) →ₗ[A] X) (hj : Function.Injective j) :
    Polynomial.rootMultiplicity 1 (Algebra.lsmul k k (∀ i, P i) a).charpoly =
      ∑ i, if Nonempty (S ≃ₗ[A] P i) then Module.finrank k (P i) else 0 := by
  rw [charpoly_lsmul_pi P a, rootMultiplicity_finset_prod _ _ fun i _ ↦
    (Algebra.lsmul k k (P i) a).charpoly_monic.ne_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hact (y : P i) : a • y = if Nonempty (S ≃ₗ[A] P i) then y else 0 :=
    smul_eq_ite_of_injective ha (j ∘ₗ LinearMap.single A P i)
      (hj.comp fun _ _ h ↦ Pi.single_injective i h) y
  split_ifs with hi
  · have hone : Algebra.lsmul k k (P i) a = 1 :=
      LinearMap.ext fun y ↦ by simpa [hi] using hact y
    rw [hone, LinearMap.charpoly_one, ← C_1, Polynomial.rootMultiplicity_X_sub_C_pow]
  · have hzero : Algebra.lsmul k k (P i) a = 0 :=
      LinearMap.ext fun y ↦ by simpa [hi] using hact y
    rw [hzero, LinearMap.charpoly_zero]
    refine Polynomial.rootMultiplicity_eq_zero ?_
    simp [Polynomial.IsRoot]

omit [Field k] [Algebra k A] [Module k M] [IsScalarTower k A M] in
private theorem jordanHolderMultiplicity_eq_pi_compositionSeries
    [IsNoetherian A M] [IsArtinian A M]
    (s : CompositionSeries (Submodule A M)) (hbot : s.head = ⊥) (htop : s.last = ⊤)
    (S : Type*) [AddCommGroup S] [Module A S] :
    let F (i : Fin s.length) := ↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)
    have : ∀ i, IsSimpleModule A (F i) := fun i ↦ isSimpleModule_subquotient s i
    jordanHolderMultiplicity A (∀ i, F i) S = jordanHolderMultiplicity A M S := by
  intro F hF
  rw [jordanHolderMultiplicity_pi_eq_natCard,
    ← compositionMultiplicity_eq_jordanHolderMultiplicity s hbot htop S,
    compositionMultiplicity_def]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun i ↦ ?_)
  rw [isCompositionFactorAt_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩

private theorem exists_pos_finrank_eq_of_exists_linearEquiv
    {ι κ : Type*} (P : ι → Type*) (Q : κ → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)] [∀ i, Module A (P i)]
    [∀ i, IsScalarTower k A (P i)] [∀ i, FiniteDimensional k (P i)]
    [∀ i, IsSimpleModule A (P i)]
    [∀ j, AddCommGroup (Q j)] [∀ j, Module k (Q j)] [∀ j, Module A (Q j)]
    [∀ j, IsScalarTower k A (Q j)] [∀ j, FiniteDimensional k (Q j)]
    [∀ j, IsSimpleModule A (Q j)]
    {S : Type*} [AddCommGroup S] [Module A S]
    (hoccur : (∃ i, Nonempty (S ≃ₗ[A] P i)) ∨ ∃ j, Nonempty (S ≃ₗ[A] Q j)) :
    ∃ d : ℕ, 0 < d ∧
      (∀ i, Nonempty (S ≃ₗ[A] P i) → Module.finrank k (P i) = d) ∧
      ∀ j, Nonempty (S ≃ₗ[A] Q j) → Module.finrank k (Q j) = d := by
  rcases hoccur with ⟨i₀, ⟨e₀⟩⟩ | ⟨j₀, ⟨e₀⟩⟩
  · have : Nontrivial (P i₀) := IsSimpleModule.nontrivial A _
    exact ⟨_, Module.finrank_pos,
      fun i ⟨e⟩ ↦ ((e.symm.trans e₀).restrictScalars k).finrank_eq,
      fun j ⟨e⟩ ↦ ((e.symm.trans e₀).restrictScalars k).finrank_eq⟩
  · have : Nontrivial (Q j₀) := IsSimpleModule.nontrivial A _
    exact ⟨_, Module.finrank_pos,
      fun i ⟨e⟩ ↦ ((e.symm.trans e₀).restrictScalars k).finrank_eq,
      fun j ⟨e⟩ ↦ ((e.symm.trans e₀).restrictScalars k).finrank_eq⟩

/-- **Characteristic polynomials determine Jordan–Hölder multiplicities**, over an arbitrary
field. If every element of `A` acts with the same characteristic polynomial on two
finite-dimensional `A`-modules `M` and `N`, then `M` and `N` have the same Jordan–Hölder
multiplicity for every module `S` (in any universe). Neither semisimplicity nor any restriction on
the characteristic of `k` is needed. -/
theorem jordanHolderMultiplicity_eq_of_charpoly_lsmul_eq
    [FiniteDimensional k M] [IsNoetherian A M] [IsArtinian A M]
    [FiniteDimensional k N] [IsNoetherian A N] [IsArtinian A N]
    (h : ∀ a : A, (Algebra.lsmul k k M a).charpoly = (Algebra.lsmul k k N a).charpoly)
    (S : Type*) [AddCommGroup S] [Module A S] :
    jordanHolderMultiplicity A M S = jordanHolderMultiplicity A N S := by
  classical
  by_cases hS : IsSimpleModule A S
  swap
  · rw [jordanHolderMultiplicity_eq_zero_of_not_isSimpleModule S hS,
      jordanHolderMultiplicity_eq_zero_of_not_isSimpleModule S hS]
  obtain ⟨s, hsbot, hstop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian A M
  obtain ⟨t, htbot, httop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian A N
  let P (i : Fin s.length) := ↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)
  let Q (j : Fin t.length) := ↥(t j.succ) ⧸ Submodule.comap (t j.succ).subtype (t j.castSucc)
  have hP : ∀ i, IsSimpleModule A (P i) := fun i ↦ isSimpleModule_subquotient s i
  have hQ : ∀ j, IsSimpleModule A (Q j) := fun j ↦ isSimpleModule_subquotient t j
  have hPfin : ∀ i, FiniteDimensional k (P i) := fun i ↦ finite_subquotient (k := k) s i
  have hQfin : ∀ j, FiniteDimensional k (Q j) := fun j ↦ finite_subquotient (k := k) t j
  let X := (∀ i, P i) × (∀ j, Q j)
  have : Module.Finite (Module.End A X) X := Module.Finite.of_restrictScalars_finite k _ _
  obtain ⟨a, ha⟩ := IsSemisimpleModule.exists_forall_smul_eq_ite (R := A) (M := X) S
  have ha_eq :
      (Algebra.lsmul k k (∀ i, P i) a).charpoly =
        (Algebra.lsmul k k (∀ j, Q j) a).charpoly := by
    rw [charpoly_lsmul_pi P a, charpoly_lsmul_pi Q a,
      ← charpoly_lsmul_eq_prod_compositionSeries s hsbot hstop a,
      ← charpoly_lsmul_eq_prod_compositionSeries t htbot httop a, h a]
  have hrmM := rootMultiplicity_one_charpoly_lsmul_pi (k := k) ha P
    (LinearMap.inl A (∀ i, P i) (∀ j, Q j)) LinearMap.inl_injective
  have hrmN := rootMultiplicity_one_charpoly_lsmul_pi (k := k) ha Q
    (LinearMap.inr A (∀ i, P i) (∀ j, Q j)) LinearMap.inr_injective
  rw [← jordanHolderMultiplicity_eq_pi_compositionSeries (A := A) s hsbot hstop S,
    ← jordanHolderMultiplicity_eq_pi_compositionSeries (A := A) t htbot httop S,
    jordanHolderMultiplicity_pi_eq_natCard, jordanHolderMultiplicity_pi_eq_natCard]
  by_cases hoccur : (∃ i, Nonempty (S ≃ₗ[A] P i)) ∨ ∃ j, Nonempty (S ≃ₗ[A] Q j)
  · obtain ⟨d, hd, hdP, hdQ⟩ := exists_pos_finrank_eq_of_exists_linearEquiv (k := k) P Q hoccur
    have heq := (hrmM.symm.trans (congrArg (Polynomial.rootMultiplicity 1) ha_eq)).trans hrmN
    rw [Fintype.sum_ite_eq_card_nsmul hdP, Fintype.sum_ite_eq_card_nsmul hdQ,
      smul_eq_mul, smul_eq_mul, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at heq
    exact Nat.eq_of_mul_eq_mul_right hd heq
  · push Not at hoccur
    have : IsEmpty {i // Nonempty (S ≃ₗ[A] P i)} :=
      ⟨fun i ↦ (hoccur.1 i.1).false i.2.some⟩
    have : IsEmpty {j // Nonempty (S ≃ₗ[A] Q j)} :=
      ⟨fun j ↦ (hoccur.2 j.1).false j.2.some⟩
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

/-- **Equal Jordan–Hölder multiplicities are equivalent to equal characteristic polynomials** on
`A`, for finite-dimensional modules over any field. -/
theorem jordanHolderMultiplicity_eq_iff_charpoly_lsmul_eq
    [FiniteDimensional k M] [IsNoetherian A M] [IsArtinian A M]
    [FiniteDimensional k N] [IsNoetherian A N] [IsArtinian A N] :
    (∀ (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      jordanHolderMultiplicity A M S = jordanHolderMultiplicity A N S) ↔
      ∀ a : A, (Algebra.lsmul k k M a).charpoly = (Algebra.lsmul k k N a).charpoly := by
  refine ⟨fun h a ↦ ?_,
    fun h S _ _ _ ↦ jordanHolderMultiplicity_eq_of_charpoly_lsmul_eq h S⟩
  obtain ⟨s, hsbot, hstop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian A M
  obtain ⟨t, htbot, httop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian A N
  let P (i : Fin s.length) := ↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)
  let Q (j : Fin t.length) := ↥(t j.succ) ⧸ Submodule.comap (t j.succ).subtype (t j.castSucc)
  have hP : ∀ i, IsSimpleModule A (P i) := fun i ↦ isSimpleModule_subquotient s i
  have hQ : ∀ j, IsSimpleModule A (Q j) := fun j ↦ isSimpleModule_subquotient t j
  have hPfin : ∀ i, FiniteDimensional k (P i) := fun i ↦ finite_subquotient (k := k) s i
  have hQfin : ∀ j, FiniteDimensional k (Q j) := fun j ↦ finite_subquotient (k := k) t j
  have : Module.Finite A (∀ i, P i) := Module.Finite.of_restrictScalars_finite k A _
  have : Module.Finite A (∀ j, Q j) := Module.Finite.of_restrictScalars_finite k A _
  obtain ⟨e⟩ := IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq
    (R := A) (∀ i, P i) (∀ j, Q j) fun S _ _ _ ↦ by
      rw [jordanHolderMultiplicity_eq_pi_compositionSeries (A := A) s hsbot hstop S,
        jordanHolderMultiplicity_eq_pi_compositionSeries (A := A) t htbot httop S, h S]
  rw [charpoly_lsmul_eq_prod_compositionSeries s hsbot hstop a,
    charpoly_lsmul_eq_prod_compositionSeries t htbot httop a,
    ← charpoly_lsmul_pi P a, ← charpoly_lsmul_pi Q a]
  exact charpoly_lsmul_eq_of_linearEquiv e a

end CharpolyDetermination

end TauCeti

/-! ### Semisimple modules are determined by characteristic polynomials -/

namespace IsSemisimpleModule

section Charpoly

universe u v w

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]
variable (M : Type v) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable (N : Type w) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- **Module-level Brauer–Nesbitt theorem.** Over an algebra `A` over an arbitrary field `k`, two
finite-dimensional semisimple `A`-modules on which every element of `A` acts with the same
characteristic polynomial are isomorphic. No finiteness of `A` and no characteristic assumption on
`k` are needed. -/
theorem nonempty_linearEquiv_of_charpoly_lsmul_eq
    [FiniteDimensional k M] [IsSemisimpleModule A M]
    [FiniteDimensional k N] [IsSemisimpleModule A N]
    (h : ∀ a : A, (Algebra.lsmul k k M a).charpoly = (Algebra.lsmul k k N a).charpoly) :
    Nonempty (M ≃ₗ[A] N) := by
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  exact nonempty_linearEquiv_of_jordanHolderMultiplicity_eq M N fun S _ _ _ ↦
    TauCeti.jordanHolderMultiplicity_eq_of_charpoly_lsmul_eq h S

/-- Two finite-dimensional semisimple `A`-modules over any field are isomorphic if and only if
every element of `A` acts on them with the same characteristic polynomial. -/
theorem nonempty_linearEquiv_iff_charpoly_lsmul_eq
    [FiniteDimensional k M] [IsSemisimpleModule A M]
    [FiniteDimensional k N] [IsSemisimpleModule A N] :
    Nonempty (M ≃ₗ[A] N) ↔
      ∀ a : A, (Algebra.lsmul k k M a).charpoly = (Algebra.lsmul k k N a).charpoly := by
  refine ⟨fun ⟨e⟩ a ↦ ?_, nonempty_linearEquiv_of_charpoly_lsmul_eq M N⟩
  have hconj : (e.restrictScalars k).conj (Algebra.lsmul k k M a) = Algebra.lsmul k k N a := by
    ext y
    simp
  rw [← hconj, LinearEquiv.charpoly_conj]

end Charpoly

end IsSemisimpleModule

/-! ### Burnside–Wedderburn surjectivity and traces modulo the characteristic -/

namespace Algebra

section MultiFactorDensity

/-- **Multi-factor Burnside–Wedderburn surjectivity over an algebraically closed field.** For
finitely many pairwise non-isomorphic finite-dimensional simple modules over an algebra over an
algebraically closed field `k`, the diagonal action `A → ∏ i, End_k (T i)` is surjective. -/
theorem pi_lsmul_surjective_of_isAlgClosed
    {k A ι : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [Finite ι]
    (T : ι → Type*) [∀ i, AddCommGroup (T i)] [∀ i, Module k (T i)] [∀ i, Module A (T i)]
    [∀ i, IsScalarTower k A (T i)] [∀ i, FiniteDimensional k (T i)]
    [∀ i, IsSimpleModule A (T i)]
    (hne : ∀ i j, Nonempty (T i ≃ₗ[A] T j) → i = j) :
    Function.Surjective
      (AlgHom.pi fun i ↦ (Algebra.lsmul k k (T i) : A →ₐ[k] Module.End k (T i))) :=
  pi_lsmul_surjective_of_forall_end_eq_smul T hne fun _ g ↦
    ⟨TauCeti.endAlgEquivSelfOfIsSimpleModule (k := k) g,
      fun x ↦ (TauCeti.endAlgEquivSelfOfIsSimpleModule_smul g x).symm⟩

end MultiFactorDensity

end Algebra

namespace TauCeti

section TraceModP

universe u v w

variable {k : Type*} [Field k] [IsAlgClosed k] {A : Type u} [Ring A] [Algebra k A]
variable {M : Type v} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable {N : Type w} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

omit [IsAlgClosed k] in
/-- A nontrivial finite-dimensional vector space admits an endomorphism of trace `1`. -/
private theorem exists_trace_eq_one {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] :
    ∃ e : Module.End k V, LinearMap.trace k V e = 1 := by
  let b := Module.Free.chooseBasis k V
  have : Nonempty (Module.Free.ChooseBasisIndex k V) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Module.finrank k V = 0 := by
      rw [Module.finrank_eq_card_chooseBasisIndex, Fintype.card_eq_zero]
    exact Module.finrank_pos.ne' this
  let i₀ := Classical.arbitrary (Module.Free.ChooseBasisIndex k V)
  refine ⟨(b.coord i₀).smulRight (b i₀), ?_⟩
  rw [LinearMap.trace_smulRight, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

open scoped Classical in
/-- Given a finite family of finite-dimensional simple quotients `A ⧸ m x` and a simple module `S`
isomorphic to one of them, there exists `a : A` whose trace on `A ⧸ m x` is `1` when
`A ⧸ m x ≅ S` and `0` otherwise. -/
private theorem exists_lsmul_trace_eq_ite {ι : Type*} [Finite ι] (m : ι → Ideal A)
    [∀ x, IsSimpleModule A (A ⧸ m x)] [∀ x, FiniteDimensional k (A ⧸ m x)]
    (S : Type*) [AddCommGroup S] [Module A S]
    (hocc : ∃ x₀ : ι, Nonempty ((A ⧸ m x₀) ≃ₗ[A] S)) :
    ∃ a : A, ∀ x : ι,
      LinearMap.trace k (A ⧸ m x) (Algebra.lsmul k k (A ⧸ m x) a) =
        if Nonempty ((A ⧸ m x) ≃ₗ[A] S) then 1 else 0 := by
  classical
  let r : Setoid ι :=
    { r x y := Nonempty ((A ⧸ m x) ≃ₗ[A] A ⧸ m y)
      iseqv := ⟨fun _ ↦ ⟨LinearEquiv.refl A _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩,
        fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩ }
  let T (q : Quotient r) : Type u := A ⧸ m q.out
  have hT_ne : ∀ q₁ q₂, Nonempty (T q₁ ≃ₗ[A] T q₂) → q₁ = q₂ := by
    intro q₁ q₂ hne
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
    exact Quotient.sound hne
  obtain ⟨x₀, ⟨e₀⟩⟩ := hocc
  let q₀ : Quotient r := Quotient.mk r x₀
  have hq₀ : Nonempty (T q₀ ≃ₗ[A] S) := by
    have heq : Nonempty (T q₀ ≃ₗ[A] A ⧸ m x₀) := Quotient.exact (Quotient.out_eq q₀)
    exact ⟨heq.some.trans e₀⟩
  have : Nontrivial (T q₀) := IsSimpleModule.nontrivial A _
  obtain ⟨eT, heT⟩ := exists_trace_eq_one (k := k) (V := T q₀)
  let g : ∀ q : Quotient r, Module.End k (T q) := fun q ↦ if hq : q = q₀ then hq ▸ eT else 0
  obtain ⟨a, ha⟩ := Algebra.pi_lsmul_surjective_of_isAlgClosed T hT_ne g
  refine ⟨a, fun x ↦ ?_⟩
  have heq : Nonempty ((A ⧸ m x) ≃ₗ[A] T (Quotient.mk r x)) :=
    Quotient.exact (Quotient.out_eq (Quotient.mk r x)).symm
  have haq : Algebra.lsmul k k (T (Quotient.mk r x)) a = g (Quotient.mk r x) := by
    simpa [AlgHom.pi_apply] using congrFun ha (Quotient.mk r x)
  rw [trace_lsmul_eq_of_linearEquiv heq.some a, haq]
  generalize Quotient.mk r x = q at heq ⊢
  dsimp only [g]
  split_ifs with hq hne hne
  · subst hq; exact heT
  · subst hq; exact (hne ⟨heq.some.trans hq₀.some⟩).elim
  · exfalso
    exact hq (hT_ne _ _ ⟨heq.some.symm.trans (hne.some.trans hq₀.some.symm)⟩)
  · simp

omit [IsAlgClosed k] in
open scoped Classical in
private theorem natCast_jordanHolderMultiplicity_eq_trace_of_trace_ite
    [FiniteDimensional k M] [IsNoetherian A M] [IsArtinian A M]
    (s : CompositionSeries (Submodule A M)) (hsbot : s.head = ⊥) (hstop : s.last = ⊤)
    (m : Fin s.length → Ideal A)
    (e : ∀ i, Nonempty
      ((↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) ≃ₗ[A] A ⧸ m i))
    {S : Type*} [AddCommGroup S] [Module A S] {a : A}
    (ha : ∀ i, LinearMap.trace k (A ⧸ m i) (Algebra.lsmul k k (A ⧸ m i) a) =
      if Nonempty ((A ⧸ m i) ≃ₗ[A] S) then 1 else 0) :
    (jordanHolderMultiplicity A M S : k) = LinearMap.trace k M (Algebra.lsmul k k M a) := by
  have htr (i : Fin s.length) :
      LinearMap.trace k (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc))
        (Algebra.lsmul k k _ a) = if IsCompositionFactorAt s i S then 1 else 0 := by
    refine (trace_lsmul_eq_of_linearEquiv (k := k) (e i).some a).trans ((ha i).trans ?_)
    refine if_congr ?_ rfl rfl
    rw [isCompositionFactorAt_iff]
    exact ⟨fun ⟨e'⟩ ↦ ⟨(e i).some.trans e'⟩,
      fun ⟨e'⟩ ↦ ⟨(e i).some.symm.trans e'⟩⟩
  rw [trace_lsmul_eq_sum_compositionSeries (k := k) s hsbot hstop a,
    Finset.sum_congr rfl fun i _ ↦ htr i,
    ← compositionMultiplicity_eq_jordanHolderMultiplicity s hsbot hstop S,
    compositionMultiplicity_eq_sum_ite]
  simp

omit [Field k] [IsAlgClosed k] [Algebra k A] [Module k M] [IsScalarTower k A M] in
private theorem jordanHolderMultiplicity_eq_zero_of_forall_isEmpty_quot
    [IsNoetherian A M] [IsArtinian A M]
    (s : CompositionSeries (Submodule A M)) (hsbot : s.head = ⊥) (hstop : s.last = ⊤)
    (m : Fin s.length → Ideal A)
    (e : ∀ i, Nonempty
      ((↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) ≃ₗ[A] A ⧸ m i))
    {S : Type*} [AddCommGroup S] [Module A S]
    (hnone : ∀ i, IsEmpty ((A ⧸ m i) ≃ₗ[A] S)) :
    jordanHolderMultiplicity A M S = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := (jordanHolderMultiplicity_ne_zero_iff s hsbot hstop S).mp hne
  exact (hnone i).false ((e i).some.symm.trans (isCompositionFactorAt_iff.mp hi).some)

/-- **Equal trace functions determine Jordan–Hölder multiplicities modulo `char k`** over an
algebraically closed field. If every element of `A` acts with the same trace on two
finite-dimensional `A`-modules `M` and `N`, then for every module `S`, the multiplicities `[M : S]`
and `[N : S]` agree in `k`. No semisimplicity assumption is needed. -/
theorem natCast_jordanHolderMultiplicity_eq_of_trace_lsmul_eq
    [FiniteDimensional k M] [IsNoetherian A M] [IsArtinian A M]
    [FiniteDimensional k N] [IsNoetherian A N] [IsArtinian A N]
    (h : ∀ a : A, LinearMap.trace k M (Algebra.lsmul k k M a) =
      LinearMap.trace k N (Algebra.lsmul k k N a))
    (S : Type*) [AddCommGroup S] [Module A S] :
    (jordanHolderMultiplicity A M S : k) = (jordanHolderMultiplicity A N S : k) := by
  classical
  by_cases hS : IsSimpleModule A S
  swap
  · rw [jordanHolderMultiplicity_eq_zero_of_not_isSimpleModule S hS,
      jordanHolderMultiplicity_eq_zero_of_not_isSimpleModule S hS]
  obtain ⟨s, hsbot, hstop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian A M
  obtain ⟨t, htbot, httop⟩ := exists_compositionSeries_of_isNoetherian_isArtinian A N
  have hPfin : ∀ i : Fin s.length, FiniteDimensional k _ :=
    fun i ↦ finite_subquotient (k := k) s i
  have hQfin : ∀ j : Fin t.length, FiniteDimensional k _ :=
    fun j ↦ finite_subquotient (k := k) t j
  choose m₁ hm₁ e₁ using fun i ↦
    isSimpleModule_iff_quot_maximal.mp (isSimpleModule_subquotient s i)
  choose m₂ hm₂ e₂ using fun j ↦
    isSimpleModule_iff_quot_maximal.mp (isSimpleModule_subquotient t j)
  let m : Fin s.length ⊕ Fin t.length → Ideal A := Sum.elim m₁ m₂
  have hm_simple : ∀ x, IsSimpleModule A (A ⧸ m x) := by
    rintro (i | j)
    exacts [isSimpleModule_iff_isCoatom.mpr (hm₁ i).out,
      isSimpleModule_iff_isCoatom.mpr (hm₂ j).out]
  have hm_fin : ∀ x, FiniteDimensional k (A ⧸ m x) := by
    rintro (i | j)
    exacts [Module.Finite.equiv ((e₁ i).some.restrictScalars k),
      Module.Finite.equiv ((e₂ j).some.restrictScalars k)]
  by_cases hocc : ∃ x, Nonempty ((A ⧸ m x) ≃ₗ[A] S)
  · obtain ⟨a, ha⟩ := exists_lsmul_trace_eq_ite (k := k) m S hocc
    rw [natCast_jordanHolderMultiplicity_eq_trace_of_trace_ite s hsbot hstop m₁ e₁
        (fun i ↦ ha (.inl i)),
      natCast_jordanHolderMultiplicity_eq_trace_of_trace_ite t htbot httop m₂ e₂
        (fun j ↦ ha (.inr j)),
      h a]
  · push Not at hocc
    rw [jordanHolderMultiplicity_eq_zero_of_forall_isEmpty_quot s hsbot hstop m₁ e₁
        (fun i ↦ hocc (.inl i)),
      jordanHolderMultiplicity_eq_zero_of_forall_isEmpty_quot t htbot httop m₂ e₂
        (fun j ↦ hocc (.inr j))]

end TraceModP

end TauCeti
