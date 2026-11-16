/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
public import TauCeti.RingTheory.CompositionSeries.Multiplicity
-- Non-public: `charP_of_injective_algebraMap` transports characteristic `p` to the algebraic
-- closure inside the characteristic-`p` trace criterion.
import Mathlib.Algebra.CharP.Algebra
-- Non-public: `AlgebraicClosure` is used only internally to reduce the characteristic-`p` trace
-- criterion to the algebraically closed case before descending back to `k`.
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- Non-public: `LinearMap.charpoly_baseChange` relates characteristic polynomials across field
-- extensions in the descent proofs.
import Mathlib.LinearAlgebra.Charpoly.BaseChange
-- Non-public: `LinearMap.charpoly_of_finrank_eq_two` is used only inside the rank-two trace
-- criterion over fields with trivial unit group.
import TauCeti.LinearAlgebra.Charpoly.FinrankTwo
-- Non-public: Amitsur's theorem is used only to pass from elementwise characteristic polynomials
-- on `Γ` to all of `R[Γ]`.
import TauCeti.LinearAlgebra.Matrix.Charpoly.Amitsur
-- Non-public: `Matrix.charpolyRev_smul` and `Matrix.charpolyRev_eq_charpolyRev_iff` preserve equal
-- characteristic polynomials under scalar multiplication.
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
-- Non-public: `TauCeti.Representation.nonempty_equiv_iff` converts between module isomorphisms on
-- `ρ.asModule` and representation equivalences inside proofs.
import TauCeti.RepresentationTheory.AsModule
-- Non-public: `Representation.trace_asAlgebraHom_eq_of_character_eq` extends equal characters on
-- `Γ` to equal trace functions on `k[Γ]` inside the trace-criterion proofs.
import TauCeti.RepresentationTheory.Semisimple
-- Non-public: module-level Brauer–Nesbitt, multi-factor Burnside–Wedderburn surjectivity, and
-- trace-mod-`p` multiplicity theorems are applied to `ρ.asModule` inside proofs.
import TauCeti.RingTheory.Semisimple.Charpoly

/-!
# The Brauer–Nesbitt theorem for representations

Over an arbitrary field `k` and for an arbitrary monoid `Γ`, two finite-dimensional representations
`ρ` and `σ` of `Γ` whose operators `ρ g` and `σ g` have the same characteristic polynomial for
every `g : Γ` have the same Jordan–Hölder composition multiplicities — in other words,
isomorphic semisimplifications. When `ρ` and `σ` are semisimple, they are therefore equivalent
(`Representation.nonempty_equiv_of_charpoly_eq`); for jointly continuous representations on spaces
with their module topology, the equivalence is automatically an isomorphism of continuous
representations (`TauCeti.ContinuousRep.nonempty_iso_of_charpoly_eq`).

## Proof overview

1. **From `Γ` to `R[Γ]` (`Representation.charpoly_asAlgebraHom_eq_of_charpoly_eq`):** over any
   commutative ring `R`, every `a : R[Γ]` is a finite sum
   `∑ g ∈ a.coeff.support, a.coeff g • MonoidAlgebra.of g`. Every nonempty word product of the
   summands `a.coeff g • ρ g` is a scalar multiple of `ρ l.prod`, so Amitsur's theorem
   (`LinearMap.charpoly_sum_eq_of_forall_list_prod`) propagates equality of characteristic
   polynomials from `Γ` to every element of `R[Γ]`.
2. **Module-level Brauer–Nesbitt (`TauCeti.RingTheory.Semisimple.Charpoly`):** passing to the
   associated `k[Γ]`-modules `ρ.asModule` and `σ.asModule`, equal characteristic polynomials on
   `k[Γ]` determine all Jordan–Hölder multiplicities over any field `k`, and hence determine
   semisimple representations up to equivalence.
3. **Descent along arbitrary field extensions:** if `ρ` and `σ` acquire the same Jordan–Hölder
   multiplicities (or become equivalent) after base change to a field extension `k'`, then their
   characteristic polynomials agree over `k'`; injectivity of `k ↪ k'` pulls equality of
   characteristic polynomials back to `k`, where Brauer–Nesbitt identifies the multiplicities (and
   the representations if semisimple).
4. **Trace criteria in positive characteristic:**
   - Over an algebraically closed field `k`, multi-factor Burnside–Wedderburn surjectivity
     (`Representation.pi_asAlgebraHom_surjective`) implies that equal characters determine
     Jordan–Hölder multiplicities modulo `char k`
     (`Representation.natCast_jordanHolderMultiplicity_eq_of_character_eq`).
   - Over any field `k` of characteristic `p`, if `finrank k V < p` and `finrank k W < p`, every
     multiplicity is strictly less than `p`; passing to `AlgebraicClosure k`, matching
     multiplicities modulo `p` forces exact equality, and descent pulls the conclusion back to `k`.
   - For a group `Γ` and rank-two representations over a field `k` with `Subsingleton kˣ` (such as
     `𝔽₂`), every operator has determinant `1`, so the trace alone determines the quadratic
     characteristic polynomial `X ^ 2 - tr(ρ g) X + 1`.

## Main results

* `Representation.charpoly_asAlgebraHom_eq_of_charpoly_eq`: over any commutative ring `R`, equal
  characteristic polynomials on `Γ` propagate to equal characteristic polynomials on `R[Γ]`.
* `Representation.pi_asAlgebraHom_surjective`: over an algebraically closed field, the diagonal
  algebra action `k[Γ] → ∏ i, End_k (V i)` on finitely many pairwise non-equivalent
  finite-dimensional irreducible representations is surjective.
* `Representation.natCast_jordanHolderMultiplicity_eq_of_character_eq`: over an algebraically
  closed field, finite-dimensional representations with the same character have the same
  Jordan–Hölder multiplicities in `k` (modulo `char k`).
* `Representation.jordanHolderMultiplicity_asModule_eq_of_charpoly_eq` and
  `Representation.jordanHolderMultiplicity_asModule_eq_iff_charpoly_eq`: over any field and for
  any monoid, equal characteristic polynomials on `Γ` are equivalent to equal Jordan–Hölder
  multiplicities.
* `Representation.nonempty_equiv_of_charpoly_eq` and
  `Representation.nonempty_equiv_iff_charpoly_eq`: **the Brauer–Nesbitt theorem** for
  finite-dimensional semisimple representations over any field.
* `Representation.jordanHolderMultiplicity_asModule_eq_of_baseChange`,
  `Representation.nonempty_equiv_of_baseChange_jordanHolderMultiplicity_eq`,
  `Representation.jordanHolderMultiplicity_asModule_eq_of_nonempty_equiv_baseChange`, and
  `Representation.nonempty_equiv_of_nonempty_equiv_baseChange`: descent of Jordan–Hölder
  multiplicities and semisimple equivalence along an arbitrary field extension `k ↪ k'`.
* `Representation.jordanHolderMultiplicity_asModule_eq_of_character_eq_of_finrank_lt_char` and
  `Representation.nonempty_equiv_of_character_eq_of_finrank_lt_char`: trace determination when the
  dimension is strictly smaller than the characteristic `p`.
* `Representation.jordanHolderMultiplicity_asModule_eq_of_character_eq_of_finrank_eq_two` and
  `Representation.nonempty_equiv_of_character_eq_of_finrank_eq_two`: trace determination for
  rank-two group representations over a field with trivial unit group (such as `𝔽₂`).
* `TauCeti.ContinuousRep.nonempty_iso_of_charpoly_eq` and
  `TauCeti.ContinuousRep.nonempty_iso_iff_charpoly_eq`: **the Brauer–Nesbitt theorem for
  continuous representations** carrying their module topology.

## References

* R. Brauer and C. Nesbitt, *On the modular characters of groups*, Annals of Mathematics **42**
  (1941), 556–590.
* G. Chenevier, *The `p`-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, in *Automorphic Forms and Galois Representations*,
  Vol. 1, LMS Lecture Note Series **414** (2014), Cor. 1.14 and Cor. 2.13.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, Proposition 2.6(b).
-/

public section

open Module Polynomial
open scoped MonoidAlgebra TensorProduct

namespace Representation

/-! ### Finite-length instances on `ρ.asModule` -/

/-- If `V` is Noetherian over `R`, then `ρ.asModule` is Noetherian over `R[Γ]`. -/
instance instIsNoetherianAsModule {R Γ V : Type*} [CommSemiring R] [Monoid Γ]
    [AddCommMonoid V] [Module R V] [IsNoetherian R V] (ρ : Representation R Γ V) :
    IsNoetherian R[Γ] ρ.asModule :=
  isNoetherian_of_tower R (isNoetherian_of_linearEquiv ρ.asModuleEquiv.symm)

/-- If `V` is Artinian over `R`, then `ρ.asModule` is Artinian over `R[Γ]`. -/
instance instIsArtinianAsModule {R Γ V : Type*} [CommSemiring R] [Monoid Γ]
    [AddCommMonoid V] [Module R V] [IsArtinian R V] (ρ : Representation R Γ V) :
    IsArtinian R[Γ] ρ.asModule :=
  isArtinian_of_tower R (isArtinian_of_linearEquiv ρ.asModuleEquiv.symm)

/-! ### Characteristic polynomials on `R[Γ]` via Amitsur's theorem -/

section MonoidAlgebraCharpoly

variable {R Γ V W : Type*} [CommRing R] [Monoid Γ]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]

/-- Equal characteristic polynomials are preserved under scalar multiplication of endomorphisms of
finite free modules over any commutative ring. -/
private theorem charpoly_smul_eq_of_charpoly_eq {f : Module.End R V} {g : Module.End R W}
    (h : f.charpoly = g.charpoly) (c : R) :
    (c • f).charpoly = (c • g).charpoly := by
  nontriviality R
  let bV := Module.Free.chooseBasis R V
  let bW := Module.Free.chooseBasis R W
  have hVW : Fintype.card (Module.Free.ChooseBasisIndex R V) =
      Fintype.card (Module.Free.ChooseBasisIndex R W) := by
    have hdeg := congrArg Polynomial.natDegree h
    rw [← LinearMap.charpoly_toMatrix f bV, ← LinearMap.charpoly_toMatrix g bW,
      Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim] at hdeg
    exact hdeg
  rw [← LinearMap.charpoly_toMatrix (c • f) bV, ← LinearMap.charpoly_toMatrix (c • g) bW,
    ← Matrix.charpolyRev_eq_charpolyRev_iff hVW, map_smul, map_smul,
    Matrix.charpolyRev_smul, Matrix.charpolyRev_smul]
  have hrev : (LinearMap.toMatrix bV bV f).charpolyRev =
      (LinearMap.toMatrix bW bW g).charpolyRev := by
    rw [Matrix.charpolyRev_eq_charpolyRev_iff hVW,
      LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]
    exact h
  rw [hrev]

omit [Module.Free R V] [Module.Finite R V] in
private theorem list_prod_smul_apply (ρ : Representation R Γ V) (a : Γ → R) (l : List Γ) :
    (l.map fun g ↦ a g • ρ g).prod = (l.map a).prod • ρ l.prod := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.prod_cons, ih, map_mul, smul_mul_smul_comm]

/-- **Amitsur's theorem for representations.** Over any commutative ring `R`, if two finite free
representations of a monoid `Γ` have the same characteristic polynomial at every `g : Γ`, then
every element of the monoid algebra `R[Γ]` acts on them with the same characteristic polynomial. -/
theorem charpoly_asAlgebraHom_eq_of_charpoly_eq {ρ : Representation R Γ V}
    {σ : Representation R Γ W} (h : ∀ g : Γ, (ρ g).charpoly = (σ g).charpoly) (a : R[Γ]) :
    (ρ.asAlgebraHom a).charpoly = (σ.asAlgebraHom a).charpoly := by
  nontriviality R
  have hVW : Module.finrank R V = Module.finrank R W := by
    let bV := Module.Free.chooseBasis R V
    let bW := Module.Free.chooseBasis R W
    have hdeg := congrArg Polynomial.natDegree (h 1)
    rw [← LinearMap.charpoly_toMatrix (ρ 1) bV, ← LinearMap.charpoly_toMatrix (σ 1) bW,
      Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim,
      ← Module.finrank_eq_card_chooseBasisIndex,
      ← Module.finrank_eq_card_chooseBasisIndex] at hdeg
    exact hdeg
  have ha : a = ∑ g ∈ a.coeff.support, MonoidAlgebra.single g (a.coeff g) :=
    (MonoidAlgebra.sum_coeff_single a).symm
  rw [ha, map_sum, map_sum]
  simp only [asAlgebraHom_single]
  refine LinearMap.charpoly_sum_eq_of_forall_list_prod hVW fun l _ _ _ ↦ ?_
  rw [list_prod_smul_apply, list_prod_smul_apply]
  exact charpoly_smul_eq_of_charpoly_eq (h l.prod) (l.map a.coeff).prod

end MonoidAlgebraCharpoly

/-! ### Dictionary between `ρ.asAlgebraHom` and `Algebra.lsmul` on `ρ.asModule` -/

section AsModuleCharpoly

variable {R Γ V : Type*} [CommRing R] [Monoid Γ] [AddCommGroup V] [Module R V]

private theorem asModuleEquiv_conj_lsmul (ρ : Representation R Γ V) (a : R[Γ]) :
    ρ.asModuleEquiv.conj (Algebra.lsmul R R ρ.asModule a) = ρ.asAlgebraHom a := by
  ext v
  rfl

private theorem charpoly_lsmul_asModule {k : Type*} [Field k] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Γ V) (a : k[Γ]) :
    (Algebra.lsmul k k ρ.asModule a).charpoly = (ρ.asAlgebraHom a).charpoly := by
  rw [← asModuleEquiv_conj_lsmul ρ a, LinearEquiv.charpoly_conj]

private theorem trace_lsmul_asModule (ρ : Representation R Γ V) (a : R[Γ]) :
    LinearMap.trace R ρ.asModule (Algebra.lsmul R R ρ.asModule a) =
      LinearMap.trace R V (ρ.asAlgebraHom a) := by
  rw [← asModuleEquiv_conj_lsmul ρ a, LinearMap.trace_conj']

end AsModuleCharpoly

/-! ### Multi-factor density and traces modulo the characteristic -/

section AlgClosed

variable {k Γ : Type*} [Field k] [IsAlgClosed k] [Monoid Γ]

/-- **Multi-factor Burnside–Wedderburn surjectivity for representations.** Over an algebraically
closed field `k`, for finitely many pairwise non-equivalent finite-dimensional irreducible
representations `ρ i` of a monoid `Γ`, the diagonal algebra action
`k[Γ] → ∏ i, End_k (V i)` is surjective. -/
theorem pi_asAlgebraHom_surjective {ι : Type*} [Finite ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (ρ : ∀ i, Representation k Γ (V i)) [∀ i, (ρ i).IsIrreducible]
    (hne : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) :
    Function.Surjective (AlgHom.pi fun i ↦ (ρ i).asAlgebraHom) := by
  have : ∀ i, IsSimpleModule k[Γ] (ρ i).asModule := fun i ↦
    (irreducible_iff_isSimpleModule_asModule (ρ i)).mp inferInstance
  have hne' : ∀ i j, Nonempty ((ρ i).asModule ≃ₗ[k[Γ]] (ρ j).asModule) → i = j :=
    fun i j h ↦ hne i j (TauCeti.Representation.nonempty_equiv_iff.mpr h)
  intro f
  obtain ⟨a, ha⟩ := Algebra.pi_lsmul_surjective_of_isAlgClosed (fun i ↦ (ρ i).asModule) hne'
    fun i ↦ (ρ i).asModuleEquiv.symm.conj (f i)
  refine ⟨a, funext fun i ↦ ?_⟩
  have hai := congrFun ha i
  simp only [AlgHom.pi_apply] at hai ⊢
  rw [← asModuleEquiv_conj_lsmul (ρ i) a, hai]
  exact LinearEquiv.apply_symm_apply (ρ i).asModuleEquiv.conj (f i)

/-- **Characters determine Jordan–Hölder multiplicities modulo `char k`** over an algebraically
closed field. If two finite-dimensional representations of a monoid `Γ` have the same character,
then for every `k[Γ]`-module `S`, the Jordan–Hölder multiplicities of `S` in `ρ.asModule` and
`σ.asModule` agree in `k`. No semisimplicity assumption is needed. -/
theorem natCast_jordanHolderMultiplicity_eq_of_character_eq
    {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {ρ : Representation k Γ V} {σ : Representation k Γ W}
    (h : ρ.character = σ.character) (S : Type*) [AddCommGroup S] [Module k[Γ] S] :
    (TauCeti.jordanHolderMultiplicity k[Γ] ρ.asModule S : k) =
      (TauCeti.jordanHolderMultiplicity k[Γ] σ.asModule S : k) := by
  refine TauCeti.natCast_jordanHolderMultiplicity_eq_of_trace_lsmul_eq (k := k) (fun a ↦ ?_) S
  rw [trace_lsmul_asModule, trace_lsmul_asModule]
  exact trace_asAlgebraHom_eq_of_character_eq h a

end AlgClosed

/-! ### Brauer–Nesbitt over an arbitrary field -/

section BrauerNesbitt

universe u v

variable {k : Type u} {Γ : Type v} {V W : Type*} [Field k] [Monoid Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **Equal characteristic polynomials determine Jordan–Hölder multiplicities** over any field
`k` and for any monoid `Γ`. No semisimplicity assumption is needed: two finite-dimensional
representations with equal characteristic polynomials at every `g : Γ` have the same composition
factors with the same multiplicities. -/
theorem jordanHolderMultiplicity_asModule_eq_of_charpoly_eq
    {ρ : Representation k Γ V} {σ : Representation k Γ W}
    (h : ∀ g : Γ, (ρ g).charpoly = (σ g).charpoly)
    (S : Type*) [AddCommGroup S] [Module k[Γ] S] :
    TauCeti.jordanHolderMultiplicity k[Γ] ρ.asModule S =
      TauCeti.jordanHolderMultiplicity k[Γ] σ.asModule S := by
  refine TauCeti.jordanHolderMultiplicity_eq_of_charpoly_lsmul_eq (k := k) (fun a ↦ ?_) S
  rw [charpoly_lsmul_asModule, charpoly_lsmul_asModule]
  exact charpoly_asAlgebraHom_eq_of_charpoly_eq h a

/-- **Equal Jordan–Hölder multiplicities are equivalent to equal characteristic polynomials** on
`Γ`, for finite-dimensional representations over any field and for any monoid. -/
theorem jordanHolderMultiplicity_asModule_eq_iff_charpoly_eq
    (ρ : Representation k Γ V) (σ : Representation k Γ W) :
    (∀ (S : Type (max u v)) [AddCommGroup S] [Module k[Γ] S] [IsSimpleModule k[Γ] S],
      TauCeti.jordanHolderMultiplicity k[Γ] ρ.asModule S =
        TauCeti.jordanHolderMultiplicity k[Γ] σ.asModule S) ↔
      ∀ g : Γ, (ρ g).charpoly = (σ g).charpoly := by
  refine ⟨fun h g ↦ ?_,
    fun h S _ _ _ ↦ jordanHolderMultiplicity_asModule_eq_of_charpoly_eq h S⟩
  have ha := (TauCeti.jordanHolderMultiplicity_eq_iff_charpoly_lsmul_eq
    (k := k) (A := k[Γ]) (M := ρ.asModule) (N := σ.asModule)).mp h (MonoidAlgebra.single g 1)
  simpa only [charpoly_lsmul_asModule, asAlgebraHom_single_one] using ha

/-- **The Brauer–Nesbitt theorem.** Over any field `k` and for any monoid `Γ`, two
finite-dimensional semisimple representations with the same characteristic polynomial at every
`g : Γ` are equivalent. -/
theorem nonempty_equiv_of_charpoly_eq (ρ : Representation k Γ V) (σ : Representation k Γ W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : ∀ g : Γ, (ρ g).charpoly = (σ g).charpoly) :
    Nonempty (ρ.Equiv σ) := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp inferInstance
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp inferInstance
  refine TauCeti.Representation.nonempty_equiv_iff.mpr <|
    IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_lsmul_eq (k := k) _ _ fun a ↦ ?_
  rw [charpoly_lsmul_asModule, charpoly_lsmul_asModule]
  exact charpoly_asAlgebraHom_eq_of_charpoly_eq h a

private theorem charpoly_eq_of_equiv {ρ : Representation k Γ V} {σ : Representation k Γ W}
    (e : ρ.Equiv σ) (g : Γ) :
    (ρ g).charpoly = (σ g).charpoly := by
  have hconj : e.toLinearEquiv.conj (ρ g) = σ g := by
    ext w
    have h := LinearMap.congr_fun (e.isIntertwining' g) (e.toLinearEquiv.symm w)
    exact h.trans (congrArg (σ g) (e.toLinearEquiv.apply_symm_apply w))
  rw [← hconj, LinearEquiv.charpoly_conj]

/-- Two finite-dimensional semisimple representations of a monoid over any field are equivalent if
and only if every element of the monoid acts on them with the same characteristic polynomial. -/
theorem nonempty_equiv_iff_charpoly_eq (ρ : Representation k Γ V) (σ : Representation k Γ W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation] :
    Nonempty (ρ.Equiv σ) ↔ ∀ g : Γ, (ρ g).charpoly = (σ g).charpoly :=
  ⟨fun ⟨e⟩ ↦ charpoly_eq_of_equiv e, nonempty_equiv_of_charpoly_eq ρ σ⟩

end BrauerNesbitt

/-! ### Descent along field extensions -/

section BaseChangeDescent

universe u v w

variable {k : Type u} {k' : Type v} {Γ : Type w} {V W : Type*}
  [Field k] [Field k'] [Algebra k k'] [Monoid Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

private theorem charpoly_eq_of_charpoly_baseChange_eq
    {ρ : Representation k Γ V} {σ : Representation k Γ W}
    (h : ∀ g : Γ, (ρ.baseChange k' g).charpoly = (σ.baseChange k' g).charpoly) (g : Γ) :
    (ρ g).charpoly = (σ g).charpoly := by
  have hg := h g
  rw [baseChange_apply, baseChange_apply, LinearMap.charpoly_baseChange,
    LinearMap.charpoly_baseChange] at hg
  exact Polynomial.map_injective (algebraMap k k') (algebraMap k k').injective hg

/-- **Field-extension descent of Jordan–Hölder multiplicities.** If two finite-dimensional
representations over `k` acquire the same Jordan–Hölder multiplicities after extending scalars to
any field extension `k'`, then they already have the same Jordan–Hölder multiplicities over
`k`. -/
theorem jordanHolderMultiplicity_asModule_eq_of_baseChange
    {ρ : Representation k Γ V} {σ : Representation k Γ W}
    (h : ∀ (S : Type (max v w)) [AddCommGroup S] [Module k'[Γ] S] [IsSimpleModule k'[Γ] S],
      TauCeti.jordanHolderMultiplicity k'[Γ] (ρ.baseChange k').asModule S =
        TauCeti.jordanHolderMultiplicity k'[Γ] (σ.baseChange k').asModule S)
    (T : Type*) [AddCommGroup T] [Module k[Γ] T] :
    TauCeti.jordanHolderMultiplicity k[Γ] ρ.asModule T =
      TauCeti.jordanHolderMultiplicity k[Γ] σ.asModule T :=
  jordanHolderMultiplicity_asModule_eq_of_charpoly_eq
    (charpoly_eq_of_charpoly_baseChange_eq (k' := k')
      ((jordanHolderMultiplicity_asModule_eq_iff_charpoly_eq
        (ρ.baseChange k') (σ.baseChange k')).mp h)) T

/-- **Field-extension descent for semisimple representations from multiplicities.** If `ρ` and `σ`
are semisimple over `k` and acquire the same Jordan–Hölder multiplicities after extending scalars
to a field extension `k'`, then `ρ` and `σ` are equivalent over `k`. -/
theorem nonempty_equiv_of_baseChange_jordanHolderMultiplicity_eq
    (ρ : Representation k Γ V) (σ : Representation k Γ W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : ∀ (S : Type (max v w)) [AddCommGroup S] [Module k'[Γ] S] [IsSimpleModule k'[Γ] S],
      TauCeti.jordanHolderMultiplicity k'[Γ] (ρ.baseChange k').asModule S =
        TauCeti.jordanHolderMultiplicity k'[Γ] (σ.baseChange k').asModule S) :
    Nonempty (ρ.Equiv σ) :=
  nonempty_equiv_of_charpoly_eq ρ σ
    (charpoly_eq_of_charpoly_baseChange_eq (k' := k')
      ((jordanHolderMultiplicity_asModule_eq_iff_charpoly_eq
        (ρ.baseChange k') (σ.baseChange k')).mp h))

/-- **Equivalence after field extension forces equal Jordan–Hölder multiplicities over `k`.** -/
theorem jordanHolderMultiplicity_asModule_eq_of_nonempty_equiv_baseChange
    {ρ : Representation k Γ V} {σ : Representation k Γ W}
    (h : Nonempty ((ρ.baseChange k').Equiv (σ.baseChange k')))
    (T : Type*) [AddCommGroup T] [Module k[Γ] T] :
    TauCeti.jordanHolderMultiplicity k[Γ] ρ.asModule T =
      TauCeti.jordanHolderMultiplicity k[Γ] σ.asModule T :=
  let ⟨e⟩ := h
  jordanHolderMultiplicity_asModule_eq_of_charpoly_eq
    (charpoly_eq_of_charpoly_baseChange_eq (k' := k') (charpoly_eq_of_equiv e)) T

/-- **Field-extension descent of equivalence for semisimple representations.** If `ρ` and `σ` are
finite-dimensional semisimple representations over `k` that become equivalent over a field
extension `k'`, then they are already equivalent over `k`. -/
theorem nonempty_equiv_of_nonempty_equiv_baseChange
    (ρ : Representation k Γ V) (σ : Representation k Γ W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : Nonempty ((ρ.baseChange k').Equiv (σ.baseChange k'))) :
    Nonempty (ρ.Equiv σ) :=
  let ⟨e⟩ := h
  nonempty_equiv_of_charpoly_eq ρ σ
    (charpoly_eq_of_charpoly_baseChange_eq (k' := k') (charpoly_eq_of_equiv e))

end BaseChangeDescent

/-! ### Trace criteria in positive characteristic -/

section TraceCriteria

variable {k Γ V W : Type*} [Field k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **Characters determine Jordan–Hölder multiplicities when `dim < char k`.** Over any field `k`
of characteristic `p`, two representations of a monoid `Γ` of dimensions strictly less than `p`
with the same character have the same Jordan–Hölder multiplicities. -/
theorem jordanHolderMultiplicity_asModule_eq_of_character_eq_of_finrank_lt_char [Monoid Γ]
    {p : ℕ} [CharP k p] {ρ : Representation k Γ V} {σ : Representation k Γ W}
    (hV : Module.finrank k V < p) (hW : Module.finrank k W < p)
    (h : ρ.character = σ.character) (S : Type*) [AddCommGroup S] [Module k[Γ] S] :
    TauCeti.jordanHolderMultiplicity k[Γ] ρ.asModule S =
      TauCeti.jordanHolderMultiplicity k[Γ] σ.asModule S := by
  let K := AlgebraicClosure k
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hchar : (ρ.baseChange K).character = (σ.baseChange K).character := by
    funext g
    rw [character_baseChange, character_baseChange, congrFun h g]
  refine jordanHolderMultiplicity_asModule_eq_of_baseChange (k' := K) (fun T _ _ _ ↦ ?_) S
  have hmV : TauCeti.jordanHolderMultiplicity K[Γ] (ρ.baseChange K).asModule T < p := by
    have hle := TauCeti.jordanHolderMultiplicity_le_finrank (k := K) (A := K[Γ])
      (M := (ρ.baseChange K).asModule) T
    rw [(ρ.baseChange K).asModuleEquiv.finrank_eq, Module.finrank_baseChange] at hle
    exact hle.trans_lt hV
  have hmW : TauCeti.jordanHolderMultiplicity K[Γ] (σ.baseChange K).asModule T < p := by
    have hle := TauCeti.jordanHolderMultiplicity_le_finrank (k := K) (A := K[Γ])
      (M := (σ.baseChange K).asModule) T
    rw [(σ.baseChange K).asModuleEquiv.finrank_eq, Module.finrank_baseChange] at hle
    exact hle.trans_lt hW
  have hmod := (CharP.cast_eq_iff_mod_eq K p).mp
    (natCast_jordanHolderMultiplicity_eq_of_character_eq hchar T)
  rwa [Nat.mod_eq_of_lt hmV, Nat.mod_eq_of_lt hmW] at hmod

/-- **Characters determine semisimple representations when `dim < char k`.** Over any field `k` of
characteristic `p`, two semisimple representations of a monoid `Γ` of dimensions strictly less than
`p` with the same character are equivalent. -/
theorem nonempty_equiv_of_character_eq_of_finrank_lt_char [Monoid Γ]
    {p : ℕ} [CharP k p] (ρ : Representation k Γ V) (σ : Representation k Γ W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (hV : Module.finrank k V < p) (hW : Module.finrank k W < p)
    (h : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp inferInstance
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp inferInstance
  have : Module.Finite k[Γ] ρ.asModule := Module.Finite.of_restrictScalars_finite k k[Γ] _
  have : Module.Finite k[Γ] σ.asModule := Module.Finite.of_restrictScalars_finite k k[Γ] _
  exact TauCeti.Representation.nonempty_equiv_iff.mpr <|
    IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq ρ.asModule σ.asModule
      fun S _ _ _ ↦ jordanHolderMultiplicity_asModule_eq_of_character_eq_of_finrank_lt_char
        hV hW h S

omit [FiniteDimensional k V] in
/-- Every operator in a group representation over a field with trivial unit group (such as
`𝔽₂`) has determinant `1`. -/
private theorem det_eq_one_of_subsingleton_units [Subsingleton kˣ] [Group Γ]
    (ρ : Representation k Γ V) (g : Γ) :
    LinearMap.det (ρ g) = 1 := by
  have hu : IsUnit (LinearMap.det (ρ g)) :=
    isUnit_iff_exists_inv.mpr ⟨LinearMap.det (ρ g⁻¹), by
      rw [← map_mul LinearMap.det, ← map_mul, mul_inv_cancel, map_one, map_one]⟩
  simpa using congrArg Units.val (Subsingleton.elim hu.unit 1)

private theorem charpoly_eq_of_character_eq_of_finrank_eq_two [Subsingleton kˣ] [Group Γ]
    {ρ : Representation k Γ V} {σ : Representation k Γ W}
    (hV : Module.finrank k V = 2) (hW : Module.finrank k W = 2)
    (h : ρ.character = σ.character) (g : Γ) :
    (ρ g).charpoly = (σ g).charpoly := by
  rw [LinearMap.charpoly_of_finrank_eq_two hV, LinearMap.charpoly_of_finrank_eq_two hW,
    det_eq_one_of_subsingleton_units, det_eq_one_of_subsingleton_units]
  have htr : LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g) := congrFun h g
  rw [htr]

/-- **Characters determine Jordan–Hölder multiplicities for rank-two group representations over a
field with trivial unit group (such as `𝔽₂`).** -/
theorem jordanHolderMultiplicity_asModule_eq_of_character_eq_of_finrank_eq_two
    [Subsingleton kˣ] [Group Γ] {ρ : Representation k Γ V} {σ : Representation k Γ W}
    (hV : Module.finrank k V = 2) (hW : Module.finrank k W = 2)
    (h : ρ.character = σ.character) (S : Type*) [AddCommGroup S] [Module k[Γ] S] :
    TauCeti.jordanHolderMultiplicity k[Γ] ρ.asModule S =
      TauCeti.jordanHolderMultiplicity k[Γ] σ.asModule S :=
  jordanHolderMultiplicity_asModule_eq_of_charpoly_eq
    (charpoly_eq_of_character_eq_of_finrank_eq_two hV hW h) S

/-- **Characters determine rank-two semisimple group representations over a field with trivial unit
group (such as `𝔽₂`).** -/
theorem nonempty_equiv_of_character_eq_of_finrank_eq_two
    [Subsingleton kˣ] [Group Γ] (ρ : Representation k Γ V) (σ : Representation k Γ W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (hV : Module.finrank k V = 2) (hW : Module.finrank k W = 2)
    (h : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) :=
  nonempty_equiv_of_charpoly_eq ρ σ (charpoly_eq_of_character_eq_of_finrank_eq_two hV hW h)

end TraceCriteria

end Representation

/-! ### Continuous Brauer–Nesbitt theorem -/

namespace TauCeti.ContinuousRep

section BrauerNesbitt

variable {Γ k V W : Type*} [Monoid Γ] [TopologicalSpace Γ]
  [Field k] [TopologicalSpace k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [TopologicalSpace V] [IsModuleTopology k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [TopologicalSpace W] [IsModuleTopology k W]

/-- **The Brauer–Nesbitt theorem for continuous representations.** For any field `k` with a
topology and any monoid `Γ` with a topology, two finite-dimensional semisimple jointly continuous
representations on spaces with their module topology are isomorphic as continuous representations
whenever every `g : Γ` acts on them with the same characteristic polynomial. -/
theorem nonempty_iso_of_charpoly_eq (ρ : ContinuousRep Γ k V) (σ : ContinuousRep Γ k W)
    [ρ.toRepresentation.IsSemisimpleRepresentation]
    [σ.toRepresentation.IsSemisimpleRepresentation]
    (h : ∀ g : Γ, (ρ g).charpoly = (σ g).charpoly) :
    Nonempty (Iso ρ σ) :=
  let ⟨e⟩ := Representation.nonempty_equiv_of_charpoly_eq
    ρ.toRepresentation σ.toRepresentation h
  ⟨Iso.ofEquiv e⟩

/-- Two finite-dimensional semisimple jointly continuous representations on spaces with their module
topology are isomorphic as continuous representations if and only if every `g : Γ` acts on them
with the same characteristic polynomial. -/
theorem nonempty_iso_iff_charpoly_eq (ρ : ContinuousRep Γ k V) (σ : ContinuousRep Γ k W)
    [ρ.toRepresentation.IsSemisimpleRepresentation]
    [σ.toRepresentation.IsSemisimpleRepresentation] :
    Nonempty (Iso ρ σ) ↔ ∀ g : Γ, (ρ g).charpoly = (σ g).charpoly :=
  ⟨fun ⟨e⟩ ↦ (Representation.nonempty_equiv_iff_charpoly_eq
      ρ.toRepresentation σ.toRepresentation).mp ⟨e.toRepresentationEquiv⟩,
    nonempty_iso_of_charpoly_eq ρ σ⟩

end BrauerNesbitt

end TauCeti.ContinuousRep
