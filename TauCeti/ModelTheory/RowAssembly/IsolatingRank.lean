/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RowAssembly.OmegaWitness
public import TauCeti.ModelTheory.Counting.Stratification
public import Mathlib.SetTheory.Cardinal.Continuum
import TauCeti.ModelTheory.RelationalConfiguration.Topology

/-!
# Non-isolation of the internal Scott rank and a large level-`ω` class

Transporting `BaseAssembly` and its Cantor-indexed companions `CompanionAssembly z` (`z : ℕ → Bool`)
onto the standard carrier `ℕ` yields relational configurations `baseCode` and `companionCode z`
over `omegaLang` with the following consequences for `TauCeti.IsIsolatingRank`:

* `not_isIsolatingRank_internalScottRank`: the internal Scott rank of the decoded structure is not
  an isolating rank, since `baseCode` has internal Scott rank `ω` while every `companionCode z` is
  `bfEquivSetoid`-equivalent to `baseCode` at level `ω` and non-isomorphic to it;
* `omega0_lt_apply_baseCode_of_isIsolatingRank`: every isolating rank `ρ` on
  `omegaLang`-configurations satisfies `ω < ρ baseCode`;
* `mk_isoClasses_bfEquivSetoid_omega0_baseCode`: the single level-`ω` back-and-forth equivalence
  class `{d | bfEquivSetoid omegaLang ℕ ω baseCode d}` meets continuum many (`𝔠`) isomorphism
  classes, showing both that one-sidedness of `IsIsolatingRank.isolates` is essential and that
  having at most one equivalence class at every level up to a limit ordinal does not bound the
  number of isomorphism classes within an arbitrary set of configurations.

## References

* Adapted from `InfinitaryLogic/ModelTheory/ScottRankOmegaExample.lean` and
  `InfinitaryLogic/Descriptive/ScatteredCounting.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a39bc3e0b`,
  Apache-2.0).
-/

public section

namespace TauCeti.RowAssembly

open FirstOrder FirstOrder.Language Cardinal TauCeti.RelationalConfiguration
open scoped Ordinal

/-- A relational configuration on `ℕ` encoding `BaseAssembly`. -/
noncomputable def baseCode : RelationalConfiguration omegaLang ℕ :=
  ((nonempty_equiv_of_countable : Nonempty (BaseAssembly ≃ ℕ)).some).encodeVia

/-- A relational configuration on `ℕ` encoding `CompanionAssembly z`. -/
noncomputable def companionCode (z : ℕ → Bool) : RelationalConfiguration omegaLang ℕ :=
  ((nonempty_equiv_of_countable : Nonempty (CompanionAssembly z ≃ ℕ)).some).encodeVia

/-- The structure decoded from `baseCode` has internal Scott rank `ω`. -/
theorem internalScottRank_baseCode :
    @internalScottRank omegaLang _ ℕ baseCode.toStructure = ω := by
  obtain ⟨e⟩ :=
    ((nonempty_equiv_of_countable : Nonempty (BaseAssembly ≃ ℕ)).some).nonempty_equiv_encodeVia
      (L := omegaLang)
  have heq :=
    @Language.Equiv.internalScottRank_eq omegaLang _ BaseAssembly ℕ _ baseCode.toStructure e
  exact heq.symm.trans internalScottRank_baseAssembly

/-- The structure decoded from `baseCode` has Scott height strictly greater than `ω`. -/
theorem omega0_lt_scottHeight_baseCode :
    ω < @scottHeight omegaLang _ ℕ baseCode.toStructure := by
  obtain ⟨e⟩ :=
    ((nonempty_equiv_of_countable : Nonempty (BaseAssembly ≃ ℕ)).some).nonempty_equiv_encodeVia
      (L := omegaLang)
  have heq := @Language.Equiv.scottHeight_eq omegaLang _ BaseAssembly _ ℕ baseCode.toStructure e
  exact heq ▸ omega0_lt_scottHeight_baseAssembly

/-- The structure decoded from `baseCode` has Scott height at most `ω + ω`. -/
theorem scottHeight_baseCode_le_omega0_add_omega0 :
    @scottHeight omegaLang _ ℕ baseCode.toStructure ≤ ω + ω := by
  obtain ⟨e⟩ :=
    ((nonempty_equiv_of_countable : Nonempty (BaseAssembly ≃ ℕ)).some).nonempty_equiv_encodeVia
      (L := omegaLang)
  have heq := @Language.Equiv.scottHeight_eq omegaLang _ BaseAssembly _ ℕ baseCode.toStructure e
  exact heq ▸ scottHeight_baseAssembly_le_omega0_add_omega0

/-- Every `companionCode z` is back-and-forth equivalent to `baseCode` at level `ω`. -/
theorem bfEquivSetoid_omega0_baseCode_companionCode (z : ℕ → Bool) :
    bfEquivSetoid omegaLang ℕ (ω : Ordinal.{0}) baseCode (companionCode z) := by
  rw [baseCode, companionCode, Equiv.bfEquivSetoid_encodeVia_iff]
  exact (bfEquiv_omega0_companionAssembly z).symm

/-- No `companionCode z` is isomorphic to `baseCode`. -/
theorem not_isoSetoid_baseCode_companionCode (z : ℕ → Bool) :
    ¬ isoSetoid omegaLang ℕ baseCode (companionCode z) := by
  rw [baseCode, companionCode, Equiv.isoSetoid_encodeVia_iff]
  rintro ⟨Φ⟩
  exact (isEmpty_equiv_companionAssembly_baseAssembly z).false Φ.symm

/-- Two companion configurations `companionCode z` and `companionCode z'` are isomorphic if and
only if `z = z'`. -/
@[simp]
theorem isoSetoid_companionCode_iff {z z' : ℕ → Bool} :
    isoSetoid omegaLang ℕ (companionCode z) (companionCode z') ↔ z = z' := by
  refine ⟨fun h => ?_, fun h => h ▸ (isoSetoid omegaLang ℕ).refl _⟩
  by_contra hne
  rw [companionCode, companionCode, Equiv.isoSetoid_encodeVia_iff] at h
  obtain ⟨Φ⟩ := h
  exact (isEmpty_equiv_companionAssembly hne).false Φ

/-- **The internal Scott rank is not an isolating rank.** Reading `internalScottRank` on the
decoded structure of a configuration over `omegaLang` fails `IsIsolatingRank.isolates` at
`baseCode`. -/
theorem not_isIsolatingRank_internalScottRank :
    ¬ IsIsolatingRank (L := omegaLang)
        (fun c => letI := c.toStructure; internalScottRank (L := omegaLang) ℕ) := by
  intro h
  have hbf : bfEquivSetoid omegaLang ℕ (@internalScottRank omegaLang _ ℕ baseCode.toStructure)
      baseCode (companionCode fun _ => false) := by
    rw [internalScottRank_baseCode]
    exact bfEquivSetoid_omega0_baseCode_companionCode fun _ => false
  exact not_isoSetoid_baseCode_companionCode (fun _ => false) (h.isolates hbf)

/-- Every isolating rank `ρ` on configurations over `omegaLang` strictly exceeds `ω` at
`baseCode`. -/
theorem omega0_lt_apply_baseCode_of_isIsolatingRank
    {ρ : RelationalConfiguration omegaLang ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ) :
    ω < ρ baseCode := by
  by_contra! hle
  exact not_isoSetoid_baseCode_companionCode (fun _ => false)
    (hρ.isolates_of_le hle (bfEquivSetoid_omega0_baseCode_companionCode fun _ => false))

/-- **A single level-`ω` back-and-forth class meeting continuum many isomorphism classes.** The
level-`ω` equivalence class of `baseCode` contains continuum many (`𝔠`) pairwise non-isomorphic
configurations on `ℕ`. -/
theorem mk_isoClasses_bfEquivSetoid_omega0_baseCode :
    #(Quotient ((isoSetoid omegaLang ℕ).comap
      (Subtype.val : {d | bfEquivSetoid omegaLang ℕ (ω : Ordinal.{0}) baseCode d} → _))) = 𝔠 := by
  apply le_antisymm
  · exact mk_quotient_le.trans ((mk_subtype_le _).trans (mk_le_continuum omegaLang ℕ))
  · let f : (ℕ → Bool) → Quotient ((isoSetoid omegaLang ℕ).comap
        (Subtype.val : {d | bfEquivSetoid omegaLang ℕ (ω : Ordinal.{0}) baseCode d} → _)) :=
      fun z => Quotient.mk _ ⟨companionCode z, bfEquivSetoid_omega0_baseCode_companionCode z⟩
    have hf : Function.Injective f := fun z z' h => by
      have hiso : isoSetoid omegaLang ℕ (companionCode z) (companionCode z') :=
        Quotient.exact (s := (isoSetoid omegaLang ℕ).comap Subtype.val) h
      exact isoSetoid_companionCode_iff.mp hiso
    have hcantor : #(ℕ → Bool) = 𝔠 := by
      simp [Cardinal.two_power_aleph0]
    exact hcantor ▸ mk_le_of_injective hf

end TauCeti.RowAssembly
