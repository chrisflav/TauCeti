/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported

/-!
# Functoriality and ambient coercion for `MvPolynomial.supported`

Changing coefficients along a ring homomorphism preserves the variable-restricted polynomial
subalgebra `MvPolynomial.supported R s`, and reflects membership when the ring homomorphism is
injective (`MvPolynomial.map_mem_supported`, `MvPolynomial.map_mem_supported_iff`). Variable
renaming preserves `MvPolynomial.supported` along maps respecting the variable sets and reflects
membership when the variable map is injective (`MvPolynomial.rename_mem_supported`,
`MvPolynomial.rename_mem_supported_iff`). Coercing the inverse of Mathlib's
`MvPolynomial.supportedEquivMvPolynomial` back into `MvPolynomial σ R` agrees with renaming along
`((↑) : s → σ)` (`MvPolynomial.coe_supportedEquivMvPolynomial_symm`).
-/

public section

namespace MvPolynomial

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Changing coefficients along a ring homomorphism preserves `MvPolynomial.supported`. -/
theorem map_mem_supported (f : R →+* S) {s : Set σ} {p : MvPolynomial σ R}
    (hp : p ∈ supported R s) : map f p ∈ supported S s :=
  mem_supported.2 ((Finset.coe_subset.2 (p.vars_map f)).trans (mem_supported.1 hp))

/-- Along an injective ring homomorphism, `MvPolynomial.map` reflects and preserves membership in
`MvPolynomial.supported`. -/
theorem map_mem_supported_iff {f : R →+* S} (hf : Function.Injective f) {s : Set σ}
    {p : MvPolynomial σ R} : map f p ∈ supported S s ↔ p ∈ supported R s := by
  rw [mem_supported, mem_supported, p.vars_map_of_injective hf]

/-- Renaming variables along `f : σ → τ` maps `MvPolynomial.supported R s` into
`MvPolynomial.supported R t` whenever `Set.MapsTo f s t`. -/
theorem rename_mem_supported {f : σ → τ} {s : Set σ} {t : Set τ} (hst : Set.MapsTo f s t)
    {p : MvPolynomial σ R} (hp : p ∈ supported R s) : rename f p ∈ supported R t := by
  classical
  refine mem_supported.2 ((Finset.coe_subset.2 (vars_rename f p)).trans ?_)
  rw [Finset.coe_image]
  exact (Set.image_mono (mem_supported.1 hp)).trans hst.image_subset

/-- Along an injective variable map `f : σ → τ`, `MvPolynomial.rename f` lands in
`MvPolynomial.supported R t` if and only if the input lies in
`MvPolynomial.supported R (f ⁻¹' t)`. -/
theorem rename_mem_supported_iff {f : σ → τ} (hf : Function.Injective f) {t : Set τ}
    {p : MvPolynomial σ R} :
    rename f p ∈ supported R t ↔ p ∈ supported R (f ⁻¹' t) := by
  classical
  rw [mem_supported, mem_supported, vars_def, degrees_rename_of_injective hf,
    Multiset.toFinset_map, ← vars_def, Finset.coe_image, Set.image_subset_iff]

/-- Coercing `(MvPolynomial.supportedEquivMvPolynomial s).symm` into the ambient polynomial ring
renames variables along the subtype inclusion `((↑) : s → σ)`. -/
theorem coe_supportedEquivMvPolynomial_symm (s : Set σ) (q : MvPolynomial s R) :
    ((supportedEquivMvPolynomial s).symm q : MvPolynomial σ R) = rename ((↑) : s → σ) q := by
  have h : (supported R s).val.comp (supportedEquivMvPolynomial s).symm.toAlgHom =
      rename ((↑) : s → σ) :=
    algHom_ext fun i ↦ by simp
  exact congr($h q)

@[simp]
theorem rename_coe_supportedEquivMvPolynomial (s : Set σ) (p : supported R s) :
    rename ((↑) : s → σ) (supportedEquivMvPolynomial s p) = (p : MvPolynomial σ R) := by
  rw [← coe_supportedEquivMvPolynomial_symm, AlgEquiv.symm_apply_apply]

end MvPolynomial
