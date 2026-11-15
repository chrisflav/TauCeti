/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Membership of concatenated paths in a set

Every point on a concatenated path `γ₁.trans γ₂` lies in the range of `γ₁` or of `γ₂`
(`Path.trans_range`), so if both paths stay in a set `s`, their concatenation also stays in `s`.

## Main declarations

* `Path.trans_apply_mem` -- if `γ₁` and `γ₂` take values in `s`, so does `γ₁.trans γ₂`.
-/

public section

open Set
open scoped unitInterval

namespace Path

variable {X : Type*} [TopologicalSpace X]

/-- If two paths take values in `s`, so does their concatenation. -/
theorem trans_apply_mem {s : Set X} {a b c : X} {γ₁ : Path a b} {γ₂ : Path b c}
    (h₁ : ∀ t, γ₁ t ∈ s) (h₂ : ∀ t, γ₂ t ∈ s) (t : I) : (γ₁.trans γ₂) t ∈ s := by
  obtain ⟨u, hu⟩ | ⟨u, hu⟩ := γ₁.trans_range γ₂ ▸ mem_range_self t
  exacts [hu ▸ h₁ u, hu ▸ h₂ u]

end Path
