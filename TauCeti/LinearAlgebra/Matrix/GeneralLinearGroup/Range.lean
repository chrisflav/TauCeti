/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# General linear groups under field embeddings

Over a field, a square matrix is invertible if and only if its determinant is nonzero. Consequently,
for any ring homomorphism `f : K →+* L` between fields, an invertible matrix `M : GL n L` lies in
the image of `Matrix.GeneralLinearGroup.map f : GL n K →* GL n L` if and only if every entry of `M`
lies in the range of `f` (unlike the general subalgebra case in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subalgebra`, where the entries of `M⁻¹` must also
be checked).

## Main results

* `Matrix.GeneralLinearGroup.mem_range_map_iff`: over fields, an element of `GL n L` lies in the
  range of `Matrix.GeneralLinearGroup.map f` if and only if all its entries lie in `f.range`.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n K L : Type*} [DecidableEq n] [Fintype n] [Field K] [Field L]

/-- **Descent of invertible matrices along a field homomorphism.** For any ring homomorphism
`f : K →+* L` between fields, an element `M : GL n L` lies in the range of
`Matrix.GeneralLinearGroup.map f` if and only if every entry of `M` lies in `f.range`. -/
theorem mem_range_map_iff (f : K →+* L) (M : GL n L) :
    M ∈ (Matrix.GeneralLinearGroup.map (n := n) f).range ↔
      ∀ i j, (M : Matrix n n L) i j ∈ f.range := by
  constructor
  · rintro ⟨N, rfl⟩ i j
    exact ⟨(N : Matrix n n K) i j, rfl⟩
  · intro h
    choose A' hA using h
    let A : Matrix n n K := Matrix.of A'
    have hAmap : f.mapMatrix A = (M : Matrix n n L) := Matrix.ext hA
    have hdet : A.det ≠ 0 := by
      intro h0
      have hM0 : (M : Matrix n n L).det = 0 := by
        rw [← hAmap, ← RingHom.map_det, h0, map_zero]
      exact M.det_ne_zero hM0
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, ?_⟩
    apply Units.ext
    exact hAmap

end Matrix.GeneralLinearGroup
