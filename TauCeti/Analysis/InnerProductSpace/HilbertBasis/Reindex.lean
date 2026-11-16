/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
public import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Reindexing Hilbert bases and basis-induced unitary equivalences

An equivalence `e : ι ≃ κ` of index types reindexes a Hilbert basis `b : HilbertBasis ι 𝕜 E` to a
Hilbert basis `b.reindex e : HilbertBasis κ 𝕜 E` with `(b.reindex e) j = b (e.symm j)`, mirroring
Mathlib's `OrthonormalBasis.reindex` and `TauCeti`'s `HilbertBasis.mapₗᵢ`.

Given Hilbert bases `b : HilbertBasis ι 𝕜 E`, `c : HilbertBasis κ 𝕜 F`, and an index equivalence
`e : ι ≃ κ`, composing `b.repr`, `LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e`, and `c.repr.symm`
yields the unique linear isometric equivalence `b.equivₗᵢ c e : E ≃ₗᵢ[𝕜] F` sending `b i` to
`c (e i)` (`HilbertBasis.equivₗᵢ_apply`, `HilbertBasis.eq_equivₗᵢ_of_apply`).
-/

public section

variable {ι κ μ 𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

namespace HilbertBasis

/-- Reindex a Hilbert basis along an equivalence of index types. -/
protected noncomputable def reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    HilbertBasis κ 𝕜 E :=
  ofRepr (b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e))

/-- The coordinate representation of `b.reindex e` reindexes `b.repr` along `e`. -/
@[simp]
theorem repr_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).repr = b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e) :=
  (rfl)

/-- The `j`th vector of `b.reindex e` is `b (e.symm j)`. -/
@[simp]
theorem reindex_apply (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) (j : κ) :
    b.reindex e j = b (e.symm j) := by
  classical
  simp only [← HilbertBasis.repr_symm_single, repr_reindex, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.lpCongrLeft_symm,
    LinearIsometryEquiv.lpCongrLeft_single]

/-- Function-level form of `HilbertBasis.reindex_apply`. -/
@[simp]
theorem coe_reindex (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)

/-- Reindexing along the identity equivalence leaves a Hilbert basis unchanged. -/
@[simp]
theorem reindex_refl (b : HilbertBasis ι 𝕜 E) :
    b.reindex (Equiv.refl ι) = b :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Reindexing successively along two equivalences is reindexing along their composition. -/
@[simp]
theorem reindex_trans (b : HilbertBasis ι 𝕜 E) (e₁ : ι ≃ κ) (e₂ : κ ≃ μ) :
    (b.reindex e₁).reindex e₂ = b.reindex (e₁.trans e₂) :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- Reindexing along `e` and then along `e.symm` recovers the original Hilbert basis. -/
theorem reindex_symm (b : HilbertBasis ι 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e).reindex e.symm = b := by
  simp

/-- Reindexing along `e.symm` and then along `e` recovers the original Hilbert basis. -/
theorem reindex_symm_self (b : HilbertBasis κ 𝕜 E) (e : ι ≃ κ) :
    (b.reindex e.symm).reindex e = b := by
  simp

/-- Transporting along a linear isometric equivalence commutes with reindexing. -/
theorem mapₗᵢ_reindex (b : HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (σ : ι ≃ κ) :
    (b.reindex σ).mapₗᵢ e = (b.mapₗᵢ e).reindex σ :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- The linear isometric equivalence sending a Hilbert basis `b` to a Hilbert basis `c` along an
index equivalence `e : ι ≃ κ`. -/
protected noncomputable def equivₗᵢ (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (e : ι ≃ κ) : E ≃ₗᵢ[𝕜] F :=
  (b.repr.trans (LinearIsometryEquiv.lpCongrLeft 2 𝕜 𝕜 e)).trans c.repr.symm

/-- The basis-induced linear isometric equivalence sends `b i` to `c (e i)`. -/
@[simp]
theorem equivₗᵢ_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) (i : ι) :
    b.equivₗᵢ c e (b i) = c (e i) := by
  classical
  simp only [HilbertBasis.equivₗᵢ, LinearIsometryEquiv.trans_apply, HilbertBasis.repr_self,
    LinearIsometryEquiv.lpCongrLeft_single, HilbertBasis.repr_symm_single]

/-- The coordinates of `b.equivₗᵢ c e x` in `c` are the reindexed coordinates of `x` in `b`. -/
@[simp]
theorem repr_equivₗᵢ_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ)
    (x : E) (j : κ) :
    c.repr (b.equivₗᵢ c e x) j = b.repr x (e.symm j) := by
  simp only [HilbertBasis.equivₗᵢ, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.lpCongrLeft_apply]

/-- The inverse of `b.equivₗᵢ c e` is `c.equivₗᵢ b e.symm`. -/
@[simp]
theorem equivₗᵢ_symm (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    (b.equivₗᵢ c e).symm = c.equivₗᵢ b e.symm := by
  ext x
  apply b.repr.injective
  ext i
  simp [HilbertBasis.equivₗᵢ]

/-- The equivalence induced by a single Hilbert basis and the identity permutation is the identity.
-/
@[simp]
theorem equivₗᵢ_refl (b : HilbertBasis ι 𝕜 E) :
    b.equivₗᵢ b (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E := by
  ext x
  apply b.repr.injective
  ext i
  simp

/-- Composing two basis-induced linear isometric equivalences corresponds to composing the index
equivalences. -/
@[simp]
theorem equivₗᵢ_trans (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (d : HilbertBasis μ 𝕜 G) (e₁ : ι ≃ κ) (e₂ : κ ≃ μ) :
    (b.equivₗᵢ c e₁).trans (c.equivₗᵢ d e₂) = b.equivₗᵢ d (e₁.trans e₂) := by
  ext x
  apply d.repr.injective
  ext k
  simp

/-- Transporting `b` along `b.equivₗᵢ c e` produces `c` reindexed by `e.symm`. -/
theorem mapₗᵢ_equivₗᵢ (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ) :
    b.mapₗᵢ (b.equivₗᵢ c e) = c.reindex e.symm :=
  DFunLike.ext _ _ fun _ ↦ by simp

/-- **Uniqueness of the basis-induced unitary.** A linear isometric equivalence sending `b i` to
`c (e i)` for every `i` coincides with `b.equivₗᵢ c e`. -/
theorem eq_equivₗᵢ_of_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (e : ι ≃ κ)
    {U : E ≃ₗᵢ[𝕜] F} (hU : ∀ i, U (b i) = c (e i)) : U = b.equivₗᵢ c e := by
  have hclm : U.toLinearIsometry.toContinuousLinearMap =
      (b.equivₗᵢ c e).toLinearIsometry.toContinuousLinearMap := by
    refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span)
      ?_
    rintro _ ⟨i, rfl⟩
    simp [hU i]
  ext x
  exact DFunLike.congr_fun hclm x

end HilbertBasis
