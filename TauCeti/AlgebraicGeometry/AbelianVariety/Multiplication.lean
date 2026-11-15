/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.DimensionZero
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.TangentSpace
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Basic

/-!
# Multiplication by `n` on abelian varieties: étaleness, characteristic `p`, and isogenies

For an abelian variety `A` over a field `K` and an integer `n : ℤ`, the differential of the
multiplication-by-`n` endomorphism `[n] = mulBy A n : A ⟶ A` at the identity is scalar
multiplication by `(n : K)` on `T₀A` (`AbelianVariety.tangentMap_mulBy`). Combining this with the
differential criteria for unramified and étale homomorphisms of abelian varieties yields the exact
characteristic criterion for étaleness of `[n]` (`Stacks Tag 0BFH`, Milne *Abelian Varieties* I §7):

* `AbelianVariety.etale_toSchemeHom_mulBy_iff`: `[n]` is étale if and only if `A.dim = 0` or
  `(n : K) ≠ 0`;
* `AbelianVariety.etale_toSchemeHom_mulBy_iff_of_dim_pos`: when `0 < A.dim`, `[n]` is étale if and
  only if `(n : K) ≠ 0`;
* `AbelianVariety.not_etale_toSchemeHom_mulBy_charP`: in characteristic `p > 0`, `[p]` is never
  étale on a positive-dimensional abelian variety (`0 < A.dim`);
* `AbelianVariety.isIsogeny_mulBy_of_ne_zero` and `AbelianVariety.isIsogeny_mulBy_of_charZero`:
  whenever `(n : K) ≠ 0` (in particular, for every `n ≠ 0` in characteristic zero), `[n]` is an
  isogeny;
* `AbelianVariety.etale_torsion_hom_of_ne_zero` and
  `AbelianVariety.isFinite_torsion_hom_of_ne_zero`: when `(n : K) ≠ 0`, the `n`-torsion group scheme
  `A[n]` is finite étale over `Spec K`.

## References

* [The Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* J. S. Milne, *Abelian Varieties*, I §7.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti.AlgebraicGeometry.AbelianVariety

open scoped Hom CategoryTheory.Obj

universe u

variable {K : Type u} [Field K]

noncomputable section

/-! ### Underlying morphisms of powers and `[n]` -/

/-- `Hom.toOverHom` preserves integer powers for the pointwise group law. -/
@[simp]
theorem Hom.toOverHom_zpow {A B : AbelianVariety K} (f : A ⟶ B) (n : ℤ) :
    Hom.toOverHom (f ^ n) = Hom.toOverHom f ^ n :=
  map_zpow
    ({ toFun := Hom.toOverHom
       map_one' := Hom.toOverHom_one
       map_mul' := fun _ _ ↦ Hom.toOverHom_mul _ _ } : (A ⟶ B) →* (A.toOver ⟶ B.toOver)) f n

/-- `Hom.toOverHom (mulBy A n)` is the `n`-th power of `𝟙 A.toOver` in the group of endomorphisms
of `A.toOver`. -/
theorem toOverHom_mulBy (A : AbelianVariety K) (n : ℤ) :
    Hom.toOverHom (mulBy A n) = 𝟙 A.toOver ^ n := by
  rw [mulBy_eq_zpow, Hom.toOverHom_zpow, Hom.toOverHom_id]

/-- On underlying schemes, `mulBy A n` is `(𝟙 A.toOver ^ n).left`. -/
theorem toSchemeHom_mulBy (A : AbelianVariety K) (n : ℤ) :
    Hom.toSchemeHom (mulBy A n) = (𝟙 A.toOver ^ n).left :=
  congrArg Over.Hom.left (toOverHom_mulBy A n)

/-! ### Dimension and nontriviality of `T₀A` -/

/-- The dimension of an abelian variety is nonnegative. -/
theorem dim_nonneg (A : AbelianVariety K) : 0 ≤ A.dim := by
  rw [← finrank_tangentSpace_eq_dim]
  exact_mod_cast Nat.zero_le _

/-- An abelian variety has positive dimension if and only if its dimension is nonzero. -/
theorem dim_pos_iff_ne_zero (A : AbelianVariety K) : 0 < A.dim ↔ A.dim ≠ 0 := by
  rw [← finrank_tangentSpace_eq_dim]
  norm_cast
  exact Nat.pos_iff_ne_zero

/-- An abelian variety has dimension zero if and only if its tangent space at `0` is a
subsingleton. -/
theorem dim_eq_zero_iff_subsingleton_tangentSpace (A : AbelianVariety K) :
    A.dim = 0 ↔ Subsingleton A.TangentSpace := by
  rw [← finrank_tangentSpace_eq_dim, ← Module.finrank_zero_iff (R := K) (M := A.TangentSpace)]
  norm_cast

/-- An abelian variety has positive dimension if and only if its tangent space at `0` is
nontrivial. -/
theorem dim_pos_iff_nontrivial_tangentSpace (A : AbelianVariety K) :
    0 < A.dim ↔ Nontrivial A.TangentSpace := by
  rw [← finrank_tangentSpace_eq_dim, ← Module.finrank_pos_iff (R := K) (M := A.TangentSpace)]
  norm_cast

/-! ### Unramifiedness and étaleness of multiplication by `n` -/

/-- Scalar multiplication `(c • LinearMap.id : V →ₗ[K] V)` over a field `K` is injective if and only
if `V` is a subsingleton or `c ≠ 0`. -/
private lemma injective_smul_id_iff {V : Type*} [AddCommGroup V] [Module K V] (c : K) :
    Function.Injective (c • (LinearMap.id : V →ₗ[K] V)) ↔ Subsingleton V ∨ c ≠ 0 := by
  constructor
  · intro hinj
    by_cases hc : c = 0
    · refine Or.inl ⟨fun x y ↦ hinj ?_⟩
      simp [hc]
    · exact Or.inr hc
  · rintro (hsub | hc)
    · exact Function.injective_of_subsingleton _
    · intro x y hxy
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_right_inj hc] using hxy

/-- The differential of `[n]` on `T₀A` is injective if and only if `A.dim = 0` or `(n : K) ≠ 0`. -/
theorem injective_tangentMap_mulBy_iff (A : AbelianVariety K) (n : ℤ) :
    Function.Injective (Hom.tangentMap (mulBy A n)) ↔ A.dim = 0 ∨ (n : K) ≠ 0 := by
  rw [tangentMap_mulBy, injective_smul_id_iff, dim_eq_zero_iff_subsingleton_tangentSpace]

/-- Multiplication by `n : ℤ` on an abelian variety `A` over `K` is formally unramified if and only
if `A.dim = 0` or `(n : K) ≠ 0`. -/
theorem formallyUnramified_toSchemeHom_mulBy_iff (A : AbelianVariety K) (n : ℤ) :
    FormallyUnramified (Hom.toSchemeHom (mulBy A n)) ↔ A.dim = 0 ∨ (n : K) ≠ 0 := by
  rw [Hom.formallyUnramified_toSchemeHom_iff, injective_tangentMap_mulBy_iff]

/-- Multiplication by `n : ℤ` on a positive-dimensional abelian variety over `K` is formally
unramified if and only if `(n : K) ≠ 0`. -/
theorem formallyUnramified_toSchemeHom_mulBy_iff_of_dim_pos {A : AbelianVariety K}
    (hdim : 0 < A.dim) (n : ℤ) :
    FormallyUnramified (Hom.toSchemeHom (mulBy A n)) ↔ (n : K) ≠ 0 := by
  rw [formallyUnramified_toSchemeHom_mulBy_iff, or_iff_right hdim.ne']

/-- Multiplication by `n : ℤ` on an abelian variety `A` over `K` is unramified if and only if
`A.dim = 0` or `(n : K) ≠ 0`. -/
theorem unramified_toSchemeHom_mulBy_iff (A : AbelianVariety K) (n : ℤ) :
    Unramified (Hom.toSchemeHom (mulBy A n)) ↔ A.dim = 0 ∨ (n : K) ≠ 0 := by
  rw [Hom.unramified_toSchemeHom_iff, injective_tangentMap_mulBy_iff]

/-- Multiplication by `n : ℤ` on a positive-dimensional abelian variety over `K` is unramified if
and only if `(n : K) ≠ 0`. -/
theorem unramified_toSchemeHom_mulBy_iff_of_dim_pos {A : AbelianVariety K} (hdim : 0 < A.dim)
    (n : ℤ) :
    Unramified (Hom.toSchemeHom (mulBy A n)) ↔ (n : K) ≠ 0 := by
  rw [unramified_toSchemeHom_mulBy_iff, or_iff_right hdim.ne']

/-- **Stacks Project, Tag 0BFH.** Multiplication by `n : ℤ` on an abelian variety `A` over a field
`K` is étale if and only if `A.dim = 0` or `(n : K) ≠ 0`. -/
@[stacks 0BFH]
theorem etale_toSchemeHom_mulBy_iff (A : AbelianVariety K) (n : ℤ) :
    Etale (Hom.toSchemeHom (mulBy A n)) ↔ A.dim = 0 ∨ (n : K) ≠ 0 := by
  rw [Hom.etale_toSchemeHom_end_iff_injective_tangentMap, injective_tangentMap_mulBy_iff]

/-- **Stacks Project, Tag 0BFH.** On an abelian variety `A` of positive dimension over a field `K`,
multiplication by `n : ℤ` is étale if and only if `(n : K) ≠ 0` (that is, `n` is invertible in
`K`). -/
@[stacks 0BFH]
theorem etale_toSchemeHom_mulBy_iff_of_dim_pos {A : AbelianVariety K} (hdim : 0 < A.dim) (n : ℤ) :
    Etale (Hom.toSchemeHom (mulBy A n)) ↔ (n : K) ≠ 0 := by
  rw [etale_toSchemeHom_mulBy_iff, or_iff_right hdim.ne']

/-- Whenever `(n : K) ≠ 0`, multiplication by `n` on `A` is étale. -/
theorem etale_toSchemeHom_mulBy_of_ne_zero (A : AbelianVariety K) {n : ℤ} (hn : (n : K) ≠ 0) :
    Etale (Hom.toSchemeHom (mulBy A n)) :=
  (etale_toSchemeHom_mulBy_iff A n).mpr (Or.inr hn)

/-- Over a field of characteristic zero, multiplication by any nonzero integer `n` is étale. -/
theorem etale_toSchemeHom_mulBy_of_charZero (A : AbelianVariety K) [CharZero K] {n : ℤ}
    (hn : n ≠ 0) :
    Etale (Hom.toSchemeHom (mulBy A n)) :=
  etale_toSchemeHom_mulBy_of_ne_zero A (Int.cast_ne_zero.mpr hn)

/-- On a positive-dimensional abelian variety, multiplication by `n` is not étale whenever
`(n : K) = 0`. -/
theorem not_etale_toSchemeHom_mulBy_of_eq_zero {A : AbelianVariety K} (hdim : 0 < A.dim) {n : ℤ}
    (hn : (n : K) = 0) :
    ¬ Etale (Hom.toSchemeHom (mulBy A n)) := by
  rw [etale_toSchemeHom_mulBy_iff_of_dim_pos hdim, not_not]
  exact hn

/-- In characteristic `p > 0`, multiplication by `p` on a positive-dimensional abelian variety is
not étale. (Notice `CharP K 0` also gives `[0]`, which is likewise not étale for `0 < A.dim`.) -/
theorem not_etale_toSchemeHom_mulBy_charP {A : AbelianVariety K} (hdim : 0 < A.dim) (p : ℕ)
    [CharP K p] :
    ¬ Etale (Hom.toSchemeHom (mulBy A p)) :=
  not_etale_toSchemeHom_mulBy_of_eq_zero hdim (by rw [Int.cast_natCast, CharP.cast_eq_zero])

/-- On the zero-dimensional abelian variety `trivial K`, multiplication by every integer `n` is
étale. -/
theorem etale_toSchemeHom_mulBy_trivial (K : Type u) [Field K] (n : ℤ) :
    Etale (Hom.toSchemeHom (mulBy (trivial K) n)) :=
  (etale_toSchemeHom_mulBy_iff (trivial K) n).mpr (Or.inl (dim_trivial K))

/-! ### Prime-to-characteristic multiplication isogenies and torsion -/

/-- Whenever `(n : K) ≠ 0`, multiplication by `n` on an abelian variety `A` over `K` is an
isogeny. -/
theorem isIsogeny_mulBy_of_ne_zero (A : AbelianVariety K) {n : ℤ} (hn : (n : K) ≠ 0) :
    IsIsogeny (mulBy A n) := by
  have := etale_toSchemeHom_mulBy_of_ne_zero A hn
  exact isIsogeny_of_etale (mulBy A n)

/-- Over a field of characteristic zero, multiplication by every nonzero integer `n` is an
isogeny. -/
theorem isIsogeny_mulBy_of_charZero (A : AbelianVariety K) [CharZero K] {n : ℤ} (hn : n ≠ 0) :
    IsIsogeny (mulBy A n) :=
  isIsogeny_mulBy_of_ne_zero A (Int.cast_ne_zero.mpr hn)

private lemma forget₂Grp_intCast_left_eq_toSchemeHom_mulBy (A : AbelianVariety K) (n : ℤ) :
    ((CommGrp.forget₂Grp (Over (Spec (.of K)))).map
      (n : CategoryTheory.End (CommGrp.mk A.toOver)).asHom).hom.hom.left =
      Hom.toSchemeHom (mulBy A n) := by
  rw [CommGrp.forget₂Grp_map_hom, CommGrp.intCast_hom_hom_hom, toSchemeHom_mulBy]

/-- If `A.dim = 0` or `(n : K) ≠ 0`, then the `n`-torsion group scheme `A[n]` is étale over
`Spec K`. -/
theorem etale_torsion_hom_of_dim_eq_zero_or_ne_zero {A : AbelianVariety K} {n : ℤ}
    (h : A.dim = 0 ∨ (n : K) ≠ 0) :
    Etale (GroupScheme.torsion (CommGrp.mk A.toOver) n).X.hom := by
  rw [GroupScheme.torsion_eq_kernel]
  refine Grp.etale_kernel_hom _ ?_
  rw [forget₂Grp_intCast_left_eq_toSchemeHom_mulBy]
  exact (etale_toSchemeHom_mulBy_iff A n).mpr h

/-- Whenever `(n : K) ≠ 0`, the `n`-torsion group scheme `A[n]` is étale over `Spec K`. -/
theorem etale_torsion_hom_of_ne_zero (A : AbelianVariety K) {n : ℤ} (hn : (n : K) ≠ 0) :
    Etale (GroupScheme.torsion (CommGrp.mk A.toOver) n).X.hom :=
  etale_torsion_hom_of_dim_eq_zero_or_ne_zero (Or.inr hn)

/-- Whenever `(n : K) ≠ 0`, the `n`-torsion group scheme `A[n]` is finite over `Spec K`. -/
theorem isFinite_torsion_hom_of_ne_zero (A : AbelianVariety K) {n : ℤ} (hn : (n : K) ≠ 0) :
    IsFinite (GroupScheme.torsion (CommGrp.mk A.toOver) n).X.hom := by
  rw [GroupScheme.torsion_eq_kernel]
  let φ := (CommGrp.forget₂Grp (Over (Spec (.of K)))).map
    (n : CategoryTheory.End (CommGrp.mk A.toOver)).asHom
  have : IsFinite φ.hom.hom.left := by
    rw [forget₂Grp_intCast_left_eq_toSchemeHom_mulBy]
    exact (isIsogeny_mulBy_of_ne_zero A hn).isFinite
  exact GroupScheme.isFinite_kernel_hom (f := φ)

end

end TauCeti.AlgebraicGeometry.AbelianVariety
