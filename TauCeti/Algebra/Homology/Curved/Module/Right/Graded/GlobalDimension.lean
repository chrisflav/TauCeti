/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Comparison
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Adjunction
public import TauCeti.CategoryTheory.Abelian.Injective.Dimension
public import TauCeti.CategoryTheory.Triangulated.VerdierLocalization

/-!
# Finite graded global dimension and Positselski's Theorem 7.8(a)

For a curved differential graded algebra `(𝒜, d, w)` over `R`, the absolutely acyclic curved right
modules are always both coacyclic and contraacyclic, giving canonical triangulated localization
comparisons `AbsoluteDerivedCategory.toCoderived` (`D_abs → D_co`) and
`AbsoluteDerivedCategory.toContraderived` (`D_abs → D_ctr`). In general all three acyclic classes
and derived categories of the second kind are distinct: already over the dual numbers
`k[ε]/(ε²)` with `d = 0` and `w = 0`, an unbounded acyclic periodic complex of free modules is
neither coacyclic nor contraacyclic, and the coderived and contraderived categories differ.

This file proves Positselski's Theorem 7.8(a) together with its objectwise refinements:

1. **Objectwise finite graded projective dimension**: if the underlying graded right module
   `toGradedModuleCat M` has finite projective dimension in the abelian category of graded right
   `A`-modules, then `M` is contraacyclic if and only if `M` is absolutely acyclic. The proof
   inducts on projective dimension: in the base case `M` is graded-projective and right orthogonal
   to contraacyclic objects, hence contractible; in the inductive step, `exists_epi_from_inducedObj`
   provides a closed epimorphism `G⁺(P) ⟶ M` from a contractible graded-projective curved module,
   reducing the projective dimension of the kernel by `1` while two-out-of-three transfers both
   contraacyclicity and absolute acyclicity across the short exact sequence.
2. **Objectwise finite graded injective dimension**: dually, if `toGradedModuleCat M` has finite
   injective dimension, then `M` is coacyclic if and only if `M` is absolutely acyclic, using
   `exists_mono_to_coinducedObj` into `G⁻(I)`.
3. **Finite right graded global dimension (Positselski's Theorem 7.8(a))**: when every graded right
   `A`-module has projective dimension at most `n`, the category of graded right `A`-modules has
   both enough projectives and enough injectives, so every graded right `A`-module also has
   injective dimension at most `n`. Consequently `absolutelyAcyclic R h = coacyclic R h =
   contraacyclic R h`, both canonical localization comparisons `toCoderived R h` and
   `toContraderived R h` are equivalences of categories, and the coderived, contraderived, and
   absolute derived categories of curved right modules coincide.

## Main results

* `TauCeti.CurvedDGRightModuleCat.contraacyclic_iff_absolutelyAcyclic_of_hasProjectiveDimensionLT`:
  contraacyclicity coincides with absolute acyclicity on curved right modules of finite underlying
  graded projective dimension.
* `TauCeti.CurvedDGRightModuleCat.coacyclic_iff_absolutelyAcyclic_of_hasInjectiveDimensionLT`:
  coacyclicity coincides with absolute acyclicity on curved right modules of finite underlying
  graded injective dimension.
* `CurvedDGRightModuleCat.absolutelyAcyclic_eq_contraacyclic_of_forall_hasProjectiveDimensionLE`,
  `CurvedDGRightModuleCat.absolutelyAcyclic_eq_coacyclic_of_forall_hasProjectiveDimensionLE`, and
  `CurvedDGRightModuleCat.coacyclic_eq_contraacyclic_of_forall_hasProjectiveDimensionLE`:
  the three acyclic classes coincide under finite right graded global dimension.
* `AbsoluteDerivedCategory.isEquivalence_toContraderived_of_forall_hasProjectiveDimensionLE` and
  `AbsoluteDerivedCategory.isEquivalence_toCoderived_of_forall_hasProjectiveDimensionLE`:
  **Positselski's Theorem 7.8(a)** — both canonical comparisons `D_abs → D_ctr` and `D_abs → D_co`
  are equivalences when the underlying graded algebra has finite right graded global dimension.
* `TauCeti.CurvedDGRightModuleCat.coderivedEquivContraderivedOfForallHasProjectiveDimensionLE`:
  the induced equivalence `CoderivedCategory R h ≌ ContraderivedCategory R h`.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6, Theorem.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Theorem 7.8(a).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  (h : IsCurvedDGAlgebra 𝒜 d w)

/-! ### Objectwise finite graded projective dimension -/

private theorem absolutelyAcyclic_of_contraacyclic_of_gradedProjective
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (hM : contraacyclic R h (DGHomotopyCategory.of R M))
    (hPM : Projective (toGradedModuleCat M)) :
    absolutelyAcyclic R h (DGHomotopyCategory.of R M) := by
  have hP : gradedProjective R h (DGHomotopyCategory.of R M) :=
    (gradedProjective_iff _).mpr hPM
  have hZero : IsZero (DGHomotopyCategory.of R M) :=
    (IsZero.iff_id_eq_zero _).mpr
      (contraacyclic_le_rightOrthogonal_gradedProjective R h _ hM
        (𝟙 (DGHomotopyCategory.of R M)) hP)
  exact (absolutelyAcyclic R h).prop_of_isZero hZero

/-- A contraacyclic curved right module whose underlying graded right module has finite projective
dimension `< n` is absolutely acyclic. -/
theorem absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT :
    ∀ (n : ℕ) {M : CurvedDGRightModuleCat.{u, u, u} h},
      contraacyclic R h (DGHomotopyCategory.of R M) →
      HasProjectiveDimensionLT (toGradedModuleCat M) n →
      absolutelyAcyclic R h (DGHomotopyCategory.of R M)
  | 0, M, hM, hd => by
    have : HasProjectiveDimensionLT (toGradedModuleCat M) 0 := hd
    have h1 : HasProjectiveDimensionLT (toGradedModuleCat M) 1 :=
      hasProjectiveDimensionLT_of_ge (toGradedModuleCat M) 0 1 (Nat.zero_le 1)
    exact absolutelyAcyclic_of_contraacyclic_of_gradedProjective h hM
      (projective_iff_hasProjectiveDimensionLT_one.mpr h1)
  | 1, M, hM, hd =>
    absolutelyAcyclic_of_contraacyclic_of_gradedProjective h hM
      (projective_iff_hasProjectiveDimensionLT_one.mpr hd)
  | n + 2, M, hM, hd => by
    obtain ⟨P, hP, π, hπ⟩ := exists_epi_from_inducedObj h M
    let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
    have hG_zero : IsZero (DGHomotopyCategory.of R (inducedObj h P)) :=
      isZero_homotopy_inducedObj h P
    have hK_contra : contraacyclic R h ((dgClosedToHomotopy R).obj S.X₁) :=
      prop_X₁_of_shortExact (contraacyclic R h) (totalizations_le_contraacyclic R h) hS
        ((contraacyclic R h).prop_of_isZero hG_zero) hM
    have hS_gr : (S.map (forgetDifferential (h := h))).ShortExact :=
      hS.map_of_exact (forgetDifferential (h := h))
    have hK_dim : HasProjectiveDimensionLT (toGradedModuleCat (ForgetEnrichment.to _ S.X₁))
        (n + 1) :=
      (hS_gr.hasProjectiveDimensionLT_X₃_iff n
        (projective_toGradedModuleCat_inducedObj h P)).mp hd
    have hK_abs : absolutelyAcyclic R h ((dgClosedToHomotopy R).obj S.X₁) :=
      absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT (n + 1) hK_contra hK_dim
    exact prop_X₃_of_shortExact (absolutelyAcyclic R h) (totalizations_le_absolutelyAcyclic R h)
      hS hK_abs ((absolutelyAcyclic R h).prop_of_isZero hG_zero)

/-- If the underlying graded right module of `M` has projective dimension `< n`, then `M` is
contraacyclic if and only if `M` is absolutely acyclic. -/
theorem contraacyclic_iff_absolutelyAcyclic_of_hasProjectiveDimensionLT (n : ℕ)
    (M : CurvedDGRightModuleCat.{u, u, u} h)
    [hd : HasProjectiveDimensionLT (toGradedModuleCat M) n] :
    contraacyclic R h (DGHomotopyCategory.of R M) ↔
      absolutelyAcyclic R h (DGHomotopyCategory.of R M) :=
  ⟨fun hM ↦ absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT h n hM hd,
    fun hM ↦ absolutelyAcyclic_le_contraacyclic R h _ hM⟩

/-- If the underlying graded right module of `M` has projective dimension `≤ n`, then `M` is
contraacyclic if and only if `M` is absolutely acyclic. -/
theorem contraacyclic_iff_absolutelyAcyclic_of_hasProjectiveDimensionLE (n : ℕ)
    (M : CurvedDGRightModuleCat.{u, u, u} h)
    [HasProjectiveDimensionLE (toGradedModuleCat M) n] :
    contraacyclic R h (DGHomotopyCategory.of R M) ↔
      absolutelyAcyclic R h (DGHomotopyCategory.of R M) :=
  contraacyclic_iff_absolutelyAcyclic_of_hasProjectiveDimensionLT h (n + 1) M

/-! ### Objectwise finite graded injective dimension -/

private theorem absolutelyAcyclic_of_coacyclic_of_gradedInjective
    {M : CurvedDGRightModuleCat.{u, u, u} h}
    (hM : coacyclic R h (DGHomotopyCategory.of R M))
    (hIM : Injective (toGradedModuleCat M)) :
    absolutelyAcyclic R h (DGHomotopyCategory.of R M) := by
  have hI : gradedInjective R h (DGHomotopyCategory.of R M) :=
    (gradedInjective_iff _).mpr hIM
  have hZero : IsZero (DGHomotopyCategory.of R M) :=
    (IsZero.iff_id_eq_zero _).mpr
      (coacyclic_le_leftOrthogonal_gradedInjective R h _ hM
        (𝟙 (DGHomotopyCategory.of R M)) hI)
  exact (absolutelyAcyclic R h).prop_of_isZero hZero

/-- A coacyclic curved right module whose underlying graded right module has finite injective
dimension `< n` is absolutely acyclic. -/
theorem absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT :
    ∀ (n : ℕ) {M : CurvedDGRightModuleCat.{u, u, u} h},
      coacyclic R h (DGHomotopyCategory.of R M) →
      HasInjectiveDimensionLT (toGradedModuleCat M) n →
      absolutelyAcyclic R h (DGHomotopyCategory.of R M)
  | 0, M, hM, hd => by
    have : HasInjectiveDimensionLT (toGradedModuleCat M) 0 := hd
    have h1 : HasInjectiveDimensionLT (toGradedModuleCat M) 1 :=
      hasInjectiveDimensionLT_of_ge (toGradedModuleCat M) 0 1 (Nat.zero_le 1)
    exact absolutelyAcyclic_of_coacyclic_of_gradedInjective h hM
      (injective_iff_hasInjectiveDimensionLT_one.mpr h1)
  | 1, M, hM, hd =>
    absolutelyAcyclic_of_coacyclic_of_gradedInjective h hM
      (injective_iff_hasInjectiveDimensionLT_one.mpr hd)
  | n + 2, M, hM, hd => by
    obtain ⟨I, hI, ι, hι⟩ := exists_mono_to_coinducedObj h M
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    have hG_zero : IsZero (DGHomotopyCategory.of R (coinducedObj h I)) :=
      isZero_homotopy_coinducedObj h I
    have hQ_co : coacyclic R h ((dgClosedToHomotopy R).obj S.X₃) :=
      prop_X₃_of_shortExact (coacyclic R h) (totalizations_le_coacyclic R h) hS
        hM ((coacyclic R h).prop_of_isZero hG_zero)
    have hS_gr : (S.map (forgetDifferential (h := h))).ShortExact :=
      hS.map_of_exact (forgetDifferential (h := h))
    have hQ_dim : HasInjectiveDimensionLT (toGradedModuleCat (ForgetEnrichment.to _ S.X₃))
        (n + 1) :=
      (hS_gr.hasInjectiveDimensionLT_X₃_iff n
        (injective_toGradedModuleCat_coinducedObj h I)).mpr hd
    have hQ_abs : absolutelyAcyclic R h ((dgClosedToHomotopy R).obj S.X₃) :=
      absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT (n + 1) hQ_co hQ_dim
    exact prop_X₁_of_shortExact (absolutelyAcyclic R h) (totalizations_le_absolutelyAcyclic R h)
      hS ((absolutelyAcyclic R h).prop_of_isZero hG_zero) hQ_abs

/-- If the underlying graded right module of `M` has injective dimension `< n`, then `M` is
coacyclic if and only if `M` is absolutely acyclic. -/
theorem coacyclic_iff_absolutelyAcyclic_of_hasInjectiveDimensionLT (n : ℕ)
    (M : CurvedDGRightModuleCat.{u, u, u} h)
    [hd : HasInjectiveDimensionLT (toGradedModuleCat M) n] :
    coacyclic R h (DGHomotopyCategory.of R M) ↔
      absolutelyAcyclic R h (DGHomotopyCategory.of R M) :=
  ⟨fun hM ↦ absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT h n hM hd,
    fun hM ↦ absolutelyAcyclic_le_coacyclic R h _ hM⟩

/-- If the underlying graded right module of `M` has injective dimension `≤ n`, then `M` is
coacyclic if and only if `M` is absolutely acyclic. -/
theorem coacyclic_iff_absolutelyAcyclic_of_hasInjectiveDimensionLE (n : ℕ)
    (M : CurvedDGRightModuleCat.{u, u, u} h)
    [HasInjectiveDimensionLE (toGradedModuleCat M) n] :
    coacyclic R h (DGHomotopyCategory.of R M) ↔
      absolutelyAcyclic R h (DGHomotopyCategory.of R M) :=
  coacyclic_iff_absolutelyAcyclic_of_hasInjectiveDimensionLT h (n + 1) M

/-! ### Finite right graded global dimension (Positselski's Theorem 7.8(a)) -/

section GlobalDimension

variable (R)

/-- When every graded right `A`-module has projective dimension `≤ n`, the contraacyclic and
absolutely acyclic classes coincide. -/
theorem absolutelyAcyclic_eq_contraacyclic_of_forall_hasProjectiveDimensionLE {n : ℕ}
    (hd : ∀ E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE E n) :
    absolutelyAcyclic R h = contraacyclic R h := by
  refine le_antisymm (absolutelyAcyclic_le_contraacyclic R h) fun X hX ↦ ?_
  exact absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT h (n + 1) hX
    (hd (toGradedModuleCat X.underlying))

/-- When every graded right `A`-module has injective dimension `≤ n`, the coacyclic and absolutely
acyclic classes coincide. -/
theorem absolutelyAcyclic_eq_coacyclic_of_forall_hasInjectiveDimensionLE {n : ℕ}
    (hd : ∀ E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasInjectiveDimensionLE E n) :
    absolutelyAcyclic R h = coacyclic R h := by
  refine le_antisymm (absolutelyAcyclic_le_coacyclic R h) fun X hX ↦ ?_
  exact absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT h (n + 1) hX
    (hd (toGradedModuleCat X.underlying))

/-- When every graded right `A`-module has projective dimension `≤ n`, every graded right
`A`-module also has injective dimension `≤ n`, so the coacyclic and absolutely acyclic classes
coincide. -/
theorem absolutelyAcyclic_eq_coacyclic_of_forall_hasProjectiveDimensionLE {n : ℕ}
    (hd : ∀ E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE E n) :
    absolutelyAcyclic R h = coacyclic R h := by
  have : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece :=
    (InternalGrading.ofDecomposition_piece 𝒜).symm ▸ inferInstance
  exact absolutelyAcyclic_eq_coacyclic_of_forall_hasInjectiveDimensionLE R h
    ((CategoryTheory.forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE
      (GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) n).mp hd)

/-- **Positselski's Theorem 7.8(a) (acyclic classes).** When every graded right `A`-module has
projective dimension `≤ n`, the coacyclic and contraacyclic classes coincide. -/
theorem coacyclic_eq_contraacyclic_of_forall_hasProjectiveDimensionLE {n : ℕ}
    (hd : ∀ E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE E n) :
    coacyclic R h = contraacyclic R h :=
  (absolutelyAcyclic_eq_coacyclic_of_forall_hasProjectiveDimensionLE R h hd).symm.trans
    (absolutelyAcyclic_eq_contraacyclic_of_forall_hasProjectiveDimensionLE R h hd)

/-- **Positselski's Theorem 7.8(a) (contraderived comparison).** When every graded right `A`-module
has projective dimension `≤ n`, the canonical comparison functor
`AbsoluteDerivedCategory.toContraderived R h : D_abs → D_ctr` is an equivalence of categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toContraderived_of_forall_hasProjectiveDimensionLE
    {n : ℕ}
    (hd : ∀ E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE E n) :
    (AbsoluteDerivedCategory.toContraderived R h).IsEquivalence := by
  have hle : contraacyclic R h ≤ absolutelyAcyclic R h :=
    (absolutelyAcyclic_eq_contraacyclic_of_forall_hasProjectiveDimensionLE R h hd).symm.le
  let Φ := ObjectProperty.trWLocalizerMorphismOfLE (absolutelyAcyclic_le_contraacyclic R h)
  have : Φ.IsLocalizedEquivalence :=
    ObjectProperty.isLocalizedEquivalence_trWLocalizerMorphismOfLE _ hle
  have : CatCommSq Φ.functor (AbsoluteDerivedCategory.Q R h) (ContraderivedCategory.Q R h)
      (AbsoluteDerivedCategory.toContraderived R h) :=
    ⟨Functor.isoWhiskerRight (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor _)) _ ≪≫
      Functor.leftUnitor _ ≪≫ (AbsoluteDerivedCategory.toContraderivedFactors R h).symm⟩
  exact Φ.isEquivalence (AbsoluteDerivedCategory.Q R h) (ContraderivedCategory.Q R h)
    (AbsoluteDerivedCategory.toContraderived R h)

/-- When every graded right `A`-module has injective dimension `≤ n`, the canonical comparison
functor `AbsoluteDerivedCategory.toCoderived R h : D_abs → D_co` is an equivalence of
categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toCoderived_of_forall_hasInjectiveDimensionLE
    {n : ℕ}
    (hd : ∀ E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasInjectiveDimensionLE E n) :
    (AbsoluteDerivedCategory.toCoderived R h).IsEquivalence := by
  have hle : coacyclic R h ≤ absolutelyAcyclic R h :=
    (absolutelyAcyclic_eq_coacyclic_of_forall_hasInjectiveDimensionLE R h hd).symm.le
  let Φ := ObjectProperty.trWLocalizerMorphismOfLE (absolutelyAcyclic_le_coacyclic R h)
  have : Φ.IsLocalizedEquivalence :=
    ObjectProperty.isLocalizedEquivalence_trWLocalizerMorphismOfLE _ hle
  have : CatCommSq Φ.functor (AbsoluteDerivedCategory.Q R h) (CoderivedCategory.Q R h)
      (AbsoluteDerivedCategory.toCoderived R h) :=
    ⟨Functor.isoWhiskerRight (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor _)) _ ≪≫
      Functor.leftUnitor _ ≪≫ (AbsoluteDerivedCategory.toCoderivedFactors R h).symm⟩
  exact Φ.isEquivalence (AbsoluteDerivedCategory.Q R h) (CoderivedCategory.Q R h)
    (AbsoluteDerivedCategory.toCoderived R h)

/-- **Positselski's Theorem 7.8(a) (coderived comparison).** When every graded right `A`-module has
projective dimension `≤ n`, the canonical comparison functor
`AbsoluteDerivedCategory.toCoderived R h : D_abs → D_co` is an equivalence of categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toCoderived_of_forall_hasProjectiveDimensionLE
    {n : ℕ}
    (hd : ∀ E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE E n) :
    (AbsoluteDerivedCategory.toCoderived R h).IsEquivalence := by
  have : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece :=
    (InternalGrading.ofDecomposition_piece 𝒜).symm ▸ inferInstance
  exact AbsoluteDerivedCategory.isEquivalence_toCoderived_of_forall_hasInjectiveDimensionLE R h
    ((CategoryTheory.forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE
      (GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) n).mp hd)

/-- **Positselski's Theorem 7.8(a) (coderived–contraderived equivalence).** When every graded right
`A`-module has projective dimension `≤ n`, the coderived and contraderived categories of curved
right modules are canonically equivalent via the absolute derived category. -/
noncomputable def coderivedEquivContraderivedOfForallHasProjectiveDimensionLE {n : ℕ}
    (hd : ∀ E : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE E n) :
    CoderivedCategory R h ≌ ContraderivedCategory R h :=
  letI := AbsoluteDerivedCategory.isEquivalence_toCoderived_of_forall_hasProjectiveDimensionLE
    R h hd
  letI := AbsoluteDerivedCategory.isEquivalence_toContraderived_of_forall_hasProjectiveDimensionLE
    R h hd
  (AbsoluteDerivedCategory.toCoderived R h).asEquivalence.symm.trans
    (AbsoluteDerivedCategory.toContraderived R h).asEquivalence

end GlobalDimension

end TauCeti.CurvedDGRightModuleCat
