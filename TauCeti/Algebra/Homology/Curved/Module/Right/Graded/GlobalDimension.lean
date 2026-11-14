/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Comparison
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective
public import TauCeti.CategoryTheory.Abelian.Injective.Dimension
import TauCeti.Algebra.Category.GradedModuleCat.Coinduced
import TauCeti.Algebra.Category.GradedModuleCat.Free
import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Induced

/-!
# Coincidence of curved derived categories under finite graded global dimension

Let `(A, d, w)` be a right-convention curved differential graded algebra over a commutative ring
`R`. When the underlying graded ring `(A, 𝒜)` has finite right graded global dimension — meaning
that a single natural number `n` bounds the projective dimensions (equivalently, the injective
dimensions) of all objects in the abelian category of graded right `A`-modules — Positselski proved
that the three acyclic classes of the second kind on curved right `A`-modules coincide:
`coacyclic = contraacyclic = absolutelyAcyclic`. Consequently, the comparison triangle functors
between the absolute derived, coderived, and contraderived categories are equivalences, and the
homotopy subcategories of graded-projective and graded-injective curved modules map equivalently
onto all three derived categories of the second kind.

The argument works object by object before imposing a global bound:

* Unconditionally, the full subcategories of graded-projective and graded-injective curved modules
  in `DGHomotopyCategory` embed fully and faithfully into `ContraderivedCategory` and
  `CoderivedCategory`, respectively, by the orthogonality theorems of
  `Curved.Module.Right.Graded.Projective` and `Curved.Module.Right.Graded.Injective`.
* In any short exact sequence `0 ⟶ K ⟶ E ⟶ M ⟶ 0` of curved right modules whose middle term `E`
  is contractible, the totalization `cone(cone(K ⟶ E) ⟶ M)` is absolutely acyclic, while
  `cone(K ⟶ E) ≅ K⟦1⟧` in the homotopy category. Thus `M ≅ K⟦1⟧` and `K ≅ M⟦-1⟧` in
  `AbsoluteDerivedCategory`.
* Applying the left adjoint `G⁺` (`inducedObj`) to a projective presentation of the underlying
  graded module `toGradedModuleCat M` yields an epimorphism `G⁺(P₀) ⟶ M` with contractible
  graded-projective source; dimension shifting along its kernel resolves any curved module `X` of
  projective dimension `≤ n` in `AbsoluteDerivedCategory` by a graded-projective curved module `P`.
  If `X` is contraacyclic, `P` becomes zero in `ContraderivedCategory`, hence `P` is contractible
  by full faithfulness, hence `X` is zero in `AbsoluteDerivedCategory` and therefore absolutely
  acyclic.
* Dually, `GradedModuleCat` has enough injectives via coinduced graded modules, and applying the
  right adjoint `G⁻` (`coinducedObj`) to an injective presentation resolves any curved module `X`
  of injective dimension `≤ n` in `AbsoluteDerivedCategory` by a graded-injective curved module
  `I`; if `X` is coacyclic, full faithfulness into `CoderivedCategory` forces `I` to be
  contractible and `X` to be absolutely acyclic.
* Under a uniform projective-dimension bound `≤ n` on graded right `A`-modules, projective-injective
  global symmetry
  (`CategoryTheory.forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE`) supplies the
  same injective-dimension bound, so all three acyclic classes coincide and every object of
  `AbsoluteDerivedCategory` admits both graded-projective and graded-injective replacements.

## Main definitions and results

* `ContraderivedCategory.fullyFaithfulGradedProjective` and
  `CoderivedCategory.fullyFaithfulGradedInjective`: unconditional full faithfulness of the
  graded-projective and graded-injective homotopy subcategories into `D_ctr` and `D_co`.
* `AbsoluteDerivedCategory.exists_gradedProjective_Q_obj_iso` and
  `AbsoluteDerivedCategory.exists_gradedInjective_Q_obj_iso`: graded-projective and
  graded-injective replacements in `D_abs` for curved modules whose underlying graded module has
  finite projective or injective dimension.
* `contraacyclic_iff_absolutelyAcyclic_of_hasProjectiveDimensionLE` and
  `coacyclic_iff_absolutelyAcyclic_of_hasInjectiveDimensionLE`: pointwise equivalence with
  absolute acyclicity under finite projective or injective dimension of the underlying graded
  module.
* `coacyclic_eq_absolutelyAcyclic`, `contraacyclic_eq_absolutelyAcyclic`, and
  `coacyclic_eq_contraacyclic`: Positselski's coincidence of the three acyclic classes under finite
  right graded global dimension.
* `AbsoluteDerivedCategory.isEquivalence_toCoderived`,
  `AbsoluteDerivedCategory.isEquivalence_toContraderived`,
  `AbsoluteDerivedCategory.coderivedEquivalence`,
  `AbsoluteDerivedCategory.contraderivedEquivalence`,
  `CoderivedCategory.toContraderived`, and `coderivedContraderivedEquivalence`: triangle
  equivalences identifying `D_abs`, `D_co`, and `D_ctr`.
* `ContraderivedCategory.isEquivalence_gradedProjective`,
  `CoderivedCategory.isEquivalence_gradedInjective`,
  `AbsoluteDerivedCategory.isEquivalence_gradedProjective`, and
  `AbsoluteDerivedCategory.isEquivalence_gradedInjective`: equivalences from the
  graded-projective and graded-injective homotopy subcategories onto the derived categories of the
  second kind.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6, Theorem 3.6(a).
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6, Theorem 7.8(a).
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

private theorem isLocalization_of_eq {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {W₁ W₂ : MorphismProperty C} [hL : L.IsLocalization W₁] (hW : W₁ = W₂) :
    L.IsLocalization W₂ :=
  hW ▸ hL

private theorem isLocalizedEquivalence_trWLocalizerMorphismOfLE
    {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {P Q : ObjectProperty C} (hle : P ≤ Q) (heq : Q = P) :
    (ObjectProperty.trWLocalizerMorphismOfLE hle).IsLocalizedEquivalence := by
  let Φ := ObjectProperty.trWLocalizerMorphismOfLE hle
  have : Q.trW.Q.IsLocalization P.trW :=
    isLocalization_of_eq Q.trW.Q (congrArg ObjectProperty.trW heq)
  have : (Φ.functor ⋙ Q.trW.Q).IsLocalization P.trW :=
    Functor.IsLocalization.of_iso P.trW
      ((Functor.leftUnitor Q.trW.Q).symm ≪≫
        Functor.isoWhiskerRight
          (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor hle).symm) Q.trW.Q)
  exact LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization Φ Q.trW.Q

private theorem isEquivalence_of_factors
    {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {P Q : ObjectProperty C} (hle : P ≤ Q) (heq : Q = P)
    (L₁ : C ⥤ D₁) [L₁.IsLocalization P.trW]
    (L₂ : C ⥤ D₂) [L₂.IsLocalization Q.trW]
    (G : D₁ ⥤ D₂) (fac : L₁ ⋙ G ≅ L₂) :
    G.IsEquivalence := by
  let Φ := ObjectProperty.trWLocalizerMorphismOfLE hle
  have := isLocalizedEquivalence_trWLocalizerMorphismOfLE hle heq
  let : CatCommSq Φ.functor L₁ L₂ G :=
    ⟨Functor.isoWhiskerRight (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor hle)) L₂ ≪≫
      Functor.leftUnitor L₂ ≪≫ fac.symm⟩
  exact Φ.isEquivalence L₁ L₂ G

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

local instance : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-! ### Unconditional full faithfulness on graded-projective and graded-injective subcategories -/

/-- The composite of the graded-projective homotopy subcategory inclusion with localization to the
contraderived category is faithful. -/
instance ContraderivedCategory.instFaithfulGradedProjective :
    ((gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h).Faithful where
  map_injective {X Y} {_ _} hfg :=
    (gradedProjective R h).ι.map_injective
      ((ContraderivedCategory.map_bijective_of_gradedProjective X.property Y.obj).injective hfg)

/-- The composite of the graded-projective homotopy subcategory inclusion with localization to the
contraderived category is full. -/
instance ContraderivedCategory.instFullGradedProjective :
    ((gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h).Full where
  map_surjective {X Y} φ :=
    let ⟨f, hf⟩ :=
      (ContraderivedCategory.map_bijective_of_gradedProjective X.property Y.obj).surjective φ
    ⟨ObjectProperty.homMk f, hf⟩

variable (R h) in
/-- **Full faithfulness of graded-projective curved modules in the contraderived category.** The
homotopy subcategory of graded-projective curved right modules embeds fully and faithfully into
`ContraderivedCategory R h` with no homological dimension hypothesis. -/
noncomputable def ContraderivedCategory.fullyFaithfulGradedProjective :
    ((gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h).FullyFaithful :=
  .ofFullyFaithful _

/-- The composite of the graded-injective homotopy subcategory inclusion with localization to the
coderived category is faithful. -/
instance CoderivedCategory.instFaithfulGradedInjective :
    ((gradedInjective R h).ι ⋙ CoderivedCategory.Q R h).Faithful where
  map_injective {X Y} {_ _} hfg :=
    (gradedInjective R h).ι.map_injective
      ((CoderivedCategory.map_bijective_of_gradedInjective X.obj Y.property).injective hfg)

/-- The composite of the graded-injective homotopy subcategory inclusion with localization to the
coderived category is full. -/
instance CoderivedCategory.instFullGradedInjective :
    ((gradedInjective R h).ι ⋙ CoderivedCategory.Q R h).Full where
  map_surjective {X Y} φ :=
    let ⟨f, hf⟩ :=
      (CoderivedCategory.map_bijective_of_gradedInjective X.obj Y.property).surjective φ
    ⟨ObjectProperty.homMk f, hf⟩

variable (R h) in
/-- **Full faithfulness of graded-injective curved modules in the coderived category.** The
homotopy subcategory of graded-injective curved right modules embeds fully and faithfully into
`CoderivedCategory R h` with no homological dimension hypothesis. -/
noncomputable def CoderivedCategory.fullyFaithfulGradedInjective :
    ((gradedInjective R h).ι ⋙ CoderivedCategory.Q R h).FullyFaithful :=
  .ofFullyFaithful _

/-! ### Short exact sequences with contractible middle term in the absolute derived category -/

namespace AbsoluteDerivedCategory

/-- For any short exact sequence `K ⟶ E ⟶ M` of curved right modules, the induced map
`cone(K ⟶ E) ⟶ M` has absolutely acyclic cone (the totalization of the sequence) and therefore
becomes an isomorphism in `AbsoluteDerivedCategory R h`. -/
theorem isIso_Q_map_coneDesc
    {S : ShortComplex
      (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))}
    (hS : S.ShortExact) :
    IsIso ((Q R h).map ((dgClosedToHomotopy R).map (coneDesc S.f S.g S.zero))) := by
  have hTot := totalizations_le_absolutelyAcyclic R h _ (totalizations_totalization hS)
  rw [totalization_eq] at hTot
  exact Localization.inverts (Q R h) (absolutelyAcyclic R h).trW _
    (ObjectProperty.trW.mk (absolutelyAcyclic R h)
      (coneTriangle_distinguished (coneDesc S.f S.g S.zero)) hTot)

/-- In a short exact sequence `K ⟶ E ⟶ M` of curved right modules whose middle term `E` is zero in
the homotopy category, `M` is isomorphic to `K⟦1⟧` in `AbsoluteDerivedCategory R h`. -/
noncomputable def isoShiftOneOfShortExact
    {S : ShortComplex
      (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))}
    (hS : S.ShortExact) (h₂ : IsZero ((dgClosedToHomotopy R).obj S.X₂)) :
    (Q R h).obj ((dgClosedToHomotopy R).obj S.X₃) ≅
      ((Q R h).obj ((dgClosedToHomotopy R).obj S.X₁))⟦(1 : ℤ)⟧ := by
  have := isIso_Q_map_coneDesc hS
  have : IsIso (coneTriangle S.f).mor₃ :=
    ((coneTriangle S.f).isZero₂_iff_isIso₃ (coneTriangle_distinguished S.f)).mp h₂
  exact (asIso ((Q R h).map ((dgClosedToHomotopy R).map (coneDesc S.f S.g S.zero)))).symm ≪≫
    (Q R h).mapIso (asIso (coneTriangle S.f).mor₃) ≪≫
    ((Q R h).commShiftIso (1 : ℤ)).app ((dgClosedToHomotopy R).obj S.X₁)

/-- In a short exact sequence `K ⟶ E ⟶ M` of curved right modules whose middle term `E` is zero in
the homotopy category, `K` is isomorphic to `M⟦-1⟧` in `AbsoluteDerivedCategory R h`. -/
noncomputable def isoShiftNegOneOfShortExact
    {S : ShortComplex
      (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))}
    (hS : S.ShortExact) (h₂ : IsZero ((dgClosedToHomotopy R).obj S.X₂)) :
    (Q R h).obj ((dgClosedToHomotopy R).obj S.X₁) ≅
      ((Q R h).obj ((dgClosedToHomotopy R).obj S.X₃))⟦(-1 : ℤ)⟧ :=
  (((shiftFunctorCompIsoId (AbsoluteDerivedCategory R h) (1 : ℤ) (-1 : ℤ) (by omega)).app
      ((Q R h).obj ((dgClosedToHomotopy R).obj S.X₁))).symm) ≪≫
    (shiftFunctor (AbsoluteDerivedCategory R h) (-1 : ℤ)).mapIso
      (isoShiftOneOfShortExact hS h₂).symm

/-! ### Graded-projective and graded-injective replacements in the absolute derived category -/

/-- **Graded-projective replacement in `AbsoluteDerivedCategory`.** Every curved right module `X`
whose underlying graded module has projective dimension `≤ n` is isomorphic in
`AbsoluteDerivedCategory R h` to a graded-projective curved module, constructed by iterating
syzygies of epimorphisms out of contractible induced curved modules `G⁺(P₀)`. -/
theorem exists_gradedProjective_Q_obj_iso (n : ℕ)
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
    [HasProjectiveDimensionLE (toGradedModuleCat X.underlying) n] :
    ∃ P : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
      gradedProjective R h P ∧ Nonempty ((Q R h).obj P ≅ (Q R h).obj X) := by
  have : EnoughProjectives
      (GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) :=
    GradedModuleCat.enoughProjectives.{u, u, u}
  induction n generalizing X with
  | zero =>
    have hProj : Projective (toGradedModuleCat X.underlying) :=
      projective_iff_hasProjectiveDimensionLT_one.mpr ‹_›
    exact ⟨X, (gradedProjective_iff X).mpr hProj, ⟨Iso.refl _⟩⟩
  | succ n ih =>
    let M : CurvedDGRightModuleCat.{u, u, u} h := X.underlying
    let U := Projective.over (toGradedModuleCat M)
    let p := inducedDesc (Projective.π (toGradedModuleCat M))
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
    have hS' : (S.map (forgetDifferential (h := h))).ShortExact :=
      hS.map_of_exact (forgetDifferential (h := h))
    let K : CurvedDGRightModuleCat.{u, u, u} h := ForgetEnrichment.to _ (kernel p)
    have : HasProjectiveDimensionLE (toGradedModuleCat (DGHomotopyCategory.of R K).underlying) n :=
      (hS'.hasProjectiveDimensionLT_X₃_iff n (projective_toGradedModuleCat_inducedObj h U)).mp ‹_›
    obtain ⟨P', hP', ⟨e'⟩⟩ := ih (DGHomotopyCategory.of R K)
    refine ⟨P'⟦(1 : ℤ)⟧, (gradedProjective R h).le_shift (1 : ℤ) P' hP', ⟨?_⟩⟩
    exact ((Q R h).commShiftIso (1 : ℤ)).app P' ≪≫
      (shiftFunctor (AbsoluteDerivedCategory R h) (1 : ℤ)).mapIso e' ≪≫
      (isoShiftOneOfShortExact hS (isZero_homotopy_inducedObj h U)).symm ≪≫
      eqToIso (congrArg (Q R h).obj (DGHomotopyCategory.of_underlying R X))

/-- **Graded-injective replacement in `AbsoluteDerivedCategory`.** Every curved right module `X`
whose underlying graded module has injective dimension `≤ n` is isomorphic in
`AbsoluteDerivedCategory R h` to a graded-injective curved module, constructed by iterating
cosyzygies of monomorphisms into contractible coinduced curved modules `G⁻(I₀)`. -/
theorem exists_gradedInjective_Q_obj_iso (n : ℕ)
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
    [HasInjectiveDimensionLE (toGradedModuleCat X.underlying) n] :
    ∃ I : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
      gradedInjective R h I ∧ Nonempty ((Q R h).obj I ≅ (Q R h).obj X) := by
  induction n generalizing X with
  | zero =>
    have hInj : Injective (toGradedModuleCat X.underlying) :=
      injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
    exact ⟨X, (gradedInjective_iff X).mpr hInj, ⟨Iso.refl _⟩⟩
  | succ n ih =>
    let M : CurvedDGRightModuleCat.{u, u, u} h := X.underlying
    let V := Injective.under (toGradedModuleCat M)
    let i := coinducedLift (Injective.ι (toGradedModuleCat M))
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
    have hS' : (S.map (forgetDifferential (h := h))).ShortExact :=
      hS.map_of_exact (forgetDifferential (h := h))
    let C : CurvedDGRightModuleCat.{u, u, u} h := ForgetEnrichment.to _ (cokernel i)
    have : HasInjectiveDimensionLE (toGradedModuleCat (DGHomotopyCategory.of R C).underlying) n :=
      (hS'.hasInjectiveDimensionLT_X₃_iff n (injective_toGradedModuleCat_coinducedObj h V)).mpr ‹_›
    obtain ⟨I', hI', ⟨e'⟩⟩ := ih (DGHomotopyCategory.of R C)
    refine ⟨I'⟦(-1 : ℤ)⟧, (gradedInjective R h).le_shift (-1 : ℤ) I' hI', ⟨?_⟩⟩
    exact ((Q R h).commShiftIso (-1 : ℤ)).app I' ≪≫
      (shiftFunctor (AbsoluteDerivedCategory R h) (-1 : ℤ)).mapIso e' ≪≫
      (isoShiftNegOneOfShortExact hS (isZero_homotopy_coinducedObj h V)).symm ≪≫
      eqToIso (congrArg (Q R h).obj (DGHomotopyCategory.of_underlying R X))

end AbsoluteDerivedCategory

/-! ### Pointwise acyclicity criteria under finite projective or injective dimension -/

/-- A contraacyclic curved right module whose underlying graded module has finite projective
dimension is absolutely acyclic. -/
theorem absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLE (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasProjectiveDimensionLE (toGradedModuleCat X.underlying) n]
    (hX : contraacyclic R h X) :
    absolutelyAcyclic R h X := by
  obtain ⟨P, hP, ⟨e⟩⟩ := AbsoluteDerivedCategory.exists_gradedProjective_Q_obj_iso n X
  have eCtr : (ContraderivedCategory.Q R h).obj P ≅ (ContraderivedCategory.Q R h).obj X :=
    ((AbsoluteDerivedCategory.toContraderivedFactors R h).app P).symm ≪≫
      (AbsoluteDerivedCategory.toContraderived R h).mapIso e ≪≫
      (AbsoluteDerivedCategory.toContraderivedFactors R h).app X
  have hZeroCtrP : IsZero ((ContraderivedCategory.Q R h).obj P) :=
    (ContraderivedCategory.isZero_Q_obj hX).of_iso eCtr
  have hIdZero : (𝟙 P : P ⟶ P) = 0 :=
    (ContraderivedCategory.map_bijective_of_gradedProjective hP P).injective <| by
      rw [Functor.map_zero]
      exact hZeroCtrP.eq_of_src _ _
  have hZeroP : IsZero P := (Limits.IsZero.iff_id_eq_zero P).mpr hIdZero
  exact (AbsoluteDerivedCategory.isZero_Q_obj_iff X).mp
    (((AbsoluteDerivedCategory.Q R h).map_isZero hZeroP).of_iso e.symm)

/-- For a curved right module whose underlying graded module has projective dimension `≤ n`,
contraacyclicity is equivalent to absolute acyclicity. -/
theorem contraacyclic_iff_absolutelyAcyclic_of_hasProjectiveDimensionLE (n : ℕ)
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
    [HasProjectiveDimensionLE (toGradedModuleCat X.underlying) n] :
    contraacyclic R h X ↔ absolutelyAcyclic R h X :=
  ⟨absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLE n,
    fun hX ↦ absolutelyAcyclic_le_contraacyclic R h X hX⟩

/-- A coacyclic curved right module whose underlying graded module has finite injective dimension
is absolutely acyclic. -/
theorem absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLE (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasInjectiveDimensionLE (toGradedModuleCat X.underlying) n]
    (hX : coacyclic R h X) :
    absolutelyAcyclic R h X := by
  obtain ⟨I, hI, ⟨e⟩⟩ := AbsoluteDerivedCategory.exists_gradedInjective_Q_obj_iso n X
  have eCo : (CoderivedCategory.Q R h).obj I ≅ (CoderivedCategory.Q R h).obj X :=
    ((AbsoluteDerivedCategory.toCoderivedFactors R h).app I).symm ≪≫
      (AbsoluteDerivedCategory.toCoderived R h).mapIso e ≪≫
      (AbsoluteDerivedCategory.toCoderivedFactors R h).app X
  have hZeroCoI : IsZero ((CoderivedCategory.Q R h).obj I) :=
    (CoderivedCategory.isZero_Q_obj hX).of_iso eCo
  have hIdZero : (𝟙 I : I ⟶ I) = 0 :=
    (CoderivedCategory.map_bijective_of_gradedInjective I hI).injective <| by
      rw [Functor.map_zero]
      exact hZeroCoI.eq_of_src _ _
  have hZeroI : IsZero I := (Limits.IsZero.iff_id_eq_zero I).mpr hIdZero
  exact (AbsoluteDerivedCategory.isZero_Q_obj_iff X).mp
    (((AbsoluteDerivedCategory.Q R h).map_isZero hZeroI).of_iso e.symm)

/-- For a curved right module whose underlying graded module has injective dimension `≤ n`,
coacyclicity is equivalent to absolute acyclicity. -/
theorem coacyclic_iff_absolutelyAcyclic_of_hasInjectiveDimensionLE (n : ℕ)
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
    [HasInjectiveDimensionLE (toGradedModuleCat X.underlying) n] :
    coacyclic R h X ↔ absolutelyAcyclic R h X :=
  ⟨absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLE n,
    fun hX ↦ absolutelyAcyclic_le_coacyclic R h X hX⟩

/-! ### Finite right graded global dimension: Positselski's coincidence theorem -/

section GlobalDimension

variable (h) {n : ℕ}
  (hn : ∀ U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
    HasProjectiveDimensionLE U n)

include hn

/-- **Positselski's Theorem 7.8(a) (coacyclic = absolutely acyclic).** When every graded right
`A`-module has projective dimension `≤ n` (and hence injective dimension `≤ n`), the coacyclic
and absolutely acyclic classes of curved right `A`-modules coincide. -/
theorem coacyclic_eq_absolutelyAcyclic :
    coacyclic R h = absolutelyAcyclic R h := by
  have hnInj : ∀ U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasInjectiveDimensionLE U n :=
    (CategoryTheory.forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE _ n).mp hn
  refine le_antisymm (fun X hX ↦ ?_) (absolutelyAcyclic_le_coacyclic R h)
  have := hnInj (toGradedModuleCat X.underlying)
  exact absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLE n hX

/-- **Positselski's Theorem 7.8(a) (contraacyclic = absolutely acyclic).** When every graded right
`A`-module has projective dimension `≤ n`, the contraacyclic and absolutely acyclic classes of
curved right `A`-modules coincide. -/
theorem contraacyclic_eq_absolutelyAcyclic :
    contraacyclic R h = absolutelyAcyclic R h := by
  refine le_antisymm (fun X hX ↦ ?_) (absolutelyAcyclic_le_contraacyclic R h)
  have := hn (toGradedModuleCat X.underlying)
  exact absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLE n hX

/-- **Positselski's Theorem 7.8(a) (coacyclic = contraacyclic).** Under finite right graded global
dimension, the coacyclic and contraacyclic classes of curved right `A`-modules coincide. -/
theorem coacyclic_eq_contraacyclic :
    coacyclic R h = contraacyclic R h :=
  (coacyclic_eq_absolutelyAcyclic h hn).trans (contraacyclic_eq_absolutelyAcyclic h hn).symm

/-- Under finite right graded global dimension, the comparison triangle functor
`AbsoluteDerivedCategory.toCoderived R h` is an equivalence of categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toCoderived :
    (AbsoluteDerivedCategory.toCoderived R h).IsEquivalence :=
  isEquivalence_of_factors (absolutelyAcyclic_le_coacyclic R h)
    (coacyclic_eq_absolutelyAcyclic h hn) (AbsoluteDerivedCategory.Q R h)
    (CoderivedCategory.Q R h) (AbsoluteDerivedCategory.toCoderived R h)
    (AbsoluteDerivedCategory.toCoderivedFactors R h)

/-- Under finite right graded global dimension, the comparison triangle functor
`AbsoluteDerivedCategory.toContraderived R h` is an equivalence of categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toContraderived :
    (AbsoluteDerivedCategory.toContraderived R h).IsEquivalence :=
  isEquivalence_of_factors (absolutelyAcyclic_le_contraacyclic R h)
    (contraacyclic_eq_absolutelyAcyclic h hn) (AbsoluteDerivedCategory.Q R h)
    (ContraderivedCategory.Q R h) (AbsoluteDerivedCategory.toContraderived R h)
    (AbsoluteDerivedCategory.toContraderivedFactors R h)

/-- **Equivalence `D_abs ≌ D_co` under finite right graded global dimension,** induced by the
comparison triangle functor `AbsoluteDerivedCategory.toCoderived R h`. -/
noncomputable def AbsoluteDerivedCategory.coderivedEquivalence :
    AbsoluteDerivedCategory R h ≌ CoderivedCategory R h :=
  have := AbsoluteDerivedCategory.isEquivalence_toCoderived h hn
  (AbsoluteDerivedCategory.toCoderived R h).asEquivalence

/-- The forward functor of `AbsoluteDerivedCategory.coderivedEquivalence` is
`AbsoluteDerivedCategory.toCoderived R h`. -/
@[simp]
theorem AbsoluteDerivedCategory.coderivedEquivalence_functor :
    (AbsoluteDerivedCategory.coderivedEquivalence h hn).functor =
      AbsoluteDerivedCategory.toCoderived R h := by
  rw [coderivedEquivalence]
  rfl

/-- **Equivalence `D_abs ≌ D_ctr` under finite right graded global dimension,** induced by the
comparison triangle functor `AbsoluteDerivedCategory.toContraderived R h`. -/
noncomputable def AbsoluteDerivedCategory.contraderivedEquivalence :
    AbsoluteDerivedCategory R h ≌ ContraderivedCategory R h :=
  have := AbsoluteDerivedCategory.isEquivalence_toContraderived h hn
  (AbsoluteDerivedCategory.toContraderived R h).asEquivalence

/-- The forward functor of `AbsoluteDerivedCategory.contraderivedEquivalence` is
`AbsoluteDerivedCategory.toContraderived R h`. -/
@[simp]
theorem AbsoluteDerivedCategory.contraderivedEquivalence_functor :
    (AbsoluteDerivedCategory.contraderivedEquivalence h hn).functor =
      AbsoluteDerivedCategory.toContraderived R h := by
  rw [contraderivedEquivalence]
  rfl

/-- The comparison functor `CoderivedCategory R h ⥤ ContraderivedCategory R h` under finite right
graded global dimension, induced by the equality `coacyclic R h = contraacyclic R h`. -/
noncomputable def CoderivedCategory.toContraderived :
    CoderivedCategory R h ⥤ ContraderivedCategory R h :=
  (ObjectProperty.trWLocalizerMorphismOfLE (coacyclic_eq_contraacyclic h hn).le).localizedFunctor
    (CoderivedCategory.Q R h) (ContraderivedCategory.Q R h)

/-- `CoderivedCategory.toContraderived` commutes coherently with all integral shifts. -/
noncomputable instance : (CoderivedCategory.toContraderived h hn).CommShift ℤ :=
  inferInstanceAs (((ObjectProperty.trWLocalizerMorphismOfLE
    (coacyclic_eq_contraacyclic h hn).le).localizedFunctor
      (CoderivedCategory.Q R h) (ContraderivedCategory.Q R h)).CommShift ℤ)

/-- `CoderivedCategory.toContraderived` preserves distinguished triangles. -/
instance : (CoderivedCategory.toContraderived h hn).IsTriangulated :=
  LocalizerMorphism.isTriangulated_localizedFunctor _
    (CoderivedCategory.Q R h) (ContraderivedCategory.Q R h)

/-- Localizing to the coderived category and applying `CoderivedCategory.toContraderived` agrees
naturally with localizing directly to the contraderived category. -/
noncomputable def CoderivedCategory.toContraderivedFactors :
    CoderivedCategory.Q R h ⋙ CoderivedCategory.toContraderived h hn ≅
      ContraderivedCategory.Q R h :=
  Localization.fac _
    ((ObjectProperty.trWLocalizerMorphismOfLE (coacyclic_eq_contraacyclic h hn).le).inverts
      (ContraderivedCategory.Q R h)) (CoderivedCategory.Q R h) ≪≫
    Functor.isoWhiskerRight (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor _)) _ ≪≫
    Functor.leftUnitor _

/-- Under finite right graded global dimension, `CoderivedCategory.toContraderived` is an
equivalence of categories. -/
theorem CoderivedCategory.isEquivalence_toContraderived :
    (CoderivedCategory.toContraderived h hn).IsEquivalence :=
  isEquivalence_of_factors (coacyclic_eq_contraacyclic h hn).le
    (coacyclic_eq_contraacyclic h hn).symm (CoderivedCategory.Q R h)
    (ContraderivedCategory.Q R h) (CoderivedCategory.toContraderived h hn)
    (CoderivedCategory.toContraderivedFactors h hn)

/-- **Equivalence `D_co ≌ D_ctr` under finite right graded global dimension,** induced by the
triangle functor `CoderivedCategory.toContraderived h hn`. -/
noncomputable def coderivedContraderivedEquivalence :
    CoderivedCategory R h ≌ ContraderivedCategory R h :=
  have := CoderivedCategory.isEquivalence_toContraderived h hn
  (CoderivedCategory.toContraderived h hn).asEquivalence

/-- The forward functor of `coderivedContraderivedEquivalence` is
`CoderivedCategory.toContraderived h hn`. -/
@[simp]
theorem coderivedContraderivedEquivalence_functor :
    (coderivedContraderivedEquivalence h hn).functor =
      CoderivedCategory.toContraderived h hn := by
  rw [coderivedContraderivedEquivalence]
  rfl

/-! ### Graded-projective and graded-injective homotopy models under finite global dimension -/

/-- Under finite right graded global dimension, the homotopy subcategory of graded-projective curved
modules maps essentially surjectively onto `AbsoluteDerivedCategory R h`. -/
theorem AbsoluteDerivedCategory.essSurj_gradedProjective :
    ((gradedProjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h).EssSurj where
  mem_essImage Z := by
    have := Localization.essSurj (AbsoluteDerivedCategory.Q R h) (absolutelyAcyclic R h).trW
    let X := (AbsoluteDerivedCategory.Q R h).objPreimage Z
    have := hn (toGradedModuleCat X.underlying)
    obtain ⟨P, hP, ⟨eP⟩⟩ := AbsoluteDerivedCategory.exists_gradedProjective_Q_obj_iso n X
    exact ⟨⟨P, hP⟩, ⟨eP ≪≫ (AbsoluteDerivedCategory.Q R h).objObjPreimageIso Z⟩⟩

/-- Under finite right graded global dimension, the homotopy subcategory of graded-injective curved
modules maps essentially surjectively onto `AbsoluteDerivedCategory R h`. -/
theorem AbsoluteDerivedCategory.essSurj_gradedInjective :
    ((gradedInjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h).EssSurj where
  mem_essImage Z := by
    have := Localization.essSurj (AbsoluteDerivedCategory.Q R h) (absolutelyAcyclic R h).trW
    have hnInj : ∀ U : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
        HasInjectiveDimensionLE U n :=
      (CategoryTheory.forall_hasProjectiveDimensionLE_iff_forall_hasInjectiveDimensionLE _ n).mp hn
    let X := (AbsoluteDerivedCategory.Q R h).objPreimage Z
    have := hnInj (toGradedModuleCat X.underlying)
    obtain ⟨I, hI, ⟨eI⟩⟩ := AbsoluteDerivedCategory.exists_gradedInjective_Q_obj_iso n X
    exact ⟨⟨I, hI⟩, ⟨eI ≪≫ (AbsoluteDerivedCategory.Q R h).objObjPreimageIso Z⟩⟩

/-- **Graded-projective model of the contraderived category.** Under finite right graded global
dimension, the composite `(gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h` is an
equivalence of categories. -/
theorem ContraderivedCategory.isEquivalence_gradedProjective :
    ((gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h).IsEquivalence := by
  have := AbsoluteDerivedCategory.essSurj_gradedProjective h hn
  have := AbsoluteDerivedCategory.isEquivalence_toContraderived h hn
  have : ((gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h).EssSurj :=
    Functor.essSurj_of_iso
      (Functor.associator (gradedProjective R h).ι (AbsoluteDerivedCategory.Q R h)
        (AbsoluteDerivedCategory.toContraderived R h) ≪≫
        Functor.isoWhiskerLeft (gradedProjective R h).ι
          (AbsoluteDerivedCategory.toContraderivedFactors R h))
  exact {}

/-- **Graded-injective model of the coderived category.** Under finite right graded global
dimension, the composite `(gradedInjective R h).ι ⋙ CoderivedCategory.Q R h` is an equivalence of
categories. -/
theorem CoderivedCategory.isEquivalence_gradedInjective :
    ((gradedInjective R h).ι ⋙ CoderivedCategory.Q R h).IsEquivalence := by
  have := AbsoluteDerivedCategory.essSurj_gradedInjective h hn
  have := AbsoluteDerivedCategory.isEquivalence_toCoderived h hn
  have : ((gradedInjective R h).ι ⋙ CoderivedCategory.Q R h).EssSurj :=
    Functor.essSurj_of_iso
      (Functor.associator (gradedInjective R h).ι (AbsoluteDerivedCategory.Q R h)
        (AbsoluteDerivedCategory.toCoderived R h) ≪≫
        Functor.isoWhiskerLeft (gradedInjective R h).ι
          (AbsoluteDerivedCategory.toCoderivedFactors R h))
  exact {}

/-- **Graded-projective model of the absolute derived category.** Under finite right graded global
dimension, the composite `(gradedProjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h` is an
equivalence of categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_gradedProjective :
    ((gradedProjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h).IsEquivalence := by
  have := ContraderivedCategory.isEquivalence_gradedProjective h hn
  have := AbsoluteDerivedCategory.isEquivalence_toContraderived h hn
  have : (((gradedProjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h) ⋙
      AbsoluteDerivedCategory.toContraderived R h).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (Functor.isoWhiskerLeft (gradedProjective R h).ι
        (AbsoluteDerivedCategory.toContraderivedFactors R h).symm ≪≫
        (Functor.associator (gradedProjective R h).ι (AbsoluteDerivedCategory.Q R h)
          (AbsoluteDerivedCategory.toContraderived R h)).symm)
  exact Functor.isEquivalence_of_comp_right
    ((gradedProjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h)
    (AbsoluteDerivedCategory.toContraderived R h)

/-- **Graded-injective model of the absolute derived category.** Under finite right graded global
dimension, the composite `(gradedInjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h` is an
equivalence of categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_gradedInjective :
    ((gradedInjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h).IsEquivalence := by
  have := CoderivedCategory.isEquivalence_gradedInjective h hn
  have := AbsoluteDerivedCategory.isEquivalence_toCoderived h hn
  have : (((gradedInjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h) ⋙
      AbsoluteDerivedCategory.toCoderived R h).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (Functor.isoWhiskerLeft (gradedInjective R h).ι
        (AbsoluteDerivedCategory.toCoderivedFactors R h).symm ≪≫
        (Functor.associator (gradedInjective R h).ι (AbsoluteDerivedCategory.Q R h)
          (AbsoluteDerivedCategory.toCoderived R h)).symm)
  exact Functor.isEquivalence_of_comp_right
    ((gradedInjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h)
    (AbsoluteDerivedCategory.toCoderived R h)

/-- Bundled equivalence between the homotopy subcategory of graded-projective curved modules and
`ContraderivedCategory R h` under finite right graded global dimension. -/
noncomputable def ContraderivedCategory.gradedProjectiveEquivalence :
    (gradedProjective R h).FullSubcategory ≌ ContraderivedCategory R h :=
  have := ContraderivedCategory.isEquivalence_gradedProjective h hn
  ((gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h).asEquivalence

/-- The forward functor of `ContraderivedCategory.gradedProjectiveEquivalence` is the subcategory
inclusion followed by `ContraderivedCategory.Q R h`. -/
@[simp]
theorem ContraderivedCategory.gradedProjectiveEquivalence_functor :
    (ContraderivedCategory.gradedProjectiveEquivalence h hn).functor =
      (gradedProjective R h).ι ⋙ ContraderivedCategory.Q R h := by
  rw [gradedProjectiveEquivalence]
  rfl

/-- Bundled equivalence between the homotopy subcategory of graded-injective curved modules and
`CoderivedCategory R h` under finite right graded global dimension. -/
noncomputable def CoderivedCategory.gradedInjectiveEquivalence :
    (gradedInjective R h).FullSubcategory ≌ CoderivedCategory R h :=
  have := CoderivedCategory.isEquivalence_gradedInjective h hn
  ((gradedInjective R h).ι ⋙ CoderivedCategory.Q R h).asEquivalence

/-- The forward functor of `CoderivedCategory.gradedInjectiveEquivalence` is the subcategory
inclusion followed by `CoderivedCategory.Q R h`. -/
@[simp]
theorem CoderivedCategory.gradedInjectiveEquivalence_functor :
    (CoderivedCategory.gradedInjectiveEquivalence h hn).functor =
      (gradedInjective R h).ι ⋙ CoderivedCategory.Q R h := by
  rw [gradedInjectiveEquivalence]
  rfl

/-- Bundled equivalence between the homotopy subcategory of graded-projective curved modules and
`AbsoluteDerivedCategory R h` under finite right graded global dimension. -/
noncomputable def AbsoluteDerivedCategory.gradedProjectiveEquivalence :
    (gradedProjective R h).FullSubcategory ≌ AbsoluteDerivedCategory R h :=
  have := AbsoluteDerivedCategory.isEquivalence_gradedProjective h hn
  ((gradedProjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h).asEquivalence

/-- The forward functor of `AbsoluteDerivedCategory.gradedProjectiveEquivalence` is the subcategory
inclusion followed by `AbsoluteDerivedCategory.Q R h`. -/
@[simp]
theorem AbsoluteDerivedCategory.gradedProjectiveEquivalence_functor :
    (AbsoluteDerivedCategory.gradedProjectiveEquivalence h hn).functor =
      (gradedProjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h := by
  rw [gradedProjectiveEquivalence]
  rfl

/-- Bundled equivalence between the homotopy subcategory of graded-injective curved modules and
`AbsoluteDerivedCategory R h` under finite right graded global dimension. -/
noncomputable def AbsoluteDerivedCategory.gradedInjectiveEquivalence :
    (gradedInjective R h).FullSubcategory ≌ AbsoluteDerivedCategory R h :=
  have := AbsoluteDerivedCategory.isEquivalence_gradedInjective h hn
  ((gradedInjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h).asEquivalence

/-- The forward functor of `AbsoluteDerivedCategory.gradedInjectiveEquivalence` is the subcategory
inclusion followed by `AbsoluteDerivedCategory.Q R h`. -/
@[simp]
theorem AbsoluteDerivedCategory.gradedInjectiveEquivalence_functor :
    (AbsoluteDerivedCategory.gradedInjectiveEquivalence h hn).functor =
      (gradedInjective R h).ι ⋙ AbsoluteDerivedCategory.Q R h := by
  rw [gradedInjectiveEquivalence]
  rfl

end GlobalDimension

end TauCeti.CurvedDGRightModuleCat
