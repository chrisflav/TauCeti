/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Morphism
public import TauCeti.RingTheory.Huber.Padic.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Examples of the formal-scheme section topology and global morphism correspondence

Concrete checks exercising the intrinsic section topology on affine formal opens
(`TauCeti.FormalScheme.IsAffineOpen.sectionsTopology`), gluing of morphisms along open covers
(`TauCeti.FormalScheme.glueMorphisms`), the global morphism correspondence
(`TauCeti.FormalScheme.homSpfEquiv`), the residue-field continuity criterion
(`TauCeti.FormalScheme.continuousOnAffines_iff_Γevaluation_eq_zero`), and automatic continuity of
section maps (`TauCeti.FormalScheme.sectionMap_continuous`):

1. **Ordinary schemes (`sections_discrete`, `homSpfDiscreteEquiv`)**: affine opens of a scheme `X`
   become affine formal opens of `X.toFormalScheme` with discrete intrinsic section topology, and
   morphisms into `ofSpf R` for discrete `R` correspond to *all* ring homomorphisms `R →+* Γ(X, O)`.
2. **Empty affine formal opens (`sections_empty`, `sectionsHom_empty`)**: sections over an empty
   affine formal open form a subsingleton ring with discrete topology, and morphisms from an empty
   formal scheme into `ofSpf A` correspond to the unique zero homomorphism.
3. **Identity, evaluation, and gluing (`sectionsHom_identity`, `sectionsHom_evaluation`,
   `glueMorphisms_pair`)**: the identity on `ofSpf A` induces `(Spf.globalSectionsIso _).inv`,
   evaluation at `1` sends `Polynomial.X` to `1` on `Spec R`, and compatible local morphisms glue.
4. **`p`-adic integers versus `Spec ℚ_[p]` (`existsUnique_point_ofSpf_padicInt`,
   `sections_padic_nondiscrete`, `not_continuousOnAffines_padic_to_spec`,
   `not_exists_sectionsHom_padic_to_spec`)**: `ofSpf ℤ_[p]` has a single point while its intrinsic
   global-section topology is non-discrete; the canonical inclusion `ℤ_[p] →+* Γ(Spec ℚ_[p], O)`
   fails `ContinuousOnAffines` (because `Γ(Spec ℚ_[p], O)` has the discrete section topology) and
   cannot be induced by any morphism `(Spec ℚ_[p]).toFormalScheme ⟶ ofSpf ℤ_[p]`.
-/

public section

open CategoryTheory TopologicalSpace Topology Opposite AlgebraicGeometry
open TauCeti TauCeti.FormalScheme

universe u

noncomputable section

namespace TauCeti.Examples.FormalScheme.Morphism

/-! ### 1. Affine formal opens of ordinary schemes -/

/-- Every affine open of an ordinary scheme `X` is an affine formal open of `X.toFormalScheme` whose
intrinsic section topology is discrete. -/
theorem sections_discrete (X : Scheme.{u}) {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    @DiscreteTopology (X.toFormalScheme.presheaf.obj (op U)) hU.toFormalScheme.sectionsTopology :=
  X.isAffineOpen_discreteTopology_sectionsTopology hU.toFormalScheme

/-- When `R` is discrete, every ring homomorphism `R →+* Γ(X, O_X)` corresponds to a unique
morphism `X ⟶ ofSpf R`. -/
def homSpfDiscreteEquiv (X : FormalScheme.{u}) (R : Type u) [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] :
    (X ⟶ ofSpf R) ≃ (R →+* X.presheaf.obj (op ⊤)) :=
  (homSpfEquiv X R).trans
    { toFun := Subtype.val
      invFun φ := ⟨φ, continuousOnAffines_of_discreteTopology φ⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-! ### 2. Empty formal opens and empty formal schemes -/

/-- Over an empty affine formal open `U`, `Γ(U, O_X)` is a subsingleton ring and its intrinsic
section topology is discrete. -/
theorem sections_empty {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) [IsEmpty U] :
    Subsingleton (X.presheaf.obj (op U)) ∧
      @DiscreteTopology (X.presheaf.obj (op U)) hU.sectionsTopology := by
  let : TopologicalSpace (X.presheaf.obj (op U)) := hU.sectionsTopology
  have : T2Space (X.presheaf.obj (op U)) := hU.t2Space
  have hnilp : Filter.Tendsto (fun n : ℕ ↦ (1 : X.presheaf.obj (op U)) ^ n) Filter.atTop (𝓝 0) :=
    (hU.isTopologicallyNilpotent_iff_evaluation_eq_zero 1).mpr fun x ↦ IsEmpty.elim inferInstance x
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ (1 : X.presheaf.obj (op U))) Filter.atTop (𝓝 1) :=
    tendsto_const_nhds
  have h10 : (1 : X.presheaf.obj (op U)) = 0 :=
    tendsto_nhds_unique hconst (by simpa only [one_pow] using hnilp)
  have hsub : Subsingleton (X.presheaf.obj (op U)) := subsingleton_of_zero_eq_one h10.symm
  exact ⟨hsub, inferInstance⟩

/-- From an empty formal scheme `X`, there is a unique morphism `X ⟶ ofSpf A`, whose global-section
homomorphism maps every element to `0` and satisfies `ContinuousOnAffines`. -/
theorem sectionsHom_empty (X : FormalScheme.{u}) [hx : IsEmpty X] (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] :
    ∃! f : X ⟶ ofSpf A, ∀ a : A, sectionsHom f a = 0 := by
  have hsub : Subsingleton (X.presheaf.obj (op ⊤)) :=
    ⟨fun s₁ s₂ ↦ X.toLocallyRingedSpace.sheaf.eq_of_locally_eq'
      (fun i : PEmpty.{u + 1} ↦ PEmpty.elim i) ⊤ (fun i ↦ PEmpty.elim i)
      (fun x _ ↦ hx.elim x) s₁ s₂ (fun i ↦ PEmpty.elim i)⟩
  let φ : A →+* X.presheaf.obj (op ⊤) :=
    { toFun _ := 0
      map_one' := Subsingleton.elim _ _
      map_mul' _ _ := Subsingleton.elim _ _
      map_zero' := rfl
      map_add' _ _ := Subsingleton.elim _ _ }
  have hφ : ContinuousOnAffines X A φ :=
    (continuousOnAffines_iff_Γevaluation_eq_zero (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 φ).mpr
      fun _ _ x ↦ hx.elim x
  refine ⟨homSpf φ hφ, fun a ↦ by simp [φ], fun g _ ↦ sectionsHom_injective ?_⟩
  ext a
  exact Subsingleton.elim _ _

/-! ### 3. Identity, polynomial evaluation, and two-open gluing -/

/-- The identity morphism on `ofSpf A` induces `(Spf.globalSectionsIso _).inv` on global sections
and satisfies `ContinuousOnAffines`. -/
theorem sectionsHom_identity (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] :
    ContinuousOnAffines (ofSpf A) A (sectionsHom (𝟙 (ofSpf A))) ∧
      ∀ a : A,
        (@Spf.globalSectionsIso A _ _ _ (IsAdicRing.ideal A) (IsAdicRing.ideal_spec A).2.2
          (IsAdicRing.ideal_spec A).2.1).hom (sectionsHom (𝟙 (ofSpf A)) a) = a := by
  have := (IsAdicRing.ideal_spec A).2.2
  refine ⟨continuousOnAffines_sectionsHom (𝟙 (ofSpf A)), fun a ↦ ?_⟩
  rw [sectionsHom_id]
  exact ConcreteCategory.congr_hom
    (Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv_hom_id a

section Evaluation

/-- Discrete topology on `R[X]` for the polynomial evaluation check. -/
local instance polyDiscreteTopology (R : Type u) [CommRing R] : TopologicalSpace (Polynomial R) := ⊥
/-- Discreteness of `R[X]` for the polynomial evaluation check. -/
local instance instDiscretePoly (R : Type u) [CommRing R] : DiscreteTopology (Polynomial R) := ⟨rfl⟩

/-- Gluing evaluation at `1` via `homSpf` gives a morphism `(Spec R).toFormalScheme ⟶ ofSpf R[X]`
whose induced global-section map sends `Polynomial.X` to the unit section `1`. -/
theorem sectionsHom_evaluation (R : Type u) [CommRing R] :
    ∃ f : (Spec (CommRingCat.of R)).toFormalScheme ⟶ ofSpf (Polynomial R),
      sectionsHom f Polynomial.X = 1 := by
  let X := (Spec (CommRingCat.of R)).toFormalScheme
  let φ : Polynomial R →+* X.presheaf.obj (op ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).comp (Polynomial.evalRingHom 1)
  refine ⟨homSpf φ (continuousOnAffines_of_discreteTopology φ), ?_⟩
  rw [sectionsHom_homSpf]
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (Polynomial.eval 1 Polynomial.X) = 1
  simp

end Evaluation

/-- Gluing two compatible morphisms on a two-open cover `U ⊔ V = ⊤` recovers each piece on `U` and
`V`. -/
theorem glueMorphisms_pair {X Y : FormalScheme.{u}} {U V : Opens X} (hUV : U ⊔ V = ⊤)
    (fU : X.restrict U ⟶ Y) (fV : X.restrict V ⟶ Y)
    (hcompat : X.restrictHomOfLE (inf_le_left : U ⊓ V ≤ U) ≫ fU =
      X.restrictHomOfLE inf_le_right ≫ fV) :
    ∃! g : X ⟶ Y, X.ofRestrict U ≫ g = fU ∧ X.ofRestrict V ≫ g = fV := by
  let cov : Bool → Opens X := fun b ↦ cond b U V
  have hcov : (⨆ b, cov b) = ⊤ := by
    rw [eq_top_iff, ← hUV, sup_le_iff]
    exact ⟨le_iSup cov true, le_iSup cov false⟩
  let f : ∀ b, X.restrict (cov b) ⟶ Y := fun b ↦
    match b with
    | true => fU
    | false => fV
  have hf : ∀ i j, X.restrictHomOfLE (inf_le_left : cov i ⊓ cov j ≤ cov i) ≫ f i =
      X.restrictHomOfLE inf_le_right ≫ f j := by
    intro i j
    cases i <;> cases j
    · exact congrArg (fun h : cov false ⊓ cov false ≤ cov false ↦ X.restrictHomOfLE h ≫ f false)
        (Subsingleton.elim _ _)
    · dsimp only [cov, f, Bool.cond_false, Bool.cond_true]
      have hl : X.restrictHomOfLE (inf_le_left : V ⊓ U ≤ V) =
          X.restrictHomOfLE (inf_comm (a := V) (b := U)).le ≫
            X.restrictHomOfLE (inf_le_right : U ⊓ V ≤ V) :=
        (X.restrictHomOfLE_comp _ _).symm
      have hr : X.restrictHomOfLE (inf_le_right : V ⊓ U ≤ U) =
          X.restrictHomOfLE (inf_comm (a := V) (b := U)).le ≫
            X.restrictHomOfLE (inf_le_left : U ⊓ V ≤ U) :=
        (X.restrictHomOfLE_comp _ _).symm
      rw [hl, hr, Category.assoc, Category.assoc, hcompat]
    · exact hcompat
    · exact congrArg (fun h : cov true ⊓ cov true ≤ cov true ↦ X.restrictHomOfLE h ≫ f true)
        (Subsingleton.elim _ _)
  refine ⟨glueMorphisms cov hcov f hf,
    ⟨ofRestrict_glueMorphisms cov hcov f hf true, ofRestrict_glueMorphisms cov hcov f hf false⟩,
    fun g ⟨hgU, hgV⟩ ↦ hom_ext_of_ofRestrict cov hcov fun b ↦ ?_⟩
  cases b
  · exact hgV.trans (ofRestrict_glueMorphisms cov hcov f hf false).symm
  · exact hgU.trans (ofRestrict_glueMorphisms cov hcov f hf true).symm

/-! ### 4. `p`-adic integers versus `Spec ℚ_[p]` -/

section Padic

/-- The `(p)`-adic ring structure of finite ideal type on `ℤ_[p]`. -/
local instance padicIntIsAdicRing (p : ℕ) [Fact p.Prime] : IsAdicRing ℤ_[p] :=
  ⟨IsLocalRing.maximalIdeal ℤ_[p],
    by rw [PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _,
    Huber.PadicInt.isAdic_maximalIdeal, inferInstance⟩

/-- `ofSpf ℤ_[p]` has a unique underlying point, corresponding to the maximal ideal `(p)`. -/
theorem existsUnique_point_ofSpf_padicInt (p : ℕ) [Fact p.Prime] :
    ∃! _ : ofSpf ℤ_[p], True := by
  refine ⟨⟨⟨IsLocalRing.maximalIdeal ℤ_[p], (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).isPrime⟩,
    Spf.mem_carrier.mpr
      (by simpa only [pow_one] using IsLocalRing.isOpen_maximalIdeal_pow ℤ_[p] 1)⟩,
    trivial, fun x _ ↦ Subtype.ext (PrimeSpectrum.ext ?_)⟩
  have hxopen : IsOpen (x.1.asIdeal : Set ℤ_[p]) := Spf.mem_carrier.mp x.2
  obtain ⟨n, hn⟩ := (isAdic_iff.mp (Huber.PadicInt.isAdic_maximalIdeal (p := p))).2
    (x.1.asIdeal : Set ℤ_[p]) (hxopen.mem_nhds x.1.asIdeal.zero_mem)
  have hle : IsLocalRing.maximalIdeal ℤ_[p] ≤ x.1.asIdeal :=
    x.1.isPrime.le_of_pow_le (show IsLocalRing.maximalIdeal ℤ_[p] ^ n ≤ x.1.asIdeal from hn)
  exact ((IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).eq_of_le x.1.isPrime.ne_top hle).symm

/-- Although `ofSpf ℤ_[p]` has a single underlying point, the intrinsic section topology
`(isAffineOpen_top_ofSpf ℤ_[p]).sectionsTopology` on its global sections is not discrete. -/
theorem sections_padic_nondiscrete (p : ℕ) [Fact p.Prime] :
    ¬ @DiscreteTopology ((ofSpf ℤ_[p]).presheaf.obj (op ⊤))
      (isAffineOpen_top_ofSpf ℤ_[p]).sectionsTopology := by
  rw [sectionsTopology_top_ofSpf ℤ_[p]]
  have := (IsAdicRing.ideal_spec ℤ_[p]).2.2
  let : TopologicalSpace
      ((Spf.structureSheaf (IsAdicRing.ideal_spec ℤ_[p]).2.1).obj.obj (op ⊤)) :=
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec ℤ_[p]).2.1 ⊤
  intro hdisc
  have hdiscZ : DiscreteTopology ℤ_[p] :=
    (Spf.isHomeomorph_globalSectionsIso
      (IsAdicRing.ideal_spec ℤ_[p]).2.1).homeomorph.discreteTopology_iff.mp hdisc
  have hnil : Filter.Tendsto (fun n : ℕ ↦ (p : ℤ_[p]) ^ n) Filter.atTop (𝓝 0) :=
    (Huber.PadicInt.isTopologicallyNilpotent_iff_dvd (c := (p : ℤ_[p]))).mpr dvd_rfl
  rw [nhds_discrete, Filter.tendsto_pure] at hnil
  obtain ⟨n, hn⟩ := hnil.exists
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hn

/-- The canonical inclusion `ℤ_[p] →+* Γ(Spec ℚ_[p], O)` fails `ContinuousOnAffines`, since the
intrinsic section topology on `Spec ℚ_[p]` is discrete while `(p : ℤ_[p])` is topologically
nilpotent and non-nilpotent in `ℚ_[p]`. -/
theorem not_continuousOnAffines_padic_to_spec (p : ℕ) [Fact p.Prime] :
    ¬ ContinuousOnAffines (Spec (CommRingCat.of ℚ_[p])).toFormalScheme ℤ_[p]
      (((Scheme.ΓSpecIso (CommRingCat.of ℚ_[p])).inv.hom).comp (algebraMap ℤ_[p] ℚ_[p])) := by
  let S := Spec (CommRingCat.of ℚ_[p])
  let X := S.toFormalScheme
  let φ : ℤ_[p] →+* X.presheaf.obj (op ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℚ_[p])).inv.hom).comp (algebraMap ℤ_[p] ℚ_[p])
  intro hφ
  have htop : X.IsAffineOpen (⊤ : Opens X) :=
    (AlgebraicGeometry.isAffineOpen_top S).toFormalScheme
  let : TopologicalSpace (X.presheaf.obj (op (⊤ : Opens X))) := htop.sectionsTopology
  have : DiscreteTopology (X.presheaf.obj (op (⊤ : Opens X))) :=
    sections_discrete S (AlgebraicGeometry.isAffineOpen_top S)
  let ψ := (X.presheaf.map (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op).hom.comp φ
  have hcont : Continuous ψ := hφ htop
  have hnil : IsTopologicallyNilpotent (p : ℤ_[p]) :=
    (Huber.PadicInt.isTopologicallyNilpotent_iff_dvd (c := (p : ℤ_[p]))).mpr dvd_rfl
  have hψnil : Filter.Tendsto (fun n : ℕ ↦ ψ (p : ℤ_[p]) ^ n) Filter.atTop (𝓝 0) :=
    hnil.map hcont
  rw [nhds_discrete, Filter.tendsto_pure] at hψnil
  obtain ⟨n, hn⟩ := hψnil.exists
  have hres : X.presheaf.map (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op = 𝟙 _ :=
    (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_id _)
  have hφn : φ ((p : ℤ_[p]) ^ n) = 0 :=
    (ConcreteCategory.congr_hom hres (φ ((p : ℤ_[p]) ^ n))).symm.trans
      ((map_pow ψ (p : ℤ_[p]) n).trans hn)
  have hQn : (p : ℚ_[p]) ^ n = 0 := by
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of ℚ_[p])).hom.hom (φ ((p : ℤ_[p]) ^ n)) = 0 :=
      (congrArg (Scheme.ΓSpecIso (CommRingCat.of ℚ_[p])).hom.hom hφn).trans (map_zero _)
    have h2 := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (CommRingCat.of ℚ_[p])).inv_hom_id
      (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ n))
    have h3 : algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ n) = (p : ℚ_[p]) ^ n := by simp
    exact h3.symm.trans (h2.symm.trans h1)
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hQn

/-- No morphism of formal schemes `(Spec ℚ_[p]).toFormalScheme ⟶ ofSpf ℤ_[p]` induces the canonical
inclusion `ℤ_[p] →+* Γ(Spec ℚ_[p], O)` on global sections. -/
theorem not_exists_sectionsHom_padic_to_spec (p : ℕ) [Fact p.Prime] :
    ¬ ∃ f : (Spec (CommRingCat.of ℚ_[p])).toFormalScheme ⟶ ofSpf ℤ_[p],
      sectionsHom f =
        ((Scheme.ΓSpecIso (CommRingCat.of ℚ_[p])).inv.hom).comp (algebraMap ℤ_[p] ℚ_[p]) := by
  rintro ⟨f, hf⟩
  exact not_continuousOnAffines_padic_to_spec p (hf ▸ continuousOnAffines_sectionsHom f)

end Padic

end TauCeti.Examples.FormalScheme.Morphism
