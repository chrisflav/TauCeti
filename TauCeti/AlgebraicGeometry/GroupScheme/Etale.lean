/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.RationalPoint.Image
import TauCeti.CategoryTheory.Monoidal.Grp.KernelPair
import TauCeti.CategoryTheory.Monoidal.Grp.Translation
import TauCeti.Topology.Sets.Opens

/-!
# Étale and unramified homomorphisms of group schemes

A faithfully flat, quasi-compact homomorphism of group schemes is étale if and only if
its scheme-theoretic kernel is étale over the base. An étale homomorphism always has an étale
kernel, without the fpqc hypotheses. This criterion applies over arbitrary schemes and does
not require commutativity, smoothness, or finiteness of either group.

Over a field `K`, any Zariski-local-at-source, base-change-stable, multiplicative morphism
property `P` satisfying fpqc descent holds for a homomorphism `φ : G ⟶ H` from a group scheme
`G` locally of finite type over `Spec K` if and only if it holds on an open neighbourhood of the
identity point of `G` (`TauCeti.AlgebraicGeometry.morphismProperty_iff_exists_unit`). Indeed, after
base change to an algebraic closure `L` of `K`, the set of points where `P` fails locally is closed;
if nonempty, it contains an `L`-rational point, which left translation moves to the identity.
Specializing to `@Etale` and `@Unramified` shows that `φ` is étale (respectively formally
unramified) on all of `G` as soon as it is étale near the identity (respectively formally
unramified on the stalk at the identity).

## Main results

* `CategoryTheory.Grp.etale_kernel_hom`, `CategoryTheory.Grp.etale_iff_etale_kernel`:
  kernel criterion for étale group-scheme homomorphisms over an arbitrary base scheme.
* `TauCeti.AlgebraicGeometry.morphismProperty_iff_exists_unit`: identity-neighbourhood criterion
  for homomorphisms of group schemes locally of finite type over a field.
* `TauCeti.AlgebraicGeometry.etale_iff_exists_etale_unit`: `φ.left` is étale iff it is étale on an
  open neighbourhood of the identity point.
* `TauCeti.AlgebraicGeometry.formallyUnramified_iff_stalkMap_unit`: `φ.left` is formally unramified
  iff its stalk map at the identity point is formally unramified.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
* [The Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.28.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

universe u

namespace CategoryTheory.Grp

variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- The scheme-theoretic kernel of an étale homomorphism is étale over the base. -/
theorem etale_kernel_hom (f : G ⟶ H) (hf : Etale f.hom.hom.left) :
    Etale (kernel f).X.hom := by
  simpa only [Over.forget_map, Over.toUnit_left] using
    MorphismProperty.of_isPullback (P := @Etale)
      ((TauCeti.GroupScheme.isPullback_kernel_hom f).map (Over.forget S)) hf

/-- An fpqc homomorphism of group schemes is étale exactly when its kernel is étale over
the base. The kernel is scheme-theoretic, so infinitesimal points are included. -/
theorem etale_iff_etale_kernel (f : G ⟶ H) [Surjective f.hom.hom.left]
    [Flat f.hom.hom.left] [QuasiCompact f.hom.hom.left] :
    Etale f.hom.hom.left ↔ Etale (kernel f).X.hom := by
  have hk := TauCeti.GroupScheme.isPullback_kernel_hom f
  constructor
  · exact etale_kernel_hom f
  · intro hK
    let := hK
    have h := (TauCeti.isPullback_mul_of_isPullback_one f.hom.hom
      (kernel.ι f).hom.hom hk).map (Over.forget S)
    have hs : Etale (snd (kernel f).X G.X).left := by
      rw [Over.snd_left]
      infer_instance
    have hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
        f.hom.hom.left := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    exact MorphismProperty.of_isPullback_of_descendsAlong h.flip hf hs

end CategoryTheory.Grp

namespace TauCeti.AlgebraicGeometry

section IdentityCriterion

/-- Pulling back a morphism in `Over S` along `t : T ⟶ S` yields a cartesian square on underlying
schemes. -/
private lemma isPullback_over_pullback_map_left {S T : Scheme.{u}} (t : T ⟶ S) {X Y : Over S}
    (φ : X ⟶ Y) :
    IsPullback ((Over.pullback t).map φ).left (pullback.fst X.hom t)
      (pullback.fst Y.hom t) φ.left :=
  .of_right (t := .flip <| .of_hasPullback Y.hom t)
    (by simpa [Over.pullback_map_left, Over.w φ] using (.flip <| .of_hasPullback X.hom t))
    (by simp [Over.pullback_map_left])

/-- Over an algebraically closed field, if a base-change-stable Zariski-local property `P` holds on
an open `U'` containing the identity point of `G'`, then `P` holds on all of `G'`. -/
private lemma morphismProperty_of_unit_algClosed (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange]
    {L : Type u} [Field L] [IsAlgClosed L] {G' H' : Over (Spec (.of L))} [GrpObj G'] [GrpObj H']
    [LocallyOfFiniteType G'.hom] (φ' : G' ⟶ H') [IsMonHom φ'] (U' : G'.left.Opens)
    (hU₀ : η[G'].left (IsLocalRing.closedPoint L) ∈ U') (hPU' : P (U'.ι ≫ φ'.left)) :
    P φ'.left := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  let Z : Set G'.left := {z | ¬ ∃ V : G'.left.Opens, z ∈ V ∧ P (V.ι ≫ φ'.left)}
  have hZclosed : IsClosed Z := TopologicalSpace.Opens.isClosed_setOf_not_exists _
  have hZempty : ¬ Z.Nonempty := by
    intro hne
    obtain ⟨p, hp, hpZ⟩ := hZclosed.isLocallyClosed.exists_rationalPoint_mem G'.hom hne
    let x : 𝟙_ (Over (Spec (.of L))) ⟶ G' := Over.homMk p hp
    let τ := leftTranslation x⁻¹
    let σ := leftTranslation (x⁻¹ ≫ φ')
    have hτσ : τ.hom.left ≫ φ'.left = φ'.left ≫ σ.hom.left :=
      congrArg Over.Hom.left (leftTranslation_hom_comp φ' x⁻¹)
    refine hpZ ⟨τ.hom.left ⁻¹ᵁ U', ?_, ?_⟩
    · have hxτ' : x ≫ τ.hom = η[G'] := by
        rw [comp_leftTranslation_hom, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp,
          inv_mul_cancel, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
      have hxτ : p ≫ τ.hom.left = η[G'].left := congrArg Over.Hom.left hxτ'
      have hpt : τ.hom.left (p (IsLocalRing.closedPoint L)) =
          η[G'].left (IsLocalRing.closedPoint L) :=
        (p.comp_apply τ.hom.left _).symm.trans congr($hxτ (IsLocalRing.closedPoint L))
      rw [Scheme.Hom.mem_preimage, hpt]
      exact hU₀
    · have hcomm : ((τ.hom.left ⁻¹ᵁ U').ι ≫ φ'.left) ≫ σ.hom.left =
          (τ.hom.left ∣_ U') ≫ U'.ι ≫ φ'.left := by
        rw [Category.assoc, ← hτσ, morphismRestrict_ι_assoc]
      have : IsIso σ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map σ.hom))
      have : IsIso (τ.hom.left ∣_ U') := by
        have : IsIso τ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map τ.hom))
        infer_instance
      rw [← P.cancel_right_of_respectsIso _ σ.hom.left, hcomm, P.cancel_left_of_respectsIso]
      exact hPU'
  have hall (z : G'.left) : ∃ V : G'.left.Opens, z ∈ V ∧ P (V.ι ≫ φ'.left) :=
    not_not.mp fun hz ↦ hZempty ⟨z, hz⟩
  choose V hzV hPV using hall
  exact IsZariskiLocalAtSource.of_iSup_eq_top V
    (eq_top_iff.mpr fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hzV z⟩) hPV

variable {K : Type u} [Field K] {G H : Over (Spec (.of K))} [GrpObj G] [GrpObj H]
  [LocallyOfFiniteType G.hom]

/-- **Identity-neighbourhood criterion for group-scheme homomorphisms over a field.** Let `P` be a
Zariski-local-at-source, base-change-stable, multiplicative morphism property satisfying fpqc
descent, and let `φ : G ⟶ H` be a homomorphism of group schemes over `Spec K` with `G` locally of
finite type over `Spec K`. Then `P` holds for `φ.left` if and only if `P` holds on an open
neighbourhood of the identity point `η[G]`. -/
theorem morphismProperty_iff_exists_unit (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] (φ : G ⟶ H) [IsMonHom φ] :
    P φ.left ↔
      ∃ U : G.left.Opens, η[G].left (IsLocalRing.closedPoint K) ∈ U ∧ P (U.ι ≫ φ.left) := by
  refine ⟨fun hφ ↦ ⟨⊤, trivial, P.comp_mem _ _ (IsZariskiLocalAtSource.of_isOpenImmersion _) hφ⟩,
    fun ⟨U, hU₀, hPU⟩ ↦ ?_⟩
  let L := AlgebraicClosure K
  let t : Spec (.of L) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let G' := (Over.pullback t).mapGrp.obj (Grp.mk G)
  let H' := (Over.pullback t).mapGrp.obj (Grp.mk H)
  let φ' : G'.X ⟶ H'.X := ((Over.pullback t).mapGrp.map (Grp.ofHom φ)).hom.hom
  have hpb : IsPullback φ'.left (pullback.fst G.hom t) (pullback.fst H.hom t) φ.left :=
    isPullback_over_pullback_map_left t φ
  let U' : G'.X.left.Opens := pullback.fst G.hom t ⁻¹ᵁ U
  have hU'₀ : η[G'.X].left (IsLocalRing.closedPoint L) ∈ U' := by
    have hone : η[G'.X].left ≫ pullback.fst G.hom t =
        (𝟙_ (Over (Spec (.of L)))).hom ≫ t ≫ η[G].left := by
      simpa only [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp] using
        GroupScheme.pullback_mapGrp_one_left_fst t (Grp.mk G) (𝟙_ (Over (Spec (.of L))))
    let x₀L : (𝟙_ (Over (Spec (.of L)))).left := IsLocalRing.closedPoint L
    have hpt : pullback.fst G.hom t (η[G'.X].left x₀L) =
        η[G].left (IsLocalRing.closedPoint K) :=
      (η[G'.X].left.comp_apply (pullback.fst G.hom t) x₀L).symm.trans <|
        congr($hone x₀L).trans <|
          (Scheme.Hom.comp_apply (𝟙_ (Over (Spec (.of L)))).hom (t ≫ η[G].left) x₀L).trans <|
            (Scheme.Hom.comp_apply t η[G].left _).trans <|
              congrArg η[G].left (@Subsingleton.elim (PrimeSpectrum K) inferInstance _ _)
    exact (pullback.fst G.hom t).mem_preimage.mpr (hpt.symm ▸ hU₀)
  have hPU' : P (U'.ι ≫ φ'.left) :=
    P.of_isPullback ((isPullback_morphismRestrict (pullback.fst G.hom t) U).paste_vert hpb.flip) hPU
  have : LocallyOfFiniteType G'.X.hom := by
    -- `(Over.pullback t).mapGrp` sends `G` to an `Over`-object with structure map `pullback.snd`
    change LocallyOfFiniteType (pullback.snd G.hom t)
    infer_instance
  have hPφ' : P φ'.left := morphismProperty_of_unit_algClosed P φ' U' hU'₀ hPU'
  have ht : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) t :=
    ⟨⟨⟨fun x ↦ ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩,
      Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)⟩, inferInstance⟩
  have hpbH := (IsPullback.of_hasPullback H.hom t).flip
  have hfst : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (pullback.fst H.hom t) :=
    ⟨⟨MorphismProperty.of_isPullback hpbH ht.1.1, MorphismProperty.of_isPullback hpbH ht.1.2⟩,
      MorphismProperty.of_isPullback hpbH ht.2⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong hpb hfst hPφ'

/-- **Étaleness of a group-scheme homomorphism over a field is tested at the identity.** For group
schemes `G` and `H` over `Spec K` with `G` locally of finite type, a homomorphism `φ : G ⟶ H` is
étale if and only if it is étale on an open neighbourhood of the identity point. -/
theorem etale_iff_exists_etale_unit (φ : G ⟶ H) [IsMonHom φ] :
    Etale φ.left ↔
      ∃ U : G.left.Opens, η[G].left (IsLocalRing.closedPoint K) ∈ U ∧ Etale (U.ι ≫ φ.left) := by
  have : IsZariskiLocalAtSource @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
  exact morphismProperty_iff_exists_unit @Etale φ

/-- **Unramifiedness of a group-scheme homomorphism over a field is tested at the identity.** For
group schemes `G` and `H` over `Spec K` with `G` locally of finite type, a homomorphism `φ : G ⟶ H`
is unramified if and only if its stalk map at the identity point is formally unramified. -/
theorem unramified_iff_stalkMap_unit (φ : G ⟶ H) [IsMonHom φ] :
    Unramified φ.left ↔
      (φ.left.stalkMap (η[G].left (IsLocalRing.closedPoint K))).hom.FormallyUnramified := by
  have : LocallyOfFiniteType (φ.left ≫ H.hom) := by
    rw [Over.w φ]
    infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp φ.left H.hom
  have : IsZariskiLocalAtSource @Unramified.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
  rw [morphismProperty_iff_exists_unit @Unramified φ, ← φ.left.unramifiedAt_iff_stalkMap]
  refine exists_congr fun U ↦ and_congr_right fun _ ↦ ?_
  rw [unramified_iff]

/-- **Formal unramifiedness of a group-scheme homomorphism over a field is tested at the identity.**
For group schemes `G` and `H` over `Spec K` with `G` locally of finite type, a homomorphism
`φ : G ⟶ H` is formally unramified if and only if its stalk map at the identity point is formally
unramified. -/
theorem formallyUnramified_iff_stalkMap_unit (φ : G ⟶ H) [IsMonHom φ] :
    FormallyUnramified φ.left ↔
      (φ.left.stalkMap (η[G].left (IsLocalRing.closedPoint K))).hom.FormallyUnramified := by
  have : LocallyOfFiniteType (φ.left ≫ H.hom) := by
    rw [Over.w φ]
    infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp φ.left H.hom
  rw [← unramified_iff_stalkMap_unit φ, unramified_iff, and_iff_right ‹_›]

end IdentityCriterion

end TauCeti.AlgebraicGeometry
