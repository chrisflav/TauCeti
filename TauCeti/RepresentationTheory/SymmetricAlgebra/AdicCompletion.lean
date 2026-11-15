/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Translation
public import TauCeti.RepresentationTheory.Dual
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic
public import TauCeti.RingTheory.Invariant.AdicCompletion
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RepresentationTheory.SymmetricAlgebra.FiniteType
import TauCeti.RepresentationTheory.SymmetricAlgebra.OrbitSeparation

/-!
# Completed-local quotient comparison for symmetric-algebra invariants

Let a finite group `G` act linearly on a finite-dimensional vector space `V` over a field `K`,
and so on the algebra of polynomial functions `Sym(V*)` via `ρ.dual`. Evaluation at a vector
`v : V` is the `K`-algebra homomorphism
`SymmetricAlgebra.lift (Module.Dual.eval K V v) : Sym(V*) →ₐ[K] K`, whose kernel `I_v` is the
maximal ideal of polynomial functions vanishing at `v`.

Under the induced `G`-action on ideals of `Sym(V*)`, `g • I_v = I_{ρ g v}`, so the decomposition
group `MulAction.stabilizer G I_v` is the point stabilizer `ρ.stabilizer v`. Two characteristic-free
comparisons then combine at `v`:

1. For any subgroup `H` with `ρ.stabilizer v ≤ H`, applying
   `AdicCompletion.underInvariantsEquivOfStabilizerLE` identifies the completion of `Sym(V*)^G` at
   `I_v ∩ Sym(V*)^G` with the completion of `Sym(V*)^H` at `I_v ∩ Sym(V*)^H`.
2. Over any commutative ring, for any subgroup `H` with `H ≤ ρ.stabilizer v`, the translation
   automorphism `SymmetricAlgebra.translation (Module.Dual.eval R V v)` commutes with the `H`-action
   on `Sym(V*)`, restricts to an automorphism of `Sym(V*)^H`, and carries `I_v ∩ Sym(V*)^H` onto the
   homogeneous irrelevant ideal `I_0 ∩ Sym(V*)^H`.

Taking `H = ρ.stabilizer v` yields a canonical `K`-algebra isomorphism between the completion of
`Sym(V*)^G` at the image of `v` in `V / G` and the completion of `Sym(V*)^{G_v}` at the homogeneous
vertex `0`, without any assumption on the characteristic of `K`. Consequently, `Sym(V*)^G` is
regular at `I_v ∩ Sym(V*)^G` if and only if `Sym(V*)^{G_v}` is regular at its vertex.

## Main definitions and results

* `SymmetricAlgebra.ker_lift_le_ker_lift_iff`, `SymmetricAlgebra.ker_lift_eq_ker_lift_iff`:
  evaluation kernels determine linear forms over any commutative ring.
* `SymmetricAlgebra.map_translation_ker_lift_self`: `SymmetricAlgebra.translation f` carries
  `RingHom.ker (SymmetricAlgebra.lift f)` onto the irrelevant ideal.
* `Representation.smul_ker_lift_eval` and `Representation.stabilizer_ker_lift_eval`: equivariance of
  evaluation ideals and identification of `MulAction.stabilizer G I_v` with `ρ.stabilizer v`.
* `Representation.symmetricAlgebraInvariantsTranslationEquiv`: for `H ≤ ρ.stabilizer v`, translation
  by `v` restricts to an `R`-algebra automorphism of
  `(dual (ρ.comp H.subtype)).symmetricAlgebraInvariants` carrying `I_v ∩ Sym(V*)^H` onto
  `I_0 ∩ Sym(V*)^H`.
* `Representation.adicCompletionUnderKerLiftEvalEquivOfStabilizerLE`: completed-local comparison
  between `G`-invariants and `H`-invariants at `v` when `ρ.stabilizer v ≤ H`.
* `Representation.adicCompletionUnderKerLiftEvalEquiv`: **completed-local quotient comparison**
  identifying the completion of `Sym(V*)^G` at `v` with the completion of `Sym(V*)^{G_v}` at `0`.
* `Representation.isRegularLocalRing_atPrime_under_ker_lift_eval_iff`: regularity of `Sym(V*)^G` at
  `v` is equivalent to regularity of `Sym(V*)^{G_v}` at its homogeneous vertex.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Chapter V, § 5, Exercise 8.
* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), § 22.1.
* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Chapter 7.
-/

public section

open scoped Pointwise
open TauCeti.SymmetricAlgebra

namespace SymmetricAlgebra

section CommRing

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

/-- Over any commutative ring, an inclusion between kernels of symmetric-algebra evaluations forces
the underlying linear forms to coincide. -/
theorem ker_lift_le_ker_lift_iff {f g : M →ₗ[R] R} :
    RingHom.ker (lift f) ≤ RingHom.ker (lift g) ↔ f = g := by
  refine ⟨fun h ↦ LinearMap.ext fun m ↦ ?_, fun h ↦ h ▸ le_rfl⟩
  have hm : ι R M m - algebraMap R (SymmetricAlgebra R M) (f m) ∈ RingHom.ker (lift f) := by
    simp [RingHom.mem_ker]
  have hgm := h hm
  rw [RingHom.mem_ker, map_sub, lift_ι_apply, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, sub_eq_zero] at hgm
  exact hgm.symm

/-- Two symmetric-algebra evaluation homomorphisms `lift f` and `lift g` have the same kernel if
and only if `f = g`. -/
@[simp]
theorem ker_lift_eq_ker_lift_iff {f g : M →ₗ[R] R} :
    RingHom.ker (lift f) = RingHom.ker (lift g) ↔ f = g :=
  ⟨fun h ↦ ker_lift_le_ker_lift_iff.mp h.le, fun h ↦ h ▸ rfl⟩

/-- The kernel of `lift 0` is the homogeneous irrelevant ideal of `SymmetricAlgebra R M`. -/
theorem ker_lift_zero_eq_irrelevant :
    RingHom.ker (lift (0 : M →ₗ[R] R)) =
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R M)).toIdeal := by
  have h0 : lift (0 : M →ₗ[R] R) = algebraMapInv :=
    algHom_ext <| LinearMap.ext fun m ↦ by simp [algebraMapInv_ι]
  rw [toIdeal_irrelevant_eq_ker_algebraMapInv, h0]

/-- Translation by `f` carries the kernel of `lift (g + f)` onto the kernel of `lift g`. -/
theorem map_translation_ker_lift (f g : M →ₗ[R] R) :
    (RingHom.ker (lift (g + f))).map (translation f) = RingHom.ker (lift g) := by
  have hfg : (g + f) + Algebra.linearMap R R ∘ₗ (-f) = g := by ext m; simp
  have hgf : g + Algebra.linearMap R R ∘ₗ f = g + f := by ext m; simp
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun p hp ↦ ?_) fun p hp ↦ ?_
  · change lift g (translation f p) = 0
    rwa [lift_translation, hgf]
  · have hmem : (translation f).symm p ∈ RingHom.ker (lift (g + f)) := by
      change lift (g + f) ((translation f).symm p) = 0
      rwa [translation_symm, lift_translation, hfg]
    rw [← (translation f).apply_symm_apply p]
    exact Ideal.mem_map_of_mem (translation f) hmem

/-- Translation by `f` carries the kernel of `lift f` onto the homogeneous irrelevant ideal. -/
theorem map_translation_ker_lift_self (f : M →ₗ[R] R) :
    (RingHom.ker (lift f)).map (translation f) =
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R M)).toIdeal := by
  simpa [zero_add, ker_lift_zero_eq_irrelevant] using map_translation_ker_lift f 0

end CommRing

section Field

variable {K M : Type*} [Field K] [AddCommMonoid M] [Module K M]

/-- Over a field, the kernel of `lift f : SymmetricAlgebra K M →ₐ[K] K` is maximal. -/
instance isMaximal_ker_lift (f : M →ₗ[K] K) : (RingHom.ker (lift f)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap K _ c, AlgHom.commutes _ c⟩

end Field

end SymmetricAlgebra

namespace Representation

section CommRing

variable {R G V : Type*} [CommRing R] [Group G] [AddCommMonoid V] [Module R V]
  (ρ : Representation R G V)

/-- Under the contragredient action of `G` on `Sym(V*)`, `g` translates the evaluation ideal at `v`
to the evaluation ideal at `ρ g v`. -/
theorem smul_ker_lift_eval (g : G) (v : V) :
    letI := ρ.dual.symmetricAlgebraMulSemiringAction
    g • RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval R V v)) =
      RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval R V (ρ g v))) := by
  let := ρ.dual.symmetricAlgebraMulSemiringAction
  ext p
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, RingHom.mem_ker, RingHom.mem_ker,
    symmetricAlgebraMulSemiringAction_smul, ρ.lift_eval_symmetricAlgebra_dual, inv_inv]

/-- If `g` fixes `v`, translation by `Module.Dual.eval R V v` commutes with the contragredient
action of `g` on `Sym(V*)`. -/
theorem translation_eval_symmetricAlgebra_dual_of_mem_stabilizer {g : G} {v : V}
    (hg : g ∈ ρ.stabilizer v) (p : SymmetricAlgebra R (Module.Dual R V)) :
    SymmetricAlgebra.translation (Module.Dual.eval R V v) (ρ.dual.symmetricAlgebra g p) =
      ρ.dual.symmetricAlgebra g (SymmetricAlgebra.translation (Module.Dual.eval R V v) p) := by
  have hginv : ρ g⁻¹ v = v := (ρ.stabilizer v).inv_mem hg
  have hcomp :
      (SymmetricAlgebra.translation (Module.Dual.eval R V v)).toAlgHom.comp
        (SymmetricAlgebra.map R (ρ.dual g)) =
      (SymmetricAlgebra.map R (ρ.dual g)).comp
        (SymmetricAlgebra.translation (Module.Dual.eval R V v)).toAlgHom :=
    SymmetricAlgebra.algHom_ext <| LinearMap.ext fun φ ↦ by
      simp [Module.Dual.transpose_apply, hginv]
  rw [symmetricAlgebra_apply, symmetricAlgebra_apply]
  exact DFunLike.congr_fun hcomp p

/-- For a subgroup `H ≤ ρ.stabilizer v`, `SymmetricAlgebra.translation (Module.Dual.eval R V v)`
preserves `(dual (ρ.comp H.subtype)).symmetricAlgebraInvariants`. -/
theorem translation_eval_mem_symmetricAlgebraInvariants_iff {v : V} {H : Subgroup G}
    (hH : H ≤ ρ.stabilizer v) (p : SymmetricAlgebra R (Module.Dual R V)) :
    SymmetricAlgebra.translation (Module.Dual.eval R V v) p ∈
        (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants ↔
      p ∈ (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants := by
  rw [dual_comp]
  simp only [mem_symmetricAlgebraInvariants, symmetricAlgebra_comp_apply, Subgroup.coe_subtype]
  refine ⟨fun hp h ↦ ?_, fun hp h ↦ ?_⟩
  · apply (SymmetricAlgebra.translation (Module.Dual.eval R V v)).injective
    rw [ρ.translation_eval_symmetricAlgebra_dual_of_mem_stabilizer (hH h.2), hp h]
  · rw [← ρ.translation_eval_symmetricAlgebra_dual_of_mem_stabilizer (hH h.2), hp h]

/-- For a subgroup `H ≤ ρ.stabilizer v`, translation by `v` restricts to an `R`-algebra
automorphism of `(dual (ρ.comp H.subtype)).symmetricAlgebraInvariants`. -/
noncomputable def symmetricAlgebraInvariantsTranslationEquiv {v : V} {H : Subgroup G}
    (hH : H ≤ ρ.stabilizer v) :
    (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants ≃ₐ[R]
      (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants :=
  let e := SymmetricAlgebra.translation (Module.Dual.eval R V v)
  have hmem (p : (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants) :
      e p.1 ∈ (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants :=
    (ρ.translation_eval_mem_symmetricAlgebraInvariants_iff hH p.1).mpr p.2
  have hsymm (p : (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants) :
      e.symm p.1 ∈ (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants := by
    refine (ρ.translation_eval_mem_symmetricAlgebraInvariants_iff hH (e.symm p.1)).mp ?_
    simpa [e] using p.2
  AlgEquiv.ofAlgHom
    ((e.toAlgHom.comp (Subalgebra.val _)).codRestrict _ hmem)
    ((e.symm.toAlgHom.comp (Subalgebra.val _)).codRestrict _ hsymm)
    (AlgHom.ext fun p ↦ Subtype.ext (e.apply_symm_apply p.1))
    (AlgHom.ext fun p ↦ Subtype.ext (e.symm_apply_apply p.1))

/-- In the ambient symmetric algebra, `symmetricAlgebraInvariantsTranslationEquiv` acts by
`SymmetricAlgebra.translation (Module.Dual.eval R V v)`. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsTranslationEquiv_apply {v : V} {H : Subgroup G}
    (hH : H ≤ ρ.stabilizer v) (p : (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants) :
    (ρ.symmetricAlgebraInvariantsTranslationEquiv hH p :
        SymmetricAlgebra R (Module.Dual R V)) =
      SymmetricAlgebra.translation (Module.Dual.eval R V v) p.1 := by
  dsimp only [symmetricAlgebraInvariantsTranslationEquiv]
  rfl

/-- In the ambient symmetric algebra, the inverse of `symmetricAlgebraInvariantsTranslationEquiv`
acts by `(SymmetricAlgebra.translation (Module.Dual.eval R V v)).symm`. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsTranslationEquiv_symm_apply {v : V} {H : Subgroup G}
    (hH : H ≤ ρ.stabilizer v) (p : (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants) :
    ((ρ.symmetricAlgebraInvariantsTranslationEquiv hH).symm p :
        SymmetricAlgebra R (Module.Dual R V)) =
      (SymmetricAlgebra.translation (Module.Dual.eval R V v)).symm p.1 := by
  dsimp only [symmetricAlgebraInvariantsTranslationEquiv]
  rfl

/-- Under `symmetricAlgebraInvariantsTranslationEquiv`, the contraction of the evaluation ideal at
`v` to `Sym(V*)^H` maps onto the contraction of the homogeneous irrelevant ideal. -/
theorem map_under_ker_lift_eval_symmetricAlgebraInvariantsTranslationEquiv {v : V}
    {H : Subgroup G} (hH : H ≤ ρ.stabilizer v) :
    ((RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval R V v))).under
        (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants).map
      (ρ.symmetricAlgebraInvariantsTranslationEquiv hH) =
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R (Module.Dual R V))).toIdeal.under
        (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants := by
  let e := ρ.symmetricAlgebraInvariantsTranslationEquiv hH
  have hmap := SymmetricAlgebra.map_translation_ker_lift_self (Module.Dual.eval R V v)
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun p hp ↦ ?_) fun p hp ↦ ?_
  · rw [Ideal.mem_comap, Ideal.mem_under, ← hmap]
    exact Ideal.mem_map_of_mem _ hp
  · have hp0 : (p : SymmetricAlgebra R (Module.Dual R V)) ∈
        RingHom.ker (SymmetricAlgebra.lift (0 : Module.Dual R V →ₗ[R] R)) := by
      rwa [SymmetricAlgebra.ker_lift_zero_eq_irrelevant]
    have hfv : Module.Dual.eval R V v + Algebra.linearMap R R ∘ₗ (-Module.Dual.eval R V v) = 0 := by
      ext φ; simp
    have hmem : e.symm p ∈
        (RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval R V v))).under
          (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants := by
      change SymmetricAlgebra.lift (Module.Dual.eval R V v)
        (e.symm p : SymmetricAlgebra R (Module.Dual R V)) = 0
      rw [show (e.symm p : SymmetricAlgebra R (Module.Dual R V)) =
          (SymmetricAlgebra.translation (Module.Dual.eval R V v)).symm p.1 from
        ρ.coe_symmetricAlgebraInvariantsTranslationEquiv_symm_apply hH p]
      rw [SymmetricAlgebra.translation_symm, SymmetricAlgebra.lift_translation, hfv]
      exact hp0
    rw [← e.apply_symm_apply p]
    exact Ideal.mem_map_of_mem e hmem

end CommRing

section Field

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V)

/-- Over a field, the stabilizer of the evaluation ideal at `v` in `Sym(V*)` equals the vector
stabilizer `ρ.stabilizer v`. -/
theorem stabilizer_ker_lift_eval (v : V) :
    letI := ρ.dual.symmetricAlgebraMulSemiringAction
    MulAction.stabilizer G (RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval K V v))) =
      ρ.stabilizer v := by
  let := ρ.dual.symmetricAlgebraMulSemiringAction
  ext g
  rw [MulAction.mem_stabilizer_iff, ρ.smul_ker_lift_eval, SymmetricAlgebra.ker_lift_eq_ker_lift_iff,
    (Module.eval_apply_injective K).eq_iff, mem_stabilizer]

/-- Every `G`-invariant polynomial function is invariant under any subgroup `H` of `G`. -/
theorem symmetricAlgebraInvariants_dual_le_comp_subtype (H : Subgroup G) :
    ρ.dual.symmetricAlgebraInvariants ≤
      (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants := fun p hp ↦ by
  let := ρ.dual.symmetricAlgebraMulSemiringAction
  have := ρ.dual.smulCommClass_symmetricAlgebraMulSemiringAction
  rw [dual_comp, ρ.dual.symmetricAlgebraInvariants_comp_subtype, FixedPoints.mem_subalgebra]
  intro h
  exact (ρ.dual.mem_symmetricAlgebraInvariants p).mp hp h.1

variable [Finite G] [FiniteDimensional K V]

/-- **Completed-local comparison with an intermediate subgroup containing `ρ.stabilizer v`.** Let a
finite group `G` act linearly on a finite-dimensional `K`-vector space `V`, and let `H` be a
subgroup of `G` with `ρ.stabilizer v ≤ H`. Then the inclusion `Sym(V*)^G ↪ Sym(V*)^H` induces a
`K`-algebra isomorphism between their completions at the contractions of the evaluation ideal at
`v`. -/
noncomputable def adicCompletionUnderKerLiftEvalEquivOfStabilizerLE (v : V)
    {H : Subgroup G} (hH : ρ.stabilizer v ≤ H) :
    AdicCompletion
      ((RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval K V v))).under
        ρ.dual.symmetricAlgebraInvariants)
      ρ.dual.symmetricAlgebraInvariants ≃ₐ[K]
    AdicCompletion
      ((RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval K V v))).under
        (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants)
      (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants :=
  let B := SymmetricAlgebra K (Module.Dual K V)
  let Q : Ideal B := RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval K V v))
  letI := ρ.dual.symmetricAlgebraMulSemiringAction
  haveI := ρ.dual.smulCommClass_symmetricAlgebraMulSemiringAction
  have hC_eq : (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants =
      FixedPoints.subalgebra K B H := by
    rw [dual_comp, ρ.dual.symmetricAlgebraInvariants_comp_subtype]
  letI : Algebra ρ.dual.symmetricAlgebraInvariants
      (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants :=
    (Subalgebra.inclusion (ρ.symmetricAlgebraInvariants_dual_le_comp_subtype H)).toAlgebra
  haveI : IsScalarTower K ρ.dual.symmetricAlgebraInvariants
      (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ρ.dual.symmetricAlgebraInvariants
      (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul ρ.dual.symmetricAlgebraInvariants B :=
    ⟨fun h ↦ Subtype.ext (by simpa [Algebra.smul_def] using h 1)⟩
  haveI : FaithfulSMul (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants B :=
    ⟨fun h ↦ Subtype.ext (by simpa [Algebra.smul_def] using h 1)⟩
  haveI : IsNoetherianRing ρ.dual.symmetricAlgebraInvariants :=
    Algebra.FiniteType.isNoetherianRing K _
  haveI : Algebra.IsInvariant ρ.dual.symmetricAlgebraInvariants B G :=
    ρ.dual.isInvariant_symmetricAlgebraInvariants
  haveI : Algebra.IsInvariant (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants B H :=
    hC_eq ▸ inferInstance
  haveI : SMulCommClass G ρ.dual.symmetricAlgebraInvariants B :=
    ⟨fun g a b ↦ by
      have ha : g • (a : B) = a := by
        simpa [symmetricAlgebraMulSemiringAction_smul] using
          (ρ.dual.mem_symmetricAlgebraInvariants a.1).mp a.2 g
      rw [Subalgebra.smul_def, smul_eq_mul, smul_mul', ha, ← smul_eq_mul, ← Subalgebra.smul_def]⟩
  haveI : SMulCommClass H (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants B :=
    ⟨fun h c b ↦ by
      let c₀ : B := c
      have hc' : c₀ ∈ (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants := c.2
      rw [hC_eq, FixedPoints.mem_subalgebra] at hc'
      have hc : h • (c : B) = c := hc' h
      rw [Subalgebra.smul_def, smul_eq_mul, smul_mul', hc, ← smul_eq_mul, ← Subalgebra.smul_def]⟩
  AdicCompletion.underInvariantsEquivOfStabilizerLE K ρ.dual.symmetricAlgebraInvariants Q
    ((ρ.stabilizer_ker_lift_eval v).le.trans hH)
    (dual (ρ.comp H.subtype)).symmetricAlgebraInvariants

/-- On canonical images of `G`-invariants, `adicCompletionUnderKerLiftEvalEquivOfStabilizerLE` acts
by the subalgebra inclusion `Sym(V*)^G ↪ Sym(V*)^H`. -/
@[simp]
theorem adicCompletionUnderKerLiftEvalEquivOfStabilizerLE_of (v : V)
    {H : Subgroup G} (hH : ρ.stabilizer v ≤ H) (p : ρ.dual.symmetricAlgebraInvariants) :
    ρ.adicCompletionUnderKerLiftEvalEquivOfStabilizerLE v hH (AdicCompletion.of _ _ p) =
      AdicCompletion.of _ _
        (Subalgebra.inclusion (ρ.symmetricAlgebraInvariants_dual_le_comp_subtype H) p) := by
  dsimp only [adicCompletionUnderKerLiftEvalEquivOfStabilizerLE]
  rw [AdicCompletion.underInvariantsEquivOfStabilizerLE_of]
  rfl

/-- **Completed-local quotient comparison.** For a finite group `G` acting linearly on a
finite-dimensional vector space `V` over an arbitrary field `K` and any vector `v : V`, the
completion of `Sym(V*)^G` at the contraction of the evaluation ideal at `v` is canonically
isomorphic as a `K`-algebra to the completion of `Sym(V*)^{G_v}` at the homogeneous irrelevant
ideal. -/
noncomputable def adicCompletionUnderKerLiftEvalEquiv (v : V) :
    AdicCompletion
      ((RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval K V v))).under
        ρ.dual.symmetricAlgebraInvariants)
      ρ.dual.symmetricAlgebraInvariants ≃ₐ[K]
    AdicCompletion
      ((HomogeneousIdeal.irrelevant (homogeneousSubmodule K (Module.Dual K V))).toIdeal.under
        (dual (ρ.comp (ρ.stabilizer v).subtype)).symmetricAlgebraInvariants)
      (dual (ρ.comp (ρ.stabilizer v).subtype)).symmetricAlgebraInvariants :=
  (ρ.adicCompletionUnderKerLiftEvalEquivOfStabilizerLE v le_rfl).trans
    (AdicCompletion.congrₐ (ρ.symmetricAlgebraInvariantsTranslationEquiv le_rfl)
      (ρ.map_under_ker_lift_eval_symmetricAlgebraInvariantsTranslationEquiv le_rfl))

/-- On canonical images of `G`-invariants, `adicCompletionUnderKerLiftEvalEquiv` translates by `v`
inside `Sym(V*)^{G_v}`. -/
theorem adicCompletionUnderKerLiftEvalEquiv_of (v : V) (p : ρ.dual.symmetricAlgebraInvariants) :
    ρ.adicCompletionUnderKerLiftEvalEquiv v (AdicCompletion.of _ _ p) =
      AdicCompletion.of _ _
        (ρ.symmetricAlgebraInvariantsTranslationEquiv le_rfl
          (Subalgebra.inclusion
            (ρ.symmetricAlgebraInvariants_dual_le_comp_subtype (ρ.stabilizer v)) p)) := by
  rw [adicCompletionUnderKerLiftEvalEquiv, AlgEquiv.trans_apply,
    ρ.adicCompletionUnderKerLiftEvalEquivOfStabilizerLE_of v le_rfl p,
    AdicCompletion.congrₐ_of]

/-- The localization of `Sym(V*)^G` at `v` and the localization of `Sym(V*)^{G_v}` at the
homogeneous vertex `0` have the same Krull dimension. -/
theorem ringKrullDim_atPrime_under_ker_lift_eval_eq (v : V) :
    ringKrullDim (Localization.AtPrime
      ((RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval K V v))).under
        ρ.dual.symmetricAlgebraInvariants)) =
      ringKrullDim (Localization.AtPrime
        ((HomogeneousIdeal.irrelevant (homogeneousSubmodule K (Module.Dual K V))).toIdeal.under
          (dual (ρ.comp (ρ.stabilizer v).subtype)).symmetricAlgebraInvariants)) := by
  let A := ρ.dual.symmetricAlgebraInvariants
  let C := (dual (ρ.comp (ρ.stabilizer v).subtype)).symmetricAlgebraInvariants
  let Pv := (RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval K V v))).under A
  let P0 := (HomogeneousIdeal.irrelevant (homogeneousSubmodule K (Module.Dual K V))).toIdeal.under C
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing K C
  have : Pv.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) _
  have : P0.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := C) _
  rw [← TauCeti.AdicCompletion.ringKrullDim_eq_atPrime Pv,
    ← TauCeti.AdicCompletion.ringKrullDim_eq_atPrime P0]
  exact ringKrullDim_eq_of_ringEquiv (ρ.adicCompletionUnderKerLiftEvalEquiv v).toRingEquiv

/-- **Completed-local regularity transfer.** For a finite group `G` acting linearly on a
finite-dimensional `K`-vector space `V`, the localization of `Sym(V*)^G` at the evaluation ideal of
`v` is a regular local ring if and only if the localization of `Sym(V*)^{G_v}` at its homogeneous
irrelevant ideal is a regular local ring. -/
theorem isRegularLocalRing_atPrime_under_ker_lift_eval_iff (v : V) :
    IsRegularLocalRing (Localization.AtPrime
      ((RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval K V v))).under
        ρ.dual.symmetricAlgebraInvariants)) ↔
      IsRegularLocalRing (Localization.AtPrime
        ((HomogeneousIdeal.irrelevant (homogeneousSubmodule K (Module.Dual K V))).toIdeal.under
          (dual (ρ.comp (ρ.stabilizer v).subtype)).symmetricAlgebraInvariants)) := by
  let A := ρ.dual.symmetricAlgebraInvariants
  let C := (dual (ρ.comp (ρ.stabilizer v).subtype)).symmetricAlgebraInvariants
  let Pv := (RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval K V v))).under A
  let P0 := (HomogeneousIdeal.irrelevant (homogeneousSubmodule K (Module.Dual K V))).toIdeal.under C
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing K C
  have : Pv.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) _
  have : P0.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := C) _
  rw [← TauCeti.AdicCompletion.isRegularLocalRing_iff_atPrime Pv,
    ← TauCeti.AdicCompletion.isRegularLocalRing_iff_atPrime P0]
  let e := (ρ.adicCompletionUnderKerLiftEvalEquiv v).toRingEquiv
  exact ⟨fun h ↦ h.of_ringEquiv e, fun h ↦ h.of_ringEquiv e.symm⟩

end Field

end Representation
