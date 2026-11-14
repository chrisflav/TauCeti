/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Injective
public import TauCeti.Algebra.DirectSum.Internal
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import TauCeti.Algebra.Category.GradedModuleCat.Abelian

/-!
# Coinduced graded modules and injective presentations

For a graded `k`-algebra `A = ⨁ 𝒜_q` and a family `E : ℤ → Type v` of `k`-modules, the
**coinduced graded module** `coinduced 𝒜 E` consists of finite sums of homogeneous families in
`∀ p : ℤ, A →ₗ[k] E p`, where a family has degree `n` when its `p`-th component vanishes on
`𝒜_q` for every `q ≠ p - n`, and where `A` acts on the left by right translation `(a • f)_p(b) =
f_p(b * a)`.

Graded morphisms `M ⟶ coinduced 𝒜 E` are in natural `k`-linear bijection with degreewise
`k`-linear maps `∀ p : ℤ, M_p →ₗ[k] E p`: a graded map is sent to evaluation at `1 ∈ A` on each
homogeneous piece, while a family `φ` lifts to `m ↦ (p, b ↦ φ_p((b • m)_p))`.

Consequently:

* if every `E p` satisfies Baer's criterion over `k` (in particular, if every `E p` is an injective
  `k`-module and `k` is `v`-small, or `E` already lives in `max uA v`), `coinduced 𝒜 E` is an
  injective object of `GradedModuleCat 𝒜`;
* embedding each homogeneous piece `M_p` into an injective `k`-module gives a graded monomorphism
  into an injective graded module, so `GradedModuleCat 𝒜` has enough injectives whenever `k` is
  small relative to the module universe.

No positivity, commutativity, or finite-dimensionality assumption on `A` is imposed.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v

/-! ### The ambient right-translation module and its graded submodule -/

/-- Wrapper for `∀ p : ℤ, A →ₗ[k] E p` carrying the right-translation left `A`-action, avoiding
any instance diamond with `LinearMap.module` when `A = k`. -/
@[ext]
private structure CoinducedAmbient (k : Type uk) [CommRing k] (A : Type uA) [Ring A] [Algebra k A]
    (E : ℤ → Type v) [∀ p, AddCommGroup (E p)] [∀ p, Module k (E p)] : Type (max uA v) where
  /-- The underlying family of `k`-linear maps out of `A`. -/
  fn : ∀ p : ℤ, A →ₗ[k] E p

namespace CoinducedAmbient

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {E : ℤ → Type v} [∀ p, AddCommGroup (E p)] [∀ p, Module k (E p)]

private instance : Zero (CoinducedAmbient k A E) := ⟨⟨0⟩⟩
private instance : Add (CoinducedAmbient k A E) := ⟨fun x y ↦ ⟨x.fn + y.fn⟩⟩
private instance : Neg (CoinducedAmbient k A E) := ⟨fun x ↦ ⟨-x.fn⟩⟩
private instance : Sub (CoinducedAmbient k A E) := ⟨fun x y ↦ ⟨x.fn - y.fn⟩⟩
private instance : SMul ℕ (CoinducedAmbient k A E) := ⟨fun n x ↦ ⟨n • x.fn⟩⟩
private instance : SMul ℤ (CoinducedAmbient k A E) := ⟨fun n x ↦ ⟨n • x.fn⟩⟩
private instance : SMul k (CoinducedAmbient k A E) := ⟨fun c x ↦ ⟨c • x.fn⟩⟩

private instance : AddCommGroup (CoinducedAmbient k A E) :=
  Function.Injective.addCommGroup fn (fun _ _ ↦ CoinducedAmbient.ext)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

private instance : Module k (CoinducedAmbient k A E) :=
  Function.Injective.module k ⟨⟨fn, rfl⟩, fun _ _ ↦ rfl⟩ (fun _ _ ↦ CoinducedAmbient.ext)
    (fun _ _ ↦ rfl)

private instance : SMul A (CoinducedAmbient k A E) where
  smul a x := ⟨fun p ↦ (x.fn p).comp (LinearMap.mulRight k a)⟩

@[simp]
private theorem fn_zero : (0 : CoinducedAmbient k A E).fn = 0 := rfl

@[simp]
private theorem fn_add (x y : CoinducedAmbient k A E) : (x + y).fn = x.fn + y.fn := rfl

@[simp]
private theorem fn_neg (x : CoinducedAmbient k A E) : (-x).fn = -x.fn := rfl

@[simp]
private theorem fn_sub (x y : CoinducedAmbient k A E) : (x - y).fn = x.fn - y.fn := rfl

@[simp]
private theorem fn_smul_base (c : k) (x : CoinducedAmbient k A E) : (c • x).fn = c • x.fn := rfl

@[simp]
private theorem fn_smul (a : A) (x : CoinducedAmbient k A E) (p : ℤ) (b : A) :
    (a • x).fn p b = x.fn p (b * a) := rfl

private instance : Module A (CoinducedAmbient k A E) where
  one_smul x := by ext p b; simp
  mul_smul a₁ a₂ x := by ext p b; simp [mul_assoc]
  smul_zero a := by ext p _b; simp
  smul_add a x y := by ext p b; simp
  add_smul a₁ a₂ x := by ext p b; simp [mul_add]
  zero_smul x := by ext p _b; simp

private instance : IsScalarTower k A (CoinducedAmbient k A E) where
  smul_assoc c a x := by
    ext p b
    simp

end CoinducedAmbient

section Construction

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
  (E : ℤ → Type v) [∀ p, AddCommGroup (E p)] [∀ p, Module k (E p)]

omit [GradedAlgebra 𝒜] in
/-- Homogeneous elements of degree `n` in `CoinducedAmbient k A E`: those whose `p`-th component
vanishes on `𝒜 q` whenever `q ≠ p - n`. -/
private def coinducedPiece (n : ℤ) : Submodule k (CoinducedAmbient k A E) where
  carrier := {x | ∀ (p q : ℤ), q ≠ p - n → ∀ b ∈ 𝒜 q, x.fn p b = 0}
  zero_mem' _ _ _ _ _ := rfl
  add_mem' hx hy p q hq b hb := by simp [hx p q hq b hb, hy p q hq b hb]
  smul_mem' c x hx p q hq b hb := by simp [hx p q hq b hb]

private theorem smul_mem_coinducedPiece {r n : ℤ} {a : A} (ha : a ∈ 𝒜 r)
    {x : CoinducedAmbient k A E} (hx : x ∈ coinducedPiece 𝒜 E n) :
    a • x ∈ coinducedPiece 𝒜 E (r + n) := by
  intro p q hq b hb
  exact hx p (q + r) (by omega) (b * a) (SetLike.GradedMul.mul_mem hb ha)

omit [GradedAlgebra 𝒜] in
private def coinducedBaseSubmodule : Submodule k (CoinducedAmbient k A E) :=
  LinearMap.range (DirectSum.coeLinearMap (coinducedPiece 𝒜 E))

omit [GradedAlgebra 𝒜] in
private theorem coinducedPiece_le_base (n : ℤ) :
    coinducedPiece 𝒜 E n ≤ coinducedBaseSubmodule 𝒜 E := by
  intro x hx
  exact ⟨DirectSum.lof k ℤ (fun m ↦ coinducedPiece 𝒜 E m) n ⟨x, hx⟩,
    DirectSum.coeLinearMap_lof (coinducedPiece 𝒜 E) n ⟨x, hx⟩⟩

private theorem coinducedBaseSubmodule_smul_mem (a : A) {x : CoinducedAmbient k A E}
    (hx : x ∈ coinducedBaseSubmodule 𝒜 E) : a • x ∈ coinducedBaseSubmodule 𝒜 E := by
  classical
  obtain ⟨y, rfl⟩ := hx
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y z hy hz => simpa only [map_add, smul_add] using (coinducedBaseSubmodule 𝒜 E).add_mem hy hz
  | of n f =>
    rw [DirectSum.coeLinearMap_of]
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add a₁ a₂ ha₁ ha₂ =>
      simpa only [add_smul] using (coinducedBaseSubmodule 𝒜 E).add_mem ha₁ ha₂
    | homogeneous a =>
      exact coinducedPiece_le_base 𝒜 E _ (smul_mem_coinducedPiece 𝒜 E a.2 f.2)

/-- The `A`-submodule of `CoinducedAmbient k A E` spanned by all homogeneous pieces. -/
private def coinducedSubmodule : Submodule A (CoinducedAmbient k A E) where
  carrier := coinducedBaseSubmodule 𝒜 E
  zero_mem' := (coinducedBaseSubmodule 𝒜 E).zero_mem
  add_mem' := (coinducedBaseSubmodule 𝒜 E).add_mem
  smul_mem' a _ hx := coinducedBaseSubmodule_smul_mem 𝒜 E a hx

private theorem coinduced_coeLinearMap_injective :
    Function.Injective (DirectSum.coeLinearMap (coinducedPiece 𝒜 E)) := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  ext n : 1
  apply Subtype.ext
  ext p b
  simp only [DirectSum.zero_apply, Submodule.coe_zero, CoinducedAmbient.fn_zero,
    Pi.zero_apply, LinearMap.zero_apply]
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add b₁ b₂ hb₁ hb₂ => simp [hb₁, hb₂]
  | homogeneous b =>
    rcases b with ⟨b, hb⟩
    rename_i q
    by_cases hqn : q = p - n
    · have hsum : ∀ z : ⨁ m, coinducedPiece 𝒜 E m,
          (DirectSum.coeLinearMap (coinducedPiece 𝒜 E) z).fn p b = (z n).1.fn p b := by
        intro z
        induction z using DirectSum.induction_on with
        | zero => simp
        | of m x =>
          rw [DirectSum.coeLinearMap_of]
          by_cases hmn : m = n
          · subst hmn; simp
          · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hmn)]
            simpa using x.2 p q (by omega) b hb
        | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
      have hzero : (DirectSum.coeLinearMap (coinducedPiece 𝒜 E) y).fn p b = 0 := by
        rw [hy]
        rfl
      exact (hsum y).symm.trans hzero
    · exact (y n).2 p q hqn b hb

private def coinducedEquiv :
    (⨁ n : ℤ, coinducedPiece 𝒜 E n) ≃ₗ[k] coinducedSubmodule 𝒜 E :=
  LinearEquiv.ofInjective (DirectSum.coeLinearMap (coinducedPiece 𝒜 E))
    (coinduced_coeLinearMap_injective 𝒜 E)

private theorem coinducedEquiv_apply_val (y : ⨁ n : ℤ, coinducedPiece 𝒜 E n) :
    (coinducedEquiv 𝒜 E y).1 = DirectSum.coeLinearMap (coinducedPiece 𝒜 E) y :=
  rfl

private def coinducedGrading : InternalGrading k (coinducedSubmodule 𝒜 E) ℤ :=
  (InternalGrading.ofDecomposition
    (DirectSum.summand k (fun n ↦ (coinducedPiece 𝒜 E n : Type (max uA v))))).map
    (coinducedEquiv 𝒜 E)

private theorem mem_coinducedGrading_piece_iff (n : ℤ) (x : coinducedSubmodule 𝒜 E) :
    x ∈ (coinducedGrading 𝒜 E).piece n ↔ x.1 ∈ coinducedPiece 𝒜 E n := by
  rw [coinducedGrading, InternalGrading.map_piece, InternalGrading.ofDecomposition_piece,
    DirectSum.summand_def]
  constructor
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    rw [LinearEquiv.coe_coe, coinducedEquiv_apply_val, DirectSum.coeLinearMap_lof]
    exact t.2
  · intro hx
    refine ⟨DirectSum.lof k ℤ (fun m ↦ coinducedPiece 𝒜 E m) n ⟨x.1, hx⟩, ⟨⟨x.1, hx⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, coinducedEquiv_apply_val, DirectSum.coeLinearMap_lof]

/-- The **coinduced graded module** of a family `E : ℤ → Type v` of `k`-modules over a graded
`k`-algebra `A = ⨁ 𝒜_q`. -/
def coinduced : GradedModuleCat.{max uA v} 𝒜 where
  carrier := coinducedSubmodule 𝒜 E
  grading := coinducedGrading 𝒜 E
  gradedSMul :=
    ⟨fun {_ _} _ _ ha hx ↦
      (mem_coinducedGrading_piece_iff 𝒜 E _ _).mpr
        (smul_mem_coinducedPiece 𝒜 E ha ((mem_coinducedGrading_piece_iff 𝒜 E _ _).mp hx))⟩

end Construction

/-! ### Universal property -/

section UniversalProperty

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {E : ℤ → Type v} [∀ p, AddCommGroup (E p)] [∀ p, Module k (E p)]

private def coinducedFn (x : coinduced 𝒜 E) : ∀ p : ℤ, A →ₗ[k] E p :=
  x.1.fn

private theorem coinducedFn_zero : coinducedFn (0 : coinduced 𝒜 E) = 0 :=
  rfl

private theorem coinducedFn_smul (b : A) (x : coinduced 𝒜 E) (p : ℤ) :
    coinducedFn (b • x) p 1 = coinducedFn x p b :=
  congrArg (x.1.fn p) (one_mul b)

private theorem coinducedFn_eq_zero_of_mem {n p q : ℤ} {x : coinduced 𝒜 E}
    (hx : x ∈ (coinduced 𝒜 E).grading.piece n) (hq : q ≠ p - n) {b : A} (hb : b ∈ 𝒜 q) :
    coinducedFn x p b = 0 :=
  (mem_coinducedGrading_piece_iff 𝒜 E n x).mp hx p q hq b hb

private theorem coinduced_carrier_ext {x y : coinduced 𝒜 E}
    (h : ∀ p b, coinducedFn x p b = coinducedFn y p b) : x = y :=
  Subtype.ext (CoinducedAmbient.ext (funext fun p ↦ LinearMap.ext fun b ↦ h p b))

/-- Evaluate the degree-`p` piece of `coinduced 𝒜 E` at `1 ∈ A` to obtain an element of `E p`. -/
def coinducedCounit (p : ℤ) : (coinduced 𝒜 E).grading.piece p →ₗ[k] E p where
  toFun x := coinducedFn x.1 p 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem coinducedCounit_mk (p : ℤ) (x : coinduced 𝒜 E)
    (hx : x ∈ (coinduced 𝒜 E).grading.piece p) :
    coinducedCounit p ⟨x, hx⟩ = coinducedFn x p 1 :=
  rfl

omit [GradedAlgebra 𝒜] in
private def coinducedLiftAmbient {M : GradedModuleCat.{max uA v} 𝒜}
    (φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p) : M →ₗ[A] CoinducedAmbient k A E where
  toFun m :=
    ⟨fun p ↦
      { toFun := fun b ↦ φ p (DirectSum.decompose M.grading.piece (b • m) p)
        map_add' := fun b₁ b₂ ↦ by simp [add_smul]
        map_smul' := fun c b ↦ by
          rw [smul_assoc, ← (φ p).map_smul]
          congr 1
          exact congrArg (fun d ↦ d p) (DirectSum.decompose_smul M.grading.piece c (b • m)) }⟩
  map_add' m₁ m₂ := by
    ext p b
    simp [smul_add]
  map_smul' a m := by
    ext p b
    simp [mul_smul]

omit [GradedAlgebra 𝒜] in
@[simp]
private theorem coinducedLiftAmbient_fn {M : GradedModuleCat.{max uA v} 𝒜}
    (φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p) (m : M) (p : ℤ) (b : A) :
    (coinducedLiftAmbient φ m).fn p b = φ p (DirectSum.decompose M.grading.piece (b • m) p) :=
  rfl

omit [GradedAlgebra 𝒜] in
private theorem coinducedLiftAmbient_mem_piece {M : GradedModuleCat.{max uA v} 𝒜}
    (φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p) {n : ℤ} {m : M}
    (hm : m ∈ M.grading.piece n) :
    coinducedLiftAmbient φ m ∈ coinducedPiece 𝒜 E n := by
  intro p q hq b hb
  have hbm : b • m ∈ M.grading.piece (q + n) := SetLike.GradedSMul.smul_mem hb hm
  have hdec : DirectSum.decompose M.grading.piece (b • m) p = 0 :=
    Subtype.ext (DirectSum.decompose_of_mem_ne M.grading.piece hbm (by omega))
  rw [coinducedLiftAmbient_fn, hdec, map_zero]

private theorem coinducedLiftAmbient_mem {M : GradedModuleCat.{max uA v} 𝒜}
    (φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p) (m : M) :
    coinducedLiftAmbient φ m ∈ coinducedSubmodule 𝒜 E := by
  classical
  rw [← DirectSum.sum_support_decompose M.grading.piece m, map_sum]
  refine (coinducedSubmodule 𝒜 E).sum_mem fun n _ ↦ ?_
  exact coinducedPiece_le_base 𝒜 E n
    (coinducedLiftAmbient_mem_piece φ (DirectSum.decompose M.grading.piece m n).2)

/-- Lift a degreewise family of `k`-linear maps `M_p →ₗ[k] E p` to a morphism of graded `A`-modules
`M ⟶ coinduced 𝒜 E`. -/
def coinducedLift {M : GradedModuleCat.{max uA v} 𝒜}
    (φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p) : M ⟶ coinduced 𝒜 E :=
  ofHom ((coinducedLiftAmbient φ).codRestrict (coinducedSubmodule 𝒜 E) (coinducedLiftAmbient_mem φ))
    (LinearMap.isHomogeneous_def.mpr fun n m hm ↦ by
      rw [add_zero]
      exact (mem_coinducedGrading_piece_iff 𝒜 E n _).mpr (coinducedLiftAmbient_mem_piece φ hm))

private theorem coinducedFn_coinducedLift {M : GradedModuleCat.{max uA v} 𝒜}
    (φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p) (m : M) (p : ℤ) (b : A) :
    coinducedFn ((coinducedLift φ).hom m) p b =
      φ p (DirectSum.decompose M.grading.piece (b • m) p) :=
  rfl

/-- Evaluating the lifted map at `1 ∈ A` on the degree-`p` piece recovers `φ p`. -/
@[simp]
theorem coinducedCounit_coinducedLift {M : GradedModuleCat.{max uA v} 𝒜}
    (φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p) (p : ℤ) (m : M.grading.piece p) :
    coinducedCounit p ⟨(coinducedLift φ).hom m, map_mem (coinducedLift φ) m.2⟩ = φ p m := by
  rw [coinducedCounit_mk, coinducedFn_coinducedLift, one_smul]
  congr 1
  exact Subtype.ext (DirectSum.decompose_of_mem_same M.grading.piece m.2)

/-- Morphisms into `coinduced 𝒜 E` are determined by their composites with `coinducedCounit`. -/
@[ext]
theorem coinduced_hom_ext {M : GradedModuleCat.{max uA v} 𝒜} {f g : M ⟶ coinduced 𝒜 E}
    (h : ∀ p (m : M.grading.piece p),
      coinducedCounit p ⟨f.hom m, map_mem f m.2⟩ = coinducedCounit p ⟨g.hom m, map_mem g m.2⟩) :
    f = g := by
  apply hom_ext
  apply M.grading.linearMap_ext
  intro n m hm
  apply coinduced_carrier_ext
  intro p b
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp [coinducedFn]
  | add b₁ b₂ hb₁ hb₂ =>
    rw [map_add, map_add, hb₁, hb₂]
  | homogeneous b =>
    rcases b with ⟨b, hb⟩
    rename_i q
    by_cases hqn : q = p - n
    · have hbm : b • m ∈ M.grading.piece p := by
        have h' := SetLike.GradedSMul.smul_mem hb hm
        rwa [hqn, vadd_eq_add, sub_add_cancel] at h'
      have hspec := h p ⟨b • m, hbm⟩
      have heval (u : M ⟶ coinduced 𝒜 E) :
          coinducedCounit p ⟨u.hom (b • m), map_mem u hbm⟩ = coinducedFn (u.hom m) p b := by
        rw [coinducedCounit_mk, u.hom.map_smul, coinducedFn_smul]
      rw [heval f, heval g] at hspec
      exact hspec
    · exact (coinducedFn_eq_zero_of_mem (map_mem f hm) hqn hb).trans
        (coinducedFn_eq_zero_of_mem (map_mem g hm) hqn hb).symm

/-- Precomposing `coinducedLift` with a graded morphism restricts the generating maps along that
morphism. -/
@[simp]
theorem comp_coinducedLift {L M : GradedModuleCat.{max uA v} 𝒜} (g : L ⟶ M)
    (φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p) :
    g ≫ coinducedLift φ =
      coinducedLift (fun p ↦ (φ p).comp
        ((g.hom.restrictScalars k).restrict (fun _ hx ↦ map_mem g hx))) := by
  apply coinduced_hom_ext
  intro p m
  let gm : M.grading.piece p := ((g.hom.restrictScalars k).restrict (fun _ hx ↦ map_mem g hx)) m
  exact (coinducedCounit_coinducedLift φ p gm).trans
    (coinducedCounit_coinducedLift
      (fun q ↦ (φ q).comp ((g.hom.restrictScalars k).restrict (fun _ hx ↦ map_mem g hx))) p m).symm

/-- **Universal property of the coinduced graded module.** Morphisms from `M` into `coinduced 𝒜 E`
correspond `k`-linearly to families of `k`-linear maps `M_p →ₗ[k] E p`. -/
def coinducedHomEquiv (M : GradedModuleCat.{max uA v} 𝒜) :
    (M ⟶ coinduced 𝒜 E) ≃ₗ[k] (∀ p : ℤ, M.grading.piece p →ₗ[k] E p) where
  toFun f p :=
    (coinducedCounit p).comp ((f.hom.restrictScalars k).restrict (fun _ hx ↦ map_mem f hx))
  invFun := coinducedLift
  left_inv _f := coinduced_hom_ext fun p m ↦ coinducedCounit_coinducedLift _ p m
  right_inv φ := funext fun p ↦ LinearMap.ext fun m ↦ coinducedCounit_coinducedLift φ p m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coinducedHomEquiv_apply (M : GradedModuleCat.{max uA v} 𝒜) (f : M ⟶ coinduced 𝒜 E)
    (p : ℤ) (m : M.grading.piece p) :
    coinducedHomEquiv M f p m = coinducedCounit p ⟨f.hom m, map_mem f m.2⟩ := by
  unfold coinducedHomEquiv
  rfl

@[simp]
theorem coinducedHomEquiv_symm_apply (M : GradedModuleCat.{max uA v} 𝒜)
    (φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p) :
    (coinducedHomEquiv M).symm φ = coinducedLift φ := by
  unfold coinducedHomEquiv
  rfl

/-! ### Injectivity and injective presentations -/

/-- If `φ p : M_p →ₗ[k] E p` is injective in every degree `p`, then `coinducedLift φ` is injective
on the total module. -/
theorem coinducedLift_injective_of_injective {M : GradedModuleCat.{max uA v} 𝒜}
    {φ : ∀ p : ℤ, M.grading.piece p →ₗ[k] E p} (hφ : ∀ p, Function.Injective (φ p)) :
    Function.Injective (coinducedLift φ).hom := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  apply (DirectSum.decomposeAddEquiv M.grading.piece).injective
  rw [map_zero]
  ext p : 1
  rw [DirectSum.zero_apply]
  have hp : φ p (DirectSum.decompose M.grading.piece m p) = 0 := by
    have h1 : coinducedFn ((coinducedLift φ).hom m) p 1 = 0 := by
      rw [hm, coinducedFn_zero]
      rfl
    rw [coinducedFn_coinducedLift, one_smul] at h1
    exact h1
  exact hφ p (hp.trans (map_zero (φ p)).symm)

/-- A coinduced graded module built from `k`-modules satisfying Baer's criterion is an injective
object of `GradedModuleCat 𝒜`, without any universe-smallness restriction on `k`. -/
theorem injective_coinduced_of_baer (hE : ∀ p, Module.Baer k (E p)) :
    Injective (coinduced 𝒜 E) where
  factors {X Y} g f _ := by
    have hf_inj : Function.Injective (Hom.hom f) := (mono_iff_injective f).mp ‹_›
    let res (p : ℤ) : X.grading.piece p →ₗ[k] Y.grading.piece p :=
      ((Hom.hom f).restrictScalars k).restrict (fun _ hx ↦ map_mem f hx)
    have hres (p : ℤ) : Function.Injective (res p) := fun x₁ x₂ h ↦
      Subtype.ext (hf_inj (congrArg Subtype.val h))
    choose ψ hψ using fun p ↦ (hE p).extension_property (res p) (hres p) (coinducedHomEquiv X g p)
    refine ⟨coinducedLift ψ, ?_⟩
    apply coinduced_hom_ext
    intro p x
    rw [comp_coinducedLift, coinducedCounit_coinducedLift]
    exact DFunLike.congr_fun (hψ p) x

/-- A coinduced graded module built from injective `k`-modules is an injective object of
`GradedModuleCat 𝒜` when `k` is `v`-small. -/
instance injective_coinduced [Small.{v} k] [∀ p, Injective (ModuleCat.of k (E p))] :
    Injective (coinduced 𝒜 E) :=
  injective_coinduced_of_baer fun p ↦
    Module.Baer.of_injective (Module.injective_module_of_injective_object k (E p))

end UniversalProperty

section EnoughInjectives

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Every graded `𝒜`-module embeds into an injective coinduced graded module when `k` is small
relative to `max uA v`. -/
theorem enoughInjectives [Small.{max uA v} k] :
    EnoughInjectives (GradedModuleCat.{max uA v} 𝒜) where
  presentation M := by
    let P (p : ℤ) : InjectivePresentation (ModuleCat.of k (M.grading.piece p)) :=
      (EnoughInjectives.presentation (ModuleCat.of k (M.grading.piece p))).some
    let E (p : ℤ) : Type (max uA v) := (P p).J
    have hE (p : ℤ) : Injective (ModuleCat.of k (E p)) := (P p).injective
    let φ (p : ℤ) : M.grading.piece p →ₗ[k] E p := (P p).f.hom
    have hφ (p : ℤ) : Function.Injective (φ p) :=
      have := (P p).mono
      (ModuleCat.mono_iff_injective (P p).f).mp inferInstance
    have : Mono (coinducedLift (𝒜 := 𝒜) (E := E) φ) :=
      (mono_iff_injective _).mpr (coinducedLift_injective_of_injective hφ)
    exact ⟨{ J := coinduced 𝒜 E, f := coinducedLift φ }⟩

/-- When the module universe contains `k` and `A`, `GradedModuleCat` has enough injectives. -/
instance enoughInjectives_max : EnoughInjectives (GradedModuleCat.{max uk uA v} 𝒜) := by
  have : Small.{max uk uA v} k := Small.mk' (Equiv.ulift.{max uA v} (α := k)).symm
  exact enoughInjectives.{uk, uA, max uk v} 𝒜

/-- When `k` is small relative to `A`, `GradedModuleCat.{uA} 𝒜` has enough injectives. This avoids
universe `max` unification when `k` and `A` live in the same universe. -/
instance enoughInjectives_self [Small.{uA} k] : EnoughInjectives (GradedModuleCat.{uA} 𝒜) :=
  enoughInjectives.{uk, uA, uA} 𝒜

end EnoughInjectives

end TauCeti.GradedModuleCat
