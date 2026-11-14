/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Pi
public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Correspondence
import Mathlib.Geometry.Manifold.Algebra.Monoid
import TauCeti.Dynamics.PeriodicPts.Chain
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Discrete cyclic action, fixed points, and periodic orbits of generated maps

A real function `S(q, Q)` on `M × N` generates the cotangent relation
`p = d_q S(q, Q)`, `P = -d_Q S(q, Q)` parametrized by `TauCeti.CotangentBundle.generatingSource`
and `TauCeti.CotangentBundle.generatingTarget`; when this relation over `W ⊆ M × N` is the graph of
a partial map `φ : U → T*N` (`TauCeti.CotangentBundle.IsGeneratedGraphOn`), the source projection
restricts to a bijection between `W` and `U`.

For a cyclic chain of functions `S i : Q × Q → ℝ`, `i : ZMod N` (`N ≥ 1`), on domains
`W i ⊆ Q × Q`, define on the configuration domain
`cyclicConfigDomain W = {c : ZMod N → Q | ∀ i, (c i, c (i + 1)) ∈ W i}` the **cyclic action**

`cyclicAction S c = ∑ i : ZMod N, S i (c i, c (i + 1))`.

* **Differential and critical equations.** Varying a single vertex `c i` gives
  `d(y ↦ cyclicAction S (update c i y)) = d₁(S i)(c i, c (i + 1)) + d₂(S (i - 1))(c (i - 1), c i)`
  for all `N ≥ 1`, including `N = 1` where the single summand `y ↦ S 0 (y, y)` is differentiated
  along the diagonal (`TauCeti.CotangentBundle.mvfderiv_cyclicAction_update`), and the full
  product differential is the sum of these vertex variations along the coordinate projections
  (`TauCeti.CotangentBundle.mvfderiv_cyclicAction`). For `ModelWithCorners.pi`, a configuration `c`
  is critical (`mvfderiv = 0`) if and only if at every vertex the outgoing covector
  `generatingTarget J (S (i - 1)) (c (i - 1), c i)` of edge `i - 1` equals the incoming covector
  `generatingSource J (S i) (c i, c (i + 1))` of edge `i`
  (`TauCeti.CotangentBundle.mvfderiv_cyclicAction_eq_zero_iff`).
* **Periodic-state and composite fixed-point dictionary.** When `S i` over `W i` generates the
  graph of `φ i`, the cyclic state sequences `z : ZMod N → T*Q` with `φ i (z i) = z (i + 1)`
  correspond bijectively, by their base points `z ↦ fun i ↦ (z i).proj` and
  `c ↦ fun i ↦ generatingSource J (S i) (c i, c (i + 1))`, to the critical configurations of
  `cyclicAction S` in `cyclicConfigDomain W` (`TauCeti.CotangentBundle.periodicEquiv`,
  `TauCeti.CotangentBundle.periodicEquivOfContMDiffOn`,
  `TauCeti.CotangentBundle.exists_equiv_periodic_of_generating`). Composing with
  `TauCeti.periodicChainFixedPointEquiv` yields the bijection with phase points fixed by the
  `N`-fold composite `Φ (N - 1) ∘ ⋯ ∘ Φ 0` whose intermediate states all lie in the domains `U i`
  (`TauCeti.CotangentBundle.compositeFixedPointEquiv`,
  `TauCeti.CotangentBundle.foldl_compositeFixedPointEquiv_symm_coe`,
  `TauCeti.CotangentBundle.compositeFixedPointEquiv_symm_shift`). Neither finite dimension, nor
  boundarylessness, nor symplecticity of the maps is used.
* **Iterates, cyclic shifts, and fixed points.** Taking equal summands `S i = s` gives the
  correspondence between critical points of `∑ i : ZMod N, s (c i, c (i + 1))` and marked
  `N`-periodic phase points (`f^[N] z₀ = z₀` with intermediate iterates in `u`,
  `TauCeti.CotangentBundle.iterateFixedPointEquiv`). Shifting indices by `k : ZMod N` preserves the
  configuration domain, leaves the cyclic action invariant, preserves criticality, and advances the
  marked initial state along the orbit to `f^[k.val] z₀`
  (`TauCeti.CotangentBundle.iterate_iterateFixedPointEquiv_symm_coe`,
  `TauCeti.CotangentBundle.iterateFixedPointEquiv_symm_shift`). Specializing to `N = 1` recovers
  the bijection between fixed points of `φ` and critical points of the diagonal restriction
  `q ↦ s (q, q)` on `{q | (q, q) ∈ w}`, where `d(q ↦ s (q, q)) = d₁s(q, q) + d₂s(q, q)`
  (`TauCeti.CotangentBundle.fixedPointEquiv`, Cannas da Silva, Proposition 5.1).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.1, Proposition 5.1.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989, §48.
* C. Golé, *Symplectic Twist Maps: Global Variational Techniques*, World Scientific, 2001,
  Chapter 2.
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti.CotangentBundle

/-! ### Cyclic configuration domain and discrete cyclic action -/

section ConfigDomain

variable {Q : Type*}

/-- The **cyclic configuration domain** of edge domains `W : ZMod N → Set (Q × Q)`: the cyclic
sequences `c : ZMod N → Q` whose every consecutive pair `(c i, c (i + 1))` belongs to `W i`. -/
def cyclicConfigDomain {N : ℕ} (W : ZMod N → Set (Q × Q)) : Set (ZMod N → Q) :=
  {c | ∀ i, (c i, c (i + 1)) ∈ W i}

/-- Explicit set-builder form of `cyclicConfigDomain`. -/
theorem cyclicConfigDomain_def {N : ℕ} (W : ZMod N → Set (Q × Q)) :
    cyclicConfigDomain W = {c | ∀ i, (c i, c (i + 1)) ∈ W i} :=
  (rfl)

/-- A cyclic sequence belongs to `cyclicConfigDomain W` iff every consecutive pair
`(c i, c (i + 1))` belongs to `W i`. -/
@[simp]
theorem mem_cyclicConfigDomain {N : ℕ} {W : ZMod N → Set (Q × Q)} {c : ZMod N → Q} :
    c ∈ cyclicConfigDomain W ↔ ∀ i, (c i, c (i + 1)) ∈ W i :=
  .rfl

/-- `cyclicConfigDomain` is monotone with respect to pointwise inclusion of the edge domains. -/
theorem cyclicConfigDomain_mono {N : ℕ} {W W' : ZMod N → Set (Q × Q)} (h : ∀ i, W i ⊆ W' i) :
    cyclicConfigDomain W ⊆ cyclicConfigDomain W' :=
  fun _ hc i ↦ h i (hc i)

/-- Shifting indices by `k : ZMod N` preserves membership in the shifted configuration domain. -/
theorem mem_cyclicConfigDomain_shift_iff {N : ℕ} {W : ZMod N → Set (Q × Q)} (k : ZMod N)
    (c : ZMod N → Q) :
    (fun i ↦ c (i + k)) ∈ cyclicConfigDomain (fun i ↦ W (i + k)) ↔ c ∈ cyclicConfigDomain W := by
  refine ⟨fun h j ↦ ?_, fun h i ↦ ?_⟩
  · simpa only [sub_add_cancel, add_right_comm _ 1 k] using h (j - k)
  · simpa only [add_right_comm i 1 k] using h (i + k)

/-- The **discrete cyclic action** of a chain of functions `S : ZMod N → Q × Q → ℝ`:
`cyclicAction S c = ∑ i : ZMod N, S i (c i, c (i + 1))`. -/
def cyclicAction {N : ℕ} [NeZero N] (S : ZMod N → Q × Q → ℝ) (c : ZMod N → Q) : ℝ :=
  ∑ i : ZMod N, S i (c i, c (i + 1))

/-- Explicit finite-sum form of `cyclicAction`. -/
theorem cyclicAction_def {N : ℕ} [NeZero N] (S : ZMod N → Q × Q → ℝ) (c : ZMod N → Q) :
    cyclicAction S c = ∑ i : ZMod N, S i (c i, c (i + 1)) :=
  (rfl)

/-- The cyclic action of the zero chain vanishes identically. -/
@[simp]
theorem cyclicAction_zero {N : ℕ} [NeZero N] :
    cyclicAction (0 : ZMod N → Q × Q → ℝ) = 0 := by
  ext c
  simp [cyclicAction_def]

/-- `cyclicAction` is additive in the chain of generators. -/
theorem cyclicAction_add {N : ℕ} [NeZero N] (S T : ZMod N → Q × Q → ℝ) :
    cyclicAction (S + T) = cyclicAction S + cyclicAction T := by
  ext c
  simp [cyclicAction_def, Finset.sum_add_distrib]

/-- Negating every generator negates `cyclicAction`. -/
@[simp]
theorem cyclicAction_neg {N : ℕ} [NeZero N] (S : ZMod N → Q × Q → ℝ) :
    cyclicAction (-S) = -cyclicAction S := by
  ext c
  simp [cyclicAction_def, Finset.sum_neg_distrib]

/-- Shifting both the chain of generators and the configuration by `k : ZMod N` leaves
`cyclicAction` invariant. -/
theorem cyclicAction_shift {N : ℕ} [NeZero N] {S : ZMod N → Q × Q → ℝ} (k : ZMod N)
    (c : ZMod N → Q) :
    cyclicAction (fun i ↦ S (i + k)) (fun i ↦ c (i + k)) = cyclicAction S c := by
  simp only [cyclicAction_def, add_right_comm _ 1 k]
  exact Equiv.sum_comp (Equiv.addRight k) fun j ↦ S j (c j, c (j + 1))

/-- For equal summands, cyclic index shifts leave `cyclicAction` invariant. -/
@[simp]
theorem cyclicAction_const_shift {N : ℕ} [NeZero N] {s : Q × Q → ℝ} (k : ZMod N)
    (c : ZMod N → Q) :
    cyclicAction (fun _ : ZMod N ↦ s) (fun i ↦ c (i + k)) =
      cyclicAction (fun _ : ZMod N ↦ s) c :=
  cyclicAction_shift (S := fun _ ↦ s) k c

end ConfigDomain

section CyclicAction

variable {F K Q : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K} [TopologicalSpace Q] [ChartedSpace K Q]

/-- For `N ≥ 1`, if every edge domain `W i` is open in `Q × Q`, then `cyclicConfigDomain W` is open
in `ZMod N → Q`. -/
theorem isOpen_cyclicConfigDomain {N : ℕ} [NeZero N] {W : ZMod N → Set (Q × Q)}
    (hW : ∀ i, IsOpen (W i)) : IsOpen (cyclicConfigDomain W) := by
  have heq : cyclicConfigDomain W =
      ⋂ i : ZMod N, (fun c : ZMod N → Q ↦ (c i, c (i + 1))) ⁻¹' W i := by
    ext c
    simp
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦
    (hW i).preimage ((continuous_apply i).prodMk (continuous_apply (i + 1)))

variable {N : ℕ} [NeZero N] {S : ZMod N → Q × Q → ℝ} {W : ZMod N → Set (Q × Q)}

/-- If each `S i` is `C^n` on `W i`, then `cyclicAction S` is `C^n` on `cyclicConfigDomain W` for
the product model `ModelWithCorners.pi`. -/
theorem contMDiffOn_cyclicAction {n : WithTop ℕ∞}
    (hS : ∀ i, ContMDiffOn (J.prod J) 𝓘(ℝ) n (S i) (W i)) :
    ContMDiffOn (ModelWithCorners.pi fun _ : ZMod N ↦ J) 𝓘(ℝ) n (cyclicAction S)
      (cyclicConfigDomain W) :=
  contMDiffOn_finsetSum fun i _ ↦ (hS i).comp (contMDiffOn_apply.prodMk contMDiffOn_apply)
    fun _ hc ↦ hc i

/-- If each `S i` is differentiable at `(c i, c (i + 1))`, then `cyclicAction S` is differentiable
at `c` for the product model `ModelWithCorners.pi`. -/
theorem mdifferentiableAt_cyclicAction {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    MDifferentiableAt (ModelWithCorners.pi fun _ : ZMod N ↦ J) 𝓘(ℝ) (cyclicAction S) c := by
  have hsum : MDifferentiableAt (ModelWithCorners.pi fun _ : ZMod N ↦ J) 𝓘(ℝ)
      (∑ i ∈ Finset.univ, fun c' : ZMod N → Q ↦ S i (c' i, c' (i + 1))) c :=
    MDifferentiableAt.sum fun i _ ↦
      (hS i).comp c (mdifferentiableAt_apply.prodMk mdifferentiableAt_apply)
  exact hsum.congr_of_eventuallyEq <| .of_forall fun c' ↦ by simp [cyclicAction_def]

/-! ### Partial differentials and critical-point equations of the cyclic action -/

private theorem mdifferentiableAt_update_apply {ι : Type*} [DecidableEq ι] (c : ι → Q) (i k : ι) :
    MDifferentiableAt J J (fun y ↦ update c i y k) (c i) := by
  rcases eq_or_ne k i with rfl | hk
  · rw [show (fun y ↦ update c k y k) = id from funext fun y ↦ update_self k y c]
    exact mdifferentiableAt_id
  · simpa only [update_of_ne hk] using mdifferentiableAt_const

private theorem comp_mfderiv_eq_of_eq_id {x : Q} (g : Q → ℝ) (f : Q → Q) (hf : f = id) :
    (mvfderiv J g (f x)).comp (mfderiv J J f x) = mvfderiv J g x := by
  subst hf
  simp only [id_eq, mfderiv_id, ContinuousLinearMap.comp_id]

private theorem comp_mfderiv_eq_zero_of_eq_const {x q : Q} (g : Q → ℝ) (f : Q → Q)
    (hf : f = fun _ ↦ q) :
    (mvfderiv J g (f x)).comp (mfderiv J J f x) = 0 := by
  subst hf
  simp only [mfderiv_const, ContinuousLinearMap.comp_zero]

private theorem comp_mfderiv_update_apply {ι : Type*} [DecidableEq ι] (c : ι → Q) (i k : ι)
    (g : Q → ℝ) :
    (mvfderiv J g (update c i (c i) k)).comp (mfderiv J J (fun y ↦ update c i y k) (c i)) =
      if k = i then mvfderiv J g (c i) else 0 := by
  rcases eq_or_ne k i with rfl | hk
  · simp only [↓reduceIte]
    exact comp_mfderiv_eq_of_eq_id g (fun y ↦ update c k y k) (funext fun y ↦ update_self k y c)
  · simp only [hk, ↓reduceIte]
    exact comp_mfderiv_eq_zero_of_eq_const g (fun y ↦ update c i y k)
      (funext fun y ↦ update_of_ne hk y c)

private theorem mdifferentiableAt_and_mvfderiv_comp_prodMk_update {ι : Type*} [DecidableEq ι]
    {c : ι → Q} {h : Q × Q → ℝ} (i a b : ι)
    (hh : a = i ∨ b = i → MDifferentiableAt (J.prod J) 𝓘(ℝ) h (c a, c b)) :
    MDifferentiableAt J 𝓘(ℝ) (fun y ↦ h (update c i y a, update c i y b)) (c i) ∧
      mvfderiv J (fun y ↦ h (update c i y a, update c i y b)) (c i) =
        (if a = i then mvfderiv J (fun x ↦ h (x, c b)) (c i) else 0) +
          (if b = i then mvfderiv J (fun y ↦ h (c a, y)) (c i) else 0) := by
  by_cases hab : a = i ∨ b = i
  · have hh' : MDifferentiableAt (J.prod J) 𝓘(ℝ) h (update c i (c i) a, update c i (c i) b) := by
      simpa only [update_eq_self] using hh hab
    have ha := mdifferentiableAt_update_apply (J := J) c i a
    have hb := mdifferentiableAt_update_apply (J := J) c i b
    refine ⟨hh'.comp (c i) (ha.prodMk hb), ?_⟩
    rw [hh'.mvfderiv_comp_prodMk ha hb, comp_mfderiv_update_apply, comp_mfderiv_update_apply]
    simp only [update_eq_self]
  · obtain ⟨ha, hb⟩ := not_or.1 hab
    simp only [update_of_ne ha, update_of_ne hb, ha, hb, ↓reduceIte, add_zero]
    exact ⟨mdifferentiableAt_const, mvfderiv_const _⟩

/-- **Vertex variation differential of the cyclic action.** Varying a single vertex `c i` while
holding the remaining vertices fixed differentiates `S i` in its first slot and `S (i - 1)` in its
second slot; for `N = 1` both terms come from differentiating `y ↦ S 0 (y, y)` along the
diagonal. -/
theorem mvfderiv_cyclicAction_update {c : ZMod N → Q} (i : ZMod N)
    (hSi : MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    (hSi' : MDifferentiableAt (J.prod J) 𝓘(ℝ) (S (i - 1)) (c (i - 1), c i)) :
    mvfderiv J (fun y ↦ cyclicAction S (update c i y)) (c i) =
      mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) +
        mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i) := by
  have hterm (j : ZMod N) :=
    mdifferentiableAt_and_mvfderiv_comp_prodMk_update (c := c) (h := S j) i j (j + 1) <| by
      rintro (rfl | hj1)
      · exact hSi
      · obtain rfl := eq_sub_of_add_eq hj1
        simpa only [sub_add_cancel] using hSi'
  simp only [cyclicAction_def]
  rw [TauCeti.mvfderiv_fun_sum fun j _ ↦ (hterm j).1]
  calc ∑ j : ZMod N, mvfderiv J (fun y ↦ S j (update c i y j, update c i y (j + 1))) (c i)
      = ∑ j : ZMod N,
          ((if j = i then mvfderiv J (fun x ↦ S j (x, c (j + 1))) (c i) else 0) +
            (if j = i - 1 then mvfderiv J (fun y ↦ S j (c j, y)) (c i) else 0)) :=
        Finset.sum_congr rfl fun j _ ↦ by
          simpa only [← eq_sub_iff_add_eq] using (hterm j).2
    _ = mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) +
          mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp

/-- **First-variation formula for the cyclic action.** On the product manifold `ZMod N → Q`, the
differential of `cyclicAction S` at `c` decomposes into the sum of vertex partial differentials
`(d₁(S i)(c i, c (i + 1)) + d₂(S (i - 1))(c (i - 1), c i)) ∘ d(eval i)`. -/
theorem mvfderiv_cyclicAction {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c =
      ∑ i : ZMod N,
        (mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) +
          mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i)).comp
            (mfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) J (fun z ↦ z i) c) := by
  rw [(mdifferentiableAt_cyclicAction hS).mvfderiv_pi_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [mvfderiv_cyclicAction_update i (hS i) (by simpa only [sub_add_cancel] using hS (i - 1))]

variable (J) in
/-- **Critical-point equations of the cyclic action (partial-differential form).** A configuration
`c : ZMod N → Q` is critical for `cyclicAction S` if and only if
`-d₂(S (i - 1))(c (i - 1), c i) = d₁(S i)(c i, c (i + 1))` at every vertex `i`. -/
theorem mvfderiv_cyclicAction_eq_zero_iff_forall_neg_mvfderiv_eq {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0 ↔
      ∀ i : ZMod N,
        -mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i) =
          mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) := by
  rw [(mdifferentiableAt_cyclicAction hS).mvfderiv_pi_eq_zero_iff]
  refine forall_congr' fun i ↦ ?_
  rw [mvfderiv_cyclicAction_update i (hS i) (by simpa only [sub_add_cancel] using hS (i - 1)),
    neg_eq_iff_add_eq_zero, add_comm]

variable (J) in
/-- **Critical-point equations of the cyclic action (covector matching form).** A configuration
`c : ZMod N → Q` is a critical point of `cyclicAction S` if and only if at every vertex `i` the
outgoing covector `generatingTarget J (S (i - 1)) (c (i - 1), c i)` of edge `i - 1` equals the
incoming covector `generatingSource J (S i) (c i, c (i + 1))` of edge `i`. -/
theorem mvfderiv_cyclicAction_eq_zero_iff {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0 ↔
      ∀ i : ZMod N,
        generatingTarget J (S (i - 1)) (c (i - 1), c i) =
          generatingSource J (S i) (c i, c (i + 1)) := by
  rw [(mdifferentiableAt_cyclicAction hS).mvfderiv_pi_eq_zero_iff]
  refine forall_congr' fun i ↦ ?_
  have hSi' : MDifferentiableAt (J.prod J) 𝓘(ℝ) (S (i - 1)) (c (i - 1), c i) := by
    simpa only [sub_add_cancel] using hS (i - 1)
  have h₁ : MDifferentiableAt J 𝓘(ℝ) (fun y ↦ S (i - 1) (c (i - 1), y)) (c i) :=
    hSi'.comp_of_eq (c i) (mdifferentiableAt_const.prodMk mdifferentiableAt_id) rfl
  have h₂ : MDifferentiableAt J 𝓘(ℝ) (fun x ↦ S i (x, c (i + 1))) (c i) :=
    (hS i).comp_of_eq (c i) (mdifferentiableAt_id.prodMk mdifferentiableAt_const) rfl
  rw [generatingTarget_eq_generatingSource_iff h₁ h₂, mvfderiv_fun_add h₁ h₂,
    mvfderiv_cyclicAction_update i (hS i) hSi', add_comm]

/-- Reversing the sign of every generator negates the differential of `cyclicAction` and preserves
its critical configurations. -/
theorem mvfderiv_cyclicAction_neg_eq_zero_iff (c : ZMod N → Q) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (-S)) c = 0 ↔
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0 := by
  rw [cyclicAction_neg, mvfderiv_neg, neg_eq_zero]

/-- Shifting both `S` and `c` by `k : ZMod N` preserves criticality of `cyclicAction`. -/
theorem mvfderiv_cyclicAction_shift_eq_zero_iff (k : ZMod N) {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J)
        (cyclicAction (fun i ↦ S (i + k))) (fun i ↦ c (i + k)) = 0 ↔
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0 := by
  have hS' : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S (i + k))
      (c (i + k), c (i + 1 + k)) := fun i ↦ by
    simpa only [add_right_comm i 1 k] using hS (i + k)
  rw [mvfderiv_cyclicAction_eq_zero_iff J hS', mvfderiv_cyclicAction_eq_zero_iff J hS]
  refine ⟨fun h j ↦ ?_, fun h i ↦ ?_⟩
  · have hj := h (j - k)
    simpa only [sub_add_cancel, sub_right_comm _ k 1, add_right_comm _ 1 k] using hj
  · have hi := h (i + k)
    simpa only [add_sub_right_comm, add_right_comm i 1 k] using hi

omit [NeZero N] in
/-- Shifting edge domains and generators by `k : ZMod N` preserves edgewise differentiability on
`cyclicConfigDomain`. -/
theorem mdifferentiableAt_cyclicConfigDomain_shift (k : ZMod N)
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    ∀ c ∈ cyclicConfigDomain (fun i ↦ W (i + k)), ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S (i + k)) (c i, c (i + 1)) := by
  intro c hc i
  have hc' : (fun j ↦ c (j - k)) ∈ cyclicConfigDomain W := fun j ↦ by
    simpa only [sub_add_cancel, add_sub_right_comm] using hc (j - k)
  simpa only [add_sub_cancel_right, add_right_comm i k 1] using hSd _ hc' (i + k)

/-! ### The periodic-state / critical-configuration dictionary -/

/-- **Chain dictionary between periodic state sequences and critical configurations.** Let `S i`
over `W i` generate the graph of `φ i : U i → T*Q` for each `i : ZMod N`, and assume `S i` is
differentiable at the edges of every configuration in `cyclicConfigDomain W`. Then cyclic state
sequences `z : ZMod N → T*Q` satisfying `φ i (z i) = z (i + 1)` correspond bijectively to critical
points of `cyclicAction S` in `cyclicConfigDomain W`, via `z ↦ fun i ↦ (z i).proj` and
`c ↦ fun i ↦ generatingSource J (S i) (c i, c (i + 1))`. -/
def periodicEquiv
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i)) :
    {z : ZMod N → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ U i, φ i ⟨z i, h⟩ = z (i + 1)} ≃
      {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
        mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0} where
  toFun z := ⟨fun i ↦ (z.1 i).proj, by
    have hmem : (fun i ↦ (z.1 i).proj) ∈ cyclicConfigDomain W := fun i ↦ by
      obtain ⟨hzi, hstep⟩ := z.2 i
      simpa only [← hstep] using (hφ i).proj_mem ⟨z.1 i, hzi⟩
    refine ⟨hmem, (mvfderiv_cyclicAction_eq_zero_iff J (hSd _ hmem)).2 fun i ↦ ?_⟩
    obtain ⟨hzi, hstep⟩ := z.2 i
    obtain ⟨hzprev, hstep_prev⟩ := z.2 (i - 1)
    rw [sub_add_cancel] at hstep_prev
    have hsrc : z.1 i = generatingSource J (S i) ((z.1 i).proj, (z.1 (i + 1)).proj) := by
      simpa only [← hstep] using (hφ i).eq_generatingSource ⟨z.1 i, hzi⟩
    have htgt : z.1 i = generatingTarget J (S (i - 1)) ((z.1 (i - 1)).proj, (z.1 i).proj) := by
      rw [← hstep_prev]
      exact (hφ (i - 1)).apply_eq_generatingTarget ⟨z.1 (i - 1), hzprev⟩
    exact htgt.symm.trans hsrc⟩
  invFun c := ⟨fun i ↦ generatingSource J (S i) (c.1 i, c.1 (i + 1)), fun i ↦ by
    refine ⟨(hφ i).generatingSource_mem (c.2.1 i), ?_⟩
    rw [(hφ i).apply_generatingSource (c.2.1 i)]
    have hmatch := (mvfderiv_cyclicAction_eq_zero_iff J (hSd c.1 c.2.1)).1 c.2.2 (i + 1)
    simpa only [add_sub_cancel_right] using hmatch⟩
  left_inv z := Subtype.ext <| funext fun i ↦ by
    obtain ⟨hzi, hstep⟩ := z.2 i
    simpa only [← hstep] using ((hφ i).eq_generatingSource ⟨z.1 i, hzi⟩).symm
  right_inv c := Subtype.ext <| funext fun i ↦ proj_generatingSource (c.1 i, c.1 (i + 1))

/-- `periodicEquiv` sends a cyclic state sequence `z` to its sequence of base points
`i ↦ (z i).proj`. -/
@[simp]
theorem periodicEquiv_apply_coe
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i))
    (z : {z : ZMod N → CotangentBundle J Q //
      ∀ i, ∃ h : z i ∈ U i, φ i ⟨z i, h⟩ = z (i + 1)}) (i : ZMod N) :
    (periodicEquiv hSd hφ z : ZMod N → Q) i = (z.1 i).proj :=
  (rfl)

/-- `periodicEquiv.symm` reconstructs the `i`-th phase state from a critical configuration `c` as
`generatingSource J (S i) (c i, c (i + 1))`. -/
@[simp]
theorem periodicEquiv_symm_apply_coe
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0})
    (i : ZMod N) :
    ((periodicEquiv hSd hφ).symm c : ZMod N → CotangentBundle J Q) i =
      generatingSource J (S i) (c.1 i, c.1 (i + 1)) :=
  (rfl)

/-- Smooth open-domain specialization of `periodicEquiv` when each `S i` is `C^n` (`1 ≤ n`) on an
open domain `W i ⊆ Q × Q`. -/
def periodicEquivOfContMDiffOn {n : WithTop ℕ∞} (hW : ∀ i, IsOpen (W i))
    (hS : ∀ i, ContMDiffOn (J.prod J) 𝓘(ℝ) n (S i) (W i)) (hn : 1 ≤ n)
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i)) :
    {z : ZMod N → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ U i, φ i ⟨z i, h⟩ = z (i + 1)} ≃
      {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
        mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0} :=
  periodicEquiv
    (fun _ hc i ↦ ((hS i _ (hc i)).contMDiffAt ((hW i).mem_nhds (hc i))).mdifferentiableAt
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))) hφ

/-- `periodicEquivOfContMDiffOn` sends a cyclic state sequence `z` to its sequence of base points
`i ↦ (z i).proj`. -/
@[simp]
theorem periodicEquivOfContMDiffOn_apply_coe {n : WithTop ℕ∞} (hW : ∀ i, IsOpen (W i))
    (hS : ∀ i, ContMDiffOn (J.prod J) 𝓘(ℝ) n (S i) (W i)) (hn : 1 ≤ n)
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i))
    (z : {z : ZMod N → CotangentBundle J Q //
      ∀ i, ∃ h : z i ∈ U i, φ i ⟨z i, h⟩ = z (i + 1)}) (i : ZMod N) :
    (periodicEquivOfContMDiffOn hW hS hn hφ z : ZMod N → Q) i = (z.1 i).proj :=
  (rfl)

/-- `periodicEquivOfContMDiffOn.symm` reconstructs the `i`-th phase state from a critical
configuration `c` as `generatingSource J (S i) (c i, c (i + 1))`. -/
@[simp]
theorem periodicEquivOfContMDiffOn_symm_apply_coe {n : WithTop ℕ∞} (hW : ∀ i, IsOpen (W i))
    (hS : ∀ i, ContMDiffOn (J.prod J) 𝓘(ℝ) n (S i) (W i)) (hn : 1 ≤ n)
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0})
    (i : ZMod N) :
    ((periodicEquivOfContMDiffOn hW hS hn hφ).symm c : ZMod N → CotangentBundle J Q) i =
      generatingSource J (S i) (c.1 i, c.1 (i + 1)) :=
  (rfl)

/-- **Periodic states and critical points of the cyclic action** (for `N = 1`, Cannas da Silva,
Prop. 5.1, p. 29): let `S i` be smooth on open sets `W i ⊆ Q × Q`, for `i : ZMod N`, and let the
relation `p = d_q S i (q, Q)`, `P = -d_Q S i (q, Q)` over `W i` be the graph of `φ i`. The cyclic
sequences of states `z i` with `φ i (z i) = z (i + 1)` correspond, by their base points, to the
critical points of `A (q) = ∑ i, S i (q i, q (i + 1))` on the configurations whose every edge
`(q i, q (i + 1))` lies in `W i`. -/
theorem exists_equiv_periodic_of_generating [IsManifold J 1 Q]
    (hW : ∀ i, IsOpen (W i)) (hS : ∀ i, ContMDiffOn (J.prod J) 𝓘(ℝ) ∞ (S i) (W i))
    {U V : ZMod N → TopologicalSpace.Opens (CotangentBundle J Q)}
    (φ : ∀ i, U i ≃ₘ⟮J.prod 𝓘(ℝ, F →L[ℝ] ℝ), J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯ V i)
    (hφ : ∀ i (z : U i),
      ((z : CotangentBundle J Q).1, (φ i z : CotangentBundle J Q).1) ∈ W i ∧
        (z : CotangentBundle J Q).2 =
          mvfderiv J (fun q ↦ S i (q, (φ i z : CotangentBundle J Q).1))
            (z : CotangentBundle J Q).1 ∧
        (φ i z : CotangentBundle J Q).2 =
          -mvfderiv J (fun y ↦ S i ((z : CotangentBundle J Q).1, y))
            (φ i z : CotangentBundle J Q).1)
    (hW' : ∀ i, ∀ x ∈ W i, ∃ z : U i,
      (z : CotangentBundle J Q) = TotalSpace.mk' (F →L[ℝ] ℝ) x.1
        (mvfderiv J (fun q ↦ S i (q, x.2)) x.1) ∧ (φ i z : CotangentBundle J Q).1 = x.2) :
    ∃ e : {z : ZMod N → CotangentBundle J Q //
          ∀ i, ∃ h : z i ∈ U i, (φ i ⟨z i, h⟩ : CotangentBundle J Q) = z (i + 1)} ≃
        {q : ZMod N → Q // (∀ i, (q i, q (i + 1)) ∈ W i) ∧
          mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J)
            (fun c : ZMod N → Q ↦ ∑ i, S i (c i, c (i + 1))) q = 0},
      ∀ z i, (e z : ZMod N → Q) i = (z.1 i).1 := by
  have hφ' : ∀ i, IsGeneratedGraphOn J J (S i) (W i)
      (fun z : U i ↦ (φ i z : CotangentBundle J Q)) :=
    fun i ↦ IsGeneratedGraphOn.of_covector (hφ i) fun x hx ↦ by
      obtain ⟨z, hz, hproj⟩ := hW' i x hx
      exact ⟨z, congrArg TotalSpace.proj hz, hproj⟩
  exact ⟨periodicEquivOfContMDiffOn hW hS (by simp) hφ',
    periodicEquivOfContMDiffOn_apply_coe hW hS (by simp) hφ'⟩

/-! ### Fixed points of composites, finite iterates, and cyclic shifts -/

/-- **Composite fixed-point dictionary.** For maps `Φ : ZMod N → T*Q → T*Q` whose restrictions to
`U i` are generated by `S i` over `W i`, the phase points `z₀` fixed by the `N`-fold composite
`Φ (N - 1) ∘ ⋯ ∘ Φ 0` whose intermediate states `Fin.foldl k (fun z j ↦ Φ j z) z₀` (`k < N`) all
belong to `U k` correspond bijectively to the critical configurations of `cyclicAction S` in
`cyclicConfigDomain W`, sending `z₀` to its base points along the chain and `c` to
`generatingSource J (S 0) (c 0, c 1)`. -/
def compositeFixedPointEquiv
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)}
    {Φ : ZMod N → CotangentBundle J Q → CotangentBundle J Q}
    (hΦ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) ((U i).domRestrict (Φ i))) :
    {z₀ : CotangentBundle J Q //
        (∀ k < N, Fin.foldl k (fun z j ↦ Φ (j : ZMod N) z) z₀ ∈ U k) ∧
          Fin.foldl N (fun z j ↦ Φ (j : ZMod N) z) z₀ = z₀} ≃
      {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
        mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0} :=
  ((periodicChainFixedPointEquiv U Φ).trans (Equiv.subtypeEquivRight fun _ ↦ by simp)).trans
    (periodicEquiv hSd hΦ)

/-- `compositeFixedPointEquiv` sends a fixed point `z₀` of the composite chain to the base points
of its partial composites along the chain. -/
@[simp]
theorem compositeFixedPointEquiv_apply_coe
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)}
    {Φ : ZMod N → CotangentBundle J Q → CotangentBundle J Q}
    (hΦ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) ((U i).domRestrict (Φ i)))
    (z₀ : {z₀ : CotangentBundle J Q //
      (∀ k < N, Fin.foldl k (fun z j ↦ Φ (j : ZMod N) z) z₀ ∈ U k) ∧
        Fin.foldl N (fun z j ↦ Φ (j : ZMod N) z) z₀ = z₀}) (i : ZMod N) :
    (compositeFixedPointEquiv hSd hΦ z₀ : ZMod N → Q) i =
      (Fin.foldl i.val (fun z j ↦ Φ (j : ZMod N) z) z₀.1).proj := by
  rw [compositeFixedPointEquiv, Equiv.trans_apply, periodicEquiv_apply_coe, Equiv.trans_apply,
    Equiv.subtypeEquivRight_apply_coe, periodicChainFixedPointEquiv_apply_coe]

/-- `compositeFixedPointEquiv.symm` reconstructs the initial phase state `z₀` from a critical
configuration `c` as `generatingSource J (S 0) (c 0, c 1)`. -/
@[simp]
theorem compositeFixedPointEquiv_symm_apply_coe
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)}
    {Φ : ZMod N → CotangentBundle J Q → CotangentBundle J Q}
    (hΦ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) ((U i).domRestrict (Φ i)))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0}) :
    ((compositeFixedPointEquiv hSd hΦ).symm c : CotangentBundle J Q) =
      generatingSource J (S 0) (c.1 0, c.1 1) := by
  rw [compositeFixedPointEquiv, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    periodicChainFixedPointEquiv_symm_apply_coe, Equiv.subtypeEquivRight_symm_apply_coe,
    periodicEquiv_symm_apply_coe, zero_add]

/-- Folding `m` steps of `Φ` from the initial phase state reconstructed from a critical
configuration `c` yields the source covector `generatingSource J (S m) (c m, c (m + 1))` at residue
`(m : ZMod N)`. -/
theorem foldl_compositeFixedPointEquiv_symm_coe
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)}
    {Φ : ZMod N → CotangentBundle J Q → CotangentBundle J Q}
    (hΦ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) ((U i).domRestrict (Φ i)))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0}) (m : ℕ) :
    Fin.foldl m (fun z j ↦ Φ (j : ZMod N) z)
        ((compositeFixedPointEquiv hSd hΦ).symm c : CotangentBundle J Q) =
      generatingSource J (S m) (c.1 m, c.1 (m + 1)) := by
  rw [compositeFixedPointEquiv, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    foldl_periodicChainFixedPointEquiv_symm_coe, Equiv.subtypeEquivRight_symm_apply_coe,
    periodicEquiv_symm_apply_coe]

/-- **Shifting a critical configuration shifts the composite chain and advances the initial
state.** Shifting `S`, `W`, `U`, `Φ`, and `c` by `k : ZMod N` advances the corresponding initial
state `z₀ = (compositeFixedPointEquiv hSd hΦ).symm c` to its `k.val`-step partial composite along
the chain. -/
theorem compositeFixedPointEquiv_symm_shift
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)}
    {Φ : ZMod N → CotangentBundle J Q → CotangentBundle J Q}
    (hΦ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) ((U i).domRestrict (Φ i))) (k : ZMod N)
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0}) :
    ((compositeFixedPointEquiv (mdifferentiableAt_cyclicConfigDomain_shift k hSd)
      (fun i ↦ hΦ (i + k))).symm
      ⟨fun i ↦ c.1 (i + k), (mem_cyclicConfigDomain_shift_iff k c.1).2 c.2.1,
        (mvfderiv_cyclicAction_shift_eq_zero_iff k (hSd c.1 c.2.1)).2 c.2.2⟩ :
        CotangentBundle J Q) =
      Fin.foldl k.val (fun z j ↦ Φ (j : ZMod N) z)
        ((compositeFixedPointEquiv hSd hΦ).symm c : CotangentBundle J Q) := by
  rw [compositeFixedPointEquiv_symm_apply_coe, foldl_compositeFixedPointEquiv_symm_coe,
    ZMod.natCast_zmod_val]
  simp only [zero_add, add_comm 1 k]

section Iterates

variable {s : Q × Q → ℝ} {w : Set (Q × Q)} {u : Set (CotangentBundle J Q)}
  {f : CotangentBundle J Q → CotangentBundle J Q}

/-- **Marked `N`-periodic points and equal-summand cyclic action.** When `s` over `w` generates the
graph of `u.domRestrict f`, the marked phase points fixed by the `N`-th iterate `f^[N]` whose
intermediate iterates `f^[k] z₀` (`k < N`) all lie in `u` correspond bijectively to the critical
points of `cyclicAction (fun _ ↦ s)` in `cyclicConfigDomain (fun _ ↦ w)`. -/
def iterateFixedPointEquiv
    (hsd : ∀ c ∈ cyclicConfigDomain (fun _ : ZMod N ↦ w), ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) s (c i, c (i + 1)))
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f)) :
    {z₀ : CotangentBundle J Q // (∀ k < N, f^[k] z₀ ∈ u) ∧ f^[N] z₀ = z₀} ≃
      {c : ZMod N → Q // c ∈ cyclicConfigDomain (fun _ ↦ w) ∧
        mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (fun _ ↦ s)) c = 0} :=
  (Equiv.subtypeEquivRight fun z₀ ↦ by simp only [finFoldl_const]).trans
    (compositeFixedPointEquiv hsd fun _ ↦ hf)

/-- `iterateFixedPointEquiv` sends a marked `N`-periodic phase point `z₀` to the base points
`i ↦ (f^[i.val] z₀).proj` of its forward orbit. -/
@[simp]
theorem iterateFixedPointEquiv_apply_coe
    (hsd : ∀ c ∈ cyclicConfigDomain (fun _ ↦ w), ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) s (c i, c (i + 1)))
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f))
    (z₀ : {z₀ : CotangentBundle J Q // (∀ k < N, f^[k] z₀ ∈ u) ∧ f^[N] z₀ = z₀})
    (i : ZMod N) :
    (iterateFixedPointEquiv (N := N) hsd hf z₀ : ZMod N → Q) i = (f^[i.val] z₀.1).proj := by
  rw [iterateFixedPointEquiv, Equiv.trans_apply, compositeFixedPointEquiv_apply_coe,
    Equiv.subtypeEquivRight_apply_coe, finFoldl_const]

/-- `iterateFixedPointEquiv.symm` reconstructs the marked initial state `z₀` from a critical
configuration `c` as `generatingSource J s (c 0, c 1)`. -/
@[simp]
theorem iterateFixedPointEquiv_symm_apply_coe
    (hsd : ∀ c ∈ cyclicConfigDomain (fun _ ↦ w), ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) s (c i, c (i + 1)))
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain (fun _ ↦ w) ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (fun _ ↦ s)) c = 0}) :
    ((iterateFixedPointEquiv (N := N) hsd hf).symm c : CotangentBundle J Q) =
      generatingSource J s (c.1 0, c.1 1) := by
  rw [iterateFixedPointEquiv, Equiv.symm_trans_apply, Equiv.subtypeEquivRight_symm_apply_coe,
    compositeFixedPointEquiv_symm_apply_coe]

/-- Iterating `f` `m` times from the initial periodic state reconstructed from a critical
configuration `c` yields the source covector `generatingSource J s (c m, c (m + 1))` at residue
`(m : ZMod N)`. -/
theorem iterate_iterateFixedPointEquiv_symm_coe
    (hsd : ∀ c ∈ cyclicConfigDomain (fun _ ↦ w), ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) s (c i, c (i + 1)))
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain (fun _ ↦ w) ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (fun _ ↦ s)) c = 0})
    (m : ℕ) :
    f^[m] ((iterateFixedPointEquiv (N := N) hsd hf).symm c : CotangentBundle J Q) =
      generatingSource J s (c.1 m, c.1 (m + 1)) := by
  rw [← finFoldl_const, iterateFixedPointEquiv, Equiv.symm_trans_apply,
    Equiv.subtypeEquivRight_symm_apply_coe]
  exact foldl_compositeFixedPointEquiv_symm_coe (S := fun _ ↦ s) (W := fun _ ↦ w)
    (U := fun _ ↦ u) (Φ := fun _ ↦ f) hsd (fun _ ↦ hf) c m

/-- **A cyclic shift of a critical configuration is the same periodic orbit with a shifted marked
point.** Shifting `c` by `k : ZMod N` advances the corresponding initial periodic state
`z₀ = (iterateFixedPointEquiv hsd hf).symm c` to `f^[k.val] z₀`. -/
theorem iterateFixedPointEquiv_symm_shift
    (hsd : ∀ c ∈ cyclicConfigDomain (fun _ ↦ w), ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) s (c i, c (i + 1)))
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f)) (k : ZMod N)
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain (fun _ ↦ w) ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (fun _ ↦ s)) c = 0}) :
    ((iterateFixedPointEquiv (N := N) hsd hf).symm
      ⟨fun i ↦ c.1 (i + k), (mem_cyclicConfigDomain_shift_iff (W := fun _ ↦ w) k c.1).2 c.2.1,
        (mvfderiv_cyclicAction_shift_eq_zero_iff (S := fun _ ↦ s) k
          (hsd c.1 c.2.1)).2 c.2.2⟩ : CotangentBundle J Q) =
      f^[k.val] ((iterateFixedPointEquiv (N := N) hsd hf).symm c : CotangentBundle J Q) := by
  rw [iterateFixedPointEquiv, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
    Equiv.subtypeEquivRight_symm_apply_coe, Equiv.subtypeEquivRight_symm_apply_coe,
    ← finFoldl_const]
  exact compositeFixedPointEquiv_symm_shift (S := fun _ ↦ s) (W := fun _ ↦ w)
    (U := fun _ ↦ u) (Φ := fun _ ↦ f) hsd (fun _ ↦ hf) k c

end Iterates

/-! ### Fixed points and diagonal restriction (`N = 1`, Cannas da Silva Prop. 5.1) -/

section FixedPoints

variable {s : Q × Q → ℝ} {w : Set (Q × Q)} {u : Set (CotangentBundle J Q)}
  {φ : u → CotangentBundle J Q}

/-- On the diagonal `(q, q)`, the outgoing and incoming covectors of `s` agree if and only if `q`
is a critical point of `x ↦ s (x, x)`. -/
theorem generatingTarget_eq_generatingSource_diag_iff {q : Q}
    (hs : MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q)) :
    generatingTarget J s (q, q) = generatingSource J s (q, q) ↔
      mvfderiv J (fun x ↦ s (x, x)) q = 0 := by
  have h₁ : MDifferentiableAt J 𝓘(ℝ) (fun y ↦ s (q, y)) q :=
    hs.comp_of_eq q (mdifferentiableAt_const.prodMk mdifferentiableAt_id) rfl
  have h₂ : MDifferentiableAt J 𝓘(ℝ) (fun x ↦ s (x, q)) q :=
    hs.comp_of_eq q (mdifferentiableAt_id.prodMk mdifferentiableAt_const) rfl
  rw [generatingTarget_eq_generatingSource_iff h₁ h₂, mvfderiv_fun_add h₁ h₂, add_comm,
    ← hs.mvfderiv_diag]

/-- For `N = 1`, a constant configuration `fun _ : ZMod 1 ↦ q` is critical for `cyclicAction` if
and only if `q` is a critical point of the diagonal function `x ↦ s (x, x)`. -/
theorem mvfderiv_cyclicAction_zmod_one_eq_zero_iff {q : Q}
    (hs : MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q)) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod 1 ↦ J)
        (cyclicAction (fun _ : ZMod 1 ↦ s)) (fun _ ↦ q) = 0 ↔
      mvfderiv J (fun x ↦ s (x, x)) q = 0 := by
  rw [mvfderiv_cyclicAction_eq_zero_iff J fun _ ↦ hs, Unique.forall_iff,
    generatingTarget_eq_generatingSource_diag_iff hs]

/-- **Fixed points and critical points of the diagonal restriction** (Cannas da Silva, Prop. 5.1,
p. 29), derived as the case `N = 1` of `periodicEquiv`: when `s` over `w ⊆ Q × Q` generates the
graph of `φ : u → T*Q` and is differentiable along the diagonal of `w`, the fixed points of `φ`
correspond bijectively to the critical points of `q ↦ s (q, q)` on `{q | (q, q) ∈ w}`, sending `z`
to `z.proj` and `q` to `generatingSource J s (q, q)`. -/
def fixedPointEquiv
    (hsd : ∀ q, (q, q) ∈ w → MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q))
    (hφ : IsGeneratedGraphOn J J s w φ) :
    {z : CotangentBundle J Q // ∃ h : z ∈ u, φ ⟨z, h⟩ = z} ≃
      {q : Q // (q, q) ∈ w ∧ mvfderiv J (fun x ↦ s (x, x)) q = 0} :=
  ({ toFun := fun z ↦ ⟨fun _ : ZMod 1 ↦ z.1, fun _ ↦ z.2⟩
     invFun := fun z ↦ ⟨z.1 0, by
       simpa only [Subsingleton.elim (0 + 1 : ZMod 1) 0] using z.2 0⟩
     left_inv := fun _ ↦ Subtype.ext rfl
     right_inv := fun z ↦ Subtype.ext <| funext fun i ↦ by rw [Subsingleton.elim i 0] } :
    {z : CotangentBundle J Q // ∃ h : z ∈ u, φ ⟨z, h⟩ = z} ≃
      {z : ZMod 1 → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ u, φ ⟨z i, h⟩ = z (i + 1)}).trans <|
  (periodicEquiv (N := 1) (S := fun _ ↦ s) (W := fun _ ↦ w)
    (fun c hc i ↦ by
      have hi : c (i + 1) = c i := congrArg c (Subsingleton.elim _ _)
      exact hi ▸ hsd (c i) (hi ▸ hc i))
    (fun _ ↦ hφ)).trans
  { toFun := fun c ↦ ⟨c.1 0, by
      have h0 : c.1 = fun _ : ZMod 1 ↦ c.1 0 := funext fun i ↦ congrArg c.1 (Subsingleton.elim i 0)
      have hw0 : (c.1 0, c.1 0) ∈ w := by
        simpa only [Subsingleton.elim (0 + 1 : ZMod 1) 0] using c.2.1 0
      refine ⟨hw0, (mvfderiv_cyclicAction_zmod_one_eq_zero_iff (hsd _ hw0)).1 ?_⟩
      exact h0 ▸ c.2.2⟩
    invFun := fun q ↦ ⟨fun _ : ZMod 1 ↦ q.1, ⟨fun _ ↦ q.2.1,
      (mvfderiv_cyclicAction_zmod_one_eq_zero_iff (hsd _ q.2.1)).2 q.2.2⟩⟩
    left_inv := fun c ↦ Subtype.ext <| funext fun i ↦ congrArg c.1 (Subsingleton.elim 0 i)
    right_inv := fun _ ↦ Subtype.ext rfl }

/-- `fixedPointEquiv` sends a fixed point `z` of `φ` to its base point `z.proj`. -/
@[simp]
theorem fixedPointEquiv_apply_coe
    (hsd : ∀ q, (q, q) ∈ w → MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q))
    (hφ : IsGeneratedGraphOn J J s w φ)
    (z : {z : CotangentBundle J Q // ∃ h : z ∈ u, φ ⟨z, h⟩ = z}) :
    (fixedPointEquiv hsd hφ z : Q) = z.1.proj :=
  (rfl)

/-- `fixedPointEquiv.symm` reconstructs a fixed point from a diagonal critical point `q` as
`generatingSource J s (q, q)`. -/
@[simp]
theorem fixedPointEquiv_symm_apply_coe
    (hsd : ∀ q, (q, q) ∈ w → MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q))
    (hφ : IsGeneratedGraphOn J J s w φ)
    (q : {q : Q // (q, q) ∈ w ∧ mvfderiv J (fun x ↦ s (x, x)) q = 0}) :
    ((fixedPointEquiv hsd hφ).symm q : CotangentBundle J Q) =
      generatingSource J s (q.1, q.1) :=
  (rfl)

end FixedPoints

end CyclicAction

end TauCeti.CotangentBundle
