/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TauCeti Contributors
-/
module

public import TauCeti.LinearAlgebra.Trace.HattoriStallings.MonoidExtension

/-!
# Induced Modules for Monoid Extensions

This file constructs the induced module `Ind_{Γ'_+}^{Γ_+}(Q)` for a finite-index subextension
`Γ' ≤ Γ` of a monoid extension `1 → G → Γ → ℤ → 1`, establishes its finite projectivity over
`Λ[G]`, and proves vanishing of centralizer traces outside the degree subgroup `dℤ`, as needed
for Stacks Project, Section 64.15 (Lemma 64.15.6).

## Main definitions

* `TauCeti.MonoidExtension.Subextension E`: a subgroup `Γ' ≤ Γ` whose image under `E.degree` is
  `dℤ` for a positive integer `d = index`.
* `TauCeti.MonoidExtension.Subextension.toExtension`: the induced monoid extension
  `1 → G' → Γ' → ℤ → 1` with `G' = G ∩ Γ'`.
* `TauCeti.MonoidExtension.InducedModule Λ S Q`: the choice-free model of `Ind_{Γ'_+}^{Γ_+}(Q)`
  as `S.kernel`-equivariant functions on the degree strip `0 ≤ deg(x) < S.index`, equipped with
  canonical `Λ[E.monoid]`- and `Λ[G]`-module structures.

## Main results

* `TauCeti.MonoidExtension.InducedModule.finite_projective`: if `G` is finite and `Q` is finite
  projective over `Λ[G']`, then `InducedModule Λ S Q` is finite projective over `Λ[G]`.
* `TauCeti.MonoidExtension.centralizerTrace_inducedModule_eq_zero_of_not_dvd`: if `S.index` does
  not divide `E.degree γ`, then the centralizer trace of `γ` on `InducedModule Λ S Q` vanishes.

## References

* [Stacks Project, Lemma 64.15.6 (Tag 03UA)](https://stacks.math.columbia.edu/tag/03UA)
-/

@[expose] public section

noncomputable section

namespace TauCeti

namespace MonoidExtension

open _root_.MonoidAlgebra

/-! ### Section 1: Finite-index subextensions and the degree strip -/

variable {G Γ : Type*} [Group G] [Group Γ]

/-- A subextension of a monoid extension `E : MonoidExtension G Γ`: a subgroup `subgroup ≤ Γ`
whose image under `E.degree` is `index • ℤ` for a positive natural number `index`. -/
structure Subextension (E : MonoidExtension G Γ) where
  /-- The subgroup `Γ' ≤ Γ`. -/
  subgroup : Subgroup Γ
  /-- The positive index `d = [ℤ : E.degree(Γ')]`. -/
  index : ℕ
  /-- Positivity of `index`. -/
  index_pos : 0 < index
  /-- Every element of `subgroup` has degree divisible by `index`. -/
  dvd_degree : ∀ x ∈ subgroup, (index : ℤ) ∣ E.degree x
  /-- There exists an element of `subgroup` of degree equal to `index`. -/
  exists_degree_eq : ∃ x ∈ subgroup, E.degree x = index

namespace Subextension

variable {E : MonoidExtension G Γ} (S : E.Subextension)

/-- The kernel subgroup `G' = G ∩ Γ'` inside `G`. -/
def kernel : Subgroup G := S.subgroup.comap E.incl

@[simp]
theorem mem_kernel (g : G) : g ∈ S.kernel ↔ E.incl g ∈ S.subgroup := Iff.rfl

/-- The induced monoid extension `1 → S.kernel → S.subgroup → ℤ → 1`, where the degree on
`S.subgroup` is `E.degree / S.index`. -/
def toExtension : MonoidExtension S.kernel S.subgroup where
  incl :=
    { toFun := fun g' ↦ ⟨E.incl g'.1, g'.2⟩
      map_one' := Subtype.ext (map_one E.incl)
      map_mul' := fun g₁ g₂ ↦ Subtype.ext (map_mul E.incl g₁.1 g₂.1) }
  proj :=
    { toFun := fun x ↦ Multiplicative.ofAdd (E.degree x.1 / (S.index : ℤ))
      map_one' := by
        change Multiplicative.ofAdd (E.degree 1 / (S.index : ℤ)) = 1
        rw [E.degree_one, Int.zero_ediv]
        rfl
      map_mul' := fun x y ↦ by
        change Multiplicative.ofAdd (E.degree (x.1 * y.1) / (S.index : ℤ)) =
          Multiplicative.ofAdd (E.degree x.1 / (S.index : ℤ)) *
            Multiplicative.ofAdd (E.degree y.1 / (S.index : ℤ))
        rw [← ofAdd_add, E.degree_mul, Int.add_ediv_of_dvd_left (S.dvd_degree x.1 x.2)] }
  incl_injective := fun g₁ g₂ h ↦ Subtype.ext (E.incl_injective (congrArg Subtype.val h))
  proj_surjective := fun z ↦ by
    obtain ⟨x₁, hx₁, hdeg⟩ := S.exists_degree_eq
    refine ⟨⟨x₁ ^ Multiplicative.toAdd z, zpow_mem hx₁ _⟩, ?_⟩
    change Multiplicative.ofAdd (E.degree (x₁ ^ Multiplicative.toAdd z) / (S.index : ℤ)) = z
    rw [E.degree_zpow, hdeg, Int.mul_ediv_cancel _ (Int.natCast_ne_zero.mpr S.index_pos.ne')]
    exact ofAdd_toAdd z
  ker_proj := by
    ext ⟨x, hx⟩
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk]
    constructor
    · intro hker
      have hdiv : E.degree x / (S.index : ℤ) = 0 := by
        have h1 : Multiplicative.ofAdd (E.degree x / (S.index : ℤ)) = Multiplicative.ofAdd 0 :=
          hker
        exact Multiplicative.ofAdd.injective h1
      obtain ⟨k, hk⟩ := S.dvd_degree x hx
      have hk0 : k = 0 := by
        have hpos : (S.index : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr S.index_pos.ne'
        rw [hk, Int.mul_ediv_cancel_left _ hpos] at hdiv
        exact hdiv
      have hdeg0 : E.degree x = 0 := by rw [hk, hk0, mul_zero]
      obtain ⟨g, hg⟩ := (E.degree_eq_zero_iff x).mp hdeg0
      exact ⟨⟨g, show E.incl g ∈ S.subgroup by rw [hg]; exact hx⟩, Subtype.ext hg⟩
    · rintro ⟨⟨g, hg⟩, hEq⟩
      have hgx : E.incl g = x := congrArg Subtype.val hEq
      change Multiplicative.ofAdd (E.degree x / (S.index : ℤ)) = 1
      rw [← hgx, E.degree_incl, Int.zero_ediv]
      rfl

theorem toExtension_degree (x : S.subgroup) :
    S.toExtension.degree x = E.degree x.1 / (S.index : ℤ) := by
  rw [degree_apply]
  exact toAdd_ofAdd _

theorem degree_eq_index_mul_toExtension_degree (x : S.subgroup) :
    E.degree x.1 = (S.index : ℤ) * S.toExtension.degree x := by
  rw [toExtension_degree, Int.mul_ediv_cancel' (S.dvd_degree x.1 x.2)]

theorem mem_toExtension_monoid_iff (x : S.subgroup) :
    x ∈ S.toExtension.monoid ↔ 0 ≤ E.degree x.1 := by
  rw [S.toExtension.mem_monoid, S.degree_eq_index_mul_toExtension_degree x]
  have hpos : (0 : ℤ) < S.index := Int.natCast_pos.mpr S.index_pos
  constructor
  · intro h
    exact mul_nonneg hpos.le h
  · intro h
    exact nonneg_of_mul_nonneg_right h hpos

/-- Inclusion of positive submonoids `S.toExtension.monoid →* E.monoid`. -/
def monoidIncl : S.toExtension.monoid →* E.monoid where
  toFun γ' := ⟨γ'.1.1, (E.mem_monoid _).mpr ((S.mem_toExtension_monoid_iff γ'.1).mp γ'.2)⟩
  map_one' := Subtype.ext (by simp [OneMemClass.coe_one])
  map_mul' _ _ := Subtype.ext (by simp [Submonoid.coe_mul])

@[simp]
theorem coe_monoidIncl (γ' : S.toExtension.monoid) :
    (S.monoidIncl γ' : Γ) = γ'.1.1 :=
  (rfl)

theorem monoidIncl_injective : Function.Injective S.monoidIncl :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun u : E.monoid ↦ (u : Γ)) h))

/-- The degree strip `{ x : Γ | 0 ≤ E.degree x < S.index }`. -/
def strip : Set Γ := { x : Γ | 0 ≤ E.degree x ∧ E.degree x < (S.index : ℤ) }

/-- Right multiplication on `S.strip` by an element of `S.kernel`. -/
def stripMulKernel (x : S.strip) (g' : S.kernel) : S.strip :=
  ⟨x.1 * E.incl g'.1, by
    change 0 ≤ E.degree (x.1 * E.incl g'.1) ∧ E.degree (x.1 * E.incl g'.1) < (S.index : ℤ)
    rw [E.degree_mul, E.degree_incl, add_zero]
    exact x.2⟩

@[simp]
theorem coe_stripMulKernel (x : S.strip) (g' : S.kernel) :
    (S.stripMulKernel x g' : Γ) = x.1 * E.incl g'.1 :=
  (rfl)

@[simp]
theorem stripMulKernel_one (x : S.strip) : S.stripMulKernel x 1 = x :=
  Subtype.ext (by simp)

theorem stripMulKernel_mul (x : S.strip) (g₁ g₂ : S.kernel) :
    S.stripMulKernel (S.stripMulKernel x g₁) g₂ = S.stripMulKernel x (g₁ * g₂) :=
  Subtype.ext (by simp [mul_assoc])

/-- Left multiplication on `S.strip` by an element of `G`. -/
def groupMulStrip (g : G) (x : S.strip) : S.strip :=
  ⟨E.incl g * x.1, by
    change 0 ≤ E.degree (E.incl g * x.1) ∧ E.degree (E.incl g * x.1) < (S.index : ℤ)
    rw [E.degree_mul, E.degree_incl, zero_add]
    exact x.2⟩

@[simp]
theorem coe_groupMulStrip (g : G) (x : S.strip) :
    (S.groupMulStrip g x : Γ) = E.incl g * x.1 :=
  (rfl)

@[simp]
theorem groupMulStrip_one (x : S.strip) : S.groupMulStrip 1 x = x :=
  Subtype.ext (by simp)

theorem groupMulStrip_mul (g₁ g₂ : G) (x : S.strip) :
    S.groupMulStrip (g₁ * g₂) x = S.groupMulStrip g₁ (S.groupMulStrip g₂ x) :=
  Subtype.ext (by simp [mul_assoc])

/-- For any `γ ∈ E.monoid` and `x ∈ S.strip`, there exist `y ∈ S.strip` and
`γ' ∈ S.toExtension.monoid` such that `γ * y = x * γ'`. -/
theorem exists_strip_mul_eq (γ : E.monoid) (x : S.strip) :
    ∃ (y : S.strip) (γ' : S.toExtension.monoid), γ.1 * y.1 = x.1 * γ'.1.1 := by
  obtain ⟨x₁, hx₁, hdeg₁⟩ := S.exists_degree_eq
  let z : Γ := γ.1⁻¹ * x.1
  let d : ℤ := S.index
  have hd : 0 < d := Int.natCast_pos.mpr S.index_pos
  let q : ℤ := E.degree z / d
  let γ'₀ : Γ := x₁ ^ (-q)
  have hγ'₀_sub : γ'₀ ∈ S.subgroup := zpow_mem hx₁ (-q)
  have hdeg_γ'₀ : E.degree γ'₀ = -q * d := by
    rw [E.degree_zpow, hdeg₁]
  let y₀ : Γ := z * γ'₀
  have hdeg_y₀ : E.degree y₀ = E.degree z % d := by
    rw [Int.emod_def, E.degree_mul, hdeg_γ'₀]
    dsimp only [q]
    ring
  have hy₀ : y₀ ∈ S.strip := by
    refine ⟨?_, ?_⟩
    · rw [hdeg_y₀]
      exact Int.emod_nonneg _ hd.ne'
    · rw [hdeg_y₀]
      exact Int.emod_lt_of_pos _ hd
  have heq : γ.1 * y₀ = x.1 * γ'₀ := by
    dsimp only [y₀, z]
    group
  have hγ'₀_nonneg : 0 ≤ E.degree γ'₀ := by
    have hdeg_eq : E.degree γ.1 + E.degree y₀ = E.degree x.1 + E.degree γ'₀ := by
      rw [← E.degree_mul, ← E.degree_mul, heq]
    have hγ_nonneg : 0 ≤ E.degree γ.1 := (E.mem_monoid γ.1).mp γ.2
    have hy_nonneg : 0 ≤ E.degree y₀ := hy₀.1
    have hx_lt : E.degree x.1 < d := x.2.2
    have : -d < -q * d := by linarith
    have hq_le : -1 < -q := by nlinarith
    have hq_nonneg : 0 ≤ -q := by omega
    rw [hdeg_γ'₀]
    exact mul_nonneg hq_nonneg hd.le
  refine ⟨⟨y₀, hy₀⟩, ⟨⟨γ'₀, hγ'₀_sub⟩, (S.mem_toExtension_monoid_iff _).mpr hγ'₀_nonneg⟩, heq⟩

/-- Uniqueness up to `S.kernel` of a solution `γ * y = x * γ'` with `y ∈ S.strip` and
`γ' ∈ S.toExtension.monoid`. -/
theorem exists_kernel_of_strip_mul_eq {γ : E.monoid} {x y₁ y₂ : S.strip}
    {γ'₁ γ'₂ : S.toExtension.monoid}
    (h₁ : γ.1 * y₁.1 = x.1 * γ'₁.1.1) (h₂ : γ.1 * y₂.1 = x.1 * γ'₂.1.1) :
    ∃ g' : S.kernel, y₁ = S.stripMulKernel y₂ g' ∧
      γ'₁ = γ'₂ * S.toExtension.monoidIncl g' := by
  let u : Γ := y₂.1⁻¹ * y₁.1
  have hu_eq : u = (γ'₂.1.1)⁻¹ * γ'₁.1.1 := by
    have h3 : (γ.1 * y₂.1)⁻¹ * (γ.1 * y₁.1) = (x.1 * γ'₂.1.1)⁻¹ * (x.1 * γ'₁.1.1) := by
      rw [h₁, h₂]
    dsimp only [u]
    calc y₂.1⁻¹ * y₁.1 = (γ.1 * y₂.1)⁻¹ * (γ.1 * y₁.1) := by group
      _ = (x.1 * γ'₂.1.1)⁻¹ * (x.1 * γ'₁.1.1) := h3
      _ = (γ'₂.1.1)⁻¹ * γ'₁.1.1 := by group
  have hu_sub : u ∈ S.subgroup := by
    rw [hu_eq]
    exact mul_mem (inv_mem γ'₂.1.2) γ'₁.1.2
  have hdeg_u : E.degree u = E.degree y₁.1 - E.degree y₂.1 := by
    dsimp only [u]
    rw [E.degree_mul, E.degree_inv]
    ring
  have hdeg0 : E.degree u = 0 := by
    obtain ⟨k, hk⟩ := S.dvd_degree u hu_sub
    have hlt1 : E.degree u < (S.index : ℤ) := by linarith [y₁.2.2, y₂.2.1]
    have hlt2 : -(S.index : ℤ) < E.degree u := by linarith [y₁.2.1, y₂.2.2]
    have hk0 : k = 0 := by nlinarith [Int.natCast_pos.mpr S.index_pos]
    rw [hk, hk0, mul_zero]
  obtain ⟨g, hg⟩ := (E.degree_eq_zero_iff u).mp hdeg0
  let g' : S.kernel := ⟨g, show E.incl g ∈ S.subgroup by rw [hg]; exact hu_sub⟩
  refine ⟨g', Subtype.ext ?_, Subtype.ext (Subtype.ext ?_)⟩
  · rw [coe_stripMulKernel]
    change y₁.1 = y₂.1 * E.incl g
    rw [hg]
    dsimp only [u]
    group
  · rw [Submonoid.coe_mul, Subgroup.coe_mul, S.toExtension.coe_monoidIncl]
    change γ'₁.1.1 = γ'₂.1.1 * E.incl g
    rw [hg, hu_eq]
    group

end Subextension

/-! ### Section 2: The induced module `InducedModule Λ S Q` -/

/-- Choice-free model of the induced `Λ[E.monoid]`-module `Ind_{Γ'_+}^{Γ_+}(Q)` for a subextension
`S : E.Subextension`: functions `f : S.strip → Q` satisfying `f (x * g') = (g'⁻¹) • f x` for all
`g' ∈ S.kernel`. -/
structure InducedModule (Λ : Type*) [Ring Λ] {E : MonoidExtension G Γ} (S : E.Subextension)
    (Q : Type*) [AddCommGroup Q] [Module Λ Q]
    [Module (MonoidAlgebra Λ S.toExtension.monoid) Q] where
  /-- Underlying function on the degree strip `S.strip`. -/
  toFun : S.strip → Q
  /-- Right `S.kernel`-equivariance on `S.strip`. -/
  equivariant : ∀ (x : S.strip) (g' : S.kernel),
    toFun (S.stripMulKernel x g') =
      (MonoidAlgebra.single (S.toExtension.monoidIncl g'⁻¹) (1 : Λ) :
        MonoidAlgebra Λ S.toExtension.monoid) • toFun x

namespace InducedModule

variable {Λ : Type*} [Ring Λ] {E : MonoidExtension G Γ} {S : E.Subextension}
variable {Q : Type*} [AddCommGroup Q] [Module Λ Q]
variable [Module (MonoidAlgebra Λ S.toExtension.monoid) Q]

instance : CoeFun (InducedModule Λ S Q) (fun _ ↦ S.strip → Q) := ⟨InducedModule.toFun⟩

@[ext]
theorem ext {f₁ f₂ : InducedModule Λ S Q} (h : ∀ x : S.strip, f₁ x = f₂ x) : f₁ = f₂ := by
  cases f₁
  cases f₂
  congr
  funext x
  exact h x

instance instAddCommGroup : AddCommGroup (InducedModule Λ S Q) where
  add f g :=
    { toFun := fun x ↦ f x + g x
      equivariant := fun x g' ↦ by rw [f.equivariant, g.equivariant, smul_add] }
  zero :=
    { toFun := fun _ ↦ 0
      equivariant := fun _ _ ↦ by simp }
  neg f :=
    { toFun := fun x ↦ -f x
      equivariant := fun x g' ↦ by rw [f.equivariant, smul_neg] }
  sub f g :=
    { toFun := fun x ↦ f x - g x
      equivariant := fun x g' ↦ by rw [f.equivariant, g.equivariant, smul_sub] }
  nsmul n f :=
    { toFun := fun x ↦ n • f x
      equivariant := fun x g' ↦ by rw [f.equivariant, smul_comm] }
  zsmul n f :=
    { toFun := fun x ↦ n • f x
      equivariant := fun x g' ↦ by rw [f.equivariant, smul_comm] }
  add_assoc f g h := ext fun x ↦ add_assoc (f x) (g x) (h x)
  zero_add f := ext fun x ↦ zero_add (f x)
  add_zero f := ext fun x ↦ add_zero (f x)
  nsmul_zero f := ext fun x ↦ AddMonoid.nsmul_zero (f x)
  nsmul_succ n f := ext fun x ↦ AddMonoid.nsmul_succ n (f x)
  zsmul_zero' f := ext fun x ↦ SubNegMonoid.zsmul_zero' (f x)
  zsmul_succ' n f := ext fun x ↦ SubNegMonoid.zsmul_succ' n (f x)
  zsmul_neg' n f := ext fun x ↦ SubNegMonoid.zsmul_neg' n (f x)
  neg_add_cancel f := ext fun x ↦ neg_add_cancel (f x)
  sub_eq_add_neg f g := ext fun x ↦ sub_eq_add_neg (f x) (g x)
  add_comm f g := ext fun x ↦ add_comm (f x) (g x)

@[simp]
theorem zero_apply (x : S.strip) : (0 : InducedModule Λ S Q) x = 0 := (rfl)

@[simp]
theorem add_apply (f g : InducedModule Λ S Q) (x : S.strip) : (f + g) x = f x + g x := (rfl)

@[simp]
theorem neg_apply (f : InducedModule Λ S Q) (x : S.strip) : (-f) x = -f x := (rfl)

@[simp]
theorem sub_apply (f g : InducedModule Λ S Q) (x : S.strip) : (f - g) x = f x - g x := (rfl)

theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → InducedModule Λ S Q) (x : S.strip) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

variable [IsScalarTower Λ (MonoidAlgebra Λ S.toExtension.monoid) Q]

/-- Left `Λ`-module structure on `InducedModule Λ S Q` acting pointwise. Agrees definitionally
with `AddCommGroup.toIntModule` when `Λ = ℤ`. -/
instance instModuleCoeff : Module Λ (InducedModule Λ S Q) where
  smul r f :=
    { toFun := fun x ↦ r • f x
      equivariant := fun x g' ↦ by
        rw [f.equivariant]
        simpa only [singleSMulEnd_apply] using
          ((singleSMulEnd Λ (S.toExtension.monoidIncl g'⁻¹) Q).map_smul r (f x)).symm }
  one_smul f := ext fun x ↦ one_smul Λ (f x)
  mul_smul r s f := ext fun x ↦ mul_smul r s (f x)
  smul_zero r := ext fun _ ↦ smul_zero r
  smul_add r f g := ext fun x ↦ smul_add r (f x) (g x)
  add_smul r s f := ext fun x ↦ add_smul r s (f x)
  zero_smul f := ext fun x ↦ zero_smul Λ (f x)

@[simp]
theorem smul_apply (r : Λ) (f : InducedModule Λ S Q) (x : S.strip) :
    (r • f) x = r • f x :=
  (rfl)

/-- Action of a single monoid element `γ ∈ E.monoid` on `InducedModule Λ S Q`: evaluated at
`x ∈ S.strip`, choose `y ∈ S.strip` and `γ' ∈ S.toExtension.monoid` with `γ * y = x * γ'` and
return `single γ' 1 • f y`. -/
def monoidAct (γ : E.monoid) (f : InducedModule Λ S Q) : InducedModule Λ S Q where
  toFun x :=
    let h := S.exists_strip_mul_eq γ x
    (MonoidAlgebra.single h.choose_spec.choose (1 : Λ) :
      MonoidAlgebra Λ S.toExtension.monoid) • f h.choose
  equivariant x g' := by
    let h₁ := S.exists_strip_mul_eq γ (S.stripMulKernel x g')
    let h₂ := S.exists_strip_mul_eq γ x
    let y₁ := h₁.choose
    let γ'₁ := h₁.choose_spec.choose
    have heq₁ : γ.1 * y₁.1 = (x.1 * E.incl g'.1) * γ'₁.1.1 := h₁.choose_spec.choose_spec
    let y₂ := h₂.choose
    let γ'₂ := h₂.choose_spec.choose
    have heq₂ : γ.1 * y₂.1 = x.1 * γ'₂.1.1 := h₂.choose_spec.choose_spec
    let γ'₃ : S.toExtension.monoid := S.toExtension.monoidIncl g' * γ'₁
    have hγ'₃ : γ'₃.1.1 = E.incl g'.1 * γ'₁.1.1 := by
      rw [Submonoid.coe_mul, Subgroup.coe_mul, S.toExtension.coe_monoidIncl]
      rfl
    have heq₃ : γ.1 * y₁.1 = x.1 * γ'₃.1.1 := by
      rw [hγ'₃, ← mul_assoc]
      exact heq₁
    obtain ⟨k', hy, hγ'⟩ := S.exists_kernel_of_strip_mul_eq heq₃ heq₂
    change (MonoidAlgebra.single γ'₁ (1 : Λ) : MonoidAlgebra Λ S.toExtension.monoid) • f y₁ =
      (MonoidAlgebra.single (S.toExtension.monoidIncl g'⁻¹) (1 : Λ) :
        MonoidAlgebra Λ S.toExtension.monoid) •
        ((MonoidAlgebra.single γ'₂ (1 : Λ) : MonoidAlgebra Λ S.toExtension.monoid) • f y₂)
    rw [hy, f.equivariant, ← mul_smul, ← mul_smul, single_mul_single, single_mul_single, mul_one]
    congr 2
    apply S.monoidIncl_injective
    apply Subtype.ext
    have h3 : E.incl g'.1 * γ'₁.1.1 = γ'₂.1.1 * E.incl k'.1 := by
      have h3' := congrArg (fun u : S.toExtension.monoid ↦ (u.1 : Γ)) hγ'
      rw [hγ'₃, Submonoid.coe_mul, Subgroup.coe_mul, S.toExtension.coe_monoidIncl] at h3'
      exact h3'
    change (γ'₁ * S.toExtension.monoidIncl k'⁻¹).1.1 = (S.toExtension.monoidIncl g'⁻¹ * γ'₂).1.1
    rw [Submonoid.coe_mul, Subgroup.coe_mul, S.toExtension.coe_monoidIncl,
      Submonoid.coe_mul, Subgroup.coe_mul, S.toExtension.coe_monoidIncl]
    change γ'₁.1.1 * E.incl k'⁻¹.1 = E.incl g'⁻¹.1 * γ'₂.1.1
    calc γ'₁.1.1 * E.incl k'⁻¹.1
        = (E.incl g'.1)⁻¹ * (E.incl g'.1 * γ'₁.1.1) * (E.incl k'.1)⁻¹ := by
          simp [map_inv]
      _ = (E.incl g'.1)⁻¹ * (γ'₂.1.1 * E.incl k'.1) * (E.incl k'.1)⁻¹ := by rw [h3]
      _ = E.incl g'⁻¹.1 * γ'₂.1.1 := by simp [map_inv, mul_assoc]

omit [IsScalarTower Λ (MonoidAlgebra Λ S.toExtension.monoid) Q] in
theorem monoidAct_apply_of_eq (γ : E.monoid) (f : InducedModule Λ S Q) (x y : S.strip)
    (γ' : S.toExtension.monoid) (h : γ.1 * y.1 = x.1 * γ'.1.1) :
    monoidAct γ f x =
      (MonoidAlgebra.single γ' (1 : Λ) : MonoidAlgebra Λ S.toExtension.monoid) • f y := by
  let h₀ := S.exists_strip_mul_eq γ x
  obtain ⟨k', hy, hγ'⟩ := S.exists_kernel_of_strip_mul_eq h₀.choose_spec.choose_spec h
  change (MonoidAlgebra.single h₀.choose_spec.choose (1 : Λ) :
      MonoidAlgebra Λ S.toExtension.monoid) • f h₀.choose = _
  rw [hγ', hy, f.equivariant, ← mul_smul, single_mul_single, mul_one, mul_assoc, ← map_mul,
    mul_inv_cancel, map_one, mul_one]

/-- Left `Λ`-scalar multiplication packaged as a ring homomorphism into `Module.End ℤ`. -/
def coeffActionHom : Λ →+* Module.End ℤ (InducedModule Λ S Q) where
  toFun r :=
    { toFun := fun f ↦ r • f
      map_add' := smul_add r
      map_smul' := fun n f ↦ by simp only [RingHom.id_apply, smul_comm n r f] }
  map_one' := by ext f x; simp
  map_mul' r s := by ext f x; simp [mul_smul]
  map_zero' := by ext f x; simp
  map_add' r s := by ext f x; simp [add_smul]

/-- Monoid action of `E.monoid` packaged as a monoid homomorphism into `Module.End ℤ`. -/
def monoidActionHom : E.monoid →* Module.End ℤ (InducedModule Λ S Q) where
  toFun γ :=
    { toFun := monoidAct γ
      map_add' := fun f g ↦ ext fun x ↦ by
        obtain ⟨y, γ', h⟩ := S.exists_strip_mul_eq γ x
        rw [add_apply, monoidAct_apply_of_eq γ (f + g) x y γ' h,
          monoidAct_apply_of_eq γ f x y γ' h, monoidAct_apply_of_eq γ g x y γ' h,
          add_apply, smul_add]
      map_smul' := fun n f ↦ ext fun x ↦ by
        obtain ⟨y, γ', h⟩ := S.exists_strip_mul_eq γ x
        rw [RingHom.id_apply, monoidAct_apply_of_eq γ (n • f) x y γ' h]
        change (MonoidAlgebra.single γ' (1 : Λ) : MonoidAlgebra Λ S.toExtension.monoid) •
            (n • f y) = n • monoidAct γ f x
        rw [monoidAct_apply_of_eq γ f x y γ' h, smul_comm] }
  map_one' := by
    ext f x
    change monoidAct 1 f x = f x
    rw [monoidAct_apply_of_eq 1 f x x 1 (by simp [OneMemClass.coe_one]), ← one_def, one_smul]
  map_mul' γ₁ γ₂ := by
    ext f x
    rw [mul_apply_eq_comp]
    change monoidAct (γ₁ * γ₂) f x = monoidAct γ₁ (monoidAct γ₂ f) x
    obtain ⟨y₁, γ'₁, h₁⟩ := S.exists_strip_mul_eq γ₁ x
    obtain ⟨y₂, γ'₂, h₂⟩ := S.exists_strip_mul_eq γ₂ y₁
    have h₁₂ : (γ₁ * γ₂).1 * y₂.1 = x.1 * (γ'₁ * γ'₂).1.1 := by
      rw [Submonoid.coe_mul, Submonoid.coe_mul, Subgroup.coe_mul, mul_assoc, h₂, ← mul_assoc, h₁,
        mul_assoc]
    rw [monoidAct_apply_of_eq (γ₁ * γ₂) f x y₂ (γ'₁ * γ'₂) h₁₂,
      monoidAct_apply_of_eq γ₁ (monoidAct γ₂ f) x y₁ γ'₁ h₁,
      monoidAct_apply_of_eq γ₂ f y₁ y₂ γ'₂ h₂,
      ← mul_smul, single_mul_single, mul_one]

/-- Ring homomorphism `MonoidAlgebra Λ E.monoid →+* Module.End ℤ (InducedModule Λ S Q)`. -/
def inducedActionHom : MonoidAlgebra Λ E.monoid →+* Module.End ℤ (InducedModule Λ S Q) :=
  liftNCRingHom (coeffActionHom (Λ := Λ) (S := S) (Q := Q))
    (monoidActionHom (Λ := Λ) (S := S) (Q := Q)) fun r γ ↦ by
      ext f x
      rw [mul_apply_eq_comp, mul_apply_eq_comp]
      change r • monoidAct γ f x = monoidAct γ (r • f) x
      obtain ⟨y, γ', h⟩ := S.exists_strip_mul_eq γ x
      rw [monoidAct_apply_of_eq γ f x y γ' h, monoidAct_apply_of_eq γ (r • f) x y γ' h, smul_apply]
      simpa only [singleSMulEnd_apply] using ((singleSMulEnd Λ γ' Q).map_smul r (f y)).symm

/-- Left `MonoidAlgebra Λ E.monoid`-module structure on `InducedModule Λ S Q`. -/
instance instModuleMonoidAlgebra : Module (MonoidAlgebra Λ E.monoid) (InducedModule Λ S Q) :=
  Module.compHom (InducedModule Λ S Q) (inducedActionHom (Λ := Λ) (S := S) (Q := Q))

theorem single_smul_apply_of_eq (γ : E.monoid) (a : Λ) (f : InducedModule Λ S Q)
    (x y : S.strip) (γ' : S.toExtension.monoid) (h : γ.1 * y.1 = x.1 * γ'.1.1) :
    ((MonoidAlgebra.single γ a : MonoidAlgebra Λ E.monoid) • f) x =
      (MonoidAlgebra.single γ' a : MonoidAlgebra Λ S.toExtension.monoid) • f y := by
  change (inducedActionHom (Λ := Λ) (S := S) (Q := Q) (MonoidAlgebra.single γ a) f) x = _
  rw [inducedActionHom, liftNCRingHom_single, mul_apply_eq_comp]
  change a • monoidAct γ f x = _
  rw [monoidAct_apply_of_eq γ f x y γ' h, ← smul_assoc, smul_single, smul_eq_mul, mul_one]

instance instIsScalarTowerMonoidAlgebra :
    IsScalarTower Λ (MonoidAlgebra Λ E.monoid) (InducedModule Λ S Q) where
  smul_assoc r u f := by
    induction u using MonoidAlgebra.induction_linear with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => simp [add_smul, smul_add, h₁, h₂]
    | single γ a =>
      ext x
      obtain ⟨y, γ', h⟩ := S.exists_strip_mul_eq γ x
      rw [smul_single, single_smul_apply_of_eq γ (r • a) f x y γ' h, smul_apply,
        single_smul_apply_of_eq γ a f x y γ' h, ← smul_single, smul_assoc]

/-- Left `MonoidAlgebra Λ G`-module structure on `InducedModule Λ S Q`, restricted along
`E.monoidIncl : G →* E.monoid`. -/
instance instModuleGroupAlgebra : Module (MonoidAlgebra Λ G) (InducedModule Λ S Q) :=
  Module.compHom (InducedModule Λ S Q)
    ((inducedActionHom (Λ := Λ) (S := S) (Q := Q)).comp
      (mapDomainRingHom Λ E.monoidIncl))

theorem smul_eq_mapDomain (r : MonoidAlgebra Λ G) (f : InducedModule Λ S Q) :
    r • f = mapDomain E.monoidIncl r • f :=
  rfl

instance instIsScalarTowerGroupAlgebra :
    IsScalarTower Λ (MonoidAlgebra Λ G) (InducedModule Λ S Q) where
  smul_assoc r u f := by
    rw [smul_eq_mapDomain, smul_eq_mapDomain, mapDomain_smul, smul_assoc]

@[simp]
theorem single_group_smul_apply (g : G) (a : Λ) (f : InducedModule Λ S Q) (x : S.strip) :
    ((MonoidAlgebra.single g a : MonoidAlgebra Λ G) • f) x =
      a • f (S.groupMulStrip g⁻¹ x) := by
  rw [smul_eq_mapDomain, mapDomain_single]
  have h : (E.monoidIncl g).1 * (S.groupMulStrip g⁻¹ x).1 = x.1 * (1 : S.toExtension.monoid).1.1 :=
    by simp
  rw [single_smul_apply_of_eq (E.monoidIncl g) a f x (S.groupMulStrip g⁻¹ x) 1 h]
  have h1 : (MonoidAlgebra.single (1 : S.toExtension.monoid) a :
      MonoidAlgebra Λ S.toExtension.monoid) = a • 1 := by
    rw [one_def, smul_single, smul_eq_mul, mul_one]
  rw [h1, smul_assoc, one_smul]

/-! ### Section 3: Explicit `Λ[G]`-retraction, finite projectivity, and centralizer trace -/

section Retraction

/-- Degree-`r` basepoint `γ₁ ^ r` in `S.strip` built from a fixed degree-`1` element `γ₁`. -/
def baseStrip (γ₁ : E.fiber 1) (r : Fin S.index) : S.strip :=
  ⟨γ₁.1.1 ^ (r : ℕ), by
    change 0 ≤ E.degree (γ₁.1.1 ^ (r : ℕ)) ∧ E.degree (γ₁.1.1 ^ (r : ℕ)) < (S.index : ℤ)
    rw [E.degree_pow, γ₁.2, Nat.cast_one, mul_one]
    exact ⟨Int.natCast_nonneg r.1, Int.ofNat_lt.mpr r.2⟩⟩

@[simp]
theorem coe_baseStrip (γ₁ : E.fiber 1) (r : Fin S.index) :
    (baseStrip (S := S) γ₁ r : Γ) = γ₁.1.1 ^ (r : ℕ) :=
  (rfl)

/-- Conjugated kernel subgroup `H_r = E.conjAut (γ₁ ^ r) (S.kernel) ≤ G`. -/
def conjKernel (γ₁ : E.fiber 1) (r : Fin S.index) : Subgroup G :=
  S.kernel.map (E.conjAut (γ₁.1.1 ^ (r : ℕ))).toMonoidHom

theorem mem_conjKernel_iff (γ₁ : E.fiber 1) (r : Fin S.index) (g : G) :
    g ∈ conjKernel (S := S) γ₁ r ↔ (E.conjAut (γ₁.1.1 ^ (r : ℕ))).symm g ∈ S.kernel := by
  simp only [conjKernel, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa using hk
  · intro h
    exact ⟨_, h, (E.conjAut _).apply_symm_apply g⟩

/-- Equivalence `S.kernel ≃* conjKernel γ₁ r` induced by `E.conjAut (γ₁ ^ r)`. -/
def conjKernelEquiv (γ₁ : E.fiber 1) (r : Fin S.index) :
    S.kernel ≃* conjKernel (S := S) γ₁ r where
  toFun k := ⟨E.conjAut (γ₁.1.1 ^ (r : ℕ)) k.1, ⟨k.1, k.2, rfl⟩⟩
  invFun h := ⟨(E.conjAut (γ₁.1.1 ^ (r : ℕ))).symm h.1, (mem_conjKernel_iff γ₁ r h.1).mp h.2⟩
  left_inv k := Subtype.ext ((E.conjAut _).symm_apply_apply k.1)
  right_inv h := Subtype.ext ((E.conjAut _).apply_symm_apply h.1)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem groupMulStrip_baseStrip_mul_conjKernel (γ₁ : E.fiber 1) (r : Fin S.index) (g : G)
    (k : S.kernel) :
    S.groupMulStrip (g * (conjKernelEquiv (S := S) γ₁ r k).1) (baseStrip γ₁ r) =
      S.stripMulKernel (S.groupMulStrip g (baseStrip γ₁ r)) k := by
  apply Subtype.ext
  rw [Subextension.coe_groupMulStrip, Subextension.coe_stripMulKernel,
    Subextension.coe_groupMulStrip, coe_baseStrip]
  change E.incl (g * E.conjAut (γ₁.1.1 ^ (r : ℕ)) k.1) * γ₁.1.1 ^ (r : ℕ) =
    (E.incl g * γ₁.1.1 ^ (r : ℕ)) * E.incl k.1
  rw [map_mul, E.incl_conjAut]
  group

/-- The natural-number degree `r : Fin S.index` of an element `x : S.strip`. -/
def stripDeg (x : S.strip) : Fin S.index :=
  ⟨(E.degree x.1).toNat, by
    have h0 : 0 ≤ E.degree x.1 := x.2.1
    have hlt : E.degree x.1 < (S.index : ℤ) := x.2.2
    omega⟩

theorem stripDeg_coe (x : S.strip) : ((stripDeg x : ℕ) : ℤ) = E.degree x.1 :=
  Int.toNat_of_nonneg x.2.1

@[simp]
theorem stripDeg_groupMulStrip_baseStrip (γ₁ : E.fiber 1) (r : Fin S.index) (g : G) :
    stripDeg (S.groupMulStrip g (baseStrip (S := S) γ₁ r)) = r := by
  apply Fin.ext
  have h : E.degree (E.incl g * γ₁.1.1 ^ (r : ℕ)) = (r : ℕ) := by
    rw [E.degree_mul, E.degree_incl, zero_add, E.degree_pow, γ₁.2, Nat.cast_one, mul_one]
  change (E.degree (S.groupMulStrip g (baseStrip γ₁ r) : Γ)).toNat = r.1
  rw [Subextension.coe_groupMulStrip, coe_baseStrip, h, Int.toNat_natCast]

/-- The unique element `g : G` such that `x = E.incl g * γ₁ ^ (stripDeg x)`. -/
def stripGroupCoord (γ₁ : E.fiber 1) (x : S.strip) : G :=
  (E.exists_incl_mul_of_degree_eq (x := x.1) (y := γ₁.1.1 ^ (stripDeg x : ℕ)) (by
    rw [E.degree_pow, γ₁.2, Nat.cast_one, mul_one, stripDeg_coe])).choose

theorem groupMulStrip_stripGroupCoord (γ₁ : E.fiber 1) (x : S.strip) :
    S.groupMulStrip (stripGroupCoord γ₁ x) (baseStrip γ₁ (stripDeg x)) = x := by
  apply Subtype.ext
  rw [Subextension.coe_groupMulStrip, coe_baseStrip]
  exact ((E.exists_incl_mul_of_degree_eq (x := x.1) (y := γ₁.1.1 ^ (stripDeg x : ℕ)) (by
    rw [E.degree_pow, γ₁.2, Nat.cast_one, mul_one, stripDeg_coe])).choose_spec).symm

@[simp]
theorem stripGroupCoord_groupMulStrip_baseStrip (γ₁ : E.fiber 1) (r : Fin S.index) (g : G) :
    stripGroupCoord γ₁ (S.groupMulStrip g (baseStrip (S := S) γ₁ r)) = g := by
  have h := congrArg Subtype.val
    (groupMulStrip_stripGroupCoord γ₁ (S.groupMulStrip g (baseStrip (S := S) γ₁ r)))
  rw [stripDeg_groupMulStrip_baseStrip, Subextension.coe_groupMulStrip,
    Subextension.coe_groupMulStrip, coe_baseStrip] at h
  exact E.incl_injective (mul_right_cancel h)

theorem stripGroupCoord_stripMulKernel (γ₁ : E.fiber 1) (x : S.strip) (k : S.kernel) :
    stripDeg (S.stripMulKernel x k) = stripDeg x ∧
      stripGroupCoord γ₁ (S.stripMulKernel x k) =
        stripGroupCoord γ₁ x * (conjKernelEquiv (S := S) γ₁ (stripDeg x) k).1 := by
  have hx := groupMulStrip_stripGroupCoord γ₁ x
  have hmul : S.stripMulKernel x k =
      S.groupMulStrip (stripGroupCoord γ₁ x * (conjKernelEquiv (S := S) γ₁ (stripDeg x) k).1)
        (baseStrip γ₁ (stripDeg x)) := by
    rw [groupMulStrip_baseStrip_mul_conjKernel, hx]
  rw [hmul, stripDeg_groupMulStrip_baseStrip, stripGroupCoord_groupMulStrip_baseStrip]
  exact ⟨rfl, rfl⟩

/-- The `Λ[G]`-linear inclusion of `InducedModule Λ S Q` into `Fin S.index × Fin m → Λ[G]` built
from a `Λ[S.kernel]`-retract `iQ : Q →ₗ[Λ[S.kernel]] (Fin m → Λ[S.kernel])`. -/
def retractIncl [Finite G] (γ₁ : E.fiber 1)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    {m : ℕ} (iQ : Q →ₗ[MonoidAlgebra Λ S.kernel] (Fin m → MonoidAlgebra Λ S.kernel)) :
    InducedModule Λ S Q →ₗ[MonoidAlgebra Λ G] (Fin S.index × Fin m → MonoidAlgebra Λ G) :=
  have : ∀ r : Fin S.index, Fintype (G ⧸ conjKernel (S := S) γ₁ r) := fun _ ↦ Fintype.ofFinite _
  let φ : Fin S.index → S.kernel →* G := fun r ↦
    (conjKernel (S := S) γ₁ r).subtype.comp (conjKernelEquiv (S := S) γ₁ r).toMonoidHom
  { toFun := fun f rj ↦
      ∑ q : G ⧸ conjKernel (S := S) γ₁ rj.1,
        MonoidAlgebra.single q.out (1 : Λ) *
          mapDomain (φ rj.1) (iQ (f (S.groupMulStrip q.out (baseStrip γ₁ rj.1))) rj.2)
    map_add' := fun f g ↦ by
      funext rj
      simp only [Pi.add_apply, add_apply, map_add, mapDomain_add, mul_add, Finset.sum_add_distrib]
    map_smul' := fun u f ↦ by
      rw [RingHom.id_apply]
      induction u using MonoidAlgebra.induction_linear with
      | zero =>
        funext rj
        simp
      | add u₁ u₂ h₁ h₂ =>
        funext rj
        simp only [add_smul, Pi.add_apply] at h₁ h₂ ⊢
        simp only [add_apply, map_add, Pi.add_apply, mapDomain_add, mul_add,
          Finset.sum_add_distrib]
        exact congrArg₂ (· + ·) (congrFun h₁ rj) (congrFun h₂ rj)
      | single h a =>
        funext rj
        rcases rj with ⟨r, j⟩
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        let eQ : (G ⧸ conjKernel (S := S) γ₁ r) ≃ (G ⧸ conjKernel (S := S) γ₁ r) :=
          MulAction.toPerm h⁻¹
        rw [Fintype.sum_equiv eQ _ _ (fun q ↦ ?_)]
        have hrel : (eQ q).out⁻¹ * (h⁻¹ * q.out) ∈ conjKernel (S := S) γ₁ r :=
          QuotientGroup.eq.mp (by
            rw [QuotientGroup.out_eq']
            exact congrArg (h⁻¹ • ·) (QuotientGroup.out_eq' q).symm)
        let k' : S.kernel := (conjKernelEquiv (S := S) γ₁ r).symm ⟨_, hrel⟩
        have hk'_eq : h⁻¹ * q.out = (eQ q).out * (conjKernelEquiv (S := S) γ₁ r k').1 := by
          have h1 : (conjKernelEquiv (S := S) γ₁ r k').1 = (eQ q).out⁻¹ * (h⁻¹ * q.out) := by
            change ((conjKernelEquiv (S := S) γ₁ r)
              ((conjKernelEquiv (S := S) γ₁ r).symm ⟨_, hrel⟩)).1 = _
            rw [MulEquiv.apply_symm_apply]
          rw [h1, mul_inv_cancel_left]
        rw [single_group_smul_apply, ← Subextension.groupMulStrip_mul, hk'_eq,
          groupMulStrip_baseStrip_mul_conjKernel, f.equivariant]
        have ha : a • ((MonoidAlgebra.single (S.toExtension.monoidIncl k'⁻¹) (1 : Λ) :
              MonoidAlgebra Λ S.toExtension.monoid) •
              f (S.groupMulStrip (eQ q).out (baseStrip γ₁ r))) =
            (MonoidAlgebra.single k'⁻¹ a : MonoidAlgebra Λ S.kernel) •
              f (S.groupMulStrip (eQ q).out (baseStrip γ₁ r)) := by
          rw [hQG', mapDomain_single, ← smul_assoc, smul_single, smul_eq_mul, mul_one]
        rw [ha, iQ.map_smul, Pi.smul_apply, smul_eq_mul,
          ← mapDomainRingHom_apply Λ (φ r), map_mul, mapDomainRingHom_apply,
          mapDomainRingHom_apply, mapDomain_single, ← mul_assoc, ← mul_assoc,
          single_mul_single, single_mul_single, one_mul, mul_one]
        congr 2
        have hq' : q.out * (φ r k')⁻¹ = h * (eQ q).out := by
          have hφ : φ r k' = (conjKernelEquiv (S := S) γ₁ r k').1 := rfl
          calc q.out * (φ r k')⁻¹ = h * (h⁻¹ * q.out) * (φ r k')⁻¹ := by group
            _ = h * ((eQ q).out * φ r k') * (φ r k')⁻¹ := by rw [hk'_eq, ← hφ]
            _ = h * (eQ q).out := by group
        rw [map_inv, hq'] }

theorem retractIncl_apply [Finite G] (γ₁ : E.fiber 1)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    {m : ℕ} (iQ : Q →ₗ[MonoidAlgebra Λ S.kernel] (Fin m → MonoidAlgebra Λ S.kernel))
    (f : InducedModule Λ S Q) (r : Fin S.index) (j : Fin m)
    [Fintype (G ⧸ conjKernel (S := S) γ₁ r)] :
    retractIncl (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' iQ f (r, j) =
      ∑ q : G ⧸ conjKernel (S := S) γ₁ r,
        MonoidAlgebra.single q.out (1 : Λ) *
          mapDomain ((conjKernel (S := S) γ₁ r).subtype.comp
            (conjKernelEquiv (S := S) γ₁ r).toMonoidHom)
            (iQ (f (S.groupMulStrip q.out (baseStrip γ₁ r))) j) := by
  dsimp only [retractIncl, LinearMap.coe_mk, AddHom.coe_mk]
  congr! 1
  exact Finset.ext fun _ ↦ by simp

/-- Auxiliary single-entry summand used to define `retractProj`. -/
def retractProjTerm (γ₁ : E.fiber 1)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    {m : ℕ} (rQ : (Fin m → MonoidAlgebra Λ S.kernel) →ₗ[MonoidAlgebra Λ S.kernel] Q)
    (r₀ : Fin S.index) (j : Fin m) (h : G) (a : Λ) : InducedModule Λ S Q := by
  classical
  exact
    { toFun := fun x ↦
        if stripDeg x = r₀ then
          if hmem : (stripGroupCoord γ₁ x)⁻¹ * h ∈ conjKernel (S := S) γ₁ r₀ then
            (MonoidAlgebra.single
                ((conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩) a :
              MonoidAlgebra Λ S.kernel) • rQ (Pi.single j 1)
          else 0
        else 0
      equivariant := fun x k' ↦ by
        obtain ⟨hdeg, hcoord⟩ := stripGroupCoord_stripMulKernel γ₁ x k'
        by_cases hr : stripDeg x = r₀
        · subst hr
          have hdeg' : stripDeg (S.stripMulKernel x k') = stripDeg x := hdeg
          simp only [hdeg', ↓reduceIte]
          have hmul : (stripGroupCoord γ₁ (S.stripMulKernel x k'))⁻¹ * h =
              ((conjKernelEquiv (S := S) γ₁ (stripDeg x) k').1)⁻¹ *
                ((stripGroupCoord γ₁ x)⁻¹ * h) := by
            rw [hcoord, mul_inv_rev, mul_assoc]
          have hmem_iff : (stripGroupCoord γ₁ (S.stripMulKernel x k'))⁻¹ * h ∈
                conjKernel (S := S) γ₁ (stripDeg x) ↔
              (stripGroupCoord γ₁ x)⁻¹ * h ∈ conjKernel (S := S) γ₁ (stripDeg x) := by
            rw [hmul]
            exact Subgroup.mul_mem_cancel_left _ (inv_mem (conjKernelEquiv γ₁ (stripDeg x) k').2)
          by_cases hmem : (stripGroupCoord γ₁ x)⁻¹ * h ∈ conjKernel (S := S) γ₁ (stripDeg x)
          · have hmem' := hmem_iff.mpr hmem
            simp only [hmem, hmem', ↓reduceDIte]
            rw [← mapDomain_single (f := S.toExtension.monoidIncl), ← hQG', ← mul_smul,
              single_mul_single, one_mul]
            congr 2
            apply (conjKernelEquiv (S := S) γ₁ (stripDeg x)).injective
            apply Subtype.ext
            simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, map_inv,
              InvMemClass.coe_inv]
            exact hmul
          · have hmem' : (stripGroupCoord γ₁ (S.stripMulKernel x k'))⁻¹ * h ∉
                conjKernel (S := S) γ₁ (stripDeg x) := fun hc ↦ hmem (hmem_iff.mp hc)
            simp [hmem, hmem']
        · have hr' : stripDeg (S.stripMulKernel x k') ≠ r₀ := by rwa [hdeg]
          simp [hr, hr'] }

/-- The `Λ[G]`-linear retraction `(Fin S.index × Fin m → Λ[G]) →ₗ[Λ[G]] InducedModule Λ S Q`
left-inverse to `retractIncl`. -/
def retractProj (γ₁ : E.fiber 1)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    {m : ℕ} (rQ : (Fin m → MonoidAlgebra Λ S.kernel) →ₗ[MonoidAlgebra Λ S.kernel] Q) :
    (Fin S.index × Fin m → MonoidAlgebra Λ G) →ₗ[MonoidAlgebra Λ G] InducedModule Λ S Q := by
  classical
  have : IsScalarTower Λ (MonoidAlgebra Λ S.kernel) Q :=
    ⟨fun r u q ↦ by rw [hQG', hQG', mapDomain_smul, smul_assoc]⟩
  have hterm_zero : ∀ r₀ j h, retractProjTerm (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ r₀ j h 0 =
      0 := fun r₀ j h ↦ ext fun x ↦ by
    dsimp only [retractProjTerm, zero_apply]
    split_ifs <;> simp
  have hterm_add : ∀ r₀ j h a₁ a₂,
      retractProjTerm (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ r₀ j h (a₁ + a₂) =
        retractProjTerm γ₁ hQG' rQ r₀ j h a₁ + retractProjTerm γ₁ hQG' rQ r₀ j h a₂ :=
    fun r₀ j h a₁ a₂ ↦ ext fun x ↦ by
      rw [add_apply]
      dsimp only [retractProjTerm]
      split_ifs <;> simp [single_add, add_smul]
  have hterm_smul : ∀ r₀ j h₁ a₁ h₂ a₂,
      retractProjTerm (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ r₀ j (h₁ * h₂) (a₁ * a₂) =
        (MonoidAlgebra.single h₁ a₁ : MonoidAlgebra Λ G) •
          retractProjTerm γ₁ hQG' rQ r₀ j h₂ a₂ :=
    fun r₀ j h₁ a₁ h₂ a₂ ↦ ext fun x ↦ by
      rw [single_group_smul_apply]
      have hx := groupMulStrip_stripGroupCoord γ₁ x
      have hgx : S.groupMulStrip h₁⁻¹ x =
          S.groupMulStrip (h₁⁻¹ * stripGroupCoord γ₁ x) (baseStrip γ₁ (stripDeg x)) := by
        conv_lhs => rw [← hx]
        rw [← Subextension.groupMulStrip_mul]
      have hdeg_gx : stripDeg (S.groupMulStrip h₁⁻¹ x) = stripDeg x := by
        rw [hgx, stripDeg_groupMulStrip_baseStrip]
      have hcoord_gx : stripGroupCoord γ₁ (S.groupMulStrip h₁⁻¹ x) =
          h₁⁻¹ * stripGroupCoord γ₁ x := by
        rw [hgx, stripGroupCoord_groupMulStrip_baseStrip]
      have hprod : (stripGroupCoord γ₁ (S.groupMulStrip h₁⁻¹ x))⁻¹ * h₂ =
          (stripGroupCoord γ₁ x)⁻¹ * (h₁ * h₂) := by
        rw [hcoord_gx, mul_inv_rev, inv_inv, mul_assoc]
      dsimp only [retractProjTerm]
      simp only [hdeg_gx, hprod]
      split_ifs with hr hmem
      · rw [← smul_assoc, smul_single, smul_eq_mul]
      · simp
      · simp
  refine
    { toFun := fun v ↦ ∑ rj : Fin S.index × Fin m,
        (v rj).coeff.sum (retractProjTerm γ₁ hQG' rQ rj.1 rj.2)
      map_add' := fun v w ↦ by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun rj _ ↦ ?_
        rw [Pi.add_apply, coeff_add]
        exact Finsupp.sum_add_index' (hterm_zero rj.1 rj.2) (hterm_add rj.1 rj.2)
      map_smul' := fun u v ↦ by
        rw [RingHom.id_apply]
        induction u using MonoidAlgebra.induction_linear with
        | zero => simp
        | add u₁ u₂ h₁ h₂ =>
          have hadd : ∀ w₁ w₂ : Fin S.index × Fin m → MonoidAlgebra Λ G,
              (∑ rj : Fin S.index × Fin m,
                ((w₁ + w₂) rj).coeff.sum (retractProjTerm γ₁ hQG' rQ rj.1 rj.2)) =
              (∑ rj : Fin S.index × Fin m,
                (w₁ rj).coeff.sum (retractProjTerm γ₁ hQG' rQ rj.1 rj.2)) +
              (∑ rj : Fin S.index × Fin m,
                (w₂ rj).coeff.sum (retractProjTerm γ₁ hQG' rQ rj.1 rj.2)) := fun w₁ w₂ ↦ by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun rj _ ↦ ?_
            rw [Pi.add_apply, coeff_add]
            exact Finsupp.sum_add_index' (hterm_zero rj.1 rj.2) (hterm_add rj.1 rj.2)
          rw [add_smul, add_smul, hadd, h₁, h₂]
        | single h₁ a₁ =>
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun rj _ ↦ ?_
          rw [Pi.smul_apply, smul_eq_mul]
          generalize v rj = w
          induction w using MonoidAlgebra.induction_linear with
          | zero => simp
          | add w₁ w₂ hw₁ hw₂ =>
            rw [mul_add, coeff_add, coeff_add,
              Finsupp.sum_add_index' (hterm_zero rj.1 rj.2) (hterm_add rj.1 rj.2),
              Finsupp.sum_add_index' (hterm_zero rj.1 rj.2) (hterm_add rj.1 rj.2),
              smul_add, hw₁, hw₂]
          | single h₂ a₂ =>
            rw [single_mul_single, coeff_single, coeff_single,
              Finsupp.sum_single_index (hterm_zero rj.1 rj.2 _),
              Finsupp.sum_single_index (hterm_zero rj.1 rj.2 _),
              hterm_smul] }

theorem retractProj_single_apply_ne (γ₁ : E.fiber 1)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    {m : ℕ} (rQ : (Fin m → MonoidAlgebra Λ S.kernel) →ₗ[MonoidAlgebra Λ S.kernel] Q)
    (rj : Fin S.index × Fin m) (h : G) (a : Λ) (x : S.strip) (hne : stripDeg x ≠ rj.1) :
    retractProj γ₁ hQG' rQ (Pi.single rj (MonoidAlgebra.single h a)) x = 0 := by
  classical
  change (∑ p : Fin S.index × Fin m,
      ((Pi.single rj (MonoidAlgebra.single h a) :
          Fin S.index × Fin m → MonoidAlgebra Λ G) p).coeff.sum
        (retractProjTerm (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ p.1 p.2)) x = 0
  rw [Finset.sum_eq_single rj]
  · rw [Pi.single_eq_same, coeff_single, Finsupp.sum_single_index]
    · dsimp only [retractProjTerm]
      simp [hne]
    · ext y
      dsimp only [retractProjTerm, zero_apply]
      split_ifs <;> simp
  · intro p _ hp
    rw [Pi.single_eq_of_ne hp]
    simp
  · intro hmem
    exact absurd (Finset.mem_univ rj) hmem

/-- `retractProj` is a left inverse to `retractIncl`. -/
theorem retractProj_comp_retractIncl [Finite G] (γ₁ : E.fiber 1)
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    {m : ℕ} (iQ : Q →ₗ[MonoidAlgebra Λ S.kernel] (Fin m → MonoidAlgebra Λ S.kernel))
    (rQ : (Fin m → MonoidAlgebra Λ S.kernel) →ₗ[MonoidAlgebra Λ S.kernel] Q)
    (hrQ : rQ ∘ₗ iQ = .id) :
    retractProj (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ ∘ₗ retractIncl γ₁ hQG' iQ = .id := by
  classical
  have : ∀ r : Fin S.index, Fintype (G ⧸ conjKernel (S := S) γ₁ r) := fun _ ↦ Fintype.ofFinite _
  let φ : Fin S.index → S.kernel →* G := fun r ↦
    (conjKernel (S := S) γ₁ r).subtype.comp (conjKernelEquiv (S := S) γ₁ r).toMonoidHom
  apply LinearMap.ext
  intro f
  apply InducedModule.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  set r₀ : Fin S.index := stripDeg x
  set g₀ : G := stripGroupCoord γ₁ x
  have hx : x = S.groupMulStrip g₀ (baseStrip γ₁ r₀) :=
    (groupMulStrip_stripGroupCoord γ₁ x).symm
  let evalX : InducedModule Λ S Q →+ Q :=
    { toFun := fun f' ↦ f' x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hsum_proj : (retractProj γ₁ hQG' rQ (retractIncl γ₁ hQG' iQ f)) x =
      ∑ j : Fin m, (retractIncl γ₁ hQG' iQ f (r₀, j)).coeff.sum fun h a ↦
        if hmem : g₀⁻¹ * h ∈ conjKernel (S := S) γ₁ r₀ then
          (MonoidAlgebra.single
              ((conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩) a :
            MonoidAlgebra Λ S.kernel) • rQ (Pi.single j 1)
        else 0 := by
    change (∑ rj : Fin S.index × Fin m,
        (retractIncl γ₁ hQG' iQ f rj).coeff.sum
          (retractProjTerm (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ rj.1 rj.2)) x = _
    rw [sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single r₀]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      change evalX ((retractIncl γ₁ hQG' iQ f (r₀, j)).coeff.sum
        (retractProjTerm (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ r₀ j)) = _
      rw [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun h _ ↦ ?_
      change (if stripDeg x = r₀ then _ else 0) = _
      simp only [r₀, g₀, ↓reduceIte]
    · intro r _ hr
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      change evalX ((retractIncl γ₁ hQG' iQ f (r, j)).coeff.sum
        (retractProjTerm (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ r j)) = 0
      rw [Finsupp.sum, map_sum]
      refine Finset.sum_eq_zero fun h _ ↦ ?_
      change (if stripDeg x = r then _ else 0) = 0
      simp [r₀, Ne.symm hr]
    · intro hmem
      exact absurd (Finset.mem_univ r₀) hmem
  rw [hsum_proj]
  let q₀ : G ⧸ conjKernel (S := S) γ₁ r₀ := QuotientGroup.mk g₀
  have hrel₀ : q₀.out⁻¹ * g₀ ∈ conjKernel (S := S) γ₁ r₀ :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' q₀)
  let k₀ : S.kernel := (conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hrel₀⟩
  have hg₀_eq : g₀ = q₀.out * φ r₀ k₀ := by
    have h1 : φ r₀ k₀ = q₀.out⁻¹ * g₀ := by
      change ((conjKernelEquiv (S := S) γ₁ r₀)
        ((conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hrel₀⟩)).1 = _
      rw [MulEquiv.apply_symm_apply]
    rw [h1, mul_inv_cancel_left]
  have hj_eval : ∀ j : Fin m,
      ((retractIncl γ₁ hQG' iQ f (r₀, j)).coeff.sum fun h a ↦
        if hmem : g₀⁻¹ * h ∈ conjKernel (S := S) γ₁ r₀ then
          (MonoidAlgebra.single
              ((conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩) a :
            MonoidAlgebra Λ S.kernel) • rQ (Pi.single j 1)
        else 0) =
      (MonoidAlgebra.single k₀⁻¹ (1 : Λ) : MonoidAlgebra Λ S.kernel) •
        rQ (Pi.single j (iQ (f (S.groupMulStrip q₀.out (baseStrip γ₁ r₀))) j)) := by
    intro j
    let ψ : MonoidAlgebra Λ G →+ Q :=
      { toFun := fun u ↦ u.coeff.sum fun h a ↦
          if hmem : g₀⁻¹ * h ∈ conjKernel (S := S) γ₁ r₀ then
            (MonoidAlgebra.single
                ((conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩) a :
              MonoidAlgebra Λ S.kernel) • rQ (Pi.single j 1)
          else 0
        map_zero' := by simp
        map_add' := fun u₁ u₂ ↦ by
          rw [coeff_add]
          exact Finsupp.sum_add_index' (fun _ ↦ by split_ifs <;> simp) (fun h a₁ a₂ ↦ by
            split_ifs <;> simp [single_add, add_smul]) }
    have hψ_single : ∀ (h : G) (a : Λ),
        ψ (MonoidAlgebra.single h a) =
          if hmem : g₀⁻¹ * h ∈ conjKernel (S := S) γ₁ r₀ then
            (MonoidAlgebra.single
                ((conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩) a :
              MonoidAlgebra Λ S.kernel) • rQ (Pi.single j 1)
          else 0 := fun h a ↦ by
      change (MonoidAlgebra.single h a : MonoidAlgebra Λ G).coeff.sum (fun h' a' ↦
        if hmem : g₀⁻¹ * h' ∈ conjKernel (S := S) γ₁ r₀ then
          (MonoidAlgebra.single
              ((conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩) a' :
            MonoidAlgebra Λ S.kernel) • rQ (Pi.single j 1)
        else 0) = _
      rw [coeff_single, Finsupp.sum_single_index (by split_ifs <;> simp)]
    change ψ (retractIncl γ₁ hQG' iQ f (r₀, j)) = _
    rw [retractIncl_apply]
    change ψ (∑ q : G ⧸ conjKernel (S := S) γ₁ r₀,
        MonoidAlgebra.single q.out (1 : Λ) *
          mapDomain (φ r₀) (iQ (f (S.groupMulStrip q.out (baseStrip γ₁ r₀))) j)) = _
    rw [map_sum, Finset.sum_eq_single q₀]
    · generalize iQ (f (S.groupMulStrip q₀.out (baseStrip γ₁ r₀))) j = u
      induction u using MonoidAlgebra.induction_linear with
      | zero => simp
      | add u₁ u₂ h₁ h₂ =>
        rw [mapDomain_add, mul_add, map_add, h₁, h₂, Pi.single_add, map_add, smul_add]
      | single k a =>
        rw [mapDomain_single, single_mul_single, one_mul, hψ_single]
        have hmem : g₀⁻¹ * (q₀.out * φ r₀ k) ∈ conjKernel (S := S) γ₁ r₀ := by
          rw [hg₀_eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
          exact mul_mem (inv_mem (conjKernelEquiv γ₁ r₀ k₀).2) (conjKernelEquiv γ₁ r₀ k).2
        simp only [hmem, ↓reduceDIte]
        have hsymm : (conjKernelEquiv (S := S) γ₁ r₀).symm ⟨_, hmem⟩ = k₀⁻¹ * k := by
          apply (conjKernelEquiv (S := S) γ₁ r₀).injective
          apply Subtype.ext
          rw [MulEquiv.apply_symm_apply, map_mul, map_inv]
          change g₀⁻¹ * (q₀.out * φ r₀ k) = (φ r₀ k₀)⁻¹ * φ r₀ k
          rw [hg₀_eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
        rw [hsymm]
        have h1 : (MonoidAlgebra.single (k₀⁻¹ * k) a : MonoidAlgebra Λ S.kernel) =
            MonoidAlgebra.single k₀⁻¹ (1 : Λ) * MonoidAlgebra.single k a := by
          rw [single_mul_single, one_mul]
        rw [h1, mul_smul, ← rQ.map_smul]
        congr 2
        funext j'
        by_cases hj' : j' = j <;> simp [hj']
    · intro q _ hq
      generalize iQ (f (S.groupMulStrip q.out (baseStrip γ₁ r₀))) j = u
      induction u using MonoidAlgebra.induction_linear with
      | zero => simp
      | add u₁ u₂ h₁ h₂ => rw [mapDomain_add, mul_add, map_add, h₁, h₂, add_zero]
      | single k a =>
        rw [mapDomain_single, single_mul_single, one_mul, hψ_single]
        have hnmem : g₀⁻¹ * (q.out * φ r₀ k) ∉ conjKernel (S := S) γ₁ r₀ := by
          intro hmem
          have hmem' : g₀⁻¹ * q.out ∈ conjKernel (S := S) γ₁ r₀ := by
            have h1 := mul_mem hmem (inv_mem (conjKernelEquiv (S := S) γ₁ r₀ k).2)
            dsimp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype,
              MulEquiv.coe_toMonoidHom] at h1
            simpa [mul_assoc] using h1
          have hqeq : q = q₀ := by
            rw [← QuotientGroup.out_eq' q]
            exact (QuotientGroup.eq.mpr hmem').symm
          exact hq hqeq
        simp only [hnmem, ↓reduceDIte]
    · intro hmem
      exact absurd (Finset.mem_univ q₀) hmem
  simp_rw [hj_eval, ← Finset.smul_sum, ← map_sum]
  have hpi : (∑ j : Fin m,
      Pi.single j (iQ (f (S.groupMulStrip q₀.out (baseStrip γ₁ r₀))) j)) =
      iQ (f (S.groupMulStrip q₀.out (baseStrip γ₁ r₀))) := by
    funext j'
    simp [Finset.sum_apply, Pi.single_apply]
  have hri : rQ (iQ (f (S.groupMulStrip q₀.out (baseStrip γ₁ r₀)))) =
      f (S.groupMulStrip q₀.out (baseStrip γ₁ r₀)) :=
    LinearMap.congr_fun hrQ _
  rw [hpi, hri, hQG', mapDomain_single, hx, hg₀_eq]
  dsimp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
  rw [groupMulStrip_baseStrip_mul_conjKernel, f.equivariant]

/-- If `G` is finite and `Q` is finite projective over `Λ[S.kernel]`, then `InducedModule Λ S Q`
is finite projective over `Λ[G]`. -/
theorem finite_projective [Finite G]
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    [Module.Finite (MonoidAlgebra Λ S.kernel) Q]
    [Module.Projective (MonoidAlgebra Λ S.kernel) Q] :
    Module.Finite (MonoidAlgebra Λ G) (InducedModule Λ S Q) ∧
      Module.Projective (MonoidAlgebra Λ G) (InducedModule Λ S Q) := by
  obtain ⟨γ₁⟩ := E.fiber_nonempty 1
  obtain ⟨m, rQ, iQ, -, -, hrQ⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ S.kernel) Q
  let i := retractIncl (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' iQ
  let r := retractProj (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ
  have hr : r ∘ₗ i = .id := retractProj_comp_retractIncl γ₁ hQG' iQ rQ hrQ
  have hsurj : Function.Surjective r :=
    Function.RightInverse.surjective (LinearMap.congr_fun hr)
  refine ⟨Module.Finite.of_surjective r hsurj, Module.Projective.of_split i r hr⟩

end Retraction

end InducedModule

/-- If `S.index ∤ E.degree γ`, then the centralizer trace of `γ` on `InducedModule Λ S Q` vanishes
in `Λ / [Λ, Λ]`. -/
theorem centralizerTrace_inducedModule_eq_zero_of_not_dvd {Λ : Type*} [Ring Λ]
    {E : MonoidExtension G Γ} [Finite G] (S : E.Subextension)
    (γ : E.monoid) (hnd : ¬ (S.index : ℤ) ∣ E.degree γ.1)
    (Q : Type*) [AddCommGroup Q] [Module Λ Q]
    [Module (MonoidAlgebra Λ S.toExtension.monoid) Q]
    [IsScalarTower Λ (MonoidAlgebra Λ S.toExtension.monoid) Q]
    [Module (MonoidAlgebra Λ S.kernel) Q]
    (hQG' : ∀ (r : MonoidAlgebra Λ S.kernel) (q : Q),
      r • q = mapDomain S.toExtension.monoidIncl r • q)
    [Module.Finite (MonoidAlgebra Λ S.kernel) Q]
    [Module.Projective (MonoidAlgebra Λ S.kernel) Q] :
    haveI := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').1
    haveI := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').2
    LinearMap.centralizerTrace Λ E.monoidIncl γ (InducedModule Λ S Q)
        (InducedModule.smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q)) = 0 := by
  classical
  have := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').1
  have := (InducedModule.finite_projective (Λ := Λ) (S := S) (Q := Q) hQG').2
  obtain ⟨γ₁⟩ := E.fiber_nonempty 1
  obtain ⟨m, rQ, iQ, -, -, hrQ⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (MonoidAlgebra Λ S.kernel) Q
  let i0 := InducedModule.retractIncl (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' iQ
  let r0 := InducedModule.retractProj (Λ := Λ) (S := S) (Q := Q) γ₁ hQG' rQ
  have hr0 : r0 ∘ₗ i0 = .id := InducedModule.retractProj_comp_retractIncl γ₁ hQG' iQ rQ hrQ
  let eIdx : Fin S.index × Fin m ≃ Fin (S.index * m) := finProdFinEquiv
  let ePi : (Fin S.index × Fin m → MonoidAlgebra Λ G) ≃ₗ[MonoidAlgebra Λ G]
      (Fin (S.index * m) → MonoidAlgebra Λ G) :=
    LinearEquiv.piCongrLeft' (MonoidAlgebra Λ G) (fun _ ↦ MonoidAlgebra Λ G) eIdx
  let i := ePi.toLinearMap ∘ₗ i0
  let r := r0 ∘ₗ ePi.symm.toLinearMap
  have hr : r ∘ₗ i = .id := by
    apply LinearMap.ext
    intro f
    change r0 (ePi.symm (ePi (i0 f))) = f
    rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hr0 f
  let Z := E.monoidIncl.centralizerSubgroup γ
  have : Fintype (G ⧸ Z.subtype.range) := Fintype.ofFinite _
  rw [LinearMap.centralizerTrace_eq_of_retract E.monoidIncl γ (InducedModule Λ S Q)
      (InducedModule.smul_eq_mapDomain (Λ := Λ) (S := S) (Q := Q)) i r hr]
  suffices hzero : ∀ (idx : Fin (S.index * m)) (q : G ⧸ Z.subtype.range),
      (i ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ E.monoid) •
        r (Pi.single idx (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) idx).coeff q.out⁻¹ = 0 by
    simp [hzero]
  intro idx q
  let p := eIdx.symm idx
  have hsymm : ePi.symm (Pi.single idx (MonoidAlgebra.single q.out⁻¹ (1 : Λ))) =
      Pi.single p (MonoidAlgebra.single q.out⁻¹ (1 : Λ)) := by
    apply ePi.injective
    rw [LinearEquiv.apply_symm_apply]
    funext k
    change (Pi.single idx (MonoidAlgebra.single q.out⁻¹ (1 : Λ)) :
        Fin (S.index * m) → MonoidAlgebra Λ G) k =
      (Pi.single p (MonoidAlgebra.single q.out⁻¹ (1 : Λ)) :
        Fin S.index × Fin m → MonoidAlgebra Λ G) (eIdx.symm k)
    by_cases hk : k = idx
    · subst hk
      simp [p]
    · have hk' : eIdx.symm k ≠ p := fun hEq ↦ hk (eIdx.symm.injective hEq)
      simp [hk, hk']
  have heval : ∀ v : Fin S.index × Fin m → MonoidAlgebra Λ G, ePi v idx = v p := fun v ↦ rfl
  change (ePi (i0 ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      r0 (ePi.symm (Pi.single idx (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))))) idx).coeff q.out⁻¹ = 0
  rw [hsymm, heval]
  have hvanish : ∀ g : G,
      ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ E.monoid) •
          r0 (Pi.single p (MonoidAlgebra.single q.out⁻¹ (1 : Λ))))
        (S.groupMulStrip g (InducedModule.baseStrip γ₁ p.1)) = 0 := by
    intro g
    let x := S.groupMulStrip g (InducedModule.baseStrip γ₁ p.1)
    obtain ⟨y, γ', heq⟩ := S.exists_strip_mul_eq γ x
    rw [InducedModule.single_smul_apply_of_eq γ 1 _ x y γ' heq]
    have hne : InducedModule.stripDeg y ≠ p.1 := by
      intro hdeg
      have h1 := congrArg E.degree heq
      rw [E.degree_mul, E.degree_mul] at h1
      have hy_deg : E.degree y.1 = (p.1 : ℕ) := by
        rw [← InducedModule.stripDeg_coe y, hdeg]
      have hx_deg : E.degree x.1 = (p.1 : ℕ) := by
        rw [Subextension.coe_groupMulStrip, InducedModule.coe_baseStrip, E.degree_mul,
          E.degree_incl, zero_add, E.degree_pow, γ₁.2, Nat.cast_one, mul_one]
      have hγ_eq : E.degree γ.1 = E.degree γ'.1.1 := by linarith
      rw [hγ_eq] at hnd
      exact hnd (S.dvd_degree γ'.1.1 γ'.1.2)
    rw [InducedModule.retractProj_single_apply_ne γ₁ hQG' rQ p q.out⁻¹ 1 y hne, smul_zero]
  have hi0 : i0 ((MonoidAlgebra.single γ (1 : Λ) : MonoidAlgebra Λ E.monoid) •
      r0 (Pi.single p (MonoidAlgebra.single q.out⁻¹ (1 : Λ)))) p = 0 := by
    have : Fintype (G ⧸ InducedModule.conjKernel (S := S) γ₁ p.1) := Fintype.ofFinite _
    rw [show p = (p.1, p.2) from rfl, InducedModule.retractIncl_apply]
    refine Finset.sum_eq_zero fun q' _ ↦ ?_
    rw [hvanish q'.out, map_zero, Pi.zero_apply, mapDomain_zero, mul_zero]
  rw [hi0]
  simp

end MonoidExtension

end TauCeti
