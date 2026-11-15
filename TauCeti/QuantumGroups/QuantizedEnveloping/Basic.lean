/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.RingQuot
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Hom
public import TauCeti.QuantumGroups.QuantumInteger.Factorial

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Constructions

/-!
# The Drinfeld–Jimbo quantized enveloping algebra on a full Cartan datum

This file constructs the quantized enveloping algebra `QuantizedEnvelopingAlgebra D q` associated to
a symmetrizable Cartan datum `D : CartanDatum ι X Y` on full lattices and a parameter `q` in a field
`K`. It is presented as the quotient of the free `K`-algebra on Chevalley generators `Eᵢ`, `Fᵢ`
(`i : ι`) and toral generators `K_y` (`y : Y`) by:

* the group-algebra relations `K_0 = 1` and `K_y K_z = K_(y + z)` on the full coweight lattice `Y`;
* the toral conjugation relations `K_y Eᵢ K_(-y) = q^⟨αᵢ, y⟩ Eᵢ` and
  `K_y Fᵢ K_(-y) = q^(-⟨αᵢ, y⟩) Fᵢ`;
* the commutator relations `Eᵢ Fᵢ - Fᵢ Eᵢ = (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)` and `Eᵢ Fⱼ = Fⱼ Eᵢ` for
  `i ≠ j`, where `qᵢ = q^(dᵢ)` and `Kᵢ = K_(dᵢ hᵢ)`;
* the quantum Serre relations `∑_{r + s = 1 - aᵢⱼ} (-1)^r Eᵢ^(r) Eⱼ Eᵢ^(s) = 0` and their `F`
  analogues for `i ≠ j`, written with `qᵢ`-divided powers `x^(r) = x^r / [r]_(qᵢ)!`.

Retaining a toral symbol `K_y` for every `y ∈ Y` preserves central directions (coweights annihilated
by every simple root, whose `K_c` are central) and intermediate isogeny lattices between the coroot
lattice and the coweight lattice; when `ι` is empty the algebra is canonically the group algebra
`K[Y]` (`TauCeti.QuantizedEnvelopingAlgebra.torusEquiv`). No finiteness, decidable-equality, or
freeness hypothesis is imposed on `ι`, `X`, or `Y`.

## Main definitions

* `TauCeti.QuantizedEnvelopingAlgebra D q`: the Drinfeld–Jimbo quantized enveloping algebra over
  `K`.
* `TauCeti.QuantizedEnvelopingAlgebra.e`, `TauCeti.QuantizedEnvelopingAlgebra.f`,
  `TauCeti.QuantizedEnvelopingAlgebra.k`, `TauCeti.QuantizedEnvelopingAlgebra.simpleK`,
  `TauCeti.QuantizedEnvelopingAlgebra.simpleKInv`: the Chevalley and toral generators.
* `TauCeti.QuantizedEnvelopingAlgebra.serreLength` and
  `TauCeti.QuantizedEnvelopingAlgebra.serreElement`: the Serre degree `1 - aᵢⱼ` and divided-power
  quantum Serre polynomial.
* `TauCeti.QuantizedEnvelopingAlgebra.GeneratorTuple`,
  `TauCeti.QuantizedEnvelopingAlgebra.lift`, and
  `TauCeti.QuantizedEnvelopingAlgebra.liftEquiv`: the universal property of the presentation.
* `TauCeti.QuantizedEnvelopingAlgebra.kUnits`: the group homomorphism `Multiplicative Y →* Uˣ`.
* `TauCeti.QuantizedEnvelopingAlgebra.map`: functoriality along a `CartanDatum.Hom`.
* `TauCeti.QuantizedEnvelopingAlgebra.torusEquiv`: for empty `ι`, the isomorphism with the group
  algebra `AddMonoidAlgebra K Y`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.e_mul_e_of_cartan_eq_zero` and
  `TauCeti.QuantizedEnvelopingAlgebra.f_mul_f_of_cartan_eq_zero`: generators at orthogonal distinct
  nodes commute when `qᵢ - qᵢ⁻¹ ≠ 0`.
* `TauCeti.QuantizedEnvelopingAlgebra.k_mem_center_of_forall_pairing_root_eq_zero`: `K_c` is
  central whenever `⟨αᵢ, c⟩ = 0` for every `i`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.1–1.4 and §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, Chapter 4.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  278 (2015), 40–89, Definition 3.2 (presentation on intermediate lattices).
* The `RingQuot` and `GeneratorTuple` presentation pattern follows
  `TauCeti.QuantumGroups.UqSl2.Basic` and `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`.
-/

public section

open Finset

namespace TauCeti

namespace QuantizedEnvelopingAlgebra

/-- The generators of the presentation of a quantized enveloping algebra: raising and lowering
generators `Eᵢ`, `Fᵢ` (`i : ι`) and a toral generator `K_y` for every coweight `y : Y`. -/
inductive Generator (ι Y : Type*)
  | e (i : ι)
  | f (i : ι)
  | k (y : Y)
  deriving DecidableEq

section Serre

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-- The degree `1 - aᵢⱼ` of the quantum Serre relation between nodes `i` and `j`. -/
def serreLength (D : CartanDatum ι X Y) (i j : ι) : ℕ :=
  (1 - D.cartan i j).toNat

/-- The defining formula for `serreLength`. -/
theorem serreLength_def (D : CartanDatum ι X Y) (i j : ι) :
    serreLength D i j = (1 - D.cartan i j).toNat := (rfl)

/-- For distinct nodes `i ≠ j`, `aᵢⱼ ≤ 0`, so `serreLength D i j ≥ 1`. -/
theorem serreLength_pos (D : CartanDatum ι X Y) {i j : ι} (hij : i ≠ j) :
    0 < serreLength D i j := by
  have h := D.cartan_nonpos hij
  rw [serreLength_def]
  omega

/-- For distinct nodes `i ≠ j`, casting `serreLength D i j` back to `ℤ` recovers `1 - aᵢⱼ`. -/
theorem natCast_serreLength (D : CartanDatum ι X Y) {i j : ι} (hij : i ≠ j) :
    (serreLength D i j : ℤ) = 1 - D.cartan i j := by
  have h := D.cartan_nonpos hij
  rw [serreLength_def]
  omega

/-- For distinct nodes `i ≠ j`, `1 - serreLength D i j = aᵢⱼ`. -/
theorem one_sub_serreLength (D : CartanDatum ι X Y) {i j : ι} (hij : i ≠ j) :
    1 - (serreLength D i j : ℤ) = D.cartan i j := by
  rw [natCast_serreLength D hij]
  ring

/-- When `aᵢⱼ = 0`, the Serre length is `1`. -/
@[simp]
theorem serreLength_of_cartan_eq_zero (D : CartanDatum ι X Y) {i j : ι} (h : D.cartan i j = 0) :
    serreLength D i j = 1 := by
  simp [serreLength_def, h]

/-- A morphism of Cartan data preserves the Serre lengths. -/
theorem serreLength_of_hom {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (i j : ι) :
    serreLength D' i j = serreLength D i j := by
  rw [serreLength_def, serreLength_def, φ.cartan_eq]

/-- The divided-power quantum Serre combination
`∑_{r = 0}^{1 - aᵢⱼ} (-1)^r xᵢ^(r)_(qᵢ) xⱼ xᵢ^(1 - aᵢⱼ - r)_(qᵢ)` of a family `x : ι → A` in a
`K`-algebra, with `qᵢ = q^(dᵢ)`. -/
noncomputable def serreElement {A : Type*} [Ring A] [Algebra K A] (D : CartanDatum ι X Y) (q : K)
    (x : ι → A) (i j : ι) : A :=
  ∑ r ∈ range (serreLength D i j + 1),
    (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (x i) r * x j *
        quantumDividedPower (q ^ D.symmetrizer i) (x i) (serreLength D i j - r))

/-- The defining sum for `serreElement`. -/
theorem serreElement_def {A : Type*} [Ring A] [Algebra K A] (D : CartanDatum ι X Y) (q : K)
    (x : ι → A) (i j : ι) :
    serreElement D q x i j =
      ∑ r ∈ range (serreLength D i j + 1),
        (-1 : K) ^ r •
          (quantumDividedPower (q ^ D.symmetrizer i) (x i) r * x j *
            quantumDividedPower (q ^ D.symmetrizer i) (x i) (serreLength D i j - r)) := (rfl)

/-- Algebra homomorphisms carry `serreElement` to `serreElement` of the composed family. -/
@[simp]
theorem _root_.AlgHom.map_serreElement {A B : Type*} [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (D : CartanDatum ι X Y) (q : K) (x : ι → A) (i j : ι) :
    φ (serreElement D q x i j) = serreElement D q (φ ∘ x) i j := by
  simp [serreElement_def]

/-- Rescaling `x k` by `c k` multiplies `serreElement D q x i j` by `cᵢ^(1 - aᵢⱼ) cⱼ`. -/
theorem serreElement_smul {A : Type*} [Ring A] [Algebra K A] (D : CartanDatum ι X Y) (q : K)
    (c : ι → K) (x : ι → A) (i j : ι) :
    serreElement D q (fun k => c k • x k) i j =
      (c i ^ serreLength D i j * c j) • serreElement D q x i j := by
  rw [serreElement_def, serreElement_def, smul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hle : r ≤ serreLength D i j := Nat.lt_succ_iff.mp (mem_range.mp hr)
  simp only [quantumDividedPower_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  have hpow : c i ^ serreLength D i j = c i ^ r * c i ^ (serreLength D i j - r) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [hpow]
  ring

/-- When `aᵢⱼ = 0` and `qᵢ - qᵢ⁻¹ ≠ 0`, `serreElement D q x i j` is `xⱼ xᵢ - xᵢ xⱼ`. -/
theorem serreElement_of_cartan_eq_zero {A : Type*} [Ring A] [Algebra K A] (D : CartanDatum ι X Y)
    {q : K} (x : ι → A) {i j : ι} (h : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) :
    serreElement D q x i j = x j * x i - x i * x j := by
  rw [serreElement_def, serreLength_of_cartan_eq_zero D h, sum_range_succ, sum_range_one]
  simp [quantumDividedPower_one hq, sub_eq_add_neg]

end Serre

/-- The defining relations of the Drinfeld–Jimbo quantized enveloping algebra of a Cartan datum
`D` at parameter `q`, as a binary relation on the free `K`-algebra on `Generator ι Y`. -/
inductive Relation {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
    (D : CartanDatum ι X Y) (q : K) :
    FreeAlgebra K (Generator ι Y) → FreeAlgebra K (Generator ι Y) → Prop
  | k_zero : Relation D q (FreeAlgebra.ι K (.k 0)) 1
  | k_mul_k (y z : Y) :
      Relation D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.k z)) (FreeAlgebra.ι K (.k (y + z)))
  | k_mul_e_mul_k_neg (y : Y) (i : ι) :
      Relation D q
        (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.k (-y)))
        (q ^ D.pairing (D.root i) y • FreeAlgebra.ι K (.e i))
  | k_mul_f_mul_k_neg (y : Y) (i : ι) :
      Relation D q
        (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.k (-y)))
        (q ^ (-D.pairing (D.root i) y) • FreeAlgebra.ι K (.f i))
  | e_mul_f_sub_f_mul_e_self (i : ι) :
      Relation D q
        (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f i) -
          FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.e i))
        ((q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (FreeAlgebra.ι K (.k (D.simpleTorus i)) - FreeAlgebra.ι K (.k (-D.simpleTorus i))))
  | e_mul_f_of_ne {i j : ι} (hij : i ≠ j) :
      Relation D q
        (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f j))
        (FreeAlgebra.ι K (.f j) * FreeAlgebra.ι K (.e i))
  | serre_e {i j : ι} (hij : i ≠ j) :
      Relation D q (serreElement D q (fun k => FreeAlgebra.ι K (.e k)) i j) 0
  | serre_f {i j : ι} (hij : i ≠ j) :
      Relation D q (serreElement D q (fun k => FreeAlgebra.ι K (.f k)) i j) 0

end QuantizedEnvelopingAlgebra

/-- The **quantized enveloping algebra** `U_q(D)` of a symmetrizable Cartan datum `D` on full
lattices `(X, Y)` at parameter `q : K`, defined as the quotient of the free `K`-algebra on
`Eᵢ`, `Fᵢ`, and `K_y` (`y ∈ Y`) by the Drinfeld–Jimbo relations. -/
def QuantizedEnvelopingAlgebra {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
    (D : CartanDatum ι X Y) (q : K) : Type _ :=
  RingQuot (QuantizedEnvelopingAlgebra.Relation D q)

namespace QuantizedEnvelopingAlgebra

section Instances

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

noncomputable instance : Ring (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Ring (RingQuot (Relation D q)))

noncomputable instance : Algebra K (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Algebra K (RingQuot (Relation D q)))

end Instances

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-! ### Generators and defining relations -/

/-- The quotient algebra map from the free algebra onto `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def mkAlgHom (D : CartanDatum ι X Y) (q : K) :
    FreeAlgebra K (Generator ι Y) →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  RingQuot.mkAlgHom K (Relation D q)

/-- The image in `QuantizedEnvelopingAlgebra D q` of a free generator. -/
noncomputable def generator (D : CartanDatum ι X Y) (q : K) (g : Generator ι Y) :
    QuantizedEnvelopingAlgebra D q :=
  mkAlgHom D q (FreeAlgebra.ι K g)

/-- `mkAlgHom` sends a free generator to the corresponding generator of
`QuantizedEnvelopingAlgebra D q`. -/
@[simp]
theorem mkAlgHom_ι (D : CartanDatum ι X Y) (q : K) (g : Generator ι Y) :
    mkAlgHom D q (FreeAlgebra.ι K g) = generator D q g := (rfl)

/-- The raising Chevalley generator `Eᵢ` of `QuantizedEnvelopingAlgebra D q`. -/
noncomputable abbrev e (D : CartanDatum ι X Y) (q : K) (i : ι) :
    QuantizedEnvelopingAlgebra D q :=
  generator D q (.e i)

/-- The lowering Chevalley generator `Fᵢ` of `QuantizedEnvelopingAlgebra D q`. -/
noncomputable abbrev f (D : CartanDatum ι X Y) (q : K) (i : ι) :
    QuantizedEnvelopingAlgebra D q :=
  generator D q (.f i)

/-- The toral generator `K_y` (`y : Y`) of `QuantizedEnvelopingAlgebra D q`. -/
noncomputable abbrev k (D : CartanDatum ι X Y) (q : K) (y : Y) :
    QuantizedEnvelopingAlgebra D q :=
  generator D q (.k y)

/-- The simple toral generator `Kᵢ = K_(dᵢ hᵢ)`. -/
noncomputable abbrev simpleK (D : CartanDatum ι X Y) (q : K) (i : ι) :
    QuantizedEnvelopingAlgebra D q :=
  k D q (D.simpleTorus i)

/-- The inverse simple toral generator `Kᵢ⁻¹ = K_(-dᵢ hᵢ)`. -/
noncomputable abbrev simpleKInv (D : CartanDatum ι X Y) (q : K) (i : ι) :
    QuantizedEnvelopingAlgebra D q :=
  k D q (-D.simpleTorus i)

private theorem mkAlgHom_rel {D : CartanDatum ι X Y} {q : K}
    {a b : FreeAlgebra K (Generator ι Y)} (h : Relation D q a b) :
    mkAlgHom D q a = mkAlgHom D q b :=
  RingQuot.mkAlgHom_rel K h

variable (D : CartanDatum ι X Y) (q : K)

/-- `K_0 = 1`. -/
@[simp]
theorem k_zero : k D q 0 = 1 := by
  simpa only [map_one, mkAlgHom_ι] using mkAlgHom_rel (Relation.k_zero (D := D) (q := q))

/-- `K_y K_z = K_(y + z)`. -/
@[simp]
theorem k_mul_k (y z : Y) : k D q y * k D q z = k D q (y + z) := by
  simpa only [map_mul, mkAlgHom_ι] using mkAlgHom_rel (Relation.k_mul_k (D := D) (q := q) y z)

/-- Left multiplication by `K_y` followed by `K_z` multiplies by `K_(y + z)`. -/
@[simp]
theorem k_mul_k_mul (y z : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q y * (k D q z * x) = k D q (y + z) * x := by
  rw [← mul_assoc, k_mul_k]

/-- The defining conjugation relation `K_y Eᵢ K_(-y) = q^⟨αᵢ, y⟩ • Eᵢ`. -/
theorem k_mul_e_mul_k_neg (y : Y) (i : ι) :
    k D q y * e D q i * k D q (-y) = q ^ D.pairing (D.root i) y • e D q i := by
  simpa only [map_mul, map_smul, mkAlgHom_ι] using
    mkAlgHom_rel (Relation.k_mul_e_mul_k_neg (D := D) (q := q) y i)

/-- The defining conjugation relation `K_y Fᵢ K_(-y) = q^(-⟨αᵢ, y⟩) • Fᵢ`. -/
theorem k_mul_f_mul_k_neg (y : Y) (i : ι) :
    k D q y * f D q i * k D q (-y) = q ^ (-D.pairing (D.root i) y) • f D q i := by
  simpa only [map_mul, map_smul, mkAlgHom_ι] using
    mkAlgHom_rel (Relation.k_mul_f_mul_k_neg (D := D) (q := q) y i)

/-- The diagonal commutator relation `Eᵢ Fᵢ - Fᵢ Eᵢ = (qᵢ - qᵢ⁻¹)⁻¹ • (Kᵢ - Kᵢ⁻¹)`. -/
theorem e_mul_f_sub_f_mul_e_self (i : ι) :
    e D q i * f D q i - f D q i * e D q i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (simpleK D q i - simpleKInv D q i) := by
  simpa only [map_sub, map_mul, map_smul, mkAlgHom_ι] using
    mkAlgHom_rel (Relation.e_mul_f_sub_f_mul_e_self (D := D) (q := q) i)

/-- Raising and lowering generators at distinct nodes commute: `Eᵢ Fⱼ = Fⱼ Eᵢ` for `i ≠ j`. -/
theorem e_mul_f_of_ne {i j : ι} (hij : i ≠ j) :
    e D q i * f D q j = f D q j * e D q i := by
  simpa only [map_mul, mkAlgHom_ι] using
    mkAlgHom_rel (Relation.e_mul_f_of_ne (D := D) (q := q) hij)

/-- The combined Kronecker-delta commutator relation `[Eᵢ, Fⱼ] = δᵢⱼ (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)`. -/
theorem e_mul_f_sub_f_mul_e [DecidableEq ι] (i j : ι) :
    e D q i * f D q j - f D q j * e D q i =
      if i = j then
        (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (simpleK D q i - simpleKInv D q i)
      else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp [e_mul_f_sub_f_mul_e_self]
  · simp [hij, e_mul_f_of_ne D q hij]

/-- The positive quantum Serre relation for `i ≠ j`. -/
theorem serre_e {i j : ι} (hij : i ≠ j) :
    serreElement D q (e D q) i j = 0 := by
  simpa only [AlgHom.map_serreElement, map_zero, Function.comp_def, mkAlgHom_ι] using
    mkAlgHom_rel (Relation.serre_e (D := D) (q := q) hij)

/-- The negative quantum Serre relation for `i ≠ j`. -/
theorem serre_f {i j : ι} (hij : i ≠ j) :
    serreElement D q (f D q) i j = 0 := by
  simpa only [AlgHom.map_serreElement, map_zero, Function.comp_def, mkAlgHom_ι] using
    mkAlgHom_rel (Relation.serre_f (D := D) (q := q) hij)

/-! ### Toral units and commutation rules -/

/-- The toral generators packaged as a group homomorphism `Multiplicative Y →* Uˣ`, sending
`y` to the unit `K_y` with inverse `K_(-y)`. -/
noncomputable def kUnits : Multiplicative Y →* (QuantizedEnvelopingAlgebra D q)ˣ where
  toFun y :=
    { val := k D q y.toAdd
      inv := k D q (-y.toAdd)
      val_inv := by simp
      inv_val := by simp }
  map_one' := by ext; simp
  map_mul' y z := by ext; simp [toAdd_mul]

@[simp]
theorem kUnits_val (y : Multiplicative Y) :
    ((kUnits D q y : (QuantizedEnvelopingAlgebra D q)ˣ) : QuantizedEnvelopingAlgebra D q) =
      k D q y.toAdd := (rfl)

@[simp]
theorem kUnits_inv (y : Multiplicative Y) :
    (((kUnits D q y)⁻¹ : (QuantizedEnvelopingAlgebra D q)ˣ) : QuantizedEnvelopingAlgebra D q) =
      k D q (-y.toAdd) := (rfl)

/-- Natural powers of `K_y` multiply the coweight by `n`: `(K_y)^n = K_(n • y)`. -/
@[simp]
theorem k_pow (y : Y) (n : ℕ) : k D q y ^ n = k D q (n • y) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, k_mul_k, succ_nsmul]

/-- Toral generators commute with one another. -/
theorem k_commute (y z : Y) : Commute (k D q y) (k D q z) := by
  rw [Commute, SemiconjBy, k_mul_k, k_mul_k, add_comm]

/-- `K_y Eᵢ = q^⟨αᵢ, y⟩ • (Eᵢ K_y)`. -/
theorem k_mul_e (y : Y) (i : ι) :
    k D q y * e D q i = q ^ D.pairing (D.root i) y • (e D q i * k D q y) := by
  calc
    k D q y * e D q i = k D q y * e D q i * k D q (-y) * k D q y := by
      simp [mul_assoc]
    _ = q ^ D.pairing (D.root i) y • (e D q i * k D q y) := by
      rw [k_mul_e_mul_k_neg, smul_mul_assoc]

/-- `K_y Fᵢ = q^(-⟨αᵢ, y⟩) • (Fᵢ K_y)`. -/
theorem k_mul_f (y : Y) (i : ι) :
    k D q y * f D q i = q ^ (-D.pairing (D.root i) y) • (f D q i * k D q y) := by
  calc
    k D q y * f D q i = k D q y * f D q i * k D q (-y) * k D q y := by
      simp [mul_assoc]
    _ = q ^ (-D.pairing (D.root i) y) • (f D q i * k D q y) := by
      rw [k_mul_f_mul_k_neg, smul_mul_assoc]

/-- At `q = 0`, the toral relation along `hᵢ` (`⟨αᵢ, hᵢ⟩ = 2`) forces `Eᵢ = 0`. -/
@[simp]
theorem e_zero (i : ι) : e D (0 : K) i = 0 := by
  have h := k_mul_e_mul_k_neg D (0 : K) (D.coroot i) i
  rw [D.pairing_root_coroot_self] at h
  calc
    e D (0 : K) i = k D 0 (-D.coroot i) * (k D 0 (D.coroot i) * e D 0 i * k D 0 (-D.coroot i)) *
        k D 0 (D.coroot i) := by simp [mul_assoc]
    _ = 0 := by simp [h]

/-- At `q = 0`, the toral relation along `-hᵢ` forces `Fᵢ = 0`. -/
@[simp]
theorem f_zero (i : ι) : f D (0 : K) i = 0 := by
  have h := k_mul_f_mul_k_neg D (0 : K) (-D.coroot i) i
  rw [map_neg, neg_neg, D.pairing_root_coroot_self] at h
  calc
    f D (0 : K) i = k D 0 (D.coroot i) * (k D 0 (-D.coroot i) * f D 0 i *
        k D 0 (- -D.coroot i)) * k D 0 (-D.coroot i) := by simp [mul_assoc]
    _ = 0 := by simp [h]

/-- `Eᵢ K_y = q^(-⟨αᵢ, y⟩) • (K_y Eᵢ)`. -/
theorem e_mul_k (i : ι) (y : Y) :
    e D q i * k D q y = q ^ (-D.pairing (D.root i) y) • (k D q y * e D q i) := by
  calc
    e D q i * k D q y = k D q y * (k D q (-y) * e D q i * k D q (- -y)) := by
      simp [mul_assoc]
    _ = q ^ (-D.pairing (D.root i) y) • (k D q y * e D q i) := by
      rw [k_mul_e_mul_k_neg, map_neg, mul_smul_comm]

/-- `Fᵢ K_y = q^⟨αᵢ, y⟩ • (K_y Fᵢ)`. -/
theorem f_mul_k (i : ι) (y : Y) :
    f D q i * k D q y = q ^ D.pairing (D.root i) y • (k D q y * f D q i) := by
  calc
    f D q i * k D q y = k D q y * (k D q (-y) * f D q i * k D q (- -y)) := by
      simp [mul_assoc]
    _ = q ^ D.pairing (D.root i) y • (k D q y * f D q i) := by
      rw [k_mul_f_mul_k_neg, map_neg, neg_neg, mul_smul_comm]

/-- `Kⱼ Eᵢ = qᵢ^(aⱼᵢ') • (Eᵢ Kⱼ)`, specifically `Kⱼ Eᵢ = (q^(dᵢ))^aᵢⱼ • (Eᵢ Kⱼ)` by
symmetrizability `⟨αᵢ, dⱼ hⱼ⟩ = dᵢ aᵢⱼ`. -/
theorem simpleK_mul_e (j i : ι) :
    simpleK D q j * e D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q i * simpleK D q j) := by
  rw [k_mul_e, D.pairing_root_simpleTorus, ← zpow_natCast, zpow_mul]

/-- `Kⱼ Fᵢ = (q^(dᵢ))^(-aᵢⱼ) • (Fᵢ Kⱼ)`. -/
theorem simpleK_mul_f (j i : ι) :
    simpleK D q j * f D q i =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (f D q i * simpleK D q j) := by
  rw [k_mul_f, D.pairing_root_simpleTorus, ← zpow_natCast, ← zpow_mul, mul_neg]

/-- `Kⱼ⁻¹ Eᵢ = (q^(dᵢ))^(-aᵢⱼ) • (Eᵢ Kⱼ⁻¹)`. -/
theorem simpleKInv_mul_e (j i : ι) :
    simpleKInv D q j * e D q i =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (e D q i * simpleKInv D q j) := by
  rw [k_mul_e, map_neg, D.pairing_root_simpleTorus, ← zpow_natCast, ← zpow_mul, mul_neg]

/-- `Kⱼ⁻¹ Fᵢ = (q^(dᵢ))^aᵢⱼ • (Fᵢ Kⱼ⁻¹)`. -/
theorem simpleKInv_mul_f (j i : ι) :
    simpleKInv D q j * f D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (f D q i * simpleKInv D q j) := by
  rw [k_mul_f, map_neg, neg_neg, D.pairing_root_simpleTorus, ← zpow_natCast, zpow_mul]

/-- `Eᵢ Kⱼ = (q^(dᵢ))^(-aᵢⱼ) • (Kⱼ Eᵢ)`. -/
theorem e_mul_simpleK (i j : ι) :
    e D q i * simpleK D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (simpleK D q j * e D q i) := by
  rw [e_mul_k, D.pairing_root_simpleTorus, ← zpow_natCast, ← zpow_mul, mul_neg]

/-- `Fᵢ Kⱼ = (q^(dᵢ))^aᵢⱼ • (Kⱼ Fᵢ)`. -/
theorem f_mul_simpleK (i j : ι) :
    f D q i * simpleK D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleK D q j * f D q i) := by
  rw [f_mul_k, D.pairing_root_simpleTorus, ← zpow_natCast, zpow_mul]

/-- `Eᵢ Kⱼ⁻¹ = (q^(dᵢ))^aᵢⱼ • (Kⱼ⁻¹ Eᵢ)`. -/
theorem e_mul_simpleKInv (i j : ι) :
    e D q i * simpleKInv D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleKInv D q j * e D q i) := by
  rw [e_mul_k, map_neg, neg_neg, D.pairing_root_simpleTorus, ← zpow_natCast, zpow_mul]

/-- `Fᵢ Kⱼ⁻¹ = (q^(dᵢ))^(-aᵢⱼ) • (Kⱼ⁻¹ Fᵢ)`. -/
theorem f_mul_simpleKInv (i j : ι) :
    f D q i * simpleKInv D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (simpleKInv D q j * f D q i) := by
  rw [f_mul_k, map_neg, D.pairing_root_simpleTorus, ← zpow_natCast, ← zpow_mul, mul_neg]

/-- Commuting `K_y` past `Eᵢ^(n)_(qᵢ)` multiplies by `(q^⟨αᵢ, y⟩)^n`. -/
theorem k_mul_quantumDividedPower_e (y : Y) (i : ι) (n : ℕ) :
    k D q y * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n =
      (q ^ D.pairing (D.root i) y) ^ n •
        (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n * k D q y) := by
  have hk := pow_mul_pow_of_mul_eq_smul_mul (k_mul_e D q y i) 1 n
  rw [pow_one, one_mul] at hk
  rw [quantumDividedPower_def, mul_smul_comm, smul_mul_assoc, hk, smul_comm]

/-- Commuting `K_y` past `Fᵢ^(n)_(qᵢ)` multiplies by `(q^(-⟨αᵢ, y⟩))^n`. -/
theorem k_mul_quantumDividedPower_f (y : Y) (i : ι) (n : ℕ) :
    k D q y * quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n =
      (q ^ (-D.pairing (D.root i) y)) ^ n •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n * k D q y) := by
  have hk := pow_mul_pow_of_mul_eq_smul_mul (k_mul_f D q y i) 1 n
  rw [pow_one, one_mul] at hk
  rw [quantumDividedPower_def, mul_smul_comm, smul_mul_assoc, hk, smul_comm]

/-- Commuting `Eᵢ^(n)_(qᵢ)` past `K_y` multiplies by `(q^(-⟨αᵢ, y⟩))^n`. -/
theorem quantumDividedPower_e_mul_k (i : ι) (y : Y) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n * k D q y =
      (q ^ (-D.pairing (D.root i) y)) ^ n •
        (k D q y * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) := by
  have hk := pow_mul_pow_of_mul_eq_smul_mul (e_mul_k D q i y) n 1
  rw [pow_one, mul_one] at hk
  rw [quantumDividedPower_def, smul_mul_assoc, mul_smul_comm, hk, smul_comm]

/-- Commuting `Fᵢ^(n)_(qᵢ)` past `K_y` multiplies by `(q^⟨αᵢ, y⟩)^n`. -/
theorem quantumDividedPower_f_mul_k (i : ι) (y : Y) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n * k D q y =
      (q ^ D.pairing (D.root i) y) ^ n •
        (k D q y * quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) := by
  have hk := pow_mul_pow_of_mul_eq_smul_mul (f_mul_k D q i y) n 1
  rw [pow_one, mul_one] at hk
  rw [quantumDividedPower_def, smul_mul_assoc, mul_smul_comm, hk, smul_comm]

/-- Raising generators at distinct orthogonal nodes (`aᵢⱼ = 0`) commute when `qᵢ - qᵢ⁻¹ ≠ 0`. -/
theorem e_mul_e_of_cartan_eq_zero {q : K} {i j : ι} (hij : i ≠ j) (h : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) :
    e D q i * e D q j = e D q j * e D q i := by
  have hs := serre_e D q hij
  rw [serreElement_of_cartan_eq_zero D (e D q) h hq, sub_eq_zero] at hs
  exact hs.symm

/-- Lowering generators at distinct orthogonal nodes (`aᵢⱼ = 0`) commute when `qᵢ - qᵢ⁻¹ ≠ 0`. -/
theorem f_mul_f_of_cartan_eq_zero {q : K} {i j : ι} (hij : i ≠ j) (h : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) :
    f D q i * f D q j = f D q j * f D q i := by
  have hs := serre_f D q hij
  rw [serreElement_of_cartan_eq_zero D (f D q) h hq, sub_eq_zero] at hs
  exact hs.symm

/-! ### Universal property and induction -/

/-- A family of elements `(e, f, k)` in a `K`-algebra `A` satisfying the defining Drinfeld–Jimbo
relations of `QuantizedEnvelopingAlgebra D q`. -/
structure GeneratorTuple (D : CartanDatum ι X Y) (q : K) (A : Type*) [Ring A] [Algebra K A] where
  /-- Proposed images of the raising generators `Eᵢ`. -/
  e : ι → A
  /-- Proposed images of the lowering generators `Fᵢ`. -/
  f : ι → A
  /-- Proposed images of the toral generators `K_y`. -/
  k : Y → A
  k_zero : k 0 = 1
  k_mul_k (y z : Y) : k y * k z = k (y + z)
  k_mul_e_mul_k_neg (y : Y) (i : ι) : k y * e i * k (-y) = q ^ D.pairing (D.root i) y • e i
  k_mul_f_mul_k_neg (y : Y) (i : ι) : k y * f i * k (-y) = q ^ (-D.pairing (D.root i) y) • f i
  e_mul_f_sub_f_mul_e_self (i : ι) :
    e i * f i - f i * e i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k (D.simpleTorus i) - k (-D.simpleTorus i))
  e_mul_f_of_ne {i j : ι} (hij : i ≠ j) : e i * f j = f j * e i
  serre_e {i j : ι} (hij : i ≠ j) : serreElement D q e i j = 0
  serre_f {i j : ι} (hij : i ≠ j) : serreElement D q f i j = 0

namespace GeneratorTuple

variable {D : CartanDatum ι X Y} {q : K} {A : Type*} [Ring A] [Algebra K A]

/-- The function on generator symbols underlying a `GeneratorTuple`. -/
def toFun (x : GeneratorTuple D q A) : Generator ι Y → A
  | .e i => x.e i
  | .f i => x.f i
  | .k y => x.k y

@[simp] theorem toFun_e (x : GeneratorTuple D q A) (i : ι) : x.toFun (.e i) = x.e i := (rfl)
@[simp] theorem toFun_f (x : GeneratorTuple D q A) (i : ι) : x.toFun (.f i) = x.f i := (rfl)
@[simp] theorem toFun_k (x : GeneratorTuple D q A) (y : Y) : x.toFun (.k y) = x.k y := (rfl)

/-- Two generator tuples agreeing on `e`, `f`, and `k` are equal. -/
@[ext]
theorem ext {x y : GeneratorTuple D q A} (he : x.e = y.e) (hf : x.f = y.f) (hk : x.k = y.k) :
    x = y := by
  cases x
  cases y
  congr

end GeneratorTuple

section Lift

variable {D : CartanDatum ι X Y} {q : K} {A : Type*} [Ring A] [Algebra K A]

/-- **Universal property of `QuantizedEnvelopingAlgebra`**: a `GeneratorTuple` in `A` extends to a
`K`-algebra homomorphism `QuantizedEnvelopingAlgebra D q →ₐ[K] A`. -/
noncomputable def lift (x : GeneratorTuple D q A) : QuantizedEnvelopingAlgebra D q →ₐ[K] A :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K x.toFun, by
    rintro _ _ (h | ⟨y, z⟩ | ⟨y, i⟩ | ⟨y, i⟩ | ⟨i⟩ | @⟨i, j, hij⟩ | @⟨i, j, hij⟩ | @⟨i, j, hij⟩)
    · simpa only [map_one, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k] using x.k_zero
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k] using x.k_mul_k y z
    · simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k,
        GeneratorTuple.toFun_e] using x.k_mul_e_mul_k_neg y i
    · simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_k,
        GeneratorTuple.toFun_f] using x.k_mul_f_mul_k_neg y i
    · simpa only [map_sub, map_mul, map_smul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_e,
        GeneratorTuple.toFun_f, GeneratorTuple.toFun_k] using x.e_mul_f_sub_f_mul_e_self i
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply, GeneratorTuple.toFun_e,
        GeneratorTuple.toFun_f] using x.e_mul_f_of_ne hij
    · simpa only [AlgHom.map_serreElement, map_zero, Function.comp_def, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun_e] using x.serre_e hij
    · simpa only [AlgHom.map_serreElement, map_zero, Function.comp_def, FreeAlgebra.lift_ι_apply,
        GeneratorTuple.toFun_f] using x.serre_f hij⟩

/-- `lift` takes each generator symbol to its image in the tuple. -/
@[simp]
theorem lift_generator (x : GeneratorTuple D q A) (g : Generator ι Y) :
    lift x (generator D q g) = x.toFun g :=
  (RingQuot.liftAlgHom_mkAlgHom_apply K _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)

/-- `lift` sends `Eᵢ` to the `i`-th raising element of the tuple. -/
theorem lift_e (x : GeneratorTuple D q A) (i : ι) : lift x (e D q i) = x.e i :=
  lift_generator x (.e i)

/-- `lift` sends `Fᵢ` to the `i`-th lowering element of the tuple. -/
theorem lift_f (x : GeneratorTuple D q A) (i : ι) : lift x (f D q i) = x.f i :=
  lift_generator x (.f i)

/-- `lift` sends `K_y` to the `y`-th toral element of the tuple. -/
theorem lift_k (x : GeneratorTuple D q A) (y : Y) : lift x (k D q y) = x.k y :=
  lift_generator x (.k y)

/-- Two algebra homomorphisms out of `QuantizedEnvelopingAlgebra D q` agreeing on `Eᵢ`, `Fᵢ`, and
`K_y` are equal. -/
@[ext high]
theorem hom_ext {φ ψ : QuantizedEnvelopingAlgebra D q →ₐ[K] A}
    (he : ∀ i, φ (e D q i) = ψ (e D q i))
    (hf : ∀ i, φ (f D q i) = ψ (f D q i))
    (hk : ∀ y, φ (k D q y) = ψ (k D q y)) : φ = ψ := by
  apply RingQuot.ringQuot_ext' K φ ψ
  apply FreeAlgebra.hom_ext
  funext g
  cases g with
  | e i => exact he i
  | f i => exact hf i
  | k y => exact hk y

/-- Algebra maps out of `QuantizedEnvelopingAlgebra D q` correspond bijectively to
`GeneratorTuple`s in the target algebra. -/
noncomputable def liftEquiv : (QuantizedEnvelopingAlgebra D q →ₐ[K] A) ≃ GeneratorTuple D q A where
  toFun φ :=
    { e := fun i => φ (e D q i)
      f := fun i => φ (f D q i)
      k := fun y => φ (k D q y)
      k_zero := by rw [← map_one φ, ← k_zero D q]
      k_mul_k := fun y z => by rw [← map_mul, k_mul_k]
      k_mul_e_mul_k_neg := fun y i => by
        simpa only [map_mul, map_smul] using congrArg φ (k_mul_e_mul_k_neg D q y i)
      k_mul_f_mul_k_neg := fun y i => by
        simpa only [map_mul, map_smul] using congrArg φ (k_mul_f_mul_k_neg D q y i)
      e_mul_f_sub_f_mul_e_self := fun i => by
        simpa only [map_sub, map_mul, map_smul] using congrArg φ (e_mul_f_sub_f_mul_e_self D q i)
      e_mul_f_of_ne := fun hij => by
        simpa only [map_mul] using congrArg φ (e_mul_f_of_ne D q hij)
      serre_e := fun hij => by
        simpa only [AlgHom.map_serreElement, map_zero, Function.comp_def] using
          congrArg φ (serre_e D q hij)
      serre_f := fun hij => by
        simpa only [AlgHom.map_serreElement, map_zero, Function.comp_def] using
          congrArg φ (serre_f D q hij) }
  invFun := lift
  left_inv φ := hom_ext (by simp) (by simp) (by simp)
  right_inv x := by ext <;> simp

@[simp]
theorem liftEquiv_apply_e (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).e i = φ (e D q i) := (rfl)

@[simp]
theorem liftEquiv_apply_f (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).f i = φ (f D q i) := (rfl)

@[simp]
theorem liftEquiv_apply_k (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (y : Y) :
    (liftEquiv φ).k y = φ (k D q y) := (rfl)

@[simp]
theorem liftEquiv_symm_apply (x : GeneratorTuple D q A) : liftEquiv.symm x = lift x := (rfl)

end Lift

/-- The presentation generators generate the entire `K`-algebra `QuantizedEnvelopingAlgebra D q`. -/
theorem adjoin_range_generator :
    Algebra.adjoin K (Set.range (generator D q)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  have h : FreeAlgebra.lift K (generator D q) = mkAlgHom D q := by
    apply FreeAlgebra.hom_ext
    funext g
    simp
  rw [h, AlgHom.range_eq_top]
  exact RingQuot.mkAlgHom_surjective K (Relation D q)

/-- Induction principle for `QuantizedEnvelopingAlgebra D q`: a predicate holding on scalars and all
generators `Eᵢ`, `Fᵢ`, `K_y`, and closed under sums and products, holds on the whole algebra. -/
@[elab_as_elim]
theorem induction {D : CartanDatum ι X Y} {q : K} {C : QuantizedEnvelopingAlgebra D q → Prop}
    (algebraMap : ∀ r, C (algebraMap K (QuantizedEnvelopingAlgebra D q) r))
    (e : ∀ i, C (QuantizedEnvelopingAlgebra.e D q i))
    (f : ∀ i, C (QuantizedEnvelopingAlgebra.f D q i))
    (k : ∀ y, C (QuantizedEnvelopingAlgebra.k D q y))
    (mul : ∀ a b, C a → C b → C (a * b))
    (add : ∀ a b, C a → C b → C (a + b))
    (x : QuantizedEnvelopingAlgebra D q) : C x := by
  have hx : x ∈ Algebra.adjoin K (Set.range (generator D q)) := by
    rw [adjoin_range_generator]
    exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    cases g with
    | e i => exact e i
    | f i => exact f i
    | k y => exact k y
  | algebraMap r => exact algebraMap r
  | add a b _ _ ha hb => exact add a b ha hb
  | mul a b _ _ ha hb => exact mul a b ha hb

/-- An element commuting with all `Eᵢ`, `Fᵢ`, and `K_y` commutes with every element of
`QuantizedEnvelopingAlgebra D q`. -/
theorem commute_of_commute_generators {D : CartanDatum ι X Y} {q : K}
    {z : QuantizedEnvelopingAlgebra D q}
    (he : ∀ i, Commute (e D q i) z)
    (hf : ∀ i, Commute (f D q i) z)
    (hk : ∀ y, Commute (k D q y) z)
    (x : QuantizedEnvelopingAlgebra D q) : Commute x z := by
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (R := K)
    (s := Set.range (generator D q)) ?_ ?_).symm
  · rw [adjoin_range_generator]
    exact Algebra.mem_top
  · rintro _ ⟨g, rfl⟩
    cases g with
    | e i => exact (he i).symm
    | f i => exact (hf i).symm
    | k y => exact (hk y).symm

/-- For a root-annihilating coweight `c ∈ Y` (`⟨αᵢ, c⟩ = 0` for all `i`), `K_c` commutes with every
element of `QuantizedEnvelopingAlgebra D q`. -/
theorem commute_k_of_forall_pairing_root_eq_zero {D : CartanDatum ι X Y} {q : K} {c : Y}
    (hc : ∀ i, D.pairing (D.root i) c = 0) (x : QuantizedEnvelopingAlgebra D q) :
    Commute (k D q c) x := by
  refine (commute_of_commute_generators (z := k D q c)
    (fun i => ?_) (fun i => ?_) (fun y => k_commute D q y c) x).symm
  · rw [Commute, SemiconjBy, e_mul_k, hc i, neg_zero, zpow_zero, one_smul]
  · rw [Commute, SemiconjBy, f_mul_k, hc i, zpow_zero, one_smul]

/-- For a root-annihilating coweight `c ∈ Y` (`⟨αᵢ, c⟩ = 0` for all `i`), `K_c` lies in the center
of `QuantizedEnvelopingAlgebra D q`. -/
theorem k_mem_center_of_forall_pairing_root_eq_zero {D : CartanDatum ι X Y} {q : K} {c : Y}
    (hc : ∀ i, D.pairing (D.root i) c = 0) :
    k D q c ∈ Subalgebra.center K (QuantizedEnvelopingAlgebra D q) := by
  rw [Subalgebra.mem_center_iff]
  intro x
  exact (commute_k_of_forall_pairing_root_eq_zero hc x).symm

/-! ### Functoriality in the Cartan datum -/

section Map

variable {X' Y' X'' Y'' : Type*} [AddCommGroup X'] [AddCommGroup Y']
  [AddCommGroup X''] [AddCommGroup Y'']
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}

/-- A morphism of Cartan data `φ : D → D'` induces an algebra homomorphism
`QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q` sending `Eᵢ ↦ Eᵢ`,
`Fᵢ ↦ Fᵢ`, and `K_y ↦ K_(φ y)`. -/
noncomputable def map (q : K) (φ : CartanDatum.Hom D D') :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q :=
  lift
    { e := e D' q
      f := f D' q
      k := fun y => k D' q (φ.toLinearMap y)
      k_zero := by simp
      k_mul_k := fun y z => by rw [k_mul_k, map_add]
      k_mul_e_mul_k_neg := fun y i => by
        rw [map_neg, k_mul_e_mul_k_neg, φ.pairing_root_map]
      k_mul_f_mul_k_neg := fun y i => by
        rw [map_neg, k_mul_f_mul_k_neg, φ.pairing_root_map]
      e_mul_f_sub_f_mul_e_self := fun i => by
        rw [map_neg, φ.map_simpleTorus, e_mul_f_sub_f_mul_e_self, φ.symmetrizer_eq]
      e_mul_f_of_ne := fun hij => e_mul_f_of_ne D' q hij
      serre_e := fun {i j} hij => by
        have hs := serre_e D' q hij
        rwa [serreElement_def, serreLength_of_hom φ, φ.symmetrizer_eq, ← serreElement_def] at hs
      serre_f := fun {i j} hij => by
        have hs := serre_f D' q hij
        rwa [serreElement_def, serreLength_of_hom φ, φ.symmetrizer_eq, ← serreElement_def] at hs }

@[simp]
theorem map_e (q : K) (φ : CartanDatum.Hom D D') (i : ι) :
    map q φ (e D q i) = e D' q i :=
  lift_e _ i

@[simp]
theorem map_f (q : K) (φ : CartanDatum.Hom D D') (i : ι) :
    map q φ (f D q i) = f D' q i :=
  lift_f _ i

@[simp]
theorem map_k (q : K) (φ : CartanDatum.Hom D D') (y : Y) :
    map q φ (k D q y) = k D' q (φ.toLinearMap y) :=
  lift_k _ y

@[simp]
theorem map_id (D : CartanDatum ι X Y) (q : K) :
    map q (CartanDatum.Hom.id D) = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext <;> simp

theorem map_comp (q : K) (ψ : CartanDatum.Hom D' D'') (φ : CartanDatum.Hom D D') :
    map q (ψ.comp φ) = (map q ψ).comp (map q φ) := by
  ext <;> simp

end Map

/-! ### The empty-root torus -/

section Torus

/-- When `ι` is empty, `QuantizedEnvelopingAlgebra D q` is canonically isomorphic to the group
algebra `AddMonoidAlgebra K Y` of the full coweight lattice `Y`. -/
noncomputable def torusEquiv [IsEmpty ι] :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] AddMonoidAlgebra K Y :=
  AlgEquiv.ofAlgHom
    (lift
      { e := isEmptyElim
        f := isEmptyElim
        k := fun y => AddMonoidAlgebra.single y 1
        k_zero := AddMonoidAlgebra.one_def.symm
        k_mul_k := fun y z => by
          rw [AddMonoidAlgebra.single_mul_single, one_mul]
        k_mul_e_mul_k_neg := fun _ i => isEmptyElim i
        k_mul_f_mul_k_neg := fun _ i => isEmptyElim i
        e_mul_f_sub_f_mul_e_self := isEmptyElim
        e_mul_f_of_ne := fun {i} => isEmptyElim i
        serre_e := fun {i} => isEmptyElim i
        serre_f := fun {i} => isEmptyElim i })
    (AddMonoidAlgebra.lift K (QuantizedEnvelopingAlgebra D q) Y
      ((Units.coeHom (QuantizedEnvelopingAlgebra D q)).comp (kUnits D q)))
    (by
      ext y
      simp)
    (by
      ext i
      · exact isEmptyElim i
      · exact isEmptyElim i
      · simp)

@[simp]
theorem torusEquiv_k [IsEmpty ι] (y : Y) :
    torusEquiv D q (k D q y) = AddMonoidAlgebra.single y 1 :=
  lift_k _ y

@[simp]
theorem torusEquiv_symm_single [IsEmpty ι] (y : Y) (r : K) :
    (torusEquiv D q).symm (AddMonoidAlgebra.single y r) = r • k D q y := by
  simp [torusEquiv]

end Torus

/-! ### Checks on concrete Cartan data -/

section Checks

-- Adjoint `A₁` (`Y = ℤ`, coroot `h = 2`, root `α(y) = y`, fundamental coweight `ϖ = 1`) at `q = 2`:
-- `K_ϖ E K_(-ϖ) = 2 E`, whereas `K₁ E K₁⁻¹ = K_h E K_(-h) = 4 E`.
example :
    let D := CartanDatum.rankOne (Y := ℤ) (.id : Module.Dual ℤ ℤ) 2 rfl
    k D (2 : ℚ) 1 * e D (2 : ℚ) () * k D (2 : ℚ) (-1) = (2 : ℚ) • e D (2 : ℚ) () ∧
      simpleK D (2 : ℚ) () * e D (2 : ℚ) () * simpleKInv D (2 : ℚ) () =
        (4 : ℚ) • e D (2 : ℚ) () := by
  intro D
  have h₁ := k_mul_e_mul_k_neg D (2 : ℚ) 1 ()
  have h₂ := k_mul_e_mul_k_neg D (2 : ℚ) (D.simpleTorus ()) ()
  rw [D.pairing_root_simpleTorus_self] at h₂
  refine ⟨?_, ?_⟩
  · simpa [D] using h₁
  · norm_num [D] at h₂ ⊢
    exact h₂

-- Empty `ι` on `Y = ℤ`: the toral generators `K_n` (`n : ℤ`) are linearly independent, transported
-- from the standard basis of `K[ℤ]`.
example (K : Type*) [Field K] (q : K) :
    let D : CartanDatum Empty (Module.Dual ℤ ℤ) ℤ :=
      { pairing := .id
        root := Empty.elim
        coroot := Empty.elim
        linearIndependent_root := linearIndependent_empty_type
        linearIndependent_coroot := linearIndependent_empty_type
        pairing_root_coroot_self i := i.elim
        pairing_root_coroot_nonpos {i} := i.elim
        symmetrizer := Empty.elim
        symmetrizer_pos i := i.elim
        symmetrizer_mul_pairing i := i.elim }
    LinearIndependent K (k D q) := by
  intro D
  have hcomp :
      (fun n : ℤ => torusEquiv D q (k D q n)) = AddMonoidAlgebra.basis ℤ K := by
    funext n
    simp
  have hli : LinearIndependent K (fun n : ℤ => torusEquiv D q (k D q n)) := by
    rw [hcomp]
    exact (AddMonoidAlgebra.basis ℤ K).linearIndependent
  exact hli.of_comp (torusEquiv D q).toLinearMap

end Checks

end QuantizedEnvelopingAlgebra

end TauCeti
