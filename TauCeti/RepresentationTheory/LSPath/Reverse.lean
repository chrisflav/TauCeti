/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Combinatorics
public import TauCeti.RepresentationTheory.LSPath.Lower

import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Reversal duality and raising stability for Lakshmibai–Seshadri paths

Let `λ` be a dominant weight for a base `b` of a finite reduced root datum and `w₀` be the longest
element of the Weyl group. Conjugation by `w₀` carries the stabilizer `W_λ` onto the stabilizer
`W_{-w₀ λ}` of the dual dominant weight `-w₀ λ`, and right multiplication by `w₀` reverses saturated
chains of `W / W_λ` into saturated chains of `W / W_{-w₀ λ}`
(`CoxeterSystem.MinimalCosetRepChain.reverseMul`) while preserving their reflection bonds
(`RootPairing.reflectionBond_neg_neg`).

Reversing the directions of a Lakshmibai–Seshadri path `(τ₀, …, τ_l; a₀, …, a_{l+1})` of shape `λ`
and replacing each break `a_k` by `1 - a_{l+1-k}` therefore yields a Lakshmibai–Seshadri path of
shape `-w₀ λ`. This gives an involutive bijection
`TauCeti.LSPath.reverse : LSPath P b λ ≃ LSPath P b (-(longestElement P b • λ))`
whose realized piecewise-linear path is the path reversal `π.reverse`
(`TauCeti.LSPath.toPLPath_reverse`).

Combining reversal duality with Littelmann's lowering stability
(`TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`) immediately yields stability under the
raising operators (`TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`).

## Main definitions

* `TauCeti.LSPath.reverse`: Littelmann's reversal bijection
  `LSPath P b λ ≃ LSPath P b (-(longestElement P b • λ))`.

## Main results

* `TauCeti.longestElement_mul_mem_parabolic_wallIndices_iff`: conjugation by `w₀` carries the
  parabolic subgroup `W_λ` onto `W_{-w₀ λ}`.
* `TauCeti.bondGcd_reverseMul` and `TauCeti.isAChain_reverseMul_iff`: reversing a saturated chain
  by `w₀` preserves its bond gcd and carries `a`-chains to `(1 - a)`-chains.
* `TauCeti.LSPath.timed_reverse` and `TauCeti.LSPath.toPLPath_reverse`: path reversal on LS
  encodings realizes `PLPath.reverseTimed` and `PLPath.reverse`.
* `TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`: **Littelmann's raising operator preserves
  Lakshmibai–Seshadri paths.**

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329–346, §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499–525, §§2, 4.
-/

public section

universe u w x

namespace TauCeti

open RootPairing

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]

/-! ### Parabolic subgroups and chains under the longest element -/

/-- Conjugation by the longest element `w₀` carries the wall parabolic subgroup of a dominant
weight `λ` onto the wall parabolic subgroup of the dual dominant weight `-w₀ λ`. -/
theorem longestElement_mul_mem_parabolic_wallIndices_iff {lam : M}
    (hlam : lam ∈ dominantChamber P b) (p : P.weylGroup) :
    longestElement P b * p * longestElement P b ∈
        (weylCoxeterSystem P b).parabolic (P.wallIndices b (-(longestElement P b • lam))) ↔
      p ∈ (weylCoxeterSystem P b).parabolic (P.wallIndices b lam) := by
  have := P.flip_isReduced
  have hlam' : -(longestElement P b • lam) ∈ dominantChamber P b :=
    neg_smul_mem_dominantChamber_longestElement hlam
  rw [P.parabolic_wallIndices_eq_stabilizer b hlam, P.parabolic_wallIndices_eq_stabilizer b hlam',
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  simp only [smul_neg, mul_smul, smul_smul_longestElement, neg_inj]
  exact ⟨fun h ↦ by simpa [smul_smul_longestElement] using congrArg (longestElement P b • ·) h,
    fun h ↦ by rw [h]⟩

/-- The minimal coset representative of `w w₀` in `W / W_{-w₀ λ}` carries `-w₀ λ` to `-w λ`. -/
theorem minimalCosetRep_mul_longestElement_smul {lam : M} (hlam : lam ∈ dominantChamber P b)
    (w : P.weylGroup) :
    (weylCoxeterSystem P b).minimalCosetRep
        (P.wallIndices b (-(longestElement P b • lam))) (w * longestElement P b) •
        (-(longestElement P b • lam)) =
      -(w • lam) := by
  have := P.flip_isReduced
  have hlam' : -(longestElement P b • lam) ∈ dominantChamber P b :=
    neg_smul_mem_dominantChamber_longestElement hlam
  have hmem := (weylCoxeterSystem P b).inv_mul_minimalCosetRep_mem
    (P.wallIndices b (-(longestElement P b • lam))) (w * longestElement P b)
  rw [(inv_mul_mem_parabolic_wallIndices_iff hlam').mp hmem, smul_neg, mul_smul,
    smul_smul_longestElement]

private theorem reflectionBond_reverseMul {lam : M} (hlam : lam ∈ dominantChamber P b)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam))
    (i : Fin (C.reverseMul (P.isLongest_longestElement b)
      (longestElement_mul_mem_parabolic_wallIndices_iff hlam)).length) :
    P.reflectionBond b
        (((C.reverseMul (P.isLongest_longestElement b)
          (longestElement_mul_mem_parabolic_wallIndices_iff hlam)) i.castSucc).1 •
            (-(longestElement P b • lam)))
        (((C.reverseMul (P.isLongest_longestElement b)
          (longestElement_mul_mem_parabolic_wallIndices_iff hlam)) i.succ).1 •
            (-(longestElement P b • lam))) =
      P.reflectionBond b
        ((C (Fin.rev (i.cast (by simp))).castSucc).1 • lam)
        ((C (Fin.rev (i.cast (by simp))).succ).1 • lam) := by
  simp only [CoxeterSystem.MinimalCosetRepChain.reverseMul_apply]
  rw [minimalCosetRep_mul_longestElement_smul hlam, minimalCosetRep_mul_longestElement_smul hlam,
    P.reflectionBond_neg_neg]
  have hi : i.val < C.length := by simpa using i.isLt
  have h₁ : Fin.rev (⟨i.castSucc, by simp; omega⟩ : Fin (C.length + 1)) =
      (Fin.rev (i.cast (by simp))).succ :=
    Fin.ext (by simp; omega)
  have h₂ : Fin.rev (⟨i.succ, by simp; omega⟩ : Fin (C.length + 1)) =
      (Fin.rev (i.cast (by simp))).castSucc :=
    Fin.ext (by simp)
  rw [h₁, h₂]

/-- Reversing a saturated chain of `W / W_λ` by the longest element preserves its bond gcd. -/
theorem bondGcd_reverseMul {lam : M} (hlam : lam ∈ dominantChamber P b)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)) :
    bondGcd (-(longestElement P b • lam))
        (C.reverseMul (P.isLongest_longestElement b)
          (longestElement_mul_mem_parabolic_wallIndices_iff hlam)) =
      bondGcd lam C := by
  set C' := C.reverseMul (P.isLongest_longestElement b)
    (longestElement_mul_mem_parabolic_wallIndices_iff hlam)
  have hlen : C'.length = C.length := CoxeterSystem.MinimalCosetRepChain.length_reverseMul ..
  apply Nat.dvd_antisymm
  · rw [dvd_bondGcd_iff]
    intro i
    let j : Fin C'.length := (Fin.rev i).cast hlen.symm
    have h := bondGcd_dvd (lam := -(longestElement P b • lam)) (C := C') j
    rw [reflectionBond_reverseMul hlam C j] at h
    simpa [j] using h
  · rw [dvd_bondGcd_iff]
    intro i
    rw [reflectionBond_reverseMul hlam C i]
    exact bondGcd_dvd _

/-- Reversing a saturated chain of `W / W_λ` by the longest element turns `a`-chains into
`(1 - a)`-chains. -/
theorem isAChain_reverseMul_iff {a : ℚ} {lam : M} (hlam : lam ∈ dominantChamber P b)
    (C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam)) :
    IsAChain (1 - a) (-(longestElement P b • lam))
        (C.reverseMul (P.isLongest_longestElement b)
          (longestElement_mul_mem_parabolic_wallIndices_iff hlam)) ↔
      IsAChain a lam C := by
  set C' := C.reverseMul (P.isLongest_longestElement b)
    (longestElement_mul_mem_parabolic_wallIndices_iff hlam)
  have hlen : C'.length = C.length := CoxeterSystem.MinimalCosetRepChain.length_reverseMul ..
  have hsub (r : ℚ) (z : ℤ) : (∃ m : ℤ, (1 - r) * z = m) ↔ (∃ m : ℤ, r * z = m) := by
    refine ⟨fun ⟨m, hm⟩ ↦ ⟨z - m, ?_⟩, fun ⟨m, hm⟩ ↦ ⟨z - m, ?_⟩⟩ <;>
      · push_cast
        linarith
  simp only [isAChain_iff_forall_reflectionBond]
  constructor
  · intro h i
    let j : Fin C'.length := (Fin.rev i).cast hlen.symm
    have hj := h j
    rw [reflectionBond_reverseMul hlam C j] at hj
    exact (hsub a _).mp (by simpa [j] using hj)
  · intro h i
    rw [reflectionBond_reverseMul hlam C i]
    exact (hsub a _).mpr (h _)

/-! ### Reversal of Lakshmibai–Seshadri paths -/

namespace LSPath

private noncomputable def reverseAux {lam lam' : M} (hlam : lam ∈ dominantChamber P b)
    (h : lam' = -(longestElement P b • lam)) (π : LSPath P b lam) : LSPath P b lam' where
  length := π.length
  dir j :=
    ⟨(weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b lam')
      ((π.dir (Fin.rev j)).1 * longestElement P b),
      (weylCoxeterSystem P b).isMinimalCosetRep_minimalCosetRep _ _⟩
  time k := 1 - π.time (Fin.rev k)
  time_zero := by simp [π.time_last]
  time_last := by simp [π.time_zero]
  strictMono_time i j hij := sub_lt_sub_left (π.strictMono_time (Fin.rev_lt_rev.mpr hij)) 1
  dir_succ_ne j hEq := by
    have := P.flip_isReduced
    have hval := congrArg (fun x ↦ x.1 • lam') hEq
    dsimp only at hval
    subst h
    rw [minimalCosetRep_mul_longestElement_smul hlam,
      minimalCosetRep_mul_longestElement_smul hlam, neg_inj] at hval
    have h₁ : Fin.rev j.succ = (Fin.rev j).castSucc := Fin.ext (by simp)
    have h₂ : Fin.rev j.castSucc = (Fin.rev j).succ := Fin.ext (by simp; omega)
    rw [h₁, h₂] at hval
    have heq := eq_of_isMinimalCosetRep_of_smul_eq hlam
      (π.dir (Fin.rev j).castSucc).2 (π.dir (Fin.rev j).succ).2 hval
    exact π.dir_succ_ne (Fin.rev j) (Subtype.ext heq.symm)
  exists_isAChain j := by
    subst h
    obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain (Fin.rev j)
    refine ⟨C.reverseMul (P.isLongest_longestElement b)
      (longestElement_mul_mem_parabolic_wallIndices_iff hlam), ?_, ?_, ?_⟩
    · apply Subtype.ext
      have hidx : (Fin.rev j).succ = Fin.rev j.castSucc := Fin.ext (by simp; omega)
      rw [CoxeterSystem.MinimalCosetRepChain.head_reverseMul, hlast, hidx]
    · apply Subtype.ext
      have hidx : (Fin.rev j).castSucc = Fin.rev j.succ := Fin.ext (by simp)
      rw [CoxeterSystem.MinimalCosetRepChain.last_reverseMul, hhead, hidx]
    · have htime : Fin.rev j.castSucc.succ = (Fin.rev j).castSucc.succ :=
        Fin.ext (by simp; omega)
      rw [htime]
      exact (isAChain_reverseMul_iff hlam C).mpr hC

private theorem reverseAux_reverseAux {lam lam' : M} (hlam : lam ∈ dominantChamber P b)
    (h : lam' = -(longestElement P b • lam)) (π : LSPath P b lam) :
    have := P.flip_isReduced
    reverseAux (h ▸ neg_smul_mem_dominantChamber_longestElement hlam)
      (by simp [h, smul_neg, smul_smul_longestElement]) (reverseAux hlam h π) = π := by
  have := P.flip_isReduced
  subst h
  apply LSPath.ext
  · apply List.ext_get
    · simp [reverseAux]
    · intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn, reverseAux]
      apply Subtype.ext
      dsimp only
      have hJK := longestElement_mul_mem_parabolic_wallIndices_iff hlam
      have hrev : Fin.rev (Fin.rev (⟨n, by simpa [reverseAux] using h₁⟩ : Fin (π.length + 1))) =
          ⟨n, by simpa using h₂⟩ :=
        Fin.ext (by simp)
      rw [hrev]
      exact (P.isLongest_longestElement b).minimalCosetRep_mul_minimalCosetRep_mul hJK
        (π.dir ⟨n, by simpa using h₂⟩).2
  · apply List.ext_get
    · simp [reverseAux]
    · intro n h₁ h₂
      simp only [List.get_eq_getElem, List.getElem_ofFn, reverseAux, Fin.rev_rev, sub_sub_cancel]

/-- **Littelmann's path reversal on Lakshmibai–Seshadri paths.** Reversing the directions and
replacing each break `a_k` by `1 - a_{l+1-k}` gives a bijection between LS paths of dominant shape
`λ` and LS paths of dual dominant shape `-w₀ λ`, realizing piecewise-linear path reversal
(`TauCeti.LSPath.toPLPath_reverse`). -/
noncomputable def reverse {lam : M} (hlam : lam ∈ dominantChamber P b) :
    LSPath P b lam ≃ LSPath P b (-(longestElement P b • lam)) where
  toFun := reverseAux hlam rfl
  invFun :=
    have := P.flip_isReduced
    reverseAux (neg_smul_mem_dominantChamber_longestElement hlam)
      (by simp [smul_neg, smul_smul_longestElement])
  left_inv π := reverseAux_reverseAux hlam rfl π
  right_inv π := by
    have := P.flip_isReduced
    exact reverseAux_reverseAux (neg_smul_mem_dominantChamber_longestElement hlam)
      (by simp [smul_neg, smul_smul_longestElement]) π

section ReverseAPI

variable {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam)

@[simp]
theorem length_reverse : (reverse hlam π).length = π.length :=
  (rfl)

@[simp]
theorem dir_reverse (j : Fin ((reverse hlam π).length + 1)) :
    ((reverse hlam π).dir j).1 =
      (weylCoxeterSystem P b).minimalCosetRep
        (P.wallIndices b (-(longestElement P b • lam)))
        ((π.dir (Fin.rev (j.cast (by rw [length_reverse])))).1 * longestElement P b) :=
  (rfl)

/-- Each direction of the reversed LS path carries `-w₀ λ` to the negative of the corresponding
direction of `π` on `λ`. -/
theorem dir_reverse_smul (j : Fin ((reverse hlam π).length + 1)) :
    ((reverse hlam π).dir j).1 • (-(longestElement P b • lam)) =
      -((π.dir (Fin.rev (j.cast (by rw [length_reverse])))).1 • lam) :=
  minimalCosetRep_mul_longestElement_smul hlam _

@[simp]
theorem time_reverse (k : Fin ((reverse hlam π).length + 2)) :
    (reverse hlam π).time k = 1 - π.time (Fin.rev (k.cast (by rw [length_reverse]))) :=
  (rfl)

@[simp]
theorem duration_reverse (j : Fin ((reverse hlam π).length + 1)) :
    (reverse hlam π).duration j = π.duration (Fin.rev (j.cast (by rw [length_reverse]))) := by
  set j' : Fin (π.length + 1) := j.cast (by rw [length_reverse])
  have hj : j.val ≤ π.length := Nat.lt_succ_iff.mp (by simpa [length_reverse] using j.isLt)
  have h₁ : Fin.rev (j.succ.cast (by rw [length_reverse])) = (Fin.rev j').castSucc :=
    Fin.ext (by simp [j'])
  have h₂ : Fin.rev (j.castSucc.cast (by rw [length_reverse])) = (Fin.rev j').succ :=
    Fin.ext (by simp [j']; omega)
  simp only [duration_def, time_reverse, h₁, h₂]
  ring

@[simp]
theorem length_reverse_symm (π' : LSPath P b (-(longestElement P b • lam))) :
    ((reverse hlam).symm π').length = π'.length :=
  (rfl)

@[simp]
theorem dir_reverse_symm (π' : LSPath P b (-(longestElement P b • lam)))
    (j : Fin (((reverse hlam).symm π').length + 1)) :
    (((reverse hlam).symm π').dir j).1 =
      (weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b lam)
        ((π'.dir (Fin.rev (j.cast (by rw [length_reverse_symm])))).1 * longestElement P b) :=
  (rfl)

/-- Each direction of the inverse reversed LS path carries `λ` to the negative of the corresponding
direction of `π'` on `-w₀ λ`. -/
theorem dir_reverse_symm_smul (π' : LSPath P b (-(longestElement P b • lam)))
    (j : Fin (((reverse hlam).symm π').length + 1)) :
    (((reverse hlam).symm π').dir j).1 • lam =
      -((π'.dir (Fin.rev (j.cast (by rw [length_reverse_symm])))).1 •
        (-(longestElement P b • lam))) := by
  have := P.flip_isReduced
  have hlam' := neg_smul_mem_dominantChamber_longestElement hlam
  have h := minimalCosetRep_mul_longestElement_smul hlam'
    (π'.dir (Fin.rev (j.cast (by rw [length_reverse_symm])))).1
  simpa [smul_neg, smul_smul_longestElement] using h

@[simp]
theorem time_reverse_symm (π' : LSPath P b (-(longestElement P b • lam)))
    (k : Fin (((reverse hlam).symm π').length + 2)) :
    ((reverse hlam).symm π').time k =
      1 - π'.time (Fin.rev (k.cast (by rw [length_reverse_symm]))) :=
  (rfl)

@[simp]
theorem duration_reverse_symm (π' : LSPath P b (-(longestElement P b • lam)))
    (j : Fin (((reverse hlam).symm π').length + 1)) :
    ((reverse hlam).symm π').duration j =
      π'.duration (Fin.rev (j.cast (by rw [length_reverse_symm]))) := by
  set j' : Fin (π'.length + 1) := j.cast (by rw [length_reverse_symm])
  have hj : j.val ≤ π'.length := Nat.lt_succ_iff.mp (by simpa [length_reverse_symm] using j.isLt)
  have h₁ : Fin.rev (j.succ.cast (by rw [length_reverse_symm])) = (Fin.rev j').castSucc :=
    Fin.ext (by simp [j'])
  have h₂ : Fin.rev (j.castSucc.cast (by rw [length_reverse_symm])) = (Fin.rev j').succ :=
    Fin.ext (by simp [j']; omega)
  simp only [duration_def, time_reverse_symm, h₁, h₂]
  ring

section Realization

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Reversing an LS path reverses its distinguished timed presentation. -/
@[simp]
theorem timed_reverse :
    (reverse hlam π).timed 𝕜 f = PLPath.reverseTimed (π.timed 𝕜 f) := by
  apply List.ext_getElem
  · simp [PLPath.reverseTimed_def, timed_def]
  · intro n h₁ h₂
    simp only [timed_def, PLPath.reverseTimed_def, List.getElem_ofFn, List.getElem_map,
      List.getElem_reverse, List.length_map, List.length_ofFn, duration_reverse, dir_reverse_smul]
    have hidx : Fin.rev (⟨n, by simpa [timed_def] using h₁⟩ : Fin (π.length + 1)) =
        ⟨π.length + 1 - 1 - n, by simp [timed_def, PLPath.reverseTimed_def] at h₂; omega⟩ :=
      Fin.ext (by simp)
    rw [map_neg, smul_neg, Fin.cast_mk, hidx]

/-- **Reversing an LS path realizes piecewise-linear path reversal.** -/
@[simp]
theorem toPLPath_reverse :
    (reverse hlam π).toPLPath 𝕜 f = (π.toPLPath 𝕜 f).reverse := by
  rw [toPLPath_def, timed_reverse, PLPath.ofSegments_map_snd_reverseTimed, ← toPLPath_def]

/-- The inverse of `LSPath.reverse` also realizes piecewise-linear path reversal. -/
@[simp]
theorem toPLPath_reverse_symm (π' : LSPath P b (-(longestElement P b • lam))) :
    ((reverse hlam).symm π').toPLPath 𝕜 f = (π'.toPLPath 𝕜 f).reverse := by
  have h := toPLPath_reverse hlam ((reverse hlam).symm π') 𝕜 f
  rw [(reverse hlam).apply_symm_apply] at h
  rw [h, PLPath.reverse_reverse]

end Realization

end ReverseAPI

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths.** Let `π` be an LS path of
dominant shape `λ`, realized in `V` by `f`, let `αᵢ` be a simple root and let `F` be a form on `V`
inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`. If the raising operator `e_αᵢ` is defined on the
path of `π`, then its result is again the path of an LS path of shape `λ`. -/
theorem exists_toPLPath_eq_of_raise_eq_some {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] {lam : M}
    (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support)
    (F : Module.Dual 𝕜 V) (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  have := P.flip_isReduced
  rw [PLPath.raise_def, Option.map_eq_some_iff] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  rw [← toPLPath_reverse hlam π 𝕜 f] at hr
  obtain ⟨ρ, hρ⟩ := exists_toPLPath_eq_of_lower_eq_some (reverse hlam π)
    (neg_smul_mem_dominantChamber_longestElement hlam) f i F hF hr
  exact ⟨(reverse hlam).symm ρ, by rw [toPLPath_reverse_symm, hρ]⟩

end LSPath

end TauCeti
