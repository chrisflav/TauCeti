/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Algebra
public import TauCeti.Analysis.Sobolev.Circle.Derivative
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.Analysis.Normed.Lp.DiscreteConvolution

/-!
# Linear and bilinear pushforwards on the circle Sobolev spaces

A continuous complex-linear map `L : E →L[ℂ] F` acts coefficientwise on the Fourier-coefficient
Sobolev spaces `TauCeti.CircleSobolev s E`, giving a continuous complex-linear operator
`CircleSobolev.mapCLM L : H^s(E) →L[ℂ] H^s(F)` of norm at most `‖L‖` at every real order `s`.

Smooth nonlinear analysis on complex targets also requires pushing Sobolev functions forward along
continuous *real*-linear maps `L : E →L[ℝ] F` and *real*-bilinear pairings
`B : E →L[ℝ] E' →L[ℝ] F` (such as evaluation of real Fréchet derivatives). Because the Fourier
characters `e^{2πinx/T}` are complex scalars, a real-linear map `L` does not act diagonally on
Fourier coefficients: decomposing `L` into `ContinuousLinearMap.complexLinearPart L` and
`ContinuousLinearMap.complexAntilinearPart L` gives
`L (e^{2πinx/T} • v) = e^{2πinx/T} • L¹⁰ v + e^{-2πinx/T} • L⁰¹ v`, so the `n`-th Fourier
coefficient of `L ∘ a` is `L¹⁰ (a.coeff n) + L⁰¹ (a.coeff (-n))`. Similarly, decomposing a
real-bilinear map `B` in each argument reduces the pointwise pairing `x ↦ B (a x) (b x)` for
`s > 1/2` to four discrete convolutions applied to `a`, `b` and their coefficient reflections
`CircleSobolev.reflect`.

## Main definitions

* `TauCeti.CircleSobolev.mapCLM L` and `TauCeti.CircleSobolev.mapCLE e`: the complex-linear
  pushforward `H^s(E) →L[ℂ] H^s(F)` (and continuous linear equivalence) induced by `L : E →L[ℂ] F`
  at any real order `s`.
* `TauCeti.CircleSobolev.mapRealCLM L` and `TauCeti.CircleSobolev.mapRealCLE e`: the real-linear
  pushforward `H^s(E) →L[ℝ] H^s(F)` (and continuous real-linear equivalence) induced by
  `L : E →L[ℝ] F` at any real order `s`.
* `TauCeti.CircleSobolev.realConvolution hs B`: for `s > 1/2` and complete `F`, the continuous
  real-bilinear map `H^s(E) →L[ℝ] H^s(E') →L[ℝ] H^s(F)` induced by `B : E →L[ℝ] E' →L[ℝ] F`.

## Main statements

* `TauCeti.CircleSobolev.toContinuousMap_mapCLM`,
  `TauCeti.CircleSobolev.toContinuousMap_mapRealCLM`, and
  `TauCeti.CircleSobolev.toContinuousMap_realConvolution_apply`: for `s > 1/2`, all three
  constructions act pointwise on continuous representatives.
* `TauCeti.CircleSobolev.derivative_mapCLM` and `TauCeti.CircleSobolev.derivative_mapRealCLM`:
  both linear pushforwards commute with `CircleSobolev.derivative`.
* `TauCeti.CircleSobolev.mapRealCLM_restrictScalars` and
  `TauCeti.CircleSobolev.realConvolution_bilinearRestrictScalars`: when the underlying map is
  complex-linear (or complex-bilinear), the real pushforward agrees with the complex one.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, Section 3 (Sobolev spaces as
  algebras and functoriality under linear and bilinear maps).
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699 (real-linear operators on complex boundary Sobolev
  spaces).
-/

public section

noncomputable section

open Complex ComplexConjugate Real
open scoped DiscreteConvolution
open DiscreteConvolution (AddConvolutionExists
  addConvolutionExists_and_summable_sq_one_add_abs_rpow_mul_norm_addConvolution
  tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le)

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E E' F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-! ### Complex-linear pushforward -/

private theorem memℓp_mapCLM_aux (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    Memℓp (fun n ↦ weight s n • L (a.coeff n)) 2 := by
  rw [memℓp_weight_smul_iff]
  refine Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (fun n ↦ ?_)
    ((hasSum_sq_weight_mul_norm_coeff a).summable.mul_left (‖L‖ ^ 2))
  rw [← mul_pow]
  refine pow_le_pow_left₀ (mul_nonneg (weight_nonneg s n) (norm_nonneg _)) ?_ 2
  calc weight s n * ‖L (a.coeff n)‖
      ≤ weight s n * (‖L‖ * ‖a.coeff n‖) :=
        mul_le_mul_of_nonneg_left (L.le_opNorm _) (weight_nonneg s n)
    _ = ‖L‖ * (weight s n * ‖a.coeff n‖) := by ring

private theorem norm_mapCLM_aux_le (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    ‖(⟨fun n ↦ L (a.coeff n), memℓp_mapCLM_aux L a⟩ : CircleSobolev s F)‖ ≤ ‖L‖ * ‖a‖ := by
  have hle :
      ‖(⟨fun n ↦ L (a.coeff n), memℓp_mapCLM_aux L a⟩ : CircleSobolev s F)‖ ^ 2 ≤
        (‖L‖ * ‖a‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun n ↦ ?_) (hasSum_sq_weight_mul_norm_coeff _)
      ((hasSum_sq_weight_mul_norm_coeff a).mul_left (‖L‖ ^ 2))
    rw [← mul_pow]
    refine pow_le_pow_left₀ (mul_nonneg (weight_nonneg s n) (norm_nonneg _)) ?_ 2
    calc weight s n * ‖L (a.coeff n)‖
        ≤ weight s n * (‖L‖ * ‖a.coeff n‖) :=
          mul_le_mul_of_nonneg_left (L.le_opNorm _) (weight_nonneg s n)
      _ = ‖L‖ * (weight s n * ‖a.coeff n‖) := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

/-- Pushforward of `H^s(E)` to `H^s(F)` along a continuous complex-linear map `L : E →L[ℂ] F`,
acting coefficientwise on Fourier series. -/
def mapCLM (L : E →L[ℂ] F) : CircleSobolev s E →L[ℂ] CircleSobolev s F :=
  LinearMap.mkContinuous
    { toFun a := ⟨fun n ↦ L (a.coeff n), memℓp_mapCLM_aux L a⟩
      map_add' a b := CircleSobolev.ext <| funext fun n ↦ L.map_add (a.coeff n) (b.coeff n)
      map_smul' c a := CircleSobolev.ext <| funext fun n ↦ L.map_smul c (a.coeff n) }
    ‖L‖ (norm_mapCLM_aux_le L)

@[simp]
theorem coeff_mapCLM (L : E →L[ℂ] F) (a : CircleSobolev s E) (n : ℤ) :
    (mapCLM L a).coeff n = L (a.coeff n) :=
  (rfl)

theorem norm_mapCLM_le (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    ‖mapCLM L a‖ ≤ ‖L‖ * ‖a‖ :=
  norm_mapCLM_aux_le L a

theorem opNorm_mapCLM_le (L : E →L[ℂ] F) :
    ‖(mapCLM L : CircleSobolev s E →L[ℂ] CircleSobolev s F)‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

@[simp]
theorem mapCLM_id :
    (mapCLM (.id ℂ E) : CircleSobolev s E →L[ℂ] CircleSobolev s E) = .id ℂ _ := by
  ext a : 1
  exact CircleSobolev.ext (funext fun _ ↦ rfl)

@[simp]
theorem mapCLM_zero :
    (mapCLM (0 : E →L[ℂ] F) : CircleSobolev s E →L[ℂ] CircleSobolev s F) = 0 := by
  ext a : 1
  exact CircleSobolev.ext (funext fun _ ↦ rfl)

theorem mapCLM_comp (L' : F →L[ℂ] G) (L : E →L[ℂ] F) :
    (mapCLM (L'.comp L) : CircleSobolev s E →L[ℂ] CircleSobolev s G) =
      (mapCLM L').comp (mapCLM L) := by
  ext a : 1
  exact CircleSobolev.ext (funext fun _ ↦ rfl)

@[simp]
theorem mapCLM_comp_apply (L' : F →L[ℂ] G) (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    mapCLM (L'.comp L) a = mapCLM L' (mapCLM L a) :=
  (rfl)

@[simp]
theorem mapCLM_single (L : E →L[ℂ] F) (n : ℤ) (v : E) :
    mapCLM L (single (s := s) n v) = single n (L v) :=
  CircleSobolev.ext <| funext fun m ↦ by
    rcases eq_or_ne m n with rfl | hm
    · simp
    · simp [hm]

@[simp]
theorem inclusion_mapCLM (h : t ≤ s) (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    inclusion h (mapCLM L a) = mapCLM L (inclusion h a) :=
  CircleSobolev.ext <| funext fun _ ↦ by simp

@[simp]
theorem derivative_mapCLM (T : ℝ) [Fact (0 < T)] (h : s + 1 ≤ t) (L : E →L[ℂ] F)
    (a : CircleSobolev t E) :
    derivative T h (mapCLM L a) = mapCLM L (derivative T h a) :=
  CircleSobolev.ext <| funext fun _ ↦ by simp

@[simp]
theorem toContinuousMap_mapCLM (T : ℝ) [Fact (0 < T)] [CompleteSpace E] [CompleteSpace F]
    (hs : 1 / 2 < s) (L : E →L[ℂ] F) (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (mapCLM L a) x = L (toContinuousMap T hs a x) := by
  have heq :
      ((ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs)).comp (mapCLM L) =
        L.comp ((ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs)) :=
    continuousLinearMap_ext_single fun n v ↦ by simp
  exact DFunLike.congr_fun heq a

/-- Pushforward of `H^s(E)` to `H^s(F)` along a continuous complex-linear equivalence
`e : E ≃L[ℂ] F`. -/
def mapCLE (e : E ≃L[ℂ] F) : CircleSobolev s E ≃L[ℂ] CircleSobolev s F :=
  ContinuousLinearEquiv.equivOfInverse (mapCLM (e : E →L[ℂ] F)) (mapCLM (e.symm : F →L[ℂ] E))
    (fun a ↦ by simp [← mapCLM_comp_apply])
    (fun b ↦ by simp [← mapCLM_comp_apply])

@[simp]
theorem coe_mapCLE (e : E ≃L[ℂ] F) :
    (mapCLE (s := s) e : CircleSobolev s E →L[ℂ] CircleSobolev s F) = mapCLM (e : E →L[ℂ] F) :=
  (rfl)

@[simp]
theorem mapCLE_apply (e : E ≃L[ℂ] F) (a : CircleSobolev s E) :
    mapCLE e a = mapCLM (e : E →L[ℂ] F) a :=
  (rfl)

@[simp]
theorem mapCLE_symm (e : E ≃L[ℂ] F) :
    (mapCLE (s := s) e : CircleSobolev s E ≃L[ℂ] CircleSobolev s F).symm = mapCLE e.symm :=
  (rfl)

/-! ### Real-linear pushforward -/

/-- Continuous real-linear maps out of `H^s` are determined by their values on Fourier
monomials. -/
theorem continuousLinearMap_real_ext_single {M : Type*} [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] [T2Space M] {f g : CircleSobolev s E →L[ℝ] M}
    (h : ∀ n x, f (single n x) = g (single n x)) : f = g :=
  ContinuousLinearMap.ext fun a ↦
    ((hasSum_single a).mapL f).unique (by simpa only [h] using (hasSum_single a).mapL g)

@[simp]
theorem reflect_single (n : ℤ) (v : E) :
    reflect (single (s := s) n v) = single (-n) v :=
  CircleSobolev.ext <| funext fun m ↦ by
    simp only [coeff_reflect, coeff_single, Pi.single_apply, neg_eq_iff_eq_neg]

private theorem memℓp_antiPart_reflect (L : E →L[ℝ] F) (a : CircleSobolev s E) :
    Memℓp (fun n ↦ weight s n • L.complexAntilinearPart (a.coeff (-n))) 2 := by
  rw [memℓp_weight_smul_iff]
  refine Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (fun n ↦ ?_)
    ((hasSum_sq_weight_mul_norm_coeff (reflect a)).summable.mul_left (‖L‖ ^ 2))
  rw [← mul_pow, coeff_reflect]
  refine pow_le_pow_left₀ (mul_nonneg (weight_nonneg s n) (norm_nonneg _)) ?_ 2
  calc weight s n * ‖L.complexAntilinearPart (a.coeff (-n))‖
      ≤ weight s n * (‖L.complexAntilinearPart‖ * ‖a.coeff (-n)‖) :=
        mul_le_mul_of_nonneg_left (L.complexAntilinearPart.le_opNorm _) (weight_nonneg s n)
    _ ≤ weight s n * (‖L‖ * ‖a.coeff (-n)‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right L.norm_complexAntilinearPart_le (norm_nonneg _))
          (weight_nonneg s n)
    _ = ‖L‖ * (weight s n * ‖a.coeff (-n)‖) := by ring

private def mapAntiPartCLM (L : E →L[ℝ] F) : CircleSobolev s E →L[ℝ] CircleSobolev s F :=
  LinearMap.mkContinuous
    { toFun a := ⟨fun n ↦ L.complexAntilinearPart (a.coeff (-n)), memℓp_antiPart_reflect L a⟩
      map_add' a b := CircleSobolev.ext <| funext fun n ↦
        L.complexAntilinearPart.map_add (a.coeff (-n)) (b.coeff (-n))
      map_smul' r a := CircleSobolev.ext <| funext fun n ↦ by
        dsimp only
        rw [coeff_real_smul, Pi.smul_apply, ← Complex.coe_smul,
          L.complexAntilinearPart.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul,
          RingHom.id_apply, coeff_real_smul, Pi.smul_apply] }
    ‖L‖ fun a ↦ by
      have hle :
          ‖(⟨fun n ↦ L.complexAntilinearPart (a.coeff (-n)), memℓp_antiPart_reflect L a⟩ :
              CircleSobolev s F)‖ ^ 2 ≤ (‖L‖ * ‖a‖) ^ 2 := by
        rw [mul_pow, ← reflect.norm_map a]
        refine hasSum_le (fun n ↦ ?_) (hasSum_sq_weight_mul_norm_coeff _)
          ((hasSum_sq_weight_mul_norm_coeff (reflect a)).mul_left (‖L‖ ^ 2))
        rw [← mul_pow, coeff_reflect]
        refine pow_le_pow_left₀ (mul_nonneg (weight_nonneg s n) (norm_nonneg _)) ?_ 2
        calc weight s n * ‖L.complexAntilinearPart (a.coeff (-n))‖
            ≤ weight s n * (‖L‖ * ‖a.coeff (-n)‖) := by
              refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg s n)
              exact (L.complexAntilinearPart.le_opNorm _).trans
                (mul_le_mul_of_nonneg_right L.norm_complexAntilinearPart_le (norm_nonneg _))
          _ = ‖L‖ * (weight s n * ‖a.coeff (-n)‖) := by ring
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

@[simp]
private theorem coeff_mapAntiPartCLM (L : E →L[ℝ] F) (a : CircleSobolev s E) (n : ℤ) :
    (mapAntiPartCLM L a).coeff n = L.complexAntilinearPart (a.coeff (-n)) :=
  (rfl)

/-- Pushforward of `H^s(E)` to `H^s(F)` along a continuous real-linear map `L : E →L[ℝ] F`.
On Fourier coefficients it sends `a` to
`n ↦ L.complexLinearPart (a.coeff n) + L.complexAntilinearPart (a.coeff (-n))`, so for
`s > 1/2` it acts pointwise as `L ∘ a` on continuous representatives
(`CircleSobolev.toContinuousMap_mapRealCLM`). -/
def mapRealCLM (L : E →L[ℝ] F) : CircleSobolev s E →L[ℝ] CircleSobolev s F :=
  (mapCLM L.complexLinearPart).restrictScalars ℝ + mapAntiPartCLM L

theorem coeff_mapRealCLM (L : E →L[ℝ] F) (a : CircleSobolev s E) (n : ℤ) :
    (mapRealCLM L a).coeff n =
      L.complexLinearPart (a.coeff n) + L.complexAntilinearPart (a.coeff (-n)) := by
  simp [mapRealCLM]

theorem norm_mapRealCLM_le (L : E →L[ℝ] F) (a : CircleSobolev s E) :
    ‖mapRealCLM L a‖ ≤ 2 * ‖L‖ * ‖a‖ := by
  have h1 : ‖mapCLM L.complexLinearPart a‖ ≤ ‖L‖ * ‖a‖ :=
    (norm_mapCLM_le _ a).trans
      (mul_le_mul_of_nonneg_right L.norm_complexLinearPart_le (norm_nonneg a))
  have h2 : ‖mapAntiPartCLM L a‖ ≤ ‖L‖ * ‖a‖ :=
    (mapAntiPartCLM L).le_opNorm a |>.trans
      (mul_le_mul_of_nonneg_right (LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _)
        (norm_nonneg a))
  calc ‖mapRealCLM L a‖ ≤ ‖mapCLM L.complexLinearPart a‖ + ‖mapAntiPartCLM L a‖ :=
        norm_add_le _ _
    _ ≤ ‖L‖ * ‖a‖ + ‖L‖ * ‖a‖ := add_le_add h1 h2
    _ = 2 * ‖L‖ * ‖a‖ := by ring

theorem opNorm_mapRealCLM_le (L : E →L[ℝ] F) :
    ‖(mapRealCLM L : CircleSobolev s E →L[ℝ] CircleSobolev s F)‖ ≤ 2 * ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_mapRealCLM_le L)

private theorem mapRealCLM_single_eq (L : E →L[ℝ] F) (m : ℤ) (v : E) :
    mapRealCLM L (single (s := s) m v) =
      single m (L.complexLinearPart v) + single (-m) (L.complexAntilinearPart v) := by
  refine CircleSobolev.ext (funext fun n ↦ ?_)
  simp only [coeff_mapRealCLM, coeff_add, Pi.add_apply, coeff_single, Pi.single_apply,
    neg_eq_iff_eq_neg]
  split_ifs <;> simp

@[simp]
theorem mapRealCLM_single_zero (L : E →L[ℝ] F) (v : E) :
    mapRealCLM L (single (s := s) 0 v) = single 0 (L v) := by
  rw [mapRealCLM_single_eq, neg_zero, ← map_add, L.complexLinearPart_add_complexAntilinearPart]

@[simp]
theorem mapRealCLM_restrictScalars (L : E →L[ℂ] F) :
    (mapRealCLM (L.restrictScalars ℝ) : CircleSobolev s E →L[ℝ] CircleSobolev s F) =
      (mapCLM L).restrictScalars ℝ := by
  refine continuousLinearMap_real_ext_single fun m v ↦ ?_
  simp [mapRealCLM_single_eq]

@[simp]
theorem mapRealCLM_restrictScalars_apply (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    mapRealCLM (L.restrictScalars ℝ) a = mapCLM L a :=
  DFunLike.congr_fun (mapRealCLM_restrictScalars L) a

@[simp]
theorem mapRealCLM_id :
    (mapRealCLM (.id ℝ E) : CircleSobolev s E →L[ℝ] CircleSobolev s E) = .id ℝ _ :=
  mapRealCLM_restrictScalars (.id ℂ E)

@[simp]
theorem mapRealCLM_zero :
    (mapRealCLM (0 : E →L[ℝ] F) : CircleSobolev s E →L[ℝ] CircleSobolev s F) = 0 :=
  mapRealCLM_restrictScalars (0 : E →L[ℂ] F)

theorem mapRealCLM_comp (L' : F →L[ℝ] G) (L : E →L[ℝ] F) :
    (mapRealCLM (L'.comp L) : CircleSobolev s E →L[ℝ] CircleSobolev s G) =
      (mapRealCLM L').comp (mapRealCLM L) := by
  refine continuousLinearMap_real_ext_single fun m v ↦ ?_
  obtain ⟨h1, h2⟩ := ContinuousLinearMap.complexLinearPart_eq_and_complexAntilinearPart_eq
    (L := L'.comp L) (v := v)
    (a := L'.complexLinearPart (L.complexLinearPart v) +
      L'.complexAntilinearPart (L.complexAntilinearPart v))
    (b := L'.complexAntilinearPart (L.complexLinearPart v) +
      L'.complexLinearPart (L.complexAntilinearPart v))
    fun z ↦ by
      simp only [ContinuousLinearMap.comp_apply,
        L.apply_smul_eq_complexLinearPart_add_complexAntilinearPart z v, map_add,
        L'.apply_smul_eq_complexLinearPart_add_complexAntilinearPart, conj_conj, smul_add]
      abel
  simp only [ContinuousLinearMap.comp_apply, mapRealCLM_single_eq, map_add, neg_neg, h1, h2]
  abel

@[simp]
theorem mapRealCLM_comp_apply (L' : F →L[ℝ] G) (L : E →L[ℝ] F) (a : CircleSobolev s E) :
    mapRealCLM (L'.comp L) a = mapRealCLM L' (mapRealCLM L a) :=
  DFunLike.congr_fun (mapRealCLM_comp L' L) a

@[simp]
theorem inclusion_mapRealCLM (h : t ≤ s) (L : E →L[ℝ] F) (a : CircleSobolev s E) :
    inclusion h (mapRealCLM L a) = mapRealCLM L (inclusion h a) :=
  CircleSobolev.ext <| funext fun _ ↦ by simp [coeff_mapRealCLM]

@[simp]
theorem derivative_mapRealCLM (T : ℝ) [Fact (0 < T)] (h : s + 1 ≤ t) (L : E →L[ℝ] F)
    (a : CircleSobolev t E) :
    derivative T h (mapRealCLM L a) = mapRealCLM L (derivative T h a) := by
  have heq : ((derivative T h).restrictScalars ℝ).comp (mapRealCLM L) =
      (mapRealCLM L).comp ((derivative T h).restrictScalars ℝ) := by
    refine continuousLinearMap_real_ext_single fun m v ↦ ?_
    have hconj : conj (2 * π * I * m / T : ℂ) = (2 * π * I * (-m : ℤ) / T : ℂ) :=
      Complex.ext (by simp) (by simp)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      mapRealCLM_single_eq, map_add, derivative_single, L.complexLinearPart.map_smul,
      L.complexAntilinearPart.map_smulₛₗ, hconj]
  exact DFunLike.congr_fun heq a

@[simp]
theorem toContinuousMap_mapRealCLM (T : ℝ) [Fact (0 < T)] [CompleteSpace E] [CompleteSpace F]
    (hs : 1 / 2 < s) (L : E →L[ℝ] F) (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (mapRealCLM L a) x = L (toContinuousMap T hs a x) := by
  set evE : CircleSobolev s E →L[ℝ] E :=
    ((ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs)).restrictScalars ℝ
  set evF : CircleSobolev s F →L[ℝ] F :=
    ((ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs)).restrictScalars ℝ
  have heq : evF.comp (mapRealCLM L) = L.comp evE := by
    refine continuousLinearMap_real_ext_single fun m v ↦ ?_
    simp only [evE, evF, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousMap.evalCLM_apply, mapRealCLM_single_eq, map_add, toContinuousMap_single,
      ContinuousMap.smul_apply', ContinuousMap.const_apply,
      L.apply_smul_eq_complexLinearPart_add_complexAntilinearPart, fourier_neg]
  exact DFunLike.congr_fun heq a

/-- Pushforward of `H^s(E)` to `H^s(F)` along a continuous real-linear equivalence
`e : E ≃L[ℝ] F`. -/
def mapRealCLE (e : E ≃L[ℝ] F) : CircleSobolev s E ≃L[ℝ] CircleSobolev s F :=
  ContinuousLinearEquiv.equivOfInverse (mapRealCLM (e : E →L[ℝ] F))
    (mapRealCLM (e.symm : F →L[ℝ] E))
    (fun a ↦ by simp [← mapRealCLM_comp_apply])
    (fun b ↦ by simp [← mapRealCLM_comp_apply])

@[simp]
theorem coe_mapRealCLE (e : E ≃L[ℝ] F) :
    (mapRealCLE (s := s) e : CircleSobolev s E →L[ℝ] CircleSobolev s F) =
      mapRealCLM (e : E →L[ℝ] F) :=
  (rfl)

@[simp]
theorem mapRealCLE_apply (e : E ≃L[ℝ] F) (a : CircleSobolev s E) :
    mapRealCLE e a = mapRealCLM (e : E →L[ℝ] F) a :=
  (rfl)

@[simp]
theorem mapRealCLE_symm (e : E ≃L[ℝ] F) :
    (mapRealCLE (s := s) e : CircleSobolev s E ≃L[ℝ] CircleSobolev s F).symm =
      mapRealCLE e.symm :=
  (rfl)

/-! ### Real-bilinear convolution product for `s > 1/2` -/

section RealConvolution

private def b11 (B : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (ContinuousLinearMap.complexLinearPartCLM E' F).comp
    (ContinuousLinearMap.complexLinearPartCLM E (E' →L[ℝ] F) B)

private def b12 (B : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (ContinuousLinearMap.complexAntilinearPartCLM E' F).comp
    (ContinuousLinearMap.complexLinearPartCLM E (E' →L[ℝ] F) B)

private def b21 (B : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (ContinuousLinearMap.complexLinearPartCLM E' F).comp
    (ContinuousLinearMap.complexAntilinearPartCLM E (E' →L[ℝ] F) B)

private def b22 (B : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (ContinuousLinearMap.complexAntilinearPartCLM E' F).comp
    (ContinuousLinearMap.complexAntilinearPartCLM E (E' →L[ℝ] F) B)

private theorem norm_b11_le (B : E →L[ℝ] E' →L[ℝ] F) : ‖b11 B‖ ≤ ‖B‖ :=
  (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦
    (ContinuousLinearMap.norm_complexLinearPartCLM_apply_le _).trans
      ((ContinuousLinearMap.complexLinearPartCLM E (E' →L[ℝ] F) B).le_opNorm v)).trans
    (ContinuousLinearMap.norm_complexLinearPartCLM_apply_le B)

private theorem norm_b12_le (B : E →L[ℝ] E' →L[ℝ] F) : ‖b12 B‖ ≤ ‖B‖ :=
  (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦
    (ContinuousLinearMap.norm_complexAntilinearPartCLM_apply_le _).trans
      ((ContinuousLinearMap.complexLinearPartCLM E (E' →L[ℝ] F) B).le_opNorm v)).trans
    (ContinuousLinearMap.norm_complexLinearPartCLM_apply_le B)

private theorem norm_b21_le (B : E →L[ℝ] E' →L[ℝ] F) : ‖b21 B‖ ≤ ‖B‖ :=
  (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦
    (ContinuousLinearMap.norm_complexLinearPartCLM_apply_le _).trans
      ((ContinuousLinearMap.complexAntilinearPartCLM E (E' →L[ℝ] F) B).le_opNorm v)).trans
    (ContinuousLinearMap.norm_complexAntilinearPartCLM_apply_le B)

private theorem norm_b22_le (B : E →L[ℝ] E' →L[ℝ] F) : ‖b22 B‖ ≤ ‖B‖ :=
  (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦
    (ContinuousLinearMap.norm_complexAntilinearPartCLM_apply_le _).trans
      ((ContinuousLinearMap.complexAntilinearPartCLM E (E' →L[ℝ] F) B).le_opNorm v)).trans
    (ContinuousLinearMap.norm_complexAntilinearPartCLM_apply_le B)

private def reflectRealCLM (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M] :
    CircleSobolev s M →L[ℝ] CircleSobolev s M :=
  (reflect (s := s) (E := M)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

@[simp]
private theorem reflectRealCLM_apply {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
    (a : CircleSobolev s M) :
    reflectRealCLM M a = reflect a :=
  (rfl)

private theorem summable_sq_weight_mul_norm_coeff' {M : Type*} [NormedAddCommGroup M]
    [NormedSpace ℂ M] (a : CircleSobolev s M) :
    Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a.coeff n‖) ^ 2 := by
  simpa only [weight_def] using (hasSum_sq_weight_mul_norm_coeff a).summable

variable [CompleteSpace F]

private theorem addConvolutionExists_and_memℓp_real (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    AddConvolutionExists L.toLinearMap₁₂ a.coeff b.coeff ∧
      Memℓp (fun n ↦ weight s n • (a.coeff ⋆₊[L.toLinearMap₁₂] b.coeff) n) 2 := by
  obtain ⟨h₁, h₂⟩ := addConvolutionExists_and_summable_sq_one_add_abs_rpow_mul_norm_addConvolution
    L hs (summable_sq_weight_mul_norm_coeff' a) (summable_sq_weight_mul_norm_coeff' b)
  exact ⟨h₁, (memℓp_weight_smul_iff _).2 (by simpa only [weight_def] using h₂)⟩

private def convRealDirectAux (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev s E)
    (b : CircleSobolev s E') : CircleSobolev s F where
  coeff := a.coeff ⋆₊[L.toLinearMap₁₂] b.coeff
  memℓp_weight_smul_coeff := (addConvolutionExists_and_memℓp_real hs L a b).2

private theorem coeff_convRealDirectAux (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    (convRealDirectAux hs L a b).coeff = a.coeff ⋆₊[L.toLinearMap₁₂] b.coeff :=
  (rfl)

private theorem norm_convRealDirectAux_le (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    ‖convRealDirectAux hs L a b‖ ≤
      2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ * ‖a‖ * ‖b‖ := by
  have hK : 0 ≤ ∑' n, weight (-(2 * s)) n := tsum_nonneg fun n ↦ weight_nonneg _ n
  have h := tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le L hs
    (summable_sq_weight_mul_norm_coeff' a) (summable_sq_weight_mul_norm_coeff' b)
  simp only [neg_mul, ← weight_def, ← coeff_convRealDirectAux hs L a b] at h
  rw [(hasSum_sq_weight_mul_norm_coeff _).tsum_eq, (hasSum_sq_weight_mul_norm_coeff _).tsum_eq,
    (hasSum_sq_weight_mul_norm_coeff _).tsum_eq] at h
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h.trans_eq ?_)
  have h4 : ((2 : ℝ) ^ (s + 1)) ^ 2 = 4 ^ (s + 1) := by
    rw [sq, ← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  simp only [mul_pow, Real.sq_sqrt hK, h4]
  ring

private def convRealDirect (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev s E →L[ℝ] CircleSobolev s E' →L[ℝ] CircleSobolev s F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (convRealDirectAux hs L)
      (fun a a' b ↦ CircleSobolev.ext <|
        ((addConvolutionExists_and_memℓp_real hs L a b).1.add_distrib _
          (addConvolutionExists_and_memℓp_real hs L a' b).1))
      (fun r a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        simp only [coeff_convRealDirectAux, DiscreteConvolution.addConvolution_eq_tsum_sub,
          coeff_real_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, tsum_const_smul''])
      (fun a b b' ↦ CircleSobolev.ext <|
        ((addConvolutionExists_and_memℓp_real hs L a b).1.distrib_add _
          (addConvolutionExists_and_memℓp_real hs L a b').1))
      (fun r a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        simp only [coeff_convRealDirectAux, DiscreteConvolution.addConvolution_eq_tsum_sub,
          coeff_real_smul, Pi.smul_apply, map_smul, tsum_const_smul'']))
    (2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖L‖) (norm_convRealDirectAux_le hs L)

@[simp]
private theorem coeff_convRealDirect (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    (convRealDirect hs L a b).coeff = a.coeff ⋆₊[L.toLinearMap₁₂] b.coeff :=
  (rfl)

@[simp]
private theorem convRealDirect_single_single (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (m n : ℤ) (v : E) (w : E') :
    convRealDirect hs L (single m v) (single n w) = single (m + n) (L v w) :=
  CircleSobolev.ext <| by simp

private theorem norm_convRealDirect_le (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    ‖convRealDirect hs L a b‖ ≤
      2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ * ‖a‖ * ‖b‖ :=
  norm_convRealDirectAux_le hs L a b

/-- **The real-bilinear product on `H^s`, `s > 1/2`.** A continuous real-bilinear map
`B : E →L[ℝ] E' →L[ℝ] F` between complex normed spaces (with `F` complete) induces a continuous
real-bilinear map `H^s(E) →L[ℝ] H^s(E') →L[ℝ] H^s(F)` whose continuous representative is the
pointwise pairing `x ↦ B (a x) (b x)` (`CircleSobolev.toContinuousMap_realConvolution_apply`). -/
def realConvolution (hs : 1 / 2 < s) (B : E →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev s E →L[ℝ] CircleSobolev s E' →L[ℝ] CircleSobolev s F :=
  convRealDirect hs (b11 B) +
    (ContinuousLinearMap.compL ℝ _ _ _ |>.flip (reflectRealCLM E')).comp
      (convRealDirect hs (b12 B)) +
    (convRealDirect hs (b21 B)).comp (reflectRealCLM E) +
    ((ContinuousLinearMap.compL ℝ _ _ _ |>.flip (reflectRealCLM E')).comp
      (convRealDirect hs (b22 B))).comp (reflectRealCLM E)

private theorem realConvolution_def (hs : 1 / 2 < s) (B : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolution hs B a b =
      convRealDirect hs (b11 B) a b +
        convRealDirect hs (b12 B) a (reflect b) +
        convRealDirect hs (b21 B) (reflect a) b +
        convRealDirect hs (b22 B) (reflect a) (reflect b) :=
  (rfl)

theorem norm_realConvolution_le (hs : 1 / 2 < s) (B : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    ‖realConvolution hs B a b‖ ≤
      4 * (2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n)) * ‖B‖ * ‖a‖ * ‖b‖ := by
  set C := 2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n)
  have hC : 0 ≤ C := by positivity
  have h1 : ‖convRealDirect hs (b11 B) a b‖ ≤ C * ‖B‖ * ‖a‖ * ‖b‖ :=
    (norm_convRealDirect_le hs (b11 B) a b).trans (by gcongr; exact norm_b11_le B)
  have h2 : ‖convRealDirect hs (b12 B) a (reflect b)‖ ≤ C * ‖B‖ * ‖a‖ * ‖b‖ :=
    (norm_convRealDirect_le hs (b12 B) a (reflect b)).trans
      (by rw [reflect.norm_map]; gcongr; exact norm_b12_le B)
  have h3 : ‖convRealDirect hs (b21 B) (reflect a) b‖ ≤ C * ‖B‖ * ‖a‖ * ‖b‖ :=
    (norm_convRealDirect_le hs (b21 B) (reflect a) b).trans
      (by rw [reflect.norm_map]; gcongr; exact norm_b21_le B)
  have h4 : ‖convRealDirect hs (b22 B) (reflect a) (reflect b)‖ ≤ C * ‖B‖ * ‖a‖ * ‖b‖ :=
    (norm_convRealDirect_le hs (b22 B) (reflect a) (reflect b)).trans
      (by rw [reflect.norm_map, reflect.norm_map]; gcongr; exact norm_b22_le B)
  rw [realConvolution_def]
  calc ‖convRealDirect hs (b11 B) a b + convRealDirect hs (b12 B) a (reflect b) +
          convRealDirect hs (b21 B) (reflect a) b +
          convRealDirect hs (b22 B) (reflect a) (reflect b)‖
      ≤ (‖convRealDirect hs (b11 B) a b‖ + ‖convRealDirect hs (b12 B) a (reflect b)‖) +
          ‖convRealDirect hs (b21 B) (reflect a) b‖ +
          ‖convRealDirect hs (b22 B) (reflect a) (reflect b)‖ := by
        linarith [norm_add_le (convRealDirect hs (b11 B) a b +
            convRealDirect hs (b12 B) a (reflect b) +
            convRealDirect hs (b21 B) (reflect a) b)
          (convRealDirect hs (b22 B) (reflect a) (reflect b)),
          norm_add_le (convRealDirect hs (b11 B) a b + convRealDirect hs (b12 B) a (reflect b))
            (convRealDirect hs (b21 B) (reflect a) b),
          norm_add_le (convRealDirect hs (b11 B) a b)
            (convRealDirect hs (b12 B) a (reflect b))]
    _ ≤ (C * ‖B‖ * ‖a‖ * ‖b‖ + C * ‖B‖ * ‖a‖ * ‖b‖) + C * ‖B‖ * ‖a‖ * ‖b‖ +
          C * ‖B‖ * ‖a‖ * ‖b‖ := by gcongr
    _ = 4 * C * ‖B‖ * ‖a‖ * ‖b‖ := by ring

theorem opNorm_realConvolution_le (hs : 1 / 2 < s) (B : E →L[ℝ] E' →L[ℝ] F) :
    ‖realConvolution hs B‖ ≤ 4 * (2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n)) * ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b ↦ ?_
  exact norm_realConvolution_le hs B a b

@[simp]
theorem realConvolution_inclusion (ht : 1 / 2 < t) (h : t ≤ s) (B : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolution ht B (inclusion h a) (inclusion h b) =
      inclusion h (realConvolution (ht.trans_le h) B a b) :=
  CircleSobolev.ext <| funext fun n ↦ by
    have hreflE : reflect (inclusion h a) = inclusion h (reflect a) :=
      CircleSobolev.ext <| funext fun _ ↦ by simp
    have hreflE' : reflect (inclusion h b) = inclusion h (reflect b) :=
      CircleSobolev.ext <| funext fun _ ↦ by simp
    simp [realConvolution_def, hreflE, hreflE']

@[simp]
theorem realConvolution_bilinearRestrictScalars (hs : 1 / 2 < s) (B : E →L[ℂ] E' →L[ℂ] F) :
    realConvolution hs (B.bilinearRestrictScalars ℝ) =
      (convolution hs B).bilinearRestrictScalars ℝ := by
  refine continuousLinearMap_real_ext_single fun m v ↦
    continuousLinearMap_real_ext_single fun k w ↦ ?_
  have hB1 : ContinuousLinearMap.complexLinearPartCLM E (E' →L[ℝ] F)
      (B.bilinearRestrictScalars ℝ) v = (B v).restrictScalars ℝ := by
    rw [ContinuousLinearMap.complexLinearPartCLM_apply_apply]
    exact (ContinuousLinearMap.complexLinearPart_eq_and_complexAntilinearPart_eq
      (L := B.bilinearRestrictScalars ℝ) (v := v)
      (a := (B v).restrictScalars ℝ) (b := 0) fun z ↦ by ext u; simp).1
  have hB2 : ContinuousLinearMap.complexAntilinearPartCLM E (E' →L[ℝ] F)
      (B.bilinearRestrictScalars ℝ) v = 0 := by
    rw [ContinuousLinearMap.complexAntilinearPartCLM_apply_apply]
    exact (ContinuousLinearMap.complexLinearPart_eq_and_complexAntilinearPart_eq
      (L := B.bilinearRestrictScalars ℝ) (v := v)
      (a := (B v).restrictScalars ℝ) (b := 0) fun z ↦ by ext u; simp).2
  rw [ContinuousLinearMap.bilinearRestrictScalars_apply_apply, convolution_single_single,
    realConvolution_def]
  simp [b11, b12, b21, b22, hB1, hB2]

@[simp]
theorem realConvolution_bilinearRestrictScalars_apply (hs : 1 / 2 < s) (B : E →L[ℂ] E' →L[ℂ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolution hs (B.bilinearRestrictScalars ℝ) a b = convolution hs B a b :=
  DFunLike.congr_fun
    (DFunLike.congr_fun (realConvolution_bilinearRestrictScalars hs B) a) b

/-- **On continuous representatives the real-bilinear product is pointwise:** for `s > 1/2`, the
continuous function attached to `realConvolution hs B a b` is `x ↦ B (a x) (b x)`. -/
@[simp]
theorem toContinuousMap_realConvolution_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E]
    [CompleteSpace E'] (hs : 1 / 2 < s) (B : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') (x : AddCircle T) :
    toContinuousMap T hs (realConvolution hs B a b) x =
      B (toContinuousMap T hs a x) (toContinuousMap T hs b x) := by
  set evE : CircleSobolev s E →L[ℝ] E :=
    ((ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs)).restrictScalars ℝ
  set evE' : CircleSobolev s E' →L[ℝ] E' :=
    ((ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs)).restrictScalars ℝ
  set evF : CircleSobolev s F →L[ℝ] F :=
    ((ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs)).restrictScalars ℝ
  set lhs : CircleSobolev s E →L[ℝ] CircleSobolev s E' →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ _ _ F evF).comp (realConvolution hs B)
  set rhs : CircleSobolev s E →L[ℝ] CircleSobolev s E' →L[ℝ] F :=
    ((ContinuousLinearMap.compL ℝ _ _ F |>.flip evE').comp B).comp evE
  have heq : lhs = rhs := by
    refine continuousLinearMap_real_ext_single fun m v ↦
      continuousLinearMap_real_ext_single fun k w ↦ ?_
    simp only [lhs, rhs, evE, evE', evF, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousMap.evalCLM_apply]
    rw [realConvolution_def]
    simp only [reflect_single, convRealDirect_single_single, map_add, toContinuousMap_single,
      ContinuousMap.add_apply, ContinuousMap.smul_apply', ContinuousMap.const_apply]
    rw [B.apply_smul_eq_complexLinearPart_add_complexAntilinearPart (fourier m x) v,
      add_apply, smul_apply, smul_apply,
      ContinuousLinearMap.apply_smul_eq_complexLinearPart_add_complexAntilinearPart _
        (fourier k x) w,
      ContinuousLinearMap.apply_smul_eq_complexLinearPart_add_complexAntilinearPart _
        (fourier k x) w,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      ← fourier_neg, ← fourier_neg, ← fourier_add, ← fourier_add, ← fourier_add, ← fourier_add]
    simp only [b11, b12, b21, b22, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.complexLinearPartCLM_apply_apply,
      ContinuousLinearMap.complexAntilinearPartCLM_apply_apply]
    abel
  exact DFunLike.congr_fun (DFunLike.congr_fun heq a) b

end RealConvolution

end CircleSobolev

end TauCeti
