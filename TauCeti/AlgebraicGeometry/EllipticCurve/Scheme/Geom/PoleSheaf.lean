/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.PoleSheaf
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.PointsDivisor
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass

/-!
# Pole sheaves and relative ampleness on elliptic curves over a scheme

Let `E` be an elliptic curve over an arbitrary base scheme `S`, in the sense of
`EllipticCurveGeom`. Its zero section `E.zero : S ⟶ E.carrier` is a section of the smooth separated
relative curve `E.structureMap : E.carrier ⟶ S`, so its ideal sheaf `E.zeroSectionDivisor` and every
power `E.zeroSectionDivisor ^ n` (`n : ℕ`) cut out relative effective Cartier divisors `n[0]` on `E`
over `S`.

The dual invertible sheaves `E.poleSheaf n : InvertibleSheaf E.carrier` are the pole sheaves
`𝒪_E(n[0])`. Their Picard classes satisfy `[𝒪_E(0[0])] = 1`,
`[𝒪_E((m + n)[0])] = [𝒪_E(m[0])] * [𝒪_E(n[0])]`, and `[𝒪_E(n[0])] = [𝒪_E([0])] ^ n`, commute with
every base-change square of elliptic curves preserving the zero section, agree on pointed
Weierstrass charts with the pole sheaves `WeierstrassCurve.poleSheaf` of the local equations, and
are **relatively ample** over `S` for every `0 < n` (in particular for the cubic polarisation
`n = 3`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.zeroSectionDivisor`: the ideal sheaf of the zero
  section `[0]` on `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheaf`: the invertible sheaf `𝒪_E(n[0])` on `E`
  for `n : ℕ`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isRelativeEffectiveCartier_zeroSectionDivisor` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isRelativeEffectiveCartier_zeroSectionDivisor_pow`:
  `[0]` and `n[0]` are relative effective Cartier divisors over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mk_poleSheaf_zero`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mk_poleSheaf_add`, and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mk_poleSheaf`: additivity of `n ↦ [𝒪_E(n[0])]` in
  the Picard group of `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pullback_mk_poleSheaf_of_isPullback` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pullback_mk_poleSheaf_baseChange`: `𝒪_E(n[0])`
  commutes with arbitrary base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pullback_toTotal_mk_poleSheaf`: on any pointed
  Weierstrass chart, `𝒪_E(n[0])` pulls back to the pole sheaf of the local Weierstrass equation.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isRelativelyAmple_poleSheaf` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isRelativelyAmple_poleSheaf_three`: for every `0 < n`
  (in particular `n = 3`), `𝒪_E(n[0])` is relatively ample over `S`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.1–2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
* [A. Grothendieck, *Éléments de géométrie algébrique: II. Étude globale élémentaire de quelques
  classes de morphismes*][ega2], §4.6.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-! ### The zero-section divisor `[0]` and its multiples `n[0]` -/

/-- The relative divisor `[0]` on an elliptic curve `E` over `S`, represented by the ideal sheaf of
its zero section `E.zero`. -/
noncomputable def zeroSectionDivisor : E.carrier.IdealSheafData :=
  E.zero.ker

/-- Unfolding lemma for `EllipticCurveGeom.zeroSectionDivisor`. -/
theorem zeroSectionDivisor_def : E.zeroSectionDivisor = E.zero.ker :=
  (rfl)

/-- **The zero section of an elliptic curve over a scheme cuts out a relative effective Cartier
divisor.** -/
theorem isRelativeEffectiveCartier_zeroSectionDivisor :
    E.zeroSectionDivisor.IsRelativeEffectiveCartier E.structureMap :=
  Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension E.zero E.zero_comp

/-- **Every nonnegative multiple `n[0]` is a relative effective Cartier divisor** on `E` over
`S`. -/
theorem isRelativeEffectiveCartier_zeroSectionDivisor_pow (n : ℕ) :
    (E.zeroSectionDivisor ^ n).IsRelativeEffectiveCartier E.structureMap :=
  TauCeti.isRelativeEffectiveCartier_pow E.isRelativeEffectiveCartier_zeroSectionDivisor n

/-- The divisor of `n` copies of the identity `S`-point `1` equals `E.zeroSectionDivisor ^ n`. -/
@[simp]
theorem pointsDivisor_const_one (n : ℕ) :
    E.pointsDivisor (fun _ : Fin n ↦ 1) = E.zeroSectionDivisor ^ n := by
  simp [pointsDivisor_def, zeroSectionDivisor_def, hom_one_left]

/-! ### The pole sheaves `𝒪_E(n[0])` and their Picard classes -/

/-- The **pole sheaf** `𝒪_E(n[0])` on an elliptic curve `E` over `S`, defined as the dual of the
invertible ideal sheaf of `n[0] = E.zeroSectionDivisor ^ n`. -/
noncomputable def poleSheaf (n : ℕ) : InvertibleSheaf E.carrier :=
  (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier.toInvertibleSheaf.dual

/-- Unfolding lemma for `EllipticCurveGeom.poleSheaf`. -/
theorem poleSheaf_def (n : ℕ) :
    E.poleSheaf n =
      (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow
        n).isEffectiveCartier.toInvertibleSheaf.dual :=
  (rfl)

/-- The zero-th pole sheaf `𝒪_E(0[0])` has trivial Picard class. -/
@[simp]
theorem mk_poleSheaf_zero : LineBundleClass.mk (E.poleSheaf 0) = 1 := by
  rw [poleSheaf_def, ← LineBundleClass.inv_mk,
    LineBundleClass.mk_toInvertibleSheaf_congr _ (Scheme.IdealSheafData.isEffectiveCartier_top _)
      (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]),
    LineBundleClass.mk_toInvertibleSheaf_top, inv_one]

/-- In the Picard group of `E`, `[𝒪_E((m + n)[0])] = [𝒪_E(m[0])] * [𝒪_E(n[0])]`. -/
theorem mk_poleSheaf_add (m n : ℕ) :
    LineBundleClass.mk (E.poleSheaf (m + n)) =
      LineBundleClass.mk (E.poleSheaf m) * LineBundleClass.mk (E.poleSheaf n) := by
  have hm := (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow m).isEffectiveCartier
  have hn := (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  rw [poleSheaf_def, poleSheaf_def, poleSheaf_def, ← LineBundleClass.inv_mk,
    ← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk,
    LineBundleClass.mk_toInvertibleSheaf_congr _ (TauCeti.isEffectiveCartier_mul hm hn)
      (pow_add _ m n),
    LineBundleClass.mk_toInvertibleSheaf_mul, mul_inv]

/-- In the Picard group of `E`, `[𝒪_E(n[0])] = [𝒪_E([0])] ^ n`. -/
theorem mk_poleSheaf (n : ℕ) :
    LineBundleClass.mk (E.poleSheaf n) = LineBundleClass.mk (E.poleSheaf 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [mk_poleSheaf_add, ih, pow_succ]

/-! ### Base change and local Weierstrass comparison -/

section BaseChange

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'}
  {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S}
  (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0

/-- Along a pullback square of elliptic curves preserving zero sections, the zero-section divisor of
`E'` is the inverse image of that of `E`. -/
theorem zeroSectionDivisor_eq_comap :
    E'.zeroSectionDivisor = E.zeroSectionDivisor.comap g :=
  Scheme.IdealSheafData.ker_eq_comap_of_isPullback E.zero (isPullback_zero_of_isPullback hg h0)

/-- Along a pullback square of elliptic curves preserving zero sections, `n[0]` pulls back to
`n[0]`. -/
theorem zeroSectionDivisor_pow_eq_comap (n : ℕ) :
    E'.zeroSectionDivisor ^ n = (E.zeroSectionDivisor ^ n).comap g := by
  rw [zeroSectionDivisor_eq_comap hg h0, Scheme.IdealSheafData.comap_pow]

/-- **Base-change compatibility of pole sheaves.** For any pullback square of elliptic curves
carrying the zero section to the zero section, `g^* [𝒪_E(n[0])] = [𝒪_{E'}(n[0])]`. -/
theorem pullback_mk_poleSheaf_of_isPullback (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk (E'.poleSheaf n) := by
  have hI := (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hI' := (E'.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hcomap : ((E.zeroSectionDivisor ^ n).comap g).IsEffectiveCartier :=
    zeroSectionDivisor_pow_eq_comap hg h0 n ▸ hI'
  rw [poleSheaf_def, poleSheaf_def, ← LineBundleClass.inv_mk, LineBundleClass.pullback_inv,
    hI.pullback_mk_toInvertibleSheaf hcomap,
    LineBundleClass.mk_toInvertibleSheaf_congr hcomap hI'
      (zeroSectionDivisor_pow_eq_comap hg h0 n).symm,
    LineBundleClass.inv_mk]

/-- Along a pullback square of elliptic curves preserving zero sections, the pulled-back invertible
sheaf `g^* (E.poleSheaf n)` is isomorphic to `E'.poleSheaf n`. -/
theorem nonempty_pullback_poleSheaf_iso_of_isPullback (n : ℕ) :
    Nonempty (((InvertibleSheaf.pullback g).obj (E.poleSheaf n)).obj ≅ (E'.poleSheaf n).obj) := by
  rw [← LineBundleClass.mk_eq_mk_iff, ← LineBundleClass.pullback_mk]
  exact pullback_mk_poleSheaf_of_isPullback hg h0 n

end BaseChange

/-- **The pole sheaves `𝒪_E(n[0])` commute with `EllipticCurveGeom.baseChange`.** -/
@[simp]
theorem pullback_mk_poleSheaf_baseChange {S' : Scheme.{u}} (f : S' ⟶ S) (n : ℕ) :
    LineBundleClass.pullback ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f)
        (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk ((E.baseChange f).poleSheaf n) :=
  pullback_mk_poleSheaf_of_isPullback (E.isPullback_baseChange f)
    (by rw [← Category.assoc, E.zero_baseChangeIso_hom, pullbackSection_fst]) n

/-- **The pole sheaves commute with `EllipticCurveGeom.baseChangeMap`.** -/
@[simp]
theorem pullback_mk_poleSheaf_baseChangeMap {T T' : Scheme.{u}} {f : T ⟶ S} {f' : T' ⟶ S}
    (k : T' ⟶ T) (hk : k ≫ f = f') (n : ℕ) :
    LineBundleClass.pullback (E.baseChangeMap k hk)
        (LineBundleClass.mk ((E.baseChange f).poleSheaf n)) =
      LineBundleClass.mk ((E.baseChange f').poleSheaf n) := by
  have hfst : E.baseChangeMap k hk ≫ (E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f =
      (E.baseChangeIso f').hom ≫ pullback.fst E.structureMap f' := by
    rw [← Category.assoc, E.baseChangeMap_baseChangeIso_hom, Category.assoc, pullback.mapSnd_fst]
  rw [← E.pullback_mk_poleSheaf_baseChange f n, LineBundleClass.pullback_comp, hfst,
    E.pullback_mk_poleSheaf_baseChange f' n]

/-- Under `WeierstrassCurve.toEllipticCurveGeomIso`, the zero-section divisor of
`W.toEllipticCurveGeom` is that of `W`. -/
@[simp]
theorem zeroSectionDivisor_toEllipticCurveGeom {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    (WeierstrassCurve.toEllipticCurveGeom W).zeroSectionDivisor =
      W.zeroSectionDivisor.comap (WeierstrassCurve.toEllipticCurveGeomIso W).hom := by
  have hpb : IsPullback (WeierstrassCurve.toEllipticCurveGeom W).zero (𝟙 _)
      (WeierstrassCurve.toEllipticCurveGeomIso W).hom W.projModelZero :=
    IsPullback.of_vert_isIso_mono
      ⟨by rw [Category.id_comp, WeierstrassCurve.zero_toEllipticCurveGeomIso_hom]⟩
  rw [zeroSectionDivisor_def, WeierstrassCurve.zeroSectionDivisor_def]
  exact Scheme.IdealSheafData.ker_eq_comap_of_isPullback W.projModelZero hpb

/-- Under `WeierstrassCurve.toEllipticCurveGeomIso`, the pole sheaf of `W.toEllipticCurveGeom` has
the same Picard class as `W.poleSheaf n`. -/
@[simp]
theorem pullback_mk_poleSheaf_toEllipticCurveGeom {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (n : ℕ) :
    LineBundleClass.pullback (WeierstrassCurve.toEllipticCurveGeomIso W).hom
        (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk ((WeierstrassCurve.toEllipticCurveGeom W).poleSheaf n) := by
  have hI := (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hI' :=
    ((WeierstrassCurve.toEllipticCurveGeom W).isRelativeEffectiveCartier_zeroSectionDivisor_pow
      n).isEffectiveCartier
  have hpow : (WeierstrassCurve.toEllipticCurveGeom W).zeroSectionDivisor ^ n =
      (W.zeroSectionDivisor ^ n).comap (WeierstrassCurve.toEllipticCurveGeomIso W).hom := by
    rw [zeroSectionDivisor_toEllipticCurveGeom, Scheme.IdealSheafData.comap_pow]
  have hcomap : ((W.zeroSectionDivisor ^ n).comap
      (WeierstrassCurve.toEllipticCurveGeomIso W).hom).IsEffectiveCartier := hpow ▸ hI'
  rw [WeierstrassCurve.poleSheaf_def, poleSheaf_def, ← LineBundleClass.inv_mk,
    LineBundleClass.pullback_inv, hI.pullback_mk_toInvertibleSheaf hcomap,
    LineBundleClass.mk_toInvertibleSheaf_congr hcomap hI' hpow.symm, LineBundleClass.inv_mk]

/-- Pulling back `(W.toEllipticCurveGeom).poleSheaf n` along
`(WeierstrassCurve.toEllipticCurveGeomIso W).inv` recovers `W.poleSheaf n` in the Picard group. -/
@[simp]
theorem pullback_inv_mk_poleSheaf_toEllipticCurveGeom {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (n : ℕ) :
    LineBundleClass.pullback (WeierstrassCurve.toEllipticCurveGeomIso W).inv
        (LineBundleClass.mk ((WeierstrassCurve.toEllipticCurveGeom W).poleSheaf n)) =
      LineBundleClass.mk (W.poleSheaf n) := by
  rw [← pullback_mk_poleSheaf_toEllipticCurveGeom W n, LineBundleClass.pullback_comp,
    Iso.inv_hom_id, LineBundleClass.pullback_id]

/-- On any pointed Weierstrass chart `c` of `E`, pulling `E.poleSheaf n` back along
`c.modelIso.inv ≫ c.toTotal` gives the pole sheaf `c.equation.poleSheaf n` of the local equation. -/
theorem pullback_modelIso_inv_toTotal_mk_poleSheaf
    (c : PointedWeierstrassChart E.structureMap E.zero) (n : ℕ) :
    LineBundleClass.pullback (c.modelIso.inv ≫ c.toTotal)
        (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk (c.equation.poleSheaf n) := by
  let g : (WeierstrassCurve.toEllipticCurveGeom c.equation).carrier ⟶ E.carrier :=
    (WeierstrassCurve.toEllipticCurveGeomIso c.equation).hom ≫ c.modelIso.inv ≫ c.toTotal
  have hg : IsPullback g (WeierstrassCurve.toEllipticCurveGeom c.equation).structureMap
      E.structureMap (c.baseIso.inv ≫ c.baseMap) :=
    c.isPullback_modelIso_inv_toTotal.of_iso
      (WeierstrassCurve.toEllipticCurveGeomIso c.equation).symm (.refl _) (.refl _) (.refl _)
      (by simp [g]) (by simp [Iso.eq_inv_comp]) (by simp) (by simp)
  have h0 : (WeierstrassCurve.toEllipticCurveGeom c.equation).zero ≫ g =
      (c.baseIso.inv ≫ c.baseMap) ≫ E.zero := by
    simp [g, c.projModelZero_modelIso_inv_toTotal]
  have hpull := pullback_mk_poleSheaf_of_isPullback hg h0 n
  rw [← LineBundleClass.pullback_comp] at hpull
  rw [← pullback_inv_mk_poleSheaf_toEllipticCurveGeom c.equation n, ← hpull,
    LineBundleClass.pullback_comp, Iso.inv_hom_id, LineBundleClass.pullback_id]

/-- **Comparison with local Weierstrass charts.** On any pointed Weierstrass chart `c` of `E`,
pulling `E.poleSheaf n` back to `c.pullbackCarrier` agrees with pulling `c.equation.poleSheaf n`
back along `c.modelIso.hom`. -/
theorem pullback_toTotal_mk_poleSheaf
    (c : PointedWeierstrassChart E.structureMap E.zero) (n : ℕ) :
    LineBundleClass.pullback c.toTotal (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.pullback c.modelIso.hom (LineBundleClass.mk (c.equation.poleSheaf n)) := by
  rw [← E.pullback_modelIso_inv_toTotal_mk_poleSheaf c n, LineBundleClass.pullback_comp,
    Iso.hom_inv_id_assoc]

/-! ### Relative ampleness over an arbitrary base scheme -/

/-- **Every positive pole sheaf `𝒪_E(n[0])` (`0 < n`) on an elliptic curve `E` over a scheme `S` is
relatively ample over `S`.** Zariski-locally on `S`, `E` is isomorphic to the projective model of an
elliptic Weierstrass curve, on which `𝒪(n[0])` is ample. -/
theorem isRelativelyAmple_poleSheaf {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.mk (E.poleSheaf n)).IsRelativelyAmple E.structureMap := by
  obtain ⟨A⟩ := E.localModel
  refine LineBundleClass.IsRelativelyAmple.of_forall_exists_isAffineOpen fun s ↦ ?_
  obtain ⟨idx, x, rfl⟩ := A.covers s
  let c := A.chart idx
  let U : S.Opens := c.baseMap.opensRange
  have hpb₁ : IsPullback c.toTotal (c.toBase ≫ c.baseMap.isoOpensRange.hom) E.structureMap U.ι :=
    c.isPullback.of_iso (.refl _) (.refl _) c.baseMap.isoOpensRange (.refl _)
      (by simp) (by simp) (by simp) c.baseMap.isoOpensRange_hom_ι.symm
  have hpb₂ : IsPullback (E.structureMap ⁻¹ᵁ U).ι (E.structureMap ∣_ U) E.structureMap U.ι :=
    (isPullback_morphismRestrict E.structureMap U).flip
  let i : (E.structureMap ⁻¹ᵁ U).toScheme ≅ c.pullbackCarrier := hpb₂.isoIsPullback _ _ hpb₁
  have hi : i.hom ≫ c.toTotal = (E.structureMap ⁻¹ᵁ U).ι := hpb₂.isoIsPullback_hom_fst _ _ hpb₁
  refine ⟨U, isAffineOpen_opensRange c.baseMap, ⟨x, rfl⟩, ?_⟩
  rw [← hi, ← LineBundleClass.pullback_comp, E.pullback_toTotal_mk_poleSheaf c n,
    LineBundleClass.pullback_comp]
  exact (c.equation.isAmple_poleSheaf hn).pullback_of_isIso (i.hom ≫ c.modelIso.hom)

/-- **The cubic polarisation `𝒪_E(3[0])` on an elliptic curve over any scheme `S` is relatively
ample over `S`.** -/
theorem isRelativelyAmple_poleSheaf_three :
    (LineBundleClass.mk (E.poleSheaf 3)).IsRelativelyAmple E.structureMap :=
  E.isRelativelyAmple_poleSheaf (by decide)

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
