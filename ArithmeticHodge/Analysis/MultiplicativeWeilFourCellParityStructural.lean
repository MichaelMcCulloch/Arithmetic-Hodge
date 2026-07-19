import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellRealDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointParityPencil
import ArithmeticHodge.Analysis.YoshidaPointwiseParityCore

set_option autoImplicit false

open Complex Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellParityStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeil
open MultiplicativeWeilFourCellRealDiagonalStructural
open MultiplicativeWeilFourCellRealRescaleStructural
open MultiplicativeWeilFourCellSingleProfileStructural
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFourCellEndpointVarianceStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic

/-!
# Reflection parity reduction of the exact four-cell target

Both the complete local diagonal and the surviving prime-two endpoint pairing
are invariant under simultaneous reflection.  Hence the exact normalized
four-cell target splits into independent even and odd sectors; there is no
mixed parity reserve to estimate.
-/

/-- The production crop bundled in the endpoint-periodic source core. -/
def fourCellWholePeriodicCore (parent : BombieriTest) (k : ℤ) :
    YoshidaClippedPeriodicCore (fourCellWholeHalfWidth k) :=
  ⟨fourCellWholeProfile parent k, by
    simpa only [fourCellWholeProfile] using
      yoshidaCriticalPullbackCrop_mem_periodicCore_structural
        (fourCellWholeHalfWidth_pos k) (fourCellWholeCentered parent k)
        (fourCellWholeCentered_criticalPullbackSupported parent k)⟩

/-- Normalized reflection-even part of the complete real profile. -/
def fourCellNormalizedEvenProfile (parent : BombieriTest) (k : ℤ) :
    ℝ → ℝ :=
  factorTwoReflectionEvenPart (fourCellNormalizedRealProfile parent k)

/-- Normalized reflection-odd part of the complete real profile. -/
def fourCellNormalizedOddProfile (parent : BombieriTest) (k : ℤ) :
    ℝ → ℝ :=
  factorTwoReflectionOddPart (fourCellNormalizedRealProfile parent k)

theorem fourCellNormalizedEvenProfile_even
    (parent : BombieriTest) (k : ℤ) :
    Function.Even (fourCellNormalizedEvenProfile parent k) :=
  factorTwoReflectionEvenPart_even _

theorem fourCellNormalizedOddProfile_odd
    (parent : BombieriTest) (k : ℤ) :
    Function.Odd (fourCellNormalizedOddProfile parent k) :=
  factorTwoReflectionOddPart_odd _

theorem fourCellNormalizedEvenProfile_contDiff
    (parent : BombieriTest) (k : ℤ) :
    ContDiff ℝ 1 (fourCellNormalizedEvenProfile parent k) := by
  let w := fourCellNormalizedRealProfile parent k
  have hw : ContDiff ℝ 1 w :=
    fourCellNormalizedRealProfile_contDiff parent k
  have hreflect : ContDiff ℝ 1 (fun x : ℝ ↦ w (-x)) := by
    exact hw.comp (by fun_prop)
  unfold fourCellNormalizedEvenProfile factorTwoReflectionEvenPart
  exact (hw.add hreflect).div_const 2

theorem fourCellNormalizedOddProfile_contDiff
    (parent : BombieriTest) (k : ℤ) :
    ContDiff ℝ 1 (fourCellNormalizedOddProfile parent k) := by
  let w := fourCellNormalizedRealProfile parent k
  have hw : ContDiff ℝ 1 w :=
    fourCellNormalizedRealProfile_contDiff parent k
  have hreflect : ContDiff ℝ 1 (fun x : ℝ ↦ w (-x)) := by
    exact hw.comp (by fun_prop)
  unfold fourCellNormalizedOddProfile factorTwoReflectionOddPart
  exact (hw.sub hreflect).div_const 2

private theorem centeredRescale_evenCore_eq_normalizedEven
    (parent : BombieriTest) (k : ℤ) :
    centeredRescale (fourCellWholeHalfWidth k) (fun y ↦
      ((((periodicCoreEvenPart (fourCellWholePeriodicCore parent k) :
        YoshidaClippedPeriodicCore (fourCellWholeHalfWidth k)) :
          YoshidaClippedSmooth (fourCellWholeHalfWidth k)) y).re)) =
      fourCellNormalizedEvenProfile parent k := by
  funext x
  unfold centeredRescale fourCellNormalizedEvenProfile
    factorTwoReflectionEvenPart fourCellNormalizedRealProfile
  change (((2 : ℂ)⁻¹ *
      (fourCellWholeProfile parent k (fourCellWholeHalfWidth k * x) +
        fourCellWholeProfile parent k (-(fourCellWholeHalfWidth k * x)))).re) =
    ((fourCellWholeProfile parent k (fourCellWholeHalfWidth k * x)).re +
      (fourCellWholeProfile parent k
        (fourCellWholeHalfWidth k * -x)).re) / 2
  rw [show fourCellWholeHalfWidth k * -x =
      -(fourCellWholeHalfWidth k * x) by ring]
  norm_num [Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply]
  ring

private theorem centeredRescale_oddCore_eq_normalizedOdd
    (parent : BombieriTest) (k : ℤ) :
    centeredRescale (fourCellWholeHalfWidth k) (fun y ↦
      ((((periodicCoreOddPart (fourCellWholePeriodicCore parent k) :
        YoshidaClippedPeriodicCore (fourCellWholeHalfWidth k)) :
          YoshidaClippedSmooth (fourCellWholeHalfWidth k)) y).re)) =
      fourCellNormalizedOddProfile parent k := by
  funext x
  unfold centeredRescale fourCellNormalizedOddProfile
    factorTwoReflectionOddPart fourCellNormalizedRealProfile
  change (((2 : ℂ)⁻¹ *
      (fourCellWholeProfile parent k (fourCellWholeHalfWidth k * x) -
        fourCellWholeProfile parent k (-(fourCellWholeHalfWidth k * x)))).re) =
    ((fourCellWholeProfile parent k (fourCellWholeHalfWidth k * x)).re -
      (fourCellWholeProfile parent k
        (fourCellWholeHalfWidth k * -x)).re) / 2
  rw [show fourCellWholeHalfWidth k * -x =
      -(fourCellWholeHalfWidth k * x) by ring]
  norm_num [Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply]
  ring

/-- The complete arbitrary-halfwidth physical diagonal splits exactly across
the normalized reflection-even and reflection-odd production profiles. -/
theorem centeredPhysical_fourCell_eq_even_add_odd
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    centeredClippedPhysicalQuadratic (fourCellWholeHalfWidth k)
        (fourCellNormalizedRealProfile parent k) =
      centeredClippedPhysicalQuadratic (fourCellWholeHalfWidth k)
          (fourCellNormalizedEvenProfile parent k) +
        centeredClippedPhysicalQuadratic (fourCellWholeHalfWidth k)
          (fourCellNormalizedOddProfile parent k) := by
  let a := fourCellWholeHalfWidth k
  let r := fourCellWholePeriodicCore parent k
  let e : YoshidaClippedSmooth a :=
    ((periodicCoreEvenPart r : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a)
  let o : YoshidaClippedSmooth a :=
    ((periodicCoreOddPart r : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a)
  have ha : 0 < a := fourCellWholeHalfWidth_pos k
  have hends := fourCellWholeProfile_endpoints_zero parent k
  have hereal : ∀ x ∈ Icc (-a) a, e x = ((e x).re : ℂ) := by
    intro x _hx
    have hx0 := fourCellWholeProfile_im_eq_zero parent k hparent x
    have hnx0 := fourCellWholeProfile_im_eq_zero parent k hparent (-x)
    have him : (e x).im = 0 := by
      dsimp only [e, r]
      simp only [periodicCoreEvenPart_apply, fourCellWholePeriodicCore,
        Complex.mul_im, Complex.add_im, hx0, hnx0]
      norm_num [Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  have horeal : ∀ x ∈ Icc (-a) a, o x = ((o x).re : ℂ) := by
    intro x _hx
    have hx0 := fourCellWholeProfile_im_eq_zero parent k hparent x
    have hnx0 := fourCellWholeProfile_im_eq_zero parent k hparent (-x)
    have him : (o x).im = 0 := by
      dsimp only [o, r]
      simp only [periodicCoreOddPart_apply, fourCellWholePeriodicCore,
        Complex.mul_im, Complex.sub_im, hx0, hnx0]
      norm_num [Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  have heends : e (-a) = 0 ∧ e a = 0 := by
    dsimp only [e, r]
    simp only [periodicCoreEvenPart_apply, fourCellWholePeriodicCore, neg_neg]
    rw [hends.1, hends.2]
    simp
  have hoends : o (-a) = 0 ∧ o a = 0 := by
    dsimp only [o, r]
    simp only [periodicCoreOddPart_apply, fourCellWholePeriodicCore, neg_neg]
    rw [hends.1, hends.2]
    simp
  have helocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale a (fun y ↦ (e y).re)) := by
    rw [show centeredRescale a (fun y ↦ (e y).re) =
        fourCellNormalizedEvenProfile parent k by
      simpa only [a, e, r] using
        centeredRescale_evenCore_eq_normalizedEven parent k]
    exact (fourCellNormalizedEvenProfile_contDiff parent k).contDiffOn
      |>.locallyLipschitzOn (convex_Icc (-1) 1)
  have holocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale a (fun y ↦ (o y).re)) := by
    rw [show centeredRescale a (fun y ↦ (o y).re) =
        fourCellNormalizedOddProfile parent k by
      simpa only [a, o, r] using
        centeredRescale_oddCore_eq_normalizedOdd parent k]
    exact (fourCellNormalizedOddProfile_contDiff parent k).contDiffOn
      |>.locallyLipschitzOn (convex_Icc (-1) 1)
  have hediag :=
    clippedCriticalFormValue_eq_centeredClippedPhysicalQuadratic_of_endpoints_zero
      ha e hereal heends.1 heends.2 helocal
  have hodiag :=
    clippedCriticalFormValue_eq_centeredClippedPhysicalQuadratic_of_endpoints_zero
      ha o horeal hoends.1 hoends.2 holocal
  have heprofile := centeredRescale_evenCore_eq_normalizedEven parent k
  have hoprofile := centeredRescale_oddCore_eq_normalizedOdd parent k
  have hsplit := congrArg Complex.re
    (yoshidaClippedLocalCriticalForm_self_eq_even_add_odd ha r)
  have hwhole :=
    fourCell_clippedLocalCritical_re_eq_centeredPhysical parent k hparent
  simp only [clippedCriticalFormValue] at hediag hodiag
  rw [heprofile] at hediag
  rw [hoprofile] at hodiag
  change (yoshidaClippedLocalCriticalForm a ha (r : YoshidaClippedSmooth a)
      (r : YoshidaClippedSmooth a)).re =
    (yoshidaClippedLocalCriticalForm a ha e e).re +
      (yoshidaClippedLocalCriticalForm a ha o o).re at hsplit
  change (yoshidaClippedLocalCriticalForm a ha (r : YoshidaClippedSmooth a)
      (r : YoshidaClippedSmooth a)).re =
    a * centeredClippedPhysicalQuadratic a
      (fourCellNormalizedRealProfile parent k) at hwhole
  rw [hwhole, hediag, hodiag] at hsplit
  nlinarith

/-- The endpoint pairing has no reflection-even/odd mixed term. -/
theorem fourCellEndpointPairing_eq_even_add_odd
    (parent : BombieriTest) (k : ℤ) :
    fourCellEndpointPairing (fourCellNormalizedRealProfile parent k) =
      fourCellEndpointPairing (fourCellNormalizedEvenProfile parent k) +
        fourCellEndpointPairing (fourCellNormalizedOddProfile parent k) := by
  let w := fourCellNormalizedRealProfile parent k
  let e := fourCellNormalizedEvenProfile parent k
  let o := fourCellNormalizedOddProfile parent k
  have hw : Continuous w := fourCellNormalizedRealProfile_continuous parent k
  have he : Continuous e :=
    (fourCellNormalizedEvenProfile_contDiff parent k).continuous
  have ho : Continuous o :=
    (fourCellNormalizedOddProfile_contDiff parent k).continuous
  have hparity := factorTwoCenteredCorrelationBilinear_eq_zero_of_even_odd
    (fourCellNormalizedEvenProfile_even parent k)
    (fourCellNormalizedOddProfile_odd parent k) (8 / 5)
  have hsplit : e + o = w := by
    simpa only [e, o, w, fourCellNormalizedEvenProfile,
      fourCellNormalizedOddProfile] using
        factorTwoReflectionEvenPart_add_oddPart w
  rw [fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    fourCellEndpointPairing_eq_centeredEndpointCorrelation,
    fourCellEndpointPairing_eq_centeredEndpointCorrelation]
  change centeredEndpointCorrelation w (8 / 5) =
    centeredEndpointCorrelation e (8 / 5) +
      centeredEndpointCorrelation o (8 / 5)
  rw [← hsplit, centeredEndpointCorrelation_add e o he ho]
  rw [show factorTwoCenteredCorrelationBilinear e o (8 / 5) = 0 by
    simpa only [e, o] using hparity]
  ring

/-- The exact normalized four-cell bracket is the sum of its independent
reflection-even and reflection-odd brackets. -/
theorem fourCell_centeredPhysical_sub_pairing_eq_parity
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    centeredClippedPhysicalQuadratic (fourCellWholeHalfWidth k)
          (fourCellNormalizedRealProfile parent k) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fourCellNormalizedRealProfile parent k) =
      (centeredClippedPhysicalQuadratic (fourCellWholeHalfWidth k)
            (fourCellNormalizedEvenProfile parent k) -
          Real.sqrt 2 * Real.log 2 *
            fourCellEndpointPairing (fourCellNormalizedEvenProfile parent k)) +
        (centeredClippedPhysicalQuadratic (fourCellWholeHalfWidth k)
            (fourCellNormalizedOddProfile parent k) -
          Real.sqrt 2 * Real.log 2 *
            fourCellEndpointPairing
              (fourCellNormalizedOddProfile parent k)) := by
  rw [centeredPhysical_fourCell_eq_even_add_odd parent k hparent,
    fourCellEndpointPairing_eq_even_add_odd parent k]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellParityStructural
