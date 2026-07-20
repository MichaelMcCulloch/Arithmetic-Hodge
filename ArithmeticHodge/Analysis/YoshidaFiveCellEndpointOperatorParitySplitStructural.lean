import ArithmeticHodge.Analysis.YoshidaFiveCellEndpointAdaptedIntrinsicLowStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural
import ArithmeticHodge.Analysis.YoshidaPointwiseParityCore

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorParitySplitStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeil
open MultiplicativeWeilFiveCellSingleProfileStructural
open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaClippedEndpointContinuous
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseBoundaryContinuousPhaseCongruenceStructural
open YoshidaFiveCellCanonicalLowTailSchurStructural
open YoshidaFiveCellEndpointAdaptedIntrinsicLowStructural
open YoshidaFiveCellEndpointAdaptedLowTailStructural
open YoshidaFiveCellEndpointOperatorProbeStructural
open YoshidaFiveCellHighTailCoercivityStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaEndpointScaledCorrelation
open YoshidaPointwiseParityCore
open YoshidaRegularKernelBound
open YoshidaSectionSixAnalytic

/-!
# Reflection parity of the complete five-cell endpoint operator

The clipped critical form has no even--odd cross term.  This file transports
that structural orthogonality through the exact physical-coordinate bridge
and the retained five-cell prime atom.  Consequently both the complete
operator and its low--tail polarization split into independent reflection
channels.
-/

/-- Pointwise even part of an arbitrary clipped smooth profile. -/
def fiveCellClippedEvenPart
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
    YoshidaClippedSmooth fiveCellOperatorHalfWidth :=
  (2 : ℂ)⁻¹ • (f + clippedReflection f)

/-- Pointwise odd part of an arbitrary clipped smooth profile. -/
def fiveCellClippedOddPart
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
    YoshidaClippedSmooth fiveCellOperatorHalfWidth :=
  (2 : ℂ)⁻¹ • (f - clippedReflection f)

@[simp]
theorem fiveCellClippedEvenPart_apply
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) (x : ℝ) :
    fiveCellClippedEvenPart f x = (f x + f (-x)) / 2 := by
  unfold fiveCellClippedEvenPart
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_add, Pi.add_apply]
  change (2 : ℂ)⁻¹ * (f x + f (-x)) = (f x + f (-x)) / 2
  ring

@[simp]
theorem fiveCellClippedOddPart_apply
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) (x : ℝ) :
    fiveCellClippedOddPart f x = (f x - f (-x)) / 2 := by
  unfold fiveCellClippedOddPart
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sub, Pi.sub_apply]
  change (2 : ℂ)⁻¹ * (f x - f (-x)) = (f x - f (-x)) / 2
  ring

theorem fiveCellClippedEvenPart_even
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
    Function.Even (fiveCellClippedEvenPart f : ℝ → ℂ) := by
  intro x
  simp only [fiveCellClippedEvenPart_apply, neg_neg]
  ring

theorem fiveCellClippedOddPart_odd
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
    Function.Odd (fiveCellClippedOddPart f : ℝ → ℂ) := by
  intro x
  simp only [fiveCellClippedOddPart_apply, neg_neg]
  ring

theorem fiveCellClippedEvenPart_add_oddPart
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
    fiveCellClippedEvenPart f + fiveCellClippedOddPart f = f := by
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add, Pi.add_apply,
    fiveCellClippedEvenPart_apply, fiveCellClippedOddPart_apply]
  ring

/-- Centered real coordinate of a clipped profile. -/
def fiveCellClippedCenteredRealProfile
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) : ℝ → ℝ :=
  centeredRescale fiveCellOperatorHalfWidth (fun y ↦ (f y).re)

theorem fiveCellClippedCenteredRealProfile_evenPart
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
    fiveCellClippedCenteredRealProfile (fiveCellClippedEvenPart f) =
      factorTwoReflectionEvenPart (fiveCellClippedCenteredRealProfile f) := by
  funext x
  unfold fiveCellClippedCenteredRealProfile centeredRescale
    factorTwoReflectionEvenPart
  simp only [fiveCellClippedEvenPart_apply, Complex.div_re,
    Complex.add_re]
  rw [show fiveCellOperatorHalfWidth * -x =
      -(fiveCellOperatorHalfWidth * x) by ring]
  norm_num
  ring

theorem fiveCellClippedCenteredRealProfile_oddPart
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
    fiveCellClippedCenteredRealProfile (fiveCellClippedOddPart f) =
      factorTwoReflectionOddPart (fiveCellClippedCenteredRealProfile f) := by
  funext x
  unfold fiveCellClippedCenteredRealProfile centeredRescale
    factorTwoReflectionOddPart
  simp only [fiveCellClippedOddPart_apply, Complex.div_re,
    Complex.sub_re]
  rw [show fiveCellOperatorHalfWidth * -x =
      -(fiveCellOperatorHalfWidth * x) by ring]
  norm_num
  ring

private theorem fiveCellClippedCriticalForm_eq_even_add_odd
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
    yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
        fiveCellOperatorHalfWidth_pos f f =
      yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
          fiveCellOperatorHalfWidth_pos
          (fiveCellClippedEvenPart f) (fiveCellClippedEvenPart f) +
        yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
          fiveCellOperatorHalfWidth_pos
          (fiveCellClippedOddPart f) (fiveCellClippedOddPart f) := by
  let B := yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
    fiveCellOperatorHalfWidth_pos
  let e := fiveCellClippedEvenPart f
  let o := fiveCellClippedOddPart f
  have hdecomp : f = e + o := by
    simpa only [e, o] using (fiveCellClippedEvenPart_add_oddPart f).symm
  have heven : ∀ x : ℝ, e (-x) = e x := by
    simpa only [e] using fiveCellClippedEvenPart_even f
  have hodd : ∀ x : ℝ, o (-x) = -o x := by
    simpa only [o] using fiveCellClippedOddPart_odd f
  have hcrossEO : B e o = 0 :=
    yoshidaClippedLocalCriticalForm_even_odd_eq_zero
      fiveCellOperatorHalfWidth_pos e o heven hodd
  have hcrossOE : B o e = 0 :=
    yoshidaClippedLocalCriticalForm_odd_even_eq_zero
      fiveCellOperatorHalfWidth_pos o e hodd heven
  change B f f = B e e + B o o
  rw [hdecomp, map_add]
  simp only [map_add]
  change (B e e + B o e) + (B e o + B o o) = B e e + B o o
  rw [hcrossEO, hcrossOE]
  ring

/-- The complete physical quadratic splits on any real endpoint-zero clipped
profile.  The local-Lipschitz assumptions are exactly those required by the
lossless critical-form bridge. -/
theorem centeredClippedPhysicalQuadratic_eq_reflectionParity
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth)
    (hreal : ∀ x ∈ Icc (-fiveCellOperatorHalfWidth)
      fiveCellOperatorHalfWidth, f x = ((f x).re : ℂ))
    (hneg : f (-fiveCellOperatorHalfWidth) = 0)
    (hpos : f fiveCellOperatorHalfWidth = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fiveCellClippedCenteredRealProfile f))
    (heLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionEvenPart
        (fiveCellClippedCenteredRealProfile f)))
    (hoLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionOddPart
        (fiveCellClippedCenteredRealProfile f))) :
    centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
        (fiveCellClippedCenteredRealProfile f) =
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
          (factorTwoReflectionEvenPart
            (fiveCellClippedCenteredRealProfile f)) +
        centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
          (factorTwoReflectionOddPart
            (fiveCellClippedCenteredRealProfile f)) := by
  let e := fiveCellClippedEvenPart f
  let o := fiveCellClippedOddPart f
  have hereal : ∀ x ∈ Icc (-fiveCellOperatorHalfWidth)
      fiveCellOperatorHalfWidth, e x = ((e x).re : ℂ) := by
    intro x hx
    have hxneg : -x ∈ Icc (-fiveCellOperatorHalfWidth)
        fiveCellOperatorHalfWidth := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    dsimp only [e]
    rw [fiveCellClippedEvenPart_apply, hreal x hx, hreal (-x) hxneg]
    simp
  have horeal : ∀ x ∈ Icc (-fiveCellOperatorHalfWidth)
      fiveCellOperatorHalfWidth, o x = ((o x).re : ℂ) := by
    intro x hx
    have hxneg : -x ∈ Icc (-fiveCellOperatorHalfWidth)
        fiveCellOperatorHalfWidth := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    dsimp only [o]
    rw [fiveCellClippedOddPart_apply, hreal x hx, hreal (-x) hxneg]
    simp
  have heends : e (-fiveCellOperatorHalfWidth) = 0 ∧
      e fiveCellOperatorHalfWidth = 0 := by
    dsimp only [e]
    simp only [fiveCellClippedEvenPart_apply, neg_neg]
    rw [hneg, hpos]
    simp
  have hoends : o (-fiveCellOperatorHalfWidth) = 0 ∧
      o fiveCellOperatorHalfWidth = 0 := by
    dsimp only [o]
    simp only [fiveCellClippedOddPart_apply, neg_neg]
    rw [hneg, hpos]
    simp
  have heprofile : fiveCellClippedCenteredRealProfile e =
      factorTwoReflectionEvenPart
        (fiveCellClippedCenteredRealProfile f) := by
    simpa only [e] using fiveCellClippedCenteredRealProfile_evenPart f
  have hoprofile : fiveCellClippedCenteredRealProfile o =
      factorTwoReflectionOddPart
        (fiveCellClippedCenteredRealProfile f) := by
    simpa only [o] using fiveCellClippedCenteredRealProfile_oddPart f
  have hfdiag :=
    clippedCriticalFormValue_eq_centeredClippedPhysicalQuadratic_of_endpoints_zero
      fiveCellOperatorHalfWidth_pos f hreal hneg hpos hlocal
  have hediag :=
    clippedCriticalFormValue_eq_centeredClippedPhysicalQuadratic_of_endpoints_zero
      fiveCellOperatorHalfWidth_pos e hereal heends.1 heends.2
        (by
          change LocallyLipschitzOn (Icc (-1 : ℝ) 1)
            (fiveCellClippedCenteredRealProfile e)
          rw [heprofile]
          exact heLocal)
  have hodiag :=
    clippedCriticalFormValue_eq_centeredClippedPhysicalQuadratic_of_endpoints_zero
      fiveCellOperatorHalfWidth_pos o horeal hoends.1 hoends.2
        (by
          change LocallyLipschitzOn (Icc (-1 : ℝ) 1)
            (fiveCellClippedCenteredRealProfile o)
          rw [hoprofile]
          exact hoLocal)
  have hsplit := congrArg Complex.re
    (fiveCellClippedCriticalForm_eq_even_add_odd f)
  simp only [clippedCriticalFormValue] at hfdiag hediag hodiag
  change (yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
      fiveCellOperatorHalfWidth_pos f f).re =
    (yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
      fiveCellOperatorHalfWidth_pos e e).re +
    (yoshidaClippedLocalCriticalForm fiveCellOperatorHalfWidth
      fiveCellOperatorHalfWidth_pos o o).re at hsplit
  rw [hfdiag, hediag, hodiag] at hsplit
  change fiveCellOperatorHalfWidth *
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
        (fiveCellClippedCenteredRealProfile f) =
    fiveCellOperatorHalfWidth *
        centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
          (fiveCellClippedCenteredRealProfile e) +
      fiveCellOperatorHalfWidth *
        centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
          (fiveCellClippedCenteredRealProfile o) at hsplit
  rw [heprofile, hoprofile] at hsplit
  nlinarith [fiveCellOperatorHalfWidth_pos]

/-- The retained five-cell prime atom is diagonal in reflection parity. -/
theorem fiveCellEndpointPairing_eq_reflectionParity
    (w : ℝ → ℝ) (hw : Continuous w) :
    fiveCellEndpointPairing w =
      fiveCellEndpointPairing (factorTwoReflectionEvenPart w) +
        fiveCellEndpointPairing (factorTwoReflectionOddPart w) := by
  let e := factorTwoReflectionEvenPart w
  let o := factorTwoReflectionOddPart w
  have hec : Continuous e := continuous_factorTwoReflectionEvenPart hw
  have hoc : Continuous o := continuous_factorTwoReflectionOddPart hw
  have hcross := factorTwoCenteredCorrelationBilinear_eq_zero_of_even_odd
    (factorTwoReflectionEvenPart_even w)
    (factorTwoReflectionOddPart_odd w) (4 / 3)
  have hsplit : e + o = w := by
    simpa only [e, o] using factorTwoReflectionEvenPart_add_oddPart w
  rw [fiveCellEndpointPairing_eq_centeredEndpointCorrelation,
    fiveCellEndpointPairing_eq_centeredEndpointCorrelation,
    fiveCellEndpointPairing_eq_centeredEndpointCorrelation]
  change centeredEndpointCorrelation w (4 / 3) =
    centeredEndpointCorrelation e (4 / 3) +
      centeredEndpointCorrelation o (4 / 3)
  rw [← hsplit, centeredEndpointCorrelation_add e o hec hoc,
    show factorTwoCenteredCorrelationBilinear e o (4 / 3) = 0 by
      simpa only [e, o] using hcross]
  ring

/-- The full five-cell endpoint operator is exactly the sum of its even and
odd reflection values on every real endpoint-zero clipped smooth profile. -/
theorem fiveCellEndpointOperator_eq_reflectionParity
    (f : YoshidaClippedSmooth fiveCellOperatorHalfWidth)
    (hreal : ∀ x ∈ Icc (-fiveCellOperatorHalfWidth)
      fiveCellOperatorHalfWidth, f x = ((f x).re : ℂ))
    (hneg : f (-fiveCellOperatorHalfWidth) = 0)
    (hpos : f fiveCellOperatorHalfWidth = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fiveCellClippedCenteredRealProfile f))
    (heLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionEvenPart
        (fiveCellClippedCenteredRealProfile f)))
    (hoLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionOddPart
        (fiveCellClippedCenteredRealProfile f))) :
    fiveCellEndpointOperator (fiveCellClippedCenteredRealProfile f) =
      fiveCellEndpointOperator
          (factorTwoReflectionEvenPart
            (fiveCellClippedCenteredRealProfile f)) +
        fiveCellEndpointOperator
          (factorTwoReflectionOddPart
            (fiveCellClippedCenteredRealProfile f)) := by
  have hfcont : Continuous (f : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero
      fiveCellOperatorHalfWidth_pos f hneg hpos
  have hw : Continuous (fiveCellClippedCenteredRealProfile f) := by
    unfold fiveCellClippedCenteredRealProfile centeredRescale
    exact (Complex.continuous_re.comp hfcont).comp
      (continuous_const.mul continuous_id)
  have hphysical := centeredClippedPhysicalQuadratic_eq_reflectionParity
    f hreal hneg hpos hlocal heLocal hoLocal
  have hprime := fiveCellEndpointPairing_eq_reflectionParity
    (fiveCellClippedCenteredRealProfile f) hw
  unfold fiveCellEndpointOperator
  rw [hphysical, hprime]
  ring

theorem factorTwoReflectionEvenPart_add
    (u v : ℝ → ℝ) :
    factorTwoReflectionEvenPart (u + v) =
      factorTwoReflectionEvenPart u + factorTwoReflectionEvenPart v := by
  funext x
  unfold factorTwoReflectionEvenPart
  simp only [Pi.add_apply]
  ring

theorem factorTwoReflectionOddPart_add
    (u v : ℝ → ℝ) :
    factorTwoReflectionOddPart (u + v) =
      factorTwoReflectionOddPart u + factorTwoReflectionOddPart v := by
  funext x
  unfold factorTwoReflectionOddPart
  simp only [Pi.add_apply]
  ring

theorem fiveCellClippedCenteredRealProfile_add
    (f g : YoshidaClippedSmooth fiveCellOperatorHalfWidth) :
    fiveCellClippedCenteredRealProfile (f + g) =
      fiveCellClippedCenteredRealProfile f +
        fiveCellClippedCenteredRealProfile g := by
  funext x
  unfold fiveCellClippedCenteredRealProfile centeredRescale
  simp only [Submodule.coe_add, Pi.add_apply, Complex.add_re]

/-- Polarization of a parity-diagonal quadratic has only the even--even and
odd--odd channels.  The three hypotheses are diagonal identities, so this
lemma can be reused with any exact realization of the five-cell form. -/
theorem fiveCellEndpointOperatorCross_eq_reflectionParity_of_splits
    (u v : ℝ → ℝ)
    (hu : fiveCellEndpointOperator u =
      fiveCellEndpointOperator (factorTwoReflectionEvenPart u) +
        fiveCellEndpointOperator (factorTwoReflectionOddPart u))
    (hv : fiveCellEndpointOperator v =
      fiveCellEndpointOperator (factorTwoReflectionEvenPart v) +
        fiveCellEndpointOperator (factorTwoReflectionOddPart v))
    (huv : fiveCellEndpointOperator (u + v) =
      fiveCellEndpointOperator
          (factorTwoReflectionEvenPart u +
            factorTwoReflectionEvenPart v) +
        fiveCellEndpointOperator
          (factorTwoReflectionOddPart u +
            factorTwoReflectionOddPart v)) :
    fiveCellEndpointOperatorCross u v =
      fiveCellEndpointOperatorCross
          (factorTwoReflectionEvenPart u)
          (factorTwoReflectionEvenPart v) +
        fiveCellEndpointOperatorCross
          (factorTwoReflectionOddPart u)
          (factorTwoReflectionOddPart v) := by
  unfold fiveCellEndpointOperatorCross
  rw [hu, hv, huv]
  ring

/-- Exact parity splitting of the five-cell polarization on two real,
endpoint-zero clipped smooth profiles. -/
theorem fiveCellEndpointOperatorCross_eq_reflectionParity
    (f g : YoshidaClippedSmooth fiveCellOperatorHalfWidth)
    (hfreal : ∀ x ∈ Icc (-fiveCellOperatorHalfWidth)
      fiveCellOperatorHalfWidth, f x = ((f x).re : ℂ))
    (hgreal : ∀ x ∈ Icc (-fiveCellOperatorHalfWidth)
      fiveCellOperatorHalfWidth, g x = ((g x).re : ℂ))
    (hfneg : f (-fiveCellOperatorHalfWidth) = 0)
    (hfpos : f fiveCellOperatorHalfWidth = 0)
    (hgneg : g (-fiveCellOperatorHalfWidth) = 0)
    (hgpos : g fiveCellOperatorHalfWidth = 0)
    (hfLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fiveCellClippedCenteredRealProfile f))
    (hfeLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionEvenPart
        (fiveCellClippedCenteredRealProfile f)))
    (hfoLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionOddPart
        (fiveCellClippedCenteredRealProfile f)))
    (hgLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fiveCellClippedCenteredRealProfile g))
    (hgeLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionEvenPart
        (fiveCellClippedCenteredRealProfile g)))
    (hgoLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionOddPart
        (fiveCellClippedCenteredRealProfile g))) :
    fiveCellEndpointOperatorCross
        (fiveCellClippedCenteredRealProfile f)
        (fiveCellClippedCenteredRealProfile g) =
      fiveCellEndpointOperatorCross
          (factorTwoReflectionEvenPart
            (fiveCellClippedCenteredRealProfile f))
          (factorTwoReflectionEvenPart
            (fiveCellClippedCenteredRealProfile g)) +
        fiveCellEndpointOperatorCross
          (factorTwoReflectionOddPart
            (fiveCellClippedCenteredRealProfile f))
          (factorTwoReflectionOddPart
            (fiveCellClippedCenteredRealProfile g)) := by
  let u := fiveCellClippedCenteredRealProfile f
  let v := fiveCellClippedCenteredRealProfile g
  have hu := fiveCellEndpointOperator_eq_reflectionParity f hfreal
    hfneg hfpos hfLocal hfeLocal hfoLocal
  have hv := fiveCellEndpointOperator_eq_reflectionParity g hgreal
    hgneg hgpos hgLocal hgeLocal hgoLocal
  have hfgreal : ∀ x ∈ Icc (-fiveCellOperatorHalfWidth)
      fiveCellOperatorHalfWidth,
      (f + g) x = (((f + g) x).re : ℂ) := by
    intro x hx
    simp only [Submodule.coe_add, Pi.add_apply, Complex.add_re]
    rw [hfreal x hx, hgreal x hx]
    simp
  have hfgneg : (f + g) (-fiveCellOperatorHalfWidth) = 0 := by
    simp only [Submodule.coe_add, Pi.add_apply, hfneg, hgneg, add_zero]
  have hfgpos : (f + g) fiveCellOperatorHalfWidth = 0 := by
    simp only [Submodule.coe_add, Pi.add_apply, hfpos, hgpos, add_zero]
  have hfgLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fiveCellClippedCenteredRealProfile (f + g)) := by
    rw [fiveCellClippedCenteredRealProfile_add]
    exact hfLocal.add hgLocal
  have hfgeLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionEvenPart
        (fiveCellClippedCenteredRealProfile (f + g))) := by
    rw [fiveCellClippedCenteredRealProfile_add,
      factorTwoReflectionEvenPart_add]
    exact hfeLocal.add hgeLocal
  have hfgoLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionOddPart
        (fiveCellClippedCenteredRealProfile (f + g))) := by
    rw [fiveCellClippedCenteredRealProfile_add,
      factorTwoReflectionOddPart_add]
    exact hfoLocal.add hgoLocal
  have huvRaw := fiveCellEndpointOperator_eq_reflectionParity
    (f + g) hfgreal hfgneg hfgpos hfgLocal hfgeLocal hfgoLocal
  have huv : fiveCellEndpointOperator (u + v) =
      fiveCellEndpointOperator
          (factorTwoReflectionEvenPart u +
            factorTwoReflectionEvenPart v) +
        fiveCellEndpointOperator
          (factorTwoReflectionOddPart u +
            factorTwoReflectionOddPart v) := by
    simpa only [u, v, fiveCellClippedCenteredRealProfile_add,
      factorTwoReflectionEvenPart_add,
      factorTwoReflectionOddPart_add] using huvRaw
  simpa only [u, v] using
    fiveCellEndpointOperatorCross_eq_reflectionParity_of_splits u v
      hu hv huv

/-- Two scalar Schur contractions recombine without a sign condition on
either cross term.  This is the two-channel Cauchy inequality in inverse-free
form. -/
theorem twoChannelSchur_recombine
    {Lₑ Lₒ Tₑ Tₒ Cₑ Cₒ : ℝ}
    (hLₑ : 0 ≤ Lₑ) (hLₒ : 0 ≤ Lₒ)
    (hTₑ : 0 ≤ Tₑ) (hTₒ : 0 ≤ Tₒ)
    (hCₑ : Cₑ ^ 2 ≤ Lₑ * Tₑ)
    (hCₒ : Cₒ ^ 2 ≤ Lₒ * Tₒ) :
    (Cₑ + Cₒ) ^ 2 ≤ (Lₑ + Lₒ) * (Tₑ + Tₒ) := by
  have hprod : Cₑ ^ 2 * Cₒ ^ 2 ≤
      (Lₑ * Tₑ) * (Lₒ * Tₒ) :=
    mul_le_mul hCₑ hCₒ (sq_nonneg Cₒ) (mul_nonneg hLₑ hTₑ)
  have hright : 0 ≤ Lₑ * Tₒ + Lₒ * Tₑ :=
    add_nonneg (mul_nonneg hLₑ hTₒ) (mul_nonneg hLₒ hTₑ)
  have hcrossSquare : (2 * Cₑ * Cₒ) ^ 2 ≤
      (Lₑ * Tₒ + Lₒ * Tₑ) ^ 2 := by
    nlinarith [sq_nonneg (Lₑ * Tₒ - Lₒ * Tₑ)]
  have hcross : 2 * Cₑ * Cₒ ≤
      Lₑ * Tₒ + Lₒ * Tₑ := by
    nlinarith
  nlinarith

/-- Same-parity low--tail Schur bounds imply the unsplit scalar Schur bound.
The hypotheses are exact diagonal and polarization identities, so no positive
definite inverse or strictness is required. -/
theorem fiveCellEndpointOperatorCross_sq_le_of_reflectionParitySchur
    (u v : ℝ → ℝ)
    (hu : fiveCellEndpointOperator u =
      fiveCellEndpointOperator (factorTwoReflectionEvenPart u) +
        fiveCellEndpointOperator (factorTwoReflectionOddPart u))
    (hv : fiveCellEndpointOperator v =
      fiveCellEndpointOperator (factorTwoReflectionEvenPart v) +
        fiveCellEndpointOperator (factorTwoReflectionOddPart v))
    (hcross : fiveCellEndpointOperatorCross u v =
      fiveCellEndpointOperatorCross
          (factorTwoReflectionEvenPart u)
          (factorTwoReflectionEvenPart v) +
        fiveCellEndpointOperatorCross
          (factorTwoReflectionOddPart u)
          (factorTwoReflectionOddPart v))
    (huEven : 0 ≤ fiveCellEndpointOperator
      (factorTwoReflectionEvenPart u))
    (huOdd : 0 ≤ fiveCellEndpointOperator
      (factorTwoReflectionOddPart u))
    (hvEven : 0 ≤ fiveCellEndpointOperator
      (factorTwoReflectionEvenPart v))
    (hvOdd : 0 ≤ fiveCellEndpointOperator
      (factorTwoReflectionOddPart v))
    (hEven : fiveCellEndpointOperatorCross
        (factorTwoReflectionEvenPart u)
        (factorTwoReflectionEvenPart v) ^ 2 ≤
      fiveCellEndpointOperator (factorTwoReflectionEvenPart u) *
        fiveCellEndpointOperator (factorTwoReflectionEvenPart v))
    (hOdd : fiveCellEndpointOperatorCross
        (factorTwoReflectionOddPart u)
        (factorTwoReflectionOddPart v) ^ 2 ≤
      fiveCellEndpointOperator (factorTwoReflectionOddPart u) *
        fiveCellEndpointOperator (factorTwoReflectionOddPart v)) :
    fiveCellEndpointOperatorCross u v ^ 2 ≤
      fiveCellEndpointOperator u * fiveCellEndpointOperator v := by
  rw [hu, hv, hcross]
  exact twoChannelSchur_recombine
    huEven huOdd hvEven hvOdd hEven hOdd

/-! ## Locality and smooth-profile corollaries -/

/-- The arbitrary-width physical quadratic only depends on the restriction
of its argument to the centered endpoint interval. -/
theorem centeredClippedPhysicalQuadratic_congr_Icc
    {u v : ℝ → ℝ}
    (huv : ∀ x ∈ Icc (-1 : ℝ) 1, u x = v x) :
    centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth u =
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth v := by
  have hraw : centeredRawLogEnergy u = centeredRawLogEnergy v :=
    centeredRawLogEnergy_congr_Icc huv
  have hpotential :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) =
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change yoshidaEndpointPotential x * u x ^ 2 =
      yoshidaEndpointPotential x * v x ^ 2
    rw [huv x hx]
  have hmass : (∫ x : ℝ in -1..1, u x ^ 2) =
      ∫ x : ℝ in -1..1, v x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change u x ^ 2 = v x ^ 2
    rw [huv x hx]
  have hcorrelation (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
      centeredEndpointCorrelation u t = centeredEndpointCorrelation v t := by
    calc
      centeredEndpointCorrelation u t =
          factorTwoCenteredCorrelationBilinear u u t :=
        (factorTwoCenteredCorrelationBilinear_self u t).symm
      _ = factorTwoCenteredCorrelationBilinear v v t :=
        factorTwoCenteredCorrelationBilinear_congr_Icc
          huv huv ht0 ht2
      _ = centeredEndpointCorrelation v t :=
        factorTwoCenteredCorrelationBilinear_self v t
  have hregular :
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fiveCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation u t) =
        ∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fiveCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation v t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change yoshidaRegularKernel (fiveCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation u t =
      yoshidaRegularKernel (fiveCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation v t
    rw [hcorrelation t ht.1 ht.2]
  have hminus :
      (∫ x : ℝ in -1..1,
          Real.exp (-fiveCellOperatorHalfWidth * x / 2) * u x) =
        ∫ x : ℝ in -1..1,
          Real.exp (-fiveCellOperatorHalfWidth * x / 2) * v x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change Real.exp (-fiveCellOperatorHalfWidth * x / 2) * u x =
      Real.exp (-fiveCellOperatorHalfWidth * x / 2) * v x
    rw [huv x hx]
  have hplus :
      (∫ x : ℝ in -1..1,
          Real.exp (fiveCellOperatorHalfWidth * x / 2) * u x) =
        ∫ x : ℝ in -1..1,
          Real.exp (fiveCellOperatorHalfWidth * x / 2) * v x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    change Real.exp (fiveCellOperatorHalfWidth * x / 2) * u x =
      Real.exp (fiveCellOperatorHalfWidth * x / 2) * v x
    rw [huv x hx]
  unfold centeredClippedPhysicalQuadratic
  rw [hraw, hpotential, hmass, hregular, hminus, hplus]

/-- The full five-cell endpoint operator is local to `[-1,1]`. -/
theorem fiveCellEndpointOperator_congr_Icc
    {u v : ℝ → ℝ}
    (huv : ∀ x ∈ Icc (-1 : ℝ) 1, u x = v x) :
    fiveCellEndpointOperator u = fiveCellEndpointOperator v := by
  have hphysical := centeredClippedPhysicalQuadratic_congr_Icc huv
  have hpair : fiveCellEndpointPairing u = fiveCellEndpointPairing v := by
    rw [fiveCellEndpointPairing_eq_centeredEndpointCorrelation,
      fiveCellEndpointPairing_eq_centeredEndpointCorrelation]
    calc
      centeredEndpointCorrelation u (4 / 3) =
          factorTwoCenteredCorrelationBilinear u u (4 / 3) :=
        (factorTwoCenteredCorrelationBilinear_self u (4 / 3)).symm
      _ = factorTwoCenteredCorrelationBilinear v v (4 / 3) :=
        factorTwoCenteredCorrelationBilinear_congr_Icc
          huv huv (by norm_num) (by norm_num)
      _ = centeredEndpointCorrelation v (4 / 3) :=
        factorTwoCenteredCorrelationBilinear_self v (4 / 3)
  unfold fiveCellEndpointOperator
  rw [hphysical, hpair]

/-- Zero extension of a centered profile away from its physical interval. -/
def fiveCellCompactRestriction (w : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ if x ∈ Icc (-1 : ℝ) 1 then w x else 0

/-- A globally smooth centered real profile gives a clipped smooth profile at
the physical five-cell halfwidth. -/
def fiveCellClippedOfSmooth
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) :
    YoshidaClippedSmooth fiveCellOperatorHalfWidth := by
  let core : ℝ → ℂ := fun y ↦
    (w (y / fiveCellOperatorHalfWidth) : ℂ)
  have hcore : ContDiff ℝ ∞ core := by
    dsimp only [core]
    have hscale : ContDiff ℝ ∞
        (fun y : ℝ ↦ y / fiveCellOperatorHalfWidth) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp (hw.comp hscale)
  refine ⟨fun y ↦ if y ∈
      Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth
      then core y else 0, ?_, ?_⟩
  · apply hcore.contDiffOn.congr
    intro y hy
    simp only [hy, ↓reduceIte]
  · intro y hy
    simp only [hy, ↓reduceIte]

theorem fiveCellClippedCenteredRealProfile_ofSmooth
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) :
    fiveCellClippedCenteredRealProfile (fiveCellClippedOfSmooth w hw) =
      fiveCellCompactRestriction w := by
  funext x
  have hmem : fiveCellOperatorHalfWidth * x ∈
      Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth ↔
      x ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · intro hx
      constructor
      · apply (mul_le_mul_iff_right₀ fiveCellOperatorHalfWidth_pos).mp
        simpa only [mul_neg, mul_one] using hx.1
      · apply (mul_le_mul_iff_right₀ fiveCellOperatorHalfWidth_pos).mp
        simpa only [mul_one] using hx.2
    · intro hx
      constructor
      · simpa only [mul_neg, mul_one] using
          (mul_le_mul_iff_right₀ fiveCellOperatorHalfWidth_pos).mpr hx.1
      · simpa only [mul_one] using
          (mul_le_mul_iff_right₀ fiveCellOperatorHalfWidth_pos).mpr hx.2
  unfold fiveCellClippedCenteredRealProfile centeredRescale
    fiveCellCompactRestriction fiveCellClippedOfSmooth
  dsimp only
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [if_pos hx, if_pos (hmem.mpr hx)]
    simp only [Complex.ofReal_re]
    rw [mul_div_cancel_left₀ x fiveCellOperatorHalfWidth_pos.ne']
  · rw [if_neg hx, if_neg (mt hmem.mp hx)]
    rfl

private theorem fiveCellClippedOfSmooth_real
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) :
    ∀ y ∈ Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth,
      fiveCellClippedOfSmooth w hw y =
        ((fiveCellClippedOfSmooth w hw y).re : ℂ) := by
  intro y hy
  unfold fiveCellClippedOfSmooth
  simp only [hy, ↓reduceIte, Complex.ofReal_re]

private theorem fiveCellClippedOfSmooth_endpoints
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hend : w (-1) = 0 ∧ w 1 = 0) :
    fiveCellClippedOfSmooth w hw (-fiveCellOperatorHalfWidth) = 0 ∧
      fiveCellClippedOfSmooth w hw fiveCellOperatorHalfWidth = 0 := by
  unfold fiveCellClippedOfSmooth
  have hwidthNe : fiveCellOperatorHalfWidth ≠ 0 :=
    fiveCellOperatorHalfWidth_pos.ne'
  constructor
  · have hmem : -fiveCellOperatorHalfWidth ∈
      Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth :=
      ⟨le_rfl, by linarith [fiveCellOperatorHalfWidth_pos]⟩
    change (if -fiveCellOperatorHalfWidth ∈
        Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth then
      (w ((-fiveCellOperatorHalfWidth) /
        fiveCellOperatorHalfWidth) : ℂ) else 0) = 0
    rw [if_pos hmem]
    simp only [neg_div, div_self hwidthNe, hend.1, Complex.ofReal_zero]
  · have hmem : fiveCellOperatorHalfWidth ∈
      Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth :=
      ⟨by linarith [fiveCellOperatorHalfWidth_pos], le_rfl⟩
    change (if fiveCellOperatorHalfWidth ∈
        Icc (-fiveCellOperatorHalfWidth) fiveCellOperatorHalfWidth then
      (w (fiveCellOperatorHalfWidth /
        fiveCellOperatorHalfWidth) : ℂ) else 0) = 0
    rw [if_pos hmem]
    simp only [div_self hwidthNe, hend.2, Complex.ofReal_zero]

private theorem locallyLipschitzOn_congr_Icc
    {u v : ℝ → ℝ}
    (huv : ∀ x ∈ Icc (-1 : ℝ) 1, u x = v x)
    (hu : LocallyLipschitzOn (Icc (-1 : ℝ) 1) u) :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) v := by
  intro x hx
  obtain ⟨K, t, ht, hLip⟩ := hu hx
  refine ⟨K, t ∩ Icc (-1 : ℝ) 1,
    Filter.inter_mem ht self_mem_nhdsWithin, ?_⟩
  intro y hy z hz
  rw [← huv y hy.2, ← huv z hz.2]
  exact hLip hy.1 hz.1

/-- On a globally smooth endpoint-zero real profile, the full five-cell
operator is reflection-diagonal.  This is the profile-level form used by the
endpoint-adapted low and tail pieces. -/
theorem fiveCellEndpointOperator_eq_reflectionParity_of_smooth
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hend : w (-1) = 0 ∧ w 1 = 0) :
    fiveCellEndpointOperator w =
      fiveCellEndpointOperator (factorTwoReflectionEvenPart w) +
        fiveCellEndpointOperator (factorTwoReflectionOddPart w) := by
  let f := fiveCellClippedOfSmooth w hw
  let wc := fiveCellCompactRestriction w
  have hprofile : fiveCellClippedCenteredRealProfile f = wc := by
    simpa only [f, wc] using fiveCellClippedCenteredRealProfile_ofSmooth w hw
  have hwOne : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hwLip : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hwOne.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have heSmooth : ContDiff ℝ ∞ (factorTwoReflectionEvenPart w) := by
    unfold factorTwoReflectionEvenPart
    fun_prop
  have hoSmooth : ContDiff ℝ ∞ (factorTwoReflectionOddPart w) := by
    unfold factorTwoReflectionOddPart
    fun_prop
  have heOne : ContDiff ℝ 1 (factorTwoReflectionEvenPart w) :=
    heSmooth.of_le (by norm_num)
  have hoOne : ContDiff ℝ 1 (factorTwoReflectionOddPart w) :=
    hoSmooth.of_le (by norm_num)
  have heLip : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionEvenPart w) :=
    heOne.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hoLip : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionOddPart w) :=
    hoOne.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hwc : ∀ x ∈ Icc (-1 : ℝ) 1, wc x = w x := by
    intro x hx
    simp only [wc, fiveCellCompactRestriction, hx, ↓reduceIte]
  have hewc : ∀ x ∈ Icc (-1 : ℝ) 1,
      factorTwoReflectionEvenPart wc x =
        factorTwoReflectionEvenPart w x := by
    intro x hx
    have hnx : -x ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    unfold factorTwoReflectionEvenPart
    rw [hwc x hx, hwc (-x) hnx]
  have howc : ∀ x ∈ Icc (-1 : ℝ) 1,
      factorTwoReflectionOddPart wc x =
        factorTwoReflectionOddPart w x := by
    intro x hx
    have hnx : -x ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    unfold factorTwoReflectionOddPart
    rw [hwc x hx, hwc (-x) hnx]
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fiveCellClippedCenteredRealProfile f) := by
    rw [hprofile]
    exact locallyLipschitzOn_congr_Icc
      (fun x hx ↦ (hwc x hx).symm) hwLip
  have heLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionEvenPart
        (fiveCellClippedCenteredRealProfile f)) := by
    rw [hprofile]
    exact locallyLipschitzOn_congr_Icc
      (fun x hx ↦ (hewc x hx).symm) heLip
  have hoLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (factorTwoReflectionOddPart
        (fiveCellClippedCenteredRealProfile f)) := by
    rw [hprofile]
    exact locallyLipschitzOn_congr_Icc
      (fun x hx ↦ (howc x hx).symm) hoLip
  have hfend := fiveCellClippedOfSmooth_endpoints w hw hend
  have hsplit := fiveCellEndpointOperator_eq_reflectionParity f
    (fiveCellClippedOfSmooth_real w hw) hfend.1 hfend.2
    hlocal heLocal hoLocal
  rw [hprofile] at hsplit
  calc
    fiveCellEndpointOperator w = fiveCellEndpointOperator wc :=
      fiveCellEndpointOperator_congr_Icc (fun x hx ↦ (hwc x hx).symm)
    _ = fiveCellEndpointOperator (factorTwoReflectionEvenPart wc) +
        fiveCellEndpointOperator (factorTwoReflectionOddPart wc) := hsplit
    _ = fiveCellEndpointOperator (factorTwoReflectionEvenPart w) +
        fiveCellEndpointOperator (factorTwoReflectionOddPart w) := by
      rw [fiveCellEndpointOperator_congr_Icc hewc,
        fiveCellEndpointOperator_congr_Icc howc]

private theorem contDiff_top_centeredLegendreLowProjection
    (w : ℝ → ℝ) (hw : Continuous w) (k : ℕ) :
    ContDiff ℝ ∞ (centeredLegendreLowProjection w hw k) := by
  let p := centeredLegendreProjectionPolynomial w hw k
  have hp : ContDiff ℝ ∞ (fun y : ℝ ↦ p.eval y) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      p.contDiff_aeval (𝕜 := ℝ) ∞
  have haff : ContDiff ℝ ∞ (fun x : ℝ ↦ (x + 1) / 2) := by
    fun_prop
  simpa only [centeredLegendreLowProjection, p, Function.comp_apply] using
    hp.comp haff

private theorem contDiff_top_fiveCellEvenEndpointReserve :
    ContDiff ℝ ∞ fiveCellEvenEndpointReserve := by
  let p := shiftedLegendreReal 10
  have hp : ContDiff ℝ ∞ (fun y : ℝ ↦ p.eval y) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      p.contDiff_aeval (𝕜 := ℝ) ∞
  have haff : ContDiff ℝ ∞ (fun x : ℝ ↦ (x + 1) / 2) := by
    fun_prop
  simpa only [fiveCellEvenEndpointReserve, p, Function.comp_apply] using
    hp.comp haff

private theorem contDiff_top_fiveCellOddEndpointReserve :
    ContDiff ℝ ∞ fiveCellOddEndpointReserve := by
  let p := shiftedLegendreReal 9
  have hp : ContDiff ℝ ∞ (fun y : ℝ ↦ p.eval y) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      p.contDiff_aeval (𝕜 := ℝ) ∞
  have haff : ContDiff ℝ ∞ (fun x : ℝ ↦ (x + 1) / 2) := by
    fun_prop
  simpa only [fiveCellOddEndpointReserve, p, Function.comp_apply] using
    hp.comp haff

theorem contDiff_top_fiveCellEndpointAdaptedLow
    (w : ℝ → ℝ) (hw : Continuous w) :
    ContDiff ℝ ∞ (fiveCellEndpointAdaptedLow w hw) := by
  unfold fiveCellEndpointAdaptedLow
  exact ((contDiff_top_centeredLegendreLowProjection w hw 9).sub
    (contDiff_const.mul contDiff_top_fiveCellEvenEndpointReserve)).sub
      (contDiff_const.mul contDiff_top_fiveCellOddEndpointReserve)

private theorem contDiff_top_fiveCellNormalizedRealProfile
    (parent : BombieriTest) (k : ℤ) :
    ContDiff ℝ ∞ (fiveCellNormalizedRealProfile parent k) := by
  have hsupported := fiveCellWholeCentered_criticalPullbackSupported parent k
  have hscale : ContDiff ℝ ∞
      (fun x : ℝ ↦ fiveCellWholeHalfWidth k * x) := by fun_prop
  have hpullback : ContDiff ℝ ∞
      (fun x : ℝ ↦
        (fiveCellWholeCentered parent k).logarithmicPullbackSchwartz (1 / 2)
          (fiveCellWholeHalfWidth k * x)) :=
    ((fiveCellWholeCentered parent k).logarithmicPullbackSchwartz (1 / 2)).smooth ⊤
      |>.comp hscale
  unfold fiveCellNormalizedRealProfile centeredRescale
  rw [show (fiveCellWholeProfile parent k : ℝ → ℂ) =
      (fiveCellWholeCentered parent k).logarithmicPullbackSchwartz (1 / 2) by
    exact yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported]
  exact Complex.reCLM.contDiff.comp hpullback

theorem contDiff_top_fiveCellProductionEndpointAdaptedTail
    (parent : BombieriTest) (k : ℤ) :
    let w := fiveCellNormalizedRealProfile parent k
    let hw : Continuous w :=
      (fiveCellNormalizedRealProfile_contDiff parent k).continuous
    ContDiff ℝ ∞ (fiveCellEndpointAdaptedTail w hw) := by
  dsimp only
  unfold fiveCellEndpointAdaptedTail
  exact (contDiff_top_fiveCellNormalizedRealProfile parent k).sub
    (contDiff_top_fiveCellEndpointAdaptedLow
      (fiveCellNormalizedRealProfile parent k)
      (fiveCellNormalizedRealProfile_contDiff parent k).continuous)

/-- Both endpoint-adapted production pieces satisfy the smooth reflection
split directly; no closure or density argument is needed. -/
theorem fiveCellProductionEndpointAdapted_operator_eq_reflectionParity
    (parent : BombieriTest) (k : ℤ) :
    let w := fiveCellNormalizedRealProfile parent k
    let hw : Continuous w :=
      (fiveCellNormalizedRealProfile_contDiff parent k).continuous
    (fiveCellEndpointOperator (fiveCellEndpointAdaptedLow w hw) =
      fiveCellEndpointOperator
          (factorTwoReflectionEvenPart
            (fiveCellEndpointAdaptedLow w hw)) +
        fiveCellEndpointOperator
          (factorTwoReflectionOddPart
            (fiveCellEndpointAdaptedLow w hw))) ∧
    (fiveCellEndpointOperator (fiveCellEndpointAdaptedTail w hw) =
      fiveCellEndpointOperator
          (factorTwoReflectionEvenPart
            (fiveCellEndpointAdaptedTail w hw)) +
        fiveCellEndpointOperator
          (factorTwoReflectionOddPart
            (fiveCellEndpointAdaptedTail w hw))) := by
  dsimp only
  let w := fiveCellNormalizedRealProfile parent k
  let hw : Continuous w :=
    (fiveCellNormalizedRealProfile_contDiff parent k).continuous
  have htraces := fiveCellProductionEndpointAdapted_traces_zero parent k
  constructor
  · exact fiveCellEndpointOperator_eq_reflectionParity_of_smooth
      (fiveCellEndpointAdaptedLow w hw)
      (contDiff_top_fiveCellEndpointAdaptedLow w hw) htraces.1
  · exact fiveCellEndpointOperator_eq_reflectionParity_of_smooth
      (fiveCellEndpointAdaptedTail w hw)
      (by simpa only [w, hw] using
        contDiff_top_fiveCellProductionEndpointAdaptedTail parent k)
      htraces.2

/-- The adapted low--tail polarization itself has only the even--even and
odd--odd channels on every production profile. -/
theorem fiveCellProductionEndpointAdapted_operatorCross_eq_reflectionParity
    (parent : BombieriTest) (k : ℤ) :
    let w := fiveCellNormalizedRealProfile parent k
    let hw : Continuous w :=
      (fiveCellNormalizedRealProfile_contDiff parent k).continuous
    fiveCellEndpointOperatorCross
        (fiveCellEndpointAdaptedLow w hw)
        (fiveCellEndpointAdaptedTail w hw) =
      fiveCellEndpointOperatorCross
          (factorTwoReflectionEvenPart
            (fiveCellEndpointAdaptedLow w hw))
          (factorTwoReflectionEvenPart
            (fiveCellEndpointAdaptedTail w hw)) +
        fiveCellEndpointOperatorCross
          (factorTwoReflectionOddPart
            (fiveCellEndpointAdaptedLow w hw))
          (factorTwoReflectionOddPart
            (fiveCellEndpointAdaptedTail w hw)) := by
  dsimp only
  let w := fiveCellNormalizedRealProfile parent k
  let hw : Continuous w :=
    (fiveCellNormalizedRealProfile_contDiff parent k).continuous
  let u := fiveCellEndpointAdaptedLow w hw
  let v := fiveCellEndpointAdaptedTail w hw
  have hsplits :=
    fiveCellProductionEndpointAdapted_operator_eq_reflectionParity parent k
  have hu : fiveCellEndpointOperator u =
      fiveCellEndpointOperator (factorTwoReflectionEvenPart u) +
        fiveCellEndpointOperator (factorTwoReflectionOddPart u) := by
    simpa only [u, w, hw] using hsplits.1
  have hv : fiveCellEndpointOperator v =
      fiveCellEndpointOperator (factorTwoReflectionEvenPart v) +
        fiveCellEndpointOperator (factorTwoReflectionOddPart v) := by
    simpa only [v, w, hw] using hsplits.2
  have huSmooth : ContDiff ℝ ∞ u := by
    simpa only [u] using contDiff_top_fiveCellEndpointAdaptedLow w hw
  have hvSmooth : ContDiff ℝ ∞ v := by
    simpa only [v, w, hw] using
      contDiff_top_fiveCellProductionEndpointAdaptedTail parent k
  have htraces := fiveCellProductionEndpointAdapted_traces_zero parent k
  have huvRaw := fiveCellEndpointOperator_eq_reflectionParity_of_smooth
    (u + v) (huSmooth.add hvSmooth)
    ⟨by simp only [Pi.add_apply, u, v, w, htraces.1.1, htraces.2.1,
          add_zero],
      by simp only [Pi.add_apply, u, v, w, htraces.1.2, htraces.2.2,
          add_zero]⟩
  rw [factorTwoReflectionEvenPart_add,
    factorTwoReflectionOddPart_add] at huvRaw
  simpa only [u, v] using
    fiveCellEndpointOperatorCross_eq_reflectionParity_of_splits
      u v hu hv huvRaw

end

end ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorParitySplitStructural
