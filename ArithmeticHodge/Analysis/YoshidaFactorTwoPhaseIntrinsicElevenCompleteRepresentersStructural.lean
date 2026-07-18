import ArithmeticHodge.Analysis.YoshidaFactorTwoFixedLagRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoForwardPolePolynomialReductionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoIntegrableLagRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPolePolynomialReductionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoForwardPolePolynomialReductionStructural
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural
open YoshidaFactorTwoReflectedPolePolynomialReductionStructural
open YoshidaFactorTwoReflectedPoleRepresenterStructural

noncomputable section

/-!
# Complete cutoff-eleven low-tail representers

The exact low-tail phase block is assembled here as two one-variable
representers.  Polynomial moment cancellation is performed before the
forward and reflected poles are exposed, so their residual selectors contain
only logarithms and no hidden polynomial correction.
-/

private def primeLag : ℝ :=
  factorTwoPrimeShift / yoshidaEndpointA

private def primeCoefficient : ℝ :=
  Real.log 3 / (2 * Real.sqrt 3)

/-- Reflected-pole contribution to the complete low-tail half-cross. -/
def factorTwoIntrinsicElevenReflectedMixed
    (eLow oLow eR oR : ℝ → ℝ) (a b : ℝ) : ℝ :=
  -(1 / 4 : ℝ) *
    ((∫ t : ℝ in 0..2,
        factorTwoCenteredPhaseCorrelation
          (eLow + eR) (oLow + oR) a (-b) t / (2 - t)) -
      (∫ t : ℝ in 0..2,
        factorTwoCenteredPhaseCorrelation eLow oLow a (-b) t / (2 - t)) -
      ∫ t : ℝ in 0..2,
        factorTwoCenteredPhaseCorrelation eR oR a (-b) t / (2 - t))

/-- Retained `p = 3` contribution to the complete low-tail half-cross. -/
def factorTwoIntrinsicElevenPrimeMixed
    (eLow oLow eR oR : ℝ → ℝ) (a b : ℝ) : ℝ :=
  -primeCoefficient *
    (factorTwoCenteredPhaseCorrelation
        (eLow + eR) (oLow + oR) a b primeLag -
      factorTwoCenteredPhaseCorrelation eLow oLow a b primeLag -
      factorTwoCenteredPhaseCorrelation eR oR a b primeLag)

def factorTwoIntrinsicElevenAnalyticEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  (a / 2) *
      factorTwoContinuousLagK factorTwoSymmetricAnalyticLag
        (centeredPolynomialLift pE) x +
    (b / 2) *
      factorTwoContinuousLagJ factorTwoAlternatingAnalyticLag
        (centeredPolynomialLift pO) x

def factorTwoIntrinsicElevenAnalyticOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  (a / 2) *
      factorTwoContinuousLagK factorTwoSymmetricAnalyticLag
        (centeredPolynomialLift pO) x -
    (b / 2) *
      factorTwoContinuousLagJ factorTwoAlternatingAnalyticLag
        (centeredPolynomialLift pE) x

def factorTwoIntrinsicElevenForwardEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  -(a / 4) * forwardPoleKLogSelector pE x -
    (b / 4) * forwardPoleLLogSelector pO x

def factorTwoIntrinsicElevenForwardOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  -(a / 4) * forwardPoleKLogSelector pO x +
    (b / 4) * forwardPoleLLogSelector pE x

def factorTwoIntrinsicElevenReflectedEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  -(a / 4) * reflectedPoleKLogSelector pE x +
    (b / 4) * reflectedPoleJLogSelector pO x

def factorTwoIntrinsicElevenReflectedOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  -(a / 4) * reflectedPoleKLogSelector pO x -
    (b / 4) * reflectedPoleJLogSelector pE x

def factorTwoIntrinsicElevenPrimeEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  -primeCoefficient *
    (a * factorTwoFixedLagK primeLag (centeredPolynomialLift pE) x +
      b * factorTwoFixedLagJ primeLag (centeredPolynomialLift pO) x)

def factorTwoIntrinsicElevenPrimeOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  -primeCoefficient *
    (a * factorTwoFixedLagK primeLag (centeredPolynomialLift pO) x -
      b * factorTwoFixedLagJ primeLag (centeredPolynomialLift pE) x)

/-- Complete even residual representer for a polynomial low pair. -/
def factorTwoIntrinsicElevenEvenMixedRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenCleanSurvivorRepresenter pE x +
    factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b x +
    factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b x +
    factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b x +
    factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b x

/-- Complete odd residual representer for a polynomial low pair. -/
def factorTwoIntrinsicElevenOddMixedRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenCleanSurvivorRepresenter pO x +
    factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b x +
    factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b x +
    factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b x +
    factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b x

/-- Polarizing both profiles in a fixed phase produces exactly two symmetric
and two alternating low-tail rows. -/
theorem factorTwoCenteredPhaseCorrelation_add_add_sub
    (eLow eR oLow oR : ℝ → ℝ)
    (heLow : Continuous eLow) (heR : Continuous eR)
    (hoLow : Continuous oLow) (hoR : Continuous oR)
    (a b t : ℝ) :
    factorTwoCenteredPhaseCorrelation (eLow + eR) (oLow + oR) a b t -
        factorTwoCenteredPhaseCorrelation eLow oLow a b t -
        factorTwoCenteredPhaseCorrelation eR oR a b t =
      2 * a *
          (factorTwoCenteredCorrelationBilinear eLow eR t +
            factorTwoCenteredCorrelationBilinear oLow oR t) +
        b *
          (factorTwoP67ResidualAlternatingCrossDifference eLow oR t +
            factorTwoP67ResidualAlternatingCrossDifference eR oLow t) := by
  unfold factorTwoCenteredPhaseCorrelation
  rw [centeredEndpointCorrelation_add eLow eR heLow heR t,
    centeredEndpointCorrelation_add oLow oR hoLow hoR t,
    factorTwoCenteredCrossCorrelation_add_left oLow oR (eLow + eR)
      hoLow hoR (heLow.add heR) t,
    factorTwoCenteredCrossCorrelation_add_right oLow eLow eR
      hoLow heLow heR t,
    factorTwoCenteredCrossCorrelation_add_right oR eLow eR
      hoR heLow heR t,
    factorTwoCenteredCrossCorrelation_add_left eLow eR (oLow + oR)
      heLow heR (hoLow.add hoR) t,
    factorTwoCenteredCrossCorrelation_add_right eLow oLow oR
      heLow hoLow hoR t,
    factorTwoCenteredCrossCorrelation_add_right eR oLow oR
      heR hoLow hoR t]
  unfold factorTwoP67ResidualAlternatingCrossDifference
  ring

/-! ## Pairing integrability -/

private theorem continuous_centeredPolynomialLift_complete (p : ℝ[X]) :
    Continuous (centeredPolynomialLift p) := by
  unfold centeredPolynomialLift
  fun_prop

private theorem intervalIntegrable_cleanSurvivor_mul
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenCleanSurvivorRepresenter p x * r x)
      volume (-1) 1 := by
  let q : ℝ → ℝ := centeredPolynomialLift p
  have hq : Continuous q := continuous_centeredPolynomialLift_complete p
  have hV : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * q x * r x)
      volume (-1) 1 := intervalIntegrable_endpointPotential_mul q r hq hr
  have hR : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointEvenRegularRepresenter q x * r x)
      volume (-1) 1 := intervalIntegrable_regularRepresenter_mul q r hq hr
  have hC : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * r x))
          |>.intervalIntegrable (-1) 1
  have hS : IntervalIntegrable
      (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * r x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2) * r x))
          |>.intervalIntegrable (-1) 1
  have hRank : IntervalIntegrable
      (fun x : ℝ ↦
        yoshidaEndpointCoshMoment q *
            (Real.cosh (yoshidaEndpointA * x / 2) * r x) -
          yoshidaEndpointSinhMoment q *
            (Real.sinh (yoshidaEndpointA * x / 2) * r x))
      volume (-1) 1 :=
    (hC.const_mul (yoshidaEndpointCoshMoment q)).sub
      (hS.const_mul (yoshidaEndpointSinhMoment q))
  apply ((hV.sub (hR.const_mul yoshidaEndpointA)).add
    (hRank.const_mul (2 * yoshidaEndpointA))).congr
  intro x _hx
  dsimp only [q]
  unfold factorTwoIntrinsicElevenCleanSurvivorRepresenter
  ring

private theorem intervalIntegrable_mul_continuousLagK_of_bounded
    (q p r : ℝ → ℝ) (hq : Measurable q)
    (hp : Continuous p) (hr : Continuous r)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    IntervalIntegrable (fun x ↦ r x * factorTwoContinuousLagK q p x)
      volume (-1) 1 := by
  have hright :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      q p r hq hp hr C hqC
  have hleft :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      q r p hq hr hp C hqC
  simpa only [factorTwoContinuousLagK, mul_add] using hright.add hleft

private theorem intervalIntegrable_mul_continuousLagJ_of_bounded
    (q p r : ℝ → ℝ) (hq : Measurable q)
    (hp : Continuous p) (hr : Continuous r)
    (C : ℝ) (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C) :
    IntervalIntegrable (fun x ↦ r x * factorTwoContinuousLagJ q p x)
      volume (-1) 1 := by
  have hright :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      q p r hq hp hr C hqC
  have hleft :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      q r p hq hr hp C hqC
  simpa only [factorTwoContinuousLagJ, mul_sub] using hright.sub hleft

private theorem intervalIntegrable_mul_forwardPoleKLogSelector
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦ r x * forwardPoleKLogSelector p x)
      volume (-1) 1 := by
  have hp := continuous_centeredPolynomialLift_complete p
  have hfull : IntervalIntegrable (fun x ↦
      r x * factorTwoForwardHankelK (centeredPolynomialLift p) x)
      volume (-1) 1 :=
    (hr.mul (continuous_factorTwoForwardHankelK
      (centeredPolynomialLift p) hp)).intervalIntegrable (-1) 1
  have hcorrection : Continuous
      (centeredPolynomialLift (forwardPoleKCorrection p)) :=
    continuous_centeredPolynomialLift_complete _
  have hpoly : IntervalIntegrable (fun x ↦
      r x * centeredPolynomialLift (forwardPoleKCorrection p) x)
      volume (-1) 1 := (hr.mul hcorrection).intervalIntegrable (-1) 1
  apply (hfull.sub hpoly).congr
  intro x hx
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  change r x * factorTwoForwardHankelK (centeredPolynomialLift p) x -
      r x * centeredPolynomialLift (forwardPoleKCorrection p) x =
    r x * forwardPoleKLogSelector p x
  rw [forwardPoleK_centeredPolynomialLift p hxIcc]
  ring

private theorem intervalIntegrable_mul_forwardPoleLLogSelector
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦ r x * forwardPoleLLogSelector p x)
      volume (-1) 1 := by
  have hp := continuous_centeredPolynomialLift_complete p
  have hfull : IntervalIntegrable (fun x ↦
      r x * factorTwoForwardHankelL (centeredPolynomialLift p) x)
      volume (-1) 1 :=
    (hr.mul (continuous_factorTwoForwardHankelL
      (centeredPolynomialLift p) hp)).intervalIntegrable (-1) 1
  have hcorrection : Continuous
      (centeredPolynomialLift (forwardPoleLCorrection p)) :=
    continuous_centeredPolynomialLift_complete _
  have hpoly : IntervalIntegrable (fun x ↦
      r x * centeredPolynomialLift (forwardPoleLCorrection p) x)
      volume (-1) 1 := (hr.mul hcorrection).intervalIntegrable (-1) 1
  apply (hfull.sub hpoly).congr
  intro x hx
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  change r x * factorTwoForwardHankelL (centeredPolynomialLift p) x -
      r x * centeredPolynomialLift (forwardPoleLCorrection p) x =
    r x * forwardPoleLLogSelector p x
  rw [forwardPoleL_centeredPolynomialLift p hxIcc]
  ring

private theorem intervalIntegrable_mul_reflectedPoleKLogSelector
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦ r x * reflectedPoleKLogSelector p x)
      volume (-1) 1 := by
  have hp := continuous_centeredPolynomialLift_complete p
  have hright :=
    intervalIntegrable_mul_factorTwoReflectedPoleRightRepresenter
      (centeredPolynomialLift p) r hp hr
  have hleft :=
    intervalIntegrable_mul_factorTwoReflectedPoleLeftRepresenter
      r (centeredPolynomialLift p) hr hp
  have hfull : IntervalIntegrable (fun x ↦
      r x * factorTwoReflectedPoleK (centeredPolynomialLift p) x)
      volume (-1) 1 := by
    simpa only [factorTwoReflectedPoleK, mul_add] using hright.add hleft
  have hcorrection : Continuous
      (centeredPolynomialLift (reflectedPoleKCorrection p)) :=
    continuous_centeredPolynomialLift_complete _
  have hpoly : IntervalIntegrable (fun x ↦
      r x * centeredPolynomialLift (reflectedPoleKCorrection p) x)
      volume (-1) 1 := (hr.mul hcorrection).intervalIntegrable (-1) 1
  apply (hfull.sub hpoly).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ))] with x hx hx1
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  change r x * factorTwoReflectedPoleK (centeredPolynomialLift p) x -
      r x * centeredPolynomialLift (reflectedPoleKCorrection p) x =
    r x * reflectedPoleKLogSelector p x
  rw [reflectedPoleK_centeredPolynomialLift p hxIoo]
  unfold reflectedPoleKLogSelector
  ring

private theorem intervalIntegrable_mul_reflectedPoleJLogSelector
    (p : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦ r x * reflectedPoleJLogSelector p x)
      volume (-1) 1 := by
  have hp := continuous_centeredPolynomialLift_complete p
  have hright :=
    intervalIntegrable_mul_factorTwoReflectedPoleRightRepresenter
      (centeredPolynomialLift p) r hp hr
  have hleft :=
    intervalIntegrable_mul_factorTwoReflectedPoleLeftRepresenter
      r (centeredPolynomialLift p) hr hp
  have hfull : IntervalIntegrable (fun x ↦
      r x * factorTwoReflectedPoleJ (centeredPolynomialLift p) x)
      volume (-1) 1 := by
    simpa only [factorTwoReflectedPoleJ, mul_sub] using hright.sub hleft
  have hcorrection : Continuous
      (centeredPolynomialLift (reflectedPoleJCorrection p)) :=
    continuous_centeredPolynomialLift_complete _
  have hpoly : IntervalIntegrable (fun x ↦
      r x * centeredPolynomialLift (reflectedPoleJCorrection p) x)
      volume (-1) 1 := (hr.mul hcorrection).intervalIntegrable (-1) 1
  apply (hfull.sub hpoly).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ))] with x hx hx1
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  change r x * factorTwoReflectedPoleJ (centeredPolynomialLift p) x -
      r x * centeredPolynomialLift (reflectedPoleJCorrection p) x =
    r x * reflectedPoleJLogSelector p x
  rw [reflectedPoleJ_centeredPolynomialLift p hxIoo]
  unfold reflectedPoleJLogSelector
  ring

private theorem intervalIntegrable_mul_fixedLagK
    (τ : ℝ) (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦ r x * factorTwoFixedLagK τ p x)
      volume (-1) 1 := by
  have hright :=
    intervalIntegrable_mul_factorTwoFixedLagRightRepresenter τ p r hp hr
  have hleft :=
    intervalIntegrable_mul_factorTwoFixedLagLeftRepresenter τ r p hr hp
  simpa only [factorTwoFixedLagK, mul_add, mul_comm] using hright.add hleft

private theorem intervalIntegrable_mul_fixedLagJ
    (τ : ℝ) (p r : ℝ → ℝ) (hp : Continuous p) (hr : Continuous r) :
    IntervalIntegrable (fun x ↦ r x * factorTwoFixedLagJ τ p x)
      volume (-1) 1 := by
  have hright :=
    intervalIntegrable_mul_factorTwoFixedLagRightRepresenter τ p r hp hr
  have hleft :=
    intervalIntegrable_mul_factorTwoFixedLagLeftRepresenter τ r p hr hp
  simpa only [factorTwoFixedLagJ, mul_sub, mul_comm] using hright.sub hleft

private theorem intervalIntegrable_analyticEvenRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hE := intervalIntegrable_mul_continuousLagK_of_bounded
    factorTwoSymmetricAnalyticLag (centeredPolynomialLift pE) r
    measurable_factorTwoSymmetricAnalyticLag
    (continuous_centeredPolynomialLift_complete pE) hr (3 / 8000)
    (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht)
  have hO := intervalIntegrable_mul_continuousLagJ_of_bounded
    factorTwoAlternatingAnalyticLag (centeredPolynomialLift pO) r
    measurable_factorTwoAlternatingAnalyticLag
    (continuous_centeredPolynomialLift_complete pO) hr (1 / 1000)
    (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)
  apply ((hE.const_mul (a / 2)).add (hO.const_mul (b / 2))).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenAnalyticEvenRepresenter
  ring

private theorem intervalIntegrable_analyticOddRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hO := intervalIntegrable_mul_continuousLagK_of_bounded
    factorTwoSymmetricAnalyticLag (centeredPolynomialLift pO) r
    measurable_factorTwoSymmetricAnalyticLag
    (continuous_centeredPolynomialLift_complete pO) hr (3 / 8000)
    (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht)
  have hE := intervalIntegrable_mul_continuousLagJ_of_bounded
    factorTwoAlternatingAnalyticLag (centeredPolynomialLift pE) r
    measurable_factorTwoAlternatingAnalyticLag
    (continuous_centeredPolynomialLift_complete pE) hr (1 / 1000)
    (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)
  apply ((hO.const_mul (a / 2)).sub (hE.const_mul (b / 2))).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenAnalyticOddRepresenter
  ring

private theorem intervalIntegrable_forwardEvenRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hE := intervalIntegrable_mul_forwardPoleKLogSelector pE r hr
  have hO := intervalIntegrable_mul_forwardPoleLLogSelector pO r hr
  apply ((hE.const_mul (-(a / 4))).sub (hO.const_mul (b / 4))).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenForwardEvenRepresenter
  ring

private theorem intervalIntegrable_forwardOddRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hO := intervalIntegrable_mul_forwardPoleKLogSelector pO r hr
  have hE := intervalIntegrable_mul_forwardPoleLLogSelector pE r hr
  apply ((hO.const_mul (-(a / 4))).add (hE.const_mul (b / 4))).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenForwardOddRepresenter
  ring

theorem intervalIntegrable_reflectedEvenRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hE := intervalIntegrable_mul_reflectedPoleKLogSelector pE r hr
  have hO := intervalIntegrable_mul_reflectedPoleJLogSelector pO r hr
  apply ((hE.const_mul (-(a / 4))).add (hO.const_mul (b / 4))).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenReflectedEvenRepresenter
  ring

theorem intervalIntegrable_reflectedOddRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hO := intervalIntegrable_mul_reflectedPoleKLogSelector pO r hr
  have hE := intervalIntegrable_mul_reflectedPoleJLogSelector pE r hr
  apply ((hO.const_mul (-(a / 4))).sub (hE.const_mul (b / 4))).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenReflectedOddRepresenter
  ring

private theorem intervalIntegrable_primeEvenRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hE := intervalIntegrable_mul_fixedLagK primeLag
    (centeredPolynomialLift pE) r
    (continuous_centeredPolynomialLift_complete pE) hr
  have hO := intervalIntegrable_mul_fixedLagJ primeLag
    (centeredPolynomialLift pO) r
    (continuous_centeredPolynomialLift_complete pO) hr
  apply (((hE.const_mul a).add (hO.const_mul b)).const_mul
    (-primeCoefficient)).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenPrimeEvenRepresenter
  ring

private theorem intervalIntegrable_primeOddRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hO := intervalIntegrable_mul_fixedLagK primeLag
    (centeredPolynomialLift pO) r
    (continuous_centeredPolynomialLift_complete pO) hr
  have hE := intervalIntegrable_mul_fixedLagJ primeLag
    (centeredPolynomialLift pE) r
    (continuous_centeredPolynomialLift_complete pE) hr
  apply (((hO.const_mul a).sub (hE.const_mul b)).const_mul
    (-primeCoefficient)).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenPrimeOddRepresenter
  ring

/-- The complete even representer is interval-integrable against every
continuous residual profile. -/
theorem intervalIntegrable_completeEvenRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hC := intervalIntegrable_cleanSurvivor_mul pE r hr
  have hA := intervalIntegrable_analyticEvenRepresenter_mul pE pO r hr a b
  have hF := intervalIntegrable_forwardEvenRepresenter_mul pE pO r hr a b
  have hR := intervalIntegrable_reflectedEvenRepresenter_mul pE pO r hr a b
  have hP := intervalIntegrable_primeEvenRepresenter_mul pE pO r hr a b
  apply ((((hC.add hA).add hF).add hR).add hP).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenEvenMixedRepresenter
  ring

/-- The complete odd representer is interval-integrable against every
continuous residual profile. -/
theorem intervalIntegrable_completeOddRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hC := intervalIntegrable_cleanSurvivor_mul pO r hr
  have hA := intervalIntegrable_analyticOddRepresenter_mul pE pO r hr a b
  have hF := intervalIntegrable_forwardOddRepresenter_mul pE pO r hr a b
  have hR := intervalIntegrable_reflectedOddRepresenter_mul pE pO r hr a b
  have hP := intervalIntegrable_primeOddRepresenter_mul pE pO r hr a b
  apply ((((hC.add hA).add hF).add hR).add hP).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenOddMixedRepresenter
  ring

private theorem intervalIntegrable_correlationBilinear_div_two_sub
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable (fun t ↦
      factorTwoCenteredCorrelationBilinear u v t / (2 - t))
      volume 0 2 := by
  have huv := intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
    u v hu hv
  have hvu := intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
    v u hv hu
  apply ((huv.add hvu).const_mul (1 / 2 : ℝ)).congr
  intro t _ht
  unfold factorTwoCenteredCorrelationBilinear
  ring

private theorem intervalIntegrable_crossDifference_div_two_sub
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o) :
    IntervalIntegrable (fun t ↦
      factorTwoP67ResidualAlternatingCrossDifference e o t / (2 - t))
      volume 0 2 := by
  have hoe := intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
    o e ho he
  have heo := intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
    e o he ho
  apply (hoe.sub heo).congr
  intro t _ht
  unfold factorTwoP67ResidualAlternatingCrossDifference
  ring

private theorem factorTwoIntrinsicElevenMixedPairing_add
    (FE₁ FE₂ FO₁ FO₂ e o : ℝ → ℝ)
    (hE₁ : IntervalIntegrable (fun x ↦ FE₁ x * e x) volume (-1) 1)
    (hE₂ : IntervalIntegrable (fun x ↦ FE₂ x * e x) volume (-1) 1)
    (hO₁ : IntervalIntegrable (fun x ↦ FO₁ x * o x) volume (-1) 1)
    (hO₂ : IntervalIntegrable (fun x ↦ FO₂ x * o x) volume (-1) 1) :
    factorTwoIntrinsicElevenMixedPairing
        (fun x ↦ FE₁ x + FE₂ x) (fun x ↦ FO₁ x + FO₂ x) e o =
      factorTwoIntrinsicElevenMixedPairing FE₁ FO₁ e o +
        factorTwoIntrinsicElevenMixedPairing FE₂ FO₂ e o := by
  unfold factorTwoIntrinsicElevenMixedPairing
  rw [show (fun x : ℝ ↦ (FE₁ x + FE₂ x) * e x) = fun x ↦
      FE₁ x * e x + FE₂ x * e x by
    funext x
    ring,
    intervalIntegral.integral_add hE₁ hE₂,
    show (fun x : ℝ ↦ (FO₁ x + FO₂ x) * o x) = fun x ↦
      FO₁ x * o x + FO₂ x * o x by
        funext x
        ring,
    intervalIntegral.integral_add hO₁ hO₂]
  ring

/-! ## Exact component pairings -/

/-- The four bounded analytic rows are exactly the analytic `FE/FO`
pairing. -/
theorem factorTwoP67ResidualAnalyticMixed_eq_intrinsicElevenPairing
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o) (a b : ℝ) :
    factorTwoP67ResidualAnalyticMixed
        (centeredPolynomialLift pE) (centeredPolynomialLift pO)
        e o a b =
      factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b)
        (factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b)
        e o := by
  have hpE := continuous_centeredPolynomialLift_complete pE
  have hpO := continuous_centeredPolynomialLift_complete pO
  have hSE :=
    integral_factorTwoSymmetricAnalyticLag_mul_correlationBilinear_eq_K
      (centeredPolynomialLift pE) e hpE he
  have hSO :=
    integral_factorTwoSymmetricAnalyticLag_mul_correlationBilinear_eq_K
      (centeredPolynomialLift pO) o hpO ho
  have hDE :=
    integral_factorTwoAlternatingAnalyticLag_mul_crossDifference_eq_neg_J
      (centeredPolynomialLift pE) o hpE ho
  have hDO :=
    integral_factorTwoAlternatingAnalyticLag_mul_crossDifference_eq_J
      e (centeredPolynomialLift pO) he hpO
  have hEK := intervalIntegrable_mul_continuousLagK_of_bounded
    factorTwoSymmetricAnalyticLag (centeredPolynomialLift pE) e
    measurable_factorTwoSymmetricAnalyticLag hpE he (3 / 8000)
    (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht)
  have hEJ := intervalIntegrable_mul_continuousLagJ_of_bounded
    factorTwoAlternatingAnalyticLag (centeredPolynomialLift pO) e
    measurable_factorTwoAlternatingAnalyticLag hpO he (1 / 1000)
    (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)
  have hOK := intervalIntegrable_mul_continuousLagK_of_bounded
    factorTwoSymmetricAnalyticLag (centeredPolynomialLift pO) o
    measurable_factorTwoSymmetricAnalyticLag hpO ho (3 / 8000)
    (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht)
  have hOJ := intervalIntegrable_mul_continuousLagJ_of_bounded
    factorTwoAlternatingAnalyticLag (centeredPolynomialLift pE) o
    measurable_factorTwoAlternatingAnalyticLag hpE ho (1 / 1000)
    (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht)
  change
    a * ((∫ t : ℝ in 0..2,
          factorTwoSymmetricAnalyticLag t *
            factorTwoCenteredCorrelationBilinear
              (centeredPolynomialLift pE) e t) +
        ∫ t : ℝ in 0..2,
          factorTwoSymmetricAnalyticLag t *
            factorTwoCenteredCorrelationBilinear
              (centeredPolynomialLift pO) o t) +
      (b / 2) * ((∫ t : ℝ in 0..2,
          factorTwoAlternatingAnalyticLag t *
            factorTwoP67ResidualAlternatingCrossDifference
              (centeredPolynomialLift pE) o t) +
        ∫ t : ℝ in 0..2,
          factorTwoAlternatingAnalyticLag t *
            factorTwoP67ResidualAlternatingCrossDifference
              e (centeredPolynomialLift pO) t) = _
  unfold factorTwoP67ResidualAlternatingCrossDifference
  rw [hSE, hSO, hDE, hDO]
  unfold factorTwoIntrinsicElevenMixedPairing
    factorTwoIntrinsicElevenAnalyticEvenRepresenter
    factorTwoIntrinsicElevenAnalyticOddRepresenter
  rw [show (fun x : ℝ ↦
      ((a / 2) * factorTwoContinuousLagK factorTwoSymmetricAnalyticLag
          (centeredPolynomialLift pE) x +
        (b / 2) * factorTwoContinuousLagJ factorTwoAlternatingAnalyticLag
          (centeredPolynomialLift pO) x) * e x) = fun x ↦
      (a / 2) * (e x * factorTwoContinuousLagK factorTwoSymmetricAnalyticLag
          (centeredPolynomialLift pE) x) +
        (b / 2) * (e x * factorTwoContinuousLagJ factorTwoAlternatingAnalyticLag
          (centeredPolynomialLift pO) x) by
    funext x
    ring,
    intervalIntegral.integral_add
      (hEK.const_mul (a / 2)) (hEJ.const_mul (b / 2)),
    show (fun x : ℝ ↦
      ((a / 2) * factorTwoContinuousLagK factorTwoSymmetricAnalyticLag
          (centeredPolynomialLift pO) x -
        (b / 2) * factorTwoContinuousLagJ factorTwoAlternatingAnalyticLag
          (centeredPolynomialLift pE) x) * o x) = fun x ↦
      (a / 2) * (o x * factorTwoContinuousLagK factorTwoSymmetricAnalyticLag
          (centeredPolynomialLift pO) x) -
        (b / 2) * (o x * factorTwoContinuousLagJ factorTwoAlternatingAnalyticLag
          (centeredPolynomialLift pE) x) by
    funext x
    ring,
    intervalIntegral.integral_sub
      (hOK.const_mul (a / 2)) (hOJ.const_mul (b / 2))]
  repeat rw [intervalIntegral.integral_const_mul]
  ring

/-- The forward-Hankel half-cross is exactly the reduced logarithmic
forward `FE/FO` pairing after moment-gap cancellation. -/
theorem factorTwoP67ResidualForwardHankelMixed_eq_intrinsicElevenPairing
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o)
    {k : ℕ}
    (heGap : centeredLegendreMomentsVanishBelow e k)
    (hoGap : centeredLegendreMomentsVanishBelow o k)
    (hpEdeg : pE.natDegree < k) (hpOdeg : pO.natDegree < k)
    (a b : ℝ) :
    factorTwoP67ResidualForwardHankelMixed
        (centeredPolynomialLift pE) (centeredPolynomialLift pO)
        e o a b =
      factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b)
        (factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b)
        e o := by
  have hpE := continuous_centeredPolynomialLift_complete pE
  have hpO := continuous_centeredPolynomialLift_complete pO
  have hEK := integral_mul_forwardPoleK_centeredPolynomialLift_eq_logSelector
    pE e he heGap hpEdeg
  have hOK := integral_mul_forwardPoleK_centeredPolynomialLift_eq_logSelector
    pO o ho hoGap hpOdeg
  have hOL := integral_mul_forwardPoleL_centeredPolynomialLift_eq_logSelector
    pE o ho hoGap hpEdeg
  have hEL := integral_mul_forwardPoleL_centeredPolynomialLift_eq_logSelector
    pO e he heGap hpOdeg
  rw [factorTwoP67ResidualForwardHankelMixed_eq_pairings
      (centeredPolynomialLift pE) (centeredPolynomialLift pO) e o
      hpE hpO he ho a b,
    hEK, hOK, hOL, hEL]
  have hEKInt := intervalIntegrable_mul_forwardPoleKLogSelector pE e he
  have hELInt := intervalIntegrable_mul_forwardPoleLLogSelector pO e he
  have hOKInt := intervalIntegrable_mul_forwardPoleKLogSelector pO o ho
  have hOLInt := intervalIntegrable_mul_forwardPoleLLogSelector pE o ho
  unfold factorTwoIntrinsicElevenMixedPairing
    factorTwoIntrinsicElevenForwardEvenRepresenter
    factorTwoIntrinsicElevenForwardOddRepresenter
  rw [show (fun x : ℝ ↦
      (-(a / 4) * forwardPoleKLogSelector pE x -
        (b / 4) * forwardPoleLLogSelector pO x) * e x) = fun x ↦
      (-(a / 4)) * (e x * forwardPoleKLogSelector pE x) -
        (b / 4) * (e x * forwardPoleLLogSelector pO x) by
    funext x
    ring,
    intervalIntegral.integral_sub
      (hEKInt.const_mul (-(a / 4))) (hELInt.const_mul (b / 4)),
    show (fun x : ℝ ↦
      (-(a / 4) * forwardPoleKLogSelector pO x +
        (b / 4) * forwardPoleLLogSelector pE x) * o x) = fun x ↦
      (-(a / 4)) * (o x * forwardPoleKLogSelector pO x) +
        (b / 4) * (o x * forwardPoleLLogSelector pE x) by
    funext x
    ring,
    intervalIntegral.integral_add
      (hOKInt.const_mul (-(a / 4))) (hOLInt.const_mul (b / 4))]
  repeat rw [intervalIntegral.integral_const_mul]
  ring

/-- Setting the phase to zero in the generic endpoint decomposition isolates
the clean survivor pairing without repeating the raw-log cancellation proof. -/
theorem factorTwoIntrinsicNineNonpolynomialMixed_zero_eq_cleanPairing
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) o)
    {k : ℕ}
    (heGap : centeredLegendreMomentsVanishBelow e k)
    (hoGap : centeredLegendreMomentsVanishBelow o k)
    (hpEdeg : pE.natDegree < k) (hpOdeg : pO.natDegree < k) :
    factorTwoIntrinsicNineNonpolynomialMixed
        (centeredPolynomialLift pE) (centeredPolynomialLift pO)
        e o 0 0 =
      factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenCleanSurvivorRepresenter pE)
        (factorTwoIntrinsicElevenCleanSurvivorRepresenter pO)
        e o := by
  have h0 := factorTwoEndpointLowTailMixed_centeredPolynomialLift_eq
    pE pO e o he ho heLocal hoLocal heGap hoGap hpEdeg hpOdeg 0 0
  have hclean := factorTwoIntrinsicElevenCleanMixedPairing_eq
    pE pO e o he ho heLocal hoLocal heGap hoGap hpEdeg hpOdeg
  rw [hclean]
  simpa [factorTwoEndpointLowTailMixed,
    factorTwoP67ResidualSmoothMixedIntegrand] using h0.symm

set_option maxHeartbeats 800000 in
/-- The nonpolynomial aggregate is its zero-phase clean part plus exactly the
reflected pole and retained prime phase polarizations. -/
theorem factorTwoIntrinsicNineNonpolynomialMixed_eq_zero_add_reflected_add_prime
    (eLow oLow eR oR : ℝ → ℝ) (a b : ℝ) :
    factorTwoIntrinsicNineNonpolynomialMixed eLow oLow eR oR a b =
      factorTwoIntrinsicNineNonpolynomialMixed eLow oLow eR oR 0 0 +
        factorTwoIntrinsicElevenReflectedMixed eLow oLow eR oR a b +
        factorTwoIntrinsicElevenPrimeMixed eLow oLow eR oR a b := by
  unfold factorTwoIntrinsicNineNonpolynomialMixed
    factorTwoIntrinsicElevenReflectedMixed
    factorTwoIntrinsicElevenPrimeMixed primeCoefficient primeLag
    factorTwoCenteredPhaseCorrelation
  simp only [mul_zero, zero_mul, add_zero, sub_zero, neg_zero,
    zero_div]
  rw [intervalIntegral.integral_zero]
  ring

/-- The reflected phase polarization is exactly the reduced logarithmic
reflected `FE/FO` pairing. -/
theorem factorTwoIntrinsicElevenReflectedMixed_eq_pairing
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o)
    {k : ℕ}
    (heGap : centeredLegendreMomentsVanishBelow e k)
    (hoGap : centeredLegendreMomentsVanishBelow o k)
    (hpEdeg : pE.natDegree < k) (hpOdeg : pO.natDegree < k)
    (a b : ℝ) :
    factorTwoIntrinsicElevenReflectedMixed
        (centeredPolynomialLift pE) (centeredPolynomialLift pO)
        e o a b =
      factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b)
        (factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b)
        e o := by
  let PE : ℝ → ℝ := centeredPolynomialLift pE
  let PO : ℝ → ℝ := centeredPolynomialLift pO
  let BE : ℝ → ℝ := factorTwoCenteredCorrelationBilinear PE e
  let BO : ℝ → ℝ := factorTwoCenteredCorrelationBilinear PO o
  let DE : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference PE o
  let DO : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference e PO
  have hPE : Continuous PE := continuous_centeredPolynomialLift_complete pE
  have hPO : Continuous PO := continuous_centeredPolynomialLift_complete pO
  have hFull := intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    (PE + e) (PO + o) (hPE.add he) (hPO.add ho) a (-b)
  have hLow := intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    PE PO hPE hPO a (-b)
  have hTail := intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    e o he ho a (-b)
  have hDiff :
      ((∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation (PE + e) (PO + o) a (-b) t /
            (2 - t)) -
        (∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation PE PO a (-b) t / (2 - t)) -
        ∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation e o a (-b) t / (2 - t)) =
        ∫ t : ℝ in 0..2,
          (2 * a * (BE t + BO t) - b * (DE t + DO t)) / (2 - t) := by
    rw [← intervalIntegral.integral_sub hFull hLow,
      ← intervalIntegral.integral_sub (hFull.sub hLow) hTail]
    apply intervalIntegral.integral_congr
    intro t _ht
    have hphase := factorTwoCenteredPhaseCorrelation_add_add_sub
      PE e PO o hPE he hPO ho a (-b) t
    dsimp only [BE, BO, DE, DO]
    calc
      factorTwoCenteredPhaseCorrelation (PE + e) (PO + o) a (-b) t /
            (2 - t) -
          factorTwoCenteredPhaseCorrelation PE PO a (-b) t / (2 - t) -
          factorTwoCenteredPhaseCorrelation e o a (-b) t / (2 - t) =
        (factorTwoCenteredPhaseCorrelation (PE + e) (PO + o) a (-b) t -
            factorTwoCenteredPhaseCorrelation PE PO a (-b) t -
            factorTwoCenteredPhaseCorrelation e o a (-b) t) / (2 - t) := by
          ring
      _ = _ := by rw [hphase]; ring
  have hBEInt : IntervalIntegrable (fun t ↦ BE t / (2 - t))
      volume 0 2 := by
    dsimp only [BE]
    exact intervalIntegrable_correlationBilinear_div_two_sub PE e hPE he
  have hBOInt : IntervalIntegrable (fun t ↦ BO t / (2 - t))
      volume 0 2 := by
    dsimp only [BO]
    exact intervalIntegrable_correlationBilinear_div_two_sub PO o hPO ho
  have hDEInt : IntervalIntegrable (fun t ↦ DE t / (2 - t))
      volume 0 2 := by
    dsimp only [DE]
    exact intervalIntegrable_crossDifference_div_two_sub PE o hPE ho
  have hDOInt : IntervalIntegrable (fun t ↦ DO t / (2 - t))
      volume 0 2 := by
    dsimp only [DO]
    exact intervalIntegrable_crossDifference_div_two_sub e PO he hPO
  have hRows :
      (∫ t : ℝ in 0..2,
          (2 * a * (BE t + BO t) - b * (DE t + DO t)) / (2 - t)) =
        2 * a * ((∫ t : ℝ in 0..2, BE t / (2 - t)) +
          ∫ t : ℝ in 0..2, BO t / (2 - t)) -
        b * ((∫ t : ℝ in 0..2, DE t / (2 - t)) +
          ∫ t : ℝ in 0..2, DO t / (2 - t)) := by
    rw [show (fun t : ℝ ↦
        (2 * a * (BE t + BO t) - b * (DE t + DO t)) / (2 - t)) =
      fun t ↦
        (2 * a) * (BE t / (2 - t)) +
          (2 * a) * (BO t / (2 - t)) -
          (b * (DE t / (2 - t)) + b * (DO t / (2 - t))) by
      funext t
      ring,
      intervalIntegral.integral_sub
        ((hBEInt.const_mul (2 * a)).add (hBOInt.const_mul (2 * a)))
        ((hDEInt.const_mul b).add (hDOInt.const_mul b)),
      intervalIntegral.integral_add
        (hBEInt.const_mul (2 * a)) (hBOInt.const_mul (2 * a)),
      intervalIntegral.integral_add
        (hDEInt.const_mul b) (hDOInt.const_mul b)]
    repeat rw [intervalIntegral.integral_const_mul]
    ring
  have hBE : (∫ t : ℝ in 0..2, BE t / (2 - t)) =
      (1 / 2 : ℝ) *
        ∫ x : ℝ in -1..1, e x * reflectedPoleKLogSelector pE x := by
    dsimp only [BE, PE]
    rw [integral_correlationBilinear_div_two_sub_eq_reflectedPoleK
        (centeredPolynomialLift pE) e hPE he,
      integral_mul_reflectedPoleK_centeredPolynomialLift_eq_logSelector
        pE e he heGap hpEdeg]
  have hBO : (∫ t : ℝ in 0..2, BO t / (2 - t)) =
      (1 / 2 : ℝ) *
        ∫ x : ℝ in -1..1, o x * reflectedPoleKLogSelector pO x := by
    dsimp only [BO, PO]
    rw [integral_correlationBilinear_div_two_sub_eq_reflectedPoleK
        (centeredPolynomialLift pO) o hPO ho,
      integral_mul_reflectedPoleK_centeredPolynomialLift_eq_logSelector
        pO o ho hoGap hpOdeg]
  have hDE : (∫ t : ℝ in 0..2, DE t / (2 - t)) =
      -(∫ x : ℝ in -1..1, o x * reflectedPoleJLogSelector pE x) := by
    dsimp only [DE, PE]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    rw [integral_crossDifference_div_two_sub_eq_neg_reflectedPoleJ
        (centeredPolynomialLift pE) o hPE ho,
      integral_mul_reflectedPoleJ_centeredPolynomialLift_eq_logSelector
        pE o ho hoGap hpEdeg]
  have hDO : (∫ t : ℝ in 0..2, DO t / (2 - t)) =
      ∫ x : ℝ in -1..1, e x * reflectedPoleJLogSelector pO x := by
    dsimp only [DO, PO]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    rw [integral_crossDifference_div_two_sub_eq_reflectedPoleJ
        e (centeredPolynomialLift pO) he hPO,
      integral_mul_reflectedPoleJ_centeredPolynomialLift_eq_logSelector
        pO e he heGap hpOdeg]
  unfold factorTwoIntrinsicElevenReflectedMixed
  change -(1 / 4 : ℝ) *
      ((∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation (PE + e) (PO + o) a (-b) t /
            (2 - t)) -
        (∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation PE PO a (-b) t / (2 - t)) -
        ∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation e o a (-b) t / (2 - t)) = _
  rw [hDiff, hRows, hBE, hBO, hDE, hDO]
  have hEK := intervalIntegrable_mul_reflectedPoleKLogSelector pE e he
  have hEJ := intervalIntegrable_mul_reflectedPoleJLogSelector pO e he
  have hOK := intervalIntegrable_mul_reflectedPoleKLogSelector pO o ho
  have hOJ := intervalIntegrable_mul_reflectedPoleJLogSelector pE o ho
  unfold factorTwoIntrinsicElevenMixedPairing
    factorTwoIntrinsicElevenReflectedEvenRepresenter
    factorTwoIntrinsicElevenReflectedOddRepresenter
  rw [show (fun x : ℝ ↦
      (-(a / 4) * reflectedPoleKLogSelector pE x +
        (b / 4) * reflectedPoleJLogSelector pO x) * e x) = fun x ↦
      (-(a / 4)) * (e x * reflectedPoleKLogSelector pE x) +
        (b / 4) * (e x * reflectedPoleJLogSelector pO x) by
    funext x
    ring,
    intervalIntegral.integral_add
      (hEK.const_mul (-(a / 4))) (hEJ.const_mul (b / 4)),
    show (fun x : ℝ ↦
      (-(a / 4) * reflectedPoleKLogSelector pO x -
        (b / 4) * reflectedPoleJLogSelector pE x) * o x) = fun x ↦
      (-(a / 4)) * (o x * reflectedPoleKLogSelector pO x) -
        (b / 4) * (o x * reflectedPoleJLogSelector pE x) by
    funext x
    ring,
    intervalIntegral.integral_sub
      (hOK.const_mul (-(a / 4))) (hOJ.const_mul (b / 4))]
  repeat rw [intervalIntegral.integral_const_mul]
  ring

/-- The retained `p = 3` phase polarization is exactly the fixed-lag
`FE/FO` pairing. -/
theorem factorTwoIntrinsicElevenPrimeMixed_eq_pairing
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o) (a b : ℝ) :
    factorTwoIntrinsicElevenPrimeMixed
        (centeredPolynomialLift pE) (centeredPolynomialLift pO)
        e o a b =
      factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b)
        (factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b)
        e o := by
  let PE : ℝ → ℝ := centeredPolynomialLift pE
  let PO : ℝ → ℝ := centeredPolynomialLift pO
  let BE : ℝ → ℝ := factorTwoCenteredCorrelationBilinear PE e
  let BO : ℝ → ℝ := factorTwoCenteredCorrelationBilinear PO o
  let DE : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference PE o
  let DO : ℝ → ℝ := factorTwoP67ResidualAlternatingCrossDifference e PO
  have hPE : Continuous PE := continuous_centeredPolynomialLift_complete pE
  have hPO : Continuous PO := continuous_centeredPolynomialLift_complete pO
  have hτ12 := factorTwoPrimeShift_div_endpointA_mem_one_two
  have hτ : primeLag ∈ Icc (0 : ℝ) 2 := by
    dsimp only [primeLag]
    exact ⟨(by linarith [hτ12.1]), hτ12.2⟩
  have hphase := factorTwoCenteredPhaseCorrelation_add_add_sub
    PE e PO o hPE he hPO ho a b primeLag
  have hBE : BE primeLag =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        e x * factorTwoFixedLagK primeLag PE x := by
    dsimp only [BE]
    simpa only [mul_comm] using
      correlationBilinear_eq_fixedLagK primeLag PE e hPE he hτ
  have hBO : BO primeLag =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        o x * factorTwoFixedLagK primeLag PO x := by
    dsimp only [BO]
    simpa only [mul_comm] using
      correlationBilinear_eq_fixedLagK primeLag PO o hPO ho hτ
  have hDE : DE primeLag =
      -(∫ x : ℝ in -1..1, o x * factorTwoFixedLagJ primeLag PE x) := by
    dsimp only [DE]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    simpa only [mul_comm] using
      crossDifference_eq_neg_fixedLagJ primeLag PE o hPE ho hτ
  have hDO : DO primeLag =
      ∫ x : ℝ in -1..1, e x * factorTwoFixedLagJ primeLag PO x := by
    dsimp only [DO]
    unfold factorTwoP67ResidualAlternatingCrossDifference
    simpa only [mul_comm] using
      crossDifference_eq_fixedLagJ primeLag e PO he hPO hτ
  have hEK := intervalIntegrable_mul_fixedLagK primeLag PE e hPE he
  have hEJ := intervalIntegrable_mul_fixedLagJ primeLag PO e hPO he
  have hOK := intervalIntegrable_mul_fixedLagK primeLag PO o hPO ho
  have hOJ := intervalIntegrable_mul_fixedLagJ primeLag PE o hPE ho
  unfold factorTwoIntrinsicElevenPrimeMixed
  change -primeCoefficient *
      (factorTwoCenteredPhaseCorrelation (PE + e) (PO + o) a b primeLag -
        factorTwoCenteredPhaseCorrelation PE PO a b primeLag -
        factorTwoCenteredPhaseCorrelation e o a b primeLag) = _
  rw [hphase]
  change -primeCoefficient *
      (2 * a * (BE primeLag + BO primeLag) +
        b * (DE primeLag + DO primeLag)) = _
  rw [hBE, hBO, hDE, hDO]
  unfold factorTwoIntrinsicElevenMixedPairing
    factorTwoIntrinsicElevenPrimeEvenRepresenter
    factorTwoIntrinsicElevenPrimeOddRepresenter
  rw [show (fun x : ℝ ↦
      (-primeCoefficient *
          (a * factorTwoFixedLagK primeLag (centeredPolynomialLift pE) x +
            b * factorTwoFixedLagJ primeLag (centeredPolynomialLift pO) x)) *
        e x) = fun x ↦
      (-primeCoefficient * a) *
          (e x * factorTwoFixedLagK primeLag PE x) +
        (-primeCoefficient * b) *
          (e x * factorTwoFixedLagJ primeLag PO x) by
    funext x
    dsimp only [PE, PO]
    ring,
    intervalIntegral.integral_add
      (hEK.const_mul (-primeCoefficient * a))
      (hEJ.const_mul (-primeCoefficient * b)),
    show (fun x : ℝ ↦
      (-primeCoefficient *
          (a * factorTwoFixedLagK primeLag (centeredPolynomialLift pO) x -
            b * factorTwoFixedLagJ primeLag (centeredPolynomialLift pE) x)) *
        o x) = fun x ↦
      (-primeCoefficient * a) *
          (o x * factorTwoFixedLagK primeLag PO x) +
        (primeCoefficient * b) *
          (o x * factorTwoFixedLagJ primeLag PE x) by
    funext x
    dsimp only [PE, PO]
    ring,
    intervalIntegral.integral_add
      (hOK.const_mul (-primeCoefficient * a))
      (hOJ.const_mul (primeCoefficient * b))]
  repeat rw [intervalIntegral.integral_const_mul]
  ring

/-- Expanding the assembled pair of complete representers gives the five
component pairings exactly.  This algebraic assembly only needs continuity;
moment gaps enter later when the individual components are identified with
the corresponding low--tail rows. -/
theorem factorTwoIntrinsicElevenMixedPairing_complete_eq_components
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o) (a b : ℝ) :
    factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b)
        (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b)
        e o =
      factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenCleanSurvivorRepresenter pE)
          (factorTwoIntrinsicElevenCleanSurvivorRepresenter pO) e o +
        factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b)
          (factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b) e o +
        factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b)
          (factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b) e o +
        factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b)
          (factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b) e o +
        factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b)
          (factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b) e o := by
  have hCE := intervalIntegrable_cleanSurvivor_mul pE e he
  have hCO := intervalIntegrable_cleanSurvivor_mul pO o ho
  have hAE := intervalIntegrable_analyticEvenRepresenter_mul
    pE pO e he a b
  have hAO := intervalIntegrable_analyticOddRepresenter_mul
    pE pO o ho a b
  have hFE := intervalIntegrable_forwardEvenRepresenter_mul
    pE pO e he a b
  have hFO := intervalIntegrable_forwardOddRepresenter_mul
    pE pO o ho a b
  have hRE := intervalIntegrable_reflectedEvenRepresenter_mul
    pE pO e he a b
  have hRO := intervalIntegrable_reflectedOddRepresenter_mul
    pE pO o ho a b
  have hPrE := intervalIntegrable_primeEvenRepresenter_mul
    pE pO e he a b
  have hPrO := intervalIntegrable_primeOddRepresenter_mul
    pE pO o ho a b
  have hECA := hCE.add hAE
  have hECAF := hECA.add hFE
  have hECAFR := hECAF.add hRE
  have hOCA := hCO.add hAO
  have hOCAF := hOCA.add hFO
  have hOCAFR := hOCAF.add hRO
  unfold factorTwoIntrinsicElevenMixedPairing
    factorTwoIntrinsicElevenEvenMixedRepresenter
    factorTwoIntrinsicElevenOddMixedRepresenter
  rw [show (fun x : ℝ ↦
      (factorTwoIntrinsicElevenCleanSurvivorRepresenter pE x +
          factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b x +
          factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b x +
          factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b x +
          factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b x) * e x) =
    fun x ↦
      (((factorTwoIntrinsicElevenCleanSurvivorRepresenter pE x * e x +
          factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b x * e x) +
        factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b x * e x) +
        factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b x * e x) +
        factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b x * e x by
    funext x
    ring,
    intervalIntegral.integral_add hECAFR hPrE,
    intervalIntegral.integral_add hECAF hRE,
    intervalIntegral.integral_add hECA hFE,
    intervalIntegral.integral_add hCE hAE,
    show (fun x : ℝ ↦
      (factorTwoIntrinsicElevenCleanSurvivorRepresenter pO x +
          factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b x +
          factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b x +
          factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b x +
          factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b x) * o x) =
    fun x ↦
      (((factorTwoIntrinsicElevenCleanSurvivorRepresenter pO x * o x +
          factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b x * o x) +
        factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b x * o x) +
        factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b x * o x) +
        factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b x * o x by
    funext x
    ring,
    intervalIntegral.integral_add hOCAFR hPrO,
    intervalIntegral.integral_add hOCAF hRO,
    intervalIntegral.integral_add hOCA hFO,
    intervalIntegral.integral_add hCO hAO]
  ring

/-- The complete cutoff-eleven low--tail half-cross is exactly the pairing
with the assembled even and odd representers.  No parity or phase-disk
hypothesis is needed for this identity. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_eq_intrinsicElevenPairing
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heGap : centeredLegendreMomentsVanishBelow e 11)
    (hoGap : centeredLegendreMomentsVanishBelow o 11)
    (hpEdeg : pE.natDegree < 11) (hpOdeg : pO.natDegree < 11)
    (a b : ℝ) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) e
        (centeredPolynomialLift pO) o a b =
      factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b)
        (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b)
        e o := by
  have hPE := continuous_centeredPolynomialLift_complete pE
  have hPO := continuous_centeredPolynomialLift_complete pO
  have hlinearE : (∫ t : ℝ in 0..2,
      t * factorTwoP67ResidualAlternatingCrossDifference
        (centeredPolynomialLift pE) o t) = 0 := by
    simpa only [factorTwoP67ResidualAlternatingCrossDifference] using
      integral_linear_mul_crossDifference_eq_zero_of_second_momentGap
        (centeredPolynomialLift pE) o hPE ho hoGap (by norm_num)
  have hlinearORaw :=
    integral_linear_mul_crossDifference_eq_zero_of_second_momentGap
      (centeredPolynomialLift pO) e hPO he heGap (by norm_num)
  have hlinearO : (∫ t : ℝ in 0..2,
      t * factorTwoP67ResidualAlternatingCrossDifference
        e (centeredPolynomialLift pO) t) = 0 := by
    rw [show (fun t : ℝ ↦
        t * factorTwoP67ResidualAlternatingCrossDifference
          e (centeredPolynomialLift pO) t) =
      fun t ↦ -(t *
        (factorTwoCenteredCrossCorrelation e (centeredPolynomialLift pO) t -
          factorTwoCenteredCrossCorrelation (centeredPolynomialLift pO) e t)) by
      funext t
      unfold factorTwoP67ResidualAlternatingCrossDifference
      ring,
      intervalIntegral.integral_neg, hlinearORaw, neg_zero]
  have hSmooth :=
    integral_factorTwoP67ResidualSmoothMixedIntegrand_eq_of_cancellations
      (centeredPolynomialLift pE) (centeredPolynomialLift pO) e o
      hPE hPO he ho heGap hoGap (by norm_num) (by norm_num)
      hlinearE hlinearO a b
  have hBase := factorTwoEndpointLowTailMixed_centeredPolynomialLift_eq
    pE pO e o he ho heLocal hoLocal heGap hoGap
      hpEdeg hpOdeg a b
  have hAnalytic :=
    factorTwoP67ResidualAnalyticMixed_eq_intrinsicElevenPairing
      pE pO e o he ho a b
  have hForward :=
    factorTwoP67ResidualForwardHankelMixed_eq_intrinsicElevenPairing
      pE pO e o he ho heGap hoGap hpEdeg hpOdeg a b
  have hClean := factorTwoIntrinsicNineNonpolynomialMixed_zero_eq_cleanPairing
    pE pO e o he ho heLocal hoLocal heGap hoGap hpEdeg hpOdeg
  have hNonpolynomial :=
    factorTwoIntrinsicNineNonpolynomialMixed_eq_zero_add_reflected_add_prime
      (centeredPolynomialLift pE) (centeredPolynomialLift pO) e o a b
  have hReflected := factorTwoIntrinsicElevenReflectedMixed_eq_pairing
    pE pO e o he ho heGap hoGap hpEdeg hpOdeg a b
  have hPrime := factorTwoIntrinsicElevenPrimeMixed_eq_pairing
    pE pO e o he ho a b
  have hCE := intervalIntegrable_cleanSurvivor_mul pE e he
  have hCO := intervalIntegrable_cleanSurvivor_mul pO o ho
  have hAE := intervalIntegrable_analyticEvenRepresenter_mul
    pE pO e he a b
  have hAO := intervalIntegrable_analyticOddRepresenter_mul
    pE pO o ho a b
  have hFE := intervalIntegrable_forwardEvenRepresenter_mul
    pE pO e he a b
  have hFO := intervalIntegrable_forwardOddRepresenter_mul
    pE pO o ho a b
  have hRE := intervalIntegrable_reflectedEvenRepresenter_mul
    pE pO e he a b
  have hRO := intervalIntegrable_reflectedOddRepresenter_mul
    pE pO o ho a b
  have hPrE := intervalIntegrable_primeEvenRepresenter_mul
    pE pO e he a b
  have hPrO := intervalIntegrable_primeOddRepresenter_mul
    pE pO o ho a b
  have hECA := hCE.add hAE
  have hECAF := hECA.add hFE
  have hECAFR := hECAF.add hRE
  have hOCA := hCO.add hAO
  have hOCAF := hOCA.add hFO
  have hOCAFR := hOCAF.add hRO
  have hComplete :
      factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b)
          (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b)
          e o =
        factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenCleanSurvivorRepresenter pE)
            (factorTwoIntrinsicElevenCleanSurvivorRepresenter pO) e o +
          factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b)
            (factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b) e o +
          factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b)
            (factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b) e o +
          factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b)
            (factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b) e o +
          factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b)
            (factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b) e o := by
    unfold factorTwoIntrinsicElevenMixedPairing
      factorTwoIntrinsicElevenEvenMixedRepresenter
      factorTwoIntrinsicElevenOddMixedRepresenter
    rw [show (fun x : ℝ ↦
        (factorTwoIntrinsicElevenCleanSurvivorRepresenter pE x +
            factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b x +
            factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b x +
            factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b x +
            factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b x) * e x) =
      fun x ↦
        (((factorTwoIntrinsicElevenCleanSurvivorRepresenter pE x * e x +
            factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b x * e x) +
          factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b x * e x) +
          factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b x * e x) +
          factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b x * e x by
      funext x
      ring,
      intervalIntegral.integral_add hECAFR hPrE,
      intervalIntegral.integral_add hECAF hRE,
      intervalIntegral.integral_add hECA hFE,
      intervalIntegral.integral_add hCE hAE,
      show (fun x : ℝ ↦
        (factorTwoIntrinsicElevenCleanSurvivorRepresenter pO x +
            factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b x +
            factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b x +
            factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b x +
            factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b x) * o x) =
      fun x ↦
        (((factorTwoIntrinsicElevenCleanSurvivorRepresenter pO x * o x +
            factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b x * o x) +
          factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b x * o x) +
          factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b x * o x) +
          factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b x * o x by
      funext x
      ring,
      intervalIntegral.integral_add hOCAFR hPrO,
      intervalIntegral.integral_add hOCAF hRO,
      intervalIntegral.integral_add hOCA hFO,
      intervalIntegral.integral_add hCO hAO]
    ring
  calc
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) e
        (centeredPolynomialLift pO) o a b =
      (1 / 2 : ℝ) * (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSmoothMixedIntegrand
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          e o a b t) +
        factorTwoIntrinsicNineNonpolynomialMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          e o a b := hBase
    _ = factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b)
            (factorTwoIntrinsicElevenAnalyticOddRepresenter pE pO a b) e o +
          factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b)
            (factorTwoIntrinsicElevenForwardOddRepresenter pE pO a b) e o +
          factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenCleanSurvivorRepresenter pE)
            (factorTwoIntrinsicElevenCleanSurvivorRepresenter pO) e o +
          factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b)
            (factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b) e o +
          factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b)
            (factorTwoIntrinsicElevenPrimeOddRepresenter pE pO a b) e o := by
      rw [hSmooth, hNonpolynomial, hAnalytic, hForward, hClean,
        hReflected, hPrime]
      ring
    _ = factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b)
          (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b)
          e o := by
      rw [hComplete]
      ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
