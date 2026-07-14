import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOperatorContraction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSquareAssembly

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRemainderClosure

noncomputable section

open UnitIntervalLogEnergyAffine
open CenteredEndpointCorrelation
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseSquareAssembly
open YoshidaRegularKernelSchur

/-!
# The exact zero-phase remainder left by the radius-two square

The radius-two singular-square lower bound is not tight even at phase zero.
After half of the clean form, one eighth of the raw energy, and half of the
signed remainder are assembled, exactly half of the endpoint potential and
`log 2 / 2` times the mass have been discarded.  This identity is an
obstruction to closing the structural residual merely by declaring that
intermediate lower bound nonnegative; the discarded terms must be recovered
from the singular square or compensated by a sharper whole-form argument.
-/

/-- At phase zero the signed remainder contains only the scalar, regular,
and hyperbolic diagonal terms. -/
theorem factorTwoPhaseSignedRemainder_zero_phase
    (w : ℝ → ℝ) :
    factorTwoPhaseSignedRemainder (0 : ℝ → ℝ) w 0 0 =
      -(yoshidaEndpointScalarMassLoss + Real.log 2) *
          (∫ x : ℝ in -1..1, w x ^ 2) -
        yoshidaEndpointA *
          (yoshidaEndpointRegularQuadratic
            (fun x : ℝ ↦ (w x : ℂ))).re +
        yoshidaEndpointHyperbolicQuadratic
          (fun x : ℝ ↦ (w x : ℂ)) := by
  unfold factorTwoPhaseSignedRemainder
    factorTwoCenteredForwardPhaseKernel
    factorTwoCenteredReflectedDesingularizedPhaseKernel
    factorTwoCenteredPhaseCorrelation
    centeredEndpointCorrelation
    factorTwoCenteredCrossCorrelation
    yoshidaEndpointRegularQuadratic
    yoshidaEndpointHyperbolicQuadratic
  simp

/-- Exact loss in the zero-phase specialization of
`half_clean_add_eighth_raw_add_half_radiusTwo_remainder_le`. -/
theorem half_clean_add_eighth_raw_add_half_remainder_zero_phase_eq
    (w : ℝ → ℝ) :
    (1 / 2 : ℝ) * yoshidaEndpointOddCleanQuadratic w +
        centeredRawLogEnergy w / 8 +
        (1 / 2 : ℝ) *
          factorTwoPhaseSignedRemainder (0 : ℝ → ℝ) w 0 0 =
      yoshidaEndpointOddCleanQuadratic w -
        (1 / 2 : ℝ) *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointPotential x * w x ^ 2) -
        (Real.log 2 / 2) *
          (∫ x : ℝ in -1..1, w x ^ 2) := by
  rw [factorTwoPhaseSignedRemainder_zero_phase]
  unfold yoshidaEndpointOddCleanQuadratic
  ring

/-- Consequently the radius-two lower expression is strictly below the
clean form for every profile of positive endpoint mass. -/
theorem half_clean_add_eighth_raw_add_half_remainder_zero_phase_lt_clean
    (w : ℝ → ℝ)
    (hmass : 0 < ∫ x : ℝ in -1..1, w x ^ 2) :
    (1 / 2 : ℝ) * yoshidaEndpointOddCleanQuadratic w +
        centeredRawLogEnergy w / 8 +
        (1 / 2 : ℝ) *
          factorTwoPhaseSignedRemainder (0 : ℝ → ℝ) w 0 0 <
      yoshidaEndpointOddCleanQuadratic w := by
  rw [half_clean_add_eighth_raw_add_half_remainder_zero_phase_eq]
  have hpotential :
      0 ≤ ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact mul_nonneg
      (yoshidaEndpointPotential_nonneg_on_Icc
        (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx))
      (sq_nonneg _)
  have hlog : 0 < Real.log 2 / 2 := by positivity
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRemainderClosure
