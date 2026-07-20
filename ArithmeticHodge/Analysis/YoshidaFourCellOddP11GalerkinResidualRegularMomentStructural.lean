import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreEntryBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelWideEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRegularMomentStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11CoreEntryBoundsStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellRegularKernelWideEnvelope

/-!
# The regular `q0`--`P11` moment

The sixth-order regular-kernel polynomial is exceptionally sparse against
the first five odd Legendre modes and `P11`.  In particular the entire `P3`
moment vanishes.  This module records that cancellation before estimating
the small uniform kernel remainder.
-/

/-- Exact symmetric correlation polynomial between a five-mode odd profile
and the genuine `P11` direction. -/
def fourCellOddFiveModeP11CorrelationPolynomial
    (c d e f g t : ℝ) : ℝ :=
  (-c - d - e - f - g) * t ^ 1 +
    ((65 / 2 : ℝ) * c + 30 * d + (51 / 2 : ℝ) * e +
      19 * f + (21 / 2 : ℝ) * g) * t ^ 2 +
    ((-693 / 2 : ℝ) * c - 294 * d - 210 * e -
      (225 / 2 : ℝ) * f - (55 / 2 : ℝ) * g) * t ^ 3 +
    ((3575 / 2 : ℝ) * c + (5525 / 4 : ℝ) * d +
      (1615 / 2 : ℝ) * e + (2261 / 8 : ℝ) * f) * t ^ 4 +
    ((-21021 / 4 : ℝ) * c - (14553 / 4 : ℝ) * d -
      (6615 / 4 : ℝ) * e - (1155 / 4 : ℝ) * f +
      (495 / 8 : ℝ) * g) * t ^ 5 +
    ((153153 / 16 : ℝ) * c + (46189 / 8 : ℝ) * d +
      (29393 / 16 : ℝ) * e) * t ^ 6 +
    ((-45045 / 4 : ℝ) * c - (45045 / 8 : ℝ) * d -
      (7623 / 8 : ℝ) * e + (693 / 4 : ℝ) * f -
      (429 / 4 : ℝ) * g) * t ^ 7 +
    ((138567 / 16 : ℝ) * c + (415701 / 128 : ℝ) * d) * t ^ 8 +
    ((-546975 / 128 : ℝ) * c - (117975 / 128 : ℝ) * d +
      (23595 / 128 : ℝ) * e - (14157 / 128 : ℝ) * f +
      (15015 / 128 : ℝ) * g) * t ^ 9 +
    ((323323 / 256 : ℝ) * c) * t ^ 10 +
    ((-46189 / 256 : ℝ) * c + (7293 / 128 : ℝ) * d -
      (5577 / 128 : ℝ) * e + (13013 / 256 : ℝ) * f -
      (21021 / 256 : ℝ) * g) * t ^ 11 +
    ((2261 / 1024 : ℝ) * c - (4199 / 1024 : ℝ) * d +
      (7735 / 1024 : ℝ) * e - (15925 / 1024 : ℝ) * f +
      (9555 / 256 : ℝ) * g) * t ^ 13 +
    ((323 / 2048 : ℝ) * d -
      (1615 / 2048 : ℝ) * e + (765 / 256 : ℝ) * f -
      (2805 / 256 : ℝ) * g) * t ^ 15 +
    ((1197 / 32768 : ℝ) * e -
      (10659 / 32768 : ℝ) * f + (65637 / 32768 : ℝ) * g) * t ^ 17 +
    ((1001 / 65536 : ℝ) * f -
      (13585 / 65536 : ℝ) * g) * t ^ 19 +
    ((2431 / 262144 : ℝ) * g) * t ^ 21

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
theorem factorTwoCenteredCorrelationBilinear_fiveMode_P11_eq
    (c d e f g t : ℝ) :
    factorTwoCenteredCorrelationBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
        fourCellOddP11DirectTail t =
      fourCellOddFiveModeP11CorrelationPolynomial c d e f g t := by
  have hlowOdd : Function.Odd
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) :=
    odd_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g
  have hswap := factorTwoCenteredCrossCorrelation_swap_of_odd_odd
    hlowOdd odd_fourCellOddP11DirectTail t
  unfold factorTwoCenteredCorrelationBilinear
  rw [hswap]
  rw [show
      (factorTwoCenteredCrossCorrelation
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
          fourCellOddP11DirectTail t +
        factorTwoCenteredCrossCorrelation
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
          fourCellOddP11DirectTail t) / 2 =
        factorTwoCenteredCrossCorrelation
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
          fourCellOddP11DirectTail t by ring]
  unfold factorTwoCenteredCrossCorrelation
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
    fourCellOddP11DirectTail fourCellOddFiveModeP11CorrelationPolynomial
  simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  have hlinear :
      (∫ x : ℝ in -1..1 - t, x) =
        (((1 - t) ^ 2 - (-1 : ℝ) ^ 2) / 2) := by
    have h := YoshidaEndpointOcticPotential.integral_pow_nat
      1 (-1 : ℝ) (1 - t)
    norm_num at h ⊢
  rw [hlinear]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRegularMomentStructural
