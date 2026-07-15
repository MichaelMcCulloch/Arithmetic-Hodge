import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations

noncomputable section

open MeasureTheory Real Set
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseLegendreFourFiveStructural

/-!
# Exact alternating correlation models involving `P5`

The three new alternating entries in the six-mode border share the same
endpoint factor `t * (2 - t)`.  This file identifies their remaining scalar
polynomials and transfers each coupling to the common regular-error,
archimedean-model, and retained-prime decomposition.  No enclosure or phase
sampling occurs here.
-/

def alternatingQ05 (t : ℝ) : ℝ :=
  1 - 7 * t + 14 * t ^ 2 - (21 / 2 : ℝ) * t ^ 3 +
    (21 / 8 : ℝ) * t ^ 4

def alternatingQ25 (t : ℝ) : ℝ :=
  1 - (11 / 2 : ℝ) * t + (31 / 4 : ℝ) * t ^ 2 -
    (19 / 8 : ℝ) * t ^ 3 - (19 / 16 : ℝ) * t ^ 4 +
    (9 / 32 : ℝ) * t ^ 5 + (9 / 64 : ℝ) * t ^ 6

def alternatingQ45 (t : ℝ) : ℝ :=
  1 - 2 * t - t ^ 2 + 2 * t ^ 3 + t ^ 4 -
    (13 / 16 : ℝ) * t ^ 5 - (13 / 32 : ℝ) * t ^ 6 +
    (7 / 64 : ℝ) * t ^ 7 + (7 / 128 : ℝ) * t ^ 8

/-- Exact ordered-correlation difference for the `P0/P5` entry. -/
theorem crossDifference_p0_p5
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation factorTwoCenteredP5 centeredEvenP0 t -
        factorTwoCenteredCrossCorrelation centeredEvenP0 factorTwoCenteredP5 t =
      intrinsicAlternatingCorrelation alternatingQ05 t := by
  unfold factorTwoCenteredCrossCorrelation factorTwoCenteredP5 centeredEvenP0
    intrinsicAlternatingCorrelation alternatingQ05
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  simp only [smul_eq_mul]
  ring

/-- Exact ordered-correlation difference for the `P2/P5` entry. -/
theorem crossDifference_p2_p5
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation factorTwoCenteredP5 centeredEvenP2 t -
        factorTwoCenteredCrossCorrelation centeredEvenP2 factorTwoCenteredP5 t =
      intrinsicAlternatingCorrelation alternatingQ25 t := by
  unfold factorTwoCenteredCrossCorrelation factorTwoCenteredP5 centeredEvenP2
    intrinsicAlternatingCorrelation alternatingQ25
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  simp only [smul_eq_mul]
  ring

/-- Exact ordered-correlation difference for the `P4/P5` entry. -/
theorem crossDifference_p4_p5
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation factorTwoCenteredP5 factorTwoCenteredP4 t -
        factorTwoCenteredCrossCorrelation factorTwoCenteredP4 factorTwoCenteredP5 t =
      intrinsicAlternatingCorrelation alternatingQ45 t := by
  unfold factorTwoCenteredCrossCorrelation factorTwoCenteredP5
    factorTwoCenteredP4 intrinsicAlternatingCorrelation alternatingQ45
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  simp only [smul_eq_mul]
  ring

/-- Structural kernel decomposition of the `P0/P5` alternating entry. -/
theorem factorTwoIntrinsicFourP45Cross05_eq_structuralModel :
    factorTwoIntrinsicFourP45Cross05 =
      intrinsicAlternatingRegularError alternatingQ05 +
        intrinsicAlternatingArchModel alternatingQ05 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ05
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoIntrinsicFourP45Cross05
  exact factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
    centeredEvenP0 factorTwoCenteredP5 alternatingQ05
    (by unfold alternatingQ05; fun_prop) crossDifference_p0_p5

/-- Structural kernel decomposition of the `P2/P5` alternating entry. -/
theorem factorTwoIntrinsicFourP45Cross25_eq_structuralModel :
    factorTwoIntrinsicFourP45Cross25 =
      intrinsicAlternatingRegularError alternatingQ25 +
        intrinsicAlternatingArchModel alternatingQ25 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ25
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoIntrinsicFourP45Cross25
  exact factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
    centeredEvenP2 factorTwoCenteredP5 alternatingQ25
    (by unfold alternatingQ25; fun_prop) crossDifference_p2_p5

/-- Structural kernel decomposition of the `P4/P5` alternating entry. -/
theorem factorTwoIntrinsicSixAlternating45_eq_structuralModel :
    factorTwoIntrinsicSixAlternating45 =
      intrinsicAlternatingRegularError alternatingQ45 +
        intrinsicAlternatingArchModel alternatingQ45 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ45
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoIntrinsicSixAlternating45
  exact factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
    factorTwoCenteredP4 factorTwoCenteredP5 alternatingQ45
    (by unfold alternatingQ45; fun_prop) crossDifference_p4_p5

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations
