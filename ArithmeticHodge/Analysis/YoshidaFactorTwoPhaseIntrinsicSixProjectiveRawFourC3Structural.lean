import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC3Structural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural positivity of the third raw four-mode coefficient

The coefficient adjacent to the negative endpoint is treated through its
exact mixed-endpoint scalar formula.  The three-dimensional mixed determinant
is positive by the endpoint Sylvester gates.  Consequently the only remaining
analytic input is the displayed fixed `P4/P1` boundary Schur inequality.  No
sampling of the projective half-line is used.
-/

/-- The linear coefficient of the negative odd endpoint is its strictly
positive endpoint diagonal. -/
theorem coefficientOdd11Polynomial_coeff_one_pos :
    0 < coefficientOdd11Polynomial.coeff 1 := by
  have h := oddStructuralLow_endpoint_gates.2.2.1
  rw [show coefficientOdd11Polynomial.coeff 1 =
      factorTwoIntrinsicOddPhaseLow11 (-1) by
    simp [coefficientOdd11Polynomial, endpointAffinePolynomial]]
  simpa [factorTwoIntrinsicOddPhaseLow11,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11] using h

/-- The exact fixed boundary determinant left after removing the positive
mixed-determinant summand from `c3`. -/
def factorTwoIntrinsicSixProjectiveRawFourC3Boundary : ℝ :=
  pivotCoeff 3 * coefficientOdd11Polynomial.coeff 0 -
    p1AlternatingAdjugateCoeff 2

/-- Structural reduction of `c3`: the endpoint boundary Schur inequality is
the only additional input beyond the already-proved positive mixed
determinant. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_three_nonneg_of_boundary
    (hBoundary : 0 ≤ factorTwoIntrinsicSixProjectiveRawFourC3Boundary) :
    0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 3 := by
  have hMixed : 0 ≤
      pivotCoeff 2 * coefficientOdd11Polynomial.coeff 1 :=
    mul_nonneg pivotCoeff_two_pos.le
      coefficientOdd11Polynomial_coeff_one_pos.le
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  unfold factorTwoIntrinsicSixProjectiveRawFourC3Boundary at hBoundary
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC3Structural
