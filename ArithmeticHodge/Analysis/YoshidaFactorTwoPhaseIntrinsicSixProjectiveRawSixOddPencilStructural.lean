import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDiscriminant
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientFrontierStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOddPencilStructural

noncomputable section

open Matrix
open Polynomial
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreePositiveMixedDiscriminant
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientFrontierStructural

/-!
# The raw six-mode odd determinant as a positive matrix pencil

The odd `P1/P3/P5` cubic is the determinant of the affine pencil joining
its two phase-endpoint matrices.  Consequently its two mixed coefficients
are positive by the invariant mixed-determinant theorem whenever those
endpoint matrices are positive definite.  No coefficient evaluation or
sampling of the projective half-line is involved.
-/

def rawSixOddEndpointMatrix (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoIntrinsicOddPhaseLow11 a)
    (factorTwoIntrinsicOddPhaseLow13 a)
    (factorTwoIntrinsicFourP45Cross15 a)
    (factorTwoIntrinsicOddPhaseLow33 a)
    (factorTwoIntrinsicFourP45Cross35 a)
    (factorTwoIntrinsicSixP5Diagonal a)

def rawSixOddPlusMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  rawSixOddEndpointMatrix 1

def rawSixOddMinusMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  rawSixOddEndpointMatrix (-1)

private def rawSixOddCoefficientMatrix : Matrix (Fin 3) (Fin 3) ℝ[X] :=
  !![coefficientOdd11Polynomial, coefficientOdd13Polynomial,
        coefficientOdd15Polynomial;
      coefficientOdd13Polynomial, coefficientOdd33Polynomial,
        coefficientOdd35Polynomial;
      coefficientOdd15Polynomial, coefficientOdd35Polynomial,
        coefficientP5DiagonalPolynomial]

private theorem rawSixOddDeterminantPolynomial_eq_matrix_det :
    factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial =
      rawSixOddCoefficientMatrix.det := by
  unfold factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial
    rawSixOddCoefficientMatrix
  rw [Matrix.det_fin_three]
  simp
  ring

private theorem rawSixOddCoefficientMatrix_eq_affine_pencil :
    rawSixOddCoefficientMatrix =
      rawSixOddPlusMatrix.map (Polynomial.C : ℝ →+* ℝ[X]) +
        (X : ℝ[X]) •
          rawSixOddMinusMatrix.map (Polynomial.C : ℝ →+* ℝ[X]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawSixOddCoefficientMatrix, rawSixOddPlusMatrix,
      rawSixOddMinusMatrix, rawSixOddEndpointMatrix, symmetricMatrix3,
      coefficientOdd11Polynomial, coefficientOdd13Polynomial,
      coefficientOdd15Polynomial, coefficientOdd33Polynomial,
      coefficientOdd35Polynomial, coefficientP5DiagonalPolynomial,
      YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural.endpointAffinePolynomial]

/-- Exact invariant realization of the raw odd cubic as a determinant
pencil between its two phase endpoints. -/
theorem rawSixOddDeterminantPolynomial_eq_determinantPencil :
    factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial =
      determinantPencil rawSixOddPlusMatrix rawSixOddMinusMatrix := by
  rw [rawSixOddDeterminantPolynomial_eq_matrix_det,
    rawSixOddCoefficientMatrix_eq_affine_pencil]
  rfl

theorem rawSixOddDetCoeff_zero_eq :
    rawSixOddDetCoeff 0 = rawSixOddPlusMatrix.det := by
  change
    factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial.coeff 0 = _
  rw [rawSixOddDeterminantPolynomial_eq_determinantPencil,
    determinantPencil_eq_coefficients]
  simp

theorem rawSixOddDetCoeff_one_eq :
    rawSixOddDetCoeff 1 =
      matrixMixedDeterminantOne rawSixOddPlusMatrix rawSixOddMinusMatrix := by
  change
    factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial.coeff 1 = _
  rw [rawSixOddDeterminantPolynomial_eq_determinantPencil,
    determinantPencil_eq_coefficients]
  simp

theorem rawSixOddDetCoeff_two_eq :
    rawSixOddDetCoeff 2 =
      matrixMixedDeterminantOne rawSixOddMinusMatrix rawSixOddPlusMatrix := by
  change
    factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial.coeff 2 = _
  rw [rawSixOddDeterminantPolynomial_eq_determinantPencil,
    determinantPencil_eq_coefficients]
  simp

theorem rawSixOddDetCoeff_three_eq :
    rawSixOddDetCoeff 3 = rawSixOddMinusMatrix.det := by
  change
    factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial.coeff 3 = _
  rw [rawSixOddDeterminantPolynomial_eq_determinantPencil,
    determinantPencil_eq_coefficients]
  simp

/-- Positive definiteness at the two phase endpoints makes every
coefficient of the intervening odd determinant pencil strictly positive.
The middle signs follow invariantly from mixed-determinant positivity. -/
theorem rawSixOddDetCoefficients_pos_of_endpoint_posDef
    (hplus : rawSixOddPlusMatrix.PosDef)
    (hminus : rawSixOddMinusMatrix.PosDef) :
    0 < rawSixOddDetCoeff 0 ∧
      0 < rawSixOddDetCoeff 1 ∧
      0 < rawSixOddDetCoeff 2 ∧
      0 < rawSixOddDetCoeff 3 := by
  rw [rawSixOddDetCoeff_zero_eq, rawSixOddDetCoeff_one_eq,
    rawSixOddDetCoeff_two_eq, rawSixOddDetCoeff_three_eq]
  exact ⟨hplus.det_pos,
    matrixMixedDeterminantOne_pos hplus hminus,
    matrixMixedDeterminantOne_pos hminus hplus,
    hminus.det_pos⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOddPencilStructural
