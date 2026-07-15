import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural

noncomputable section

open Polynomial
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLowSchur

private theorem p4PivotCoefficientPolynomial_expansion :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial =
      C (symmetricDeterminant
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)) +
      C (mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))) * X +
      C (mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)) * X ^ 2 +
      C (symmetricDeterminant
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))) * X ^ 3 := by
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial mixedDeterminantOne symmetricDeterminant
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

private theorem pivotCoeff_one_eq_mixedDeterminantOne :
    pivotCoeff 1 = mixedDeterminantOne
      (factorTwoStructuralPhaseLow00 1)
      (factorTwoStructuralPhaseLow02 1)
      (factorTwoIntrinsicFourP45Cross04 1)
      (factorTwoStructuralPhaseLow22 1)
      (factorTwoIntrinsicFourP45Cross24 1)
      (factorTwoIntrinsicSixP4Diagonal 1)
      (factorTwoStructuralPhaseLow00 (-1))
      (factorTwoStructuralPhaseLow02 (-1))
      (factorTwoIntrinsicFourP45Cross04 (-1))
      (factorTwoStructuralPhaseLow22 (-1))
      (factorTwoIntrinsicFourP45Cross24 (-1))
      (factorTwoIntrinsicSixP4Diagonal (-1)) := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 1 = _
  rw [p4PivotCoefficientPolynomial_expansion]
  simp

private theorem pivotCoeff_two_eq_mixedDeterminantOne :
    pivotCoeff 2 = mixedDeterminantOne
      (factorTwoStructuralPhaseLow00 (-1))
      (factorTwoStructuralPhaseLow02 (-1))
      (factorTwoIntrinsicFourP45Cross04 (-1))
      (factorTwoStructuralPhaseLow22 (-1))
      (factorTwoIntrinsicFourP45Cross24 (-1))
      (factorTwoIntrinsicSixP4Diagonal (-1))
      (factorTwoStructuralPhaseLow00 1)
      (factorTwoStructuralPhaseLow02 1)
      (factorTwoIntrinsicFourP45Cross04 1)
      (factorTwoStructuralPhaseLow22 1)
      (factorTwoIntrinsicFourP45Cross24 1)
      (factorTwoIntrinsicSixP4Diagonal 1) := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 2 = _
  rw [p4PivotCoefficientPolynomial_expansion]
  simp

private theorem plus_endpoint_p024_gates :
    0 < factorTwoStructuralPhaseLow00 1 ∧
      0 < leadingMinorTwo
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoStructuralPhaseLow22 1) ∧
      0 < symmetricDeterminant
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1) := by
  refine ⟨factorTwoIntrinsicEven_plus_endpoint_structural_gates.1, ?_, ?_⟩
  · simpa [leadingMinorTwo, factorTwoIntrinsicEvenPhaseDet] using
      factorTwoIntrinsicEven_plus_endpoint_structural_gates.2
  · change 0 < factorTwoIntrinsicP024Determinant 1
    rw [← factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
    exact factorTwoIntrinsicSixP4SchurLeading_plus_pos

private theorem minus_endpoint_p024_gates :
    0 < factorTwoStructuralPhaseLow00 (-1) ∧
      0 < leadingMinorTwo
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoStructuralPhaseLow22 (-1)) ∧
      0 < symmetricDeterminant
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1)) := by
  refine ⟨factorTwoIntrinsicEven_minus_endpoint_kernel_gates.1, ?_, ?_⟩
  · simpa [leadingMinorTwo, factorTwoIntrinsicEvenPhaseDet] using
      factorTwoIntrinsicEven_minus_endpoint_kernel_gates.2
  · change 0 < factorTwoIntrinsicP024Determinant (-1)
    rw [← factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
    exact factorTwoIntrinsicSixP4SchurLeading_minus_pos

/-- The coefficient linear in the negative endpoint of the projective
`P0/P2/P4` determinant is strictly positive. -/
theorem pivotCoeff_one_pos : 0 < pivotCoeff 1 := by
  rw [pivotCoeff_one_eq_mixedDeterminantOne]
  exact mixedDeterminantOne_pos
    _ _ _ _ _ _ _ _ _ _ _ _
    plus_endpoint_p024_gates.1
    plus_endpoint_p024_gates.2.1
    plus_endpoint_p024_gates.2.2
    minus_endpoint_p024_gates.1
    minus_endpoint_p024_gates.2.1
    minus_endpoint_p024_gates.2.2

/-- The coefficient quadratic in the negative endpoint is the reverse mixed
determinant and is strictly positive as well. -/
theorem pivotCoeff_two_pos : 0 < pivotCoeff 2 := by
  rw [pivotCoeff_two_eq_mixedDeterminantOne]
  exact mixedDeterminantOne_pos
    _ _ _ _ _ _ _ _ _ _ _ _
    minus_endpoint_p024_gates.1
    minus_endpoint_p024_gates.2.1
    minus_endpoint_p024_gates.2.2
    plus_endpoint_p024_gates.1
    plus_endpoint_p024_gates.2.1
    plus_endpoint_p024_gates.2.2

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural
