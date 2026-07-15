import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixEndpointPositiveStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOuterConeStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientFrontierStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixEndpointPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOddPencilStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

/-!
# Outer-coefficient closure for the raw six-mode cone

Positive definiteness of the two odd endpoint matrices makes all four
coefficients of the intervening odd determinant pencil strictly positive.
Together with positivity of the two endpoint even pivots, this closes the
constant and leading coefficients of the complete raw sextic and leaves only
the five genuinely mixed coefficients.
-/

/-- All coefficients of the raw odd determinant pencil are strictly positive. -/
theorem rawSixOddDetCoefficients_pos :
    0 < rawSixOddDetCoeff 0 ∧
      0 < rawSixOddDetCoeff 1 ∧
      0 < rawSixOddDetCoeff 2 ∧
      0 < rawSixOddDetCoeff 3 :=
  rawSixOddDetCoefficients_pos_of_endpoint_posDef
    rawSixOddPlusMatrix_posDef rawSixOddMinusMatrix_posDef

private theorem coefficientOdd11_zero_pos :
    0 < coefficientOdd11Polynomial.coeff 0 := by
  have h := oddStructuralLow_endpoint_gates.1
  simpa [coefficientOdd11Polynomial, endpointAffinePolynomial,
    factorTwoIntrinsicOddPhaseLow11,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11] using h

private theorem coefficientOdd11_one_pos :
    0 < coefficientOdd11Polynomial.coeff 1 := by
  have h := oddStructuralLow_endpoint_gates.2.2.1
  simpa [coefficientOdd11Polynomial, endpointAffinePolynomial,
    factorTwoIntrinsicOddPhaseLow11,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11] using h

private theorem pivotCoeff_zero_pos : 0 < pivotCoeff 0 := by
  have hprod :=
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_zero_pos
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient] at hprod
  by_contra h
  have hp : pivotCoeff 0 ≤ 0 := le_of_not_gt h
  have hnonpos :=
    mul_nonpos_of_nonpos_of_nonneg hp coefficientOdd11_zero_pos.le
  linarith

private theorem pivotCoeff_three_pos : 0 < pivotCoeff 3 := by
  have hprod :=
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_four_pos
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient] at hprod
  by_contra h
  have hp : pivotCoeff 3 ≤ 0 := le_of_not_gt h
  have hnonpos :=
    mul_nonpos_of_nonpos_of_nonneg hp coefficientOdd11_one_pos.le
  linarith

/-- The plus-endpoint coefficient of the complete raw sextic is positive. -/
theorem factorTwoIntrinsicSixProjectiveRawSixCoefficient_zero_pos :
    0 < factorTwoIntrinsicSixProjectiveRawSixCoefficient 0 := by
  simp only [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  exact mul_pos pivotCoeff_zero_pos rawSixOddDetCoefficients_pos.1

/-- The minus-endpoint coefficient of the complete raw sextic is positive. -/
theorem factorTwoIntrinsicSixProjectiveRawSixCoefficient_six_pos :
    0 < factorTwoIntrinsicSixProjectiveRawSixCoefficient 6 := by
  simp only [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  exact mul_pos pivotCoeff_three_pos rawSixOddDetCoefficients_pos.2.2.2

/-- Exact five-gate frontier remaining after the two endpoint coefficients
have been closed structurally. -/
theorem factorTwoIntrinsicSixProjectiveRawDeterminant_mem_cone_iff_middle :
    StrictNonnegativeCoefficientCone
        factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial ↔
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 1 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 2 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 3 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 4 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 5 := by
  rw [factorTwoIntrinsicSixProjectiveRawDeterminant_mem_cone_iff_coefficients]
  constructor
  · rintro ⟨_, h1, h2, h3, h4, h5, _⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨factorTwoIntrinsicSixProjectiveRawSixCoefficient_zero_pos,
      h1, h2, h3, h4, h5,
      factorTwoIntrinsicSixProjectiveRawSixCoefficient_six_pos.le⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOuterConeStructural
