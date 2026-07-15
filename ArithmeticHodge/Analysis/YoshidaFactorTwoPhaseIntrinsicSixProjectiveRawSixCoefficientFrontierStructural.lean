import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientsStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientFrontierStructural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

/-!
# Exact coefficient frontier for the raw six-mode determinant

The complete raw determinant is a product of two cubics, corrected by a
shifted quartic, a twice-shifted quadratic, and the cubic alternating square.
This file records that degree structure and exposes the resulting seven
convolution coefficients.  All reductions are polynomial identities; no
pointwise sampling of the projective half-line occurs.
-/

abbrev rawSixOddDetCoeff (n : ℕ) : ℝ :=
  factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial.coeff n

abbrev rawSixMixedOneCoeff (n : ℕ) : ℝ :=
  factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial.coeff n

abbrev rawSixMixedTwoCoeff (n : ℕ) : ℝ :=
  factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial.coeff n

/-- The seven exact convolution coefficients of the raw sextic. -/
def factorTwoIntrinsicSixProjectiveRawSixCoefficient : ℕ → ℝ
  | 0 => pivotCoeff 0 * rawSixOddDetCoeff 0
  | 1 => pivotCoeff 0 * rawSixOddDetCoeff 1 +
      pivotCoeff 1 * rawSixOddDetCoeff 0 - rawSixMixedOneCoeff 0
  | 2 => pivotCoeff 0 * rawSixOddDetCoeff 2 +
      pivotCoeff 1 * rawSixOddDetCoeff 1 +
      pivotCoeff 2 * rawSixOddDetCoeff 0 - rawSixMixedOneCoeff 1 +
      rawSixMixedTwoCoeff 0
  | 3 => pivotCoeff 0 * rawSixOddDetCoeff 3 +
      pivotCoeff 1 * rawSixOddDetCoeff 2 +
      pivotCoeff 2 * rawSixOddDetCoeff 1 +
      pivotCoeff 3 * rawSixOddDetCoeff 0 - rawSixMixedOneCoeff 2 +
      rawSixMixedTwoCoeff 1 -
      factorTwoIntrinsicSixProjectiveRawSixAlternatingDeterminant ^ 2
  | 4 => pivotCoeff 1 * rawSixOddDetCoeff 3 +
      pivotCoeff 2 * rawSixOddDetCoeff 2 +
      pivotCoeff 3 * rawSixOddDetCoeff 1 - rawSixMixedOneCoeff 3 +
      rawSixMixedTwoCoeff 2
  | 5 => pivotCoeff 2 * rawSixOddDetCoeff 3 +
      pivotCoeff 3 * rawSixOddDetCoeff 2 - rawSixMixedOneCoeff 4
  | 6 => pivotCoeff 3 * rawSixOddDetCoeff 3
  | _ => 0

private theorem natDegree_pivot_le :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.natDegree ≤ 3 := by
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial
  compute_degree

private theorem natDegree_oddDet_le :
    factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial.natDegree ≤ 3 := by
  unfold factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial
    coefficientOdd11Polynomial coefficientOdd13Polynomial
    coefficientOdd15Polynomial coefficientOdd33Polynomial
    coefficientOdd35Polynomial coefficientP5DiagonalPolynomial
    endpointAffinePolynomial
  compute_degree

private theorem natDegree_mixedOne_le :
    factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial.natDegree ≤ 4 := by
  unfold factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial
    coefficientRawSixAdjugatePairPolynomial coefficientRawAdjugatePairPolynomial
    coefficientLowDetPolynomial coefficientLow00Polynomial
    coefficientLow02Polynomial coefficientLow22Polynomial
    coefficientCross04Polynomial coefficientCross24Polynomial
    coefficientP4DiagonalPolynomial coefficientOdd11Polynomial
    coefficientOdd13Polynomial coefficientOdd15Polynomial
    coefficientOdd33Polynomial coefficientOdd35Polynomial
    coefficientP5DiagonalPolynomial endpointAffinePolynomial
  compute_degree

private theorem natDegree_mixedTwo_le :
    factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial.natDegree ≤ 2 := by
  unfold factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial
    coefficientRawSixAdjugateCofactorPolynomial
    coefficientRawSixEvenEnergyPolynomial coefficientLow00Polynomial
    coefficientLow02Polynomial coefficientLow22Polynomial
    coefficientCross04Polynomial coefficientCross24Polynomial
    coefficientP4DiagonalPolynomial coefficientOdd11Polynomial
    coefficientOdd13Polynomial coefficientOdd15Polynomial
    coefficientOdd33Polynomial coefficientOdd35Polynomial
    coefficientP5DiagonalPolynomial endpointAffinePolynomial
  compute_degree

private theorem pivot_as_coefficients :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial =
      C (pivotCoeff 0) + C (pivotCoeff 1) * X +
        C (pivotCoeff 2) * X ^ 2 + C (pivotCoeff 3) * X ^ 3 := by
  rw [factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.as_sum_range_C_mul_X_pow'
    (show factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.natDegree < 4 by
      have h := natDegree_pivot_le
      omega)]
  simp [Finset.sum_range_succ]

private theorem oddDet_as_coefficients :
    factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial =
      C (rawSixOddDetCoeff 0) + C (rawSixOddDetCoeff 1) * X +
        C (rawSixOddDetCoeff 2) * X ^ 2 +
        C (rawSixOddDetCoeff 3) * X ^ 3 := by
  rw [factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial.as_sum_range_C_mul_X_pow'
    (show factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial.natDegree < 4 by
      have h := natDegree_oddDet_le
      omega)]
  simp [Finset.sum_range_succ]

private theorem mixedOne_as_coefficients :
    factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial =
      C (rawSixMixedOneCoeff 0) + C (rawSixMixedOneCoeff 1) * X +
        C (rawSixMixedOneCoeff 2) * X ^ 2 +
        C (rawSixMixedOneCoeff 3) * X ^ 3 +
        C (rawSixMixedOneCoeff 4) * X ^ 4 := by
  rw [factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial.as_sum_range_C_mul_X_pow'
    (show factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial.natDegree < 5 by
      have h := natDegree_mixedOne_le
      omega)]
  simp [Finset.sum_range_succ]

private theorem mixedTwo_as_coefficients :
    factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial =
      C (rawSixMixedTwoCoeff 0) + C (rawSixMixedTwoCoeff 1) * X +
        C (rawSixMixedTwoCoeff 2) * X ^ 2 := by
  rw [factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial.as_sum_range_C_mul_X_pow'
    (show factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial.natDegree < 3 by
      have h := natDegree_mixedTwo_le
      omega)]
  simp [Finset.sum_range_succ]

/-- Exact degree-six expansion of the complete raw determinant. -/
theorem factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial_eq_coefficients :
    factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial =
      C (factorTwoIntrinsicSixProjectiveRawSixCoefficient 0) +
        C (factorTwoIntrinsicSixProjectiveRawSixCoefficient 1) * X +
        C (factorTwoIntrinsicSixProjectiveRawSixCoefficient 2) * X ^ 2 +
        C (factorTwoIntrinsicSixProjectiveRawSixCoefficient 3) * X ^ 3 +
        C (factorTwoIntrinsicSixProjectiveRawSixCoefficient 4) * X ^ 4 +
        C (factorTwoIntrinsicSixProjectiveRawSixCoefficient 5) * X ^ 5 +
        C (factorTwoIntrinsicSixProjectiveRawSixCoefficient 6) * X ^ 6 := by
  rw [factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial_eq_components]
  unfold factorTwoIntrinsicSixProjectiveRawSixCoefficientPolynomial
  rw [pivot_as_coefficients, oddDet_as_coefficients,
    mixedOne_as_coefficients, mixedTwo_as_coefficients]
  simp only [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  simp only [map_add, map_sub, map_mul, map_pow]
  ring

/-- Every coefficient of the complete raw determinant is one of the seven
displayed scalars, and all higher coefficients vanish. -/
theorem coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial
    (n : ℕ) :
    factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial.coeff n =
      factorTwoIntrinsicSixProjectiveRawSixCoefficient n := by
  rw [factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial_eq_coefficients]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]

/-- Structural degree support: the complete raw determinant has no term of
degree at least seven. -/
theorem coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial_eq_zero
    (n : ℕ) (hn : 7 ≤ n) :
    factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial.coeff n = 0 := by
  rw [coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]

/-- Exact finite frontier for the strict coefficient cone of the raw
sextic.  The first gate is strict because it is the constant term; the six
remaining displayed coefficients are closed sign gates. -/
theorem factorTwoIntrinsicSixProjectiveRawDeterminant_mem_cone_iff_coefficients :
    StrictNonnegativeCoefficientCone
        factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial ↔
      0 < factorTwoIntrinsicSixProjectiveRawSixCoefficient 0 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 1 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 2 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 3 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 4 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 5 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 6 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
      exact h.1
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
      exact h.2 1
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
      exact h.2 2
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
      exact h.2 3
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
      exact h.2 4
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
      exact h.2 5
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
      exact h.2 6
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    constructor
    · rw [coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
      exact h0
    · intro n
      rw [coeff_factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial]
      rcases n with _ | n
      · exact h0.le
      rcases n with _ | n
      · exact h1
      rcases n with _ | n
      · exact h2
      rcases n with _ | n
      · exact h3
      rcases n with _ | n
      · exact h4
      rcases n with _ | n
      · exact h5
      rcases n with _ | n
      · exact h6
      simp [factorTwoIntrinsicSixProjectiveRawSixCoefficient]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientFrontierStructural
