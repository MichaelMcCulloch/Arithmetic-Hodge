import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientsStructural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural

/-!
# Exact coefficient frontier for the raw six-mode determinant

This is the public, coefficient-level reconstruction of the last raw
determinant.  It exposes the finite algebraic target behind the final
projective `P5` gap; no pointwise sampling of the half-line occurs here.
-/

def coefficientOdd15Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoIntrinsicFourP45Cross15 1)
    (factorTwoIntrinsicFourP45Cross15 (-1))

def coefficientOdd35Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoIntrinsicFourP45Cross35 1)
    (factorTwoIntrinsicFourP45Cross35 (-1))

def coefficientP5DiagonalPolynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoIntrinsicSixP5Diagonal 1)
    (factorTwoIntrinsicSixP5Diagonal (-1))

def factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial :
    ℝ[X] :=
  coefficientOdd11Polynomial *
      (coefficientOdd33Polynomial * coefficientP5DiagonalPolynomial -
        coefficientOdd35Polynomial ^ 2) -
    coefficientOdd13Polynomial *
      (coefficientOdd13Polynomial * coefficientP5DiagonalPolynomial -
        coefficientOdd15Polynomial * coefficientOdd35Polynomial) +
    coefficientOdd15Polynomial *
      (coefficientOdd13Polynomial * coefficientOdd35Polynomial -
        coefficientOdd15Polynomial * coefficientOdd33Polynomial)

private def rawSixAlternating0 : Fin 3 → ℝ
  | 0 => factorTwoIntrinsicAlternating01
  | 1 => factorTwoIntrinsicAlternating03
  | 2 => factorTwoIntrinsicFourP45Cross05

private def rawSixAlternating2 : Fin 3 → ℝ
  | 0 => factorTwoIntrinsicAlternating21
  | 1 => factorTwoIntrinsicAlternating23
  | 2 => factorTwoIntrinsicFourP45Cross25

private def rawSixAlternating4 : Fin 3 → ℝ
  | 0 => factorTwoIntrinsicFourP45Cross41
  | 1 => factorTwoIntrinsicFourP45Cross43
  | 2 => factorTwoIntrinsicSixAlternating45

def coefficientRawSixAdjugatePairPolynomial (i j : Fin 3) : ℝ[X] :=
  coefficientRawAdjugatePairPolynomial
    (rawSixAlternating0 i) (rawSixAlternating2 i) (rawSixAlternating4 i)
    (rawSixAlternating0 j) (rawSixAlternating2 j) (rawSixAlternating4 j)

def factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial :
    ℝ[X] :=
  (coefficientOdd33Polynomial * coefficientP5DiagonalPolynomial -
      coefficientOdd35Polynomial ^ 2) *
        coefficientRawSixAdjugatePairPolynomial 0 0 +
    2 * (coefficientOdd15Polynomial * coefficientOdd35Polynomial -
      coefficientOdd13Polynomial * coefficientP5DiagonalPolynomial) *
        coefficientRawSixAdjugatePairPolynomial 0 1 +
    2 * (coefficientOdd13Polynomial * coefficientOdd35Polynomial -
      coefficientOdd15Polynomial * coefficientOdd33Polynomial) *
        coefficientRawSixAdjugatePairPolynomial 0 2 +
    (coefficientOdd11Polynomial * coefficientP5DiagonalPolynomial -
      coefficientOdd15Polynomial ^ 2) *
        coefficientRawSixAdjugatePairPolynomial 1 1 +
    2 * (coefficientOdd13Polynomial * coefficientOdd15Polynomial -
      coefficientOdd11Polynomial * coefficientOdd35Polynomial) *
        coefficientRawSixAdjugatePairPolynomial 1 2 +
    (coefficientOdd11Polynomial * coefficientOdd33Polynomial -
      coefficientOdd13Polynomial ^ 2) *
        coefficientRawSixAdjugatePairPolynomial 2 2

private def rawSixCross0 (i j : Fin 3) : ℝ :=
  rawSixAlternating2 i * rawSixAlternating4 j -
    rawSixAlternating4 i * rawSixAlternating2 j

private def rawSixCross2 (i j : Fin 3) : ℝ :=
  rawSixAlternating4 i * rawSixAlternating0 j -
    rawSixAlternating0 i * rawSixAlternating4 j

private def rawSixCross4 (i j : Fin 3) : ℝ :=
  rawSixAlternating0 i * rawSixAlternating2 j -
    rawSixAlternating2 i * rawSixAlternating0 j

private def rawSixCofactor0 : Fin 3 → ℝ
  | 0 => rawSixCross0 1 2
  | 1 => rawSixCross0 2 0
  | 2 => rawSixCross0 0 1

private def rawSixCofactor2 : Fin 3 → ℝ
  | 0 => rawSixCross2 1 2
  | 1 => rawSixCross2 2 0
  | 2 => rawSixCross2 0 1

private def rawSixCofactor4 : Fin 3 → ℝ
  | 0 => rawSixCross4 1 2
  | 1 => rawSixCross4 2 0
  | 2 => rawSixCross4 0 1

def coefficientRawSixEvenEnergyPolynomial
    (u0 u2 u4 v0 v2 v4 : ℝ) : ℝ[X] :=
  coefficientLow00Polynomial * C u0 * C v0 +
    coefficientLow02Polynomial * (C u0 * C v2 + C u2 * C v0) +
    coefficientCross04Polynomial * (C u0 * C v4 + C u4 * C v0) +
    coefficientLow22Polynomial * C u2 * C v2 +
    coefficientCross24Polynomial * (C u2 * C v4 + C u4 * C v2) +
    coefficientP4DiagonalPolynomial * C u4 * C v4

def coefficientRawSixAdjugateCofactorPolynomial (i j : Fin 3) : ℝ[X] :=
  coefficientRawSixEvenEnergyPolynomial
    (rawSixCofactor0 i) (rawSixCofactor2 i) (rawSixCofactor4 i)
    (rawSixCofactor0 j) (rawSixCofactor2 j) (rawSixCofactor4 j)

def factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial :
    ℝ[X] :=
  coefficientOdd11Polynomial * coefficientRawSixAdjugateCofactorPolynomial 0 0 +
    2 * coefficientOdd13Polynomial *
      coefficientRawSixAdjugateCofactorPolynomial 0 1 +
    2 * coefficientOdd15Polynomial *
      coefficientRawSixAdjugateCofactorPolynomial 0 2 +
    coefficientOdd33Polynomial * coefficientRawSixAdjugateCofactorPolynomial 1 1 +
    2 * coefficientOdd35Polynomial *
      coefficientRawSixAdjugateCofactorPolynomial 1 2 +
    coefficientP5DiagonalPolynomial *
      coefficientRawSixAdjugateCofactorPolynomial 2 2

def factorTwoIntrinsicSixProjectiveRawSixAlternatingDeterminant : ℝ :=
  rawSixAlternating0 0 *
      (rawSixAlternating2 1 * rawSixAlternating4 2 -
        rawSixAlternating4 1 * rawSixAlternating2 2) -
    rawSixAlternating2 0 *
      (rawSixAlternating0 1 * rawSixAlternating4 2 -
        rawSixAlternating4 1 * rawSixAlternating0 2) +
    rawSixAlternating4 0 *
      (rawSixAlternating0 1 * rawSixAlternating2 2 -
        rawSixAlternating2 1 * rawSixAlternating0 2)

def factorTwoIntrinsicSixProjectiveRawSixCoefficientPolynomial : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial *
      factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial -
    X *
      factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial +
    X ^ 2 *
      factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial -
    X ^ 3 *
      C (factorTwoIntrinsicSixProjectiveRawSixAlternatingDeterminant ^ 2)

private theorem rawP4PivotPolynomial_eq_coefficientPolynomial :
    factorTwoIntrinsicSixProjectiveRawP4PivotPolynomial =
      factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial := by
  unfold factorTwoIntrinsicSixProjectiveRawP4PivotPolynomial
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial = _
  rfl

private theorem rawOddDeterminantPolynomial_eq_coefficientPolynomial :
    factorTwoIntrinsicSixProjectiveRawOddDeterminantPolynomial =
      factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial := by
  unfold factorTwoIntrinsicSixProjectiveRawOddDeterminantPolynomial
  change factorTwoIntrinsicSixProjectiveRawSixOddDeterminantCoefficientPolynomial = _
  rfl

private theorem rawMixedAdjugateOnePolynomial_eq_coefficientPolynomial :
    factorTwoIntrinsicSixProjectiveRawMixedAdjugateOnePolynomial =
      factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial := by
  unfold factorTwoIntrinsicSixProjectiveRawMixedAdjugateOnePolynomial
  change
    factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial = _
  rfl

private theorem rawMixedAdjugateTwoPolynomial_eq_coefficientPolynomial :
    factorTwoIntrinsicSixProjectiveRawMixedAdjugateTwoPolynomial =
      factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial := by
  have h00 :
      factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial 0 0 =
        coefficientRawSixAdjugateCofactorPolynomial 0 0 := by
    rw [factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial_eq_expanded]
    unfold factorTwoIntrinsicSixProjectiveRawExpandedAdjugateCofactorPolynomial
    change coefficientRawSixAdjugateCofactorPolynomial 0 0 = _
    rfl
  have h01 :
      factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial 0 1 =
        coefficientRawSixAdjugateCofactorPolynomial 0 1 := by
    rw [factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial_eq_expanded]
    unfold factorTwoIntrinsicSixProjectiveRawExpandedAdjugateCofactorPolynomial
    change coefficientRawSixAdjugateCofactorPolynomial 0 1 = _
    rfl
  have h02 :
      factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial 0 2 =
        coefficientRawSixAdjugateCofactorPolynomial 0 2 := by
    rw [factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial_eq_expanded]
    unfold factorTwoIntrinsicSixProjectiveRawExpandedAdjugateCofactorPolynomial
    change coefficientRawSixAdjugateCofactorPolynomial 0 2 = _
    rfl
  have h11 :
      factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial 1 1 =
        coefficientRawSixAdjugateCofactorPolynomial 1 1 := by
    rw [factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial_eq_expanded]
    unfold factorTwoIntrinsicSixProjectiveRawExpandedAdjugateCofactorPolynomial
    change coefficientRawSixAdjugateCofactorPolynomial 1 1 = _
    rfl
  have h12 :
      factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial 1 2 =
        coefficientRawSixAdjugateCofactorPolynomial 1 2 := by
    rw [factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial_eq_expanded]
    unfold factorTwoIntrinsicSixProjectiveRawExpandedAdjugateCofactorPolynomial
    change coefficientRawSixAdjugateCofactorPolynomial 1 2 = _
    rfl
  have h22 :
      factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial 2 2 =
        coefficientRawSixAdjugateCofactorPolynomial 2 2 := by
    rw [factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial_eq_expanded]
    unfold factorTwoIntrinsicSixProjectiveRawExpandedAdjugateCofactorPolynomial
    change coefficientRawSixAdjugateCofactorPolynomial 2 2 = _
    rfl
  unfold factorTwoIntrinsicSixProjectiveRawMixedAdjugateTwoPolynomial
    factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial
    factorTwoIntrinsicSixProjectiveRawOddEntryPolynomial
  rw [h00, h01, h02, h11, h12, h22]
  change
    factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateTwoCoefficientPolynomial = _
  rfl

private theorem rawAlternatingDeterminant_eq_coefficientDeterminant :
    factorTwoIntrinsicSixProjectiveRawAlternatingDeterminant =
      factorTwoIntrinsicSixProjectiveRawSixAlternatingDeterminant := by
  unfold factorTwoIntrinsicSixProjectiveRawAlternatingDeterminant
  change factorTwoIntrinsicSixProjectiveRawSixAlternatingDeterminant = _
  rfl

/-- The private raw determinant implementation is definitionally the public
coefficient reconstruction above. -/
theorem factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial_eq_components :
    factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial =
      factorTwoIntrinsicSixProjectiveRawSixCoefficientPolynomial := by
  unfold factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial
    factorTwoIntrinsicSixProjectiveRawSixCoefficientPolynomial
  rw [rawP4PivotPolynomial_eq_coefficientPolynomial,
    rawOddDeterminantPolynomial_eq_coefficientPolynomial,
    rawMixedAdjugateOnePolynomial_eq_coefficientPolynomial,
    rawMixedAdjugateTwoPolynomial_eq_coefficientPolynomial,
    rawAlternatingDeterminant_eq_coefficientDeterminant]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientsStructural
