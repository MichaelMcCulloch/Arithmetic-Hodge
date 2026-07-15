import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural

/-!
# Exact coefficient frontier for the raw five-mode determinant

The raw `P0/P2/P4/P1/P3` determinant is a quintic.  This file rebuilds its
private component polynomials from the public endpoint scalars and exposes
the six exact convolution coefficients.  The two endpoint coefficients are
positive endpoint determinants; only the four middle coefficients mix the
two signs.
-/

/-- The affine odd `P1,P3` entry in projective coordinates. -/
def coefficientOdd13Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoIntrinsicOddPhaseLow13 1)
    (factorTwoIntrinsicOddPhaseLow13 (-1))

/-- The affine odd `P3,P3` entry in projective coordinates. -/
def coefficientOdd33Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoIntrinsicOddPhaseLow33 1)
    (factorTwoIntrinsicOddPhaseLow33 (-1))

/-- The determinant of the affine odd `P1/P3` endpoint pencil. -/
def factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial : ℝ[X] :=
  coefficientOdd11Polynomial * coefficientOdd33Polynomial -
    coefficientOdd13Polynomial ^ 2

/-- Polarized adjugate form of the public affine even `P0/P2/P4` pencil. -/
def coefficientRawAdjugatePairPolynomial
    (u0 u2 u4 v0 v2 v4 : ℝ) : ℝ[X] :=
  (coefficientLow22Polynomial * coefficientP4DiagonalPolynomial -
      coefficientCross24Polynomial ^ 2) * C u0 * C v0 +
    (coefficientCross04Polynomial * coefficientCross24Polynomial -
        coefficientLow02Polynomial * coefficientP4DiagonalPolynomial) *
      (C u0 * C v2 + C u2 * C v0) +
    (coefficientLow02Polynomial * coefficientCross24Polynomial -
        coefficientCross04Polynomial * coefficientLow22Polynomial) *
      (C u0 * C v4 + C u4 * C v0) +
    (coefficientLow00Polynomial * coefficientP4DiagonalPolynomial -
        coefficientCross04Polynomial ^ 2) * C u2 * C v2 +
    (coefficientLow02Polynomial * coefficientCross04Polynomial -
        coefficientLow00Polynomial * coefficientCross24Polynomial) *
      (C u2 * C v4 + C u4 * C v2) +
    coefficientLowDetPolynomial * C u4 * C v4

/-- The unshifted cubic coupling in the raw five-mode determinant. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial :
    ℝ[X] :=
  coefficientOdd33Polynomial *
      coefficientRawAdjugatePairPolynomial
        factorTwoIntrinsicAlternating01
        factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41
        factorTwoIntrinsicAlternating01
        factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41 -
    2 * coefficientOdd13Polynomial *
      coefficientRawAdjugatePairPolynomial
        factorTwoIntrinsicAlternating01
        factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41
        factorTwoIntrinsicAlternating03
        factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43 +
    coefficientOdd11Polynomial *
      coefficientRawAdjugatePairPolynomial
        factorTwoIntrinsicAlternating03
        factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43
        factorTwoIntrinsicAlternating03
        factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43

/-- `P0` coordinate of the oriented cross product of the `P1` and `P3`
alternating columns. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCross0 : ℝ :=
  factorTwoIntrinsicAlternating21 * factorTwoIntrinsicFourP45Cross43 -
    factorTwoIntrinsicFourP45Cross41 * factorTwoIntrinsicAlternating23

/-- `P2` coordinate of the oriented cross product of the `P1` and `P3`
alternating columns. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCross2 : ℝ :=
  factorTwoIntrinsicFourP45Cross41 * factorTwoIntrinsicAlternating03 -
    factorTwoIntrinsicAlternating01 * factorTwoIntrinsicFourP45Cross43

/-- `P4` coordinate of the oriented cross product of the `P1` and `P3`
alternating columns. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCross4 : ℝ :=
  factorTwoIntrinsicAlternating01 * factorTwoIntrinsicAlternating23 -
    factorTwoIntrinsicAlternating21 * factorTwoIntrinsicAlternating03

/-- Polynomial-ring realization of the `P0` cross-product coordinate. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial : ℝ[X] :=
  C factorTwoIntrinsicAlternating21 *
      C factorTwoIntrinsicFourP45Cross43 -
    C factorTwoIntrinsicFourP45Cross41 *
      C factorTwoIntrinsicAlternating23

/-- Polynomial-ring realization of the `P2` cross-product coordinate. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial : ℝ[X] :=
  C factorTwoIntrinsicFourP45Cross41 *
      C factorTwoIntrinsicAlternating03 -
    C factorTwoIntrinsicAlternating01 *
      C factorTwoIntrinsicFourP45Cross43

/-- Polynomial-ring realization of the `P4` cross-product coordinate. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial : ℝ[X] :=
  C factorTwoIntrinsicAlternating01 *
      C factorTwoIntrinsicAlternating23 -
    C factorTwoIntrinsicAlternating21 *
      C factorTwoIntrinsicAlternating03

/-- The affine even energy of the oriented alternating cross product. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial :
    ℝ[X] :=
  coefficientLow00Polynomial *
      factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial *
      factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial +
    coefficientLow02Polynomial *
      (factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial *
          factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial +
        factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial *
          factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial) +
    coefficientCross04Polynomial *
      (factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial *
          factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial +
        factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial *
          factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial) +
    coefficientLow22Polynomial *
      factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial *
      factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial +
    coefficientCross24Polynomial *
      (factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial *
          factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial +
        factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial *
          factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial) +
    coefficientP4DiagonalPolynomial *
      factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial *
      factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial

/-- Public component reconstruction of the raw five-mode determinant. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficientPolynomial : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial *
      factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial -
    X *
      factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial +
    X ^ 2 *
      factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial

/-- The public raw five-mode determinant is exactly the displayed component
polynomial; no evaluations or sampling enter this identity. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial_eq_components :
    factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial =
      factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficientPolynomial := by
  unfold factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial
  change
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial *
        (coefficientOdd11Polynomial * coefficientOdd33Polynomial -
          coefficientOdd13Polynomial ^ 2) -
      X *
        (coefficientOdd33Polynomial *
            coefficientRawAdjugatePairPolynomial
              factorTwoIntrinsicAlternating01
              factorTwoIntrinsicAlternating21
              factorTwoIntrinsicFourP45Cross41
              factorTwoIntrinsicAlternating01
              factorTwoIntrinsicAlternating21
              factorTwoIntrinsicFourP45Cross41 -
          2 * coefficientOdd13Polynomial *
            coefficientRawAdjugatePairPolynomial
              factorTwoIntrinsicAlternating01
              factorTwoIntrinsicAlternating21
              factorTwoIntrinsicFourP45Cross41
              factorTwoIntrinsicAlternating03
              factorTwoIntrinsicAlternating23
              factorTwoIntrinsicFourP45Cross43 +
          coefficientOdd11Polynomial *
            coefficientRawAdjugatePairPolynomial
              factorTwoIntrinsicAlternating03
              factorTwoIntrinsicAlternating23
              factorTwoIntrinsicFourP45Cross43
              factorTwoIntrinsicAlternating03
              factorTwoIntrinsicAlternating23
              factorTwoIntrinsicFourP45Cross43) +
      X ^ 2 *
        factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial = _
  unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficientPolynomial
    factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
    factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial
  rfl

abbrev rawFiveOddMinorCoeff (n : ℕ) : ℝ :=
  factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff n

abbrev rawFiveCouplingCoeff (n : ℕ) : ℝ :=
  factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial.coeff n

abbrev rawFiveCrossEnergyCoeff (n : ℕ) : ℝ :=
  factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial.coeff n

/-- The six exact convolution coefficients of the raw quintic. -/
def factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient : ℕ → ℝ
  | 0 => pivotCoeff 0 * rawFiveOddMinorCoeff 0
  | 1 => pivotCoeff 0 * rawFiveOddMinorCoeff 1 +
      pivotCoeff 1 * rawFiveOddMinorCoeff 0 - rawFiveCouplingCoeff 0
  | 2 => pivotCoeff 0 * rawFiveOddMinorCoeff 2 +
      pivotCoeff 1 * rawFiveOddMinorCoeff 1 +
      pivotCoeff 2 * rawFiveOddMinorCoeff 0 - rawFiveCouplingCoeff 1 +
      rawFiveCrossEnergyCoeff 0
  | 3 => pivotCoeff 1 * rawFiveOddMinorCoeff 2 +
      pivotCoeff 2 * rawFiveOddMinorCoeff 1 +
      pivotCoeff 3 * rawFiveOddMinorCoeff 0 - rawFiveCouplingCoeff 2 +
      rawFiveCrossEnergyCoeff 1
  | 4 => pivotCoeff 2 * rawFiveOddMinorCoeff 2 +
      pivotCoeff 3 * rawFiveOddMinorCoeff 1 - rawFiveCouplingCoeff 3
  | 5 => pivotCoeff 3 * rawFiveOddMinorCoeff 2
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

private theorem natDegree_oddMinor_le :
    factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.natDegree ≤ 2 := by
  unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
    coefficientOdd11Polynomial coefficientOdd13Polynomial
    coefficientOdd33Polynomial endpointAffinePolynomial
  compute_degree

private theorem natDegree_coupling_le :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial.natDegree ≤ 3 := by
  unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial
    coefficientRawAdjugatePairPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    coefficientOdd11Polynomial coefficientOdd13Polynomial
    coefficientOdd33Polynomial endpointAffinePolynomial
  compute_degree

private theorem natDegree_crossEnergy_le :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial.natDegree ≤ 1 := by
  unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial
    factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial
    factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial
    endpointAffinePolynomial
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

private theorem oddMinor_as_coefficients :
    factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial =
      C (rawFiveOddMinorCoeff 0) + C (rawFiveOddMinorCoeff 1) * X +
        C (rawFiveOddMinorCoeff 2) * X ^ 2 := by
  rw [factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.as_sum_range_C_mul_X_pow'
    (show factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.natDegree < 3 by
      have h := natDegree_oddMinor_le
      omega)]
  simp [Finset.sum_range_succ]

private theorem coupling_as_coefficients :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial =
      C (rawFiveCouplingCoeff 0) + C (rawFiveCouplingCoeff 1) * X +
        C (rawFiveCouplingCoeff 2) * X ^ 2 +
        C (rawFiveCouplingCoeff 3) * X ^ 3 := by
  rw [factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial.as_sum_range_C_mul_X_pow'
    (show factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial.natDegree < 4 by
      have h := natDegree_coupling_le
      omega)]
  simp [Finset.sum_range_succ]

private theorem crossEnergy_as_coefficients :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial =
      C (rawFiveCrossEnergyCoeff 0) +
        C (rawFiveCrossEnergyCoeff 1) * X := by
  rw [factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial.as_sum_range_C_mul_X_pow'
    (show factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial.natDegree < 2 by
      have h := natDegree_crossEnergy_le
      omega)]
  simp [Finset.sum_range_succ]

/-- Exact degree-five expansion of the public raw determinant. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial_eq_coefficients :
    factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial =
      C (factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 0) +
        C (factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1) * X +
        C (factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 2) * X ^ 2 +
        C (factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 3) * X ^ 3 +
        C (factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4) * X ^ 4 +
        C (factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 5) * X ^ 5 := by
  rw [factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial_eq_components]
  unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficientPolynomial
  rw [pivot_as_coefficients, oddMinor_as_coefficients,
    coupling_as_coefficients, crossEnergy_as_coefficients]
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  simp only [map_add, map_sub, map_mul]
  ring

/-- Every coefficient of the public raw determinant is one of the six
displayed scalars, and all higher coefficients vanish. -/
theorem coeff_factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial
    (n : ℕ) :
    factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial.coeff n =
      factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient n := by
  rw [factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial_eq_coefficients]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  simp only [coeff_add, coeff_C, coeff_C_mul_X,
    coeff_C_mul_X_pow]
  simp [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]

/-- Structural degree support: the raw determinant has no term of degree at
least six. -/
theorem coeff_factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial_eq_zero
    (n : ℕ) (hn : 6 ≤ n) :
    factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial.coeff n = 0 := by
  rw [coeff_factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial]
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
  simp [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]

private theorem rawFiveOddMinorCoeff_zero_eq :
    rawFiveOddMinorCoeff 0 =
      factorTwoIntrinsicOddPhaseLow11 1 *
          factorTwoIntrinsicOddPhaseLow33 1 -
        factorTwoIntrinsicOddPhaseLow13 1 ^ 2 := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial,
    coefficientOdd11Polynomial, coefficientOdd13Polynomial,
    coefficientOdd33Polynomial, endpointAffinePolynomial]

private theorem rawFiveOddMinorCoeff_two_eq :
    rawFiveOddMinorCoeff 2 =
      factorTwoIntrinsicOddPhaseLow11 (-1) *
          factorTwoIntrinsicOddPhaseLow33 (-1) -
        factorTwoIntrinsicOddPhaseLow13 (-1) ^ 2 := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 2 = _
  have hpoly :
      factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial =
        C (factorTwoIntrinsicOddPhaseLow11 1 *
              factorTwoIntrinsicOddPhaseLow33 1 -
            factorTwoIntrinsicOddPhaseLow13 1 ^ 2) +
          C (factorTwoIntrinsicOddPhaseLow11 1 *
                factorTwoIntrinsicOddPhaseLow33 (-1) +
              factorTwoIntrinsicOddPhaseLow11 (-1) *
                factorTwoIntrinsicOddPhaseLow33 1 -
              2 * factorTwoIntrinsicOddPhaseLow13 1 *
                factorTwoIntrinsicOddPhaseLow13 (-1)) * X +
          C (factorTwoIntrinsicOddPhaseLow11 (-1) *
                factorTwoIntrinsicOddPhaseLow33 (-1) -
              factorTwoIntrinsicOddPhaseLow13 (-1) ^ 2) * X ^ 2 := by
    unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
      coefficientOdd11Polynomial coefficientOdd13Polynomial
      coefficientOdd33Polynomial endpointAffinePolynomial
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private theorem rawFiveOddMinorCoeff_zero_pos :
    0 < rawFiveOddMinorCoeff 0 := by
  rw [rawFiveOddMinorCoeff_zero_eq]
  have h := oddStructuralLow_endpoint_gates.2.1
  simpa [factorTwoIntrinsicOddPhaseLow11,
    factorTwoIntrinsicOddPhaseLow13, factorTwoIntrinsicOddPhaseLow33,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow13,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow33] using h

private theorem rawFiveOddMinorCoeff_two_pos :
    0 < rawFiveOddMinorCoeff 2 := by
  rw [rawFiveOddMinorCoeff_two_eq]
  have h := oddStructuralLow_endpoint_gates.2.2.2
  simpa [factorTwoIntrinsicOddPhaseLow11,
    factorTwoIntrinsicOddPhaseLow13, factorTwoIntrinsicOddPhaseLow33,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow13,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow33] using h

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
  have := mul_nonpos_of_nonpos_of_nonneg hp coefficientOdd11_zero_pos.le
  linarith

private theorem pivotCoeff_three_pos : 0 < pivotCoeff 3 := by
  have hprod :=
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_four_pos
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient] at hprod
  by_contra h
  have hp : pivotCoeff 3 ≤ 0 := le_of_not_gt h
  have := mul_nonpos_of_nonpos_of_nonneg hp coefficientOdd11_one_pos.le
  linarith

/-- The plus-endpoint coefficient is strictly positive. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_zero_pos :
    0 < factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 0 := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  exact mul_pos pivotCoeff_zero_pos rawFiveOddMinorCoeff_zero_pos

/-- The minus-endpoint coefficient is strictly positive. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_five_pos :
    0 < factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 5 := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  exact mul_pos pivotCoeff_three_pos rawFiveOddMinorCoeff_two_pos

/-- The raw quintic belongs to the strict nonnegative coefficient cone once
its four genuinely mixed coefficients are nonnegative. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFive_mem_cone_of_middle
    (h1 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1)
    (h2 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 2)
    (h3 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 3)
    (h4 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4) :
    StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial := by
  constructor
  · rw [coeff_factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial]
    exact factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_zero_pos
  · intro n
    rw [coeff_factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial]
    rcases n with _ | n
    · exact factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_zero_pos.le
    rcases n with _ | n
    · exact h1
    rcases n with _ | n
    · exact h2
    rcases n with _ | n
    · exact h3
    rcases n with _ | n
    · exact h4
    rcases n with _ | n
    · exact factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_five_pos.le
    simp [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]

/-- Exact minimal frontier for the raw quintic coefficient cone. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFive_mem_cone_iff_middle :
    StrictNonnegativeCoefficientCone
        factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial ↔
      0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 2 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 3 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial]
      exact h.2 1
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial]
      exact h.2 2
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial]
      exact h.2 3
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial]
      exact h.2 4
  · rintro ⟨h1, h2, h3, h4⟩
    exact factorTwoIntrinsicSixProjectiveRawMinorFive_mem_cone_of_middle
      h1 h2 h3 h4

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
