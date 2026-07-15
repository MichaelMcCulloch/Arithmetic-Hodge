import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEndpointControlsStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4UniformStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP4UniformStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Exact coefficient frontier for the projective six-mode gates

This file does not sample the projective half-line.  It exposes the exact
low-degree convolution underlying each determinant polynomial.  In
particular, the second pivot is a product of two cubics minus `X` times the
square of a quadratic.  Its coefficient cone is therefore equivalent to a
short list of scalar mixed-coefficient inequalities; the two endpoint
coefficients factor separately.
-/

private def endpointAffinePolynomial (plus minus : ℝ) : ℝ[X] :=
  C plus + C minus * X

private theorem eval_endpointAffinePolynomial (plus minus x : ℝ) :
    (endpointAffinePolynomial plus minus).eval x = plus + x * minus := by
  simp [endpointAffinePolynomial]
  ring

private theorem coeff_three_endpointAffinePolynomial_triple
    (a0 a1 b0 b1 c0 c1 : ℝ) :
    (endpointAffinePolynomial a0 a1 *
        endpointAffinePolynomial b0 b1 *
        endpointAffinePolynomial c0 c1).coeff 3 = a1 * b1 * c1 := by
  have h :
      endpointAffinePolynomial a0 a1 *
          endpointAffinePolynomial b0 b1 *
          endpointAffinePolynomial c0 c1 =
        C (a0 * b0 * c0) +
          C (a1 * b0 * c0 + a0 * b1 * c0 + a0 * b0 * c1) * X +
          C (a1 * b1 * c0 + a1 * b0 * c1 + a0 * b1 * c1) * X ^ 2 +
          C (a1 * b1 * c1) * X ^ 3 := by
    unfold endpointAffinePolynomial
    simp only [map_add, map_mul]
    ring
  rw [h]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private def coefficientLow00Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoStructuralPhaseLow00 1)
    (factorTwoStructuralPhaseLow00 (-1))

private def coefficientLow02Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoStructuralPhaseLow02 1)
    (factorTwoStructuralPhaseLow02 (-1))

private def coefficientLow22Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoStructuralPhaseLow22 1)
    (factorTwoStructuralPhaseLow22 (-1))

private def coefficientLowDetPolynomial : ℝ[X] :=
  coefficientLow00Polynomial * coefficientLow22Polynomial -
    coefficientLow02Polynomial ^ 2

private def coefficientCross04Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoIntrinsicFourP45Cross04 (-1))

private def coefficientCross24Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicFourP45Cross24 (-1))

private def coefficientP4DiagonalPolynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoIntrinsicSixP4Diagonal 1)
    (factorTwoIntrinsicSixP4Diagonal (-1))

private def coefficientOdd11Polynomial : ℝ[X] :=
  endpointAffinePolynomial
    (factorTwoIntrinsicOddPhaseLow11 1)
    (factorTwoIntrinsicOddPhaseLow11 (-1))

private def coefficientAdjugateTwoPolynomial
    (u0 u2 v0 v2 : ℝ[X]) : ℝ[X] :=
  coefficientLow22Polynomial * u0 * v0 -
    coefficientLow02Polynomial * (u0 * v2 + u2 * v0) +
    coefficientLow00Polynomial * u2 * v2

/-- The exact cubic numerator of the projective `P4` pivot, rebuilt with
public endpoint scalars so that its coefficients can be named below. -/
def factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial : ℝ[X] :=
  coefficientLowDetPolynomial * coefficientP4DiagonalPolynomial -
    coefficientAdjugateTwoPolynomial
      coefficientCross04Polynomial coefficientCross24Polynomial
      coefficientCross04Polynomial coefficientCross24Polynomial

/-- The exact quadratic numerator of the `P4`--`P1` alternating cross. -/
def factorTwoIntrinsicSixProjectiveP4P1CrossCoefficientPolynomial : ℝ[X] :=
  coefficientLowDetPolynomial * C factorTwoIntrinsicFourP45Cross41 -
    coefficientAdjugateTwoPolynomial
      coefficientCross04Polynomial coefficientCross24Polynomial
      (C factorTwoIntrinsicAlternating01)
      (C factorTwoIntrinsicAlternating21)

/-- The exact cubic numerator of the projective `P1,P1` residual. -/
def factorTwoIntrinsicSixProjectiveP1ResidualCoefficientPolynomial : ℝ[X] :=
  coefficientLowDetPolynomial * coefficientOdd11Polynomial -
    X * coefficientAdjugateTwoPolynomial
      (C factorTwoIntrinsicAlternating01)
      (C factorTwoIntrinsicAlternating21)
      (C factorTwoIntrinsicAlternating01)
      (C factorTwoIntrinsicAlternating21)

/-! The raw determinant factor is lower degree than the fraction-free Schur
numerator.  It is therefore the right object for coefficient signs. -/

private def coefficientP1AlternatingAdjugatePolynomial : ℝ[X] :=
  (coefficientLow22Polynomial * coefficientP4DiagonalPolynomial -
      coefficientCross24Polynomial ^ 2) *
        C factorTwoIntrinsicAlternating01 ^ 2 +
    (coefficientCross04Polynomial * coefficientCross24Polynomial -
        coefficientLow02Polynomial * coefficientP4DiagonalPolynomial) *
      (2 * C factorTwoIntrinsicAlternating01 *
        C factorTwoIntrinsicAlternating21) +
    (coefficientLow02Polynomial * coefficientCross24Polynomial -
        coefficientCross04Polynomial * coefficientLow22Polynomial) *
      (2 * C factorTwoIntrinsicAlternating01 *
        C factorTwoIntrinsicFourP45Cross41) +
    (coefficientLow00Polynomial * coefficientP4DiagonalPolynomial -
        coefficientCross04Polynomial ^ 2) *
      C factorTwoIntrinsicAlternating21 ^ 2 +
    (coefficientLow02Polynomial * coefficientCross04Polynomial -
        coefficientLow00Polynomial * coefficientCross24Polynomial) *
      (2 * C factorTwoIntrinsicAlternating21 *
        C factorTwoIntrinsicFourP45Cross41) +
    coefficientLowDetPolynomial *
      C factorTwoIntrinsicFourP45Cross41 ^ 2

/-- Public reconstruction of the raw degree-four `P0/P2/P4/P1`
determinant. -/
def factorTwoIntrinsicSixProjectiveRawMinorFourCoefficientPolynomial : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial *
      coefficientOdd11Polynomial -
    X * coefficientP1AlternatingAdjugatePolynomial

private theorem eval_coefficientLowDetPolynomial (x : ℝ) :
    coefficientLowDetPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveLowDet x := by
  unfold coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial
    factorTwoIntrinsicSixProjectiveLowDet
    factorTwoIntrinsicSixProjectiveLow00
    factorTwoIntrinsicSixProjectiveLow02
    factorTwoIntrinsicSixProjectiveLow22
  simp only [eval_sub, eval_mul, eval_pow, eval_endpointAffinePolynomial]

private theorem eval_coefficientAdjugateTwoPolynomial
    (x : ℝ) (u0 u2 v0 v2 : ℝ[X]) :
    (coefficientAdjugateTwoPolynomial u0 u2 v0 v2).eval x =
      factorTwoIntrinsicSixAdjugateBilinear
        (factorTwoIntrinsicSixProjectiveLow00 x)
        (factorTwoIntrinsicSixProjectiveLow02 x)
        (factorTwoIntrinsicSixProjectiveLow22 x)
        (u0.eval x) (u2.eval x) (v0.eval x) (v2.eval x) := by
  unfold coefficientAdjugateTwoPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial
    factorTwoIntrinsicSixAdjugateBilinear
    factorTwoIntrinsicSixProjectiveLow00
    factorTwoIntrinsicSixProjectiveLow02
    factorTwoIntrinsicSixProjectiveLow22
  simp only [eval_sub, eval_add, eval_mul, eval_endpointAffinePolynomial]

theorem eval_factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    (x : ℝ) :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveP4Pivot x := by
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    factorTwoIntrinsicSixProjectiveP4Pivot
  change _ = factorTwoIntrinsicSixProjectiveLowDet x *
      factorTwoIntrinsicSixProjectiveP4Diagonal x -
        factorTwoIntrinsicSixAdjugateBilinear
          (factorTwoIntrinsicSixProjectiveLow00 x)
          (factorTwoIntrinsicSixProjectiveLow02 x)
          (factorTwoIntrinsicSixProjectiveLow22 x)
          (factorTwoIntrinsicSixProjectiveCross04 x)
          (factorTwoIntrinsicSixProjectiveCross24 x)
          (factorTwoIntrinsicSixProjectiveCross04 x)
          (factorTwoIntrinsicSixProjectiveCross24 x)
  simp only [eval_sub, eval_mul, eval_coefficientLowDetPolynomial,
    eval_coefficientAdjugateTwoPolynomial]
  unfold coefficientP4DiagonalPolynomial coefficientCross04Polynomial
    coefficientCross24Polynomial
    factorTwoIntrinsicSixProjectiveP4Diagonal
    factorTwoIntrinsicSixProjectiveCross04
    factorTwoIntrinsicSixProjectiveCross24
  simp only [eval_endpointAffinePolynomial]

theorem eval_factorTwoIntrinsicSixProjectiveP4P1CrossCoefficientPolynomial
    (x : ℝ) :
    factorTwoIntrinsicSixProjectiveP4P1CrossCoefficientPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveP4OddCross x 0 := by
  unfold factorTwoIntrinsicSixProjectiveP4P1CrossCoefficientPolynomial
    factorTwoIntrinsicSixProjectiveP4OddCross
  change _ = factorTwoIntrinsicSixProjectiveLowDet x *
      factorTwoIntrinsicFourP45Cross41 -
        factorTwoIntrinsicSixAdjugateBilinear
          (factorTwoIntrinsicSixProjectiveLow00 x)
          (factorTwoIntrinsicSixProjectiveLow02 x)
          (factorTwoIntrinsicSixProjectiveLow22 x)
          (factorTwoIntrinsicSixProjectiveCross04 x)
          (factorTwoIntrinsicSixProjectiveCross24 x)
          factorTwoIntrinsicAlternating01
          factorTwoIntrinsicAlternating21
  simp only [eval_sub, eval_mul, eval_C,
    eval_coefficientLowDetPolynomial,
    eval_coefficientAdjugateTwoPolynomial]
  unfold coefficientCross04Polynomial coefficientCross24Polynomial
    factorTwoIntrinsicSixProjectiveCross04
    factorTwoIntrinsicSixProjectiveCross24
  simp only [eval_endpointAffinePolynomial]

theorem eval_factorTwoIntrinsicSixProjectiveP1ResidualCoefficientPolynomial
    (x : ℝ) :
    factorTwoIntrinsicSixProjectiveP1ResidualCoefficientPolynomial.eval x =
      factorTwoIntrinsicSixProjectiveOddResidual x 0 0 := by
  unfold factorTwoIntrinsicSixProjectiveP1ResidualCoefficientPolynomial
    factorTwoIntrinsicSixProjectiveOddResidual
  change _ = factorTwoIntrinsicSixProjectiveLowDet x *
      factorTwoIntrinsicSixProjectiveOdd11 x -
        x * factorTwoIntrinsicSixAdjugateBilinear
          (factorTwoIntrinsicSixProjectiveLow00 x)
          (factorTwoIntrinsicSixProjectiveLow02 x)
          (factorTwoIntrinsicSixProjectiveLow22 x)
          factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
          factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
  simp only [eval_sub, eval_mul, eval_X,
    eval_coefficientLowDetPolynomial,
    eval_coefficientAdjugateTwoPolynomial, eval_C]
  unfold coefficientOdd11Polynomial
    factorTwoIntrinsicSixProjectiveOdd11
  simp only [eval_endpointAffinePolynomial]

/-- Exact factorization of the second gate into a cubic-by-cubic product
minus the shifted square of a quadratic. -/
theorem factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial_eq_components :
    factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial =
      factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial *
          factorTwoIntrinsicSixProjectiveP1ResidualCoefficientPolynomial -
        X *
          factorTwoIntrinsicSixProjectiveP4P1CrossCoefficientPolynomial ^ 2 := by
  apply Polynomial.funext
  intro x
  rw [eval_factorTwoIntrinsicSixProjectiveBaseMinorTwoPolynomial]
  simp only [eval_sub, eval_mul, eval_pow, eval_X,
    eval_factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial,
    eval_factorTwoIntrinsicSixProjectiveP1ResidualCoefficientPolynomial,
    eval_factorTwoIntrinsicSixProjectiveP4P1CrossCoefficientPolynomial]
  rfl

/-- The public raw four-mode determinant is definitionally the quartic
component polynomial displayed above. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial_eq_components :
    factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial =
      factorTwoIntrinsicSixProjectiveRawMinorFourCoefficientPolynomial := by
  unfold factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial
  change
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial *
          coefficientOdd11Polynomial -
        X *
          ((coefficientLow22Polynomial *
                  coefficientP4DiagonalPolynomial -
                coefficientCross24Polynomial ^ 2) *
              C factorTwoIntrinsicAlternating01 *
              C factorTwoIntrinsicAlternating01 +
            (coefficientCross04Polynomial *
                  coefficientCross24Polynomial -
                coefficientLow02Polynomial *
                  coefficientP4DiagonalPolynomial) *
              (C factorTwoIntrinsicAlternating01 *
                  C factorTwoIntrinsicAlternating21 +
                C factorTwoIntrinsicAlternating21 *
                  C factorTwoIntrinsicAlternating01) +
            (coefficientLow02Polynomial *
                  coefficientCross24Polynomial -
                coefficientCross04Polynomial *
                  coefficientLow22Polynomial) *
              (C factorTwoIntrinsicAlternating01 *
                  C factorTwoIntrinsicFourP45Cross41 +
                C factorTwoIntrinsicFourP45Cross41 *
                  C factorTwoIntrinsicAlternating01) +
            (coefficientLow00Polynomial *
                  coefficientP4DiagonalPolynomial -
                coefficientCross04Polynomial ^ 2) *
              C factorTwoIntrinsicAlternating21 *
              C factorTwoIntrinsicAlternating21 +
            (coefficientLow02Polynomial *
                  coefficientCross04Polynomial -
                coefficientLow00Polynomial *
                  coefficientCross24Polynomial) *
              (C factorTwoIntrinsicAlternating21 *
                  C factorTwoIntrinsicFourP45Cross41 +
                C factorTwoIntrinsicFourP45Cross41 *
                  C factorTwoIntrinsicAlternating21) +
            coefficientLowDetPolynomial *
              C factorTwoIntrinsicFourP45Cross41 *
              C factorTwoIntrinsicFourP45Cross41) = _
  unfold factorTwoIntrinsicSixProjectiveRawMinorFourCoefficientPolynomial
    coefficientP1AlternatingAdjugatePolynomial
  ring

/-! ## Exact seven-coefficient reduction for the second pivot -/

private abbrev pivotCoeff (n : ℕ) : ℝ :=
  factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff n

private abbrev residualOneCoeff (n : ℕ) : ℝ :=
  factorTwoIntrinsicSixProjectiveP1ResidualCoefficientPolynomial.coeff n

private abbrev crossFourOneCoeff (n : ℕ) : ℝ :=
  factorTwoIntrinsicSixProjectiveP4P1CrossCoefficientPolynomial.coeff n

private abbrev p1AlternatingAdjugateCoeff (n : ℕ) : ℝ :=
  coefficientP1AlternatingAdjugatePolynomial.coeff n

/-- The five exact coefficients of the raw determinant factor.  Only the
three middle entries mix the two signed endpoints. -/
def factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient : ℕ → ℝ
  | 0 => pivotCoeff 0 * coefficientOdd11Polynomial.coeff 0
  | 1 => pivotCoeff 0 * coefficientOdd11Polynomial.coeff 1 +
      pivotCoeff 1 * coefficientOdd11Polynomial.coeff 0 -
      p1AlternatingAdjugateCoeff 0
  | 2 => pivotCoeff 1 * coefficientOdd11Polynomial.coeff 1 +
      pivotCoeff 2 * coefficientOdd11Polynomial.coeff 0 -
      p1AlternatingAdjugateCoeff 1
  | 3 => pivotCoeff 2 * coefficientOdd11Polynomial.coeff 1 +
      pivotCoeff 3 * coefficientOdd11Polynomial.coeff 0 -
      p1AlternatingAdjugateCoeff 2
  | 4 => pivotCoeff 3 * coefficientOdd11Polynomial.coeff 1
  | _ => 0

private theorem natDegree_factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial_le :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.natDegree ≤ 3 := by
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial
  compute_degree

private theorem natDegree_coefficientOdd11Polynomial_le :
    coefficientOdd11Polynomial.natDegree ≤ 1 := by
  unfold coefficientOdd11Polynomial endpointAffinePolynomial
  compute_degree

private theorem natDegree_coefficientP1AlternatingAdjugatePolynomial_le :
    coefficientP1AlternatingAdjugatePolynomial.natDegree ≤ 2 := by
  unfold coefficientP1AlternatingAdjugatePolynomial
    coefficientLowDetPolynomial coefficientLow00Polynomial
    coefficientLow02Polynomial coefficientLow22Polynomial
    coefficientCross04Polynomial coefficientCross24Polynomial
    coefficientP4DiagonalPolynomial endpointAffinePolynomial
  compute_degree

private theorem factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial_as_coefficients :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial =
      C (pivotCoeff 0) + C (pivotCoeff 1) * X +
        C (pivotCoeff 2) * X ^ 2 + C (pivotCoeff 3) * X ^ 3 := by
  rw [factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.as_sum_range_C_mul_X_pow'
    (show factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.natDegree < 4 by
      have h :=
        natDegree_factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial_le
      omega)]
  simp [Finset.sum_range_succ]

private theorem coefficientOdd11Polynomial_as_coefficients :
    coefficientOdd11Polynomial =
      C (coefficientOdd11Polynomial.coeff 0) +
        C (coefficientOdd11Polynomial.coeff 1) * X := by
  rw [coefficientOdd11Polynomial.as_sum_range_C_mul_X_pow'
    (show coefficientOdd11Polynomial.natDegree < 2 by
      have h := natDegree_coefficientOdd11Polynomial_le
      omega)]
  simp [Finset.sum_range_succ]

private theorem coefficientP1AlternatingAdjugatePolynomial_as_coefficients :
    coefficientP1AlternatingAdjugatePolynomial =
      C (p1AlternatingAdjugateCoeff 0) +
        C (p1AlternatingAdjugateCoeff 1) * X +
        C (p1AlternatingAdjugateCoeff 2) * X ^ 2 := by
  rw [coefficientP1AlternatingAdjugatePolynomial.as_sum_range_C_mul_X_pow'
    (show coefficientP1AlternatingAdjugatePolynomial.natDegree < 3 by
      have h := natDegree_coefficientP1AlternatingAdjugatePolynomial_le
      omega)]
  simp [Finset.sum_range_succ]

/-- Exact quartic expansion of the raw determinant. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial_eq_coefficients :
    factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial =
      C (factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 0) +
        C (factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 1) * X +
        C (factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 2) * X ^ 2 +
        C (factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 3) * X ^ 3 +
        C (factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 4) * X ^ 4 := by
  rw [factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial_eq_components]
  unfold factorTwoIntrinsicSixProjectiveRawMinorFourCoefficientPolynomial
  rw [factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial_as_coefficients,
    coefficientOdd11Polynomial_as_coefficients,
    coefficientP1AlternatingAdjugatePolynomial_as_coefficients]
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  simp only [map_add, map_sub, map_mul]
  ring

/-- Every coefficient of the public raw determinant is one of the five
displayed scalars (and is zero above degree four). -/
theorem coeff_factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial
    (n : ℕ) :
    factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial.coeff n =
      factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient n := by
  rw [factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial_eq_coefficients]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  rcases n with _ | n
  · simp only [coeff_add, coeff_C, coeff_C_mul_X,
      coeff_C_mul_X_pow]
    simp [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  simp only [coeff_add, coeff_C, coeff_C_mul_X,
    coeff_C_mul_X_pow]
  simp [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]

/-! ## Endpoint factors and the three mixed scalar inequalities -/

private theorem coefficientOdd11Polynomial_coeff_zero :
    coefficientOdd11Polynomial.coeff 0 =
      factorTwoIntrinsicOddPhaseLow11 1 := by
  simp [coefficientOdd11Polynomial, endpointAffinePolynomial]

private theorem coefficientOdd11Polynomial_coeff_one :
    coefficientOdd11Polynomial.coeff 1 =
      factorTwoIntrinsicOddPhaseLow11 (-1) := by
  simp [coefficientOdd11Polynomial, endpointAffinePolynomial]

private theorem coefficientOdd11Polynomial_coeff_zero_pos :
    0 < coefficientOdd11Polynomial.coeff 0 := by
  rw [coefficientOdd11Polynomial_coeff_zero]
  have h := oddStructuralLow_endpoint_gates.1
  simpa [factorTwoIntrinsicOddPhaseLow11,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11] using h

private theorem coefficientOdd11Polynomial_coeff_one_pos :
    0 < coefficientOdd11Polynomial.coeff 1 := by
  rw [coefficientOdd11Polynomial_coeff_one]
  have h := oddStructuralLow_endpoint_gates.2.2.1
  simpa [factorTwoIntrinsicOddPhaseLow11,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11] using h

private theorem pivotCoeff_zero_eq_plus_endpoint :
    pivotCoeff 0 = factorTwoIntrinsicSixP4SchurLeading 1 := by
  calc
    pivotCoeff 0 =
        factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.eval 0 := by
      exact Polynomial.coeff_zero_eq_eval_zero _
    _ = factorTwoIntrinsicSixProjectiveP4Pivot 0 :=
      eval_factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial 0
    _ = factorTwoIntrinsicSixP4SchurLeading 1 := by
      simpa using
        (factorTwoIntrinsicSixProjectiveP4Pivot_eq_homogeneous
          0 (by norm_num))

private theorem pivotCoeff_three_eq_minus_endpoint :
    pivotCoeff 3 = factorTwoIntrinsicSixP4SchurLeading (-1) := by
  rw [factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 3 = _
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
  rw [show
      (coefficientLow00Polynomial * coefficientLow22Polynomial -
              coefficientLow02Polynomial ^ 2) *
            coefficientP4DiagonalPolynomial -
          (coefficientLow22Polynomial * coefficientCross04Polynomial *
                coefficientCross04Polynomial -
              coefficientLow02Polynomial *
                (coefficientCross04Polynomial * coefficientCross24Polynomial +
                  coefficientCross24Polynomial * coefficientCross04Polynomial) +
              coefficientLow00Polynomial * coefficientCross24Polynomial *
                coefficientCross24Polynomial) =
        coefficientLow00Polynomial * coefficientLow22Polynomial *
              coefficientP4DiagonalPolynomial -
            coefficientLow02Polynomial * coefficientLow02Polynomial *
              coefficientP4DiagonalPolynomial -
            coefficientLow22Polynomial * coefficientCross04Polynomial *
              coefficientCross04Polynomial +
            coefficientLow02Polynomial * coefficientCross04Polynomial *
              coefficientCross24Polynomial +
            coefficientLow02Polynomial * coefficientCross04Polynomial *
              coefficientCross24Polynomial -
            coefficientLow00Polynomial * coefficientCross24Polynomial *
              coefficientCross24Polynomial by ring]
  unfold coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
  simp only [coeff_add, coeff_sub,
    coeff_three_endpointAffinePolynomial_triple]
  unfold factorTwoIntrinsicP024Determinant
    ThreeByThreeRankOneSchur.symmetricDeterminant
  have hdiag : factorTwoIntrinsicSixP4Diagonal (-1) =
      factorTwoIntrinsicP4PhaseDiagonal (-1) := by rfl
  rw [hdiag]
  ring

private theorem pivotCoeff_zero_pos : 0 < pivotCoeff 0 := by
  rw [pivotCoeff_zero_eq_plus_endpoint]
  exact factorTwoIntrinsicSixP4SchurLeading_plus_pos

private theorem pivotCoeff_three_pos : 0 < pivotCoeff 3 := by
  rw [pivotCoeff_three_eq_minus_endpoint]
  exact factorTwoIntrinsicSixP4SchurLeading_minus_pos

/-- The constant coefficient is the product of the positive plus-endpoint
even determinant and the positive plus-endpoint odd diagonal. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_zero_pos :
    0 < factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 0 := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  exact mul_pos pivotCoeff_zero_pos coefficientOdd11Polynomial_coeff_zero_pos

/-- The leading coefficient is the corresponding product at the minus
endpoint. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_four_pos :
    0 < factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 4 := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  exact mul_pos pivotCoeff_three_pos coefficientOdd11Polynomial_coeff_one_pos

/-- The raw quartic belongs to the strict nonnegative coefficient cone as
soon as its three genuinely mixed coefficients are nonnegative. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFour_mem_cone_of_middle
    (h1 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 1)
    (h2 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 2)
    (h3 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 3) :
    StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial := by
  constructor
  · rw [coeff_factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial]
    exact factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_zero_pos
  · intro n
    rw [coeff_factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial]
    rcases n with _ | n
    · exact factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_zero_pos.le
    rcases n with _ | n
    · exact h1
    rcases n with _ | n
    · exact h2
    rcases n with _ | n
    · exact h3
    rcases n with _ | n
    · exact factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_four_pos.le
    simp [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]

/-- Exact minimal frontier: cone membership of the raw quartic is equivalent
to the signs of its three mixed coefficients. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFour_mem_cone_iff_middle :
    StrictNonnegativeCoefficientCone
        factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial ↔
      0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 1 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 2 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 3 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial]
      exact h.2 1
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial]
      exact h.2 2
    · rw [← coeff_factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial]
      exact h.2 3
  · rintro ⟨h1, h2, h3⟩
    exact factorTwoIntrinsicSixProjectiveRawMinorFour_mem_cone_of_middle
      h1 h2 h3

/-- The same three scalar inequalities close the second projective pivot on
the whole nonnegative half-line. -/
theorem factorTwoIntrinsicSixProjectiveBaseMinorTwoX_pos_of_middle
    (x : ℝ) (hx : 0 ≤ x)
    (h1 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 1)
    (h2 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 2)
    (h3 : 0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 3) :
    0 < factorTwoIntrinsicSixProjectiveBaseMinorTwoX x := by
  exact factorTwoIntrinsicSixProjectiveBaseMinorTwoX_pos_of_raw_cone
    x hx
    (factorTwoIntrinsicSixProjectiveRawMinorFour_mem_cone_of_middle h1 h2 h3)

/-- The seven exact convolution coefficients of the second projective
pivot.  Keeping these as named scalars makes the remaining analytic targets
small and avoids expanding the already-proved endpoint formulae repeatedly. -/
def factorTwoIntrinsicSixProjectiveBaseMinorTwoCoefficient : ℕ → ℝ
  | 0 => pivotCoeff 0 * residualOneCoeff 0
  | 1 => pivotCoeff 0 * residualOneCoeff 1 +
      pivotCoeff 1 * residualOneCoeff 0 - crossFourOneCoeff 0 ^ 2
  | 2 => pivotCoeff 0 * residualOneCoeff 2 +
      pivotCoeff 1 * residualOneCoeff 1 +
      pivotCoeff 2 * residualOneCoeff 0 -
      2 * crossFourOneCoeff 0 * crossFourOneCoeff 1
  | 3 => pivotCoeff 0 * residualOneCoeff 3 +
      pivotCoeff 1 * residualOneCoeff 2 +
      pivotCoeff 2 * residualOneCoeff 1 +
      pivotCoeff 3 * residualOneCoeff 0 -
      (crossFourOneCoeff 1 ^ 2 +
        2 * crossFourOneCoeff 0 * crossFourOneCoeff 2)
  | 4 => pivotCoeff 1 * residualOneCoeff 3 +
      pivotCoeff 2 * residualOneCoeff 2 +
      pivotCoeff 3 * residualOneCoeff 1 -
      2 * crossFourOneCoeff 1 * crossFourOneCoeff 2
  | 5 => pivotCoeff 2 * residualOneCoeff 3 +
      pivotCoeff 3 * residualOneCoeff 2 - crossFourOneCoeff 2 ^ 2
  | 6 => pivotCoeff 3 * residualOneCoeff 3
  | _ => 0

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
