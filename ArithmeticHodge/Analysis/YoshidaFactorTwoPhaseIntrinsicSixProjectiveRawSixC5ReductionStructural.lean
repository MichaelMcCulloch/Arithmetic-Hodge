import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC4Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOuterConeStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixC5ReductionStructural

noncomputable section

open Polynomial
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreePositiveMixedDiscriminant
open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC4Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientFrontierStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOddPencilStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOuterConeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# The negative-endpoint tangent reduction for the fifth raw-six coefficient

The coefficient adjacent to the negative endpoint is the first variation of
the complete determinant there.  Eliminate the negative-endpoint `P1/P3`
block from the new `P5` direction.  The resulting identity splits `C5` into
the already-positive raw-five tangent and one division-free Cauchy surplus
for the residual `P5` direction.
-/

/-! ## Negative-endpoint even block -/

def rawSixC5EvenMinus00 : ℝ := factorTwoStructuralPhaseLow00 (-1)
def rawSixC5EvenMinus02 : ℝ := factorTwoStructuralPhaseLow02 (-1)
def rawSixC5EvenMinus04 : ℝ := factorTwoIntrinsicFourP45Cross04 (-1)
def rawSixC5EvenMinus22 : ℝ := factorTwoStructuralPhaseLow22 (-1)
def rawSixC5EvenMinus24 : ℝ := factorTwoIntrinsicFourP45Cross24 (-1)
def rawSixC5EvenMinus44 : ℝ := factorTwoIntrinsicSixP4Diagonal (-1)

def rawSixC5EvenMinusDet : ℝ :=
  symmetricDeterminant
    rawSixC5EvenMinus00 rawSixC5EvenMinus02 rawSixC5EvenMinus04
    rawSixC5EvenMinus22 rawSixC5EvenMinus24 rawSixC5EvenMinus44

def rawSixC5EvenPlus00 : ℝ := factorTwoStructuralPhaseLow00 1
def rawSixC5EvenPlus02 : ℝ := factorTwoStructuralPhaseLow02 1
def rawSixC5EvenPlus04 : ℝ := factorTwoIntrinsicFourP45Cross04 1
def rawSixC5EvenPlus22 : ℝ := factorTwoStructuralPhaseLow22 1
def rawSixC5EvenPlus24 : ℝ := factorTwoIntrinsicFourP45Cross24 1
def rawSixC5EvenPlus44 : ℝ := factorTwoIntrinsicSixP4Diagonal 1

/-- Polarized adjugate form of the negative-endpoint even `P0/P2/P4`
matrix. -/
def rawSixC5EvenMinusAdjugatePair
    (u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  (rawSixC5EvenMinus22 * rawSixC5EvenMinus44 - rawSixC5EvenMinus24 ^ 2) *
      u0 * v0 +
    (rawSixC5EvenMinus04 * rawSixC5EvenMinus24 -
        rawSixC5EvenMinus02 * rawSixC5EvenMinus44) *
      (u0 * v2 + u2 * v0) +
    (rawSixC5EvenMinus02 * rawSixC5EvenMinus24 -
        rawSixC5EvenMinus04 * rawSixC5EvenMinus22) *
      (u0 * v4 + u4 * v0) +
    (rawSixC5EvenMinus00 * rawSixC5EvenMinus44 - rawSixC5EvenMinus04 ^ 2) *
      u2 * v2 +
    (rawSixC5EvenMinus02 * rawSixC5EvenMinus04 -
        rawSixC5EvenMinus00 * rawSixC5EvenMinus24) *
      (u2 * v4 + u4 * v2) +
    (rawSixC5EvenMinus00 * rawSixC5EvenMinus22 - rawSixC5EvenMinus02 ^ 2) *
      u4 * v4

private def rawSixC5EvenPlusAdjugatePair
    (u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  (rawSixC5EvenPlus22 * rawSixC5EvenPlus44 - rawSixC5EvenPlus24 ^ 2) *
      u0 * v0 +
    (rawSixC5EvenPlus04 * rawSixC5EvenPlus24 -
        rawSixC5EvenPlus02 * rawSixC5EvenPlus44) *
      (u0 * v2 + u2 * v0) +
    (rawSixC5EvenPlus02 * rawSixC5EvenPlus24 -
        rawSixC5EvenPlus04 * rawSixC5EvenPlus22) *
      (u0 * v4 + u4 * v0) +
    (rawSixC5EvenPlus00 * rawSixC5EvenPlus44 - rawSixC5EvenPlus04 ^ 2) *
      u2 * v2 +
    (rawSixC5EvenPlus02 * rawSixC5EvenPlus04 -
        rawSixC5EvenPlus00 * rawSixC5EvenPlus24) *
      (u2 * v4 + u4 * v2) +
    (rawSixC5EvenPlus00 * rawSixC5EvenPlus22 - rawSixC5EvenPlus02 ^ 2) *
      u4 * v4

private def rawSixC5EvenMixedAdjugatePair
    (u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  (rawSixC5EvenPlus22 * rawSixC5EvenMinus44 +
      rawSixC5EvenMinus22 * rawSixC5EvenPlus44 -
      2 * rawSixC5EvenPlus24 * rawSixC5EvenMinus24) * u0 * v0 +
    (rawSixC5EvenPlus04 * rawSixC5EvenMinus24 +
      rawSixC5EvenMinus04 * rawSixC5EvenPlus24 -
      rawSixC5EvenPlus02 * rawSixC5EvenMinus44 -
      rawSixC5EvenMinus02 * rawSixC5EvenPlus44) *
        (u0 * v2 + u2 * v0) +
    (rawSixC5EvenPlus02 * rawSixC5EvenMinus24 +
      rawSixC5EvenMinus02 * rawSixC5EvenPlus24 -
      rawSixC5EvenPlus04 * rawSixC5EvenMinus22 -
      rawSixC5EvenMinus04 * rawSixC5EvenPlus22) *
        (u0 * v4 + u4 * v0) +
    (rawSixC5EvenPlus00 * rawSixC5EvenMinus44 +
      rawSixC5EvenMinus00 * rawSixC5EvenPlus44 -
      2 * rawSixC5EvenPlus04 * rawSixC5EvenMinus04) * u2 * v2 +
    (rawSixC5EvenPlus02 * rawSixC5EvenMinus04 +
      rawSixC5EvenMinus02 * rawSixC5EvenPlus04 -
      rawSixC5EvenPlus00 * rawSixC5EvenMinus24 -
      rawSixC5EvenMinus00 * rawSixC5EvenPlus24) *
        (u2 * v4 + u4 * v2) +
    (rawSixC5EvenPlus00 * rawSixC5EvenMinus22 +
      rawSixC5EvenMinus00 * rawSixC5EvenPlus22 -
      2 * rawSixC5EvenPlus02 * rawSixC5EvenMinus02) * u4 * v4

/-! ## Odd `P1/P3` elimination data -/

def rawSixC5OddMinus11 : ℝ := factorTwoIntrinsicOddPhaseLow11 (-1)
def rawSixC5OddMinus13 : ℝ := factorTwoIntrinsicOddPhaseLow13 (-1)
def rawSixC5OddMinus33 : ℝ := factorTwoIntrinsicOddPhaseLow33 (-1)

def rawSixC5OddPlus11 : ℝ := factorTwoIntrinsicOddPhaseLow11 1
def rawSixC5OddPlus13 : ℝ := factorTwoIntrinsicOddPhaseLow13 1
def rawSixC5OddPlus33 : ℝ := factorTwoIntrinsicOddPhaseLow33 1

def rawSixC5OddMinus15 : ℝ := factorTwoIntrinsicFourP45Cross15 (-1)
def rawSixC5OddMinus35 : ℝ := factorTwoIntrinsicFourP45Cross35 (-1)
def rawSixC5OddPlus15 : ℝ := factorTwoIntrinsicFourP45Cross15 1
def rawSixC5OddPlus35 : ℝ := factorTwoIntrinsicFourP45Cross35 1
def rawSixC5OddMinus55 : ℝ := factorTwoIntrinsicSixP5Diagonal (-1)
def rawSixC5OddPlus55 : ℝ := factorTwoIntrinsicSixP5Diagonal 1

/-- Determinant of the negative-endpoint `P1/P3` block. -/
def rawSixC5OddMinusDelta : ℝ :=
  rawSixC5OddMinus11 * rawSixC5OddMinus33 - rawSixC5OddMinus13 ^ 2

def rawSixC5OddMinusDet : ℝ :=
  symmetricDeterminant
    rawSixC5OddMinus11 rawSixC5OddMinus13 rawSixC5OddMinus15
    rawSixC5OddMinus33 rawSixC5OddMinus35 rawSixC5OddMinus55

/-- Coefficient linear in the plus endpoint in the full odd determinant
viewed from the negative endpoint. -/
def rawSixC5OddMixedMinusPlus : ℝ :=
  mixedDeterminantOne
    rawSixC5OddMinus11 rawSixC5OddMinus13 rawSixC5OddMinus15
    rawSixC5OddMinus33 rawSixC5OddMinus35 rawSixC5OddMinus55
    rawSixC5OddPlus11 rawSixC5OddPlus13 rawSixC5OddPlus15
    rawSixC5OddPlus33 rawSixC5OddPlus35 rawSixC5OddPlus55

def rawSixC5OddLowMixedMinusPlus : ℝ :=
  rawSixC5OddPlus11 * rawSixC5OddMinus33 +
    rawSixC5OddMinus11 * rawSixC5OddPlus33 -
    2 * rawSixC5OddPlus13 * rawSixC5OddMinus13

/-- The numerator `adj(B_minus) c_minus`. -/
def rawSixC5OddProjection1 : ℝ :=
  rawSixC5OddMinus33 * rawSixC5OddMinus15 -
    rawSixC5OddMinus13 * rawSixC5OddMinus35

def rawSixC5OddProjection3 : ℝ :=
  rawSixC5OddMinus11 * rawSixC5OddMinus35 -
    rawSixC5OddMinus13 * rawSixC5OddMinus15

/-! ## Endpoint alternating adjugate contractions -/

def rawSixC5AlternatingPair11 : ℝ :=
  rawSixC5EvenMinusAdjugatePair
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41

def rawSixC5AlternatingPair13 : ℝ :=
  rawSixC5EvenMinusAdjugatePair
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43

def rawSixC5AlternatingPair15 : ℝ :=
  rawSixC5EvenMinusAdjugatePair
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41
    factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
    factorTwoIntrinsicSixAlternating45

def rawSixC5AlternatingPair33 : ℝ :=
  rawSixC5EvenMinusAdjugatePair
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43

def rawSixC5AlternatingPair35 : ℝ :=
  rawSixC5EvenMinusAdjugatePair
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43
    factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
    factorTwoIntrinsicSixAlternating45

def rawSixC5AlternatingPair55 : ℝ :=
  rawSixC5EvenMinusAdjugatePair
    factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
    factorTwoIntrinsicSixAlternating45
    factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
    factorTwoIntrinsicSixAlternating45

def rawSixC5RawFiveEndpointCoupling : ℝ :=
  rawSixC5OddMinus33 * rawSixC5AlternatingPair11 -
    2 * rawSixC5OddMinus13 * rawSixC5AlternatingPair13 +
    rawSixC5OddMinus11 * rawSixC5AlternatingPair33

def rawSixC5RawSixEndpointCoupling : ℝ :=
  (rawSixC5OddMinus33 * rawSixC5OddMinus55 - rawSixC5OddMinus35 ^ 2) *
      rawSixC5AlternatingPair11 +
    2 * (rawSixC5OddMinus15 * rawSixC5OddMinus35 -
      rawSixC5OddMinus13 * rawSixC5OddMinus55) *
      rawSixC5AlternatingPair13 +
    2 * (rawSixC5OddMinus13 * rawSixC5OddMinus35 -
      rawSixC5OddMinus15 * rawSixC5OddMinus33) *
      rawSixC5AlternatingPair15 +
    (rawSixC5OddMinus11 * rawSixC5OddMinus55 - rawSixC5OddMinus15 ^ 2) *
      rawSixC5AlternatingPair33 +
    2 * (rawSixC5OddMinus13 * rawSixC5OddMinus15 -
      rawSixC5OddMinus11 * rawSixC5OddMinus35) *
      rawSixC5AlternatingPair35 +
    rawSixC5OddMinusDelta * rawSixC5AlternatingPair55

/-- `Delta^2` times the plus-endpoint energy of the odd residual obtained by
projecting `P5` against `P1/P3` at the negative endpoint. -/
def rawSixC5ResidualOddPlusNumerator : ℝ :=
  rawSixC5OddMinusDelta ^ 2 * rawSixC5OddPlus55 -
    2 * rawSixC5OddMinusDelta *
      (rawSixC5OddPlus15 * rawSixC5OddProjection1 +
        rawSixC5OddPlus35 * rawSixC5OddProjection3) +
    rawSixC5OddPlus11 * rawSixC5OddProjection1 ^ 2 +
    2 * rawSixC5OddPlus13 *
      rawSixC5OddProjection1 * rawSixC5OddProjection3 +
    rawSixC5OddPlus33 * rawSixC5OddProjection3 ^ 2

/-! ## Residual alternating column -/

def rawSixC5ResidualAlternating0 : ℝ :=
  rawSixC5OddMinusDelta * factorTwoIntrinsicFourP45Cross05 -
    factorTwoIntrinsicAlternating01 * rawSixC5OddProjection1 -
    factorTwoIntrinsicAlternating03 * rawSixC5OddProjection3

def rawSixC5ResidualAlternating2 : ℝ :=
  rawSixC5OddMinusDelta * factorTwoIntrinsicFourP45Cross25 -
    factorTwoIntrinsicAlternating21 * rawSixC5OddProjection1 -
    factorTwoIntrinsicAlternating23 * rawSixC5OddProjection3

def rawSixC5ResidualAlternating4 : ℝ :=
  rawSixC5OddMinusDelta * factorTwoIntrinsicSixAlternating45 -
    factorTwoIntrinsicFourP45Cross41 * rawSixC5OddProjection1 -
    factorTwoIntrinsicFourP45Cross43 * rawSixC5OddProjection3

def rawSixC5ResidualEvenAdjugateEnergy : ℝ :=
  rawSixC5EvenMinusAdjugatePair
    rawSixC5ResidualAlternating0 rawSixC5ResidualAlternating2
    rawSixC5ResidualAlternating4
    rawSixC5ResidualAlternating0 rawSixC5ResidualAlternating2
    rawSixC5ResidualAlternating4

/-- The sole new analytic gate after bordering the proved raw-five tangent. -/
def RawSixC5ResidualTangentGate : Prop :=
  rawSixC5ResidualEvenAdjugateEnergy ≤
    rawSixC5EvenMinusDet * rawSixC5ResidualOddPlusNumerator

/-! ## Exact endpoint coefficient identifications -/

private theorem coefficientRawAdjugatePairPolynomial_tangent_expansion
    (u0 u2 u4 v0 v2 v4 : ℝ) :
    coefficientRawAdjugatePairPolynomial u0 u2 u4 v0 v2 v4 =
      C (rawSixC5EvenPlusAdjugatePair u0 u2 u4 v0 v2 v4) +
        C (rawSixC5EvenMixedAdjugatePair u0 u2 u4 v0 v2 v4) * X +
        C (rawSixC5EvenMinusAdjugatePair u0 u2 u4 v0 v2 v4) * X ^ 2 := by
  unfold coefficientRawAdjugatePairPolynomial
    coefficientLowDetPolynomial coefficientLow00Polynomial
    coefficientLow02Polynomial coefficientLow22Polynomial
    coefficientCross04Polynomial coefficientCross24Polynomial
    coefficientP4DiagonalPolynomial endpointAffinePolynomial
    rawSixC5EvenPlusAdjugatePair rawSixC5EvenMixedAdjugatePair
    rawSixC5EvenMinusAdjugatePair rawSixC5EvenPlus00 rawSixC5EvenPlus02
    rawSixC5EvenPlus04 rawSixC5EvenPlus22 rawSixC5EvenPlus24
    rawSixC5EvenPlus44 rawSixC5EvenMinus00
    rawSixC5EvenMinus02 rawSixC5EvenMinus04 rawSixC5EvenMinus22
    rawSixC5EvenMinus24 rawSixC5EvenMinus44
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

private theorem coefficientRawAdjugatePairPolynomial_coeff_two
    (u0 u2 u4 v0 v2 v4 : ℝ) :
    (coefficientRawAdjugatePairPolynomial
      u0 u2 u4 v0 v2 v4).coeff 2 =
      rawSixC5EvenMinusAdjugatePair u0 u2 u4 v0 v2 v4 := by
  rw [coefficientRawAdjugatePairPolynomial_tangent_expansion]
  simp

private theorem coeff_three_affine_mul_quadratic
    (p m c0 c1 c2 : ℝ) :
    ((C p + C m * X) *
      (C c0 + C c1 * X + C c2 * X ^ 2)).coeff 3 = m * c2 := by
  have hpoly :
      (C p + C m * X) * (C c0 + C c1 * X + C c2 * X ^ 2) =
        C (p * c0) + C (p * c1 + m * c0) * X +
          C (p * c2 + m * c1) * X ^ 2 + C (m * c2) * X ^ 3 := by
    simp only [map_add, map_mul]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private theorem coeff_three_endpointAffine_mul_rawAdjugate
    (p m u0 u2 u4 v0 v2 v4 : ℝ) :
    (endpointAffinePolynomial p m *
      coefficientRawAdjugatePairPolynomial
        u0 u2 u4 v0 v2 v4).coeff 3 =
      m * rawSixC5EvenMinusAdjugatePair u0 u2 u4 v0 v2 v4 := by
  rw [coefficientRawAdjugatePairPolynomial_tangent_expansion]
  unfold endpointAffinePolynomial
  exact coeff_three_affine_mul_quadratic _ _ _ _ _

private theorem pivotCoeff_three_eq_rawSixC5EvenMinusDet :
    pivotCoeff 3 = rawSixC5EvenMinusDet := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 3 = _
  have hpoly :
      factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial =
        C (symmetricDeterminant
          rawSixC5EvenPlus00 rawSixC5EvenPlus02 rawSixC5EvenPlus04
          rawSixC5EvenPlus22 rawSixC5EvenPlus24 rawSixC5EvenPlus44) +
        C (mixedDeterminantOne
          rawSixC5EvenPlus00 rawSixC5EvenPlus02 rawSixC5EvenPlus04
          rawSixC5EvenPlus22 rawSixC5EvenPlus24 rawSixC5EvenPlus44
          rawSixC5EvenMinus00 rawSixC5EvenMinus02 rawSixC5EvenMinus04
          rawSixC5EvenMinus22 rawSixC5EvenMinus24 rawSixC5EvenMinus44) * X +
        C (mixedDeterminantOne
          rawSixC5EvenMinus00 rawSixC5EvenMinus02 rawSixC5EvenMinus04
          rawSixC5EvenMinus22 rawSixC5EvenMinus24 rawSixC5EvenMinus44
          rawSixC5EvenPlus00 rawSixC5EvenPlus02 rawSixC5EvenPlus04
          rawSixC5EvenPlus22 rawSixC5EvenPlus24 rawSixC5EvenPlus44) * X ^ 2 +
        C rawSixC5EvenMinusDet * X ^ 3 := by
    unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
      coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
      coefficientLow00Polynomial coefficientLow02Polynomial
      coefficientLow22Polynomial coefficientCross04Polynomial
      coefficientCross24Polynomial coefficientP4DiagonalPolynomial
      endpointAffinePolynomial rawSixC5EvenMinusDet
      rawSixC5EvenPlus00 rawSixC5EvenPlus02 rawSixC5EvenPlus04
      rawSixC5EvenPlus22 rawSixC5EvenPlus24 rawSixC5EvenPlus44
      rawSixC5EvenMinus00 rawSixC5EvenMinus02 rawSixC5EvenMinus04
      rawSixC5EvenMinus22 rawSixC5EvenMinus24 rawSixC5EvenMinus44
      mixedDeterminantOne symmetricDeterminant
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private theorem rawFiveOddMinorCoeff_two_eq_rawSixC5Delta :
    rawFiveOddMinorCoeff 2 = rawSixC5OddMinusDelta := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 2 = _
  have hpoly :
      factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial =
        C (rawSixC5OddPlus11 * rawSixC5OddPlus33 - rawSixC5OddPlus13 ^ 2) +
          C rawSixC5OddLowMixedMinusPlus * X +
          C rawSixC5OddMinusDelta * X ^ 2 := by
    unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
      coefficientOdd11Polynomial coefficientOdd13Polynomial
      coefficientOdd33Polynomial endpointAffinePolynomial
      rawSixC5OddLowMixedMinusPlus rawSixC5OddMinusDelta
      rawSixC5OddPlus11 rawSixC5OddPlus13 rawSixC5OddPlus33
      rawSixC5OddMinus11 rawSixC5OddMinus13 rawSixC5OddMinus33
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private theorem rawFiveOddMinorCoeff_one_eq_rawSixC5Mixed :
    rawFiveOddMinorCoeff 1 = rawSixC5OddLowMixedMinusPlus := by
  rw [rawFiveOddMinorCoeff_one_eq]
  unfold rawSixC5OddLowMixedMinusPlus
    rawSixC5OddPlus11 rawSixC5OddPlus13 rawSixC5OddPlus33
    rawSixC5OddMinus11 rawSixC5OddMinus13 rawSixC5OddMinus33
  ring

private theorem rawFiveCouplingCoeff_three_eq_rawSixC5Endpoint :
    rawFiveCouplingCoeff 3 = rawSixC5RawFiveEndpointCoupling := by
  change
    factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial.coeff 3 = _
  let A11 := rawSixC5EvenPlusAdjugatePair
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41
  let A13 := rawSixC5EvenPlusAdjugatePair
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43
  let A33 := rawSixC5EvenPlusAdjugatePair
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43
  let B11 := rawSixC5EvenMixedAdjugatePair
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41
  let B13 := rawSixC5EvenMixedAdjugatePair
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicFourP45Cross41
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43
  let B33 := rawSixC5EvenMixedAdjugatePair
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross43
  have hpoly :
      factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial =
        C (rawSixC5OddPlus33 * A11 - 2 * rawSixC5OddPlus13 * A13 +
          rawSixC5OddPlus11 * A33) +
        C (rawSixC5OddPlus33 * B11 + rawSixC5OddMinus33 * A11 -
          2 * (rawSixC5OddPlus13 * B13 + rawSixC5OddMinus13 * A13) +
          rawSixC5OddPlus11 * B33 + rawSixC5OddMinus11 * A33) * X +
        C (rawSixC5OddPlus33 * rawSixC5AlternatingPair11 +
          rawSixC5OddMinus33 * B11 -
          2 * (rawSixC5OddPlus13 * rawSixC5AlternatingPair13 +
            rawSixC5OddMinus13 * B13) +
          rawSixC5OddPlus11 * rawSixC5AlternatingPair33 +
          rawSixC5OddMinus11 * B33) * X ^ 2 +
        C rawSixC5RawFiveEndpointCoupling * X ^ 3 := by
    unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial
    rw [coefficientRawAdjugatePairPolynomial_tangent_expansion,
      coefficientRawAdjugatePairPolynomial_tangent_expansion,
      coefficientRawAdjugatePairPolynomial_tangent_expansion]
    unfold coefficientOdd11Polynomial coefficientOdd13Polynomial
      coefficientOdd33Polynomial endpointAffinePolynomial
    dsimp only [A11, A13, A33, B11, B13, B33]
    unfold rawSixC5RawFiveEndpointCoupling
      rawSixC5AlternatingPair11 rawSixC5AlternatingPair13
      rawSixC5AlternatingPair33 rawSixC5OddPlus11 rawSixC5OddPlus13
      rawSixC5OddPlus33 rawSixC5OddMinus11 rawSixC5OddMinus13
      rawSixC5OddMinus33
    simp only [map_add, map_sub, map_mul, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private theorem rawSixOddDetCoeff_three_eq_rawSixC5Det :
    rawSixOddDetCoeff 3 = rawSixC5OddMinusDet := by
  rw [rawSixOddDetCoeff_three_eq]
  simpa [rawSixOddMinusMatrix, rawSixC5OddMinusDet,
    rawSixC5OddMinus11, rawSixC5OddMinus13, rawSixC5OddMinus15,
    rawSixC5OddMinus33, rawSixC5OddMinus35, rawSixC5OddMinus55] using
      rawSixOddEndpointMatrix_det_eq_symmetricDeterminant (-1)

private theorem rawSixOddDetCoeff_two_eq_rawSixC5Mixed :
    rawSixOddDetCoeff 2 = rawSixC5OddMixedMinusPlus := by
  rw [rawSixOddDetCoeff_two_eq]
  unfold rawSixOddMinusMatrix rawSixOddPlusMatrix rawSixOddEndpointMatrix
    rawSixC5OddMixedMinusPlus rawSixC5OddMinus11 rawSixC5OddMinus13
    rawSixC5OddMinus15 rawSixC5OddMinus33 rawSixC5OddMinus35
    rawSixC5OddMinus55 rawSixC5OddPlus11 rawSixC5OddPlus13
    rawSixC5OddPlus15 rawSixC5OddPlus33 rawSixC5OddPlus35
    rawSixC5OddPlus55
  exact matrixMixedDeterminantOne_symmetricMatrix3 _ _ _ _ _ _ _ _ _ _ _ _

private theorem coeff_four_quadratic_mul_quadratic
    (a0 a1 a2 b0 b1 b2 : ℝ) :
    ((C a0 + C a1 * X + C a2 * X ^ 2) *
      (C b0 + C b1 * X + C b2 * X ^ 2)).coeff 4 = a2 * b2 := by
  have hpoly :
      (C a0 + C a1 * X + C a2 * X ^ 2) *
          (C b0 + C b1 * X + C b2 * X ^ 2) =
        C (a0 * b0) + C (a0 * b1 + a1 * b0) * X +
          C (a0 * b2 + a1 * b1 + a2 * b0) * X ^ 2 +
          C (a1 * b2 + a2 * b1) * X ^ 3 + C (a2 * b2) * X ^ 4 := by
    simp only [map_add, map_mul]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private theorem coeff_four_scaled_affineDet_mul_rawAdjugate
    (k p1 m1 p2 m2 p3 m3 p4 m4 u0 u2 u4 v0 v2 v4 : ℝ) :
    (C k *
      (endpointAffinePolynomial p1 m1 * endpointAffinePolynomial p2 m2 -
        endpointAffinePolynomial p3 m3 * endpointAffinePolynomial p4 m4) *
      coefficientRawAdjugatePairPolynomial
        u0 u2 u4 v0 v2 v4).coeff 4 =
      k * (m1 * m2 - m3 * m4) *
        rawSixC5EvenMinusAdjugatePair u0 u2 u4 v0 v2 v4 := by
  rw [coefficientRawAdjugatePairPolynomial_tangent_expansion]
  have hquad :
      C k *
          (endpointAffinePolynomial p1 m1 * endpointAffinePolynomial p2 m2 -
            endpointAffinePolynomial p3 m3 * endpointAffinePolynomial p4 m4) =
        C (k * (p1 * p2 - p3 * p4)) +
          C (k * (p1 * m2 + m1 * p2 - p3 * m4 - m3 * p4)) * X +
          C (k * (m1 * m2 - m3 * m4)) * X ^ 2 := by
    unfold endpointAffinePolynomial
    simp only [map_add, map_sub, map_mul]
    ring
  rw [hquad]
  exact coeff_four_quadratic_mul_quadratic _ _ _ _ _ _

private theorem rawSixAdjugatePair_zero_zero :
    coefficientRawSixAdjugatePairPolynomial 0 0 =
      coefficientRawAdjugatePairPolynomial
        factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41
        factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41 := by
  rfl

private theorem rawSixAdjugatePair_zero_one :
    coefficientRawSixAdjugatePairPolynomial 0 1 =
      coefficientRawAdjugatePairPolynomial
        factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41
        factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43 := by
  rfl

private theorem rawSixAdjugatePair_zero_two :
    coefficientRawSixAdjugatePairPolynomial 0 2 =
      coefficientRawAdjugatePairPolynomial
        factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41
        factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
        factorTwoIntrinsicSixAlternating45 := by
  rfl

private theorem rawSixAdjugatePair_one_one :
    coefficientRawSixAdjugatePairPolynomial 1 1 =
      coefficientRawAdjugatePairPolynomial
        factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43
        factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43 := by
  rfl

private theorem rawSixAdjugatePair_one_two :
    coefficientRawSixAdjugatePairPolynomial 1 2 =
      coefficientRawAdjugatePairPolynomial
        factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43
        factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
        factorTwoIntrinsicSixAlternating45 := by
  rfl

private theorem rawSixAdjugatePair_two_two :
    coefficientRawSixAdjugatePairPolynomial 2 2 =
      coefficientRawAdjugatePairPolynomial
        factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
        factorTwoIntrinsicSixAlternating45
        factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
        factorTwoIntrinsicSixAlternating45 := by
  rfl

private theorem rawSixMixedOneCoeff_four_eq_rawSixC5Endpoint :
    rawSixMixedOneCoeff 4 = rawSixC5RawSixEndpointCoupling := by
  change
    factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial.coeff 4 = _
  have h00 :
      ((coefficientOdd33Polynomial * coefficientP5DiagonalPolynomial -
          coefficientOdd35Polynomial ^ 2) *
        coefficientRawSixAdjugatePairPolynomial 0 0).coeff 4 =
        (rawSixC5OddMinus33 * rawSixC5OddMinus55 -
          rawSixC5OddMinus35 ^ 2) * rawSixC5AlternatingPair11 := by
    rw [rawSixAdjugatePair_zero_zero]
    simpa [coefficientOdd33Polynomial, coefficientOdd35Polynomial,
      coefficientP5DiagonalPolynomial, pow_two,
      rawSixC5OddMinus33, rawSixC5OddMinus35, rawSixC5OddMinus55,
      rawSixC5AlternatingPair11] using
      (coeff_four_scaled_affineDet_mul_rawAdjugate
        1
        (factorTwoIntrinsicOddPhaseLow33 1)
        (factorTwoIntrinsicOddPhaseLow33 (-1))
        (factorTwoIntrinsicSixP5Diagonal 1)
        (factorTwoIntrinsicSixP5Diagonal (-1))
        (factorTwoIntrinsicFourP45Cross35 1)
        (factorTwoIntrinsicFourP45Cross35 (-1))
        (factorTwoIntrinsicFourP45Cross35 1)
        (factorTwoIntrinsicFourP45Cross35 (-1))
        factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41
        factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41)
  have h01 :
      (2 * (coefficientOdd15Polynomial * coefficientOdd35Polynomial -
          coefficientOdd13Polynomial * coefficientP5DiagonalPolynomial) *
        coefficientRawSixAdjugatePairPolynomial 0 1).coeff 4 =
        2 * (rawSixC5OddMinus15 * rawSixC5OddMinus35 -
          rawSixC5OddMinus13 * rawSixC5OddMinus55) *
          rawSixC5AlternatingPair13 := by
    rw [rawSixAdjugatePair_zero_one]
    simpa [coefficientOdd15Polynomial, coefficientOdd35Polynomial,
      coefficientOdd13Polynomial, coefficientP5DiagonalPolynomial,
      rawSixC5OddMinus15, rawSixC5OddMinus35, rawSixC5OddMinus13,
      rawSixC5OddMinus55, rawSixC5AlternatingPair13] using
      (coeff_four_scaled_affineDet_mul_rawAdjugate
        2
        (factorTwoIntrinsicFourP45Cross15 1)
        (factorTwoIntrinsicFourP45Cross15 (-1))
        (factorTwoIntrinsicFourP45Cross35 1)
        (factorTwoIntrinsicFourP45Cross35 (-1))
        (factorTwoIntrinsicOddPhaseLow13 1)
        (factorTwoIntrinsicOddPhaseLow13 (-1))
        (factorTwoIntrinsicSixP5Diagonal 1)
        (factorTwoIntrinsicSixP5Diagonal (-1))
        factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41
        factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43)
  have h02 :
      (2 * (coefficientOdd13Polynomial * coefficientOdd35Polynomial -
          coefficientOdd15Polynomial * coefficientOdd33Polynomial) *
        coefficientRawSixAdjugatePairPolynomial 0 2).coeff 4 =
        2 * (rawSixC5OddMinus13 * rawSixC5OddMinus35 -
          rawSixC5OddMinus15 * rawSixC5OddMinus33) *
          rawSixC5AlternatingPair15 := by
    rw [rawSixAdjugatePair_zero_two]
    simpa [coefficientOdd13Polynomial, coefficientOdd35Polynomial,
      coefficientOdd15Polynomial, coefficientOdd33Polynomial,
      rawSixC5OddMinus13, rawSixC5OddMinus35, rawSixC5OddMinus15,
      rawSixC5OddMinus33, rawSixC5AlternatingPair15] using
      (coeff_four_scaled_affineDet_mul_rawAdjugate
        2
        (factorTwoIntrinsicOddPhaseLow13 1)
        (factorTwoIntrinsicOddPhaseLow13 (-1))
        (factorTwoIntrinsicFourP45Cross35 1)
        (factorTwoIntrinsicFourP45Cross35 (-1))
        (factorTwoIntrinsicFourP45Cross15 1)
        (factorTwoIntrinsicFourP45Cross15 (-1))
        (factorTwoIntrinsicOddPhaseLow33 1)
        (factorTwoIntrinsicOddPhaseLow33 (-1))
        factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41
        factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
        factorTwoIntrinsicSixAlternating45)
  have h11 :
      ((coefficientOdd11Polynomial * coefficientP5DiagonalPolynomial -
          coefficientOdd15Polynomial ^ 2) *
        coefficientRawSixAdjugatePairPolynomial 1 1).coeff 4 =
        (rawSixC5OddMinus11 * rawSixC5OddMinus55 -
          rawSixC5OddMinus15 ^ 2) * rawSixC5AlternatingPair33 := by
    rw [rawSixAdjugatePair_one_one]
    simpa [coefficientOdd11Polynomial, coefficientOdd15Polynomial,
      coefficientP5DiagonalPolynomial, pow_two,
      rawSixC5OddMinus11, rawSixC5OddMinus15, rawSixC5OddMinus55,
      rawSixC5AlternatingPair33] using
      (coeff_four_scaled_affineDet_mul_rawAdjugate
        1
        (factorTwoIntrinsicOddPhaseLow11 1)
        (factorTwoIntrinsicOddPhaseLow11 (-1))
        (factorTwoIntrinsicSixP5Diagonal 1)
        (factorTwoIntrinsicSixP5Diagonal (-1))
        (factorTwoIntrinsicFourP45Cross15 1)
        (factorTwoIntrinsicFourP45Cross15 (-1))
        (factorTwoIntrinsicFourP45Cross15 1)
        (factorTwoIntrinsicFourP45Cross15 (-1))
        factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43
        factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43)
  have h12 :
      (2 * (coefficientOdd13Polynomial * coefficientOdd15Polynomial -
          coefficientOdd11Polynomial * coefficientOdd35Polynomial) *
        coefficientRawSixAdjugatePairPolynomial 1 2).coeff 4 =
        2 * (rawSixC5OddMinus13 * rawSixC5OddMinus15 -
          rawSixC5OddMinus11 * rawSixC5OddMinus35) *
          rawSixC5AlternatingPair35 := by
    rw [rawSixAdjugatePair_one_two]
    simpa [coefficientOdd13Polynomial, coefficientOdd15Polynomial,
      coefficientOdd11Polynomial, coefficientOdd35Polynomial,
      rawSixC5OddMinus13, rawSixC5OddMinus15, rawSixC5OddMinus11,
      rawSixC5OddMinus35, rawSixC5AlternatingPair35] using
      (coeff_four_scaled_affineDet_mul_rawAdjugate
        2
        (factorTwoIntrinsicOddPhaseLow13 1)
        (factorTwoIntrinsicOddPhaseLow13 (-1))
        (factorTwoIntrinsicFourP45Cross15 1)
        (factorTwoIntrinsicFourP45Cross15 (-1))
        (factorTwoIntrinsicOddPhaseLow11 1)
        (factorTwoIntrinsicOddPhaseLow11 (-1))
        (factorTwoIntrinsicFourP45Cross35 1)
        (factorTwoIntrinsicFourP45Cross35 (-1))
        factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43
        factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
        factorTwoIntrinsicSixAlternating45)
  have h22 :
      ((coefficientOdd11Polynomial * coefficientOdd33Polynomial -
          coefficientOdd13Polynomial ^ 2) *
        coefficientRawSixAdjugatePairPolynomial 2 2).coeff 4 =
        rawSixC5OddMinusDelta * rawSixC5AlternatingPair55 := by
    rw [rawSixAdjugatePair_two_two]
    simpa [coefficientOdd11Polynomial, coefficientOdd33Polynomial,
      coefficientOdd13Polynomial, pow_two, rawSixC5OddMinusDelta,
      rawSixC5OddMinus11, rawSixC5OddMinus13, rawSixC5OddMinus33,
      rawSixC5AlternatingPair55] using
      (coeff_four_scaled_affineDet_mul_rawAdjugate
        1
        (factorTwoIntrinsicOddPhaseLow11 1)
        (factorTwoIntrinsicOddPhaseLow11 (-1))
        (factorTwoIntrinsicOddPhaseLow33 1)
        (factorTwoIntrinsicOddPhaseLow33 (-1))
        (factorTwoIntrinsicOddPhaseLow13 1)
        (factorTwoIntrinsicOddPhaseLow13 (-1))
        (factorTwoIntrinsicOddPhaseLow13 1)
        (factorTwoIntrinsicOddPhaseLow13 (-1))
        factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
        factorTwoIntrinsicSixAlternating45
        factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
        factorTwoIntrinsicSixAlternating45)
  unfold factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial
  simp only [coeff_add, h00, h01, h02, h11, h12, h22]
  unfold rawSixC5RawSixEndpointCoupling
  ring

/-! ## The bordering identity and sign reduction -/

private theorem rawSixC5OddMixed_bordering :
    rawSixC5OddMinusDelta * rawSixC5OddMixedMinusPlus -
        rawSixC5OddMinusDet * rawSixC5OddLowMixedMinusPlus =
      rawSixC5ResidualOddPlusNumerator := by
  unfold rawSixC5OddMixedMinusPlus rawSixC5OddMinusDet
    rawSixC5OddLowMixedMinusPlus
    rawSixC5ResidualOddPlusNumerator rawSixC5OddProjection1
    rawSixC5OddProjection3 rawSixC5OddMinusDelta
    mixedDeterminantOne symmetricDeterminant
  ring

private theorem rawSixC5EvenMinusAdjugatePair_three_column_residual
    (delta y1 y3 a0 a2 a4 u0 u2 u4 v0 v2 v4 : ℝ) :
    rawSixC5EvenMinusAdjugatePair
        (delta * a0 - u0 * y1 - v0 * y3)
        (delta * a2 - u2 * y1 - v2 * y3)
        (delta * a4 - u4 * y1 - v4 * y3)
        (delta * a0 - u0 * y1 - v0 * y3)
        (delta * a2 - u2 * y1 - v2 * y3)
        (delta * a4 - u4 * y1 - v4 * y3) =
      delta ^ 2 * rawSixC5EvenMinusAdjugatePair
          a0 a2 a4 a0 a2 a4 -
        2 * delta * y1 * rawSixC5EvenMinusAdjugatePair
          u0 u2 u4 a0 a2 a4 -
        2 * delta * y3 * rawSixC5EvenMinusAdjugatePair
          v0 v2 v4 a0 a2 a4 +
        y1 ^ 2 * rawSixC5EvenMinusAdjugatePair
          u0 u2 u4 u0 u2 u4 +
        2 * y1 * y3 * rawSixC5EvenMinusAdjugatePair
          u0 u2 u4 v0 v2 v4 +
        y3 ^ 2 * rawSixC5EvenMinusAdjugatePair
          v0 v2 v4 v0 v2 v4 := by
  unfold rawSixC5EvenMinusAdjugatePair
  ring

private theorem rawSixC5ResidualEvenAdjugateEnergy_expansion :
    rawSixC5ResidualEvenAdjugateEnergy =
      rawSixC5OddMinusDelta ^ 2 * rawSixC5AlternatingPair55 -
        2 * rawSixC5OddMinusDelta * rawSixC5OddProjection1 *
          rawSixC5AlternatingPair15 -
        2 * rawSixC5OddMinusDelta * rawSixC5OddProjection3 *
          rawSixC5AlternatingPair35 +
        rawSixC5OddProjection1 ^ 2 * rawSixC5AlternatingPair11 +
        2 * rawSixC5OddProjection1 * rawSixC5OddProjection3 *
          rawSixC5AlternatingPair13 +
        rawSixC5OddProjection3 ^ 2 * rawSixC5AlternatingPair33 := by
  simpa only [rawSixC5ResidualEvenAdjugateEnergy,
    rawSixC5ResidualAlternating0, rawSixC5ResidualAlternating2,
    rawSixC5ResidualAlternating4, rawSixC5AlternatingPair11,
    rawSixC5AlternatingPair13, rawSixC5AlternatingPair15,
    rawSixC5AlternatingPair33, rawSixC5AlternatingPair35,
    rawSixC5AlternatingPair55] using
      rawSixC5EvenMinusAdjugatePair_three_column_residual
        rawSixC5OddMinusDelta rawSixC5OddProjection1
        rawSixC5OddProjection3
        factorTwoIntrinsicFourP45Cross05
        factorTwoIntrinsicFourP45Cross25
        factorTwoIntrinsicSixAlternating45
        factorTwoIntrinsicAlternating01
        factorTwoIntrinsicAlternating21
        factorTwoIntrinsicFourP45Cross41
        factorTwoIntrinsicAlternating03
        factorTwoIntrinsicAlternating23
        factorTwoIntrinsicFourP45Cross43

private theorem rawSixC5Alternating_bordering :
    rawSixC5OddMinusDelta * rawSixC5RawSixEndpointCoupling -
        rawSixC5OddMinusDet * rawSixC5RawFiveEndpointCoupling =
      rawSixC5ResidualEvenAdjugateEnergy := by
  rw [rawSixC5ResidualEvenAdjugateEnergy_expansion]
  unfold rawSixC5OddMinusDet rawSixC5RawSixEndpointCoupling
    rawSixC5RawFiveEndpointCoupling rawSixC5OddProjection1
    rawSixC5OddProjection3 rawSixC5OddMinusDelta symmetricDeterminant
  ring

/-- Division-free Schur bordering at the negative endpoint.  The first term
is the already-proved five-mode tangent; the second line is exactly the
residual `P5` tangent Cauchy surplus. -/
theorem factorTwoIntrinsicSixProjectiveRawSixCoefficient_five_bordering :
    rawSixC5OddMinusDelta *
        factorTwoIntrinsicSixProjectiveRawSixCoefficient 5 =
      rawSixC5OddMinusDet *
          factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4 +
        rawSixC5EvenMinusDet * rawSixC5ResidualOddPlusNumerator -
        rawSixC5ResidualEvenAdjugateEnergy := by
  simp only [factorTwoIntrinsicSixProjectiveRawSixCoefficient,
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rw [pivotCoeff_three_eq_rawSixC5EvenMinusDet,
    rawFiveOddMinorCoeff_two_eq_rawSixC5Delta,
    rawFiveOddMinorCoeff_one_eq_rawSixC5Mixed,
    rawFiveCouplingCoeff_three_eq_rawSixC5Endpoint,
    rawSixOddDetCoeff_three_eq_rawSixC5Det,
    rawSixOddDetCoeff_two_eq_rawSixC5Mixed,
    rawSixMixedOneCoeff_four_eq_rawSixC5Endpoint]
  calc
    rawSixC5OddMinusDelta *
          (pivotCoeff 2 * rawSixC5OddMinusDet +
            rawSixC5EvenMinusDet * rawSixC5OddMixedMinusPlus -
            rawSixC5RawSixEndpointCoupling) =
        rawSixC5OddMinusDet *
            (pivotCoeff 2 * rawSixC5OddMinusDelta +
              rawSixC5EvenMinusDet * rawSixC5OddLowMixedMinusPlus -
              rawSixC5RawFiveEndpointCoupling) +
          rawSixC5EvenMinusDet *
            (rawSixC5OddMinusDelta * rawSixC5OddMixedMinusPlus -
              rawSixC5OddMinusDet * rawSixC5OddLowMixedMinusPlus) -
          (rawSixC5OddMinusDelta * rawSixC5RawSixEndpointCoupling -
            rawSixC5OddMinusDet * rawSixC5RawFiveEndpointCoupling) := by
      ring
    _ = _ := by
      rw [rawSixC5OddMixed_bordering, rawSixC5Alternating_bordering]

theorem rawSixC5OddMinusDelta_pos : 0 < rawSixC5OddMinusDelta := by
  have h := factorTwoIntrinsicOddPhaseLow_minus_minor_gt_one_div_forty
  unfold rawSixC5OddMinusDelta rawSixC5OddMinus11 rawSixC5OddMinus13
    rawSixC5OddMinus33
  exact lt_trans (by norm_num) h

theorem rawSixC5OddMinusDet_pos : 0 < rawSixC5OddMinusDet := by
  rw [← rawSixOddDetCoeff_three_eq_rawSixC5Det]
  exact rawSixOddDetCoefficients_pos.2.2.2

theorem rawSixC5EvenMinusDet_pos : 0 < rawSixC5EvenMinusDet := by
  have h := factorTwoIntrinsicSixP4SchurLeading_minus_pos
  have heq :
      rawSixC5EvenMinusDet =
        factorTwoIntrinsicSixP4SchurLeading (-1) := by
    have hdiag : factorTwoIntrinsicSixP4Diagonal (-1) =
        factorTwoIntrinsicP4PhaseDiagonal (-1) := by rfl
    unfold rawSixC5EvenMinusDet rawSixC5EvenMinus00 rawSixC5EvenMinus02
      rawSixC5EvenMinus04 rawSixC5EvenMinus22 rawSixC5EvenMinus24
      rawSixC5EvenMinus44 factorTwoIntrinsicSixP4SchurLeading
      factorTwoIntrinsicSixLowDet factorTwoIntrinsicSixP4Low0
      factorTwoIntrinsicSixP4Low2 symmetricDeterminant
    rw [hdiag]
    ring
  rw [heq]
  exact h

/-- The fifth raw-six coefficient is nonnegative once the single residual
`P5` tangent Cauchy gate is supplied.  All other terms are closed by the
structural raw-five theorem and endpoint positive definiteness. -/
theorem factorTwoIntrinsicSixProjectiveRawSixCoefficient_five_nonneg_of_residual_tangent
    (hgate : RawSixC5ResidualTangentGate) :
    0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 5 := by
  have hbase :
      0 ≤ rawSixC5OddMinusDet *
        factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4 :=
    mul_nonneg rawSixC5OddMinusDet_pos.le
      factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_four_nonneg
  have hresidual :
      0 ≤ rawSixC5EvenMinusDet * rawSixC5ResidualOddPlusNumerator -
        rawSixC5ResidualEvenAdjugateEnergy := by
    unfold RawSixC5ResidualTangentGate at hgate
    exact sub_nonneg.mpr hgate
  have hscaled :
      0 ≤ rawSixC5OddMinusDelta *
        factorTwoIntrinsicSixProjectiveRawSixCoefficient 5 := by
    rw [factorTwoIntrinsicSixProjectiveRawSixCoefficient_five_bordering]
    nlinarith
  by_contra hcoefficient
  have hneg : factorTwoIntrinsicSixProjectiveRawSixCoefficient 5 < 0 :=
    lt_of_not_ge hcoefficient
  have := mul_neg_of_pos_of_neg rawSixC5OddMinusDelta_pos hneg
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixC5ReductionStructural
