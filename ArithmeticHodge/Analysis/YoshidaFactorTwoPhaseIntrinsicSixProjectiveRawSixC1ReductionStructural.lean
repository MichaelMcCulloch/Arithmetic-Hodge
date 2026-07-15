import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC1Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixEndpointPositiveStructural

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixC1ReductionStructural

noncomputable section

open Polynomial
open ThreeByThreePositiveMixedDiscriminant
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC1Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientFrontierStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixEndpointPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOddPencilStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# A bordered-Schur reduction for the first raw-six coefficient

The coefficient linear in the projective variable is reduced by eliminating
the plus-endpoint `P1/P3` block from the new `P5` direction.  The result is
the already-proved raw-five coefficient plus one residual Cauchy gate.  No
entry box or coefficient family is enumerated.
-/

/-! ## Endpoint coordinates -/

private abbrev e00p : ℝ := factorTwoStructuralPhaseLow00 1
private abbrev e02p : ℝ := factorTwoStructuralPhaseLow02 1
private abbrev e04p : ℝ := factorTwoIntrinsicFourP45Cross04 1
private abbrev e22p : ℝ := factorTwoStructuralPhaseLow22 1
private abbrev e24p : ℝ := factorTwoIntrinsicFourP45Cross24 1
private abbrev e44p : ℝ := factorTwoIntrinsicSixP4Diagonal 1

private abbrev o11p : ℝ := factorTwoIntrinsicOddPhaseLow11 1
private abbrev o13p : ℝ := factorTwoIntrinsicOddPhaseLow13 1
private abbrev o15p : ℝ := factorTwoIntrinsicFourP45Cross15 1
private abbrev o33p : ℝ := factorTwoIntrinsicOddPhaseLow33 1
private abbrev o35p : ℝ := factorTwoIntrinsicFourP45Cross35 1
private abbrev o55p : ℝ := factorTwoIntrinsicSixP5Diagonal 1

private abbrev o11m : ℝ := factorTwoIntrinsicOddPhaseLow11 (-1)
private abbrev o13m : ℝ := factorTwoIntrinsicOddPhaseLow13 (-1)
private abbrev o15m : ℝ := factorTwoIntrinsicFourP45Cross15 (-1)
private abbrev o33m : ℝ := factorTwoIntrinsicOddPhaseLow33 (-1)
private abbrev o35m : ℝ := factorTwoIntrinsicFourP45Cross35 (-1)
private abbrev o55m : ℝ := factorTwoIntrinsicSixP5Diagonal (-1)

private abbrev j01 : ℝ := factorTwoIntrinsicAlternating01
private abbrev j03 : ℝ := factorTwoIntrinsicAlternating03
private abbrev j05 : ℝ := factorTwoIntrinsicFourP45Cross05
private abbrev j21 : ℝ := factorTwoIntrinsicAlternating21
private abbrev j23 : ℝ := factorTwoIntrinsicAlternating23
private abbrev j25 : ℝ := factorTwoIntrinsicFourP45Cross25
private abbrev j41 : ℝ := factorTwoIntrinsicFourP45Cross41
private abbrev j43 : ℝ := factorTwoIntrinsicFourP45Cross43
private abbrev j45 : ℝ := factorTwoIntrinsicSixAlternating45

/-- Plus-endpoint determinant of the old odd `P1/P3` block. -/
def rawSixC1OddLowDetPlus : ℝ := o11p * o33p - o13p ^ 2

/-- First coordinate of `adj(O2+)` applied to the plus `P5` cross column. -/
def rawSixC1OddP5Beta1 : ℝ := o33p * o15p - o13p * o35p

/-- Second coordinate of `adj(O2+)` applied to the plus `P5` cross column. -/
def rawSixC1OddP5Beta3 : ℝ := o11p * o35p - o13p * o15p

/-- Division-free `O+`-orthogonal residual direction obtained by adjoining
`P5` to `P1/P3`. -/
def rawSixC1OddP5Residual : Fin 3 → ℝ
  | 0 => -rawSixC1OddP5Beta1
  | 1 => -rawSixC1OddP5Beta3
  | 2 => rawSixC1OddLowDetPlus

/-- Alternating column of the division-free odd `P5` residual. -/
def rawSixC1AlternatingResidual : Fin 3 → ℝ
  | 0 => j01 * rawSixC1OddP5Residual 0 +
      j03 * rawSixC1OddP5Residual 1 + j05 * rawSixC1OddP5Residual 2
  | 1 => j21 * rawSixC1OddP5Residual 0 +
      j23 * rawSixC1OddP5Residual 1 + j25 * rawSixC1OddP5Residual 2
  | 2 => j41 * rawSixC1OddP5Residual 0 +
      j43 * rawSixC1OddP5Residual 1 + j45 * rawSixC1OddP5Residual 2

/-- Minus-endpoint energy of the division-free odd `P5` residual. -/
def rawSixC1OddP5ResidualMinusEnergy : ℝ :=
  symmetricQuadratic o11m o13m o15m o33m o35m o55m
    (rawSixC1OddP5Residual 0)
    (rawSixC1OddP5Residual 1)
    (rawSixC1OddP5Residual 2)

/-- Plus-even adjugate energy of its alternating column. -/
def rawSixC1AlternatingResidualEvenAdjugateEnergy : ℝ :=
  adjugateQuadratic e00p e02p e04p e22p e24p e44p
    (rawSixC1AlternatingResidual 0)
    (rawSixC1AlternatingResidual 1)
    (rawSixC1AlternatingResidual 2)

/-- The sole residual gate left by the bordered-Schur reduction. -/
def FactorTwoIntrinsicSixProjectiveRawSixC1ResidualGate : Prop :=
  rawSixC1AlternatingResidualEvenAdjugateEnergy ≤
    pivotCoeff 0 * rawSixC1OddP5ResidualMinusEnergy

/-! ## Cancellation-preserving algebra -/

private def evenAdjugatePair
    (u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  (e22p * e44p - e24p ^ 2) * u0 * v0 +
    (e04p * e24p - e02p * e44p) * (u0 * v2 + u2 * v0) +
    (e02p * e24p - e04p * e22p) * (u0 * v4 + u4 * v0) +
    (e00p * e44p - e04p ^ 2) * u2 * v2 +
    (e02p * e04p - e00p * e24p) * (u2 * v4 + u4 * v2) +
    (e00p * e22p - e02p ^ 2) * u4 * v4

private def alternating0 : Fin 3 → ℝ
  | 0 => j01
  | 1 => j03
  | 2 => j05

private def alternating2 : Fin 3 → ℝ
  | 0 => j21
  | 1 => j23
  | 2 => j25

private def alternating4 : Fin 3 → ℝ
  | 0 => j41
  | 1 => j43
  | 2 => j45

private theorem rawSixAdjugatePair_eval_zero_eq (i j : Fin 3) :
    (coefficientRawSixAdjugatePairPolynomial i j).eval 0 =
      evenAdjugatePair
        (alternating0 i) (alternating2 i) (alternating4 i)
        (alternating0 j) (alternating2 j) (alternating4 j) := by
  have hpoly : coefficientRawSixAdjugatePairPolynomial i j =
      coefficientRawAdjugatePairPolynomial
        (alternating0 i) (alternating2 i) (alternating4 i)
        (alternating0 j) (alternating2 j) (alternating4 j) := by
    fin_cases i <;> fin_cases j <;> rfl
  rw [hpoly]
  unfold coefficientRawAdjugatePairPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial evenAdjugatePair
  simp

private def oldAlternatingPenalty : ℝ :=
  o33p * evenAdjugatePair j01 j21 j41 j01 j21 j41 -
    2 * o13p * evenAdjugatePair j01 j21 j41 j03 j23 j43 +
    o11p * evenAdjugatePair j03 j23 j43 j03 j23 j43

private def newAlternatingPenalty : ℝ :=
  (o33p * o55p - o35p ^ 2) *
      evenAdjugatePair j01 j21 j41 j01 j21 j41 +
    2 * (o15p * o35p - o13p * o55p) *
      evenAdjugatePair j01 j21 j41 j03 j23 j43 +
    2 * (o13p * o35p - o15p * o33p) *
      evenAdjugatePair j01 j21 j41 j05 j25 j45 +
    (o11p * o55p - o15p ^ 2) *
      evenAdjugatePair j03 j23 j43 j03 j23 j43 +
    2 * (o13p * o15p - o11p * o35p) *
      evenAdjugatePair j03 j23 j43 j05 j25 j45 +
    (o11p * o33p - o13p ^ 2) *
      evenAdjugatePair j05 j25 j45 j05 j25 j45

private def oldOddMixed : ℝ :=
  o11p * o33m + o11m * o33p - 2 * o13p * o13m

private def newOddMixed : ℝ :=
  mixedDeterminantOne
    o11p o13p o15p o33p o35p o55p
    o11m o13m o15m o33m o35m o55m

private theorem rawSixOddPlusMatrix_det_eq :
    rawSixOddPlusMatrix.det =
      symmetricDeterminant o11p o13p o15p o33p o35p o55p := by
  unfold rawSixOddPlusMatrix
  exact rawSixOddEndpointMatrix_det_eq_symmetricDeterminant 1

private theorem rawSixOddDetCoeff_one_eq_newOddMixed :
    rawSixOddDetCoeff 1 = newOddMixed := by
  rw [rawSixOddDetCoeff_one_eq]
  unfold newOddMixed rawSixOddPlusMatrix rawSixOddMinusMatrix
    rawSixOddEndpointMatrix
  exact matrixMixedDeterminantOne_symmetricMatrix3
    _ _ _ _ _ _ _ _ _ _ _ _

private theorem bordered_odd_mixed_identity :
    rawSixC1OddLowDetPlus * newOddMixed -
        (rawSixOddPlusMatrix.det) * oldOddMixed =
      rawSixC1OddP5ResidualMinusEnergy := by
  unfold rawSixC1OddLowDetPlus rawSixC1OddP5ResidualMinusEnergy
    rawSixC1OddP5Residual rawSixC1OddP5Beta1 rawSixC1OddP5Beta3
    newOddMixed oldOddMixed mixedDeterminantOne symmetricQuadratic
  simp only [rawSixC1OddLowDetPlus]
  rw [rawSixOddPlusMatrix_det_eq]
  unfold symmetricDeterminant
  ring

private theorem bordered_alternating_identity :
    rawSixC1OddLowDetPlus * newAlternatingPenalty -
        rawSixOddPlusMatrix.det * oldAlternatingPenalty =
      rawSixC1AlternatingResidualEvenAdjugateEnergy := by
  unfold rawSixC1OddLowDetPlus rawSixC1AlternatingResidualEvenAdjugateEnergy
    rawSixC1AlternatingResidual rawSixC1OddP5Residual
    rawSixC1OddP5Beta1 rawSixC1OddP5Beta3 newAlternatingPenalty
    oldAlternatingPenalty evenAdjugatePair adjugateQuadratic
  simp only [rawSixC1OddLowDetPlus]
  rw [rawSixOddPlusMatrix_det_eq]
  unfold symmetricDeterminant
  ring

private theorem rawFiveOddMinorCoeff_zero_eq :
    rawFiveOddMinorCoeff 0 = rawSixC1OddLowDetPlus := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
    coefficientOdd11Polynomial coefficientOdd13Polynomial
    coefficientOdd33Polynomial endpointAffinePolynomial
    rawSixC1OddLowDetPlus
  simp

private theorem rawFiveCouplingCoeff_zero_eq :
    rawFiveCouplingCoeff 0 = oldAlternatingPenalty := by
  change
    factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial
    coefficientRawAdjugatePairPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    coefficientOdd11Polynomial coefficientOdd13Polynomial
    coefficientOdd33Polynomial endpointAffinePolynomial
    oldAlternatingPenalty evenAdjugatePair
  simp

private theorem rawSixMixedOneCoeff_zero_eq :
    rawSixMixedOneCoeff 0 = newAlternatingPenalty := by
  change
    factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold factorTwoIntrinsicSixProjectiveRawSixMixedAdjugateOneCoefficientPolynomial
    coefficientOdd11Polynomial
    coefficientOdd13Polynomial coefficientOdd15Polynomial
    coefficientOdd33Polynomial coefficientOdd35Polynomial
    coefficientP5DiagonalPolynomial endpointAffinePolynomial
    newAlternatingPenalty
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
    eval_C, eval_X]
  rw [rawSixAdjugatePair_eval_zero_eq 0 0,
    rawSixAdjugatePair_eval_zero_eq 0 1,
    rawSixAdjugatePair_eval_zero_eq 0 2,
    rawSixAdjugatePair_eval_zero_eq 1 1,
    rawSixAdjugatePair_eval_zero_eq 1 2,
    rawSixAdjugatePair_eval_zero_eq 2 2]
  simp [alternating0, alternating2, alternating4]

/-- Exact bordered-Schur decomposition of the first raw-six coefficient.
The first summand is the old raw-five coefficient; the other two terms are
the minus energy and plus-even adjugate energy of one `O+`-orthogonal `P5`
residual direction. -/
theorem factorTwoIntrinsicSixProjectiveRawSixCoefficient_one_borderedSchur :
    rawSixC1OddLowDetPlus *
        factorTwoIntrinsicSixProjectiveRawSixCoefficient 1 =
      rawSixOddPlusMatrix.det *
          factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1 +
        pivotCoeff 0 * rawSixC1OddP5ResidualMinusEnergy -
        rawSixC1AlternatingResidualEvenAdjugateEnergy := by
  have hOdd := bordered_odd_mixed_identity
  have hAlt := bordered_alternating_identity
  simp only [factorTwoIntrinsicSixProjectiveRawSixCoefficient,
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rw [rawSixOddDetCoeff_zero_eq, rawSixOddDetCoeff_one_eq_newOddMixed]
  rw [rawFiveOddMinorCoeff_zero_eq, rawFiveOddMinorCoeff_one_eq,
    rawFiveCouplingCoeff_zero_eq, rawSixMixedOneCoeff_zero_eq]
  change rawSixC1OddLowDetPlus *
      (pivotCoeff 0 * newOddMixed +
        pivotCoeff 1 * rawSixOddPlusMatrix.det - newAlternatingPenalty) =
    rawSixOddPlusMatrix.det *
        (pivotCoeff 0 * oldOddMixed +
          pivotCoeff 1 * rawSixC1OddLowDetPlus - oldAlternatingPenalty) +
      pivotCoeff 0 * rawSixC1OddP5ResidualMinusEnergy -
      rawSixC1AlternatingResidualEvenAdjugateEnergy
  calc
    rawSixC1OddLowDetPlus *
          (pivotCoeff 0 * newOddMixed +
            pivotCoeff 1 * rawSixOddPlusMatrix.det - newAlternatingPenalty) =
        rawSixOddPlusMatrix.det *
            (pivotCoeff 0 * oldOddMixed +
              pivotCoeff 1 * rawSixC1OddLowDetPlus - oldAlternatingPenalty) +
          pivotCoeff 0 *
            (rawSixC1OddLowDetPlus * newOddMixed -
              rawSixOddPlusMatrix.det * oldOddMixed) -
          (rawSixC1OddLowDetPlus * newAlternatingPenalty -
            rawSixOddPlusMatrix.det * oldAlternatingPenalty) := by ring
    _ = _ := by rw [hOdd, hAlt]

private theorem rawSixC1OddLowDetPlus_pos :
    0 < rawSixC1OddLowDetPlus := by
  have h := oddStructuralLow_endpoint_gates.2.1
  simpa [rawSixC1OddLowDetPlus, factorTwoIntrinsicOddPhaseLow11,
    factorTwoIntrinsicOddPhaseLow13, factorTwoIntrinsicOddPhaseLow33,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow13,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow33] using h

/-- The single residual Cauchy gate, together with the already-proved
raw-five C1 sign, proves the raw-six C1 sign. -/
theorem factorTwoIntrinsicSixProjectiveRawSixCoefficient_one_nonneg_of_residualGate
    (hResidual : FactorTwoIntrinsicSixProjectiveRawSixC1ResidualGate) :
    0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 1 := by
  have hidentity :=
    factorTwoIntrinsicSixProjectiveRawSixCoefficient_one_borderedSchur
  have hFive :=
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_one_nonneg
  have hOddDet : 0 < rawSixOddPlusMatrix.det :=
    rawSixOddPlusMatrix_posDef.det_pos
  have hright : 0 ≤ rawSixOddPlusMatrix.det *
        factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1 +
      pivotCoeff 0 * rawSixC1OddP5ResidualMinusEnergy -
        rawSixC1AlternatingResidualEvenAdjugateEnergy := by
    have hOld := mul_nonneg hOddDet.le hFive
    unfold FactorTwoIntrinsicSixProjectiveRawSixC1ResidualGate at hResidual
    linarith
  have hscaled : 0 ≤ rawSixC1OddLowDetPlus *
      factorTwoIntrinsicSixProjectiveRawSixCoefficient 1 := by
    linarith
  exact nonneg_of_mul_nonneg_left
    (by simpa only [mul_comm] using hscaled) rawSixC1OddLowDetPlus_pos

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixC1ReductionStructural
