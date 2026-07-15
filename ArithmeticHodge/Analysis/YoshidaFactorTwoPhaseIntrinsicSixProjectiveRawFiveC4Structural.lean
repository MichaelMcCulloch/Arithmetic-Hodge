import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC3Structural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC4Structural

noncomputable section

open Polynomial
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural positivity of the fourth raw five-mode coefficient

This is the coefficient adjacent to the negative endpoint.  We keep its
endpoint geometry visible: it is the adjugate trace of the negative odd
Gram against one mixed Schur matrix.  The proof uses rational endpoint
boxes and exact polynomial identities, never samples the projective
half-line.
-/

private def e00m : ℝ := factorTwoStructuralPhaseLow00 (-1)
private def e02m : ℝ := factorTwoStructuralPhaseLow02 (-1)
private def e04m : ℝ := factorTwoIntrinsicFourP45Cross04 (-1)
private def e22m : ℝ := factorTwoStructuralPhaseLow22 (-1)
private def e24m : ℝ := factorTwoIntrinsicFourP45Cross24 (-1)
private def e44m : ℝ := factorTwoIntrinsicSixP4Diagonal (-1)

private def o11p : ℝ := factorTwoIntrinsicOddPhaseLow11 1
private def o13p : ℝ := factorTwoIntrinsicOddPhaseLow13 1
private def o33p : ℝ := factorTwoIntrinsicOddPhaseLow33 1
private def o11m : ℝ := factorTwoIntrinsicOddPhaseLow11 (-1)
private def o13m : ℝ := factorTwoIntrinsicOddPhaseLow13 (-1)
private def o33m : ℝ := factorTwoIntrinsicOddPhaseLow33 (-1)

private def a01 : ℝ := factorTwoIntrinsicAlternating01
private def a21 : ℝ := factorTwoIntrinsicAlternating21
private def a41 : ℝ := factorTwoIntrinsicFourP45Cross41
private def a03 : ℝ := factorTwoIntrinsicAlternating03
private def a23 : ℝ := factorTwoIntrinsicAlternating23
private def a43 : ℝ := factorTwoIntrinsicFourP45Cross43

private def evenDetMinus : ℝ :=
  symmetricDeterminant e00m e02m e04m e22m e24m e44m

private def oddDetMinus : ℝ := o11m * o33m - o13m ^ 2

private def oddMixed : ℝ :=
  o11p * o33m + o11m * o33p - 2 * o13p * o13m

private def endpointAdjugatePair
    (u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  (e22m * e44m - e24m ^ 2) * u0 * v0 +
    (e04m * e24m - e02m * e44m) * (u0 * v2 + u2 * v0) +
    (e02m * e24m - e04m * e22m) * (u0 * v4 + u4 * v0) +
    (e00m * e44m - e04m ^ 2) * u2 * v2 +
    (e02m * e04m - e00m * e24m) * (u2 * v4 + u4 * v2) +
    (e00m * e22m - e02m ^ 2) * u4 * v4

private def j11 : ℝ := endpointAdjugatePair a01 a21 a41 a01 a21 a41
private def j13 : ℝ := endpointAdjugatePair a01 a21 a41 a03 a23 a43
private def j33 : ℝ := endpointAdjugatePair a03 a23 a43 a03 a23 a43

private def endpointCouplingMinus : ℝ :=
  o33m * j11 - 2 * o13m * j13 + o11m * j33

private theorem pivotCoeff_three_eq_evenDetMinus :
    pivotCoeff 3 = evenDetMinus := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 3 = _
  have hpoly :
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
        C evenDetMinus * X ^ 3 := by
    unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
      coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
      coefficientLow00Polynomial coefficientLow02Polynomial
      coefficientLow22Polynomial coefficientCross04Polynomial
      coefficientCross24Polynomial coefficientP4DiagonalPolynomial
      endpointAffinePolynomial evenDetMinus e00m e02m e04m e22m e24m e44m
      mixedDeterminantOne symmetricDeterminant
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private theorem rawFiveOddMinorCoeff_two_eq_oddDetMinus :
    rawFiveOddMinorCoeff 2 = oddDetMinus := by
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
          C oddDetMinus * X ^ 2 := by
    unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
      coefficientOdd11Polynomial coefficientOdd13Polynomial
      coefficientOdd33Polynomial endpointAffinePolynomial oddDetMinus
      o11m o13m o33m
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private def endpointAdjugatePairAt
    (q00 q02 q04 q22 q24 q44 u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  (q22 * q44 - q24 ^ 2) * u0 * v0 +
    (q04 * q24 - q02 * q44) * (u0 * v2 + u2 * v0) +
    (q02 * q24 - q04 * q22) * (u0 * v4 + u4 * v0) +
    (q00 * q44 - q04 ^ 2) * u2 * v2 +
    (q02 * q04 - q00 * q24) * (u2 * v4 + u4 * v2) +
    (q00 * q22 - q02 ^ 2) * u4 * v4

private def endpointAdjugatePairMixed
    (u0 u2 u4 v0 v2 v4 : ℝ) : ℝ :=
  let p00 := factorTwoStructuralPhaseLow00 1
  let p02 := factorTwoStructuralPhaseLow02 1
  let p04 := factorTwoIntrinsicFourP45Cross04 1
  let p22 := factorTwoStructuralPhaseLow22 1
  let p24 := factorTwoIntrinsicFourP45Cross24 1
  let p44 := factorTwoIntrinsicSixP4Diagonal 1
  (p22 * e44m + e22m * p44 - 2 * p24 * e24m) * u0 * v0 +
    (p04 * e24m + e04m * p24 - p02 * e44m - e02m * p44) *
      (u0 * v2 + u2 * v0) +
    (p02 * e24m + e02m * p24 - p04 * e22m - e04m * p22) *
      (u0 * v4 + u4 * v0) +
    (p00 * e44m + e00m * p44 - 2 * p04 * e04m) * u2 * v2 +
    (p02 * e04m + e02m * p04 - p00 * e24m - e00m * p24) *
      (u2 * v4 + u4 * v2) +
    (p00 * e22m + e00m * p22 - 2 * p02 * e02m) * u4 * v4

private theorem coefficientRawAdjugatePairPolynomial_expansion
    (u0 u2 u4 v0 v2 v4 : ℝ) :
    coefficientRawAdjugatePairPolynomial u0 u2 u4 v0 v2 v4 =
      C (endpointAdjugatePairAt
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)
        u0 u2 u4 v0 v2 v4) +
      C (endpointAdjugatePairMixed u0 u2 u4 v0 v2 v4) * X +
      C (endpointAdjugatePair u0 u2 u4 v0 v2 v4) * X ^ 2 := by
  unfold coefficientRawAdjugatePairPolynomial
    coefficientLowDetPolynomial coefficientLow00Polynomial
    coefficientLow02Polynomial coefficientLow22Polynomial
    coefficientCross04Polynomial coefficientCross24Polynomial
    coefficientP4DiagonalPolynomial endpointAffinePolynomial
    endpointAdjugatePairAt endpointAdjugatePairMixed endpointAdjugatePair
    e00m e02m e04m e22m e24m e44m
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

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

private theorem rawFiveCouplingCoeff_three_eq_endpoint :
    rawFiveCouplingCoeff 3 = endpointCouplingMinus := by
  change
    factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial.coeff 3 = _
  let A11 := endpointAdjugatePairAt
    (factorTwoStructuralPhaseLow00 1) (factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 1) (factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 1) (factorTwoIntrinsicSixP4Diagonal 1)
    a01 a21 a41 a01 a21 a41
  let A13 := endpointAdjugatePairAt
    (factorTwoStructuralPhaseLow00 1) (factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 1) (factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 1) (factorTwoIntrinsicSixP4Diagonal 1)
    a01 a21 a41 a03 a23 a43
  let A33 := endpointAdjugatePairAt
    (factorTwoStructuralPhaseLow00 1) (factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 1) (factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 1) (factorTwoIntrinsicSixP4Diagonal 1)
    a03 a23 a43 a03 a23 a43
  let B11 := endpointAdjugatePairMixed a01 a21 a41 a01 a21 a41
  let B13 := endpointAdjugatePairMixed a01 a21 a41 a03 a23 a43
  let B33 := endpointAdjugatePairMixed a03 a23 a43 a03 a23 a43
  have hpoly :
      factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial =
        C (o33p * A11 - 2 * o13p * A13 + o11p * A33) +
        C (o33p * B11 + o33m * A11 -
            2 * (o13p * B13 + o13m * A13) +
            o11p * B33 + o11m * A33) * X +
        C (o33p * j11 + o33m * B11 -
            2 * (o13p * j13 + o13m * B13) +
            o11p * j33 + o11m * B33) * X ^ 2 +
        C endpointCouplingMinus * X ^ 3 := by
    unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial
    rw [coefficientRawAdjugatePairPolynomial_expansion,
      coefficientRawAdjugatePairPolynomial_expansion,
      coefficientRawAdjugatePairPolynomial_expansion]
    unfold coefficientOdd11Polynomial coefficientOdd13Polynomial
      coefficientOdd33Polynomial endpointAffinePolynomial
    dsimp only [A11, A13, A33, B11, B13, B33]
    unfold endpointCouplingMinus j11 j13 j33
      o11p o13p o33p o11m o13m o33m
      a01 a21 a41 a03 a23 a43
    simp only [map_add, map_sub, map_mul, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

private theorem coefficient_four_eq_endpoint_trace :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4 =
      pivotCoeff 2 * oddDetMinus + evenDetMinus * oddMixed -
        endpointCouplingMinus := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rw [pivotCoeff_three_eq_evenDetMinus,
    rawFiveOddMinorCoeff_two_eq_oddDetMinus,
    rawFiveOddMinorCoeff_one_eq,
    rawFiveCouplingCoeff_three_eq_endpoint]
  unfold oddMixed o11p o13p o33p o11m o13m o33m
  ring

/-! The remaining proof is a correlated rational Schur estimate. -/

/-! ## Eliminate the third odd coordinate at the negative endpoint

The useful cancellation is a two-by-two Schur elimination in the odd block.
Multiplying by its negative-endpoint `P₃` diagonal avoids division.  The
first summand below is a positive odd minor times a one-odd-mode gate; the
only numerical estimate left is one small, correlated adjugate excess.
-/

private def strongMinus : ℝ := e00m + 2 * e02m + e22m
private def skewMinus : ℝ := e00m - e22m
private def weakMinus : ℝ := e00m - 2 * e02m + e22m
private def crossSumMinus : ℝ := e04m + e24m
private def crossDifferenceMinus : ℝ := e24m - e04m

private def xOne : ℝ := a01 + a21
private def yOne : ℝ := a01 - a21
private def xThree : ℝ := a03 + a23
private def yThree : ℝ := a03 - a23

private def transformedX : ℝ := o33m * xOne - o13m * xThree
private def transformedY : ℝ := o33m * yOne - o13m * yThree
private def transformedZ : ℝ := o33m * a41 - o13m * a43

private def transformedOddPlus : ℝ :=
  o33m ^ 2 * o11p - 2 * o33m * o13m * o13p + o13m ^ 2 * o33p

private def transformedAdjugate : ℝ :=
  endpointAdjugatePair
    (o33m * a01 - o13m * a03)
    (o33m * a21 - o13m * a23)
    (o33m * a41 - o13m * a43)
    (o33m * a01 - o13m * a03)
    (o33m * a21 - o13m * a23)
    (o33m * a41 - o13m * a43)

private def p3EndpointGate : ℝ :=
  pivotCoeff 2 * o33m + evenDetMinus * o33p - j33

private def transformedReserve : ℝ :=
  evenDetMinus * transformedOddPlus - transformedAdjugate

private theorem transformedAdjugate_expansion :
    transformedAdjugate =
      o33m ^ 2 * j11 - 2 * o33m * o13m * j13 + o13m ^ 2 * j33 := by
  unfold transformedAdjugate j11 j13 j33 endpointAdjugatePair
  ring

private theorem scaled_coefficient_four_decomposition :
    o33m * factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4 =
      oddDetMinus * p3EndpointGate + transformedReserve := by
  rw [coefficient_four_eq_endpoint_trace]
  unfold transformedReserve
  rw [transformedAdjugate_expansion]
  unfold oddDetMinus oddMixed endpointCouplingMinus p3EndpointGate
    transformedOddPlus
  ring

/-! ## Aligned negative-endpoint coordinates -/

/-- The determinant in the sum/difference coordinates of the `P₀/P₂`
plane. -/
private def alignedDeterminant
    (U K W S T F : ℝ) : ℝ :=
  (F * (U * W - K ^ 2) -
      (W * S ^ 2 + U * T ^ 2 + 2 * K * S * T)) / 4

/-- The polarized adjugate quadratic in the same aligned coordinates. -/
private def alignedAdjugateQuadratic
    (U K W S T F X Y Z : ℝ) : ℝ :=
  ((F * W - T ^ 2) * X ^ 2 +
      (F * U - S ^ 2) * Y ^ 2 +
      (-F * K - S * T) * (2 * X * Y) +
      (-W * S - K * T) * (2 * X * Z) +
      (K * S + U * T) * (2 * Y * Z) +
      (U * W - K ^ 2) * Z ^ 2) / 4

private theorem evenDetMinus_eq_aligned :
    evenDetMinus = alignedDeterminant strongMinus skewMinus weakMinus
      crossSumMinus crossDifferenceMinus e44m := by
  unfold evenDetMinus alignedDeterminant strongMinus skewMinus weakMinus
    crossSumMinus crossDifferenceMinus symmetricDeterminant
  ring

private theorem transformedAdjugate_eq_aligned :
    transformedAdjugate =
      alignedAdjugateQuadratic strongMinus skewMinus weakMinus
        crossSumMinus crossDifferenceMinus e44m
        transformedX transformedY transformedZ := by
  unfold transformedAdjugate alignedAdjugateQuadratic strongMinus skewMinus
    weakMinus crossSumMinus crossDifferenceMinus transformedX transformedY
    transformedZ xOne yOne xThree yThree endpointAdjugatePair
  ring

/-- The sole correlated endpoint quantity that must be bounded. -/
private def transformedExcess
    (U K W S T F X Y Z Q : ℝ) : ℝ :=
  alignedAdjugateQuadratic U K W S T F X Y Z -
    Q * alignedDeterminant U K W S T F

private theorem transformedReserve_eq_neg_excess :
    transformedReserve =
      -transformedExcess strongMinus skewMinus weakMinus crossSumMinus
        crossDifferenceMinus e44m transformedX transformedY transformedZ
        transformedOddPlus := by
  unfold transformedReserve transformedExcess
  rw [evenDetMinus_eq_aligned, transformedAdjugate_eq_aligned]
  ring

/-! ## Rational boxes and elementary interval tools -/

private theorem positive_sq_bounds
    {u l r : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hur : u ≤ r) :
    l ^ 2 ≤ u ^ 2 ∧ u ^ 2 ≤ r ^ 2 := by
  have hu : 0 ≤ u := hl.trans hlu
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlu) (add_nonneg hu hl)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hur)
      (add_nonneg (hu.trans hur) hu)]

private theorem positive_mul_bounds
    {u v lu ru lv rv : ℝ}
    (hlu0 : 0 ≤ lu) (hlv0 : 0 ≤ lv)
    (hlu : lu ≤ u) (hru : u ≤ ru)
    (hlv : lv ≤ v) (hrv : v ≤ rv) :
    lu * lv ≤ u * v ∧ u * v ≤ ru * rv := by
  have hu0 : 0 ≤ u := hlu0.trans hlu
  have hv0 : 0 ≤ v := hlv0.trans hlv
  constructor
  · calc
      lu * lv ≤ u * lv := mul_le_mul_of_nonneg_right hlu hlv0
      _ ≤ u * v := mul_le_mul_of_nonneg_left hlv hu0
  · calc
      u * v ≤ ru * v := mul_le_mul_of_nonneg_right hru hv0
      _ ≤ ru * rv := mul_le_mul_of_nonneg_left hrv (hu0.trans hru)

private theorem positive_mul3_bounds
    {u v w lu ru lv rv lw rw : ℝ}
    (hlu0 : 0 ≤ lu) (hlv0 : 0 ≤ lv) (hlw0 : 0 ≤ lw)
    (hlu : lu ≤ u) (hru : u ≤ ru)
    (hlv : lv ≤ v) (hrv : v ≤ rv)
    (hlw : lw ≤ w) (hrw : w ≤ rw) :
    lu * lv * lw ≤ u * v * w ∧ u * v * w ≤ ru * rv * rw := by
  have huv := positive_mul_bounds hlu0 hlv0 hlu hru hlv hrv
  have huv0 : 0 ≤ u * v :=
    mul_nonneg (hlu0.trans hlu) (hlv0.trans hlv)
  constructor
  · calc
      lu * lv * lw ≤ (u * v) * lw :=
        mul_le_mul_of_nonneg_right huv.1 hlw0
      _ ≤ u * v * w := mul_le_mul_of_nonneg_left hlw huv0
  · calc
      u * v * w ≤ (ru * rv) * w :=
        mul_le_mul_of_nonneg_right huv.2 (hlw0.trans hlw)
      _ ≤ ru * rv * rw :=
        mul_le_mul_of_nonneg_left hrw
          (mul_nonneg (hlu0.trans hlu |>.trans hru)
            (hlv0.trans hlv |>.trans hrv))

private theorem mul_le_budget_of_abs_le
    {u v r m : ℝ} (hr : 0 ≤ r)
    (hu : |u| ≤ r) (hv : |v| ≤ m) : u * v ≤ r * m := by
  calc
    u * v ≤ |u * v| := le_abs_self _
    _ = |u| * |v| := abs_mul u v
    _ ≤ r * m := mul_le_mul hu hv (abs_nonneg v) hr

private theorem negative_endpoint_aligned_bounds :
    (2198709 / 1000000 : ℝ) < strongMinus ∧
      strongMinus < 2200885 / 1000000 ∧
      (77471 / 1000000 : ℝ) < skewMinus ∧
      skewMinus < 79531 / 1000000 ∧
      (18409 / 1000000 : ℝ) < weakMinus ∧
      weakMinus < 20585 / 1000000 ∧
      (292634 / 1000000 : ℝ) < crossSumMinus ∧
      crossSumMinus < 300081 / 1000000 ∧
      (66134 / 1000000 : ℝ) < crossDifferenceMinus ∧
      crossDifferenceMinus < 70081 / 1000000 := by
  rcases factorTwoIntrinsicP4_negative_aligned_bounds with
    ⟨hUL, hUU, hKL, hKU, hSL, hSU, hWL, hWU, hTL, hTU⟩
  simpa only [strongMinus, skewMinus, weakMinus, crossSumMinus,
    crossDifferenceMinus, e00m, e02m, e04m, e22m, e24m] using
      ⟨hUL, hUU, hKL, hKU, hWL, hWU, hSL, hSU, hTL, hTU⟩

private theorem alternating_aligned_bounds :
    (56168 / 100000 : ℝ) < xOne ∧ xOne < 56173 / 100000 ∧
      (1687 / 100000 : ℝ) < yOne ∧ yOne < 1692 / 100000 ∧
      (53815 / 100000 : ℝ) < xThree ∧ xThree < 53836 / 100000 ∧
      (555 / 10000 : ℝ) < yThree ∧ yThree < 279 / 5000 := by
  simpa only [xOne, yOne, xThree, yThree, a01, a21, a03, a23] using
    factorTwoIntrinsicAlternatingSharpBounds

private theorem e44m_lower : (12 / 25 : ℝ) < e44m := by
  change (12 / 25 : ℝ) < factorTwoIntrinsicP4PhaseDiagonal (-1)
  simpa [factorTwoIntrinsicP4MinusDiagonalLower] using
    factorTwoIntrinsicP4MinusDiagonalLower_lt_phaseDiagonal

private theorem e44m_upper : e44m < (64 / 125 : ℝ) := by
  simpa only [e44m] using
    factorTwoIntrinsicSixP4Diagonal_minus_lt_sixty_four_div_one_twenty_five

private def uCenter : ℝ := 2199797 / 1000000
private def kCenter : ℝ := 78501 / 1000000
private def wCenter : ℝ := 19497 / 1000000
private def sCenter : ℝ := 592715 / 2000000
private def tCenter : ℝ := 136215 / 2000000

private theorem negative_endpoint_center_radii :
    |strongMinus - uCenter| ≤ (1088 / 1000000 : ℝ) ∧
      |skewMinus - kCenter| ≤ (1030 / 1000000 : ℝ) ∧
      |weakMinus - wCenter| ≤ (1088 / 1000000 : ℝ) ∧
      |crossSumMinus - sCenter| ≤ (7447 / 2000000 : ℝ) ∧
      |crossDifferenceMinus - tCenter| ≤ (3947 / 2000000 : ℝ) := by
  rcases negative_endpoint_aligned_bounds with
    ⟨hUL, hUU, hKL, hKU, hWL, hWU, hSL, hSU, hTL, hTU⟩
  repeat' apply And.intro
  all_goals rw [abs_le]
  all_goals simp only [uCenter, kCenter, wCenter, sCenter, tCenter]
  all_goals constructor <;> norm_num at * <;> linarith

/-! ## A quantitative one-odd-mode gate for `P₃` -/

private def p3EndpointExcess
    (U K W S T F X Y R : ℝ) : ℝ :=
  alignedAdjugateQuadratic U K W S T F X Y (-R) -
    (2115 / 10000 : ℝ) * alignedDeterminant U K W S T F

private theorem p3_endpoint_excess_eq :
    j33 - (2115 / 10000 : ℝ) * evenDetMinus =
      p3EndpointExcess strongMinus skewMinus weakMinus crossSumMinus
        crossDifferenceMinus e44m xThree yThree (-a43) := by
  unfold p3EndpointExcess j33 xThree yThree
  rw [evenDetMinus_eq_aligned]
  unfold alignedAdjugateQuadratic strongMinus skewMinus weakMinus
    crossSumMinus crossDifferenceMinus endpointAdjugatePair
  ring

private def x3Center : ℝ := 107651 / 200000
private def y3Center : ℝ := 1113 / 20000
private def r3Center : ℝ := 3 / 1000

private theorem p3_coordinate_radii_of_cross43_bounds
    (h43 : (-4 / 1000 : ℝ) < a43 ∧ a43 < -2 / 1000) :
    |xThree - x3Center| ≤ (21 / 200000 : ℝ) ∧
      |yThree - y3Center| ≤ (3 / 20000 : ℝ) ∧
      |-a43 - r3Center| ≤ (1 / 1000 : ℝ) := by
  rcases alternating_aligned_bounds with
    ⟨_hx1L, _hx1U, _hy1L, _hy1U, hxL, hxU, hyL, hyU⟩
  repeat' apply And.intro
  all_goals rw [abs_le]
  all_goals simp only [x3Center, y3Center, r3Center]
  all_goals constructor <;> norm_num at * <;> linarith

/-! The secant slopes below are written explicitly so every estimate remains
an ordinary rational interval argument. -/

private def p3XSlope
    (K W S T F X Y R : ℝ) : ℝ :=
  ((F * W - T ^ 2) * (X + x3Center) +
      2 * (-F * K - S * T) * Y +
      2 * (W * S + K * T) * R) / 4

private def p3YSlope
    (U K S T F Y R : ℝ) : ℝ :=
  ((F * U - S ^ 2) * (Y + y3Center) +
      2 * (-F * K - S * T) * x3Center -
      2 * (K * S + U * T) * R) / 4

private def p3RSlope
    (U K W S T R : ℝ) : ℝ :=
  ((U * W - K ^ 2) * (R + r3Center) +
      2 * (W * S + K * T) * x3Center -
      2 * (K * S + U * T) * y3Center) / 4

private def p3USlope (W T F : ℝ) : ℝ :=
  (F * y3Center ^ 2 - 2 * T * y3Center * r3Center +
      W * r3Center ^ 2 -
      (2115 / 10000 : ℝ) * (F * W - T ^ 2)) / 4

private def p3KSlope (K S T F : ℝ) : ℝ :=
  (-2 * F * x3Center * y3Center +
      2 * T * x3Center * r3Center -
      2 * S * y3Center * r3Center -
      (K + kCenter) * r3Center ^ 2 +
      (2115 / 10000 : ℝ) * F * (K + kCenter) +
      2 * (2115 / 10000 : ℝ) * S * T) / 4

private def p3WSlope (S F : ℝ) : ℝ :=
  (F * x3Center ^ 2 + 2 * S * x3Center * r3Center +
      uCenter * r3Center ^ 2 -
      (2115 / 10000 : ℝ) * (F * uCenter - S ^ 2)) / 4

private def p3SSlope (S T : ℝ) : ℝ :=
  (-(S + sCenter) * y3Center ^ 2 -
      2 * T * x3Center * y3Center +
      2 * wCenter * x3Center * r3Center -
      2 * kCenter * y3Center * r3Center +
      (2115 / 10000 : ℝ) * wCenter * (S + sCenter) +
      2 * (2115 / 10000 : ℝ) * kCenter * T) / 4

private def p3TSlope (T : ℝ) : ℝ :=
  (-(T + tCenter) * x3Center ^ 2 -
      2 * sCenter * x3Center * y3Center +
      2 * kCenter * x3Center * r3Center -
      2 * uCenter * y3Center * r3Center +
      (2115 / 10000 : ℝ) * uCenter * (T + tCenter) +
      2 * (2115 / 10000 : ℝ) * kCenter * sCenter) / 4

private def p3FSlope : ℝ :=
  (wCenter * x3Center ^ 2 + uCenter * y3Center ^ 2 -
      2 * kCenter * x3Center * y3Center -
      (2115 / 10000 : ℝ) *
        (uCenter * wCenter - kCenter ^ 2)) / 4

private theorem p3_x_step
    (U K W S T F X Y R : ℝ) :
    p3EndpointExcess U K W S T F X Y R -
        p3EndpointExcess U K W S T F x3Center Y R =
      (X - x3Center) * p3XSlope K W S T F X Y R := by
  unfold p3EndpointExcess p3XSlope alignedAdjugateQuadratic
    alignedDeterminant x3Center
  ring

private theorem p3_y_step
    (U K W S T F Y R : ℝ) :
    p3EndpointExcess U K W S T F x3Center Y R -
        p3EndpointExcess U K W S T F x3Center y3Center R =
      (Y - y3Center) * p3YSlope U K S T F Y R := by
  unfold p3EndpointExcess p3YSlope alignedAdjugateQuadratic
    alignedDeterminant x3Center y3Center
  ring

private theorem p3_r_step
    (U K W S T F R : ℝ) :
    p3EndpointExcess U K W S T F x3Center y3Center R -
        p3EndpointExcess U K W S T F x3Center y3Center r3Center =
      (R - r3Center) * p3RSlope U K W S T R := by
  unfold p3EndpointExcess p3RSlope alignedAdjugateQuadratic
    alignedDeterminant x3Center y3Center r3Center
  ring

private theorem p3_u_step (U K W S T F : ℝ) :
    p3EndpointExcess U K W S T F x3Center y3Center r3Center -
        p3EndpointExcess uCenter K W S T F x3Center y3Center r3Center =
      (U - uCenter) * p3USlope W T F := by
  unfold p3EndpointExcess p3USlope alignedAdjugateQuadratic
    alignedDeterminant x3Center y3Center r3Center uCenter
  ring

private theorem p3_k_step (K W S T F : ℝ) :
    p3EndpointExcess uCenter K W S T F x3Center y3Center r3Center -
        p3EndpointExcess uCenter kCenter W S T F
          x3Center y3Center r3Center =
      (K - kCenter) * p3KSlope K S T F := by
  unfold p3EndpointExcess p3KSlope alignedAdjugateQuadratic
    alignedDeterminant x3Center y3Center r3Center uCenter kCenter
  ring

private theorem p3_w_step (W S T F : ℝ) :
    p3EndpointExcess uCenter kCenter W S T F
        x3Center y3Center r3Center -
      p3EndpointExcess uCenter kCenter wCenter S T F
        x3Center y3Center r3Center =
      (W - wCenter) * p3WSlope S F := by
  unfold p3EndpointExcess p3WSlope alignedAdjugateQuadratic
    alignedDeterminant x3Center y3Center r3Center uCenter kCenter wCenter
  ring

private theorem p3_s_step (S T F : ℝ) :
    p3EndpointExcess uCenter kCenter wCenter S T F
        x3Center y3Center r3Center -
      p3EndpointExcess uCenter kCenter wCenter sCenter T F
        x3Center y3Center r3Center =
      (S - sCenter) * p3SSlope S T := by
  unfold p3EndpointExcess p3SSlope alignedAdjugateQuadratic
    alignedDeterminant x3Center y3Center r3Center uCenter kCenter wCenter
    sCenter
  ring

private theorem p3_t_step (T F : ℝ) :
    p3EndpointExcess uCenter kCenter wCenter sCenter T F
        x3Center y3Center r3Center -
      p3EndpointExcess uCenter kCenter wCenter sCenter tCenter F
        x3Center y3Center r3Center =
      (T - tCenter) * p3TSlope T := by
  unfold p3EndpointExcess p3TSlope alignedAdjugateQuadratic
    alignedDeterminant x3Center y3Center r3Center uCenter kCenter wCenter
    sCenter tCenter
  ring

private theorem p3_f_step (F F0 : ℝ) :
    p3EndpointExcess uCenter kCenter wCenter sCenter tCenter F
        x3Center y3Center r3Center -
      p3EndpointExcess uCenter kCenter wCenter sCenter tCenter F0
        x3Center y3Center r3Center =
      (F - F0) * p3FSlope := by
  unfold p3EndpointExcess p3FSlope alignedAdjugateQuadratic
    alignedDeterminant x3Center y3Center r3Center uCenter kCenter wCenter
    sCenter tCenter
  ring

set_option maxHeartbeats 1200000 in
private theorem p3_slope_bounds
    (h43 : (-4 / 1000 : ℝ) < a43 ∧ a43 < -2 / 1000) :
    |p3XSlope skewMinus weakMinus crossSumMinus crossDifferenceMinus
        e44m xThree yThree (-a43)| ≤ (1 / 1000 : ℝ) ∧
      |p3YSlope strongMinus skewMinus crossSumMinus crossDifferenceMinus
        e44m yThree (-a43)| ≤ (1 / 50 : ℝ) ∧
      |p3RSlope strongMinus skewMinus weakMinus crossSumMinus
        crossDifferenceMinus (-a43)| ≤ (3 / 1000 : ℝ) ∧
      |p3USlope weakMinus crossDifferenceMinus e44m| ≤
        (1 / 5000 : ℝ) ∧
      |p3KSlope skewMinus crossSumMinus crossDifferenceMinus e44m| ≤
        (1 / 500 : ℝ) ∧
      |p3WSlope crossSumMinus e44m| ≤ (1 / 50 : ℝ) ∧
      |p3SSlope crossSumMinus crossDifferenceMinus| ≤
        (1 / 2000 : ℝ) ∧
      |p3TSlope crossDifferenceMinus| ≤ (1 / 200 : ℝ) := by
  rcases negative_endpoint_aligned_bounds with
    ⟨hUL, hUU, hKL, hKU, hWL, hWU, hSL, hSU, hTL, hTU⟩
  rcases alternating_aligned_bounds with
    ⟨_hx1L, _hx1U, _hy1L, _hy1U, hxL, hxU, hyL, hyU⟩
  have hRL : (2 / 1000 : ℝ) < -a43 := by linarith [h43.2]
  have hRU : -a43 < (4 / 1000 : ℝ) := by linarith [h43.1]
  have hFL := e44m_lower
  have hFU := e44m_upper
  have hXsum : (1 : ℝ) ≤ xThree + x3Center ∧
      xThree + x3Center ≤ 11 / 10 := by
    simp only [x3Center]
    constructor <;> linarith
  have hYsum : (1 / 10 : ℝ) ≤ yThree + y3Center ∧
      yThree + y3Center ≤ 3 / 25 := by
    simp only [y3Center]
    constructor <;> linarith
  have hRsum : (1 / 200 : ℝ) ≤ -a43 + r3Center ∧
      -a43 + r3Center ≤ 7 / 1000 := by
    simp only [r3Center]
    constructor <;> linarith
  have hKsum : (3 / 20 : ℝ) ≤ skewMinus + kCenter ∧
      skewMinus + kCenter ≤ 4 / 25 := by
    simp only [kCenter]
    constructor <;> linarith
  have hT2 := positive_sq_bounds (by norm_num) hTL.le hTU.le
  have hS2 := positive_sq_bounds (by norm_num) hSL.le hSU.le
  have hK2 := positive_sq_bounds (by norm_num) hKL.le hKU.le
  have hFW := positive_mul_bounds (by norm_num) (by norm_num)
    hFL.le hFU.le hWL.le hWU.le
  have hFK := positive_mul_bounds (by norm_num) (by norm_num)
    hFL.le hFU.le hKL.le hKU.le
  have hST := positive_mul_bounds (by norm_num) (by norm_num)
    hSL.le hSU.le hTL.le hTU.le
  have hWS := positive_mul_bounds (by norm_num) (by norm_num)
    hWL.le hWU.le hSL.le hSU.le
  have hKT := positive_mul_bounds (by norm_num) (by norm_num)
    hKL.le hKU.le hTL.le hTU.le
  have hFUprod := positive_mul_bounds (by norm_num) (by norm_num)
    hFL.le hFU.le hUL.le hUU.le
  have hKS := positive_mul_bounds (by norm_num) (by norm_num)
    hKL.le hKU.le hSL.le hSU.le
  have hUT := positive_mul_bounds (by norm_num) (by norm_num)
    hUL.le hUU.le hTL.le hTU.le
  have hUW := positive_mul_bounds (by norm_num) (by norm_num)
    hUL.le hUU.le hWL.le hWU.le
  have hFWX := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hFL.le hFU.le hWL.le hWU.le hXsum.1 hXsum.2
  have hTTX := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hTL.le hTU.le hTL.le hTU.le hXsum.1 hXsum.2
  have hFKY := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hFL.le hFU.le hKL.le hKU.le hyL.le hyU.le
  have hSTY := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hSL.le hSU.le hTL.le hTU.le hyL.le hyU.le
  have hWSR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hWL.le hWU.le hSL.le hSU.le hRL.le hRU.le
  have hKTR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hKL.le hKU.le hTL.le hTU.le hRL.le hRU.le
  have hFUY := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hFL.le hFU.le hUL.le hUU.le hYsum.1 hYsum.2
  have hSSY := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hSL.le hSU.le hSL.le hSU.le hYsum.1 hYsum.2
  have hKSR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hKL.le hKU.le hSL.le hSU.le hRL.le hRU.le
  have hUTR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hUL.le hUU.le hTL.le hTU.le hRL.le hRU.le
  have hUWR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hUL.le hUU.le hWL.le hWU.le hRsum.1 hRsum.2
  have hKKR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hKL.le hKU.le hKL.le hKU.le hRsum.1 hRsum.2
  have hFKsum := positive_mul_bounds (by norm_num) (by norm_num)
    hFL.le hFU.le hKsum.1 hKsum.2
  simp only [x3Center, y3Center, r3Center, kCenter] at *
  constructor
  · rw [abs_le]
    constructor <;> unfold p3XSlope x3Center <;>
      nlinarith only [hFWX.1, hFWX.2, hTTX.1, hTTX.2,
        hFKY.1, hFKY.2, hSTY.1, hSTY.2,
        hWSR.1, hWSR.2, hKTR.1, hKTR.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold p3YSlope x3Center y3Center <;>
      nlinarith only [hFUY.1, hFUY.2, hSSY.1, hSSY.2,
        hFK.1, hFK.2, hST.1, hST.2,
        hKSR.1, hKSR.2, hUTR.1, hUTR.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold p3RSlope x3Center y3Center r3Center <;>
      nlinarith only [hUWR.1, hUWR.2, hKKR.1, hKKR.2,
        hWS.1, hWS.2, hKT.1, hKT.2, hKS.1, hKS.2,
        hUT.1, hUT.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold p3USlope y3Center r3Center <;>
      nlinarith only [hFW.1, hFW.2, hT2.1, hT2.2,
        hFL.le, hFU.le, hTL.le, hTU.le, hWL.le, hWU.le]
  constructor
  · rw [abs_le]
    constructor <;> unfold p3KSlope x3Center y3Center r3Center kCenter <;>
      nlinarith only [hFKsum.1, hFKsum.2, hST.1, hST.2,
        hFL.le, hFU.le, hKL.le, hKU.le, hSL.le, hSU.le,
        hTL.le, hTU.le]
  constructor
  · rw [abs_le]
    constructor <;> unfold p3WSlope x3Center r3Center uCenter <;>
      nlinarith only [hS2.1, hS2.2, hFL.le, hFU.le, hSL.le, hSU.le]
  constructor
  · rw [abs_le]
    constructor <;> unfold p3SSlope x3Center y3Center r3Center
      kCenter wCenter sCenter <;>
      nlinarith only [hSL.le, hSU.le, hTL.le, hTU.le]
  · rw [abs_le]
    constructor <;> unfold p3TSlope x3Center y3Center r3Center
      uCenter kCenter sCenter tCenter <;>
      nlinarith only [hTL.le, hTU.le]

private theorem p3_endpoint_excess_lt_of_cross43_bounds
    (h43 : (-4 / 1000 : ℝ) < a43 ∧ a43 < -2 / 1000) :
    p3EndpointExcess strongMinus skewMinus weakMinus crossSumMinus
        crossDifferenceMinus e44m xThree yThree (-a43) <
      (3 / 20000 : ℝ) := by
  rcases negative_endpoint_center_radii with
    ⟨hRU, hRK, hRW, hRS, hRT⟩
  rcases p3_coordinate_radii_of_cross43_bounds h43 with
    ⟨hRX, hRY, hRR⟩
  rcases p3_slope_bounds h43 with
    ⟨hSX, hSY, hSR, hSU, hSK, hSW, hSS, hST⟩
  have hXstep :
      p3EndpointExcess strongMinus skewMinus weakMinus crossSumMinus
          crossDifferenceMinus e44m xThree yThree (-a43) -
        p3EndpointExcess strongMinus skewMinus weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center yThree (-a43) ≤
        (21 / 200000 : ℝ) * (1 / 1000) := by
    rw [p3_x_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRX hSX
  have hYstep :
      p3EndpointExcess strongMinus skewMinus weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center yThree (-a43) -
        p3EndpointExcess strongMinus skewMinus weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center (-a43) ≤
        (3 / 20000 : ℝ) * (1 / 50) := by
    rw [p3_y_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRY hSY
  have hRstep :
      p3EndpointExcess strongMinus skewMinus weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center (-a43) -
        p3EndpointExcess strongMinus skewMinus weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center r3Center ≤
        (1 / 1000 : ℝ) * (3 / 1000) := by
    rw [p3_r_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRR hSR
  have hUstep :
      p3EndpointExcess strongMinus skewMinus weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center r3Center -
        p3EndpointExcess uCenter skewMinus weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center r3Center ≤
        (1088 / 1000000 : ℝ) * (1 / 5000) := by
    rw [p3_u_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRU hSU
  have hKstep :
      p3EndpointExcess uCenter skewMinus weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center r3Center -
        p3EndpointExcess uCenter kCenter weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center r3Center ≤
        (1030 / 1000000 : ℝ) * (1 / 500) := by
    rw [p3_k_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRK hSK
  have hWstep :
      p3EndpointExcess uCenter kCenter weakMinus crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center r3Center -
        p3EndpointExcess uCenter kCenter wCenter crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center r3Center ≤
        (1088 / 1000000 : ℝ) * (1 / 50) := by
    rw [p3_w_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRW hSW
  have hSstep :
      p3EndpointExcess uCenter kCenter wCenter crossSumMinus
          crossDifferenceMinus e44m x3Center y3Center r3Center -
        p3EndpointExcess uCenter kCenter wCenter sCenter
          crossDifferenceMinus e44m x3Center y3Center r3Center ≤
        (7447 / 2000000 : ℝ) * (1 / 2000) := by
    rw [p3_s_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRS hSS
  have hTstep :
      p3EndpointExcess uCenter kCenter wCenter sCenter
          crossDifferenceMinus e44m x3Center y3Center r3Center -
        p3EndpointExcess uCenter kCenter wCenter sCenter tCenter e44m
          x3Center y3Center r3Center ≤
        (3947 / 2000000 : ℝ) * (1 / 200) := by
    rw [p3_t_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRT hST
  have hFslope : p3FSlope < 0 := by
    norm_num [p3FSlope, uCenter, kCenter, wCenter, x3Center, y3Center]
  have hFstep :
      p3EndpointExcess uCenter kCenter wCenter sCenter tCenter e44m
          x3Center y3Center r3Center ≤
        p3EndpointExcess uCenter kCenter wCenter sCenter tCenter (12 / 25)
          x3Center y3Center r3Center := by
    rw [← sub_nonpos]
    rw [p3_f_step]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith [e44m_lower]) hFslope.le
  have hCenter :
      p3EndpointExcess uCenter kCenter wCenter sCenter tCenter (12 / 25)
          x3Center y3Center r3Center < (17 / 200000 : ℝ) := by
    norm_num [p3EndpointExcess, alignedAdjugateQuadratic,
      alignedDeterminant, uCenter, kCenter, wCenter, sCenter, tCenter,
      x3Center, y3Center, r3Center]
  have hBudget :
      (21 / 200000 : ℝ) * (1 / 1000) +
        (3 / 20000 : ℝ) * (1 / 50) +
        (1 / 1000 : ℝ) * (3 / 1000) +
        (1088 / 1000000 : ℝ) * (1 / 5000) +
        (1030 / 1000000 : ℝ) * (1 / 500) +
        (1088 / 1000000 : ℝ) * (1 / 50) +
        (7447 / 2000000 : ℝ) * (1 / 2000) +
        (3947 / 2000000 : ℝ) * (1 / 200) +
        (17 / 200000 : ℝ) < 3 / 20000 := by
    norm_num
  linarith only [hXstep, hYstep, hRstep, hUstep, hKstep, hWstep,
    hSstep, hTstep, hFstep, hCenter, hBudget]

private theorem p3_endpoint_excess_lt :
    j33 - (2115 / 10000 : ℝ) * evenDetMinus < 3 / 20000 := by
  rw [p3_endpoint_excess_eq]
  exact p3_endpoint_excess_lt_of_cross43_bounds (by
    simpa only [a43] using factorTwoIntrinsicFourP45Cross43_bounds)

/-! ## The transformed odd reserve -/

private def clean11 : ℝ := yoshidaEndpointOddLowGram11
private def clean13 : ℝ := yoshidaEndpointOddLowGram13
private def clean33 : ℝ := yoshidaEndpointOddLowGram33
private def perturb11 : ℝ :=
  factorTwoCenteredSymmetricPerturbation centeredP1
private def perturb13Neg : ℝ :=
  -factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3
private def perturb33Neg : ℝ :=
  -factorTwoCenteredSymmetricPerturbation centeredP3

private def oddTransformedQ (A B C P R T : ℝ) : ℝ :=
  (C + T) ^ 2 * (A + P) -
    2 * (C + T) * (B + R) * (B - R) +
    (B + R) ^ 2 * (C - T)

private theorem transformedOddPlus_eq_clean_coordinates :
    transformedOddPlus =
      oddTransformedQ clean11 clean13 clean33 perturb11
        perturb13Neg perturb33Neg := by
  unfold transformedOddPlus oddTransformedQ clean11 clean13 clean33
    perturb11 perturb13Neg perturb33Neg o11p o13p o33p o13m o33m
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  ring

private theorem odd_clean_perturbation_boxes :
    (1778 / 10000 : ℝ) < clean11 ∧ clean11 < 179 / 1000 ∧
      (1 / 5 : ℝ) < clean13 ∧ clean13 < 2002 / 10000 ∧
      (3315 / 10000 : ℝ) < clean33 ∧ clean33 < 333 / 1000 ∧
      (14 / 1000 : ℝ) < perturb11 ∧ perturb11 < 20 / 1000 ∧
      (9 / 1000 : ℝ) < perturb13Neg ∧ perturb13Neg < 11 / 1000 ∧
      (117 / 1000 : ℝ) < perturb33Neg ∧ perturb33Neg < 120 / 1000 := by
  have hc11L := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hc13 := yoshidaEndpointOddLowGram13_bounds
  have hc33L := yoshidaEndpointOddLowGram33_gt_3315_div_10000
  have hcU := yoshidaEndpointOddLowGram_diagonal_upper_bounds
  rcases oddStructuralLow_perturbation_sharp_bounds with
    ⟨hp11, hp13, hp33⟩
  unfold clean11 clean13 clean33 perturb11 perturb13Neg perturb33Neg
  constructor
  · exact hc11L
  constructor
  · exact hcU.1
  constructor
  · exact hc13.1
  constructor
  · exact hc13.2
  constructor
  · exact hc33L
  constructor
  · exact hcU.2
  constructor
  · exact hp11.1
  constructor
  · exact hp11.2
  constructor
  · linarith [hp13.2]
  constructor
  · linarith [hp13.1]
  constructor
  · linarith [hp33.2]
  · linarith [hp33.1]

private theorem oddQ_a_step (A B C P R T A0 : ℝ) :
    oddTransformedQ A B C P R T - oddTransformedQ A0 B C P R T =
      (A - A0) * (C + T) ^ 2 := by
  unfold oddTransformedQ
  ring

private theorem oddQ_b_step (B C P R T B0 A0 : ℝ) :
    oddTransformedQ A0 B C P R T - oddTransformedQ A0 B0 C P R T =
      (B0 - B) *
        ((B + B0) * C + 3 * (B + B0) * T - 2 * C * R + 2 * R * T) := by
  unfold oddTransformedQ
  ring

private theorem oddQ_c_step (C P R T C0 B0 A0 : ℝ) :
    oddTransformedQ A0 B0 C P R T - oddTransformedQ A0 B0 C0 P R T =
      (C - C0) *
        (A0 * (C + C0) + 2 * A0 * T - B0 ^ 2 + 2 * B0 * R +
          P * (C + C0) + 2 * P * T + 3 * R ^ 2) := by
  unfold oddTransformedQ
  ring

private theorem oddQ_p_step (P R T P0 C0 B0 A0 : ℝ) :
    oddTransformedQ A0 B0 C0 P R T -
        oddTransformedQ A0 B0 C0 P0 R T =
      (P - P0) * (C0 + T) ^ 2 := by
  unfold oddTransformedQ
  ring

private theorem oddQ_r_step (R T R0 P0 C0 B0 A0 : ℝ) :
    oddTransformedQ A0 B0 C0 P0 R T -
        oddTransformedQ A0 B0 C0 P0 R0 T =
      (R - R0) *
        (2 * B0 * (C0 - T) + (R + R0) * (3 * C0 + T)) := by
  unfold oddTransformedQ
  ring

private theorem oddQ_t_step (T T0 R0 P0 C0 B0 A0 : ℝ) :
    oddTransformedQ A0 B0 C0 P0 R0 T -
        oddTransformedQ A0 B0 C0 P0 R0 T0 =
      (T - T0) *
        (2 * A0 * C0 + (A0 + P0) * (T + T0) - 3 * B0 ^ 2 -
          2 * B0 * R0 + 2 * C0 * P0 + R0 ^ 2) := by
  unfold oddTransformedQ
  ring

private theorem transformedOddPlus_gt_three_div_two_fifty :
    (3 / 250 : ℝ) < transformedOddPlus := by
  rw [transformedOddPlus_eq_clean_coordinates]
  rcases odd_clean_perturbation_boxes with
    ⟨hAL, _hAU, hBL, hBU, hCL, _hCU, hPL, _hPU,
      hRL, hRU, hTL, _hTU⟩
  have hCpos : 0 < clean33 := lt_trans (by norm_num) hCL
  have hTpos : 0 < perturb33Neg := lt_trans (by norm_num) hTL
  have hRpos : 0 < perturb13Neg := lt_trans (by norm_num) hRL
  have hBpos : 0 < clean13 := lt_trans (by norm_num) hBL
  have hAstep :
      oddTransformedQ (1778 / 10000) clean13 clean33 perturb11
          perturb13Neg perturb33Neg <
        oddTransformedQ clean11 clean13 clean33 perturb11
          perturb13Neg perturb33Neg := by
    rw [← sub_pos]
    rw [oddQ_a_step]
    exact mul_pos (by linarith) (sq_pos_of_pos (add_pos hCpos hTpos))
  have hBfactor :
      0 < (clean13 + 2002 / 10000) * clean33 +
          3 * (clean13 + 2002 / 10000) * perturb33Neg -
          2 * clean33 * perturb13Neg +
          2 * perturb13Neg * perturb33Neg := by
    have hleft : 0 < clean13 + 2002 / 10000 - 2 * perturb13Neg := by
      linarith
    have hright : 0 < 3 * (clean13 + 2002 / 10000) +
        2 * perturb13Neg := by positivity
    nlinarith [mul_pos hCpos hleft, mul_pos hTpos hright]
  have hBstep :
      oddTransformedQ (1778 / 10000) (2002 / 10000) clean33 perturb11
          perturb13Neg perturb33Neg <
        oddTransformedQ (1778 / 10000) clean13 clean33 perturb11
          perturb13Neg perturb33Neg := by
    rw [← sub_pos]
    rw [oddQ_b_step]
    exact mul_pos (by linarith) hBfactor
  have hCslope :
      0 < (1778 / 10000 : ℝ) * (clean33 + 3315 / 10000) +
          2 * (1778 / 10000) * perturb33Neg - (2002 / 10000) ^ 2 +
          2 * (2002 / 10000) * perturb13Neg +
          perturb11 * (clean33 + 3315 / 10000) +
          2 * perturb11 * perturb33Neg + 3 * perturb13Neg ^ 2 := by
    have hcore : (2002 / 10000 : ℝ) ^ 2 <
        (1778 / 10000) * (clean33 + 3315 / 10000) := by
      calc
        _ < (1778 / 10000 : ℝ) *
            ((3315 / 10000) + (3315 / 10000)) := by norm_num
        _ < _ := mul_lt_mul_of_pos_left (by linarith) (by norm_num)
    have hPpos : 0 < perturb11 := lt_trans (by norm_num) hPL
    have hsumC : 0 < clean33 + 3315 / 10000 :=
      add_pos hCpos (by norm_num)
    have h1 : 0 < 2 * (1778 / 10000 : ℝ) * perturb33Neg :=
      mul_pos (by norm_num) hTpos
    have h2 : 0 < 2 * (2002 / 10000 : ℝ) * perturb13Neg :=
      mul_pos (by norm_num) hRpos
    have h3 : 0 < perturb11 * (clean33 + 3315 / 10000) :=
      mul_pos hPpos hsumC
    have h4 : 0 < 2 * perturb11 * perturb33Neg :=
      mul_pos (mul_pos (by norm_num) hPpos) hTpos
    have h5 : 0 < 3 * perturb13Neg ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos hRpos)
    nlinarith only [hcore, h1, h2, h3, h4, h5]
  have hCstep :
      oddTransformedQ (1778 / 10000) (2002 / 10000) (3315 / 10000)
          perturb11 perturb13Neg perturb33Neg <
        oddTransformedQ (1778 / 10000) (2002 / 10000) clean33
          perturb11 perturb13Neg perturb33Neg := by
    rw [← sub_pos]
    rw [oddQ_c_step]
    exact mul_pos (by linarith) hCslope
  have hPstep :
      oddTransformedQ (1778 / 10000) (2002 / 10000) (3315 / 10000)
          (14 / 1000) perturb13Neg perturb33Neg <
        oddTransformedQ (1778 / 10000) (2002 / 10000) (3315 / 10000)
          perturb11 perturb13Neg perturb33Neg := by
    rw [← sub_pos]
    rw [oddQ_p_step]
    exact mul_pos (by linarith) (sq_pos_of_pos (add_pos (by norm_num) hTpos))
  have hRstep :
      oddTransformedQ (1778 / 10000) (2002 / 10000) (3315 / 10000)
          (14 / 1000) (9 / 1000) perturb33Neg <
        oddTransformedQ (1778 / 10000) (2002 / 10000) (3315 / 10000)
          (14 / 1000) perturb13Neg perturb33Neg := by
    rw [← sub_pos]
    rw [oddQ_r_step]
    apply mul_pos (by linarith)
    have hdiff : 0 < (3315 / 10000 : ℝ) - perturb33Neg := by linarith
    positivity
  have hTslope :
      0 < 2 * (1778 / 10000 : ℝ) * (3315 / 10000) +
          ((1778 / 10000) + (14 / 1000)) *
            (perturb33Neg + 117 / 1000) - 3 * (2002 / 10000) ^ 2 -
          2 * (2002 / 10000) * (9 / 1000) +
          2 * (3315 / 10000) * (14 / 1000) + (9 / 1000) ^ 2 := by
    nlinarith [hTL]
  have hTstep :
      oddTransformedQ (1778 / 10000) (2002 / 10000) (3315 / 10000)
          (14 / 1000) (9 / 1000) (117 / 1000) <
        oddTransformedQ (1778 / 10000) (2002 / 10000) (3315 / 10000)
          (14 / 1000) (9 / 1000) perturb33Neg := by
    rw [← sub_pos]
    rw [oddQ_t_step]
    exact mul_pos (by linarith) hTslope
  have hCorner : (3 / 250 : ℝ) <
      oddTransformedQ (1778 / 10000) (2002 / 10000) (3315 / 10000)
        (14 / 1000) (9 / 1000) (117 / 1000) := by
    norm_num [oddTransformedQ]
  linarith

/-! ## A centered telescope for the transformed reserve

The transformed second coordinate is negative.  Writing its opposite as a
positive coordinate keeps every interval multiplication below in the
positive orthant.
-/

private def transformedPositiveExcess
    (U K W S T F X R Z Q : ℝ) : ℝ :=
  transformedExcess U K W S T F X (-R) Z Q

private theorem transformed_excess_eq_positive :
    transformedExcess strongMinus skewMinus weakMinus crossSumMinus
        crossDifferenceMinus e44m transformedX transformedY transformedZ
        transformedOddPlus =
      transformedPositiveExcess strongMinus skewMinus weakMinus crossSumMinus
        crossDifferenceMinus e44m transformedX (-transformedY) transformedZ
        transformedOddPlus := by
  unfold transformedPositiveExcess
  ring

private theorem transformed_coordinate_boxes :
    (1382 / 10000 : ℝ) < transformedX ∧
      transformedX < 142 / 1000 ∧
      (393 / 100000 : ℝ) < -transformedY ∧
      -transformedY < 423 / 100000 ∧
      (636 / 10000 : ℝ) < transformedZ ∧
      transformedZ < 661 / 10000 := by
  rcases factorTwoIntrinsicOddPhaseLow_minus_entry_bounds with
    ⟨_ho11L, _ho11U, ho13L, ho13U, ho33L, ho33U⟩
  rcases alternating_aligned_bounds with
    ⟨hx1L, hx1U, hy1L, hy1U, hx3L, hx3U, hy3L, hy3U⟩
  have h41 : (141 / 1000 : ℝ) < a41 ∧ a41 < 144 / 1000 := by
    simpa only [a41] using factorTwoIntrinsicFourP45Cross41_bounds
  have h43 : (-4 / 1000 : ℝ) < a43 ∧ a43 < -2 / 1000 := by
    simpa only [a43] using factorTwoIntrinsicFourP45Cross43_bounds
  have hr43L : (2 / 1000 : ℝ) < -a43 := by linarith
  have hr43U : -a43 < (4 / 1000 : ℝ) := by linarith
  have h33x1 := positive_mul_bounds (by norm_num) (by norm_num)
    ho33L.le ho33U.le hx1L.le hx1U.le
  have h13x3 := positive_mul_bounds (by norm_num) (by norm_num)
    ho13L.le ho13U.le hx3L.le hx3U.le
  have h33y1 := positive_mul_bounds (by norm_num) (by norm_num)
    ho33L.le ho33U.le hy1L.le hy1U.le
  have h13y3 := positive_mul_bounds (by norm_num) (by norm_num)
    ho13L.le ho13U.le hy3L.le hy3U.le
  have h33a41 := positive_mul_bounds (by norm_num) (by norm_num)
    ho33L.le ho33U.le h41.1.le h41.2.le
  have h13r43 := positive_mul_bounds (by norm_num) (by norm_num)
    ho13L.le ho13U.le hr43L.le hr43U.le
  unfold transformedX transformedY transformedZ
  simp only [o33m, o13m]
  constructor
  · nlinarith only [h33x1.1, h13x3.2]
  constructor
  · nlinarith only [h33x1.2, h13x3.1]
  constructor
  · nlinarith only [h13y3.1, h33y1.2]
  constructor
  · nlinarith only [h13y3.2, h33y1.1]
  constructor
  · nlinarith only [h33a41.1, h13r43.1]
  · nlinarith only [h33a41.2, h13r43.2]

private def transformedXCenter : ℝ := 1401 / 10000
private def transformedRCenter : ℝ := 408 / 100000
private def transformedZCenter : ℝ := 6485 / 100000

private theorem transformed_coordinate_radii :
    |transformedX - transformedXCenter| ≤ (19 / 10000 : ℝ) ∧
      |-transformedY - transformedRCenter| ≤ (15 / 100000 : ℝ) ∧
      |transformedZ - transformedZCenter| ≤ (1 / 800 : ℝ) := by
  rcases transformed_coordinate_boxes with
    ⟨hXL, hXU, hRL, hRU, hZL, hZU⟩
  repeat' apply And.intro
  all_goals rw [abs_le]
  all_goals simp only [transformedXCenter, transformedRCenter,
    transformedZCenter]
  all_goals constructor <;> norm_num at * <;> linarith

private def transformedXSlope
    (K W S T F X R Z : ℝ) : ℝ :=
  ((F * W - T ^ 2) * (X + transformedXCenter) +
      2 * (F * K + S * T) * R -
      2 * (W * S + K * T) * Z) / 4

private def transformedRSlope
    (U K S T F R Z : ℝ) : ℝ :=
  ((F * U - S ^ 2) * (R + transformedRCenter) +
      2 * (F * K + S * T) * transformedXCenter -
      2 * (K * S + U * T) * Z) / 4

private def transformedZSlope
    (U K W S T Z : ℝ) : ℝ :=
  ((U * W - K ^ 2) * (Z + transformedZCenter) -
      2 * (W * S + K * T) * transformedXCenter -
      2 * (K * S + U * T) * transformedRCenter) / 4

private def transformedUSlope (W T F : ℝ) : ℝ :=
  (F * transformedRCenter ^ 2 -
      2 * T * transformedRCenter * transformedZCenter +
      W * transformedZCenter ^ 2 -
      (3 / 250 : ℝ) * (F * W - T ^ 2)) / 4

private def transformedKSlope (K S T F : ℝ) : ℝ :=
  (2 * F * transformedXCenter * transformedRCenter -
      2 * T * transformedXCenter * transformedZCenter -
      2 * S * transformedRCenter * transformedZCenter -
      (K + kCenter) * transformedZCenter ^ 2 +
      (3 / 250 : ℝ) * F * (K + kCenter) +
      2 * (3 / 250 : ℝ) * S * T) / 4

private def transformedWSlope (S F : ℝ) : ℝ :=
  (F * transformedXCenter ^ 2 -
      2 * S * transformedXCenter * transformedZCenter +
      uCenter * transformedZCenter ^ 2 -
      (3 / 250 : ℝ) * (F * uCenter - S ^ 2)) / 4

private def transformedSSlope (S T : ℝ) : ℝ :=
  (-(S + sCenter) * transformedRCenter ^ 2 +
      2 * T * transformedXCenter * transformedRCenter -
      2 * wCenter * transformedXCenter * transformedZCenter -
      2 * kCenter * transformedRCenter * transformedZCenter +
      (3 / 250 : ℝ) * wCenter * (S + sCenter) +
      2 * (3 / 250 : ℝ) * kCenter * T) / 4

private def transformedTSlope (T : ℝ) : ℝ :=
  (-(T + tCenter) * transformedXCenter ^ 2 +
      2 * sCenter * transformedXCenter * transformedRCenter -
      2 * kCenter * transformedXCenter * transformedZCenter -
      2 * uCenter * transformedRCenter * transformedZCenter +
      (3 / 250 : ℝ) * uCenter * (T + tCenter) +
      2 * (3 / 250 : ℝ) * kCenter * sCenter) / 4

private def transformedFSlope : ℝ :=
  (wCenter * transformedXCenter ^ 2 +
      uCenter * transformedRCenter ^ 2 +
      2 * kCenter * transformedXCenter * transformedRCenter -
      (3 / 250 : ℝ) * (uCenter * wCenter - kCenter ^ 2)) / 4

private theorem transformed_q_step
    (U K W S T F X R Z Q : ℝ) :
    transformedPositiveExcess U K W S T F X R Z Q -
        transformedPositiveExcess U K W S T F X R Z (3 / 250) =
      -(Q - 3 / 250) * alignedDeterminant U K W S T F := by
  unfold transformedPositiveExcess transformedExcess
  ring

private theorem transformed_x_step
    (U K W S T F X R Z : ℝ) :
    transformedPositiveExcess U K W S T F X R Z (3 / 250) -
        transformedPositiveExcess U K W S T F transformedXCenter R Z
          (3 / 250) =
      (X - transformedXCenter) * transformedXSlope K W S T F X R Z := by
  unfold transformedPositiveExcess transformedExcess transformedXSlope
    alignedAdjugateQuadratic alignedDeterminant transformedXCenter
  ring

private theorem transformed_r_step
    (U K W S T F R Z : ℝ) :
    transformedPositiveExcess U K W S T F transformedXCenter R Z
        (3 / 250) -
      transformedPositiveExcess U K W S T F transformedXCenter
        transformedRCenter Z (3 / 250) =
      (R - transformedRCenter) * transformedRSlope U K S T F R Z := by
  unfold transformedPositiveExcess transformedExcess transformedRSlope
    alignedAdjugateQuadratic alignedDeterminant transformedXCenter
    transformedRCenter
  ring

private theorem transformed_z_step
    (U K W S T F Z : ℝ) :
    transformedPositiveExcess U K W S T F transformedXCenter
        transformedRCenter Z (3 / 250) -
      transformedPositiveExcess U K W S T F transformedXCenter
        transformedRCenter transformedZCenter (3 / 250) =
      (Z - transformedZCenter) * transformedZSlope U K W S T Z := by
  unfold transformedPositiveExcess transformedExcess transformedZSlope
    alignedAdjugateQuadratic alignedDeterminant transformedXCenter
    transformedRCenter transformedZCenter
  ring

private theorem transformed_u_step (U K W S T F : ℝ) :
    transformedPositiveExcess U K W S T F transformedXCenter
        transformedRCenter transformedZCenter (3 / 250) -
      transformedPositiveExcess uCenter K W S T F transformedXCenter
        transformedRCenter transformedZCenter (3 / 250) =
      (U - uCenter) * transformedUSlope W T F := by
  unfold transformedPositiveExcess transformedExcess transformedUSlope
    alignedAdjugateQuadratic alignedDeterminant transformedXCenter
    transformedRCenter transformedZCenter uCenter
  ring

private theorem transformed_k_step (K W S T F : ℝ) :
    transformedPositiveExcess uCenter K W S T F transformedXCenter
        transformedRCenter transformedZCenter (3 / 250) -
      transformedPositiveExcess uCenter kCenter W S T F transformedXCenter
        transformedRCenter transformedZCenter (3 / 250) =
      (K - kCenter) * transformedKSlope K S T F := by
  unfold transformedPositiveExcess transformedExcess transformedKSlope
    alignedAdjugateQuadratic alignedDeterminant transformedXCenter
    transformedRCenter transformedZCenter uCenter kCenter
  ring

private theorem transformed_w_step (W S T F : ℝ) :
    transformedPositiveExcess uCenter kCenter W S T F transformedXCenter
        transformedRCenter transformedZCenter (3 / 250) -
      transformedPositiveExcess uCenter kCenter wCenter S T F
        transformedXCenter transformedRCenter transformedZCenter (3 / 250) =
      (W - wCenter) * transformedWSlope S F := by
  unfold transformedPositiveExcess transformedExcess transformedWSlope
    alignedAdjugateQuadratic alignedDeterminant transformedXCenter
    transformedRCenter transformedZCenter uCenter kCenter wCenter
  ring

private theorem transformed_s_step (S T F : ℝ) :
    transformedPositiveExcess uCenter kCenter wCenter S T F
        transformedXCenter transformedRCenter transformedZCenter (3 / 250) -
      transformedPositiveExcess uCenter kCenter wCenter sCenter T F
        transformedXCenter transformedRCenter transformedZCenter (3 / 250) =
      (S - sCenter) * transformedSSlope S T := by
  unfold transformedPositiveExcess transformedExcess transformedSSlope
    alignedAdjugateQuadratic alignedDeterminant transformedXCenter
    transformedRCenter transformedZCenter uCenter kCenter wCenter sCenter
  ring

private theorem transformed_t_step (T F : ℝ) :
    transformedPositiveExcess uCenter kCenter wCenter sCenter T F
        transformedXCenter transformedRCenter transformedZCenter (3 / 250) -
      transformedPositiveExcess uCenter kCenter wCenter sCenter tCenter F
        transformedXCenter transformedRCenter transformedZCenter (3 / 250) =
      (T - tCenter) * transformedTSlope T := by
  unfold transformedPositiveExcess transformedExcess transformedTSlope
    alignedAdjugateQuadratic alignedDeterminant transformedXCenter
    transformedRCenter transformedZCenter uCenter kCenter wCenter sCenter
    tCenter
  ring

private theorem transformed_f_step (F F0 : ℝ) :
    transformedPositiveExcess uCenter kCenter wCenter sCenter tCenter F
        transformedXCenter transformedRCenter transformedZCenter (3 / 250) -
      transformedPositiveExcess uCenter kCenter wCenter sCenter tCenter F0
        transformedXCenter transformedRCenter transformedZCenter (3 / 250) =
      (F - F0) * transformedFSlope := by
  unfold transformedPositiveExcess transformedExcess transformedFSlope
    alignedAdjugateQuadratic alignedDeterminant transformedXCenter
    transformedRCenter transformedZCenter uCenter kCenter wCenter sCenter
    tCenter
  ring

set_option maxHeartbeats 1200000 in
private theorem transformed_slope_bounds :
    |transformedXSlope skewMinus weakMinus crossSumMinus
        crossDifferenceMinus e44m transformedX (-transformedY) transformedZ| ≤
        (24 / 100000 : ℝ) ∧
      |transformedRSlope strongMinus skewMinus crossSumMinus
        crossDifferenceMinus e44m (-transformedY) transformedZ| ≤
        (12 / 10000 : ℝ) ∧
      |transformedZSlope strongMinus skewMinus weakMinus crossSumMinus
        crossDifferenceMinus transformedZ| ≤ (22 / 100000 : ℝ) ∧
      |transformedUSlope weakMinus crossDifferenceMinus e44m| ≤
        (1 / 100000 : ℝ) ∧
      |transformedKSlope skewMinus crossSumMinus crossDifferenceMinus e44m| ≤
        (4 / 100000 : ℝ) ∧
      |transformedWSlope crossSumMinus e44m| ≤ (43 / 100000 : ℝ) ∧
      |transformedSSlope crossSumMinus crossDifferenceMinus| ≤
        (1 / 50000 : ℝ) ∧
      |transformedTSlope crossDifferenceMinus| ≤
        (22 / 100000 : ℝ) := by
  rcases negative_endpoint_aligned_bounds with
    ⟨hUL, hUU, hKL, hKU, hWL, hWU, hSL, hSU, hTL, hTU⟩
  rcases transformed_coordinate_boxes with
    ⟨hXL, hXU, hRL, hRU, hZL, hZU⟩
  have hFL := e44m_lower
  have hFU := e44m_upper
  have hXsum : (2783 / 10000 : ℝ) ≤ transformedX + transformedXCenter ∧
      transformedX + transformedXCenter ≤ 2821 / 10000 := by
    simp only [transformedXCenter]
    constructor <;> linarith
  have hRsum : (801 / 100000 : ℝ) ≤
        -transformedY + transformedRCenter ∧
      -transformedY + transformedRCenter ≤ 831 / 100000 := by
    simp only [transformedRCenter]
    constructor <;> linarith
  have hZsum : (2569 / 20000 : ℝ) ≤
        transformedZ + transformedZCenter ∧
      transformedZ + transformedZCenter ≤ 2619 / 20000 := by
    simp only [transformedZCenter]
    constructor <;> linarith
  have hKsum : (1559 / 10000 : ℝ) ≤ skewMinus + kCenter ∧
      skewMinus + kCenter ≤ 1581 / 10000 := by
    simp only [kCenter]
    constructor <;> linarith
  have hT2 := positive_sq_bounds (by norm_num) hTL.le hTU.le
  have hS2 := positive_sq_bounds (by norm_num) hSL.le hSU.le
  have hK2 := positive_sq_bounds (by norm_num) hKL.le hKU.le
  have hFW := positive_mul_bounds (by norm_num) (by norm_num)
    hFL.le hFU.le hWL.le hWU.le
  have hFK := positive_mul_bounds (by norm_num) (by norm_num)
    hFL.le hFU.le hKL.le hKU.le
  have hST := positive_mul_bounds (by norm_num) (by norm_num)
    hSL.le hSU.le hTL.le hTU.le
  have hWS := positive_mul_bounds (by norm_num) (by norm_num)
    hWL.le hWU.le hSL.le hSU.le
  have hKT := positive_mul_bounds (by norm_num) (by norm_num)
    hKL.le hKU.le hTL.le hTU.le
  have hFUprod := positive_mul_bounds (by norm_num) (by norm_num)
    hFL.le hFU.le hUL.le hUU.le
  have hKS := positive_mul_bounds (by norm_num) (by norm_num)
    hKL.le hKU.le hSL.le hSU.le
  have hUT := positive_mul_bounds (by norm_num) (by norm_num)
    hUL.le hUU.le hTL.le hTU.le
  have hUW := positive_mul_bounds (by norm_num) (by norm_num)
    hUL.le hUU.le hWL.le hWU.le
  have hFWX := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hFL.le hFU.le hWL.le hWU.le hXsum.1 hXsum.2
  have hTTX := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hTL.le hTU.le hTL.le hTU.le hXsum.1 hXsum.2
  have hFKR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hFL.le hFU.le hKL.le hKU.le hRL.le hRU.le
  have hSTR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hSL.le hSU.le hTL.le hTU.le hRL.le hRU.le
  have hWSZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hWL.le hWU.le hSL.le hSU.le hZL.le hZU.le
  have hKTZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hKL.le hKU.le hTL.le hTU.le hZL.le hZU.le
  have hFUR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hFL.le hFU.le hUL.le hUU.le hRsum.1 hRsum.2
  have hSSR := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hSL.le hSU.le hSL.le hSU.le hRsum.1 hRsum.2
  have hKSZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hKL.le hKU.le hSL.le hSU.le hZL.le hZU.le
  have hUTZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hUL.le hUU.le hTL.le hTU.le hZL.le hZU.le
  have hUWZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hUL.le hUU.le hWL.le hWU.le hZsum.1 hZsum.2
  have hKKZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hKL.le hKU.le hKL.le hKU.le hZsum.1 hZsum.2
  have hFKsum := positive_mul_bounds (by norm_num) (by norm_num)
    hFL.le hFU.le hKsum.1 hKsum.2
  simp only [transformedXCenter, transformedRCenter, transformedZCenter,
    kCenter] at *
  constructor
  · rw [abs_le]
    constructor <;> unfold transformedXSlope transformedXCenter <;>
      nlinarith only [hFWX.1, hFWX.2, hTTX.1, hTTX.2,
        hFKR.1, hFKR.2, hSTR.1, hSTR.2,
        hWSZ.1, hWSZ.2, hKTZ.1, hKTZ.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold transformedRSlope transformedXCenter
      transformedRCenter <;>
      nlinarith only [hFUR.1, hFUR.2, hSSR.1, hSSR.2,
        hFK.1, hFK.2, hST.1, hST.2,
        hKSZ.1, hKSZ.2, hUTZ.1, hUTZ.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold transformedZSlope transformedXCenter
      transformedRCenter transformedZCenter <;>
      nlinarith only [hUWZ.1, hUWZ.2, hKKZ.1, hKKZ.2,
        hWS.1, hWS.2, hKT.1, hKT.2, hKS.1, hKS.2,
        hUT.1, hUT.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold transformedUSlope transformedRCenter
      transformedZCenter <;>
      nlinarith only [hFW.1, hFW.2, hT2.1, hT2.2,
        hFL.le, hFU.le, hTL.le, hTU.le, hWL.le, hWU.le]
  constructor
  · rw [abs_le]
    constructor <;> unfold transformedKSlope transformedXCenter
      transformedRCenter transformedZCenter kCenter <;>
      nlinarith only [hFKsum.1, hFKsum.2, hST.1, hST.2,
        hFL.le, hFU.le, hKL.le, hKU.le, hSL.le, hSU.le,
        hTL.le, hTU.le]
  constructor
  · rw [abs_le]
    constructor <;> unfold transformedWSlope transformedXCenter
      transformedZCenter uCenter <;>
      nlinarith only [hS2.1, hS2.2, hFL.le, hFU.le, hSL.le, hSU.le]
  constructor
  · rw [abs_le]
    constructor <;> unfold transformedSSlope transformedXCenter
      transformedRCenter transformedZCenter kCenter wCenter sCenter <;>
      nlinarith only [hSL.le, hSU.le, hTL.le, hTU.le]
  · rw [abs_le]
    constructor <;> unfold transformedTSlope transformedXCenter
      transformedRCenter transformedZCenter uCenter kCenter sCenter tCenter <;>
      nlinarith only [hTL.le, hTU.le]

private theorem evenDetMinus_pos : 0 < evenDetMinus := by
  have h := factorTwoIntrinsicSixP4SchurLeading_minus_pos
  have heq : evenDetMinus = factorTwoIntrinsicSixP4SchurLeading (-1) := by
    have hdiag : factorTwoIntrinsicSixP4Diagonal (-1) =
        factorTwoIntrinsicP4PhaseDiagonal (-1) := by rfl
    unfold evenDetMinus e00m e02m e22m e04m e24m e44m
      factorTwoIntrinsicSixP4SchurLeading factorTwoIntrinsicSixLowDet
      factorTwoIntrinsicSixP4Low0 factorTwoIntrinsicSixP4Low2
      symmetricDeterminant
    rw [hdiag]
    ring
  rw [heq]
  exact h

private theorem transformed_excess_lt_one_div_two_fifty_thousand :
    transformedExcess strongMinus skewMinus weakMinus crossSumMinus
        crossDifferenceMinus e44m transformedX transformedY transformedZ
        transformedOddPlus < (1 / 250000 : ℝ) := by
  rw [transformed_excess_eq_positive]
  rcases negative_endpoint_center_radii with
    ⟨hRU, hRK, hRW, hRS, hRT⟩
  rcases transformed_coordinate_radii with ⟨hRX, hRR, hRZ⟩
  rcases transformed_slope_bounds with
    ⟨hSX, hSR, hSZ, hSU, hSK, hSW, hSS, hST⟩
  have hDet : 0 < alignedDeterminant strongMinus skewMinus weakMinus
      crossSumMinus crossDifferenceMinus e44m := by
    rw [← evenDetMinus_eq_aligned]
    exact evenDetMinus_pos
  have hQstep :
      transformedPositiveExcess strongMinus skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedX
          (-transformedY) transformedZ transformedOddPlus ≤
        transformedPositiveExcess strongMinus skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedX
          (-transformedY) transformedZ (3 / 250) := by
    rw [← sub_nonpos]
    rw [transformed_q_step]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sub_nonneg.mpr
        transformedOddPlus_gt_three_div_two_fifty.le)) hDet.le
  have hXstep :
      transformedPositiveExcess strongMinus skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedX
          (-transformedY) transformedZ (3 / 250) -
        transformedPositiveExcess strongMinus skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          (-transformedY) transformedZ (3 / 250) ≤
        (19 / 10000 : ℝ) * (24 / 100000) := by
    rw [transformed_x_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRX hSX
  have hRstep :
      transformedPositiveExcess strongMinus skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          (-transformedY) transformedZ (3 / 250) -
        transformedPositiveExcess strongMinus skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZ (3 / 250) ≤
        (15 / 100000 : ℝ) * (12 / 10000) := by
    rw [transformed_r_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRR hSR
  have hZstep :
      transformedPositiveExcess strongMinus skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZ (3 / 250) -
        transformedPositiveExcess strongMinus skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZCenter (3 / 250) ≤
        (1 / 800 : ℝ) * (22 / 100000) := by
    rw [transformed_z_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRZ hSZ
  have hUstep :
      transformedPositiveExcess strongMinus skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZCenter (3 / 250) -
        transformedPositiveExcess uCenter skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZCenter (3 / 250) ≤
        (1088 / 1000000 : ℝ) * (1 / 100000) := by
    rw [transformed_u_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRU hSU
  have hKstep :
      transformedPositiveExcess uCenter skewMinus weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZCenter (3 / 250) -
        transformedPositiveExcess uCenter kCenter weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZCenter (3 / 250) ≤
        (1030 / 1000000 : ℝ) * (4 / 100000) := by
    rw [transformed_k_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRK hSK
  have hWstep :
      transformedPositiveExcess uCenter kCenter weakMinus
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZCenter (3 / 250) -
        transformedPositiveExcess uCenter kCenter wCenter
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZCenter (3 / 250) ≤
        (1088 / 1000000 : ℝ) * (43 / 100000) := by
    rw [transformed_w_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRW hSW
  have hSstep :
      transformedPositiveExcess uCenter kCenter wCenter
          crossSumMinus crossDifferenceMinus e44m transformedXCenter
          transformedRCenter transformedZCenter (3 / 250) -
        transformedPositiveExcess uCenter kCenter wCenter sCenter
          crossDifferenceMinus e44m transformedXCenter transformedRCenter
          transformedZCenter (3 / 250) ≤
        (7447 / 2000000 : ℝ) * (1 / 50000) := by
    rw [transformed_s_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRS hSS
  have hTstep :
      transformedPositiveExcess uCenter kCenter wCenter sCenter
          crossDifferenceMinus e44m transformedXCenter transformedRCenter
          transformedZCenter (3 / 250) -
        transformedPositiveExcess uCenter kCenter wCenter sCenter tCenter
          e44m transformedXCenter transformedRCenter transformedZCenter
          (3 / 250) ≤
        (3947 / 2000000 : ℝ) * (22 / 100000) := by
    rw [transformed_t_step]
    exact mul_le_budget_of_abs_le (by norm_num) hRT hST
  have hFslope : 0 < transformedFSlope := by
    norm_num [transformedFSlope, uCenter, kCenter, wCenter,
      transformedXCenter, transformedRCenter]
  have hFstep :
      transformedPositiveExcess uCenter kCenter wCenter sCenter tCenter
          e44m transformedXCenter transformedRCenter transformedZCenter
          (3 / 250) ≤
        transformedPositiveExcess uCenter kCenter wCenter sCenter tCenter
          (64 / 125) transformedXCenter transformedRCenter
          transformedZCenter (3 / 250) := by
    rw [← sub_nonpos]
    rw [transformed_f_step]
    exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr e44m_upper.le) hFslope.le
  have hCenter :
      transformedPositiveExcess uCenter kCenter wCenter sCenter tCenter
          (64 / 125) transformedXCenter transformedRCenter
          transformedZCenter (3 / 250) < (19 / 10000000 : ℝ) := by
    norm_num [transformedPositiveExcess, transformedExcess,
      alignedAdjugateQuadratic, alignedDeterminant, uCenter, kCenter,
      wCenter, sCenter, tCenter, transformedXCenter, transformedRCenter,
      transformedZCenter]
  have hBudget :
      (19 / 10000 : ℝ) * (24 / 100000) +
        (15 / 100000 : ℝ) * (12 / 10000) +
        (1 / 800 : ℝ) * (22 / 100000) +
        (1088 / 1000000 : ℝ) * (1 / 100000) +
        (1030 / 1000000 : ℝ) * (4 / 100000) +
        (1088 / 1000000 : ℝ) * (43 / 100000) +
        (7447 / 2000000 : ℝ) * (1 / 50000) +
        (3947 / 2000000 : ℝ) * (22 / 100000) +
        (19 / 10000000 : ℝ) < 1 / 250000 := by
    norm_num
  linarith only [hQstep, hXstep, hRstep, hZstep, hUstep, hKstep,
    hWstep, hSstep, hTstep, hFstep, hCenter, hBudget]

private theorem p3EndpointGate_gt_one_div_five_thousand :
    (1 / 5000 : ℝ) < p3EndpointGate := by
  have hp := pivotCoeff_two_gt_four_div_five_thousand
  rcases factorTwoIntrinsicOddPhaseLow_minus_entry_bounds with
    ⟨_ho11L, _ho11U, _ho13L, _ho13U, ho33mL, _ho33mU⟩
  rcases factorTwoIntrinsicOddPhaseLow_plus_entry_bounds with
    ⟨_ho11pL, _ho11pU, _ho13pL, _ho13pU, ho33pL, _ho33pU⟩
  have hp0 : 0 < pivotCoeff 2 := lt_trans (by norm_num) hp
  have hpProduct :
      (4 / 5000 : ℝ) * (4485 / 10000) < pivotCoeff 2 * o33m := by
    calc
      (4 / 5000 : ℝ) * (4485 / 10000) <
          pivotCoeff 2 * (4485 / 10000) :=
        mul_lt_mul_of_pos_right hp (by norm_num)
      _ < pivotCoeff 2 * o33m := by
        apply mul_lt_mul_of_pos_left _ hp0
        simpa only [o33m] using ho33mL
  have hOddExtra :
      0 < evenDetMinus * (o33p - 2115 / 10000) := by
    apply mul_pos evenDetMinus_pos
    simpa only [o33p] using sub_pos.mpr ho33pL
  have hTail :
      (-3 / 20000 : ℝ) < evenDetMinus * o33p - j33 := by
    nlinarith only [hOddExtra, p3_endpoint_excess_lt]
  unfold p3EndpointGate
  nlinarith only [hpProduct, hTail]

private theorem oddDetMinus_gt_one_div_forty :
    (1 / 40 : ℝ) < oddDetMinus := by
  simpa only [oddDetMinus, o11m, o13m, o33m] using
    factorTwoIntrinsicOddPhaseLow_minus_minor_gt_one_div_forty

private theorem transformedReserve_gt_neg_one_div_two_fifty_thousand :
    (-1 / 250000 : ℝ) < transformedReserve := by
  rw [transformedReserve_eq_neg_excess]
  linarith only [transformed_excess_lt_one_div_two_fifty_thousand]

/-- The fourth mixed coefficient of the raw five-mode determinant is
nonnegative. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_four_nonneg :
    0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4 := by
  have hOdd0 : 0 < oddDetMinus :=
    lt_trans (by norm_num) oddDetMinus_gt_one_div_forty
  have hProduct :
      (1 / 200000 : ℝ) < oddDetMinus * p3EndpointGate := by
    calc
      (1 / 200000 : ℝ) = (1 / 40 : ℝ) * (1 / 5000) := by
        norm_num
      _ < oddDetMinus * (1 / 5000) :=
        mul_lt_mul_of_pos_right oddDetMinus_gt_one_div_forty (by norm_num)
      _ < oddDetMinus * p3EndpointGate :=
        mul_lt_mul_of_pos_left p3EndpointGate_gt_one_div_five_thousand hOdd0
  have hScaled :
      0 < o33m * factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4 := by
    rw [scaled_coefficient_four_decomposition]
    nlinarith only [hProduct,
      transformedReserve_gt_neg_one_div_two_fifty_thousand]
  have ho33m : 0 < o33m := by
    have h := factorTwoIntrinsicOddPhaseLow_minus_entry_bounds
    simpa only [o33m] using lt_trans (by norm_num) h.2.2.2.2.1
  by_contra hCoefficient
  have hneg : factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 4 < 0 :=
    lt_of_not_ge hCoefficient
  have := mul_neg_of_pos_of_neg ho33m hneg
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC4Structural
