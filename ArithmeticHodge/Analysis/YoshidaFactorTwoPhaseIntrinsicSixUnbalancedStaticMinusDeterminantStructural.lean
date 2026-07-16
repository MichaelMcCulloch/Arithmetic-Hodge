import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedPositiveProfileStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5CombinedPositiveProfileStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# The final negative static Schur gate

The first five coordinates retain the congruence used for the negative
minor.  The `P₅` column is completed only after its correlations have been
formed.  Thus the final comparison is a six-dimensional weighted SOS, not
an independent-entry or corner certificate.
-/

def factorTwoIntrinsicSixUnbalancedMinorMinusLowerSixQuadratic
    (s d p u v w : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic s d p u v +
    2 * ((factorTwoIntrinsicSixUnbalancedKMinus05 +
        factorTwoIntrinsicSixUnbalancedKMinus25) * s +
      (factorTwoIntrinsicSixUnbalancedKMinus05 -
        factorTwoIntrinsicSixUnbalancedKMinus25) * d +
      factorTwoIntrinsicSixUnbalancedKMinus45 * p) * w +
    2 * factorTwoIntrinsicSixUnbalancedOPlus15 * (u - v) * w +
    2 * factorTwoIntrinsicSixUnbalancedOPlus35 * v * w +
    factorTwoIntrinsicSixUnbalancedOPlus55 * w ^ 2

def factorTwoIntrinsicSixUnbalancedMinorMinusExactSixQuadratic
    (c0 c2 c4 c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedMinorMinusExactFiveQuadratic
      c0 c2 c4 c1 c3 +
    2 * (c0 * factorTwoIntrinsicSixUnbalancedKMinus05 +
      c2 * factorTwoIntrinsicSixUnbalancedKMinus25 +
      c4 * factorTwoIntrinsicSixUnbalancedKMinus45) * c5 +
    2 * factorTwoIntrinsicSixUnbalancedOPlus15 * c1 * c5 +
    2 * factorTwoIntrinsicSixUnbalancedOPlus35 * c3 * c5 +
    factorTwoIntrinsicSixUnbalancedOPlus55 * c5 ^ 2

theorem factorTwoIntrinsicSixUnbalancedMinorMinusLowerSix_le_exact
    (s d p u v w : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerSixQuadratic
        s d p u v w ≤
      factorTwoIntrinsicSixUnbalancedMinorMinusExactSixQuadratic
        (s + d) (s - d) p (u - v) v w := by
  have h := factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_le_exact
    s d p u v
  unfold factorTwoIntrinsicSixUnbalancedMinorMinusLowerSixQuadratic
    factorTwoIntrinsicSixUnbalancedMinorMinusExactSixQuadratic
  nlinarith

private def minusDetMapS (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  x0 - (2 / 15 : ℝ) * x1 - (1 / 6 : ℝ) * x2 -
    (1 / 20 : ℝ) * x3 + (4 / 25 : ℝ) * x4

private def minusDetMapD (x3 x4 : ℝ) : ℝ :=
  x3 - (11 / 4 : ℝ) * x4

private def minusDetMapP (x1 x2 x3 x4 : ℝ) : ℝ :=
  x1 - (4 / 35 : ℝ) * x2 + (9 / 50 : ℝ) * x3 -
    (3 / 8 : ℝ) * x4

private def minusDetMapU (x2 x3 x4 : ℝ) : ℝ :=
  x2 - (1 / 14 : ℝ) * x3 + (7 / 80 : ℝ) * x4

private def minusDetTransformedFiveQuadratic
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
    (minusDetMapS x0 x1 x2 x3 x4) (minusDetMapD x3 x4)
    (minusDetMapP x1 x2 x3 x4) (minusDetMapU x2 x3 x4) x4

private theorem minusDetTransformedFive_reserve
    (x0 x1 x2 x3 x4 : ℝ) :
    (8653 / 6250 : ℝ) * x0 ^ 2 +
        (24687 / 80000 : ℝ) * x1 ^ 2 +
        (6447 / 80000 : ℝ) * x2 ^ 2 +
        (2153 / 1500000 : ℝ) * x3 ^ 2 +
        (517 / 800000 : ℝ) * x4 ^ 2 ≤
      minusDetTransformedFiveQuadratic x0 x1 x2 x3 x4 := by
  simpa only [minusDetTransformedFiveQuadratic, minusDetMapS, minusDetMapD,
    minusDetMapP, minusDetMapU] using
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerFive_transformed_reserve
      x0 x1 x2 x3 x4

private theorem minusDetTransformedFive_eq_matrix
    (x0 x1 x2 x3 x4 : ℝ) :
    minusDetTransformedFiveQuadratic x0 x1 x2 x3 x4 =
      minusMinorFiveQuadratic
        minorMinusT00 minorMinusT01 minorMinusT02 minorMinusT03 minorMinusT04
        minorMinusT11 minorMinusT12 minorMinusT13 minorMinusT14
        minorMinusT22 minorMinusT23 minorMinusT24 minorMinusT33 minorMinusT34
        minorMinusT44 x0 x1 x2 x3 x4 := by
  simpa only [minusDetTransformedFiveQuadratic, minusDetMapS, minusDetMapD,
    minusDetMapP, minusDetMapU] using
      minorMinusLowerFive_congruence x0 x1 x2 x3 x4

private def minusDetG0 : ℝ :=
  factorTwoIntrinsicSixUnbalancedKMinus05 +
    factorTwoIntrinsicSixUnbalancedKMinus25

private def minusDetG1 : ℝ :=
  -(2 / 15 : ℝ) * minusDetG0 +
    factorTwoIntrinsicSixUnbalancedKMinus45

private def minusDetG2 : ℝ :=
  -(1 / 6 : ℝ) * minusDetG0 -
    (4 / 35 : ℝ) * factorTwoIntrinsicSixUnbalancedKMinus45 +
    factorTwoIntrinsicSixUnbalancedOPlus15

private def minusDetG3 : ℝ :=
  -(1 / 20 : ℝ) * minusDetG0 +
    (factorTwoIntrinsicSixUnbalancedKMinus05 -
      factorTwoIntrinsicSixUnbalancedKMinus25) +
    (9 / 50 : ℝ) * factorTwoIntrinsicSixUnbalancedKMinus45 -
    (1 / 14 : ℝ) * factorTwoIntrinsicSixUnbalancedOPlus15

private def minusDetG4 : ℝ :=
  (4 / 25 : ℝ) * minusDetG0 -
    (11 / 4 : ℝ) * (factorTwoIntrinsicSixUnbalancedKMinus05 -
      factorTwoIntrinsicSixUnbalancedKMinus25) -
    (3 / 8 : ℝ) * factorTwoIntrinsicSixUnbalancedKMinus45 -
    (73 / 80 : ℝ) * factorTwoIntrinsicSixUnbalancedOPlus15 +
    factorTwoIntrinsicSixUnbalancedOPlus35

private def minusDetTransformedSixQuadratic
    (x0 x1 x2 x3 x4 z : ℝ) : ℝ :=
  minusDetTransformedFiveQuadratic x0 x1 x2 x3 x4 +
    2 * minusDetG0 * x0 * z + 2 * minusDetG1 * x1 * z +
    2 * minusDetG2 * x2 * z + 2 * minusDetG3 * x3 * z +
    2 * minusDetG4 * x4 * z +
    factorTwoIntrinsicSixUnbalancedOPlus55 * z ^ 2

private theorem minusDetLowerSix_congruence
    (x0 x1 x2 x3 x4 z : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerSixQuadratic
        (minusDetMapS x0 x1 x2 x3 x4) (minusDetMapD x3 x4)
        (minusDetMapP x1 x2 x3 x4) (minusDetMapU x2 x3 x4) x4 z =
      minusDetTransformedSixQuadratic x0 x1 x2 x3 x4 z := by
  unfold factorTwoIntrinsicSixUnbalancedMinorMinusLowerSixQuadratic
    minusDetTransformedSixQuadratic minusDetTransformedFiveQuadratic
    minusDetG1 minusDetG2 minusDetG3 minusDetG4 minusDetG0
    minusDetMapS minusDetMapD minusDetMapP minusDetMapU
  ring_nf

private def minusDetShift0 : ℝ := -1 / 30
private def minusDetShift1 : ℝ := -3 / 16
private def minusDetShift2 : ℝ := -81 / 80
private def minusDetShift3 : ℝ := -50 / 9
private def minusDetShift4 : ℝ := -15 / 8

/-! ## Cancellation-aware completed border -/

private def minusDetH0 : ℝ :=
  7222927 / 24000000 -
    (4129 / 11200) * factorTwoIntrinsicSixUnbalancedEMinusP4Sum -
    (31439 / 40320) * factorTwoIntrinsicSixUnbalancedKMinusOneSum -
    (15 / 8) * factorTwoIntrinsicSixUnbalancedKMinusShearSum +
    (factorTwoIntrinsicFourP45Cross05 +
      factorTwoIntrinsicFourP45Cross25) / 2

private def minusDetH1 : ℝ :=
  -1306476377 / 10080000000 +
    (11803 / 63000) * factorTwoIntrinsicSixUnbalancedEMinusP4Sum +
    (31439 / 302400) * factorTwoIntrinsicSixUnbalancedKMinusOneSum +
    factorTwoIntrinsicSixUnbalancedKMinusShearSum / 4 +
    (115 / 288) * factorTwoIntrinsicSixUnbalancedEMinusP4Difference -
    (31439 / 40320) * factorTwoIntrinsicSixUnbalancedKMinus41 -
    (15 / 8) * factorTwoIntrinsicSixUnbalancedKMinusShearTail -
    (factorTwoIntrinsicFourP45Cross05 +
      factorTwoIntrinsicFourP45Cross25) / 15 +
    factorTwoIntrinsicP45Alternating / 2

private def minusDetH2 : ℝ :=
  -4307779961 / 23520000000 +
    (9203 / 201600) * factorTwoIntrinsicSixUnbalancedEMinusP4Sum +
    (64871 / 241920) * factorTwoIntrinsicSixUnbalancedKMinusOneSum +
    (5 / 16) * factorTwoIntrinsicSixUnbalancedKMinusShearSum -
    (23 / 504) * factorTwoIntrinsicSixUnbalancedEMinusP4Difference -
    (115 / 288) * factorTwoIntrinsicSixUnbalancedKMinusOneDifference -
    (197249 / 705600) * factorTwoIntrinsicSixUnbalancedKMinus41 +
    (3 / 14) * factorTwoIntrinsicSixUnbalancedKMinusShearTail -
    (factorTwoIntrinsicFourP45Cross05 +
      factorTwoIntrinsicFourP45Cross25) / 12 -
    (2 / 35) * factorTwoIntrinsicP45Alternating +
    factorTwoIntrinsicSixUnbalancedOPlus15

private def minusDetH3 : ℝ :=
  -10888709537 / 352800000000 +
    (9701 / 224000) * factorTwoIntrinsicSixUnbalancedEMinusP4Sum +
    (23479 / 806400) * factorTwoIntrinsicSixUnbalancedKMinusOneSum +
    (3 / 32) * factorTwoIntrinsicSixUnbalancedKMinusShearSum +
    (2467 / 5600) * factorTwoIntrinsicSixUnbalancedEMinusP4Difference -
    (4327 / 5760) * factorTwoIntrinsicSixUnbalancedKMinusOneDifference -
    (15 / 8) * factorTwoIntrinsicSixUnbalancedKMinusShearDifference -
    (178783 / 1568000) * factorTwoIntrinsicSixUnbalancedKMinus41 -
    (27 / 80) * factorTwoIntrinsicSixUnbalancedKMinusShearTail +
    (19 / 40) * factorTwoIntrinsicFourP45Cross05 -
    (21 / 40) * factorTwoIntrinsicFourP45Cross25 +
    (9 / 100) * factorTwoIntrinsicP45Alternating -
    (1 / 14) * factorTwoIntrinsicSixUnbalancedOPlus15

private def minusDetH4 : ℝ :=
  13226532359 / 268800000000 -
    (372317 / 3360000) * factorTwoIntrinsicSixUnbalancedEMinusP4Sum -
    (151423 / 1344000) * factorTwoIntrinsicSixUnbalancedKMinusOneSum -
    (233 / 1440) * factorTwoIntrinsicSixUnbalancedKMinusShearSum -
    (78191 / 67200) * factorTwoIntrinsicSixUnbalancedEMinusP4Difference +
    (56699 / 26880) * factorTwoIntrinsicSixUnbalancedKMinusOneDifference +
    (685 / 144) * factorTwoIntrinsicSixUnbalancedKMinusShearDifference +
    (349633 / 1344000) * factorTwoIntrinsicSixUnbalancedKMinus41 +
    (1873 / 5600) * factorTwoIntrinsicSixUnbalancedKMinusShearTail -
    (259 / 200) * factorTwoIntrinsicFourP45Cross05 +
    (291 / 200) * factorTwoIntrinsicFourP45Cross25 -
    (3 / 16) * factorTwoIntrinsicP45Alternating -
    (73 / 80) * factorTwoIntrinsicSixUnbalancedOPlus15 +
    factorTwoIntrinsicSixUnbalancedOPlus35

private def minusDetW : ℝ :=
  103412374889051 / 406425600000000 -
    (821671 / 8064000) * factorTwoIntrinsicSixUnbalancedEMinusP4Sum -
    (6256361 / 29030400) * factorTwoIntrinsicSixUnbalancedKMinusOneSum -
    (199 / 384) * factorTwoIntrinsicSixUnbalancedKMinusShearSum -
    (94967 / 322560) * factorTwoIntrinsicSixUnbalancedEMinusP4Difference +
    (723097 / 1161216) * factorTwoIntrinsicSixUnbalancedKMinusOneDifference +
    (575 / 384) * factorTwoIntrinsicSixUnbalancedKMinusShearDifference +
    (129811631 / 225792000) * factorTwoIntrinsicSixUnbalancedKMinus41 +
    (12387 / 8960) * factorTwoIntrinsicSixUnbalancedKMinusShearTail -
    (47 / 180) * factorTwoIntrinsicFourP45Cross05 +
    (43 / 80) * factorTwoIntrinsicFourP45Cross25 -
    (4129 / 11200) * factorTwoIntrinsicP45Alternating +
    (44161 / 20160) * factorTwoIntrinsicSixUnbalancedOPlus15 -
    (15 / 4) * factorTwoIntrinsicSixUnbalancedOPlus35 +
    factorTwoIntrinsicSixUnbalancedOPlus55

/-! The border translation is carried out through the already-certified
explicit matrix of the five-mode form.  This avoids expanding the full
quadratic twice. -/

private def minusDetMatrixH0 : ℝ :=
  minorMinusT00 * minusDetShift0 + minorMinusT01 * minusDetShift1 +
    minorMinusT02 * minusDetShift2 + minorMinusT03 * minusDetShift3 +
    minorMinusT04 * minusDetShift4 + minusDetG0

private def minusDetMatrixH1 : ℝ :=
  minorMinusT01 * minusDetShift0 + minorMinusT11 * minusDetShift1 +
    minorMinusT12 * minusDetShift2 + minorMinusT13 * minusDetShift3 +
    minorMinusT14 * minusDetShift4 + minusDetG1

private def minusDetMatrixH2 : ℝ :=
  minorMinusT02 * minusDetShift0 + minorMinusT12 * minusDetShift1 +
    minorMinusT22 * minusDetShift2 + minorMinusT23 * minusDetShift3 +
    minorMinusT24 * minusDetShift4 + minusDetG2

private def minusDetMatrixH3 : ℝ :=
  minorMinusT03 * minusDetShift0 + minorMinusT13 * minusDetShift1 +
    minorMinusT23 * minusDetShift2 + minorMinusT33 * minusDetShift3 +
    minorMinusT34 * minusDetShift4 + minusDetG3

private def minusDetMatrixH4 : ℝ :=
  minorMinusT04 * minusDetShift0 + minorMinusT14 * minusDetShift1 +
    minorMinusT24 * minusDetShift2 + minorMinusT34 * minusDetShift3 +
    minorMinusT44 * minusDetShift4 + minusDetG4

private def minusDetMatrixW : ℝ :=
  minusMinorFiveQuadratic
      minorMinusT00 minorMinusT01 minorMinusT02 minorMinusT03 minorMinusT04
      minorMinusT11 minorMinusT12 minorMinusT13 minorMinusT14
      minorMinusT22 minorMinusT23 minorMinusT24 minorMinusT33 minorMinusT34
      minorMinusT44 minusDetShift0 minusDetShift1 minusDetShift2
      minusDetShift3 minusDetShift4 +
    2 * minusDetG0 * minusDetShift0 +
    2 * minusDetG1 * minusDetShift1 +
    2 * minusDetG2 * minusDetShift2 +
    2 * minusDetG3 * minusDetShift3 +
    2 * minusDetG4 * minusDetShift4 +
    factorTwoIntrinsicSixUnbalancedOPlus55

set_option maxHeartbeats 800000 in
private theorem minusDetH0_eq_matrix : minusDetH0 = minusDetMatrixH0 := by
  unfold minusDetH0 minusDetMatrixH0 minorMinusT00 minorMinusT01
    minorMinusT02 minorMinusT03 minorMinusT04 minusMinorFiveBilinear
    minusDetShift0 minusDetShift1 minusDetShift2 minusDetShift3
    minusDetShift4 minusDetG0 factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22 minusP4Lower
    intrinsicStaticMinusOddLower11 intrinsicStaticMinusOddLower13
    intrinsicStaticMinusOddLower33
  ring

set_option maxHeartbeats 800000 in
private theorem minusDetH1_eq_matrix : minusDetH1 = minusDetMatrixH1 := by
  unfold minusDetH1 minusDetMatrixH1 minorMinusT01 minorMinusT11
    minorMinusT12 minorMinusT13 minorMinusT14 minusMinorFiveBilinear
    minusDetShift0 minusDetShift1 minusDetShift2 minusDetShift3
    minusDetShift4 minusDetG1 minusDetG0
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22 minusP4Lower
    intrinsicStaticMinusOddLower11 intrinsicStaticMinusOddLower13
    intrinsicStaticMinusOddLower33
  ring

set_option maxHeartbeats 800000 in
private theorem minusDetH2_eq_matrix : minusDetH2 = minusDetMatrixH2 := by
  unfold minusDetH2 minusDetMatrixH2 minorMinusT02 minorMinusT12
    minorMinusT22 minorMinusT23 minorMinusT24 minusMinorFiveBilinear
    minusDetShift0 minusDetShift1 minusDetShift2 minusDetShift3
    minusDetShift4 minusDetG2 minusDetG0
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22 minusP4Lower
    intrinsicStaticMinusOddLower11 intrinsicStaticMinusOddLower13
    intrinsicStaticMinusOddLower33
  ring

set_option maxHeartbeats 800000 in
private theorem minusDetH3_eq_matrix : minusDetH3 = minusDetMatrixH3 := by
  unfold minusDetH3 minusDetMatrixH3 minorMinusT03 minorMinusT13
    minorMinusT23 minorMinusT33 minorMinusT34 minusMinorFiveBilinear
    minusDetShift0 minusDetShift1 minusDetShift2 minusDetShift3
    minusDetShift4 minusDetG3 minusDetG0
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22 minusP4Lower
    intrinsicStaticMinusOddLower11 intrinsicStaticMinusOddLower13
    intrinsicStaticMinusOddLower33
  ring

set_option maxHeartbeats 800000 in
private theorem minusDetH4_eq_matrix : minusDetH4 = minusDetMatrixH4 := by
  unfold minusDetH4 minusDetMatrixH4 minorMinusT04 minorMinusT14
    minorMinusT24 minorMinusT34 minorMinusT44 minusMinorFiveBilinear
    minusDetShift0 minusDetShift1 minusDetShift2 minusDetShift3
    minusDetShift4 minusDetG4 minusDetG0
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22 minusP4Lower
    intrinsicStaticMinusOddLower11 intrinsicStaticMinusOddLower13
    intrinsicStaticMinusOddLower33
  ring

set_option maxHeartbeats 800000 in
private theorem minusDetW_eq_matrix : minusDetW = minusDetMatrixW := by
  unfold minusDetW minusDetMatrixW minusMinorFiveQuadratic
    minorMinusT00 minorMinusT01 minorMinusT02 minorMinusT03 minorMinusT04
    minorMinusT11 minorMinusT12 minorMinusT13 minorMinusT14
    minorMinusT22 minorMinusT23 minorMinusT24 minorMinusT33 minorMinusT34
    minorMinusT44 minusMinorFiveBilinear minusDetShift0 minusDetShift1
    minusDetShift2 minusDetShift3 minusDetShift4 minusDetG1 minusDetG2
    minusDetG3 minusDetG4 minusDetG0
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22 minusP4Lower
    intrinsicStaticMinusOddLower11 intrinsicStaticMinusOddLower13
    intrinsicStaticMinusOddLower33
  ring

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
private theorem minusDetTransformedSix_border_congruence
    (x0 x1 x2 x3 x4 z : ℝ) :
    minusDetTransformedSixQuadratic
        (x0 + minusDetShift0 * z) (x1 + minusDetShift1 * z)
        (x2 + minusDetShift2 * z) (x3 + minusDetShift3 * z)
        (x4 + minusDetShift4 * z) z =
      minusDetTransformedFiveQuadratic x0 x1 x2 x3 x4 +
        2 * minusDetH0 * x0 * z + 2 * minusDetH1 * x1 * z +
        2 * minusDetH2 * x2 * z + 2 * minusDetH3 * x3 * z +
        2 * minusDetH4 * x4 * z + minusDetW * z ^ 2 := by
  unfold minusDetTransformedSixQuadratic
  simp only [minusDetTransformedFive_eq_matrix, minusDetH0_eq_matrix,
    minusDetH1_eq_matrix, minusDetH2_eq_matrix, minusDetH3_eq_matrix,
    minusDetH4_eq_matrix, minusDetW_eq_matrix]
  unfold minusDetMatrixH0 minusDetMatrixH1 minusDetMatrixH2
    minusDetMatrixH3 minusDetMatrixH4 minusDetMatrixW
    minusMinorFiveQuadratic
  ring

/-! ## Entrywise-safe part of the completed border -/

/-- The first three completed-border coordinates are small already from the
public structural boxes.  The final two coordinates are deliberately not
split this way; their proof retains the complete correlated profile. -/
private theorem minusDetH012_bounds :
    |minusDetH0| < (3 / 1000 : ℝ) ∧
      |minusDetH1| < (21 / 10000 : ℝ) ∧
      |minusDetH2| < (1 / 1000 : ℝ) := by
  have hP4 := factorTwoIntrinsicP4MinusCross_refined_bounds
  change
    (2927 / 10000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedEMinusP4Sum ∧
      factorTwoIntrinsicSixUnbalancedEMinusP4Sum < 2931 / 10000 ∧
      (662 / 10000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedEMinusP4Difference ∧
      factorTwoIntrinsicSixUnbalancedEMinusP4Difference < 666 / 10000
    at hP4
  have hOne := factorTwoIntrinsicSixUnbalancedKMinus_firstColumn_bounds
  change
    (20077 / 50000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedKMinusOneSum ∧
      factorTwoIntrinsicSixUnbalancedKMinusOneSum < 80313 / 200000 ∧
      (2747 / 200000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedKMinusOneDifference ∧
      factorTwoIntrinsicSixUnbalancedKMinusOneDifference < 43 / 3125 ∧
      (1043 / 10000 : ℝ) < factorTwoIntrinsicSixUnbalancedKMinus41 ∧
      factorTwoIntrinsicSixUnbalancedKMinus41 < 529 / 5000
    at hOne
  rcases hP4 with ⟨hP4sL, hP4sU, hP4dL, hP4dU⟩
  rcases hOne with ⟨hOneSumL, hOneSumU, hOneDiffL, hOneDiffU,
    hOneTailL, hOneTailU⟩
  rcases factorTwoIntrinsicSixUnbalancedKMinusShearLow_bounds with
    ⟨hShearSumL, hShearSumU, hShearDiffL, hShearDiffU⟩
  rcases factorTwoIntrinsicSixUnbalancedKMinusShearTail_bounds with
    ⟨hShearTailL, hShearTailU⟩
  rcases factorTwoIntrinsicFourP45Cross05_bounds with ⟨h05L, h05U⟩
  rcases factorTwoIntrinsicFourP45Cross25_bounds with ⟨h25L, h25U⟩
  have h45 := factorTwoIntrinsicSixAlternating45_bounds
  change
    (-2 / 1000 : ℝ) < factorTwoIntrinsicP45Alternating ∧
      factorTwoIntrinsicP45Alternating < 0
    at h45
  rcases h45 with ⟨h45L, h45U⟩
  have h15 := factorTwoIntrinsicFourP45Cross15_one_bounds
  change
    (131727 / 1000000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedOPlus15 ∧
      factorTwoIntrinsicSixUnbalancedOPlus15 < 131929 / 1000000
    at h15
  rcases h15 with ⟨h15L, h15U⟩
  unfold minusDetH0 minusDetH1 minusDetH2
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    constructor <;> linarith
  · rw [abs_lt]
    constructor <;> linarith

/-! ## The three cancellation-preserving border cores -/

/-- The `H3` border coordinate with its positive-endpoint `P1-P5` tail
removed.  This is the quantity whose symmetric and alternating profiles must
be estimated jointly. -/
private def minusDetH3Core : ℝ :=
  minusDetH3 + (1 / 14 : ℝ) *
    factorTwoIntrinsicSixUnbalancedOPlus15

/-- The `H4` border coordinate with its complete positive-endpoint `P5`
cross tail removed. -/
private def minusDetH4Core : ℝ :=
  minusDetH4 + (73 / 80 : ℝ) *
      factorTwoIntrinsicSixUnbalancedOPlus15 -
    factorTwoIntrinsicSixUnbalancedOPlus35

/-- The completed diagonal with its whole correlated positive-endpoint odd
`P5` tail removed. -/
private def minusDetWCore : ℝ :=
  minusDetW - minusP5OddPositiveTail

private theorem minusDetH3_eq_core_add_tail :
    minusDetH3 = minusDetH3Core -
      (1 / 14 : ℝ) * factorTwoIntrinsicSixUnbalancedOPlus15 := by
  unfold minusDetH3Core
  ring

private theorem minusDetH4_eq_core_add_tail :
    minusDetH4 = minusDetH4Core -
        (73 / 80 : ℝ) * factorTwoIntrinsicSixUnbalancedOPlus15 +
      factorTwoIntrinsicSixUnbalancedOPlus35 := by
  unfold minusDetH4Core
  ring

private theorem minusDetW_eq_core_add_tail :
    minusDetW = minusDetWCore + minusP5OddPositiveTail := by
  unfold minusDetWCore
  ring

/-- Rational boxes needed only for the three full non-`P5` profiles.  They
are kept separate from the endpoint tails so that neither source is split
entrywise. -/
private def MinusP5BorderCoreBounds : Prop :=
  (47 / 5000 : ℝ) < minusDetH3Core ∧
    minusDetH3Core < (189 / 20000 : ℝ) ∧
    (-6521 / 125000 : ℝ) < minusDetH4Core ∧
    minusDetH4Core < (-26043 / 500000 : ℝ) ∧
    (146357 / 1000000 : ℝ) < minusDetWCore

/-! ## Six-dimensional weighted SOS -/

/-- The only analytic frontier left after the safe border boxes have been
discharged.  These bounds are intentionally formed on the two complete
correlated profiles and on the completed diagonal. -/
private def MinusP5BorderCombinedBounds : Prop :=
  |minusDetH3| < (1 / 2000 : ℝ) ∧
    |minusDetH4| < (1 / 4000 : ℝ) ∧
    (1 / 2000 : ℝ) < minusDetW

/-- Once the three non-tail profiles have been bounded jointly, the public
endpoint-cross boxes and the one whole-profile `P5` tail bound close the
completed border. -/
private theorem minusP5BorderCombinedBounds_of_coreBounds
    (hcore : MinusP5BorderCoreBounds)
    (htail : (-729 / 5000 : ℝ) < minusP5OddPositiveTail) :
    MinusP5BorderCombinedBounds := by
  rcases hcore with ⟨h3L, h3U, h4L, h4U, hWL⟩
  have h15 := factorTwoIntrinsicFourP45Cross15_one_bounds
  have h35 := factorTwoIntrinsicFourP45Cross35_one_bounds
  change
    (131727 / 1000000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedOPlus15 ∧
      factorTwoIntrinsicSixUnbalancedOPlus15 < 131929 / 1000000
    at h15
  change
    (172324 / 1000000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedOPlus35 ∧
      factorTwoIntrinsicSixUnbalancedOPlus35 < 172427 / 1000000
    at h35
  constructor
  · rw [minusDetH3_eq_core_add_tail, abs_lt]
    constructor <;> linarith [h15.1, h15.2]
  constructor
  · rw [minusDetH4_eq_core_add_tail, abs_lt]
    constructor <;> linarith [h15.1, h15.2, h35.1, h35.2]
  · rw [minusDetW_eq_core_add_tail]
    linarith

private theorem two_mul_mul_ge_neg_weighted_square
    {a e r x z : ℝ} (he : 0 < e) (_hr : 0 < r)
    (ha : |a| < e * r) :
    -e * x ^ 2 - e * r ^ 2 * z ^ 2 ≤ 2 * a * x * z := by
  rcases abs_lt.mp ha with ⟨haL, haU⟩
  by_cases hxz : 0 ≤ x * z
  · have hmul := mul_le_mul_of_nonneg_right haL.le hxz
    nlinarith [mul_nonneg he.le (sq_nonneg (x - r * z))]
  · have hxz' : x * z ≤ 0 := le_of_not_ge hxz
    have hmul := mul_le_mul_of_nonpos_right haU.le hxz'
    nlinarith [mul_nonneg he.le (sq_nonneg (x + r * z))]

private theorem minusDetCompletedBorder_pos_of_combinedBounds
    (hfrontier : MinusP5BorderCombinedBounds)
    (x0 x1 x2 x3 x4 z : ℝ)
    (hne : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨
      x4 ≠ 0 ∨ z ≠ 0) :
    0 < minusDetTransformedFiveQuadratic x0 x1 x2 x3 x4 +
      2 * minusDetH0 * x0 * z + 2 * minusDetH1 * x1 * z +
      2 * minusDetH2 * x2 * z + 2 * minusDetH3 * x3 * z +
      2 * minusDetH4 * x4 * z + minusDetW * z ^ 2 := by
  rcases minusDetH012_bounds with ⟨hH0, hH1, hH2⟩
  rcases hfrontier with ⟨hH3, hH4, hW⟩
  have hH0' :
      |minusDetH0| <
        (8653 / 6250 : ℝ) * (75 / 34612 : ℝ) := by
    convert hH0 using 1
    all_goals norm_num
  have hH1' :
      |minusDetH1| <
        (24687 / 80000 : ℝ) * (56 / 8229 : ℝ) := by
    convert hH1 using 1
    all_goals norm_num
  have hH2' :
      |minusDetH2| <
        (6447 / 80000 : ℝ) * (80 / 6447 : ℝ) := by
    convert hH2 using 1
    all_goals norm_num
  have hH3' :
      |minusDetH3| <
        (2153 / 1500000 : ℝ) * (750 / 2153 : ℝ) := by
    convert hH3 using 1
    all_goals norm_num
  have hH4' :
      |minusDetH4| <
        (517 / 800000 : ℝ) * (200 / 517 : ℝ) := by
    convert hH4 using 1
    all_goals norm_num
  have hc0 := two_mul_mul_ge_neg_weighted_square
    (a := minusDetH0) (e := (8653 / 6250 : ℝ))
    (r := (75 / 34612 : ℝ)) (x := x0) (z := z)
    (by norm_num) (by norm_num) hH0'
  have hc1 := two_mul_mul_ge_neg_weighted_square
    (a := minusDetH1) (e := (24687 / 80000 : ℝ))
    (r := (56 / 8229 : ℝ)) (x := x1) (z := z)
    (by norm_num) (by norm_num) hH1'
  have hc2 := two_mul_mul_ge_neg_weighted_square
    (a := minusDetH2) (e := (6447 / 80000 : ℝ))
    (r := (80 / 6447 : ℝ)) (x := x2) (z := z)
    (by norm_num) (by norm_num) hH2'
  have hc3 := two_mul_mul_ge_neg_weighted_square
    (a := minusDetH3) (e := (2153 / 1500000 : ℝ))
    (r := (750 / 2153 : ℝ)) (x := x3) (z := z)
    (by norm_num) (by norm_num) hH3'
  have hc4 := two_mul_mul_ge_neg_weighted_square
    (a := minusDetH4) (e := (517 / 800000 : ℝ))
    (r := (200 / 517 : ℝ)) (x := x4) (z := z)
    (by norm_num) (by norm_num) hH4'
  have hreserve := minusDetTransformedFive_reserve x0 x1 x2 x3 x4
  by_cases hz : z = 0
  · have hxne :
        x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0 := by
      rcases hne with h0 | h1 | h2 | h3 | h4 | hz'
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
      · exact (hz' hz).elim
    have hreservePos :
        0 < (8653 / 6250 : ℝ) * x0 ^ 2 +
          (24687 / 80000 : ℝ) * x1 ^ 2 +
          (6447 / 80000 : ℝ) * x2 ^ 2 +
          (2153 / 1500000 : ℝ) * x3 ^ 2 +
          (517 / 800000 : ℝ) * x4 ^ 2 := by
      rcases hxne with h0 | h1 | h2 | h3 | h4
      all_goals positivity
    simp only [hz, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero]
    exact hreservePos.trans_le hreserve
  · have hpenalty :
        (8653 / 6250 : ℝ) * (75 / 34612 : ℝ) ^ 2 +
            (24687 / 80000 : ℝ) * (56 / 8229 : ℝ) ^ 2 +
            (6447 / 80000 : ℝ) * (80 / 6447 : ℝ) ^ 2 +
            (2153 / 1500000 : ℝ) * (750 / 2153 : ℝ) ^ 2 +
            (517 / 800000 : ℝ) * (200 / 517 : ℝ) ^ 2 <
          1 / 2000 := by
      norm_num
    have hleftover :
        0 < minusDetW -
          ((8653 / 6250 : ℝ) * (75 / 34612 : ℝ) ^ 2 +
            (24687 / 80000 : ℝ) * (56 / 8229 : ℝ) ^ 2 +
            (6447 / 80000 : ℝ) * (80 / 6447 : ℝ) ^ 2 +
            (2153 / 1500000 : ℝ) * (750 / 2153 : ℝ) ^ 2 +
            (517 / 800000 : ℝ) * (200 / 517 : ℝ) ^ 2) := by
      linarith
    have hzsq : 0 < z ^ 2 := sq_pos_of_ne_zero hz
    have hstrict := mul_pos hleftover hzsq
    nlinarith only [hreserve, hc0, hc1, hc2, hc3, hc4, hstrict]

/-! ## Inverting the two rational congruences -/

private theorem minusDetTransformedSix_pos_of_combinedBounds
    (hfrontier : MinusP5BorderCombinedBounds)
    (y0 y1 y2 y3 y4 z : ℝ)
    (hne : y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0 ∨ y3 ≠ 0 ∨
      y4 ≠ 0 ∨ z ≠ 0) :
    0 < minusDetTransformedSixQuadratic y0 y1 y2 y3 y4 z := by
  let x0 : ℝ := y0 - minusDetShift0 * z
  let x1 : ℝ := y1 - minusDetShift1 * z
  let x2 : ℝ := y2 - minusDetShift2 * z
  let x3 : ℝ := y3 - minusDetShift3 * z
  let x4 : ℝ := y4 - minusDetShift4 * z
  have hneX :
      x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0 ∨ z ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hx0, hx1, hx2, hx3, hx4, hz⟩
    have hy0 : y0 = 0 := by
      dsimp only [x0] at hx0
      rw [hz] at hx0
      simpa using hx0
    have hy1 : y1 = 0 := by
      dsimp only [x1] at hx1
      rw [hz] at hx1
      simpa using hx1
    have hy2 : y2 = 0 := by
      dsimp only [x2] at hx2
      rw [hz] at hx2
      simpa using hx2
    have hy3 : y3 = 0 := by
      dsimp only [x3] at hx3
      rw [hz] at hx3
      simpa using hx3
    have hy4 : y4 = 0 := by
      dsimp only [x4] at hx4
      rw [hz] at hx4
      simpa using hx4
    rcases hne with hy0' | hy1' | hy2' | hy3' | hy4' | hz'
    · exact hy0' hy0
    · exact hy1' hy1
    · exact hy2' hy2
    · exact hy3' hy3
    · exact hy4' hy4
    · exact hz' hz
  have hpos := minusDetCompletedBorder_pos_of_combinedBounds
    hfrontier x0 x1 x2 x3 x4 z hneX
  have hcong := minusDetTransformedSix_border_congruence
    x0 x1 x2 x3 x4 z
  have hx0 : x0 + minusDetShift0 * z = y0 := by
    dsimp only [x0]
    ring
  have hx1 : x1 + minusDetShift1 * z = y1 := by
    dsimp only [x1]
    ring
  have hx2 : x2 + minusDetShift2 * z = y2 := by
    dsimp only [x2]
    ring
  have hx3 : x3 + minusDetShift3 * z = y3 := by
    dsimp only [x3]
    ring
  have hx4 : x4 + minusDetShift4 * z = y4 := by
    dsimp only [x4]
    ring
  rw [hx0, hx1, hx2, hx3, hx4] at hcong
  rw [hcong]
  exact hpos

private theorem
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerSix_pos_of_combinedBounds
    (hfrontier : MinusP5BorderCombinedBounds)
    (s d p u v w : ℝ)
    (hne : s ≠ 0 ∨ d ≠ 0 ∨ p ≠ 0 ∨ u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedMinorMinusLowerSixQuadratic
      s d p u v w := by
  let x4 : ℝ := v
  let x3 : ℝ := d + (11 / 4 : ℝ) * x4
  let x2 : ℝ := u + (1 / 14 : ℝ) * x3 - (7 / 80 : ℝ) * x4
  let x1 : ℝ := p + (4 / 35 : ℝ) * x2 - (9 / 50 : ℝ) * x3 +
    (3 / 8 : ℝ) * x4
  let x0 : ℝ := s + (2 / 15 : ℝ) * x1 + (1 / 6 : ℝ) * x2 +
    (1 / 20 : ℝ) * x3 - (4 / 25 : ℝ) * x4
  have hneX :
      x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0 ∨ w ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hx0, hx1, hx2, hx3, hx4, hw⟩
    have hv : v = 0 := by simpa only [x4] using hx4
    have hd : d = 0 := by
      dsimp only [x3, x4] at hx3
      nlinarith
    have hu : u = 0 := by
      dsimp only [x2] at hx2
      nlinarith
    have hp : p = 0 := by
      dsimp only [x1] at hx1
      nlinarith
    have hs : s = 0 := by
      dsimp only [x0] at hx0
      nlinarith
    rcases hne with hs' | hd' | hp' | hu' | hv' | hw'
    · exact hs' hs
    · exact hd' hd
    · exact hp' hp
    · exact hu' hu
    · exact hv' hv
    · exact hw' hw
  have htrans := minusDetTransformedSix_pos_of_combinedBounds
    hfrontier x0 x1 x2 x3 x4 w hneX
  have hcong := minusDetLowerSix_congruence x0 x1 x2 x3 x4 w
  have hsMap : minusDetMapS x0 x1 x2 x3 x4 = s := by
    unfold minusDetMapS
    dsimp only [x0]
    ring
  have hdMap : minusDetMapD x3 x4 = d := by
    unfold minusDetMapD
    dsimp only [x3]
    ring
  have hpMap : minusDetMapP x1 x2 x3 x4 = p := by
    unfold minusDetMapP
    dsimp only [x1]
    ring
  have huMap : minusDetMapU x2 x3 x4 = u := by
    unfold minusDetMapU
    dsimp only [x2]
    ring
  rw [hsMap, hdMap, hpMap, huMap] at hcong
  dsimp only [x4] at hcong
  rw [hcong]
  exact htrans

private theorem
    factorTwoIntrinsicSixUnbalancedMinorMinusExactSix_pos_of_combinedBounds
    (hfrontier : MinusP5BorderCombinedBounds)
    (c0 c2 c4 c1 c3 c5 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedMinorMinusExactSixQuadratic
      c0 c2 c4 c1 c3 c5 := by
  let s : ℝ := (c0 + c2) / 2
  let d : ℝ := (c0 - c2) / 2
  let u : ℝ := c1 + c3
  have hneAligned :
      s ≠ 0 ∨ d ≠ 0 ∨ c4 ≠ 0 ∨ u ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    rcases hzero with ⟨hs, hd, hp, hu, hv, hw⟩
    have hc0 : c0 = 0 := by
      dsimp only [s, d] at hs hd
      nlinarith
    have hc2 : c2 = 0 := by
      dsimp only [s, d] at hs hd
      nlinarith
    have hc1 : c1 = 0 := by
      dsimp only [u] at hu
      nlinarith
    rcases hne with h0 | h2 | h4 | h1 | h3 | h5
    · exact h0 hc0
    · exact h2 hc2
    · exact h4 hp
    · exact h1 hc1
    · exact h3 hv
    · exact h5 hw
  have hlow :=
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerSix_pos_of_combinedBounds
      hfrontier s d c4 u c3 c5 hneAligned
  have hle := factorTwoIntrinsicSixUnbalancedMinorMinusLowerSix_le_exact
    s d c4 u c3 c5
  have hsMap : s + d = c0 := by
    dsimp only [s, d]
    ring
  have hdMap : s - d = c2 := by
    dsimp only [s, d]
    ring
  have huMap : u - c3 = c1 := by
    dsimp only [u]
    ring
  rw [hsMap, hdMap, huMap] at hle
  exact hlow.trans_le hle

/-! ## Factored Schur witness for the final odd determinant -/

private theorem minusDet_adjugateVector_linear_identity
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 : ℝ) :
    adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 0 * ell0 +
        adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 1 * ell1 +
        adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 2 * ell2 =
      adjugateQuadratic q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 := by
  simp only [adjugateVector]
  unfold adjugateQuadratic
  ring

private theorem minusDet_adjugateVector_neg_quadratic_identity
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 : ℝ) :
    symmetricQuadratic q00 q01 q02 q11 q12 q22
        (-adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 0)
        (-adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 1)
        (-adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 2) =
      symmetricDeterminant q00 q01 q02 q11 q12 q22 *
        adjugateQuadratic q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 := by
  simp only [adjugateVector]
  unfold symmetricQuadratic symmetricDeterminant adjugateQuadratic
  ring

private def minusDetEll0 (c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedKMinus01 * c1 +
    factorTwoIntrinsicSixUnbalancedKMinus03 * c3 +
    factorTwoIntrinsicSixUnbalancedKMinus05 * c5

private def minusDetEll2 (c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedKMinus21 * c1 +
    factorTwoIntrinsicSixUnbalancedKMinus23 * c3 +
    factorTwoIntrinsicSixUnbalancedKMinus25 * c5

private def minusDetEll4 (c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedKMinus41 * c1 +
    factorTwoIntrinsicSixUnbalancedKMinus43 * c3 +
    factorTwoIntrinsicSixUnbalancedKMinus45 * c5

private def minusDetAdjugateQuadratic (c1 c3 c5 : ℝ) : ℝ :=
  adjugateQuadratic
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (minusDetEll0 c1 c3 c5) (minusDetEll2 c1 c3 c5)
    (minusDetEll4 c1 c3 c5)

private def minusDetAdjugateVector
    (c1 c3 c5 : ℝ) (i : Fin 3) : ℝ :=
  adjugateVector
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (minusDetEll0 c1 c3 c5) (minusDetEll2 c1 c3 c5)
    (minusDetEll4 c1 c3 c5) i

private theorem minusDetAdjugateVector_dot
    (c1 c3 c5 : ℝ) :
    minusDetAdjugateVector c1 c3 c5 0 * minusDetEll0 c1 c3 c5 +
        minusDetAdjugateVector c1 c3 c5 1 * minusDetEll2 c1 c3 c5 +
        minusDetAdjugateVector c1 c3 c5 2 * minusDetEll4 c1 c3 c5 =
      minusDetAdjugateQuadratic c1 c3 c5 := by
  unfold minusDetAdjugateVector minusDetAdjugateQuadratic
  exact minusDet_adjugateVector_linear_identity
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (minusDetEll0 c1 c3 c5) (minusDetEll2 c1 c3 c5)
    (minusDetEll4 c1 c3 c5)

private theorem minusDetAdjugateVector_even_quadratic
    (c1 c3 c5 : ℝ) :
    symmetricQuadratic
        factorTwoIntrinsicSixUnbalancedEMinus00
        factorTwoIntrinsicSixUnbalancedEMinus02
        factorTwoIntrinsicSixUnbalancedEMinus04
        factorTwoIntrinsicSixUnbalancedEMinus22
        factorTwoIntrinsicSixUnbalancedEMinus24
        factorTwoIntrinsicSixUnbalancedEMinus44
        (-minusDetAdjugateVector c1 c3 c5 0)
        (-minusDetAdjugateVector c1 c3 c5 1)
        (-minusDetAdjugateVector c1 c3 c5 2) =
      factorTwoIntrinsicSixUnbalancedEMinusDet *
        minusDetAdjugateQuadratic c1 c3 c5 := by
  unfold minusDetAdjugateVector minusDetAdjugateQuadratic
  exact minusDet_adjugateVector_neg_quadratic_identity
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    (minusDetEll0 c1 c3 c5) (minusDetEll2 c1 c3 c5)
    (minusDetEll4 c1 c3 c5)

private theorem minusDetAdjugateVector_cross_identity
    (c1 c3 c5 : ℝ) :
    2 * ((-minusDetAdjugateVector c1 c3 c5 0) *
          factorTwoIntrinsicSixUnbalancedKMinus01 +
        (-minusDetAdjugateVector c1 c3 c5 1) *
          factorTwoIntrinsicSixUnbalancedKMinus21 +
        (-minusDetAdjugateVector c1 c3 c5 2) *
          factorTwoIntrinsicSixUnbalancedKMinus41) *
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c1) +
      2 * ((-minusDetAdjugateVector c1 c3 c5 0) *
          factorTwoIntrinsicSixUnbalancedKMinus03 +
        (-minusDetAdjugateVector c1 c3 c5 1) *
          factorTwoIntrinsicSixUnbalancedKMinus23 +
        (-minusDetAdjugateVector c1 c3 c5 2) *
          factorTwoIntrinsicSixUnbalancedKMinus43) *
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c3) +
      2 * ((-minusDetAdjugateVector c1 c3 c5 0) *
          factorTwoIntrinsicSixUnbalancedKMinus05 +
        (-minusDetAdjugateVector c1 c3 c5 1) *
          factorTwoIntrinsicSixUnbalancedKMinus25 +
        (-minusDetAdjugateVector c1 c3 c5 2) *
          factorTwoIntrinsicSixUnbalancedKMinus45) *
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c5) =
      -2 * factorTwoIntrinsicSixUnbalancedEMinusDet *
        minusDetAdjugateQuadratic c1 c3 c5 := by
  calc
    _ = -2 * factorTwoIntrinsicSixUnbalancedEMinusDet *
        (minusDetAdjugateVector c1 c3 c5 0 * minusDetEll0 c1 c3 c5 +
          minusDetAdjugateVector c1 c3 c5 1 * minusDetEll2 c1 c3 c5 +
          minusDetAdjugateVector c1 c3 c5 2 *
            minusDetEll4 c1 c3 c5) := by
      unfold minusDetEll0 minusDetEll2 minusDetEll4
      ring
    _ = _ := by rw [minusDetAdjugateVector_dot]

private theorem minusDetOddQuadratic_scale
    (c1 c3 c5 : ℝ) :
    symmetricQuadratic
        factorTwoIntrinsicSixUnbalancedOPlus11
        factorTwoIntrinsicSixUnbalancedOPlus13
        factorTwoIntrinsicSixUnbalancedOPlus15
        factorTwoIntrinsicSixUnbalancedOPlus33
        factorTwoIntrinsicSixUnbalancedOPlus35
        factorTwoIntrinsicSixUnbalancedOPlus55
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c1)
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c3)
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c5) =
      factorTwoIntrinsicSixUnbalancedEMinusDet ^ 2 *
        symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedOPlus11
          factorTwoIntrinsicSixUnbalancedOPlus13
          factorTwoIntrinsicSixUnbalancedOPlus15
          factorTwoIntrinsicSixUnbalancedOPlus33
          factorTwoIntrinsicSixUnbalancedOPlus35
          factorTwoIntrinsicSixUnbalancedOPlus55 c1 c3 c5 := by
  unfold symmetricQuadratic
  ring

private theorem minusDetExactSix_adjugate_specialization
    (c1 c3 c5 : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorMinusExactSixQuadratic
        (-minusDetAdjugateVector c1 c3 c5 0)
        (-minusDetAdjugateVector c1 c3 c5 1)
        (-minusDetAdjugateVector c1 c3 c5 2)
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c1)
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c3)
        (factorTwoIntrinsicSixUnbalancedEMinusDet * c5) =
      factorTwoIntrinsicSixUnbalancedEMinusDet *
        factorTwoIntrinsicSixUnbalancedTMinusQuadratic c1 c3 c5 := by
  calc
    _ = symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          (-minusDetAdjugateVector c1 c3 c5 0)
          (-minusDetAdjugateVector c1 c3 c5 1)
          (-minusDetAdjugateVector c1 c3 c5 2) +
        (2 * ((-minusDetAdjugateVector c1 c3 c5 0) *
              factorTwoIntrinsicSixUnbalancedKMinus01 +
            (-minusDetAdjugateVector c1 c3 c5 1) *
              factorTwoIntrinsicSixUnbalancedKMinus21 +
            (-minusDetAdjugateVector c1 c3 c5 2) *
              factorTwoIntrinsicSixUnbalancedKMinus41) *
            (factorTwoIntrinsicSixUnbalancedEMinusDet * c1) +
          2 * ((-minusDetAdjugateVector c1 c3 c5 0) *
              factorTwoIntrinsicSixUnbalancedKMinus03 +
            (-minusDetAdjugateVector c1 c3 c5 1) *
              factorTwoIntrinsicSixUnbalancedKMinus23 +
            (-minusDetAdjugateVector c1 c3 c5 2) *
              factorTwoIntrinsicSixUnbalancedKMinus43) *
            (factorTwoIntrinsicSixUnbalancedEMinusDet * c3) +
          2 * ((-minusDetAdjugateVector c1 c3 c5 0) *
              factorTwoIntrinsicSixUnbalancedKMinus05 +
            (-minusDetAdjugateVector c1 c3 c5 1) *
              factorTwoIntrinsicSixUnbalancedKMinus25 +
            (-minusDetAdjugateVector c1 c3 c5 2) *
              factorTwoIntrinsicSixUnbalancedKMinus45) *
            (factorTwoIntrinsicSixUnbalancedEMinusDet * c5)) +
        symmetricQuadratic
          factorTwoIntrinsicSixUnbalancedOPlus11
          factorTwoIntrinsicSixUnbalancedOPlus13
          factorTwoIntrinsicSixUnbalancedOPlus15
          factorTwoIntrinsicSixUnbalancedOPlus33
          factorTwoIntrinsicSixUnbalancedOPlus35
          factorTwoIntrinsicSixUnbalancedOPlus55
          (factorTwoIntrinsicSixUnbalancedEMinusDet * c1)
          (factorTwoIntrinsicSixUnbalancedEMinusDet * c3)
          (factorTwoIntrinsicSixUnbalancedEMinusDet * c5) := by
      unfold factorTwoIntrinsicSixUnbalancedMinorMinusExactSixQuadratic
        factorTwoIntrinsicSixUnbalancedMinorMinusExactFiveQuadratic
        symmetricQuadratic
      ring
    _ = factorTwoIntrinsicSixUnbalancedEMinusDet *
          minusDetAdjugateQuadratic c1 c3 c5 -
        2 * factorTwoIntrinsicSixUnbalancedEMinusDet *
          minusDetAdjugateQuadratic c1 c3 c5 +
        factorTwoIntrinsicSixUnbalancedEMinusDet ^ 2 *
          symmetricQuadratic
            factorTwoIntrinsicSixUnbalancedOPlus11
            factorTwoIntrinsicSixUnbalancedOPlus13
            factorTwoIntrinsicSixUnbalancedOPlus15
            factorTwoIntrinsicSixUnbalancedOPlus33
            factorTwoIntrinsicSixUnbalancedOPlus35
            factorTwoIntrinsicSixUnbalancedOPlus55 c1 c3 c5 := by
      rw [minusDetAdjugateVector_even_quadratic,
        minusDetAdjugateVector_cross_identity,
        minusDetOddQuadratic_scale]
      ring_nf
    _ = _ := by
      rw [factorTwoIntrinsicSixUnbalancedTMinusQuadratic_eq_fractionFree]
      unfold minusDetAdjugateQuadratic minusDetEll0 minusDetEll2
        minusDetEll4
      ring_nf

private theorem minusDetTQuadratic_determinant_witness :
    factorTwoIntrinsicSixUnbalancedTMinusQuadratic
        (factorTwoIntrinsicSixUnbalancedTMinus13 *
            factorTwoIntrinsicSixUnbalancedTMinus35 -
          factorTwoIntrinsicSixUnbalancedTMinus33 *
            factorTwoIntrinsicSixUnbalancedTMinus15)
        (factorTwoIntrinsicSixUnbalancedTMinus13 *
            factorTwoIntrinsicSixUnbalancedTMinus15 -
          factorTwoIntrinsicSixUnbalancedTMinus11 *
            factorTwoIntrinsicSixUnbalancedTMinus35)
        factorTwoIntrinsicSixUnbalancedTMinusMinor =
      factorTwoIntrinsicSixUnbalancedTMinusMinor *
        factorTwoIntrinsicSixUnbalancedTMinusDet := by
  unfold factorTwoIntrinsicSixUnbalancedTMinusQuadratic
    factorTwoIntrinsicSixUnbalancedTMinusMinor
    factorTwoIntrinsicSixUnbalancedTMinusDet leadingMinorTwo
    symmetricQuadratic symmetricDeterminant
  ring

private theorem factorTwoIntrinsicSixUnbalancedTMinusDet_pos_of_combinedBounds
    (hfrontier : MinusP5BorderCombinedBounds) :
    0 < factorTwoIntrinsicSixUnbalancedTMinusDet := by
  let d : ℝ := factorTwoIntrinsicSixUnbalancedEMinusDet
  let p : ℝ :=
    factorTwoIntrinsicSixUnbalancedTMinus13 *
        factorTwoIntrinsicSixUnbalancedTMinus35 -
      factorTwoIntrinsicSixUnbalancedTMinus33 *
        factorTwoIntrinsicSixUnbalancedTMinus15
  let q : ℝ :=
    factorTwoIntrinsicSixUnbalancedTMinus13 *
        factorTwoIntrinsicSixUnbalancedTMinus15 -
      factorTwoIntrinsicSixUnbalancedTMinus11 *
        factorTwoIntrinsicSixUnbalancedTMinus35
  let m : ℝ := factorTwoIntrinsicSixUnbalancedTMinusMinor
  have hd : 0 < d := by
    rcases factorTwoIntrinsicSixUnbalancedEMinus_positive with
      ⟨_he00, _heMinor, hdet⟩
    simpa only [d] using hdet
  have hm : 0 < m := by
    simpa only [m] using factorTwoIntrinsicSixUnbalancedTMinusMinor_pos
  have hne :
      -minusDetAdjugateVector p q m 0 ≠ 0 ∨
        -minusDetAdjugateVector p q m 1 ≠ 0 ∨
        -minusDetAdjugateVector p q m 2 ≠ 0 ∨
        d * p ≠ 0 ∨ d * q ≠ 0 ∨ d * m ≠ 0 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (mul_ne_zero hd.ne' hm.ne')))))
  have hquad :=
    factorTwoIntrinsicSixUnbalancedMinorMinusExactSix_pos_of_combinedBounds
      hfrontier
      (-minusDetAdjugateVector p q m 0)
      (-minusDetAdjugateVector p q m 1)
      (-minusDetAdjugateVector p q m 2)
      (d * p) (d * q) (d * m) hne
  have hspecial := minusDetExactSix_adjugate_specialization p q m
  dsimp only [d] at hspecial hquad
  rw [hspecial] at hquad
  dsimp only [p, q, m] at hquad
  rw [minusDetTQuadratic_determinant_witness] at hquad
  rcases mul_pos_iff.mp hquad with hpos | hneg
  · rcases mul_pos_iff.mp hpos.2 with hminorDet | hminorDetNeg
    · exact hminorDet.2
    · exact False.elim
        ((not_lt_of_ge factorTwoIntrinsicSixUnbalancedTMinusMinor_pos.le)
          hminorDetNeg.1)
  · exact False.elim ((not_lt_of_ge hd.le) hneg.1)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural
