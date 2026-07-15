import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural
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
  unfold minusDetTransformedSixQuadratic minusDetTransformedFiveQuadratic
    minusDetShift0 minusDetShift1 minusDetShift2 minusDetShift3
    minusDetShift4 minusDetH0 minusDetH1 minusDetH2 minusDetH3 minusDetH4
    minusDetW minusDetG1 minusDetG2 minusDetG3 minusDetG4 minusDetG0
    minusDetMapS minusDetMapD minusDetMapP minusDetMapU
    factorTwoIntrinsicSixUnbalancedMinorMinusLowerFiveQuadratic
    factorTwoIntrinsicSixUnbalancedMinorMinusEvenLowerQuadratic
    factorTwoIntrinsicSixUnbalancedMinorMinusLower00
    factorTwoIntrinsicSixUnbalancedMinorMinusLower02
    factorTwoIntrinsicSixUnbalancedMinorMinusLower22
    factorTwoIntrinsicSixUnbalancedEMinusP4Sum
    factorTwoIntrinsicSixUnbalancedEMinusP4Difference
    factorTwoIntrinsicSixUnbalancedKMinusOneSum
    factorTwoIntrinsicSixUnbalancedKMinusOneDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearSum
    factorTwoIntrinsicSixUnbalancedKMinusShearDifference
    factorTwoIntrinsicSixUnbalancedKMinusShearTail
    factorTwoIntrinsicSixUnbalancedKMinus05
    factorTwoIntrinsicSixUnbalancedKMinus25
    factorTwoIntrinsicSixUnbalancedKMinus45
    intrinsicStaticMinusOddLower minusP4Lower symmetricQuadratic
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural
