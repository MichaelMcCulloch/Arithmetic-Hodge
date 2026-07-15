import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusMinorStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
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

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusDeterminantStructural
