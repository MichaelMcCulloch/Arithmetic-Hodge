import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC1Structural

noncomputable section

open MeasureTheory Polynomial Real Set
open CenteredOddOneThreeEnergy
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseLowSchur

/-! ## Cancellation-preserving endpoint reduction -/

private def e00p : ℝ := factorTwoStructuralPhaseLow00 1
private def e02p : ℝ := factorTwoStructuralPhaseLow02 1
private def e04p : ℝ := factorTwoIntrinsicFourP45Cross04 1
private def e22p : ℝ := factorTwoStructuralPhaseLow22 1
private def e24p : ℝ := factorTwoIntrinsicFourP45Cross24 1
private def e44p : ℝ := factorTwoIntrinsicSixP4Diagonal 1

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

private def u0 : ℝ := factorTwoIntrinsicAlternating01
private def u2 : ℝ := factorTwoIntrinsicAlternating21
private def u4 : ℝ := factorTwoIntrinsicFourP45Cross41
private def v0 : ℝ := factorTwoIntrinsicAlternating03
private def v2 : ℝ := factorTwoIntrinsicAlternating23
private def v4 : ℝ := factorTwoIntrinsicFourP45Cross43

private def lowDetPlus : ℝ := e00p * e22p - e02p ^ 2

private def lowMixedOne : ℝ :=
  e00m * e22p + e00p * e22m - 2 * e02p * e02m

private def evenDetPlus : ℝ :=
  symmetricDeterminant e00p e02p e04p e22p e24p e44p

private def evenMixedOne : ℝ :=
  mixedDeterminantOne
    e00p e02p e04p e22p e24p e44p
    e00m e02m e04m e22m e24m e44m

private def oddDetPlus : ℝ := o11p * o33p - o13p ^ 2

private def oddMixedOne : ℝ :=
  o11p * o33m + o11m * o33p - 2 * o13p * o13m

private def lowAdjugatePair
    (x0 x2 y0 y2 : ℝ) : ℝ :=
  e22p * x0 * y0 - e02p * (x0 * y2 + x2 * y0) +
    e00p * x2 * y2

private def fullAdjugatePair
    (x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  (e22p * e44p - e24p ^ 2) * x0 * y0 +
    (e04p * e24p - e02p * e44p) * (x0 * y2 + x2 * y0) +
    (e02p * e24p - e04p * e22p) * (x0 * y4 + x4 * y0) +
    (e00p * e44p - e04p ^ 2) * x2 * y2 +
    (e02p * e04p - e00p * e24p) * (x2 * y4 + x4 * y2) +
    (e00p * e22p - e02p ^ 2) * x4 * y4

private def lowCoupling : ℝ :=
  o33p * lowAdjugatePair u0 u2 u0 u2 -
    2 * o13p * lowAdjugatePair u0 u2 v0 v2 +
    o11p * lowAdjugatePair v0 v2 v0 v2

private def fullCoupling : ℝ :=
  o33p * fullAdjugatePair u0 u2 u4 u0 u2 u4 -
    2 * o13p * fullAdjugatePair u0 u2 u4 v0 v2 v4 +
    o11p * fullAdjugatePair v0 v2 v4 v0 v2 v4

private def lowCoefficientOne : ℝ :=
  lowDetPlus * oddMixedOne + lowMixedOne * oddDetPlus - lowCoupling

private def p4Polar (x0 x2 : ℝ) : ℝ :=
  e22p * e04p * x0 - e02p * (e04p * x2 + e24p * x0) +
    e00p * e24p * x2

private def p4ResidualOne : ℝ := lowDetPlus * u4 - p4Polar u0 u2
private def p4ResidualThree : ℝ := lowDetPlus * v4 - p4Polar v0 v2

private def p4ResidualOddAdjugate : ℝ :=
  o33p * p4ResidualOne ^ 2 -
    2 * o13p * p4ResidualOne * p4ResidualThree +
    o11p * p4ResidualThree ^ 2

/-! ## Aligned coordinates -/

private def plusStrong : ℝ := e00p + 2 * e02p + e22p
private def plusSkew : ℝ := e00p - e22p
private def plusWeak : ℝ := e00p - 2 * e02p + e22p
private def plusCrossSum : ℝ := e04p + e24p
private def plusCrossDifference : ℝ := e24p - e04p

private def minusStrong : ℝ := e00m + 2 * e02m + e22m
private def minusSkew : ℝ := e00m - e22m
private def minusWeak : ℝ := e00m - 2 * e02m + e22m
private def minusCrossSum : ℝ := e04m + e24m
private def minusCrossDifference : ℝ := e24m - e04m

private def uSum : ℝ := u0 + u2
private def uDifference : ℝ := u0 - u2
private def vSum : ℝ := v0 + v2
private def vDifference : ℝ := v0 - v2

private def alignedLowPair (s d t e : ℝ) : ℝ :=
  (plusWeak * s * t - plusSkew * (s * e + d * t) +
    plusStrong * d * e) / 4

private def oddSumQuadratic : ℝ :=
  o33p * uSum ^ 2 - 2 * o13p * uSum * vSum + o11p * vSum ^ 2

private def oddDifferenceQuadratic : ℝ :=
  o33p * uDifference ^ 2 -
    2 * o13p * uDifference * vDifference +
    o11p * vDifference ^ 2

private def oddSumDifferencePolar : ℝ :=
  2 * (o33p * uSum * uDifference -
    o13p * (uSum * vDifference + uDifference * vSum) +
    o11p * vSum * vDifference)

private def strongBracket : ℝ :=
  plusStrong * oddMixedOne + minusStrong * oddDetPlus - oddSumQuadratic

private def weakBracket : ℝ :=
  minusWeak * oddDetPlus - oddDifferenceQuadratic

private def skewBracket : ℝ :=
  oddSumDifferencePolar - 2 * minusSkew * oddDetPlus -
    plusSkew * oddMixedOne

private def strongBoxForm
    (A Am a b c am bm cm s t : ℝ) : ℝ :=
  A * (a * cm + am * c - 2 * b * bm) +
    Am * (a * c - b ^ 2) -
    (c * s ^ 2 - 2 * b * s * t + a * t ^ 2)

private def weakBoxForm (Rm a b c d e : ℝ) : ℝ :=
  Rm * (a * c - b ^ 2) -
    (c * d ^ 2 - 2 * b * d * e + a * e ^ 2)

private theorem strongBracket_eq_boxForm :
    strongBracket = strongBoxForm plusStrong minusStrong
      o11p o13p o33p o11m o13m o33m uSum vSum := by
  unfold strongBracket strongBoxForm oddMixedOne oddDetPlus
    oddSumQuadratic
  ring

private theorem weakBracket_eq_boxForm :
    weakBracket = weakBoxForm minusWeak o11p o13p o33p
      uDifference vDifference := by
  unfold weakBracket weakBoxForm oddDetPlus oddDifferenceQuadratic
  ring

private theorem lowDetPlus_eq_aligned :
    lowDetPlus =
      (plusStrong * plusWeak - plusSkew ^ 2) / 4 := by
  unfold lowDetPlus plusStrong plusWeak plusSkew
  ring

private theorem lowMixedOne_eq_aligned :
    lowMixedOne =
      (plusStrong * minusWeak + minusStrong * plusWeak -
        2 * plusSkew * minusSkew) / 4 := by
  unfold lowMixedOne plusStrong plusWeak plusSkew
    minusStrong minusWeak minusSkew
  ring

private theorem lowAdjugatePair_eq_aligned
    (x0 x2 y0 y2 : ℝ) :
    lowAdjugatePair x0 x2 y0 y2 =
      (plusWeak * (x0 + x2) * (y0 + y2) -
          plusSkew * ((x0 + x2) * (y0 - y2) +
            (x0 - x2) * (y0 + y2)) +
        plusStrong * (x0 - x2) * (y0 - y2)) / 4 := by
  unfold lowAdjugatePair plusStrong plusWeak plusSkew
  ring

private theorem lowCoupling_eq_aligned :
    lowCoupling =
      o33p * alignedLowPair uSum uDifference uSum uDifference -
        2 * o13p * alignedLowPair uSum uDifference vSum vDifference +
        o11p * alignedLowPair vSum vDifference vSum vDifference := by
  unfold lowCoupling alignedLowPair uSum uDifference vSum vDifference
    lowAdjugatePair plusStrong plusWeak plusSkew
  ring

private theorem lowCoefficientOne_eq_aligned :
    lowCoefficientOne =
      ((plusStrong * plusWeak - plusSkew ^ 2) / 4) * oddMixedOne +
        ((plusStrong * minusWeak + minusStrong * plusWeak -
          2 * plusSkew * minusSkew) / 4) * oddDetPlus -
        (o33p * alignedLowPair uSum uDifference uSum uDifference -
          2 * o13p * alignedLowPair uSum uDifference vSum vDifference +
          o11p * alignedLowPair vSum vDifference vSum vDifference) := by
  unfold lowCoefficientOne
  rw [lowDetPlus_eq_aligned, lowMixedOne_eq_aligned,
    lowCoupling_eq_aligned]

private theorem four_mul_lowCoefficientOne_eq_brackets :
    4 * lowCoefficientOne =
      plusWeak * strongBracket + plusStrong * weakBracket +
        plusSkew * skewBracket := by
  unfold lowCoefficientOne lowDetPlus lowMixedOne lowCoupling
    lowAdjugatePair strongBracket weakBracket skewBracket
    oddSumQuadratic oddDifferenceQuadratic oddSumDifferencePolar
    oddMixedOne oddDetPlus plusStrong plusSkew plusWeak
    minusStrong minusSkew minusWeak uSum uDifference vSum vDifference
  ring

private theorem p4Polar_eq_aligned (x0 x2 : ℝ) :
    p4Polar x0 x2 =
      (plusWeak * plusCrossSum * (x0 + x2) -
          plusSkew * plusCrossSum * (x0 - x2) +
          plusSkew * plusCrossDifference * (x0 + x2) -
        plusStrong * plusCrossDifference * (x0 - x2)) / 4 := by
  unfold p4Polar plusStrong plusWeak plusSkew plusCrossSum
    plusCrossDifference
  ring

/-! ## Exact Schur residual coordinates -/

private def schurSum : ℝ :=
  -(plusWeak * plusCrossSum + plusSkew * plusCrossDifference) / 2

private def schurDifference : ℝ :=
  (plusSkew * plusCrossSum + plusStrong * plusCrossDifference) / 2

private def evenMinusSchurReserve : ℝ :=
  (minusStrong * schurSum ^ 2 +
      2 * minusSkew * schurSum * schurDifference +
      minusWeak * schurDifference ^ 2) / 4 +
    (minusCrossSum * schurSum -
        minusCrossDifference * schurDifference) * lowDetPlus +
    e44m * lowDetPlus ^ 2

private def reserveComparisonQuadratic (R : ℝ) : ℝ :=
  (101 / 10000 : ℝ) * R ^ 2 -
    (761 / 10000000) * R + 123 / 1000000000

private def residualUpperEnvelope (R : ℝ) : ℝ :=
  (353 / 100000 : ℝ) * R - 1847 / 100000000

private def residualThreeAbsEnvelope (R : ℝ) : ℝ :=
  (133 / 5000 : ℝ) * R - 733 / 5000000

private def residualOneLowerEnvelope (R : ℝ) : ℝ :=
  -(781 / 100000 : ℝ) * R + 406 / 10000000

private def residualThreeUpperEnvelope (R : ℝ) : ℝ :=
  -(523 / 20000 : ℝ) * R + 301 / 2000000

private def schurSumMagnitudeLower (R : ℝ) : ℝ :=
  (R * (1924 / 10000 : ℝ) +
    (-141 / 1000000) * (19581 / 1000000)) / 2

private def schurSumMagnitudeUpper (R : ℝ) : ℝ :=
  (R * (193081 / 1000000 : ℝ) +
    (1919 / 1000000) * (19581 / 1000000)) / 2

private def schurDifferenceLower : ℝ :=
  ((-141 / 1000000 : ℝ) * (193081 / 1000000) +
    (547765 / 1000000) * (1925 / 100000)) / 2

private def schurDifferenceUpper : ℝ :=
  ((1919 / 1000000 : ℝ) * (193081 / 1000000) +
    (549941 / 1000000) * (19581 / 1000000)) / 2

private def lowDetLower (R : ℝ) : ℝ :=
  ((547765 / 1000000 : ℝ) * R - (1919 / 1000000) ^ 2) / 4

private def lowDetUpper (R : ℝ) : ℝ :=
  ((549941 / 1000000 : ℝ) * R) / 4

private def coarseSchurReserve (R : ℝ) : ℝ :=
  ((2198709 / 1000000 : ℝ) * schurSumMagnitudeLower R ^ 2 -
      2 * (79531 / 1000000) * schurSumMagnitudeUpper R *
        schurDifferenceUpper +
      (18409 / 1000000) * schurDifferenceLower ^ 2) / 4 +
    (-(300081 / 1000000 : ℝ) * schurSumMagnitudeUpper R -
        (70081 / 1000000) * schurDifferenceUpper) * lowDetUpper R +
    (12 / 25) * lowDetLower R ^ 2

private def alignedResidualForm (s d z : ℝ) : ℝ :=
  (plusWeak * (plusStrong * z - plusCrossSum * s) +
      plusSkew * (plusCrossSum * d - plusCrossDifference * s) +
      plusStrong * plusCrossDifference * d - plusSkew ^ 2 * z) / 4

private theorem lowDet_mul_evenMixed_sub_evenDet_mul_lowMixed_eq_reserve :
    lowDetPlus * evenMixedOne - evenDetPlus * lowMixedOne =
      evenMinusSchurReserve := by
  unfold evenMinusSchurReserve schurSum schurDifference
    lowDetPlus evenMixedOne evenDetPlus lowMixedOne
    plusStrong plusSkew plusWeak plusCrossSum plusCrossDifference
    minusStrong minusSkew minusWeak minusCrossSum minusCrossDifference
    mixedDeterminantOne symmetricDeterminant
  ring

private theorem alignedResidualForm_eq_schur
    (s d z : ℝ) :
    alignedResidualForm s d z =
      (s * schurSum + d * schurDifference) / 2 + z * lowDetPlus := by
  unfold alignedResidualForm schurSum schurDifference
  rw [lowDetPlus_eq_aligned]
  ring

private theorem p4ResidualOne_eq_alignedResidualForm :
    p4ResidualOne = alignedResidualForm uSum uDifference u4 := by
  rw [alignedResidualForm_eq_schur]
  unfold p4ResidualOne schurSum schurDifference uSum uDifference
  rw [p4Polar_eq_aligned]
  ring

private theorem p4ResidualThree_eq_alignedResidualForm :
    p4ResidualThree = alignedResidualForm vSum vDifference v4 := by
  rw [alignedResidualForm_eq_schur]
  unfold p4ResidualThree schurSum schurDifference vSum vDifference
  rw [p4Polar_eq_aligned]
  ring

private theorem residualOddAdjugate_completion :
    o33p * p4ResidualOddAdjugate =
      (o33p * p4ResidualOne - o13p * p4ResidualThree) ^ 2 +
        oddDetPlus * p4ResidualThree ^ 2 := by
  unfold p4ResidualOddAdjugate oddDetPlus
  ring

private theorem e44m_gt_twelve_div_twenty_five :
    (12 / 25 : ℝ) < e44m := by
  change (12 / 25 : ℝ) < factorTwoIntrinsicP4PhaseDiagonal (-1)
  simpa [factorTwoIntrinsicP4MinusDiagonalLower] using
    factorTwoIntrinsicP4MinusDiagonalLower_lt_phaseDiagonal

private theorem evenMinusSchurReserve_gt_comparison :
    reserveComparisonQuadratic plusWeak < evenMinusSchurReserve := by
  rcases factorTwoIntrinsicP4_positive_aligned_bounds with
    ⟨hAL, hAU, hXL, hXU, _hSL0, hSU, hRL, hRU, _hTL0, hTU⟩
  rcases factorTwoIntrinsicP4_negative_aligned_bounds with
    ⟨hAmL, _hAmU, _hXmL, hXmU, _hSmL, hSmU,
      hRmL, _hRmU, _hDmL, hDmU⟩
  change (547765 / 1000000 : ℝ) < plusStrong at hAL
  change plusStrong < (549941 / 1000000 : ℝ) at hAU
  change (-141 / 1000000 : ℝ) < plusSkew at hXL
  change plusSkew < (1919 / 1000000 : ℝ) at hXU
  change plusCrossSum < (193081 / 1000000 : ℝ) at hSU
  change (6065 / 1000000 : ℝ) < plusWeak at hRL
  change plusWeak < (8241 / 1000000 : ℝ) at hRU
  change plusCrossDifference < (19581 / 1000000 : ℝ) at hTU
  change (2198709 / 1000000 : ℝ) < minusStrong at hAmL
  change minusSkew < (79531 / 1000000 : ℝ) at hXmU
  change minusCrossSum < (300081 / 1000000 : ℝ) at hSmU
  change (18409 / 1000000 : ℝ) < minusWeak at hRmL
  change minusCrossDifference < (70081 / 1000000 : ℝ) at hDmU
  have hsharp := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds
  have hSL : (1924 / 10000 : ℝ) < plusCrossSum := by
    simpa [plusCrossSum, e04p, e24p,
      factorTwoIntrinsicP4PlusCrossSum] using hsharp.1
  have hTL : (1925 / 100000 : ℝ) < plusCrossDifference := by
    simpa [plusCrossDifference, e04p, e24p,
      factorTwoIntrinsicP4PlusCrossDifference] using hsharp.2
  have hA0 : 0 < plusStrong := lt_trans (by norm_num) hAL
  have hR0 : 0 < plusWeak := lt_trans (by norm_num) hRL
  have hS0 : 0 < plusCrossSum := lt_trans (by norm_num) hSL
  have hT0 : 0 < plusCrossDifference := lt_trans (by norm_num) hTL
  have hXTLower :
      (-141 / 1000000 : ℝ) * (19581 / 1000000) <
        plusSkew * plusCrossDifference := by
    by_cases hX : 0 ≤ plusSkew
    · have hprod : 0 ≤ plusSkew * plusCrossDifference :=
        mul_nonneg hX hT0.le
      norm_num at hprod ⊢
      linarith
    · have hXneg : plusSkew < 0 := lt_of_not_ge hX
      calc
        (-141 / 1000000 : ℝ) * (19581 / 1000000) <
            plusSkew * (19581 / 1000000) :=
          mul_lt_mul_of_pos_right
            hXL (by norm_num)
        _ < plusSkew * plusCrossDifference :=
          mul_lt_mul_of_neg_left
            hTU hXneg
  have hXTUpper : plusSkew * plusCrossDifference <
      (1919 / 1000000 : ℝ) * (19581 / 1000000) := by
    by_cases hX : plusSkew ≤ 0
    · have hprod : plusSkew * plusCrossDifference ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hX hT0.le
      norm_num at hprod ⊢
      linarith
    · have hX0 : 0 < plusSkew := lt_of_not_ge hX
      calc
        plusSkew * plusCrossDifference <
            (1919 / 1000000 : ℝ) * plusCrossDifference :=
          mul_lt_mul_of_pos_right
            hXU hT0
        _ < (1919 / 1000000 : ℝ) * (19581 / 1000000) :=
          mul_lt_mul_of_pos_left
            hTU
            (by norm_num)
  have hRSLo : plusWeak * (1924 / 10000 : ℝ) <
      plusWeak * plusCrossSum :=
    mul_lt_mul_of_pos_left hSL hR0
  have hRSHi : plusWeak * plusCrossSum <
      plusWeak * (193081 / 1000000 : ℝ) :=
    mul_lt_mul_of_pos_left
      hSU hR0
  have hsMagL : schurSumMagnitudeLower plusWeak < -schurSum := by
    unfold schurSumMagnitudeLower schurSum
    linarith
  have hsMagU : -schurSum < schurSumMagnitudeUpper plusWeak := by
    unfold schurSumMagnitudeUpper schurSum
    linarith
  have hsMagLower0 : 0 < schurSumMagnitudeLower plusWeak := by
    unfold schurSumMagnitudeLower
    norm_num at hRL ⊢
    nlinarith
  have hsNeg : schurSum < 0 := by linarith
  have hsMagUpper0 : 0 < schurSumMagnitudeUpper plusWeak := by linarith
  have hXSLower :
      (-141 / 1000000 : ℝ) * (193081 / 1000000) <
        plusSkew * plusCrossSum := by
    by_cases hX : 0 ≤ plusSkew
    · have hprod : 0 ≤ plusSkew * plusCrossSum := mul_nonneg hX hS0.le
      norm_num at hprod ⊢
      linarith
    · have hXneg : plusSkew < 0 := lt_of_not_ge hX
      calc
        (-141 / 1000000 : ℝ) * (193081 / 1000000) <
            plusSkew * (193081 / 1000000) :=
          mul_lt_mul_of_pos_right
            hXL (by norm_num)
        _ < plusSkew * plusCrossSum :=
          mul_lt_mul_of_neg_left
            hSU hXneg
  have hXSUpper : plusSkew * plusCrossSum <
      (1919 / 1000000 : ℝ) * (193081 / 1000000) := by
    by_cases hX : plusSkew ≤ 0
    · have hprod : plusSkew * plusCrossSum ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hX hS0.le
      norm_num at hprod ⊢
      linarith
    · have hX0 : 0 < plusSkew := lt_of_not_ge hX
      calc
        plusSkew * plusCrossSum <
            (1919 / 1000000 : ℝ) * plusCrossSum :=
          mul_lt_mul_of_pos_right
            hXU hS0
        _ < (1919 / 1000000 : ℝ) * (193081 / 1000000) :=
          mul_lt_mul_of_pos_left
            hSU
            (by norm_num)
  have hATLower :
      (547765 / 1000000 : ℝ) * (1925 / 100000) <
        plusStrong * plusCrossDifference := by
    calc
      _ < plusStrong * (1925 / 100000) :=
        mul_lt_mul_of_pos_right
          hAL (by norm_num)
      _ < plusStrong * plusCrossDifference := mul_lt_mul_of_pos_left hTL hA0
  have hATUpper : plusStrong * plusCrossDifference <
      (549941 / 1000000 : ℝ) * (19581 / 1000000) := by
    calc
      _ < (549941 / 1000000 : ℝ) * plusCrossDifference :=
        mul_lt_mul_of_pos_right
          hAU hT0
      _ < _ := mul_lt_mul_of_pos_left
        hTU
        (by norm_num)
  have hdL : schurDifferenceLower < schurDifference := by
    unfold schurDifferenceLower schurDifference
    linarith
  have hdU : schurDifference < schurDifferenceUpper := by
    unfold schurDifferenceUpper schurDifference
    linarith
  have hdLower0 : 0 < schurDifferenceLower := by
    norm_num [schurDifferenceLower]
  have hd0 : 0 < schurDifference := lt_trans hdLower0 hdL
  have hdUpper0 : 0 < schurDifferenceUpper := lt_trans hd0 hdU
  have hXsum0 : 0 < plusSkew + (1919 / 1000000 : ℝ) := by
    norm_num at hXL ⊢
    linarith
  have hXsqU : plusSkew ^ 2 < (1919 / 1000000 : ℝ) ^ 2 := by
    have hmul := mul_pos
      (sub_pos.mpr hXU) hXsum0
    nlinarith
  have hARLower : (547765 / 1000000 : ℝ) * plusWeak <
      plusStrong * plusWeak :=
    mul_lt_mul_of_pos_right
      hAL hR0
  have hARUpper : plusStrong * plusWeak <
      (549941 / 1000000 : ℝ) * plusWeak :=
    mul_lt_mul_of_pos_right
      hAU hR0
  have hzL : lowDetLower plusWeak < lowDetPlus := by
    rw [lowDetPlus_eq_aligned]
    unfold lowDetLower
    linarith
  have hzU : lowDetPlus < lowDetUpper plusWeak := by
    rw [lowDetPlus_eq_aligned]
    unfold lowDetUpper
    nlinarith [sq_nonneg plusSkew]
  have hzLower0 : 0 < lowDetLower plusWeak := by
    unfold lowDetLower
    norm_num at hRL ⊢
    nlinarith
  have hz0 : 0 < lowDetPlus := lt_trans hzLower0 hzL
  have hzUpper0 : 0 < lowDetUpper plusWeak := lt_trans hz0 hzU
  have hsSqL : schurSumMagnitudeLower plusWeak ^ 2 < schurSum ^ 2 := by
    have hmul := mul_pos (sub_pos.mpr hsMagL)
      (by linarith : 0 < -schurSum + schurSumMagnitudeLower plusWeak)
    nlinarith
  have hdSqL : schurDifferenceLower ^ 2 < schurDifference ^ 2 := by
    have hmul := mul_pos (sub_pos.mpr hdL)
      (by positivity : 0 < schurDifference + schurDifferenceLower)
    nlinarith
  have hzSqL : lowDetLower plusWeak ^ 2 < lowDetPlus ^ 2 := by
    have hmul := mul_pos (sub_pos.mpr hzL)
      (by positivity : 0 < lowDetPlus + lowDetLower plusWeak)
    nlinarith
  have hAm : (2198709 / 1000000 : ℝ) < minusStrong := hAmL
  have hXm0 : 0 < minusSkew := by
    have h := factorTwoIntrinsicP4_negative_aligned_bounds.2.2.1
    simpa only [minusSkew, e00m, e22m] using lt_trans (by norm_num) h
  have hXm : minusSkew < (79531 / 1000000 : ℝ) := hXmU
  have hRm : (18409 / 1000000 : ℝ) < minusWeak := hRmL
  have hSm0 : 0 < minusCrossSum := by
    have h := factorTwoIntrinsicP4_negative_aligned_bounds.2.2.2.2.1
    simpa only [minusCrossSum, e04m, e24m] using lt_trans (by norm_num) h
  have hSm : minusCrossSum < (300081 / 1000000 : ℝ) := hSmU
  have hDm0 : 0 < minusCrossDifference := by
    have h := factorTwoIntrinsicP4_negative_aligned_bounds.2.2.2.2.2.2.2.2.1
    simpa only [minusCrossDifference, e04m, e24m] using
      lt_trans (by norm_num) h
  have hDm : minusCrossDifference < (70081 / 1000000 : ℝ) := hDmU
  have hAmTerm :
      (2198709 / 1000000 : ℝ) * schurSumMagnitudeLower plusWeak ^ 2 <
        minusStrong * schurSum ^ 2 := by
    calc
      _ < minusStrong * schurSumMagnitudeLower plusWeak ^ 2 :=
        mul_lt_mul_of_pos_right hAm (sq_pos_of_pos hsMagLower0)
      _ < _ := mul_lt_mul_of_pos_left hsSqL (lt_trans (by norm_num) hAm)
  have hCrossMagnitude :
      minusSkew * (-schurSum) * schurDifference <
        (79531 / 1000000 : ℝ) * schurSumMagnitudeUpper plusWeak *
          schurDifferenceUpper := by
    calc
      _ < (79531 / 1000000 : ℝ) * (-schurSum) * schurDifference :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hXm (by linarith)) hd0
      _ < (79531 / 1000000 : ℝ) *
          schurSumMagnitudeUpper plusWeak * schurDifference :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hsMagU (by norm_num)) hd0
      _ < _ := mul_lt_mul_of_pos_left hdU
        (mul_pos (by norm_num) hsMagUpper0)
  have hRmTerm :
      (18409 / 1000000 : ℝ) * schurDifferenceLower ^ 2 <
        minusWeak * schurDifference ^ 2 := by
    calc
      _ < minusWeak * schurDifferenceLower ^ 2 :=
        mul_lt_mul_of_pos_right hRm (sq_pos_of_pos hdLower0)
      _ < _ := mul_lt_mul_of_pos_left hdSqL (lt_trans (by norm_num) hRm)
  have hSmMagnitude : minusCrossSum * (-schurSum) * lowDetPlus <
      (300081 / 1000000 : ℝ) * schurSumMagnitudeUpper plusWeak *
        lowDetUpper plusWeak := by
    calc
      _ < (300081 / 1000000 : ℝ) * (-schurSum) * lowDetPlus :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hSm (by linarith)) hz0
      _ < (300081 / 1000000 : ℝ) *
          schurSumMagnitudeUpper plusWeak * lowDetPlus :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hsMagU (by norm_num)) hz0
      _ < _ := mul_lt_mul_of_pos_left hzU
        (mul_pos (by norm_num) hsMagUpper0)
  have hDmMagnitude : minusCrossDifference * schurDifference * lowDetPlus <
      (70081 / 1000000 : ℝ) * schurDifferenceUpper *
        lowDetUpper plusWeak := by
    calc
      _ < (70081 / 1000000 : ℝ) * schurDifference * lowDetPlus :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hDm hd0) hz0
      _ < (70081 / 1000000 : ℝ) *
          schurDifferenceUpper * lowDetPlus :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hdU (by norm_num)) hz0
      _ < _ := mul_lt_mul_of_pos_left hzU
        (mul_pos (by norm_num) hdUpper0)
  have hFterm : (12 / 25 : ℝ) * lowDetLower plusWeak ^ 2 <
      e44m * lowDetPlus ^ 2 := by
    calc
      _ < e44m * lowDetLower plusWeak ^ 2 :=
        mul_lt_mul_of_pos_right e44m_gt_twelve_div_twenty_five
          (sq_pos_of_pos hzLower0)
      _ < _ := mul_lt_mul_of_pos_left hzSqL
        (lt_trans (by norm_num) e44m_gt_twelve_div_twenty_five)
  have hcoarse : coarseSchurReserve plusWeak < evenMinusSchurReserve := by
    unfold coarseSchurReserve evenMinusSchurReserve
    nlinarith
  have hcomparison : reserveComparisonQuadratic plusWeak <
      coarseSchurReserve plusWeak := by
    unfold reserveComparisonQuadratic coarseSchurReserve
      schurSumMagnitudeLower schurSumMagnitudeUpper
      schurDifferenceLower schurDifferenceUpper lowDetLower lowDetUpper
    norm_num
    nlinarith [sq_nonneg plusWeak]
  exact hcomparison.trans hcoarse

private theorem plusSkew_sq_lt_upper :
    plusSkew ^ 2 < (1919 / 1000000 : ℝ) ^ 2 := by
  have hp := factorTwoIntrinsicP4_positive_aligned_bounds
  have hXL : (-141 / 1000000 : ℝ) < plusSkew := by
    simpa only [plusSkew, e00p, e22p] using hp.2.2.1
  have hXU : plusSkew < (1919 / 1000000 : ℝ) := by
    simpa only [plusSkew, e00p, e22p] using hp.2.2.2.1
  have hsum : 0 < plusSkew + (1919 / 1000000 : ℝ) := by
    norm_num at hXL ⊢
    linarith
  have hmul := mul_pos (sub_pos.mpr hXU) hsum
  nlinarith

private theorem p4ResidualOne_gt_lowerEnvelope :
    residualOneLowerEnvelope plusWeak < p4ResidualOne := by
  rcases factorTwoIntrinsicP4_positive_aligned_bounds with
    ⟨hAL, _hAU, hXL, hXU, _hSL0, hSU, hRL, _hRU, _hTL0, hTU⟩
  change (547765 / 1000000 : ℝ) < plusStrong at hAL
  change (-141 / 1000000 : ℝ) < plusSkew at hXL
  change plusSkew < (1919 / 1000000 : ℝ) at hXU
  change plusCrossSum < (193081 / 1000000 : ℝ) at hSU
  change (6065 / 1000000 : ℝ) < plusWeak at hRL
  change plusCrossDifference < (19581 / 1000000 : ℝ) at hTU
  have hsharp := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds
  have hSL : (1924 / 10000 : ℝ) < plusCrossSum := by
    simpa [plusCrossSum, e04p, e24p,
      factorTwoIntrinsicP4PlusCrossSum] using hsharp.1
  have hTL : (1925 / 100000 : ℝ) < plusCrossDifference := by
    simpa [plusCrossDifference, e04p, e24p,
      factorTwoIntrinsicP4PlusCrossDifference] using hsharp.2
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨husL, husU, hudL, hudU, _hvsL, _hvsU, _hvdL, _hvdU⟩
  rcases factorTwoIntrinsicFourP45Cross41_bounds with ⟨hu4L, hu4U⟩
  have hA0 : 0 < plusStrong := lt_trans (by norm_num) hAL
  have hR0 : 0 < plusWeak := lt_trans (by norm_num) hRL
  have hS0 : 0 < plusCrossSum := lt_trans (by norm_num) hSL
  have hT0 : 0 < plusCrossDifference := lt_trans (by norm_num) hTL
  have hus0 : 0 < uSum := by
    simpa only [uSum, u0, u2] using lt_trans (by norm_num) husL
  have hud0 : 0 < uDifference := by
    simpa only [uDifference, u0, u2] using lt_trans (by norm_num) hudL
  have hu40 : 0 < u4 := by
    simpa only [u4] using lt_trans (by norm_num) hu4L
  have hAzL :
      (547765 / 1000000 : ℝ) * (141 / 1000) < plusStrong * u4 := by
    calc
      _ < plusStrong * (141 / 1000) :=
        mul_lt_mul_of_pos_right
          (by simpa only [plusStrong, e00p, e02p, e22p] using hAL) (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left (by simpa only [u4] using hu4L) hA0
  have hSsU : plusCrossSum * uSum <
      (193081 / 1000000 : ℝ) * (56173 / 100000) := by
    calc
      _ < (193081 / 1000000 : ℝ) * uSum :=
        mul_lt_mul_of_pos_right
          (by simpa only [plusCrossSum, e04p, e24p] using hSU) hus0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [uSum, u0, u2] using husU) (by norm_num)
  have hCoeffR :
      (547765 / 1000000 : ℝ) * (141 / 1000) -
          (193081 / 1000000) * (56173 / 100000) <
        plusStrong * u4 - plusCrossSum * uSum := by linarith
  have hRterm :
      plusWeak * ((547765 / 1000000 : ℝ) * (141 / 1000) -
          (193081 / 1000000) * (56173 / 100000)) <
        plusWeak * (plusStrong * u4 - plusCrossSum * uSum) :=
    mul_lt_mul_of_pos_left hCoeffR hR0
  have hSdL : (1924 / 10000 : ℝ) * (1687 / 100000) <
      plusCrossSum * uDifference := by
    calc
      _ < plusCrossSum * (1687 / 100000) :=
        mul_lt_mul_of_pos_right hSL (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [uDifference, u0, u2] using hudL) hS0
  have hTsU : plusCrossDifference * uSum <
      (19581 / 1000000 : ℝ) * (56173 / 100000) := by
    calc
      _ < (19581 / 1000000 : ℝ) * uSum :=
        mul_lt_mul_of_pos_right
          (by simpa only [plusCrossDifference, e04p, e24p] using hTU) hus0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [uSum, u0, u2] using husU) (by norm_num)
  have hCoeffXL :
      (1924 / 10000 : ℝ) * (1687 / 100000) -
          (19581 / 1000000) * (56173 / 100000) <
        plusCrossSum * uDifference - plusCrossDifference * uSum := by linarith
  have hCoeffXU :
      plusCrossSum * uDifference - plusCrossDifference * uSum < 0 := by
    have hSdU : plusCrossSum * uDifference <
        (193081 / 1000000 : ℝ) * (1692 / 100000) := by
      calc
        _ < (193081 / 1000000 : ℝ) * uDifference :=
          mul_lt_mul_of_pos_right
            (by simpa only [plusCrossSum, e04p, e24p] using hSU) hud0
        _ < _ := mul_lt_mul_of_pos_left
          (by simpa only [uDifference, u0, u2] using hudU) (by norm_num)
    have hTsL : (1925 / 100000 : ℝ) * (56168 / 100000) <
        plusCrossDifference * uSum := by
      calc
        _ < plusCrossDifference * (56168 / 100000) :=
          mul_lt_mul_of_pos_right hTL (by norm_num)
        _ < _ := mul_lt_mul_of_pos_left
          (by simpa only [uSum, u0, u2] using husL) hT0
    norm_num at hSdU hTsL ⊢
    linarith
  have hXterm :
      (1919 / 1000000 : ℝ) *
          ((1924 / 10000) * (1687 / 100000) -
            (19581 / 1000000) * (56173 / 100000)) <
        plusSkew *
          (plusCrossSum * uDifference - plusCrossDifference * uSum) := by
    by_cases hX : plusSkew ≤ 0
    · have hprod : 0 ≤ plusSkew *
          (plusCrossSum * uDifference - plusCrossDifference * uSum) :=
        mul_nonneg_of_nonpos_of_nonpos hX hCoeffXU.le
      norm_num at hprod ⊢
      linarith
    · have hX0 : 0 < plusSkew := lt_of_not_ge hX
      calc
        _ < plusSkew *
            ((1924 / 10000 : ℝ) * (1687 / 100000) -
              (19581 / 1000000) * (56173 / 100000)) :=
          mul_lt_mul_of_neg_right
            (by simpa only [plusSkew, e00p, e22p] using hXU) (by norm_num)
        _ < _ := mul_lt_mul_of_pos_left hCoeffXL hX0
  have hATd :
      (547765 / 1000000 : ℝ) * (1925 / 100000) * (1687 / 100000) <
        plusStrong * plusCrossDifference * uDifference := by
    calc
      _ < plusStrong * (1925 / 100000) * (1687 / 100000) :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right
            (by simpa only [plusStrong, e00p, e02p, e22p] using hAL)
            (by norm_num)) (by norm_num)
      _ < plusStrong * plusCrossDifference * (1687 / 100000) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hTL hA0) (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [uDifference, u0, u2] using hudL)
        (mul_pos hA0 hT0)
  have hX2z : -(1919 / 1000000 : ℝ) ^ 2 * (144 / 1000) <
      -(plusSkew ^ 2 * u4) := by
    have hprod : plusSkew ^ 2 * u4 <
        (1919 / 1000000 : ℝ) ^ 2 * (144 / 1000) := by
      calc
        _ < (1919 / 1000000 : ℝ) ^ 2 * u4 :=
          mul_lt_mul_of_pos_right plusSkew_sq_lt_upper hu40
        _ < _ := mul_lt_mul_of_pos_left (by simpa only [u4] using hu4U)
          (sq_pos_of_pos (by norm_num))
    linarith
  rw [p4ResidualOne_eq_alignedResidualForm]
  unfold alignedResidualForm residualOneLowerEnvelope
  norm_num at hRterm hXterm hATd hX2z ⊢
  nlinarith

private theorem p4ResidualThree_envelopes :
    -residualThreeAbsEnvelope plusWeak < p4ResidualThree ∧
      p4ResidualThree < residualThreeUpperEnvelope plusWeak ∧
      p4ResidualThree < 0 := by
  rcases factorTwoIntrinsicP4_positive_aligned_bounds with
    ⟨hAL, hAU, hXL, hXU, _hSL0, hSU, hRL, _hRU, _hTL0, hTU⟩
  change (547765 / 1000000 : ℝ) < plusStrong at hAL
  change plusStrong < (549941 / 1000000 : ℝ) at hAU
  change (-141 / 1000000 : ℝ) < plusSkew at hXL
  change plusSkew < (1919 / 1000000 : ℝ) at hXU
  change plusCrossSum < (193081 / 1000000 : ℝ) at hSU
  change (6065 / 1000000 : ℝ) < plusWeak at hRL
  change plusCrossDifference < (19581 / 1000000 : ℝ) at hTU
  have hsharp := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds
  have hSL : (1924 / 10000 : ℝ) < plusCrossSum := by
    simpa [plusCrossSum, e04p, e24p,
      factorTwoIntrinsicP4PlusCrossSum] using hsharp.1
  have hTL : (1925 / 100000 : ℝ) < plusCrossDifference := by
    simpa [plusCrossDifference, e04p, e24p,
      factorTwoIntrinsicP4PlusCrossDifference] using hsharp.2
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨_ue1, _ue2, _ud1, _ud2, hvsL, hvsU, hvdL, hvdU⟩
  rcases factorTwoIntrinsicFourP45Cross43_bounds with ⟨hv4L, hv4U⟩
  have hA0 : 0 < plusStrong := by
    simpa only [plusStrong, e00p, e02p, e22p] using
      lt_trans (by norm_num : (0 : ℝ) < 547765 / 1000000) hAL
  have hR0 : 0 < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using
      lt_trans (by norm_num : (0 : ℝ) < 6065 / 1000000) hRL
  have hS0 : 0 < plusCrossSum := lt_trans (by norm_num) hSL
  have hT0 : 0 < plusCrossDifference := lt_trans (by norm_num) hTL
  have hvs0 : 0 < vSum := by
    simpa only [vSum, v0, v2] using lt_trans (by norm_num) hvsL
  have hvd0 : 0 < vDifference := by
    simpa only [vDifference, v0, v2] using lt_trans (by norm_num) hvdL
  have hv4neg : v4 < 0 := by
    simpa only [v4] using lt_trans hv4U (by norm_num)
  have hAzL :
      (549941 / 1000000 : ℝ) * (-4 / 1000) < plusStrong * v4 := by
    calc
      _ < (549941 / 1000000 : ℝ) * v4 :=
        mul_lt_mul_of_pos_left (by simpa only [v4] using hv4L) (by norm_num)
      _ < plusStrong * v4 :=
        mul_lt_mul_of_neg_right
          (by simpa only [plusStrong, e00p, e02p, e22p] using hAU) hv4neg
  have hSsU : plusCrossSum * vSum <
      (193081 / 1000000 : ℝ) * (53836 / 100000) := by
    calc
      _ < (193081 / 1000000 : ℝ) * vSum :=
        mul_lt_mul_of_pos_right
          (by simpa only [plusCrossSum, e04p, e24p] using hSU) hvs0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vSum, v0, v2] using hvsU) (by norm_num)
  have hCoeffRL :
      (549941 / 1000000 : ℝ) * (-4 / 1000) -
          (193081 / 1000000) * (53836 / 100000) <
        plusStrong * v4 - plusCrossSum * vSum := by linarith
  have hRtermL :
      plusWeak * ((549941 / 1000000 : ℝ) * (-4 / 1000) -
          (193081 / 1000000) * (53836 / 100000)) <
        plusWeak * (plusStrong * v4 - plusCrossSum * vSum) :=
    mul_lt_mul_of_pos_left hCoeffRL hR0
  have hSdU : plusCrossSum * vDifference <
      (193081 / 1000000 : ℝ) * (279 / 5000) := by
    calc
      _ < (193081 / 1000000 : ℝ) * vDifference :=
        mul_lt_mul_of_pos_right
          (by simpa only [plusCrossSum, e04p, e24p] using hSU) hvd0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vDifference, v0, v2] using hvdU) (by norm_num)
  have hTsL : (1925 / 100000 : ℝ) * (53815 / 100000) <
      plusCrossDifference * vSum := by
    calc
      _ < plusCrossDifference * (53815 / 100000) :=
        mul_lt_mul_of_pos_right hTL (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vSum, v0, v2] using hvsL) hT0
  have hCoeffXU :
      plusCrossSum * vDifference - plusCrossDifference * vSum <
        (193081 / 1000000 : ℝ) * (279 / 5000) -
          (1925 / 100000) * (53815 / 100000) := by linarith
  have hCoeffXL : 0 <
      plusCrossSum * vDifference - plusCrossDifference * vSum := by
    have hSdL : (1924 / 10000 : ℝ) * (555 / 10000) <
        plusCrossSum * vDifference := by
      calc
        _ < plusCrossSum * (555 / 10000) :=
          mul_lt_mul_of_pos_right hSL (by norm_num)
        _ < _ := mul_lt_mul_of_pos_left
          (by simpa only [vDifference, v0, v2] using hvdL) hS0
    have hTsU : plusCrossDifference * vSum <
        (19581 / 1000000 : ℝ) * (53836 / 100000) := by
      calc
        _ < (19581 / 1000000 : ℝ) * vSum :=
          mul_lt_mul_of_pos_right
            (by simpa only [plusCrossDifference, e04p, e24p] using hTU) hvs0
        _ < _ := mul_lt_mul_of_pos_left
          (by simpa only [vSum, v0, v2] using hvsU) (by norm_num)
    norm_num at hSdL hTsU ⊢
    linarith
  have hXtermL :
      (-141 / 1000000 : ℝ) *
          ((193081 / 1000000) * (279 / 5000) -
            (1925 / 100000) * (53815 / 100000)) <
        plusSkew *
          (plusCrossSum * vDifference - plusCrossDifference * vSum) := by
    by_cases hX : 0 ≤ plusSkew
    · have hprod : 0 ≤ plusSkew *
          (plusCrossSum * vDifference - plusCrossDifference * vSum) :=
        mul_nonneg hX hCoeffXL.le
      norm_num at hprod ⊢
      linarith
    · have hXneg : plusSkew < 0 := lt_of_not_ge hX
      calc
        _ < plusSkew *
            ((193081 / 1000000 : ℝ) * (279 / 5000) -
              (1925 / 100000) * (53815 / 100000)) :=
          mul_lt_mul_of_pos_right
            (by simpa only [plusSkew, e00p, e22p] using hXL) (by norm_num)
        _ < _ := mul_lt_mul_of_neg_left hCoeffXU hXneg
  have hATdL :
      (547765 / 1000000 : ℝ) * (1925 / 100000) * (555 / 10000) <
        plusStrong * plusCrossDifference * vDifference := by
    calc
      _ < plusStrong * (1925 / 100000) * (555 / 10000) :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right
            (by simpa only [plusStrong, e00p, e02p, e22p] using hAL)
            (by norm_num)) (by norm_num)
      _ < plusStrong * plusCrossDifference * (555 / 10000) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hTL hA0) (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vDifference, v0, v2] using hvdL)
        (mul_pos hA0 hT0)
  have hlastNonneg : 0 ≤ -(plusSkew ^ 2 * v4) := by
    have hmul : plusSkew ^ 2 * v4 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg plusSkew) hv4neg.le
    linarith
  have hLowerModel :
      -residualThreeAbsEnvelope plusWeak < p4ResidualThree := by
    rw [p4ResidualThree_eq_alignedResidualForm]
    unfold alignedResidualForm residualThreeAbsEnvelope
    norm_num at hRtermL hXtermL hATdL ⊢
    nlinarith
  have hAzU : plusStrong * v4 <
      (547765 / 1000000 : ℝ) * (-2 / 1000) := by
    calc
      _ < (547765 / 1000000 : ℝ) * v4 :=
        mul_lt_mul_of_neg_right
          (by simpa only [plusStrong, e00p, e02p, e22p] using hAL) hv4neg
      _ < _ := mul_lt_mul_of_pos_left (by simpa only [v4] using hv4U) (by norm_num)
  have hSsL : (1924 / 10000 : ℝ) * (53815 / 100000) <
      plusCrossSum * vSum := by
    calc
      _ < plusCrossSum * (53815 / 100000) :=
        mul_lt_mul_of_pos_right hSL (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vSum, v0, v2] using hvsL) hS0
  have hCoeffRU : plusStrong * v4 - plusCrossSum * vSum <
      (547765 / 1000000 : ℝ) * (-2 / 1000) -
        (1924 / 10000) * (53815 / 100000) := by linarith
  have hRtermU : plusWeak * (plusStrong * v4 - plusCrossSum * vSum) <
      plusWeak * ((547765 / 1000000 : ℝ) * (-2 / 1000) -
        (1924 / 10000) * (53815 / 100000)) :=
    mul_lt_mul_of_pos_left hCoeffRU hR0
  have hXtermU : plusSkew *
        (plusCrossSum * vDifference - plusCrossDifference * vSum) <
      (1919 / 1000000 : ℝ) *
        ((193081 / 1000000) * (279 / 5000) -
          (1925 / 100000) * (53815 / 100000)) := by
    by_cases hX : plusSkew ≤ 0
    · have hprod : plusSkew *
          (plusCrossSum * vDifference - plusCrossDifference * vSum) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hX hCoeffXL.le
      norm_num at hprod ⊢
      linarith
    · have hX0 : 0 < plusSkew := lt_of_not_ge hX
      calc
        _ < (1919 / 1000000 : ℝ) *
            (plusCrossSum * vDifference - plusCrossDifference * vSum) :=
          mul_lt_mul_of_pos_right
            (by simpa only [plusSkew, e00p, e22p] using hXU) hCoeffXL
        _ < _ := mul_lt_mul_of_pos_left hCoeffXU (by norm_num)
  have hATdU : plusStrong * plusCrossDifference * vDifference <
      (549941 / 1000000 : ℝ) * (19581 / 1000000) * (279 / 5000) := by
    calc
      _ < (549941 / 1000000 : ℝ) * plusCrossDifference * vDifference :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right
            (by simpa only [plusStrong, e00p, e02p, e22p] using hAU) hT0) hvd0
      _ < (549941 / 1000000 : ℝ) * (19581 / 1000000) * vDifference :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left
            (by simpa only [plusCrossDifference, e04p, e24p] using hTU)
            (by norm_num)) hvd0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vDifference, v0, v2] using hvdU)
        (mul_pos (by norm_num) (by norm_num))
  have hlastU : -(plusSkew ^ 2 * v4) <
      (1919 / 1000000 : ℝ) ^ 2 * (4 / 1000) := by
    have hvabs : -v4 < (4 / 1000 : ℝ) := by
      change (-4 / 1000 : ℝ) < v4 at hv4L
      linarith
    have hprod : plusSkew ^ 2 * (-v4) <
        (1919 / 1000000 : ℝ) ^ 2 * (4 / 1000) := by
      calc
        _ < (1919 / 1000000 : ℝ) ^ 2 * (-v4) :=
          mul_lt_mul_of_pos_right plusSkew_sq_lt_upper (by linarith)
        _ < _ := mul_lt_mul_of_pos_left hvabs (sq_pos_of_pos (by norm_num))
    nlinarith
  have hUpperModel :
      p4ResidualThree < residualThreeUpperEnvelope plusWeak := by
    rw [p4ResidualThree_eq_alignedResidualForm]
    unfold alignedResidualForm residualThreeUpperEnvelope
    norm_num at hRtermU hXtermU hATdU hlastU hRL ⊢
    nlinarith
  have hEnvelopeNeg : residualThreeUpperEnvelope plusWeak < 0 := by
    unfold residualThreeUpperEnvelope
    have hR := by simpa only [plusWeak, e00p, e02p, e22p] using hRL
    norm_num at hR ⊢
    linarith
  exact ⟨hLowerModel, hUpperModel, hUpperModel.trans hEnvelopeNeg⟩

private def transformedResidualSum (C : ℝ) : ℝ :=
  C * uSum - (1912 / 10000) * vSum

private def transformedResidualDifference (C : ℝ) : ℝ :=
  C * uDifference - (1912 / 10000) * vDifference

private def transformedResidualFourth (C : ℝ) : ℝ :=
  C * u4 - (1912 / 10000) * v4

private theorem fixed_residual_combination_eq (C : ℝ) :
    C * p4ResidualOne - (1912 / 10000) * p4ResidualThree =
      alignedResidualForm
        (transformedResidualSum C)
        (transformedResidualDifference C)
        (transformedResidualFourth C) := by
  rw [p4ResidualOne_eq_alignedResidualForm,
    p4ResidualThree_eq_alignedResidualForm]
  unfold transformedResidualSum transformedResidualDifference
    transformedResidualFourth alignedResidualForm
  ring

private theorem alignedResidualForm_lt_boxUpper
    (s d z sL sU dL dU zU : ℝ)
    (hsL0 : 0 < sL) (hsL : sL < s) (hsU : s < sU)
    (hdL : dL < d) (hdU : d < dU) (hdU0 : dU < 0)
    (hz0 : 0 < z) (hzU : z < zU) :
    alignedResidualForm s d z <
      (plusWeak *
          ((549941 / 1000000 : ℝ) * zU - (1924 / 10000) * sL) +
        (-141 / 1000000) *
          ((193081 / 1000000) * dL - (19581 / 1000000) * sU) +
        (547765 / 1000000) * (1925 / 100000) * dU) / 4 := by
  rcases factorTwoIntrinsicP4_positive_aligned_bounds with
    ⟨hAL, hAU, hXL, _hXU, _hSL0, hSU, hRL, _hRU, _hTL0, hTU⟩
  have hsharp := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds
  have hSL : (1924 / 10000 : ℝ) < plusCrossSum := by
    simpa [plusCrossSum, e04p, e24p,
      factorTwoIntrinsicP4PlusCrossSum] using hsharp.1
  have hTL : (1925 / 100000 : ℝ) < plusCrossDifference := by
    simpa [plusCrossDifference, e04p, e24p,
      factorTwoIntrinsicP4PlusCrossDifference] using hsharp.2
  have hA0 : 0 < plusStrong := by
    simpa only [plusStrong, e00p, e02p, e22p] using
      lt_trans (by norm_num : (0 : ℝ) < 547765 / 1000000) hAL
  have hR0 : 0 < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using
      lt_trans (by norm_num : (0 : ℝ) < 6065 / 1000000) hRL
  have hS0 : 0 < plusCrossSum := lt_trans (by norm_num) hSL
  have hT0 : 0 < plusCrossDifference := lt_trans (by norm_num) hTL
  have hs0 : 0 < s := lt_trans hsL0 hsL
  have hdneg : d < 0 := lt_trans hdU hdU0
  have hzU0 : 0 < zU := lt_trans hz0 hzU
  have hAzU : plusStrong * z <
      (549941 / 1000000 : ℝ) * zU := by
    calc
      _ < (549941 / 1000000 : ℝ) * z :=
        mul_lt_mul_of_pos_right
          (by simpa only [plusStrong, e00p, e02p, e22p] using hAU) hz0
      _ < _ := mul_lt_mul_of_pos_left hzU (by norm_num)
  have hSsL : (1924 / 10000 : ℝ) * sL < plusCrossSum * s := by
    calc
      _ < plusCrossSum * sL := mul_lt_mul_of_pos_right hSL hsL0
      _ < _ := mul_lt_mul_of_pos_left hsL hS0
  have hCoeffRU : plusStrong * z - plusCrossSum * s <
      (549941 / 1000000 : ℝ) * zU - (1924 / 10000) * sL := by
    linarith
  have hRterm : plusWeak * (plusStrong * z - plusCrossSum * s) <
      plusWeak * ((549941 / 1000000 : ℝ) * zU -
        (1924 / 10000) * sL) := mul_lt_mul_of_pos_left hCoeffRU hR0
  have hSdL : (193081 / 1000000 : ℝ) * dL <
      plusCrossSum * d := by
    calc
      _ < (193081 / 1000000 : ℝ) * d :=
        mul_lt_mul_of_pos_left hdL (by norm_num)
      _ < plusCrossSum * d :=
        mul_lt_mul_of_neg_right
          (by simpa only [plusCrossSum, e04p, e24p] using hSU) hdneg
  have hTsU : plusCrossDifference * s <
      (19581 / 1000000 : ℝ) * sU := by
    calc
      _ < (19581 / 1000000 : ℝ) * s :=
        mul_lt_mul_of_pos_right
          (by simpa only [plusCrossDifference, e04p, e24p] using hTU) hs0
      _ < _ := mul_lt_mul_of_pos_left hsU (by norm_num)
  have hCoeffXL :
      (193081 / 1000000 : ℝ) * dL - (19581 / 1000000) * sU <
        plusCrossSum * d - plusCrossDifference * s := by linarith
  have hCoeffXneg : plusCrossSum * d - plusCrossDifference * s < 0 := by
    have hfirst : plusCrossSum * d < 0 := mul_neg_of_pos_of_neg hS0 hdneg
    have hsecond : 0 < plusCrossDifference * s := mul_pos hT0 hs0
    linarith
  have hXterm : plusSkew * (plusCrossSum * d - plusCrossDifference * s) <
      (-141 / 1000000 : ℝ) *
        ((193081 / 1000000) * dL - (19581 / 1000000) * sU) := by
    by_cases hX : 0 ≤ plusSkew
    · have hprod : plusSkew *
          (plusCrossSum * d - plusCrossDifference * s) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hX hCoeffXneg.le
      have hcorner : 0 < (-141 / 1000000 : ℝ) *
          ((193081 / 1000000) * dL - (19581 / 1000000) * sU) := by
        have hcornerNeg : (193081 / 1000000 : ℝ) * dL -
            (19581 / 1000000) * sU < 0 := by
          have hdLneg : dL < 0 := lt_trans hdL hdneg
          have hsU0 : 0 < sU := lt_trans hs0 hsU
          have hleft : (193081 / 1000000 : ℝ) * dL < 0 :=
            mul_neg_of_pos_of_neg (by norm_num) hdLneg
          have hright : 0 < (19581 / 1000000 : ℝ) * sU :=
            mul_pos (by norm_num) hsU0
          linarith
        exact mul_pos_of_neg_of_neg (by norm_num) hcornerNeg
      linarith
    · have hXneg : plusSkew < 0 := lt_of_not_ge hX
      have hcornerNeg : (193081 / 1000000 : ℝ) * dL -
          (19581 / 1000000) * sU < 0 := by
        have hdLneg : dL < 0 := lt_trans hdL hdneg
        have hsU0 : 0 < sU := lt_trans hs0 hsU
        have hleft : (193081 / 1000000 : ℝ) * dL < 0 :=
          mul_neg_of_pos_of_neg (by norm_num) hdLneg
        have hright : 0 < (19581 / 1000000 : ℝ) * sU :=
          mul_pos (by norm_num) hsU0
        linarith
      calc
        _ < plusSkew *
            ((193081 / 1000000 : ℝ) * dL -
              (19581 / 1000000) * sU) :=
          mul_lt_mul_of_neg_left hCoeffXL hXneg
        _ < _ := mul_lt_mul_of_neg_right
          (by simpa only [plusSkew, e00p, e22p] using hXL) hcornerNeg
  have hATLower :
      (547765 / 1000000 : ℝ) * (1925 / 100000) <
        plusStrong * plusCrossDifference := by
    calc
      _ < plusStrong * (1925 / 100000) :=
        mul_lt_mul_of_pos_right
          (by simpa only [plusStrong, e00p, e02p, e22p] using hAL) (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hTL hA0
  have hATd : plusStrong * plusCrossDifference * d <
      (547765 / 1000000 : ℝ) * (1925 / 100000) * dU := by
    calc
      _ < (547765 / 1000000 : ℝ) * (1925 / 100000) * d :=
        mul_lt_mul_of_neg_right hATLower hdneg
      _ < _ := mul_lt_mul_of_pos_left hdU
        (mul_pos (by norm_num) (by norm_num))
  have hlast : -(plusSkew ^ 2 * z) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg (sq_nonneg plusSkew) hz0.le)
  unfold alignedResidualForm
  nlinarith

private theorem transformedResidual_216_bounds :
    (18388448 / 1000000000 : ℝ) < transformedResidualSum (216 / 1000) ∧
      transformedResidualSum (216 / 1000) < 184394 / 10000000 ∧
      (-702504 / 100000000 : ℝ) <
        transformedResidualDifference (216 / 1000) ∧
      transformedResidualDifference (216 / 1000) < -695688 / 100000000 ∧
      0 < transformedResidualFourth (216 / 1000) ∧
      transformedResidualFourth (216 / 1000) < 318688 / 10000000 := by
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨husL, husU, hudL, hudU, hvsL, hvsU, hvdL, hvdU⟩
  rcases factorTwoIntrinsicFourP45Cross41_bounds with ⟨hu4L, hu4U⟩
  rcases factorTwoIntrinsicFourP45Cross43_bounds with ⟨hv4L, hv4U⟩
  unfold transformedResidualSum transformedResidualDifference
    transformedResidualFourth uSum uDifference vSum vDifference
    u0 u2 u4 v0 v2 v4
  constructor
  · norm_num at husL hvsU ⊢
    linarith
  constructor
  · norm_num at husU hvsL ⊢
    linarith
  constructor
  · norm_num at hudL hvdU ⊢
    linarith
  constructor
  · norm_num at hudU hvdL ⊢
    linarith
  constructor
  · norm_num at hu4L hv4U ⊢
    linarith
  · norm_num at hu4U hv4L ⊢
    linarith

private theorem transformedResidual_2115_bounds :
    (15860888 / 1000000000 : ℝ) < transformedResidualSum (2115 / 10000) ∧
      transformedResidualSum (2115 / 10000) < 15911615 / 1000000000 ∧
      (-7100955 / 1000000000 : ℝ) <
        transformedResidualDifference (2115 / 10000) ∧
      transformedResidualDifference (2115 / 10000) < -703302 / 100000000 ∧
      0 < transformedResidualFourth (2115 / 10000) ∧
      transformedResidualFourth (2115 / 10000) < 312208 / 10000000 := by
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨husL, husU, hudL, hudU, hvsL, hvsU, hvdL, hvdU⟩
  rcases factorTwoIntrinsicFourP45Cross41_bounds with ⟨hu4L, hu4U⟩
  rcases factorTwoIntrinsicFourP45Cross43_bounds with ⟨hv4L, hv4U⟩
  unfold transformedResidualSum transformedResidualDifference
    transformedResidualFourth uSum uDifference vSum vDifference
    u0 u2 u4 v0 v2 v4
  constructor
  · norm_num at husL hvsU ⊢
    linarith
  constructor
  · norm_num at husU hvsL ⊢
    linarith
  constructor
  · norm_num at hudL hvdU ⊢
    linarith
  constructor
  · norm_num at hudU hvdL ⊢
    linarith
  constructor
  · norm_num at hu4L hv4U ⊢
    linarith
  · norm_num at hu4U hv4L ⊢
    linarith

private theorem fixedResidual_216_lt_upperEnvelope :
    (216 / 1000 : ℝ) * p4ResidualOne -
        (1912 / 10000) * p4ResidualThree <
      residualUpperEnvelope plusWeak := by
  rw [fixed_residual_combination_eq]
  rcases transformedResidual_216_bounds with
    ⟨hsL, hsU, hdL, hdU, hz0, hzU⟩
  have hbox := alignedResidualForm_lt_boxUpper
    (transformedResidualSum (216 / 1000))
    (transformedResidualDifference (216 / 1000))
    (transformedResidualFourth (216 / 1000))
    (18388448 / 1000000000) (184394 / 10000000)
    (-702504 / 100000000) (-695688 / 100000000)
    (318688 / 10000000)
    (by norm_num) hsL hsU hdL hdU (by norm_num) hz0 hzU
  have hR : (6065 / 1000000 : ℝ) < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using
      factorTwoIntrinsicP4_positive_aligned_bounds.2.2.2.2.2.2.1
  calc
    _ < (plusWeak *
          ((549941 / 1000000 : ℝ) * (318688 / 10000000) -
            (1924 / 10000) * (18388448 / 1000000000)) +
        (-141 / 1000000) *
          ((193081 / 1000000) * (-702504 / 100000000) -
            (19581 / 1000000) * (184394 / 10000000)) +
        (547765 / 1000000) * (1925 / 100000) *
          (-695688 / 100000000)) / 4 := hbox
    _ < residualUpperEnvelope plusWeak := by
      unfold residualUpperEnvelope
      norm_num at hR ⊢
      linarith

private theorem fixedResidual_2115_lt_upperEnvelope :
    (2115 / 10000 : ℝ) * p4ResidualOne -
        (1912 / 10000) * p4ResidualThree <
      residualUpperEnvelope plusWeak := by
  rw [fixed_residual_combination_eq]
  rcases transformedResidual_2115_bounds with
    ⟨hsL, hsU, hdL, hdU, hz0, hzU⟩
  have hbox := alignedResidualForm_lt_boxUpper
    (transformedResidualSum (2115 / 10000))
    (transformedResidualDifference (2115 / 10000))
    (transformedResidualFourth (2115 / 10000))
    (15860888 / 1000000000) (15911615 / 1000000000)
    (-7100955 / 1000000000) (-703302 / 100000000)
    (312208 / 10000000)
    (by norm_num) hsL hsU hdL hdU (by norm_num) hz0 hzU
  have hR : (6065 / 1000000 : ℝ) < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using
      factorTwoIntrinsicP4_positive_aligned_bounds.2.2.2.2.2.2.1
  calc
    _ < (plusWeak *
          ((549941 / 1000000 : ℝ) * (312208 / 10000000) -
            (1924 / 10000) * (15860888 / 1000000000)) +
        (-141 / 1000000) *
          ((193081 / 1000000) * (-7100955 / 1000000000) -
            (19581 / 1000000) * (15911615 / 1000000000)) +
        (547765 / 1000000) * (1925 / 100000) *
          (-703302 / 100000000)) / 4 := hbox
    _ < residualUpperEnvelope plusWeak := by
      unfold residualUpperEnvelope
      norm_num at hR ⊢
      linarith

private theorem correlatedResidual_bounds :
    0 < o33p * p4ResidualOne - o13p * p4ResidualThree ∧
      o33p * p4ResidualOne - o13p * p4ResidualThree <
        residualUpperEnvelope plusWeak := by
  rcases factorTwoIntrinsicOddPhaseLow_plus_entry_bounds with
    ⟨_haL, _haU, hbL, hbU, hcL, hcU⟩
  have hb0 : 0 < o13p := by
    simpa only [o13p] using lt_trans (by norm_num : (0 : ℝ) < 189 / 1000) hbL
  have hc0 : 0 < o33p := by
    simpa only [o33p] using lt_trans (by norm_num : (0 : ℝ) < 2115 / 10000) hcL
  have hbLower : (189 / 1000 : ℝ) < o13p := by simpa only [o13p] using hbL
  have hbUpper : o13p < (1912 / 10000 : ℝ) := by simpa only [o13p] using hbU
  have hcLower : (2115 / 10000 : ℝ) < o33p := by simpa only [o33p] using hcL
  have hcUpper : o33p < (216 / 1000 : ℝ) := by simpa only [o33p] using hcU
  rcases p4ResidualThree_envelopes with ⟨_hthreeL, hthreeU, hthreeNeg⟩
  have hEnvelope0 : 0 < residualUpperEnvelope plusWeak := by
    have hR : (6065 / 1000000 : ℝ) < plusWeak := by
      simpa only [plusWeak, e00p, e02p, e22p] using
        factorTwoIntrinsicP4_positive_aligned_bounds.2.2.2.2.2.2.1
    unfold residualUpperEnvelope
    norm_num at hR ⊢
    linarith
  constructor
  · by_cases hOne : 0 ≤ p4ResidualOne
    · have hfirst : 0 ≤ o33p * p4ResidualOne := mul_nonneg hc0.le hOne
      have hsecond : 0 < -(o13p * p4ResidualThree) := by
        exact neg_pos.mpr (mul_neg_of_pos_of_neg hb0 hthreeNeg)
      linarith
    · have hOneNeg : p4ResidualOne < 0 := lt_of_not_ge hOne
      have hOneModel := p4ResidualOne_gt_lowerEnvelope
      have hcTerm : (216 / 1000 : ℝ) * p4ResidualOne <
          o33p * p4ResidualOne := mul_lt_mul_of_neg_right hcUpper hOneNeg
      have hOneTerm : (216 / 1000 : ℝ) *
          residualOneLowerEnvelope plusWeak <
            (216 / 1000) * p4ResidualOne :=
        mul_lt_mul_of_pos_left hOneModel (by norm_num)
      have hbTerm : (189 / 1000 : ℝ) * (-p4ResidualThree) <
          o13p * (-p4ResidualThree) :=
        mul_lt_mul_of_pos_right hbLower (by linarith)
      have hThreeTerm : (189 / 1000 : ℝ) *
          (-residualThreeUpperEnvelope plusWeak) <
            (189 / 1000) * (-p4ResidualThree) := by
        apply mul_lt_mul_of_pos_left _ (by norm_num)
        linarith
      have hmodel : 0 <
          (216 / 1000 : ℝ) * residualOneLowerEnvelope plusWeak +
            (189 / 1000) * (-residualThreeUpperEnvelope plusWeak) := by
        have hR : (6065 / 1000000 : ℝ) < plusWeak := by
          simpa only [plusWeak, e00p, e02p, e22p] using
            factorTwoIntrinsicP4_positive_aligned_bounds.2.2.2.2.2.2.1
        unfold residualOneLowerEnvelope residualThreeUpperEnvelope
        norm_num at hR ⊢
        linarith
      nlinarith
  · by_cases hOne : 0 ≤ p4ResidualOne
    · have hcTerm : o33p * p4ResidualOne ≤
          (216 / 1000 : ℝ) * p4ResidualOne :=
        mul_le_mul_of_nonneg_right hcUpper.le hOne
      have hbTerm : -(o13p * p4ResidualThree) <
          -((1912 / 10000 : ℝ) * p4ResidualThree) := by
        have := mul_lt_mul_of_neg_right hbUpper hthreeNeg
        linarith
      nlinarith [fixedResidual_216_lt_upperEnvelope]
    · have hOneNeg : p4ResidualOne < 0 := lt_of_not_ge hOne
      have hcTerm : o33p * p4ResidualOne <
          (2115 / 10000 : ℝ) * p4ResidualOne :=
        mul_lt_mul_of_neg_right hcLower hOneNeg
      have hbTerm : -(o13p * p4ResidualThree) <
          -((1912 / 10000 : ℝ) * p4ResidualThree) := by
        have := mul_lt_mul_of_neg_right hbUpper hthreeNeg
        linarith
      nlinarith [fixedResidual_2115_lt_upperEnvelope]

private theorem reserveComparisonQuadratic_pos :
    0 < reserveComparisonQuadratic plusWeak := by
  have hR : (6065 / 1000000 : ℝ) < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using
      factorTwoIntrinsicP4_positive_aligned_bounds.2.2.2.2.2.2.1
  unfold reserveComparisonQuadratic
  norm_num at hR ⊢
  nlinarith [sq_nonneg plusWeak]

private theorem residualUpperEnvelope_pos :
    0 < residualUpperEnvelope plusWeak := by
  have hR : (6065 / 1000000 : ℝ) < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using
      factorTwoIntrinsicP4_positive_aligned_bounds.2.2.2.2.2.2.1
  unfold residualUpperEnvelope
  norm_num at hR ⊢
  linarith

private theorem residualThreeAbsEnvelope_pos :
    0 < residualThreeAbsEnvelope plusWeak := by
  have hR : (6065 / 1000000 : ℝ) < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using
      factorTwoIntrinsicP4_positive_aligned_bounds.2.2.2.2.2.2.1
  unfold residualThreeAbsEnvelope
  norm_num at hR ⊢
  linarith

private theorem envelope_square_comparison :
    residualUpperEnvelope plusWeak ^ 2 +
        (73 / 10000 : ℝ) * residualThreeAbsEnvelope plusWeak ^ 2 <
      (2115 / 10000) * (1 / 250) *
        reserveComparisonQuadratic plusWeak := by
  have hp := factorTwoIntrinsicP4_positive_aligned_bounds
  have hRL : (6065 / 1000000 : ℝ) < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using hp.2.2.2.2.2.2.1
  have hRU : plusWeak < (8241 / 1000000 : ℝ) := by
    simpa only [plusWeak, e00p, e02p, e22p] using hp.2.2.2.2.2.2.2.1
  have hinterval : 0 ≤
      (plusWeak - 6065 / 1000000) * (8241 / 1000000 - plusWeak) :=
    mul_nonneg (sub_nonneg.mpr hRL.le) (sub_nonneg.mpr hRU.le)
  unfold residualUpperEnvelope residualThreeAbsEnvelope
    reserveComparisonQuadratic
  norm_num at hinterval ⊢
  nlinarith

private theorem oddDetPlus_lt_seventy_three_div_ten_thousand :
    oddDetPlus < (73 / 10000 : ℝ) := by
  rcases factorTwoIntrinsicOddPhaseLow_plus_entry_bounds with
    ⟨haL, haU, hbL, _hbU, _hcL, hcU⟩
  have ha0 : 0 < o11p := by
    simpa only [o11p] using lt_trans (by norm_num : (0 : ℝ) < 1918 / 10000) haL
  have hb0 : 0 < o13p := by
    simpa only [o13p] using lt_trans (by norm_num : (0 : ℝ) < 189 / 1000) hbL
  have hc0 : 0 < o33p := by
    simpa only [o33p] using lt_trans (by norm_num : (0 : ℝ) < 2115 / 10000)
      factorTwoIntrinsicOddPhaseLow_plus_entry_bounds.2.2.2.2.1
  have hprod : o11p * o33p < (199 / 1000 : ℝ) * (216 / 1000) := by
    calc
      o11p * o33p < (199 / 1000 : ℝ) * o33p :=
        mul_lt_mul_of_pos_right (by simpa only [o11p] using haU) hc0
      _ < (199 / 1000 : ℝ) * (216 / 1000) :=
        mul_lt_mul_of_pos_left (by simpa only [o33p] using hcU) (by norm_num)
  have hsum : 0 < o13p + (189 / 1000 : ℝ) := by
    positivity
  have hmul := mul_pos
    (by simpa only [o13p] using sub_pos.mpr hbL) hsum
  have hmul' : 0 < (o13p - 189 / 1000) * (o13p + 189 / 1000) := by
    simpa only [o13p] using hmul
  have hsq : (189 / 1000 : ℝ) ^ 2 < o13p ^ 2 := by
    nlinarith [hmul']
  unfold oddDetPlus
  norm_num at hprod hsq ⊢
  nlinarith

private theorem reserve_times_oddDet_gt_residualOddAdjugate :
    p4ResidualOddAdjugate < evenMinusSchurReserve * oddDetPlus := by
  have hdetL : (1 / 250 : ℝ) < oddDetPlus := by
    simpa only [oddDetPlus, o11p, o13p, o33p] using
      factorTwoIntrinsicOddPhaseLow_plus_minor_gt_one_div_two_fifty
  have hdet0 : 0 < oddDetPlus := lt_trans (by norm_num) hdetL
  have hdetU := oddDetPlus_lt_seventy_three_div_ten_thousand
  have hcL : (2115 / 10000 : ℝ) < o33p := by
    simpa only [o33p] using
      factorTwoIntrinsicOddPhaseLow_plus_entry_bounds.2.2.2.2.1
  have hc0 : 0 < o33p := lt_trans (by norm_num) hcL
  rcases correlatedResidual_bounds with ⟨hw0, hwU⟩
  rcases p4ResidualThree_envelopes with ⟨hthreeL, _hthreeU, hthreeNeg⟩
  have hWSq :
      (o33p * p4ResidualOne - o13p * p4ResidualThree) ^ 2 <
        residualUpperEnvelope plusWeak ^ 2 := by
    have hmul := mul_pos (sub_pos.mpr hwU)
      (add_pos hw0 residualUpperEnvelope_pos)
    nlinarith
  have hThreeAbs : -p4ResidualThree <
      residualThreeAbsEnvelope plusWeak := by linarith
  have hThreeSq : p4ResidualThree ^ 2 <
      residualThreeAbsEnvelope plusWeak ^ 2 := by
    have hmul := mul_pos (sub_pos.mpr hThreeAbs)
      (add_pos (by linarith : 0 < -p4ResidualThree)
        residualThreeAbsEnvelope_pos)
    nlinarith
  have hdetThree : oddDetPlus * p4ResidualThree ^ 2 <
      (73 / 10000 : ℝ) * residualThreeAbsEnvelope plusWeak ^ 2 := by
    calc
      _ < (73 / 10000 : ℝ) * p4ResidualThree ^ 2 :=
        mul_lt_mul_of_pos_right hdetU (sq_pos_of_neg hthreeNeg)
      _ < _ := mul_lt_mul_of_pos_left hThreeSq (by norm_num)
  have hAdjUpper : o33p * p4ResidualOddAdjugate <
      residualUpperEnvelope plusWeak ^ 2 +
        (73 / 10000 : ℝ) * residualThreeAbsEnvelope plusWeak ^ 2 := by
    rw [residualOddAdjugate_completion]
    linarith
  have hQReserve : reserveComparisonQuadratic plusWeak <
      evenMinusSchurReserve := evenMinusSchurReserve_gt_comparison
  have hReserve0 : 0 < evenMinusSchurReserve :=
    reserveComparisonQuadratic_pos.trans hQReserve
  have hproductLower :
      (2115 / 10000 : ℝ) * (1 / 250) *
          reserveComparisonQuadratic plusWeak <
        o33p * (evenMinusSchurReserve * oddDetPlus) := by
    calc
      _ < o33p * (1 / 250) * reserveComparisonQuadratic plusWeak :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hcL (by norm_num))
          reserveComparisonQuadratic_pos
      _ < o33p * oddDetPlus * reserveComparisonQuadratic plusWeak :=
        mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hdetL hc0)
          reserveComparisonQuadratic_pos
      _ < o33p * oddDetPlus * evenMinusSchurReserve :=
        mul_lt_mul_of_pos_left hQReserve (mul_pos hc0 hdet0)
      _ = o33p * (evenMinusSchurReserve * oddDetPlus) := by ring
  have hscaled : o33p * p4ResidualOddAdjugate <
      o33p * (evenMinusSchurReserve * oddDetPlus) :=
    hAdjUpper.trans (envelope_square_comparison.trans hproductLower)
  nlinarith

private theorem lowDetPlus_pos : 0 < lowDetPlus := by
  have hp := factorTwoIntrinsicP4_positive_aligned_bounds
  have hA : (547765 / 1000000 : ℝ) < plusStrong := by
    simpa only [plusStrong, e00p, e02p, e22p] using hp.1
  have hR : (6065 / 1000000 : ℝ) < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using hp.2.2.2.2.2.2.1
  have hXsq := plusSkew_sq_lt_upper
  rw [lowDetPlus_eq_aligned]
  norm_num at hA hR hXsq ⊢
  nlinarith

private theorem evenDetPlus_pos : 0 < evenDetPlus := by
  have h := factorTwoIntrinsicSixP4SchurLeading_plus_pos
  rw [factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant] at h
  simpa only [evenDetPlus, factorTwoIntrinsicP024Determinant,
    e00p, e02p, e04p, e22p, e24p, e44p,
    factorTwoIntrinsicSixP4Diagonal] using h

private theorem pivotCoeff_zero_eq_evenDetPlus :
    pivotCoeff 0 = evenDetPlus := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial evenDetPlus e00p e02p e04p e22p e24p e44p
    symmetricDeterminant
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

private theorem pivotCoeff_one_eq_evenMixedOne :
    pivotCoeff 1 = evenMixedOne := by
  simpa only [evenMixedOne, e00p, e02p, e04p, e22p, e24p, e44p,
    e00m, e02m, e04m, e22m, e24m, e44m] using
      pivotCoeff_one_eq_exact_mixed

private theorem rawFiveOddMinorCoeff_zero_eq_oddDetPlus :
    rawFiveOddMinorCoeff 0 = oddDetPlus := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
    coefficientOdd11Polynomial coefficientOdd13Polynomial
    coefficientOdd33Polynomial endpointAffinePolynomial
    oddDetPlus o11p o13p o33p
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

private theorem rawFiveCouplingCoeff_zero_eq_fullCoupling :
    rawFiveCouplingCoeff 0 = fullCoupling := by
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
    fullCoupling fullAdjugatePair
    e00p e02p e04p e22p e24p e44p
    o11p o13p o33p u0 u2 u4 v0 v2 v4
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    eval_ofNat]
  ring

private theorem coefficient_one_eq_endpoint_trace :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1 =
      evenDetPlus * oddMixedOne + evenMixedOne * oddDetPlus - fullCoupling := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rw [pivotCoeff_zero_eq_evenDetPlus, pivotCoeff_one_eq_evenMixedOne,
    rawFiveOddMinorCoeff_zero_eq_oddDetPlus,
    rawFiveCouplingCoeff_zero_eq_fullCoupling,
    rawFiveOddMinorCoeff_one_eq]
  unfold oddMixedOne o11p o13p o33p o11m o13m o33m
  ring

private theorem lowDet_mul_fullAdjugatePair
    (x0 x2 x4 y0 y2 y4 : ℝ) :
    lowDetPlus * fullAdjugatePair x0 x2 x4 y0 y2 y4 =
      evenDetPlus * lowAdjugatePair x0 x2 y0 y2 +
        (lowDetPlus * x4 - p4Polar x0 x2) *
          (lowDetPlus * y4 - p4Polar y0 y2) := by
  unfold lowDetPlus fullAdjugatePair lowAdjugatePair evenDetPlus p4Polar
    symmetricDeterminant
  ring

private theorem lowDet_mul_fullCoupling :
    lowDetPlus * fullCoupling =
      evenDetPlus * lowCoupling + p4ResidualOddAdjugate := by
  unfold fullCoupling lowCoupling p4ResidualOddAdjugate
    p4ResidualOne p4ResidualThree fullAdjugatePair lowAdjugatePair
    lowDetPlus evenDetPlus p4Polar symmetricDeterminant
  ring

private theorem coefficient_one_schur_identity :
    lowDetPlus * factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1 =
      evenDetPlus * lowCoefficientOne +
        (lowDetPlus * evenMixedOne - evenDetPlus * lowMixedOne) * oddDetPlus -
        p4ResidualOddAdjugate := by
  rw [coefficient_one_eq_endpoint_trace]
  unfold lowCoefficientOne
  rw [mul_sub, mul_add, lowDet_mul_fullCoupling]
  ring

private theorem strongBoxForm_gt
    (A Am a b c am bm cm s t : ℝ)
    (hA : (547765 / 1000000 : ℝ) < A)
    (hAm : (2198709 / 1000000 : ℝ) < Am)
    (ha : (1918 / 10000 : ℝ) < a)
    (hbL : (189 / 1000 : ℝ) < b)
    (hbU : b < (1912 / 10000 : ℝ))
    (hc : (2115 / 10000 : ℝ) < c)
    (ham : (1578 / 10000 : ℝ) < am)
    (hbmL : (209 / 1000 : ℝ) < bm)
    (hbmU : bm < (2112 / 10000 : ℝ))
    (hcm : (4485 / 10000 : ℝ) < cm)
    (hsL : (56168 / 100000 : ℝ) < s)
    (hsU : s < (56173 / 100000 : ℝ))
    (htL : (53815 / 100000 : ℝ) < t)
    (htU : t < (53836 / 100000 : ℝ))
    (hP : 0 < a * c - b ^ 2)
    (hQ : 0 < a * cm + am * c - 2 * b * bm) :
    (23 / 1000 : ℝ) < strongBoxForm A Am a b c am bm cm s t := by
  have hca : 0 <
      (547765 / 1000000 : ℝ) * cm +
        (2198709 / 1000000 : ℝ) * c - t ^ 2 := by
    have hcm' : (4485 / 10000 : ℝ) < cm := hcm
    have hc' : (2115 / 10000 : ℝ) < c := hc
    have ht0 : 0 < t := lt_trans (by norm_num) htL
    have htsq : t ^ 2 < (53836 / 100000 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ htU ht0.le (by norm_num)
    have hcmprod := mul_lt_mul_of_pos_left hcm' (by norm_num :
      (0 : ℝ) < 547765 / 1000000)
    have hcprod := mul_lt_mul_of_pos_left hc' (by norm_num :
      (0 : ℝ) < 2198709 / 1000000)
    norm_num at hcmprod hcprod htsq ⊢
    nlinarith
  have hbCoefficient :
      -2 * (547765 / 1000000 : ℝ) * bm -
          (2198709 / 1000000 : ℝ) * (b + 1912 / 10000) +
          2 * s * t < 0 := by
    have hbmprod := mul_lt_mul_of_pos_left hbmL (by norm_num :
      (0 : ℝ) < 2 * (547765 / 1000000))
    have hbadd : (189 / 1000 + 1912 / 10000 : ℝ) <
        b + 1912 / 10000 := by linarith
    have hbprod := mul_lt_mul_of_pos_left hbadd (by norm_num :
      (0 : ℝ) < 2198709 / 1000000)
    have hs0 : 0 < s := lt_trans (by norm_num) hsL
    have ht0 : 0 < t := lt_trans (by norm_num) htL
    have hst : s * t <
        (56173 / 100000 : ℝ) * (53836 / 100000) := by
      calc
        s * t < (56173 / 100000 : ℝ) * t :=
          mul_lt_mul_of_pos_right hsU ht0
        _ < (56173 / 100000 : ℝ) * (53836 / 100000) :=
          mul_lt_mul_of_pos_left htU (by norm_num)
    norm_num at hbmprod hbprod hst ⊢
    nlinarith
  have hcCoefficient : 0 <
      (547765 / 1000000 : ℝ) * am +
        (2198709 / 1000000 : ℝ) * (1918 / 10000) - s ^ 2 := by
    have hamprod := mul_lt_mul_of_pos_left ham (by norm_num :
      (0 : ℝ) < 547765 / 1000000)
    have hs0 : 0 < s := lt_trans (by norm_num) hsL
    have hssq : s ^ 2 < (56173 / 100000 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hsU hs0.le (by norm_num)
    norm_num at hamprod hssq ⊢
    nlinarith
  have hsCoefficient :
      -(2115 / 10000 : ℝ) * (s + 56173 / 100000) +
          2 * (1912 / 10000 : ℝ) * t < 0 := by
    have hsadd : (56168 / 100000 + 56173 / 100000 : ℝ) <
        s + 56173 / 100000 := by linarith
    have hsprod := mul_lt_mul_of_pos_left hsadd (by norm_num :
      (0 : ℝ) < 2115 / 10000)
    have htprod := mul_lt_mul_of_pos_left htU (by norm_num :
      (0 : ℝ) < 2 * (1912 / 10000))
    norm_num at hsprod htprod ⊢
    nlinarith
  have htCoefficient : 0 <
      -(1918 / 10000 : ℝ) * (t + 53815 / 100000) +
        2 * (1912 / 10000 : ℝ) * (56173 / 100000) := by
    have htadd : t + 53815 / 100000 <
        (53836 / 100000 + 53815 / 100000 : ℝ) := by linarith
    have htprod := mul_lt_mul_of_pos_left htadd (by norm_num :
      (0 : ℝ) < 1918 / 10000)
    norm_num at htprod ⊢
    nlinarith
  have hstepT :
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          (1578 / 10000) (2112 / 10000) (4485 / 10000)
          (56173 / 100000) (53815 / 100000) ≤
        strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          (1578 / 10000) (2112 / 10000) (4485 / 10000)
          (56173 / 100000) t := by
    have hmul := mul_nonneg (sub_nonneg.mpr htL.le) htCoefficient.le
    unfold strongBoxForm
    nlinarith
  have hstepS :
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          (1578 / 10000) (2112 / 10000) (4485 / 10000)
          (56173 / 100000) t ≤
        strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          (1578 / 10000) (2112 / 10000) (4485 / 10000) s t := by
    have hmul := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hsU.le) hsCoefficient.le
    unfold strongBoxForm
    nlinarith
  have hstepCm :
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          (1578 / 10000) (2112 / 10000) (4485 / 10000) s t ≤
        strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          (1578 / 10000) (2112 / 10000) cm s t := by
    have hmul := mul_nonneg
      (sub_nonneg.mpr hcm.le)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 547765 / 1000000)
        (by norm_num : (0 : ℝ) ≤ 1918 / 10000))
    unfold strongBoxForm
    nlinarith
  have hstepBm :
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          (1578 / 10000) (2112 / 10000) cm s t ≤
        strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          (1578 / 10000) bm cm s t := by
    have hmul := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hbmU.le)
      (by norm_num : (-2 * (547765 / 1000000 : ℝ) *
        (1912 / 10000)) ≤ 0)
    unfold strongBoxForm
    nlinarith
  have hstepAmOdd :
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          (1578 / 10000) bm cm s t ≤
        strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          am bm cm s t := by
    have hmul := mul_nonneg (sub_nonneg.mpr ham.le)
      (by norm_num : (0 : ℝ) ≤
        (547765 / 1000000) * (2115 / 10000))
    unfold strongBoxForm
    nlinarith
  have hstepC :
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) (2115 / 10000)
          am bm cm s t ≤
        strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) c am bm cm s t := by
    have hmul := mul_nonneg (sub_nonneg.mpr hc.le) hcCoefficient.le
    unfold strongBoxForm
    nlinarith
  have hstepB :
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) (1912 / 10000) c am bm cm s t ≤
        strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) b c am bm cm s t := by
    have hmul := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hbU.le) hbCoefficient.le
    unfold strongBoxForm
    nlinarith
  have hstepAodd :
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          (1918 / 10000) b c am bm cm s t ≤
        strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          a b c am bm cm s t := by
    have hmul := mul_nonneg (sub_nonneg.mpr ha.le) hca.le
    unfold strongBoxForm
    nlinarith
  have hstepAm :
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
          a b c am bm cm s t ≤
        strongBoxForm (547765 / 1000000) Am a b c am bm cm s t := by
    have hmul := mul_nonneg (sub_nonneg.mpr hAm.le) hP.le
    unfold strongBoxForm
    nlinarith
  have hstepA :
      strongBoxForm (547765 / 1000000) Am a b c am bm cm s t ≤
        strongBoxForm A Am a b c am bm cm s t := by
    have hmul := mul_nonneg (sub_nonneg.mpr hA.le) hQ.le
    unfold strongBoxForm
    nlinarith
  have hcorner : (23 / 1000 : ℝ) <
      strongBoxForm (547765 / 1000000) (2198709 / 1000000)
        (1918 / 10000) (1912 / 10000) (2115 / 10000)
        (1578 / 10000) (2112 / 10000) (4485 / 10000)
        (56173 / 100000) (53815 / 100000) := by
    norm_num [strongBoxForm]
  linarith [hstepT, hstepS, hstepCm, hstepBm, hstepAmOdd,
    hstepC, hstepB, hstepAodd, hstepAm, hstepA]

private theorem strongBracket_gt : (23 / 1000 : ℝ) < strongBracket := by
  rw [strongBracket_eq_boxForm]
  have hp := factorTwoIntrinsicP4_positive_aligned_bounds
  have hm := factorTwoIntrinsicP4_negative_aligned_bounds
  have hoP := factorTwoIntrinsicOddPhaseLow_plus_entry_bounds
  have hoM := factorTwoIntrinsicOddPhaseLow_minus_entry_bounds
  have hJ := factorTwoIntrinsicAlternatingSharpBounds
  unfold FactorTwoIntrinsicAlternatingSharpBounds at hJ
  apply strongBoxForm_gt
  · simpa only [plusStrong, e00p, e02p, e22p] using hp.1
  · simpa only [minusStrong, e00m, e02m, e22m] using hm.1
  · simpa only [o11p] using hoP.1
  · simpa only [o13p] using hoP.2.2.1
  · simpa only [o13p] using hoP.2.2.2.1
  · simpa only [o33p] using hoP.2.2.2.2.1
  · simpa only [o11m] using hoM.1
  · simpa only [o13m] using hoM.2.2.1
  · simpa only [o13m] using hoM.2.2.2.1
  · simpa only [o33m] using hoM.2.2.2.2.1
  · simpa only [uSum, u0, u2] using hJ.1
  · simpa only [uSum, u0, u2] using hJ.2.1
  · simpa only [vSum, v0, v2] using hJ.2.2.2.2.1
  · simpa only [vSum, v0, v2] using hJ.2.2.2.2.2.1
  · exact (factorTwoIntrinsicOddPhaseLow_plus_minor_gt_one_div_two_fifty).trans' (by norm_num)
  · have hq := rawFiveOddMinorCoeff_one_gt_one_div_twenty_five
    rw [rawFiveOddMinorCoeff_one_eq] at hq
    simpa only [oddMixedOne, o11p, o13p, o33p, o11m, o13m, o33m] using
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 25) hq)

private theorem weakBoxForm_gt
    (Rm a b c d e : ℝ)
    (hRm : (18409 / 1000000 : ℝ) < Rm)
    (ha : (1918 / 10000 : ℝ) < a)
    (hbL : (189 / 1000 : ℝ) < b)
    (hbU : b < (1912 / 10000 : ℝ))
    (hc : (2115 / 10000 : ℝ) < c)
    (hdL : (1687 / 100000 : ℝ) < d)
    (hdU : d < (1692 / 100000 : ℝ))
    (heL : (555 / 10000 : ℝ) < e)
    (heU : e < (279 / 5000 : ℝ))
    (hP : 0 < a * c - b ^ 2) :
    (-23 / 100000 : ℝ) < weakBoxForm Rm a b c d e := by
  have heCoefficient :
      2 * (1912 / 10000 : ℝ) * (1687 / 100000) -
          (1918 / 10000 : ℝ) * (e + 279 / 5000) < 0 := by
    have headd : (555 / 10000 + 279 / 5000 : ℝ) <
        e + 279 / 5000 := by linarith
    have heprod := mul_lt_mul_of_pos_left headd (by norm_num :
      (0 : ℝ) < 1918 / 10000)
    norm_num at heprod ⊢
    nlinarith
  have hdCoefficient :
      0 < -(2115 / 10000 : ℝ) * (d + 1687 / 100000) +
        2 * (1912 / 10000 : ℝ) * e := by
    have hdadd : d + 1687 / 100000 <
        (1692 / 100000 + 1687 / 100000 : ℝ) := by linarith
    have hdprod := mul_lt_mul_of_pos_left hdadd (by norm_num :
      (0 : ℝ) < 2115 / 10000)
    have heprod := mul_lt_mul_of_pos_left heL (by norm_num :
      (0 : ℝ) < 2 * (1912 / 10000))
    norm_num at hdprod heprod ⊢
    nlinarith
  have hcCoefficient : 0 <
      (18409 / 1000000 : ℝ) * (1918 / 10000) - d ^ 2 := by
    have hd0 : 0 < d := lt_trans (by norm_num) hdL
    have hdsq : d ^ 2 < (1692 / 100000 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hdU hd0.le (by norm_num)
    norm_num at hdsq ⊢
    nlinarith
  have hbCoefficient :
      -(18409 / 1000000 : ℝ) * (b + 1912 / 10000) +
        2 * d * e < 0 := by
    have hbadd : (189 / 1000 + 1912 / 10000 : ℝ) <
        b + 1912 / 10000 := by linarith
    have hbprod := mul_lt_mul_of_pos_left hbadd (by norm_num :
      (0 : ℝ) < 18409 / 1000000)
    have hd0 : 0 < d := lt_trans (by norm_num) hdL
    have he0 : 0 < e := lt_trans (by norm_num) heL
    have hde : d * e < (1692 / 100000 : ℝ) * (279 / 5000) := by
      calc
        d * e < (1692 / 100000 : ℝ) * e :=
          mul_lt_mul_of_pos_right hdU he0
        _ < (1692 / 100000 : ℝ) * (279 / 5000) :=
          mul_lt_mul_of_pos_left heU (by norm_num)
    norm_num at hbprod hde ⊢
    nlinarith
  have haCoefficient : 0 <
      (18409 / 1000000 : ℝ) * c - e ^ 2 := by
    have hcprod := mul_lt_mul_of_pos_left hc (by norm_num :
      (0 : ℝ) < 18409 / 1000000)
    have he0 : 0 < e := lt_trans (by norm_num) heL
    have hesq : e ^ 2 < (279 / 5000 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ heU he0.le (by norm_num)
    norm_num at hcprod hesq ⊢
    nlinarith
  have hstepE :
      weakBoxForm (18409 / 1000000) (1918 / 10000)
          (1912 / 10000) (2115 / 10000) (1687 / 100000)
          (279 / 5000) ≤
        weakBoxForm (18409 / 1000000) (1918 / 10000)
          (1912 / 10000) (2115 / 10000) (1687 / 100000) e := by
    have hmul := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr heU.le) heCoefficient.le
    unfold weakBoxForm
    nlinarith
  have hstepD :
      weakBoxForm (18409 / 1000000) (1918 / 10000)
          (1912 / 10000) (2115 / 10000) (1687 / 100000) e ≤
        weakBoxForm (18409 / 1000000) (1918 / 10000)
          (1912 / 10000) (2115 / 10000) d e := by
    have hmul := mul_nonneg (sub_nonneg.mpr hdL.le) hdCoefficient.le
    unfold weakBoxForm
    nlinarith
  have hstepC :
      weakBoxForm (18409 / 1000000) (1918 / 10000)
          (1912 / 10000) (2115 / 10000) d e ≤
        weakBoxForm (18409 / 1000000) (1918 / 10000)
          (1912 / 10000) c d e := by
    have hmul := mul_nonneg (sub_nonneg.mpr hc.le) hcCoefficient.le
    unfold weakBoxForm
    nlinarith
  have hstepB :
      weakBoxForm (18409 / 1000000) (1918 / 10000)
          (1912 / 10000) c d e ≤
        weakBoxForm (18409 / 1000000) (1918 / 10000) b c d e := by
    have hmul := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hbU.le) hbCoefficient.le
    unfold weakBoxForm
    nlinarith
  have hstepA :
      weakBoxForm (18409 / 1000000) (1918 / 10000) b c d e ≤
        weakBoxForm (18409 / 1000000) a b c d e := by
    have hmul := mul_nonneg (sub_nonneg.mpr ha.le) haCoefficient.le
    unfold weakBoxForm
    nlinarith
  have hstepRm :
      weakBoxForm (18409 / 1000000) a b c d e ≤
        weakBoxForm Rm a b c d e := by
    have hmul := mul_nonneg (sub_nonneg.mpr hRm.le) hP.le
    unfold weakBoxForm
    nlinarith
  have hcorner : (-23 / 100000 : ℝ) <
      weakBoxForm (18409 / 1000000) (1918 / 10000)
        (1912 / 10000) (2115 / 10000) (1687 / 100000)
        (279 / 5000) := by
    norm_num [weakBoxForm]
  exact hcorner.trans_le
    (hstepE.trans (hstepD.trans (hstepC.trans
      (hstepB.trans (hstepA.trans hstepRm)))))

private theorem weakBracket_gt : (-23 / 100000 : ℝ) < weakBracket := by
  rw [weakBracket_eq_boxForm]
  have hp := factorTwoIntrinsicP4_positive_aligned_bounds
  have hm := factorTwoIntrinsicP4_negative_aligned_bounds
  have hoP := factorTwoIntrinsicOddPhaseLow_plus_entry_bounds
  have hJ := factorTwoIntrinsicAlternatingSharpBounds
  unfold FactorTwoIntrinsicAlternatingSharpBounds at hJ
  apply weakBoxForm_gt
  · simpa only [minusWeak, e00m, e02m, e22m] using hm.2.2.2.2.2.2.1
  · simpa only [o11p] using hoP.1
  · simpa only [o13p] using hoP.2.2.1
  · simpa only [o13p] using hoP.2.2.2.1
  · simpa only [o33p] using hoP.2.2.2.2.1
  · simpa only [uDifference, u0, u2] using hJ.2.2.1
  · simpa only [uDifference, u0, u2] using hJ.2.2.2.1
  · simpa only [vDifference, v0, v2] using hJ.2.2.2.2.2.2.1
  · simpa only [vDifference, v0, v2] using hJ.2.2.2.2.2.2.2
  · exact (by
      have h := factorTwoIntrinsicOddPhaseLow_plus_minor_gt_one_div_two_fifty
      unfold o11p o13p o33p
      linarith : 0 < o11p * o33p - o13p ^ 2)

private theorem oddMixedOne_lt_forty_seven_div_thousand :
    oddMixedOne < (47 / 1000 : ℝ) := by
  rcases factorTwoIntrinsicOddPhaseLow_plus_entry_bounds with
    ⟨haL, haU, hbL, _hbU, _hcL, hcU⟩
  rcases factorTwoIntrinsicOddPhaseLow_minus_entry_bounds with
    ⟨hamL, hamU, hbmL, _hbmU, _hcmL, hcmU⟩
  have ha0 : 0 < o11p := by
    simpa only [o11p] using lt_trans (by norm_num : (0 : ℝ) < 1918 / 10000) haL
  have hc0 : 0 < o33p := by
    simpa only [o33p] using lt_trans (by norm_num : (0 : ℝ) < 2115 / 10000)
      factorTwoIntrinsicOddPhaseLow_plus_entry_bounds.2.2.2.2.1
  have hb0 : 0 < o13p := by
    simpa only [o13p] using lt_trans (by norm_num : (0 : ℝ) < 189 / 1000) hbL
  have ham0 : 0 < o11m := by
    simpa only [o11m] using lt_trans (by norm_num : (0 : ℝ) < 1578 / 10000) hamL
  have hbm0 : 0 < o13m := by
    simpa only [o13m] using lt_trans (by norm_num : (0 : ℝ) < 209 / 1000) hbmL
  have hcm0 : 0 < o33m := by
    simpa only [o33m] using lt_trans (by norm_num : (0 : ℝ) < 4485 / 10000)
      factorTwoIntrinsicOddPhaseLow_minus_entry_bounds.2.2.2.2.1
  have hprod1 : o11p * o33m < (199 / 1000 : ℝ) * (453 / 1000) := by
    calc
      o11p * o33m < (199 / 1000 : ℝ) * o33m :=
        mul_lt_mul_of_pos_right (by simpa only [o11p] using haU) hcm0
      _ < (199 / 1000 : ℝ) * (453 / 1000) :=
        mul_lt_mul_of_pos_left (by simpa only [o33m] using hcmU) (by norm_num)
  have hprod2 : o11m * o33p < (165 / 1000 : ℝ) * (216 / 1000) := by
    calc
      o11m * o33p < (165 / 1000 : ℝ) * o33p :=
        mul_lt_mul_of_pos_right (by simpa only [o11m] using hamU) hc0
      _ < (165 / 1000 : ℝ) * (216 / 1000) :=
        mul_lt_mul_of_pos_left (by simpa only [o33p] using hcU) (by norm_num)
  have hprod3 : (189 / 1000 : ℝ) * (209 / 1000) < o13p * o13m := by
    calc
      (189 / 1000 : ℝ) * (209 / 1000) < o13p * (209 / 1000) :=
        mul_lt_mul_of_pos_right (by simpa only [o13p] using hbL) (by norm_num)
      _ < o13p * o13m :=
        mul_lt_mul_of_pos_left (by simpa only [o13m] using hbmL) hb0
  unfold oddMixedOne
  norm_num at hprod1 hprod2 hprod3 ⊢
  nlinarith

private theorem oddSumDifferencePolar_bounds :
    (-1 / 100000 : ℝ) < oddSumDifferencePolar ∧
      oddSumDifferencePolar < (9 / 10000 : ℝ) := by
  rcases factorTwoIntrinsicOddPhaseLow_plus_entry_bounds with
    ⟨haL, haU, hbL, hbU, hcL, hcU⟩
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨hsL, hsU, hdL, hdU, htL, htU, heL, heU⟩
  have ha0 : 0 < o11p := by
    simpa only [o11p] using lt_trans (by norm_num : (0 : ℝ) < 1918 / 10000) haL
  have hb0 : 0 < o13p := by
    simpa only [o13p] using lt_trans (by norm_num : (0 : ℝ) < 189 / 1000) hbL
  have hc0 : 0 < o33p := by
    simpa only [o33p] using lt_trans (by norm_num : (0 : ℝ) < 2115 / 10000) hcL
  have hs0 : 0 < uSum := by
    simpa only [uSum, u0, u2] using lt_trans (by norm_num : (0 : ℝ) < 56168 / 100000) hsL
  have hd0 : 0 < uDifference := by
    simpa only [uDifference, u0, u2] using
      lt_trans (by norm_num : (0 : ℝ) < 1687 / 100000) hdL
  have ht0 : 0 < vSum := by
    simpa only [vSum, v0, v2] using
      lt_trans (by norm_num : (0 : ℝ) < 53815 / 100000) htL
  have he0 : 0 < vDifference := by
    simpa only [vDifference, v0, v2] using
      lt_trans (by norm_num : (0 : ℝ) < 555 / 10000) heL
  have hcsL : (2115 / 10000 : ℝ) * (56168 / 100000) < o33p * uSum := by
    calc
      _ < o33p * (56168 / 100000) :=
        mul_lt_mul_of_pos_right (by simpa only [o33p] using hcL) (by norm_num)
      _ < o33p * uSum :=
        mul_lt_mul_of_pos_left (by simpa only [uSum, u0, u2] using hsL) hc0
  have hcsdL :
      (2115 / 10000 : ℝ) * (56168 / 100000) * (1687 / 100000) <
        o33p * uSum * uDifference := by
    calc
      _ < o33p * uSum * (1687 / 100000) :=
        mul_lt_mul_of_pos_right hcsL (by norm_num)
      _ < o33p * uSum * uDifference :=
        mul_lt_mul_of_pos_left
          (by simpa only [uDifference, u0, u2] using hdL) (mul_pos hc0 hs0)
  have hatL : (1918 / 10000 : ℝ) * (53815 / 100000) < o11p * vSum := by
    calc
      _ < o11p * (53815 / 100000) :=
        mul_lt_mul_of_pos_right (by simpa only [o11p] using haL) (by norm_num)
      _ < o11p * vSum :=
        mul_lt_mul_of_pos_left (by simpa only [vSum, v0, v2] using htL) ha0
  have hateL :
      (1918 / 10000 : ℝ) * (53815 / 100000) * (555 / 10000) <
        o11p * vSum * vDifference := by
    calc
      _ < o11p * vSum * (555 / 10000) :=
        mul_lt_mul_of_pos_right hatL (by norm_num)
      _ < o11p * vSum * vDifference :=
        mul_lt_mul_of_pos_left
          (by simpa only [vDifference, v0, v2] using heL) (mul_pos ha0 ht0)
  have hseU : uSum * vDifference <
      (56173 / 100000 : ℝ) * (279 / 5000) := by
    calc
      _ < (56173 / 100000 : ℝ) * vDifference :=
        mul_lt_mul_of_pos_right (by simpa only [uSum, u0, u2] using hsU) he0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vDifference, v0, v2] using heU) (by norm_num)
  have hdtU : uDifference * vSum <
      (1692 / 100000 : ℝ) * (53836 / 100000) := by
    calc
      _ < (1692 / 100000 : ℝ) * vSum :=
        mul_lt_mul_of_pos_right
          (by simpa only [uDifference, u0, u2] using hdU) ht0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vSum, v0, v2] using htU) (by norm_num)
  have hmiddle0 : 0 < uSum * vDifference + uDifference * vSum := by positivity
  have hmiddleU : uSum * vDifference + uDifference * vSum <
      (56173 / 100000 : ℝ) * (279 / 5000) +
        (1692 / 100000) * (53836 / 100000) := by linarith
  have hbmiddleU : o13p * (uSum * vDifference + uDifference * vSum) <
      (1912 / 10000 : ℝ) *
        ((56173 / 100000) * (279 / 5000) +
          (1692 / 100000) * (53836 / 100000)) := by
    calc
      _ < (1912 / 10000 : ℝ) *
          (uSum * vDifference + uDifference * vSum) :=
        mul_lt_mul_of_pos_right (by simpa only [o13p] using hbU) hmiddle0
      _ < _ := mul_lt_mul_of_pos_left hmiddleU (by norm_num)
  have hcsU : o33p * uSum < (216 / 1000 : ℝ) * (56173 / 100000) := by
    calc
      _ < (216 / 1000 : ℝ) * uSum :=
        mul_lt_mul_of_pos_right (by simpa only [o33p] using hcU) hs0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [uSum, u0, u2] using hsU) (by norm_num)
  have hcsdU : o33p * uSum * uDifference <
      (216 / 1000 : ℝ) * (56173 / 100000) * (1692 / 100000) := by
    calc
      _ < (216 / 1000 : ℝ) * (56173 / 100000) * uDifference :=
        mul_lt_mul_of_pos_right hcsU hd0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [uDifference, u0, u2] using hdU) (by norm_num)
  have hatU : o11p * vSum < (199 / 1000 : ℝ) * (53836 / 100000) := by
    calc
      _ < (199 / 1000 : ℝ) * vSum :=
        mul_lt_mul_of_pos_right (by simpa only [o11p] using haU) ht0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vSum, v0, v2] using htU) (by norm_num)
  have hateU : o11p * vSum * vDifference <
      (199 / 1000 : ℝ) * (53836 / 100000) * (279 / 5000) := by
    calc
      _ < (199 / 1000 : ℝ) * (53836 / 100000) * vDifference :=
        mul_lt_mul_of_pos_right hatU he0
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vDifference, v0, v2] using heU) (by norm_num)
  have hseL : (56168 / 100000 : ℝ) * (555 / 10000) <
      uSum * vDifference := by
    calc
      _ < uSum * (555 / 10000) :=
        mul_lt_mul_of_pos_right
          (by simpa only [uSum, u0, u2] using hsL) (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vDifference, v0, v2] using heL) hs0
  have hdtL : (1687 / 100000 : ℝ) * (53815 / 100000) <
      uDifference * vSum := by
    calc
      _ < uDifference * (53815 / 100000) :=
        mul_lt_mul_of_pos_right
          (by simpa only [uDifference, u0, u2] using hdL) (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left
        (by simpa only [vSum, v0, v2] using htL) hd0
  have hmiddleL :
      (56168 / 100000 : ℝ) * (555 / 10000) +
          (1687 / 100000) * (53815 / 100000) <
        uSum * vDifference + uDifference * vSum := by linarith
  have hbmiddleL :
      (189 / 1000 : ℝ) *
          ((56168 / 100000) * (555 / 10000) +
            (1687 / 100000) * (53815 / 100000)) <
        o13p * (uSum * vDifference + uDifference * vSum) := by
    calc
      _ < o13p *
          ((56168 / 100000) * (555 / 10000) +
            (1687 / 100000) * (53815 / 100000)) :=
        mul_lt_mul_of_pos_right (by simpa only [o13p] using hbL) (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hmiddleL hb0
  constructor <;> unfold oddSumDifferencePolar
  · norm_num at hcsdL hateL hbmiddleU ⊢
    nlinarith
  · norm_num at hcsdU hateU hbmiddleL ⊢
    nlinarith

private theorem skewBracket_bounds :
    (-13 / 10000 : ℝ) < skewBracket ∧
      skewBracket < (1 / 1000 : ℝ) := by
  have hp := factorTwoIntrinsicP4_positive_aligned_bounds
  have hm := factorTwoIntrinsicP4_negative_aligned_bounds
  have hdetL : 0 < oddDetPlus := by
    unfold oddDetPlus o11p o13p o33p
    linarith [factorTwoIntrinsicOddPhaseLow_plus_minor_gt_one_div_two_fifty]
  have hdetU := oddDetPlus_lt_seventy_three_div_ten_thousand
  have hmixL : 0 < oddMixedOne := by
    have h := rawFiveOddMinorCoeff_one_gt_one_div_twenty_five
    rw [rawFiveOddMinorCoeff_one_eq] at h
    simpa only [oddMixedOne, o11p, o13p, o33p, o11m, o13m, o33m] using
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 25) h)
  have hmixU := oddMixedOne_lt_forty_seven_div_thousand
  have hXmL : (77471 / 1000000 : ℝ) < minusSkew := by
    simpa only [minusSkew, e00m, e22m] using hm.2.2.1
  have hXmU : minusSkew < (79531 / 1000000 : ℝ) := by
    simpa only [minusSkew, e00m, e22m] using hm.2.2.2.1
  have hXm0 : 0 < minusSkew := lt_trans (by norm_num) hXmL
  have hXL : (-141 / 1000000 : ℝ) < plusSkew := by
    have hx := hp.2.2.1
    simpa only [plusSkew, e00p, e22p] using hx
  have hXU : plusSkew < (1919 / 1000000 : ℝ) := by
    simpa only [plusSkew, e00p, e22p] using hp.2.2.2.1
  have hXmDetU : minusSkew * oddDetPlus <
      (79531 / 1000000 : ℝ) * (73 / 10000) := by
    calc
      _ < (79531 / 1000000 : ℝ) * oddDetPlus :=
        mul_lt_mul_of_pos_right hXmU hdetL
      _ < _ := mul_lt_mul_of_pos_left hdetU (by norm_num)
  constructor
  · rcases oddSumDifferencePolar_bounds with ⟨hpolar, _⟩
    by_cases hX : plusSkew ≤ 0
    · have hlast : 0 ≤ -plusSkew * oddMixedOne :=
        mul_nonneg (neg_nonneg.mpr hX) hmixL.le
      unfold skewBracket
      norm_num at hpolar hXmDetU ⊢
      nlinarith
    · have hX0 : 0 < plusSkew := lt_of_not_ge hX
      have hXMixU : plusSkew * oddMixedOne <
          (1919 / 1000000 : ℝ) * (47 / 1000) := by
        calc
          _ < (1919 / 1000000 : ℝ) * oddMixedOne :=
            mul_lt_mul_of_pos_right hXU hmixL
          _ < _ := mul_lt_mul_of_pos_left hmixU (by norm_num)
      unfold skewBracket
      norm_num at hpolar hXmDetU hXMixU ⊢
      nlinarith
  · rcases oddSumDifferencePolar_bounds with ⟨_, hpolar⟩
    have hmiddle : 0 < 2 * minusSkew * oddDetPlus := by positivity
    by_cases hX : 0 ≤ plusSkew
    · have hlast : 0 ≤ plusSkew * oddMixedOne := mul_nonneg hX hmixL.le
      unfold skewBracket
      norm_num at hpolar ⊢
      linarith
    · have hnegX0 : 0 < -plusSkew := neg_pos.mpr (lt_of_not_ge hX)
      have hnegXU : -plusSkew < (141 / 1000000 : ℝ) := by linarith
      have hnegXMixU : (-plusSkew) * oddMixedOne <
          (141 / 1000000 : ℝ) * (47 / 1000) := by
        calc
          _ < (141 / 1000000 : ℝ) * oddMixedOne :=
            mul_lt_mul_of_pos_right hnegXU hmixL
          _ < _ := mul_lt_mul_of_pos_left hmixU (by norm_num)
      unfold skewBracket
      norm_num at hpolar hnegXMixU ⊢
      nlinarith

private theorem lowCoefficientOne_pos : 0 < lowCoefficientOne := by
  have hp := factorTwoIntrinsicP4_positive_aligned_bounds
  have hA0 : 0 < plusStrong := by
    simpa only [plusStrong, e00p, e02p, e22p] using
      lt_trans (by norm_num : (0 : ℝ) < 547765 / 1000000) hp.1
  have hAU : plusStrong < (549941 / 1000000 : ℝ) := by
    simpa only [plusStrong, e00p, e02p, e22p] using hp.2.1
  have hR : (6065 / 1000000 : ℝ) < plusWeak := by
    simpa only [plusWeak, e00p, e02p, e22p] using hp.2.2.2.2.2.2.1
  have hR0 : 0 < plusWeak := lt_trans (by norm_num) hR
  have hXL : (-141 / 1000000 : ℝ) < plusSkew := by
    have hx := hp.2.2.1
    simpa only [plusSkew, e00p, e22p] using hx
  have hXU : plusSkew < (1919 / 1000000 : ℝ) := by
    simpa only [plusSkew, e00p, e22p] using hp.2.2.2.1
  have hStrong := strongBracket_gt
  have hStrong0 : 0 < strongBracket := lt_trans (by norm_num) hStrong
  have hWeak := weakBracket_gt
  rcases skewBracket_bounds with ⟨hSkewL, hSkewU⟩
  have hRW : (6065 / 1000000 : ℝ) * (23 / 1000) <
      plusWeak * strongBracket := by
    calc
      _ < plusWeak * (23 / 1000) := mul_lt_mul_of_pos_right hR (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hStrong hR0
  have hAW : (549941 / 1000000 : ℝ) * (-23 / 100000) <
      plusStrong * weakBracket := by
    by_cases hW : 0 ≤ weakBracket
    · have : 0 ≤ plusStrong * weakBracket := mul_nonneg hA0.le hW
      nlinarith
    · have hWneg : weakBracket < 0 := lt_of_not_ge hW
      calc
        _ < (549941 / 1000000 : ℝ) * weakBracket :=
          mul_lt_mul_of_pos_left hWeak (by norm_num)
        _ < plusStrong * weakBracket := mul_lt_mul_of_neg_right hAU hWneg
  have hXK : (1919 / 1000000 : ℝ) * (-13 / 10000) <
      plusSkew * skewBracket := by
    by_cases hX : 0 ≤ plusSkew
    · by_cases hK : 0 ≤ skewBracket
      · have : 0 ≤ plusSkew * skewBracket := mul_nonneg hX hK
        nlinarith
      · have hKneg : skewBracket < 0 := lt_of_not_ge hK
        calc
          _ < (1919 / 1000000 : ℝ) * skewBracket :=
            mul_lt_mul_of_pos_left hSkewL (by norm_num)
          _ < plusSkew * skewBracket := mul_lt_mul_of_neg_right hXU hKneg
    · have hXneg : plusSkew < 0 := lt_of_not_ge hX
      by_cases hK : skewBracket ≤ 0
      · have : 0 ≤ plusSkew * skewBracket :=
          mul_nonneg_of_nonpos_of_nonpos hXneg.le hK
        nlinarith
      · have hKpos : 0 < skewBracket := lt_of_not_ge hK
        have hbetter : (-141 / 1000000 : ℝ) * (1 / 1000) <
            plusSkew * skewBracket := by
          calc
            _ < (-141 / 1000000 : ℝ) * skewBracket :=
              mul_lt_mul_of_neg_left hSkewU (by norm_num)
            _ < plusSkew * skewBracket := mul_lt_mul_of_pos_right hXL hKpos
        norm_num at hbetter ⊢
        linarith
  have hsum : 0 < plusWeak * strongBracket + plusStrong * weakBracket +
      plusSkew * skewBracket := by
    norm_num at hRW hAW hXK ⊢
    linarith
  rw [← four_mul_lowCoefficientOne_eq_brackets] at hsum
  nlinarith

/-- The first mixed coefficient of the raw five-mode determinant is
nonnegative. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_one_nonneg :
    0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1 := by
  have hidentity := coefficient_one_schur_identity
  rw [lowDet_mul_evenMixed_sub_evenDet_mul_lowMixed_eq_reserve] at hidentity
  have hbase : 0 < evenDetPlus * lowCoefficientOne :=
    mul_pos evenDetPlus_pos lowCoefficientOne_pos
  have hlast : 0 < evenMinusSchurReserve * oddDetPlus -
      p4ResidualOddAdjugate := by
    linarith [reserve_times_oddDet_gt_residualOddAdjugate]
  have hscaled : 0 < lowDetPlus *
      factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1 := by
    nlinarith
  have hcoefficient :
      0 < factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 1 := by
    rcases mul_pos_iff.mp hscaled with h | h
    · exact h.2
    · exact (not_lt_of_ge lowDetPlus_pos.le h.1).elim
  exact hcoefficient.le

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC1Structural
