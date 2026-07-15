import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoStructuralConstantBounds

/-!
# The final positive static Schur gate

The `P₁/P₃` block is kept in the shear

`P₁, P₃ - (25 / 24) P₁`.

The final step is a bordered completion, not a corner expansion.  The
coarse public lower bound for the negative-endpoint `P₅` diagonal loses the
signed perturbation reserve, so we first recover that reserve directly from
the structural kernel identity.
-/

/-! ## The signed `P₅` reserve -/

/-- The negative `P₅` perturbation has a quantitative structural margin.
This uses one global pole-free error estimate and the retained-prime
correlation; there is no subdivision or sampled evaluation. -/
theorem factorTwoCenteredSymmetricPerturbation_p5_lt_neg_eighty_one_thousandths :
    factorTwoCenteredSymmetricPerturbation factorTwoCenteredP5 <
      (-81 / 1000 : ℝ) := by
  let α : ℝ := Real.log 2 / Real.sqrt 2
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c : ℝ := oddP5Correlation55
    (factorTwoPrimeShift / yoshidaEndpointA)
  have herr := abs_poleFreeAnalyticError_oddP5Correlation55_le
  rw [abs_le] at herr
  have hlog := strict_log_two_fine_bounds
  have hα : (49 / 100 : ℝ) < α ∧ α < (491 / 1000 : ℝ) := by
    simpa only [α] using factorTwoDyadicWeight_bounds
  have hβ : (63427 / 100000 : ℝ) < β ∧ β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds
  have hc : (7 / 500 : ℝ) < c ∧ c < (3 / 200 : ℝ) := by
    simpa only [c] using oddP5PrimeCorrelation55_bounds
  have hβ0 : 0 < β :=
    (by norm_num : (0 : ℝ) < 63427 / 100000).trans hβ.1
  have hprimeLower :
      (63427 / 100000 : ℝ) * (7 / 500) < β * c := by
    calc
      (63427 / 100000 : ℝ) * (7 / 500) < β * (7 / 500) :=
        mul_lt_mul_of_pos_right hβ.1 (by norm_num)
      _ < β * c := mul_lt_mul_of_pos_left hc.1 hβ0
  rw [factorTwoCenteredSymmetricPerturbation_p5_structural_eq]
  dsimp only [α, β, c] at hprimeLower ⊢
  nlinarith [herr.2, hlog.1, hα.1, hprimeLower]

private theorem fourteen_fifty_fifths_le_clean_p5 :
    (14 / 55 : ℝ) ≤
      yoshidaEndpointOddCleanQuadratic factorTwoCenteredP5 := by
  have hclean := seven_fifths_energy_le_clean_P5
  have henergy :
      factorTwoIntrinsicEnergy factorTwoCenteredP5 = (2 / 11 : ℝ) := by
    simpa [factorTwoIntrinsicEnergy] using integral_factorTwoCenteredP5_sq
  rw [henergy] at hclean
  norm_num at hclean ⊢
  exact hclean

/-- The endpoint diagonal used by the positive static block is larger than
`1/3`.  Keeping the sign of the `P₅` perturbation is essential here. -/
theorem one_third_lt_factorTwoIntrinsicSixUnbalancedOMinus55 :
    (1 / 3 : ℝ) < factorTwoIntrinsicSixUnbalancedOMinus55 := by
  have hclean := fourteen_fifty_fifths_le_clean_p5
  have hpert :=
    factorTwoCenteredSymmetricPerturbation_p5_lt_neg_eighty_one_thousandths
  unfold factorTwoIntrinsicSixUnbalancedOMinus55
    factorTwoIntrinsicP5PhaseDiagonal
  norm_num at hclean hpert ⊢
  nlinarith

/-! ## Bordered coordinates -/

def plusP5ShearCross : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlus35 -
    (25 / 24 : ℝ) * factorTwoIntrinsicSixUnbalancedTPlus15

def plusP5BorderCross : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlus11 * plusP5ShearCross -
    plusShearCross * factorTwoIntrinsicSixUnbalancedTPlus15

def plusP5BorderDiagonal : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlus11 *
      factorTwoIntrinsicSixUnbalancedTPlus55 -
    factorTwoIntrinsicSixUnbalancedTPlus15 ^ 2

/-- Fraction-free bordered determinant identity after the `25/24` shear. -/
theorem factorTwoIntrinsicSixUnbalancedTPlus11_mul_det_eq_bordered :
    factorTwoIntrinsicSixUnbalancedTPlus11 *
        factorTwoIntrinsicSixUnbalancedTPlusDet =
      factorTwoIntrinsicSixUnbalancedTPlusMinor * plusP5BorderDiagonal -
        plusP5BorderCross ^ 2 := by
  unfold factorTwoIntrinsicSixUnbalancedTPlusDet symmetricDeterminant
    factorTwoIntrinsicSixUnbalancedTPlusMinor leadingMinorTwo
    plusP5BorderDiagonal plusP5BorderCross plusP5ShearCross plusShearCross
  ring

/-! ## The exact six-dimensional congruence

The first five coordinates are exactly the congruence used for the minor.
The sixth coordinate is then completed by one rational column.  The
quantities `plusDetH0`, ..., `plusDetH4`, and `plusDetW` are kept as exact
structural expressions; bounding them only after they have been formed is
the cancellation-preserving part of the proof.
-/

private def plusDetFiveQuadratic
    (a00 a01 a02 a03 a04 a11 a12 a13 a14 a22 a23 a24 a33 a34 a44
      x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  a00 * x0 ^ 2 + 2 * a01 * x0 * x1 + 2 * a02 * x0 * x2 +
    2 * a03 * x0 * x3 + 2 * a04 * x0 * x4 + a11 * x1 ^ 2 +
    2 * a12 * x1 * x2 + 2 * a13 * x1 * x3 + 2 * a14 * x1 * x4 +
    a22 * x2 ^ 2 + 2 * a23 * x2 * x3 + 2 * a24 * x2 * x4 +
    a33 * x3 ^ 2 + 2 * a34 * x3 * x4 + a44 * x4 ^ 2

private def plusDetLowerFiveQuadratic
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33 s d p u v : ℝ) : ℝ :=
  (54807 / 100000 : ℝ) * s ^ 2 +
    2 * (63 / 100000 : ℝ) * s * d +
    (631 / 100000 : ℝ) * d ^ 2 + 2 * S * s * p - 2 * D * d * p +
    (3439 / 25000 : ℝ) * p ^ 2 +
    2 * ((s1 / 2 - 1207 / 10000) * s +
      (d1 / 2 - 53 / 10000) * d + (a41 / 2 - 169 / 5000) * p) *
      (u - (25 / 24 : ℝ) * v) +
    2 * ((s3 / 2 - 687 / 10000) * s +
      (d3 / 2 + 13 / 10000) * d + (a43 / 2 - 253 / 5000) * p) * v +
    o11 * (u - (25 / 24 : ℝ) * v) ^ 2 +
    2 * o13 * (u - (25 / 24 : ℝ) * v) * v + o33 * v ^ 2

private def plusDetLowerSixQuadratic
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33
      a05 a25 a45 o15 o35 o55 s d p u v w : ℝ) : ℝ :=
  plusDetLowerFiveQuadratic S D s1 d1 s3 d3 a41 a43 o11 o13 o33
      s d p u v +
    2 * (((a05 + a25) / 2 - 283 / 10000) * s +
      ((a05 - a25) / 2 + 133 / 10000) * d +
      (a45 / 2 - 457 / 5000) * p) * w +
    2 * o15 * (u - (25 / 24 : ℝ) * v) * w +
    2 * o35 * v * w + o55 * w ^ 2

private def plusDetT00 : ℝ := 54807 / 100000
private def plusDetT01 : ℝ := 8193 / 100000000

private def plusDetT02 (S : ℝ) : ℝ :=
  -72341 / 375000 + S

private def plusDetT03 (S s1 : ℝ) : ℝ :=
  -33240533 / 68000000 + (27 / 25) * S + s1 / 2

private def plusDetT04 (S s1 s3 : ℝ) : ℝ :=
  -33784021 / 68400000 + (83 / 32) * S - (359 / 720) * s1 + s3 / 2

private def plusDetT11 : ℝ := 630928807 / 100000000000

private def plusDetT12 (S D : ℝ) : ℝ :=
  22050023 / 1125000000 - S / 1000 - D

private def plusDetT13 (S D s1 d1 : ℝ) : ℝ :=
  880683533 / 68000000000 - (27 / 25000) * S - s1 / 2000 -
    (27 / 25) * D + d1 / 2

private def plusDetT14 (S D s1 d1 s3 d3 : ℝ) : ℝ :=
  2144825021 / 68400000000 - (83 / 32000) * S +
    (359 / 720000) * s1 - s3 / 2000 - (83 / 32) * D -
    (359 / 720) * d1 + d3 / 2

private def plusDetT22 (S D : ℝ) : ℝ :=
  13492963 / 50625000 - (32 / 45) * S - (56 / 9) * D

private def plusDetT23 (S D s1 d1 a41 : ℝ) : ℝ :=
  250417709 / 765000000 - (1059 / 1000) * S - (8 / 45) * s1 -
    (2653 / 425) * D + (14 / 9) * d1 + a41 / 2

private def plusDetT24 (S D s1 d1 s3 d3 a41 a43 : ℝ) : ℝ :=
  1254873029 / 2052000000 - (173 / 90) * S + (359 / 2025) * s1 -
    (8 / 45) * s3 - (16439 / 1368) * D - (2513 / 1620) * d1 +
    (14 / 9) * d3 - (359 / 720) * a41 + a43 / 2

private def plusDetT33 (S D s1 d1 a41 o11 : ℝ) : ℝ :=
  600565366679 / 1156000000000 - (729 / 500) * S - (27 / 40) * s1 -
    (2646 / 425) * D + (49 / 17) * d1 + (27 / 25) * a41 + o11

private def plusDetT34
    (S D s1 d1 s3 d3 a41 a43 o11 o13 : ℝ) : ℝ :=
  186410386043 / 232560000000 - (18117 / 6400) * S -
    (523 / 3200) * s1 - (27 / 80) * s3 - (121337 / 10336) * D +
    (124771 / 232560) * d1 + (49 / 34) * d3 +
    (6067 / 8000) * a41 + (27 / 50) * a43 -
    (359 / 360) * o11 + o13

private def plusDetT44
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33 : ℝ) : ℝ :=
  118763043007 / 83174400000 - (83 / 16) * S + (359 / 360) * s1 - s3 -
    (6225 / 304) * D - (1795 / 456) * d1 + (75 / 19) * d3 -
    (29797 / 11520) * a41 + (83 / 32) * a43 +
    (128881 / 129600) * o11 - (359 / 180) * o13 + o33

private def plusDetTransformedFiveQuadratic
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33
      x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  plusDetFiveQuadratic plusDetT00 plusDetT01 (plusDetT02 S)
    (plusDetT03 S s1) (plusDetT04 S s1 s3) plusDetT11
    (plusDetT12 S D) (plusDetT13 S D s1 d1)
    (plusDetT14 S D s1 d1 s3 d3) (plusDetT22 S D)
    (plusDetT23 S D s1 d1 a41)
    (plusDetT24 S D s1 d1 s3 d3 a41 a43)
    (plusDetT33 S D s1 d1 a41 o11)
    (plusDetT34 S D s1 d1 s3 d3 a41 a43 o11 o13)
    (plusDetT44 S D s1 d1 s3 d3 a41 a43 o11 o13 o33)
    x0 x1 x2 x3 x4

private def plusDetG0 (a05 a25 : ℝ) : ℝ :=
  a05 / 2 - 3 / 400 + (a25 / 2 - 13 / 625)

private def plusDetG1 (a05 a25 : ℝ) : ℝ :=
  -plusDetG0 a05 a25 / 1000 +
    (a05 / 2 - 3 / 400 - (a25 / 2 - 13 / 625))

private def plusDetG2 (a05 a25 a45 : ℝ) : ℝ :=
  -(16 / 45 : ℝ) * plusDetG0 a05 a25 +
    (28 / 9) * (a05 / 2 - 3 / 400 - (a25 / 2 - 13 / 625)) +
    (a45 / 2 - 457 / 5000)

private def plusDetG3 (a05 a25 a45 o15 : ℝ) : ℝ :=
  -(27 / 40 : ℝ) * plusDetG0 a05 a25 +
    (49 / 17) * (a05 / 2 - 3 / 400 - (a25 / 2 - 13 / 625)) +
    (27 / 25) * (a45 / 2 - 457 / 5000) + o15

private def plusDetG4 (a05 a25 a45 o15 o35 : ℝ) : ℝ :=
  -plusDetG0 a05 a25 +
    (75 / 19) * (a05 / 2 - 3 / 400 - (a25 / 2 - 13 / 625)) +
    (83 / 32) * (a45 / 2 - 457 / 5000) +
    (2 / 45) * o15 + (o35 - (25 / 24) * o15)

private def plusDetTransformedSixQuadratic
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33
      a05 a25 a45 o15 o35 o55 x0 x1 x2 x3 x4 z : ℝ) : ℝ :=
  plusDetTransformedFiveQuadratic S D s1 d1 s3 d3 a41 a43 o11 o13 o33
      x0 x1 x2 x3 x4 +
    2 * plusDetG0 a05 a25 * x0 * z +
    2 * plusDetG1 a05 a25 * x1 * z +
    2 * plusDetG2 a05 a25 a45 * x2 * z +
    2 * plusDetG3 a05 a25 a45 o15 * x3 * z +
    2 * plusDetG4 a05 a25 a45 o15 o35 * x4 * z + o55 * z ^ 2

set_option maxHeartbeats 800000 in
private theorem plusDetLowerSixQuadratic_congruence
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33
      a05 a25 a45 o15 o35 o55 x0 x1 x2 x3 x4 z : ℝ) :
    plusDetLowerSixQuadratic S D s1 d1 s3 d3 a41 a43 o11 o13 o33
        a05 a25 a45 o15 o35 o55
        (x0 - x1 / 1000 - (16 / 45) * x2 - (27 / 40) * x3 - x4)
        (x1 + (28 / 9) * x2 + (49 / 17) * x3 + (75 / 19) * x4)
        (x2 + (27 / 25) * x3 + (83 / 32) * x4)
        (x3 + (2 / 45) * x4) x4 z =
      plusDetTransformedSixQuadratic S D s1 d1 s3 d3 a41 a43 o11 o13 o33
        a05 a25 a45 o15 o35 o55 x0 x1 x2 x3 x4 z := by
  unfold plusDetLowerSixQuadratic plusDetLowerFiveQuadratic
    plusDetTransformedSixQuadratic plusDetTransformedFiveQuadratic
    plusDetFiveQuadratic plusDetT00 plusDetT01 plusDetT02 plusDetT03
    plusDetT04 plusDetT11 plusDetT12 plusDetT13 plusDetT14 plusDetT22
    plusDetT23 plusDetT24 plusDetT33 plusDetT34 plusDetT44
    plusDetG1 plusDetG2 plusDetG3 plusDetG4 plusDetG0
  ring

private def plusDetShift0 : ℝ := 7 / 100
private def plusDetShift1 : ℝ := -21 / 4
private def plusDetShift2 : ℝ := -49 / 20
private def plusDetShift3 : ℝ := -7 / 25
private def plusDetShift4 : ℝ := 15 / 8

private def plusDetH0
    (S s1 s3 a05 a25 : ℝ) : ℝ :=
  plusDetT00 * plusDetShift0 + plusDetT01 * plusDetShift1 +
    plusDetT02 S * plusDetShift2 + plusDetT03 S s1 * plusDetShift3 +
    plusDetT04 S s1 s3 * plusDetShift4 + plusDetG0 a05 a25

private def plusDetH1
    (S D s1 d1 s3 d3 a05 a25 : ℝ) : ℝ :=
  plusDetT01 * plusDetShift0 + plusDetT11 * plusDetShift1 +
    plusDetT12 S D * plusDetShift2 +
    plusDetT13 S D s1 d1 * plusDetShift3 +
    plusDetT14 S D s1 d1 s3 d3 * plusDetShift4 +
    plusDetG1 a05 a25

private def plusDetH2
    (S D s1 d1 s3 d3 a41 a43 a05 a25 a45 : ℝ) : ℝ :=
  plusDetT02 S * plusDetShift0 + plusDetT12 S D * plusDetShift1 +
    plusDetT22 S D * plusDetShift2 +
    plusDetT23 S D s1 d1 a41 * plusDetShift3 +
    plusDetT24 S D s1 d1 s3 d3 a41 a43 * plusDetShift4 +
    plusDetG2 a05 a25 a45

private def plusDetH3
    (S D s1 d1 s3 d3 a41 a43 o11 o13 a05 a25 a45 o15 : ℝ) : ℝ :=
  plusDetT03 S s1 * plusDetShift0 +
    plusDetT13 S D s1 d1 * plusDetShift1 +
    plusDetT23 S D s1 d1 a41 * plusDetShift2 +
    plusDetT33 S D s1 d1 a41 o11 * plusDetShift3 +
    plusDetT34 S D s1 d1 s3 d3 a41 a43 o11 o13 * plusDetShift4 +
    plusDetG3 a05 a25 a45 o15

private def plusDetH4
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33
      a05 a25 a45 o15 o35 : ℝ) : ℝ :=
  plusDetT04 S s1 s3 * plusDetShift0 +
    plusDetT14 S D s1 d1 s3 d3 * plusDetShift1 +
    plusDetT24 S D s1 d1 s3 d3 a41 a43 * plusDetShift2 +
    plusDetT34 S D s1 d1 s3 d3 a41 a43 o11 o13 * plusDetShift3 +
    plusDetT44 S D s1 d1 s3 d3 a41 a43 o11 o13 o33 * plusDetShift4 +
    plusDetG4 a05 a25 a45 o15 o35

private def plusDetW
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33
      a05 a25 a45 o15 o35 o55 : ℝ) : ℝ :=
  plusDetTransformedSixQuadratic S D s1 d1 s3 d3 a41 a43 o11 o13 o33
    a05 a25 a45 o15 o35 o55
    plusDetShift0 plusDetShift1 plusDetShift2 plusDetShift3 plusDetShift4 1

private abbrev plusDetS : ℝ := factorTwoIntrinsicP4PlusCrossSum
private abbrev plusDetD : ℝ := factorTwoIntrinsicP4PlusCrossDifference
private abbrev plusDetS1 : ℝ :=
  factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21
private abbrev plusDetD1 : ℝ :=
  factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21
private abbrev plusDetS3 : ℝ :=
  factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23
private abbrev plusDetD3 : ℝ :=
  factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23
private abbrev plusDetA41 : ℝ := factorTwoIntrinsicFourP45Cross41
private abbrev plusDetA43 : ℝ := factorTwoIntrinsicFourP45Cross43
private abbrev plusDetO11 : ℝ := factorTwoIntrinsicSixUnbalancedOMinus11
private abbrev plusDetO13 : ℝ := factorTwoIntrinsicSixUnbalancedOMinus13
private abbrev plusDetO33 : ℝ := factorTwoIntrinsicSixUnbalancedOMinus33
private abbrev plusDetA05 : ℝ := factorTwoIntrinsicFourP45Cross05
private abbrev plusDetA25 : ℝ := factorTwoIntrinsicFourP45Cross25
private abbrev plusDetA45 : ℝ := factorTwoIntrinsicP45Alternating
private abbrev plusDetO15 : ℝ := factorTwoIntrinsicSixUnbalancedOMinus15
private abbrev plusDetO35 : ℝ := factorTwoIntrinsicSixUnbalancedOMinus35
private abbrev plusDetO55 : ℝ := factorTwoIntrinsicSixUnbalancedOMinus55

private abbrev plusDetActualH0 : ℝ :=
  plusDetH0 plusDetS plusDetS1 plusDetS3 plusDetA05 plusDetA25

private abbrev plusDetActualH1 : ℝ :=
  plusDetH1 plusDetS plusDetD plusDetS1 plusDetD1 plusDetS3 plusDetD3
    plusDetA05 plusDetA25

private abbrev plusDetActualH2 : ℝ :=
  plusDetH2 plusDetS plusDetD plusDetS1 plusDetD1 plusDetS3 plusDetD3
    plusDetA41 plusDetA43 plusDetA05 plusDetA25 plusDetA45

private abbrev plusDetActualH3 : ℝ :=
  plusDetH3 plusDetS plusDetD plusDetS1 plusDetD1 plusDetS3 plusDetD3
    plusDetA41 plusDetA43 plusDetO11 plusDetO13
    plusDetA05 plusDetA25 plusDetA45 plusDetO15

private abbrev plusDetActualH4 : ℝ :=
  plusDetH4 plusDetS plusDetD plusDetS1 plusDetD1 plusDetS3 plusDetD3
    plusDetA41 plusDetA43 plusDetO11 plusDetO13 plusDetO33
    plusDetA05 plusDetA25 plusDetA45 plusDetO15 plusDetO35

private abbrev plusDetActualW : ℝ :=
  plusDetW plusDetS plusDetD plusDetS1 plusDetD1 plusDetS3 plusDetD3
    plusDetA41 plusDetA43 plusDetO11 plusDetO13 plusDetO33
    plusDetA05 plusDetA25 plusDetA45 plusDetO15 plusDetO35 plusDetO55

private theorem plusDetActualH0_bounds :
    (-11 / 5000 : ℝ) < plusDetActualH0 ∧
      plusDetActualH0 < (49 / 20000 : ℝ) := by
  have hS := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds.1
  have hSU := factorTwoIntrinsicP4PlusCrossSum_bounds.2
  have hJ := factorTwoIntrinsicAlternatingSharpBounds
  unfold FactorTwoIntrinsicAlternatingSharpBounds at hJ
  have h05 := factorTwoIntrinsicFourP45Cross05_bounds
  have h25 := factorTwoIntrinsicFourP45Cross25_bounds
  unfold plusDetActualH0 plusDetH0 plusDetS plusDetS1 plusDetS3
    plusDetA05 plusDetA25 plusDetT00 plusDetT01 plusDetT02 plusDetT03
    plusDetT04 plusDetG0 plusDetShift0 plusDetShift1 plusDetShift2 plusDetShift3
    plusDetShift4
  constructor <;> linarith

private theorem plusDetActualH1_bounds :
    (-9 / 5000 : ℝ) < plusDetActualH1 ∧
      plusDetActualH1 < (21 / 10000 : ℝ) := by
  have hS := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds.1
  have hSU := factorTwoIntrinsicP4PlusCrossSum_bounds.2
  have hD := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds.2
  have hDU := factorTwoIntrinsicP4PlusCrossDifference_bounds.2
  have hJ := factorTwoIntrinsicAlternatingSharpBounds
  unfold FactorTwoIntrinsicAlternatingSharpBounds at hJ
  have h05 := factorTwoIntrinsicFourP45Cross05_bounds
  have h25 := factorTwoIntrinsicFourP45Cross25_bounds
  unfold plusDetActualH1 plusDetH1 plusDetS plusDetD plusDetS1 plusDetD1
    plusDetS3 plusDetD3 plusDetA05 plusDetA25 plusDetT01 plusDetT11
    plusDetT12 plusDetT13 plusDetT14 plusDetG1 plusDetG0
    plusDetShift0 plusDetShift1
    plusDetShift2 plusDetShift3 plusDetShift4
  constructor <;> linarith

private theorem plusDetActualH0_abs_lt :
    |plusDetActualH0| < (1 / 400 : ℝ) := by
  rw [abs_lt]
  rcases plusDetActualH0_bounds with ⟨hL, hU⟩
  constructor <;> linarith

private theorem plusDetActualH1_abs_lt :
    |plusDetActualH1| < (1 / 450 : ℝ) := by
  rw [abs_lt]
  rcases plusDetActualH1_bounds with ⟨hL, hU⟩
  constructor <;> linarith

/-- The genuinely correlated analytic frontier left by the six-dimensional
completion.  Each quantity is formed before any estimate is taken. -/
def PlusP5BorderCombinedBounds : Prop :=
  |plusDetActualH2| < (1 / 625 : ℝ) ∧
    |plusDetActualH3| < (1 / 625 : ℝ) ∧
    |plusDetActualH4| < (1 / 625 : ℝ) ∧
    (63 / 1000 : ℝ) < plusDetActualW

/-! ## The six-dimensional weighted SOS -/

private def plusDetAbsoluteComparison
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  (27 / 50 : ℝ) * x0 ^ 2 + (63 / 10000 : ℝ) * x1 ^ 2 +
    (397 / 50000 : ℝ) * x2 ^ 2 + (12 / 125 : ℝ) * x3 ^ 2 +
    (149 / 50000 : ℝ) * x4 ^ 2 -
    2 * (41 / 500000 : ℝ) * |x0 * x1| -
    2 * (51 / 100000 : ℝ) * |x0 * x2| -
    2 * (237 / 500000 : ℝ) * |x0 * x3| -
    2 * (5891 / 1000000 : ℝ) * |x0 * x4| -
    2 * (79 / 500000 : ℝ) * |x1 * x2| -
    2 * (41 / 250000 : ℝ) * |x1 * x3| -
    2 * (107 / 250000 : ℝ) * |x1 * x4| -
    2 * (1893 / 1000000 : ℝ) * |x2 * x3| -
    2 * (1813 / 500000 : ℝ) * |x2 * x4| -
    2 * (897 / 100000 : ℝ) * |x3 * x4|

private def plusDetReserve0 : ℝ := 63371 / 500000
private def plusDetReserve1 : ℝ := 10613 / 10000000
private def plusDetReserve2 : ℝ := 173 / 2000000
private def plusDetReserve3 : ℝ := 3973 / 2625000
private def plusDetReserve4 : ℝ := 26049 / 200000000

private def plusDetOldPairSquares
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  ((41 / 500000 : ℝ) / ((3 / 200) * (1 / 10))) *
      ((1 / 10 : ℝ) * |x0| - (3 / 200 : ℝ) * |x1|) ^ 2 +
    ((51 / 100000 : ℝ) / ((3 / 200) * (49 / 100))) *
      ((49 / 100 : ℝ) * |x0| - (3 / 200 : ℝ) * |x2|) ^ 2 +
    ((237 / 500000 : ℝ) / ((3 / 200) * (21 / 200))) *
      ((21 / 200 : ℝ) * |x0| - (3 / 200 : ℝ) * |x3|) ^ 2 +
    ((5891 / 1000000 : ℝ) / (3 / 200)) *
      (|x0| - (3 / 200 : ℝ) * |x4|) ^ 2 +
    ((79 / 500000 : ℝ) / ((1 / 10) * (49 / 100))) *
      ((49 / 100 : ℝ) * |x1| - (1 / 10 : ℝ) * |x2|) ^ 2 +
    ((41 / 250000 : ℝ) / ((1 / 10) * (21 / 200))) *
      ((21 / 200 : ℝ) * |x1| - (1 / 10 : ℝ) * |x3|) ^ 2 +
    ((107 / 250000 : ℝ) / (1 / 10)) *
      (|x1| - (1 / 10 : ℝ) * |x4|) ^ 2 +
    ((1893 / 1000000 : ℝ) / ((49 / 100) * (21 / 200))) *
      ((21 / 200 : ℝ) * |x2| - (49 / 100 : ℝ) * |x3|) ^ 2 +
    ((1813 / 500000 : ℝ) / (49 / 100)) *
      (|x2| - (49 / 100 : ℝ) * |x4|) ^ 2 +
    ((897 / 100000 : ℝ) / (21 / 200)) *
      (|x3| - (21 / 200 : ℝ) * |x4|) ^ 2

private def plusDetAbsoluteComparisonSOS
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  plusDetReserve0 * x0 ^ 2 + plusDetReserve1 * x1 ^ 2 +
    plusDetReserve2 * x2 ^ 2 + plusDetReserve3 * x3 ^ 2 +
    plusDetReserve4 * x4 ^ 2 + plusDetOldPairSquares x0 x1 x2 x3 x4

private theorem plusDetAbsoluteComparison_eq_sos
    (x0 x1 x2 x3 x4 : ℝ) :
    plusDetAbsoluteComparison x0 x1 x2 x3 x4 =
      plusDetAbsoluteComparisonSOS x0 x1 x2 x3 x4 := by
  unfold plusDetAbsoluteComparison plusDetAbsoluteComparisonSOS
    plusDetOldPairSquares plusDetReserve0 plusDetReserve1 plusDetReserve2
    plusDetReserve3 plusDetReserve4
  simp only [abs_mul]
  ring_nf
  simp only [sq_abs]
  ring

private def plusDetBorderRadius0 : ℝ := 1 / 400
private def plusDetBorderRadius1 : ℝ := 1 / 450
private def plusDetBorderRadius2 : ℝ := 1 / 625
private def plusDetBorderRadius3 : ℝ := 1 / 625
private def plusDetBorderRadius4 : ℝ := 1 / 625

private def plusDetBorderLeftover : ℝ :=
  63 / 1000 - plusDetBorderRadius0 ^ 2 / plusDetReserve0 -
    plusDetBorderRadius1 ^ 2 / plusDetReserve1 -
    plusDetBorderRadius2 ^ 2 / plusDetReserve2 -
    plusDetBorderRadius3 ^ 2 / plusDetReserve3 -
    plusDetBorderRadius4 ^ 2 / plusDetReserve4

private theorem plusDetBorderLeftover_pos : 0 < plusDetBorderLeftover := by
  norm_num [plusDetBorderLeftover, plusDetBorderRadius0,
    plusDetBorderRadius1, plusDetBorderRadius2, plusDetBorderRadius3,
    plusDetBorderRadius4, plusDetReserve0, plusDetReserve1,
    plusDetReserve2, plusDetReserve3, plusDetReserve4]

private def plusDetBorderComparison
    (x0 x1 x2 x3 x4 z : ℝ) : ℝ :=
  plusDetAbsoluteComparison x0 x1 x2 x3 x4 + (63 / 1000 : ℝ) * z ^ 2 -
    2 * plusDetBorderRadius0 * |x0 * z| -
    2 * plusDetBorderRadius1 * |x1 * z| -
    2 * plusDetBorderRadius2 * |x2 * z| -
    2 * plusDetBorderRadius3 * |x3 * z| -
    2 * plusDetBorderRadius4 * |x4 * z|

private def plusDetBorderSOS
    (x0 x1 x2 x3 x4 z : ℝ) : ℝ :=
  plusDetOldPairSquares x0 x1 x2 x3 x4 +
    plusDetBorderLeftover * z ^ 2 +
    plusDetReserve0 *
      (|x0| - plusDetBorderRadius0 / plusDetReserve0 * |z|) ^ 2 +
    plusDetReserve1 *
      (|x1| - plusDetBorderRadius1 / plusDetReserve1 * |z|) ^ 2 +
    plusDetReserve2 *
      (|x2| - plusDetBorderRadius2 / plusDetReserve2 * |z|) ^ 2 +
    plusDetReserve3 *
      (|x3| - plusDetBorderRadius3 / plusDetReserve3 * |z|) ^ 2 +
    plusDetReserve4 *
      (|x4| - plusDetBorderRadius4 / plusDetReserve4 * |z|) ^ 2

private theorem plusDetBorderComparison_eq_sos
    (x0 x1 x2 x3 x4 z : ℝ) :
    plusDetBorderComparison x0 x1 x2 x3 x4 z =
      plusDetBorderSOS x0 x1 x2 x3 x4 z := by
  unfold plusDetBorderComparison
  rw [show plusDetAbsoluteComparison x0 x1 x2 x3 x4 =
      plusDetAbsoluteComparisonSOS x0 x1 x2 x3 x4 by
    exact plusDetAbsoluteComparison_eq_sos x0 x1 x2 x3 x4]
  unfold plusDetBorderSOS plusDetAbsoluteComparisonSOS
    plusDetBorderLeftover plusDetBorderRadius0 plusDetBorderRadius1
    plusDetBorderRadius2 plusDetBorderRadius3 plusDetBorderRadius4
    plusDetReserve0 plusDetReserve1 plusDetReserve2 plusDetReserve3
    plusDetReserve4
  simp only [abs_mul]
  ring_nf
  simp only [sq_abs]
  ring

private theorem plusDetOldPairSquares_nonneg
    (x0 x1 x2 x3 x4 : ℝ) :
    0 ≤ plusDetOldPairSquares x0 x1 x2 x3 x4 := by
  unfold plusDetOldPairSquares
  positivity

private theorem plusDetBorderComparison_pos_of_ne
    (x0 x1 x2 x3 x4 z : ℝ) (hz : z ≠ 0) :
    0 < plusDetBorderComparison x0 x1 x2 x3 x4 z := by
  rw [plusDetBorderComparison_eq_sos]
  unfold plusDetBorderSOS
  have hzsq : 0 < z ^ 2 := sq_pos_of_ne_zero hz
  have hleft : 0 < plusDetBorderLeftover * z ^ 2 :=
    mul_pos plusDetBorderLeftover_pos hzsq
  have hpairs := plusDetOldPairSquares_nonneg x0 x1 x2 x3 x4
  have h0 : 0 ≤ plusDetReserve0 *
      (|x0| - plusDetBorderRadius0 / plusDetReserve0 * |z|) ^ 2 := by
    exact mul_nonneg (by norm_num [plusDetReserve0]) (sq_nonneg _)
  have h1 : 0 ≤ plusDetReserve1 *
      (|x1| - plusDetBorderRadius1 / plusDetReserve1 * |z|) ^ 2 := by
    exact mul_nonneg (by norm_num [plusDetReserve1]) (sq_nonneg _)
  have h2 : 0 ≤ plusDetReserve2 *
      (|x2| - plusDetBorderRadius2 / plusDetReserve2 * |z|) ^ 2 := by
    exact mul_nonneg (by norm_num [plusDetReserve2]) (sq_nonneg _)
  have h3 : 0 ≤ plusDetReserve3 *
      (|x3| - plusDetBorderRadius3 / plusDetReserve3 * |z|) ^ 2 := by
    exact mul_nonneg (by norm_num [plusDetReserve3]) (sq_nonneg _)
  have h4 : 0 ≤ plusDetReserve4 *
      (|x4| - plusDetBorderRadius4 / plusDetReserve4 * |z|) ^ 2 := by
    exact mul_nonneg (by norm_num [plusDetReserve4]) (sq_nonneg _)
  linarith

private theorem plusDet_cross_lower_of_abs_le
    {a radius x z : ℝ} (h : |a| ≤ radius) :
    -2 * radius * |x * z| ≤ 2 * a * x * z := by
  have hmul : |a * x * z| ≤ radius * |x * z| := by
    calc
      |a * x * z| = |a| * (|x| * |z|) := by simp only [abs_mul, mul_assoc]
      _ ≤ radius * (|x| * |z|) :=
        mul_le_mul_of_nonneg_right h
          (mul_nonneg (abs_nonneg x) (abs_nonneg z))
      _ = radius * |x * z| := by rw [abs_mul]
  have hneg : -|a * x * z| ≤ a * x * z := neg_abs_le _
  nlinarith

private theorem plusDetBorderComparison_le
    (M h0 h1 h2 h3 h4 W x0 x1 x2 x3 x4 z : ℝ)
    (hM : plusDetAbsoluteComparison x0 x1 x2 x3 x4 ≤ M)
    (hh0 : |h0| ≤ plusDetBorderRadius0)
    (hh1 : |h1| ≤ plusDetBorderRadius1)
    (hh2 : |h2| ≤ plusDetBorderRadius2)
    (hh3 : |h3| ≤ plusDetBorderRadius3)
    (hh4 : |h4| ≤ plusDetBorderRadius4)
    (hW : (63 / 1000 : ℝ) ≤ W) :
    plusDetBorderComparison x0 x1 x2 x3 x4 z ≤
      M + 2 * h0 * x0 * z + 2 * h1 * x1 * z + 2 * h2 * x2 * z +
        2 * h3 * x3 * z + 2 * h4 * x4 * z + W * z ^ 2 := by
  have hc0 := plusDet_cross_lower_of_abs_le (x := x0) (z := z) hh0
  have hc1 := plusDet_cross_lower_of_abs_le (x := x1) (z := z) hh1
  have hc2 := plusDet_cross_lower_of_abs_le (x := x2) (z := z) hh2
  have hc3 := plusDet_cross_lower_of_abs_le (x := x3) (z := z) hh3
  have hc4 := plusDet_cross_lower_of_abs_le (x := x4) (z := z) hh4
  have hd := mul_le_mul_of_nonneg_right hW (sq_nonneg z)
  unfold plusDetBorderComparison
  linarith

set_option maxHeartbeats 800000 in
private theorem plusDetTransformedSixQuadratic_border_congruence
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33
      a05 a25 a45 o15 o35 o55 x0 x1 x2 x3 x4 z : ℝ) :
    plusDetTransformedSixQuadratic S D s1 d1 s3 d3 a41 a43 o11 o13 o33
        a05 a25 a45 o15 o35 o55
        (x0 + plusDetShift0 * z) (x1 + plusDetShift1 * z)
        (x2 + plusDetShift2 * z) (x3 + plusDetShift3 * z)
        (x4 + plusDetShift4 * z) z =
      plusDetTransformedFiveQuadratic S D s1 d1 s3 d3 a41 a43 o11 o13 o33
          x0 x1 x2 x3 x4 +
        2 * plusDetH0 S s1 s3 a05 a25 * x0 * z +
        2 * plusDetH1 S D s1 d1 s3 d3 a05 a25 * x1 * z +
        2 * plusDetH2 S D s1 d1 s3 d3 a41 a43 a05 a25 a45 * x2 * z +
        2 * plusDetH3 S D s1 d1 s3 d3 a41 a43 o11 o13
          a05 a25 a45 o15 * x3 * z +
        2 * plusDetH4 S D s1 d1 s3 d3 a41 a43 o11 o13 o33
          a05 a25 a45 o15 o35 * x4 * z +
        plusDetW S D s1 d1 s3 d3 a41 a43 o11 o13 o33
          a05 a25 a45 o15 o35 o55 * z ^ 2 := by
  unfold plusDetH0 plusDetH1 plusDetH2 plusDetH3 plusDetH4 plusDetW
    plusDetShift0 plusDetShift1 plusDetShift2 plusDetShift3 plusDetShift4
  unfold plusDetTransformedSixQuadratic plusDetTransformedFiveQuadratic
    plusDetFiveQuadratic
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
