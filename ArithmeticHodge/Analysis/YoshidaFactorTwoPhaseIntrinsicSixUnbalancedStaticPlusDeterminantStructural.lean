import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedAlternatingModelsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural

noncomputable section

open MeasureTheory Real Set
open ThreeByThreeRankOneSchur
open YoshidaConstantBounds
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations
open YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedAlternatingModelsStructural
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

/-! ## Combined alternating profiles

The five border residuals do not tolerate entrywise alternating boxes.  We
therefore form each full polynomial correlation first.  The following
six-parameter identity is the common structural core: it expands one actual
even/odd profile pairing, identifies its single endpoint correlation
polynomial, and only then applies the sharp kernel decomposition. -/

private def plusDetAlternatingEvenProfile
    (c0 c2 c4 : ℝ) : ℝ → ℝ :=
  c0 • centeredEvenP0 + c2 • centeredEvenP2 + c4 • factorTwoCenteredP4

private def plusDetAlternatingOddProfile
    (d1 d3 d5 : ℝ) : ℝ → ℝ :=
  d1 • centeredP1 + d3 • centeredP3 + d5 • factorTwoCenteredP5

private theorem continuous_centeredEvenP0_plusDet :
    Continuous centeredEvenP0 := by
  unfold centeredEvenP0
  fun_prop

private theorem continuous_centeredEvenP2_plusDet :
    Continuous centeredEvenP2 := by
  unfold centeredEvenP2
  fun_prop

private theorem continuous_centeredP1_plusDet :
    Continuous centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem continuous_centeredP3_plusDet :
    Continuous centeredP3 := by
  unfold centeredP3
  fun_prop

private theorem continuous_plusDetAlternatingEvenProfile
    (c0 c2 c4 : ℝ) :
    Continuous (plusDetAlternatingEvenProfile c0 c2 c4) := by
  unfold plusDetAlternatingEvenProfile
  exact ((continuous_centeredEvenP0_plusDet.const_smul c0).add
    (continuous_centeredEvenP2_plusDet.const_smul c2)).add
      (continuous_factorTwoCenteredP4.const_smul c4)

private theorem continuous_plusDetAlternatingOddProfile
    (d1 d3 d5 : ℝ) :
    Continuous (plusDetAlternatingOddProfile d1 d3 d5) := by
  unfold plusDetAlternatingOddProfile
  exact ((continuous_centeredP1_plusDet.const_smul d1).add
    (continuous_centeredP3_plusDet.const_smul d3)).add
      (continuous_factorTwoCenteredP5.const_smul d5)

private def plusDetAlternatingCrossDifference
    (e o : ℝ → ℝ) (t : ℝ) : ℝ :=
  factorTwoCenteredCrossCorrelation o e t -
    factorTwoCenteredCrossCorrelation e o t

private def plusDetAlternatingQ
    (c0 c2 c4 d1 d3 d5 t : ℝ) : ℝ :=
  c0 * d1 +
    c2 * d1 * (-1 + t / 2 + t ^ 2 / 4) +
    c0 * d3 * (1 - (5 / 2 : ℝ) * t + (5 / 4 : ℝ) * t ^ 2) +
    c2 * d3 *
      (1 - t - t ^ 2 / 2 + t ^ 3 / 4 + t ^ 4 / 8) +
    c4 * d1 * alternatingQ41 t + c4 * d3 * alternatingQ43 t +
    c0 * d5 * alternatingQ05 t + c2 * d5 * alternatingQ25 t +
    c4 * d5 * alternatingQ45 t

private theorem plusDetAlternatingCoupling_evenProfile
    (c0 c2 c4 : ℝ) (o : ℝ → ℝ) (ho : Continuous o) :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile c0 c2 c4) o =
      c0 * factorTwoCenteredAlternatingCoupling centeredEvenP0 o +
        c2 * factorTwoCenteredAlternatingCoupling centeredEvenP2 o +
        c4 * factorTwoCenteredAlternatingCoupling factorTwoCenteredP4 o := by
  have h0 : Continuous (c0 • centeredEvenP0) :=
    continuous_centeredEvenP0_plusDet.const_smul c0
  have h2 : Continuous (c2 • centeredEvenP2) :=
    continuous_centeredEvenP2_plusDet.const_smul c2
  have h4 : Continuous (c4 • factorTwoCenteredP4) :=
    continuous_factorTwoCenteredP4.const_smul c4
  unfold plusDetAlternatingEvenProfile
  rw [factorTwoCenteredAlternatingCoupling_add_left
      (c0 • centeredEvenP0 + c2 • centeredEvenP2)
      (c4 • factorTwoCenteredP4) o (h0.add h2) h4 ho,
    factorTwoCenteredAlternatingCoupling_add_left
      (c0 • centeredEvenP0) (c2 • centeredEvenP2) o h0 h2 ho,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_left]

private theorem plusDetAlternatingCoupling_oddProfile
    (e : ℝ → ℝ) (he : Continuous e) (d1 d3 d5 : ℝ) :
    factorTwoCenteredAlternatingCoupling e
        (plusDetAlternatingOddProfile d1 d3 d5) =
      d1 * factorTwoCenteredAlternatingCoupling e centeredP1 +
        d3 * factorTwoCenteredAlternatingCoupling e centeredP3 +
        d5 * factorTwoCenteredAlternatingCoupling e factorTwoCenteredP5 := by
  have h1 : Continuous (d1 • centeredP1) :=
    continuous_centeredP1_plusDet.const_smul d1
  have h3 : Continuous (d3 • centeredP3) :=
    continuous_centeredP3_plusDet.const_smul d3
  have h5 : Continuous (d5 • factorTwoCenteredP5) :=
    continuous_factorTwoCenteredP5.const_smul d5
  unfold plusDetAlternatingOddProfile
  rw [factorTwoCenteredAlternatingCoupling_add_right e
      (d1 • centeredP1 + d3 • centeredP3)
      (d5 • factorTwoCenteredP5) he (h1.add h3) h5,
    factorTwoCenteredAlternatingCoupling_add_right e
      (d1 • centeredP1) (d3 • centeredP3) he h1 h3,
    factorTwoCenteredAlternatingCoupling_smul_right,
    factorTwoCenteredAlternatingCoupling_smul_right,
    factorTwoCenteredAlternatingCoupling_smul_right]

private theorem plusDetAlternatingCrossDifference_evenProfile
    (c0 c2 c4 : ℝ) (o : ℝ → ℝ) (ho : Continuous o) (t : ℝ) :
    plusDetAlternatingCrossDifference
        (plusDetAlternatingEvenProfile c0 c2 c4) o t =
      c0 * plusDetAlternatingCrossDifference centeredEvenP0 o t +
        c2 * plusDetAlternatingCrossDifference centeredEvenP2 o t +
        c4 * plusDetAlternatingCrossDifference factorTwoCenteredP4 o t := by
  have h0 : Continuous (c0 • centeredEvenP0) :=
    continuous_centeredEvenP0_plusDet.const_smul c0
  have h2 : Continuous (c2 • centeredEvenP2) :=
    continuous_centeredEvenP2_plusDet.const_smul c2
  have h4 : Continuous (c4 • factorTwoCenteredP4) :=
    continuous_factorTwoCenteredP4.const_smul c4
  unfold plusDetAlternatingCrossDifference plusDetAlternatingEvenProfile
  rw [factorTwoCenteredCrossCorrelation_add_right o
      (c0 • centeredEvenP0 + c2 • centeredEvenP2)
      (c4 • factorTwoCenteredP4) ho (h0.add h2) h4 t,
    factorTwoCenteredCrossCorrelation_add_right o
      (c0 • centeredEvenP0) (c2 • centeredEvenP2) ho h0 h2 t,
    factorTwoCenteredCrossCorrelation_add_left
      (c0 • centeredEvenP0 + c2 • centeredEvenP2)
      (c4 • factorTwoCenteredP4) o (h0.add h2) h4 ho t,
    factorTwoCenteredCrossCorrelation_add_left
      (c0 • centeredEvenP0) (c2 • centeredEvenP2) o h0 h2 ho t]
  repeat rw [factorTwoCenteredCrossCorrelation_smul_left,
    factorTwoCenteredCrossCorrelation_smul_right]
  ring

private theorem plusDetAlternatingCrossDifference_oddProfile
    (e : ℝ → ℝ) (he : Continuous e) (d1 d3 d5 t : ℝ) :
    plusDetAlternatingCrossDifference e
        (plusDetAlternatingOddProfile d1 d3 d5) t =
      d1 * plusDetAlternatingCrossDifference e centeredP1 t +
        d3 * plusDetAlternatingCrossDifference e centeredP3 t +
        d5 * plusDetAlternatingCrossDifference e factorTwoCenteredP5 t := by
  have h1 : Continuous (d1 • centeredP1) :=
    continuous_centeredP1_plusDet.const_smul d1
  have h3 : Continuous (d3 • centeredP3) :=
    continuous_centeredP3_plusDet.const_smul d3
  have h5 : Continuous (d5 • factorTwoCenteredP5) :=
    continuous_factorTwoCenteredP5.const_smul d5
  unfold plusDetAlternatingCrossDifference plusDetAlternatingOddProfile
  rw [factorTwoCenteredCrossCorrelation_add_left
      (d1 • centeredP1 + d3 • centeredP3)
      (d5 • factorTwoCenteredP5) e (h1.add h3) h5 he t,
    factorTwoCenteredCrossCorrelation_add_left
      (d1 • centeredP1) (d3 • centeredP3) e h1 h3 he t,
    factorTwoCenteredCrossCorrelation_add_right e
      (d1 • centeredP1 + d3 • centeredP3)
      (d5 • factorTwoCenteredP5) he (h1.add h3) h5 t,
    factorTwoCenteredCrossCorrelation_add_right e
      (d1 • centeredP1) (d3 • centeredP3) he h1 h3 t]
  repeat rw [factorTwoCenteredCrossCorrelation_smul_left,
    factorTwoCenteredCrossCorrelation_smul_right]
  ring

private theorem plusDetAlternatingCrossDifference_profile
    (c0 c2 c4 d1 d3 d5 t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    plusDetAlternatingCrossDifference
        (plusDetAlternatingEvenProfile c0 c2 c4)
        (plusDetAlternatingOddProfile d1 d3 d5) t =
      intrinsicAlternatingCorrelation
        (plusDetAlternatingQ c0 c2 c4 d1 d3 d5) t := by
  rw [plusDetAlternatingCrossDifference_evenProfile c0 c2 c4
      (plusDetAlternatingOddProfile d1 d3 d5)
      (continuous_plusDetAlternatingOddProfile d1 d3 d5) t,
    plusDetAlternatingCrossDifference_oddProfile centeredEvenP0
      (by unfold centeredEvenP0; fun_prop) d1 d3 d5 t,
    plusDetAlternatingCrossDifference_oddProfile centeredEvenP2
      (by unfold centeredEvenP2; fun_prop) d1 d3 d5 t,
    plusDetAlternatingCrossDifference_oddProfile factorTwoCenteredP4
      continuous_factorTwoCenteredP4 d1 d3 d5 t]
  have h01 := factorTwoCenteredCrossDifference_p0_p1 t
  have h03 := factorTwoCenteredCrossDifference_p0_p3 t
  have h21 := factorTwoCenteredCrossDifference_p2_p1 t
  have h23 := factorTwoCenteredCrossDifference_p2_p3 t
  have h41 := crossDifference_p4_p1 t ht
  have h43 := crossDifference_p4_p3 t ht
  have h05 := crossDifference_p0_p5 t ht
  have h25 := crossDifference_p2_p5 t ht
  have h45 := crossDifference_p4_p5 t ht
  unfold plusDetAlternatingCrossDifference
  rw [h01, h03, h21, h23, h41, h43, h05, h25, h45]
  unfold plusDetAlternatingQ intrinsicAlternatingCorrelation
  ring

private theorem plusDetAlternatingCoupling_profile_expansion
    (c0 c2 c4 d1 d3 d5 : ℝ) :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile c0 c2 c4)
        (plusDetAlternatingOddProfile d1 d3 d5) =
      c0 * d1 * factorTwoIntrinsicAlternating01 +
        c2 * d1 * factorTwoIntrinsicAlternating21 +
        c0 * d3 * factorTwoIntrinsicAlternating03 +
        c2 * d3 * factorTwoIntrinsicAlternating23 +
        c4 * d1 * factorTwoIntrinsicFourP45Cross41 +
        c4 * d3 * factorTwoIntrinsicFourP45Cross43 +
        c0 * d5 * factorTwoIntrinsicFourP45Cross05 +
        c2 * d5 * factorTwoIntrinsicFourP45Cross25 +
        c4 * d5 * factorTwoIntrinsicP45Alternating := by
  rw [plusDetAlternatingCoupling_evenProfile c0 c2 c4
      (plusDetAlternatingOddProfile d1 d3 d5)
      (continuous_plusDetAlternatingOddProfile d1 d3 d5),
    plusDetAlternatingCoupling_oddProfile centeredEvenP0
      (by unfold centeredEvenP0; fun_prop) d1 d3 d5,
    plusDetAlternatingCoupling_oddProfile centeredEvenP2
      (by unfold centeredEvenP2; fun_prop) d1 d3 d5,
    plusDetAlternatingCoupling_oddProfile factorTwoCenteredP4
      continuous_factorTwoCenteredP4 d1 d3 d5]
  unfold factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating21
    factorTwoIntrinsicAlternating03 factorTwoIntrinsicAlternating23
    factorTwoIntrinsicFourP45Cross41 factorTwoIntrinsicFourP45Cross43
    factorTwoIntrinsicFourP45Cross05 factorTwoIntrinsicFourP45Cross25
    factorTwoIntrinsicP45Alternating
  ring

private theorem plusDetAlternatingCoupling_profile_eq_sharpModel
    (c0 c2 c4 d1 d3 d5 : ℝ) :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile c0 c2 c4)
        (plusDetAlternatingOddProfile d1 d3 d5) =
      intrinsicAlternatingSharpRegularError
          (plusDetAlternatingQ c0 c2 c4 d1 d3 d5) +
        intrinsicAlternatingSharpArchModel
          (plusDetAlternatingQ c0 c2 c4 d1 d3 d5) -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation
            (plusDetAlternatingQ c0 c2 c4 d1 d3 d5)
              (factorTwoPrimeShift / yoshidaEndpointA) := by
  calc
    _ = intrinsicAlternatingRegularError
          (plusDetAlternatingQ c0 c2 c4 d1 d3 d5) +
        intrinsicAlternatingArchModel
          (plusDetAlternatingQ c0 c2 c4 d1 d3 d5) -
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation
            (plusDetAlternatingQ c0 c2 c4 d1 d3 d5)
              (factorTwoPrimeShift / yoshidaEndpointA) :=
      factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
        (plusDetAlternatingEvenProfile c0 c2 c4)
        (plusDetAlternatingOddProfile d1 d3 d5)
        (plusDetAlternatingQ c0 c2 c4 d1 d3 d5)
        (by
          unfold plusDetAlternatingQ alternatingQ41 alternatingQ43
            alternatingQ05 alternatingQ25 alternatingQ45
          fun_prop)
        (plusDetAlternatingCrossDifference_profile c0 c2 c4 d1 d3 d5)
    _ = _ := by rw [intrinsicAlternatingSharp_decomposition]

private def plusDetAlternatingQH2 : ℝ → ℝ :=
  plusDetAlternatingQ (124 / 45) (-52 / 15) 1
    (-10319 / 4800) (15 / 8) 1

private def plusDetAlternatingQH3 : ℝ → ℝ := fun t ↦
  plusDetAlternatingQ (1501 / 680) (-2419 / 680) (27 / 25)
      (-10319 / 4800) (15 / 8) 1 t +
    plusDetAlternatingQ (-81600701 / 11628000)
      (21466553 / 3876000) (337741 / 160000) 1 0 0 t

private def plusDetAlternatingQH4 : ℝ → ℝ := fun t ↦
  plusDetAlternatingQ (56 / 19) (-94 / 19) (83 / 32)
      (-10319 / 4800) (15 / 8) 1 t +
    plusDetAlternatingQ (-81600701 / 11628000)
      (21466553 / 3876000) (337741 / 160000) (-359 / 360) 1 0 t

private def plusDetAlternatingQW : ℝ → ℝ :=
  plusDetAlternatingQ (-81600701 / 11628000)
    (21466553 / 3876000) (337741 / 160000)
    (-10319 / 4800) (15 / 8) 1

/-- The positive Bernstein part of the complete `W` alternating profile. -/
private def plusDetAlternatingQWPositive (t : ℝ) : ℝ :=
  (3339755746409 / 131328000000 : ℝ) * (1 - t / 2) ^ 8 +
    (1681489994323 / 6976800000) * (t / 2) * (1 - t / 2) ^ 7 +
    (812962228089071 / 1116288000000) * (t / 2) ^ 2 * (1 - t / 2) ^ 6 +
    (1364572417050373 / 1116288000000) * (t / 2) ^ 3 * (1 - t / 2) ^ 5 +
    (404364394466447 / 279072000000) * (t / 2) ^ 4 * (1 - t / 2) ^ 4 +
    (636598716513713 / 558144000000) * (t / 2) ^ 5 * (1 - t / 2) ^ 3 +
    (437549057539853 / 1116288000000) * (t / 2) ^ 6 * (1 - t / 2) ^ 2 +
    (3166000829 / 6912000000) * (t / 2) ^ 8

/-- The sole negative Bernstein term of the complete `W` alternating
profile, recorded with positive sign. -/
private def plusDetAlternatingQWNegative (t : ℝ) : ℝ :=
  (42929072419607 / 1116288000000 : ℝ) *
    (t / 2) ^ 7 * (1 - t / 2)

private def plusDetAlternatingSharpModel (q : ℝ → ℝ) : ℝ :=
  intrinsicAlternatingSharpRegularError q +
    intrinsicAlternatingSharpArchModel q -
    (Real.log 3 / Real.sqrt 3) *
      intrinsicAlternatingCorrelation q
        (factorTwoPrimeShift / yoshidaEndpointA)

private theorem intrinsicAlternatingRegularError_zero_plusDet :
    intrinsicAlternatingRegularError (fun _ : ℝ ↦ 0) = 0 := by
  unfold intrinsicAlternatingRegularError intrinsicAlternatingCorrelation
  simp

private theorem intrinsicAlternatingArchModel_zero_plusDet :
    intrinsicAlternatingArchModel (fun _ : ℝ ↦ 0) = 0 := by
  unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
  simp

private theorem intrinsicAlternatingRegularError_neg_plusDet
    (q : ℝ → ℝ) (hq : Continuous q) :
    intrinsicAlternatingRegularError (-q) =
      -intrinsicAlternatingRegularError q := by
  have h := intrinsicAlternatingRegularError_sub
    (fun _ : ℝ ↦ 0) q continuous_const hq
  rw [show (fun _ : ℝ ↦ 0) - q = -q by
      funext t
      simp,
    intrinsicAlternatingRegularError_zero_plusDet] at h
  linarith

private theorem intrinsicAlternatingArchModel_neg_plusDet
    (q : ℝ → ℝ) (hq : Continuous q) :
    intrinsicAlternatingArchModel (-q) =
      -intrinsicAlternatingArchModel q := by
  have h := intrinsicAlternatingArchModel_sub
    (fun _ : ℝ ↦ 0) q continuous_const hq
  rw [show (fun _ : ℝ ↦ 0) - q = -q by
      funext t
      simp,
    intrinsicAlternatingArchModel_zero_plusDet] at h
  linarith

private theorem intrinsicAlternatingRegularError_add_plusDet
    (q r : ℝ → ℝ) (hq : Continuous q) (hr : Continuous r) :
    intrinsicAlternatingRegularError (q + r) =
      intrinsicAlternatingRegularError q +
        intrinsicAlternatingRegularError r := by
  have h := intrinsicAlternatingRegularError_sub q (-r) hq hr.neg
  rw [show q - (-r) = q + r by
      funext t
      simp,
    intrinsicAlternatingRegularError_neg_plusDet r hr] at h
  linarith

private theorem intrinsicAlternatingArchModel_add_plusDet
    (q r : ℝ → ℝ) (hq : Continuous q) (hr : Continuous r) :
    intrinsicAlternatingArchModel (q + r) =
      intrinsicAlternatingArchModel q + intrinsicAlternatingArchModel r := by
  have h := intrinsicAlternatingArchModel_sub q (-r) hq hr.neg
  rw [show q - (-r) = q + r by
      funext t
      simp,
    intrinsicAlternatingArchModel_neg_plusDet r hr] at h
  linarith

private theorem plusDetAlternatingSharpModel_add
    (q r : ℝ → ℝ) (hq : Continuous q) (hr : Continuous r) :
    plusDetAlternatingSharpModel (q + r) =
      plusDetAlternatingSharpModel q + plusDetAlternatingSharpModel r := by
  have hreg := intrinsicAlternatingRegularError_add_plusDet q r hq hr
  have harch := intrinsicAlternatingArchModel_add_plusDet q r hq hr
  unfold plusDetAlternatingSharpModel
    intrinsicAlternatingSharpRegularError intrinsicAlternatingSharpArchModel
    intrinsicAlternatingCorrelation intrinsicAlternatingPolynomialCorrection
  simp only [Pi.add_apply]
  rw [hreg, harch]
  ring

private theorem plusDetAlternatingH2Coupling_eq_sharpModel :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile (124 / 45) (-52 / 15) 1)
        (plusDetAlternatingOddProfile (-10319 / 4800) (15 / 8) 1) =
      plusDetAlternatingSharpModel plusDetAlternatingQH2 := by
  simpa only [plusDetAlternatingSharpModel, plusDetAlternatingQH2] using
    plusDetAlternatingCoupling_profile_eq_sharpModel
      (124 / 45) (-52 / 15) 1 (-10319 / 4800) (15 / 8) 1

private theorem plusDetAlternatingH3Couplings_eq_sharpModel :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile (1501 / 680) (-2419 / 680) (27 / 25))
        (plusDetAlternatingOddProfile (-10319 / 4800) (15 / 8) 1) +
      factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile (-81600701 / 11628000)
          (21466553 / 3876000) (337741 / 160000))
        (plusDetAlternatingOddProfile 1 0 0) =
      plusDetAlternatingSharpModel plusDetAlternatingQH3 := by
  let q : ℝ → ℝ := plusDetAlternatingQ
    (1501 / 680) (-2419 / 680) (27 / 25)
    (-10319 / 4800) (15 / 8) 1
  let r : ℝ → ℝ := plusDetAlternatingQ
    (-81600701 / 11628000) (21466553 / 3876000)
    (337741 / 160000) 1 0 0
  have hq : Continuous q := by
    dsimp only [q]
    unfold plusDetAlternatingQ alternatingQ41 alternatingQ43
      alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  have hr : Continuous r := by
    dsimp only [r]
    unfold plusDetAlternatingQ alternatingQ41 alternatingQ43
      alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  have hmain := plusDetAlternatingCoupling_profile_eq_sharpModel
    (1501 / 680) (-2419 / 680) (27 / 25)
    (-10319 / 4800) (15 / 8) 1
  have htail := plusDetAlternatingCoupling_profile_eq_sharpModel
    (-81600701 / 11628000) (21466553 / 3876000)
    (337741 / 160000) 1 0 0
  have hmain' :
      factorTwoCenteredAlternatingCoupling
          (plusDetAlternatingEvenProfile
            (1501 / 680) (-2419 / 680) (27 / 25))
          (plusDetAlternatingOddProfile (-10319 / 4800) (15 / 8) 1) =
        plusDetAlternatingSharpModel q := by
    simpa only [plusDetAlternatingSharpModel] using hmain
  have htail' :
      factorTwoCenteredAlternatingCoupling
          (plusDetAlternatingEvenProfile (-81600701 / 11628000)
            (21466553 / 3876000) (337741 / 160000))
          (plusDetAlternatingOddProfile 1 0 0) =
        plusDetAlternatingSharpModel r := by
    simpa only [plusDetAlternatingSharpModel] using htail
  have hadd := plusDetAlternatingSharpModel_add q r hq hr
  rw [hmain', htail', ← hadd]
  rfl

private theorem plusDetAlternatingH4Couplings_eq_sharpModel :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile (56 / 19) (-94 / 19) (83 / 32))
        (plusDetAlternatingOddProfile (-10319 / 4800) (15 / 8) 1) +
      factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile (-81600701 / 11628000)
          (21466553 / 3876000) (337741 / 160000))
        (plusDetAlternatingOddProfile (-359 / 360) 1 0) =
      plusDetAlternatingSharpModel plusDetAlternatingQH4 := by
  let q : ℝ → ℝ := plusDetAlternatingQ
    (56 / 19) (-94 / 19) (83 / 32)
    (-10319 / 4800) (15 / 8) 1
  let r : ℝ → ℝ := plusDetAlternatingQ
    (-81600701 / 11628000) (21466553 / 3876000)
    (337741 / 160000) (-359 / 360) 1 0
  have hq : Continuous q := by
    dsimp only [q]
    unfold plusDetAlternatingQ alternatingQ41 alternatingQ43
      alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  have hr : Continuous r := by
    dsimp only [r]
    unfold plusDetAlternatingQ alternatingQ41 alternatingQ43
      alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  have hmain := plusDetAlternatingCoupling_profile_eq_sharpModel
    (56 / 19) (-94 / 19) (83 / 32)
    (-10319 / 4800) (15 / 8) 1
  have htail := plusDetAlternatingCoupling_profile_eq_sharpModel
    (-81600701 / 11628000) (21466553 / 3876000)
    (337741 / 160000) (-359 / 360) 1 0
  have hmain' :
      factorTwoCenteredAlternatingCoupling
          (plusDetAlternatingEvenProfile (56 / 19) (-94 / 19) (83 / 32))
          (plusDetAlternatingOddProfile (-10319 / 4800) (15 / 8) 1) =
        plusDetAlternatingSharpModel q := by
    simpa only [plusDetAlternatingSharpModel] using hmain
  have htail' :
      factorTwoCenteredAlternatingCoupling
          (plusDetAlternatingEvenProfile (-81600701 / 11628000)
            (21466553 / 3876000) (337741 / 160000))
          (plusDetAlternatingOddProfile (-359 / 360) 1 0) =
        plusDetAlternatingSharpModel r := by
    simpa only [plusDetAlternatingSharpModel] using htail
  have hadd := plusDetAlternatingSharpModel_add q r hq hr
  rw [hmain', htail', ← hadd]
  rfl

private theorem plusDetAlternatingWCoupling_eq_sharpModel :
    factorTwoCenteredAlternatingCoupling
        (plusDetAlternatingEvenProfile (-81600701 / 11628000)
          (21466553 / 3876000) (337741 / 160000))
        (plusDetAlternatingOddProfile (-10319 / 4800) (15 / 8) 1) =
      plusDetAlternatingSharpModel plusDetAlternatingQW := by
  simpa only [plusDetAlternatingSharpModel, plusDetAlternatingQW] using
    plusDetAlternatingCoupling_profile_eq_sharpModel
      (-81600701 / 11628000) (21466553 / 3876000)
      (337741 / 160000) (-10319 / 4800) (15 / 8) 1

/-! ## Exact full affine sharp models -/

private def plusDetSharpModelH2 : ℝ :=
  (25704453062981 / 104652000000000 : ℝ) -
    (1341157 / 900000 : ℝ) * plusDetS -
    (33630601 / 116280000 : ℝ) * plusDetD +
    (1 / 2 : ℝ) * plusDetAlternatingSharpModel plusDetAlternatingQH2

private def plusDetSharpModelH3 : ℝ :=
  (4071911594689399 / 9883800000000000 : ℝ) -
    (14231391 / 6400000 : ℝ) * plusDetS +
    (2115529 / 3040000 : ℝ) * plusDetD +
    (1 / 2 : ℝ) * plusDetAlternatingSharpModel plusDetAlternatingQH3

private def plusDetSharpModelH4 : ℝ :=
  (12706719959751107 / 21209472000000000 : ℝ) -
    (23208881 / 5760000 : ℝ) * plusDetS +
    (36981907 / 4651200 : ℝ) * plusDetD +
    (1 / 2 : ℝ) * plusDetAlternatingSharpModel plusDetAlternatingQH4

private def plusDetSharpModelW : ℝ :=
  (1057809782673918967591 / 5408415360000000000000 : ℝ) -
    (8993029607 / 2880000000 : ℝ) * plusDetS +
    (1232757689669 / 46512000000 : ℝ) * plusDetD +
    plusDetAlternatingSharpModel plusDetAlternatingQW

private theorem plusDetActualH2_eq_sharpModel :
    plusDetActualH2 = plusDetSharpModelH2 := by
  unfold plusDetSharpModelH2
  rw [← plusDetAlternatingH2Coupling_eq_sharpModel,
    plusDetAlternatingCoupling_profile_expansion]
  unfold plusDetActualH2 plusDetH2 plusDetT02
    plusDetT12 plusDetT22 plusDetT23 plusDetT24 plusDetG2 plusDetG0
    plusDetShift0 plusDetShift1 plusDetShift2 plusDetShift3 plusDetShift4
    plusDetS plusDetD plusDetS1 plusDetD1 plusDetS3 plusDetD3
    plusDetA41 plusDetA43 plusDetA05 plusDetA25 plusDetA45
  ring

private theorem plusDetActualH3_eq_sharpModel_add_B1 :
    plusDetActualH3 = plusDetSharpModelH3 + plusP5OddB1 := by
  unfold plusDetSharpModelH3
  rw [← plusDetAlternatingH3Couplings_eq_sharpModel]
  repeat rw [plusDetAlternatingCoupling_profile_expansion]
  unfold plusDetActualH3 plusP5OddB1 plusDetH3
    plusDetT03 plusDetT13 plusDetT23 plusDetT33 plusDetT34 plusDetG3
    plusDetG0 plusDetShift0 plusDetShift1 plusDetShift2 plusDetShift3
    plusDetShift4 plusDetS plusDetD plusDetS1 plusDetD1 plusDetS3
    plusDetD3 plusDetA41 plusDetA43 plusDetO11 plusDetO13 plusDetA05
    plusDetA25 plusDetA45 plusDetO15
  ring

private theorem plusDetActualH4_eq_sharpModel_add_B4 :
    plusDetActualH4 = plusDetSharpModelH4 + plusP5OddB4 := by
  unfold plusDetSharpModelH4
  rw [← plusDetAlternatingH4Couplings_eq_sharpModel]
  repeat rw [plusDetAlternatingCoupling_profile_expansion]
  unfold plusDetActualH4 plusP5OddB4 plusDetH4
    plusDetT04 plusDetT14 plusDetT24 plusDetT34 plusDetT44 plusDetG4
    plusDetG0 plusDetShift0 plusDetShift1 plusDetShift2 plusDetShift3
    plusDetShift4 plusDetS plusDetD plusDetS1 plusDetD1 plusDetS3
    plusDetD3 plusDetA41 plusDetA43 plusDetO11 plusDetO13 plusDetO33
    plusDetA05 plusDetA25 plusDetA45 plusDetO15 plusDetO35
  ring

set_option maxHeartbeats 800000 in
private theorem plusDetActualW_eq_sharpModel_add_Q :
    plusDetActualW = plusDetSharpModelW + plusP5OddQ := by
  unfold plusDetSharpModelW
  rw [← plusDetAlternatingWCoupling_eq_sharpModel,
    plusDetAlternatingCoupling_profile_expansion]
  unfold plusDetActualW plusP5OddQ plusDetW
    plusDetTransformedSixQuadratic plusDetTransformedFiveQuadratic
    plusDetFiveQuadratic plusDetT00 plusDetT01 plusDetT02 plusDetT03
    plusDetT04 plusDetT11 plusDetT12 plusDetT13 plusDetT14 plusDetT22
    plusDetT23 plusDetT24 plusDetT33 plusDetT34 plusDetT44 plusDetG1
    plusDetG2 plusDetG3 plusDetG4 plusDetG0 plusDetShift0 plusDetShift1
    plusDetShift2 plusDetShift3 plusDetShift4 plusDetS plusDetD plusDetS1
    plusDetD1 plusDetS3 plusDetD3 plusDetA41 plusDetA43 plusDetO11
    plusDetO13 plusDetO33 plusDetA05 plusDetA25 plusDetA45 plusDetO15
    plusDetO35 plusDetO55
  ring

private theorem plusDetAlternatingQH2_polynomial (t : ℝ) :
    plusDetAlternatingQH2 t =
      (-611113 / 43200 : ℝ) - (42797 / 4000) * t +
        (4597879 / 144000) * t ^ 2 - (1337453 / 57600) * t ^ 3 +
        (1162387 / 115200) * t ^ 4 - (1913 / 1280) * t ^ 5 -
        (1913 / 2560) * t ^ 6 + (7 / 64) * t ^ 7 +
        (7 / 128) * t ^ 8 := by
  unfold plusDetAlternatingQH2 plusDetAlternatingQ alternatingQ41
    alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
  ring

private theorem plusDetAlternatingQH3_polynomial (t : ℝ) :
    plusDetAlternatingQH3 t =
      (-13750902299 / 465120000 : ℝ) + (4380755963 / 620160000) * t +
        (20323396423 / 1240320000) * t ^ 2 -
        (526512517 / 32640000) * t ^ 3 +
        (608243483 / 65280000) * t ^ 4 - (84951 / 54400) * t ^ 5 -
        (84951 / 108800) * t ^ 6 + (189 / 1600) * t ^ 7 +
        (189 / 3200) * t ^ 8 := by
  unfold plusDetAlternatingQH3 plusDetAlternatingQ alternatingQ41
    alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
  ring

private theorem plusDetAlternatingQH4_polynomial (t : ℝ) :
    plusDetAlternatingQH4 t =
      (-701556616831 / 83721600000 : ℝ) -
        (123472939931 / 13953600000) * t +
        (75008376999 / 2067200000) * t ^ 2 -
        (2849589069587 / 111628800000) * t ^ 3 +
        (2332337330413 / 223257600000) * t ^ 4 -
        (23436273 / 9728000) * t ^ 5 -
        (23436273 / 19456000) * t ^ 6 + (581 / 2048) * t ^ 7 +
        (581 / 4096) * t ^ 8 := by
  unfold plusDetAlternatingQH4 plusDetAlternatingQ alternatingQ41
    alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
  ring

private theorem plusDetAlternatingQW_polynomial (t : ℝ) :
    plusDetAlternatingQW t =
      (3339755746409 / 131328000000 : ℝ) +
        (388287114221 / 20672000000) * t -
        (91814899302449 / 1488384000000) * t ^ 2 +
        (182293898050181 / 2976768000000) * t ^ 3 -
        (146720128381819 / 5953536000000) * t ^ 4 +
        (6098875261 / 13230080000) * t ^ 5 +
        (6098875261 / 26460160000) * t ^ 6 +
        (2364187 / 10240000) * t ^ 7 +
        (2364187 / 20480000) * t ^ 8 := by
  unfold plusDetAlternatingQW plusDetAlternatingQ alternatingQ41
    alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
  ring

private theorem plusDetAlternatingQW_signed_bernstein (t : ℝ) :
    plusDetAlternatingQW t =
      plusDetAlternatingQWPositive t - plusDetAlternatingQWNegative t := by
  rw [plusDetAlternatingQW_polynomial]
  unfold plusDetAlternatingQWPositive plusDetAlternatingQWNegative
  ring

private theorem plusDetAlternatingQW_signed_parts_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    0 ≤ plusDetAlternatingQWPositive t ∧
      0 ≤ plusDetAlternatingQWNegative t := by
  have hx0 : 0 ≤ t / 2 := by linarith
  have hx1 : 0 ≤ 1 - t / 2 := by linarith
  unfold plusDetAlternatingQWPositive plusDetAlternatingQWNegative
  constructor <;> positivity

/-! ## Global Bernstein certificates for the complete profiles -/

private theorem abs_plusDetAlternatingQH2_le_seventeen
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |plusDetAlternatingQH2 t| ≤ 17 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  rw [abs_le]
  constructor
  · have h : 0 ≤ (17 : ℝ) + plusDetAlternatingQH2 t := by
      rw [show (17 : ℝ) + plusDetAlternatingQH2 t =
          (123287 / 43200 : ℝ) * (1 - x) ^ 8 +
            (77351 / 54000 : ℝ) * x * (1 - x) ^ 7 +
            (6246461 / 108000 : ℝ) * x ^ 2 * (1 - x) ^ 6 +
            (31428409 / 108000 : ℝ) * x ^ 3 * (1 - x) ^ 5 +
            (1618007 / 2700 : ℝ) * x ^ 4 * (1 - x) ^ 4 +
            (1905169 / 2700 : ℝ) * x ^ 5 * (1 - x) ^ 3 +
            (50339327 / 108000 : ℝ) * x ^ 6 * (1 - x) ^ 2 +
            (14171041 / 108000 : ℝ) * x ^ 7 * (1 - x) +
            (3717253 / 216000 : ℝ) * x ^ 8 by
        rw [plusDetAlternatingQH2_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith
  · have h : 0 ≤ (17 : ℝ) - plusDetAlternatingQH2 t := by
      rw [show (17 : ℝ) - plusDetAlternatingQH2 t =
          (1345513 / 43200 : ℝ) * (1 - x) ^ 8 +
            (14610649 / 54000 : ℝ) * x * (1 - x) ^ 7 +
            (96569539 / 108000 : ℝ) * x ^ 2 * (1 - x) ^ 6 +
            (174203591 / 108000 : ℝ) * x ^ 3 * (1 - x) ^ 5 +
            (4807993 / 2700 : ℝ) * x ^ 4 * (1 - x) ^ 4 +
            (3235631 / 2700 : ℝ) * x ^ 5 * (1 - x) ^ 3 +
            (52476673 / 108000 : ℝ) * x ^ 6 * (1 - x) ^ 2 +
            (15204959 / 108000 : ℝ) * x ^ 7 * (1 - x) +
            (3626747 / 216000 : ℝ) * x ^ 8 by
        rw [plusDetAlternatingQH2_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith

private theorem abs_plusDetAlternatingQH3_le_thirty
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |plusDetAlternatingQH3 t| ≤ 30 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  rw [abs_le]
  constructor
  · have h : 0 ≤ (30 : ℝ) + plusDetAlternatingQH3 t := by
      rw [show (30 : ℝ) + plusDetAlternatingQH3 t =
          (202697701 / 465120000 : ℝ) * (1 - x) ^ 8 +
            (3277086221 / 186048000 : ℝ) * x * (1 - x) ^ 7 +
            (41079283937 / 232560000 : ℝ) * x ^ 2 * (1 - x) ^ 6 +
            (544466049919 / 930240000 : ℝ) * x ^ 3 * (1 - x) ^ 5 +
            (470682569017 / 465120000 : ℝ) * x ^ 4 * (1 - x) ^ 4 +
            (53151033397 / 48960000 : ℝ) * x ^ 5 * (1 - x) ^ 3 +
            (80947416643 / 116280000 : ℝ) * x ^ 6 * (1 - x) ^ 2 +
            (197193253969 / 930240000 : ℝ) * x ^ 7 * (1 - x) +
            (10956887 / 360000 : ℝ) * x ^ 8 by
        rw [plusDetAlternatingQH3_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith
  · have h : 0 ≤ (30 : ℝ) - plusDetAlternatingQH3 t := by
      rw [show (30 : ℝ) - plusDetAlternatingQH3 t =
          (27704502299 / 465120000 : ℝ) * (1 - x) ^ 8 +
            (86025953779 / 186048000 : ℝ) * x * (1 - x) ^ 7 +
            (349621516063 / 232560000 : ℝ) * x ^ 2 * (1 - x) ^ 6 +
            (2581140350081 / 930240000 : ℝ) * x ^ 3 * (1 - x) ^ 5 +
            (1482821430983 / 465120000 : ℝ) * x ^ 4 * (1 - x) ^ 4 +
            (111354566603 / 48960000 : ℝ) * x ^ 5 * (1 - x) ^ 3 +
            (114402983357 / 116280000 : ℝ) * x ^ 6 * (1 - x) ^ 2 +
            (249321946031 / 930240000 : ℝ) * x ^ 7 * (1 - x) +
            (10643113 / 360000 : ℝ) * x ^ 8 by
        rw [plusDetAlternatingQH3_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith

private theorem abs_plusDetAlternatingQH4_le_eleven
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |plusDetAlternatingQH4 t| ≤ 11 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  rw [abs_le]
  constructor
  · have h : 0 ≤ (11 : ℝ) + plusDetAlternatingQH4 t := by
      rw [show (11 : ℝ) + plusDetAlternatingQH4 t =
          (219380983169 / 83721600000 : ℝ) * (1 - x) ^ 8 +
            (13668629309 / 4186080000 : ℝ) * x * (1 - x) ^ 7 +
            (3961148824183 / 41860800000 : ℝ) * x ^ 2 * (1 - x) ^ 6 +
            (18490381110179 / 41860800000 : ℝ) * x ^ 3 * (1 - x) ^ 5 +
            (580271422291 / 654075000 : ℝ) * x ^ 4 * (1 - x) ^ 4 +
            (160156726433 / 163518750 : ℝ) * x ^ 5 * (1 - x) ^ 3 +
            (22234622078269 / 41860800000 : ℝ) * x ^ 6 * (1 - x) ^ 2 +
            (2774139937739 / 41860800000 : ℝ) * x ^ 7 * (1 - x) +
            (2963264317 / 259200000 : ℝ) * x ^ 8 by
        rw [plusDetAlternatingQH4_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith
  · have h : 0 ≤ (11 : ℝ) - plusDetAlternatingQH4 t := by
      rw [show (11 : ℝ) - plusDetAlternatingQH4 t =
          (1622494216831 / 83721600000 : ℝ) * (1 - x) ^ 8 +
            (723081450691 / 4186080000 : ℝ) * x * (1 - x) ^ 7 +
            (21825103975817 / 41860800000 : ℝ) * x ^ 2 * (1 - x) ^ 6 +
            (33082124489821 / 41860800000 : ℝ) * x ^ 3 * (1 - x) ^ 5 +
            (427004077709 / 654075000 : ℝ) * x ^ 4 * (1 - x) ^ 4 +
            (41298373567 / 163518750 : ℝ) * x ^ 5 * (1 - x) ^ 3 +
            (3551630721731 / 41860800000 : ℝ) * x ^ 6 * (1 - x) ^ 2 +
            (4593360862261 / 41860800000 : ℝ) * x ^ 7 * (1 - x) +
            (2739135683 / 259200000 : ℝ) * x ^ 8 by
        rw [plusDetAlternatingQH4_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith

private theorem abs_plusDetAlternatingQW_le_thirty_one
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |plusDetAlternatingQW t| ≤ 31 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  rw [abs_le]
  constructor
  · have h : 0 ≤ (31 : ℝ) + plusDetAlternatingQW t := by
      rw [show (31 : ℝ) + plusDetAlternatingQW t =
          (7410923746409 / 131328000000 : ℝ) * (1 - x) ^ 8 +
            (3411736394323 / 6976800000 : ℝ) * x * (1 - x) ^ 7 +
            (1781900212089071 / 1116288000000 : ℝ) * x ^ 2 * (1 - x) ^ 6 +
            (3302448385050373 / 1116288000000 : ℝ) * x ^ 3 * (1 - x) ^ 5 +
            (1009950634466447 / 279072000000 : ℝ) * x ^ 4 * (1 - x) ^ 4 +
            (1605536700513713 / 558144000000 : ℝ) * x ^ 5 * (1 - x) ^ 3 +
            (1406487041539853 / 1116288000000 : ℝ) * x ^ 6 * (1 - x) ^ 2 +
            (233910351580393 / 1116288000000 : ℝ) * x ^ 7 * (1 - x) +
            (217438000829 / 6912000000 : ℝ) * x ^ 8 by
        rw [plusDetAlternatingQW_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith
  · have h : 0 ≤ (31 : ℝ) - plusDetAlternatingQW t := by
      rw [show (31 : ℝ) - plusDetAlternatingQW t =
          (731412253591 / 131328000000 : ℝ) * (1 - x) ^ 8 +
            (48756405677 / 6976800000 : ℝ) * x * (1 - x) ^ 7 +
            (155975755910929 / 1116288000000 : ℝ) * x ^ 2 * (1 - x) ^ 6 +
            (573303550949627 / 1116288000000 : ℝ) * x ^ 3 * (1 - x) ^ 5 +
            (201221845533553 / 279072000000 : ℝ) * x ^ 4 * (1 - x) ^ 4 +
            (332339267486287 / 558144000000 : ℝ) * x ^ 5 * (1 - x) ^ 3 +
            (531388926460147 / 1116288000000 : ℝ) * x ^ 6 * (1 - x) ^ 2 +
            (319768496419607 / 1116288000000 : ℝ) * x ^ 7 * (1 - x) +
            (211105999171 / 6912000000 : ℝ) * x ^ 8 by
        rw [plusDetAlternatingQW_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith

/-! ## One sharp remainder estimate per complete profile -/

private theorem integral_plusDetAlternatingQW_signed_majorant :
    (∫ t : ℝ in 0..2,
      intrinsicAlternatingSignedLowerMagnitude t *
          intrinsicAlternatingCorrelation plusDetAlternatingQWPositive t +
        intrinsicAlternatingSignedUpperMagnitude t *
          intrinsicAlternatingCorrelation plusDetAlternatingQWNegative t) <
      (463 / 1000000 : ℝ) := by
  unfold intrinsicAlternatingSignedLowerMagnitude
    intrinsicAlternatingSignedUpperMagnitude intrinsicAlternatingCorrelation
    plusDetAlternatingQWPositive plusDetAlternatingQWNegative
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem plusDetAlternatingSharpRegularErrorW_signed_lower :
    (-(463 / 1000000) : ℝ) <
      intrinsicAlternatingSharpRegularError plusDetAlternatingQW := by
  apply intrinsicAlternatingSharpRegularError_lower_of_signed_decomposition
    plusDetAlternatingQW plusDetAlternatingQWPositive
      plusDetAlternatingQWNegative
  · unfold plusDetAlternatingQW plusDetAlternatingQ alternatingQ41
      alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  · unfold plusDetAlternatingQWPositive
    fun_prop
  · unfold plusDetAlternatingQWNegative
    fun_prop
  · funext t
    exact plusDetAlternatingQW_signed_bernstein t
  · intro t ht0 ht2
    exact (plusDetAlternatingQW_signed_parts_nonneg ht0 ht2).1
  · intro t ht0 ht2
    exact (plusDetAlternatingQW_signed_parts_nonneg ht0 ht2).2
  · exact integral_plusDetAlternatingQW_signed_majorant

private theorem abs_plusDetAlternatingSharpRegularErrorH2_lt :
    |intrinsicAlternatingSharpRegularError plusDetAlternatingQH2| <
      (17 / 25000 : ℝ) := by
  exact abs_intrinsicAlternatingSharpRegularError_lt_of_uniform_q_bound
    plusDetAlternatingQH2
    (by
      unfold plusDetAlternatingQH2 plusDetAlternatingQ alternatingQ41
        alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
      fun_prop)
    17 (by norm_num)
    (fun t ht0 ht2 ↦ abs_plusDetAlternatingQH2_le_seventeen ht0 ht2)

private theorem abs_plusDetAlternatingSharpRegularErrorH3_lt :
    |intrinsicAlternatingSharpRegularError plusDetAlternatingQH3| <
      (30 / 25000 : ℝ) := by
  exact abs_intrinsicAlternatingSharpRegularError_lt_of_uniform_q_bound
    plusDetAlternatingQH3
    (by
      unfold plusDetAlternatingQH3 plusDetAlternatingQ alternatingQ41
        alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
      fun_prop)
    30 (by norm_num)
    (fun t ht0 ht2 ↦ abs_plusDetAlternatingQH3_le_thirty ht0 ht2)

private theorem abs_plusDetAlternatingSharpRegularErrorH4_lt :
    |intrinsicAlternatingSharpRegularError plusDetAlternatingQH4| <
      (11 / 25000 : ℝ) := by
  exact abs_intrinsicAlternatingSharpRegularError_lt_of_uniform_q_bound
    plusDetAlternatingQH4
    (by
      unfold plusDetAlternatingQH4 plusDetAlternatingQ alternatingQ41
        alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
      fun_prop)
    11 (by norm_num)
    (fun t ht0 ht2 ↦ abs_plusDetAlternatingQH4_le_eleven ht0 ht2)

private theorem abs_plusDetAlternatingSharpRegularErrorW_lt :
    |intrinsicAlternatingSharpRegularError plusDetAlternatingQW| <
      (31 / 25000 : ℝ) := by
  exact abs_intrinsicAlternatingSharpRegularError_lt_of_uniform_q_bound
    plusDetAlternatingQW
    (by
      unfold plusDetAlternatingQW plusDetAlternatingQ alternatingQ41
        alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
      fun_prop)
    31 (by norm_num)
    (fun t ht0 ht2 ↦ abs_plusDetAlternatingQW_le_thirty_one ht0 ht2)

/-! ## Exact sharp archimedean model for a polynomial profile -/

private theorem integral_inv_two_add_plusDet :
    (∫ t : ℝ in 0..2, 1 / (2 + t)) = Real.log 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log (2 + t)
  have hderiv (t : ℝ) (ht : 2 + t ≠ 0) :
      HasDerivAt F (1 / (2 + t)) t := by
    have hadd : HasDerivAt (fun x : ℝ ↦ 2 + x) 1 t := by
      simpa using (hasDerivAt_const t 2).add (hasDerivAt_id t)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log ht).comp t hadd
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (2 + t))
      (uIcc (0 : ℝ) 2) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hderiv t (by
      have ht' : t ∈ Icc (0 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      linarith [ht'.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring]
  ring

private theorem intervalIntegrable_inv_two_add_plusDet :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

private theorem intrinsicAlternatingSharpArchModel_eq_integral_plusDet
    (q : ℝ → ℝ) (hq : Continuous q) :
    intrinsicAlternatingSharpArchModel q =
      ∫ t : ℝ in 0..2,
        intrinsicAlternatingKernelPolynomial6 t *
            intrinsicAlternatingCorrelation q t +
          t ^ 2 * q t / (2 + t) := by
  let C : ℝ → ℝ := intrinsicAlternatingCorrelation q
  let f : ℝ → ℝ := fun t ↦ (t / 10) * C t + t ^ 2 * q t / (2 + t)
  let g : ℝ → ℝ := fun t ↦
    (intrinsicAlternatingKernelPolynomial6 t - t / 10) * C t
  have hC : Continuous C := by
    dsimp only [C]
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hK : Continuous intrinsicAlternatingKernelPolynomial6 := by
    rw [show intrinsicAlternatingKernelPolynomial6 = fun t : ℝ ↦
        intrinsicAlternatingKernelCoeff1 yoshidaEndpointA * t +
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA * t ^ 3 +
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA * t ^ 5 by
      funext t
      exact intrinsicAlternatingKernelPolynomial6_expansion t]
    fun_prop
  have hrat : ContinuousOn (fun t : ℝ ↦ t ^ 2 * q t / (2 + t))
      (uIcc (0 : ℝ) 2) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hden : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (((continuousAt_id.pow 2).mul hq.continuousAt).div
      (continuousAt_const.add continuousAt_id) hden).continuousWithinAt
  have hf : IntervalIntegrable f volume 0 2 := by
    apply ContinuousOn.intervalIntegrable
    exact ((continuous_id.div_const 10).mul hC).continuousOn.add hrat
  have hg : IntervalIntegrable g volume 0 2 := by
    exact ((hK.sub (continuous_id.div_const 10)).mul hC).intervalIntegrable 0 2
  unfold intrinsicAlternatingSharpArchModel intrinsicAlternatingArchModel
    intrinsicAlternatingPolynomialCorrection
  change (∫ t : ℝ in 0..2, f t) + (∫ t : ℝ in 0..2, g t) = _
  rw [← intervalIntegral.integral_add hf hg]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [f, g, C]
  ring

private theorem intrinsicAlternatingSharpArchModel_eq_data_plusDet
    (q quotient : ℝ → ℝ) (r P m1 m3 m5 : ℝ)
    (hq : Continuous q) (hquotient : Continuous quotient)
    (hdiv : ∀ t ∈ Icc (0 : ℝ) 2,
      t ^ 2 * q t / (2 + t) = quotient t + r * (1 / (2 + t)))
    (hP : (∫ t : ℝ in 0..2, quotient t) = P)
    (hm1 : (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation q t) = m1)
    (hm3 : (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation q t) = m3)
    (hm5 : (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation q t) = m5) :
    intrinsicAlternatingSharpArchModel q =
      P + r * Real.log 2 +
        m1 * intrinsicAlternatingKernelCoeff1 yoshidaEndpointA +
        m3 * intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        m5 * intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  rw [intrinsicAlternatingSharpArchModel_eq_integral_plusDet q hq]
  let C : ℝ → ℝ := intrinsicAlternatingCorrelation q
  have hC : Continuous C := by
    dsimp only [C]
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have h1I : IntervalIntegrable
      (fun t : ℝ ↦ intrinsicAlternatingKernelCoeff1 yoshidaEndpointA *
        (t * C t)) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      intrinsicAlternatingKernelCoeff1 yoshidaEndpointA * (t * C t))).intervalIntegrable 0 2
  have h3I : IntervalIntegrable
      (fun t : ℝ ↦ intrinsicAlternatingKernelCoeff3 yoshidaEndpointA *
        (t ^ 3 * C t)) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      intrinsicAlternatingKernelCoeff3 yoshidaEndpointA *
        (t ^ 3 * C t))).intervalIntegrable 0 2
  have h5I : IntervalIntegrable
      (fun t : ℝ ↦ intrinsicAlternatingKernelCoeff5 yoshidaEndpointA *
        (t ^ 5 * C t)) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      intrinsicAlternatingKernelCoeff5 yoshidaEndpointA *
        (t ^ 5 * C t))).intervalIntegrable 0 2
  have hqI : IntervalIntegrable quotient volume 0 2 :=
    hquotient.intervalIntegrable 0 2
  have hinvI : IntervalIntegrable
      (fun t : ℝ ↦ r * (1 / (2 + t))) volume 0 2 :=
    intervalIntegrable_inv_two_add_plusDet.const_mul r
  calc
    (∫ t : ℝ in 0..2,
        intrinsicAlternatingKernelPolynomial6 t *
            intrinsicAlternatingCorrelation q t +
          t ^ 2 * q t / (2 + t)) =
      ∫ t : ℝ in 0..2,
        intrinsicAlternatingKernelCoeff1 yoshidaEndpointA * (t * C t) +
          (intrinsicAlternatingKernelCoeff3 yoshidaEndpointA *
              (t ^ 3 * C t) +
            (intrinsicAlternatingKernelCoeff5 yoshidaEndpointA *
                (t ^ 5 * C t) +
              (quotient t + r * (1 / (2 + t))))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
        change intrinsicAlternatingKernelPolynomial6 t *
            intrinsicAlternatingCorrelation q t +
              t ^ 2 * q t / (2 + t) = _
        rw [hdiv t ht, intrinsicAlternatingKernelPolynomial6_expansion]
        dsimp only [C]
        ring
    _ = _ := by
      rw [intervalIntegral.integral_add h1I
          (h3I.add (h5I.add (hqI.add hinvI))),
        intervalIntegral.integral_add h3I (h5I.add (hqI.add hinvI)),
        intervalIntegral.integral_add h5I (hqI.add hinvI),
        intervalIntegral.integral_add hqI hinvI]
      repeat rw [intervalIntegral.integral_const_mul]
      dsimp only [C]
      rw [hP, hm1, hm3, hm5, integral_inv_two_add_plusDet]
      ring

private def plusDetAlternatingArchQuotientH2 (t : ℝ) : ℝ :=
  (-20829797 / 21600 : ℝ) + (20829797 / 43200) * t -
    (714697 / 2880) * t ^ 2 + (17097079 / 144000) * t ^ 3 -
    (217 / 5) * t ^ 4 + (1162387 / 115200) * t ^ 5 -
    (1913 / 2560) * t ^ 7 + (7 / 128) * t ^ 9

private theorem plusDetAlternatingArchDivisionH2
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    t ^ 2 * plusDetAlternatingQH2 t / (2 + t) =
      plusDetAlternatingArchQuotientH2 t +
        (20829797 / 10800 : ℝ) * (1 / (2 + t)) := by
  have hden : 2 + t ≠ 0 := by linarith [ht.1]
  rw [plusDetAlternatingQH2_polynomial]
  unfold plusDetAlternatingArchQuotientH2
  field_simp [hden]
  ring

private theorem integral_plusDetAlternatingArchQuotientH2 :
    (∫ t : ℝ in 0..2, plusDetAlternatingArchQuotientH2 t) =
      (-9042463 / 6750 : ℝ) := by
  unfold plusDetAlternatingArchQuotientH2
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  norm_num

private theorem integral_plusDetAlternatingQH2_moment_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation plusDetAlternatingQH2 t) =
        (-319889 / 40500 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQH2_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_plusDetAlternatingQH2_moment_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation plusDetAlternatingQH2 t) =
        (-1060561 / 141750 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQH2_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_plusDetAlternatingQH2_moment_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation plusDetAlternatingQH2 t) =
        (-81252041 / 7796250 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQH2_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem plusDetAlternatingSharpArchModelH2_eq :
    intrinsicAlternatingSharpArchModel plusDetAlternatingQH2 =
      (-9042463 / 6750 : ℝ) +
        (20829797 / 10800) * Real.log 2 +
        (-319889 / 40500) *
          intrinsicAlternatingKernelCoeff1 yoshidaEndpointA +
        (-1060561 / 141750) *
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (-81252041 / 7796250) *
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  apply intrinsicAlternatingSharpArchModel_eq_data_plusDet
    plusDetAlternatingQH2 plusDetAlternatingArchQuotientH2
    (20829797 / 10800) (-9042463 / 6750)
    (-319889 / 40500) (-1060561 / 141750) (-81252041 / 7796250)
  · unfold plusDetAlternatingQH2 plusDetAlternatingQ alternatingQ41
      alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  · unfold plusDetAlternatingArchQuotientH2
    fun_prop
  · exact plusDetAlternatingArchDivisionH2
  · exact integral_plusDetAlternatingArchQuotientH2
  · exact integral_plusDetAlternatingQH2_moment_one
  · exact integral_plusDetAlternatingQH2_moment_three
  · exact integral_plusDetAlternatingQH2_moment_five

private def plusDetAlternatingArchQuotientH3 (t : ℝ) : ℝ :=
  (-139525242391 / 232560000 : ℝ) +
    (139525242391 / 465120000) * t -
    (268905517 / 1632000) * t ^ 2 +
    (106564852423 / 1240320000) * t ^ 3 -
    (94563 / 2720) * t ^ 4 + (608243483 / 65280000) * t ^ 5 -
    (84951 / 108800) * t ^ 7 + (189 / 3200) * t ^ 9

private theorem plusDetAlternatingArchDivisionH3
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    t ^ 2 * plusDetAlternatingQH3 t / (2 + t) =
      plusDetAlternatingArchQuotientH3 t +
        (139525242391 / 116280000 : ℝ) * (1 / (2 + t)) := by
  have hden : 2 + t ≠ 0 := by linarith [ht.1]
  rw [plusDetAlternatingQH3_polynomial]
  unfold plusDetAlternatingArchQuotientH3
  field_simp [hden]
  ring

private theorem integral_plusDetAlternatingArchQuotientH3 :
    (∫ t : ℝ in 0..2, plusDetAlternatingArchQuotientH3 t) =
      (-779285785199 / 930240000 : ℝ) := by
  unfold plusDetAlternatingArchQuotientH3
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  norm_num

private theorem integral_plusDetAlternatingQH3_moment_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation plusDetAlternatingQH3 t) =
        (-2188473899 / 139536000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQH3_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_plusDetAlternatingQH3_moment_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation plusDetAlternatingQH3 t) =
        (-3933625 / 229824 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQH3_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_plusDetAlternatingQH3_moment_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation plusDetAlternatingQH3 t) =
        (-1547548853 / 56430000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQH3_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem plusDetAlternatingSharpArchModelH3_eq :
    intrinsicAlternatingSharpArchModel plusDetAlternatingQH3 =
      (-779285785199 / 930240000 : ℝ) +
        (139525242391 / 116280000) * Real.log 2 +
        (-2188473899 / 139536000) *
          intrinsicAlternatingKernelCoeff1 yoshidaEndpointA +
        (-3933625 / 229824) *
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (-1547548853 / 56430000) *
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  apply intrinsicAlternatingSharpArchModel_eq_data_plusDet
    plusDetAlternatingQH3 plusDetAlternatingArchQuotientH3
    (139525242391 / 116280000) (-779285785199 / 930240000)
    (-2188473899 / 139536000) (-3933625 / 229824)
    (-1547548853 / 56430000)
  · unfold plusDetAlternatingQH3 plusDetAlternatingQ alternatingQ41
      alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  · unfold plusDetAlternatingArchQuotientH3
    fun_prop
  · exact plusDetAlternatingArchDivisionH3
  · exact integral_plusDetAlternatingArchQuotientH3
  · exact integral_plusDetAlternatingQH3_moment_one
  · exact integral_plusDetAlternatingQH3_moment_three
  · exact integral_plusDetAlternatingQH3_moment_five

private def plusDetAlternatingArchQuotientH4 (t : ℝ) : ℝ :=
  (-2317001796641 / 2203200000 : ℝ) +
    (2317001796641 / 4406400000) * t -
    (1490819691767 / 5581440000) * t ^ 2 +
    (266931576999 / 2067200000) * t ^ 3 -
    (882 / 19) * t ^ 4 + (2332337330413 / 223257600000) * t ^ 5 -
    (23436273 / 19456000) * t ^ 7 + (581 / 4096) * t ^ 9

private theorem plusDetAlternatingArchDivisionH4
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    t ^ 2 * plusDetAlternatingQH4 t / (2 + t) =
      plusDetAlternatingArchQuotientH4 t +
        (2317001796641 / 1101600000 : ℝ) * (1 / (2 + t)) := by
  have hden : 2 + t ≠ 0 := by linarith [ht.1]
  rw [plusDetAlternatingQH4_polynomial]
  unfold plusDetAlternatingArchQuotientH4
  field_simp [hden]
  ring

private theorem integral_plusDetAlternatingArchQuotientH4 :
    (∫ t : ℝ in 0..2, plusDetAlternatingArchQuotientH4 t) =
      (-1906108694057 / 1308150000 : ℝ) := by
  unfold plusDetAlternatingArchQuotientH4
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  norm_num

private theorem integral_plusDetAlternatingQH4_moment_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation plusDetAlternatingQH4 t) =
        (2770694059 / 3139560000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQH4_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_plusDetAlternatingQH4_moment_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation plusDetAlternatingQH4 t) =
        (5962046723 / 1569780000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQH4_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_plusDetAlternatingQH4_moment_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation plusDetAlternatingQH4 t) =
        (29549817047 / 3453516000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQH4_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem plusDetAlternatingSharpArchModelH4_eq :
    intrinsicAlternatingSharpArchModel plusDetAlternatingQH4 =
      (-1906108694057 / 1308150000 : ℝ) +
        (2317001796641 / 1101600000) * Real.log 2 +
        (2770694059 / 3139560000) *
          intrinsicAlternatingKernelCoeff1 yoshidaEndpointA +
        (5962046723 / 1569780000) *
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (29549817047 / 3453516000) *
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  apply intrinsicAlternatingSharpArchModel_eq_data_plusDet
    plusDetAlternatingQH4 plusDetAlternatingArchQuotientH4
    (2317001796641 / 1101600000) (-1906108694057 / 1308150000)
    (2770694059 / 3139560000) (5962046723 / 1569780000)
    (29549817047 / 3453516000)
  · unfold plusDetAlternatingQH4 plusDetAlternatingQ alternatingQ41
      alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  · unfold plusDetAlternatingArchQuotientH4
    fun_prop
  · exact plusDetAlternatingArchDivisionH4
  · exact integral_plusDetAlternatingArchQuotientH4
  · exact integral_plusDetAlternatingQH4_moment_one
  · exact integral_plusDetAlternatingQH4_moment_three
  · exact integral_plusDetAlternatingQH4_moment_five

private def plusDetAlternatingArchQuotientW (t : ℝ) : ℝ :=
  (2552067723389477 / 1116288000000 : ℝ) -
    (2552067723389477 / 2232576000000) * t +
    (86961452369281 / 148838400000) * t ^ 2 -
    (420828925734449 / 1488384000000) * t ^ 3 +
    (571204907 / 5168000) * t ^ 4 -
    (146720128381819 / 5953536000000) * t ^ 5 +
    (6098875261 / 26460160000) * t ^ 7 +
    (2364187 / 20480000) * t ^ 9

private theorem plusDetAlternatingArchDivisionW
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    t ^ 2 * plusDetAlternatingQW t / (2 + t) =
      plusDetAlternatingArchQuotientW t -
        (2552067723389477 / 558144000000 : ℝ) * (1 / (2 + t)) := by
  have hden : 2 + t ≠ 0 := by linarith [ht.1]
  rw [plusDetAlternatingQW_polynomial]
  unfold plusDetAlternatingArchQuotientW
  field_simp [hden]
  ring

private theorem integral_plusDetAlternatingArchQuotientW :
    (∫ t : ℝ in 0..2, plusDetAlternatingArchQuotientW t) =
      (93327169729909 / 29376000000 : ℝ) := by
  unfold plusDetAlternatingArchQuotientW
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  norm_num

private theorem integral_plusDetAlternatingQW_moment_one :
    (∫ t : ℝ in 0..2,
      t * intrinsicAlternatingCorrelation plusDetAlternatingQW t) =
        (49531625507 / 2462400000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQW_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_plusDetAlternatingQW_moment_three :
    (∫ t : ℝ in 0..2,
      t ^ 3 * intrinsicAlternatingCorrelation plusDetAlternatingQW t) =
        (477772978451 / 20930400000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQW_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem integral_plusDetAlternatingQW_moment_five :
    (∫ t : ℝ in 0..2,
      t ^ 5 * intrinsicAlternatingCorrelation plusDetAlternatingQW t) =
        (16531028919223 / 460468800000 : ℝ) := by
  unfold intrinsicAlternatingCorrelation
  simp_rw [plusDetAlternatingQW_polynomial]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  norm_num

private theorem plusDetAlternatingSharpArchModelW_eq :
    intrinsicAlternatingSharpArchModel plusDetAlternatingQW =
      (93327169729909 / 29376000000 : ℝ) +
        (-2552067723389477 / 558144000000) * Real.log 2 +
        (49531625507 / 2462400000) *
          intrinsicAlternatingKernelCoeff1 yoshidaEndpointA +
        (477772978451 / 20930400000) *
          intrinsicAlternatingKernelCoeff3 yoshidaEndpointA +
        (16531028919223 / 460468800000) *
          intrinsicAlternatingKernelCoeff5 yoshidaEndpointA := by
  apply intrinsicAlternatingSharpArchModel_eq_data_plusDet
    plusDetAlternatingQW plusDetAlternatingArchQuotientW
    (-2552067723389477 / 558144000000)
    (93327169729909 / 29376000000)
    (49531625507 / 2462400000) (477772978451 / 20930400000)
    (16531028919223 / 460468800000)
  · unfold plusDetAlternatingQW plusDetAlternatingQ alternatingQ41
      alternatingQ43 alternatingQ05 alternatingQ25 alternatingQ45
    fun_prop
  · unfold plusDetAlternatingArchQuotientW
    fun_prop
  · intro t ht
    have h := plusDetAlternatingArchDivisionW t ht
    linarith
  · exact integral_plusDetAlternatingArchQuotientW
  · exact integral_plusDetAlternatingQW_moment_one
  · exact integral_plusDetAlternatingQW_moment_three
  · exact integral_plusDetAlternatingQW_moment_five

private theorem log_two_pow_fine_bounds_plusDet
    (n : ℕ) (hn : n ≠ 0) :
    (69314718055 / 100000000000 : ℝ) ^ n < (Real.log 2) ^ n ∧
      (Real.log 2) ^ n <
        (69314718057 / 100000000000 : ℝ) ^ n := by
  have hlog := strict_log_two_fine_bounds
  have hlog0 : 0 ≤ Real.log 2 := by linarith [hlog.1]
  constructor
  · exact pow_lt_pow_left₀ hlog.1 (by norm_num) hn
  · exact pow_lt_pow_left₀ hlog.2 hlog0 hn

private theorem plusDetAlternatingSharpArchModelH2_bounds :
    (-3546612 / 1000000 : ℝ) <
        intrinsicAlternatingSharpArchModel plusDetAlternatingQH2 ∧
      intrinsicAlternatingSharpArchModel plusDetAlternatingQH2 <
        (-3546611 / 1000000 : ℝ) := by
  rw [plusDetAlternatingSharpArchModelH2_eq]
  unfold intrinsicAlternatingKernelCoeff1 intrinsicAlternatingKernelCoeff3
    intrinsicAlternatingKernelCoeff5 yoshidaEndpointA
  have hlog := strict_log_two_fine_bounds
  have h2 := log_two_pow_fine_bounds_plusDet 2 (by norm_num)
  have h3 := log_two_pow_fine_bounds_plusDet 3 (by norm_num)
  have h4 := log_two_pow_fine_bounds_plusDet 4 (by norm_num)
  have h5 := log_two_pow_fine_bounds_plusDet 5 (by norm_num)
  have h6 := log_two_pow_fine_bounds_plusDet 6 (by norm_num)
  have h7 := log_two_pow_fine_bounds_plusDet 7 (by norm_num)
  constructor <;> nlinarith [hlog.1, hlog.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2]

private theorem plusDetAlternatingSharpArchModelH3_bounds :
    (-7572248 / 1000000 : ℝ) <
        intrinsicAlternatingSharpArchModel plusDetAlternatingQH3 ∧
      intrinsicAlternatingSharpArchModel plusDetAlternatingQH3 <
        (-7572247 / 1000000 : ℝ) := by
  rw [plusDetAlternatingSharpArchModelH3_eq]
  unfold intrinsicAlternatingKernelCoeff1 intrinsicAlternatingKernelCoeff3
    intrinsicAlternatingKernelCoeff5 yoshidaEndpointA
  have hlog := strict_log_two_fine_bounds
  have h2 := log_two_pow_fine_bounds_plusDet 2 (by norm_num)
  have h3 := log_two_pow_fine_bounds_plusDet 3 (by norm_num)
  have h4 := log_two_pow_fine_bounds_plusDet 4 (by norm_num)
  have h5 := log_two_pow_fine_bounds_plusDet 5 (by norm_num)
  have h6 := log_two_pow_fine_bounds_plusDet 6 (by norm_num)
  have h7 := log_two_pow_fine_bounds_plusDet 7 (by norm_num)
  constructor <;> nlinarith [hlog.1, hlog.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2]

private theorem plusDetAlternatingSharpArchModelH4_bounds :
    (886397 / 1000000 : ℝ) <
        intrinsicAlternatingSharpArchModel plusDetAlternatingQH4 ∧
      intrinsicAlternatingSharpArchModel plusDetAlternatingQH4 <
        (886398 / 1000000 : ℝ) := by
  rw [plusDetAlternatingSharpArchModelH4_eq]
  unfold intrinsicAlternatingKernelCoeff1 intrinsicAlternatingKernelCoeff3
    intrinsicAlternatingKernelCoeff5 yoshidaEndpointA
  have hlog := strict_log_two_fine_bounds
  have h2 := log_two_pow_fine_bounds_plusDet 2 (by norm_num)
  have h3 := log_two_pow_fine_bounds_plusDet 3 (by norm_num)
  have h4 := log_two_pow_fine_bounds_plusDet 4 (by norm_num)
  have h5 := log_two_pow_fine_bounds_plusDet 5 (by norm_num)
  have h6 := log_two_pow_fine_bounds_plusDet 6 (by norm_num)
  have h7 := log_two_pow_fine_bounds_plusDet 7 (by norm_num)
  constructor <;> nlinarith [hlog.1, hlog.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2]

private theorem plusDetAlternatingSharpArchModelW_bounds :
    (4814111 / 500000 : ℝ) <
        intrinsicAlternatingSharpArchModel plusDetAlternatingQW ∧
      intrinsicAlternatingSharpArchModel plusDetAlternatingQW <
        (9628223 / 1000000 : ℝ) := by
  rw [plusDetAlternatingSharpArchModelW_eq]
  unfold intrinsicAlternatingKernelCoeff1 intrinsicAlternatingKernelCoeff3
    intrinsicAlternatingKernelCoeff5 yoshidaEndpointA
  have hlog := strict_log_two_fine_bounds
  have h2 := log_two_pow_fine_bounds_plusDet 2 (by norm_num)
  have h3 := log_two_pow_fine_bounds_plusDet 3 (by norm_num)
  have h4 := log_two_pow_fine_bounds_plusDet 4 (by norm_num)
  have h5 := log_two_pow_fine_bounds_plusDet 5 (by norm_num)
  have h6 := log_two_pow_fine_bounds_plusDet 6 (by norm_num)
  have h7 := log_two_pow_fine_bounds_plusDet 7 (by norm_num)
  constructor <;> nlinarith [hlog.1, hlog.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2]

/-! ## The retained-prime value of each complete correlation -/

private theorem factorTwoPrimeRatio_fine_bounds_plusDet :
    (1169925 / 1000000 : ℝ) <
        factorTwoPrimeShift / yoshidaEndpointA ∧
      factorTwoPrimeShift / yoshidaEndpointA <
        (1169926 / 1000000 : ℝ) := by
  have hApos : 0 < yoshidaEndpointA := yoshidaEndpointA_pos
  have hshift := strict_log_three_halves_fine_bounds
  have hlog := strict_log_two_fine_bounds
  constructor
  · rw [lt_div_iff₀ hApos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    nlinarith [hshift.1, hlog.2]
  · rw [div_lt_iff₀ hApos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    nlinarith [hshift.2, hlog.1]

private theorem offset_pow_lt_plusDet
    {y eps : ℝ} (hy : 0 ≤ y) (hye : y < eps)
    (n : ℕ) (hn : n ≠ 0) :
    y ^ n < eps ^ n :=
  pow_lt_pow_left₀ hye hy hn

private theorem plusDetAlternatingPrimeCorrelationH2_bounds :
    (-574037 / 100000 : ℝ) <
        intrinsicAlternatingCorrelation plusDetAlternatingQH2
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation plusDetAlternatingQH2
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (-574021 / 100000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 116992 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hy0 : 0 < y := by dsimp only [y, tau]; linarith [htau.1]
  have hyU : y < (1 / 100000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := offset_pow_lt_plusDet hy0.le hyU 2 (by norm_num)
  have hy3 := offset_pow_lt_plusDet hy0.le hyU 3 (by norm_num)
  have hy4 := offset_pow_lt_plusDet hy0.le hyU 4 (by norm_num)
  have hy5 := offset_pow_lt_plusDet hy0.le hyU 5 (by norm_num)
  have hy6 := offset_pow_lt_plusDet hy0.le hyU 6 (by norm_num)
  have hy7 := offset_pow_lt_plusDet hy0.le hyU 7 (by norm_num)
  have hy8 := offset_pow_lt_plusDet hy0.le hyU 8 (by norm_num)
  have hy9 := offset_pow_lt_plusDet hy0.le hyU 9 (by norm_num)
  have hy10 := offset_pow_lt_plusDet hy0.le hyU 10 (by norm_num)
  have htauy : tau = 116992 / 100000 + y := by dsimp only [y]; ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  unfold intrinsicAlternatingCorrelation
  rw [plusDetAlternatingQH2_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9, hy10,
    sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6, pow_nonneg hy0.le 7,
    pow_nonneg hy0.le 8, pow_nonneg hy0.le 9, pow_nonneg hy0.le 10]

private theorem plusDetAlternatingPrimeCorrelationH3_bounds :
    (-1176118 / 100000 : ℝ) <
        intrinsicAlternatingCorrelation plusDetAlternatingQH3
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation plusDetAlternatingQH3
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (-1176096 / 100000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 116992 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hy0 : 0 < y := by dsimp only [y, tau]; linarith [htau.1]
  have hyU : y < (1 / 100000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := offset_pow_lt_plusDet hy0.le hyU 2 (by norm_num)
  have hy3 := offset_pow_lt_plusDet hy0.le hyU 3 (by norm_num)
  have hy4 := offset_pow_lt_plusDet hy0.le hyU 4 (by norm_num)
  have hy5 := offset_pow_lt_plusDet hy0.le hyU 5 (by norm_num)
  have hy6 := offset_pow_lt_plusDet hy0.le hyU 6 (by norm_num)
  have hy7 := offset_pow_lt_plusDet hy0.le hyU 7 (by norm_num)
  have hy8 := offset_pow_lt_plusDet hy0.le hyU 8 (by norm_num)
  have hy9 := offset_pow_lt_plusDet hy0.le hyU 9 (by norm_num)
  have hy10 := offset_pow_lt_plusDet hy0.le hyU 10 (by norm_num)
  have htauy : tau = 116992 / 100000 + y := by dsimp only [y]; ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  unfold intrinsicAlternatingCorrelation
  rw [plusDetAlternatingQH3_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9, hy10,
    sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6, pow_nonneg hy0.le 7,
    pow_nonneg hy0.le 8, pow_nonneg hy0.le 9, pow_nonneg hy0.le 10]

private theorem plusDetAlternatingPrimeCorrelationH4_bounds :
    (63269 / 25000 : ℝ) <
        intrinsicAlternatingCorrelation plusDetAlternatingQH4
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation plusDetAlternatingQH4
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (63271 / 25000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 116992 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hy0 : 0 < y := by dsimp only [y, tau]; linarith [htau.1]
  have hyU : y < (1 / 100000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := offset_pow_lt_plusDet hy0.le hyU 2 (by norm_num)
  have hy3 := offset_pow_lt_plusDet hy0.le hyU 3 (by norm_num)
  have hy4 := offset_pow_lt_plusDet hy0.le hyU 4 (by norm_num)
  have hy5 := offset_pow_lt_plusDet hy0.le hyU 5 (by norm_num)
  have hy6 := offset_pow_lt_plusDet hy0.le hyU 6 (by norm_num)
  have hy7 := offset_pow_lt_plusDet hy0.le hyU 7 (by norm_num)
  have hy8 := offset_pow_lt_plusDet hy0.le hyU 8 (by norm_num)
  have hy9 := offset_pow_lt_plusDet hy0.le hyU 9 (by norm_num)
  have hy10 := offset_pow_lt_plusDet hy0.le hyU 10 (by norm_num)
  have htauy : tau = 116992 / 100000 + y := by dsimp only [y]; ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  unfold intrinsicAlternatingCorrelation
  rw [plusDetAlternatingQH4_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9, hy10,
    sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6, pow_nonneg hy0.le 7,
    pow_nonneg hy0.le 8, pow_nonneg hy0.le 9, pow_nonneg hy0.le 10]

private theorem plusDetAlternatingPrimeCorrelationW_bounds :
    (852879 / 50000 : ℝ) <
        intrinsicAlternatingCorrelation plusDetAlternatingQW
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation plusDetAlternatingQW
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (1705771 / 100000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 1169925 / 1000000
  have htau := factorTwoPrimeRatio_fine_bounds_plusDet
  have hy0 : 0 < y := by dsimp only [y, tau]; linarith [htau.1]
  have hyU : y < (1 / 1000000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := offset_pow_lt_plusDet hy0.le hyU 2 (by norm_num)
  have hy3 := offset_pow_lt_plusDet hy0.le hyU 3 (by norm_num)
  have hy4 := offset_pow_lt_plusDet hy0.le hyU 4 (by norm_num)
  have hy5 := offset_pow_lt_plusDet hy0.le hyU 5 (by norm_num)
  have hy6 := offset_pow_lt_plusDet hy0.le hyU 6 (by norm_num)
  have hy7 := offset_pow_lt_plusDet hy0.le hyU 7 (by norm_num)
  have hy8 := offset_pow_lt_plusDet hy0.le hyU 8 (by norm_num)
  have hy9 := offset_pow_lt_plusDet hy0.le hyU 9 (by norm_num)
  have hy10 := offset_pow_lt_plusDet hy0.le hyU 10 (by norm_num)
  have htauy : tau = 1169925 / 1000000 + y := by dsimp only [y]; ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  unfold intrinsicAlternatingCorrelation
  rw [plusDetAlternatingQW_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9, hy10,
    sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6, pow_nonneg hy0.le 7,
    pow_nonneg hy0.le 8, pow_nonneg hy0.le 9, pow_nonneg hy0.le 10]

private theorem log_three_div_sqrt_three_fine_bounds_plusDet :
    (6342841 / 10000000 : ℝ) < Real.log 3 / Real.sqrt 3 ∧
      Real.log 3 / Real.sqrt 3 < (6342842 / 10000000 : ℝ) := by
  have hlog2 := strict_log_two_fine_bounds
  have hlog32 := strict_log_three_halves_fine_bounds
  have hlog3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    calc
      Real.log 3 = Real.log (2 * (3 / 2 : ℝ)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hsSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsLower : (17320508 / 10000000 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hsUpper : Real.sqrt 3 < (17320509 / 10000000 : ℝ) := by
    nlinarith
  rw [lt_div_iff₀ hspos, div_lt_iff₀ hspos, hlog3]
  constructor <;> nlinarith

private theorem mul_strict_bounds_plusDet
    {a c aL aU cL cU : ℝ}
    (ha : aL < a ∧ a < aU) (hc : cL < c ∧ c < cU)
    (haL0 : 0 < aL) (hcL0 : 0 < cL) :
    aL * cL < a * c ∧ a * c < aU * cU := by
  have ha0 : 0 < a := haL0.trans ha.1
  have hc0 : 0 < c := hcL0.trans hc.1
  have haU0 : 0 < aU := ha0.trans ha.2
  constructor
  · calc
      aL * cL < a * cL := mul_lt_mul_of_pos_right ha.1 hcL0
      _ < a * c := mul_lt_mul_of_pos_left hc.1 ha0
  · calc
      a * c < aU * c := mul_lt_mul_of_pos_right ha.2 hc0
      _ < aU * cU := mul_lt_mul_of_pos_left hc.2 haU0

/-! ## Rational boxes for the four full sharp models -/

private theorem plusDetAlternatingSharpModelH2_bounds :
    (4681 / 50000 : ℝ) <
        plusDetAlternatingSharpModel plusDetAlternatingQH2 ∧
      plusDetAlternatingSharpModel plusDetAlternatingQH2 <
        (4756 / 50000 : ℝ) := by
  have herr := abs_lt.mp abs_plusDetAlternatingSharpRegularErrorH2_lt
  have harch := plusDetAlternatingSharpArchModelH2_bounds
  have hcorr := plusDetAlternatingPrimeCorrelationH2_bounds
  have hbeta := log_three_div_sqrt_three_fine_bounds_plusDet
  have hnegcorr :
      (574021 / 100000 : ℝ) <
          -intrinsicAlternatingCorrelation plusDetAlternatingQH2
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
        -intrinsicAlternatingCorrelation plusDetAlternatingQH2
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (574037 / 100000 : ℝ) := by
    constructor <;> linarith [hcorr.1, hcorr.2]
  have hprod := mul_strict_bounds_plusDet hbeta hnegcorr
    (by norm_num) (by norm_num)
  unfold plusDetAlternatingSharpModel
  constructor <;> nlinarith [hprod.1, hprod.2]

private theorem plusDetAlternatingSharpModelH3_bounds :
    (-5685 / 50000 : ℝ) <
        plusDetAlternatingSharpModel plusDetAlternatingQH3 ∧
      plusDetAlternatingSharpModel plusDetAlternatingQH3 <
        (-5555 / 50000 : ℝ) := by
  have herr := abs_lt.mp abs_plusDetAlternatingSharpRegularErrorH3_lt
  have harch := plusDetAlternatingSharpArchModelH3_bounds
  have hcorr := plusDetAlternatingPrimeCorrelationH3_bounds
  have hbeta := log_three_div_sqrt_three_fine_bounds_plusDet
  have hnegcorr :
      (1176096 / 100000 : ℝ) <
          -intrinsicAlternatingCorrelation plusDetAlternatingQH3
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
        -intrinsicAlternatingCorrelation plusDetAlternatingQH3
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (1176118 / 100000 : ℝ) := by
    constructor <;> linarith [hcorr.1, hcorr.2]
  have hprod := mul_strict_bounds_plusDet hbeta hnegcorr
    (by norm_num) (by norm_num)
  unfold plusDetAlternatingSharpModel
  constructor <;> nlinarith [hprod.1, hprod.2]

private theorem plusDetAlternatingSharpModelH4_bounds :
    (-35968 / 50000 : ℝ) <
        plusDetAlternatingSharpModel plusDetAlternatingQH4 ∧
      plusDetAlternatingSharpModel plusDetAlternatingQH4 <
        (-35917 / 50000 : ℝ) := by
  have herr := abs_lt.mp abs_plusDetAlternatingSharpRegularErrorH4_lt
  have harch := plusDetAlternatingSharpArchModelH4_bounds
  have hcorr := plusDetAlternatingPrimeCorrelationH4_bounds
  have hbeta := log_three_div_sqrt_three_fine_bounds_plusDet
  have hprod := mul_strict_bounds_plusDet hbeta hcorr
    (by norm_num) (by norm_num)
  unfold plusDetAlternatingSharpModel
  constructor <;> nlinarith [hprod.1, hprod.2]

private theorem plusDetAlternatingSharpModelW_bounds :
    (-11926 / 10000 : ℝ) <
        plusDetAlternatingSharpModel plusDetAlternatingQW ∧
      plusDetAlternatingSharpModel plusDetAlternatingQW <
        (-11898 / 10000 : ℝ) := by
  have herr := abs_lt.mp abs_plusDetAlternatingSharpRegularErrorW_lt
  have harch := plusDetAlternatingSharpArchModelW_bounds
  have hcorr := plusDetAlternatingPrimeCorrelationW_bounds
  have hbeta := log_three_div_sqrt_three_fine_bounds_plusDet
  have hprod := mul_strict_bounds_plusDet hbeta hcorr
    (by norm_num) (by norm_num)
  unfold plusDetAlternatingSharpModel
  constructor <;> nlinarith [hprod.1, hprod.2]

private theorem plusDetAlternatingSharpModelW_strong_lower :
    (-11917 / 10000 : ℝ) <
      plusDetAlternatingSharpModel plusDetAlternatingQW := by
  have herr := plusDetAlternatingSharpRegularErrorW_signed_lower
  have harch := plusDetAlternatingSharpArchModelW_bounds
  have hcorr := plusDetAlternatingPrimeCorrelationW_bounds
  have hbeta := log_three_div_sqrt_three_fine_bounds_plusDet
  have hprod := mul_strict_bounds_plusDet hbeta hcorr
    (by norm_num) (by norm_num)
  unfold plusDetAlternatingSharpModel
  nlinarith [hprod.2]

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
