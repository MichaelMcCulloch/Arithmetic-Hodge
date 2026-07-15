import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedAlternatingModelsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural

noncomputable section

open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open CenteredEndpointCorrelation
open MeasureTheory Real Set
open YoshidaConstantBounds
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusPositive
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PrimeCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural positivity of the corrected negative static block

The even endpoint is discharged in the shared even-block module.  The
remaining work is the fraction-free odd Schur block.  Its first pivot is
isolated below using a deliberately weaker rational even lower form; this
keeps the `P0/P2/P4` and alternating correlations coupled until the final
exact Schur inequality.
-/

/-! ## A correlated enclosure of the negative `P4` column -/

private theorem poleFreeAnalyticError_add
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    poleFreeAnalyticError C + poleFreeAnalyticError D =
      poleFreeAnalyticError (C + D) := by
  have hCI := intervalIntegrable_poleFreeAnalyticError C hC
  have hDI := intervalIntegrable_poleFreeAnalyticError D hD
  unfold poleFreeAnalyticError
  rw [← intervalIntegral.integral_add hCI hDI]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [Pi.add_apply]
  ring

private theorem poleFreeAnalyticError_sub
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    poleFreeAnalyticError C - poleFreeAnalyticError D =
      poleFreeAnalyticError (C - D) := by
  have hCI := intervalIntegrable_poleFreeAnalyticError C hC
  have hDI := intervalIntegrable_poleFreeAnalyticError D hD
  unfold poleFreeAnalyticError
  rw [← intervalIntegral.integral_sub hCI hDI]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [Pi.sub_apply]
  ring

private theorem abs_poleFreeAnalyticError_p4Sum_lt :
    |poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum| <
      (3 / 32000 : ℝ) := by
  have hcont : Continuous factorTwoIntrinsicP4CorrelationSum := by
    simpa only [factorTwoIntrinsicP4CorrelationSum] using
      continuous_factorTwoIntrinsicP4Correlation04.add
        continuous_factorTwoIntrinsicP4Correlation24
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4CorrelationSum hcont
  have hL1 := integral_abs_factorTwoIntrinsicP4CorrelationSum_lt
  nlinarith

private theorem abs_poleFreeAnalyticError_p4Difference_lt :
    |poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference| <
      (3 / 100000 : ℝ) := by
  have hcont : Continuous factorTwoIntrinsicP4CorrelationDifference := by
    simpa only [factorTwoIntrinsicP4CorrelationDifference] using
      continuous_factorTwoIntrinsicP4Correlation24.sub
        continuous_factorTwoIntrinsicP4Correlation04
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4CorrelationDifference hcont
  have hL1 := integral_abs_factorTwoIntrinsicP4CorrelationDifference_lt
  nlinarith

private def minusP4P6Sum : ℝ :=
  poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
    poleFreeCoeff6 yoshidaEndpointA * (32 / 99 + 32 / 315)

private def minusP4P6Difference : ℝ :=
  poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
    poleFreeCoeff6 yoshidaEndpointA * (32 / 99 - 32 / 315)

private theorem minusP4P6_bounds :
    0 ≤ minusP4P6Sum ∧ minusP4P6Sum < (1 / 10000 : ℝ) ∧
      0 ≤ minusP4P6Difference ∧
        minusP4P6Difference < (1 / 10000 : ℝ) := by
  rcases poleFree_coefficient_bounds with
    ⟨_h0l, _h0u, _h2l, _h2u, h4l, h4u, h6l, h6u⟩
  unfold minusP4P6Sum minusP4P6Difference
  norm_num at h4l h4u h6l h6u ⊢
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The two negative-endpoint `P4` coordinates are enclosed only after the
clean, regular-error, polynomial, archimedean, and retained-prime pieces
have been combined. -/
private theorem factorTwoIntrinsicP4MinusCross_refined_bounds :
    (2927 / 10000 : ℝ) < factorTwoIntrinsicP4MinusCrossSum ∧
      factorTwoIntrinsicP4MinusCrossSum < (2931 / 10000 : ℝ) ∧
      (662 / 10000 : ℝ) < factorTwoIntrinsicP4MinusCrossDifference ∧
      factorTwoIntrinsicP4MinusCrossDifference < (666 / 10000 : ℝ) := by
  let e04 : ℝ := poleFreeAnalyticError factorTwoIntrinsicP4Correlation04
  let e24 : ℝ := poleFreeAnalyticError factorTwoIntrinsicP4Correlation24
  let errS : ℝ := poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum
  let errD : ℝ :=
    poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let cs : ℝ := factorTwoIntrinsicP4CorrelationSum
    (factorTwoPrimeShift / yoshidaEndpointA)
  let cd : ℝ := factorTwoIntrinsicP4CorrelationDifference
    (factorTwoPrimeShift / yoshidaEndpointA)
  let pSum : ℝ := minusP4P6Sum
  let pDiff : ℝ := minusP4P6Difference
  have herrS : e04 + e24 = errS := by
    dsimp only [e04, e24, errS]
    simpa only [factorTwoIntrinsicP4CorrelationSum] using
      poleFreeAnalyticError_add factorTwoIntrinsicP4Correlation04
        factorTwoIntrinsicP4Correlation24
        continuous_factorTwoIntrinsicP4Correlation04
        continuous_factorTwoIntrinsicP4Correlation24
  have herrD : e24 - e04 = errD := by
    dsimp only [e04, e24, errD]
    simpa only [factorTwoIntrinsicP4CorrelationDifference] using
      poleFreeAnalyticError_sub factorTwoIntrinsicP4Correlation24
        factorTwoIntrinsicP4Correlation04
        continuous_factorTwoIntrinsicP4Correlation24
        continuous_factorTwoIntrinsicP4Correlation04
  rcases factorTwoIntrinsicP4_perturbation_structural_eq with
    ⟨h04, h24, _h44⟩
  have hSraw : factorTwoIntrinsicP4MinusCrossSum =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
          yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4) -
        (e04 + e24) - pSum - 72 + 104 * Real.log 2 + beta * cs := by
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    rw [h04, h24]
    dsimp only [e04, e24, pSum, beta, cs, minusP4P6Sum,
      factorTwoIntrinsicP4CorrelationSum]
    unfold factorTwoIntrinsicP4PerturbationBase04
      factorTwoIntrinsicP4PerturbationBase24
    ring
  have hS : factorTwoIntrinsicP4MinusCrossSum =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
          yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4) -
        errS - pSum - 72 + 104 * Real.log 2 + beta * cs := by
    rw [hSraw, herrS]
  have hDraw : factorTwoIntrinsicP4MinusCrossDifference =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
          yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4) -
        (e24 - e04) + pDiff + 158 / 3 - 76 * Real.log 2 + beta * cd := by
    unfold factorTwoIntrinsicP4MinusCrossDifference
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    rw [h04, h24]
    dsimp only [e04, e24, pDiff, beta, cd, minusP4P6Difference,
      factorTwoIntrinsicP4CorrelationDifference]
    unfold factorTwoIntrinsicP4PerturbationBase04
      factorTwoIntrinsicP4PerturbationBase24
    ring
  have hD : factorTwoIntrinsicP4MinusCrossDifference =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
          yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4) -
        errD + pDiff + 158 / 3 - 76 * Real.log 2 + beta * cd := by
    rw [hDraw, herrD]
  have hcleanS :=
    factorTwoIntrinsicP4CleanCross_sum_sub_seventeen_seventieths_abs_lt
  have hcleanD :=
    factorTwoIntrinsicP4CleanCross_difference_sub_three_seventieths_abs_lt
  have herrSB : |errS| < (3 / 32000 : ℝ) := by
    simpa only [errS] using abs_poleFreeAnalyticError_p4Sum_lt
  have herrDB : |errD| < (3 / 100000 : ℝ) := by
    simpa only [errD] using abs_poleFreeAnalyticError_p4Difference_lt
  have hp := minusP4P6_bounds
  have hpSum0 : 0 ≤ pSum := by simpa only [pSum] using hp.1
  have hpSumU : pSum < (1 / 10000 : ℝ) := by
    simpa only [pSum] using hp.2.1
  have hpDiff0 : 0 ≤ pDiff := by simpa only [pDiff] using hp.2.2.1
  have hpDiffU : pDiff < (1 / 10000 : ℝ) := by
    simpa only [pDiff] using hp.2.2.2
  have hlog := strict_log_two_fine_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbetaPos : 0 < beta := by
    dsimp only [beta]
    positivity
  have hprime := factorTwoIntrinsicP4PrimeCorrelation_sum_difference_bounds
  have hcsL : (-29337 / 500000 : ℝ) < cs := by
    simpa only [cs] using hprime.1
  have hcsU : cs < (-29333 / 500000 : ℝ) := by
    simpa only [cs] using hprime.2.1
  have hcdL : (56755 / 1000000 : ℝ) < cd := by
    simpa only [cd] using hprime.2.2.1
  have hcdU : cd < (56757 / 1000000 : ℝ) := by
    simpa only [cd] using hprime.2.2.2
  have hbetaCsL :
      (6343 / 10000 : ℝ) * (-29337 / 500000) < beta * cs := by
    calc
      _ < beta * (-29337 / 500000 : ℝ) :=
        mul_lt_mul_of_neg_right hbeta.2 (by norm_num)
      _ < beta * cs := mul_lt_mul_of_pos_left hcsL hbetaPos
  have hbetaCsU :
      beta * cs < (63427 / 100000 : ℝ) * (-29333 / 500000) := by
    calc
      beta * cs < beta * (-29333 / 500000 : ℝ) :=
        mul_lt_mul_of_pos_left hcsU hbetaPos
      _ < _ := mul_lt_mul_of_neg_right hbeta.1 (by norm_num)
  have hbetaCdL :
      (63427 / 100000 : ℝ) * (56755 / 1000000) < beta * cd := by
    calc
      _ < beta * (56755 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < beta * cd := mul_lt_mul_of_pos_left hcdL hbetaPos
  have hcd0 : 0 < cd := (by norm_num : (0 : ℝ) < 56755 / 1000000).trans hcdL
  have hbetaCdU :
      beta * cd < (6343 / 10000 : ℝ) * (56757 / 1000000) := by
    calc
      beta * cd < (6343 / 10000 : ℝ) * cd :=
        mul_lt_mul_of_pos_right hbeta.2 hcd0
      _ < _ := mul_lt_mul_of_pos_left hcdU (by norm_num)
  rw [abs_lt] at hcleanS hcleanD herrSB herrDB
  constructor
  · rw [hS]
    linarith
  constructor
  · rw [hS]
    linarith
  constructor
  · rw [hD]
    linarith
  · rw [hD]
    linarith

/-! ## The first fraction-free odd Schur pivot -/

private theorem factorTwoIntrinsicSixUnbalancedKMinus_firstColumn_bounds :
    (20077 / 50000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedKMinus01 +
          factorTwoIntrinsicSixUnbalancedKMinus21 ∧
      factorTwoIntrinsicSixUnbalancedKMinus01 +
          factorTwoIntrinsicSixUnbalancedKMinus21 < (80313 / 200000 : ℝ) ∧
      (2747 / 200000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedKMinus01 -
          factorTwoIntrinsicSixUnbalancedKMinus21 ∧
      factorTwoIntrinsicSixUnbalancedKMinus01 -
          factorTwoIntrinsicSixUnbalancedKMinus21 < (43 / 3125 : ℝ) ∧
      (1043 / 10000 : ℝ) < factorTwoIntrinsicSixUnbalancedKMinus41 ∧
      factorTwoIntrinsicSixUnbalancedKMinus41 < (529 / 5000 : ℝ) := by
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨hsL, hsU, hdL, hdU, _hs3L, _hs3U, _hd3L, _hd3U⟩
  have h41 := factorTwoIntrinsicFourP45Cross41_bounds
  unfold factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus41
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Expanded determinant of the rational `P0/P2/P4/P1` lower Gram in the
sum/difference coordinates of both coupled columns. -/
private def factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
    (S D s d k : ℝ) : ℝ :=
  (96085027857 / 125000000000000 : ℝ) -
    (82335071 / 10000000000) * k ^ 2 -
    (82419 / 312500) * d ^ 2 +
    (2343 / 125000) * s * d -
    (333 / 156250) * s ^ 2 -
    (10686997 / 100000000) * D ^ 2 -
    (303809 / 40000000) * S * D -
    (43179 / 50000000) * S ^ 2 -
    (27473 / 25000) * D * d * k +
    (781 / 20000) * D * s * k -
    (781 / 20000) * S * d * k +
    (111 / 12500) * S * s * k +
    (1 / 4) * D ^ 2 * s ^ 2 +
    (1 / 2) * S * D * s * d +
    (1 / 4) * S ^ 2 * d ^ 2

private theorem factorTwoIntrinsicSixUnbalancedTMinus11LowerGate_eq_schur
    (S D s d k : ℝ) :
    factorTwoIntrinsicSixUnbalancedTMinus11LowerGate S D s d k =
      symmetricDeterminant
          intrinsicStaticMinusEvenLower00
          intrinsicStaticMinusEvenLower02
          ((S - D) / 2)
          intrinsicStaticMinusEvenLower22
          ((S + D) / 2)
          factorTwoIntrinsicP4MinusDiagonalLower *
        intrinsicStaticMinusOddLower11 -
      adjugateQuadratic
          intrinsicStaticMinusEvenLower00
          intrinsicStaticMinusEvenLower02
          ((S - D) / 2)
          intrinsicStaticMinusEvenLower22
          ((S + D) / 2)
          factorTwoIntrinsicP4MinusDiagonalLower
          ((s + d) / 2) ((s - d) / 2) k := by
  unfold factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
    intrinsicStaticMinusEvenLower00 intrinsicStaticMinusEvenLower02
    intrinsicStaticMinusEvenLower22 intrinsicStaticMinusOddLower11
    factorTwoIntrinsicP4MinusDiagonalLower symmetricDeterminant
    adjugateQuadratic
  ring

set_option maxHeartbeats 1000000 in
private theorem factorTwoIntrinsicSixUnbalancedTMinus11LowerGate_pos_of_bounds
    {S D s d k : ℝ}
    (hS : (2927 / 10000 : ℝ) < S ∧ S < 2931 / 10000)
    (hD : (662 / 10000 : ℝ) < D ∧ D < 666 / 10000)
    (hs : (20077 / 50000 : ℝ) < s ∧ s < 80313 / 200000)
    (hd : (2747 / 200000 : ℝ) < d ∧ d < 43 / 3125)
    (hk : (1043 / 10000 : ℝ) < k ∧ k < 529 / 5000) :
    0 < factorTwoIntrinsicSixUnbalancedTMinus11LowerGate S D s d k := by
  have hS0 : 0 < S := (by norm_num : (0 : ℝ) < 2927 / 10000).trans hS.1
  have hD0 : 0 < D := (by norm_num : (0 : ℝ) < 662 / 10000).trans hD.1
  have hs0 : 0 < s := (by norm_num : (0 : ℝ) < 20077 / 50000).trans hs.1
  have hd0 : 0 < d := (by norm_num : (0 : ℝ) < 2747 / 200000).trans hd.1
  have hk0 : 0 < k := (by norm_num : (0 : ℝ) < 1043 / 10000).trans hk.1

  have hdkL : (2747 / 200000 : ℝ) * (1043 / 10000) < d * k :=
    mul_lt_mul hd.1 hk.1.le (by norm_num) hd0.le
  have hskU : s * k < (80313 / 200000 : ℝ) * (529 / 5000) :=
    mul_lt_mul hs.2 hk.2.le hk0 (by norm_num)
  have hDsdU : D * s * d <
      (666 / 10000 : ℝ) * (80313 / 200000) * (43 / 3125) := by
    have hDs : D * s < (666 / 10000 : ℝ) * (80313 / 200000) :=
      mul_lt_mul hD.2 hs.2.le hs0 (by norm_num)
    exact mul_lt_mul hDs hd.2.le hd0 (by positivity)
  have hd2U : d ^ 2 < (43 / 3125 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hd.2 hd0.le (by norm_num)
  have hSd2U : (S + 2931 / 10000) * d ^ 2 <
      (2 * (2931 / 10000 : ℝ)) * (43 / 3125) ^ 2 := by
    have hsum : S + 2931 / 10000 < 2 * (2931 / 10000 : ℝ) := by
      linarith [hS.2]
    calc
      (S + 2931 / 10000) * d ^ 2 <
          (2 * (2931 / 10000 : ℝ)) * d ^ 2 :=
        mul_lt_mul_of_pos_right hsum (sq_pos_of_pos hd0)
      _ ≤ (2 * (2931 / 10000 : ℝ)) * (43 / 3125) ^ 2 :=
        mul_le_mul_of_nonneg_left hd2U.le (by norm_num)
  let slopeS : ℝ :=
    -(303809 / 40000000) * D -
      (43179 / 50000000) * (S + 2931 / 10000) -
      (781 / 20000) * d * k +
      (111 / 12500) * s * k +
      (1 / 2) * D * s * d +
      (1 / 4) * (S + 2931 / 10000) * d ^ 2
  have hslopeS : slopeS < 0 := by
    dsimp only [slopeS]
    nlinarith [hS.1, hD.1, hdkL, hskU, hDsdU, hSd2U]
  have hchangeS :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate S D s d k -
          factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
            (2931 / 10000) D s d k =
        (S - 2931 / 10000) * slopeS := by
    dsimp only [slopeS]
    unfold factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
    ring
  have hstepS :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) D s d k ≤
        factorTwoIntrinsicSixUnbalancedTMinus11LowerGate S D s d k := by
    have hp : 0 ≤ (S - 2931 / 10000) * slopeS :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith [hS.2]) hslopeS.le
    linarith [hchangeS]

  have hDsumL : 2 * (662 / 10000 : ℝ) < D + 666 / 10000 := by
    linarith [hD.1]
  have hs2U : s ^ 2 < (80313 / 200000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hs.2 hs0.le (by norm_num)
  have hDsumS2U : (D + 666 / 10000) * s ^ 2 <
      (2 * (666 / 10000 : ℝ)) * (80313 / 200000) ^ 2 := by
    have hsum : D + 666 / 10000 < 2 * (666 / 10000 : ℝ) := by
      linarith [hD.2]
    calc
      (D + 666 / 10000) * s ^ 2 <
          (2 * (666 / 10000 : ℝ)) * s ^ 2 :=
        mul_lt_mul_of_pos_right hsum (sq_pos_of_pos hs0)
      _ ≤ (2 * (666 / 10000 : ℝ)) * (80313 / 200000) ^ 2 :=
        mul_le_mul_of_nonneg_left hs2U.le (by norm_num)
  have hSsdU : (2931 / 10000 : ℝ) * s * d <
      (2931 / 10000) * (80313 / 200000) * (43 / 3125) := by
    have hsd : s * d < (80313 / 200000 : ℝ) * (43 / 3125) :=
      mul_lt_mul hs.2 hd.2.le hd0 (by norm_num)
    simpa only [mul_assoc] using
      mul_lt_mul_of_pos_left hsd
        (by norm_num : (0 : ℝ) < 2931 / 10000)
  let slopeD : ℝ :=
    -(10686997 / 100000000) * (D + 666 / 10000) -
      (303809 / 40000000) * (2931 / 10000) -
      (27473 / 25000) * d * k +
      (781 / 20000) * s * k +
      (1 / 4) * (D + 666 / 10000) * s ^ 2 +
      (1 / 2) * (2931 / 10000) * s * d
  have hslopeD : slopeD < 0 := by
    dsimp only [slopeD]
    nlinarith [hDsumL, hdkL, hskU, hDsumS2U, hSsdU]
  have hchangeD :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) D s d k -
          factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
            (2931 / 10000) (666 / 10000) s d k =
        (D - 666 / 10000) * slopeD := by
    dsimp only [slopeD]
    unfold factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
    ring
  have hstepD :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) s d k ≤
        factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) D s d k := by
    have hp : 0 ≤ (D - 666 / 10000) * slopeD :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith [hD.2]) hslopeD.le
    linarith [hchangeD]

  have hDkL : (666 / 10000 : ℝ) * (1043 / 10000) <
      (666 / 10000) * k := mul_lt_mul_of_pos_left hk.1 (by norm_num)
  have hSkL : (2931 / 10000 : ℝ) * (1043 / 10000) <
      (2931 / 10000) * k := mul_lt_mul_of_pos_left hk.1 (by norm_num)
  let slopes : ℝ :=
    (2343 / 125000) * d -
      (333 / 156250) * (s + 20077 / 50000) +
      (781 / 20000) * (666 / 10000) * k +
      (111 / 12500) * (2931 / 10000) * k +
      (1 / 4) * (666 / 10000) ^ 2 * (s + 20077 / 50000) +
      (1 / 2) * (2931 / 10000) * (666 / 10000) * d
  have hslopes : 0 < slopes := by
    dsimp only [slopes]
    nlinarith [hd.1, hs.2, hDkL, hSkL]
  have hchanges :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) s d k -
          factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
            (2931 / 10000) (666 / 10000) (20077 / 50000) d k =
        (s - 20077 / 50000) * slopes := by
    dsimp only [slopes]
    unfold factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
    ring
  have hsteps :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) (20077 / 50000) d k ≤
        factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) s d k := by
    have hp : 0 ≤ (s - 20077 / 50000) * slopes :=
      mul_nonneg (by linarith [hs.1]) hslopes.le
    linarith [hchanges]

  let sloped : ℝ :=
    -(82419 / 312500) * (d + 43 / 3125) +
      (2343 / 125000) * (20077 / 50000) -
      (27473 / 25000) * (666 / 10000) * k -
      (781 / 20000) * (2931 / 10000) * k +
      (1 / 2) * (2931 / 10000) * (666 / 10000) * (20077 / 50000) +
      (1 / 4) * (2931 / 10000) ^ 2 * (d + 43 / 3125)
  have hsloped : sloped < 0 := by
    dsimp only [sloped]
    nlinarith [hd.1, hd.2, hDkL, hSkL]
  have hchanged :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) (20077 / 50000) d k -
          factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
            (2931 / 10000) (666 / 10000) (20077 / 50000) (43 / 3125) k =
        (d - 43 / 3125) * sloped := by
    dsimp only [sloped]
    unfold factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
    ring
  have hstepd :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) (20077 / 50000) (43 / 3125) k ≤
        factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) (20077 / 50000) d k := by
    have hp : 0 ≤ (d - 43 / 3125) * sloped :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith [hd.2]) hsloped.le
    linarith [hchanged]

  let slopek : ℝ :=
    -(82335071 / 10000000000) * (k + 529 / 5000) -
      (27473 / 25000) * (666 / 10000) * (43 / 3125) +
      (781 / 20000) * (666 / 10000) * (20077 / 50000) -
      (781 / 20000) * (2931 / 10000) * (43 / 3125) +
      (111 / 12500) * (2931 / 10000) * (20077 / 50000)
  have hslopek : slopek < 0 := by
    dsimp only [slopek]
    nlinarith [hk.1]
  have hchangek :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) (20077 / 50000) (43 / 3125) k -
          factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
            (2931 / 10000) (666 / 10000) (20077 / 50000) (43 / 3125)
              (529 / 5000) =
        (k - 529 / 5000) * slopek := by
    dsimp only [slopek]
    unfold factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
    ring
  have hstepk :
      factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) (20077 / 50000) (43 / 3125)
            (529 / 5000) ≤
        factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
          (2931 / 10000) (666 / 10000) (20077 / 50000) (43 / 3125) k := by
    have hp : 0 ≤ (k - 529 / 5000) * slopek :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith [hk.2]) hslopek.le
    linarith [hchangek]
  have hcorner : 0 < factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
      (2931 / 10000) (666 / 10000) (20077 / 50000) (43 / 3125)
        (529 / 5000) := by
    norm_num [factorTwoIntrinsicSixUnbalancedTMinus11LowerGate]
  linarith [hstepS, hstepD, hsteps, hstepd, hstepk, hcorner]

private theorem factorTwoIntrinsicSixUnbalancedTMinus11LowerGate_pos :
    0 < factorTwoIntrinsicSixUnbalancedTMinus11LowerGate
      factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
      (factorTwoIntrinsicSixUnbalancedKMinus01 +
        factorTwoIntrinsicSixUnbalancedKMinus21)
      (factorTwoIntrinsicSixUnbalancedKMinus01 -
        factorTwoIntrinsicSixUnbalancedKMinus21)
      factorTwoIntrinsicSixUnbalancedKMinus41 := by
  rcases factorTwoIntrinsicP4MinusCross_refined_bounds with
    ⟨hSL, hSU, hDL, hDU⟩
  rcases factorTwoIntrinsicSixUnbalancedKMinus_firstColumn_bounds with
    ⟨hsL, hsU, hdL, hdU, hkL, hkU⟩
  exact factorTwoIntrinsicSixUnbalancedTMinus11LowerGate_pos_of_bounds
    ⟨hSL, hSU⟩ ⟨hDL, hDU⟩ ⟨hsL, hsU⟩ ⟨hdL, hdU⟩ ⟨hkL, hkU⟩

private def minusThreeBilinear
    (e00 e02 e04 e22 e24 e44
      x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  x0 * (e00 * y0 + e02 * y2 + e04 * y4) +
    x2 * (e02 * y0 + e22 * y2 + e24 * y4) +
    x4 * (e04 * y0 + e24 * y2 + e44 * y4)

private theorem symmetricQuadratic_eq_minusThreeBilinear_self
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 =
      minusThreeBilinear e00 e02 e04 e22 e24 e44
        x0 x2 x4 x0 x2 x4 := by
  unfold symmetricQuadratic minusThreeBilinear
  ring_nf

private theorem symmetricQuadratic_add_minusThreeVector
    (e00 e02 e04 e22 e24 e44 x0 x2 x4 y0 y2 y4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (x0 + y0) (x2 + y2) (x4 + y4) =
      symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 +
        2 * minusThreeBilinear e00 e02 e04 e22 e24 e44
          x0 x2 x4 y0 y2 y4 +
        symmetricQuadratic e00 e02 e04 e22 e24 e44 y0 y2 y4 := by
  unfold symmetricQuadratic minusThreeBilinear
  ring_nf

private theorem symmetricQuadratic_scale_minusThreeVector
    (e00 e02 e04 e22 e24 e44 d x0 x2 x4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (d * x0) (d * x2) (d * x4) =
      d ^ 2 * symmetricQuadratic e00 e02 e04 e22 e24 e44 x0 x2 x4 := by
  unfold symmetricQuadratic
  ring_nf

private theorem minusThreeBilinear_scale_left
    (e00 e02 e04 e22 e24 e44 d x0 x2 x4 y0 y2 y4 : ℝ) :
    minusThreeBilinear e00 e02 e04 e22 e24 e44
        (d * x0) (d * x2) (d * x4) y0 y2 y4 =
      d * minusThreeBilinear e00 e02 e04 e22 e24 e44
        x0 x2 x4 y0 y2 y4 := by
  unfold minusThreeBilinear
  ring_nf

private theorem minusThreeBilinear_adjugateVector
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 x0 x2 x4 : ℝ) :
    minusThreeBilinear e00 e02 e04 e22 e24 e44 x0 x2 x4
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 *
        (x0 * ell0 + x2 * ell2 + x4 * ell4) := by
  simp only [adjugateVector]
  unfold minusThreeBilinear symmetricDeterminant
  ring_nf

private theorem symmetricQuadratic_adjugateVector_minus
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 : ℝ) :
    symmetricQuadratic e00 e02 e04 e22 e24 e44
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 0)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 1)
        (adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 2) =
      symmetricDeterminant e00 e02 e04 e22 e24 e44 *
        adjugateQuadratic e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 := by
  rw [symmetricQuadratic_eq_minusThreeBilinear_self]
  rw [minusThreeBilinear_adjugateVector]
  simp only [adjugateVector]
  unfold adjugateQuadratic
  ring_nf

private theorem fractionFree_three_by_three_completion_minus
    (e00 e02 e04 e22 e24 e44 ell0 ell2 ell4 c0 c2 c4 r : ℝ) :
    let d := symmetricDeterminant e00 e02 e04 e22 e24 e44
    let v := adjugateVector e00 e02 e04 e22 e24 e44 ell0 ell2 ell4
    d ^ 2 *
        (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
          2 * (c0 * ell0 + c2 * ell2 + c4 * ell4) + r) =
      symmetricQuadratic e00 e02 e04 e22 e24 e44
          (d * c0 + v 0) (d * c2 + v 1) (d * c4 + v 2) +
        d * (d * r - adjugateQuadratic
          e00 e02 e04 e22 e24 e44 ell0 ell2 ell4) := by
  dsimp only
  rw [symmetricQuadratic_add_minusThreeVector]
  rw [symmetricQuadratic_scale_minusThreeVector]
  rw [minusThreeBilinear_scale_left]
  rw [minusThreeBilinear_adjugateVector]
  rw [symmetricQuadratic_adjugateVector_minus]
  ring_nf

private theorem three_by_one_fractionFree_completion
    (e00 e02 e04 e22 e24 e44 k0 k2 k4 o c0 c2 c4 c1 : ℝ) :
    let d := symmetricDeterminant e00 e02 e04 e22 e24 e44
    let v := adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4
    d ^ 2 * (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
        2 * (c0 * k0 + c2 * k2 + c4 * k4) * c1 + o * c1 ^ 2) =
      symmetricQuadratic e00 e02 e04 e22 e24 e44
        (d * c0 + v 0 * c1) (d * c2 + v 1 * c1)
        (d * c4 + v 2 * c1) +
      d *
        (d * o - adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4) *
        c1 ^ 2 := by
  have h := fractionFree_three_by_three_completion_minus
    e00 e02 e04 e22 e24 e44
    (k0 * c1) (k2 * c1) (k4 * c1) c0 c2 c4 (o * c1 ^ 2)
  have hv0 :
      adjugateVector e00 e02 e04 e22 e24 e44
          (k0 * c1) (k2 * c1) (k4 * c1) 0 =
        adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4 0 * c1 := by
    simp only [adjugateVector]
    ring_nf
  have hv2 :
      adjugateVector e00 e02 e04 e22 e24 e44
          (k0 * c1) (k2 * c1) (k4 * c1) 1 =
        adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4 1 * c1 := by
    simp only [adjugateVector]
    ring_nf
  have hv4 :
      adjugateVector e00 e02 e04 e22 e24 e44
          (k0 * c1) (k2 * c1) (k4 * c1) 2 =
        adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4 2 * c1 := by
    simp only [adjugateVector]
    ring_nf
  have hadj :
      adjugateQuadratic e00 e02 e04 e22 e24 e44
          (k0 * c1) (k2 * c1) (k4 * c1) =
        adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4 * c1 ^ 2 := by
    unfold adjugateQuadratic
    ring_nf
  dsimp only at h ⊢
  rw [hv0, hv2, hv4, hadj] at h
  ring_nf at h ⊢
  exact h

private theorem three_by_one_quadratic_pos_of_fractionFree
    (e00 e02 e04 e22 e24 e44 k0 k2 k4 o : ℝ)
    (he00 : 0 < e00)
    (heMinor : 0 < leadingMinorTwo e00 e02 e22)
    (heDet : 0 < symmetricDeterminant e00 e02 e04 e22 e24 e44)
    (hgate : 0 <
      symmetricDeterminant e00 e02 e04 e22 e24 e44 * o -
        adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4)
    (c0 c2 c4 c1 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0) :
    0 < symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
      2 * (c0 * k0 + c2 * k2 + c4 * k4) * c1 + o * c1 ^ 2 := by
  let detE := symmetricDeterminant e00 e02 e04 e22 e24 e44
  let v := adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4
  by_cases hc1 : c1 = 0
  · subst c1
    simp only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    apply symmetricQuadratic_pos e00 e02 e04 e22 e24 e44
      he00 heMinor heDet c0 c2 c4
    simpa using hne
  · have hEven : 0 ≤ symmetricQuadratic e00 e02 e04 e22 e24 e44
        (detE * c0 + v 0 * c1) (detE * c2 + v 1 * c1)
        (detE * c4 + v 2 * c1) :=
      symmetricQuadratic_nonneg e00 e02 e04 e22 e24 e44
        he00 heMinor heDet _ _ _
    have hgateSq : 0 <
        symmetricDeterminant e00 e02 e04 e22 e24 e44 *
          (symmetricDeterminant e00 e02 e04 e22 e24 e44 * o -
            adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4) *
          c1 ^ 2 :=
      mul_pos (mul_pos heDet hgate) (sq_pos_of_ne_zero hc1)
    have hid := three_by_one_fractionFree_completion
      e00 e02 e04 e22 e24 e44 k0 k2 k4 o c0 c2 c4 c1
    dsimp only [detE, v] at hEven hid
    have hscaled : 0 < symmetricDeterminant e00 e02 e04 e22 e24 e44 ^ 2 *
        (symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
          2 * (c0 * k0 + c2 * k2 + c4 * k4) * c1 + o * c1 ^ 2) := by
      rw [hid]
      exact add_pos_of_nonneg_of_pos hEven hgateSq
    rcases mul_pos_iff.mp hscaled with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge (sq_nonneg _)) hneg.1)

private def factorTwoIntrinsicSixUnbalancedTMinus11LowerQuadratic
    (c0 c2 c4 c1 : ℝ) : ℝ :=
  factorTwoIntrinsicP024MinusLowerQuadratic c0 c2 c4 +
    2 * (c0 * factorTwoIntrinsicSixUnbalancedKMinus01 +
      c2 * factorTwoIntrinsicSixUnbalancedKMinus21 +
      c4 * factorTwoIntrinsicSixUnbalancedKMinus41) * c1 +
    intrinsicStaticMinusOddLower11 * c1 ^ 2

private theorem factorTwoIntrinsicSixUnbalancedTMinus11LowerQuadratic_pos
    (c0 c2 c4 c1 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedTMinus11LowerQuadratic c0 c2 c4 c1 := by
  rcases intrinsicStaticMinusEvenLower_principal_minors_pos with
    ⟨he00, heMinor⟩
  have heDet : 0 < symmetricDeterminant
      intrinsicStaticMinusEvenLower00
      intrinsicStaticMinusEvenLower02
      (factorTwoIntrinsicFourP45Cross04 (-1))
      intrinsicStaticMinusEvenLower22
      (factorTwoIntrinsicFourP45Cross24 (-1))
      factorTwoIntrinsicP4MinusDiagonalLower := by
    have hadj := factorTwoIntrinsicP4MinusAdjugate_lt
    unfold symmetricDeterminant
    nlinarith
  have hS : factorTwoIntrinsicFourP45Cross04 (-1) =
      (factorTwoIntrinsicP4MinusCrossSum -
        factorTwoIntrinsicP4MinusCrossDifference) / 2 := by
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  have hD : factorTwoIntrinsicFourP45Cross24 (-1) =
      (factorTwoIntrinsicP4MinusCrossSum +
        factorTwoIntrinsicP4MinusCrossDifference) / 2 := by
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  have hk0 : factorTwoIntrinsicSixUnbalancedKMinus01 =
      ((factorTwoIntrinsicSixUnbalancedKMinus01 +
          factorTwoIntrinsicSixUnbalancedKMinus21) +
        (factorTwoIntrinsicSixUnbalancedKMinus01 -
          factorTwoIntrinsicSixUnbalancedKMinus21)) / 2 := by ring
  have hk2 : factorTwoIntrinsicSixUnbalancedKMinus21 =
      ((factorTwoIntrinsicSixUnbalancedKMinus01 +
          factorTwoIntrinsicSixUnbalancedKMinus21) -
        (factorTwoIntrinsicSixUnbalancedKMinus01 -
          factorTwoIntrinsicSixUnbalancedKMinus21)) / 2 := by ring
  have hgate := factorTwoIntrinsicSixUnbalancedTMinus11LowerGate_pos
  rw [factorTwoIntrinsicSixUnbalancedTMinus11LowerGate_eq_schur,
    ← hS, ← hD, ← hk0, ← hk2] at hgate
  unfold factorTwoIntrinsicSixUnbalancedTMinus11LowerQuadratic
    factorTwoIntrinsicP024MinusLowerQuadratic
  exact three_by_one_quadratic_pos_of_fractionFree
    intrinsicStaticMinusEvenLower00
    intrinsicStaticMinusEvenLower02
    (factorTwoIntrinsicFourP45Cross04 (-1))
    intrinsicStaticMinusEvenLower22
    (factorTwoIntrinsicFourP45Cross24 (-1))
    factorTwoIntrinsicP4MinusDiagonalLower
    factorTwoIntrinsicSixUnbalancedKMinus01
    factorTwoIntrinsicSixUnbalancedKMinus21
    factorTwoIntrinsicSixUnbalancedKMinus41
    intrinsicStaticMinusOddLower11 he00 heMinor heDet hgate
    c0 c2 c4 c1 hne

private def factorTwoIntrinsicSixUnbalancedTMinus11ExactQuadratic
    (c0 c2 c4 c1 : ℝ) : ℝ :=
  symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44 c0 c2 c4 +
    2 * (c0 * factorTwoIntrinsicSixUnbalancedKMinus01 +
      c2 * factorTwoIntrinsicSixUnbalancedKMinus21 +
      c4 * factorTwoIntrinsicSixUnbalancedKMinus41) * c1 +
    factorTwoIntrinsicSixUnbalancedOPlus11 * c1 ^ 2

private theorem factorTwoIntrinsicSixUnbalancedTMinus11Lower_le_exact
    (c0 c2 c4 c1 : ℝ) :
    factorTwoIntrinsicSixUnbalancedTMinus11LowerQuadratic c0 c2 c4 c1 ≤
      factorTwoIntrinsicSixUnbalancedTMinus11ExactQuadratic c0 c2 c4 c1 := by
  have hEven := factorTwoIntrinsicP024MinusLowerQuadratic_le_exact c0 c2 c4
  have hOdd := intrinsicStaticMinusOddLower_le c1 0
  have hOdd' : intrinsicStaticMinusOddLower11 * c1 ^ 2 ≤
      factorTwoIntrinsicSixUnbalancedOPlus11 * c1 ^ 2 := by
    simpa only [intrinsicStaticMinusOddLower,
      intrinsicStaticMinusOddLower11,
      factorTwoIntrinsicStaticOddQuadratic,
      factorTwoIntrinsicOddPhaseQuadratic,
      factorTwoIntrinsicSixUnbalancedOPlus11,
      factorTwoIntrinsicOddPhaseLow11,
      factorTwoIntrinsicOddPhaseLow13,
      factorTwoIntrinsicOddPhaseLow33,
      mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
      neg_neg, one_mul] using hOdd
  unfold factorTwoIntrinsicSixUnbalancedTMinus11LowerQuadratic
    factorTwoIntrinsicSixUnbalancedTMinus11ExactQuadratic
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
  linarith

private theorem factorTwoIntrinsicSixUnbalancedTMinus11ExactQuadratic_pos
    (c0 c2 c4 c1 : ℝ)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0) :
    0 < factorTwoIntrinsicSixUnbalancedTMinus11ExactQuadratic c0 c2 c4 c1 :=
  (factorTwoIntrinsicSixUnbalancedTMinus11LowerQuadratic_pos
    c0 c2 c4 c1 hne).trans_le
      (factorTwoIntrinsicSixUnbalancedTMinus11Lower_le_exact c0 c2 c4 c1)

private theorem fractionFree_gate_pos_of_quadratic_pos
    (e00 e02 e04 e22 e24 e44 k0 k2 k4 o : ℝ)
    (heDet : 0 < symmetricDeterminant e00 e02 e04 e22 e24 e44)
    (hquad : ∀ c0 c2 c4 c1 : ℝ,
      c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0 →
      0 < symmetricQuadratic e00 e02 e04 e22 e24 e44 c0 c2 c4 +
        2 * (c0 * k0 + c2 * k2 + c4 * k4) * c1 + o * c1 ^ 2) :
    0 < symmetricDeterminant e00 e02 e04 e22 e24 e44 * o -
      adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4 := by
  let detE := symmetricDeterminant e00 e02 e04 e22 e24 e44
  let v := adjugateVector e00 e02 e04 e22 e24 e44 k0 k2 k4
  have hne : -v 0 ≠ 0 ∨ -v 1 ≠ 0 ∨ -v 2 ≠ 0 ∨ detE ≠ 0 := by
    exact Or.inr (Or.inr (Or.inr (by dsimp only [detE]; positivity)))
  have h := hquad (-v 0) (-v 1) (-v 2) detE hne
  have hid :
      symmetricQuadratic e00 e02 e04 e22 e24 e44
          (-v 0) (-v 1) (-v 2) +
        2 * ((-v 0) * k0 + (-v 1) * k2 + (-v 2) * k4) * detE +
        o * detE ^ 2 =
      detE * (detE * o -
        adjugateQuadratic e00 e02 e04 e22 e24 e44 k0 k2 k4) := by
    dsimp only [detE, v]
    simp only [adjugateVector]
    unfold symmetricQuadratic symmetricDeterminant adjugateQuadratic
    ring
  rw [hid] at h
  rcases mul_pos_iff.mp h with hpos | hneg
  · exact hpos.2
  · exact False.elim ((not_lt_of_ge heDet.le) hneg.1)

/-- The first fraction-free Sylvester pivot of the corrected negative Schur
block is strictly positive.  The proof retains the coupled `P4` clean,
regular, archimedean, and prime pieces until their two aligned coordinates
have been assembled. -/
theorem factorTwoIntrinsicSixUnbalancedTMinus11_pos :
    0 < factorTwoIntrinsicSixUnbalancedTMinus11 := by
  have hE := factorTwoIntrinsicSixUnbalancedEMinus_positive
  have hgate : 0 <
      factorTwoIntrinsicSixUnbalancedEMinusDet *
          factorTwoIntrinsicSixUnbalancedOPlus11 -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEMinus00
          factorTwoIntrinsicSixUnbalancedEMinus02
          factorTwoIntrinsicSixUnbalancedEMinus04
          factorTwoIntrinsicSixUnbalancedEMinus22
          factorTwoIntrinsicSixUnbalancedEMinus24
          factorTwoIntrinsicSixUnbalancedEMinus44
          factorTwoIntrinsicSixUnbalancedKMinus01
          factorTwoIntrinsicSixUnbalancedKMinus21
          factorTwoIntrinsicSixUnbalancedKMinus41 := by
    apply fractionFree_gate_pos_of_quadratic_pos
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44
      factorTwoIntrinsicSixUnbalancedKMinus01
      factorTwoIntrinsicSixUnbalancedKMinus21
      factorTwoIntrinsicSixUnbalancedKMinus41
      factorTwoIntrinsicSixUnbalancedOPlus11
    · simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using hE.2.2
    · intro c0 c2 c4 c1 hne
      simpa only [factorTwoIntrinsicSixUnbalancedTMinus11ExactQuadratic] using
        factorTwoIntrinsicSixUnbalancedTMinus11ExactQuadratic_pos
          c0 c2 c4 c1 hne
  have hfrac := factorTwoIntrinsicSixUnbalancedTMinusQuadratic_eq_fractionFree
    1 0 0
  unfold factorTwoIntrinsicSixUnbalancedTMinusQuadratic symmetricQuadratic at hfrac
  norm_num at hfrac
  rw [hfrac]
  simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using hgate

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural
