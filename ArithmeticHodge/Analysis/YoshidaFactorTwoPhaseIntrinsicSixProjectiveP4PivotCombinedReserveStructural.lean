import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural

noncomputable section

open MeasureTheory Polynomial Real Set
open CenteredEndpointCorrelation
open ThreeByThreeConvexPencil
open ThreeByThreePositiveMixedDiscriminant
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaConstantBounds
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4PrimeCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseSymmetricCarleman

/-!
# Combined structural reserve for the first two projective pivot coefficients

This module sharpens both endpoint lower Grams and the two combined negative
`P4` cross coordinates.  The proof is entirely by exact identities, analytic
inequalities, Loewner monotonicity, and rational arithmetic.
-/

private def plusLower00 : ℝ := 13836 / 100000
private def plusLower02 : ℝ := 13544 / 100000
private def plusLower22 : ℝ := 13817 / 100000

private def minusLower00 : ℝ := 59292 / 100000
private def minusLower02 : ℝ := 54506 / 100000
private def minusLower22 : ℝ := 51518 / 100000

private def plusP4Lower : ℝ := 3439 / 25000
def minusP4Lower : ℝ := 49065 / 100000

/-! ## Sharpened rational lower Grams -/

private def plusModelDefect00 : ℝ :=
  yoshidaEndpointEvenLowGram00 + evenPositivePerturbationTaylor00 - plusLower00

private def plusModelDefect02 : ℝ :=
  yoshidaEndpointEvenLowGram02 + evenPositivePerturbationTaylor02 - plusLower02

private def plusModelDefect22 : ℝ :=
  yoshidaEndpointEvenLowGram22 + evenPositivePerturbationTaylor22 - plusLower22

private theorem plusModelDefect_bounds :
    (57 / 1000000 : ℝ) < plusModelDefect00 ∧
      |plusModelDefect02| < (51 / 1000000 : ℝ) ∧
      (53 / 1000000 : ℝ) < plusModelDefect22 := by
  have hc00 := intrinsicEven_cleanGram00_gt
  have hc02 := intrinsicEven_cleanGram02_bounds
  have hc22 := intrinsicEven_cleanGram22_gt
  have ht := evenPositivePerturbationTaylor_ultra_bounds
  unfold plusModelDefect00 plusModelDefect02 plusModelDefect22
    plusLower00 plusLower02 plusLower22
  constructor
  · nlinarith
  constructor
  · rw [abs_lt]
    constructor <;> nlinarith
  · nlinarith

private theorem plusModelDefect_det_pos :
    0 < plusModelDefect00 * plusModelDefect22 - plusModelDefect02 ^ 2 := by
  rcases plusModelDefect_bounds with ⟨h00, h02, h22⟩
  have h00pos : 0 < plusModelDefect00 :=
    (by norm_num : (0 : ℝ) < 57 / 1000000).trans h00
  have hprod :
      (57 / 1000000 : ℝ) * (53 / 1000000) <
        plusModelDefect00 * plusModelDefect22 := by
    exact mul_lt_mul h00 h22.le (by norm_num) h00pos.le
  have h02' := (abs_lt.mp h02)
  have hsq : plusModelDefect02 ^ 2 < (51 / 1000000 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h02'.2)
      (by linarith : 0 < plusModelDefect02 + 51 / 1000000)]
  have hrat :
      (51 / 1000000 : ℝ) ^ 2 <
        (57 / 1000000) * (53 / 1000000) := by norm_num
  nlinarith

private theorem plusModelDefect_quadratic_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < plusModelDefect00 * c ^ 2 +
      2 * plusModelDefect02 * c * d + plusModelDefect22 * d ^ 2 := by
  exact real_twoByTwo_quadratic_pos _ _ _ c d
    ((by norm_num : (0 : ℝ) < 57 / 1000000).trans plusModelDefect_bounds.1)
    plusModelDefect_det_pos hne

private theorem plusCombinedModel_quadratic_le_exact (c d : ℝ) :
    (yoshidaEndpointEvenLowGram00 + evenPositivePerturbationTaylor00) * c ^ 2 +
        2 * (yoshidaEndpointEvenLowGram02 + evenPositivePerturbationTaylor02) *
          c * d +
        (yoshidaEndpointEvenLowGram22 + evenPositivePerturbationTaylor22) *
          d ^ 2 ≤
      factorTwoStructuralPhaseLow00 1 * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 1 * c * d +
        factorTwoStructuralPhaseLow22 1 * d ^ 2 := by
  have hpert := evenPositivePerturbationTaylor_quadratic_le c d
  have hclean :
      yoshidaEndpointOddCleanQuadratic (factorTwoEvenStructuralLowProfile c d) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2 := by
    simpa only [factorTwoEvenStructuralLowProfile] using
      yoshidaEndpointEvenLowGram_quadratic_eq_clean c d
  rw [factorTwoStructuralPhaseLow_endpoint_quadratic, hclean]
  nlinarith

private theorem plusLower_quadratic_le_exact (c d : ℝ) :
    plusLower00 * c ^ 2 + 2 * plusLower02 * c * d + plusLower22 * d ^ 2 ≤
      factorTwoStructuralPhaseLow00 1 * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 1 * c * d +
        factorTwoStructuralPhaseLow22 1 * d ^ 2 := by
  have hdef : 0 ≤ plusModelDefect00 * c ^ 2 +
      2 * plusModelDefect02 * c * d + plusModelDefect22 * d ^ 2 := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (plusModelDefect_quadratic_pos c d hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  have hmodel := plusCombinedModel_quadratic_le_exact c d
  unfold plusModelDefect00 plusModelDefect02 plusModelDefect22 at hdef
  nlinarith

private theorem plusLower_remainder_quadratic_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < (factorTwoStructuralPhaseLow00 1 - plusLower00) * c ^ 2 +
      2 * (factorTwoStructuralPhaseLow02 1 - plusLower02) * c * d +
      (factorTwoStructuralPhaseLow22 1 - plusLower22) * d ^ 2 := by
  have hstrict := plusModelDefect_quadratic_pos c d hne
  have hmodel := plusCombinedModel_quadratic_le_exact c d
  unfold plusModelDefect00 plusModelDefect02 plusModelDefect22 at hstrict
  nlinarith

private theorem negativeTaylor02_eq_neg_positiveTaylor02 :
    evenNegativePerturbationTaylor02 = -evenPositivePerturbationTaylor02 := by
  rw [show evenNegativePerturbationTaylor02 = step01Midpoint02 by rfl,
    step01Midpoint_eq_kernel_sub_positiveMoment.2.1]
  unfold evenPositivePerturbationTaylor02
  ring

private def minusModelDefect00 : ℝ :=
  yoshidaEndpointEvenLowGram00 + evenNegativePerturbationTaylor00 - minusLower00

private def minusModelDefect02 : ℝ :=
  yoshidaEndpointEvenLowGram02 + evenNegativePerturbationTaylor02 - minusLower02

private def minusModelDefect22 : ℝ :=
  yoshidaEndpointEvenLowGram22 + evenNegativePerturbationTaylor22 - minusLower22

private theorem minusModelDefect_bounds :
    (108 / 1000000 : ℝ) < minusModelDefect00 ∧
      |minusModelDefect02| < (51 / 1000000 : ℝ) ∧
      (59 / 1000000 : ℝ) < minusModelDefect22 := by
  have hc00 := intrinsicEven_cleanGram00_gt
  have hc02 := intrinsicEven_cleanGram02_bounds
  have hc22 := intrinsicEven_cleanGram22_gt
  have hm00 := step01Midpoint00_gt
  have hm22 := step01Midpoint22_gt
  have hn00 : (227278 / 1000000 : ℝ) - 3 / 4000 <
      evenNegativePerturbationTaylor00 := by
    unfold step01Midpoint00 at hm00
    nlinarith
  have hn22 : (188489 / 1000000 : ℝ) - 3 / 20000 <
      evenNegativePerturbationTaylor22 := by
    unfold step01Midpoint22 at hm22
    nlinarith
  have ht := evenPositivePerturbationTaylor_ultra_bounds
  unfold minusModelDefect00 minusModelDefect02 minusModelDefect22
    minusLower00 minusLower02 minusLower22 at ⊢
  rw [negativeTaylor02_eq_neg_positiveTaylor02]
  constructor
  · nlinarith
  constructor
  · rw [abs_lt]
    constructor <;> nlinarith
  · nlinarith

private theorem minusModelDefect_det_pos :
    0 < minusModelDefect00 * minusModelDefect22 - minusModelDefect02 ^ 2 := by
  rcases minusModelDefect_bounds with ⟨h00, h02, h22⟩
  have h00pos : 0 < minusModelDefect00 :=
    (by norm_num : (0 : ℝ) < 108 / 1000000).trans h00
  have hprod :
      (108 / 1000000 : ℝ) * (59 / 1000000) <
        minusModelDefect00 * minusModelDefect22 := by
    exact mul_lt_mul h00 h22.le (by norm_num) h00pos.le
  have h02' := abs_lt.mp h02
  have hsq : minusModelDefect02 ^ 2 < (51 / 1000000 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h02'.2)
      (by linarith : 0 < minusModelDefect02 + 51 / 1000000)]
  have hrat :
      (51 / 1000000 : ℝ) ^ 2 <
        (108 / 1000000) * (59 / 1000000) := by norm_num
  nlinarith

private theorem minusModelDefect_quadratic_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < minusModelDefect00 * c ^ 2 +
      2 * minusModelDefect02 * c * d + minusModelDefect22 * d ^ 2 := by
  exact real_twoByTwo_quadratic_pos _ _ _ c d
    ((by norm_num : (0 : ℝ) < 108 / 1000000).trans minusModelDefect_bounds.1)
    minusModelDefect_det_pos hne

private theorem minusCombinedModel_quadratic_le_exact (c d : ℝ) :
    (yoshidaEndpointEvenLowGram00 + evenNegativePerturbationTaylor00) * c ^ 2 +
        2 * (yoshidaEndpointEvenLowGram02 + evenNegativePerturbationTaylor02) *
          c * d +
        (yoshidaEndpointEvenLowGram22 + evenNegativePerturbationTaylor22) *
          d ^ 2 ≤
      factorTwoStructuralPhaseLow00 (-1) * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 (-1) * c * d +
        factorTwoStructuralPhaseLow22 (-1) * d ^ 2 := by
  have hpert := evenNegativePerturbationTaylor_quadratic_le c d
  have hclean :
      yoshidaEndpointOddCleanQuadratic (factorTwoEvenStructuralLowProfile c d) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2 := by
    simpa only [factorTwoEvenStructuralLowProfile] using
      yoshidaEndpointEvenLowGram_quadratic_eq_clean c d
  rw [factorTwoStructuralPhaseLow_endpoint_quadratic, hclean]
  nlinarith

private theorem minusLower_quadratic_le_exact (c d : ℝ) :
    minusLower00 * c ^ 2 + 2 * minusLower02 * c * d + minusLower22 * d ^ 2 ≤
      factorTwoStructuralPhaseLow00 (-1) * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 (-1) * c * d +
        factorTwoStructuralPhaseLow22 (-1) * d ^ 2 := by
  have hdef : 0 ≤ minusModelDefect00 * c ^ 2 +
      2 * minusModelDefect02 * c * d + minusModelDefect22 * d ^ 2 := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (minusModelDefect_quadratic_pos c d hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  have hmodel := minusCombinedModel_quadratic_le_exact c d
  unfold minusModelDefect00 minusModelDefect02 minusModelDefect22 at hdef
  nlinarith

private theorem minusLower_remainder_quadratic_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < (factorTwoStructuralPhaseLow00 (-1) - minusLower00) * c ^ 2 +
      2 * (factorTwoStructuralPhaseLow02 (-1) - minusLower02) * c * d +
      (factorTwoStructuralPhaseLow22 (-1) - minusLower22) * d ^ 2 := by
  have hstrict := minusModelDefect_quadratic_pos c d hne
  have hmodel := minusCombinedModel_quadratic_le_exact c d
  unfold minusModelDefect00 minusModelDefect02 minusModelDefect22 at hstrict
  nlinarith

/-! ## Sharp `P4` diagonal and combined negative cross boxes -/

private theorem plusP4Lower_lt_exact :
    plusP4Lower < factorTwoIntrinsicSixP4Diagonal 1 := by
  have hclean :=
    one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have hpert := factorTwoCenteredSymmetricPerturbation_p4_lower
  change plusP4Lower < factorTwoIntrinsicP4PhaseDiagonal 1
  unfold plusP4Lower factorTwoIntrinsicP4PhaseDiagonal
  norm_num at hclean hpert ⊢
  nlinarith

private theorem abs_poleFreeAnalyticError_correlation44_le :
    |poleFreeAnalyticError factorTwoIntrinsicP4Correlation44| ≤
      (1 / 12000 : ℝ) := by
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4Correlation44
      continuous_factorTwoIntrinsicP4Correlation44
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  simp_rw [centeredEndpointCorrelation_p4] at hcorr
  rw [integral_factorTwoCenteredP4_sq] at hcorr
  nlinarith

theorem minusP4Lower_lt_exact :
    minusP4Lower < factorTwoIntrinsicSixP4Diagonal (-1) := by
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let C : ℝ := factorTwoIntrinsicP4Correlation44
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hclean :=
    one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have heq := factorTwoIntrinsicP4_perturbation_structural_eq.2.2
  have herr := abs_poleFreeAnalyticError_correlation44_le
  have herrUpper : poleFreeAnalyticError factorTwoIntrinsicP4Correlation44 ≤
      (1 / 12000 : ℝ) := (le_abs_self _).trans herr
  have hlog := strict_log_two_fine_bounds.1
  have halpha := log_two_div_sqrt_two_kernel_lower
  have hbeta := log_three_div_sqrt_three_kernel_bounds.1
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    positivity
  have hC := factorTwoIntrinsicP4PrimeCorrelation44_bounds.1
  have hprime :
      (63427 / 100000 : ℝ) * (68143 / 1000000) < beta * C := by
    calc
      (63427 / 100000 : ℝ) * (68143 / 1000000) <
          beta * (68143 / 1000000) :=
        mul_lt_mul_of_pos_right hbeta (by norm_num)
      _ < beta * C := mul_lt_mul_of_pos_left hC hbeta0
  change minusP4Lower < factorTwoIntrinsicP4PhaseDiagonal (-1)
  unfold minusP4Lower factorTwoIntrinsicP4PhaseDiagonal
  rw [heq]
  unfold factorTwoIntrinsicP4PerturbationBase44
  dsimp only [beta, C] at hprime
  norm_num at hclean ⊢
  nlinarith

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
    factorTwoIntrinsicP4CorrelationSum
      hcont
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
    factorTwoIntrinsicP4CorrelationDifference
      hcont
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

private theorem minusCross_sharp_bounds :
    0 < factorTwoIntrinsicP4MinusCrossSum ∧
      factorTwoIntrinsicP4MinusCrossSum < (293088 / 1000000 : ℝ) ∧
      0 < factorTwoIntrinsicP4MinusCrossDifference ∧
      factorTwoIntrinsicP4MinusCrossDifference < (66510 / 1000000 : ℝ) := by
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
  have hpDiffU : pDiff < (1 / 10000 : ℝ) := by
    simpa only [pDiff] using hp.2.2.2
  have hlog := strict_log_two_fine_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbetaPos : 0 < beta := by
    dsimp only [beta]
    positivity
  have hprime := factorTwoIntrinsicP4PrimeCorrelation_sum_difference_bounds
  have hcsU : cs < (-29333 / 500000 : ℝ) := by
    simpa only [cs] using hprime.2.1
  have hcdU : cd < (56757 / 1000000 : ℝ) := by
    simpa only [cd] using hprime.2.2.2
  have hbetaCsU :
      beta * cs < (63427 / 100000 : ℝ) * (-29333 / 500000) := by
    calc
      beta * cs < beta * (-29333 / 500000) :=
        mul_lt_mul_of_pos_left hcsU hbetaPos
      _ < (63427 / 100000 : ℝ) * (-29333 / 500000) :=
        mul_lt_mul_of_neg_right hbeta.1 (by norm_num)
  have hcd0 : 0 < cd :=
    (by norm_num : (0 : ℝ) < 56755 / 1000000).trans hprime.2.2.1
  have hbetaCdU :
      beta * cd < (6343 / 10000 : ℝ) * (56757 / 1000000) := by
    calc
      beta * cd < (6343 / 10000 : ℝ) * cd :=
        mul_lt_mul_of_pos_right hbeta.2 hcd0
      _ < (6343 / 10000 : ℝ) * (56757 / 1000000) :=
        mul_lt_mul_of_pos_left hcdU (by norm_num)
  have hcoarse := factorTwoIntrinsicP4MinusCross_sum_difference_bounds
  rw [abs_lt] at hcleanS hcleanD herrSB herrDB
  refine ⟨hcoarse.1, ?_, hcoarse.2.2.1, ?_⟩
  · rw [hS]
    nlinarith
  · rw [hD]
    nlinarith

/-! ## Positive lower matrices and positive Loewner remainders -/

private theorem plusLower_gates :
    0 < plusLower00 ∧
      0 < leadingMinorTwo plusLower00 plusLower02 plusLower22 ∧
      0 < symmetricDeterminant
        plusLower00 plusLower02 (factorTwoIntrinsicFourP45Cross04 1)
        plusLower22 (factorTwoIntrinsicFourP45Cross24 1) plusP4Lower := by
  let S : ℝ := factorTwoIntrinsicP4PlusCrossSum
  let D : ℝ := factorTwoIntrinsicP4PlusCrossDifference
  have hS := factorTwoIntrinsicP4PlusCrossSum_bounds
  have hD := factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hSsq : S ^ 2 < (193 / 1000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hS.2 hS.1.le (by norm_num)
  have hDsq : D ^ 2 < (39 / 2000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hD.2 hD.1.le (by norm_num)
  have hSD : S * D < (193 / 1000 : ℝ) * (39 / 2000) := by
    calc
      S * D < (193 / 1000 : ℝ) * D :=
        mul_lt_mul_of_pos_right hS.2 hD.1
      _ < (193 / 1000 : ℝ) * (39 / 2000) :=
        mul_lt_mul_of_pos_left hD.2 (by norm_num)
  have h04 : factorTwoIntrinsicFourP45Cross04 1 = (S - D) / 2 := by
    dsimp only [S, D]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  have h24 : factorTwoIntrinsicFourP45Cross24 1 = (S + D) / 2 := by
    dsimp only [S, D]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  constructor
  · norm_num [plusLower00]
  constructor
  · norm_num [leadingMinorTwo, plusLower00, plusLower02, plusLower22]
  · rw [h04, h24]
    unfold symmetricDeterminant plusLower00 plusLower02 plusLower22 plusP4Lower
    dsimp only [S, D] at hSsq hDsq hSD ⊢
    nlinarith

private theorem minusLower_gates :
    0 < minusLower00 ∧
      0 < leadingMinorTwo minusLower00 minusLower02 minusLower22 ∧
      0 < symmetricDeterminant
        minusLower00 minusLower02 (factorTwoIntrinsicFourP45Cross04 (-1))
        minusLower22 (factorTwoIntrinsicFourP45Cross24 (-1)) minusP4Lower := by
  let S : ℝ := factorTwoIntrinsicP4MinusCrossSum
  let D : ℝ := factorTwoIntrinsicP4MinusCrossDifference
  have h := minusCross_sharp_bounds
  have hS : 0 < S ∧ S < (293088 / 1000000 : ℝ) := by
    simpa only [S] using ⟨h.1, h.2.1⟩
  have hD : 0 < D ∧ D < (66510 / 1000000 : ℝ) := by
    simpa only [D] using ⟨h.2.2.1, h.2.2.2⟩
  have hSsq : S ^ 2 < (293088 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hS.2 hS.1.le (by norm_num)
  have hDsq : D ^ 2 < (66510 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hD.2 hD.1.le (by norm_num)
  have hSD : S * D <
      (293088 / 1000000 : ℝ) * (66510 / 1000000) := by
    calc
      S * D < (293088 / 1000000 : ℝ) * D :=
        mul_lt_mul_of_pos_right hS.2 hD.1
      _ < (293088 / 1000000 : ℝ) * (66510 / 1000000) :=
        mul_lt_mul_of_pos_left hD.2 (by norm_num)
  have h04 : factorTwoIntrinsicFourP45Cross04 (-1) = (S - D) / 2 := by
    dsimp only [S, D]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  have h24 : factorTwoIntrinsicFourP45Cross24 (-1) = (S + D) / 2 := by
    dsimp only [S, D]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  constructor
  · norm_num [minusLower00]
  constructor
  · norm_num [leadingMinorTwo, minusLower00, minusLower02, minusLower22]
  · rw [h04, h24]
    unfold symmetricDeterminant minusLower00 minusLower02 minusLower22 minusP4Lower
    dsimp only [S, D] at hSsq hDsq hSD ⊢
    nlinarith

private theorem blockRemainder_gates_of_low_pos
    (q00 q01 q11 q22 l00 l01 l11 l22 : ℝ)
    (hlow : ∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
      0 < (q00 - l00) * c ^ 2 + 2 * (q01 - l01) * c * d +
        (q11 - l11) * d ^ 2)
    (h22 : l22 < q22) :
    0 < q00 - l00 ∧
      0 < leadingMinorTwo (q00 - l00) (q01 - l01) (q11 - l11) ∧
      0 < symmetricDeterminant
        (q00 - l00) (q01 - l01) 0 (q11 - l11) 0 (q22 - l22) := by
  apply leadingMinors_pos_of_symmetricQuadratic_pos
  intro x0 x1 x2 hne
  by_cases hlowne : x0 ≠ 0 ∨ x1 ≠ 0
  · have hlo := hlow x0 x1 hlowne
    have htail : 0 ≤ (q22 - l22) * x2 ^ 2 :=
      mul_nonneg (sub_nonneg.mpr h22.le) (sq_nonneg x2)
    unfold symmetricQuadratic
    nlinarith
  · push_neg at hlowne
    rcases hlowne with ⟨hx0, hx1⟩
    have hx2 : x2 ≠ 0 := by
      rcases hne with h | h | h
      · exact (h hx0).elim
      · exact (h hx1).elim
      · exact h
    have htail : 0 < (q22 - l22) * x2 ^ 2 :=
      mul_pos (sub_pos.mpr h22) (sq_pos_of_ne_zero hx2)
    subst x0
    subst x1
    simpa [symmetricQuadratic] using htail

private def plusExactMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoStructuralPhaseLow00 1)
    (factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicSixP4Diagonal 1)

private def minusExactMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoStructuralPhaseLow00 (-1))
    (factorTwoStructuralPhaseLow02 (-1))
    (factorTwoIntrinsicFourP45Cross04 (-1))
    (factorTwoStructuralPhaseLow22 (-1))
    (factorTwoIntrinsicFourP45Cross24 (-1))
    (factorTwoIntrinsicSixP4Diagonal (-1))

private def plusLowerMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3 plusLower00 plusLower02
    (factorTwoIntrinsicFourP45Cross04 1) plusLower22
    (factorTwoIntrinsicFourP45Cross24 1) plusP4Lower

private def minusLowerMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3 minusLower00 minusLower02
    (factorTwoIntrinsicFourP45Cross04 (-1)) minusLower22
    (factorTwoIntrinsicFourP45Cross24 (-1)) minusP4Lower

private def plusRemainderMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoStructuralPhaseLow00 1 - plusLower00)
    (factorTwoStructuralPhaseLow02 1 - plusLower02) 0
    (factorTwoStructuralPhaseLow22 1 - plusLower22) 0
    (factorTwoIntrinsicSixP4Diagonal 1 - plusP4Lower)

private def minusRemainderMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoStructuralPhaseLow00 (-1) - minusLower00)
    (factorTwoStructuralPhaseLow02 (-1) - minusLower02) 0
    (factorTwoStructuralPhaseLow22 (-1) - minusLower22) 0
    (factorTwoIntrinsicSixP4Diagonal (-1) - minusP4Lower)

private theorem plusExactMatrix_eq_add :
    plusExactMatrix = plusLowerMatrix + plusRemainderMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusExactMatrix, plusLowerMatrix, plusRemainderMatrix, symmetricMatrix3]

private theorem minusExactMatrix_eq_add :
    minusExactMatrix = minusLowerMatrix + minusRemainderMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusExactMatrix, minusLowerMatrix, minusRemainderMatrix, symmetricMatrix3]

private theorem plusLowerMatrix_posDef : plusLowerMatrix.PosDef := by
  exact symmetricMatrix3_posDef _ _ _ _ _ _
    plusLower_gates.1 plusLower_gates.2.1 plusLower_gates.2.2

private theorem minusLowerMatrix_posDef : minusLowerMatrix.PosDef := by
  exact symmetricMatrix3_posDef _ _ _ _ _ _
    minusLower_gates.1 minusLower_gates.2.1 minusLower_gates.2.2

private theorem plusRemainderMatrix_posDef : plusRemainderMatrix.PosDef := by
  have hgates := blockRemainder_gates_of_low_pos
    (q00 := factorTwoStructuralPhaseLow00 1)
    (q01 := factorTwoStructuralPhaseLow02 1)
    (q11 := factorTwoStructuralPhaseLow22 1)
    (q22 := factorTwoIntrinsicSixP4Diagonal 1)
    (l00 := plusLower00) (l01 := plusLower02) (l11 := plusLower22)
    (l22 := plusP4Lower) plusLower_remainder_quadratic_pos plusP4Lower_lt_exact
  exact symmetricMatrix3_posDef _ _ _ _ _ _ hgates.1 hgates.2.1 hgates.2.2

private theorem minusRemainderMatrix_posDef : minusRemainderMatrix.PosDef := by
  have hgates := blockRemainder_gates_of_low_pos
    (q00 := factorTwoStructuralPhaseLow00 (-1))
    (q01 := factorTwoStructuralPhaseLow02 (-1))
    (q11 := factorTwoStructuralPhaseLow22 (-1))
    (q22 := factorTwoIntrinsicSixP4Diagonal (-1))
    (l00 := minusLower00) (l01 := minusLower02) (l11 := minusLower22)
    (l22 := minusP4Lower) minusLower_remainder_quadratic_pos minusP4Lower_lt_exact
  exact symmetricMatrix3_posDef _ _ _ _ _ _ hgates.1 hgates.2.1 hgates.2.2

private theorem lower_mixed_one_lt_exact :
    mixedDeterminantOne
        plusLower00 plusLower02 (factorTwoIntrinsicFourP45Cross04 1)
        plusLower22 (factorTwoIntrinsicFourP45Cross24 1) plusP4Lower
        minusLower00 minusLower02 (factorTwoIntrinsicFourP45Cross04 (-1))
        minusLower22 (factorTwoIntrinsicFourP45Cross24 (-1)) minusP4Lower <
      mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 1) (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1) (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)
        (factorTwoStructuralPhaseLow00 (-1)) (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1)) := by
  have h := matrixMixedDeterminantOne_add_add_gt
    plusLowerMatrix_posDef plusRemainderMatrix_posDef
    minusLowerMatrix_posDef minusRemainderMatrix_posDef
  rw [← plusExactMatrix_eq_add, ← minusExactMatrix_eq_add] at h
  simpa [plusLowerMatrix, minusLowerMatrix, plusExactMatrix, minusExactMatrix,
    matrixMixedDeterminantOne_symmetricMatrix3] using h

private theorem lower_mixed_two_lt_exact :
    mixedDeterminantOne
        minusLower00 minusLower02 (factorTwoIntrinsicFourP45Cross04 (-1))
        minusLower22 (factorTwoIntrinsicFourP45Cross24 (-1)) minusP4Lower
        plusLower00 plusLower02 (factorTwoIntrinsicFourP45Cross04 1)
        plusLower22 (factorTwoIntrinsicFourP45Cross24 1) plusP4Lower <
      mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 (-1)) (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))
        (factorTwoStructuralPhaseLow00 1) (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1) (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1) := by
  have h := matrixMixedDeterminantOne_add_add_gt
    minusLowerMatrix_posDef minusRemainderMatrix_posDef
    plusLowerMatrix_posDef plusRemainderMatrix_posDef
  rw [← minusExactMatrix_eq_add, ← plusExactMatrix_eq_add] at h
  simpa [plusLowerMatrix, minusLowerMatrix, plusExactMatrix, minusExactMatrix,
    matrixMixedDeterminantOne_symmetricMatrix3] using h

/-! ## Exact rational weighted reserve -/

private theorem mul_lt_mul_of_positive_upper
    (x y X Y : ℝ) (_hx : 0 < x) (hxU : x < X)
    (hy : 0 < y) (hyU : y < Y) (hX : 0 < X) :
    x * y < X * Y := by
  calc
    x * y < X * y := mul_lt_mul_of_pos_right hxU hy
    _ < X * Y := mul_lt_mul_of_pos_left hyU hX

private theorem lower_weighted_reserve :
    (11 / 100000 : ℝ) <
      (157 / 1000 : ℝ) * mixedDeterminantOne
        plusLower00 plusLower02 (factorTwoIntrinsicFourP45Cross04 1)
        plusLower22 (factorTwoIntrinsicFourP45Cross24 1) plusP4Lower
        minusLower00 minusLower02 (factorTwoIntrinsicFourP45Cross04 (-1))
        minusLower22 (factorTwoIntrinsicFourP45Cross24 (-1)) minusP4Lower +
      (19 / 100 : ℝ) * mixedDeterminantOne
        minusLower00 minusLower02 (factorTwoIntrinsicFourP45Cross04 (-1))
        minusLower22 (factorTwoIntrinsicFourP45Cross24 (-1)) minusP4Lower
        plusLower00 plusLower02 (factorTwoIntrinsicFourP45Cross04 1)
        plusLower22 (factorTwoIntrinsicFourP45Cross24 1) plusP4Lower := by
  let Sp : ℝ := factorTwoIntrinsicP4PlusCrossSum
  let Dp : ℝ := factorTwoIntrinsicP4PlusCrossDifference
  let Sm : ℝ := factorTwoIntrinsicP4MinusCrossSum
  let Dm : ℝ := factorTwoIntrinsicP4MinusCrossDifference
  have hpS : 0 < Sp ∧ Sp < (193 / 1000 : ℝ) := by
    simpa only [Sp] using factorTwoIntrinsicP4PlusCrossSum_bounds
  have hpD : 0 < Dp ∧ Dp < (39 / 2000 : ℝ) := by
    simpa only [Dp] using factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hm := minusCross_sharp_bounds
  have hmS : 0 < Sm ∧ Sm < (293088 / 1000000 : ℝ) := by
    simpa only [Sm] using ⟨hm.1, hm.2.1⟩
  have hmD : 0 < Dm ∧ Dm < (66510 / 1000000 : ℝ) := by
    simpa only [Dm] using ⟨hm.2.2.1, hm.2.2.2⟩
  have hpSsq : Sp ^ 2 < (193 / 1000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hpS.2 hpS.1.le (by norm_num)
  have hpDsq : Dp ^ 2 < (39 / 2000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hpD.2 hpD.1.le (by norm_num)
  have hmSsq : Sm ^ 2 < (293088 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hmS.2 hmS.1.le (by norm_num)
  have hmDsq : Dm ^ 2 < (66510 / 1000000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hmD.2 hmD.1.le (by norm_num)
  have hpSD : Sp * Dp < (193 / 1000 : ℝ) * (39 / 2000) :=
    mul_lt_mul_of_positive_upper Sp Dp _ _ hpS.1 hpS.2 hpD.1 hpD.2 (by norm_num)
  have hmSD : Sm * Dm <
      (293088 / 1000000 : ℝ) * (66510 / 1000000) :=
    mul_lt_mul_of_positive_upper Sm Dm _ _ hmS.1 hmS.2 hmD.1 hmD.2 (by norm_num)
  have hpS_mS : Sp * Sm <
      (193 / 1000 : ℝ) * (293088 / 1000000) :=
    mul_lt_mul_of_positive_upper Sp Sm _ _ hpS.1 hpS.2 hmS.1 hmS.2 (by norm_num)
  have hpS_mD : Sp * Dm <
      (193 / 1000 : ℝ) * (66510 / 1000000) :=
    mul_lt_mul_of_positive_upper Sp Dm _ _ hpS.1 hpS.2 hmD.1 hmD.2 (by norm_num)
  have hpD_mS : Dp * Sm <
      (39 / 2000 : ℝ) * (293088 / 1000000) :=
    mul_lt_mul_of_positive_upper Dp Sm _ _ hpD.1 hpD.2 hmS.1 hmS.2 (by norm_num)
  have hpD_mD : Dp * Dm <
      (39 / 2000 : ℝ) * (66510 / 1000000) :=
    mul_lt_mul_of_positive_upper Dp Dm _ _ hpD.1 hpD.2 hmD.1 hmD.2 (by norm_num)
  have hp04 : factorTwoIntrinsicFourP45Cross04 1 = (Sp - Dp) / 2 := by
    dsimp only [Sp, Dp]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  have hp24 : factorTwoIntrinsicFourP45Cross24 1 = (Sp + Dp) / 2 := by
    dsimp only [Sp, Dp]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  have hm04 : factorTwoIntrinsicFourP45Cross04 (-1) = (Sm - Dm) / 2 := by
    dsimp only [Sm, Dm]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  have hm24 : factorTwoIntrinsicFourP45Cross24 (-1) = (Sm + Dm) / 2 := by
    dsimp only [Sm, Dm]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  rw [hp04, hp24, hm04, hm24]
  unfold mixedDeterminantOne plusLower00 plusLower02 plusLower22 plusP4Lower
    minusLower00 minusLower02 minusLower22 minusP4Lower
  dsimp only [Sp, Dp, Sm, Dm] at hpSsq hpDsq hmSsq hmDsq hpSD hmSD hpS_mS hpS_mD hpD_mS hpD_mD ⊢
  nlinarith

/-- The weighted reserve needed by the projective `C2` closure. -/
theorem pivotCoeff_weighted_reserve :
    (11 / 100000 : ℝ) <
      (157 / 1000 : ℝ) * pivotCoeff 1 +
        (19 / 100 : ℝ) * pivotCoeff 2 := by
  rw [pivotCoeff_one_eq_exact_mixed, pivotCoeff_two_eq_exact_mixed]
  nlinarith [lower_weighted_reserve, lower_mixed_one_lt_exact,
    lower_mixed_two_lt_exact]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural
