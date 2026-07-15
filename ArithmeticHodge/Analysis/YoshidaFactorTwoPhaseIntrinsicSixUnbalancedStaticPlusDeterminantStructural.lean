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
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
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

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
