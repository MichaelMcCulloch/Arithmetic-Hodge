import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualDualDirectStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualDualObstructionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Quantitative obstruction for the exact Galerkin residual dual

The direct module isolates the necessary `P11` scalar inequality.  This
follow-up keeps the production import stable while certifying the small
Galerkin pivot and the quantitative reversal.
-/

private theorem fourCellOddCoreLocalBilinear_fiveMode_fiveMode_local
    (c d e f g C D E F G : ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
        (fourCellOddOneThreeFiveSevenNineLowProfile C D E F G) =
      (fourCellOddFiveModeCoreExpression
          (c + C) (d + D) (e + E) (f + F) (g + G) -
        fourCellOddFiveModeCoreExpression c d e f g -
        fourCellOddFiveModeCoreExpression C D E F G) / 2 := by
  have hadd := fourCellOddCoreLocalQuadratic_add
    (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
    (fourCellOddOneThreeFiveSevenNineLowProfile C D E F G)
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g).continuous
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile C D E F G).continuous
  have hsum :
      fourCellOddOneThreeFiveSevenNineLowProfile c d e f g +
          fourCellOddOneThreeFiveSevenNineLowProfile C D E F G =
        fourCellOddOneThreeFiveSevenNineLowProfile
          (c + C) (d + D) (e + E) (f + F) (g + G) := by
    funext x
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply]
    ring
  rw [hsum,
    fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression,
    fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression,
    fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression] at hadd
  linarith

private theorem fiveMode_one_eq_local :
    fourCellOddOneThreeFiveSevenNineLowProfile 1 0 0 0 0 = centeredP1 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem exactGalerkinResidual_P1_row_expansion :
    fourCellOddCoreLocalBilinear
        fourCellOddP11GalerkinRetainedResidualProfile centeredP1 =
      fourCellOddOneThreeFivePerturbed11 -
        fourCellOddP11GalerkinRetainedSolution 0 *
          fourCellOddOneThreeFivePerturbed13 -
        fourCellOddP11GalerkinRetainedSolution 1 *
          fourCellOddOneThreeFivePerturbed15 -
        fourCellOddP11GalerkinRetainedSolution 2 *
          fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 -
        fourCellOddP11GalerkinRetainedSolution 3 *
          fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode_local
    1 (-fourCellOddP11GalerkinRetainedSolution 0)
      (-fourCellOddP11GalerkinRetainedSolution 1)
      (-fourCellOddP11GalerkinRetainedSolution 2)
      (-fourCellOddP11GalerkinRetainedSolution 3)
    1 0 0 0 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  ring_nf at h
  unfold fourCellOddP11GalerkinRetainedResidualProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  rw [fiveMode_one_eq_local] at h
  linarith

/-- The exact inverse-defined Galerkin pivot is below `9/2500`.  This is
the only pivot estimate needed for the scalar obstruction. -/
theorem fourCellOddCoreLocalQuadratic_exactGalerkinResidual_lt_nine_div_2500 :
    fourCellOddCoreLocalQuadratic
        fourCellOddP11GalerkinRetainedResidualProfile < (9 / 2500 : ℝ) := by
  rw [fourCellOddCoreLocalQuadratic_exactGalerkinResidual_eq_P1_row,
    exactGalerkinResidual_P1_row_expansion]
  rcases fourCellOddP11GalerkinRetainedSolution_coordinate_bounds with
    ⟨ha3lo, ha3hi, ha5lo, ha5hi, ha7lo, ha7hi, ha9lo, ha9hi⟩
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨h11lo, h11hi, h13lo, h13hi, _h33lo, _h33hi,
      h15lo, h15hi, _h35lo, _h35hi, _h55lo, _h55hi⟩
  rcases fourCellOddCoreLocalBilinear_P1_P7_bounds with
    ⟨h17lo, h17hi⟩
  rcases fourCellOddCoreLocalBilinear_P1_P9_bounds with
    ⟨h19lo, h19hi⟩
  have hprod13 :
      (114 / 100 : ℝ) * (218706 / 1000000) <
        fourCellOddP11GalerkinRetainedSolution 0 *
          fourCellOddOneThreeFivePerturbed13 := by
    calc
      (114 / 100 : ℝ) * (218706 / 1000000) <
          fourCellOddP11GalerkinRetainedSolution 0 *
            (218706 / 1000000) :=
        mul_lt_mul_of_pos_right ha3lo (by norm_num)
      _ < fourCellOddP11GalerkinRetainedSolution 0 *
          fourCellOddOneThreeFivePerturbed13 :=
        mul_lt_mul_of_pos_left h13lo (by linarith)
  have hneg5pos : 0 < -fourCellOddP11GalerkinRetainedSolution 1 := by
    linarith
  have hprod15 :
      (-fourCellOddP11GalerkinRetainedSolution 1) *
          fourCellOddOneThreeFivePerturbed15 <
        (23 / 100 : ℝ) * (135673 / 10000000) := by
    calc
      (-fourCellOddP11GalerkinRetainedSolution 1) *
          fourCellOddOneThreeFivePerturbed15 <
        (23 / 100 : ℝ) * fourCellOddOneThreeFivePerturbed15 :=
          mul_lt_mul_of_pos_right (by linarith) (by linarith)
      _ < (23 / 100 : ℝ) * (135673 / 10000000) :=
          mul_lt_mul_of_pos_left h15hi (by norm_num)
  have hneg7pos : 0 < -fourCellOddP11GalerkinRetainedSolution 2 := by
    linarith
  have hprod17 :
      (-fourCellOddP11GalerkinRetainedSolution 2) *
          fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 <
        (7 / 100 : ℝ) * (18 / 500) := by
    calc
      (-fourCellOddP11GalerkinRetainedSolution 2) *
          fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 <
        (7 / 100 : ℝ) *
          fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 :=
            mul_lt_mul_of_pos_right (by linarith) (by linarith)
      _ < (7 / 100 : ℝ) * (18 / 500) :=
        mul_lt_mul_of_pos_left h17hi (by norm_num)
  have hprod19 :
      (2 / 100 : ℝ) * (219 / 5000) <
        fourCellOddP11GalerkinRetainedSolution 3 *
          fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 := by
    calc
      (2 / 100 : ℝ) * (219 / 5000) <
          fourCellOddP11GalerkinRetainedSolution 3 * (219 / 5000) :=
        mul_lt_mul_of_pos_right ha9lo (by norm_num)
      _ < fourCellOddP11GalerkinRetainedSolution 3 *
          fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 :=
        mul_lt_mul_of_pos_left h19lo (by linarith)
  nlinarith

/-- The exact inverse-defined Galerkin pivot is strictly positive.  Together
with the preceding rational upper bound, this records the honest scale
`0 < Q(q₀) < 9 / 2500`; in particular, a lower bound such as `1 / 50`
would contradict the certified upper bound. -/
theorem fourCellOddCoreLocalQuadratic_exactGalerkinResidual_pos :
    0 < fourCellOddCoreLocalQuadratic
        fourCellOddP11GalerkinRetainedResidualProfile :=
  fourCellOddP11GalerkinRetainedSolution_residual_core_pos

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualDualObstructionStructural
