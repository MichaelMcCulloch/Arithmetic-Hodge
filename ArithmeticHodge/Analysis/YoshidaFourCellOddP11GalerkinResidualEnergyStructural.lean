import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualEnergyStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFourCellOddP11CoreDiagonalBoundsStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP13AugmentedOptimalSelectorStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Energy budget for the exact old Galerkin residual

The exact residual is a six-mode selector with zero `P₁₁` coefficient.
Its positive-half mass is therefore diagonal in the shifted-Legendre
coordinates.  The public solution box gives a simple energy bound, which in
turn controls the full `L¹` norm of its symmetric correlation with `P₁₁`.
-/

private theorem exactResidual_eq_sixModeSelector :
    fourCellOddP11GalerkinRetainedResidualProfile =
      fourCellOddP13SixModeSelector
        1 (-fourCellOddP11GalerkinRetainedSolution 0)
          (-fourCellOddP11GalerkinRetainedSolution 1)
          (-fourCellOddP11GalerkinRetainedSolution 2)
          (-fourCellOddP11GalerkinRetainedSolution 3) 0 := by
  rw [show fourCellOddP11GalerkinRetainedResidualProfile =
      fourCellOddP11GalerkinResidualProfile
        (fourCellOddP11GalerkinRetainedSolution 0)
        (fourCellOddP11GalerkinRetainedSolution 1)
        (fourCellOddP11GalerkinRetainedSolution 2)
        (fourCellOddP11GalerkinRetainedSolution 3) by rfl,
    fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  funext x
  unfold fourCellOddP13SixModeSelector fourCellOddP13SixModeProfile
  simp

private theorem continuous_exactResidual :
    Continuous fourCellOddP11GalerkinRetainedResidualProfile := by
  rw [exactResidual_eq_sixModeSelector]
  exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous

private theorem odd_exactResidual :
    Function.Odd fourCellOddP11GalerkinRetainedResidualProfile := by
  unfold fourCellOddP11GalerkinRetainedResidualProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _

/-- The positive-half mass of `q0` in exact diagonal coordinates. -/
theorem integral_zero_one_fourCellOddP11GalerkinRetainedResidualProfile_sq :
    (∫ x : ℝ in 0..1,
      fourCellOddP11GalerkinRetainedResidualProfile x ^ 2) =
      (1 / 3 : ℝ) +
        fourCellOddP11GalerkinRetainedSolution 0 ^ 2 / 7 +
        fourCellOddP11GalerkinRetainedSolution 1 ^ 2 / 11 +
        fourCellOddP11GalerkinRetainedSolution 2 ^ 2 / 15 +
        fourCellOddP11GalerkinRetainedSolution 3 ^ 2 / 19 := by
  have hmass := integral_zero_one_fourCellOddP13SixModeSelector_sq
    1 (-fourCellOddP11GalerkinRetainedSolution 0)
      (-fourCellOddP11GalerkinRetainedSolution 1)
      (-fourCellOddP11GalerkinRetainedSolution 2)
      (-fourCellOddP11GalerkinRetainedSolution 3) 0
  rw [← exactResidual_eq_sixModeSelector] at hmass
  norm_num at hmass ⊢
  nlinarith

/-- Sharp simple norm budget used by the regular-kernel envelope. -/
theorem factorTwoIntrinsicEnergy_fourCellOddP11GalerkinRetainedResidualProfile_lt_two :
    factorTwoIntrinsicEnergy
      fourCellOddP11GalerkinRetainedResidualProfile < 2 := by
  rcases fourCellOddP11GalerkinRetainedSolution_coordinate_bounds with
    ⟨hs0lo, hs0hi, hs1lo, hs1hi, hs2lo, hs2hi, hs3lo, hs3hi⟩
  have hs0sq : fourCellOddP11GalerkinRetainedSolution 0 ^ 2 <
      (115 / 100 : ℝ) ^ 2 := by
    nlinarith
  have hs1sq : fourCellOddP11GalerkinRetainedSolution 1 ^ 2 <
      (23 / 100 : ℝ) ^ 2 := by
    nlinarith
  have hs2sq : fourCellOddP11GalerkinRetainedSolution 2 ^ 2 <
      (7 / 100 : ℝ) ^ 2 := by
    nlinarith
  have hs3sq : fourCellOddP11GalerkinRetainedSolution 3 ^ 2 <
      (3 / 100 : ℝ) ^ 2 := by
    nlinarith
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP11GalerkinRetainedResidualProfile continuous_exactResidual
      (Or.inr odd_exactResidual)
  unfold factorTwoIntrinsicEnergy
  rw [hfold,
    integral_zero_one_fourCellOddP11GalerkinRetainedResidualProfile_sq]
  nlinarith

/-- The general correlation `L¹` inequality and the exact `P₁₁` energy
give the stronger rational envelope `24 / 23 < 2`. -/
theorem integral_abs_exactResidual_P11_correlation_lt_twenty_four_div_twenty_three :
    (∫ t : ℝ in 0..2,
      |factorTwoCenteredCorrelationBilinear
        fourCellOddP11GalerkinRetainedResidualProfile
        fourCellOddP11DirectTail t|) < (24 / 23 : ℝ) := by
  have hL1 := integral_abs_factorTwoCenteredCorrelationBilinear_le_half_energy_add
    fourCellOddP11GalerkinRetainedResidualProfile fourCellOddP11DirectTail
    continuous_exactResidual contDiff_fourCellOddP11DirectTail.continuous
  have hq :=
    factorTwoIntrinsicEnergy_fourCellOddP11GalerkinRetainedResidualProfile_lt_two
  rw [factorTwoIntrinsicEnergy_fourCellOddP11DirectTail] at hL1
  linarith

/-- Convenient looser form matching the kernel-envelope interface. -/
theorem integral_abs_exactResidual_P11_correlation_lt_two :
    (∫ t : ℝ in 0..2,
      |factorTwoCenteredCorrelationBilinear
        fourCellOddP11GalerkinRetainedResidualProfile
        fourCellOddP11DirectTail t|) < 2 := by
  exact integral_abs_exactResidual_P11_correlation_lt_twenty_four_div_twenty_three.trans
    (by norm_num)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualEnergyStructural
