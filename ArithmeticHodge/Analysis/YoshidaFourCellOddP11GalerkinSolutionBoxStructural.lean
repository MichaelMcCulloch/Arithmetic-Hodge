import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinFiniteSolveStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ExplicitSelectorCauchyStructural

set_option autoImplicit false

open MeasureTheory Real Set Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinSolutionBoxStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP11ExplicitSelectorCauchyStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Rational box for the exact finite Galerkin solution

The proof uses the exact normal equation together with a rational approximate
inverse.  All error estimates are consequences of the public analytic boxes
for the core entries; no entry is sampled or numerically evaluated.
-/

private def approximateCenter : Fin 4 → ℝ :=
  ![(229 / 200 : ℝ), -(443 / 2000 : ℝ),
    -(53 / 1000 : ℝ), (51 / 2000 : ℝ)]

private def approximateInverse : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(571 / 100 : ℝ), -(94 / 100 : ℝ),
      -(103 / 100 : ℝ), -(126 / 100 : ℝ);
    -(94 / 100 : ℝ), (507 / 100 : ℝ),
      -(183 / 100 : ℝ), -(44 / 100 : ℝ);
    -(103 / 100 : ℝ), -(183 / 100 : ℝ),
      (547 / 100 : ℝ), (4 / 100 : ℝ);
    -(126 / 100 : ℝ), -(44 / 100 : ℝ),
      (4 / 100 : ℝ), (697 / 100 : ℝ)]

private theorem fourCellOddCoreLocalBilinear_fiveMode_fiveMode
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

private theorem fiveMode_three_eq :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0 = centeredP3 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem fiveMode_five_eq :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0 =
      factorTwoCenteredP5 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem fiveMode_seven_eq :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0 =
      factorTwoCenteredP7 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem fiveMode_nine_eq :
    fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1 =
      factorTwoCenteredP9 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem fiveMode_one_eq :
    fourCellOddOneThreeFiveSevenNineLowProfile 1 0 0 0 0 = centeredP1 := by
  funext x
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp

private theorem retainedGram_zero_zero :
    fourCellOddP11GalerkinRetainedGram 0 0 =
      fourCellOddOneThreeFivePerturbed33 := by
  have hdiag := fourCellOddCoreLocalBilinear_self_eq_quadratic
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0)
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0)
    (odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0)
  rw [fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression] at hdiag
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at hdiag
  norm_num at hdiag
  simpa [fourCellOddP11GalerkinRetainedGram] using hdiag

private theorem retainedGram_zero_one :
    fourCellOddP11GalerkinRetainedGram 0 1 =
      fourCellOddOneThreeFivePerturbed35 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode
    0 1 0 0 0 0 0 1 0 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  ring_nf at h
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0) = _
  exact h

private theorem retainedGram_one_one :
    fourCellOddP11GalerkinRetainedGram 1 1 =
      fourCellOddOneThreeFivePerturbed55 := by
  have hdiag := fourCellOddCoreLocalBilinear_self_eq_quadratic
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0)
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0)
    (odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0)
  rw [fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression] at hdiag
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at hdiag
  norm_num at hdiag
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0) = _
  exact hdiag

private theorem retainedGram_zero_two :
    fourCellOddP11GalerkinRetainedGram 0 2 =
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7 := by
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0) = _
  rw [fiveMode_three_eq, fiveMode_seven_eq]

private theorem retainedGram_zero_three :
    fourCellOddP11GalerkinRetainedGram 0 3 =
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9 := by
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1) = _
  rw [fiveMode_three_eq, fiveMode_nine_eq]

private theorem retainedGram_one_two :
    fourCellOddP11GalerkinRetainedGram 1 2 =
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP7 := by
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0) = _
  rw [fiveMode_five_eq, fiveMode_seven_eq]

private theorem retainedGram_one_three :
    fourCellOddP11GalerkinRetainedGram 1 3 =
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP9 := by
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1) = _
  rw [fiveMode_five_eq, fiveMode_nine_eq]

private theorem retainedGram_two_two :
    fourCellOddP11GalerkinRetainedGram 2 2 =
      fourCellOddCoreLocalQuadratic factorTwoCenteredP7 := by
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0) = _
  rw [fiveMode_seven_eq]
  apply fourCellOddCoreLocalBilinear_self_eq_quadratic
  · rw [← fiveMode_seven_eq]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0
  · exact odd_factorTwoCenteredP7

private theorem retainedGram_two_three :
    fourCellOddP11GalerkinRetainedGram 2 3 =
      fourCellOddCoreLocalBilinear factorTwoCenteredP7 factorTwoCenteredP9 := by
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1) = _
  rw [fiveMode_seven_eq, fiveMode_nine_eq]

private theorem retainedGram_three_three :
    fourCellOddP11GalerkinRetainedGram 3 3 =
      fourCellOddCoreLocalQuadratic factorTwoCenteredP9 := by
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1) = _
  rw [fiveMode_nine_eq]
  apply fourCellOddCoreLocalBilinear_self_eq_quadratic
  · rw [← fiveMode_nine_eq]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1
  · exact odd_factorTwoCenteredP9

private theorem retainedGram_one_zero :
    fourCellOddP11GalerkinRetainedGram 1 0 =
      fourCellOddOneThreeFivePerturbed35 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode
    0 0 1 0 0 0 1 0 0 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  ring_nf at h
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0) = _
  exact h

private theorem retainedGram_two_zero :
    fourCellOddP11GalerkinRetainedGram 2 0 =
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode
    0 0 0 1 0 0 1 0 0 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  ring_nf at h
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0) = _
  simpa [fiveMode_three_eq, fiveMode_seven_eq] using h

private theorem retainedGram_three_zero :
    fourCellOddP11GalerkinRetainedGram 3 0 =
      fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode
    0 0 0 0 1 0 1 0 0 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  ring_nf at h
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0) = _
  simpa [fiveMode_three_eq, fiveMode_nine_eq] using h

private theorem retainedGram_two_one :
    fourCellOddP11GalerkinRetainedGram 2 1 =
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP7 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode
    0 0 0 1 0 0 0 1 0 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  ring_nf at h
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0) = _
  simpa [fiveMode_five_eq, fiveMode_seven_eq] using h

private theorem retainedGram_three_one :
    fourCellOddP11GalerkinRetainedGram 3 1 =
      fourCellOddCoreLocalBilinear factorTwoCenteredP5 factorTwoCenteredP9 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode
    0 0 0 0 1 0 0 1 0 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  ring_nf at h
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0) = _
  simpa [fiveMode_five_eq, fiveMode_nine_eq] using h

private theorem retainedGram_three_two :
    fourCellOddP11GalerkinRetainedGram 3 2 =
      fourCellOddCoreLocalBilinear factorTwoCenteredP7 factorTwoCenteredP9 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode
    0 0 0 0 1 0 0 0 1 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  ring_nf at h
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1)
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0) = _
  simpa [fiveMode_seven_eq, fiveMode_nine_eq] using h

private theorem retainedRhs_zero :
    fourCellOddP11GalerkinRetainedRhs 0 =
      fourCellOddOneThreeFivePerturbed13 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode
    0 1 0 0 0 1 0 0 0 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 1 0 0 0)
    centeredP1 = _
  rwa [fiveMode_one_eq] at h

private theorem retainedRhs_one :
    fourCellOddP11GalerkinRetainedRhs 1 =
      fourCellOddOneThreeFivePerturbed15 := by
  have h := fourCellOddCoreLocalBilinear_fiveMode_fiveMode
    0 0 1 0 0 1 0 0 0 0
  unfold fourCellOddFiveModeCoreExpression
    fourCellOddOneThreeFivePerturbedQuadratic at h
  norm_num at h
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 1 0 0)
    centeredP1 = _
  rwa [fiveMode_one_eq] at h

private theorem retainedRhs_two :
    fourCellOddP11GalerkinRetainedRhs 2 =
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 := by
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 1 0) centeredP1 = _
  rw [fiveMode_seven_eq,
    fourCellOddCoreLocalBilinear_comm factorTwoCenteredP7 centeredP1]
  · rw [← fiveMode_seven_eq]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      0 0 0 1 0).continuous
  · unfold centeredP1
    fun_prop

private theorem retainedRhs_three :
    fourCellOddP11GalerkinRetainedRhs 3 =
      fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 := by
  change fourCellOddCoreLocalBilinear
    (fourCellOddOneThreeFiveSevenNineLowProfile 0 0 0 0 1) centeredP1 = _
  rw [fiveMode_nine_eq,
    fourCellOddCoreLocalBilinear_comm factorTwoCenteredP9 centeredP1]
  · rw [← fiveMode_nine_eq]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      0 0 0 0 1).continuous
  · unfold centeredP1
    fun_prop

private def solutionDeviation : Fin 4 → ℝ :=
  fourCellOddP11GalerkinRetainedSolution - approximateCenter

private def normalResidual : Fin 4 → ℝ :=
  fourCellOddP11GalerkinRetainedRhs -
    fourCellOddP11GalerkinRetainedGram *ᵥ approximateCenter

private def inverseError : Matrix (Fin 4) (Fin 4) ℝ :=
  1 - approximateInverse * fourCellOddP11GalerkinRetainedGram

set_option maxHeartbeats 1000000 in
private theorem solutionDeviation_fixedPoint :
    solutionDeviation =
      approximateInverse *ᵥ normalResidual +
        inverseError *ᵥ solutionDeviation := by
  have hnormal := fourCellOddP11GalerkinRetainedSolution_normalEquation
  have h₀ := congrFun hnormal 0
  have h₁ := congrFun hnormal 1
  have h₂ := congrFun hnormal 2
  have h₃ := congrFun hnormal 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₀ h₁ h₂ h₃
  funext i
  fin_cases i
  all_goals
    simp [solutionDeviation, normalResidual, inverseError,
      approximateCenter, approximateInverse, Matrix.mulVec,
      Matrix.vecMul, Matrix.one_apply, vecHead, vecTail,
      dotProduct, Fin.sum_univ_succ]
  · linear_combination
      (571 / 100 : ℝ) * h₀ - (94 / 100 : ℝ) * h₁ -
        (103 / 100 : ℝ) * h₂ - (126 / 100 : ℝ) * h₃
  · linear_combination
      -(94 / 100 : ℝ) * h₀ + (507 / 100 : ℝ) * h₁ -
        (183 / 100 : ℝ) * h₂ - (44 / 100 : ℝ) * h₃
  · linear_combination
      -(103 / 100 : ℝ) * h₀ - (183 / 100 : ℝ) * h₁ +
        (547 / 100 : ℝ) * h₂ + (4 / 100 : ℝ) * h₃
  · linear_combination
      -(126 / 100 : ℝ) * h₀ - (44 / 100 : ℝ) * h₁ +
        (4 / 100 : ℝ) * h₂ + (697 / 100 : ℝ) * h₃

private theorem normalResidual_zero_abs_lt :
    |normalResidual 0| < (31 / 100000 : ℝ) := by
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨_11lo, _11hi, h13lo, h13hi, h33lo, h33hi,
      _15lo, _15hi, h35lo, h35hi, h55lo, h55hi⟩
  rcases fourCellOddCoreLocalBilinear_P3_P7_bounds with ⟨h37lo, h37hi⟩
  rcases fourCellOddCoreLocalBilinear_P3_P9_bounds with ⟨h39lo, h39hi⟩
  rw [abs_lt]
  simp [normalResidual, approximateCenter, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, retainedGram_zero_zero, retainedGram_zero_one,
    retainedGram_zero_two, retainedGram_zero_three, retainedRhs_zero]
  constructor <;> nlinarith

private theorem normalResidual_one_abs_lt :
    |normalResidual 1| < (12 / 100000 : ℝ) := by
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨_11lo, _11hi, _13lo, _13hi, _33lo, _33hi,
      h15lo, h15hi, h35lo, h35hi, h55lo, h55hi⟩
  rcases fourCellOddCoreLocal_highCross_certificate_bounds with
    ⟨h57lo, h57hi, h59lo, h59hi, _79lo, _79hi⟩
  rw [abs_lt]
  simp [normalResidual, approximateCenter, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, retainedGram_one_zero, retainedGram_one_one,
    retainedGram_one_two, retainedGram_one_three, retainedRhs_one]
  constructor <;> nlinarith

private theorem normalResidual_two_abs_lt :
    |normalResidual 2| < (139 / 100000 : ℝ) := by
  rcases fourCellOddCoreLocalBilinear_P3_P7_bounds with ⟨h37lo, h37hi⟩
  rcases fourCellOddCoreLocal_highCross_certificate_bounds with
    ⟨h57lo, h57hi, _59lo, _59hi, h79lo, h79hi⟩
  rcases fourCellOddCoreLocalBilinear_P1_high_certificate_bounds with
    ⟨h17lo, h17hi, _19lo, _19hi⟩
  have h77lo := one_fifth_lt_fourCellOddCoreLocalQuadratic_P7
  have h77hi := fourCellOddCoreLocalQuadratic_P7_lt_one_fourth
  rw [abs_lt]
  simp [normalResidual, approximateCenter, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, retainedGram_two_zero, retainedGram_two_one,
    retainedGram_two_two, retainedGram_two_three, retainedRhs_two]
  constructor <;> nlinarith

private theorem normalResidual_three_abs_lt :
    |normalResidual 3| < (24 / 100000 : ℝ) := by
  rcases fourCellOddCoreLocalBilinear_P3_P9_bounds with ⟨h39lo, h39hi⟩
  rcases fourCellOddCoreLocal_highCross_certificate_bounds with
    ⟨_57lo, _57hi, h59lo, h59hi, h79lo, h79hi⟩
  rcases fourCellOddCoreLocalBilinear_P1_high_certificate_bounds with
    ⟨_17lo, _17hi, h19lo, h19hi⟩
  have h99lo := twenty_nine_two_hundredths_lt_fourCellOddCoreLocalQuadratic_P9
  have h99hi := fourCellOddCoreLocalQuadratic_P9_lt_four_twenty_fifths
  rw [abs_lt]
  simp [normalResidual, approximateCenter, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, retainedGram_three_zero, retainedGram_three_one,
    retainedGram_three_two, retainedGram_three_three, retainedRhs_three]
  constructor <;> nlinarith

private theorem approximateInverse_mulVec_normalResidual_zero_abs_lt :
    |(approximateInverse *ᵥ normalResidual) 0| < (37 / 10000 : ℝ) := by
  rcases (abs_lt.mp normalResidual_zero_abs_lt) with ⟨hz₀lo, hz₀hi⟩
  rcases (abs_lt.mp normalResidual_one_abs_lt) with ⟨hz₁lo, hz₁hi⟩
  rcases (abs_lt.mp normalResidual_two_abs_lt) with ⟨hz₂lo, hz₂hi⟩
  rcases (abs_lt.mp normalResidual_three_abs_lt) with ⟨hz₃lo, hz₃hi⟩
  rw [abs_lt]
  simp [approximateInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  constructor <;> nlinarith

private theorem approximateInverse_mulVec_normalResidual_one_abs_lt :
    |(approximateInverse *ᵥ normalResidual) 1| < (36 / 10000 : ℝ) := by
  rcases (abs_lt.mp normalResidual_zero_abs_lt) with ⟨hz₀lo, hz₀hi⟩
  rcases (abs_lt.mp normalResidual_one_abs_lt) with ⟨hz₁lo, hz₁hi⟩
  rcases (abs_lt.mp normalResidual_two_abs_lt) with ⟨hz₂lo, hz₂hi⟩
  rcases (abs_lt.mp normalResidual_three_abs_lt) with ⟨hz₃lo, hz₃hi⟩
  rw [abs_lt]
  simp [approximateInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  constructor <;> nlinarith

private theorem approximateInverse_mulVec_normalResidual_two_abs_lt :
    |(approximateInverse *ᵥ normalResidual) 2| < (82 / 10000 : ℝ) := by
  rcases (abs_lt.mp normalResidual_zero_abs_lt) with ⟨hz₀lo, hz₀hi⟩
  rcases (abs_lt.mp normalResidual_one_abs_lt) with ⟨hz₁lo, hz₁hi⟩
  rcases (abs_lt.mp normalResidual_two_abs_lt) with ⟨hz₂lo, hz₂hi⟩
  rcases (abs_lt.mp normalResidual_three_abs_lt) with ⟨hz₃lo, hz₃hi⟩
  rw [abs_lt]
  simp [approximateInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  constructor <;> nlinarith

private theorem approximateInverse_mulVec_normalResidual_three_abs_lt :
    |(approximateInverse *ᵥ normalResidual) 3| < (22 / 10000 : ℝ) := by
  rcases (abs_lt.mp normalResidual_zero_abs_lt) with ⟨hz₀lo, hz₀hi⟩
  rcases (abs_lt.mp normalResidual_one_abs_lt) with ⟨hz₁lo, hz₁hi⟩
  rcases (abs_lt.mp normalResidual_two_abs_lt) with ⟨hz₂lo, hz₂hi⟩
  rcases (abs_lt.mp normalResidual_three_abs_lt) with ⟨hz₃lo, hz₃hi⟩
  rw [abs_lt]
  simp [approximateInverse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  constructor <;> nlinarith

private def inverseErrorBound : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(17 / 10000 : ℝ), 7 / 10000, 27 / 1000, 1 / 100;
    1 / 2000, 11 / 10000, 46 / 1000, 19 / 5000;
    1 / 1000, 1 / 1250, 139 / 1000, 1 / 2000;
    11 / 10000, 3 / 5000, 3 / 2500, 53 / 1000]

set_option maxHeartbeats 1000000 in
private theorem inverseError_entry_abs_lt (i j : Fin 4) :
    |inverseError i j| < inverseErrorBound i j := by
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨_11lo, _11hi, h13lo, h13hi, h33lo, h33hi,
      h15lo, h15hi, h35lo, h35hi, h55lo, h55hi⟩
  rcases fourCellOddCoreLocalBilinear_P3_P7_bounds with ⟨h37lo, h37hi⟩
  rcases fourCellOddCoreLocalBilinear_P3_P9_bounds with ⟨h39lo, h39hi⟩
  rcases fourCellOddCoreLocal_highCross_certificate_bounds with
    ⟨h57lo, h57hi, h59lo, h59hi, h79lo, h79hi⟩
  have h77lo := one_fifth_lt_fourCellOddCoreLocalQuadratic_P7
  have h77hi := fourCellOddCoreLocalQuadratic_P7_lt_one_fourth
  have h99lo := twenty_nine_two_hundredths_lt_fourCellOddCoreLocalQuadratic_P9
  have h99hi := fourCellOddCoreLocalQuadratic_P9_lt_four_twenty_fifths
  fin_cases i <;> fin_cases j <;>
    rw [abs_lt] <;>
    simp [inverseError, inverseErrorBound, approximateInverse,
      Matrix.vecMul, Matrix.one_apply, dotProduct, Fin.sum_univ_succ,
      retainedGram_zero_zero, retainedGram_zero_one,
      retainedGram_zero_two, retainedGram_zero_three,
      retainedGram_one_zero, retainedGram_one_one,
      retainedGram_one_two, retainedGram_one_three,
      retainedGram_two_zero, retainedGram_two_one,
      retainedGram_two_two, retainedGram_two_three,
      retainedGram_three_zero, retainedGram_three_one,
      retainedGram_three_two, retainedGram_three_three] <;>
    constructor <;> nlinarith

private theorem abs_add_five_le (a b c d e : ℝ) :
    |a + (b + (c + (d + e)))| ≤
      |a| + |b| + |c| + |d| + |e| := by
  have h₀ := abs_add a (b + (c + (d + e)))
  have h₁ := abs_add b (c + (d + e))
  have h₂ := abs_add c (d + e)
  have h₃ := abs_add d e
  linarith

private theorem inverseError_mul_deviation_abs_le (i j : Fin 4) :
    |inverseError i j * solutionDeviation j| ≤
      inverseErrorBound i j * |solutionDeviation j| := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right
    (inverseError_entry_abs_lt i j).le (abs_nonneg _)

private theorem solutionDeviation_zero_row_bound :
    |solutionDeviation 0| ≤
      (37 / 10000 : ℝ) +
        (17 / 10000 : ℝ) * |solutionDeviation 0| +
        (7 / 10000 : ℝ) * |solutionDeviation 1| +
        (27 / 1000 : ℝ) * |solutionDeviation 2| +
        (1 / 100 : ℝ) * |solutionDeviation 3| := by
  have hfix := congrFun solutionDeviation_fixedPoint 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hfix
  rw [hfix]
  have htri := abs_add_five_le
    ((approximateInverse *ᵥ normalResidual) 0)
    (inverseError 0 0 * solutionDeviation 0)
    (inverseError 0 1 * solutionDeviation 1)
    (inverseError 0 2 * solutionDeviation 2)
    (inverseError 0 3 * solutionDeviation 3)
  have hm₀ := inverseError_mul_deviation_abs_le 0 0
  have hm₁ := inverseError_mul_deviation_abs_le 0 1
  have hm₂ := inverseError_mul_deviation_abs_le 0 2
  have hm₃ := inverseError_mul_deviation_abs_le 0 3
  simp [inverseErrorBound] at hm₀ hm₁ hm₂ hm₃
  linarith [approximateInverse_mulVec_normalResidual_zero_abs_lt.le]

private theorem solutionDeviation_one_row_bound :
    |solutionDeviation 1| ≤
      (36 / 10000 : ℝ) +
        (1 / 2000 : ℝ) * |solutionDeviation 0| +
        (11 / 10000 : ℝ) * |solutionDeviation 1| +
        (46 / 1000 : ℝ) * |solutionDeviation 2| +
        (19 / 5000 : ℝ) * |solutionDeviation 3| := by
  have hfix := congrFun solutionDeviation_fixedPoint 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hfix
  rw [hfix]
  have htri := abs_add_five_le
    ((approximateInverse *ᵥ normalResidual) 1)
    (inverseError 1 0 * solutionDeviation 0)
    (inverseError 1 1 * solutionDeviation 1)
    (inverseError 1 2 * solutionDeviation 2)
    (inverseError 1 3 * solutionDeviation 3)
  have hm₀ := inverseError_mul_deviation_abs_le 1 0
  have hm₁ := inverseError_mul_deviation_abs_le 1 1
  have hm₂ := inverseError_mul_deviation_abs_le 1 2
  have hm₃ := inverseError_mul_deviation_abs_le 1 3
  simp [inverseErrorBound] at hm₀ hm₁ hm₂ hm₃
  linarith [approximateInverse_mulVec_normalResidual_one_abs_lt.le]

private theorem solutionDeviation_two_row_bound :
    |solutionDeviation 2| ≤
      (82 / 10000 : ℝ) +
        (1 / 1000 : ℝ) * |solutionDeviation 0| +
        (1 / 1250 : ℝ) * |solutionDeviation 1| +
        (139 / 1000 : ℝ) * |solutionDeviation 2| +
        (1 / 2000 : ℝ) * |solutionDeviation 3| := by
  have hfix := congrFun solutionDeviation_fixedPoint 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hfix
  rw [hfix]
  have htri := abs_add_five_le
    ((approximateInverse *ᵥ normalResidual) 2)
    (inverseError 2 0 * solutionDeviation 0)
    (inverseError 2 1 * solutionDeviation 1)
    (inverseError 2 2 * solutionDeviation 2)
    (inverseError 2 3 * solutionDeviation 3)
  have hm₀ := inverseError_mul_deviation_abs_le 2 0
  have hm₁ := inverseError_mul_deviation_abs_le 2 1
  have hm₂ := inverseError_mul_deviation_abs_le 2 2
  have hm₃ := inverseError_mul_deviation_abs_le 2 3
  simp [inverseErrorBound] at hm₀ hm₁ hm₂ hm₃
  linarith [approximateInverse_mulVec_normalResidual_two_abs_lt.le]

private theorem solutionDeviation_three_row_bound :
    |solutionDeviation 3| ≤
      (22 / 10000 : ℝ) +
        (11 / 10000 : ℝ) * |solutionDeviation 0| +
        (3 / 5000 : ℝ) * |solutionDeviation 1| +
        (3 / 2500 : ℝ) * |solutionDeviation 2| +
        (53 / 1000 : ℝ) * |solutionDeviation 3| := by
  have hfix := congrFun solutionDeviation_fixedPoint 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hfix
  rw [hfix]
  have htri := abs_add_five_le
    ((approximateInverse *ᵥ normalResidual) 3)
    (inverseError 3 0 * solutionDeviation 0)
    (inverseError 3 1 * solutionDeviation 1)
    (inverseError 3 2 * solutionDeviation 2)
    (inverseError 3 3 * solutionDeviation 3)
  have hm₀ := inverseError_mul_deviation_abs_le 3 0
  have hm₁ := inverseError_mul_deviation_abs_le 3 1
  have hm₂ := inverseError_mul_deviation_abs_le 3 2
  have hm₃ := inverseError_mul_deviation_abs_le 3 3
  simp [inverseErrorBound] at hm₀ hm₁ hm₂ hm₃
  linarith [approximateInverse_mulVec_normalResidual_three_abs_lt.le]

private theorem solutionDeviation_abs_sum_lt :
    |solutionDeviation 0| + |solutionDeviation 1| +
        |solutionDeviation 2| + |solutionDeviation 3| <
      (23 / 1000 : ℝ) := by
  have h₀ := solutionDeviation_zero_row_bound
  have h₁ := solutionDeviation_one_row_bound
  have h₂ := solutionDeviation_two_row_bound
  have h₃ := solutionDeviation_three_row_bound
  have ha₀ := abs_nonneg (solutionDeviation 0)
  have ha₁ := abs_nonneg (solutionDeviation 1)
  have ha₂ := abs_nonneg (solutionDeviation 2)
  have ha₃ := abs_nonneg (solutionDeviation 3)
  have hcontract :
      |solutionDeviation 0| + |solutionDeviation 1| +
          |solutionDeviation 2| + |solutionDeviation 3| ≤
        (177 / 10000 : ℝ) + (107 / 500 : ℝ) *
          (|solutionDeviation 0| + |solutionDeviation 1| +
            |solutionDeviation 2| + |solutionDeviation 3|) := by
    nlinarith
  nlinarith

private theorem solutionDeviation_component_abs_bounds :
    |solutionDeviation 0| < (1 / 200 : ℝ) ∧
    |solutionDeviation 1| < (1 / 200 : ℝ) ∧
    |solutionDeviation 2| < (3 / 250 : ℝ) ∧
    |solutionDeviation 3| < (7 / 2000 : ℝ) := by
  have hsum := solutionDeviation_abs_sum_lt
  have h₀ := solutionDeviation_zero_row_bound
  have h₁ := solutionDeviation_one_row_bound
  have h₂ := solutionDeviation_two_row_bound
  have h₃ := solutionDeviation_three_row_bound
  have ha₀ := abs_nonneg (solutionDeviation 0)
  have ha₁ := abs_nonneg (solutionDeviation 1)
  have ha₂ := abs_nonneg (solutionDeviation 2)
  have ha₃ := abs_nonneg (solutionDeviation 3)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Coarse exact coordinate box for the inverse-defined Galerkin
projection.  The proof uses only the public certified core-entry intervals.
-/
theorem fourCellOddP11GalerkinRetainedSolution_coordinate_bounds :
    (114 / 100 : ℝ) < fourCellOddP11GalerkinRetainedSolution 0 ∧
    fourCellOddP11GalerkinRetainedSolution 0 < (115 / 100 : ℝ) ∧
    -(23 / 100 : ℝ) < fourCellOddP11GalerkinRetainedSolution 1 ∧
    fourCellOddP11GalerkinRetainedSolution 1 < -(21 / 100 : ℝ) ∧
    -(7 / 100 : ℝ) < fourCellOddP11GalerkinRetainedSolution 2 ∧
    fourCellOddP11GalerkinRetainedSolution 2 < -(4 / 100 : ℝ) ∧
    (2 / 100 : ℝ) < fourCellOddP11GalerkinRetainedSolution 3 ∧
    fourCellOddP11GalerkinRetainedSolution 3 < (3 / 100 : ℝ) := by
  rcases solutionDeviation_component_abs_bounds with ⟨h₀, h₁, h₂, h₃⟩
  rw [abs_lt] at h₀ h₁ h₂ h₃
  simp [solutionDeviation, approximateCenter] at h₀ h₁ h₂ h₃
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The exact inverse-defined Galerkin residual. -/
def fourCellOddP11GalerkinRetainedResidualProfile : ℝ → ℝ :=
  fourCellOddP11GalerkinResidualProfile
    (fourCellOddP11GalerkinRetainedSolution 0)
    (fourCellOddP11GalerkinRetainedSolution 1)
    (fourCellOddP11GalerkinRetainedSolution 2)
    (fourCellOddP11GalerkinRetainedSolution 3)

def fourCellOddP11GalerkinResidualBernstein0 : ℝ :=
  1 + (3 / 2 : ℝ) * fourCellOddP11GalerkinRetainedSolution 0 -
    (15 / 8 : ℝ) * fourCellOddP11GalerkinRetainedSolution 1 +
    (35 / 16 : ℝ) * fourCellOddP11GalerkinRetainedSolution 2 -
    (315 / 128 : ℝ) * fourCellOddP11GalerkinRetainedSolution 3

def fourCellOddP11GalerkinResidualBernstein1 : ℝ :=
  1 + (7 / 8 : ℝ) * fourCellOddP11GalerkinRetainedSolution 0 +
    (5 / 16 : ℝ) * fourCellOddP11GalerkinRetainedSolution 1 -
    (175 / 64 : ℝ) * fourCellOddP11GalerkinRetainedSolution 2 +
    (105 / 16 : ℝ) * fourCellOddP11GalerkinRetainedSolution 3

def fourCellOddP11GalerkinResidualBernstein2 : ℝ :=
  1 + (1 / 4 : ℝ) * fourCellOddP11GalerkinRetainedSolution 0 +
    (19 / 16 : ℝ) * fourCellOddP11GalerkinRetainedSolution 1 -
    (7 / 16 : ℝ) * fourCellOddP11GalerkinRetainedSolution 2 -
    (63 / 8 : ℝ) * fourCellOddP11GalerkinRetainedSolution 3

def fourCellOddP11GalerkinResidualBernstein3 : ℝ :=
  1 - (3 / 8 : ℝ) * fourCellOddP11GalerkinRetainedSolution 0 +
    (3 / 4 : ℝ) * fourCellOddP11GalerkinRetainedSolution 1 +
    (19 / 8 : ℝ) * fourCellOddP11GalerkinRetainedSolution 2 +
    (9 / 2 : ℝ) * fourCellOddP11GalerkinRetainedSolution 3

def fourCellOddP11GalerkinResidualBernstein4 : ℝ :=
  1 - fourCellOddP11GalerkinRetainedSolution 0 -
    fourCellOddP11GalerkinRetainedSolution 1 -
    fourCellOddP11GalerkinRetainedSolution 2 -
    fourCellOddP11GalerkinRetainedSolution 3

/-- Exact degree-four Bernstein expansion in `x²` of the inverse-defined
residual. -/
theorem fourCellOddP11GalerkinRetainedResidualProfile_eq_bernstein
    (x : ℝ) :
    fourCellOddP11GalerkinRetainedResidualProfile x =
      x *
        (fourCellOddP11GalerkinResidualBernstein0 * (1 - x ^ 2) ^ 4 +
          4 * fourCellOddP11GalerkinResidualBernstein1 * x ^ 2 *
            (1 - x ^ 2) ^ 3 +
          6 * fourCellOddP11GalerkinResidualBernstein2 * (x ^ 2) ^ 2 *
            (1 - x ^ 2) ^ 2 +
          4 * fourCellOddP11GalerkinResidualBernstein3 * (x ^ 2) ^ 3 *
            (1 - x ^ 2) +
          fourCellOddP11GalerkinResidualBernstein4 * (x ^ 2) ^ 4) := by
  unfold fourCellOddP11GalerkinRetainedResidualProfile
    fourCellOddP11GalerkinResidualBernstein0
    fourCellOddP11GalerkinResidualBernstein1
    fourCellOddP11GalerkinResidualBernstein2
    fourCellOddP11GalerkinResidualBernstein3
    fourCellOddP11GalerkinResidualBernstein4
    fourCellOddP11GalerkinResidualProfile
    fourCellOddP11GalerkinLowProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  ring

theorem fourCellOddP11GalerkinResidualBernstein_coefficients_pos :
    0 < fourCellOddP11GalerkinResidualBernstein0 ∧
    0 < fourCellOddP11GalerkinResidualBernstein1 ∧
    0 < fourCellOddP11GalerkinResidualBernstein2 ∧
    0 < fourCellOddP11GalerkinResidualBernstein3 ∧
    0 < fourCellOddP11GalerkinResidualBernstein4 := by
  rcases fourCellOddP11GalerkinRetainedSolution_coordinate_bounds with
    ⟨ha₃lo, ha₃hi, ha₅lo, ha₅hi,
      ha₇lo, ha₇hi, ha₉lo, ha₉hi⟩
  unfold fourCellOddP11GalerkinResidualBernstein0
    fourCellOddP11GalerkinResidualBernstein1
    fourCellOddP11GalerkinResidualBernstein2
    fourCellOddP11GalerkinResidualBernstein3
    fourCellOddP11GalerkinResidualBernstein4
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The exact Galerkin residual has the positive ground-state sign on the
whole production half-interval. -/
theorem fourCellOddP11GalerkinRetainedResidualProfile_pos
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < fourCellOddP11GalerkinRetainedResidualProfile x := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hgap : 0 ≤ 1 - x ^ 2 := by nlinarith
  rcases fourCellOddP11GalerkinResidualBernstein_coefficients_pos with
    ⟨hb₀, hb₁, hb₂, hb₃, hb₄⟩
  rw [fourCellOddP11GalerkinRetainedResidualProfile_eq_bernstein]
  have h₀ : 0 ≤ fourCellOddP11GalerkinResidualBernstein0 *
      (1 - x ^ 2) ^ 4 := by positivity
  have h₁ : 0 ≤ 4 * fourCellOddP11GalerkinResidualBernstein1 *
      x ^ 2 * (1 - x ^ 2) ^ 3 := by positivity
  have h₂ : 0 ≤ 6 * fourCellOddP11GalerkinResidualBernstein2 *
      (x ^ 2) ^ 2 * (1 - x ^ 2) ^ 2 := by positivity
  have h₃ : 0 ≤ 4 * fourCellOddP11GalerkinResidualBernstein3 *
      (x ^ 2) ^ 3 * (1 - x ^ 2) := by positivity
  have h₄ : 0 < fourCellOddP11GalerkinResidualBernstein4 *
      (x ^ 2) ^ 4 := by positivity
  positivity

/-- The reflection-even endpoint-strip transform of the exact residual is
strictly positive on the normalized closed strip. -/
theorem fourCellOddEndpointStripEven_galerkinResidual_pos
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    0 < fourCellOddEndpointStripEven
      fourCellOddP11GalerkinRetainedResidualProfile z := by
  rcases hz with ⟨hzlo, hzhi⟩
  have hp0 : 0 < (4 / 5 : ℝ) + z / 5 := by nlinarith
  have hp1 : (4 / 5 : ℝ) + z / 5 ≤ 1 := by nlinarith
  have hm0 : 0 < (4 / 5 : ℝ) - z / 5 := by nlinarith
  have hm1 : (4 / 5 : ℝ) - z / 5 ≤ 1 := by nlinarith
  have hp := fourCellOddP11GalerkinRetainedResidualProfile_pos hp0 hp1
  have hm := fourCellOddP11GalerkinRetainedResidualProfile_pos hm0 hm1
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
  simpa only [sub_eq_add_neg] using (half_pos (add_pos hp hm))

def fourCellOddP11GalerkinStripOddBernstein0 : ℝ :=
  -(1 / 5 : ℝ) +
    (33 / 50 : ℝ) * fourCellOddP11GalerkinRetainedSolution 0 +
    (1203 / 5000 : ℝ) * fourCellOddP11GalerkinRetainedSolution 1 -
    (972587 / 1250000 : ℝ) * fourCellOddP11GalerkinRetainedSolution 2 -
    (41734881 / 50000000 : ℝ) *
      fourCellOddP11GalerkinRetainedSolution 3

def fourCellOddP11GalerkinStripOddBernstein1 : ℝ :=
  -(1 / 5 : ℝ) +
    (133 / 200 : ℝ) * fourCellOddP11GalerkinRetainedSolution 0 +
    (3239 / 10000 : ℝ) * fourCellOddP11GalerkinRetainedSolution 1 -
    (2621633 / 5000000 : ℝ) *
      fourCellOddP11GalerkinRetainedSolution 2 -
    (430467 / 625000 : ℝ) * fourCellOddP11GalerkinRetainedSolution 3

def fourCellOddP11GalerkinStripOddBernstein2 : ℝ :=
  -(1 / 5 : ℝ) +
    (67 / 100 : ℝ) * fourCellOddP11GalerkinRetainedSolution 0 +
    (20381 / 50000 : ℝ) * fourCellOddP11GalerkinRetainedSolution 1 -
    (317093 / 1250000 : ℝ) * fourCellOddP11GalerkinRetainedSolution 2 -
    (1306413 / 3125000 : ℝ) *
      fourCellOddP11GalerkinRetainedSolution 3

def fourCellOddP11GalerkinStripOddBernstein3 : ℝ :=
  -(1 / 5 : ℝ) +
    (27 / 40 : ℝ) * fourCellOddP11GalerkinRetainedSolution 0 +
    (6147 / 12500 : ℝ) * fourCellOddP11GalerkinRetainedSolution 1 +
    (21233 / 625000 : ℝ) * fourCellOddP11GalerkinRetainedSolution 2 -
    (12699 / 781250 : ℝ) * fourCellOddP11GalerkinRetainedSolution 3

def fourCellOddP11GalerkinStripOddBernstein4 : ℝ :=
  -(1 / 5 : ℝ) +
    (17 / 25 : ℝ) * fourCellOddP11GalerkinRetainedSolution 0 +
    (1801 / 3125 : ℝ) * fourCellOddP11GalerkinRetainedSolution 1 +
    (26461 / 78125 : ℝ) * fourCellOddP11GalerkinRetainedSolution 2 +
    (204317 / 390625 : ℝ) * fourCellOddP11GalerkinRetainedSolution 3

/-- Exact positive Bernstein expansion after factoring `-z` from the
reflection-odd endpoint-strip transform of the exact residual. -/
theorem neg_fourCellOddEndpointStripOdd_galerkinResidual_eq_bernstein
    (z : ℝ) :
    -fourCellOddEndpointStripOdd
        fourCellOddP11GalerkinRetainedResidualProfile z =
      z *
        (fourCellOddP11GalerkinStripOddBernstein0 * (1 - z ^ 2) ^ 4 +
          4 * fourCellOddP11GalerkinStripOddBernstein1 * z ^ 2 *
            (1 - z ^ 2) ^ 3 +
          6 * fourCellOddP11GalerkinStripOddBernstein2 * (z ^ 2) ^ 2 *
            (1 - z ^ 2) ^ 2 +
          4 * fourCellOddP11GalerkinStripOddBernstein3 * (z ^ 2) ^ 3 *
            (1 - z ^ 2) +
          fourCellOddP11GalerkinStripOddBernstein4 * (z ^ 2) ^ 4) := by
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    fourCellOddP11GalerkinRetainedResidualProfile
    fourCellOddP11GalerkinStripOddBernstein0
    fourCellOddP11GalerkinStripOddBernstein1
    fourCellOddP11GalerkinStripOddBernstein2
    fourCellOddP11GalerkinStripOddBernstein3
    fourCellOddP11GalerkinStripOddBernstein4
    fourCellOddP11GalerkinResidualProfile
    fourCellOddP11GalerkinLowProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP7_eq,
    factorTwoCenteredP9_eq, factorTwoCenteredP9_eq]
  ring

set_option maxHeartbeats 500000 in
theorem fourCellOddP11GalerkinStripOddBernstein_coefficients_pos :
    0 < fourCellOddP11GalerkinStripOddBernstein0 ∧
    0 < fourCellOddP11GalerkinStripOddBernstein1 ∧
    0 < fourCellOddP11GalerkinStripOddBernstein2 ∧
    0 < fourCellOddP11GalerkinStripOddBernstein3 ∧
    0 < fourCellOddP11GalerkinStripOddBernstein4 := by
  rcases fourCellOddP11GalerkinRetainedSolution_coordinate_bounds with
    ⟨ha₃lo, ha₃hi, ha₅lo, ha₅hi,
      ha₇lo, ha₇hi, ha₉lo, ha₉hi⟩
  unfold fourCellOddP11GalerkinStripOddBernstein0
    fourCellOddP11GalerkinStripOddBernstein1
    fourCellOddP11GalerkinStripOddBernstein2
    fourCellOddP11GalerkinStripOddBernstein3
    fourCellOddP11GalerkinStripOddBernstein4
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- On the positive normalized half-strip, the reflection-odd component of
the exact Galerkin residual has a fixed negative sign. -/
theorem fourCellOddEndpointStripOdd_galerkinResidual_neg
    {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    fourCellOddEndpointStripOdd
      fourCellOddP11GalerkinRetainedResidualProfile z < 0 := by
  have hz2 : 0 < z ^ 2 := sq_pos_of_pos hz
  have hgap : 0 ≤ 1 - z ^ 2 := by nlinarith
  rcases fourCellOddP11GalerkinStripOddBernstein_coefficients_pos with
    ⟨hb₀, hb₁, hb₂, hb₃, hb₄⟩
  rw [← neg_pos,
    neg_fourCellOddEndpointStripOdd_galerkinResidual_eq_bernstein]
  have h₀ : 0 ≤ fourCellOddP11GalerkinStripOddBernstein0 *
      (1 - z ^ 2) ^ 4 := by positivity
  have h₁ : 0 ≤ 4 * fourCellOddP11GalerkinStripOddBernstein1 *
      z ^ 2 * (1 - z ^ 2) ^ 3 := by positivity
  have h₂ : 0 ≤ 6 * fourCellOddP11GalerkinStripOddBernstein2 *
      (z ^ 2) ^ 2 * (1 - z ^ 2) ^ 2 := by positivity
  have h₃ : 0 ≤ 4 * fourCellOddP11GalerkinStripOddBernstein3 *
      (z ^ 2) ^ 3 * (1 - z ^ 2) := by positivity
  have h₄ : 0 < fourCellOddP11GalerkinStripOddBernstein4 *
      (z ^ 2) ^ 4 := by positivity
  positivity

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinSolutionBoxStructural
