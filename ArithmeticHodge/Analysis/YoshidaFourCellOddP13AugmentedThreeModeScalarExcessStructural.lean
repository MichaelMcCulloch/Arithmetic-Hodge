import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorP13ObstructionStructural

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedThreeModeScalarExcessStructural

noncomputable section

open YoshidaFourCellOddP13AugmentedFiniteSolveStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddP13AugmentedOptimalSelectorP13ObstructionStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Rational closure of the three omitted-mode obstruction

The exact `P13/P15/P17` Bessel obstruction has ample scalar margin.  This
module records a deliberately coarse rational interface for the analytic
enclosures: it is enough to bound the exact augmented quadratic by
`9 / 10000` and the three signed omitted moments by
`-7 / 10000`, `13 / 10000`, and `9 / 10000`, respectively.

The proof below is exact rational algebra.  In particular, it contains no
grid, floating-point evaluation, or finite search.
-/

/-- Coarse signed rational moment bounds already force the strict
`P13/P15/P17` Bessel excess at `39 / 400`. -/
theorem threeModeBessel_excess_of_rational_bounds
    (a3 a5 a7 a9 a11 Q : ℝ)
    (hQ : Q < (9 / 10000 : ℝ))
    (h13 :
      fourCellOddP13AugmentedFirstOmittedMoment a3 a5 a7 a9 a11 <
        -(7 / 10000 : ℝ))
    (h15 : (13 / 10000 : ℝ) <
      fourCellOddP13AugmentedSecondOmittedMoment a3 a5 a7 a9 a11)
    (h17 : (9 / 10000 : ℝ) <
      fourCellOddP13AugmentedThirdOmittedMoment a3 a5 a7 a9 a11) :
    Q * (39 / 400 : ℝ) <
      fourCellOddP13AugmentedThreeOmittedModeBesselBudget
        a3 a5 a7 a9 a11 := by
  have h13sq : (7 / 10000 : ℝ) ^ 2 <
      fourCellOddP13AugmentedFirstOmittedMoment a3 a5 a7 a9 a11 ^ 2 := by
    nlinarith
  have h15sq : (13 / 10000 : ℝ) ^ 2 <
      fourCellOddP13AugmentedSecondOmittedMoment a3 a5 a7 a9 a11 ^ 2 := by
    nlinarith
  have h17sq : (9 / 10000 : ℝ) ^ 2 <
      fourCellOddP13AugmentedThirdOmittedMoment a3 a5 a7 a9 a11 ^ 2 := by
    nlinarith
  unfold fourCellOddP13AugmentedThreeOmittedModeBesselBudget
  nlinarith

/-- Exact-solution specialization: the four displayed rational enclosures
close the strict optimal-norm obstruction. -/
theorem exactSolution_threeModeBessel_obstruction_of_rational_bounds
    (hQ :
      fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) <
        (9 / 10000 : ℝ))
    (h13 :
      fourCellOddP13AugmentedFirstOmittedMoment
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4) <
        -(7 / 10000 : ℝ))
    (h15 : (13 / 10000 : ℝ) <
      fourCellOddP13AugmentedSecondOmittedMoment
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4))
    (h17 : (9 / 10000 : ℝ) <
      fourCellOddP13AugmentedThirdOmittedMoment
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4)) :
    fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) * (39 / 400) <
      fourCellOddP13AugmentedThreeOmittedModeBesselBudget
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4) := by
  exact threeModeBessel_excess_of_rational_bounds
    (fourCellOddP13AugmentedRetainedSolution 0)
    (fourCellOddP13AugmentedRetainedSolution 1)
    (fourCellOddP13AugmentedRetainedSolution 2)
    (fourCellOddP13AugmentedRetainedSolution 3)
    (fourCellOddP13AugmentedRetainedSolution 4)
    (fourCellOddCoreLocalQuadratic
      (fourCellOddP13AugmentedGalerkinResidualProfile
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4)))
    hQ h13 h15 h17

/-- The same four rational enclosures directly refute the full
`19 / 20` existential selector certificate. -/
theorem exactSolution_not_nineteenTwentieths_of_rational_bounds
    (hQ :
      fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) <
        (9 / 10000 : ℝ))
    (h13 :
      fourCellOddP13AugmentedFirstOmittedMoment
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4) <
        -(7 / 10000 : ℝ))
    (h15 : (13 / 10000 : ℝ) <
      fourCellOddP13AugmentedSecondOmittedMoment
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4))
    (h17 : (9 / 10000 : ℝ) <
      fourCellOddP13AugmentedThirdOmittedMoment
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4)) :
    ¬ FourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound
        (1 - (19 / 20 : ℝ) ^ 2)
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4) := by
  apply fourCellOddP13AugmentedExactSolution_not_nineteenTwentieths_of_threeModeBessel
  exact exactSolution_threeModeBessel_obstruction_of_rational_bounds
    hQ h13 h15 h17

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedThreeModeScalarExcessStructural
