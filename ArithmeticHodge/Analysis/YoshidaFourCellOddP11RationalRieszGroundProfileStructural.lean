import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinRieszStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11RationalRieszGroundProfileStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeStrictCoercivityStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11UniversalCoreCauchyStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# A positive rational profile near the odd Galerkin residual

The certified five-mode Gram block points to a residual close to

`P₁ - 1.14653 P₃ + 0.21885 P₅ + 0.06127 P₇ - 0.02692 P₉`.

This file fixes those rational coefficients and proves, without sampling,
that the resulting odd polynomial is strictly positive on `(0, 1]`.  The
proof is an exact degree-four Bernstein expansion in `x²`, with every
Bernstein coefficient positive.  This supplies a concrete positive profile
for a block-valued ground-state/Picone argument; no unresolved core
positivity statement is assumed here.
-/

def fourCellOddP11RationalRieszA3 : ℝ := 114653 / 100000
def fourCellOddP11RationalRieszA5 : ℝ := -21885 / 100000
def fourCellOddP11RationalRieszA7 : ℝ := -6127 / 100000
def fourCellOddP11RationalRieszA9 : ℝ := 2692 / 100000

/-- A rational approximation to the finite core-Riesz residual of `P₁`
against `span(P₃,P₅,P₇,P₉)`. -/
def fourCellOddP11RationalRieszGroundProfile : ℝ → ℝ :=
  fourCellOddP11GalerkinResidualProfile
    fourCellOddP11RationalRieszA3
    fourCellOddP11RationalRieszA5
    fourCellOddP11RationalRieszA7
    fourCellOddP11RationalRieszA9

/-- Exact Bernstein normal form.  The five displayed coefficients are all
strictly positive, so the sign of the profile is the sign of `x` on the
closed production half-interval. -/
theorem fourCellOddP11RationalRieszGroundProfile_eq_bernstein (x : ℝ) :
    fourCellOddP11RationalRieszGroundProfile x =
      x *
        ((9375559 / 3200000 : ℝ) * (1 - x ^ 2) ^ 4 +
          4 * (14585733 / 6400000 : ℝ) * x ^ 2 * (1 - x ^ 2) ^ 3 +
          6 * (673247 / 800000 : ℝ) * (x ^ 2) ^ 2 * (1 - x ^ 2) ^ 2 +
          4 * (30523 / 80000 : ℝ) * (x ^ 2) ^ 3 * (1 - x ^ 2) +
          (10667 / 100000 : ℝ) * (x ^ 2) ^ 4) := by
  unfold fourCellOddP11RationalRieszGroundProfile
    fourCellOddP11RationalRieszA3 fourCellOddP11RationalRieszA5
    fourCellOddP11RationalRieszA7 fourCellOddP11RationalRieszA9
    fourCellOddP11GalerkinResidualProfile
    fourCellOddP11GalerkinLowProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  ring

/-- Structural positivity of the rational ground profile on the positive
half-interval. -/
theorem fourCellOddP11RationalRieszGroundProfile_pos
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < fourCellOddP11RationalRieszGroundProfile x := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hgap : 0 ≤ 1 - x ^ 2 := by nlinarith
  rw [fourCellOddP11RationalRieszGroundProfile_eq_bernstein]
  have h0 : 0 ≤
      (9375559 / 3200000 : ℝ) * (1 - x ^ 2) ^ 4 := by positivity
  have h1 : 0 ≤
      4 * (14585733 / 6400000 : ℝ) * x ^ 2 * (1 - x ^ 2) ^ 3 := by
    positivity
  have h2 : 0 ≤
      6 * (673247 / 800000 : ℝ) * (x ^ 2) ^ 2 *
        (1 - x ^ 2) ^ 2 := by
    positivity
  have h3 : 0 ≤
      4 * (30523 / 80000 : ℝ) * (x ^ 2) ^ 3 * (1 - x ^ 2) := by
    positivity
  have h4 : 0 < (10667 / 100000 : ℝ) * (x ^ 2) ^ 4 := by
    positivity
  have hsum : 0 <
      (9375559 / 3200000 : ℝ) * (1 - x ^ 2) ^ 4 +
        4 * (14585733 / 6400000 : ℝ) * x ^ 2 * (1 - x ^ 2) ^ 3 +
        6 * (673247 / 800000 : ℝ) * (x ^ 2) ^ 2 * (1 - x ^ 2) ^ 2 +
        4 * (30523 / 80000 : ℝ) * (x ^ 2) ^ 3 * (1 - x ^ 2) +
        (10667 / 100000 : ℝ) * (x ^ 2) ^ 4 := by
    positivity
  exact mul_pos hx hsum

theorem fourCellOddP11RationalRieszGroundProfile_one :
    fourCellOddP11RationalRieszGroundProfile 1 = 10667 / 100000 := by
  rw [fourCellOddP11RationalRieszGroundProfile_eq_bernstein]
  norm_num

theorem contDiff_fourCellOddP11RationalRieszGroundProfile :
    ContDiff ℝ 1 fourCellOddP11RationalRieszGroundProfile := by
  unfold fourCellOddP11RationalRieszGroundProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _

theorem odd_fourCellOddP11RationalRieszGroundProfile :
    Function.Odd fourCellOddP11RationalRieszGroundProfile := by
  unfold fourCellOddP11RationalRieszGroundProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _

/-- Its `P₁` coefficient is exactly one, as required of a Galerkin residual.
-/
theorem centeredOddP1Coefficient_rationalRieszGroundProfile :
    centeredOddP1Coefficient fourCellOddP11RationalRieszGroundProfile = 1 := by
  unfold fourCellOddP11RationalRieszGroundProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode,
    centeredOddP1Coefficient_fiveModeLowProfile]

/-- The candidate has strictly positive complete core energy by the already
certified finite five-mode block. -/
theorem fourCellOddCoreLocalQuadratic_rationalRieszGroundProfile_pos :
    0 < fourCellOddCoreLocalQuadratic
      fourCellOddP11RationalRieszGroundProfile := by
  unfold fourCellOddP11RationalRieszGroundProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  apply fourCellOddCoreLocalQuadratic_fiveMode_pos
  intro hzero
  have hfirst := congrFun hzero 0
  norm_num at hfirst

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11RationalRieszGroundProfileStructural
