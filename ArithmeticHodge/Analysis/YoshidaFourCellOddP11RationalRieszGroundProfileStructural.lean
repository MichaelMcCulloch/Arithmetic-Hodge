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
open YoshidaFourCellOddEndpointStripCoercivityStructural
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

/-! ## The endpoint-strip parity block -/

/-- Exact positive Bernstein expansion of the strip-even component. -/
theorem fourCellOddEndpointStripEven_rationalRiesz_eq_bernstein (z : ℝ) :
    fourCellOddEndpointStripEven
        fourCellOddP11RationalRieszGroundProfile z =
      (187844423387 / 312500000000 : ℝ) * (1 - z ^ 2) ^ 4 +
        4 * (2947668491 / 5000000000 : ℝ) * z ^ 2 *
          (1 - z ^ 2) ^ 3 +
        6 * (3615654977 / 6250000000 : ℝ) * (z ^ 2) ^ 2 *
          (1 - z ^ 2) ^ 2 +
        4 * (11072042849 / 19531250000 : ℝ) * (z ^ 2) ^ 3 *
          (1 - z ^ 2) +
        (5405382001 / 9765625000 : ℝ) * (z ^ 2) ^ 4 := by
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
  rw [fourCellOddP11RationalRieszGroundProfile_eq_bernstein,
    fourCellOddP11RationalRieszGroundProfile_eq_bernstein]
  ring

/-- The strip-even component is strictly positive on its entire normalized
strip. -/
theorem fourCellOddEndpointStripEven_rationalRiesz_pos
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    0 < fourCellOddEndpointStripEven
      fourCellOddP11RationalRieszGroundProfile z := by
  have hzsq : 0 ≤ z ^ 2 := sq_nonneg z
  have hgap : 0 ≤ 1 - z ^ 2 := by
    rcases hz with ⟨hzlo, hzhi⟩
    nlinarith [sq_nonneg (z - 1), sq_nonneg (z + 1)]
  rw [fourCellOddEndpointStripEven_rationalRiesz_eq_bernstein]
  by_cases hboundary : z ^ 2 = 1
  · rw [hboundary]
    norm_num
  · have hgapNe : 1 - z ^ 2 ≠ 0 := by
      intro hzero
      apply hboundary
      nlinarith
    have hgapPos : 0 < 1 - z ^ 2 :=
      lt_of_le_of_ne hgap (Ne.symm hgapNe)
    have hfirst : 0 <
        (187844423387 / 312500000000 : ℝ) * (1 - z ^ 2) ^ 4 := by
      positivity
    have hsecond : 0 ≤
        4 * (2947668491 / 5000000000 : ℝ) * z ^ 2 *
          (1 - z ^ 2) ^ 3 := by positivity
    have hthird : 0 ≤
        6 * (3615654977 / 6250000000 : ℝ) * (z ^ 2) ^ 2 *
          (1 - z ^ 2) ^ 2 := by positivity
    have hfourth : 0 ≤
        4 * (11072042849 / 19531250000 : ℝ) * (z ^ 2) ^ 3 *
          (1 - z ^ 2) := by positivity
    have hfifth : 0 ≤
        (5405382001 / 9765625000 : ℝ) * (z ^ 2) ^ 4 := by positivity
    positivity

/-- Exact positive Bernstein expansion after factoring `-z` from the
strip-odd component. -/
theorem neg_fourCellOddEndpointStripOdd_rationalRiesz_eq_bernstein (z : ℝ) :
    -fourCellOddEndpointStripOdd
        fourCellOddP11RationalRieszGroundProfile z =
      z *
        ((661570943077 / 1250000000000 : ℝ) * (1 - z ^ 2) ^ 4 +
          4 * (252570675579 / 500000000000 : ℝ) * z ^ 2 *
            (1 - z ^ 2) ^ 3 +
          6 * (151017540419 / 312500000000 : ℝ) * (z ^ 2) ^ 2 *
            (1 - z ^ 2) ^ 2 +
          4 * (72463591169 / 156250000000 : ℝ) * (z ^ 2) ^ 3 *
            (1 - z ^ 2) +
          (17454731129 / 39062500000 : ℝ) * (z ^ 2) ^ 4) := by
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  rw [fourCellOddP11RationalRieszGroundProfile_eq_bernstein,
    fourCellOddP11RationalRieszGroundProfile_eq_bernstein]
  ring

/-- On the positive normalized half-strip, the strip-odd component has the
fixed negative sign needed for a two-channel Picone transform. -/
theorem fourCellOddEndpointStripOdd_rationalRiesz_neg
    {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    fourCellOddEndpointStripOdd
      fourCellOddP11RationalRieszGroundProfile z < 0 := by
  have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz
  have hgap : 0 ≤ 1 - z ^ 2 := by nlinarith
  rw [← neg_pos,
    neg_fourCellOddEndpointStripOdd_rationalRiesz_eq_bernstein]
  have h0 : 0 ≤
      (661570943077 / 1250000000000 : ℝ) * (1 - z ^ 2) ^ 4 := by
    positivity
  have h1 : 0 ≤
      4 * (252570675579 / 500000000000 : ℝ) * z ^ 2 *
        (1 - z ^ 2) ^ 3 := by positivity
  have h2 : 0 ≤
      6 * (151017540419 / 312500000000 : ℝ) * (z ^ 2) ^ 2 *
        (1 - z ^ 2) ^ 2 := by positivity
  have h3 : 0 ≤
      4 * (72463591169 / 156250000000 : ℝ) * (z ^ 2) ^ 3 *
        (1 - z ^ 2) := by positivity
  have h4 : 0 <
      (17454731129 / 39062500000 : ℝ) * (z ^ 2) ^ 4 := by
    positivity
  positivity

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
