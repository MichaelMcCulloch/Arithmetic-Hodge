import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreEntryBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural

noncomputable section

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open YoshidaConstantBounds
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural
open YoshidaFourCellOddP11CoreEntryBoundsStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Structural diagonal bound for the first augmented odd mode

The augmented six-mode Galerkin block needs one new diagonal entry, the core
quadratic of the genuine `P₁₁` tail direction.  Its positivity does not
require a sampled kernel estimate: the already proved infinite-dimensional
odd coercivity theorem applies directly, because `P₁₁` is exactly
orthogonal to `P₁` and has positive-half mass `1 / 23`.
-/

/-- Rational, assumption-free lower bound for the new `P₁₁` diagonal.
This is the normalized coercivity floor `(343 / 12500) * (1 / 23)`. -/
theorem threeHundredFortyThree_div_twoHundredEightySevenThousandFiveHundred_le_fourCellOddCoreLocalQuadratic_P11 :
    (343 / 287500 : ℝ) ≤
      fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail := by
  have hP1 : centeredOddP1Coefficient fourCellOddP11DirectTail = 0 :=
    fourCellOddP11DirectTail_moments.1
  have h :=
    threeHundredFortyThree_div_twelveThousandFiveHundred_mul_mass_le_coreLocalQuadratic_of_P1
      fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail
      odd_fourCellOddP11DirectTail hP1
  rw [integral_zero_one_fourCellOddP11DirectTail_sq] at h
  norm_num at h ⊢
  exact h

/-- In particular, the augmented diagonal is strictly positive. -/
theorem fourCellOddCoreLocalQuadratic_P11_pos :
    0 < fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail := by
  have h :=
    threeHundredFortyThree_div_twoHundredEightySevenThousandFiveHundred_le_fourCellOddCoreLocalQuadratic_P11
  norm_num at h ⊢
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 343 / 287500) h

/-! ## The sole smooth diagonal moment -/

/-- The smooth-kernel moment left intact in the exact `P₁₁` diagonal. -/
def fourCellOddP11CoreDiagonalRegularMoment : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation fourCellOddP11DirectTail t

theorem factorTwoIntrinsicEnergy_fourCellOddP11DirectTail :
    factorTwoIntrinsicEnergy fourCellOddP11DirectTail = (2 / 23 : ℝ) := by
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail.continuous
    (Or.inr odd_fourCellOddP11DirectTail)
  unfold factorTwoIntrinsicEnergy
  rw [hfold, integral_zero_one_fourCellOddP11DirectTail_sq]
  norm_num

/-- Cauchy control of the whole smooth correction.  This is an
infinite-dimensional correlation estimate, not a quadrature certificate. -/
theorem fourCellOddP11CoreDiagonalRegularCorrection_sq_le :
    (2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreDiagonalRegularMoment) ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 529 : ℝ) := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    |factorTwoCenteredCorrelationBilinear
      fourCellOddP11DirectTail fourCellOddP11DirectTail t|
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear
        fourCellOddP11DirectTail fourCellOddP11DirectTail t
  have hregular : |R| ≤ (1 / 20 : ℝ) * I := by
    simpa only [R, I] using
      abs_fourCellRegularBilinear_le_one_twentieth_integral_abs
        fourCellOddP11DirectTail fourCellOddP11DirectTail
        contDiff_fourCellOddP11DirectTail.continuous
        contDiff_fourCellOddP11DirectTail.continuous
        odd_fourCellOddP11DirectTail odd_fourCellOddP11DirectTail
  have hI : I ^ 2 ≤ (2 / 23 : ℝ) * (2 / 23 : ℝ) := by
    have h :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        fourCellOddP11DirectTail fourCellOddP11DirectTail
        contDiff_fourCellOddP11DirectTail.continuous
        contDiff_fourCellOddP11DirectTail.continuous
    simpa only [I, factorTwoIntrinsicEnergy_fourCellOddP11DirectTail] using h
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have hR :
      (2 * fourCellOperatorHalfWidth * R) ^ 2 ≤
        (fourCellOperatorHalfWidth / 10) ^ 2 * I ^ 2 := by
    have habs :
        |2 * fourCellOperatorHalfWidth * R| ≤
          (fourCellOperatorHalfWidth / 10) * I := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity :
        0 ≤ (2 : ℝ)), abs_of_nonneg ha0]
      nlinarith
    calc
      (2 * fourCellOperatorHalfWidth * R) ^ 2 =
          |2 * fourCellOperatorHalfWidth * R| ^ 2 := by rw [sq_abs]
      _ ≤ ((fourCellOperatorHalfWidth / 10) * I) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (div_nonneg ha0 (by norm_num)) hI0)).2 habs
      _ = (fourCellOperatorHalfWidth / 10) ^ 2 * I ^ 2 := by ring
  have hmul := mul_le_mul_of_nonneg_left hI
    (sq_nonneg (fourCellOperatorHalfWidth / 10))
  have hfinal :
      (2 * fourCellOperatorHalfWidth * R) ^ 2 ≤
        (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 529 : ℝ) := by
    calc
      (2 * fourCellOperatorHalfWidth * R) ^ 2 ≤
          (fourCellOperatorHalfWidth / 10) ^ 2 * I ^ 2 := hR
      _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 *
          ((2 / 23 : ℝ) * (2 / 23 : ℝ)) := hmul
      _ = (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 529 : ℝ) := by
        ring
  simpa only [R, fourCellOddP11CoreDiagonalRegularMoment,
    factorTwoCenteredCorrelationBilinear_self] using hfinal

private theorem fourCellOperatorHalfWidth_le_one_half :
    fourCellOperatorHalfWidth ≤ (1 / 2 : ℝ) := by
  have hlog := strict_log_two_bounds.2
  unfold fourCellOperatorHalfWidth
  nlinarith

/-- Fully rational square radius for the smooth diagonal correction. -/
theorem fourCellOddP11CoreDiagonalRegularCorrection_sq_le_rational :
    (2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreDiagonalRegularMoment) ^ 2 ≤
      (1 / 230 : ℝ) ^ 2 := by
  have h := fourCellOddP11CoreDiagonalRegularCorrection_sq_le
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha := fourCellOperatorHalfWidth_le_one_half
  nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1 / 2)]

/-- Absolute-value form of the same rational radius. -/
theorem abs_fourCellOddP11CoreDiagonalRegularCorrection_le :
    |2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreDiagonalRegularMoment| ≤ (1 / 230 : ℝ) := by
  have h := fourCellOddP11CoreDiagonalRegularCorrection_sq_le_rational
  rw [← sq_abs] at h
  nlinarith [abs_nonneg (2 * fourCellOperatorHalfWidth *
    fourCellOddP11CoreDiagonalRegularMoment)]

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural
