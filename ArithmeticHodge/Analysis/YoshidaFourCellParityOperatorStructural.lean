import ArithmeticHodge.Analysis.YoshidaFourCellParityHalfFoldStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRawParityFoldStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelSquareStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellParityOperatorStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointPotentialBound
open YoshidaFourCellEndpointHalfFoldStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularKernelSquareStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound

/-!
# Exact parity operators for the four-cell bracket

The complete four-cell bracket is kept intact while it is folded by
reflection parity.  In particular, the regular-kernel quadratic and the
prime endpoint atom are not estimated or discarded.  The resulting two
identities are the exact operator statements on which a structural capacity
proof (or a production counterexample) must act.
-/

/-- Fixed normalized halfwidth of four consecutive quarter cells. -/
def fourCellOperatorHalfWidth : ℝ :=
  5 * Real.log 2 / 8

/-- The complete regular-kernel quadratic on the centered square. -/
def fourCellRegularFullSquare (w : ℝ → ℝ) : ℝ :=
  ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1,
    yoshidaRegularKernel
        (fourCellOperatorHalfWidth * |y - x|) * w y * w x

/-- Exact positive-half normal form of the even four-cell bracket. -/
def fourCellEvenParityOperator (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w 1) +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    fourCellOperatorHalfWidth * fourCellRegularFullSquare w +
    8 * fourCellOperatorHalfWidth *
      fourCellPositiveCoshMoment w
        (fourCellOperatorHalfWidth / 2) ^ 2 +
    (Real.sqrt 2 * Real.log 2 / 2) *
      (∫ t : ℝ in 0..2 / 5,
        fourCellEndpointHalfAntimatched w t ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointHalfMass w

/-- Exact positive-half normal form of the odd four-cell bracket. -/
def fourCellOddParityOperator (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    fourCellOperatorHalfWidth * fourCellRegularFullSquare w -
    8 * fourCellOperatorHalfWidth *
      fourCellPositiveSinhMoment w
        (fourCellOperatorHalfWidth / 2) ^ 2 +
    (Real.sqrt 2 * Real.log 2 / 2) *
      (∫ t : ℝ in 0..2 / 5,
        fourCellEndpointHalfMatched w t ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointHalfMass w

private theorem fourCellOperatorHalfWidth_nonneg :
    0 ≤ fourCellOperatorHalfWidth := by
  unfold fourCellOperatorHalfWidth
  positivity

private theorem fourCellOperatorHalfWidth_le_log_three_div_two :
    fourCellOperatorHalfWidth ≤ Real.log 3 / 2 := by
  have h := five_mul_log_two_div_four_lt_log_three
  unfold fourCellOperatorHalfWidth
  linarith

/-- On an even locally Lipschitz profile, the complete four-cell bracket is
exactly the even parity operator above. -/
theorem fourCellBracket_eq_evenParityOperator
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
      fourCellEvenParityOperator w := by
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_even
    w hlocal heven
  have hpotential := endpointPotential_eq_two_mul_positiveHalf
    w hw (Or.inl heven)
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw (Or.inl heven)
  have hregular :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      w hw fourCellOperatorHalfWidth fourCellOperatorHalfWidth_nonneg
        fourCellOperatorHalfWidth_le_log_three_div_two
  have hpolar := physicalPolarProduct_eq_positiveCoshSquare_of_even
    w hw heven fourCellOperatorHalfWidth
  have hprime := neg_primePairing_eq_halfAntimatched_sub_mass_of_even
    w hw heven
  unfold centeredClippedPhysicalQuadratic fourCellEvenParityOperator
    fourCellRegularFullSquare
  rw [hraw, hpotential, hmass, hpolar]
  linear_combination hprime - fourCellOperatorHalfWidth * hregular

/-- On an odd locally Lipschitz profile, the complete four-cell bracket is
exactly the odd parity operator above. -/
theorem fourCellBracket_eq_oddParityOperator
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hodd : Function.Odd w) :
    centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
      fourCellOddParityOperator w := by
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hlocal hodd
  have hpotential := endpointPotential_eq_two_mul_positiveHalf
    w hw (Or.inr hodd)
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw (Or.inr hodd)
  have hregular :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      w hw fourCellOperatorHalfWidth fourCellOperatorHalfWidth_nonneg
        fourCellOperatorHalfWidth_le_log_three_div_two
  have hpolar := physicalPolarProduct_eq_neg_positiveSinhSquare_of_odd
    w hw hodd fourCellOperatorHalfWidth
  have hprime := neg_primePairing_eq_halfMatched_sub_mass_of_odd
    w hw hodd
  unfold centeredClippedPhysicalQuadratic fourCellOddParityOperator
    fourCellRegularFullSquare
  rw [hraw, hpotential, hmass, hpolar]
  linear_combination hprime - fourCellOperatorHalfWidth * hregular

end

end ArithmeticHodge.Analysis.YoshidaFourCellParityOperatorStructural
