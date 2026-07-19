import ArithmeticHodge.Analysis.YoshidaFourCellOddPolarPotentialStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularParityFoldStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellCompletedParityOperatorStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointPotentialBound
open YoshidaFourCellEndpointHalfFoldStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularKernelSquareStructural
open YoshidaFourCellRegularParityFoldStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaFourCellOddPolarPotentialStructural
open YoshidaRegularKernelBound

/-!
# Completed positive-half four-cell parity operators

The regular autocorrelation in the exact four-cell parity operators is not
discarded or bounded by its norm.  It is completed into two nonnegative
positive-half kernel squares minus the exact regular row potential.  In the
odd channel the negative hyperbolic rank is then charged to the endpoint
potential, leaving the compiled `10 / 9` reserve.
-/

/-- Even four-cell operator after exact regular-kernel square completion. -/
def fourCellEvenCompletedParityOperator (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w 1) +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) +
    fourCellOperatorHalfWidth *
      (fourCellPositiveHalfRegularSameSignSquare w
          fourCellOperatorHalfWidth +
        fourCellPositiveHalfRegularReflectedSquare w
          fourCellOperatorHalfWidth 1) -
    2 * fourCellOperatorHalfWidth *
      fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth +
    8 * fourCellOperatorHalfWidth *
      fourCellPositiveCoshMoment w
        (fourCellOperatorHalfWidth / 2) ^ 2 +
    (Real.sqrt 2 * Real.log 2 / 2) *
      (∫ t : ℝ in 0..2 / 5,
        fourCellEndpointHalfAntimatched w t ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointHalfMass w

/-- Odd four-cell operator after exact regular-kernel square completion. -/
def fourCellOddCompletedParityOperator (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) +
    fourCellOperatorHalfWidth *
      (fourCellPositiveHalfRegularSameSignSquare w
          fourCellOperatorHalfWidth +
        fourCellPositiveHalfRegularReflectedSquare w
          fourCellOperatorHalfWidth (-1)) -
    2 * fourCellOperatorHalfWidth *
      fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth -
    8 * fourCellOperatorHalfWidth *
      fourCellPositiveSinhMoment w
        (fourCellOperatorHalfWidth / 2) ^ 2 +
    (Real.sqrt 2 * Real.log 2 / 2) *
      (∫ t : ℝ in 0..2 / 5,
        fourCellEndpointHalfMatched w t ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointHalfMass w

/-- The rigorous lower operator after paying the entire odd hyperbolic rank
from the endpoint potential and retaining `10 / 9` of that potential. -/
def fourCellOddPostPolarLowerOperator (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    (10 / 9 : ℝ) * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) +
    fourCellOperatorHalfWidth *
      (fourCellPositiveHalfRegularSameSignSquare w
          fourCellOperatorHalfWidth +
        fourCellPositiveHalfRegularReflectedSquare w
          fourCellOperatorHalfWidth (-1)) -
    2 * fourCellOperatorHalfWidth *
      fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth +
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

private theorem neg_regularFullSquare_eq_completion_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    -fourCellOperatorHalfWidth * fourCellRegularFullSquare w =
      fourCellOperatorHalfWidth *
          (fourCellPositiveHalfRegularSameSignSquare w
              fourCellOperatorHalfWidth +
            fourCellPositiveHalfRegularReflectedSquare w
              fourCellOperatorHalfWidth 1) -
        2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  have hfull :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      w hw fourCellOperatorHalfWidth fourCellOperatorHalfWidth_nonneg
        fourCellOperatorHalfWidth_le_log_three_div_two
  change 2 * I = fourCellRegularFullSquare w at hfull
  have hcompletion :=
    neg_two_mul_regularCorrelation_eq_positiveHalfCompletion_even
      w hw heven fourCellOperatorHalfWidth
        fourCellOperatorHalfWidth_nonneg
        fourCellOperatorHalfWidth_le_log_three_div_two
  change -2 * fourCellOperatorHalfWidth * I = _ at hcompletion
  calc
    -fourCellOperatorHalfWidth * fourCellRegularFullSquare w =
        -2 * fourCellOperatorHalfWidth * I := by rw [← hfull]; ring
    _ = _ := hcompletion

private theorem neg_regularFullSquare_eq_completion_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    -fourCellOperatorHalfWidth * fourCellRegularFullSquare w =
      fourCellOperatorHalfWidth *
          (fourCellPositiveHalfRegularSameSignSquare w
              fourCellOperatorHalfWidth +
            fourCellPositiveHalfRegularReflectedSquare w
              fourCellOperatorHalfWidth (-1)) -
        2 * fourCellOperatorHalfWidth *
          fourCellPositiveHalfRegularRowMass w fourCellOperatorHalfWidth := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  have hfull :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      w hw fourCellOperatorHalfWidth fourCellOperatorHalfWidth_nonneg
        fourCellOperatorHalfWidth_le_log_three_div_two
  change 2 * I = fourCellRegularFullSquare w at hfull
  have hcompletion :=
    neg_two_mul_regularCorrelation_eq_positiveHalfCompletion_odd
      w hw hodd fourCellOperatorHalfWidth
        fourCellOperatorHalfWidth_nonneg
        fourCellOperatorHalfWidth_le_log_three_div_two
  change -2 * fourCellOperatorHalfWidth * I = _ at hcompletion
  calc
    -fourCellOperatorHalfWidth * fourCellRegularFullSquare w =
        -2 * fourCellOperatorHalfWidth * I := by rw [← hfull]; ring
    _ = _ := hcompletion

/-- The exact even parity operator is its completed positive-half form. -/
theorem fourCellEvenParityOperator_eq_completed
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    fourCellEvenParityOperator w = fourCellEvenCompletedParityOperator w := by
  have hregular := neg_regularFullSquare_eq_completion_even w hw heven
  unfold fourCellEvenParityOperator fourCellEvenCompletedParityOperator
  linear_combination hregular

/-- The exact odd parity operator is its completed positive-half form. -/
theorem fourCellOddParityOperator_eq_completed
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    fourCellOddParityOperator w = fourCellOddCompletedParityOperator w := by
  have hregular := neg_regularFullSquare_eq_completion_odd w hw hodd
  unfold fourCellOddParityOperator fourCellOddCompletedParityOperator
  linear_combination hregular

/-- Complete even four-cell bracket in exact positive-half square form. -/
theorem fourCellBracket_eq_evenCompletedParityOperator
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
      fourCellEvenCompletedParityOperator w := by
  rw [fourCellBracket_eq_evenParityOperator w hw hlocal heven,
    fourCellEvenParityOperator_eq_completed w hw heven]

/-- Complete odd four-cell bracket in exact positive-half square form. -/
theorem fourCellBracket_eq_oddCompletedParityOperator
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hodd : Function.Odd w) :
    centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
      fourCellOddCompletedParityOperator w := by
  rw [fourCellBracket_eq_oddParityOperator w hw hlocal hodd,
    fourCellOddParityOperator_eq_completed w hw hodd]

/-- The post-polar odd operator is a genuine lower bound for the exact
completed odd operator. -/
theorem fourCellOddPostPolarLowerOperator_le_completed
    (w : ℝ → ℝ) (hw : Continuous w) :
    fourCellOddPostPolarLowerOperator w ≤
      fourCellOddCompletedParityOperator w := by
  have hpolar := ten_ninths_potential_le_odd_potential_sub_polar w hw
  unfold fourCellOddPostPolarLowerOperator
    fourCellOddCompletedParityOperator
  linarith

/-- Nonnegativity of the explicit post-polar lower operator is sufficient
for the complete odd four-cell bracket. -/
theorem fourCellBracket_nonnegative_of_oddPostPolarLowerOperator
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hodd : Function.Odd w)
    (hlower : 0 ≤ fourCellOddPostPolarLowerOperator w) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  rw [fourCellBracket_eq_oddCompletedParityOperator w hw hlocal hodd]
  exact hlower.trans (fourCellOddPostPolarLowerOperator_le_completed w hw)

end

end ArithmeticHodge.Analysis.YoshidaFourCellCompletedParityOperatorStructural
