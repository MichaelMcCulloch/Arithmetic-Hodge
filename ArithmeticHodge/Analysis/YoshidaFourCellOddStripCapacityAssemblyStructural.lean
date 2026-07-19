import ArithmeticHodge.Analysis.YoshidaFourCellCompletedParityOperatorStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddEndpointStripCoercivityStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddStripEmbeddingStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityAssemblyStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointPotentialBound
open YoshidaFourCellCompletedParityOperatorStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddStripEmbeddingStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularParityFoldStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural

/-!
# Lossless-row odd four-cell strip assembly

The odd endpoint-strip gap is inserted into the exact completed operator while
the regular row potential, the odd hyperbolic rank, both regular completion
squares, and all endpoint potential are retained exactly.  This avoids the
false lower operators obtained by charging either the regular row uniformly
or the entire hyperbolic rank termwise.
-/

/-- The sharp retained odd capacity operator.  Its only loss relative to the
exact completed operator is the mean-zero gap used inside the endpoint strip;
the unused same-sign raw energy is kept as an explicit remainder. -/
def fourCellOddStripCapacityLowerOperator (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass w +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass w +
    (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w -
        fourCellOddEndpointStripRawEnergy w) +
    (1 / 2 : ℝ) * fourCellPositiveHalfRawReflectedEnergy w (-1) +
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
        (fourCellOperatorHalfWidth / 2) ^ 2

/-- The unused same-sign raw energy outside the endpoint strip is genuinely
nonnegative on the production `C¹` form domain. -/
theorem fourCellOddStripCapacity_rawRemainder_nonneg
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    0 ≤ fourCellPositiveHalfRawSameSignEnergy w -
      fourCellOddEndpointStripRawEnergy w := by
  exact sub_nonneg.mpr
    (fourCellOddEndpointStripRawEnergy_le_positiveHalf w hw)

/-- The strip-capacity operator is a lower bound for the exact completed odd
operator, with no regular-row or hyperbolic estimate. -/
theorem fourCellOddStripCapacityLowerOperator_le_completed
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddStripCapacityLowerOperator w ≤
      fourCellOddCompletedParityOperator w := by
  have hstrip :=
    fourCellOddEndpointStrip_retained_prime_coercivity w hw hodd
  have hprime :=
    neg_primePairing_eq_halfMatched_sub_mass_of_odd
      w hw.continuous hodd
  unfold fourCellOddStripCapacityLowerOperator
    fourCellOddCompletedParityOperator
  linear_combination hstrip + hprime

/-- Nonnegativity of the lossless-row strip operator suffices for the exact
odd four-cell bracket. -/
theorem fourCellBracket_nonnegative_of_oddStripCapacity
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hlower : 0 ≤ fourCellOddStripCapacityLowerOperator w) :
    0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  rw [fourCellBracket_eq_oddCompletedParityOperator w hw.continuous
    (hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)) hodd]
  exact hlower.trans
    (fourCellOddStripCapacityLowerOperator_le_completed w hw hodd)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityAssemblyStructural
