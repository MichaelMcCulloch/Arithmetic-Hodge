import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellSingleProfileStructural
import ArithmeticHodge.Analysis.YoshidaFourCellParityOperatorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointParityPencil

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorProbeStructural

noncomputable section

open MultiplicativeWeilFiveCellSingleProfileStructural
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularKernelSquareStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural

/-!
# Structural probe of the five-cell endpoint operator

The normalized five-cell prime atom couples the endpoint strips
`[1 / 3, 1]` and `[-1, -1 / 3]` at lag `4 / 3`.  This file keeps that
channel exact.  Its first normal form is the pointwise Hadamard
diagonalization into matched and antimatched strip squares.
-/

/-- Fixed normalized halfwidth of five consecutive quarter cells. -/
def fiveCellOperatorHalfWidth : ℝ :=
  3 * Real.log 2 / 4

/-- The matched Hadamard square on the five-cell endpoint strips. -/
def fiveCellEndpointMatchedSquare (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in (1 / 3 : ℝ)..1,
    (w x + w (x - 4 / 3)) ^ 2

/-- The antimatched Hadamard square on the five-cell endpoint strips. -/
def fiveCellEndpointAntimatchedSquare (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in (1 / 3 : ℝ)..1,
    (w x - w (x - 4 / 3)) ^ 2

/-- The exact endpoint-corrected five-cell operator. -/
def fiveCellEndpointOperator (w : ℝ → ℝ) : ℝ :=
  centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w -
    Real.sqrt 2 * Real.log 2 * fiveCellEndpointPairing w

/-- Both Hadamard channels are literal nonnegative squares. -/
theorem fiveCellEndpointMatchedSquare_nonneg (w : ℝ → ℝ) :
    0 ≤ fiveCellEndpointMatchedSquare w := by
  unfold fiveCellEndpointMatchedSquare
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  positivity

theorem fiveCellEndpointAntimatchedSquare_nonneg (w : ℝ → ℝ) :
    0 ≤ fiveCellEndpointAntimatchedSquare w := by
  unfold fiveCellEndpointAntimatchedSquare
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  positivity

/-- Sharp Hadamard signature of the lag-`4 / 3` endpoint pairing.  No
endpoint trace, parity, or finite-dimensional hypothesis enters. -/
theorem four_mul_fiveCellEndpointPairing_eq_matched_sub_antimatched
    (w : ℝ → ℝ) (hw : Continuous w) :
    4 * fiveCellEndpointPairing w =
      fiveCellEndpointMatchedSquare w -
        fiveCellEndpointAntimatchedSquare w := by
  have hplus : IntervalIntegrable
      (fun x : ℝ ↦ (w x + w (x - 4 / 3)) ^ 2)
      volume (1 / 3) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦ (w x + w (x - 4 / 3)) ^ 2)).intervalIntegrable _ _
  have hminus : IntervalIntegrable
      (fun x : ℝ ↦ (w x - w (x - 4 / 3)) ^ 2)
      volume (1 / 3) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦ (w x - w (x - 4 / 3)) ^ 2)).intervalIntegrable _ _
  unfold fiveCellEndpointPairing fiveCellEndpointMatchedSquare
    fiveCellEndpointAntimatchedSquare
  rw [← intervalIntegral.integral_sub hplus hminus,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

/-- Exact positive-minus-negative square normal form of the complete
five-cell endpoint operator. -/
theorem fiveCellEndpointOperator_eq_physical_add_antimatched_sub_matched
    (w : ℝ → ℝ) (hw : Continuous w) :
    fiveCellEndpointOperator w =
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w +
          (Real.sqrt 2 * Real.log 2 / 4) *
            fiveCellEndpointAntimatchedSquare w -
        (Real.sqrt 2 * Real.log 2 / 4) *
          fiveCellEndpointMatchedSquare w := by
  unfold fiveCellEndpointOperator
  rw [show fiveCellEndpointPairing w =
      (fiveCellEndpointMatchedSquare w -
        fiveCellEndpointAntimatchedSquare w) / 4 by
    linarith [four_mul_fiveCellEndpointPairing_eq_matched_sub_antimatched
      w hw]]
  ring

/-- The sharp universal capacity frontier.  Positivity is exactly the
requirement that the physical diagonal plus the favorable antimatched
channel pay for the adverse matched channel. -/
theorem fiveCellEndpointOperator_nonnegative_iff_capacity
    (w : ℝ → ℝ) (hw : Continuous w) :
    0 ≤ fiveCellEndpointOperator w ↔
      (Real.sqrt 2 * Real.log 2 / 4) *
          fiveCellEndpointMatchedSquare w ≤
        centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w +
          (Real.sqrt 2 * Real.log 2 / 4) *
            fiveCellEndpointAntimatchedSquare w := by
  rw [fiveCellEndpointOperator_eq_physical_add_antimatched_sub_matched w hw]
  exact sub_nonneg

end

end ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorProbeStructural
