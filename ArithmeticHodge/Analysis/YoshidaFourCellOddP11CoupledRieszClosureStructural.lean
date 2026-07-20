import ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalCoupledClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoupledRieszClosureStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11EndpointFormDualClosureStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# The corrected `P₁`/`P₁₁+` Riesz determinant

After the exact five-mode projection, separate Cauchy estimates for the
finite row, tail row, and finite--tail cross do not compose.  The invariant
that does compose is the corrected determinant below; it retains the sign
and correlation of the mixed row.
-/

/-- Corrected determinant of a finite row `(A,b,C)`, a tail row `(A,x,z)`,
and their coupled cross `y`. -/
def coupledP1TailSchurDefect
    (A b C x y z : ℝ) : ℝ :=
  (A * C - b ^ 2) +
    2 * (A * y - b * x) +
    (A * z - x ^ 2)

/-- Exact determinant identity.  In particular, the mixed correlation
cannot be replaced by its absolute value without spending finite reserve. -/
theorem coupledP1TailSchurDefect_eq
    (A b C x y z : ℝ) :
    coupledP1TailSchurDefect A b C x y z =
      A * (C + 2 * y + z) - (b + x) ^ 2 := by
  unfold coupledP1TailSchurDefect
  ring

theorem add_row_sq_le_of_coupledP1TailSchurDefect_nonneg
    {A b C x y z : ℝ}
    (hdefect : 0 ≤ coupledP1TailSchurDefect A b C x y z) :
    (b + x) ^ 2 ≤ A * (C + 2 * y + z) := by
  rw [coupledP1TailSchurDefect_eq] at hdefect
  linarith

/-- Sharp structural obstruction to a rowwise allocation: even saturated
finite Schur, tail Schur, and finite--tail Cauchy inequalities do not imply
the coupled conclusion.  The missing datum is the sign of `A*y - b*x`. -/
theorem rowwise_schur_bounds_do_not_imply_coupled :
    ¬ (∀ A b C x y z : ℝ,
      0 ≤ A → 0 ≤ C → 0 ≤ z →
      b ^ 2 ≤ A * C → x ^ 2 ≤ A * z → y ^ 2 ≤ C * z →
      (b + x) ^ 2 ≤ A * (C + 2 * y + z)) := by
  intro h
  have hbad := h 1 1 1 1 (-1) 1
  norm_num at hbad

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoupledRieszClosureStructural
