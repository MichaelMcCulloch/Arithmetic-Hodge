import ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalFormDualClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalCoupledClosureStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Coupled closure of the odd `P₁` extension row

The scalar tail density is too weak before projection.  Here the first five
odd shifted-Legendre modes remain coupled in the complete core form, and only
the genuine `P₁₁+` residual is exposed to a Riesz estimate.
-/

/-- The certified five-mode expression, named for use in the coupled
finite/tail decomposition. -/
def fourCellOddFiveModeCoreExpression (c d e f g : ℝ) : ℝ :=
  fourCellOddOneThreeFivePerturbedQuadratic c d e +
    2 * fourCellOddCoreLocalBilinear
        centeredP1 factorTwoCenteredP7 * c * f +
    2 * fourCellOddCoreLocalBilinear
        centeredP3 factorTwoCenteredP7 * d * f +
    2 * fourCellOddCoreLocalBilinear
        factorTwoCenteredP5 factorTwoCenteredP7 * e * f +
    fourCellOddCoreLocalQuadratic factorTwoCenteredP7 * f ^ 2 +
    2 * fourCellOddCoreLocalBilinear
        centeredP1 factorTwoCenteredP9 * c * g +
    2 * fourCellOddCoreLocalBilinear
        centeredP3 factorTwoCenteredP9 * d * g +
    2 * fourCellOddCoreLocalBilinear
        factorTwoCenteredP5 factorTwoCenteredP9 * e * g +
    2 * fourCellOddCoreLocalBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 * f * g +
    fourCellOddCoreLocalQuadratic factorTwoCenteredP9 * g ^ 2

theorem fourCellOddFiveModeCoreExpression_nonneg (c d e f g : ℝ) :
    0 ≤ fourCellOddFiveModeCoreExpression c d e f g := by
  simpa only [fourCellOddFiveModeCoreExpression] using
    fourCellOddFiveModeCoreQuadratic_nonneg c d e f g

/-- The exact degree-one row of the certified five-mode coefficient form. -/
def fourCellOddP1FiveModeRow (d e f g : ℝ) : ℝ :=
  fourCellOddOneThreeFivePerturbed13 * d +
    fourCellOddOneThreeFivePerturbed15 * e +
    fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 * f +
    fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 * g

/-- Finite Schur closure of the `P₁` row against the complete coupled
`P₃/P₅/P₇/P₉` block.  This is extracted from positivity of the whole
five-mode form, so no diagonal or rowwise allocation is made. -/
theorem fourCellOddP1FiveModeRow_sq_le
    (d e f g : ℝ) :
    fourCellOddP1FiveModeRow d e f g ^ 2 ≤
      fourCellOddOneThreeFivePerturbed11 *
        fourCellOddFiveModeCoreExpression 0 d e f g := by
  let A := fourCellOddOneThreeFivePerturbed11
  let R := fourCellOddP1FiveModeRow d e f g
  let C := fourCellOddFiveModeCoreExpression 0 d e f g
  have hA : 0 < A := by
    rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
      ⟨h11, _h11', _h13, _h13', _h33, _h33', _⟩
    dsimp only [A]
    linarith
  have hexpand (c : ℝ) :
      fourCellOddFiveModeCoreExpression c d e f g =
        A * c ^ 2 + 2 * R * c + C := by
    dsimp only [A, R, C]
    unfold fourCellOddFiveModeCoreExpression fourCellOddP1FiveModeRow
      fourCellOddOneThreeFivePerturbedQuadratic
    ring
  have hquad := fourCellOddFiveModeCoreExpression_nonneg (-R / A) d e f g
  rw [hexpand] at hquad
  have heq :
      A * (-R / A) ^ 2 + 2 * R * (-R / A) + C =
        (A * C - R ^ 2) / A := by
    field_simp [ne_of_gt hA]
    ring
  rw [heq] at hquad
  have hmul := mul_nonneg hquad hA.le
  have hcancel : ((A * C - R ^ 2) / A) * A = A * C - R ^ 2 := by
    field_simp [ne_of_gt hA]
  rw [hcancel] at hmul
  have hdet : 0 ≤ A * C - R ^ 2 := hmul
  dsimp only [A, R, C] at hdet ⊢
  linarith

/-- On `P₁⊥`, the canonical five-mode part has no degree-one coordinate. -/
theorem fourCellOddOneThreeFiveSevenNineLowPart_eq_P1Orthogonal
    (v : ℝ → ℝ) (hone : centeredOddP1Coefficient v = 0) :
    fourCellOddOneThreeFiveSevenNineLowPart v =
      fourCellOddOneThreeFiveSevenNineLowProfile 0
        (centeredOddP3Coefficient v) (fourCellOddP5TailCoefficient v)
          (fourCellOddP7TailCoefficient v) (fourCellOddP9TailCoefficient v) := by
  unfold fourCellOddOneThreeFiveSevenNineLowPart
  rw [hone]

/-- Exact coupled finite/`P₁₁+` decomposition of an arbitrary `P₁`-orthogonal
odd profile.  No mixed row is discarded. -/
theorem fourCellOddCoreLocalQuadratic_P1Orthogonal_fiveMode_decomposition
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v)
    (hone : centeredOddP1Coefficient v = 0) :
    fourCellOddCoreLocalQuadratic v =
      fourCellOddCoreLocalQuadratic
        (fourCellOddOneThreeFiveSevenNineLowProfile 0
          (centeredOddP3Coefficient v) (fourCellOddP5TailCoefficient v)
            (fourCellOddP7TailCoefficient v) (fourCellOddP9TailCoefficient v)) +
      2 * fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile 0
          (centeredOddP3Coefficient v) (fourCellOddP5TailCoefficient v)
            (fourCellOddP7TailCoefficient v) (fourCellOddP9TailCoefficient v))
        (fourCellOddOneThreeFiveSevenNineResidual v) +
      fourCellOddCoreLocalQuadratic
        (fourCellOddOneThreeFiveSevenNineResidual v) := by
  have h := fourCellOddCoreLocal_oneThreeFiveSevenNine_decomposition v hv
  rw [fourCellOddOneThreeFiveSevenNineLowPart_eq_P1Orthogonal v hone] at h
  exact h

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
