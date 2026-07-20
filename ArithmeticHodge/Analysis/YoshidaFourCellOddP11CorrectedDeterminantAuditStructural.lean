import ArithmeticHodge.Analysis.YoshidaFourCellOddP11SelectorConstructionStructural

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CorrectedDeterminantAuditStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Aggregate form of the corrected odd determinant

The production determinant is not the conjunction of an independently
worst tail ratio and an independently worst selector ratio.  It is exactly
the rank-one Schur form of the *sum* of the retained four-mode profile and
the genuine `P₁₁+` tail.  This identity is the structural target that a
correlation-preserving proof must keep intact.
-/

/-- The corrected finite--tail determinant is exactly the aggregate
`P₁` Schur form.  In particular, its finite--tail middle term is the
polarization required to reconstruct the quadratic of `p + r`. -/
theorem fourCellOddP11CoupledRieszDefect_eq_aggregate
    (d e f g : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hrodd : Function.Odd r) :
    let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
    fourCellOddP11CoupledRieszDefect d e f g r =
      fourCellOddCoreLocalQuadratic centeredP1 *
          fourCellOddCoreLocalQuadratic (p + r) -
        fourCellOddCoreLocalBilinear centeredP1 (p + r) ^ 2 := by
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hp : ContDiff ℝ 1 p := by
    dsimp only [p]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hpodd : Function.Odd p := by
    dsimp only [p]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hP1 : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hP1odd : Function.Odd centeredP1 := by
    intro x
    unfold centeredP1
    ring
  have hquadratic := fourCellOddCoreLocalQuadratic_add
    p r hp.continuous hr.continuous
  have hrow :
      fourCellOddCoreLocalBilinear centeredP1 (p + r) =
        fourCellOddCoreLocalBilinear centeredP1 p +
          fourCellOddCoreLocalBilinear centeredP1 r := by
    calc
      fourCellOddCoreLocalBilinear centeredP1 (p + r) =
          fourCellOddCoreLocalBilinear (p + r) centeredP1 :=
        fourCellOddCoreLocalBilinear_comm
          centeredP1 (p + r) hP1.continuous (hp.add hr).continuous
      _ = fourCellOddCoreLocalBilinear p centeredP1 +
          fourCellOddCoreLocalBilinear r centeredP1 :=
        fourCellOddCoreLocalBilinear_add_left
          p r centeredP1 hp hr hP1 hpodd hrodd hP1odd
      _ = fourCellOddCoreLocalBilinear centeredP1 p +
          fourCellOddCoreLocalBilinear centeredP1 r := by
        rw [fourCellOddCoreLocalBilinear_comm p centeredP1
              hp.continuous hP1.continuous,
          fourCellOddCoreLocalBilinear_comm r centeredP1
              hr.continuous hP1.continuous]
  unfold fourCellOddP11CoupledRieszDefect
  rw [coupledP1TailSchurDefect_eq]
  dsimp only [p] at hquadratic hrow ⊢
  rw [hquadratic, hrow]

/-- Nonnegativity of the corrected determinant is therefore exactly one
aggregate Schur inequality, with no matched-factor hypothesis. -/
theorem fourCellOddP11CoupledRieszDefect_nonneg_iff_aggregate
    (d e f g : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hrodd : Function.Odd r) :
    let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
    0 ≤ fourCellOddP11CoupledRieszDefect d e f g r ↔
      fourCellOddCoreLocalBilinear centeredP1 (p + r) ^ 2 ≤
        fourCellOddCoreLocalQuadratic centeredP1 *
          fourCellOddCoreLocalQuadratic (p + r) := by
  rw [fourCellOddP11CoupledRieszDefect_eq_aggregate d e f g r hr hrodd]
  constructor <;> intro h <;> linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CorrectedDeterminantAuditStructural
