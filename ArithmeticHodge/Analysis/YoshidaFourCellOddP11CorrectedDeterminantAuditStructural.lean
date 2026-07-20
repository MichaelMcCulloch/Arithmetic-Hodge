import ArithmeticHodge.Analysis.YoshidaFourCellOddP11SelectorConstructionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalCoupledClosureStructural

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CorrectedDeterminantAuditStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
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

private theorem centeredOddP1Coefficient_lowProfile_without_P1_eq_zero
    (d e f g : ℝ) :
    centeredOddP1Coefficient
      (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g) = 0 := by
  unfold fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  rw [show factorTwoCenteredP7 = fun x ↦
      (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
    funext x
    exact factorTwoCenteredP7_eq x,
    show factorTwoCenteredP9 = fun x ↦
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 by
      funext x
      exact factorTwoCenteredP9_eq x]
  unfold centeredOddP1Coefficient centeredP1 centeredP3 factorTwoCenteredP5
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num
  ring

private theorem centeredOddP1Coefficient_lowProfile_add_P11Plus_eq_zero
    (d e f g : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hr1 : centeredOddP1Coefficient r = 0) :
    centeredOddP1Coefficient
      (fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g + r) = 0 := by
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  have hp : Continuous p :=
    (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g).continuous
  have hp1 : centeredOddP1Coefficient p = 0 := by
    dsimp only [p]
    exact centeredOddP1Coefficient_lowProfile_without_P1_eq_zero d e f g
  change centeredOddP1Coefficient (p + r) = 0
  unfold centeredOddP1Coefficient at hp1 hr1 ⊢
  simp only [Pi.add_apply]
  rw [show (fun x : ℝ ↦ (p x + r x) * centeredP1 x) =
      fun x ↦ p x * centeredP1 x + r x * centeredP1 x by
    funext x
    ring]
  have hpInt : IntervalIntegrable (fun x : ℝ ↦ p x * centeredP1 x)
      volume (-1) 1 :=
    (hp.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  have hrInt : IntervalIntegrable (fun x : ℝ ↦ r x * centeredP1 x)
      volume (-1) 1 :=
    (hr.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _
  have hsplit :
      (∫ x : ℝ in -1..1,
          p x * centeredP1 x + r x * centeredP1 x) =
        (∫ x : ℝ in -1..1, p x * centeredP1 x) +
          ∫ x : ℝ in -1..1, r x * centeredP1 x := by
    exact intervalIntegral.integral_add hpInt hrInt
  rw [hsplit]
  dsimp only [p]
  linarith

/-- The universal corrected `P₁/P₁₁+` determinant is neither stronger nor
weaker than the original analytic frontier: it is exactly the complete
`P₁`-orthogonal form-dual inequality. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_iff_P1OrthogonalFormDual :
    FourCellOddP11CoupledRieszDefectNonnegative ↔
      FourCellOddP1OrthogonalFormDualBound := by
  constructor
  · intro hdefect
    exact fourCellOddP1OrthogonalFormDualBound_of_fiveModeP11CoupledTail
      (fourCellOddP1FiveModeP11CoupledTailBound_of_correctedDefect hdefect)
  · intro hdual d e f g r hr hrodd hr1 _hr3 _hr5 _hr7 _hr9
    let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
    have hp : ContDiff ℝ 1 p := by
      dsimp only [p]
      exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
    have hpodd : Function.Odd p := by
      dsimp only [p]
      exact odd_fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
    have hsum1 : centeredOddP1Coefficient (p + r) = 0 := by
      dsimp only [p]
      exact centeredOddP1Coefficient_lowProfile_add_P11Plus_eq_zero
        d e f g r hr.continuous hr1
    have haggregate := hdual (p + r) (hp.add hr) (hpodd.add hrodd) hsum1
    exact (fourCellOddP11CoupledRieszDefect_nonneg_iff_aggregate
      d e f g r hr hrodd).2 haggregate

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CorrectedDeterminantAuditStructural
