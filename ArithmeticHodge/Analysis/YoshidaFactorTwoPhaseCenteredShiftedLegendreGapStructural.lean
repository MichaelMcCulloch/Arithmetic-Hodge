import ArithmeticHodge.Analysis.ShiftedLegendreLogEnergyOrthogonalProjection
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual

set_option autoImplicit false

open MeasureTheory Polynomial
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCenteredShiftedLegendreGapStructural

open ShiftedLegendreBasis
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaFactorTwoPhaseIntrinsicHigherResidual

noncomputable section

/-!
# Moment gaps of centered shifted-Legendre modes

Transporting a shifted-Legendre polynomial from `[0,1]` to `[-1,1]`
preserves its orthogonality to every lower shifted-Legendre mode.  This is
the structural gap certificate used when higher modes are inserted into a
cutoff selector family.
-/

/-- A centered shifted-Legendre mode of degree `n` annihilates every
shifted-Legendre moment below any cutoff `k ≤ n`. -/
theorem centeredPolynomialLift_shiftedLegendreReal_momentsVanishBelow
    (n k : ℕ) (hk : k ≤ n) :
    centeredLegendreMomentsVanishBelow
      (centeredPolynomialLift (shiftedLegendreReal n)) k := by
  intro m hm
  rw [show (fun t : unitInterval ↦
      centeredPullback
          (centeredPolynomialLift (shiftedLegendreReal n)) (t : ℝ) *
        (shiftedLegendreReal m).eval (t : ℝ)) =
      fun t : unitInterval ↦
        (shiftedLegendreReal n).eval (t : ℝ) *
          (shiftedLegendreReal m).eval (t : ℝ) by
    funext t
    rw [centeredPullback_centeredPolynomialLift]]
  change (∫ t : unitInterval,
    (fun x : ℝ ↦ (shiftedLegendreReal n).eval x *
      (shiftedLegendreReal m).eval x) (t : ℝ)) = 0
  rw [integral_unitInterval_eq_intervalIntegral
    (fun x : ℝ ↦ (shiftedLegendreReal n).eval x *
      (shiftedLegendreReal m).eval x)]
  exact integral_shiftedLegendreReal_mul_eq_zero (by omega)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCenteredShiftedLegendreGapStructural
