import ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshRegularStructural
import ArithmeticHodge.Analysis.YoshidaEndpointOddOneThreeRawPolarization

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCoshSchurStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeilFourCellRealRescaleStructural
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointPotentialBound
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshRegularStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound

/-!
# Endpoint-preserving even cosh Schur reduction

The constant cosh pivot does not preserve the endpoint-zero production
domain.  The normalized seed `1 - x^2` does.  This file proves the exact
homogeneity needed to use that seed and packages the resulting production
Schur reduction.  Its residual is simultaneously even, endpoint-zero, and
zero in the wide-cosh coordinate, so it enters the existing coupled-core
estimate without a separate universal constant-row obligation.
-/

/-- The exact even four-cell bracket, named to expose its homogeneity. -/
def fourCellEvenExactBracket (w : ℝ → ℝ) : ℝ :=
  centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w

private theorem centeredEndpointCorrelation_const_mul
    (c : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    centeredEndpointCorrelation (fun x ↦ c * w x) t =
      c ^ 2 * centeredEndpointCorrelation w t := by
  unfold centeredEndpointCorrelation
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

private theorem fourCellEndpointPairing_const_mul
    (c : ℝ) (w : ℝ → ℝ) :
    fourCellEndpointPairing (fun x ↦ c * w x) =
      c ^ 2 * fourCellEndpointPairing w := by
  unfold fourCellEndpointPairing
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

private theorem centeredClippedPhysicalQuadratic_const_mul
    (a c : ℝ) (w : ℝ → ℝ) :
    centeredClippedPhysicalQuadratic a (fun x ↦ c * w x) =
      c ^ 2 * centeredClippedPhysicalQuadratic a w := by
  have hpotential :
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * (c * w x) ^ 2) =
        c ^ 2 *
          ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hmass :
      (∫ x : ℝ in -1..1, (c * w x) ^ 2) =
        c ^ 2 * ∫ x : ℝ in -1..1, w x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hregular :
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (a * t) *
            centeredEndpointCorrelation (fun x ↦ c * w x) t) =
        c ^ 2 *
          ∫ t : ℝ in 0..2,
            yoshidaRegularKernel (a * t) * centeredEndpointCorrelation w t := by
    simp_rw [centeredEndpointCorrelation_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  have hnegative :
      (∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * (c * w x)) =
        c * ∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * w x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hpositive :
      (∫ x : ℝ in -1..1, Real.exp (a * x / 2) * (c * w x)) =
        c * ∫ x : ℝ in -1..1, Real.exp (a * x / 2) * w x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  unfold centeredClippedPhysicalQuadratic
  rw [centeredRawLogEnergy_const_mul, hpotential, hmass, hregular,
    hnegative, hpositive]
  ring

/-- Exact degree-two homogeneity of the complete production bracket. -/
theorem fourCellEvenExactBracket_const_mul
    (c : ℝ) (w : ℝ → ℝ) :
    fourCellEvenExactBracket (fun x ↦ c * w x) =
      c ^ 2 * fourCellEvenExactBracket w := by
  unfold fourCellEvenExactBracket
  rw [centeredClippedPhysicalQuadratic_const_mul,
    fourCellEndpointPairing_const_mul]
  ring

/-- The endpoint-adapted low component is a scalar multiple of the fixed
endpoint-zero seed, rather than a constant function. -/
theorem fourCellEvenEndpointCoshLow_eq_const_mul_seed (w : ℝ → ℝ) :
    fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit =
      fun x ↦
        (fourCellPositiveCoshMoment w (fourCellOperatorHalfWidth / 2) *
          (fourCellPositiveCoshMoment fourCellEvenEndpointCoshSeed
            (fourCellOperatorHalfWidth / 2))⁻¹) *
          fourCellEvenEndpointCoshSeed x := by
  funext x
  unfold fourCellEvenCoshLow fourCellEvenEndpointCoshUnit
  ring

/-- Positivity of the one fixed endpoint seed propagates to every low line
selected by the endpoint-preserving cosh coordinate. -/
theorem fourCellEvenExactBracket_endpointCoshLow_nonnegative
    (w : ℝ → ℝ)
    (hseed : 0 ≤ fourCellEvenExactBracket fourCellEvenEndpointCoshSeed) :
    0 ≤ fourCellEvenExactBracket
      (fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit) := by
  rw [fourCellEvenEndpointCoshLow_eq_const_mul_seed,
    fourCellEvenExactBracket_const_mul]
  exact mul_nonneg (sq_nonneg _) hseed

/-- Production-only endpoint-cosh Schur reduction.  The tail hypothesis is
the existing coupled-core target on the endpoint-zero, zero-cosh residual;
the only other profile-dependent obligation is its exact mixed determinant.
-/
theorem fourCell_evenBracket_nonnegative_of_endpointCoshSchur
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hweven : Function.Even w) (hend : w (-1) = 0 ∧ w 1 = 0)
    (hseed : 0 ≤ fourCellEvenExactBracket fourCellEvenEndpointCoshSeed)
    (hcore : (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
        (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit))
    (hdet : fourCellExactBracketPolarization
          (fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit)
          (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit) ^ 2 ≤
        fourCellEvenExactBracket
            (fourCellEvenCoshLow w fourCellEvenEndpointCoshUnit) *
          fourCellEvenPolarFreeOperator
            (fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit)) :
    0 ≤ fourCellEvenExactBracket w := by
  let v : ℝ → ℝ :=
    fourCellEvenCoshResidual w fourCellEvenEndpointCoshUnit
  have hv : Continuous v :=
    (fourCellEvenEndpointCoshResidual_constraints
      w hw.continuous hweven hend).1
  have hveven : Function.Even v :=
    (fourCellEvenEndpointCoshResidual_constraints
      w hw.continuous hweven hend).2.1
  have hvzero : fourCellPositiveCoshMoment v
      (fourCellOperatorHalfWidth / 2) = 0 :=
    (fourCellEvenEndpointCoshResidual_constraints
      w hw.continuous hweven hend).2.2.2
  have hvDiff : ContDiff ℝ 1 v := by
    dsimp only [v]
    unfold fourCellEvenCoshResidual fourCellEvenCoshLow
      fourCellEvenEndpointCoshUnit fourCellEvenEndpointCoshSeed
    fun_prop
  have hvLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v :=
    hvDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)
  have htail : 0 ≤ fourCellEvenPolarFreeOperator v := by
    apply fourCellEvenPolarFreeOperator_nonnegative_of_coupledCore
      v hv hvLocal hveven hvzero
    simpa only [v] using hcore
  apply fourCell_evenBracket_nonnegative_of_normalizedCoshSchur
    w fourCellEvenEndpointCoshUnit hw.continuous
      fourCellEvenEndpointCoshUnit_continuous hweven
      fourCellEvenEndpointCoshUnit_even hvLocal
      fourCellPositiveCoshMoment_endpointCoshUnit
  · simpa only [fourCellEvenExactBracket] using
      fourCellEvenExactBracket_endpointCoshLow_nonnegative w hseed
  · simpa only [v] using htail
  · simpa only [fourCellEvenExactBracket, v] using hdet

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCoshSchurStructural
