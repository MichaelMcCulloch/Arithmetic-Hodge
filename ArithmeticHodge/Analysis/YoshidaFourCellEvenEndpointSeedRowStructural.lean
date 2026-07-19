import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCapacityCauchyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointCoshSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedRowStructural

noncomputable section

open YoshidaFourCellEvenEndpointCapacityCauchyStructural
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshRegularStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural

/-!
# The fixed endpoint-seed mixed row

After normalizing the endpoint-cosh coefficient, the outer even Schur problem
contains one fixed row.  This file identifies that row with the polarization
of the same coupled core used by the cutoff-eight proof, minus the already
positive scalar/regular polarization.  The positive wide-cosh rank cancels
exactly because the residual has zero wide-cosh moment.
-/

/-- Polarization of the singular/endpoint/prime coupled core. -/
def fourCellEvenZeroCoshCoupledCorePolarization
    (u v : ℝ → ℝ) : ℝ :=
  (fourCellEvenZeroCoshCoupledCore (u + v) -
      fourCellEvenZeroCoshCoupledCore u -
      fourCellEvenZeroCoshCoupledCore v) / 2

private theorem fourCellPositiveCoshMoment_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (lambda : ℝ) :
    fourCellPositiveCoshMoment (u + v) lambda =
      fourCellPositiveCoshMoment u lambda +
        fourCellPositiveCoshMoment v lambda := by
  have huInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (lambda * x) * u x) volume 0 1 :=
    ((Real.continuous_cosh.comp
      (continuous_const.mul continuous_id)).mul hu).intervalIntegrable _ _
  have hvInt : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (lambda * x) * v x) volume 0 1 :=
    ((Real.continuous_cosh.comp
      (continuous_const.mul continuous_id)).mul hv).intervalIntegrable _ _
  unfold fourCellPositiveCoshMoment
  rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * (u + v) x) =
      fun x ↦ Real.cosh (lambda * x) * u x +
        Real.cosh (lambda * x) * v x by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add huInt hvInt]

/-- The normalized endpoint-seed row is exactly the coupled-core mixed entry
minus the scalar/regular mixed entry.  No raw, potential, prime, or smooth
kernel term is estimated in this identity. -/
theorem fourCellEvenEndpointSeedRow_eq_core_sub_signed
    (v : ℝ → ℝ) (hv : Continuous v)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v)
    (heven : Function.Even v)
    (hzero : fourCellPositiveCoshMoment v
      (fourCellOperatorHalfWidth / 2) = 0) :
    fourCellEvenEndpointSeedRow v =
      fourCellEvenZeroCoshCoupledCorePolarization
          fourCellEvenEndpointCoshSeed v -
        fourCellEvenSignedMassRegularPolarization
          fourCellEvenEndpointCoshSeed v := by
  let s : ℝ → ℝ := fourCellEvenEndpointCoshSeed
  have hs : Continuous s := by
    simpa only [s] using fourCellEvenEndpointCoshSeed_continuous
  have hsDiff : ContDiff ℝ 1 s := by
    dsimp only [s]
    unfold fourCellEvenEndpointCoshSeed
    fun_prop
  have hsLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) s :=
    hsDiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)
  have hsEven : Function.Even s := by
    simpa only [s] using fourCellEvenEndpointCoshSeed_even
  have hsv : Continuous (s + v) := hs.add hv
  have hsvLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) (s + v) :=
    hsLocal.add hlocal
  have hsvEven : Function.Even (s + v) := hsEven.add heven
  have hCadd := fourCellPositiveCoshMoment_add s v hs hv
    (fourCellOperatorHalfWidth / 2)
  have hbracket :
      fourCellEvenExactBracket (s + v) =
        fourCellEvenExactBracket s +
          2 * fourCellExactBracketPolarization s v +
          fourCellEvenExactBracket v := by
    simpa only [fourCellEvenExactBracket] using
      fourCell_evenBracket_add_eq_low_add_mixed_add_tail s v hs hv
  have hpfAdd :
      fourCellEvenExactBracket (s + v) =
        fourCellEvenPolarFreeOperator (s + v) +
          8 * fourCellOperatorHalfWidth *
            fourCellPositiveCoshMoment (s + v)
              (fourCellOperatorHalfWidth / 2) ^ 2 := by
    simpa only [fourCellEvenExactBracket] using
      fourCell_evenBracket_eq_polarFree_add_coshRank
        (s + v) hsv hsvLocal hsvEven
  have hpfSeed :
      fourCellEvenExactBracket s =
        fourCellEvenPolarFreeOperator s +
          8 * fourCellOperatorHalfWidth *
            fourCellPositiveCoshMoment s
              (fourCellOperatorHalfWidth / 2) ^ 2 := by
    simpa only [fourCellEvenExactBracket] using
      fourCell_evenBracket_eq_polarFree_add_coshRank
        s hs hsLocal hsEven
  have hpfV :
      fourCellEvenExactBracket v =
        fourCellEvenPolarFreeOperator v +
          8 * fourCellOperatorHalfWidth *
            fourCellPositiveCoshMoment v
              (fourCellOperatorHalfWidth / 2) ^ 2 := by
    simpa only [fourCellEvenExactBracket] using
      fourCell_evenBracket_eq_polarFree_add_coshRank
        v hv hlocal heven
  have hnormalAdd :
      fourCellEvenPolarFreeOperator (s + v) =
        fourCellEvenZeroCoshCoupledCore (s + v) -
          fourCellEvenSignedMassRegularQuadratic (s + v) := by
    rw [fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular_of_even
      (s + v) hsv hsvLocal hsvEven]
    unfold fourCellEvenSignedMassRegularQuadratic
    ring
  have hnormalSeed :
      fourCellEvenPolarFreeOperator s =
        fourCellEvenZeroCoshCoupledCore s -
          fourCellEvenSignedMassRegularQuadratic s := by
    rw [fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular_of_even
      s hs hsLocal hsEven]
    unfold fourCellEvenSignedMassRegularQuadratic
    ring
  have hnormalV :
      fourCellEvenPolarFreeOperator v =
        fourCellEvenZeroCoshCoupledCore v -
          fourCellEvenSignedMassRegularQuadratic v := by
    rw [fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular_of_even
      v hv hlocal heven]
    unfold fourCellEvenSignedMassRegularQuadratic
    ring
  have hsigned := fourCellEvenSignedMassRegularQuadratic_add s v hs hv
  rw [hpfAdd, hpfSeed, hpfV, hCadd, hzero,
    hnormalAdd, hnormalSeed, hnormalV, hsigned] at hbracket
  change fourCellExactBracketPolarization s v = _
  unfold fourCellEvenZeroCoshCoupledCorePolarization
  dsimp only [s] at hbracket ⊢
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedRowStructural
