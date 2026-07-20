import ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalCoupledClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural

noncomputable section

open CenteredOddOneThreeEnergy
open CenteredEndpointCorrelation
open ShiftedLegendreCenteredLowModeL2
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaRegularKernelBound

/-!
# Exact function/coefficient bridge for the odd five-mode core

This module identifies the previously certified coefficient expression with
the actual core quadratic evaluated on the corresponding shifted-Legendre
profile.  It contains no new positivity estimate.
-/

private theorem centeredRawLogBilinear_const_mul_right_bridge
    (u v : ℝ → ℝ) (a : ℝ) :
    centeredRawLogBilinear u (fun x ↦ a * v x) =
      a * centeredRawLogBilinear u v := by
  unfold centeredRawLogBilinear
  rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1,
      ((u x - u y) * (a * v x - a * v y)) / |x - y|) =
      fun x ↦ a * ∫ y : ℝ in -1..1,
        ((u x - u y) * (v x - v y)) / |x - y| by
    funext x
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _hy
    ring,
    intervalIntegral.integral_const_mul]

private theorem endpointStripOdd_const_mul_bridge
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOdd (fun x ↦ a * v x) =
      fun z ↦ a * fourCellOddEndpointStripOdd v z := by
  funext z
  unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  ring

private theorem endpointStripOddRawPolarization_const_mul_right_bridge
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (a : ℝ) :
    fourCellOddEndpointStripOddRawPolarization u (fun x ↦ a * v x) =
      a * fourCellOddEndpointStripOddRawPolarization u v := by
  have hav : ContDiff ℝ 1 (fun x ↦ a * v x) := contDiff_const.mul hv
  rw [fourCellOddEndpointStripOddRawPolarization_eq_bilinear u _ hu hav,
    fourCellOddEndpointStripOddRawPolarization_eq_bilinear u v hu hv,
    endpointStripOdd_const_mul_bridge,
    centeredRawLogBilinear_const_mul_right_bridge]
  ring

private theorem rawStripPolarization_const_mul_right_bridge
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) (a : ℝ) :
    fourCellOddRawStripCancellationPolarization u (fun x ↦ a * v x) =
      a * fourCellOddRawStripCancellationPolarization u v := by
  have hav : ContDiff ℝ 1 (fun x ↦ a * v x) := contDiff_const.mul hv
  have havodd : Function.Odd (fun x ↦ a * v x) := by
    intro x
    change a * v (-x) = -(a * v x)
    rw [hvodd]
    ring
  rw [fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      u _ hu hav huodd havodd,
    fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      u v hu hv huodd hvodd,
    centeredRawLogBilinear_const_mul_right_bridge,
    endpointStripOddRawPolarization_const_mul_right_bridge u v hu hv]
  ring

private theorem endpointStripEven_const_mul_bridge
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripEven (fun x ↦ a * v x) =
      fun z ↦ a * fourCellOddEndpointStripEven v z := by
  funext z
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
  ring

private theorem endpointStripEvenMassBilinear_const_mul_right_bridge
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripEvenMassBilinear u (fun x ↦ a * v x) =
      a * fourCellOddEndpointStripEvenMassBilinear u v := by
  unfold fourCellOddEndpointStripEvenMassBilinear
  rw [endpointStripEven_const_mul_bridge]
  rw [show (fun z : ℝ ↦ fourCellOddEndpointStripEven u z *
      (a * fourCellOddEndpointStripEven v z)) =
      fun z ↦ a * (fourCellOddEndpointStripEven u z *
        fourCellOddEndpointStripEven v z) by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem endpointStripOddMassBilinear_const_mul_right_bridge
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOddMassBilinear u (fun x ↦ a * v x) =
      a * fourCellOddEndpointStripOddMassBilinear u v := by
  unfold fourCellOddEndpointStripOddMassBilinear
  rw [endpointStripOdd_const_mul_bridge]
  rw [show (fun z : ℝ ↦ fourCellOddEndpointStripOdd u z *
      (a * fourCellOddEndpointStripOdd v z)) =
      fun z ↦ a * (fourCellOddEndpointStripOdd u z *
        fourCellOddEndpointStripOdd v z) by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem integral_weight_mul_const_mul_right_bridge
    (W u v : ℝ → ℝ) (a l r : ℝ) :
    (∫ x : ℝ in l..r, W x * u x * (a * v x)) =
      a * ∫ x : ℝ in l..r, W x * u x * v x := by
  rw [show (fun x : ℝ ↦ W x * u x * (a * v x)) =
      fun x ↦ a * (W x * u x * v x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem integral_mul_const_mul_right_bridge
    (u v : ℝ → ℝ) (a l r : ℝ) :
    (∫ x : ℝ in l..r, u x * (a * v x)) =
      a * ∫ x : ℝ in l..r, u x * v x := by
  rw [show (fun x : ℝ ↦ u x * (a * v x)) =
      fun x ↦ a * (u x * v x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem correlationBilinear_const_mul_right_bridge
    (u v : ℝ → ℝ) (a t : ℝ) :
    factorTwoCenteredCorrelationBilinear u (fun x ↦ a * v x) t =
      a * factorTwoCenteredCorrelationBilinear u v t := by
  have hv : (fun x ↦ a * v x) = a • v := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hv]
  simpa only [one_mul, one_smul] using
    factorTwoCenteredCorrelationBilinear_smul_smul 1 a u v t

private theorem stripReducedBilinear_const_mul_right_bridge
    (u v : ℝ → ℝ) (a : ℝ) :
    fourCellOddStripReducedBilinear u (fun x ↦ a * v x) =
      a * fourCellOddStripReducedBilinear u v := by
  unfold fourCellOddStripReducedBilinear
  rw [endpointStripEvenMassBilinear_const_mul_right_bridge,
    endpointStripOddMassBilinear_const_mul_right_bridge,
    integral_weight_mul_const_mul_right_bridge,
    integral_mul_const_mul_right_bridge]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear u (fun x ↦ a * v x) t) =
      fun t ↦ a *
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear u v t) by
    funext t
    rw [correlationBilinear_const_mul_right_bridge]
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Homogeneity of the actual core polarization in its second argument. -/
theorem fourCellOddCoreLocalBilinear_const_mul_right
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) (a : ℝ) :
    fourCellOddCoreLocalBilinear u (fun x ↦ a * v x) =
      a * fourCellOddCoreLocalBilinear u v := by
  unfold fourCellOddCoreLocalBilinear
  rw [rawStripPolarization_const_mul_right_bridge u v hu hv huodd hvodd,
    stripReducedBilinear_const_mul_right_bridge]
  ring

private theorem endpointStripEvenMass_const_mul_bridge
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripEvenMass (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddEndpointStripEvenMass v := by
  unfold fourCellOddEndpointStripEvenMass
  rw [endpointStripEven_const_mul_bridge]
  rw [show (fun z : ℝ ↦
      (a * fourCellOddEndpointStripEven v z) ^ 2) =
      fun z ↦ a ^ 2 * fourCellOddEndpointStripEven v z ^ 2 by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem endpointStripOddMass_const_mul_bridge
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOddMass (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddEndpointStripOddMass v := by
  unfold fourCellOddEndpointStripOddMass
  rw [endpointStripOdd_const_mul_bridge]
  rw [show (fun z : ℝ ↦
      (a * fourCellOddEndpointStripOdd v z) ^ 2) =
      fun z ↦ a ^ 2 * fourCellOddEndpointStripOdd v z ^ 2 by
    funext z
    ring,
    intervalIntegral.integral_const_mul]
  ring

private theorem endpointStripOddRawEnergy_const_mul_bridge
    (v : ℝ → ℝ) (a : ℝ) :
    fourCellOddEndpointStripOddRawEnergy (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddEndpointStripOddRawEnergy v := by
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [endpointStripOdd_const_mul_bridge,
    YoshidaEndpointOddOneThreeRawPolarization.centeredRawLogEnergy_const_mul]
  ring

private theorem rawStripReserve_const_mul_bridge
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v)
    (a : ℝ) :
    fourCellOddRawStripCancellationReserve (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddRawStripCancellationReserve v := by
  have hav : ContDiff ℝ 1 (fun x ↦ a * v x) := contDiff_const.mul hv
  have havodd : Function.Odd (fun x ↦ a * v x) := by
    intro x
    change a * v (-x) = -(a * v x)
    rw [hvodd]
    ring
  have hvLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) v :=
    hv.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have havLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (fun x ↦ a * v x) :=
    hav.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hfoldV := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    v hvLocal hvodd
  have hfoldAV := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    (fun x ↦ a * v x) havLocal havodd
  unfold fourCellOddRawStripCancellationReserve
  rw [← hfoldAV, ← hfoldV,
    endpointStripOddRawEnergy_const_mul_bridge,
    YoshidaEndpointOddOneThreeRawPolarization.centeredRawLogEnergy_const_mul]
  ring

private theorem integral_weight_mul_sq_const_mul_bridge
    (W v : ℝ → ℝ) (a l r : ℝ) :
    (∫ x : ℝ in l..r, W x * (a * v x) ^ 2) =
      a ^ 2 * ∫ x : ℝ in l..r, W x * v x ^ 2 := by
  rw [show (fun x : ℝ ↦ W x * (a * v x) ^ 2) =
      fun x ↦ a ^ 2 * (W x * v x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem integral_sq_const_mul_bridge
    (v : ℝ → ℝ) (a l r : ℝ) :
    (∫ x : ℝ in l..r, (a * v x) ^ 2) =
      a ^ 2 * ∫ x : ℝ in l..r, v x ^ 2 := by
  rw [show (fun x : ℝ ↦ (a * v x) ^ 2) =
      fun x ↦ a ^ 2 * v x ^ 2 by
    funext x
    ring,
    intervalIntegral.integral_const_mul]

private theorem centeredCorrelation_const_mul_bridge
    (v : ℝ → ℝ) (a t : ℝ) :
    centeredEndpointCorrelation (fun x ↦ a * v x) t =
      a ^ 2 * centeredEndpointCorrelation v t := by
  have hav : (fun x ↦ a * v x) = a • v := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hav, ← factorTwoCenteredCorrelationBilinear_self,
    factorTwoCenteredCorrelationBilinear_smul_smul,
    factorTwoCenteredCorrelationBilinear_self]
  ring

/-- Homogeneity of the actual core diagonal on smooth odd profiles. -/
theorem fourCellOddCoreLocalQuadratic_const_mul
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v)
    (a : ℝ) :
    fourCellOddCoreLocalQuadratic (fun x ↦ a * v x) =
      a ^ 2 * fourCellOddCoreLocalQuadratic v := by
  rw [fourCellOddCoreLocalQuadratic_eq_retained_sub_signed,
    fourCellOddCoreLocalQuadratic_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointQuadratic
    fourCellOddRetainedPrimePotentialQuadratic
    fourCellOddSignedMassRegularQuadratic
  rw [rawStripReserve_const_mul_bridge v hv hvodd a,
    endpointStripEvenMass_const_mul_bridge,
    endpointStripOddMass_const_mul_bridge,
    integral_weight_mul_sq_const_mul_bridge,
    integral_sq_const_mul_bridge]
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation (fun x ↦ a * v x) t) =
      fun t ↦ a ^ 2 *
        (yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation v t) by
    funext t
    rw [centeredCorrelation_const_mul_bridge]
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Symmetry of the actual core polarization. -/
theorem fourCellOddCoreLocalBilinear_comm
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    fourCellOddCoreLocalBilinear u v =
      fourCellOddCoreLocalBilinear v u := by
  have huv := fourCellOddCoreLocalQuadratic_add u v hu hv
  have hvu := fourCellOddCoreLocalQuadratic_add v u hv hu
  have hadd : u + v = v + u := add_comm u v
  rw [hadd] at huv
  linarith

private theorem fourCellOddCoreLocalQuadratic_neg
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (hvodd : Function.Odd v) :
    fourCellOddCoreLocalQuadratic (-v) =
      fourCellOddCoreLocalQuadratic v := by
  calc
    fourCellOddCoreLocalQuadratic (-v) =
        fourCellOddCoreLocalQuadratic (fun x ↦ (-1 : ℝ) * v x) := by
      congr 1
      funext x
      simp
    _ = (-1 : ℝ) ^ 2 * fourCellOddCoreLocalQuadratic v :=
      fourCellOddCoreLocalQuadratic_const_mul v hv hvodd (-1)
    _ = fourCellOddCoreLocalQuadratic v := by ring

private theorem fourCellOddCoreLocalBilinear_neg_right
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    fourCellOddCoreLocalBilinear u (-v) =
      -fourCellOddCoreLocalBilinear u v := by
  calc
    fourCellOddCoreLocalBilinear u (-v) =
        fourCellOddCoreLocalBilinear u (fun x ↦ (-1 : ℝ) * v x) := by
      congr 1
      funext x
      simp
    _ = (-1 : ℝ) * fourCellOddCoreLocalBilinear u v :=
      fourCellOddCoreLocalBilinear_const_mul_right
        u v hu hv huodd hvodd (-1)
    _ = -fourCellOddCoreLocalBilinear u v := by ring

private theorem fourCellOddCoreLocalQuadratic_parallelogram
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    fourCellOddCoreLocalQuadratic (u + v) +
        fourCellOddCoreLocalQuadratic (u - v) =
      2 * fourCellOddCoreLocalQuadratic u +
        2 * fourCellOddCoreLocalQuadratic v := by
  have hplus := fourCellOddCoreLocalQuadratic_add
    u v hu.continuous hv.continuous
  have hminus := fourCellOddCoreLocalQuadratic_add
    u (-v) hu.continuous hv.neg.continuous
  rw [fourCellOddCoreLocalBilinear_neg_right u v hu hv huodd hvodd,
    fourCellOddCoreLocalQuadratic_neg v hv hvodd] at hminus
  rw [sub_eq_add_neg]
  linarith

private theorem odd_sub_bridge
    {u v : ℝ → ℝ} (huodd : Function.Odd u) (hvodd : Function.Odd v) :
    Function.Odd (u - v) := by
  intro x
  simp only [Pi.sub_apply]
  rw [huodd, hvodd]
  ring

private theorem fourCellOddCoreLocalQuadratic_three_point_difference
    (u v w : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w)
    (huodd : Function.Odd u) (hvodd : Function.Odd v)
    (hwodd : Function.Odd w) :
    fourCellOddCoreLocalQuadratic (u + v + w) -
        fourCellOddCoreLocalQuadratic (u + v - w) =
      (fourCellOddCoreLocalQuadratic (u + w) -
          fourCellOddCoreLocalQuadratic (u - w)) +
        (fourCellOddCoreLocalQuadratic (v + w) -
          fourCellOddCoreLocalQuadratic (v - w)) := by
  have h1 := fourCellOddCoreLocalQuadratic_parallelogram
    (u + w) v (hu.add hw) hv (huodd.add hwodd) hvodd
  have h2 := fourCellOddCoreLocalQuadratic_parallelogram
    (u - w) v (hu.sub hw) hv (odd_sub_bridge huodd hwodd) hvodd
  have h3 := fourCellOddCoreLocalQuadratic_parallelogram
    (v + w) u (hv.add hw) hu (hvodd.add hwodd) huodd
  have h4 := fourCellOddCoreLocalQuadratic_parallelogram
    (v - w) u (hv.sub hw) hu (odd_sub_bridge hvodd hwodd) huodd
  have hFneg := fourCellOddCoreLocalQuadratic_neg
    (u - v - w) ((hu.sub hv).sub hw)
      (odd_sub_bridge (odd_sub_bridge huodd hvodd) hwodd)
  have hDneg := fourCellOddCoreLocalQuadratic_neg
    (u - v + w) ((hu.sub hv).add hw)
      ((odd_sub_bridge huodd hvodd).add hwodd)
  have h11 : (u + w) + v = u + v + w := by abel
  have h12 : (u + w) - v = u - v + w := by abel
  have h21 : (u - w) + v = u + v - w := by abel
  have h22 : (u - w) - v = u - v - w := by abel
  have h31 : (v + w) + u = u + v + w := by abel
  have h32 : (v + w) - u = -(u - v - w) := by abel
  have h41 : (v - w) + u = u + v - w := by abel
  have h42 : (v - w) - u = -(u - v + w) := by abel
  rw [h11, h12] at h1
  rw [h21, h22] at h2
  rw [h31, h32, hFneg] at h3
  rw [h41, h42, hDneg] at h4
  linarith

/-- Additivity of the actual core polarization in its first argument. -/
theorem fourCellOddCoreLocalBilinear_add_left
    (u v w : ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w)
    (huodd : Function.Odd u) (hvodd : Function.Odd v)
    (hwodd : Function.Odd w) :
    fourCellOddCoreLocalBilinear (u + v) w =
      fourCellOddCoreLocalBilinear u w +
        fourCellOddCoreLocalBilinear v w := by
  have hdelta := fourCellOddCoreLocalQuadratic_three_point_difference
    u v w hu hv hw huodd hvodd hwodd
  have huv : ContDiff ℝ 1 (u + v) := hu.add hv
  have huvodd : Function.Odd (u + v) := huodd.add hvodd
  have hsumPlus := fourCellOddCoreLocalQuadratic_add
    (u + v) w huv.continuous hw.continuous
  have hsumMinus := fourCellOddCoreLocalQuadratic_add
    (u + v) (-w) huv.continuous hw.neg.continuous
  have huPlus := fourCellOddCoreLocalQuadratic_add
    u w hu.continuous hw.continuous
  have huMinus := fourCellOddCoreLocalQuadratic_add
    u (-w) hu.continuous hw.neg.continuous
  have hvPlus := fourCellOddCoreLocalQuadratic_add
    v w hv.continuous hw.continuous
  have hvMinus := fourCellOddCoreLocalQuadratic_add
    v (-w) hv.continuous hw.neg.continuous
  rw [fourCellOddCoreLocalBilinear_neg_right
        (u + v) w huv hw huvodd hwodd,
      fourCellOddCoreLocalQuadratic_neg w hw hwodd] at hsumMinus
  rw [fourCellOddCoreLocalBilinear_neg_right u w hu hw huodd hwodd,
      fourCellOddCoreLocalQuadratic_neg w hw hwodd] at huMinus
  rw [fourCellOddCoreLocalBilinear_neg_right v w hv hw hvodd hwodd,
      fourCellOddCoreLocalQuadratic_neg w hw hwodd] at hvMinus
  have hsumMinusArg : (u + v) + (-w) = u + v - w := by abel
  have huMinusArg : u + (-w) = u - w := by abel
  have hvMinusArg : v + (-w) = v - w := by abel
  rw [hsumMinusArg] at hsumMinus
  rw [huMinusArg] at huMinus
  rw [hvMinusArg] at hvMinus
  linarith

/-- Homogeneity of the actual core polarization in its first argument. -/
theorem fourCellOddCoreLocalBilinear_const_mul_left
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v) (a : ℝ) :
    fourCellOddCoreLocalBilinear (fun x ↦ a * u x) v =
      a * fourCellOddCoreLocalBilinear u v := by
  have hau : ContDiff ℝ 1 (fun x ↦ a * u x) := contDiff_const.mul hu
  calc
    fourCellOddCoreLocalBilinear (fun x ↦ a * u x) v =
        fourCellOddCoreLocalBilinear v (fun x ↦ a * u x) :=
      fourCellOddCoreLocalBilinear_comm _ _ hau.continuous hv.continuous
    _ = a * fourCellOddCoreLocalBilinear v u :=
      fourCellOddCoreLocalBilinear_const_mul_right
        v u hv hu hvodd huodd a
    _ = a * fourCellOddCoreLocalBilinear u v := by
      rw [fourCellOddCoreLocalBilinear_comm v u hv.continuous hu.continuous]

private theorem odd_const_mul_bridge
    {v : ℝ → ℝ} (hvodd : Function.Odd v) (a : ℝ) :
    Function.Odd (fun x ↦ a * v x) := by
  intro x
  change a * v (-x) = -(a * v x)
  rw [hvodd]
  ring

private theorem contDiff_centeredP1_bridge :
    ContDiff ℝ 1 centeredP1 := by
  unfold centeredP1
  fun_prop

private theorem contDiff_centeredP3_bridge :
    ContDiff ℝ 1 centeredP3 := by
  unfold centeredP3
  fun_prop

private theorem contDiff_factorTwoCenteredP5_bridge :
    ContDiff ℝ 1 factorTwoCenteredP5 := by
  unfold factorTwoCenteredP5
  fun_prop

private theorem contDiff_factorTwoCenteredP7_bridge :
    ContDiff ℝ 1 factorTwoCenteredP7 := by
  rw [show factorTwoCenteredP7 = fun x ↦
      (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
    funext x
    exact factorTwoCenteredP7_eq x]
  fun_prop

private theorem contDiff_factorTwoCenteredP9_bridge :
    ContDiff ℝ 1 factorTwoCenteredP9 := by
  rw [show factorTwoCenteredP9 = fun x ↦
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 by
    funext x
    exact factorTwoCenteredP9_eq x]
  fun_prop

private theorem odd_centeredP1_bridge : Function.Odd centeredP1 := by
  intro x
  unfold centeredP1
  ring

private theorem odd_centeredP3_bridge : Function.Odd centeredP3 := by
  intro x
  unfold centeredP3
  ring

/-- Coefficient expansion of the `P₁/P₃/P₅` core row against any
smooth odd test profile. -/
theorem fourCellOddCoreLocalBilinear_oneThreeFiveLowProfile_left
    (c d e : ℝ) (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hwodd : Function.Odd w) :
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveLowProfile c d e) w =
      c * fourCellOddCoreLocalBilinear centeredP1 w +
        d * fourCellOddCoreLocalBilinear centeredP3 w +
          e * fourCellOddCoreLocalBilinear factorTwoCenteredP5 w := by
  let p1 : ℝ → ℝ := fun x ↦ c * centeredP1 x
  let p3 : ℝ → ℝ := fun x ↦ d * centeredP3 x
  let p5 : ℝ → ℝ := fun x ↦ e * factorTwoCenteredP5 x
  have hp1 : ContDiff ℝ 1 p1 := by
    dsimp only [p1]
    exact contDiff_const.mul contDiff_centeredP1_bridge
  have hp3 : ContDiff ℝ 1 p3 := by
    dsimp only [p3]
    exact contDiff_const.mul contDiff_centeredP3_bridge
  have hp5 : ContDiff ℝ 1 p5 := by
    dsimp only [p5]
    exact contDiff_const.mul contDiff_factorTwoCenteredP5_bridge
  have hp1odd : Function.Odd p1 := by
    dsimp only [p1]
    exact odd_const_mul_bridge odd_centeredP1_bridge c
  have hp3odd : Function.Odd p3 := by
    dsimp only [p3]
    exact odd_const_mul_bridge odd_centeredP3_bridge d
  have hp5odd : Function.Odd p5 := by
    dsimp only [p5]
    exact odd_const_mul_bridge odd_factorTwoCenteredP5 e
  have hprofile :
      fourCellOddOneThreeFiveLowProfile c d e = (p1 + p3) + p5 := by
    funext x
    dsimp only [p1, p3, p5]
    unfold fourCellOddOneThreeFiveLowProfile
      factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply]
  rw [hprofile,
    fourCellOddCoreLocalBilinear_add_left
      (p1 + p3) p5 w (hp1.add hp3) hp5 hw
        (hp1odd.add hp3odd) hp5odd hwodd,
    fourCellOddCoreLocalBilinear_add_left
      p1 p3 w hp1 hp3 hw hp1odd hp3odd hwodd]
  dsimp only [p1, p3, p5]
  rw [fourCellOddCoreLocalBilinear_const_mul_left
      centeredP1 w contDiff_centeredP1_bridge hw
        odd_centeredP1_bridge hwodd c,
    fourCellOddCoreLocalBilinear_const_mul_left
      centeredP3 w contDiff_centeredP3_bridge hw
        odd_centeredP3_bridge hwodd d,
    fourCellOddCoreLocalBilinear_const_mul_left
      factorTwoCenteredP5 w contDiff_factorTwoCenteredP5_bridge hw
        odd_factorTwoCenteredP5 hwodd e]

/-- Exact diagonal identity for the already normalized `P₁/P₃/P₅` block. -/
theorem fourCellOddCoreLocalQuadratic_oneThreeFiveLowProfile_eq_perturbed
    (c d e : ℝ) :
    fourCellOddCoreLocalQuadratic
        (fourCellOddOneThreeFiveLowProfile c d e) =
      fourCellOddOneThreeFivePerturbedQuadratic c d e := by
  have hdiag :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq c d e
  have hpert :=
    fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed c d e
  unfold fourCellOddCoreLocalQuadratic
  rw [hdiag, hpert]

/-- The certified five-mode coefficient expression is exactly the actual
core quadratic of the corresponding function. -/
theorem fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression
    (c d e f g : ℝ) :
    fourCellOddCoreLocalQuadratic
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) =
      fourCellOddFiveModeCoreExpression c d e f g := by
  let p : ℝ → ℝ := fourCellOddOneThreeFiveLowProfile c d e
  let p7 : ℝ → ℝ := fun x ↦ f * factorTwoCenteredP7 x
  let p9 : ℝ → ℝ := fun x ↦ g * factorTwoCenteredP9 x
  have hp : ContDiff ℝ 1 p := by
    dsimp only [p]
    exact contDiff_fourCellOddOneThreeFiveLowProfile c d e
  have hpodd : Function.Odd p := by
    dsimp only [p]
    exact odd_fourCellOddOneThreeFiveLowProfile c d e
  have hp7 : ContDiff ℝ 1 p7 := by
    dsimp only [p7]
    exact contDiff_const.mul contDiff_factorTwoCenteredP7_bridge
  have hp7odd : Function.Odd p7 := by
    dsimp only [p7]
    exact odd_const_mul_bridge odd_factorTwoCenteredP7 f
  have hp9 : ContDiff ℝ 1 p9 := by
    dsimp only [p9]
    exact contDiff_const.mul contDiff_factorTwoCenteredP9_bridge
  have hp9odd : Function.Odd p9 := by
    dsimp only [p9]
    exact odd_const_mul_bridge odd_factorTwoCenteredP9 g
  have hprofile :
      fourCellOddOneThreeFiveSevenNineLowProfile c d e f g =
        (p + p7) + p9 := by
    funext x
    dsimp only [p, p7, p9]
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
    simp only [Pi.add_apply]
  have hpQ : fourCellOddCoreLocalQuadratic p =
      fourCellOddOneThreeFivePerturbedQuadratic c d e := by
    dsimp only [p]
    exact fourCellOddCoreLocalQuadratic_oneThreeFiveLowProfile_eq_perturbed
      c d e
  have hp7Q : fourCellOddCoreLocalQuadratic p7 =
      f ^ 2 * fourCellOddCoreLocalQuadratic factorTwoCenteredP7 := by
    dsimp only [p7]
    exact fourCellOddCoreLocalQuadratic_const_mul
      factorTwoCenteredP7 contDiff_factorTwoCenteredP7_bridge
        odd_factorTwoCenteredP7 f
  have hp9Q : fourCellOddCoreLocalQuadratic p9 =
      g ^ 2 * fourCellOddCoreLocalQuadratic factorTwoCenteredP9 := by
    dsimp only [p9]
    exact fourCellOddCoreLocalQuadratic_const_mul
      factorTwoCenteredP9 contDiff_factorTwoCenteredP9_bridge
        odd_factorTwoCenteredP9 g
  have hpP7base :=
    fourCellOddCoreLocalBilinear_oneThreeFiveLowProfile_left
      c d e factorTwoCenteredP7 contDiff_factorTwoCenteredP7_bridge
        odd_factorTwoCenteredP7
  have hpP7 : fourCellOddCoreLocalBilinear p p7 =
      f * (c * fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP7 +
        d * fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP7 +
          e * fourCellOddCoreLocalBilinear
            factorTwoCenteredP5 factorTwoCenteredP7) := by
    have hscale := fourCellOddCoreLocalBilinear_const_mul_right
      p factorTwoCenteredP7 hp contDiff_factorTwoCenteredP7_bridge
        hpodd odd_factorTwoCenteredP7 f
    dsimp only [p7] at ⊢
    rw [hscale]
    rw [hpP7base]
  have hpP9base :=
    fourCellOddCoreLocalBilinear_oneThreeFiveLowProfile_left
      c d e factorTwoCenteredP9 contDiff_factorTwoCenteredP9_bridge
        odd_factorTwoCenteredP9
  have hpP9 : fourCellOddCoreLocalBilinear p p9 =
      g * (c * fourCellOddCoreLocalBilinear centeredP1 factorTwoCenteredP9 +
        d * fourCellOddCoreLocalBilinear centeredP3 factorTwoCenteredP9 +
          e * fourCellOddCoreLocalBilinear
            factorTwoCenteredP5 factorTwoCenteredP9) := by
    have hscale := fourCellOddCoreLocalBilinear_const_mul_right
      p factorTwoCenteredP9 hp contDiff_factorTwoCenteredP9_bridge
        hpodd odd_factorTwoCenteredP9 g
    dsimp only [p9] at ⊢
    rw [hscale]
    rw [hpP9base]
  have hp7P9 : fourCellOddCoreLocalBilinear p7 p9 =
      f * g * fourCellOddCoreLocalBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 := by
    have hleft := fourCellOddCoreLocalBilinear_const_mul_left
      factorTwoCenteredP7 factorTwoCenteredP9
        contDiff_factorTwoCenteredP7_bridge contDiff_factorTwoCenteredP9_bridge
        odd_factorTwoCenteredP7 odd_factorTwoCenteredP9 f
    have hright := fourCellOddCoreLocalBilinear_const_mul_right
      p7 factorTwoCenteredP9 hp7 contDiff_factorTwoCenteredP9_bridge
        hp7odd odd_factorTwoCenteredP9 g
    dsimp only [p7, p9] at ⊢
    rw [hright]
    rw [hleft]
    ring
  have hinner := fourCellOddCoreLocalQuadratic_add
    p p7 hp.continuous hp7.continuous
  have houter := fourCellOddCoreLocalQuadratic_add
    (p + p7) p9 (hp.add hp7).continuous hp9.continuous
  have houterRow := fourCellOddCoreLocalBilinear_add_left
    p p7 p9 hp hp7 hp9 hpodd hp7odd hp9odd
  rw [hprofile]
  rw [houter, hinner, houterRow, hpQ, hp7Q, hp9Q,
    hpP7, hpP9, hp7P9]
  unfold fourCellOddFiveModeCoreExpression
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
