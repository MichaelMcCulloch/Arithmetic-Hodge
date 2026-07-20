import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRepresenterStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedResidualRepresenterStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogEigen
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality
open ShiftedLogKernelCrossEnergy
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFourCellOddP11FiveModeThreeHalvesStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11GalerkinResidualRepresenterStructural
open YoshidaFourCellOddP13AugmentedDecompositionStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Exact cutoff-13 representer for the augmented odd Galerkin residual

The augmented residual is a six-mode polynomial (`P1` through `P11`).
Against the genuine `P13+` space, both its global raw-log row and its scalar
mass row vanish.  This file turns the surviving endpoint/regular row into an
exact two-strip `L²` representer.  Subtracting an arbitrary six-mode selector
then leaves one finite norm inequality which implies the universal residual
dual required by the augmented Galerkin--Riesz reduction.
-/

/-- The complete retained odd cutoff through `P11`. -/
def fourCellOddP13SixModeProfile
    (c d e f g h : ℝ) : ℝ → ℝ := fun x ↦
  fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x +
    h * fourCellOddP11DirectTail x

theorem contDiff_fourCellOddP13SixModeProfile
    (c d e f g h : ℝ) :
    ContDiff ℝ 1 (fourCellOddP13SixModeProfile c d e f g h) := by
  unfold fourCellOddP13SixModeProfile
  exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g).add
    (contDiff_const.mul contDiff_fourCellOddP11DirectTail)

theorem odd_fourCellOddP13SixModeProfile
    (c d e f g h : ℝ) :
    Function.Odd (fourCellOddP13SixModeProfile c d e f g h) := by
  intro x
  unfold fourCellOddP13SixModeProfile
  rw [odd_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g,
    odd_fourCellOddP11DirectTail]
  ring

/-- The augmented Galerkin residual is the six-mode vector with coordinates
`(1,-a3,-a5,-a7,-a9,-a11)`. -/
theorem fourCellOddP13AugmentedGalerkinResidualProfile_eq_sixMode
    (a3 a5 a7 a9 a11 : ℝ) :
    fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11 =
      fourCellOddP13SixModeProfile 1 (-a3) (-a5) (-a7) (-a9) (-a11) := by
  funext x
  unfold fourCellOddP13AugmentedGalerkinResidualProfile
    fourCellOddP11AugmentedLowProfile fourCellOddP13SixModeProfile
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  ring

/-- Polynomial realization of the complete retained odd cutoff. -/
def fourCellOddP13SixModePolynomial
    (c d e f g h : ℝ) : ℝ[X] :=
  fourCellOddFiveModePolynomial c d e f g +
    h • (-(centeredShiftedLegendreReal 11))

theorem fourCellOddP13SixModePolynomial_eval
    (c d e f g h x : ℝ) :
    (fourCellOddP13SixModePolynomial c d e f g h).eval x =
      fourCellOddP13SixModeProfile c d e f g h x := by
  unfold fourCellOddP13SixModePolynomial fourCellOddP13SixModeProfile
  simp only [Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_neg,
    smul_eq_mul]
  rw [fourCellOddFiveModePolynomial_eval]
  unfold fourCellOddP11DirectTail
  ring

/-- Reflection-odd endpoint-strip pullback of the six-mode polynomial. -/
def fourCellOddP13SixModeEndpointStripOddPolynomial
    (c d e f g h : ℝ) : ℝ[X] :=
  let p := fourCellOddP13SixModePolynomial c d e f g h
  (1 / 2 : ℝ) •
    (p.comp ((1 / 5 : ℝ) • X + C (4 / 5 : ℝ)) -
      p.comp ((-(1 / 5 : ℝ)) • X + C (4 / 5 : ℝ)))

/-- Unit-interval form of the reflection-odd strip polynomial. -/
def fourCellOddP13SixModeEndpointStripOddUnitPolynomial
    (c d e f g h : ℝ) : ℝ[X] :=
  (fourCellOddP13SixModeEndpointStripOddPolynomial c d e f g h).comp
    ((2 : ℝ) • X - C 1)

theorem fourCellOddP13SixModeEndpointStripOddPolynomial_eval
    (c d e f g h z : ℝ) :
    (fourCellOddP13SixModeEndpointStripOddPolynomial c d e f g h).eval z =
      fourCellOddEndpointStripOdd
        (fourCellOddP13SixModeProfile c d e f g h) z := by
  unfold fourCellOddP13SixModeEndpointStripOddPolynomial
    fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  dsimp only
  simp only [Polynomial.eval_smul, Polynomial.eval_sub,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, smul_eq_mul]
  rw [fourCellOddP13SixModePolynomial_eval,
    fourCellOddP13SixModePolynomial_eval]
  have hplus : (4 / 5 : ℝ) + z / 5 = z * (1 / 5) + 4 / 5 := by ring
  have hminus : (4 / 5 : ℝ) + -z / 5 = z * (-(1 / 5)) + 4 / 5 := by ring
  rw [hplus, hminus]
  ring

theorem centeredPullback_sixModeEndpointStripOdd_eq_eval
    (c d e f g h t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd
          (fourCellOddP13SixModeProfile c d e f g h)) t =
      (fourCellOddP13SixModeEndpointStripOddUnitPolynomial
        c d e f g h).eval t := by
  unfold fourCellOddP13SixModeEndpointStripOddUnitPolynomial centeredPullback
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X,
    Polynomial.eval_C, smul_eq_mul]
  rw [fourCellOddP13SixModeEndpointStripOddPolynomial_eval]

/-- Exact upper-strip density of the adverse raw endpoint row. -/
def fourCellOddP13SixModeRawUpperRepresenter
    (c d e f g h : ℝ) (x : ℝ) : ℝ :=
  let K := shiftedLogKernel
    (fourCellOddP13SixModeEndpointStripOddUnitPolynomial c d e f g h)
  K.eval ((5 * x - 3) / 2) - K.eval ((5 - 5 * x) / 2)

/-- Polynomiality turns the singular endpoint-strip polarization into an
ordinary upper-strip pairing. -/
theorem fourCellOddEndpointStripOddRawPolarization_sixMode_eq_integral
    (c d e f g h : ℝ) (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) :
    fourCellOddEndpointStripOddRawPolarization
        (fourCellOddP13SixModeProfile c d e f g h) r =
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddP13SixModeRawUpperRepresenter c d e f g h x * r x := by
  let low : ℝ → ℝ := fourCellOddP13SixModeProfile c d e f g h
  let strip : ℝ → ℝ := fourCellOddEndpointStripOdd low
  let tailStrip : ℝ → ℝ := fourCellOddEndpointStripOdd r
  let p : ℝ[X] :=
    fourCellOddP13SixModeEndpointStripOddUnitPolynomial c d e f g h
  let K : ℝ[X] := shiftedLogKernel p
  have hlow : ContDiff ℝ 1 low := by
    dsimp only [low]
    exact contDiff_fourCellOddP13SixModeProfile c d e f g h
  have htailStrip : Continuous tailStrip := by
    dsimp only [tailStrip]
    unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    fun_prop
  have hmode : ∀ t : ℝ, centeredPullback strip t = p.eval t := by
    intro t
    dsimp only [strip, low, p]
    exact centeredPullback_sixModeEndpointStripOdd_eq_eval c d e f g h t
  have hKcont : Continuous (fun x : ℝ ↦ K.eval x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (K.hasDerivAt x).continuousAt
  have hraw := fourCellOddEndpointStripOddRawPolarization_eq_bilinear
    low r hlow hr
  have hpoly := centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p strip tailStrip htailStrip hmode
  have hplus :
      (∫ t : ℝ in 0..1,
        r (3 / 5 + (2 / 5) * t) * K.eval t) =
      (5 / 2 : ℝ) * ∫ x : ℝ in 3 / 5..1,
        r x * K.eval ((5 * x - 3) / 2) := by
    let F : ℝ → ℝ := fun x ↦ r x * K.eval ((5 * x - 3) / 2)
    calc
      (∫ t : ℝ in 0..1,
          r (3 / 5 + (2 / 5) * t) * K.eval t) =
        ∫ t : ℝ in 0..1, F (3 / 5 + (2 / 5) * t) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          dsimp only [F]
          congr 2
          ring
      _ = (2 / 5 : ℝ)⁻¹ • ∫ x : ℝ in
          3 / 5 + (2 / 5) * 0..3 / 5 + (2 / 5) * 1, F x :=
        intervalIntegral.integral_comp_add_mul
          (f := F) (a := (0 : ℝ)) (b := 1)
            (by norm_num : (2 / 5 : ℝ) ≠ 0) (3 / 5)
      _ = (5 / 2 : ℝ) * ∫ x : ℝ in 3 / 5..1,
          r x * K.eval ((5 * x - 3) / 2) := by
        norm_num [F, smul_eq_mul]
  have hminus :
      (∫ t : ℝ in 0..1,
        r (1 - (2 / 5) * t) * K.eval t) =
      (5 / 2 : ℝ) * ∫ x : ℝ in 3 / 5..1,
        r x * K.eval ((5 - 5 * x) / 2) := by
    let F : ℝ → ℝ := fun x ↦ r x * K.eval ((5 - 5 * x) / 2)
    calc
      (∫ t : ℝ in 0..1,
          r (1 - (2 / 5) * t) * K.eval t) =
        ∫ t : ℝ in 0..1, F (1 - (2 / 5) * t) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          dsimp only [F]
          congr 2
          ring
      _ = (2 / 5 : ℝ)⁻¹ • ∫ x : ℝ in
          1 - (2 / 5) * 1..1 - (2 / 5) * 0, F x :=
        intervalIntegral.integral_comp_sub_mul
          (f := F) (a := (0 : ℝ)) (b := 1)
            (by norm_num : (2 / 5 : ℝ) ≠ 0) 1
      _ = (5 / 2 : ℝ) * ∫ x : ℝ in 3 / 5..1,
          r x * K.eval ((5 - 5 * x) / 2) := by
        norm_num [F, smul_eq_mul]
  have hA : IntervalIntegrable
      (fun t : ℝ ↦ r (3 / 5 + (2 / 5) * t) * K.eval t)
      volume 0 1 := by
    exact ((hr.continuous.comp (by fun_prop)).mul hKcont).intervalIntegrable _ _
  have hB : IntervalIntegrable
      (fun t : ℝ ↦ r (1 - (2 / 5) * t) * K.eval t)
      volume 0 1 := by
    exact ((hr.continuous.comp (by fun_prop)).mul hKcont).intervalIntegrable _ _
  have hunit :
      (∫ t : unitInterval,
        centeredPullback tailStrip (t : ℝ) * K.eval (t : ℝ)) =
      (5 / 4 : ℝ) * ∫ x : ℝ in 3 / 5..1,
        (K.eval ((5 * x - 3) / 2) - K.eval ((5 - 5 * x) / 2)) * r x := by
    have hunitToInterval :
        (∫ t : unitInterval,
          centeredPullback tailStrip (t : ℝ) * K.eval (t : ℝ)) =
        ∫ t : ℝ in 0..1, centeredPullback tailStrip t * K.eval t := by
      change (∫ t : unitInterval,
        (fun s : ℝ ↦ centeredPullback tailStrip s * K.eval s) (t : ℝ)) = _
      simpa only using integral_unitInterval_eq_intervalIntegral
        (fun s : ℝ ↦ centeredPullback tailStrip s * K.eval s)
    rw [hunitToInterval]
    dsimp only [tailStrip]
    unfold centeredPullback fourCellOddEndpointStripOdd
      fourCellOddEndpointStripPullback
    rw [show (fun t : ℝ ↦
        ((r (4 / 5 + (2 * t - 1) / 5) -
          r (4 / 5 + -(2 * t - 1) / 5)) / 2) * K.eval t) =
      fun t ↦
        ((r (3 / 5 + (2 / 5) * t) - r (1 - (2 / 5) * t)) / 2) *
          K.eval t by
      funext t
      rw [show (4 / 5 : ℝ) + (2 * t - 1) / 5 =
          3 / 5 + (2 / 5) * t by ring,
        show (4 / 5 : ℝ) + -(2 * t - 1) / 5 =
          1 - (2 / 5) * t by ring]]
    rw [show (fun t : ℝ ↦
        ((r (3 / 5 + (2 / 5) * t) - r (1 - (2 / 5) * t)) / 2) *
          K.eval t) = fun t ↦
        (1 / 2 : ℝ) *
          (r (3 / 5 + (2 / 5) * t) * K.eval t -
            r (1 - (2 / 5) * t) * K.eval t) by
      funext t
      ring,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hA hB,
      hplus, hminus]
    rw [show (fun x : ℝ ↦
        (K.eval ((5 * x - 3) / 2) - K.eval ((5 - 5 * x) / 2)) * r x) =
      fun x ↦ r x * K.eval ((5 * x - 3) / 2) -
        r x * K.eval ((5 - 5 * x) / 2) by
      funext x
      ring,
      intervalIntegral.integral_sub]
    · ring
    · exact (hr.continuous.mul
        (hKcont.comp (by fun_prop))).intervalIntegrable _ _
    · exact (hr.continuous.mul
        (hKcont.comp (by fun_prop))).intervalIntegrable _ _
  rw [hpoly, hunit] at hraw
  dsimp only [low, strip, tailStrip, p, K] at hraw
  unfold fourCellOddP13SixModeRawUpperRepresenter
  convert hraw using 1
  ring

theorem continuous_fourCellOddP13SixModeRawUpperRepresenter
    (c d e f g h : ℝ) :
    Continuous (fourCellOddP13SixModeRawUpperRepresenter c d e f g h) := by
  let K : ℝ[X] := shiftedLogKernel
    (fourCellOddP13SixModeEndpointStripOddUnitPolynomial c d e f g h)
  have hK : Continuous (fun x : ℝ ↦ K.eval x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (K.hasDerivAt x).continuousAt
  unfold fourCellOddP13SixModeRawUpperRepresenter
  exact (hK.comp (by fun_prop)).sub (hK.comp (by fun_prop))

private theorem integral_centeredPullback_mul_shiftedLegendre_eq_neg_half
    (n : ℕ) (q r : ℝ → ℝ)
    (hmode : ∀ t : ℝ, centeredPullback q t =
      -(shiftedLegendreReal n).eval t) :
    (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * ∫ x : ℝ in -1..1, r x * q x := by
  calc
    (∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
        ∫ t : ℝ in 0..1,
          centeredPullback r t * (shiftedLegendreReal n).eval t := by
      change (∫ t : unitInterval,
        (fun s : ℝ ↦ centeredPullback r s *
          (shiftedLegendreReal n).eval s) (t : ℝ)) = _
      simpa only using integral_unitInterval_eq_intervalIntegral
        (fun s : ℝ ↦ centeredPullback r s *
          (shiftedLegendreReal n).eval s)
    _ = ∫ t : ℝ in 0..1,
        -((fun x : ℝ ↦ r x * q x) (2 * t - 1)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      have hpull := hmode t
      unfold centeredPullback at hpull ⊢
      have hp : (shiftedLegendreReal n).eval t =
          -q (2 * t - 1) := by
        linarith
      change r (2 * t - 1) * (shiftedLegendreReal n).eval t =
        -(r (2 * t - 1) * q (2 * t - 1))
      rw [hp]
      ring
    _ = -(∫ t : ℝ in 0..1,
        (fun x : ℝ ↦ r x * q x) (2 * t - 1)) := by
      rw [intervalIntegral.integral_neg]
    _ = -((1 / 2 : ℝ) * ∫ x : ℝ in -1..1,
        r x * q x) := by
      rw [integral_comp_two_mul_sub_one (fun x : ℝ ↦ r x * q x)]
    _ = _ := by ring

private theorem centeredPullback_fourCellOddP11DirectTail
    (t : ℝ) :
    centeredPullback fourCellOddP11DirectTail t =
      -(shiftedLegendreReal 11).eval t := by
  unfold centeredPullback fourCellOddP11DirectTail
  rw [eval_centeredShiftedLegendreReal]
  congr 3
  ring

/-- The global raw-log row of `P11` vanishes on the genuine `P13+`
subspace.  This is the Legendre eigenvalue mechanism, not a coefficient
enumeration. -/
theorem centeredRawLogBilinear_P11_P13Plus_eq_zero
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    centeredRawLogBilinear fourCellOddP11DirectTail r = 0 := by
  let p : ℝ[X] := -(shiftedLegendreReal 11)
  have hmode : ∀ t : ℝ, centeredPullback fourCellOddP11DirectTail t =
      p.eval t := by
    intro t
    dsimp only [p]
    rw [Polynomial.eval_neg]
    exact centeredPullback_fourCellOddP11DirectTail t
  have hfullFold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ fourCellOddP11DirectTail x * r x)
    ((contDiff_fourCellOddP11DirectTail.continuous.mul hr.continuous)
      |>.intervalIntegrable _ _)
    (by
      intro x
      change fourCellOddP11DirectTail (-x) * r (-x) =
        fourCellOddP11DirectTail x * r x
      rw [odd_fourCellOddP11DirectTail, hodd]
      ring)
  have hfull : (∫ x : ℝ in -1..1,
      r x * fourCellOddP11DirectTail x) = 0 := by
    rw [show (fun x : ℝ ↦ r x * fourCellOddP11DirectTail x) =
        fun x ↦ fourCellOddP11DirectTail x * r x by
      funext x
      ring,
      hfullFold, h11]
    ring
  have hunit := integral_centeredPullback_mul_shiftedLegendre_eq_neg_half
    11 fourCellOddP11DirectTail r centeredPullback_fourCellOddP11DirectTail
  have hpLog : shiftedLogKernel p =
      -(Polynomial.C (2 * (harmonic 11 : ℝ)) * shiftedLegendreReal 11) := by
    dsimp only [p]
    rw [map_neg, shiftedLogKernel_shiftedLegendreReal]
  have hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [hpLog]
    simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (fun t : unitInterval ↦ centeredPullback r (t : ℝ) *
        -(2 * (harmonic 11 : ℝ) *
          (shiftedLegendreReal 11).eval (t : ℝ))) =
      fun t : unitInterval ↦ -(2 * (harmonic 11 : ℝ)) *
        (centeredPullback r (t : ℝ) *
          (shiftedLegendreReal 11).eval (t : ℝ)) by
      funext t
      ring,
      integral_const_mul, hunit, hfull]
    ring
  rw [centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p fourCellOddP11DirectTail r hr.continuous hmode, hpair]
  ring

private def fourCellOddFiveModeCenteredPullbackPolynomial
    (c d e f g : ℝ) : ℝ[X] :=
  (fourCellOddFiveModePolynomial c d e f g).comp
    ((2 : ℝ) • X - C 1)

private theorem centeredPullback_fiveMode_eq_eval
    (c d e f g t : ℝ) :
    centeredPullback
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) t =
      (fourCellOddFiveModeCenteredPullbackPolynomial c d e f g).eval t := by
  unfold fourCellOddFiveModeCenteredPullbackPolynomial centeredPullback
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X,
    Polynomial.eval_C, smul_eq_mul]
  rw [fourCellOddFiveModePolynomial_eval]

private def fourCellOddP13SixModeCenteredPullbackPolynomial
    (c d e f g h : ℝ) : ℝ[X] :=
  fourCellOddFiveModeCenteredPullbackPolynomial c d e f g +
    h • (-(shiftedLegendreReal 11))

private theorem centeredPullback_sixMode_eq_eval
    (c d e f g h t : ℝ) :
    centeredPullback (fourCellOddP13SixModeProfile c d e f g h) t =
      (fourCellOddP13SixModeCenteredPullbackPolynomial c d e f g h).eval t := by
  unfold fourCellOddP13SixModeProfile
    fourCellOddP13SixModeCenteredPullbackPolynomial centeredPullback
  simp only [Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_neg,
    smul_eq_mul]
  rw [← centeredPullback_fiveMode_eq_eval c d e f g t]
  have h11 := centeredPullback_fourCellOddP11DirectTail t
  unfold centeredPullback at h11
  rw [h11]
  unfold centeredPullback
  ring

/-- All global singular modes through `P11` disappear on `P13+`. -/
theorem centeredRawLogBilinear_sixMode_P13Plus_eq_zero
    (c d e f g h : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    centeredRawLogBilinear
      (fourCellOddP13SixModeProfile c d e f g h) r = 0 := by
  let p5 : ℝ[X] := fourCellOddFiveModeCenteredPullbackPolynomial c d e f g
  let p11 : ℝ[X] := -(shiftedLegendreReal 11)
  let p : ℝ[X] := fourCellOddP13SixModeCenteredPullbackPolynomial c d e f g h
  have hlow := centeredRawLogBilinear_oneThreeFiveSevenNine_tail_eq_zero
    r hr h1 h3 h5 h7 h9 c d e f g
  have hp11 := centeredRawLogBilinear_P11_P13Plus_eq_zero r hr hodd h11
  have hmode5 : ∀ t : ℝ,
      centeredPullback
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) t =
        p5.eval t := by
    intro t
    dsimp only [p5]
    exact centeredPullback_fiveMode_eq_eval c d e f g t
  have hmode11 : ∀ t : ℝ,
      centeredPullback fourCellOddP11DirectTail t = p11.eval t := by
    intro t
    dsimp only [p11]
    rw [Polynomial.eval_neg]
    exact centeredPullback_fourCellOddP11DirectTail t
  have hmode : ∀ t : ℝ,
      centeredPullback (fourCellOddP13SixModeProfile c d e f g h) t =
        p.eval t := by
    intro t
    dsimp only [p]
    exact centeredPullback_sixMode_eq_eval c d e f g h t
  have hpair5 : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p5).eval (t : ℝ)) = 0 := by
    have hrep := centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
      p5 (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)
        r hr.continuous hmode5
    rw [hlow] at hrep
    linarith
  have hpair11 : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p11).eval (t : ℝ)) = 0 := by
    have hrep := centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
      p11 fourCellOddP11DirectTail r hr.continuous hmode11
    rw [hp11] at hrep
    linarith
  have hkernel : shiftedLogKernel p =
      shiftedLogKernel p5 + h • shiftedLogKernel p11 := by
    dsimp only [p, p5, p11,
      fourCellOddP13SixModeCenteredPullbackPolynomial]
    rw [map_add, map_smul]
  have hI5 : Integrable (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p5).eval (t : ℝ)) := by
    exact (show Continuous (fun t : unitInterval ↦
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p5).eval (t : ℝ)) by
      dsimp only [centeredPullback]
      fun_prop).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hI11 : Integrable (fun t : unitInterval ↦
      h * (centeredPullback r (t : ℝ) *
        (shiftedLogKernel p11).eval (t : ℝ))) := by
    exact (show Continuous (fun t : unitInterval ↦
      h * (centeredPullback r (t : ℝ) *
        (shiftedLogKernel p11).eval (t : ℝ))) by
      dsimp only [centeredPullback]
      fun_prop).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hpair : (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLogKernel p).eval (t : ℝ)) = 0 := by
    rw [hkernel]
    simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
    rw [show (fun t : unitInterval ↦ centeredPullback r (t : ℝ) *
        ((shiftedLogKernel p5).eval (t : ℝ) +
          h * (shiftedLogKernel p11).eval (t : ℝ))) =
      fun t : unitInterval ↦ centeredPullback r (t : ℝ) *
          (shiftedLogKernel p5).eval (t : ℝ) +
        h * (centeredPullback r (t : ℝ) *
          (shiftedLogKernel p11).eval (t : ℝ)) by
      funext t
      ring,
      integral_add hI5 hI11, hpair5]
    rw [integral_const_mul, hpair11]
    ring
  rw [centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p (fourCellOddP13SixModeProfile c d e f g h) r hr.continuous hmode,
    hpair]
  ring

/-! ## The smooth row and cutoff-13 cancellations -/

/-- Smooth lag representer generated by the complete six-mode cutoff. -/
def fourCellOddP13SixModeRegularRepresenter
    (c d e f g h : ℝ) : ℝ → ℝ :=
  factorTwoContinuousLagK
    (fun t ↦ yoshidaRegularKernel (fourCellOperatorHalfWidth * t))
    (fourCellOddP13SixModeProfile c d e f g h)

private theorem regularRightRepresenter_neg_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) (x : ℝ) :
    factorTwoContinuousLagRightRepresenter q p (-x) =
      -factorTwoContinuousLagLeftRepresenter q p x := by
  unfold factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  have h := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ ↦ q (y + x) * p y)
    (a := (-1 : ℝ)) (b := x)
  have heq : (fun y : ℝ ↦ q (-y + x) * p (-y)) =
      fun y ↦ -(q (x - y) * p y) := by
    funext y
    rw [hp y]
    ring
  rw [heq, intervalIntegral.integral_neg] at h
  calc
    (∫ y : ℝ in -x..1, q (y - -x) * p y) =
        ∫ y : ℝ in -x..1, q (y + x) * p y := by
      apply intervalIntegral.integral_congr
      intro y _hy
      ring
    _ = _ := by simpa only [neg_neg] using h.symm

private theorem regularLeftRepresenter_neg_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) (x : ℝ) :
    factorTwoContinuousLagLeftRepresenter q p (-x) =
      -factorTwoContinuousLagRightRepresenter q p x := by
  unfold factorTwoContinuousLagLeftRepresenter
    factorTwoContinuousLagRightRepresenter
  have h := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ ↦ q (y - x) * p y)
    (a := (-1 : ℝ)) (b := -x)
  have heq : (fun y : ℝ ↦ q (-y - x) * p (-y)) =
      fun y ↦ -(q (-x - y) * p y) := by
    funext y
    rw [hp y]
    ring
  rw [heq, intervalIntegral.integral_neg] at h
  have h' := congrArg Neg.neg h
  simpa only [neg_neg] using h'

private theorem odd_factorTwoContinuousLagK_of_odd
    (q p : ℝ → ℝ) (hp : Function.Odd p) :
    Function.Odd (factorTwoContinuousLagK q p) := by
  intro x
  unfold factorTwoContinuousLagK
  rw [regularRightRepresenter_neg_of_odd q p hp,
    regularLeftRepresenter_neg_of_odd q p hp]
  ring

theorem odd_fourCellOddP13SixModeRegularRepresenter
    (c d e f g h : ℝ) :
    Function.Odd
      (fourCellOddP13SixModeRegularRepresenter c d e f g h) := by
  unfold fourCellOddP13SixModeRegularRepresenter
  exact odd_factorTwoContinuousLagK_of_odd _ _
    (odd_fourCellOddP13SixModeProfile c d e f g h)

private theorem regularLag_abs_le_quarter
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    |yoshidaRegularKernel (fourCellOperatorHalfWidth * t)| ≤ 1 / 4 := by
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
    mul_nonneg ha0 ht.1
  have harg4 : fourCellOperatorHalfWidth * t ≤
      5 * Real.log 2 / 4 := by
    calc
      fourCellOperatorHalfWidth * t ≤ fourCellOperatorHalfWidth * 2 :=
        mul_le_mul_of_nonneg_left ht.2 ha0
      _ = 5 * Real.log 2 / 4 := by
        unfold fourCellOperatorHalfWidth
        ring
  have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
  rw [abs_of_nonneg hk0]
  exact yoshidaRegularKernel_le_quarter harg0

theorem intervalIntegrable_mul_fourCellOddP13SixModeRegularRepresenter
    (u : ℝ → ℝ) (hu : Continuous u) (c d e f g h : ℝ) :
    IntervalIntegrable
      (fun x : ℝ ↦ u x *
        fourCellOddP13SixModeRegularRepresenter c d e f g h x)
      volume (-1) 1 := by
  let q : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let p : ℝ → ℝ := fourCellOddP13SixModeProfile c d e f g h
  have hq : Measurable q := by
    dsimp only [q]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddP13SixModeProfile c d e f g h).continuous
  have hqbound : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ 1 / 4 := by
    intro t ht
    simpa only [q] using regularLag_abs_le_quarter t ht
  have hright :=
    intervalIntegrable_mul_factorTwoContinuousLagRightRepresenter_of_bounded
      q p u hq hp hu (1 / 4) hqbound
  have hleft :=
    intervalIntegrable_mul_factorTwoContinuousLagLeftRepresenter_of_bounded
      q u p hq hu hp (1 / 4) hqbound
  change IntervalIntegrable
    (fun x : ℝ ↦ u x * factorTwoContinuousLagK q p x)
      volume (-1) 1
  unfold factorTwoContinuousLagK
  rw [show (fun x : ℝ ↦ u x *
      (factorTwoContinuousLagRightRepresenter q p x +
        factorTwoContinuousLagLeftRepresenter q p x)) =
      fun x ↦
        u x * factorTwoContinuousLagRightRepresenter q p x +
          u x * factorTwoContinuousLagLeftRepresenter q p x by
    funext x
    ring]
  exact hright.add hleft

theorem integral_mul_fourCellOddP13SixModeRegularRepresenter_eq_two_mul
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (c d e f g h : ℝ) :
    (∫ x : ℝ in -1..1,
        r x * fourCellOddP13SixModeRegularRepresenter c d e f g h x) =
      2 * ∫ x : ℝ in 0..1,
        r x * fourCellOddP13SixModeRegularRepresenter c d e f g h x := by
  have heven : Function.Even (fun x : ℝ ↦
      r x * fourCellOddP13SixModeRegularRepresenter c d e f g h x) := by
    intro x
    change r (-x) *
        fourCellOddP13SixModeRegularRepresenter c d e f g h (-x) =
      r x * fourCellOddP13SixModeRegularRepresenter c d e f g h x
    rw [hodd x, odd_fourCellOddP13SixModeRegularRepresenter c d e f g h x]
    ring
  exact integral_neg_one_one_eq_two_mul_zero_one_of_even _
    (intervalIntegrable_mul_fourCellOddP13SixModeRegularRepresenter
      r hr c d e f g h) heven

theorem two_mul_width_mul_regularCorrelation_sixMode_eq_representer
    (r : ℝ → ℝ) (hr : Continuous r) (c d e f g h : ℝ) :
    2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              (fourCellOddP13SixModeProfile c d e f g h) r t) =
      fourCellOperatorHalfWidth *
        (∫ x : ℝ in -1..1,
          r x * fourCellOddP13SixModeRegularRepresenter c d e f g h x) := by
  let k : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let p : ℝ → ℝ := fourCellOddP13SixModeProfile c d e f g h
  have hk : Measurable k := by
    dsimp only [k]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddP13SixModeProfile c d e f g h).continuous
  have hkbound : ∀ t ∈ Icc (0 : ℝ) 2, |k t| ≤ 1 / 4 := by
    intro t ht
    simpa only [k] using regularLag_abs_le_quarter t ht
  have hregular := integral_boundedLag_mul_correlationBilinear_eq_K
    k p r hk hp hr (1 / 4) hkbound
  change 2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        k t * factorTwoCenteredCorrelationBilinear p r t) =
    fourCellOperatorHalfWidth *
      (∫ x : ℝ in -1..1,
        r x * fourCellOddP13SixModeRegularRepresenter c d e f g h x)
  rw [hregular]
  dsimp only [fourCellOddP13SixModeRegularRepresenter, k, p]
  ring

/-- Exact positive-half mass annihilation by the six retained odd modes. -/
theorem integral_zero_one_sixMode_mul_P13Plus_eq_zero
    (c d e f g h : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SixModeProfile c d e f g h x * r x) = 0 := by
  have hlow := integral_zero_one_fiveMode_mul_P11Plus_eq_zero
    r hr.continuous hodd h1 h3 h5 h7 h9 c d e f g
  have hlowI : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x * r x)
      volume 0 1 :=
    ((contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g).continuous.mul
      hr.continuous).intervalIntegrable _ _
  have hpI : IntervalIntegrable (fun x : ℝ ↦
      h * (fourCellOddP11DirectTail x * r x)) volume 0 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP11DirectTail.continuous.mul hr.continuous))
      |>.intervalIntegrable _ _
  unfold fourCellOddP13SixModeProfile
  rw [show (fun x : ℝ ↦
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x +
        h * fourCellOddP11DirectTail x) * r x) =
      fun x ↦
        fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x * r x +
          h * (fourCellOddP11DirectTail x * r x) by
    funext x
    ring,
    intervalIntegral.integral_add hlowI hpI,
    intervalIntegral.integral_const_mul,
    hlow, h11]
  ring

/-- The complete raw reserve leaves only the adverse endpoint-strip row on
the genuine `P13+` space. -/
theorem fourCellOddRawStripCancellationPolarization_sixMode_P13Plus_eq
    (c d e f g h : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    fourCellOddRawStripCancellationPolarization
        (fourCellOddP13SixModeProfile c d e f g h) r =
      -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawPolarization
        (fourCellOddP13SixModeProfile c d e f g h) r := by
  rw [fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      _ r (contDiff_fourCellOddP13SixModeProfile c d e f g h) hr
        (odd_fourCellOddP13SixModeProfile c d e f g h) hodd,
    centeredRawLogBilinear_sixMode_P13Plus_eq_zero
      c d e f g h r hr hodd h1 h3 h5 h7 h9 h11]
  ring

/-- The signed scalar mass vanishes exactly at cutoff 13. -/
theorem fourCellOddSignedMassRegularBilinear_sixMode_P13Plus_eq_regular
    (c d e f g h : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    fourCellOddSignedMassRegularBilinear
        (fourCellOddP13SixModeProfile c d e f g h) r =
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              (fourCellOddP13SixModeProfile c d e f g h) r t) := by
  unfold fourCellOddSignedMassRegularBilinear
  rw [integral_zero_one_sixMode_mul_P13Plus_eq_zero
    c d e f g h r hr hodd h1 h3 h5 h7 h9 h11]
  ring

/-- Fully reduced cutoff-13 core row in a single global regular Riesz
coordinate. -/
theorem fourCellOddCoreLocalBilinear_sixMode_P13Plus_eq_regularRepresenter
    (c d e f g h : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP13SixModeProfile c d e f g h) r =
      -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawPolarization
          (fourCellOddP13SixModeProfile c d e f g h) r +
        fourCellOddRetainedPrimePotentialBilinear
          (fourCellOddP13SixModeProfile c d e f g h) r -
        fourCellOperatorHalfWidth *
          (∫ x : ℝ in -1..1,
            r x * fourCellOddP13SixModeRegularRepresenter c d e f g h x) := by
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointBilinear
  rw [fourCellOddRawStripCancellationPolarization_sixMode_P13Plus_eq
      c d e f g h r hr hodd h1 h3 h5 h7 h9 h11,
    fourCellOddSignedMassRegularBilinear_sixMode_P13Plus_eq_regular
      c d e f g h r hr hodd h1 h3 h5 h7 h9 h11,
    two_mul_width_mul_regularCorrelation_sixMode_eq_representer
      r hr.continuous c d e f g h]

/-- Exact density below the physical endpoint strip. -/
def fourCellOddP13SixModeLowerRepresenter
    (c d e f g h : ℝ) (x : ℝ) : ℝ :=
  (93 / 50 : ℝ) * yoshidaEndpointPotential x *
      fourCellOddP13SixModeProfile c d e f g h x -
    2 * fourCellOperatorHalfWidth *
      fourCellOddP13SixModeRegularRepresenter c d e f g h x

/-- Exact density on the physical endpoint strip. -/
def fourCellOddP13SixModeUpperRepresenter
    (c d e f g h : ℝ) (x : ℝ) : ℝ :=
  fourCellOddP13SixModeLowerRepresenter c d e f g h x +
    Real.sqrt 2 * Real.log 2 *
      ((fourCellOddP13SixModeProfile c d e f g h x +
        fourCellOddP13SixModeProfile c d e f g h (8 / 5 - x)) / 2) +
    (2 - Real.sqrt 2 * Real.log 2) *
      ((fourCellOddP13SixModeProfile c d e f g h x -
        fourCellOddP13SixModeProfile c d e f g h (8 / 5 - x)) / 2) -
    (1 / 2 : ℝ) *
      fourCellOddP13SixModeRawUpperRepresenter c d e f g h x

/-- Exact positive-half two-strip row at cutoff 13. -/
theorem fourCellOddCoreLocalBilinear_sixMode_P13Plus_eq_twoStripRepresenter
    (c d e f g h : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (h11 : (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * r x) = 0) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP13SixModeProfile c d e f g h) r =
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP13SixModeLowerRepresenter c d e f g h x * r x) +
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddP13SixModeUpperRepresenter c d e f g h x * r x := by
  let low : ℝ → ℝ := fourCellOddP13SixModeProfile c d e f g h
  let P : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * low x * r x
  let R : ℝ → ℝ := fun x ↦
    r x * fourCellOddP13SixModeRegularRepresenter c d e f g h x
  let E : ℝ → ℝ := fun x ↦ ((low x + low (8 / 5 - x)) / 2) * r x
  let O : ℝ → ℝ := fun x ↦ ((low x - low (8 / 5 - x)) / 2) * r x
  let S : ℝ → ℝ := fun x ↦
    fourCellOddP13SixModeRawUpperRepresenter c d e f g h x * r x
  have hlow : Continuous low := by
    dsimp only [low]
    exact (contDiff_fourCellOddP13SixModeProfile c d e f g h).continuous
  have hPfull : IntervalIntegrable P volume (-1) 1 := by
    dsimp only [P, low]
    exact intervalIntegrable_endpointPotential_mul
      (fourCellOddP13SixModeProfile c d e f g h) r hlow hr.continuous
  have hP : IntervalIntegrable P volume 0 1 := by
    apply hPfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hPL : IntervalIntegrable P volume 0 (3 / 5) := by
    apply hP.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hPU : IntervalIntegrable P volume (3 / 5) 1 := by
    apply hP.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hRfull : IntervalIntegrable R volume (-1) 1 := by
    dsimp only [R]
    exact intervalIntegrable_mul_fourCellOddP13SixModeRegularRepresenter
      r hr.continuous c d e f g h
  have hR : IntervalIntegrable R volume 0 1 := by
    apply hRfull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hRL : IntervalIntegrable R volume 0 (3 / 5) := by
    apply hR.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hRU : IntervalIntegrable R volume (3 / 5) 1 := by
    apply hR.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hE : IntervalIntegrable E volume (3 / 5) 1 := by
    dsimp only [E]
    exact (((hlow.add (hlow.comp (by fun_prop))).div_const 2).mul
      hr.continuous).intervalIntegrable _ _
  have hO : IntervalIntegrable O volume (3 / 5) 1 := by
    dsimp only [O]
    exact (((hlow.sub (hlow.comp (by fun_prop))).div_const 2).mul
      hr.continuous).intervalIntegrable _ _
  have hS : IntervalIntegrable S volume (3 / 5) 1 := by
    dsimp only [S]
    exact ((continuous_fourCellOddP13SixModeRawUpperRepresenter
      c d e f g h).mul hr.continuous).intervalIntegrable _ _
  have hPSplit := intervalIntegral.integral_add_adjacent_intervals hPL hPU
  have hRSplit := intervalIntegral.integral_add_adjacent_intervals hRL hRU
  have hraw := fourCellOddEndpointStripOddRawPolarization_sixMode_eq_integral
    c d e f g h r hr
  have heven := fourCellOddEndpointStripEvenMassBilinear_eq_integral
    low r hlow hr.continuous
  have hstripOdd := fourCellOddEndpointStripOddMassBilinear_eq_integral
    low r hlow hr.continuous
  have hRFold :=
    integral_mul_fourCellOddP13SixModeRegularRepresenter_eq_two_mul
      r hr.continuous hodd c d e f g h
  have hrow :=
    fourCellOddCoreLocalBilinear_sixMode_P13Plus_eq_regularRepresenter
      c d e f g h r hr hodd h1 h3 h5 h7 h9 h11
  unfold fourCellOddRetainedPrimePotentialBilinear at hrow
  change fourCellOddEndpointStripEvenMassBilinear low r =
      ∫ x : ℝ in 3 / 5..1, E x at heven
  change fourCellOddEndpointStripOddMassBilinear low r =
      ∫ x : ℝ in 3 / 5..1, O x at hstripOdd
  change fourCellOddEndpointStripOddRawPolarization low r =
      ∫ x : ℝ in 3 / 5..1, S x at hraw
  change (∫ x : ℝ in -1..1, R x) =
      2 * ∫ x : ℝ in 0..1, R x at hRFold
  change fourCellOddCoreLocalBilinear low r =
      -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawPolarization low r +
        (Real.sqrt 2 * Real.log 2 *
            fourCellOddEndpointStripEvenMassBilinear low r +
          (2 - Real.sqrt 2 * Real.log 2) *
            fourCellOddEndpointStripOddMassBilinear low r +
          (93 / 50 : ℝ) * ∫ x : ℝ in 0..1, P x) -
        fourCellOperatorHalfWidth * ∫ x : ℝ in -1..1, R x at hrow
  rw [hraw, heven, hstripOdd, hRFold, ← hPSplit, ← hRSplit] at hrow
  rw [show (fun x : ℝ ↦
      fourCellOddP13SixModeLowerRepresenter c d e f g h x * r x) =
      fun x ↦ (93 / 50 : ℝ) * P x -
        2 * fourCellOperatorHalfWidth * R x by
    funext x
    dsimp only [P, R, low]
    unfold fourCellOddP13SixModeLowerRepresenter
    ring,
    show (fun x : ℝ ↦
      fourCellOddP13SixModeUpperRepresenter c d e f g h x * r x) =
      fun x ↦
        ((93 / 50 : ℝ) * P x - 2 * fourCellOperatorHalfWidth * R x) +
          Real.sqrt 2 * Real.log 2 * E x +
          (2 - Real.sqrt 2 * Real.log 2) * O x - (1 / 2 : ℝ) * S x by
    funext x
    dsimp only [P, R, E, O, S, low]
    unfold fourCellOddP13SixModeUpperRepresenter
      fourCellOddP13SixModeLowerRepresenter
    ring,
    intervalIntegral.integral_sub (hPL.const_mul _) (hRL.const_mul _),
    intervalIntegral.integral_sub
      ((((hPU.const_mul _).sub (hRU.const_mul _)).add (hE.const_mul _)).add
        (hO.const_mul _)) (hS.const_mul _),
    intervalIntegral.integral_add
      (((hPU.const_mul _).sub (hRU.const_mul _)).add (hE.const_mul _))
        (hO.const_mul _),
    intervalIntegral.integral_add
      ((hPU.const_mul _).sub (hRU.const_mul _)) (hE.const_mul _),
    intervalIntegral.integral_sub (hPU.const_mul _) (hRU.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  dsimp only [low] at hrow
  rw [hrow]
  rw [intervalIntegral.integral_const_mul]
  ring

/-! ## Six-mode selector quotient and ordinary `L²` Cauchy -/

/-- An arbitrary retained selector through `P11`. -/
def fourCellOddP13SixModeSelector
    (b1 b3 b5 b7 b9 b11 : ℝ) : ℝ → ℝ :=
  fourCellOddP13SixModeProfile b1 b3 b5 b7 b9 b11

/-- Lower-strip augmented residual row modulo a retained six-mode selector. -/
def fourCellOddP13AugmentedResidualLowerSelectorResidual
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) (x : ℝ) : ℝ :=
  fourCellOddP13SixModeLowerRepresenter
      1 (-a3) (-a5) (-a7) (-a9) (-a11) x -
    fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x

/-- Upper-strip augmented residual row modulo the same selector. -/
def fourCellOddP13AugmentedResidualUpperSelectorResidual
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) (x : ℝ) : ℝ :=
  fourCellOddP13SixModeUpperRepresenter
      1 (-a3) (-a5) (-a7) (-a9) (-a11) x -
    fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x

/-- A finite, explicit cutoff-13 selector norm certificate.  The two `MemLp`
fields merely record that the displayed finite row densities are legitimate
`L²` representatives; the quantitative content is the final scalar norm
inequality. -/
def FourCellOddP13AugmentedResidualSelectorTwoStripNormBound
    (kappa a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) : Prop :=
  MemLp
      (fourCellOddP13AugmentedResidualLowerSelectorResidual
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11) 2
      (volume.restrict (Ioc (0 : ℝ) (3 / 5))) ∧
    MemLp
      (fourCellOddP13AugmentedResidualUpperSelectorResidual
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11) 2
      (volume.restrict (Ioc (3 / 5 : ℝ) 1)) ∧
    (∫ x : ℝ in 0..3 / 5,
        fourCellOddP13AugmentedResidualLowerSelectorResidual
          a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 x ^ 2) +
      (∫ x : ℝ in 3 / 5..1,
        fourCellOddP13AugmentedResidualUpperSelectorResidual
          a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 x ^ 2) ≤
      fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa

/-- Quotient formulation: the selector may be supplied together with the
finite norm certificate after the Galerkin coefficients are fixed. -/
def FourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound
    (kappa a3 a5 a7 a9 a11 : ℝ) : Prop :=
  ∃ b1 b3 b5 b7 b9 b11 : ℝ,
    FourCellOddP13AugmentedResidualSelectorTwoStripNormBound
      kappa a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11

private theorem memLp_two_restrict_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    hf.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

private theorem sum_pair_sq_le_sum_norm_mul_sum_mass
    (A B NL NU ML MU : ℝ)
    (hNL : 0 ≤ NL) (hNU : 0 ≤ NU)
    (hML : 0 ≤ ML) (hMU : 0 ≤ MU)
    (hA : A ^ 2 ≤ NL * ML) (hB : B ^ 2 ≤ NU * MU) :
    (A + B) ^ 2 ≤ (NL + NU) * (ML + MU) := by
  have hcross : 2 * A * B ≤ NL * MU + NU * ML := by
    by_cases hab : A * B ≤ 0
    · have hright : 0 ≤ NL * MU + NU * ML :=
        add_nonneg (mul_nonneg hNL hMU) (mul_nonneg hNU hML)
      nlinarith
    · have habpos : 0 < A * B := lt_of_not_ge hab
      have hprod : (A * B) ^ 2 ≤ (NL * ML) * (NU * MU) := by
        rw [mul_pow]
        exact mul_le_mul hA hB (sq_nonneg B) (mul_nonneg hNL hML)
      have hscaled := mul_le_mul_of_nonneg_left hprod
        (by norm_num : (0 : ℝ) ≤ 4)
      have hamgm :
          4 * ((NL * ML) * (NU * MU)) ≤ (NL * MU + NU * ML) ^ 2 := by
        nlinarith only [sq_nonneg (NL * MU - NU * ML)]
      have hsquares : (2 * A * B) ^ 2 ≤
          (NL * MU + NU * ML) ^ 2 := by
        nlinarith only [hscaled, hamgm]
      have hleft : 0 ≤ 2 * A * B := by nlinarith
      have hright : 0 ≤ NL * MU + NU * ML :=
        add_nonneg (mul_nonneg hNL hMU) (mul_nonneg hNU hML)
      exact (sq_le_sq₀ hleft hright).1 hsquares
  nlinarith only [hA, hB, hcross]

/-- The explicit finite selector norm inequality discharges the sole
infinite-dimensional `P13+` residual dual in the augmented Galerkin--Riesz
certificate. -/
theorem fourCellOddP13AugmentedGalerkinResidualL2Dual_of_selectorTwoStripNormBound
    (kappa a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ)
    (hnorm : FourCellOddP13AugmentedResidualSelectorTwoStripNormBound
      kappa a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11) :
    FourCellOddP13AugmentedGalerkinResidualL2Dual
      kappa a3 a5 a7 a9 a11 := by
  rcases hnorm with ⟨hL, hU, hnorm⟩
  intro r hr hodd h1 h3 h5 h7 h9 h11
  let L : ℝ → ℝ :=
    fourCellOddP13AugmentedResidualLowerSelectorResidual
      a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  let U : ℝ → ℝ :=
    fourCellOddP13AugmentedResidualUpperSelectorResidual
      a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  let T : ℝ → ℝ :=
    fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  let μU : Measure ℝ := volume.restrict (Ioc (3 / 5 : ℝ) 1)
  have hT : Continuous T := by
    dsimp only [T, fourCellOddP13SixModeSelector]
    exact (contDiff_fourCellOddP13SixModeProfile b1 b3 b5 b7 b9 b11).continuous
  have hTzero : (∫ x : ℝ in 0..1, T x * r x) = 0 := by
    dsimp only [T, fourCellOddP13SixModeSelector]
    exact integral_zero_one_sixMode_mul_P13Plus_eq_zero
      b1 b3 b5 b7 b9 b11 r hr hodd h1 h3 h5 h7 h9 h11
  have hTL : IntervalIntegrable (fun x : ℝ ↦ T x * r x)
      volume 0 (3 / 5) := (hT.mul hr.continuous).intervalIntegrable _ _
  have hTU : IntervalIntegrable (fun x : ℝ ↦ T x * r x)
      volume (3 / 5) 1 := (hT.mul hr.continuous).intervalIntegrable _ _
  have hTsplit := intervalIntegral.integral_add_adjacent_intervals hTL hTU
  have hrFull : MemLp r 2 (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    memLp_two_restrict_of_continuous r hr.continuous
  have hrL : MemLp r 2 μL := by
    apply hrFull.mono_measure
    dsimp only [μL]
    apply Measure.restrict_mono
    · intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact le_rfl
  have hrU : MemLp r 2 μU := by
    apply hrFull.mono_measure
    dsimp only [μU]
    apply Measure.restrict_mono
    · intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩
    · exact le_rfl
  change MemLp L 2 μL at hL
  change MemLp U 2 μU at hU
  have hLprod := hL.integrable_mul hrL
  have hUprod := hU.integrable_mul hrU
  have hLprodI : IntervalIntegrable (fun x : ℝ ↦ L x * r x)
      volume 0 (3 / 5) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    simpa only [μL] using hLprod
  have hUprodI : IntervalIntegrable (fun x : ℝ ↦ U x * r x)
      volume (3 / 5) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    simpa only [μU] using hUprod
  have hrawPair :=
    fourCellOddCoreLocalBilinear_sixMode_P13Plus_eq_twoStripRepresenter
      1 (-a3) (-a5) (-a7) (-a9) (-a11)
        r hr hodd h1 h3 h5 h7 h9 h11
  have hrawL :
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP13SixModeLowerRepresenter
          1 (-a3) (-a5) (-a7) (-a9) (-a11) x * r x) =
      (∫ x : ℝ in 0..3 / 5, L x * r x) +
        ∫ x : ℝ in 0..3 / 5, T x * r x := by
    rw [← intervalIntegral.integral_add hLprodI hTL]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [L, T]
    unfold fourCellOddP13AugmentedResidualLowerSelectorResidual
      fourCellOddP13SixModeSelector
    ring
  have hrawU :
      (∫ x : ℝ in 3 / 5..1,
        fourCellOddP13SixModeUpperRepresenter
          1 (-a3) (-a5) (-a7) (-a9) (-a11) x * r x) =
      (∫ x : ℝ in 3 / 5..1, U x * r x) +
        ∫ x : ℝ in 3 / 5..1, T x * r x := by
    rw [← intervalIntegral.integral_add hUprodI hTU]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [U, T]
    unfold fourCellOddP13AugmentedResidualUpperSelectorResidual
      fourCellOddP13SixModeSelector
    ring
  have hpair :
      fourCellOddCoreLocalBilinear
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) r =
        (∫ x : ℝ in 0..3 / 5, L x * r x) +
          ∫ x : ℝ in 3 / 5..1, U x * r x := by
    rw [fourCellOddP13AugmentedGalerkinResidualProfile_eq_sixMode]
    rw [hrawL, hrawU] at hrawPair
    rw [hrawPair]
    linarith only [hTsplit, hTzero]
  have hcauchyL := sq_integral_mul_le_weighted
    μL (fun _ : ℝ ↦ 1) L r (by simp)
      (by simpa only [div_one, Real.sqrt_one] using hL)
      (by simpa only [Real.sqrt_one, one_mul] using hrL)
  have hcauchyU := sq_integral_mul_le_weighted
    μU (fun _ : ℝ ↦ 1) U r (by simp)
      (by simpa only [div_one, Real.sqrt_one] using hU)
      (by simpa only [Real.sqrt_one, one_mul] using hrU)
  have hcauchyL' :
      (∫ x : ℝ in 0..3 / 5, L x * r x) ^ 2 ≤
        (∫ x : ℝ in 0..3 / 5, L x ^ 2) *
          (∫ x : ℝ in 0..3 / 5, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μL, div_one, one_mul] using hcauchyL
  have hcauchyU' :
      (∫ x : ℝ in 3 / 5..1, U x * r x) ^ 2 ≤
        (∫ x : ℝ in 3 / 5..1, U x ^ 2) *
          (∫ x : ℝ in 3 / 5..1, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μU, div_one, one_mul] using hcauchyU
  have hNL : 0 ≤ ∫ x : ℝ in 0..3 / 5, L x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hNU : 0 ≤ ∫ x : ℝ in 3 / 5..1, U x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hML : 0 ≤ ∫ x : ℝ in 0..3 / 5, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hMU : 0 ≤ ∫ x : ℝ in 3 / 5..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have htwo := sum_pair_sq_le_sum_norm_mul_sum_mass
    (∫ x : ℝ in 0..3 / 5, L x * r x)
    (∫ x : ℝ in 3 / 5..1, U x * r x)
    (∫ x : ℝ in 0..3 / 5, L x ^ 2)
    (∫ x : ℝ in 3 / 5..1, U x ^ 2)
    (∫ x : ℝ in 0..3 / 5, r x ^ 2)
    (∫ x : ℝ in 3 / 5..1, r x ^ 2)
    hNL hNU hML hMU hcauchyL' hcauchyU'
  have hrLInt : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume 0 (3 / 5) := (hr.continuous.pow 2).intervalIntegrable _ _
  have hrUInt : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume (3 / 5) 1 := (hr.continuous.pow 2).intervalIntegrable _ _
  have hmassSplit := intervalIntegral.integral_add_adjacent_intervals
    hrLInt hrUInt
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  change (∫ x : ℝ in 0..3 / 5, L x ^ 2) +
      (∫ x : ℝ in 3 / 5..1, U x ^ 2) ≤
    fourCellOddCoreLocalQuadratic
        (fourCellOddP13AugmentedGalerkinResidualProfile
          a3 a5 a7 a9 a11) * kappa at hnorm
  have hnormScaled := mul_le_mul_of_nonneg_right hnorm hmass
  rw [hmassSplit] at htwo
  rw [hpair]
  nlinarith only [htwo, hnormScaled]

theorem fourCellOddP13AugmentedGalerkinResidualL2Dual_of_moduloSixModeTwoStripNormBound
    (kappa a3 a5 a7 a9 a11 : ℝ)
    (hnorm : FourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound
      kappa a3 a5 a7 a9 a11) :
    FourCellOddP13AugmentedGalerkinResidualL2Dual
      kappa a3 a5 a7 a9 a11 := by
  rcases hnorm with ⟨b1, b3, b5, b7, b9, b11, hbound⟩
  exact
    fourCellOddP13AugmentedGalerkinResidualL2Dual_of_selectorTwoStripNormBound
      kappa a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 hbound

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
