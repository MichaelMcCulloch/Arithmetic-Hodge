import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11EndpointFormDualClosureStructural
import ArithmeticHodge.Analysis.ShiftedLogKernelCrossEnergy
import ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11FiveModeThreeHalvesStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreLogKernel
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open ShiftedLogKernelCrossEnergy
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11EndpointFormDualClosureStructural
open YoshidaFourCellOddP11ThreeHalvesClosureStructural
open YoshidaFourCellOddP11WeightedDualSelectorStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# The five-mode selector at matched factor `3 / 2`

This module exposes the exact degree-`< 11` upper-strip raw representer for
an arbitrary retained `P₁/P₃/P₅/P₇/P₉` profile.  The singular double
integral is first diagonalized by the polynomial logarithmic kernel and is
then transported to the physical endpoint strip.  This is the structural
input needed to turn the remaining five-mode weighted Cauchy problem into a
finite selector Gram inequality.
-/

/-- Polynomial whose evaluation is the retained five-mode low profile. -/
def fourCellOddFiveModePolynomial (c d e f g : ℝ) : ℝ[X] :=
  c • X +
    d • ((1 / 2 : ℝ) • ((5 : ℝ) • X ^ 3 - (3 : ℝ) • X)) +
    e • ((1 / 8 : ℝ) •
      ((63 : ℝ) • X ^ 5 - (70 : ℝ) • X ^ 3 + (15 : ℝ) • X)) +
    f • ((1 / 16 : ℝ) •
      ((429 : ℝ) • X ^ 7 - (693 : ℝ) • X ^ 5 +
        (315 : ℝ) • X ^ 3 - (35 : ℝ) • X)) +
    g • ((1 / 128 : ℝ) •
      ((12155 : ℝ) • X ^ 9 - (25740 : ℝ) • X ^ 7 +
        (18018 : ℝ) • X ^ 5 - (4620 : ℝ) • X ^ 3 +
          (315 : ℝ) • X))

theorem fourCellOddFiveModePolynomial_eval
    (c d e f g x : ℝ) :
    (fourCellOddFiveModePolynomial c d e f g).eval x =
      fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x := by
  unfold fourCellOddFiveModePolynomial
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul]
  rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  ring

/-- Polynomial of the reflection-odd endpoint-strip pullback. -/
def fourCellOddFiveModeEndpointStripOddPolynomial
    (c d e f g : ℝ) : ℝ[X] :=
  let p := fourCellOddFiveModePolynomial c d e f g
  (1 / 2 : ℝ) •
    (p.comp ((1 / 5 : ℝ) • X + C (4 / 5 : ℝ)) -
      p.comp ((-(1 / 5 : ℝ)) • X + C (4 / 5 : ℝ)))

/-- The same strip polynomial after the centered-to-unit affine pullback. -/
def fourCellOddFiveModeEndpointStripOddUnitPolynomial
    (c d e f g : ℝ) : ℝ[X] :=
  (fourCellOddFiveModeEndpointStripOddPolynomial c d e f g).comp
    ((2 : ℝ) • X - C 1)

theorem fourCellOddFiveModeEndpointStripOddPolynomial_eval
    (c d e f g z : ℝ) :
    (fourCellOddFiveModeEndpointStripOddPolynomial c d e f g).eval z =
      fourCellOddEndpointStripOdd
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) z := by
  unfold fourCellOddFiveModeEndpointStripOddPolynomial
    fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  dsimp only
  simp only [Polynomial.eval_smul, Polynomial.eval_sub,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, smul_eq_mul]
  rw [fourCellOddFiveModePolynomial_eval,
    fourCellOddFiveModePolynomial_eval]
  have hplus : (4 / 5 : ℝ) + z / 5 = z * (1 / 5) + 4 / 5 := by ring
  have hminus : (4 / 5 : ℝ) + -z / 5 = z * (-(1 / 5)) + 4 / 5 := by ring
  rw [hplus, hminus]
  ring

theorem centeredPullback_fiveModeEndpointStripOdd_eq_eval
    (c d e f g t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd
          (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)) t =
      (fourCellOddFiveModeEndpointStripOddUnitPolynomial c d e f g).eval t := by
  unfold fourCellOddFiveModeEndpointStripOddUnitPolynomial centeredPullback
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X,
    Polynomial.eval_C, smul_eq_mul]
  rw [fourCellOddFiveModeEndpointStripOddPolynomial_eval]

/-- Public form of the polynomial raw-log representer identity.  The
existing production proof uses this fact internally; it is restated here so
the all-five-mode strip row can be synthesized without expanding tail
modes. -/
theorem centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    (p : ℝ[X]) (q r : ℝ → ℝ) (hr : Continuous r)
    (hmode : ∀ t : ℝ, centeredPullback q t = p.eval t) :
    centeredRawLogBilinear q r =
      4 * ∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLogKernel p).eval (t : ℝ) := by
  let u : unitInterval → ℝ := fun t ↦ centeredPullback r (t : ℝ)
  let U : unitInterval × unitInterval → ℝ := fun z ↦
    (u z.1 - u z.2) * unitIntervalRawPolynomialLogKernel p z
  have hucont : Continuous u := by
    dsimp only [u, centeredPullback]
    exact hr.comp (by fun_prop)
  have hu : Integrable u :=
    hucont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUInt : Integrable U := by
    simpa only [U] using
      integrable_sub_mul_unitIntervalRawPolynomialLogKernel u hu p
  have hcross :=
    integral_sub_mul_unitIntervalRawPolynomialLogKernel_eq u hu p
  have hUpair : (∫ z, U z) =
      2 * ∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLogKernel p).eval (t : ℝ) := by
    simpa only [U, u] using hcross
  have hiter : (∫ z, U z) =
      ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|) := by
    calc
      (∫ z, U z) = ∫ s : unitInterval, ∫ t : unitInterval, U (s, t) :=
        MeasureTheory.integral_prod _ hUInt
      _ = ∫ s : unitInterval, ∫ t : ℝ in 0..1,
          (centeredPullback r (s : ℝ) - centeredPullback r t) *
            ((p.eval (s : ℝ) - p.eval t) / |(s : ℝ) - t|) := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [← integral_unitInterval_eq_intervalIntegral]
        apply integral_congr_ae
        filter_upwards [] with t
        rfl
      _ = _ := by
        rw [← integral_unitInterval_eq_intervalIntegral]
  rw [hiter] at hUpair
  have hpoint (s t : ℝ) :
      (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|) =
        2 * (((q (2 * s - 1) - q (2 * t - 1)) *
          (r (2 * s - 1) - r (2 * t - 1))) /
            |(2 * s - 1) - (2 * t - 1)|) := by
    have hms := hmode s
    have hmt := hmode t
    unfold centeredPullback at hms hmt ⊢
    rw [← hms, ← hmt,
      show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hst : |s - t| = 0
    · simp [hst]
    · field_simp [hst]
  have hscaled :
      (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        (centeredPullback r s - centeredPullback r t) *
          ((p.eval s - p.eval t) / |s - t|)) =
        (1 / 2 : ℝ) * centeredRawLogBilinear q r := by
    let H : ℝ → ℝ → ℝ := fun x y ↦
      ((q x - q y) * (r x - r y)) / |x - y|
    calc
      _ = ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          2 * H (2 * s - 1) (2 * t - 1) := by
        apply intervalIntegral.integral_congr
        intro s _hs
        apply intervalIntegral.integral_congr
        intro t _ht
        exact hpoint s t
      _ = 2 * (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
          H (2 * s - 1) (2 * t - 1)) := by
        rw [show (fun s : ℝ ↦ ∫ t : ℝ in 0..1,
            2 * H (2 * s - 1) (2 * t - 1)) =
            fun s ↦ 2 * ∫ t : ℝ in 0..1,
              H (2 * s - 1) (2 * t - 1) by
          funext s
          rw [intervalIntegral.integral_const_mul],
          intervalIntegral.integral_const_mul]
      _ = 2 * ((1 / 4 : ℝ) *
          ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, H x y) := by
        rw [integral_integral_comp_two_mul_sub_one H]
      _ = _ := by
        unfold centeredRawLogBilinear
        dsimp only [H]
        ring
  rw [hscaled] at hUpair
  linarith

/-- Exact upper-strip density generated by the adverse raw-log row. -/
def fourCellOddFiveModeRawUpperRepresenter
    (c d e f g : ℝ) (x : ℝ) : ℝ :=
  let K := shiftedLogKernel
    (fourCellOddFiveModeEndpointStripOddUnitPolynomial c d e f g)
  K.eval ((5 * x - 3) / 2) - K.eval ((5 - 5 * x) / 2)

/-- The adverse strip raw polarization is exactly the pairing with the
displayed degree-`< 11` upper-strip representer.  No tail truncation is
used: only the polynomiality of the retained low profile enters. -/
theorem fourCellOddEndpointStripOddRawPolarization_fiveMode_eq_integral
    (c d e f g : ℝ) (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) :
    fourCellOddEndpointStripOddRawPolarization
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r =
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddFiveModeRawUpperRepresenter c d e f g x * r x := by
  let low : ℝ → ℝ :=
    fourCellOddOneThreeFiveSevenNineLowProfile c d e f g
  let strip : ℝ → ℝ := fourCellOddEndpointStripOdd low
  let tailStrip : ℝ → ℝ := fourCellOddEndpointStripOdd r
  let p : ℝ[X] :=
    fourCellOddFiveModeEndpointStripOddUnitPolynomial c d e f g
  let K : ℝ[X] := shiftedLogKernel p
  have hlow : ContDiff ℝ 1 low := by
    dsimp only [low]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g
  have htailStrip : Continuous tailStrip := by
    dsimp only [tailStrip]
    unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    fun_prop
  have hmode : ∀ t : ℝ, centeredPullback strip t = p.eval t := by
    intro t
    dsimp only [strip, low, p]
    exact centeredPullback_fiveModeEndpointStripOdd_eq_eval c d e f g t
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
  unfold fourCellOddFiveModeRawUpperRepresenter
  convert hraw using 1
  ring

/-! ## Exact nonsingular endpoint rows -/

/-- Affine transport of the reflection-even endpoint mass.  This form is
valid for arbitrary continuous profiles; the reflected copy is absorbed by
the symmetry of the strip channel. -/
theorem fourCellOddEndpointStripEvenMassBilinear_eq_integral
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r) :
    fourCellOddEndpointStripEvenMassBilinear u r =
      ∫ x : ℝ in 3 / 5..1,
        ((u x + u (8 / 5 - x)) / 2) * r x := by
  let F : ℝ → ℝ := fun x ↦ ((u x + u (8 / 5 - x)) / 2) * r x
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  have hplus := intervalIntegral.integral_comp_add_mul
    (a := (-1 : ℝ)) (b := 1) (f := F)
      (by norm_num : (1 / 5 : ℝ) ≠ 0) (4 / 5)
  have hminus := intervalIntegral.integral_comp_sub_mul
    (a := (-1 : ℝ)) (b := 1) (f := F)
      (by norm_num : (1 / 5 : ℝ) ≠ 0) (4 / 5)
  unfold fourCellOddEndpointStripEvenMassBilinear
    fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
  rw [show (fun z : ℝ ↦
      ((u (4 / 5 + z / 5) + u (4 / 5 + -z / 5)) / 2) *
        ((r (4 / 5 + z / 5) + r (4 / 5 + -z / 5)) / 2)) =
      fun z ↦ (1 / 2 : ℝ) *
        (F (4 / 5 + (1 / 5) * z) + F (4 / 5 - (1 / 5) * z)) by
    funext z
    dsimp only [F]
    ring_nf,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      (by exact (show Continuous (fun z : ℝ ↦
          F (4 / 5 + (1 / 5) * z)) by fun_prop).intervalIntegrable _ _)
      (by exact (show Continuous (fun z : ℝ ↦
          F (4 / 5 - (1 / 5) * z)) by fun_prop).intervalIntegrable _ _),
    hplus, hminus]
  norm_num [F, smul_eq_mul]
  ring

/-- Affine transport of the reflection-odd endpoint mass. -/
theorem fourCellOddEndpointStripOddMassBilinear_eq_integral
    (u r : ℝ → ℝ) (hu : Continuous u) (hr : Continuous r) :
    fourCellOddEndpointStripOddMassBilinear u r =
      ∫ x : ℝ in 3 / 5..1,
        ((u x - u (8 / 5 - x)) / 2) * r x := by
  let F : ℝ → ℝ := fun x ↦ ((u x - u (8 / 5 - x)) / 2) * r x
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  have hplus := intervalIntegral.integral_comp_add_mul
    (a := (-1 : ℝ)) (b := 1) (f := F)
      (by norm_num : (1 / 5 : ℝ) ≠ 0) (4 / 5)
  have hminus := intervalIntegral.integral_comp_sub_mul
    (a := (-1 : ℝ)) (b := 1) (f := F)
      (by norm_num : (1 / 5 : ℝ) ≠ 0) (4 / 5)
  unfold fourCellOddEndpointStripOddMassBilinear
    fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  rw [show (fun z : ℝ ↦
      ((u (4 / 5 + z / 5) - u (4 / 5 + -z / 5)) / 2) *
        ((r (4 / 5 + z / 5) - r (4 / 5 + -z / 5)) / 2)) =
      fun z ↦ (1 / 2 : ℝ) *
        (F (4 / 5 + (1 / 5) * z) + F (4 / 5 - (1 / 5) * z)) by
    funext z
    dsimp only [F]
    ring_nf,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      (by exact (show Continuous (fun z : ℝ ↦
          F (4 / 5 + (1 / 5) * z)) by fun_prop).intervalIntegrable _ _)
      (by exact (show Continuous (fun z : ℝ ↦
          F (4 / 5 - (1 / 5) * z)) by fun_prop).intervalIntegrable _ _),
    hplus, hminus]
  norm_num [F, smul_eq_mul]
  ring

/-! ## Positive-half form of the smooth row -/

private theorem fiveModeRegularRightRepresenter_neg_of_odd
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

private theorem fiveModeRegularLeftRepresenter_neg_of_odd
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

private theorem odd_factorTwoContinuousLagK_of_odd_fiveMode
    (q p : ℝ → ℝ) (hp : Function.Odd p) :
    Function.Odd (factorTwoContinuousLagK q p) := by
  intro x
  unfold factorTwoContinuousLagK
  rw [fiveModeRegularRightRepresenter_neg_of_odd q p hp,
    fiveModeRegularLeftRepresenter_neg_of_odd q p hp]
  ring

theorem odd_fourCellOddFiveModeRegularRepresenter
    (c d e f g : ℝ) :
    Function.Odd (fourCellOddFiveModeRegularRepresenter c d e f g) := by
  unfold fourCellOddFiveModeRegularRepresenter
  exact odd_factorTwoContinuousLagK_of_odd_fiveMode _ _
    (odd_fourCellOddOneThreeFiveSevenNineLowProfile c d e f g)

private theorem fiveModeRegularLag_abs_le_quarter
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

theorem intervalIntegrable_mul_fourCellOddFiveModeRegularRepresenter
    (u : ℝ → ℝ) (hu : Continuous u) (c d e f g : ℝ) :
    IntervalIntegrable
      (fun x : ℝ ↦ u x * fourCellOddFiveModeRegularRepresenter c d e f g x)
      volume (-1) 1 := by
  let q : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let p : ℝ → ℝ :=
    fourCellOddOneThreeFiveSevenNineLowProfile c d e f g
  have hq : Measurable q := by
    dsimp only [q]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hp : Continuous p := by
    dsimp only [p]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      c d e f g).continuous
  have hqbound : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ 1 / 4 := by
    intro t ht
    simpa only [q] using fiveModeRegularLag_abs_le_quarter t ht
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

/-- Oddness of both factors folds the complete smooth representer exactly
to the positive half interval. -/
theorem integral_mul_fourCellOddFiveModeRegularRepresenter_eq_two_mul
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (c d e f g : ℝ) :
    (∫ x : ℝ in -1..1,
        r x * fourCellOddFiveModeRegularRepresenter c d e f g x) =
      2 * ∫ x : ℝ in 0..1,
        r x * fourCellOddFiveModeRegularRepresenter c d e f g x := by
  have heven : Function.Even (fun x : ℝ ↦
      r x * fourCellOddFiveModeRegularRepresenter c d e f g x) := by
    intro x
    change r (-x) * fourCellOddFiveModeRegularRepresenter c d e f g (-x) =
      r x * fourCellOddFiveModeRegularRepresenter c d e f g x
    rw [hodd x, odd_fourCellOddFiveModeRegularRepresenter c d e f g x]
    ring
  exact integral_neg_one_one_eq_two_mul_zero_one_of_even _
    (intervalIntegrable_mul_fourCellOddFiveModeRegularRepresenter
      r hr c d e f g) heven

/-! ## Complete two-strip representer -/

theorem continuous_fourCellOddFiveModeRawUpperRepresenter
    (c d e f g : ℝ) :
    Continuous (fourCellOddFiveModeRawUpperRepresenter c d e f g) := by
  let K : ℝ[X] := shiftedLogKernel
    (fourCellOddFiveModeEndpointStripOddUnitPolynomial c d e f g)
  have hK : Continuous (fun x : ℝ ↦ K.eval x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (K.hasDerivAt x).continuousAt
  unfold fourCellOddFiveModeRawUpperRepresenter
  exact (hK.comp (by fun_prop)).sub (hK.comp (by fun_prop))

/-- Exact row density below the endpoint strip. -/
def fourCellOddFiveModeLowerRepresenter
    (c d e f g : ℝ) (x : ℝ) : ℝ :=
  (93 / 50 : ℝ) * yoshidaEndpointPotential x *
      fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x -
    2 * fourCellOperatorHalfWidth *
      fourCellOddFiveModeRegularRepresenter c d e f g x

/-- Exact row density on the upper endpoint strip.  The first two added
terms are respectively the reflection-even and reflection-odd prime rows;
the last one is the adverse raw-log row. -/
def fourCellOddFiveModeUpperRepresenter
    (c d e f g : ℝ) (x : ℝ) : ℝ :=
  fourCellOddFiveModeLowerRepresenter c d e f g x +
    Real.sqrt 2 * Real.log 2 *
      ((fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x +
        fourCellOddOneThreeFiveSevenNineLowProfile c d e f g (8 / 5 - x)) / 2) +
    (2 - Real.sqrt 2 * Real.log 2) *
      ((fourCellOddOneThreeFiveSevenNineLowProfile c d e f g x -
        fourCellOddOneThreeFiveSevenNineLowProfile c d e f g (8 / 5 - x)) / 2) -
    (1 / 2 : ℝ) * fourCellOddFiveModeRawUpperRepresenter c d e f g x

/-- Exact positive-half normal form of the complete five-mode/`P₁₁+`
mixed row.  Every term is now a one-variable pairing against the same tail;
in particular no singular double integral or lag correlation remains. -/
theorem fourCellOddCoreLocalBilinear_fiveMode_P11Plus_eq_twoStripRepresenter
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (c d e f g : ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r =
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddFiveModeLowerRepresenter c d e f g x * r x) +
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddFiveModeUpperRepresenter c d e f g x * r x := by
  let low : ℝ → ℝ :=
    fourCellOddOneThreeFiveSevenNineLowProfile c d e f g
  let P : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * low x * r x
  let R : ℝ → ℝ := fun x ↦
    r x * fourCellOddFiveModeRegularRepresenter c d e f g x
  let E : ℝ → ℝ := fun x ↦ ((low x + low (8 / 5 - x)) / 2) * r x
  let O : ℝ → ℝ := fun x ↦ ((low x - low (8 / 5 - x)) / 2) * r x
  let S : ℝ → ℝ := fun x ↦
    fourCellOddFiveModeRawUpperRepresenter c d e f g x * r x
  have hlow : Continuous low := by
    dsimp only [low]
    exact (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
      c d e f g).continuous
  have hPfull : IntervalIntegrable P volume (-1) 1 := by
    dsimp only [P, low]
    exact intervalIntegrable_endpointPotential_mul
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) r
      hlow hr.continuous
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
    exact intervalIntegrable_mul_fourCellOddFiveModeRegularRepresenter
      r hr.continuous c d e f g
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
    exact ((continuous_fourCellOddFiveModeRawUpperRepresenter c d e f g).mul
      hr.continuous).intervalIntegrable _ _
  have hPSplit := intervalIntegral.integral_add_adjacent_intervals hPL hPU
  have hRSplit := intervalIntegral.integral_add_adjacent_intervals hRL hRU
  have hraw :=
    fourCellOddEndpointStripOddRawPolarization_fiveMode_eq_integral
      c d e f g r hr
  have heven := fourCellOddEndpointStripEvenMassBilinear_eq_integral
    low r hlow hr.continuous
  have hstripOdd := fourCellOddEndpointStripOddMassBilinear_eq_integral
    low r hlow hr.continuous
  have hRFold :=
    integral_mul_fourCellOddFiveModeRegularRepresenter_eq_two_mul
      r hr.continuous hodd c d e f g
  have hrow :=
    fourCellOddCoreLocalBilinear_fiveMode_P11Plus_eq_regularRepresenter
      r hr hodd h1 h3 h5 h7 h9 c d e f g
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
      fourCellOddFiveModeLowerRepresenter c d e f g x * r x) =
      fun x ↦ (93 / 50 : ℝ) * P x -
        2 * fourCellOperatorHalfWidth * R x by
    funext x
    dsimp only [P, R, low]
    unfold fourCellOddFiveModeLowerRepresenter
    ring,
    show (fun x : ℝ ↦
      fourCellOddFiveModeUpperRepresenter c d e f g x * r x) =
      fun x ↦
        ((93 / 50 : ℝ) * P x - 2 * fourCellOperatorHalfWidth * R x) +
          Real.sqrt 2 * Real.log 2 * E x +
          (2 - Real.sqrt 2 * Real.log 2) * O x - (1 / 2 : ℝ) * S x by
    funext x
    dsimp only [P, R, E, O, S, low]
    unfold fourCellOddFiveModeUpperRepresenter
      fourCellOddFiveModeLowerRepresenter
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
    intervalIntegral.integral_sub (hPU.const_mul _) (hRU.const_mul _)]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [hrow]
  ring

/-! ## A genuine finite `P₁₁+` probe for the factor `3 / 2` -/

/-- Rational low direction selected by the adverse finite Gram channel. -/
def fourCellOddP11ThreeHalvesCounterexampleLow : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile
    (-1) 1 (-(1 / 4 : ℝ)) (1 / 6 : ℝ) (3 / 8 : ℝ)

/-- Four high odd Legendre modes, beginning strictly above the retained
block.  For odd indices `centeredShiftedLegendreReal` is the negative of the
classical centered Legendre convention, hence these signs represent
`(4/5)P₁₃ - P₁₇ + P₂₁ - (2/3)P₂₅`. -/
def fourCellOddP11ThreeHalvesCounterexampleTailPolynomial : ℝ[X] :=
  (-(4 / 5 : ℝ)) • centeredShiftedLegendreReal 13 +
    centeredShiftedLegendreReal 17 - centeredShiftedLegendreReal 21 +
      (2 / 3 : ℝ) • centeredShiftedLegendreReal 25

def fourCellOddP11ThreeHalvesCounterexampleTail : ℝ → ℝ := fun x ↦
  fourCellOddP11ThreeHalvesCounterexampleTailPolynomial.eval x

theorem contDiff_fourCellOddP11ThreeHalvesCounterexampleTail :
    ContDiff ℝ 1 fourCellOddP11ThreeHalvesCounterexampleTail := by
  unfold fourCellOddP11ThreeHalvesCounterexampleTail
  exact fourCellOddP11ThreeHalvesCounterexampleTailPolynomial.contDiff_aeval
    (𝕜 := ℝ) 1

theorem odd_fourCellOddP11ThreeHalvesCounterexampleTail :
    Function.Odd fourCellOddP11ThreeHalvesCounterexampleTail := by
  intro x
  unfold fourCellOddP11ThreeHalvesCounterexampleTail
    fourCellOddP11ThreeHalvesCounterexampleTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul, eval_centeredShiftedLegendreReal_neg]
  norm_num
  ring

private theorem counterexample_centeredP1_eq_legendre :
    centeredP1 = fun x ↦ -(centeredShiftedLegendreReal 1).eval x := by
  funext x
  rw [ShiftedLegendreCenteredLowModes.eval_centeredShiftedLegendreReal_one]
  unfold centeredP1
  ring

private theorem counterexample_centeredP3_eq_legendre :
    centeredP3 = fun x ↦ -(centeredShiftedLegendreReal 3).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose, centeredP3,
    Polynomial.smul_eq_C_mul]
  ring

private theorem counterexample_centeredP5_eq_legendre :
    factorTwoCenteredP5 =
      fun x ↦ -(centeredShiftedLegendreReal 5).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    factorTwoCenteredP5, Polynomial.smul_eq_C_mul]
  ring

private theorem counterexample_centeredP7_eq_legendre :
    factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP7 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem counterexample_centeredP9_eq_legendre :
    factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP9 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem integral_threeHalvesCounterexampleTail_mul_centeredMode_eq_zero
    (n : ℕ) (hn : n < 11) :
    (∫ x : ℝ in -1..1,
      fourCellOddP11ThreeHalvesCounterexampleTail x *
        (centeredShiftedLegendreReal n).eval x) = 0 := by
  have h13 := centeredPolynomialPair_legendre_eq_zero
    (m := 13) (n := n) (by omega)
  have h17 := centeredPolynomialPair_legendre_eq_zero
    (m := 17) (n := n) (by omega)
  have h21 := centeredPolynomialPair_legendre_eq_zero
    (m := 21) (n := n) (by omega)
  have h25 := centeredPolynomialPair_legendre_eq_zero
    (m := 25) (n := n) (by omega)
  unfold centeredPolynomialPair at h13 h17 h21 h25
  have h13I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 13).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 :=
    ((centeredShiftedLegendreReal 13).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h17I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 17).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 :=
    ((centeredShiftedLegendreReal 17).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h21I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 21).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 :=
    ((centeredShiftedLegendreReal 21).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h25I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 25).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 :=
    ((centeredShiftedLegendreReal 25).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  unfold fourCellOddP11ThreeHalvesCounterexampleTail
    fourCellOddP11ThreeHalvesCounterexampleTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  rw [show (fun x : ℝ ↦
      ((-(4 / 5 : ℝ)) * (centeredShiftedLegendreReal 13).eval x +
          (centeredShiftedLegendreReal 17).eval x -
          (centeredShiftedLegendreReal 21).eval x +
          (2 / 3 : ℝ) * (centeredShiftedLegendreReal 25).eval x) *
        (centeredShiftedLegendreReal n).eval x) = fun x ↦
      (-(4 / 5 : ℝ)) * ((centeredShiftedLegendreReal 13).eval x *
        (centeredShiftedLegendreReal n).eval x) +
      (centeredShiftedLegendreReal 17).eval x *
        (centeredShiftedLegendreReal n).eval x -
      (centeredShiftedLegendreReal 21).eval x *
        (centeredShiftedLegendreReal n).eval x +
      (2 / 3 : ℝ) * ((centeredShiftedLegendreReal 25).eval x *
        (centeredShiftedLegendreReal n).eval x) by
    funext x
    ring,
    intervalIntegral.integral_add
      (((h13I.const_mul _).add h17I).sub h21I) (h25I.const_mul _),
    intervalIntegral.integral_sub ((h13I.const_mul _).add h17I) h21I,
    intervalIntegral.integral_add (h13I.const_mul _) h17I,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    h13, h17, h21, h25]
  ring

/-- The displayed degree-25 polynomial is a genuine `P₁₁+` tail: all
five retained odd moments vanish by orthogonality, not coefficient
enumeration. -/
theorem fourCellOddP11ThreeHalvesCounterexampleTail_moments :
    centeredOddP1Coefficient fourCellOddP11ThreeHalvesCounterexampleTail = 0 ∧
    centeredOddP3Coefficient fourCellOddP11ThreeHalvesCounterexampleTail = 0 ∧
    centeredOddP5Coefficient fourCellOddP11ThreeHalvesCounterexampleTail = 0 ∧
    centeredOddP7Coefficient fourCellOddP11ThreeHalvesCounterexampleTail = 0 ∧
    centeredOddP9Coefficient fourCellOddP11ThreeHalvesCounterexampleTail = 0 := by
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient centeredOddP7Coefficient centeredOddP9Coefficient
  rw [counterexample_centeredP1_eq_legendre,
    counterexample_centeredP3_eq_legendre,
    counterexample_centeredP5_eq_legendre,
    counterexample_centeredP7_eq_legendre,
    counterexample_centeredP9_eq_legendre]
  have h1 := integral_threeHalvesCounterexampleTail_mul_centeredMode_eq_zero
    1 (by omega)
  have h3 := integral_threeHalvesCounterexampleTail_mul_centeredMode_eq_zero
    3 (by omega)
  have h5 := integral_threeHalvesCounterexampleTail_mul_centeredMode_eq_zero
    5 (by omega)
  have h7 := integral_threeHalvesCounterexampleTail_mul_centeredMode_eq_zero
    7 (by omega)
  have h9 := integral_threeHalvesCounterexampleTail_mul_centeredMode_eq_zero
    9 (by omega)
  simp only []
  repeat' first
    | rw [show (fun x : ℝ ↦
          fourCellOddP11ThreeHalvesCounterexampleTail x *
            -(centeredShiftedLegendreReal 1).eval x) = fun x ↦
          -(fourCellOddP11ThreeHalvesCounterexampleTail x *
            (centeredShiftedLegendreReal 1).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h1]
    | rw [show (fun x : ℝ ↦
          fourCellOddP11ThreeHalvesCounterexampleTail x *
            -(centeredShiftedLegendreReal 3).eval x) = fun x ↦
          -(fourCellOddP11ThreeHalvesCounterexampleTail x *
            (centeredShiftedLegendreReal 3).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h3]
    | rw [show (fun x : ℝ ↦
          fourCellOddP11ThreeHalvesCounterexampleTail x *
            -(centeredShiftedLegendreReal 5).eval x) = fun x ↦
          -(fourCellOddP11ThreeHalvesCounterexampleTail x *
            (centeredShiftedLegendreReal 5).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h5]
    | rw [show (fun x : ℝ ↦
          fourCellOddP11ThreeHalvesCounterexampleTail x *
            -(centeredShiftedLegendreReal 7).eval x) = fun x ↦
          -(fourCellOddP11ThreeHalvesCounterexampleTail x *
            (centeredShiftedLegendreReal 7).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h7]
    | rw [show (fun x : ℝ ↦
          fourCellOddP11ThreeHalvesCounterexampleTail x *
            -(centeredShiftedLegendreReal 9).eval x) = fun x ↦
          -(fourCellOddP11ThreeHalvesCounterexampleTail x *
            (centeredShiftedLegendreReal 9).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h9]
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11FiveModeThreeHalvesStructural
