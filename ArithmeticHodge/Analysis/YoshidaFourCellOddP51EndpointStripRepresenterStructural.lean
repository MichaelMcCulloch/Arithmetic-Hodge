import ArithmeticHodge.Analysis.YoshidaFourCellOddP51RawMassCancellationStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedResidualRepresenterStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped BigOperators unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51EndpointStripRepresenterStructural

noncomputable section

open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogKernel
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP11FiveModeThreeHalvesStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Polynomial upper-strip representer for q51

The endpoint-strip raw polarization is singular only before its polynomial
mode is inserted.  For the exact inverse-solved `q51`, the shifted log
operator produces an ordinary polynomial density on `[3/5,1]`.  Combining
that density with the two physical strip channels gives one continuous
upper-strip correction.
-/

/-- Polynomial realization of the exact inverse-solved `q51`. -/
def fourCellOddQ51Polynomial : ℝ[X] :=
  (-(centeredShiftedLegendreReal 1)) -
    ∑ i : FourCellOddP51RetainedIndex,
      fourCellOddP51RetainedSolution i •
        (-(centeredShiftedLegendreReal
          (fourCellOddFiniteRetainedDegree i)))

theorem fourCellOddQ51Polynomial_eval (x : ℝ) :
    fourCellOddQ51Polynomial.eval x = fourCellOddQ51 x := by
  rw [fourCellOddQ51_eq]
  unfold fourCellOddQ51Polynomial fourCellOddP51RetainedProfile
    fourCellOddFiniteRetainedProfile fourCellOddFiniteRetainedBasis
    centeredP1
  simp only [Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_finset_sum, Polynomial.eval_smul, Finset.sum_apply,
    smul_eq_mul, eval_centeredShiftedLegendreReal_one]
  ring

/-- Reflection-odd endpoint-strip pullback of the q51 polynomial. -/
def fourCellOddQ51EndpointStripOddPolynomial : ℝ[X] :=
  let p := fourCellOddQ51Polynomial
  (1 / 2 : ℝ) •
    (p.comp ((1 / 5 : ℝ) • X + C (4 / 5 : ℝ)) -
      p.comp ((-(1 / 5 : ℝ)) • X + C (4 / 5 : ℝ)))

/-- Unit-interval realization of the reflection-odd strip polynomial. -/
def fourCellOddQ51EndpointStripOddUnitPolynomial : ℝ[X] :=
  fourCellOddQ51EndpointStripOddPolynomial.comp
    ((2 : ℝ) • X - C 1)

theorem fourCellOddQ51EndpointStripOddPolynomial_eval (z : ℝ) :
    fourCellOddQ51EndpointStripOddPolynomial.eval z =
      fourCellOddEndpointStripOdd fourCellOddQ51 z := by
  unfold fourCellOddQ51EndpointStripOddPolynomial
    fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
  dsimp only
  simp only [Polynomial.eval_smul, Polynomial.eval_sub,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, smul_eq_mul]
  rw [fourCellOddQ51Polynomial_eval, fourCellOddQ51Polynomial_eval]
  ring

theorem centeredPullback_fourCellOddQ51EndpointStripOdd_eq_eval
    (t : ℝ) :
    centeredPullback (fourCellOddEndpointStripOdd fourCellOddQ51) t =
      fourCellOddQ51EndpointStripOddUnitPolynomial.eval t := by
  unfold fourCellOddQ51EndpointStripOddUnitPolynomial centeredPullback
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X,
    Polynomial.eval_C, smul_eq_mul]
  rw [fourCellOddQ51EndpointStripOddPolynomial_eval]

/-- Exact polynomial density of the adverse raw endpoint row. -/
def fourCellOddQ51RawUpperRepresenter (x : ℝ) : ℝ :=
  let K := shiftedLogKernel fourCellOddQ51EndpointStripOddUnitPolynomial
  K.eval ((5 * x - 3) / 2) - K.eval ((5 - 5 * x) / 2)

/-- Polynomiality converts the q51 endpoint-strip raw polarization into an
ordinary upper-strip pairing. -/
theorem fourCellOddEndpointStripOddRawPolarization_Q51_eq_integral
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) :
    fourCellOddEndpointStripOddRawPolarization fourCellOddQ51 r =
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddQ51RawUpperRepresenter x * r x := by
  let low : ℝ → ℝ := fourCellOddQ51
  let strip : ℝ → ℝ := fourCellOddEndpointStripOdd low
  let tailStrip : ℝ → ℝ := fourCellOddEndpointStripOdd r
  let p : ℝ[X] := fourCellOddQ51EndpointStripOddUnitPolynomial
  let K : ℝ[X] := shiftedLogKernel p
  have hlow : ContDiff ℝ 1 low := by
    simpa only [low] using contDiff_fourCellOddQ51
  have htailStrip : Continuous tailStrip := by
    dsimp only [tailStrip]
    unfold fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    fun_prop
  have hmode : ∀ t : ℝ, centeredPullback strip t = p.eval t := by
    intro t
    dsimp only [strip, low, p]
    exact centeredPullback_fourCellOddQ51EndpointStripOdd_eq_eval t
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
  unfold fourCellOddQ51RawUpperRepresenter
  convert hraw using 1
  ring

theorem continuous_fourCellOddQ51RawUpperRepresenter :
    Continuous fourCellOddQ51RawUpperRepresenter := by
  let K : ℝ[X] := shiftedLogKernel
    fourCellOddQ51EndpointStripOddUnitPolynomial
  have hK : Continuous (fun x : ℝ ↦ K.eval x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (K.hasDerivAt x).continuousAt
  unfold fourCellOddQ51RawUpperRepresenter
  exact (hK.comp (by fun_prop)).sub (hK.comp (by fun_prop))

/-- The complete nonsingular upper-strip correction, excluding the global
endpoint-potential and smooth regular rows. -/
def fourCellOddQ51UpperEndpointCorrection (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.log 2 *
      ((fourCellOddQ51 x + fourCellOddQ51 (8 / 5 - x)) / 2) +
    (2 - Real.sqrt 2 * Real.log 2) *
      ((fourCellOddQ51 x - fourCellOddQ51 (8 / 5 - x)) / 2) -
    (1 / 2 : ℝ) * fourCellOddQ51RawUpperRepresenter x

theorem continuous_fourCellOddQ51UpperEndpointCorrection :
    Continuous fourCellOddQ51UpperEndpointCorrection := by
  unfold fourCellOddQ51UpperEndpointCorrection
  exact (continuous_const.mul
      ((contDiff_fourCellOddQ51.continuous.add
        (contDiff_fourCellOddQ51.continuous.comp (by fun_prop))).div_const 2))
    |>.add (continuous_const.mul
      ((contDiff_fourCellOddQ51.continuous.sub
        (contDiff_fourCellOddQ51.continuous.comp (by fun_prop))).div_const 2))
    |>.sub (continuous_const.mul
      continuous_fourCellOddQ51RawUpperRepresenter)

/-- The raw and two physical endpoint-strip channels combine into the one
continuous correction density. -/
theorem fourCellOddQ51_endpoint_channels_eq_upperCorrection
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) :
    -(1 / 2 : ℝ) *
        fourCellOddEndpointStripOddRawPolarization fourCellOddQ51 r +
      Real.sqrt 2 * Real.log 2 *
        fourCellOddEndpointStripEvenMassBilinear fourCellOddQ51 r +
      (2 - Real.sqrt 2 * Real.log 2) *
        fourCellOddEndpointStripOddMassBilinear fourCellOddQ51 r =
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddQ51UpperEndpointCorrection x * r x := by
  have hraw := fourCellOddEndpointStripOddRawPolarization_Q51_eq_integral r hr
  have heven := fourCellOddEndpointStripEvenMassBilinear_eq_integral
    fourCellOddQ51 r contDiff_fourCellOddQ51.continuous hr.continuous
  have hodd := fourCellOddEndpointStripOddMassBilinear_eq_integral
    fourCellOddQ51 r contDiff_fourCellOddQ51.continuous hr.continuous
  have hrawI : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddQ51RawUpperRepresenter x * r x)
      volume (3 / 5) 1 :=
    (continuous_fourCellOddQ51RawUpperRepresenter.mul hr.continuous)
      |>.intervalIntegrable _ _
  have hevenI : IntervalIntegrable
      (fun x : ℝ ↦
        ((fourCellOddQ51 x + fourCellOddQ51 (8 / 5 - x)) / 2) * r x)
      volume (3 / 5) 1 := by
    exact (((contDiff_fourCellOddQ51.continuous.add
      (contDiff_fourCellOddQ51.continuous.comp (by fun_prop))).div_const 2).mul
        hr.continuous).intervalIntegrable _ _
  have hoddI : IntervalIntegrable
      (fun x : ℝ ↦
        ((fourCellOddQ51 x - fourCellOddQ51 (8 / 5 - x)) / 2) * r x)
      volume (3 / 5) 1 := by
    exact (((contDiff_fourCellOddQ51.continuous.sub
      (contDiff_fourCellOddQ51.continuous.comp (by fun_prop))).div_const 2).mul
        hr.continuous).intervalIntegrable _ _
  rw [hraw, heven, hodd]
  unfold fourCellOddQ51UpperEndpointCorrection
  rw [show (fun x : ℝ ↦
      (Real.sqrt 2 * Real.log 2 *
          ((fourCellOddQ51 x + fourCellOddQ51 (8 / 5 - x)) / 2) +
        (2 - Real.sqrt 2 * Real.log 2) *
          ((fourCellOddQ51 x - fourCellOddQ51 (8 / 5 - x)) / 2) -
        (1 / 2 : ℝ) * fourCellOddQ51RawUpperRepresenter x) * r x) =
      fun x ↦
        Real.sqrt 2 * Real.log 2 *
          (((fourCellOddQ51 x + fourCellOddQ51 (8 / 5 - x)) / 2) * r x) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (((fourCellOddQ51 x - fourCellOddQ51 (8 / 5 - x)) / 2) * r x) -
        (1 / 2 : ℝ) * (fourCellOddQ51RawUpperRepresenter x * r x) by
    funext x
    ring,
    intervalIntegral.integral_sub
      ((hevenI.const_mul _).add (hoddI.const_mul _)) (hrawI.const_mul _),
    intervalIntegral.integral_add (hevenI.const_mul _) (hoddI.const_mul _)]
  repeat rw [intervalIntegral.integral_const_mul]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51EndpointStripRepresenterStructural
