import ArithmeticHodge.Analysis.YoshidaFourCellOddP11FormDualProbeStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11EndpointFormDualClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalFormDualClosureStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaConstantBounds
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFourCellOddP11EndpointFormDualClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

/-!
# The exact `P₁` row on its full orthogonal complement

The affine endpoint representer previously exposed on `P₁₁+` in fact only
needs `P₁` orthogonality.  This file records that stronger equality and then
tests the natural scalar weighted-dual closure against the first admissible
direction.  The test is exact: `P₃` disproves the scalar-weight strengthening,
although it does not disprove the complete-form Schur inequality.
-/

private theorem integral_zero_one_centeredP1_mul_eq_zero
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0) :
    (∫ x : ℝ in 0..1, centeredP1 x * r x) = 0 := by
  have hfull : (∫ x : ℝ in -1..1, r x * centeredP1 x) = 0 := by
    rw [integral_mul_centeredP1_eq, hone]
    ring
  have heven : Function.Even (fun x : ℝ ↦ r x * centeredP1 x) := by
    intro x
    change r (-x) * centeredP1 (-x) = r x * centeredP1 x
    rw [hodd]
    unfold centeredP1
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ r x * centeredP1 x)
    ((hr.mul (by unfold centeredP1; fun_prop)).intervalIntegrable _ _)
    heven
  rw [hfull] at hfold
  rw [show (fun x : ℝ ↦ centeredP1 x * r x) =
      fun x ↦ r x * centeredP1 x by
    funext x
    ring]
  linarith

/-- Exact affine/regular representer of the complete `P₁` row on the whole
odd `P₁`-orthogonal subspace.  No `P₃/P₅/P₇/P₉` moment is assumed. -/
theorem fourCellOddCoreLocalBilinear_P1_P1Orthogonal_eq_affineEndpointRepresenter
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (hone : centeredOddP1Coefficient r = 0) :
    fourCellOddCoreLocalBilinear centeredP1 r =
      Real.sqrt 2 * Real.log 2 *
          (∫ x : ℝ in 3 / 5..1, (8 / 5 - x) * r x) +
        (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1,
            yoshidaEndpointPotential x * x * r x) -
        fourCellOperatorHalfWidth *
          (∫ x : ℝ in -1..1,
            r x * fourCellOddFiveModeRegularRepresenter 1 0 0 0 0 x) := by
  have hp :
      fourCellOddOneThreeFiveSevenNineLowProfile 1 0 0 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  have hpDiff : ContDiff ℝ 1 centeredP1 := by
    unfold centeredP1
    fun_prop
  have hpOdd : Function.Odd centeredP1 := by
    intro x
    unfold centeredP1
    ring
  have hrawCross : centeredRawLogBilinear centeredP1 r = 0 :=
    centeredRawLogBilinear_centeredP1_tail_eq_zero r hr.continuous hone
  have hraw :=
    fourCellOddRawStripCancellationPolarization_eq_centered_sub_strip
      centeredP1 r hpDiff hr hpOdd hodd
  rw [hrawCross] at hraw
  have hmass := integral_zero_one_centeredP1_mul_eq_zero
    r hr.continuous hodd hone
  have hregular :=
    two_mul_width_mul_regularCorrelation_fiveMode_eq_representer
      r hr.continuous 1 0 0 0 0
  rw [hp] at hregular
  have hrawStrip :=
    fourCellOddEndpointStripOddRawPolarization_P1_eq_four_mul_mass r hr
  have heven :=
    fourCellOddEndpointStripEvenMassBilinear_P1_eq r hr.continuous
  have hstripOdd :=
    fourCellOddEndpointStripOddMassBilinear_P1_eq r hr.continuous
  have hfirst : IntervalIntegrable
      (fun x : ℝ ↦ (4 / 5 : ℝ) * r x) volume (3 / 5) 1 :=
    (hr.continuous.const_mul (4 / 5 : ℝ)).intervalIntegrable _ _
  have hsecond : IntervalIntegrable
      (fun x : ℝ ↦ (x - 4 / 5) * r x) volume (3 / 5) 1 :=
    ((continuous_id.sub continuous_const).mul hr.continuous)
      |>.intervalIntegrable _ _
  have hstrip :
      (4 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x) -
          (∫ x : ℝ in 3 / 5..1, (x - 4 / 5) * r x) =
        ∫ x : ℝ in 3 / 5..1, (8 / 5 - x) * r x := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hfirst hsecond]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [fourCellOddCoreLocalBilinear_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointBilinear
    fourCellOddSignedMassRegularBilinear
  rw [hraw, hrawStrip, hmass, hregular]
  simp only [mul_zero, zero_add]
  unfold fourCellOddRetainedPrimePotentialBilinear
  rw [heven, hstripOdd]
  unfold centeredP1
  calc
    _ = Real.sqrt 2 * Real.log 2 *
          ((4 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x) -
            ∫ x : ℝ in 3 / 5..1, (x - 4 / 5) * r x) +
        (93 / 50 : ℝ) *
          (∫ x : ℝ in 0..1,
            yoshidaEndpointPotential x * x * r x) -
        fourCellOperatorHalfWidth *
          (∫ x : ℝ in -1..1,
            r x * fourCellOddFiveModeRegularRepresenter 1 0 0 0 0 x) := by
      ring
    _ = _ := by rw [hstrip]

/-- The exact scalar density retained by the strongest currently available
`P₁`-orthogonal coercivity theorem. -/
def fourCellOddP1ExactTailWeight (w : ℝ → ℝ) : ℝ :=
  (27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5, w x ^ 2) +
    (93 / 50 : ℝ) *
      (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * w x ^ 2) +
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2 / x) -
    (57 / 25 : ℝ) * (∫ x : ℝ in 3 / 5..1, w x ^ 2)

theorem fourCellOddP1ExactTailWeight_le_core
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w = 0) :
    fourCellOddP1ExactTailWeight w ≤ fourCellOddCoreLocalQuadratic w := by
  simpa only [fourCellOddP1ExactTailWeight, fourCellOddCoreLocalQuadratic]
    using rawPrimeExactPotentialTailWeight_le_core_add_localWidthDefect_of_P1
      w hw hodd hone

private theorem integral_zero_three_fifths_centeredP3_sq :
    (∫ x : ℝ in 0..3 / 5, centeredP3 x ^ 2) =
      (1539 / 21875 : ℝ) := by
  unfold centeredP3
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))]
  norm_num

private theorem integral_three_fifths_one_centeredP3_sq :
    (∫ x : ℝ in 3 / 5..1, centeredP3 x ^ 2) =
      (1586 / 21875 : ℝ) := by
  unfold centeredP3
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  norm_num

private theorem integral_three_fifths_one_centeredP3_sq_div_x :
    (∫ x : ℝ in 3 / 5..1, centeredP3 x ^ 2 / x) =
      (152 / 1875 : ℝ) := by
  rw [show (fun x : ℝ ↦ centeredP3 x ^ 2 / x) =
      fun x ↦ (25 / 4 : ℝ) * x ^ 5 - (15 / 2 : ℝ) * x ^ 3 +
        (9 / 4 : ℝ) * x by
    funext x
    by_cases hzero : x = 0
    · simp [hzero, centeredP3]
    · unfold centeredP3
      field_simp [hzero]
      ring]
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_id]
  norm_num

private theorem fourCellOddP1ExactTailWeight_centeredP3_lt :
    fourCellOddP1ExactTailWeight centeredP3 < (13 / 100 : ℝ) := by
  have hpotential := integral_zero_one_endpointPotential_oddStructuralLow 0 1
  have hlog := strict_log_two_bounds.1
  unfold factorTwoOddStructuralLowProfile at hpotential
  simp only [zero_mul, zero_add, one_mul] at hpotential
  unfold fourCellOddP1ExactTailWeight
  rw [integral_zero_three_fifths_centeredP3_sq,
    integral_three_fifths_one_centeredP3_sq,
    integral_three_fifths_one_centeredP3_sq_div_x,
    hpotential]
  nlinarith

private theorem fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11 :
    fourCellOddCoreLocalQuadratic centeredP1 =
      fourCellOddOneThreeFivePerturbed11 := by
  have hdiag :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq 1 0 0
  have hpert := fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed 1 0 0
  have hp : fourCellOddOneThreeFiveLowProfile 1 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [hp] at hdiag
  unfold fourCellOddCoreLocalQuadratic
  rw [hdiag, hpert]
  unfold fourCellOddOneThreeFivePerturbedQuadratic
  ring

private theorem fourCellOddCoreLocalQuadratic_centeredP3_eq_perturbed33 :
    fourCellOddCoreLocalQuadratic centeredP3 =
      fourCellOddOneThreeFivePerturbed33 := by
  have hdiag :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq 0 1 0
  have hpert := fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed 0 1 0
  have hp : fourCellOddOneThreeFiveLowProfile 0 1 0 = centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [hp] at hdiag
  unfold fourCellOddCoreLocalQuadratic
  rw [hdiag, hpert]
  unfold fourCellOddOneThreeFivePerturbedQuadratic
  ring

private theorem fourCellOddCoreLocalBilinear_P1_P3_eq_perturbed13 :
    fourCellOddCoreLocalBilinear centeredP1 centeredP3 =
      fourCellOddOneThreeFivePerturbed13 := by
  have hdiag :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq 1 1 0
  have hpert := fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed 1 1 0
  have hp : fourCellOddOneThreeFiveLowProfile 1 1 0 =
      centeredP1 + centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [hp] at hdiag
  have hadd := fourCellOddCoreLocalQuadratic_add centeredP1 centeredP3
    (by unfold centeredP1; fun_prop) (by unfold centeredP3; fun_prop)
  have hP1 :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq 1 0 0
  have hP1pert :=
    fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed 1 0 0
  have hp1 : fourCellOddOneThreeFiveLowProfile 1 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [hp1, hP1pert] at hP1
  have hP3 :=
    fourCellOddHalfCoreReserve_add_localWidthDefect_oneThreeFive_eq 0 1 0
  have hP3pert :=
    fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed 0 1 0
  have hp3 : fourCellOddOneThreeFiveLowProfile 0 1 0 = centeredP3 := by
    funext x
    unfold fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [hp3, hP3pert] at hP3
  unfold fourCellOddCoreLocalQuadratic at hadd
  rw [hdiag, hpert, hP1, hP3] at hadd
  unfold fourCellOddOneThreeFivePerturbedQuadratic at hadd
  nlinarith

/-- The `P₃` test direction satisfies the genuine complete-form Schur
inequality.  Thus it obstructs only the scalar-density surrogate below,
not `FourCellOddP1OrthogonalFormDualBound` itself. -/
theorem fourCellOddCoreLocalBilinear_P1_P3_sq_le_mul :
    fourCellOddCoreLocalBilinear centeredP1 centeredP3 ^ 2 ≤
      fourCellOddCoreLocalQuadratic centeredP1 *
        fourCellOddCoreLocalQuadratic centeredP3 := by
  rw [fourCellOddCoreLocalBilinear_P1_P3_eq_perturbed13,
    fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11,
    fourCellOddCoreLocalQuadratic_centeredP3_eq_perturbed33]
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨h11lo, _h11hi, _h13lo, h13hi, h33lo, _⟩
  nlinarith

/-- `P₃` is an exact counterdirection to closing the `P₁` row by the
scalar density alone.  The complete quadratic contains indispensable
coupled raw/prime information discarded by that density. -/
theorem not_fourCellOddP1ExactTailWeight_dual :
    ¬ (∀ (v : ℝ → ℝ),
      ContDiff ℝ 1 v → Function.Odd v →
      centeredOddP1Coefficient v = 0 →
      fourCellOddCoreLocalBilinear centeredP1 v ^ 2 ≤
        fourCellOddCoreLocalQuadratic centeredP1 *
          fourCellOddP1ExactTailWeight v) := by
  intro hdual
  have hP3diff : ContDiff ℝ 1 centeredP3 := by
    unfold centeredP3
    fun_prop
  have hP3odd : Function.Odd centeredP3 := by
    intro x
    unfold centeredP3
    ring
  have hP3one : centeredOddP1Coefficient centeredP3 = 0 := by
    unfold centeredOddP1Coefficient
    rw [show (fun x : ℝ ↦ centeredP3 x * centeredP1 x) =
        fun x ↦ centeredP1 x * centeredP3 x by
      funext x
      ring,
      integral_centeredP1_mul_p3]
    ring
  have h := hdual centeredP3 hP3diff hP3odd hP3one
  rw [fourCellOddCoreLocalBilinear_P1_P3_eq_perturbed13,
    fourCellOddCoreLocalQuadratic_centeredP1_eq_perturbed11] at h
  rcases fourCellOddOneThreeFivePerturbed_entry_bounds with
    ⟨h11lo, h11hi, h13lo, h13hi, _⟩
  have hweight := fourCellOddP1ExactTailWeight_centeredP3_lt
  have hweight0 : 0 ≤ fourCellOddP1ExactTailWeight centeredP3 := by
    have hpotential := integral_zero_one_endpointPotential_oddStructuralLow 0 1
    unfold factorTwoOddStructuralLowProfile at hpotential
    simp only [zero_mul, zero_add, one_mul] at hpotential
    unfold fourCellOddP1ExactTailWeight
    rw [integral_zero_three_fifths_centeredP3_sq,
      integral_three_fifths_one_centeredP3_sq,
      integral_three_fifths_one_centeredP3_sq_div_x,
      hpotential]
    nlinarith [strict_log_two_bounds.2]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
