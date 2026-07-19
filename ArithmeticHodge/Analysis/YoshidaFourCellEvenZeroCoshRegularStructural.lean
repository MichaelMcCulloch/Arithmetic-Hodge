import ArithmeticHodge.Analysis.YoshidaFourCellEvenPolarSchurStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelLowerStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshRegularStructural

noncomputable section

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRegularKernelLowerStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound

/-!
# The wide regular row on the even zero-cosh hyperplane

The four-cell regular kernel differs from the constant `1 / 5` by at most
`1 / 20` on the whole lag range.  On an even profile the constant part is the
square of the ordinary mean.  Vanishing of the wider positive cosh moment
already forces that mean to carry at most `1 / 1000` of the full mass, so the
complete regular correlation costs only `501 / 10000` of the mass.
-/

private theorem intervalIntegrable_fourCellRegularKernel_mul_continuous
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 4 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact (measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1.le
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 (by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring)
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_right hk1 (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- On the zero-wide-cosh slice, the complete wide regular correlation is at
most `501 / 10000` of the full centered mass.  The proof keeps the signed
constant autocorrelation exactly and bounds only the `1 / 20` kernel
oscillation by its sharp `L¹` energy budget. -/
theorem fourCellRegularCorrelation_le_fiveHundredOne_div_tenThousand_mass_of_coshMoment_zero
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation w t) ≤
      (501 / 10000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  let δ : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) - 1 / 5
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous w hw
  have hCint : IntervalIntegrable C volume 0 2 :=
    hC.intervalIntegrable _ _
  have hKC := intervalIntegrable_fourCellRegularKernel_mul_continuous C hC
  have hconst : IntervalIntegrable (fun t : ℝ ↦ (1 / 5 : ℝ) * C t)
      volume 0 2 := hCint.const_mul (1 / 5)
  have hδC : IntervalIntegrable (fun t : ℝ ↦ δ t * C t)
      volume 0 2 := by
    apply hKC.sub hconst |>.congr
    intro t _ht
    dsimp only [δ]
    ring
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2,
      |δ t * C t| ≤ (1 / 20 : ℝ) * |C t| := by
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    have harg4 : fourCellOperatorHalfWidth * t ≤
        5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk0 := one_fifth_le_yoshidaRegularKernel_fourCellRange harg0 harg4
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    have hδ0 : 0 ≤ δ t := by dsimp only [δ]; linarith
    have hδ1 : δ t ≤ (1 / 20 : ℝ) := by dsimp only [δ]; linarith
    rw [abs_mul, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_right hδ1 (abs_nonneg _)
  have habsInt : IntervalIntegrable (fun t : ℝ ↦ |δ t * C t|)
      volume 0 2 := hδC.abs
  have hmajorInt : IntervalIntegrable (fun t : ℝ ↦
      (1 / 20 : ℝ) * |C t|) volume 0 2 :=
    (hC.abs.intervalIntegrable _ _).const_mul (1 / 20)
  have hmono :
      (∫ t : ℝ in 0..2, |δ t * C t|) ≤
        ∫ t : ℝ in 0..2, (1 / 20 : ℝ) * |C t| := by
    apply intervalIntegral.integral_mono_on (by norm_num) habsInt hmajorInt
    exact hpoint
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (by norm_num : (0 : ℝ) ≤ 2) (f := fun t ↦ δ t * C t)
      (μ := volume)
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy w hw
  rw [intervalIntegral.integral_const_mul] at hmono
  simp only [Real.norm_eq_abs] at hnorm
  have hδUpper : (∫ t : ℝ in 0..2, δ t * C t) ≤
      (1 / 20 : ℝ) * M := by
    have hleabs := le_abs_self (∫ t : ℝ in 0..2, δ t * C t)
    dsimp only [C] at hmono
    dsimp only [C, M] at hcorr ⊢
    linarith
  have hmeanIdentity :=
    two_mul_integral_cosh_mul_centeredCorrelation_of_even w hw heven 0
  have hmean : 2 * (∫ t : ℝ in 0..2, C t) =
      (∫ x : ℝ in -1..1, w x) ^ 2 := by
    simpa [C, centeredCoshMoment] using hmeanIdentity
  have hcoeff :=
    centeredEvenP0Coefficient_sq_le_one_div_fourThousand_mass_of_coshMoment_zero
      w hw heven hzero
  have hmeanSq : (∫ x : ℝ in -1..1, w x) ^ 2 ≤
      (1 / 1000 : ℝ) * M := by
    unfold centeredEvenP0Coefficient at hcoeff
    dsimp only [M]
    nlinarith
  have hmeanUpper : (1 / 5 : ℝ) * (∫ t : ℝ in 0..2, C t) ≤
      (1 / 10000 : ℝ) * M := by
    nlinarith
  have hrewrite :
      (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) =
        (∫ t : ℝ in 0..2, δ t * C t) +
          (1 / 5 : ℝ) * (∫ t : ℝ in 0..2, C t) := by
    rw [show (fun t : ℝ ↦
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) =
      fun t ↦ δ t * C t + (1 / 5 : ℝ) * C t by
      funext t
      dsimp only [δ]
      ring,
      intervalIntegral.integral_add hδC hconst,
      intervalIntegral.integral_const_mul]
  change (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) * C t) ≤
    (501 / 10000 : ℝ) * M
  rw [hrewrite]
  linarith

/-- Multiplying by the complete four-cell width costs less than
`87 / 2000` of the mass.  This is the precise smooth-kernel loss used by the
polar-free coercivity problem. -/
theorem two_mul_fourCellWidth_mul_regularCorrelation_le_eightySeven_div_twoThousand_mass_of_coshMoment_zero
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t) ≤
      (87 / 2000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hI : I ≤ (501 / 10000 : ℝ) * M := by
    simpa only [I, M] using
      fourCellRegularCorrelation_le_fiveHundredOne_div_tenThousand_mass_of_coshMoment_zero
        w hw heven hzero
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hwidth0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hwidth : 2 * fourCellOperatorHalfWidth < (1733 / 2000 : ℝ) := by
    have hlog := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hI hwidth0
  have hmassScaled : 0 ≤ (501 / 10000 : ℝ) * M :=
    mul_nonneg (by norm_num) hM
  have hwidthScaled := mul_le_mul_of_nonneg_right hwidth.le hmassScaled
  have hconstant :
      (1733 / 2000 : ℝ) * (501 / 10000) ≤ 87 / 2000 := by
    norm_num
  have hconstantScaled := mul_le_mul_of_nonneg_right hconstant hM
  calc
    2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) ≤
        2 * fourCellOperatorHalfWidth *
          ((501 / 10000 : ℝ) *
            (∫ x : ℝ in -1..1, w x ^ 2)) := hscaled
    _ ≤ (1733 / 2000 : ℝ) *
          ((501 / 10000 : ℝ) *
            (∫ x : ℝ in -1..1, w x ^ 2)) := hwidthScaled
    _ ≤ (87 / 2000 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) := by
      simpa only [mul_assoc] using hconstantScaled

/-- The singular, endpoint-potential, and retained prime channels before the
scalar and smooth-kernel losses.  These three terms must be estimated as one
coupled form; consuming the raw energy in a separate prime bound is too
lossy. -/
def fourCellEvenZeroCoshCoupledCore (w : ℝ → ℝ) : ℝ :=
  centeredRawLogEnergy w / 4 +
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w

private theorem log_five_four_lt_4463_div_20000 :
    Real.log (5 / 4 : ℝ) < 4463 / 20000 := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCellScalar_lt_31577_div_20000 :
    Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi <
      (31577 / 20000 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  rw [hwidth]
  linarith [log_five_four_lt_4463_div_20000,
    strict_log_log_two_bounds.2, strict_euler_gamma_bounds.2,
    strict_log_pi_bounds.2]

/-- Exact zero-cosh normal form for the polar-free operator. -/
theorem fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0) :
    fourCellEvenPolarFreeOperator w =
      fourCellEvenZeroCoshCoupledCore w -
        (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) *
          (∫ x : ℝ in -1..1, w x ^ 2) -
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation w t) := by
  have hbracket := fourCell_evenBracket_eq_polarFree_add_coshRank
    w hw hlocal heven
  rw [hzero] at hbracket
  norm_num at hbracket
  rw [← hbracket]
  unfold centeredClippedPhysicalQuadratic
    fourCellEvenZeroCoshCoupledCore
  rw [physicalPolarProduct_eq_positiveCoshSquare_of_even
    w hw heven fourCellOperatorHalfWidth, hzero]
  ring

/-- A single structural lower bound of `33 / 20` for the coupled core closes
the complete zero-cosh polar-free tail.  The rational target retains a strict
margin after the exact scalar and regular losses. -/
theorem fourCellEvenPolarFreeOperator_nonnegative_of_coupledCore
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hzero : fourCellPositiveCoshMoment w
      (fourCellOperatorHalfWidth / 2) = 0)
    (hcore : (33 / 20 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore w) :
    0 ≤ fourCellEvenPolarFreeOperator w := by
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let S : ℝ := Real.log (2 * fourCellOperatorHalfWidth) +
    Real.eulerMascheroniConstant + Real.log Real.pi
  let I : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation w t
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hscalar : S * M ≤ (31577 / 20000 : ℝ) * M := by
    exact mul_le_mul_of_nonneg_right fourCellScalar_lt_31577_div_20000.le hM
  have hregular : 2 * fourCellOperatorHalfWidth * I ≤
      (87 / 2000 : ℝ) * M := by
    simpa only [I, M] using
      two_mul_fourCellWidth_mul_regularCorrelation_le_eightySeven_div_twoThousand_mass_of_coshMoment_zero
        w hw heven hzero
  have hnormal :=
    fourCellEvenPolarFreeOperator_eq_coupledCore_sub_scalar_sub_regular
      w hw hlocal heven hzero
  dsimp only [S, I, M] at hscalar hregular hcore hnormal ⊢
  rw [hnormal]
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshRegularStructural
