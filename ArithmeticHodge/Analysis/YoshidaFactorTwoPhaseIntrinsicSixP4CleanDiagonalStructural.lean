import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointRegularCorrelation
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

/-!
# Structural clean diagonal for the intrinsic `P4` mode

The even moments of the exact autocorrelation vanish through degree six.
The three surviving odd moments therefore evaluate the regular-kernel
degree-six model exactly.  The single uniform kernel remainder is controlled
by the sharp autocorrelation `L1` energy inequality.
-/

/-- The three odd moments left after the even degree-six orthogonality of the
`P4` autocorrelation. -/
theorem factorTwoIntrinsicP4Correlation44_odd_moments :
    (∫ t : ℝ in 0..2, t * factorTwoIntrinsicP4Correlation44 t) =
        (-4 / 693 : ℝ) ∧
      (∫ t : ℝ in 0..2, t ^ 3 * factorTwoIntrinsicP4Correlation44 t) =
        (8 / 5005 : ℝ) ∧
      (∫ t : ℝ in 0..2, t ^ 5 * factorTwoIntrinsicP4Correlation44 t) =
        (-64 / 27027 : ℝ) := by
  constructor
  · unfold factorTwoIntrinsicP4Correlation44
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [integral_pow]
    norm_num
  · constructor
    · unfold factorTwoIntrinsicP4Correlation44
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · unfold factorTwoIntrinsicP4Correlation44
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num

/-- The degree-six regular-kernel model against `P4` is an exact positive
odd-power polynomial in the endpoint scale. -/
theorem integral_regularKernelPolynomial6_mul_p4Correlation44 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        factorTwoIntrinsicP4Correlation44 t) =
      yoshidaEndpointA / 4158 + yoshidaEndpointA ^ 3 / 514800 +
        31 * yoshidaEndpointA ^ 5 / 408648240 := by
  unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP4Correlation44
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  rw [show (fun x : ℝ ↦ yoshidaEndpointA * x) =
      fun x ↦ yoshidaEndpointA * x ^ 1 by
    funext x
    ring,
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem p4RegularEnvelope_pointwise
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ yoshidaRegularKernel (yoshidaEndpointA * t) -
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) ∧
      yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) <
        (1 / 500000 : ℝ) := by
  apply yoshidaRegularKernelPolynomial6_envelope
  · exact mul_nonneg yoshidaEndpointA_pos.le ht.1
  · rw [show Real.log 2 = 2 * yoshidaEndpointA by
      unfold yoshidaEndpointA
      ring]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left ht.2 yoshidaEndpointA_pos.le)

private theorem measurable_yoshidaRegularKernel_p4 :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem intervalIntegrable_p4RegularEnvelope :
    IntervalIntegrable
      (fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
            factorTwoIntrinsicP4Correlation44 t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (yoshidaEndpointA * t) -
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
        factorTwoIntrinsicP4Correlation44 t
  let g : ℝ → ℝ := fun t ↦
    (1 / 500000 : ℝ) * |factorTwoIntrinsicP4Correlation44 t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul
      continuous_factorTwoIntrinsicP4Correlation44.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_yoshidaRegularKernel_p4.comp
      (measurable_const.mul measurable_id)).sub
        (by unfold yoshidaRegularKernelPolynomial6; fun_prop)).mul
          continuous_factorTwoIntrinsicP4Correlation44.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have henv := p4RegularEnvelope_pointwise
      (⟨ht.1.le, ht.2⟩ : t ∈ Icc (0 : ℝ) 2)
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le
      (abs_nonneg (factorTwoIntrinsicP4Correlation44 t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- Exact sixth-order model plus its one global analytic error for the `P4`
regular quadratic. -/
theorem re_yoshidaEndpointRegularQuadratic_p4_eq :
    (yoshidaEndpointRegularQuadratic
      (fun x ↦ (factorTwoCenteredP4 x : ℂ))).re =
      yoshidaEndpointA / 4158 + yoshidaEndpointA ^ 3 / 514800 +
        31 * yoshidaEndpointA ^ 5 / 408648240 +
          oddCleanRegularEnvelopeError factorTwoIntrinsicP4Correlation44 := by
  rw [re_yoshidaEndpointRegularQuadratic_eq_correlation _
    continuous_factorTwoCenteredP4]
  simp_rw [centeredEndpointCorrelation_p4]
  have hpolyContinuous : Continuous (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        factorTwoIntrinsicP4Correlation44 t) := by
    apply Continuous.mul
    · unfold yoshidaRegularKernelPolynomial6
      fun_prop
    · exact continuous_factorTwoIntrinsicP4Correlation44
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
          factorTwoIntrinsicP4Correlation44 t) volume 0 2 :=
    hpolyContinuous.intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (yoshidaEndpointA * t) *
        factorTwoIntrinsicP4Correlation44 t) =
      fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
            factorTwoIntrinsicP4Correlation44 t +
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
          factorTwoIntrinsicP4Correlation44 t by
      funext t
      ring,
    intervalIntegral.integral_add intervalIntegrable_p4RegularEnvelope hpoly]
  have hmodel := integral_regularKernelPolynomial6_mul_p4Correlation44
  unfold oddCleanRegularEnvelopeError
  nlinarith

private theorem abs_p4RegularEnvelopeError_le :
    |oddCleanRegularEnvelopeError factorTwoIntrinsicP4Correlation44| ≤
      (1 / 1125000 : ℝ) := by
  have herr := abs_oddCleanRegularEnvelopeError_le
    factorTwoIntrinsicP4Correlation44
      continuous_factorTwoIntrinsicP4Correlation44
  have hL1 := integral_abs_centeredEndpointCorrelation_le_energy
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  simp_rw [centeredEndpointCorrelation_p4] at hL1
  rw [integral_factorTwoCenteredP4_sq] at hL1
  nlinarith

/-- The exact `P4` regular loss is two orders of magnitude smaller than the
generic mean-zero Schur bound. -/
theorem endpointA_mul_re_yoshidaEndpointRegularQuadratic_p4_lt :
    yoshidaEndpointA *
        (yoshidaEndpointRegularQuadratic
          (fun x ↦ (factorTwoCenteredP4 x : ℂ))).re <
      (3 / 100000 : ℝ) := by
  let R : ℝ :=
    (yoshidaEndpointRegularQuadratic
      (fun x ↦ (factorTwoCenteredP4 x : ℂ))).re
  let e : ℝ := oddCleanRegularEnvelopeError
    factorTwoIntrinsicP4Correlation44
  have hA0 : 0 < yoshidaEndpointA := yoshidaEndpointA_pos
  have hAlower : (6931 / 20000 : ℝ) < yoshidaEndpointA := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.1]
  have hAupper : yoshidaEndpointA < (347 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.2]
  have hA3 := pow_lt_pow_left₀ hAupper hA0.le
    (by norm_num : (3 : ℕ) ≠ 0)
  have hA5 := pow_lt_pow_left₀ hAupper hA0.le
    (by norm_num : (5 : ℕ) ≠ 0)
  have he := abs_p4RegularEnvelopeError_le
  have heLower : -(1 / 1125000 : ℝ) ≤ e := by
    simpa only [e] using neg_le_of_abs_le he
  have heUpper : e ≤ (1 / 1125000 : ℝ) := by
    simpa only [e] using le_of_abs_le he
  have hReq : R = yoshidaEndpointA / 4158 +
      yoshidaEndpointA ^ 3 / 514800 +
      31 * yoshidaEndpointA ^ 5 / 408648240 + e := by
    simpa only [R, e] using re_yoshidaEndpointRegularQuadratic_p4_eq
  have hR0 : 0 < R := by
    have hA3nonneg : 0 ≤ yoshidaEndpointA ^ 3 := by positivity
    have hA5nonneg : 0 ≤ yoshidaEndpointA ^ 5 := by positivity
    norm_num at hAlower heLower ⊢
    nlinarith [hReq]
  have hRupper : R < (8645 / 100000000 : ℝ) := by
    norm_num at hA3 hA5 heUpper ⊢
    nlinarith [hReq]
  calc
    yoshidaEndpointA * R <
        yoshidaEndpointA * (8645 / 100000000 : ℝ) :=
      mul_lt_mul_of_pos_left hRupper hA0
    _ < (347 / 1000 : ℝ) * (8645 / 100000000 : ℝ) :=
      mul_lt_mul_of_pos_right hAupper (by norm_num)
    _ < (3 / 100000 : ℝ) := by norm_num

/-- Exact potential mass and the structural degree-six regular estimate lift
the clean `P4` diagonal to the reserve needed by the endpoint Schur gate. -/
theorem one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4 :
    (1571 / 5000 : ℝ) <
      yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 := by
  have hraw := factorTwoCenteredP4_raw_reserve
  have hpotential := integral_endpointPotential_mul_factorTwoCenteredP4_sq
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hregular := endpointA_mul_re_yoshidaEndpointRegularQuadratic_p4_lt
  have hhyper := yoshidaEndpointHyperbolicQuadratic_nonneg_of_even
    factorTwoCenteredP4 even_factorTwoCenteredP4
  have hlog := strict_log_two_bounds.2
  unfold factorTwoIntrinsicEnergy at hraw
  rw [integral_factorTwoCenteredP4_sq] at hraw
  unfold yoshidaEndpointOddCleanQuadratic
  rw [integral_factorTwoCenteredP4_sq]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
