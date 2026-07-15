import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural

noncomputable section

open CenteredOddOneThreeEnergy
open CenteredEndpointCorrelation
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointRegularCorrelation
open YoshidaRegularKernelBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseLegendreFourFiveStructural

/-!
# Structural clean `P1/P3`--`P5` crosses

The singular potential part is evaluated exactly from four even logarithmic
moments.  Its logarithmic terms cancel by Legendre orthogonality.  The
remaining regular and hyperbolic crosses are treated by global analytic
envelopes below; no interval subdivision or finite certificate is used.
-/

private theorem measurable_yoshidaRegularKernel_local :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

/-- The regular kernel paired with any continuous correlation is integrable
on the complete overlap interval. -/
private theorem intervalIntegrable_regularKernel_mul
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦ yoshidaRegularKernel (yoshidaEndpointA * t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (yoshidaEndpointA * t) * C t
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
    exact (measurable_yoshidaRegularKernel_local.comp
      (measurable_const.mul measurable_id)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have harg0 : 0 ≤ yoshidaEndpointA * t :=
      mul_nonneg yoshidaEndpointA_pos.le htIcc.1
    have harg2 : yoshidaEndpointA * t ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left htIcc.2
        (by positivity : 0 ≤ Real.log 2 / 2)]
    have hK := yoshidaRegularKernel_mem_Icc harg0 harg2
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK.1]
    exact mul_le_mul_of_nonneg_right hK.2 (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

/-- Polarizing the regular quadratic turns its symmetric cross exactly into
the symmetric overlap correlation. -/
theorem re_yoshidaEndpointRegularRealBilinear_add_eq_correlation
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    (yoshidaEndpointRegularRealBilinear u v +
        yoshidaEndpointRegularRealBilinear v u).re =
      4 * ∫ t : ℝ in 0..2,
        yoshidaRegularKernel (yoshidaEndpointA * t) *
          factorTwoCenteredCorrelationBilinear u v t := by
  have hCu : Continuous (centeredEndpointCorrelation u) :=
    continuous_centeredEndpointCorrelation_of_continuous u hu
  have hCv : Continuous (centeredEndpointCorrelation v) :=
    continuous_centeredEndpointCorrelation_of_continuous v hv
  have hB : Continuous (factorTwoCenteredCorrelationBilinear u v) := by
    unfold factorTwoCenteredCorrelationBilinear
    exact ((continuous_factorTwoCenteredCrossCorrelation u v hu hv).add
      (continuous_factorTwoCenteredCrossCorrelation v u hv hu)).div_const 2
  have hIu := intervalIntegrable_regularKernel_mul
    (centeredEndpointCorrelation u) hCu
  have hIv := intervalIntegrable_regularKernel_mul
    (centeredEndpointCorrelation v) hCv
  have hIb := intervalIntegrable_regularKernel_mul
    (factorTwoCenteredCorrelationBilinear u v) hB
  have hsum := re_yoshidaEndpointRegularQuadratic_eq_correlation
    (u + v) (hu.add hv)
  have huq := re_yoshidaEndpointRegularQuadratic_eq_correlation u hu
  have hvq := re_yoshidaEndpointRegularQuadratic_eq_correlation v hv
  have hpolar := congrArg Complex.re
    (yoshidaEndpointRegularQuadratic_add_ofReal u v hu hv)
  simp only [add_re] at hpolar
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (yoshidaEndpointA * t) *
        centeredEndpointCorrelation (u + v) t) =
      fun t ↦
        yoshidaRegularKernel (yoshidaEndpointA * t) *
            centeredEndpointCorrelation u t +
          2 * (yoshidaRegularKernel (yoshidaEndpointA * t) *
            factorTwoCenteredCorrelationBilinear u v t) +
          yoshidaRegularKernel (yoshidaEndpointA * t) *
            centeredEndpointCorrelation v t by
    funext t
    rw [centeredEndpointCorrelation_add u v hu hv t]
    ring,
    intervalIntegral.integral_add (hIu.add (hIb.const_mul 2)) hIv,
    intervalIntegral.integral_add hIu (hIb.const_mul 2),
    intervalIntegral.integral_const_mul] at hsum
  simp only [Pi.add_apply] at hsum
  rw [hsum, huq, hvq] at hpolar
  simp only [add_re]
  linarith

/-- Exact potential part of the clean `P1`--`P5` cross. -/
theorem integral_endpointPotential_mul_centeredP1_mul_P5 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP1 x *
        factorTwoCenteredP5 x) = (1 / 14 : ℝ) := by
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)).congr
    intro x _hx
    ring
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)).congr
    intro x _hx
    ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredP1 x * factorTwoCenteredP5 x) =
      fun x ↦ (63 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) -
        (70 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) +
        (15 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    unfold centeredP1 factorTwoCenteredP5
    ring,
    intervalIntegral.integral_add
      ((h6.const_mul (63 / 8 : ℝ)).sub (h4.const_mul (70 / 8 : ℝ)))
      (h2.const_mul (15 / 8 : ℝ)),
    intervalIntegral.integral_sub
      (h6.const_mul (63 / 8 : ℝ)) (h4.const_mul (70 / 8 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

/-- Exact potential part of the clean `P3`--`P5` cross. -/
theorem integral_endpointPotential_mul_centeredP3_mul_P5 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP3 x *
        factorTwoCenteredP5 x) = (1 / 9 : ℝ) := by
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)).congr
    intro x _hx
    ring
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)).congr
    intro x _hx
    ring
  have h8 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 8) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 4) (continuous_id.pow 4)).congr
    intro x _hx
    ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredP3 x * factorTwoCenteredP5 x) =
      fun x ↦ (315 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) -
        (539 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) +
        (285 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (45 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    unfold centeredP3 factorTwoCenteredP5
    ring,
    intervalIntegral.integral_sub
      (((h8.const_mul (315 / 16 : ℝ)).sub
        (h6.const_mul (539 / 16 : ℝ))).add
          (h4.const_mul (285 / 16 : ℝ)))
      (h2.const_mul (45 / 16 : ℝ)),
    intervalIntegral.integral_add
      ((h8.const_mul (315 / 16 : ℝ)).sub
        (h6.const_mul (539 / 16 : ℝ)))
      (h4.const_mul (285 / 16 : ℝ)),
    intervalIntegral.integral_sub
      (h8.const_mul (315 / 16 : ℝ)) (h6.const_mul (539 / 16 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

/-! ## The single global regular-kernel polynomial -/

/-- Sixth-order regular-kernel model for the `P1`--`P5` cross. -/
def oddP5CleanRegularPolynomial15 : ℝ :=
  yoshidaEndpointA ^ 3 / 712800 +
    31 * yoshidaEndpointA ^ 5 / 90810720 +
      61 * yoshidaEndpointA ^ 6 / 1995840

/-- Sixth-order regular-kernel model for the `P3`--`P5` cross. -/
def oddP5CleanRegularPolynomial35 : ℝ :=
  -yoshidaEndpointA / 8316 - yoshidaEndpointA ^ 3 / 772200 -
    31 * yoshidaEndpointA ^ 5 / 544864320

private def regularKernelCoefficient : ℕ → ℝ
  | 0 => 1 / 4
  | 1 => -1 / 48
  | 2 => -1 / 32
  | 3 => 7 / 11520
  | 4 => 5 / 1536
  | 5 => -31 / 1935360
  | 6 => -61 / 184320
  | _ => 0

private def oddP5Correlation15Coefficient : ℕ → ℝ
  | 0 => 0
  | 1 => -1
  | 2 => 7
  | 3 => -15
  | 4 => 105 / 8
  | 5 => -35 / 8
  | 6 => 0
  | 7 => 3 / 16
  | _ => 0

private def oddP5Correlation35Coefficient : ℕ → ℝ
  | 0 => 0
  | 1 => -1
  | 2 => 9 / 2
  | 3 => -5
  | 4 => 0
  | 5 => 15 / 8
  | 6 => 0
  | 7 => -7 / 16
  | 8 => 0
  | 9 => 5 / 128
  | _ => 0

private theorem integral_double_polynomial_zero_two
    (N M : ℕ) (a : ℕ → ℕ → ℝ) :
    (∫ t : ℝ in 0..2,
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        a i j * t ^ (i + j)) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        a i j * (2 : ℝ) ^ (i + j + 1) / (i + j + 1) := by
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring
    · intro j hj
      exact ((continuous_id.pow (i + j)).const_mul (a i j))
        |>.intervalIntegrable 0 2
  · intro i hi
    apply Continuous.intervalIntegrable
    fun_prop

private theorem regularKernelPolynomial_eq_sum (t : ℝ) :
    yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) =
      ∑ i ∈ Finset.range 7,
        regularKernelCoefficient i * yoshidaEndpointA ^ i * t ^ i := by
  simp [yoshidaRegularKernelPolynomial6, regularKernelCoefficient,
    Finset.sum_range_succ]
  ring

private theorem oddP5Correlation15_eq_sum (t : ℝ) :
    oddP5Correlation15 t =
      ∑ j ∈ Finset.range 8,
        oddP5Correlation15Coefficient j * t ^ j := by
  simp [oddP5Correlation15, oddP5Correlation15Coefficient,
    Finset.sum_range_succ]
  ring

private theorem oddP5Correlation35_eq_sum (t : ℝ) :
    oddP5Correlation35 t =
      ∑ j ∈ Finset.range 10,
        oddP5Correlation35Coefficient j * t ^ j := by
  simp [oddP5Correlation35, oddP5Correlation35Coefficient,
    Finset.sum_range_succ]
  ring

/-- Exact polynomial regular-kernel integral for the `P1`--`P5` cross. -/
theorem integral_regularKernelPolynomial_mul_oddP5Correlation15 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddP5Correlation15 t) = oddP5CleanRegularPolynomial15 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddP5Correlation15 t) =
      fun t ↦ ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 8,
        (regularKernelCoefficient i * oddP5Correlation15Coefficient j *
          yoshidaEndpointA ^ i) * t ^ (i + j) by
    funext t
    rw [regularKernelPolynomial_eq_sum, oddP5Correlation15_eq_sum]
    simp [regularKernelCoefficient, oddP5Correlation15Coefficient,
      Finset.sum_range_succ]
    ring,
    integral_double_polynomial_zero_two]
  norm_num [regularKernelCoefficient, oddP5Correlation15Coefficient,
    oddP5CleanRegularPolynomial15, Finset.sum_range_succ]
  ring

/-- Exact polynomial regular-kernel integral for the `P3`--`P5` cross. -/
theorem integral_regularKernelPolynomial_mul_oddP5Correlation35 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddP5Correlation35 t) = oddP5CleanRegularPolynomial35 := by
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddP5Correlation35 t) =
      fun t ↦ ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 10,
        (regularKernelCoefficient i * oddP5Correlation35Coefficient j *
          yoshidaEndpointA ^ i) * t ^ (i + j) by
    funext t
    rw [regularKernelPolynomial_eq_sum, oddP5Correlation35_eq_sum]
    simp [regularKernelCoefficient, oddP5Correlation35Coefficient,
      Finset.sum_range_succ]
    ring,
    integral_double_polynomial_zero_two]
  norm_num [regularKernelCoefficient, oddP5Correlation35Coefficient,
    oddP5CleanRegularPolynomial35, Finset.sum_range_succ]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
