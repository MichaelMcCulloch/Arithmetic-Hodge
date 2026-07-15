import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural

noncomputable section

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoStructuralConstantBounds
open YoshidaRenormalizedGeometricKernel
open YoshidaRegularKernelBound

/-!
# Structural diagonal perturbation for the intrinsic odd `P5` mode

The `P5-P5` overlap is integrated as one exact autocorrelation polynomial.
Orthogonality kills every even moment seen by the degree-six pole-free
polynomial.  The two endpoint poles are then divided exactly, leaving one
copy of `log 2`; the only approximation is the already established global
pole-free analytic envelope.
-/

/-! ## Exact autocorrelation and its orthogonal moments -/

/-- Exact positive-lag autocorrelation of the centered Legendre `P5` mode. -/
def oddP5Correlation55 (t : ℝ) : ℝ :=
  2 / 11 - t + (5 / 2 : ℝ) * t ^ 3 - (21 / 8 : ℝ) * t ^ 5 +
    (5 / 4 : ℝ) * t ^ 7 - (35 / 128 : ℝ) * t ^ 9 +
    (63 / 2816 : ℝ) * t ^ 11

private theorem integral_polynomial_ten
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 + (a₈ * x ^ 8 +
            (a₉ * x ^ 9 + a₁₀ * x ^ 10)))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem centeredEndpointCorrelation_p5 (t : ℝ) :
    centeredEndpointCorrelation factorTwoCenteredP5 t =
      oddP5Correlation55 t := by
  unfold CenteredEndpointCorrelation.centeredEndpointCorrelation
    factorTwoCenteredP5
  rw [show (fun x : ℝ ↦
      ((63 * (t + x) ^ 5 - 70 * (t + x) ^ 3 + 15 * (t + x)) / 8) *
        ((63 * x ^ 5 - 70 * x ^ 3 + 15 * x) / 8)) =
      fun x ↦ 0 * x ^ 0 +
        (((15 * t * (63 * t ^ 4 - 70 * t ^ 2 + 15) / 64 : ℝ)) * x ^ 1 +
          (((225 * (21 * t ^ 4 - 14 * t ^ 2 + 1) / 64 : ℝ)) * x ^ 2 +
            ((-35 * t * (63 * t ^ 4 - 205 * t ^ 2 + 60) / 32 : ℝ) * x ^ 3 +
              ((-525 * (t - 1) * (t + 1) * (21 * t ^ 2 - 2) / 32 : ℝ) * x ^ 4 +
                ((21 * t * (189 * t ^ 4 - 2310 * t ^ 2 + 970) / 64 : ℝ) * x ^ 5 +
                  ((35 * (567 * t ^ 4 - 1638 * t ^ 2 + 194) / 64 : ℝ) * x ^ 6 +
                    ((2205 * t * (9 * t ^ 2 - 8) / 32 : ℝ) * x ^ 7 +
                      ((2205 * (9 * t ^ 2 - 2) / 32 : ℝ) * x ^ 8 +
                        ((19845 * t / 64 : ℝ) * x ^ 9 +
                          (3969 / 64 : ℝ) * x ^ 10))))))))) by
      funext x
      ring,
    integral_polynomial_ten]
  unfold oddP5Correlation55
  ring

theorem continuous_oddP5Correlation55 :
    Continuous oddP5Correlation55 := by
  unfold oddP5Correlation55
  fun_prop

theorem oddP5Correlation55_even_moments :
    (∫ t : ℝ in 0..2, oddP5Correlation55 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * oddP5Correlation55 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * oddP5Correlation55 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * oddP5Correlation55 t) = 0 := by
  constructor
  · unfold oddP5Correlation55
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [integral_pow]
    norm_num
  · constructor
    · unfold oddP5Correlation55
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold oddP5Correlation55
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold oddP5Correlation55
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

theorem integral_abs_oddP5Correlation55_le :
    (∫ t : ℝ in 0..2, |oddP5Correlation55 t|) ≤ 2 / 11 := by
  have h := integral_abs_centeredEndpointCorrelation_le_energy
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
  simp_rw [centeredEndpointCorrelation_p5] at h
  rw [integral_factorTwoCenteredP5_sq] at h
  exact h

theorem abs_poleFreeAnalyticError_oddP5Correlation55_le :
    |poleFreeAnalyticError oddP5Correlation55| ≤ 3 / 44000 := by
  have herr := abs_poleFreeAnalyticError_le oddP5Correlation55
    continuous_oddP5Correlation55
  have hcorr := integral_abs_oddP5Correlation55_le
  calc
    |poleFreeAnalyticError oddP5Correlation55| ≤
        (3 / 8000 : ℝ) * (∫ t : ℝ in 0..2, |oddP5Correlation55 t|) := herr
    _ ≤ (3 / 8000 : ℝ) * (2 / 11) :=
      mul_le_mul_of_nonneg_left hcorr (by norm_num)
    _ = 3 / 44000 := by norm_num

theorem integral_polynomialDifference_mul_oddP5Correlation55 :
    (∫ t : ℝ in 0..2,
      poleFreePolynomialDifference t * oddP5Correlation55 t) = 0 := by
  have h₀ : IntervalIntegrable oddP5Correlation55 volume 0 2 :=
    continuous_oddP5Correlation55.intervalIntegrable 0 2
  have h₂ : IntervalIntegrable
      (fun t : ℝ ↦ t ^ 2 * oddP5Correlation55 t) volume 0 2 :=
    ((continuous_id.pow 2).mul continuous_oddP5Correlation55)
      |>.intervalIntegrable 0 2
  have h₄ : IntervalIntegrable
      (fun t : ℝ ↦ t ^ 4 * oddP5Correlation55 t) volume 0 2 :=
    ((continuous_id.pow 4).mul continuous_oddP5Correlation55)
      |>.intervalIntegrable 0 2
  have h₆ : IntervalIntegrable
      (fun t : ℝ ↦ t ^ 6 * oddP5Correlation55 t) volume 0 2 :=
    ((continuous_id.pow 6).mul continuous_oddP5Correlation55)
      |>.intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      poleFreePolynomialDifference t * oddP5Correlation55 t) = fun t ↦
        ((polynomialD0 * oddP5Correlation55 t +
          polynomialD2 * (t ^ 2 * oddP5Correlation55 t)) +
          polynomialD4 * (t ^ 4 * oddP5Correlation55 t)) +
          polynomialD6 * (t ^ 6 * oddP5Correlation55 t) by
      funext t
      rw [poleFreePolynomialDifference_expansion]
      ring,
    intervalIntegral.integral_add
      (((h₀.const_mul polynomialD0).add (h₂.const_mul polynomialD2)).add
        (h₄.const_mul polynomialD4)) (h₆.const_mul polynomialD6),
    intervalIntegral.integral_add
      ((h₀.const_mul polynomialD0).add (h₂.const_mul polynomialD2))
      (h₄.const_mul polynomialD4),
    intervalIntegral.integral_add
      (h₀.const_mul polynomialD0) (h₂.const_mul polynomialD2)]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [oddP5Correlation55_even_moments.1,
    oddP5Correlation55_even_moments.2.1,
    oddP5Correlation55_even_moments.2.2.1,
    oddP5Correlation55_even_moments.2.2.2]
  ring

theorem integral_regularQuadratic_mul_oddP5Correlation55 :
    (∫ t : ℝ in 0..2,
      oddStructuralRegularQuadratic t * oddP5Correlation55 t) = 0 := by
  have h₀ : IntervalIntegrable oddP5Correlation55 volume 0 2 :=
    continuous_oddP5Correlation55.intervalIntegrable 0 2
  have h₂ : IntervalIntegrable
      (fun t : ℝ ↦ t ^ 2 * oddP5Correlation55 t) volume 0 2 :=
    ((continuous_id.pow 2).mul continuous_oddP5Correlation55)
      |>.intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      oddStructuralRegularQuadratic t * oddP5Correlation55 t) = fun t ↦
        (79 / 60 : ℝ) * oddP5Correlation55 t +
          (3 / 125 : ℝ) * (t ^ 2 * oddP5Correlation55 t) by
      funext t
      unfold oddStructuralRegularQuadratic
      ring,
    intervalIntegral.integral_add
      (h₀.const_mul (79 / 60 : ℝ)) (h₂.const_mul (3 / 125 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [oddP5Correlation55_even_moments.1,
    oddP5Correlation55_even_moments.2.1]
  ring

theorem oddStructuralRegularError_oddP5Correlation55_sharp_expansion :
    oddStructuralRegularError oddP5Correlation55 =
      poleFreeAnalyticError oddP5Correlation55 := by
  have hsplit := evenStructuralRegularError_eq_analytic_add_polynomial
    oddP5Correlation55 continuous_oddP5Correlation55
  rw [evenStructuralRegularError,
    integral_polynomialDifference_mul_oddP5Correlation55] at hsplit
  simpa using hsplit

/-! ## Exact endpoint-pole moment -/

private theorem integral_inv_two_add_local :
    (∫ t : ℝ in 0..2, 1 / (2 + t)) = Real.log 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log (2 + t)
  have hderiv (t : ℝ) (ht : 2 + t ≠ 0) :
      HasDerivAt F (1 / (2 + t)) t := by
    have hadd : HasDerivAt (fun x : ℝ ↦ 2 + x) 1 t := by
      simpa using (hasDerivAt_const t 2).add (hasDerivAt_id t)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log ht).comp t hadd
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (2 + t))
      (uIcc (0 : ℝ) 2) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hderiv t (by
      have ht' : t ∈ Icc (0 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      linarith [ht'.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring]
  ring

private theorem intervalIntegrable_inv_two_add_local :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

private theorem intervalIntegrable_poleWeight_mul_oddP5Correlation55 :
    IntervalIntegrable
      (fun t ↦ oddStructuralPoleWeight t * oddP5Correlation55 t)
      volume 0 2 := by
  have hbase : IntervalIntegrable
      (fun t : ℝ ↦
        ((63 / 1408 : ℝ) * t ^ 9 - (259 / 704 : ℝ) * t ^ 7 +
          (181 / 176 : ℝ) * t ^ 5 - (25 / 22 : ℝ) * t ^ 3 +
          (5 / 11 : ℝ) * t) - (2 / 11 : ℝ) * (1 / (2 + t)))
      volume 0 2 :=
    ((by fun_prop : Continuous (fun t : ℝ ↦
      (63 / 1408 : ℝ) * t ^ 9 - (259 / 704 : ℝ) * t ^ 7 +
        (181 / 176 : ℝ) * t ^ 5 - (25 / 22 : ℝ) * t ^ 3 +
        (5 / 11 : ℝ) * t)).intervalIntegrable 0 2).sub
      (intervalIntegrable_inv_two_add_local.const_mul (2 / 11 : ℝ))
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
  have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
  unfold oddStructuralPoleWeight oddP5Correlation55
  field_simp [hp, hm]
  ring

theorem integral_poleWeight_mul_oddP5Correlation55 :
    (∫ t : ℝ in 0..2,
      oddStructuralPoleWeight t * oddP5Correlation55 t) =
        47 / 330 - (2 / 11 : ℝ) * Real.log 2 := by
  have hrewrite : (∫ t : ℝ in 0..2,
      oddStructuralPoleWeight t * oddP5Correlation55 t) =
      ∫ t : ℝ in 0..2,
        ((63 / 1408 : ℝ) * t ^ 9 - (259 / 704 : ℝ) * t ^ 7 +
          (181 / 176 : ℝ) * t ^ 5 - (25 / 22 : ℝ) * t ^ 3 +
          (5 / 11 : ℝ) * t) - (2 / 11 : ℝ) * (1 / (2 + t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold oddStructuralPoleWeight oddP5Correlation55
    field_simp [hp, hm]
    ring
  rw [hrewrite, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun t : ℝ ↦
      (63 / 1408 : ℝ) * t ^ 9 - (259 / 704 : ℝ) * t ^ 7 +
        (181 / 176 : ℝ) * t ^ 5 - (25 / 22 : ℝ) * t ^ 3 +
        (5 / 11 : ℝ) * t)).intervalIntegrable 0 2)
    (intervalIntegrable_inv_two_add_local.const_mul (2 / 11 : ℝ)),
    intervalIntegral.integral_const_mul, integral_inv_two_add_local]
  have hpoly : (∫ t : ℝ in 0..2,
      (63 / 1408 : ℝ) * t ^ 9 - (259 / 704 : ℝ) * t ^ 7 +
        (181 / 176 : ℝ) * t ^ 5 - (25 / 22 : ℝ) * t ^ 3 +
        (5 / 11 : ℝ) * t) = 47 / 330 := by
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [integral_pow]
    norm_num
  rw [hpoly]

/-! ## Exact regular-plus-poles perturbation formula -/

private theorem endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles
    (C : ℝ → ℝ) :
    yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) =
      ∫ t : ℝ in 0..2,
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
          oddStructuralPoleWeight t) * C t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [
      (Set.countable_singleton (2 : ℝ)).ae_notMem
        (volume.restrict (Set.uIoc (0 : ℝ) 2)),
      ae_restrict_mem measurableSet_uIoc] with t ht2 ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) 2 := by
    simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have htne : t ≠ 2 := by simpa using ht2
  have htlt : t < 2 := lt_of_le_of_ne ht'.2 htne
  calc
    yoshidaEndpointA *
        (factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) =
      (yoshidaEndpointA *
        factorTwoSymmetricWeight (yoshidaEndpointA * t)) * C t := by ring
    _ = _ := by
      rw [yoshidaEndpointA_mul_factorTwoSymmetricWeight_eq_regular_poles
        ht'.1 htlt]
      unfold oddStructuralPoleWeight
      ring

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

private theorem measurable_symmetricRegularWeight_local :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_local.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel_local.comp (by fun_prop))

private theorem intervalIntegrable_oddStructuralRegularError_local
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * C t) volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
      oddStructuralRegularQuadratic t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 500 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_const.mul measurable_symmetricRegularWeight_local).sub
      (by unfold oddStructuralRegularQuadratic; fun_prop)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hk := oddStructuralRegularKernelControl t
      (⟨ht.1.le, ht.2⟩ : t ∈ Icc (0 : ℝ) 2)
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

private theorem integral_regular_poles_oddP5Correlation55_eq :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddP5Correlation55 t) =
      oddStructuralRegularError oddP5Correlation55 +
        (47 / 330 - (2 / 11 : ℝ) * Real.log 2) := by
  have herr := intervalIntegrable_oddStructuralRegularError_local
    oddP5Correlation55 continuous_oddP5Correlation55
  have hquad : IntervalIntegrable
      (fun t ↦ oddStructuralRegularQuadratic t * oddP5Correlation55 t)
      volume 0 2 :=
    ((by unfold oddStructuralRegularQuadratic; fun_prop :
      Continuous oddStructuralRegularQuadratic).mul
        continuous_oddP5Correlation55).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddP5Correlation55 t) = fun t ↦
      ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddP5Correlation55 t +
        oddStructuralRegularQuadratic t * oddP5Correlation55 t) +
      oddStructuralPoleWeight t * oddP5Correlation55 t by
    funext t
    ring,
    intervalIntegral.integral_add (herr.add hquad)
      intervalIntegrable_poleWeight_mul_oddP5Correlation55,
    intervalIntegral.integral_add herr hquad,
    integral_regularQuadratic_mul_oddP5Correlation55,
    integral_poleWeight_mul_oddP5Correlation55]
  unfold oddStructuralRegularError
  ring

theorem factorTwoCenteredSymmetricPerturbation_p5_structural_eq :
    factorTwoCenteredSymmetricPerturbation factorTwoCenteredP5 =
      poleFreeAnalyticError oddP5Correlation55 +
        (47 / 330 - (2 / 11 : ℝ) * Real.log 2) -
        (Real.log 2 / Real.sqrt 2) * (2 / 11) -
        (Real.log 3 / Real.sqrt 3) * oddP5Correlation55
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoCenteredSymmetricPerturbation
  simp_rw [centeredEndpointCorrelation_p5]
  rw [endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles,
    integral_regular_poles_oddP5Correlation55_eq,
    oddStructuralRegularError_oddP5Correlation55_sharp_expansion]
  norm_num [oddP5Correlation55]

/-! ## The retained-prime correlation -/

private theorem hasDerivAt_oddP5Correlation55 (x : ℝ) :
    HasDerivAt oddP5Correlation55
      ((x ^ 2 - 2) *
        (63 * x ^ 8 - 504 * x ^ 6 + 1232 * x ^ 4 -
          896 * x ^ 2 + 128) / 256) x := by
  rw [show oddP5Correlation55 = fun t : ℝ ↦
      2 / 11 - t + (5 / 2 : ℝ) * t ^ 3 - (21 / 8 : ℝ) * t ^ 5 +
        (5 / 4 : ℝ) * t ^ 7 - (35 / 128 : ℝ) * t ^ 9 +
        (63 / 2816 : ℝ) * t ^ 11 by
    funext t
    rfl]
  convert (((((((hasDerivAt_const x (2 / 11 : ℝ)).sub
      (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 3).const_mul (5 / 2))).sub
          (((hasDerivAt_id x).pow 5).const_mul (21 / 8))).add
            (((hasDerivAt_id x).pow 7).const_mul (5 / 4))).sub
              (((hasDerivAt_id x).pow 9).const_mul (35 / 128))).add
                (((hasDerivAt_id x).pow 11).const_mul (63 / 2816))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem oddP5Correlation55_strictAntiOn :
    StrictAntiOn oddP5Correlation55
      (Icc (11699 / 10000 : ℝ) (117 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    continuous_oddP5Correlation55.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_oddP5Correlation55 x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hx2hi := pow_lt_pow_left₀ hx.2 hx0
    (by norm_num : (2 : ℕ) ≠ 0)
  let y : ℝ := x ^ 2 - 1
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    norm_num at hx2lo
    linarith
  have hy1 : y ≤ 1 := by
    dsimp only [y]
    norm_num at hx2hi
    linarith
  have hyplus : 0 ≤ 1 + y := by linarith
  have hfactor : 0 ≤ y * (1 - y) * (1 + y) :=
    mul_nonneg (mul_nonneg hy0 (sub_nonneg.mpr hy1)) hyplus
  have hy3 : y ^ 3 ≤ y := by
    nlinarith
  have hQ : 0 <
      63 * x ^ 8 - 504 * x ^ 6 + 1232 * x ^ 4 -
        896 * x ^ 2 + 128 := by
    rw [show
      63 * x ^ 8 - 504 * x ^ 6 + 1232 * x ^ 4 -
          896 * x ^ 2 + 128 =
        63 * y ^ 4 - 252 * y ^ 3 + 98 * y ^ 2 + 308 * y + 23 by
      dsimp only [y]
      ring]
    nlinarith [sq_nonneg y, pow_nonneg hy0 4]
  have hxFactor : x ^ 2 - 2 < 0 := by
    norm_num at hx2hi
    linarith
  have hproduct : (x ^ 2 - 2) *
      (63 * x ^ 8 - 504 * x ^ 6 + 1232 * x ^ 4 -
        896 * x ^ 2 + 128) < 0 :=
    mul_neg_of_neg_of_pos hxFactor hQ
  nlinarith

theorem oddP5PrimeCorrelation55_bounds :
    (7 / 500 : ℝ) < oddP5Correlation55
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddP5Correlation55 (factorTwoPrimeShift / yoshidaEndpointA) <
        (3 / 200 : ℝ) := by
  let τ : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let a : ℝ := 116992 / 100000
  let b : ℝ := 116993 / 100000
  have hτ := factorTwoPrimeRatio_sharp_bounds
  have ha : a ∈ Icc (11699 / 10000 : ℝ) (117 / 100) := by norm_num [a]
  have hb : b ∈ Icc (11699 / 10000 : ℝ) (117 / 100) := by norm_num [b]
  have hτmem : τ ∈ Icc (11699 / 10000 : ℝ) (117 / 100) := by
    dsimp only [τ]
    exact ⟨factorTwoPrimeRatio_kernel_bounds.1.le,
      factorTwoPrimeRatio_kernel_bounds.2.le⟩
  have hlo := oddP5Correlation55_strictAntiOn hτmem hb hτ.2
  have hhi := oddP5Correlation55_strictAntiOn ha hτmem hτ.1
  dsimp only [τ, a, b] at hlo hhi ⊢
  constructor
  · calc
      (7 / 500 : ℝ) < oddP5Correlation55 (116993 / 100000) := by
        norm_num [oddP5Correlation55]
      _ < oddP5Correlation55
          (factorTwoPrimeShift / yoshidaEndpointA) := hlo
  · calc
      oddP5Correlation55 (factorTwoPrimeShift / yoshidaEndpointA) <
          oddP5Correlation55 (116992 / 100000) := hhi
      _ < (3 / 200 : ℝ) := by
        norm_num [oddP5Correlation55]

/-! ## Endpoint-ready diagonal bounds -/

theorem neg_eighty_three_thousandths_lt_factorTwoCenteredSymmetricPerturbation_p5 :
    (-83 / 1000 : ℝ) <
      factorTwoCenteredSymmetricPerturbation factorTwoCenteredP5 := by
  let α : ℝ := Real.log 2 / Real.sqrt 2
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c : ℝ := oddP5Correlation55
    (factorTwoPrimeShift / yoshidaEndpointA)
  have herr := abs_poleFreeAnalyticError_oddP5Correlation55_le
  rw [abs_le] at herr
  have hlog := strict_log_two_fine_bounds
  have hα : (49 / 100 : ℝ) < α ∧ α < (491 / 1000 : ℝ) := by
    simpa only [α] using factorTwoDyadicWeight_bounds
  have hβ : (63427 / 100000 : ℝ) < β ∧ β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds
  have hc : (7 / 500 : ℝ) < c ∧ c < (3 / 200 : ℝ) := by
    simpa only [c] using oddP5PrimeCorrelation55_bounds
  have hprimeUpper :
      β * c < (6343 / 10000 : ℝ) * (3 / 200) :=
    mul_lt_mul_of_nonneg hβ.2 hc.2
      (by linarith [hβ.1]) (by linarith [hc.1])
  rw [factorTwoCenteredSymmetricPerturbation_p5_structural_eq]
  dsimp only [α, β, c] at hprimeUpper ⊢
  nlinarith [herr.1, hlog.2, hα.2]

theorem factorTwoCenteredSymmetricPerturbation_p5_neg :
    factorTwoCenteredSymmetricPerturbation factorTwoCenteredP5 < 0 := by
  let α : ℝ := Real.log 2 / Real.sqrt 2
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c : ℝ := oddP5Correlation55
    (factorTwoPrimeShift / yoshidaEndpointA)
  have herr := abs_poleFreeAnalyticError_oddP5Correlation55_le
  rw [abs_le] at herr
  have hlog := strict_log_two_fine_bounds
  have hα : (49 / 100 : ℝ) < α ∧ α < (491 / 1000 : ℝ) := by
    simpa only [α] using factorTwoDyadicWeight_bounds
  have hβ : (63427 / 100000 : ℝ) < β ∧ β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds
  have hc : (7 / 500 : ℝ) < c ∧ c < (3 / 200 : ℝ) := by
    simpa only [c] using oddP5PrimeCorrelation55_bounds
  have hprimePos : 0 < β * c :=
    mul_pos (by linarith [hβ.1]) (by linarith [hc.1])
  rw [factorTwoCenteredSymmetricPerturbation_p5_structural_eq]
  dsimp only [α, β, c] at hprimePos ⊢
  nlinarith [herr.2, hlog.1, hα.1]

theorem factorTwoCenteredSymmetricPerturbation_p5_endpoint_bounds :
    (-83 / 1000 : ℝ) <
        factorTwoCenteredSymmetricPerturbation factorTwoCenteredP5 ∧
      factorTwoCenteredSymmetricPerturbation factorTwoCenteredP5 < 0 :=
  ⟨neg_eighty_three_thousandths_lt_factorTwoCenteredSymmetricPerturbation_p5,
    factorTwoCenteredSymmetricPerturbation_p5_neg⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
