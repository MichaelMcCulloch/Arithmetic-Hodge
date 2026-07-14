import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp

noncomputable section

open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOcticTwoModeSchurData
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddLowEndpointPositive
open YoshidaFactorTwoPhaseOddStructuralPerturbation
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaRegularKernelBound

/-!
# A structural Loewner lower Gram for the odd perturbation

The global pole-free degree-six model is integrated exactly against the
`P₁/P₃` correlation polynomials.  Its sole analytic remainder is charged
once to the complete profile energy.  There is no subdivision, sampling, or
certificate.
-/

private theorem integral_polynomial_thirteen
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 + (a₈ * x ^ 8 +
            (a₉ * x ^ 9 + (a₁₀ * x ^ 10 + (a₁₁ * x ^ 11 +
              (a₁₂ * x ^ 12 + a₁₃ * x ^ 13))))))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 +
        a₁₂ * (r ^ 13 - l ^ 13) / 13 +
        a₁₃ * (r ^ 14 - l ^ 14) / 14 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

def oddPolynomialMoment11 : ℝ :=
  (-4 / 9 : ℝ) * polynomialD2 - (16 / 15 : ℝ) * polynomialD4 -
    (96 / 35 : ℝ) * polynomialD6

def oddPolynomialMoment13 : ℝ :=
  -(16 / 105 : ℝ) * polynomialD4 - (32 / 45 : ℝ) * polynomialD6

def oddPolynomialMoment33 : ℝ :=
  -(32 / 245 : ℝ) * polynomialD6

theorem integral_polynomialDifference_mul_oddCorrelations :
    (∫ t : ℝ in 0..2,
      poleFreePolynomialDifference t * oddStructuralCorrelation11 t) =
        oddPolynomialMoment11 ∧
      (∫ t : ℝ in 0..2,
        poleFreePolynomialDifference t * oddStructuralCorrelation13 t) =
        oddPolynomialMoment13 ∧
      (∫ t : ℝ in 0..2,
        poleFreePolynomialDifference t * oddStructuralCorrelation33 t) =
        oddPolynomialMoment33 := by
  constructor
  · rw [show (fun t : ℝ ↦
        poleFreePolynomialDifference t * oddStructuralCorrelation11 t) =
      fun t ↦ ((2 / 3 : ℝ) * polynomialD0) * t ^ 0 +
        ((-polynomialD0) * t ^ 1 +
          (((2 / 3 : ℝ) * polynomialD2) * t ^ 2 +
            (((1 / 6 : ℝ) * polynomialD0 - polynomialD2) * t ^ 3 +
              (((2 / 3 : ℝ) * polynomialD4) * t ^ 4 +
                (((1 / 6 : ℝ) * polynomialD2 - polynomialD4) * t ^ 5 +
                  (((2 / 3 : ℝ) * polynomialD6) * t ^ 6 +
                    (((1 / 6 : ℝ) * polynomialD4 - polynomialD6) * t ^ 7 +
                      (0 * t ^ 8 + (((1 / 6 : ℝ) * polynomialD6) * t ^ 9 +
                        (0 * t ^ 10 + (0 * t ^ 11 +
                          (0 * t ^ 12 + 0 * t ^ 13)))))))))))) by
      funext t
      rw [poleFreePolynomialDifference_expansion]
      unfold oddStructuralCorrelation11
      ring,
    integral_polynomial_thirteen]
    unfold oddPolynomialMoment11
    ring
  · constructor
    · rw [show (fun t : ℝ ↦
          poleFreePolynomialDifference t * oddStructuralCorrelation13 t) =
        fun t ↦ 0 * t ^ 0 +
          ((-polynomialD0) * t ^ 1 +
            (((5 / 2 : ℝ) * polynomialD0) * t ^ 2 +
              ((-(3 / 2 : ℝ) * polynomialD0 - polynomialD2) * t ^ 3 +
                (((5 / 2 : ℝ) * polynomialD2) * t ^ 4 +
                  (((1 / 8 : ℝ) * polynomialD0 -
                      (3 / 2 : ℝ) * polynomialD2 - polynomialD4) * t ^ 5 +
                    (((5 / 2 : ℝ) * polynomialD4) * t ^ 6 +
                      (((1 / 8 : ℝ) * polynomialD2 -
                          (3 / 2 : ℝ) * polynomialD4 - polynomialD6) * t ^ 7 +
                        (((5 / 2 : ℝ) * polynomialD6) * t ^ 8 +
                          (((1 / 8 : ℝ) * polynomialD4 -
                            (3 / 2 : ℝ) * polynomialD6) * t ^ 9 +
                            (0 * t ^ 10 + (((1 / 8 : ℝ) * polynomialD6) * t ^ 11 +
                              (0 * t ^ 12 + 0 * t ^ 13)))))))))))) by
        funext t
        rw [poleFreePolynomialDifference_expansion]
        unfold oddStructuralCorrelation13
        ring,
      integral_polynomial_thirteen]
      unfold oddPolynomialMoment13
      ring
    · rw [show (fun t : ℝ ↦
          poleFreePolynomialDifference t * oddStructuralCorrelation33 t) =
        fun t ↦ ((2 / 7 : ℝ) * polynomialD0) * t ^ 0 +
          ((-polynomialD0) * t ^ 1 +
            (((2 / 7 : ℝ) * polynomialD2) * t ^ 2 +
              ((polynomialD0 - polynomialD2) * t ^ 3 +
                (((2 / 7 : ℝ) * polynomialD4) * t ^ 4 +
                  ((-(3 / 8 : ℝ) * polynomialD0 + polynomialD2 -
                      polynomialD4) * t ^ 5 +
                    (((2 / 7 : ℝ) * polynomialD6) * t ^ 6 +
                      (((5 / 112 : ℝ) * polynomialD0 -
                          (3 / 8 : ℝ) * polynomialD2 + polynomialD4 -
                          polynomialD6) * t ^ 7 +
                        (0 * t ^ 8 +
                          (((5 / 112 : ℝ) * polynomialD2 -
                            (3 / 8 : ℝ) * polynomialD4 + polynomialD6) * t ^ 9 +
                            (0 * t ^ 10 +
                              (((5 / 112 : ℝ) * polynomialD4 -
                                (3 / 8 : ℝ) * polynomialD6) * t ^ 11 +
                                (0 * t ^ 12 +
                                  ((5 / 112 : ℝ) * polynomialD6) * t ^ 13)))))))))))) by
        funext t
        rw [poleFreePolynomialDifference_expansion]
        unfold oddStructuralCorrelation33
        ring,
      integral_polynomial_thirteen]
      unfold oddPolynomialMoment33
      ring

theorem oddPolynomialMoment_bounds :
    (-8 / 984375 : ℝ) ≤ oddPolynomialMoment11 ∧
      oddPolynomialMoment11 ≤ (-7 / 5625000 : ℝ) ∧
      (-151 / 19687500 : ℝ) ≤ oddPolynomialMoment13 ∧
      oddPolynomialMoment13 ≤ (-47 / 6562500 : ℝ) ∧
      (-1 / 15312500 : ℝ) ≤ oddPolynomialMoment33 ∧
      oddPolynomialMoment33 ≤ 0 := by
  rcases poleFree_coefficient_bounds with
    ⟨hd0L, hd0U, hd2L, hd2U, hd4L, hd4U, hd6L, hd6U⟩
  unfold oddPolynomialMoment11 oddPolynomialMoment13 oddPolynomialMoment33
    polynomialD2 polynomialD4 polynomialD6
  constructor
  · norm_num at hd2U hd4U hd6U ⊢
    linarith
  constructor
  · norm_num at hd2L hd4L hd6L ⊢
    linarith
  constructor
  · norm_num at hd4U hd6U ⊢
    linarith
  constructor
  · norm_num at hd4L hd6L ⊢
    linarith
  constructor
  · norm_num at hd6U ⊢
    linarith
  · norm_num at hd6L ⊢
    linarith

theorem centeredEndpointCorrelation_oddStructuralProfile
    (c d t : ℝ) :
    centeredEndpointCorrelation (factorTwoOddStructuralLowProfile c d) t =
      c ^ 2 * oddStructuralCorrelation11 t +
        2 * c * d * oddStructuralCorrelation13 t +
        d ^ 2 * oddStructuralCorrelation33 t := by
  have h1 : Continuous centeredP1 := by
    unfold centeredP1
    fun_prop
  have h3 : Continuous centeredP3 := by
    unfold centeredP3
    fun_prop
  rw [show factorTwoOddStructuralLowProfile c d =
      c • centeredP1 + d • centeredP3 by
    funext x
    unfold factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul],
    centeredEndpointCorrelation_add (c • centeredP1)
      (d • centeredP3) (h1.const_smul c) (h3.const_smul d)]
  have hself1 :
      centeredEndpointCorrelation (c • centeredP1) t =
        c ^ 2 * factorTwoCenteredCorrelationBilinear
          centeredP1 centeredP1 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  have hself3 :
      centeredEndpointCorrelation (d • centeredP3) t =
        d ^ 2 * factorTwoCenteredCorrelationBilinear
          centeredP3 centeredP3 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  rw [hself1, hself3,
    factorTwoCenteredCorrelationBilinear_smul_smul,
    factorTwoCenteredCorrelationBilinear_p1_p1,
    factorTwoCenteredCorrelationBilinear_p1_p3,
    factorTwoCenteredCorrelationBilinear_p3_p3]
  unfold oddStructuralCorrelation11 oddStructuralCorrelation13
    oddStructuralCorrelation33
  ring

theorem integral_oddStructuralProfile_sq (c d : ℝ) :
    (∫ x : ℝ in -1..1, factorTwoOddStructuralLowProfile c d x ^ 2) =
      (2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2 := by
  have h11 : IntervalIntegrable (fun x : ℝ ↦ centeredP1 x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredP1
    fun_prop
  have h13 : IntervalIntegrable
      (fun x : ℝ ↦ centeredP1 x * centeredP3 x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredP1 centeredP3
    fun_prop
  have h33 : IntervalIntegrable (fun x : ℝ ↦ centeredP3 x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold centeredP3
    fun_prop
  rw [show (fun x : ℝ ↦ factorTwoOddStructuralLowProfile c d x ^ 2) =
      fun x ↦ c ^ 2 * centeredP1 x ^ 2 +
        (2 * c * d) * (centeredP1 x * centeredP3 x) +
        d ^ 2 * centeredP3 x ^ 2 by
    funext x
    unfold factorTwoOddStructuralLowProfile
    ring,
    intervalIntegral.integral_add
      ((h11.const_mul (c ^ 2)).add (h13.const_mul (2 * c * d)))
      (h33.const_mul (d ^ 2)),
    intervalIntegral.integral_add
      (h11.const_mul (c ^ 2)) (h13.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_centeredP1_sq, integral_centeredP1_mul_p3,
    integral_centeredP3_sq]
  ring

theorem abs_poleFreeAnalyticError_oddProfile_le (c d : ℝ) :
    |poleFreeAnalyticError
        (centeredEndpointCorrelation
          (factorTwoOddStructuralLowProfile c d))| ≤
      (3 / 8000 : ℝ) *
        ((2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2) := by
  have herr := abs_poleFreeAnalyticError_le
    (centeredEndpointCorrelation (factorTwoOddStructuralLowProfile c d))
    (continuous_centeredEndpointCorrelation_of_continuous
      (factorTwoOddStructuralLowProfile c d)
      (continuous_factorTwoOddStructuralLowProfile c d))
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy
    (factorTwoOddStructuralLowProfile c d)
    (continuous_factorTwoOddStructuralLowProfile c d)
  have hscaled := mul_le_mul_of_nonneg_left hcorr
    (by norm_num : (0 : ℝ) ≤ 3 / 8000)
  rw [integral_oddStructuralProfile_sq] at hscaled
  exact herr.trans hscaled

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

theorem oddStructuralRegularError_profile_expansion (c d : ℝ) :
    oddStructuralRegularError
        (centeredEndpointCorrelation
          (factorTwoOddStructuralLowProfile c d)) =
      c ^ 2 * oddStructuralRegularError oddStructuralCorrelation11 +
        2 * c * d * oddStructuralRegularError oddStructuralCorrelation13 +
        d ^ 2 * oddStructuralRegularError oddStructuralCorrelation33 := by
  have h11 := intervalIntegrable_oddStructuralRegularError_local
    oddStructuralCorrelation11 (by unfold oddStructuralCorrelation11; fun_prop)
  have h13 := intervalIntegrable_oddStructuralRegularError_local
    oddStructuralCorrelation13 (by unfold oddStructuralCorrelation13; fun_prop)
  have h33 := intervalIntegrable_oddStructuralRegularError_local
    oddStructuralCorrelation33 (by unfold oddStructuralCorrelation33; fun_prop)
  unfold oddStructuralRegularError
  simp_rw [centeredEndpointCorrelation_oddStructuralProfile]
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
        oddStructuralRegularQuadratic t) *
        (c ^ 2 * oddStructuralCorrelation11 t +
          2 * c * d * oddStructuralCorrelation13 t +
          d ^ 2 * oddStructuralCorrelation33 t)) =
      fun t ↦ c ^ 2 *
          ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
            oddStructuralRegularQuadratic t) * oddStructuralCorrelation11 t) +
        (2 * c * d) *
          ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
            oddStructuralRegularQuadratic t) * oddStructuralCorrelation13 t) +
        d ^ 2 *
          ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
            oddStructuralRegularQuadratic t) * oddStructuralCorrelation33 t) by
    funext t
    ring,
    intervalIntegral.integral_add
      ((h11.const_mul (c ^ 2)).add (h13.const_mul (2 * c * d)))
      (h33.const_mul (d ^ 2)),
    intervalIntegral.integral_add (h11.const_mul (c ^ 2))
      (h13.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]

private theorem integral_polynomialDifference_oddProfile (c d : ℝ) :
    (∫ t : ℝ in 0..2,
      poleFreePolynomialDifference t *
        centeredEndpointCorrelation
          (factorTwoOddStructuralLowProfile c d) t) =
      oddPolynomialMoment11 * c ^ 2 +
        2 * oddPolynomialMoment13 * c * d +
        oddPolynomialMoment33 * d ^ 2 := by
  have h11 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * oddStructuralCorrelation11 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold oddStructuralCorrelation11; fun_prop)).intervalIntegrable 0 2
  have h13 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * oddStructuralCorrelation13 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold oddStructuralCorrelation13; fun_prop)).intervalIntegrable 0 2
  have h33 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * oddStructuralCorrelation33 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold oddStructuralCorrelation33; fun_prop)).intervalIntegrable 0 2
  simp_rw [centeredEndpointCorrelation_oddStructuralProfile]
  rw [show (fun t : ℝ ↦
      poleFreePolynomialDifference t *
        (c ^ 2 * oddStructuralCorrelation11 t +
          2 * c * d * oddStructuralCorrelation13 t +
          d ^ 2 * oddStructuralCorrelation33 t)) =
      fun t ↦ c ^ 2 *
          (poleFreePolynomialDifference t * oddStructuralCorrelation11 t) +
        (2 * c * d) *
          (poleFreePolynomialDifference t * oddStructuralCorrelation13 t) +
        d ^ 2 *
          (poleFreePolynomialDifference t * oddStructuralCorrelation33 t) by
    funext t
    ring,
    intervalIntegral.integral_add
      ((h11.const_mul (c ^ 2)).add (h13.const_mul (2 * c * d)))
      (h33.const_mul (d ^ 2)),
    intervalIntegral.integral_add (h11.const_mul (c ^ 2))
      (h13.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_polynomialDifference_mul_oddCorrelations.1,
    integral_polynomialDifference_mul_oddCorrelations.2.1,
    integral_polynomialDifference_mul_oddCorrelations.2.2]
  ring

theorem oddStructuralRegularError_profile_sharp_expansion (c d : ℝ) :
    oddStructuralRegularError
        (centeredEndpointCorrelation
          (factorTwoOddStructuralLowProfile c d)) =
      poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoOddStructuralLowProfile c d)) +
        oddPolynomialMoment11 * c ^ 2 +
        2 * oddPolynomialMoment13 * c * d +
        oddPolynomialMoment33 * d ^ 2 := by
  have hsplit := evenStructuralRegularError_eq_analytic_add_polynomial
    (centeredEndpointCorrelation (factorTwoOddStructuralLowProfile c d))
    (continuous_centeredEndpointCorrelation_of_continuous
      (factorTwoOddStructuralLowProfile c d)
      (continuous_factorTwoOddStructuralLowProfile c d))
  rw [evenStructuralRegularError,
    integral_polynomialDifference_oddProfile] at hsplit
  calc
    oddStructuralRegularError
          (centeredEndpointCorrelation
            (factorTwoOddStructuralLowProfile c d)) =
        poleFreeAnalyticError
            (centeredEndpointCorrelation
              (factorTwoOddStructuralLowProfile c d)) +
          (oddPolynomialMoment11 * c ^ 2 +
            2 * oddPolynomialMoment13 * c * d +
            oddPolynomialMoment33 * d ^ 2) := hsplit
    _ = _ := by ring

def oddPerturbationBase11 : ℝ :=
  -4 / 375 + (2 / 3 - (2 / 3 : ℝ) * Real.log 2) -
    (Real.log 2 / Real.sqrt 2) * (2 / 3) -
    (Real.log 3 / Real.sqrt 3) * oddStructuralCorrelation11
      (factorTwoPrimeShift / yoshidaEndpointA)

def oddPerturbationBase13 : ℝ :=
  (7 - 10 * Real.log 2) -
    (Real.log 3 / Real.sqrt 3) * oddStructuralCorrelation13
      (factorTwoPrimeShift / yoshidaEndpointA)

def oddPerturbationBase33 : ℝ :=
  (5 / 21 - (2 / 7 : ℝ) * Real.log 2) -
    (Real.log 2 / Real.sqrt 2) * (2 / 7) -
    (Real.log 3 / Real.sqrt 3) * oddStructuralCorrelation33
      (factorTwoPrimeShift / yoshidaEndpointA)

theorem oddPerturbation_profile_kernel_eq (c d : ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoOddStructuralLowProfile c d) =
      oddStructuralRegularError
          (centeredEndpointCorrelation
            (factorTwoOddStructuralLowProfile c d)) +
        oddPerturbationBase11 * c ^ 2 +
        2 * oddPerturbationBase13 * c * d +
        oddPerturbationBase33 * d ^ 2 := by
  rw [factorTwoCenteredSymmetricPerturbation_oddStructuralLow,
    factorTwoCenteredSymmetricPerturbation_p1_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_structural_eq,
    factorTwoCenteredSymmetricPerturbation_p3_structural_eq,
    oddStructuralRegularError_profile_expansion]
  unfold oddPerturbationBase11 oddPerturbationBase13 oddPerturbationBase33
  ring

def oddPerturbationTaylor11 : ℝ :=
  oddPerturbationBase11 + oddPolynomialMoment11 - 1 / 4000

def oddPerturbationTaylor13 : ℝ :=
  oddPerturbationBase13 + oddPolynomialMoment13

def oddPerturbationTaylor33 : ℝ :=
  oddPerturbationBase33 + oddPolynomialMoment33 - 3 / 28000

theorem oddPerturbationTaylor_quadratic_le (c d : ℝ) :
    oddPerturbationTaylor11 * c ^ 2 +
        2 * oddPerturbationTaylor13 * c * d +
        oddPerturbationTaylor33 * d ^ 2 ≤
      factorTwoCenteredSymmetricPerturbation
        (factorTwoOddStructuralLowProfile c d) := by
  have herr := abs_poleFreeAnalyticError_oddProfile_le c d
  have herrLower :
      -(3 / 8000 : ℝ) *
          ((2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2) ≤
        poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoOddStructuralLowProfile c d)) :=
    by simpa only [neg_mul] using neg_le_of_abs_le herr
  rw [oddPerturbation_profile_kernel_eq,
    oddStructuralRegularError_profile_sharp_expansion]
  unfold oddPerturbationTaylor11 oddPerturbationTaylor13
    oddPerturbationTaylor33
  nlinarith

/-! ## Tight structural bounds at the retained prime lag -/

private theorem log_two_div_sqrt_two_upper :
    Real.log 2 / Real.sqrt 2 < (49014 / 100000 : ℝ) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hspos]
  have hlog := strict_log_two_fine_bounds.2
  have hs := sqrt_two_kernel_bounds.1
  nlinarith

theorem factorTwoPrimeRatio_sharp_bounds :
    (116992 / 100000 : ℝ) < factorTwoPrimeShift / yoshidaEndpointA ∧
      factorTwoPrimeShift / yoshidaEndpointA < (116993 / 100000 : ℝ) := by
  have hApos : 0 < yoshidaEndpointA := yoshidaEndpointA_pos
  constructor
  · rw [lt_div_iff₀ hApos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    have h32 := strict_log_three_halves_kernel_bounds.1
    have h2 := strict_log_two_fine_bounds.2
    nlinarith
  · rw [div_lt_iff₀ hApos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    have h32 := strict_log_three_halves_kernel_bounds.2
    have h2 := strict_log_two_fine_bounds.1
    nlinarith

private theorem hasDerivAt_correlation11 (x : ℝ) :
    HasDerivAt oddStructuralCorrelation11 (-1 + x ^ 2 / 2) x := by
  rw [show oddStructuralCorrelation11 = fun t : ℝ ↦
      2 / 3 - t + t ^ 3 / 6 by
    funext t
    unfold oddStructuralCorrelation11
    ring]
  convert (((hasDerivAt_const x (2 / 3 : ℝ)).sub (hasDerivAt_id x)).add
    (((hasDerivAt_id x).pow 3).div_const 6)) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem hasDerivAt_correlation13 (x : ℝ) :
    HasDerivAt oddStructuralCorrelation13
      (-1 + 5 * x - (9 / 2) * x ^ 2 + (5 / 8) * x ^ 4) x := by
  rw [show oddStructuralCorrelation13 = fun t : ℝ ↦
      -t + (5 / 2) * t ^ 2 - (3 / 2) * t ^ 3 + (1 / 8) * t ^ 5 by
    funext t
    unfold oddStructuralCorrelation13
    ring]
  convert ((((hasDerivAt_id x).neg.add
      (((hasDerivAt_id x).pow 2).const_mul (5 / 2))).sub
    (((hasDerivAt_id x).pow 3).const_mul (3 / 2))).add
      (((hasDerivAt_id x).pow 5).const_mul (1 / 8))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem hasDerivAt_correlation33 (x : ℝ) :
    HasDerivAt oddStructuralCorrelation33
      (-1 + 3 * x ^ 2 - (15 / 8) * x ^ 4 + (5 / 16) * x ^ 6) x := by
  rw [show oddStructuralCorrelation33 = fun t : ℝ ↦
      2 / 7 - t + t ^ 3 - (3 / 8) * t ^ 5 + (5 / 112) * t ^ 7 by
    funext t
    unfold oddStructuralCorrelation33
    ring]
  convert (((((hasDerivAt_const x (2 / 7 : ℝ)).sub
      (hasDerivAt_id x)).add ((hasDerivAt_id x).pow 3)).sub
    (((hasDerivAt_id x).pow 5).const_mul (3 / 8))).add
      (((hasDerivAt_id x).pow 7).const_mul (5 / 112))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem correlation11_strictAntiOn :
    StrictAntiOn oddStructuralCorrelation11
      (Icc (11699 / 10000 : ℝ) (117 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold oddStructuralCorrelation11; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_correlation11 x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2 := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (2 : ℕ) ≠ 0)
  norm_num at hx2 ⊢
  nlinarith

private theorem correlation13_strictAntiOn :
    StrictAntiOn oddStructuralCorrelation13
      (Icc (11699 / 10000 : ℝ) (117 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold oddStructuralCorrelation13; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_correlation13 x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hx4hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (4 : ℕ) ≠ 0)
  norm_num at hx2lo hx4hi ⊢
  nlinarith

private theorem correlation33_strictMonoOn :
    StrictMonoOn oddStructuralCorrelation33
      (Icc (11699 / 10000 : ℝ) (117 / 100)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (by unfold oddStructuralCorrelation33; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_correlation33 x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hx4hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (4 : ℕ) ≠ 0)
  have hx6lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (6 : ℕ) ≠ 0)
  norm_num at hx2lo hx4hi hx6lo ⊢
  nlinarith

theorem oddPrimeCorrelations_loewner_bounds :
    (-236376 / 1000000 : ℝ) < oddStructuralCorrelation11
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddStructuralCorrelation11
        (factorTwoPrimeShift / yoshidaEndpointA) < (-236372 / 1000000 : ℝ) ∧
      (123896 / 1000000 : ℝ) < oddStructuralCorrelation13
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddStructuralCorrelation13
        (factorTwoPrimeShift / yoshidaEndpointA) < (123898 / 1000000 : ℝ) ∧
      (2911 / 100000 : ℝ) < oddStructuralCorrelation33
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddStructuralCorrelation33
        (factorTwoPrimeShift / yoshidaEndpointA) < (2912 / 100000 : ℝ) := by
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
  have h11lo := correlation11_strictAntiOn hτmem hb hτ.2
  have h11hi := correlation11_strictAntiOn ha hτmem hτ.1
  have h13lo := correlation13_strictAntiOn hτmem hb hτ.2
  have h13hi := correlation13_strictAntiOn ha hτmem hτ.1
  have h33lo := correlation33_strictMonoOn ha hτmem hτ.1
  have h33hi := correlation33_strictMonoOn hτmem hb hτ.2
  dsimp only [τ, a, b] at h11lo h11hi h13lo h13hi h33lo h33hi ⊢
  constructor
  · calc
      (-236376 / 1000000 : ℝ) <
          oddStructuralCorrelation11 (116993 / 100000) := by
        norm_num [oddStructuralCorrelation11]
      _ < oddStructuralCorrelation11
          (factorTwoPrimeShift / yoshidaEndpointA) := h11lo
  constructor
  · calc
      oddStructuralCorrelation11 (factorTwoPrimeShift / yoshidaEndpointA) <
          oddStructuralCorrelation11 (116992 / 100000) := h11hi
      _ < (-236372 / 1000000 : ℝ) := by
        norm_num [oddStructuralCorrelation11]
  constructor
  · calc
      (123896 / 1000000 : ℝ) <
          oddStructuralCorrelation13 (116993 / 100000) := by
        norm_num [oddStructuralCorrelation13]
      _ < oddStructuralCorrelation13
          (factorTwoPrimeShift / yoshidaEndpointA) := h13lo
  constructor
  · calc
      oddStructuralCorrelation13 (factorTwoPrimeShift / yoshidaEndpointA) <
          oddStructuralCorrelation13 (116992 / 100000) := h13hi
      _ < (123898 / 1000000 : ℝ) := by
        norm_num [oddStructuralCorrelation13]
  constructor
  · calc
      (2911 / 100000 : ℝ) <
          oddStructuralCorrelation33 (116992 / 100000) := by
        norm_num [oddStructuralCorrelation33]
      _ < oddStructuralCorrelation33
          (factorTwoPrimeShift / yoshidaEndpointA) := h33lo
  · calc
      oddStructuralCorrelation33 (factorTwoPrimeShift / yoshidaEndpointA) <
          oddStructuralCorrelation33 (116993 / 100000) := h33hi
      _ < (2912 / 100000 : ℝ) := by
        norm_num [oddStructuralCorrelation33]

def oddPerturbationLoewner11 : ℝ := 168 / 10000

def oddPerturbationLoewner13 : ℝ := -101 / 10000

def oddPerturbationLoewner33 : ℝ := -1188 / 10000

/-! ## The Loewner defect -/

private theorem taylor11_sub_loewner_lower :
    (7 / 1000000 : ℝ) <
      oddPerturbationTaylor11 - oddPerturbationLoewner11 := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c11 : ℝ := oddStructuralCorrelation11
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hlog := strict_log_two_fine_bounds.2
  have hα := log_two_div_sqrt_two_upper
  have hβ : (63427 / 100000 : ℝ) < β := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds.1
  have hc11 : c11 < (-236372 / 1000000 : ℝ) := by
    simpa only [c11] using oddPrimeCorrelations_loewner_bounds.2.1
  have hcneg : (236372 / 1000000 : ℝ) < -c11 := by
    linarith
  have hp :
      (63427 / 100000 : ℝ) * (236372 / 1000000) <
        -(β * c11) := by
    have hmul := mul_lt_mul_of_nonneg hβ hcneg (by norm_num) (by norm_num)
    nlinarith
  have hm := oddPolynomialMoment_bounds.1
  unfold oddPerturbationTaylor11 oddPerturbationBase11
    oddPerturbationLoewner11
  dsimp only [β, c11] at hp
  nlinarith

private theorem taylor13_sub_loewner_abs_upper :
    |oddPerturbationTaylor13 - oddPerturbationLoewner13| <
      (38 / 1000000 : ℝ) := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c13 : ℝ := oddStructuralCorrelation13
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hlog := strict_log_two_fine_bounds
  have hβ : (63427 / 100000 : ℝ) < β ∧
      β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds
  have hc13 : (123896 / 1000000 : ℝ) < c13 ∧
      c13 < (123898 / 1000000 : ℝ) := by
    exact ⟨by simpa only [c13] using
        oddPrimeCorrelations_loewner_bounds.2.2.1,
      by simpa only [c13] using
        oddPrimeCorrelations_loewner_bounds.2.2.2.1⟩
  have hpLower :
      (63427 / 100000 : ℝ) * (123896 / 1000000) < β * c13 :=
    mul_lt_mul_of_nonneg hβ.1 hc13.1 (by norm_num) (by norm_num)
  have hpUpper :
      β * c13 < (6343 / 10000 : ℝ) * (123898 / 1000000) :=
    mul_lt_mul_of_nonneg hβ.2 hc13.2
      (by linarith [hc13.1]) (by linarith [hβ.1])
  have hm := oddPolynomialMoment_bounds
  unfold oddPerturbationTaylor13 oddPerturbationBase13
    oddPerturbationLoewner13
  dsimp only [β, c13] at hpLower hpUpper
  rw [abs_lt]
  constructor <;> nlinarith

private theorem taylor33_sub_loewner_lower :
    (235 / 1000000 : ℝ) <
      oddPerturbationTaylor33 - oddPerturbationLoewner33 := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c33 : ℝ := oddStructuralCorrelation33
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hlog := strict_log_two_fine_bounds.2
  have hα := log_two_div_sqrt_two_upper
  have hβ : β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds.2
  have hc33 : c33 < (2912 / 100000 : ℝ) := by
    simpa only [c33] using
      oddPrimeCorrelations_loewner_bounds.2.2.2.2.2
  have hc33pos : 0 < c33 := by
    have := oddPrimeCorrelations_loewner_bounds.2.2.2.2.1
    dsimp only [c33]
    linarith
  have hβpos : 0 < β := by
    have := log_three_div_sqrt_three_kernel_bounds.1
    dsimp only [β]
    linarith
  have hpUpper :
      β * c33 < (6343 / 10000 : ℝ) * (2912 / 100000) :=
    mul_lt_mul_of_nonneg hβ hc33 hβpos.le hc33pos.le
  have hm := oddPolynomialMoment_bounds.2.2.2.2.1
  unfold oddPerturbationTaylor33 oddPerturbationBase33
    oddPerturbationLoewner33
  dsimp only [β, c33] at hpUpper
  nlinarith

private theorem loewner_sub_taylor_defect_det_pos :
    0 <
      (oddPerturbationTaylor11 - oddPerturbationLoewner11) *
          (oddPerturbationTaylor33 - oddPerturbationLoewner33) -
        (oddPerturbationTaylor13 - oddPerturbationLoewner13) ^ 2 := by
  let d11 := oddPerturbationTaylor11 - oddPerturbationLoewner11
  let d13 := oddPerturbationTaylor13 - oddPerturbationLoewner13
  let d33 := oddPerturbationTaylor33 - oddPerturbationLoewner33
  have h11 : (7 / 1000000 : ℝ) < d11 := by
    simpa only [d11] using taylor11_sub_loewner_lower
  have h13 : |d13| < (38 / 1000000 : ℝ) := by
    simpa only [d13] using taylor13_sub_loewner_abs_upper
  have h33 : (235 / 1000000 : ℝ) < d33 := by
    simpa only [d33] using taylor33_sub_loewner_lower
  have h11pos : 0 < d11 := (by norm_num : (0 : ℝ) < 7 / 1000000).trans h11
  have hprod :
      (7 / 1000000 : ℝ) * (235 / 1000000 : ℝ) < d11 * d33 := by
    calc
      (7 / 1000000 : ℝ) * (235 / 1000000 : ℝ) <
          d11 * (235 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_right h11 (by norm_num)
      _ < d11 * d33 := mul_lt_mul_of_pos_left h33 h11pos
  have hsq : d13 ^ 2 < (38 / 1000000 : ℝ) ^ 2 := by
    rw [abs_lt] at h13
    nlinarith [mul_pos (sub_pos.mpr h13.2)
      (by linarith : 0 < d13 + 38 / 1000000)]
  have hrat :
      (38 / 1000000 : ℝ) ^ 2 <
        (7 / 1000000 : ℝ) * (235 / 1000000 : ℝ) := by
    norm_num
  dsimp only [d11, d13, d33] at hprod hsq ⊢
  nlinarith

private theorem oddPerturbationLoewner_quadratic_le_taylor (c d : ℝ) :
    oddPerturbationLoewner11 * c ^ 2 +
        2 * oddPerturbationLoewner13 * c * d +
        oddPerturbationLoewner33 * d ^ 2 ≤
      oddPerturbationTaylor11 * c ^ 2 +
        2 * oddPerturbationTaylor13 * c * d +
        oddPerturbationTaylor33 * d ^ 2 := by
  let d11 := oddPerturbationTaylor11 - oddPerturbationLoewner11
  let d13 := oddPerturbationTaylor13 - oddPerturbationLoewner13
  let d33 := oddPerturbationTaylor33 - oddPerturbationLoewner33
  have h11 : 0 < d11 := by
    have h := taylor11_sub_loewner_lower
    dsimp only [d11]
    nlinarith
  have hdet : 0 < d11 * d33 - d13 ^ 2 := by
    simpa only [d11, d13, d33] using loewner_sub_taylor_defect_det_pos
  have hquad : 0 ≤ d11 * c ^ 2 + 2 * d13 * c * d + d33 * d ^ 2 := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (real_twoByTwo_quadratic_pos d11 d13 d33 c d h11 hdet hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  dsimp only [d11, d13, d33] at hquad
  nlinarith

theorem oddPerturbationLoewner_principal_minors :
    0 < oddPerturbationLoewner11 ∧
      oddPerturbationLoewner33 < 0 ∧
      oddPerturbationLoewner11 * oddPerturbationLoewner33 -
        oddPerturbationLoewner13 ^ 2 < 0 := by
  norm_num [oddPerturbationLoewner11, oddPerturbationLoewner13,
    oddPerturbationLoewner33]

/-- A direct structural Loewner lower Gram for the complete odd symmetric
perturbation.  The analytic error is charged once to the whole `P₁/P₃`
profile; the remaining degree-six polynomial is integrated exactly. -/
theorem oddPerturbationLoewner_quadratic_le (c d : ℝ) :
    oddPerturbationLoewner11 * c ^ 2 +
        2 * oddPerturbationLoewner13 * c * d +
        oddPerturbationLoewner33 * d ^ 2 ≤
      factorTwoCenteredSymmetricPerturbation
        (factorTwoOddStructuralLowProfile c d) := by
  exact (oddPerturbationLoewner_quadratic_le_taylor c d).trans
    (oddPerturbationTaylor_quadratic_le c d)

/-! ## The matching upper Loewner Gram -/

def oddPerturbationUpperTaylor11 : ℝ :=
  oddPerturbationBase11 + oddPolynomialMoment11 + 1 / 4000

def oddPerturbationUpperTaylor13 : ℝ :=
  oddPerturbationBase13 + oddPolynomialMoment13

def oddPerturbationUpperTaylor33 : ℝ :=
  oddPerturbationBase33 + oddPolynomialMoment33 + 3 / 28000

theorem oddPerturbation_quadratic_le_upperTaylor (c d : ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoOddStructuralLowProfile c d) ≤
      oddPerturbationUpperTaylor11 * c ^ 2 +
        2 * oddPerturbationUpperTaylor13 * c * d +
        oddPerturbationUpperTaylor33 * d ^ 2 := by
  have herr := abs_poleFreeAnalyticError_oddProfile_le c d
  have herrUpper :
      poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoOddStructuralLowProfile c d)) ≤
        (3 / 8000 : ℝ) *
          ((2 / 3 : ℝ) * c ^ 2 + (2 / 7 : ℝ) * d ^ 2) :=
    (le_abs_self _).trans herr
  rw [oddPerturbation_profile_kernel_eq,
    oddStructuralRegularError_profile_sharp_expansion]
  unfold oddPerturbationUpperTaylor11 oddPerturbationUpperTaylor13
    oddPerturbationUpperTaylor33
  nlinarith

def oddPerturbationUpper11 : ℝ := 1734 / 100000

def oddPerturbationUpper13 : ℝ := -10065 / 1000000

def oddPerturbationUpper33 : ℝ := -11833 / 100000

private theorem upper11_sub_taylor_lower :
    (2 / 1000000 : ℝ) <
      oddPerturbationUpper11 - oddPerturbationUpperTaylor11 := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c11 : ℝ := oddStructuralCorrelation11
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hlog := strict_log_two_fine_bounds.1
  have hα := log_two_div_sqrt_two_kernel_lower
  have hβ : β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds.2
  have hc11 : (-236376 / 1000000 : ℝ) < c11 := by
    simpa only [c11] using oddPrimeCorrelations_loewner_bounds.1
  have hcneg : -c11 < (236376 / 1000000 : ℝ) := by
    linarith
  have hcnegpos : 0 < -c11 := by
    have := oddPrimeCorrelations_loewner_bounds.2.1
    dsimp only [c11]
    linarith
  have hβpos : 0 < β := by
    have := log_three_div_sqrt_three_kernel_bounds.1
    dsimp only [β]
    linarith
  have hp :
      -(β * c11) <
        (6343 / 10000 : ℝ) * (236376 / 1000000) := by
    have hmul := mul_lt_mul_of_nonneg hβ hcneg hβpos.le hcnegpos.le
    nlinarith
  have hm := oddPolynomialMoment_bounds.2.1
  unfold oddPerturbationUpper11 oddPerturbationUpperTaylor11
    oddPerturbationBase11
  dsimp only [β, c11] at hp
  nlinarith

private theorem upper13_sub_taylor_abs_upper :
    |oddPerturbationUpper13 - oddPerturbationUpperTaylor13| <
      (3 / 1000000 : ℝ) := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c13 : ℝ := oddStructuralCorrelation13
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hlog := strict_log_two_fine_bounds
  have hβ : (63427 / 100000 : ℝ) < β ∧
      β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds
  have hc13 : (123896 / 1000000 : ℝ) < c13 ∧
      c13 < (123898 / 1000000 : ℝ) := by
    exact ⟨by simpa only [c13] using
        oddPrimeCorrelations_loewner_bounds.2.2.1,
      by simpa only [c13] using
        oddPrimeCorrelations_loewner_bounds.2.2.2.1⟩
  have hpLower :
      (63427 / 100000 : ℝ) * (123896 / 1000000) < β * c13 :=
    mul_lt_mul_of_nonneg hβ.1 hc13.1 (by norm_num) (by norm_num)
  have hpUpper :
      β * c13 < (6343 / 10000 : ℝ) * (123898 / 1000000) :=
    mul_lt_mul_of_nonneg hβ.2 hc13.2
      (by linarith [hc13.1]) (by linarith [hβ.1])
  have hm := oddPolynomialMoment_bounds
  unfold oddPerturbationUpper13 oddPerturbationUpperTaylor13
    oddPerturbationBase13
  dsimp only [β, c13] at hpLower hpUpper
  rw [abs_lt]
  constructor <;> nlinarith

private theorem upper33_sub_taylor_lower :
    (7 / 1000000 : ℝ) <
      oddPerturbationUpper33 - oddPerturbationUpperTaylor33 := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c33 : ℝ := oddStructuralCorrelation33
    (factorTwoPrimeShift / yoshidaEndpointA)
  have hlog := strict_log_two_fine_bounds.1
  have hα := log_two_div_sqrt_two_kernel_lower
  have hβ : (63427 / 100000 : ℝ) < β := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds.1
  have hc33 : (2911 / 100000 : ℝ) < c33 := by
    simpa only [c33] using
      oddPrimeCorrelations_loewner_bounds.2.2.2.2.1
  have hpLower :
      (63427 / 100000 : ℝ) * (2911 / 100000) < β * c33 :=
    mul_lt_mul_of_nonneg hβ hc33 (by norm_num) (by norm_num)
  have hm := oddPolynomialMoment_bounds.2.2.2.2.2
  unfold oddPerturbationUpper33 oddPerturbationUpperTaylor33
    oddPerturbationBase33
  dsimp only [β, c33] at hpLower
  nlinarith

private theorem upper_sub_taylor_defect_det_pos :
    0 <
      (oddPerturbationUpper11 - oddPerturbationUpperTaylor11) *
          (oddPerturbationUpper33 - oddPerturbationUpperTaylor33) -
        (oddPerturbationUpper13 - oddPerturbationUpperTaylor13) ^ 2 := by
  let d11 := oddPerturbationUpper11 - oddPerturbationUpperTaylor11
  let d13 := oddPerturbationUpper13 - oddPerturbationUpperTaylor13
  let d33 := oddPerturbationUpper33 - oddPerturbationUpperTaylor33
  have h11 : (2 / 1000000 : ℝ) < d11 := by
    simpa only [d11] using upper11_sub_taylor_lower
  have h13 : |d13| < (3 / 1000000 : ℝ) := by
    simpa only [d13] using upper13_sub_taylor_abs_upper
  have h33 : (7 / 1000000 : ℝ) < d33 := by
    simpa only [d33] using upper33_sub_taylor_lower
  have h11pos : 0 < d11 := (by norm_num : (0 : ℝ) < 2 / 1000000).trans h11
  have hprod :
      (2 / 1000000 : ℝ) * (7 / 1000000 : ℝ) < d11 * d33 := by
    calc
      (2 / 1000000 : ℝ) * (7 / 1000000 : ℝ) <
          d11 * (7 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_right h11 (by norm_num)
      _ < d11 * d33 := mul_lt_mul_of_pos_left h33 h11pos
  have hsq : d13 ^ 2 < (3 / 1000000 : ℝ) ^ 2 := by
    rw [abs_lt] at h13
    nlinarith [mul_pos (sub_pos.mpr h13.2)
      (by linarith : 0 < d13 + 3 / 1000000)]
  have hrat :
      (3 / 1000000 : ℝ) ^ 2 <
        (2 / 1000000 : ℝ) * (7 / 1000000 : ℝ) := by
    norm_num
  dsimp only [d11, d13, d33] at hprod hsq ⊢
  nlinarith

private theorem upperTaylor_quadratic_le_upper (c d : ℝ) :
    oddPerturbationUpperTaylor11 * c ^ 2 +
        2 * oddPerturbationUpperTaylor13 * c * d +
        oddPerturbationUpperTaylor33 * d ^ 2 ≤
      oddPerturbationUpper11 * c ^ 2 +
        2 * oddPerturbationUpper13 * c * d +
        oddPerturbationUpper33 * d ^ 2 := by
  let d11 := oddPerturbationUpper11 - oddPerturbationUpperTaylor11
  let d13 := oddPerturbationUpper13 - oddPerturbationUpperTaylor13
  let d33 := oddPerturbationUpper33 - oddPerturbationUpperTaylor33
  have h11 : 0 < d11 := by
    have h := upper11_sub_taylor_lower
    dsimp only [d11]
    nlinarith
  have hdet : 0 < d11 * d33 - d13 ^ 2 := by
    simpa only [d11, d13, d33] using upper_sub_taylor_defect_det_pos
  have hquad : 0 ≤ d11 * c ^ 2 + 2 * d13 * c * d + d33 * d ^ 2 := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (real_twoByTwo_quadratic_pos d11 d13 d33 c d h11 hdet hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  dsimp only [d11, d13, d33] at hquad
  nlinarith

/-- A rational upper Loewner Gram for the same complete odd perturbation.
Together with any lower clean Gram, this gives the odd-minus endpoint by
literal coefficient subtraction. -/
theorem oddPerturbation_quadratic_le_upper (c d : ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoOddStructuralLowProfile c d) ≤
      oddPerturbationUpper11 * c ^ 2 +
        2 * oddPerturbationUpper13 * c * d +
        oddPerturbationUpper33 * d ^ 2 := by
  exact (oddPerturbation_quadratic_le_upperTaylor c d).trans
    (upperTaylor_quadratic_le_upper c d)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
