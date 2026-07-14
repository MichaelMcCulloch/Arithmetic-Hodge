import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseLowSchur

/-!
# A sharp structural lower Gram at the positive even endpoint

The clean lower Gram is combined with the same global pole-free degree-six
model used at the negative endpoint.  Its polynomial moments are integrated
exactly, and its one analytic remainder is charged once to the full coupled
profile energy.  There is no subdivision, sampling, or finite certificate.
-/

private theorem integral_polynomial_eleven
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 + (a₈ * x ^ 8 +
            (a₉ * x ^ 9 + (a₁₀ * x ^ 10 + a₁₁ * x ^ 11))))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

def evenPositivePolynomialMoment00 : ℝ :=
  2 * polynomialD0 + (4 / 3 : ℝ) * polynomialD2 +
    (32 / 15 : ℝ) * polynomialD4 + (32 / 7 : ℝ) * polynomialD6

def evenPositivePolynomialMoment02 : ℝ :=
  (4 / 15 : ℝ) * polynomialD2 +
    (16 / 21 : ℝ) * polynomialD4 + (32 / 15 : ℝ) * polynomialD6

def evenPositivePolynomialMoment22 : ℝ :=
  (16 / 75 : ℝ) * polynomialD4 + (32 / 35 : ℝ) * polynomialD6

theorem integral_polynomialDifference_mul_evenCorrelations :
    (∫ t : ℝ in 0..2,
      poleFreePolynomialDifference t * evenStructuralCorrelation00 t) =
        evenPositivePolynomialMoment00 ∧
      (∫ t : ℝ in 0..2,
        poleFreePolynomialDifference t * evenStructuralCorrelation02 t) =
        evenPositivePolynomialMoment02 ∧
      (∫ t : ℝ in 0..2,
        poleFreePolynomialDifference t * evenStructuralCorrelation22 t) =
        evenPositivePolynomialMoment22 := by
  constructor
  · rw [show (fun t : ℝ ↦
        poleFreePolynomialDifference t * evenStructuralCorrelation00 t) =
      fun t ↦ (2 * polynomialD0) * t ^ 0 +
        ((-polynomialD0) * t ^ 1 +
          ((2 * polynomialD2) * t ^ 2 +
            ((-polynomialD2) * t ^ 3 +
              ((2 * polynomialD4) * t ^ 4 +
                ((-polynomialD4) * t ^ 5 +
                  ((2 * polynomialD6) * t ^ 6 +
                    ((-polynomialD6) * t ^ 7 +
                      (0 * t ^ 8 + (0 * t ^ 9 +
                        (0 * t ^ 10 + 0 * t ^ 11)))))))))) by
      funext t
      rw [poleFreePolynomialDifference_expansion]
      unfold evenStructuralCorrelation00
      ring,
    integral_polynomial_eleven]
    unfold evenPositivePolynomialMoment00
    ring
  · constructor
    · rw [show (fun t : ℝ ↦
          poleFreePolynomialDifference t * evenStructuralCorrelation02 t) =
        fun t ↦ 0 * t ^ 0 +
          ((-polynomialD0) * t ^ 1 +
            (((3 / 2 : ℝ) * polynomialD0) * t ^ 2 +
              ((-(1 / 2 : ℝ) * polynomialD0 - polynomialD2) * t ^ 3 +
                (((3 / 2 : ℝ) * polynomialD2) * t ^ 4 +
                  ((-(1 / 2 : ℝ) * polynomialD2 - polynomialD4) * t ^ 5 +
                    (((3 / 2 : ℝ) * polynomialD4) * t ^ 6 +
                      ((-(1 / 2 : ℝ) * polynomialD4 - polynomialD6) * t ^ 7 +
                        (((3 / 2 : ℝ) * polynomialD6) * t ^ 8 +
                          ((-(1 / 2 : ℝ) * polynomialD6) * t ^ 9 +
                            (0 * t ^ 10 + 0 * t ^ 11)))))))))) by
        funext t
        rw [poleFreePolynomialDifference_expansion]
        unfold evenStructuralCorrelation02
        ring,
      integral_polynomial_eleven]
      unfold evenPositivePolynomialMoment02
      ring
    · rw [show (fun t : ℝ ↦
          poleFreePolynomialDifference t * evenStructuralCorrelation22 t) =
        fun t ↦ ((2 / 5 : ℝ) * polynomialD0) * t ^ 0 +
          ((-polynomialD0) * t ^ 1 +
            (((2 / 5 : ℝ) * polynomialD2) * t ^ 2 +
              (((1 / 2 : ℝ) * polynomialD0 - polynomialD2) * t ^ 3 +
                (((2 / 5 : ℝ) * polynomialD4) * t ^ 4 +
                  ((-(3 / 40 : ℝ) * polynomialD0 +
                      (1 / 2 : ℝ) * polynomialD2 - polynomialD4) * t ^ 5 +
                    (((2 / 5 : ℝ) * polynomialD6) * t ^ 6 +
                      ((-(3 / 40 : ℝ) * polynomialD2 +
                          (1 / 2 : ℝ) * polynomialD4 - polynomialD6) * t ^ 7 +
                        (0 * t ^ 8 +
                          (((1 / 2 : ℝ) * polynomialD6 -
                            (3 / 40 : ℝ) * polynomialD4) * t ^ 9 +
                            (0 * t ^ 10 +
                              (-(3 / 40 : ℝ) * polynomialD6) * t ^ 11)))))))))) by
        funext t
        rw [poleFreePolynomialDifference_expansion]
        unfold evenStructuralCorrelation22
        ring,
      integral_polynomial_eleven]
      unfold evenPositivePolynomialMoment22
      ring

theorem evenPositivePolynomialMoment_bounds :
    (467 / 1250000 : ℝ) ≤ evenPositivePolynomialMoment00 ∧
      evenPositivePolynomialMoment00 ≤ (5399 / 13125000 : ℝ) ∧
      (17 / 2625000 : ℝ) ≤ evenPositivePolynomialMoment02 ∧
      evenPositivePolynomialMoment02 ≤ (6 / 546875 : ℝ) ∧
      (47 / 4687500 : ℝ) ≤ evenPositivePolynomialMoment22 ∧
      evenPositivePolynomialMoment22 ≤ (117 / 10937500 : ℝ) := by
  rcases poleFree_coefficient_bounds with
    ⟨hd0L, hd0U, hd2L, hd2U, hd4L, hd4U, hd6L, hd6U⟩
  unfold evenPositivePolynomialMoment00 evenPositivePolynomialMoment02
    evenPositivePolynomialMoment22 polynomialD0 polynomialD2 polynomialD4
    polynomialD6
  constructor
  · norm_num at hd0L hd2L hd4L hd6L ⊢
    linarith
  constructor
  · norm_num at hd0U hd2U hd4U hd6U ⊢
    linarith
  constructor
  · norm_num at hd2L hd4L hd6L ⊢
    linarith
  constructor
  · norm_num at hd2U hd4U hd6U ⊢
    linarith
  constructor
  · norm_num at hd4L hd6L ⊢
    linarith
  · norm_num at hd4U hd6U ⊢
    linarith

private theorem integral_polynomialDifference_evenProfile (c d : ℝ) :
    (∫ t : ℝ in 0..2,
      poleFreePolynomialDifference t *
        centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d) t) =
      evenPositivePolynomialMoment00 * c ^ 2 +
        2 * evenPositivePolynomialMoment02 * c * d +
        evenPositivePolynomialMoment22 * d ^ 2 := by
  have h00 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation00 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation00; fun_prop)).intervalIntegrable 0 2
  have h02 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation02 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation02; fun_prop)).intervalIntegrable 0 2
  have h22 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation22 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation22; fun_prop)).intervalIntegrable 0 2
  simp_rw [centeredEndpointCorrelation_evenStructuralProfile]
  rw [show (fun t : ℝ ↦
      poleFreePolynomialDifference t *
        (c ^ 2 * evenStructuralCorrelation00 t +
          2 * c * d * evenStructuralCorrelation02 t +
          d ^ 2 * evenStructuralCorrelation22 t)) =
      fun t ↦ c ^ 2 *
          (poleFreePolynomialDifference t * evenStructuralCorrelation00 t) +
        (2 * c * d) *
          (poleFreePolynomialDifference t * evenStructuralCorrelation02 t) +
        d ^ 2 *
          (poleFreePolynomialDifference t * evenStructuralCorrelation22 t) by
    funext t
    ring,
    intervalIntegral.integral_add
      ((h00.const_mul (c ^ 2)).add (h02.const_mul (2 * c * d)))
      (h22.const_mul (d ^ 2)),
    intervalIntegral.integral_add (h00.const_mul (c ^ 2))
      (h02.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_polynomialDifference_mul_evenCorrelations.1,
    integral_polynomialDifference_mul_evenCorrelations.2.1,
    integral_polynomialDifference_mul_evenCorrelations.2.2]
  ring

def evenPositivePerturbationTaylor00 : ℝ :=
  evenStructuralKernelBase00 + evenPositivePolynomialMoment00 - 3 / 4000

def evenPositivePerturbationTaylor02 : ℝ :=
  evenStructuralKernelBase02 + evenPositivePolynomialMoment02

def evenPositivePerturbationTaylor22 : ℝ :=
  evenStructuralKernelBase22 + evenPositivePolynomialMoment22 - 3 / 20000

theorem evenPositivePerturbationTaylor_quadratic_le (c d : ℝ) :
    evenPositivePerturbationTaylor00 * c ^ 2 +
        2 * evenPositivePerturbationTaylor02 * c * d +
        evenPositivePerturbationTaylor22 * d ^ 2 ≤
      factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) := by
  have herr := abs_poleFreeAnalyticError_profile_le c d
  have herrLower :
      -(3 / 8000 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) ≤
        poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) :=
    by
      simpa only [neg_mul] using neg_le_of_abs_le herr
  rw [factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq,
    evenStructuralRegularError_eq_analytic_add_polynomial
      (centeredEndpointCorrelation (factorTwoEvenStructuralLowProfile c d))
      (continuous_centeredEndpointCorrelation_of_continuous
        (factorTwoEvenStructuralLowProfile c d)
        (continuous_factorTwoEvenStructuralLowProfile c d)),
    integral_polynomialDifference_evenProfile]
  unfold evenPositivePerturbationTaylor00 evenPositivePerturbationTaylor02
    evenPositivePerturbationTaylor22
  nlinarith

def evenPositivePerturbationSharp00 : ℝ := -4569 / 20000

def evenPositivePerturbationSharp02 : ℝ := -20487 / 100000

def evenPositivePerturbationSharp22 : ℝ := -9467 / 50000

private theorem positiveTaylor00_sub_rational_lower :
    (309 / 2500000 : ℝ) <
      evenPositivePerturbationTaylor00 - evenPositivePerturbationSharp00 := by
  have hb := evenStructuralKernelBase00_lower
  have hm := evenPositivePolynomialMoment_bounds.1
  unfold evenPositivePerturbationTaylor00 evenPositivePerturbationSharp00
  norm_num at hb hm ⊢
  linarith

private theorem positiveTaylor02_sub_rational_abs_upper :
    |evenPositivePerturbationTaylor02 - evenPositivePerturbationSharp02| <
      (573 / 4375000 : ℝ) := by
  have hb := evenStructuralKernelBase02_bounds
  have hm := evenPositivePolynomialMoment_bounds
  unfold evenPositivePerturbationTaylor02 evenPositivePerturbationSharp02
  rw [abs_lt]
  constructor <;> norm_num at hb hm ⊢ <;> linarith

private theorem positiveTaylor22_sub_rational_lower :
    (2813 / 18750000 : ℝ) <
      evenPositivePerturbationTaylor22 - evenPositivePerturbationSharp22 := by
  have hb := evenStructuralKernelBase22_lower
  have hm := evenPositivePolynomialMoment_bounds.2.2.2.2.1
  unfold evenPositivePerturbationTaylor22 evenPositivePerturbationSharp22
  norm_num at hb hm ⊢
  linarith

private theorem positivePerturbation_rational_defect_det_pos :
    0 <
      (evenPositivePerturbationTaylor00 - evenPositivePerturbationSharp00) *
          (evenPositivePerturbationTaylor22 - evenPositivePerturbationSharp22) -
        (evenPositivePerturbationTaylor02 - evenPositivePerturbationSharp02) ^ 2 := by
  let d00 := evenPositivePerturbationTaylor00 - evenPositivePerturbationSharp00
  let d02 := evenPositivePerturbationTaylor02 - evenPositivePerturbationSharp02
  let d22 := evenPositivePerturbationTaylor22 - evenPositivePerturbationSharp22
  have h00 : (309 / 2500000 : ℝ) < d00 := by
    simpa only [d00] using positiveTaylor00_sub_rational_lower
  have h02 : |d02| < (573 / 4375000 : ℝ) := by
    simpa only [d02] using positiveTaylor02_sub_rational_abs_upper
  have h22 : (2813 / 18750000 : ℝ) < d22 := by
    simpa only [d22] using positiveTaylor22_sub_rational_lower
  have h00pos : 0 < d00 := (by norm_num : (0 : ℝ) < 309 / 2500000).trans h00
  have hprod :
      (309 / 2500000 : ℝ) * (2813 / 18750000 : ℝ) < d00 * d22 := by
    calc
      (309 / 2500000 : ℝ) * (2813 / 18750000 : ℝ) <
          d00 * (2813 / 18750000 : ℝ) :=
        mul_lt_mul_of_pos_right h00 (by norm_num)
      _ < d00 * d22 := mul_lt_mul_of_pos_left h22 h00pos
  have hsq : d02 ^ 2 < (573 / 4375000 : ℝ) ^ 2 := by
    rw [abs_lt] at h02
    nlinarith [mul_pos (sub_pos.mpr h02.2)
      (by linarith : 0 < d02 + 573 / 4375000)]
  have hrat :
      (573 / 4375000 : ℝ) ^ 2 <
        (309 / 2500000 : ℝ) * (2813 / 18750000 : ℝ) := by
    norm_num
  dsimp only [d00, d02, d22] at hprod hsq ⊢
  nlinarith

private theorem positivePerturbation_rational_le_taylor (c d : ℝ) :
    evenPositivePerturbationSharp00 * c ^ 2 +
        2 * evenPositivePerturbationSharp02 * c * d +
        evenPositivePerturbationSharp22 * d ^ 2 ≤
      evenPositivePerturbationTaylor00 * c ^ 2 +
        2 * evenPositivePerturbationTaylor02 * c * d +
        evenPositivePerturbationTaylor22 * d ^ 2 := by
  let d00 := evenPositivePerturbationTaylor00 - evenPositivePerturbationSharp00
  let d02 := evenPositivePerturbationTaylor02 - evenPositivePerturbationSharp02
  let d22 := evenPositivePerturbationTaylor22 - evenPositivePerturbationSharp22
  have h00 : 0 < d00 := by
    have h := positiveTaylor00_sub_rational_lower
    dsimp only [d00]
    nlinarith
  have hdet : 0 < d00 * d22 - d02 ^ 2 := by
    simpa only [d00, d02, d22] using positivePerturbation_rational_defect_det_pos
  have hquad : 0 ≤ d00 * c ^ 2 + 2 * d02 * c * d + d22 * d ^ 2 := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (real_twoByTwo_quadratic_pos d00 d02 d22 c d h00 hdet hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  dsimp only [d00, d02, d22] at hquad
  nlinarith

theorem evenPositivePerturbationSharp_quadratic_le (c d : ℝ) :
    evenPositivePerturbationSharp00 * c ^ 2 +
        2 * evenPositivePerturbationSharp02 * c * d +
        evenPositivePerturbationSharp22 * d ^ 2 ≤
      factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) := by
  exact (positivePerturbation_rational_le_taylor c d).trans
    (evenPositivePerturbationTaylor_quadratic_le c d)

def evenPositiveEndpointSharp00 : ℝ := 69 / 500

def evenPositiveEndpointSharp02 : ℝ := 6769 / 50000

def evenPositiveEndpointSharp22 : ℝ := 13751 / 100000

theorem evenPositiveEndpointSharp_principal_minors_pos :
    0 < evenPositiveEndpointSharp00 ∧
      0 < evenPositiveEndpointSharp22 ∧
      (1 / 1600 : ℝ) <
        evenPositiveEndpointSharp00 * evenPositiveEndpointSharp22 -
          evenPositiveEndpointSharp02 ^ 2 := by
  norm_num [evenPositiveEndpointSharp00, evenPositiveEndpointSharp02,
    evenPositiveEndpointSharp22]

/-- Direct sharp Loewner lower Gram for the complete positive even endpoint. -/
theorem evenPositiveEndpointSharp_quadratic_le (c d : ℝ) :
    evenPositiveEndpointSharp00 * c ^ 2 +
        2 * evenPositiveEndpointSharp02 * c * d +
        evenPositiveEndpointSharp22 * d ^ 2 ≤
      factorTwoIntrinsicStaticEvenQuadratic 1 c d := by
  have hclean := intrinsicEven_clean_profile_rationalQuadratic_le c d
  have hpert := evenPositivePerturbationSharp_quadratic_le c d
  rw [factorTwoIntrinsicStaticEvenQuadratic_eq_profile,
    factorTwoEndpointPhaseDiagonal]
  norm_num [evenPositiveEndpointSharp00, evenPositiveEndpointSharp02,
    evenPositiveEndpointSharp22, evenPositivePerturbationSharp00,
    evenPositivePerturbationSharp02, evenPositivePerturbationSharp22] at hpert ⊢
  have hprofile : factorTwoEvenStructuralLowProfile c d =
      yoshidaEndpointEvenLowProfile c d := by
    funext x
    unfold factorTwoEvenStructuralLowProfile yoshidaEndpointEvenLowProfile
      centeredEvenP0
    ring
  rw [← hprofile] at hclean
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
