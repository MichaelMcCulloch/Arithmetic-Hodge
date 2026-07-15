import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural perturbation entries for the `P₀/P₂/P₄` plane

The symmetric perturbation is split into its two exact Cauchy poles, a
degree-six pole-free Taylor polynomial, and one uniform analytic remainder.
All integrations below are exact polynomial or logarithmic identities.
-/

private theorem integral_polynomial_nine
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 +
            (a₈ * x ^ 8 + a₉ * x ^ 9))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 +
        a₉ * (r ^ 10 - l ^ 10) / 10 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_inv_two_add :
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

private theorem intervalIntegrable_inv_two_add :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

/-- Exact Cauchy-pole contributions to the three `P₄` correlations. -/
theorem integral_poleWeight_mul_factorTwoIntrinsicP4Correlations :
    (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation04 t) =
        187 / 3 - 90 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation24 t) =
        29 / 3 - 14 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation44 t) =
        7 / 54 - (2 / 9 : ℝ) * Real.log 2 := by
  have h04 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation04 t) =
      ∫ t : ℝ in 0..2,
        (45 - 22 * t + (35 / 4 : ℝ) * t ^ 2 - (7 / 4 : ℝ) * t ^ 3) -
          90 / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight factorTwoIntrinsicP4Correlation04
    field_simp [hp, hm]
    ring
  have h24 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation24 t) =
      ∫ t : ℝ in 0..2,
        (7 - 3 * t + (3 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 5) -
          14 / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight factorTwoIntrinsicP4Correlation24
    field_simp [hp, hm]
    ring
  have h44 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation44 t) =
      ∫ t : ℝ in 0..2,
        ((4 / 9 : ℝ) * t - (13 / 18 : ℝ) * t ^ 3 +
          (55 / 144 : ℝ) * t ^ 5 - (35 / 576 : ℝ) * t ^ 7) -
          (2 / 9 : ℝ) / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight factorTwoIntrinsicP4Correlation44
    field_simp [hp, hm]
    ring
  rw [h04, h24, h44]
  have hpoly04 : IntervalIntegrable
      (fun t : ℝ ↦ 45 - 22 * t + (35 / 4 : ℝ) * t ^ 2 -
        (7 / 4 : ℝ) * t ^ 3) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      45 - 22 * t + (35 / 4 : ℝ) * t ^ 2 - (7 / 4 : ℝ) * t ^ 3))
      |>.intervalIntegrable 0 2
  have hpoly24 : IntervalIntegrable
      (fun t : ℝ ↦ 7 - 3 * t + (3 / 4 : ℝ) * t ^ 3 -
        (1 / 8 : ℝ) * t ^ 5) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      7 - 3 * t + (3 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 5))
      |>.intervalIntegrable 0 2
  have hpoly44 : IntervalIntegrable
      (fun t : ℝ ↦ (4 / 9 : ℝ) * t - (13 / 18 : ℝ) * t ^ 3 +
        (55 / 144 : ℝ) * t ^ 5 - (35 / 576 : ℝ) * t ^ 7) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      (4 / 9 : ℝ) * t - (13 / 18 : ℝ) * t ^ 3 +
        (55 / 144 : ℝ) * t ^ 5 - (35 / 576 : ℝ) * t ^ 7))
      |>.intervalIntegrable 0 2
  constructor
  · rw [show (fun t : ℝ ↦
        (45 - 22 * t + (35 / 4 : ℝ) * t ^ 2 - (7 / 4 : ℝ) * t ^ 3) -
          90 / (2 + t)) =
      fun t ↦
        (45 - 22 * t + (35 / 4 : ℝ) * t ^ 2 - (7 / 4 : ℝ) * t ^ 3) -
          90 * (1 / (2 + t)) by funext t; ring,
      intervalIntegral.integral_sub hpoly04
        (intervalIntegrable_inv_two_add.const_mul 90),
      intervalIntegral.integral_const_mul, integral_inv_two_add]
    rw [show (fun t : ℝ ↦
        45 - 22 * t + (35 / 4 : ℝ) * t ^ 2 - (7 / 4 : ℝ) * t ^ 3) =
      fun t ↦ 45 * t ^ 0 + ((-22 : ℝ) * t ^ 1 +
        ((35 / 4 : ℝ) * t ^ 2 + ((-7 / 4 : ℝ) * t ^ 3 +
          (0 * t ^ 4 + (0 * t ^ 5 +
            (0 * t ^ 6 + (0 * t ^ 7 + (0 * t ^ 8 + 0 * t ^ 9)))))))) by
      funext t; ring, integral_polynomial_nine]
    norm_num
  · constructor
    · rw [show (fun t : ℝ ↦
          (7 - 3 * t + (3 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 5) -
            14 / (2 + t)) =
        fun t ↦
          (7 - 3 * t + (3 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 5) -
            14 * (1 / (2 + t)) by funext t; ring,
        intervalIntegral.integral_sub hpoly24
          (intervalIntegrable_inv_two_add.const_mul 14),
        intervalIntegral.integral_const_mul, integral_inv_two_add]
      rw [show (fun t : ℝ ↦
          7 - 3 * t + (3 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 5) =
        fun t ↦ 7 * t ^ 0 + ((-3 : ℝ) * t ^ 1 + (0 * t ^ 2 +
          ((3 / 4 : ℝ) * t ^ 3 + (0 * t ^ 4 +
            ((-1 / 8 : ℝ) * t ^ 5 +
              (0 * t ^ 6 + (0 * t ^ 7 + (0 * t ^ 8 + 0 * t ^ 9)))))))) by
        funext t; ring, integral_polynomial_nine]
      norm_num
    · rw [show (fun t : ℝ ↦
          ((4 / 9 : ℝ) * t - (13 / 18 : ℝ) * t ^ 3 +
            (55 / 144 : ℝ) * t ^ 5 - (35 / 576 : ℝ) * t ^ 7) -
            (2 / 9 : ℝ) / (2 + t)) =
        fun t ↦
          ((4 / 9 : ℝ) * t - (13 / 18 : ℝ) * t ^ 3 +
            (55 / 144 : ℝ) * t ^ 5 - (35 / 576 : ℝ) * t ^ 7) -
            (2 / 9 : ℝ) * (1 / (2 + t)) by funext t; ring,
        intervalIntegral.integral_sub hpoly44
          (intervalIntegrable_inv_two_add.const_mul (2 / 9 : ℝ)),
        intervalIntegral.integral_const_mul, integral_inv_two_add]
      rw [show (fun t : ℝ ↦
          (4 / 9 : ℝ) * t - (13 / 18 : ℝ) * t ^ 3 +
            (55 / 144 : ℝ) * t ^ 5 - (35 / 576 : ℝ) * t ^ 7) =
        fun t ↦ 0 * t ^ 0 + ((4 / 9 : ℝ) * t ^ 1 + (0 * t ^ 2 +
          ((-13 / 18 : ℝ) * t ^ 3 + (0 * t ^ 4 +
            ((55 / 144 : ℝ) * t ^ 5 + (0 * t ^ 6 +
              ((-35 / 576 : ℝ) * t ^ 7 + (0 * t ^ 8 + 0 * t ^ 9)))))))) by
        funext t; ring, integral_polynomial_nine]
      norm_num

private theorem integral_evenPolynomial6_mul
    (a₀ a₂ a₄ a₆ : ℝ) (C : ℝ → ℝ) (hC : Continuous C) :
    (∫ t : ℝ in 0..2,
      (a₀ + a₂ * t ^ 2 + a₄ * t ^ 4 + a₆ * t ^ 6) * C t) =
      a₀ * (∫ t : ℝ in 0..2, C t) +
        a₂ * (∫ t : ℝ in 0..2, t ^ 2 * C t) +
        a₄ * (∫ t : ℝ in 0..2, t ^ 4 * C t) +
        a₆ * (∫ t : ℝ in 0..2, t ^ 6 * C t) := by
  have h0 : IntervalIntegrable C volume 0 2 := hC.intervalIntegrable 0 2
  have h2 : IntervalIntegrable (fun t : ℝ ↦ t ^ 2 * C t) volume 0 2 :=
    ((continuous_id.pow 2).mul hC).intervalIntegrable 0 2
  have h4 : IntervalIntegrable (fun t : ℝ ↦ t ^ 4 * C t) volume 0 2 :=
    ((continuous_id.pow 4).mul hC).intervalIntegrable 0 2
  have h6 : IntervalIntegrable (fun t : ℝ ↦ t ^ 6 * C t) volume 0 2 :=
    ((continuous_id.pow 6).mul hC).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (a₀ + a₂ * t ^ 2 + a₄ * t ^ 4 + a₆ * t ^ 6) * C t) =
    fun t ↦ a₀ * C t + a₂ * (t ^ 2 * C t) +
      a₄ * (t ^ 4 * C t) + a₆ * (t ^ 6 * C t) by
    funext t
    ring,
    intervalIntegral.integral_add
      (((h0.const_mul a₀).add (h2.const_mul a₂)).add (h4.const_mul a₄))
      (h6.const_mul a₆),
    intervalIntegral.integral_add
      ((h0.const_mul a₀).add (h2.const_mul a₂)) (h4.const_mul a₄),
    intervalIntegral.integral_add (h0.const_mul a₀) (h2.const_mul a₂)]
  repeat rw [intervalIntegral.integral_const_mul]

/-- Exact degree-six pole-free contributions.  Orthogonality kills every
coefficient through degree two for `C₀₄`, through degree four for `C₂₄`, and
the entire polynomial for `C₄₄`. -/
theorem integral_poleFreeKernelPolynomial6_mul_factorTwoIntrinsicP4Correlations :
    (∫ t : ℝ in 0..2,
      poleFreeKernelPolynomial6 t * factorTwoIntrinsicP4Correlation04 t) =
        poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
          poleFreeCoeff6 yoshidaEndpointA * (32 / 99) ∧
      (∫ t : ℝ in 0..2,
        poleFreeKernelPolynomial6 t * factorTwoIntrinsicP4Correlation24 t) =
        poleFreeCoeff6 yoshidaEndpointA * (32 / 315) ∧
      (∫ t : ℝ in 0..2,
        poleFreeKernelPolynomial6 t * factorTwoIntrinsicP4Correlation44 t) = 0 := by
  have h04 := factorTwoIntrinsicP4Correlation04_moments
  have h24 := factorTwoIntrinsicP4Correlation24_moments
  have h44 := factorTwoIntrinsicP4Correlation44_moments
  constructor
  · rw [show (fun t : ℝ ↦
        poleFreeKernelPolynomial6 t * factorTwoIntrinsicP4Correlation04 t) =
      fun t ↦
        (poleFreeCoeff0 yoshidaEndpointA +
          poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
          poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
          poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
            factorTwoIntrinsicP4Correlation04 t by
      funext t
      rw [poleFreeKernelPolynomial6_expansion],
      integral_evenPolynomial6_mul _ _ _ _ _
        continuous_factorTwoIntrinsicP4Correlation04,
      h04.1, h04.2.1, h04.2.2.1, h04.2.2.2]
    ring
  · constructor
    · rw [show (fun t : ℝ ↦
          poleFreeKernelPolynomial6 t * factorTwoIntrinsicP4Correlation24 t) =
        fun t ↦
          (poleFreeCoeff0 yoshidaEndpointA +
            poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
            poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
            poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
              factorTwoIntrinsicP4Correlation24 t by
        funext t
        rw [poleFreeKernelPolynomial6_expansion],
        integral_evenPolynomial6_mul _ _ _ _ _
          continuous_factorTwoIntrinsicP4Correlation24,
        h24.1, h24.2.1, h24.2.2.1, h24.2.2.2]
      ring
    · rw [show (fun t : ℝ ↦
          poleFreeKernelPolynomial6 t * factorTwoIntrinsicP4Correlation44 t) =
        fun t ↦
          (poleFreeCoeff0 yoshidaEndpointA +
            poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
            poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
            poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
              factorTwoIntrinsicP4Correlation44 t by
        funext t
        rw [poleFreeKernelPolynomial6_expansion],
        integral_evenPolynomial6_mul _ _ _ _ _
          continuous_factorTwoIntrinsicP4Correlation44,
        h44.1, h44.2.1, h44.2.2.1, h44.2.2.2]
      ring

private theorem endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles
    (C : ℝ → ℝ) :
    yoshidaEndpointA *
        (∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) =
      ∫ t : ℝ in 0..2,
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
          evenStructuralPoleWeight t) * C t := by
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
      unfold evenStructuralPoleWeight
      ring

private theorem intervalIntegrable_regularWeight_mul
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦ yoshidaEndpointA *
        factorTwoCenteredSymmetricRegularWeight t * C t) volume 0 2 := by
  have he :=
    YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided.intervalIntegrable_poleFreeAnalyticError
      C hC
  have hp : IntervalIntegrable
      (fun t ↦ poleFreeKernelPolynomial6 t * C t) volume 0 2 :=
    (continuous_poleFreeKernelPolynomial6.mul hC).intervalIntegrable 0 2
  apply (he.add hp).congr
  intro t _ht
  unfold oddLowPoleFreeKernel
  ring

private theorem integral_regularWeight_mul_eq_analytic_poly
    (C : ℝ → ℝ) (hC : Continuous C) :
    (∫ t : ℝ in 0..2,
      yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t * C t) =
      poleFreeAnalyticError C +
        ∫ t : ℝ in 0..2, poleFreeKernelPolynomial6 t * C t := by
  have he :=
    YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided.intervalIntegrable_poleFreeAnalyticError
      C hC
  have hp : IntervalIntegrable
      (fun t ↦ poleFreeKernelPolynomial6 t * C t) volume 0 2 :=
    (continuous_poleFreeKernelPolynomial6.mul hC).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t * C t) =
    fun t ↦
      (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t +
        poleFreeKernelPolynomial6 t * C t by
    funext t
    unfold oddLowPoleFreeKernel
    ring,
    intervalIntegral.integral_add he hp]
  rfl

private theorem intervalIntegrable_pole04 :
    IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation04 t)
      volume 0 2 := by
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦ 45 - 22 * t + (35 / 4 : ℝ) * t ^ 2 -
        (7 / 4 : ℝ) * t ^ 3) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      45 - 22 * t + (35 / 4 : ℝ) * t ^ 2 - (7 / 4 : ℝ) * t ^ 3))
      |>.intervalIntegrable 0 2
  have hbase := hpoly.sub (intervalIntegrable_inv_two_add.const_mul 90)
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
  have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
  unfold evenStructuralPoleWeight factorTwoIntrinsicP4Correlation04
  field_simp [hp, hm]
  ring

private theorem intervalIntegrable_pole24 :
    IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation24 t)
      volume 0 2 := by
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦ 7 - 3 * t + (3 / 4 : ℝ) * t ^ 3 -
        (1 / 8 : ℝ) * t ^ 5) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      7 - 3 * t + (3 / 4 : ℝ) * t ^ 3 - (1 / 8 : ℝ) * t ^ 5))
      |>.intervalIntegrable 0 2
  have hbase := hpoly.sub (intervalIntegrable_inv_two_add.const_mul 14)
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
  have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
  unfold evenStructuralPoleWeight factorTwoIntrinsicP4Correlation24
  field_simp [hp, hm]
  ring

private theorem intervalIntegrable_pole44 :
    IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation44 t)
      volume 0 2 := by
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦ (4 / 9 : ℝ) * t - (13 / 18 : ℝ) * t ^ 3 +
        (55 / 144 : ℝ) * t ^ 5 - (35 / 576 : ℝ) * t ^ 7) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      (4 / 9 : ℝ) * t - (13 / 18 : ℝ) * t ^ 3 +
        (55 / 144 : ℝ) * t ^ 5 - (35 / 576 : ℝ) * t ^ 7))
      |>.intervalIntegrable 0 2
  have hbase := hpoly.sub
    (intervalIntegrable_inv_two_add.const_mul (2 / 9 : ℝ))
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
  have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
  unfold evenStructuralPoleWeight factorTwoIntrinsicP4Correlation44
  field_simp [hp, hm]
  ring

private theorem integral_regular_poles_mul_factorTwoIntrinsicP4Correlations :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        evenStructuralPoleWeight t) * factorTwoIntrinsicP4Correlation04 t) =
        poleFreeAnalyticError factorTwoIntrinsicP4Correlation04 +
          poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
          poleFreeCoeff6 yoshidaEndpointA * (32 / 99) +
          187 / 3 - 90 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
          evenStructuralPoleWeight t) * factorTwoIntrinsicP4Correlation24 t) =
        poleFreeAnalyticError factorTwoIntrinsicP4Correlation24 +
          poleFreeCoeff6 yoshidaEndpointA * (32 / 315) +
          29 / 3 - 14 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
          evenStructuralPoleWeight t) * factorTwoIntrinsicP4Correlation44 t) =
        poleFreeAnalyticError factorTwoIntrinsicP4Correlation44 +
          7 / 54 - (2 / 9 : ℝ) * Real.log 2 := by
  rcases integral_poleWeight_mul_factorTwoIntrinsicP4Correlations with
    ⟨hp04, hp24, hp44⟩
  rcases integral_poleFreeKernelPolynomial6_mul_factorTwoIntrinsicP4Correlations with
    ⟨hq04, hq24, hq44⟩
  constructor
  · rw [show (fun t : ℝ ↦
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
          evenStructuralPoleWeight t) * factorTwoIntrinsicP4Correlation04 t) =
      fun t ↦
        yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t *
          factorTwoIntrinsicP4Correlation04 t +
        evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation04 t by
      funext t; ring,
      intervalIntegral.integral_add
        (intervalIntegrable_regularWeight_mul _
          continuous_factorTwoIntrinsicP4Correlation04) intervalIntegrable_pole04,
      integral_regularWeight_mul_eq_analytic_poly _
        continuous_factorTwoIntrinsicP4Correlation04,
      hq04, hp04]
    ring
  · constructor
    · rw [show (fun t : ℝ ↦
          (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
            evenStructuralPoleWeight t) * factorTwoIntrinsicP4Correlation24 t) =
        fun t ↦
          yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t *
            factorTwoIntrinsicP4Correlation24 t +
          evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation24 t by
        funext t; ring,
        intervalIntegral.integral_add
          (intervalIntegrable_regularWeight_mul _
            continuous_factorTwoIntrinsicP4Correlation24) intervalIntegrable_pole24,
        integral_regularWeight_mul_eq_analytic_poly _
          continuous_factorTwoIntrinsicP4Correlation24,
        hq24, hp24]
      ring
    · rw [show (fun t : ℝ ↦
          (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
            evenStructuralPoleWeight t) * factorTwoIntrinsicP4Correlation44 t) =
        fun t ↦
          yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t *
            factorTwoIntrinsicP4Correlation44 t +
          evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation44 t by
        funext t; ring,
        intervalIntegral.integral_add
          (intervalIntegrable_regularWeight_mul _
            continuous_factorTwoIntrinsicP4Correlation44) intervalIntegrable_pole44,
        integral_regularWeight_mul_eq_analytic_poly _
          continuous_factorTwoIntrinsicP4Correlation44,
        hq44, hp44]
      ring

/-- Exact non-remainder part of the negative-endpoint `P₀-P₄` perturbation. -/
def factorTwoIntrinsicP4PerturbationBase04 : ℝ :=
  poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
    poleFreeCoeff6 yoshidaEndpointA * (32 / 99) +
    187 / 3 - 90 * Real.log 2 -
    (Real.log 3 / Real.sqrt 3) * factorTwoIntrinsicP4Correlation04
      (factorTwoPrimeShift / yoshidaEndpointA)

/-- Exact non-remainder part of the negative-endpoint `P₂-P₄` perturbation. -/
def factorTwoIntrinsicP4PerturbationBase24 : ℝ :=
  poleFreeCoeff6 yoshidaEndpointA * (32 / 315) +
    29 / 3 - 14 * Real.log 2 -
    (Real.log 3 / Real.sqrt 3) * factorTwoIntrinsicP4Correlation24
      (factorTwoPrimeShift / yoshidaEndpointA)

/-- Exact non-remainder part of the negative-endpoint `P₄` perturbation. -/
def factorTwoIntrinsicP4PerturbationBase44 : ℝ :=
  7 / 54 - (2 / 9 : ℝ) * Real.log 2 -
    (Real.log 2 / Real.sqrt 2) * (2 / 9) -
    (Real.log 3 / Real.sqrt 3) * factorTwoIntrinsicP4Correlation44
      (factorTwoPrimeShift / yoshidaEndpointA)

/-- The three exact perturbation entries: one uniform analytic remainder plus
the explicit pole, polynomial, and retained-prime terms. -/
theorem factorTwoIntrinsicP4_perturbation_structural_eq :
    factorTwoCenteredSymmetricPerturbationBilinear
        centeredEvenP0 factorTwoCenteredP4 =
      poleFreeAnalyticError factorTwoIntrinsicP4Correlation04 +
        factorTwoIntrinsicP4PerturbationBase04 ∧
      factorTwoCenteredSymmetricPerturbationBilinear
          centeredEvenP2 factorTwoCenteredP4 =
        poleFreeAnalyticError factorTwoIntrinsicP4Correlation24 +
          factorTwoIntrinsicP4PerturbationBase24 ∧
      factorTwoCenteredSymmetricPerturbation factorTwoCenteredP4 =
        poleFreeAnalyticError factorTwoIntrinsicP4Correlation44 +
          factorTwoIntrinsicP4PerturbationBase44 := by
  rcases integral_regular_poles_mul_factorTwoIntrinsicP4Correlations with
    ⟨h04, h24, h44⟩
  constructor
  · unfold factorTwoCenteredSymmetricPerturbationBilinear
    simp_rw [factorTwoCenteredCorrelationBilinear_p0_p4]
    rw [endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles, h04]
    unfold factorTwoIntrinsicP4PerturbationBase04
      factorTwoIntrinsicP4Correlation04
    ring
  · constructor
    · unfold factorTwoCenteredSymmetricPerturbationBilinear
      simp_rw [factorTwoCenteredCorrelationBilinear_p2_p4]
      rw [endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles, h24]
      unfold factorTwoIntrinsicP4PerturbationBase24
        factorTwoIntrinsicP4Correlation24
      ring
    · rw [← factorTwoCenteredSymmetricPerturbationBilinear_self]
      unfold factorTwoCenteredSymmetricPerturbationBilinear
      simp_rw [factorTwoCenteredCorrelationBilinear_self,
        centeredEndpointCorrelation_p4]
      rw [endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles, h44]
      unfold factorTwoIntrinsicP4PerturbationBase44
        factorTwoIntrinsicP4Correlation44
      ring


end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
