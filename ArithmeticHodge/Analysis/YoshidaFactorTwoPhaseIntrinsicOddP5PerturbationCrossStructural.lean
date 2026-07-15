import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural

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
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaRenormalizedGeometricKernel
open YoshidaRegularKernelBound

/-!
# Structural odd low-to-`P5` perturbation crosses

The same global degree-six pole-free kernel used for the `P1/P3` Loewner
Gram is integrated against the two new exact overlap polynomials.  The
analytic remainder is charged once to each complete polarized profile; no
rank cutoff, interval subdivision, or sampled certificate is used.
-/

private theorem integral_polynomial_fifteen
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 + (a₈ * x ^ 8 +
            (a₉ * x ^ 9 + (a₁₀ * x ^ 10 + (a₁₁ * x ^ 11 +
              (a₁₂ * x ^ 12 + (a₁₃ * x ^ 13 +
                (a₁₄ * x ^ 14 + a₁₅ * x ^ 15))))))))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 +
        a₁₂ * (r ^ 13 - l ^ 13) / 13 +
        a₁₃ * (r ^ 14 - l ^ 14) / 14 +
        a₁₄ * (r ^ 15 - l ^ 15) / 15 +
        a₁₅ * (r ^ 16 - l ^ 16) / 16 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_polynomial_eighteen
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 + (a₈ * x ^ 8 +
            (a₉ * x ^ 9 + (a₁₀ * x ^ 10 + (a₁₁ * x ^ 11 +
              (a₁₂ * x ^ 12 + (a₁₃ * x ^ 13 +
                (a₁₄ * x ^ 14 + (a₁₅ * x ^ 15 +
                  (a₁₆ * x ^ 16 + (a₁₇ * x ^ 17 +
                    a₁₈ * x ^ 18)))))))))))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 +
        a₁₂ * (r ^ 13 - l ^ 13) / 13 +
        a₁₃ * (r ^ 14 - l ^ 14) / 14 +
        a₁₄ * (r ^ 15 - l ^ 15) / 15 +
        a₁₅ * (r ^ 16 - l ^ 16) / 16 +
        a₁₆ * (r ^ 17 - l ^ 17) / 17 +
        a₁₇ * (r ^ 18 - l ^ 18) / 18 +
        a₁₈ * (r ^ 19 - l ^ 19) / 19 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-! ## Exact squared masses and analytic remainder budgets -/

private theorem integral_oddP5Correlation15_sq :
    (∫ t : ℝ in 0..2, oddP5Correlation15 t ^ 2) = 16 / 5005 := by
  rw [show (fun t : ℝ ↦ oddP5Correlation15 t ^ 2) = fun t ↦
      0 * t ^ 0 + (0 * t ^ 1 + (1 * t ^ 2 + ((-14 : ℝ) * t ^ 3 +
        (79 * t ^ 4 + ((-945 / 4 : ℝ) * t ^ 5 +
          ((835 / 2 : ℝ) * t ^ 6 + ((-455 : ℝ) * t ^ 7 +
            ((19401 / 64 : ℝ) * t ^ 8 + ((-3591 / 32 : ℝ) * t ^ 9 +
              ((865 / 64 : ℝ) * t ^ 10 + ((315 / 64 : ℝ) * t ^ 11 +
                ((-105 / 64 : ℝ) * t ^ 12 + (0 * t ^ 13 +
                  ((9 / 256 : ℝ) * t ^ 14 + 0 * t ^ 15)))))))))))))) by
    funext t
    unfold oddP5Correlation15
    ring,
    integral_polynomial_fifteen]
  norm_num

private theorem integral_oddP5Correlation35_sq :
    (∫ t : ℝ in 0..2, oddP5Correlation35 t ^ 2) = 4304 / 1119195 := by
  rw [show (fun t : ℝ ↦ oddP5Correlation35 t ^ 2) = fun t ↦
      0 * t ^ 0 + (0 * t ^ 1 + (1 * t ^ 2 + ((-9 : ℝ) * t ^ 3 +
        ((121 / 4 : ℝ) * t ^ 4 + ((-45 : ℝ) * t ^ 5 +
          ((85 / 4 : ℝ) * t ^ 6 + ((135 / 8 : ℝ) * t ^ 7 +
            ((-143 / 8 : ℝ) * t ^ 8 + ((-63 / 16 : ℝ) * t ^ 9 +
              ((125 / 16 : ℝ) * t ^ 10 + ((45 / 128 : ℝ) * t ^ 11 +
                ((-65 / 32 : ℝ) * t ^ 12 + (0 * t ^ 13 +
                  ((173 / 512 : ℝ) * t ^ 14 + (0 * t ^ 15 +
                    ((-35 / 1024 : ℝ) * t ^ 16 + (0 * t ^ 17 +
                      (25 / 16384 : ℝ) * t ^ 18))))))))))))))))) by
    funext t
    unfold oddP5Correlation35
    ring,
    integral_polynomial_eighteen]
  norm_num

private theorem sq_intervalIntegral_mul_le_zero_two
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x : ℝ in 0..2, f x * g x) ^ 2 ≤
      (∫ x : ℝ in 0..2, f x ^ 2) *
        (∫ x : ℝ in 0..2, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 2)
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hgMeas : AEStronglyMeasurable g μ :=
    hg.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (0 : ℝ) 2) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (0 : ℝ) 2) :=
      (hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

theorem integral_abs_oddP5Correlation15_lt :
    (∫ t : ℝ in 0..2, |oddP5Correlation15 t|) < 2 / 25 := by
  have hcs := sq_intervalIntegral_mul_le_zero_two
    (fun _ : ℝ ↦ 1) (fun t ↦ |oddP5Correlation15 t|)
    continuous_const (by unfold oddP5Correlation15; fun_prop)
  simp only [one_mul, one_pow, sq_abs] at hcs
  rw [show (∫ _t : ℝ in 0..2, (1 : ℝ)) = 2 by norm_num,
    integral_oddP5Correlation15_sq] at hcs
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..2, |oddP5Correlation15 t| :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)
  have hrat : (2 : ℝ) * (16 / 5005) < (2 / 25 : ℝ) ^ 2 := by
    norm_num
  nlinarith

theorem integral_abs_oddP5Correlation35_lt :
    (∫ t : ℝ in 0..2, |oddP5Correlation35 t|) < 11 / 125 := by
  have hcs := sq_intervalIntegral_mul_le_zero_two
    (fun _ : ℝ ↦ 1) (fun t ↦ |oddP5Correlation35 t|)
    continuous_const (by unfold oddP5Correlation35; fun_prop)
  simp only [one_mul, one_pow, sq_abs] at hcs
  rw [show (∫ _t : ℝ in 0..2, (1 : ℝ)) = 2 by norm_num,
    integral_oddP5Correlation35_sq] at hcs
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..2, |oddP5Correlation35 t| :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)
  have hrat : (2 : ℝ) * (4304 / 1119195) < (11 / 125 : ℝ) ^ 2 := by
    norm_num
  nlinarith

theorem abs_poleFreeAnalyticError_oddP5Correlation15_lt :
    |poleFreeAnalyticError oddP5Correlation15| < 3 / 100000 := by
  have herr := abs_poleFreeAnalyticError_le oddP5Correlation15
    (by unfold oddP5Correlation15; fun_prop)
  have hcorr := integral_abs_oddP5Correlation15_lt
  nlinarith

theorem abs_poleFreeAnalyticError_oddP5Correlation35_lt :
    |poleFreeAnalyticError oddP5Correlation35| < 33 / 1000000 := by
  have herr := abs_poleFreeAnalyticError_le oddP5Correlation35
    (by unfold oddP5Correlation35; fun_prop)
  have hcorr := integral_abs_oddP5Correlation35_lt
  nlinarith

/-! ## Exact degree-six polynomial moments -/

def oddP5PolynomialMoment15 : ℝ :=
  -(32 / 693 : ℝ) * polynomialD6

def oddP5PolynomialMoment35 : ℝ := 0

theorem integral_polynomialDifference_mul_oddP5Correlations :
    (∫ t : ℝ in 0..2,
        poleFreePolynomialDifference t * oddP5Correlation15 t) =
        oddP5PolynomialMoment15 ∧
      (∫ t : ℝ in 0..2,
        poleFreePolynomialDifference t * oddP5Correlation35 t) =
        oddP5PolynomialMoment35 := by
  constructor
  · rw [show (fun t : ℝ ↦
        poleFreePolynomialDifference t * oddP5Correlation15 t) = fun t ↦
      0 * t ^ 0 + ((-polynomialD0) * t ^ 1 +
        ((7 * polynomialD0) * t ^ 2 +
          ((-15 * polynomialD0 - polynomialD2) * t ^ 3 +
            (((105 / 8 : ℝ) * polynomialD0 + 7 * polynomialD2) * t ^ 4 +
              ((-(35 / 8 : ℝ) * polynomialD0 - 15 * polynomialD2 -
                  polynomialD4) * t ^ 5 +
                (((105 / 8 : ℝ) * polynomialD2 + 7 * polynomialD4) * t ^ 6 +
                  (((3 / 16 : ℝ) * polynomialD0 -
                      (35 / 8 : ℝ) * polynomialD2 - 15 * polynomialD4 -
                      polynomialD6) * t ^ 7 +
                    (((105 / 8 : ℝ) * polynomialD4 + 7 * polynomialD6) * t ^ 8 +
                      (((3 / 16 : ℝ) * polynomialD2 -
                          (35 / 8 : ℝ) * polynomialD4 -
                          15 * polynomialD6) * t ^ 9 +
                        (((105 / 8 : ℝ) * polynomialD6) * t ^ 10 +
                          (((3 / 16 : ℝ) * polynomialD4 -
                            (35 / 8 : ℝ) * polynomialD6) * t ^ 11 +
                            (0 * t ^ 12 + (((3 / 16 : ℝ) * polynomialD6) * t ^ 13 +
                              (0 * t ^ 14 + 0 * t ^ 15)))))))))))))) by
      funext t
      rw [poleFreePolynomialDifference_expansion]
      unfold oddP5Correlation15
      ring,
      integral_polynomial_fifteen]
    unfold oddP5PolynomialMoment15
    ring
  · rw [show (fun t : ℝ ↦
        poleFreePolynomialDifference t * oddP5Correlation35 t) = fun t ↦
      0 * t ^ 0 + ((-polynomialD0) * t ^ 1 +
        (((9 / 2 : ℝ) * polynomialD0) * t ^ 2 +
          ((-5 * polynomialD0 - polynomialD2) * t ^ 3 +
            (((9 / 2 : ℝ) * polynomialD2) * t ^ 4 +
              (((15 / 8 : ℝ) * polynomialD0 - 5 * polynomialD2 -
                  polynomialD4) * t ^ 5 +
                (((9 / 2 : ℝ) * polynomialD4) * t ^ 6 +
                  ((-(7 / 16 : ℝ) * polynomialD0 +
                      (15 / 8 : ℝ) * polynomialD2 - 5 * polynomialD4 -
                      polynomialD6) * t ^ 7 +
                    (((9 / 2 : ℝ) * polynomialD6) * t ^ 8 +
                      (((5 / 128 : ℝ) * polynomialD0 -
                          (7 / 16 : ℝ) * polynomialD2 +
                          (15 / 8 : ℝ) * polynomialD4 -
                          5 * polynomialD6) * t ^ 9 +
                        (0 * t ^ 10 +
                          (((5 / 128 : ℝ) * polynomialD2 -
                              (7 / 16 : ℝ) * polynomialD4 +
                              (15 / 8 : ℝ) * polynomialD6) * t ^ 11 +
                            (0 * t ^ 12 +
                              (((5 / 128 : ℝ) * polynomialD4 -
                                  (7 / 16 : ℝ) * polynomialD6) * t ^ 13 +
                                (0 * t ^ 14 +
                                  ((5 / 128 : ℝ) * polynomialD6) * t ^ 15)))))))))))))) by
      funext t
      rw [poleFreePolynomialDifference_expansion]
      unfold oddP5Correlation35
      ring,
      integral_polynomial_fifteen]
    unfold oddP5PolynomialMoment35
    ring

theorem oddP5PolynomialMoment_bounds :
    (-1 / 40000000 : ℝ) ≤ oddP5PolynomialMoment15 ∧
      oddP5PolynomialMoment15 ≤ 0 ∧
      oddP5PolynomialMoment35 = 0 := by
  rcases poleFree_coefficient_bounds with
    ⟨_d0l, _d0u, _d2l, _d2u, _d4l, _d4u, hd6l, hd6u⟩
  unfold oddP5PolynomialMoment15 oddP5PolynomialMoment35 polynomialD6
  norm_num at hd6l hd6u ⊢
  constructor
  · nlinarith
  · nlinarith

theorem integral_regularQuadratic_mul_oddP5Correlations :
    (∫ t : ℝ in 0..2,
        oddStructuralRegularQuadratic t * oddP5Correlation15 t) = 0 ∧
      (∫ t : ℝ in 0..2,
        oddStructuralRegularQuadratic t * oddP5Correlation35 t) = 0 := by
  constructor
  · rw [show (fun t : ℝ ↦
        oddStructuralRegularQuadratic t * oddP5Correlation15 t) = fun t ↦
      0 * t ^ 0 + ((-79 / 60 : ℝ) * t ^ 1 +
        ((553 / 60 : ℝ) * t ^ 2 + ((-9887 / 500 : ℝ) * t ^ 3 +
          ((69797 / 4000 : ℝ) * t ^ 4 + ((-14689 / 2400 : ℝ) * t ^ 5 +
            ((63 / 200 : ℝ) * t ^ 6 + ((227 / 1600 : ℝ) * t ^ 7 +
              (0 * t ^ 8 + ((9 / 2000 : ℝ) * t ^ 9 +
                (0 * t ^ 10 + (0 * t ^ 11 +
                  (0 * t ^ 12 + (0 * t ^ 13 +
                    (0 * t ^ 14 + 0 * t ^ 15)))))))))))))) by
      funext t
      unfold oddStructuralRegularQuadratic oddP5Correlation15
      ring,
      integral_polynomial_fifteen]
    norm_num
  · rw [show (fun t : ℝ ↦
        oddStructuralRegularQuadratic t * oddP5Correlation35 t) = fun t ↦
      0 * t ^ 0 + ((-79 / 60 : ℝ) * t ^ 1 +
        ((237 / 40 : ℝ) * t ^ 2 + ((-9911 / 1500 : ℝ) * t ^ 3 +
          ((27 / 250 : ℝ) * t ^ 4 + ((1879 / 800 : ℝ) * t ^ 5 +
            (0 * t ^ 6 + ((-2549 / 4800 : ℝ) * t ^ 7 +
              (0 * t ^ 8 + ((7859 / 192000 : ℝ) * t ^ 9 +
                (0 * t ^ 10 + ((3 / 3200 : ℝ) * t ^ 11 +
                  (0 * t ^ 12 + (0 * t ^ 13 +
                    (0 * t ^ 14 + 0 * t ^ 15)))))))))))))) by
      funext t
      unfold oddStructuralRegularQuadratic oddP5Correlation35
      ring,
      integral_polynomial_fifteen]
    norm_num

/-! ## Exact endpoint-pole moments -/

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

private theorem intervalIntegrable_poleWeight_mul_oddP5Correlation15 :
    IntervalIntegrable
      (fun t ↦ oddStructuralPoleWeight t * oddP5Correlation15 t)
      volume 0 2 := by
  have hbase : IntervalIntegrable
      (fun t : ℝ ↦
        (119 - 59 * t + (105 / 4 : ℝ) * t ^ 2 -
          (29 / 4 : ℝ) * t ^ 3 + (3 / 8 : ℝ) * t ^ 5) -
            238 * (1 / (2 + t))) volume 0 2 :=
    ((by fun_prop : Continuous (fun t : ℝ ↦
      119 - 59 * t + (105 / 4 : ℝ) * t ^ 2 -
        (29 / 4 : ℝ) * t ^ 3 + (3 / 8 : ℝ) * t ^ 5)).intervalIntegrable 0 2).sub
      (intervalIntegrable_inv_two_add_local.const_mul 238)
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by
    intro h
    apply htneg2
    linarith
  have hm : 2 - t ≠ 0 := by
    intro h
    apply ht2
    linarith
  unfold oddStructuralPoleWeight oddP5Correlation15
  field_simp [hp, hm]
  ring

private theorem intervalIntegrable_poleWeight_mul_oddP5Correlation35 :
    IntervalIntegrable
      (fun t ↦ oddStructuralPoleWeight t * oddP5Correlation35 t)
      volume 0 2 := by
  have hbase : IntervalIntegrable
      (fun t : ℝ ↦
        (9 - 4 * t + (3 / 2 : ℝ) * t ^ 3 -
          (9 / 16 : ℝ) * t ^ 5 + (5 / 64 : ℝ) * t ^ 7) -
            18 * (1 / (2 + t))) volume 0 2 :=
    ((by fun_prop : Continuous (fun t : ℝ ↦
      9 - 4 * t + (3 / 2 : ℝ) * t ^ 3 -
        (9 / 16 : ℝ) * t ^ 5 + (5 / 64 : ℝ) * t ^ 7)).intervalIntegrable 0 2).sub
      (intervalIntegrable_inv_two_add_local.const_mul 18)
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by
    intro h
    apply htneg2
    linarith
  have hm : 2 - t ≠ 0 := by
    intro h
    apply ht2
    linarith
  unfold oddStructuralPoleWeight oddP5Correlation35
  field_simp [hp, hm]
  ring

theorem integral_poleWeight_mul_oddP5Correlations :
    (∫ t : ℝ in 0..2,
        oddStructuralPoleWeight t * oddP5Correlation15 t) =
        165 - 238 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        oddStructuralPoleWeight t * oddP5Correlation35 t) =
        25 / 2 - 18 * Real.log 2 := by
  have h15 : (∫ t : ℝ in 0..2,
      oddStructuralPoleWeight t * oddP5Correlation15 t) =
      ∫ t : ℝ in 0..2,
        (119 - 59 * t + (105 / 4 : ℝ) * t ^ 2 -
          (29 / 4 : ℝ) * t ^ 3 + (3 / 8 : ℝ) * t ^ 5) -
            238 * (1 / (2 + t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by
      intro h
      apply htneg2
      linarith
    have hm : 2 - t ≠ 0 := by
      intro h
      apply ht2
      linarith
    unfold oddStructuralPoleWeight oddP5Correlation15
    field_simp [hp, hm]
    ring
  have h35 : (∫ t : ℝ in 0..2,
      oddStructuralPoleWeight t * oddP5Correlation35 t) =
      ∫ t : ℝ in 0..2,
        (9 - 4 * t + (3 / 2 : ℝ) * t ^ 3 -
          (9 / 16 : ℝ) * t ^ 5 + (5 / 64 : ℝ) * t ^ 7) -
            18 * (1 / (2 + t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by
      intro h
      apply htneg2
      linarith
    have hm : 2 - t ≠ 0 := by
      intro h
      apply ht2
      linarith
    unfold oddStructuralPoleWeight oddP5Correlation35
    field_simp [hp, hm]
    ring
  rw [h15, h35]
  have hpoly (f : ℝ → ℝ) (hf : Continuous f) :
      IntervalIntegrable f volume 0 2 := hf.intervalIntegrable 0 2
  constructor
  · rw [intervalIntegral.integral_sub
      (hpoly _ (by fun_prop))
      (intervalIntegrable_inv_two_add_local.const_mul 238),
      intervalIntegral.integral_const_mul,
      integral_inv_two_add_local]
    rw [show (fun t : ℝ ↦
        119 - 59 * t + (105 / 4 : ℝ) * t ^ 2 -
          (29 / 4 : ℝ) * t ^ 3 + (3 / 8 : ℝ) * t ^ 5) = fun t ↦
      119 * t ^ 0 + ((-59 : ℝ) * t ^ 1 +
        ((105 / 4 : ℝ) * t ^ 2 + ((-29 / 4 : ℝ) * t ^ 3 +
          (0 * t ^ 4 + ((3 / 8 : ℝ) * t ^ 5 +
            (0 * t ^ 6 + (0 * t ^ 7 + (0 * t ^ 8 + (0 * t ^ 9 +
              (0 * t ^ 10 + (0 * t ^ 11 + (0 * t ^ 12 +
                (0 * t ^ 13 + (0 * t ^ 14 + 0 * t ^ 15)))))))))))))) by
      funext t
      ring,
      integral_polynomial_fifteen]
    ring
  · rw [intervalIntegral.integral_sub
      (hpoly _ (by fun_prop))
      (intervalIntegrable_inv_two_add_local.const_mul 18),
      intervalIntegral.integral_const_mul,
      integral_inv_two_add_local]
    rw [show (fun t : ℝ ↦
        9 - 4 * t + (3 / 2 : ℝ) * t ^ 3 -
          (9 / 16 : ℝ) * t ^ 5 + (5 / 64 : ℝ) * t ^ 7) = fun t ↦
      9 * t ^ 0 + ((-4 : ℝ) * t ^ 1 + (0 * t ^ 2 +
        ((3 / 2 : ℝ) * t ^ 3 + (0 * t ^ 4 +
          ((-9 / 16 : ℝ) * t ^ 5 + (0 * t ^ 6 +
            ((5 / 64 : ℝ) * t ^ 7 + (0 * t ^ 8 + (0 * t ^ 9 +
              (0 * t ^ 10 + (0 * t ^ 11 + (0 * t ^ 12 +
                (0 * t ^ 13 + (0 * t ^ 14 + 0 * t ^ 15)))))))))))))) by
      funext t
      ring,
      integral_polynomial_fifteen]
    ring

/-! ## Exact structural perturbation formulas -/

theorem oddStructuralRegularError_oddP5Correlations_sharp_expansion :
    oddStructuralRegularError oddP5Correlation15 =
        poleFreeAnalyticError oddP5Correlation15 + oddP5PolynomialMoment15 ∧
      oddStructuralRegularError oddP5Correlation35 =
        poleFreeAnalyticError oddP5Correlation35 + oddP5PolynomialMoment35 := by
  constructor
  · have hsplit := evenStructuralRegularError_eq_analytic_add_polynomial
      oddP5Correlation15 (by unfold oddP5Correlation15; fun_prop)
    rw [evenStructuralRegularError,
      integral_polynomialDifference_mul_oddP5Correlations.1] at hsplit
    exact hsplit
  · have hsplit := evenStructuralRegularError_eq_analytic_add_polynomial
      oddP5Correlation35 (by unfold oddP5Correlation35; fun_prop)
    rw [evenStructuralRegularError,
      integral_polynomialDifference_mul_oddP5Correlations.2] at hsplit
    exact hsplit

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

private theorem integral_regular_poles_oddP5Correlation15_eq :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddP5Correlation15 t) =
      oddStructuralRegularError oddP5Correlation15 +
        (165 - 238 * Real.log 2) := by
  have herr := intervalIntegrable_oddStructuralRegularError_local
    oddP5Correlation15 (by unfold oddP5Correlation15; fun_prop)
  have hquad : IntervalIntegrable
      (fun t ↦ oddStructuralRegularQuadratic t * oddP5Correlation15 t)
      volume 0 2 :=
    (by unfold oddStructuralRegularQuadratic oddP5Correlation15; fun_prop :
      Continuous (fun t ↦
        oddStructuralRegularQuadratic t * oddP5Correlation15 t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddP5Correlation15 t) = fun t ↦
      ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddP5Correlation15 t +
        oddStructuralRegularQuadratic t * oddP5Correlation15 t) +
      oddStructuralPoleWeight t * oddP5Correlation15 t by
    funext t
    ring,
    intervalIntegral.integral_add (herr.add hquad)
      intervalIntegrable_poleWeight_mul_oddP5Correlation15,
    intervalIntegral.integral_add herr hquad,
    integral_regularQuadratic_mul_oddP5Correlations.1,
    integral_poleWeight_mul_oddP5Correlations.1]
  unfold oddStructuralRegularError
  ring

private theorem integral_regular_poles_oddP5Correlation35_eq :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddP5Correlation35 t) =
      oddStructuralRegularError oddP5Correlation35 +
        (25 / 2 - 18 * Real.log 2) := by
  have herr := intervalIntegrable_oddStructuralRegularError_local
    oddP5Correlation35 (by unfold oddP5Correlation35; fun_prop)
  have hquad : IntervalIntegrable
      (fun t ↦ oddStructuralRegularQuadratic t * oddP5Correlation35 t)
      volume 0 2 :=
    (by unfold oddStructuralRegularQuadratic oddP5Correlation35; fun_prop :
      Continuous (fun t ↦
        oddStructuralRegularQuadratic t * oddP5Correlation35 t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        oddStructuralPoleWeight t) * oddP5Correlation35 t) = fun t ↦
      ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddP5Correlation35 t +
        oddStructuralRegularQuadratic t * oddP5Correlation35 t) +
      oddStructuralPoleWeight t * oddP5Correlation35 t by
    funext t
    ring,
    intervalIntegral.integral_add (herr.add hquad)
      intervalIntegrable_poleWeight_mul_oddP5Correlation35,
    intervalIntegral.integral_add herr hquad,
    integral_regularQuadratic_mul_oddP5Correlations.2,
    integral_poleWeight_mul_oddP5Correlations.2]
  unfold oddStructuralRegularError
  ring

theorem factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_structural_eq :
    factorTwoCenteredSymmetricPerturbationBilinear centeredP1 factorTwoCenteredP5 =
      poleFreeAnalyticError oddP5Correlation15 + oddP5PolynomialMoment15 +
        (165 - 238 * Real.log 2) -
        (Real.log 3 / Real.sqrt 3) * oddP5Correlation15
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_p1_p5]
  rw [endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles,
    integral_regular_poles_oddP5Correlation15_eq,
    oddStructuralRegularError_oddP5Correlations_sharp_expansion.1]
  norm_num [oddP5Correlation15]

theorem factorTwoCenteredSymmetricPerturbationBilinear_p3_p5_structural_eq :
    factorTwoCenteredSymmetricPerturbationBilinear centeredP3 factorTwoCenteredP5 =
      poleFreeAnalyticError oddP5Correlation35 + oddP5PolynomialMoment35 +
        (25 / 2 - 18 * Real.log 2) -
        (Real.log 3 / Real.sqrt 3) * oddP5Correlation35
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_p3_p5]
  rw [endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles,
    integral_regular_poles_oddP5Correlation35_eq,
    oddStructuralRegularError_oddP5Correlations_sharp_expansion.2]
  norm_num [oddP5Correlation35]

/-! ## Retained-prime correlation boxes -/

private theorem hasDerivAt_oddP5Correlation15 (x : ℝ) :
    HasDerivAt oddP5Correlation15
      (-1 + 14 * x - 45 * x ^ 2 + (105 / 2 : ℝ) * x ^ 3 -
        (175 / 8 : ℝ) * x ^ 4 + (21 / 16 : ℝ) * x ^ 6) x := by
  rw [show oddP5Correlation15 = fun t : ℝ ↦
      -t + 7 * t ^ 2 - 15 * t ^ 3 + (105 / 8 : ℝ) * t ^ 4 -
        (35 / 8 : ℝ) * t ^ 5 + (3 / 16 : ℝ) * t ^ 7 by
    funext t
    unfold oddP5Correlation15
    ring]
  convert ((((((hasDerivAt_id x).neg.add
      (((hasDerivAt_id x).pow 2).const_mul 7)).sub
        (((hasDerivAt_id x).pow 3).const_mul 15)).add
          (((hasDerivAt_id x).pow 4).const_mul (105 / 8))).sub
            (((hasDerivAt_id x).pow 5).const_mul (35 / 8))).add
              (((hasDerivAt_id x).pow 7).const_mul (3 / 16))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem hasDerivAt_oddP5Correlation35 (x : ℝ) :
    HasDerivAt oddP5Correlation35
      (-1 + 9 * x - 15 * x ^ 2 + (75 / 8 : ℝ) * x ^ 4 -
        (49 / 16 : ℝ) * x ^ 6 + (45 / 128 : ℝ) * x ^ 8) x := by
  rw [show oddP5Correlation35 = fun t : ℝ ↦
      -t + (9 / 2 : ℝ) * t ^ 2 - 5 * t ^ 3 +
        (15 / 8 : ℝ) * t ^ 5 - (7 / 16 : ℝ) * t ^ 7 +
        (5 / 128 : ℝ) * t ^ 9 by
    funext t
    unfold oddP5Correlation35
    ring]
  convert ((((((hasDerivAt_id x).neg.add
      (((hasDerivAt_id x).pow 2).const_mul (9 / 2))).sub
        (((hasDerivAt_id x).pow 3).const_mul 5)).add
          (((hasDerivAt_id x).pow 5).const_mul (15 / 8))).sub
            (((hasDerivAt_id x).pow 7).const_mul (7 / 16))).add
              (((hasDerivAt_id x).pow 9).const_mul (5 / 128))) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem oddP5Correlation15_strictMonoOn :
    StrictMonoOn oddP5Correlation15
      (Icc (11699 / 10000 : ℝ) (117 / 100)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (by unfold oddP5Correlation15; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_oddP5Correlation15 x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (2 : ℕ) ≠ 0)
  have hx3lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (3 : ℕ) ≠ 0)
  have hx4hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (4 : ℕ) ≠ 0)
  have hx6lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (6 : ℕ) ≠ 0)
  norm_num at hx2hi hx3lo hx4hi hx6lo ⊢
  nlinarith [hx.1]

private theorem oddP5Correlation35_strictAntiOn :
    StrictAntiOn oddP5Correlation35
      (Icc (11699 / 10000 : ℝ) (117 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold oddP5Correlation35; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_oddP5Correlation35 x).deriv]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hx4hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (4 : ℕ) ≠ 0)
  have hx6lo := pow_lt_pow_left₀ hx.1
    (by norm_num : (0 : ℝ) ≤ 11699 / 10000)
    (by norm_num : (6 : ℕ) ≠ 0)
  have hx8hi := pow_lt_pow_left₀ hx.2 hx0 (by norm_num : (8 : ℕ) ≠ 0)
  norm_num at hx2lo hx4hi hx6lo hx8hi ⊢
  nlinarith [hx.2]

theorem oddP5PrimeCorrelations_bounds :
    (-46373 / 1000000 : ℝ) < oddP5Correlation15
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddP5Correlation15 (factorTwoPrimeShift / yoshidaEndpointA) <
        (-46369 / 1000000 : ℝ) ∧
      (-59731 / 1000000 : ℝ) < oddP5Correlation35
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      oddP5Correlation35 (factorTwoPrimeShift / yoshidaEndpointA) <
        (-59729 / 1000000 : ℝ) := by
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
  have h15lo := oddP5Correlation15_strictMonoOn ha hτmem hτ.1
  have h15hi := oddP5Correlation15_strictMonoOn hτmem hb hτ.2
  have h35lo := oddP5Correlation35_strictAntiOn hτmem hb hτ.2
  have h35hi := oddP5Correlation35_strictAntiOn ha hτmem hτ.1
  dsimp only [τ, a, b] at h15lo h15hi h35lo h35hi ⊢
  constructor
  · calc
      (-46373 / 1000000 : ℝ) < oddP5Correlation15 (116992 / 100000) := by
        norm_num [oddP5Correlation15]
      _ < oddP5Correlation15
          (factorTwoPrimeShift / yoshidaEndpointA) := h15lo
  constructor
  · calc
      oddP5Correlation15 (factorTwoPrimeShift / yoshidaEndpointA) <
          oddP5Correlation15 (116993 / 100000) := h15hi
      _ < (-46369 / 1000000 : ℝ) := by
        norm_num [oddP5Correlation15]
  constructor
  · calc
      (-59731 / 1000000 : ℝ) < oddP5Correlation35 (116993 / 100000) := by
        norm_num [oddP5Correlation35]
      _ < oddP5Correlation35
          (factorTwoPrimeShift / yoshidaEndpointA) := h35lo
  · calc
      oddP5Correlation35 (factorTwoPrimeShift / yoshidaEndpointA) <
          oddP5Correlation35 (116992 / 100000) := h35hi
      _ < (-59729 / 1000000 : ℝ) := by
        norm_num [oddP5Correlation35]

/-! ## Tight perturbation-cross boxes -/

theorem factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_bounds :
    (603 / 10000 : ℝ) <
        factorTwoCenteredSymmetricPerturbationBilinear
          centeredP1 factorTwoCenteredP5 ∧
      factorTwoCenteredSymmetricPerturbationBilinear
          centeredP1 factorTwoCenteredP5 < (121 / 2000 : ℝ) := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c : ℝ := oddP5Correlation15
    (factorTwoPrimeShift / yoshidaEndpointA)
  have herr := abs_poleFreeAnalyticError_oddP5Correlation15_lt
  rw [abs_lt] at herr
  have hm := oddP5PolynomialMoment_bounds
  have hlog := strict_log_two_fine_bounds
  have hβ : (63427 / 100000 : ℝ) < β ∧
      β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds
  have hc : (-46373 / 1000000 : ℝ) < c ∧
      c < (-46369 / 1000000 : ℝ) := by
    exact ⟨by simpa only [c] using oddP5PrimeCorrelations_bounds.1,
      by simpa only [c] using oddP5PrimeCorrelations_bounds.2.1⟩
  have hz : (46369 / 1000000 : ℝ) < -c ∧
      -c < (46373 / 1000000 : ℝ) := by
    constructor <;> linarith
  have hpLower :
      (63427 / 100000 : ℝ) * (46369 / 1000000) < -(β * c) := by
    have hmul := mul_lt_mul_of_nonneg hβ.1 hz.1 (by norm_num) (by norm_num)
    nlinarith
  have hpUpper :
      -(β * c) < (6343 / 10000 : ℝ) * (46373 / 1000000) := by
    have hmul := mul_lt_mul_of_nonneg hβ.2 hz.2
      (by linarith [hβ.1]) (by linarith [hz.1])
    nlinarith
  rw [factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_structural_eq]
  dsimp only [β, c] at hpLower hpUpper
  constructor <;> nlinarith

theorem factorTwoCenteredSymmetricPerturbationBilinear_p3_p5_bounds :
    (153 / 2500 : ℝ) <
        factorTwoCenteredSymmetricPerturbationBilinear
          centeredP3 factorTwoCenteredP5 ∧
      factorTwoCenteredSymmetricPerturbationBilinear
          centeredP3 factorTwoCenteredP5 < (613 / 10000 : ℝ) := by
  let β : ℝ := Real.log 3 / Real.sqrt 3
  let c : ℝ := oddP5Correlation35
    (factorTwoPrimeShift / yoshidaEndpointA)
  have herr := abs_poleFreeAnalyticError_oddP5Correlation35_lt
  rw [abs_lt] at herr
  have hm := oddP5PolynomialMoment_bounds.2.2
  have hlog := strict_log_two_fine_bounds
  have hβ : (63427 / 100000 : ℝ) < β ∧
      β < (6343 / 10000 : ℝ) := by
    simpa only [β] using log_three_div_sqrt_three_kernel_bounds
  have hc : (-59731 / 1000000 : ℝ) < c ∧
      c < (-59729 / 1000000 : ℝ) := by
    exact ⟨by simpa only [c] using oddP5PrimeCorrelations_bounds.2.2.1,
      by simpa only [c] using oddP5PrimeCorrelations_bounds.2.2.2⟩
  have hz : (59729 / 1000000 : ℝ) < -c ∧
      -c < (59731 / 1000000 : ℝ) := by
    constructor <;> linarith
  have hpLower :
      (63427 / 100000 : ℝ) * (59729 / 1000000) < -(β * c) := by
    have hmul := mul_lt_mul_of_nonneg hβ.1 hz.1 (by norm_num) (by norm_num)
    nlinarith
  have hpUpper :
      -(β * c) < (6343 / 10000 : ℝ) * (59731 / 1000000) := by
    have hmul := mul_lt_mul_of_nonneg hβ.2 hz.2
      (by linarith [hβ.1]) (by linarith [hz.1])
    nlinarith
  rw [factorTwoCenteredSymmetricPerturbationBilinear_p3_p5_structural_eq]
  dsimp only [β, c] at hpLower hpUpper
  constructor <;> nlinarith

theorem factorTwoCenteredSymmetricPerturbationBilinear_oddP5_cross_bounds :
    ((603 / 10000 : ℝ) <
        factorTwoCenteredSymmetricPerturbationBilinear
          centeredP1 factorTwoCenteredP5 ∧
      factorTwoCenteredSymmetricPerturbationBilinear
          centeredP1 factorTwoCenteredP5 < (121 / 2000 : ℝ)) ∧
      ((153 / 2500 : ℝ) <
        factorTwoCenteredSymmetricPerturbationBilinear
          centeredP3 factorTwoCenteredP5 ∧
      factorTwoCenteredSymmetricPerturbationBilinear
          centeredP3 factorTwoCenteredP5 < (613 / 10000 : ℝ)) :=
  ⟨factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_bounds,
    factorTwoCenteredSymmetricPerturbationBilinear_p3_p5_bounds⟩
end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
