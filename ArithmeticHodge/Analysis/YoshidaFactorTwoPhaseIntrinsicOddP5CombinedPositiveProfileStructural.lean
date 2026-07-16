import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedPositiveProfileStructural

noncomputable section

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoStructuralConstantBounds
open YoshidaRegularKernelBound

/-!
# The correlated positive-endpoint odd `P5` completion tail

The negative static determinant carries the completed odd direction

`r = (44161 / 40320) P1 - (15 / 8) P3 + P5`.

Its rational low `P1/P3` square is handled by the five-dimensional minor.
This file keeps the remaining `P5` tail as one structural difference before
estimating it.  Its correlation is the autocorrelation of the completed
profile minus the autocorrelation of its low `P1/P3` border; it is not itself
an autocorrelation.  In particular, the exact identity below forms the
diagonal together with its two cancelling crosses.
-/

def minusP5OddPositiveCompletionProfile (x : ℝ) : ℝ :=
  (44161 / 40320 : ℝ) * centeredP1 x -
    (15 / 8 : ℝ) * centeredP3 x + factorTwoCenteredP5 x

def minusP5OddPositiveBorderProfile (x : ℝ) : ℝ :=
  (44161 / 40320 : ℝ) * centeredP1 x -
    (15 / 8 : ℝ) * centeredP3 x

/-- Autocorrelation polynomial of the complete positive odd profile. -/
def minusP5OddPositiveCompletionCorrelation (t : ℝ) : ℝ :=
  (1950193921 / 1625702400 : ℝ) * oddStructuralCorrelation11 t -
    (44161 / 10752 : ℝ) * oddStructuralCorrelation13 t +
    (225 / 64 : ℝ) * oddStructuralCorrelation33 t +
    (44161 / 20160 : ℝ) * oddP5Correlation15 t -
    (15 / 4 : ℝ) * oddP5Correlation35 t + oddP5Correlation55 t

/-- Autocorrelation polynomial of the low `P1/P3` border profile. -/
def minusP5OddPositiveBorderCorrelation (t : ℝ) : ℝ :=
  (1950193921 / 1625702400 : ℝ) * oddStructuralCorrelation11 t -
    (44161 / 10752 : ℝ) * oddStructuralCorrelation13 t +
    (225 / 64 : ℝ) * oddStructuralCorrelation33 t

/-- The exact positive-endpoint `P5` tail occurring in `minusDetW`. -/
def minusP5OddPositiveTail : ℝ :=
  (44161 / 20160 : ℝ) * factorTwoIntrinsicSixUnbalancedOPlus15 -
    (15 / 4 : ℝ) * factorTwoIntrinsicSixUnbalancedOPlus35 +
    factorTwoIntrinsicSixUnbalancedOPlus55

/-- One correlation polynomial for the whole completed positive tail. -/
def minusP5OddPositiveTailCorrelation (t : ℝ) : ℝ :=
  (44161 / 20160 : ℝ) * oddP5Correlation15 t -
    (15 / 4 : ℝ) * oddP5Correlation35 t + oddP5Correlation55 t

theorem minusP5OddPositiveCompletionProfile_polynomial (x : ℝ) :
    minusP5OddPositiveCompletionProfile x =
      (63 / 8 : ℝ) * x ^ 5 - (215 / 16 : ℝ) * x ^ 3 +
        (233161 / 40320 : ℝ) * x := by
  unfold minusP5OddPositiveCompletionProfile centeredP1 centeredP3
    factorTwoCenteredP5
  ring

theorem minusP5OddPositiveBorderProfile_polynomial (x : ℝ) :
    minusP5OddPositiveBorderProfile x =
      -(75 / 16 : ℝ) * x ^ 3 + (157561 / 40320 : ℝ) * x := by
  unfold minusP5OddPositiveBorderProfile centeredP1 centeredP3
  ring

theorem minusP5OddPositiveTailCorrelation_polynomial (t : ℝ) :
    minusP5OddPositiveTailCorrelation t =
      (2 / 11 : ℝ) + (11279 / 20160 : ℝ) * t -
        (4439 / 2880 : ℝ) * t ^ 2 -
        (15601 / 1344 : ℝ) * t ^ 3 +
        (44161 / 1536 : ℝ) * t ^ 4 -
        (88657 / 4608 : ℝ) * t ^ 5 +
        (354961 / 107520 : ℝ) * t ^ 7 -
        (215 / 512 : ℝ) * t ^ 9 + (63 / 2816 : ℝ) * t ^ 11 := by
  unfold minusP5OddPositiveTailCorrelation oddP5Correlation15
    oddP5Correlation35 oddP5Correlation55
  ring

theorem minusP5OddPositiveCompletionCorrelation_polynomial (t : ℝ) :
    minusP5OddPositiveCompletionCorrelation t =
      (53273080331 / 26824089600 : ℝ) -
        (78872161 / 1625702400 : ℝ) * t -
        (3809243 / 322560 : ℝ) * t ^ 2 -
        (16889174879 / 9754214400 : ℝ) * t ^ 3 +
        (44161 / 1536 : ℝ) * t ^ 4 -
        (5437475 / 258048 : ℝ) * t ^ 5 +
        (92959 / 26880 : ℝ) * t ^ 7 -
        (215 / 512 : ℝ) * t ^ 9 + (63 / 2816 : ℝ) * t ^ 11 := by
  unfold minusP5OddPositiveCompletionCorrelation oddStructuralCorrelation11
    oddStructuralCorrelation13 oddStructuralCorrelation33
    oddP5Correlation15 oddP5Correlation35 oddP5Correlation55
  ring

/-- The `P5` tail correlation is exactly the completed autocorrelation with
the rationally handled low-profile autocorrelation removed. -/
theorem minusP5OddPositiveTailCorrelation_eq_completion_sub_border (t : ℝ) :
    minusP5OddPositiveTailCorrelation t =
      minusP5OddPositiveCompletionCorrelation t -
        minusP5OddPositiveBorderCorrelation t := by
  unfold minusP5OddPositiveTailCorrelation
    minusP5OddPositiveCompletionCorrelation
    minusP5OddPositiveBorderCorrelation
  ring

theorem continuous_minusP5OddPositiveCompletionProfile :
    Continuous minusP5OddPositiveCompletionProfile := by
  unfold minusP5OddPositiveCompletionProfile centeredP1 centeredP3
    factorTwoCenteredP5
  fun_prop

theorem continuous_minusP5OddPositiveBorderProfile :
    Continuous minusP5OddPositiveBorderProfile := by
  unfold minusP5OddPositiveBorderProfile centeredP1 centeredP3
  fun_prop

theorem continuous_minusP5OddPositiveTailCorrelation :
    Continuous minusP5OddPositiveTailCorrelation := by
  unfold minusP5OddPositiveTailCorrelation oddP5Correlation15
    oddP5Correlation35 oddP5Correlation55
  fun_prop

theorem continuous_minusP5OddPositiveCompletionCorrelation :
    Continuous minusP5OddPositiveCompletionCorrelation := by
  unfold minusP5OddPositiveCompletionCorrelation oddStructuralCorrelation11
    oddStructuralCorrelation13 oddStructuralCorrelation33
    oddP5Correlation15 oddP5Correlation35 oddP5Correlation55
  fun_prop

theorem continuous_minusP5OddPositiveBorderCorrelation :
    Continuous minusP5OddPositiveBorderCorrelation := by
  unfold minusP5OddPositiveBorderCorrelation oddStructuralCorrelation11
    oddStructuralCorrelation13 oddStructuralCorrelation33
  fun_prop

/-! ## Exact profile-correlation bridges -/

private theorem factorTwoCenteredCorrelationBilinear_add_left_positiveProfile
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear (u + v) w t =
      factorTwoCenteredCorrelationBilinear u w t +
        factorTwoCenteredCorrelationBilinear v w t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_add_left u v w hu hv hw t,
    factorTwoCenteredCrossCorrelation_add_right w u v hw hu hv t]
  ring

private theorem factorTwoCenteredCorrelationBilinear_smul_left_positiveProfile
    (c : ℝ) (u v : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear (c • u) v t =
      c * factorTwoCenteredCorrelationBilinear u v t := by
  simpa using factorTwoCenteredCorrelationBilinear_smul_smul c 1 u v t

theorem centeredEndpointCorrelation_minusP5OddPositiveBorderProfile
    (t : ℝ) :
    centeredEndpointCorrelation minusP5OddPositiveBorderProfile t =
      minusP5OddPositiveBorderCorrelation t := by
  let q : ℝ → ℝ := factorTwoOddStructuralLowProfile
    (44161 / 40320) (-15 / 8)
  have hprofile : minusP5OddPositiveBorderProfile = q := by
    funext x
    dsimp only [q]
    unfold minusP5OddPositiveBorderProfile
      factorTwoOddStructuralLowProfile
    ring
  rw [hprofile, centeredEndpointCorrelation_oddStructuralProfile]
  unfold minusP5OddPositiveBorderCorrelation
  ring

theorem centeredEndpointCorrelation_minusP5OddPositiveCompletionProfile
    (t : ℝ) :
    centeredEndpointCorrelation minusP5OddPositiveCompletionProfile t =
      minusP5OddPositiveCompletionCorrelation t := by
  let q : ℝ → ℝ := factorTwoOddStructuralLowProfile
    (44161 / 40320) (-15 / 8)
  have hq : Continuous q := by
    dsimp only [q]
    exact continuous_factorTwoOddStructuralLowProfile _ _
  have h5 : Continuous factorTwoCenteredP5 :=
    continuous_factorTwoCenteredP5
  have hprofile :
      minusP5OddPositiveCompletionProfile = q + factorTwoCenteredP5 := by
    funext x
    dsimp only [q]
    unfold minusP5OddPositiveCompletionProfile
      factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply]
    ring
  have hqprofile :
      q = (44161 / 40320 : ℝ) • centeredP1 +
        (-15 / 8 : ℝ) • centeredP3 := by
    funext x
    dsimp only [q]
    unfold factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hprofile,
    centeredEndpointCorrelation_add q factorTwoCenteredP5 hq h5 t,
    centeredEndpointCorrelation_oddStructuralProfile,
    hqprofile,
    factorTwoCenteredCorrelationBilinear_add_left_positiveProfile
      ((44161 / 40320 : ℝ) • centeredP1)
      ((-15 / 8 : ℝ) • centeredP3) factorTwoCenteredP5
      ((by unfold centeredP1; fun_prop : Continuous centeredP1).const_smul
        (44161 / 40320 : ℝ))
      ((by unfold centeredP3; fun_prop : Continuous centeredP3).const_smul
        (-15 / 8 : ℝ)) h5 t,
    factorTwoCenteredCorrelationBilinear_smul_left_positiveProfile,
    factorTwoCenteredCorrelationBilinear_smul_left_positiveProfile,
    factorTwoCenteredCorrelationBilinear_p1_p5,
    factorTwoCenteredCorrelationBilinear_p3_p5,
    centeredEndpointCorrelation_p5]
  unfold minusP5OddPositiveCompletionCorrelation
  ring

/-- A first global structural box for the completed positive tail.  Each
input box is itself proved from a global kernel identity; this theorem only
assembles their endpoint-safe signs.  The sharper whole-profile identity
below retains the cancellations analytically. -/
theorem neg_three_sixteenths_lt_minusP5OddPositiveTail :
    (-3 / 16 : ℝ) < minusP5OddPositiveTail := by
  have h15 := factorTwoIntrinsicFourP45Cross15_one_bounds
  have h35 := factorTwoIntrinsicFourP45Cross35_one_bounds
  have h55 := three_hundred_forty_three_two_thousandths_lt_p5_plus
  change
    (131727 / 1000000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedOPlus15 ∧
      factorTwoIntrinsicSixUnbalancedOPlus15 < 131929 / 1000000 at h15
  change
    (172324 / 1000000 : ℝ) <
        factorTwoIntrinsicSixUnbalancedOPlus35 ∧
      factorTwoIntrinsicSixUnbalancedOPlus35 < 172427 / 1000000 at h35
  change
    (343 / 2000 : ℝ) < factorTwoIntrinsicSixUnbalancedOPlus55 at h55
  unfold minusP5OddPositiveTail
  nlinarith [h15.1, h35.2, h55]

/-! ## Exact whole-profile decomposition -/

private theorem poleFreeAnalyticError_add_positiveProfile
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    poleFreeAnalyticError (C + D) =
      poleFreeAnalyticError C + poleFreeAnalyticError D := by
  have hCI := intervalIntegrable_poleFreeAnalyticError C hC
  have hDI := intervalIntegrable_poleFreeAnalyticError D hD
  unfold poleFreeAnalyticError
  rw [show (fun t : ℝ ↦
      (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) *
        (C + D) t) =
      fun t ↦
        (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t +
          (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * D t by
    funext t
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hCI hDI]

private theorem poleFreeAnalyticError_const_mul_positiveProfile
    (c : ℝ) (C : ℝ → ℝ) :
    poleFreeAnalyticError (fun t ↦ c * C t) =
      c * poleFreeAnalyticError C := by
  unfold poleFreeAnalyticError
  rw [show (fun t : ℝ ↦
      (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) *
        (c * C t)) =
      fun t ↦ c *
        ((oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]

theorem poleFreeAnalyticError_minusP5OddPositiveTailCorrelation_eq :
    poleFreeAnalyticError minusP5OddPositiveTailCorrelation =
      (44161 / 20160 : ℝ) * poleFreeAnalyticError oddP5Correlation15 -
        (15 / 4 : ℝ) * poleFreeAnalyticError oddP5Correlation35 +
        poleFreeAnalyticError oddP5Correlation55 := by
  let C15 : ℝ → ℝ := fun t ↦
    (44161 / 20160 : ℝ) * oddP5Correlation15 t
  let C35 : ℝ → ℝ := fun t ↦
    (-15 / 4 : ℝ) * oddP5Correlation35 t
  have h15 : Continuous oddP5Correlation15 := by
    unfold oddP5Correlation15
    fun_prop
  have h35 : Continuous oddP5Correlation35 := by
    unfold oddP5Correlation35
    fun_prop
  have h55 : Continuous oddP5Correlation55 :=
    continuous_oddP5Correlation55
  have hC15 : Continuous C15 := by
    dsimp only [C15]
    exact continuous_const.mul h15
  have hC35 : Continuous C35 := by
    dsimp only [C35]
    exact continuous_const.mul h35
  have hprofile :
      minusP5OddPositiveTailCorrelation =
        C15 + C35 + oddP5Correlation55 := by
    funext t
    dsimp only [C15, C35]
    simp only [Pi.add_apply]
    unfold minusP5OddPositiveTailCorrelation
    ring
  rw [hprofile,
    poleFreeAnalyticError_add_positiveProfile (C15 + C35)
      oddP5Correlation55 (hC15.add hC35) h55,
    poleFreeAnalyticError_add_positiveProfile C15 C35 hC15 hC35]
  dsimp only [C15, C35]
  repeat rw [poleFreeAnalyticError_const_mul_positiveProfile]
  ring

/-- Sixth-order clean regular model of the complete `P5` tail. -/
def minusP5OddPositiveTailCleanPolynomial : ℝ :=
  (44161 / 20160 : ℝ) * oddP5CleanRegularPolynomial15 -
    (15 / 4 : ℝ) * oddP5CleanRegularPolynomial35 +
    oddP5CleanRegularPolynomial55

/-- One signed regular-kernel envelope for the complete `P5` tail. -/
def minusP5OddPositiveTailCleanEnvelope : ℝ :=
  (44161 / 20160 : ℝ) * oddP5CleanRegularEnvelopeError15 -
    (15 / 4 : ℝ) * oddP5CleanRegularEnvelopeError35 +
    oddCleanRegularEnvelopeError oddP5Correlation55

private theorem measurable_yoshidaRegularKernel_positiveProfile :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem regularEnvelope_pointwise_positiveProfile
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

private theorem intervalIntegrable_regularEnvelope_mul_positiveProfile
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaRegularKernel (yoshidaEndpointA * t) -
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 500000 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact ((measurable_yoshidaRegularKernel_positiveProfile.comp
      (measurable_const.mul measurable_id)).sub
        (by unfold yoshidaRegularKernelPolynomial6; fun_prop)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have henv := regularEnvelope_pointwise_positiveProfile htIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg henv.1]
    exact mul_le_mul_of_nonneg_right henv.2.le (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

private theorem oddCleanRegularEnvelopeError_add_positiveProfile
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    oddCleanRegularEnvelopeError (C + D) =
      oddCleanRegularEnvelopeError C + oddCleanRegularEnvelopeError D := by
  have hCI := intervalIntegrable_regularEnvelope_mul_positiveProfile C hC
  have hDI := intervalIntegrable_regularEnvelope_mul_positiveProfile D hD
  unfold oddCleanRegularEnvelopeError
  rw [show (fun t : ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * t) -
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
          (C + D) t) =
      fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t +
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * D t by
    funext t
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hCI hDI]
  ring

private theorem oddCleanRegularEnvelopeError_const_mul_positiveProfile
    (c : ℝ) (C : ℝ → ℝ) :
    oddCleanRegularEnvelopeError (fun t ↦ c * C t) =
      c * oddCleanRegularEnvelopeError C := by
  unfold oddCleanRegularEnvelopeError
  rw [show (fun t : ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * t) -
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
          (c * C t)) =
      fun t ↦ c *
        ((yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- The entrywise expression above is genuinely one signed global envelope
of the complete tail correlation. -/
theorem minusP5OddPositiveTailCleanEnvelope_eq_profile :
    minusP5OddPositiveTailCleanEnvelope =
      oddCleanRegularEnvelopeError minusP5OddPositiveTailCorrelation := by
  let C15 : ℝ → ℝ := fun t ↦
    (44161 / 20160 : ℝ) * oddP5Correlation15 t
  let C35 : ℝ → ℝ := fun t ↦
    (-15 / 4 : ℝ) * oddP5Correlation35 t
  have h15 : Continuous oddP5Correlation15 := by
    unfold oddP5Correlation15
    fun_prop
  have h35 : Continuous oddP5Correlation35 := by
    unfold oddP5Correlation35
    fun_prop
  have hC15 : Continuous C15 := by
    dsimp only [C15]
    exact continuous_const.mul h15
  have hC35 : Continuous C35 := by
    dsimp only [C35]
    exact continuous_const.mul h35
  have hprofile :
      minusP5OddPositiveTailCorrelation =
        C15 + C35 + oddP5Correlation55 := by
    funext t
    dsimp only [C15, C35]
    simp only [Pi.add_apply]
    unfold minusP5OddPositiveTailCorrelation
    ring
  rw [hprofile,
    oddCleanRegularEnvelopeError_add_positiveProfile (C15 + C35)
      oddP5Correlation55 (hC15.add hC35)
      continuous_oddP5Correlation55,
    oddCleanRegularEnvelopeError_add_positiveProfile C15 C35 hC15 hC35]
  dsimp only [C15, C35]
  repeat rw [oddCleanRegularEnvelopeError_const_mul_positiveProfile]
  unfold minusP5OddPositiveTailCleanEnvelope
    oddP5CleanRegularEnvelopeError15 oddP5CleanRegularEnvelopeError35
  ring

/-- The low-profile factor in the exact clean hyperbolic cross. -/
def minusP5OddPositiveTailSinhFactor : ℝ :=
  (44161 / 20160 : ℝ) * oddCleanSinhMoment1 -
    (15 / 4 : ℝ) * oddCleanSinhMoment3 + oddP5CleanSinhMoment

/-- All explicit clean-polynomial, pole, mass, and retained-prime terms of
the positive tail. -/
def minusP5OddPositiveTailAlgebraicBase : ℝ :=
  (44161 / 20160 : ℝ) *
      ((1 / 14 : ℝ) + oddP5PolynomialMoment15 +
        (165 - 238 * Real.log 2)) -
    (15 / 4 : ℝ) *
      ((1 / 9 : ℝ) + oddP5PolynomialMoment35 +
        (25 / 2 - 18 * Real.log 2)) +
    (25402 / 38115 : ℝ) -
    (2 / 11 : ℝ) * (Real.log 2 + yoshidaEndpointScalarMassLoss) +
    (47 / 330 - (2 / 11 : ℝ) * Real.log 2) -
    (Real.log 2 / Real.sqrt 2) * (2 / 11 : ℝ) -
    (Real.log 3 / Real.sqrt 3) *
      minusP5OddPositiveTailCorrelation
        (factorTwoPrimeShift / yoshidaEndpointA) -
    yoshidaEndpointA * minusP5OddPositiveTailCleanPolynomial

/-- Exact whole-profile identity for the completed positive-endpoint tail.
Only one clean regular envelope and one pole-free analytic remainder survive.
-/
theorem minusP5OddPositiveTail_eq_structuralProfile :
    minusP5OddPositiveTail =
      minusP5OddPositiveTailAlgebraicBase + plusP5OddQRawReserve -
        yoshidaEndpointA * minusP5OddPositiveTailCleanEnvelope -
        2 * yoshidaEndpointA * oddP5CleanSinhMoment *
          minusP5OddPositiveTailSinhFactor +
        poleFreeAnalyticError minusP5OddPositiveTailCorrelation := by
  rw [poleFreeAnalyticError_minusP5OddPositiveTailCorrelation_eq]
  unfold minusP5OddPositiveTail minusP5OddPositiveTailAlgebraicBase
    minusP5OddPositiveTailCleanPolynomial
    minusP5OddPositiveTailCleanEnvelope
    minusP5OddPositiveTailSinhFactor
    factorTwoIntrinsicSixUnbalancedOPlus15
    factorTwoIntrinsicSixUnbalancedOPlus35
    factorTwoIntrinsicSixUnbalancedOPlus55
    factorTwoIntrinsicFourP45Cross15 factorTwoIntrinsicFourP45Cross35
    factorTwoIntrinsicP5PhaseDiagonal
  rw [cleanBilinear_p1_p5_eq, cleanBilinear_p3_p5_eq,
    yoshidaEndpointOddCleanQuadratic_p5_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p3_p5_structural_eq,
    factorTwoCenteredSymmetricPerturbation_p5_structural_eq]
  unfold minusP5OddPositiveTailCorrelation
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedPositiveProfileStructural
