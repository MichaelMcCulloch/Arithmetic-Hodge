import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenGlobalRemainderStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationKernelStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenGlobalRemainderStructural
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaRegularKernelBound

/-!
# The exact global perturbation kernel model

For an arbitrary continuous real profile, the symmetric perturbation is the
sum of one global degree-six pole-free kernel integral, the two exact Cauchy
poles, and the retained prime atoms.  The only approximation used by later
inequalities is the already-proved global analytic remainder envelope; this
identity itself is exact.
-/

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

private theorem measurable_yoshidaRegularKernel_globalModel :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_factorTwoCenteredSymmetricRegularWeight_globalModel :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_globalModel.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel_globalModel.comp (by fun_prop))

private theorem intervalIntegrable_poleFreeAnalyticError_integrand
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦ (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t
  let g : ℝ → ℝ := fun t ↦ (3 / 8000 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f, oddLowPoleFreeKernel]
    exact ((measurable_const.mul
      measurable_factorTwoCenteredSymmetricRegularWeight_globalModel).sub
        continuous_poleFreeKernelPolynomial6.measurable).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hk := (abs_poleFreeKernel_sub_polynomial_lt
      (⟨ht.1.le, ht.2⟩ : t ∈ Icc (0 : ℝ) 2)).le
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

private theorem intervalIntegrable_evenStructuralPoleWeight_mul_correlation
    (e : ℝ → ℝ) (he : Continuous e) :
    IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * centeredEndpointCorrelation e t)
      volume 0 2 := by
  let C : ℝ → ℝ := centeredEndpointCorrelation e
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous e he
  have hplus : IntervalIntegrable (fun t : ℝ ↦ C t / (2 + t))
      volume 0 2 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hne : 2 + t ≠ 0 := by linarith [ht.1]
    exact hC.continuousAt.div
      (continuousAt_const.add continuousAt_id) hne |>.continuousWithinAt
  have hminus : IntervalIntegrable (fun t : ℝ ↦ C t / (2 - t))
      volume 0 2 := by
    simpa only [C] using
      intervalIntegrable_centeredEndpointCorrelation_div_two_sub e he
  have hsum :=
    (hplus.const_mul (-1 / 2 : ℝ)).add
      (hminus.const_mul (-1 / 2 : ℝ))
  apply hsum.congr
  intro t _ht
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at _ht
  dsimp only [C]
  unfold evenStructuralPoleWeight
  by_cases ht2 : t = 2
  · subst t
    norm_num
    ring
  · have hp : 2 + t ≠ 0 := by linarith [_ht.1]
    have hm : 2 - t ≠ 0 := by
      intro h
      apply ht2
      linarith
    field_simp [hp, hm]
    ring

/-- Exact arbitrary-profile decomposition of the symmetric perturbation into
the global degree-six pole-free model, the two exposed Cauchy poles, and the
two retained prime atoms. -/
theorem factorTwoCenteredSymmetricPerturbation_eq_globalPolynomialKernel
    (e : ℝ → ℝ) (he : Continuous e) :
    factorTwoCenteredSymmetricPerturbation e =
      poleFreeAnalyticError (centeredEndpointCorrelation e) +
        (∫ t : ℝ in 0..2,
          poleFreeKernelPolynomial6 t * centeredEndpointCorrelation e t) +
        (∫ t : ℝ in 0..2,
          evenStructuralPoleWeight t * centeredEndpointCorrelation e t) -
        (Real.log 2 / Real.sqrt 2) * centeredEndpointCorrelation e 0 -
        (Real.log 3 / Real.sqrt 3) * centeredEndpointCorrelation e
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation e
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous e he
  have ha : IntervalIntegrable
      (fun t ↦ (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t)
      volume 0 2 :=
    intervalIntegrable_poleFreeAnalyticError_integrand C hC
  have hp : IntervalIntegrable
      (fun t ↦ poleFreeKernelPolynomial6 t * C t) volume 0 2 :=
    (continuous_poleFreeKernelPolynomial6.mul hC).intervalIntegrable 0 2
  have hπ : IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * C t) volume 0 2 := by
    simpa only [C] using
      intervalIntegrable_evenStructuralPoleWeight_mul_correlation e he
  unfold factorTwoCenteredSymmetricPerturbation
  change yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) -
      (Real.log 2 / Real.sqrt 2) * C 0 -
      (Real.log 3 / Real.sqrt 3) *
        C (factorTwoPrimeShift / yoshidaEndpointA) = _
  rw [endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles C]
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        evenStructuralPoleWeight t) * C t) =
      fun t ↦
        ((oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t +
          poleFreeKernelPolynomial6 t * C t) +
        evenStructuralPoleWeight t * C t by
    funext t
    unfold oddLowPoleFreeKernel
    ring,
    intervalIntegral.integral_add (ha.add hp) hπ,
    intervalIntegral.integral_add ha hp]
  unfold poleFreeAnalyticError
  rfl

/-- Lower model bound obtained by charging the one analytic remainder to
`3 / 40000` of the centered energy. -/
theorem globalPolynomialKernel_sub_energyError_le_perturbation
    (e : ℝ → ℝ) (he : Continuous e) :
    (∫ t : ℝ in 0..2,
        poleFreeKernelPolynomial6 t * centeredEndpointCorrelation e t) +
      (∫ t : ℝ in 0..2,
        evenStructuralPoleWeight t * centeredEndpointCorrelation e t) -
      (Real.log 2 / Real.sqrt 2) * centeredEndpointCorrelation e 0 -
      (Real.log 3 / Real.sqrt 3) * centeredEndpointCorrelation e
        (factorTwoPrimeShift / yoshidaEndpointA) -
      (3 / 40000 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) ≤
        factorTwoCenteredSymmetricPerturbation e := by
  rw [factorTwoCenteredSymmetricPerturbation_eq_globalPolynomialKernel e he]
  have herr :=
    (poleFreeAnalyticError_centeredEndpointCorrelation_mem_energyInterval e he).1
  linarith

/-- Upper model bound obtained by charging the one analytic remainder to
`3 / 40000` of the centered energy. -/
theorem perturbation_le_globalPolynomialKernel_add_energyError
    (e : ℝ → ℝ) (he : Continuous e) :
    factorTwoCenteredSymmetricPerturbation e ≤
      (∫ t : ℝ in 0..2,
        poleFreeKernelPolynomial6 t * centeredEndpointCorrelation e t) +
      (∫ t : ℝ in 0..2,
        evenStructuralPoleWeight t * centeredEndpointCorrelation e t) -
      (Real.log 2 / Real.sqrt 2) * centeredEndpointCorrelation e 0 -
      (Real.log 3 / Real.sqrt 3) * centeredEndpointCorrelation e
        (factorTwoPrimeShift / yoshidaEndpointA) +
      (3 / 40000 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) := by
  rw [factorTwoCenteredSymmetricPerturbation_eq_globalPolynomialKernel e he]
  have herr :=
    (poleFreeAnalyticError_centeredEndpointCorrelation_mem_energyInterval e he).2
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationKernelStructural
