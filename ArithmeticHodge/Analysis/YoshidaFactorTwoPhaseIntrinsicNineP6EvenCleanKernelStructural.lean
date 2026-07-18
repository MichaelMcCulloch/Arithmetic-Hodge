import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenGlobalRemainderStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanKernelStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointRegularCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

/-!
# A global degree-six model for the clean regular quadratic

The clean regular quadratic of an arbitrary continuous real profile is one
exact degree-six correlation integral plus a single global envelope error.
The latter is charged once to the full profile energy.  Nothing here depends
on a finite basis, a subdivision, or sampled kernel values.
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

private theorem intervalIntegrable_regularKernel_mul_local
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

/-- Exact sixth-order decomposition of the clean regular quadratic of an
arbitrary continuous real profile. -/
theorem re_yoshidaEndpointRegularQuadratic_eq_polynomial6_add_error
    (e : ℝ → ℝ) (he : Continuous e) :
    (yoshidaEndpointRegularQuadratic (fun x ↦ (e x : ℂ))).re =
      2 * (∫ t : ℝ in 0..2,
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
          centeredEndpointCorrelation e t) +
        oddCleanRegularEnvelopeError (centeredEndpointCorrelation e) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation e
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous e he
  have htrue : IntervalIntegrable
      (fun t ↦ yoshidaRegularKernel (yoshidaEndpointA * t) * C t)
      volume 0 2 := intervalIntegrable_regularKernel_mul_local C hC
  have hpoly : IntervalIntegrable
      (fun t ↦ yoshidaRegularKernelPolynomial6
        (yoshidaEndpointA * t) * C t) volume 0 2 := by
    exact (by
      unfold yoshidaRegularKernelPolynomial6
      fun_prop : Continuous (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) * C t))
      |>.intervalIntegrable 0 2
  have herr : IntervalIntegrable
      (fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t)
      volume 0 2 := by
    apply (htrue.sub hpoly).congr
    intro t _ht
    ring
  rw [re_yoshidaEndpointRegularQuadratic_eq_correlation e he]
  change 2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (yoshidaEndpointA * t) * C t) = _
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (yoshidaEndpointA * t) * C t) =
      fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t +
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) * C t by
    funext t
    ring,
    intervalIntegral.integral_add herr hpoly]
  unfold oddCleanRegularEnvelopeError
  ring

/-- The clean degree-six replacement error costs at most `1 / 250000` of
the centered energy of the whole profile. -/
theorem abs_oddCleanRegularEnvelopeError_centeredEndpointCorrelation_le_energy
    (e : ℝ → ℝ) (he : Continuous e) :
    |oddCleanRegularEnvelopeError (centeredEndpointCorrelation e)| ≤
      (1 / 250000 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) := by
  have herr := abs_oddCleanRegularEnvelopeError_le
    (centeredEndpointCorrelation e)
    (continuous_centeredEndpointCorrelation_of_continuous e he)
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy e he
  exact herr.trans (mul_le_mul_of_nonneg_left hcorr (by norm_num))

/-- Direct two-sided form of the clean global energy charge. -/
theorem oddCleanRegularEnvelopeError_centeredEndpointCorrelation_mem_energyInterval
    (e : ℝ → ℝ) (he : Continuous e) :
    -(1 / 250000 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) ≤
        oddCleanRegularEnvelopeError (centeredEndpointCorrelation e) ∧
      oddCleanRegularEnvelopeError (centeredEndpointCorrelation e) ≤
        (1 / 250000 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) := by
  simpa only [neg_mul] using
    (abs_le.mp
      (abs_oddCleanRegularEnvelopeError_centeredEndpointCorrelation_le_energy
        e he))

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanKernelStructural
