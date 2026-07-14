import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive

noncomputable section

open YoshidaConstantBounds
open CenteredEndpointCorrelation
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenLowHyperbolic
open YoshidaEndpointEvenLowMatrixAlgebra
open YoshidaEndpointEvenLowPositive
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenSharpScalar
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseStructuralLowData
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel
open YoshidaRegularKernelBound

/-!
# The intrinsic even endpoint through the global regular kernel

The two Cauchy poles and the two retained prime atoms are kept exact.  Only
the pole-free regular kernel is replaced by its global quadratic model.  Most
importantly, its uniform remainder is estimated on the *whole* structural
profile.  Thus it costs the diagonal energy

`(2 c^2 + (2/5) d^2) / 500`

once, rather than three unrelated entry errors.  This coupling is what leaves
a (small) structural determinant margin at the negative endpoint.
-/

def evenStructuralCorrelation00 (t : ℝ) : ℝ := 2 - t

def evenStructuralCorrelation02 (t : ℝ) : ℝ :=
  -t * (t - 2) * (t - 1) / 2

def evenStructuralCorrelation22 (t : ℝ) : ℝ :=
  -(t - 2) *
    (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40

def evenStructuralRegularQuadratic (t : ℝ) : ℝ :=
  79 / 60 + (3 / 125 : ℝ) * t ^ 2

def evenStructuralRegularError (C : ℝ → ℝ) : ℝ :=
  oddStructuralRegularError C

theorem evenStructuralRegularKernelControl :
    ∀ t ∈ Icc (0 : ℝ) 2,
      |yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
        evenStructuralRegularQuadratic t| ≤ 1 / 500 := by
  intro t ht
  simpa only [evenStructuralRegularQuadratic, oddStructuralRegularQuadratic]
    using oddStructuralRegularKernelControl t ht

theorem centeredEndpointCorrelation_evenStructuralProfile
    (c d t : ℝ) :
    centeredEndpointCorrelation (factorTwoEvenStructuralLowProfile c d) t =
      c ^ 2 * evenStructuralCorrelation00 t +
        2 * c * d * evenStructuralCorrelation02 t +
        d ^ 2 * evenStructuralCorrelation22 t := by
  have h0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have h2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  rw [factorTwoEvenStructuralLowProfile_eq_smul_add,
    centeredEndpointCorrelation_add (c • centeredEvenP0)
      (d • centeredEvenP2) (h0.const_smul c) (h2.const_smul d)]
  have hself0 :
      centeredEndpointCorrelation (c • centeredEvenP0) t =
        c ^ 2 * factorTwoCenteredCorrelationBilinear
          centeredEvenP0 centeredEvenP0 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  have hself2 :
      centeredEndpointCorrelation (d • centeredEvenP2) t =
        d ^ 2 * factorTwoCenteredCorrelationBilinear
          centeredEvenP2 centeredEvenP2 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  rw [hself0, hself2,
    factorTwoCenteredCorrelationBilinear_smul_smul,
    factorTwoCenteredCorrelationBilinear_p0_p0,
    factorTwoCenteredCorrelationBilinear_p0_p2,
    factorTwoCenteredCorrelationBilinear_p2_p2]
  unfold evenStructuralCorrelation00 evenStructuralCorrelation02
    evenStructuralCorrelation22
  ring

theorem integral_evenStructuralProfile_sq (c d : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoEvenStructuralLowProfile c d x ^ 2) =
      2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2 := by
  have hprofile : factorTwoEvenStructuralLowProfile c d =
      yoshidaEndpointEvenLowProfile c d := by
    funext x
    unfold factorTwoEvenStructuralLowProfile
      yoshidaEndpointEvenLowProfile centeredEvenP0
    ring
  rw [hprofile]
  exact integral_yoshidaEndpointEvenLowProfile_sq c d

/-- The global kernel remainder is charged once to the complete quadratic
profile.  In particular there is no independent mixed-entry error budget. -/
theorem abs_evenStructuralRegularError_profile_le (c d : ℝ) :
    |evenStructuralRegularError
        (centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d))| ≤
      (1 / 500 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) := by
  have herr := abs_oddStructuralRegularError_le
    oddStructuralRegularKernelControl
    (centeredEndpointCorrelation (factorTwoEvenStructuralLowProfile c d))
    (continuous_centeredEndpointCorrelation_of_continuous
      (factorTwoEvenStructuralLowProfile c d)
      (continuous_factorTwoEvenStructuralLowProfile c d))
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy
    (factorTwoEvenStructuralLowProfile c d)
    (continuous_factorTwoEvenStructuralLowProfile c d)
  have hscaled := mul_le_mul_of_nonneg_left hcorr (by norm_num : (0 : ℝ) ≤ 1 / 500)
  rw [integral_evenStructuralProfile_sq] at hscaled
  exact herr.trans hscaled

/-! ## Exact polynomial moments of the quadratic model -/

private theorem integral_septic
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + a₇ * x ^ 7))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 +
        a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 +
        a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 +
        a₇ * (r ^ 8 - l ^ 8) / 8 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem integral_regularQuadratic_mul_evenStructuralCorrelations :
    (∫ t : ℝ in 0..2,
      evenStructuralRegularQuadratic t * evenStructuralCorrelation00 t) =
        1999 / 750 ∧
      (∫ t : ℝ in 0..2,
        evenStructuralRegularQuadratic t * evenStructuralCorrelation02 t) =
        4 / 625 ∧
      (∫ t : ℝ in 0..2,
        evenStructuralRegularQuadratic t * evenStructuralCorrelation22 t) =
        0 := by
  constructor
  · rw [show (fun t : ℝ ↦
        evenStructuralRegularQuadratic t * evenStructuralCorrelation00 t) =
      fun t ↦ (79 / 30 : ℝ) * t ^ 0 +
        ((-79 / 60 : ℝ) * t ^ 1 + ((6 / 125 : ℝ) * t ^ 2 +
          ((-3 / 125 : ℝ) * t ^ 3 + (0 * t ^ 4 +
            (0 * t ^ 5 + (0 * t ^ 6 + 0 * t ^ 7)))))) by
      funext t
      unfold evenStructuralRegularQuadratic evenStructuralCorrelation00
      ring,
      integral_septic]
    norm_num
  · constructor
    · rw [show (fun t : ℝ ↦
          evenStructuralRegularQuadratic t * evenStructuralCorrelation02 t) =
        fun t ↦ 0 * t ^ 0 + ((-79 / 60 : ℝ) * t ^ 1 +
          ((79 / 40 : ℝ) * t ^ 2 +
            ((-2047 / 3000 : ℝ) * t ^ 3 +
              ((9 / 250 : ℝ) * t ^ 4 +
                ((-3 / 250 : ℝ) * t ^ 5 +
                  (0 * t ^ 6 + 0 * t ^ 7)))))) by
        funext t
        unfold evenStructuralRegularQuadratic evenStructuralCorrelation02
        ring,
        integral_septic]
      norm_num
    · rw [show (fun t : ℝ ↦
          evenStructuralRegularQuadratic t * evenStructuralCorrelation22 t) =
        fun t ↦ (79 / 150 : ℝ) * t ^ 0 +
          ((-79 / 60 : ℝ) * t ^ 1 + ((6 / 625 : ℝ) * t ^ 2 +
            ((1903 / 3000 : ℝ) * t ^ 3 +
              (0 * t ^ 4 +
                ((-347 / 4000 : ℝ) * t ^ 5 +
                  (0 * t ^ 6 +
                    ((-9 / 5000 : ℝ) * t ^ 7))))))) by
        funext t
        unfold evenStructuralRegularQuadratic evenStructuralCorrelation22
        ring,
        integral_septic]
      norm_num

/-! ## Exact contributions of the two exposed Cauchy poles -/

def evenStructuralPoleWeight (t : ℝ) : ℝ :=
  -1 / (2 * (2 + t)) - 1 / (2 * (2 - t))

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

theorem integral_poleWeight_mul_evenStructuralCorrelations :
    (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * evenStructuralCorrelation00 t) =
        -2 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        evenStructuralPoleWeight t * evenStructuralCorrelation02 t) =
        4 - 6 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        evenStructuralPoleWeight t * evenStructuralCorrelation22 t) =
        1 / 5 - (2 / 5 : ℝ) * Real.log 2 := by
  have h00 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * evenStructuralCorrelation00 t) =
      ∫ t : ℝ in 0..2, -2 * (1 / (2 + t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight evenStructuralCorrelation00
    field_simp [hp, hm]
    ring
  have h02 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * evenStructuralCorrelation02 t) =
      ∫ t : ℝ in 0..2, (3 - t) - 6 / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight evenStructuralCorrelation02
    field_simp [hp, hm]
    ring
  have h22 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * evenStructuralCorrelation22 t) =
      ∫ t : ℝ in 0..2,
        ((-3 / 20 : ℝ) * t ^ 3 + (2 / 5 : ℝ) * t) -
          (2 / 5 : ℝ) / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight evenStructuralCorrelation22
    field_simp [hp, hm]
    ring
  rw [h00, h02, h22]
  have hpoly02 : IntervalIntegrable
      (fun t : ℝ ↦ 3 - t) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦ 3 - t))
      |>.intervalIntegrable 0 2
  have hpoly22 : IntervalIntegrable
      (fun t : ℝ ↦ (-3 / 20 : ℝ) * t ^ 3 + (2 / 5 : ℝ) * t)
      volume 0 2 :=
    (by fun_prop : Continuous
      (fun t : ℝ ↦ (-3 / 20 : ℝ) * t ^ 3 + (2 / 5 : ℝ) * t))
      |>.intervalIntegrable 0 2
  constructor
  · rw [intervalIntegral.integral_const_mul, integral_inv_two_add]
  · constructor
    · rw [show (fun t : ℝ ↦ (3 - t) - 6 / (2 + t)) =
          fun t ↦ (3 - t) - 6 * (1 / (2 + t)) by
        funext t; ring,
        intervalIntegral.integral_sub hpoly02
          (intervalIntegrable_inv_two_add.const_mul 6),
        intervalIntegral.integral_const_mul, integral_inv_two_add]
      rw [show (fun t : ℝ ↦ 3 - t) =
          fun t ↦ 3 * t ^ 0 + ((-1 : ℝ) * t ^ 1 +
            (0 * t ^ 2 + (0 * t ^ 3 + (0 * t ^ 4 +
              (0 * t ^ 5 + (0 * t ^ 6 + 0 * t ^ 7)))))) by
        funext t; ring,
        integral_septic]
      norm_num
    · rw [show (fun t : ℝ ↦
          ((-3 / 20 : ℝ) * t ^ 3 + (2 / 5 : ℝ) * t) -
            (2 / 5 : ℝ) / (2 + t)) =
          fun t ↦ ((-3 / 20 : ℝ) * t ^ 3 + (2 / 5 : ℝ) * t) -
            (2 / 5 : ℝ) * (1 / (2 + t)) by
        funext t; ring,
        intervalIntegral.integral_sub hpoly22
          (intervalIntegrable_inv_two_add.const_mul (2 / 5 : ℝ)),
        intervalIntegral.integral_const_mul, integral_inv_two_add]
      rw [show (fun t : ℝ ↦
          (-3 / 20 : ℝ) * t ^ 3 + (2 / 5 : ℝ) * t) =
          fun t ↦ 0 * t ^ 0 + ((2 / 5 : ℝ) * t ^ 1 + (0 * t ^ 2 +
            ((-3 / 20 : ℝ) * t ^ 3 + (0 * t ^ 4 +
              (0 * t ^ 5 + (0 * t ^ 6 + 0 * t ^ 7)))))) by
        funext t; ring,
        integral_septic]
      norm_num

/-! ## Exact regular--pole--prime separation -/

private theorem measurable_yoshidaRegularKernel_even :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_factorTwoCenteredSymmetricRegularWeight_even :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_even.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel_even.comp (by fun_prop))

private theorem intervalIntegrable_evenStructuralRegularError
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          evenStructuralRegularQuadratic t) * C t) volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
      evenStructuralRegularQuadratic t) * C t
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
    exact ((measurable_const.mul
      measurable_factorTwoCenteredSymmetricRegularWeight_even).sub
        (by unfold evenStructuralRegularQuadratic; fun_prop)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have hk := evenStructuralRegularKernelControl t htIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

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

private theorem intervalIntegrable_pole00 :
    IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * evenStructuralCorrelation00 t)
      volume 0 2 := by
  apply (intervalIntegrable_inv_two_add.const_mul (-2 : ℝ)).congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
  have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
  unfold evenStructuralPoleWeight evenStructuralCorrelation00
  field_simp [hp, hm]
  ring

private theorem intervalIntegrable_pole02 :
    IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * evenStructuralCorrelation02 t)
      volume 0 2 := by
  have hbase : IntervalIntegrable
      (fun t : ℝ ↦ (3 - t) - 6 * (1 / (2 + t))) volume 0 2 :=
    ((by fun_prop : Continuous (fun t : ℝ ↦ 3 - t)).intervalIntegrable 0 2).sub
      (intervalIntegrable_inv_two_add.const_mul 6)
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
  have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
  unfold evenStructuralPoleWeight evenStructuralCorrelation02
  field_simp [hp, hm]
  ring

private theorem intervalIntegrable_pole22 :
    IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * evenStructuralCorrelation22 t)
      volume 0 2 := by
  have hbase : IntervalIntegrable
      (fun t : ℝ ↦
        ((-3 / 20 : ℝ) * t ^ 3 + (2 / 5 : ℝ) * t) -
          (2 / 5 : ℝ) * (1 / (2 + t))) volume 0 2 :=
    ((by fun_prop : Continuous
      (fun t : ℝ ↦ (-3 / 20 : ℝ) * t ^ 3 + (2 / 5 : ℝ) * t))
        |>.intervalIntegrable 0 2).sub
      (intervalIntegrable_inv_two_add.const_mul (2 / 5 : ℝ))
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
  have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
  unfold evenStructuralPoleWeight evenStructuralCorrelation22
  field_simp [hp, hm]
  ring

private theorem integral_regular_poles_correlation00_eq :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        evenStructuralPoleWeight t) * evenStructuralCorrelation00 t) =
      evenStructuralRegularError evenStructuralCorrelation00 +
        1999 / 750 - 2 * Real.log 2 := by
  have herr := intervalIntegrable_evenStructuralRegularError
    evenStructuralCorrelation00 (by unfold evenStructuralCorrelation00; fun_prop)
  have hquad : IntervalIntegrable
      (fun t ↦ evenStructuralRegularQuadratic t *
        evenStructuralCorrelation00 t) volume 0 2 :=
    (by unfold evenStructuralRegularQuadratic evenStructuralCorrelation00
        fun_prop : Continuous (fun t ↦ evenStructuralRegularQuadratic t *
          evenStructuralCorrelation00 t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        evenStructuralPoleWeight t) * evenStructuralCorrelation00 t) =
      fun t ↦
        ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          evenStructuralRegularQuadratic t) * evenStructuralCorrelation00 t +
          evenStructuralRegularQuadratic t * evenStructuralCorrelation00 t) +
        evenStructuralPoleWeight t * evenStructuralCorrelation00 t by
    funext t; ring,
    intervalIntegral.integral_add (herr.add hquad) intervalIntegrable_pole00,
    intervalIntegral.integral_add herr hquad,
    integral_regularQuadratic_mul_evenStructuralCorrelations.1,
    integral_poleWeight_mul_evenStructuralCorrelations.1]
  unfold evenStructuralRegularError oddStructuralRegularError
    evenStructuralRegularQuadratic oddStructuralRegularQuadratic
  ring

private theorem integral_regular_poles_correlation02_eq :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        evenStructuralPoleWeight t) * evenStructuralCorrelation02 t) =
      evenStructuralRegularError evenStructuralCorrelation02 +
        2504 / 625 - 6 * Real.log 2 := by
  have herr := intervalIntegrable_evenStructuralRegularError
    evenStructuralCorrelation02 (by unfold evenStructuralCorrelation02; fun_prop)
  have hquad : IntervalIntegrable
      (fun t ↦ evenStructuralRegularQuadratic t *
        evenStructuralCorrelation02 t) volume 0 2 :=
    (by unfold evenStructuralRegularQuadratic evenStructuralCorrelation02
        fun_prop : Continuous (fun t ↦ evenStructuralRegularQuadratic t *
          evenStructuralCorrelation02 t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        evenStructuralPoleWeight t) * evenStructuralCorrelation02 t) =
      fun t ↦
        ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          evenStructuralRegularQuadratic t) * evenStructuralCorrelation02 t +
          evenStructuralRegularQuadratic t * evenStructuralCorrelation02 t) +
        evenStructuralPoleWeight t * evenStructuralCorrelation02 t by
    funext t; ring,
    intervalIntegral.integral_add (herr.add hquad) intervalIntegrable_pole02,
    intervalIntegral.integral_add herr hquad,
    integral_regularQuadratic_mul_evenStructuralCorrelations.2.1,
    integral_poleWeight_mul_evenStructuralCorrelations.2.1]
  unfold evenStructuralRegularError oddStructuralRegularError
    evenStructuralRegularQuadratic oddStructuralRegularQuadratic
  ring

private theorem integral_regular_poles_correlation22_eq :
    (∫ t : ℝ in 0..2,
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        evenStructuralPoleWeight t) * evenStructuralCorrelation22 t) =
      evenStructuralRegularError evenStructuralCorrelation22 +
        1 / 5 - (2 / 5 : ℝ) * Real.log 2 := by
  have herr := intervalIntegrable_evenStructuralRegularError
    evenStructuralCorrelation22 (by unfold evenStructuralCorrelation22; fun_prop)
  have hquad : IntervalIntegrable
      (fun t ↦ evenStructuralRegularQuadratic t *
        evenStructuralCorrelation22 t) volume 0 2 :=
    (by unfold evenStructuralRegularQuadratic evenStructuralCorrelation22
        fun_prop : Continuous (fun t ↦ evenStructuralRegularQuadratic t *
          evenStructuralCorrelation22 t)).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t +
        evenStructuralPoleWeight t) * evenStructuralCorrelation22 t) =
      fun t ↦
        ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          evenStructuralRegularQuadratic t) * evenStructuralCorrelation22 t +
          evenStructuralRegularQuadratic t * evenStructuralCorrelation22 t) +
        evenStructuralPoleWeight t * evenStructuralCorrelation22 t by
    funext t; ring,
    intervalIntegral.integral_add (herr.add hquad) intervalIntegrable_pole22,
    intervalIntegral.integral_add herr hquad,
    integral_regularQuadratic_mul_evenStructuralCorrelations.2.2,
    integral_poleWeight_mul_evenStructuralCorrelations.2.2]
  unfold evenStructuralRegularError oddStructuralRegularError
    evenStructuralRegularQuadratic oddStructuralRegularQuadratic
  ring

/-- Exact three perturbation entries.  The two prime atoms remain literal;
the only remainder is the global pole-free kernel error. -/
theorem factorTwoCenteredSymmetricPerturbation_even_structural_eq :
    factorTwoCenteredSymmetricPerturbation centeredEvenP0 =
        evenStructuralRegularError evenStructuralCorrelation00 +
          1999 / 750 - 2 * Real.log 2 -
          (Real.log 2 / Real.sqrt 2) * 2 -
          (Real.log 3 / Real.sqrt 3) * evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      factorTwoCenteredSymmetricPerturbationBilinear
          centeredEvenP0 centeredEvenP2 =
        evenStructuralRegularError evenStructuralCorrelation02 +
          2504 / 625 - 6 * Real.log 2 -
          (Real.log 3 / Real.sqrt 3) * evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      factorTwoCenteredSymmetricPerturbation centeredEvenP2 =
        evenStructuralRegularError evenStructuralCorrelation22 +
          1 / 5 - (2 / 5 : ℝ) * Real.log 2 -
          (Real.log 2 / Real.sqrt 2) * (2 / 5) -
          (Real.log 3 / Real.sqrt 3) * evenStructuralCorrelation22
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  constructor
  · rw [factorTwoCenteredSymmetricPerturbation_p0_eq]
    rw [show (fun t : ℝ ↦
        factorTwoSymmetricWeight (yoshidaEndpointA * t) * (2 - t)) =
      fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        evenStructuralCorrelation00 t by
      funext t; rfl,
      endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles,
      integral_regular_poles_correlation00_eq]
    unfold evenStructuralCorrelation00
    ring
  · constructor
    · rw [factorTwoCenteredSymmetricPerturbationBilinear_p0_p2_eq]
      rw [show (fun t : ℝ ↦
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            (-t * (t - 2) * (t - 1) / 2)) =
        fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          evenStructuralCorrelation02 t by
        funext t; rfl,
        endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles,
        integral_regular_poles_correlation02_eq]
      unfold evenStructuralCorrelation02
      ring
    · rw [factorTwoCenteredSymmetricPerturbation_p2_eq]
      rw [show (fun t : ℝ ↦
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            (-(t - 2) *
              (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40)) =
        fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          evenStructuralCorrelation22 t by
        funext t; rfl,
        endpoint_mul_integral_symmetricWeight_mul_eq_regular_poles,
        integral_regular_poles_correlation22_eq]
      unfold evenStructuralCorrelation22
      ring

theorem evenStructuralRegularError_profile_expansion (c d : ℝ) :
    evenStructuralRegularError
        (centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d)) =
      c ^ 2 * evenStructuralRegularError evenStructuralCorrelation00 +
        2 * c * d * evenStructuralRegularError evenStructuralCorrelation02 +
        d ^ 2 * evenStructuralRegularError evenStructuralCorrelation22 := by
  have h00 := intervalIntegrable_evenStructuralRegularError
    evenStructuralCorrelation00 (by unfold evenStructuralCorrelation00; fun_prop)
  have h02 := intervalIntegrable_evenStructuralRegularError
    evenStructuralCorrelation02 (by unfold evenStructuralCorrelation02; fun_prop)
  have h22 := intervalIntegrable_evenStructuralRegularError
    evenStructuralCorrelation22 (by unfold evenStructuralCorrelation22; fun_prop)
  unfold evenStructuralRegularError oddStructuralRegularError
  simp_rw [centeredEndpointCorrelation_evenStructuralProfile]
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
        oddStructuralRegularQuadratic t) *
        (c ^ 2 * evenStructuralCorrelation00 t +
          2 * c * d * evenStructuralCorrelation02 t +
          d ^ 2 * evenStructuralCorrelation22 t)) =
      fun t ↦ c ^ 2 *
          ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
            evenStructuralRegularQuadratic t) * evenStructuralCorrelation00 t) +
        (2 * c * d) *
          ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
            evenStructuralRegularQuadratic t) * evenStructuralCorrelation02 t) +
        d ^ 2 *
          ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
            evenStructuralRegularQuadratic t) * evenStructuralCorrelation22 t) by
    funext t
    unfold oddStructuralRegularQuadratic evenStructuralRegularQuadratic
    ring,
    intervalIntegral.integral_add
      ((h00.const_mul (c ^ 2)).add (h02.const_mul (2 * c * d)))
      (h22.const_mul (d ^ 2)),
    intervalIntegral.integral_add (h00.const_mul (c ^ 2))
      (h02.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  simp only [evenStructuralRegularQuadratic, oddStructuralRegularQuadratic]

def evenStructuralKernelBase00 : ℝ :=
  1999 / 750 - 2 * Real.log 2 -
    (Real.log 2 / Real.sqrt 2) * 2 -
    (Real.log 3 / Real.sqrt 3) * evenStructuralCorrelation00
      (factorTwoPrimeShift / yoshidaEndpointA)

def evenStructuralKernelBase02 : ℝ :=
  2504 / 625 - 6 * Real.log 2 -
    (Real.log 3 / Real.sqrt 3) * evenStructuralCorrelation02
      (factorTwoPrimeShift / yoshidaEndpointA)

def evenStructuralKernelBase22 : ℝ :=
  1 / 5 - (2 / 5 : ℝ) * Real.log 2 -
    (Real.log 2 / Real.sqrt 2) * (2 / 5) -
    (Real.log 3 / Real.sqrt 3) * evenStructuralCorrelation22
      (factorTwoPrimeShift / yoshidaEndpointA)

/-- Complete structural perturbation: one coupled regular error plus an exact
quadratic containing both Cauchy poles and both retained prime atoms. -/
theorem factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq
    (c d : ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) =
      evenStructuralRegularError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) +
        evenStructuralKernelBase00 * c ^ 2 +
        2 * evenStructuralKernelBase02 * c * d +
        evenStructuralKernelBase22 * d ^ 2 := by
  rw [factorTwoCenteredSymmetricPerturbation_structuralLow,
    factorTwoCenteredSymmetricPerturbation_even_structural_eq.1,
    factorTwoCenteredSymmetricPerturbation_even_structural_eq.2.1,
    factorTwoCenteredSymmetricPerturbation_even_structural_eq.2.2,
    evenStructuralRegularError_profile_expansion]
  unfold evenStructuralKernelBase00 evenStructuralKernelBase02
    evenStructuralKernelBase22
  ring

/-! ## Structural rational bounds for the retained primes -/

theorem strict_log_three_halves_kernel_bounds :
    (4054651 / 10000000 : ℝ) < Real.log (3 / 2) ∧
      Real.log (3 / 2) < (202733 / 500000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (x := (1 / 5 : ℝ))
    (by norm_num) (by norm_num) 6
  have hup := Real.log_div_le_sum_range_add (x := (1 / 5 : ℝ))
    (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

theorem sqrt_two_kernel_bounds :
    (141421 / 100000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < (70711 / 50000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg 2
  constructor <;> nlinarith

theorem sqrt_three_kernel_bounds :
    (34641 / 20000 : ℝ) < Real.sqrt 3 ∧
      Real.sqrt 3 < (86603 / 50000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg 3
  constructor <;> nlinarith

theorem log_two_div_sqrt_two_kernel_lower :
    (12253 / 25000 : ℝ) < Real.log 2 / Real.sqrt 2 := by
  have hlog := strict_log_two_fine_bounds.1
  have hs := sqrt_two_kernel_bounds.2
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [lt_div_iff₀ hspos]
  nlinarith

theorem log_three_div_sqrt_three_kernel_bounds :
    (63427 / 100000 : ℝ) < Real.log 3 / Real.sqrt 3 ∧
      Real.log 3 / Real.sqrt 3 < (6343 / 10000 : ℝ) := by
  have hlog2 := strict_log_two_fine_bounds
  have hlog32 := strict_log_three_halves_kernel_bounds
  have hlog3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    calc
      Real.log 3 = Real.log (2 * (3 / 2 : ℝ)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hs := sqrt_three_kernel_bounds
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hspos, lt_div_iff₀ hspos, hlog3]
  constructor <;> nlinarith

theorem factorTwoPrimeRatio_kernel_bounds :
    (11699 / 10000 : ℝ) < factorTwoPrimeShift / yoshidaEndpointA ∧
      factorTwoPrimeShift / yoshidaEndpointA < (117 / 100 : ℝ) := by
  have hlog2 := strict_log_two_fine_bounds
  have hlog32 := strict_log_three_halves_kernel_bounds
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold factorTwoPrimeShift yoshidaEndpointA
  constructor
  · rw [lt_div_iff₀ (by positivity : 0 < Real.log 2 / 2)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity : 0 < Real.log 2 / 2)]
    nlinarith

theorem primeRatio_evenCorrelation_bounds :
    evenStructuralCorrelation00
        (factorTwoPrimeShift / yoshidaEndpointA) > (83 / 100 : ℝ) ∧
      0 < evenStructuralCorrelation02
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      evenStructuralCorrelation02
          (factorTwoPrimeShift / yoshidaEndpointA) < (1651 / 20000 : ℝ) ∧
      (-1337 / 10000 : ℝ) < evenStructuralCorrelation22
        (factorTwoPrimeShift / yoshidaEndpointA) := by
  let t := factorTwoPrimeShift / yoshidaEndpointA
  have ht := factorTwoPrimeRatio_kernel_bounds
  have ht0 : 0 < t := by dsimp only [t]; linarith
  have ht1 : 1 < t := by dsimp only [t]; linarith
  have ht2 : t < 2 := by dsimp only [t]; linarith
  constructor
  · dsimp only [t] at ht ⊢
    unfold evenStructuralCorrelation00
    linarith
  · constructor
    · dsimp only [t] at ht0 ht1 ht2 ⊢
      unfold evenStructuralCorrelation02
      have hprod : t * (t - 2) * (t - 1) < 0 :=
        mul_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg ht0 (sub_neg.mpr ht2))
          (sub_pos.mpr ht1)
      nlinarith
    · constructor
      · dsimp only [t] at ht ⊢
        unfold evenStructuralCorrelation02
        have hdiff : evenStructuralCorrelation02 (117 / 100) -
            evenStructuralCorrelation02 t =
            (117 / 100 - t) *
              (-((117 / 100 : ℝ) ^ 2 + (117 / 100 : ℝ) * t + t ^ 2) / 2 +
                (3 / 2 : ℝ) * ((117 / 100 : ℝ) + t) - 1) := by
          unfold evenStructuralCorrelation02
          ring
        have hbracket : 0 <
            -((117 / 100 : ℝ) ^ 2 + (117 / 100 : ℝ) * t + t ^ 2) / 2 +
              (3 / 2 : ℝ) * ((117 / 100 : ℝ) + t) - 1 := by
          nlinarith [sq_nonneg (t - 11699 / 10000),
            sq_nonneg (117 / 100 - t)]
        have hdir : evenStructuralCorrelation02 t <
            evenStructuralCorrelation02 (117 / 100) := by
          have hprod := mul_pos (sub_pos.mpr ht.2) hbracket
          linarith
        calc
          evenStructuralCorrelation02
              (factorTwoPrimeShift / yoshidaEndpointA) <
              evenStructuralCorrelation02 (117 / 100) := hdir
          _ < 1651 / 20000 := by
            unfold evenStructuralCorrelation02
            norm_num
      · let a : ℝ := 11699 / 10000
        let b : ℝ := 117 / 100
        have ha : a < t := by simpa only [a, t] using ht.1
        have hb : t < b := by simpa only [b, t] using ht.2
        have ha0 : 0 < a := by norm_num [a]
        have hb0 : 0 < b := by norm_num [b]
        have hta : 0 < t + a := add_pos ht0 ha0
        have hbt : 0 < b + t := add_pos hb0 ht0
        have hsqLo : a ^ 2 < t ^ 2 := by
          nlinarith [mul_pos (sub_pos.mpr ha) hta]
        have hsqHi : t ^ 2 < b ^ 2 := by
          nlinarith [mul_pos (sub_pos.mpr hb) hbt]
        have hcubeLo : a ^ 3 < t ^ 3 := by
          have hsum : 0 < t ^ 2 + t * a + a ^ 2 := by positivity
          nlinarith [mul_pos (sub_pos.mpr ha) hsum]
        have hfifthHi : t ^ 5 < b ^ 5 := by
          have hsum : 0 < b ^ 4 + b ^ 3 * t + b ^ 2 * t ^ 2 +
              b * t ^ 3 + t ^ 4 := by positivity
          nlinarith [mul_pos (sub_pos.mpr hb) hsum]
        dsimp only [t] at ht0 ht1 ht2 ⊢
        unfold evenStructuralCorrelation22
        dsimp only [a, b] at hcubeLo hfifthHi hb
        nlinarith

/-! ## A rational negative-endpoint matrix -/

theorem yoshidaEndpointEvenLow00_kernel_lower :
    (35637 / 100000 : ℝ) < yoshidaEndpointEvenLow00 := by
  have hL := strict_log_two_fine_bounds.1
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloss :=
    yoshidaEndpointEvenSharpMassLoss_lt_eight_hundred_fifty_four_div_six_hundred_twenty_five
  have hC0 : (201 / 100 : ℝ) < yoshidaEndpointEvenLowC0 := by
    simpa only [yoshidaEndpointEvenLowC0] using
      two_hundred_one_div_hundred_lt_integral_yoshidaEndpoint_cosh
  have hC0pos : 0 < yoshidaEndpointEvenLowC0 :=
    (by norm_num : (0 : ℝ) < 201 / 100).trans hC0
  let delta : ℝ := (201 / 100 : ℝ) ^ 2 - 79 / 32
  have hdelta : 0 < delta := by norm_num [delta]
  have hsq : (201 / 100 : ℝ) ^ 2 < yoshidaEndpointEvenLowC0 ^ 2 := by
    nlinarith
  have hgap : delta < yoshidaEndpointEvenLowC0 ^ 2 - 79 / 32 := by
    dsimp only [delta]
    linarith
  have hprod : (69314718055 / 100000000000 : ℝ) * delta <
      Real.log 2 * (yoshidaEndpointEvenLowC0 ^ 2 - 79 / 32) := by
    calc
      (69314718055 / 100000000000 : ℝ) * delta <
          Real.log 2 * delta := mul_lt_mul_of_pos_right hL hdelta
      _ < Real.log 2 *
          (yoshidaEndpointEvenLowC0 ^ 2 - 79 / 32) :=
        mul_lt_mul_of_pos_left hgap hLpos
  unfold yoshidaEndpointEvenLow00 evenLow00
  nlinarith

theorem yoshidaEndpointEvenLow22_kernel_lower :
    (8071 / 25000 : ℝ) < yoshidaEndpointEvenLow22 := by
  have hL := strict_log_two_fine_bounds.2
  have hloss :=
    yoshidaEndpointEvenSharpMassLoss_lt_eight_hundred_fifty_four_div_six_hundred_twenty_five
  have hnonneg : 0 ≤ Real.log 2 * yoshidaEndpointEvenLowC2 ^ 2 :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (sq_nonneg _)
  unfold yoshidaEndpointEvenLow22 evenLow22
  nlinarith

def evenStructuralMinusKernel00 : ℝ :=
  yoshidaEndpointEvenLow00 - evenStructuralKernelBase00 - 1 / 250

def evenStructuralMinusKernel02 : ℝ :=
  yoshidaEndpointEvenLow02 - evenStructuralKernelBase02

def evenStructuralMinusKernel22 : ℝ :=
  yoshidaEndpointEvenLow22 - evenStructuralKernelBase22 - 1 / 1250

theorem evenStructuralMinusKernel00_lower :
    (29 / 50 : ℝ) < evenStructuralMinusKernel00 := by
  have hlow := yoshidaEndpointEvenLow00_kernel_lower
  have hL := strict_log_two_fine_bounds.1
  have ha := log_two_div_sqrt_two_kernel_lower
  have hb := log_three_div_sqrt_three_kernel_bounds.1
  have hC := primeRatio_evenCorrelation_bounds.1
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hprod : (63427 / 100000 : ℝ) * (83 / 100 : ℝ) <
      (Real.log 3 / Real.sqrt 3) *
        evenStructuralCorrelation00
          (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      (63427 / 100000 : ℝ) * (83 / 100 : ℝ) <
          (Real.log 3 / Real.sqrt 3) * (83 / 100 : ℝ) :=
        mul_lt_mul_of_pos_right hb (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_left hC hbeta
  unfold evenStructuralMinusKernel00 evenStructuralKernelBase00
  nlinarith

theorem evenStructuralMinusKernel02_bounds :
    0 < evenStructuralMinusKernel02 ∧
      evenStructuralMinusKernel02 < (68 / 125 : ℝ) := by
  have hlow := yoshidaEndpointEvenLow_matrix_bounds
  have hL := strict_log_two_fine_bounds
  have hb := log_three_div_sqrt_three_kernel_bounds
  have hC := primeRatio_evenCorrelation_bounds.2
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hprodPos : 0 < (Real.log 3 / Real.sqrt 3) *
      evenStructuralCorrelation02
        (factorTwoPrimeShift / yoshidaEndpointA) :=
    mul_pos hbeta hC.1
  have hprodUpper :
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (1651 / 20000 : ℝ) := by
    calc
      (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation02
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (6343 / 10000 : ℝ) *
            evenStructuralCorrelation02
              (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hb.2 hC.1
      _ < (6343 / 10000 : ℝ) * (1651 / 20000 : ℝ) :=
        mul_lt_mul_of_pos_left hC.2.1 (by norm_num)
  unfold evenStructuralMinusKernel02 evenStructuralKernelBase02
  constructor <;> nlinarith

theorem evenStructuralMinusKernel22_lower :
    (1021 / 2000 : ℝ) < evenStructuralMinusKernel22 := by
  have hlow := yoshidaEndpointEvenLow22_kernel_lower
  have hL := strict_log_two_fine_bounds.1
  have ha := log_two_div_sqrt_two_kernel_lower
  have hb := log_three_div_sqrt_three_kernel_bounds.2
  have hC := primeRatio_evenCorrelation_bounds.2.2.2
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hCneg : (-1337 / 10000 : ℝ) < 0 := by norm_num
  have hstep1 : (Real.log 3 / Real.sqrt 3) * (-1337 / 10000 : ℝ) <
      (Real.log 3 / Real.sqrt 3) *
        evenStructuralCorrelation22
          (factorTwoPrimeShift / yoshidaEndpointA) :=
    mul_lt_mul_of_pos_left hC hbeta
  have hstep2 : (6343 / 10000 : ℝ) * (-1337 / 10000 : ℝ) <
      (Real.log 3 / Real.sqrt 3) * (-1337 / 10000 : ℝ) :=
    mul_lt_mul_of_neg_right hb hCneg
  have hprod := hstep2.trans hstep1
  unfold evenStructuralMinusKernel22 evenStructuralKernelBase22
  nlinarith

theorem evenStructuralMinusKernel_principal_minors_pos :
    0 < evenStructuralMinusKernel00 ∧
      0 < evenStructuralMinusKernel00 * evenStructuralMinusKernel22 -
        evenStructuralMinusKernel02 ^ 2 := by
  have h00 := evenStructuralMinusKernel00_lower
  have h02 := evenStructuralMinusKernel02_bounds
  have h22 := evenStructuralMinusKernel22_lower
  have h00pos : 0 < evenStructuralMinusKernel00 :=
    (by norm_num : (0 : ℝ) < 29 / 50).trans h00
  have h22pos : 0 < evenStructuralMinusKernel22 :=
    (by norm_num : (0 : ℝ) < 1021 / 2000).trans h22
  have hprod : (29 / 50 : ℝ) * (1021 / 2000 : ℝ) <
      evenStructuralMinusKernel00 * evenStructuralMinusKernel22 := by
    exact mul_lt_mul h00 h22.le (by norm_num) h00pos.le
  have hsq : evenStructuralMinusKernel02 ^ 2 < (68 / 125 : ℝ) ^ 2 := by
    have hsum : 0 < (68 / 125 : ℝ) + evenStructuralMinusKernel02 :=
      add_pos (by norm_num) h02.1
    have hdiff : 0 < (68 / 125 : ℝ) - evenStructuralMinusKernel02 :=
      sub_pos.mpr h02.2
    nlinarith [mul_pos hdiff hsum]
  constructor
  · exact h00pos
  · have hrational : (68 / 125 : ℝ) ^ 2 <
        (29 / 50 : ℝ) * (1021 / 2000 : ℝ) := by norm_num
    nlinarith

/-- The lower Gram, exact pole/prime block, and the single coupled regular
error dominate the negative endpoint by an explicit positive matrix. -/
theorem evenStructuralMinusKernel_quadratic_le_endpoint
    (c d : ℝ) :
    evenStructuralMinusKernel00 * c ^ 2 +
        2 * evenStructuralMinusKernel02 * c * d +
        evenStructuralMinusKernel22 * d ^ 2 ≤
      yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) -
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) := by
  have hprofile : factorTwoEvenStructuralLowProfile c d =
      yoshidaEndpointEvenLowProfile c d := by
    funext x
    unfold factorTwoEvenStructuralLowProfile
      yoshidaEndpointEvenLowProfile centeredEvenP0
    ring
  have hclean := yoshidaEndpointEvenLow_quadratic_le_clean c d
  rw [← hprofile] at hclean
  have herr := abs_evenStructuralRegularError_profile_le c d
  have herrUpper :
      evenStructuralRegularError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) ≤
        (1 / 500 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) :=
    (le_abs_self _).trans herr
  rw [factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq]
  unfold evenStructuralMinusKernel00 evenStructuralMinusKernel02
    evenStructuralMinusKernel22
  nlinarith

theorem factorTwoIntrinsicEven_minus_endpoint_kernel_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) -
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) := by
  have hmatrix := real_twoByTwo_quadratic_pos
    evenStructuralMinusKernel00 evenStructuralMinusKernel02
    evenStructuralMinusKernel22 c d
    evenStructuralMinusKernel_principal_minors_pos.1
    evenStructuralMinusKernel_principal_minors_pos.2 hne
  exact hmatrix.trans_le
    (evenStructuralMinusKernel_quadratic_le_endpoint c d)

/-- One endpoint is now unconditional: both the `00` entry and determinant
gate at symmetric phase `-1` are strictly positive. -/
theorem factorTwoIntrinsicEven_minus_endpoint_kernel_gates :
    0 < factorTwoStructuralPhaseLow00 (-1) ∧
      0 < factorTwoIntrinsicEvenPhaseDet (-1) := by
  apply factorTwoIntrinsicEven_endpoint_gates_of_profile_pos (-1)
  intro c d hne
  simpa only [neg_one_mul, sub_eq_add_neg] using
    factorTwoIntrinsicEven_minus_endpoint_kernel_pos c d hne

/-! ## The exact remaining positive-endpoint reserve -/

def evenStructuralCleanReserve (c d : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic
      (factorTwoEvenStructuralLowProfile c d) -
    (yoshidaEndpointEvenLow00 * c ^ 2 +
      2 * yoshidaEndpointEvenLow02 * c * d +
      yoshidaEndpointEvenLow22 * d ^ 2)

def EvenStructuralPositiveReserveInequality : Prop :=
  ∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
    -(yoshidaEndpointEvenLow00 * c ^ 2 +
        2 * yoshidaEndpointEvenLow02 * c * d +
        yoshidaEndpointEvenLow22 * d ^ 2 +
        evenStructuralRegularError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) +
        evenStructuralKernelBase00 * c ^ 2 +
        2 * evenStructuralKernelBase02 * c * d +
        evenStructuralKernelBase22 * d ^ 2) <
      evenStructuralCleanReserve c d

/-- This is the sharp structural missing inequality for the other endpoint:
it asks exactly for the unused clean-form reserve to dominate the residual
kernel defect.  No entrywise or finite-mode relaxation is hidden here. -/
theorem evenStructuralPositiveReserveInequality_iff_plus_endpoint :
    EvenStructuralPositiveReserveInequality ↔
      ∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
        0 < yoshidaEndpointOddCleanQuadratic
            (factorTwoEvenStructuralLowProfile c d) +
          factorTwoCenteredSymmetricPerturbation
            (factorTwoEvenStructuralLowProfile c d) := by
  unfold EvenStructuralPositiveReserveInequality
    evenStructuralCleanReserve
  constructor <;> intro h c d hne
  · have := h c d hne
    rw [factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq]
    linarith
  · have := h c d hne
    rw [factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq] at this
    linarith
end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
