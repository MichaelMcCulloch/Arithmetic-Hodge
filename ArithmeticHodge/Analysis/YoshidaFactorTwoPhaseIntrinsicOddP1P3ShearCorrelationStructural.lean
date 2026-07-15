import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP1P3ShearCorrelationStructural

noncomputable section

open ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoEndpointClean
open YoshidaRegularKernelBound

/-!
# Coupled correlations for the `P₃ - P₁` shear

Bounding the three `P₁/P₃` entries separately destroys the cancellation
used by the corrected endpoint Schur blocks.  The two polynomials below are
the polarized cross and diagonal correlations after the determinant-one
change of basis `(P₁, P₃) ↦ (P₁, P₃ - P₁)`.  Their exact `L²`
masses give global `L¹` bounds by Cauchy--Schwarz, with no subdivision of
the overlap interval.
-/

/-- Correlation pairing of `P₁` with `P₃ - P₁`. -/
def oddStructuralP1P3ShearCrossCorrelation (t : ℝ) : ℝ :=
  oddStructuralCorrelation13 t - oddStructuralCorrelation11 t

/-- Autocorrelation of `P₃ - P₁`. -/
def oddStructuralP1P3ShearDiagonalCorrelation (t : ℝ) : ℝ :=
  oddStructuralCorrelation11 t - 2 * oddStructuralCorrelation13 t +
    oddStructuralCorrelation33 t

theorem oddStructuralP1P3ShearCrossCorrelation_eq_polynomial
    (t : ℝ) :
    oddStructuralP1P3ShearCrossCorrelation t =
      -2 / 3 + (5 / 2 : ℝ) * t ^ 2 - (5 / 3 : ℝ) * t ^ 3 +
        (1 / 8 : ℝ) * t ^ 5 := by
  unfold oddStructuralP1P3ShearCrossCorrelation
    oddStructuralCorrelation11 oddStructuralCorrelation13
  ring

theorem oddStructuralP1P3ShearDiagonalCorrelation_eq_polynomial
    (t : ℝ) :
    oddStructuralP1P3ShearDiagonalCorrelation t =
      20 / 21 - 5 * t ^ 2 + (25 / 6 : ℝ) * t ^ 3 -
        (5 / 8 : ℝ) * t ^ 5 + (5 / 112 : ℝ) * t ^ 7 := by
  unfold oddStructuralP1P3ShearDiagonalCorrelation
    oddStructuralCorrelation11 oddStructuralCorrelation13
    oddStructuralCorrelation33
  ring

/-- Both sheared correlations retain the mean-zero cancellation of the
centered structural block. -/
theorem integral_oddStructuralP1P3ShearCrossCorrelation_eq_zero :
    (∫ t : ℝ in 0..2, oddStructuralP1P3ShearCrossCorrelation t) = 0 := by
  simp_rw [oddStructuralP1P3ShearCrossCorrelation_eq_polynomial]
  norm_num [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_pow]

theorem integral_oddStructuralP1P3ShearDiagonalCorrelation_eq_zero :
    (∫ t : ℝ in 0..2, oddStructuralP1P3ShearDiagonalCorrelation t) = 0 := by
  simp_rw [oddStructuralP1P3ShearDiagonalCorrelation_eq_polynomial]
  norm_num [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_pow]

/-- Exact squared mass of the polarized sheared correlation. -/
theorem integral_sq_oddStructuralP1P3ShearCrossCorrelation :
    (∫ t : ℝ in 0..2,
      oddStructuralP1P3ShearCrossCorrelation t ^ 2) = 460 / 2079 := by
  rw [show (fun t : ℝ ↦ oddStructuralP1P3ShearCrossCorrelation t ^ 2) =
      fun t ↦
        (4 / 9 : ℝ) - (10 / 3 : ℝ) * t ^ 2 +
          (20 / 9 : ℝ) * t ^ 3 + (25 / 4 : ℝ) * t ^ 4 -
          (17 / 2 : ℝ) * t ^ 5 + (25 / 9 : ℝ) * t ^ 6 +
          (5 / 8 : ℝ) * t ^ 7 - (5 / 12 : ℝ) * t ^ 8 +
          (1 / 64 : ℝ) * t ^ 10 by
    funext t
    rw [oddStructuralP1P3ShearCrossCorrelation_eq_polynomial]
    ring]
  norm_num [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_pow]

/-- Exact squared mass of the sheared autocorrelation. -/
theorem integral_sq_oddStructuralP1P3ShearDiagonalCorrelation :
    (∫ t : ℝ in 0..2,
      oddStructuralP1P3ShearDiagonalCorrelation t ^ 2) = 10040 / 27027 := by
  rw [show
      (fun t : ℝ ↦ oddStructuralP1P3ShearDiagonalCorrelation t ^ 2) =
        fun t ↦
          (400 / 441 : ℝ) - (200 / 21 : ℝ) * t ^ 2 +
            (500 / 63 : ℝ) * t ^ 3 + 25 * t ^ 4 -
            (300 / 7 : ℝ) * t ^ 5 + (625 / 36 : ℝ) * t ^ 6 +
            (3725 / 588 : ℝ) * t ^ 7 - (125 / 24 : ℝ) * t ^ 8 -
            (25 / 56 : ℝ) * t ^ 9 + (1025 / 1344 : ℝ) * t ^ 10 -
            (25 / 448 : ℝ) * t ^ 12 + (25 / 12544 : ℝ) * t ^ 14 by
    funext t
    rw [oddStructuralP1P3ShearDiagonalCorrelation_eq_polynomial]
    ring]
  norm_num [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_pow]

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

/-- Global `L¹` budget for the polarized shear correlation. -/
theorem integral_abs_oddStructuralP1P3ShearCrossCorrelation_lt :
    (∫ t : ℝ in 0..2,
      |oddStructuralP1P3ShearCrossCorrelation t|) < 2 / 3 := by
  have hcs := sq_intervalIntegral_mul_le_zero_two
    (fun _ : ℝ ↦ 1)
    (fun t ↦ |oddStructuralP1P3ShearCrossCorrelation t|)
    continuous_const
    (by
      unfold oddStructuralP1P3ShearCrossCorrelation
        oddStructuralCorrelation11 oddStructuralCorrelation13
      fun_prop)
  simp only [one_mul, one_pow, sq_abs] at hcs
  rw [show (∫ _t : ℝ in 0..2, (1 : ℝ)) = 2 by norm_num,
    integral_sq_oddStructuralP1P3ShearCrossCorrelation] at hcs
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..2,
      |oddStructuralP1P3ShearCrossCorrelation t| :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ abs_nonneg _)
  have hrat : (2 : ℝ) * (460 / 2079) < (2 / 3 : ℝ) ^ 2 := by
    norm_num
  nlinarith

/-- Global `L¹` budget for the sheared autocorrelation. -/
theorem integral_abs_oddStructuralP1P3ShearDiagonalCorrelation_lt :
    (∫ t : ℝ in 0..2,
      |oddStructuralP1P3ShearDiagonalCorrelation t|) < 13 / 15 := by
  have hcs := sq_intervalIntegral_mul_le_zero_two
    (fun _ : ℝ ↦ 1)
    (fun t ↦ |oddStructuralP1P3ShearDiagonalCorrelation t|)
    continuous_const
    (by
      unfold oddStructuralP1P3ShearDiagonalCorrelation
        oddStructuralCorrelation11 oddStructuralCorrelation13
        oddStructuralCorrelation33
      fun_prop)
  simp only [one_mul, one_pow, sq_abs] at hcs
  rw [show (∫ _t : ℝ in 0..2, (1 : ℝ)) = 2 by norm_num,
    integral_sq_oddStructuralP1P3ShearDiagonalCorrelation] at hcs
  have hnonneg : 0 ≤ ∫ t : ℝ in 0..2,
      |oddStructuralP1P3ShearDiagonalCorrelation t| :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ abs_nonneg _)
  have hrat : (2 : ℝ) * (10040 / 27027) < (13 / 15 : ℝ) ^ 2 := by
    norm_num
  nlinarith

private theorem measurable_yoshidaRegularKernel_shear :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_factorTwoCenteredSymmetricRegularWeight_shear :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_shear.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel_shear.comp (by fun_prop))

private theorem intervalIntegrable_oddStructuralRegularError_shear
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
    exact ((measurable_const.mul
      measurable_factorTwoCenteredSymmetricRegularWeight_shear).sub
        (by unfold oddStructuralRegularQuadratic; fun_prop)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have hk := oddStructuralRegularKernelControl t htIcc
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

theorem oddStructuralRegularError_shearCross_eq :
    oddStructuralRegularError oddStructuralP1P3ShearCrossCorrelation =
      oddStructuralRegularError oddStructuralCorrelation13 -
        oddStructuralRegularError oddStructuralCorrelation11 := by
  have h13 := intervalIntegrable_oddStructuralRegularError_shear
    oddStructuralCorrelation13
      (by unfold oddStructuralCorrelation13; fun_prop)
  have h11 := intervalIntegrable_oddStructuralRegularError_shear
    oddStructuralCorrelation11
      (by unfold oddStructuralCorrelation11; fun_prop)
  unfold oddStructuralRegularError
    oddStructuralP1P3ShearCrossCorrelation
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
        oddStructuralRegularQuadratic t) *
          (oddStructuralCorrelation13 t - oddStructuralCorrelation11 t)) =
      fun t ↦
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddStructuralCorrelation13 t -
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddStructuralCorrelation11 t by
    funext t
    ring,
    intervalIntegral.integral_sub h13 h11]

theorem oddStructuralRegularError_shearDiagonal_eq :
    oddStructuralRegularError oddStructuralP1P3ShearDiagonalCorrelation =
      oddStructuralRegularError oddStructuralCorrelation11 -
        2 * oddStructuralRegularError oddStructuralCorrelation13 +
          oddStructuralRegularError oddStructuralCorrelation33 := by
  have h11 := intervalIntegrable_oddStructuralRegularError_shear
    oddStructuralCorrelation11
      (by unfold oddStructuralCorrelation11; fun_prop)
  have h13 := intervalIntegrable_oddStructuralRegularError_shear
    oddStructuralCorrelation13
      (by unfold oddStructuralCorrelation13; fun_prop)
  have h33 := intervalIntegrable_oddStructuralRegularError_shear
    oddStructuralCorrelation33
      (by unfold oddStructuralCorrelation33; fun_prop)
  unfold oddStructuralRegularError
    oddStructuralP1P3ShearDiagonalCorrelation
  rw [show (fun t : ℝ ↦
      (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
        oddStructuralRegularQuadratic t) *
          (oddStructuralCorrelation11 t -
            2 * oddStructuralCorrelation13 t + oddStructuralCorrelation33 t)) =
      fun t ↦
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddStructuralCorrelation11 t -
        2 * ((yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddStructuralCorrelation13 t) +
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          oddStructuralRegularQuadratic t) * oddStructuralCorrelation33 t by
    funext t
    ring,
    intervalIntegral.integral_add (h11.sub (h13.const_mul 2)) h33,
    intervalIntegral.integral_sub h11 (h13.const_mul 2),
    intervalIntegral.integral_const_mul]

/-- Coupled regular-remainder budget for the polarized shear entry. -/
theorem abs_oddStructuralRegularError_shearCross_lt :
    |oddStructuralRegularError oddStructuralP1P3ShearCrossCorrelation| <
      1 / 750 := by
  have herr := abs_oddStructuralRegularError_le
    oddStructuralRegularKernelControl
    oddStructuralP1P3ShearCrossCorrelation
    (by
      unfold oddStructuralP1P3ShearCrossCorrelation
        oddStructuralCorrelation11 oddStructuralCorrelation13
      fun_prop)
  have hcorr := integral_abs_oddStructuralP1P3ShearCrossCorrelation_lt
  nlinarith

/-- Coupled regular-remainder budget for the sheared diagonal entry. -/
theorem abs_oddStructuralRegularError_shearDiagonal_lt :
    |oddStructuralRegularError oddStructuralP1P3ShearDiagonalCorrelation| <
      13 / 7500 := by
  have herr := abs_oddStructuralRegularError_le
    oddStructuralRegularKernelControl
    oddStructuralP1P3ShearDiagonalCorrelation
    (by
      unfold oddStructuralP1P3ShearDiagonalCorrelation
        oddStructuralCorrelation11 oddStructuralCorrelation13
        oddStructuralCorrelation33
      fun_prop)
  have hcorr := integral_abs_oddStructuralP1P3ShearDiagonalCorrelation_lt
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP1P3ShearCorrelationStructural
