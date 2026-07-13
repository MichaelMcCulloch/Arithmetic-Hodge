import ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalGeometric
import ArithmeticHodge.Analysis.YoshidaFactorTwoCoreReduction

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalPhysical

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilRestrictedSupportEndpointPositive
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments
open YoshidaBombieriDiagonalResidual
open YoshidaCriticalLogCorrelation
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCoreReduction
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoDiagonalGeometric
open YoshidaFactorTwoSelfCorrelationSupport
open YoshidaRenormalizedGeometricKernel
open YoshidaShiftedGeometricSeries

/-!
# Exact physical diagonal on a factor-two cell

The polar moments and the complete renormalized digamma series are assembled
in the same self-correlation coordinates as the adjacent cross symbol.
-/

theorem integral_exp_selfCorrelation_eq_factorTwo_interval
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (t : ℝ) :
    (∫ s : ℝ, ((Real.exp (t * s) : ℝ) : ℂ) *
      bombieriCriticalCrossCorrelation g g s) =
      ∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
        ((Real.exp (t * s) : ℝ) : ℂ) *
          factorTwoSelfCorrelation g s := by
  change (∫ s : ℝ, ((Real.exp (t * s) : ℝ) : ℂ) *
      factorTwoSelfCorrelation g s) = _
  rw [intervalIntegral.integral_of_le (by
      linarith [factorTwoLogLength_pos] :
        -factorTwoLogLength ≤ factorTwoLogLength),
    ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs ↦ by
    rw [factorTwoSelfCorrelation_eq_zero_outside
      g ha hab hsupport hratio hs, mul_zero])).symm

theorem bombieriSelfPolar_re_eq_factorTwo_integral
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (star (mellin (g : ℝ → ℂ) 1) * mellin (g : ℝ → ℂ) 0 +
      star (mellin (g : ℝ → ℂ) 0) * mellin (g : ℝ → ℂ) 1).re =
      ∫ s : ℝ in 0..factorTwoLogLength,
        4 * Real.cosh (s / 2) * factorTwoSelfCorrelationRe g s := by
  let J : ℝ → ℂ := fun s ↦
    ((((Real.exp (s / 2) + Real.exp (-s / 2) : ℝ)) : ℂ) *
      factorTwoSelfCorrelation g s)
  let R : ℝ → ℝ := fun s ↦
    (Real.exp (s / 2) + Real.exp (-s / 2)) *
      factorTwoSelfCorrelationRe g s
  have hplus := integral_exp_mul_bombieriCriticalCrossCorrelation
    (1 / 2 : ℝ) g g
  rw [bombieriCriticalMoment_neg_half_eq_mellin_one,
    bombieriCriticalMoment_half_eq_mellin_zero] at hplus
  have hminus := integral_exp_mul_bombieriCriticalCrossCorrelation
    (-(1 / 2) : ℝ) g g
  rw [show -(-(1 / 2 : ℝ)) = 1 / 2 by ring,
    bombieriCriticalMoment_half_eq_mellin_zero,
    bombieriCriticalMoment_neg_half_eq_mellin_one] at hminus
  have hplusInterval := integral_exp_selfCorrelation_eq_factorTwo_interval
    g ha hab hsupport hratio (1 / 2)
  have hminusInterval := integral_exp_selfCorrelation_eq_factorTwo_interval
    g ha hab hsupport hratio (-(1 / 2))
  have hJ : IntervalIntegrable J volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    unfold J
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      (((Real.exp (s / 2) + Real.exp (-s / 2) : ℝ)) : ℂ))).mul
        (factorTwoSelfCorrelation_contDiff g 0).continuous
  have hR : IntervalIntegrable R volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    unfold R factorTwoSelfCorrelationRe
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      Real.exp (s / 2) + Real.exp (-s / 2))).mul
        (Complex.continuous_re.comp
          (factorTwoSelfCorrelation_contDiff g 0).continuous)
  have hplusInt : IntervalIntegrable (fun s : ℝ ↦
      ((Real.exp ((1 / 2 : ℝ) * s) : ℝ) : ℂ) *
        factorTwoSelfCorrelation g s) volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      ((Real.exp ((1 / 2 : ℝ) * s) : ℝ) : ℂ))).mul
        (factorTwoSelfCorrelation_contDiff g 0).continuous
  have hminusInt : IntervalIntegrable (fun s : ℝ ↦
      ((Real.exp (-(1 / 2 : ℝ) * s) : ℝ) : ℂ) *
        factorTwoSelfCorrelation g s) volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      ((Real.exp (-(1 / 2 : ℝ) * s) : ℝ) : ℂ))).mul
        (factorTwoSelfCorrelation_contDiff g 0).continuous
  have hpolar :
      star (mellin (g : ℝ → ℂ) 1) * mellin (g : ℝ → ℂ) 0 +
          star (mellin (g : ℝ → ℂ) 0) * mellin (g : ℝ → ℂ) 1 =
        ∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength, J s := by
    rw [← hplus, ← hminus, hplusInterval, hminusInterval,
      ← intervalIntegral.integral_add hplusInt hminusInt]
    apply intervalIntegral.integral_congr
    intro s _hs
    unfold J
    push_cast
    rw [show (1 / 2 : ℂ) * (s : ℂ) = (s : ℂ) / 2 by ring,
      show -(1 / 2 : ℂ) * (s : ℂ) = -(s : ℂ) / 2 by ring]
    ring
  have hL : 0 ≤ factorTwoLogLength := factorTwoLogLength_pos.le
  have hneg : IntervalIntegrable R volume (-factorTwoLogLength) 0 := by
    apply hR.mono_set
    intro s hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ 0)] at hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ factorTwoLogLength)]
    exact ⟨hs.1, hs.2.trans hL⟩
  have hpos : IntervalIntegrable R volume 0 factorTwoLogLength := by
    apply hR.mono_set
    intro s hs
    rw [uIcc_of_le hL] at hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ factorTwoLogLength)]
    exact ⟨(neg_nonpos.mpr hL).trans hs.1, hs.2⟩
  have hreflect : IntervalIntegrable (fun s : ℝ ↦ R (-s)) volume
      0 factorTwoLogLength := by
    have h := (hneg.comp_mul_left (c := (-1 : ℝ))).symm
    convert h using 1 <;> norm_num
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hneg hpos
  have hreflectIntegral := intervalIntegral.integral_comp_neg
    (f := R) (a := 0) (b := factorTwoLogLength)
  rw [hpolar]
  calc
    (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength, J s).re =
        ∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
          (J s).re := by
      simpa only [Complex.reCLM_apply] using
        (Complex.reCLM.intervalIntegral_comp_comm hJ).symm
    _ = ∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength, R s := by
      apply intervalIntegral.integral_congr
      intro s _hs
      simp only [J, R, factorTwoSelfCorrelationRe, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = (∫ s : ℝ in -factorTwoLogLength..0, R s) +
        ∫ s : ℝ in 0..factorTwoLogLength, R s := hsplit.symm
    _ = (∫ s : ℝ in 0..factorTwoLogLength, R (-s)) +
        ∫ s : ℝ in 0..factorTwoLogLength, R s := by
      rw [hreflectIntegral]
      simp only [neg_zero]
    _ = ∫ s : ℝ in 0..factorTwoLogLength, (R (-s) + R s) := by
      rw [intervalIntegral.integral_add hreflect hpos]
    _ = ∫ s : ℝ in 0..factorTwoLogLength,
        4 * Real.cosh (s / 2) * factorTwoSelfCorrelationRe g s := by
      apply intervalIntegral.integral_congr
      intro s _hs
      dsimp only [R]
      unfold factorTwoSelfCorrelationRe
      rw [factorTwoSelfCorrelation_neg]
      simp only [Complex.conj_re]
      rw [Real.cosh_eq]
      ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalPhysical
