import ArithmeticHodge.Analysis.YoshidaOddTailPaired

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaOddDigammaLoss

open DigammaTrapezoid
open YoshidaCoercivityNumerics
open YoshidaOddTailPaired
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Odd-tail low digamma loss

This module isolates the genuine low-frequency digamma step in Yoshida's odd
Section 6 estimate.  The constant 2773 / 1000 is represented faithfully as a
bound for one half of the symmetric integral of the negative digamma kernel.
It is never assumed to be a pointwise kernel bound.

The Fourier-tail part of the argument is discharged on the actual periodic
core.  The numerical half-integral certificate is exposed as the precise
remaining premise until a separate certified quadrature or analytic bound is
proved.
-/

theorem digammaQuarterVerticalRe_neg (v : ℝ) :
    digammaQuarterVerticalRe (-v) = digammaQuarterVerticalRe v := by
  unfold digammaQuarterVerticalRe
  rw [digamma_quarter_vertical_re_eq_trapezoid_series,
    digamma_quarter_vertical_re_eq_trapezoid_series]
  congr 1
  · unfold shiftedReciprocalRealPart reciprocalRealPart
    ring
  · apply tsum_congr
    intro n
    unfold quarterDigammaSeriesTerm shiftedReciprocalRealPart reciprocalRealPart
    ring

theorem digammaQuarterVerticalRe_abs (v : ℝ) :
    digammaQuarterVerticalRe |v| = digammaQuarterVerticalRe v := by
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv]
  · rw [abs_of_neg (lt_of_not_ge hv), digammaQuarterVerticalRe_neg]

theorem digammaQuarterVerticalRe_nonpos_of_abs_le_yoshidaTZero
    {tZero v : ℝ} (ht : YoshidaTZeroTailBounds.IsYoshidaTZero tZero)
    (hv : |v| ≤ tZero) :
    digammaQuarterVerticalRe v ≤ 0 := by
  have hmono := YoshidaTZeroTailBounds.re_digamma_quarter_vertical_monotoneOn
    (show |v| ∈ Set.Ici (0 : ℝ) by exact abs_nonneg v)
    (show tZero ∈ Set.Ici (0 : ℝ) by exact ht.1.le) hv
  change digammaQuarterVerticalRe |v| ≤
    digammaQuarterVerticalRe tZero at hmono
  have htzero : digammaQuarterVerticalRe tZero = 0 := by
    simpa [digammaQuarterVerticalRe] using ht.2
  rw [digammaQuarterVerticalRe_abs, htzero] at hmono
  exact hmono

/-- The exact missing numerical certificate in the source's low digamma
loss.  The constant is a bound for one half of the symmetric integral, not
for the pointwise kernel. -/
def LowDigammaHalfIntegralBound (tZero : ℝ) : Prop :=
  -(1 / 2 : ℝ) *
      (∫ v : ℝ in -tZero..tZero, digammaQuarterVerticalRe v) ≤
    (2773 / 1000 : ℝ)

/-- The actual low digamma-loss estimate.  It combines the exact odd-tail
pointwise bound with a half-integral certificate for the negative digamma
kernel; no false pointwise `2773 / 1000` bound is assumed. -/
theorem oddTenTail_low_digamma_loss_le_lowIntervalPenalty
    {tZero : ℝ} (ht : YoshidaTZeroTailBounds.IsYoshidaTZero tZero)
    (hhalf : LowDigammaHalfIntegralBound tZero)
    (f : YoshidaClippedPeriodicCore yoshidaA)
    (hf : f ∈ yoshidaPeriodicCoreOddTailSubmodule
      YoshidaCoercivityNumerics.yoshidaA_pos 10)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        ‖((f : YoshidaClippedSmooth yoshidaA) : ℝ → ℂ) x‖ ^ 2) = 1) :
    -(1 / (2 * Real.pi)) *
        (∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v *
            Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
              YoshidaCoercivityNumerics.yoshidaA_pos v
              (f : YoshidaClippedSmooth yoshidaA))) ≤
      lowIntervalPenalty 10 tZero := by
  let q : ℝ → ℝ := fun v ↦
    Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
      YoshidaCoercivityNumerics.yoshidaA_pos v
      (f : YoshidaClippedSmooth yoshidaA))
  let K : ℝ := yoshidaA / Real.pi ^ 2 * weightedTail 10 tZero
  have htUpper : tZero ≤ (51 / 25 : ℝ) :=
    YoshidaTZeroTailBounds.yoshidaTZero_le_51_div_25 ht
  have hwindow : yoshidaA * tZero < piLowerR * (10 + 1 : ℕ) := by
    calc
      yoshidaA * tZero ≤ yoshidaA * (51 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left htUpper yoshidaA_pos.le
      _ ≤ (((YoshidaTZeroTailBounds.lowCUpperQ : ℚ) : ℝ)) :=
        YoshidaTZeroTailBounds.yoshidaA_mul_51_div_25_le_lowCUpper
      _ < piLowerR * (10 + 1 : ℕ) := by
        norm_num [YoshidaTZeroTailBounds.lowCUpperQ, piLowerR]
  have htail0 : 0 ≤ weightedTail 10 tZero :=
    weightedTail_nonneg 10 tZero
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg
      (div_nonneg yoshidaA_pos.le (sq_nonneg Real.pi)) htail0
  have hqpoint {v : ℝ} (hv : v ∈ Set.Icc (-tZero) tZero) : q v ≤ K := by
    have habs : |v| ≤ tZero := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
    have hsample := oddTail_paired_pointwise_estimate_weightedTail
      (N := 10) (by norm_num) f hf henergy ht.1.le habs hwindow
    dsimp only [q, K]
    calc
      Complex.normSq (yoshidaCriticalSampleLinear yoshidaA yoshidaA_pos v
          (f : YoshidaClippedSmooth yoshidaA)) ≤
        yoshidaA / Real.pi ^ 2 * Real.sin (yoshidaA * v) ^ 2 *
          weightedTail 10 tZero := hsample
      _ = (yoshidaA / Real.pi ^ 2 * weightedTail 10 tZero) *
          Real.sin (yoshidaA * v) ^ 2 := by ring
      _ ≤ (yoshidaA / Real.pi ^ 2 * weightedTail 10 tZero) * 1 := by
        exact mul_le_mul_of_nonneg_left (Real.sin_sq_le_one _) hK0
      _ = yoshidaA / Real.pi ^ 2 * weightedTail 10 tZero := by ring
  have hpoint {v : ℝ} (hv : v ∈ Set.Icc (-tZero) tZero) :
      -digammaQuarterVerticalRe v * q v ≤
        -digammaQuarterVerticalRe v * K := by
    exact mul_le_mul_of_nonneg_left (hqpoint hv)
      (neg_nonneg.mpr
        (digammaQuarterVerticalRe_nonpos_of_abs_le_yoshidaTZero ht
          (abs_le.mpr ⟨by linarith [hv.1], hv.2⟩)))
  have hqCont : Continuous q := by
    dsimp only [q]
    exact Complex.continuous_normSq.comp
      (continuous_yoshidaCriticalSample yoshidaA_pos
        (f : YoshidaClippedSmooth yoshidaA))
  have hgCont : Continuous digammaQuarterVerticalRe := by
    exact YoshidaTZeroTailBounds.continuous_re_digamma_quarter_vertical
  have hmono :
      (∫ v : ℝ in -tZero..tZero,
        -digammaQuarterVerticalRe v * q v) ≤
      ∫ v : ℝ in -tZero..tZero,
        -digammaQuarterVerticalRe v * K := by
    exact intervalIntegral.integral_mono_on (by linarith [ht.1])
      ((hgCont.neg.mul hqCont).intervalIntegrable (-tZero) tZero)
      ((hgCont.neg.mul continuous_const).intervalIntegrable (-tZero) tZero)
      (fun v hv ↦ hpoint hv)
  have hhalf' :
      -(∫ v : ℝ in -tZero..tZero, digammaQuarterVerticalRe v) ≤
        2 * (2773 / 1000 : ℝ) := by
    unfold LowDigammaHalfIntegralBound at hhalf
    linarith
  have hscaled :
      K * (-(∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v)) ≤
        K * (2 * (2773 / 1000 : ℝ)) :=
    mul_le_mul_of_nonneg_left hhalf' hK0
  have hnegIntegral :
      -(∫ v : ℝ in -tZero..tZero,
        digammaQuarterVerticalRe v * q v) ≤
        K * (2 * (2773 / 1000 : ℝ)) := by
    calc
      -(∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v * q v) =
        ∫ v : ℝ in -tZero..tZero,
          -digammaQuarterVerticalRe v * q v := by
            rw [← intervalIntegral.integral_neg]
            apply intervalIntegral.integral_congr
            intro v _
            ring
      _ ≤ ∫ v : ℝ in -tZero..tZero,
          -digammaQuarterVerticalRe v * K := hmono
      _ = K * (-(∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v)) := by
            rw [← intervalIntegral.integral_neg]
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro v _
            ring
      _ ≤ K * (2 * (2773 / 1000 : ℝ)) := hscaled
  calc
    -(1 / (2 * Real.pi)) *
        (∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v *
            Complex.normSq (yoshidaCriticalSampleLinear yoshidaA
              yoshidaA_pos v (f : YoshidaClippedSmooth yoshidaA))) =
      (1 / (2 * Real.pi)) *
        (-(∫ v : ℝ in -tZero..tZero,
          digammaQuarterVerticalRe v * q v)) := by
            dsimp only [q]
            ring
    _ ≤ (1 / (2 * Real.pi)) *
        (K * (2 * (2773 / 1000 : ℝ))) :=
      mul_le_mul_of_nonneg_left hnegIntegral (by positivity)
    _ = lowIntervalPenalty 10 tZero := by
      dsimp only [K]
      unfold lowIntervalPenalty
      field_simp [Real.pi_ne_zero]

end ArithmeticHodge.Analysis.YoshidaOddDigammaLoss

