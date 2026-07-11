import ArithmeticHodge.Analysis.YoshidaClippedLowModes
import ArithmeticHodge.Analysis.YoshidaCoercivityNumerics

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set
open scoped BigOperators ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic

open YoshidaCoercivityNumerics

/-!
# Yoshida's Section 6 analytic bridge

This module pins the Fourier normalization in Yoshida's equations (6.5)--(6.7),
proves the exact finite clipped-mode transform, integrates the paired
Cauchy--Schwarz estimate, and connects the resulting lower bound to the actual
clipped local critical form.

The repository critical sample uses `exp (-I * v * x)`, so it is Yoshida's
printed Fourier transform evaluated at `-v`. The infinite periodic-tail
Fourier expansion, its Parseval identity, the polar estimate, and the
source-specific digamma split remain precise named premises. No positivity or
ordinary-`L²` boundedness of the local critical form is assumed.
-/

/-- On the critical line, the clipped-mode Laplace exponent is purely
imaginary. This identity fixes the repository's negative-frequency sign. -/
theorem modeLaplaceExponent_critical
    {a : ℝ} (ha : 0 < a) (v : ℝ) (n : ℤ) :
    yoshidaModeLaplaceExponent a n (v * Complex.I) =
      (((Real.pi * (n : ℝ) / a - v : ℝ) : ℂ) * Complex.I) := by
  unfold yoshidaModeLaplaceExponent
  push_cast
  field_simp [ha.ne']
  ring

/-- A nonzero Section 6 denominator gives a nonzero critical-line mode
exponent. -/
theorem modeLaplaceExponent_critical_ne
    {a : ℝ} (ha : 0 < a) {v : ℝ} {n : ℤ}
    (hden : a * v - Real.pi * (n : ℝ) ≠ 0) :
    yoshidaModeLaplaceExponent a n (v * Complex.I) ≠ 0 := by
  rw [modeLaplaceExponent_critical ha]
  intro h
  have him := congrArg Complex.im h
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one,
    zero_mul, add_zero, zero_im] at him
  apply hden
  have ha0 : a ≠ 0 := ha.ne'
  field_simp [ha0] at him
  linarith

/-- Exact one-mode form of Yoshida (6.5) in the repository's
negative-frequency convention. -/
theorem criticalSample_clippedExponential_eq_section6
    {a : ℝ} (ha : 0 < a) (v : ℝ) (n : ℤ)
    (hden : a * v - Real.pi * (n : ℝ) ≠ 0) :
    yoshidaCriticalSampleLinear a ha v (yoshidaClippedExponential a n) =
      ((Real.sqrt (2 * a) * (-1 : ℝ) ^ n * Real.sin (a * v) /
        (a * v - Real.pi * (n : ℝ)) : ℝ) : ℂ) := by
  rw [yoshidaCriticalSampleLinear,
    yoshidaCenteredLaplace_clippedExponential_of_ne ha (v * Complex.I) n
      (modeLaplaceExponent_critical_ne ha hden),
    modeLaplaceExponent_critical ha]
  have ha0 : a ≠ 0 := ha.ne'
  have hsqrt : Real.sqrt (2 * a) ≠ 0 := by positivity
  have hr : Real.pi * (n : ℝ) / a - v ≠ 0 := by
    intro h
    apply hden
    field_simp [ha0] at h
    linarith
  have hphase : (Real.pi * (n : ℝ) / a - v) * a =
      (n : ℝ) * Real.pi - a * v := by
    field_simp [ha0]
  rw [show ((((Real.pi * (n : ℝ) / a - v : ℝ) : ℂ) * Complex.I) *
        (a : ℂ)) =
      ((((n : ℝ) * Real.pi - a * v : ℝ) : ℂ) * Complex.I) by
    calc
      (((Real.pi * (n : ℝ) / a - v : ℝ) : ℂ) * Complex.I) *
          (a : ℂ) =
          (((((Real.pi * (n : ℝ) / a - v) * a : ℝ) : ℂ) *
            Complex.I)) := by push_cast; ring
      _ = _ := by rw [hphase]]
  rw [show ((((Real.pi * (n : ℝ) / a - v : ℝ) : ℂ) * Complex.I) *
        (-(a : ℂ))) =
      (((-((n : ℝ) * Real.pi - a * v) : ℝ) : ℂ) * Complex.I) by
    calc
      (((Real.pi * (n : ℝ) / a - v : ℝ) : ℂ) * Complex.I) *
          (-(a : ℂ)) =
          (((-((Real.pi * (n : ℝ) / a - v) * a) : ℝ) : ℂ) *
            Complex.I) := by push_cast; ring
      _ = _ := by rw [hphase]]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  rw [Real.cos_int_mul_pi_sub, Real.sin_int_mul_pi_sub]
  have hdenC : (((a * v - Real.pi * (n : ℝ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  have hrC : (((Real.pi * (n : ℝ) / a - v : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hr
  have hsqrt_sqC : (((Real.sqrt (2 * a) : ℝ) : ℂ) ^ 2) =
      (((2 * a : ℝ) : ℂ)) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * a)
  push_cast
  field_simp [ha0, hsqrt, hr, hden, hdenC, hrC]
  rw [hsqrt_sqC]
  rw [show ((Real.pi : ℂ) * (n : ℂ) - (a : ℂ) * (v : ℂ)) =
      -((a : ℂ) * (v : ℂ) - (Real.pi : ℂ) * (n : ℂ)) by ring]
  field_simp [hdenC]
  push_cast
  ring_nf

/-- A finite linear combination of clipped Yoshida exponentials. -/
def finiteClippedFourierTail
    (a : ℝ) (S : Finset ℤ) (c : ℤ → ℂ) : YoshidaClippedSmooth a :=
  ∑ n ∈ S, c n • yoshidaClippedExponential a n

/-- Finite-sum form of Yoshida (6.5), in the repository's negative-frequency
convention. The only excluded points are the actual removable resonances. -/
theorem criticalSample_finiteClippedFourierTail_eq_section6
    {a : ℝ} (ha : 0 < a) (v : ℝ) (S : Finset ℤ) (c : ℤ → ℂ)
    (hden : ∀ n ∈ S, a * v - Real.pi * (n : ℝ) ≠ 0) :
    yoshidaCriticalSampleLinear a ha v (finiteClippedFourierTail a S c) =
      ∑ n ∈ S, c n *
        ((Real.sqrt (2 * a) * (-1 : ℝ) ^ n * Real.sin (a * v) /
          (a * v - Real.pi * (n : ℝ)) : ℝ) : ℂ) := by
  rw [finiteClippedFourierTail, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul, smul_eq_mul,
    criticalSample_clippedExponential_eq_section6 ha v n (hden n hn)]

/-- Yoshida's printed Fourier convention is obtained by evaluating the
repository critical sample at `-t`; this is the exact finite-sum (6.5). -/
theorem criticalSample_neg_finiteClippedFourierTail_eq_source6_5
    {a : ℝ} (ha : 0 < a) (t : ℝ) (S : Finset ℤ) (c : ℤ → ℂ)
    (hden : ∀ n ∈ S, a * t + Real.pi * (n : ℝ) ≠ 0) :
    yoshidaCriticalSampleLinear a ha (-t) (finiteClippedFourierTail a S c) =
      ∑ n ∈ S, c n *
        ((Real.sqrt (2 * a) * (-1 : ℝ) ^ n * Real.sin (a * t) /
          (a * t + Real.pi * (n : ℝ)) : ℝ) : ℂ) := by
  rw [criticalSample_finiteClippedFourierTail_eq_section6 ha (-t) S c]
  · apply Finset.sum_congr rfl
    intro n hn
    congr 1
    norm_cast
    rw [mul_neg, Real.sin_neg]
    rw [show -(a * t) - Real.pi * (n : ℝ) =
      -(a * t + Real.pi * (n : ℝ)) by ring]
    field_simp [hden n hn]
  · intro n hn
    have h := hden n hn
    intro hz
    apply h
    calc
      a * t + Real.pi * (n : ℝ) =
          -(-(a * t) - Real.pi * (n : ℝ)) := by ring
      _ = -(a * (-t) - Real.pi * (n : ℝ)) := by ring
      _ = 0 := by rw [hz]; simp

/-- The exact oscillatory window in Yoshida (6.6). -/
theorem integral_sin_sq_mul_symmetric
    {a T : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in -T..T, Real.sin (a * t) ^ 2) =
      T - Real.sin (2 * a * T) / (2 * a) := by
  rw [intervalIntegral.integral_comp_mul_left
    (f := fun x : ℝ ↦ Real.sin x ^ 2) ha.ne']
  rw [integral_sin_sq]
  simp only [mul_neg, Real.sin_neg, Real.cos_neg, smul_eq_mul]
  field_simp [ha.ne']
  ring_nf
  rw [show a * T * 2 = 2 * (a * T) by ring, Real.sin_two_mul]
  ring

/-- Continuity of the clipped critical sample as a Fourier transform of a
compactly supported integrable function. -/
theorem continuous_yoshidaCriticalSample
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    Continuous (fun v : ℝ ↦ yoshidaCriticalSampleLinear a ha v f) := by
  have hfint : Integrable (f : ℝ → ℂ) :=
    f.property.1.continuousOn.integrableOn_Icc
      |>.integrable_of_forall_notMem_eq_zero
        (fun x hx ↦ yoshidaClippedSmooth_eq_zero_outside f hx)
  have hfourier : Continuous (FourierTransform.fourier (f : ℝ → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hfint
  have heq : (fun v : ℝ ↦ yoshidaCriticalSampleLinear a ha v f) =
      fun v : ℝ ↦ FourierTransform.fourier (f : ℝ → ℂ)
        (v / (2 * Real.pi)) := by
    funext v
    exact yoshidaCriticalSample_eq_fourier ha v f
  rw [heq]
  exact hfourier.comp (by fun_prop)

/-- Critical-sample energy on the symmetric interval `[-T,T]`. -/
def clippedCentralEnergy
    (a : ℝ) (ha : 0 < a) (f : YoshidaClippedSmooth a) (T : ℝ) : ℝ :=
  ∫ t : ℝ in -T..T, Complex.normSq (yoshidaCriticalSampleLinear a ha t f)

/-- Reusable analytic core of Yoshida (6.6). The pointwise premise is exactly
the paired Cauchy--Schwarz estimate produced from (6.5); no positivity of the
critical form or extension to all `L²` is assumed. -/
theorem paired_central_energy_estimate6_6
    {a C T W : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (f : YoshidaClippedSmooth a)
    (hpoint : ∀ t ∈ Set.Icc (-T) T,
      Complex.normSq (yoshidaCriticalSampleLinear a ha t f) ≤
        a / Real.pi ^ 2 * Real.sin (a * t) ^ 2 * W) :
    C / (2 * Real.pi) * clippedCentralEnergy a ha f T ≤
      a * C / (2 * Real.pi ^ 3) *
        (T - Real.sin (2 * a * T) / (2 * a)) * W := by
  have hleftCont : Continuous (fun t : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha t f)) :=
    Complex.continuous_normSq.comp (continuous_yoshidaCriticalSample ha f)
  have hrightCont : Continuous (fun t : ℝ ↦
      a / Real.pi ^ 2 * Real.sin (a * t) ^ 2 * W) := by
    fun_prop
  have hIntegral : clippedCentralEnergy a ha f T ≤
      (a / Real.pi ^ 2 * W) *
        (T - Real.sin (2 * a * T) / (2 * a)) := by
    calc
      clippedCentralEnergy a ha f T ≤
          ∫ t : ℝ in -T..T,
            a / Real.pi ^ 2 * Real.sin (a * t) ^ 2 * W := by
        unfold clippedCentralEnergy
        exact intervalIntegral.integral_mono_on (by linarith)
          (hleftCont.intervalIntegrable (-T) T)
          (hrightCont.intervalIntegrable (-T) T) hpoint
      _ = (a / Real.pi ^ 2 * W) *
          (∫ t : ℝ in -T..T, Real.sin (a * t) ^ 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = (a / Real.pi ^ 2 * W) *
          (T - Real.sin (2 * a * T) / (2 * a)) := by
        rw [integral_sin_sq_mul_symmetric ha]
  have hscale : 0 ≤ C / (2 * Real.pi) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hIntegral hscale
  unfold clippedCentralEnergy at hscaled ⊢
  calc
    C / (2 * Real.pi) *
        (∫ t : ℝ in -T..T,
          Complex.normSq (yoshidaCriticalSampleLinear a ha t f)) ≤
        C / (2 * Real.pi) *
          ((a / Real.pi ^ 2 * W) *
            (T - Real.sin (2 * a * T) / (2 * a))) := hscaled
    _ = a * C / (2 * Real.pi ^ 3) *
        (T - Real.sin (2 * a * T) / (2 * a)) * W := by
      field_simp [Real.pi_ne_zero]

/-- Real polar contribution to the diagonal clipped critical form. -/
def clippedPolarEnergy
    (a : ℝ) (ha : 0 < a) (f : YoshidaClippedSmooth a) : ℝ :=
  2 * (star (yoshidaPositivePolarLinear a ha f) *
    yoshidaNegativePolarLinear a ha f).re

/-- Real archimedean contribution, including the `-log π` kernel term. -/
def clippedArchEnergy
    (a : ℝ) (ha : 0 < a) (f : YoshidaClippedSmooth a) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ v : ℝ,
    ((Complex.digamma
      ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re - Real.log Real.pi) *
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)

/-- Critical-line spectral mass in the repository normalization. -/
def clippedSpectralMass
    (a : ℝ) (ha : 0 < a) (f : YoshidaClippedSmooth a) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ v : ℝ,
    Complex.normSq (yoshidaCriticalSampleLinear a ha v f)

/-- Digamma-weighted critical-line energy before subtracting `log π`. -/
def clippedDigammaEnergy
    (a : ℝ) (ha : 0 < a) (f : YoshidaClippedSmooth a) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ v : ℝ,
    (Complex.digamma
      ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re *
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)

/-- The real diagonal value of the current clipped local critical form. -/
def clippedCriticalFormValue
    (a : ℝ) (ha : 0 < a) (f : YoshidaClippedSmooth a) : ℝ :=
  (yoshidaClippedLocalCriticalForm a ha f f).re

/-- On the diagonal, the clipped critical cross integrand is the coercion of
the real Bombieri kernel times the sample norm square. -/
theorem criticalCrossIntegrand_self_eq_ofReal
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) (v : ℝ) :
    yoshidaClippedCriticalCrossIntegrand a ha f f v =
      ((((Complex.digamma
        ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re - Real.log Real.pi) *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f) : ℝ) : ℂ) := by
  rw [yoshidaClippedCriticalCrossIntegrand,
    MultiplicativeWeil.bombieriLocalCriticalKernel]
  let s := yoshidaCriticalSampleLinear a ha v f
  let k := (Complex.digamma
    ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re - Real.log Real.pi
  have hnorm : star s * s = ((Complex.normSq s : ℝ) : ℂ) := by
    simpa only [starRingEnd_apply] using
      (Complex.normSq_eq_conj_mul_self (z := s)).symm
  change (k : ℂ) * star s * s = ((k * Complex.normSq s : ℝ) : ℂ)
  calc
    (k : ℂ) * star s * s = (k : ℂ) * (star s * s) := by ring
    _ = (k : ℂ) * (Complex.normSq s : ℂ) := by rw [hnorm]
    _ = ((k * Complex.normSq s : ℝ) : ℂ) := by push_cast; ring

/-- Exact real decomposition of the current clipped local critical form. -/
theorem clippedCriticalFormValue_eq_polar_add_arch
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    clippedCriticalFormValue a ha f =
      clippedPolarEnergy a ha f + clippedArchEnergy a ha f := by
  unfold clippedCriticalFormValue clippedPolarEnergy clippedArchEnergy
  rw [yoshidaClippedLocalCriticalForm_apply,
    yoshidaClippedLocalCriticalPairing]
  have hint :
      (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f f v) =
        (((∫ v : ℝ,
          ((Complex.digamma
            ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re - Real.log Real.pi) *
            Complex.normSq (yoshidaCriticalSampleLinear a ha v f) : ℝ)) : ℂ) := by
    calc
      (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f f v) =
          ∫ v : ℝ,
            ((((Complex.digamma
              ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re - Real.log Real.pi) *
              Complex.normSq (yoshidaCriticalSampleLinear a ha v f) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with v
        exact criticalCrossIntegrand_self_eq_ofReal ha f v
      _ = _ := integral_complex_ofReal
  rw [hint]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- When the two real terms are integrable, the archimedean energy is the
digamma energy minus `log π` times spectral mass. -/
theorem clippedArchEnergy_eq_digamma_sub_log_mass
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hDigamma : Integrable (fun v : ℝ ↦
      (Complex.digamma
        ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)))
    (hMass : Integrable (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f))) :
    clippedArchEnergy a ha f =
      clippedDigammaEnergy a ha f -
        Real.log Real.pi * clippedSpectralMass a ha f := by
  unfold clippedArchEnergy clippedDigammaEnergy clippedSpectralMass
  have hLogMass : Integrable (fun v : ℝ ↦
      Real.log Real.pi *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) :=
    hMass.const_mul _
  calc
    (1 / (2 * Real.pi)) *
        (∫ v : ℝ,
          ((Complex.digamma
            ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re - Real.log Real.pi) *
            Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) =
      (1 / (2 * Real.pi)) *
        (∫ v : ℝ,
          (Complex.digamma
            ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re *
              Complex.normSq (yoshidaCriticalSampleLinear a ha v f) -
            Real.log Real.pi *
              Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) := by
        apply congrArg (fun x : ℝ ↦ (1 / (2 * Real.pi)) * x)
        apply integral_congr_ae
        filter_upwards [] with v
        ring
    _ = (1 / (2 * Real.pi)) *
        ((∫ v : ℝ,
          (Complex.digamma
            ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re *
              Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) -
          ∫ v : ℝ, Real.log Real.pi *
            Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) := by
        rw [integral_sub hDigamma hLogMass]
    _ = (1 / (2 * Real.pi)) *
          (∫ v : ℝ,
            (Complex.digamma
              ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re *
                Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) -
        Real.log Real.pi *
          ((1 / (2 * Real.pi)) *
            ∫ v : ℝ, Complex.normSq
              (yoshidaCriticalSampleLinear a ha v f)) := by
        rw [integral_const_mul]
        ring

/-- The exact remaining archimedean content of Yoshida (6.4)--(6.7), after
the polar contribution has been separated from the current clipped form. -/
def ClippedSection6ArchLowerEstimate
    (N : ℕ) (tZero tOne : ℝ) (a : ℝ) (ha : 0 < a)
    (f : YoshidaClippedSmooth a) : Prop :=
  digammaQuarterVerticalRe tOne - Real.log Real.pi -
      highFrequencyPenalty N tOne (digammaQuarterVerticalRe tOne) -
      lowIntervalPenalty N tZero ≤
    clippedArchEnergy a ha f

/-- A finer description of the actual (6.4)--(6.6) obligation: the digamma
energy dominates `C` after the high- and low-frequency losses. -/
def ClippedSection6DigammaLowerEstimate
    (N : ℕ) (tZero tOne : ℝ) (a : ℝ) (ha : 0 < a)
    (f : YoshidaClippedSmooth a) : Prop :=
  digammaQuarterVerticalRe tOne -
      highFrequencyPenalty N tOne (digammaQuarterVerticalRe tOne) -
      lowIntervalPenalty N tZero ≤
    clippedDigammaEnergy a ha f

/-- Unit spectral mass and the source digamma split imply the archimedean
Section 6 lower estimate. The integrability assumptions are explicit. -/
theorem clippedSection6ArchLowerEstimate_of_digamma_parseval
    {N : ℕ} {tZero tOne a : ℝ} (ha : 0 < a)
    (f : YoshidaClippedSmooth a)
    (hDigammaInt : Integrable (fun v : ℝ ↦
      (Complex.digamma
        ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re *
        Complex.normSq (yoshidaCriticalSampleLinear a ha v f)))
    (hMassInt : Integrable (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)))
    (hParseval : clippedSpectralMass a ha f = 1)
    (hDigamma : ClippedSection6DigammaLowerEstimate
      N tZero tOne a ha f) :
    ClippedSection6ArchLowerEstimate N tZero tOne a ha f := by
  unfold ClippedSection6ArchLowerEstimate
  rw [clippedArchEnergy_eq_digamma_sub_log_mass
    ha f hDigammaInt hMassInt]
  rw [hParseval]
  unfold ClippedSection6DigammaLowerEstimate at hDigamma
  linarith

/-- Honest bridge from the named polar and archimedean estimates to the
production `section6LowerBound` and the actual clipped form value. -/
theorem section6LowerBound_le_clippedCriticalFormValue
    {N : ℕ} {tZero tOne a : ℝ} (ha : 0 < a)
    (f : YoshidaClippedSmooth a)
    (hpolar : -(1 / Real.sqrt 2 - Real.log 2) ≤
      clippedPolarEnergy a ha f)
    (harch : ClippedSection6ArchLowerEstimate N tZero tOne a ha f) :
    section6LowerBound N tZero tOne ≤
      clippedCriticalFormValue a ha f := by
  rw [clippedCriticalFormValue_eq_polar_add_arch ha f]
  unfold ClippedSection6ArchLowerEstimate at harch
  unfold section6LowerBound
  dsimp only
  linarith

/-- With a genuine Yoshida `t₀`, the remaining odd Section 6 analytic
premises imply the source coercivity constant on the actual clipped form. -/
theorem odd_clipped_form_value_ge_38_div_25
    {tZero : ℝ} (ht : YoshidaTZeroTailBounds.IsYoshidaTZero tZero)
    (f : YoshidaClippedSmooth YoshidaWeightedTailBounds.yoshidaA)
    (hpolar : -(1 / Real.sqrt 2 - Real.log 2) ≤
      clippedPolarEnergy YoshidaWeightedTailBounds.yoshidaA
        YoshidaCoercivityNumerics.yoshidaA_pos f)
    (harch : ClippedSection6ArchLowerEstimate 10 tZero 50
      YoshidaWeightedTailBounds.yoshidaA
      YoshidaCoercivityNumerics.yoshidaA_pos f) :
    (38 / 25 : ℝ) ≤
      clippedCriticalFormValue YoshidaWeightedTailBounds.yoshidaA
        YoshidaCoercivityNumerics.yoshidaA_pos f := by
  apply YoshidaCoercivityNumerics.odd_form_value_ge_of_yoshidaTZero_and_equation6_7 ht
  exact section6LowerBound_le_clippedCriticalFormValue
    YoshidaCoercivityNumerics.yoshidaA_pos f hpolar harch

/-- With a genuine Yoshida `t₀`, the remaining even Section 6 analytic
premises imply the source coercivity constant on the actual clipped form. -/
theorem even_clipped_form_value_ge_102_div_25
    {tZero : ℝ} (ht : YoshidaTZeroTailBounds.IsYoshidaTZero tZero)
    (f : YoshidaClippedSmooth YoshidaWeightedTailBounds.yoshidaA)
    (hpolar : -(1 / Real.sqrt 2 - Real.log 2) ≤
      clippedPolarEnergy YoshidaWeightedTailBounds.yoshidaA
        YoshidaCoercivityNumerics.yoshidaA_pos f)
    (harch : ClippedSection6ArchLowerEstimate 199 tZero 700
      YoshidaWeightedTailBounds.yoshidaA
      YoshidaCoercivityNumerics.yoshidaA_pos f) :
    (102 / 25 : ℝ) ≤
      clippedCriticalFormValue YoshidaWeightedTailBounds.yoshidaA
        YoshidaCoercivityNumerics.yoshidaA_pos f := by
  apply YoshidaCoercivityNumerics.even_form_value_ge_of_yoshidaTZero_and_equation6_7 ht
  exact section6LowerBound_le_clippedCriticalFormValue
    YoshidaCoercivityNumerics.yoshidaA_pos f hpolar harch

/-- The odd Section 6 bridge at the canonical certified Yoshida zero. -/
theorem odd_canonical_clipped_form_value_ge_38_div_25
    (f : YoshidaClippedSmooth YoshidaWeightedTailBounds.yoshidaA)
    (hpolar : -(1 / Real.sqrt 2 - Real.log 2) ≤
      clippedPolarEnergy YoshidaWeightedTailBounds.yoshidaA
        YoshidaCoercivityNumerics.yoshidaA_pos f)
    (harch : ClippedSection6ArchLowerEstimate 10
      YoshidaTZeroTailBounds.yoshidaTZero 50
      YoshidaWeightedTailBounds.yoshidaA
      YoshidaCoercivityNumerics.yoshidaA_pos f) :
    (38 / 25 : ℝ) ≤
      clippedCriticalFormValue YoshidaWeightedTailBounds.yoshidaA
        YoshidaCoercivityNumerics.yoshidaA_pos f :=
  odd_clipped_form_value_ge_38_div_25
    YoshidaTZeroTailBounds.isYoshidaTZero_yoshidaTZero f hpolar harch

/-- The even Section 6 bridge at the canonical certified Yoshida zero. -/
theorem even_canonical_clipped_form_value_ge_102_div_25
    (f : YoshidaClippedSmooth YoshidaWeightedTailBounds.yoshidaA)
    (hpolar : -(1 / Real.sqrt 2 - Real.log 2) ≤
      clippedPolarEnergy YoshidaWeightedTailBounds.yoshidaA
        YoshidaCoercivityNumerics.yoshidaA_pos f)
    (harch : ClippedSection6ArchLowerEstimate 199
      YoshidaTZeroTailBounds.yoshidaTZero 700
      YoshidaWeightedTailBounds.yoshidaA
      YoshidaCoercivityNumerics.yoshidaA_pos f) :
    (102 / 25 : ℝ) ≤
      clippedCriticalFormValue YoshidaWeightedTailBounds.yoshidaA
        YoshidaCoercivityNumerics.yoshidaA_pos f :=
  even_clipped_form_value_ge_102_div_25
    YoshidaTZeroTailBounds.isYoshidaTZero_yoshidaTZero f hpolar harch

end ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic
