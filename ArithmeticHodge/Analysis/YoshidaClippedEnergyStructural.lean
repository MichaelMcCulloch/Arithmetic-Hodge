import ArithmeticHodge.Analysis.YoshidaClippedCriticalForm
import Mathlib.Analysis.Fourier.FourierTransform

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set
open scoped ComplexConjugate FourierTransform

namespace ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic

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

/-- The unweighted critical-line norm square is integrable for every clipped
smooth function.  This is a generic Fourier-decay fact, independent of any
mode or coercivity certificate. -/
theorem integrable_normSq_yoshidaCriticalSample
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    Integrable (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) := by
  let D : ℝ := yoshidaCriticalDecayConstant a f
  let K : ℝ := 2 * D ^ 2
  let q : ℝ → ℝ := fun v ↦ (1 + v ^ 2)⁻¹
  let S : Set ℝ := Set.Icc (-1 : ℝ) 1
  have hD : 0 ≤ D := yoshidaCriticalDecayConstant_nonneg ha f
  have hcontinuous : Continuous (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) :=
    Complex.continuous_normSq.comp
      (continuous_yoshidaCriticalSample ha f)
  have hcompact : IntegrableOn (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) S :=
    hcontinuous.continuousOn.integrableOn_compact isCompact_Icc
  have hq : Integrable q := by
    simpa only [q] using integrable_inv_one_add_sq
  have hmajor : Integrable (fun v ↦ K * q v) := hq.const_mul K
  have htail : IntegrableOn (fun v : ℝ ↦
      Complex.normSq (yoshidaCriticalSampleLinear a ha v f)) Sᶜ := by
    apply hmajor.integrableOn.mono'
    · exact hcontinuous.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
      have habs : 1 < |v| := by
        by_contra h
        apply hv
        exact abs_le.mp (le_of_not_gt h)
      have hv0 : v ≠ 0 := abs_pos.mp (zero_lt_one.trans habs)
      have hs := yoshidaCriticalSample_norm_le_inv_abs ha v hv0 f
      have hsSq :
          Complex.normSq (yoshidaCriticalSampleLinear a ha v f) ≤
            D ^ 2 / v ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        have hs' : ‖yoshidaCriticalSampleLinear a ha v f‖ ≤ D / |v| := by
          simpa only [D] using hs
        have hright : 0 ≤ D / |v| := div_nonneg hD (abs_nonneg v)
        have hsq := sq_le_sq₀ (norm_nonneg _) hright |>.2 hs'
        simpa only [div_pow, sq_abs] using hsq
      have hrecip : 1 / v ^ 2 ≤ 2 / (1 + v ^ 2) := by
        have hvSq : 1 < v ^ 2 := by
          rw [← sq_abs]
          nlinarith
        rw [div_le_div_iff₀ (by positivity : 0 < v ^ 2)
          (by positivity : 0 < 1 + v ^ 2)]
        nlinarith
      have htailBound :
          Complex.normSq (yoshidaCriticalSampleLinear a ha v f) ≤
            K * q v := by
        calc
          Complex.normSq (yoshidaCriticalSampleLinear a ha v f) ≤
              D ^ 2 / v ^ 2 := hsSq
          _ ≤ D ^ 2 * (2 / (1 + v ^ 2)) := by
            have hmul := mul_le_mul_of_nonneg_left hrecip (sq_nonneg D)
            calc
              D ^ 2 / v ^ 2 = D ^ 2 * (1 / v ^ 2) := by ring
              _ ≤ D ^ 2 * (2 / (1 + v ^ 2)) := hmul
          _ = K * q v := by
            dsimp only [K, q]
            ring
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
      exact htailBound
  rw [← integrableOn_univ]
  simpa only [S, union_compl_self] using hcompact.union htail

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

end ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic
