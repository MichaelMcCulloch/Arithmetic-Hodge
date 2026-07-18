import ArithmeticHodge.Analysis.MultiplicativeWeilDilationMellin
import ArithmeticHodge.Analysis.YoshidaBombieriCrossMoments

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFarLocalCrossStructural

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments

/-!
# Exact local-critical cross at a separated dilation

For a cross from `f` to a normalized dilation of `g`, separation on the
negative logarithmic half-line makes the initial Cauchy summand a rank-one
endpoint term.  Its `r⁻¹ᐟ²` contribution cancels the corresponding polar
endpoint in the local critical form exactly.  What remains is the growing
`r¹ᐟ²` endpoint and the complete Cauchy tail; no estimate or truncation enters
the identity.
-/

private theorem sqrt_mul_exp_neg_log
    (r : ℝ) (hr : 0 < r) :
    Real.sqrt r * Real.exp (-Real.log r) = (Real.sqrt r)⁻¹ := by
  have hsqrt :
      Real.sqrt r = Real.exp (Real.log r / 2) := by
    rw [← Real.exp_log (Real.sqrt_pos.2 hr), Real.log_sqrt hr.le]
  rw [hsqrt, ← Real.exp_add, ← Real.exp_neg]
  congr 1
  ring

/-- The zero Mellin endpoint of a normalized dilation has weight `r¹ᐟ²`. -/
theorem mellin_normalizedDilation_zero
    (r : ℝ) (hr : 0 < r) (g : BombieriTest) :
    mellin (normalizedDilation r hr g : ℝ → ℂ) 0 =
      ((Real.sqrt r : ℝ) : ℂ) * mellin (g : ℝ → ℂ) 0 := by
  have h := mellin_normalizedDilation_vertical r hr g 0 0
  simpa using h

/-- The one Mellin endpoint of a normalized dilation has weight `r⁻¹ᐟ²`. -/
theorem mellin_normalizedDilation_one
    (r : ℝ) (hr : 0 < r) (g : BombieriTest) :
    mellin (normalizedDilation r hr g : ℝ → ℂ) 1 =
      (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * mellin (g : ℝ → ℂ) 1 := by
  have h := mellin_normalizedDilation_vertical r hr g 1 0
  have h' :
      mellin (normalizedDilation r hr g : ℝ → ℂ) 1 =
        ((Real.sqrt r * Real.exp (-1 * Real.log r) : ℝ) : ℂ) *
          mellin (g : ℝ → ℂ) 1 := by
    simpa using h
  rw [show Real.sqrt r * Real.exp (-1 * Real.log r) =
      (Real.sqrt r)⁻¹ by
    simpa only [neg_one_mul] using sqrt_mul_exp_neg_log r hr] at h'
  exact h'

/-- If the logarithmic cross-correlation has no negative-lag support, the
initial Cauchy summand is exactly the decaying endpoint product. -/
theorem bombieriCauchyCrossValue_zero_dilation_eq_endpoint
    (f g : BombieriTest) (r : ℝ) (hr : 0 < r)
    (hnegative : ∀ u : ℝ, u < 0 →
      bombieriCriticalCrossCorrelation f
        (normalizedDilation r hr g) u = 0) :
    bombieriCauchyCrossValue f (normalizedDilation r hr g) 0 =
      (((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
        starRingEnd ℂ (mellin (f : ℝ → ℂ) 0) *
          mellin (g : ℝ → ℂ) 1 := by
  have hremoveAbs :
      bombieriCauchyCrossValue f (normalizedDilation r hr g) 0 =
        ∫ u : ℝ, ((Real.exp ((-(1 / 2 : ℝ)) * u) : ℝ) : ℂ) *
          bombieriCriticalCrossCorrelation f
            (normalizedDilation r hr g) u := by
    rw [bombieriCauchyCrossValue]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
      congr 2
      norm_num
    · have hzero := hnegative u (lt_of_not_ge hu)
      rw [hzero, mul_zero, mul_zero]
  rw [hremoveAbs,
    integral_exp_mul_bombieriCriticalCrossCorrelation]
  rw [show -(-(1 / 2 : ℝ)) = 1 / 2 by ring,
    bombieriCriticalMoment_half_eq_mellin_zero,
    bombieriCriticalMoment_neg_half_eq_mellin_one,
    mellin_normalizedDilation_one r hr g]
  simp only [starRingEnd_apply]
  ring

/-- Zero correlation removes every Euler/`log π` renormalization term from
the normalized local critical-kernel distribution. -/
theorem normalized_localCriticalKernel_dilation_eq_neg_cauchySeries
    (f g : BombieriTest) (r : ℝ) (hr : 0 < r)
    (hzero : bombieriCriticalCrossCorrelation f
      (normalizedDilation r hr g) 0 = 0) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, bombieriLocalCriticalKernel v *
        bombieriCriticalSpectralProduct f
          (normalizedDilation r hr g) v) =
      -(bombieriCauchyCrossValue f (normalizedDilation r hr g) 0 +
        ∑' k : ℕ, bombieriCauchyCrossValue f
          (normalizedDilation r hr g) (k + 1)) := by
  have hdist := normalized_localCriticalKernel_crossProduct_eq_cauchySeries
    f (normalizedDilation r hr g)
  rw [bombieriCrossDigammaCauchySeriesValue, hzero] at hdist
  simpa using hdist

/-- Exact separated local-critical formula.  The `r⁻¹ᐟ²` polar endpoint is
cancelled by the zeroth Cauchy summand, leaving only the `r¹ᐟ²` endpoint and
the untruncated Cauchy tail. -/
theorem bombieriLocalCriticalForm_dilation_eq_endpoint_sub_cauchyTail
    (f g : BombieriTest) (r : ℝ) (hr : 0 < r)
    (hnegative : ∀ u : ℝ, u < 0 →
      bombieriCriticalCrossCorrelation f
        (normalizedDilation r hr g) u = 0)
    (hzero : bombieriCriticalCrossCorrelation f
      (normalizedDilation r hr g) 0 = 0) :
    bombieriLocalCriticalForm f (normalizedDilation r hr g) =
      ((Real.sqrt r : ℝ) : ℂ) *
          starRingEnd ℂ (mellin (f : ℝ → ℂ) 1) *
            mellin (g : ℝ → ℂ) 0 -
        ∑' k : ℕ, bombieriCauchyCrossValue f
          (normalizedDilation r hr g) (k + 1) := by
  have hcritical :=
    normalized_localCriticalKernel_dilation_eq_neg_cauchySeries
      f g r hr hzero
  have hcritical' :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, bombieriLocalCriticalCrossIntegrand f
          (normalizedDilation r hr g) v) =
        -(bombieriCauchyCrossValue f (normalizedDilation r hr g) 0 +
          ∑' k : ℕ, bombieriCauchyCrossValue f
            (normalizedDilation r hr g) (k + 1)) := by
    simpa only [bombieriLocalCriticalCrossIntegrand,
      bombieriCriticalSpectralProduct, mellinLinearMap_apply,
      mul_assoc] using hcritical
  rw [bombieriLocalCriticalForm_apply]
  unfold bombieriLocalCriticalPairing
  rw [hcritical']
  simp only [mellinLinearMap_apply, starRingEnd_apply]
  rw [mellin_normalizedDilation_zero r hr g,
    mellin_normalizedDilation_one r hr g,
    bombieriCauchyCrossValue_zero_dilation_eq_endpoint
      f g r hr hnegative]
  simp only [starRingEnd_apply]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFarLocalCrossStructural
