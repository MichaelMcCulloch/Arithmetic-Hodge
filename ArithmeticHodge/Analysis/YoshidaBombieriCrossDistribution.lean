import ArithmeticHodge.Analysis.YoshidaCauchyPairing
import ArithmeticHodge.Analysis.YoshidaDigammaDistribution
import ArithmeticHodge.Analysis.MultiplicativeWeilLocalCriticalForm

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped FourierTransform SchwartzMap

namespace ArithmeticHodge.Analysis.YoshidaBombieriCrossDistribution

noncomputable section

open MultiplicativeWeil
open YoshidaCauchyPairing
open YoshidaDigammaDistribution

/-!
# The Bombieri cross distribution in logarithmic coordinates

This is the sesquilinear counterpart of the diagonal Yoshida bridge.  It
identifies the critical-line product for two arbitrary Bombieri tests with
the cross-correlation of their critical logarithmic pullbacks.  Keeping the
product complex is essential for adjacent-cell determinant arguments.
-/

def bombieriCriticalSpectralProduct
    (f g : BombieriTest) (v : ℝ) : ℂ :=
  star (mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)) *
    mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)

def bombieriCriticalCrossCorrelation
    (f g : BombieriTest) (u : ℝ) : ℂ :=
  crossCorrelation
    (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ)
    (g.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) u

def bombieriCauchyCrossValue
    (f g : BombieriTest) (k : ℕ) : ℂ :=
  ∫ u : ℝ,
    (Real.exp (-(2 * (k : ℝ) + 1 / 2) * |u|) : ℝ) *
      bombieriCriticalCrossCorrelation f g u

theorem bombieriCriticalSpectralProduct_eq_angular
    (f g : BombieriTest) (v : ℝ) :
    bombieriCriticalSpectralProduct f g v =
      star (angularFourier
        (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) v) *
      angularFourier
        (g.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) v := by
  rw [bombieriCriticalSpectralProduct,
    bombieriMellin_vertical_eq_fourier,
    bombieriMellin_vertical_eq_fourier]
  rfl

private theorem continuous_bombieriCriticalSpectralProduct
    (f g : BombieriTest) :
    Continuous (bombieriCriticalSpectralProduct f g) := by
  unfold bombieriCriticalSpectralProduct
  exact (((bombieriMellin_differentiable f).continuous.comp
      (by fun_prop)).star).mul
    ((bombieriMellin_differentiable g).continuous.comp (by fun_prop))

theorem bombieriCriticalSpectralProduct_weighted_integrable
    (f g : BombieriTest) :
    Integrable (fun v : ℝ ↦
      (1 + v ^ 2) * ‖bombieriCriticalSpectralProduct f g v‖) := by
  let C : ℝ :=
    ‖SchwartzMap.toBoundedContinuousFunction
      (𝓕 (f.logarithmicPullbackSchwartz (1 / 2)))‖
  let W : ℝ → ℝ := fun v ↦
    (1 + v ^ 2) *
      ‖mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)‖
  have hW : Integrable W := by
    simpa only [W] using bombieriMellin_one_add_sq_norm_integrable g
  have hmajor : Integrable (fun v : ℝ ↦ C * W v) := hW.const_mul C
  apply hmajor.mono'
  · exact ((continuous_const.add (continuous_id.pow 2)).mul
      (continuous_bombieriCriticalSpectralProduct f g).norm).aestronglyMeasurable
  · filter_upwards [] with v
    have hf :
        ‖mellin (f : ℝ → ℂ)
            ((1 / 2 : ℝ) + v * Complex.I)‖ ≤ C := by
      rw [bombieriMellin_vertical_eq_fourier]
      simpa only [C, SchwartzMap.toBoundedContinuousFunction_apply] using
        BoundedContinuousFunction.norm_coe_le_norm
          (SchwartzMap.toBoundedContinuousFunction
            (𝓕 (f.logarithmicPullbackSchwartz (1 / 2))))
          (v / (2 * Real.pi))
    have hnonneg :
        0 ≤ (1 + v ^ 2) *
          ‖mellin (g : ℝ → ℂ)
            ((1 / 2 : ℝ) + v * Complex.I)‖ := by positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    calc
      (1 + v ^ 2) * ‖bombieriCriticalSpectralProduct f g v‖ =
          ‖mellin (f : ℝ → ℂ)
              ((1 / 2 : ℝ) + v * Complex.I)‖ * W v := by
        simp only [bombieriCriticalSpectralProduct, norm_mul, norm_star, W]
        ring
      _ ≤ C * W v := mul_le_mul_of_nonneg_right hf hnonneg

theorem bombieriCriticalSpectralProduct_integrable
    (f g : BombieriTest) :
    Integrable (bombieriCriticalSpectralProduct f g) := by
  have hW := bombieriCriticalSpectralProduct_weighted_integrable f g
  apply hW.mono'
  · exact (continuous_bombieriCriticalSpectralProduct f g).aestronglyMeasurable
  · filter_upwards [] with v
    calc
      ‖bombieriCriticalSpectralProduct f g v‖ ≤
          (1 + v ^ 2) * ‖bombieriCriticalSpectralProduct f g v‖ := by
        exact le_mul_of_one_le_left (norm_nonneg _)
          (by nlinarith [sq_nonneg v])

private theorem bombieriFourierProduct_integrable
    (f g : BombieriTest) :
    Integrable (fun w : ℝ ↦
      star (FourierTransform.fourier
        (f.logarithmicPullbackSchwartz (1 / 2)) w) *
      FourierTransform.fourier
        (g.logarithmicPullbackSchwartz (1 / 2)) w) := by
  let F : SchwartzMap ℝ ℂ :=
    𝓕 (f.logarithmicPullbackSchwartz (1 / 2))
  let G : SchwartzMap ℝ ℂ :=
    𝓕 (g.logarithmicPullbackSchwartz (1 / 2))
  have hG : Integrable (G : ℝ → ℂ) := G.integrable
  have hFcont : Continuous (fun w : ℝ ↦ star (F w)) := F.continuous.star
  have hprod := hG.bdd_mul hFcont.aestronglyMeasurable
    (c := ‖SchwartzMap.toBoundedContinuousFunction F‖)
    (by
      filter_upwards [] with w
      simpa only [norm_star,
        SchwartzMap.toBoundedContinuousFunction_apply] using
        BoundedContinuousFunction.norm_coe_le_norm
          (SchwartzMap.toBoundedContinuousFunction F) w)
  apply hprod.congr
  filter_upwards [] with w
  rfl

theorem normalized_bombieriDigammaKernel_crossProduct
    (f g : BombieriTest) (k : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
        bombieriCriticalSpectralProduct f g v) =
      bombieriCauchyCrossValue f g k := by
  let b : ℝ := 2 * (k : ℝ) + 1 / 2
  have hb : 0 < b := by positivity
  have h := angular_cauchy_crossCorrelation_pairing
    (f.logarithmicPullbackSchwartz (1 / 2)).integrable
    (g.logarithmicPullbackSchwartz (1 / 2)).integrable
    (f.logarithmicPullbackSchwartz (1 / 2)).continuous
    (g.logarithmicPullbackSchwartz (1 / 2)).continuous
    (g.logarithmicPullback_hasCompactSupport (1 / 2))
    (bombieriFourierProduct_integrable f g) b hb
  have hkernel (v : ℝ) :
      (bombieriDigammaKernel k v : ℂ) =
        (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) := by
    unfold bombieriDigammaKernel
    dsimp only [b]
    push_cast
    ring
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
        bombieriCriticalSpectralProduct f g v) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) *
              (star (angularFourier
                (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) v) *
              angularFourier
                (g.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ) v)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      rw [hkernel, bombieriCriticalSpectralProduct_eq_angular]
    _ = bombieriCauchyCrossValue f g k := by
      simpa only [bombieriCauchyCrossValue,
        bombieriCriticalCrossCorrelation, b] using h

private theorem starReflection_bombieriCriticalPullback_integrable
    (f : BombieriTest) :
    Integrable (starReflection
      (f.logarithmicPullbackSchwartz (1 / 2) : ℝ → ℂ)) := by
  have hneg : Integrable (fun x : ℝ ↦
      f.logarithmicPullbackSchwartz (1 / 2) (-x)) :=
    (f.logarithmicPullbackSchwartz (1 / 2)).integrable.comp_neg
  simpa only [starReflection, RCLike.star_def] using
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg

private theorem bombieriCriticalCrossCorrelation_integrable
    (f g : BombieriTest) :
    Integrable (bombieriCriticalCrossCorrelation f g) := by
  exact (starReflection_bombieriCriticalPullback_integrable f).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (g.logarithmicPullbackSchwartz (1 / 2)).integrable

private theorem bombieriCriticalCrossCorrelation_continuous
    (f g : BombieriTest) :
    Continuous (bombieriCriticalCrossCorrelation f g) := by
  exact (g.logarithmicPullback_hasCompactSupport (1 / 2)).continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ)
    (starReflection_bombieriCriticalPullback_integrable f).locallyIntegrable
    (g.logarithmicPullbackSchwartz (1 / 2)).continuous

theorem normalized_integral_bombieriCriticalSpectralProduct_eq_zeroCorrelation
    (f g : BombieriTest) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, bombieriCriticalSpectralProduct f g v) =
      bombieriCriticalCrossCorrelation f g 0 := by
  let H : ℝ → ℂ := bombieriCriticalCrossCorrelation f g
  have hH : Integrable H := by
    simpa only [H] using bombieriCriticalCrossCorrelation_integrable f g
  have hHcont : Continuous H := by
    simpa only [H] using bombieriCriticalCrossCorrelation_continuous f g
  have hFH : Integrable (FourierTransform.fourier H) := by
    apply (bombieriFourierProduct_integrable f g).congr
    filter_upwards [] with w
    exact (fourier_crossCorrelation
      (f.logarithmicPullbackSchwartz (1 / 2)).integrable
      (g.logarithmicPullbackSchwartz (1 / 2)).integrable
      (f.logarithmicPullbackSchwartz (1 / 2)).continuous
      (g.logarithmicPullbackSchwartz (1 / 2)).continuous w).symm
  have hinv : FourierTransform.fourierInv
      (FourierTransform.fourier H) 0 = H 0 :=
    hH.fourierInv_fourier_eq hFH hHcont.continuousAt
  have hzero : (∫ w : ℝ, FourierTransform.fourier H w) = H 0 := by
    rw [Real.fourierInv_eq] at hinv
    simpa using hinv
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := by positivity
  have hscale := Measure.integral_comp_mul_left
    (bombieriCriticalSpectralProduct f g) c
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, bombieriCriticalSpectralProduct f g v) =
        |c⁻¹| • ∫ v : ℝ, bombieriCriticalSpectralProduct f g v := by
      rw [Complex.real_smul]
      congr 1
      dsimp [c]
      rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
      push_cast
      rw [one_div]
    _ = ∫ w : ℝ, bombieriCriticalSpectralProduct f g (c * w) :=
      hscale.symm
    _ = ∫ w : ℝ,
        star (FourierTransform.fourier
          (f.logarithmicPullbackSchwartz (1 / 2)) w) *
        FourierTransform.fourier
          (g.logarithmicPullbackSchwartz (1 / 2)) w := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [bombieriCriticalSpectralProduct_eq_angular]
      unfold angularFourier
      rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
      congr 3 <;> dsimp [c] <;> field_simp [Real.pi_ne_zero]
    _ = ∫ w : ℝ, FourierTransform.fourier H w := by
      apply integral_congr_ae
      filter_upwards [] with w
      exact (fourier_crossCorrelation
        (f.logarithmicPullbackSchwartz (1 / 2)).integrable
        (g.logarithmicPullbackSchwartz (1 / 2)).integrable
        (f.logarithmicPullbackSchwartz (1 / 2)).continuous
        (g.logarithmicPullbackSchwartz (1 / 2)).continuous w).symm
    _ = H 0 := hzero
    _ = bombieriCriticalCrossCorrelation f g 0 := rfl

def bombieriCrossDigammaCauchySeriesValue
    (f g : BombieriTest) : ℂ :=
  -(bombieriCauchyCrossValue f g 0 +
      (Real.eulerMascheroniConstant : ℂ) *
        bombieriCriticalCrossCorrelation f g 0 +
      ∑' k : ℕ,
        (bombieriCauchyCrossValue f g (k + 1) -
          (((k + 1 : ℕ) : ℝ)⁻¹ : ℂ) *
            bombieriCriticalCrossCorrelation f g 0)) -
    (Real.log Real.pi : ℂ) * bombieriCriticalCrossCorrelation f g 0

theorem normalized_localCriticalKernel_crossProduct_eq_cauchySeries
    (f g : BombieriTest) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, bombieriLocalCriticalKernel v *
        bombieriCriticalSpectralProduct f g v) =
      bombieriCrossDigammaCauchySeriesValue f g := by
  simpa only [bombieriLocalCriticalKernel,
    bombieriCrossDigammaCauchySeriesValue] using
    localCriticalKernel_integral_eq_cauchySeries
      (bombieriCriticalSpectralProduct f g)
      (bombieriCriticalSpectralProduct_integrable f g)
      (bombieriCriticalSpectralProduct_weighted_integrable f g)
      (bombieriCauchyCrossValue f g)
      (bombieriCriticalCrossCorrelation f g 0)
      (normalized_bombieriDigammaKernel_crossProduct f g)
      (normalized_integral_bombieriCriticalSpectralProduct_eq_zeroCorrelation f g)

end

end ArithmeticHodge.Analysis.YoshidaBombieriCrossDistribution
