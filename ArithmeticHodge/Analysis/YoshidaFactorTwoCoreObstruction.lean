import ArithmeticHodge.Analysis.YoshidaFactorTwoCoreReduction
import ArithmeticHodge.Analysis.MultiplicativeWeilPrimeDilationObstruction
import ArithmeticHodge.Analysis.YoshidaCriticalLogCorrelation

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCoreObstruction

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaFactorTwoCoreReduction
open YoshidaCriticalLogCorrelation

/-!
# Obstruction to separating the factor-two core from the positive residual

The diagonal core is not a positive form.  In particular, every nonzero test
whose two polar Mellin moments vanish has strictly negative core diagonal.
Thus the positive residual cannot be discarded by a triangle inequality in a
proof of the factor-two determinant.
-/

def bombieriInitialCauchyEnergy (g : BombieriTest) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ v : ℝ,
    bombieriDigammaKernel 0 v *
      Complex.normSq (mellin (g : ℝ → ℂ)
        ((1 / 2 : ℝ) + v * Complex.I))

theorem bombieriInitialCauchyEnergy_nonneg (g : BombieriTest) :
    0 ≤ bombieriInitialCauchyEnergy g := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun v ↦
    mul_nonneg (by
      unfold bombieriDigammaKernel
      positivity) (Complex.normSq_nonneg _)

theorem ofReal_bombieriInitialCauchyEnergy_eq
    (g : BombieriTest) :
    (bombieriInitialCauchyEnergy g : ℂ) =
      bombieriCauchyCrossValue g g 0 := by
  calc
    (bombieriInitialCauchyEnergy g : ℂ) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel 0 v : ℂ) *
            bombieriCriticalSpectralProduct g g v) := by
      rw [bombieriInitialCauchyEnergy]
      push_cast
      rw [← integral_complex_ofReal]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      simp [bombieriCriticalSpectralProduct,
        Complex.normSq_eq_conj_mul_self, mul_comm]
    _ = bombieriCauchyCrossValue g g 0 :=
      normalized_bombieriDigammaKernel_crossProduct g g 0

theorem bombieriInitialCauchyValue_re_nonneg (g : BombieriTest) :
    0 ≤ (bombieriCauchyCrossValue g g 0).re := by
  rw [← ofReal_bombieriInitialCauchyEnergy_eq]
  exact bombieriInitialCauchyEnergy_nonneg g

theorem bombieriCriticalCrossCorrelation_self_zero_eq_quadratic_one
    (g : BombieriTest) :
    bombieriCriticalCrossCorrelation g g 0 = bombieriQuadraticTest g 1 := by
  rw [bombieriCriticalCrossCorrelation_zero_eq_inner,
    bombieriQuadraticTest_apply_one]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Complex.normSq_eq_conj_mul_self]

theorem bombieriCriticalCrossCorrelation_self_zero_re_pos
    (g : BombieriTest) (hg : g ≠ 0) :
    0 < (bombieriCriticalCrossCorrelation g g 0).re := by
  rw [bombieriCriticalCrossCorrelation_self_zero_eq_quadratic_one]
  exact bombieriQuadraticTest_apply_one_re_pos g hg

theorem bombieriCoreDiagonal_neg_of_polar_moments_zero
    (g : BombieriTest) (hg : g ≠ 0)
    (hzero : mellin (g : ℝ → ℂ) 0 = 0)
    (hone : mellin (g : ℝ → ℂ) 1 = 0) :
    bombieriCoreDiagonal g < 0 := by
  have hA0 := bombieriInitialCauchyValue_re_nonneg g
  have hC0 := bombieriCriticalCrossCorrelation_self_zero_re_pos g hg
  have hgamma : 0 < Real.eulerMascheroniConstant :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans
      Real.one_half_lt_eulerMascheroniConstant
  have hlogpi : 0 < Real.log Real.pi :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  have hgammaC : 0 < Real.eulerMascheroniConstant *
      (bombieriCriticalCrossCorrelation g g 0).re := mul_pos hgamma hC0
  have hlogpiC : 0 < Real.log Real.pi *
      (bombieriCriticalCrossCorrelation g g 0).re := mul_pos hlogpi hC0
  unfold bombieriCoreDiagonal bombieriCoreDiagonalSymbol
  rw [hzero, hone]
  simp only [star_zero, zero_mul, add_zero, sub_re, mul_re, ofReal_re,
    ofReal_im, zero_mul, sub_zero, zero_re]
  linarith

theorem not_core_bound_of_polar_moments_zero
    (g : BombieriTest) (hg : g ≠ 0)
    (hzero : mellin (g : ℝ → ℂ) 0 = 0)
    (hone : mellin (g : ℝ → ℂ) 1 = 0) :
    ¬ ‖factorTwoCoreCrossSymbol g‖ ≤ bombieriCoreDiagonal g := by
  intro h
  have hn := norm_nonneg (factorTwoCoreCrossSymbol g)
  have hc := bombieriCoreDiagonal_neg_of_polar_moments_zero
    g hg hzero hone
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCoreObstruction
