import ArithmeticHodge.Analysis.YoshidaBombieriDiagonalResidual

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaBombieriResidualPairing

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaBombieriDiagonalResidual

/-!
# Sesquilinear positive residual pairings

The positive diagonal multiplier is applied to an arbitrary pair of Bombieri
tests.  This exposes the Hermitian cross term that must be retained in the
factor-two determinant argument.
-/

def bombieriResidualCrossIntegrand
    (f g : BombieriTest) (n : ℕ) (v : ℝ) : ℂ :=
  (bombieriDiagonalResidualMultiplier n v : ℂ) *
    bombieriCriticalSpectralProduct f g v

theorem bombieriResidualCrossIntegrand_integrable
    (f g : BombieriTest) (n : ℕ) :
    Integrable (bombieriResidualCrossIntegrand f g n) := by
  let p : ℝ := (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hW := bombieriCriticalSpectralProduct_weighted_integrable f g
  have hmajor : Integrable (fun v : ℝ ↦
      p * ((1 + v ^ 2) * ‖bombieriCriticalSpectralProduct f g v‖)) :=
    hW.const_mul p
  apply hmajor.mono'
  · have hkernel : Continuous (fun v : ℝ ↦
        bombieriDigammaKernel (n + 1) v) := by
      unfold bombieriDigammaKernel
      apply Continuous.div continuous_const
        ((continuous_const.pow 2).add (continuous_id.pow 2))
      intro v
      change
        (2 * (((n + 1 : ℕ) : ℝ)) + 1 / 2) ^ 2 + v ^ 2 ≠ 0
      positivity
    have hmult : Continuous (fun v : ℝ ↦
        bombieriDiagonalResidualMultiplier n v) := by
      exact continuous_const.sub hkernel
    have hproduct : Continuous (bombieriCriticalSpectralProduct f g) := by
      unfold bombieriCriticalSpectralProduct
      exact (((bombieriMellin_differentiable f).continuous.comp
          (by fun_prop)).star).mul
        ((bombieriMellin_differentiable g).continuous.comp (by fun_prop))
    exact ((Complex.continuous_ofReal.comp hmult).mul
      hproduct).aestronglyMeasurable
  · filter_upwards [] with v
    simp only [bombieriResidualCrossIntegrand, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have hcoefficient := abs_bombieriDigammaKernel_sub_inv_le n v
    have hmass : 0 ≤ ‖bombieriCriticalSpectralProduct f g v‖ := norm_nonneg _
    calc
      |bombieriDiagonalResidualMultiplier n v| *
          ‖bombieriCriticalSpectralProduct f g v‖ ≤
          ((1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) *
            ‖bombieriCriticalSpectralProduct f g v‖ := by
        apply mul_le_mul_of_nonneg_right _ hmass
        simpa only [bombieriDiagonalResidualMultiplier, abs_sub_comm] using
          hcoefficient
      _ = p * ((1 + v ^ 2) *
          ‖bombieriCriticalSpectralProduct f g v‖) := by
        simp only [p, div_eq_mul_inv]
        ring

def bombieriResidualCross
    (f g : BombieriTest) (n : ℕ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ v : ℝ, bombieriResidualCrossIntegrand f g n v)

theorem bombieriResidualCross_eq_cauchyResidual
    (f g : BombieriTest) (n : ℕ) :
    bombieriResidualCross f g n =
      ((((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) *
          bombieriCriticalCrossCorrelation f g 0) -
        bombieriCauchyCrossValue f g (n + 1) := by
  let P : ℝ → ℂ := bombieriCriticalSpectralProduct f g
  let r : ℂ := (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)
  let K : ℝ → ℂ := fun v ↦ (bombieriDigammaKernel (n + 1) v : ℂ)
  let R : ℝ → ℂ := bombieriResidualCrossIntegrand f g n
  have hP : Integrable P := by
    simpa only [P] using bombieriCriticalSpectralProduct_integrable f g
  have hR : Integrable R := by
    simpa only [R] using bombieriResidualCrossIntegrand_integrable f g n
  have hpoint (v : ℝ) :
      R v = r * P v - K v * P v := by
    simp only [R, r, K, P, bombieriResidualCrossIntegrand,
      bombieriDiagonalResidualMultiplier]
    push_cast
    ring
  have hK : Integrable (fun v ↦ K v * P v) := by
    have hconst : Integrable (fun v ↦ r * P v) := hP.const_mul _
    apply (hconst.sub hR).congr
    filter_upwards [] with v
    change r * P v - R v = K v * P v
    rw [hpoint]
    ring
  calc
    bombieriResidualCross f g n =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (r * P v - K v * P v)) := by
      rw [bombieriResidualCross]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      exact hpoint v
    _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (r * (∫ v : ℝ, P v) -
          (∫ v : ℝ, K v * P v))) := by
      rw [integral_sub (hP.const_mul _) hK]
      congr 2
      exact MeasureTheory.integral_const_mul _ _
    _ = r *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, P v)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, K v * P v) := by ring
    _ = r * bombieriCriticalCrossCorrelation f g 0 -
        bombieriCauchyCrossValue f g (n + 1) := by
      rw [show (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, P v) =
          bombieriCriticalCrossCorrelation f g 0 by
        simpa only [P] using
          normalized_integral_bombieriCriticalSpectralProduct_eq_zeroCorrelation
            f g]
      rw [show (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, K v * P v) =
          bombieriCauchyCrossValue f g (n + 1) by
        simpa only [K, P] using
          normalized_bombieriDigammaKernel_crossProduct f g (n + 1)]
    _ = _ := by
      simp only [r]

theorem bombieriResidualCross_self
    (g : BombieriTest) (n : ℕ) :
    bombieriResidualCross g g n =
      (bombieriDiagonalResidual g n : ℂ) := by
  rw [bombieriResidualCross_eq_cauchyResidual]
  exact (ofReal_bombieriDiagonalResidual_eq_cauchyResidual g n).symm

end

end ArithmeticHodge.Analysis.YoshidaBombieriResidualPairing
