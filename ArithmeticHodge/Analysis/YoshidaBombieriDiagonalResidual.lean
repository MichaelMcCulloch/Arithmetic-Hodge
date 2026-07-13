import ArithmeticHodge.Analysis.YoshidaBombieriCrossDistribution

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaBombieriDiagonalResidual

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution

/-!
# Positive diagonal residuals in Bombieri's digamma series

Every harmonic-subtracted Cauchy term in the diagonal critical form has a
strictly positive rational spectral multiplier.  This packages the complete
infinite family structurally; no finite truncation or enclosure is involved.
-/

def bombieriDiagonalResidualMultiplier (n : ℕ) (v : ℝ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)⁻¹) - bombieriDigammaKernel (n + 1) v

theorem bombieriDiagonalResidualMultiplier_eq (n : ℕ) (v : ℝ) :
    bombieriDiagonalResidualMultiplier n v =
      (v ^ 2 + (2 * ((n + 1 : ℕ) : ℝ) + 1 / 2) / 2) /
        (((n + 1 : ℕ) : ℝ) *
          ((2 * ((n + 1 : ℕ) : ℝ) + 1 / 2) ^ 2 + v ^ 2)) := by
  rw [bombieriDiagonalResidualMultiplier, bombieriDigammaKernel]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hm : (0 : ℝ) < n + 1 := by positivity
  have hden :
      (2 * ((n : ℝ) + 1) + 1 / 2) ^ 2 + v ^ 2 ≠ 0 := by
    positivity
  field_simp
  ring

theorem bombieriDiagonalResidualMultiplier_pos (n : ℕ) (v : ℝ) :
    0 < bombieriDiagonalResidualMultiplier n v := by
  rw [bombieriDiagonalResidualMultiplier_eq]
  positivity

def bombieriDiagonalResidualIntegrand
    (g : BombieriTest) (n : ℕ) (v : ℝ) : ℝ :=
  bombieriDiagonalResidualMultiplier n v *
    Complex.normSq (mellin (g : ℝ → ℂ)
      ((1 / 2 : ℝ) + v * Complex.I))

theorem bombieriCriticalNormSq_weighted_integrable (g : BombieriTest) :
    Integrable (fun v : ℝ ↦
      (1 + v ^ 2) * Complex.normSq
        (mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I))) := by
  have h := bombieriCriticalSpectralProduct_weighted_integrable g g
  apply h.congr
  filter_upwards [] with v
  simp only [bombieriCriticalSpectralProduct, norm_mul, norm_star,
    Complex.normSq_eq_norm_sq]
  ring

theorem bombieriDiagonalResidualIntegrand_integrable
    (g : BombieriTest) (n : ℕ) :
    Integrable (bombieriDiagonalResidualIntegrand g n) := by
  let M : ℝ → ℂ := fun v ↦
    mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)
  let p : ℝ := (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hW : Integrable (fun v : ℝ ↦
      (1 + v ^ 2) * Complex.normSq (M v)) := by
    simpa only [M] using bombieriCriticalNormSq_weighted_integrable g
  have hmajor : Integrable (fun v : ℝ ↦
      p * ((1 + v ^ 2) * Complex.normSq (M v))) := hW.const_mul p
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
    have hmass : Continuous (fun v : ℝ ↦ Complex.normSq (M v)) :=
      Complex.continuous_normSq.comp
        ((bombieriMellin_differentiable g).continuous.comp (by fun_prop))
    exact ((continuous_const.sub hkernel).mul hmass).aestronglyMeasurable
  · filter_upwards [] with v
    simp only [bombieriDiagonalResidualIntegrand, M,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
    have hcoefficient := abs_bombieriDigammaKernel_sub_inv_le n v
    have hmass : 0 ≤ Complex.normSq (M v) := Complex.normSq_nonneg _
    calc
      |bombieriDiagonalResidualMultiplier n v| * Complex.normSq (M v) ≤
          ((1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) *
            Complex.normSq (M v) := by
        apply mul_le_mul_of_nonneg_right _ hmass
        simpa only [bombieriDiagonalResidualMultiplier, abs_sub_comm] using
          hcoefficient
      _ = p * ((1 + v ^ 2) * Complex.normSq (M v)) := by
        simp only [p, div_eq_mul_inv]
        ring

def bombieriDiagonalResidual (g : BombieriTest) (n : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ v : ℝ, bombieriDiagonalResidualIntegrand g n v

theorem bombieriDiagonalResidual_nonneg (g : BombieriTest) (n : ℕ) :
    0 ≤ bombieriDiagonalResidual g n := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun v ↦
    mul_nonneg (bombieriDiagonalResidualMultiplier_pos n v).le
      (Complex.normSq_nonneg _)

def bombieriWeightedSpectralMass (g : BombieriTest) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ v : ℝ,
    (1 + v ^ 2) * Complex.normSq
      (mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I))

theorem bombieriWeightedSpectralMass_nonneg (g : BombieriTest) :
    0 ≤ bombieriWeightedSpectralMass g := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun v ↦
    mul_nonneg (by positivity) (Complex.normSq_nonneg _)

theorem bombieriDiagonalResidual_le_invSq_mul_mass
    (g : BombieriTest) (n : ℕ) :
    bombieriDiagonalResidual g n ≤
      (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * bombieriWeightedSpectralMass g := by
  let p : ℝ := (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  let W : ℝ → ℝ := fun v ↦
    (1 + v ^ 2) * Complex.normSq
      (mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I))
  have hW : Integrable W := by
    simpa only [W] using bombieriCriticalNormSq_weighted_integrable g
  have hmajor : Integrable (fun v : ℝ ↦ p * W v) := hW.const_mul p
  have hint :
      (∫ v : ℝ, bombieriDiagonalResidualIntegrand g n v) ≤
        ∫ v : ℝ, p * W v := by
    apply integral_mono (bombieriDiagonalResidualIntegrand_integrable g n)
      hmajor
    intro v
    have hcoefficient := abs_bombieriDigammaKernel_sub_inv_le n v
    have hmultiplier : bombieriDiagonalResidualMultiplier n v ≤
        (1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2) := by
      rw [← abs_of_pos (bombieriDiagonalResidualMultiplier_pos n v)]
      simpa only [bombieriDiagonalResidualMultiplier, abs_sub_comm] using
        hcoefficient
    have hmass : 0 ≤ Complex.normSq
        (mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)) :=
      Complex.normSq_nonneg _
    calc
      bombieriDiagonalResidualIntegrand g n v ≤
          ((1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) *
            Complex.normSq
              (mellin (g : ℝ → ℂ)
                ((1 / 2 : ℝ) + v * Complex.I)) := by
        exact mul_le_mul_of_nonneg_right hmultiplier hmass
      _ = p * W v := by
        simp only [p, W, div_eq_mul_inv]
        ring
  calc
    bombieriDiagonalResidual g n =
        (1 / (2 * Real.pi)) *
          ∫ v : ℝ, bombieriDiagonalResidualIntegrand g n v := rfl
    _ ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, p * W v :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = p * bombieriWeightedSpectralMass g := by
      rw [MeasureTheory.integral_const_mul]
      simp only [bombieriWeightedSpectralMass, W]
      ring
    _ = _ := rfl

theorem summable_bombieriDiagonalResidual (g : BombieriTest) :
    Summable (bombieriDiagonalResidual g) := by
  have hp : Summable (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    exact (summable_nat_add_iff 1).2
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  have hmajor := hp.mul_right (bombieriWeightedSpectralMass g)
  apply hmajor.of_nonneg_of_le
  · exact bombieriDiagonalResidual_nonneg g
  · exact bombieriDiagonalResidual_le_invSq_mul_mass g

theorem tsum_bombieriDiagonalResidual_nonneg (g : BombieriTest) :
    0 ≤ ∑' n : ℕ, bombieriDiagonalResidual g n :=
  tsum_nonneg (bombieriDiagonalResidual_nonneg g)

theorem ofReal_bombieriDiagonalResidual_eq_cauchyResidual
    (g : BombieriTest) (n : ℕ) :
    (bombieriDiagonalResidual g n : ℂ) =
      ((((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) *
          bombieriCriticalCrossCorrelation g g 0) -
        bombieriCauchyCrossValue g g (n + 1) := by
  let P : ℝ → ℂ := bombieriCriticalSpectralProduct g g
  let r : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
  let K : ℝ → ℂ := fun v ↦ (bombieriDigammaKernel (n + 1) v : ℂ)
  let R : ℝ → ℂ := fun v ↦
    (bombieriDiagonalResidualIntegrand g n v : ℂ)
  have hP : Integrable P := by
    simpa only [P] using bombieriCriticalSpectralProduct_integrable g g
  have hR : Integrable R := by
    simpa only [R] using
      (bombieriDiagonalResidualIntegrand_integrable g n).ofReal
  have hpoint (v : ℝ) :
      R v = (r : ℂ) * P v - K v * P v := by
    simp only [R, r, K, P, bombieriDiagonalResidualIntegrand,
      bombieriDiagonalResidualMultiplier, bombieriCriticalSpectralProduct]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [starRingEnd_apply]
    ring
  have hK : Integrable (fun v ↦ K v * P v) := by
    have hconst : Integrable (fun v ↦ (r : ℂ) * P v) := hP.const_mul _
    apply (hconst.sub hR).congr
    filter_upwards [] with v
    change (r : ℂ) * P v - R v = K v * P v
    rw [hpoint]
    ring
  calc
    (bombieriDiagonalResidual g n : ℂ) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, R v) := by
      rw [bombieriDiagonalResidual]
      push_cast
      rw [← integral_complex_ofReal]
    _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, ((r : ℂ) * P v - K v * P v)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      exact hpoint v
    _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ((r : ℂ) * (∫ v : ℝ, P v) -
            (∫ v : ℝ, K v * P v))) := by
      rw [integral_sub (hP.const_mul _) hK]
      congr 2
      exact MeasureTheory.integral_const_mul _ _
    _ = (r : ℂ) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, P v)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, K v * P v) := by ring
    _ = (r : ℂ) * bombieriCriticalCrossCorrelation g g 0 -
        bombieriCauchyCrossValue g g (n + 1) := by
      rw [show (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, P v) =
          bombieriCriticalCrossCorrelation g g 0 by
        simpa only [P] using
          normalized_integral_bombieriCriticalSpectralProduct_eq_zeroCorrelation
            g g]
      rw [show (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, K v * P v) =
          bombieriCauchyCrossValue g g (n + 1) by
        simpa only [K, P] using
          normalized_bombieriDigammaKernel_crossProduct g g (n + 1)]
    _ = _ := by
      simp only [r, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem summable_bombieriCauchySeriesResidual (g : BombieriTest) :
    Summable (fun n : ℕ ↦
      bombieriCauchyCrossValue g g (n + 1) -
        ((((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) *
          bombieriCriticalCrossCorrelation g g 0)) := by
  have hcast := Complex.ofRealCLM.summable
    (summable_bombieriDiagonalResidual g)
  apply hcast.neg.congr
  intro n
  rw [Complex.ofRealCLM_apply,
    ofReal_bombieriDiagonalResidual_eq_cauchyResidual]
  ring

theorem ofReal_tsum_bombieriDiagonalResidual_eq_cauchySeries
    (g : BombieriTest) :
    ((∑' n : ℕ, bombieriDiagonalResidual g n : ℝ) : ℂ) =
      ∑' n : ℕ,
        ((((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) *
            bombieriCriticalCrossCorrelation g g 0 -
          bombieriCauchyCrossValue g g (n + 1)) := by
  calc
    ((∑' n : ℕ, bombieriDiagonalResidual g n : ℝ) : ℂ) =
        ∑' n : ℕ, (bombieriDiagonalResidual g n : ℂ) := by
      simpa only [Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.map_tsum (summable_bombieriDiagonalResidual g)
    _ = _ := by
      apply tsum_congr
      intro n
      exact ofReal_bombieriDiagonalResidual_eq_cauchyResidual g n

theorem cauchySeries_eq_neg_ofReal_tsum_bombieriDiagonalResidual
    (g : BombieriTest) :
    (∑' n : ℕ,
      (bombieriCauchyCrossValue g g (n + 1) -
        ((((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) *
          bombieriCriticalCrossCorrelation g g 0))) =
      -((∑' n : ℕ, bombieriDiagonalResidual g n : ℝ) : ℂ) := by
  calc
    (∑' n : ℕ,
        (bombieriCauchyCrossValue g g (n + 1) -
          ((((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) *
            bombieriCriticalCrossCorrelation g g 0))) =
        -(∑' n : ℕ,
          ((((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) *
              bombieriCriticalCrossCorrelation g g 0 -
            bombieriCauchyCrossValue g g (n + 1))) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro n
      ring
    _ = -((∑' n : ℕ, bombieriDiagonalResidual g n : ℝ) : ℂ) := by
      rw [ofReal_tsum_bombieriDiagonalResidual_eq_cauchySeries]

end

end ArithmeticHodge.Analysis.YoshidaBombieriDiagonalResidual
