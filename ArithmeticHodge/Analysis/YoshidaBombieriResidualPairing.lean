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

private theorem bombieriDiagonalResidualIntegrand_add
    (f g : BombieriTest) (n : ℕ) (v : ℝ) :
    bombieriDiagonalResidualIntegrand (f + g) n v =
      bombieriDiagonalResidualIntegrand f n v +
        bombieriDiagonalResidualIntegrand g n v +
        2 * (bombieriResidualCrossIntegrand f g n v).re := by
  have hmellin :
      mellin ((f + g : BombieriTest) : ℝ → ℂ)
          ((1 / 2 : ℝ) + v * Complex.I) =
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I) +
          mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I) := by
    change
      mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I) (f + g) =
        mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I) f +
          mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I) g
    exact map_add _ _ _
  unfold bombieriDiagonalResidualIntegrand
  rw [hmellin, Complex.normSq_add]
  unfold bombieriResidualCrossIntegrand bombieriCriticalSpectralProduct
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero]
  ring

private theorem bombieriDiagonalResidualIntegrand_sub
    (f g : BombieriTest) (n : ℕ) (v : ℝ) :
    bombieriDiagonalResidualIntegrand (f - g) n v =
      bombieriDiagonalResidualIntegrand f n v +
        bombieriDiagonalResidualIntegrand g n v -
        2 * (bombieriResidualCrossIntegrand f g n v).re := by
  have hmellin :
      mellin ((f - g : BombieriTest) : ℝ → ℂ)
          ((1 / 2 : ℝ) + v * Complex.I) =
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I) -
          mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I) := by
    change
      mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I) (f - g) =
        mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I) f -
          mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I) g
    exact map_sub _ _ _
  unfold bombieriDiagonalResidualIntegrand
  rw [hmellin, Complex.normSq_sub]
  unfold bombieriResidualCrossIntegrand bombieriCriticalSpectralProduct
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero]
  ring

/-- Exact Hermitian polarization of one positive diagonal residual under
addition. -/
theorem bombieriDiagonalResidual_add
    (f g : BombieriTest) (n : ℕ) :
    bombieriDiagonalResidual (f + g) n =
      bombieriDiagonalResidual f n + bombieriDiagonalResidual g n +
        2 * (bombieriResidualCross f g n).re := by
  have hf := bombieriDiagonalResidualIntegrand_integrable f n
  have hg := bombieriDiagonalResidualIntegrand_integrable g n
  have hcross : Integrable (fun v : ℝ ↦
      (bombieriResidualCrossIntegrand f g n v).re) :=
    Complex.reCLM.integrable_comp
      (bombieriResidualCrossIntegrand_integrable f g n)
  have hsplit :
      (∫ v : ℝ, (bombieriDiagonalResidualIntegrand f n v +
        bombieriDiagonalResidualIntegrand g n v +
          2 * (bombieriResidualCrossIntegrand f g n v).re)) =
        (∫ v : ℝ, bombieriDiagonalResidualIntegrand f n v) +
          (∫ v : ℝ, bombieriDiagonalResidualIntegrand g n v) +
          2 * ∫ v : ℝ, (bombieriResidualCrossIntegrand f g n v).re := by
    calc
      _ = (∫ v : ℝ, (bombieriDiagonalResidualIntegrand f n v +
              bombieriDiagonalResidualIntegrand g n v)) +
            ∫ v : ℝ, 2 * (bombieriResidualCrossIntegrand f g n v).re := by
        simpa only [Pi.add_apply] using
          (integral_add (hf.add hg) (hcross.const_mul 2))
      _ = _ := by
        rw [show (∫ v : ℝ, (bombieriDiagonalResidualIntegrand f n v +
              bombieriDiagonalResidualIntegrand g n v)) =
            (∫ v : ℝ, bombieriDiagonalResidualIntegrand f n v) +
              ∫ v : ℝ, bombieriDiagonalResidualIntegrand g n v by
          simpa only [Pi.add_apply] using integral_add hf hg,
          MeasureTheory.integral_const_mul]
  have hreal :
      (∫ v : ℝ, (bombieriResidualCrossIntegrand f g n v).re) =
        (∫ v : ℝ, bombieriResidualCrossIntegrand f g n v).re := by
    simpa only [RCLike.re_to_complex] using
      integral_re (bombieriResidualCrossIntegrand_integrable f g n)
  unfold bombieriDiagonalResidual bombieriResidualCross
  rw [show (∫ v : ℝ, bombieriDiagonalResidualIntegrand (f + g) n v) =
      ∫ v : ℝ, (bombieriDiagonalResidualIntegrand f n v +
        bombieriDiagonalResidualIntegrand g n v +
          2 * (bombieriResidualCrossIntegrand f g n v).re) by
    apply integral_congr_ae
    filter_upwards [] with v
    exact bombieriDiagonalResidualIntegrand_add f g n v]
  rw [hsplit]
  rw [hreal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- Exact Hermitian polarization of one positive diagonal residual under
subtraction. -/
theorem bombieriDiagonalResidual_sub
    (f g : BombieriTest) (n : ℕ) :
    bombieriDiagonalResidual (f - g) n =
      bombieriDiagonalResidual f n + bombieriDiagonalResidual g n -
        2 * (bombieriResidualCross f g n).re := by
  have hf := bombieriDiagonalResidualIntegrand_integrable f n
  have hg := bombieriDiagonalResidualIntegrand_integrable g n
  have hcross : Integrable (fun v : ℝ ↦
      (bombieriResidualCrossIntegrand f g n v).re) :=
    Complex.reCLM.integrable_comp
      (bombieriResidualCrossIntegrand_integrable f g n)
  have hsplit :
      (∫ v : ℝ, (bombieriDiagonalResidualIntegrand f n v +
        bombieriDiagonalResidualIntegrand g n v -
          2 * (bombieriResidualCrossIntegrand f g n v).re)) =
        (∫ v : ℝ, bombieriDiagonalResidualIntegrand f n v) +
          (∫ v : ℝ, bombieriDiagonalResidualIntegrand g n v) -
          2 * ∫ v : ℝ, (bombieriResidualCrossIntegrand f g n v).re := by
    calc
      _ = (∫ v : ℝ, (bombieriDiagonalResidualIntegrand f n v +
              bombieriDiagonalResidualIntegrand g n v)) -
            ∫ v : ℝ, 2 * (bombieriResidualCrossIntegrand f g n v).re := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          (integral_sub (hf.add hg) (hcross.const_mul 2))
      _ = _ := by
        rw [show (∫ v : ℝ, (bombieriDiagonalResidualIntegrand f n v +
              bombieriDiagonalResidualIntegrand g n v)) =
            (∫ v : ℝ, bombieriDiagonalResidualIntegrand f n v) +
              ∫ v : ℝ, bombieriDiagonalResidualIntegrand g n v by
          simpa only [Pi.add_apply] using integral_add hf hg,
          MeasureTheory.integral_const_mul]
  have hreal :
      (∫ v : ℝ, (bombieriResidualCrossIntegrand f g n v).re) =
        (∫ v : ℝ, bombieriResidualCrossIntegrand f g n v).re := by
    simpa only [RCLike.re_to_complex] using
      integral_re (bombieriResidualCrossIntegrand_integrable f g n)
  unfold bombieriDiagonalResidual bombieriResidualCross
  rw [show (∫ v : ℝ, bombieriDiagonalResidualIntegrand (f - g) n v) =
      ∫ v : ℝ, (bombieriDiagonalResidualIntegrand f n v +
        bombieriDiagonalResidualIntegrand g n v -
          2 * (bombieriResidualCrossIntegrand f g n v).re) by
    apply integral_congr_ae
    filter_upwards [] with v
    exact bombieriDiagonalResidualIntegrand_sub f g n v]
  rw [hsplit]
  rw [hreal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

private theorem normSq_integral_star_mul_le
    (F G : ℝ → ℂ)
    (hFmeas : AEStronglyMeasurable F)
    (hGmeas : AEStronglyMeasurable G)
    (hFsq : Integrable (fun v : ℝ ↦ ‖F v‖ ^ 2))
    (hGsq : Integrable (fun v : ℝ ↦ ‖G v‖ ^ 2)) :
    Complex.normSq (∫ v : ℝ, star (F v) * G v) ≤
      (∫ v : ℝ, ‖F v‖ ^ 2) * ∫ v : ℝ, ‖G v‖ ^ 2 := by
  have hFLp : MemLp F 2 volume :=
    (memLp_two_iff_integrable_sq_norm hFmeas).2 hFsq
  have hGLp : MemLp G 2 volume :=
    (memLp_two_iff_integrable_sq_norm hGmeas).2 hGsq
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := F) (g := G) (μ := volume)
    Real.HolderConjugate.two_two (by simpa using hFLp) (by simpa using hGLp)
  let A : ℝ := ∫ v : ℝ, ‖F v‖ ^ 2
  let B : ℝ := ∫ v : ℝ, ‖G v‖ ^ 2
  have hA0 : 0 ≤ A := integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun _ ↦ sq_nonneg _
  have hholder' :
      (∫ v : ℝ, ‖F v‖ * ‖G v‖) ≤ Real.sqrt A * Real.sqrt B := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [A, B, Real.rpow_two] using hholder
  have hnorm :
      ‖∫ v : ℝ, star (F v) * G v‖ ≤
        ∫ v : ℝ, ‖F v‖ * ‖G v‖ := by
    calc
      ‖∫ v : ℝ, star (F v) * G v‖ ≤
          ∫ v : ℝ, ‖star (F v) * G v‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ v : ℝ, ‖F v‖ * ‖G v‖ := by
        apply integral_congr_ae
        filter_upwards [] with v
        rw [norm_mul, norm_star]
  have hbound := hnorm.trans hholder'
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∫ v : ℝ, star (F v) * G v‖ ^ 2 ≤
        (Real.sqrt A * Real.sqrt B) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hbound
    _ = A * B := by
      rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    _ = _ := rfl

theorem normSq_bombieriResidualCross_le
    (f g : BombieriTest) (n : ℕ) :
    Complex.normSq (bombieriResidualCross f g n) ≤
      bombieriDiagonalResidual f n * bombieriDiagonalResidual g n := by
  let w : ℝ → ℝ := bombieriDiagonalResidualMultiplier n
  let Mf : ℝ → ℂ := fun v ↦
    mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)
  let Mg : ℝ → ℂ := fun v ↦
    mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)
  let F : ℝ → ℂ := fun v ↦ (Real.sqrt (w v) : ℂ) * Mf v
  let G : ℝ → ℂ := fun v ↦ (Real.sqrt (w v) : ℂ) * Mg v
  have hkernel : Continuous (fun v : ℝ ↦
      bombieriDigammaKernel (n + 1) v) := by
    unfold bombieriDigammaKernel
    apply Continuous.div continuous_const
      ((continuous_const.pow 2).add (continuous_id.pow 2))
    intro v
    change (2 * (((n + 1 : ℕ) : ℝ)) + 1 / 2) ^ 2 + v ^ 2 ≠ 0
    positivity
  have hw : Continuous w := by
    exact continuous_const.sub hkernel
  have hMf : Continuous Mf :=
    (bombieriMellin_differentiable f).continuous.comp (by fun_prop)
  have hMg : Continuous Mg :=
    (bombieriMellin_differentiable g).continuous.comp (by fun_prop)
  have hF : Continuous F := by
    exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hw)).mul hMf
  have hG : Continuous G := by
    exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hw)).mul hMg
  have hFsq : Integrable (fun v : ℝ ↦ ‖F v‖ ^ 2) := by
    apply (bombieriDiagonalResidualIntegrand_integrable f n).congr
    filter_upwards [] with v
    have hw0 := (bombieriDiagonalResidualMultiplier_pos n v).le
    simp only [F, w, Mf, bombieriDiagonalResidualIntegrand,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hw0, Complex.normSq_eq_norm_sq]
  have hGsq : Integrable (fun v : ℝ ↦ ‖G v‖ ^ 2) := by
    apply (bombieriDiagonalResidualIntegrand_integrable g n).congr
    filter_upwards [] with v
    have hw0 := (bombieriDiagonalResidualMultiplier_pos n v).le
    simp only [G, w, Mg, bombieriDiagonalResidualIntegrand,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hw0, Complex.normSq_eq_norm_sq]
  have hcross :
      (∫ v : ℝ, star (F v) * G v) =
        ∫ v : ℝ, bombieriResidualCrossIntegrand f g n v := by
    apply integral_congr_ae
    filter_upwards [] with v
    have hw0 := (bombieriDiagonalResidualMultiplier_pos n v).le
    change
      star ((Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ) *
          mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)) *
          ((Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ) *
            mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)) =
        (bombieriDiagonalResidualMultiplier n v : ℂ) *
          (star (mellin (f : ℝ → ℂ)
              ((1 / 2 : ℝ) + v * Complex.I)) *
            mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I))
    rw [star_mul]
    have hstar :
        star (Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ) =
          (Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ) := by
      simp
    rw [hstar]
    have hsqrt :
        (Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ) *
            (Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ) =
          (bombieriDiagonalResidualMultiplier n v : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw0]
    calc
      star (mellin (f : ℝ → ℂ)
            ((1 / 2 : ℝ) + v * Complex.I)) *
          (Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ) *
          ((Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ) *
            mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I)) =
          star (mellin (f : ℝ → ℂ)
              ((1 / 2 : ℝ) + v * Complex.I)) *
            ((Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ) *
              (Real.sqrt (bombieriDiagonalResidualMultiplier n v) : ℂ)) *
            mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I) := by ring
      _ = _ := by rw [hsqrt]; ring
  have hcs := normSq_integral_star_mul_le F G
    hF.aestronglyMeasurable hG.aestronglyMeasurable hFsq hGsq
  rw [hcross] at hcs
  have hFint :
      (∫ v : ℝ, ‖F v‖ ^ 2) =
        ∫ v : ℝ, bombieriDiagonalResidualIntegrand f n v := by
    apply integral_congr_ae
    filter_upwards [] with v
    have hw0 := (bombieriDiagonalResidualMultiplier_pos n v).le
    simp only [F, w, Mf, bombieriDiagonalResidualIntegrand,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hw0, Complex.normSq_eq_norm_sq]
  have hGint :
      (∫ v : ℝ, ‖G v‖ ^ 2) =
        ∫ v : ℝ, bombieriDiagonalResidualIntegrand g n v := by
    apply integral_congr_ae
    filter_upwards [] with v
    have hw0 := (bombieriDiagonalResidualMultiplier_pos n v).le
    simp only [G, w, Mg, bombieriDiagonalResidualIntegrand,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hw0, Complex.normSq_eq_norm_sq]
  rw [hFint, hGint] at hcs
  let c : ℝ := 1 / (2 * Real.pi)
  let A : ℝ := ∫ v : ℝ, bombieriDiagonalResidualIntegrand f n v
  let B : ℝ := ∫ v : ℝ, bombieriDiagonalResidualIntegrand g n v
  let I : ℂ := ∫ v : ℝ, bombieriResidualCrossIntegrand f g n v
  have hcs' : Complex.normSq I ≤ A * B := by
    simpa only [I, A, B] using hcs
  rw [bombieriResidualCross, bombieriDiagonalResidual,
    bombieriDiagonalResidual]
  change Complex.normSq ((c : ℂ) * I) ≤ (c * A) * (c * B)
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  calc
    c * c * Complex.normSq I = c ^ 2 * Complex.normSq I := by ring
    _ ≤ c ^ 2 * (A * B) :=
      mul_le_mul_of_nonneg_left hcs' (sq_nonneg c)
    _ = _ := by ring

end

end ArithmeticHodge.Analysis.YoshidaBombieriResidualPairing
