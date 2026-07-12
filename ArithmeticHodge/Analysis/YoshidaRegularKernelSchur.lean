import ArithmeticHodge.Analysis.YoshidaRegularKernelBound
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaRegularKernelSchur

open YoshidaRegularKernelBound

noncomputable section

/-!
# Structural Schur bound for Yoshida's regular kernel

The pointwise bound `0 ≤ h ≤ 1 / 4` on the endpoint square gives an
operator bound without discretizing the kernel.  This is the exact regular
remainder estimate needed by the continuous endpoint inequality.
-/

/-- The endpoint regular-kernel quadratic form on the scaled interval
`[-1,1]`. -/
def yoshidaEndpointRegularQuadratic (f : ℝ → ℂ) : ℂ :=
  let μ : Measure ℝ := volume.restrict (Icc (-1) 1)
  ∫ p : ℝ × ℝ,
    (yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) : ℂ) *
      f p.2 * star (f p.1) ∂μ.prod μ

/-- Uniform endpoint Schur estimate.  Its constant comes only from the
interval length and the structural pointwise bound on the regular kernel. -/
theorem norm_yoshidaEndpointRegularQuadratic_le
    (f : ℝ → ℂ) (hf : Continuous f) :
    ‖yoshidaEndpointRegularQuadratic f‖ ≤
      (1 / 2 : ℝ) * ∫ x : ℝ in Icc (-1) 1, ‖f x‖ ^ 2 := by
  let I : Set ℝ := Icc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  let K : ℝ × ℝ → ℂ := fun p ↦
    (yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) : ℂ)
  let G : ℝ × ℝ → ℂ := fun p ↦ K p * f p.2 * star (f p.1)
  have hregularMeas : Measurable yoshidaRegularKernel := by
    unfold yoshidaRegularKernel
    apply Measurable.ite (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  have hKMeas : Measurable K := by
    dsimp only [K]
    fun_prop
  have hfInt : Integrable f μ := by
    simpa only [μ, I] using
      hf.continuousOn.integrableOn_compact isCompact_Icc
  have hprodNorm : Integrable
      (fun p : ℝ × ℝ ↦ ‖f p.1‖ * ‖f p.2‖) (μ.prod μ) :=
    hfInt.norm.mul_prod hfInt.norm
  have hdomInt : Integrable
      (fun p : ℝ × ℝ ↦ (1 / 4 : ℝ) * (‖f p.1‖ * ‖f p.2‖))
      (μ.prod μ) :=
    hprodNorm.const_mul (1 / 4 : ℝ)
  have hpMem : ∀ᵐ p ∂μ.prod μ, p ∈ I ×ˢ I := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hKBound : ∀ᵐ p ∂μ.prod μ, ‖K p‖ ≤ (1 / 4 : ℝ) := by
    filter_upwards [hpMem] with p hp
    have habs : |p.1 - p.2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
    have harg0 : 0 ≤ (Real.log 2 / 2) * |p.1 - p.2| :=
      mul_nonneg (by positivity) (abs_nonneg _)
    have harg2 : (Real.log 2 / 2) * |p.1 - p.2| ≤ Real.log 2 := by
      have := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ Real.log 2 / 2)
      nlinarith
    have hreg := yoshidaRegularKernel_mem_Icc harg0 harg2
    dsimp only [K]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hreg.1]
    exact hreg.2
  have hGMeas : AEStronglyMeasurable G (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G]
    fun_prop
  have hGInt : Integrable G (μ.prod μ) := by
    refine hdomInt.mono' hGMeas ?_
    filter_upwards [hKBound] with p hp
    dsimp only [G]
    rw [norm_mul, norm_mul, norm_star]
    have hnonneg : 0 ≤ ‖f p.1‖ * ‖f p.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right hp hnonneg
    nlinarith
  have hquad :
      ‖∫ p : ℝ × ℝ, G p ∂μ.prod μ‖ ≤
        (1 / 4 : ℝ) * (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 := by
    calc
      ‖∫ p : ℝ × ℝ, G p ∂μ.prod μ‖ ≤
          ∫ p : ℝ × ℝ, ‖G p‖ ∂μ.prod μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ p : ℝ × ℝ,
          (1 / 4 : ℝ) * (‖f p.1‖ * ‖f p.2‖) ∂μ.prod μ := by
        apply integral_mono_ae hGInt.norm hdomInt
        filter_upwards [hKBound] with p hp
        dsimp only [G]
        rw [norm_mul, norm_mul, norm_star]
        have hnonneg : 0 ≤ ‖f p.1‖ * ‖f p.2‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have hmul := mul_le_mul_of_nonneg_right hp hnonneg
        nlinarith
      _ = (1 / 4 : ℝ) * (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 := by
        rw [MeasureTheory.integral_const_mul,
          integral_prod_mul (fun x : ℝ ↦ ‖f x‖) (fun x : ℝ ↦ ‖f x‖)]
        ring
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    simpa only [μ, I] using
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hconst : MemLp (fun _ : ℝ ↦ (1 : ℂ)) 2 μ := memLp_const 1
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (by simpa using hconst) (by simpa using hfLp)
  simp at hholder
  have hlen : μ.real Set.univ = 2 := by
    norm_num [μ, I]
  rw [hlen] at hholder
  have hL10 : 0 ≤ ∫ x : ℝ, ‖f x‖ ∂μ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hE0 : 0 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hrhs0 : 0 ≤
      (2 : ℝ) ^ ((2 : ℝ)⁻¹) *
        (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hE0 _)
  have hL1sq :
      (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 ≤
        2 * ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ := by
    have hsqle :
        (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 ≤
          (((2 : ℝ) ^ ((2 : ℝ)⁻¹)) *
            ((∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹))) ^ 2 :=
      (sq_le_sq₀ hL10 hrhs0).2 hholder
    calc
      (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 ≤ _ := hsqle
      _ = 2 * ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ := by
        rw [mul_pow]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hE0]
        norm_num
  unfold yoshidaEndpointRegularQuadratic
  change ‖∫ p : ℝ × ℝ, G p ∂μ.prod μ‖ ≤ _
  calc
    ‖∫ p : ℝ × ℝ, G p ∂μ.prod μ‖ ≤
        (1 / 4 : ℝ) * (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 := hquad
    _ ≤ (1 / 4 : ℝ) *
        (2 * ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hL1sq (by norm_num)
    _ = (1 / 2 : ℝ) * ∫ x : ℝ in Icc (-1) 1, ‖f x‖ ^ 2 := by
      simp only [μ, I]
      ring

end

end ArithmeticHodge.Analysis.YoshidaRegularKernelSchur
