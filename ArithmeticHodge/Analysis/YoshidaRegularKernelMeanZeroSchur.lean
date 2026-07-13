import ArithmeticHodge.Analysis.YoshidaRegularKernelSchur

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaRegularKernelMeanZeroSchur

open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

noncomputable section

/-!
# Mean-zero Schur bound for Yoshida's regular kernel

On the endpoint square the regular kernel lies in `[0,1/4]`.  For a
mean-zero function its constant `1/8` component contributes nothing, while
the centered kernel has absolute value at most `1/8`.  This improves the
dimension-free Schur constant by a factor of two without using a mode
cutoff or a numerical certificate.
-/

/-- Cancellation of the constant kernel improves the endpoint regular
quadratic bound from `1/2` to `1/4` on the mean-zero subspace. -/
theorem norm_yoshidaEndpointRegularQuadratic_le_of_integral_eq_zero
    (f : ℝ → ℂ) (hf : Continuous f)
    (hmean : (∫ x : ℝ in Icc (-1) 1, f x) = 0) :
    ‖yoshidaEndpointRegularQuadratic f‖ ≤
      (1 / 4 : ℝ) * ∫ x : ℝ in Icc (-1) 1, ‖f x‖ ^ 2 := by
  let I : Set ℝ := Icc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  let K : ℝ × ℝ → ℂ := fun p ↦
    (yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) : ℂ)
  let K₀ : ℝ × ℝ → ℂ := fun p ↦
    ((yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) -
      (1 / 8 : ℝ) : ℝ) : ℂ)
  let G : ℝ × ℝ → ℂ := fun p ↦
    K p * f p.2 * star (f p.1)
  let G₀ : ℝ × ℝ → ℂ := fun p ↦
    K₀ p * f p.2 * star (f p.1)
  let C : ℝ × ℝ → ℂ := fun p ↦
    (1 / 8 : ℂ) * (star (f p.1) * f p.2)
  have hregularMeas : Measurable yoshidaRegularKernel := by
    unfold yoshidaRegularKernel
    apply Measurable.ite (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  have hK₀Meas : Measurable K₀ := by
    dsimp only [K₀]
    fun_prop
  have hfInt : Integrable f μ := by
    simpa only [μ, I] using
      hf.continuousOn.integrableOn_compact isCompact_Icc
  have hfStarInt : Integrable (fun x ↦ star (f x)) μ := by
    simpa only [Complex.conjCLE_apply] using
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hfInt
  have hprodNorm : Integrable
      (fun p : ℝ × ℝ ↦ ‖f p.1‖ * ‖f p.2‖) (μ.prod μ) :=
    hfInt.norm.mul_prod hfInt.norm
  have hdomInt : Integrable
      (fun p : ℝ × ℝ ↦ (1 / 8 : ℝ) * (‖f p.1‖ * ‖f p.2‖))
      (μ.prod μ) :=
    hprodNorm.const_mul (1 / 8 : ℝ)
  have hpMem : ∀ᵐ p ∂μ.prod μ, p ∈ I ×ˢ I := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hK₀Bound : ∀ᵐ p ∂μ.prod μ, ‖K₀ p‖ ≤ (1 / 8 : ℝ) := by
    filter_upwards [hpMem] with p hp
    have habs : |p.1 - p.2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
    have harg0 : 0 ≤ (Real.log 2 / 2) * |p.1 - p.2| :=
      mul_nonneg (by positivity) (abs_nonneg _)
    have harg2 : (Real.log 2 / 2) * |p.1 - p.2| ≤ Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_left habs
        (by positivity : 0 ≤ Real.log 2 / 2)
      nlinarith
    have hreg := yoshidaRegularKernel_mem_Icc harg0 harg2
    dsimp only [K₀]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hreg.1, hreg.2]
  have hG₀Meas : AEStronglyMeasurable G₀ (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G₀]
    fun_prop
  have hG₀Int : Integrable G₀ (μ.prod μ) := by
    refine hdomInt.mono' hG₀Meas ?_
    filter_upwards [hK₀Bound] with p hp
    dsimp only [G₀]
    rw [norm_mul, norm_mul, norm_star]
    have hnonneg : 0 ≤ ‖f p.1‖ * ‖f p.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right hp hnonneg
    nlinarith
  have hstarProdInt : Integrable
      (fun p : ℝ × ℝ ↦ star (f p.1) * f p.2) (μ.prod μ) :=
    hfStarInt.mul_prod hfInt
  have hCInt : Integrable C (μ.prod μ) := by
    dsimp only [C]
    exact hstarProdInt.const_mul (1 / 8 : ℂ)
  have hmeanμ : (∫ x : ℝ, f x ∂μ) = 0 := by
    simpa only [μ, I] using hmean
  have hCzero : (∫ p : ℝ × ℝ, C p ∂μ.prod μ) = 0 := by
    dsimp only [C]
    calc
      (∫ p : ℝ × ℝ,
          (1 / 8 : ℂ) * (star (f p.1) * f p.2) ∂μ.prod μ) =
        (1 / 8 : ℂ) *
          ∫ p : ℝ × ℝ, star (f p.1) * f p.2 ∂μ.prod μ :=
        MeasureTheory.integral_const_mul _ _
      _ = (1 / 8 : ℂ) *
          ((∫ x : ℝ, star (f x) ∂μ) * ∫ x : ℝ, f x ∂μ) := by
        exact congrArg (fun z : ℂ ↦ (1 / 8 : ℂ) * z)
          (integral_prod_mul (μ := μ) (ν := μ)
            (fun x : ℝ ↦ star (f x)) f)
      _ = 0 := by rw [hmeanμ, mul_zero, mul_zero]
  have hdecomp : ∀ p : ℝ × ℝ, G p = G₀ p + C p := by
    intro p
    dsimp only [G, G₀, C, K, K₀]
    push_cast
    ring
  have hintegralDecomp :
      (∫ p : ℝ × ℝ, G p ∂μ.prod μ) =
        ∫ p : ℝ × ℝ, G₀ p ∂μ.prod μ := by
    calc
      _ = ∫ p : ℝ × ℝ, (G₀ p + C p) ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards [] with p
        exact hdecomp p
      _ = (∫ p : ℝ × ℝ, G₀ p ∂μ.prod μ) +
          ∫ p : ℝ × ℝ, C p ∂μ.prod μ :=
        integral_add hG₀Int hCInt
      _ = _ := by rw [hCzero, add_zero]
  have hquad₀ :
      ‖∫ p : ℝ × ℝ, G₀ p ∂μ.prod μ‖ ≤
        (1 / 8 : ℝ) * (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 := by
    calc
      ‖∫ p : ℝ × ℝ, G₀ p ∂μ.prod μ‖ ≤
          ∫ p : ℝ × ℝ, ‖G₀ p‖ ∂μ.prod μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ p : ℝ × ℝ,
          (1 / 8 : ℝ) * (‖f p.1‖ * ‖f p.2‖) ∂μ.prod μ := by
        apply integral_mono_ae hG₀Int.norm hdomInt
        filter_upwards [hK₀Bound] with p hp
        dsimp only [G₀]
        rw [norm_mul, norm_mul, norm_star]
        have hnonneg : 0 ≤ ‖f p.1‖ * ‖f p.2‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have hmul := mul_le_mul_of_nonneg_right hp hnonneg
        nlinarith
      _ = (1 / 8 : ℝ) * (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 := by
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
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hE0]
        norm_num
  unfold yoshidaEndpointRegularQuadratic
  change ‖∫ p : ℝ × ℝ, G p ∂μ.prod μ‖ ≤ _
  rw [hintegralDecomp]
  calc
    ‖∫ p : ℝ × ℝ, G₀ p ∂μ.prod μ‖ ≤
        (1 / 8 : ℝ) * (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 := hquad₀
    _ ≤ (1 / 8 : ℝ) *
        (2 * ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hL1sq (by norm_num)
    _ = (1 / 4 : ℝ) *
        ∫ x : ℝ in Icc (-1) 1, ‖f x‖ ^ 2 := by
      simp only [μ, I]
      ring

end

end ArithmeticHodge.Analysis.YoshidaRegularKernelMeanZeroSchur
