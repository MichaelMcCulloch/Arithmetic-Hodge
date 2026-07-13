import ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantCross
import ArithmeticHodge.Analysis.YoshidaEndpointEvenStructuralReduction
import ArithmeticHodge.Analysis.YoshidaRegularKernelLowerBound

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenLowRegular

open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaRegularKernelBound
open YoshidaRegularKernelLowerBound
open YoshidaRegularKernelSchur

noncomputable section

/-- Exact `L¹` mass of the centered quadratic Legendre mode. -/
theorem integral_abs_centeredEvenP2 :
    (∫ x : ℝ in -1..1, |centeredEvenP2 x|) =
      4 * Real.sqrt 3 / 9 := by
  let r : ℝ := Real.sqrt 3 / 3
  let p : ℝ → ℝ := centeredEvenP2
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hr1 : r ≤ 1 := by
    dsimp only [r]
    nlinarith [Real.sqrt_nonneg 3]
  have hrSq : 3 * r ^ 2 = 1 := by
    dsimp only [r]
    nlinarith
  have hpNonpos {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ r) : p x ≤ 0 := by
    have hsq : x ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hx0 hr0).2 hxr
    dsimp only [p, centeredEvenP2]
    nlinarith
  have hpNonneg {x : ℝ} (hrx : r ≤ x) (hx0 : 0 ≤ x) : 0 ≤ p x := by
    have hsq : r ^ 2 ≤ x ^ 2 := (sq_le_sq₀ hr0 hx0).2 hrx
    dsimp only [p, centeredEvenP2]
    nlinarith
  have hpEven : Function.Even p := by
    intro x
    dsimp only [p, centeredEvenP2]
    congr 1
    ring
  have habsEven : Function.Even (fun x ↦ |p x|) := fun x ↦ by
    change |p (-x)| = |p x|
    rw [hpEven x]
  have hcont : Continuous (fun x ↦ |p x|) := by
    dsimp only [p, centeredEvenP2]
    fun_prop
  have hfold : (∫ x : ℝ in -1..1, |p x|) =
      2 * ∫ x : ℝ in 0..1, |p x| := by
    have hleft : IntervalIntegrable (fun x ↦ |p x|) volume (-1) 0 :=
      hcont.intervalIntegrable (-1) 0
    have hright : IntervalIntegrable (fun x ↦ |p x|) volume 0 1 :=
      hcont.intervalIntegrable 0 1
    have hreflect : (∫ x : ℝ in 0..1, |p (-x)|) =
        ∫ x : ℝ in -1..0, |p x| := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg
          (f := fun x : ℝ ↦ |p x|) (a := (0 : ℝ)) (b := 1))
    calc
      (∫ x : ℝ in -1..1, |p x|) =
          (∫ x : ℝ in -1..0, |p x|) + ∫ x : ℝ in 0..1, |p x| :=
        (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
      _ = (∫ x : ℝ in 0..1, |p x|) + ∫ x : ℝ in 0..1, |p x| := by
        congr 1
        rw [← hreflect]
        apply intervalIntegral.integral_congr
        intro x _hx
        exact habsEven x
      _ = _ := by ring
  have hsplit : (∫ x : ℝ in 0..1, |p x|) =
      (∫ x : ℝ in 0..r, -p x) + ∫ x : ℝ in r..1, p x := by
    rw [(intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 r) (hcont.intervalIntegrable r 1)).symm]
    congr 1
    · apply intervalIntegral.integral_congr
      intro x hx
      change |p x| = -p x
      rw [abs_of_nonpos]
      have hxr : x ∈ Icc 0 r := by
        simpa only [uIcc_of_le hr0] using hx
      apply hpNonpos
      · exact hxr.1
      · exact hxr.2
    · apply intervalIntegral.integral_congr
      intro x hx
      change |p x| = p x
      rw [abs_of_nonneg]
      have hxr : x ∈ Icc r 1 := by
        simpa only [uIcc_of_le hr1] using hx
      apply hpNonneg
      · exact hxr.1
      · exact hr0.trans hxr.1
  have hleftEval : (∫ x : ℝ in 0..r, -p x) = (r - r ^ 3) / 2 := by
    rw [show (fun x : ℝ ↦ -p x) =
        fun x ↦ -(3 / 2 : ℝ) * x ^ 2 + 1 / 2 by
      funext x
      dsimp only [p, centeredEvenP2]
      ring,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 r)
        (Continuous.intervalIntegrable (by fun_prop) 0 r),
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have hrightEval : (∫ x : ℝ in r..1, p x) = (r - r ^ 3) / 2 := by
    rw [show p = fun x ↦ (3 / 2 : ℝ) * x ^ 2 - 1 / 2 by
      funext x
      dsimp only [p, centeredEvenP2]
      ring,
      intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) r 1)
        (Continuous.intervalIntegrable (by fun_prop) r 1),
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have hrCube : (Real.sqrt 3 / 3) ^ 3 = Real.sqrt 3 / 9 := by
    calc
      (Real.sqrt 3 / 3) ^ 3 =
          Real.sqrt 3 * (Real.sqrt 3 ^ 2) / 27 := by ring
      _ = Real.sqrt 3 / 9 := by rw [hsqrt]; ring
  rw [show (∫ x : ℝ in -1..1, |centeredEvenP2 x|) =
      ∫ x : ℝ in -1..1, |p x| by rfl, hfold, hsplit]
  rw [hleftEval, hrightEval]
  dsimp only [r]
  rw [hrCube]
  ring

/-- A rational upper bound convenient for fixed-mode regular-kernel estimates. -/
theorem integral_abs_centeredEvenP2_lt_four_fifths :
    (∫ x : ℝ in -1..1, |centeredEvenP2 x|) < 4 / 5 := by
  rw [integral_abs_centeredEvenP2]
  have hsqrt : Real.sqrt 3 < 9 / 5 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  nlinarith

/-- After removing its midpoint rank-one part, the endpoint regular kernel
has `L¹ × L¹` bilinear norm at most `1 / 64`. -/
theorem norm_yoshidaEndpointRegularRealBilinear_sub_midpoint_le
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    ‖yoshidaEndpointRegularRealBilinear u v -
        (15 / 64 : ℂ) *
          ((∫ x : ℝ in Icc (-1) 1, u x : ℝ) : ℂ) *
          ((∫ x : ℝ in Icc (-1) 1, v x : ℝ) : ℂ)‖ ≤
      (1 / 64 : ℝ) *
        (∫ x : ℝ in Icc (-1) 1, |u x|) *
        (∫ x : ℝ in Icc (-1) 1, |v x|) := by
  let I : Set ℝ := Icc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  let K : ℝ × ℝ → ℂ := fun p ↦
    (yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) : ℂ)
  let K₀ : ℝ × ℝ → ℂ := fun p ↦
    ((yoshidaRegularKernel ((Real.log 2 / 2) * |p.1 - p.2|) -
      (15 / 64 : ℝ) : ℝ) : ℂ)
  let G : ℝ × ℝ → ℂ := fun p ↦
    K p * (u p.2 : ℂ) * star (v p.1 : ℂ)
  let G₀ : ℝ × ℝ → ℂ := fun p ↦
    K₀ p * (u p.2 : ℂ) * star (v p.1 : ℂ)
  let C : ℝ × ℝ → ℂ := fun p ↦
    (15 / 64 : ℂ) * ((v p.1 : ℂ) * (u p.2 : ℂ))
  have hregularMeas : Measurable yoshidaRegularKernel := by
    unfold yoshidaRegularKernel
    apply Measurable.ite (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  have hK₀Meas : Measurable K₀ := by
    dsimp only [K₀]
    fun_prop
  have huInt : Integrable (fun x ↦ (u x : ℂ)) μ := by
    exact (Complex.continuous_ofReal.comp hu).continuousOn.integrableOn_compact
      isCompact_Icc
  have hvInt : Integrable (fun x ↦ (v x : ℂ)) μ := by
    exact (Complex.continuous_ofReal.comp hv).continuousOn.integrableOn_compact
      isCompact_Icc
  have hprodNorm : Integrable
      (fun p : ℝ × ℝ ↦ ‖v p.1‖ * ‖u p.2‖) (μ.prod μ) :=
    by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        hvInt.norm.mul_prod huInt.norm
  have hdomInt : Integrable
      (fun p : ℝ × ℝ ↦ (1 / 64 : ℝ) * (‖v p.1‖ * ‖u p.2‖))
      (μ.prod μ) := hprodNorm.const_mul (1 / 64 : ℝ)
  have hpMem : ∀ᵐ p ∂μ.prod μ, p ∈ I ×ˢ I := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hK₀Bound : ∀ᵐ p ∂μ.prod μ, ‖K₀ p‖ ≤ (1 / 64 : ℝ) := by
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
    have hlower := seven_div_thirty_two_le_yoshidaRegularKernel harg0 harg2
    have hupper := (yoshidaRegularKernel_mem_Icc harg0 harg2).2
    dsimp only [K₀]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hG₀Meas : AEStronglyMeasurable G₀ (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G₀]
    fun_prop
  have hG₀Int : Integrable G₀ (μ.prod μ) := by
    refine hdomInt.mono' hG₀Meas ?_
    filter_upwards [hK₀Bound] with p hp
    dsimp only [G₀]
    rw [norm_mul, norm_mul, norm_star]
    have hnonneg : 0 ≤ ‖v p.1‖ * ‖u p.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖K₀ p‖ * ‖(u p.2 : ℂ)‖ * ‖(v p.1 : ℂ)‖ =
          ‖K₀ p‖ * (‖v p.1‖ * ‖u p.2‖) := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        ring
      _ ≤ (1 / 64 : ℝ) * (‖v p.1‖ * ‖u p.2‖) :=
        mul_le_mul_of_nonneg_right hp hnonneg
  have hprodInt : Integrable
      (fun p : ℝ × ℝ ↦ (v p.1 : ℂ) * (u p.2 : ℂ)) (μ.prod μ) :=
    hvInt.mul_prod huInt
  have hCInt : Integrable C (μ.prod μ) := by
    dsimp only [C]
    exact hprodInt.const_mul (15 / 64 : ℂ)
  have huCast : (∫ x : ℝ, (u x : ℂ) ∂μ) =
      (((∫ x : ℝ, u x ∂μ : ℝ)) : ℂ) := by
    exact integral_ofReal
  have hvCast : (∫ x : ℝ, (v x : ℂ) ∂μ) =
      (((∫ x : ℝ, v x ∂μ : ℝ)) : ℂ) := by
    exact integral_ofReal
  have hCvalue : (∫ p : ℝ × ℝ, C p ∂μ.prod μ) =
      (15 / 64 : ℂ) *
        (((∫ x : ℝ, u x ∂μ : ℝ) : ℂ) *
          ((∫ x : ℝ, v x ∂μ : ℝ) : ℂ)) := by
    dsimp only [C]
    calc
      (∫ p : ℝ × ℝ,
          (15 / 64 : ℂ) * ((v p.1 : ℂ) * (u p.2 : ℂ)) ∂μ.prod μ) =
          (15 / 64 : ℂ) *
            ∫ p : ℝ × ℝ, (v p.1 : ℂ) * (u p.2 : ℂ) ∂μ.prod μ :=
        MeasureTheory.integral_const_mul _ _
      _ = (15 / 64 : ℂ) *
          ((∫ x : ℝ, (v x : ℂ) ∂μ) *
            ∫ x : ℝ, (u x : ℂ) ∂μ) := by
        exact congrArg (fun z : ℂ ↦ (15 / 64 : ℂ) * z)
          (integral_prod_mul (μ := μ) (ν := μ)
            (fun x : ℝ ↦ (v x : ℂ)) (fun x : ℝ ↦ (u x : ℂ)))
      _ = _ := by
        rw [huCast, hvCast]
        ring
  have hdecomp : ∀ p : ℝ × ℝ, G p = G₀ p + C p := by
    intro p
    dsimp only [G, G₀, C, K, K₀]
    push_cast
    rw [show star (v p.1 : ℂ) = (v p.1 : ℂ) by simp]
    ring
  have hintegralDecomp :
      yoshidaEndpointRegularRealBilinear u v -
          (15 / 64 : ℂ) *
            (((∫ x : ℝ, u x ∂μ : ℝ) : ℂ) *
              ((∫ x : ℝ, v x ∂μ : ℝ) : ℂ)) =
        ∫ p : ℝ × ℝ, G₀ p ∂μ.prod μ := by
    unfold yoshidaEndpointRegularRealBilinear
    dsimp only
    change (∫ p : ℝ × ℝ, G p ∂μ.prod μ) - _ = _
    calc
      (∫ p : ℝ × ℝ, G p ∂μ.prod μ) - _ =
          ((∫ p : ℝ × ℝ, G₀ p ∂μ.prod μ) +
            ∫ p : ℝ × ℝ, C p ∂μ.prod μ) - _ := by
        congr 2
        calc
          (∫ p : ℝ × ℝ, G p ∂μ.prod μ) =
              ∫ p : ℝ × ℝ, (G₀ p + C p) ∂μ.prod μ := by
            apply integral_congr_ae
            filter_upwards [] with p
            exact hdecomp p
          _ = _ := integral_add hG₀Int hCInt
      _ = _ := by rw [hCvalue]; ring
  have hquad :
      ‖∫ p : ℝ × ℝ, G₀ p ∂μ.prod μ‖ ≤
        (1 / 64 : ℝ) *
          (∫ x : ℝ, ‖u x‖ ∂μ) * (∫ x : ℝ, ‖v x‖ ∂μ) := by
    calc
      ‖∫ p : ℝ × ℝ, G₀ p ∂μ.prod μ‖ ≤
          ∫ p : ℝ × ℝ, ‖G₀ p‖ ∂μ.prod μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ p : ℝ × ℝ,
          (1 / 64 : ℝ) * (‖v p.1‖ * ‖u p.2‖) ∂μ.prod μ := by
        apply integral_mono_ae hG₀Int.norm hdomInt
        filter_upwards [hK₀Bound] with p hp
        dsimp only [G₀]
        rw [norm_mul, norm_mul, norm_star]
        have hnonneg : 0 ≤ ‖v p.1‖ * ‖u p.2‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        calc
          ‖K₀ p‖ * ‖(u p.2 : ℂ)‖ * ‖(v p.1 : ℂ)‖ =
              ‖K₀ p‖ * (‖v p.1‖ * ‖u p.2‖) := by
            simp only [Complex.norm_real, Real.norm_eq_abs]
            ring
          _ ≤ (1 / 64 : ℝ) * (‖v p.1‖ * ‖u p.2‖) :=
            mul_le_mul_of_nonneg_right hp hnonneg
      _ = (1 / 64 : ℝ) *
          (∫ x : ℝ, ‖u x‖ ∂μ) * (∫ x : ℝ, ‖v x‖ ∂μ) := by
        rw [MeasureTheory.integral_const_mul,
          integral_prod_mul (fun x : ℝ ↦ ‖v x‖) (fun x : ℝ ↦ ‖u x‖)]
        ring
  simpa only [μ, I, Complex.norm_real, Real.norm_eq_abs, mul_assoc] using
    (show ‖yoshidaEndpointRegularRealBilinear u v -
        (15 / 64 : ℂ) *
          (((∫ x : ℝ, u x ∂μ : ℝ) : ℂ) *
            ((∫ x : ℝ, v x ∂μ : ℝ) : ℂ))‖ ≤
          (1 / 64 : ℝ) *
            (∫ x : ℝ, ‖u x‖ ∂μ) * (∫ x : ℝ, ‖v x‖ ∂μ) by
      rw [hintegralDecomp]
      exact hquad)

/-- General centered-kernel `L²` bound for continuous real profiles.  The
midpoint rank-one term is retained rather than cancelled. -/
theorem norm_yoshidaEndpointRegularQuadratic_ofReal_sub_midpoint_le
    (f : ℝ → ℝ) (hf : Continuous f) :
    ‖yoshidaEndpointRegularQuadratic (fun x ↦ (f x : ℂ)) -
        (15 / 64 : ℂ) *
          (((∫ x : ℝ in Icc (-1) 1, f x) ^ 2 : ℝ) : ℂ)‖ ≤
      (1 / 32 : ℝ) * ∫ x : ℝ in Icc (-1) 1, |f x| ^ 2 := by
  let I : Set ℝ := Icc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  have hbilinear :=
    norm_yoshidaEndpointRegularRealBilinear_sub_midpoint_le f f hf hf
  have heq : yoshidaEndpointRegularQuadratic (fun x ↦ (f x : ℂ)) =
      yoshidaEndpointRegularRealBilinear f f := by
    unfold yoshidaEndpointRegularQuadratic
    unfold yoshidaEndpointRegularRealBilinear
    unfold yoshidaEndpointA
    rfl
  have hcentered :
      ‖yoshidaEndpointRegularQuadratic (fun x ↦ (f x : ℂ)) -
          (15 / 64 : ℂ) *
            (((∫ x : ℝ in Icc (-1) 1, f x) ^ 2 : ℝ) : ℂ)‖ ≤
        (1 / 64 : ℝ) *
          (∫ x : ℝ in Icc (-1) 1, |f x|) ^ 2 := by
    rw [heq]
    simpa only [Complex.ofReal_pow, Complex.ofReal_mul, pow_two, mul_assoc] using
      hbilinear
  have hfMeas : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    exact (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hconst : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 μ := memLp_const 1
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (by simpa using hconst) (by simpa using hfLp)
  simp at hholder
  have hlen : μ.real Set.univ = 2 := by
    norm_num [μ, I]
  rw [hlen] at hholder
  have hholder' :
      (∫ x : ℝ, ‖f x‖ ∂μ) ≤
        (2 : ℝ) ^ ((2 : ℝ)⁻¹) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hholder
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
      (sq_le_sq₀ hL10 hrhs0).2 hholder'
    calc
      (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 ≤ _ := hsqle
      _ = 2 * ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ := by
        rw [mul_pow]
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hE0]
        norm_num
  have hL1sqSet :
      (∫ x : ℝ in Icc (-1) 1, |f x|) ^ 2 ≤
        2 * ∫ x : ℝ in Icc (-1) 1, |f x| ^ 2 := by
    simpa only [μ, I, Real.norm_eq_abs] using hL1sq
  have hscaled := mul_le_mul_of_nonneg_left hL1sqSet
    (by norm_num : (0 : ℝ) ≤ 1 / 64)
  calc
    _ ≤ (1 / 64 : ℝ) *
        (∫ x : ℝ in Icc (-1) 1, |f x|) ^ 2 := hcentered
    _ ≤ (1 / 32 : ℝ) *
        ∫ x : ℝ in Icc (-1) 1, |f x| ^ 2 := by
      linarith

/-- On the `{1,P₂}` block the midpoint part and its centered remainder
combine without any cross loss. -/
theorem yoshidaEndpointRegularQuadratic_one_add_p2_re_le (c b : ℝ) :
    (yoshidaEndpointRegularQuadratic
      (fun x ↦ ((c + b * centeredEvenP2 x : ℝ) : ℂ))).re ≤
        c ^ 2 + b ^ 2 / 80 := by
  let p : ℝ → ℝ := centeredEvenP2
  let f : ℝ → ℝ := fun x ↦ c + b * p x
  have hpcont : Continuous p := by
    unfold p centeredEvenP2
    fun_prop
  have hfcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hpmeanInterval : (∫ x : ℝ in -1..1, p x) = 0 := by
    simpa only [p, centeredEvenP0, one_mul] using integral_centeredEvenP0_mul_p2
  have hmean : (∫ x : ℝ in Icc (-1) 1, f x) = 2 * c := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [show f = fun x ↦ c + b * p x by rfl,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable continuous_const (-1) 1)
        ((hpcont.const_mul b).intervalIntegrable (-1) 1),
      intervalIntegral.integral_const_mul, hpmeanInterval]
    norm_num
  have hmass : (∫ x : ℝ in Icc (-1) 1, |f x| ^ 2) =
      2 * c ^ 2 + (2 / 5 : ℝ) * b ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [show (fun x : ℝ ↦ |f x| ^ 2) =
        fun x ↦ c ^ 2 + ((2 * c * b) * p x + b ^ 2 * p x ^ 2) by
      funext x
      rw [sq_abs]
      dsimp only [f]
      ring]
    have hconst : IntervalIntegrable (fun _ : ℝ ↦ c ^ 2) volume (-1) 1 :=
      continuous_const.intervalIntegrable (-1) 1
    have hcross : IntervalIntegrable (fun x ↦ (2 * c * b) * p x)
        volume (-1) 1 := (hpcont.const_mul (2 * c * b)).intervalIntegrable (-1) 1
    have hdiag : IntervalIntegrable (fun x ↦ b ^ 2 * p x ^ 2)
        volume (-1) 1 := ((hpcont.pow 2).const_mul (b ^ 2)).intervalIntegrable (-1) 1
    calc
      (∫ x : ℝ in -1..1,
          c ^ 2 + ((2 * c * b) * p x + b ^ 2 * p x ^ 2)) =
          (∫ _x : ℝ in -1..1, c ^ 2) +
            ∫ x : ℝ in -1..1,
              ((2 * c * b) * p x + b ^ 2 * p x ^ 2) :=
        intervalIntegral.integral_add hconst (hcross.add hdiag)
      _ = (∫ _x : ℝ in -1..1, c ^ 2) +
          ((∫ x : ℝ in -1..1, (2 * c * b) * p x) +
            ∫ x : ℝ in -1..1, b ^ 2 * p x ^ 2) := by
        rw [intervalIntegral.integral_add hcross hdiag]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, hpmeanInterval,
          show (∫ x : ℝ in -1..1, p x ^ 2) = 2 / 5 by
            simpa only [p] using integral_centeredEvenP2_sq]
        norm_num
        ring
  have hcenter :=
    norm_yoshidaEndpointRegularQuadratic_ofReal_sub_midpoint_le f hfcont
  rw [hmean, hmass] at hcenter
  let R : ℂ := yoshidaEndpointRegularQuadratic (fun x ↦ (f x : ℂ))
  have hre := Complex.re_le_norm
    (R - (15 / 64 : ℂ) * ((((2 * c) ^ 2 : ℝ)) : ℂ))
  have hrewrite :
      (R - (15 / 64 : ℂ) * ((((2 * c) ^ 2 : ℝ)) : ℂ)).re =
        R.re - (15 / 16 : ℝ) * c ^ 2 := by
    have hcast : (((((2 * c) ^ 2 : ℝ)) : ℂ)) =
        ((4 * c ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast]
    simp only [sub_re, mul_re, ofReal_re, ofReal_im]
    norm_num
    ring
  rw [hrewrite] at hre
  have htotal := hre.trans hcenter
  dsimp only [R, f, p] at htotal ⊢
  nlinarith

/-- The symmetric regular-kernel cross between `1` and `P₂` is much
smaller than the uniform Schur estimate. -/
theorem abs_yoshidaEndpointRegularConstantCross_centeredEvenP2_lt :
    |yoshidaEndpointRegularConstantCross centeredEvenP2| < 1 / 20 := by
  let p : ℝ → ℝ := centeredEvenP2
  have hpcont : Continuous p := by
    unfold p centeredEvenP2
    fun_prop
  have hpmean : (∫ x : ℝ in Icc (-1) 1, p x) = 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    simpa only [p, centeredEvenP0, one_mul] using integral_centeredEvenP0_mul_p2
  let A : ℝ := ∫ x : ℝ in Icc (-1) 1, |p x|
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hAlt : A < 4 / 5 := by
    dsimp only [A]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    simpa only [p] using integral_abs_centeredEvenP2_lt_four_fifths
  have hone : (∫ _x : ℝ in Icc (-1) 1, |(1 : ℝ)|) = 2 := by
    norm_num
  have hleft :=
    norm_yoshidaEndpointRegularRealBilinear_sub_midpoint_le
      (fun _ : ℝ ↦ 1) p continuous_const hpcont
  rw [hpmean, hone] at hleft
  norm_num only [Complex.ofReal_zero, mul_zero, sub_zero] at hleft
  have hleftLt :
      ‖yoshidaEndpointRegularRealBilinear (fun _ : ℝ ↦ 1) p‖ < 1 / 40 := by
    apply lt_of_le_of_lt hleft
    dsimp only [A] at hA0 hAlt ⊢
    nlinarith
  have hright :=
    norm_yoshidaEndpointRegularRealBilinear_sub_midpoint_le
      p (fun _ : ℝ ↦ 1) hpcont continuous_const
  rw [hpmean, hone] at hright
  norm_num only [Complex.ofReal_zero, zero_mul, sub_zero] at hright
  have hrightLt :
      ‖yoshidaEndpointRegularRealBilinear p (fun _ : ℝ ↦ 1)‖ < 1 / 40 := by
    apply lt_of_le_of_lt hright
    dsimp only [A] at hA0 hAlt ⊢
    nlinarith
  have hsum :
      |(yoshidaEndpointRegularRealBilinear (fun _ : ℝ ↦ 1) p +
          yoshidaEndpointRegularRealBilinear p (fun _ : ℝ ↦ 1)).re| <
        1 / 20 := by
    calc
      |(yoshidaEndpointRegularRealBilinear (fun _ : ℝ ↦ 1) p +
          yoshidaEndpointRegularRealBilinear p (fun _ : ℝ ↦ 1)).re| ≤
          ‖yoshidaEndpointRegularRealBilinear (fun _ : ℝ ↦ 1) p +
          yoshidaEndpointRegularRealBilinear p (fun _ : ℝ ↦ 1)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖yoshidaEndpointRegularRealBilinear (fun _ : ℝ ↦ 1) p‖ +
          ‖yoshidaEndpointRegularRealBilinear p (fun _ : ℝ ↦ 1)‖ :=
        norm_add_le _ _
      _ < _ := by linarith
  unfold yoshidaEndpointRegularConstantCross
  simpa only [p] using hsum

/-- The fixed `P₂` diagonal improves the sharp mean-zero Schur value
`1 / 80` to a strict `1 / 100`. -/
theorem norm_yoshidaEndpointRegularQuadratic_centeredEvenP2_lt :
    ‖yoshidaEndpointRegularQuadratic
        (fun x ↦ (centeredEvenP2 x : ℂ))‖ < 1 / 100 := by
  let p : ℝ → ℝ := centeredEvenP2
  have hpcont : Continuous p := by
    unfold p centeredEvenP2
    fun_prop
  have hpmean : (∫ x : ℝ in Icc (-1) 1, p x) = 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    simpa only [p, centeredEvenP0, one_mul] using integral_centeredEvenP0_mul_p2
  let A : ℝ := ∫ x : ℝ in Icc (-1) 1, |p x|
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hAlt : A < 4 / 5 := by
    dsimp only [A]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    simpa only [p] using integral_abs_centeredEvenP2_lt_four_fifths
  have hbilinear :=
    norm_yoshidaEndpointRegularRealBilinear_sub_midpoint_le
      p p hpcont hpcont
  rw [hpmean] at hbilinear
  norm_num only [Complex.ofReal_zero, mul_zero, sub_zero] at hbilinear
  have hsmall : (1 / 64 : ℝ) * A * A < 1 / 100 := by
    nlinarith
  have hfixed : ‖yoshidaEndpointRegularRealBilinear p p‖ < 1 / 100 := by
    apply lt_of_le_of_lt hbilinear
    simpa only [A] using hsmall
  have heq : yoshidaEndpointRegularQuadratic
      (fun x ↦ (centeredEvenP2 x : ℂ)) =
        yoshidaEndpointRegularRealBilinear p p := by
    unfold yoshidaEndpointRegularQuadratic
    unfold yoshidaEndpointRegularRealBilinear
    unfold yoshidaEndpointA
    rfl
  rw [heq]
  exact hfixed

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenLowRegular
