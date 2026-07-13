import ArithmeticHodge.Analysis.CenteredEndpointCorrelation
import ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound
import ArithmeticHodge.Analysis.YoshidaRegularKernelSchur
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointRegularCorrelation

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

noncomputable section

private def centeredZeroExtension (w : ℝ → ℝ) : ℝ → ℝ :=
  Set.indicator (Icc (-1) 1) w

private theorem centeredZeroExtension_integrable
    (w : ℝ → ℝ) (hw : Continuous w) :
    Integrable (centeredZeroExtension w) := by
  exact (hw.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
    measurableSet_Icc

private def centeredFullCorrelation (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, centeredZeroExtension w (t + x) * centeredZeroExtension w x

private theorem centeredFullCorrelation_eq_centeredEndpointCorrelation
    (w : ℝ → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    centeredFullCorrelation w t = centeredEndpointCorrelation w t := by
  let J : Set ℝ := Icc (-1) (1 - t)
  have hJmeas : MeasurableSet J := measurableSet_Icc
  rw [centeredFullCorrelation, centeredEndpointCorrelation,
    intervalIntegral.integral_of_le (by linarith)]
  rw [← integral_Icc_eq_integral_Ioc]
  rw [← integral_indicator hJmeas]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ J
  · have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    have htxI : t + x ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    simp only [J, Set.indicator_of_mem hx, centeredZeroExtension,
      Set.indicator_of_mem hxI, Set.indicator_of_mem htxI]
  · rw [Set.indicator_of_notMem hx]
    by_cases hxI : x ∈ Icc (-1 : ℝ) 1
    · have htxI : t + x ∉ Icc (-1 : ℝ) 1 := by
        intro hmem
        apply hx
        exact ⟨hxI.1, by linarith [hmem.2]⟩
      simp only [centeredZeroExtension, Set.indicator_of_mem hxI,
        Set.indicator_of_notMem htxI, zero_mul]
    · simp only [centeredZeroExtension, Set.indicator_of_notMem hxI,
        mul_zero]

private theorem centeredFullCorrelation_even (w : ℝ → ℝ) :
    Function.Even (centeredFullCorrelation w) := by
  intro t
  unfold centeredFullCorrelation
  calc
    (∫ x : ℝ,
        centeredZeroExtension w (-t + x) * centeredZeroExtension w x) =
        ∫ x : ℝ,
          centeredZeroExtension w ((x + t) - t) *
            centeredZeroExtension w (x + t) := by
      symm
      simpa only [add_comm] using
        (integral_add_right_eq_self
          (fun x : ℝ ↦ centeredZeroExtension w (x - t) *
            centeredZeroExtension w x) t)
    _ = ∫ x : ℝ,
        centeredZeroExtension w (t + x) * centeredZeroExtension w x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring_nf

private theorem centeredFullCorrelation_eq_zero_of_two_lt
    (w : ℝ → ℝ) {t : ℝ} (ht : 2 < t) :
    centeredFullCorrelation w t = 0 := by
  unfold centeredFullCorrelation
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have htx : t + x ∉ Icc (-1 : ℝ) 1 := by
      intro hmem
      linarith [hx.1, hmem.2]
    simp only [centeredZeroExtension, Set.indicator_of_notMem htx, zero_mul,
      Pi.zero_apply]
  · simp only [centeredZeroExtension, Set.indicator_of_notMem hx, mul_zero,
      Pi.zero_apply]

theorem re_yoshidaEndpointRegularQuadratic_eq_correlation
    (w : ℝ → ℝ) (hw : Continuous w) :
    (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re =
      2 * ∫ t : ℝ in 0..2,
        yoshidaRegularKernel (yoshidaEndpointA * t) *
          centeredEndpointCorrelation w t := by
  let I : Set ℝ := Icc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  let W : ℝ → ℝ := centeredZeroExtension w
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (yoshidaEndpointA * |t|)
  let G : ℝ × ℝ → ℝ := fun p ↦ K (p.1 - p.2) * W p.2 * W p.1
  let J : ℝ × ℝ → ℝ := fun p ↦ K p.1 * W (p.2 - p.1) * W p.2
  let F : ℝ → ℝ := fun t ↦ K t * centeredFullCorrelation w t
  have hWInt : Integrable W := by
    simpa only [W] using centeredZeroExtension_integrable w hw
  have hWMeas : Measurable W := by
    dsimp only [W, centeredZeroExtension]
    exact hw.measurable.indicator measurableSet_Icc
  have hregularMeas : Measurable yoshidaRegularKernel := by
    unfold yoshidaRegularKernel
    apply Measurable.ite (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  have hKMeas : Measurable K := by
    dsimp only [K]
    fun_prop
  have hKBound (t : ℝ) (ht : |t| ≤ 2) :
      0 ≤ K t ∧ K t ≤ 1 / 4 := by
    have harg0 : 0 ≤ yoshidaEndpointA * |t| :=
      mul_nonneg yoshidaEndpointA_pos.le (abs_nonneg _)
    have harg2 : yoshidaEndpointA * |t| ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left ht
        (by positivity : 0 ≤ Real.log 2 / 2)]
    simpa only [K] using yoshidaRegularKernel_mem_Icc harg0 harg2
  have hprod : Integrable (fun p : ℝ × ℝ ↦ W p.2 * W p.1) := by
    simpa only [mul_comm] using hWInt.mul_prod hWInt
  have hGMeas : AEStronglyMeasurable G := by
    apply Measurable.aestronglyMeasurable
    dsimp only [G]
    fun_prop
  have hG : Integrable G := by
    have hdom : Integrable
        (fun p : ℝ × ℝ ↦ (1 / 4 : ℝ) * ‖W p.2 * W p.1‖) :=
      hprod.norm.const_mul (1 / 4 : ℝ)
    refine hdom.mono' hGMeas ?_
    filter_upwards [] with p
    by_cases hp1 : W p.1 = 0
    · simp [G, hp1]
    by_cases hp2 : W p.2 = 0
    · simp [G, hp2]
    have hp1I : p.1 ∈ I := by
      by_contra hp
      apply hp1
      simp [W, I, centeredZeroExtension, Set.indicator_of_notMem hp]
    have hp2I : p.2 ∈ I := by
      by_contra hp
      apply hp2
      simp [W, I, centeredZeroExtension, Set.indicator_of_notMem hp]
    have hdiff : |p.1 - p.2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hp1I.1, hp1I.2, hp2I.1, hp2I.2]
    have hk := hKBound (p.1 - p.2) hdiff
    dsimp only [G]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hk.1,
      Real.norm_eq_abs]
    calc
      K (p.1 - p.2) * |W p.2| * |W p.1| =
          K (p.1 - p.2) * (|W p.2| * |W p.1|) := by ring
      _ ≤ (1 / 4 : ℝ) * (|W p.2| * |W p.1|) :=
        mul_le_mul_of_nonneg_right hk.2 (by positivity)
      _ = (1 / 4 : ℝ) * |W p.2 * W p.1| := by rw [abs_mul]
  let Wneg : ℝ → ℝ := fun x ↦ W (-x)
  have hWnegInt : Integrable Wneg := by
    simpa only [Wneg] using hWInt.comp_neg
  have hbaseJ : Integrable (fun p : ℝ × ℝ ↦ W (p.2 - p.1) * W p.2) := by
    have hconv := hWInt.convolution_integrand
      (ContinuousLinearMap.mul ℝ ℝ) hWnegInt
    simpa only [Wneg, neg_sub, mul_comm] using hconv
  have hJMeas : AEStronglyMeasurable J := by
    apply Measurable.aestronglyMeasurable
    dsimp only [J]
    fun_prop
  have hJ : Integrable J := by
    have hdom : Integrable
        (fun p : ℝ × ℝ ↦ (1 / 4 : ℝ) * ‖W (p.2 - p.1) * W p.2‖) :=
      hbaseJ.norm.const_mul (1 / 4 : ℝ)
    refine hdom.mono' hJMeas ?_
    filter_upwards [] with p
    by_cases hpx : W p.2 = 0
    · simp [J, hpx]
    by_cases hpy : W (p.2 - p.1) = 0
    · simp [J, hpy]
    have hpxI : p.2 ∈ I := by
      by_contra hp
      apply hpx
      simp [W, I, centeredZeroExtension, Set.indicator_of_notMem hp]
    have hpyI : p.2 - p.1 ∈ I := by
      by_contra hp
      apply hpy
      simp [W, I, centeredZeroExtension, Set.indicator_of_notMem hp]
    have ht : |p.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hpxI.1, hpxI.2, hpyI.1, hpyI.2]
    have hk := hKBound p.1 ht
    dsimp only [J]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hk.1,
      Real.norm_eq_abs]
    calc
      K p.1 * |W (p.2 - p.1)| * |W p.2| =
          K p.1 * (|W (p.2 - p.1)| * |W p.2|) := by ring
      _ ≤ (1 / 4 : ℝ) * (|W (p.2 - p.1)| * |W p.2|) :=
        mul_le_mul_of_nonneg_right hk.2 (by positivity)
      _ = (1 / 4 : ℝ) * |W (p.2 - p.1) * W p.2| := by rw [abs_mul]
  have hfullSquare : (∫ p : ℝ × ℝ, G p) = ∫ p : ℝ × ℝ, J p := by
    change (∫ p : ℝ × ℝ, G p ∂(volume : Measure ℝ).prod volume) =
      ∫ p : ℝ × ℝ, J p ∂(volume : Measure ℝ).prod volume
    rw [integral_prod G hG, integral_prod J hJ]
    calc
      (∫ x : ℝ, ∫ y : ℝ, G (x, y)) =
          ∫ x : ℝ, ∫ t : ℝ, J (t, x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        calc
          (∫ y : ℝ, G (x, y)) =
              ∫ t : ℝ, G (x, x - t) := by
            symm
            exact integral_sub_left_eq_self (fun y : ℝ ↦ G (x, y)) volume x
          _ = ∫ t : ℝ, J (t, x) := by
            apply integral_congr_ae
            filter_upwards [] with t
            dsimp only [G, J]
            congr 2
            · congr 2
              rw [show x - (x - t) = t by ring]
      _ = ∫ t : ℝ, ∫ x : ℝ, J (t, x) :=
        (integral_integral_swap hJ).symm
  have hJinner (t : ℝ) :
      (∫ x : ℝ, J (t, x)) = F t := by
    calc
      (∫ x : ℝ, J (t, x)) =
          K t * ∫ x : ℝ, W (x - t) * W x := by
        rw [show (fun x : ℝ ↦ J (t, x)) =
            fun x ↦ K t * (W (x - t) * W x) by
          funext x
          dsimp only [J]
          ring]
        rw [integral_const_mul]
      _ = K t * centeredFullCorrelation w t := by
        apply congrArg (fun z : ℝ ↦ K t * z)
        calc
          (∫ x : ℝ, W (x - t) * W x) =
              ∫ x : ℝ, W ((x + t) - t) * W (x + t) := by
            symm
            exact integral_add_right_eq_self
              (fun x : ℝ ↦ W (x - t) * W x) t
          _ = ∫ x : ℝ, W (t + x) * W x := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring_nf
      _ = F t := rfl
  have hFInt : Integrable F := by
    apply hJ.integral_prod_left.congr
    filter_upwards [] with t
    exact hJinner t
  have hrestrictedRe :
      (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re =
        ∫ p : ℝ × ℝ, G p := by
    let H : ℝ × ℝ → ℂ := fun p ↦
      (yoshidaRegularKernel (yoshidaEndpointA * |p.1 - p.2|) : ℂ) *
        (w p.2 : ℂ) * star (w p.1 : ℂ)
    have hH : Integrable H (μ.prod μ) := by
      dsimp only [μ]
      rw [Measure.prod_restrict]
      have hGI : Integrable G ((volume.prod volume).restrict (I ×ˢ I)) :=
        hG.integrableOn
      have hGc := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integrable_comp hGI
      apply hGc.congr
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      dsimp only [I] at hp
      simp [H, G, K, W, centeredZeroExtension, yoshidaEndpointA,
        hp.1, hp.2]
    unfold yoshidaEndpointRegularQuadratic
    change (∫ p : ℝ × ℝ, H p ∂μ.prod μ).re = _
    have hwithin :
        (∫ p : ℝ × ℝ, (H p).re ∂μ.prod μ) =
          ∫ p : ℝ × ℝ in I ×ˢ I, G p := by
      dsimp only [μ]
      rw [Measure.prod_restrict]
      apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      intro p hp
      dsimp only [H, G, K, W, centeredZeroExtension, I]
      simp only [Set.indicator_of_mem hp.1, Set.indicator_of_mem hp.2]
      unfold yoshidaEndpointA
      norm_num
    calc
      (∫ p : ℝ × ℝ, H p ∂μ.prod μ).re =
          ∫ p : ℝ × ℝ, (H p).re ∂μ.prod μ :=
        (integral_re hH).symm
      _ = ∫ p : ℝ × ℝ in I ×ˢ I, G p := hwithin
      _ = ∫ p : ℝ × ℝ, G p :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ by
          by_cases hp1 : p.1 ∈ I
          · have hp2 : p.2 ∉ I := by
              intro hmem
              exact hp ⟨hp1, hmem⟩
            dsimp only [I] at hp2
            dsimp only [G, W, centeredZeroExtension, I]
            rw [Set.indicator_of_notMem hp2]
            ring
          · dsimp only [I] at hp1
            dsimp only [G, W, centeredZeroExtension, I]
            rw [Set.indicator_of_notMem hp1]
            ring)
  have hFEven : Function.Even F := by
    intro t
    dsimp only [F, K]
    rw [abs_neg, centeredFullCorrelation_even]
  have hleft : (∫ t : ℝ in Iic 0, F t) = ∫ t : ℝ in Ioi 0, F t := by
    calc
      (∫ t : ℝ in Iic 0, F t) = ∫ t : ℝ in Iic 0, F (-t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t _ht
        exact (hFEven t).symm
      _ = ∫ t : ℝ in Ioi 0, F t := by
        simpa only [neg_zero] using integral_comp_neg_Iic 0 F
  have hwhole : (∫ t : ℝ, F t) = 2 * ∫ t : ℝ in Ioi 0, F t := by
    rw [← intervalIntegral.integral_Iic_add_Ioi
        hFInt.integrableOn hFInt.integrableOn, hleft]
    ring
  have hpositive : (∫ t : ℝ in Ioi 0, F t) = ∫ t : ℝ in 0..2, F t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self
    intro t ht
    have ht2 : 2 < t := by
      rcases ht with ⟨ht0, htNot⟩
      simp only [mem_Ioi] at ht0
      simp only [mem_Ioc, not_and, not_le] at htNot
      exact htNot ht0
    dsimp only [F]
    rw [centeredFullCorrelation_eq_zero_of_two_lt w ht2, mul_zero]
  calc
    (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re =
        ∫ p : ℝ × ℝ, G p := hrestrictedRe
    _ = ∫ p : ℝ × ℝ, J p := hfullSquare
    _ = ∫ t : ℝ, F t := by
      change (∫ p : ℝ × ℝ, J p ∂(volume : Measure ℝ).prod volume) = _
      rw [integral_prod J hJ]
      apply integral_congr_ae
      filter_upwards [] with t
      exact hJinner t
    _ = 2 * ∫ t : ℝ in 0..2, F t := by rw [hwhole, hpositive]
    _ = 2 * ∫ t : ℝ in 0..2,
        yoshidaRegularKernel (yoshidaEndpointA * t) *
          centeredEndpointCorrelation w t := by
      apply congrArg (fun z : ℝ ↦ 2 * z)
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 2 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      dsimp only [F, K]
      rw [abs_of_nonneg ht'.1,
        centeredFullCorrelation_eq_centeredEndpointCorrelation w ht'.1 ht'.2]

end


end ArithmeticHodge.Analysis.YoshidaEndpointRegularCorrelation
