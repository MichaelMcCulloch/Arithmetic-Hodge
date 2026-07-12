import ArithmeticHodge.Analysis.YoshidaCauchyPairing
import ArithmeticHodge.Analysis.YoshidaDigammaDistribution
import ArithmeticHodge.Analysis.YoshidaOddFourierDecay
import ArithmeticHodge.Analysis.YoshidaClippedMomentBridge

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped FourierTransform

namespace ArithmeticHodge.Analysis.YoshidaOddSpectralBridge

noncomputable section

open MultiplicativeWeil
open YoshidaCauchyPairing
open YoshidaClippedMomentBridge
open YoshidaDigammaDistribution
open YoshidaOddFourierDecay
open YoshidaOddGramPrefix
open YoshidaOddModeRegularity

/-- The zero-extended normalized sine mode at Yoshida's ratio-two length. -/
def oddModeFunction (n : ℕ) : ℝ → ℂ :=
  (yoshidaClippedOddMode yoshidaHalfLength n : ℝ → ℂ)

/-- Angular Fourier product entering the odd local critical pairing. -/
def oddAngularSpectralProduct (n m : ℕ) (v : ℝ) : ℂ :=
  star (angularFourier (oddModeFunction n) v) *
    angularFourier (oddModeFunction m) v

theorem angularFourier_oddModeFunction_eq_criticalSample
    (n : ℕ) (v : ℝ) :
    angularFourier (oddModeFunction n) v =
      yoshidaCriticalSampleLinear yoshidaHalfLength yoshidaHalfLength_pos v
        (yoshidaClippedOddMode yoshidaHalfLength n) := by
  exact (yoshidaCriticalSample_eq_fourier
    yoshidaHalfLength_pos v (yoshidaClippedOddMode yoshidaHalfLength n)).symm

private theorem continuous_oddAngularSpectralProduct (n m : ℕ) :
    Continuous (oddAngularSpectralProduct n m) := by
  unfold oddAngularSpectralProduct angularFourier oddModeFunction
  exact ((continuous_fourier_yoshidaClippedOddMode
    yoshidaHalfLength_pos n).comp (by fun_prop)).star.mul
      ((continuous_fourier_yoshidaClippedOddMode
        yoshidaHalfLength_pos m).comp (by fun_prop))

theorem oddAngularSpectralProduct_weighted_integrable (n m : ℕ) :
    Integrable (fun v : ℝ ↦
      (1 + v ^ 2) * ‖oddAngularSpectralProduct n m v‖) := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := by positivity
  have hcSq : 1 ≤ c ^ 2 := by
    dsimp [c]
    nlinarith [Real.pi_gt_three]
  let B : ℝ → ℝ := fun w ↦ (1 + w ^ 2) *
    ‖FourierTransform.fourier
        (yoshidaClippedOddMode yoshidaHalfLength n : ℝ → ℂ) w *
      FourierTransform.fourier
        (yoshidaClippedOddMode yoshidaHalfLength m : ℝ → ℂ) w‖
  have hB : Integrable B := by
    simpa only [B] using
      integrable_one_add_sq_mul_norm_fourierProduct_all
        yoshidaHalfLength_pos n m
  have hscaled : Integrable (fun v : ℝ ↦ c ^ 2 * B (v / c)) :=
    (hB.comp_div hc).const_mul (c ^ 2)
  apply hscaled.mono'
  · exact ((continuous_const.add (continuous_id.pow 2)).mul
      (continuous_oddAngularSpectralProduct n m).norm).aestronglyMeasurable
  · filter_upwards [] with v
    have hweight : 1 + v ^ 2 ≤ c ^ 2 * (1 + (v / c) ^ 2) := by
      field_simp [hc]
      nlinarith
    have hnorm :
        ‖oddAngularSpectralProduct n m v‖ =
          ‖FourierTransform.fourier
              (yoshidaClippedOddMode yoshidaHalfLength n : ℝ → ℂ) (v / c) *
            FourierTransform.fourier
              (yoshidaClippedOddMode yoshidaHalfLength m : ℝ → ℂ) (v / c)‖ := by
      simp [oddAngularSpectralProduct, angularFourier, oddModeFunction, c]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    rw [hnorm]
    dsimp only [B]
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right hweight
        (norm_nonneg
        (FourierTransform.fourier
            (yoshidaClippedOddMode yoshidaHalfLength n : ℝ → ℂ) (v / c) *
          FourierTransform.fourier
            (yoshidaClippedOddMode yoshidaHalfLength m : ℝ → ℂ) (v / c))))

theorem oddAngularSpectralProduct_integrable (n m : ℕ) :
    Integrable (oddAngularSpectralProduct n m) := by
  have hW := oddAngularSpectralProduct_weighted_integrable n m
  apply hW.mono'
  · exact (continuous_oddAngularSpectralProduct n m).aestronglyMeasurable
  · filter_upwards [] with v
    calc
      ‖oddAngularSpectralProduct n m v‖ ≤
          (1 + v ^ 2) * ‖oddAngularSpectralProduct n m v‖ := by
        exact le_mul_of_one_le_left (norm_nonneg _)
          (by nlinarith [sq_nonneg v])

theorem oddFourierProduct_integrable (n m : ℕ) :
    Integrable (fun w : ℝ ↦
      star (FourierTransform.fourier (oddModeFunction n) w) *
        FourierTransform.fourier (oddModeFunction m) w) := by
  have hW := integrable_one_add_sq_mul_norm_fourierProduct_all
    yoshidaHalfLength_pos n m
  apply hW.mono'
  · exact ((continuous_fourier_yoshidaClippedOddMode
      yoshidaHalfLength_pos n).star.mul
        (continuous_fourier_yoshidaClippedOddMode
          yoshidaHalfLength_pos m)).aestronglyMeasurable
  · filter_upwards [] with w
    simp only [oddModeFunction, norm_mul, norm_star]
    have hnonneg : 0 ≤
        ‖FourierTransform.fourier
            (yoshidaClippedOddMode yoshidaHalfLength n : ℝ → ℂ) w‖ *
          ‖FourierTransform.fourier
            (yoshidaClippedOddMode yoshidaHalfLength m : ℝ → ℂ) w‖ := by positivity
    exact le_mul_of_one_le_left hnonneg (by nlinarith [sq_nonneg w])

/-- Exponentially weighted cross-correlation for the `k`-th Bombieri
Cauchy kernel. -/
def oddCauchyCorrelationValue (n m k : ℕ) : ℂ :=
  ∫ u : ℝ,
    (Real.exp (-(2 * (k : ℝ) + 1 / 2) * |u|) : ℝ) *
      crossCorrelation (oddModeFunction n) (oddModeFunction m) u

theorem normalized_bombieriDigammaKernel_oddSpectralProduct
    (n m k : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
        oddAngularSpectralProduct n m v) =
      oddCauchyCorrelationValue n m k := by
  let b : ℝ := 2 * (k : ℝ) + 1 / 2
  have hb : 0 < b := by positivity
  have h := angular_cauchy_crossCorrelation_pairing
    (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos n)
    (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos m)
    (continuous_yoshidaClippedOddMode yoshidaHalfLength_pos n)
    (continuous_yoshidaClippedOddMode yoshidaHalfLength_pos m)
    (hasCompactSupport_yoshidaClippedOddMode m)
    (oddFourierProduct_integrable n m) b hb
  have hkernel (v : ℝ) :
      (bombieriDigammaKernel k v : ℂ) =
        (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) := by
    unfold bombieriDigammaKernel
    dsimp [b]
    push_cast
    ring
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) *
        oddAngularSpectralProduct n m v) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            (2 * b : ℂ) / ((b : ℂ) ^ 2 + (v : ℂ) ^ 2) *
              oddAngularSpectralProduct n m v) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      rw [hkernel]
    _ = oddCauchyCorrelationValue n m k := by
      simpa only [oddAngularSpectralProduct, oddModeFunction,
        oddCauchyCorrelationValue, b] using h

private theorem starReflection_oddMode_integrable (n : ℕ) :
    Integrable (starReflection (oddModeFunction n)) := by
  have hneg : Integrable (fun x : ℝ ↦ oddModeFunction n (-x)) :=
    (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos n).comp_neg
  simpa only [starReflection, RCLike.star_def] using
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg

private theorem oddCrossCorrelation_integrable (n m : ℕ) :
    Integrable (crossCorrelation (oddModeFunction n) (oddModeFunction m)) := by
  exact (starReflection_oddMode_integrable n).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos m)

private theorem oddCrossCorrelation_continuous (n m : ℕ) :
    Continuous (crossCorrelation (oddModeFunction n) (oddModeFunction m)) := by
  exact (hasCompactSupport_yoshidaClippedOddMode m).continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ)
    (starReflection_oddMode_integrable n).locallyIntegrable
    (continuous_yoshidaClippedOddMode yoshidaHalfLength_pos m)

theorem normalized_integral_oddAngularSpectralProduct_eq_crossCorrelation_zero
    (n m : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, oddAngularSpectralProduct n m v) =
      crossCorrelation (oddModeFunction n) (oddModeFunction m) 0 := by
  let H : ℝ → ℂ :=
    crossCorrelation (oddModeFunction n) (oddModeFunction m)
  have hH : Integrable H := by
    simpa only [H] using oddCrossCorrelation_integrable n m
  have hHcont : Continuous H := by
    simpa only [H] using oddCrossCorrelation_continuous n m
  have hFH : Integrable (FourierTransform.fourier H) := by
    apply (oddFourierProduct_integrable n m).congr
    filter_upwards [] with w
    exact (fourier_crossCorrelation
      (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos n)
      (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos m)
      (continuous_yoshidaClippedOddMode yoshidaHalfLength_pos n)
      (continuous_yoshidaClippedOddMode yoshidaHalfLength_pos m) w).symm
  have hinv : FourierTransform.fourierInv
      (FourierTransform.fourier H) 0 = H 0 :=
    hH.fourierInv_fourier_eq hFH hHcont.continuousAt
  have hzero : (∫ w : ℝ, FourierTransform.fourier H w) = H 0 := by
    rw [Real.fourierInv_eq] at hinv
    simpa using hinv
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := by positivity
  have hscale := Measure.integral_comp_mul_left
    (oddAngularSpectralProduct n m) c
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, oddAngularSpectralProduct n m v) =
        |c⁻¹| • ∫ v : ℝ, oddAngularSpectralProduct n m v := by
      rw [Complex.real_smul]
      congr 1
      dsimp [c]
      rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
      push_cast
      rw [one_div]
    _ = ∫ w : ℝ, oddAngularSpectralProduct n m (c * w) := hscale.symm
    _ = ∫ w : ℝ,
        star (FourierTransform.fourier (oddModeFunction n) w) *
          FourierTransform.fourier (oddModeFunction m) w := by
      apply integral_congr_ae
      filter_upwards [] with w
      unfold oddAngularSpectralProduct angularFourier
      congr 3 <;> dsimp [c] <;> field_simp [Real.pi_ne_zero]
    _ = ∫ w : ℝ, FourierTransform.fourier H w := by
      apply integral_congr_ae
      filter_upwards [] with w
      exact (fourier_crossCorrelation
        (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos n)
        (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos m)
        (continuous_yoshidaClippedOddMode yoshidaHalfLength_pos n)
        (continuous_yoshidaClippedOddMode yoshidaHalfLength_pos m) w).symm
    _ = H 0 := hzero
    _ = crossCorrelation (oddModeFunction n) (oddModeFunction m) 0 := rfl

/-- Cauchy-series value of the digamma part of the odd local critical
pairing. -/
def oddCorrelationZero (n m : ℕ) : ℂ :=
  crossCorrelation (oddModeFunction n) (oddModeFunction m) 0

def oddDigammaCauchySeriesValue (n m : ℕ) : ℂ :=
  -(oddCauchyCorrelationValue n m 0 +
      (Real.eulerMascheroniConstant : ℂ) * oddCorrelationZero n m +
      (∑' k : ℕ,
        (oddCauchyCorrelationValue n m (k + 1) -
          (((k + 1 : ℕ) : ℝ)⁻¹ : ℂ) * oddCorrelationZero n m))) -
    (Real.log Real.pi : ℂ) * oddCorrelationZero n m

theorem normalized_localCriticalKernel_oddSpectralProduct_eq_cauchySeries
    (n m : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        (((Complex.digamma
          ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
            Real.log Real.pi : ℝ) : ℂ) *
          oddAngularSpectralProduct n m v) =
      oddDigammaCauchySeriesValue n m := by
  simpa only [oddDigammaCauchySeriesValue] using
    localCriticalKernel_integral_eq_cauchySeries
      (oddAngularSpectralProduct n m)
      (oddAngularSpectralProduct_integrable n m)
      (oddAngularSpectralProduct_weighted_integrable n m)
      (oddCauchyCorrelationValue n m)
      (oddCorrelationZero n m)
      (normalized_bombieriDigammaKernel_oddSpectralProduct n m)
      (normalized_integral_oddAngularSpectralProduct_eq_crossCorrelation_zero n m)

theorem normalized_oddCriticalCrossIntegrand_eq_cauchySeries
    (n m : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand
          yoshidaHalfLength yoshidaHalfLength_pos
          (yoshidaClippedOddMode yoshidaHalfLength n)
          (yoshidaClippedOddMode yoshidaHalfLength m) v) =
      oddDigammaCauchySeriesValue n m := by
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ,
        yoshidaClippedCriticalCrossIntegrand
          yoshidaHalfLength yoshidaHalfLength_pos
          (yoshidaClippedOddMode yoshidaHalfLength n)
          (yoshidaClippedOddMode yoshidaHalfLength m) v) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ,
            (((Complex.digamma
              ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
                Real.log Real.pi : ℝ) : ℂ) *
              oddAngularSpectralProduct n m v) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      rw [yoshidaClippedCriticalCrossIntegrand,
        MultiplicativeWeil.bombieriLocalCriticalKernel]
      rw [← angularFourier_oddModeFunction_eq_criticalSample n v,
        ← angularFourier_oddModeFunction_eq_criticalSample m v]
      rw [oddAngularSpectralProduct]
      ring
    _ = oddDigammaCauchySeriesValue n m :=
      normalized_localCriticalKernel_oddSpectralProduct_eq_cauchySeries n m

private theorem star_oddModeFunction (n : ℕ) (x : ℝ) :
    star (oddModeFunction n x) = oddModeFunction n x := by
  unfold oddModeFunction
  rw [yoshidaClippedOddMode_apply_all yoshidaHalfLength_pos]
  by_cases hx : x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength
  · rw [if_pos hx]
    let r : ℝ := (Real.sqrt yoshidaHalfLength)⁻¹ *
      Real.sin (Real.pi * (n : ℝ) * x / yoshidaHalfLength)
    change star (r : ℂ) = (r : ℂ)
    simp
  · simp [hx]

theorem oddCrossCorrelation_eq_clippedOddCorrelation_swap
    {u : ℝ} (hu0 : 0 ≤ u) (huL : u ≤ yoshidaLength)
    (n m : ℕ) :
    crossCorrelation (oddModeFunction n) (oddModeFunction m) u =
      (clippedOddCorrelation yoshidaHalfLength m n u : ℂ) := by
  rw [crossCorrelation_apply]
  have hle : -yoshidaHalfLength ≤ yoshidaHalfLength - u := by
    rw [show yoshidaLength = 2 * yoshidaHalfLength by
      exact two_mul_yoshidaHalfLength.symm] at huL
    linarith
  have hsupport :
      (∫ x : ℝ,
        star (oddModeFunction n x) * oddModeFunction m (u + x)) =
        ∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength - u,
          star (oddModeFunction n x) * oddModeFunction m (u + x) := by
    rw [intervalIntegral.integral_of_le hle,
      ← integral_Icc_eq_integral_Ioc]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      by_cases hxn : x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength
      · have hxgt : yoshidaHalfLength - u < x := by
          by_contra hnot
          exact hx ⟨hxn.1, le_of_not_gt hnot⟩
        have hout : u + x ∉
            Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
          intro hmem
          linarith [hmem.2]
        simp only [oddModeFunction]
        rw [yoshidaClippedSmooth_eq_zero_outside _ hout, mul_zero]
      · simp only [oddModeFunction]
        rw [yoshidaClippedSmooth_eq_zero_outside _ hxn, star_zero, zero_mul])).symm
  rw [hsupport]
  calc
    (∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength - u,
        star (oddModeFunction n x) * oddModeFunction m (u + x)) =
        ∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength - u,
          ((clippedOddRealMode yoshidaHalfLength m (u + x) *
            clippedOddRealMode yoshidaHalfLength n x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈
          Set.Icc (-yoshidaHalfLength) (yoshidaHalfLength - u) := by
        simpa only [uIcc_of_le hle] using hx
      have hxIcc : x ∈
          Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
        constructor
        · exact hx'.1
        · linarith [hx'.2, hu0]
      have huxIcc : u + x ∈
          Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
        constructor <;> linarith [hx'.1, hx'.2, hu0]
      change star (oddModeFunction n x) * oddModeFunction m (u + x) = _
      rw [star_oddModeFunction]
      simp only [oddModeFunction]
      rw [
        yoshidaClippedOddMode_apply_of_mem yoshidaHalfLength_pos n hxIcc,
        yoshidaClippedOddMode_apply_of_mem yoshidaHalfLength_pos m huxIcc]
      norm_cast
      simp only [clippedOddRealMode]
      ring
    _ = (∫ x : ℝ in -yoshidaHalfLength..yoshidaHalfLength - u,
          clippedOddRealMode yoshidaHalfLength m (u + x) *
            clippedOddRealMode yoshidaHalfLength n x : ℝ) := by
      rw [intervalIntegral.integral_ofReal]
    _ = (clippedOddCorrelation yoshidaHalfLength m n u : ℂ) := rfl

theorem oddCrossCorrelation_neg_eq_swap (u : ℝ) (n m : ℕ) :
    crossCorrelation (oddModeFunction n) (oddModeFunction m) (-u) =
      crossCorrelation (oddModeFunction m) (oddModeFunction n) u := by
  rw [crossCorrelation_apply, crossCorrelation_apply]
  let G : ℝ → ℂ := fun y ↦
    star (oddModeFunction n (y + u)) * oddModeFunction m y
  calc
    (∫ x : ℝ, star (oddModeFunction n x) * oddModeFunction m (-u + x)) =
        ∫ x : ℝ, G (x + (-u)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [G]
      congr 2 <;> ring_nf
    _ = ∫ y : ℝ, G y := MeasureTheory.integral_add_right_eq_self G (-u)
    _ = ∫ y : ℝ,
        star (oddModeFunction m y) * oddModeFunction n (u + y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp only [G]
      rw [star_oddModeFunction, star_oddModeFunction]
      rw [add_comm y u, mul_comm]

theorem clippedOddCorrelation_half_comm
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (u : ℝ) :
    clippedOddCorrelation yoshidaHalfLength n m u =
      clippedOddCorrelation yoshidaHalfLength m n u := by
  by_cases hnm : n = m
  · subst m
    rfl
  rw [clippedOddCorrelation_half_offdiag hn hm hnm,
    clippedOddCorrelation_half_offdiag hm hn (Ne.symm hnm)]
  rw [add_comm m n]
  rw [show yoshidaKappa m * Real.sin (yoshidaKappa n * u) -
      yoshidaKappa n * Real.sin (yoshidaKappa m * u) =
      -(yoshidaKappa n * Real.sin (yoshidaKappa m * u) -
        yoshidaKappa m * Real.sin (yoshidaKappa n * u)) by ring_nf]
  rw [show yoshidaKappa m ^ 2 - yoshidaKappa n ^ 2 =
      -(yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) by ring_nf]
  rw [mul_neg, neg_div_neg_eq]

theorem oddCrossCorrelation_eq_clippedOddCorrelation
    {u : ℝ} (hu0 : 0 ≤ u) (huL : u ≤ yoshidaLength)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    crossCorrelation (oddModeFunction n) (oddModeFunction m) u =
      (clippedOddCorrelation yoshidaHalfLength n m u : ℂ) := by
  rw [oddCrossCorrelation_eq_clippedOddCorrelation_swap hu0 huL n m]
  rw [clippedOddCorrelation_half_comm hm hn u]

theorem oddCrossCorrelation_neg_eq_clippedOddCorrelation
    {u : ℝ} (hu0 : 0 ≤ u) (huL : u ≤ yoshidaLength)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    crossCorrelation (oddModeFunction n) (oddModeFunction m) (-u) =
      (clippedOddCorrelation yoshidaHalfLength n m u : ℂ) := by
  calc
    crossCorrelation (oddModeFunction n) (oddModeFunction m) (-u) =
        crossCorrelation (oddModeFunction m) (oddModeFunction n) u :=
      oddCrossCorrelation_neg_eq_swap u n m
    _ = (clippedOddCorrelation yoshidaHalfLength m n u : ℂ) :=
      oddCrossCorrelation_eq_clippedOddCorrelation hu0 huL hm hn
    _ = (clippedOddCorrelation yoshidaHalfLength n m u : ℂ) := by
      rw [clippedOddCorrelation_half_comm hm hn u]

end


end ArithmeticHodge.Analysis.YoshidaOddSpectralBridge
