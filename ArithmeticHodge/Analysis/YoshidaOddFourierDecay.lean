import ArithmeticHodge.Analysis.YoshidaOddModeRegularity
import ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped FourierTransform

namespace ArithmeticHodge.Analysis.YoshidaOddFourierDecay

noncomputable section

open YoshidaOddModeRegularity
open YoshidaSectionSixAnalytic

/-!
# Quadratic Fourier decay of clipped odd modes

Endpoint cancellation in the normalized odd sine modes improves their angular
Fourier transform from the generic clipped `O(1 / |v|)` estimate to
`O(1 / v ^ 2)`.  This gives integrability of every odd-mode transform and of
`(1 + w ^ 2)` times every pairwise Fourier-product norm, exactly the weighted
spectral hypothesis required by the abstract digamma distribution.
-/

theorem fourier_yoshidaClippedOddMode_eq_criticalSample
    {a : ℝ} (ha : 0 < a) (n : ℕ) (w : ℝ) :
    FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w =
      yoshidaCriticalSampleLinear a ha (2 * Real.pi * w)
        (yoshidaClippedOddMode a n) := by
  rw [yoshidaCriticalSample_eq_fourier]
  rw [show (2 * Real.pi * w) / (2 * Real.pi) = w by
    field_simp [Real.pi_ne_zero]]

private theorem negOne_zpow_neg_nat (n : ℕ) :
    (-1 : ℝ) ^ (-(n : ℤ)) = (-1 : ℝ) ^ (n : ℤ) := by
  rw [← Int.cast_negOnePow, ← Int.cast_negOnePow]
  simp

theorem criticalSample_yoshidaClippedOddMode_exact
    {a : ℝ} (ha : 0 < a) (n : ℕ) (v : ℝ)
    (hminus : a * v - Real.pi * (n : ℝ) ≠ 0)
    (hplus : a * v + Real.pi * (n : ℝ) ≠ 0) :
    yoshidaCriticalSampleLinear a ha v (yoshidaClippedOddMode a n) =
      (-Complex.I / (Real.sqrt 2 : ℂ)) *
        (((Real.sqrt (2 * a) * (-1 : ℝ) ^ (n : ℤ) * Real.sin (a * v) /
            (a * v - Real.pi * (n : ℝ)) : ℝ) : ℂ) -
          ((Real.sqrt (2 * a) * (-1 : ℝ) ^ (n : ℤ) * Real.sin (a * v) /
            (a * v + Real.pi * (n : ℝ)) : ℝ) : ℂ)) := by
  rw [yoshidaCriticalSample_clippedOddMode]
  rw [criticalSample_clippedExponential_eq_section6 ha v (n : ℤ) hminus]
  rw [criticalSample_clippedExponential_eq_section6 ha v (-(n : ℤ))]
  · norm_num only [Int.cast_neg, Int.cast_natCast]
    rw [negOne_zpow_neg_nat]
    congr 4
    ring
  · norm_num only [Int.cast_neg, Int.cast_natCast]
    simpa [sub_eq_add_neg] using hplus

theorem criticalSample_yoshidaClippedOddMode_combined
    {a : ℝ} (ha : 0 < a) (n : ℕ) (v : ℝ)
    (hminus : a * v - Real.pi * (n : ℝ) ≠ 0)
    (hplus : a * v + Real.pi * (n : ℝ) ≠ 0) :
    yoshidaCriticalSampleLinear a ha v (yoshidaClippedOddMode a n) =
      (-Complex.I / (Real.sqrt 2 : ℂ)) *
        ((Real.sqrt (2 * a) * (-1 : ℝ) ^ (n : ℤ) * Real.sin (a * v) *
            (2 * Real.pi * (n : ℝ)) /
              ((a * v) ^ 2 - (Real.pi * (n : ℝ)) ^ 2) : ℝ) : ℂ) := by
  have hsquare : (a * v) ^ 2 - (Real.pi * (n : ℝ)) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  have hsquare' : a ^ 2 * v ^ 2 - Real.pi ^ 2 * (n : ℝ) ^ 2 ≠ 0 := by
    simpa only [mul_pow] using hsquare
  rw [criticalSample_yoshidaClippedOddMode_exact ha n v hminus hplus]
  apply congrArg (fun z : ℂ ↦ (-Complex.I / (Real.sqrt 2 : ℂ)) * z)
  norm_cast
  field_simp [hminus, hplus, hsquare, hsquare']
  ring

private theorem clippedOdd_tail_aux
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) {v : ℝ}
    (hv : 2 * Real.pi * (n : ℝ) ≤ a * |v|) :
    a * v - Real.pi * (n : ℝ) ≠ 0 ∧
      a * v + Real.pi * (n : ℝ) ≠ 0 ∧
      a ^ 2 * v ^ 2 / 2 ≤
        (a * v) ^ 2 - (Real.pi * (n : ℝ)) ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  have hav_abs : |a * v| = a * |v| := by
    rw [abs_mul, abs_of_pos ha]
  have habs : Real.pi * (n : ℝ) < |a * v| := by
    rw [hav_abs]
    linarith
  have hminus : a * v - Real.pi * (n : ℝ) ≠ 0 := by
    intro h
    have hav : a * v = Real.pi * (n : ℝ) := sub_eq_zero.mp h
    rw [hav, abs_of_pos hp] at habs
    exact lt_irrefl _ habs
  have hplus : a * v + Real.pi * (n : ℝ) ≠ 0 := by
    intro h
    have hav : a * v = -(Real.pi * (n : ℝ)) := eq_neg_of_add_eq_zero_left h
    rw [hav, abs_neg, abs_of_pos hp] at habs
    exact lt_irrefl _ habs
  refine ⟨hminus, hplus, ?_⟩
  have hsquares :
      (2 * Real.pi * (n : ℝ)) ^ 2 ≤ (a * |v|) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hv
  have hsquares' :
      (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 ≤ a ^ 2 * v ^ 2 := by
    simpa only [mul_pow, sq_abs] using hsquares
  nlinarith [hsquares', sq_nonneg (a * v),
    sq_nonneg (Real.pi * (n : ℝ))]

theorem norm_criticalSample_yoshidaClippedOddMode_le_inv_sq
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) {v : ℝ}
    (hv : 2 * Real.pi * (n : ℝ) ≤ a * |v|) :
    ‖yoshidaCriticalSampleLinear a ha v (yoshidaClippedOddMode a n)‖ ≤
      4 * Real.sqrt (2 * a) * Real.pi * (n : ℝ) / (a ^ 2 * v ^ 2) := by
  obtain ⟨hminus, hplus, hden_lower⟩ := clippedOdd_tail_aux ha hn hv
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  have hv0 : v ≠ 0 := by
    intro hvzero
    subst v
    norm_num at hv
    linarith
  have hbase_pos : 0 < a ^ 2 * v ^ 2 / 2 := by positivity
  have hden_pos :
      0 < (a * v) ^ 2 - (Real.pi * (n : ℝ)) ^ 2 :=
    lt_of_lt_of_le hbase_pos hden_lower
  have hsqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_two_one : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have houter : 1 / |Real.sqrt 2| ≤ 1 := by
    rw [abs_of_pos hsqrt_two_pos]
    exact (div_le_one hsqrt_two_pos).2 hsqrt_two_one
  have houter_nonneg : 0 ≤ 1 / |Real.sqrt 2| := by positivity
  have hnum :
      |Real.sqrt (2 * a) * (-1 : ℝ) ^ (n : ℤ) * Real.sin (a * v) *
          (2 * Real.pi * (n : ℝ))| ≤
        Real.sqrt (2 * a) * (2 * Real.pi * (n : ℝ)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_zpow]
    norm_num only [abs_neg, abs_one, one_zpow, mul_one]
    rw [abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hnR)]
    gcongr
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (a * v))
        (Real.sqrt_nonneg (2 * a)))
  have hnum_nonneg :
      0 ≤ Real.sqrt (2 * a) * (2 * Real.pi * (n : ℝ)) := by positivity
  rw [criticalSample_yoshidaClippedOddMode_combined ha n v hminus hplus,
    norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos hden_pos]
  calc
    1 / |Real.sqrt 2| *
          (|Real.sqrt (2 * a) * (-1 : ℝ) ^ (n : ℤ) * Real.sin (a * v) *
            (2 * Real.pi * (n : ℝ))| /
              ((a * v) ^ 2 - (Real.pi * (n : ℝ)) ^ 2)) ≤
        1 * (|Real.sqrt (2 * a) * (-1 : ℝ) ^ (n : ℤ) * Real.sin (a * v) *
            (2 * Real.pi * (n : ℝ))| /
              ((a * v) ^ 2 - (Real.pi * (n : ℝ)) ^ 2)) := by
          gcongr
    _ ≤ Real.sqrt (2 * a) * (2 * Real.pi * (n : ℝ)) /
          ((a * v) ^ 2 - (Real.pi * (n : ℝ)) ^ 2) := by
          simpa only [one_mul] using
            (div_le_div_of_nonneg_right hnum (le_of_lt hden_pos))
    _ ≤ Real.sqrt (2 * a) * (2 * Real.pi * (n : ℝ)) /
          (a ^ 2 * v ^ 2 / 2) := by
          exact div_le_div₀ hnum_nonneg le_rfl hbase_pos hden_lower
    _ = 4 * Real.sqrt (2 * a) * Real.pi * (n : ℝ) /
          (a ^ 2 * v ^ 2) := by
          field_simp
          ring

theorem norm_fourier_yoshidaClippedOddMode_le_inv_sq
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) {w : ℝ}
    (hw : (n : ℝ) ≤ a * |w|) :
    ‖FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w‖ ≤
      Real.sqrt (2 * a) * (n : ℝ) /
        (a ^ 2 * Real.pi * w ^ 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw0 : w ≠ 0 := by
    intro hwzero
    subst w
    norm_num at hw
    linarith
  have hsample :
      2 * Real.pi * (n : ℝ) ≤ a * |2 * Real.pi * w| := by
    have hmul := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * Real.pi by positivity)
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
    nlinarith
  rw [fourier_yoshidaClippedOddMode_eq_criticalSample ha n w]
  calc
    ‖yoshidaCriticalSampleLinear a ha (2 * Real.pi * w)
        (yoshidaClippedOddMode a n)‖ ≤
        4 * Real.sqrt (2 * a) * Real.pi * (n : ℝ) /
          (a ^ 2 * (2 * Real.pi * w) ^ 2) :=
      norm_criticalSample_yoshidaClippedOddMode_le_inv_sq ha hn hsample
    _ = Real.sqrt (2 * a) * (n : ℝ) /
          (a ^ 2 * Real.pi * w ^ 2) := by
      field_simp [ne_of_gt ha, Real.pi_ne_zero, hw0]
      ring

private theorem norm_fourier_yoshidaClippedOddMode_le_inv_one_add_sq
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) {w : ℝ}
    (hone : 1 ≤ |w|) (htail : (n : ℝ) ≤ a * |w|) :
    ‖FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w‖ ≤
      (2 * (Real.sqrt (2 * a) * (n : ℝ) / (a ^ 2 * Real.pi))) *
        ‖((1 + w ^ 2)⁻¹ : ℝ)‖ := by
  have hw_sq : 1 ≤ w ^ 2 := by
    rw [← sq_abs]
    simpa only [one_pow] using
      ((sq_le_sq₀ (by norm_num) (abs_nonneg w)).2 hone)
  have hw_sq_pos : 0 < w ^ 2 := lt_of_lt_of_le (by norm_num) hw_sq
  have hone_sq_pos : 0 < 1 + w ^ 2 := by positivity
  have hrecip : 1 / w ^ 2 ≤ 2 / (1 + w ^ 2) := by
    rw [div_le_div_iff₀ hw_sq_pos hone_sq_pos]
    nlinarith
  have hconstant_nonneg :
      0 ≤ Real.sqrt (2 * a) * (n : ℝ) / (a ^ 2 * Real.pi) := by
    positivity
  calc
    ‖FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w‖ ≤
        Real.sqrt (2 * a) * (n : ℝ) / (a ^ 2 * Real.pi * w ^ 2) :=
      norm_fourier_yoshidaClippedOddMode_le_inv_sq ha hn htail
    _ = (Real.sqrt (2 * a) * (n : ℝ) / (a ^ 2 * Real.pi)) *
          (1 / w ^ 2) := by ring
    _ ≤ (Real.sqrt (2 * a) * (n : ℝ) / (a ^ 2 * Real.pi)) *
          (2 / (1 + w ^ 2)) :=
      mul_le_mul_of_nonneg_left hrecip hconstant_nonneg
    _ = (2 * (Real.sqrt (2 * a) * (n : ℝ) / (a ^ 2 * Real.pi))) *
          ‖((1 + w ^ 2)⁻¹ : ℝ)‖ := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos hone_sq_pos]
      ring

theorem fourier_yoshidaClippedOddMode_isBigO_atTop
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    (fun w : ℝ ↦
      FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w) =O[Filter.atTop]
      (fun w : ℝ ↦ (1 + w ^ 2)⁻¹) := by
  apply Asymptotics.IsBigO.of_bound
    (2 * (Real.sqrt (2 * a) * (n : ℝ) / (a ^ 2 * Real.pi)))
  filter_upwards [Filter.eventually_ge_atTop
      (max 1 ((n : ℝ) / a))] with w hw
  have hw_one : 1 ≤ w := le_trans (le_max_left _ _) hw
  have hone : 1 ≤ |w| := le_trans hw_one (le_abs_self w)
  have hw_tail : (n : ℝ) ≤ a * |w| := by
    have hquot : (n : ℝ) / a ≤ w := le_trans (le_max_right _ _) hw
    have hmul := mul_le_mul_of_nonneg_left hquot (le_of_lt ha)
    rw [mul_div_cancel₀ _ (ne_of_gt ha)] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left (le_abs_self w) (le_of_lt ha))
  exact norm_fourier_yoshidaClippedOddMode_le_inv_one_add_sq
    ha hn hone hw_tail

theorem fourier_yoshidaClippedOddMode_isBigO_atBot
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    (fun w : ℝ ↦
      FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w) =O[Filter.atBot]
      (fun w : ℝ ↦ (1 + w ^ 2)⁻¹) := by
  apply Asymptotics.IsBigO.of_bound
    (2 * (Real.sqrt (2 * a) * (n : ℝ) / (a ^ 2 * Real.pi)))
  filter_upwards [Filter.eventually_le_atBot
      (-max 1 ((n : ℝ) / a))] with w hw
  have hw_neg : max 1 ((n : ℝ) / a) ≤ -w := by linarith
  have hw_one : 1 ≤ -w := le_trans (le_max_left _ _) hw_neg
  have hone : 1 ≤ |w| := by
    rw [← abs_neg]
    exact le_trans hw_one (le_abs_self (-w))
  have hw_tail : (n : ℝ) ≤ a * |w| := by
    have hquot : (n : ℝ) / a ≤ -w :=
      le_trans (le_max_right _ _) hw_neg
    have hmul := mul_le_mul_of_nonneg_left hquot (le_of_lt ha)
    rw [mul_div_cancel₀ _ (ne_of_gt ha)] at hmul
    rw [← abs_neg]
    exact hmul.trans
      (mul_le_mul_of_nonneg_left (le_abs_self (-w)) (le_of_lt ha))
  exact norm_fourier_yoshidaClippedOddMode_le_inv_one_add_sq
    ha hn hone hw_tail

theorem continuous_fourier_yoshidaClippedOddMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Continuous (fun w : ℝ ↦
      FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w) := by
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (integrable_yoshidaClippedOddMode ha n)

theorem integrable_fourier_yoshidaClippedOddMode
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    Integrable (fun w : ℝ ↦
      FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w) := by
  exact MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atBot_atTop
    (continuous_fourier_yoshidaClippedOddMode ha n).locallyIntegrable
    (fourier_yoshidaClippedOddMode_isBigO_atBot ha hn)
    (integrable_inv_one_add_sq.integrableAtFilter Filter.atBot)
    (fourier_yoshidaClippedOddMode_isBigO_atTop ha hn)
    (integrable_inv_one_add_sq.integrableAtFilter Filter.atTop)

private theorem one_add_sq_isBigO_self
    {l : Filter ℝ} :
    (fun w : ℝ ↦ ((1 + w ^ 2 : ℝ) : ℂ)) =O[l]
      (fun w : ℝ ↦ 1 + w ^ 2) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards with w
  rw [Complex.norm_real]
  simp only [one_mul]
  exact le_rfl

private theorem weightedFourierProduct_isBigO
    {l : Filter ℝ} {a : ℝ} {n m : ℕ}
    (hnO : (fun w : ℝ ↦
      FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w) =O[l]
        (fun w : ℝ ↦ (1 + w ^ 2)⁻¹))
    (hmO : (fun w : ℝ ↦
      FourierTransform.fourier (yoshidaClippedOddMode a m : ℝ → ℂ) w) =O[l]
        (fun w : ℝ ↦ (1 + w ^ 2)⁻¹)) :
    (fun w : ℝ ↦ ((1 + w ^ 2 : ℝ) : ℂ) *
      (FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w *
       FourierTransform.fourier (yoshidaClippedOddMode a m : ℝ → ℂ) w)) =O[l]
      (fun w : ℝ ↦ (1 + w ^ 2)⁻¹) := by
  have hproduct := hnO.mul hmO
  have hweighted := (one_add_sq_isBigO_self (l := l)).mul hproduct
  apply hweighted.congr_right
  intro w
  have hne : 1 + w ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hne]

theorem weightedFourierProduct_isBigO_atTop
    {a : ℝ} (ha : 0 < a) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (fun w : ℝ ↦ ((1 + w ^ 2 : ℝ) : ℂ) *
      (FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w *
       FourierTransform.fourier (yoshidaClippedOddMode a m : ℝ → ℂ) w)) =O[Filter.atTop]
      (fun w : ℝ ↦ (1 + w ^ 2)⁻¹) :=
  weightedFourierProduct_isBigO
    (fourier_yoshidaClippedOddMode_isBigO_atTop ha hn)
    (fourier_yoshidaClippedOddMode_isBigO_atTop ha hm)

theorem weightedFourierProduct_isBigO_atBot
    {a : ℝ} (ha : 0 < a) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (fun w : ℝ ↦ ((1 + w ^ 2 : ℝ) : ℂ) *
      (FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w *
       FourierTransform.fourier (yoshidaClippedOddMode a m : ℝ → ℂ) w)) =O[Filter.atBot]
      (fun w : ℝ ↦ (1 + w ^ 2)⁻¹) :=
  weightedFourierProduct_isBigO
    (fourier_yoshidaClippedOddMode_isBigO_atBot ha hn)
    (fourier_yoshidaClippedOddMode_isBigO_atBot ha hm)

theorem continuous_weightedFourierProduct
    {a : ℝ} (ha : 0 < a) (n m : ℕ) :
    Continuous (fun w : ℝ ↦ ((1 + w ^ 2 : ℝ) : ℂ) *
      (FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w *
       FourierTransform.fourier (yoshidaClippedOddMode a m : ℝ → ℂ) w)) := by
  have hweightR : Continuous (fun w : ℝ ↦ 1 + w ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hweightC : Continuous (fun w : ℝ ↦ ((1 + w ^ 2 : ℝ) : ℂ)) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_ofReal.comp hweightR
  exact hweightC.mul
    ((continuous_fourier_yoshidaClippedOddMode ha n).mul
      (continuous_fourier_yoshidaClippedOddMode ha m))

theorem integrable_weightedFourierProduct
    {a : ℝ} (ha : 0 < a) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    Integrable (fun w : ℝ ↦ ((1 + w ^ 2 : ℝ) : ℂ) *
      (FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w *
       FourierTransform.fourier (yoshidaClippedOddMode a m : ℝ → ℂ) w)) := by
  exact MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atBot_atTop
    (continuous_weightedFourierProduct ha n m).locallyIntegrable
    (weightedFourierProduct_isBigO_atBot ha hn hm)
    (integrable_inv_one_add_sq.integrableAtFilter Filter.atBot)
    (weightedFourierProduct_isBigO_atTop ha hn hm)
    (integrable_inv_one_add_sq.integrableAtFilter Filter.atTop)

theorem integrable_one_add_sq_mul_norm_fourierProduct
    {a : ℝ} (ha : 0 < a) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    Integrable (fun w : ℝ ↦ (1 + w ^ 2) *
      ‖FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w *
       FourierTransform.fourier (yoshidaClippedOddMode a m : ℝ → ℂ) w‖) := by
  have hnorm := (integrable_weightedFourierProduct ha hn hm).norm
  have habs : ∀ w : ℝ, |1 + w ^ 2| = 1 + w ^ 2 := fun w ↦
    abs_of_nonneg (by positivity)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    habs] using hnorm

theorem yoshidaClippedOddMode_zero (a : ℝ) :
    yoshidaClippedOddMode a 0 = 0 := by
  simp [yoshidaClippedOddMode]

private theorem fourier_zero_fun :
    FourierTransform.fourier (0 : ℝ → ℂ) = 0 := by
  funext w
  rw [Real.fourier_eq]
  simp

theorem integrable_fourier_yoshidaClippedOddMode_all
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun w : ℝ ↦
      FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w) := by
  rcases n with _ | n
  · simp only [yoshidaClippedOddMode_zero]
    change Integrable (fun w : ℝ ↦
      FourierTransform.fourier (0 : ℝ → ℂ) w)
    rw [fourier_zero_fun]
    exact MeasureTheory.integrable_zero ℝ ℂ volume
  · exact integrable_fourier_yoshidaClippedOddMode ha (Nat.succ_pos n)

theorem integrable_one_add_sq_mul_norm_fourierProduct_all
    {a : ℝ} (ha : 0 < a) (n m : ℕ) :
    Integrable (fun w : ℝ ↦ (1 + w ^ 2) *
      ‖FourierTransform.fourier (yoshidaClippedOddMode a n : ℝ → ℂ) w *
       FourierTransform.fourier (yoshidaClippedOddMode a m : ℝ → ℂ) w‖) := by
  rcases n with _ | n
  · simp only [yoshidaClippedOddMode_zero]
    change Integrable (fun w : ℝ ↦ (1 + w ^ 2) *
      ‖FourierTransform.fourier (0 : ℝ → ℂ) w *
        FourierTransform.fourier (yoshidaClippedOddMode a m : ℝ → ℂ) w‖)
    rw [fourier_zero_fun]
    simpa only [Pi.zero_apply, norm_zero, zero_mul, mul_zero] using
      (MeasureTheory.integrable_zero ℝ ℝ volume)
  rcases m with _ | m
  · simp only [yoshidaClippedOddMode_zero]
    change Integrable (fun w : ℝ ↦ (1 + w ^ 2) *
      ‖FourierTransform.fourier
          (yoshidaClippedOddMode a (n + 1) : ℝ → ℂ) w *
        FourierTransform.fourier (0 : ℝ → ℂ) w‖)
    rw [fourier_zero_fun]
    simpa only [Pi.zero_apply, norm_zero, zero_mul, mul_zero] using
      (MeasureTheory.integrable_zero ℝ ℝ volume)
  exact integrable_one_add_sq_mul_norm_fourierProduct ha
    (Nat.succ_pos n) (Nat.succ_pos m)

end

end ArithmeticHodge.Analysis.YoshidaOddFourierDecay
