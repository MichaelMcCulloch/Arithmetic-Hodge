import ArithmeticHodge.Analysis.YoshidaOddSpectralBridge

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaOddCorrelationFold

noncomputable section

open YoshidaCauchyPairing
open YoshidaClippedMomentBridge
open YoshidaOddGramPrefix
open YoshidaOddModeRegularity
open YoshidaOddSpectralBridge

private theorem starReflection_oddModeFunction_integrable (n : ℕ) :
    Integrable (starReflection (oddModeFunction n)) := by
  have hneg : Integrable (fun x : ℝ ↦ oddModeFunction n (-x)) :=
    (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos n).comp_neg
  simpa only [starReflection, RCLike.star_def] using
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hneg

theorem oddCrossCorrelation_integrable (n m : ℕ) :
    Integrable (crossCorrelation (oddModeFunction n) (oddModeFunction m)) := by
  exact (starReflection_oddModeFunction_integrable n).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_yoshidaClippedOddMode yoshidaHalfLength_pos m)

theorem oddCrossCorrelation_eq_zero_of_length_lt
    {u : ℝ} (hu : yoshidaLength < u) (n m : ℕ) :
    crossCorrelation (oddModeFunction n) (oddModeFunction m) u = 0 := by
  rw [crossCorrelation_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength
  · have hux : u + x ∉ Set.Icc (-yoshidaHalfLength) yoshidaHalfLength := by
      intro hmem
      rw [← two_mul_yoshidaHalfLength] at hu
      linarith [hx.1, hmem.2]
    simp only [oddModeFunction]
    rw [yoshidaClippedSmooth_eq_zero_outside _ hux, mul_zero]
    simp
  · simp only [oddModeFunction]
    rw [yoshidaClippedSmooth_eq_zero_outside _ hx, star_zero, zero_mul]
    simp

private theorem oddCrossCorrelation_comm_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    crossCorrelation (oddModeFunction n) (oddModeFunction m) u =
      crossCorrelation (oddModeFunction m) (oddModeFunction n) u := by
  by_cases huL : u ≤ yoshidaLength
  · rw [oddCrossCorrelation_eq_clippedOddCorrelation_swap hu huL,
      oddCrossCorrelation_eq_clippedOddCorrelation_swap hu huL]
    norm_cast
    exact clippedOddCorrelation_half_comm hm hn u
  · have hLt : yoshidaLength < u := lt_of_not_ge huL
    rw [oddCrossCorrelation_eq_zero_of_length_lt hLt,
      oddCrossCorrelation_eq_zero_of_length_lt hLt]

theorem oddCrossCorrelation_comm
    (u : ℝ) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    crossCorrelation (oddModeFunction n) (oddModeFunction m) u =
      crossCorrelation (oddModeFunction m) (oddModeFunction n) u := by
  by_cases hu : 0 ≤ u
  · exact oddCrossCorrelation_comm_of_nonneg hu hn hm
  · have hneg : 0 ≤ -u := by linarith
    calc
      crossCorrelation (oddModeFunction n) (oddModeFunction m) u =
          crossCorrelation (oddModeFunction m) (oddModeFunction n) (-u) := by
        simpa only [neg_neg] using
          oddCrossCorrelation_neg_eq_swap (-u) n m
      _ = crossCorrelation (oddModeFunction n) (oddModeFunction m) (-u) :=
        oddCrossCorrelation_comm_of_nonneg hneg hm hn
      _ = crossCorrelation (oddModeFunction m) (oddModeFunction n) u :=
        oddCrossCorrelation_neg_eq_swap u n m

theorem oddCrossCorrelation_even
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    Function.Even (crossCorrelation (oddModeFunction n) (oddModeFunction m)) := by
  intro u
  rw [oddCrossCorrelation_neg_eq_swap]
  exact oddCrossCorrelation_comm u hm hn

theorem exp_abs_mul_oddCrossCorrelation_integrable
    {a : ℝ} (ha : 0 < a) (n m : ℕ) :
    Integrable (fun u : ℝ ↦
      ((Real.exp (-a * |u|) : ℝ) : ℂ) *
        crossCorrelation (oddModeFunction n) (oddModeFunction m) u) := by
  have hcoeff : Continuous (fun u : ℝ ↦
      ((Real.exp (-a * |u|) : ℝ) : ℂ)) := by fun_prop
  refine (oddCrossCorrelation_integrable n m).bdd_mul (c := 1)
    hcoeff.aestronglyMeasurable ?_
  filter_upwards [] with u
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_le_one_iff).2 (mul_nonpos_of_nonpos_of_nonneg
    (by linarith : -a ≤ 0) (abs_nonneg u))

/-- Correct compact-support fold: the correlation of two modes supported on
`[-yoshidaHalfLength, yoshidaHalfLength]` reaches `yoshidaLength` on each side. -/
theorem exp_abs_mul_oddCrossCorrelation_eq_two_integral_length
    {a : ℝ} (ha : 0 < a) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    (∫ u : ℝ,
      ((Real.exp (-a * |u|) : ℝ) : ℂ) *
        crossCorrelation (oddModeFunction n) (oddModeFunction m) u) =
      2 * ∫ u : ℝ in 0..yoshidaLength,
        ((Real.exp (-a * u) : ℝ) : ℂ) *
          (clippedOddCorrelation yoshidaHalfLength n m u : ℂ) := by
  let F : ℝ → ℂ := fun u ↦
    ((Real.exp (-a * |u|) : ℝ) : ℂ) *
      crossCorrelation (oddModeFunction n) (oddModeFunction m) u
  have hFint : Integrable F := by
    simpa only [F] using
      exp_abs_mul_oddCrossCorrelation_integrable ha n m
  have hFeven : Function.Even F := by
    intro u
    dsimp only [F]
    rw [abs_neg, oddCrossCorrelation_even hn hm]
  have hleft : (∫ u : ℝ in Set.Iic 0, F u) =
      ∫ u : ℝ in Set.Ioi 0, F u := by
    calc
      (∫ u : ℝ in Set.Iic 0, F u) =
          ∫ u : ℝ in Set.Iic 0, F (-u) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _
        exact (hFeven u).symm
      _ = ∫ u : ℝ in Set.Ioi 0, F u := by
        simpa only [neg_zero] using integral_comp_neg_Iic 0 F
  have hwhole : (∫ u : ℝ, F u) =
      2 * ∫ u : ℝ in Set.Ioi 0, F u := by
    rw [← intervalIntegral.integral_Iic_add_Ioi
        hFint.integrableOn hFint.integrableOn,
      hleft]
    ring
  have hpositive : (∫ u : ℝ in Set.Ioi 0, F u) =
      ∫ u : ℝ in 0..yoshidaLength, F u := by
    rw [intervalIntegral.integral_of_le yoshidaLength_pos.le]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self
    intro u hu
    have huLt : yoshidaLength < u := by
      rcases hu with ⟨hu0, huNot⟩
      simp only [mem_Ioi] at hu0
      simp only [mem_Ioc, not_and, not_le] at huNot
      exact huNot hu0
    dsimp only [F]
    rw [oddCrossCorrelation_eq_zero_of_length_lt huLt, mul_zero]
  have hinterval : (∫ u : ℝ in 0..yoshidaLength, F u) =
      ∫ u : ℝ in 0..yoshidaLength,
        ((Real.exp (-a * u) : ℝ) : ℂ) *
          (clippedOddCorrelation yoshidaHalfLength n m u : ℂ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) yoshidaLength := by
      simpa only [uIcc_of_le yoshidaLength_pos.le] using hu
    dsimp only [F]
    rw [abs_of_nonneg hu'.1,
      oddCrossCorrelation_eq_clippedOddCorrelation_swap hu'.1 hu'.2]
    rw [clippedOddCorrelation_half_comm hm hn u]
  change (∫ u : ℝ, F u) = _
  rw [hwhole, hpositive, hinterval]

/-- Exact decomposition showing the additional tail omitted by a fold only to
`yoshidaHalfLength`. -/
theorem exp_abs_mul_oddCrossCorrelation_eq_half_plus_tail
    {a : ℝ} (ha : 0 < a) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    (∫ u : ℝ,
      ((Real.exp (-a * |u|) : ℝ) : ℂ) *
        crossCorrelation (oddModeFunction n) (oddModeFunction m) u) =
      2 * (∫ u : ℝ in 0..yoshidaHalfLength,
        ((Real.exp (-a * u) : ℝ) : ℂ) *
          (clippedOddCorrelation yoshidaHalfLength n m u : ℂ)) +
      2 * (∫ u : ℝ in yoshidaHalfLength..yoshidaLength,
        ((Real.exp (-a * u) : ℝ) : ℂ) *
          (clippedOddCorrelation yoshidaHalfLength n m u : ℂ)) := by
  let G : ℝ → ℂ := fun u ↦
    ((Real.exp (-a * u) : ℝ) : ℂ) *
      (clippedOddCorrelation yoshidaHalfLength n m u : ℂ)
  have hGint : IntervalIntegrable G volume 0 yoshidaLength := by
    have hFint := exp_abs_mul_oddCrossCorrelation_integrable ha n m
    apply hFint.intervalIntegrable.congr
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) yoshidaLength := by
      have huIcc := Set.uIoc_subset_uIcc hu
      simpa only [uIcc_of_le yoshidaLength_pos.le] using huIcc
    dsimp only [G]
    rw [abs_of_nonneg hu'.1,
      oddCrossCorrelation_eq_clippedOddCorrelation_swap hu'.1 hu'.2]
    rw [clippedOddCorrelation_half_comm hm hn u]
  have hhalf : IntervalIntegrable G volume 0 yoshidaHalfLength := by
    apply hGint.mono_set
    intro u hu
    rw [uIcc_of_le yoshidaHalfLength_pos.le] at hu
    rw [uIcc_of_le yoshidaLength_pos.le]
    constructor
    · exact hu.1
    · rw [← two_mul_yoshidaHalfLength]
      linarith [hu.2, yoshidaHalfLength_pos]
  have htail : IntervalIntegrable G volume yoshidaHalfLength yoshidaLength := by
    apply hGint.mono_set
    intro u hu
    have hhalf_le_length : yoshidaHalfLength ≤ yoshidaLength := by
      rw [← two_mul_yoshidaHalfLength]
      linarith [yoshidaHalfLength_pos]
    rw [uIcc_of_le hhalf_le_length] at hu
    rw [uIcc_of_le yoshidaLength_pos.le]
    exact ⟨yoshidaHalfLength_pos.le.trans hu.1, hu.2⟩
  rw [exp_abs_mul_oddCrossCorrelation_eq_two_integral_length ha hn hm]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hhalf htail
  dsimp only [G] at hsplit
  rw [← hsplit]
  ring

/-- Each Cauchy-series correlation value is the real compact-interval
Laplace moment used by the renormalized geometric-kernel identity. -/
theorem oddCauchyCorrelationValue_eq_two_integral_length
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (k : ℕ) :
    oddCauchyCorrelationValue n m k =
      ((2 * ∫ u : ℝ in 0..yoshidaLength,
        Real.exp (-(2 * (k : ℝ) + 1 / 2) * u) *
          clippedOddCorrelation yoshidaHalfLength n m u : ℝ) : ℂ) := by
  have h := exp_abs_mul_oddCrossCorrelation_eq_two_integral_length
    (a := 2 * (k : ℝ) + 1 / 2) (by positivity) hn hm
  rw [oddCauchyCorrelationValue]
  calc
    (∫ u : ℝ,
        (Real.exp (-(2 * (k : ℝ) + 1 / 2) * |u|) : ℝ) *
          crossCorrelation (oddModeFunction n) (oddModeFunction m) u) =
        2 * ∫ u : ℝ in 0..yoshidaLength,
          ((Real.exp (-(2 * (k : ℝ) + 1 / 2) * u) : ℝ) : ℂ) *
            (clippedOddCorrelation yoshidaHalfLength n m u : ℂ) := h
    _ = ((2 * ∫ u : ℝ in 0..yoshidaLength,
          Real.exp (-(2 * (k : ℝ) + 1 / 2) * u) *
            clippedOddCorrelation yoshidaHalfLength n m u : ℝ) : ℂ) := by
      push_cast
      rw [← intervalIntegral.integral_ofReal]
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      push_cast
      rfl

theorem oddCorrelationZero_eq_clippedOddCorrelation_zero
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    oddCorrelationZero n m =
      (clippedOddCorrelation yoshidaHalfLength n m 0 : ℂ) := by
  exact oddCrossCorrelation_eq_clippedOddCorrelation
    (u := 0) (by norm_num) yoshidaLength_pos.le hn hm

end

end ArithmeticHodge.Analysis.YoshidaOddCorrelationFold
