import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural

noncomputable section

open MeasureTheory Real Set
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur

/-!
# Structural bounds for the three `P5` alternating entries

Each entry uses its exact correlation polynomial.  The regular kernel is
controlled by the common quadratic majorant, the archimedean model is
integrated symbolically, and the retained-prime value is enclosed at the
single structural lag.
-/

private theorem integral_inv_two_add_p5 :
    (∫ t : ℝ in 0..2, 1 / (2 + t)) = Real.log 2 := by
  let F : ℝ → ℝ := fun t ↦ Real.log (2 + t)
  have hderiv (t : ℝ) (ht : 2 + t ≠ 0) :
      HasDerivAt F (1 / (2 + t)) t := by
    have hadd : HasDerivAt (fun x : ℝ ↦ 2 + x) 1 t := by
      simpa using (hasDerivAt_const t 2).add (hasDerivAt_id t)
    simpa only [F, Function.comp_apply, one_div, mul_one] using
      (Real.hasDerivAt_log ht).comp t hadd
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (2 + t))
      (uIcc (0 : ℝ) 2) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hderiv t (by
      have ht' : t ∈ Icc (0 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
      linarith [ht'.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring]
  ring

private theorem intervalIntegrable_inv_two_add_p5 :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

private theorem integral_abs_alternatingCorrelation_le_majorant
    (q : ℝ → ℝ) (hq : Continuous q) :
    (∫ t : ℝ in 0..2, |intrinsicAlternatingCorrelation q t|) ≤
      ∫ t : ℝ in 0..2, t * (2 - t) * (q t ^ 2 + 1) / 2 := by
  let g : ℝ → ℝ := fun t ↦ t * (2 - t) * (q t ^ 2 + 1) / 2
  have hcorr : Continuous (intrinsicAlternatingCorrelation q) := by
    unfold intrinsicAlternatingCorrelation
    fun_prop
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hcorr.abs.intervalIntegrable 0 2) (hg.intervalIntegrable 0 2)
  intro t ht
  have hw : 0 ≤ t * (2 - t) :=
    mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hqabs : |q t| ≤ (q t ^ 2 + 1) / 2 := by
    nlinarith [sq_nonneg (|q t| - 1), sq_abs (q t)]
  unfold intrinsicAlternatingCorrelation
  rw [abs_mul, abs_of_nonneg hw]
  simpa only [g, div_eq_mul_inv, mul_assoc] using
    (mul_le_mul_of_nonneg_left hqabs hw)

private theorem integral_abs_q05_le :
    (∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation alternatingQ05 t|) ≤
        (112 / 165 : ℝ) := by
  calc
    _ ≤ ∫ t : ℝ in 0..2,
        t * (2 - t) * (alternatingQ05 t ^ 2 + 1) / 2 :=
      integral_abs_alternatingCorrelation_le_majorant alternatingQ05
        (by unfold alternatingQ05; fun_prop)
    _ = (112 / 165 : ℝ) := by
      unfold alternatingQ05
      ring_nf
      repeat' first
        | rw [intervalIntegral.integral_add
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        | rw [intervalIntegral.integral_sub
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      norm_num

private theorem integral_abs_q25_le :
    (∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation alternatingQ25 t|) ≤
        (1361 / 2002 : ℝ) := by
  calc
    _ ≤ ∫ t : ℝ in 0..2,
        t * (2 - t) * (alternatingQ25 t ^ 2 + 1) / 2 :=
      integral_abs_alternatingCorrelation_le_majorant alternatingQ25
        (by unfold alternatingQ25; fun_prop)
    _ = (1361 / 2002 : ℝ) := by
      unfold alternatingQ25
      ring_nf
      repeat' first
        | rw [intervalIntegral.integral_add
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        | rw [intervalIntegral.integral_sub
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      norm_num

private theorem integral_abs_q45_le :
    (∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation alternatingQ45 t|) ≤
        (10044329 / 14549535 : ℝ) := by
  calc
    _ ≤ ∫ t : ℝ in 0..2,
        t * (2 - t) * (alternatingQ45 t ^ 2 + 1) / 2 :=
      integral_abs_alternatingCorrelation_le_majorant alternatingQ45
        (by unfold alternatingQ45; fun_prop)
    _ = (10044329 / 14549535 : ℝ) := by
      unfold alternatingQ45
      ring_nf
      repeat' first
        | rw [intervalIntegral.integral_add
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        | rw [intervalIntegral.integral_sub
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      norm_num

private theorem abs_regularError_q05_lt :
    |intrinsicAlternatingRegularError alternatingQ05| <
      (7 / 10000 : ℝ) := by
  have h := abs_intrinsicAlternatingRegularError_le alternatingQ05
    (by unfold alternatingQ05; fun_prop)
  calc
    _ ≤ (1 / 1000 : ℝ) *
        (∫ t : ℝ in 0..2,
          |intrinsicAlternatingCorrelation alternatingQ05 t|) := h
    _ ≤ (1 / 1000 : ℝ) * (112 / 165 : ℝ) :=
      mul_le_mul_of_nonneg_left integral_abs_q05_le (by norm_num)
    _ < (7 / 10000 : ℝ) := by norm_num

private theorem abs_regularError_q25_lt :
    |intrinsicAlternatingRegularError alternatingQ25| <
      (7 / 10000 : ℝ) := by
  have h := abs_intrinsicAlternatingRegularError_le alternatingQ25
    (by unfold alternatingQ25; fun_prop)
  calc
    _ ≤ (1 / 1000 : ℝ) *
        (∫ t : ℝ in 0..2,
          |intrinsicAlternatingCorrelation alternatingQ25 t|) := h
    _ ≤ (1 / 1000 : ℝ) * (1361 / 2002 : ℝ) :=
      mul_le_mul_of_nonneg_left integral_abs_q25_le (by norm_num)
    _ < (7 / 10000 : ℝ) := by norm_num

private theorem abs_regularError_q45_lt :
    |intrinsicAlternatingRegularError alternatingQ45| <
      (7 / 10000 : ℝ) := by
  have h := abs_intrinsicAlternatingRegularError_le alternatingQ45
    (by unfold alternatingQ45; fun_prop)
  calc
    _ ≤ (1 / 1000 : ℝ) *
        (∫ t : ℝ in 0..2,
          |intrinsicAlternatingCorrelation alternatingQ45 t|) := h
    _ ≤ (1 / 1000 : ℝ) * (10044329 / 14549535 : ℝ) :=
      mul_le_mul_of_nonneg_left integral_abs_q45_le (by norm_num)
    _ < (7 / 10000 : ℝ) := by norm_num

private theorem archModel_q05 :
    intrinsicAlternatingArchModel alternatingQ05 =
      -(8192 / 15 : ℝ) + 788 * Real.log 2 := by
  let p : ℝ → ℝ := fun t ↦
    -(21 / 80 : ℝ) * t ^ 7 + (63 / 40 : ℝ) * t ^ 6 -
      (7 / 8 : ℝ) * t ^ 5 - (49 / 4 : ℝ) * t ^ 4 +
      44 * t ^ 3 - (489 / 5 : ℝ) * t ^ 2 + 197 * t - 394
  have hint : intrinsicAlternatingArchModel alternatingQ05 =
      ∫ t : ℝ in 0..2, p t + 788 * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      alternatingQ05
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    dsimp only [p]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 2 := by
    exact (by dsimp only [p]; fun_prop : Continuous p).intervalIntegrable 0 2
  rw [hint, intervalIntegral.integral_add hp
      (intervalIntegrable_inv_two_add_p5.const_mul 788),
    intervalIntegral.integral_const_mul, integral_inv_two_add_p5]
  dsimp only [p]
  ring_nf
  repeat' first
    | rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem archModel_q25 :
    intrinsicAlternatingArchModel alternatingQ25 =
      -(715 / 6 : ℝ) + 172 * Real.log 2 := by
  let p : ℝ → ℝ := fun t ↦
    -(9 / 640 : ℝ) * t ^ 9 + (101 / 320 : ℝ) * t ^ 7 -
      (39 / 16 : ℝ) * t ^ 5 + (21 / 10 : ℝ) * t ^ 4 +
      (131 / 20 : ℝ) * t ^ 3 - (104 / 5 : ℝ) * t ^ 2 +
      43 * t - 86
  have hint : intrinsicAlternatingArchModel alternatingQ25 =
      ∫ t : ℝ in 0..2, p t + 172 * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      alternatingQ25
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    dsimp only [p]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 2 := by
    exact (by dsimp only [p]; fun_prop : Continuous p).intervalIntegrable 0 2
  rw [hint, intervalIntegral.integral_add hp
      (intervalIntegrable_inv_two_add_p5.const_mul 172),
    intervalIntegral.integral_const_mul, integral_inv_two_add_p5]
  dsimp only [p]
  ring_nf
  repeat' first
    | rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem archModel_q45 :
    intrinsicAlternatingArchModel alternatingQ45 =
      -(41 / 15 : ℝ) + 4 * Real.log 2 := by
  let p : ℝ → ℝ := fun t ↦
    -(7 / 1280 : ℝ) * t ^ 11 + (15 / 128 : ℝ) * t ^ 9 -
      (107 / 160 : ℝ) * t ^ 7 + (3 / 2 : ℝ) * t ^ 5 -
      (3 / 2 : ℝ) * t ^ 3 + (1 / 5 : ℝ) * t ^ 2 + t - 2
  have hint : intrinsicAlternatingArchModel alternatingQ45 =
      ∫ t : ℝ in 0..2, p t + 4 * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      alternatingQ45
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    dsimp only [p]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 2 := by
    exact (by dsimp only [p]; fun_prop : Continuous p).intervalIntegrable 0 2
  rw [hint, intervalIntegral.integral_add hp
      (intervalIntegrable_inv_two_add_p5.const_mul 4),
    intervalIntegral.integral_const_mul, integral_inv_two_add_p5]
  dsimp only [p]
  ring_nf
  repeat' first
    | rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem archModel_q05_bounds :
    (6664 / 100000 : ℝ) < intrinsicAlternatingArchModel alternatingQ05 ∧
      intrinsicAlternatingArchModel alternatingQ05 < (6665 / 100000 : ℝ) := by
  rw [archModel_q05]
  have h := strict_log_two_fine_bounds
  constructor <;> nlinarith [h.1, h.2]

private theorem archModel_q25_bounds :
    (5464 / 100000 : ℝ) < intrinsicAlternatingArchModel alternatingQ25 ∧
      intrinsicAlternatingArchModel alternatingQ25 < (5466 / 100000 : ℝ) := by
  rw [archModel_q25]
  have h := strict_log_two_fine_bounds
  constructor <;> nlinarith [h.1, h.2]

private theorem archModel_q45_bounds :
    (3925 / 100000 : ℝ) < intrinsicAlternatingArchModel alternatingQ45 ∧
      intrinsicAlternatingArchModel alternatingQ45 < (3926 / 100000 : ℝ) := by
  rw [archModel_q45]
  have h := strict_log_two_fine_bounds
  constructor <;> nlinarith [h.1, h.2]

private theorem offset_pow_lt
    {y eps : ℝ} (hy : 0 ≤ y) (hye : y < eps)
    (n : ℕ) (hn : n ≠ 0) :
    y ^ n < eps ^ n :=
  pow_lt_pow_left₀ hye hy hn

private theorem primeCorrelation_q05_bounds :
    (744 / 10000 : ℝ) < intrinsicAlternatingCorrelation alternatingQ05
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation alternatingQ05
        (factorTwoPrimeShift / yoshidaEndpointA) < (745 / 10000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 116992 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hy0 : 0 < y := by dsimp only [y, tau]; linarith [htau.1]
  have hyU : y < (1 / 100000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := offset_pow_lt hy0.le hyU 2 (by norm_num)
  have hy3 := offset_pow_lt hy0.le hyU 3 (by norm_num)
  have hy4 := offset_pow_lt hy0.le hyU 4 (by norm_num)
  have hy5 := offset_pow_lt hy0.le hyU 5 (by norm_num)
  have hy6 := offset_pow_lt hy0.le hyU 6 (by norm_num)
  have htauy : tau = 116992 / 100000 + y := by dsimp only [y]; ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  unfold intrinsicAlternatingCorrelation alternatingQ05
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6,
    sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6]

private theorem primeCorrelation_q25_bounds :
    (1187 / 10000 : ℝ) < intrinsicAlternatingCorrelation alternatingQ25
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation alternatingQ25
        (factorTwoPrimeShift / yoshidaEndpointA) < (1188 / 10000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 116992 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hy0 : 0 < y := by dsimp only [y, tau]; linarith [htau.1]
  have hyU : y < (1 / 100000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := offset_pow_lt hy0.le hyU 2 (by norm_num)
  have hy3 := offset_pow_lt hy0.le hyU 3 (by norm_num)
  have hy4 := offset_pow_lt hy0.le hyU 4 (by norm_num)
  have hy5 := offset_pow_lt hy0.le hyU 5 (by norm_num)
  have hy6 := offset_pow_lt hy0.le hyU 6 (by norm_num)
  have hy7 := offset_pow_lt hy0.le hyU 7 (by norm_num)
  have hy8 := offset_pow_lt hy0.le hyU 8 (by norm_num)
  have htauy : tau = 116992 / 100000 + y := by dsimp only [y]; ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  unfold intrinsicAlternatingCorrelation alternatingQ25
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8,
    sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6, pow_nonneg hy0.le 7,
    pow_nonneg hy0.le 8]

private theorem primeCorrelation_q45_bounds :
    (631 / 10000 : ℝ) < intrinsicAlternatingCorrelation alternatingQ45
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation alternatingQ45
        (factorTwoPrimeShift / yoshidaEndpointA) < (632 / 10000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 116992 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hy0 : 0 < y := by dsimp only [y, tau]; linarith [htau.1]
  have hyU : y < (1 / 100000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := offset_pow_lt hy0.le hyU 2 (by norm_num)
  have hy3 := offset_pow_lt hy0.le hyU 3 (by norm_num)
  have hy4 := offset_pow_lt hy0.le hyU 4 (by norm_num)
  have hy5 := offset_pow_lt hy0.le hyU 5 (by norm_num)
  have hy6 := offset_pow_lt hy0.le hyU 6 (by norm_num)
  have hy7 := offset_pow_lt hy0.le hyU 7 (by norm_num)
  have hy8 := offset_pow_lt hy0.le hyU 8 (by norm_num)
  have hy9 := offset_pow_lt hy0.le hyU 9 (by norm_num)
  have hy10 := offset_pow_lt hy0.le hyU 10 (by norm_num)
  have htauy : tau = 116992 / 100000 + y := by dsimp only [y]; ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  unfold intrinsicAlternatingCorrelation alternatingQ45
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9, hy10,
    sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6, pow_nonneg hy0.le 7,
    pow_nonneg hy0.le 8, pow_nonneg hy0.le 9, pow_nonneg hy0.le 10]

/-- Coarse structural enclosure of the `P0/P5` alternating entry. -/
theorem factorTwoIntrinsicFourP45Cross05_bounds :
    (18 / 1000 : ℝ) < factorTwoIntrinsicFourP45Cross05 ∧
      factorTwoIntrinsicFourP45Cross05 < (21 / 1000 : ℝ) := by
  rw [factorTwoIntrinsicFourP45Cross05_eq_structuralModel]
  have herr := abs_lt.mp abs_regularError_q05_lt
  have harch := archModel_q05_bounds
  have hcorr := primeCorrelation_q05_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 :=
    (by norm_num : (0 : ℝ) < 63427 / 100000).trans hbeta.1
  have hcorr0 : 0 < intrinsicAlternatingCorrelation alternatingQ05
      (factorTwoPrimeShift / yoshidaEndpointA) :=
    (by norm_num : (0 : ℝ) < 744 / 10000).trans hcorr.1
  have hproductLower :
      (63427 / 100000 : ℝ) * (744 / 10000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ05
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      _ < (Real.log 3 / Real.sqrt 3) * (744 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hcorr.1 hbeta0
  have hproductUpper :
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ05
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (745 / 10000 : ℝ) := by
    calc
      _ < (6343 / 10000 : ℝ) *
          intrinsicAlternatingCorrelation alternatingQ05
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hbeta.2 hcorr0
      _ < _ := mul_lt_mul_of_pos_left hcorr.2 (by norm_num)
  constructor <;> nlinarith

/-- Coarse structural enclosure of the `P2/P5` alternating entry. -/
theorem factorTwoIntrinsicFourP45Cross25_bounds :
    (-22 / 1000 : ℝ) < factorTwoIntrinsicFourP45Cross25 ∧
      factorTwoIntrinsicFourP45Cross25 < (-19 / 1000 : ℝ) := by
  rw [factorTwoIntrinsicFourP45Cross25_eq_structuralModel]
  have herr := abs_lt.mp abs_regularError_q25_lt
  have harch := archModel_q25_bounds
  have hcorr := primeCorrelation_q25_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 :=
    (by norm_num : (0 : ℝ) < 63427 / 100000).trans hbeta.1
  have hcorr0 : 0 < intrinsicAlternatingCorrelation alternatingQ25
      (factorTwoPrimeShift / yoshidaEndpointA) :=
    (by norm_num : (0 : ℝ) < 1187 / 10000).trans hcorr.1
  have hproductLower :
      (63427 / 100000 : ℝ) * (1187 / 10000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ25
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      _ < (Real.log 3 / Real.sqrt 3) * (1187 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hcorr.1 hbeta0
  have hproductUpper :
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ25
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (1188 / 10000 : ℝ) := by
    calc
      _ < (6343 / 10000 : ℝ) *
          intrinsicAlternatingCorrelation alternatingQ25
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hbeta.2 hcorr0
      _ < _ := mul_lt_mul_of_pos_left hcorr.2 (by norm_num)
  constructor <;> nlinarith

/-- Structural enclosure of the `P4/P5` alternating entry. -/
theorem factorTwoIntrinsicSixAlternating45_bounds :
    (-2 / 1000 : ℝ) < factorTwoIntrinsicSixAlternating45 ∧
      factorTwoIntrinsicSixAlternating45 < 0 := by
  rw [factorTwoIntrinsicSixAlternating45_eq_structuralModel]
  have herr := abs_lt.mp abs_regularError_q45_lt
  have harch := archModel_q45_bounds
  have hcorr := primeCorrelation_q45_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 :=
    (by norm_num : (0 : ℝ) < 63427 / 100000).trans hbeta.1
  have hcorr0 : 0 < intrinsicAlternatingCorrelation alternatingQ45
      (factorTwoPrimeShift / yoshidaEndpointA) :=
    (by norm_num : (0 : ℝ) < 631 / 10000).trans hcorr.1
  have hproductLower :
      (63427 / 100000 : ℝ) * (631 / 10000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ45
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      _ < (Real.log 3 / Real.sqrt 3) * (631 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hcorr.1 hbeta0
  have hproductUpper :
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ45
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (632 / 10000 : ℝ) := by
    calc
      _ < (6343 / 10000 : ℝ) *
          intrinsicAlternatingCorrelation alternatingQ45
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hbeta.2 hcorr0
      _ < _ := mul_lt_mul_of_pos_left hcorr.2 (by norm_num)
  constructor <;> nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingBoundsStructural
