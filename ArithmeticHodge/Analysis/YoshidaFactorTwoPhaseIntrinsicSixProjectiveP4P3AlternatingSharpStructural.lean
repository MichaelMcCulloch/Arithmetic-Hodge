import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural

noncomputable section

open MeasureTheory Real Set
open CenteredOddOneThreeEnergy
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural

/-! ## The missing `P4/P3` alternating coordinate -/

private def alternatingQ43 (t : ℝ) : ℝ :=
  -1 + (3 / 2 : ℝ) * t + (3 / 4 : ℝ) * t ^ 2 -
    (7 / 8 : ℝ) * t ^ 3 - (7 / 16 : ℝ) * t ^ 4 +
    (5 / 32 : ℝ) * t ^ 5 + (5 / 64 : ℝ) * t ^ 6

private theorem crossDifference_p4_p3
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation centeredP3 factorTwoCenteredP4 t -
        factorTwoCenteredCrossCorrelation factorTwoCenteredP4 centeredP3 t =
      intrinsicAlternatingCorrelation alternatingQ43 t := by
  unfold factorTwoCenteredCrossCorrelation centeredP3 factorTwoCenteredP4
    intrinsicAlternatingCorrelation alternatingQ43
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  rw [intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  have htwo :
      (∫ x : ℝ in -1..1 - t, t * x ^ 2 * (45 / 4)) =
        (45 * t / 4) * (((1 - t) ^ 3 - (-1 : ℝ) ^ 3) / 3) := by
    rw [show (fun x : ℝ ↦ t * x ^ 2 * (45 / 4)) =
        fun x ↦ (45 * t / 4) * x ^ 2 by funext x; ring,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  have hfour :
      (∫ x : ℝ in -1..1 - t, t * x ^ 4 * 45) =
        (45 * t) * (((1 - t) ^ 5 - (-1 : ℝ) ^ 5) / 5) := by
    rw [show (fun x : ℝ ↦ t * x ^ 4 * 45) =
        fun x ↦ (45 * t) * x ^ 4 by funext x; ring,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [htwo, hfour]
  simp only [smul_eq_mul]
  ring

private theorem cross43_eq_structuralModel :
    factorTwoIntrinsicFourP45Cross43 =
      intrinsicAlternatingRegularError alternatingQ43 +
        intrinsicAlternatingArchModel alternatingQ43 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ43
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoIntrinsicFourP45Cross43
  exact factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
    factorTwoCenteredP4 centeredP3 alternatingQ43
    (by unfold alternatingQ43; fun_prop) crossDifference_p4_p3

private theorem integral_inv_two_add_raw_five_c1 :
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

private theorem intervalIntegrable_inv_two_add_raw_five_c1 :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

private theorem alternatingArchModel_q43 :
    intrinsicAlternatingArchModel alternatingQ43 =
      (17 / 6 : ℝ) - 4 * Real.log 2 := by
  let p : ℝ → ℝ := fun t ↦
    2 - t - (1 / 5 : ℝ) * t ^ 2 +
      (23 / 20 : ℝ) * t ^ 3 -
      (11 / 16 : ℝ) * t ^ 5 +
      (49 / 320 : ℝ) * t ^ 7 - (1 / 128 : ℝ) * t ^ 9
  have hint : intrinsicAlternatingArchModel alternatingQ43 =
      ∫ t : ℝ in 0..2, p t - 4 * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      alternatingQ43
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    have hden : 2 + t ≠ 0 := by linarith [ht.1]
    dsimp only [p]
    field_simp [hden]
    ring
  have hp : IntervalIntegrable p volume 0 2 := by
    exact (by dsimp only [p]; fun_prop : Continuous p).intervalIntegrable 0 2
  rw [hint, intervalIntegral.integral_sub hp
      (intervalIntegrable_inv_two_add_raw_five_c1.const_mul 4),
    intervalIntegral.integral_const_mul, integral_inv_two_add_raw_five_c1]
  dsimp only [p]
  ring_nf
  repeat' first
    | rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    | rw [intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  norm_num

private theorem integral_abs_alternatingCorrelation_q43_le :
    (∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation alternatingQ43 t|) ≤
        (9067 / 12870 : ℝ) := by
  let g : ℝ → ℝ := fun t ↦
    t * (2 - t) * (alternatingQ43 t ^ 2 + 1) / 2
  have hcorr : Continuous
      (intrinsicAlternatingCorrelation alternatingQ43) := by
    unfold intrinsicAlternatingCorrelation alternatingQ43
    fun_prop
  have hg : Continuous g := by
    dsimp only [g]
    unfold alternatingQ43
    fun_prop
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2,
      |intrinsicAlternatingCorrelation alternatingQ43 t| ≤ g t := by
    intro t ht
    let q : ℝ := alternatingQ43 t
    have hw : 0 ≤ t * (2 - t) :=
      mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    have hq : |q| ≤ (q ^ 2 + 1) / 2 := by
      nlinarith [sq_nonneg (|q| - 1), sq_abs q]
    dsimp only [q] at hq
    unfold intrinsicAlternatingCorrelation
    rw [abs_mul, abs_of_nonneg hw]
    dsimp only [g]
    simpa only [div_eq_mul_inv, mul_assoc] using
      (mul_le_mul_of_nonneg_left hq hw)
  calc
    (∫ t : ℝ in 0..2,
        |intrinsicAlternatingCorrelation alternatingQ43 t|) ≤
        ∫ t : ℝ in 0..2, g t := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hcorr.abs.intervalIntegrable 0 2) (hg.intervalIntegrable 0 2)
      exact hpoint
    _ = (9067 / 12870 : ℝ) := by
      dsimp only [g]
      unfold alternatingQ43
      ring_nf
      repeat' first
        | rw [intervalIntegral.integral_add
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        | rw [intervalIntegral.integral_sub
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      norm_num

private theorem abs_alternatingRegularError_q43_lt :
    |intrinsicAlternatingRegularError alternatingQ43| <
      (71 / 100000 : ℝ) := by
  have h := abs_intrinsicAlternatingRegularError_le alternatingQ43
    (by unfold alternatingQ43; fun_prop)
  have hint := integral_abs_alternatingCorrelation_q43_le
  calc
    |intrinsicAlternatingRegularError alternatingQ43| ≤
        (1 / 1000 : ℝ) *
          (∫ t : ℝ in 0..2,
            |intrinsicAlternatingCorrelation alternatingQ43 t|) := h
    _ ≤ (1 / 1000 : ℝ) * (9067 / 12870 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hint (by norm_num)
    _ < (71 / 100000 : ℝ) := by norm_num

private theorem alternatingCorrelation_q43_prime_bounds :
    (1004 / 10000 : ℝ) <
        intrinsicAlternatingCorrelation alternatingQ43
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation alternatingQ43
          (factorTwoPrimeShift / yoshidaEndpointA) < (1006 / 10000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 11699 / 10000
  have htau := factorTwoPrimeRatio_kernel_bounds
  have hy0 : 0 < y := by
    dsimp only [y, tau]
    linarith [htau.1]
  have hyU : y < (1 / 10000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 : y ^ 2 < (1 / 10000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy3 : y ^ 3 < (1 / 10000 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy4 : y ^ 4 < (1 / 10000 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy5 : y ^ 5 < (1 / 10000 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy6 : y ^ 6 < (1 / 10000 : ℝ) ^ 6 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy7 : y ^ 7 < (1 / 10000 : ℝ) ^ 7 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy8 : y ^ 8 < (1 / 10000 : ℝ) ^ 8 :=
    pow_lt_pow_left₀ hyU hy0.le (by norm_num)
  have hy2n : 0 ≤ y ^ 2 := sq_nonneg y
  have hy3n : 0 ≤ y ^ 3 := by positivity
  have hy4n : 0 ≤ y ^ 4 := by positivity
  have hy5n : 0 ≤ y ^ 5 := by positivity
  have hy6n : 0 ≤ y ^ 6 := by positivity
  have hy7n : 0 ≤ y ^ 7 := by positivity
  have hy8n : 0 ≤ y ^ 8 := by positivity
  have htauy : tau = 11699 / 10000 + y := by
    dsimp only [y]
    ring
  dsimp only [tau] at htauy ⊢
  rw [htauy]
  unfold intrinsicAlternatingCorrelation alternatingQ43
  ring_nf
  constructor <;>
    nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8,
      hy2n, hy3n, hy4n, hy5n, hy6n, hy7n, hy8n]

/-- Structural rational enclosure for the `P4/P3` alternating coordinate. -/
theorem factorTwoIntrinsicFourP45Cross43_bounds :
    (-4 / 1000 : ℝ) < factorTwoIntrinsicFourP45Cross43 ∧
      factorTwoIntrinsicFourP45Cross43 < (-2 / 1000 : ℝ) := by
  rw [cross43_eq_structuralModel, alternatingArchModel_q43]
  have herr := abs_lt.mp abs_alternatingRegularError_q43_lt
  have hcorr := alternatingCorrelation_q43_prime_bounds
  have hlog := strict_log_two_fine_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 := by linarith [hbeta.1]
  have hcorr0 : 0 < intrinsicAlternatingCorrelation alternatingQ43
      (factorTwoPrimeShift / yoshidaEndpointA) := by linarith [hcorr.1]
  have hprodLower :
      (63427 / 100000 : ℝ) * (1004 / 10000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ43
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      _ < (Real.log 3 / Real.sqrt 3) * (1004 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hcorr.1 hbeta0
  have hprodUpper :
      (Real.log 3 / Real.sqrt 3) *
          intrinsicAlternatingCorrelation alternatingQ43
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (6343 / 10000 : ℝ) * (1006 / 10000 : ℝ) := by
    calc
      _ < (6343 / 10000 : ℝ) *
          intrinsicAlternatingCorrelation alternatingQ43
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hbeta.2 hcorr0
      _ < _ := mul_lt_mul_of_pos_left hcorr.2 (by norm_num)
  constructor <;> nlinarith [hlog.1, hlog.2, hprodLower, hprodUpper]


end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
