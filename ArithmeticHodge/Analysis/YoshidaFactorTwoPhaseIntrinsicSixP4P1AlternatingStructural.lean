import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural

noncomputable section

open MeasureTheory Real Set
open CenteredOddOneThreeEnergy
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaConstantBounds

/-!
# Structural interval for the P4/P1 alternating coupling

The coupling is reduced to its exact polynomial correlation model.  The
archimedean term is integrated symbolically, the regular-kernel remainder is
controlled uniformly, and the retained prime atom is enclosed on its
structural shift interval.
-/

private def a41 : ℝ := factorTwoIntrinsicFourP45Cross41

private def alternatingQ41 (t : ℝ) : ℝ :=
  -1 + 4 * t - (23 / 6 : ℝ) * t ^ 2 + (7 / 12 : ℝ) * t ^ 3 +
    (7 / 24 : ℝ) * t ^ 4

private theorem crossDifference_p4_p1
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation centeredP1 factorTwoCenteredP4 t -
        factorTwoCenteredCrossCorrelation factorTwoCenteredP4 centeredP1 t =
      intrinsicAlternatingCorrelation alternatingQ41 t := by
  unfold factorTwoCenteredCrossCorrelation centeredP1 factorTwoCenteredP4
    intrinsicAlternatingCorrelation alternatingQ41
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  simp only [smul_eq_mul]
  ring

private theorem a41_eq_structuralModel :
    a41 = intrinsicAlternatingRegularError alternatingQ41 +
        intrinsicAlternatingArchModel alternatingQ41 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ41
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold a41 factorTwoIntrinsicFourP45Cross41
  exact factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
    factorTwoCenteredP4 centeredP1 alternatingQ41
    (by unfold alternatingQ41; fun_prop) crossDifference_p4_p1

private theorem integral_inv_two_add_c2 :
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

private theorem intervalIntegrable_inv_two_add_c2 :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

private theorem alternatingArchModel_q41 :
    intrinsicAlternatingArchModel alternatingQ41 =
      (608 / 9 : ℝ) - (292 / 3 : ℝ) * Real.log 2 := by
  let p : ℝ → ℝ := fun t ↦
    (146 / 3 : ℝ) - 73 / 3 * t + 172 / 15 * t ^ 2 -
      44 / 15 * t ^ 3 - 7 / 6 * t ^ 4 + 19 / 24 * t ^ 5 -
      7 / 240 * t ^ 7
  have hint : intrinsicAlternatingArchModel alternatingQ41 =
      ∫ t : ℝ in 0..2, p t - (292 / 3) * (1 / (2 + t)) := by
    unfold intrinsicAlternatingArchModel intrinsicAlternatingCorrelation
      alternatingQ41
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
      (intervalIntegrable_inv_two_add_c2.const_mul (292 / 3)),
    intervalIntegral.integral_const_mul, integral_inv_two_add_c2]
  dsimp only [p]
  ring_nf
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num

private theorem integral_abs_alternatingCorrelation_q41_le :
    (∫ t : ℝ in 0..2,
      |intrinsicAlternatingCorrelation alternatingQ41 t|) ≤
        (21506 / 31185 : ℝ) := by
  let g : ℝ → ℝ := fun t ↦
    t * (2 - t) * (alternatingQ41 t ^ 2 + 1) / 2
  have hcorr : Continuous
      (intrinsicAlternatingCorrelation alternatingQ41) := by
    unfold intrinsicAlternatingCorrelation alternatingQ41
    fun_prop
  have hg : Continuous g := by
    dsimp only [g]
    unfold alternatingQ41
    fun_prop
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2,
      |intrinsicAlternatingCorrelation alternatingQ41 t| ≤ g t := by
    intro t ht
    let q : ℝ := alternatingQ41 t
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
        |intrinsicAlternatingCorrelation alternatingQ41 t|) ≤
        ∫ t : ℝ in 0..2, g t := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hcorr.abs.intervalIntegrable 0 2) (hg.intervalIntegrable 0 2)
      exact hpoint
    _ = (21506 / 31185 : ℝ) := by
      dsimp only [g]
      unfold alternatingQ41
      ring_nf
      repeat' first
        | rw [intervalIntegral.integral_add
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        | rw [intervalIntegral.integral_sub
            (Continuous.intervalIntegrable (by fun_prop) 0 2)
            (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      norm_num

private theorem abs_alternatingRegularError_q41_lt :
    |intrinsicAlternatingRegularError alternatingQ41| <
      (7 / 10000 : ℝ) := by
  have h := abs_intrinsicAlternatingRegularError_le alternatingQ41
    (by unfold alternatingQ41; fun_prop)
  have hint := integral_abs_alternatingCorrelation_q41_le
  calc
    |intrinsicAlternatingRegularError alternatingQ41| ≤
        (1 / 1000 : ℝ) *
          (∫ t : ℝ in 0..2,
            |intrinsicAlternatingCorrelation alternatingQ41 t|) := h
    _ ≤ (1 / 1000 : ℝ) * (21506 / 31185 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hint (by norm_num)
    _ < (7 / 10000 : ℝ) := by norm_num

private theorem alternatingCorrelation_q41_prime_bounds :
    (-85 / 1000 : ℝ) <
        intrinsicAlternatingCorrelation alternatingQ41
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      intrinsicAlternatingCorrelation alternatingQ41
          (factorTwoPrimeShift / yoshidaEndpointA) < (-84 / 1000 : ℝ) := by
  let τ : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := τ - 11699 / 10000
  have hτ := factorTwoPrimeRatio_kernel_bounds
  have hy0 : 0 < y := by
    dsimp only [y, τ]
    linarith [hτ.1]
  have hyU : y < (1 / 10000 : ℝ) := by
    dsimp only [y, τ]
    linarith [hτ.2]
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
  have hy2_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hy3_nonneg : 0 ≤ y ^ 3 := by positivity
  have hy4_nonneg : 0 ≤ y ^ 4 := by positivity
  have hy5_nonneg : 0 ≤ y ^ 5 := by positivity
  have hy6_nonneg : 0 ≤ y ^ 6 := by positivity
  have hτy : τ = 11699 / 10000 + y := by
    dsimp only [y]
    ring
  dsimp only [τ] at hτy ⊢
  rw [hτy]
  unfold intrinsicAlternatingCorrelation alternatingQ41
  ring_nf
  constructor <;>
    nlinarith [hy2, hy3, hy4, hy5, hy6, hy2_nonneg,
      hy3_nonneg, hy4_nonneg, hy5_nonneg, hy6_nonneg]

private theorem alternatingArchModel_q41_bounds :
    (891 / 10000 : ℝ) < intrinsicAlternatingArchModel alternatingQ41 ∧
      intrinsicAlternatingArchModel alternatingQ41 < (893 / 10000 : ℝ) := by
  rw [alternatingArchModel_q41]
  have hlog := strict_log_two_fine_bounds
  constructor <;> nlinarith [hlog.1, hlog.2]

theorem factorTwoIntrinsicFourP45Cross41_bounds :
    (141 / 1000 : ℝ) < factorTwoIntrinsicFourP45Cross41 ∧
      factorTwoIntrinsicFourP45Cross41 < (144 / 1000 : ℝ) := by
  change (141 / 1000 : ℝ) < a41 ∧ a41 < (144 / 1000 : ℝ)
  rw [a41_eq_structuralModel]
  have herr := (abs_lt.mp abs_alternatingRegularError_q41_lt)
  have harch := alternatingArchModel_q41_bounds
  have hcorr := alternatingCorrelation_q41_prime_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 := by
    linarith [hbeta.1]
  have hnegcorr0 : 0 <
      -intrinsicAlternatingCorrelation alternatingQ41
        (factorTwoPrimeShift / yoshidaEndpointA) := by
    linarith [hcorr.2]
  have hprod_lower :
      (63427 / 100000 : ℝ) * (84 / 1000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          (-intrinsicAlternatingCorrelation alternatingQ41
            (factorTwoPrimeShift / yoshidaEndpointA)) := by
    calc
      (63427 / 100000 : ℝ) * (84 / 1000 : ℝ) <
          (Real.log 3 / Real.sqrt 3) * (84 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          (-intrinsicAlternatingCorrelation alternatingQ41
            (factorTwoPrimeShift / yoshidaEndpointA)) :=
        mul_lt_mul_of_pos_left (by linarith [hcorr.2]) hbeta0
  have hprod_upper :
      (Real.log 3 / Real.sqrt 3) *
          (-intrinsicAlternatingCorrelation alternatingQ41
            (factorTwoPrimeShift / yoshidaEndpointA)) <
        (6343 / 10000 : ℝ) * (85 / 1000 : ℝ) := by
    calc
      (Real.log 3 / Real.sqrt 3) *
          (-intrinsicAlternatingCorrelation alternatingQ41
            (factorTwoPrimeShift / yoshidaEndpointA)) <
          (6343 / 10000 : ℝ) *
            (-intrinsicAlternatingCorrelation alternatingQ41
              (factorTwoPrimeShift / yoshidaEndpointA)) :=
        mul_lt_mul_of_pos_right hbeta.2 hnegcorr0
      _ < (6343 / 10000 : ℝ) * (85 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_left (by linarith [hcorr.1]) (by norm_num)
  constructor <;>
    nlinarith [herr.1, herr.2, harch.1, harch.2, hprod_lower, hprod_upper]


end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
