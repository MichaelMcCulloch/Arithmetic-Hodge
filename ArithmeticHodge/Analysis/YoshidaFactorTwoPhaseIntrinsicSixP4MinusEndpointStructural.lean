import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PrimeCorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural

noncomputable section

open CenteredEndpointCorrelation
open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open YoshidaConstantBounds
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PrimeCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural closure of the negative `P0/P2/P4` endpoint

The exact perturbation split is imported from the shared structural layer.
This file proves the retained-prime sign, a rational `P4` diagonal reserve,
and the final exact-column Schur gate.
-/

private theorem factorTwoIntrinsicP4PrimeCorrelation44_gt_one_sixteenth :
    (1 / 16 : ℝ) < factorTwoIntrinsicP4Correlation44
      (factorTwoPrimeShift / yoshidaEndpointA) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 1
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hyLower : (16992 / 100000 : ℝ) < y := by
    dsimp only [y, tau]
    linarith [htau.1]
  have hy0 : 0 ≤ y := by linarith [hyLower]
  have hyUpper : y < (17 / 100 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := pow_lt_pow_left₀ hyUpper hy0
    (by norm_num : (2 : ℕ) ≠ 0)
  have hy3 := pow_lt_pow_left₀ hyUpper hy0
    (by norm_num : (3 : ℕ) ≠ 0)
  have hy6 := pow_lt_pow_left₀ hyUpper hy0
    (by norm_num : (6 : ℕ) ≠ 0)
  have hy7 := pow_lt_pow_left₀ hyUpper hy0
    (by norm_num : (7 : ℕ) ≠ 0)
  have hy8 := pow_lt_pow_left₀ hyUpper hy0
    (by norm_num : (8 : ℕ) ≠ 0)
  have hy9 := pow_lt_pow_left₀ hyUpper hy0
    (by norm_num : (9 : ℕ) ≠ 0)
  have hidentity :
      factorTwoIntrinsicP4Correlation44 tau =
        (53 + 333 * y - 900 * y ^ 2 - 1380 * y ^ 3 +
          1710 * y ^ 4 + 1854 * y ^ 5 - 420 * y ^ 6 -
          900 * y ^ 7 - 315 * y ^ 8 - 35 * y ^ 9) / 1152 := by
    dsimp only [tau, y]
    unfold factorTwoIntrinsicP4Correlation44
    ring
  rw [show factorTwoPrimeShift / yoshidaEndpointA = tau by rfl, hidentity]
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hy5 : 0 ≤ y ^ 5 := by positivity
  norm_num at hy2 hy3 hy6 hy7 hy8 hy9 ⊢
  nlinarith

private theorem abs_poleFreeAnalyticError_correlation44_le :
    |poleFreeAnalyticError factorTwoIntrinsicP4Correlation44| ≤
      (1 / 12000 : ℝ) := by
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4Correlation44
    continuous_factorTwoIntrinsicP4Correlation44
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  simp_rw [centeredEndpointCorrelation_p4] at hcorr
  rw [integral_factorTwoCenteredP4_sq] at hcorr
  have hscaled := mul_le_mul_of_nonneg_left hcorr
    (by norm_num : (0 : ℝ) ≤ 3 / 8000)
  exact herr.trans (by norm_num at hscaled ⊢; linarith)

/-- The complete `P4` symmetric perturbation is strictly below `-17/100`.
The retained `p=3` autocorrelation is kept with its favourable sign. -/
theorem factorTwoIntrinsicP4Perturbation_lt_neg_seventeen_hundredths :
    factorTwoCenteredSymmetricPerturbation factorTwoCenteredP4 <
      (-17 / 100 : ℝ) := by
  have heq := factorTwoIntrinsicP4_perturbation_structural_eq.2.2
  have herr := abs_poleFreeAnalyticError_correlation44_le
  have herrUpper : poleFreeAnalyticError factorTwoIntrinsicP4Correlation44 ≤
      (1 / 12000 : ℝ) := (le_abs_self _).trans herr
  have hlog := strict_log_two_fine_bounds.1
  have hdyadic := log_two_div_sqrt_two_kernel_lower
  have hbeta := log_three_div_sqrt_three_kernel_bounds.1
  have hbetaPos : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hcorr := factorTwoIntrinsicP4PrimeCorrelation44_gt_one_sixteenth
  have hprime :
      (63427 / 100000 : ℝ) * (1 / 16) <
        (Real.log 3 / Real.sqrt 3) *
          factorTwoIntrinsicP4Correlation44
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      (63427 / 100000 : ℝ) * (1 / 16) <
          (Real.log 3 / Real.sqrt 3) * (1 / 16) :=
        mul_lt_mul_of_pos_right hbeta (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          factorTwoIntrinsicP4Correlation44
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_left hcorr hbetaPos
  rw [heq]
  unfold factorTwoIntrinsicP4PerturbationBase44
  nlinarith

/-- A rational diagonal retained by the exact-column Schur lower form. -/
def factorTwoIntrinsicP4MinusDiagonalLower : ℝ := 12 / 25

/-- The structural clean diagonal and the negative perturbation leave a
strict `12/25` reserve. -/
theorem factorTwoIntrinsicP4MinusDiagonalLower_lt_phaseDiagonal :
    factorTwoIntrinsicP4MinusDiagonalLower <
      factorTwoIntrinsicP4PhaseDiagonal (-1) := by
  have hclean :=
    one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have hpert := factorTwoIntrinsicP4Perturbation_lt_neg_seventeen_hundredths
  unfold factorTwoIntrinsicP4MinusDiagonalLower
    factorTwoIntrinsicP4PhaseDiagonal
  norm_num at hclean hpert ⊢
  nlinarith

/-! ## Coarse global control of the two mixed analytic errors -/

private theorem abs_factorTwoCenteredCorrelationBilinear_le_energy_add
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (horth : (∫ x : ℝ in -1..1, u x * v x) = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |factorTwoCenteredCorrelationBilinear u v t| ≤
      (∫ x : ℝ in -1..1, u x ^ 2) +
        ∫ x : ℝ in -1..1, v x ^ 2 := by
  have huI : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2) volume (-1) 1 :=
    (hu.pow 2).intervalIntegrable (-1) 1
  have hvI : IntervalIntegrable (fun x : ℝ ↦ v x ^ 2) volume (-1) 1 :=
    (hv.pow 2).intervalIntegrable (-1) 1
  have huvI : IntervalIntegrable (fun x : ℝ ↦ u x * v x) volume (-1) 1 :=
    (hu.mul hv).intervalIntegrable (-1) 1
  have hsumEnergy :
      (∫ x : ℝ in -1..1, (u + v) x ^ 2) =
        (∫ x : ℝ in -1..1, u x ^ 2) +
          ∫ x : ℝ in -1..1, v x ^ 2 := by
    rw [show (fun x : ℝ ↦ (u + v) x ^ 2) =
        fun x ↦ u x ^ 2 + 2 * (u x * v x) + v x ^ 2 by
      funext x
      simp only [Pi.add_apply]
      ring,
      intervalIntegral.integral_add (huI.add (huvI.const_mul 2)) hvI,
      intervalIntegral.integral_add huI (huvI.const_mul 2),
      intervalIntegral.integral_const_mul, horth]
    ring
  have hplus := abs_centeredEndpointCorrelation_le_energy
    (u + v) (hu.add hv) ht.1 ht.2
  rw [hsumEnergy] at hplus
  have hselfU := abs_centeredEndpointCorrelation_le_energy u hu ht.1 ht.2
  have hselfV := abs_centeredEndpointCorrelation_le_energy v hv ht.1 ht.2
  have hpolar := centeredEndpointCorrelation_add u v hu hv t
  have habs :
      |centeredEndpointCorrelation (u + v) t -
          centeredEndpointCorrelation u t -
          centeredEndpointCorrelation v t| ≤
        |centeredEndpointCorrelation (u + v) t| +
          |centeredEndpointCorrelation u t| +
          |centeredEndpointCorrelation v t| := by
    calc
      _ ≤ |centeredEndpointCorrelation (u + v) t -
            centeredEndpointCorrelation u t| +
          |centeredEndpointCorrelation v t| := abs_sub _ _
      _ ≤ (|centeredEndpointCorrelation (u + v) t| +
            |centeredEndpointCorrelation u t|) +
          |centeredEndpointCorrelation v t| :=
        add_le_add (abs_sub _ _) le_rfl
      _ = _ := by ring
  have hidentity :
      factorTwoCenteredCorrelationBilinear u v t =
        (centeredEndpointCorrelation (u + v) t -
          centeredEndpointCorrelation u t -
          centeredEndpointCorrelation v t) / 2 := by
    linarith
  rw [hidentity, abs_div]
  norm_num
  nlinarith

private theorem integral_abs_factorTwoIntrinsicP4Correlation04_le :
    (∫ t : ℝ in 0..2, |factorTwoIntrinsicP4Correlation04 t|) ≤
      (40 / 9 : ℝ) := by
  have hcont := continuous_factorTwoIntrinsicP4Correlation04.abs
  have hbound : ∀ t ∈ Icc (0 : ℝ) 2,
      |factorTwoIntrinsicP4Correlation04 t| ≤ (20 / 9 : ℝ) := by
    intro t ht
    rw [← factorTwoCenteredCorrelationBilinear_p0_p4]
    have h := abs_factorTwoCenteredCorrelationBilinear_le_energy_add
      centeredEvenP0 factorTwoCenteredP4
      (by unfold centeredEvenP0; fun_prop)
      continuous_factorTwoCenteredP4
      (by simpa only [centeredEvenP0, one_mul] using
        integral_factorTwoCenteredP4) ht
    rw [show (∫ x : ℝ in -1..1, centeredEvenP0 x ^ 2) = 2 by
      unfold centeredEvenP0
      norm_num,
      integral_factorTwoCenteredP4_sq] at h
    norm_num at h ⊢
    exact h
  calc
    (∫ t : ℝ in 0..2, |factorTwoIntrinsicP4Correlation04 t|) ≤
        ∫ _t : ℝ in 0..2, (20 / 9 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hcont.intervalIntegrable 0 2)
        (continuous_const.intervalIntegrable 0 2)
      exact hbound
    _ = (40 / 9 : ℝ) := by norm_num

private theorem integral_abs_factorTwoIntrinsicP4Correlation24_le :
    (∫ t : ℝ in 0..2, |factorTwoIntrinsicP4Correlation24 t|) ≤
      (56 / 45 : ℝ) := by
  have hcont := continuous_factorTwoIntrinsicP4Correlation24.abs
  have hbound : ∀ t ∈ Icc (0 : ℝ) 2,
      |factorTwoIntrinsicP4Correlation24 t| ≤ (28 / 45 : ℝ) := by
    intro t ht
    rw [← factorTwoCenteredCorrelationBilinear_p2_p4]
    have h := abs_factorTwoCenteredCorrelationBilinear_le_energy_add
      centeredEvenP2 factorTwoCenteredP4
      (by unfold centeredEvenP2; fun_prop)
      continuous_factorTwoCenteredP4
      (by simpa only [mul_comm] using
        integral_factorTwoCenteredP4_mul_centeredEvenP2) ht
    rw [integral_centeredEvenP2_sq,
      integral_factorTwoCenteredP4_sq] at h
    norm_num at h ⊢
    exact h
  calc
    (∫ t : ℝ in 0..2, |factorTwoIntrinsicP4Correlation24 t|) ≤
        ∫ _t : ℝ in 0..2, (28 / 45 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hcont.intervalIntegrable 0 2)
        (continuous_const.intervalIntegrable 0 2)
      exact hbound
    _ = (56 / 45 : ℝ) := by norm_num

private theorem abs_poleFreeAnalyticError_correlation04_le :
    |poleFreeAnalyticError factorTwoIntrinsicP4Correlation04| ≤
      (1 / 600 : ℝ) := by
  exact (abs_poleFreeAnalyticError_le _
    continuous_factorTwoIntrinsicP4Correlation04).trans <| by
      have h := integral_abs_factorTwoIntrinsicP4Correlation04_le
      nlinarith

private theorem abs_poleFreeAnalyticError_correlation24_le :
    |poleFreeAnalyticError factorTwoIntrinsicP4Correlation24| ≤
      (7 / 15000 : ℝ) := by
  exact (abs_poleFreeAnalyticError_le _
    continuous_factorTwoIntrinsicP4Correlation24).trans <| by
      have h := integral_abs_factorTwoIntrinsicP4Correlation24_le
      nlinarith

private theorem factorTwoIntrinsicP4PolynomialCorrections_bounds :
    0 ≤ poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
          poleFreeCoeff6 yoshidaEndpointA * (32 / 99 + 32 / 315) ∧
      poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
          poleFreeCoeff6 yoshidaEndpointA * (32 / 99 + 32 / 315) <
        (1 / 10000 : ℝ) ∧
      0 ≤ poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
          poleFreeCoeff6 yoshidaEndpointA * (32 / 99 - 32 / 315) ∧
      poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
          poleFreeCoeff6 yoshidaEndpointA * (32 / 99 - 32 / 315) <
        (1 / 10000 : ℝ) := by
  have hA0 : 0 < yoshidaEndpointA := yoshidaEndpointA_pos
  have hA : yoshidaEndpointA < (347 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.2]
  have hA5 := pow_lt_pow_left₀ hA hA0.le
    (by norm_num : (5 : ℕ) ≠ 0)
  have hA6 := pow_lt_pow_left₀ hA hA0.le
    (by norm_num : (6 : ℕ) ≠ 0)
  have hA7 := pow_lt_pow_left₀ hA hA0.le
    (by norm_num : (7 : ℕ) ≠ 0)
  have hc4 : 0 ≤ poleFreeCoeff4 yoshidaEndpointA := by
    unfold poleFreeCoeff4
    positivity
  have hc6 : 0 ≤ poleFreeCoeff6 yoshidaEndpointA := by
    unfold poleFreeCoeff6
    positivity
  constructor
  · positivity
  constructor
  · unfold poleFreeCoeff4 poleFreeCoeff6
    norm_num at hA5 hA6 hA7 ⊢
    nlinarith
  constructor
  · positivity
  · unfold poleFreeCoeff4 poleFreeCoeff6
    norm_num at hA5 hA6 hA7 ⊢
    nlinarith

/-- Sum coordinate of the genuine negative-endpoint `P4` column. -/
def factorTwoIntrinsicP4MinusCrossSum : ℝ :=
  factorTwoIntrinsicFourP45Cross04 (-1) +
    factorTwoIntrinsicFourP45Cross24 (-1)

/-- Difference coordinate, oriented as `P2-P0`. -/
def factorTwoIntrinsicP4MinusCrossDifference : ℝ :=
  factorTwoIntrinsicFourP45Cross24 (-1) -
    factorTwoIntrinsicFourP45Cross04 (-1)

/-- Positive structural boxes for the two combined signed cross coordinates.
They retain the prime cancellation and use no subdivision or quadrature. -/
theorem factorTwoIntrinsicP4MinusCross_sum_difference_bounds :
    0 < factorTwoIntrinsicP4MinusCrossSum ∧
      factorTwoIntrinsicP4MinusCrossSum < (3 / 10 : ℝ) ∧
      0 < factorTwoIntrinsicP4MinusCrossDifference ∧
      factorTwoIntrinsicP4MinusCrossDifference < (7 / 100 : ℝ) := by
  let e04 : ℝ := poleFreeAnalyticError factorTwoIntrinsicP4Correlation04
  let e24 : ℝ := poleFreeAnalyticError factorTwoIntrinsicP4Correlation24
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let cs : ℝ := factorTwoIntrinsicP4CorrelationSum
    (factorTwoPrimeShift / yoshidaEndpointA)
  let cd : ℝ := factorTwoIntrinsicP4CorrelationDifference
    (factorTwoPrimeShift / yoshidaEndpointA)
  let pSum : ℝ := poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
    poleFreeCoeff6 yoshidaEndpointA * (32 / 99 + 32 / 315)
  let pDiff : ℝ := poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
    poleFreeCoeff6 yoshidaEndpointA * (32 / 99 - 32 / 315)
  have hcleanS :=
    factorTwoIntrinsicP4CleanCross_sum_sub_seventeen_seventieths_abs_lt
  have hcleanD :=
    factorTwoIntrinsicP4CleanCross_difference_sub_three_seventieths_abs_lt
  rw [abs_lt] at hcleanS hcleanD
  have he04 := abs_poleFreeAnalyticError_correlation04_le
  have he24 := abs_poleFreeAnalyticError_correlation24_le
  have he04B : -(1 / 600 : ℝ) ≤ e04 ∧ e04 ≤ 1 / 600 := by
    simpa only [e04] using abs_le.mp he04
  have he24B : -(7 / 15000 : ℝ) ≤ e24 ∧ e24 ≤ 7 / 15000 := by
    simpa only [e24] using abs_le.mp he24
  rcases factorTwoIntrinsicP4PolynomialCorrections_bounds with
    ⟨hpSum0', hpSumU', hpDiff0', hpDiffU'⟩
  have hpSum0 : 0 ≤ pSum := by
    simpa only [pSum] using hpSum0'
  have hpSumU : pSum < (1 / 10000 : ℝ) := by
    simpa only [pSum] using hpSumU'
  have hpDiff0 : 0 ≤ pDiff := by
    simpa only [pDiff] using hpDiff0'
  have hpDiffU : pDiff < (1 / 10000 : ℝ) := by
    simpa only [pDiff] using hpDiffU'
  have hlog := strict_log_two_fine_bounds
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hbetaPos : 0 < beta := by
    dsimp only [beta]
    positivity
  have hprime := factorTwoIntrinsicP4PrimeCorrelation_sum_difference_bounds
  have hcsL : (-29337 / 500000 : ℝ) < cs := by
    simpa only [cs] using hprime.1
  have hcsU : cs < (-29333 / 500000 : ℝ) := by
    simpa only [cs] using hprime.2.1
  have hcdL : (56755 / 1000000 : ℝ) < cd := by
    simpa only [cd] using hprime.2.2.1
  have hcdU : cd < (56757 / 1000000 : ℝ) := by
    simpa only [cd] using hprime.2.2.2
  have hbetaL : (63427 / 100000 : ℝ) < beta := by
    simpa only [beta] using hbeta.1
  have hbetaU : beta < (6343 / 10000 : ℝ) := by
    simpa only [beta] using hbeta.2
  have hbetaCsL :
      (6343 / 10000 : ℝ) * (-29337 / 500000) < beta * cs := by
    calc
      (6343 / 10000 : ℝ) * (-29337 / 500000) <
          beta * (-29337 / 500000) :=
        mul_lt_mul_of_neg_right hbetaU (by norm_num)
      _ < beta * cs := mul_lt_mul_of_pos_left hcsL hbetaPos
  have hbetaCsU :
      beta * cs <
        (63427 / 100000 : ℝ) * (-29333 / 500000) := by
    calc
      beta * cs < beta * (-29333 / 500000) :=
        mul_lt_mul_of_pos_left hcsU hbetaPos
      _ < (63427 / 100000 : ℝ) * (-29333 / 500000) :=
        mul_lt_mul_of_neg_right hbetaL (by norm_num)
  have hbetaCdL :
      (63427 / 100000 : ℝ) * (56755 / 1000000) < beta * cd := by
    calc
      (63427 / 100000 : ℝ) * (56755 / 1000000) <
          beta * (56755 / 1000000) :=
        mul_lt_mul_of_pos_right hbetaL (by norm_num)
      _ < beta * cd := mul_lt_mul_of_pos_left hcdL hbetaPos
  have hbetaCdU :
      beta * cd < (6343 / 10000 : ℝ) * (56757 / 1000000) := by
    calc
      beta * cd < beta * (56757 / 1000000) :=
        mul_lt_mul_of_pos_left hcdU hbetaPos
      _ < (6343 / 10000 : ℝ) * (56757 / 1000000) :=
        mul_lt_mul_of_pos_right hbetaU (by norm_num)
  rcases factorTwoIntrinsicP4_perturbation_structural_eq with
    ⟨h04, h24, _h44⟩
  have hS : factorTwoIntrinsicP4MinusCrossSum =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
          yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4) -
        (e04 + e24) - pSum - 72 + 104 * Real.log 2 + beta * cs := by
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    rw [h04, h24]
    dsimp only [e04, e24, pSum, beta, cs,
      factorTwoIntrinsicP4CorrelationSum]
    unfold factorTwoIntrinsicP4PerturbationBase04
      factorTwoIntrinsicP4PerturbationBase24
    ring
  have hD : factorTwoIntrinsicP4MinusCrossDifference =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
          yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4) -
        (e24 - e04) + pDiff + 158 / 3 - 76 * Real.log 2 + beta * cd := by
    unfold factorTwoIntrinsicP4MinusCrossDifference
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    rw [h04, h24]
    dsimp only [e04, e24, pDiff, beta, cd,
      factorTwoIntrinsicP4CorrelationDifference]
    unfold factorTwoIntrinsicP4PerturbationBase04
      factorTwoIntrinsicP4PerturbationBase24
    ring
  constructor
  · rw [hS]
    linarith
  constructor
  · rw [hS]
    linarith
  constructor
  · rw [hD]
    linarith
  · rw [hD]
    linarith

/-- Absolute-value form of the structural cross-coordinate boxes. -/
theorem factorTwoIntrinsicP4MinusCross_sum_difference_abs_bounds :
    |factorTwoIntrinsicP4MinusCrossSum| < (3 / 10 : ℝ) ∧
      |factorTwoIntrinsicP4MinusCrossDifference| < (7 / 100 : ℝ) := by
  rcases factorTwoIntrinsicP4MinusCross_sum_difference_bounds with
    ⟨hS0, hSU, hD0, hDU⟩
  rw [abs_of_pos hS0, abs_of_pos hD0]
  exact ⟨hSU, hDU⟩

/-- Rational low block with the genuine signed `P4` column and a structural
diagonal reserve. -/
def factorTwoIntrinsicP024MinusLowerQuadratic
    (c0 c2 c4 : ℝ) : ℝ :=
  symmetricQuadratic
    intrinsicStaticMinusEvenLower00
    intrinsicStaticMinusEvenLower02
    (factorTwoIntrinsicFourP45Cross04 (-1))
    intrinsicStaticMinusEvenLower22
    (factorTwoIntrinsicFourP45Cross24 (-1))
    factorTwoIntrinsicP4MinusDiagonalLower c0 c2 c4

theorem factorTwoIntrinsicP024MinusLowerQuadratic_le_exact
    (c0 c2 c4 : ℝ) :
    factorTwoIntrinsicP024MinusLowerQuadratic c0 c2 c4 ≤
      symmetricQuadratic
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicP4PhaseDiagonal (-1)) c0 c2 c4 := by
  have hlow := intrinsicStaticMinusEvenLower_le c0 c2
  unfold factorTwoIntrinsicStaticEvenQuadratic at hlow
  unfold intrinsicStaticMinusEvenLower at hlow
  unfold factorTwoIntrinsicP024MinusLowerQuadratic symmetricQuadratic
  have hdiag := factorTwoIntrinsicP4MinusDiagonalLower_lt_phaseDiagonal.le
  have hdiagScaled := mul_le_mul_of_nonneg_right hdiag (sq_nonneg c4)
  nlinarith

/-- The low-block adjugate in the positive sum/difference coordinates of the
genuine negative-endpoint `P4` column. -/
theorem factorTwoIntrinsicP4MinusAdjugate_eq_sum_difference :
    intrinsicStaticMinusEvenLower22 *
          factorTwoIntrinsicFourP45Cross04 (-1) ^ 2 -
        2 * intrinsicStaticMinusEvenLower02 *
          factorTwoIntrinsicFourP45Cross04 (-1) *
          factorTwoIntrinsicFourP45Cross24 (-1) +
        intrinsicStaticMinusEvenLower00 *
          factorTwoIntrinsicFourP45Cross24 (-1) ^ 2 =
      ((intrinsicStaticMinusEvenLower00 +
              intrinsicStaticMinusEvenLower22 -
            2 * intrinsicStaticMinusEvenLower02) / 4) *
          factorTwoIntrinsicP4MinusCrossSum ^ 2 +
        ((intrinsicStaticMinusEvenLower00 -
              intrinsicStaticMinusEvenLower22) / 2) *
          factorTwoIntrinsicP4MinusCrossSum *
          factorTwoIntrinsicP4MinusCrossDifference +
        ((intrinsicStaticMinusEvenLower00 +
              intrinsicStaticMinusEvenLower22 +
            2 * intrinsicStaticMinusEvenLower02) / 4) *
          factorTwoIntrinsicP4MinusCrossDifference ^ 2 := by
  unfold factorTwoIntrinsicP4MinusCrossSum
    factorTwoIntrinsicP4MinusCrossDifference
  ring

/-- The structural cross-coordinate boxes fit strictly inside the exact
rational low-block adjugate budget. -/
theorem factorTwoIntrinsicP4MinusAdjugate_lt :
    intrinsicStaticMinusEvenLower22 *
          factorTwoIntrinsicFourP45Cross04 (-1) ^ 2 -
        2 * intrinsicStaticMinusEvenLower02 *
          factorTwoIntrinsicFourP45Cross04 (-1) *
          factorTwoIntrinsicFourP45Cross24 (-1) +
        intrinsicStaticMinusEvenLower00 *
          factorTwoIntrinsicFourP45Cross24 (-1) ^ 2 <
      (intrinsicStaticMinusEvenLower00 *
          intrinsicStaticMinusEvenLower22 -
        intrinsicStaticMinusEvenLower02 ^ 2) *
          factorTwoIntrinsicP4MinusDiagonalLower := by
  let S : ℝ := factorTwoIntrinsicP4MinusCrossSum
  let D : ℝ := factorTwoIntrinsicP4MinusCrossDifference
  have h := factorTwoIntrinsicP4MinusCross_sum_difference_bounds
  have hS : 0 < S ∧ S < (3 / 10 : ℝ) := by
    simpa only [S] using ⟨h.1, h.2.1⟩
  have hD : 0 < D ∧ D < (7 / 100 : ℝ) := by
    simpa only [D] using ⟨h.2.2.1, h.2.2.2⟩
  have hSsq : S ^ 2 < (3 / 10 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hS.2 hS.1.le (by norm_num)
  have hDsq : D ^ 2 < (7 / 100 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hD.2 hD.1.le (by norm_num)
  have hSD : S * D < (3 / 10 : ℝ) * (7 / 100 : ℝ) := by
    calc
      S * D < (3 / 10 : ℝ) * D :=
        mul_lt_mul_of_pos_right hS.2 hD.1
      _ < (3 / 10 : ℝ) * (7 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left hD.2 (by norm_num)
  rw [factorTwoIntrinsicP4MinusAdjugate_eq_sum_difference]
  dsimp only [S, D] at hSsq hDsq hSD ⊢
  unfold intrinsicStaticMinusEvenLower00
    intrinsicStaticMinusEvenLower02 intrinsicStaticMinusEvenLower22
    factorTwoIntrinsicP4MinusDiagonalLower
  nlinarith

/-- One exact adjugate inequality closes the negative endpoint. -/
theorem factorTwoIntrinsicSixP4SchurLeading_minus_pos_of_adjugate
    (hadj :
      intrinsicStaticMinusEvenLower22 *
            factorTwoIntrinsicFourP45Cross04 (-1) ^ 2 -
          2 * intrinsicStaticMinusEvenLower02 *
            factorTwoIntrinsicFourP45Cross04 (-1) *
            factorTwoIntrinsicFourP45Cross24 (-1) +
          intrinsicStaticMinusEvenLower00 *
            factorTwoIntrinsicFourP45Cross24 (-1) ^ 2 <
        (intrinsicStaticMinusEvenLower00 *
            intrinsicStaticMinusEvenLower22 -
          intrinsicStaticMinusEvenLower02 ^ 2) *
            factorTwoIntrinsicP4MinusDiagonalLower) :
    0 < factorTwoIntrinsicSixP4SchurLeading (-1) := by
  rcases intrinsicStaticMinusEvenLower_principal_minors_pos with
    ⟨h00, hminor⟩
  have hdet : 0 < symmetricDeterminant
      intrinsicStaticMinusEvenLower00
      intrinsicStaticMinusEvenLower02
      (factorTwoIntrinsicFourP45Cross04 (-1))
      intrinsicStaticMinusEvenLower22
      (factorTwoIntrinsicFourP45Cross24 (-1))
      factorTwoIntrinsicP4MinusDiagonalLower := by
    unfold symmetricDeterminant
    nlinarith
  apply factorTwoIntrinsicSixP4SchurLeading_pos_of_profile_pos (-1)
  intro c0 c2 c4 hne
  rw [factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic]
  have hlower : 0 <
      factorTwoIntrinsicP024MinusLowerQuadratic c0 c2 c4 := by
    exact symmetricQuadratic_pos
      intrinsicStaticMinusEvenLower00
      intrinsicStaticMinusEvenLower02
      (factorTwoIntrinsicFourP45Cross04 (-1))
      intrinsicStaticMinusEvenLower22
      (factorTwoIntrinsicFourP45Cross24 (-1))
      factorTwoIntrinsicP4MinusDiagonalLower h00 hminor hdet c0 c2 c4 hne
  exact hlower.trans_le
    (factorTwoIntrinsicP024MinusLowerQuadratic_le_exact c0 c2 c4)

/-- Unconditional structural positivity of the negative-endpoint intrinsic
`P0/P2/P4` Schur leading coefficient. -/
theorem factorTwoIntrinsicSixP4SchurLeading_minus_pos :
    0 < factorTwoIntrinsicSixP4SchurLeading (-1) := by
  exact factorTwoIntrinsicSixP4SchurLeading_minus_pos_of_adjugate
    factorTwoIntrinsicP4MinusAdjugate_lt

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
