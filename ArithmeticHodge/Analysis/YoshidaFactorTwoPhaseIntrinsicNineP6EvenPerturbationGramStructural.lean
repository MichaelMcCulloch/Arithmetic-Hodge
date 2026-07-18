import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenEndpointLowerModelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationGramStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenEndpointLowerModelStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
open Matrix
open scoped BigOperators

/-!
# Exact perturbation Gram on the intrinsic `P0/P2/P4/P6` plane

The four perturbation pieces are kept separate: the compiled degree-six
kernel, the reflected Cauchy pole, and the retained atoms at `p = 2` and
`p = 3`.  Every integral in this file is symbolic.  The only transcendental
quantities left in the resulting matrix are the constants already enclosed
elsewhere (`log 2`, `log 3`, `sqrt 2`, `sqrt 3`, and the prime height).
-/

private theorem integral_polynomial_twelve
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
        a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 + a₁₁ * x ^ 11 +
        a₁₂ * x ^ 12) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 +
        a₁₂ * (r ^ 13 - l ^ 13) / 13 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_inv_two_add :
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

private theorem intervalIntegrable_inv_two_add :
    IntervalIntegrable (fun t : ℝ ↦ 1 / (2 + t)) volume 0 2 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have hne : 2 + t ≠ 0 := by linarith [ht'.1]
  exact (continuousAt_const.div
    (continuousAt_const.add continuousAt_id) hne).continuousWithinAt

/-! ## The new reflected-pole row -/

/-- Exact reflected-pole entries involving `P6`.  Polynomial division by
`2 + t` is displayed in the proof; no sampled evaluation is used. -/
theorem integral_poleWeight_mul_factorTwoIntrinsicP6Correlations :
    (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation06 t) =
        6259 / 5 - 1806 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation26 t) =
        2071 / 6 - 498 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation46 t) =
        457 / 30 - 22 * Real.log 2 ∧
      (∫ t : ℝ in 0..2,
        evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation66 t) =
        37 / 390 - (2 / 13 : ℝ) * Real.log 2 := by
  have h06 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation06 t) =
      ∫ t : ℝ in 0..2,
        (903 - 451 * t + (441 / 2 : ℝ) * t ^ 2 -
          (381 / 4 : ℝ) * t ^ 3 + (231 / 8 : ℝ) * t ^ 4 -
          (33 / 8 : ℝ) * t ^ 5) - 1806 / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight factorTwoIntrinsicP6Correlation06
    field_simp [hp, hm]
    ring
  have h26 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation26 t) =
      ∫ t : ℝ in 0..2,
        (249 - 124 * t + (231 / 4 : ℝ) * t ^ 2 -
          (37 / 2 : ℝ) * t ^ 3 + (31 / 16 : ℝ) * t ^ 5 -
          (11 / 64 : ℝ) * t ^ 7) - 498 / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight factorTwoIntrinsicP6Correlation26
    field_simp [hp, hm]
    ring
  have h46 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation46 t) =
      ∫ t : ℝ in 0..2,
        (11 - 5 * t + (5 / 2 : ℝ) * t ^ 3 -
          (25 / 16 : ℝ) * t ^ 5 + (31 / 64 : ℝ) * t ^ 7 -
          (7 / 128 : ℝ) * t ^ 9) - 22 / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight factorTwoIntrinsicP6Correlation46
    field_simp [hp, hm]
    ring
  have h66 : (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation66 t) =
      ∫ t : ℝ in 0..2,
        ((6 / 13 : ℝ) * t - (85 / 52 : ℝ) * t ^ 3 +
          (461 / 208 : ℝ) * t ^ 5 - (1099 / 832 : ℝ) * t ^ 7 +
          (147 / 416 : ℝ) * t ^ 9 - (231 / 6656 : ℝ) * t ^ 11) -
          (2 / 13 : ℝ) / (2 + t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-2 : ℝ)] with t ht2 htneg2
    intro _ht
    have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
    have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
    unfold evenStructuralPoleWeight factorTwoIntrinsicP6Correlation66
    field_simp [hp, hm]
    ring
  rw [h06, h26, h46, h66]
  have hp06 : IntervalIntegrable
      (fun t : ℝ ↦ 903 - 451 * t + (441 / 2 : ℝ) * t ^ 2 -
        (381 / 4 : ℝ) * t ^ 3 + (231 / 8 : ℝ) * t ^ 4 -
        (33 / 8 : ℝ) * t ^ 5) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      903 - 451 * t + (441 / 2 : ℝ) * t ^ 2 -
        (381 / 4 : ℝ) * t ^ 3 + (231 / 8 : ℝ) * t ^ 4 -
        (33 / 8 : ℝ) * t ^ 5)) |>.intervalIntegrable 0 2
  have hp26 : IntervalIntegrable
      (fun t : ℝ ↦ 249 - 124 * t + (231 / 4 : ℝ) * t ^ 2 -
        (37 / 2 : ℝ) * t ^ 3 + (31 / 16 : ℝ) * t ^ 5 -
        (11 / 64 : ℝ) * t ^ 7) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      249 - 124 * t + (231 / 4 : ℝ) * t ^ 2 -
        (37 / 2 : ℝ) * t ^ 3 + (31 / 16 : ℝ) * t ^ 5 -
        (11 / 64 : ℝ) * t ^ 7)) |>.intervalIntegrable 0 2
  have hp46 : IntervalIntegrable
      (fun t : ℝ ↦ 11 - 5 * t + (5 / 2 : ℝ) * t ^ 3 -
        (25 / 16 : ℝ) * t ^ 5 + (31 / 64 : ℝ) * t ^ 7 -
        (7 / 128 : ℝ) * t ^ 9) volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      11 - 5 * t + (5 / 2 : ℝ) * t ^ 3 -
        (25 / 16 : ℝ) * t ^ 5 + (31 / 64 : ℝ) * t ^ 7 -
        (7 / 128 : ℝ) * t ^ 9)) |>.intervalIntegrable 0 2
  have hp66 : IntervalIntegrable
      (fun t : ℝ ↦ (6 / 13 : ℝ) * t - (85 / 52 : ℝ) * t ^ 3 +
        (461 / 208 : ℝ) * t ^ 5 - (1099 / 832 : ℝ) * t ^ 7 +
        (147 / 416 : ℝ) * t ^ 9 - (231 / 6656 : ℝ) * t ^ 11)
      volume 0 2 :=
    (by fun_prop : Continuous (fun t : ℝ ↦
      (6 / 13 : ℝ) * t - (85 / 52 : ℝ) * t ^ 3 +
        (461 / 208 : ℝ) * t ^ 5 - (1099 / 832 : ℝ) * t ^ 7 +
        (147 / 416 : ℝ) * t ^ 9 - (231 / 6656 : ℝ) * t ^ 11))
      |>.intervalIntegrable 0 2
  constructor
  · rw [show (fun t : ℝ ↦
        (903 - 451 * t + (441 / 2 : ℝ) * t ^ 2 -
          (381 / 4 : ℝ) * t ^ 3 + (231 / 8 : ℝ) * t ^ 4 -
          (33 / 8 : ℝ) * t ^ 5) - 1806 / (2 + t)) =
      fun t ↦
        (903 - 451 * t + (441 / 2 : ℝ) * t ^ 2 -
          (381 / 4 : ℝ) * t ^ 3 + (231 / 8 : ℝ) * t ^ 4 -
          (33 / 8 : ℝ) * t ^ 5) - 1806 * (1 / (2 + t)) by
        funext t; ring,
      intervalIntegral.integral_sub hp06
        (intervalIntegrable_inv_two_add.const_mul 1806),
      intervalIntegral.integral_const_mul, integral_inv_two_add]
    rw [show (fun t : ℝ ↦
        903 - 451 * t + (441 / 2 : ℝ) * t ^ 2 -
          (381 / 4 : ℝ) * t ^ 3 + (231 / 8 : ℝ) * t ^ 4 -
          (33 / 8 : ℝ) * t ^ 5) =
      fun t ↦
        903 * t ^ 0 + (-451 : ℝ) * t ^ 1 + (441 / 2 : ℝ) * t ^ 2 +
          (-381 / 4 : ℝ) * t ^ 3 + (231 / 8 : ℝ) * t ^ 4 +
          (-33 / 8 : ℝ) * t ^ 5 + 0 * t ^ 6 + 0 * t ^ 7 +
          0 * t ^ 8 + 0 * t ^ 9 + 0 * t ^ 10 + 0 * t ^ 11 + 0 * t ^ 12 by
        funext t; ring, integral_polynomial_twelve]
    norm_num
  · constructor
    · rw [show (fun t : ℝ ↦
          (249 - 124 * t + (231 / 4 : ℝ) * t ^ 2 -
            (37 / 2 : ℝ) * t ^ 3 + (31 / 16 : ℝ) * t ^ 5 -
            (11 / 64 : ℝ) * t ^ 7) - 498 / (2 + t)) =
        fun t ↦
          (249 - 124 * t + (231 / 4 : ℝ) * t ^ 2 -
            (37 / 2 : ℝ) * t ^ 3 + (31 / 16 : ℝ) * t ^ 5 -
            (11 / 64 : ℝ) * t ^ 7) - 498 * (1 / (2 + t)) by
          funext t; ring,
        intervalIntegral.integral_sub hp26
          (intervalIntegrable_inv_two_add.const_mul 498),
        intervalIntegral.integral_const_mul, integral_inv_two_add]
      rw [show (fun t : ℝ ↦
          249 - 124 * t + (231 / 4 : ℝ) * t ^ 2 -
            (37 / 2 : ℝ) * t ^ 3 + (31 / 16 : ℝ) * t ^ 5 -
            (11 / 64 : ℝ) * t ^ 7) =
        fun t ↦
          249 * t ^ 0 + (-124 : ℝ) * t ^ 1 + (231 / 4 : ℝ) * t ^ 2 +
            (-37 / 2 : ℝ) * t ^ 3 + 0 * t ^ 4 +
            (31 / 16 : ℝ) * t ^ 5 + 0 * t ^ 6 +
            (-11 / 64 : ℝ) * t ^ 7 + 0 * t ^ 8 + 0 * t ^ 9 +
            0 * t ^ 10 + 0 * t ^ 11 + 0 * t ^ 12 by
          funext t; ring, integral_polynomial_twelve]
      norm_num
    · constructor
      · rw [show (fun t : ℝ ↦
            (11 - 5 * t + (5 / 2 : ℝ) * t ^ 3 -
              (25 / 16 : ℝ) * t ^ 5 + (31 / 64 : ℝ) * t ^ 7 -
              (7 / 128 : ℝ) * t ^ 9) - 22 / (2 + t)) =
          fun t ↦
            (11 - 5 * t + (5 / 2 : ℝ) * t ^ 3 -
              (25 / 16 : ℝ) * t ^ 5 + (31 / 64 : ℝ) * t ^ 7 -
              (7 / 128 : ℝ) * t ^ 9) - 22 * (1 / (2 + t)) by
            funext t; ring,
          intervalIntegral.integral_sub hp46
            (intervalIntegrable_inv_two_add.const_mul 22),
          intervalIntegral.integral_const_mul, integral_inv_two_add]
        rw [show (fun t : ℝ ↦
            11 - 5 * t + (5 / 2 : ℝ) * t ^ 3 -
              (25 / 16 : ℝ) * t ^ 5 + (31 / 64 : ℝ) * t ^ 7 -
              (7 / 128 : ℝ) * t ^ 9) =
          fun t ↦
            11 * t ^ 0 + (-5 : ℝ) * t ^ 1 + 0 * t ^ 2 +
              (5 / 2 : ℝ) * t ^ 3 + 0 * t ^ 4 +
              (-25 / 16 : ℝ) * t ^ 5 + 0 * t ^ 6 +
              (31 / 64 : ℝ) * t ^ 7 + 0 * t ^ 8 +
              (-7 / 128 : ℝ) * t ^ 9 + 0 * t ^ 10 +
              0 * t ^ 11 + 0 * t ^ 12 by
            funext t; ring, integral_polynomial_twelve]
        norm_num
      · rw [show (fun t : ℝ ↦
            ((6 / 13 : ℝ) * t - (85 / 52 : ℝ) * t ^ 3 +
              (461 / 208 : ℝ) * t ^ 5 - (1099 / 832 : ℝ) * t ^ 7 +
              (147 / 416 : ℝ) * t ^ 9 - (231 / 6656 : ℝ) * t ^ 11) -
              (2 / 13 : ℝ) / (2 + t)) =
          fun t ↦
            ((6 / 13 : ℝ) * t - (85 / 52 : ℝ) * t ^ 3 +
              (461 / 208 : ℝ) * t ^ 5 - (1099 / 832 : ℝ) * t ^ 7 +
              (147 / 416 : ℝ) * t ^ 9 - (231 / 6656 : ℝ) * t ^ 11) -
              (2 / 13 : ℝ) * (1 / (2 + t)) by
            funext t; ring,
          intervalIntegral.integral_sub hp66
            (intervalIntegrable_inv_two_add.const_mul (2 / 13 : ℝ)),
          intervalIntegral.integral_const_mul, integral_inv_two_add]
        rw [show (fun t : ℝ ↦
            (6 / 13 : ℝ) * t - (85 / 52 : ℝ) * t ^ 3 +
              (461 / 208 : ℝ) * t ^ 5 - (1099 / 832 : ℝ) * t ^ 7 +
              (147 / 416 : ℝ) * t ^ 9 - (231 / 6656 : ℝ) * t ^ 11) =
          fun t ↦
            0 * t ^ 0 + (6 / 13 : ℝ) * t ^ 1 + 0 * t ^ 2 +
              (-85 / 52 : ℝ) * t ^ 3 + 0 * t ^ 4 +
              (461 / 208 : ℝ) * t ^ 5 + 0 * t ^ 6 +
              (-1099 / 832 : ℝ) * t ^ 7 + 0 * t ^ 8 +
              (147 / 416 : ℝ) * t ^ 9 + 0 * t ^ 10 +
              (-231 / 6656 : ℝ) * t ^ 11 + 0 * t ^ 12 by
            funext t; ring, integral_polynomial_twelve]
        norm_num

private theorem intervalIntegrable_pole_mul_factor
    (P : ℝ → ℝ) (hP : Continuous P) :
    IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * ((t - 2) * P t))
      volume 0 2 := by
  have hbase : IntervalIntegrable (fun t : ℝ ↦ 2 * P t / (2 + t))
      volume 0 2 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    have hne : 2 + t ≠ 0 := by linarith [ht'.1]
    exact ((continuousAt_const.mul hP.continuousAt).div
      (continuousAt_const.add continuousAt_id) hne).continuousWithinAt
  apply hbase.congr_ae
  filter_upwards [
    (MeasureTheory.Measure.ae_ne volume (2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self),
    (MeasureTheory.Measure.ae_ne volume (-2 : ℝ)).filter_mono
      (ae_mono Measure.restrict_le_self)] with t ht2 htneg2
  have hp : 2 + t ≠ 0 := by intro h; apply htneg2; linarith
  have hm : 2 - t ≠ 0 := by intro h; apply ht2; linarith
  unfold evenStructuralPoleWeight
  field_simp [hp, hm]
  ring

private theorem intervalIntegrable_pole_mul_of_eq_factor
    (C P : ℝ → ℝ) (hP : Continuous P)
    (hfactor : ∀ t, C t = (t - 2) * P t) :
    IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * C t) volume 0 2 := by
  apply (intervalIntegrable_pole_mul_factor P hP).congr
  intro t _ht
  dsimp only
  rw [hfactor t]

private theorem integral_ten_add
    (f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : ℝ → ℝ)
    (h₀ : IntervalIntegrable f₀ volume 0 2)
    (h₁ : IntervalIntegrable f₁ volume 0 2)
    (h₂ : IntervalIntegrable f₂ volume 0 2)
    (h₃ : IntervalIntegrable f₃ volume 0 2)
    (h₄ : IntervalIntegrable f₄ volume 0 2)
    (h₅ : IntervalIntegrable f₅ volume 0 2)
    (h₆ : IntervalIntegrable f₆ volume 0 2)
    (h₇ : IntervalIntegrable f₇ volume 0 2)
    (h₈ : IntervalIntegrable f₈ volume 0 2)
    (h₉ : IntervalIntegrable f₉ volume 0 2) :
    (∫ t : ℝ in 0..2,
      f₀ t + (f₁ t + (f₂ t + (f₃ t + (f₄ t +
        (f₅ t + (f₆ t + (f₇ t + (f₈ t + f₉ t))))))))) =
      (∫ t : ℝ in 0..2, f₀ t) +
        ((∫ t : ℝ in 0..2, f₁ t) +
          ((∫ t : ℝ in 0..2, f₂ t) +
            ((∫ t : ℝ in 0..2, f₃ t) +
              ((∫ t : ℝ in 0..2, f₄ t) +
                ((∫ t : ℝ in 0..2, f₅ t) +
                  ((∫ t : ℝ in 0..2, f₆ t) +
                    ((∫ t : ℝ in 0..2, f₇ t) +
                      ((∫ t : ℝ in 0..2, f₈ t) +
                        (∫ t : ℝ in 0..2, f₉ t))))))))) := by
  rw [intervalIntegral.integral_add h₀
      (h₁.add (h₂.add (h₃.add (h₄.add
        (h₅.add (h₆.add (h₇.add (h₈.add h₉)))))))),
    intervalIntegral.integral_add h₁
      (h₂.add (h₃.add (h₄.add
        (h₅.add (h₆.add (h₇.add (h₈.add h₉))))))),
    intervalIntegral.integral_add h₂
      (h₃.add (h₄.add
        (h₅.add (h₆.add (h₇.add (h₈.add h₉)))))),
    intervalIntegral.integral_add h₃
      (h₄.add (h₅.add (h₆.add (h₇.add (h₈.add h₉))))),
    intervalIntegral.integral_add h₄
      (h₅.add (h₆.add (h₇.add (h₈.add h₉)))),
    intervalIntegral.integral_add h₅
      (h₆.add (h₇.add (h₈.add h₉))),
    intervalIntegral.integral_add h₆ (h₇.add (h₈.add h₉)),
    intervalIntegral.integral_add h₇ (h₈.add h₉),
    intervalIntegral.integral_add h₈ h₉]

/-- The whole reflected-pole integral is the quadratic form of its ten exact
entries. -/
theorem integral_poleWeight_mul_intrinsicEvenP0246Correlation
    (c0 c2 c4 c6 : ℝ) :
    (∫ t : ℝ in 0..2,
      evenStructuralPoleWeight t *
        centeredEndpointCorrelation
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) t) =
      c0 ^ 2 * (-2 * Real.log 2) +
        2 * c0 * c2 * (4 - 6 * Real.log 2) +
        2 * c0 * c4 * (187 / 3 - 90 * Real.log 2) +
        2 * c0 * c6 * (6259 / 5 - 1806 * Real.log 2) +
        c2 ^ 2 * (1 / 5 - (2 / 5 : ℝ) * Real.log 2) +
        2 * c2 * c4 * (29 / 3 - 14 * Real.log 2) +
        2 * c2 * c6 * (2071 / 6 - 498 * Real.log 2) +
        c4 ^ 2 * (7 / 54 - (2 / 9 : ℝ) * Real.log 2) +
        2 * c4 * c6 * (457 / 30 - 22 * Real.log 2) +
        c6 ^ 2 * (37 / 390 - (2 / 13 : ℝ) * Real.log 2) := by
  have h00 : IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * evenStructuralCorrelation00 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor
      evenStructuralCorrelation00 (fun _ ↦ (-1 : ℝ)) continuous_const
    intro t
    unfold evenStructuralCorrelation00
    ring
  have h02 : IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * evenStructuralCorrelation02 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor
      evenStructuralCorrelation02 (fun t ↦ -t * (t - 1) / 2) (by fun_prop)
    intro t
    unfold evenStructuralCorrelation02
    ring
  have h22 : IntervalIntegrable
      (fun t ↦ evenStructuralPoleWeight t * evenStructuralCorrelation22 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor evenStructuralCorrelation22
      (fun t ↦ -(3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40)
      (by fun_prop)
    intro t
    unfold evenStructuralCorrelation22
    ring
  have h04 : IntervalIntegrable (fun t ↦
      evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation04 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor factorTwoIntrinsicP4Correlation04
      (fun t ↦ -t * (t - 1) * (7 * t ^ 2 - 14 * t + 4) / 8)
      (by fun_prop)
    intro t
    unfold factorTwoIntrinsicP4Correlation04
    ring
  have h24 : IntervalIntegrable (fun t ↦
      evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation24 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor factorTwoIntrinsicP4Correlation24
      (fun t ↦ -t *
        (t ^ 5 + 2 * t ^ 4 - 6 * t ^ 3 - 12 * t ^ 2 + 24 * t - 8) / 16)
      (by fun_prop)
    intro t
    unfold factorTwoIntrinsicP4Correlation24
    ring
  have h44 : IntervalIntegrable (fun t ↦
      evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation44 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor factorTwoIntrinsicP4Correlation44
      (fun t ↦
        -(35 * t ^ 8 + 70 * t ^ 7 - 220 * t ^ 6 - 440 * t ^ 5 +
          416 * t ^ 4 + 832 * t ^ 3 - 256 * t ^ 2 - 512 * t + 128) / 1152)
      (by fun_prop)
    intro t
    unfold factorTwoIntrinsicP4Correlation44
    ring
  have h06 : IntervalIntegrable (fun t ↦
      evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation06 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor factorTwoIntrinsicP6Correlation06
      (fun t ↦ -t * (t - 1) *
        (33 * t ^ 4 - 132 * t ^ 3 + 168 * t ^ 2 - 72 * t + 8) / 16)
      (by fun_prop)
    intro t
    unfold factorTwoIntrinsicP6Correlation06
    ring
  have h26 : IntervalIntegrable (fun t ↦
      evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation26 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor factorTwoIntrinsicP6Correlation26
      (fun t ↦ -t *
        (11 * t ^ 7 + 22 * t ^ 6 - 124 * t ^ 5 - 248 * t ^ 4 +
          1184 * t ^ 3 - 1328 * t ^ 2 + 544 * t - 64) / 128)
      (by fun_prop)
    intro t
    unfold factorTwoIntrinsicP6Correlation26
    ring
  have h46 : IntervalIntegrable (fun t ↦
      evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation46 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor factorTwoIntrinsicP6Correlation46
      (fun t ↦ -t *
        (7 * t ^ 9 + 14 * t ^ 8 - 62 * t ^ 7 - 124 * t ^ 6 +
          200 * t ^ 5 + 400 * t ^ 4 - 320 * t ^ 3 - 640 * t ^ 2 +
          640 * t - 128) / 256)
      (by fun_prop)
    intro t
    unfold factorTwoIntrinsicP6Correlation46
    ring
  have h66 : IntervalIntegrable (fun t ↦
      evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation66 t)
      volume 0 2 := by
    apply intervalIntegrable_pole_mul_of_eq_factor factorTwoIntrinsicP6Correlation66
      (fun t ↦
        -(231 * t ^ 12 + 462 * t ^ 11 - 2352 * t ^ 10 - 4704 * t ^ 9 +
          8792 * t ^ 8 + 17584 * t ^ 7 - 14752 * t ^ 6 - 29504 * t ^ 5 +
          10880 * t ^ 4 + 21760 * t ^ 3 - 3072 * t ^ 2 - 6144 * t + 1024) /
            13312)
      (by fun_prop)
    intro t
    unfold factorTwoIntrinsicP6Correlation66
    ring
  rw [show (fun t : ℝ ↦
      evenStructuralPoleWeight t *
        centeredEndpointCorrelation
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) t) =
    fun t ↦
      c0 ^ 2 * (evenStructuralPoleWeight t * evenStructuralCorrelation00 t) +
        (2 * c0 * c2 *
          (evenStructuralPoleWeight t * evenStructuralCorrelation02 t) +
        (c2 ^ 2 *
          (evenStructuralPoleWeight t * evenStructuralCorrelation22 t) +
        (2 * c0 * c4 *
          (evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation04 t) +
        (2 * c2 * c4 *
          (evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation24 t) +
        (c4 ^ 2 *
          (evenStructuralPoleWeight t * factorTwoIntrinsicP4Correlation44 t) +
        (2 * c0 * c6 *
          (evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation06 t) +
        (2 * c2 * c6 *
          (evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation26 t) +
        (2 * c4 * c6 *
          (evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation46 t) +
        c6 ^ 2 *
          (evenStructuralPoleWeight t * factorTwoIntrinsicP6Correlation66 t))))))))) by
      funext t
      rw [centeredEndpointCorrelation_intrinsicEvenP0246]
      ring,
    integral_ten_add _ _ _ _ _ _ _ _ _ _
      (h00.const_mul (c0 ^ 2))
      (h02.const_mul (2 * c0 * c2))
      (h22.const_mul (c2 ^ 2))
      (h04.const_mul (2 * c0 * c4))
      (h24.const_mul (2 * c2 * c4))
      (h44.const_mul (c4 ^ 2))
      (h06.const_mul (2 * c0 * c6))
      (h26.const_mul (2 * c2 * c6))
      (h46.const_mul (2 * c4 * c6))
      (h66.const_mul (c6 ^ 2))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_poleWeight_mul_evenStructuralCorrelations.1,
    integral_poleWeight_mul_evenStructuralCorrelations.2.1,
    integral_poleWeight_mul_evenStructuralCorrelations.2.2,
    integral_poleWeight_mul_factorTwoIntrinsicP4Correlations.1,
    integral_poleWeight_mul_factorTwoIntrinsicP4Correlations.2.1,
    integral_poleWeight_mul_factorTwoIntrinsicP4Correlations.2.2,
    integral_poleWeight_mul_factorTwoIntrinsicP6Correlations.1,
    integral_poleWeight_mul_factorTwoIntrinsicP6Correlations.2.1,
    integral_poleWeight_mul_factorTwoIntrinsicP6Correlations.2.2.1,
    integral_poleWeight_mul_factorTwoIntrinsicP6Correlations.2.2.2]
  ring

/-! ## Four exact coefficient matrices -/

/-- A symmetric `4 × 4` matrix in the coefficient order `P0,P2,P4,P6`. -/
def factorTwoP6EvenSymmetricMatrix
    (q00 q02 q04 q06 q22 q24 q26 q44 q46 q66 : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![q00, q02, q04, q06;
    q02, q22, q24, q26;
    q04, q24, q44, q46;
    q06, q26, q46, q66]

/-- The compiled degree-six pole-free kernel Gram. -/
def factorTwoP6EvenDegreeSixKernelGramMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenSymmetricMatrix
    (2 * poleFreeCoeff0 yoshidaEndpointA +
      (4 / 3 : ℝ) * poleFreeCoeff2 yoshidaEndpointA +
      (32 / 15 : ℝ) * poleFreeCoeff4 yoshidaEndpointA +
      (32 / 7 : ℝ) * poleFreeCoeff6 yoshidaEndpointA)
    ((4 / 15 : ℝ) * poleFreeCoeff2 yoshidaEndpointA +
      (16 / 21 : ℝ) * poleFreeCoeff4 yoshidaEndpointA +
      (32 / 15 : ℝ) * poleFreeCoeff6 yoshidaEndpointA)
    (poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
      poleFreeCoeff6 yoshidaEndpointA * (32 / 99))
    (poleFreeCoeff6 yoshidaEndpointA * (32 / 3003))
    ((16 / 75 : ℝ) * poleFreeCoeff4 yoshidaEndpointA +
      (32 / 35 : ℝ) * poleFreeCoeff6 yoshidaEndpointA)
    (poleFreeCoeff6 yoshidaEndpointA * (32 / 315))
    0 0 0 0

/-- The exact reflected-pole Gram. -/
def factorTwoP6EvenReflectedPoleGramMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenSymmetricMatrix
    (-2 * Real.log 2)
    (4 - 6 * Real.log 2)
    (187 / 3 - 90 * Real.log 2)
    (6259 / 5 - 1806 * Real.log 2)
    (1 / 5 - (2 / 5 : ℝ) * Real.log 2)
    (29 / 3 - 14 * Real.log 2)
    (2071 / 6 - 498 * Real.log 2)
    (7 / 54 - (2 / 9 : ℝ) * Real.log 2)
    (457 / 30 - 22 * Real.log 2)
    (37 / 390 - (2 / 13 : ℝ) * Real.log 2)

/-- The exact retained `p = 2` atom Gram. -/
def factorTwoP6EvenPrimeTwoAtomGramMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenSymmetricMatrix
    (-(Real.log 2 / Real.sqrt 2) * 2) 0 0 0
    (-(Real.log 2 / Real.sqrt 2) * (2 / 5 : ℝ)) 0 0
    (-(Real.log 2 / Real.sqrt 2) * (2 / 9 : ℝ)) 0
    (-(Real.log 2 / Real.sqrt 2) * (2 / 13 : ℝ))

/-- Normalized `p = 3` correlation height. -/
def factorTwoP6EvenPrimeHeight : ℝ :=
  factorTwoPrimeShift / yoshidaEndpointA

/-- The exact retained `p = 3` atom Gram.  Its entries are explicit
polynomials at the single normalized prime height. -/
def factorTwoP6EvenPrimeThreeAtomGramMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  let β : ℝ := -(Real.log 3 / Real.sqrt 3)
  let τ : ℝ := factorTwoP6EvenPrimeHeight
  factorTwoP6EvenSymmetricMatrix
    (β * evenStructuralCorrelation00 τ)
    (β * evenStructuralCorrelation02 τ)
    (β * factorTwoIntrinsicP4Correlation04 τ)
    (β * factorTwoIntrinsicP6Correlation06 τ)
    (β * evenStructuralCorrelation22 τ)
    (β * factorTwoIntrinsicP4Correlation24 τ)
    (β * factorTwoIntrinsicP6Correlation26 τ)
    (β * factorTwoIntrinsicP4Correlation44 τ)
    (β * factorTwoIntrinsicP6Correlation46 τ)
    (β * factorTwoIntrinsicP6Correlation66 τ)

/-- The exact perturbation Gram is the sum of the four structural blocks. -/
def factorTwoP6EvenPerturbationGramMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  factorTwoP6EvenDegreeSixKernelGramMatrix +
    factorTwoP6EvenReflectedPoleGramMatrix +
    factorTwoP6EvenPrimeTwoAtomGramMatrix +
    factorTwoP6EvenPrimeThreeAtomGramMatrix

private theorem dotProduct_mulVec_factorTwoP6EvenSymmetricMatrix
    (q00 q02 q04 q06 q22 q24 q26 q44 q46 q66 c0 c2 c4 c6 : ℝ) :
    dotProduct (star (![c0, c2, c4, c6] : Fin 4 → ℝ))
      (factorTwoP6EvenSymmetricMatrix
          q00 q02 q04 q06 q22 q24 q26 q44 q46 q66 *ᵥ
            (![c0, c2, c4, c6] : Fin 4 → ℝ)) =
      c0 ^ 2 * q00 + 2 * c0 * c2 * q02 + 2 * c0 * c4 * q04 +
        2 * c0 * c6 * q06 + c2 ^ 2 * q22 + 2 * c2 * c4 * q24 +
        2 * c2 * c6 * q26 + c4 ^ 2 * q44 + 2 * c4 * c6 * q46 +
        c6 ^ 2 * q66 := by
  simp [dotProduct, mulVec, factorTwoP6EvenSymmetricMatrix,
    Fin.sum_univ_succ]
  ring

/-- The assembled perturbation Gram is symmetric. -/
theorem factorTwoP6EvenPerturbationGramMatrix_isSymm :
    factorTwoP6EvenPerturbationGramMatrix.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [factorTwoP6EvenPerturbationGramMatrix,
      factorTwoP6EvenDegreeSixKernelGramMatrix,
      factorTwoP6EvenReflectedPoleGramMatrix,
      factorTwoP6EvenPrimeTwoAtomGramMatrix,
      factorTwoP6EvenPrimeThreeAtomGramMatrix,
      factorTwoP6EvenSymmetricMatrix, Matrix.transpose_apply]

/-- Exact coefficient-quadratic evaluation of the perturbation model on the
intrinsic even `P0/P2/P4/P6` profile. -/
theorem factorTwoP6EvenPerturbationPolynomialModel_intrinsicEvenP0246_eq_matrixQuadratic
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenPerturbationPolynomialModel
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) =
      dotProduct (star (![c0, c2, c4, c6] : Fin 4 → ℝ))
        (factorTwoP6EvenPerturbationGramMatrix *ᵥ
          (![c0, c2, c4, c6] : Fin 4 → ℝ)) := by
  have hkernel :=
    integral_poleFreeKernelPolynomial6_mul_intrinsicEvenP0246Correlation
      c0 c2 c4 c6
  have hpole :=
    integral_poleWeight_mul_intrinsicEvenP0246Correlation c0 c2 c4 c6
  have hzero :
      centeredEndpointCorrelation
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) 0 =
        2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
          (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 := by
    rw [centeredEndpointCorrelation_intrinsicEvenP0246]
    norm_num [evenStructuralCorrelation00, evenStructuralCorrelation02,
      evenStructuralCorrelation22, factorTwoIntrinsicP4Correlation04,
      factorTwoIntrinsicP4Correlation24, factorTwoIntrinsicP4Correlation44,
      factorTwoIntrinsicP6Correlation06, factorTwoIntrinsicP6Correlation26,
      factorTwoIntrinsicP6Correlation46, factorTwoIntrinsicP6Correlation66]
    ring
  unfold factorTwoP6EvenPerturbationPolynomialModel
  rw [hkernel, hpole, hzero,
    centeredEndpointCorrelation_intrinsicEvenP0246]
  simp [factorTwoP6EvenPerturbationGramMatrix,
    factorTwoP6EvenDegreeSixKernelGramMatrix,
    factorTwoP6EvenReflectedPoleGramMatrix,
    factorTwoP6EvenPrimeTwoAtomGramMatrix,
    factorTwoP6EvenPrimeThreeAtomGramMatrix,
    factorTwoP6EvenPrimeHeight,
    factorTwoP6EvenSymmetricMatrix,
    factorTwoIntrinsicEvenP024PolynomialKernelGram,
    dotProduct, mulVec, Fin.sum_univ_succ]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationGramStructural
