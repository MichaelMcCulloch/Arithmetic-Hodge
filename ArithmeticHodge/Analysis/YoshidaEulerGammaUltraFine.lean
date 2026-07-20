import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeTrigEnclosures

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArithmeticHodge.Analysis.YoshidaEulerGammaUltraFine

noncomputable section

open Filter Topology
open RatInterval
open YoshidaConstantBounds
open YoshidaFactorTwoPrimeTrigEnclosures

/-!
# A sixth-order Euler--Mascheroni enclosure

The standard corrected harmonic upper approximation is sharpened by the next
two Euler--Maclaurin terms.  The resulting lower and upper sequences differ
by `1 / (252 N^6)`, so the power-of-two sample `N = 256` is already much
narrower than the scalar-certificate budget.
-/

def gammaFourthLowerApprox (n : ℕ) : ℝ :=
  gammaUpperApprox n - 1 / (120 * ((n : ℝ) + 1) ^ 4)

def gammaSixthUpperApprox (n : ℕ) : ℝ :=
  gammaFourthLowerApprox n + 1 / (252 * ((n : ℝ) + 1) ^ 6)

private theorem log_increment_le_fourth_correction
    {t : ℝ} (ht : 0 < t) :
    Real.log ((t + 1) / t) ≤
      (2 * t + 1) / (2 * t * (t + 1)) +
        (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
        (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4)) := by
  let x : ℝ := 1 / (2 * t + 1)
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hx1 : x < 1 := by
    dsimp only [x]
    rw [div_lt_one (by positivity)]
    linarith
  have h := Real.log_div_le_sum_range_add hx0 hx1 4
  have hratio : (1 + x) / (1 - x) = (t + 1) / t := by
    dsimp only [x]
    field_simp [ht.ne', (by linarith : (2 * t + 1) ≠ 0)]
    ring
  rw [hratio] at h
  dsimp only [x] at h
  norm_num [Finset.sum_range_succ] at h
  have hbound : 1 / 2 * Real.log ((t + 1) / t) ≤
      (2 * t + 1)⁻¹ + (2 * t + 1)⁻¹ ^ 3 / 3 +
        (2 * t + 1)⁻¹ ^ 5 / 5 + (2 * t + 1)⁻¹ ^ 7 / 7 +
        (2 * t + 1)⁻¹ ^ 9 / (1 - (2 * t + 1)⁻¹ ^ 2) := by
    simpa only [inv_pow] using h
  have hden1 : 0 < 2 * t + 1 := by linarith
  have hden2 : 0 < 1 - (2 * t + 1)⁻¹ ^ 2 := by
    have hone : (2 * t + 1)⁻¹ < 1 := by
      rw [inv_lt_one₀ hden1]
      linarith [hbound]
    have hnonneg : 0 ≤ (2 * t + 1)⁻¹ := by positivity
    nlinarith
  have hpoly : 0 < (2 * t + 1) ^ 2 - 1 := by
    nlinarith [sq_nonneg t]
  have hdiff : 0 ≤
      ((2 * t + 1) / (2 * t * (t + 1)) +
          (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
          (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4))) -
        2 * ((2 * t + 1)⁻¹ + (2 * t + 1)⁻¹ ^ 3 / 3 +
          (2 * t + 1)⁻¹ ^ 5 / 5 + (2 * t + 1)⁻¹ ^ 7 / 7 +
          (2 * t + 1)⁻¹ ^ 9 /
            (1 - (2 * t + 1)⁻¹ ^ 2)) := by
    rw [show
      ((2 * t + 1) / (2 * t * (t + 1)) +
          (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
          (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4))) -
        2 * ((2 * t + 1)⁻¹ + (2 * t + 1)⁻¹ ^ 3 / 3 +
          (2 * t + 1)⁻¹ ^ 5 / 5 + (2 * t + 1)⁻¹ ^ 7 / 7 +
          (2 * t + 1)⁻¹ ^ 9 /
            (1 - (2 * t + 1)⁻¹ ^ 2)) =
        (2560 * t ^ 8 + 10240 * t ^ 7 + 17376 * t ^ 6 +
          16288 * t ^ 5 + 9434 * t ^ 4 + 3668 * t ^ 3 +
          952 * t ^ 2 + 126 * t + 7) /
          (840 * t ^ 4 * (t + 1) ^ 4 * (2 * t + 1) ^ 7) by
      field_simp [ht.ne', (by linarith : (t + 1) ≠ 0), hden1.ne',
        hden2.ne', hpoly.ne']
      ring]
    positivity
  calc
    Real.log ((t + 1) / t) ≤
        2 * ((2 * t + 1)⁻¹ + (2 * t + 1)⁻¹ ^ 3 / 3 +
          (2 * t + 1)⁻¹ ^ 5 / 5 + (2 * t + 1)⁻¹ ^ 7 / 7 +
          (2 * t + 1)⁻¹ ^ 9 /
            (1 - (2 * t + 1)⁻¹ ^ 2)) := by
      linarith [hbound]
    _ ≤ (2 * t + 1) / (2 * t * (t + 1)) +
        (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
        (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4)) := by
      linarith

private theorem sixth_correction_le_log_increment
    {t : ℝ} (ht : 0 < t) :
    (2 * t + 1) / (2 * t * (t + 1)) +
        (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
        (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4)) +
        (1 / (252 * (t + 1) ^ 6) - 1 / (252 * t ^ 6)) ≤
      Real.log ((t + 1) / t) := by
  let x : ℝ := 1 / (2 * t + 1)
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hx1 : x < 1 := by
    dsimp only [x]
    rw [div_lt_one (by positivity)]
    linarith
  have h := Real.sum_range_le_log_div hx0 hx1 5
  have hratio : (1 + x) / (1 - x) = (t + 1) / t := by
    dsimp only [x]
    field_simp [ht.ne', (by linarith : (2 * t + 1) ≠ 0)]
    ring
  rw [hratio] at h
  dsimp only [x] at h
  norm_num [Finset.sum_range_succ] at h
  have hbound :
      (2 * t + 1)⁻¹ + (2 * t + 1)⁻¹ ^ 3 / 3 +
          (2 * t + 1)⁻¹ ^ 5 / 5 + (2 * t + 1)⁻¹ ^ 7 / 7 +
          (2 * t + 1)⁻¹ ^ 9 / 9 ≤
        1 / 2 * Real.log ((t + 1) / t) := by
    simpa only [inv_pow] using h
  have hden1 : 0 < 2 * t + 1 := by linarith
  have hdiff : 0 ≤
      2 * ((2 * t + 1)⁻¹ + (2 * t + 1)⁻¹ ^ 3 / 3 +
          (2 * t + 1)⁻¹ ^ 5 / 5 + (2 * t + 1)⁻¹ ^ 7 / 7 +
          (2 * t + 1)⁻¹ ^ 9 / 9) -
        ((2 * t + 1) / (2 * t * (t + 1)) +
          (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
          (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4)) +
          (1 / (252 * (t + 1) ^ 6) - 1 / (252 * t ^ 6))) := by
    rw [show
      2 * ((2 * t + 1)⁻¹ + (2 * t + 1)⁻¹ ^ 3 / 3 +
          (2 * t + 1)⁻¹ ^ 5 / 5 + (2 * t + 1)⁻¹ ^ 7 / 7 +
          (2 * t + 1)⁻¹ ^ 9 / 9) -
        ((2 * t + 1) / (2 * t * (t + 1)) +
          (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
          (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4)) +
          (1 / (252 * (t + 1) ^ 6) - 1 / (252 * t ^ 6))) =
        (43008 * t ^ 12 + 258048 * t ^ 11 + 708540 * t ^ 10 +
          1177260 * t ^ 9 + 1318530 * t ^ 8 + 1049088 * t ^ 7 +
          608306 * t ^ 6 + 259074 * t ^ 5 + 80433 * t ^ 4 +
          17756 * t ^ 3 + 2649 * t ^ 2 + 240 * t + 10) /
          (2520 * t ^ 6 * (t + 1) ^ 6 * (2 * t + 1) ^ 9) by
      field_simp [ht.ne', (by linarith : (t + 1) ≠ 0), hden1.ne']
      ring]
    positivity
  calc
    (2 * t + 1) / (2 * t * (t + 1)) +
          (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
          (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4)) +
          (1 / (252 * (t + 1) ^ 6) - 1 / (252 * t ^ 6)) ≤
        2 * ((2 * t + 1)⁻¹ + (2 * t + 1)⁻¹ ^ 3 / 3 +
          (2 * t + 1)⁻¹ ^ 5 / 5 + (2 * t + 1)⁻¹ ^ 7 / 7 +
          (2 * t + 1)⁻¹ ^ 9 / 9) := by
      linarith [hbound]
    _ ≤ Real.log ((t + 1) / t) := by
      linarith [hbound]

private theorem gammaFourthLowerApprox_step (n : ℕ) :
    gammaFourthLowerApprox n ≤ gammaFourthLowerApprox (n + 1) := by
  let t : ℝ := n + 1
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have hlog := log_increment_le_fourth_correction ht
  have hdiff :
      gammaFourthLowerApprox (n + 1) - gammaFourthLowerApprox n =
        (2 * t + 1) / (2 * t * (t + 1)) -
          Real.log ((t + 1) / t) +
          (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
          (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4)) := by
    simp only [gammaFourthLowerApprox, gammaUpperApprox, gammaLowerApprox,
      harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_one, t]
    rw [Real.log_div (by positivity) (by positivity)]
    field_simp [ht.ne', (by linarith : (t + 1) ≠ 0)]
    ring
  apply sub_nonneg.mp
  rw [hdiff]
  linarith

private theorem gammaSixthUpperApprox_step (n : ℕ) :
    gammaSixthUpperApprox (n + 1) ≤ gammaSixthUpperApprox n := by
  let t : ℝ := n + 1
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have hlog := sixth_correction_le_log_increment ht
  have hdiff :
      gammaSixthUpperApprox (n + 1) - gammaSixthUpperApprox n =
        (2 * t + 1) / (2 * t * (t + 1)) -
          Real.log ((t + 1) / t) +
          (1 / (12 * (t + 1) ^ 2) - 1 / (12 * t ^ 2)) +
          (-1 / (120 * (t + 1) ^ 4) + 1 / (120 * t ^ 4)) +
          (1 / (252 * (t + 1) ^ 6) - 1 / (252 * t ^ 6)) := by
    simp only [gammaSixthUpperApprox, gammaFourthLowerApprox,
      gammaUpperApprox, gammaLowerApprox, harmonic_succ, Rat.cast_add,
      Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one, t]
    rw [Real.log_div (by positivity) (by positivity)]
    field_simp [ht.ne', (by linarith : (t + 1) ≠ 0)]
    ring
  apply sub_nonpos.mp
  rw [hdiff]
  linarith

private theorem tendsto_fourthCorrection :
    Tendsto (fun n : ℕ ↦ 1 / (120 * ((n : ℝ) + 1) ^ 4)) atTop
      (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 4
  have h' := h.const_mul (1 / 120 : ℝ)
  convert h' using 1
  · funext n
    field_simp
  · ring

private theorem tendsto_sixthCorrection :
    Tendsto (fun n : ℕ ↦ 1 / (252 * ((n : ℝ) + 1) ^ 6)) atTop
      (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 6
  have h' := h.const_mul (1 / 252 : ℝ)
  convert h' using 1
  · funext n
    field_simp
  · ring

theorem tendsto_gammaFourthLowerApprox :
    Tendsto gammaFourthLowerApprox atTop
      (nhds Real.eulerMascheroniConstant) := by
  simpa only [gammaFourthLowerApprox, sub_zero] using
    tendsto_gammaUpperApprox.sub tendsto_fourthCorrection

theorem tendsto_gammaSixthUpperApprox :
    Tendsto gammaSixthUpperApprox atTop
      (nhds Real.eulerMascheroniConstant) := by
  simpa only [gammaSixthUpperApprox, add_zero] using
    tendsto_gammaFourthLowerApprox.add tendsto_sixthCorrection

theorem gammaFourthLowerApprox_le_eulerGamma (n : ℕ) :
    gammaFourthLowerApprox n ≤ Real.eulerMascheroniConstant :=
  (monotone_nat_of_le_succ gammaFourthLowerApprox_step).ge_of_tendsto
    tendsto_gammaFourthLowerApprox n

theorem eulerGamma_le_gammaSixthUpperApprox (n : ℕ) :
    Real.eulerMascheroniConstant ≤ gammaSixthUpperApprox n :=
  (antitone_nat_of_succ_le gammaSixthUpperApprox_step).le_of_tendsto
    tendsto_gammaSixthUpperApprox n

/-! ## Fixed rational enclosure at `N = 256` -/

def gammaFourthLowerInterval256 : RatInterval :=
  pure (harmonic 256) - pure 8 * factorTwoPrimeLogTwoInterval -
      pure (1 / (2 * 256 : ℚ)) + pure (1 / (12 * 256 ^ 2 : ℚ)) -
    pure (1 / (120 * 256 ^ 4 : ℚ))

def gammaSixthCorrectionInterval256 : RatInterval :=
  ⟨0, 1 / (252 * 256 ^ 6 : ℚ)⟩

/-- Fine rational enclosure of Euler's constant. -/
def eulerGammaUltraFineInterval : RatInterval :=
  gammaFourthLowerInterval256 + gammaSixthCorrectionInterval256

private theorem log_256_eq_eight_log_two :
    Real.log (256 : ℝ) = 8 * Real.log 2 := by
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
  norm_num

private theorem gammaFourthLowerApprox_255_eq :
    gammaFourthLowerApprox 255 =
      (harmonic 256 : ℝ) - 8 * Real.log 2 - 1 / (2 * 256) +
        1 / (12 * 256 ^ 2) - 1 / (120 * 256 ^ 4) := by
  simp only [gammaFourthLowerApprox, gammaUpperApprox, gammaLowerApprox,
    Nat.cast_ofNat]
  norm_num only
  rw [log_256_eq_eight_log_two]

private theorem gammaFourthLowerInterval256_contains :
    gammaFourthLowerInterval256.Contains (gammaFourthLowerApprox 255) := by
  have hlog : factorTwoPrimeLogTwoInterval.Contains (Real.log 2) := by
    have h := factorTwoPrimeLogTwoInterval_contains
    unfold YoshidaFactorTwoPhasePerturbationMomentSeries.factorTwoMomentLength
      YoshidaEndpointHyperbolicBound.yoshidaEndpointA at h
    convert h using 1
    ring
  have h := contains_sub
    (contains_add
      (contains_sub
        (contains_sub
          (contains_pure (harmonic 256))
          (contains_mul (contains_pure 8) hlog))
        (contains_pure (1 / (2 * 256 : ℚ))))
      (contains_pure (1 / (12 * 256 ^ 2 : ℚ))))
    (contains_pure (1 / (120 * 256 ^ 4 : ℚ)))
  unfold gammaFourthLowerInterval256
  rw [gammaFourthLowerApprox_255_eq]
  convert h using 1
  norm_num

theorem eulerGammaUltraFineInterval_contains :
    eulerGammaUltraFineInterval.Contains Real.eulerMascheroniConstant := by
  have hbase := gammaFourthLowerInterval256_contains
  have hlo := gammaFourthLowerApprox_le_eulerGamma 255
  have hup := eulerGamma_le_gammaSixthUpperApprox 255
  have hsix : gammaSixthUpperApprox 255 =
      gammaFourthLowerApprox 255 + 1 / (252 * (256 : ℝ) ^ 6) := by
    norm_num [gammaSixthUpperApprox]
  unfold eulerGammaUltraFineInterval gammaSixthCorrectionInterval256
  change (RatInterval.add gammaFourthLowerInterval256
      ⟨0, 1 / (252 * 256 ^ 6 : ℚ)⟩).Contains
    Real.eulerMascheroniConstant
  unfold RatInterval.Contains RatInterval.add
  norm_num only [Rat.cast_add, Rat.cast_zero]
  constructor
  · simpa only [add_zero] using hbase.1.trans hlo
  · rw [hsix] at hup
    norm_num at hup ⊢
    linarith [hbase.2]

theorem eulerGammaUltraFineInterval_width_le :
    width eulerGammaUltraFineInterval ≤ (1 / 1000000000000 : ℚ) := by
  decide +kernel

end

end ArithmeticHodge.Analysis.YoshidaEulerGammaUltraFine
