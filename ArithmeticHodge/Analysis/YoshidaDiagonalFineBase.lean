import ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaDiagonalFineBase

noncomputable section

open RatInterval
open YoshidaConstantBounds
open YoshidaDiagonalAcceleratedSeries
open YoshidaDiagonalMomentEnclosures
open YoshidaDiagonalSeriesTail
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

/-!
# Fine common enclosure for the accelerated diagonal base

The production diagonal targets have width `10⁻⁵`.  The exploratory common
base interval is about `3 · 10⁻⁴` wide because of its coarse Euler-gamma and
`log π` boxes.  This module refines the one-millionth boxes from the low-mode
certificates into reusable asymmetric bounds that are tight enough for the
high-mode tail checkpoints.
-/

def fineGammaInterval : RatInterval :=
  ⟨5772155 / 10000000, 5772159 / 10000000⟩

def fineLogPiInterval : RatInterval :=
  ⟨11447298 / 10000000, 1144730 / 1000000⟩

private theorem strict_log_four_hundred_bounds :
    (59914645469 / 10000000000 : ℝ) < Real.log 400 ∧
      Real.log 400 < (59914645474 / 10000000000 : ℝ) := by
  have htwo := strict_log_two_fine_bounds
  have hhundred := strict_log_one_hundred_bounds
  have hid : Real.log (400 : ℝ) = 2 * Real.log 2 + Real.log 100 := by
    calc
      Real.log (400 : ℝ) = Real.log ((2 : ℝ) ^ 2 * 100) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log 100 := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 2 + Real.log 100 := by
        rw [Real.log_pow]
        norm_num
  rw [hid]
  constructor <;> linarith

set_option maxRecDepth 100000 in
private theorem strict_euler_gamma_fine_bounds :
    (5772155 / 10000000 : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (5772159 / 10000000 : ℝ) := by
  have hlower := gammaLowerApprox_le_eulerGamma 799
  have hupper := eulerGamma_le_gammaUpperApprox 399
  have htwo := strict_log_two_fine_bounds
  have hhundred := strict_log_one_hundred_bounds
  have hlogEightHundred :
      (66846117274 / 10000000000 : ℝ) < Real.log 800 ∧
        Real.log 800 < (66846117280 / 10000000000 : ℝ) := by
    have hid : Real.log (800 : ℝ) =
        3 * Real.log 2 + Real.log 100 := by
      calc
        Real.log (800 : ℝ) = Real.log ((2 : ℝ) ^ 3 * 100) := by norm_num
        _ = Real.log ((2 : ℝ) ^ 3) + Real.log 100 := by
          rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = 3 * Real.log 2 + Real.log 100 := by
          rw [Real.log_pow]
          norm_num
    rw [hid]
    constructor <;> linarith
  constructor
  · apply lt_of_lt_of_le ?_ hlower
    simp only [gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [hlogEightHundred.2]
  · apply lt_of_le_of_lt hupper
    simp only [gammaUpperApprox, gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [strict_log_four_hundred_bounds.1]

private theorem log_pi_d20_fine_lower :
    (11447298 / 10000000 : ℝ) <
      Real.log (314159265358979323846 / 100000000000000000000 : ℝ) := by
  have h := Real.sum_range_le_log_div
    (x := (107079632679489661923 / 207079632679489661923 : ℝ))
    (by norm_num) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem log_3141593_million_fine_upper :
    Real.log (3141593 / 1000000 : ℝ) < (1144730 / 1000000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (2141593 / 4141593 : ℝ))
    (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem strict_log_pi_fine_bounds :
    (11447298 / 10000000 : ℝ) < Real.log Real.pi ∧
      Real.log Real.pi < (1144730 / 1000000 : ℝ) := by
  constructor
  · have hpi := Real.pi_gt_d20
    have hlog := log_pi_d20_fine_lower
    norm_num at hpi hlog ⊢
    exact hlog.trans (Real.log_lt_log (by norm_num) hpi)
  · have hpi := Real.pi_lt_d6
    have hlog := log_3141593_million_fine_upper
    norm_num at hpi hlog ⊢
    exact (Real.log_lt_log Real.pi_pos hpi).trans hlog

theorem fineGammaInterval_contains :
    fineGammaInterval.Contains Real.eulerMascheroniConstant := by
  have h := strict_euler_gamma_fine_bounds
  constructor
  · norm_num [fineGammaInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [fineGammaInterval, Contains] at h ⊢
    exact h.2.le

theorem fineLogPiInterval_contains :
    fineLogPiInterval.Contains (Real.log Real.pi) := by
  have h := strict_log_pi_fine_bounds
  constructor
  · norm_num [fineLogPiInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [fineLogPiInterval, Contains] at h ⊢
    exact h.2.le

def fineDiagonalBaseInterval (n : ℕ) : RatInterval :=
  pure 2 * diagonalRampInterval n (-1 / 2) sqrtTwoInterval -
      fineGammaInterval - fineLogPiInterval + logFourThirdsInterval +
    diagonalAInterval * positiveSquare piFineInterval / pure 6

/-- The fine common base interval contains the exact accelerated base at
every Fourier mode. -/
theorem fineDiagonalBaseInterval_contains_acceleratedBase (n : ℕ) :
    (fineDiagonalBaseInterval n).Contains (diagonalAcceleratedBase n) := by
  rw [← diagonalBaseValue_eq_acceleratedBase]
  have hramp := diagonalRampInterval_contains n (-1 / 2) sqrtTwoInterval
    (by norm_num) sqrtTwoInterval_contains
  have hramp' : (diagonalRampInterval n (-1 / 2) sqrtTwoInterval).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2) (-1 / 2 : ℝ)
        (Real.sqrt 2)) := by
    convert hramp using 1
    norm_num
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hsix : (RatInterval.pure (6 : ℚ)).Contains (6 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hpiSq : (positiveSquare piFineInterval).Contains (Real.pi ^ 2) :=
    positiveSquare_contains (by norm_num [piFineInterval])
      piFineInterval_contains
  have htail :
      (diagonalAInterval * positiveSquare piFineInterval /
        RatInterval.pure 6).Contains
        (diagonalAValue * Real.pi ^ 2 / 6) :=
    contains_div_of_pos (by norm_num [RatInterval.pure])
      (contains_mul diagonalAInterval_contains hpiSq) hsix
  unfold fineDiagonalBaseInterval diagonalBaseValue
  exact contains_add
    (contains_add
      (contains_sub
        (contains_sub (contains_mul htwo hramp') fineGammaInterval_contains)
        fineLogPiInterval_contains)
      logFourThirdsInterval_contains)
    htail

end

end ArithmeticHodge.Analysis.YoshidaDiagonalFineBase
