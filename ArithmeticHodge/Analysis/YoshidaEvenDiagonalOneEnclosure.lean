import ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures
import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEvenDiagonalOneEnclosure

noncomputable section

open RatInterval
open YoshidaConstantBounds
open YoshidaDiagonalAcceleratedSeries
open YoshidaDiagonalMomentEnclosures
open YoshidaDiagonalSeriesTail
open YoshidaEvenMomentTargets
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

private def oneGammaInterval : RatInterval :=
  ⟨577215 / 1000000, 577216 / 1000000⟩

private def oneLogPiInterval : RatInterval :=
  ⟨1144729 / 1000000, 1144730 / 1000000⟩

/-! The production box is only one hundred-thousandth wide, so the coarse
constant intervals used by the ten-mode exploratory package are sharpened
here by exact rational logarithm estimates. -/

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
    (577215 / 1000000 : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (577216 / 1000000 : ℝ) := by
  have hlower := gammaLowerApprox_le_eulerGamma 399
  have hupper := eulerGamma_le_gammaUpperApprox 399
  have hlog := strict_log_four_hundred_bounds
  constructor
  · apply lt_of_lt_of_le ?_ hlower
    simp only [gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [hlog.2]
  · apply lt_of_le_of_lt hupper
    simp only [gammaUpperApprox, gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [hlog.1]

private theorem log_3141592_million_fine_lower :
    (1144729 / 1000000 : ℝ) < Real.log (3141592 / 1000000 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (267699 / 517699 : ℝ))
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
    (1144729 / 1000000 : ℝ) < Real.log Real.pi ∧
      Real.log Real.pi < (1144730 / 1000000 : ℝ) := by
  constructor
  · have hpi := Real.pi_gt_d6
    have hlog := log_3141592_million_fine_lower
    norm_num at hpi hlog ⊢
    exact hlog.trans (Real.log_lt_log (by norm_num) hpi)
  · have hpi := Real.pi_lt_d6
    have hlog := log_3141593_million_fine_upper
    norm_num at hpi hlog ⊢
    exact (Real.log_lt_log Real.pi_pos hpi).trans hlog

private theorem oneGammaInterval_contains :
    oneGammaInterval.Contains Real.eulerMascheroniConstant := by
  have h := strict_euler_gamma_fine_bounds
  constructor
  · norm_num [oneGammaInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [oneGammaInterval, Contains] at h ⊢
    exact h.2.le

private theorem oneLogPiInterval_contains :
    oneLogPiInterval.Contains (Real.log Real.pi) := by
  have h := strict_log_pi_fine_bounds
  constructor
  · norm_num [oneLogPiInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [oneLogPiInterval, Contains] at h ⊢
    exact h.2.le

private def oneDiagonalBaseInterval : RatInterval :=
  pure 2 * diagonalRampInterval 1 (-1 / 2) sqrtTwoInterval -
      oneGammaInterval - oneLogPiInterval + logFourThirdsInterval +
    diagonalAInterval * positiveSquare piFineInterval / pure 6

private theorem oneDiagonalBaseInterval_contains_acceleratedBase :
    oneDiagonalBaseInterval.Contains (diagonalAcceleratedBase 1) := by
  rw [← diagonalBaseValue_eq_acceleratedBase]
  have hramp := diagonalRampInterval_contains 1 (-1 / 2) sqrtTwoInterval
    (by norm_num) sqrtTwoInterval_contains
  have hramp' : (diagonalRampInterval 1 (-1 / 2) sqrtTwoInterval).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa 1 ^ 2) (-1 / 2 : ℝ)
        (Real.sqrt 2)) := by
    convert hramp using 1
    norm_num
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hsix : (RatInterval.pure (6 : ℚ)).Contains (6 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hpiSq : (positiveSquare piFineInterval).Contains (Real.pi ^ 2) :=
    positiveSquare_contains (by norm_num [piFineInterval]) piFineInterval_contains
  have htail :
      (diagonalAInterval * positiveSquare piFineInterval /
        RatInterval.pure 6).Contains
        (diagonalAValue * Real.pi ^ 2 / 6) :=
    contains_div_of_pos (by norm_num [RatInterval.pure])
      (contains_mul diagonalAInterval_contains hpiSq) hsix
  unfold oneDiagonalBaseInterval diagonalBaseValue
  exact contains_add
    (contains_add
      (contains_sub
        (contains_sub (contains_mul htwo hramp') oneGammaInterval_contains)
        oneLogPiInterval_contains)
      logFourThirdsInterval_contains)
    htail

private def oneDiagonalSeriesInterval (N : ℕ) : RatInterval :=
  oneDiagonalBaseInterval - diagonalHeadInterval 1 (N - 1) +
    diagonalTailInterval 1 N

private def oneCoarseSeriesInterval
    (N : ℕ) (coarseHead : RatInterval) : RatInterval :=
  oneDiagonalBaseInterval - coarseHead + diagonalTailInterval 1 N

private theorem oneDiagonalSeriesInterval_contains
    {N : ℕ} (hN : 16 ≤ N) (hmode : 10 ≤ N) :
    (oneDiagonalSeriesInterval N).Contains (yoshidaDiagonalMoment 1) := by
  rw [yoshidaDiagonalMoment_eq_acceleratedSeries (by norm_num : 1 ≠ 0)]
  rw [← diagonalCorrection_head_add_tail_eq_tsum
    (n := 1) (N := N) (by norm_num : 1 ≠ 0) (by omega)]
  have hbase := oneDiagonalBaseInterval_contains_acceleratedBase
  have hhead := diagonalHeadInterval_contains 1 (N - 1)
  have htail := diagonalTailInterval_contains_neg_tsum
    (n := 1) (N := N) hN hmode
  unfold oneDiagonalSeriesInterval
  have hcombine := contains_add (contains_sub hbase hhead) htail
  convert hcombine using 1
  all_goals ring

private def oneModeChunkBox : ℕ → RatInterval
  | 0 => ⟨-246171326114 / 1000000000000, -246171325700 / 1000000000000⟩
  | 1 => ⟨-113547759 / 1000000000000, -113547718 / 1000000000000⟩
  | 2 => ⟨-21161239 / 1000000000000, -21161215 / 1000000000000⟩
  | 3 => ⟨-7423300 / 1000000000000, -7423283 / 1000000000000⟩
  | 4 => ⟨-3440034 / 1000000000000, -3440020 / 1000000000000⟩
  | 5 => ⟨-1870046 / 1000000000000, -1870034 / 1000000000000⟩
  | 6 => ⟨-1128150 / 1000000000000, -1128140 / 1000000000000⟩
  | 7 => ⟨-732483 / 1000000000000, -732474 / 1000000000000⟩
  | 8 => ⟨-502329 / 1000000000000, -502321 / 1000000000000⟩
  | 9 => ⟨-359393 / 1000000000000, -359386 / 1000000000000⟩
  | 10 => ⟨-265958 / 1000000000000, -265951 / 1000000000000⟩
  | 11 => ⟨-202313 / 1000000000000, -202307 / 1000000000000⟩
  | 12 => ⟨-157467 / 1000000000000, -157461 / 1000000000000⟩
  | 13 => ⟨-124959 / 1000000000000, -124953 / 1000000000000⟩
  | 14 => ⟨-100820 / 1000000000000, -100815 / 1000000000000⟩
  | 15 => ⟨-82520 / 1000000000000, -82515 / 1000000000000⟩
  | 16 => ⟨-68396 / 1000000000000, -68391 / 1000000000000⟩
  | 17 => ⟨-57320 / 1000000000000, -57316 / 1000000000000⟩
  | 18 => ⟨-48513 / 1000000000000, -48509 / 1000000000000⟩
  | 19 => ⟨-41422 / 1000000000000, -41418 / 1000000000000⟩
  | 20 => ⟨-35648 / 1000000000000, -35644 / 1000000000000⟩
  | 21 => ⟨-30900 / 1000000000000, -30896 / 1000000000000⟩
  | 22 => ⟨-26959 / 1000000000000, -26955 / 1000000000000⟩
  | 23 => ⟨-23661 / 1000000000000, -23657 / 1000000000000⟩
  | 24 => ⟨-20879 / 1000000000000, -20876 / 1000000000000⟩
  | 25 => ⟨-18518 / 1000000000000, -18514 / 1000000000000⟩
  | 26 => ⟨-16499 / 1000000000000, -16496 / 1000000000000⟩
  | 27 => ⟨-14763 / 1000000000000, -14760 / 1000000000000⟩
  | 28 => ⟨-13263 / 1000000000000, -13260 / 1000000000000⟩
  | 29 => ⟨-11959 / 1000000000000, -11956 / 1000000000000⟩
  | 30 => ⟨-10821 / 1000000000000, -10818 / 1000000000000⟩
  | 31 => ⟨-9786 / 1000000000000, -9783 / 1000000000000⟩
  | _ => pure 0

/-! Each checkpoint has 256 consecutive corrections, except the final
checkpoint, which has 255.  Thus the 32 blocks cover exactly the accelerated
head `k = 1, ..., 8191`; the analytic tail starts at `k = 8192`. -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem oneModeChunk_kernel_certificate
    {i : ℕ} (hi : i < 32) :
    IsSubinterval (scheduledChunkInterval 1 32 i) (oneModeChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
private theorem oneModeCoarseSeries_kernel_certificate :
    IsSubinterval
      (oneCoarseSeriesInterval 8192
        (coarseCheckpointHead oneModeChunkBox 32))
      ⟨38331 / 100000, 38332 / 100000⟩ := by
  decide +kernel

private theorem oneDiagonalSeriesInterval_sub_coarse
    {N : ℕ} {coarseHead : RatInterval}
    (hhead : IsSubinterval (diagonalHeadInterval 1 (N - 1)) coarseHead) :
    IsSubinterval (oneDiagonalSeriesInterval N)
      (oneCoarseSeriesInterval N coarseHead) := by
  exact isSubinterval_add
    (isSubinterval_sub_right oneDiagonalBaseInterval hhead)
    (isSubinterval_refl _)

private theorem oneMode_diagonal_certificate :
    IsSubinterval (oneDiagonalSeriesInterval 8192)
      ⟨38331 / 100000, 38332 / 100000⟩ := by
  apply isSubinterval_trans
    (oneDiagonalSeriesInterval_sub_coarse
      (diagonalHeadInterval_sub_coarseCheckpoint 1 32 (by norm_num)
        oneModeChunkBox (fun _ hi ↦ oneModeChunk_kernel_certificate hi)))
  exact oneModeCoarseSeries_kernel_certificate

/-- The exact candidate box for the first normalized even cosine mode contains
the actual production diagonal moment. -/
theorem yoshidaEvenDiagonalTarget_one_contains :
    (yoshidaEvenDiagonalTargets 1).Contains (yoshidaDiagonalMoment 1) := by
  have hseries := oneDiagonalSeriesInterval_contains
    (N := 8192) (by norm_num) (by norm_num)
  have htarget :
      (⟨38331 / 100000, 38332 / 100000⟩ : RatInterval).Contains
        (yoshidaDiagonalMoment 1) :=
    contains_of_subinterval oneMode_diagonal_certificate hseries
  change (⟨38331 / 100000, 38332 / 100000⟩ : RatInterval).Contains
    (yoshidaDiagonalMoment 1)
  exact htarget

end

end ArithmeticHodge.Analysis.YoshidaEvenDiagonalOneEnclosure
