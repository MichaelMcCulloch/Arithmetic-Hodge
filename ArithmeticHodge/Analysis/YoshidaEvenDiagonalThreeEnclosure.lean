import ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures
import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEvenDiagonalThreeEnclosure

noncomputable section

open RatInterval
open YoshidaConstantBounds
open YoshidaDiagonalAcceleratedSeries
open YoshidaDiagonalMomentEnclosures
open YoshidaDiagonalSeriesTail
open YoshidaEvenMomentTargets
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

private def threeGammaInterval : RatInterval :=
  ⟨577215 / 1000000, 577216 / 1000000⟩

private def threeLogPiInterval : RatInterval :=
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

private theorem threeGammaInterval_contains :
    threeGammaInterval.Contains Real.eulerMascheroniConstant := by
  have h := strict_euler_gamma_fine_bounds
  constructor
  · norm_num [threeGammaInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [threeGammaInterval, Contains] at h ⊢
    exact h.2.le

private theorem threeLogPiInterval_contains :
    threeLogPiInterval.Contains (Real.log Real.pi) := by
  have h := strict_log_pi_fine_bounds
  constructor
  · norm_num [threeLogPiInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [threeLogPiInterval, Contains] at h ⊢
    exact h.2.le

private def threeDiagonalBaseInterval : RatInterval :=
  pure 2 * diagonalRampInterval 3 (-1 / 2) sqrtTwoInterval -
      threeGammaInterval - threeLogPiInterval + logFourThirdsInterval +
    diagonalAInterval * positiveSquare piFineInterval / pure 6

private theorem threeDiagonalBaseInterval_contains_acceleratedBase :
    threeDiagonalBaseInterval.Contains (diagonalAcceleratedBase 3) := by
  rw [← diagonalBaseValue_eq_acceleratedBase]
  have hramp := diagonalRampInterval_contains 3 (-1 / 2) sqrtTwoInterval
    (by norm_num) sqrtTwoInterval_contains
  have hramp' : (diagonalRampInterval 3 (-1 / 2) sqrtTwoInterval).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa 3 ^ 2) (-1 / 2 : ℝ)
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
  unfold threeDiagonalBaseInterval diagonalBaseValue
  exact contains_add
    (contains_add
      (contains_sub
        (contains_sub (contains_mul htwo hramp') threeGammaInterval_contains)
        threeLogPiInterval_contains)
      logFourThirdsInterval_contains)
    htail

private def threeDiagonalSeriesInterval (N : ℕ) : RatInterval :=
  threeDiagonalBaseInterval - diagonalHeadInterval 3 (N - 1) +
    diagonalTailInterval 3 N

private def threeCoarseSeriesInterval
    (N : ℕ) (coarseHead : RatInterval) : RatInterval :=
  threeDiagonalBaseInterval - coarseHead + diagonalTailInterval 3 N

private theorem threeDiagonalSeriesInterval_contains
    {N : ℕ} (hN : 16 ≤ N) (hmode : 30 ≤ N) :
    (threeDiagonalSeriesInterval N).Contains (yoshidaDiagonalMoment 3) := by
  rw [yoshidaDiagonalMoment_eq_acceleratedSeries (by norm_num : 3 ≠ 0)]
  rw [← diagonalCorrection_head_add_tail_eq_tsum
    (n := 3) (N := N) (by norm_num : 3 ≠ 0) (by omega)]
  have hbase := threeDiagonalBaseInterval_contains_acceleratedBase
  have hhead := diagonalHeadInterval_contains 3 (N - 1)
  have htail := diagonalTailInterval_contains_neg_tsum
    (n := 3) (N := N) hN hmode
  unfold threeDiagonalSeriesInterval
  have hcombine := contains_add (contains_sub hbase hhead) htail
  convert hcombine using 1
  all_goals ring

private def threeModeChunkBox : ℕ → RatInterval
  | 0 => ⟨-1305291539636 / 1000000000000, -1305291539279 / 1000000000000⟩
  | 1 => ⟨-1039576587 / 1000000000000, -1039576546 / 1000000000000⟩
  | 2 => ⟨-193939825 / 1000000000000, -193939801 / 1000000000000⟩
  | 3 => ⟨-68047718 / 1000000000000, -68047700 / 1000000000000⟩
  | 4 => ⟨-31536385 / 1000000000000, -31536371 / 1000000000000⟩
  | 5 => ⟨-17144170 / 1000000000000, -17144159 / 1000000000000⟩
  | 6 => ⟨-10342818 / 1000000000000, -10342808 / 1000000000000⟩
  | 7 => ⟨-6715430 / 1000000000000, -6715422 / 1000000000000⟩
  | 8 => ⟨-4605397 / 1000000000000, -4605389 / 1000000000000⟩
  | 9 => ⟨-3294954 / 1000000000000, -3294947 / 1000000000000⟩
  | 10 => ⟨-2438334 / 1000000000000, -2438328 / 1000000000000⟩
  | 11 => ⟨-1854829 / 1000000000000, -1854823 / 1000000000000⟩
  | 12 => ⟨-1443673 / 1000000000000, -1443667 / 1000000000000⟩
  | 13 => ⟨-1145632 / 1000000000000, -1145626 / 1000000000000⟩
  | 14 => ⟨-924321 / 1000000000000, -924316 / 1000000000000⟩
  | 15 => ⟨-756549 / 1000000000000, -756545 / 1000000000000⟩
  | 16 => ⟨-627053 / 1000000000000, -627049 / 1000000000000⟩
  | 17 => ⟨-525509 / 1000000000000, -525505 / 1000000000000⟩
  | 18 => ⟨-444763 / 1000000000000, -444759 / 1000000000000⟩
  | 19 => ⟨-379750 / 1000000000000, -379746 / 1000000000000⟩
  | 20 => ⟨-326817 / 1000000000000, -326813 / 1000000000000⟩
  | 21 => ⟨-283284 / 1000000000000, -283280 / 1000000000000⟩
  | 22 => ⟨-247152 / 1000000000000, -247149 / 1000000000000⟩
  | 23 => ⟨-216914 / 1000000000000, -216911 / 1000000000000⟩
  | 24 => ⟨-191415 / 1000000000000, -191411 / 1000000000000⟩
  | 25 => ⟨-169761 / 1000000000000, -169758 / 1000000000000⟩
  | 26 => ⟨-151254 / 1000000000000, -151251 / 1000000000000⟩
  | 27 => ⟨-135343 / 1000000000000, -135340 / 1000000000000⟩
  | 28 => ⟨-121588 / 1000000000000, -121585 / 1000000000000⟩
  | 29 => ⟨-109635 / 1000000000000, -109632 / 1000000000000⟩
  | 30 => ⟨-99199 / 1000000000000, -99197 / 1000000000000⟩
  | 31 => ⟨-90047 / 1000000000000, -90045 / 1000000000000⟩
  | 32 => ⟨-81987 / 1000000000000, -81985 / 1000000000000⟩
  | 33 => ⟨-74861 / 1000000000000, -74859 / 1000000000000⟩
  | 34 => ⟨-68538 / 1000000000000, -68535 / 1000000000000⟩
  | 35 => ⟨-62907 / 1000000000000, -62905 / 1000000000000⟩
  | 36 => ⟨-57877 / 1000000000000, -57874 / 1000000000000⟩
  | 37 => ⟨-53369 / 1000000000000, -53366 / 1000000000000⟩
  | 38 => ⟨-49317 / 1000000000000, -49314 / 1000000000000⟩
  | 39 => ⟨-45665 / 1000000000000, -45663 / 1000000000000⟩
  | 40 => ⟨-42365 / 1000000000000, -42363 / 1000000000000⟩
  | 41 => ⟨-39376 / 1000000000000, -39373 / 1000000000000⟩
  | 42 => ⟨-36661 / 1000000000000, -36659 / 1000000000000⟩
  | 43 => ⟨-34190 / 1000000000000, -34188 / 1000000000000⟩
  | 44 => ⟨-31937 / 1000000000000, -31935 / 1000000000000⟩
  | 45 => ⟨-29877 / 1000000000000, -29875 / 1000000000000⟩
  | 46 => ⟨-27991 / 1000000000000, -27988 / 1000000000000⟩
  | 47 => ⟨-26260 / 1000000000000, -26258 / 1000000000000⟩
  | 48 => ⟨-24669 / 1000000000000, -24667 / 1000000000000⟩
  | 49 => ⟨-23204 / 1000000000000, -23202 / 1000000000000⟩
  | 50 => ⟨-21852 / 1000000000000, -21850 / 1000000000000⟩
  | 51 => ⟨-20604 / 1000000000000, -20602 / 1000000000000⟩
  | 52 => ⟨-19449 / 1000000000000, -19447 / 1000000000000⟩
  | 53 => ⟨-18379 / 1000000000000, -18377 / 1000000000000⟩
  | 54 => ⟨-17386 / 1000000000000, -17383 / 1000000000000⟩
  | 55 => ⟨-16463 / 1000000000000, -16461 / 1000000000000⟩
  | 56 => ⟨-15604 / 1000000000000, -15602 / 1000000000000⟩
  | 57 => ⟨-14804 / 1000000000000, -14802 / 1000000000000⟩
  | 58 => ⟨-14058 / 1000000000000, -14056 / 1000000000000⟩
  | 59 => ⟨-13361 / 1000000000000, -13359 / 1000000000000⟩
  | 60 => ⟨-12709 / 1000000000000, -12707 / 1000000000000⟩
  | 61 => ⟨-12099 / 1000000000000, -12097 / 1000000000000⟩
  | 62 => ⟨-11528 / 1000000000000, -11526 / 1000000000000⟩
  | 63 => ⟨-10992 / 1000000000000, -10990 / 1000000000000⟩
  | 64 => ⟨-10488 / 1000000000000, -10487 / 1000000000000⟩
  | 65 => ⟨-10015 / 1000000000000, -10014 / 1000000000000⟩
  | 66 => ⟨-9570 / 1000000000000, -9569 / 1000000000000⟩
  | 67 => ⟨-9151 / 1000000000000, -9149 / 1000000000000⟩
  | 68 => ⟨-8756 / 1000000000000, -8755 / 1000000000000⟩
  | 69 => ⟨-8384 / 1000000000000, -8382 / 1000000000000⟩
  | 70 => ⟨-8032 / 1000000000000, -8030 / 1000000000000⟩
  | 71 => ⟨-7670 / 1000000000000, -7669 / 1000000000000⟩
  | _ => pure 0

/-! Each checkpoint has 256 consecutive corrections, except the final
checkpoint, which has 255.  Thus the 72 blocks cover exactly the accelerated
head `k = 1, ..., 18431`; the analytic tail starts at `k = 18432`. -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem threeModeChunk_kernel_certificate
    {i : ℕ} (hi : i < 72) :
    IsSubinterval (scheduledChunkInterval 3 72 i) (threeModeChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
private theorem threeModeCoarseSeries_kernel_certificate :
    IsSubinterval
      (threeCoarseSeriesInterval 18432
        (coarseCheckpointHead threeModeChunkBox 72))
      ⟨146725 / 100000, 146726 / 100000⟩ := by
  decide +kernel

private theorem threeDiagonalSeriesInterval_sub_coarse
    {N : ℕ} {coarseHead : RatInterval}
    (hhead : IsSubinterval (diagonalHeadInterval 3 (N - 1)) coarseHead) :
    IsSubinterval (threeDiagonalSeriesInterval N)
      (threeCoarseSeriesInterval N coarseHead) := by
  exact isSubinterval_add
    (isSubinterval_sub_right threeDiagonalBaseInterval hhead)
    (isSubinterval_refl _)

private theorem threeMode_diagonal_certificate :
    IsSubinterval (threeDiagonalSeriesInterval 18432)
      ⟨146725 / 100000, 146726 / 100000⟩ := by
  apply isSubinterval_trans
    (threeDiagonalSeriesInterval_sub_coarse
      (diagonalHeadInterval_sub_coarseCheckpoint 3 72 (by norm_num)
        threeModeChunkBox (fun _ hi ↦ threeModeChunk_kernel_certificate hi)))
  exact threeModeCoarseSeries_kernel_certificate

/-- The exact candidate box for the third normalized even cosine mode contains
the actual production diagonal moment. -/
theorem yoshidaEvenDiagonalTarget_three_contains :
    (yoshidaEvenDiagonalTargets 3).Contains (yoshidaDiagonalMoment 3) := by
  have hseries := threeDiagonalSeriesInterval_contains
    (N := 18432) (by norm_num) (by norm_num)
  have htarget :
      (⟨146725 / 100000, 146726 / 100000⟩ : RatInterval).Contains
        (yoshidaDiagonalMoment 3) :=
    contains_of_subinterval threeMode_diagonal_certificate hseries
  change (⟨146725 / 100000, 146726 / 100000⟩ : RatInterval).Contains
    (yoshidaDiagonalMoment 3)
  exact htarget

end

end ArithmeticHodge.Analysis.YoshidaEvenDiagonalThreeEnclosure
