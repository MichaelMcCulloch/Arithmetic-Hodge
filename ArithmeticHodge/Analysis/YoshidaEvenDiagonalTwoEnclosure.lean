import ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures
import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEvenDiagonalTwoEnclosure

noncomputable section

open RatInterval
open YoshidaConstantBounds
open YoshidaDiagonalAcceleratedSeries
open YoshidaDiagonalMomentEnclosures
open YoshidaDiagonalSeriesTail
open YoshidaEvenMomentTargets
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

private def twoGammaInterval : RatInterval :=
  ⟨577215 / 1000000, 577216 / 1000000⟩

private def twoLogPiInterval : RatInterval :=
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

private theorem twoGammaInterval_contains :
    twoGammaInterval.Contains Real.eulerMascheroniConstant := by
  have h := strict_euler_gamma_fine_bounds
  constructor
  · norm_num [twoGammaInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [twoGammaInterval, Contains] at h ⊢
    exact h.2.le

private theorem twoLogPiInterval_contains :
    twoLogPiInterval.Contains (Real.log Real.pi) := by
  have h := strict_log_pi_fine_bounds
  constructor
  · norm_num [twoLogPiInterval, Contains] at h ⊢
    exact h.1.le
  · norm_num [twoLogPiInterval, Contains] at h ⊢
    exact h.2.le

private def twoDiagonalBaseInterval : RatInterval :=
  pure 2 * diagonalRampInterval 2 (-1 / 2) sqrtTwoInterval -
      twoGammaInterval - twoLogPiInterval + logFourThirdsInterval +
    diagonalAInterval * positiveSquare piFineInterval / pure 6

private theorem twoDiagonalBaseInterval_contains_acceleratedBase :
    twoDiagonalBaseInterval.Contains (diagonalAcceleratedBase 2) := by
  rw [← diagonalBaseValue_eq_acceleratedBase]
  have hramp := diagonalRampInterval_contains 2 (-1 / 2) sqrtTwoInterval
    (by norm_num) sqrtTwoInterval_contains
  have hramp' : (diagonalRampInterval 2 (-1 / 2) sqrtTwoInterval).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa 2 ^ 2) (-1 / 2 : ℝ)
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
  unfold twoDiagonalBaseInterval diagonalBaseValue
  exact contains_add
    (contains_add
      (contains_sub
        (contains_sub (contains_mul htwo hramp') twoGammaInterval_contains)
        twoLogPiInterval_contains)
      logFourThirdsInterval_contains)
    htail

private def twoDiagonalSeriesInterval (N : ℕ) : RatInterval :=
  twoDiagonalBaseInterval - diagonalHeadInterval 2 (N - 1) +
    diagonalTailInterval 2 N

private def twoCoarseSeriesInterval
    (N : ℕ) (coarseHead : RatInterval) : RatInterval :=
  twoDiagonalBaseInterval - coarseHead + diagonalTailInterval 2 N

private theorem twoDiagonalSeriesInterval_contains
    {N : ℕ} (hN : 16 ≤ N) (hmode : 20 ≤ N) :
    (twoDiagonalSeriesInterval N).Contains (yoshidaDiagonalMoment 2) := by
  rw [yoshidaDiagonalMoment_eq_acceleratedSeries (by norm_num : 2 ≠ 0)]
  rw [← diagonalCorrection_head_add_tail_eq_tsum
    (n := 2) (N := N) (by norm_num : 2 ≠ 0) (by omega)]
  have hbase := twoDiagonalBaseInterval_contains_acceleratedBase
  have hhead := diagonalHeadInterval_contains 2 (N - 1)
  have htail := diagonalTailInterval_contains_neg_tsum
    (n := 2) (N := N) hN hmode
  unfold twoDiagonalSeriesInterval
  have hcombine := contains_add (contains_sub hbase hhead) htail
  convert hcombine using 1
  all_goals ring

private def twoModeChunkBox : ℕ → RatInterval
  | 0 => ⟨-906848113423 / 1000000000000, -906848113044 / 1000000000000⟩
  | 1 => ⟨-461144842 / 1000000000000, -461144801 / 1000000000000⟩
  | 2 => ⟨-85971444 / 1000000000000, -85971420 / 1000000000000⟩
  | 3 => ⟨-30160538 / 1000000000000, -30160521 / 1000000000000⟩
  | 4 => ⟨-13977009 / 1000000000000, -13976995 / 1000000000000⟩
  | 5 => ⟨-7598146 / 1000000000000, -7598134 / 1000000000000⟩
  | 6 => ⟨-4583781 / 1000000000000, -4583771 / 1000000000000⟩
  | 7 => ⟨-2976152 / 1000000000000, -2976143 / 1000000000000⟩
  | 8 => ⟨-2041013 / 1000000000000, -2041006 / 1000000000000⟩
  | 9 => ⟨-1460247 / 1000000000000, -1460240 / 1000000000000⟩
  | 10 => ⟨-1080611 / 1000000000000, -1080604 / 1000000000000⟩
  | 11 => ⟨-822014 / 1000000000000, -822008 / 1000000000000⟩
  | 12 => ⟨-639799 / 1000000000000, -639793 / 1000000000000⟩
  | 13 => ⟨-507714 / 1000000000000, -507709 / 1000000000000⟩
  | 14 => ⟨-409635 / 1000000000000, -409630 / 1000000000000⟩
  | 15 => ⟨-335283 / 1000000000000, -335278 / 1000000000000⟩
  | 16 => ⟨-277893 / 1000000000000, -277889 / 1000000000000⟩
  | 17 => ⟨-232892 / 1000000000000, -232888 / 1000000000000⟩
  | 18 => ⟨-197107 / 1000000000000, -197103 / 1000000000000⟩
  | 19 => ⟨-168295 / 1000000000000, -168291 / 1000000000000⟩
  | 20 => ⟨-144837 / 1000000000000, -144833 / 1000000000000⟩
  | 21 => ⟨-125544 / 1000000000000, -125540 / 1000000000000⟩
  | 22 => ⟨-109532 / 1000000000000, -109528 / 1000000000000⟩
  | 23 => ⟨-96131 / 1000000000000, -96127 / 1000000000000⟩
  | 24 => ⟨-84830 / 1000000000000, -84827 / 1000000000000⟩
  | 25 => ⟨-75234 / 1000000000000, -75231 / 1000000000000⟩
  | 26 => ⟨-67032 / 1000000000000, -67029 / 1000000000000⟩
  | 27 => ⟨-59981 / 1000000000000, -59978 / 1000000000000⟩
  | 28 => ⟨-53885 / 1000000000000, -53882 / 1000000000000⟩
  | 29 => ⟨-48588 / 1000000000000, -48585 / 1000000000000⟩
  | 30 => ⟨-43963 / 1000000000000, -43960 / 1000000000000⟩
  | 31 => ⟨-39907 / 1000000000000, -39904 / 1000000000000⟩
  | 32 => ⟨-36335 / 1000000000000, -36332 / 1000000000000⟩
  | 33 => ⟨-33177 / 1000000000000, -33174 / 1000000000000⟩
  | 34 => ⟨-30375 / 1000000000000, -30372 / 1000000000000⟩
  | 35 => ⟨-27879 / 1000000000000, -27877 / 1000000000000⟩
  | 36 => ⟨-25650 / 1000000000000, -25647 / 1000000000000⟩
  | 37 => ⟨-23652 / 1000000000000, -23650 / 1000000000000⟩
  | 38 => ⟨-21856 / 1000000000000, -21854 / 1000000000000⟩
  | 39 => ⟨-20162 / 1000000000000, -20160 / 1000000000000⟩
  | _ => pure 0

/-! Each checkpoint has 256 consecutive corrections, except the final
checkpoint, which has 255.  Thus the 40 blocks cover exactly the accelerated
head `k = 1, ..., 10239`; the analytic tail starts at `k = 10240`. -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem twoModeChunk_kernel_certificate
    {i : ℕ} (hi : i < 40) :
    IsSubinterval (scheduledChunkInterval 2 40 i) (twoModeChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
private theorem twoModeCoarseSeries_kernel_certificate :
    IsSubinterval
      (twoCoarseSeriesInterval 10240
        (coarseCheckpointHead twoModeChunkBox 40))
      ⟨106433 / 100000, 106434 / 100000⟩ := by
  decide +kernel

private theorem twoDiagonalSeriesInterval_sub_coarse
    {N : ℕ} {coarseHead : RatInterval}
    (hhead : IsSubinterval (diagonalHeadInterval 2 (N - 1)) coarseHead) :
    IsSubinterval (twoDiagonalSeriesInterval N)
      (twoCoarseSeriesInterval N coarseHead) := by
  exact isSubinterval_add
    (isSubinterval_sub_right twoDiagonalBaseInterval hhead)
    (isSubinterval_refl _)

private theorem twoMode_diagonal_certificate :
    IsSubinterval (twoDiagonalSeriesInterval 10240)
      ⟨106433 / 100000, 106434 / 100000⟩ := by
  apply isSubinterval_trans
    (twoDiagonalSeriesInterval_sub_coarse
      (diagonalHeadInterval_sub_coarseCheckpoint 2 40 (by norm_num)
        twoModeChunkBox (fun _ hi ↦ twoModeChunk_kernel_certificate hi)))
  exact twoModeCoarseSeries_kernel_certificate

/-- The exact candidate box for the second normalized even cosine mode contains
the actual production diagonal moment. -/
theorem yoshidaEvenDiagonalTarget_two_contains :
    (yoshidaEvenDiagonalTargets 2).Contains (yoshidaDiagonalMoment 2) := by
  have hseries := twoDiagonalSeriesInterval_contains
    (N := 10240) (by norm_num) (by norm_num)
  have htarget :
      (⟨106433 / 100000, 106434 / 100000⟩ : RatInterval).Contains
        (yoshidaDiagonalMoment 2) :=
    contains_of_subinterval twoMode_diagonal_certificate hseries
  change (⟨106433 / 100000, 106434 / 100000⟩ : RatInterval).Contains
    (yoshidaDiagonalMoment 2)
  exact htarget

end

end ArithmeticHodge.Analysis.YoshidaEvenDiagonalTwoEnclosure
